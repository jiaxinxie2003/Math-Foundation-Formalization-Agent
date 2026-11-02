import json
import re
import subprocess
import os
import threading
from datetime import datetime
from dataclasses import dataclass, field
from openai import OpenAI

# ========== 1. 创建一个本地客户端实例，把客户端指向 DeepSeek，用于与deepseek通信 ==========
client = OpenAI(
    api_key=" ",           # 替换成你自己的 key
    base_url="https://api.deepseek.com"       # 大模型公司的网址exit
)


# ========== 2. 定义工具 ==========
COQ_OUTPUT_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), "coq_output")

def _load_coqc_timeout():
    """coqc 编译超时秒数：默认 100，可通过环境变量 COQC_TIMEOUT 覆盖（正数才生效）。"""
    try:
        t = float(os.environ.get("COQC_TIMEOUT", "100"))
        return t if t > 0 else 100
    except ValueError:
        return 100

COQC_TIMEOUT = _load_coqc_timeout()


def _kill_process_tree(proc):
    """强制终止进程及其整个进程树，确保子进程不残留（Windows 用 taskkill /F /T）。"""
    if proc is None or proc.poll() is not None:
        return
    try:
        if os.name == "nt":
            subprocess.run(
                ["taskkill", "/F", "/T", "/PID", str(proc.pid)],
                capture_output=True,
                timeout=10,
            )
        else:
            proc.kill()
    except Exception:
        pass
    try:
        proc.kill()
    except Exception:
        pass
    try:
        proc.wait(timeout=5)
    except Exception:
        pass


def _safe_read_path(filename):
    """用于 read_coq_file / compile_coq：允许任意路径的 .v 文件，只做后缀校验。"""
    if not filename.endswith(".v"):
        return None, f"文件名《{filename}》不是 .v 后缀，只允许操作 Coq 源文件（.v）。"
    if not os.path.isabs(filename):
        return None, f"文件路径《{filename}》不是绝对路径，请提供完整的文件路径。"
    return filename, None


def _resolve_file_path(filename):
    """解析文件路径：绝对路径（含盘符）直接使用，纯文件名放到 COQ_OUTPUT_DIR。"""
    if not filename.endswith(".v"):
        return None, f"文件名《{filename}》不是 .v 后缀，只允许操作 Coq 源文件（.v）。"
    if os.path.isabs(filename):
        return filename, None
    basename = os.path.basename(filename)
    safe = os.path.join(COQ_OUTPUT_DIR, basename)
    os.makedirs(COQ_OUTPUT_DIR, exist_ok=True)
    return safe, None


# ========== Coq Session：持久化 coqtop 进程管理 ==========

def split_commands(content):
    """
    将 Coq 源文件按完整 Vernac 命令拆分为独立句子。

    === 拆分规则 ===
    - 以 '.' 后跟空白符 / EOF 作为命令终止符（Vernac 标准分隔符）
    - 将句首出现的 bullets（-、+、*、--、++、**、---、+++、***）拆为独立命令
    - 将句首出现的 brace（{、}）拆为独立命令
    - 正确处理 Coq 字符串字面量 "" 和嵌套注释 (* *)

    === 已验证可正确处理的 Coq 语法 ===
    - Module ... End、Section ... End
    - Record foo := { ... }.
    - Inductive ... := ... | ... .
    - Fixpoint ... := match ... with ... end.
    - Program Definition / Obligation / Next Obligation
    - Ltac ... := ...                       （Ltac 体内不含 '.' 作为分隔符）
    - Notation / Infix / Arguments / Hint   （均为 '.' 终止的单条命令）
    - 多行 match ... with ... end          （match 体内不使用 '.' 分隔）
    - 字符串中的 '.'："hello.world"          （由 in_string 跟踪跳过）
    - 注释中的 '.'：(* this.is.ok *)         （由 comment_depth 跟踪跳过）
    - 投影语法 r.(field)                    （'.' 后跟 '('，非空白，不拆分）
    - 证明脚本中的 bullets / braces          （句首的 -+*{} 被正确拆分）

    === 已知限制 ===
    - 不解析 Coq 的完整语法树，仅做词法级切分
    - 如果 Ltac 定义体内以某种方式内嵌了 Vernac '.'（极端罕见），会错误切分
    - 极少数情况下 '.' 前是空格但并非命令终止符（如 Notation 中的 ".()" 记法），
      可能误切分，实际使用中极少触发

    返回命令字符串列表，列表非空。
    """
    commands = []
    n = len(content)
    i = 0
    in_string = False
    comment_depth = 0
    sent_start = 0
    at_sent_start = True   # 当前扫描位置是否处于句首（仅前面有空白）

    while i < n:
        c = content[i]

        # ---- 字符串字面量 ----
        if in_string:
            if c == '"' and content[i-1:i] != '\\':
                in_string = False
            i += 1
            continue

        # ---- 嵌套注释 (* ... *) ----
        if comment_depth > 0:
            if content[i:i+2] == '(*':
                comment_depth += 1
                i += 2
                continue
            if content[i:i+2] == '*)':
                comment_depth -= 1
                i += 2
                continue
            i += 1
            continue

        if content[i:i+2] == '(*':
            comment_depth += 1
            i += 2
            continue

        if c == '"':
            in_string = True
            at_sent_start = False
            i += 1
            continue

        # ---- 非空白字符表示已离开句首 ----
        if c not in ' \t\n\r':
            at_sent_start = False

        # ---- '.' 命令终止符：后面必须是空白或 EOF ----
        if c == '.':
            after = content[i+1] if i+1 < n else ''
            if after in ('', ' ', '\t', '\n', '\r'):
                text = content[sent_start:i+1].strip()
                if text:
                    commands.append(text)
                i += 1
                while i < n and content[i] in ' \t\n\r':
                    i += 1
                sent_start = i
                at_sent_start = True
                continue

        # ---- bullets / braces 检测：仅在句首 ----
        if at_sent_start and c in '-+*{}':
            if c in '{}':
                if sent_start < i:
                    before = content[sent_start:i].strip()
                    if before:
                        commands.append(before)
                commands.append(c)
                i += 1
                while i < n and content[i] in ' \t\n\r':
                    i += 1
                sent_start = i
                at_sent_start = True
                continue

            # bullets: -、+、* 及多字符变体（-- / ++ / ** / --- / +++ / ***）
            j = i
            bullet_char = content[i]
            while j < n and content[j] == bullet_char and (j - i) < 3:
                j += 1
            after_bullet = content[j] if j < n else ''
            if after_bullet in ('', ' ', '\t', '\n', '\r'):
                if sent_start < i:
                    before = content[sent_start:i].strip()
                    if before:
                        commands.append(before)
                commands.append(content[i:j])
                i = j
                while i < n and content[i] in ' \t\n\r':
                    i += 1
                sent_start = i
                at_sent_start = True
                continue

        i += 1

    remaining = content[sent_start:].strip()
    if remaining:
        commands.append(remaining)

    return commands


class CoqSession:
    """持久化 coqtop 会话，使用 subprocess.Popen 维持长期 coqtop 进程。"""

    def __init__(self, coqtop_path, load_flags=None):
        self.coqtop_path = coqtop_path
        self.load_flags = load_flags or []
        self.process = None
        self._stderr_thread = None

    def start(self):
        """启动 coqtop 进程。"""
        if self.process is not None:
            return
        self.process = subprocess.Popen(
            [self.coqtop_path, "-quiet"] + self.load_flags,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            encoding="utf-8",
            errors="replace",
            bufsize=1,
        )
        # 后台线程持续排空 stderr，防止管道阻塞
        self._start_stderr_drain()
        # 读取初始 prompt
        self.read_until_prompt(timeout=10)

    def stop(self):
        """关闭 coqtop 进程及其整个子进程树。"""
        if self.process is None:
            return
        try:
            self.process.stdin.close()
        except Exception:
            pass
        _kill_process_tree(self.process)
        self.process = None
        self._stderr_thread = None

    def restart(self):
        """关闭并重新启动 coqtop。"""
        self.stop()
        self.start()

    def _write_stdin(self, data, timeout=10):
        """在后台线程写 stdin；超时说明 coqtop 已停止读取输入，抛异常避免无限阻塞。"""
        result = []

        def writer():
            try:
                self.process.stdin.write(data)
                self.process.stdin.flush()
                result.append(True)
            except Exception as e:
                result.append(e)

        t = threading.Thread(target=writer, daemon=True)
        t.start()
        t.join(timeout=timeout)
        if t.is_alive():
            raise RuntimeError("coqtop 停止读取输入（可能卡在某个不终止的 tactic）")
        if result and isinstance(result[0], Exception):
            raise result[0]

    def send_command(self, cmd, timeout=30, read_output=True):
        """向 coqtop 发送一条命令。read_output=False 时仅写入不读取·（批量加载使用）。"""
        if self.process is None:
            raise RuntimeError("CoqSession 未启动，请先调用 start()")
        if self.process.poll() is not None:
            raise RuntimeError(
                f"coqtop 进程已退出 (exit code {self.process.returncode})，请调用 restart()"
            )
        try:
            self._write_stdin(cmd.strip() + '\n')
        except RuntimeError:
            _kill_process_tree(self.process)
            raise
        if read_output:
            return self.read_until_prompt(timeout=timeout)
        return None

    def load_file(self, filename):
        """
        读取 .v 文件，按 Vernac 命令逐条发送给 coqtop。
        加载期间不读取每条命令的输出（read_output=False），
        全部发送完毕后再统一读取一次 prompt，确保 coqtop 已处理完所有命令。
        只有后续 show_goal() 才会真正获取证明状态。
        """
        with open(filename, 'r', encoding='utf-8') as f:
            content = f.read()
        commands = split_commands(content)
        for cmd in commands:
            self.send_command(cmd, read_output=False)
        # 批量加载完成后，读取一次输出使 coqtop 回到 stable prompt 状态
        self.read_until_prompt()

    def show_goal(self):
        """
        发送 Show. 并返回当前目标状态。

        返回值语义：
        - 正常 Goal：返回 hypotheses + goal 的原始文本
        - 无活动证明（Qed. / Abort. 之后）：返回明确的「当前没有活动证明」提示
        - coqtop 报错：返回带错误信息的提示

        LLM 可根据返回值中是否包含 'No focused proof' 或 'Error' 判断
        当前是否处于可证明状态。
        """
        raw = self.send_command('Show.')
        output = _extract_goal_output(raw)

        if not output:
            return "当前没有活动证明（No focused proof）。"
        if 'No focused proof' in output:
            return "当前没有活动证明（No focused proof）。"
        if 'Error:' in output:
            return (
                "无法获取证明状态（coqtop 报错）：\n"
                f"{output}\n\n"
                "请先使用 compile_coq 检查文件中的编译错误。"
            )
        return output

    def show_proof(self):
        """发送 Show Proof. 并返回当前证明项。"""
        raw = self.send_command('Show Proof.')
        return _extract_goal_output(raw)

    def read_until_prompt(self, timeout=30):
        """
        持续读取 stdout 直到 Coq prompt 出现，或超时/EOF。
        使用独立线程避免阻塞主流程。
        """
        output_lines = []
        done = threading.Event()
        read_error = []

        def reader():
            try:
                while not done.is_set():
                    if self.process is None or self.process.stdout is None:
                        break
                    line = self.process.stdout.readline()
                    if not line:          # EOF — 进程异常退出
                        read_error.append("coqtop 进程意外终止")
                        done.set()
                        break
                    output_lines.append(line)
                    s = line.strip()
                    # Coq prompt 格式：以 "<" 结尾的短行（兼容不同 Coq 版本）
                    if s.endswith('<'):
                        done.set()
                        break
            except Exception as e:
                read_error.append(str(e))
                done.set()

        t = threading.Thread(target=reader, daemon=True)
        t.start()
        t.join(timeout=timeout)

        if t.is_alive():
            done.set()
            t.join(timeout=2)

        if read_error:
            raise RuntimeError(read_error[0])

        return ''.join(output_lines)

    def _start_stderr_drain(self):
        """后台线程持续排空 stderr，防止管道满导致进程阻塞。"""

        def drain():
            try:
                while self.process and self.process.stderr:
                    line = self.process.stderr.readline()
                    if not line:
                        break
            except Exception:
                pass

        self._stderr_thread = threading.Thread(target=drain, daemon=True)
        self._stderr_thread.start()


# 全局会话状态：跟踪当前已加载的文件
_coq_session = None          # CoqSession 实例，None 表示需要重新建立
_coq_session_file = None     # 当前 session 加载的文件路径


def _invalidate_coq_session():
    """在文件被修改后调用，标记当前 session 为无效。"""
    global _coq_session, _coq_session_file
    if _coq_session is not None:
        _coq_session.stop()
        _coq_session = None
    _coq_session_file = None


def _extract_goal_output(raw_output):
    """从 coqtop 输出中移除末尾 prompt，返回干净的证明状态。"""
    if not raw_output:
        return raw_output
    output = raw_output.rstrip()
    for suffix in ('\n<', '\nCoq <', '\np <'):
        if output.endswith(suffix):
            output = output[:-len(suffix)]
    return output.strip()


# 用于创建文件并写入一些内容的函数工具
def create_text_file(filename, content):
    safe, err = _resolve_file_path(filename)
    if err:
        return err
    _coqc_error_cache.pop(safe, None)  # 文件已修改，缓存失效
    with open(safe, 'w', encoding='utf-8') as f:
        f.write(content)
    _invalidate_coq_session()          # 文件已修改，Coq 会话必须重建
    return f"已成功创建文件《{safe}》（绝对路径）。如需编译，请使用 compile_coq 并传入此完整路径。"

# 替换文件中的指定内容（第二次及之后的修改使用此工具，而非重写整个文件）
def replace_in_file(filename, old_string, new_string):
    safe, err = _resolve_file_path(filename)
    if err:
        return err
    if not os.path.isfile(safe):
        return f"文件《{safe}》不存在，请检查路径是否正确。如需创建新文件请使用 create_text_file。"
    with open(safe, 'r', encoding='utf-8') as f:
        content = f.read()
    if old_string not in content:
        return f"替换失败！在文件《{safe}》中未找到要替换的内容。\n要替换的文本：\n{old_string[:500]}"
    new_content = content.replace(old_string, new_string, 1)
    _coqc_error_cache.pop(safe, None)  # 文件已修改，缓存失效
    with open(safe, 'w', encoding='utf-8') as f:
        f.write(new_content)
    _invalidate_coq_session()           # 文件已修改，Coq 会话必须重建
    return f"替换成功！已在文件《{safe}》中将指定内容替换为新内容。"

# 读取文件工具
def read_coq_file(filename):
    safe, err = _safe_read_path(filename)
    if err:
        return err
    if not os.path.isfile(safe):
        return f"文件《{safe}》不存在，请检查路径是否正确。"
    with open(safe, 'r', encoding='utf-8') as f:
        content = f.read()
    return f"文件《{safe}》的内容如下：\n{content}"

# coqc 编译结果缓存：compile_coq 将所有结果（成功/失败/超时）缓存，get_coq_proof_state 直接复用，避免重复调用 coqc
_coqc_error_cache = {}  # {filepath: {"success": bool, "timed_out": bool, "error_line": int|None, "error": str}}

def _parse_coqc_error(error_output):
    """解析 coqc 错误输出，提取行号。"""
    match = re.search(r'line (\d+)', error_output)
    error_line = int(match.group(1)) if match else None
    return error_line


def _coq_load_flags(filename):
    """为编译/coqtop 生成加载路径：把文件所在目录映射到空逻辑前缀，
    使 Require Export <同目录模块> 能被稳定解析。"""
    if not filename:
        return []
    d = os.path.dirname(os.path.abspath(filename))
    if not d:
        return []
    return ["-Q", d, ""]


def _run_coqc(coqc_path, filename):
    """运行 coqc；超时则强制终止整个进程树。

    Returns:
        (returncode, stdout, stderr, timed_out)
        timed_out 为 True 时 returncode 为 None，stdout/stderr 为空字符串。
    """
    proc = subprocess.Popen(
        [coqc_path] + _coq_load_flags(filename) + [filename],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        encoding="utf-8",
        errors="replace",
    )
    try:
        out, err = proc.communicate(timeout=COQC_TIMEOUT)
        return proc.returncode, out, err, False
    except subprocess.TimeoutExpired:
        _kill_process_tree(proc)
        return None, "", "", True


# Coq编译工具
def compile_coq(filename):
    coqc_path = r"D:\Coq\bin\coqc.exe"
    safe, err = _safe_read_path(filename)
    if err:
        return err
    if not os.path.isfile(safe):
        return f"文件《{safe}》不存在，请检查路径是否正确。"
    if not os.path.isfile(coqc_path):
        return f"coqc 编译器未找到，请检查 Coq 是否安装在 {coqc_path}。"

    # 文件被重新编译，清除旧缓存
    _coqc_error_cache.pop(safe, None)

    returncode, out, err, timed_out = _run_coqc(coqc_path, safe)

    if timed_out:
        timeout_msg = (
            f"编译超时！文件《{safe}》在 {COQC_TIMEOUT:g} 秒内未完成编译。\n"
            f"可能原因：证明脚本中存在不终止或展开爆炸的 tactic"
            f"（如 auto/eauto/repeat/compute/simpl 等），请换用更受控的证明策略。"
        )
        _coqc_error_cache[safe] = {
            "success": False, "timed_out": True, "error_line": None, "error": timeout_msg,
        }
        return timeout_msg
    if returncode == 0:
        _coqc_error_cache[safe] = {
            "success": True, "timed_out": False, "error_line": None, "error": "",
        }
        return f"编译成功！文件《{safe}》已通过 Coq 验证。"

    error_output = err.strip() or out.strip()
    # 缓存错误信息和行号，供 get_coq_proof_state 复用
    _coqc_error_cache[safe] = {
        "success": False,
        "timed_out": False,
        "error_line": _parse_coqc_error(error_output),
        "error": error_output,
    }
    return f"编译失败！文件《{safe}》存在错误：\n{error_output}"


# 获取Coq证明状态的工具
# 使用持久化 CoqSession，不再每次重启 coqtop 重复执行整个文件
def get_coq_proof_state(filename):
    global _coq_session, _coq_session_file

    coqtop_path = r"D:\Coq\bin\coqtop.exe"
    coqc_path = r"D:\Coq\bin\coqc.exe"
    safe, err = _safe_read_path(filename)
    if err:
        return err
    if not os.path.isfile(safe):
        return f"文件《{safe}》不存在，请检查路径是否正确。"
    if not os.path.isfile(coqtop_path):
        return f"coqtop 未找到，请检查 Coq 是否安装在 {coqtop_path}。"

    try:
        with open(safe, 'r', encoding='utf-8') as f:
            content = f.read()
    except Exception as e:
        return f"读取文件《{safe}》失败：{e}"

    # Step 1: 获取编译结果（优先从缓存读取 compile_coq 的结果）
    timed_out = False
    cached = _coqc_error_cache.get(safe)
    if cached:
        coqc_error = cached.get("error", "")
        error_line = cached.get("error_line")
        timed_out = cached.get("timed_out", False)
    elif os.path.isfile(coqc_path):
        coqc_error = ""
        error_line = None
        returncode, out, err, timed_out = _run_coqc(coqc_path, safe)
        if timed_out:
            coqc_error = f"编译超时！文件《{safe}》在 {COQC_TIMEOUT:g} 秒内未完成编译。"
        elif returncode != 0:
            error_output = err.strip() or out.strip()
            coqc_error = error_output
            error_line = _parse_coqc_error(error_output)
    else:
        coqc_error = ""
        error_line = None

    # 编译超时：文件含不终止 tactic，coqtop 加载同样会卡住，直接返回诊断，不再执行 coqc / coqtop。
    if timed_out:
        return (
            f"=== coqc 编译超时 ===\n{coqc_error}\n\n"
            f"无法获取证明状态：文件中存在不终止或展开爆炸的 tactic，"
            f"coqtop 加载同样会卡住。\n"
            f"请使用 read_coq_file 查看文件内容，定位并替换可疑的 tactic"
            f"（如 auto/eauto/repeat/compute/simpl 等）。"
        )

    # 无明确可信的错误行号（编译成功 / 错误输出为空 / 行号缺失）时，
    # 不得把整个文件加载到 coqtop，避免误入不终止的 tactic 而阻塞。
    if error_line is None:
        if coqc_error:
            return (
                f"=== coqc 编译错误 ===\n{coqc_error}\n\n"
                f"未能定位错误行号，为避免 coqtop 加载整个文件时卡住，未获取证明状态。\n"
                f"请使用 read_coq_file 查看文件内容。"
            )
        return "当前文件无编译错误，且没有处于进行中的证明，无法获取证明状态。"

    # Step 2: 确定是否需要重新建立会话（首次调用 / 文件变更 / session 已失效）
    need_reload = (_coq_session is None or _coq_session_file != safe)

    if need_reload:
        # 关闭旧会话
        if _coq_session is not None:
            _coq_session.stop()
            _coq_session = None
        _coq_session_file = None

        try:
            # 启动新会话，仅加载错误行之前的代码（该前缀已由 coqc 验证通过，不会卡住）
            _coq_session = CoqSession(coqtop_path, load_flags=_coq_load_flags(safe))
            _coq_session.start()

            prefix_text = '\n'.join(content.split('\n')[:error_line])
            cut = -1
            for sep in ('.\n', '. ', '.\t'):
                pos = prefix_text.rfind(sep)
                if pos > cut:
                    cut = pos
            load_content = prefix_text[:cut + 1] if cut >= 0 else prefix_text

            commands = split_commands(load_content)
            for cmd in commands:
                _coq_session.send_command(cmd, read_output=False)
            _coq_session.read_until_prompt()
        except Exception as e:
            _invalidate_coq_session()
            return f"无法获取证明状态（coqtop 加载失败）：{e}\n请使用 read_coq_file 查看文件内容。"

        _coq_session_file = safe

    # Step 3: 仅发送 Show. 获取当前证明状态（不再重新执行整个文件）
    try:
        goal_output = _coq_session.show_goal()
    except Exception as e:
        _invalidate_coq_session()
        return f"无法获取证明状态（coqtop 读取失败）：{e}\n请使用 read_coq_file 查看文件内容。"

    # Step 4: 组装返回结果
    parts = []
    if goal_output:
        parts.append(f"=== 当前证明状态 ===\n{goal_output}")
    if coqc_error:
        parts.append(f"=== coqc 编译错误 ===\n{coqc_error}")
    if not parts:
        return "coqtop 未返回任何输出，文件可能为空或格式不正确。"

    return "\n\n".join(parts)


# 对工具的具体描述
tools = [
    {
        "type": "function",  # 工具的类型(自定义函数工具的固定写法即为如此)
        "function": {
            "name": "create_text_file",   # 函数工具的名字
            "description": "创建一个新的 Coq .v 源文件。可提供纯文件名（如 my_proof.v，自动保存到 coq_output 目录）或绝对路径（如 D:\\path\\to\\new_proof.v，直接写到该位置）。基于已有文件生成新文件时，请用绝对路径写到基础文件所在目录，并在文件开头 Require Export <基础文件名>。",
            "parameters": {
                "type": "object",
                "properties": {
                    "filename": {"type": "string", "description": "要创建的 .v 文件名（纯文件名不带路径，或完整的绝对路径如 D:\\path\\to\\new_proof.v）"},
                    "content": {"type": "string", "description": "要写入的 Coq 代码内容"}
                },
                "required": ["filename", "content"]      # 想要使这个函数工具能够被调用运行，不可缺少的参数
            }
            
        }
    },
    {
        "type": "function",
        "function": {
            "name": "replace_in_file",
            "description": "替换 .v 文件中指定的文本片段。编译失败后应优先使用此工具做精准修改，而不是重写整个文件。可接受纯文件名（如 proof.v，自动保存到 coq_output 目录）或绝对路径（如 D:\\path\\to\\file.v，直接修改该文件）。修改用户指定的目标文件时必须使用绝对路径。old_string 必须与文件中的原文完全匹配（含缩进和换行），new_string 为替换后的内容。一次只替换一处匹配。",
            "parameters": {
                "type": "object",
                "properties": {
                    "filename": {"type": "string", "description": "要修改的 .v 文件名（纯文件名不带路径，或完整的绝对路径如 D:\\path\\to\\file.v）"},
                    "old_string": {"type": "string", "description": "文件中要被替换的原文（必须完全匹配，含缩进和换行）"},
                    "new_string": {"type": "string", "description": "替换后的新文本"}
                },
                "required": ["filename", "old_string", "new_string"]
            }
        }
    },
    {
        "type": "function",
        "function": {
            "name": "read_coq_file",
            "description": "读取任意路径下的 .v Coq 源文件内容。必须提供完整的绝对路径（如 D:\\Vscode\\py\\mk.v）。用于查看已有文件中的代码，了解当前定义或在此基础上进行修改。",
            "parameters": {
                "type": "object",
                "properties": {
                    "filename": {"type": "string", "description": "要读取的 .v 文件的绝对路径（如 D:\\Vscode\\py\\mk.v）"}
                },
                "required": ["filename"]
            }
        }
    },
    {
        "type": "function",
        "function": {
            "name": "compile_coq",
            "description": "使用 coqc 编译器编译指定的 .v Coq 源文件。必须提供完整的绝对路径（如 D:\\Vscode\\py\\my_agent_new\\coq_output\\proof.v）。成功时返回编译通过的信息，失败时返回具体错误信息以便修正。",
            "parameters": {
                "type": "object",
                "properties": {
                    "filename": {"type": "string", "description": "要编译的 .v 文件的绝对路径（如 D:\\Vscode\\py\\my_agent_new\\coq_output\\proof.v）"}
                },
                "required": ["filename"]
            }
        }
    },
    {
        "type": "function",
        "function": {
            "name": "get_coq_proof_state",
            "description": "获取 .v 文件中当前的 Coq 证明状态，包括已有的假设条件（hypotheses）和待证明的目标（goals）。必须提供完整的绝对路径。编译失败后，使用此工具查看出错位置的证明上下文，以便分析问题并调整证明策略。",
            "parameters": {
                "type": "object",
                "properties": {
                    "filename": {"type": "string", "description": "要查看证明状态的 .v 文件的绝对路径"}
                },
                "required": ["filename"]
            }
        }
    }
]

# 基础工具集（Fast）：仅创建、修改、编译 — 覆盖简单证明的完整流程
basic_tools = [t for t in tools if t["function"]["name"] in (
    "create_text_file", "replace_in_file", "compile_coq"
)]


# ========== 2a. 通用任务描述结构 ==========

class TaskType:
    """Rocq 任务的基本类型。"""
    PROVE = "PROVE"      # 在已有文件中证明指定定理
    CREATE = "CREATE"    # 新建 .v 文件并完成内容/证明
    MODIFY = "MODIFY"    # 修改已有文件中的定义/声明/代码
    ANALYZE = "ANALYZE"  # 分析文件/错误，给出结论（不强制编译）
    COMPILE = "COMPILE"  # 以编译通过为主要目标


@dataclass
class TaskSpec:
    """通用 Rocq 任务描述。

    解耦自 TaskCompletionChecker 的“目标文件 + 定理范围”假设，可表达
    证明、创建、修改、分析、编译等多种任务。
    """
    task_type: str = TaskType.ANALYZE
    source_files: list = field(default_factory=list)    # 输入/基础文件（绝对路径）
    target_files: list = field(default_factory=list)    # 输出/目标文件（绝对路径）
    target_theorems: list = field(default_factory=list) # 目标定理名（PROVE 用）
    modification_target: str = ""                       # 要修改的对象名（MODIFY 用）
    description: str = ""                               # 自然语言任务描述
    completion_criteria: str = ""                       # 完成标准（自然语言）
    raw_message: str = ""                               # 原始用户消息

    def known_type(self):
        return (self.task_type or "").upper() in (
            TaskType.PROVE, TaskType.CREATE, TaskType.MODIFY,
            TaskType.ANALYZE, TaskType.COMPILE
        )

    def primary_target(self):
        """返回主目标文件路径（target 优先，其次 source）。"""
        if self.target_files:
            return self.target_files[0]
        if self.source_files:
            return self.source_files[0]
        return None


# ========== 3. FSM 状态机：控制任务终止条件 ==========
# COMPILE_SUCCESS/COMPILE_FAIL 仅作为“是否已通过编译”的中间状态；
# 最终是否成功由 TaskCompletionManager 按任务类型判定。
class AgentFSM:
    INIT = "INIT"                    # 任务初始状态
    EXECUTING = "EXECUTING"          # 正在执行中（文件已修改，编译结果已过期）
    COMPILE_SUCCESS = "COMPILE_SUCCESS"  # 中间状态：最近一次编译成功
    COMPILE_FAIL = "COMPILE_FAIL"    # 中间状态：最近一次编译失败
    TASK_SUCCESS = "TASK_SUCCESS"    # 最终状态：经程序检查任务成功
    TASK_FAIL = "TASK_FAIL"          # 最终状态：任务失败

    def __init__(self):
        self.state = AgentFSM.INIT

    def on_file_modified(self):
        """文件被创建/修改后，之前的编译结果失效。"""
        self.state = AgentFSM.EXECUTING

    def on_compile_success(self):
        self.state = AgentFSM.COMPILE_SUCCESS

    def on_compile_fail(self):
        self.state = AgentFSM.COMPILE_FAIL

    def on_task_success(self):
        self.state = AgentFSM.TASK_SUCCESS

    def on_task_fail(self):
        self.state = AgentFSM.TASK_FAIL

    @property
    def can_finish(self):
        """编译这一中间条件是否已满足；分析类任务可绕过此门槛。"""
        return self.state == AgentFSM.COMPILE_SUCCESS

    @property
    def must_continue(self):
        """编译失败或从未编译过，LLM 声称完成时需强制继续。"""
        return self.state != AgentFSM.COMPILE_SUCCESS


# ========== 3a. 任务完成检查器：验证目标定理是否全部完成 ==========

def _theorem_number(name):
    """提取定理名中的主编号：MKT4 -> 4, MKT4' -> 4, MKT49a -> 49, Lemma50' -> 50。"""
    m = re.match(r'[A-Za-z]+(\d+)', name)
    return int(m.group(1)) if m else None


class TaskCompletionChecker:
    """任务完成检查器：验证目标文件中指定定理是否全部完成证明。"""

    def __init__(self):
        self.target_file = None
        self.target_theorems = []
        self.start_theorem = None
        self.end_theorem = None
        self.missing_theorem = None     # 范围内找不到的端点定理名
        self.existing_theorems = []     # 端点缺失时退化的“已存在定理”子集
        self.task_type = "open"         # prove_existing / extend_file / new_file / open
        self.goal = ""                  # 自然语言目标（原始用户消息）
        self.base_files = []            # 要 import 的 .v 文件绝对路径
        self.output_file = None         # 新建文件路径（new_file 任务）

    def parse_task(self, user_message: str, fallback_file: str = None):
        """从用户消息中解析目标任务：目标文件 + 定理范围（可空）+ 任务类型。

        fallback_file: 当消息中未显式给出 .v 路径时继承该文件（用于“继续完成 A到B”这类
        省略路径的指令，避免被误判为“继续旧任务”）。

        任务类型：
        - prove_existing：点名了定理（或“所有/全部定理”）→ 严格模式（不改定义、不建文件）
        - new_file      ：含“新生成/新建/以X为基础/基于”等 → 宽松模式，可建文件
        - extend_file   ：仅引用文件并要求证明、未点名定理 → 宽松模式
        - open          ：无文件、纯自然语言描述 → 宽松模式
        """
        self.goal = user_message

        # 1. 提取所有 .v 文件路径（绝对路径，含盘符），并设置目标文件
        files = re.findall(r'[A-Za-z]:\\[^\s"\']*\.v', user_message)
        self.base_files = [f.strip('"\'') for f in files]
        if self.base_files:
            self.target_file = self.base_files[0]
        elif fallback_file:
            self.target_file = fallback_file

        # 2. 提取定理范围：支持 到/至/和...之间/与...之间/从...到/to/between...and
        # 使用 [A-Za-z0-9_] 而非 \w，因为 Python 3 的 \w 会匹配中文字符
        range_patterns = [
            # --- 定理前缀 + 到/至 ---
            r'定理\s*([A-Za-z0-9_]+[\']?)\s*到\s*(?:定理\s*)?([A-Za-z0-9_]+[\']?)',
            r'定理\s*([A-Za-z0-9_]+[\']?)\s*至\s*(?:定理\s*)?([A-Za-z0-9_]+[\']?)',
            # --- 定理前缀 + 和/与（不含"之间"：支持"定理A和定理B的证明"等）---
            r'定理\s*([A-Za-z0-9_]+[\']?)\s*和\s*(?:定理\s*)?([A-Za-z0-9_]+[\']?)',
            r'定理\s*([A-Za-z0-9_]+[\']?)\s*与\s*(?:定理\s*)?([A-Za-z0-9_]+[\']?)',
            # --- 定理前缀 + 和/与...之间 ---
            r'定理\s*([A-Za-z0-9_]+[\']?)\s*和\s*(?:定理\s*)?([A-Za-z0-9_]+[\']?)\s*之间',
            r'定理\s*([A-Za-z0-9_]+[\']?)\s*与\s*(?:定理\s*)?([A-Za-z0-9_]+[\']?)\s*之间',
            # --- 无前缀 + 和/与（不含"之间"）---
            r'([A-Za-z0-9_]+[\']?)\s*和\s*(?:定理\s*)?([A-Za-z0-9_]+[\']?)',
            r'([A-Za-z0-9_]+[\']?)\s*与\s*(?:定理\s*)?([A-Za-z0-9_]+[\']?)',
            # --- 无前缀 + 到/至 + 之间 ---
            r'([A-Za-z0-9_]+[\']?)\s*到\s*(?:定理\s*)?([A-Za-z0-9_]+[\']?)\s*之间',
            r'([A-Za-z0-9_]+[\']?)\s*至\s*(?:定理\s*)?([A-Za-z0-9_]+[\']?)\s*之间',
            # --- 无前缀 + 和/与 + 之间 ---
            r'([A-Za-z0-9_]+[\']?)\s*和\s*(?:定理\s*)?([A-Za-z0-9_]+[\']?)\s*之间',
            r'([A-Za-z0-9_]+[\']?)\s*与\s*(?:定理\s*)?([A-Za-z0-9_]+[\']?)\s*之间',
            # --- 无前后缀 + 到/至 ---
            r'([A-Za-z0-9_]+[\']?)\s*到\s*(?:定理\s*)?([A-Za-z0-9_]+[\']?)',
            r'([A-Za-z0-9_]+[\']?)\s*至\s*(?:定理\s*)?([A-Za-z0-9_]+[\']?)',
            # --- 从...到 ---
            r'从\s*([A-Za-z0-9_]+[\']?)\s*到\s*(?:定理\s*)?([A-Za-z0-9_]+[\']?)',
            # --- 英文 ---
            r'([A-Za-z0-9_]+[\']?)\s+to\s+([A-Za-z0-9_]+[\']?)',
            r'between\s+([A-Za-z0-9_]+[\']?)\s+and\s+([A-Za-z0-9_]+[\']?)',
        ]
        for pattern in range_patterns:
            m = re.search(pattern, user_message)
            if m:
                self.start_theorem = m.group(1)
                self.end_theorem = m.group(2)
                break

        # 3. 如果没有范围，检查是否是单个定理
        if not self.start_theorem:
            single_patterns = [
                r'定理\s*([A-Za-z0-9_]+[\']*)\s*(?:的证明|证明)',
                r'证明\s*定理\s*([A-Za-z0-9_]+[\']*)',
            ]
            for pattern in single_patterns:
                m = re.search(pattern, user_message)
                if m:
                    self.start_theorem = m.group(1)
                    self.end_theorem = m.group(1)
                    break

        # 4. 分类任务类型，并枚举目标定理（仅 prove_existing 需要）
        new_file_hint = bool(re.search(
            r'新(?:生成|建|创建)|生成(?:一个|新的|新)?[^\n]{0,30}?\.v|以[^\n]{0,20}为基础|基于',
            user_message
        ))

        if self.start_theorem and self.end_theorem:
            # 点名了定理 → prove_existing
            self.task_type = "prove_existing"
            if self.target_file:
                self._enumerate_theorems()
        elif self.target_file and not new_file_hint:
            # 引用了文件但未点名定理：区分“所有定理”与“继续/补证”
            has_range_language = bool(
                re.search(r'[A-Za-z0-9_]+\s*[到至]\s*[A-Za-z0-9_]+', user_message) or
                re.search(r'[A-Za-z0-9_]+\s*[和与]\s*[A-Za-z0-9_]+\s*之间', user_message) or
                re.search(r'[A-Za-z0-9_]+\s+to\s+[A-Za-z0-9_]+', user_message) or
                re.search(r'从\s*[A-Za-z0-9_]+\s*到', user_message) or
                re.search(r'之间', user_message)
            )
            if (not has_range_language and
                re.search(r'所有(?:定理|theorem)|全部(?:定理|theorem)|all\s+(?:theorems|lemmas)',
                          user_message, re.IGNORECASE)):
                self.task_type = "prove_existing"
                self._enumerate_all_theorems()
            else:
                self.task_type = "extend_file"
        elif new_file_hint:
            self.task_type = "new_file"
        elif self.target_file:
            self.task_type = "extend_file"
        else:
            self.task_type = "open"

    def _enumerate_theorems(self):
        """在目标文件中定位 start/end 定理，提取范围内的所有定理名。

        若起点或终点定理不存在，记录 missing_theorem；终点缺失时退化为
        “已存在定理”子集存入 existing_theorems（但不自动作为有效目标）。
        """
        all_theorems = self._find_all_theorems()
        if not all_theorems:
            return
        try:
            start_idx = all_theorems.index(self.start_theorem)
        except ValueError:
            self.missing_theorem = self.start_theorem
            self.target_theorems = []
            self.existing_theorems = []
            return
        try:
            end_idx = all_theorems.index(self.end_theorem)
        except ValueError:
            self.missing_theorem = self.end_theorem
            self.existing_theorems = self._enumerate_existing_range(
                all_theorems, start_idx, self.start_theorem, self.end_theorem
            )
            self.target_theorems = []
            return
        if start_idx <= end_idx:
            self.target_theorems = all_theorems[start_idx:end_idx + 1]
        else:
            self.target_theorems = all_theorems[end_idx:start_idx + 1]
        self.existing_theorems = list(self.target_theorems)
        self.missing_theorem = None

    def _enumerate_existing_range(self, all_theorems, start_idx, start_name, end_name):
        """端点缺失时，从起点起取编号在 [start_num, end_num] 内的已存在定理。"""
        start_num = _theorem_number(start_name)
        end_num = _theorem_number(end_name)
        if start_num is None or end_num is None:
            return []
        result = []
        for name in all_theorems[start_idx:]:
            num = _theorem_number(name)
            if num is None:
                continue
            if num < start_num:
                continue
            if num > end_num:
                break
            result.append(name)
        return result

    def _theorems_until_number(self, all_theorems, start_num, end_num):
        """返回编号在 (start_num, end_num] 内的已存在定理（用于“继续到X”范围扩展）。"""
        result = []
        for name in all_theorems:
            num = _theorem_number(name)
            if num is None:
                continue
            if num <= start_num:
                continue
            if num > end_num:
                break
            result.append(name)
        return result

    def extend_to(self, end_name):
        """将当前任务范围“继续”扩展到新终点 end_name，返回是否找到新定理。

        扩展后的目标是编号严格大于当前已有目标最大编号、且不超过 end_name 编号的
        已存在定理；成功时替换 target_theorems 并清除 missing_theorem。
        """
        if not self.target_file:
            return False
        end_num = _theorem_number(end_name)
        if end_num is None:
            self.missing_theorem = end_name
            return False
        all_theorems = self._find_all_theorems()
        if not all_theorems:
            return False
        prev_max = 0
        for t in self.target_theorems:
            n = _theorem_number(t)
            if n is not None and n > prev_max:
                prev_max = n
        new_targets = self._theorems_until_number(all_theorems, prev_max, end_num)
        if not new_targets:
            if end_name not in all_theorems:
                self.missing_theorem = end_name
            return False
        self.target_theorems = new_targets
        self.missing_theorem = None
        return True

    def resolve_to_existing(self):
        """将“端点缺失”的待续任务解析为已存在定理范围。返回是否成功。"""
        if not self.existing_theorems:
            return False
        self.target_theorems = list(self.existing_theorems)
        self.missing_theorem = None
        return True

    def has_pending_missing(self):
        """是否存在“端点缺失但可退化为已存在定理”的待续任务。"""
        return self.missing_theorem is not None and len(self.existing_theorems) > 0

    def _enumerate_all_theorems(self):
        """枚举目标文件中的所有定理。"""
        self.target_theorems = self._find_all_theorems()

    def _find_all_theorems(self):
        """在目标文件中查找所有定理/引理声明，返回名称列表。"""
        if not self.target_file:
            return []
        try:
            with open(self.target_file, 'r', encoding='utf-8') as f:
                content = f.read()
        except Exception:
            return []
        theorems = []
        for m in re.finditer(
            r'^\s*(?:Theorem|Lemma|Corollary|Proposition|Example|Remark|Fact)\s+([A-Za-z0-9_]+[\']?)',
            content, re.MULTILINE
        ):
            theorems.append(m.group(1))
        return theorems

    def count_completed(self):
        """返回目标定理中已完成证明（Proof. ... Qed.）的数量。"""
        if not self.target_file or not self.target_theorems:
            return 0
        try:
            with open(self.target_file, 'r', encoding='utf-8') as f:
                content = f.read()
        except Exception:
            return 0
        count = 0
        for thm_name in self.target_theorems:
            if self._check_theorem_proof(content, thm_name) == "complete":
                count += 1
        return count

    def check_completion(self):
        """
        检查任务是否完成。

        prove_existing：逐个定理验证 Proof. ... Qed. 且编译通过；
        其余类型：编译通过 + 无 Admitted + LLM 自检目标已达成。

        Returns:
            (all_done: bool, details: str)
        """
        if self.task_type != "prove_existing":
            return self._check_general_completion()

        if not self.target_file:
            return True, ""

        if not self.target_theorems:
            return True, ""

        try:
            with open(self.target_file, 'r', encoding='utf-8') as f:
                content = f.read()
        except Exception as e:
            return False, f"无法读取目标文件 {self.target_file}：{e}"

        incomplete = []
        admitted_theorems = []

        for thm_name in self.target_theorems:
            status = self._check_theorem_proof(content, thm_name)
            if status == "incomplete":
                incomplete.append(thm_name)
            elif status == "admitted":
                admitted_theorems.append(thm_name)

        compile_ok = self._compile_check()

        details_parts = []
        all_done = True

        completed = len(self.target_theorems) - len(incomplete) - len(admitted_theorems)
        details_parts.append(
            f"进度：{completed}/{len(self.target_theorems)} 个定理已完成。"
        )

        if incomplete:
            all_done = False
            details_parts.append(
                f"以下定理证明不完整（缺少 Proof. ... Qed.）：{', '.join(incomplete[:10])}"
            )

        if admitted_theorems:
            all_done = False
            details_parts.append(
                f"以下定理使用了 Admitted：{', '.join(admitted_theorems[:10])}"
            )

        if not compile_ok:
            all_done = False
            details_parts.append("目标文件编译未通过。")

        if all_done:
            details_parts.append(
                f"所有 {len(self.target_theorems)} 个目标定理均已完成证明且编译通过。"
            )

        return all_done, "\n".join(details_parts)

    def _check_theorem_proof(self, content, thm_name):
        """
        检查单个定理的证明状态。

        Returns: "complete" | "incomplete" | "admitted" | "not_found"
        """
        pattern = (
            rf'^\s*(?:Theorem|Lemma|Corollary|Proposition|Example|Remark|Fact)\s+'
            rf'{re.escape(thm_name)}\b'
        )
        m = re.search(pattern, content, re.MULTILINE)
        if not m:
            return "not_found"

        thm_start = m.start()
        after_thm = content[thm_start:]

        # 找到下一个定理声明作为边界
        next_thm = re.search(
            r'^\s*(?:Theorem|Lemma|Corollary|Proposition|Example|Remark|Fact)\s+[A-Za-z0-9_]+',
            after_thm[len(m.group()):],
            re.MULTILINE
        )

        if next_thm:
            thm_content = after_thm[:len(m.group()) + next_thm.start()]
        else:
            thm_content = after_thm

        if re.search(r'\bAdmitted\.', thm_content):
            return "admitted"

        if re.search(r'\bProof\.', thm_content) and re.search(r'\b(?:Qed|Defined)\.', thm_content):
            return "complete"

        return "incomplete"

    def _compile_check_file(self, filename):
        """独立编译检查指定文件（不依赖 FSM 状态）。"""
        if not filename or not os.path.isfile(filename):
            return False
        coqc_path = r"D:\Coq\bin\coqc.exe"
        if not os.path.isfile(coqc_path):
            return False
        returncode = _run_coqc(coqc_path, filename)[0]
        return returncode == 0

    def _compile_check(self):
        """独立编译检查目标文件（不依赖 FSM 状态）。"""
        return self._compile_check_file(self.target_file)

    def _check_general_completion(self):
        """一般任务完成核验：编译通过 + 无 Admitted + LLM 判定目标已达成。"""
        work_file = self.output_file or self.target_file
        if not work_file or not os.path.isfile(work_file):
            return False, "尚未生成/定位到可编译的 .v 文件。"

        if not self._compile_check_file(work_file):
            return False, "目标文件编译未通过。"

        try:
            with open(work_file, 'r', encoding='utf-8') as f:
                content = f.read()
        except Exception as e:
            return False, f"无法读取 {work_file}：{e}"

        admitted = _find_admitted(content)
        if admitted:
            return False, f"文件仍含未完成证明（{', '.join(admitted)}），不允许留 Admitted。"

        ok, reason = _llm_goal_check(self.goal, content)
        return ok, reason

    def has_target(self):
        """是否指定了有效任务目标。

        prove_existing 需要“目标文件 + 非空定理范围”；其余类型只需有目标描述/文件。
        """
        if self.task_type == "prove_existing":
            return self.target_file is not None and len(self.target_theorems) > 0
        return self.task_type in ("new_file", "extend_file", "open") and bool(self.goal)

    def format_context(self):
        """生成任务上下文描述，用于注入 Agent Prompt。"""
        if not self.has_target():
            return ""
        if self.task_type == "prove_existing":
            thm_list = ', '.join(self.target_theorems[:10])
            if len(self.target_theorems) > 10:
                thm_list += f' ... （共 {len(self.target_theorems)} 个）'
            return (
                f"## 任务目标\n"
                f"- 目标文件：{self.target_file}\n"
                f"- 目标定理（{len(self.target_theorems)} 个）：{thm_list}\n"
                f"- 所有定理必须完成 Proof. ... Qed. 且编译通过，任务才算完成。\n"
            )
        lines = ["## 任务目标"]
        if self.goal:
            lines.append(f"- 目标：{self.goal}")
        if self.base_files:
            lines.append(f"- 基础文件：{', '.join(self.base_files)}")
        if self.task_type == "new_file":
            lines.append("- 需要新建一个 .v 文件完成证明（可 Import 基础文件）")
        lines.append("- 完成标准：编译通过 + 无 Admitted + 满足上述目标。")
        return "\n".join(lines) + "\n"


class TaskCompletionManager:
    """统一的任务完成检查器：按 TaskSpec.task_type 分发到不同的完成检查逻辑。

    TaskCompletionChecker 仅保留为 PROVE 类任务的证明完成检查器；
    CREATE/MODIFY/ANALYZE/COMPILE 各自有独立判定，不再把“编译成功”等同于“任务成功”。
    """

    def __init__(self):
        self.prove_checker = TaskCompletionChecker()
        self._baseline_content = {}   # MODIFY 任务：修改前的文件内容快照 {filepath: content}

    def configure_for_spec(self, spec):
        """在任务开始 / TaskSpec 变化时同步检查器状态。

        PROVE：同步 prove_checker；MODIFY：记录修改前的基线内容，
        用于程序化判断“文件是否真的被修改”。
        """
        t = (spec.task_type or "").upper()
        self._baseline_content = {}
        if t == TaskType.PROVE:
            pc = self.prove_checker
            pc.target_file = spec.primary_target()
            pc.target_theorems = list(spec.target_theorems)
            if pc.target_file and not pc.target_theorems:
                pc.target_theorems = pc._find_all_theorems()
            pc.task_type = "prove_existing"
            pc.goal = spec.description or spec.raw_message
        elif t == TaskType.MODIFY:
            work = spec.primary_target()
            if work and os.path.isfile(work):
                content = _read_file_safe(work)
                if content is not None:
                    self._baseline_content[work] = content

    def check_completion(self, spec, work_filename=None, analysis_text=None):
        """返回 (all_done, details)。"""
        t = (spec.task_type or "").upper()
        if t == TaskType.PROVE:
            return self._check_prove(spec)
        if t == TaskType.CREATE:
            return self._check_create(spec, work_filename)
        if t == TaskType.MODIFY:
            return self._check_modify(spec, work_filename)
        if t == TaskType.ANALYZE:
            return self._check_analyze(analysis_text)
        if t == TaskType.COMPILE:
            return self._check_compile(spec, work_filename)
        return self._check_general(spec, work_filename)

    def _check_prove(self, spec):
        self.configure_for_spec(spec)
        pc = self.prove_checker
        if not pc.target_file:
            return False, "未指定目标文件，无法进行证明完成检查。"
        if not os.path.isfile(pc.target_file):
            return False, f"目标文件《{pc.target_file}》不存在。"
        if not pc.target_theorems:
            return False, f"目标文件《{pc.target_file}》中未找到任何定理声明。"
        return pc.check_completion()

    def _missing_proofs(self, content, theorem_names):
        """返回 theorem_names 中在 content 里缺少完整 Proof..Qed 证明的定理名。"""
        missing = []
        for name in theorem_names:
            if self.prove_checker._check_theorem_proof(content, name) != "complete":
                missing.append(name)
        return missing

    def _check_create(self, spec, work_filename):
        work = work_filename or spec.primary_target()
        if not work:
            return False, "尚未确定要创建的目标文件。"
        if not os.path.isfile(work):
            return False, f"目标文件《{work}》尚未创建。"
        if not self.prove_checker._compile_check_file(work):
            return False, f"目标文件《{work}》编译未通过。"
        content = _read_file_safe(work)
        if content is None:
            return False, f"无法读取《{work}》。"
        if not content.strip():
            return False, f"目标文件《{work}》内容为空。"
        admitted = _find_admitted(content)
        if admitted:
            return False, f"文件仍含未完成证明（{', '.join(admitted)}），不允许留 Admitted。"
        # 若用户点明了要证明的定理，程序化检查这些定理是否已有完整证明
        missing = self._missing_proofs(content, spec.target_theorems)
        if missing:
            return False, f"以下定理在目标文件中缺少完整 Proof. ... Qed. 证明：{', '.join(missing[:10])}"
        # LLM 目标自检仅作辅助确认
        ok, reason = _llm_goal_check(spec.description or spec.raw_message, content)
        return ok, reason

    def _check_modify(self, spec, work_filename):
        work = work_filename or spec.primary_target()
        if not work or not os.path.isfile(work):
            return False, "未定位到要修改的目标文件。"
        if not self.prove_checker._compile_check_file(work):
            return False, f"目标文件《{work}》编译未通过。"
        content = _read_file_safe(work)
        if content is None:
            return False, f"无法读取《{work}》。"
        # 程序化判断：文件是否真的被修改（与任务开始时基线比较）
        baseline = self._baseline_content.get(work)
        if baseline is not None and baseline == content:
            return False, "目标文件内容未发生变化，修改尚未应用。"
        # 程序化判断：不允许留 Admitted
        admitted = _find_admitted(content)
        if admitted:
            return False, f"文件仍含未完成证明（{', '.join(admitted)}），不允许留 Admitted。"
        # LLM 目标自检仅作辅助确认
        ok, reason = _llm_goal_check(spec.description or spec.raw_message, content)
        return ok, reason

    def _check_analyze(self, analysis_text):
        text = (analysis_text or "").strip()
        if not text:
            return False, "尚未给出分析结论。"
        if len(text) < 30:
            return False, "分析内容过短，请给出包含错误原因、相关位置和修复建议的完整分析。"
        missing = []
        if not self._has_error_cause(text):
            missing.append("错误原因")
        if not self._has_location(text):
            missing.append("相关位置（行号/文件路径）")
        if not self._has_fix_suggestion(text):
            missing.append("修复建议")
        if missing:
            return False, f"分析不完整，缺少：{'、'.join(missing)}。请补充后重新输出完整分析。"
        return True, "分析已完成：包含错误原因、位置与修复建议。"

    def _has_error_cause(self, text):
        return bool(re.search(
            r'错误|报错|失败|问题|原因|因为|error|cannot|unbound|not\s+found|'
            r'type\s+error|unif|incompatible|ill[- ]?typed|universe',
            text, re.IGNORECASE))

    def _has_location(self, text):
        return bool(
            re.search(r'第\s*\d+\s*行|line\s*\d+|\b\d+\s*行|:\d+', text, re.IGNORECASE)
            or re.search(r'[A-Za-z]:\\[^\s"\']*\.v', text)
            or re.search(r'位置|定位|行号|位于|出现在', text)
        )

    def _has_fix_suggestion(self, text):
        return bool(re.search(
            r'建议|应该|可以|改为|改成|修改|换成|需要|替换|fix|change|replace|将.*改',
            text, re.IGNORECASE))

    def _check_compile(self, spec, work_filename):
        work = work_filename or spec.primary_target()
        if not work:
            return False, "未指定要编译的文件。"
        if not os.path.isfile(work):
            return False, f"文件《{work}》不存在。"
        if not self.prove_checker._compile_check_file(work):
            return False, f"文件《{work}》编译未通过。"
        return True, f"文件《{work}》编译通过。"

    def _check_general(self, spec, work_filename):
        work = work_filename or spec.primary_target()
        if not work or not os.path.isfile(work):
            return False, "尚未生成/定位到可编译的 .v 文件。"
        if not self.prove_checker._compile_check_file(work):
            return False, "目标文件编译未通过。"
        content = _read_file_safe(work)
        if content is None:
            return False, f"无法读取《{work}》。"
        admitted = _find_admitted(content)
        if admitted:
            return False, f"文件仍含未完成证明（{', '.join(admitted)}），不允许留 Admitted。"
        ok, reason = _llm_goal_check(spec.description or spec.raw_message, content)
        return ok, reason


# ========== 3b. 通用任务解析（LLM 生成 TaskSpec） ==========

def _extract_file_paths(text):
    """提取消息中所有 .v 文件的绝对路径（含盘符）。"""
    return [m.strip('"\'') for m in re.findall(r'[A-Za-z]:\\[^\s"\']*\.v', text)]


def _clean_json_block(text):
    """从 LLM 回复中提取第一个 { 到最后一个 } 之间的 JSON 文本。"""
    if not text:
        return ""
    start = text.find('{')
    end = text.rfind('}')
    if start == -1 or end == -1 or end < start:
        return ""
    return text[start:end + 1]


def _task_spec_from_obj(obj, user_message, files, fallback):
    """将 LLM 返回的 dict 归一化为 TaskSpec，并合并正则提取到的文件路径。"""
    raw_type = str(obj.get("task_type", "")).upper()
    allowed = {TaskType.PROVE, TaskType.CREATE, TaskType.MODIFY,
               TaskType.ANALYZE, TaskType.COMPILE}
    task_type = raw_type if raw_type in allowed else TaskType.ANALYZE

    def norm_list(v):
        if isinstance(v, str):
            return [v] if v else []
        if isinstance(v, list):
            return [str(x) for x in v if x]
        return []

    source = norm_list(obj.get("source_files", []))
    target = norm_list(obj.get("target_files", []))
    for f in files:
        if f not in source and f not in target:
            source.append(f)

    theorems = norm_list(obj.get("target_theorems", []))

    # PROVE/MODIFY/COMPILE 未给出 target 但有 source 时，默认以首个 source 为目标
    if not target and task_type in (TaskType.PROVE, TaskType.MODIFY, TaskType.COMPILE) and source:
        target.append(source[0])
        if len(source) > 1:
            source = source[1:]

    return TaskSpec(
        task_type=task_type,
        source_files=source,
        target_files=target,
        target_theorems=theorems,
        modification_target=str(obj.get("modification_target", "") or ""),
        description=str(obj.get("description", "") or "").strip() or user_message.strip(),
        completion_criteria=str(obj.get("completion_criteria", "") or "").strip(),
        raw_message=user_message,
    )


def _heuristic_task_spec(user_message, files, fallback=None):
    """LLM 解析失败时的回退：按关键词 + 文件路径粗分类。"""
    text = user_message
    if re.search(r'新(?:生成|建|创建)|生成|基于|以[^\n]{0,20}为基础', text):
        task_type = TaskType.CREATE
    elif re.search(r'修改|改一下|改掉|写错|错(?:了|误)|纠正', text):
        task_type = TaskType.MODIFY
    elif re.search(r'检查|分析|为什么|为何|报错|错误|error', text, re.IGNORECASE):
        task_type = TaskType.ANALYZE
    elif re.search(r'定理|引理|证明|theorem|lemma|proof', text, re.IGNORECASE):
        task_type = TaskType.PROVE
    elif re.search(r'编译|compile', text, re.IGNORECASE):
        task_type = TaskType.COMPILE
    else:
        task_type = TaskType.ANALYZE

    source = list(files)
    target = []
    if task_type in (TaskType.PROVE, TaskType.MODIFY, TaskType.COMPILE) and files:
        target = [files[0]]
        source = files[1:] if len(files) > 1 else []

    return TaskSpec(
        task_type=task_type,
        source_files=source,
        target_files=target,
        target_theorems=[],
        modification_target="",
        description=user_message.strip(),
        completion_criteria="",
        raw_message=user_message,
    )


def parse_task_spec(user_message, fallback=None):
    """通用任务解析入口：优先用 LLM 将自然语言解析为 TaskSpec，失败时回退到启发式。"""
    files = _extract_file_paths(user_message)
    prompt = (
        "你是 Rocq/Coq 任务解析器。请根据用户指令输出一个 JSON 对象（不要输出其他文字），"
        "字段如下：\n"
        "- task_type: 只能是 PROVE / CREATE / MODIFY / ANALYZE / COMPILE 之一\n"
        "- source_files: 字符串数组，输入/基础文件绝对路径\n"
        "- target_files: 字符串数组，输出/目标文件绝对路径\n"
        "- target_theorems: 字符串数组，需要证明的定理名\n"
        "- modification_target: 字符串，要修改的定义/声明/代码名称（没有则为空字符串）\n"
        "- description: 字符串，一句话任务描述\n"
        "- completion_criteria: 字符串，完成标准（没有则为空字符串）\n\n"
        "判定规则：\n"
        "- 证明指定定理 → PROVE；新建文件并写内容/证明 → CREATE\n"
        "- 修改已有定义/声明/代码 → MODIFY；只分析/找错误 → ANALYZE；以编译为目标 → COMPILE\n\n"
        f"用户指令：\n{user_message}\n\n"
        f"消息中已识别的 .v 文件路径：{files}\n"
    )
    try:
        response = client.chat.completions.create(
            model="deepseek-flash",
            messages=[{"role": "user", "content": prompt}],
            temperature=0,
        )
        raw = (response.choices[0].message.content or "").strip()
        obj = json.loads(_clean_json_block(raw))
        return _task_spec_from_obj(obj, user_message, files, fallback)
    except Exception as e:
        print(f"【任务解析】LLM 解析失败（{e}），回退到启发式解析。")
        return _heuristic_task_spec(user_message, files, fallback)


def _print_task_spec(spec):
    print(f"【任务解析】任务类型：{spec.task_type}")
    print(f"【任务解析】描述：{spec.description[:80]}")
    if spec.source_files:
        print(f"【任务解析】源/基础文件：{', '.join(spec.source_files)}")
    if spec.target_files:
        print(f"【任务解析】目标文件：{', '.join(spec.target_files)}")
    if spec.target_theorems:
        thm = ', '.join(spec.target_theorems[:10])
        if len(spec.target_theorems) > 10:
            thm += ' ...'
        print(f"【任务解析】目标定理（{len(spec.target_theorems)} 个）：{thm}")
    if spec.modification_target:
        print(f"【任务解析】修改对象：{spec.modification_target}")


# ========== 4. 新增：尝试历史、错误分类、相似度检测 ==========

def _similarity(text1, text2):
    """简单的编辑距离相似度（0~1），用于检测重复修改。"""
    if text1 == text2:
        return 1.0
    if not text1 or not text2:
        return 0.0
    # 去除空白后比较
    t1 = ''.join(text1.split())
    t2 = ''.join(text2.split())
    if t1 == t2:
        return 0.95  # 仅空白差异，视为高度重复
    if len(t1) < 5 or len(t2) < 5:
        return 0.0
    # Levenshtein 距离
    m, n = len(t1), len(t2)
    if m > n:
        t1, t2 = t2, t1
        m, n = n, m
    prev = list(range(n + 1))
    for i in range(1, m + 1):
        curr = [i] + [0] * n
        for j in range(1, n + 1):
            cost = 0 if t1[i - 1] == t2[j - 1] else 1
            curr[j] = min(prev[j] + 1, curr[j - 1] + 1, prev[j - 1] + cost)
        prev = curr
    distance = prev[n]
    max_len = max(m, n)
    return 1.0 - distance / max_len


class AttemptHistory:
    """记录每次修改尝试，支持重复检测和失败分析。"""

    def __init__(self, max_history=3):
        self.attempts = []  # [{round, edit, compile_error, goal, error_category, raw_response}]
        self.max_history = max_history

    def record(self, round_num, edit="", compile_error="", goal="", error_category="",
               raw_llm_response=""):
        if not compile_error:
            return  # 只记录失败尝试，编译成功不记录
        self.attempts.append({
            "round": round_num,
            "edit": edit,
            "compile_error": compile_error,
            "goal": goal,
            "error_category": error_category,
            "raw_response": raw_llm_response[:500] if raw_llm_response else ""
        })
        if len(self.attempts) > self.max_history:
            self.attempts = self.attempts[-self.max_history:]

    def get_recent_failures(self, n=3):
        """返回最近 n 次失败尝试（不含编译成功的）。"""
        failures = [a for a in self.attempts if a["compile_error"]]
        return failures[-n:]

    def get_last_error(self):
        for a in reversed(self.attempts):
            if a["compile_error"]:
                return a
        return None

    def get_last_goal(self):
        for a in reversed(self.attempts):
            if a["goal"]:
                return a["goal"]
        return None

    def is_duplicate(self, new_edit, threshold=0.92):
        """检查 new_edit 是否与最近尝试高度相似。"""
        recent_edits = [a["edit"] for a in self.attempts[-5:] if a["edit"]]
        for old_edit in recent_edits:
            if _similarity(old_edit, new_edit) >= threshold:
                return True
        return False

    def count_consecutive_same_error_category(self):
        """连续出现相同错误类型的次数。"""
        if len(self.attempts) < 2:
            return 1
        count = 1
        last_cat = self.attempts[-1]["error_category"]
        if not last_cat:
            return 1
        for a in reversed(self.attempts[:-1]):
            if a["error_category"] == last_cat:
                count += 1
            else:
                break
        return count

    def count_consecutive_identical_error(self):
        """连续出现完全相同 compile_error 的次数。"""
        if len(self.attempts) < 2:
            return 1
        count = 1
        last_err = self.attempts[-1]["compile_error"]
        if not last_err:
            return 1
        for a in reversed(self.attempts[:-1]):
            if a["compile_error"] == last_err:
                count += 1
            else:
                break
        return count

    def count_consecutive_similar_edits(self, threshold=0.92):
        """连续生成相似修改的次数。"""
        if len(self.attempts) < 2:
            return 1
        count = 1
        last_edit = self.attempts[-1]["edit"]
        if not last_edit:
            return 1
        edits = [a["edit"] for a in self.attempts[-8:] if a["edit"]]
        for old_edit in reversed(edits[:-1]):
            if _similarity(old_edit, last_edit) >= threshold:
                count += 1
            else:
                break
        return count

    def should_force_strategy_change(self):
        """连续3次同类错误 → 需要切换策略。"""
        return self.count_consecutive_same_error_category() >= 3

    def should_early_stop(self):
        """提前终止：相同错误≥5次 或 相似修改≥3次。"""
        if self.count_consecutive_identical_error() >= 5:
            return True, "连续 5 次出现完全相同的编译错误，已陷入重复修改循环。"
        if self.count_consecutive_similar_edits(threshold=0.90) >= 3:
            return True, "连续 3 次生成几乎相同的修改，已陷入重复修改循环。"
        return False, ""

    def format_recent_failures(self, n=3):
        """将最近失败尝试格式化为 Prompt 文本。"""
        failures = self.get_recent_failures(n)
        if not failures:
            return ""
        lines = [
            "\n=== 以下修改已尝试过且失败，请不要再次生成相同或近似的修改 ===\n"
        ]
        for i, a in enumerate(failures):
            error_cat = f"（{a['error_category']}）" if a['error_category'] else ""
            edit_text = a['edit']
            if len(edit_text) > 400:
                edit_text = edit_text[:400] + "\n...[截断]"
            error_text = a['compile_error']
            if len(error_text) > 600:
                error_text = error_text[:600] + "\n...[截断]"
            lines.append(
                f"Attempt {i + 1} (第 {a['round']} 轮):\n"
                f"  修改内容：\n{edit_text}\n"
                f"  错误类型：{error_cat}\n"
                f"  错误信息：\n{error_text}\n"
            )
        lines.append("=== 失败历史结束 ===\n")
        return "\n".join(lines)

    def format_strategy_hint(self):
        """当同一思路反复失败时，生成策略切换提示。"""
        last_cat = self.attempts[-1]["error_category"] if self.attempts else ""
        count = self.count_consecutive_same_error_category()

        if count < 3:
            return ""

        hints = {
            "Timeout": (
                "\n【策略提示】证明脚本编译超时，很可能是某个 tactic 不终止或展开爆炸。请：\n"
                "- 检查 auto / eauto / trivial / firstorder 是否深搜爆炸\n"
                "- 检查 repeat 是否搭配了不递减的 tactic 导致死循环\n"
                "- 检查 compute / vm_compute / native_compute / simpl 是否展开过大\n"
                "- 用更受控的步骤（intros / destruct / induction / apply）替代自动搜索\n"
                "- 先用 get_coq_proof_state 查看当前 Goal，手动规划证明\n"
            ),
            "Rewrite Failure": (
                "\n【策略提示】连续多次 Rewrite 失败。请放弃 rewrite，考虑以下策略：\n"
                "- destruct / induction（对关键变量做归纳）\n"
                "- inversion（反转假设中的等式）\n"
                "- apply（直接应用已有引理）\n"
                "- assert（引入中间引理）\n"
                "- remember（给复杂表达式命名）\n"
                "- generalize dependent（泛化依赖假设）\n"
            ),
            "Unification Error": (
                "\n【策略提示】连续多次 Unification 失败。请检查：\n"
                "- 是否混淆了不同但相似的变量名？\n"
                "- 类型参数是否传递完整？\n"
                "- 是否需要对某个变量做 unfold / simpl 展开？\n"
                "- 尝试使用 apply ... with (...) 明确指定参数\n"
            ),
            "Type Error": (
                "\n【策略提示】连续多次类型错误。请检查：\n"
                "- 函数/引理的参数类型是否匹配？\n"
                "- 是否需要调整归纳假设的表述？\n"
                "- 尝试使用 Check / About 理解目标类型\n"
            ),
            "Tactic Failure": (
                "\n【策略提示】连续多次策略执行失败。请：\n"
                "- 先用 get_coq_proof_state 查看当前 Goal 和 hypotheses\n"
                "- 确认策略的前提条件是否满足\n"
                "- 考虑从更高层次重新组织证明结构\n"
            ),
        }

        for key, hint in hints.items():
            if key in (last_cat or ""):
                return hint

        return (
            "\n【策略提示】连续多次尝试均以相同类型失败。\n"
            "请放弃当前证明思路，重新设计证明策略，而不是继续微调已有代码。\n"
        )


# ========== 4a. 编译错误分类 ==========

def classify_compile_error(error_text):
    """将 coqc 编译错误分类，返回 (类别, 简短描述)。"""
    if not error_text:
        return "Unknown Error", error_text

    error_lower = error_text.lower()

    categories = [
        ("Timeout", [
            r"编译超时", r"超时", r"timed?\s*out", r"timeout",
        ]),
        ("Syntax Error", [
            r"syntax\s*error", r"illegal\s+character", r"unexpected\s+token",
            r"parse\s+error", r"ill[- ]?formed", r"expects",
            r"lexing:", r"illegal\s+begin",
        ]),
        ("Universe Error", [
            r"universe\s+inconsistency", r"universe\s+\w+\s+and\s+\w+\s+are\s+not",
            r"cannot\s+enforce", r"would\s+be\s+higher",
        ]),
        ("Cannot Find Reference", [
            r"cannot\s+find", r"unknown\s+identifier", r"not\s+found",
            r"reference\s+.*not", r"has\s+not\s+been\s+declared",
            r"unbound\s+reference",
        ]),
        ("Type Error", [
            r"type\s+error", r"has\s+type", r"is\s+not\s+a",
            r"incorrect\s+type", r"wrong\s+type", r"ill[- ]?typed",
            r"should\s+be\s+of\s+type", r"expected\s+type",
        ]),
        ("Unification Error", [
            r"unif", r"cannot\s+unify", r"unable\s+to\s+unify",
            r"cannot\s+be\s+applied", r"cannot\s+infer",
            r"different\s+instances", r"incompatible",
        ]),
        ("Rewrite Failure", [
            r"rewrite", r"found\s+no\s+subterm", r"no\s+subterm",
            r"does\s+not\s+match", r"setoid\s+rewrite",
        ]),
        ("Missing Identifier", [
            r"not\s+a\s+defined", r"undeclared", r"unbound",
            r"not\s+declared", r"unknown\s+variable",
        ]),
        ("Tactic Failure", [
            r"tactic\s+failure", r"no\s+more\s+subgoals",
            r"no\s+such\s+goal", r"cannot\s+apply",
            r"not\s+a\s+valid", r"does\s+not\s+apply",
            r"not\s+the\s+right", r"wrong\s+number\s+of",
            r"not\s+enough", r"too\s+many",
        ]),
        ("Incomplete Proof", [
            r"incomplete", r"attempt\s+to\s+save", r"still\s+have\s+subgoals",
            r"unsolved", r"remaining\s+subgoals", r"not\s+finished",
            r"admitted",
        ]),
    ]

    for category, regexes in categories:
        for regex in regexes:
            if re.search(regex, error_lower):
                # 提取错误的简短描述（第一行有效信息）
                lines = [l.strip() for l in error_text.split('\n') if l.strip()]
                short = lines[0] if lines else error_text[:200]
                if len(short) > 300:
                    short = short[:300] + "..."
                return category, short

    lines = [l.strip() for l in error_text.split('\n') if l.strip()]
    short = lines[0] if lines else error_text[:200]
    return "Unknown Error", short[:300]


# ========== 4b. 定理边界提取 ==========

def extract_theorem_context(content, error_line=None):
    """
    从文件中提取当前待证明定理及其上下文（前后各~25行）。
    返回用于构造 Prompt 的精简代码片段，不返回整个文件。
    """
    lines = content.split('\n')

    # 确定焦点行
    if error_line is not None and 1 <= error_line <= len(lines):
        focus = error_line - 1  # 转为0-index
    else:
        # 查找最后一个 Admitted 或 Proof. 之后的内容
        focus = None
        for i in range(len(lines) - 1, -1, -1):
            if re.match(r'^\s*(Admitted|Abort)\.', lines[i]):
                focus = i
                break
        if focus is None:
            # 查找最后一个 Proof.
            for i in range(len(lines) - 1, -1, -1):
                if re.match(r'^\s*Proof\.', lines[i]):
                    focus = i
                    break
        if focus is None:
            focus = len(lines) - 1

    # 向上查找当前 theorem/lemma 的声明
    theorem_start = None
    theorem_line_text = ""
    for i in range(focus, -1, -1):
        stripped = lines[i].strip()
        if re.match(
            r'^\s*(Theorem|Lemma|Corollary|Proposition|Example|Remark|Fact|Goal)\s+',
            stripped
        ):
            theorem_start = i
            theorem_line_text = stripped
            break

    if theorem_start is None:
        # 没找到 theorem，返回最后 60 行
        context_start = max(0, len(lines) - 60)
        return {
            "snippet": '\n'.join(lines[context_start:]),
            "theorem_line": "",
            "theorem_start": 0,
            "context_start": context_start,
            "context_end": len(lines),
            "focus_line": focus,
        }

    # 向前取 25 行作为上下文，向后取到 focus + 10 行
    context_start = max(0, theorem_start - 25)
    context_end = min(len(lines), max(focus + 10, theorem_start + 30))

    snippet = '\n'.join(lines[context_start:context_end])

    return {
        "snippet": snippet,
        "theorem_line": theorem_line_text,
        "theorem_start": theorem_start,
        "context_start": context_start,
        "context_end": context_end,
        "focus_line": focus,
    }


# ========== 4c. Planner 与 Executor Prompt 构建 ==========

# 存储最近一次 Planner 生成的证明计划，Executor 可复用
_plan_cache = {"plan": "", "theorem_line": "", "round": 0}

def build_planner_prompt(theorem_context, goal_text, user_goal):
    """构造 Planner 的 Prompt：分析 Goal，给出证明计划。"""
    return (
        "你是一位 Coq 定理证明策略专家。请分析以下证明目标并给出详细的证明计划。\n\n"
        f"## 待证明定理\n{theorem_context['theorem_line']}\n\n"
        f"## 当前 Goal\n{goal_text}\n\n"
        f"## 周围代码上下文\n```coq\n{theorem_context['snippet']}\n```\n\n"
        f"## 用户目标\n{user_goal}\n\n"
        "请输出证明计划（不要输出完整代码，只需策略步骤）：\n"
        "1. 核心思路（induction / destruct / rewrite / apply / assert / ...）\n"
        "2. 关键步骤序列（策略名称 + 作用简要说明）\n"
        "3. 可能的风险点和备选方案\n\n"
        "注意：只给出计划，不要写完整的 Coq 代码。"
    )


# ========== 5. 规划阶段：代码分析 + 三种证明方案 ==========

def _extract_file_path(text: str):
    """从用户消息中提取 .v 文件的绝对路径。"""
    match = re.search(r'([A-Za-z]:\\[^\s]*\.v)', text)
    if match:
        return match.group(1)
    return None

def _read_file_safe(path: str):
    """安全读取文件，返回内容或 None。"""
    try:
        with open(path, 'r', encoding='utf-8') as f:
            return f.read()
    except Exception:
        return None

def _run_planner(theorem_context, goal_text, compile_error):
    """
    【按需 Planner】仅在进入 Advanced Mode 时调用。
    输入精简上下文（定理 + Goal + 错误），输出简短证明计划。
    """
    prompt = (
        "你是一位 Coq 证明策略专家。请分析以下证明目标并给出简短的证明计划。\n\n"
        f"## 待证明定理\n{theorem_context['theorem_line']}\n\n"
        f"## 当前错误\n{compile_error}\n\n"
        f"## 当前 Goal\n{goal_text}\n\n"
        f"## 上下文\n```coq\n{theorem_context['snippet']}\n```\n\n"
        "请输出简短的证明计划（3-5 步策略序列，不要完整代码）：\n"
        "1. 核心思路\n"
        "2. 关键策略步骤\n"
        "3. 可能的备选方案\n"
    )
    print("【Planner】正在分析证明策略...")
    response = client.chat.completions.create(
        model="deepseek-flash",
        messages=[{"role": "user", "content": prompt}],
        reasoning_effort="high",
        extra_body={"thinking": {"type": "enabled"}},
    )
    plan = response.choices[0].message.content
    print(f"【Planner】计划：\n{plan}")
    return plan


# ========== 5. 对话压缩：控制上下文长度 ==========

def _find_safe_cut(messages, target_recent):
    """确保 recent 切片不从 tool 消息开始（tool 消息需要前面的 assistant 消息配对）。"""
    if len(messages) <= target_recent:
        return 0
    cut = len(messages) - target_recent
    # tool 消息不能独立存在，向前找到最近的 assistant/user/system 消息
    while cut > 0 and messages[cut]["role"] == "tool":
        cut -= 1
    return cut

def compress_messages(messages, max_messages=25, keep_recent=8):
    """
    压缩消息列表，控制上下文长度：
    - 保留 system 消息和初始 user 消息（含证明方案）
    - 扫描中间消息，仅保留：最新编译错误、最新证明状态、关键统计
    - 保留最近 N 条消息以维持对话连贯性
    """
    if len(messages) <= max_messages:
        return messages

    system_msg = messages[0] if messages[0]["role"] == "system" else None
    initial_user = messages[1] if len(messages) > 1 and messages[1]["role"] == "user" else None

    cut = _find_safe_cut(messages, keep_recent)
    middle = messages[(2 if system_msg else 1):cut]
    recent = messages[cut:]

    # 扫描中间消息，只提取关键信息
    latest_compile_error = None
    latest_proof_state = None
    compile_attempts = 0
    replace_attempts = 0
    filename = None

    for msg in middle:
        content = msg.get("content", "")
        if msg["role"] == "tool":
            if "已成功创建文件" in content:
                m = re.search(r'《(.+?)》', content)
                if m:
                    filename = m.group(1)
            elif "编译失败" in content:
                compile_attempts += 1
                latest_compile_error = content
            elif "编译成功" in content:
                compile_attempts += 1
            elif "替换成功" in content:
                replace_attempts += 1
            elif "证明状态" in content or "coqtop" in content:
                latest_proof_state = content

    # 同时对 recent 中的重复错误做去重：只保留最后一次编译失败和最后一次证明状态
    recent = _dedup_recent_tool_results(recent)

    # 构建压缩摘要，初始用户消息过长则截断
    summary_parts = ["[会话压缩 — 以下为之前交互的摘要]"]
    if filename:
        summary_parts.append(f"工作文件: {filename}")
    summary_parts.append(f"历史编译尝试: {compile_attempts} 次, 文件修改: {replace_attempts} 次")

    if latest_compile_error:
        err = latest_compile_error
        if len(err) > 600:
            err = err[:600] + "\n...[截断]"
        summary_parts.append(f"\n--- 最新编译错误 ---\n{err}")

    if latest_proof_state:
        state = latest_proof_state
        if len(state) > 600:
            state = state[:600] + "\n...[截断]"
        summary_parts.append(f"\n--- 最新证明状态 ---\n{state}")

    compressed = []
    if system_msg:
        compressed.append(system_msg)
    if initial_user:
        user_content = initial_user.get("content", "")
        if len(user_content) > 2000:
            # 截断过长的初始消息（通常含证明方案），保留首 tail 各一半
            half = 1000
            initial_user = dict(initial_user)
            initial_user["content"] = user_content[:half] + "\n\n...[中间内容已截断]...\n\n" + user_content[-half:]
        compressed.append(initial_user)
    compressed.append({"role": "user", "content": "\n".join(summary_parts)})
    compressed.extend(recent)

    print(f"【压缩】消息从 {len(messages)} 条压缩至 {len(compressed)} 条")
    return compressed


def _dedup_recent_tool_results(recent):
    """
    在 recent 消息中，只保留最新的 compile_coq 失败结果和最新的 get_coq_proof_state 结果。
    旧的同类结果替换为简短占位符。
    """
    # 找到最后一次 compile_coq 失败的位置
    last_compile_fail_idx = -1
    last_proof_state_idx = -1
    for i, msg in enumerate(recent):
        if msg["role"] != "tool":
            continue
        content = msg.get("content", "")
        if "编译失败" in content:
            last_compile_fail_idx = i
        elif "证明状态" in content or "coqtop" in content:
            last_proof_state_idx = i

    cleaned = []
    for i, msg in enumerate(recent):
        if msg["role"] == "tool":
            content = msg.get("content", "")
            if "编译失败" in content and i != last_compile_fail_idx:
                cleaned.append(dict(msg, content="[已省略旧的编译错误，最新错误见上下文摘要]"))
                continue
            if ("证明状态" in content or "coqtop" in content) and i != last_proof_state_idx:
                cleaned.append(dict(msg, content="[已省略旧的证明状态，最新状态见上下文摘要]"))
                continue
        cleaned.append(msg)
    return cleaned


# ========== 5b. Advanced Mode 多条件触发辅助函数 ==========

CONTEXT_TOKEN_THRESHOLD = 500000  # 上下文 token 阈值


def _estimate_token_count(messages):
    """估算消息列表的 token 数量。中文/Coq 混合文本按 ~2.5 字符/token 估算。"""
    total_chars = sum(len(str(m.get("content", ""))) for m in messages)
    return int(total_chars / 2.5)


def _get_trigger_reason(consecutive_failures, completed_count, estimated_tokens):
    """返回触发 Advanced Mode 的原因列表。"""
    reasons = []
    if consecutive_failures >= 10:
        reasons.append(f"连续编译失败 {consecutive_failures} 次")
    if completed_count > 0 and completed_count % 5 == 0:
        reasons.append(f"已完成 {completed_count} 个定理")
    if estimated_tokens > CONTEXT_TOKEN_THRESHOLD:
        reasons.append(
            f"上下文长度 {estimated_tokens} tokens 超过阈值 {CONTEXT_TOKEN_THRESHOLD}"
        )
    return reasons


def _build_task_scale_advanced_entry(completed_count, total_count, work_filename):
    """任务规模触发：已完成多个定理，压缩上下文并整理状态。"""
    parts = [
        "【系统通知】已进入 Advanced Mode（任务规模触发）。\n",
        f"当前已完成 {completed_count}/{total_count} 个定理。",
        "为避免上下文过长，已对历史对话进行压缩，同时保留关键证明状态。\n",
        "## 当前进度摘要",
    ]
    if work_filename:
        parts.append(f"- 工作文件：{work_filename}")
    parts.append(f"- 已完成定理数：{completed_count}")
    parts.append(f"- 剩余定理数：{total_count - completed_count}")
    parts.append(
        "\n请继续完成剩余定理的证明。使用 read_coq_file 查看当前文件状态，"
        "然后逐个完成剩余定理。"
    )
    return "\n".join(parts)


def _build_context_length_advanced_entry(estimated_tokens, threshold, work_filename):
    """上下文长度触发：上下文过长，需要压缩。"""
    parts = [
        "【系统通知】已进入 Advanced Mode（上下文长度触发）。\n",
        f"当前上下文约 {estimated_tokens} tokens，超过阈值 {threshold} tokens。",
        "已对历史对话进行压缩以控制上下文长度，同时保留关键证明状态。\n",
    ]
    if work_filename:
        parts.append(f"工作文件：{work_filename}")
    parts.append("\n请基于压缩后的上下文继续当前证明工作。")
    return "\n".join(parts)


def _apply_compression(messages, entry_msg):
    """统一的上下文压缩入口：压缩消息、注入摘要、重新计算 token 数。

    所有 compression 路径（任务规模触发、上下文长度触发）必须通过此函数，
    确保压缩逻辑和返回值处理保持一致，避免不同触发入口导致状态不一致。

    Returns:
        (compressed_messages, new_estimated_tokens)
    """
    messages = compress_messages(messages, max_messages=20, keep_recent=6)
    messages.append({"role": "user", "content": entry_msg})
    new_tokens = _estimate_token_count(messages)
    print(f"【压缩】压缩后上下文约 {new_tokens} tokens")
    return messages, new_tokens


# ========== 6. 执行阶段：形式化证明 ==========

def _build_fast_continue_prompt(task_spec, last_error, last_error_category):
    """Fast Mode 继续提示：仅含错误信息 + 任务相关的下一步提示。"""
    parts = ["编译尚未通过，请修改代码后使用 compile_coq 验证。"]
    if last_error:
        parts.append(f"\n错误类型：{last_error_category or 'Unknown'}")
        parts.append(f"错误内容：\n{last_error}")
    parts.append("\n" + _task_action_hint(task_spec))
    return "\n\n".join(parts)


def _build_advanced_continue_prompt(task_spec, attempt_history, last_error, last_error_category, last_goal):
    """Advanced Mode 继续提示：含 Goal + 失败历史 + 策略提示 + Planner 计划。"""
    parts = ["编译尚未通过，请修改代码后使用 compile_coq 验证。"]

    if last_error:
        parts.append(f"\n错误类型：{last_error_category or 'Unknown'}")
        parts.append(f"错误内容：\n{last_error}")

    if last_goal and "No focused proof" not in last_goal:
        goal_short = last_goal[:600] + "\n...[截断]" if len(last_goal) > 600 else last_goal
        parts.append(f"\n当前证明状态：\n{goal_short}")

    strategy_hint = attempt_history.format_strategy_hint()
    if strategy_hint:
        parts.append(strategy_hint)

    failure_text = attempt_history.format_recent_failures(n=3)
    if failure_text:
        parts.append(failure_text)

    if _plan_cache["plan"]:
        plan_short = _plan_cache["plan"]
        if len(plan_short) > 800:
            plan_short = plan_short[:800] + "\n...[截断]"
        parts.append(f"\nPlanner 证明计划：\n{plan_short}")

    parts.append("\n" + _task_action_hint(task_spec))
    return "\n\n".join(parts)


def _build_advanced_mode_entry(task_spec, attempt_history, last_error, last_error_category,
                               last_goal, work_filename):
    """构建进入 Advanced Mode 时的上下文注入消息。"""
    parts = [
        "【系统通知】已进入 Advanced Mode。以下为扩展上下文，请使用这些信息重新规划证明。\n"
    ]

    if last_error:
        parts.append(f"## 当前错误（{last_error_category or 'Unknown'}）\n```\n{last_error}\n```\n")

    if last_goal and "No focused proof" not in last_goal:
        goal_short = last_goal[:800] + "\n...[截断]" if len(last_goal) > 800 else last_goal
        parts.append(f"## 当前证明状态\n```\n{goal_short}\n```\n")

    strategy_hint = attempt_history.format_strategy_hint()
    if strategy_hint:
        parts.append(strategy_hint)

    failure_text = attempt_history.format_recent_failures(n=3)
    if failure_text:
        parts.append(failure_text)

    if _plan_cache["plan"]:
        plan_short = _plan_cache["plan"]
        if len(plan_short) > 800:
            plan_short = plan_short[:800] + "\n...[截断]"
        parts.append(f"## Planner 证明计划\n{plan_short}\n")

    if work_filename:
        parts.append(f"工作文件：{work_filename}")

    parts.append(_task_action_hint(task_spec) + " 不要重复之前的失败方案。")
    return "\n\n".join(parts)


# ========== 6b. 任务总结 Markdown 生成 ==========

def generate_task_summary(summary_data):
    """生成任务总结 Markdown 文件，保存到 RocqAgent_output。"""
    output_dir = r"D:\Vscode\py\Axiom_of_Choice"
    os.makedirs(output_dir, exist_ok=True)

    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    summary_path = os.path.join(output_dir, f"task_summary_{timestamp}.md")

    start_time = summary_data.get("start_time", datetime.now())
    end_time = summary_data.get("end_time", datetime.now())
    duration = end_time - start_time

    task_type = summary_data.get("task_type", "N/A")
    target_file = summary_data.get("target_file", "N/A")
    target_theorems = summary_data.get("target_theorems", [])
    completion_criteria = summary_data.get("completion_criteria", "")
    user_message = summary_data.get("user_message", "")
    final_status = summary_data.get("final_status", "UNKNOWN")
    compile_result = summary_data.get("compile_result", "UNKNOWN")
    total_iterations = summary_data.get("total_iterations", 0)
    comp_details = summary_data.get("completion_details", "")
    planner_called = summary_data.get("planner_called", False)
    work_filename = summary_data.get("work_filename", "")
    compile_errors = summary_data.get("compile_errors", [])
    early_stop = summary_data.get("early_stop_reason", None)
    max_iter_hit = summary_data.get("max_iterations_reached", False)

    # ---- 构建 Markdown ----
    lines = []
    lines.append("# Task Summary\n")

    lines.append("## 1. Basic Information")
    lines.append(f"- Task start time: {start_time.strftime('%Y-%m-%d %H:%M:%S')}")
    lines.append(f"- Task end time: {end_time.strftime('%Y-%m-%d %H:%M:%S')}")
    lines.append(f"- Duration: {duration}")
    lines.append(f"- User input: `{user_message}`\n")

    lines.append("## 2. Target Information")
    lines.append(f"- Task type: `{task_type}`")
    lines.append(f"- Target file: `{target_file}`")
    if target_theorems:
        lines.append(f"- Target theorems ({len(target_theorems)}): {', '.join(target_theorems)}")
    else:
        lines.append("- Target theorems: N/A")
    if completion_criteria:
        lines.append(f"- Completion requirement: {completion_criteria}")
    else:
        lines.append("- Completion requirement: compile successfully and satisfy the task description.\n")

    lines.append("## 3. Execution Result")
    status_icon = {"SUCCESS": "SUCCESS", "INCOMPLETE": "INCOMPLETE", "FAILED": "FAILED"}.get(final_status, final_status)
    lines.append(f"- Final status: {status_icon}")
    lines.append(f"- Final compile result: {compile_result}")
    lines.append(f"- Total Agent iterations: {total_iterations}")
    if early_stop:
        lines.append(f"- Early stop reason: {early_stop}")
    if max_iter_hit:
        lines.append("- Warning: Reached maximum iterations limit.")
    lines.append("")

    lines.append("## 4. Proof Completion Status")
    if comp_details:
        lines.append(comp_details)
    else:
        lines.append("No completion check performed (no target specified).\n")

    lines.append("## 5. Execution Summary")
    if final_status == "SUCCESS":
        if target_theorems:
            lines.append(f"- Successfully completed {len(target_theorems)} target theorems in `{target_file}`.")
        else:
            lines.append("- Task completed successfully (compilation passed).")
    elif final_status == "INCOMPLETE":
        lines.append("- Task was not fully completed before exit.")
        if max_iter_hit:
            lines.append(f"- Reached maximum iterations ({total_iterations}).")
    elif final_status == "FAILED":
        lines.append("- Task failed to complete.")
        if early_stop:
            lines.append(f"- Failure reason: {early_stop}")

    if planner_called:
        lines.append("- Planner was invoked during execution.")
    if work_filename:
        lines.append(f"- Primary work file: `{work_filename}`")
    if compile_errors:
        unique_errors = list(dict.fromkeys(compile_errors))[-5:]
        lines.append(f"- Compile errors encountered: {len(compile_errors)} total")
        lines.append("- Last unique errors:")
        for err in unique_errors:
            err_short = err[:200].replace('\n', ' ')
            lines.append(f"  - {err_short}")

    lines.append("")

    md_content = "\n".join(lines)

    with open(summary_path, 'w', encoding='utf-8') as f:
        f.write(md_content)

    print(f"\n任务总结已保存至: {summary_path}")
    return summary_path


def _find_admitted(content):
    """返回文件中“未完成证明”的构造名列表（Admitted/admit/Abort/Axiom/Conjecture）。"""
    found = []
    for m in re.finditer(r'\b(Admitted|admit|Abort|Axiom|Conjecture)\b', content):
        found.append(m.group(1))
    return found


def _llm_goal_check(goal, content):
    """LLM 自检：判断当前 .v 文件是否已达成用户目标。返回 (bool, 理由)。"""
    prompt = (
        "你是一位 Coq 定理证明专家。请判断下面的 .v 文件是否已经完成了用户的目标。\n\n"
        f"## 用户目标\n{goal}\n\n"
        f"## 当前 .v 文件内容（可能较长，已展示主要部分）\n```coq\n{content[:12000]}\n```\n\n"
        "请只回答一行：YES 或 NO，然后附一句简短理由。"
    )
    try:
        response = client.chat.completions.create(
            model="deepseek-flash",
            messages=[{"role": "user", "content": prompt}],
            reasoning_effort="high",
            extra_body={"thinking": {"type": "enabled"}},
        )
        text = (response.choices[0].message.content or "").strip()
    except Exception as e:
        return False, f"LLM 自检调用失败：{e}"
    ok = text[:3].upper().startswith("YES")
    return ok, text


def _format_task_spec_context(task_spec):
    """把 TaskSpec 渲染为系统提示词中的任务目标片段。"""
    lines = ["## 任务目标"]
    if task_spec.description:
        lines.append(f"- 目标：{task_spec.description}")
    if task_spec.source_files:
        lines.append(f"- 源/基础文件：{', '.join(task_spec.source_files)}")
    if task_spec.target_files:
        lines.append(f"- 目标文件：{', '.join(task_spec.target_files)}")
    if task_spec.target_theorems:
        thm = ', '.join(task_spec.target_theorems[:20])
        if len(task_spec.target_theorems) > 20:
            thm += ' ...'
        lines.append(f"- 目标定理：{thm}")
    if task_spec.modification_target:
        lines.append(f"- 修改对象：{task_spec.modification_target}")
    if len(lines) == 1:
        return ""
    return "\n".join(lines) + "\n"


def _completion_criteria_text(task_spec):
    """按任务类型给出完成标准；优先使用 TaskSpec.completion_criteria。"""
    t = (task_spec.task_type or "").upper()
    if task_spec.completion_criteria:
        return f"- {task_spec.completion_criteria}\n"
    if t == TaskType.PROVE:
        return "- 所有目标定理都必须完成 Proof. ... Qed. 且编译通过\n"
    if t == TaskType.CREATE:
        return "- 目标文件必须已创建、内容完整且编译通过，无 Admitted\n"
    if t == TaskType.MODIFY:
        return "- 指定定义/代码必须已按需求修改，且文件编译通过\n"
    if t == TaskType.COMPILE:
        return "- 目标文件必须编译通过\n"
    if t == TaskType.ANALYZE:
        return "- 给出清晰的分析/结论即可，不强制要求编译\n"
    return "- 编译通过且无 Admitted，且满足任务描述\n"


def _task_action_hint(task_spec):
    """根据任务类型给出“下一步该用什么工具”的提示。"""
    t = (task_spec.task_type or "").upper()
    if t == TaskType.PROVE:
        return "请使用 replace_in_file 修改目标文件中的证明脚本，然后 compile_coq 编译验证。"
    if t == TaskType.CREATE:
        return "请使用 create_text_file 创建目标 .v 文件并写入内容，然后 compile_coq 编译验证。"
    if t == TaskType.MODIFY:
        return "请使用 replace_in_file 修改目标文件中的定义/代码，然后 compile_coq 编译验证。"
    if t == TaskType.COMPILE:
        return "请使用 compile_coq 编译目标文件。"
    if t == TaskType.ANALYZE:
        return "请使用 read_coq_file 阅读相关文件，然后输出你的分析结论。"
    return "请根据任务目标继续操作，并适时使用 compile_coq 验证。"


def _build_incomplete_continue_prompt(task_spec, details):
    """编译通过但任务未完成时的继续提示（按任务类型区分）。"""
    return (
        f"【系统通知】编译通过但任务尚未完成！\n{details}\n\n"
        f"{_task_action_hint(task_spec)}"
    )


def _build_system_prompt(task_spec):
    """构建系统提示词：任务上下文与修改权限按 TaskSpec.task_type 动态生成。"""
    task_context = _format_task_spec_context(task_spec)

    common = (
        "你是一个 Rocq/Coq 证明与代码助手。\n\n"
        "## 工作流程\n"
        "1. 使用 read_coq_file 了解现有代码与目标\n"
        "2. 使用 create_text_file / replace_in_file 创建或修改 .v 文件\n"
        "3. 使用 compile_coq 编译验证\n"
        "4. 编译成功只是中间步骤，需满足下方完成标准\n\n"
        + (task_context + "\n" if task_context else "") +
        "## 任务完成标准\n"
        + _completion_criteria_text(task_spec) +
        "\n"
    )

    t = (task_spec.task_type or "").upper()
    if t == TaskType.PROVE:
        common += (
            "## 修改限制（本任务：证明已有定理）\n"
            "- 尽量只修改 Proof. 到 Qed. 之间的证明脚本\n"
            "- 不要修改已通过编译的定义和引理\n"
            "- 不要创建新的 .v 文件\n"
            "- 使用 replace_in_file 做精准修改，用绝对路径\n"
        )
    elif t == TaskType.CREATE:
        common += (
            "## 修改权限（本任务：创建新文件）\n"
            "- 可以使用 create_text_file 创建新的 .v 文件\n"
            "- 若基于已有文件：新文件需 Require Export <basename>. 且与基础文件放在同一目录\n"
            "- 先列里程碑，逐步实现，每步用 compile_coq 验证\n"
        )
    elif t == TaskType.MODIFY:
        common += (
            "## 修改权限（本任务：修改已有代码）\n"
            "- 可以修改定义、声明或相关代码\n"
            "- 使用 replace_in_file 精准修改，用绝对路径\n"
            "- 修改后必须 compile_coq 编译验证\n"
        )
    elif t == TaskType.ANALYZE:
        common += (
            "## 权限（本任务：分析）\n"
            "- 可以只读取和分析，不必修改文件\n"
            "- 使用 read_coq_file 阅读相关文件，必要时 compile_coq 复现错误\n"
            "- 最后输出你的分析结论\n"
        )
    elif t == TaskType.COMPILE:
        common += (
            "## 权限（本任务：编译）\n"
            "- 使用 compile_coq 编译目标文件\n"
            "- 若编译失败，定位并说明错误原因\n"
        )

    common += (
        "## 注意\n"
        "- 先编译再下结论，编译成功前不要声称完成\n"
        "- 如果连续失败，尝试不同的策略而不是微调\n"
    )
    return common


MAX_NO_TOOL_ROUNDS = 3


class AgentSession:
    """跨多轮对话保存 Agent 状态。程序启动时创建一次，agent_run 复用同一实例。"""

    IDLE = "IDLE"
    EXECUTING = "EXECUTING"
    WAITING_FOR_USER = "WAITING_FOR_USER"

    def __init__(self):
        self.execution_state = AgentSession.IDLE
        self.messages = []
        self.is_initialized = False

        # 长期任务状态
        self.task_spec = None                 # 当前 TaskSpec（通用任务描述）
        self.completion_manager = TaskCompletionManager()
        self.fsm = AgentFSM()
        self.attempt_history = AttemptHistory(max_history=3)

        # 当前证明执行状态（跨轮次保留；开始新任务时由 reset_task_state 重置）
        self.consecutive_failures = 0
        self.in_advanced_mode = False
        self.planner_called = False
        self.completed_theorem_count = 0
        self._prev_completed_count = 0
        self._advanced_triggered_by_scale = False
        self._last_compression_tokens = 0
        self._last_compression_round = 0
        self._last_edit = ""
        self._last_compile_error = ""
        self._last_error_category = ""
        self._last_goal = ""
        self._work_filename = None
        self._raw_llm_response = ""
        self.file_content_cache = {}

        # 连续无工具调用轮数（与 attempt_history 的“编译/执行尝试”语义分离）
        self.no_tool_rounds = 0
        # LLM 请求用户澄清时保存的问题文本
        self.pending_question = ""

        # 上一轮结果
        self.last_final_status = None
        self.last_completion_details = ""

    def reset_for_feedback(self):
        """收到对现有任务的反馈/纠正时，重置执行状态（保留任务定义与工作文件路径），
        使智能体重新审视并修改已生成内容，而不是沿用“已完成”的 FSM 状态直接判定成功。"""
        self.fsm = AgentFSM()
        self.attempt_history = AttemptHistory(max_history=3)
        self.consecutive_failures = 0
        self.in_advanced_mode = False
        self.planner_called = False
        self._last_edit = ""
        self._last_compile_error = ""
        self._last_error_category = ""
        self._last_goal = ""
        self.no_tool_rounds = 0
        self.pending_question = ""
        _plan_cache["plan"] = ""
        _plan_cache["theorem_line"] = ""
        _plan_cache["round"] = 0

    def reset_task_state(self):
        """开始一个全新任务时，重置与该任务相关的执行状态（保留 messages 与 system 上下文）。"""
        self.fsm = AgentFSM()
        self.attempt_history = AttemptHistory(max_history=3)
        self.consecutive_failures = 0
        self.in_advanced_mode = False
        self.planner_called = False
        self.completed_theorem_count = 0
        self._prev_completed_count = 0
        self._advanced_triggered_by_scale = False
        self._last_compression_tokens = 0
        self._last_compression_round = 0
        self._last_edit = ""
        self._last_compile_error = ""
        self._last_error_category = ""
        self._last_goal = ""
        self.no_tool_rounds = 0
        self.pending_question = ""
        spec = self.task_spec
        self._work_filename = spec.primary_target() if spec is not None else None
        self._raw_llm_response = ""
        self.file_content_cache = {}
        _plan_cache["plan"] = ""
        _plan_cache["theorem_line"] = ""
        _plan_cache["round"] = 0


def _is_continue_instruction(text):
    """判断是否为“继续当前任务”类指令（继续 / 换一种方法 / 存在的定理等）。"""
    return bool(re.search(r'继续|换一种|换方法|换一个|存在', text))


def _is_new_task_instruction(text):
    """判断消息是否为“新任务”指令（区别于对现有工作的反馈/纠正）。

    可靠的新任务信号只有两类：
    1. 显式给出 .v 文件绝对路径；
    2. 明确的新建/生成文件/基于某文件等动作词。
    其余（如“IsRealIso 里的 x 属于 R 和 y 属于 R 应该改成…”）视为反馈，沿用已有任务。
    """
    if re.search(r'[A-Za-z]:\\[^\s"\']*\.v', text):
        return True
    return bool(re.search(
        r'新(?:生成|建|创建)|生成(?:一个|新的|新)?[^\n]{0,30}?\.v|以[^\n]{0,20}为基础|基于',
        text
    ))


def _extract_continue_to(text):
    """从“继续...到X”类消息中提取终点定理名 X（无起点、无文件路径时使用）。"""
    m = re.search(r'[到至]\s*(?:定理\s*)?([A-Za-z0-9_]+[\']?)', text)
    return m.group(1) if m else None


def _is_clarification_request(text):
    """判断 LLM 的无工具纯文本是否为“向用户请求额外信息/澄清”，而非普通状态说明。"""
    if not text:
        return False
    t = text.strip()
    patterns = [
        # 英文澄清请求
        r'i\s+need\s+(?:more\s+)?(?:information|context|details)',
        r'i\s+need\s+you\s+to\s+(?:confirm|clarify|provide|tell|specify)',
        r'i\s+need\s+(?:one\s+)?(?:a\s+)?(?:concrete\s+)?(?:fact|answer|clarification)',
        r'please\s+(?:provide|clarify|confirm|tell|specify)',
        r'cannot\s+proceed\s+without',
        r'can\s*not\s+proceed\s+without',
        r'without\s+(?:that|this|more)\s+(?:clarification|information|confirmation)',
        # 中文澄清请求
        r'需要(?:更多|进一步|额外)?(?:信息|上下文|细节|说明|确认|澄清)',
        r'请(?:确认|提供|告诉|说明|补充|明确)',
        r'无法(?:继续|进行|确定|判断)',
        r'需要用户',
    ]
    return any(re.search(p, t, re.IGNORECASE) for p in patterns)


def agent_run(session: AgentSession, user_message: str):
    """执行一轮用户指令（多轮对话中的一步）。

    先判断是否为对当前任务的“继续”指令；否则用通用任务解析器把自然语言
    解析为 TaskSpec，再进入 LLM + 工具主循环。只要请求属于合理的 Rocq
    文件操作 / 证明 / 修改 / 分析 / 编译任务，就交给 LLM 处理，不再因
    “未指定定理范围”而直接拒绝。
    函数返回仅表示当前任务本轮执行结束，不销毁 Session 或 Coq 会话。
    """
    # -------- 任务解析：继续当前任务 / 解析为新 TaskSpec --------
    is_continue = (
        session.task_spec is not None
        and _is_continue_instruction(user_message)
        and not _is_new_task_instruction(user_message)
    )

    if is_continue:
        # 继续当前任务：沿用 TaskSpec，重置执行状态重新审视
        session.reset_for_feedback()
        spec = session.task_spec
        print(f"【任务继续】沿用任务类型 {spec.task_type}：{spec.description[:60]}")
    else:
        # 解析为新任务
        spec = parse_task_spec(user_message, fallback=session.task_spec)
        if spec is None or not (spec.description or spec.source_files or spec.target_files):
            # 无法解析出任何有效信息：默认 ANALYZE，交给 LLM 理解
            spec = TaskSpec(
                task_type=TaskType.ANALYZE,
                description=user_message,
                raw_message=user_message,
            )
        session.task_spec = spec
        session.reset_task_state()
        session.completion_manager.configure_for_spec(spec)
        _print_task_spec(spec)

    # -------- 初始化 / 更新 system message --------
    if not session.is_initialized:
        session.messages.append({
            "role": "system",
            "content": _build_system_prompt(session.task_spec)
        })
        session.is_initialized = True
        print("开始任务 [Fast Mode]")
    else:
        # 更新 system 消息以反映（可能变化的）任务目标
        session.messages[0]["content"] = _build_system_prompt(session.task_spec)

    # 追加用户消息，保留历史对话上下文
    session.messages.append({"role": "user", "content": user_message})

    session.execution_state = AgentSession.EXECUTING

    # -------- 任务计时 --------
    task_start_time = datetime.now()

    # -------- 任务退出追踪（本轮）--------
    final_status = None          # SUCCESS | INCOMPLETE | FAILED
    completion_details = ""      # TaskCompletionManager 返回的详情
    early_stop_reason = None     # 提前终止原因

    max_iterations = 200
    iteration = 0

    while iteration < max_iterations:
        iteration += 1
        mode_label = "Advanced" if session.in_advanced_mode else "Fast"
        print(f"--- 第 {iteration} 轮 [{mode_label} Mode] 连续失败={session.consecutive_failures} ---")

        # ======== 提前终止检测（首轮跳过，避免用户“继续”后立即再次触发）========
        should_stop = False
        stop_reason = ""
        if iteration > 1:
            should_stop, stop_reason = session.attempt_history.should_early_stop()
        if should_stop:
            print(f"\n{'='*60}")
            print(f"【提前终止】{stop_reason}")
            print("当前证明陷入重复修改。建议重新规划证明策略。")
            print(f"{'='*60}\n")
            session.messages.append({
                "role": "user",
                "content": (
                    f"【系统通知】{stop_reason}\n"
                    "当前证明陷入重复修改。建议重新规划证明策略。"
                )
            })
            final_status = "FAILED"
            early_stop_reason = stop_reason
            break

        # ======== 进入 Advanced Mode 检测（多条件触发）========
        estimated_tokens = _estimate_token_count(session.messages)
        # 上下文长度触发需满足：超过阈值 且 （首次压缩 或 比上次压缩后增长 30%）
        context_trigger = (
            estimated_tokens > CONTEXT_TOKEN_THRESHOLD
            and (session._last_compression_tokens == 0
                 or estimated_tokens > session._last_compression_tokens * 1.3)
        )
        if not session.in_advanced_mode and (
            session.consecutive_failures >= 10
            or (session.completed_theorem_count > 0 and session.completed_theorem_count % 5 == 0
                and session.completed_theorem_count > session._prev_completed_count)
            or context_trigger
        ):
            session.in_advanced_mode = True
            failure_trigger = session.consecutive_failures >= 10
            scale_trigger = (
                session.completed_theorem_count > 0 and session.completed_theorem_count % 5 == 0
                and session.completed_theorem_count > session._prev_completed_count
            )

            trigger_reasons = _get_trigger_reason(
                session.consecutive_failures, session.completed_theorem_count, estimated_tokens
            )
            print(
                "【模式切换】Fast → Advanced Mode"
                f"（触发原因：{'; '.join(trigger_reasons)}）"
            )

            # 获取 Proof State（所有触发类型都需要）
            if session._work_filename:
                try:
                    goal_result = get_coq_proof_state(session._work_filename)
                    if "No focused proof" not in goal_result:
                        session._last_goal = goal_result
                    print("【Advanced】已获取 Proof State")
                except Exception as e:
                    print(f"【Advanced】获取 Proof State 失败：{e}")

            # ---- 失败触发：运行 Planner + 注入完整错误上下文 ----
            if failure_trigger:
                if not session.planner_called and session._work_filename:
                    try:
                        content = _read_file_safe(session._work_filename)
                        if content:
                            session.file_content_cache[session._work_filename] = content
                            ctx = extract_theorem_context(content)
                            plan = _run_planner(
                                ctx, session._last_goal or "", session._last_compile_error
                            )
                            _plan_cache["plan"] = plan or ""
                            session.planner_called = True
                            print("【Advanced】Planner 已完成")
                    except Exception as e:
                        print(f"【Advanced】Planner 失败：{e}")

                advanced_ctx_prompt = _build_advanced_mode_entry(
                    session.task_spec, session.attempt_history,
                    session._last_compile_error, session._last_error_category,
                    session._last_goal, session._work_filename or ""
                )
                session.messages.append({"role": "user", "content": advanced_ctx_prompt})

            # ---- 任务规模 / 上下文长度触发：压缩上下文 ----
            else:
                if scale_trigger:
                    session._advanced_triggered_by_scale = True
                    session._prev_completed_count = session.completed_theorem_count
                    total = len(session.completion_manager.prove_checker.target_theorems)
                    entry_msg = _build_task_scale_advanced_entry(
                        session.completed_theorem_count, total, session._work_filename or ""
                    )
                else:
                    entry_msg = _build_context_length_advanced_entry(
                        estimated_tokens, CONTEXT_TOKEN_THRESHOLD,
                        session._work_filename or ""
                    )
                # === 统一压缩入口：所有 compression 路径必须通过 _apply_compression ===
                session.messages, estimated_tokens = _apply_compression(session.messages, entry_msg)
                session._last_compression_tokens = estimated_tokens
                session._last_compression_round = iteration
                # 更新缓存中的文件内容
                if session._work_filename:
                    content = _read_file_safe(session._work_filename)
                    if content:
                        session.file_content_cache[session._work_filename] = content

        # ======== 消息压缩（仅 Advanced Mode）========
        if session.in_advanced_mode and len(session.messages) > 25:
            session.messages = compress_messages(session.messages)

        # ======== LLM 调用 ========
        print("大模型(deepseek-flash)思考中")
        response = client.chat.completions.create(
            model="deepseek-flash",
            messages=session.messages,
            reasoning_effort="high",
            extra_body={"thinking": {"type": "enabled"}},
            tools=tools,
            tool_choice="auto"
        )

        msg = response.choices[0].message
        session._raw_llm_response = msg.content or ""
        print(f"大模型的回复：{msg.content}")
        session.messages.append(msg.model_dump(exclude_none=True))

        # ======== 无工具调用：FSM + 任务完成检查 + 无工具轮数保护 ========
        if not msg.tool_calls:
            session.no_tool_rounds += 1
            print(f"【无工具调用】连续第 {session.no_tool_rounds} 轮")
            task_type = (session.task_spec.task_type or "").upper()

            # 先做程序化完成检查（不因 LLM 自己声称完成而放行）
            all_done = False
            details = ""
            checked = False
            if task_type == TaskType.ANALYZE:
                # 分析类任务：LLM 给出结论即可完成，不强制编译
                all_done, details = session.completion_manager.check_completion(
                    session.task_spec,
                    work_filename=session._work_filename,
                    analysis_text=(msg.content or ""),
                )
                checked = True
            elif session.fsm.can_finish:
                # 其余任务：以“最近一次编译成功”作为中间门槛，再做类型化完成检查
                all_done, details = session.completion_manager.check_completion(
                    session.task_spec, work_filename=session._work_filename
                )
                checked = True

            if checked:
                print(f"【任务检查】{details}")

            if all_done:
                final_status = "SUCCESS"
                completion_details = details
                session.fsm.on_task_success()
                break

            # 任务未完成：优先识别“向用户请求澄清”，避免把问题文本塞回上下文空转
            if _is_clarification_request(msg.content or ""):
                session.pending_question = (msg.content or "").strip()
                final_status = "NEEDS_INPUT"
                completion_details = "LLM 请求额外信息，进入 WAITING_FOR_USER"
                print("【用户澄清】LLM 请求额外信息，进入 WAITING_FOR_USER")
                break

            # 连续无工具调用达到阈值：停止自动循环，避免一路跑到 max_iterations
            if session.no_tool_rounds >= MAX_NO_TOOL_ROUNDS:
                final_status = "FAILED"
                completion_details = (
                    f"LLM 连续 {session.no_tool_rounds} 轮未调用工具且任务未完成，停止自动循环"
                )
                print(
                    f"【无工具调用】达到最大连续轮数 {MAX_NO_TOOL_ROUNDS}，停止自动循环"
                )
                break

            # 普通“尚未完成、准备继续”的文本：允许继续一轮
            if task_type == TaskType.ANALYZE:
                session.messages.append({
                    "role": "user",
                    "content": (
                        f"【系统通知】{details}\n"
                        "请使用 read_coq_file 阅读相关文件，必要时用 compile_coq 复现错误，"
                        "然后输出包含错误原因、相关位置和修复建议的完整分析。"
                    )
                })
                continue

            if session.fsm.can_finish:
                print(f"【FSM】编译通过但任务未完成，强制继续。")
                session.messages.append({
                    "role": "user",
                    "content": _build_incomplete_continue_prompt(session.task_spec, details)
                })
                session.fsm.on_file_modified()  # 重置编译状态，强制继续
            else:
                print(f"【FSM】尚未成功编译，强制继续。")
                if session.in_advanced_mode:
                    continue_prompt = _build_advanced_continue_prompt(
                        session.task_spec, session.attempt_history,
                        session._last_compile_error, session._last_error_category,
                        session._last_goal
                    )
                else:
                    continue_prompt = _build_fast_continue_prompt(
                        session.task_spec, session._last_compile_error,
                        session._last_error_category
                    )
                session.messages.append({"role": "user", "content": continue_prompt})
            continue

        # ======== 执行工具调用 ========
        session.no_tool_rounds = 0
        for tool_call in msg.tool_calls:
            func_name = tool_call.function.name
            try:
                args = json.loads(tool_call.function.arguments)
            except json.JSONDecodeError as e:
                print(f"【JSON修复】tool_call 参数 JSON 解析失败：{e}")
                try:
                    from json_repair import repair_json
                    repaired_args = repair_json(tool_call.function.arguments)
                    args = json.loads(repaired_args)
                    print("【JSON修复】修复成功")
                except Exception as repair_err:
                    print(f"【JSON修复】修复失败：{repair_err}")
                    session.messages.append({
                        "role": "tool",
                        "tool_call_id": tool_call.id,
                        "content": (
                            f"工具调用参数 JSON 解析失败且无法修复。"
                            f"请重新生成合法的 JSON 参数。"
                        )
                    })
                    continue

            if func_name == "create_text_file":
                session.fsm.on_file_modified()
                _p, _err = _resolve_file_path(args["filename"])
                session._work_filename = _p if not _err else os.path.join(COQ_OUTPUT_DIR, args["filename"])
                edit_content = args.get("content", "")

                if iteration > 2 and session.attempt_history.is_duplicate(edit_content):
                    print("【重复检测】创建内容与历史尝试高度相似，已被拒绝。")
                    session.messages.append({
                        "role": "tool",
                        "tool_call_id": tool_call.id,
                        "content": "【重复修改警告】此修改与之前已失败的尝试高度相似。请设计一个不同的证明方案。"
                    })
                    continue

                print("正在创建文件并写入内容...")
                result = create_text_file(args["filename"], edit_content)
                session._last_edit = edit_content
                session.messages.append({"role": "tool", "tool_call_id": tool_call.id, "content": result})

            elif func_name == "replace_in_file":
                session.fsm.on_file_modified()
                filename = args["filename"]
                session._work_filename = filename if os.path.isabs(filename) else os.path.join(COQ_OUTPUT_DIR, filename)

                old_str = args.get("old_string", "")
                new_str = args.get("new_string", "")
                session._last_edit = f"replace:\n  old: {old_str[:400]}\n  new: {new_str[:400]}"

                if iteration > 2 and session.attempt_history.is_duplicate(session._last_edit):
                    print("【重复检测】此修改与历史尝试高度相似，已被拒绝。")
                    session.messages.append({
                        "role": "tool",
                        "tool_call_id": tool_call.id,
                        "content": "【重复修改警告】此修改与之前已失败的尝试高度相似。请设计一个不同的证明方案。"
                    })
                    continue

                print("正在替换文件中的内容...")
                result = replace_in_file(args["filename"], old_str, new_str)
                session.messages.append({"role": "tool", "tool_call_id": tool_call.id, "content": result})

            elif func_name == "read_coq_file":
                print("正在读取 Coq 文件...")
                result = read_coq_file(args["filename"])
                safe_path = (
                    os.path.join(COQ_OUTPUT_DIR, args["filename"])
                    if not os.path.isabs(args["filename"])
                    else args["filename"]
                )
                if safe_path not in session.file_content_cache and os.path.isfile(safe_path):
                    try:
                        with open(safe_path, 'r', encoding='utf-8') as f:
                            session.file_content_cache[safe_path] = f.read()
                    except Exception:
                        pass
                session.messages.append({"role": "tool", "tool_call_id": tool_call.id, "content": result})

            elif func_name == "compile_coq":
                print("正在编译 Coq 文件...")
                result = compile_coq(args["filename"])
                session.messages.append({"role": "tool", "tool_call_id": tool_call.id, "content": result})

                if "编译成功" in result:
                    session.fsm.on_compile_success()
                    session.consecutive_failures = 0
                    # 更新已完成定理计数（仅 PROVE 任务）
                    if (session.task_spec.task_type or "").upper() == TaskType.PROVE:
                        pc = session.completion_manager.prove_checker
                        new_count = pc.count_completed()
                        if new_count > session.completed_theorem_count:
                            session.completed_theorem_count = new_count
                            total = len(pc.target_theorems)
                            print(
                                f"【进度】已完成 {session.completed_theorem_count}/{total} 个定理"
                            )
                    if session.in_advanced_mode:
                        session.in_advanced_mode = False
                        session.planner_called = False
                        session._advanced_triggered_by_scale = False
                        print("【模式切换】Advanced → Fast Mode（编译成功）")
                    print(f"【FSM】编译成功")
                else:
                    session.fsm.on_compile_fail()
                    session.consecutive_failures += 1
                    print(f"【FSM】编译失败（连续 {session.consecutive_failures} 次）")

                    # 错误分类
                    error_category, error_short = classify_compile_error(result)
                    session._last_compile_error = error_short
                    session._last_error_category = error_category
                    print(f"【错误分类】{error_category}")

                    # 仅在 Advanced Mode 自动获取 Proof State
                    if session.in_advanced_mode and session._work_filename:
                        try:
                            goal_result = get_coq_proof_state(session._work_filename)
                            if "No focused proof" not in goal_result:
                                session._last_goal = goal_result
                        except Exception:
                            pass

                    # 记录失败（仅失败尝试）
                    session.attempt_history.record(
                        round_num=iteration,
                        edit=session._last_edit,
                        compile_error=error_short,
                        goal=session._last_goal,
                        error_category=error_category,
                        raw_llm_response=session._raw_llm_response
                    )

                    # Advanced Mode：连续同类错误 → 策略提示
                    if session.in_advanced_mode:
                        same_cat_count = session.attempt_history.count_consecutive_same_error_category()
                        if same_cat_count >= 3:
                            print("【策略警告】连续同类错误 ≥ 3 次")
                            strategy_hint = session.attempt_history.format_strategy_hint()
                            if strategy_hint:
                                session.messages.append({"role": "user", "content": strategy_hint})

            elif func_name == "get_coq_proof_state":
                print("正在获取 Coq 证明状态...")
                result = get_coq_proof_state(args["filename"])
                session._last_goal = result
                session.messages.append({"role": "tool", "tool_call_id": tool_call.id, "content": result})

            else:
                session.messages.append({
                    "role": "tool",
                    "tool_call_id": tool_call.id,
                    "content": f"{func_name}是未知工具，请重新确认！"
                })
                break

    if iteration >= max_iterations and final_status is None:
        final_status = "INCOMPLETE"
        print(f"警告: 已达到最大迭代次数({max_iterations})，任务可能未完成。")

    # -------- 生成任务总结 Markdown --------
    if final_status is None:
        final_status = "UNKNOWN"

    task_end_time = datetime.now()

    # 最终编译结果
    if session.fsm.state == AgentFSM.COMPILE_SUCCESS:
        compile_result = "PASS"
    elif session.fsm.state == AgentFSM.COMPILE_FAIL:
        compile_result = "FAIL"
    else:
        compile_result = "UNKNOWN"

    spec = session.task_spec
    summary_data = {
        "start_time": task_start_time,
        "end_time": task_end_time,
        "user_message": user_message,
        "task_type": (spec.task_type if spec else "N/A"),
        "target_file": (spec.primary_target() if spec else None) or "N/A",
        "target_theorems": (spec.target_theorems if spec else []),
        "completion_criteria": (spec.completion_criteria if spec else ""),
        "final_status": final_status,
        "compile_result": compile_result,
        "total_iterations": iteration,
        "completion_details": completion_details,
        "planner_called": session.planner_called,
        "work_filename": session._work_filename or "",
        "compile_errors": [a["compile_error"] for a in session.attempt_history.attempts if a.get("compile_error")],
        "early_stop_reason": early_stop_reason,
        "max_iterations_reached": iteration >= max_iterations,
    }
    generate_task_summary(summary_data)

    # -------- 保存本轮结果到 Session，进入等待用户状态 --------
    session.last_final_status = final_status
    session.last_completion_details = completion_details
    session.execution_state = AgentSession.WAITING_FOR_USER

    # 注意：不再调用 _invalidate_coq_session()，Coq 会话跨轮保留，仅在程序退出时清理
    return final_status



def main():
    print("您好！欢迎来到Coq编程智能体！我可以帮您创建 Coq 源文件并编译验证。请告诉我您想要证明的定理！")
    print("（输入 exit 或 quit 退出程序）")

    # 程序启动时创建一次 Session，跨多轮保存所有 Agent 状态
    session = AgentSession()

    while True:
        try:
            user_input = input("请输入指令: ").strip()
        except (EOFError, KeyboardInterrupt):
            print()
            break

        if user_input.lower() in ("exit", "quit"):
            break

        if user_input == "":
            print("请勿输入空消息！")
            continue

        try:
            status = agent_run(session, user_input)
            if status == "SUCCESS":
                print("\n【本轮完成】任务执行成功。等待下一条指令（输入 exit 退出）。")
            elif status == "NEEDS_INPUT":
                question = session.pending_question
                print("\n【需要你的输入】大模型在等待澄清，请根据下面的问题回复：")
                if question:
                    print(f"  大模型的问题：{question}")
                print("（可直接回复，或输入“继续”/新任务）")
            elif status == "FAILED":
                print("\n【本轮结束】任务失败/暂停。可输入“继续”或“换一种方法继续”恢复，或输入新任务。")
            elif status == "INCOMPLETE":
                print("\n【本轮结束】任务未完成（可能达到最大迭代次数）。可输入“继续”恢复。")
            else:
                print(f"\n【本轮结束】状态：{status}")
        except Exception as e:
            print(f"\n执行出错：{e}")
            session.execution_state = AgentSession.WAITING_FOR_USER
            # 出错不退出整个程序，继续等待用户下一条指令

    # 只有真正退出程序时才清理长期资源（Coq 会话）
    _invalidate_coq_session()
    print("已退出，Coq 会话已清理。感谢使用！")


if __name__ == "__main__":
    main()
