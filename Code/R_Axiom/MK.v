(* TOP MARKER *)
Notation "∀ x .. y , P" := (forall x, .. (forall y, P) ..)
  (at level 200, x binder, y binder, right associativity,
  format "'[ ' ∀ x .. y ']' , P") : type_scope.

Notation "∃ x .. y , P" := (exists x, .. (exists y, P) ..)
  (at level 200, x binder, y binder, right associativity,
  format "'[ ' ∃ x .. y ']' , P") : type_scope.

Notation "'λ' x .. y , t" := (fun x => .. (fun y => t) ..)
  (at level 200, x binder, y binder, right associativity,
  format "'[ ' 'λ' x .. y ']' , t").

Axiom classic : ∀ P, P \/ ~P.

Proposition peirce : ∀ P, (~P -> P) -> P.
Proof.
  intros; destruct (classic P); auto.
Qed.

Proposition NNPP : ∀ P, ~~P <-> P.
Proof.
  split; intros; destruct (classic P); tauto.
Qed.

Proposition notandor : ∀ P Q,
  (~(P /\ Q) <-> (~P) \/ (~Q)) /\ (~(P \/ Q) <-> (~P) /\ (~Q)).
Proof.
  intros; destruct (classic P); tauto.
Qed.

Proposition inp : ∀ {P Q: Prop}, (P -> Q) -> (~Q) -> (~P).
Proof.
  intros; intro; auto.
Qed.

(* Structure *)

Class mk_structure := {
  Class : Type;
  In : Class -> Class -> Prop;
  Classifier : (Class -> Prop) -> Class
  }.

Parameter MKS: mk_structure.

Notation "x ∈ y" := (@ In MKS x y) (at level 70).

Notation "\{ P \}" := (@ Classifier MKS P) (at level 0).

(* Definitions *)

Definition Ensemble x := ∃ y, x ∈ y.

Global Hint Unfold Ensemble : core.

(* 并 x∪y = {z:z∈x或者z∈y} *)
Definition Union x y := \{ λ z, z ∈ x \/ z ∈ y \}.

Notation "x ∪ y" := (Union x y) (at level 65, right associativity).

(* 定义3  交 x∩y = {z:z∈x同时z∈y} *)
Definition Intersection x y := \{ λ z, z ∈ x /\ z ∈ y \}.

Notation "x ∩ y" := (Intersection x y) (at level 60, right associativity).

(* 定义9  x∉y当且仅当x∈y不真 *)
Definition NotIn x y := ~ (x ∈ y).

Notation "x ∉ y" := (NotIn x y) (at level 10).

(* 定义10  ¬x={y：y∉x} *)
Definition Complement x := \{λ y, y ∉ x \}.

Notation "¬ x" := (Complement x) (at level 5, right associativity).

(* 定义13  x~y=x∩(¬ y) *)
Definition Setminus x y := x ∩ (¬ y).

Notation "x ~ y" := (Setminus x y) (at level 50, left associativity).

(* 定义85  x≠y 当且仅当 x=y 不真 *)
Notation "x ≠ y" := (~ (x = y)) (at level 70).

(* 定义15  Φ={x:x≠x} *)
Definition Φ := \{λ x, x ≠ x \}.

(* 定义18  全域 μ={x:x=x} *)
Definition μ := \{ λ x, x = x \}.

(* 定义22  ∩x={z:对于每个y，如果y∈x，则z∈y} *) 
Definition Element_I x := \{ λ z, ∀ y, y ∈ x -> z ∈ y \}.

Notation "∩ x" := (Element_I x) (at level 66).

(* 定义23  ∪x={z:对于某个y，z∈y同时y∈x} *)
Definition Element_U x := \{ λ z, ∃ y, z ∈ y /\ y ∈ x \}.

Notation "∪ x" := (Element_U x) (at level 66).

(* 定义25  x⊂y 当且仅当对于每个z，如果z∈x，则z∈y *)
Definition Included x y := ∀ z, z ∈ x -> z ∈ y.

Notation "x ⊂ y" := (Included x y) (at level 70).

(* 定义36  pow(x)={y:y⊂x} *)
Definition PowerClass x := \{ λ y, y ⊂ x \}.

Notation "pow( x )" := (PowerClass x)
  (at level 0, right associativity).

(* 定义40  [x]={z:如果x∈μ，则z=x} *)
Definition Singleton x := \{ λ z, x ∈ μ -> z = x \}.

Notation "[ x ]" := (Singleton x) (at level 0, right associativity).

(* 定义45  [x|y]=[x]∪[y] *)
Definition Unordered x y := [x] ∪ [y].

Notation "[ x | y ]" := (Unordered x y) (at level 0).

(* 定义48  [x,y] = [[x]|[x|y]] *)
Definition Ordered x y := [ [x] | [x|y]].

Notation "[ x , y ]" := (Ordered x y) (at level 0).

(* 定义51  z的1st坐标=∩∩z *)
Definition First z := ∩∩z.

(* 定义52  z的2nd坐标=(∩∪z)∪(∪∪z)~(∪∩z) *)
Definition Second z := (∩∪z)∪(∪∪z) ~ (∪∩z).

(* 定义56  r是一个关系当且仅当对于r的每个元z存在x与y使得z=[x,y]; 一个关系是一个类，它的元为序偶 *)
Definition Relation r := ∀ z, z ∈ r -> ∃ x y, z = [x,y].

(* { (x,y) : ... } *)
Notation "\{\ P \}\" :=
  (\{ λ z, ∃ x y, z = [x,y] /\ P x y \}) (at level 0).

(* 定义57 r∘s={u:对于某个x，某个y及某个z,u=[x,z],[x,y]∈s同时[y,z]∈r},类r∘s是r与s的合成 *)
Definition Composition r s :=
  \{\ λ x z, ∃ y, [x,y] ∈ s /\ [y,z] ∈ r \}\.

Notation "r ∘ s" := (Composition r s) (at level 50).

(* 定义60  r ⁻¹={[x,y]:[y,x]∈r} *)
Definition Inverse r := \{\ λ x y, [y,x] ∈ r \}\.

Notation "r ⁻¹" := (Inverse r) (at level 5).

(* 定义63 f是一个函数当且仅当f是一个关系同时对每个x，每个y，每个z，如果 [x,y]∈f 且
   [x，z]∈f，则 y=z。*)
Definition Function f  :=
  Relation f /\ (∀ x y z, [x,y] ∈ f -> [x,z] ∈ f -> y = z).

(* 定义65 f的定义域={x：对于某个y，[x，y]∈f} *)
Definition Domain f := \{ λ x, ∃ y, [x,y] ∈ f \}.

Notation "dom( f )" := (Domain f)(at level 5).

(* 定义66 f的值域={y：对于某个x，[x，y]∈f} *)
Definition Range f := \{ λ y, ∃ x, [x,y] ∈ f \}.

Notation "ran( f )" := (Range f)(at level 5).

(* 定义68 f(x)=∩{y:[x,y]∈f} *)
Definition Value f x := ∩(\{ λ y, [x,y] ∈ f \}).

Notation "f [ x ]" := (Value f x)(at level 5).

(* 定义72 x × y={[u,v]:u∈x/\v∈y} *)
Definition Cartesian x y := \{\ λ u v, u ∈ x /\ v ∈ y \}\.

Notation "x × y" := (Cartesian x y) (at level 2, right associativity).

(* 定义76 Exponent y x = {f:f是一个函数，f的定义域=x同时f的值域⊂ y} *)
Definition Exponent y x :=
  \{ λ f, Function f /\ dom( f ) = x /\ ran( f ) ⊂ y \}.

(* 定义78 f在x上，当且仅当f为一函数同时x=f的定义域 *)
Definition On f x := Function f /\ dom(f) = x.

(* 定义79 f到y，当且仅当f是一个函数同时f的值域⊂y *)
Definition To f y := Function f /\ ran(f) ⊂ y.

(* 定义80 f到y上，当且仅当f是一个函数同时f的值域=y *)
Definition Onto f y := Function f /\ ran(f) = y.

(* 定义81 *)
Definition Rrelation x r y := [x,y] ∈ r.

(* 定义82 *)
Definition Connect r x := ∀ u v, u ∈ x -> v ∈ x
  -> (Rrelation u r v) \/ (Rrelation v r u) \/ (u = v).

(* 定义83 *)
Definition Transitive r x := ∀ u v w, u ∈ x -> v ∈ x -> w ∈ x
  -> Rrelation u r v -> Rrelation v r w -> Rrelation u r w.

(* 定义84 *)
Definition Asymmetric r x := ∀ u v, u ∈ x -> v ∈ x
  -> Rrelation u r v -> ~ Rrelation v r u.

(* 定义86 *)
Definition FirstMember z r x :=
  z ∈ x /\ (∀ y, y ∈ x -> ~ Rrelation y r z).

(* 定义87 *)
Definition WellOrdered r x :=
  Connect r x /\ (∀ y, y ⊂ x -> y ≠ Φ -> ∃ z, FirstMember z r y).

(* 定义89 *)
Definition rSection y r x := y ⊂ x /\ WellOrdered r x
  /\ (∀ u v, u ∈ x -> v ∈ y -> Rrelation u r v -> u ∈ y).

(* 定义93 *)
Definition Order_Pr f r s := Function f
  /\ WellOrdered r dom(f) /\ WellOrdered s ran(f)
  /\ (∀ u v, u ∈ dom(f) -> v ∈ dom(f) -> Rrelation u r v
    -> Rrelation f[u] s f[v]).

(* 定义95 *)
Definition Function1_1 f := Function f /\ Function (f⁻¹).

(* 定义98 *)
Definition Order_PXY f x y r s := WellOrdered r x /\ WellOrdered s y
  /\ Order_Pr f r s /\ rSection dom(f) r x /\ rSection ran(f) s y.

(* 定义103 *)
Definition E := \{\ λ x y, x ∈ y \}\.

(* 定义105 *)
Definition Full x := ∀ m, m ∈ x -> m ⊂ x.

(* 定义106 *)
Definition Ordinal x := Connect E x /\ Full x.

(* 定义112 *)
Definition R := \{ λ x, Ordinal x \}.

(* 定义115 *)
Definition Ordinal_Number x := x ∈ R.

(* 定义116 *)
Definition Less x y := x ∈ y.

Notation "x ≺ y" := (Less x y) (at level 67, left associativity).

(* 定义117 *)
Definition LessEqual (x y: Class) := x ∈ y \/ x = y.

Notation "x ≼ y" := (LessEqual x y) (at level 67, left associativity).

(* 定义122 *)
Definition PlusOne x := x ∪ [x].

(* 定义125 *)
Definition Restriction f x := f ∩ (x × μ).

Notation "f | ( x )" := (Restriction f x) (at level 30).

(* 定义129 *)
Definition Integer x := Ordinal x /\ WellOrdered (E⁻¹) x.

(* 定义130 *)
Definition LastMember x E y := FirstMember x (E⁻¹) y.

(* 定义131 *)
Definition ω := \{ λ x, Integer x \}.

(* 选择函数 *)
Definition ChoiceFunction c :=
  Function c /\ (∀ x, x ∈ dom(c) -> c[x] ∈ x).

(* 定义141 *)
Definition Nest n := ∀ x y, x ∈ n -> y ∈ n -> x ⊂ y \/ y ⊂ x.

(* 定义144 x≈y当且仅当存在一个1-1函数f，f的定义域=x而f的值域=y *)
Definition Equivalent x y :=
  ∃ f, Function1_1 f /\ dom(f) = x /\ ran(f) = y.

Notation "x ≈ y" := (Equivalent x y) (at level 70).

(* 定义148 x是一个基数就是说x是一个序数，并且如果y∈R和y≺x，则x≈y不真 *)
Definition Cardinal_Number x  :=
  Ordinal_Number x /\ (∀ y, y ∈ R -> y ≺ x -> ~ (x ≈ y)).

(* 定义149 C = { x : x 是基数 } *)
Definition C := \{ λ x, Cardinal_Number x \}.

(* 定义151 P = { (x,y) : x ≈ y 且 y ∈ C } *)
Definition P := \{\ λ x y, x ≈ y /\ y ∈ C \}\.

(* 定义166 x是有限的当且仅当P[x]∈w *)
Definition Finite x := P[x] ∈ ω.

Definition Max x y := x ∪ y.

Definition LessLess := \{\ λ a b, ∃ u v x y, a = [u,v]
  /\ b = [x,y] /\ [u,v] ∈ (R × R) /\ [x,y] ∈ (R × R)
  /\ ((Max u v ≺ Max x y) \/ (Max u v = Max x y /\ u ≺ x)
    \/ (Max u v = Max x y /\ u = x /\ v ≺ y)) \}\.

Notation "≪" := (LessLess)(at level 0, no associativity).

(* Axioms *)

Class MK_Axioms := {
  AI : ∀ x y, x = y <-> (∀ z, z ∈ x <-> z ∈ y);
  AII : ∀ b P, b ∈ \{ P \} <-> Ensemble b /\ (P b);
  AIII : ∀ {x}, Ensemble x
    -> ∃ y, Ensemble y /\ (∀ z, z ⊂ x -> z ∈ y);
  AIV : ∀ {x y}, Ensemble x -> Ensemble y -> Ensemble (x ∪ y);
  AV : ∀ {f}, Function f -> Ensemble dom(f) -> Ensemble ran(f);
  AVI : ∀ x, Ensemble x -> Ensemble (∪x);
  AVII : ∀ x, x ≠ Φ -> ∃ y, y ∈ x /\ x ∩ y = Φ;
  AVIII : ∃ y, Ensemble y /\ Φ ∈ y
    /\ (∀ x, x ∈ y -> (x ∪ [x]) ∈ y);
  AIX : exists c, ChoiceFunction c /\ dom(c) = μ ~ [Φ]
  }.

Parameter MK_Axiom : MK_Axioms.

Notation AxiomI := (@ AI MK_Axiom).
Notation AxiomII := (@ AII MK_Axiom).
Notation AxiomIII := (@ AIII MK_Axiom).
Notation AxiomIV := (@ AIV MK_Axiom).
Notation AxiomV := (@ AV MK_Axiom).
Notation AxiomVI := (@ AVI MK_Axiom).
Notation AxiomVII := (@ AVII MK_Axiom).
Notation AxiomVIII := (@ AVIII MK_Axiom).
Notation AxiomIX := (@ AIX MK_Axiom).

Ltac New H := pose proof H.

Ltac TF P := destruct (classic P).

Ltac Absurd := apply peirce; intros.

(* 批处理条件或目标中"与"和"或"策略 *)

Ltac deand :=
  match goal with
   | H: ?a /\ ?b |- _ => destruct H; deand
   | _ => idtac
  end.

Ltac deor :=
  match goal with
   | H: ?a \/ ?b |- _ => destruct H; deor
   | _ => idtac 
  end.

Ltac deandG :=
  match goal with
    |- ?a /\ ?b => split; deandG
    | _ => idtac
  end.

Ltac eqext := apply AxiomI; split; intros.

Ltac appA2G := apply AxiomII; split; eauto.

Ltac appA2H H := apply AxiomII in H as [].


Theorem MKT4 : ∀ x y z, z ∈ x \/ z ∈ y <-> z ∈ (x ∪ y).
Proof.
  intros x y z; split.
  - intros [H|H].
    + apply AxiomII; split; [unfold Ensemble; eauto | left; assumption].
    + apply AxiomII; split; [unfold Ensemble; eauto | right; assumption].
  - intros H.
    apply AxiomII in H as [E H].
    destruct H as [H|H]; auto.
Qed.

Theorem MKT4' : ∀ x y z, z ∈ x /\ z ∈ y <-> z ∈ (x ∩ y).
Proof.
  intros x y z; split.
  - intros [H1 H2].
    apply AxiomII; split; [unfold Ensemble; eauto | split; assumption].
  - intros H.
    apply AxiomII in H as [E H].
    destruct H as [H1 H2]; auto.
Qed.

Theorem MKT5 : ∀ x, x ∪ x = x.
Proof.
  intros x.
  apply AxiomI; intros z; split.
  - intros H.
    apply AxiomII in H as [E [H|H]]; assumption.
  - intros H.
    apply AxiomII; split; [unfold Ensemble; eauto | auto].
Qed.

Theorem MKT5' : ∀ x, x ∩ x = x.
Proof.
  intros x.
  apply AxiomI; intros z; split.
  - intros H.
    apply AxiomII in H as [E [H1 H2]]; assumption.
  - intros H.
    apply AxiomII; split; [unfold Ensemble; eauto | split; assumption].
Qed.

Theorem MKT6 : ∀ x y, x ∪ y = y ∪ x.
Proof.
  intros x y.
  apply AxiomI; intros z; split.
  - intros H.
    apply AxiomII in H as [E [H|H]].
    + apply AxiomII; split; [assumption | right; assumption].
    + apply AxiomII; split; [assumption | left; assumption].
  - intros H.
    apply AxiomII in H as [E [H|H]].
    + apply AxiomII; split; [assumption | right; assumption].
    + apply AxiomII; split; [assumption | left; assumption].
Qed.

Theorem MKT6' : ∀ x y, x ∩ y = y ∩ x.
Proof.
  intros x y.
  apply AxiomI; intros z; split.
  - intros H.
    apply AxiomII in H as [E [H1 H2]].
    apply AxiomII; split; [assumption | split; auto].
  - intros H.
    apply AxiomII in H as [E [H1 H2]].
    apply AxiomII; split; [assumption | split; auto].
Qed.

Theorem MKT7 : ∀ x y z, (x ∪ y) ∪ z = x ∪ (y ∪ z).
Proof.
  intros x y z; apply AxiomI; intros w; split.
  - intros H.
    apply AxiomII in H as [E [H|H]].
    + apply AxiomII in H as [E' [H|H]].
      * apply AxiomII; split; [assumption | left; assumption].
      * apply AxiomII; split; [assumption | right; apply AxiomII; split; [assumption | left; assumption]].
    + apply AxiomII; split; [assumption | right; apply AxiomII; split; [assumption | right; assumption]].
  - intros H.
    apply AxiomII in H as [E [H|H]].
    + apply AxiomII; split; [assumption | left; apply AxiomII; split; [assumption | left; assumption]].
    + apply AxiomII in H as [E' [H|H]].
      * apply AxiomII; split; [assumption | left; apply AxiomII; split; [assumption | right; assumption]].
      * apply AxiomII; split; [assumption | right; assumption].
Qed.

Theorem MKT7' : ∀ x y z, (x ∩ y) ∩ z = x ∩ (y ∩ z).
Proof.
  intros x y z; apply AxiomI; intros w; split.
  - intros H.
    apply AxiomII in H as [E [H1 H2]].
    apply AxiomII in H1 as [E' [H1a H1b]].
    apply AxiomII; split; [assumption | split; [assumption | apply AxiomII; split; [assumption | split; assumption]]].
  - intros H.
    apply AxiomII in H as [E [H1 H2]].
    apply AxiomII in H2 as [E' [H2a H2b]].
    apply AxiomII; split; [assumption | split; [apply AxiomII; split; [assumption | split; assumption] | assumption]].
Qed.

Theorem MKT8 : ∀ x y z, x ∩ (y ∪ z) = (x ∩ y) ∪ (x ∩ z).
Proof.
  intros x y z; apply AxiomI; intros w; split.
  - intros H.
    apply AxiomII in H as [E [H1 H2]].
    apply AxiomII in H2 as [E' [H2|H2]].
    + apply AxiomII; split; [assumption | left; apply AxiomII; split; [assumption | split; assumption]].
    + apply AxiomII; split; [assumption | right; apply AxiomII; split; [assumption | split; assumption]].
  - intros H.
    apply AxiomII in H as [E [H|H]].
    + apply AxiomII in H as [E' [H1 H2]].
      apply AxiomII; split; [assumption | split; [assumption | apply AxiomII; split; [assumption | left; assumption]]].
    + apply AxiomII in H as [E' [H1 H2]].
      apply AxiomII; split; [assumption | split; [assumption | apply AxiomII; split; [assumption | right; assumption]]].
Qed.

Theorem MKT8' : ∀ x y z, x ∪ (y ∩ z) = (x ∪ y) ∩ (x ∪ z).
Proof.
  intros x y z; apply AxiomI; intros w; split.
  - intros H.
    apply AxiomII in H as [E [H|H]].
    + apply AxiomII; split; [assumption | split].
      * apply AxiomII; split; [assumption | left; assumption].
      * apply AxiomII; split; [assumption | left; assumption].
    + apply AxiomII in H as [E' [H1 H2]].
      apply AxiomII; split; [assumption | split].
      * apply AxiomII; split; [assumption | right; assumption].
      * apply AxiomII; split; [assumption | right; assumption].
  - intros H.
    apply AxiomII in H as [E [H1 H2]].
    apply AxiomII in H1 as [E' [H1|H1]].
    + apply AxiomII; split; [assumption | left; assumption].
    + apply AxiomII in H2 as [E'' [H2|H2]].
      * apply AxiomII; split; [assumption | left; assumption].
      * apply AxiomII; split; [assumption | right; apply AxiomII; split; [assumption | split; assumption]].
Qed.

Theorem MKT11: ∀ x, ¬ (¬ x) = x.
Proof.
  intros x; apply AxiomI; intros z; split.
  - intros H.
    apply AxiomII in H as [E H1].
    destruct (classic (z ∈ x)); auto.
    exfalso; apply H1; apply AxiomII; split; [assumption | assumption].
  - intros H.
    apply AxiomII; split.
    + unfold Ensemble; eauto.
    + intros Hw.
      apply AxiomII in Hw as [E Hnx].
      apply Hnx; assumption.
Qed.

Theorem MKT12 : ∀ x y, ¬ (x ∪ y) = (¬ x) ∩ (¬ y).
Proof.
  intros x y; apply AxiomI; intros z; split.
  - intros H.
    apply AxiomII in H as [E H1].
    apply AxiomII; split; [assumption | split].
    + apply AxiomII; split; [assumption | intros Hx; apply H1; apply AxiomII; split; [assumption | left; assumption]].
    + apply AxiomII; split; [assumption | intros Hy; apply H1; apply AxiomII; split; [assumption | right; assumption]].
  - intros H.
    apply AxiomII in H as [E [H1 H2]].
    apply AxiomII in H1 as [Ex Hnx].
    apply AxiomII in H2 as [Ey Hny].
    apply AxiomII; split.
    + assumption.
    + intros H2'.
      apply AxiomII in H2' as [E' [H2'|H2']].
      * apply Hnx; assumption.
      * apply Hny; assumption.
Qed.

Theorem MKT12' : ∀ x y, ¬ (x ∩ y) = (¬ x) ∪ (¬ y).
Proof.
  intros x y; apply AxiomI; intros z; split.
  - intros H.
    apply AxiomII in H as [E H1].
    apply AxiomII; split.
    + assumption.
    + destruct (classic (z ∈ x)); destruct (classic (z ∈ y)).
      * exfalso; apply H1; apply AxiomII; split; [assumption | split; assumption].
      * right; apply AxiomII; split; [assumption | assumption].
      * left; apply AxiomII; split; [assumption | assumption].
      * left; apply AxiomII; split; [assumption | assumption].
  - intros H.
    apply AxiomII in H as [E [H|H]].
    + apply AxiomII in H as [Ex Hnx].
      apply AxiomII; split.
      * assumption.
      * intros H2; apply AxiomII in H2 as [E2 [H2x H2y]]; apply Hnx; assumption.
    + apply AxiomII in H as [Ey Hny].
      apply AxiomII; split.
      * assumption.
      * intros H2; apply AxiomII in H2 as [E2 [H2x H2y]]; apply Hny; assumption.
Qed.

Theorem MKT14 : ∀ x y z, x ∩ (y ~ z) = (x ∩ y) ~ z.
Proof.
  intros x y z; apply AxiomI; intros w; split.
  - intros H.
    apply AxiomII in H as [E [H1 H2]].
    apply AxiomII in H2 as [E' [H2a H2b]].
    apply AxiomII; split; [assumption | split].
    + apply AxiomII; split; [assumption | split; assumption].
    + assumption.
  - intros H.
    apply AxiomII in H as [E [H1 H2]].
    apply AxiomII in H1 as [E' [H1a H1b]].
    apply AxiomII; split; [assumption | split; [assumption | apply AxiomII; split; [assumption | split; assumption]]].
Qed.

Theorem MKT16 : ∀ {x}, x ∉ Φ.
Proof.
  intros x H.
  apply AxiomII in H as [E Hneq].
  apply Hneq; auto.
Qed.

Theorem MKT17 : ∀ x, Φ ∪ x = x.
Proof.
  intros x; apply AxiomI; intros z; split.
  - intros H.
    apply AxiomII in H as [E [H|H]].
    + apply AxiomII in H as [E' Hneq]; exfalso; apply Hneq; auto.
    + assumption.
  - intros H.
    apply AxiomII; split; [unfold Ensemble; eauto | right; assumption].
Qed.

Theorem MKT17' : ∀ x, Φ ∩ x = Φ.
Proof.
  intros x; apply AxiomI; intros z; split.
  - intros H.
    apply AxiomII in H as [E [H1 H2]].
    apply AxiomII in H1 as [E' Hneq]; exfalso; apply Hneq; auto.
  - intros H.
    apply AxiomII in H as [E Hneq]; exfalso; apply Hneq; auto.
Qed.

Theorem MKT19 : ∀ x, x ∈ μ <-> Ensemble x.
Proof.
  intros x; split.
  - intros H; apply AxiomII in H as [E _]; assumption.
  - intros H; apply AxiomII; split; [assumption | auto].
Qed.

Theorem MKT19a : ∀ x, x ∈ μ -> Ensemble x.
Proof.
  intros x H; apply AxiomII in H as [E _]; assumption.
Qed.

Theorem MKT19b : ∀ x, Ensemble x -> x ∈ μ.
Proof.
  intros x H; apply AxiomII; split; [assumption | auto].
Qed.

Theorem MKT20 : ∀ x, x ∪ μ = μ.
Proof.
  intros x; apply AxiomI; intros z; split.
  - intros H.
    apply AxiomII in H as [E [H|H]].
    + apply AxiomII; split; [assumption | auto].
    + apply AxiomII; split; [assumption | auto].
  - intros H.
    apply AxiomII in H as [E H].
    apply AxiomII; split; [assumption | right; apply AxiomII; split; [assumption | auto]].
Qed.

Theorem MKT20' : ∀ x, x ∩ μ = x.
Proof.
  intros x; apply AxiomI; intros z; split.
  - intros H.
    apply AxiomII in H as [E [H1 H2]].
    assumption.
  - intros H.
    apply AxiomII; split.
    + unfold Ensemble; eauto.
    + split; [assumption | apply AxiomII; split; [unfold Ensemble; eauto | auto]].
Qed.

Theorem MKT21 : ¬ Φ = μ.
Proof.
  intros; apply AxiomI; intros z; split.
  - intros H.
    apply AxiomII in H as [E H1].
    apply AxiomII; split; [assumption | auto].
  - intros H.
    apply AxiomII in H as [E H1].
    apply AxiomII; split; [assumption | intros Hz; apply AxiomII in Hz as [E' Hneq]; apply Hneq; auto].
Qed.

Theorem MKT21' : ¬ μ = Φ.
Proof.
  intros; apply AxiomI; intros z; split.
  - intros H.
    apply AxiomII in H as [E H1].
    exfalso; apply H1; apply AxiomII; split; [assumption | auto].
  - intros H.
    apply AxiomII in H as [E Hneq]; exfalso; apply Hneq; auto.
Qed.

Theorem MKT24 : ∩Φ = μ.
Proof.
  intros; apply AxiomI; intros z; split.
  - intros H.
    apply AxiomII in H as [E H].
    apply AxiomII; split; [assumption | auto].
  - intros H.
    apply AxiomII in H as [E H].
    apply AxiomII; split; [assumption | intros y Hy; apply AxiomII in Hy as [E' Hneq]; exfalso; apply Hneq; auto].
Qed.

Theorem MKT24' : ∪Φ = Φ.
Proof.
  apply AxiomI; intros z; split.
  - intro H.
    apply AxiomII in H as [E [y [Hyz Hyphi]]].
    exfalso.
    apply AxiomII in Hyphi as [E' Hneq].
    apply Hneq; reflexivity.
  - intro H.
    exfalso.
    apply AxiomII in H as [E Hneq].
    apply Hneq; reflexivity.
Qed.

Theorem MKT26 : ∀ x, Φ ⊂ x.
Proof.
  intros x z Hz.
  apply AxiomII in Hz as [E Hneq]; exfalso; apply Hneq; auto.
Qed.

Theorem MKT26' : ∀ x, x ⊂ μ.
Proof.
  intros x z Hz.
  apply AxiomII; split; [unfold Ensemble; eauto | auto].
Qed.

Theorem MKT26a : ∀ x, x ⊂ x.
Proof.
  intros x z Hz; assumption.
Qed.

Theorem MKT27 : ∀ x y, (x ⊂ y /\ y ⊂ x) <-> x = y.
Proof.
  intros x y; split.
  - intros [Hxy Hyx].
    apply AxiomI; intros z; split; intros Hz.
    + apply Hxy; assumption.
    + apply Hyx; assumption.
  - intros H; subst.
    split; intros z Hz; assumption.
Qed.

Theorem MKT28 : ∀ {x y z}, x ⊂ y -> y ⊂ z -> x ⊂ z.
Proof.
  intros x y z Hxy Hyz w Hw.
  apply Hyz; apply Hxy; assumption.
Qed.

Theorem MKT29 : ∀ x y, x ∪ y = y <-> x ⊂ y.
Proof.
  intros x y; split.
  - intros H z Hz.
    assert (Hzin : z ∈ x ∪ y).
    { apply AxiomII; split; [unfold Ensemble; eauto | left; assumption]. }
    rewrite H in Hzin.
    assumption.
  - intros Hxy.
    apply AxiomI; intros z; split.
    + intros H.
      apply AxiomII in H as [E [H|H]].
      * apply Hxy; assumption.
      * assumption.
    + intros H.
      apply AxiomII; split; [unfold Ensemble; eauto | right; assumption].
Qed.

Theorem MKT30 : ∀ x y, x ∩ y = x <-> x ⊂ y.
Proof.
  intros x y; split.
  - intros H z Hz.
    rewrite <- H in Hz.
    apply AxiomII in Hz as [E [H1 H2]].
    assumption.
  - intros Hxy.
    apply AxiomI; intros z; split.
    + intros H.
      apply AxiomII in H as [E [H1 H2]].
      assumption.
    + intros H.
      apply AxiomII; split; [unfold Ensemble; eauto | split; [assumption | apply Hxy; assumption]].
Qed.

Theorem MKT31 : ∀ x y, x ⊂ y -> (∪x ⊂ ∪y) /\ (∩y ⊂ ∩x).
Proof.
  intros x y Hxy; split.
  - intros z Hz.
    apply AxiomII in Hz as [E [y0 [Hz1 Hy0]]].
    apply AxiomII; split.
    + assumption.
    + exists y0; split; [assumption | apply Hxy; assumption].
  - intros z Hz.
    apply AxiomII in Hz as [E H1].
    apply AxiomII; split.
    + assumption.
    + intros y0 Hy0.
      apply H1; apply Hxy; assumption.
Qed.

Theorem MKT32 : ∀ x y, x ∈ y -> (x ⊂ ∪y) /\ (∩y ⊂ x).
Proof.
  intros x y Hxy; split.
  - intros z Hz.
    apply AxiomII; split.
    + unfold Ensemble; eauto.
    + exists x; split; [assumption | assumption].
  - intros z Hz.
    apply AxiomII in Hz as [E H1].
    apply H1; assumption.
Qed.

(*A.4 集的存在性 *)

Theorem MKT33 : ∀ x z, Ensemble x -> z ⊂ x -> Ensemble z.
Proof.
  intros x z Hex Hsub.
  destruct (AxiomIII Hex) as [y [Ey Hy]].
  unfold Ensemble; exists y; apply Hy; exact Hsub.
Qed.

Theorem MKT34 : Φ = ∩μ.
Proof.
  intros; apply AxiomI; intros z; split.
  - intros H.
    apply AxiomII in H as [E Hneq].
    exfalso; apply Hneq; auto.
  - intros H.
    apply AxiomII in H as [E H1].
    apply H1.
    apply AxiomII; split.
    + destruct AxiomVIII as [y0 [Ey0 [HΦ _]]]; unfold Ensemble; eauto.
    + auto.
Qed.

Theorem MKT34' : μ = ∪μ.
Proof.
  intros; apply AxiomI; intros z; split.
  - intros H.
    apply AxiomII in H as [E H].
    apply AxiomII; split.
    + assumption.
    + destruct (AxiomIII E) as [y [Ey Hy]].
      exists y; split.
      * apply Hy; intros w Hw; assumption.
      * apply AxiomII; split; [assumption | auto].
  - intros H.
    apply AxiomII in H as [E [y [Hz Hy]]].
    apply AxiomII; split; [unfold Ensemble; eauto | auto].
Qed.

Theorem MKT35 : ∀ x, x ≠ Φ -> Ensemble (∩x).
Proof.
  intros x Hne.
  destruct (AxiomVII x Hne) as [y [Hyx _]].
  assert (Ey : Ensemble y) by (unfold Ensemble; eauto).
  destruct (AxiomIII Ey) as [C [EC HC]].
  assert (Hsub : ∩x ⊂ y).
  { intros z Hz.
    apply AxiomII in Hz as [E Hz].
    apply Hz; assumption. }
  unfold Ensemble; exists C; apply HC; exact Hsub.
Qed.

Theorem MKT37 : μ = pow(μ).
Proof.
  intros; apply AxiomI; intros z; split.
  - intros H.
    apply AxiomII in H as [E H].
    apply AxiomII; split; [assumption | apply MKT26'].
  - intros H.
    apply AxiomII in H as [E H].
    apply AxiomII; split; [assumption | auto].
Qed.

Theorem MKT38a : ∀ {x}, Ensemble x -> Ensemble pow(x).
Proof.
  intros x Hex.
  destruct (AxiomIII Hex) as [y1 [Ey1 Hy1]].
  destruct (AxiomIII Ey1) as [y2 [Ey2 Hy2]].
  assert (Hsub : pow(x) ⊂ y1).
  { intros z Hz.
    apply AxiomII in Hz as [E Hzsub].
    apply Hy1; exact Hzsub. }
  unfold Ensemble; exists y2; apply Hy2; exact Hsub.
Qed.

Theorem MKT38b : ∀ {x}, Ensemble x -> (∀ y, y ⊂ x <-> y ∈ pow(x)).
Proof.
  intros x Hex y; split.
  - intros Hsub.
    destruct (AxiomIII Hex) as [c [Ec Hc]].
    apply AxiomII; split.
    + unfold Ensemble; exists c; apply Hc; exact Hsub.
    + exact Hsub.
  - intros H.
    apply AxiomII in H as [E Hsub].
    exact Hsub.
Qed.

Theorem MKT39 : ~ Ensemble μ.
Proof.
  intros Hμ.
  destruct (AxiomIII Hμ) as [y [Ey Hy]].
  set (R0 := \{ λ x, x ∈ y /\ x ∉ x \}).
  assert (HR_mu : R0 ⊂ μ).
  { intros w Hw.
    apply AxiomII in Hw as [E [Hwy _]].
    apply (MKT26' y); assumption. }
  assert (HR_y : R0 ∈ y).
  { apply Hy; exact HR_mu. }
  assert (HR_not : R0 ∉ R0).
  { intros HRR.
    apply AxiomII in HRR as [E [HRy HRnot]].
    apply HRnot.
    apply AxiomII; split; [assumption | split; assumption]. }
  apply HR_not.
  apply AxiomII; split.
  + exists y; exact HR_y.
  + split; [exact HR_y | exact HR_not].
Qed.

Theorem MKT41 : ∀ x, Ensemble x -> (∀ y, y ∈ [x] <-> y = x).
Proof.
  intros x Hex y; split.
  - intros H.
    apply AxiomII in H as [E H].
    apply H; apply MKT19b; assumption.
  - intros H; subst.
    apply AxiomII; split.
    + assumption.
    + intros _; reflexivity.
Qed.

Theorem MKT42 : ∀ x, Ensemble x -> Ensemble ([x]).
Proof.
  intros x Hex.
  assert (Hsub : [x] ⊂ pow(x)).
  { intros z Hz.
    apply AxiomII in Hz as [E Hzx].
    apply AxiomII; split.
    + assumption.
    + assert (Hz : z = x) by (apply Hzx; apply MKT19b; assumption).
      subst z.
      apply MKT26a. }
  destruct (AxiomIII (MKT38a Hex)) as [c [Ec Hc]].
  unfold Ensemble; exists c; apply Hc; exact Hsub.
Qed.

Theorem MKT43 : ∀ x, [x] = μ <-> ~ Ensemble x.
Proof.
  intros x; split.
  - intros H Hx.
    assert (Hsing : Ensemble ([x])) by (apply MKT42; assumption).
    assert (Hin : [x] ∈ μ) by (apply MKT19b; assumption).
    rewrite <- H in Hin.
    apply AxiomII in Hin as [E Hin2].
    assert (Hx_mu : x ∈ μ) by (apply MKT19b; assumption).
    assert (Hx_eq : [x] = x) by (apply Hin2; assumption).
    assert (Hmu : μ = x) by congruence.
    apply MKT39.
    rewrite Hmu.
    assumption.
  - intros Hnx.
    apply AxiomI; intros z; split.
    + intros Hz.
      apply AxiomII in Hz as [E _].
      apply AxiomII; split; [assumption | auto].
    + intros Hz.
      apply AxiomII in Hz as [E _].
      apply AxiomII; split.
      * assumption.
      * intros Hxm.
        exfalso; apply Hnx; apply MKT19a; assumption.
Qed.

Theorem MKT42' : ∀ x, Ensemble ([x]) -> Ensemble x.
Proof.
  intros x H.
  destruct (classic (Ensemble x)); auto.
  exfalso.
  apply MKT39.
  assert (Hsing : [x] = μ) by (apply (proj2 (MKT43 x)); assumption).
  rewrite <- Hsing.
  assumption.
Qed.

Theorem MKT44 : ∀ {x}, Ensemble x -> ∩[x] = x /\ ∪[x] = x.
Proof.
  intros x Hex; split.
  - apply AxiomI; intros z; split.
    + intros H.
      apply AxiomII in H as [E H1].
      apply (H1 x).
      apply AxiomII; split; [assumption | intros _; reflexivity].
    + intros H.
      apply AxiomII; split.
      * unfold Ensemble; eauto.
      * intros y Hy.
        assert (Hyx : y = x) by (apply (proj1 (MKT41 x Hex y)); assumption).
        subst y; assumption.
  - apply AxiomI; intros z; split.
    + intros H.
      apply AxiomII in H as [E [y [Hz Hy]]].
      assert (Hyx : y = x) by (apply (proj1 (MKT41 x Hex y)); assumption).
      subst y; assumption.
    + intros H.
      apply AxiomII; split.
      * unfold Ensemble; eauto.
      * exists x; split; [assumption | apply AxiomII; split; [assumption | intros _; reflexivity]].
Qed.

Theorem MKT44' : ∀ x, ~ Ensemble x -> ∩[x] = Φ /\ ∪[x] = μ.
Proof.
  intros x Hnx.
  assert (Hsing : [x] = μ) by (apply (proj2 (MKT43 x)); assumption).
  split.
  - rewrite Hsing; symmetry; apply MKT34.
  - rewrite Hsing; symmetry; apply MKT34'.
Qed.

Theorem MKT46a : ∀ {x y}, Ensemble x -> Ensemble y
  -> Ensemble ([x|y]).
Proof.
  intros x y Hex Hey.
  apply AxiomIV; apply MKT42; assumption.
Qed.

Theorem MKT46b : ∀ {x y}, Ensemble x -> Ensemble y
  -> (∀ z, z ∈ [x|y] <-> (z = x \/ z = y)).
Proof.
  intros x y Hex Hey z; split.
  - intros H.
    apply AxiomII in H as [E [H|H]].
    + left; apply (proj1 (MKT41 x Hex z)); assumption.
    + right; apply (proj1 (MKT41 y Hey z)); assumption.
  - intros [H|H]; subst.
    + apply AxiomII; split; [assumption | left; apply AxiomII; split; [assumption | intros _; reflexivity]].
    + apply AxiomII; split; [assumption | right; apply AxiomII; split; [assumption | intros _; reflexivity]].
Qed.

Theorem MKT46' : ∀ x y, [x|y] = μ <-> ~ Ensemble x \/ ~ Ensemble y.
Proof.
  intros x y; split.
  - intros H.
    destruct (classic (Ensemble x)) as [Hex | Hnx]; [| left; assumption].
    destruct (classic (Ensemble y)) as [Hey | Hny]; [| right; assumption].
    exfalso.
    assert (Hsing : Ensemble ([x|y])) by (apply MKT46a; assumption).
    assert (Hin : [x|y] ∈ μ) by (apply MKT19b; assumption).
    rewrite <- H in Hin.
    apply AxiomII in Hin as [E [Hin|Hin]].
    + apply (proj1 (MKT41 x Hex ([x|y]))) in Hin.
      assert (Hx : μ = x) by congruence.
      apply MKT39; rewrite Hx; assumption.
    + apply (proj1 (MKT41 y Hey ([x|y]))) in Hin.
      assert (Hy : μ = y) by congruence.
      apply MKT39; rewrite Hy; assumption.
  - intros [Hx | Hy].
    + assert (Hsing : [x] = μ) by (apply (proj2 (MKT43 x)); assumption).
      change ([x] ∪ [y] = μ).
      rewrite Hsing.
      rewrite (MKT6 μ ([y])).
      apply MKT20.
    + assert (Hsing : [y] = μ) by (apply (proj2 (MKT43 y)); assumption).
      change ([x] ∪ [y] = μ).
      rewrite Hsing.
      apply MKT20.
Qed.

Theorem MKT47a : ∀ x y, Ensemble x -> Ensemble y -> ∩[x|y] = x ∩ y.
Proof.
  intros x y Hex Hey; apply AxiomI; intros z; split.
  - intros H.
    apply AxiomII in H as [E H1].
    apply AxiomII; split.
    + assumption.
    + split.
      * apply (H1 x).
        apply (proj2 (MKT46b Hex Hey x)); left; reflexivity.
      * apply (H1 y).
        apply (proj2 (MKT46b Hex Hey y)); right; reflexivity.
  - intros H.
    apply AxiomII in H as [E [Hx Hy]].
    apply AxiomII; split.
    + assumption.
    + intros w Hw.
      destruct (proj1 (MKT46b Hex Hey w) Hw) as [Hwx | Hwy].
      * subst w; assumption.
      * subst w; assumption.
Qed.

Theorem MKT47b : ∀ x y, Ensemble x -> Ensemble y
  -> ∪[x|y] = x ∪ y.
Proof.
  intros x y Hex Hey; apply AxiomI; intros z; split.
  - intros H.
    apply AxiomII in H as [E [w [Hzw Hw]]].
    destruct (proj1 (MKT46b Hex Hey w) Hw) as [Hwx | Hwy].
    + apply AxiomII; split; [assumption | left; subst w; assumption].
    + apply AxiomII; split; [assumption | right; subst w; assumption].
  - intros H.
    apply AxiomII in H as [E [Hx | Hy]].
    + apply AxiomII; split.
      * assumption.
      * exists x; split.
        -- assumption.
        -- apply (proj2 (MKT46b Hex Hey x)); left; reflexivity.
    + apply AxiomII; split.
      * assumption.
      * exists y; split.
        -- assumption.
        -- apply (proj2 (MKT46b Hex Hey y)); right; reflexivity.
Qed.

Theorem MKT47' : ∀ x y, ~ Ensemble x \/ ~ Ensemble y
  -> (∩[x|y] = Φ) /\ (∪[x|y] = μ).
Proof.
  intros x y H.
  assert (Hsing : [x|y] = μ) by (apply (proj2 (MKT46' x y)); assumption).
  split.
  - rewrite Hsing; symmetry; apply MKT34.
  - rewrite Hsing; symmetry; apply MKT34'.
Qed.

(* A.5 序偶：关系 *)

Theorem MKT49a : ∀ {x y}, Ensemble x -> Ensemble y
  -> Ensemble ([x,y]).
Proof.
  intros x y Hex Hey.
  change (Ensemble (Unordered (Singleton x) (Unordered x y))).
  apply MKT46a.
  - apply MKT42; exact Hex.
  - apply MKT46a; assumption.
Qed.

Theorem MKT49b : ∀ x y, Ensemble ([x,y]) -> Ensemble x /\ Ensemble y.
Proof.
  intros x y H.
  change (Ensemble (Unordered (Singleton x) (Unordered x y))) in H.
  assert (Hun : ∀ a b, Ensemble ([a|b]) -> Ensemble a /\ Ensemble b).
  { intros a b Hab.
    destruct (classic (Ensemble a)) as [Ha | Hna].
    - destruct (classic (Ensemble b)) as [Hb | Hnb].
      + split; assumption.
      + exfalso.
        assert (Hmu : [a|b] = μ) by (apply (proj2 (MKT46' a b)); right; exact Hnb).
        rewrite Hmu in Hab.
        apply MKT39; exact Hab.
    - exfalso.
      assert (Hmu : [a|b] = μ) by (apply (proj2 (MKT46' a b)); left; exact Hna).
      rewrite Hmu in Hab.
      apply MKT39; exact Hab. }
  destruct (Hun (Singleton x) (Unordered x y) H) as [Hx Hxy].
  split.
  - apply MKT42'; exact Hx.
  - destruct (Hun x y Hxy) as [_ Hy]; exact Hy.
Qed.

Theorem MKT49c1 : ∀ {x y}, Ensemble ([x,y]) -> Ensemble x.
Proof.
  intros x y H.
  apply (proj1 (MKT49b x y H)).
Qed.

Theorem MKT49c2 : ∀ {x y}, Ensemble ([x,y]) -> Ensemble y.
Proof.
  intros x y H.
  apply (proj2 (MKT49b x y H)).
Qed.

Theorem MKT49' : ∀ x y, ~ Ensemble ([x,y]) -> [x,y] = μ.
Proof.
  intros x y H.
  change (Unordered (Singleton x) (Unordered x y) = μ).
  apply (proj2 (MKT46' (Singleton x) (Unordered x y))).
  apply (proj1 (notandor (Ensemble (Singleton x)) (Ensemble (Unordered x y)))).
  intros [Hx Hxy].
  apply H.
  change (Ensemble (Unordered (Singleton x) (Unordered x y))).
  apply MKT46a; assumption.
Qed.

Theorem MKT50 : ∀ {x y}, Ensemble x -> Ensemble y
  -> (∪[x,y] = [x|y]) /\ (∩[x,y] = [x]) /\ (∪(∩[x,y]) = x)
    /\ (∩(∩[x,y]) = x) /\ (∪(∪[x,y]) = x∪y) /\ (∩(∪[x,y]) = x∩y).
Proof.
  intros x y Hex Hey.
  assert (Hx : Ensemble ([x])) by (apply MKT42; exact Hex).
  assert (Hxy : Ensemble (Unordered x y)) by (apply MKT46a; assumption).
  assert (H1 : ∪[x,y] = [x|y]).
  { change (∪(Unordered (Singleton x) (Unordered x y)) = Unordered x y).
    rewrite (MKT47b (Singleton x) (Unordered x y) Hx Hxy).
    change (Singleton x ∪ (Singleton x ∪ Singleton y)
      = Singleton x ∪ Singleton y).
    rewrite <- (MKT7 (Singleton x) (Singleton x) (Singleton y)).
    rewrite (MKT5 (Singleton x)).
    reflexivity. }
  assert (H2 : ∩[x,y] = [x]).
  { change (∩(Unordered (Singleton x) (Unordered x y)) = [x]).
    rewrite (MKT47a (Singleton x) (Unordered x y) Hx Hxy).
    change (Singleton x ∩ (Singleton x ∪ Singleton y) = Singleton x).
    rewrite (MKT8 (Singleton x) (Singleton x) (Singleton y)).
    rewrite (MKT5' (Singleton x)).
    rewrite (MKT6 (Singleton x) (Singleton x ∩ Singleton y)).
    apply (proj2 (MKT29 (Singleton x ∩ Singleton y) (Singleton x))).
    intros z Hz.
    apply AxiomII in Hz as [E [Hz1 _]].
    exact Hz1. }
  assert (H3 : ∪(∩[x,y]) = x).
  { rewrite H2. exact (proj2 (MKT44 Hex)). }
  assert (H4 : ∩(∩[x,y]) = x).
  { rewrite H2. exact (proj1 (MKT44 Hex)). }
  assert (H5 : ∪(∪[x,y]) = x ∪ y).
  { rewrite H1. exact (MKT47b x y Hex Hey). }
  assert (H6 : ∩(∪[x,y]) = x ∩ y).
  { rewrite H1. exact (MKT47a x y Hex Hey). }
  repeat split; assumption.
Qed.

Lemma Lemma50' : ∀ (x y: Class), ~ Ensemble x \/ ~ Ensemble y
  -> ~ Ensemble ([x]) \/ ~ Ensemble ([x | y]).
Proof.
  intros x y H.
  destruct H as [Hx | Hy].
  - left. intros Hx'. apply Hx. apply MKT42'; exact Hx'.
  - right. intros Hxy. apply Hy.
    assert (Hun : ∀ a b, Ensemble ([a|b]) -> Ensemble a /\ Ensemble b).
    { intros a b Hab.
      destruct (classic (Ensemble a)) as [Ha | Hna].
      - destruct (classic (Ensemble b)) as [Hb | Hnb].
        + split; assumption.
        + exfalso.
          assert (Hmu : [a|b] = μ) by (apply (proj2 (MKT46' a b)); right; exact Hnb).
          rewrite Hmu in Hab.
          apply MKT39; exact Hab.
      - exfalso.
        assert (Hmu : [a|b] = μ) by (apply (proj2 (MKT46' a b)); left; exact Hna).
        rewrite Hmu in Hab.
        apply MKT39; exact Hab. }
    exact (proj2 (Hun x y Hxy)).
Qed.

Theorem MKT50' : ∀ {x y}, ~ Ensemble x \/ ~ Ensemble y
  -> (∪(∩[x,y]) = Φ) /\ (∩(∩[x,y]) = μ) /\ (∪(∪[x,y]) = μ)
    /\ (∩(∪[x,y]) = Φ).
Proof.
  intros x y H.
  assert (Hnx : ~ Ensemble ([x,y])).
  { intros Hxy. destruct H as [Hx | Hy].
    - apply Hx; apply (proj1 (MKT49b x y Hxy)).
    - apply Hy; apply (proj2 (MKT49b x y Hxy)). }
  assert (Hpair : [x,y] = μ) by (apply MKT49'; exact Hnx).
  split.
  - rewrite Hpair.
    rewrite <- MKT34.
    exact MKT24'.
  - split.
    + rewrite Hpair.
      rewrite <- MKT34.
      exact MKT24.
    + split.
      * rewrite Hpair.
        rewrite <- MKT34'.
        exact (eq_sym MKT34').
      * rewrite Hpair.
        rewrite <- MKT34'.
        exact (eq_sym MKT34).
Qed.

Theorem MKT53 : Second μ = μ.
Proof.
  unfold Second.
  rewrite <- MKT34'.
  rewrite <- MKT34'.
  rewrite <- MKT34.
  rewrite MKT24'.
  change (Φ ∪ (μ ∩ (¬ Φ)) = μ).
  rewrite MKT21.
  rewrite (MKT5' μ).
  exact (MKT20 Φ).
Qed.

Theorem MKT54a : ∀ x y, Ensemble x -> Ensemble y
  -> First ([x,y]) = x.
Proof.
  intros x y Hex Hey.
  unfold First.
  destruct (MKT50 Hex Hey) as [_ [H2 [H3 _]]].
  rewrite H2.
  exact (proj1 (MKT44 Hex)).
Qed.

Theorem MKT54b : ∀ x y, Ensemble x -> Ensemble y
  -> Second ([x,y]) = y.
Proof.
  intros x y Hex Hey.
  unfold Second.
  destruct (MKT50 Hex Hey) as [H1 [H2 [H3 [H4 [H5 H6]]]]].
  rewrite H5.
  rewrite H3.
  rewrite H1.
  rewrite (MKT47a x y Hex Hey).
  apply AxiomI; intros z; split.
  - intros Hz.
    apply AxiomII in Hz as [E [Hz | Hz]].
    + apply AxiomII in Hz as [E' [Hzx Hzy]]. exact Hzy.
    + apply AxiomII in Hz as [E' [Hzu Hznotx]].
      apply AxiomII in Hzu as [E'' [Hzx | Hzy]].
      * apply AxiomII in Hznotx as [E''' Hnx]. exfalso. apply Hnx; exact Hzx.
      * exact Hzy.
  - intros Hzy.
    assert (Ez : Ensemble z).
    { apply (MKT33 (∪y) z (AxiomVI y Hey)).
      apply (proj1 (MKT32 z y Hzy)). }
    destruct (classic (z ∈ x)) as [Hzx | Hnzx].
    + apply AxiomII; split; [exact Ez | left; apply AxiomII; split; [exact Ez | split; assumption]].
    + apply AxiomII; split; [exact Ez | right; apply AxiomII; split; [exact Ez | split]].
      * apply AxiomII; split; [exact Ez | right; assumption].
      * apply AxiomII; split; [exact Ez | exact Hnzx].
Qed.

Theorem MKT54' : ∀ x y, ~ Ensemble x \/ ~ Ensemble y
  -> First ([x,y]) = μ /\ Second ([x,y]) = μ.
Proof.
  intros x y H.
  assert (Hnx : ~ Ensemble ([x,y])).
  { intros Hxy. destruct H as [Hx | Hy].
    - apply Hx; apply (proj1 (MKT49b x y Hxy)).
    - apply Hy; apply (proj2 (MKT49b x y Hxy)). }
  assert (Hpair : [x,y] = μ) by (apply MKT49'; exact Hnx).
  split.
  - unfold First. rewrite Hpair.
    rewrite <- MKT34.
    exact MKT24.
  - rewrite Hpair. exact MKT53.
Qed.

Theorem MKT55 : ∀ x y u v, Ensemble x -> Ensemble y
  -> ([x,y] = [u,v] <-> x = u /\ y = v).
Proof.
  intros x y u v Hex Hey.
  split.
  - intros H.
    change (Unordered (Singleton x) (Unordered x y)
      = Unordered (Singleton u) (Unordered u v)) in H.
    assert (HxyE : Ensemble ([x,y])) by (apply MKT49a; assumption).
    assert (HuvE : Ensemble ([u,v])).
    { change (Ensemble (Unordered (Singleton u) (Unordered u v))).
      rewrite <- H. exact HxyE. }
    destruct (MKT49b u v HuvE) as [Hu Hv].
    assert (Hxmu : x ∈ Singleton x).
    { apply (proj2 (MKT41 x Hex x)); reflexivity. }
    assert (Hxsing : Ensemble (Singleton x)) by (apply MKT42; exact Hex).
    assert (Hxyun : Ensemble (Unordered x y)) by (apply MKT46a; assumption).
    assert (Husing : Ensemble (Singleton u)) by (apply MKT42; exact Hu).
    assert (Huvun : Ensemble (Unordered u v)) by (apply MKT46a; assumption).
    (* Step 1: x = u *)
    assert (Hxu : x = u).
    {
      assert (Hxin : Singleton x ∈ Unordered (Singleton x) (Unordered x y)).
      { change (Singleton x ∈ Singleton (Singleton x) ∪ Singleton (Unordered x y)).
        apply MKT4. left. apply (proj2 (MKT41 (Singleton x) Hxsing (Singleton x))); reflexivity. }
      assert (Hxin' : Singleton x ∈ Unordered (Singleton u) (Unordered u v)).
      { rewrite <- H. exact Hxin. }
      change (Singleton x ∈ Singleton (Singleton u) ∪ Singleton (Unordered u v)) in Hxin'.
      apply MKT4 in Hxin'.
      destruct Hxin' as [Hxinu | Hxinuv].
      - assert (Hxu0 : Singleton x = Singleton u).
        { apply (proj1 (MKT41 (Singleton u) Husing (Singleton x))); exact Hxinu. }
        apply (proj1 (MKT41 u Hu x)).
        rewrite <- Hxu0. exact Hxmu.
      - assert (Hxu0 : Singleton x = Unordered u v).
        { apply (proj1 (MKT41 (Unordered u v) Huvun (Singleton x))); exact Hxinuv. }
        assert (Hux : u = x).
        { apply (proj1 (MKT41 x Hex u)).
          rewrite Hxu0.
          apply (proj2 (MKT46b Hu Hv u)); left; reflexivity. }
        symmetry; exact Hux.
    }
    (* Step 2: y = v *)
    assert (Hyv : y = v).
    {
      assert (Hxv : Ensemble (Unordered x v)) by (apply MKT46a; assumption).
      assert (Hx' : Unordered (Singleton x) (Unordered x y)
        = Unordered (Singleton x) (Unordered x v)).
      { rewrite <- Hxu in H. exact H. }
    assert (Hyx : Unordered x y ∈ Unordered (Singleton x) (Unordered x y)).
    { change (Unordered x y ∈ Singleton (Singleton x) ∪ Singleton (Unordered x y)).
      apply MKT4. right. apply (proj2 (MKT41 (Unordered x y) Hxyun (Unordered x y))); reflexivity. }
    assert (Hyx' : Unordered x y ∈ Unordered (Singleton x) (Unordered x v)).
    { rewrite <- Hx'. exact Hyx. }
    change (Unordered x y ∈ Singleton (Singleton x) ∪ Singleton (Unordered x v)) in Hyx'.
    apply MKT4 in Hyx'.
    destruct Hyx' as [Hyx_in_x | Hyx_in_xv].
    + assert (Hxy : Unordered x y = Singleton x).
      { apply (proj1 (MKT41 (Singleton x) Hxsing (Unordered x y))); exact Hyx_in_x. }
      assert (Hyx2 : y = x).
      { apply (proj1 (MKT41 x Hex y)).
        rewrite <- Hxy.
        apply (proj2 (MKT46b Hex Hey y)); right; reflexivity. }
      assert (Hxvin : Unordered x v ∈ Unordered (Singleton x) (Unordered x v)).
      { change (Unordered x v ∈ Singleton (Singleton x) ∪ Singleton (Unordered x v)).
        apply MKT4. right. apply (proj2 (MKT41 (Unordered x v) Hxv (Unordered x v))); reflexivity. }
      assert (Hxvin' : Unordered x v ∈ Unordered (Singleton x) (Unordered x y)).
      { rewrite Hx'. exact Hxvin. }
      assert (Hxx : Unordered (Singleton x) (Unordered x y)
        = Singleton (Singleton x)).
      { change (Singleton (Singleton x) ∪ Singleton (Unordered x y)
          = Singleton (Singleton x)).
        rewrite Hxy.
        exact (MKT5 (Singleton (Singleton x))). }
      assert (Hxvx : Unordered x v = Singleton x).
      { apply (proj1 (MKT41 (Singleton x) Hxsing (Unordered x v))).
        rewrite Hxx in Hxvin'. exact Hxvin'. }
      assert (Hvx : v = x).
      { apply (proj1 (MKT41 x Hex v)).
        rewrite <- Hxvx.
        apply (proj2 (MKT46b Hex Hv v)); right; reflexivity. }
      rewrite Hyx2. symmetry. exact Hvx.
    + assert (Hxy : Unordered x y = Unordered x v).
      { apply (proj1 (MKT41 (Unordered x v) Hxv (Unordered x y))); exact Hyx_in_xv. }
      assert (Hyv2 : y = x \/ y = v).
      { apply (proj1 (MKT46b Hex Hv y)).
        rewrite <- Hxy.
        apply (proj2 (MKT46b Hex Hey y)); right; reflexivity. }
      destruct Hyv2 as [Hyx2 | Hyv].
      * assert (Hxyx : Unordered x y = Singleton x).
        { change (Singleton x ∪ Singleton y = Singleton x).
          rewrite Hyx2. exact (MKT5 (Singleton x)). }
        assert (Hxvx : Unordered x v = Singleton x).
        { rewrite <- Hxy. exact Hxyx. }
        assert (Hvx : v = x).
        { apply (proj1 (MKT41 x Hex v)).
          rewrite <- Hxvx.
          apply (proj2 (MKT46b Hex Hv v)); right; reflexivity. }
        rewrite Hyx2. symmetry. exact Hvx.
      * exact Hyv.
    }
    split; assumption.
  - intros [Hxu Hyv].
    rewrite Hxu, Hyv. reflexivity.
Qed.

Theorem MKT58 : ∀ r s t, (r ∘ s) ∘ t = r ∘ (s ∘ t).
Proof.
  intros r s t.
  apply AxiomI; intros w; split.
  - intros Hw.
    apply AxiomII in Hw as [Ew Hw].
    destruct Hw as [x [z [Hwz [y [Hxt Hyz]]]]].
    apply AxiomII in Hyz as [Eyz Hyz].
    destruct Hyz as [u [v [Hyzuv [y' [Hus Hy'r]]]]].
    destruct (MKT49b y z Eyz) as [Ey Ez].
    destruct (proj1 (MKT55 y z u v Ey Ez) Hyzuv) as [Hyu Hzv].
    assert (Exz : Ensemble ([x,z])).
    { rewrite <- Hwz. exact Ew. }
    destruct (MKT49b x z Exz) as [Ex Ez'].
    assert (Euy' : Ensemble ([u,y'])).
    { unfold Ensemble; eauto. }
    destruct (MKT49b u y' Euy') as [Eu Ey'].
    assert (Exy' : Ensemble ([x,y'])).
    { apply MKT49a; assumption. }
    assert (Hys' : [y,y'] ∈ s).
    { rewrite Hyu. exact Hus. }
    apply AxiomII; split; [exact Ew | exists x; exists z; split; [exact Hwz |]].
    exists y'; split.
    + apply AxiomII; split; [exact Exy' | exists x; exists y'; split; [reflexivity |
        exists y; split; [exact Hxt | exact Hys']]].
    + rewrite Hzv. exact Hy'r.
  - intros Hw.
    apply AxiomII in Hw as [Ew Hw].
    destruct Hw as [x [z [Hwz [y [Hxy Hyr]]]]].
    apply AxiomII in Hxy as [Exy Hxy].
    destruct Hxy as [u [v [Hxyuv [y' [Hut Hys]]]]].
    destruct (MKT49b x y Exy) as [Ex Ey].
    destruct (proj1 (MKT55 x y u v Ex Ey) Hxyuv) as [Hxu Hyv].
    assert (Exz : Ensemble ([x,z])).
    { rewrite <- Hwz. exact Ew. }
    destruct (MKT49b x z Exz) as [Ex' Ez].
    assert (Euy' : Ensemble ([u,y'])).
    { unfold Ensemble; eauto. }
    destruct (MKT49b u y' Euy') as [Eu Ey'].
    assert (Ey'z : Ensemble ([y',z])).
    { apply MKT49a; assumption. }
    assert (Hxt' : [x,y'] ∈ t).
    { rewrite Hxu. exact Hut. }
    assert (Hys' : [y',y] ∈ s).
    { rewrite Hyv. exact Hys. }
    apply AxiomII; split; [exact Ew | exists x; exists z; split; [exact Hwz |]].
    exists y'; split.
    + exact Hxt'.
    + apply AxiomII; split; [exact Ey'z | exists y'; exists z; split; [reflexivity |
        exists y; split; [exact Hys' | exact Hyr]]].
Qed.

Theorem MKT59 : ∀ r s t, Relation r -> Relation s
  -> r ∘ (s ∪ t) = (r ∘ s) ∪ (r ∘ t)
    /\ r ∘ (s ∩ t) ⊂ (r ∘ s) ∩ (r ∘ t).
Proof.
  intros r s t Hr Hs.
  split.
  - apply AxiomI; intros w; split.
    + intros Hw.
      apply AxiomII in Hw as [Ew Hw].
      destruct Hw as [x [z [Hwz [y [Hy_ Hyr]]]]].
      apply AxiomII in Hy_ as [E2 Hy_].
      destruct Hy_ as [Hys | Hyt].
      * apply AxiomII; split; [exact Ew | left; apply AxiomII; split; [exact Ew |
          exists x; exists z; split; [exact Hwz | exists y; split; [exact Hys | exact Hyr]]]].
      * apply AxiomII; split; [exact Ew | right; apply AxiomII; split; [exact Ew |
          exists x; exists z; split; [exact Hwz | exists y; split; [exact Hyt | exact Hyr]]]].
    + intros Hw.
      apply AxiomII in Hw as [Ew Hw].
      destruct Hw as [Hws | Hwt].
      * apply AxiomII in Hws as [Ews Hws].
        destruct Hws as [x [z [Hwz [y [Hys Hyr]]]]].
        apply AxiomII; split; [exact Ew | exists x; exists z; split; [exact Hwz |]].
        exists y; split; [| exact Hyr].
        apply AxiomII; split; [unfold Ensemble; eauto | left; exact Hys].
      * apply AxiomII in Hwt as [Ewt Hwt].
        destruct Hwt as [x [z [Hwz [y [Hyt Hyr]]]]].
        apply AxiomII; split; [exact Ew | exists x; exists z; split; [exact Hwz |]].
        exists y; split; [| exact Hyr].
        apply AxiomII; split; [unfold Ensemble; eauto | right; exact Hyt].
  - intros w Hw.
    apply AxiomII in Hw as [Ew Hw].
    destruct Hw as [x [z [Hwz [y [Hyi Hyr]]]]].
    apply AxiomII in Hyi as [E2 Hyi].
    destruct Hyi as [Hys Hyt].
    apply AxiomII; split; [exact Ew | split].
    + apply AxiomII; split; [exact Ew | exists x; exists z; split; [exact Hwz |
        exists y; split; [exact Hys | exact Hyr]]].
    + apply AxiomII; split; [exact Ew | exists x; exists z; split; [exact Hwz |
        exists y; split; [exact Hyt | exact Hyr]]].
Qed.

Theorem MKT61 : ∀ r, Relation r -> (r⁻¹)⁻¹ = r.
Proof.
  intros r Hr.
  apply AxiomI; intros z; split.
  - intros Hz.
    apply AxiomII in Hz as [Ez Hz].
    destruct Hz as [x [y [Hzy Hyx]]].
    apply AxiomII in Hyx as [Eyx Hyx].
    destruct Hyx as [u [v [Hyxuv Hvr]]].
    destruct (MKT49b y x Eyx) as [Ey Ex].
    destruct (proj1 (MKT55 y x u v Ey Ex) Hyxuv) as [Hyu Hxv].
    rewrite Hzy.
    rewrite <- Hxv in Hvr.
    rewrite <- Hyu in Hvr.
    exact Hvr.
  - intros Hz.
    destruct (Hr z Hz) as [x [y Hzy]].
    assert (Ezy : Ensemble ([x,y])).
    { rewrite <- Hzy. unfold Ensemble; eauto. }
    destruct (MKT49b x y Ezy) as [Ex Ey].
    apply AxiomII; split; [rewrite Hzy; exact Ezy |].
    exists x; exists y; split; [exact Hzy |].
    apply AxiomII; split.
    + apply MKT49a; assumption.
    + exists y; exists x; split; [reflexivity |].
      rewrite <- Hzy. exact Hz.
Qed.

Theorem MKT62 : ∀ r s, (r ∘ s)⁻¹ = (s⁻¹) ∘ (r⁻¹).
Proof.
  intros r s.
  apply AxiomI; intros z; split.
  - intros Hz.
    apply AxiomII in Hz as [Ez Hz].
    destruct Hz as [a [b [Hzab Hba]]].
    apply AxiomII in Hba as [Eba Hba].
    destruct Hba as [u [v [Hbauv [y [Hus Hyr]]]]].
    destruct (MKT49b b a Eba) as [Eb Ea].
    destruct (proj1 (MKT55 b a u v Eb Ea) Hbauv) as [Hbu Hav].
    assert (Euy : Ensemble ([u,y])).
    { unfold Ensemble; eauto. }
    destruct (MKT49b u y Euy) as [Eu Ey].
    assert (Eay : Ensemble ([a,y])).
    { apply MKT49a; assumption. }
    assert (Eyb : Ensemble ([y,b])).
    { apply MKT49a; assumption. }
    apply AxiomII; split; [exact Ez | exists a; exists b; split; [exact Hzab |]].
    exists y; split.
    + apply AxiomII; split; [exact Eay | exists a; exists y; split; [reflexivity |]].
      rewrite Hav. exact Hyr.
    + apply AxiomII; split; [exact Eyb | exists y; exists b; split; [reflexivity |]].
      rewrite Hbu. exact Hus.
  - intros Hz.
    apply AxiomII in Hz as [Ez Hz].
    destruct Hz as [a [b [Hzab [y [Hay Hyb]]]]].
    apply AxiomII in Hay as [Eay Hay].
    destruct Hay as [u [v [Hayuv Hvr]]].
    destruct (MKT49b a y Eay) as [Ea Ey].
    destruct (proj1 (MKT55 a y u v Ea Ey) Hayuv) as [Hau Hyv].
    apply AxiomII in Hyb as [Eyb Hyb].
    destruct Hyb as [u' [v' [Hybuv Hvs]]].
    destruct (MKT49b y b Eyb) as [Ey' Eb].
    destruct (proj1 (MKT55 y b u' v' Ey' Eb) Hybuv) as [Hyu' Hbv'].
    assert (Eba : Ensemble ([b,a])).
    { apply MKT49a; assumption. }
    apply AxiomII; split; [exact Ez | exists a; exists b; split; [exact Hzab |]].
    apply AxiomII; split; [exact Eba | exists b; exists a; split; [reflexivity |]].
    exists y; split.
    + rewrite Hbv'. rewrite Hyu'. exact Hvs.
    + rewrite Hyv. rewrite Hau. exact Hvr.
Qed.

(* A.6 函数 *)
Theorem MKT64 : ∀ f g, Function f -> Function g -> Function (f ∘ g).
Proof.
  intros f g Hf Hg.
  unfold Function.
  split.
  - intros z Hz.
    apply AxiomII in Hz as [Ez Hz].
    destruct Hz as [x [y [Hzy _]]].
    exists x; exists y; exact Hzy.
  - intros x y z Hxy Hxz.
    assert (comp_in : ∀ r s a b, Ensemble a -> Ensemble b
      -> ([a,b] ∈ (r ∘ s) <-> ∃ w, [a,w] ∈ s /\ [w,b] ∈ r)).
    { intros r0 s0 a b Ea Eb; split.
      - intros Hab.
        apply AxiomII in Hab as [E Hab].
        destruct Hab as [u [v [Hauv [w [Huz Hwr]]]]].
        destruct (proj1 (MKT55 a b u v Ea Eb) Hauv) as [Hau Hbv].
        exists w; split.
        + rewrite Hau. exact Huz.
        + rewrite Hbv. exact Hwr.
      - intros [w [Haw Hwb]].
        apply AxiomII; split; [apply MKT49a; assumption |
          exists a; exists b; split; [reflexivity | exists w; split; assumption]]. }
    pose proof Hxy as Hxy0.
    pose proof Hxz as Hxz0.
    apply AxiomII in Hxy as [Exy _].
    apply AxiomII in Hxz as [Exz _].
    destruct (MKT49b x y Exy) as [Ex Ey].
    destruct (MKT49b x z Exz) as [Ex' Ez].
    destruct (proj1 (comp_in f g x y Ex Ey) Hxy0) as [y1 [Hy1g Hy1f]].
    destruct (proj1 (comp_in f g x z Ex' Ez) Hxz0) as [y2 [Hy2g Hy2f]].
    assert (Hy12 : y1 = y2).
    { apply (proj2 Hg x y1 y2); assumption. }
    rewrite <- Hy12 in Hy2f.
    apply (proj2 Hf y1 y z); assumption.
Qed.

(* 定理67 μ的定义域=μ同时μ的值域=μ *)
Theorem MKT67a: dom(μ) = μ.
Proof.
  apply AxiomI; intros x; split.
  - intros Hx.
    apply AxiomII in Hx as [Ex _].
    apply MKT19b; exact Ex.
  - intros Hx.
    apply AxiomII in Hx as [Ex _].
    apply AxiomII; split; [exact Ex | exists x].
    apply AxiomII; split.
    + apply MKT49a; assumption.
    + reflexivity.
Qed.

Theorem MKT67b: ran(μ) = μ.
Proof.
  apply AxiomI; intros y; split.
  - intros Hy.
    apply AxiomII in Hy as [Ey _].
    apply MKT19b; exact Ey.
  - intros Hy.
    apply AxiomII in Hy as [Ey _].
    apply AxiomII; split; [exact Ey | exists y].
    apply AxiomII; split.
    + apply MKT49a; assumption.
    + reflexivity.
Qed.

Theorem MKT69a : ∀ {x f}, x ∉ dom(f) -> f[x] = μ.
Proof.
  intros x f Hx.
  assert (Hset : \{ λ y, [x,y] ∈ f \} = Φ).
  { apply AxiomI; intros z; split.
    - intros Hz.
      apply AxiomII in Hz as [Ez Hxz].
      exfalso.
      apply Hx.
      apply AxiomII; split.
      + assert (Exz : Ensemble ([x,z])) by (unfold Ensemble; eauto).
        exact (proj1 (MKT49b x z Exz)).
      + exists z; exact Hxz.
    - intros Hz.
      apply AxiomII in Hz as [E Hneq].
      exfalso; apply Hneq; reflexivity. }
  unfold Value.
  rewrite Hset.
  exact MKT24.
Qed.

Theorem MKT69b : ∀ {x f}, x ∈ dom(f) -> f[x] ∈ μ.
Proof.
  intros x f Hx.
  apply AxiomII in Hx as [Ex Hx].
  destruct Hx as [y Hxy].
  assert (Hne : \{ λ y, [x,y] ∈ f \} ≠ Φ).
  { intro H.
    assert (HyS : y ∈ \{ λ y, [x,y] ∈ f \}).
    { apply AxiomII; split.
      + assert (Exy : Ensemble ([x,y])) by (unfold Ensemble; eauto).
        exact (proj2 (MKT49b x y Exy)).
      + exact Hxy. }
    rewrite H in HyS.
    apply AxiomII in HyS as [E HyS].
    apply HyS; reflexivity. }
  assert (Ef : Ensemble (∩(\{ λ y, [x,y] ∈ f \}))).
  { apply MKT35; exact Hne. }
  apply MKT19b.
  unfold Value. exact Ef.
Qed.

Theorem MKT69a' : ∀ {x f}, f[x] = μ -> x ∉ dom(f).
Proof.
  intros x f H.
  intro Hx.
  assert (Hfx : f[x] ∈ μ) by (apply MKT69b; exact Hx).
  rewrite H in Hfx.
  apply MKT19a in Hfx.
  apply MKT39; exact Hfx.
Qed.

Theorem MKT69b' : ∀ {x f}, f[x] ∈ μ -> x ∈ dom(f).
Proof.
  intros x f H.
  apply (proj1 (NNPP (x ∈ dom(f)))).
  intro Hx.
  assert (Hfx : f[x] = μ) by (apply MKT69a; exact Hx).
  rewrite Hfx in H.
  apply MKT19a in H.
  apply MKT39; exact H.
Qed.

Theorem MKT70 : ∀ f, Function f -> f = \{\ λ x y, y = f[x] \}\.
Proof.
  intros f Hf.
  assert (fval : ∀ x y, [x,y] ∈ f -> y = f[x]).
  { intros x0 y0 Hxy0.
    unfold Value.
    apply AxiomI; intros w; split.
    - intros Hw.
      apply AxiomII; split; [unfold Ensemble; eauto |].
      intros y' Hy'.
      apply AxiomII in Hy' as [Ey' Hxy'].
      assert (Hy'y0 : y' = y0).
      { apply (proj2 Hf x0 y' y0); assumption. }
      rewrite <- Hy'y0 in Hw. exact Hw.
    - intros Hw.
      apply AxiomII in Hw as [Ew Hw].
      apply (Hw y0).
      apply AxiomII; split.
      + assert (Exy0 : Ensemble ([x0,y0])) by (unfold Ensemble; eauto).
        exact (proj2 (MKT49b x0 y0 Exy0)).
      + exact Hxy0. }
  apply AxiomI; intros z; split.
  - intros Hz.
    destruct (proj1 Hf z Hz) as [x [y Hzy]].
    assert (Hxyf : [x,y] ∈ f).
    { rewrite <- Hzy. exact Hz. }
    assert (Ezy : Ensemble ([x,y])).
    { unfold Ensemble; exists f; exact Hxyf. }
    destruct (MKT49b x y Ezy) as [Ex Ey].
    apply AxiomII; split; [rewrite Hzy; unfold Ensemble; exists f; exact Hxyf |].
    exists x; exists y; split; [exact Hzy | exact (fval x y Hxyf)].
  - intros Hz.
    apply AxiomII in Hz as [Ez Hz].
    destruct Hz as [x [y [Hzy Hy]]].
    assert (Exy : Ensemble ([x,y])).
    { rewrite Hzy in Ez. exact Ez. }
    destruct (MKT49b x y Exy) as [Ex Ey].
    assert (Efx : Ensemble f[x]).
    { rewrite <- Hy. exact Ey. }
    assert (Hxd : x ∈ dom(f)).
    { apply MKT69b'; apply MKT19b; exact Efx. }
    rewrite Hzy. rewrite Hy.
    apply AxiomII in Hxd as [Ex' Hxd].
    destruct Hxd as [y0 Hxy0].
    assert (Hy0 : y0 = f[x]) by (apply fval; exact Hxy0).
    rewrite <- Hy0. exact Hxy0.
Qed.

Theorem MKT71 : ∀ f g, Function f -> Function g
  -> (f = g <-> ∀ x, f[x] = g[x]).
Proof.
  intros f g Hf Hg.
  split.
  - intros H x. rewrite H. reflexivity.
  - intros H.
    rewrite (MKT70 f Hf).
    rewrite (MKT70 g Hg).
    apply AxiomI; intros z; split; intros Hz.
    + apply AxiomII in Hz as [Ez Hz].
      destruct Hz as [a [b [Hzab Hbf]]].
      apply AxiomII; split; [exact Ez | exists a; exists b; split; [exact Hzab |]].
      rewrite <- H. exact Hbf.
    + apply AxiomII in Hz as [Ez Hz].
      destruct Hz as [a [b [Hzab Hbg]]].
      apply AxiomII; split; [exact Ez | exists a; exists b; split; [exact Hzab |]].
      rewrite H. exact Hbg.
Qed.

Theorem MKT73 : ∀ u y, Ensemble u -> Ensemble y
  -> Ensemble ([u] × y).
Proof.
  intros u y Hu Hy.
  assert (Huy : Ensemble (∪y)) by exact (AxiomVI y Hy).
  assert (Hpowu : Ensemble (pow(u))) by exact (MKT38a Hu).
  assert (Hpowuy : Ensemble (pow(∪y))) by exact (MKT38a Huy).
  assert (Huni : Ensemble (pow(u) ∪ pow(∪y))) by exact (AxiomIV Hpowu Hpowuy).
  assert (Hpow2 : Ensemble (pow(pow(u) ∪ pow(∪y)))) by exact (MKT38a Huni).
  assert (Hpow3 : Ensemble (pow(pow(pow(u) ∪ pow(∪y))))) by exact (MKT38a Hpow2).
  assert (Hsub : ([u] × y) ⊂ pow(pow(pow(u) ∪ pow(∪y)))).
  { intros z Hz.
    apply AxiomII in Hz as [Ez Hz].
    destruct Hz as [a [b [Hzab [Hau Hby]]]].
    apply AxiomII; split; [exact Ez |].
    intros w Hw.
    assert (Ha : a = u) by (exact (proj1 (MKT41 u Hu a) Hau)).
    subst a.
    assert (Eb : Ensemble b).
    { apply (MKT33 (∪y) b (AxiomVI y Hy)).
      apply (proj1 (MKT32 b y Hby)). }
    rewrite Hzab in Hw.
    change (w ∈ Unordered (Singleton u) (Unordered u b)) in Hw.
    assert (Hsu : Ensemble (Singleton u)) by exact (MKT42 u Hu).
    assert (Hun : Ensemble (Unordered u b)) by exact (MKT46a Hu Eb).
    destruct (proj1 (MKT46b Hsu Hun w) Hw) as [Hwu | Hwub].
    - subst w.
      apply AxiomII; split; [exact Hsu |].
      intros w' Hw'.
      assert (Hw'u : w' = u) by (exact (proj1 (MKT41 u Hu w') Hw')).
      subst w'.
      apply MKT4. left. apply AxiomII; split; [exact Hu | apply MKT26a].
    - subst w.
      apply AxiomII; split; [exact Hun |].
      intros w' Hw'.
      destruct (proj1 (MKT46b Hu Eb w') Hw') as [Hw'u | Hw'b].
      * subst w'.
        apply MKT4. left. apply AxiomII; split; [exact Hu | apply MKT26a].
      * subst w'.
        apply MKT4. right. apply AxiomII; split; [exact Eb |].
        apply (proj1 (MKT32 b y Hby)).
  }
  exact (MKT33 (pow(pow(pow(u) ∪ pow(∪y)))) ([u] × y) Hpow3 Hsub).
Qed.

Theorem MKT74 : ∀ {x y}, Ensemble x -> Ensemble y
  -> Ensemble (x × y).
Proof.
  intros x y Hex Hey.
  assert (Hux : Ensemble (∪x)) by exact (AxiomVI x Hex).
  assert (Huy : Ensemble (∪y)) by exact (AxiomVI y Hey).
  assert (Hpowux : Ensemble (pow(∪x))) by exact (MKT38a Hux).
  assert (Hpowuy : Ensemble (pow(∪y))) by exact (MKT38a Huy).
  assert (Huni : Ensemble (pow(∪x) ∪ pow(∪y))) by exact (AxiomIV Hpowux Hpowuy).
  assert (Hpow2 : Ensemble (pow(pow(∪x) ∪ pow(∪y)))) by exact (MKT38a Huni).
  assert (Hpow3 : Ensemble (pow(pow(pow(∪x) ∪ pow(∪y))))) by exact (MKT38a Hpow2).
  assert (Hsub : (x × y) ⊂ pow(pow(pow(∪x) ∪ pow(∪y)))).
  { intros z Hz.
    apply AxiomII in Hz as [Ez Hz].
    destruct Hz as [a [b [Hzab [Hax Hby]]]].
    apply AxiomII; split; [exact Ez |].
    intros w Hw.
    assert (Ea : Ensemble a).
    { apply (MKT33 (∪x) a (AxiomVI x Hex)).
      apply (proj1 (MKT32 a x Hax)). }
    assert (Eb : Ensemble b).
    { apply (MKT33 (∪y) b (AxiomVI y Hey)).
      apply (proj1 (MKT32 b y Hby)). }
    rewrite Hzab in Hw.
    change (w ∈ Unordered (Singleton a) (Unordered a b)) in Hw.
    assert (Hsa : Ensemble (Singleton a)) by exact (MKT42 a Ea).
    assert (Hunab : Ensemble (Unordered a b)) by exact (MKT46a Ea Eb).
    destruct (proj1 (MKT46b Hsa Hunab w) Hw) as [Hwa | Hwab].
    - subst w.
      apply AxiomII; split; [exact Hsa |].
      intros w' Hw'.
      assert (Hw'a : w' = a) by (exact (proj1 (MKT41 a Ea w') Hw')).
      subst w'.
      apply MKT4. left. apply AxiomII; split; [exact Ea |].
      apply (proj1 (MKT32 a x Hax)).
    - subst w.
      apply AxiomII; split; [exact Hunab |].
      intros w' Hw'.
      destruct (proj1 (MKT46b Ea Eb w') Hw') as [Hw'a | Hw'b].
      * subst w'.
        apply MKT4. left. apply AxiomII; split; [exact Ea |].
        apply (proj1 (MKT32 a x Hax)).
      * subst w'.
        apply MKT4. right. apply AxiomII; split; [exact Eb |].
        apply (proj1 (MKT32 b y Hby)).
  }
  exact (MKT33 (pow(pow(pow(∪x) ∪ pow(∪y)))) (x × y) Hpow3 Hsub).
Qed.

Theorem MKT75 : ∀ f, Function f -> Ensemble dom(f) -> Ensemble f.
Proof.
  intros f Hf Hdom.
  assert (Hran : Ensemble ran(f)) by (apply AxiomV; assumption).
  assert (Hprod : Ensemble (dom(f) × ran(f))).
  { apply MKT74; assumption. }
  assert (Hsub : f ⊂ (dom(f) × ran(f))).
  { intros z Hz.
    destruct (proj1 Hf z Hz) as [x [y Hzy]].
    assert (Hxyf : [x,y] ∈ f).
    { rewrite <- Hzy. exact Hz. }
    assert (Ezy : Ensemble ([x,y])).
    { unfold Ensemble; exists f; exact Hxyf. }
    destruct (MKT49b x y Ezy) as [Ex Ey].
    apply AxiomII; split; [rewrite Hzy; unfold Ensemble; exists f; exact Hxyf |].
    exists x; exists y; split; [exact Hzy | split].
    + apply AxiomII; split; [exact Ex | exists y; exact Hxyf].
    + apply AxiomII; split; [exact Ey | exists x; exact Hxyf].
  }
  exact (MKT33 (dom(f) × ran(f)) f Hprod Hsub).
Qed.

(* 定理77 如果x与y均为集，则 Exponent y x 也是集*)
Theorem MKT77 : ∀ x y, Ensemble x -> Ensemble y
  -> Ensemble (Exponent y x).
Proof.
  intros x y Hex Hey.
  assert (Hprod : Ensemble (x × y)) by (apply MKT74; assumption).
  assert (Hpow : Ensemble (pow(x × y))) by (apply MKT38a; exact Hprod).
  assert (Hsub : Exponent y x ⊂ pow(x × y)).
  { intros f Hf.
    apply AxiomII in Hf as [Ef [Hfunct [Hdom Hran]]].
    apply AxiomII; split; [exact Ef |].
    intros z Hz.
    destruct (proj1 Hfunct z Hz) as [a [b Hzb]].
    assert (Habf : [a,b] ∈ f).
    { rewrite <- Hzb. exact Hz. }
    assert (Eab : Ensemble ([a,b])).
    { unfold Ensemble; exists f; exact Habf. }
    destruct (MKT49b a b Eab) as [Ea Eb].
    apply AxiomII; split; [rewrite Hzb; exact Eab |].
    exists a; exists b; split; [exact Hzb | split].
    + rewrite <- Hdom.
      apply AxiomII; split; [exact Ea | exists b; exact Habf].
    + apply (Hran b).
      apply AxiomII; split; [exact Eb | exists a; exact Habf].
  }
  exact (MKT33 (pow(x × y)) (Exponent y x) Hpow Hsub).
Qed.

(* A.7 良序 *)

Theorem MKT88a : ∀ {r x}, WellOrdered r x -> Asymmetric r x.
Proof.
  intros r x [Hconn Hwo].
  unfold Asymmetric.
  intros u v Hu Hv Huv Hvu.
  assert (Euv : Ensemble ([u,v])) by (unfold Ensemble; eauto).
  destruct (MKT49b u v Euv) as [Eu Ev].
  set (y := \{ λ w, w = u \/ w = v \}).
  assert (Hyx : y ⊂ x).
  { intros w Hw.
    apply AxiomII in Hw as [Ew Hw].
    destruct Hw as [Hwu | Hwv]; subst; assumption. }
  assert (Hyn : y ≠ Φ).
  { intro Hy.
    assert (Huu : u ∈ y).
    { apply AxiomII; split; [exact Eu | left; reflexivity]. }
    rewrite Hy in Huu.
    apply AxiomII in Huu as [E Huu].
    apply Huu; reflexivity. }
  destruct (Hwo y Hyx Hyn) as [z [Hz Hfirst]].
  apply AxiomII in Hz as [Ez Hz].
  destruct Hz as [Hzu | Hzv].
  - subst z.
    apply (Hfirst v).
    + apply AxiomII; split; [exact Ev | right; reflexivity].
    + exact Hvu.
  - subst z.
    apply (Hfirst u).
    + apply AxiomII; split; [exact Eu | left; reflexivity].
    + exact Huv.
Qed.

Theorem MKT88b : ∀ r x, WellOrdered r x -> Transitive r x.
Proof.
  intros r x [Hconn Hwo].
  unfold Transitive.
  intros u v w Hu Hv Hw Huv Hvw.
  assert (Euv : Ensemble ([u,v])) by (unfold Ensemble; eauto).
  assert (Evw : Ensemble ([v,w])) by (unfold Ensemble; eauto).
  destruct (MKT49b u v Euv) as [Eu Ev].
  destruct (MKT49b v w Evw) as [Ev' Ew].
  destruct (Hconn u w Hu Hw) as [Huw | [Hwu | Heq]].
  - exact Huw.
  - set (y := \{ λ t, t = u \/ t = v \/ t = w \}).
    assert (Hyx : y ⊂ x).
    { intros t Ht.
      apply AxiomII in Ht as [Et Ht].
      destruct Ht as [Htu | [Htv | Htw]]; subst; assumption. }
    assert (Hyn : y ≠ Φ).
    { intro Hy.
      assert (Huu : u ∈ y).
      { apply AxiomII; split; [exact Eu | left; reflexivity]. }
      rewrite Hy in Huu.
      apply AxiomII in Huu as [E Huu].
      apply Huu; reflexivity. }
    destruct (Hwo y Hyx Hyn) as [z [Hz Hfirst]].
    apply AxiomII in Hz as [Ez Hz].
    destruct Hz as [Hzu | [Hzv | Hzw]].
    + subst z.
      exfalso.
      apply (Hfirst w).
      * apply AxiomII; split; [exact Ew | right; right; reflexivity].
      * exact Hwu.
    + subst z.
      exfalso.
      apply (Hfirst u).
      * apply AxiomII; split; [exact Eu | left; reflexivity].
      * exact Huv.
    + subst z.
      exfalso.
      apply (Hfirst v).
      * apply AxiomII; split; [exact Ev | right; left; reflexivity].
      * exact Hvw.
  - subst w.
    assert (Hasym : Asymmetric r x).
    { apply MKT88a; split; [exact Hconn | exact Hwo]. }
    unfold Asymmetric in Hasym.
    exfalso.
    apply (Hasym u v Hu Hv Huv); exact Hvw.
Qed.

Lemma MKT_nonempty : ∀ n, n ≠ Φ -> ∃ y, y ∈ n.
Proof.
  intros n Hne.
  apply NNPP.
  intro Hn.
  apply Hne.
  apply AxiomI; intros z; split.
  - intros Hz.
    exfalso.
    apply Hn; eauto.
  - intros Hz.
    apply AxiomII in Hz as [E Hneq].
    exfalso.
    apply Hneq; reflexivity.
Qed.

Lemma MKT_wo_sub : ∀ r x y, x ⊂ y -> WellOrdered r y -> WellOrdered r x.
Proof.
  intros r x y Hxy [Hconn Hwo].
  split.
  - intros u v Hu Hv.
    exact (Hconn u v (Hxy u Hu) (Hxy v Hv)).
  - intros S HSx HSn.
    apply (Hwo S).
    + intros w Hw. apply Hxy; apply HSx; exact Hw.
    + exact HSn.
Qed.

Theorem MKT90 : ∀ n x r, n ≠ Φ -> (∀ y, y ∈ n -> rSection y r x)
  -> rSection (∩n) r x /\ rSection (∪n) r x.
Proof.
  intros n x r Hn Hsec.
  destruct (MKT_nonempty n Hn) as [y0 Hy0].
  destruct (Hsec y0 Hy0) as [Hy0x [Hw0 Hdown0]].
  destruct Hw0 as [Hconn Hwosub].
  unfold rSection.
  split.
  - (* rSection (∩n) r x *)
    split.
    + (* (∩n) ⊂ x *)
      intros w Hw.
      apply AxiomII in Hw as [Ew Hw].
      apply (Hy0x w).
      apply (Hw y0 Hy0).
    + split.
      * (* WellOrdered r x *)
        split; [exact Hconn | exact Hwosub].
      * (* closure *)
        intros u v Hu Hv Huv.
        apply AxiomII in Hv as [Ev Hv].
        assert (Eu : Ensemble u).
        { assert (Euv : Ensemble ([u,v])).
          { unfold Ensemble; exists r; exact Huv. }
          exact (proj1 (MKT49b u v Euv)). }
        apply AxiomII; split; [exact Eu |].
        intros y Hy.
        destruct (Hsec y Hy) as [Hyx [Hconn_y Hdown_y]].
        apply (Hdown_y u v Hu (Hv y Hy) Huv).
  - (* rSection (∪n) r x *)
    split.
    + (* (∪n) ⊂ x *)
      intros w Hw.
      apply AxiomII in Hw as [Ew Hw].
      destruct Hw as [y [Hwy Hy]].
      destruct (Hsec y Hy) as [Hyx [_ _]].
      exact (Hyx w Hwy).
    + split.
      * (* WellOrdered r x *)
        split; [exact Hconn | exact Hwosub].
      * (* closure *)
        intros u v Hu Hv Huv.
        assert (Eu : Ensemble u).
        { assert (Euv : Ensemble ([u,v])).
          { unfold Ensemble; exists r; exact Huv. }
          exact (proj1 (MKT49b u v Euv)). }
        apply AxiomII in Hv as [Ev Hv].
        destruct Hv as [y [Hvy Hy]].
        destruct (Hsec y Hy) as [Hyx [Hconn_y Hdown_y]].
        apply AxiomII; split; [exact Eu |].
        exists y; split; [apply (Hdown_y u v Hu Hvy Huv) | exact Hy].
Qed.

Lemma MKT_sub_not : ∀ x y, ~(x ⊂ y) -> ∃ t, t ∈ x /\ t ∉ y.
Proof.
  intros x y Hxy.
  apply NNPP; intro Hn.
  apply Hxy.
  intros t Ht.
  destruct (classic (t ∈ y)) as [Hty | Hnty]; [exact Hty |].
  exfalso.
  apply Hn; exists t; split; assumption.
Qed.

Lemma MKT_neq_sub : ∀ x y, y ⊂ x -> y ≠ x -> ∃ t, t ∈ x /\ t ∉ y.
Proof.
  intros x y Hyx Hneq.
  apply NNPP; intro Hn.
  apply Hneq.
  apply AxiomI; intros t; split.
  - exact (Hyx t).
  - intro Ht.
    destruct (classic (t ∈ y)) as [Hty | Hnty]; [exact Hty |].
    exfalso; apply Hn; exists t; split; assumption.
Qed.

Theorem MKT91 : ∀ {x y r}, rSection y r x ->  y <> x
  -> (∃ v, v ∈ x /\ y = \{ λ u, u ∈ x /\ Rrelation u r v \}).
Proof.
  intros x y r [Hyx [Hwo Hdown]] Hneq.
  destruct Hwo as [Hconn Hwosub].
  set (z := \{ λ u, u ∈ x /\ u ∉ y \}).
  destruct (classic (z ≠ Φ)) as [Hzn | Hznnot].
  - (* z has an ensemble member; use well-order *)
    assert (Hzx : z ⊂ x).
    { intros w Hw. apply AxiomII in Hw as [E [Hwx _]]. exact Hwx. }
    destruct (Hwosub z Hzx Hzn) as [v [Hvz Hvfirst]].
    apply AxiomII in Hvz as [Ev [Hvx Hvny]].
    exists v; split; [exact Hvx |].
    apply AxiomI; intros u; split.
    + intros Hu.
      assert (Huv : Rrelation u r v).
      { apply NNPP; intro Huvn.
        destruct (Hconn u v (Hyx u Hu) Hvx) as [Huv' | [Hvu | Hueq]].
        - exfalso; exact (Huvn Huv').
        - assert (Hvy : v ∈ y) by (apply (Hdown v u Hvx Hu Hvu)).
          exfalso; exact (Hvny Hvy).
        - exfalso; apply Hvny; rewrite <- Hueq; exact Hu. }
      assert (Eu : Ensemble u).
      { assert (Euv : Ensemble ([u,v])).
        { unfold Ensemble; exists r; exact Huv. }
        exact (proj1 (MKT49b u v Euv)). }
      apply AxiomII; split; [exact Eu | split; [exact (Hyx u Hu) | exact Huv]].
    + intros Hu.
      apply AxiomII in Hu as [Eu [Hux Huv]].
      apply NNPP; intro Huny.
      assert (Huz : u ∈ z).
      { apply AxiomII; split; [exact Eu | split; [exact Hux | exact Huny]]. }
      exfalso; exact (Hvfirst u Huz Huv).
  - (* no ensemble outside y; use a non-ensemble t0 *)
    assert (Hz : z = Φ) by (apply NNPP; exact Hznnot).
    destruct (MKT_neq_sub x y Hyx Hneq) as [t0 [Ht0x Ht0ny]].
    exists t0; split; [exact Ht0x |].
    apply AxiomI; intros u; split.
    + intros Hu.
      assert (Hut0 : Rrelation u r t0).
      { apply NNPP; intro Hn.
        destruct (Hconn u t0 (Hyx u Hu) Ht0x) as [Hut0' | [Ht0u | Hueq]].
        - exfalso; exact (Hn Hut0').
        - assert (Ht0y : t0 ∈ y) by (apply (Hdown t0 u Ht0x Hu Ht0u)).
          exfalso; exact (Ht0ny Ht0y).
        - exfalso; apply Ht0ny; rewrite <- Hueq; exact Hu. }
      assert (Eu : Ensemble u).
      { assert (Eut0 : Ensemble ([u,t0])).
        { unfold Ensemble; exists r; exact Hut0. }
        exact (proj1 (MKT49b u t0 Eut0)). }
      apply AxiomII; split; [exact Eu | split; [exact (Hyx u Hu) | exact Hut0]].
    + intros Hu.
      apply AxiomII in Hu as [Eu [Hux Hut0]].
      apply NNPP; intro Huny.
      assert (Huz : u ∈ z).
      { apply AxiomII; split; [exact Eu | split; [exact Hux | exact Huny]]. }
      rewrite Hz in Huz.
      apply AxiomII in Huz as [E Huz].
      exfalso; apply Huz; reflexivity.
Qed.

Theorem MKT92 : ∀ {x y z r}, rSection x r z -> rSection y r z
  -> x ⊂ y \/ y ⊂ x.
Proof.
  intros x y z r [Hxz [Hwo_z Hdownx]] [Hyz [Hwo_z' Hdowny]].
  destruct Hwo_z as [Hconn Hwosub].
  destruct (classic (x ⊂ y)) as [Hxy | Hxny].
  - left; exact Hxy.
  - right.
    apply NNPP; intro Hynx.
    destruct (MKT_sub_not x y Hxny) as [a [Hax Hany]].
    destruct (MKT_sub_not y x Hynx) as [b [Hby Hbx]].
    destruct (Hconn a b (Hxz a Hax) (Hyz b Hby)) as [Harb | [Hbra | Heq]].
    + exfalso. apply Hany. apply (Hdowny a b (Hxz a Hax) Hby Harb).
    + exfalso. apply Hbx. apply (Hdownx b a (Hyz b Hby) Hax Hbra).
    + exfalso. apply Hany. rewrite Heq; exact Hby.
Qed.

Lemma MKT_fval : ∀ f x y, Function f -> [x,y] ∈ f -> f[x] = y.
Proof.
  intros f x y Hf Hxy.
  unfold Value.
  assert (Hy : y = ∩(\{ λ y, [x,y] ∈ f \})).
  { apply AxiomI; intros w; split.
    - intros Hw.
      apply AxiomII; split; [unfold Ensemble; eauto |].
      intros y' Hy'.
      apply AxiomII in Hy' as [Ey' Hxy'].
      assert (Hy'y : y' = y).
      { apply (proj2 Hf x y' y); assumption. }
      rewrite Hy'y. exact Hw.
    - intros Hw.
      apply AxiomII in Hw as [Ew Hw].
      apply (Hw y).
      apply AxiomII; split.
      + assert (Exy : Ensemble ([x,y])) by (unfold Ensemble; eauto).
        exact (proj2 (MKT49b x y Exy)).
      + exact Hxy. }
  symmetry. exact Hy.
Qed.

Lemma MKT_dom_val : ∀ f x, Function f -> x ∈ dom(f) -> [x, f[x]] ∈ f.
Proof.
  intros f x Hf Hx.
  apply AxiomII in Hx as [Ex Hx].
  destruct Hx as [y Hxy].
  assert (Hfx : f[x] = y) by (apply (MKT_fval f x y Hf); exact Hxy).
  rewrite Hfx; exact Hxy.
Qed.

Theorem MKT94 : ∀ {x r y f}, rSection x r y -> Order_Pr f r r
  -> On f x -> To f y -> (∀ u, u ∈ x -> ~ Rrelation f[u] r u).
Proof.
  intros x r y f [Hxy [Hwo_y Hdown]] Horder Hon Hto.
  destruct Horder as [Hf [Hwo_dom [Hwo_ran Hord]]].
  destruct Hon as [_ Hdom].
  destruct Hto as [_ Hran].
  intros u Hu Hfu.
  set (S := \{ λ w, w ∈ x /\ Rrelation f[w] r w \}).
  assert (HSx : S ⊂ x).
  { intros w Hw. apply AxiomII in Hw as [E [Hwx _]]. exact Hwx. }
  assert (HSn : S ≠ Φ).
  { intro HS.
    assert (Efu_u : Ensemble ([f[u], u])).
    { unfold Ensemble; exists r; exact Hfu. }
    destruct (MKT49b (f[u]) u Efu_u) as [_ Eu].
    assert (Huu : u ∈ S).
    { apply AxiomII; split; [exact Eu | split; [exact Hu | exact Hfu]]. }
    rewrite HS in Huu.
    apply AxiomII in Huu as [E Huu].
    exfalso; apply Huu; reflexivity. }
  assert (Hwo_x : WellOrdered r x) by (apply (MKT_wo_sub r x y Hxy Hwo_y)).
  destruct Hwo_x as [Hconn Hwosub].
  destruct (Hwosub S HSx HSn) as [v [HvS Hvfirst]].
  apply AxiomII in HvS as [Ev [Hvx Hfv_v]].
  (* f[v] ∈ ran(f) *)
  assert (Hvd : v ∈ dom(f)).
  { rewrite Hdom; exact Hvx. }
  assert (Hv_fv : [v, f[v]] ∈ f) by (apply (MKT_dom_val f v Hf Hvd)).
  assert (Efv : Ensemble (f[v])).
  { assert (Efu_v : Ensemble ([f[v], v])).
    { unfold Ensemble; exists r; exact Hfv_v. }
    exact (proj1 (MKT49b (f[v]) v Efu_v)). }
  assert (Hfvr : f[v] ∈ ran(f)).
  { apply AxiomII; split; [exact Efv | exists v; exact Hv_fv]. }
  assert (Hfvy : f[v] ∈ y) by (exact (Hran (f[v]) Hfvr)).
  (* f[v] ∈ x by downward closure *)
  assert (Hfvx : f[v] ∈ x) by (apply (Hdown (f[v]) v Hfvy Hvx Hfv_v)).
  (* order preservation *)
  assert (Hf_fv : Rrelation f[f[v]] r f[v]).
  { apply (Hord (f[v]) v).
    - rewrite Hdom; exact Hfvx.
    - rewrite Hdom; exact Hvx.
    - exact Hfv_v. }
  (* f[v] ∈ S *)
  assert (HfvS : f[v] ∈ S).
  { apply AxiomII; split; [exact Efv | split; [exact Hfvx | exact Hf_fv]]. }
  exfalso.
  exact (Hvfirst (f[v]) HfvS Hfv_v).
Qed.

Lemma MKT_inv_in : ∀ f a b, Ensemble a -> Ensemble b
  -> ([a,b] ∈ f⁻¹ <-> [b,a] ∈ f).
Proof.
  intros f a b Ea Eb; split.
  - intros Hab.
    apply AxiomII in Hab as [E Hab].
    destruct Hab as [u [v [Huv Hvu]]].
    destruct (MKT49b a b E) as [Ea' Eb'].
    assert (Evu : Ensemble ([v,u])).
    { unfold Ensemble; exists f; exact Hvu. }
    destruct (MKT49b v u Evu) as [Ev Eu].
    destruct (proj1 (MKT55 a b u v Ea' Eb') Huv) as [Hau Hbv].
    rewrite <- Hau in Hvu.
    rewrite <- Hbv in Hvu.
    exact Hvu.
  - intros Hba.
    apply AxiomII; split.
    + apply MKT49a; assumption.
    + exists a; exists b; split; [reflexivity | exact Hba].
Qed.

Theorem MKT96a : ∀ {f r s}, Order_Pr f r s -> Function1_1 f.
Proof.
  intros f r s [Hf [Hwd [Hwr Hord]]].
  unfold Function1_1.
  split; [exact Hf |].
  unfold Function.
  split.
  - (* Relation (f⁻¹) *)
    intros z Hz.
    apply AxiomII in Hz as [Ez Hz].
    destruct Hz as [a [b [Hzab Hba]]].
    exists a; exists b; exact Hzab.
  - (* single-valued *)
    intros a b c Hab Hac.
    assert (Eab : Ensemble ([a,b])) by (unfold Ensemble; eauto).
    assert (Eac : Ensemble ([a,c])) by (unfold Ensemble; eauto).
    destruct (MKT49b a b Eab) as [Ea Eb].
    destruct (MKT49b a c Eac) as [Ea' Ec].
    assert (Hba : [b,a] ∈ f) by (apply (proj1 (MKT_inv_in f a b Ea Eb)); exact Hab).
    assert (Hca : [c,a] ∈ f) by (apply (proj1 (MKT_inv_in f a c Ea' Ec)); exact Hac).
    assert (Hfb : f[b] = a) by (apply (MKT_fval f b a Hf); exact Hba).
    assert (Hfc : f[c] = a) by (apply (MKT_fval f c a Hf); exact Hca).
    assert (Hbd : b ∈ dom(f)).
    { apply AxiomII; split; [exact Eb | exists a; exact Hba]. }
    assert (Hcd : c ∈ dom(f)).
    { apply AxiomII; split; [exact Ec | exists a; exact Hca]. }
    destruct Hwd as [Hconn Hwosub].
    assert (Hasym : Asymmetric s ran(f)) by (apply MKT88a; exact Hwr).
    unfold Asymmetric in Hasym.
    assert (Har : a ∈ ran(f)).
    { apply AxiomII; split; [exact Ea | exists b; exact Hba]. }
    apply NNPP; intro Hbc.
    destruct (Hconn b c Hbd Hcd) as [Hbrc | [Hcrb | Heq]].
    + assert (Hfb_fc : Rrelation f[b] s f[c]) by (apply (Hord b c Hbd Hcd Hbrc)).
      rewrite Hfb in Hfb_fc. rewrite Hfc in Hfb_fc.
      exact (Hasym a a Har Har Hfb_fc Hfb_fc).
    + assert (Hfc_fb : Rrelation f[c] s f[b]) by (apply (Hord c b Hcd Hbd Hcrb)).
      rewrite Hfc in Hfc_fb. rewrite Hfb in Hfc_fb.
      exact (Hasym a a Har Har Hfc_fb Hfc_fb).
    + apply Hbc; exact Heq.
Qed.

Lemma MKT_dom_inv : ∀ f, dom(f⁻¹) = ran(f).
Proof.
  intros f.
  apply AxiomI; intros x; split.
  - intros Hx.
    apply AxiomII in Hx as [Ex Hx].
    destruct Hx as [y Hxy].
    assert (Exy : Ensemble ([x,y])) by (unfold Ensemble; eauto).
    destruct (MKT49b x y Exy) as [Ex' Ey].
    assert (Hyx : [y,x] ∈ f).
    { apply (proj1 (MKT_inv_in f x y Ex' Ey)); exact Hxy. }
    apply AxiomII; split; [exact Ex' | exists y; exact Hyx].
  - intros Hx.
    apply AxiomII in Hx as [Ex Hx].
    destruct Hx as [y Hyx].
    assert (Eyx : Ensemble ([y,x])) by (unfold Ensemble; eauto).
    destruct (MKT49b y x Eyx) as [Ey Ex'].
    assert (Hxy : [x,y] ∈ f⁻¹).
    { apply (proj2 (MKT_inv_in f x y Ex' Ey)); exact Hyx. }
    apply AxiomII; split; [exact Ex' | exists y; exact Hxy].
Qed.

Lemma MKT_ran_inv : ∀ f, ran(f⁻¹) = dom(f).
Proof.
  intros f.
  apply AxiomI; intros y; split.
  - intros Hy.
    apply AxiomII in Hy as [Ey Hy].
    destruct Hy as [x Hxy].
    assert (Exy : Ensemble ([x,y])) by (unfold Ensemble; eauto).
    destruct (MKT49b x y Exy) as [Ex Ey'].
    assert (Hyx : [y,x] ∈ f).
    { apply (proj1 (MKT_inv_in f x y Ex Ey')); exact Hxy. }
    apply AxiomII; split; [exact Ey' | exists x; exact Hyx].
  - intros Hy.
    apply AxiomII in Hy as [Ey Hy].
    destruct Hy as [x Hyx].
    assert (Eyx : Ensemble ([y,x])) by (unfold Ensemble; eauto).
    destruct (MKT49b y x Eyx) as [Ey' Ex].
    assert (Hxy : [x,y] ∈ f⁻¹).
    { apply (proj2 (MKT_inv_in f x y Ex Ey')); exact Hyx. }
    apply AxiomII; split; [exact Ey' | exists x; exact Hxy].
Qed.

Theorem MKT96b : ∀ {f r s}, Order_Pr f r s -> Order_Pr (f⁻¹) s r.
Proof.
  intros f r s Horder.
  destruct Horder as [Hf [Hwd [Hwr Hord]]].
  assert (H96 : Function1_1 f).
  { apply (MKT96a (f:=f) (r:=r) (s:=s)); split; [exact Hf | split; [exact Hwd | split; [exact Hwr | exact Hord]]]. }
  destruct H96 as [_ Hinvf].
  unfold Order_Pr.
  split; [exact Hinvf |].
  split.
  - rewrite MKT_dom_inv; exact Hwr.
  - split.
    + rewrite MKT_ran_inv; exact Hwd.
    + intros u v Hu Hv Huv.
      rewrite MKT_dom_inv in Hu, Hv.
      pose proof Hu as Huran.
      pose proof Hv as Hvran.
      apply AxiomII in Hu as [Eu Hu].
      apply AxiomII in Hv as [Ev Hv].
      destruct Hu as [a Hua].
      destruct Hv as [b Hvb].
      assert (Hfau : f[a] = u) by (apply (MKT_fval f a u Hf); exact Hua).
      assert (Hfbv : f[b] = v) by (apply (MKT_fval f b v Hf); exact Hvb).
      assert (Eau : Ensemble ([a,u])) by (unfold Ensemble; exists f; exact Hua).
      destruct (MKT49b a u Eau) as [Ea Eu'].
      assert (Ebv : Ensemble ([b,v])) by (unfold Ensemble; exists f; exact Hvb).
      destruct (MKT49b b v Ebv) as [Eb Ev'].
      assert (Hua_inv : [u,a] ∈ f⁻¹).
      { apply (proj2 (MKT_inv_in f u a Eu' Ea)); exact Hua. }
      assert (Hvb_inv : [v,b] ∈ f⁻¹).
      { apply (proj2 (MKT_inv_in f v b Ev' Eb)); exact Hvb. }
      assert (Hu_a : (f⁻¹)[u] = a) by (apply (MKT_fval (f⁻¹) u a Hinvf); exact Hua_inv).
      assert (Hv_b : (f⁻¹)[v] = b) by (apply (MKT_fval (f⁻¹) v b Hinvf); exact Hvb_inv).
      rewrite Hu_a. rewrite Hv_b.
      assert (Hadu : a ∈ dom(f)).
      { apply AxiomII; split; [exact Ea | exists u; exact Hua]. }
      assert (Hbdu : b ∈ dom(f)).
      { apply AxiomII; split; [exact Eb | exists v; exact Hvb]. }
      destruct Hwd as [Hconn Hwosub].
      assert (Hasym : Asymmetric s ran(f)) by (apply MKT88a; exact Hwr).
      unfold Asymmetric in Hasym.
      destruct (Hconn a b Hadu Hbdu) as [Harb | [Hbra | Heq]].
      * exact Harb.
      * assert (Hfs : Rrelation f[b] s f[a]).
        { apply (Hord b a Hbdu Hadu Hbra). }
        rewrite Hfbv in Hfs. rewrite Hfau in Hfs.
        exfalso. exact (Hasym v u Hvran Huran Hfs Huv).
      * assert (Hfv_a : f[a] = v).
        { rewrite <- Heq in Hfbv. exact Hfbv. }
        assert (Huv_eq : u = v) by congruence.
        rewrite <- Huv_eq in Huv.
        exfalso. exact (Hasym u u Huran Huran Huv Huv).
Qed.

Theorem MKT96 : ∀ f r s, Order_Pr f r s
  -> Function1_1 f /\ Order_Pr (f⁻¹) s r.
Proof.
  intros f r s Horder.
  split.
  - apply (MKT96a (f:=f) (r:=r) (s:=s)); exact Horder.
  - apply (MKT96b (f:=f) (r:=r) (s:=s)); exact Horder.
Qed.

Lemma MKT_inj : ∀ f r s, Order_Pr f r s -> ∀ a b,
  a ∈ dom(f) -> b ∈ dom(f) -> f[a] = f[b] -> a = b.
Proof.
  intros f r s Horder a b Ha Hb Hfab.
  assert (Hf : Function f) by (destruct Horder as [Hf _]; exact Hf).
  assert (H11 : Function1_1 f).
  { apply (MKT96a (f:=f) (r:=r) (s:=s)); exact Horder. }
  destruct H11 as [_ Hinv].
  assert (Ha_f : [a, f[a]] ∈ f) by (apply (MKT_dom_val f a Hf Ha)).
  assert (Hb_f : [b, f[b]] ∈ f) by (apply (MKT_dom_val f b Hf Hb)).
  assert (Hb_fa : [b, f[a]] ∈ f).
  { rewrite <- Hfab in Hb_f. exact Hb_f. }
  apply AxiomII in Ha as [Ea _].
  apply AxiomII in Hb as [Eb _].
  assert (Efa : Ensemble (f[a])).
  { assert (Eaf : Ensemble ([a, f[a]])) by (unfold Ensemble; exists f; exact Ha_f).
    exact (proj2 (MKT49b a (f[a]) Eaf)). }
  assert (Hfa_b : [f[a], b] ∈ f⁻¹).
  { apply (proj2 (MKT_inv_in f (f[a]) b Efa Eb)); exact Hb_fa. }
  assert (Hfa_a : [f[a], a] ∈ f⁻¹).
  { apply (proj2 (MKT_inv_in f (f[a]) a Efa Ea)); exact Ha_f. }
  symmetry.
  apply (proj2 Hinv (f[a]) b a); assumption.
Qed.

Lemma MKT_agree : ∀ f g r s x y,
  Order_Pr f r s -> Order_Pr g r s
  -> rSection dom(f) r x -> rSection dom(g) r x
  -> rSection ran(f) s y -> rSection ran(g) s y
  -> dom(f) ⊂ dom(g) -> f ⊂ g.
Proof.
  intros f g r s x y Horderf Horderg Hdf Hdg Hrf Hrg Hdom_sub.
  pose proof Horderf as Horderf0.
  pose proof Horderg as Horderg0.
  destruct Horderf as [Hf [Hwfdom [Hwfran Hordf]]].
  destruct Horderg as [Hg [Hwgdom [Hwgran Hordg]]].
  destruct Hdf as [Hdf_sub [Hdf_wo Hdf_down]].
  destruct Hdg as [Hdg_sub [Hdg_wo Hdg_down]].
  destruct Hrf as [Hrf_sub [Hrf_wo Hrf_down]].
  destruct Hrg as [Hrg_sub [Hrg_wo Hrg_down]].
  destruct Hdf_wo as [Hconn_df Hwosub_df].
  destruct Hdg_wo as [Hconn_dg Hwosub_dg].
  destruct Hrg_wo as [Hconn_sy Hwosub_sy].
  assert (Hagree : ∀ a, a ∈ dom(f) -> f[a] = g[a]).
  { intros a Ha.
    apply NNPP; intro Hne.
    set (S := \{ λ w, w ∈ dom(f) /\ f[w] ≠ g[w] \}).
    assert (HSx : S ⊂ dom(f)).
    { intros w Hw. apply AxiomII in Hw as [E [Hw_ _]]. exact Hw_. }
    assert (HSn : S ≠ Φ).
    { intro HS.
      assert (Haa : a ∈ S).
      { apply AxiomII; split.
        - apply AxiomII in Ha as [Ea _]. exact Ea.
        - split; [exact Ha | exact Hne]. }
      rewrite HS in Haa.
      apply AxiomII in Haa as [E Haa].
      exfalso; apply Haa; reflexivity. }
    destruct (Hwosub_df S (fun w Hw => Hdf_sub w (HSx w Hw)) HSn) as [a0 [Ha0S Ha0first]].
    apply AxiomII in Ha0S as [Ea0 [Ha0df Hne0]].
    assert (Ha0dg : a0 ∈ dom(g)) by (exact (Hdom_sub a0 Ha0df)).
    assert (Ha0_fa0 : [a0, f[a0]] ∈ f) by (apply (MKT_dom_val f a0 Hf Ha0df)).
    assert (Ha0_ga0 : [a0, g[a0]] ∈ g) by (apply (MKT_dom_val g a0 Hg Ha0dg)).
    assert (Efa0 : Ensemble (f[a0])).
    { assert (Ea0fa0 : Ensemble ([a0, f[a0]])) by (unfold Ensemble; exists f; exact Ha0_fa0).
      exact (proj2 (MKT49b a0 (f[a0]) Ea0fa0)). }
    assert (Ega0 : Ensemble (g[a0])).
    { assert (Ea0ga0 : Ensemble ([a0, g[a0]])) by (unfold Ensemble; exists g; exact Ha0_ga0).
      exact (proj2 (MKT49b a0 (g[a0]) Ea0ga0)). }
    assert (Hfa0r : f[a0] ∈ ran(f)).
    { apply AxiomII; split; [exact Efa0 | exists a0; exact Ha0_fa0]. }
    assert (Hga0rg : g[a0] ∈ ran(g)).
    { apply AxiomII; split; [exact Ega0 | exists a0; exact Ha0_ga0]. }
    assert (Hfa0y : f[a0] ∈ y) by (exact (Hrf_sub (f[a0]) Hfa0r)).
    assert (Hga0y : g[a0] ∈ y) by (exact (Hrg_sub (g[a0]) Hga0rg)).
    assert (Hagree_pred : ∀ w, w ∈ dom(f) -> Rrelation w r a0 -> f[w] = g[w]).
    { intros w Hw Hwr.
      apply NNPP; intro Hwn.
      assert (HwS : w ∈ S).
      { apply AxiomII; split.
        - apply AxiomII in Hw as [Ew _]. exact Ew.
        - split; [exact Hw | exact Hwn]. }
      exfalso; exact (Ha0first w HwS Hwr). }
    destruct (Hconn_sy (f[a0]) (g[a0]) Hfa0y Hga0y) as [Hfag | [Hgaf | Hfge]].
    + (* f[a0] s g[a0] *)
      assert (Hfa0rg : f[a0] ∈ ran(g)).
      { apply (Hrg_down (f[a0]) (g[a0]) Hfa0y Hga0rg Hfag). }
      pose proof Hfa0rg as Hfa0rg0.
      apply AxiomII in Hfa0rg as [Efa0' Hfa0rg].
      destruct Hfa0rg as [a' Ha'fa0].
      assert (Hga' : g[a'] = f[a0]) by (apply (MKT_fval g a' (f[a0]) Hg); exact Ha'fa0).
      assert (Ea'fa0 : Ensemble ([a', f[a0]])) by (unfold Ensemble; exists g; exact Ha'fa0).
      destruct (MKT49b a' (f[a0]) Ea'fa0) as [Ea' _].
      assert (Ha'dg : a' ∈ dom(g)).
      { apply AxiomII; split; [exact Ea' | exists (f[a0]); exact Ha'fa0]. }
      destruct (Hconn_dg a' a0 (Hdg_sub a' Ha'dg) (Hdg_sub a0 Ha0dg)) as [Ha'ra0 | [Ha0ra' | Ha'eq]].
      * (* a' r a0 *)
        assert (Ha'x : a' ∈ x) by (exact (Hdg_sub a' Ha'dg)).
        assert (Ha'df : a' ∈ dom(f)) by (apply (Hdf_down a' a0 Ha'x Ha0df Ha'ra0)).
        assert (Hagr : f[a'] = g[a']) by (apply (Hagree_pred a' Ha'df Ha'ra0)).
        assert (Hfa' : f[a'] = f[a0]).
        { rewrite Hagr. exact Hga'. }
        assert (Ha'eq0 : a' = a0) by (apply (MKT_inj f r s Horderf0 a' a0 Ha'df Ha0df); exact Hfa').
        assert (Hga0fa0 : g[a0] = f[a0]).
        { rewrite Ha'eq0 in Hga'. exact Hga'. }
        exfalso. exact (Hne0 (eq_sym Hga0fa0)).
      * (* a0 r a' *)
        assert (Hgord0 : Rrelation g[a0] s g[a']).
        { apply (Hordg a0 a' Ha0dg Ha'dg Ha0ra'). }
        rewrite Hga' in Hgord0.
        assert (Hasym : Asymmetric s ran(g)) by (apply MKT88a; exact Hwgran).
        unfold Asymmetric in Hasym.
        exfalso. exact (Hasym (g[a0]) (f[a0]) Hga0rg Hfa0rg0 Hgord0 Hfag).
      * (* a' = a0 *)
        assert (Hga0fa0 : g[a0] = f[a0]).
        { rewrite Ha'eq in Hga'. exact Hga'. }
        exfalso. exact (Hne0 (eq_sym Hga0fa0)).
    + (* g[a0] s f[a0] *)
      assert (Hga0rf : g[a0] ∈ ran(f)).
      { apply (Hrf_down (g[a0]) (f[a0]) Hga0y Hfa0r Hgaf). }
      pose proof Hga0rf as Hga0rf0.
      apply AxiomII in Hga0rf as [Ega0' Hga0rf].
      destruct Hga0rf as [b' Hb'ga0].
      assert (Hfb' : f[b'] = g[a0]) by (apply (MKT_fval f b' (g[a0]) Hf); exact Hb'ga0).
      pose proof Hfb' as Hfb'0.
      assert (Eb'ga0 : Ensemble ([b', g[a0]])) by (unfold Ensemble; exists f; exact Hb'ga0).
      destruct (MKT49b b' (g[a0]) Eb'ga0) as [Eb' _].
      assert (Hb'df : b' ∈ dom(f)).
      { apply AxiomII; split; [exact Eb' | exists (g[a0]); exact Hb'ga0]. }
      destruct (Hconn_df b' a0 (Hdf_sub b' Hb'df) (Hdf_sub a0 Ha0df)) as [Hb'ra0 | [Ha0rb' | Hb'eq]].
      * (* b' r a0 *)
        assert (Hb'x : b' ∈ x) by (exact (Hdf_sub b' Hb'df)).
        assert (Hb'dg : b' ∈ dom(g)) by (exact (Hdom_sub b' Hb'df)).
        assert (Hagr : f[b'] = g[b']) by (apply (Hagree_pred b' Hb'df Hb'ra0)).
        assert (Hgb' : g[b'] = g[a0]).
        { rewrite Hagr in Hfb'. exact Hfb'. }
        assert (Hb'eq0 : b' = a0) by (apply (MKT_inj g r s Horderg0 b' a0 Hb'dg Ha0dg); exact Hgb').
        assert (Hfa0ga0 : f[a0] = g[a0]).
        { rewrite Hb'eq0 in Hfb'0. exact Hfb'0. }
        exfalso. exact (Hne0 Hfa0ga0).
      * (* a0 r b' *)
        assert (Hford0 : Rrelation f[a0] s f[b']).
        { apply (Hordf a0 b' Ha0df Hb'df Ha0rb'). }
        rewrite Hfb'0 in Hford0.
        assert (Hasym : Asymmetric s ran(f)) by (apply MKT88a; exact Hwfran).
        unfold Asymmetric in Hasym.
        exfalso. exact (Hasym (f[a0]) (g[a0]) Hfa0r Hga0rf0 Hford0 Hgaf).
      * (* b' = a0 *)
        assert (Hfa0ga0 : f[a0] = g[a0]).
        { rewrite Hb'eq in Hfb'0. exact Hfb'0. }
        exfalso. exact (Hne0 Hfa0ga0).
    + (* f[a0] = g[a0] *)
      exfalso. exact (Hne0 Hfge).
  }
  (* f ⊂ g *)
  intros z Hz.
  destruct (proj1 Hf z Hz) as [a [b Hzb]].
  assert (Habf : [a,b] ∈ f) by (rewrite <- Hzb; exact Hz).
  assert (Ezb : Ensemble ([a,b])) by (unfold Ensemble; exists f; exact Habf).
  destruct (MKT49b a b Ezb) as [Ea Eb].
  assert (Hfb : f[a] = b) by (apply (MKT_fval f a b Hf); exact Habf).
  assert (Had : a ∈ dom(f)).
  { apply AxiomII; split; [exact Ea | exists b; exact Habf]. }
  assert (Hag : f[a] = g[a]) by (apply (Hagree a Had)).
  assert (Hadg : a ∈ dom(g)) by (exact (Hdom_sub a Had)).
  assert (Ha_ga : [a, g[a]] ∈ g) by (apply (MKT_dom_val g a Hg Hadg)).
  assert (Hbga : b = g[a]).
  { rewrite Hag in Hfb. symmetry. exact Hfb. }
  rewrite Hzb. rewrite Hbga. exact Ha_ga.
Qed.

Theorem MKT97 :  ∀ {f g r s x y}, Order_Pr f r s -> Order_Pr g r s
  -> rSection dom(f) r x -> rSection dom(g) r x
  -> rSection ran(f) s y -> rSection ran(g) s y -> f ⊂ g \/ g ⊂ f.
Proof.
  intros f g r s x y Horderf Horderg Hdf Hdg Hrf Hrg.
  destruct (MKT92 (x:=dom(f)) (y:=dom(g)) (z:=x) (r:=r) Hdf Hdg) as [Hd_sub | Hd_sub].
  - left. apply (MKT_agree f g r s x y Horderf Horderg Hdf Hdg Hrf Hrg Hd_sub).
  - right. apply (MKT_agree g f r s x y Horderg Horderf Hdg Hdf Hrg Hrf Hd_sub).
Qed.

Lemma MKT91_strong : ∀ {x y r}, rSection y r x -> y <> x
  -> (∃ v, Ensemble v /\ v ∈ x /\ y = \{ λ u, u ∈ x /\ Rrelation u r v \})
  \/ (∀ u, Ensemble u -> u ∈ x -> u ∈ y).
Proof.
  intros x y r [Hyx [Hwo Hdown]] Hneq.
  destruct Hwo as [Hconn Hwosub].
  set (z := \{ λ u, u ∈ x /\ u ∉ y \}).
  destruct (classic (z ≠ Φ)) as [Hzn | Hznnot].
  - left.
    assert (Hzx : z ⊂ x).
    { intros w Hw. apply AxiomII in Hw as [E [Hwx _]]. exact Hwx. }
    destruct (Hwosub z Hzx Hzn) as [v [Hvz Hvfirst]].
    apply AxiomII in Hvz as [Ev [Hvx Hvny]].
    exists v; split; [exact Ev | split; [exact Hvx |]].
    apply AxiomI; intros u; split.
    + intros Hu.
      assert (Huv : Rrelation u r v).
      { apply NNPP; intro Huvn.
        destruct (Hconn u v (Hyx u Hu) Hvx) as [Huv' | [Hvu | Hueq]].
        - exfalso; exact (Huvn Huv').
        - assert (Hvy : v ∈ y) by (apply (Hdown v u Hvx Hu Hvu)).
          exfalso; exact (Hvny Hvy).
        - exfalso; apply Hvny; rewrite <- Hueq; exact Hu. }
      assert (Eu : Ensemble u).
      { assert (Euv : Ensemble ([u,v])).
        { unfold Ensemble; exists r; exact Huv. }
        exact (proj1 (MKT49b u v Euv)). }
      apply AxiomII; split; [exact Eu | split; [exact (Hyx u Hu) | exact Huv]].
    + intros Hu.
      apply AxiomII in Hu as [Eu [Hux Huv]].
      apply NNPP; intro Huny.
      assert (Huz : u ∈ z).
      { apply AxiomII; split; [exact Eu | split; [exact Hux | exact Huny]]. }
      exfalso; exact (Hvfirst u Huz Huv).
  - right.
    assert (Hz : z = Φ) by (apply NNPP; exact Hznnot).
    intros u Eu Hux.
    apply NNPP; intro Hun.
    assert (Huz : u ∈ z).
    { apply AxiomII; split; [exact Eu | split; [exact Hux | exact Hun]]. }
    rewrite Hz in Huz.
    apply AxiomII in Huz as [E Huz].
    exfalso; apply Huz; reflexivity.
Qed.

Lemma OPXY_c : ∀ f x y r s, Order_PXY f x y r s
  -> Function f /\ Order_Pr f r s /\ rSection dom(f) r x /\ rSection ran(f) s y.
Proof.
  intros f x y r s [Hwx [Hwy [Hop [Hd Hr]]]].
  split; [destruct Hop as [Hf _]; exact Hf |].
  split; [exact Hop |].
  split; [exact Hd | exact Hr].
Qed.

Theorem MKT99 : ∀ {r s x y}, WellOrdered r x -> WellOrdered s y
  -> ∃ f, Function f /\ Order_PXY f x y r s
    /\(dom(f) = x \/ ran(f) = y).
Proof.
  intros r s x y Hwox Hwoy.
  set (g := \{ λ z, ∃ f, Order_PXY f x y r s /\ z ∈ f \}).
  assert (Hgfunc : Function g).
  { unfold Function. split.
    - intros z1 Hz1.
      apply AxiomII in Hz1 as [Ez1 Hz1].
      destruct Hz1 as [f [Hfop Hz1f]].
      destruct (OPXY_c f x y r s Hfop) as [Hffunc _].
      assert (Hrel : ∀ z0, z0 ∈ f -> ∃ x y, z0 = [x,y]).
      { unfold Relation; exact (proj1 Hffunc). }
      destruct (Hrel z1 Hz1f) as [a [b Hz1b]].
      exists a; exists b; exact Hz1b.
    - intros a b c Hab Hac.
      apply AxiomII in Hab as [Eab Hab].
      destruct Hab as [f1 [Hf1op Habf1]].
      apply AxiomII in Hac as [Eac Hac].
      destruct Hac as [f2 [Hf2op Hacf2]].
      destruct (OPXY_c f1 x y r s Hf1op) as [Hf1func [Hf1pr [Hf1ds Hf1rs]]].
      destruct (OPXY_c f2 x y r s Hf2op) as [Hf2func [Hf2pr [Hf2ds Hf2rs]]].
      destruct (MKT97 (f:=f1) (g:=f2) (r:=r) (s:=s) (x:=x) (y:=y) Hf1pr Hf2pr Hf1ds Hf2ds Hf1rs Hf2rs) as [Hsub12 | Hsub21].
      + apply (proj2 Hf2func a b c).
        * exact (Hsub12 ([a,b]) Habf1).
        * exact Hacf2.
      + apply (proj2 Hf1func a b c).
        * exact Habf1.
        * exact (Hsub21 ([a,c]) Hacf2). }
  assert (Hgdom_sect : rSection dom(g) r x).
  { unfold rSection.
    split.
    - intros z Hz.
      apply AxiomII in Hz as [Ez Hz].
      destruct Hz as [w Hzw].
      apply AxiomII in Hzw as [Ezw Hzw].
      destruct Hzw as [f [Hfop Hzwf]].
      destruct (OPXY_c f x y r s Hfop) as [_ [_ [Hfd _]]].
      destruct Hfd as [Hfdsub _].
      assert (Hzdf : z ∈ dom(f)).
      { apply AxiomII; split; [exact Ez | exists w; exact Hzwf]. }
      exact (Hfdsub z Hzdf).
    - split.
      + exact Hwox.
      + intros u v Hu Hv Huv.
        apply AxiomII in Hv as [Ev Hv].
        destruct Hv as [w Hvw].
        apply AxiomII in Hvw as [Evw Hvw].
        destruct Hvw as [f [Hfop Hvwf]].
        destruct (OPXY_c f x y r s Hfop) as [_ [_ [Hfd _]]].
        destruct Hfd as [Hfdsub [Hfdwo Hfdclose]].
        assert (Hvdf : v ∈ dom(f)).
        { apply AxiomII; split; [exact Ev | exists w; exact Hvwf]. }
        assert (Hudf : u ∈ dom(f)) by (apply (Hfdclose u v Hu Hvdf Huv)).
        apply AxiomII in Hudf as [Eu' Hudf].
        destruct Hudf as [w' Hufw'].
        apply AxiomII; split; [exact Eu' | exists w'].
        apply AxiomII; split.
        * assert (Euw' : Ensemble ([u,w'])).
          { unfold Ensemble; exists f; exact Hufw'. }
          apply MKT49a; [exact Eu' | exact (proj2 (MKT49b u w' Euw'))].
        * exists f; split; [exact Hfop | exact Hufw']. }
  assert (Hgran_sect : rSection ran(g) s y).
  { unfold rSection.
    split.
    - intros z Hz.
      apply AxiomII in Hz as [Ez Hz].
      destruct Hz as [w Hzw].
      apply AxiomII in Hzw as [Ezw Hzw].
      destruct Hzw as [f [Hfop Hzwf]].
      destruct (OPXY_c f x y r s Hfop) as [_ [_ [_ Hfr]]].
      destruct Hfr as [Hfrsub _].
      assert (Hzrf : z ∈ ran(f)).
      { apply AxiomII; split; [exact Ez | exists w; exact Hzwf]. }
      exact (Hfrsub z Hzrf).
    - split.
      + exact Hwoy.
      + intros u v Hu Hv Huv.
        apply AxiomII in Hv as [Ev Hv].
        destruct Hv as [w Hwv].
        apply AxiomII in Hwv as [Evw Hwv].
        destruct Hwv as [f [Hfop Hwvf]].
        destruct (OPXY_c f x y r s Hfop) as [_ [_ [_ Hfr]]].
        destruct Hfr as [Hfrsub [Hfrwo Hfrclose]].
        assert (Hvrf : v ∈ ran(f)).
        { apply AxiomII; split; [exact Ev | exists w; exact Hwvf]. }
        assert (Hurf : u ∈ ran(f)) by (apply (Hfrclose u v Hu Hvrf Huv)).
        apply AxiomII in Hurf as [Eu' Hurf].
        destruct Hurf as [w' Hw'u].
        apply AxiomII; split; [exact Eu' | exists w'].
        apply AxiomII; split.
        * assert (Ew'u : Ensemble ([w',u])).
          { unfold Ensemble; exists f; exact Hw'u. }
          apply MKT49a; [exact (proj1 (MKT49b w' u Ew'u)) | exact Eu'].
        * exists f; split; [exact Hfop | exact Hw'u]. }
  assert (Hgorder : Order_Pr g r s).
  { unfold Order_Pr.
    split; [exact Hgfunc |].
    split.
    - destruct Hgdom_sect as [Hdgx [Hwo_x Hdgclose]].
      apply (MKT_wo_sub r dom(g) x Hdgx Hwox).
    - split.
      + destruct Hgran_sect as [Hrgx [Hwo_y Hrgclose]].
        apply (MKT_wo_sub s ran(g) y Hrgx Hwoy).
      + intros u v Hudg Hvdg Huv.
        apply AxiomII in Hudg as [Eu Hudg].
        apply AxiomII in Hvdg as [Ev Hvdg].
        destruct Hudg as [u' Huu'].
        destruct Hvdg as [v' Hvv'].
        assert (Hgu : g[u] = u') by (apply (MKT_fval g u u' Hgfunc); exact Huu').
        assert (Hgv : g[v] = v') by (apply (MKT_fval g v v' Hgfunc); exact Hvv').
        apply AxiomII in Huu' as [Euu' Huu'].
        apply AxiomII in Hvv' as [Evv' Hvv'].
        destruct Huu' as [f1 [Hf1op Huuf1]].
        destruct Hvv' as [f2 [Hf2op Hvvf2]].
        destruct (OPXY_c f1 x y r s Hf1op) as [Hf1func [Hf1pr [Hf1ds Hf1rs]]].
        destruct (OPXY_c f2 x y r s Hf2op) as [Hf2func [Hf2pr [Hf2ds Hf2rs]]].
        destruct (MKT97 (f:=f1) (g:=f2) (r:=r) (s:=s) (x:=x) (y:=y) Hf1pr Hf2pr Hf1ds Hf2ds Hf1rs Hf2rs) as [Hsub12 | Hsub21].
        * assert (Huuf2 : [u,u'] ∈ f2).
          { apply Hsub12. exact Huuf1. }
          assert (Hvvf2' : [v,v'] ∈ f2).
          { exact Hvvf2. }
          assert (Hudf2 : u ∈ dom(f2)).
          { apply AxiomII; split; [exact Eu | exists u'; exact Huuf2]. }
          assert (Hvdf2 : v ∈ dom(f2)).
          { apply AxiomII; split; [exact Ev | exists v'; exact Hvvf2']. }
          assert (Hord2 : Rrelation f2[u] s f2[v]).
          { apply (proj2 (proj2 (proj2 Hf2pr)) u v Hudf2 Hvdf2 Huv). }
          assert (Hf2u : f2[u] = u') by (apply (MKT_fval f2 u u' Hf2func); exact Huuf2).
          assert (Hf2v : f2[v] = v') by (apply (MKT_fval f2 v v' Hf2func); exact Hvvf2').
          rewrite Hf2u in Hord2. rewrite Hf2v in Hord2.
          rewrite Hgu. rewrite Hgv. exact Hord2.
        * assert (Hvvf1 : [v,v'] ∈ f1).
          { apply Hsub21. exact Hvvf2. }
          assert (Hudf1 : u ∈ dom(f1)).
          { apply AxiomII; split; [exact Eu | exists u'; exact Huuf1]. }
          assert (Hvdf1 : v ∈ dom(f1)).
          { apply AxiomII; split; [exact Ev | exists v'; exact Hvvf1]. }
          assert (Hord1 : Rrelation f1[u] s f1[v]).
          { apply (proj2 (proj2 (proj2 Hf1pr)) u v Hudf1 Hvdf1 Huv). }
          assert (Hf1u : f1[u] = u') by (apply (MKT_fval f1 u u' Hf1func); exact Huuf1).
          assert (Hf1v : f1[v] = v') by (apply (MKT_fval f1 v v' Hf1func); exact Hvvf1).
          rewrite Hf1u in Hord1. rewrite Hf1v in Hord1.
          rewrite Hgu. rewrite Hgv. exact Hord1. }
  assert (Hgorder_PXY : Order_PXY g x y r s).
  { unfold Order_PXY.
    split; [exact Hwox | split; [exact Hwoy | split; [exact Hgorder | split; [exact Hgdom_sect | exact Hgran_sect]]]]. }
  destruct (classic (dom(g) = x)) as [Hdgx | Hdgnx].
  - exists g; split; [exact Hgfunc | split; [exact Hgorder_PXY | left; exact Hdgx]].
  - destruct (classic (ran(g) = y)) as [Hrgy | Hrgny].
    + exists g; split; [exact Hgfunc | split; [exact Hgorder_PXY | right; exact Hrgy]].
    + exfalso.
      destruct (MKT91 (x:=x) (y:=dom(g)) (r:=r) Hgdom_sect Hdgnx) as [v [Hvx Hdg_eq]].
      destruct (MKT91 (x:=y) (y:=ran(g)) (r:=s) Hgran_sect Hrgny) as [w [Hwy Hrg_eq]].
      assert (Ev : Ensemble v) by (unfold Ensemble; eauto).
      assert (Ew : Ensemble w) by (unfold Ensemble; eauto).
      assert (Hvnotdg : v ∉ dom(g)).
      { intro Hvdg.
        rewrite Hdg_eq in Hvdg.
        apply AxiomII in Hvdg as [Ev' [Hvx' Hvv]].
        assert (Hasym : Asymmetric r x) by (apply MKT88a; exact Hwox).
        unfold Asymmetric in Hasym.
        exact (Hasym v v Hvx Hvx' Hvv Hvv). }
      assert (Hwnotrg : w ∉ ran(g)).
      { intro Hwrg.
        rewrite Hrg_eq in Hwrg.
        apply AxiomII in Hwrg as [Ew' [Hwy' Hww]].
        assert (Hasym : Asymmetric s y) by (apply MKT88a; exact Hwoy).
        unfold Asymmetric in Hasym.
        exact (Hasym w w Hwy Hwy' Hww Hww). }
      set (A := \{λ z, z = [v,w]\}).
      assert (HA : ∀ z, z ∈ A <-> z = [v,w]).
      { intro z; split.
        - intros Hz. apply AxiomII in Hz as [Ez Hz]. exact Hz.
        - intros Hz.
          apply AxiomII; split.
          + subst z. exact (MKT49a Ev Ew).
          + exact Hz. }
      set (g1 := g ∪ A).
      assert (Hg1func : Function g1).
      { unfold Function. split.
        - intros z Hz.
          apply AxiomII in Hz as [Ez Hz].
          destruct Hz as [Hzg | HzA].
          + destruct (proj1 Hgfunc z Hzg) as [a [b Hzb]]; exists a; exists b; exact Hzb.
          + apply (proj1 (HA z)) in HzA. exists v; exists w; exact HzA.
        - intros a b c Hab Hac.
          apply AxiomII in Hab as [Eab Hab].
          apply AxiomII in Hac as [Eac Hac].
          destruct Hab as [Habg | HabA].
          + destruct Hac as [Hacg | HacA].
            * apply (proj2 Hgfunc a b c); assumption.
            * apply (proj1 (HA ([a,c]))) in HacA.
              assert (Hac_eq : [a,c] = [v,w]) by exact HacA.
              assert (Eac0 : Ensemble ([a,c])) by (rewrite Hac_eq; exact (MKT49a Ev Ew)).
              destruct (MKT49b a c Eac0) as [Ea Ec].
              assert (Eab0 : Ensemble ([a,b])) by (unfold Ensemble; exists g; exact Habg).
              destruct (MKT49b a b Eab0) as [Ea' Eb].
              assert (Hav : a = v) by (exact (proj1 (proj1 (MKT55 a c v w Ea Ec) Hac_eq))).
              assert (Hadg : a ∈ dom(g)).
              { apply AxiomII; split; [exact Ea' | exists b; exact Habg]. }
              exfalso. apply Hvnotdg. rewrite <- Hav. exact Hadg.
          + destruct Hac as [Hacg | HacA].
            * apply (proj1 (HA ([a,b]))) in HabA.
              assert (Hab_eq : [a,b] = [v,w]) by exact HabA.
              assert (Eab0 : Ensemble ([a,b])) by (rewrite Hab_eq; exact (MKT49a Ev Ew)).
              destruct (MKT49b a b Eab0) as [Ea Eb].
              assert (Eac0 : Ensemble ([a,c])) by (unfold Ensemble; exists g; exact Hacg).
              destruct (MKT49b a c Eac0) as [Ea' Ec].
              assert (Hav : a = v) by (exact (proj1 (proj1 (MKT55 a b v w Ea Eb) Hab_eq))).
              assert (Hadg : a ∈ dom(g)).
              { apply AxiomII; split; [exact Ea' | exists c; exact Hacg]. }
              exfalso. apply Hvnotdg. rewrite <- Hav. exact Hadg.
            * apply (proj1 (HA ([a,b]))) in HabA.
              apply (proj1 (HA ([a,c]))) in HacA.
              assert (Hab_eq : [a,b] = [v,w]) by exact HabA.
              assert (Hac_eq : [a,c] = [v,w]) by exact HacA.
              assert (Eab0 : Ensemble ([a,b])) by (rewrite Hab_eq; exact (MKT49a Ev Ew)).
              destruct (MKT49b a b Eab0) as [Ea Eb].
              assert (Eac0 : Ensemble ([a,c])) by (rewrite Hac_eq; exact (MKT49a Ev Ew)).
              destruct (MKT49b a c Eac0) as [Ea' Ec].
              assert (Habac : [a,b] = [a,c]).
              { rewrite Hab_eq. symmetry. exact Hac_eq. }
              exact (proj2 (proj1 (MKT55 a b a c Ea Eb) Habac)). }
      assert (Hg1val_A : g1[v] = w).
      { apply (MKT_fval g1 v w Hg1func).
        apply AxiomII; split.
        + exact (MKT49a Ev Ew).
        + right. apply (proj2 (HA ([v,w]))). reflexivity. }
      assert (Hg1val_g : ∀ t, t ∈ dom(g) -> g1[t] = g[t]).
      { intros t Ht.
        unfold Value.
        apply AxiomI; intros z; split.
        - intros Hz.
          apply AxiomII in Hz as [Ez Hz].
          apply AxiomII; split; [exact Ez |].
          intros y0 Hy.
          apply AxiomII in Hy as [Ey Hyg].
          apply (Hz y0).
          apply AxiomII; split; [exact Ey |].
          unfold g1. apply AxiomII; split; [unfold Ensemble; eauto | left; exact Hyg].
        - intros Hz.
          apply AxiomII in Hz as [Ez Hz].
          apply AxiomII; split; [exact Ez |].
          intros y0 Hy.
          apply AxiomII in Hy as [Ey Hy].
          assert (Hy' : [t,y0] ∈ g \/ [t,y0] ∈ A).
          { unfold g1 in Hy. apply AxiomII in Hy as [E Hy']. exact Hy'. }
          destruct Hy' as [Hyg | HyA].
          + apply (Hz y0). apply AxiomII; split; [exact Ey | exact Hyg].
          + apply (proj1 (HA ([t,y0]))) in HyA.
            assert (Hty_eq : [t,y0] = [v,w]) by exact HyA.
            assert (Ety0 : Ensemble ([t,y0])) by (rewrite Hty_eq; exact (MKT49a Ev Ew)).
            destruct (MKT49b t y0 Ety0) as [Et Ey'].
            assert (Htv : t = v) by (exact (proj1 (proj1 (MKT55 t y0 v w Et Ey') Hty_eq))).
            exfalso. apply Hvnotdg. rewrite <- Htv. exact Ht. }
      assert (Hdg1_mem : ∀ t, t ∈ dom(g1) -> t ∈ dom(g) \/ t = v).
      { intros t Ht.
        apply AxiomII in Ht as [Et Ht].
        destruct Ht as [p Htp].
        apply AxiomII in Htp as [E [Htpg | HtpA]].
        - left. apply AxiomII; split; [exact Et | exists p; exact Htpg].
        - apply (proj1 (HA ([t,p]))) in HtpA.
          assert (Htp_eq : [t,p] = [v,w]) by exact HtpA.
          assert (Etp0 : Ensemble ([t,p])) by (rewrite Htp_eq; exact (MKT49a Ev Ew)).
          destruct (MKT49b t p Etp0) as [Et' Ep].
          right. exact (proj1 (proj1 (MKT55 t p v w Et' Ep) Htp_eq)). }
      assert (Hrg1_mem : ∀ t, t ∈ ran(g1) -> t ∈ ran(g) \/ t = w).
      { intros t Ht.
        apply AxiomII in Ht as [Et Ht].
        destruct Ht as [p Hpt].
        apply AxiomII in Hpt as [E [Hptg | HptA]].
        - left. apply AxiomII; split; [exact Et | exists p; exact Hptg].
        - apply (proj1 (HA ([p,t]))) in HptA.
          assert (Hpt_eq : [p,t] = [v,w]) by exact HptA.
          assert (Ept0 : Ensemble ([p,t])) by (rewrite Hpt_eq; exact (MKT49a Ev Ew)).
          destruct (MKT49b p t Ept0) as [Ep Et'].
          right. exact (proj2 (proj1 (MKT55 p t v w Ep Et') Hpt_eq)). }
      assert (Hdg1_super : ∀ t, t ∈ dom(g) -> t ∈ dom(g1)).
      { intros t Ht.
        apply AxiomII in Ht as [Et Ht].
        destruct Ht as [q Htq].
        apply AxiomII; split; [exact Et | exists q].
        apply AxiomII; split.
        - assert (Etq : Ensemble ([t,q])) by (unfold Ensemble; exists g; exact Htq).
          exact Etq.
        - left. exact Htq. }
      assert (Hrg1_super : ∀ t, t ∈ ran(g) -> t ∈ ran(g1)).
      { intros t Ht.
        apply AxiomII in Ht as [Et Ht].
        destruct Ht as [q Hqt].
        apply AxiomII; split; [exact Et | exists q].
        apply AxiomII; split.
        - assert (Eqt : Ensemble ([q,t])) by (unfold Ensemble; exists g; exact Hqt).
          exact Eqt.
        - left. exact Hqt. }
      assert (Hg1ord : ∀ u u', u ∈ dom(g1) -> u' ∈ dom(g1)
        -> Rrelation u r u' -> Rrelation g1[u] s g1[u']).
      { intros u u' Hudg1 Hu'dg1 Huu'.
        destruct (Hdg1_mem u Hudg1) as [Hudg | Huv].
        - destruct (Hdg1_mem u' Hu'dg1) as [Hu'dg | Hu'v].
          + assert (Huu'' : Rrelation g[u] s g[u']).
            { apply (proj2 (proj2 (proj2 Hgorder)) u u' Hudg Hu'dg Huu'). }
            rewrite (Hg1val_g u Hudg). rewrite (Hg1val_g u' Hu'dg). exact Huu''.
          + assert (Huw : Rrelation g[u] s w).
            { assert (Hugu : [u, g[u]] ∈ g) by (apply (MKT_dom_val g u Hgfunc Hudg)).
              assert (Eu : Ensemble u).
              { apply AxiomII in Hudg as [Eu _]. exact Eu. }
              assert (Egu : Ensemble (g[u])).
              { assert (Eugu : Ensemble ([u, g[u]])) by (unfold Ensemble; exists g; exact Hugu).
                exact (proj2 (MKT49b u (g[u]) Eugu)). }
              assert (Hgur : g[u] ∈ ran(g)).
              { apply AxiomII; split; [exact Egu | exists u; exact Hugu]. }
              rewrite Hrg_eq in Hgur.
              apply AxiomII in Hgur as [Eg [Hgy Hguw]].
              exact Hguw. }
            rewrite (Hg1val_g u Hudg). rewrite Hu'v. rewrite Hg1val_A. exact Huw.
        - assert (Huv0 : u = v) by exact Huv.
          rewrite Huv0 in Huu'.
          destruct (Hdg1_mem u' Hu'dg1) as [Hu'dg | Hu'v'].
          + assert (Hu'x : u' ∈ x).
            { assert (Hudg' : u' ∈ dom(g)) by exact Hu'dg.
              rewrite Hdg_eq in Hudg'.
              apply AxiomII in Hudg' as [Eu' [Hu'x _]].
              exact Hu'x. }
            assert (Hu'rv : Rrelation u' r v).
            { assert (Hudg' : u' ∈ dom(g)) by exact Hu'dg.
              rewrite Hdg_eq in Hudg'.
              apply AxiomII in Hudg' as [Eu' [_ Hu'rv]].
              exact Hu'rv. }
            assert (Hasym : Asymmetric r x) by (apply MKT88a; exact Hwox).
            unfold Asymmetric in Hasym.
            exfalso.
            apply (Hasym v u' Hvx Hu'x Huu'); exact Hu'rv.
          + assert (Hu'v0 : u' = v) by exact Hu'v'.
            rewrite Hu'v0 in Huu'.
            assert (Hasym : Asymmetric r x) by (apply MKT88a; exact Hwox).
            unfold Asymmetric in Hasym.
            exfalso.
            exact (Hasym v v Hvx Hvx Huu' Huu'). }
      assert (Hg1dom_sect : rSection dom(g1) r x).
      { unfold rSection. split.
        - intros z Hz.
          apply AxiomII in Hz as [Ez Hz].
          destruct Hz as [p Hzp].
          apply AxiomII in Hzp as [E [Hzpg | HzpA]].
          + destruct Hgdom_sect as [Hdgx _].
            assert (Hzdg : z ∈ dom(g)).
            { apply AxiomII; split; [exact Ez | exists p; exact Hzpg]. }
            exact (Hdgx z Hzdg).
          + apply (proj1 (HA ([z,p]))) in HzpA.
            assert (Hzp_eq : [z,p] = [v,w]) by exact HzpA.
            assert (Ezp0 : Ensemble ([z,p])) by (rewrite Hzp_eq; exact (MKT49a Ev Ew)).
            destruct (MKT49b z p Ezp0) as [Ez' Ep].
            assert (Hzv : z = v) by (exact (proj1 (proj1 (MKT55 z p v w Ez' Ep) Hzp_eq))).
            rewrite Hzv. exact Hvx.
        - split.
          + exact Hwox.
          + intros u v' Hu Hv' Huv'.
            apply AxiomII in Hv' as [Ev' Hv'].
            destruct Hv' as [p Hv'p].
            apply AxiomII in Hv'p as [E [Hv'pg | Hv'pA]].
            * assert (Hv'dg : v' ∈ dom(g)).
              { apply AxiomII; split; [exact Ev' | exists p; exact Hv'pg]. }
              destruct Hgdom_sect as [_ [_ Hdgclose]].
              assert (Hudg : u ∈ dom(g)) by (apply (Hdgclose u v' Hu Hv'dg Huv')).
              exact (Hdg1_super u Hudg).
            * apply (proj1 (HA ([v',p]))) in Hv'pA.
              assert (Hv'p_eq : [v',p] = [v,w]) by exact Hv'pA.
              assert (Ev'p0 : Ensemble ([v',p])) by (rewrite Hv'p_eq; exact (MKT49a Ev Ew)).
              destruct (MKT49b v' p Ev'p0) as [Ev'' Ep].
              assert (Hv'v : v' = v) by (exact (proj1 (proj1 (MKT55 v' p v w Ev'' Ep) Hv'p_eq))).
              rewrite Hv'v in Huv'.
              assert (Eu0 : Ensemble u).
              { assert (Euv : Ensemble ([u,v])).
                { unfold Ensemble; exists r; exact Huv'. }
                exact (proj1 (MKT49b u v Euv)). }
              assert (Hudg : u ∈ dom(g)).
              { rewrite Hdg_eq. apply AxiomII; split; [exact Eu0 | split; [exact Hu | exact Huv']]. }
              exact (Hdg1_super u Hudg). }
      assert (Hg1ran_sect : rSection ran(g1) s y).
      { unfold rSection. split.
        - intros z Hz.
          apply AxiomII in Hz as [Ez Hz].
          destruct Hz as [p Hzp].
          apply AxiomII in Hzp as [E [Hzpg | HzpA]].
          + destruct Hgran_sect as [Hrgy _].
            assert (Hzrg : z ∈ ran(g)).
            { apply AxiomII; split; [exact Ez | exists p; exact Hzpg]. }
            exact (Hrgy z Hzrg).
          + apply (proj1 (HA ([p,z]))) in HzpA.
            assert (Hpz_eq : [p,z] = [v,w]) by exact HzpA.
            assert (Epz0 : Ensemble ([p,z])) by (rewrite Hpz_eq; exact (MKT49a Ev Ew)).
            destruct (MKT49b p z Epz0) as [Ep Ez'].
            assert (Hzw : z = w) by (exact (proj2 (proj1 (MKT55 p z v w Ep Ez') Hpz_eq))).
            rewrite Hzw. exact Hwy.
        - split.
          + exact Hwoy.
          + intros u v' Hu Hv' Huv'.
            apply AxiomII in Hv' as [Ev' Hv'].
            destruct Hv' as [p Hpv'].
            apply AxiomII in Hpv' as [E [Hpv'g | Hpv'A]].
            * assert (Hv'rg : v' ∈ ran(g)).
              { apply AxiomII; split; [exact Ev' | exists p; exact Hpv'g]. }
              destruct Hgran_sect as [_ [_ Hrgclose]].
              assert (Hurg : u ∈ ran(g)) by (apply (Hrgclose u v' Hu Hv'rg Huv')).
              exact (Hrg1_super u Hurg).
            * apply (proj1 (HA ([p,v']))) in Hpv'A.
              assert (Hpv'_eq : [p,v'] = [v,w]) by exact Hpv'A.
              assert (Epv'0 : Ensemble ([p,v'])) by (rewrite Hpv'_eq; exact (MKT49a Ev Ew)).
              destruct (MKT49b p v' Epv'0) as [Ep Ev''].
              assert (Hv'w : v' = w) by (exact (proj2 (proj1 (MKT55 p v' v w Ep Ev'') Hpv'_eq))).
              rewrite Hv'w in Huv'.
              assert (Eu0 : Ensemble u).
              { assert (Euw : Ensemble ([u,w])).
                { unfold Ensemble; exists s; exact Huv'. }
                exact (proj1 (MKT49b u w Euw)). }
              assert (Hurg : u ∈ ran(g)).
              { rewrite Hrg_eq. apply AxiomII; split; [exact Eu0 | split; [exact Hu | exact Huv']]. }
              exact (Hrg1_super u Hurg). }
      assert (Hg1order : Order_Pr g1 r s).
      { unfold Order_Pr. split.
        - exact Hg1func.
        - split.
          + apply (MKT_wo_sub r dom(g1) x).
            * destruct Hg1dom_sect as [Hdg1x _]. exact Hdg1x.
            * exact Hwox.
          + split.
            * apply (MKT_wo_sub s ran(g1) y).
              destruct Hg1ran_sect as [Hrg1y _]. exact Hrg1y.
              exact Hwoy.
            * exact Hg1ord. }
      assert (Hg1PXY : Order_PXY g1 x y r s).
      { unfold Order_PXY.
        split; [exact Hwox | split; [exact Hwoy | split; [exact Hg1order | split; [exact Hg1dom_sect | exact Hg1ran_sect]]]]. }
      assert (Hg1sub : g1 ⊂ g).
      { intros z Hz.
        apply AxiomII; split; [unfold Ensemble; eauto |].
        exists g1; split; [exact Hg1PXY | exact Hz]. }
      assert (Hvwg : [v,w] ∈ g).
      { apply (Hg1sub ([v,w])).
        apply AxiomII; split.
        + exact (MKT49a Ev Ew).
        + right. apply (proj2 (HA ([v,w]))). reflexivity. }
      assert (Hvdg2 : v ∈ dom(g)).
      { apply AxiomII; split; [exact Ev | exists w; exact Hvwg]. }
      exact (Hvnotdg Hvdg2).
Qed.

Theorem MKT100 : ∀ {r s x y}, WellOrdered r x -> WellOrdered s y
  -> Ensemble x -> ~ Ensemble y -> ∃ f, Function f
    /\ Order_PXY f x y r s /\ dom( f) = x.
Proof.
  intros r s x y Hwox Hwoy Hx Hy.
  destruct (MKT99 (r:=r) (s:=s) (x:=x) (y:=y) Hwox Hwoy) as [f [Hffunc [Hfop Hmax]]].
  destruct Hmax as [Hdom | Hran].
  - exists f; split; [exact Hffunc | split; [exact Hfop | exact Hdom]].
  - exfalso.
    apply Hy.
    destruct (OPXY_c f x y r s Hfop) as [_ [_ [Hdf _]]].
    destruct Hdf as [Hdfsub _].
    assert (HdomfE : Ensemble dom(f)) by (exact (MKT33 x dom(f) Hx Hdfsub)).
    assert (HranE : Ensemble ran(f)) by (apply (AxiomV Hffunc HdomfE)).
    rewrite Hran in HranE. exact HranE.
Qed.

Theorem MKT100' : ∀ r s x y, WellOrdered r x /\ WellOrdered s y
  -> Ensemble x -> ~ Ensemble y
  -> ∀ f, Function f /\ Order_PXY f x y r s /\ dom(f) = x
  -> ∀ g, Function g /\ Order_PXY g x y r s /\ dom(g) = x
  -> f = g.
Proof.
  intros r s x y Hwo Hx Hny f [Hf [Hfop Hfdom]] g [Hg [Hgop Hgdom]].
  destruct (OPXY_c f x y r s Hfop) as [Hf' [Hfpr [Hfds Hfrs]]].
  destruct (OPXY_c g x y r s Hgop) as [Hg' [Hgpr [Hgds Hgrs]]].
  destruct (MKT97 (f:=f) (g:=g) (r:=r) (s:=s) (x:=x) (y:=y) Hfpr Hgpr Hfds Hgds Hfrs Hgrs) as [Hfg | Hgf].
  - (* f ⊂ g *)
    apply AxiomI; intros z; split; intros Hz.
    + exact (Hfg z Hz).
    + destruct (proj1 Hg z Hz) as [a [b Hzb]].
      assert (Habg : [a,b] ∈ g) by (rewrite <- Hzb; exact Hz).
      assert (Eab : Ensemble ([a,b])) by (unfold Ensemble; exists g; exact Habg).
      destruct (MKT49b a b Eab) as [Ea Eb].
      assert (Hadg : a ∈ dom(g)).
      { apply AxiomII; split; [exact Ea | exists b; exact Habg]. }
      assert (Hadf : a ∈ dom(f)).
      { rewrite Hfdom. rewrite <- Hgdom. exact Hadg. }
      assert (Haf : [a, f[a]] ∈ f) by (apply (MKT_dom_val f a Hf Hadf)).
      assert (Hafg : [a, f[a]] ∈ g) by (exact (Hfg ([a, f[a]]) Haf)).
      assert (Hfg_eq : f[a] = b).
      { apply (proj2 Hg a (f[a]) b); assumption. }
      rewrite Hzb. rewrite <- Hfg_eq. exact Haf.
  - (* g ⊂ f *)
    apply AxiomI; intros z; split; intros Hz.
    + destruct (proj1 Hf z Hz) as [a [b Hzb]].
      assert (Habf : [a,b] ∈ f) by (rewrite <- Hzb; exact Hz).
      assert (Eab : Ensemble ([a,b])) by (unfold Ensemble; exists f; exact Habf).
      destruct (MKT49b a b Eab) as [Ea Eb].
      assert (Hadf : a ∈ dom(f)).
      { apply AxiomII; split; [exact Ea | exists b; exact Habf]. }
      assert (Hadg : a ∈ dom(g)).
      { rewrite Hgdom. rewrite <- Hfdom. exact Hadf. }
      assert (Hag : [a, g[a]] ∈ g) by (apply (MKT_dom_val g a Hg Hadg)).
      assert (Hgfa : [a, g[a]] ∈ f) by (exact (Hgf ([a, g[a]]) Hag)).
      assert (Hgf_eq : g[a] = b).
      { apply (proj2 Hf a (g[a]) b); assumption. }
      rewrite Hzb. rewrite <- Hgf_eq. exact Hag.
    + exact (Hgf z Hz).
Qed.

(* A.8 序数 *)

Theorem MKT101 : ∀ x, x ∉ x.
Proof.
  intros x Hxx.
  assert (Ex : Ensemble x) by (unfold Ensemble; eauto).
  assert (Hxs : x ∈ [x]).
  { apply AxiomII; split.
    - exact Ex.
    - intros _; reflexivity. }
  assert (Hne : [x] ≠ Φ).
  { intro H.
    assert (HxΦ : x ∈ Φ) by (rewrite <- H; exact Hxs).
    exact (MKT16 HxΦ). }
  destruct (AxiomVII ([x]) Hne) as [y [Hy Hdisj]].
  assert (Hyx : y = x) by (apply (proj1 (MKT41 x Ex y)); exact Hy).
  subst y.
  assert (Hin : x ∈ [x] ∩ x).
  { apply AxiomII; split.
    - exact Ex.
    - split; assumption. }
  rewrite Hdisj in Hin.
  exact (MKT16 Hin).
Qed.

Theorem MKT102 : ∀ x y, x ∈ y -> y ∈ x -> False.
Proof.
  intros x y Hxy Hyx.
  assert (Ex : Ensemble x) by (unfold Ensemble; eauto).
  assert (Ey : Ensemble y) by (unfold Ensemble; eauto).
  assert (Hxyin : x ∈ [x|y]).
  { apply AxiomII; split.
    - exact Ex.
    - left. apply AxiomII; split; [exact Ex | intros _; reflexivity]. }
  assert (Hyxin : y ∈ [x|y]).
  { apply AxiomII; split.
    - exact Ey.
    - right. apply AxiomII; split; [exact Ey | intros _; reflexivity]. }
  assert (Hne : [x|y] ≠ Φ).
  { intro H.
    assert (HxΦ : x ∈ Φ) by (rewrite <- H; exact Hxyin).
    exact (MKT16 HxΦ). }
  destruct (AxiomVII ([x|y]) Hne) as [w [Hw Hdisj]].
  destruct (proj1 (MKT46b Ex Ey w) Hw) as [Hwx | Hwy].
  - subst w.
    assert (Hin : y ∈ [x|y] ∩ x).
    { apply AxiomII; split.
      - exact Ey.
      - split; assumption. }
    rewrite Hdisj in Hin.
    exact (MKT16 Hin).
  - subst w.
    assert (Hin : x ∈ [x|y] ∩ y).
    { apply AxiomII; split.
      - exact Ex.
      - split; assumption. }
    rewrite Hdisj in Hin.
    exact (MKT16 Hin).
Qed.

Theorem MKT104 : ~ Ensemble E.
Proof.
  intro HE.
  assert (HUE : Ensemble (∪E)) by (apply AxiomVI; exact HE).
  assert (HUUE : Ensemble (∪(∪E))) by (apply AxiomVI; exact HUE).
  assert (Hsub : μ ⊂ ∪(∪E)).
  { intros x Hx.
    apply MKT19a in Hx.
    assert (Hxxs : x ∈ [x]).
    { apply AxiomII; split; [exact Hx | intros _; reflexivity]. }
    assert (HxsE : Ensemble ([x])) by (apply MKT42; exact Hx).
    assert (HxxsE : Ensemble ([x,[x]])).
    { apply MKT49a; assumption. }
    assert (Hxss : [x] ∈ [x,[x]]).
    { unfold Ordered.
      unfold Unordered.
      apply MKT4.
      left.
      apply (proj2 (MKT41 (Singleton x) HxsE (Singleton x))); reflexivity. }
    assert (HpairE : [x,[x]] ∈ E).
    { apply AxiomII; split.
      - exact HxxsE.
      - exists x; exists [x]; split; [reflexivity | exact Hxxs]. }
    apply AxiomII; split.
    - exact Hx.
    - exists [x]; split; [exact Hxxs |].
      apply AxiomII; split.
      + exact HxsE.
      + exists ([x,[x]]); split; [exact Hxss | exact HpairE]. }
  assert (Hmu : Ensemble μ) by (exact (MKT33 (∪(∪E)) μ HUUE Hsub)).
  exact (MKT39 Hmu).
Qed.

Theorem MKT107 : ∀ {x}, Ordinal x -> WellOrdered E x.
Proof.
  intros x [Hconn Hfull].
  unfold WellOrdered.
  split.
  - exact Hconn.
  - intros y Hyx Hyn.
    destruct (AxiomVII y Hyn) as [z [Hzy Hdisj]].
    exists z.
    unfold FirstMember.
    split.
    + exact Hzy.
    + intros w Hwy Hwz.
      assert (HwzE : w ∈ z).
      { unfold Rrelation in Hwz.
        apply AxiomII in Hwz as [Ewz Hwz].
        destruct Hwz as [u [v [Huv Huvrel]]].
        assert (Euv : Ensemble ([u,v])).
        { rewrite <- Huv. exact Ewz. }
        destruct (MKT49b u v Euv) as [Eu Ev].
        destruct (proj1 (MKT55 u v w z Eu Ev) (eq_sym Huv)) as [Huw Hvz].
        rewrite <- Huw. rewrite <- Hvz. exact Huvrel. }
      assert (Ew : Ensemble w) by (unfold Ensemble; eauto).
      assert (Hin : w ∈ y ∩ z).
      { apply AxiomII; split.
        - exact Ew.
        - split; assumption. }
      rewrite Hdisj in Hin.
      exact (MKT16 Hin).
Qed.

Theorem MKT108 : ∀ x y, Ordinal x -> y ⊂ x -> y <> x -> Full y
  -> y ∈ x.
Proof.
  intros x y [Hconn Hfull] Hyx Hneq Hfilly.
  destruct (MKT_neq_sub x y Hyx Hneq) as [t [Htx Htny]].
  assert (Et : Ensemble t) by (unfold Ensemble; eauto).
  assert (Htxy : t ∈ x ~ y).
  { apply AxiomII; split; [exact Et | split; [exact Htx |
      apply AxiomII; split; [exact Et | exact Htny]]]. }
  assert (Hxy_n : x ~ y ≠ Φ).
  { intro H. rewrite H in Htxy. apply AxiomII in Htxy as [E H']. apply H'; reflexivity. }
  assert (Hwo : WellOrdered E x).
  { apply MKT107; split; [exact Hconn | exact Hfull]. }
  destruct Hwo as [Hconn' Hwosub].
  assert (Hxy_sub : x ~ y ⊂ x).
  { intros w Hw. apply AxiomII in Hw as [E [Hwx _]]. exact Hwx. }
  destruct (Hwosub (x~y) Hxy_sub Hxy_n) as [d [Hdxy Hdfirst]].
  apply AxiomII in Hdxy as [Ed [Hdx Hdny0]].
  apply AxiomII in Hdny0 as [Ed2 Hdny].
  assert (Hrel_bwd : ∀ a b, Rrelation a E b -> a ∈ b).
  { intros a b Hab.
    unfold Rrelation in Hab.
    apply AxiomII in Hab as [Eab Hab].
    destruct Hab as [u [v [Huv Huvrel]]].
    assert (Euv : Ensemble ([u,v])).
    { rewrite <- Huv. exact Eab. }
    destruct (MKT49b u v Euv) as [Eu Ev].
    destruct (proj1 (MKT55 u v a b Eu Ev) (eq_sym Huv)) as [Hua Hvb].
    rewrite <- Hua. rewrite <- Hvb. exact Huvrel. }
  assert (Hrel_fwd : ∀ a b, Ensemble a -> Ensemble b -> a ∈ b -> Rrelation a E b).
  { intros a b Ea Eb Hab.
    unfold Rrelation.
    apply AxiomII; split.
    - apply MKT49a; assumption.
    - exists a; exists b; split; [reflexivity | exact Hab]. }
  assert (Hdsub : d ⊂ y).
  { intros w Hwd.
    apply NNPP; intro Hwny.
    assert (Hwx : w ∈ x) by (exact (Hfull d Hdx w Hwd)).
    assert (Ew : Ensemble w) by (unfold Ensemble; eauto).
    assert (Hwxy : w ∈ x ~ y).
    { apply AxiomII; split.
      - exact Ew.
      - split.
        + exact Hwx.
        + apply AxiomII; split; [exact Ew | exact Hwny]. }
    assert (Ed' : Ensemble d) by (unfold Ensemble; eauto).
    exact (Hdfirst w Hwxy (Hrel_fwd w d Ew Ed' Hwd)). }
  assert (Hysub : y ⊂ d).
  { intros w Hwy.
    apply NNPP; intro Hwnd.
    assert (Hwx : w ∈ x) by (exact (Hyx w Hwy)).
    assert (Ed' : Ensemble d) by (unfold Ensemble; eauto).
    assert (Ew : Ensemble w) by (unfold Ensemble; eauto).
    destruct (Hconn' w d Hwx Hdx) as [Hwdrel | [Hdwrel | Hwdeq]].
    - exfalso. exact (Hwnd (Hrel_bwd w d Hwdrel)).
    - exfalso.
      assert (Hdy : d ∈ y) by (exact (Hfilly w Hwy d (Hrel_bwd d w Hdwrel))).
      exact (Hdny Hdy).
    - exfalso. rewrite Hwdeq in Hwy. exact (Hdny Hwy). }
  assert (Hyd : y = d) by (apply (proj1 (MKT27 y d)); split; assumption).
  subst y.
  exact Hdx.
Qed.

Theorem MKT109 : ∀ {x y}, Ordinal x -> Ordinal y
  -> x ⊂ y \/ y ⊂ x.
Proof.
  intros x y Hox Hoy.
  pose proof Hox as Hox0.
  pose proof Hoy as Hoy0.
  destruct Hox as [Hconnx Hfullx].
  destruct Hoy as [Hconny Hfully].
  assert (Hconnz : Connect E (x ∩ y)).
  { unfold Connect.
    intros u v Hu Hv.
    apply AxiomII in Hu as [Eu [Hux Huy]].
    apply AxiomII in Hv as [Ev [Hvx Hvy]].
    exact (Hconnx u v Hux Hvx). }
  assert (Hfullz : Full (x ∩ y)).
  { unfold Full.
    intros m Hm.
    apply AxiomII in Hm as [Em [Hmx Hmy]].
    intros n Hnm.
    apply AxiomII; split.
    - assert (En : Ensemble n) by (unfold Ensemble; eauto). exact En.
    - split.
      + exact (Hfullx m Hmx n Hnm).
      + exact (Hfully m Hmy n Hnm). }
  assert (Hoz : Ordinal (x ∩ y)) by (split; assumption).
  assert (Hzx : x ∩ y ⊂ x).
  { intros w Hw. apply AxiomII in Hw as [E [Hwx _]]. exact Hwx. }
  assert (Hzy : x ∩ y ⊂ y).
  { intros w Hw. apply AxiomII in Hw as [E [_ Hwy]]. exact Hwy. }
  destruct (classic (x ∩ y = x)) as [Hzx_eq | Hzx_ne].
  - destruct (classic (x ∩ y = y)) as [Hzy_eq | Hzy_ne].
    + left.
      intros z Hz.
      rewrite <- Hzx_eq in Hz.
      apply AxiomII in Hz as [E [Hzx' Hzy']].
      exact Hzy'.
    + left.
      assert (Hzin : x ∩ y ∈ y) by (apply MKT108; assumption).
      rewrite Hzx_eq in Hzin.
      exact (Hfully x Hzin).
  - destruct (classic (x ∩ y = y)) as [Hzy_eq | Hzy_ne].
    + right.
      assert (Hzin : x ∩ y ∈ x) by (apply MKT108; assumption).
      rewrite Hzy_eq in Hzin.
      exact (Hfullx y Hzin).
    + assert (Hzx_in : x ∩ y ∈ x) by (apply MKT108; assumption).
      assert (Hzy_in : x ∩ y ∈ y) by (apply MKT108; assumption).
      assert (Hzz : x ∩ y ∈ x ∩ y).
      { apply AxiomII; split.
        - assert (E : Ensemble (x∩y)) by (unfold Ensemble; eauto). exact E.
        - split; assumption. }
      exfalso.
      exact (MKT101 (x∩y) Hzz).
Qed.

Theorem MKT110 : ∀ {x y}, Ordinal x -> Ordinal y
  -> x ∈ y \/ y ∈ x \/ x = y.
Proof.
  intros x y Hox Hoy.
  pose proof Hox as Hox0.
  pose proof Hoy as Hoy0.
  destruct Hox as [Hconnx Hfullx].
  destruct Hoy as [Hconny Hfully].
  assert (Hconnz : Connect E (x ∩ y)).
  { unfold Connect.
    intros u v Hu Hv.
    apply AxiomII in Hu as [Eu [Hux Huy]].
    apply AxiomII in Hv as [Ev [Hvx Hvy]].
    exact (Hconnx u v Hux Hvx). }
  assert (Hfullz : Full (x ∩ y)).
  { unfold Full.
    intros m Hm.
    apply AxiomII in Hm as [Em [Hmx Hmy]].
    intros n Hnm.
    apply AxiomII; split.
    - assert (En : Ensemble n) by (unfold Ensemble; eauto). exact En.
    - split.
      + exact (Hfullx m Hmx n Hnm).
      + exact (Hfully m Hmy n Hnm). }
  assert (Hoz : Ordinal (x ∩ y)) by (split; assumption).
  assert (Hzx : x ∩ y ⊂ x).
  { intros w Hw. apply AxiomII in Hw as [E [Hwx _]]. exact Hwx. }
  assert (Hzy : x ∩ y ⊂ y).
  { intros w Hw. apply AxiomII in Hw as [E [_ Hwy]]. exact Hwy. }
  destruct (classic (x ∩ y = x)) as [Hzx_eq | Hzx_ne].
  - destruct (classic (x ∩ y = y)) as [Hzy_eq | Hzy_ne].
    + right; right.
      apply AxiomI; intros z; split; intros Hz.
      * rewrite <- Hzx_eq in Hz.
        apply AxiomII in Hz as [E [Hzx' Hzy']].
        exact Hzy'.
      * rewrite <- Hzy_eq in Hz.
        apply AxiomII in Hz as [E [Hzx' Hzy']].
        exact Hzx'.
    + left.
      apply (MKT108 y x).
      * exact Hoy0.
      * apply (proj1 (MKT30 x y)).
        exact Hzx_eq.
      * intro Hxy.
        apply Hzy_ne.
        subst x.
        exact Hzx_eq.
      * exact Hfullx.
  - destruct (classic (x ∩ y = y)) as [Hzy_eq | Hzy_ne].
    + right; left.
      apply (MKT108 x y).
      * exact Hox0.
      * apply (proj1 (MKT30 y x)).
        rewrite (MKT6' y x).
        exact Hzy_eq.
      * intro Hyx.
        apply Hzx_ne.
        subst y.
        exact Hzy_eq.
      * exact Hfully.
    + assert (Hzx_in : x ∩ y ∈ x).
      { apply MKT108; assumption. }
      assert (Hzy_in : x ∩ y ∈ y).
      { apply MKT108; assumption. }
      assert (Hzz : x ∩ y ∈ x ∩ y).
      { apply AxiomII; split.
        - assert (E : Ensemble (x∩y)) by (unfold Ensemble; eauto). exact E.
        - split; assumption. }
      exfalso.
      exact (MKT101 (x∩y) Hzz).
Qed.

Theorem MKT111 : ∀ x y, Ordinal x -> y ∈ x -> Ordinal y.
Proof.
  intros x y [Hconnx Hfullx] Hyx.
  assert (Hyx_sub : y ⊂ x) by (exact (Hfullx y Hyx)).
  assert (Hrel_bwd : ∀ a b, Rrelation a E b -> a ∈ b).
  { intros a b Hab.
    unfold Rrelation in Hab.
    apply AxiomII in Hab as [Eab Hab].
    destruct Hab as [u [v [Huv Huvrel]]].
    assert (Euv : Ensemble ([u,v])).
    { rewrite <- Huv. exact Eab. }
    destruct (MKT49b u v Euv) as [Eu Ev].
    destruct (proj1 (MKT55 u v a b Eu Ev) (eq_sym Huv)) as [Hua Hvb].
    rewrite <- Hua. rewrite <- Hvb. exact Huvrel. }
  assert (Hrel_fwd : ∀ a b, Ensemble a -> Ensemble b -> a ∈ b -> Rrelation a E b).
  { intros a b Ea Eb Hab.
    unfold Rrelation.
    apply AxiomII; split.
    - apply MKT49a; assumption.
    - exists a; exists b; split; [reflexivity | exact Hab]. }
  split.
  - unfold Connect.
    intros u v Hu Hv.
    exact (Hconnx u v (Hyx_sub u Hu) (Hyx_sub v Hv)).
  - unfold Full.
    intros m Hmy.
    assert (Hmx : m ∈ x) by (exact (Hyx_sub m Hmy)).
    assert (Hm_sub_x : m ⊂ x) by (exact (Hfullx m Hmx)).
    assert (Hwo : WellOrdered E x).
    { apply MKT107; split; [exact Hconnx | exact Hfullx]. }
    destruct Hwo as [Hconn Hwosub].
    intros n Hnm.
    apply NNPP; intro Hnny.
    assert (Hnx : n ∈ x) by (exact (Hm_sub_x n Hnm)).
    assert (En : Ensemble n) by (unfold Ensemble; eauto).
    assert (Em : Ensemble m) by (unfold Ensemble; eauto).
    assert (Ey : Ensemble y) by (unfold Ensemble; eauto).
    assert (HnS : n ∈ x ~ y).
    { apply AxiomII; split.
      - exact En.
      - split; [exact Hnx | apply AxiomII; split; [exact En | exact Hnny]]. }
    assert (HSn : x ~ y ≠ Φ).
    { intro H. rewrite H in HnS. apply AxiomII in HnS as [E H']. apply H'; reflexivity. }
    assert (HSx : x ~ y ⊂ x).
    { intros w Hw. apply AxiomII in Hw as [E [Hwx _]]. exact Hwx. }
    destruct (Hwosub (x ~ y) HSx HSn) as [d [HdS Hdfirst]].
    apply AxiomII in HdS as [Ed [Hdx Hdny1]].
    apply AxiomII in Hdny1 as [Ed2 Hdny].
    assert (Hd_sub_y : d ⊂ y).
    { intros w Hwd.
      apply NNPP; intro Hwny.
      assert (Hwx : w ∈ x) by (exact (Hfullx d Hdx w Hwd)).
      assert (Ew : Ensemble w) by (unfold Ensemble; eauto).
      assert (HwS : w ∈ x ~ y).
      { apply AxiomII; split.
        - exact Ew.
        - split; [exact Hwx | apply AxiomII; split; [exact Ew | exact Hwny]]. }
      exact (Hdfirst w HwS (Hrel_fwd w d Ew Ed Hwd)). }
    destruct (Hconn d y Hdx Hyx) as [Hdy | [Hyd | Hdeqy]].
    + exfalso. exact (Hdny (Hrel_bwd d y Hdy)).
    + exfalso.
      assert (Hyd' : y ∈ d) by (exact (Hrel_bwd y d Hyd)).
      assert (Hyy : y ∈ y) by (exact (Hd_sub_y y Hyd')).
      exact (MKT101 y Hyy).
    + subst d.
      destruct (Hconn y n Hyx Hnx) as [Hyn | [Hnyrel | Hyneq]].
      * assert (Hyn' : y ∈ n) by (exact (Hrel_bwd y n Hyn)).
        set (T := \{ λ z, z = y \/ z = n \/ z = m \}).
        assert (HTx : T ⊂ x).
        { intros z Hz.
          apply AxiomII in Hz as [Ez Hz].
          destruct Hz as [Hzy | [Hzn | Hzm]]; subst; assumption. }
        assert (HTn : T ≠ Φ).
        { intro HT.
          assert (HyyT : y ∈ T).
          { apply AxiomII; split; [exact Ey | left; reflexivity]. }
          rewrite HT in HyyT.
          apply AxiomII in HyyT as [E H']. apply H'; reflexivity. }
        destruct (Hwosub T HTx HTn) as [a [HaT Hafirst]].
        apply AxiomII in HaT as [Ea HaT].
        destruct HaT as [Hay | [Han | Ham]].
        { subst a.
          exfalso.
          assert (HmT : m ∈ T).
          { apply AxiomII; split; [exact Em | right; right; reflexivity]. }
          apply (Hafirst m HmT).
          exact (Hrel_fwd m y Em Ey Hmy). }
        { subst a.
          exfalso.
          assert (HyT : y ∈ T).
          { apply AxiomII; split; [exact Ey | left; reflexivity]. }
          apply (Hafirst y HyT).
          exact (Hrel_fwd y n Ey En Hyn'). }
        { subst a.
          exfalso.
          assert (HnT : n ∈ T).
          { apply AxiomII; split; [exact En | right; left; reflexivity]. }
          apply (Hafirst n HnT).
          exact (Hrel_fwd n m En Em Hnm). }
      * exfalso. exact (Hnny (Hrel_bwd n y Hnyrel)).
      * exfalso.
        assert (Hym' : y ∈ m) by (rewrite Hyneq; exact Hnm).
        exact (MKT102 y m Hym' Hmy).
Qed.

Theorem MKT113a : Ordinal R.
Proof.
  split.
  - unfold Connect.
    intros u v Hu Hv.
    apply AxiomII in Hu as [Eu Hou].
    apply AxiomII in Hv as [Ev Hov].
    destruct (MKT110 Hou Hov) as [Huv | [Hvu | Hueq]].
    + left.
      unfold Rrelation.
      apply AxiomII; split.
      * exact (MKT49a Eu Ev).
      * exists u; exists v; split; [reflexivity | exact Huv].
    + right; left.
      unfold Rrelation.
      apply AxiomII; split.
      * exact (MKT49a Ev Eu).
      * exists v; exists u; split; [reflexivity | exact Hvu].
    + right; right. exact Hueq.
  - unfold Full.
    intros m Hm.
    apply AxiomII in Hm as [Em Hom].
    intros n Hnm.
    apply AxiomII; split.
    + unfold Ensemble; eauto.
    + exact (MKT111 m n Hom Hnm).
Qed.

Theorem MKT113b : ~ Ensemble R.
Proof.
  intro HR.
  assert (HRR : R ∈ R).
  { apply AxiomII; split; [exact HR | exact MKT113a]. }
  exact (MKT101 R HRR).
Qed.

Theorem MKT114 : ∀ x, rSection x E R -> Ordinal x.
Proof.
  intros x [HxR [Hwo Hdown]].
  assert (Hrel_fwd : ∀ a b, Ensemble a -> Ensemble b -> a ∈ b -> Rrelation a E b).
  { intros a b Ea Eb Hab. unfold Rrelation. apply AxiomII; split.
    - apply MKT49a; assumption.
    - exists a; exists b; split; [reflexivity | exact Hab]. }
  split.
  - unfold Connect.
    intros u v Hu Hv.
    assert (HuR : u ∈ R) by (exact (HxR u Hu)).
    assert (HvR : v ∈ R) by (exact (HxR v Hv)).
    apply AxiomII in HuR as [Eu Hou].
    apply AxiomII in HvR as [Ev Hov].
    destruct (MKT110 Hou Hov) as [Huv | [Hvu | Hueq]].
    + left. apply Hrel_fwd; [exact Eu | exact Ev | exact Huv].
    + right; left. apply Hrel_fwd; [exact Ev | exact Eu | exact Hvu].
    + right; right. exact Hueq.
  - unfold Full.
    intros m Hmx.
    assert (HmR : m ∈ R) by (exact (HxR m Hmx)).
    apply AxiomII in HmR as [Em Hom].
    intros n Hnm.
    apply (Hdown n m).
    + apply AxiomII; split.
      * unfold Ensemble; eauto.
      * exact (MKT111 m n Hom Hnm).
    + exact Hmx.
    + apply Hrel_fwd; [unfold Ensemble; eauto | exact Em | exact Hnm].
Qed.

Theorem MKT118 : ∀ x y, Ordinal x -> Ordinal y
  -> (x ⊂ y <-> x ≼ y).
Proof.
  intros x y Hox Hoy.
  split.
  - intros Hxy.
    destruct (MKT110 Hox Hoy) as [Hxy' | [Hyx | Heq]].
    + left. exact Hxy'.
    + exfalso. apply (MKT101 y (Hxy y Hyx)).
    + right. exact Heq.
  - intros [Hxy' | Heq].
    + destruct Hoy as [_ Hfully].
      exact (Hfully x Hxy').
    + rewrite Heq. exact (MKT26a y).
Qed.

Theorem MKT119 : ∀ x, Ordinal x
  -> x = \{ λ y, (y ∈ R /\ Less y x) \}.
Proof.
  intros x Hox.
  apply AxiomI; intros z; split.
  - intros Hzx.
    apply AxiomII; split.
    + unfold Ensemble; eauto.
    + split.
      * apply AxiomII; split.
        -- unfold Ensemble; eauto.
        -- exact (MKT111 x z Hox Hzx).
      * exact Hzx.
  - intros Hz.
    apply AxiomII in Hz as [Ez [HzR Hzx]].
    exact Hzx.
Qed.

Theorem MKT120 : ∀ x, x ⊂ R -> Ordinal (∪x).
Proof.
  intros x HxR.
  assert (Hyord : ∀ y, y ∈ x -> Ordinal y).
  { intros y Hyx. pose proof (proj1 (AxiomII y Ordinal) (HxR y Hyx)) as [Ey Hyord]. exact Hyord. }
  assert (Hrel_fwd : ∀ a b, Ensemble a -> Ensemble b -> a ∈ b -> Rrelation a E b).
  { intros a b Ea Eb Hab. unfold Rrelation. apply AxiomII; split.
    - apply MKT49a; assumption.
    - exists a; exists b; split; [reflexivity | exact Hab]. }
  split.
  - unfold Connect.
    intros u v Hu Hv.
    apply AxiomII in Hu as [Eu Hu].
    apply AxiomII in Hv as [Ev Hv].
    destruct Hu as [y [Huy Hyx]].
    destruct Hv as [y' [Hvy' Hy'x]].
    assert (Hoy : Ordinal y) by (exact (Hyord y Hyx)).
    assert (Hoy' : Ordinal y') by (exact (Hyord y' Hy'x)).
    assert (Hou : Ordinal u) by (exact (MKT111 y u Hoy Huy)).
    assert (Hov : Ordinal v) by (exact (MKT111 y' v Hoy' Hvy')).
    destruct (MKT110 Hou Hov) as [Huv | [Hvu | Hueq]].
    + left. apply Hrel_fwd; [exact Eu | exact Ev | exact Huv].
    + right; left. apply Hrel_fwd; [exact Ev | exact Eu | exact Hvu].
    + right; right. exact Hueq.
  - unfold Full.
    intros m Hm.
    apply AxiomII in Hm as [Em Hm].
    destruct Hm as [y [Hmy Hyx]].
    assert (Hoy : Ordinal y) by (exact (Hyord y Hyx)).
    destruct Hoy as [_ Hfully].
    assert (Hmsub : m ⊂ y) by (exact (Hfully m Hmy)).
    intros n Hnm.
    apply AxiomII; split.
    + unfold Ensemble; eauto.
    + exists y; split; [exact (Hmsub n Hnm) | exact Hyx].
Qed.

Theorem MKT121 : ∀ x, x ⊂ R -> x <> Φ -> (∩x) ∈ x.
Proof.
  intros x HxR Hxne.
  assert (Hyord : ∀ y, y ∈ x -> Ordinal y).
  { intros y Hyx. pose proof (proj1 (AxiomII y Ordinal) (HxR y Hyx)) as [Ey Hyord]. exact Hyord. }
  assert (Hrel_fwd : ∀ a b, Ensemble a -> Ensemble b -> a ∈ b -> Rrelation a E b).
  { intros a b Ea Eb Hab. unfold Rrelation. apply AxiomII; split.
    - apply MKT49a; assumption.
    - exists a; exists b; split; [reflexivity | exact Hab]. }
  assert (HwoR : WellOrdered E R).
  { apply MKT107; exact MKT113a. }
  destruct HwoR as [Hconn Hwosub].
  destruct (Hwosub x HxR Hxne) as [z [Hzx Hzfirst]].
  assert (HzR : z ∈ R) by (exact (HxR z Hzx)).
  apply AxiomII in HzR as [Ez Hzord].
  assert (Hzx_z : ∀ y, y ∈ x -> y ∉ z).
  { intros y Hyx Hyz.
    apply (Hzfirst y Hyx).
    apply Hrel_fwd; [unfold Ensemble; eauto | exact Ez | exact Hyz]. }
  assert (Hix : ∩x = z).
  { apply AxiomI; intros w; split.
    - intros Hw.
      apply AxiomII in Hw as [Ew Hw].
      apply (Hw z Hzx).
    - intros Hwz.
      apply AxiomII; split.
      + unfold Ensemble; eauto.
      + intros y Hyx.
        destruct (MKT109 (Hyord y Hyx) Hzord) as [Hyzsub | Hzy].
        * destruct (proj1 (MKT118 y z (Hyord y Hyx) Hzord) Hyzsub) as [Hyz | Hyeq].
          { exfalso. exact (Hzx_z y Hyx Hyz). }
          { subst y. exact Hwz. }
        * exact (Hzy w Hwz). }
  rewrite Hix. exact Hzx.
Qed.

Theorem MKT123 : ∀ x, x ∈ R
  -> FirstMember (PlusOne x) E (\{ λ y, (y ∈ R /\ Less x y) \}).
Proof.
  intros x HxR.
  apply AxiomII in HxR as [Ex Hox].
  destruct Hox as [Hconnx Hfullx].
  assert (Hrel_fwd : ∀ a b, Ensemble a -> Ensemble b -> a ∈ b -> Rrelation a E b).
  { intros a b Ea Eb Hab. unfold Rrelation. apply AxiomII; split.
    - apply MKT49a; assumption.
    - exists a; exists b; split; [reflexivity | exact Hab]. }
  assert (Hrel_bwd : ∀ a b, Rrelation a E b -> a ∈ b).
  { intros a b Hab. unfold Rrelation in Hab.
    apply AxiomII in Hab as [Eab Hab].
    destruct Hab as [u [v [Huv Huvrel]]].
    assert (Euv : Ensemble ([u,v])).
    { rewrite <- Huv. exact Eab. }
    destruct (MKT49b u v Euv) as [Eu Ev].
    destruct (proj1 (MKT55 u v a b Eu Ev) (eq_sym Huv)) as [Hua Hvb].
    rewrite <- Hua. rewrite <- Hvb. exact Huvrel. }
  assert (HPE : Ensemble (PlusOne x)).
  { unfold PlusOne. apply AxiomIV; [exact Ex | apply MKT42; exact Ex]. }
  assert (HPlusOrd : Ordinal (PlusOne x)).
  { unfold PlusOne.
    split.
    - unfold Connect.
      intros u v Hu Hv.
      apply AxiomII in Hu as [Eu [Hux | Hus]].
      apply AxiomII in Hv as [Ev [Hvx | Hvs]].
      + destruct (Hconnx u v Hux Hvx) as [Huv | [Hvu | Hueq]].
        * left. exact Huv.
        * right; left. exact Hvu.
        * right; right. exact Hueq.
      + apply (proj1 (MKT41 x Ex v)) in Hvs.
        subst v.
        left. apply Hrel_fwd; [exact Eu | exact Ex | exact Hux].
      + apply (proj1 (MKT41 x Ex u)) in Hus.
        subst u.
        apply AxiomII in Hv as [Ev [Hvx | Hvs]].
        * right; left. apply Hrel_fwd; [exact Ev | exact Ex | exact Hvx].
        * apply (proj1 (MKT41 x Ex v)) in Hvs.
          subst v.
          right; right. reflexivity.
    - unfold Full.
      intros m Hm.
      apply AxiomII in Hm as [Em [Hmx | Hms]].
      + assert (Hmsub : m ⊂ x) by (exact (Hfullx m Hmx)).
        intros n Hnm.
        apply AxiomII; split.
        * unfold Ensemble; eauto.
        * left. exact (Hmsub n Hnm).
      + apply (proj1 (MKT41 x Ex m)) in Hms.
        subst m.
        intros n Hnx.
        apply AxiomII; split.
        * unfold Ensemble; eauto.
        * left. exact Hnx.
  }
  unfold FirstMember.
  split.
  - apply AxiomII; split.
    + exact HPE.
    + split.
      * apply AxiomII; split; [exact HPE | exact HPlusOrd].
      * unfold PlusOne.
        apply AxiomII; split.
        -- exact Ex.
        -- right. apply (proj2 (MKT41 x Ex x)); reflexivity.
  - intros y HyS HyE.
    apply AxiomII in HyS as [Ey [HyR Hxy]].
    apply AxiomII in HyR as [Ey' Hoy].
    assert (HyPlus : y ∈ PlusOne x) by (exact (Hrel_bwd y (PlusOne x) HyE)).
    unfold PlusOne in HyPlus.
    apply AxiomII in HyPlus as [Ey'' [Hyx | Hys]].
    + exact (MKT102 x y Hxy Hyx).
    + apply (proj1 (MKT41 x Ex y)) in Hys.
      subst y.
      exact (MKT101 x Hxy).
Qed.

Theorem MKT124 : ∀ x, x ∈ R -> ∪(PlusOne x) = x.
Proof.
  intros x HxR.
  apply AxiomII in HxR as [Ex Hox].
  destruct Hox as [Hconnx Hfullx].
  assert (Hrel : ∀ y, y ∈ x ∪ [x] -> y ∈ x \/ y = x).
  { intros y Hy.
    apply AxiomII in Hy as [Ey [Hyx | Hys]].
    - left. exact Hyx.
    - right. apply (proj1 (MKT41 x Ex y)); exact Hys. }
  unfold PlusOne.
  apply AxiomI; intros z; split.
  - intros Hz.
    apply AxiomII in Hz as [Ez Hz].
    destruct Hz as [y [Hzy Hy]].
    destruct (Hrel y Hy) as [Hyx | Hyxeq].
    + exact (Hfullx y Hyx z Hzy).
    + subst y. exact Hzy.
  - intros Hzx.
    apply AxiomII; split.
    + unfold Ensemble; eauto.
    + exists x; split; [exact Hzx |].
      apply AxiomII; split.
      * exact Ex.
      * right. apply (proj2 (MKT41 x Ex x)); reflexivity.
Qed.

Theorem MKT126a : ∀ f x, Function f -> Function (f|(x)).
Proof.
  intros f x [Hrel Hsing].
  unfold Restriction.
  unfold Function.
  split.
  - intros z Hz.
    apply AxiomII in Hz as [Ez [Hzf _]].
    apply (Hrel z Hzf).
  - intros a b c Hab Hac.
    apply AxiomII in Hab as [Eab [Habf _]].
    apply AxiomII in Hac as [Eac [Hacf _]].
    apply (Hsing a b c); assumption.
Qed.

Theorem MKT126b : ∀ f x, Function f -> dom(f|(x)) = x ∩ dom(f).
Proof.
  intros f x Hf.
  apply AxiomI; intros a; split.
  - intros Ha.
    apply AxiomII in Ha as [Ea Ha].
    destruct Ha as [b Hab].
    unfold Restriction in Hab.
    apply AxiomII in Hab as [Eab [Habf Habx]].
    apply AxiomII in Habx as [Eab' Habx].
    destruct Habx as [u [v [Huv [Hux Hvmu]]]].
    assert (Eab0 : Ensemble ([a,b])) by (unfold Ensemble; eauto).
    destruct (MKT49b a b Eab0) as [Ea' Eb].
    assert (Euv : Ensemble ([u,v])) by (rewrite <- Huv; exact Eab').
    destruct (MKT49b u v Euv) as [Eu Ev].
    destruct (proj1 (MKT55 a b u v Ea' Eb) Huv) as [Hau Hbv].
    apply AxiomII; split.
    + exact Ea'.
    + split.
      * rewrite Hau. exact Hux.
      * apply AxiomII; split; [exact Ea' | exists b; exact Habf].
  - intros Ha.
    apply AxiomII in Ha as [Ea [Hax Had]].
    apply AxiomII in Had as [Ea' Had].
    destruct Had as [b Habf].
    assert (Eab : Ensemble ([a,b])) by (unfold Ensemble; eauto).
    destruct (MKT49b a b Eab) as [Ea'' Eb].
    apply AxiomII; split.
    + exact Ea''.
    + exists b.
      unfold Restriction.
      apply AxiomII; split.
      * exact Eab.
      * split; [exact Habf |].
        apply AxiomII; split.
        -- exact Eab.
        -- exists a; exists b; split; [reflexivity | split; [exact Hax | apply MKT19b; exact Eb]].
Qed.

Theorem MKT126c : ∀ f x, Function f
  -> (∀ y, y ∈ dom(f|(x)) -> (f|(x))[y] = f[y]).
Proof.
  intros f x Hf y Hy.
  assert (Hfres : Function (f|(x))) by (apply MKT126a; exact Hf).
  apply AxiomII in Hy as [Ey Hy].
  destruct Hy as [b Hyb].
  unfold Restriction in Hyb.
  apply AxiomII in Hyb as [Eyb [Hybf Hybx]].
  apply AxiomII in Hybx as [Eyb' Hybx].
  destruct Hybx as [u [v [Huv [Hux Hvmu]]]].
  assert (Eyb0 : Ensemble ([y,b])) by (unfold Ensemble; eauto).
  destruct (MKT49b y b Eyb0) as [Ey' Eb].
  assert (Euv : Ensemble ([u,v])) by (rewrite <- Huv; exact Eyb').
  destruct (MKT49b u v Euv) as [Eu Ev].
  destruct (proj1 (MKT55 y b u v Ey' Eb) Huv) as [Hyu Hbv].
  assert (Hyx : y ∈ x).
  { rewrite <- Hyu in Hux. exact Hux. }
  assert (Hfb : f[y] = b) by (apply (MKT_fval f y b Hf); exact Hybf).
  assert (Eyf : Ensemble ([y, f[y]])).
  { apply MKT49a.
    - exact Ey'.
    - rewrite Hfb. exact Eb. }
  assert (Hy_f : [y, f[y]] ∈ (f|(x))).
  { unfold Restriction.
    apply AxiomII; split.
    - exact Eyf.
    - split.
      + rewrite Hfb. exact Hybf.
      + apply AxiomII; split.
        * exact Eyf.
        * exists y; exists (f[y]); split; [reflexivity | split].
          -- exact Hyx.
          -- apply MKT19b. rewrite Hfb. exact Eb. }
  apply (MKT_fval (f|(x)) y (f[y]) Hfres).
  exact Hy_f.
Qed.

Theorem MKT127 : ∀ {f h g}, Function f -> Ordinal dom(f)
  -> (∀ u, u ∈ dom(f) -> f[u] = g[f|(u)]) -> Function h
  -> Ordinal dom(h) -> (∀ u, u ∈ dom(h) -> h[u] = g[h|(u)])
  -> h ⊂ f \/ f ⊂ h.
Proof.
  intros f h g Hf Hof Hrecf Hh Hoh Hrech.
  assert (Hrel_fwd : ∀ a b, Ensemble a -> Ensemble b -> a ∈ b -> Rrelation a E b).
  { intros a b Ea Eb Hab. unfold Rrelation. apply AxiomII; split.
    - apply MKT49a; assumption.
    - exists a; exists b; split; [reflexivity | exact Hab]. }
  assert (Hagree_gen : ∀ f' h', Function f' -> Function h'
    -> Ordinal dom(f') -> Ordinal dom(h')
    -> (∀ u, u ∈ dom(f') -> f'[u] = g[f'|(u)])
    -> (∀ u, u ∈ dom(h') -> h'[u] = g[h'|(u)])
    -> dom(f') ⊂ dom(h') -> f' ⊂ h').
  { intros f' h' Hf' Hh' Hof' Hoh' Hrecf' Hrech' Hdom_sub.
    destruct Hof' as [Hconn_f' Hfull_f'].
    destruct Hoh' as [Hconn_h' Hfull_h'].
    assert (Hwo_f' : WellOrdered E dom(f')).
    { apply MKT107. split; assumption. }
    destruct Hwo_f' as [Hconn Hwosub].
    assert (Hagr : ∀ u, u ∈ dom(f') -> f'[u] = h'[u]).
    { intros a Ha.
      apply NNPP; intro Hne.
      set (S := \{ λ w, w ∈ dom(f') /\ f'[w] ≠ h'[w] \}).
      assert (HSx : S ⊂ dom(f')).
      { intros w Hw. apply AxiomII in Hw as [E [Hw_ _]]. exact Hw_. }
      assert (HSn : S ≠ Φ).
      { intro HS.
        pose proof Ha as Ha0.
        apply AxiomII in Ha0 as [Ea _].
        assert (Haa : a ∈ S).
        { apply AxiomII; split; [exact Ea | split; [exact Ha | exact Hne]]. }
        rewrite HS in Haa.
        apply AxiomII in Haa as [E Haa].
        exfalso; apply Haa; reflexivity. }
      destruct (Hwosub S HSx HSn) as [a0 [Ha0S Ha0first]].
      apply AxiomII in Ha0S as [Ea0 [Ha0df Hne0]].
      assert (Ha0dh : a0 ∈ dom(h')) by (exact (Hdom_sub a0 Ha0df)).
      assert (Ha0_sub_f : a0 ⊂ dom(f')) by (exact (Hfull_f' a0 Ha0df)).
      assert (Ha0_sub_h : a0 ⊂ dom(h')) by (exact (Hfull_h' a0 Ha0dh)).
      assert (Hagree_a0 : ∀ u, u ∈ a0 -> f'[u] = h'[u]).
      { intros u Hu.
        apply NNPP; intro Hun.
        assert (Eu : Ensemble u).
        { assert (Hu_df : u ∈ dom(f')) by (exact (Ha0_sub_f u Hu)).
          apply AxiomII in Hu_df as [Eu _]. exact Eu. }
        assert (HuS : u ∈ S).
        { apply AxiomII; split; [exact Eu | split; [exact (Ha0_sub_f u Hu) | exact Hun]]. }
        exfalso.
        apply (Ha0first u HuS).
        apply Hrel_fwd; [exact Eu | exact Ea0 | exact Hu]. }
      assert (Hfres_eq : f'|(a0) = h'|(a0)).
      { assert (Hf_res : Function (f'|(a0))) by (apply MKT126a; exact Hf').
        assert (Hh_res : Function (h'|(a0))) by (apply MKT126a; exact Hh').
        apply (proj2 (MKT71 (f'|(a0)) (h'|(a0)) Hf_res Hh_res)).
        intros u.
        destruct (classic (u ∈ a0)) as [Hua0 | Hnua0].
          + assert (Eu : Ensemble u).
            { assert (Hu_df : u ∈ dom(f')) by (exact (Ha0_sub_f u Hua0)).
              apply AxiomII in Hu_df as [Eu _]. exact Eu. }
            assert (Huf_dom : u ∈ dom(f'|(a0))).
            { rewrite (MKT126b f' a0 Hf'). apply AxiomII; split; [exact Eu | split; [exact Hua0 | exact (Ha0_sub_f u Hua0)]]. }
            rewrite (MKT126c f' a0 Hf' u Huf_dom).
            assert (Huh_dom : u ∈ dom(h'|(a0))).
            { rewrite (MKT126b h' a0 Hh'). apply AxiomII; split; [exact Eu | split; [exact Hua0 | exact (Ha0_sub_h u Hua0)]]. }
            rewrite (MKT126c h' a0 Hh' u Huh_dom).
            exact (Hagree_a0 u Hua0).
          + assert (Huf_ndom : u ∉ dom(f'|(a0))).
            { intro Hud. rewrite (MKT126b f' a0 Hf') in Hud. apply AxiomII in Hud as [E [Hua0 _]]. exact (Hnua0 Hua0). }
            assert (Huh_ndom : u ∉ dom(h'|(a0))).
            { intro Hud. rewrite (MKT126b h' a0 Hh') in Hud. apply AxiomII in Hud as [E [Hua0 _]]. exact (Hnua0 Hua0). }
            rewrite (MKT69a (x:=u) (f:=f'|(a0)) Huf_ndom).
            rewrite (MKT69a (x:=u) (f:=h'|(a0)) Huh_ndom).
            reflexivity. }
      assert (Hfa0 : f'[a0] = g[f'|(a0)]) by (apply Hrecf'; exact Ha0df).
      assert (Hha0 : h'[a0] = g[h'|(a0)]) by (apply Hrech'; exact Ha0dh).
      assert (Hfa0_h : f'[a0] = h'[a0]).
      { rewrite Hfa0. rewrite Hha0. rewrite Hfres_eq. reflexivity. }
      exfalso. exact (Hne0 Hfa0_h). }
    intros z Hz.
    destruct (proj1 Hf' z Hz) as [a [b Hzb]].
    assert (Habf : [a,b] ∈ f') by (rewrite <- Hzb; exact Hz).
    assert (Eab : Ensemble ([a,b])) by (unfold Ensemble; exists f'; exact Habf).
    destruct (MKT49b a b Eab) as [Ea Eb].
    assert (Had : a ∈ dom(f')).
    { apply AxiomII; split; [exact Ea | exists b; exact Habf]. }
    assert (Hfh : f'[a] = h'[a]) by (exact (Hagr a Had)).
    assert (Hah : [a, h'[a]] ∈ h') by (apply (MKT_dom_val h' a Hh' (Hdom_sub a Had))).
    assert (Hfb : f'[a] = b) by (apply (MKT_fval f' a b Hf'); exact Habf).
    rewrite Hzb. rewrite <- Hfb. rewrite Hfh. exact Hah.
  }
  destruct (MKT109 Hof Hoh) as [Hdom_sub | Hdom_sub'].
  - right. exact (Hagree_gen f h Hf Hh Hof Hoh Hrecf Hrech Hdom_sub).
  - left. exact (Hagree_gen h f Hh Hf Hoh Hof Hrech Hrecf Hdom_sub').
Qed.

Theorem MKT128a :  ∀ g, ∃ f, Function f /\ Ordinal dom(f)
  /\ (∀ x, Ordinal_Number x -> f[x] = g[f|(x)]).
Proof.
  intro g.
  set (Good := fun h => Function h /\ Ordinal dom(h)
    /\ (∀ u, u ∈ dom(h) -> h[u] = g[h|(u)])).
  set (F := \{ λ z, ∃ h, Good h /\ z ∈ h \}).

  assert (HsubF : ∀ h, Good h -> h ⊂ F).
  { intros h Hh z Hz.
    apply AxiomII; split.
    - unfold Ensemble; eauto.
    - exists h; split; assumption. }

  assert (Hrel_fwd : ∀ a b, Ensemble a -> Ensemble b -> a ∈ b -> Rrelation a E b).
  { intros a b Ea Eb Hab.
    unfold Rrelation.
    apply AxiomII; split.
    - apply MKT49a; assumption.
    - exists a; exists b; split; [reflexivity | exact Hab]. }

  assert (HPlusOrd : ∀ x, Ensemble x -> Ordinal x -> Ordinal (PlusOne x)).
  { intros x Ex [Hconnx Hfullx].
    unfold PlusOne.
    split.
    - unfold Connect.
      intros u v Hu Hv.
      apply AxiomII in Hu as [Eu [Hux | Hus]].
      apply AxiomII in Hv as [Ev [Hvx | Hvs]].
      + destruct (Hconnx u v Hux Hvx) as [Huv | [Hvu | Hueq]].
        * left. exact Huv.
        * right; left. exact Hvu.
        * right; right. exact Hueq.
      + apply (proj1 (MKT41 x Ex v)) in Hvs. subst v.
        left. apply Hrel_fwd; [exact Eu | exact Ex | exact Hux].
      + apply (proj1 (MKT41 x Ex u)) in Hus. subst u.
        apply AxiomII in Hv as [Ev [Hvx | Hvs]].
        * right; left. apply Hrel_fwd; [exact Ev | exact Ex | exact Hvx].
        * apply (proj1 (MKT41 x Ex v)) in Hvs.
          subst v.
          right; right. reflexivity.
    - unfold Full.
      intros m Hm.
      apply AxiomII in Hm as [Em [Hmx | Hms]].
      + intros n Hnm.
        apply AxiomII; split; [unfold Ensemble; eauto | left; exact (Hfullx m Hmx n Hnm)].
      + apply (proj1 (MKT41 x Ex m)) in Hms. subst m.
        intros n Hnx.
        apply AxiomII; split; [unfold Ensemble; eauto | left; exact Hnx].
  }

  assert (HfuncF : Function F).
  { unfold Function; split.
    - intros z Hz.
      apply AxiomII in Hz as [Ez Hz].
      destruct Hz as [h [Hh Hz]].
      destruct Hh as [Hhf _].
      destruct (proj1 Hhf z Hz) as [a [b Hzb]].
      exists a; exists b; exact Hzb.
    - intros a b c Hab Hac.
      apply AxiomII in Hab as [Eab Hab].
      destruct Hab as [h1 [Hh1 Hab]].
      apply AxiomII in Hac as [Eac Hac].
      destruct Hac as [h2 [Hh2 Hac]].
      destruct Hh1 as [Hh1f [Hh1o Hh1r]].
      destruct Hh2 as [Hh2f [Hh2o Hh2r]].
      destruct (MKT127 (f:=h1) (h:=h2) (g:=g) Hh1f Hh1o Hh1r Hh2f Hh2o Hh2r) as [H21 | H12].
      + apply (proj2 Hh1f a b c); [exact Hab | exact (H21 ([a,c]) Hac)].
      + apply (proj2 Hh2f a b c); [exact (H12 ([a,b]) Hab) | exact Hac].
  }

  assert (HordF : Ordinal dom(F)).
  { unfold Ordinal; split.
    - unfold Connect.
      intros u v Hu Hv.
      apply AxiomII in Hu as [Eu Hu].
      destruct Hu as [w1 Hw1].
      apply AxiomII in Hw1 as [Ew1 Hw1].
      destruct Hw1 as [h1 [Hh1 Hw1h1]].
      apply AxiomII in Hv as [Ev Hv].
      destruct Hv as [w2 Hw2].
      apply AxiomII in Hw2 as [Ew2 Hw2].
      destruct Hw2 as [h2 [Hh2 Hw2h2]].
      destruct Hh1 as [Hh1f [Hh1o Hh1r]].
      destruct Hh2 as [Hh2f [Hh2o Hh2r]].
      destruct (MKT127 (f:=h1) (h:=h2) (g:=g) Hh1f Hh1o Hh1r Hh2f Hh2o Hh2r) as [H21 | H12].
      + destruct Hh1o as [Hconn _].
        apply (Hconn u v).
        * apply AxiomII; split; [exact Eu | exists w1; exact Hw1h1].
        * apply AxiomII; split; [exact Ev | exists w2; exact (H21 ([v,w2]) Hw2h2)].
      + destruct Hh2o as [Hconn _].
        apply (Hconn u v).
        * apply AxiomII; split; [exact Eu | exists w1; exact (H12 ([u,w1]) Hw1h1)].
        * apply AxiomII; split; [exact Ev | exists w2; exact Hw2h2].
    - unfold Full.
      intros m Hm.
      apply AxiomII in Hm as [Em Hm].
      destruct Hm as [w Hw].
      apply AxiomII in Hw as [Ew Hw].
      destruct Hw as [h [Hh Hwh]].
      pose proof Hh as Hhgood.
      destruct Hh as [Hhf [Hho Hhr]].
      destruct Hho as [_ Hfullh].
      assert (Hmdh : m ∈ dom(h)).
      { apply AxiomII; split; [exact Em | exists w; exact Hwh]. }
      intros z Hz.
      assert (Hzdh : z ∈ dom(h)).
      { exact (Hfullh m Hmdh z Hz). }
      apply AxiomII in Hzdh as [Ez Hzdh].
      destruct Hzdh as [v Hzv].
      apply AxiomII; split.
      + unfold Ensemble; eauto.
      + exists v.
        apply AxiomII; split.
        * unfold Ensemble; eauto.
        * exists h; split; [exact Hhgood | exact Hzv].
  }

  assert (Hrec_dom : ∀ x, x ∈ dom(F) -> F[x] = g[F|(x)]).
  { intros x Hx.
    apply AxiomII in Hx as [Ex Hx].
    destruct Hx as [y Hxy].
    apply AxiomII in Hxy as [Exy Hxy].
    destruct Hxy as [h0 [Hh0 Hxy]].
    destruct Hh0 as [Hh0f [Hh0o Hh0r]].
    assert (Hh0g : Good h0) by (unfold Good; tauto).
    assert (Hxdh0 : x ∈ dom(h0)).
    { apply AxiomII; split; [exact Ex | exists y; exact Hxy]. }
    assert (Hxf : [x, h0[x]] ∈ F).
    { apply (HsubF h0 Hh0g).
      apply (MKT_dom_val h0 x Hh0f Hxdh0). }
    assert (Hfx : F[x] = h0[x]).
    { apply (MKT_fval F x (h0[x]) HfuncF). exact Hxf. }
    assert (Hh0x : h0[x] = g[h0|(x)]).
    { apply (Hh0r x Hxdh0). }
    assert (Hres_eq : F|(x) = h0|(x)).
    { apply AxiomI; intros z; split; intro Hz.
      - apply AxiomII in Hz as [Ez HzA].
        destruct HzA as [HzF Hzx].
        apply AxiomII in Hzx as [Ezx HzxB].
        destruct HzxB as [u [v [Huv [Hux Hvmu]]]].
        assert (HuvF : [u,v] ∈ F).
        { rewrite Huv in HzF. exact HzF. }
        assert (Euv : Ensemble ([u,v])) by (unfold Ensemble; eauto).
        destruct (MKT49b u v Euv) as [Eu Ev].
        destruct Hh0o as [_ Hfullh0].
        assert (Hu_dom_h0 : u ∈ dom(h0)).
        { exact (Hfullh0 x Hxdh0 u Hux). }
        assert (Hu_h0 : [u, h0[u]] ∈ h0).
        { apply (MKT_dom_val h0 u Hh0f Hu_dom_h0). }
        assert (Hh0u : h0[u] = v).
        { assert (HuF : [u, h0[u]] ∈ F) by (exact (HsubF h0 Hh0g ([u, h0[u]]) Hu_h0)).
          apply (proj2 HfuncF u (h0[u]) v); assumption. }
        apply AxiomII; split; [exact Ez | split].
        + rewrite Huv. rewrite <- Hh0u. exact Hu_h0.
        + apply AxiomII; split; [exact Ezx | exists u; exists v; split; [exact Huv | split; [exact Hux | exact Hvmu]]].
      - apply AxiomII in Hz as [Ez HzC].
        destruct HzC as [Hz1 Hz2].
        apply AxiomII; split; [exact Ez | split].
        + exact (HsubF h0 Hh0g z Hz1).
        + exact Hz2. }
    rewrite Hfx. rewrite Hh0x. rewrite Hres_eq. reflexivity.
  }

  assert (Hrec : ∀ x, x ∈ R -> F[x] = g[F|(x)]).
  { intros x HxR.
    apply AxiomII in HxR as [Ex Hox].
    destruct (classic (x ∈ dom(F))) as [Hxd | Hxnd].
    - exact (Hrec_dom x Hxd).
    - assert (Hfx : F[x] = μ) by (apply MKT69a; exact Hxnd).
      assert (Hdom_x : dom(F) ⊂ x).
      { destruct (MKT110 Hox HordF) as [Hxd' | [Hdx | Hxeq]].
        - exfalso; exact (Hxnd Hxd').
        - destruct Hox as [_ Hfullx]. exact (Hfullx dom(F) Hdx).
        - subst x. exact (MKT26a dom(F)). }
      assert (EdF : Ensemble dom(F)).
      { destruct (MKT110 Hox HordF) as [Hxd' | [Hdx | Hxeq]].
        - exfalso; exact (Hxnd Hxd').
        - unfold Ensemble; eauto.
        - subst x. exact Ex. }
      assert (Hresx : F|(x) = F).
      { unfold Restriction.
        apply AxiomI; intros z; split; intro Hz.
        - apply AxiomII in Hz as [Ez Hz].
          destruct Hz as [HzF _]. exact HzF.
        - pose proof Hz as HzF.
          apply AxiomII in Hz as [Ez Hz].
          destruct Hz as [h [Hh Hz]].
          destruct (proj1 (proj1 Hh) z Hz) as [u [v Huv]].
          assert (Euv : Ensemble ([u,v])).
          { unfold Ensemble; exists h. rewrite <- Huv. exact Hz. }
          destruct (MKT49b u v Euv) as [Eu Ev].
          assert (Hud : u ∈ dom(F)).
          { apply AxiomII; split.
            - exact Eu.
            - exists v.
              apply AxiomII; split.
              + exact Euv.
              + exists h; split; [exact Hh | rewrite <- Huv; exact Hz]. }
          assert (Hux : u ∈ x) by (exact (Hdom_x u Hud)).
          assert (Hvmu : v ∈ μ) by (apply MKT19b; exact Ev).
          apply AxiomII; split; [exact Ez | split; [exact HzF | apply AxiomII; split; [exact Ez | exists u; exists v; split; [exact Huv | split; [exact Hux | exact Hvmu]]]]]. }
      assert (HFnd : F ∉ dom(g)).
      { intro HFg.
        assert (HgFmu : g[F] ∈ μ) by (apply MKT69b; exact HFg).
        assert (Egp : Ensemble (g[F])) by (exact (MKT19a (g[F]) HgFmu)).
        set (p := [dom(F), g[F]]).
        set (h' := F ∪ [ p ]).
        assert (Hp : Ensemble p).
        { unfold p. apply MKT49a; assumption. }
        assert (Hh'f : Function h').
        { unfold h'. unfold Function; split.
          - intros z Hz.
            apply (proj2 (MKT4 F (Singleton p) z)) in Hz as [HzF | Hzp].
            + destruct (proj1 HfuncF z HzF) as [a [b Hzb]].
              exists a; exists b; exact Hzb.
            + apply (proj1 (MKT41 p Hp z)) in Hzp.
              exists dom(F); exists (g[F]). exact Hzp.
          - intros a b c Hab Hac.
            apply (proj2 (MKT4 F (Singleton p) ([a,b]))) in Hab as [HabF | Habp].
            + apply (proj2 (MKT4 F (Singleton p) ([a,c]))) in Hac as [HacF | Hacp].
              * apply (proj2 HfuncF a b c); assumption.
              * apply (proj1 (MKT41 p Hp ([a,c]))) in Hacp.
                assert (Eac : Ensemble ([a,c])).
                { rewrite Hacp. exact Hp. }
                destruct (MKT49b a c Eac) as [Ea Ec].
                assert (Had : a = dom(F)).
                { destruct (proj1 (MKT55 a c dom(F) (g[F]) Ea Ec) Hacp) as [Ha _]. exact Ha. }
                exfalso.
                apply (MKT101 dom(F)).
                apply AxiomII; split; [exact EdF | exists b; rewrite Had in HabF; exact HabF].
            + apply (proj2 (MKT4 F (Singleton p) ([a,c]))) in Hac as [HacF | Hacp].
              * apply (proj1 (MKT41 p Hp ([a,b]))) in Habp.
                assert (Eab : Ensemble ([a,b])).
                { rewrite Habp. exact Hp. }
                destruct (MKT49b a b Eab) as [Ea Eb].
                assert (Had : a = dom(F)).
                { destruct (proj1 (MKT55 a b dom(F) (g[F]) Ea Eb) Habp) as [Ha _]. exact Ha. }
                exfalso.
                apply (MKT101 dom(F)).
                apply AxiomII; split; [exact EdF | exists c; rewrite Had in HacF; exact HacF].
              * apply (proj1 (MKT41 p Hp ([a,b]))) in Habp.
                apply (proj1 (MKT41 p Hp ([a,c]))) in Hacp.
                assert (Eab : Ensemble ([a,b])).
                { rewrite Habp. exact Hp. }
                destruct (MKT49b a b Eab) as [Ea Eb].
                assert (Eac : Ensemble ([a,c])).
                { rewrite Hacp. exact Hp. }
                destruct (MKT49b a c Eac) as [Ea' Ec].
                assert (Habac : [a,b] = [a,c]).
                { rewrite Habp. symmetry. exact Hacp. }
                exact (proj2 (proj1 (MKT55 a b a c Ea Eb) Habac)). }
        assert (Hdomh' : dom(h') = PlusOne dom(F)).
        { unfold h'. unfold PlusOne.
          apply AxiomI; intros u; split; intro Hu.
          - apply AxiomII in Hu as [Eu Hu].
            destruct Hu as [v Huv].
            apply (proj2 (MKT4 F (Singleton p) ([u,v]))) in Huv as [HuvF | Huvp].
            + apply AxiomII; split; [exact Eu | left; apply AxiomII; split; [exact Eu | exists v; exact HuvF]].
            + apply (proj1 (MKT41 p Hp ([u,v]))) in Huvp.
              apply AxiomII; split; [exact Eu | right; apply (proj2 (MKT41 dom(F) EdF u))].
              assert (Euv : Ensemble ([u,v])).
              { rewrite Huvp. exact Hp. }
              destruct (MKT49b u v Euv) as [Eu' Ev].
              destruct (proj1 (MKT55 u v dom(F) (g[F]) Eu' Ev) Huvp) as [Hud _].
              exact Hud.
          - apply AxiomII in Hu as [Eu Hu].
            destruct Hu as [HudF | Hup].
            + apply AxiomII in HudF as [Eu' HudF].
              destruct HudF as [v HuvF].
              apply AxiomII; split; [exact Eu | exists v].
              apply (proj1 (MKT4 F (Singleton p) ([u,v]))). left. exact HuvF.
            + apply (proj1 (MKT41 dom(F) EdF u)) in Hup.
              apply AxiomII; split; [exact Eu | exists (g[F])].
              apply (proj1 (MKT4 F (Singleton p) ([u, g[F]]))). right.
              rewrite Hup.
              exact (proj2 (MKT41 p Hp p) eq_refl). }
        assert (Hh'r : ∀ u, u ∈ dom(h') -> h'[u] = g[h'|(u)]).
        { intros u Hu.
          rewrite Hdomh' in Hu.
          unfold PlusOne in Hu.
          apply AxiomII in Hu as [Eu Hu].
          destruct Hu as [HudF | Hup].
          - assert (Hu_h' : [u, F[u]] ∈ h').
            { unfold h'. apply (proj1 (MKT4 F (Singleton p) ([u, F[u]]))).
              left. apply (MKT_dom_val F u HfuncF HudF). }
            assert (Hh'u : h'[u] = F[u]).
            { apply (MKT_fval h' u (F[u]) Hh'f). exact Hu_h'. }
            assert (Hresu : h'|(u) = F|(u)).
            { unfold h'. unfold Restriction.
              apply AxiomI; intros z; split; intro Hz.
              - apply AxiomII in Hz as [Ez Hz].
                destruct Hz as [Hz1 Hz2].
                apply (proj2 (MKT4 F (Singleton p) z)) in Hz1 as [HzF | Hzp].
                + apply AxiomII; split; [exact Ez | split; [exact HzF | exact Hz2]].
                + exfalso.
                  apply (proj1 (MKT41 p Hp z)) in Hzp.
                  apply AxiomII in Hz2 as [Ezz Hz2].
                  destruct Hz2 as [a [b [Hzab [Hau Hbmu]]]].
                  assert (Eab : Ensemble ([a,b])).
                  { rewrite <- Hzab. exact Ezz. }
                  destruct (MKT49b a b Eab) as [Ea Eb].
                  assert (Habp : [a,b] = [dom(F), g[F]]).
                  { rewrite Hzab in Hzp. exact Hzp. }
                  assert (Had : a = dom(F)).
                  { destruct (proj1 (MKT55 a b dom(F) (g[F]) Ea Eb) Habp) as [Ha _]. exact Ha. }
                  rewrite Had in Hau.
                  destruct HordF as [_ HfullF].
                  assert (Hdd : dom(F) ∈ dom(F)).
                  { exact (HfullF u HudF dom(F) Hau). }
                  exact (MKT101 dom(F) Hdd).
              - apply AxiomII in Hz as [Ez Hz].
                destruct Hz as [HzF Hz2].
                apply AxiomII; split; [exact Ez | split].
                + apply (proj1 (MKT4 F (Singleton p) z)). left. exact HzF.
                + exact Hz2. }
            rewrite Hh'u.
            rewrite (Hrec_dom u HudF).
            rewrite Hresu. reflexivity.
          - apply (proj1 (MKT41 dom(F) EdF u)) in Hup.
            assert (Hup_h' : [dom(F), g[F]] ∈ h').
            { unfold h'. apply (proj1 (MKT4 F (Singleton p) ([dom(F), g[F]]))). right.
              exact (proj2 (MKT41 p Hp p) eq_refl). }
            assert (Hh'u : h'[dom(F)] = g[F]).
            { apply (MKT_fval h' dom(F) (g[F]) Hh'f). exact Hup_h'. }
            assert (Hres_dF : h'|(dom(F)) = F).
            { unfold h'. unfold Restriction.
              apply AxiomI; intros z; split; intro Hz.
              - apply AxiomII in Hz as [Ez Hz].
                destruct Hz as [Hz1 Hz2].
                apply (proj2 (MKT4 F (Singleton p) z)) in Hz1 as [HzF | Hzp].
                + exact HzF.
                + exfalso.
                  apply (proj1 (MKT41 p Hp z)) in Hzp.
                  apply AxiomII in Hz2 as [Ezz Hz2].
                  destruct Hz2 as [a [b [Hzab [Hau Hbmu]]]].
                  assert (Eab : Ensemble ([a,b])).
                  { rewrite <- Hzab. exact Ezz. }
                  destruct (MKT49b a b Eab) as [Ea Eb].
                  assert (Habp : [a,b] = [dom(F), g[F]]).
                  { rewrite Hzab in Hzp. exact Hzp. }
                  assert (Had : a = dom(F)).
                  { destruct (proj1 (MKT55 a b dom(F) (g[F]) Ea Eb) Habp) as [Ha _]. exact Ha. }
                  rewrite Had in Hau.
                  exact (MKT101 dom(F) Hau).
              - pose proof Hz as HzF.
                apply AxiomII; split; [unfold Ensemble; eauto | split; [apply (proj1 (MKT4 F (Singleton p) z)); left; exact HzF |]].
                apply AxiomII in Hz as [Ez Hz].
                destruct Hz as [h [Hh Hz]].
                destruct (proj1 (proj1 Hh) z Hz) as [a [b Hzab]].
                assert (Eab : Ensemble ([a,b])).
                { unfold Ensemble; exists h. rewrite <- Hzab. exact Hz. }
                destruct (MKT49b a b Eab) as [Ea Eb].
                assert (Had : a ∈ dom(F)).
                { apply AxiomII; split.
                  - exact Ea.
                  - exists b. apply AxiomII; split.
                    + exact Eab.
                    + exists h; split; [exact Hh | rewrite <- Hzab; exact Hz]. }
                assert (Hbmu : b ∈ μ) by (apply MKT19b; exact Eb).
                apply AxiomII; split; [exact Ez |].
                exists a; exists b; split; [exact Hzab | split; [exact Had | exact Hbmu]]. }
            rewrite Hup.
            rewrite Hh'u.
            rewrite Hres_dF.
            reflexivity. }
        assert (Hh'o : Ordinal dom(h')).
        { rewrite Hdomh'. apply HPlusOrd; assumption. }
        assert (Hh' : Good h').
        { unfold Good; tauto. }
        assert (Hh'sub : h' ⊂ F).
        { intros z Hz. apply AxiomII; split; [unfold Ensemble; eauto | exists h'; split; [exact Hh' | exact Hz]]. }
        assert (HpF : p ∈ F).
        { apply (Hh'sub p).
          unfold h'. apply (proj1 (MKT4 F (Singleton p) p)). right.
          exact (proj2 (MKT41 p Hp p) eq_refl). }
        assert (Hdd : dom(F) ∈ dom(F)).
        { apply AxiomII; split; [exact EdF | exists (g[F]); exact HpF]. }
        exact (MKT101 dom(F) Hdd). }
      assert (Hg : g[F] = μ) by (apply MKT69a; exact HFnd).
      assert (Hgx : g[F|(x)] = μ).
      { rewrite Hresx. exact Hg. }
      rewrite Hfx. rewrite Hgx. reflexivity.
  }

  exists F; split; [exact HfuncF | split; [exact HordF |]].
  intros x Hx.
  exact (Hrec x Hx).
Qed.

Theorem MKT128b :  ∀ g, ∀ f, Function f /\ Ordinal dom(f)
    /\ (∀ x, Ordinal_Number x -> f[x] = g[f|(x)])
  -> ∀ h, Function h /\ Ordinal dom(h)
    /\ (∀ x, Ordinal_Number x -> h[x] = g[h|(x)]) -> f = h.
Proof.
  intros g f [Hff [Hof Hfrec]] h [Hhf [Hoh Hhrec]].
  destruct (MKT128a g) as [F [HfF [HoF HFrec]]].
  assert (Hrel_fwd : ∀ a b, Ensemble a -> Ensemble b -> a ∈ b -> Rrelation a E b).
  { intros a b Ea Eb Hab.
    unfold Rrelation.
    apply AxiomII; split.
    - apply MKT49a; assumption.
    - exists a; exists b; split; [reflexivity | exact Hab]. }
  assert (Hdomrec : ∀ p, Function p -> Ordinal dom(p)
    -> (∀ x, Ordinal_Number x -> p[x] = g[p|(x)])
    -> (∀ u, u ∈ dom(p) -> p[u] = g[p|(u)])).
  { intros p Hpf Hop Hprec u Hud.
    apply Hprec.
    assert (Hdom_eq : dom(p) = \{ λ y, (y ∈ R /\ Less y dom(p)) \}).
    { apply MKT119; exact Hop. }
    rewrite Hdom_eq in Hud.
    apply AxiomII in Hud as [Eu [HuR _]].
    exact HuR. }
  assert (Hcomp_eq : ∀ p q, Function p -> Ordinal dom(p)
    -> (∀ x, Ordinal_Number x -> p[x] = g[p|(x)])
    -> Function q -> Ordinal dom(q)
    -> (∀ x, Ordinal_Number x -> q[x] = g[q|(x)])
    -> p ⊂ q -> p = q).
  { intros p q Hpf Hop Hprec Hqf Hoq Hqrec Hpq.
    assert (Hagree : ∀ u, u ∈ dom(p) -> p[u] = q[u]).
    { intros u0 Hud0.
      apply NNPP; intro Hne.
      set (S := \{ λ w, w ∈ dom(p) /\ p[w] ≠ q[w] \}).
      assert (HSx : S ⊂ dom(p)).
      { intros w Hw. apply AxiomII in Hw as [E [Hw_ _]]. exact Hw_. }
      assert (HSn : S ≠ Φ).
      { intro HS.
        pose proof Hud0 as Hud0'.
        apply AxiomII in Hud0' as [Eu _].
        assert (Huu : u0 ∈ S).
        { apply AxiomII; split; [exact Eu | split; [exact Hud0 | exact Hne]]. }
        rewrite HS in Huu.
        apply AxiomII in Huu as [E Huu].
        exfalso; apply Huu; reflexivity. }
      assert (Hwo : WellOrdered E dom(p)).
      { apply MKT107; exact Hop. }
      destruct Hwo as [Hconn Hwosub].
      destruct (Hwosub S HSx HSn) as [a0 [Ha0S Ha0first]].
      apply AxiomII in Ha0S as [Ea0 [Ha0dp Hne0]].
      assert (Hfullp : Full dom(p)) by (destruct Hop as [_ Hfullp']; exact Hfullp').
      assert (Hfulld : Full dom(q)) by (destruct Hoq as [_ Hfulld']; exact Hfulld').
      assert (Ha0dq : a0 ∈ dom(q)).
      { pose proof Ha0dp as Ha0dp0.
        apply AxiomII in Ha0dp0 as [Ea0' Ha0dp'].
        destruct Ha0dp' as [y0 Hpa0y0].
        apply AxiomII; split; [exact Ea0' | exists y0; exact (Hpq ([a0,y0]) Hpa0y0)]. }
      assert (Hagree_below : ∀ w, w ∈ a0 -> p[w] = q[w]).
      { intros w Hwa0.
        apply NNPP; intro Hwne.
        assert (Hwdp : w ∈ dom(p)) by (exact (Hfullp a0 Ha0dp w Hwa0)).
        pose proof Hwdp as Hwdp0.
        apply AxiomII in Hwdp0 as [Ew _].
        assert (HwS : w ∈ S).
        { apply AxiomII; split; [exact Ew | split; [exact Hwdp | exact Hwne]]. }
        apply (Ha0first w HwS).
        apply Hrel_fwd; [exact Ew | exact Ea0 | exact Hwa0]. }
      assert (Hres_eq : p|(a0) = q|(a0)).
      { apply (proj2 (MKT71 (p|(a0)) (q|(a0)) (MKT126a p a0 Hpf) (MKT126a q a0 Hqf))).
        intros x.
        destruct (classic (x ∈ a0)) as [Hxa0 | Hnxa0].
        - assert (Hxdp : x ∈ dom(p)) by (exact (Hfullp a0 Ha0dp x Hxa0)).
          assert (Hxdq : x ∈ dom(q)) by (exact (Hfulld a0 Ha0dq x Hxa0)).
          pose proof Hxdp as Hxdp0.
          apply AxiomII in Hxdp0 as [Ex _].
          assert (Hxpd : x ∈ dom(p|(a0))).
          { rewrite (MKT126b p a0 Hpf). apply AxiomII; split; [exact Ex | split; [exact Hxa0 | exact Hxdp]]. }
          rewrite (MKT126c p a0 Hpf x Hxpd).
          assert (Hxqd : x ∈ dom(q|(a0))).
          { rewrite (MKT126b q a0 Hqf). apply AxiomII; split; [exact Ex | split; [exact Hxa0 | exact Hxdq]]. }
          rewrite (MKT126c q a0 Hqf x Hxqd).
          exact (Hagree_below x Hxa0).
        - assert (Hxpd : x ∉ dom(p|(a0))).
          { intro Hx. rewrite (MKT126b p a0 Hpf) in Hx.
            apply AxiomII in Hx as [E [Hxa0 _]]. exact (Hnxa0 Hxa0). }
          assert (Hxqd : x ∉ dom(q|(a0))).
          { intro Hx. rewrite (MKT126b q a0 Hqf) in Hx.
            apply AxiomII in Hx as [E [Hxa0 _]]. exact (Hnxa0 Hxa0). }
          rewrite (MKT69a (x:=x) (f:=p|(a0)) Hxpd).
          rewrite (MKT69a (x:=x) (f:=q|(a0)) Hxqd).
          reflexivity. }
      assert (Hpa0 : p[a0] = g[p|(a0)]).
      { exact (Hdomrec p Hpf Hop Hprec a0 Ha0dp). }
      assert (Hqa0 : q[a0] = g[q|(a0)]).
      { exact (Hdomrec q Hqf Hoq Hqrec a0 Ha0dq). }
      rewrite Hpa0 in Hne0. rewrite Hqa0 in Hne0. rewrite Hres_eq in Hne0.
      exact (Hne0 eq_refl). }
    assert (Hdom_eq : dom(p) = dom(q)).
    { apply NNPP; intro Hdne.
      assert (Hdpdq : dom(p) ⊂ dom(q)).
      { intros x Hx.
        pose proof Hx as Hx0.
        apply AxiomII in Hx0 as [Ex Hx'].
        destruct Hx' as [y Hxy].
        apply AxiomII; split; [exact Ex | exists y; exact (Hpq ([x,y]) Hxy)]. }
      assert (Hfullp : Full dom(p)) by (destruct Hop as [_ Hfullp']; exact Hfullp').
      assert (Hdp_in : dom(p) ∈ dom(q)).
      { apply MKT108; [exact Hoq | exact Hdpdq | exact Hdne | exact Hfullp]. }
      assert (HdomR : Ordinal_Number (dom(p))).
      { apply AxiomII; split.
        - pose proof Hdp_in as Hdp_in0. apply AxiomII in Hdp_in0 as [E _]. exact E.
        - exact Hop. }
      assert (Hp_mu : p[dom(p)] = μ).
      { apply (MKT69a (x:=dom(p)) (f:=p)). exact (MKT101 (dom(p))). }
      assert (Hq_mu : q[dom(p)] ∈ μ).
      { apply (MKT69b (x:=dom(p)) (f:=q)). exact Hdp_in. }
      assert (Hp_res : p|(dom(p)) = p).
      { apply (proj2 (MKT71 (p|(dom(p))) p (MKT126a p (dom(p)) Hpf) Hpf)).
        intros x.
        destruct (classic (x ∈ dom(p))) as [Hxdp | Hnxdp].
        - pose proof Hxdp as Hxdp0.
          apply AxiomII in Hxdp0 as [Ex _].
          assert (Hxpd : x ∈ dom(p|(dom(p)))).
          { rewrite (MKT126b p (dom(p)) Hpf).
            apply AxiomII; split; [exact Ex | split; [exact Hxdp | exact Hxdp]]. }
          rewrite (MKT126c p (dom(p)) Hpf x Hxpd).
          reflexivity.
        - assert (Hxpd : x ∉ dom(p|(dom(p)))).
          { intro Hx. rewrite (MKT126b p (dom(p)) Hpf) in Hx.
            apply AxiomII in Hx as [E [Hxdp _]]. exact (Hnxdp Hxdp). }
          rewrite (MKT69a (x:=x) (f:=p|(dom(p))) Hxpd).
          rewrite (MKT69a (x:=x) (f:=p) Hnxdp).
          reflexivity. }
      assert (Hp_eq : p = q|(dom(p))).
      { apply (proj2 (MKT71 p (q|(dom(p))) Hpf (MKT126a q (dom(p)) Hqf))).
        intros x.
        destruct (classic (x ∈ dom(p))) as [Hxdp | Hnxdp].
        - pose proof Hxdp as Hxdp0.
          apply AxiomII in Hxdp0 as [Ex _].
          assert (Hxdq : x ∈ dom(q)).
          { pose proof Hxdp as Hxdp1.
            apply AxiomII in Hxdp1 as [Ex' Hxdp'].
            destruct Hxdp' as [y Hxy].
            apply AxiomII; split; [exact Ex' | exists y; exact (Hpq ([x,y]) Hxy)]. }
          assert (Hxqd : x ∈ dom(q|(dom(p)))).
          { rewrite (MKT126b q (dom(p)) Hqf).
            apply AxiomII; split; [exact Ex | split; [exact Hxdp | exact Hxdq]]. }
          rewrite (MKT126c q (dom(p)) Hqf x Hxqd).
          exact (Hagree x Hxdp).
        - assert (Hxqd : x ∉ dom(q|(dom(p)))).
          { intro Hx. rewrite (MKT126b q (dom(p)) Hqf) in Hx.
            apply AxiomII in Hx as [E [Hxdp _]]. exact (Hnxdp Hxdp). }
          rewrite (MKT69a (x:=x) (f:=p) Hnxdp).
          rewrite (MKT69a (x:=x) (f:=q|(dom(p))) Hxqd).
          reflexivity. }
      assert (Hq_rec : q[dom(p)] = g[q|(dom(p))]).
      { apply Hqrec; exact HdomR. }
      assert (Hp_rec : p[dom(p)] = g[p|(dom(p))]).
      { apply Hprec; exact HdomR. }
      assert (Hq_eq_mu : q[dom(p)] = μ).
      { rewrite Hq_rec. rewrite <- Hp_eq. rewrite <- Hp_res. rewrite <- Hp_rec.
        exact Hp_mu. }
      exfalso.
      apply (MKT101 μ).
      rewrite Hq_eq_mu in Hq_mu.
      exact Hq_mu. }
    apply (proj2 (MKT71 p q Hpf Hqf)).
    intros x.
    destruct (classic (x ∈ dom(p))) as [Hxdp | Hnxdp].
    - exact (Hagree x Hxdp).
    - assert (Hxndq : x ∉ dom(q)).
      { intro Hxq. rewrite <- Hdom_eq in Hxq. exact (Hnxdp Hxq). }
      rewrite (MKT69a (x:=x) (f:=p) Hnxdp).
      rewrite (MKT69a (x:=x) (f:=q) Hxndq).
      reflexivity.
  }
  assert (Hp_eq_F : ∀ p, Function p -> Ordinal dom(p)
    -> (∀ x, Ordinal_Number x -> p[x] = g[p|(x)]) -> p = F).
  { intros p Hpf Hop Hprec.
    destruct (MKT127 (f:=p) (h:=F) (g:=g) Hpf Hop (Hdomrec p Hpf Hop Hprec)
              HfF HoF (Hdomrec F HfF HoF HFrec)) as [HFp | HpF].
    - symmetry. apply (Hcomp_eq F p HfF HoF HFrec Hpf Hop Hprec HFp).
    - apply (Hcomp_eq p F Hpf Hop Hprec HfF HoF HFrec HpF). }
  rewrite (Hp_eq_F f Hff Hof Hfrec).
  rewrite (Hp_eq_F h Hhf Hoh Hhrec).
  reflexivity.
Qed.

(* A.9 整数 *)

Theorem MKT132 : ∀ x y, Integer x -> y ∈ x -> Integer y.
Proof.
  intros x y [Hox Hwo] Hyx.
  split.
  - apply (MKT111 x y Hox Hyx).
  - apply (MKT_wo_sub (E⁻¹) y x).
    + destruct Hox as [_ Hfullx]. exact (Hfullx y Hyx).
    + exact Hwo.
Qed.

Theorem MKT133 : ∀ {x y}, y ∈ R -> LastMember x E y
  -> y = PlusOne x.
Proof.
  intros x y HyR Hlast.
  apply AxiomII in HyR as [Ey Hoy].
  destruct Hlast as [Hxy Hlast'].
  assert (Ex : Ensemble x) by (unfold Ensemble; eauto).
  assert (Hinv_in : ∀ a b, Ensemble a -> Ensemble b -> a ∈ b -> Rrelation b (E⁻¹) a).
  { intros a b Ea Eb Hab.
    unfold Rrelation.
    apply (proj2 (MKT_inv_in E b a Eb Ea)).
    apply AxiomII; split.
    - apply MKT49a; [exact Ea | exact Eb].
    - exists a; exists b; split; [reflexivity | exact Hab]. }
  unfold PlusOne.
  apply AxiomI; intros z; split.
  - intros Hz.
    assert (Ez : Ensemble z) by (unfold Ensemble; eauto).
    assert (Hoz : Ordinal z) by (apply (MKT111 y z Hoy Hz)).
    assert (Hox : Ordinal x) by (apply (MKT111 y x Hoy Hxy)).
    destruct (MKT110 Hoz Hox) as [Hzx | [Hxz | Hzeq]].
    + apply AxiomII; split; [exact Ez | left; exact Hzx].
    + exfalso.
      apply (Hlast' z Hz).
      apply (Hinv_in x z Ex Ez Hxz).
    + apply AxiomII; split; [exact Ez | right; apply (proj2 (MKT41 x Ex z)); exact Hzeq].
  - intros Hz.
    apply AxiomII in Hz as [Ez [Hzx | Hzxeq]].
    + destruct Hoy as [_ Hfully].
      exact (Hfully x Hxy z Hzx).
    + apply (proj1 (MKT41 x Ex z)) in Hzxeq.
      subst z. exact Hxy.
Qed.

Theorem MKT134 : ∀ {x}, x ∈ ω -> (PlusOne x) ∈ ω.
Proof.
  intros x Hxw.
  apply AxiomII in Hxw as [Ex Hint].
  destruct Hint as [Hox Hwo_inv].
  assert (Ex' : Ensemble (PlusOne x)).
  { unfold PlusOne. apply AxiomIV; [exact Ex | apply MKT42; exact Ex]. }
  assert (Hrel_fwd : ∀ a b, Ensemble a -> Ensemble b -> a ∈ b -> Rrelation a E b).
  { intros a b Ea Eb Hab.
    unfold Rrelation.
    apply AxiomII; split.
    - apply MKT49a; assumption.
    - exists a; exists b; split; [reflexivity | exact Hab]. }
  assert (Hinv_in : ∀ a b, Ensemble a -> Ensemble b -> a ∈ b -> Rrelation b (E⁻¹) a).
  { intros a b Ea Eb Hab.
    unfold Rrelation.
    apply (proj2 (MKT_inv_in E b a Eb Ea)).
    apply AxiomII; split.
    - apply MKT49a; [exact Ea | exact Eb].
    - exists a; exists b; split; [reflexivity | exact Hab]. }
  assert (Hinv_out : ∀ a b, Ensemble a -> Ensemble b -> Rrelation b (E⁻¹) a -> a ∈ b).
  { intros a b Ea Eb Hba.
    unfold Rrelation in Hba.
    apply (proj1 (MKT_inv_in E b a Eb Ea)) in Hba.
    apply AxiomII in Hba as [Eab Hba].
    destruct Hba as [u [v [Huv Huv']]].
    assert (Euv : Ensemble ([u,v])).
    { rewrite <- Huv. exact Eab. }
    destruct (MKT49b u v Euv) as [Eu Ev].
    assert (Eab' : Ensemble ([a,b])).
    { rewrite Huv. exact Euv. }
    destruct (MKT49b a b Eab') as [Ea' Eb'].
    destruct (proj1 (MKT55 a b u v Ea' Eb') Huv) as [Hau Hbv].
    rewrite <- Hau in Huv'. rewrite <- Hbv in Huv'.
    exact Huv'. }
  apply AxiomII; split; [exact Ex' | split].
  - (* Ordinal (PlusOne x) *)
    unfold PlusOne. unfold Ordinal. split.
    + (* Connect E (x ∪ [x]) *)
      unfold Connect.
      intros u v Hu Hv.
      apply AxiomII in Hu as [Eu [Hux | Hus]].
      apply AxiomII in Hv as [Ev [Hvx | Hvs]].
      * destruct Hox as [Hconn _].
        destruct (Hconn u v Hux Hvx) as [Huv | [Hvu | Hueq]].
        -- left; exact Huv.
        -- right; left; exact Hvu.
        -- right; right; exact Hueq.
      * apply (proj1 (MKT41 x Ex v)) in Hvs. subst v.
        left; apply (Hrel_fwd u x Eu Ex Hux).
      * apply (proj1 (MKT41 x Ex u)) in Hus. subst u.
        apply AxiomII in Hv as [Ev [Hvx | Hvs]].
        -- right; left; apply (Hrel_fwd v x Ev Ex Hvx).
        -- apply (proj1 (MKT41 x Ex v)) in Hvs. subst v.
           right; right; reflexivity.
    + (* Full (x ∪ [x]) *)
      unfold Full.
      intros m Hm.
      apply AxiomII in Hm as [Em [Hmx | Hms]].
      * destruct Hox as [_ Hfullx].
        intros n Hnm.
        apply AxiomII; split.
        -- unfold Ensemble; eauto.
        -- left. exact (Hfullx m Hmx n Hnm).
      * apply (proj1 (MKT41 x Ex m)) in Hms. subst m.
        intros n Hnx.
        apply AxiomII; split.
        -- unfold Ensemble; eauto.
        -- left. exact Hnx.
  - (* WellOrdered (E⁻¹) (x ∪ [x]) *)
    unfold PlusOne.
    destruct Hwo_inv as [Hconn_inv Hwosub_inv].
    unfold WellOrdered. split.
    + (* Connect (E⁻¹) (x ∪ [x]) *)
      unfold Connect.
      intros u v Hu Hv.
      apply AxiomII in Hu as [Eu [Hux | Hus]].
      apply AxiomII in Hv as [Ev [Hvx | Hvs]].
      * destruct (Hconn_inv u v Hux Hvx) as [Huv | [Hvu | Hueq]].
        -- left; exact Huv.
        -- right; left; exact Hvu.
        -- right; right; exact Hueq.
      * apply (proj1 (MKT41 x Ex v)) in Hvs. subst v.
        right; left. exact (Hinv_in u x Eu Ex Hux).
      * apply (proj1 (MKT41 x Ex u)) in Hus. subst u.
        apply AxiomII in Hv as [Ev [Hvx | Hvs]].
        -- left. exact (Hinv_in v x Ev Ex Hvx).
        -- apply (proj1 (MKT41 x Ex v)) in Hvs. subst v.
           right; right; reflexivity.
    + (* well-order property *)
      intros S HSx HSn.
      destruct (classic (∀ z, z ∈ S -> z ∈ x)) as [HS_sub | HS_notsub].
      * assert (HSx0 : S ⊂ x).
        { intros z Hz. exact (HS_sub z Hz). }
        destruct (Hwosub_inv S HSx0 HSn) as [z [HzS Hzfirst]].
        exists z; split; [exact HzS | exact Hzfirst].
      * assert (HxS : x ∈ S).
        { destruct (MKT_sub_not S x HS_notsub) as [t [HtS Htnx]].
          assert (Htxu : t ∈ x ∪ [x]) by (exact (HSx t HtS)).
          apply AxiomII in Htxu as [Et' Htxu].
          destruct Htxu as [Htx | Htxeq]; [ exfalso; exact (Htnx Htx)
            | apply (proj1 (MKT41 x Ex t)) in Htxeq; subst t; exact HtS ]. }
        exists x; split; [exact HxS |].
        intros y HyS Hyx.
        assert (Hyxu : y ∈ x ∪ [x]) by (exact (HSx y HyS)).
        apply AxiomII in Hyxu as [Ey Hyxu].
        destruct Hyxu as [Hyx_mem | Hyx_eq];
        [ apply (MKT102 y x Hyx_mem); apply (Hinv_out x y Ex Ey); exact Hyx
        | apply (proj1 (MKT41 x Ex y)) in Hyx_eq; subst y;
          apply (MKT101 x); apply (Hinv_out x x Ex Ex); exact Hyx ].
Qed.

Theorem MKT135 : Φ ∈ ω /\ (∀ x, x ∈ ω -> Φ ≠ PlusOne x).
Proof.
  split.
  - apply (proj2 (AxiomII Φ (λ x, Integer x))).
    split.
    + destruct AxiomVIII as [y0 Hy0].
      destruct Hy0 as [Ey0 Hy0'].
      (* MARKER_F *)
      assert (HΦ : Φ ∈ y0) by (exact (proj1 Hy0')).
      (* MARKER_G *)
      unfold Ensemble; exists y0; exact HΦ.
    + split.
      * (* Ordinal Φ *)
        split.
        -- unfold Connect. intros u v Hu Hv. exfalso. exact (MKT16 Hu).
        -- unfold Full. intros m Hm. exfalso. exact (MKT16 Hm).
      * (* WellOrdered (E⁻¹) Φ *)
        unfold WellOrdered. split.
        -- unfold Connect. intros u v Hu Hv. exfalso. exact (MKT16 Hu).
        -- intros y Hy Hyn.
           assert (HyΦ : y = Φ).
           { apply AxiomI; intros z; split; intros Hz;
             [ exfalso; exact (MKT16 (Hy z Hz))
             | exfalso; apply AxiomII in Hz as [E Hneq]; apply Hneq; reflexivity ]. }
           exfalso.
           apply Hyn.
           rewrite HyΦ. reflexivity.
  - (* MARKER_H *)
    intros x Hxw H.
    assert (Ex : Ensemble x).
    { unfold ω in Hxw.
      apply AxiomII in Hxw as [Ex _].
      exact Ex. }
    assert (Hx_in : x ∈ x ∪ [x]).
    { apply AxiomII; split; [exact Ex | right; apply AxiomII; split; [exact Ex | intros _; reflexivity]]. }
    assert (Hne : x ∪ [x] ≠ Φ).
    { intro H0. rewrite H0 in Hx_in. exact (MKT16 Hx_in). }
    apply Hne. symmetry. exact H.
Qed.

Theorem MKT135a : Φ ∈ ω.
Proof.
  exact (proj1 MKT135).
Qed.

Theorem MKT135b : ∀ x, x ∈ ω -> Φ ≠ PlusOne x.
Proof.
  exact (proj2 MKT135).
Qed.

Theorem MKT136 : ∀ x y, x ∈ ω -> y ∈ ω -> PlusOne x = PlusOne y
  -> x = y.
Proof.
  intros x y Hxw Hyw H.
  apply AxiomII in Hxw as [Ex Hintx].
  destruct Hintx as [Hox _].
  apply AxiomII in Hyw as [Ey Hinty].
  destruct Hinty as [Hoy _].
  destruct (MKT110 Hox Hoy) as [Hxy | [Hyx | Hxy']].
  - (* x ∈ y *)
    assert (Hy_plus : y ∈ PlusOne y).
    { unfold PlusOne. apply AxiomII; split; [exact Ey | right; apply AxiomII; split; [exact Ey | intros _; reflexivity]]. }
    assert (Hy_plus' : y ∈ PlusOne x).
    { rewrite H. exact Hy_plus. }
    unfold PlusOne in Hy_plus'.
    apply AxiomII in Hy_plus' as [Ey' [Hyx' | Hy_eq]].
    + exfalso. exact (MKT102 x y Hxy Hyx').
    + apply (proj1 (MKT41 x Ex y)) in Hy_eq. symmetry. exact Hy_eq.
  - (* y ∈ x *)
    assert (Hx_plus : x ∈ PlusOne x).
    { unfold PlusOne. apply AxiomII; split; [exact Ex | right; apply AxiomII; split; [exact Ex | intros _; reflexivity]]. }
    assert (Hx_plus' : x ∈ PlusOne y).
    { rewrite <- H. exact Hx_plus. }
    unfold PlusOne in Hx_plus'.
    apply AxiomII in Hx_plus' as [Ex' [Hxy' | Hx_eq]].
    + exfalso. exact (MKT102 y x Hyx Hxy').
    + apply (proj1 (MKT41 y Ey x)) in Hx_eq. exact Hx_eq.
  - exact Hxy'.
Qed.

Theorem MKT137 : ∀ x, x ⊂ ω -> Φ ∈ x
  -> (∀ u, u ∈ x -> (PlusOne u) ∈ x) -> x = ω.
Proof.
  intros x Hxω HΦx Hsuccx.
  assert (Hrel_fwd : ∀ a b, Ensemble a -> Ensemble b -> a ∈ b -> Rrelation a E b).
  { intros a b Ea Eb Hab. unfold Rrelation. apply AxiomII; split.
    - apply MKT49a; assumption.
    - exists a; exists b; split; [reflexivity | exact Hab]. }
  assert (Hinv_in : ∀ a b, Ensemble a -> Ensemble b -> a ∈ b -> Rrelation b (E⁻¹) a).
  { intros a b Ea Eb Hab.
    unfold Rrelation.
    apply (proj2 (MKT_inv_in E b a Eb Ea)).
    apply AxiomII; split.
    - apply MKT49a; [exact Ea | exact Eb].
    - exists a; exists b; split; [reflexivity | exact Hab]. }
  assert (Hsucc : ∀ z m, Integer z -> m ∈ z
    -> (∀ t, t ∈ z -> ~ (m ∈ t)) -> z = PlusOne m).
  { intros z m Hzint Hmz Hnot.
    destruct Hzint as [Hzord Hzwo].
    assert (Hfullz : Full z) by (exact (proj2 Hzord)).
    assert (Em : Ensemble m) by (unfold Ensemble; eauto).
    assert (Hmord : Ordinal m) by (apply (MKT111 z m Hzord Hmz)).
    assert (Hpm_sub : PlusOne m ⊂ z).
    { intros w Hw.
      unfold PlusOne in Hw.
      apply AxiomII in Hw as [Ew Hw].
      destruct Hw as [Hwm | Hwms].
      - exact (Hfullz m Hmz w Hwm).
      - apply (proj1 (MKT41 m Em w)) in Hwms.
        subst w. exact Hmz. }
    assert (Hz_sub : z ⊂ PlusOne m).
    { intros t Htz.
      assert (Et : Ensemble t) by (unfold Ensemble; eauto).
      assert (Htord : Ordinal t) by (apply (MKT111 z t Hzord Htz)).
      destruct (MKT110 Htord Hmord) as [Htm | [Hmt | Hteq]].
      - apply AxiomII; split; [exact Et | left; exact Htm].
      - exfalso. exact (Hnot t Htz Hmt).
      - apply AxiomII; split; [exact Et | right; apply (proj2 (MKT41 m Em t)); exact Hteq]. }
    apply (proj1 (MKT27 z (PlusOne m))).
    split; assumption. }
  assert (HwoR : WellOrdered E R).
  { apply MKT107; exact MKT113a. }
  apply (proj1 (MKT27 x ω)).
  split; [exact Hxω |].
  (* ω ⊂ x *)
  intros z Hzω.
  apply NNPP; intro Hzx.
  set (S := \{ λ t, t ∈ ω /\ t ∉ x \}).
  assert (HS_sub_R : S ⊂ R).
  { intros t Ht.
    apply AxiomII in Ht as [Et [Htω Htnx]].
    apply AxiomII in Htω as [Et' Hint].
    destruct Hint as [Hord _].
    apply AxiomII; split; [exact Et' | exact Hord]. }
  assert (HS_ne : S ≠ Φ).
  { intro HS.
    assert (EHz : Ensemble z) by (unfold Ensemble; eauto).
    assert (HzS : z ∈ S).
    { apply AxiomII; split; [exact EHz | split; [exact Hzω | exact Hzx]]. }
    rewrite HS in HzS.
    apply AxiomII in HzS as [E H']. exfalso; apply H'; reflexivity. }
  destruct HwoR as [HconnR HwosubR].
  destruct (HwosubR S HS_sub_R HS_ne) as [w [HwS Hwfirst]].
  apply AxiomII in HwS as [Ew [Hwω Hwnx]].
  assert (Hw_x : w ⊂ x).
  { intros t Htw.
    apply NNPP; intro Htnx.
    assert (Htω : t ∈ ω).
    { apply AxiomII in Hwω as [Ew' Hintw].
      destruct Hintw as [Hword Hwwo].
      apply (proj2 (AxiomII t (λ x, Integer x))).
      split.
      - unfold Ensemble; eauto.
      - apply (MKT132 w t (conj Hword Hwwo) Htw). }
    assert (Et : Ensemble t) by (unfold Ensemble; eauto).
    assert (HtS : t ∈ S).
    { apply AxiomII; split; [exact Et | split; [exact Htω | exact Htnx]]. }
    exfalso.
    apply (Hwfirst t HtS).
    apply Hrel_fwd; [exact Et | exact Ew | exact Htw]. }
  destruct (classic (w = Φ)) as [HwΦ | HwnΦ].
  - exfalso. apply Hwnx. rewrite HwΦ. exact HΦx.
  - exfalso.
    assert (Hwint : Integer w).
    { apply AxiomII in Hwω as [Ew' Hintw]. exact Hintw. }
    destruct Hwint as [Hword Hwwo].
    destruct Hwwo as [Hconn_w Hwosub_w].
    destruct (Hwosub_w w (MKT26a w) HwnΦ) as [m HmS].
    destruct HmS as [Hmw Hmnot].
    assert (Hmnot' : ∀ t, t ∈ w -> ~ (m ∈ t)).
    { intros t Htw Hmt.
      assert (Em : Ensemble m) by (unfold Ensemble; eauto).
      assert (Et : Ensemble t) by (unfold Ensemble; eauto).
      apply (Hmnot t Htw).
      exact (Hinv_in m t Em Et Hmt). }
    assert (Hm_x : m ∈ x) by (exact (Hw_x m Hmw)).
    assert (Hsuccx_m : PlusOne m ∈ x) by (exact (Hsuccx m Hm_x)).
    assert (Hsucc_m : w = PlusOne m).
    { apply (Hsucc w m (conj Hword (conj Hconn_w Hwosub_w)) Hmw Hmnot'). }
    exfalso. apply Hwnx. rewrite Hsucc_m. exact Hsuccx_m.
Qed.

Theorem MKT138 : ω ∈ R.
Proof.
  assert (Hrel_fwd : ∀ a b, Ensemble a -> Ensemble b -> a ∈ b -> Rrelation a E b).
  { intros a b Ea Eb Hab. unfold Rrelation. apply AxiomII; split.
    - apply MKT49a; assumption.
    - exists a; exists b; split; [reflexivity | exact Hab]. }
  assert (Hinv_in : ∀ a b, Ensemble a -> Ensemble b -> a ∈ b -> Rrelation b (E⁻¹) a).
  { intros a b Ea Eb Hab.
    unfold Rrelation.
    apply (proj2 (MKT_inv_in E b a Eb Ea)).
    apply AxiomII; split.
    - apply MKT49a; [exact Ea | exact Eb].
    - exists a; exists b; split; [reflexivity | exact Hab]. }
  assert (Hinv_out : ∀ a b, Ensemble a -> Ensemble b -> Rrelation b (E⁻¹) a -> a ∈ b).
  { intros a b Ea Eb Hba.
    unfold Rrelation in Hba.
    apply (proj1 (MKT_inv_in E b a Eb Ea)) in Hba.
    apply AxiomII in Hba as [Eab Hba].
    destruct Hba as [u [v [Huv Huvrel]]].
    assert (Euv : Ensemble ([u,v])).
    { rewrite <- Huv. exact Eab. }
    destruct (MKT49b u v Euv) as [Eu Ev].
    assert (Eab' : Ensemble ([a,b])).
    { rewrite Huv. exact Euv. }
    destruct (MKT49b a b Eab') as [Ea' Eb'].
    destruct (proj1 (MKT55 a b u v Ea' Eb') Huv) as [Hau Hbv].
    rewrite <- Hau in Huvrel. rewrite <- Hbv in Huvrel.
    exact Huvrel. }
  assert (Hsucc : ∀ z m, Integer z -> m ∈ z
    -> (∀ t, t ∈ z -> ~ (m ∈ t)) -> z = PlusOne m).
  { intros z m Hzint Hmz Hnot.
    destruct Hzint as [Hzord Hzwo].
    assert (Hfullz : Full z) by (exact (proj2 Hzord)).
    assert (Em : Ensemble m) by (unfold Ensemble; eauto).
    assert (Hmord : Ordinal m) by (apply (MKT111 z m Hzord Hmz)).
    assert (Hpm_sub : PlusOne m ⊂ z).
    { intros w Hw.
      unfold PlusOne in Hw.
      apply AxiomII in Hw as [Ew Hw].
      destruct Hw as [Hwm | Hwms].
      - exact (Hfullz m Hmz w Hwm).
      - apply (proj1 (MKT41 m Em w)) in Hwms.
        subst w. exact Hmz. }
    assert (Hz_sub : z ⊂ PlusOne m).
    { intros t Htz.
      assert (Et : Ensemble t) by (unfold Ensemble; eauto).
      assert (Htord : Ordinal t) by (apply (MKT111 z t Hzord Htz)).
      destruct (MKT110 Htord Hmord) as [Htm | [Hmt | Hteq]].
      - apply AxiomII; split; [exact Et | left; exact Htm].
      - exfalso. exact (Hnot t Htz Hmt).
      - apply AxiomII; split; [exact Et | right; apply (proj2 (MKT41 m Em t)); exact Hteq]. }
    apply (proj1 (MKT27 z (PlusOne m))).
    split; assumption. }
  apply AxiomII; split.
  - (* Ensemble ω *)
    destruct AxiomVIII as [y0 [Ey0 [HΦy0 Hsuccy0]]].
    assert (Hω_y : ω ⊂ y0).
    { intros z Hzω.
      apply NNPP; intro Hzny.
      set (S := \{ λ t, t ∈ ω /\ t ∉ y0 \}).
      assert (HS_sub_R : S ⊂ R).
      { intros t Ht.
        apply AxiomII in Ht as [Et [Htω Htny]].
        apply AxiomII in Htω as [Et' Hint].
        destruct Hint as [Hord _].
        apply AxiomII; split; [exact Et' | exact Hord]. }
      assert (HS_ne : S ≠ Φ).
      { intro HS.
        assert (EHz : Ensemble z) by (unfold Ensemble; eauto).
        assert (HzS : z ∈ S).
        { apply AxiomII; split; [exact EHz | split; [exact Hzω | exact Hzny]]. }
        rewrite HS in HzS.
        apply AxiomII in HzS as [E H']. exfalso; apply H'; reflexivity. }
      assert (HwoR : WellOrdered E R).
      { apply MKT107; exact MKT113a. }
      destruct HwoR as [HconnR HwosubR].
      destruct (HwosubR S HS_sub_R HS_ne) as [w [HwS Hwfirst]].
      apply AxiomII in HwS as [Ew [Hwω Hwny]].
      assert (Hw_y : w ⊂ y0).
      { intros t Htw.
        apply NNPP; intro Htny.
        assert (Htω : t ∈ ω).
        { apply AxiomII in Hwω as [Ew' Hintw].
          destruct Hintw as [Hword Hwwo].
          apply (proj2 (AxiomII t (λ x, Integer x))).
          split.
          - unfold Ensemble; eauto.
          - apply (MKT132 w t (conj Hword Hwwo) Htw). }
        assert (Et : Ensemble t) by (unfold Ensemble; eauto).
        assert (HtS : t ∈ S).
        { apply AxiomII; split; [exact Et | split; [exact Htω | exact Htny]]. }
        exfalso.
        apply (Hwfirst t HtS).
        apply Hrel_fwd; [exact Et | exact Ew | exact Htw]. }
      destruct (classic (w = Φ)) as [HwΦ | HwnΦ].
      + exfalso. apply Hwny. rewrite HwΦ. exact HΦy0.
      + exfalso.
        assert (Hwint : Integer w).
        { apply AxiomII in Hwω as [Ew' Hintw]. exact Hintw. }
        destruct Hwint as [Hword Hwwo].
        destruct Hwwo as [Hconn_w Hwosub_w].
        destruct (Hwosub_w w (MKT26a w) HwnΦ) as [m HmS].
        destruct HmS as [Hmw Hmnot].
        assert (Hmnot' : ∀ t, t ∈ w -> ~ (m ∈ t)).
        { intros t Htw Hmt.
          assert (Em : Ensemble m) by (unfold Ensemble; eauto).
          assert (Et : Ensemble t) by (unfold Ensemble; eauto).
          apply (Hmnot t Htw).
          exact (Hinv_in m t Em Et Hmt). }
        assert (Hm_y : m ∈ y0) by (exact (Hw_y m Hmw)).
        assert (Hsucc_y : PlusOne m ∈ y0) by (exact (Hsuccy0 m Hm_y)).
        assert (Hsucc_m : w = PlusOne m).
        { apply (Hsucc w m (conj Hword (conj Hconn_w Hwosub_w)) Hmw Hmnot'). }
        exfalso. apply Hwny. rewrite Hsucc_m. exact Hsucc_y.
    }
    exact (MKT33 y0 ω Ey0 Hω_y).
  - (* Ordinal ω *)
    split.
    + (* Connect E ω *)
      unfold Connect.
      intros u v Hu Hv.
      apply AxiomII in Hu as [Eu Hintu].
      apply AxiomII in Hv as [Ev Hintv].
      destruct Hintu as [Huord _].
      destruct Hintv as [Hvord _].
      destruct (MKT110 Huord Hvord) as [Huv | [Hvu | Hueq]].
      * left. apply Hrel_fwd; [exact Eu | exact Ev | exact Huv].
      * right; left. apply Hrel_fwd; [exact Ev | exact Eu | exact Hvu].
      * right; right. exact Hueq.
    + (* Full ω *)
      unfold Full.
      intros m Hm.
      apply AxiomII in Hm as [Em Hintm].
      destruct Hintm as [Hmord Hmwo].
      intros z Hzm.
      apply (proj2 (AxiomII z (λ x, Integer x))).
      split.
      * unfold Ensemble; eauto.
      * exact (MKT132 m z (conj Hmord Hmwo) Hzm).
Qed.

(* A.10 选择公理 *)

Theorem MKT140 : ∀ x, Ensemble x
  -> ∃ f, Function1_1 f /\ ran(f) = x /\ Ordinal_Number dom(f).
Proof.
  intros x Hx.
  destruct AxiomIX as [c [Hcfunc Hcdom]].
  destruct Hcfunc as [Hc_rel Hc_choice].
  set (g := \{\ λ h y, ∃ x0, x0 = x ~ ran(h) /\ x0 ≠ Φ
    /\ ((x0 ≠ [Φ] /\ y = c[x0]) \/ (x0 = [Φ] /\ y = Φ)) \}\).
  destruct (MKT128a g) as [F [HF [HO HFrec]]].
  pose proof HO as HO0.

  assert (EΦ : Ensemble Φ).
  { exact (MKT33 x Φ Hx (MKT26 x)). }

  assert (Hx0E : ∀ h, Ensemble (x ~ ran(h))).
  { intro h.
    apply (MKT33 x (x ~ ran(h)) Hx).
    intros z Hz.
    apply AxiomII in Hz as [E [Hzx _]].
    exact Hzx. }

  assert (Hc_in : ∀ x0, Ensemble x0 -> x0 ≠ Φ -> c[x0] ∈ x0).
  { intros x0 Hx0E' Hne.
    apply Hc_choice.
    rewrite Hcdom.
    change (x0 ∈ \{ λ z, z ∈ μ /\ z ∈ ¬ [Φ] \}).
    apply AxiomII; split.
    - exact Hx0E'.
    - split.
      + apply MKT19b; exact Hx0E'.
      + apply AxiomII; split.
        * exact Hx0E'.
        * exact (fun Hsing => Hne (proj1 (MKT41 Φ EΦ x0) Hsing)). }

  assert (Hactive : ∀ α, α ∈ R -> Ensemble (F|(α)) -> x ~ ran(F|(α)) ≠ Φ
    -> F[α] ∈ x ~ ran(F|(α))).
  { intros α HαR HFE Hne.
    set (x0 := x ~ ran(F|(α))).
    assert (Hx0Eα : Ensemble x0).
    { unfold x0. exact (Hx0E (F|(α))). }
    assert (HFrecα : F[α] = g[F|(α)]).
    { apply HFrec. exact HαR. }
    destruct (classic (x0 = [Φ])) as [Hx0eq | Hx0ne].
    - (* x0 = [Φ], so g[F|(α)] = Φ *)
      assert (HZ : \{ λ y, [F|(α), y] ∈ g \} = [Φ]).
      { apply AxiomI; intros y; split; intros Hy.
        - apply AxiomII in Hy as [Ey Hy].
          apply (proj2 (MKT41 Φ EΦ y)).
          unfold g in Hy.
          apply AxiomII in Hy as [Epair Hy].
          destruct Hy as [h [y' [Hpair Hq]]].
          destruct Hq as [x0' [Hx0' [Hne' Hdisj]]].
          destruct (proj1 (MKT55 (F|(α)) y h y' HFE Ey) Hpair) as [Hh Hy'].
          subst y'.
          assert (Hx0'eq : x0' = x0).
          { unfold x0. rewrite <- Hh in Hx0'. exact Hx0'. }
          destruct Hdisj as [H1 | H2].
          + destruct H1 as [Hns Hyc].
            exfalso. apply Hns.
            rewrite Hx0'eq. exact Hx0eq.
          + destruct H2 as [Hphieq Hphiy]. exact Hphiy.
        - apply AxiomII in Hy as [Ey Hy].
          assert (HyΦ : y = Φ) by (apply Hy; apply MKT19b; exact EΦ).
          apply AxiomII; split.
          + rewrite HyΦ. exact EΦ.
          + rewrite HyΦ.
            unfold g.
            apply AxiomII; split.
            * exact (MKT49a HFE EΦ).
            * exists (F|(α)); exists Φ; split; [reflexivity |].
              exists x0; split; [unfold x0; reflexivity | split; [exact Hne |
                right; split; [exact Hx0eq | reflexivity]]].
      }
      assert (Hgval : g[F|(α)] = Φ).
      { unfold Value. rewrite HZ. exact (proj1 (MKT44 EΦ)). }
      rewrite HFrecα. rewrite Hgval.
      change (Φ ∈ x0).
      rewrite Hx0eq.
      apply (proj2 (MKT41 Φ EΦ Φ)). reflexivity.
    - (* x0 ≠ [Φ], so g[F|(α)] = c[x0] *)
      assert (Hcx0 : c[x0] ∈ x0) by (apply Hc_in; assumption).
      assert (Ec : Ensemble (c[x0])) by (unfold Ensemble; eauto).
      assert (HZ : \{ λ y, [F|(α), y] ∈ g \} = [c[x0]]).
      { apply AxiomI; intros y; split; intros Hy.
        - apply AxiomII in Hy as [Ey Hy].
          apply (proj2 (MKT41 (c[x0]) Ec y)).
          unfold g in Hy.
          apply AxiomII in Hy as [Epair Hy].
          destruct Hy as [h [y' [Hpair Hq]]].
          destruct Hq as [x0' [Hx0' [Hne' Hdisj]]].
          destruct (proj1 (MKT55 (F|(α)) y h y' HFE Ey) Hpair) as [Hh Hy'].
          assert (Hx0'eq : x0' = x0).
          { unfold x0. rewrite <- Hh in Hx0'. exact Hx0'. }
          destruct Hdisj as [H1 | H2].
          + destruct H1 as [Hns Hyc].
            rewrite <- Hy' in Hyc.
            rewrite Hx0'eq in Hyc. exact Hyc.
          + destruct H2 as [Hphieq Hphiy].
            exfalso. apply Hx0ne.
            rewrite <- Hx0'eq. exact Hphieq.
        - apply AxiomII in Hy as [Ey Hy].
          assert (HyC : y = c[x0]) by (apply Hy; apply MKT19b; exact Ec).
          apply AxiomII; split.
          + rewrite HyC. exact Ec.
          + rewrite HyC.
            unfold g.
            apply AxiomII; split.
            * exact (MKT49a HFE Ec).
            * exists (F|(α)); exists (c[x0]); split; [reflexivity |].
              exists x0; split; [unfold x0; reflexivity | split; [exact Hne |
                left; split; [exact Hx0ne | reflexivity]]].
      }
      assert (Hgval : g[F|(α)] = c[x0]).
      { unfold Value. rewrite HZ. exact (proj1 (MKT44 Ec)). }
      rewrite HFrecα. rewrite Hgval. exact Hcx0.
  }

  assert (Hrel_fwd : ∀ a b, Ensemble a -> Ensemble b -> a ∈ b -> Rrelation a E b).
  { intros a b Ea Eb Hab.
    unfold Rrelation.
    apply AxiomII; split.
    - apply MKT49a; assumption.
    - exists a; exists b; split; [reflexivity | exact Hab]. }

  set (U := \{ λ α, α ∈ R /\ (~ Ensemble (F|(α)) \/ x ~ ran(F|(α)) = Φ) \}).
  assert (HUsub : U ⊂ R).
  { intros α Hα. apply AxiomII in Hα as [E [HαR _]]. exact HαR. }
  assert (HUne : U ≠ Φ).
  { intro HU0.
    assert (Hall : ∀ α, α ∈ R -> Ensemble (F|(α)) /\ x ~ ran(F|(α)) ≠ Φ).
    { intros α HαR.
      apply NNPP; intro Hnot.
      assert (HαU : α ∈ U).
      { apply AxiomII; split.
        - apply AxiomII in HαR as [Eα _]. exact Eα.
        - split; [exact HαR |].
          destruct (proj1 (proj1 (notandor (Ensemble (F|(α))) (x ~ ran(F|(α)) ≠ Φ))) Hnot) as [HnE | Hneq].
          + left; exact HnE.
          + right. exact (proj1 (NNPP (x ~ ran(F|(α)) = Φ)) Hneq). }
      rewrite HU0 in HαU.
      exact (MKT16 HαU). }
    assert (Hfx : ∀ α, α ∈ R -> F[α] ∈ x).
    { intros α HαR.
      destruct (Hall α HαR) as [HFE Hne].
      pose proof (Hactive α HαR HFE Hne) as Hin.
      apply AxiomII in Hin as [E [Hinx _]]. exact Hinx. }
    assert (HRdom : ∀ α, α ∈ R -> α ∈ dom(F)).
    { intros α HαR.
      apply MKT69b'.
      apply MKT19b.
      unfold Ensemble; eauto. }
    assert (HdomR : ∀ β, β ∈ dom(F) -> β ∈ R).
    { intros β Hβ.
      apply AxiomII; split.
      - apply AxiomII in Hβ as [Eβ _]. exact Eβ.
      - apply (MKT111 (dom(F)) β HO0 Hβ). }
    assert (Hfresh : ∀ β, β ∈ dom(F) -> F[β] ∉ ran(F|(β))).
    { intros β Hβ.
      assert (HβR : β ∈ R) by (apply HdomR; exact Hβ).
      destruct (Hall β HβR) as [HFE Hne].
      pose proof (Hactive β HβR HFE Hne) as Hin.
      apply AxiomII in Hin as [E [Hinx Hnotin]].
      apply AxiomII in Hnotin as [E' Hnotin].
      exact Hnotin. }
    assert (Hinjective : ∀ a b, a ∈ dom(F) -> b ∈ dom(F) -> F[a] = F[b] -> a = b).
    { intros a b Ha Hb Hfab.
      assert (HaR : a ∈ R) by (apply HdomR; exact Ha).
      assert (HbR : b ∈ R) by (apply HdomR; exact Hb).
      apply AxiomII in HaR as [Ea HordA].
      apply AxiomII in HbR as [Eb HordB].
      pose proof (MKT110 HordA HordB) as Htri.
      destruct Htri as [Hab | [Hba | Heq]].
      - (* a ∈ b *)
        exfalso.
        apply (Hfresh b Hb).
        rewrite <- Hfab.
        apply AxiomII; split.
        + apply MKT19a. apply (MKT69b (x:=a) (f:=F)). exact Ha.
        + exists a.
          unfold Restriction.
          apply AxiomII; split.
          * apply MKT49a.
            -- apply AxiomII in Ha as [Ea' _]; exact Ea'.
            -- apply MKT19a. apply (MKT69b (x:=a) (f:=F)). exact Ha.
          * split.
            -- apply MKT_dom_val; [exact HF | exact Ha].
            -- apply AxiomII; split.
               ** apply MKT49a.
                  --- apply AxiomII in Ha as [Ea' _]; exact Ea'.
                  --- apply MKT19a. apply (MKT69b (x:=a) (f:=F)). exact Ha.
               ** exists a; exists (F[a]); split; [reflexivity | split; [exact Hab |
                    apply MKT69b; exact Ha]].
      - (* b ∈ a *)
        exfalso.
        apply (Hfresh a Ha).
        rewrite Hfab.
        apply AxiomII; split.
        + apply MKT19a. apply (MKT69b (x:=b) (f:=F)). exact Hb.
        + exists b.
          unfold Restriction.
          apply AxiomII; split.
          * apply MKT49a.
            -- apply AxiomII in Hb as [Eb' _]; exact Eb'.
            -- apply MKT19a. apply (MKT69b (x:=b) (f:=F)). exact Hb.
          * split.
            -- apply MKT_dom_val; [exact HF | exact Hb].
            -- apply AxiomII; split.
               ** apply MKT49a.
                  --- apply AxiomII in Hb as [Eb' _]; exact Eb'.
                  --- apply MKT19a. apply (MKT69b (x:=b) (f:=F)). exact Hb.
               ** exists b; exists (F[b]); split; [reflexivity | split; [exact Hba |
                    apply MKT69b; exact Hb]].
      - exact Heq. }
    assert (Hinvf : Function (F⁻¹)).
    { unfold Function. split.
      - intros z Hz.
        apply AxiomII in Hz as [Ez Hz].
        destruct Hz as [a [b [Hzab _]]].
        exists a; exists b; exact Hzab.
      - intros a b c0 Hab Hac.
        apply AxiomII in Hab as [Eab Hab].
        apply AxiomII in Hac as [Eac Hac].
        destruct Hab as [u [v [Huv Hvu]]].
        destruct Hac as [u' [v' [Huv' Hv'u]]].
        destruct (MKT49b a b Eab) as [Ea Eb].
        destruct (MKT49b a c0 Eac) as [Ea' Ec0].
        destruct (proj1 (MKT55 a b u v Ea Eb) Huv) as [Hau Hbv].
        destruct (proj1 (MKT55 a c0 u' v' Ea' Ec0) Huv') as [Hau' Hcv'].
        assert (Hba : [b,a] ∈ F).
        { rewrite <- Hau in Hvu. rewrite <- Hbv in Hvu. exact Hvu. }
        assert (Hca : [c0,a] ∈ F).
        { rewrite <- Hau' in Hv'u. rewrite <- Hcv' in Hv'u. exact Hv'u. }
        assert (Hfb : F[b] = a) by (apply (MKT_fval F b a HF); exact Hba).
        assert (Hfc : F[c0] = a) by (apply (MKT_fval F c0 a HF); exact Hca).
        assert (Hbd : b ∈ dom(F)).
        { apply AxiomII; split; [exact Eb | exists a; exact Hba]. }
        assert (Hcd : c0 ∈ dom(F)).
        { apply AxiomII; split; [exact Ec0 | exists a; exact Hca]. }
        assert (Hbc : b = c0).
        { apply (Hinjective b c0 Hbd Hcd). rewrite Hfb. rewrite Hfc. reflexivity. }
        exact Hbc. }
    (* ran(F) ⊆ x *)
    assert (Hran_sub : ran(F) ⊂ x).
    { intros z Hz.
      apply AxiomII in Hz as [Ez Hz].
      destruct Hz as [a Ha].
      assert (Eaz : Ensemble ([a,z])).
      { unfold Ensemble; eauto. }
      destruct (MKT49b a z Eaz) as [Ea Ez'].
      assert (Hfa : F[a] = z) by (apply (MKT_fval F a z HF); exact Ha).
      assert (Had : a ∈ dom(F)).
      { apply AxiomII; split; [exact Ea | exists z; exact Ha]. }
      assert (HaR : a ∈ R) by (apply HdomR; exact Had).
      rewrite <- Hfa.
      exact (Hfx a HaR). }
    assert (HranE : Ensemble ran(F)).
    { apply (MKT33 x ran(F) Hx Hran_sub). }
    assert (Hdom_eq : dom(F) = R).
    { apply AxiomI; intros a; split; intros Ha.
      - exact (HdomR a Ha).
      - exact (HRdom a Ha). }
    assert (HR_E : Ensemble R).
    { assert (HraninvE : Ensemble ran(F⁻¹)).
      { apply (AxiomV (f:=F⁻¹) Hinvf).
        rewrite MKT_dom_inv. exact HranE. }
      rewrite MKT_ran_inv in HraninvE.
      rewrite Hdom_eq in HraninvE.
      exact HraninvE. }
    exact (MKT113b HR_E).
  }

  (* U ≠ Φ, so take the least element α0 of U *)
  assert (HwoR : WellOrdered E R).
  { apply MKT107; exact MKT113a. }
  destruct HwoR as [HconnR HwosubR].
  destruct (HwosubR U HUsub HUne) as [α0 [Hα0U Hα0min]].
  apply AxiomII in Hα0U as [Eα0 [Hα0R Hstop]].
  apply AxiomII in Hα0R as [Eα0' Hordα0].

  assert (HnotU : ∀ β, β ∈ α0 -> β ∉ U).
  { intros β Hβ HβU.
    apply (Hα0min β HβU).
    apply Hrel_fwd.
    - exact (MKT33 α0 β Eα0 (proj2 Hordα0 β Hβ)).
    - exact Eα0.
    - exact Hβ. }

  assert (HβE : ∀ β, β ∈ α0 -> Ensemble β).
  { intros β Hβ. exact (MKT33 α0 β Eα0 (proj2 Hordα0 β Hβ)). }
  assert (HβR : ∀ β, β ∈ α0 -> β ∈ R).
  { intros β Hβ.
    apply AxiomII; split.
    - exact (HβE β Hβ).
    - exact (MKT111 α0 β Hordα0 Hβ). }

  assert (Hactive_below : ∀ β, β ∈ α0 -> Ensemble (F|(β)) /\ x ~ ran(F|(β)) ≠ Φ).
  { intros β Hβ.
    apply NNPP; intro Hnot.
    apply (HnotU β Hβ).
    apply AxiomII; split.
    - exact (HβE β Hβ).
    - split.
      + exact (HβR β Hβ).
      + destruct (proj1 (proj1 (notandor (Ensemble (F|(β))) (x ~ ran(F|(β)) ≠ Φ))) Hnot) as [HnE | Hneq].
        * left; exact HnE.
        * right; exact (proj1 (NNPP (x ~ ran(F|(β)) = Φ)) Hneq). }

  assert (Hβdom : ∀ β, β ∈ α0 -> β ∈ dom(F)).
  { intros β Hβ.
    destruct (Hactive_below β Hβ) as [HFE Hne].
    apply MKT69b'.
    apply MKT19b.
    pose proof (Hactive β (HβR β Hβ) HFE Hne) as Hin.
    apply AxiomII in Hin as [E _]. exact E. }

  assert (Hα0ndom : α0 ∉ dom(F)).
  { intro Hα0dom.
    assert (HFrecα0 : F[α0] = g[F|(α0)]).
    { apply HFrec. apply AxiomII; split; [exact Eα0' | exact Hordα0]. }
    assert (Hgμ : g[F|(α0)] = μ).
    { destruct Hstop as [HnE | Hxeq].
      - (* ¬ Ensemble (F|(α0)) *)
        assert (HZ : \{λ y, [F|(α0), y] ∈ g\} = Φ).
        { apply AxiomI; intros y; split; intros Hy.
          - apply AxiomII in Hy as [Ey Hy].
            unfold g in Hy.
            apply AxiomII in Hy as [Epair Hy].
            exfalso. apply HnE.
            exact (proj1 (MKT49b (F|(α0)) y Epair)).
          - apply AxiomII in Hy as [E Hneq]. exfalso. apply Hneq; reflexivity. }
        unfold Value. rewrite HZ. exact MKT24.
      - (* x ~ ran(F|(α0)) = Φ *)
        assert (HZ : \{λ y, [F|(α0), y] ∈ g\} = Φ).
        { apply AxiomI; intros y; split; intros Hy.
          - apply AxiomII in Hy as [Ey Hy].
            unfold g in Hy.
            apply AxiomII in Hy as [Epair Hy].
            destruct Hy as [h [y' [Hpair Hq]]].
            destruct Hq as [x0' [Hx0' [Hne' Hdisj]]].
            destruct (proj1 (MKT55 (F|(α0)) y h y'
              (proj1 (MKT49b (F|(α0)) y Epair)) Ey) Hpair) as [Hh Hy'].
            exfalso. apply Hne'.
            rewrite Hx0'. rewrite <- Hh. exact Hxeq.
          - apply AxiomII in Hy as [E Hneq]. exfalso. apply Hneq; reflexivity. }
        unfold Value. rewrite HZ. exact MKT24. }
    rewrite <- HFrecα0 in Hgμ.
    apply (MKT69a' (x:=α0) (f:=F)).
    exact Hgμ.
    exact Hα0dom. }

  assert (Hdom_eq0 : dom(F) = α0).
  { pose proof (MKT110 Hordα0 HO0) as Htri.
    destruct Htri as [Hin | Hrest].
    - exfalso. exact (Hα0ndom Hin).
    - destruct Hrest as [Hin2 | Heq].
      + exfalso. apply (MKT101 (dom(F))). exact (Hβdom (dom(F)) Hin2).
      + symmetry. exact Heq. }

  assert (Hfresh0 : ∀ β, β ∈ dom(F) -> F[β] ∉ ran(F|(β))).
  { intros β Hβ.
    assert (Hβα : β ∈ α0) by (rewrite <- Hdom_eq0; exact Hβ).
    destruct (Hactive_below β Hβα) as [HFE Hne].
    pose proof (Hactive β (HβR β Hβα) HFE Hne) as Hin.
    apply AxiomII in Hin as [E [Hinx Hnotin]].
    apply AxiomII in Hnotin as [E' Hnotin]. exact Hnotin. }

  assert (Hinjective0 : ∀ a b, a ∈ dom(F) -> b ∈ dom(F) -> F[a] = F[b] -> a = b).
  { intros a b Ha Hb Hfab.
    assert (Hao : Ordinal a) by (exact (MKT111 (dom(F)) a HO0 Ha)).
    assert (Hbo : Ordinal b) by (exact (MKT111 (dom(F)) b HO0 Hb)).
    pose proof (MKT110 Hao Hbo) as Htri.
    destruct Htri as [Hab | [Hba | Heq]].
    - (* a ∈ b *)
      exfalso.
      apply (Hfresh0 b Hb).
      rewrite <- Hfab.
      apply AxiomII; split.
      + apply MKT19a. apply (MKT69b (x:=a) (f:=F)); exact Ha.
      + exists a.
        unfold Restriction.
        apply AxiomII; split.
        * apply MKT49a.
          -- apply AxiomII in Ha as [Ea _]; exact Ea.
          -- apply MKT19a. apply (MKT69b (x:=a) (f:=F)); exact Ha.
        * split.
          -- apply MKT_dom_val; [exact HF | exact Ha].
          -- apply AxiomII; split.
             ** apply MKT49a.
                --- apply AxiomII in Ha as [Ea _]; exact Ea.
                --- apply MKT19a. apply (MKT69b (x:=a) (f:=F)); exact Ha.
             ** exists a; exists (F[a]); split; [reflexivity | split; [exact Hab |
                  apply MKT69b; exact Ha]].
    - (* b ∈ a *)
      exfalso.
      apply (Hfresh0 a Ha).
      rewrite Hfab.
      apply AxiomII; split.
      + apply MKT19a. apply (MKT69b (x:=b) (f:=F)); exact Hb.
      + exists b.
        unfold Restriction.
        apply AxiomII; split.
        * apply MKT49a.
          -- apply AxiomII in Hb as [Eb _]; exact Eb.
          -- apply MKT19a. apply (MKT69b (x:=b) (f:=F)); exact Hb.
        * split.
          -- apply MKT_dom_val; [exact HF | exact Hb].
          -- apply AxiomII; split.
             ** apply MKT49a.
                --- apply AxiomII in Hb as [Eb _]; exact Eb.
                --- apply MKT19a. apply (MKT69b (x:=b) (f:=F)); exact Hb.
             ** exists b; exists (F[b]); split; [reflexivity | split; [exact Hba |
                  apply MKT69b; exact Hb]].
    - exact Heq. }

  assert (Hinvf0 : Function (F⁻¹)).
  { unfold Function. split.
    - intros z Hz.
      apply AxiomII in Hz as [Ez Hz].
      destruct Hz as [a [b [Hzab _]]].
      exists a; exists b; exact Hzab.
    - intros a b c0 Hab Hac.
      apply AxiomII in Hab as [Eab Hab].
      apply AxiomII in Hac as [Eac Hac].
      destruct Hab as [u [v [Huv Hvu]]].
      destruct Hac as [u' [v' [Huv' Hv'u]]].
      destruct (MKT49b a b Eab) as [Ea Eb].
      destruct (MKT49b a c0 Eac) as [Ea' Ec0].
      destruct (proj1 (MKT55 a b u v Ea Eb) Huv) as [Hau Hbv].
      destruct (proj1 (MKT55 a c0 u' v' Ea' Ec0) Huv') as [Hau' Hcv'].
      assert (Hba : [b,a] ∈ F).
      { rewrite <- Hau in Hvu. rewrite <- Hbv in Hvu. exact Hvu. }
      assert (Hca : [c0,a] ∈ F).
      { rewrite <- Hau' in Hv'u. rewrite <- Hcv' in Hv'u. exact Hv'u. }
      assert (Hfb : F[b] = a) by (apply (MKT_fval F b a HF); exact Hba).
      assert (Hfc : F[c0] = a) by (apply (MKT_fval F c0 a HF); exact Hca).
      assert (Hbd : b ∈ dom(F)).
      { apply AxiomII; split; [exact Eb | exists a; exact Hba]. }
      assert (Hcd : c0 ∈ dom(F)).
      { apply AxiomII; split; [exact Ec0 | exists a; exact Hca]. }
      assert (Hbc : b = c0).
      { apply (Hinjective0 b c0 Hbd Hcd). rewrite Hfb. rewrite Hfc. reflexivity. }
      exact Hbc. }

  assert (Hxeq0 : x ~ ran(F|(α0)) = Φ).
  { destruct Hstop as [HnE | Hxeq0].
    - exfalso.
      apply HnE.
      assert (Hres0 : F|(α0) = F).
      { apply (proj2 (MKT71 (F|(α0)) F (MKT126a F α0 HF) HF)).
        intros z.
        destruct (classic (z ∈ dom(F))) as [Hz | Hnz].
        - assert (Hz0 : z ∈ α0) by (rewrite Hdom_eq0 in Hz; exact Hz).
          assert (Ez : Ensemble z) by (exact (HβE z Hz0)).
          assert (Hzres : z ∈ dom(F|(α0))).
          { rewrite (MKT126b F α0 HF).
            apply AxiomII; split; [exact Ez | split; [exact Hz0 | exact Hz]]. }
          rewrite (MKT126c F α0 HF z Hzres).
          reflexivity.
        - assert (Hzres : z ∉ dom(F|(α0))).
          { intro Hzz. rewrite (MKT126b F α0 HF) in Hzz.
            apply AxiomII in Hzz as [E [Hz0 _]].
            apply Hnz. rewrite Hdom_eq0. exact Hz0. }
          rewrite (MKT69a (x:=z) (f:=F|(α0)) Hzres).
          rewrite (MKT69a (x:=z) (f:=F) Hnz).
          reflexivity. }
      assert (HF_E : Ensemble F).
      { apply MKT75.
        - exact HF.
        - rewrite Hdom_eq0. exact Eα0. }
      rewrite <- Hres0 in HF_E. exact HF_E.
    - exact Hxeq0. }

  assert (Hran0 : ran(F) = x).
  { apply AxiomI; intros z; split.
    - intros Hz.
      apply AxiomII in Hz as [Ez Hz].
      destruct Hz as [a Ha].
      assert (Eaz : Ensemble ([a,z])).
      { unfold Ensemble; eauto. }
      destruct (MKT49b a z Eaz) as [Ea Ez'].
      assert (Hfa : F[a] = z) by (apply (MKT_fval F a z HF); exact Ha).
      assert (Had : a ∈ dom(F)).
      { apply AxiomII; split; [exact Ea | exists z; exact Ha]. }
      assert (Haa0 : a ∈ α0) by (rewrite <- Hdom_eq0; exact Had).
      destruct (Hactive_below a Haa0) as [HFE Hne].
      pose proof (Hactive a (HβR a Haa0) HFE Hne) as Hin.
      apply AxiomII in Hin as [E [Hinx _]].
      rewrite <- Hfa. exact Hinx.
    - intros Hzx.
      assert (Hzran : z ∈ ran(F|(α0))).
      { apply NNPP; intro Hzn.
        assert (HzΦ : z ∈ Φ).
        { rewrite <- Hxeq0.
          apply AxiomII; split; [unfold Ensemble; eauto | split; [exact Hzx |
            apply AxiomII; split; [unfold Ensemble; eauto | exact Hzn]]]. }
        exact (MKT16 HzΦ). }
      apply AxiomII in Hzran as [Ez Hzran].
      destruct Hzran as [a Ha].
      apply AxiomII; split; [exact Ez | exists a].
      unfold Restriction in Ha.
      apply AxiomII in Ha as [Ea [Haz _]].
      exact Haz. }

  exists F.
  split.
  - split; [exact HF | exact Hinvf0].
  - split.
    + exact Hran0.
    + rewrite Hdom_eq0.
      apply AxiomII; split; [exact Eα0' | exact Hordα0].
Qed.

Theorem MKT142 : ∀ n, Nest n -> (∀ m, m ∈ n -> Nest m)
  -> Nest (∪n).
Proof.
  intros n Hn Hnm.
  unfold Nest.
  intros x y Hx Hy.
  apply AxiomII in Hx as [Ex Hx].
  apply AxiomII in Hy as [Ey Hy].
  destruct Hx as [m [Hxm Hmn]].
  destruct Hy as [m' [Hym' Hm'n]].
  destruct (Hn m m' Hmn Hm'n) as [Hmm' | Hm'm].
  - apply (Hnm m' Hm'n x y (Hmm' x Hxm) Hym').
  - apply (Hnm m Hmn x y Hxm (Hm'm y Hym')).
Qed.

Theorem MKT143 : ∀ x, Ensemble x -> ∃ n, (Nest n /\ n ⊂ x)
  /\ (∀ m, Nest m -> m ⊂ x -> n ⊂ m -> m = n).
Proof.
  intros x Hx.
  destruct (MKT140 x Hx) as [f [Hf11 [Hfran Hfdom]]].
  apply AxiomII in Hfdom as [Eα Hordα].
  set (α := dom(f)).
  assert (Hf : Function f) by (destruct Hf11; assumption).
  assert (EΦ : Ensemble Φ).
  { exact (MKT33 x Φ Hx (MKT26 x)). }
  assert (HPhi_ne : [Φ] ≠ Φ).
  { intro H.
    assert (Hin : Φ ∈ [Φ]) by (apply (proj2 (MKT41 Φ EΦ Φ)); reflexivity).
    rewrite H in Hin. exact (MKT16 Hin). }
  assert (HPhi_mu : [Φ] ≠ μ).
  { intro H. exact ((proj1 (MKT43 Φ) H) EΦ). }
  assert (HPhi_mu2 : Φ ≠ μ).
  { intro H.
    assert (Hin : Φ ∈ μ) by (apply MKT19b; exact EΦ).
    rewrite <- H in Hin. exact (MKT16 Hin). }

  assert (HβEns : ∀ β, β ∈ α -> Ensemble β).
  { intros β Hβ. exact (MKT33 α β Eα (proj2 Hordα β Hβ)). }
  assert (HβR : ∀ β, β ∈ α -> β ∈ R).
  { intros β Hβ.
    apply AxiomII; split.
    - exact (HβEns β Hβ).
    - exact (MKT111 α β Hordα Hβ). }
  assert (HfβE : ∀ β, β ∈ α -> Ensemble (f[β])).
  { intros β Hβ.
    apply MKT19a. apply (MKT69b (x:=β) (f:=f)). exact Hβ. }
  assert (Hfβ_dv : ∀ β, β ∈ α -> [β, f[β]] ∈ f).
  { intros β Hβ. apply (MKT_dom_val f β Hf Hβ). }
  assert (Hfβx : ∀ β, β ∈ α -> f[β] ∈ x).
  { intros β Hβ. rewrite <- Hfran. apply AxiomII; split.
    - exact (HfβE β Hβ).
    - exists β; exact (Hfβ_dv β Hβ). }

  set (g := \{\ λ h y, (∃ β, Ordinal_Number β /\ Function h /\ dom(h) = β
       /\ (∀ γ, γ ∈ β -> h[γ] = [Φ] -> f[γ] ⊂ f[β] \/ f[β] ⊂ f[γ]) /\ y = [Φ])
    \/ (∃ β, Ordinal_Number β /\ Function h /\ dom(h) = β
       /\ (∃ γ, γ ∈ β /\ h[γ] = [Φ] /\ ~(f[γ] ⊂ f[β]) /\ ~(f[β] ⊂ f[γ])) /\ y = Φ) \}\).

  assert (Hg_in : ∀ h y, [h,y] ∈ g
    -> (∃ β, Ordinal_Number β /\ Function h /\ dom(h) = β
       /\ (∀ γ, γ ∈ β -> h[γ] = [Φ] -> f[γ] ⊂ f[β] \/ f[β] ⊂ f[γ]) /\ y = [Φ])
    \/ (∃ β, Ordinal_Number β /\ Function h /\ dom(h) = β
       /\ (∃ γ, γ ∈ β /\ h[γ] = [Φ] /\ ~(f[γ] ⊂ f[β]) /\ ~(f[β] ⊂ f[γ])) /\ y = Φ)).
  { intros h y Hin.
    apply AxiomII in Hin as [Ehy Hpred].
    destruct Hpred as [h' [y' [Hpair Hpred']]].
    assert (Eh'y' : Ensemble ([h',y'])).
    { rewrite <- Hpair. exact Ehy. }
    destruct (MKT49b h' y' Eh'y') as [Eh' Ey'].
    destruct (proj1 (MKT55 h' y' h y Eh' Ey') (eq_sym Hpair)) as [Hh' Hy'].
    subst h'. subst y'.
    exact Hpred'. }

  assert (Hgfunc : Function g).
  { unfold Function. split.
    - intros z Hz.
      apply AxiomII in Hz as [Ez Hz].
      destruct Hz as [h [y [Hzy _]]].
      exists h; exists y; exact Hzy.
    - intros a b c Hab Hac.
      pose proof (Hg_in a b Hab) as Hpred1.
      pose proof (Hg_in a c Hac) as Hpred2.
      destruct Hpred1 as [H1 | H1'].
      + destruct H1 as [β1 [Hβ1R [HF1 [Hd1 [Hall1 Hb]]]]].
        destruct Hpred2 as [H2 | H2'].
        * destruct H2 as [β2 [Hβ2R [HF2 [Hd2 [Hall2 Hc]]]]].
          rewrite Hb. rewrite Hc. reflexivity.
        * destruct H2' as [β2 [Hβ2R [HF2 [Hd2 [Hbad2 Hc]]]]].
          destruct Hbad2 as [γ2 [Hγ2 [Hm2 [Hi1 Hi2]]]].
          exfalso.
          assert (Hβ12 : β1 = β2).
          { rewrite <- Hd1. rewrite <- Hd2. reflexivity. }
          assert (Hγ2' : γ2 ∈ β1).
          { rewrite Hβ12. exact Hγ2. }
          assert (Hcmp : f[γ2] ⊂ f[β1] \/ f[β1] ⊂ f[γ2]).
          { apply (Hall1 γ2 Hγ2' Hm2). }
          destruct Hcmp as [Hc1 | Hc2].
          { assert (Hi1' : ~(f[γ2] ⊂ f[β1])).
            { rewrite <- Hβ12 in Hi1. exact Hi1. }
            exact (Hi1' Hc1). }
          { assert (Hi2' : ~(f[β1] ⊂ f[γ2])).
            { rewrite <- Hβ12 in Hi2. exact Hi2. }
            exact (Hi2' Hc2). }
      + destruct H1' as [β1 [Hβ1R [HF1 [Hd1 [Hbad1 Hb]]]]].
        destruct Hbad1 as [γ1 [Hγ1 [Hm1 [Hi1 Hi2]]]].
        destruct Hpred2 as [H2 | H2'].
        * destruct H2 as [β2 [Hβ2R [HF2 [Hd2 [Hall2 Hc]]]]].
          exfalso.
          assert (Hβ12 : β1 = β2).
          { rewrite <- Hd1. rewrite <- Hd2. reflexivity. }
          assert (Hγ1' : γ1 ∈ β2).
          { rewrite <- Hβ12. exact Hγ1. }
          assert (Hcmp : f[γ1] ⊂ f[β2] \/ f[β2] ⊂ f[γ1]).
          { apply (Hall2 γ1 Hγ1' Hm1). }
          destruct Hcmp as [Hc1 | Hc2].
          { assert (Hi1' : ~(f[γ1] ⊂ f[β2])).
            { rewrite Hβ12 in Hi1. exact Hi1. }
            exact (Hi1' Hc1). }
          { assert (Hi2' : ~(f[β2] ⊂ f[γ1])).
            { rewrite Hβ12 in Hi2. exact Hi2. }
            exact (Hi2' Hc2). }
        * destruct H2' as [β2 [Hβ2R [HF2 [Hd2 [Hbad2 Hc]]]]].
          destruct Hbad2 as [γ2 [Hγ2 [Hm2 [Hi1' Hi2']]]].
          rewrite Hb. rewrite Hc. reflexivity. }

  assert (Hnotall : ∀ h β, Ordinal_Number β -> Function h -> dom(h) = β
    -> ~ (∀ γ, γ ∈ β -> h[γ] = [Φ] -> f[γ] ⊂ f[β] \/ f[β] ⊂ f[γ])
    -> ∃ γ, γ ∈ β /\ h[γ] = [Φ] /\ ~(f[γ] ⊂ f[β]) /\ ~(f[β] ⊂ f[γ])).
  { intros h β _ HF Hd Hnot.
    apply NNPP; intro Hno.
    exfalso.
    apply Hnot.
    intros γ Hγ Hh.
    apply NNPP; intro Hnc.
    apply Hno; exists γ; split; [exact Hγ | split; [exact Hh |]].
    exact (proj1 (proj2 (notandor (f[γ] ⊂ f[β]) (f[β] ⊂ f[γ]))) Hnc). }

  assert (Hg_all : ∀ h β, Ordinal_Number β -> Function h -> dom(h) = β
    -> (∀ γ, γ ∈ β -> h[γ] = [Φ] -> f[γ] ⊂ f[β] \/ f[β] ⊂ f[γ])
    -> Ensemble h -> [h, [Φ]] ∈ g).
  { intros h β HβR0 HF Hd Hall HE.
    apply AxiomII; split.
    - apply MKT49a; [exact HE | apply MKT42; exact EΦ].
    - exists h; exists ([Φ]); split; [reflexivity |].
      left. exists β; split; [exact HβR0 | split; [exact HF | split; [exact Hd |
        split; [exact Hall | reflexivity]]]]. }
  assert (Hg_bad : ∀ h β, Ordinal_Number β -> Function h -> dom(h) = β
    -> (∃ γ, γ ∈ β /\ h[γ] = [Φ] /\ ~(f[γ] ⊂ f[β]) /\ ~(f[β] ⊂ f[γ]))
    -> Ensemble h -> [h, Φ] ∈ g).
  { intros h β HβR0 HF Hd Hbad HE.
    apply AxiomII; split.
    - apply MKT49a; [exact HE | exact EΦ].
    - exists h; exists Φ; split; [reflexivity |].
      right. exists β; split; [exact HβR0 | split; [exact HF | split; [exact Hd |
        split; [exact Hbad | reflexivity]]]]. }
  assert (Hg_val_all : ∀ h β, Ordinal_Number β -> Function h -> dom(h) = β
    -> Ensemble h
    -> (∀ γ, γ ∈ β -> h[γ] = [Φ] -> f[γ] ⊂ f[β] \/ f[β] ⊂ f[γ])
    -> g[h] = [Φ]).
  { intros h β HβR0 HF Hd HE Hall.
    apply (MKT_fval g h ([Φ]) Hgfunc).
    apply (Hg_all h β HβR0 HF Hd Hall HE). }
  assert (Hg_val_bad : ∀ h β, Ordinal_Number β -> Function h -> dom(h) = β
    -> Ensemble h
    -> (∃ γ, γ ∈ β /\ h[γ] = [Φ] /\ ~(f[γ] ⊂ f[β]) /\ ~(f[β] ⊂ f[γ]))
    -> g[h] = Φ).
  { intros h β HβR0 HF Hd HE Hbad.
    apply (MKT_fval g h Φ Hgfunc).
    apply (Hg_bad h β HβR0 HF Hd Hbad HE). }
  assert (Hg_val : ∀ h β, Ordinal_Number β -> Function h -> dom(h) = β
    -> Ensemble h -> g[h] = [Φ] \/ g[h] = Φ).
  { intros h β HβR0 HF Hd HE.
    destruct (classic (∀ γ, γ ∈ β -> h[γ] = [Φ] -> f[γ] ⊂ f[β] \/ f[β] ⊂ f[γ])) as [Hall | Hnot].
    - left. apply (Hg_val_all h β HβR0 HF Hd HE Hall).
    - right. apply (Hg_val_bad h β HβR0 HF Hd HE).
      exact (Hnotall h β HβR0 HF Hd Hnot). }

  destruct (MKT128a g) as [M [HM [HOM HMrec]]].

  assert (HdomM : ∀ β, β ∈ α -> β ∈ dom(M)).
  { intros β Hβα.
    apply NNPP; intro Hβndom.
    assert (HβR0 : β ∈ R) by (exact (HβR β Hβα)).
    apply AxiomII in HβR0 as [Eβ Hβord].
    destruct (MKT110 Hβord HOM) as [Hin | [Hdomin | Heq]].
    - exfalso. exact (Hβndom Hin).
    - assert (Hγsubβ : dom(M) ⊂ β) by (exact (proj2 Hβord dom(M) Hdomin)).
      set (γ := dom(M)).
      assert (HγR : γ ∈ R).
      { apply AxiomII; split.
        - apply (MKT33 β γ Eβ Hγsubβ).
        - unfold γ. exact HOM. }
      pose proof (proj1 (AxiomII γ Ordinal) HγR) as [Eγ Hγord].
      assert (HEM : Ensemble M).
      { apply MKT75; [exact HM | exact Eγ]. }
      assert (HgM : g[M] = [Φ] \/ g[M] = Φ).
      { apply (Hg_val M γ); [exact HγR | exact HM | unfold γ; reflexivity | exact HEM]. }
      assert (HMrecβ : M[β] = g[M|(β)]) by (apply HMrec; exact (HβR β Hβα)).
      assert (HMβ : M[β] = μ) by (apply (MKT69a (x:=β) (f:=M)); exact Hβndom).
      assert (Hresβ : M|(β) = M).
      { apply (proj2 (MKT71 (M|(β)) M (MKT126a M β HM) HM)).
        intros u.
        destruct (classic (u ∈ dom(M))) as [Hud | Hnud].
        - assert (Huβ : u ∈ β) by (exact (Hγsubβ u Hud)).
          assert (Eu : Ensemble u).
          { apply AxiomII in Hud as [Eu _]. exact Eu. }
          assert (Hures : u ∈ dom(M|(β))).
          { rewrite (MKT126b M β HM).
            apply AxiomII; split; [exact Eu | split; [exact Huβ | exact Hud]]. }
          rewrite (MKT126c M β HM u Hures).
          reflexivity.
        - assert (Hures : u ∉ dom(M|(β))).
          { intro Hr. rewrite (MKT126b M β HM) in Hr.
            apply AxiomII in Hr as [E [Huβ Hud]]. exact (Hnud Hud). }
          rewrite (MKT69a (x:=u) (f:=M|(β)) Hures).
          rewrite (MKT69a (x:=u) (f:=M) Hnud).
          reflexivity. }
      assert (HgM_mu : g[M] = μ).
      { assert (H1 : g[M|(β)] = μ).
        { symmetry.
          assert (H2 : M[β] = g[M|(β)]) by exact HMrecβ.
          rewrite HMβ in H2. exact H2. }
        rewrite Hresβ in H1. exact H1. }
      destruct HgM as [HgM1 | HgM2].
      + exfalso. apply HPhi_mu. rewrite <- HgM1. exact HgM_mu.
      + exfalso. apply HPhi_mu2. rewrite <- HgM2. exact HgM_mu.
    - assert (Hγsubβ : dom(M) ⊂ β).
      { rewrite Heq. apply MKT26a. }
      set (γ := dom(M)).
      assert (HγR : γ ∈ R).
      { apply AxiomII; split.
        - apply (MKT33 β γ Eβ Hγsubβ).
        - unfold γ. exact HOM. }
      pose proof (proj1 (AxiomII γ Ordinal) HγR) as [Eγ Hγord].
      assert (HEM : Ensemble M).
      { apply MKT75; [exact HM | exact Eγ]. }
      assert (HgM : g[M] = [Φ] \/ g[M] = Φ).
      { apply (Hg_val M γ); [exact HγR | exact HM | unfold γ; reflexivity | exact HEM]. }
      assert (HMrecβ : M[β] = g[M|(β)]) by (apply HMrec; exact (HβR β Hβα)).
      assert (HMβ : M[β] = μ) by (apply (MKT69a (x:=β) (f:=M)); exact Hβndom).
      assert (Hresβ : M|(β) = M).
      { apply (proj2 (MKT71 (M|(β)) M (MKT126a M β HM) HM)).
        intros u.
        destruct (classic (u ∈ dom(M))) as [Hud | Hnud].
        - assert (Huβ : u ∈ β) by (exact (Hγsubβ u Hud)).
          assert (Eu : Ensemble u).
          { apply AxiomII in Hud as [Eu _]. exact Eu. }
          assert (Hures : u ∈ dom(M|(β))).
          { rewrite (MKT126b M β HM).
            apply AxiomII; split; [exact Eu | split; [exact Huβ | exact Hud]]. }
          rewrite (MKT126c M β HM u Hures).
          reflexivity.
        - assert (Hures : u ∉ dom(M|(β))).
          { intro Hr. rewrite (MKT126b M β HM) in Hr.
            apply AxiomII in Hr as [E [Huβ Hud]]. exact (Hnud Hud). }
          rewrite (MKT69a (x:=u) (f:=M|(β)) Hures).
          rewrite (MKT69a (x:=u) (f:=M) Hnud).
          reflexivity. }
      assert (HgM_mu : g[M] = μ).
      { assert (H1 : g[M|(β)] = μ).
        { symmetry.
          assert (H2 : M[β] = g[M|(β)]) by exact HMrecβ.
          rewrite HMβ in H2. exact H2. }
        rewrite Hresβ in H1. exact H1. }
      destruct HgM as [HgM1 | HgM2].
      + exfalso. apply HPhi_mu. rewrite <- HgM1. exact HgM_mu.
      + exfalso. apply HPhi_mu2. rewrite <- HgM2. exact HgM_mu. }

  assert (HMres : ∀ β, β ∈ α -> Function (M|(β)) /\ dom(M|(β)) = β /\ Ensemble (M|(β))).
  { intros β Hβ.
    split; [apply MKT126a; exact HM |].
    split.
    - rewrite (MKT126b M β HM).
      apply (proj2 (MKT30 β (dom(M)))).
      intros u Hu. exact (proj2 HOM β (HdomM β Hβ) u Hu).
    - apply MKT75; [apply MKT126a; exact HM |].
      rewrite (MKT126b M β HM).
      apply (MKT33 β (β ∩ dom(M))).
      + exact (HβEns β Hβ).
      + intros z Hz. apply AxiomII in Hz as [E [Hzβ _]]. exact Hzβ. }

  assert (Hresγ : ∀ β γ, β ∈ α -> γ ∈ β -> (M|(β))[γ] = M[γ]).
  { intros β γ Hβα Hγβ.
    apply (MKT126c M β HM γ).
    rewrite (MKT126b M β HM).
    apply AxiomII; split.
    - exact (HβEns γ (proj2 Hordα β Hβα γ Hγβ)).
    - split; [exact Hγβ | exact (proj2 HOM β (HdomM β Hβα) γ Hγβ)]. }

  assert (HM_all : ∀ β, β ∈ α -> M[β] = [Φ]
    -> ∀ γ, γ ∈ β -> M[γ] = [Φ] -> f[γ] ⊂ f[β] \/ f[β] ⊂ f[γ]).
  { intros β Hβα HMβ γ Hγβ HMγ.
    assert (HMrecβ : M[β] = g[M|(β)]) by (apply HMrec; exact (HβR β Hβα)).
    assert (HgMβ : g[M|(β)] = [Φ]) by (rewrite <- HMrecβ; exact HMβ).
    destruct (HMres β Hβα) as [HF' [Hd' HE']].
    assert (Hin : [M|(β), [Φ]] ∈ g).
    { rewrite <- HgMβ.
      apply (MKT_dom_val g (M|(β)) Hgfunc).
      apply MKT69b'.
      apply MKT19b.
      rewrite HgMβ. apply MKT42. exact EΦ. }
    pose proof (Hg_in (M|(β)) ([Φ]) Hin) as Hpred.
    destruct Hpred as [Hfirst | Hsecond].
    - destruct Hfirst as [β' [Hβ'R [HF'' [Hd'' [Hall' Hval]]]]].
      assert (Hβ'eq : β' = β).
      { rewrite <- Hd''. rewrite (MKT126b M β HM).
        apply (proj2 (MKT30 β (dom(M)))).
        intros u Hu. exact (proj2 HOM β (HdomM β Hβα) u Hu). }
      rewrite Hβ'eq in Hall'.
      apply (Hall' γ Hγβ).
      rewrite (Hresγ β γ Hβα Hγβ). exact HMγ.
    - destruct Hsecond as [β' [Hβ'R [HF'' [Hd'' [Hbad' Hval]]]]].
      exfalso. apply HPhi_ne. exact Hval. }

  assert (Hbad : ∀ β, β ∈ α -> M[β] = Φ
    -> ∃ γ, γ ∈ β /\ M[γ] = [Φ] /\ ~(f[γ] ⊂ f[β]) /\ ~(f[β] ⊂ f[γ])).
  { intros β Hβα HMβ.
    assert (HMrecβ : M[β] = g[M|(β)]) by (apply HMrec; exact (HβR β Hβα)).
    assert (HgMβ : g[M|(β)] = Φ) by (rewrite <- HMrecβ; exact HMβ).
    destruct (HMres β Hβα) as [HF' [Hd' HE']].
    assert (Hin : [M|(β), Φ] ∈ g).
    { rewrite <- HgMβ.
      apply (MKT_dom_val g (M|(β)) Hgfunc).
      apply MKT69b'.
      apply MKT19b.
      rewrite HgMβ. exact EΦ. }
    pose proof (Hg_in (M|(β)) Φ Hin) as Hpred.
    destruct Hpred as [Hfirst | Hsecond].
    - destruct Hfirst as [β' [Hβ'R [HF'' [Hd'' [Hall' Hval]]]]].
      exfalso. apply HPhi_ne. symmetry. exact Hval.
    - destruct Hsecond as [β' [Hβ'R [HF'' [Hd'' [Hbad' Hval]]]]].
      assert (Hβ'eq : β' = β).
      { rewrite <- Hd''. rewrite (MKT126b M β HM).
        apply (proj2 (MKT30 β (dom(M)))).
        intros u Hu. exact (proj2 HOM β (HdomM β Hβα) u Hu). }
      destruct Hbad' as [γ [Hγβ [Hmγ [Hi1 Hi2]]]].
      rewrite Hβ'eq in Hγβ, Hi1, Hi2.
      exists γ; split; [exact Hγβ | split].
      + rewrite <- (Hresγ β γ Hβα Hγβ). exact Hmγ.
      + split; [exact Hi1 | exact Hi2]. }

  set (C := \{ λ y, ∃ β, β ∈ α /\ y = f[β] /\ M[β] = [Φ] \}).

  assert (HC_sub : C ⊂ x).
  { intros z Hz.
    apply AxiomII in Hz as [Ez Hz].
    destruct Hz as [β [Hβα [Hzβ HMβ]]].
    rewrite Hzβ. exact (Hfβx β Hβα). }

  assert (HNest : Nest C).
  { unfold Nest. intros y z Hy Hz.
    apply AxiomII in Hy as [Ey Hy].
    apply AxiomII in Hz as [Ez Hz].
    destruct Hy as [β [Hβα [Hyβ HMβ]]].
    destruct Hz as [γ [Hγα [Hzγ HMγ]]].
    assert (Hβord : Ordinal β) by (exact (MKT111 α β Hordα Hβα)).
    assert (Hγord : Ordinal γ) by (exact (MKT111 α γ Hordα Hγα)).
    destruct (MKT110 Hβord Hγord) as [Hβγ | [Hγβ | Hβγeq]].
    - assert (Hcmp : f[β] ⊂ f[γ] \/ f[γ] ⊂ f[β]).
      { apply (HM_all γ Hγα HMγ β Hβγ HMβ). }
      destruct Hcmp as [Hc1 | Hc2].
      + left. rewrite Hyβ. rewrite Hzγ. exact Hc1.
      + right. rewrite Hyβ. rewrite Hzγ. exact Hc2.
    - assert (Hcmp : f[γ] ⊂ f[β] \/ f[β] ⊂ f[γ]).
      { apply (HM_all β Hβα HMβ γ Hγβ HMγ). }
      destruct Hcmp as [Hc1 | Hc2].
      + right. rewrite Hyβ. rewrite Hzγ. exact Hc1.
      + left. rewrite Hyβ. rewrite Hzγ. exact Hc2.
    - subst γ. rewrite Hyβ. rewrite Hzγ.
      left. exact (MKT26a (f[β])). }

  assert (Hmax : ∀ m, Nest m -> m ⊂ x -> C ⊂ m -> m = C).
  { intros m Hm Hmx HCm.
    apply (proj1 (MKT27 m C)); split.
    - intros y Hym.
      assert (Ey : Ensemble y) by (unfold Ensemble; exists m; exact Hym).
      assert (Hyx : y ∈ x) by (exact (Hmx y Hym)).
      assert (Hyran : y ∈ ran(f)) by (rewrite Hfran; exact Hyx).
      apply AxiomII in Hyran as [Ey' Hyran].
      destruct Hyran as [β Hβy].
      assert (Hfβ : f[β] = y) by (apply (MKT_fval f β y Hf); exact Hβy).
      assert (Hβα : β ∈ α) by (unfold α; apply AxiomII; split;
        [assert (Eβy : Ensemble ([β,y])) by (unfold Ensemble; exists f; exact Hβy);
         exact (proj1 (MKT49b β y Eβy)) | exists y; exact Hβy]).
      assert (HMβv : M[β] = [Φ] \/ M[β] = Φ).
      { assert (HMrecβ : M[β] = g[M|(β)]) by (apply HMrec; exact (HβR β Hβα)).
        destruct (HMres β Hβα) as [HF' [Hd' HE']].
        destruct (Hg_val (M|(β)) β (HβR β Hβα) HF' Hd' HE') as [Hg1 | Hg2].
        - left. rewrite HMrecβ. exact Hg1.
        - right. rewrite HMrecβ. exact Hg2. }
      destruct HMβv as [HMβ | HMβ].
      + apply AxiomII; split.
        * exact Ey.
        * exists β; split; [exact Hβα | split; [exact (eq_sym Hfβ) | exact HMβ]].
      + destruct (Hbad β Hβα HMβ) as [γ [Hγβ [HMγ [Hi1 Hi2]]]].
        assert (HfγC : f[γ] ∈ C).
        { apply AxiomII; split.
          - exact (HfβE γ (proj2 Hordα β Hβα γ Hγβ)).
          - exists γ; split; [exact (proj2 Hordα β Hβα γ Hγβ) | split;
            [reflexivity | exact HMγ]]. }
        assert (Hfγm : f[γ] ∈ m) by (exact (HCm (f[γ]) HfγC)).
        assert (Hfβm : f[β] ∈ m) by (rewrite Hfβ; exact Hym).
        destruct (Hm (f[γ]) (f[β]) Hfγm Hfβm) as [Hc1 | Hc2].
        * exfalso; exact (Hi1 Hc1).
        * exfalso; exact (Hi2 Hc2).
    - exact HCm. }

  exists C; split; [split; [exact HNest | exact HC_sub] | exact Hmax].
Qed.

(* A.11 基数 *)

Theorem MKT145 : ∀ x, x ≈ x.
Proof.
  intros x.
  set (id := \{\ λ u v, u ∈ x /\ v = u \}\).
  assert (Hid_func : Function id).
  { unfold Function. split.
    - intros z Hz.
      apply AxiomII in Hz as [Ez Hz].
      destruct Hz as [u [v [Huv _]]].
      exists u; exists v; exact Huv.
    - intros u v w Huv Huvw.
      apply AxiomII in Huv as [Euv Huv].
      apply AxiomII in Huvw as [Euvw Huvw].
      destruct Huv as [a1 [b1 [H1 [Ha1x H1b]]]].
      destruct Huvw as [a2 [b2 [H2 [Ha2x H2b]]]].
      assert (Ea1b1 : Ensemble ([a1,b1])).
      { rewrite <- H1. exact Euv. }
      destruct (MKT49b a1 b1 Ea1b1) as [Ea1 Eb1].
      assert (Ea2b2 : Ensemble ([a2,b2])).
      { rewrite <- H2. exact Euvw. }
      destruct (MKT49b a2 b2 Ea2b2) as [Ea2 Eb2].
      destruct (proj1 (MKT55 a1 b1 u v Ea1 Eb1) (eq_sym H1)) as [Ha1u Hb1v].
      destruct (proj1 (MKT55 a2 b2 u w Ea2 Eb2) (eq_sym H2)) as [Ha2u Hb2w].
      rewrite Ha1u in *. rewrite Hb1v in *. rewrite Ha2u in *. rewrite Hb2w in *.
      rewrite H1b. rewrite H2b. reflexivity. }
  assert (Hid_inv : Function (id⁻¹)).
  { unfold Function. split.
    - intros z Hz.
      apply AxiomII in Hz as [Ez Hz].
      destruct Hz as [u [v [Huv _]]].
      exists u; exists v; exact Huv.
    - intros u v w Huv Huvw.
      assert (Hinv_id : ∀ u0 v0, [u0,v0] ∈ id⁻¹ -> [v0,u0] ∈ id).
      { intros u0 v0 Huv0.
        apply AxiomII in Huv0 as [Euv0 Huv0].
        destruct Huv0 as [a [b [Hab Hba]]].
        assert (Eab : Ensemble ([a,b])).
        { rewrite <- Hab. exact Euv0. }
        destruct (MKT49b a b Eab) as [Ea Eb].
        destruct (MKT49b u0 v0 Euv0) as [Eu Ev].
        destruct (proj1 (MKT55 u0 v0 a b Eu Ev) Hab) as [Hua Hvb].
        subst a b.
        exact Hba. }
      assert (Hid_components : ∀ p q, [p,q] ∈ id -> q = p).
      { intros p q Hpq.
        apply AxiomII in Hpq as [Epq Hpq].
        destruct Hpq as [u0 [v0 [Huv0 [Hux Hvu]]]].
        assert (Eu0v0 : Ensemble ([u0,v0])).
        { rewrite <- Huv0. exact Epq. }
        destruct (MKT49b u0 v0 Eu0v0) as [Eu0 Ev0].
        destruct (MKT49b p q Epq) as [Ep Eq].
        destruct (proj1 (MKT55 p q u0 v0 Ep Eq) Huv0) as [Hpu Hqv].
        subst p q.
        exact Hvu. }
      assert (Hvu : u = v).
      { apply (Hid_components v u). apply (Hinv_id u v). exact Huv. }
      assert (Hwu : u = w).
      { apply (Hid_components w u). apply (Hinv_id u w). exact Huvw. }
      rewrite <- Hvu. rewrite <- Hwu. reflexivity. }
  assert (Hdom : dom(id) = x).
  { apply AxiomI; intros a; split.
    - intros Ha.
      apply AxiomII in Ha as [Ea Ha].
      destruct Ha as [b Hab].
      apply AxiomII in Hab as [Eab Hab].
      destruct Hab as [u [v [Huv [Hux Hvu]]]].
      assert (Euv : Ensemble ([u,v])).
      { rewrite <- Huv. exact Eab. }
      destruct (MKT49b u v Euv) as [Eu Ev].
      destruct (MKT49b a b Eab) as [Ea' Eb].
      destruct (proj1 (MKT55 a b u v Ea' Eb) Huv) as [Hau Hbv].
      rewrite Hau. exact Hux.
    - intros Ha.
      assert (Ea : Ensemble a) by (exists x; exact Ha).
      apply AxiomII; split.
      + exact Ea.
      + exists a.
        apply AxiomII; split.
        * exact (MKT49a Ea Ea).
        * exists a; exists a; split; [reflexivity | split; [exact Ha | reflexivity]]. }
  assert (Hran : ran(id) = x).
  { apply AxiomI; intros b; split.
    - intros Hb.
      apply AxiomII in Hb as [Eb Hb].
      destruct Hb as [a Hab].
      apply AxiomII in Hab as [Eab Hab].
      destruct Hab as [u [v [Huv [Hux Hvu]]]].
      assert (Euv : Ensemble ([u,v])).
      { rewrite <- Huv. exact Eab. }
      destruct (MKT49b u v Euv) as [Eu Ev].
      destruct (MKT49b a b Eab) as [Ea' Eb'].
      destruct (proj1 (MKT55 a b u v Ea' Eb') Huv) as [Hau Hbv].
      rewrite Hbv. rewrite Hvu. exact Hux.
    - intros Hb.
      assert (Eb : Ensemble b) by (exists x; exact Hb).
      apply AxiomII; split.
      + exact Eb.
      + exists b.
        apply AxiomII; split.
        * exact (MKT49a Eb Eb).
        * exists b; exists b; split; [reflexivity | split; [exact Hb | reflexivity]]. }
  exists id.
  split.
  - split; [exact Hid_func | exact Hid_inv].
  - split; [exact Hdom | exact Hran].
Qed.

Theorem MKT146 : ∀ {x y}, x ≈ y -> y ≈ x.
Proof.
  intros x y [f [Hf11 [Hdom Hran]]].
  destruct Hf11 as [Hf Hfinv].
  exists (f⁻¹).
  split.
  - split.
    + exact Hfinv.
    + assert (Hinv_inv : (f⁻¹)⁻¹ = f).
      { apply MKT61; exact (proj1 Hf). }
      rewrite Hinv_inv.
      exact Hf.
  - split.
    + rewrite MKT_dom_inv. exact Hran.
    + rewrite MKT_ran_inv. exact Hdom.
Qed.

Theorem MKT147 : ∀ y x z, x ≈ y -> y ≈ z -> x ≈ z.
Proof.
  intros y x z [f [Hf11 [Hfdom Hfran]]] [g [Hg11 [Hgdom Hgran]]].
  destruct Hf11 as [Hffunc Hfinv].
  destruct Hg11 as [Hgfunc Hginv].
  exists (g ∘ f).
  split.
  - (* Function1_1 (g ∘ f) *)
    split.
    + apply MKT64; assumption.
    + assert (Hinv_comp : (g ∘ f)⁻¹ = f⁻¹ ∘ g⁻¹).
      { apply MKT62. }
      rewrite Hinv_comp.
      apply MKT64; assumption.
  - split.
    + (* dom(g ∘ f) = x *)
      assert (Hdom_comp : dom(g ∘ f) = dom(f)).
      { apply AxiomI; intros a; split.
        - intros Ha.
          apply AxiomII in Ha as [Ea Ha].
          destruct Ha as [c Hac].
          apply AxiomII in Hac as [Eac Hac].
          destruct Hac as [u [v [Hauv [b [Hub Hvc]]]]].
          apply AxiomII; split.
          + exact Ea.
          + exists b.
            assert (Euv : Ensemble ([u,v])).
            { rewrite <- Hauv. exact Eac. }
            destruct (MKT49b u v Euv) as [Eu Ev].
            destruct (MKT49b a c Eac) as [Ea' Ec].
            destruct (proj1 (MKT55 a c u v Ea' Ec) Hauv) as [Hau Hcv].
            rewrite <- Hau in Hub.
            exact Hub.
        - intros Ha.
          apply AxiomII in Ha as [Ea Ha].
          destruct Ha as [b Hab].
          assert (Eab : Ensemble ([a,b])) by (unfold Ensemble; eauto).
          destruct (MKT49b a b Eab) as [Ea' Eb].
          assert (Hbran : b ∈ ran(f)).
          { apply AxiomII; split; [exact Eb | exists a; exact Hab]. }
          rewrite Hfran in Hbran.
          rewrite <- Hgdom in Hbran.
          apply AxiomII in Hbran as [Eb' Hbran].
          destruct Hbran as [c Hbc].
          assert (Ebc : Ensemble ([b,c])) by (unfold Ensemble; eauto).
          destruct (MKT49b b c Ebc) as [Eb'' Ec].
          apply AxiomII; split.
          + exact Ea'.
          + exists c.
            apply AxiomII; split.
            * exact (MKT49a Ea' Ec).
            * exists a; exists c; split; [reflexivity | exists b; split; [exact Hab | exact Hbc]]. }
      rewrite Hdom_comp. exact Hfdom.
    + (* ran(g ∘ f) = z *)
      assert (Hran_comp : ran(g ∘ f) = ran(g)).
      { apply AxiomI; intros c; split.
        - intros Hc.
          apply AxiomII in Hc as [Ec Hc].
          destruct Hc as [a Hac].
          apply AxiomII in Hac as [Eac Hac].
          destruct Hac as [u [v [Hauv [b [Hub Hvc]]]]].
          apply AxiomII; split.
          + exact Ec.
          + exists b.
            assert (Euv : Ensemble ([u,v])).
            { rewrite <- Hauv. exact Eac. }
            destruct (MKT49b u v Euv) as [Eu Ev].
            destruct (MKT49b a c Eac) as [Ea' Ec'].
            destruct (proj1 (MKT55 a c u v Ea' Ec') Hauv) as [Hau Hcv].
            rewrite <- Hcv in Hvc.
            exact Hvc.
        - intros Hc.
          apply AxiomII in Hc as [Ec Hc].
          destruct Hc as [b Hbc].
          assert (Ebc : Ensemble ([b,c])) by (unfold Ensemble; eauto).
          destruct (MKT49b b c Ebc) as [Eb Ec'].
          assert (Hbdom : b ∈ dom(g)).
          { apply AxiomII; split; [exact Eb | exists c; exact Hbc]. }
          rewrite Hgdom in Hbdom.
          rewrite <- Hfran in Hbdom.
          apply AxiomII in Hbdom as [Eb' Hbdom].
          destruct Hbdom as [a Hab].
          assert (Eab : Ensemble ([a,b])) by (unfold Ensemble; eauto).
          destruct (MKT49b a b Eab) as [Ea' Eb''].
          apply AxiomII; split.
          + exact Ec.
          + exists a.
            apply AxiomII; split.
            * exact (MKT49a Ea' Ec').
            * exists a; exists c; split; [reflexivity | exists b; split; [exact Hab | exact Hbc]]. }
      rewrite Hran_comp. exact Hgran.
Qed.

Theorem MKT150 : WellOrdered E C.
Proof.
  apply (MKT_wo_sub E C R).
  - intros z Hz.
    apply AxiomII in Hz as [Ez [HzR _]].
    apply AxiomII in HzR as [Ez' Hzord].
    apply AxiomII; split; [exact Ez' | exact Hzord].
  - apply MKT107; exact MKT113a.
Qed.

Theorem MKT152a : Function P.
Proof.
  assert (Hcard_eq : ∀ u v, u ∈ C -> v ∈ C -> u ≈ v -> u = v).
  { intros u v Hu Hv Huv.
    pose proof (proj1 (AxiomII u (λ x, Cardinal_Number x)) Hu) as [Eu Hcu].
    pose proof (proj1 (AxiomII v (λ x, Cardinal_Number x)) Hv) as [Ev Hcv].
    destruct Hcu as [HuR Hucard].
    destruct Hcv as [HvR Hvcard].
    pose proof (proj1 (AxiomII u Ordinal) HuR) as [Eu' Huord].
    pose proof (proj1 (AxiomII v Ordinal) HvR) as [Ev' Hvord].
    destruct (MKT110 Huord Hvord) as [Huv' | [Hvu' | Hueq]].
    - exfalso.
      apply (Hvcard u HuR Huv').
      apply MKT146. exact Huv.
    - exfalso.
      apply (Hucard v HvR Hvu').
      exact Huv.
    - exact Hueq. }
  unfold Function. split.
  - intros z Hz.
    apply AxiomII in Hz as [Ez Hz].
    destruct Hz as [x [y [Hzy _]]].
    exists x; exists y; exact Hzy.
  - intros x y z Hxy Hxz.
    apply AxiomII in Hxy as [E1 Hxy].
    apply AxiomII in Hxz as [E2 Hxz].
    destruct Hxy as [a [b [Hab [Hxb Hbc]]]].
    destruct Hxz as [a' [b' [Ha'b' [Hxa' Ha'c]]]].
    destruct (MKT49b x y E1) as [Ex Ey].
    destruct (MKT49b x z E2) as [Ex' Ez].
    assert (Eab : Ensemble ([a,b])).
    { rewrite <- Hab. exact E1. }
    destruct (MKT49b a b Eab) as [Ea Eb].
    assert (Ea'b' : Ensemble ([a',b'])).
    { rewrite <- Ha'b'. exact E2. }
    destruct (MKT49b a' b' Ea'b') as [Ea' Eb'].
    destruct (proj1 (MKT55 x y a b Ex Ey) Hab) as [Hxa Hyb].
    destruct (proj1 (MKT55 x z a' b' Ex' Ez) Ha'b') as [Hxa2 Hzb'].
    rewrite <- Hxa in *. rewrite <- Hyb in *.
    rewrite <- Hxa2 in *. rewrite <- Hzb' in *.
    assert (Hyz : y ≈ z).
    { apply (MKT147 x y z).
      - apply MKT146. exact Hxb.
      - exact Hxa'. }
    exact (Hcard_eq y z Hbc Ha'c Hyz).
Qed.

Theorem MKT152b : dom(P) = μ.
Proof.
  apply AxiomI; intros x; split.
  - intros Hx.
    apply AxiomII in Hx as [Ex Hx].
    destruct Hx as [y Hxy].
    apply AxiomII in Hxy as [Exy Hxy'].
    destruct Hxy' as [u [v [Huv [Hux Hvc]]]].
    apply AxiomII; split; [exact Ex | auto].
  - intros Hx.
    apply AxiomII in Hx as [Ex Hx].
    destruct (MKT140 x Ex) as [f [Hf11 [Hfran Hfdom]]].
    apply AxiomII in Hfdom as [Edom Hord].
    assert (Hrel_fwd : ∀ a b, Ensemble a -> Ensemble b -> a ∈ b -> Rrelation a E b).
    { intros a b Ea Eb Hab.
      unfold Rrelation.
      apply AxiomII; split.
      - apply MKT49a; assumption.
      - exists a; exists b; split; [reflexivity | exact Hab]. }
    set (S := \{ λ β, β ∈ R /\ β ≈ x \}).
    assert (HSsub : S ⊂ R).
    { intros β Hβ. apply AxiomII in Hβ as [Eβ [HβR _]]. exact HβR. }
    assert (HSne : S ≠ Φ).
    { intro HS.
      assert (HαS : dom(f) ∈ S).
      { apply AxiomII; split.
        - exact Edom.
        - split.
          + apply AxiomII; split; [exact Edom | exact Hord].
          + exists f; split; [exact Hf11 | split; [reflexivity | exact Hfran]]. }
      rewrite HS in HαS.
      exact (MKT16 HαS). }
    assert (HwoR : WellOrdered E R).
    { apply MKT107; exact MKT113a. }
    destruct HwoR as [HconnR HwosubR].
    destruct (HwosubR S HSsub HSne) as [β0 [Hβ0S Hβ0min]].
    apply AxiomII in Hβ0S as [Eβ0 Hβ0S'].
    destruct Hβ0S' as [Hβ0R Hβ0x].
    apply AxiomII in Hβ0R as [Eβ0' Hordβ0].
    assert (Hcard : ∀ y, y ∈ R -> y ∈ β0 -> ~ (β0 ≈ y)).
    { intros y HyR Hyβ0 Hβ0y.
      apply (Hβ0min y).
      - apply AxiomII; split.
        + apply AxiomII in HyR as [Ey _]. exact Ey.
        + split; [exact HyR |].
          apply (MKT147 β0 y x).
          * exact (MKT146 Hβ0y).
          * exact Hβ0x.
      - apply Hrel_fwd.
        + apply AxiomII in HyR as [Ey _]. exact Ey.
        + exact Eβ0'.
        + exact Hyβ0. }
    assert (Hβ0C : β0 ∈ C).
    { apply AxiomII; split.
      - exact Eβ0'.
      - split.
        + apply AxiomII; split; [exact Eβ0' | exact Hordβ0].
        + exact Hcard. }
    assert (Hdomfx : dom(f) ≈ x).
    { exists f; split; [exact Hf11 | split; [reflexivity | exact Hfran]]. }
    assert (Hβ0dom : β0 ≈ dom(f)).
    { apply (MKT147 x β0 dom(f)); [exact Hβ0x | apply MKT146; exact Hdomfx]. }
    assert (Hxβ0 : x ≈ β0).
    { apply (MKT147 dom(f) x β0); [exact (MKT146 Hdomfx) | exact (MKT146 Hβ0dom)]. }
    apply AxiomII; split.
    { exact Ex. }
    { exists β0.
      apply AxiomII; split.
      { exact (MKT49a Ex Eβ0'). }
      { exists x; exists β0; split; [reflexivity | split; [exact Hxβ0 | exact Hβ0C]]. } }
Qed.

Theorem MKT152c : ran(P) = C.
Proof.
  apply AxiomI; intros y; split.
  - intros Hy.
    apply AxiomII in Hy as [Ey Hy].
    destruct Hy as [x Hxy].
    apply AxiomII in Hxy as [E Hxy'].
    destruct Hxy' as [x' [y' [Hxy'' [Happrox Hyc]]]].
    destruct (MKT49b x y E) as [Ex Ey'].
    assert (Ex'y' : Ensemble ([x',y'])).
    { rewrite <- Hxy''. exact E. }
    destruct (MKT49b x' y' Ex'y') as [Ex' Ey''].
    destruct (proj1 (MKT55 x y x' y' Ex Ey') Hxy'') as [Hx' Hy'].
    rewrite Hy'. exact Hyc.
  - intros Hy.
    apply AxiomII in Hy as [Ey Hy].
    apply AxiomII; split; [exact Ey | exists y].
    apply AxiomII; split.
    + apply MKT49a; [exact Ey | exact Ey].
    + exists y; exists y; split; [reflexivity | split; [apply MKT145 | apply AxiomII; split; [exact Ey | exact Hy]]].
Qed.

(* Auxiliary lemmas for cardinal arithmetic *)

Lemma MKT_C_Ens : ∀ x, x ∈ C -> Ensemble x.
Proof.
  intros x HxC.
  pose proof (proj1 (AxiomII x (λ x, Cardinal_Number x)) HxC) as [HxE _].
  exact HxE.
Qed.

Lemma MKT_C_ord : ∀ x, x ∈ C -> Ordinal x.
Proof.
  intros x HxC.
  pose proof (proj1 (AxiomII x (λ x, Cardinal_Number x)) HxC) as [HxE [HxR _]].
  exact (proj2 (proj1 (AxiomII x Ordinal) HxR)).
Qed.

Lemma MKT_C_R : ∀ x, x ∈ C -> x ∈ R.
Proof.
  intros x HxC.
  pose proof (proj1 (AxiomII x (λ x, Cardinal_Number x)) HxC) as [HxE [HxR _]].
  exact HxR.
Qed.

Lemma MKT_C_val : ∀ x, Ensemble x -> P[x] ∈ C.
Proof.
  intros x Hx.
  assert (Hxmu : x ∈ μ) by (apply MKT19b; exact Hx).
  rewrite <- MKT152b in Hxmu.
  assert (Hp : [x, P[x]] ∈ P) by (apply (MKT_dom_val P x MKT152a); exact Hxmu).
  apply AxiomII in Hp as [E Hp].
  destruct Hp as [a [b [Hpair [Happrox Hbc]]]].
  assert (Ep : Ensemble (P[x])).
  { exact (proj2 (MKT49b x (P[x]) E)). }
  destruct (proj1 (MKT55 x (P[x]) a b Hx Ep) Hpair) as [Hxa Hpb].
  subst a b.
  exact Hbc.
Qed.

Lemma MKT_card_eq : ∀ u v, u ∈ C -> v ∈ C -> u ≈ v -> u = v.
Proof.
  intros u v Hu Hv Huv.
  pose proof (proj1 (AxiomII u (λ x, Cardinal_Number x)) Hu) as [Eu Hcu].
  pose proof (proj1 (AxiomII v (λ x, Cardinal_Number x)) Hv) as [Ev Hcv].
  destruct Hcu as [HuR Hucard].
  destruct Hcv as [HvR Hvcard].
  pose proof (proj1 (AxiomII u Ordinal) HuR) as [Eu' Huord].
  pose proof (proj1 (AxiomII v Ordinal) HvR) as [Ev' Hvord].
  destruct (MKT110 Huord Hvord) as [Huv' | [Hvu' | Hueq]].
  - exfalso.
    apply (Hvcard u HuR Huv').
    apply MKT146. exact Huv.
  - exfalso.
    apply (Hucard v HvR Hvu').
    exact Huv.
  - exact Hueq.
Qed.

Lemma MKT_card_le : ∀ κ α, κ ∈ C -> α ∈ R -> κ ≈ α -> κ ≼ α.
Proof.
  intros κ α HκC HαR Hκα.
  assert (HκR : κ ∈ R) by (apply MKT_C_R; exact HκC).
  assert (Hκord : Ordinal κ) by (apply MKT_C_ord; exact HκC).
  assert (Hαord : Ordinal α) by (exact (proj2 (proj1 (AxiomII α Ordinal) HαR))).
  destruct (MKT110 Hκord Hαord) as [Hκα' | [Hακ | Hκeq]].
  - left; exact Hκα'.
  - exfalso.
    pose proof (proj1 (AxiomII κ (λ x, Cardinal_Number x)) HκC) as [E Hκcard].
    destruct Hκcard as [_ Hκcard].
    apply (Hκcard α HαR Hακ).
    exact Hκα.
  - right; exact Hκeq.
Qed.

Theorem MKT153 : ∀ {x}, Ensemble x -> P[x] ≈ x.
Proof.
  intros x Hx.
  assert (Hxmu : x ∈ μ) by (apply MKT19b; exact Hx).
  rewrite <- MKT152b in Hxmu.
  assert (HxP : [x, P[x]] ∈ P) by (apply (MKT_dom_val P x MKT152a); exact Hxmu).
  apply AxiomII in HxP as [E HxP].
  destruct HxP as [a [b [Hpair [Happrox Hbc]]]].
  assert (Epx : Ensemble (P[x])).
  { exact (proj2 (MKT49b x (P[x]) E)). }
  destruct (proj1 (MKT55 x (P[x]) a b Hx Epx) Hpair) as [Hxa Hpb].
  subst a b.
  exact (MKT146 Happrox).
Qed.

Theorem MKT154 : ∀ x y, Ensemble x -> Ensemble y
  -> (P[x] = P[y] <-> x ≈ y).
Proof.
  intros x y Hx Hy; split.
  - intros H.
    assert (HxP : x ≈ P[x]) by (apply MKT146; apply MKT153; exact Hx).
    assert (HyP : P[y] ≈ y) by (apply MKT153; exact Hy).
    assert (HxPy : x ≈ P[y]) by (rewrite H in HxP; exact HxP).
    exact (MKT147 P[y] x y HxPy HyP).
  - intros Hxy.
    assert (HpxC : P[x] ∈ C) by (apply MKT_C_val; exact Hx).
    assert (HpyC : P[y] ∈ C) by (apply MKT_C_val; exact Hy).
    assert (Hxpx : x ≈ P[x]) by (apply MKT146; apply MKT153; exact Hx).
    assert (Hypy : y ≈ P[y]) by (apply MKT146; apply MKT153; exact Hy).
    assert (Hpxpy : P[x] ≈ P[y]).
    { apply (MKT147 x P[x] P[y]).
      - exact (MKT146 Hxpx).
      - apply (MKT147 y x P[y]).
        + exact Hxy.
        + exact Hypy. }
    exact (MKT_card_eq (P[x]) (P[y]) HpxC HpyC Hpxpy).
Qed.

Theorem MKT155 : ∀ x, P[P[x]] = P[x].
Proof.
  intros x.
  destruct (classic (Ensemble x)) as [Hx | Hnx].
  - assert (HpxC : P[x] ∈ C) by (apply MKT_C_val; exact Hx).
    assert (HpxR : P[x] ∈ R) by (apply MKT_C_R; exact HpxC).
    assert (HpxE : Ensemble (P[x])).
    { exact (MKT_C_Ens (P[x]) HpxC). }
    exact (proj2 (MKT154 (P[x]) x HpxE Hx) (MKT153 Hx)).
  - assert (Hxmu : x ∉ μ) by (intro H; apply Hnx; apply MKT19a; exact H).
    rewrite <- MKT152b in Hxmu.
    assert (Hpx : P[x] = μ) by (apply (MKT69a (x:=x) (f:=P)); exact Hxmu).
    rewrite Hpx.
    assert (Hnxpx : ~ Ensemble (P[x])).
    { rewrite Hpx. exact MKT39. }
    assert (Hpxmu : P[x] ∉ μ) by (intro H; apply Hnxpx; apply MKT19a; exact H).
    rewrite <- MKT152b in Hpxmu.
    assert (Hppx : P[P[x]] = μ) by (apply (MKT69a (x:=P[x]) (f:=P)); exact Hpxmu).
    rewrite Hpx in Hppx.
    exact Hppx.
Qed.

Theorem MKT156 : ∀ x, (Ensemble x /\ P[x] = x) <-> x∈C.
Proof.
  intros x; split.
  - intros [Hx Hpx].
    assert (HpxC : P[x] ∈ C) by (apply MKT_C_val; exact Hx).
    rewrite Hpx in HpxC.
    exact HpxC.
  - intros HxC.
    assert (HxE : Ensemble x) by (apply MKT_C_Ens; exact HxC).
    assert (HpxC : P[x] ∈ C) by (apply MKT_C_val; exact HxE).
    assert (Hpxx : P[x] ≈ x) by (apply MKT153; exact HxE).
    assert (Hpxx' : P[x] = x) by (apply (MKT_card_eq (P[x]) x HpxC HxC Hpxx)).
    split; [exact HxE | exact Hpxx'].
Qed.

(* 辅助引理：Cantor-Bernstein（复制自 MKT159，供 MKT157/158 使用） *)
Lemma MKT_CB : ∀ x y u v, Ensemble x -> Ensemble y
  -> u ⊂ x -> v ⊂ y -> x ≈ v -> y ≈ u -> x ≈ y.
Proof.
  intros x y u v Hex Hey Hu Hv Hxv Hyu.
  destruct Hxv as [f [Hf11 [Hfdom Hfran]]].
  destruct Hyu as [g [Hg11 [Hgdom Hgran]]].
  destruct Hf11 as [Hf Hfinv].
  destruct Hg11 as [Hg Hginv].

  set (fimg := fun S : Class => \{ λ z, ∃ t, t ∈ S /\ [t,z] ∈ f \}).
  set (gimg := fun W : Class => \{ λ z, ∃ w, w ∈ W /\ [w,z] ∈ g \}).
  set (Phi := fun S : Class => x ~ gimg (y ~ fimg S)).
  set (T := \{ λ t, t ∈ x /\ ∀ S : Class, (∀ z, z ∈ Phi S -> z ∈ S) -> t ∈ S \}).

  assert (Hfimg_mono : ∀ S S', S ⊂ S' -> fimg S ⊂ fimg S').
  { intros S S' HSS' z Hz.
    apply AxiomII in Hz as [Ez [t [HtS Htz]]].
    apply AxiomII; split; [exact Ez | exists t; split; [exact (HSS' t HtS) | exact Htz]]. }

  assert (Hgimg_mono : ∀ W W', W ⊂ W' -> gimg W ⊂ gimg W').
  { intros W W' HWW' z Hz.
    apply AxiomII in Hz as [Ez [w [HwW Hwz]]].
    apply AxiomII; split; [exact Ez | exists w; split; [exact (HWW' w HwW) | exact Hwz]]. }

  assert (HPhi_mono : ∀ S S', S ⊂ S' -> Phi S ⊂ Phi S').
  { intros S S' HSS' t Ht.
    apply AxiomII in Ht as [Et [Htx HtC]].
    apply AxiomII in HtC as [Et' Htnot].
    apply AxiomII; split; [exact Et | split; [exact Htx |]].
    apply AxiomII; split; [exact Et' |].
    intro Ht2.
    apply Htnot.
    apply AxiomII in Ht2 as [Et2 Ht2'].
    destruct Ht2' as [w [Hw Hwt]].
    apply AxiomII; split; [exact Et2 | exists w; split; [| exact Hwt]].
    apply AxiomII in Hw as [Ew [Hwy HwC]].
    apply AxiomII in HwC as [Ew' Hwnot].
    apply AxiomII; split; [exact Ew | split; [exact Hwy |]].
    apply AxiomII; split; [exact Ew' |].
    intro Hw2.
    apply Hwnot.
    apply AxiomII in Hw2 as [Ew2 Hw2'].
    destruct Hw2' as [t' [Ht'S Ht'w]].
    apply AxiomII; split; [exact Ew2 | exists t'; split; [exact (HSS' t' Ht'S) | exact Ht'w]]. }

  (* T ⊆ x *)
  assert (HTx : T ⊂ x).
  { intros t Ht. apply AxiomII in Ht as [E [Htx _]]. exact Htx. }

  (* Phi T ⊆ T *)
  assert (HPhiT_T : Phi T ⊂ T).
  { intros t Ht.
    apply AxiomII; split.
    - apply AxiomII in Ht as [Et [Htx _]]. exact Et.
    - split.
      + apply AxiomII in Ht as [Et [Htx _]]. exact Htx.
      + intros S HS.
        assert (HTS : T ⊂ S).
        { intros t0 Ht0. apply AxiomII in Ht0 as [E0 [Ht0x Hmem0]]. exact (Hmem0 S HS). }
        apply HS.
        apply (HPhi_mono T S HTS). exact Ht. }

  (* T ⊆ Phi T *)
  assert (HT_PhiT : T ⊂ Phi T).
  { intros t Ht.
    apply AxiomII in Ht as [Et [Htx Hmem]].
    assert (Hcl : ∀ z, z ∈ Phi (Phi T) -> z ∈ Phi T).
    { intros z Hz. apply (HPhi_mono (Phi T) T HPhiT_T). exact Hz. }
    exact (Hmem (Phi T) Hcl). }

  assert (HT_eq : T = Phi T).
  { apply (proj1 (MKT27 T (Phi T))). split; [exact HT_PhiT | exact HPhiT_T]. }

  set (h := \{ λ z, ∃ t w, z = [t,w] /\ t ∈ x /\
     ((t ∈ T /\ w = f[t]) \/ (t ∉ T /\ [w,t] ∈ g)) \}).

  assert (h_char : ∀ t w, [t,w] ∈ h ->
    t ∈ x /\ ((t ∈ T /\ w = f[t]) \/ (t ∉ T /\ [w,t] ∈ g))).
  { intros t w Htw.
    apply AxiomII in Htw as [Etw Htw].
    destruct Htw as [t1 [w1 [Hz [Ht1x [Hc | Hc]]]]].
    - assert (Et1w1 : Ensemble ([t1,w1])) by (rewrite <- Hz; exact Etw).
      destruct (MKT49b t1 w1 Et1w1) as [Et1 Ew1].
      assert (Etw0 : Ensemble ([t,w])) by exact Etw.
      destruct (MKT49b t w Etw0) as [Et Ew].
      destruct (proj1 (MKT55 t w t1 w1 Et Ew) Hz) as [Htt1 Hww1].
      subst t1 w1.
      split; [exact Ht1x | left; exact Hc].
    - assert (Et1w1 : Ensemble ([t1,w1])) by (rewrite <- Hz; exact Etw).
      destruct (MKT49b t1 w1 Et1w1) as [Et1 Ew1].
      assert (Etw0 : Ensemble ([t,w])) by exact Etw.
      destruct (MKT49b t w Etw0) as [Et Ew].
      destruct (proj1 (MKT55 t w t1 w1 Et Ew) Hz) as [Htt1 Hww1].
      subst t1 w1.
      split; [exact Ht1x | right; exact Hc]. }

  assert (h_single : ∀ t w1 w2, [t,w1] ∈ h -> [t,w2] ∈ h -> w1 = w2).
  { intros t w1 w2 H1 H2.
    pose proof (h_char t w1 H1) as [Htx Hc1].
    pose proof (h_char t w2 H2) as [Htx' Hc2].
    destruct Hc1 as [Hc1 | Hc1'].
    - destruct Hc2 as [Hc2 | Hc2'].
      + destruct Hc1 as [HtT Hw1']. destruct Hc2 as [HtT' Hw2']. rewrite Hw1'. symmetry. exact Hw2'.
      + destruct Hc1 as [HtT Hw1']. destruct Hc2' as [Htnot Hw2t]. exfalso. exact (Htnot HtT).
    - destruct Hc2 as [Hc2 | Hc2'].
      + destruct Hc1' as [Htnot Hw1t]. destruct Hc2 as [HtT Hw2']. exfalso. exact (Htnot HtT).
      + destruct Hc1' as [Htnot Hw1t]. destruct Hc2' as [Htnot' Hw2t].
        assert (Etw1 : Ensemble ([t,w1])) by (unfold Ensemble; exists h; exact H1).
        destruct (MKT49b t w1 Etw1) as [Et Ew1].
        assert (Etw2 : Ensemble ([t,w2])) by (unfold Ensemble; exists h; exact H2).
        destruct (MKT49b t w2 Etw2) as [Et' Ew2].
        apply (proj2 Hginv t w1 w2).
        * apply (proj2 (MKT_inv_in g t w1 Et Ew1)); exact Hw1t.
        * apply (proj2 (MKT_inv_in g t w2 Et' Ew2)); exact Hw2t. }

  assert (h_func : Function h).
  { split.
    - intros z Hz. apply AxiomII in Hz as [E Hz]. destruct Hz as [t [w [Hzw _]]]. exists t; exists w; exact Hzw.
    - exact h_single. }

  assert (h_dom : dom(h) = x).
  { apply AxiomI; intros t; split.
    - intros Ht.
      apply AxiomII in Ht as [Et Ht].
      destruct Ht as [w Htw].
      pose proof (h_char t w Htw) as [Htx _]. exact Htx.
    - intros Htx.
      assert (Et : Ensemble t) by (unfold Ensemble; eauto).
      apply AxiomII; split; [exact Et |].
      destruct (classic (t ∈ T)) as [HtT | Htnot].
      + assert (Htd : t ∈ dom(f)) by (rewrite Hfdom; exact Htx).
        assert (Htf : [t, f[t]] ∈ f) by (apply (MKT_dom_val f t Hf); exact Htd).
        assert (Etft : Ensemble ([t, f[t]])).
        { unfold Ensemble; exists f; exact Htf. }
        exists (f[t]).
        apply AxiomII; split; [exact Etft |].
        exists t; exists (f[t]); split; [reflexivity |].
        split; [exact Htx | left; split; [exact HtT | reflexivity]].
      + assert (Ht_Phi : ~ (t ∈ (Phi T))).
        { intro Htp. apply Htnot. rewrite HT_eq. exact Htp. }
        assert (Htg : t ∈ gimg (y ~ fimg T)).
        { apply NNPP; intro Hn.
          apply Ht_Phi.
          apply AxiomII; split; [exact Et | split; [exact Htx | apply AxiomII; split; [exact Et | exact Hn]]]. }
        apply AxiomII in Htg as [Etg Htg].
        destruct Htg as [w [Hw Hwt]].
        assert (Ewt : Ensemble ([w,t])) by (unfold Ensemble; exists g; exact Hwt).
        destruct (MKT49b w t Ewt) as [Ew Et'].
        assert (Etw : Ensemble ([t,w])) by (apply MKT49a; assumption).
        exists w.
        apply AxiomII; split; [exact Etw |].
        exists t; exists w; split; [reflexivity |].
        split; [exact Htx | right; split; [exact Htnot | exact Hwt]]. }

  assert (h_inj : ∀ t1 t2 w, [t1,w] ∈ h -> [t2,w] ∈ h -> t1 = t2).
  { intros t1 t2 w H1 H2.
    pose proof (h_char t1 w H1) as [Ht1x Hc1].
    pose proof (h_char t2 w H2) as [Ht2x Hc2].
    destruct Hc1 as [Hc1 | Hc1'].
    - destruct Hc2 as [Hc2 | Hc2'].
      + destruct Hc1 as [Ht1T Hw1']. destruct Hc2 as [Ht2T Hw2'].
        assert (Et1w : Ensemble ([t1,w])) by (unfold Ensemble; exists h; exact H1).
        destruct (MKT49b t1 w Et1w) as [Et1 Ew].
        assert (Et2w : Ensemble ([t2,w])) by (unfold Ensemble; exists h; exact H2).
        destruct (MKT49b t2 w Et2w) as [Et2 Ew'].
        apply (proj2 Hfinv w t1 t2).
        * apply (proj2 (MKT_inv_in f w t1 Ew Et1)).
          rewrite Hw1'. apply (MKT_dom_val f t1 Hf). rewrite Hfdom. exact (HTx t1 Ht1T).
        * apply (proj2 (MKT_inv_in f w t2 Ew' Et2)).
          rewrite Hw2'. apply (MKT_dom_val f t2 Hf). rewrite Hfdom. exact (HTx t2 Ht2T).
      + destruct Hc1 as [Ht1T Hw1']. destruct Hc2' as [Ht2not Hw2t].
        exfalso.
        assert (Et1w : Ensemble ([t1,w])) by (unfold Ensemble; exists h; exact H1).
        destruct (MKT49b t1 w Et1w) as [Et1 Ew].
        assert (Hw_fimg : w ∈ fimg T).
        { apply AxiomII; split; [exact Ew |].
          exists t1; split; [exact Ht1T |].
          rewrite Hw1'. apply (MKT_dom_val f t1 Hf). rewrite Hfdom. exact (HTx t1 Ht1T). }
        assert (Et2 : Ensemble t2).
        { assert (Et2w : Ensemble ([t2,w])) by (unfold Ensemble; exists h; exact H2).
          exact (proj1 (MKT49b t2 w Et2w)). }
        assert (Ht2g : t2 ∈ gimg (y ~ fimg T)).
        { apply NNPP; intro Hn.
          apply Ht2not.
          rewrite HT_eq.
          apply AxiomII; split; [exact Et2 | split; [exact Ht2x | apply AxiomII; split; [exact Et2 | exact Hn]]]. }
        apply AxiomII in Ht2g as [Et2g Ht2g].
        destruct Ht2g as [w0 [Hw0 Hw0t2]].
        assert (Ew0t2 : Ensemble ([w0,t2])) by (unfold Ensemble; exists g; exact Hw0t2).
        destruct (MKT49b w0 t2 Ew0t2) as [Ew0 Et2'].
        assert (Hww' : w = w0).
        { apply (proj2 Hginv t2 w w0).
          - apply (proj2 (MKT_inv_in g t2 w Et2' Ew)); exact Hw2t.
          - apply (proj2 (MKT_inv_in g t2 w0 Et2' Ew0)); exact Hw0t2. }
        apply AxiomII in Hw0 as [Ew0a [Hw0y Hw0C]].
        apply AxiomII in Hw0C as [Ew0b Hw0not].
        apply Hw0not. rewrite <- Hww'. exact Hw_fimg.
    - destruct Hc2 as [Hc2 | Hc2'].
      + destruct Hc1' as [Ht1not Hw1t]. destruct Hc2 as [Ht2T Hw2'].
        exfalso.
        assert (Et2w : Ensemble ([t2,w])) by (unfold Ensemble; exists h; exact H2).
        destruct (MKT49b t2 w Et2w) as [Et2 Ew].
        assert (Hw_fimg : w ∈ fimg T).
        { apply AxiomII; split; [exact Ew |].
          exists t2; split; [exact Ht2T |].
          rewrite Hw2'. apply (MKT_dom_val f t2 Hf). rewrite Hfdom. exact (HTx t2 Ht2T). }
        assert (Et1 : Ensemble t1).
        { assert (Et1w : Ensemble ([t1,w])) by (unfold Ensemble; exists h; exact H1).
          exact (proj1 (MKT49b t1 w Et1w)). }
        assert (Ht1g : t1 ∈ gimg (y ~ fimg T)).
        { apply NNPP; intro Hn.
          apply Ht1not.
          rewrite HT_eq.
          apply AxiomII; split; [exact Et1 | split; [exact Ht1x | apply AxiomII; split; [exact Et1 | exact Hn]]]. }
        apply AxiomII in Ht1g as [Et1g Ht1g].
        destruct Ht1g as [w0 [Hw0 Hw0t1]].
        assert (Ew0t1 : Ensemble ([w0,t1])) by (unfold Ensemble; exists g; exact Hw0t1).
        destruct (MKT49b w0 t1 Ew0t1) as [Ew0 Et1'].
        assert (Hww' : w = w0).
        { apply (proj2 Hginv t1 w w0).
          - apply (proj2 (MKT_inv_in g t1 w Et1' Ew)); exact Hw1t.
          - apply (proj2 (MKT_inv_in g t1 w0 Et1' Ew0)); exact Hw0t1. }
        apply AxiomII in Hw0 as [Ew0a [Hw0y Hw0C]].
        apply AxiomII in Hw0C as [Ew0b Hw0not].
        apply Hw0not. rewrite <- Hww'. exact Hw_fimg.
      + destruct Hc1' as [Ht1not Hw1t]. destruct Hc2' as [Ht2not Hw2t].
        assert (Ew : Ensemble w).
        { assert (Et1w : Ensemble ([t1,w])) by (unfold Ensemble; exists h; exact H1).
          exact (proj2 (MKT49b t1 w Et1w)). }
        assert (Et1 : Ensemble t1).
        { assert (Et1w : Ensemble ([t1,w])) by (unfold Ensemble; exists h; exact H1).
          exact (proj1 (MKT49b t1 w Et1w)). }
        assert (Et2 : Ensemble t2).
        { assert (Et2w : Ensemble ([t2,w])) by (unfold Ensemble; exists h; exact H2).
          exact (proj1 (MKT49b t2 w Et2w)). }
        apply (proj2 Hg w t1 t2).
        * exact Hw1t.
        * exact Hw2t. }

  assert (h_inv_func : Function (h⁻¹)).
  { split.
    - intros z Hz. apply AxiomII in Hz as [E Hz]. destruct Hz as [t [w [Hzw _]]]. exists t; exists w; exact Hzw.
    - intros x0 y0 z Hxy Hxz.
      assert (Ex0y0 : Ensemble ([x0,y0])) by (unfold Ensemble; exists (h⁻¹); exact Hxy).
      destruct (MKT49b x0 y0 Ex0y0) as [Ex0 Ey0].
      assert (Ex0z : Ensemble ([x0,z])) by (unfold Ensemble; exists (h⁻¹); exact Hxz).
      destruct (MKT49b x0 z Ex0z) as [Ex0' Ez].
      assert (Hy0x0 : [y0,x0] ∈ h) by (apply (proj1 (MKT_inv_in h x0 y0 Ex0 Ey0)); exact Hxy).
      assert (Hzx0 : [z,x0] ∈ h) by (apply (proj1 (MKT_inv_in h x0 z Ex0' Ez)); exact Hxz).
      apply (h_inj y0 z x0); assumption. }

  assert (h_11 : Function1_1 h) by (split; assumption).

  assert (h_ran : ran(h) = y).
  { apply AxiomI; intros w; split.
    - intros Hw.
      apply AxiomII in Hw as [Ew Hw].
      destruct Hw as [t Htw].
      pose proof (h_char t w Htw) as [Htx [Hc | Hc]].
      + destruct Hc as [HtT Hw'].
        assert (Htd : t ∈ dom(f)) by (rewrite Hfdom; exact Htx).
        assert (Htf : [t, f[t]] ∈ f) by (apply (MKT_dom_val f t Hf); exact Htd).
        assert (Hwr : w ∈ ran(f)).
        { apply AxiomII; split.
          - assert (Etft : Ensemble ([t, f[t]])) by (unfold Ensemble; exists f; exact Htf).
            rewrite Hw'. exact (proj2 (MKT49b t (f[t]) Etft)).
          - exists t; rewrite Hw'; exact Htf. }
        rewrite Hfran in Hwr. exact (Hv w Hwr).
      + destruct Hc as [Htnot Hwt].
        assert (Ewt : Ensemble ([w,t])) by (unfold Ensemble; exists g; exact Hwt).
        destruct (MKT49b w t Ewt) as [Ew' Et].
        assert (Hwd : w ∈ dom(g)).
        { apply AxiomII; split; [exact Ew' | exists t; exact Hwt]. }
        rewrite Hgdom in Hwd. exact Hwd.
    - intros Hwy.
      assert (Hwd : w ∈ dom(g)) by (rewrite Hgdom; exact Hwy).
      assert (Hgt : [w, g[w]] ∈ g) by (apply (MKT_dom_val g w Hg); exact Hwd).
      assert (Ewg : Ensemble ([w, g[w]])) by (unfold Ensemble; exists g; exact Hgt).
      destruct (MKT49b w (g[w]) Ewg) as [Ew Egw].
      assert (Egwx : g[w] ∈ x).
      { assert (Hgwr : g[w] ∈ ran(g)) by (apply AxiomII; split; [exact Egw | exists w; exact Hgt]).
        rewrite Hgran in Hgwr. exact (Hu (g[w]) Hgwr). }
      destruct (classic (g[w] ∈ T)) as [HgtT | Hgtnot].
      + assert (HgPhi : g[w] ∈ Phi T) by (rewrite <- HT_eq; exact HgtT).
        apply AxiomII in HgPhi as [Eg [Hgx HgC]].
        apply AxiomII in HgC as [Eg' Hgnot].
        assert (Hw_fimg : w ∈ fimg T).
        { apply NNPP; intro Hn.
          apply Hgnot.
          apply AxiomII; split; [exact Eg' | exists w; split; [| exact Hgt]].
          apply AxiomII; split; [exact Ew | split; [exact Hwy | apply AxiomII; split; [exact Ew | exact Hn]]]. }
        apply AxiomII in Hw_fimg as [Ewf Hw_fimg].
        destruct Hw_fimg as [t' [Ht'T Ht'w]].
        assert (Et'w : Ensemble ([t',w])) by (unfold Ensemble; exists f; exact Ht'w).
        destruct (MKT49b t' w Et'w) as [Et' Ew'].
        assert (Ew'x : t' ∈ x) by (exact (HTx t' Ht'T)).
        assert (Hwft' : w = f[t']).
        { symmetry. apply (MKT_fval f t' w Hf); exact Ht'w. }
        apply AxiomII; split; [exact Ew |].
        exists t'.
        apply AxiomII; split; [exact Et'w |].
        exists t'; exists w; split; [reflexivity |].
        split; [exact Ew'x | left; split; [exact Ht'T | exact Hwft']].
      + assert (Egww : Ensemble ([g[w], w])).
        { apply MKT49a; assumption. }
        apply AxiomII; split; [exact Ew |].
        exists (g[w]).
        apply AxiomII; split; [exact Egww |].
        exists (g[w]); exists w; split; [reflexivity |].
        split; [exact Egwx | right; split; [exact Hgtnot | exact Hgt]]. }

  exists h.
  split.
  - exact h_11.
  - split; [exact h_dom | exact h_ran].
Qed.

Lemma MKT_dom_ran_E : ∀ f, Function f -> Ensemble f
  -> Ensemble dom(f) /\ Ensemble ran(f).
Proof.
  intros f Hf HfE.
  assert (Hdom_union : dom(f) ⊂ ∪∪f).
  { intros a Ha.
    apply AxiomII in Ha as [Ea Ha].
    destruct Ha as [b Hab].
    assert (Eab : Ensemble ([a,b])) by (unfold Ensemble; exists f; exact Hab).
    destruct (MKT49b a b Eab) as [Ea' Eb].
    apply AxiomII; split.
    - exact Ea'.
    - exists ([a]); split.
      + apply AxiomII; split; [exact Ea' | intros _; reflexivity].
      + apply AxiomII; split; [apply MKT42; exact Ea' |].
        exists ([a,b]); split.
        * apply (proj2 (MKT46b (MKT42 a Ea') (MKT46a Ea' Eb) ([a]))).
          left. reflexivity.
        * exact Hab. }
  assert (Hran_union : ran(f) ⊂ ∪∪f).
  { intros b Hb.
    apply AxiomII in Hb as [Eb Hb].
    destruct Hb as [a Hab].
    assert (Eab : Ensemble ([a,b])) by (unfold Ensemble; exists f; exact Hab).
    destruct (MKT49b a b Eab) as [Ea Eb'].
    apply AxiomII; split.
    - exact Eb'.
    - exists ([a|b]); split.
      + apply (proj2 (MKT46b Ea Eb' b)).
        right. reflexivity.
      + apply AxiomII; split; [apply MKT46a; [exact Ea | exact Eb'] |].
        exists ([a,b]); split.
        * apply (proj2 (MKT46b (MKT42 a Ea) (MKT46a Ea Eb') ([a|b]))).
          right. reflexivity.
        * exact Hab. }
  split.
  - apply (MKT33 (∪∪f) dom(f) (AxiomVI (∪f) (AxiomVI f HfE)) Hdom_union).
  - apply (MKT33 (∪∪f) ran(f) (AxiomVI (∪f) (AxiomVI f HfE)) Hran_union).
Qed.

Lemma MKT_img : ∀ {f S}, Function1_1 f -> S ⊂ dom(f)
  -> ∃ R, (S ≈ R) /\ R ⊂ ran(f).
Proof.
  intros f S [Hf Hfinv] Hsub.
  set (Img := \{ λ z, ∃ t, t ∈ S /\ [t,z] ∈ f \}).
  assert (HfS : Function (f|(S))) by (apply MKT126a; exact Hf).
  assert (HfS_11 : Function1_1 (f|(S))).
  { split; [exact HfS |].
    unfold Function; split.
    - intros z Hz.
      apply AxiomII in Hz as [Ez Hz].
      destruct Hz as [a [b [Hzb _]]].
      exists a; exists b; exact Hzb.
    - intros a b c0 Hab Hac.
      assert (Eab : Ensemble ([a,b])) by (unfold Ensemble; exists ((f|(S))⁻¹); exact Hab).
      destruct (MKT49b a b Eab) as [Ea Eb].
      assert (Eac : Ensemble ([a,c0])) by (unfold Ensemble; exists ((f|(S))⁻¹); exact Hac).
      destruct (MKT49b a c0 Eac) as [Ea' Ec0].
      assert (Hba : [b,a] ∈ (f|(S))).
      { apply (proj1 (MKT_inv_in (f|(S)) a b Ea Eb)); exact Hab. }
      assert (Hca : [c0,a] ∈ (f|(S))).
      { apply (proj1 (MKT_inv_in (f|(S)) a c0 Ea' Ec0)); exact Hac. }
      unfold Restriction in Hba.
      apply AxiomII in Hba as [Eba [Hba1 _]].
      unfold Restriction in Hca.
      apply AxiomII in Hca as [Eca [Hca1 _]].
      assert (Habf : [a,b] ∈ f⁻¹).
      { apply (proj2 (MKT_inv_in f a b Ea Eb)); exact Hba1. }
      assert (Hacf : [a,c0] ∈ f⁻¹).
      { apply (proj2 (MKT_inv_in f a c0 Ea' Ec0)); exact Hca1. }
      exact (proj2 Hfinv a b c0 Habf Hacf). }
  assert (Hdom : dom(f|(S)) = S).
  { rewrite (MKT126b f S Hf).
    apply (proj2 (MKT30 S (dom(f)))); exact Hsub. }
  assert (Hran : ran(f|(S)) = Img).
  { apply AxiomI; intros z; split.
    - intros Hz.
      apply AxiomII in Hz as [Ez Hz].
      destruct Hz as [a Haz].
      apply AxiomII in Haz as [Eaz Haz].
      destruct Haz as [Haf Hazx].
      apply AxiomII; split; [exact Ez |].
      exists a; split.
      + apply AxiomII in Hazx as [Eaz' Hazx].
        destruct Hazx as [u [v [Huv [Hux Hvmu]]]].
        assert (Eaz0 : Ensemble ([a,z])) by (unfold Ensemble; exists f; exact Haf).
        destruct (MKT49b a z Eaz0) as [Ea Ez'].
        assert (Euv : Ensemble ([u,v])) by (rewrite <- Huv; exact Eaz0).
        destruct (MKT49b u v Euv) as [Eu Ev].
        destruct (proj1 (MKT55 a z u v Ea Ez') Huv) as [Hau Hzv].
        rewrite <- Hau in Hux. exact Hux.
      + exact Haf.
    - intros Hz.
      apply AxiomII in Hz as [Ez Hz].
      destruct Hz as [a [HaS Haf]].
      assert (Eaz : Ensemble ([a,z])) by (unfold Ensemble; exists f; exact Haf).
      destruct (MKT49b a z Eaz) as [Ea Ez'].
      apply AxiomII; split; [exact Ez |].
      exists a.
      apply AxiomII; split.
      * exact Eaz.
      * split; [exact Haf |].
        apply AxiomII; split; [exact Eaz |].
        exists a; exists z; split; [reflexivity | split; [exact HaS | apply MKT19b; exact Ez']]. }
  exists Img; split.
  - exists (f|(S)); split; [exact HfS_11 | split; [exact Hdom | exact Hran]].
  - intros z Hz.
    apply AxiomII in Hz as [Ez Hz].
    destruct Hz as [a [HaS Haf]].
    apply AxiomII; split; [exact Ez | exists a; exact Haf].
Qed.

Lemma MKT_sub_inj : ∀ x y z, x ⊂ y -> y ≈ z
  -> ∃ w, w ⊂ z /\ x ≈ w.
Proof.
  intros x y z Hxy [h [Hh11 [Hhdom Hhran]]].
  assert (Hxdom : x ⊂ dom(h)).
  { rewrite Hhdom. exact Hxy. }
  destruct (MKT_img (f:=h) (S:=x) Hh11 Hxdom) as [w [Hxw Hwran]].
  exists w; split.
  - rewrite Hhran in Hwran. exact Hwran.
  - exact Hxw.
Qed.

Lemma MKT_card_le_sub : ∀ κ α, κ ∈ C -> α ∈ R -> (∃ x, x ⊂ α /\ κ ≈ x) -> κ ≼ α.
Proof.
  intros κ α Hκ Hα [x [Hxα Hκx]].
  assert (Hκord : Ordinal κ) by (apply MKT_C_ord; exact Hκ).
  pose proof (proj1 (AxiomII α Ordinal) Hα) as [Eα Hαord].
  destruct (MKT110 Hκord Hαord) as [Hκα | [Hακ | Hκeq]].
  - left; exact Hκα.
  - exfalso.
    pose proof (proj1 (AxiomII κ (λ x, Cardinal_Number x)) Hκ) as [Eκ Hκcard].
    destruct Hκcard as [_ Hκnot].
    apply (Hκnot α Hα Hακ).
    assert (Eκ' : Ensemble κ) by (exact (MKT_C_Ens κ Hκ)).
    assert (Hακ_sub : α ⊂ κ) by (exact (proj2 Hκord α Hακ)).
    assert (Hαα : α ≈ α) by (apply MKT145).
    exact (MKT_CB κ α α x Eκ' Eα Hακ_sub Hxα Hκx Hαα).
  - right; exact Hκeq.
Qed.

Lemma MKT_cantor : ∀ x, Ensemble x -> ~ (x ≈ pow(x)).
Proof.
  intros x Hx H.
  destruct H as [f [Hf11 [Hfdom Hfran]]].
  destruct Hf11 as [Hf Hfinv].
  set (D := \{ λ z, z ∈ x /\ z ∉ f[z] \}).
  assert (HDx : D ⊂ x).
  { intros z Hz. apply AxiomII in Hz as [E [Hzx _]]. exact Hzx. }
  assert (HDpow : D ∈ pow(x)).
  { apply AxiomII; split.
    - apply (MKT33 x D Hx HDx).
    - exact HDx. }
  assert (HDran : D ∈ ran(f)).
  { rewrite Hfran. exact HDpow. }
  apply AxiomII in HDran as [ED HDran].
  destruct HDran as [d HdD].
  assert (Hfd : f[d] = D) by (apply (MKT_fval f d D Hf); exact HdD).
  assert (EdD : Ensemble ([d,D])) by (unfold Ensemble; exists f; exact HdD).
  destruct (MKT49b d D EdD) as [Ed ED'].
  assert (Hdx : d ∈ x).
  { rewrite <- Hfdom. apply AxiomII; split; [exact Ed | exists D; exact HdD]. }
  assert (HdnotD : d ∉ D).
  { intro HdD'.
    pose proof HdD' as HdD0.
    apply AxiomII in HdD' as [Ed' [Hdx' Hdnotfd]].
    apply Hdnotfd.
    rewrite Hfd. exact HdD0. }
  assert (HdD'' : d ∈ D).
  { apply AxiomII; split; [exact Ed | split; [exact Hdx |]].
    intro Hdfd.
    apply HdnotD. rewrite <- Hfd. exact Hdfd. }
  exact (HdnotD HdD'').
Qed.

Lemma MKT_surj_inj : ∀ f, Function f -> Ensemble f
  -> ∃ g, Function1_1 g /\ dom(g) = ran(f) /\ ran(g) ⊂ dom(f).
Proof.
  intros f Hf HfE.
  destruct (MKT_dom_ran_E f Hf HfE) as [HdomE HranE].
  destruct AxiomIX as [c [Hcfunc Hcdom]].
  destruct Hcfunc as [Hcf Hcchoice].
  assert (EΦ : Ensemble Φ) by (apply (MKT33 f Φ HfE (MKT26 f))).
  set (fib := fun z => \{ λ a, [a,z] ∈ f \}).
  assert (Hfib_sub : ∀ z, z ∈ ran(f) -> fib z ⊂ dom(f)).
  { intros z Hz a Ha.
    apply AxiomII in Ha as [Ea Haz].
    apply AxiomII; split; [exact Ea | exists z; exact Haz]. }
  assert (HfibE : ∀ z, z ∈ ran(f) -> Ensemble (fib z)).
  { intros z Hz. apply (MKT33 dom(f) (fib z) HdomE (Hfib_sub z Hz)). }
  assert (Hfib_ne : ∀ z, z ∈ ran(f) -> fib z ≠ Φ).
  { intros z Hz HΦ.
    apply AxiomII in Hz as [Ez Hz].
    destruct Hz as [a Haz].
    assert (Hafib : a ∈ fib z).
    { apply AxiomII; split.
      - assert (Eaz : Ensemble ([a,z])) by (unfold Ensemble; exists f; exact Haz).
        exact (proj1 (MKT49b a z Eaz)).
      - exact Haz. }
    rewrite HΦ in Hafib.
    exact (MKT16 Hafib). }
  assert (Hfib_domc : ∀ z, z ∈ ran(f) -> fib z ∈ dom(c)).
  { intros z Hz.
    rewrite Hcdom.
    change (fib z ∈ \{ λ x, x ∈ μ /\ x ∈ ¬ [Φ] \}).
    apply AxiomII; split.
    - exact (HfibE z Hz).
    - split.
      + apply MKT19b; apply (HfibE z Hz).
      + apply AxiomII; split.
        * exact (HfibE z Hz).
        * intro Hsing.
          apply (Hfib_ne z Hz).
          exact (proj1 (MKT41 Φ EΦ (fib z)) Hsing). }
  assert (Hcval : ∀ z, z ∈ ran(f) -> c[fib z] ∈ fib z).
  { intros z Hz. apply Hcchoice. exact (Hfib_domc z Hz). }
  set (g := \{\ λ z a, z ∈ ran(f) /\ a = c[fib z] \}\).
  assert (Hg_func : Function g).
  { split.
    - intros p Hp.
      apply AxiomII in Hp as [Ep Hp].
      destruct Hp as [z [a [Hza _]]].
      exists z; exists a; exact Hza.
    - intros z a1 a2 Hza1 Hza2.
      apply AxiomII in Hza1 as [E1 Hza1].
      apply AxiomII in Hza2 as [E2 Hza2].
      destruct Hza1 as [u [v [H1 [Hzr1 H1v]]]].
      destruct Hza2 as [u' [v' [H2 [Hzr2 H2v]]]].
      assert (Euv : Ensemble ([u,v])) by (rewrite <- H1; exact E1).
      assert (Eu'v' : Ensemble ([u',v'])) by (rewrite <- H2; exact E2).
      destruct (MKT49b u v Euv) as [Eu Ev].
      destruct (MKT49b u' v' Eu'v') as [Eu' Ev'].
      destruct (MKT49b z a1 E1) as [Ez Ea1].
      destruct (MKT49b z a2 E2) as [Ez' Ea2].
      destruct (proj1 (MKT55 z a1 u v Ez Ea1) H1) as [Hzu Hva1].
      destruct (proj1 (MKT55 z a2 u' v' Ez' Ea2) H2) as [Hzu' Hva2].
      assert (Ha1 : a1 = c[fib z]) by (rewrite Hva1; rewrite <- Hzu in H1v; exact H1v).
      assert (Ha2 : a2 = c[fib z]) by (rewrite Hva2; rewrite <- Hzu' in H2v; exact H2v).
      rewrite Ha1. rewrite Ha2. reflexivity. }
  assert (Hg_11 : Function1_1 g).
  { split; [exact Hg_func |].
    unfold Function; split.
    - intros p Hp.
      apply AxiomII in Hp as [Ep Hp].
      destruct Hp as [z [a [Hza _]]].
      exists z; exists a; exact Hza.
    - intros z1 z2 a Hz1a Hz2a.
      apply AxiomII in Hz1a as [E1 Hz1a].
      apply AxiomII in Hz2a as [E2 Hz2a].
      destruct Hz1a as [u [v [H1 H1v]]].
      destruct Hz2a as [u' [v' [H2 H2v]]].
      assert (Euv : Ensemble ([u,v])) by (rewrite <- H1; exact E1).
      assert (Eu'v' : Ensemble ([u',v'])) by (rewrite <- H2; exact E2).
      destruct (MKT49b u v Euv) as [Eu Ev].
      destruct (MKT49b u' v' Eu'v') as [Eu' Ev'].
      destruct (MKT49b z1 z2 E1) as [Ez1 Ez2].
      destruct (MKT49b z1 a E2) as [Ez1' Ea].
      destruct (proj1 (MKT55 z1 z2 u v Ez1 Ez2) H1) as [Hz1u Hz2v].
      destruct (proj1 (MKT55 z1 a u' v' Ez1' Ea) H2) as [Hz1u' Hav'].
      assert (Hg_char : ∀ x y, [x,y] ∈ g -> x ∈ ran(f) /\ y = c[fib x]).
      { intros x y Hxy.
        apply AxiomII in Hxy as [Exy Hxy].
        destruct Hxy as [p [q [Hpq Hpq']]].
        destruct (MKT49b x y Exy) as [Ex Ey].
        assert (Epq : Ensemble ([p,q])) by (rewrite <- Hpq; exact Exy).
        destruct (MKT49b p q Epq) as [Ep Eq].
        destruct (proj1 (MKT55 x y p q Ex Ey) Hpq) as [Hxp Hyq].
        destruct Hpq' as [Hp Hq].
        split.
        - rewrite <- Hxp in Hp. exact Hp.
        - rewrite Hyq. rewrite <- Hxp in Hq. exact Hq. }
      assert (Hz2z1 : [z2,z1] ∈ g).
      { rewrite Hz1u. rewrite Hz2v. exact H1v. }
      assert (Haz1 : [a,z1] ∈ g).
      { rewrite Hz1u'. rewrite Hav'. exact H2v. }
      destruct (Hg_char z2 z1 Hz2z1) as [Hz2r Hz1c].
      destruct (Hg_char a z1 Haz1) as [Har Hac].
      assert (Hc_eq : c[fib z2] = c[fib a]).
      { rewrite <- Hz1c. exact Hac. }
      pose proof (Hcval z2 Hz2r) as Hcval2.
      apply AxiomII in Hcval2 as [Ec2 Hc2].
      pose proof (Hcval a Har) as Hcvala.
      apply AxiomII in Hcvala as [Eca Hca].
      assert (Hc_a_f : [c[fib z2], a] ∈ f).
      { rewrite Hc_eq. exact Hca. }
      apply (proj2 Hf (c[fib z2]) z2 a); assumption. }
  assert (Hg_dom : dom(g) = ran(f)).
  { apply AxiomI; intros z; split.
    - intros Hz.
      apply AxiomII in Hz as [Ez Hz].
      destruct Hz as [a Hza].
      apply AxiomII in Hza as [Ea Hza].
      destruct Hza as [u [v [H1 [Hzr H1v]]]].
      assert (Eza : Ensemble ([z,a])) by exact Ea.
      destruct (MKT49b z a Eza) as [Ez' Ea'].
      assert (Euv : Ensemble ([u,v])) by (rewrite <- H1; exact Eza).
      destruct (MKT49b u v Euv) as [Eu Ev].
      destruct (proj1 (MKT55 z a u v Ez' Ea') H1) as [Hzu Hva].
      assert (Hzr' : z ∈ ran(f)).
      { rewrite <- Hzu in Hzr. exact Hzr. }
      apply AxiomII; split; [exact Ez' |].
      apply AxiomII in Hzr' as [Ez'' Hzr'].
      destruct Hzr' as [x Hxz].
      exists x; exact Hxz.
    - intros Hz.
      apply AxiomII in Hz as [Ez Hz].
      destruct Hz as [a Haz].
      assert (Hzr : z ∈ ran(f)).
      { apply AxiomII; split.
        - exact Ez.
        - exists a; exact Haz. }
      assert (Hcvalz : c[fib z] ∈ fib z) by (apply (Hcval z Hzr)).
      apply AxiomII in Hcvalz as [Ec Hcvalz].
      assert (Epair : Ensemble ([z, c[fib z]])).
      { apply MKT49a; [exact Ez | exact Ec]. }
      apply AxiomII; split; [exact Ez |].
      exists (c[fib z]).
      apply AxiomII; split; [exact Epair |].
      exists z; exists (c[fib z]); split; [reflexivity | split; [exact Hzr | reflexivity]]. }
  assert (Hg_ran : ran(g) ⊂ dom(f)).
  { intros z Hz.
    apply AxiomII in Hz as [Ez Hz].
    destruct Hz as [a Hza].
    apply AxiomII in Hza as [Ea Hza].
    destruct Hza as [u [v [H1 [Hzr H1v]]]].
    assert (Eza : Ensemble ([a,z])) by exact Ea.
    destruct (MKT49b a z Eza) as [Ea' Ez'].
    assert (Euv : Ensemble ([u,v])) by (rewrite <- H1; exact Eza).
    destruct (MKT49b u v Euv) as [Eu Ev].
    destruct (proj1 (MKT55 a z u v Ea' Ez') H1) as [Hau Hzv].
    assert (Hcvalu : c[fib u] ∈ fib u) by (apply (Hcval u Hzr)).
    apply AxiomII in Hcvalu as [Ec Hcvalu].
    assert (Hzc : z = c[fib u]).
    { rewrite Hzv. exact H1v. }
    apply AxiomII; split; [exact Ez' |].
    exists u.
    rewrite <- Hzc in Hcvalu.
    exact Hcvalu. }
  exists g; split; [exact Hg_11 | split; [exact Hg_dom | exact Hg_ran]].
Qed.

Lemma MKT_x_pow : ∀ x, Ensemble x -> ∃ S, S ⊂ pow(x) /\ x ≈ S.
Proof.
  intros x Hx.
  set (s := \{\ λ u v, u ∈ x /\ v = [u] \}\).
  assert (Hs_single : ∀ u v w, [u,v] ∈ s -> [u,w] ∈ s -> v = w).
  { intros u v w Huv Huw.
    apply AxiomII in Huv as [Euv Huv].
    apply AxiomII in Huw as [Euw Huw].
    destruct Huv as [a [b [H1 [Hax H1v]]]].
    destruct Huw as [a' [b' [H2 [Ha'x H2v]]]].
    assert (Eab : Ensemble ([a,b])).
    { rewrite <- H1. exact Euv. }
    assert (Ea'b' : Ensemble ([a',b'])).
    { rewrite <- H2. exact Euw. }
    destruct (MKT49b u v Euv) as [Eu Ev].
    destruct (MKT49b u w Euw) as [Eu' Ew].
    destruct (proj1 (MKT55 u v a b Eu Ev) H1) as [Hau Hbv].
    destruct (proj1 (MKT55 u w a' b' Eu' Ew) H2) as [Ha'u Hb'w].
    assert (Hb : b = [u]) by (rewrite <- Hau in H1v; exact H1v).
    assert (Hb' : b' = [u]) by (rewrite <- Ha'u in H2v; exact H2v).
    assert (Hv : v = b) by (exact (proj2 (proj1 (MKT55 u v a b Eu Ev) H1))).
    assert (Hw : w = b') by (exact (proj2 (proj1 (MKT55 u w a' b' Eu' Ew) H2))).
    rewrite Hv. rewrite Hw. rewrite Hb. rewrite Hb'. reflexivity. }
  assert (Hs_func : Function s).
  { split.
    - intros p Hp.
      apply AxiomII in Hp as [Ep Hp].
      destruct Hp as [u [v [Huv _]]].
      exists u; exists v; exact Huv.
    - exact Hs_single. }
  assert (Hs_inj : ∀ u1 u2 v, [u1,v] ∈ s -> [u2,v] ∈ s -> u1 = u2).
  { intros u1 u2 v H1 H2.
    apply AxiomII in H1 as [E1 H1].
    apply AxiomII in H2 as [E2 H2].
    destruct H1 as [a [b [H1a [H1x H1b]]]].
    destruct H2 as [a' [b' [H2a [H2x H2b]]]].
    assert (Eab : Ensemble ([a,b])).
    { rewrite <- H1a. exact E1. }
    assert (Ea'b' : Ensemble ([a',b'])).
    { rewrite <- H2a. exact E2. }
    destruct (MKT49b u1 v E1) as [Eu1 Ev].
    destruct (MKT49b u2 v E2) as [Eu2 Ev'].
    destruct (proj1 (MKT55 u1 v a b Eu1 Ev) H1a) as [Hu1a Hvb].
    destruct (proj1 (MKT55 u2 v a' b' Eu2 Ev') H2a) as [Hu2a' Hvb'].
    assert (Hb : b = [u1]) by (rewrite <- Hu1a in H1b; exact H1b).
    assert (Hb' : b' = [u2]) by (rewrite <- Hu2a' in H2b; exact H2b).
    assert (Hvu1 : v = [u1]).
    { rewrite Hvb. exact Hb. }
    assert (Hvu2 : v = [u2]).
    { rewrite Hvb'. exact Hb'. }
    assert (Hsing_eq : [u1] = [u2]).
    { rewrite <- Hvu1. rewrite <- Hvu2. reflexivity. }
    assert (Hu1in : u1 ∈ [u2]).
    { rewrite <- Hsing_eq.
      apply (proj2 (MKT41 u1 Eu1 u1)); reflexivity. }
    exact (proj1 (MKT41 u2 Eu2 u1) Hu1in). }
  assert (Hs_inv : Function (s⁻¹)).
  { split.
    - intros p Hp.
      apply AxiomII in Hp as [Ep Hp].
      destruct Hp as [a [b [Hpb _]]].
      exists a; exists b; exact Hpb.
    - intros u1 u2 v Hu1v Hu2v.
      assert (Eu1u2 : Ensemble ([u1,u2])) by (unfold Ensemble; exists (s⁻¹); exact Hu1v).
      destruct (MKT49b u1 u2 Eu1u2) as [Eu1 Eu2].
      assert (Eu1v : Ensemble ([u1,v])) by (unfold Ensemble; exists (s⁻¹); exact Hu2v).
      destruct (MKT49b u1 v Eu1v) as [Eu1' Ev].
      assert (Hu2u1 : [u2,u1] ∈ s).
      { apply (proj1 (MKT_inv_in s u1 u2 Eu1 Eu2)); exact Hu1v. }
      assert (Hvu1 : [v,u1] ∈ s).
      { apply (proj1 (MKT_inv_in s u1 v Eu1' Ev)); exact Hu2v. }
      exact (Hs_inj u2 v u1 Hu2u1 Hvu1). }
  assert (Hs_11 : Function1_1 s) by (split; [exact Hs_func | exact Hs_inv]).
  assert (Hs_dom : dom(s) = x).
  { apply AxiomI; intros u; split.
    - intros Hu.
      apply AxiomII in Hu as [Eu Hu].
      destruct Hu as [v Huv].
      apply AxiomII in Huv as [Ev Huv].
      destruct Huv as [a [b [H1 [Hax H1b]]]].
      assert (Eab : Ensemble ([a,b])) by (rewrite <- H1; exact Ev).
      destruct (MKT49b a b Eab) as [Ea Eb].
      destruct (MKT49b u v Ev) as [Eu' Ev'].
      destruct (proj1 (MKT55 u v a b Eu' Ev') H1) as [Hua Hvb].
      rewrite <- Hua in Hax. exact Hax.
    - intros Hu.
      assert (Eu : Ensemble u) by (unfold Ensemble; exists x; exact Hu).
      assert (Eu' : Ensemble ([u])) by (apply MKT42; exact Eu).
      assert (Euu : Ensemble ([u, [u]])) by (apply MKT49a; assumption).
      apply AxiomII; split; [exact Eu |].
      exists ([u]).
      apply AxiomII; split; [exact Euu |].
      exists u; exists ([u]); split; [reflexivity | split; [exact Hu | reflexivity]]. }
  assert (Hs_ran : ran(s) ⊂ pow(x)).
  { intros v Hv.
    apply AxiomII in Hv as [Ev Hv].
    destruct Hv as [u Huv].
    apply AxiomII in Huv as [Euv Huv].
    destruct Huv as [a [b [H1 [Hax H1b]]]].
    assert (Eab : Ensemble ([a,b])) by (rewrite <- H1; exact Euv).
    destruct (MKT49b a b Eab) as [Ea Eb].
    destruct (MKT49b u v Euv) as [Eu Ev'].
    destruct (proj1 (MKT55 u v a b Eu Ev') H1) as [Hua Hvb].
    assert (Hux : u ∈ x) by (rewrite <- Hua in Hax; exact Hax).
    assert (Hb : b = [u]) by (rewrite <- Hua in H1b; exact H1b).
    assert (Hv_sing : v = [u]) by (rewrite Hvb; exact Hb).
    apply AxiomII; split.
    + rewrite Hv_sing. apply MKT42. exact Eu.
    + rewrite Hv_sing. intros w Hw.
      apply (proj1 (MKT41 u Eu w)) in Hw.
      rewrite Hw. exact Hux. }
  exists (ran(s)).
  split.
  - exact Hs_ran.
  - exists s; split; [exact Hs_11 | split; [exact Hs_dom | reflexivity]].
Qed.

Theorem MKT157 : ∀ x y, y ∈ R -> x ⊂ y -> P[x] ≼ y.
Proof.
  intros x y HyR Hxy.
  pose proof (proj1 (AxiomII y Ordinal) HyR) as [Ey Hoy].
  assert (Hx : Ensemble x) by (apply (MKT33 y x Ey Hxy)).
  assert (HpxC : P[x] ∈ C) by (apply MKT_C_val; exact Hx).
  apply (MKT_card_le_sub P[x] y HpxC HyR).
  exists x; split; [exact Hxy | exact (MKT153 Hx)].
Qed.

Theorem MKT158 : ∀ {x y}, x ⊂ y -> P[x] ≼ P[y].
Proof.
  intros x y Hxy.
  destruct (classic (Ensemble x)) as [Hx | Hnx].
  - destruct (classic (Ensemble y)) as [Hy | Hny].
    + assert (HpxC : P[x] ∈ C) by (apply MKT_C_val; exact Hx).
      assert (HpyC : P[y] ∈ C) by (apply MKT_C_val; exact Hy).
      assert (HpyR : P[y] ∈ R) by (apply MKT_C_R; exact HpyC).
      destruct (MKT_sub_inj x y (P[y]) Hxy
        (MKT146 (MKT153 Hy))) as [w [HwP Hxw]].
      assert (Hpxw : P[x] ≈ w).
      { apply (MKT147 x (P[x]) w (MKT153 Hx) Hxw). }
      apply (MKT_card_le_sub P[x] P[y] HpxC HpyR).
      exists w; split; [exact HwP | exact Hpxw].
    + assert (Hpy : P[y] = μ).
      { apply (MKT69a (x:=y) (f:=P)).
        intro Hyy.
        apply Hny.
        apply MKT19a.
        rewrite MKT152b in Hyy.
        exact Hyy. }
      rewrite Hpy.
      left. apply MKT19b. apply (MKT_C_Ens (P[x]) (MKT_C_val x Hx)).
  - assert (Hpx : P[x] = μ).
    { apply (MKT69a (x:=x) (f:=P)).
      intro Hxx.
      apply Hnx.
      apply MKT19a.
      rewrite MKT152b in Hxx.
      exact Hxx. }
    assert (Hny : ~ Ensemble y).
    { intro Hy. apply Hnx. exact (MKT33 y x Hy Hxy). }
    assert (Hpy : P[y] = μ).
    { apply (MKT69a (x:=y) (f:=P)).
      intro Hyy. apply Hny. apply MKT19a. rewrite MKT152b in Hyy. exact Hyy. }
    rewrite Hpx. rewrite Hpy. right. reflexivity.
Qed.

Theorem MKT159 : ∀ x y u v, Ensemble x -> Ensemble y
  -> u ⊂ x -> v ⊂ y -> x ≈ v -> y ≈ u -> x ≈ y.
Proof.
  intros x y u v Hex Hey Hu Hv Hxv Hyu.
  destruct Hxv as [f [Hf11 [Hfdom Hfran]]].
  destruct Hyu as [g [Hg11 [Hgdom Hgran]]].
  destruct Hf11 as [Hf Hfinv].
  destruct Hg11 as [Hg Hginv].

  set (fimg := fun S : Class => \{ λ z, ∃ t, t ∈ S /\ [t,z] ∈ f \}).
  set (gimg := fun W : Class => \{ λ z, ∃ w, w ∈ W /\ [w,z] ∈ g \}).
  set (Phi := fun S : Class => x ~ gimg (y ~ fimg S)).
  set (T := \{ λ t, t ∈ x /\ ∀ S : Class, (∀ z, z ∈ Phi S -> z ∈ S) -> t ∈ S \}).

  assert (Hfimg_mono : ∀ S S', S ⊂ S' -> fimg S ⊂ fimg S').
  { intros S S' HSS' z Hz.
    apply AxiomII in Hz as [Ez [t [HtS Htz]]].
    apply AxiomII; split; [exact Ez | exists t; split; [exact (HSS' t HtS) | exact Htz]]. }

  assert (Hgimg_mono : ∀ W W', W ⊂ W' -> gimg W ⊂ gimg W').
  { intros W W' HWW' z Hz.
    apply AxiomII in Hz as [Ez [w [HwW Hwz]]].
    apply AxiomII; split; [exact Ez | exists w; split; [exact (HWW' w HwW) | exact Hwz]]. }

  assert (HPhi_mono : ∀ S S', S ⊂ S' -> Phi S ⊂ Phi S').
  { intros S S' HSS' t Ht.
    apply AxiomII in Ht as [Et [Htx HtC]].
    apply AxiomII in HtC as [Et' Htnot].
    apply AxiomII; split; [exact Et | split; [exact Htx |]].
    apply AxiomII; split; [exact Et' |].
    intro Ht2.
    apply Htnot.
    apply AxiomII in Ht2 as [Et2 Ht2'].
    destruct Ht2' as [w [Hw Hwt]].
    apply AxiomII; split; [exact Et2 | exists w; split; [| exact Hwt]].
    apply AxiomII in Hw as [Ew [Hwy HwC]].
    apply AxiomII in HwC as [Ew' Hwnot].
    apply AxiomII; split; [exact Ew | split; [exact Hwy |]].
    apply AxiomII; split; [exact Ew' |].
    intro Hw2.
    apply Hwnot.
    apply AxiomII in Hw2 as [Ew2 Hw2'].
    destruct Hw2' as [t' [Ht'S Ht'w]].
    apply AxiomII; split; [exact Ew2 | exists t'; split; [exact (HSS' t' Ht'S) | exact Ht'w]]. }

  (* T ⊆ x *)
  assert (HTx : T ⊂ x).
  { intros t Ht. apply AxiomII in Ht as [E [Htx _]]. exact Htx. }

  (* Phi T ⊆ T *)
  assert (HPhiT_T : Phi T ⊂ T).
  { intros t Ht.
    apply AxiomII; split.
    - apply AxiomII in Ht as [Et [Htx _]]. exact Et.
    - split.
      + apply AxiomII in Ht as [Et [Htx _]]. exact Htx.
      + intros S HS.
        assert (HTS : T ⊂ S).
        { intros t0 Ht0. apply AxiomII in Ht0 as [E0 [Ht0x Hmem0]]. exact (Hmem0 S HS). }
        apply HS.
        apply (HPhi_mono T S HTS). exact Ht. }

  (* T ⊆ Phi T *)
  assert (HT_PhiT : T ⊂ Phi T).
  { intros t Ht.
    apply AxiomII in Ht as [Et [Htx Hmem]].
    assert (Hcl : ∀ z, z ∈ Phi (Phi T) -> z ∈ Phi T).
    { intros z Hz. apply (HPhi_mono (Phi T) T HPhiT_T). exact Hz. }
    exact (Hmem (Phi T) Hcl). }

  assert (HT_eq : T = Phi T).
  { apply (proj1 (MKT27 T (Phi T))). split; [exact HT_PhiT | exact HPhiT_T]. }

  set (h := \{ λ z, ∃ t w, z = [t,w] /\ t ∈ x /\
     ((t ∈ T /\ w = f[t]) \/ (t ∉ T /\ [w,t] ∈ g)) \}).

  assert (h_char : ∀ t w, [t,w] ∈ h ->
    t ∈ x /\ ((t ∈ T /\ w = f[t]) \/ (t ∉ T /\ [w,t] ∈ g))).
  { intros t w Htw.
    apply AxiomII in Htw as [Etw Htw].
    destruct Htw as [t1 [w1 [Hz [Ht1x [Hc | Hc]]]]].
    - assert (Et1w1 : Ensemble ([t1,w1])) by (rewrite <- Hz; exact Etw).
      destruct (MKT49b t1 w1 Et1w1) as [Et1 Ew1].
      assert (Etw0 : Ensemble ([t,w])) by exact Etw.
      destruct (MKT49b t w Etw0) as [Et Ew].
      destruct (proj1 (MKT55 t w t1 w1 Et Ew) Hz) as [Htt1 Hww1].
      subst t1 w1.
      split; [exact Ht1x | left; exact Hc].
    - assert (Et1w1 : Ensemble ([t1,w1])) by (rewrite <- Hz; exact Etw).
      destruct (MKT49b t1 w1 Et1w1) as [Et1 Ew1].
      assert (Etw0 : Ensemble ([t,w])) by exact Etw.
      destruct (MKT49b t w Etw0) as [Et Ew].
      destruct (proj1 (MKT55 t w t1 w1 Et Ew) Hz) as [Htt1 Hww1].
      subst t1 w1.
      split; [exact Ht1x | right; exact Hc]. }

  assert (h_single : ∀ t w1 w2, [t,w1] ∈ h -> [t,w2] ∈ h -> w1 = w2).
  { intros t w1 w2 H1 H2.
    pose proof (h_char t w1 H1) as [Htx Hc1].
    pose proof (h_char t w2 H2) as [Htx' Hc2].
    destruct Hc1 as [Hc1 | Hc1'].
    - destruct Hc2 as [Hc2 | Hc2'].
      + destruct Hc1 as [HtT Hw1']. destruct Hc2 as [HtT' Hw2']. rewrite Hw1'. symmetry. exact Hw2'.
      + destruct Hc1 as [HtT Hw1']. destruct Hc2' as [Htnot Hw2t]. exfalso. exact (Htnot HtT).
    - destruct Hc2 as [Hc2 | Hc2'].
      + destruct Hc1' as [Htnot Hw1t]. destruct Hc2 as [HtT Hw2']. exfalso. exact (Htnot HtT).
      + destruct Hc1' as [Htnot Hw1t]. destruct Hc2' as [Htnot' Hw2t].
        assert (Etw1 : Ensemble ([t,w1])) by (unfold Ensemble; exists h; exact H1).
        destruct (MKT49b t w1 Etw1) as [Et Ew1].
        assert (Etw2 : Ensemble ([t,w2])) by (unfold Ensemble; exists h; exact H2).
        destruct (MKT49b t w2 Etw2) as [Et' Ew2].
        apply (proj2 Hginv t w1 w2).
        * apply (proj2 (MKT_inv_in g t w1 Et Ew1)); exact Hw1t.
        * apply (proj2 (MKT_inv_in g t w2 Et' Ew2)); exact Hw2t. }

  assert (h_func : Function h).
  { split.
    - intros z Hz. apply AxiomII in Hz as [E Hz]. destruct Hz as [t [w [Hzw _]]]. exists t; exists w; exact Hzw.
    - exact h_single. }

  assert (h_dom : dom(h) = x).
  { apply AxiomI; intros t; split.
    - intros Ht.
      apply AxiomII in Ht as [Et Ht].
      destruct Ht as [w Htw].
      pose proof (h_char t w Htw) as [Htx _]. exact Htx.
    - intros Htx.
      assert (Et : Ensemble t) by (unfold Ensemble; eauto).
      apply AxiomII; split; [exact Et |].
      destruct (classic (t ∈ T)) as [HtT | Htnot].
      + assert (Htd : t ∈ dom(f)) by (rewrite Hfdom; exact Htx).
        assert (Htf : [t, f[t]] ∈ f) by (apply (MKT_dom_val f t Hf); exact Htd).
        assert (Etft : Ensemble ([t, f[t]])).
        { unfold Ensemble; exists f; exact Htf. }
        exists (f[t]).
        apply AxiomII; split; [exact Etft |].
        exists t; exists (f[t]); split; [reflexivity |].
        split; [exact Htx | left; split; [exact HtT | reflexivity]].
      + assert (Ht_Phi : ~ (t ∈ (Phi T))).
        { intro Htp. apply Htnot. rewrite HT_eq. exact Htp. }
        assert (Htg : t ∈ gimg (y ~ fimg T)).
        { apply NNPP; intro Hn.
          apply Ht_Phi.
          apply AxiomII; split; [exact Et | split; [exact Htx | apply AxiomII; split; [exact Et | exact Hn]]]. }
        apply AxiomII in Htg as [Etg Htg].
        destruct Htg as [w [Hw Hwt]].
        assert (Ewt : Ensemble ([w,t])) by (unfold Ensemble; exists g; exact Hwt).
        destruct (MKT49b w t Ewt) as [Ew Et'].
        assert (Etw : Ensemble ([t,w])) by (apply MKT49a; assumption).
        exists w.
        apply AxiomII; split; [exact Etw |].
        exists t; exists w; split; [reflexivity |].
        split; [exact Htx | right; split; [exact Htnot | exact Hwt]]. }

  assert (h_inj : ∀ t1 t2 w, [t1,w] ∈ h -> [t2,w] ∈ h -> t1 = t2).
  { intros t1 t2 w H1 H2.
    pose proof (h_char t1 w H1) as [Ht1x Hc1].
    pose proof (h_char t2 w H2) as [Ht2x Hc2].
    destruct Hc1 as [Hc1 | Hc1'].
    - destruct Hc2 as [Hc2 | Hc2'].
      + destruct Hc1 as [Ht1T Hw1']. destruct Hc2 as [Ht2T Hw2'].
        assert (Et1w : Ensemble ([t1,w])) by (unfold Ensemble; exists h; exact H1).
        destruct (MKT49b t1 w Et1w) as [Et1 Ew].
        assert (Et2w : Ensemble ([t2,w])) by (unfold Ensemble; exists h; exact H2).
        destruct (MKT49b t2 w Et2w) as [Et2 Ew'].
        apply (proj2 Hfinv w t1 t2).
        * apply (proj2 (MKT_inv_in f w t1 Ew Et1)).
          rewrite Hw1'. apply (MKT_dom_val f t1 Hf). rewrite Hfdom. exact (HTx t1 Ht1T).
        * apply (proj2 (MKT_inv_in f w t2 Ew' Et2)).
          rewrite Hw2'. apply (MKT_dom_val f t2 Hf). rewrite Hfdom. exact (HTx t2 Ht2T).
      + destruct Hc1 as [Ht1T Hw1']. destruct Hc2' as [Ht2not Hw2t].
        exfalso.
        assert (Et1w : Ensemble ([t1,w])) by (unfold Ensemble; exists h; exact H1).
        destruct (MKT49b t1 w Et1w) as [Et1 Ew].
        assert (Hw_fimg : w ∈ fimg T).
        { apply AxiomII; split; [exact Ew |].
          exists t1; split; [exact Ht1T |].
          rewrite Hw1'. apply (MKT_dom_val f t1 Hf). rewrite Hfdom. exact (HTx t1 Ht1T). }
        assert (Et2 : Ensemble t2).
        { assert (Et2w : Ensemble ([t2,w])) by (unfold Ensemble; exists h; exact H2).
          exact (proj1 (MKT49b t2 w Et2w)). }
        assert (Ht2g : t2 ∈ gimg (y ~ fimg T)).
        { apply NNPP; intro Hn.
          apply Ht2not.
          rewrite HT_eq.
          apply AxiomII; split; [exact Et2 | split; [exact Ht2x | apply AxiomII; split; [exact Et2 | exact Hn]]]. }
        apply AxiomII in Ht2g as [Et2g Ht2g].
        destruct Ht2g as [w0 [Hw0 Hw0t2]].
        assert (Ew0t2 : Ensemble ([w0,t2])) by (unfold Ensemble; exists g; exact Hw0t2).
        destruct (MKT49b w0 t2 Ew0t2) as [Ew0 Et2'].
        assert (Hww' : w = w0).
        { apply (proj2 Hginv t2 w w0).
          - apply (proj2 (MKT_inv_in g t2 w Et2' Ew)); exact Hw2t.
          - apply (proj2 (MKT_inv_in g t2 w0 Et2' Ew0)); exact Hw0t2. }
        apply AxiomII in Hw0 as [Ew0a [Hw0y Hw0C]].
        apply AxiomII in Hw0C as [Ew0b Hw0not].
        apply Hw0not. rewrite <- Hww'. exact Hw_fimg.
    - destruct Hc2 as [Hc2 | Hc2'].
      + destruct Hc1' as [Ht1not Hw1t]. destruct Hc2 as [Ht2T Hw2'].
        exfalso.
        assert (Et2w : Ensemble ([t2,w])) by (unfold Ensemble; exists h; exact H2).
        destruct (MKT49b t2 w Et2w) as [Et2 Ew].
        assert (Hw_fimg : w ∈ fimg T).
        { apply AxiomII; split; [exact Ew |].
          exists t2; split; [exact Ht2T |].
          rewrite Hw2'. apply (MKT_dom_val f t2 Hf). rewrite Hfdom. exact (HTx t2 Ht2T). }
        assert (Et1 : Ensemble t1).
        { assert (Et1w : Ensemble ([t1,w])) by (unfold Ensemble; exists h; exact H1).
          exact (proj1 (MKT49b t1 w Et1w)). }
        assert (Ht1g : t1 ∈ gimg (y ~ fimg T)).
        { apply NNPP; intro Hn.
          apply Ht1not.
          rewrite HT_eq.
          apply AxiomII; split; [exact Et1 | split; [exact Ht1x | apply AxiomII; split; [exact Et1 | exact Hn]]]. }
        apply AxiomII in Ht1g as [Et1g Ht1g].
        destruct Ht1g as [w0 [Hw0 Hw0t1]].
        assert (Ew0t1 : Ensemble ([w0,t1])) by (unfold Ensemble; exists g; exact Hw0t1).
        destruct (MKT49b w0 t1 Ew0t1) as [Ew0 Et1'].
        assert (Hww' : w = w0).
        { apply (proj2 Hginv t1 w w0).
          - apply (proj2 (MKT_inv_in g t1 w Et1' Ew)); exact Hw1t.
          - apply (proj2 (MKT_inv_in g t1 w0 Et1' Ew0)); exact Hw0t1. }
        apply AxiomII in Hw0 as [Ew0a [Hw0y Hw0C]].
        apply AxiomII in Hw0C as [Ew0b Hw0not].
        apply Hw0not. rewrite <- Hww'. exact Hw_fimg.
      + destruct Hc1' as [Ht1not Hw1t]. destruct Hc2' as [Ht2not Hw2t].
        assert (Ew : Ensemble w).
        { assert (Et1w : Ensemble ([t1,w])) by (unfold Ensemble; exists h; exact H1).
          exact (proj2 (MKT49b t1 w Et1w)). }
        assert (Et1 : Ensemble t1).
        { assert (Et1w : Ensemble ([t1,w])) by (unfold Ensemble; exists h; exact H1).
          exact (proj1 (MKT49b t1 w Et1w)). }
        assert (Et2 : Ensemble t2).
        { assert (Et2w : Ensemble ([t2,w])) by (unfold Ensemble; exists h; exact H2).
          exact (proj1 (MKT49b t2 w Et2w)). }
        apply (proj2 Hg w t1 t2).
        * exact Hw1t.
        * exact Hw2t. }

  assert (h_inv_func : Function (h⁻¹)).
  { split.
    - intros z Hz. apply AxiomII in Hz as [E Hz]. destruct Hz as [t [w [Hzw _]]]. exists t; exists w; exact Hzw.
    - intros x0 y0 z Hxy Hxz.
      assert (Ex0y0 : Ensemble ([x0,y0])) by (unfold Ensemble; exists (h⁻¹); exact Hxy).
      destruct (MKT49b x0 y0 Ex0y0) as [Ex0 Ey0].
      assert (Ex0z : Ensemble ([x0,z])) by (unfold Ensemble; exists (h⁻¹); exact Hxz).
      destruct (MKT49b x0 z Ex0z) as [Ex0' Ez].
      assert (Hy0x0 : [y0,x0] ∈ h) by (apply (proj1 (MKT_inv_in h x0 y0 Ex0 Ey0)); exact Hxy).
      assert (Hzx0 : [z,x0] ∈ h) by (apply (proj1 (MKT_inv_in h x0 z Ex0' Ez)); exact Hxz).
      apply (h_inj y0 z x0); assumption. }

  assert (h_11 : Function1_1 h) by (split; assumption).

  assert (h_ran : ran(h) = y).
  { apply AxiomI; intros w; split.
    - intros Hw.
      apply AxiomII in Hw as [Ew Hw].
      destruct Hw as [t Htw].
      pose proof (h_char t w Htw) as [Htx [Hc | Hc]].
      + destruct Hc as [HtT Hw'].
        assert (Htd : t ∈ dom(f)) by (rewrite Hfdom; exact Htx).
        assert (Htf : [t, f[t]] ∈ f) by (apply (MKT_dom_val f t Hf); exact Htd).
        assert (Hwr : w ∈ ran(f)).
        { apply AxiomII; split.
          - assert (Etft : Ensemble ([t, f[t]])) by (unfold Ensemble; exists f; exact Htf).
            rewrite Hw'. exact (proj2 (MKT49b t (f[t]) Etft)).
          - exists t; rewrite Hw'; exact Htf. }
        rewrite Hfran in Hwr. exact (Hv w Hwr).
      + destruct Hc as [Htnot Hwt].
        assert (Ewt : Ensemble ([w,t])) by (unfold Ensemble; exists g; exact Hwt).
        destruct (MKT49b w t Ewt) as [Ew' Et].
        assert (Hwd : w ∈ dom(g)).
        { apply AxiomII; split; [exact Ew' | exists t; exact Hwt]. }
        rewrite Hgdom in Hwd. exact Hwd.
    - intros Hwy.
      assert (Hwd : w ∈ dom(g)) by (rewrite Hgdom; exact Hwy).
      assert (Hgt : [w, g[w]] ∈ g) by (apply (MKT_dom_val g w Hg); exact Hwd).
      assert (Ewg : Ensemble ([w, g[w]])) by (unfold Ensemble; exists g; exact Hgt).
      destruct (MKT49b w (g[w]) Ewg) as [Ew Egw].
      assert (Egwx : g[w] ∈ x).
      { assert (Hgwr : g[w] ∈ ran(g)) by (apply AxiomII; split; [exact Egw | exists w; exact Hgt]).
        rewrite Hgran in Hgwr. exact (Hu (g[w]) Hgwr). }
      destruct (classic (g[w] ∈ T)) as [HgtT | Hgtnot].
      + assert (HgPhi : g[w] ∈ Phi T) by (rewrite <- HT_eq; exact HgtT).
        apply AxiomII in HgPhi as [Eg [Hgx HgC]].
        apply AxiomII in HgC as [Eg' Hgnot].
        assert (Hw_fimg : w ∈ fimg T).
        { apply NNPP; intro Hn.
          apply Hgnot.
          apply AxiomII; split; [exact Eg' | exists w; split; [| exact Hgt]].
          apply AxiomII; split; [exact Ew | split; [exact Hwy | apply AxiomII; split; [exact Ew | exact Hn]]]. }
        apply AxiomII in Hw_fimg as [Ewf Hw_fimg].
        destruct Hw_fimg as [t' [Ht'T Ht'w]].
        assert (Et'w : Ensemble ([t',w])) by (unfold Ensemble; exists f; exact Ht'w).
        destruct (MKT49b t' w Et'w) as [Et' Ew'].
        assert (Ew'x : t' ∈ x) by (exact (HTx t' Ht'T)).
        assert (Hwft' : w = f[t']).
        { symmetry. apply (MKT_fval f t' w Hf); exact Ht'w. }
        apply AxiomII; split; [exact Ew |].
        exists t'.
        apply AxiomII; split; [exact Et'w |].
        exists t'; exists w; split; [reflexivity |].
        split; [exact Ew'x | left; split; [exact Ht'T | exact Hwft']].
      + assert (Egww : Ensemble ([g[w], w])).
        { apply MKT49a; assumption. }
        apply AxiomII; split; [exact Ew |].
        exists (g[w]).
        apply AxiomII; split; [exact Egww |].
        exists (g[w]); exists w; split; [reflexivity |].
        split; [exact Egwx | right; split; [exact Hgtnot | exact Hgt]]. }

  exists h.
  split.
  - exact h_11.
  - split; [exact h_dom | exact h_ran].
Qed.

Theorem MKT160 : ∀ {f}, Function f -> Ensemble f
  -> P[ran(f)] ≼ P[dom(f)].
Proof.
  intros f Hf HfE.
  destruct (MKT_dom_ran_E f Hf HfE) as [HdomE HranE].
  destruct (MKT_surj_inj f Hf HfE) as [g [Hg11 [Hgdom Hgran]]].
  assert (Hranf_g : ran(f) ≈ ran(g)).
  { exists g; split; [exact Hg11 | split; [exact Hgdom | reflexivity]]. }
  destruct (MKT_sub_inj (ran(g)) (dom(f)) (P[dom(f)]) Hgran
    (MKT146 (MKT153 HdomE))) as [w [HwP Hranw]].
  assert (Hprf : P[ran(f)] ≈ ran(f)) by (apply MKT153; exact HranE).
  assert (Hprf_ranw : P[ran(f)] ≈ w).
  { apply (MKT147 ran(g) (P[ran(f)]) w).
    - apply (MKT147 ran(f) (P[ran(f)]) ran(g)); assumption.
    - exact Hranw. }
  assert (HprfC : P[ran(f)] ∈ C) by (apply MKT_C_val; exact HranE).
  assert (HpdC : P[dom(f)] ∈ C) by (apply MKT_C_val; exact HdomE).
  assert (HpdR : P[dom(f)] ∈ R) by (apply MKT_C_R; exact HpdC).
  apply (MKT_card_le_sub P[ran(f)] P[dom(f)] HprfC HpdR).
  exists w; split; [exact HwP | exact Hprf_ranw].
Qed.

Theorem MKT161 : ∀ {x}, Ensemble x -> P[x] ≺ P[pow(x)].
Proof.
  intros x Hx.
  destruct (MKT_x_pow x Hx) as [S [HSpow HxS]].
  assert (HpowE : Ensemble pow(x)) by (apply MKT38a; exact Hx).
  destruct (MKT_sub_inj S pow(x) (P[pow(x)]) HSpow
    (MKT146 (MKT153 HpowE))) as [w [HwP HS_w]].
  assert (HpxS : P[x] ≈ S).
  { apply (MKT147 x (P[x]) S (MKT153 Hx) HxS). }
  assert (Hpxw : P[x] ≈ w).
  { apply (MKT147 S (P[x]) w HpxS HS_w). }
  assert (HpxC : P[x] ∈ C) by (apply MKT_C_val; exact Hx).
  assert (HpwC : P[pow(x)] ∈ C) by (apply MKT_C_val; exact HpowE).
  assert (HpwR : P[pow(x)] ∈ R) by (apply MKT_C_R; exact HpwC).
  assert (Hpx_le : P[x] ≼ P[pow(x)]).
  { apply (MKT_card_le_sub P[x] P[pow(x)] HpxC HpwR).
    exists w; split; [exact HwP | exact Hpxw]. }
  destruct Hpx_le as [Hpxin | Hpxeq].
  - exact Hpxin.
  - exfalso.
    assert (Hxpow : x ≈ pow(x)).
    { apply (proj1 (MKT154 x pow(x) Hx HpowE)). exact Hpxeq. }
    exact (MKT_cantor x Hx Hxpow).
Qed.

Theorem MKT162 : ~ Ensemble C.
Proof.
  intro HC.
  set (δ := ∪C).
  assert (HCE : Ensemble δ).
  { unfold δ. apply AxiomVI; exact HC. }
  assert (HδR : δ ∈ R).
  { unfold δ. apply AxiomII; split; [exact HCE |].
    apply MKT120.
    intros z Hz.
    apply AxiomII in Hz as [Ez [HzR _]]. exact HzR. }
  assert (HpowE : Ensemble pow(δ)) by (apply MKT38a; exact HCE).
  assert (HλC : P[pow(δ)] ∈ C) by (apply MKT_C_val; exact HpowE).
  assert (Hλδ : P[pow(δ)] ⊂ δ).
  { unfold δ. intros z Hz.
    apply AxiomII; split; [exists (P[pow(δ)]); exact Hz |].
    exists (P[pow(δ)]); split; [exact Hz | exact HλC]. }
  assert (Hpowλ : pow(δ) ≈ P[pow(δ)]) by (apply MKT146; apply MKT153; exact HpowE).
  destruct (MKT_x_pow δ HCE) as [S [HSpow HδS]].
  assert (Hpowδ : pow(δ) ≈ δ).
  { exact (MKT159 (pow(δ)) δ S (P[pow(δ)]) HpowE HCE HSpow Hλδ Hpowλ HδS). }
  exact (MKT_cantor δ HCE (MKT146 Hpowδ)).
Qed.

(* 我们把基数分为两类，有限基数与无限基数 *)

(* 有限基数 *)

Theorem MKT163 : ∀ x y, x∈ω -> y∈ω -> (PlusOne x) ≈ (PlusOne y)
  -> x ≈ y.
Proof.
  intros x y Hxw Hyw Hxy.
  apply AxiomII in Hxw as [Ex Hintx].
  apply AxiomII in Hyw as [Ey Hinty].
  pose proof Hintx as Hintx0.
  pose proof Hinty as Hinty0.
  destruct Hintx as [Hoxx Hwox].
  destruct Hinty as [Hoyy Hwoy].
  destruct Hoxx as [Hconnx Hfullx].
  destruct Hoyy as [Hconny Hfully].
  destruct Hxy as [f [Hf11 [Hdom Hran]]].
  destruct Hf11 as [Hf Hfinv].
  assert (Hx_plus : x ∈ PlusOne x).
  { unfold PlusOne. apply AxiomII; split.
    - exact Ex.
    - right. apply (proj2 (MKT41 x Ex x)); reflexivity. }
  assert (Hy_plus : y ∈ PlusOne y).
  { unfold PlusOne. apply AxiomII; split.
    - exact Ey.
    - right. apply (proj2 (MKT41 y Ey y)); reflexivity. }
  assert (Hxdom : x ∈ dom(f)).
  { rewrite Hdom. exact Hx_plus. }
  assert (Hyran : y ∈ ran(f)).
  { rewrite Hran. exact Hy_plus. }
  assert (Hxfx : [x, f[x]] ∈ f) by (apply (MKT_dom_val f x Hf Hxdom)).
  assert (Hfxr : f[x] ∈ ran(f)).
  { apply AxiomII; split.
    - assert (E : Ensemble ([x, f[x]])) by (unfold Ensemble; eauto).
      exact (proj2 (MKT49b x (f[x]) E)).
    - exists x; exact Hxfx. }
  pose proof Hfxr as Hfxr0.
  apply AxiomII in Hfxr0 as [Efx _].
  assert (Hfxy : f[x] ∈ PlusOne y).
  { rewrite <- Hran. exact Hfxr. }
  apply AxiomII in Hyran as [Ey' Hyran'].
  destruct Hyran' as [a0 Ha0].
  assert (Ea0y : Ensemble ([a0,y])) by (unfold Ensemble; eauto).
  destruct (MKT49b a0 y Ea0y) as [Ea0 Ey''].
  assert (Ha0dom : a0 ∈ dom(f)).
  { apply AxiomII; split; [exact Ea0 | exists y; exact Ha0]. }
  assert (Hfa0 : f[a0] = y) by (apply (MKT_fval f a0 y Hf); exact Ha0).
  assert (Hzx : ∀ z, z ∈ x -> Ensemble z).
  { intros z Hzy.
    assert (Hzmu : z ∈ μ) by (exact (MKT26' x z Hzy)).
    apply AxiomII in Hzmu as [Ez _]. exact Ez. }
  assert (Hzy : ∀ z, z ∈ y -> Ensemble z).
  { intros z Hzy.
    assert (Hzmu : z ∈ μ) by (exact (MKT26' y z Hzy)).
    apply AxiomII in Hzmu as [Ez _]. exact Ez. }
  destruct (classic (f[x] = y)) as [Hfxyeq | Hfxneq].
  - (* f[x] = y : restrict f to x *)
    set (g := f | (x)).
    assert (Hg_func : Function g).
    { apply (MKT126a f x Hf). }
    assert (Hg_dom : dom(g) = x).
    { unfold g. rewrite (MKT126b f x Hf).
      apply (proj2 (MKT30 x (dom(f)))).
      intros t Htx. rewrite Hdom.
      apply AxiomII; split; [unfold Ensemble; exists x; exact Htx | left; exact Htx]. }
    assert (Hg_ran : ran(g) = y).
    { apply AxiomI; intros w; split.
      - intros Hw.
        apply AxiomII in Hw as [Ew Hw].
        destruct Hw as [t Htw].
        apply AxiomII in Htw as [Etw [Htwf Htwx]].
        apply AxiomII in Htwx as [Etw' Htwx'].
        destruct Htwx' as [u [v [Huv [Hux Hvmu]]]].
        assert (Euv : Ensemble ([u,v])).
        { rewrite <- Huv. exact Etw'. }
        assert (Et : Ensemble t) by (exact (proj1 (MKT49b t w Etw))).
        assert (Ew' : Ensemble w) by (exact (proj2 (MKT49b t w Etw))).
        assert (Eu : Ensemble u) by (exact (proj1 (MKT49b u v Euv))).
        assert (Ev : Ensemble v) by (exact (proj2 (MKT49b u v Euv))).
        destruct (proj1 (MKT55 t w u v Et Ew') Huv) as [Htu Hwv].
        subst u; subst v.
        assert (Hwr : w ∈ ran(f)).
        { apply AxiomII; split; [exact Ew' | exists t; exact Htwf]. }
        rewrite Hran in Hwr.
        apply AxiomII in Hwr as [Ew'' Hwr'].
        destruct Hwr' as [Hwy | Hws].
        + exact Hwy.
        + apply (proj1 (MKT41 y Ey w)) in Hws.
          subst w.
          exfalso.
          assert (Ht_eq : t = x).
          { apply (proj2 Hfinv y t x).
            - apply (proj2 (MKT_inv_in f y t Ey Et)); exact Htwf.
            - apply (proj2 (MKT_inv_in f y x Ey Ex)).
              rewrite <- Hfxyeq. exact Hxfx. }
          rewrite Ht_eq in Hux.
          exact (MKT101 x Hux).
      - intros Hwy.
        assert (Hwran : w ∈ ran(f)).
        { rewrite Hran. apply AxiomII; split; [exact (Hzy w Hwy) | left; exact Hwy]. }
        apply AxiomII in Hwran as [Ew Hwran'].
        destruct Hwran' as [t Htw].
        assert (Etw : Ensemble ([t,w])) by (unfold Ensemble; eauto).
        destruct (MKT49b t w Etw) as [Et Ew'].
        assert (Htdom : t ∈ dom(f)).
        { apply AxiomII; split; [exact Et | exists w; exact Htw]. }
        rewrite Hdom in Htdom.
        apply AxiomII in Htdom as [Et' Htdom'].
        destruct Htdom' as [Htx | Hts].
        + assert (Hwmu : w ∈ μ) by (apply MKT19b; exact (Hzy w Hwy)).
          assert (Htwx : [t,w] ∈ x × μ).
          { apply AxiomII; split; [exact Etw | exists t; exists w; split; [reflexivity | split; [exact Htx | exact Hwmu]]]. }
          apply AxiomII; split; [exact Ew' | exists t].
          apply AxiomII; split; [exact Etw | split; [exact Htw | exact Htwx]].
        + apply (proj1 (MKT41 x Ex t)) in Hts.
          subst t.
          exfalso.
          assert (Hw_eq_y : w = y).
          { transitivity (f[x]).
            - apply (proj2 Hf x w (f[x])); [exact Htw | exact Hxfx].
            - exact Hfxyeq. }
          rewrite Hw_eq_y in Hwy.
          exact (MKT101 y Hwy). }
    assert (Hg_11 : Function1_1 g).
    { split; [exact Hg_func |].
      unfold Function; split.
      - intros z Hz.
        apply AxiomII in Hz as [Ez Hz].
        destruct Hz as [a [b [Hzb _]]].
        exists a; exists b; exact Hzb.
      - intros a b c Hab Hac.
        assert (Eab : Ensemble ([a,b])) by (unfold Ensemble; exists (g⁻¹); exact Hab).
        destruct (MKT49b a b Eab) as [Ea Eb].
        assert (Eac : Ensemble ([a,c])) by (unfold Ensemble; exists (g⁻¹); exact Hac).
        destruct (MKT49b a c Eac) as [Ea' Ec].
        assert (Hba : [b,a] ∈ g) by (apply (proj1 (MKT_inv_in g a b Ea Eb)); exact Hab).
        assert (Hca : [c,a] ∈ g) by (apply (proj1 (MKT_inv_in g a c Ea' Ec)); exact Hac).
        unfold g in Hba, Hca.
        apply AxiomII in Hba as [Eba [Hba1 _]].
        apply AxiomII in Hca as [Eca [Hca1 _]].
        apply (proj2 Hfinv a b c).
        + apply (proj2 (MKT_inv_in f a b Ea Eb)); exact Hba1.
        + apply (proj2 (MKT_inv_in f a c Ea' Ec)); exact Hca1. }
    exists g; split; [exact Hg_11 | split; [exact Hg_dom | exact Hg_ran]].
  - (* f[x] ≠ y : swap a0 and x *)
    assert (Ha0x : a0 ∈ x).
    { assert (Ha0plus : a0 ∈ PlusOne x).
      { rewrite <- Hdom. exact Ha0dom. }
      apply AxiomII in Ha0plus as [Ea0'' Ha0plus'].
      destruct Ha0plus' as [Ha0x | Ha0s].
      - exact Ha0x.
      - apply (proj1 (MKT41 x Ex a0)) in Ha0s.
        subst a0.
        exfalso.
        apply Hfxneq.
        symmetry.
        apply (proj2 Hf x y (f[x])); [exact Ha0 | exact Hxfx]. }
    assert (Hfxy_in : f[x] ∈ y).
    { apply AxiomII in Hfxy as [Efx' Hfxy'].
      destruct Hfxy' as [Hfy | Hfs].
      - exact Hfy.
      - apply (proj1 (MKT41 y Ey (f[x]))) in Hfs.
        exfalso. apply Hfxneq; exact Hfs. }
    set (g := \{\ λ t w, t ∈ x
      /\ ((t = a0 /\ w = f[x]) \/ (t ≠ a0 /\ [t,w] ∈ f)) \}\).
    assert (g_char : ∀ t w, [t,w] ∈ g <->
      Ensemble ([t,w]) /\ t ∈ x
      /\ ((t = a0 /\ w = f[x]) \/ (t ≠ a0 /\ [t,w] ∈ f))).
    { intros t w; split.
      - intros Htw.
        apply AxiomII in Htw as [Etw Htw].
        destruct Htw as [u [v [Huv Huv']]].
        destruct Huv' as [Hux Huv''].
        assert (Euv : Ensemble ([u,v])) by (rewrite <- Huv; exact Etw).
        destruct (MKT49b u v Euv) as [Eu Ev].
        destruct (MKT49b t w Etw) as [Et Ew].
        destruct (proj1 (MKT55 t w u v Et Ew) Huv) as [Htu Hwv].
        subst u; subst v.
        split; [exact Etw | split; [exact Hux | exact Huv'']].
      - intros [Etw [Htx Hc]].
        apply AxiomII; split; [exact Etw |].
        exists t; exists w; split; [reflexivity | split; [exact Htx | exact Hc]]. }
    assert (Hg_func : Function g).
    { split.
      - intros z Hz.
        apply AxiomII in Hz as [Ez Hz].
        destruct Hz as [t [w [Hzw _]]].
        exists t; exists w; exact Hzw.
      - intros t w1 w2 Htw1 Htw2.
        destruct (proj1 (g_char t w1) Htw1) as [Etw1 [Htx1 Hc1]].
        destruct (proj1 (g_char t w2) Htw2) as [Etw2 [Htx2 Hc2]].
        destruct Hc1 as [Hc1 | Hc1'].
        + destruct Hc1 as [Hta Hw1fx].
          destruct Hc2 as [Hc2 | Hc2'].
          * destruct Hc2 as [Hta' Hw2fx]. rewrite Hw1fx. rewrite Hw2fx. reflexivity.
          * destruct Hc2' as [Htna' Htw2f]. exfalso. apply Htna'. exact Hta.
        + destruct Hc1' as [Htna Htw1f].
          destruct Hc2 as [Hc2 | Hc2'].
          * destruct Hc2 as [Hta Hw2fx]. exfalso. apply Htna. exact Hta.
          * destruct Hc2' as [Htna'' Htw2f].
            apply (proj2 Hf t w1 w2); assumption.
    }
    assert (Hg_dom : dom(g) = x).
    { apply AxiomI; intros t; split.
      - intros Ht.
        apply AxiomII in Ht as [Et Ht].
        destruct Ht as [w Htw].
        destruct (proj1 (g_char t w) Htw) as [Etw [Htx _]].
        exact Htx.
      - intros Htx.
        assert (Et : Ensemble t) by (unfold Ensemble; exists x; exact Htx).
        apply AxiomII; split; [exact Et |].
        destruct (classic (t = a0)) as [Hta | Htna].
        + subst t.
          exists (f[x]).
          apply (proj2 (g_char a0 (f[x]))).
          split; [apply MKT49a; [exact Ea0 | exact Efx] |].
          split; [exact Ha0x | left; split; reflexivity].
        + assert (Htdom : t ∈ dom(f)).
          { rewrite Hdom. apply AxiomII; split; [unfold Ensemble; exists x; exact Htx | left; exact Htx]. }
          apply AxiomII in Htdom as [Et' Htdom'].
          destruct Htdom' as [w Htw].
          exists w.
          apply (proj2 (g_char t w)).
          split; [unfold Ensemble; exists f; exact Htw |].
          split; [exact Htx | right; split; [exact Htna | exact Htw]].
    }
    assert (Hg_ran : ran(g) = y).
    { apply AxiomI; intros w; split.
      - intros Hw.
        apply AxiomII in Hw as [Ew Hw].
        destruct Hw as [t Htw].
        destruct (proj1 (g_char t w) Htw) as [Etw [Htx Hc]].
        destruct (MKT49b t w Etw) as [Et Ew'].
        destruct Hc as [Hc | Hc'].
        + destruct Hc as [Hta Hwfx]. rewrite Hwfx. exact Hfxy_in.
        + destruct Hc' as [Htna Htwf].
          assert (Hwr : w ∈ ran(f)).
          { apply AxiomII; split; [exact Ew' | exists t; exact Htwf]. }
          rewrite Hran in Hwr.
          apply AxiomII in Hwr as [Ew'' Hwr'].
          destruct Hwr' as [Hwy | Hws].
          * exact Hwy.
          * apply (proj1 (MKT41 y Ey w)) in Hws.
            subst w.
            exfalso.
            assert (Ht_eq : t = a0).
            { apply (proj2 Hfinv y t a0).
              - apply (proj2 (MKT_inv_in f y t Ey Et)); exact Htwf.
              - apply (proj2 (MKT_inv_in f y a0 Ey Ea0)); exact Ha0. }
            exact (Htna Ht_eq).
      - intros Hwy.
        destruct (classic (w = f[x])) as [Hwfx | Hwnfx].
        + subst w.
          apply AxiomII; split; [exact Efx |].
          exists a0.
          apply (proj2 (g_char a0 (f[x]))).
          split; [apply MKT49a; [exact Ea0 | exact Efx] |].
          split; [exact Ha0x | left; split; reflexivity].
        + assert (Hwran : w ∈ ran(f)).
          { rewrite Hran. apply AxiomII; split; [exact (Hzy w Hwy) | left; exact Hwy]. }
          apply AxiomII in Hwran as [Ew Hwran'].
          destruct Hwran' as [t Htw].
          assert (Etw : Ensemble ([t,w])) by (unfold Ensemble; eauto).
          destruct (MKT49b t w Etw) as [Et Ew'].
          assert (Htdom : t ∈ dom(f)).
          { apply AxiomII; split; [exact Et | exists w; exact Htw]. }
          rewrite Hdom in Htdom.
          apply AxiomII in Htdom as [Et' Htdom'].
          destruct Htdom' as [Htx | Hts].
          * assert (Htna : t ≠ a0).
            { intro Hta. subst t.
              assert (Hw_eq_y : w = y).
              { apply (proj2 Hf a0 w y); [exact Htw | exact Ha0]. }
              rewrite Hw_eq_y in Hwy.
              exact (MKT101 y Hwy). }
            apply AxiomII; split; [exact Ew' |].
            exists t.
            apply (proj2 (g_char t w)).
            split; [exact Etw | split; [exact Htx | right; split; [exact Htna | exact Htw]]].
          * apply (proj1 (MKT41 x Ex t)) in Hts.
            subst t.
            exfalso.
            apply Hwnfx.
            apply (proj2 Hf x w (f[x])); [exact Htw | exact Hxfx].
    }
    assert (Hg_inj : ∀ t1 t2 w, [t1,w] ∈ g -> [t2,w] ∈ g -> t1 = t2).
    { intros t1 t2 w H1 H2.
      destruct (proj1 (g_char t1 w) H1) as [Etw1 [Ht1x Hc1]].
      destruct (proj1 (g_char t2 w) H2) as [Etw2 [Ht2x Hc2]].
      destruct (MKT49b t1 w Etw1) as [Et1 Ew1].
      destruct (MKT49b t2 w Etw2) as [Et2 Ew2].
      destruct (classic (w = f[x])) as [Hwfx | Hwnfx].
      - destruct Hc1 as [Hc1 | Hc1'].
        + destruct Hc1 as [Ht1a _].
          destruct Hc2 as [Hc2 | Hc2'].
          * destruct Hc2 as [Ht2a _]. rewrite Ht1a. rewrite Ht2a. reflexivity.
          * destruct Hc2' as [Ht2na Ht2wf].
            exfalso.
            assert (Ht2eq : t2 = x).
            { apply (proj2 Hfinv (f[x]) t2 x).
              - rewrite Hwfx in Ht2wf.
                apply (proj2 (MKT_inv_in f (f[x]) t2 Efx Et2)); exact Ht2wf.
              - apply (proj2 (MKT_inv_in f (f[x]) x Efx Ex)); exact Hxfx. }
            rewrite Ht2eq in Ht2x.
            exact (MKT101 x Ht2x).
        + destruct Hc1' as [Ht1na Ht1wf].
          exfalso.
          assert (Ht1eq : t1 = x).
          { apply (proj2 Hfinv (f[x]) t1 x).
            - rewrite Hwfx in Ht1wf.
              apply (proj2 (MKT_inv_in f (f[x]) t1 Efx Et1)); exact Ht1wf.
            - apply (proj2 (MKT_inv_in f (f[x]) x Efx Ex)); exact Hxfx. }
          rewrite Ht1eq in Ht1x.
          exact (MKT101 x Ht1x).
      - destruct Hc1 as [Hc1 | Hc1'].
        + destruct Hc1 as [Ht1a Hw]. exfalso. exact (Hwnfx Hw).
        + destruct Hc2 as [Hc2 | Hc2'].
          * destruct Hc2 as [Ht2a Hw]. exfalso. exact (Hwnfx Hw).
          * destruct Hc1' as [Ht1na Ht1wf].
            destruct Hc2' as [Ht2na Ht2wf].
            assert (Hw1f : [w,t1] ∈ f⁻¹).
            { apply (proj2 (MKT_inv_in f w t1 Ew1 Et1)); exact Ht1wf. }
            assert (Hw2f : [w,t2] ∈ f⁻¹).
            { apply (proj2 (MKT_inv_in f w t2 Ew2 Et2)); exact Ht2wf. }
            exact (proj2 Hfinv w t1 t2 Hw1f Hw2f).
    }
    assert (Hg_inv_func : Function (g⁻¹)).
    { split.
      - intros z Hz.
        apply AxiomII in Hz as [Ez Hz].
        destruct Hz as [a [b [Hzb _]]].
        exists a; exists b; exact Hzb.
      - intros a b c Hab Hac.
        assert (Eab : Ensemble ([a,b])) by (unfold Ensemble; exists (g⁻¹); exact Hab).
        destruct (MKT49b a b Eab) as [Ea Eb].
        assert (Eac : Ensemble ([a,c])) by (unfold Ensemble; exists (g⁻¹); exact Hac).
        destruct (MKT49b a c Eac) as [Ea' Ec].
        apply (Hg_inj b c a).
        + apply (proj1 (MKT_inv_in g a b Ea Eb)); exact Hab.
        + apply (proj1 (MKT_inv_in g a c Ea' Ec)); exact Hac.
    }
    assert (Hg_11 : Function1_1 g) by (split; assumption).
    exists g; split; [exact Hg_11 | split; [exact Hg_dom | exact Hg_ran]].
Qed.

Theorem MKT164 : ω ⊂ C.
Proof.
  unfold Included; intros z Hz.
  assert (LemmaA : ∀ z, z ∈ ω -> z ∈ R).
  { intros z' Hz'.
    apply AxiomII; split.
    - apply AxiomII in Hz' as [Hz'Ens _]; exact Hz'Ens.
    - apply AxiomII in Hz' as [_ Hz'Int]; unfold Integer in Hz'Int;
        destruct Hz'Int as [Hz'Ord _]; exact Hz'Ord.
  }
  assert (HΦEns : Ensemble Φ).
  { destruct AxiomVIII as [y8 [Hy8Ens [HΦ8 _]]].
    unfold Ensemble; exists y8; exact HΦ8.
  }
  (* Claim P: on ω, PlusOne is never equivalent to its argument *)
  assert (ClaimP : ∀ z, z ∈ ω -> ~ (PlusOne z ≈ z)).
  { pose (s := \{ λ x, x ∈ ω /\ ~ (PlusOne x ≈ x) \}).
    assert (Hsω : s ⊂ ω).
    { unfold Included; intros x Hx.
      unfold s in Hx; apply AxiomII in Hx as [_ [Hxω _]]; exact Hxω.
    }
    assert (HΦs : Φ ∈ s).
    { unfold s; apply AxiomII; split.
      - exact HΦEns.
      - split.
        + exact MKT135a.
        + intro Hbase.
          unfold PlusOne in Hbase.
          unfold Equivalent in Hbase.
          destruct Hbase as [f [[_ _] [Hdom Hran]]].
          assert (HΦdom : Φ ∈ dom(f)).
          { rewrite Hdom.
            apply (proj1 (MKT4 Φ ([Φ]) Φ)); right.
            unfold Singleton.
            apply AxiomII; split.
            - exact HΦEns.
            - intro; reflexivity.
          }
          apply AxiomII in HΦdom as [_ Hy].
          destruct Hy as [y Hpair].
          assert (HyEns' : Ensemble y).
          { assert (HpairEns : Ensemble ([Φ,y])).
            { unfold Ensemble; exists f; exact Hpair. }
            exact (proj2 (MKT49b Φ y HpairEns)).
          }
          assert (Hyran : y ∈ ran(f)).
          { apply AxiomII; split.
            - exact HyEns'.
            - exists Φ; exact Hpair.
          }
          assert (HyΦ : y ∈ Φ).
          { pose proof (AxiomI ran(f) Φ) as Hiff.
            exact (proj1 ((proj1 Hiff Hran) y) Hyran).
          }
          exact (@MKT16 y HyΦ).
    }
    assert (Hclos : ∀ u, u ∈ s -> PlusOne u ∈ s).
    { intros u Hu.
      unfold s in Hu; apply AxiomII in Hu as [HuEns [Huω Hnu]].
      unfold s; apply AxiomII; split.
      - assert (Hpoω : PlusOne u ∈ ω). { apply MKT134; exact Huω. }
        apply AxiomII in Hpoω as [HpoEns _]; exact HpoEns.
      - split.
        + apply MKT134; exact Huω.
        + intro Hpo.
          apply Hnu.
          apply (MKT163 (PlusOne u) u).
          * apply MKT134; exact Huω.
          * exact Huω.
          * exact Hpo.
    }
    assert (Hseq : s = ω).
    { apply MKT137; [exact Hsω | exact HΦs | exact Hclos]. }
    intros z' Hz'.
    assert (Hz's : z' ∈ s).
    { rewrite Hseq; exact Hz'. }
    unfold s in Hz's; apply AxiomII in Hz's as [_ [_ Hn]]; exact Hn.
  }
  (* Now prove z ∈ C by contradiction via a minimal counterexample *)
  apply (proj1 (NNPP (z ∈ C))); intro HznotC.
  pose (s := \{ λ w, w ∈ ω /\ w ∉ C \}).
  assert (Hsω : s ⊂ ω).
  { unfold Included; intros w Hw.
    unfold s in Hw; apply AxiomII in Hw as [_ [Hwω _]]; exact Hwω.
  }
  assert (Hsne : s ≠ Φ).
  { intro HsΦ.
    assert (Hzs : z ∈ s).
    { unfold s; apply AxiomII; split.
      - apply AxiomII in Hz as [HzEns _]; exact HzEns.
      - split; [exact Hz | exact HznotC].
    }
    rewrite HsΦ in Hzs.
    exact (@MKT16 z Hzs).
  }
  assert (Hwo : WellOrdered E ω).
  { apply MKT107.
    pose proof MKT138 as HωR.
    apply AxiomII in HωR as [_ HωOrd].
    exact HωOrd.
  }
  destruct (proj2 Hwo s Hsω Hsne) as [m Hm].
  destruct Hm as [Hms Hmin].
  unfold s in Hms.
  apply AxiomII in Hms as [HmEns [Hmω HmnotC]].
  assert (HmR : m ∈ R). { apply LemmaA; exact Hmω. }
  assert (HmnotCard : ~ Cardinal_Number m).
  { intro Hc.
    apply HmnotC.
    apply AxiomII; split; [exact HmEns | exact Hc].
  }
  assert (Hnot : ~ (∀ y, y ∈ R -> y ∈ m -> ~ (m ≈ y))).
  { intro H.
    apply HmnotCard.
    unfold Cardinal_Number, Ordinal_Number.
    split; [exact HmR | exact H].
  }
  assert (Hex : ∃ y, y ∈ R /\ y ∈ m /\ m ≈ y).
  { apply (proj1 (NNPP _)).
    intro Hnone.
    apply Hnot.
    intros y0 Hy0R Hy0m Hmy0.
    apply Hnone.
    exists y0; split; [exact Hy0R | split; [exact Hy0m | exact Hmy0]].
  }
  destruct Hex as [y [HyR [Hym Hmy]]].
  (* minimality: every element of m is in C *)
  assert (HminC : ∀ w, w ∈ m -> w ∈ C).
  { intros w Hwm.
    apply (proj1 (NNPP (w ∈ C))); intro HwnotC.
    assert (HwEns : Ensemble w).
    { unfold Ensemble; exists m; exact Hwm. }
    assert (Hwω : w ∈ ω).
    { apply AxiomII; split.
      - exact HwEns.
      - apply AxiomII in Hmω as [_ HmInt].
        apply (MKT132 m w HmInt Hwm).
    }
    assert (Hws : w ∈ s).
    { unfold s; apply AxiomII; split.
      - exact HwEns.
      - split; [exact Hwω | exact HwnotC].
    }
    assert (HpairE : [w,m] ∈ E).
    { unfold E.
      apply AxiomII; split.
      - apply MKT49a; [exact HwEns | exact HmEns].
      - exists w; exists m; split; [reflexivity | exact Hwm].
    }
    exact (Hmin w Hws HpairE).
  }
  apply AxiomII in HyR as [HyEns _].
  assert (Hyω : y ∈ ω).
  { apply AxiomII; split.
    - exact HyEns.
    - apply AxiomII in Hmω as [_ HmInt].
      apply (MKT132 m y HmInt Hym).
  }
  assert (HyC : y ∈ C). { apply HminC; exact Hym. }
  assert (Hypy : P[y] = y).
  { exact (proj2 (proj2 (MKT156 y) HyC)). }
  assert (Hpmy : P[m] = P[y]).
  { apply (proj2 (MKT154 m y HmEns HyEns)); exact Hmy. }
  assert (Hpm : P[m] = y).
  { rewrite Hypy in Hpmy; exact Hpmy. }
  assert (Hpoyω : PlusOne y ∈ ω). { apply MKT134; exact Hyω. }
  assert (HpoyR : PlusOne y ∈ R). { apply LemmaA; exact Hpoyω. }
  assert (HpoyOrd : Ordinal (PlusOne y)).
  { apply AxiomII in HpoyR as [_ HpoyOrd]; exact HpoyOrd. }
  assert (HmOrd : Ordinal m).
  { apply AxiomII in HmR as [_ HmOrd]; exact HmOrd. }
  destruct (MKT110 HpoyOrd HmOrd) as [Hpoym | [Hmpo | Hpoym_eq]].
  - (* PlusOne y ∈ m *)
    assert (HpoyC : PlusOne y ∈ C). { apply HminC; exact Hpoym. }
    assert (Hpopo : P[PlusOne y] = PlusOne y).
    { exact (proj2 (proj2 (MKT156 (PlusOne y)) HpoyC)). }
    assert (Hposub : PlusOne y ⊂ m).
    { unfold Ordinal in HmOrd; destruct HmOrd as [_ HmFull].
      exact (HmFull (PlusOne y) Hpoym).
    }
    assert (Hle : P[PlusOne y] ≼ P[m]).
    { exact (MKT158 Hposub). }
    unfold LessEqual in Hle.
    rewrite Hpopo in Hle; rewrite Hpm in Hle.
    destruct Hle as [Hin | Heq].
    + assert (Hyinpo : y ∈ PlusOne y).
      { unfold PlusOne.
        apply (proj1 (MKT4 y ([y]) y)); right.
        unfold Singleton.
        apply AxiomII; split.
        - exact HyEns.
        - intro; reflexivity.
      }
      exact (MKT102 y (PlusOne y) Hyinpo Hin).
    + assert (Hyinpo : y ∈ PlusOne y).
      { unfold PlusOne.
        apply (proj1 (MKT4 y ([y]) y)); right.
        unfold Singleton.
        apply AxiomII; split.
        - exact HyEns.
        - intro; reflexivity.
      }
      rewrite Heq in Hyinpo.
      exact (MKT101 y Hyinpo).
  - (* m ∈ PlusOne y *)
    unfold PlusOne in Hmpo.
    apply (proj2 (MKT4 y ([y]) m)) in Hmpo.
    destruct Hmpo as [Hmyin | HmSing].
    + exact (MKT102 y m Hym Hmyin).
    + apply AxiomII in HmSing as [_ HmSing'].
      assert (HyMu : y ∈ μ). { apply MKT19b; exact HyEns. }
      assert (Hmeq : m = y). { exact (HmSing' HyMu). }
      rewrite Hmeq in Hym.
      exact (MKT101 y Hym).
  - (* PlusOne y = m *)
    rewrite <- Hpoym_eq in Hmy.
    exact (ClaimP y Hyω Hmy).
Qed.

Theorem MKT165 : ω ∈ C.
Proof.
  apply AxiomII; split.
  - pose proof MKT138 as HωR.
    apply AxiomII in HωR as [HωEns _].
    exact HωEns.
  - unfold Cardinal_Number, Ordinal_Number; split.
    + exact MKT138.
    + intros y HyR Hyw Hwy.
      assert (HyC : y ∈ C).
      { apply MKT164; exact Hyw. }
      assert (Hypy : P[y] = y).
      { exact (proj2 (proj2 (MKT156 y) HyC)). }
      pose proof MKT138 as HωR.
      apply AxiomII in HωR as [HωEns HωOrd].
      apply AxiomII in HyR as [HyEns _].
      assert (Hpwpy : P[ω] = P[y]).
      { apply (proj2 (MKT154 ω y HωEns HyEns)); exact Hwy. }
      assert (Hpwy : P[ω] = y).
      { rewrite Hypy in Hpwpy; exact Hpwpy. }
      assert (Hpoy : PlusOne y ∈ ω).
      { apply MKT134; exact Hyw. }
      assert (HpoyC : PlusOne y ∈ C).
      { apply MKT164; exact Hpoy. }
      assert (Hpopo : P[PlusOne y] = PlusOne y).
      { exact (proj2 (proj2 (MKT156 (PlusOne y)) HpoyC)). }
      assert (Hposub : PlusOne y ⊂ ω).
      { unfold Ordinal in HωOrd; destruct HωOrd as [_ HωFull].
        exact (HωFull (PlusOne y) Hpoy).
      }
      assert (Hle : P[PlusOne y] ≼ P[ω]).
      { exact (MKT158 Hposub). }
      unfold LessEqual in Hle.
      rewrite Hpopo in Hle; rewrite Hpwy in Hle.
      destruct Hle as [Hin | Heq].
      * assert (Hyinpo : y ∈ PlusOne y).
        { unfold PlusOne.
          apply (proj1 (MKT4 y ([y]) y)); right.
          unfold Singleton.
          apply AxiomII; split.
          - exact HyEns.
          - intro; reflexivity.
        }
        exact (MKT102 y (PlusOne y) Hyinpo Hin).
      * assert (Hyinpo : y ∈ PlusOne y).
        { unfold PlusOne.
          apply (proj1 (MKT4 y ([y]) y)); right.
          unfold Singleton.
          apply AxiomII; split.
          - exact HyEns.
          - intro; reflexivity.
        }
        rewrite Heq in Hyinpo.
        exact (MKT101 y Hyinpo).
Qed.

Theorem MKT167 : ∀ x, Finite x <-> ∃ r, WellOrdered r x
  /\ WellOrdered (r⁻¹) x.
Proof.
  intros x.
  (* Common helper: membership in E *)
  assert (HE_mem : ∀ a b, Ensemble a -> Ensemble b -> ([a,b] ∈ E <-> a ∈ b)).
  { intros a b Ea Eb; split.
    - intros Hab.
      apply AxiomII in Hab as [Eab Hab].
      destruct Hab as [a' [b' [Hab' Ha']]].
      assert (Ea'b' : Ensemble ([a',b'])) by (rewrite <- Hab'; exact Eab).
      destruct (MKT49b a' b' Ea'b') as [Ea' Eb'].
      destruct (proj1 (MKT55 a b a' b' Ea Eb) Hab') as [Haa' Hbb'].
      rewrite <- Haa' in Ha'. rewrite <- Hbb' in Ha'. exact Ha'.
    - intros Hab.
      apply AxiomII; split.
      + exact (MKT49a Ea Eb).
      + exists a; exists b; split; [reflexivity | exact Hab]. }
  (* Common helper: if x ≈ y and y is an ensemble, then x is an ensemble *)
  assert (H_eq_Ens : ∀ x y, x ≈ y -> Ensemble y -> Ensemble x).
  { intros x0 y0 Hxy Hy.
    destruct Hxy as [h [Hh11 [Hhd Hhr]]].
    destruct Hh11 as [Hh Hh_inv].
    rewrite <- Hhd.
    rewrite <- (MKT_ran_inv h).
    apply (AxiomV (f:=h⁻¹)).
    - exact Hh_inv.
    - rewrite MKT_dom_inv. rewrite Hhr. exact Hy. }
  split.
  - (* Finite x -> ∃ r, WellOrdered r x /\ WellOrdered (r⁻¹) x *)
    intros Hfx.
    (* Ensemble x *)
    assert (HEx : Ensemble x).
    { apply MKT19a.
      rewrite <- MKT152b.
      apply (MKT69b' (x:=x) (f:=P)).
      apply MKT19b.
      pose proof Hfx as Hfx0.
      apply AxiomII in Hfx0 as [En _].
      exact En. }
    (* P[x] ≈ x *)
    assert (Hxn : P[x] ≈ x) by (apply MKT153; exact HEx).
    destruct Hxn as [f [Hf11 [Hfdom Hfran]]].
    destruct Hf11 as [Hf Hfinv].
    set (g := f⁻¹).
    assert (Hgg : Function1_1 g).
    { unfold g. split.
      - exact Hfinv.
      - assert (Hinv_inv : (f⁻¹)⁻¹ = f).
        { apply MKT61. exact (proj1 Hf). }
        rewrite Hinv_inv. exact Hf. }
    assert (Hgdom : dom(g) = x).
    { unfold g. rewrite MKT_dom_inv. exact Hfran. }
    assert (Hgran : ran(g) = P[x]).
    { unfold g. rewrite MKT_ran_inv. exact Hfdom. }
    (* injectivity of g *)
    assert (Hginj : ∀ u v, u ∈ dom(g) -> v ∈ dom(g) -> g[u] = g[v] -> u = v).
    { intros u v Hud Hvd Hguv.
      assert (Hug : [u, g[u]] ∈ g) by (apply (MKT_dom_val g u (proj1 Hgg)); exact Hud).
      assert (Hvg : [v, g[v]] ∈ g) by (apply (MKT_dom_val g v (proj1 Hgg)); exact Hvd).
      assert (Eu : Ensemble u).
      { assert (E : Ensemble ([u, g[u]])) by (unfold Ensemble; exists g; exact Hug).
        exact (proj1 (MKT49b u (g[u]) E)). }
      assert (Ev : Ensemble v).
      { assert (E : Ensemble ([v, g[v]])) by (unfold Ensemble; exists g; exact Hvg).
        exact (proj1 (MKT49b v (g[v]) E)). }
      assert (Egu : Ensemble (g[u])).
      { assert (E : Ensemble ([u, g[u]])) by (unfold Ensemble; exists g; exact Hug).
        exact (proj2 (MKT49b u (g[u]) E)). }
      assert (Egv : Ensemble (g[v])).
      { assert (E : Ensemble ([v, g[v]])) by (unfold Ensemble; exists g; exact Hvg).
        exact (proj2 (MKT49b v (g[v]) E)). }
      assert (Hwu : [g[u], u] ∈ f).
      { unfold g in Hug. apply (proj1 (MKT_inv_in f u (g[u]) Eu Egu)). exact Hug. }
      assert (Hwv : [g[v], v] ∈ f).
      { unfold g in Hvg. apply (proj1 (MKT_inv_in f v (g[v]) Ev Egv)). exact Hvg. }
      rewrite <- Hguv in Hwv.
      exact (proj2 Hf (g[u]) u v Hwu Hwv). }
    (* basic facts about g *)
    assert (Hdomval_g : ∀ u, u ∈ dom(g) -> [u, g[u]] ∈ g).
    { intros u Hu. apply (MKT_dom_val g u (proj1 Hgg)); exact Hu. }
    assert (HdomEns_g : ∀ u, u ∈ dom(g) -> Ensemble u).
    { intros u Hu.
      assert (E : Ensemble ([u, g[u]])) by (unfold Ensemble; exists g; exact (Hdomval_g u Hu)).
      exact (proj1 (MKT49b u (g[u]) E)). }
    assert (HranVal_g : ∀ u, u ∈ dom(g) -> g[u] ∈ ran(g)).
    { intros u Hu.
      apply AxiomII; split.
      - assert (E : Ensemble ([u, g[u]])) by (unfold Ensemble; exists g; exact (Hdomval_g u Hu)).
        exact (proj2 (MKT49b u (g[u]) E)).
      - exists u; exact (Hdomval_g u Hu). }
    assert (HranEns_g : ∀ u, u ∈ dom(g) -> Ensemble (g[u])).
    { intros u Hu.
      assert (E : Ensemble ([u, g[u]])) by (unfold Ensemble; exists g; exact (Hdomval_g u Hu)).
      exact (proj2 (MKT49b u (g[u]) E)). }
    assert (Hginfo : ∀ t, t ∈ x -> t ∈ dom(g) /\ Ensemble t /\ Ensemble (g[t])).
    { intros t Htx.
      assert (Htd : t ∈ dom(g)) by (rewrite Hgdom; exact Htx).
      split; [exact Htd | split].
      - exact (HdomEns_g t Htd).
      - exact (HranEns_g t Htd). }
    (* n = P[x] is an integer *)
    pose proof Hfx as Hnω.
    apply AxiomII in Hnω as [En HnInt].
    destruct HnInt as [HnOrd Hnwo_inv].
    assert (Hnwo : WellOrdered E (P[x])) by (apply MKT107; exact HnOrd).
    destruct HnOrd as [Hnconn Hnfull].
    destruct Hnwo as [Hnconn' Hnwosub].
    destruct Hnwo_inv as [Hnconn_inv Hnwosub_inv].
    (* define r *)
    set (r := \{\ λ u v, g[u] ∈ g[v] \}\).
    assert (Hr_char : ∀ u v, [u,v] ∈ r <-> Ensemble ([u,v]) /\ g[u] ∈ g[v]).
    { intros u v; split.
      - intros Huv.
        apply AxiomII in Huv as [Euv Huv].
        destruct Huv as [u' [v' [Huv' Hg']]].
        assert (Eu : Ensemble u) by (exact (proj1 (MKT49b u v Euv))).
        assert (Ev : Ensemble v) by (exact (proj2 (MKT49b u v Euv))).
        assert (Eu'v' : Ensemble ([u',v'])).
        { rewrite <- Huv'. exact Euv. }
        assert (Eu' : Ensemble u') by (exact (proj1 (MKT49b u' v' Eu'v'))).
        assert (Ev' : Ensemble v') by (exact (proj2 (MKT49b u' v' Eu'v'))).
        destruct (proj1 (MKT55 u v u' v' Eu Ev) Huv') as [Huu' Hvv'].
        split; [exact Euv |].
        rewrite <- Huu' in Hg'. rewrite <- Hvv' in Hg'. exact Hg'.
      - intros [Euv Hg].
        apply AxiomII; split; [exact Euv |].
        exists u; exists v; split; [reflexivity | exact Hg]. }
    (* WellOrdered r x *)
    assert (Hwo_r : WellOrdered r x).
    { split.
      - (* Connect r x *)
        unfold Connect.
        intros u v Hu Hv.
        assert (Hud : u ∈ dom(g)) by (rewrite Hgdom; exact Hu).
        assert (Hvd : v ∈ dom(g)) by (rewrite Hgdom; exact Hv).
        assert (Eu : Ensemble u) by (apply HdomEns_g; exact Hud).
        assert (Ev : Ensemble v) by (apply HdomEns_g; exact Hvd).
        assert (Egu : Ensemble (g[u])) by (apply HranEns_g; exact Hud).
        assert (Egv : Ensemble (g[v])) by (apply HranEns_g; exact Hvd).
        assert (Hgu : g[u] ∈ P[x]).
        { rewrite <- Hgran. exact (HranVal_g u Hud). }
        assert (Hgv : g[v] ∈ P[x]).
        { rewrite <- Hgran. exact (HranVal_g v Hvd). }
        destruct (Hnconn (g[u]) (g[v]) Hgu Hgv) as [Hguv | [Hgvu | Hgeq]].
        + left.
          assert (Hguv' : g[u] ∈ g[v]).
          { apply (proj1 (HE_mem (g[u]) (g[v]) Egu Egv)). exact Hguv. }
          unfold Rrelation.
          apply (proj2 (Hr_char u v)).
          split; [apply MKT49a; assumption | exact Hguv'].
        + right; left.
          assert (Hgvu' : g[v] ∈ g[u]).
          { apply (proj1 (HE_mem (g[v]) (g[u]) Egv Egu)). exact Hgvu. }
          unfold Rrelation.
          apply (proj2 (Hr_char v u)).
          split; [apply MKT49a; assumption | exact Hgvu'].
        + right; right.
          apply (Hginj u v Hud Hvd). exact Hgeq.
      - (* well-order property *)
        intros S HSx HSn.
        set (gS := \{ λ w, ∃ s, s ∈ S /\ w = g[s] \}).
        assert (HgSx : gS ⊂ P[x]).
        { intros w Hw.
          apply AxiomII in Hw as [Ew Hw].
          destruct Hw as [s [Hs Hwgs]].
          subst w.
          assert (Hsx : s ∈ x) by (exact (HSx s Hs)).
          assert (Hsd : s ∈ dom(g)) by (rewrite Hgdom; exact Hsx).
          rewrite <- Hgran. exact (HranVal_g s Hsd). }
        destruct (MKT_nonempty S HSn) as [s0 Hs0].
        assert (HgSn : gS ≠ Φ).
        { intro HgS0.
          assert (Hs0g : g[s0] ∈ gS).
          { apply AxiomII; split.
            - assert (Hs0x : s0 ∈ x) by (exact (HSx s0 Hs0)).
              assert (Hs0d : s0 ∈ dom(g)) by (rewrite Hgdom; exact Hs0x).
              exact (HranEns_g s0 Hs0d).
            - exists s0; split; [exact Hs0 | reflexivity]. }
          rewrite HgS0 in Hs0g.
          exact (MKT16 Hs0g). }
        destruct (Hnwosub gS HgSx HgSn) as [z [HzgS Hzfirst]].
        apply AxiomII in HzgS as [Ez HzgS].
        destruct HzgS as [s0' [Hs0' Hgs0']].
        exists s0'.
        split.
        + exact Hs0'.
        + intros t HtS Htr.
          apply (Hzfirst (g[t])).
          * apply AxiomII; split.
            -- destruct (Hginfo t (HSx t HtS)) as [Htd [Et Egt]].
               exact Egt.
            -- exists t; split; [exact HtS | reflexivity].
          * destruct (Hginfo t (HSx t HtS)) as [Htd [Et Egt]].
            assert (Hgt' : Ensemble ([t,s0']) /\ g[t] ∈ g[s0']).
            { apply (proj1 (Hr_char t s0')). exact Htr. }
            destruct Hgt' as [_ Hgt].
            assert (Hgtz : g[t] ∈ z) by (rewrite <- Hgs0' in Hgt; exact Hgt).
            unfold Rrelation.
            apply (proj2 (HE_mem (g[t]) z Egt Ez)).
            exact Hgtz. }
    (* WellOrdered (r⁻¹) x *)
    assert (Hwo_ri : WellOrdered (r⁻¹) x).
    { split.
      - (* Connect (r⁻¹) x *)
        unfold Connect.
        intros u v Hu Hv.
        assert (Hud : u ∈ dom(g)) by (rewrite Hgdom; exact Hu).
        assert (Hvd : v ∈ dom(g)) by (rewrite Hgdom; exact Hv).
        assert (Eu : Ensemble u) by (apply HdomEns_g; exact Hud).
        assert (Ev : Ensemble v) by (apply HdomEns_g; exact Hvd).
        assert (Egu : Ensemble (g[u])) by (apply HranEns_g; exact Hud).
        assert (Egv : Ensemble (g[v])) by (apply HranEns_g; exact Hvd).
        assert (Hgu : g[u] ∈ P[x]).
        { rewrite <- Hgran. exact (HranVal_g u Hud). }
        assert (Hgv : g[v] ∈ P[x]).
        { rewrite <- Hgran. exact (HranVal_g v Hvd). }
        destruct (Hnconn_inv (g[u]) (g[v]) Hgu Hgv) as [Hguv | [Hgvu | Hgeq]].
        + left.
          assert (Hgvu' : g[v] ∈ g[u]).
          { apply (proj1 (HE_mem (g[v]) (g[u]) Egv Egu)).
            apply (proj1 (MKT_inv_in E (g[u]) (g[v]) Egu Egv)).
            exact Hguv. }
          unfold Rrelation.
          apply (proj2 (MKT_inv_in r u v Eu Ev)).
          apply (proj2 (Hr_char v u)).
          split; [apply MKT49a; assumption | exact Hgvu'].
        + right; left.
          assert (Hguv' : g[u] ∈ g[v]).
          { apply (proj1 (HE_mem (g[u]) (g[v]) Egu Egv)).
            apply (proj1 (MKT_inv_in E (g[v]) (g[u]) Egv Egu)).
            exact Hgvu. }
          unfold Rrelation.
          apply (proj2 (MKT_inv_in r v u Ev Eu)).
          apply (proj2 (Hr_char u v)).
          split; [apply MKT49a; assumption | exact Hguv'].
        + right; right.
          apply (Hginj u v Hud Hvd). exact Hgeq.
      - (* well-order property *)
        intros S HSx HSn.
        set (gS := \{ λ w, ∃ s, s ∈ S /\ w = g[s] \}).
        assert (HgSx : gS ⊂ P[x]).
        { intros w Hw.
          apply AxiomII in Hw as [Ew Hw].
          destruct Hw as [s [Hs Hwgs]].
          subst w.
          assert (Hsx : s ∈ x) by (exact (HSx s Hs)).
          assert (Hsd : s ∈ dom(g)) by (rewrite Hgdom; exact Hsx).
          rewrite <- Hgran. exact (HranVal_g s Hsd). }
        destruct (MKT_nonempty S HSn) as [s0 Hs0].
        assert (HgSn : gS ≠ Φ).
        { intro HgS0.
          assert (Hs0g : g[s0] ∈ gS).
          { apply AxiomII; split.
            - assert (Hs0x : s0 ∈ x) by (exact (HSx s0 Hs0)).
              assert (Hs0d : s0 ∈ dom(g)) by (rewrite Hgdom; exact Hs0x).
              exact (HranEns_g s0 Hs0d).
            - exists s0; split; [exact Hs0 | reflexivity]. }
          rewrite HgS0 in Hs0g.
          exact (MKT16 Hs0g). }
        destruct (Hnwosub_inv gS HgSx HgSn) as [z [HzgS Hzfirst]].
        apply AxiomII in HzgS as [Ez HzgS].
        destruct HzgS as [s0' [Hs0' Hgs0']].
        exists s0'.
        split.
        + exact Hs0'.
        + intros t HtS Htri.
          apply (Hzfirst (g[t])).
          * apply AxiomII; split.
            -- destruct (Hginfo t (HSx t HtS)) as [Htd [Et Egt]].
               exact Egt.
            -- exists t; split; [exact HtS | reflexivity].
          * destruct (Hginfo t (HSx t HtS)) as [Htd [Et Egt]].
            destruct (Hginfo s0' (HSx s0' Hs0')) as [Hs0d [Es0 _]].
            assert (Hs0t : [s0', t] ∈ r).
            { apply (proj1 (MKT_inv_in r t s0' Et Es0)). exact Htri. }
            assert (Hgs0t' : Ensemble ([s0',t]) /\ g[s0'] ∈ g[t]).
            { apply (proj1 (Hr_char s0' t)). exact Hs0t. }
            destruct Hgs0t' as [_ Hgs0t].
            assert (Hzt : z ∈ g[t]) by (rewrite <- Hgs0' in Hgs0t; exact Hgs0t).
            unfold Rrelation.
            apply (proj2 (MKT_inv_in E (g[t]) z Egt Ez)).
            apply (proj2 (HE_mem z (g[t]) Ez Egt)).
            exact Hzt. }
    exists r.
    split; [exact Hwo_r | exact Hwo_ri].
  - (* (∃ r, WellOrdered r x /\ WellOrdered (r⁻¹) x) -> Finite x *)
    intros [r [Hwo_r Hwo_ri]].
    (* WellOrdered E ω *)
    assert (Hwo_omega : WellOrdered E ω).
    { apply MKT107.
      pose proof MKT138 as HωR.
      apply AxiomII in HωR as [_ Hωord].
      exact Hωord. }
    (* MARKER_MKT99 *)
    destruct (MKT99 (r:=r) (s:=E) (x:=x) (y:=ω) Hwo_r Hwo_omega)
      as [f [Hffunc [Hfop Hmax]]].
    destruct (OPXY_c f x ω r E Hfop) as [Hf' [Hfpr [Hfds Hfrs]]].
    assert (Hf11 : Function1_1 f).
    { apply (MKT96a (f:=f) (r:=r) (s:=E)). exact Hfpr. }
    destruct Hf11 as [Hff Hfinv].
    assert (Hfinvpr : Order_Pr (f⁻¹) E r).
    { apply (MKT96b (f:=f) (r:=r) (s:=E)). exact Hfpr. }
    assert (Hord_inv : ∀ u v, u ∈ dom(f⁻¹) -> v ∈ dom(f⁻¹)
      -> Rrelation u E v -> Rrelation (f⁻¹)[u] r (f⁻¹)[v]).
    { intros u v Hud Hvd Huv.
      exact (proj2 (proj2 (proj2 Hfinvpr)) u v Hud Hvd Huv). }
    (* A section S of x equivalent to ω has no r⁻¹-least element *)
    assert (Hno_least : ∀ S, S ⊂ x -> S ≠ Φ -> S = dom(f)
      -> ran(f) = ω -> False).
    { intros S HSx HSn HSdom Hfranw.
      destruct Hwo_ri as [Hconn_ri Hwosub_ri].
      destruct (Hwosub_ri S HSx HSn) as [z [HzS Hzfirst]].
      assert (Hzd : z ∈ dom(f)) by (rewrite <- HSdom; exact HzS).
      assert (Hzf : [z, f[z]] ∈ f) by (apply (MKT_dom_val f z Hff); exact Hzd).
      assert (Ez : Ensemble z).
      { assert (E : Ensemble ([z, f[z]])) by (unfold Ensemble; exists f; exact Hzf).
        exact (proj1 (MKT49b z (f[z]) E)). }
      assert (Efz : Ensemble (f[z])).
      { assert (E : Ensemble ([z, f[z]])) by (unfold Ensemble; exists f; exact Hzf).
        exact (proj2 (MKT49b z (f[z]) E)). }
      assert (Hfzran : f[z] ∈ ran(f)).
      { apply AxiomII; split; [exact Efz | exists z; exact Hzf]. }
      assert (Hfzw : f[z] ∈ ω) by (rewrite <- Hfranw; exact Hfzran).
      assert (Hpofz : PlusOne (f[z]) ∈ ω) by (apply MKT134; exact Hfzw).
      set (y := (f⁻¹)[PlusOne (f[z])]).
      assert (Hpo : PlusOne (f[z]) ∈ dom(f⁻¹)).
      { rewrite MKT_dom_inv. rewrite Hfranw. exact Hpofz. }
      assert (Hyv : [PlusOne (f[z]), (f⁻¹)[PlusOne (f[z])]] ∈ f⁻¹).
      { apply (MKT_dom_val (f⁻¹) (PlusOne (f[z])) Hfinv). exact Hpo. }
      assert (Epo : Ensemble (PlusOne (f[z]))).
      { assert (E : Ensemble ([PlusOne (f[z]), (f⁻¹)[PlusOne (f[z])]]))
          by (unfold Ensemble; exists (f⁻¹); exact Hyv).
        exact (proj1 (MKT49b (PlusOne (f[z])) ((f⁻¹)[PlusOne (f[z])]) E)). }
      assert (Ey : Ensemble y).
      { assert (E : Ensemble ([PlusOne (f[z]), (f⁻¹)[PlusOne (f[z])]]))
          by (unfold Ensemble; exists (f⁻¹); exact Hyv).
        exact (proj2 (MKT49b (PlusOne (f[z])) ((f⁻¹)[PlusOne (f[z])]) E)). }
      assert (Hyd : y ∈ dom(f)).
      { unfold y.
        apply AxiomII; split.
        - exact Ey.
        - exists (PlusOne (f[z])).
          apply (proj1 (MKT_inv_in f (PlusOne (f[z])) y Epo Ey)).
          exact Hyv. }
      assert (Hinv_fz : (f⁻¹)[f[z]] = z).
      { apply (MKT_fval (f⁻¹) (f[z]) z Hfinv).
        apply (proj2 (MKT_inv_in f (f[z]) z Efz Ez)).
        exact Hzf. }
      assert (HfzE : Rrelation (f[z]) E (PlusOne (f[z]))).
      { unfold Rrelation.
        apply (proj2 (HE_mem (f[z]) (PlusOne (f[z])) Efz Epo)).
        unfold PlusOne.
        apply (proj1 (MKT4 (f[z]) ([f[z]]) (f[z]))).
        right.
        apply (proj2 (MKT41 (f[z]) Efz (f[z]))).
        reflexivity. }
      assert (Hzy : Rrelation z r y).
      { rewrite <- Hinv_fz.
        unfold y.
        apply (Hord_inv (f[z]) (PlusOne (f[z]))).
        - rewrite MKT_dom_inv. rewrite Hfranw. exact Hfzw.
        - rewrite MKT_dom_inv. rewrite Hfranw. exact Hpofz.
        - exact HfzE. }
      assert (Hyriz : Rrelation y (r⁻¹) z).
      { unfold Rrelation.
        apply (proj2 (MKT_inv_in r y z Ey Ez)).
        exact Hzy. }
      assert (HyS : y ∈ S) by (rewrite HSdom; exact Hyd).
      exact (Hzfirst y HyS Hyriz). }
    destruct Hmax as [Hdomx | Hranw].
    + (* Case A: dom(f) = x *)
      destruct (classic (ran(f) = ω)) as [Hran_eq | Hran_ne].
      * (* ran(f) = ω -> contradiction *)
        exfalso.
        apply (Hno_least x (MKT26a x)).
        -- intro Hx0.
           assert (HΦran : Φ ∈ ran(f)) by (rewrite Hran_eq; exact MKT135a).
           apply AxiomII in HΦran as [EΦ' HΦran].
           destruct HΦran as [a Ha].
           assert (Hud : a ∈ dom(f)).
           { apply AxiomII; split.
             - assert (E : Ensemble ([a, Φ])) by (unfold Ensemble; exists f; exact Ha).
               exact (proj1 (MKT49b a Φ E)).
             - exists Φ; exact Ha. }
           rewrite Hdomx in Hud. rewrite Hx0 in Hud.
           exact (MKT16 Hud).
        -- symmetry. exact Hdomx.
        -- exact Hran_eq.
      * (* ran(f) ≠ ω -> ran(f) ∈ ω -> Finite x *)
        assert (Hranfull : Full ran(f)).
        { unfold Full.
          intros m Hm.
          destruct Hfrs as [Hran_sub [Hwo_ran Hran_close]].
          assert (Hmω : m ∈ ω) by (exact (Hran_sub m Hm)).
          pose proof Hmω as Hmω0.
          apply AxiomII in Hmω0 as [Em HmInt].
          intros n Hnm.
          assert (En : Ensemble n) by (unfold Ensemble; eauto).
          assert (Hnω : n ∈ ω).
          { apply (proj2 (AxiomII n (λ x, Integer x))).
            split; [exact En | exact (MKT132 m n HmInt Hnm)]. }
          apply (Hran_close n m Hnω Hm).
          unfold Rrelation.
          apply (proj2 (HE_mem n m En Em)).
          exact Hnm. }
        assert (Hranω : ran(f) ∈ ω).
        { apply (MKT108 ω (ran(f))).
          - pose proof MKT138 as HωR.
            apply AxiomII in HωR as [_ Hωord]. exact Hωord.
          - destruct Hfrs as [Hran_sub _]. exact Hran_sub.
          - exact Hran_ne.
          - exact Hranfull. }
        assert (Hxran : x ≈ ran(f)).
        { exists f; split; [split; [exact Hff | exact Hfinv] | split; [exact Hdomx | reflexivity]]. }
        pose proof Hranω as Hranω0.
        apply AxiomII in Hranω0 as [Eran _].
        assert (HEx : Ensemble x) by (apply (H_eq_Ens x ran(f) Hxran Eran)).
        assert (Hpx : P[x] = ran(f)).
        { assert (Hpr : P[x] = P[ran(f)]).
          { apply (proj2 (MKT154 x ran(f) HEx Eran)). exact Hxran. }
          rewrite Hpr.
          assert (HranC : ran(f) ∈ C) by (apply MKT164; exact Hranω).
          exact (proj2 (proj2 (MKT156 ran(f)) HranC)). }
        unfold Finite. rewrite Hpx. exact Hranω.
    + (* Case B: ran(f) = ω *)
      destruct Hfds as [Hdom_sub _].
      assert (Hdom_ne : dom(f) ≠ Φ).
      { intro Hd0.
        assert (HΦran : Φ ∈ ran(f)) by (rewrite Hranw; exact MKT135a).
        apply AxiomII in HΦran as [EΦ' HΦran].
        destruct HΦran as [a Ha].
        assert (Hud : a ∈ dom(f)).
        { apply AxiomII; split.
          - assert (E : Ensemble ([a, Φ])) by (unfold Ensemble; exists f; exact Ha).
            exact (proj1 (MKT49b a Φ E)).
          - exists Φ; exact Ha. }
        rewrite Hd0 in Hud.
        exact (MKT16 Hud). }
      exfalso.
      apply (Hno_least dom(f) Hdom_sub Hdom_ne eq_refl Hranw).
Qed.

Theorem MKT168 : ∀ x y, Finite x -> Finite y -> Finite (x ∪ y).
Proof.
  intros x y Hfx Hfy.
  unfold Finite in Hfx, Hfy.
  destruct (proj1 (MKT167 x) Hfx) as [r [Hwor Hwori]].
  destruct (proj1 (MKT167 y) Hfy) as [s [Hwos Hwosi]].
  set (x0 := x ~ y).
  assert (Hx0x : x0 ⊂ x).
  { intros z Hz0. unfold x0 in Hz0. apply AxiomII in Hz0 as [E [Hzx _]]. exact Hzx. }
  assert (Hx0ny : ∀ z, z ∈ x0 -> z ∉ y).
  { intros z Hz0. unfold x0 in Hz0.
    apply AxiomII in Hz0 as [E [Hzx Hzn]].
    apply AxiomII in Hzn as [E' Hn]. exact Hn. }
  assert (Hyx0 : ∀ z, z ∈ y -> z ∉ x0).
  { intros z Hzy Hz0. exact (Hx0ny z Hz0 Hzy). }
  assert (Hwo_r_x0 : WellOrdered r x0).
  { apply (MKT_wo_sub r x0 x Hx0x Hwor). }
  assert (Hwo_ri_x0 : WellOrdered (r⁻¹) x0).
  { apply (MKT_wo_sub (r⁻¹) x0 x Hx0x Hwori). }
  assert (Hunion : ∀ z, z ∈ x ∪ y -> z ∈ x0 \/ z ∈ y).
  { intros z Hz.
    apply AxiomII in Hz as [Ez Hz].
    destruct Hz as [Hzx | Hzy].
    - destruct (classic (z ∈ y)) as [Hzy' | Hzny].
      + right; exact Hzy'.
      + left; apply AxiomII; split; [exact Ez | split; [exact Hzx |
          apply AxiomII; split; [exact Ez | exact Hzny]]].
    - right; exact Hzy. }
  set (t := \{\ λ a b, (a ∈ x0 /\ b ∈ y)
       \/ (a ∈ x0 /\ b ∈ x0 /\ Rrelation a r b)
       \/ (a ∈ y /\ b ∈ y /\ Rrelation a s b) \}\).
  assert (Ht_char : ∀ a b, Ensemble a -> Ensemble b ->
    ([a,b] ∈ t <-> (a ∈ x0 /\ b ∈ y)
       \/ (a ∈ x0 /\ b ∈ x0 /\ Rrelation a r b)
       \/ (a ∈ y /\ b ∈ y /\ Rrelation a s b))).
  { intros a b Ea Eb; split.
    - intros Hab.
      apply AxiomII in Hab as [Eab Hab].
      destruct Hab as [u [v [Huv Hcl]]].
      assert (Euv : Ensemble ([u,v])) by (rewrite <- Huv; exact Eab).
      destruct (MKT49b u v Euv) as [Eu Ev].
      destruct (proj1 (MKT55 u v a b Eu Ev) (eq_sym Huv)) as [Hua Hbv].
      destruct Hcl as [H1 | [H2 | H3]].
      + left. destruct H1 as [Hux0 Hvy].
        split; [rewrite Hua in Hux0; exact Hux0 | rewrite Hbv in Hvy; exact Hvy].
      + right; left. destruct H2 as [Hux0 [Hvx0 Huvr]].
        rewrite Hua in Hux0. rewrite Hbv in Hvx0.
        rewrite Hua in Huvr. rewrite Hbv in Huvr.
        split; [exact Hux0 | split; [exact Hvx0 | exact Huvr]].
      + right; right. destruct H3 as [Huy [Hvy Huvs]].
        rewrite Hua in Huy. rewrite Hbv in Hvy.
        rewrite Hua in Huvs. rewrite Hbv in Huvs.
        split; [exact Huy | split; [exact Hvy | exact Huvs]].
    - intros Hcl.
      apply AxiomII; split.
      + apply MKT49a; assumption.
      + exists a; exists b; split; [reflexivity | exact Hcl]. }
  assert (Hwo_t : WellOrdered t (x ∪ y)).
  { unfold WellOrdered; split.
    - unfold Connect.
      intros u v Hu Hv.
      pose proof Hu as Hu_union.
      pose proof Hv as Hv_union.
      apply AxiomII in Hu as [Eu Hu].
      apply AxiomII in Hv as [Ev Hv].
      destruct (Hunion u Hu_union) as [Hux0 | Huy];
      destruct (Hunion v Hv_union) as [Hvx0 | Hvy].
      + destruct (proj1 Hwo_r_x0 u v Hux0 Hvx0) as [Huv | [Hvu | Heq]].
        * left. unfold Rrelation.
          apply (proj2 (Ht_char u v Eu Ev)).
          right; left. split; [exact Hux0 | split; [exact Hvx0 | exact Huv]].
        * right; left. unfold Rrelation.
          apply (proj2 (Ht_char v u Ev Eu)).
          right; left. split; [exact Hvx0 | split; [exact Hux0 | exact Hvu]].
        * right; right. exact Heq.
      + left. unfold Rrelation.
        apply (proj2 (Ht_char u v Eu Ev)).
        left. split; [exact Hux0 | exact Hvy].
      + right; left. unfold Rrelation.
        apply (proj2 (Ht_char v u Ev Eu)).
        left. split; [exact Hvx0 | exact Huy].
      + destruct (proj1 Hwos u v Huy Hvy) as [Huv | [Hvu | Heq]].
        * left. unfold Rrelation.
          apply (proj2 (Ht_char u v Eu Ev)).
          right; right. split; [exact Huy | split; [exact Hvy | exact Huv]].
        * right; left. unfold Rrelation.
          apply (proj2 (Ht_char v u Ev Eu)).
          right; right. split; [exact Hvy | split; [exact Huy | exact Hvu]].
        * right; right. exact Heq.
    - intros S HSx HSn.
      set (T := \{ λ w, w ∈ S /\ w ∈ x0 \}).
      assert (HTx : T ⊂ x0).
      { intros w Hw. apply AxiomII in Hw as [E [HwS Hwx0]]. exact Hwx0. }
      destruct (classic (T ≠ Φ)) as [HTn | HTn0].
      + destruct (proj2 Hwo_r_x0 T HTx HTn) as [z [HzT Hzleast]].
        apply AxiomII in HzT as [Ez [HzS Hzx0]].
        exists z. unfold FirstMember. split; [exact HzS |].
        intros w HwS Hwz.
        assert (Ew : Ensemble w).
        { pose proof (HSx w HwS) as Hwu. apply AxiomII in Hwu as [Ew _]. exact Ew. }
        destruct (Hunion w (HSx w HwS)) as [Hwx0' | Hwy].
        * destruct (proj1 (Ht_char w z Ew Ez) Hwz) as [H1 | [H2 | H3]].
          -- destruct H1 as [Hw0 Hzy]. exact (Hx0ny z Hzx0 Hzy).
          -- destruct H2 as [Hw0 [Hzx0' Hwzr]].
             apply (Hzleast w).
             ++ apply AxiomII; split; [exact Ew | split; [exact HwS | exact Hw0]].
             ++ exact Hwzr.
          -- destruct H3 as [Hwy2 [Hzy Hwzs]]. exact (Hx0ny z Hzx0 Hzy).
        * destruct (proj1 (Ht_char w z Ew Ez) Hwz) as [H1 | [H2 | H3]].
          -- destruct H1 as [Hw0 Hzy]. exact (Hyx0 w Hwy Hw0).
          -- destruct H2 as [Hw0 _]. exact (Hyx0 w Hwy Hw0).
          -- destruct H3 as [_ [Hzy _]]. exact (Hx0ny z Hzx0 Hzy).
      + assert (HT : T = Φ) by (exact (proj1 (NNPP (T = Φ)) HTn0)).
        assert (HSy : S ⊂ y).
        { intros w HwS.
          destruct (Hunion w (HSx w HwS)) as [Hwx0 | Hwy].
          - exfalso.
            assert (Ew : Ensemble w) by (pose proof (HSx w HwS) as Hwu; apply AxiomII in Hwu as [Ew _]; exact Ew).
            assert (HwΦ : w ∈ Φ).
            { rewrite <- HT. apply AxiomII; split; [exact Ew | split; [exact HwS | exact Hwx0]]. }
            exact (MKT16 HwΦ).
          - exact Hwy. }
        destruct (proj2 Hwos S HSy HSn) as [z [HzS Hzleast]].
        assert (Ez : Ensemble z) by (pose proof (HSx z HzS) as Hzun; apply AxiomII in Hzun as [Ez _]; exact Ez).
        exists z. unfold FirstMember. split; [exact HzS |].
        intros w HwS Hwz.
        assert (Ew : Ensemble w) by (pose proof (HSx w HwS) as Hwu; apply AxiomII in Hwu as [Ew _]; exact Ew).
        assert (Hwy : w ∈ y) by (exact (HSy w HwS)).
        destruct (proj1 (Ht_char w z Ew Ez) Hwz) as [H1 | [H2 | H3]].
        * apply (Hyx0 w Hwy). exact (proj1 H1).
        * destruct H2 as [Hw0 [_ _]]. exact (Hyx0 w Hwy Hw0).
        * destruct H3 as [_ [Hzy Hwzs]].
          apply (Hzleast w HwS). exact Hwzs. }
  assert (Hwo_ti : WellOrdered (t⁻¹) (x ∪ y)).
  { unfold WellOrdered; split.
    - unfold Connect.
      intros u v Hu Hv.
      pose proof Hu as Hu_union.
      pose proof Hv as Hv_union.
      apply AxiomII in Hu as [Eu Hu].
      apply AxiomII in Hv as [Ev Hv].
      destruct (Hunion u Hu_union) as [Hux0 | Huy];
      destruct (Hunion v Hv_union) as [Hvx0 | Hvy].
      + destruct (proj1 Hwo_ri_x0 u v Hux0 Hvx0) as [Huv | [Hvu | Heq]].
        * left. unfold Rrelation.
          apply (proj2 (MKT_inv_in t u v Eu Ev)).
          apply (proj2 (Ht_char v u Ev Eu)).
          right; left. split; [exact Hvx0 | split; [exact Hux0 |]].
          apply (proj1 (MKT_inv_in r u v Eu Ev)). exact Huv.
        * right; left. unfold Rrelation.
          apply (proj2 (MKT_inv_in t v u Ev Eu)).
          apply (proj2 (Ht_char u v Eu Ev)).
          right; left. split; [exact Hux0 | split; [exact Hvx0 |]].
          apply (proj1 (MKT_inv_in r v u Ev Eu)). exact Hvu.
        * right; right. exact Heq.
      + right; left. unfold Rrelation.
        apply (proj2 (MKT_inv_in t v u Ev Eu)).
        apply (proj2 (Ht_char u v Eu Ev)).
        left. split; [exact Hux0 | exact Hvy].
      + left. unfold Rrelation.
        apply (proj2 (MKT_inv_in t u v Eu Ev)).
        apply (proj2 (Ht_char v u Ev Eu)).
        left. split; [exact Hvx0 | exact Huy].
      + destruct (proj1 Hwosi u v Huy Hvy) as [Huv | [Hvu | Heq]].
        * left. unfold Rrelation.
          apply (proj2 (MKT_inv_in t u v Eu Ev)).
          apply (proj2 (Ht_char v u Ev Eu)).
          right; right. split; [exact Hvy | split; [exact Huy |]].
          apply (proj1 (MKT_inv_in s u v Eu Ev)). exact Huv.
        * right; left. unfold Rrelation.
          apply (proj2 (MKT_inv_in t v u Ev Eu)).
          apply (proj2 (Ht_char u v Eu Ev)).
          right; right. split; [exact Huy | split; [exact Hvy |]].
          apply (proj1 (MKT_inv_in s v u Ev Eu)). exact Hvu.
        * right; right. exact Heq.
    - intros S HSx HSn.
      set (T := \{ λ w, w ∈ S /\ w ∈ y \}).
      assert (HTx : T ⊂ y).
      { intros w Hw. apply AxiomII in Hw as [E [HwS Hwy]]. exact Hwy. }
      destruct (classic (T ≠ Φ)) as [HTn | HTn0].
      + destruct (proj2 Hwosi T HTx HTn) as [z [HzT Hzleast]].
        apply AxiomII in HzT as [Ez [HzS Hzy]].
        exists z. unfold FirstMember. split; [exact HzS |].
        intros w HwS Hwzt.
        assert (Ew : Ensemble w) by (pose proof (HSx w HwS) as Hwu; apply AxiomII in Hwu as [Ew _]; exact Ew).
        assert (Hzwt : [z,w] ∈ t).
        { apply (proj1 (MKT_inv_in t w z Ew Ez)). exact Hwzt. }
        destruct (Hunion w (HSx w HwS)) as [Hwx0 | Hwy'].
        * destruct (proj1 (Ht_char z w Ez Ew) Hzwt) as [H1 | [H2 | H3]].
          -- destruct H1 as [Hz0 Hw1]. exact (Hyx0 z Hzy Hz0).
          -- destruct H2 as [Hz0 [_ _]]. exact (Hyx0 z Hzy Hz0).
          -- destruct H3 as [_ [Hwy2 _]]. exact (Hyx0 w Hwy2 Hwx0).
        * destruct (proj1 (Ht_char z w Ez Ew) Hzwt) as [H1 | [H2 | H3]].
          -- destruct H1 as [Hz0 Hw1]. exact (Hyx0 z Hzy Hz0).
          -- destruct H2 as [Hz0 [_ _]]. exact (Hyx0 z Hzy Hz0).
          -- destruct H3 as [_ [Hwy2 Hzws]].
             apply (Hzleast w).
             ++ apply AxiomII; split; [exact Ew | split; [exact HwS | exact Hwy']].
             ++ apply (proj2 (MKT_inv_in s w z Ew Ez)). exact Hzws.
      + assert (HT : T = Φ) by (exact (proj1 (NNPP (T = Φ)) HTn0)).
        assert (HSx0 : S ⊂ x0).
        { intros w HwS.
          destruct (Hunion w (HSx w HwS)) as [Hwx0 | Hwy].
          - exact Hwx0.
          - exfalso.
            assert (Ew : Ensemble w) by (pose proof (HSx w HwS) as Hwu; apply AxiomII in Hwu as [Ew _]; exact Ew).
            assert (HwΦ : w ∈ Φ).
            { rewrite <- HT. apply AxiomII; split; [exact Ew | split; [exact HwS | exact Hwy]]. }
            exact (MKT16 HwΦ). }
        destruct (proj2 Hwo_ri_x0 S HSx0 HSn) as [z [HzS Hzleast]].
        assert (Ez : Ensemble z) by (pose proof (HSx z HzS) as Hzun; apply AxiomII in Hzun as [Ez _]; exact Ez).
        assert (Hzx0 : z ∈ x0) by (exact (HSx0 z HzS)).
        exists z. unfold FirstMember. split; [exact HzS |].
        intros w HwS Hwzt.
        assert (Ew : Ensemble w) by (pose proof (HSx w HwS) as Hwu; apply AxiomII in Hwu as [Ew _]; exact Ew).
        assert (Hzwt : [z,w] ∈ t).
        { apply (proj1 (MKT_inv_in t w z Ew Ez)). exact Hwzt. }
        assert (Hwx0 : w ∈ x0) by (exact (HSx0 w HwS)).
        destruct (proj1 (Ht_char z w Ez Ew) Hzwt) as [H1 | [H2 | H3]].
        * destruct H1 as [_ Hw1]. exact (Hyx0 w Hw1 Hwx0).
        * destruct H2 as [_ [Hwx0' Hzwr]].
          apply (Hzleast w HwS).
          apply (proj2 (MKT_inv_in r w z Ew Ez)). exact Hzwr.
        * destruct H3. exact (Hyx0 z H Hzx0). }
  apply (proj2 (MKT167 (x ∪ y))).
  exists t; split; assumption.
Qed.

Theorem MKT169 : ∀ x, Finite x -> (∀ z, z ∈ x -> Finite z)
  -> Finite (∪ x).
Proof.
  intros x Hfx Hfin.
  assert (HEx : Ensemble x).
  { apply NNPP; intro Hnx.
    assert (Hxmu : x ∉ μ).
    { intro Hx. apply Hnx. apply (MKT19a x Hx). }
    rewrite <- MKT152b in Hxmu.
    assert (Hpx : P[x] = μ) by (apply (MKT69a (x:=x) (f:=P)); exact Hxmu).
    assert (Hmuw : μ ∈ ω) by (rewrite <- Hpx; exact Hfx).
    assert (HmuC : μ ∈ C) by (exact (MKT164 μ Hmuw)).
    assert (HmuE : Ensemble μ) by (exact (proj1 (proj2 (MKT156 μ) HmuC))).
    exact (MKT39 HmuE). }
  assert (HxP : x ≈ P[x]).
  { apply (MKT146 (MKT153 HEx)). }
  assert (Finite_Φ : Finite Φ).
  { unfold Finite.
    assert (HΦC : Φ ∈ C) by (apply MKT164; exact MKT135a).
    assert (HpΦ : P[Φ] = Φ) by (exact (proj2 (proj2 (MKT156 Φ) HΦC))).
    rewrite HpΦ. exact MKT135a. }
  assert (HxΦeq : ∀ x, x ≈ Φ -> x = Φ).
  { intros x0 Hx0.
    apply AxiomI; intros z; split.
    - intros Hzx0.
      exfalso.
      assert (Ez : Ensemble z) by (exists x0; exact Hzx0).
      destruct Hx0 as [f [Hf11 [Hdom Hran]]].
      assert (Hzd : z ∈ dom(f)) by (rewrite Hdom; exact Hzx0).
      assert (Hfz : [z, f[z]] ∈ f) by (apply (MKT_dom_val f z (proj1 Hf11) Hzd)).
      assert (Efz : Ensemble (f[z])).
      { assert (E : Ensemble ([z, f[z]])) by (unfold Ensemble; exists f; exact Hfz).
        exact (proj2 (MKT49b z (f[z]) E)). }
      assert (Hfzr : f[z] ∈ ran(f)).
      { apply AxiomII; split; [exact Efz | exists z; exact Hfz]. }
      rewrite Hran in Hfzr.
      apply AxiomII in Hfzr as [E Hfzr'].
      exact (Hfzr' eq_refl).
    - intros Hz.
      apply AxiomII in Hz as [E Hneq].
      exfalso; apply Hneq; reflexivity. }
  assert (Hunion_dist : ∀ p q, ∪(p ∪ q) = (∪p) ∪ (∪q)).
  { intros p q. apply AxiomI; intros z; split.
    - intros Hz.
      apply AxiomII in Hz as [Ez Hz].
      destruct Hz as [w [Hzw Hw]].
      apply AxiomII in Hw as [Ew Hw].
      destruct Hw as [Hwp | Hwq].
      + apply AxiomII; split; [exact Ez | left; apply AxiomII; split; [exact Ez | exists w; split; [exact Hzw | exact Hwp]]].
      + apply AxiomII; split; [exact Ez | right; apply AxiomII; split; [exact Ez | exists w; split; [exact Hzw | exact Hwq]]].
    - intros Hz.
      apply AxiomII in Hz as [Ez Hz].
      destruct Hz as [Hzp | Hzq].
      + apply AxiomII in Hzp as [Ez' Hzp].
        destruct Hzp as [w [Hzw Hwp]].
        apply AxiomII; split; [exact Ez | exists w; split; [exact Hzw | apply AxiomII; split; [unfold Ensemble; eauto | left; exact Hwp]]].
      + apply AxiomII in Hzq as [Ez' Hzq].
        destruct Hzq as [w [Hzw Hwq]].
        apply AxiomII; split; [exact Ez | exists w; split; [exact Hzw | apply AxiomII; split; [unfold Ensemble; eauto | right; exact Hwq]]]. }
  set (S := \{ λ n, n ∈ ω /\ (∀ x, x ≈ n -> (∀ z, z ∈ x -> Finite z) -> Finite (∪x)) \}).
  assert (HSω : S ⊂ ω).
  { intros n Hn. apply AxiomII in Hn as [E Hn]. destruct Hn as [Hnω _]. exact Hnω. }
  assert (HΦS : Φ ∈ S).
  { apply AxiomII; split.
    - destruct AxiomVIII as [y8 [Hy8E [HΦ8 _]]].
      unfold Ensemble; exists y8; exact HΦ8.
    - split.
      + exact MKT135a.
      + intros x0 Hx0 Hfin0.
        rewrite (HxΦeq x0 Hx0).
        rewrite MKT24'.
        exact Finite_Φ. }
  assert (HsuccS : ∀ u, u ∈ S -> PlusOne u ∈ S).
  { intros u Hu.
    apply AxiomII in Hu as [Eu Hu].
    destruct Hu as [Huω HuIH].
    apply AxiomII; split.
    - exact (proj1 (proj1 (AxiomII (PlusOne u) (λ x, Integer x)) (MKT134 Huω))).
    - split.
      + exact (MKT134 Huω).
      + intros y0 Hy0su Hfiny0.
        destruct Hy0su as [f [Hf11 [Hdom Hran]]].
        destruct Hf11 as [Hf Hfinv].
        set (g := f⁻¹).
        assert (Hg : Function g) by (unfold g; exact Hfinv).
        assert (Hg11 : Function1_1 g).
        { unfold g. split; [exact Hfinv |].
          assert (Hinv_inv : (f⁻¹)⁻¹ = f) by (apply MKT61; exact (proj1 Hf)).
          rewrite Hinv_inv. exact Hf. }
        assert (Hgdom : dom(g) = PlusOne u).
        { unfold g. rewrite MKT_dom_inv. exact Hran. }
        assert (Hgran : ran(g) = y0).
        { unfold g. rewrite MKT_ran_inv. exact Hdom. }
        assert (HuEns : Ensemble u).
        { apply AxiomII in Huω as [HuEns _]. exact HuEns. }
        set (a := g[u]).
        assert (Hud : u ∈ dom(g)).
        { rewrite Hgdom.
          unfold PlusOne.
          apply (proj1 (MKT4 u ([u]) u)). right.
          apply (proj2 (MKT41 u HuEns u)). reflexivity. }
        assert (Hua : [u, a] ∈ g).
        { unfold a. apply (MKT_dom_val g u Hg). exact Hud. }
        assert (Ea : Ensemble a).
        { assert (E : Ensemble ([u, a])) by (unfold Ensemble; exists g; exact Hua).
          exact (proj2 (MKT49b u a E)). }
        assert (Hax : a ∈ y0).
        { assert (Eg : Ensemble (g[u])).
          { assert (E : Ensemble ([u, g[u]])) by (unfold Ensemble; exists g; exact Hua).
            exact (proj2 (MKT49b u (g[u]) E)). }
          assert (Hgran_mem : g[u] ∈ ran(g)).
          { apply AxiomII; split; [exact Eg | exists u; exact Hua]. }
          unfold a. rewrite <- Hgran. exact Hgran_mem. }
        set (h := g | (u)).
        set (x' := ran(h)).
        assert (Hh_sub_g : h ⊂ g).
        { intros p Hp. unfold h. apply AxiomII in Hp as [E Hp]. destruct Hp as [Hpg _]. exact Hpg. }
        assert (Hhi_sub_gi : h⁻¹ ⊂ g⁻¹).
        { intros p Hp.
          apply AxiomII in Hp as [Ep Hp].
          destruct Hp as [a' [b' [Hpab Hba]]].
          assert (Ea'b' : Ensemble ([a',b'])).
          { rewrite <- Hpab. exact Ep. }
          destruct (MKT49b a' b' Ea'b') as [Ea' Eb'].
          assert (Eb'a' : Ensemble ([b',a'])).
          { apply MKT49a; assumption. }
          apply AxiomII; split; [exact Ep |].
          exists a'; exists b'; split; [exact Hpab |].
          exact (Hh_sub_g ([b',a']) Hba). }
        assert (Hhi_func : Function (h⁻¹)).
        { unfold Function; split.
          - intros z Hz. apply AxiomII in Hz as [E Hz]. destruct Hz as [a' [b' [Hzb _]]]. exists a'; exists b'; exact Hzb.
          - intros a' b' c' Hab Hac.
            assert (Eab : Ensemble ([a',b'])) by (unfold Ensemble; exists (h⁻¹); exact Hab).
            destruct (MKT49b a' b' Eab) as [Ea' Eb'].
            assert (Eac : Ensemble ([a',c'])) by (unfold Ensemble; exists (h⁻¹); exact Hac).
            destruct (MKT49b a' c' Eac) as [Ea'0 Ec'].
            exact (proj2 (proj2 Hg11) a' b' c' (Hhi_sub_gi ([a',b']) Hab) (Hhi_sub_gi ([a',c']) Hac)). }
        assert (Hh_func : Function h) by (apply (MKT126a g u Hg)).
        assert (Hh11 : Function1_1 h) by (split; assumption).
        assert (Hhdom : dom(h) = u).
        { unfold h.
          rewrite (MKT126b g u Hg).
          apply (proj2 (MKT30 u (dom(g)))).
          intros t Htu.
          rewrite Hgdom.
          unfold PlusOne.
          apply (proj1 (MKT4 u ([u]) t)). left. exact Htu. }
        assert (Hx'u : x' ≈ u).
        { apply (MKT146).
          exists h; split; [exact Hh11 | split; [exact Hhdom | unfold x'; reflexivity]]. }
        assert (Hxeq : y0 = x' ∪ [a]).
        { apply AxiomI; intros z; split.
          - intros Hzx.
            assert (Ez : Ensemble z) by (exists y0; exact Hzx).
            assert (Hzran : z ∈ ran(g)) by (rewrite Hgran; exact Hzx).
            apply AxiomII in Hzran as [Ez' Hzran].
            destruct Hzran as [t Htz].
            assert (Et : Ensemble t).
            { assert (Etz : Ensemble ([t,z])) by (unfold Ensemble; exists g; exact Htz).
              exact (proj1 (MKT49b t z Etz)). }
            assert (Htd : t ∈ dom(g)).
            { apply AxiomII; split; [exact Et | exists z; exact Htz]. }
            rewrite Hgdom in Htd.
            apply AxiomII in Htd as [Et' Htd].
            destruct Htd as [Htu | Htmu].
            + assert (Hzmu : z ∈ μ) by (apply MKT19b; exact Ez).
              assert (Etz : Ensemble ([t,z])) by (unfold Ensemble; exists g; exact Htz).
              assert (Htz_h : [t,z] ∈ h).
              { unfold h. unfold Restriction.
                apply AxiomII; split; [exact Etz | split; [exact Htz |]].
                apply AxiomII; split; [exact Etz | exists t; exists z; split; [reflexivity | split; [exact Htu | exact Hzmu]]]. }
              assert (Hzx' : z ∈ x').
              { unfold x'. apply AxiomII; split; [exact Ez | exists t; exact Htz_h]. }
              apply (proj1 (MKT4 x' ([a]) z)). left. exact Hzx'.
            + assert (Htu_eq : t = u).
              { apply (proj1 (MKT41 u HuEns t)). exact Htmu. }
              subst t.
              assert (Hza : z = a).
              { apply (proj2 Hg u z a); assumption. }
              apply (proj1 (MKT4 x' ([a]) z)). right.
              apply (proj2 (MKT41 a Ea z)). exact Hza.
          - intros Hz.
            apply AxiomII in Hz as [Ez Hz].
            destruct Hz as [Hzx' | Hza].
            + assert (Hzran : z ∈ ran(g)).
              { apply AxiomII in Hzx' as [Ez' Hzx'].
                destruct Hzx' as [t Htz].
                apply AxiomII; split; [exact Ez' | exists t].
                exact (Hh_sub_g ([t,z]) Htz). }
              rewrite Hgran in Hzran. exact Hzran.
            + apply (proj1 (MKT41 a Ea z)) in Hza.
              subst z. exact Hax. }
        assert (Hunion : ∪y0 = (∪x') ∪ a).
        { rewrite Hxeq.
          rewrite Hunion_dist.
          rewrite (proj2 (MKT44 Ea)).
          reflexivity. }
        rewrite Hunion.
        apply MKT168.
        * apply (HuIH x' Hx'u).
          intros z Hzx'.
          apply Hfiny0.
          assert (Hzran : z ∈ ran(g)).
          { apply AxiomII in Hzx' as [Ez' Hzx'].
            destruct Hzx' as [t Htz].
            apply AxiomII; split; [exact Ez' | exists t].
            exact (Hh_sub_g ([t,z]) Htz). }
          rewrite Hgran in Hzran. exact Hzran.
        * exact (Hfiny0 a Hax). }
  assert (HS : S = ω) by (apply MKT137; assumption).
  assert (Hind : ∀ n, n ∈ ω -> ∀ x, x ≈ n -> (∀ z, z ∈ x -> Finite z) -> Finite (∪x)).
  { intros n Hnω.
    assert (HnS : n ∈ S) by (rewrite HS; exact Hnω).
    apply AxiomII in HnS as [E HnS].
    destruct HnS as [_ HnS'].
    exact HnS'. }
  exact (Hind (P[x]) Hfx x HxP Hfin).
Qed.

Theorem MKT170 : ∀ x y, Finite x -> Finite y -> Finite (x × y).
Proof.
  intros x y Hfx Hfy.
  destruct (proj1 (MKT167 x) Hfx) as [r [Hwo_r Hwo_ri]].
  destruct (proj1 (MKT167 y) Hfy) as [s [Hwo_s Hwo_si]].
  destruct Hwo_r as [Hconn_r Hwosub_r].
  destruct Hwo_ri as [Hconn_ri Hwosub_ri].
  destruct Hwo_s as [Hconn_s Hwosub_s].
  destruct Hwo_si as [Hconn_si Hwosub_si].
  set (L := \{\ λ a b, ∃ a1 b1 a2 b2, a = [a1,b1] /\ b = [a2,b2]
    /\ (Rrelation a1 r a2 \/ (a1 = a2 /\ Rrelation b1 s b2)) \}\).
  assert (Hxy_mem : ∀ p, p ∈ (x × y) ->
    ∃ u v, p = [u,v] /\ u ∈ x /\ v ∈ y).
  { intros p Hp. apply AxiomII in Hp as [E Hp]. exact Hp. }
  assert (Hxy_in : ∀ u v, u ∈ x -> v ∈ y -> [u,v] ∈ (x × y)).
  { intros u v Hux Hvy.
    assert (Eu : Ensemble u) by (exists x; exact Hux).
    assert (Ev : Ensemble v) by (exists y; exact Hvy).
    apply AxiomII; split.
    - apply MKT49a; assumption.
    - exists u; exists v; split; [reflexivity | split; assumption]. }
  assert (HL_mem : ∀ p q, [p,q] ∈ L ->
    ∃ a1 b1 a2 b2, p = [a1,b1] /\ q = [a2,b2]
      /\ (Rrelation a1 r a2 \/ (a1 = a2 /\ Rrelation b1 s b2))).
  { intros p q Hpq.
    apply AxiomII in Hpq as [Epq Hpq].
    destruct Hpq as [a [b [Hpq' H']]].
    destruct H' as [a1 [b1 [a2 [b2 [Ha [Hb Hc]]]]]].
    assert (Eab : Ensemble ([a,b])) by (rewrite <- Hpq'; exact Epq).
    destruct (MKT49b a b Eab) as [Ea Eb].
    assert (Ep : Ensemble p) by (exact (proj1 (MKT49b p q Epq))).
    assert (Eq : Ensemble q) by (exact (proj2 (MKT49b p q Epq))).
    destruct (proj1 (MKT55 p q a b Ep Eq) Hpq') as [Hpa Hqb].
    exists a1; exists b1; exists a2; exists b2.
    split.
    - rewrite Hpa. exact Ha.
    - split.
      + rewrite Hqb. exact Hb.
      + exact Hc. }
  assert (HL_in : ∀ p q, p ∈ (x × y) -> q ∈ (x × y) ->
    (∃ a1 b1 a2 b2, p = [a1,b1] /\ q = [a2,b2]
      /\ (Rrelation a1 r a2 \/ (a1 = a2 /\ Rrelation b1 s b2))) -> [p,q] ∈ L).
  { intros p q Hp Hq Hdec.
    apply AxiomII; split.
    - apply MKT49a.
      + apply AxiomII in Hp as [Ep _]. exact Ep.
      + apply AxiomII in Hq as [Eq _]. exact Eq.
    - destruct Hdec as [a1 [b1 [a2 [b2 [Hp' [Hq' Hc]]]]]].
      exists [a1,b1]; exists [a2,b2]; split.
      + rewrite Hp'. rewrite Hq'. reflexivity.
      + exists a1; exists b1; exists a2; exists b2.
        split; [reflexivity | split; [reflexivity | exact Hc]]. }
  assert (Hconn_L : Connect L (x × y)).
  { unfold Connect.
    intros u v Hu Hv.
    pose proof Hu as Hu0.
    pose proof Hv as Hv0.
    apply AxiomII in Hu as [Eu Hu].
    apply AxiomII in Hv as [Ev Hv].
    destruct Hu as [a [b [Huab [Hax Hby]]]].
    destruct Hv as [c [d [Hvcd [Hcx Hdy]]]].
    assert (Ea : Ensemble a).
    { assert (Eab : Ensemble ([a,b])) by (rewrite <- Huab; exact Eu).
      exact (proj1 (MKT49b a b Eab)). }
    assert (Eb : Ensemble b).
    { assert (Eab : Ensemble ([a,b])) by (rewrite <- Huab; exact Eu).
      exact (proj2 (MKT49b a b Eab)). }
    destruct (Hconn_r a c Hax Hcx) as [Hac | [Hca | Haceq]].
    - left. unfold Rrelation.
      apply (HL_in u v Hu0 Hv0).
      exists a; exists b; exists c; exists d.
      split; [exact Huab | split; [exact Hvcd | left; exact Hac]].
    - right; left. unfold Rrelation.
      apply (HL_in v u Hv0 Hu0).
      exists c; exists d; exists a; exists b.
      split; [exact Hvcd | split; [exact Huab | left; exact Hca]].
    - destruct (Hconn_s b d Hby Hdy) as [Hbd | [Hdb | Hbdeq]].
      + left. unfold Rrelation.
        apply (HL_in u v Hu0 Hv0).
        exists a; exists b; exists c; exists d.
        split; [exact Huab | split; [exact Hvcd | right; split; [exact Haceq | exact Hbd]]].
      + right; left. unfold Rrelation.
        apply (HL_in v u Hv0 Hu0).
        exists c; exists d; exists a; exists b.
        split; [exact Hvcd | split; [exact Huab | right; split; [exact (eq_sym Haceq) | exact Hdb]]].
      + right; right.
        rewrite Huab. rewrite Hvcd.
        rewrite Haceq. rewrite Hbdeq. reflexivity. }
  assert (Hconn_Li : Connect (L⁻¹) (x × y)).
  { unfold Connect.
    intros u v Hu Hv.
    pose proof Hu as Hu0.
    pose proof Hv as Hv0.
    apply AxiomII in Hu0 as [Eu _].
    apply AxiomII in Hv0 as [Ev _].
    destruct (Hconn_L u v Hu Hv) as [Huv | [Hvu | Hueq]].
    - right; left. unfold Rrelation.
      apply (proj2 (MKT_inv_in L v u Ev Eu)). exact Huv.
    - left. unfold Rrelation.
      apply (proj2 (MKT_inv_in L u v Eu Ev)). exact Hvu.
    - right; right. exact Hueq. }
  assert (Hwosub_L : ∀ S, S ⊂ (x × y) -> S ≠ Φ
    -> ∃ z, FirstMember z L S).
  { intros S HS HSn.
    set (S1 := \{ λ a, ∃ b, [a,b] ∈ S \}).
    assert (HS1x : S1 ⊂ x).
    { intros a Ha.
      apply AxiomII in Ha as [Ea Ha].
      destruct Ha as [b Hab].
      destruct (Hxy_mem ([a,b]) (HS ([a,b]) Hab)) as [u [v [Huv [Hux Hvy]]]].
      assert (Eab : Ensemble ([a,b])) by (unfold Ensemble; exists S; exact Hab).
      destruct (MKT49b a b Eab) as [Ea' Eb'].
      assert (Euv : Ensemble ([u,v])) by (rewrite <- Huv; exact Eab).
      destruct (MKT49b u v Euv) as [Eu Ev].
      destruct (proj1 (MKT55 a b u v Ea' Eb') Huv) as [Hau Hbv].
      rewrite Hau. exact Hux. }
    assert (HS1n : S1 ≠ Φ).
    { intro HS1Φ.
      destruct (MKT_nonempty S HSn) as [w Hw].
      destruct (Hxy_mem w (HS w Hw)) as [a [b [Hwab [Hax Hby]]]].
      assert (Ea : Ensemble a).
      { assert (Eab : Ensemble ([a,b])) by (rewrite <- Hwab; unfold Ensemble; exists S; exact Hw).
        exact (proj1 (MKT49b a b Eab)). }
      assert (HaS1 : a ∈ S1).
      { apply AxiomII; split; [exact Ea | exists b; rewrite <- Hwab; exact Hw]. }
      rewrite HS1Φ in HaS1.
      exact (MKT16 HaS1). }
    destruct (Hwosub_r S1 HS1x HS1n) as [a0 [Ha0S1 Ha0first]].
    set (S2 := \{ λ b, [a0,b] ∈ S \}).
    assert (HS2y : S2 ⊂ y).
    { intros b Hb.
      apply AxiomII in Hb as [Eb Hb].
      destruct (Hxy_mem ([a0,b]) (HS ([a0,b]) Hb)) as [u [v [Huv [Hux Hvy]]]].
      assert (Eab : Ensemble ([a0,b])) by (unfold Ensemble; exists S; exact Hb).
      destruct (MKT49b a0 b Eab) as [Ea0' Eb'].
      assert (Euv : Ensemble ([u,v])) by (rewrite <- Huv; exact Eab).
      destruct (MKT49b u v Euv) as [Eu Ev].
      destruct (proj1 (MKT55 a0 b u v Ea0' Eb') Huv) as [Ha0u Hbv].
      rewrite Hbv. exact Hvy. }
    assert (HS2n : S2 ≠ Φ).
    { intro HS2Φ.
      apply AxiomII in Ha0S1 as [Ea0 Ha0S1].
      destruct Ha0S1 as [b0 Hb0S].
      assert (Eb0 : Ensemble b0).
      { assert (Ea0b0 : Ensemble ([a0,b0])) by (unfold Ensemble; exists S; exact Hb0S).
        exact (proj2 (MKT49b a0 b0 Ea0b0)). }
      assert (Hb0S2 : b0 ∈ S2).
      { apply AxiomII; split; [exact Eb0 | exact Hb0S]. }
      rewrite HS2Φ in Hb0S2.
      exact (MKT16 Hb0S2). }
    destruct (Hwosub_s S2 HS2y HS2n) as [b0 [Hb0S2 Hb0first]].
    apply AxiomII in Hb0S2 as [Eb0 Hb0S2].
    exists [a0,b0].
    split.
    - exact Hb0S2.
    - intros w HwS HwL.
      assert (Hwxy : w ∈ x × y) by (exact (HS w HwS)).
      destruct (Hxy_mem w Hwxy) as [c [d [Hwcd [Hcx Hdy]]]].
      assert (Ecd : Ensemble ([c,d])) by (rewrite <- Hwcd; unfold Ensemble; exists S; exact HwS).
      destruct (MKT49b c d Ecd) as [Ec Ed].
      assert (Ea0b0 : Ensemble ([a0,b0])) by (unfold Ensemble; exists S; exact Hb0S2).
      destruct (MKT49b a0 b0 Ea0b0) as [Ea0 Eb00].
      assert (HcdS : [c,d] ∈ S) by (rewrite <- Hwcd; exact HwS).
      destruct (HL_mem w ([a0,b0]) HwL) as [a1 [b1 [a2 [b2 [Hw1 [Hw2 Hc]]]]]].
      assert (Ea1b1 : Ensemble ([a1,b1])) by (rewrite <- Hw1; unfold Ensemble; exists S; exact HwS).
      destruct (MKT49b a1 b1 Ea1b1) as [Ea1 Eb1].
      assert (Heq1 : [a1,b1] = [c,d]) by (rewrite <- Hw1; exact Hwcd).
      destruct (proj1 (MKT55 a1 b1 c d Ea1 Eb1) Heq1) as [Ha1c Hb1d].
      assert (Ea2b2 : Ensemble ([a2,b2])) by (rewrite <- Hw2; exact Ea0b0).
      destruct (MKT49b a2 b2 Ea2b2) as [Ea2 Eb2].
      assert (Heq2 : [a2,b2] = [a0,b0]) by (symmetry; exact Hw2).
      destruct (proj1 (MKT55 a2 b2 a0 b0 Ea2 Eb2) Heq2) as [Ha2a0 Hb2b0].
      destruct Hc as [Hc1 | Hc2].
      + assert (Hc_r : [c,a0] ∈ r).
        { rewrite <- Ha1c. rewrite <- Ha2a0. exact Hc1. }
        assert (HcS1 : c ∈ S1).
        { apply AxiomII; split; [exact Ec | exists d; exact HcdS]. }
        exfalso. exact (Ha0first c HcS1 Hc_r).
      + destruct Hc2 as [Ha1a2 Hdb].
        assert (Hc_a0 : c = a0).
        { rewrite <- Ha1c. rewrite <- Ha2a0. exact Ha1a2. }
        assert (Hd_s : [d,b0] ∈ s).
        { rewrite <- Hb1d. rewrite <- Hb2b0. exact Hdb. }
        assert (Ha0dS : [a0,d] ∈ S) by (rewrite <- Hc_a0; exact HcdS).
        assert (HdS2 : d ∈ S2).
        { apply AxiomII; split; [exact Ed | exact Ha0dS]. }
        exfalso. exact (Hb0first d HdS2 Hd_s). }
  assert (Hwosub_Li : ∀ S, S ⊂ (x × y) -> S ≠ Φ
    -> ∃ z, FirstMember z (L⁻¹) S).
  { intros S HS HSn.
    set (S1 := \{ λ a, ∃ b, [a,b] ∈ S \}).
    assert (HS1x : S1 ⊂ x).
    { intros a Ha.
      apply AxiomII in Ha as [Ea Ha].
      destruct Ha as [b Hab].
      destruct (Hxy_mem ([a,b]) (HS ([a,b]) Hab)) as [u [v [Huv [Hux Hvy]]]].
      assert (Eab : Ensemble ([a,b])) by (unfold Ensemble; exists S; exact Hab).
      destruct (MKT49b a b Eab) as [Ea' Eb'].
      assert (Euv : Ensemble ([u,v])) by (rewrite <- Huv; exact Eab).
      destruct (MKT49b u v Euv) as [Eu Ev].
      destruct (proj1 (MKT55 a b u v Ea' Eb') Huv) as [Hau Hbv].
      rewrite Hau. exact Hux. }
    assert (HS1n : S1 ≠ Φ).
    { intro HS1Φ.
      destruct (MKT_nonempty S HSn) as [w Hw].
      destruct (Hxy_mem w (HS w Hw)) as [a [b [Hwab [Hax Hby]]]].
      assert (Ea : Ensemble a).
      { assert (Eab : Ensemble ([a,b])) by (rewrite <- Hwab; unfold Ensemble; exists S; exact Hw).
        exact (proj1 (MKT49b a b Eab)). }
      assert (HaS1 : a ∈ S1).
      { apply AxiomII; split; [exact Ea | exists b; rewrite <- Hwab; exact Hw]. }
      rewrite HS1Φ in HaS1.
      exact (MKT16 HaS1). }
    destruct (Hwosub_ri S1 HS1x HS1n) as [a0 [Ha0S1 Ha0first]].
    set (S2 := \{ λ b, [a0,b] ∈ S \}).
    assert (HS2y : S2 ⊂ y).
    { intros b Hb.
      apply AxiomII in Hb as [Eb Hb].
      destruct (Hxy_mem ([a0,b]) (HS ([a0,b]) Hb)) as [u [v [Huv [Hux Hvy]]]].
      assert (Eab : Ensemble ([a0,b])) by (unfold Ensemble; exists S; exact Hb).
      destruct (MKT49b a0 b Eab) as [Ea0' Eb'].
      assert (Euv : Ensemble ([u,v])) by (rewrite <- Huv; exact Eab).
      destruct (MKT49b u v Euv) as [Eu Ev].
      destruct (proj1 (MKT55 a0 b u v Ea0' Eb') Huv) as [Ha0u Hbv].
      rewrite Hbv. exact Hvy. }
    assert (HS2n : S2 ≠ Φ).
    { intro HS2Φ.
      apply AxiomII in Ha0S1 as [Ea0 Ha0S1].
      destruct Ha0S1 as [b0 Hb0S].
      assert (Eb0 : Ensemble b0).
      { assert (Ea0b0 : Ensemble ([a0,b0])) by (unfold Ensemble; exists S; exact Hb0S).
        exact (proj2 (MKT49b a0 b0 Ea0b0)). }
      assert (Hb0S2 : b0 ∈ S2).
      { apply AxiomII; split; [exact Eb0 | exact Hb0S]. }
      rewrite HS2Φ in Hb0S2.
      exact (MKT16 Hb0S2). }
    destruct (Hwosub_si S2 HS2y HS2n) as [b0 [Hb0S2 Hb0first]].
    apply AxiomII in Hb0S2 as [Eb0 Hb0S2].
    exists [a0,b0].
    split.
    - exact Hb0S2.
    - intros w HwS HwLi.
      assert (Hwxy : w ∈ x × y) by (exact (HS w HwS)).
      destruct (Hxy_mem w Hwxy) as [c [d [Hwcd [Hcx Hdy]]]].
      assert (Ecd : Ensemble ([c,d])) by (rewrite <- Hwcd; unfold Ensemble; exists S; exact HwS).
      destruct (MKT49b c d Ecd) as [Ec Ed].
      assert (Ea0b0 : Ensemble ([a0,b0])) by (unfold Ensemble; exists S; exact Hb0S2).
      destruct (MKT49b a0 b0 Ea0b0) as [Ea0 Eb00].
      assert (HcdS : [c,d] ∈ S) by (rewrite <- Hwcd; exact HwS).
      assert (Ew : Ensemble w).
      { apply AxiomII in Hwxy as [Ew _]. exact Ew. }
      assert (HwL : [[a0,b0], w] ∈ L).
      { apply (proj1 (MKT_inv_in L w ([a0,b0]) Ew Ea0b0)). exact HwLi. }
      destruct (HL_mem ([a0,b0]) w HwL) as [a1 [b1 [a2 [b2 [Hw1 [Hw2 Hc]]]]]].
      assert (Ea1b1 : Ensemble ([a1,b1])) by (rewrite <- Hw1; exact Ea0b0).
      destruct (MKT49b a1 b1 Ea1b1) as [Ea1 Eb1].
      assert (Heq1 : [a1,b1] = [a0,b0]) by (symmetry; exact Hw1).
      destruct (proj1 (MKT55 a1 b1 a0 b0 Ea1 Eb1) Heq1) as [Ha1a0 Hb1b0].
      assert (Ea2b2 : Ensemble ([a2,b2])) by (rewrite <- Hw2; unfold Ensemble; exists S; exact HwS).
      destruct (MKT49b a2 b2 Ea2b2) as [Ea2 Eb2].
      assert (Heq2 : [a2,b2] = [c,d]) by (rewrite <- Hw2; exact Hwcd).
      destruct (proj1 (MKT55 a2 b2 c d Ea2 Eb2) Heq2) as [Ha2c Hb2d].
      destruct Hc as [Hc1 | Hc2].
      + assert (Hc_r : [a0,c] ∈ r).
        { rewrite <- Ha1a0. rewrite <- Ha2c. exact Hc1. }
        assert (Hc_inv : [c,a0] ∈ r⁻¹).
        { apply (proj2 (MKT_inv_in r c a0 Ec Ea0)). exact Hc_r. }
        assert (HcS1 : c ∈ S1).
        { apply AxiomII; split; [exact Ec | exists d; exact HcdS]. }
        exfalso. exact (Ha0first c HcS1 Hc_inv).
      + destruct Hc2 as [Ha1a2 Hdb].
        assert (Ha0_c : a0 = c).
        { rewrite <- Ha1a0. rewrite <- Ha2c. exact Ha1a2. }
        assert (Hd_s : [b0,d] ∈ s).
        { rewrite <- Hb1b0. rewrite <- Hb2d. exact Hdb. }
        assert (Ha0dS : [a0,d] ∈ S) by (rewrite Ha0_c; exact HcdS).
        assert (HdS2 : d ∈ S2).
        { apply AxiomII; split; [exact Ed | exact Ha0dS]. }
        assert (Hd_inv : [d,b0] ∈ s⁻¹).
        { apply (proj2 (MKT_inv_in s d b0 Ed Eb0)). exact Hd_s. }
        exfalso. exact (Hb0first d HdS2 Hd_inv). }
  apply (proj2 (MKT167 (x × y))).
  exists L.
  split.
  - split; [exact Hconn_L | exact Hwosub_L].
  - split; [exact Hconn_Li | exact Hwosub_Li].
Qed.

Theorem MKT171 : ∀ x, Finite x -> Finite pow(x).
Proof.
  intros x Hfx.
  assert (EΦ : Ensemble Φ).
  { pose proof (proj1 (AxiomII Φ (λ x, Integer x)) MKT135a) as [E _]. exact E. }
  (* x ≈ y implies pow(x) ≈ pow(y) *)
  assert (H_fin_equiv : ∀ x y, Ensemble x -> Ensemble y -> x ≈ y -> Finite x -> Finite y).
  { intros x0 y0 Hx0 Hy0 Hxy Hfx0.
    assert (Hpxpy : P[x0] = P[y0]) by (apply (proj2 (MKT154 x0 y0 Hx0 Hy0)); exact Hxy).
    unfold Finite in Hfx0 |- *.
    rewrite <- Hpxpy. exact Hfx0. }
  (* pow(Φ) = [Φ] *)
  assert (H_pow_empty : pow(Φ) = [Φ]).
  { apply AxiomI; intros z; split.
    - intros Hz.
      apply AxiomII in Hz as [Ez Hzsub].
      apply (proj2 (MKT41 Φ EΦ z)).
      apply AxiomI; intros w; split; intros Hw.
      + exfalso. exact (MKT16 (Hzsub w Hw)).
      + exfalso. apply AxiomII in Hw as [E Hneq]. apply Hneq; reflexivity.
    - intros Hz.
      apply (proj1 (MKT41 Φ EΦ z)) in Hz.
      apply AxiomII; split.
      + subst z; exact EΦ.
      + subst z; intros w Hw. apply AxiomII in Hw as [E Hneq]. exfalso. apply Hneq; reflexivity. }
  (* Finite pow(Φ) *)
  assert (H_fin_pow_empty : Finite pow(Φ)).
  { unfold Finite.
    rewrite H_pow_empty.
    assert (Hpo : PlusOne Φ ∈ ω) by (apply MKT134; exact MKT135a).
    assert (HpoC : PlusOne Φ ∈ C) by (apply MKT164; exact Hpo).
    assert (Hppo : P[PlusOne Φ] = PlusOne Φ) by (exact (proj2 (proj2 (MKT156 (PlusOne Φ)) HpoC))).
    assert (Hsing : [Φ] = PlusOne Φ).
    { unfold PlusOne. rewrite MKT17. reflexivity. }
    rewrite Hsing. rewrite Hppo. exact Hpo. }
  (* pow(PlusOne n) = pow(n) ∪ { S : S ⊂ PlusOne n /\ n ∈ S } *)
  assert (H_pow_plusone : ∀ n, Ensemble n
    -> pow(PlusOne n) = pow(n) ∪ \{ λ S, S ⊂ PlusOne n /\ n ∈ S \}).
  { intros n En.
    apply AxiomI; intros S; split.
    - intros HS.
      apply AxiomII in HS as [ES HSsub].
      destruct (classic (n ∈ S)) as [HnS | HnnotS].
      + apply AxiomII; split; [exact ES | right; apply AxiomII; split; [exact ES | split; [exact HSsub | exact HnS]]].
      + apply AxiomII; split; [exact ES | left; apply AxiomII; split; [exact ES |]].
        intros s Hs.
        pose proof (HSsub s Hs) as Hsn.
        unfold PlusOne in Hsn.
        pose proof (proj2 (MKT4 n ([n]) s) Hsn) as Hsnd.
        destruct Hsnd as [Hsn1 | Hsn2].
        * exact Hsn1.
        * apply (proj1 (MKT41 n En s)) in Hsn2.
          subst s. exfalso. exact (HnnotS Hs).
    - intros HS.
      apply AxiomII in HS as [ES HS].
      destruct HS as [HSpow | HSP1].
      + apply AxiomII; split; [exact ES |].
        intros s Hs.
        apply AxiomII in HSpow as [Es' HSsub].
        assert (Hsn : s ∈ n) by (apply (HSsub s Hs)).
        unfold PlusOne. apply (proj1 (MKT4 n ([n]) s)). left. exact Hsn.
      + apply AxiomII; split; [exact ES |].
        apply AxiomII in HSP1 as [Es' [HSsub _]]. exact HSsub. }
  (* { S : S ⊂ PlusOne n /\ n ∈ S } ≈ pow(n) *)
  assert (H_P1_equiv : ∀ n, Ensemble n -> Ensemble ([n])
    -> \{ λ S, S ⊂ PlusOne n /\ n ∈ S \} ≈ pow(n)).
  { intros n En Ensing.
    set (P1 := \{ λ S, S ⊂ PlusOne n /\ n ∈ S \}).
    set (e := \{\ λ T S, T ∈ pow(n) /\ S = T ∪ [n] \}\).
    assert (He_func : Function e).
    { unfold Function; split.
      - intros z Hz.
        apply AxiomII in Hz as [Ez Hz].
        destruct Hz as [T [S [HzTS _]]].
        exists T; exists S; exact HzTS.
      - intros T S1 S2 H1 H2.
        apply AxiomII in H1 as [E1 H1].
        apply AxiomII in H2 as [E2 H2].
        destruct H1 as [a [b [Hab [Ha Hb]]]].
        destruct H2 as [c [d [Hcd [Hc Hd]]]].
        assert (ET1 : Ensemble ([T,S1])) by (unfold Ensemble; eauto).
        destruct (MKT49b T S1 ET1) as [ET ES1].
        assert (ET2 : Ensemble ([T,S2])) by (unfold Ensemble; eauto).
        destruct (MKT49b T S2 ET2) as [ET' ES2].
        assert (Eab : Ensemble ([a,b])) by (rewrite <- Hab; exact E1).
        destruct (MKT49b a b Eab) as [Ea Eb].
        assert (Ecd : Ensemble ([c,d])) by (rewrite <- Hcd; exact E2).
        destruct (MKT49b c d Ecd) as [Ec Ed].
        destruct (proj1 (MKT55 T S1 a b ET ES1) Hab) as [HTa HS1b].
        destruct (proj1 (MKT55 T S2 c d ET' ES2) Hcd) as [HTc HS2d].
        subst a. subst c.
        rewrite HS1b. rewrite HS2d.
        rewrite Hb. rewrite Hd. reflexivity. }
    assert (Hedom : dom(e) = pow(n)).
    { apply AxiomI; intros T; split.
      - intros HT.
        apply AxiomII in HT as [ET HT].
        destruct HT as [S HTS].
        apply AxiomII in HTS as [E HTS].
        destruct HTS as [a [b [Hab [Ha Hb]]]].
        assert (ETS : Ensemble ([T,S])) by (unfold Ensemble; eauto).
        destruct (MKT49b T S ETS) as [ET' ES'].
        assert (Eab : Ensemble ([a,b])) by (rewrite <- Hab; exact E).
        destruct (MKT49b a b Eab) as [Ea Eb].
        destruct (proj1 (MKT55 T S a b ET' ES') Hab) as [HTa HSb].
        rewrite <- HTa in Ha. exact Ha.
      - intros HT.
        apply AxiomII in HT as [ET HTsub].
        assert (ETun : Ensemble (T ∪ [n])).
        { apply AxiomIV; [exact ET | exact Ensing]. }
        apply AxiomII; split; [exact ET |].
        exists (T ∪ [n]).
        apply AxiomII; split; [apply MKT49a; [exact ET | exact ETun] |].
        exists T; exists (T ∪ [n]); split; [reflexivity |].
        split; [apply AxiomII; split; [exact ET | exact HTsub] | reflexivity]. }
    assert (Heran : ran(e) = P1).
    { apply AxiomI; intros S; split.
      - intros HS.
        apply AxiomII in HS as [ES HS].
        destruct HS as [T HTS].
        apply AxiomII in HTS as [E HTS].
        destruct HTS as [a [b [Hab [Ha Hb]]]].
        assert (ETS : Ensemble ([T,S])) by (unfold Ensemble; eauto).
        destruct (MKT49b T S ETS) as [ET' ES2].
        assert (Eab : Ensemble ([a,b])) by (rewrite <- Hab; exact E).
        destruct (MKT49b a b Eab) as [Ea Eb].
        destruct (proj1 (MKT55 T S a b ET' ES2) Hab) as [HTa HSb].
        apply AxiomII in Ha as [Ea' Hasub].
        apply AxiomII; split; [exact ES | split].
        + intros s Hs.
          rewrite HSb in Hs.
          rewrite Hb in Hs.
          unfold PlusOne. apply MKT4 in Hs.
          destruct Hs as [Hsa | Hss].
          * apply (proj1 (MKT4 n ([n]) s)). left. exact (Hasub s Hsa).
          * apply (proj1 (MKT4 n ([n]) s)). right. exact Hss.
        + rewrite HSb.
          rewrite Hb.
          unfold PlusOne. apply MKT4. right.
          apply (proj2 (MKT41 n En n)). reflexivity.
      - intros HS.
        apply AxiomII in HS as [ES HS].
        destruct HS as [HSsub HnS].
        set (T := S ~ [n]).
        assert (ET : Ensemble T).
        { apply (MKT33 S T ES).
          intros s Hs'.
          unfold T in Hs'. apply AxiomII in Hs' as [E [Hs'1 _]]. exact Hs'1. }
        assert (HTsub : T ⊂ n).
        { intros s HsT.
          unfold T in HsT.
          apply AxiomII in HsT as [Es HsT'].
          destruct HsT' as [HsS Hsnot].
          pose proof (HSsub s HsS) as Hsplus.
          unfold PlusOne in Hsplus.
          apply MKT4 in Hsplus.
          destruct Hsplus as [Hsn | Hss].
          - exact Hsn.
          - apply (proj1 (MKT41 n En s)) in Hss.
            subst s. exfalso.
            destruct (proj1 (AxiomII n (λ y, y ∉ [n])) Hsnot) as [En0 Hnn].
            apply Hnn.
            apply (proj2 (MKT41 n En n)). reflexivity. }
        assert (HTpow : T ∈ pow(n)).
        { apply AxiomII; split; [exact ET | exact HTsub]. }
        assert (HSeq : S = T ∪ [n]).
        { apply AxiomI; intros s; split.
          - intros HsS.
            pose proof (HSsub s HsS) as Hsplus.
            unfold PlusOne in Hsplus.
            apply MKT4 in Hsplus.
            destruct Hsplus as [Hsn | Hss].
            + apply (proj1 (MKT4 T ([n]) s)). left.
              unfold T. apply AxiomII; split; [unfold Ensemble; eauto | split; [exact HsS |]].
              apply AxiomII; split; [unfold Ensemble; eauto | intros Hsin].
              apply (proj1 (MKT41 n En s)) in Hsin.
              subst s. exact (MKT101 n Hsn).
            + apply (proj1 (MKT4 T ([n]) s)). right. exact Hss.
          - intros HsT.
            apply MKT4 in HsT.
            destruct HsT as [HsT1 | Hsn].
            + unfold T in HsT1.
              apply AxiomII in HsT1 as [Es [HsS _]]. exact HsS.
            + apply (proj1 (MKT41 n En s)) in Hsn.
              subst s. exact HnS. }
        apply AxiomII; split.
        + exact ES.
        + exists T.
          apply AxiomII; split.
          * apply MKT49a; [exact ET | exact ES].
          * exists T; exists S; split; [reflexivity | split; [exact HTpow | exact HSeq]]. }
    assert (Heinv_func : Function (e⁻¹)).
    { unfold Function; split.
      - intros z Hz.
        apply AxiomII in Hz as [Ez Hz].
        destruct Hz as [a [b [Hzb _]]].
        exists a; exists b; exact Hzb.
      - intros S1 S2 T H1 H2.
        assert (ES1 : Ensemble S1).
        { assert (E : Ensemble ([S1,T])) by (unfold Ensemble; exists (e⁻¹); exact H2).
          exact (proj1 (MKT49b S1 T E)). }
        assert (ES2 : Ensemble S2).
        { assert (E : Ensemble ([S1,S2])) by (unfold Ensemble; exists (e⁻¹); exact H1).
          exact (proj2 (MKT49b S1 S2 E)). }
        assert (ET : Ensemble T).
        { assert (E : Ensemble ([S1,T])) by (unfold Ensemble; exists (e⁻¹); exact H2).
          exact (proj2 (MKT49b S1 T E)). }
        (* From H2 : [S1,T] ∈ e⁻¹ we get [T,S1] ∈ e *)
        assert (HTS1 : [T,S1] ∈ e) by (apply (proj1 (MKT_inv_in e S1 T ES1 ET)); exact H2).
        (* From H1 : [S1,S2] ∈ e⁻¹ we get [S2,S1] ∈ e *)
        assert (HS2S1 : [S2,S1] ∈ e) by (apply (proj1 (MKT_inv_in e S1 S2 ES1 ES2)); exact H1).
        apply AxiomII in HTS1 as [E1 HTS1].
        apply AxiomII in HS2S1 as [E2 HS2S1].
        destruct HTS1 as [a [b [Hab [Ha Hb]]]].
        destruct HS2S1 as [c [d [Hcd [Hc Hd]]]].
        assert (ET1 : Ensemble ([T,S1])) by (unfold Ensemble; eauto).
        destruct (MKT49b T S1 ET1) as [ET' ES1'].
        assert (Eab : Ensemble ([a,b])) by (rewrite <- Hab; exact E1).
        destruct (MKT49b a b Eab) as [Ea Eb].
        destruct (proj1 (MKT55 T S1 a b ET' ES1') Hab) as [HTa HS1b].
        assert (ES2S1 : Ensemble ([S2,S1])) by (unfold Ensemble; eauto).
        destruct (MKT49b S2 S1 ES2S1) as [ES2' ES1''].
        assert (Ecd : Ensemble ([c,d])) by (rewrite <- Hcd; exact E2).
        destruct (MKT49b c d Ecd) as [Ec Ed].
        destruct (proj1 (MKT55 S2 S1 c d ES2' ES1'') Hcd) as [HS2c HS1d].
        subst a. subst c.
        assert (HS1T : S1 = T ∪ [n]).
        { rewrite HS1b. rewrite Hb. reflexivity. }
        assert (HS1S2 : S1 = S2 ∪ [n]).
        { rewrite HS1d. rewrite Hd. reflexivity. }
        assert (HST : S2 ∪ [n] = T ∪ [n]) by congruence.
        apply AxiomII in Ha as [ETpow HsubT].
        apply AxiomII in Hc as [ES2pow HsubS2].
        apply AxiomI; intros s; split.
        + intros HsS2.
          assert (Hssn : s ∈ n) by (apply (HsubS2 s HsS2)).
          assert (HsST : s ∈ T ∪ [n]).
          { rewrite <- HST. apply AxiomII; split; [unfold Ensemble; eauto | left; exact HsS2]. }
          apply AxiomII in HsST as [Es HsST].
          destruct HsST as [HsT | HsSing].
          * exact HsT.
          * apply (proj1 (MKT41 n En s)) in HsSing.
            subst s. exfalso. exact (MKT101 n Hssn).
        + intros HsT.
          assert (Hssn : s ∈ n) by (apply (HsubT s HsT)).
          assert (HsTS : s ∈ S2 ∪ [n]).
          { rewrite HST. apply AxiomII; split; [unfold Ensemble; eauto | left; exact HsT]. }
          apply AxiomII in HsTS as [Es HsTS].
          destruct HsTS as [HsS2 | HsSing].
          * exact HsS2.
          * apply (proj1 (MKT41 n En s)) in HsSing.
            subst s. exfalso. exact (MKT101 n Hssn). }
    assert (Hedom_inv : dom(e⁻¹) = P1) by (rewrite MKT_dom_inv; exact Heran).
    assert (Heran_inv : ran(e⁻¹) = pow(n)) by (rewrite MKT_ran_inv; exact Hedom).
    assert (He11_inv : Function1_1 (e⁻¹)).
    { split.
      - exact Heinv_func.
      - assert (Hinv_inv : (e⁻¹)⁻¹ = e) by (apply MKT61; exact (proj1 He_func)).
        rewrite Hinv_inv. exact He_func. }
    unfold P1 in Hedom_inv.
    exists (e⁻¹).
    split; [exact He11_inv | split; [exact Hedom_inv | exact Heran_inv]]. }
  (* x ≈ y implies pow(x) ≈ pow(y) *)
  assert (H_pow_equiv : ∀ aa bb, Ensemble aa -> Ensemble bb -> aa ≈ bb -> pow(aa) ≈ pow(bb)).
  { intros aa bb Haa Hbb [f [Hf11 [Hfdom Hfran]]].
    destruct Hf11 as [Hf Hfinv].
    set (fimg := fun S : Class => \{ λ z, ∃ s, s ∈ S /\ [s,z] ∈ f \}).
    set (F := \{\ λ S T, S ∈ pow(aa) /\ T ∈ pow(bb) /\ T = fimg S \}\).
    assert (HF_func : Function F).
    { unfold Function; split.
      - intros z Hz.
        apply AxiomII in Hz as [Ez Hz].
        destruct Hz as [S [T [HzST _]]].
        exists S; exists T; exact HzST.
      - intros S T1 T2 H1 H2.
        apply AxiomII in H1 as [E1 H1].
        apply AxiomII in H2 as [E2 H2].
        destruct H1 as [a [b [Hab [Ha [Hb1 Hb2]]]]].
        destruct H2 as [c [d [Hcd [Hc [Hd1 Hd2]]]]].
        assert (EST1 : Ensemble ([S,T1])) by (unfold Ensemble; eauto).
        destruct (MKT49b S T1 EST1) as [ES ET1].
        assert (EST2 : Ensemble ([S,T2])) by (unfold Ensemble; eauto).
        destruct (MKT49b S T2 EST2) as [ES' ET2].
        assert (Eab : Ensemble ([a,b])) by (rewrite <- Hab; exact E1).
        destruct (MKT49b a b Eab) as [Ea Eb].
        assert (Ecd : Ensemble ([c,d])) by (rewrite <- Hcd; exact E2).
        destruct (MKT49b c d Ecd) as [Ec Ed].
        destruct (proj1 (MKT55 S T1 a b ES ET1) Hab) as [HSa HT1b].
        destruct (proj1 (MKT55 S T2 c d ES' ET2) Hcd) as [HSc HT2d].
        subst a. subst c.
        rewrite HT1b. rewrite HT2d.
        rewrite Hb2. rewrite Hd2. reflexivity. }
    assert (HFdom : dom(F) = pow(aa)).
    { apply AxiomI; intros S; split.
      - intros HS.
        apply AxiomII in HS as [ES HS].
        destruct HS as [T HST].
        apply AxiomII in HST as [E HST].
        destruct HST as [a [b [Hab [Ha [Hb1 Hb2]]]]].
        assert (EST : Ensemble ([S,T])) by (unfold Ensemble; eauto).
        destruct (MKT49b S T EST) as [ES' ET].
        assert (Eab : Ensemble ([a,b])) by (rewrite <- Hab; exact E).
        destruct (MKT49b a b Eab) as [Ea Eb].
        destruct (proj1 (MKT55 S T a b ES' ET) Hab) as [HSa HTb].
        rewrite <- HSa in Ha. exact Ha.
      - intros HS.
        apply AxiomII in HS as [ES HSsub].
        assert (Hfimg_sub : fimg S ⊂ bb).
        { intros z Hz.
          unfold fimg in Hz.
          apply AxiomII in Hz as [Ez Hz].
          destruct Hz as [s [Hs Hsz]].
          assert (Esz : Ensemble ([s,z])) by (unfold Ensemble; exists f; exact Hsz).
          assert (Ez' : Ensemble z) by (exact (proj2 (MKT49b s z Esz))).
          assert (Hzr : z ∈ ran(f)).
          { apply AxiomII; split; [exact Ez' | exists s; exact Hsz]. }
          rewrite Hfran in Hzr. exact Hzr. }
        assert (EfS : Ensemble (fimg S)) by (apply (MKT33 bb (fimg S) Hbb Hfimg_sub)).
        apply AxiomII; split; [exact ES |].
        exists (fimg S).
        apply AxiomII; split; [exact (MKT49a ES EfS) |].
        exists S; exists (fimg S); split; [reflexivity |].
        split.
        + apply AxiomII; split; [exact ES | exact HSsub].
        + split; [apply AxiomII; split; [exact EfS | exact Hfimg_sub] | reflexivity]. }
    assert (HFran : ran(F) = pow(bb)).
    { apply AxiomI; intros T; split.
      - intros HT.
        apply AxiomII in HT as [ET HT].
        destruct HT as [S HST].
        apply AxiomII in HST as [E HST].
        destruct HST as [a [b [Hab [Ha [Hb1 Hb2]]]]].
        assert (EST : Ensemble ([S,T])) by (unfold Ensemble; eauto).
        destruct (MKT49b S T EST) as [ES' ET'].
        assert (Eab : Ensemble ([a,b])) by (rewrite <- Hab; exact E).
        destruct (MKT49b a b Eab) as [Ea Eb].
        destruct (proj1 (MKT55 S T a b ES' ET') Hab) as [HSa HTb].
        rewrite <- HTb in Hb1. exact Hb1.
      - intros HT.
        apply AxiomII in HT as [ET HTsub].
        set (S0 := \{ λ s, s ∈ aa /\ f[s] ∈ T \}).
        assert (HS0sub : S0 ⊂ aa).
        { intros s Hs0. apply AxiomII in Hs0 as [E [Hsx _]]. exact Hsx. }
        assert (ES0 : Ensemble S0) by (apply (MKT33 aa S0 Haa HS0sub)).
        assert (Himg : fimg S0 = T).
        { apply AxiomI; intros t; split.
          - intros Ht.
            unfold fimg in Ht.
            apply AxiomII in Ht as [Et Ht].
            destruct Ht as [s [Hs0 Hst]].
            apply AxiomII in Hs0 as [Es [Hsx HfsT]].
            assert (Hsd : s ∈ dom(f)) by (rewrite Hfdom; exact Hsx).
            assert (Hsfs : [s, f[s]] ∈ f) by (apply (MKT_dom_val f s Hf Hsd)).
            assert (Htfs : t = f[s]) by (apply (proj2 Hf s t (f[s])); [exact Hst | exact Hsfs]).
            rewrite Htfs. exact HfsT.
          - intros Ht.
            assert (Htr : t ∈ ran(f)).
            { pose proof (HTsub t Ht) as Htt.
              rewrite <- Hfran in Htt.
              exact Htt. }
            apply AxiomII in Htr as [Et Htr].
            destruct Htr as [s Hst].
            assert (Esz : Ensemble ([s,t])) by (unfold Ensemble; exists f; exact Hst).
            destruct (MKT49b s t Esz) as [Es Et'].
            assert (Hsx : s ∈ aa).
            { rewrite <- Hfdom.
              apply AxiomII; split; [exact Es | exists t; exact Hst]. }
            assert (Hsd : s ∈ dom(f)) by (rewrite Hfdom; exact Hsx).
            assert (Hfst : f[s] = t) by (apply (MKT_fval f s t Hf); exact Hst).
            assert (Hs0 : s ∈ S0).
            { apply AxiomII; split; [exact Es | split; [exact Hsx | rewrite Hfst; exact Ht]]. }
            unfold fimg. apply AxiomII; split; [exact Et | exists s; split; [exact Hs0 | exact Hst]]. }
        apply AxiomII; split; [exact ET |].
        exists S0.
        apply AxiomII; split; [exact (MKT49a ES0 ET) |].
        exists S0; exists T; split; [reflexivity |].
        split.
        + apply AxiomII; split; [exact ES0 | exact HS0sub].
        + split.
          * apply AxiomII; split; [exact ET | exact HTsub].
          * symmetry. exact Himg. }
    assert (HFinv_func : Function (F⁻¹)).
    { unfold Function; split.
      - intros z Hz.
        apply AxiomII in Hz as [Ez Hz].
        destruct Hz as [a [b [Hzb _]]].
        exists a; exists b; exact Hzb.
      - intros T S1 S2 H1 H2.
        assert (ET : Ensemble T).
        { assert (E : Ensemble ([T,S1])) by (unfold Ensemble; exists (F⁻¹); exact H1).
          exact (proj1 (MKT49b T S1 E)). }
        assert (ES1 : Ensemble S1).
        { assert (E : Ensemble ([T,S1])) by (unfold Ensemble; exists (F⁻¹); exact H1).
          exact (proj2 (MKT49b T S1 E)). }
        assert (ES2 : Ensemble S2).
        { assert (E : Ensemble ([T,S2])) by (unfold Ensemble; exists (F⁻¹); exact H2).
          exact (proj2 (MKT49b T S2 E)). }
        assert (HS1T : [S1,T] ∈ F) by (apply (proj1 (MKT_inv_in F T S1 ET ES1)); exact H1).
        assert (HS2T : [S2,T] ∈ F) by (apply (proj1 (MKT_inv_in F T S2 ET ES2)); exact H2).
        apply AxiomII in HS1T as [E1 HS1T].
        apply AxiomII in HS2T as [E2 HS2T].
        destruct HS1T as [a [b [Hab [Ha [Hb1 Hb2]]]]].
        destruct HS2T as [c [d [Hcd [Hc [Hd1 Hd2]]]]].
        assert (EST1 : Ensemble ([S1,T])) by (unfold Ensemble; eauto).
        destruct (MKT49b S1 T EST1) as [ES1' ET'].
        assert (Eab : Ensemble ([a,b])) by (rewrite <- Hab; exact E1).
        destruct (MKT49b a b Eab) as [Ea Eb].
        destruct (proj1 (MKT55 S1 T a b ES1' ET') Hab) as [HS1a HTb].
        assert (EST2 : Ensemble ([S2,T])) by (unfold Ensemble; eauto).
        destruct (MKT49b S2 T EST2) as [ES2' ET''].
        assert (Ecd : Ensemble ([c,d])) by (rewrite <- Hcd; exact E2).
        destruct (MKT49b c d Ecd) as [Ec Ed].
        destruct (proj1 (MKT55 S2 T c d ES2' ET'') Hcd) as [HS2c HTd].
        subst a. subst c.
        assert (Himg : fimg S1 = fimg S2).
        { transitivity T.
          - symmetry. transitivity b; [exact HTb | exact Hb2].
          - transitivity d; [exact HTd | exact Hd2]. }
        apply AxiomII in Ha as [ES1a HS1sub].
        apply AxiomII in Hc as [ES2a HS2sub].
        apply AxiomI; intros s; split.
        + intro Hs.
          assert (Hsx : s ∈ aa) by (exact (HS1sub s Hs)).
          assert (Hsd : s ∈ dom(f)) by (rewrite Hfdom; exact Hsx).
          assert (Hsfs : [s, f[s]] ∈ f) by (apply (MKT_dom_val f s Hf Hsd)).
          assert (Efs : Ensemble (f[s])).
          { assert (E : Ensemble ([s, f[s]])) by (unfold Ensemble; exists f; exact Hsfs).
            exact (proj2 (MKT49b s (f[s]) E)). }
          assert (Hfs1 : f[s] ∈ fimg S1).
          { unfold fimg. apply AxiomII; split; [exact Efs | exists s; split; [exact Hs | exact Hsfs]]. }
          assert (Hfs2 : f[s] ∈ fimg S2) by (rewrite <- Himg; exact Hfs1).
          unfold fimg in Hfs2.
          apply AxiomII in Hfs2 as [Efs2 Hfs2].
          destruct Hfs2 as [s2 [Hs2 Hs2fs]].
          assert (Hs2x : s2 ∈ aa) by (exact (HS2sub s2 Hs2)).
          assert (Hs2d : s2 ∈ dom(f)) by (rewrite Hfdom; exact Hs2x).
          assert (Es2 : Ensemble s2).
          { assert (E : Ensemble ([s2, f[s]])) by (unfold Ensemble; exists f; exact Hs2fs).
            exact (proj1 (MKT49b s2 (f[s]) E)). }
          assert (Es' : Ensemble s).
          { assert (E : Ensemble ([s, f[s]])) by (unfold Ensemble; exists f; exact Hsfs).
            exact (proj1 (MKT49b s (f[s]) E)). }
          assert (H1i : [f[s], s2] ∈ f⁻¹) by (apply (proj2 (MKT_inv_in f (f[s]) s2 Efs Es2)); exact Hs2fs).
          assert (H2i : [f[s], s] ∈ f⁻¹) by (apply (proj2 (MKT_inv_in f (f[s]) s Efs Es')); exact Hsfs).
          assert (Hs2s : s2 = s) by (apply (proj2 Hfinv (f[s]) s2 s); [exact H1i | exact H2i]).
          subst s2. exact Hs2.
        + intro Hs.
          assert (Hsx : s ∈ aa) by (exact (HS2sub s Hs)).
          assert (Hsd : s ∈ dom(f)) by (rewrite Hfdom; exact Hsx).
          assert (Hsfs : [s, f[s]] ∈ f) by (apply (MKT_dom_val f s Hf Hsd)).
          assert (Efs : Ensemble (f[s])).
          { assert (E : Ensemble ([s, f[s]])) by (unfold Ensemble; exists f; exact Hsfs).
            exact (proj2 (MKT49b s (f[s]) E)). }
          assert (Hfs2 : f[s] ∈ fimg S2).
          { unfold fimg. apply AxiomII; split; [exact Efs | exists s; split; [exact Hs | exact Hsfs]]. }
          assert (Hfs1 : f[s] ∈ fimg S1) by (rewrite Himg; exact Hfs2).
          unfold fimg in Hfs1.
          apply AxiomII in Hfs1 as [Efs1 Hfs1].
          destruct Hfs1 as [s2 [Hs2 Hs2fs]].
          assert (Hs2x : s2 ∈ aa) by (exact (HS1sub s2 Hs2)).
          assert (Hs2d : s2 ∈ dom(f)) by (rewrite Hfdom; exact Hs2x).
          assert (Es2 : Ensemble s2).
          { assert (E : Ensemble ([s2, f[s]])) by (unfold Ensemble; exists f; exact Hs2fs).
            exact (proj1 (MKT49b s2 (f[s]) E)). }
          assert (Es' : Ensemble s).
          { assert (E : Ensemble ([s, f[s]])) by (unfold Ensemble; exists f; exact Hsfs).
            exact (proj1 (MKT49b s (f[s]) E)). }
          assert (H1i : [f[s], s2] ∈ f⁻¹) by (apply (proj2 (MKT_inv_in f (f[s]) s2 Efs Es2)); exact Hs2fs).
          assert (H2i : [f[s], s] ∈ f⁻¹) by (apply (proj2 (MKT_inv_in f (f[s]) s Efs Es')); exact Hsfs).
          assert (Hs2s : s2 = s) by (apply (proj2 Hfinv (f[s]) s2 s); [exact H1i | exact H2i]).
          subst s2. exact Hs2. }
    assert (HF11 : Function1_1 F) by (split; assumption).
    exists F.
    split; [exact HF11 | split; [exact HFdom | exact HFran]]. }
  (* induction on n ∈ ω : Finite pow(n) *)
  assert (H_ind : ∀ n, n ∈ ω -> Finite pow(n)).
  { set (Good := \{ λ n, n ∈ ω /\ Finite pow(n) \}).
    assert (HGoodω : Good ⊂ ω).
    { intros n Hn. apply AxiomII in Hn as [E [Hnω _]]. exact Hnω. }
    assert (HΦG : Φ ∈ Good).
    { apply AxiomII; split; [exact EΦ | split; [exact MKT135a | exact H_fin_pow_empty]]. }
    assert (HsuccG : ∀ u, u ∈ Good -> PlusOne u ∈ Good).
    { intros u Hu.
      apply AxiomII in Hu as [Eu Hu].
      destruct Hu as [Huω Hfu].
      apply AxiomII; split.
      - pose proof (MKT134 Huω) as Hpoω.
        apply AxiomII in Hpoω as [Ep _]. exact Ep.
      - split.
        + exact (MKT134 Huω).
        + assert (Eu' : Ensemble u) by (apply AxiomII in Huω as [Eu' _]; exact Eu').
          assert (Esu : Ensemble ([u])) by (apply MKT42; exact Eu').
          set (P1 := \{ λ S, S ⊂ PlusOne u /\ u ∈ S \}).
          assert (Hpup : pow(PlusOne u) = pow(u) ∪ P1).
          { unfold P1. exact (H_pow_plusone u Eu'). }
          assert (Hp1eq : P1 ≈ pow(u)).
          { unfold P1. apply (H_P1_equiv u Eu' Esu). }
          assert (Epowu : Ensemble pow(u)) by (apply MKT38a; exact Eu').
          assert (EP1 : Ensemble P1).
          { apply (MKT33 (pow(PlusOne u)) P1).
            - pose proof (MKT134 Huω) as Hpoω'.
              apply AxiomII in Hpoω' as [Ep _].
              apply MKT38a. exact Ep.
            - unfold P1. intros S HS.
              apply AxiomII in HS as [ES [HSsub _]].
              apply AxiomII; split; [exact ES | exact HSsub]. }
          assert (Hfp1 : Finite P1).
          { apply (H_fin_equiv pow(u) P1 Epowu EP1).
            - apply MKT146. exact Hp1eq.
            - exact Hfu. }
          assert (Hfun : Finite (pow(u) ∪ P1)) by (apply MKT168; assumption).
          rewrite Hpup. exact Hfun. }
    assert (HGood_eq : Good = ω) by (apply MKT137; assumption).
    intros n Hnω.
    assert (HnG : n ∈ Good) by (rewrite HGood_eq; exact Hnω).
    apply AxiomII in HnG as [E [Hnω' Hfn]]. exact Hfn. }
  (* Ensemble x *)
  assert (HxE : Ensemble x).
  { apply MKT19a.
    rewrite <- MKT152b.
    apply (MKT69b' (x:=x) (f:=P)).
    apply MKT19b.
    pose proof Hfx as Hpxω.
    apply AxiomII in Hpxω as [En _].
    exact En. }
  assert (HpxE : Ensemble (P[x])).
  { pose proof Hfx as Hpxω. apply AxiomII in Hpxω as [En _]. exact En. }
  assert (HxPx : x ≈ P[x]).
  { apply MKT146; apply MKT153; exact HxE. }
  assert (Hpowx : pow(x) ≈ pow(P[x])).
  { apply (H_pow_equiv x (P[x]) HxE HpxE HxPx). }
  assert (Hfinpow : Finite pow(P[x])) by (apply (H_ind (P[x])); exact Hfx).
  apply (H_fin_equiv (pow(P[x])) (pow(x))).
  - apply MKT38a; exact HpxE.
  - apply MKT38a; exact HxE.
  - apply MKT146. exact Hpowx.
  - exact Hfinpow.
Qed.

(* ==================== MKT172 ==================== *)

Lemma MKT172_empty_equiv : ∀ x, x ≈ Φ -> x = Φ.
Proof.
  intros x0 Hx0.
  apply AxiomI; intros z; split.
  - intros Hzx0.
    exfalso.
    destruct Hx0 as [f [Hf11 [Hdom Hran]]].
    assert (Hzd : z ∈ dom(f)) by (rewrite Hdom; exact Hzx0).
    assert (Hfz : [z, f[z]] ∈ f) by (apply (MKT_dom_val f z (proj1 Hf11) Hzd)).
    assert (Efz : Ensemble (f[z])).
    { assert (E : Ensemble ([z, f[z]])) by (unfold Ensemble; exists f; exact Hfz).
      exact (proj2 (MKT49b z (f[z]) E)). }
    assert (Hfzr : f[z] ∈ ran(f)).
    { apply AxiomII; split; [exact Efz | exists z; exact Hfz]. }
    rewrite Hran in Hfzr.
    apply AxiomII in Hfzr as [E Hfzr'].
    exact (Hfzr' eq_refl).
  - intros Hz.
    apply AxiomII in Hz as [E Hneq].
    exfalso; apply Hneq; reflexivity.
Qed.

Lemma MKT172_ClaimP : ∀ z, z ∈ ω -> ~ (PlusOne z ≈ z).
Proof.
  intros z Hz.
  assert (EΦ : Ensemble Φ).
  { destruct AxiomVIII as [y8 [Hy8Ens [HΦ8 _]]].
    unfold Ensemble; exists y8; exact HΦ8.
  }
  pose (s := \{ λ x, x ∈ ω /\ ~ (PlusOne x ≈ x) \}).
  assert (Hsω : s ⊂ ω).
  { unfold Included; intros x Hx.
    unfold s in Hx; apply AxiomII in Hx as [_ [Hxω _]]; exact Hxω.
  }
  assert (HΦs : Φ ∈ s).
  { unfold s; apply AxiomII; split.
    - exact EΦ.
    - split.
      + exact MKT135a.
      + intro Hbase.
        unfold PlusOne in Hbase.
        unfold Equivalent in Hbase.
        destruct Hbase as [f [[_ _] [Hdom Hran]]].
        assert (HΦdom : Φ ∈ dom(f)).
        { rewrite Hdom.
          apply (proj1 (MKT4 Φ ([Φ]) Φ)); right.
          unfold Singleton.
          apply AxiomII; split.
          - exact EΦ.
          - intro; reflexivity.
        }
        apply AxiomII in HΦdom as [_ Hy].
        destruct Hy as [y Hpair].
        assert (HyEns' : Ensemble y).
        { assert (HpairEns : Ensemble ([Φ,y])).
          { unfold Ensemble; exists f; exact Hpair. }
          exact (proj2 (MKT49b Φ y HpairEns)).
        }
        assert (Hyran : y ∈ ran(f)).
        { apply AxiomII; split.
          - exact HyEns'.
          - exists Φ; exact Hpair.
        }
        assert (HyΦ : y ∈ Φ).
        { pose proof (AxiomI ran(f) Φ) as Hiff.
          exact (proj1 ((proj1 Hiff Hran) y) Hyran).
        }
        exact (@MKT16 y HyΦ).
  }
  assert (Hclos : ∀ u, u ∈ s -> PlusOne u ∈ s).
  { intros u Hu.
    unfold s in Hu; apply AxiomII in Hu as [HuEns [Huω Hnu]].
    unfold s; apply AxiomII; split.
    - assert (Hpoω : PlusOne u ∈ ω). { apply MKT134; exact Huω. }
      apply AxiomII in Hpoω as [HpoEns _]; exact HpoEns.
    - split.
      + apply MKT134; exact Huω.
      + intro Hpo.
        apply Hnu.
        apply (MKT163 (PlusOne u) u).
        * apply MKT134; exact Huω.
        * exact Huω.
        * exact Hpo.
  }
  assert (Hseq : s = ω).
  { apply MKT137; [exact Hsω | exact HΦs | exact Hclos]. }
  assert (Hzs : z ∈ s).
  { rewrite Hseq; exact Hz. }
  unfold s in Hzs; apply AxiomII in Hzs as [_ [_ Hn]]; exact Hn.
Qed.

Lemma MKT172_succ_notin : ∀ n, n ∈ ω -> (PlusOne n) ∉ n /\ (PlusOne n) ≠ n.
Proof.
  intros n Hn.
  assert (En : Ensemble n).
  { apply AxiomII in Hn as [En _]. exact En. }
  assert (Hnord : Ordinal n).
  { apply AxiomII in Hn as [_ Hint]. destruct Hint as [Hord _]. exact Hord. }
  assert (Hnfull : Full n) by (exact (proj2 Hnord)).
  assert (Hn_m : n ∈ PlusOne n).
  { unfold PlusOne. apply (proj1 (MKT4 n ([n]) n)); right.
    apply (proj2 (MKT41 n En n)); reflexivity. }
  split.
  - intro Hm.
    exact (MKT101 n (Hnfull (PlusOne n) Hm n Hn_m)).
  - intro Heq.
    rewrite Heq in Hn_m.
    exact (MKT101 n Hn_m).
Qed.

Lemma MKT172_union_equiv : ∀ A B c d, Ensemble c -> Ensemble d -> c ∉ A -> d ∉ B
  -> A ≈ B -> A ∪ [c] ≈ B ∪ [d].
Proof.
  intros A B c d Ec Ed HcA HdB [φ [Hφ11 [Hφdom Hφran]]].
  destruct Hφ11 as [Hφ Hφinv].
  set (ψ := \{\ λ x y, (x ∈ A /\ y = φ[x]) \/ (x = c /\ y = d) \}\).
  assert (Hφval : ∀ x, x ∈ A -> φ[x] ∈ B /\ [x, φ[x]] ∈ φ).
  { intros x Hx.
    assert (Hxd : x ∈ dom(φ)) by (rewrite Hφdom; exact Hx).
    assert (Hxφ : [x, φ[x]] ∈ φ) by (apply (MKT_dom_val φ x Hφ Hxd)).
    split.
    - assert (E : Ensemble ([x, φ[x]])) by (unfold Ensemble; exists φ; exact Hxφ).
      assert (Hr : φ[x] ∈ ran(φ)).
      { apply AxiomII; split; [exact (proj2 (MKT49b x (φ[x]) E)) | exists x; exact Hxφ]. }
      rewrite Hφran in Hr. exact Hr.
    - exact Hxφ. }
  assert (Hψ_char : ∀ x y, [x,y] ∈ ψ <->
    Ensemble ([x,y]) /\ ((x ∈ A /\ y = φ[x]) \/ (x = c /\ y = d))).
  { intros x y; split.
    - intros Hxy.
      apply AxiomII in Hxy as [Exy Hxy].
      destruct Hxy as [u [v [Huv Hdisj]]].
      assert (Euv : Ensemble ([u,v])) by (rewrite <- Huv; exact Exy).
      destruct (MKT49b u v Euv) as [Eu Ev].
      destruct (MKT49b x y Exy) as [Ex Ey].
      destruct (proj1 (MKT55 x y u v Ex Ey) Huv) as [Hxu Hyv].
      subst u; subst v.
      split; [exact Exy | exact Hdisj].
    - intros [Exy Hdisj].
      apply AxiomII; split; [exact Exy |].
      exists x; exists y; split; [reflexivity | exact Hdisj]. }
  assert (Hψfunc : Function ψ).
  { unfold Function; split.
    - intros z Hz.
      apply AxiomII in Hz as [Ez Hz].
      destruct Hz as [x [y [Hzy _]]].
      exists x; exists y; exact Hzy.
    - intros x y y' Hxy Hxy'.
      destruct (proj1 (Hψ_char x y) Hxy) as [Exy H1].
      destruct (proj1 (Hψ_char x y') Hxy') as [Exy' H2].
      destruct H1 as [H1 | H1']; destruct H2 as [H2 | H2'].
      + destruct H1 as [HxA Hy]; destruct H2 as [HxA' Hy']. rewrite Hy. rewrite Hy'. reflexivity.
      + destruct H1 as [HxA Hy]; destruct H2' as [Hxc Hy']. exfalso. apply HcA. rewrite <- Hxc. exact HxA.
      + destruct H1' as [Hxc Hy]; destruct H2 as [HxA' Hy']. exfalso. apply HcA. rewrite <- Hxc. exact HxA'.
      + destruct H1' as [Hxc Hy]; destruct H2' as [Hxc' Hy']. rewrite Hy. rewrite Hy'. reflexivity. }
  assert (Hψdom : dom(ψ) = A ∪ [c]).
  { apply AxiomI; intros x; split.
    - intros Hx.
      apply AxiomII in Hx as [Ex Hx].
      destruct Hx as [y Hxy].
      destruct (proj1 (Hψ_char x y) Hxy) as [Exy H1].
      destruct H1 as [H1 | H1'].
      + destruct H1 as [HxA _]. apply (proj1 (MKT4 A ([c]) x)); left; exact HxA.
      + destruct H1' as [Hxc _]. apply (proj1 (MKT4 A ([c]) x)); right.
        apply (proj2 (MKT41 c Ec x)); exact Hxc.
    - intros Hx.
      apply (proj2 (MKT4 A ([c]) x)) in Hx.
      destruct Hx as [HxA | Hxc'].
      + assert (Hφv : φ[x] ∈ B /\ [x, φ[x]] ∈ φ) by (apply Hφval; exact HxA).
        destruct Hφv as [HxB Hxφ].
        assert (Exφx : Ensemble ([x, φ[x]])) by (unfold Ensemble; exists φ; exact Hxφ).
        destruct (MKT49b x (φ[x]) Exφx) as [Ex' Eφx].
        apply AxiomII; split; [exact Ex' |].
        exists (φ[x]).
        apply (proj2 (Hψ_char x (φ[x]))).
        split; [exact Exφx | left; split; [exact HxA | reflexivity]].
      + apply (proj1 (MKT41 c Ec x)) in Hxc'.
        subst x.
        apply AxiomII; split; [exact Ec |].
        exists d.
        apply (proj2 (Hψ_char c d)).
        split; [exact (MKT49a Ec Ed) | right; split; [reflexivity | reflexivity]]. }
  assert (Hψran : ran(ψ) = B ∪ [d]).
  { apply AxiomI; intros y; split.
    - intros Hy.
      apply AxiomII in Hy as [Ey Hy].
      destruct Hy as [x Hxy].
      destruct (proj1 (Hψ_char x y) Hxy) as [Exy H1].
      destruct H1 as [H1 | H1'].
      + destruct H1 as [HxA Hyφ].
        assert (Hφv : φ[x] ∈ B /\ [x, φ[x]] ∈ φ) by (apply Hφval; exact HxA).
        destruct Hφv as [HxB _].
        rewrite Hyφ.
        apply (proj1 (MKT4 B ([d]) (φ[x]))); left; exact HxB.
      + destruct H1' as [Hxc Hyd].
        rewrite Hyd.
        apply (proj1 (MKT4 B ([d]) d)); right.
        apply (proj2 (MKT41 d Ed d)); reflexivity.
    - intros Hy.
      apply (proj2 (MKT4 B ([d]) y)) in Hy.
      destruct Hy as [HyB | Hyd'].
      + assert (Ey : Ensemble y) by (unfold Ensemble; exists B; exact HyB).
        assert (Hyr : y ∈ ran(φ)) by (rewrite Hφran; exact HyB).
        apply AxiomII in Hyr as [Ey' Hyr].
        destruct Hyr as [x Hxy].
        assert (Exy : Ensemble ([x,y])) by (unfold Ensemble; exists φ; exact Hxy).
        destruct (MKT49b x y Exy) as [Ex Ey0].
        assert (Hxd : x ∈ dom(φ)).
        { apply AxiomII; split; [exact Ex | exists y; exact Hxy]. }
        assert (HxA : x ∈ A) by (rewrite <- Hφdom; exact Hxd).
        assert (Hyφx : y = φ[x]) by (symmetry; apply (MKT_fval φ x y Hφ); exact Hxy).
        apply AxiomII; split; [exact Ey |].
        exists x.
        apply (proj2 (Hψ_char x y)).
        split; [exact Exy | left; split; [exact HxA | exact Hyφx]].
      + apply (proj1 (MKT41 d Ed y)) in Hyd'.
        rewrite Hyd'.
        apply AxiomII; split; [exact Ed |].
        exists c.
        apply (proj2 (Hψ_char c d)).
        split; [exact (MKT49a Ec Ed) | right; split; [reflexivity | reflexivity]]. }
  assert (Hψinj : ∀ x x' y, [x,y] ∈ ψ -> [x',y] ∈ ψ -> x = x').
  { intros x x' y Hxy Hx'y.
    destruct (proj1 (Hψ_char x y) Hxy) as [Exy H1].
    destruct (proj1 (Hψ_char x' y) Hx'y) as [Ex'y H2].
    destruct H1 as [H1 | H1']; destruct H2 as [H2 | H2'].
    + destruct H1 as [HxA Hy]; destruct H2 as [Hx'A Hy'].
      assert (Hφv : φ[x] ∈ B /\ [x, φ[x]] ∈ φ) by (apply Hφval; exact HxA).
      assert (Hφv' : φ[x'] ∈ B /\ [x', φ[x']] ∈ φ) by (apply Hφval; exact Hx'A).
      destruct Hφv as [HxB Hxφ].
      destruct Hφv' as [Hx'B Hx'φ].
      assert (Exφx : Ensemble ([x, φ[x]])) by (unfold Ensemble; exists φ; exact Hxφ).
      destruct (MKT49b x (φ[x]) Exφx) as [Ex Eφx].
      assert (Ex'φx' : Ensemble ([x', φ[x']])) by (unfold Ensemble; exists φ; exact Hx'φ).
      destruct (MKT49b x' (φ[x']) Ex'φx') as [Ex' Eφx'].
      assert (Hφeq : φ[x] = φ[x']).
      { rewrite <- Hy. rewrite <- Hy'. reflexivity. }
      assert (Hx'φx : [x', φ[x]] ∈ φ).
      { rewrite <- Hφeq in Hx'φ. exact Hx'φ. }
      assert (Hinv1 : [φ[x], x] ∈ φ⁻¹).
      { apply (proj2 (MKT_inv_in φ (φ[x]) x Eφx Ex)). exact Hxφ. }
      assert (Hinv2 : [φ[x], x'] ∈ φ⁻¹).
      { apply (proj2 (MKT_inv_in φ (φ[x]) x' Eφx Ex')). exact Hx'φx. }
      exact (proj2 Hφinv (φ[x]) x x' Hinv1 Hinv2).
    + destruct H1 as [HxA Hy]; destruct H2' as [Hxc Hy'].
      exfalso.
      assert (Hφv : φ[x] ∈ B /\ [x, φ[x]] ∈ φ) by (apply Hφval; exact HxA).
      destruct Hφv as [HxB _].
      apply HdB.
      rewrite <- Hy'. rewrite Hy. exact HxB.
    + destruct H1' as [Hxc Hy]; destruct H2 as [Hx'A Hy'].
      exfalso.
      assert (Hφv' : φ[x'] ∈ B /\ [x', φ[x']] ∈ φ) by (apply Hφval; exact Hx'A).
      destruct Hφv' as [Hx'B _].
      apply HdB.
      rewrite <- Hy. rewrite Hy'. exact Hx'B.
    + destruct H1' as [Hxc Hy]; destruct H2' as [Hx'c Hy'].
      rewrite Hxc. symmetry. exact Hx'c. }
  assert (Hψ11 : Function1_1 ψ).
  { split; [exact Hψfunc |].
    unfold Function; split.
    - intros z Hz.
      apply AxiomII in Hz as [Ez Hz].
      destruct Hz as [a [b [Hzb _]]].
      exists a; exists b; exact Hzb.
    - intros p q r Hpq Hpr.
      assert (Epq : Ensemble ([p,q])) by (unfold Ensemble; exists (ψ⁻¹); exact Hpq).
      destruct (MKT49b p q Epq) as [Ep Eq].
      assert (Epr : Ensemble ([p,r])) by (unfold Ensemble; exists (ψ⁻¹); exact Hpr).
      destruct (MKT49b p r Epr) as [Ep' Er].
      assert (Hqp : [q,p] ∈ ψ) by (apply (proj1 (MKT_inv_in ψ p q Ep Eq)); exact Hpq).
      assert (Hrp : [r,p] ∈ ψ) by (apply (proj1 (MKT_inv_in ψ p r Ep' Er)); exact Hpr).
      apply (Hψinj q r p); assumption. }
  exists ψ; split; [exact Hψ11 | split; [exact Hψdom | exact Hψran]].
Qed.

Lemma MKT172_swap_remove : ∀ m, m ∈ ω -> ∀ p, p ∈ m -> (m ~ [p]) ∪ [m] ≈ m.
Proof.
  intros m Hm p0 Hp0.
  pose (S := \{ λ n, n ∈ ω /\ (∀ p, p ∈ n -> (n ~ [p]) ∪ [n] ≈ n) \}).
  assert (HSω : S ⊂ ω).
  { intros n Hn. apply AxiomII in Hn as [E [Hnω _]]. exact Hnω. }
  assert (HΦS : Φ ∈ S).
  { apply AxiomII; split.
    - destruct AxiomVIII as [y [Ey [HΦy _]]]. unfold Ensemble; exists y; exact HΦy.
    - split.
      + exact MKT135a.
      + intros p Hp. exfalso. exact (MKT16 Hp). }
  assert (HsuccS : ∀ u, u ∈ S -> PlusOne u ∈ S).
  { intros u Hu.
    apply AxiomII in Hu as [Eu Hu].
    destruct Hu as [Huω HuIH].
    apply AxiomII; split.
    - pose proof (MKT134 Huω) as Hpuω.
      apply AxiomII in Hpuω as [E _]. exact E.
    - split.
      + exact (MKT134 Huω).
      + intros p Hp.
        assert (Em : Ensemble (PlusOne u)).
        { pose proof (MKT134 Huω) as Hpuω.
          apply AxiomII in Hpuω as [Em _]. exact Em. }
        apply (proj2 (MKT4 u ([u]) p)) in Hp.
        destruct Hp as [Hpu | Hps].
        * (* p ∈ u *)
          assert (Ep : Ensemble p) by (unfold Ensemble; exists u; exact Hpu).
          assert (HIH : (u ~ [p]) ∪ [u] ≈ u) by (exact (HuIH p Hpu)).
          assert (Hc : PlusOne u ∉ ((u ~ [p]) ∪ [u])).
          { intro Hc0.
            apply (proj2 (MKT4 (u ~ [p]) ([u]) (PlusOne u))) in Hc0.
            destruct Hc0 as [Hc1 | Hc2].
            - apply AxiomII in Hc1 as [E [Hcu _]]. exact (proj1 (MKT172_succ_notin u Huω) Hcu).
            - apply (proj1 (MKT41 u Eu (PlusOne u))) in Hc2.
              exact (proj2 (MKT172_succ_notin u Huω) Hc2). }
          assert (Huu : u ∉ u) by exact (MKT101 u).
          pose proof (MKT172_union_equiv ((u ~ [p]) ∪ [u]) u (PlusOne u) u
            Em Eu Hc Huu HIH) as Hue.
          assert (Hpe : (PlusOne u ~ [p]) = ((u ~ [p]) ∪ [u])).
          { apply AxiomI; intros z; split.
            - intros Hz.
              apply AxiomII in Hz as [Ez [Hzm Hzp]].
              apply AxiomII in Hzm as [Ez' Hzm'].
              destruct Hzm' as [Hzu | Hzs].
              + apply (proj1 (MKT4 (u ~ [p]) ([u]) z)); left.
                apply AxiomII; split; [exact Ez | split; [exact Hzu | exact Hzp]].
              + apply (proj1 (MKT4 (u ~ [p]) ([u]) z)); right. exact Hzs.
            - intros Hz.
              apply (proj2 (MKT4 (u ~ [p]) ([u]) z)) in Hz.
              destruct Hz as [Hz1 | Hz2].
              + apply AxiomII in Hz1 as [Ez [Hzu Hzp]].
                apply AxiomII; split; [exact Ez | split].
                * apply (proj1 (MKT4 u ([u]) z)); left; exact Hzu.
                * exact Hzp.
              + apply AxiomII in Hz2 as [Ez Hz2'].
                assert (Hz2u : z = u) by (exact (Hz2' (MKT19b u Eu))).
                apply AxiomII; split; [exact Ez | split].
                * apply (proj1 (MKT4 u ([u]) z)); right.
                  apply (proj2 (MKT41 u Eu z)); exact Hz2u.
                * apply AxiomII; split; [unfold Ensemble; eauto |].
                  intro Hzp.
                  assert (Hup : u ∈ [p]).
                  { rewrite <- Hz2u. exact Hzp. }
                  apply (proj1 (MKT41 p Ep u)) in Hup.
                  rewrite <- Hup in Hpu.
                  exact (MKT101 u Hpu). }
          rewrite Hpe.
          change (((u ~ [p]) ∪ [u]) ∪ [PlusOne u] ≈ u ∪ [u]).
          exact Hue.
        * (* p = u *)
          apply (proj1 (MKT41 u Eu p)) in Hps.
          subst p.
          assert (Hrem : (u ∪ [u]) ~ [u] = u).
          { apply AxiomI; intros z; split.
            - intros Hz.
              apply AxiomII in Hz as [Ez [Hz1 Hz2]].
              apply AxiomII in Hz1 as [Ez' Hz1'].
              destruct Hz1' as [Hzu | Hzs].
              + exact Hzu.
              + apply (proj1 (MKT41 u Eu z)) in Hzs.
                exfalso.
                apply AxiomII in Hz2 as [E Hz2'].
                apply Hz2'.
                apply (proj2 (MKT41 u Eu z)); exact Hzs.
            - intros Hz.
              apply AxiomII; split; [unfold Ensemble; eauto | split].
              + apply (proj1 (MKT4 u ([u]) z)); left; exact Hz.
              + apply AxiomII; split; [unfold Ensemble; eauto |].
                intro Hzs.
                apply (proj1 (MKT41 u Eu z)) in Hzs.
                subst z.
                exact (MKT101 u Hz). }
          assert (Hc : PlusOne u ∉ u) by (exact (proj1 (MKT172_succ_notin u Huω))).
          assert (Huu : u ∉ u) by exact (MKT101 u).
          assert (Hun : u ≈ u) by (apply MKT145).
          pose proof (MKT172_union_equiv u u (PlusOne u) u
            Em Eu Hc Huu Hun) as Hue.
          assert (Hpe2 : (PlusOne u ~ [u]) = u).
          { unfold PlusOne. exact Hrem. }
          rewrite Hpe2.
          change (u ∪ [PlusOne u] ≈ u ∪ [u]).
          exact Hue. }
  assert (Hseq : S = ω) by (apply (MKT137 S); assumption).
  assert (HmS : m ∈ S) by (rewrite Hseq; exact Hm).
  apply AxiomII in HmS as [E HmS'].
  destruct HmS' as [_ HmS''].
  exact (HmS'' p0 Hp0).
Qed.

Lemma MKT172_nat_remove : ∀ m, m ∈ ω -> ∀ p, p ∈ PlusOne m -> (PlusOne m) ~ [p] ≈ m.
Proof.
  intros m Hm p Hp.
  assert (Em : Ensemble m) by (apply AxiomII in Hm as [E _]; exact E).
  apply (proj2 (MKT4 m ([m]) p)) in Hp.
  destruct Hp as [Hpm | Hps].
  - (* p ∈ m *)
    assert (Ep : Ensemble p) by (unfold Ensemble; exists m; exact Hpm).
    assert (Hpne : p ≠ m) by (intro Hpm0; subst p; exact (MKT101 m Hpm)).
    assert (Hrem : (m ∪ [m]) ~ [p] = (m ~ [p]) ∪ [m]).
    { apply AxiomI; intros z; split.
      - intros Hz.
        apply AxiomII in Hz as [Ez [Hz1 Hz2]].
        apply AxiomII in Hz1 as [Ez' Hz1'].
        destruct Hz1' as [Hzm | Hzmm].
        + apply (proj1 (MKT4 (m ~ [p]) ([m]) z)); left.
          apply AxiomII; split; [exact Ez | split; [exact Hzm | exact Hz2]].
        + apply (proj1 (MKT4 (m ~ [p]) ([m]) z)); right. exact Hzmm.
      - intros Hz.
        apply (proj2 (MKT4 (m ~ [p]) ([m]) z)) in Hz.
        destruct Hz as [Hz1 | Hz2].
        + apply AxiomII in Hz1 as [Ez [Hzm Hzp]].
          apply AxiomII; split; [exact Ez | split].
          * apply (proj1 (MKT4 m ([m]) z)); left; exact Hzm.
          * exact Hzp.
        + apply AxiomII; split; [unfold Ensemble; eauto | split].
          * apply (proj1 (MKT4 m ([m]) z)); right. exact Hz2.
          * apply AxiomII; split; [unfold Ensemble; eauto |].
            intro Hzp.
            apply (proj1 (MKT41 p Ep z)) in Hzp.
            apply (proj1 (MKT41 m Em z)) in Hz2.
            rewrite Hzp in Hz2.
            exact (Hpne Hz2). }
    change ((m ∪ [m]) ~ [p] ≈ m).
    rewrite Hrem.
    apply (MKT172_swap_remove m Hm p Hpm).
  - (* p = m *)
    apply (proj1 (MKT41 m Em p)) in Hps.
    subst p.
    assert (Hrem : (m ∪ [m]) ~ [m] = m).
    { apply AxiomI; intros z; split.
      - intros Hz.
        apply AxiomII in Hz as [Ez [Hz1 Hz2]].
        apply AxiomII in Hz1 as [Ez' Hz1'].
        destruct Hz1' as [Hzm | Hzs].
        + exact Hzm.
        + apply (proj1 (MKT41 m Em z)) in Hzs.
          exfalso.
          apply AxiomII in Hz2 as [E Hz2'].
          apply Hz2'.
          apply (proj2 (MKT41 m Em z)); exact Hzs.
      - intros Hz.
        apply AxiomII; split; [unfold Ensemble; eauto | split].
        + apply (proj1 (MKT4 m ([m]) z)); left; exact Hz.
        + apply AxiomII; split; [unfold Ensemble; eauto |].
          intro Hzs.
          apply (proj1 (MKT41 m Em z)) in Hzs.
          subst z.
          exact (MKT101 m Hz). }
    unfold PlusOne.
    rewrite Hrem.
    apply MKT145.
Qed.

Lemma MKT172_remove_any : ∀ x m, m ∈ ω -> x ≈ PlusOne m -> ∀ a, a ∈ x -> (x ~ [a]) ≈ m.
Proof.
  intros x m Hm Hx a Hax.
  destruct Hx as [f [Hf11 [Hfdom Hfran]]].
  destruct Hf11 as [Hf Hfinv].
  assert (Ea : Ensemble a).
  { assert (Had : a ∈ dom(f)) by (rewrite Hfdom; exact Hax).
    assert (Haf : [a, f[a]] ∈ f) by (apply (MKT_dom_val f a Hf Had)).
    assert (E : Ensemble ([a, f[a]])) by (unfold Ensemble; exists f; exact Haf).
    exact (proj1 (MKT49b a (f[a]) E)). }
  assert (Hfaval : f[a] ∈ PlusOne m /\ [a, f[a]] ∈ f).
  { assert (Had : a ∈ dom(f)) by (rewrite Hfdom; exact Hax).
    assert (Haf : [a, f[a]] ∈ f) by (apply (MKT_dom_val f a Hf Had)).
    split.
    - assert (E : Ensemble ([a, f[a]])) by (unfold Ensemble; exists f; exact Haf).
      assert (Hr : f[a] ∈ ran(f)) by (apply AxiomII; split; [exact (proj2 (MKT49b a (f[a]) E)) | exists a; exact Haf]).
      rewrite Hfran in Hr. exact Hr.
    - exact Haf. }
  destruct Hfaval as [HfaP Hfaf].
  assert (Efa : Ensemble (f[a])).
  { assert (E : Ensemble ([a, f[a]])) by (unfold Ensemble; exists f; exact Hfaf).
    exact (proj2 (MKT49b a (f[a]) E)). }
  pose proof (MKT172_nat_remove m Hm (f[a]) HfaP) as Hnat.
  set (S := x ~ [a]).
  set (g := f | (S)).
  assert (Hgfunc : Function g) by (unfold g; apply MKT126a; exact Hf).
  assert (Hg_sub : g ⊂ f).
  { intros z Hz. unfold g. apply AxiomII in Hz as [E [Hzf _]]. exact Hzf. }
  assert (Hgdom : dom(g) = S).
  { unfold g. rewrite (MKT126b f S Hf).
    apply (proj2 (MKT30 S (dom(f)))).
    intros t Ht.
    apply AxiomII in Ht as [E [Htx _]].
    rewrite Hfdom. exact Htx. }
  assert (Hgran : ran(g) = (PlusOne m) ~ [f[a]]).
  { apply AxiomI; intros y; split.
    - intros Hy.
      apply AxiomII in Hy as [Ey Hy].
      destruct Hy as [t Hty].
      apply AxiomII in Hty as [Ety Hty].
      destruct Hty as [Htyf HtyS].
      apply AxiomII in HtyS as [Ety' HtyS'].
      destruct HtyS' as [u [v [Huv [Hut Hvmu]]]].
      assert (Ety0 : Ensemble ([t,y])) by (unfold Ensemble; exists f; exact Htyf).
      destruct (MKT49b t y Ety0) as [Et Ey'].
      assert (Euv : Ensemble ([u,v])) by (rewrite <- Huv; exact Ety').
      destruct (MKT49b u v Euv) as [Eu Ev].
      destruct (proj1 (MKT55 t y u v Et Ey') Huv) as [Htu Hvy].
      subst u; subst v.
      assert (HtS : t ∈ S) by exact Hut.
      unfold S in HtS.
      apply AxiomII in HtS as [EtS HtS'].
      destruct HtS' as [Htx Htna].
      apply AxiomII in Htna as [Etna Htna'].
      assert (Hyr : y ∈ ran(f)) by (apply AxiomII; split; [exact Ey' | exists t; exact Htyf]).
      rewrite Hfran in Hyr.
      apply AxiomII; split; [exact Ey' | split; [exact Hyr |]].
      apply AxiomII; split; [exact Ey' |].
      intro Hyfa.
      apply (proj1 (MKT41 (f[a]) Efa y)) in Hyfa.
      assert (Hya_f : [a,y] ∈ f).
      { rewrite <- Hyfa in Hfaf. exact Hfaf. }
      assert (Hta : t = a).
      { apply (proj2 Hfinv y t a).
        - apply (proj2 (MKT_inv_in f y t Ey' Et)); exact Htyf.
        - apply (proj2 (MKT_inv_in f y a Ey' Ea)); exact Hya_f. }
      apply Htna'.
      apply (proj2 (MKT41 a Ea t)).
      exact Hta.
    - intros Hy.
      apply AxiomII in Hy as [Ey Hy].
      destruct Hy as [HyP Hyfa'].
      apply AxiomII in Hyfa' as [Eyfa Hyfa''].
      rewrite <- Hfran in HyP.
      apply AxiomII in HyP as [Ey' HyP'].
      destruct HyP' as [t Hty].
      assert (Ety0 : Ensemble ([t,y])) by (unfold Ensemble; exists f; exact Hty).
      destruct (MKT49b t y Ety0) as [Et Ey0].
      assert (Htna : t ∉ [a]).
      { intro Hta.
        apply (proj1 (MKT41 a Ea t)) in Hta.
        subst t.
        assert (Hyf : f[a] = y) by (apply (MKT_fval f a y Hf); exact Hty).
        apply Hyfa''.
        apply (proj2 (MKT41 (f[a]) Efa y)). symmetry. exact Hyf. }
      assert (HtS : t ∈ S).
      { unfold S. apply AxiomII; split.
        - exact Et.
        - split.
          + rewrite <- Hfdom. apply AxiomII; split; [exact Et | exists y; exact Hty].
          + apply AxiomII; split; [exact Et | exact Htna]. }
      assert (Hymu : y ∈ μ) by (apply MKT19b; exact Ey0).
      assert (HtyS : [t,y] ∈ S × μ).
      { apply AxiomII; split; [exact Ety0 |].
        exists t; exists y; split; [reflexivity | split; [exact HtS | exact Hymu]]. }
      apply AxiomII; split; [exact Ey |].
      exists t.
      apply AxiomII; split; [exact Ety0 | split; [exact Hty | exact HtyS]]. }
  assert (Hg11 : Function1_1 g).
  { split; [exact Hgfunc |].
    unfold Function; split.
    - intros z Hz.
      apply AxiomII in Hz as [Ez Hz].
      destruct Hz as [a0 [b [Hzb _]]].
      exists a0; exists b; exact Hzb.
    - intros p q r Hpq Hpr.
      assert (Epq : Ensemble ([p,q])) by (unfold Ensemble; exists (g⁻¹); exact Hpq).
      destruct (MKT49b p q Epq) as [Ep Eq].
      assert (Epr : Ensemble ([p,r])) by (unfold Ensemble; exists (g⁻¹); exact Hpr).
      destruct (MKT49b p r Epr) as [Ep' Er].
      assert (Hqpg : [q,p] ∈ g) by (apply (proj1 (MKT_inv_in g p q Ep Eq)); exact Hpq).
      assert (Hrpg : [r,p] ∈ g) by (apply (proj1 (MKT_inv_in g p r Ep' Er)); exact Hpr).
      assert (Hqpf : [q,p] ∈ f) by (exact (Hg_sub ([q,p]) Hqpg)).
      assert (Hrpf : [r,p] ∈ f) by (exact (Hg_sub ([r,p]) Hrpg)).
      assert (Hpqf : [p,q] ∈ f⁻¹) by (apply (proj2 (MKT_inv_in f p q Ep Eq)); exact Hqpf).
      assert (Hprf : [p,r] ∈ f⁻¹) by (apply (proj2 (MKT_inv_in f p r Ep' Er)); exact Hrpf).
      exact (proj2 Hfinv p q r Hpqf Hprf). }
  assert (H1 : S ≈ (PlusOne m) ~ [f[a]]).
  { exists g; split; [exact Hg11 | split; [exact Hgdom | exact Hgran]]. }
  exact (MKT147 ((PlusOne m) ~ [f[a]]) S m H1 Hnat).
Qed.

Lemma MKT172_fin_sub : ∀ n, n ∈ ω -> ∀ x y, x ≈ n -> y ⊂ x -> y ≈ n -> x = y.
Proof.
  intros n Hn.
  pose (S := \{ λ n0, n0 ∈ ω /\ (∀ x y, x ≈ n0 -> y ⊂ x -> y ≈ n0 -> x = y) \}).
  assert (HSω : S ⊂ ω).
  { intros n0 Hn0. apply AxiomII in Hn0 as [E [Hn0ω _]]. exact Hn0ω. }
  assert (HΦS : Φ ∈ S).
  { apply AxiomII; split.
    - destruct AxiomVIII as [y [Ey [HΦy _]]]. unfold Ensemble; exists y; exact HΦy.
    - split.
      + exact MKT135a.
      + intros x y Hx Hyx Hy.
        assert (HxΦ : x = Φ) by (apply MKT172_empty_equiv; exact Hx).
        assert (HyΦ : y = Φ) by (apply MKT172_empty_equiv; exact Hy).
        rewrite HxΦ. rewrite HyΦ. reflexivity. }
  assert (HsuccS : ∀ u, u ∈ S -> PlusOne u ∈ S).
  { intros u Hu.
    apply AxiomII in Hu as [Eu Hu].
    destruct Hu as [Huω HuIH].
    apply AxiomII; split.
    - pose proof (MKT134 Huω) as Hpuω.
      apply AxiomII in Hpuω as [E _]. exact E.
    - split.
      + exact (MKT134 Huω).
      + intros x y Hx Hyx Hy.
        apply NNPP; intro Hneq.
        assert (Hyneq : y ≠ x) by (intro Hyx0; apply Hneq; symmetry; exact Hyx0).
        destruct (MKT_neq_sub x y Hyx Hyneq) as [a [Hax Hany]].
        assert (Ea : Ensemble a).
        { destruct Hx as [f [Hf11 [Hfdom Hfran]]].
          assert (Had : a ∈ dom(f)) by (rewrite Hfdom; exact Hax).
          assert (Haf : [a, f[a]] ∈ f) by (apply (MKT_dom_val f a (proj1 Hf11) Had)).
          assert (E : Ensemble ([a, f[a]])) by (unfold Ensemble; exists f; exact Haf).
          exact (proj1 (MKT49b a (f[a]) E)). }
        assert (Hx1 : (x ~ [a]) ≈ u).
        { exact (MKT172_remove_any x u Huω Hx a Hax). }
        assert (Hyx1 : y ⊂ (x ~ [a])).
        { intros z Hzy.
          assert (Hzx : z ∈ x) by (exact (Hyx z Hzy)).
          assert (Ez : Ensemble z) by (unfold Ensemble; exists x; exact Hzx).
          apply AxiomII; split; [exact Ez | split; [exact Hzx |]].
          apply AxiomII; split; [exact Ez |].
          intro Hza.
          apply (proj1 (MKT41 a Ea z)) in Hza.
          apply Hany. rewrite <- Hza. exact Hzy. }
        assert (Hyne : y ≠ Φ).
        { intro Hy0.
          assert (HΦy : Φ ≈ y) by (rewrite Hy0; apply MKT145).
          assert (HΦpu : Φ ≈ PlusOne u).
          { apply (MKT147 y Φ (PlusOne u)).
            - exact HΦy.
            - exact Hy. }
          assert (HpuΦ : PlusOne u = Φ) by (apply MKT172_empty_equiv; exact (MKT146 HΦpu)).
          assert (Eu0 : Ensemble u) by (apply AxiomII in Huω as [E _]; exact E).
          assert (Huu : u ∈ PlusOne u).
          { unfold PlusOne. apply (proj1 (MKT4 u ([u]) u)); right.
            apply (proj2 (MKT41 u Eu0 u)); reflexivity. }
          rewrite HpuΦ in Huu.
          exact (MKT16 Huu). }
        destruct (MKT_nonempty y Hyne) as [b Hby].
        assert (Hy1 : (y ~ [b]) ≈ u).
        { exact (MKT172_remove_any y u Huω Hy b Hby). }
        assert (Hy1x1 : (y ~ [b]) ⊂ (x ~ [a])).
        { intros z Hz.
          apply AxiomII in Hz as [Ez [Hzy _]].
          exact (Hyx1 z Hzy). }
        assert (Hy1ne : (y ~ [b]) ≠ (x ~ [a])).
        { intro Heq.
          assert (Hx1y : (x ~ [a]) ⊂ y).
          { intros z Hz.
            rewrite <- Heq in Hz.
            apply AxiomII in Hz as [Ez Hz'].
            destruct Hz' as [Hzy _].
            exact Hzy. }
          assert (Hyx1eq : y = (x ~ [a])).
          { apply (proj1 (MKT27 y (x ~ [a]))). split; assumption. }
          assert (Hyu : y ≈ u).
          { rewrite Hyx1eq. exact Hx1. }
          assert (Hupu : u ≈ PlusOne u).
          { apply (MKT147 y u (PlusOne u)).
            - exact (MKT146 Hyu).
            - exact Hy. }
          exact (MKT172_ClaimP u Huω (MKT146 Hupu)). }
        assert (Hx1y1 : (x ~ [a]) = (y ~ [b])).
        { apply (HuIH (x ~ [a]) (y ~ [b]) Hx1 Hy1x1 Hy1). }
        exact (Hy1ne (eq_sym Hx1y1)). }
  assert (Hseq : S = ω) by (apply (MKT137 S); assumption).
  assert (HnS : n ∈ S) by (rewrite Hseq; exact Hn).
  apply AxiomII in HnS as [E HnS'].
  destruct HnS' as [_ HnS''].
  intros x y Hx Hyx Hy.
  exact (HnS'' x y Hx Hyx Hy).
Qed.

Theorem MKT172 : ∀ x y, Finite x -> y ⊂ x -> P[y] = P[x] -> x = y.
Proof.
  intros x y Hfx Hyx Hpyx.
  assert (HxE : Ensemble x).
  { apply MKT19a.
    rewrite <- MKT152b.
    apply (MKT69b' (x:=x) (f:=P)).
    apply MKT19b.
    pose proof Hfx as Hpxω.
    apply AxiomII in Hpxω as [En _].
    exact En. }
  assert (HyE : Ensemble y) by (apply (MKT33 x y HxE Hyx)).
  pose (n := P[x]).
  assert (Hnω : n ∈ ω) by (unfold n; exact Hfx).
  assert (Hxn : x ≈ n).
  { unfold n. exact (MKT146 (MKT153 HxE)). }
  assert (Hyn : y ≈ n).
  { unfold n. rewrite <- Hpyx. exact (MKT146 (MKT153 HyE)). }
  exact (MKT172_fin_sub n Hnω x y Hxn Hyx Hyn).
Qed.

Theorem MKT173 : ∀ x, Ensemble x -> ~ Finite x
  -> ∃ y, y ⊂ x /\ y <> x /\ x ≈ y.
Proof.
  intros x Hx Hnxfin.
  destruct (MKT140 x Hx) as [f [Hf11 [Hfran HfdomR]]].
  destruct Hf11 as [Hf Hfinv].
  set (α := dom(f)).
  apply AxiomII in HfdomR as [Eα Hαord].
  assert (Hαx : α ≈ x).
  { exists f; split; [split; [exact Hf | exact Hfinv] | split; [reflexivity | exact Hfran]]. }
  assert (Hxα : x ≈ α) by (apply MKT146; exact Hαx).
  (* α is not finite *)
  assert (Hαnotω : α ∉ ω).
  { intro Hαω.
    assert (HαC : α ∈ C) by (apply MKT164; exact Hαω).
    pose proof (proj2 (MKT156 α) HαC) as [HαE Hpα].
    assert (Hpxpα : P[x] = P[α]) by (apply (proj2 (MKT154 x α Hx HαE)); exact Hxα).
    assert (Hfx : Finite x).
    { unfold Finite. rewrite Hpxpα. rewrite Hpα. exact Hαω. }
    exact (Hnxfin Hfx). }
  (* ω ⊂ α *)
  assert (Hωα : ω ⊂ α).
  { pose proof (proj1 (AxiomII ω Ordinal) MKT138) as [Eω Hωord].
    destruct (MKT110 Hωord Hαord) as [Hωin | [Hαin | Hωeq]].
    - destruct Hαord as [_ Hfull]. exact (Hfull ω Hωin).
    - exfalso. exact (Hαnotω Hαin).
    - rewrite Hωeq. intros z Hz. exact Hz. }
  assert (HΦα : Φ ∈ α) by (apply Hωα; exact MKT135a).
  assert (EΦ : Ensemble Φ).
  { pose proof (proj1 (AxiomII Φ (λ x, Integer x)) MKT135a) as [E _]. exact E. }
  (* helper: membership in E *)
  assert (HE_mem : ∀ a b, Ensemble a -> Ensemble b -> ([a,b] ∈ E <-> a ∈ b)).
  { intros a b Ea Eb; split.
    - intros Hab.
      apply AxiomII in Hab as [Eab Hab].
      destruct Hab as [a' [b' [Hab' Ha']]].
      destruct (MKT49b a b Eab) as [Ea0 Eb0].
      destruct (proj1 (MKT55 a b a' b' Ea0 Eb0) Hab') as [Haa' Hbb'].
      rewrite <- Haa' in Ha'. rewrite <- Hbb' in Ha'. exact Ha'.
    - intros Hab.
      apply AxiomII; split.
      + exact (MKT49a Ea Eb).
      + exists a; exists b; split; [reflexivity | exact Hab]. }
  (* predecessor lemma inside ω *)
  assert (Hpred : ∀ γ, γ ∈ ω -> γ ≠ Φ -> ∃ β, β ∈ ω /\ PlusOne β = γ).
  { intros γ Hγω Hγne.
    pose proof (proj1 (AxiomII γ (λ x, Integer x)) Hγω) as [Eγ Hγint].
    destruct Hγint as [Hγord Hγwo_inv].
    destruct Hγwo_inv as [Hconn Hwosub].
    assert (Hγsub : γ ⊂ γ) by (intros z Hz; exact Hz).
    destruct (Hwosub γ Hγsub Hγne) as [β [Hβγ Hβmax]].
    exists β.
    split.
    - pose proof (proj1 (AxiomII ω Ordinal) MKT138) as [Eω Hωord].
      destruct Hωord as [_ Hωfull].
      exact (Hωfull γ Hγω β Hβγ).
    - pose proof (proj1 (AxiomII ω Ordinal) MKT138) as [Eω Hωord].
      destruct Hωord as [_ Hωfull].
      assert (Hβω : β ∈ ω) by (exact (Hωfull γ Hγω β Hβγ)).
      pose proof (proj1 (AxiomII β (λ x, Integer x)) Hβω) as [Eβ Hintβ].
      destruct Hintβ as [Hβord _].
      apply AxiomI; intros z; split.
      + intros Hz.
        unfold PlusOne in Hz.
        apply (proj2 (MKT4 β ([β]) z)) in Hz.
        destruct Hz as [Hzβ | Hzβs].
        * destruct Hγord as [_ Hγfull].
          exact (Hγfull β Hβγ z Hzβ).
        * assert (Hzβeq : z = β) by (apply (proj1 (MKT41 β Eβ z)); exact Hzβs).
          rewrite Hzβeq. exact Hβγ.
      + intros Hz.
        assert (Hzord : Ordinal z) by (apply (MKT111 γ z Hγord Hz)).
        destruct (MKT110 Hzord Hβord) as [Hzβ | [Hβz | Hzeq]].
        * apply (proj1 (MKT4 β ([β]) z)); left; exact Hzβ.
        * exfalso.
          apply (Hβmax z Hz).
          unfold Rrelation.
          assert (Ez : Ensemble z) by (unfold Ensemble; eauto).
          apply (proj2 (MKT_inv_in E z β Ez Eβ)).
          apply (proj2 (HE_mem β z Eβ Ez)).
          exact Hβz.
        * apply (proj1 (MKT4 β ([β]) z)); right.
          apply (proj2 (MKT41 β Eβ z)); exact Hzeq. }
  (* the shift bijection *)
  set (shift := \{\ λ β γ, β ∈ α /\ ((β ∈ ω /\ γ = PlusOne β) \/ (β ∉ ω /\ γ = β)) \}\).
  assert (Hshift_char : ∀ β γ, [β,γ] ∈ shift <->
    Ensemble ([β,γ]) /\ β ∈ α
    /\ ((β ∈ ω /\ γ = PlusOne β) \/ (β ∉ ω /\ γ = β))).
  { intros β γ; split.
    - intros Hβγ.
      apply AxiomII in Hβγ as [Eβγ Hβγ].
      destruct Hβγ as [β' [γ' [Hβγ' Hpred']]].
      destruct Hpred' as [Hβ'α Hdisj].
      assert (Eβ'γ' : Ensemble ([β',γ'])) by (rewrite <- Hβγ'; exact Eβγ).
      destruct (MKT49b β' γ' Eβ'γ') as [Eβ' Eγ'].
      destruct (MKT49b β γ Eβγ) as [Eβ Eγ].
      destruct (proj1 (MKT55 β γ β' γ' Eβ Eγ) Hβγ') as [Hββ' Hγγ'].
      subst β' γ'.
      split; [exact Eβγ | split; [exact Hβ'α | exact Hdisj]].
    - intros [Eβγ [Hβα Hdisj]].
      apply AxiomII; split; [exact Eβγ |].
      exists β; exists γ; split; [reflexivity | split; [exact Hβα | exact Hdisj]]. }
  assert (Hshift_func : Function shift).
  { split.
    - intros z Hz.
      apply AxiomII in Hz as [Ez Hz].
      destruct Hz as [β [γ [Hzβγ _]]].
      exists β; exists γ; exact Hzβγ.
    - intros β γ1 γ2 Hβγ1 Hβγ2.
      destruct (proj1 (Hshift_char β γ1) Hβγ1) as [Eβγ1 [Hβα1 Hdisj1]].
      destruct (proj1 (Hshift_char β γ2) Hβγ2) as [Eβγ2 [Hβα2 Hdisj2]].
      destruct Hdisj1 as [H1 | H1']; destruct Hdisj2 as [H2 | H2'].
      + destruct H1 as [Hβω1 Hγ1]. destruct H2 as [Hβω2 Hγ2].
        rewrite Hγ1. rewrite Hγ2. reflexivity.
      + destruct H1 as [Hβω1 Hγ1]. destruct H2' as [Hβnω2 Hγ2].
        exfalso. exact (Hβnω2 Hβω1).
      + destruct H1' as [Hβnω1 Hγ1]. destruct H2 as [Hβω2 Hγ2].
        exfalso. exact (Hβnω1 Hβω2).
      + destruct H1' as [Hβnω1 Hγ1]. destruct H2' as [Hβnω2 Hγ2].
        rewrite Hγ1. rewrite Hγ2. reflexivity. }
  assert (Hshift_11 : Function1_1 shift).
  { split; [exact Hshift_func |].
    unfold Function; split.
    - intros z Hz.
      apply AxiomII in Hz as [Ez Hz].
      destruct Hz as [β [γ [Hzβγ _]]].
      exists β; exists γ; exact Hzβγ.
    - intros a b c Hab Hac.
      assert (Eab : Ensemble ([a,b])) by (unfold Ensemble; exists (shift⁻¹); exact Hab).
      destruct (MKT49b a b Eab) as [Ea Eb].
      assert (Eac : Ensemble ([a,c])) by (unfold Ensemble; exists (shift⁻¹); exact Hac).
      destruct (MKT49b a c Eac) as [Ea' Ec].
      assert (Hba : [b,a] ∈ shift) by (apply (proj1 (MKT_inv_in shift a b Ea Eb)); exact Hab).
      assert (Hca : [c,a] ∈ shift) by (apply (proj1 (MKT_inv_in shift a c Ea' Ec)); exact Hac).
      destruct (proj1 (Hshift_char b a) Hba) as [Eba [Hba_α Hdisj1]].
      destruct (proj1 (Hshift_char c a) Hca) as [Eca [Hca_α Hdisj2]].
      destruct Hdisj1 as [H1 | H1']; destruct Hdisj2 as [H2 | H2'].
      + destruct H1 as [Hbω Ha1]. destruct H2 as [Hcω Ha2].
        assert (Hp : PlusOne b = PlusOne c).
        { rewrite <- Ha1. rewrite Ha2. reflexivity. }
        exact (MKT136 b c Hbω Hcω Hp).
      + destruct H1 as [Hbω Ha1]. destruct H2' as [Hc_nω Ha2].
        exfalso.
        assert (Hcω : c ∈ ω).
        { rewrite <- Ha2. rewrite Ha1. apply MKT134. exact Hbω. }
        exact (Hc_nω Hcω).
      + destruct H1' as [Hb_nω Ha1]. destruct H2 as [Hcω Ha2].
        exfalso.
        assert (Hbω : b ∈ ω).
        { rewrite <- Ha1. rewrite Ha2. apply MKT134. exact Hcω. }
        exact (Hb_nω Hbω).
      + destruct H1' as [Hb_nω Ha1]. destruct H2' as [Hc_nω Ha2].
        rewrite <- Ha1. rewrite <- Ha2. reflexivity. }
  assert (Hshift_dom : dom(shift) = α).
  { apply AxiomI; intros β; split.
    - intros Hβ.
      apply AxiomII in Hβ as [Eβ Hβ].
      destruct Hβ as [γ Hβγ].
      destruct (proj1 (Hshift_char β γ) Hβγ) as [Eβγ [Hβα _]].
      exact Hβα.
    - intros Hβα.
      assert (Eβ : Ensemble β) by (unfold Ensemble; eauto).
      apply AxiomII; split; [exact Eβ |].
      destruct (classic (β ∈ ω)) as [Hβω | Hβnω].
      + exists (PlusOne β).
        apply AxiomII; split.
        * pose proof (MKT134 Hβω) as Hpω.
          pose proof (proj1 (AxiomII (PlusOne β) (λ x, Integer x)) Hpω) as [Ep _].
          exact (MKT49a Eβ Ep).
        * exists β; exists (PlusOne β); split; [reflexivity |].
          split; [exact Hβα | left; split; [exact Hβω | reflexivity]].
      + exists β.
        apply AxiomII; split.
        * exact (MKT49a Eβ Eβ).
        * exists β; exists β; split; [reflexivity |].
          split; [exact Hβα | right; split; [exact Hβnω | reflexivity]]. }
  assert (Hshift_ran : ran(shift) = α ~ [Φ]).
  { apply AxiomI; intros γ; split.
    - intros Hγ.
      apply AxiomII in Hγ as [Eγ Hγ].
      destruct Hγ as [β Hβγ].
      destruct (proj1 (Hshift_char β γ) Hβγ) as [Eβγ [Hβα Hdisj]].
      destruct (MKT49b β γ Eβγ) as [Eβ Eγ'].
      apply AxiomII; split; [exact Eγ' | split].
      + destruct Hdisj as [H1 | H1'].
        * destruct H1 as [Hβω Hγβ].
          rewrite Hγβ. apply Hωα. apply MKT134. exact Hβω.
        * destruct H1' as [Hβnω Hγβ].
          rewrite Hγβ. exact Hβα.
      + apply AxiomII; split; [exact Eγ' |].
        intro HγΦ0.
        apply (proj1 (MKT41 Φ EΦ γ)) in HγΦ0.
        destruct Hdisj as [H1 | H1'].
        * destruct H1 as [Hβω Hγβ].
          assert (Hne : Φ ≠ PlusOne β) by (apply (MKT135b β Hβω)).
          apply Hne. symmetry.
          rewrite <- Hγβ. exact HγΦ0.
        * destruct H1' as [Hβnω Hγβ].
          rewrite Hγβ in HγΦ0.
          apply Hβnω.
          rewrite HγΦ0. exact MKT135a.
    - intros Hγ.
      apply AxiomII in Hγ as [Eγ' Hγ].
      destruct Hγ as [Hγα Hγn'].
      apply AxiomII in Hγn' as [Eγ'' Hγn].
      apply AxiomII; split; [exact Eγ'' |].
      destruct (classic (γ ∈ ω)) as [Hγω | Hγnω].
      + assert (Hγne : γ ≠ Φ).
        { intro HγΦ. apply Hγn. apply (proj2 (MKT41 Φ EΦ γ)). exact HγΦ. }
        destruct (Hpred γ Hγω Hγne) as [β [Hβω Hβγ]].
        exists β.
        apply AxiomII; split.
        * pose proof (proj1 (AxiomII β (λ x, Integer x)) Hβω) as [Eβ _].
          exact (MKT49a Eβ Eγ').
        * exists β; exists γ; split; [reflexivity |].
          split.
          -- apply Hωα. exact Hβω.
          -- left. split; [exact Hβω | symmetry; exact Hβγ].
      + exists γ.
        apply AxiomII; split.
        * exact (MKT49a Eγ' Eγ').
        * exists γ; exists γ; split; [reflexivity |].
          split; [exact Hγα | right; split; [exact Hγnω | reflexivity]]. }
  assert (Hshift_eq : α ≈ (α ~ [Φ])).
  { exists shift; split; [exact Hshift_11 | split; [exact Hshift_dom | exact Hshift_ran]]. }
  set (S := α ~ [Φ]).
  assert (HSα : S ⊂ α).
  { intros z Hz. unfold S in Hz. apply AxiomII in Hz as [E [Hzα _]]. exact Hzα. }
  assert (HSne : S ≠ α).
  { intro H.
    assert (HΦS : Φ ∈ S) by (rewrite H; exact HΦα).
    unfold S in HΦS.
    apply AxiomII in HΦS as [E [HΦα' HΦn']].
    apply AxiomII in HΦn' as [E' HΦn''].
    apply HΦn''.
    apply (proj2 (MKT41 Φ EΦ Φ)). reflexivity. }
  set (g := f | (S)).
  assert (Hg_func : Function g) by (unfold g; apply MKT126a; exact Hf).
  assert (Hg_sub : g ⊂ f).
  { intros z Hz. unfold g in Hz. apply AxiomII in Hz as [E [Hzf _]]. exact Hzf. }
  assert (Hg_dom : dom(g) = S).
  { unfold g. rewrite (MKT126b f S Hf).
    apply (proj2 (MKT30 S (dom(f)))).
    exact HSα. }
  assert (Hg11 : Function1_1 g).
  { split; [exact Hg_func |].
    unfold Function; split.
    - intros z Hz.
      apply AxiomII in Hz as [Ez Hz].
      destruct Hz as [a [b [Hzb _]]].
      exists a; exists b; exact Hzb.
    - intros a b c Hab Hac.
      assert (Eab : Ensemble ([a,b])) by (unfold Ensemble; exists (g⁻¹); exact Hab).
      destruct (MKT49b a b Eab) as [Ea Eb].
      assert (Eac : Ensemble ([a,c])) by (unfold Ensemble; exists (g⁻¹); exact Hac).
      destruct (MKT49b a c Eac) as [Ea' Ec].
      assert (Hba : [b,a] ∈ g) by (apply (proj1 (MKT_inv_in g a b Ea Eb)); exact Hab).
      assert (Hca : [c,a] ∈ g) by (apply (proj1 (MKT_inv_in g a c Ea' Ec)); exact Hac).
      assert (Hba_f : [b,a] ∈ f) by (exact (Hg_sub ([b,a]) Hba)).
      assert (Hca_f : [c,a] ∈ f) by (exact (Hg_sub ([c,a]) Hca)).
      assert (Hab_finv : [a,b] ∈ f⁻¹) by (apply (proj2 (MKT_inv_in f a b Ea Eb)); exact Hba_f).
      assert (Hac_finv : [a,c] ∈ f⁻¹) by (apply (proj2 (MKT_inv_in f a c Ea' Ec)); exact Hca_f).
      exact (proj2 Hfinv a b c Hab_finv Hac_finv). }
  set (y := ran(g)).
  assert (Hyx : y ⊂ x).
  { intros z Hz. unfold y in Hz.
    apply AxiomII in Hz as [Ez Hz].
    destruct Hz as [t Htz].
    assert (Hzr : z ∈ ran(f)).
    { apply AxiomII; split; [exact Ez | exists t; exact (Hg_sub ([t,z]) Htz)]. }
    rewrite <- Hfran. exact Hzr. }
  assert (Hgy : S ≈ y).
  { exists g; split; [exact Hg11 | split; [exact Hg_dom | reflexivity]]. }
  assert (Hyne : y ≠ x).
  { intro Hyx_eq.
    assert (HΦdom : Φ ∈ dom(f)) by (unfold α in HΦα; exact HΦα).
    assert (HΦg : [Φ, f[Φ]] ∈ f).
    { apply (MKT_dom_val f Φ Hf); exact HΦdom. }
    assert (EfΦ : Ensemble (f[Φ])).
    { assert (E : Ensemble ([Φ, f[Φ]])) by (unfold Ensemble; exists f; exact HΦg).
      exact (proj2 (MKT49b Φ (f[Φ]) E)). }
    assert (HfΦr : f[Φ] ∈ ran(f)).
    { apply AxiomII; split; [exact EfΦ | exists Φ; exact HΦg]. }
    assert (HfΦx : f[Φ] ∈ x) by (rewrite <- Hfran; exact HfΦr).
    assert (HfΦy : f[Φ] ∈ y) by (rewrite Hyx_eq; exact HfΦx).
    unfold y in HfΦy.
    apply AxiomII in HfΦy as [EfΦ' HfΦy].
    destruct HfΦy as [t Ht].
    assert (Etf : Ensemble ([t, f[Φ]])) by (unfold Ensemble; exists g; exact Ht).
    destruct (MKT49b t (f[Φ]) Etf) as [Et EfΦ0].
    assert (Htf : [t, f[Φ]] ∈ f).
    { unfold g in Ht. apply AxiomII in Ht as [E [Htf _]]. exact Htf. }
    assert (HtS : t ∈ S).
    { unfold g in Ht. apply AxiomII in Ht as [E [_ HtxS]].
      apply AxiomII in HtxS as [Et' HtxS'].
      destruct HtxS' as [u [v [Huv [Hut Hvmu]]]].
      assert (Euv : Ensemble ([u,v])) by (rewrite <- Huv; exact Et').
      destruct (MKT49b u v Euv) as [Eu Ev].
      destruct (proj1 (MKT55 t (f[Φ]) u v Et EfΦ0) Huv) as [Htu Hfv].
      subst u; subst v.
      exact Hut. }
    assert (HtΦ : t = Φ).
    { assert (Hft_inv : [f[Φ], t] ∈ f⁻¹).
      { apply (proj2 (MKT_inv_in f (f[Φ]) t EfΦ Et)). exact Htf. }
      assert (HfΦ_inv : [f[Φ], Φ] ∈ f⁻¹).
      { apply (proj2 (MKT_inv_in f (f[Φ]) Φ EfΦ EΦ)). exact HΦg. }
      exact (proj2 Hfinv (f[Φ]) t Φ Hft_inv HfΦ_inv). }
    assert (HΦnS : Φ ∉ S).
    { intro HΦS0.
      unfold S in HΦS0.
      apply AxiomII in HΦS0 as [E [HΦα' HΦn']].
      apply AxiomII in HΦn' as [E' HΦn''].
      apply HΦn''.
      apply (proj2 (MKT41 Φ EΦ Φ)). reflexivity. }
    rewrite HtΦ in HtS.
    exact (HΦnS HtS). }
  exists y.
  split; [exact Hyx | split; [exact Hyne |]].
  assert (Hαy : α ≈ y).
  { apply (MKT147 S α y).
    - exact Hshift_eq.
    - exact Hgy. }
  exact (MKT147 α x y Hxα Hαy).
Qed.

Theorem MKT174 : ∀ x, x ∈ (R ~ ω) -> P[PlusOne x] = P[x].
Proof.
  intros x Hx.
  apply AxiomII in Hx as [Ex Hx].
  destruct Hx as [HxR Hxnω'].
  apply AxiomII in Hxnω' as [Ex' Hxnω].
  apply AxiomII in HxR as [ExR HxOrd].
  assert (EΦ : Ensemble Φ).
  { pose proof (proj1 (AxiomII Φ (λ x, Integer x)) MKT135a) as [E _]. exact E. }
  assert (HωOrd : Ordinal ω).
  { pose proof (proj1 (AxiomII ω Ordinal) MKT138) as [E H]. exact H. }
  (* 每个非零整数都是某个整数的后继 *)
  assert (Hpred : ∀ γ, γ ∈ ω -> γ ≠ Φ -> ∃ β, β ∈ ω /\ PlusOne β = γ).
  { intros γ Hγω Hγne.
    pose (S := \{ λ γ, γ ∈ ω /\ (γ = Φ \/ ∃ β, β ∈ ω /\ PlusOne β = γ) \}).
    assert (HSω : S ⊂ ω).
    { intros z Hz. apply AxiomII in Hz as [E [Hzω _]]. exact Hzω. }
    assert (HΦS : Φ ∈ S).
    { apply AxiomII; split; [exact EΦ | split; [exact MKT135a | left; reflexivity]]. }
    assert (HsuccS : ∀ u, u ∈ S -> PlusOne u ∈ S).
    { intros u Hu.
      apply AxiomII in Hu as [Eu Hu].
      destruct Hu as [Huω Hsucc].
      apply AxiomII; split.
      - pose proof (MKT134 Huω) as Hp. apply AxiomII in Hp as [Ep _]. exact Ep.
      - split.
        + exact (MKT134 Huω).
        + right. exists u. split; [exact Huω | reflexivity]. }
    assert (HS : S = ω) by (apply (MKT137 S HSω HΦS HsuccS)).
    assert (HγS : γ ∈ S) by (rewrite HS; exact Hγω).
    apply AxiomII in HγS as [E HγS].
    destruct HγS as [Hγω' Hsucc].
    destruct Hsucc as [HγΦ | [β [Hβω Hsuccβ]]].
    - exfalso. exact (Hγne HγΦ).
    - exists β; split; [exact Hβω | exact Hsuccβ]. }
  (* x 是无限序数，故 ω ⊂ x *)
  assert (Hωx_sub : ω ⊂ x).
  { destruct (MKT110 HxOrd HωOrd) as [Hxω | [Hωx | Hxωeq]].
    - exfalso. exact (Hxnω Hxω).
    - destruct HxOrd as [_ Hfull]. exact (Hfull ω Hωx).
    - subst x. exact (MKT26a ω). }
  (* x ~ ω 的元素刻画 *)
  assert (Hxw_char : ∀ u, u ∈ (x ~ ω) <-> Ensemble u /\ u ∈ x /\ u ∉ ω).
  { intro u; split.
    - intros Hu.
      apply AxiomII in Hu as [Eu Hu].
      destruct Hu as [Hux Hunw].
      apply AxiomII in Hunw as [Eu' Hnw].
      split; [exact Eu | split; [exact Hux | exact Hnw]].
    - intros [Eu [Hux Hnw]].
      apply AxiomII; split; [exact Eu | split; [exact Hux |
        apply AxiomII; split; [exact Eu | exact Hnw]]]. }
  (* Hilbert 旅馆平移：把 x 映射到 x ∪ {x} *)
  set (g := \{\ λ u v, (u = x /\ v = Φ)
    \/ (u ∈ ω /\ v = PlusOne u)
    \/ (u ∈ (x ~ ω) /\ v = u) \}\).
  assert (Hg_char : ∀ u v, [u,v] ∈ g <->
    Ensemble ([u,v]) /\ ((u = x /\ v = Φ)
    \/ (u ∈ ω /\ v = PlusOne u)
    \/ (u ∈ (x ~ ω) /\ v = u))).
  { intros u v; split.
    - intros Huv.
      apply AxiomII in Huv as [Euv Huv].
      destruct Huv as [u' [v' [Huv' Hpred']]].
      assert (Eu'v' : Ensemble ([u',v'])) by (rewrite <- Huv'; exact Euv).
      destruct (MKT49b u' v' Eu'v') as [Eu' Ev'].
      destruct (MKT49b u v Euv) as [Eu Ev].
      destruct (proj1 (MKT55 u v u' v' Eu Ev) Huv') as [Huu' Hvv'].
      subst u'. subst v'.
      split; [exact Euv | exact Hpred'].
    - intros [Euv Hpred'].
      apply AxiomII; split; [exact Euv |].
      exists u; exists v; split; [reflexivity | exact Hpred']. }
  assert (Hg_func : Function g).
  { unfold Function; split.
    - intros z Hz.
      apply AxiomII in Hz as [Ez Hz].
      destruct Hz as [u [v [Hzuv _]]].
      exists u; exists v; exact Hzuv.
    - intros u v w Huv Huw.
      destruct (proj1 (Hg_char u v) Huv) as [Euv [H1 | [H2 | H3]]].
      + destruct H1 as [Hux Hv].
        destruct (proj1 (Hg_char u w) Huw) as [Euw [H4 | [H5 | H6]]].
        * destruct H4 as [Hux' Hw']. rewrite Hv. rewrite Hw'. reflexivity.
        * destruct H5 as [Huw' Hw']. exfalso. rewrite Hux in Huw'. exact (Hxnω Huw').
        * destruct H6 as [Huw' Hw']. exfalso.
          rewrite Hux in Huw'.
          destruct (proj1 (Hxw_char x) Huw') as [Exx [Hxx _]].
          exact (MKT101 x Hxx).
      + destruct H2 as [Huw0 Hv].
        destruct (proj1 (Hg_char u w) Huw) as [Euw [H4 | [H5 | H6]]].
        * destruct H4 as [Hux Hw']. exfalso. rewrite Hux in Huw0. exact (Hxnω Huw0).
        * destruct H5 as [Huw' Hw']. rewrite Hv. rewrite Hw'. reflexivity.
        * destruct H6 as [Huw' Hw']. exfalso.
          destruct (proj1 (Hxw_char u) Huw') as [Eu [Hux Hu_nw]].
          exact (Hu_nw Huw0).
      + destruct H3 as [Huw' Hv].
        destruct (proj1 (Hg_char u w) Huw) as [Euw [H4 | [H5 | H6]]].
        * destruct H4 as [Hux Hw']. exfalso.
          rewrite Hux in Huw'.
          destruct (proj1 (Hxw_char x) Huw') as [Exx [Hxx _]].
          exact (MKT101 x Hxx).
        * destruct H5 as [Huw_ Hw']. exfalso.
          destruct (proj1 (Hxw_char u) Huw') as [Eu [Hux Hu_nw]].
          exact (Hu_nw Huw_).
        * destruct H6 as [Huw'' Hw']. rewrite Hv. rewrite Hw'. reflexivity. }
  assert (Hg_inj : ∀ u1 u2 v, [u1,v] ∈ g -> [u2,v] ∈ g -> u1 = u2).
  { intros u1 u2 v Hu1v Hu2v.
    destruct (proj1 (Hg_char u1 v) Hu1v) as [E1 [H1 | [H2 | H3]]].
    - destruct H1 as [Hu1x HvΦ].
      destruct (proj1 (Hg_char u2 v) Hu2v) as [E2 [H4 | [H5 | H6]]].
      + destruct H4 as [Hu2x Hv']. rewrite Hu1x. rewrite Hu2x. reflexivity.
      + destruct H5 as [Hu2w Hv'].
        exfalso. apply (MKT135b u2 Hu2w). rewrite <- HvΦ. rewrite Hv'. reflexivity.
      + destruct H6 as [Hu2w Hv'].
        exfalso.
        destruct (proj1 (Hxw_char u2) Hu2w) as [Eu2 [Hux2 Hu2nw]].
        assert (Hu2Φ : u2 = Φ) by congruence.
        apply Hu2nw. rewrite Hu2Φ. exact MKT135a.
    - destruct H2 as [Hu1w Hv1].
      destruct (proj1 (Hg_char u2 v) Hu2v) as [E2 [H4 | [H5 | H6]]].
      + destruct H4 as [Hu2x Hv'].
        exfalso. apply (MKT135b u1 Hu1w). rewrite <- Hv1. rewrite Hv'. reflexivity.
      + destruct H5 as [Hu2w Hv'].
        apply (MKT136 u1 u2 Hu1w Hu2w).
        rewrite <- Hv1. rewrite Hv'. reflexivity.
      + destruct H6 as [Hu2w Hv'].
        exfalso.
        destruct (proj1 (Hxw_char u2) Hu2w) as [Eu2 [Hux2 Hu2nw]].
        apply Hu2nw.
        rewrite <- Hv'. rewrite Hv1.
        exact (MKT134 Hu1w).
    - destruct H3 as [Hu1w Hv1].
      destruct (proj1 (Hg_char u2 v) Hu2v) as [E2 [H4 | [H5 | H6]]].
      + destruct H4 as [Hu2x Hv'].
        exfalso.
        destruct (proj1 (Hxw_char u1) Hu1w) as [Eu1 [Hux1 Hu1nw]].
        assert (Hu1Φ : u1 = Φ) by congruence.
        apply Hu1nw. rewrite Hu1Φ. exact MKT135a.
      + destruct H5 as [Hu2w Hv'].
        exfalso.
        destruct (proj1 (Hxw_char u1) Hu1w) as [Eu1 [Hux1 Hu1nw]].
        apply Hu1nw.
        rewrite <- Hv1. rewrite Hv'.
        exact (MKT134 Hu2w).
      + destruct H6 as [Hu2w Hv'].
        rewrite <- Hv1. rewrite <- Hv'. reflexivity. }
  assert (Hg_11 : Function1_1 g).
  { split; [exact Hg_func |].
    unfold Function; split.
    - intros z Hz.
      apply AxiomII in Hz as [Ez Hz].
      destruct Hz as [a [b [Hzb _]]].
      exists a; exists b; exact Hzb.
    - intros x0 y0 z0 Hxy Hxz.
      assert (Ex0y0 : Ensemble ([x0,y0])) by (unfold Ensemble; exists (g⁻¹); exact Hxy).
      destruct (MKT49b x0 y0 Ex0y0) as [Ex0 Ey0].
      assert (Ex0z0 : Ensemble ([x0,z0])) by (unfold Ensemble; exists (g⁻¹); exact Hxz).
      destruct (MKT49b x0 z0 Ex0z0) as [Ex0' Ez0].
      assert (Hy0x0 : [y0,x0] ∈ g) by (apply (proj1 (MKT_inv_in g x0 y0 Ex0 Ey0)); exact Hxy).
      assert (Hz0x0 : [z0,x0] ∈ g) by (apply (proj1 (MKT_inv_in g x0 z0 Ex0' Ez0)); exact Hxz).
      apply (Hg_inj y0 z0 x0); assumption. }
  assert (Hg_dom : dom(g) = PlusOne x).
  { apply AxiomI; intros u; split.
    - intros Hu.
      apply AxiomII in Hu as [Eu Hu].
      destruct Hu as [v Huv].
      destruct (proj1 (Hg_char u v) Huv) as [Euv [H1 | [H2 | H3]]].
      + destruct H1 as [Hux Hv]. subst u.
        apply (proj1 (MKT4 x ([x]) x)); right.
        apply (proj2 (MKT41 x Ex x)); reflexivity.
      + destruct H2 as [Huw _].
        apply (proj1 (MKT4 x ([x]) u)); left.
        exact (Hωx_sub u Huw).
      + destruct H3 as [Huw _].
        apply (proj1 (MKT4 x ([x]) u)); left.
        destruct (proj1 (Hxw_char u) Huw) as [Eu' [Hux _]].
        exact Hux.
    - intros Hu.
      apply (proj2 (MKT4 x ([x]) u)) in Hu.
      destruct Hu as [Hux | Hus].
      + assert (Eu : Ensemble u) by (exists x; exact Hux).
        apply AxiomII; split; [exact Eu |].
        destruct (classic (u ∈ ω)) as [Huw | Huw'].
        * exists (PlusOne u).
          apply (proj2 (Hg_char u (PlusOne u))).
          split.
          -- apply MKT49a; [exact Eu |].
             pose proof (MKT134 Huw) as Hp.
             apply AxiomII in Hp as [Ep _]. exact Ep.
          -- right; left. split; [exact Huw | reflexivity].
        * exists u.
          apply (proj2 (Hg_char u u)).
          split.
          -- exact (MKT49a Eu Eu).
          -- right; right. split.
             ++ apply (proj2 (Hxw_char u)).
                split; [exact Eu | split; [exact Hux | exact Huw']].
             ++ reflexivity.
      + apply (proj1 (MKT41 x Ex u)) in Hus.
        subst u.
        apply AxiomII; split; [exact Ex |].
        exists Φ.
        apply (proj2 (Hg_char x Φ)).
        split.
        -- exact (MKT49a Ex EΦ).
        -- left. split; reflexivity. }
  assert (Hg_ran : ran(g) = x).
  { apply AxiomI; intros v; split.
    - intros Hv.
      apply AxiomII in Hv as [Ev Hv].
      destruct Hv as [u Huv].
      destruct (proj1 (Hg_char u v) Huv) as [Euv [H1 | [H2 | H3]]].
      + destruct H1 as [Hux HvΦ]. subst u. subst v.
        exact (Hωx_sub Φ MKT135a).
      + destruct H2 as [Huw Hv]. subst v.
        exact (Hωx_sub (PlusOne u) (MKT134 Huw)).
      + destruct H3 as [Huw Hv]. subst v.
        destruct (proj1 (Hxw_char u) Huw) as [Eu [Hux _]].
        exact Hux.
    - intros Hvx.
      assert (Ev : Ensemble v) by (exists x; exact Hvx).
      apply AxiomII; split; [exact Ev |].
      destruct (classic (v = Φ)) as [HvΦ | HvnΦ].
      + subst v.
        exists x.
        apply (proj2 (Hg_char x Φ)).
        split; [exact (MKT49a Ex EΦ) | left; split; reflexivity].
      + destruct (classic (v ∈ ω)) as [Hvw | Hvω'].
        * destruct (Hpred v Hvw HvnΦ) as [u [Huw Hvsucc]].
          exists u.
          apply (proj2 (Hg_char u v)).
          split.
          -- assert (Eu : Ensemble u)
               by (pose proof (proj1 (AxiomII u (λ x, Integer x)) Huw) as [E _]; exact E).
             exact (MKT49a Eu Ev).
          -- right; left. split; [exact Huw | exact (eq_sym Hvsucc)].
        * exists v.
          apply (proj2 (Hg_char v v)).
          split; [exact (MKT49a Ev Ev) |].
          right; right. split.
          ++ apply (proj2 (Hxw_char v)).
             split; [exact Ev | split; [exact Hvx | exact Hvω']].
          ++ reflexivity. }
  assert (HExPlus : Ensemble (PlusOne x)).
  { unfold PlusOne. apply AxiomIV; [exact Ex | apply MKT42; exact Ex]. }
  assert (Hx_eq : PlusOne x ≈ x).
  { exists g; split; [exact Hg_11 | split; [exact Hg_dom | exact Hg_ran]]. }
  apply (proj2 (MKT154 (PlusOne x) x HExPlus Ex)).
  exact Hx_eq.
Qed.

Theorem MKT177 : WellOrdered ≪ (R × R).
Proof.
  unfold WellOrdered.
  (* ---- common helpers ---- *)
  assert (MaxR : ∀ a b, a ∈ R -> b ∈ R -> (a ∪ b) ∈ R).
  { intros a b HaRb HbRb.
    pose proof HaRb as HaR0.
    pose proof HbRb as HbR0.
    apply AxiomII in HaRb as [Ea' HaO'].
    apply AxiomII in HbRb as [Eb' HbO'].
    destruct (MKT110 HaO' HbO') as [Hab | [Hba | Heq]].
    - assert (Hasub : a ⊂ b) by (destruct HbO' as [_ Hfull]; exact (Hfull a Hab)).
      assert (Hab_eq : a ∪ b = b) by (exact (proj2 (MKT29 a b) Hasub)).
      rewrite Hab_eq. exact HbR0.
    - assert (Hbsub : b ⊂ a) by (destruct HaO' as [_ Hfull]; exact (Hfull b Hba)).
      assert (Hba_eq : b ∪ a = a) by (exact (proj2 (MKT29 b a) Hbsub)).
      assert (Hab_eq : a ∪ b = a) by (rewrite (MKT6 a b); exact Hba_eq).
      rewrite Hab_eq. exact HaR0.
    - rewrite Heq. rewrite (MKT5 b). exact HbR0. }
  assert (HEmem : ∀ p q, Ensemble p -> Ensemble q -> ([p,q] ∈ E <-> p ∈ q)).
  { intros p q Ep Eq; split.
    - intros Hpq.
      apply AxiomII in Hpq as [Epq Hpq'].
      destruct Hpq' as [p' [q' [Hpq' Hp'q']]].
      assert (Ep'q' : Ensemble ([p',q'])) by (rewrite <- Hpq'; exact Epq).
      destruct (MKT49b p' q' Ep'q') as [Ep' Eq'].
      assert (Epq0 : Ensemble ([p,q])) by exact Epq.
      destruct (MKT49b p q Epq0) as [Ep0 Eq0].
      destruct (proj1 (MKT55 p q p' q' Ep0 Eq0) Hpq') as [Hpp' Hqq'].
      rewrite <- Hpp' in Hp'q'. rewrite <- Hqq' in Hp'q'. exact Hp'q'.
    - intros Hpq.
      apply AxiomII; split.
      + apply MKT49a; assumption.
      + exists p; exists q; split; [reflexivity | exact Hpq]. }
  assert (Hless_in : ∀ a b, Ensemble ([a,b]) -> a ∈ (R × R) -> b ∈ (R × R)
    -> (∃ u v x y, a = [u,v] /\ b = [x,y] /\ [u,v] ∈ (R × R)
        /\ [x,y] ∈ (R × R)
        /\ ((u ∪ v) ∈ (x ∪ y)
           \/ ((u ∪ v) = (x ∪ y) /\ u ∈ x)
           \/ ((u ∪ v) = (x ∪ y) /\ u = x /\ v ∈ y)))
    -> [a,b] ∈ ≪).
  { intros a b Eab HaRR HbRR Hinner.
    apply AxiomII; split.
    - exact Eab.
    - exists a; exists b; split; [reflexivity |].
      destruct Hinner as [u [v [x [y [Ha' [Hb' [HuvRR [HxyRR Hdisj]]]]]]]].
      exists u; exists v; exists x; exists y.
      split; [exact Ha' | split; [exact Hb' | split; [exact HuvRR | split; [exact HxyRR | exact Hdisj]]]]. }
  assert (Hless_char : ∀ a b, [a,b] ∈ ≪ ->
    ∃ u v x y, a = [u,v] /\ b = [x,y] /\ [u,v] ∈ (R × R)
      /\ [x,y] ∈ (R × R)
      /\ ((u ∪ v) ∈ (x ∪ y)
         \/ ((u ∪ v) = (x ∪ y) /\ u ∈ x)
         \/ ((u ∪ v) = (x ∪ y) /\ u = x /\ v ∈ y))).
  { intros a b Hab.
    apply AxiomII in Hab as [Eab Hab'].
    destruct Hab' as [a' [b' [Hab' Hinner]]].
    assert (Ea'b' : Ensemble ([a',b'])) by (rewrite <- Hab'; exact Eab).
    destruct (MKT49b a' b' Ea'b') as [Ea' Eb'].
    assert (Eab0 : Ensemble ([a,b])) by exact Eab.
    destruct (MKT49b a b Eab0) as [Ea Eb].
    destruct (proj1 (MKT55 a b a' b' Ea Eb) Hab') as [Haa' Hbb'].
    subst a'. subst b'.
    exact Hinner. }
  assert (HpairR : ∀ p u v, p = [u,v] -> p ∈ (R × R)
    -> u ∈ R /\ v ∈ R /\ Ensemble u /\ Ensemble v).
  { intros p0 u0 v0 Hp0 Hp0RR.
    apply AxiomII in Hp0RR as [Ep0 Hp0'].
    destruct Hp0' as [u1 [v1 [Hp01 [Hu1 Hv1]]]].
    assert (Eu1 : Ensemble u1) by (apply AxiomII in Hu1 as [E _]; exact E).
    assert (Ev1 : Ensemble v1) by (apply AxiomII in Hv1 as [E _]; exact E).
    assert (Eu0 : Ensemble u0).
    { assert (Eu0v0 : Ensemble ([u0,v0])) by (rewrite <- Hp0; exact Ep0).
      exact (proj1 (MKT49b u0 v0 Eu0v0)). }
    assert (Ev0 : Ensemble v0).
    { assert (Eu0v0 : Ensemble ([u0,v0])) by (rewrite <- Hp0; exact Ep0).
      exact (proj2 (MKT49b u0 v0 Eu0v0)). }
    assert (Huv_eq : [u0,v0] = [u1,v1]).
    { rewrite <- Hp0. exact Hp01. }
    destruct (proj1 (MKT55 u0 v0 u1 v1 Eu0 Ev0) Huv_eq) as [Hu0u1 Hv0v1].
    subst u1. subst v1.
    split; [exact Hu1 | split; [exact Hv1 | split; assumption]]. }
  assert (HwoR : WellOrdered E R) by (apply MKT107; exact MKT113a).
  destruct HwoR as [HconnR HwosubR].
  split.
  - (* Connect ≪ (R × R) *)
    unfold Connect.
    intros p q Hp Hq.
    pose proof Hp as Hp0.
    pose proof Hq as Hq0.
    apply AxiomII in Hp as [Ep Hp'].
    apply AxiomII in Hq as [Eq Hq'].
    destruct Hp' as [u [v [Hpuv [HuR HvR]]]].
    destruct Hq' as [x [y [Hqxy [HxR HyR]]]].
    pose proof HuR as HuR0.
    pose proof HvR as HvR0.
    pose proof HxR as HxR0.
    pose proof HyR as HyR0.
    apply AxiomII in HuR as [Eu HuO].
    apply AxiomII in HvR as [Ev HvO].
    apply AxiomII in HxR as [Ex HxO].
    apply AxiomII in HyR as [Ey HyO].
    assert (Hm1R : (u ∪ v) ∈ R) by (apply MaxR; [exact HuR0 | exact HvR0]).
    assert (Hm2R : (x ∪ y) ∈ R) by (apply MaxR; [exact HxR0 | exact HyR0]).
    apply AxiomII in Hm1R as [Em1 Hm1O].
    apply AxiomII in Hm2R as [Em2 Hm2O].
    assert (Epv : Ensemble ([u,v])) by (rewrite <- Hpuv; exact Ep).
    assert (Eqv : Ensemble ([x,y])) by (rewrite <- Hqxy; exact Eq).
    assert (Epq : Ensemble ([[u,v],[x,y]])).
    { apply MKT49a; assumption. }
    destruct (MKT110 Hm1O Hm2O) as [Hm12 | [Hm21 | Hmeq]].
    + (* (u∪v) ∈ (x∪y) *)
      left.
      rewrite Hpuv. rewrite Hqxy.
      apply (Hless_in ([u,v]) ([x,y]) Epq).
      * rewrite <- Hpuv. exact Hp0.
      * rewrite <- Hqxy. exact Hq0.
      * exists u; exists v; exists x; exists y.
        split; [reflexivity | split; [reflexivity | split; [rewrite <- Hpuv; exact Hp0 | split; [rewrite <- Hqxy; exact Hq0 |]]]].
        left. exact Hm12.
    + (* (x∪y) ∈ (u∪v) *)
      right; left.
      rewrite Hqxy. rewrite Hpuv.
      apply (Hless_in ([x,y]) ([u,v]) (MKT49a Eqv Epv)).
      * rewrite <- Hqxy. exact Hq0.
      * rewrite <- Hpuv. exact Hp0.
      * exists x; exists y; exists u; exists v.
        split; [reflexivity | split; [reflexivity | split; [rewrite <- Hqxy; exact Hq0 | split; [rewrite <- Hpuv; exact Hp0 |]]]].
        left. exact Hm21.
    + (* (u∪v) = (x∪y) *)
      destruct (MKT110 HuO HxO) as [Hux | [Hxu | Hueq]].
      * (* u ∈ x *)
        left.
        rewrite Hpuv. rewrite Hqxy.
        apply (Hless_in ([u,v]) ([x,y]) Epq).
        -- rewrite <- Hpuv. exact Hp0.
        -- rewrite <- Hqxy. exact Hq0.
        -- exists u; exists v; exists x; exists y.
           split; [reflexivity | split; [reflexivity | split; [rewrite <- Hpuv; exact Hp0 | split; [rewrite <- Hqxy; exact Hq0 |]]]].
           right; left. split; [exact Hmeq | exact Hux].
      * (* x ∈ u *)
        right; left.
        rewrite Hqxy. rewrite Hpuv.
        apply (Hless_in ([x,y]) ([u,v]) (MKT49a Eqv Epv)).
        -- rewrite <- Hqxy. exact Hq0.
        -- rewrite <- Hpuv. exact Hp0.
        -- exists x; exists y; exists u; exists v.
           split; [reflexivity | split; [reflexivity | split; [rewrite <- Hqxy; exact Hq0 | split; [rewrite <- Hpuv; exact Hp0 |]]]].
           right; left. split; [exact (eq_sym Hmeq) | exact Hxu].
      * (* u = x *)
        destruct (MKT110 HvO HyO) as [Hvy | [Hyv | Hveq]].
        -- (* v ∈ y *)
           left.
           rewrite Hpuv. rewrite Hqxy.
           apply (Hless_in ([u,v]) ([x,y]) Epq).
           ++ rewrite <- Hpuv. exact Hp0.
           ++ rewrite <- Hqxy. exact Hq0.
           ++ exists u; exists v; exists x; exists y.
              split; [reflexivity | split; [reflexivity | split; [rewrite <- Hpuv; exact Hp0 | split; [rewrite <- Hqxy; exact Hq0 |]]]].
              right; right. split; [exact Hmeq | split; [exact Hueq | exact Hvy]].
        -- (* y ∈ v *)
           right; left.
           rewrite Hqxy. rewrite Hpuv.
           apply (Hless_in ([x,y]) ([u,v]) (MKT49a Eqv Epv)).
           ++ rewrite <- Hqxy. exact Hq0.
           ++ rewrite <- Hpuv. exact Hp0.
           ++ exists x; exists y; exists u; exists v.
              split; [reflexivity | split; [reflexivity | split; [rewrite <- Hqxy; exact Hq0 | split; [rewrite <- Hpuv; exact Hp0 |]]]].
              right; right. split; [exact (eq_sym Hmeq) | split; [exact (eq_sym Hueq) | exact Hyv]].
        -- (* u = x /\ v = y *)
           right; right.
           subst x. subst y.
           rewrite Hpuv. rewrite Hqxy.
           reflexivity.
  - (* well-order property *)
    intros S HS HSn.
    set (M := \{ λ m, ∃ u v, [u,v] ∈ S /\ m = u ∪ v \}).
    assert (HMsubR : M ⊂ R).
    { intros m Hm.
      apply AxiomII in Hm as [Em Hm'].
      destruct Hm' as [u [v [HuvS Hmuv]]].
      rewrite Hmuv.
      assert (HuvRR : [u,v] ∈ R × R) by (exact (HS ([u,v]) HuvS)).
      destruct (HpairR ([u,v]) u v eq_refl HuvRR) as [HuR [HvR _]].
      apply MaxR; assumption. }
    assert (HMne : M ≠ Φ).
    { intro HM0.
      destruct (MKT_nonempty S HSn) as [s0 Hs0].
      assert (Hs0RR : s0 ∈ R × R) by (exact (HS s0 Hs0)).
      apply AxiomII in Hs0RR as [Es0 Hs0'].
      destruct Hs0' as [u [v [Hs0uv [HuR HvR]]]].
      assert (HuvS : [u,v] ∈ S) by (rewrite <- Hs0uv; exact Hs0).
      apply AxiomII in HuR as [Eu' _].
      apply AxiomII in HvR as [Ev' _].
      assert (HmM : (u ∪ v) ∈ M).
      { apply AxiomII; split.
        - apply AxiomIV; assumption.
        - exists u; exists v; split; [exact HuvS | reflexivity]. }
      rewrite HM0 in HmM.
      apply AxiomII in HmM as [E HmM'].
      apply HmM'; reflexivity. }
    destruct (HwosubR M HMsubR HMne) as [m0 Hm0first0].
    destruct Hm0first0 as [Hm0M Hm0first].
    apply AxiomII in Hm0M as [Em0 Hm0M'].
    destruct Hm0M' as [u0 [v0 [Hu0v0S Hm0eq]]].
    set (U := \{ λ u, ∃ v, [u,v] ∈ S /\ u ∪ v = m0 \}).
    assert (HUsubR : U ⊂ R).
    { intros u Hu.
      apply AxiomII in Hu as [Eu Hu'].
      destruct Hu' as [v [HuvS Huvm]].
      assert (HuvRR : [u,v] ∈ R × R) by (exact (HS ([u,v]) HuvS)).
      destruct (HpairR ([u,v]) u v eq_refl HuvRR) as [HuR _].
      exact HuR. }
    assert (HUne : U ≠ Φ).
    { intro HU0.
      assert (Hu0U : u0 ∈ U).
      { apply AxiomII; split.
        - assert (Hu0v0RR : [u0,v0] ∈ R × R) by (exact (HS ([u0,v0]) Hu0v0S)).
          destruct (HpairR ([u0,v0]) u0 v0 eq_refl Hu0v0RR) as [Hu0R [_ _]].
          apply AxiomII in Hu0R as [E _]. exact E.
        - exists v0; split; [exact Hu0v0S | exact (eq_sym Hm0eq)]. }
      rewrite HU0 in Hu0U.
      apply AxiomII in Hu0U as [E H']. apply H'; reflexivity. }
    destruct (HwosubR U HUsubR HUne) as [u00 Hu00first0].
    destruct Hu00first0 as [Hu00U Hu00first].
    apply AxiomII in Hu00U as [Eu00 Hu00U'].
    destruct Hu00U' as [v00 [Hu00v00S Hm0eq2]].
    set (V := \{ λ v, [u00, v] ∈ S /\ u00 ∪ v = m0 \}).
    assert (HVsubR : V ⊂ R).
    { intros v Hv.
      apply AxiomII in Hv as [Ev Hv'].
      destruct Hv' as [Hu00vS Huvm].
      assert (Hu00vRR : [u00,v] ∈ R × R) by (exact (HS ([u00,v]) Hu00vS)).
      destruct (HpairR ([u00,v]) u00 v eq_refl Hu00vRR) as [_ [HvR _]].
      exact HvR. }
    assert (HVne : V ≠ Φ).
    { intro HV0.
      assert (Hv00V : v00 ∈ V).
      { apply AxiomII; split.
        - assert (Hu00v00RR : [u00,v00] ∈ R × R) by (exact (HS ([u00,v00]) Hu00v00S)).
          destruct (HpairR ([u00,v00]) u00 v00 eq_refl Hu00v00RR) as [_ [Hv00R _]].
          apply AxiomII in Hv00R as [E _]. exact E.
        - split; [exact Hu00v00S | exact Hm0eq2]. }
      rewrite HV0 in Hv00V.
      apply AxiomII in Hv00V as [E H']. apply H'; reflexivity. }
    destruct (HwosubR V HVsubR HVne) as [v0' Hv0'first0].
    destruct Hv0'first0 as [Hv0'V Hv0'first].
    apply AxiomII in Hv0'V as [Ev0' Hv0'V'].
    destruct Hv0'V' as [Hu00v0'S Hm0eq3].
    exists ([u00, v0']).
    split.
    + exact Hu00v0'S.
    + intros y HyS Hyz.
      destruct (Hless_char y ([u00, v0']) Hyz) as [u1 [v1 [x1 [y1 [Hy1uv [Hz1xy [HuvRR [HxyRR Hdisj]]]]]]]].
      assert (HyRR : y ∈ R × R) by (exact (HS y HyS)).
      apply AxiomII in HyRR as [Ey HyRR'].
      destruct HyRR' as [a [b [Hyab [HaR HbR]]]].
      assert (HabS : [a,b] ∈ S) by (rewrite <- Hyab; exact HyS).
      assert (Ea : Ensemble a) by (apply AxiomII in HaR as [E _]; exact E).
      assert (Eb : Ensemble b) by (apply AxiomII in HbR as [E _]; exact E).
      destruct (HpairR ([u1,v1]) u1 v1 eq_refl HuvRR) as [Hu1R [Hv1R [Eu1 Ev1]]].
      assert (Huv1eq : [a,b] = [u1,v1]).
      { rewrite <- Hyab. rewrite <- Hy1uv. reflexivity. }
      destruct (proj1 (MKT55 a b u1 v1 Ea Eb) Huv1eq) as [Hau1 Hbv1].
      destruct (HpairR ([x1,y1]) x1 y1 eq_refl HxyRR) as [Hx1R [Hy1R [Ex1 Ey1]]].
      destruct (proj1 (MKT55 u00 v0' x1 y1 Eu00 Ev0') Hz1xy) as [Hu00x1 Hv0'y1].
      destruct Hdisj as [Hcase | [Hcase2 | Hcase3]].
      * (* (u1∪v1) ∈ (x1∪y1) *)
        exfalso.
        assert (Hcase' : (a ∪ b) ∈ m0).
        { rewrite <- Hm0eq3.
          rewrite <- Hau1 in Hcase. rewrite <- Hbv1 in Hcase.
          rewrite <- Hu00x1 in Hcase. rewrite <- Hv0'y1 in Hcase.
          exact Hcase. }
        assert (HmM : (a ∪ b) ∈ M).
        { apply AxiomII; split.
          - apply AxiomIV; assumption.
          - exists a; exists b; split; [exact HabS | reflexivity]. }
        assert (Hnot : ~ Rrelation (a ∪ b) E m0) by (apply Hm0first; exact HmM).
        unfold Rrelation in Hnot.
        apply Hnot.
        apply (proj2 (HEmem (a ∪ b) m0 (AxiomIV Ea Eb) Em0)).
        exact Hcase'.
      * (* (u1∪v1) = (x1∪y1) /\ u1 ∈ x1 *)
        exfalso.
        destruct Hcase2 as [Hmaxeq Hux1].
        assert (Hab_m0 : a ∪ b = m0).
        { rewrite <- Hm0eq3.
          rewrite <- Hau1 in Hmaxeq. rewrite <- Hbv1 in Hmaxeq.
          rewrite <- Hu00x1 in Hmaxeq. rewrite <- Hv0'y1 in Hmaxeq.
          exact Hmaxeq. }
        assert (HaU : a ∈ U).
        { apply AxiomII; split.
          - exact Ea.
          - exists b; split; [exact HabS | exact Hab_m0]. }
        assert (Hnot : ~ Rrelation a E u00) by (apply Hu00first; exact HaU).
        unfold Rrelation in Hnot.
        apply Hnot.
        apply (proj2 (HEmem a u00 Ea Eu00)).
        rewrite Hau1. rewrite Hu00x1. exact Hux1.
      * (* (u1∪v1) = (x1∪y1) /\ u1 = x1 /\ v1 ∈ y1 *)
        exfalso.
        destruct Hcase3 as [Hmaxeq3 [Hu1x1 Hv1y1]].
        assert (Hu1u00 : u1 = u00) by (rewrite <- Hu00x1 in Hu1x1; exact Hu1x1).
        assert (Hab_m0 : a ∪ b = m0).
        { rewrite <- Hm0eq3.
          rewrite <- Hau1 in Hmaxeq3. rewrite <- Hbv1 in Hmaxeq3.
          rewrite <- Hu00x1 in Hmaxeq3. rewrite <- Hv0'y1 in Hmaxeq3.
          exact Hmaxeq3. }
        assert (Hau00 : a = u00).
        { rewrite Hau1. rewrite Hu1u00. reflexivity. }
        assert (HbV : b ∈ V).
        { apply AxiomII; split.
          - exact Eb.
          - split.
            + (* [u00,b] ∈ S *)
              rewrite Hau1 in HabS. rewrite Hu1u00 in HabS. exact HabS.
            + (* u00 ∪ b = m0 *)
              rewrite Hau00 in Hab_m0. exact Hab_m0. }
        assert (Hnot : ~ Rrelation b E v0') by (apply Hv0'first; exact HbV).
        unfold Rrelation in Hnot.
        apply Hnot.
        apply (proj2 (HEmem b v0' Eb Ev0')).
        rewrite Hbv1. rewrite Hv0'y1. exact Hv1y1.
Qed.

Theorem MKT178 : ∀ u v x y, Rrelation ([u,v]) ≪ ([x,y])
  -> [u,v] ∈ ((PlusOne (Max x y)) × (PlusOne (Max x y))).
Proof.
  intros u v x y H.

  assert (MaxR : ∀ a b, a ∈ R -> b ∈ R -> (a ∪ b) ∈ R).
  { intros a b HaRb HbRb.
    pose proof HaRb as HaRb0.
    pose proof HbRb as HbRb0.
    apply AxiomII in HaRb as [Ea HaO].
    apply AxiomII in HbRb as [Eb HbO].
    destruct (MKT110 HaO HbO) as [Hab | [Hba | Heq]].
    - assert (Hasub : a ⊂ b) by (destruct HbO as [_ Hfull]; exact (Hfull a Hab)).
      assert (Hab_eq : a ∪ b = b) by (apply (proj2 (MKT29 a b)); exact Hasub).
      rewrite Hab_eq. exact HbRb0.
    - assert (Hbsub : b ⊂ a) by (destruct HaO as [_ Hfull]; exact (Hfull b Hba)).
      assert (Hba_eq : b ∪ a = a) by (apply (proj2 (MKT29 b a)); exact Hbsub).
      assert (Hab_eq : a ∪ b = a) by (rewrite (MKT6 a b); exact Hba_eq).
      rewrite Hab_eq. exact HaRb0.
    - rewrite Heq. rewrite (MKT5 b). exact HbRb0. }

  assert (OrdMax : ∀ a b, a ∈ R -> b ∈ R
    -> a ∈ PlusOne (a ∪ b) /\ b ∈ PlusOne (a ∪ b)).
  { intros a b HaR HbR.
    apply AxiomII in HaR as [Ea HaOrd].
    apply AxiomII in HbR as [Eb HbOrd].
    assert (Eab : Ensemble (a ∪ b)) by (apply AxiomIV; assumption).
    destruct (MKT110 HaOrd HbOrd) as [Hab | [Hba | Heq]].
    - assert (Hab_eq : a ∪ b = b).
      { apply (proj2 (MKT29 a b)).
        destruct HbOrd as [_ Hfull]. exact (Hfull a Hab). }
      split.
      + apply (proj1 (MKT4 (a∪b) ([a∪b]) a)).
        left. apply (proj1 (MKT4 a b a)). right. exact Hab.
      + apply (proj1 (MKT4 (a∪b) ([a∪b]) b)).
        right. apply (proj2 (MKT41 (a∪b) Eab b)).
        symmetry. exact Hab_eq.
    - assert (Hba_eq : b ∪ a = a).
      { apply (proj2 (MKT29 b a)).
        destruct HaOrd as [_ Hfull]. exact (Hfull b Hba). }
      assert (Hab_eq : a ∪ b = a) by (rewrite (MKT6 a b); exact Hba_eq).
      split.
      + apply (proj1 (MKT4 (a∪b) ([a∪b]) a)).
        right. apply (proj2 (MKT41 (a∪b) Eab a)).
        symmetry. exact Hab_eq.
      + assert (Hb_in : b ∈ a ∪ b).
        { exact (proj1 (MKT4 a b b) (or_introl Hba)). }
        apply (proj1 (MKT4 (a∪b) ([a∪b]) b)).
        left. exact Hb_in.
    - assert (Hab_eq : a ∪ b = a).
      { rewrite Heq. exact (MKT5 b). }
      split.
      + apply (proj1 (MKT4 (a∪b) ([a∪b]) a)).
        right. apply (proj2 (MKT41 (a∪b) Eab a)).
        symmetry. exact Hab_eq.
      + apply (proj1 (MKT4 (a∪b) ([a∪b]) b)).
        right. apply (proj2 (MKT41 (a∪b) Eab b)).
        rewrite Hab_eq. exact (eq_sym Heq). }

  assert (HinR : ∀ a b, [a,b] ∈ (R × R) -> a ∈ R /\ b ∈ R).
  { intros a b Hab.
    apply AxiomII in Hab as [Eab Hab'].
    destruct Hab' as [a' [b' [Hab' [Ha'R Hb'R]]]].
    apply AxiomII in Ha'R as [Ea' Ha'O].
    apply AxiomII in Hb'R as [Eb' Hb'O].
    assert (Ea'b' : Ensemble ([a',b'])) by (apply MKT49a; assumption).
    destruct (MKT49b a b Eab) as [Ea Eb].
    destruct (proj1 (MKT55 a b a' b' Ea Eb) Hab') as [Haa' Hbb'].
    subst a'. subst b'.
    split; apply AxiomII; split; assumption. }

  unfold Rrelation in H.
  apply AxiomII in H as [Epair Hpred].
  destruct Hpred as [a [b [Hzab Hless]]].
  destruct Hless as [u' [v' [x' [y' [Ha [Hb [Huv'R [Hxy'R Hord]]]]]]]].
  destruct (MKT49b ([u,v]) ([x,y]) Epair) as [Euv Exy].
  destruct (MKT49b u v Euv) as [Eu Ev].
  destruct (MKT49b x y Exy) as [Ex Ey].
  pose proof Huv'R as Huv'R0.
  pose proof Hxy'R as Hxy'R0.
  apply AxiomII in Huv'R as [Euv'R _].
  apply AxiomII in Hxy'R as [Exy'R _].
  destruct (MKT49b u' v' Euv'R) as [Eu' Ev'].
  destruct (MKT49b x' y' Exy'R) as [Ex' Ey'].
  assert (Hzab' : [[u,v],[x,y]] = [[u',v'],[x',y']]).
  { rewrite Ha in Hzab. rewrite Hb in Hzab. exact Hzab. }
  destruct (proj1 (MKT55 ([u,v]) ([x,y]) ([u',v']) ([x',y']) Euv Exy) Hzab') as [Huv_eq Hxy_eq].
  destruct (proj1 (MKT55 u v u' v' Eu Ev) Huv_eq) as [Huu' Hvv'].
  destruct (proj1 (MKT55 x y x' y' Ex Ey) Hxy_eq) as [Hxx' Hyy'].
  subst u'. subst v'. subst x'. subst y'.
  destruct (HinR u v Huv'R0) as [HuR HvR].
  destruct (HinR x y Hxy'R0) as [HxR HyR].
  unfold Max in Hord.
  destruct Hord as [Hcase1 | Hord'].
  - (* u∪v ∈ x∪y *)
    assert (HxyR' : (x ∪ y) ∈ R) by (apply MaxR; assumption).
    apply AxiomII in HxyR' as [ExyR HxyOrd'].
    destruct HxyOrd' as [_ HxyFull].
    assert (Hsub : u ∪ v ⊂ x ∪ y) by (exact (HxyFull (u∪v) Hcase1)).
    assert (Eab : Ensemble (u ∪ v)) by (apply AxiomIV; assumption).
    assert (Hxym : ∀ t, t ∈ PlusOne (u ∪ v) -> t ∈ PlusOne (x ∪ y)).
    { intros t Ht.
      unfold PlusOne in Ht.
      apply (proj2 (MKT4 (u∪v) ([u∪v]) t)) in Ht.
      destruct Ht as [Htu | Hts].
      - apply (proj1 (MKT4 (x∪y) ([x∪y]) t)); left.
        apply Hsub. exact Htu.
      - apply (proj1 (MKT4 (x∪y) ([x∪y]) t)); left.
        apply (proj1 (MKT41 (u∪v) Eab t)) in Hts.
        rewrite Hts. exact Hcase1. }
    assert (HuA : u ∈ PlusOne (x ∪ y)).
    { apply Hxym. apply (proj1 (OrdMax u v HuR HvR)). }
    assert (HvA : v ∈ PlusOne (x ∪ y)).
    { apply Hxym. apply (proj2 (OrdMax u v HuR HvR)). }
    unfold Max.
    apply AxiomII; split.
    + exact Euv.
    + exists u; exists v; split; [reflexivity | split; [exact HuA | exact HvA]].
  - destruct Hord' as [Hcase2 | Hcase3].
    + destruct Hcase2 as [Hm _].
      destruct (OrdMax u v HuR HvR) as [Hu1 Hv1].
      rewrite Hm in Hu1. rewrite Hm in Hv1.
      unfold Max.
      apply AxiomII; split.
      * exact Euv.
      * exists u; exists v; split; [reflexivity | split; [exact Hu1 | exact Hv1]].
    + destruct Hcase3 as [Hm [_ _]].
      destruct (OrdMax u v HuR HvR) as [Hu1 Hv1].
      rewrite Hm in Hu1. rewrite Hm in Hv1.
      unfold Max.
      apply AxiomII; split.
      * exact Euv.
      * exists u; exists v; split; [reflexivity | split; [exact Hu1 | exact Hv1]].
Qed.

Theorem MKT179 : ∀ {x}, x ∈ (C ~ ω) -> P[x × x] = x.
Proof.
  intros x Hx.

  (* Congruence of Cartesian product with respect to equipollence *)
  assert (Hprod_equiv : ∀ A B C D, Ensemble A -> Ensemble B -> Ensemble C -> Ensemble D
    -> A ≈ C -> B ≈ D -> (A × B) ≈ (C × D)).
  { intros A B C D HA HB HC HD HAC HBD.
    destruct HAC as [f [Hf11 [Hfdom Hfran]]].
    destruct HBD as [g [Hg11 [Hgdom Hgran]]].
    destruct Hf11 as [Hff Hfinv].
    destruct Hg11 as [Hgg Hginv].
    assert (HAens : ∀ t, t ∈ A -> Ensemble t) by (intros; unfold Ensemble; eauto).
    assert (HBens : ∀ t, t ∈ B -> Ensemble t) by (intros; unfold Ensemble; eauto).
    assert (HCens : ∀ t, t ∈ C -> Ensemble t) by (intros; unfold Ensemble; eauto).
    assert (HDens : ∀ t, t ∈ D -> Ensemble t) by (intros; unfold Ensemble; eauto).

    set (h := \{\ λ p q, ∃ a b, p = [a,b] /\ q = [f[a], g[b]] /\ a ∈ A /\ b ∈ B \}\).

    assert (Hh_char : ∀ p q, [p,q] ∈ h <->
      Ensemble ([p,q]) /\ ∃ a b, p = [a,b] /\ q = [f[a], g[b]] /\ a ∈ A /\ b ∈ B).
    { intros p q; split.
      - intros H. apply AxiomII in H as [Epq H].
        destruct H as [p0 [q0 [Hpq0 Hpred]]].
        destruct Hpred as [a [b [Hp0 [Hq0 [Ha Hb]]]]].
        assert (Ep0q0 : Ensemble ([p0,q0])) by (rewrite <- Hpq0; exact Epq).
        destruct (MKT49b p q Epq) as [Ep Eq].
        destruct (MKT49b p0 q0 Ep0q0) as [Ep0 Eq0].
        destruct (proj1 (MKT55 p q p0 q0 Ep Eq) Hpq0) as [Hpp0 Hqq0].
        assert (Hp0' : p = [a,b]).
        { transitivity p0; [exact Hpp0 | exact Hp0]. }
        assert (Hq0' : q = [f[a], g[b]]).
        { transitivity q0; [exact Hqq0 | exact Hq0]. }
        split; [exact Epq |].
        exists a; exists b; split; [exact Hp0' | split; [exact Hq0' | split; [exact Ha | exact Hb]]].
      - intros [Epq [a [b [Hp [Hq [Ha Hb]]]]]].
        apply AxiomII; split; [exact Epq |].
        exists p; exists q; split; [reflexivity |].
        exists a; exists b; split; [exact Hp | split; [exact Hq | split; [exact Ha | exact Hb]]]. }

    assert (Hh_func : Function h).
    { split.
      - intros z Hz. apply AxiomII in Hz as [Ez Hz'].
        destruct Hz' as [p [q [Hzpq _]]]. exists p; exists q; exact Hzpq.
      - intros p q1 q2 H1 H2.
        destruct (proj1 (Hh_char p q1) H1) as [E1 [a1 [b1 [Hp1 [Hq1 [Ha1 Hb1]]]]]].
        destruct (proj1 (Hh_char p q2) H2) as [E2 [a2 [b2 [Hp2 [Hq2 [Ha2 Hb2]]]]]].
        assert (Ea1 : Ensemble a1) by (apply HAens; exact Ha1).
        assert (Eb1 : Ensemble b1) by (apply HBens; exact Hb1).
        assert (Ea2 : Ensemble a2) by (apply HAens; exact Ha2).
        assert (Eb2 : Ensemble b2) by (apply HBens; exact Hb2).
        assert (Hpair_eq : [a1,b1] = [a2,b2]).
        { rewrite <- Hp1. rewrite <- Hp2. reflexivity. }
        destruct (proj1 (MKT55 a1 b1 a2 b2 Ea1 Eb1) Hpair_eq) as [Ha Hb].
        subst a2. subst b2.
        rewrite Hq1. rewrite Hq2. reflexivity. }

    assert (Hfval : ∀ a, a ∈ A -> [a,f[a]] ∈ f /\ f[a] ∈ C /\ Ensemble (f[a])).
    { intros a Ha.
      assert (Had : a ∈ dom(f)) by (rewrite Hfdom; exact Ha).
      assert (Haf : [a,f[a]] ∈ f) by (apply (MKT_dom_val f a Hff); exact Had).
      assert (Eaf : Ensemble ([a,f[a]])) by (unfold Ensemble; exists f; exact Haf).
      assert (Efa : Ensemble (f[a])) by (exact (proj2 (MKT49b a (f[a]) Eaf))).
      assert (Hfr0 : f[a] ∈ ran(f)).
      { apply AxiomII; split; [exact Efa | exists a; exact Haf]. }
      split; [exact Haf | split; [rewrite Hfran in Hfr0; exact Hfr0 | exact Efa]]. }

    assert (Hgval : ∀ b, b ∈ B -> [b,g[b]] ∈ g /\ g[b] ∈ D /\ Ensemble (g[b])).
    { intros b Hb.
      assert (Hbd : b ∈ dom(g)) by (rewrite Hgdom; exact Hb).
      assert (Hbg : [b,g[b]] ∈ g) by (apply (MKT_dom_val g b Hgg); exact Hbd).
      assert (Ebg : Ensemble ([b,g[b]])) by (unfold Ensemble; exists g; exact Hbg).
      assert (Egb : Ensemble (g[b])) by (exact (proj2 (MKT49b b (g[b]) Ebg))).
      assert (Hgr0 : g[b] ∈ ran(g)).
      { apply AxiomII; split; [exact Egb | exists b; exact Hbg]. }
      split; [exact Hbg | split; [rewrite Hgran in Hgr0; exact Hgr0 | exact Egb]]. }

    assert (Hh_dom : dom(h) = A × B).
    { apply AxiomI; intros p; split.
      - intros Hp. apply AxiomII in Hp as [Ep Hp'].
        destruct Hp' as [q Hpq].
        destruct (proj1 (Hh_char p q) Hpq) as [E [a [b [Hpab [Hq [Ha Hb]]]]]].
        apply AxiomII; split; [exact Ep |].
        exists a; exists b; split; [exact Hpab | split; [exact Ha | exact Hb]].
      - intros Hp. apply AxiomII in Hp as [Ep Hp'].
        destruct Hp' as [a [b [Hpab [Ha Hb]]]].
        destruct (Hfval a Ha) as [Haf [HfC Efa]].
        destruct (Hgval b Hb) as [Hbg [HgD Egb]].
        set (q := [f[a], g[b]]).
        assert (Eq : Ensemble q) by (unfold q; apply MKT49a; [exact Efa | exact Egb]).
        assert (Epq : Ensemble ([p,q])) by (apply MKT49a; [exact Ep | exact Eq]).
        apply AxiomII; split; [exact Ep | exists q].
        apply (proj2 (Hh_char p q)); split; [exact Epq |].
        exists a; exists b; split; [exact Hpab | split; [unfold q; reflexivity | split; [exact Ha | exact Hb]]]. }

    assert (Hh_ran : ran(h) = C × D).
    { apply AxiomI; intros q; split.
      - intros Hq. apply AxiomII in Hq as [Eq Hq'].
        destruct Hq' as [p Hpq].
        destruct (proj1 (Hh_char p q) Hpq) as [E [a [b [Hp [Hqab [Ha Hb]]]]]].
        destruct (Hfval a Ha) as [_ [HfC Efa]].
        destruct (Hgval b Hb) as [_ [HgD Egb]].
        apply AxiomII; split; [exact Eq |].
        exists (f[a]); exists (g[b]); split; [exact Hqab | split; [exact HfC | exact HgD]].
      - intros Hq. apply AxiomII in Hq as [Eq Hq'].
        destruct Hq' as [c [d [Hqcd [Hc Hd]]]].
        assert (Ec : Ensemble c) by (apply HCens; exact Hc).
        assert (Ed : Ensemble d) by (apply HDens; exact Hd).
        assert (Hcr : c ∈ ran(f)) by (rewrite Hfran; exact Hc).
        apply AxiomII in Hcr as [Ec0 Hcr'].
        destruct Hcr' as [a Hac].
        assert (Eac : Ensemble ([a,c])) by (unfold Ensemble; exists f; exact Hac).
        destruct (MKT49b a c Eac) as [Ea Ec1].
        assert (Had : a ∈ dom(f)).
        { apply AxiomII; split; [exact Ea | exists c; exact Hac]. }
        assert (Hfa : f[a] = c) by (apply (MKT_fval f a c Hff); exact Hac).
        assert (HaA : a ∈ A) by (rewrite <- Hfdom; exact Had).
        assert (Hdr : d ∈ ran(g)) by (rewrite Hgran; exact Hd).
        apply AxiomII in Hdr as [Ed0 Hdr'].
        destruct Hdr' as [b Hbd].
        assert (Ebd : Ensemble ([b,d])) by (unfold Ensemble; exists g; exact Hbd).
        destruct (MKT49b b d Ebd) as [Eb Ed1].
        assert (Hbd_dom : b ∈ dom(g)).
        { apply AxiomII; split; [exact Eb | exists d; exact Hbd]. }
        assert (Hgb : g[b] = d) by (apply (MKT_fval g b d Hgg); exact Hbd).
        assert (HbB : b ∈ B) by (rewrite <- Hgdom; exact Hbd_dom).
        assert (Eab : Ensemble ([a,b])) by (apply MKT49a; assumption).
        assert (Epq : Ensemble ([[a,b],q])) by (apply MKT49a; [exact Eab | exact Eq]).
        apply AxiomII; split; [exact Eq | exists ([a,b])].
        apply (proj2 (Hh_char ([a,b]) q)); split; [exact Epq |].
        exists a; exists b; split; [reflexivity | split].
        { rewrite Hqcd. rewrite Hfa. rewrite Hgb. reflexivity. }
        { split; [exact HaA | exact HbB]. } }

    assert (Hfinj : ∀ a1 a2, a1 ∈ A -> a2 ∈ A -> f[a1] = f[a2] -> a1 = a2).
    { intros a1 a2 Ha1 Ha2 Hv.
      destruct (Hfval a1 Ha1) as [Haf1 [HfC1 Efa1]].
      destruct (Hfval a2 Ha2) as [Haf2 [HfC2 Efa2]].
      assert (Ea1 : Ensemble a1) by (apply HAens; exact Ha1).
      assert (Ea2 : Ensemble a2) by (apply HAens; exact Ha2).
      assert (Hinv1 : [f[a1], a1] ∈ f⁻¹).
      { apply (proj2 (MKT_inv_in f (f[a1]) a1 Efa1 Ea1)); exact Haf1. }
      assert (Hinv2 : [f[a1], a2] ∈ f⁻¹).
      { apply (proj2 (MKT_inv_in f (f[a1]) a2 Efa1 Ea2)); rewrite Hv; exact Haf2. }
      exact (proj2 Hfinv (f[a1]) a1 a2 Hinv1 Hinv2). }

    assert (Hginj : ∀ b1 b2, b1 ∈ B -> b2 ∈ B -> g[b1] = g[b2] -> b1 = b2).
    { intros b1 b2 Hb1 Hb2 Hv.
      destruct (Hgval b1 Hb1) as [Hbg1 [HgD1 Egb1]].
      destruct (Hgval b2 Hb2) as [Hbg2 [HgD2 Egb2]].
      assert (Eb1 : Ensemble b1) by (apply HBens; exact Hb1).
      assert (Eb2 : Ensemble b2) by (apply HBens; exact Hb2).
      assert (Hinv1 : [g[b1], b1] ∈ g⁻¹).
      { apply (proj2 (MKT_inv_in g (g[b1]) b1 Egb1 Eb1)); exact Hbg1. }
      assert (Hinv2 : [g[b1], b2] ∈ g⁻¹).
      { apply (proj2 (MKT_inv_in g (g[b1]) b2 Egb1 Eb2)); rewrite Hv; exact Hbg2. }
      exact (proj2 Hginv (g[b1]) b1 b2 Hinv1 Hinv2). }

    assert (Hh_inj : ∀ p1 p2 q, [p1,q] ∈ h -> [p2,q] ∈ h -> p1 = p2).
    { intros p1 p2 q H1 H2.
      destruct (proj1 (Hh_char p1 q) H1) as [E1 [a1 [b1 [Hp1 [Hq1 [Ha1 Hb1]]]]]].
      destruct (proj1 (Hh_char p2 q) H2) as [E2 [a2 [b2 [Hp2 [Hq2 [Ha2 Hb2]]]]]].
      destruct (Hfval a1 Ha1) as [Haf1 [HfC1 Efa1]].
      destruct (Hgval b1 Hb1) as [Hbg1 [HgD1 Egb1]].
      destruct (Hfval a2 Ha2) as [Haf2 [HfC2 Efa2]].
      destruct (Hgval b2 Hb2) as [Hbg2 [HgD2 Egb2]].
      assert (Hq_eq : [f[a1], g[b1]] = [f[a2], g[b2]]).
      { rewrite <- Hq1. rewrite <- Hq2. reflexivity. }
      destruct (proj1 (MKT55 (f[a1]) (g[b1]) (f[a2]) (g[b2]) Efa1 Egb1) Hq_eq)
        as [Hf_eq Hg_eq].
      assert (Ha : a1 = a2) by (apply (Hfinj a1 a2 Ha1 Ha2 Hf_eq)).
      assert (Hb : b1 = b2) by (apply (Hginj b1 b2 Hb1 Hb2 Hg_eq)).
      rewrite Hp1. rewrite Hp2. rewrite Ha. rewrite Hb. reflexivity. }

    assert (Hh_inv_func : Function (h⁻¹)).
    { split.
      - intros z Hz. apply AxiomII in Hz as [Ez Hz'].
        destruct Hz' as [p [q [Hzpq _]]]. exists p; exists q; exact Hzpq.
      - intros q p1 p2 H1 H2.
        assert (E1 : Ensemble ([q,p1])) by (unfold Ensemble; exists (h⁻¹); exact H1).
        destruct (MKT49b q p1 E1) as [Eq Ep1].
        assert (E2 : Ensemble ([q,p2])) by (unfold Ensemble; exists (h⁻¹); exact H2).
        destruct (MKT49b q p2 E2) as [Eq' Ep2].
        assert (Hp1q : [p1,q] ∈ h) by (apply (proj1 (MKT_inv_in h q p1 Eq Ep1)); exact H1).
        assert (Hp2q : [p2,q] ∈ h) by (apply (proj1 (MKT_inv_in h q p2 Eq' Ep2)); exact H2).
        exact (Hh_inj p1 p2 q Hp1q Hp2q). }

    assert (Hh11 : Function1_1 h) by (split; [exact Hh_func | exact Hh_inv_func]).
    exists h. split; [exact Hh11 | split; [exact Hh_dom | exact Hh_ran]]. }

  apply NNPP; intro Hnot.

  set (S := \{ λ y, y ∈ C /\ y ∉ ω /\ P[y × y] ≠ y \}).
  assert (HSsub : S ⊂ C).
  { intros y Hy. apply AxiomII in Hy as [Ey [HyC _]]. exact HyC. }

  assert (HxS : x ∈ S).
  { apply AxiomII in Hx as [Ex [HxC Hxnω0]].
    apply AxiomII in Hxnω0 as [Ex0 Hxnω].
    apply AxiomII; split; [exact Ex |].
    split; [exact HxC | split; [exact Hxnω | exact Hnot]]. }

  assert (HSne : S ≠ Φ).
  { intro HS0. rewrite HS0 in HxS. exact (MKT16 HxS). }

  destruct MKT150 as [HCconn HCwo].
  destruct (HCwo S HSsub HSne) as [m Hmmin].
  destruct Hmmin as [HmS Hmfirst].
  apply AxiomII in HmS as [Em [HmC [Hmnotω Hmne]]].

  assert (HmR : m ∈ R) by (apply MKT_C_R; exact HmC).
  assert (Hmord : Ordinal m) by (apply MKT_C_ord; exact HmC).
  destruct (proj2 (MKT156 m) HmC) as [HmE HmP].
  assert (Hens_m : ∀ t, t ∈ m -> Ensemble t) by (intros; unfold Ensemble; eauto).

  assert (Hωord : Ordinal ω).
  { pose proof MKT138 as HωR.
    apply AxiomII in HωR as [_ Hωord]. exact Hωord. }

  assert (Hωm : ω ⊂ m).
  { destruct (MKT110 Hmord Hωord) as [Hmω | [Hωm_in | Heq]].
    - exfalso. exact (Hmnotω Hmω).
    - destruct Hmord as [_ Hfull]. exact (Hfull ω Hωm_in).
    - subst m. apply MKT26a. }

  assert (HΦm : Φ ∈ m) by (apply Hωm; exact MKT135a).

  assert (Hrel_fwd : ∀ a b, Ensemble a -> Ensemble b -> a ∈ b -> Rrelation a E b).
  { intros a b Ea Eb Hab.
    unfold Rrelation.
    apply AxiomII; split.
    - apply MKT49a; assumption.
    - exists a; exists b; split; [reflexivity | exact Hab]. }

  assert (HPlusOrd : ∀ z, Ensemble z -> Ordinal z -> Ordinal (PlusOne z)).
  { intros z Ez [Hconnz Hfullz].
    unfold PlusOne. split.
    - unfold Connect.
      intros u v Hu Hv.
      apply AxiomII in Hu as [Eu [Huz | Hus]].
      apply AxiomII in Hv as [Ev [Hvz | Hvs]].
      + destruct (Hconnz u v Huz Hvz) as [Huv | [Hvu | Hueq]].
        * left; exact Huv.
        * right; left; exact Hvu.
        * right; right; exact Hueq.
      + apply (proj1 (MKT41 z Ez v)) in Hvs. subst v.
        left. apply Hrel_fwd; [exact Eu | exact Ez | exact Huz].
      + apply (proj1 (MKT41 z Ez u)) in Hus. subst u.
        apply AxiomII in Hv as [Ev [Hvz | Hvs]].
        * right; left. apply Hrel_fwd; [exact Ev | exact Ez | exact Hvz].
        * apply (proj1 (MKT41 z Ez v)) in Hvs. subst v.
          right; right; reflexivity.
    - unfold Full.
      intros t Ht.
      apply AxiomII in Ht as [Et [Htz | Hts]].
      + intros u Hut. apply AxiomII; split; [unfold Ensemble; eauto | left; exact (Hfullz t Htz u Hut)].
      + apply (proj1 (MKT41 z Ez t)) in Hts. subst t.
        intros u Huz. apply AxiomII; split; [unfold Ensemble; eauto | left; exact Huz]. }

  assert (Hcard_lt : ∀ γ, γ ∈ m -> P[γ] ∈ m).
  { intros γ Hγm.
    assert (HγE : Ensemble γ) by (unfold Ensemble; exists m; exact Hγm).
    assert (HγR : γ ∈ R).
    { apply AxiomII; split; [exact HγE | exact (MKT111 m γ Hmord Hγm)]. }
    assert (HpγC : P[γ] ∈ C) by (apply MKT_C_val; exact HγE).
    assert (Hpγ_le : P[γ] ≼ γ).
    { apply (MKT_card_le (P[γ]) γ HpγC HγR). apply (MKT153 HγE). }
    destruct Hpγ_le as [Hin | Heq].
    - destruct Hmord as [_ Hfull]. exact (Hfull γ Hγm (P[γ]) Hin).
    - rewrite Heq; exact Hγm. }

  assert (Hlimit : ∀ γ, γ ∈ m -> PlusOne γ ∈ m).
  { intros γ Hγm.
    assert (HγE : Ensemble γ) by (unfold Ensemble; exists m; exact Hγm).
    assert (HγR : γ ∈ R).
    { apply AxiomII; split; [exact HγE | exact (MKT111 m γ Hmord Hγm)]. }
    assert (Hγord : Ordinal γ) by (apply (MKT111 m γ Hmord Hγm)).
    assert (HPord : Ordinal (PlusOne γ)) by (apply HPlusOrd; assumption).
    assert (HPsub : PlusOne γ ⊂ m).
    { intros z Hz. unfold PlusOne in Hz.
      apply AxiomII in Hz as [Ez [Hzγ | Hzs]].
      - destruct Hmord as [_ Hfull]. exact (Hfull γ Hγm z Hzγ).
      - apply (proj1 (MKT41 γ HγE z)) in Hzs. subst z. exact Hγm. }
    destruct (MKT118 (PlusOne γ) m HPord Hmord) as [HPiff _].
    apply HPiff in HPsub.
    destruct HPsub as [HPin | HPeq]; [exact HPin |].
    exfalso.
    assert (Hγnω : γ ∉ ω).
    { intro Hγω. apply Hmnotω.
      assert (Hpoω : PlusOne γ ∈ ω) by (apply MKT134; exact Hγω).
      rewrite HPeq in Hpoω. exact Hpoω. }
    assert (HγRw : γ ∈ (R ~ ω)).
    { apply AxiomII; split; [exact HγE |].
      split; [exact HγR | apply AxiomII; split; [exact HγE | exact Hγnω]]. }
    assert (HPγ : P[PlusOne γ] = P[γ]) by (apply (MKT174 γ HγRw)).
    assert (HmPγ : m = P[γ]).
    { transitivity (P[m]).
      - symmetry; exact HmP.
      - rewrite HPeq in HPγ. exact HPγ. }
    assert (HPγm : P[γ] ∈ m) by (apply Hcard_lt; exact Hγm).
    assert (Hmm : m ∈ m) by (rewrite <- HmPγ in HPγm; exact HPγm).
    exact (MKT101 m Hmm). }

  (* m is equipollent to a subset of m × m *)
  assert (Hm_le_sq : m ≼ P[m × m]).
  { set (D := \{ λ p, ∃ a, a ∈ m /\ p = [a,Φ] \}).
    set (d := \{\ λ a p, a ∈ m /\ p = [a,Φ] \}\).
    assert (EΦ : Ensemble Φ).
    { pose proof (proj1 (AxiomII Φ (λ x, Integer x)) MKT135a) as [E _]. exact E. }

    assert (Hd_char : ∀ a p, [a,p] ∈ d <-> Ensemble ([a,p]) /\ a ∈ m /\ p = [a,Φ]).
    { intros a p; split.
      - intros H. apply AxiomII in H as [E H'].
        destruct H' as [a0 [p0 [Hap Hpred]]].
        assert (Ea0p0 : Ensemble ([a0,p0])) by (rewrite <- Hap; exact E).
        destruct (MKT49b a p E) as [Ea Ep].
        destruct (MKT49b a0 p0 Ea0p0) as [Ea0 Ep0].
        destruct (proj1 (MKT55 a p a0 p0 Ea Ep) Hap) as [Ha Hp].
        subst a0. subst p0.
        split; [exact E | split; [exact (proj1 Hpred) | exact (proj2 Hpred)]].
      - intros [E [Ham Hp]].
        apply AxiomII; split; [exact E |].
        exists a; exists p; split; [reflexivity | split; [exact Ham | exact Hp]]. }

    assert (Hd_func : Function d).
    { split.
      - intros z Hz. apply AxiomII in Hz as [Ez Hz'].
        destruct Hz' as [a [p [Hzap _]]]. exists a; exists p; exact Hzap.
      - intros a p1 p2 H1 H2.
        destruct (proj1 (Hd_char a p1) H1) as [E1 [Ha1 Hp1]].
        destruct (proj1 (Hd_char a p2) H2) as [E2 [Ha2 Hp2]].
        rewrite Hp1. rewrite Hp2. reflexivity. }

    assert (Hd_dom : dom(d) = m).
    { apply AxiomI; intros a; split.
      - intros Ha. apply AxiomII in Ha as [Ea Ha'].
        destruct Ha' as [p Hap].
        destruct (proj1 (Hd_char a p) Hap) as [E [Ham Hp]]. exact Ham.
      - intros Ham.
        assert (Ea : Ensemble a) by (unfold Ensemble; exists m; exact Ham).
        assert (Eaphi : Ensemble ([a,Φ])) by (apply MKT49a; [exact Ea | exact EΦ]).
        apply AxiomII; split; [exact Ea | exists ([a,Φ])].
        apply (proj2 (Hd_char a ([a,Φ]))); split; [apply MKT49a; [exact Ea | exact Eaphi] | split; [exact Ham | reflexivity]]. }

    assert (Hd_ran : ran(d) = D).
    { apply AxiomI; intros p; split.
      - intros Hp. apply AxiomII in Hp as [Ep Hp'].
        destruct Hp' as [a Hap].
        destruct (proj1 (Hd_char a p) Hap) as [E [Ham Hp_eq]].
        apply AxiomII; split; [exact Ep | exists a; split; [exact Ham | exact Hp_eq]].
      - intros Hp. apply AxiomII in Hp as [Ep Hp'].
        destruct Hp' as [a [Ham Hp_eq]].
        apply AxiomII; split; [exact Ep | exists a].
        assert (Ea : Ensemble a) by (unfold Ensemble; exists m; exact Ham).
        apply (proj2 (Hd_char a p)); split; [apply MKT49a; [exact Ea | exact Ep] | split; [exact Ham | exact Hp_eq]]. }

    assert (Hd_inj : ∀ a1 a2 p, [a1,p] ∈ d -> [a2,p] ∈ d -> a1 = a2).
    { intros a1 a2 p H1 H2.
      destruct (proj1 (Hd_char a1 p) H1) as [E1 [Ha1 Hp1]].
      destruct (proj1 (Hd_char a2 p) H2) as [E2 [Ha2 Hp2]].
      assert (Ea1 : Ensemble a1) by (unfold Ensemble; exists m; exact Ha1).
      assert (Ea2 : Ensemble a2) by (unfold Ensemble; exists m; exact Ha2).
      assert (Hpp : [a1,Φ] = [a2,Φ]) by (rewrite <- Hp1; rewrite <- Hp2; reflexivity).
      exact (proj1 (proj1 (MKT55 a1 Φ a2 Φ Ea1 EΦ) Hpp)). }

    assert (Hd_inv_func : Function (d⁻¹)).
    { split.
      - intros z Hz. apply AxiomII in Hz as [Ez Hz'].
        destruct Hz' as [a [p [Hzap _]]]. exists a; exists p; exact Hzap.
      - intros a b c Hab Hac.
        assert (Eab : Ensemble ([a,b])) by (unfold Ensemble; exists (d⁻¹); exact Hab).
        destruct (MKT49b a b Eab) as [Ea Eb].
        assert (Eac : Ensemble ([a,c])) by (unfold Ensemble; exists (d⁻¹); exact Hac).
        destruct (MKT49b a c Eac) as [Ea' Ec].
        assert (Hba : [b,a] ∈ d) by (apply (proj1 (MKT_inv_in d a b Ea Eb)); exact Hab).
        assert (Hca : [c,a] ∈ d) by (apply (proj1 (MKT_inv_in d a c Ea' Ec)); exact Hac).
        exact (Hd_inj b c a Hba Hca). }

    assert (Hd11 : Function1_1 d) by (split; [exact Hd_func | exact Hd_inv_func]).
    assert (HmD : m ≈ D) by (exists d; split; [exact Hd11 | split; [exact Hd_dom | exact Hd_ran]]).

    assert (HDsub : D ⊂ m × m).
    { intros p Hp. apply AxiomII in Hp as [Ep [a [Ham Hp_eq]]].
      apply AxiomII; split; [exact Ep |].
      exists a; exists Φ; split; [exact Hp_eq | split; [exact Ham | exact HΦm]]. }

    assert (HmmE : Ensemble (m × m)) by (apply MKT74; assumption).
    assert (HDens : Ensemble D) by (apply (MKT33 (m×m) D HmmE HDsub)).
    assert (HDm : P[D] = m).
    { transitivity (P[m]).
      - apply (MKT154 D m HDens HmE). apply MKT146. exact HmD.
      - exact HmP. }
    pose proof (MKT158 HDsub) as Hle.
    rewrite HDm in Hle. exact Hle. }

  (* m × m is equipollent to an initial segment of m by MKT99; the proper case is impossible *)
  assert (Hmm_RR : m × m ⊂ R × R).
  { intros p Hp. apply AxiomII in Hp as [Ep [a [b [Hpab [Ham Hbm]]]]].
    assert (HaR : a ∈ R).
    { apply AxiomII; split; [unfold Ensemble; exists m; exact Ham | exact (MKT111 m a Hmord Ham)]. }
    assert (HbR : b ∈ R).
    { apply AxiomII; split; [unfold Ensemble; exists m; exact Hbm | exact (MKT111 m b Hmord Hbm)]. }
    apply AxiomII; split; [exact Ep |].
    exists a; exists b; split; [exact Hpab | split; [exact HaR | exact HbR]]. }

  assert (Hwo_mm : WellOrdered ≪ (m × m)).
  { apply (MKT_wo_sub ≪ (m×m) (R×R) Hmm_RR MKT177). }
  assert (Hwo_Em : WellOrdered E m) by (apply MKT107; exact Hmord).

  assert (Hsq_le_m : P[m × m] ≼ m).
  { destruct (MKT99 (r:=≪) (s:=E) (x:=m×m) (y:=m) Hwo_mm Hwo_Em)
      as [f [Hff [Hfop [Hdomx | Hranm]]]].
    - (* dom(f) = m × m *)
      destruct (OPXY_c f (m×m) m ≪ E Hfop) as [Hff0 [Hfpr [Hfsec_dom Hfsec_ran]]].
      destruct Hfsec_ran as [Hfrun_sub _].
      assert (Hf11 : Function1_1 f) by (apply (MKT96a (f:=f) (r:=≪) (s:=E)); exact Hfpr).
      assert (HmmE : Ensemble (m × m)) by (apply MKT74; assumption).
      assert (HrunE : Ensemble (ran(f))) by (apply (MKT33 m (ran(f)) HmE Hfrun_sub)).
      assert (Hmm_ran : m × m ≈ ran(f)).
      { exists f; split; [exact Hf11 | split; [exact Hdomx | reflexivity]]. }
      assert (HPsq : P[m×m] = P[ran(f)]).
      { apply (proj2 (MKT154 (m×m) (ran(f)) HmmE HrunE)); exact Hmm_ran. }
      pose proof (MKT158 Hfrun_sub) as Hle.
      rewrite <- HPsq in Hle. rewrite HmP in Hle. exact Hle.
    - (* ran(f) = m: a proper initial segment of m × m would have cardinal m *)
      exfalso.
      destruct Hfop as [Hw1 [Hw2 [Hfpr [Hfsec_dom Hfsec_ran]]]].
      assert (Hf11 : Function1_1 f) by (apply (MKT96a (f:=f) (r:=≪) (s:=E)); exact Hfpr).
      assert (HmmE : Ensemble (m × m)) by (apply MKT74; assumption).

      assert (Hdom_ne : dom(f) ≠ m × m).
      { intro Hd.
        assert (Hmm_m : m × m ≈ m).
        { exists f; split; [exact Hf11 | split; [exact Hd | exact Hranm]]. }
        apply Hmne.
        transitivity (P[m]).
        - apply (proj2 (MKT154 (m×m) m HmmE HmE)); exact Hmm_m.
        - exact HmP. }

      destruct (MKT91 (x:=m×m) (y:=dom(f)) (r:=≪) Hfsec_dom Hdom_ne)
        as [p [Hpmm Hdom_eq]].
      apply AxiomII in Hpmm as [Ep [a [b [Hpab [Ham Hbm]]]]].

      assert (Haord : Ordinal a) by (apply (MKT111 m a Hmord Ham)).
      assert (Hbord : Ordinal b) by (apply (MKT111 m b Hmord Hbm)).
      assert (Hγ_m : a ∪ b ∈ m).
      { destruct (MKT110 Haord Hbord) as [Hab | [Hba | Heq]].
        - assert (Hasub : a ⊂ b) by (destruct Hbord as [_ Hfull]; exact (Hfull a Hab)).
          rewrite (proj2 (MKT29 a b) Hasub). exact Hbm.
        - assert (Hbsub : b ⊂ a) by (destruct Haord as [_ Hfull]; exact (Hfull b Hba)).
          rewrite (MKT6 a b). rewrite (proj2 (MKT29 b a) Hbsub). exact Ham.
        - rewrite Heq. rewrite (MKT5 b). exact Hbm. }

      assert (Hpoγ_m : PlusOne (a ∪ b) ∈ m) by (apply Hlimit; exact Hγ_m).
      assert (HEplus : Ensemble (PlusOne (a ∪ b))) by (unfold Ensemble; exists m; exact Hpoγ_m).
      set (B := (PlusOne (a ∪ b)) × (PlusOne (a ∪ b))).
      assert (HBE : Ensemble B) by (unfold B; apply MKT74; assumption).

      assert (Hdom_sub_B : dom(f) ⊂ B).
      { intros u Hu. rewrite Hdom_eq in Hu.
        apply AxiomII in Hu as [Eu [Hu_mm Hu_less]].
        apply AxiomII in Hu_mm as [Eu0 [u1 [u2 [Hu12 [Hu1m Hu2m]]]]].
        rewrite Hu12 in Hu_less. rewrite Hpab in Hu_less.
        assert (Hbound := MKT178 u1 u2 a b Hu_less).
        unfold B. rewrite Hu12.
        unfold Max in Hbound.
        exact Hbound. }

      assert (HdomE : Ensemble dom(f)) by (apply (MKT33 B dom(f) HBE Hdom_sub_B)).
      assert (Hdom_m : dom(f) ≈ m).
      { exists f; split; [exact Hf11 | split; [reflexivity | exact Hranm]]. }
      assert (HPdom : P[dom(f)] = m).
      { transitivity (P[m]).
        - apply (proj2 (MKT154 dom(f) m HdomE HmE)); exact Hdom_m.
        - exact HmP. }

      assert (HBcard_lt : P[B] ∈ m).
      { set (μ := P[PlusOne (a ∪ b)]).
        assert (Hμ_m : μ ∈ m) by (apply (Hcard_lt (PlusOne (a∪b)) Hpoγ_m)).
        assert (HμC : μ ∈ C) by (apply (MKT_C_val (PlusOne (a ∪ b)) HEplus)).
        assert (HμE : Ensemble μ) by (apply (MKT_C_Ens μ HμC)).
        assert (Hplus_μ : PlusOne (a ∪ b) ≈ μ).
        { apply MKT146. unfold μ. exact (@MKT153 (PlusOne (a ∪ b)) HEplus). }
        assert (HBEq : B ≈ μ × μ).
        { unfold B. apply (Hprod_equiv (PlusOne (a∪b)) (PlusOne (a∪b)) μ μ
            HEplus HEplus HμE HμE Hplus_μ Hplus_μ). }
        assert (HμsqE : Ensemble (μ × μ)) by (apply MKT74; assumption).
        assert (HPB : P[B] = P[μ × μ]).
        { apply (proj2 (MKT154 B (μ×μ) HBE HμsqE)); exact HBEq. }
        destruct (classic (μ ∈ ω)) as [Hμω | Hμnω].
        - assert (HμP : P[μ] = μ) by (exact (proj2 (proj2 (MKT156 μ) HμC))).
          assert (Hμfin : Finite μ).
          { unfold Finite. rewrite HμP. exact Hμω. }
          assert (Hμsqfin : Finite (μ × μ)) by (apply (MKT170 μ μ Hμfin Hμfin)).
          unfold Finite in Hμsqfin.
          rewrite HPB. apply Hωm. exact Hμsqfin.
        - assert (HμnS : μ ∉ S).
          { intro HμS.
            assert (HμR_less : Rrelation μ E m).
            { apply Hrel_fwd; [exact HμE | exact HmE | exact Hμ_m]. }
            exact (Hmfirst μ HμS HμR_less). }
          assert (Hμsq_self : P[μ × μ] = μ).
          { apply NNPP; intro Hne.
            assert (HμS : μ ∈ S).
            { apply AxiomII; split; [exact HμE |].
              split; [exact HμC | split; [exact Hμnω | exact Hne]]. }
            exact (HμnS HμS). }
          rewrite HPB. rewrite Hμsq_self. exact Hμ_m. }

      pose proof (MKT158 Hdom_sub_B) as Hle.
      rewrite HPdom in Hle.
      destruct Hle as [HmB | HmBeq].
      + destruct Hmord as [_ Hfull].
        assert (Hmm : m ∈ m) by (apply (Hfull (P[B]) HBcard_lt m HmB)).
        exact (MKT101 m Hmm).
      + assert (Hmm : m ∈ m) by (rewrite <- HmBeq in HBcard_lt; exact HBcard_lt).
        exact (MKT101 m Hmm). }

  destruct Hm_le_sq as [HmS | HmSeq].
  - destruct Hsq_le_m as [Hsqm | Hsqmeq].
    + exact (MKT102 m (P[m×m]) HmS Hsqm).
    + apply Hmne; exact Hsqmeq.
  - apply Hmne; symmetry; exact HmSeq.
Qed.

Theorem MKT180 : ∀ x y, x ∈ C -> y ∈ C -> x ∉ ω \/ y ∉ ω -> x ≠ Φ
  -> y ≠ Φ -> P[x × y] = Max P[x] P[y].
Proof.
  intros x y Hx Hy Hinf Hxne Hyne.

  (* Cartesian product is symmetric up to equipollence, hence same cardinal. *)
  assert (Hswap : ∀ A B, Ensemble A -> Ensemble B
    -> P[A × B] = P[B × A]).
  { intros A B HA HB.
    set (sw := \{\ λ p q, ∃ a b, p = [a,b] /\ q = [b,a]
      /\ a ∈ A /\ b ∈ B \}\).
    assert (Hsw_char : ∀ p q, [p,q] ∈ sw <->
      Ensemble ([p,q]) /\ ∃ a b, p = [a,b] /\ q = [b,a]
        /\ a ∈ A /\ b ∈ B).
    { intros p q; split.
      - intros Hpq.
        apply AxiomII in Hpq as [Epq Hpq'].
        destruct Hpq' as [p0 [q0 [Hpq0 Hpred]]].
        destruct Hpred as [a [b [Hp0 [Hq0 [Ha Hb]]]]].
        assert (Ep0q0 : Ensemble ([p0,q0])) by (rewrite <- Hpq0; exact Epq).
        destruct (MKT49b p q Epq) as [Ep Eq].
        destruct (MKT49b p0 q0 Ep0q0) as [Ep0 Eq0].
        destruct (proj1 (MKT55 p q p0 q0 Ep Eq) Hpq0) as [Hpp Hqq].
        subst p0; subst q0.
        split; [exact Epq |].
        exists a; exists b; split; [exact Hpp | split; [exact Hqq | split; [exact Ha | exact Hb]]].
      - intros [Epq [a [b [Hp [Hq [Ha Hb]]]]]].
        apply AxiomII; split; [exact Epq |].
        exists p; exists q; split; [reflexivity |].
        exists a; exists b; split; [exact Hp | split; [exact Hq | split; [exact Ha | exact Hb]]]. }
    assert (Hsw_func : Function sw).
    { split.
      - intros z Hz.
        apply AxiomII in Hz as [Ez Hz'].
        destruct Hz' as [p [q [Hz _]]].
        exists p; exists q; exact Hz.
      - intros p q r Hpq Hpr.
        destruct (proj1 (Hsw_char p q) Hpq) as [Epq [a [b [Hp [Hq [Ha Hb]]]]]].
        destruct (proj1 (Hsw_char p r) Hpr) as [Epr [c [d [Hp' [Hr [Hc Hd]]]]]].
        assert (Ea : Ensemble a) by (unfold Ensemble; exists A; exact Ha).
        assert (Eb : Ensemble b) by (unfold Ensemble; exists B; exact Hb).
        assert (Habcd : [a,b] = [c,d]).
        { rewrite <- Hp. rewrite <- Hp'. reflexivity. }
        destruct (proj1 (MKT55 a b c d Ea Eb) Habcd) as [Hac Hbd].
        subst c; subst d.
        rewrite Hq. rewrite Hr. reflexivity. }
    assert (Hsw_inj : ∀ p1 p2 q, [p1,q] ∈ sw -> [p2,q] ∈ sw -> p1 = p2).
    { intros p1 p2 q H1 H2.
      destruct (proj1 (Hsw_char p1 q) H1) as [E1 [a [b [Hp1 [Hq1 [Ha Hb]]]]]].
      destruct (proj1 (Hsw_char p2 q) H2) as [E2 [c [d [Hp2 [Hq2 [Hc Hd]]]]]].
      destruct (MKT49b p1 q E1) as [Ep1 Eq1].
      destruct (MKT49b p2 q E2) as [Ep2 Eq2].
      assert (Ea : Ensemble a) by (unfold Ensemble; exists A; exact Ha).
      assert (Eb : Ensemble b) by (unfold Ensemble; exists B; exact Hb).
      assert (Hba_eq : [b,a] = [d,c]).
      { rewrite <- Hq1. rewrite <- Hq2. reflexivity. }
      destruct (proj1 (MKT55 b a d c Eb Ea) Hba_eq) as [Hbd Hac].
      rewrite Hp1. rewrite Hp2. rewrite Hac. rewrite Hbd. reflexivity. }
    assert (Hsw_inv_func : Function (sw⁻¹)).
    { split.
      - intros z Hz.
        apply AxiomII in Hz as [Ez Hz'].
        destruct Hz' as [p [q [Hz _]]].
        exists p; exists q; exact Hz.
      - intros p q r Hpq Hpr.
        assert (Epq : Ensemble ([p,q])) by (unfold Ensemble; exists (sw⁻¹); exact Hpq).
        destruct (MKT49b p q Epq) as [Ep Eq].
        assert (Epr : Ensemble ([p,r])) by (unfold Ensemble; exists (sw⁻¹); exact Hpr).
        destruct (MKT49b p r Epr) as [Ep' Er].
        assert (Hqpsw : [q,p] ∈ sw) by (apply (proj1 (MKT_inv_in sw p q Ep Eq)); exact Hpq).
        assert (Hrpsw : [r,p] ∈ sw) by (apply (proj1 (MKT_inv_in sw p r Ep' Er)); exact Hpr).
        exact (Hsw_inj q r p Hqpsw Hrpsw). }
    assert (Hsw_11 : Function1_1 sw) by (split; [exact Hsw_func | exact Hsw_inv_func]).
    assert (Hsw_dom : dom(sw) = A × B).
    { apply AxiomI; intros p; split.
      - intros Hp.
        apply AxiomII in Hp as [Ep Hp'].
        destruct Hp' as [q Hpq].
        destruct (proj1 (Hsw_char p q) Hpq) as [Epq [a [b [Hpab [Hq [Ha Hb]]]]]].
        apply AxiomII; split; [exact Ep |].
        exists a; exists b; split; [exact Hpab | split; [exact Ha | exact Hb]].
      - intros Hp.
        apply AxiomII in Hp as [Ep Hp'].
        destruct Hp' as [a [b [Hpab [Ha Hb]]]].
        assert (Ea : Ensemble a) by (unfold Ensemble; exists A; exact Ha).
        assert (Eb : Ensemble b) by (unfold Ensemble; exists B; exact Hb).
        set (q := [b,a]).
        assert (Eq : Ensemble q) by (unfold q; apply MKT49a; [exact Eb | exact Ea]).
        assert (Epq : Ensemble ([p,q])) by (apply MKT49a; [exact Ep | exact Eq]).
        apply AxiomII; split; [exact Ep | exists q].
        apply (proj2 (Hsw_char p q)); split; [exact Epq |].
        exists a; exists b; split; [exact Hpab | split; [unfold q; reflexivity | split; [exact Ha | exact Hb]]]. }
    assert (Hsw_ran : ran(sw) = B × A).
    { apply AxiomI; intros q; split.
      - intros Hq.
        apply AxiomII in Hq as [Eq Hq'].
        destruct Hq' as [p Hpq].
        destruct (proj1 (Hsw_char p q) Hpq) as [Epq [a [b [Hpab [Hqab [Ha Hb]]]]]].
        apply AxiomII; split; [exact Eq |].
        exists b; exists a; split; [exact Hqab | split; [exact Hb | exact Ha]].
      - intros Hq.
        apply AxiomII in Hq as [Eq Hq'].
        destruct Hq' as [b [a [Hqab [Hb Ha]]]].
        assert (Ea : Ensemble a) by (unfold Ensemble; exists A; exact Ha).
        assert (Eb : Ensemble b) by (unfold Ensemble; exists B; exact Hb).
        set (p := [a,b]).
        assert (Ep : Ensemble p) by (unfold p; apply MKT49a; [exact Ea | exact Eb]).
        assert (Epq : Ensemble ([p,q])) by (apply MKT49a; [exact Ep | exact Eq]).
        apply AxiomII; split; [exact Eq | exists p].
        apply (proj2 (Hsw_char p q)); split; [exact Epq |].
        exists a; exists b; split; [unfold p; reflexivity | split; [exact Hqab | split; [exact Ha | exact Hb]]]. }
    assert (HAB_equiv : A × B ≈ B × A).
    { exists sw; split; [exact Hsw_11 | split; [exact Hsw_dom | exact Hsw_ran]]. }
    apply (proj2 (MKT154 (A × B) (B × A) (MKT74 HA HB) (MKT74 HB HA)));
      exact HAB_equiv. }

  assert (Haux : ∀ s b, s ∈ C -> b ∈ C -> s ⊂ b -> s ≠ Φ -> b ∉ ω
    -> P[s × b] = b).
  { intros s b HsC HbC Hsb Hsne Hbnω.
    assert (HsE : Ensemble s) by (apply MKT_C_Ens; exact HsC).
    assert (HbE : Ensemble b) by (apply MKT_C_Ens; exact HbC).
    assert (Hbord : Ordinal b) by (apply MKT_C_ord; exact HbC).
    assert (Hpb : P[b] = b) by (exact (proj2 (proj2 (MKT156 b) HbC))).
    assert (HbNotω : b ∈ (¬ω)).
    { apply AxiomII; split; [exact HbE | exact Hbnω]. }
    assert (HbCw : b ∈ (C ~ ω)).
    { apply AxiomII; split; [exact HbE | split; [exact HbC | exact HbNotω]]. }
    assert (Hbsq : P[b × b] = b) by (apply (MKT179 HbCw)).
    assert (HsbE : Ensemble (s × b)) by (apply MKT74; assumption).
    assert (Hprod_sub : s × b ⊂ b × b).
    { intros p Hp.
      apply AxiomII in Hp as [Ep [u [v [Hpuv [Hus Hvb]]]]].
      apply AxiomII; split; [exact Ep |].
      exists u; exists v; split; [exact Hpuv | split; [apply Hsb; exact Hus | exact Hvb]]. }
    assert (Hle1 : P[s × b] ≼ b).
    { pose proof (MKT158 Hprod_sub) as Hle.
      rewrite Hbsq in Hle. exact Hle. }
    assert (Hpsb_sub_b : P[s × b] ⊂ b).
    { destruct Hle1 as [Hin | Heq].
      - destruct Hbord as [_ Hfull]. exact (Hfull (P[s × b]) Hin).
      - rewrite Heq. apply MKT26a. }
    destruct (MKT_nonempty s Hsne) as [a Has].
    assert (HaE : Ensemble a) by (unfold Ensemble; exists s; exact Has).
    set (d := \{\ λ t p, t ∈ b /\ p = [a,t] \}\).
    assert (Hd_char : ∀ t p, [t,p] ∈ d <->
      Ensemble ([t,p]) /\ t ∈ b /\ p = [a,t]).
    { intros t p; split.
      - intros Htp.
        apply AxiomII in Htp as [Etp Htp'].
        destruct Htp' as [t0 [p0 [Htp0 Hpred]]].
        assert (Et0p0 : Ensemble ([t0,p0])) by (rewrite <- Htp0; exact Etp).
        destruct (MKT49b t p Etp) as [Et Ep].
        destruct (MKT49b t0 p0 Et0p0) as [Et0 Ep0].
        destruct (proj1 (MKT55 t p t0 p0 Et Ep) Htp0) as [Ht Hp].
        subst t0; subst p0.
        split; [exact Etp | split; [exact (proj1 Hpred) | exact (proj2 Hpred)]].
      - intros [Etp [Htb Hp]].
        apply AxiomII; split; [exact Etp |].
        exists t; exists p; split; [reflexivity | split; [exact Htb | exact Hp]]. }
    assert (Hd_func : Function d).
    { split.
      - intros z Hz.
        apply AxiomII in Hz as [Ez Hz'].
        destruct Hz' as [t [p [Hz _]]].
        exists t; exists p; exact Hz.
      - intros t p q Htp Htq.
        destruct (proj1 (Hd_char t p) Htp) as [Etp [Htb Hp]].
        destruct (proj1 (Hd_char t q) Htq) as [Etq [Htb' Hq]].
        rewrite Hp. rewrite Hq. reflexivity. }
    assert (Hd_dom : dom(d) = b).
    { apply AxiomI; intros t; split.
      - intros Ht.
        apply AxiomII in Ht as [Et Ht'].
        destruct Ht' as [p Htp].
        destruct (proj1 (Hd_char t p) Htp) as [Etp [Htb _]].
        exact Htb.
      - intros Htb.
        assert (Et : Ensemble t) by (unfold Ensemble; exists b; exact Htb).
        assert (Eat : Ensemble ([a,t])) by (apply MKT49a; [exact HaE | exact Et]).
        apply AxiomII; split; [exact Et | exists ([a,t])].
        apply (proj2 (Hd_char t ([a,t])));
          split; [apply MKT49a; [exact Et | exact Eat] | split; [exact Htb | reflexivity]]. }
    assert (Hd_inj : ∀ t1 t2 p, [t1,p] ∈ d -> [t2,p] ∈ d -> t1 = t2).
    { intros t1 t2 p H1 H2.
      destruct (proj1 (Hd_char t1 p) H1) as [E1 [Ht1b Hp1]].
      destruct (proj1 (Hd_char t2 p) H2) as [E2 [Ht2b Hp2]].
      assert (Et1 : Ensemble t1) by (unfold Ensemble; exists b; exact Ht1b).
      assert (Et2 : Ensemble t2) by (unfold Ensemble; exists b; exact Ht2b).
      assert (Hpp : [a,t1] = [a,t2]) by (rewrite <- Hp1; rewrite <- Hp2; reflexivity).
      exact (proj2 (proj1 (MKT55 a t1 a t2 HaE Et1) Hpp)). }
    assert (Hd_inv_func : Function (d⁻¹)).
    { split.
      - intros z Hz.
        apply AxiomII in Hz as [Ez Hz'].
        destruct Hz' as [t [p [Hz _]]].
        exists t; exists p; exact Hz.
      - intros p t1 t2 Hpt1 Hpt2.
        assert (Ept1 : Ensemble ([p,t1])) by (unfold Ensemble; exists (d⁻¹); exact Hpt1).
        destruct (MKT49b p t1 Ept1) as [Ep Et1].
        assert (Ept2 : Ensemble ([p,t2])) by (unfold Ensemble; exists (d⁻¹); exact Hpt2).
        destruct (MKT49b p t2 Ept2) as [Ep' Et2].
        assert (Ht1p : [t1,p] ∈ d) by (apply (proj1 (MKT_inv_in d p t1 Ep Et1)); exact Hpt1).
        assert (Ht2p : [t2,p] ∈ d) by (apply (proj1 (MKT_inv_in d p t2 Ep' Et2)); exact Hpt2).
        exact (Hd_inj t1 t2 p Ht1p Ht2p). }
    assert (Hd_ran_sub : ran(d) ⊂ s × b).
    { intros p Hp.
      apply AxiomII in Hp as [Ep Hp'].
      destruct Hp' as [t Htp].
      destruct (proj1 (Hd_char t p) Htp) as [Etp [Htb Hp_eq]].
      apply AxiomII; split; [exact Ep |].
      exists a; exists t; split; [exact Hp_eq | split; [exact Has | exact Htb]]. }
    assert (Hd11 : Function1_1 d) by (split; [exact Hd_func | exact Hd_inv_func]).
    destruct (MKT_img (f:=d) (S:=b) Hd11) as [D [HbD HDran]].
    { rewrite Hd_dom. apply MKT26a. }
    assert (HDsub_sb : D ⊂ s × b).
    { intros z Hz. apply Hd_ran_sub. apply HDran. exact Hz. }
    assert (HsbP : s × b ≈ P[s × b]).
    { apply MKT146. apply MKT153. exact HsbE. }
    assert (Hsb_b : s × b ≈ b).
    { apply (MKT159 (s × b) b D (P[s × b]) HsbE HbE HDsub_sb Hpsb_sub_b HsbP HbD). }
    assert (Hpsb_eq : P[s × b] = P[b]).
    { apply (proj2 (MKT154 (s × b) b HsbE HbE)); exact Hsb_b. }
    transitivity (P[b]); [exact Hpsb_eq | exact Hpb]. }

  destruct (proj2 (MKT156 x) Hx) as [HxE Hpx].
  destruct (proj2 (MKT156 y) Hy) as [HyE Hpy].
  assert (Hxord : Ordinal x) by (apply MKT_C_ord; exact Hx).
  assert (Hyord : Ordinal y) by (apply MKT_C_ord; exact Hy).
  destruct (MKT109 (x:=x) (y:=y) Hxord Hyord) as [Hxy | Hyx].
  - (* x ⊂ y *)
    assert (Hynω : y ∉ ω).
    { destruct Hinf as [Hxnω | Hynω]; [| exact Hynω].
      intro Hyω. apply Hxnω.
      assert (HyR : y ∈ R) by (apply MKT_C_R; exact Hy).
      assert (Hxle : x ≼ y).
      { pose proof (MKT157 x y HyR Hxy) as Hle.
        rewrite Hpx in Hle. exact Hle. }
      destruct Hxle as [Hxyin | Hxeq].
      + apply AxiomII; split; [exact HxE |].
        apply AxiomII in Hyω as [_ Hyint].
        exact (MKT132 y x Hyint Hxyin).
      + rewrite Hxeq. exact Hyω. }
    assert (Hunion : x ∪ y = y) by (apply (proj2 (MKT29 x y)); exact Hxy).
    rewrite Hpx. rewrite Hpy. unfold Max. rewrite Hunion.
    apply (Haux x y Hx Hy Hxy Hxne Hynω).
  - (* y ⊂ x *)
    assert (Hxnω : x ∉ ω).
    { destruct Hinf as [Hxnω | Hynω]; [exact Hxnω |].
      intro Hxω. apply Hynω.
      assert (HxR : x ∈ R) by (apply MKT_C_R; exact Hx).
      assert (Hyle : y ≼ x).
      { pose proof (MKT157 y x HxR Hyx) as Hle.
        rewrite Hpy in Hle. exact Hle. }
      destruct Hyle as [Hyxin | Hyeq].
      + apply AxiomII; split; [exact HyE |].
        apply AxiomII in Hxω as [_ Hxint].
        exact (MKT132 x y Hxint Hyxin).
      + rewrite Hyeq. exact Hxω. }
    assert (Hunion : x ∪ y = x).
    { rewrite (MKT6 x y). apply (proj2 (MKT29 y x)); exact Hyx. }
    rewrite Hpx. rewrite Hpy. unfold Max. rewrite Hunion.
    rewrite (Hswap x y HxE HyE).
    apply (Haux y x Hy Hx Hyx Hyne Hxnω).
Qed.

Theorem MKT181a : ∃ f, Order_Pr f E E /\ dom(f) = R
  /\ ran(f) = C ~ ω.
Proof.
  assert (HEmem : ∀ a b, Ensemble a -> Ensemble b -> ([a,b] ∈ E <-> a ∈ b)).
  { intros a b Ea Eb; split.
    - intros Hab.
      apply AxiomII in Hab as [Eab Hab].
      destruct Hab as [a' [b' [Hab' Hmem]]].
      destruct (MKT49b a b Eab) as [Ea0 Eb0].
      assert (Ea'b' : Ensemble ([a',b'])) by (rewrite <- Hab'; exact Eab).
      destruct (MKT49b a' b' Ea'b') as [Ea1 Eb1].
      destruct (proj1 (MKT55 a b a' b' Ea0 Eb0) Hab') as [Haa' Hbb'].
      rewrite <- Haa' in Hmem. rewrite <- Hbb' in Hmem. exact Hmem.
    - intros Hab.
      apply AxiomII; split.
      + apply MKT49a; assumption.
      + exists a; exists b; split; [reflexivity | exact Hab]. }
  assert (Hmemrel : ∀ a b, Ensemble a -> Ensemble b -> Rrelation a E b -> a ∈ b).
  { intros a b Ea Eb Hab.
    unfold Rrelation in Hab.
    apply (proj1 (HEmem a b Ea Eb)). exact Hab. }
  assert (HCw_notEns : ~ Ensemble (C ~ ω)).
  { intro H.
    assert (HωE : Ensemble ω).
    { pose proof MKT138 as HωR.
      apply AxiomII in HωR as [E _]. exact E. }
    assert (HCeq : C = (C ~ ω) ∪ ω).
    { apply AxiomI; intros z; split.
      - intros HzC.
        pose proof (proj1 (AxiomII z (λ x, Cardinal_Number x)) HzC) as [Ez _].
        apply AxiomII; split; [exact Ez |].
        destruct (classic (z ∈ ω)) as [Hzω | Hznω].
        + right; exact Hzω.
        + left; unfold Setminus; apply AxiomII; split.
          * exact Ez.
          * split; [exact HzC | apply AxiomII; split; [exact Ez | exact Hznω]].
      - intros Hz.
        apply AxiomII in Hz as [Ez [Hz | Hz]].
        + unfold Setminus in Hz; apply AxiomII in Hz as [Ez' [HzC _]]; exact HzC.
        + apply MKT164; exact Hz. }
    apply MKT162.
    rewrite HCeq.
    apply AxiomIV; assumption. }
  assert (HwoR : WellOrdered E R) by (apply MKT107; exact MKT113a).
  assert (HCw_subC : (C ~ ω) ⊂ C).
  { intros z Hz. unfold Setminus in Hz.
    apply AxiomII in Hz as [Ez [HzC _]]. exact HzC. }
  assert (HwoCw : WellOrdered E (C ~ ω)).
  { apply (MKT_wo_sub E (C ~ ω) C HCw_subC MKT150). }
  destruct (MKT99 (r:=E) (s:=E) (x:=R) (y:=C ~ ω) HwoR HwoCw)
    as [f [Hff [Hfop Halt]]].
  destruct Hfop as [HwoR0 [HwoCw0 [Hfpr [HfsecR HfsecCw]]]].
  assert (Hran_then_dom : ran(f) = C ~ ω -> dom(f) = R).
  { intros Hran.
    apply NNPP; intro Hdom_ne.
    destruct (MKT91 (x:=R) (y:=dom(f)) (r:=E) HfsecR Hdom_ne)
      as [v [HvR Hdom_eq]].
    apply AxiomII in HvR as [Ev Hvord].
    assert (Hdom_sub_v : dom(f) ⊂ v).
    { intros u Hu.
      rewrite Hdom_eq in Hu.
      apply AxiomII in Hu as [Eu [HuR Hurv]].
      apply (Hmemrel u v Eu Ev Hurv). }
    assert (HdomE : Ensemble dom(f)) by (apply (MKT33 v dom(f) Ev Hdom_sub_v)).
    assert (HranE : Ensemble ran(f)) by (apply (AxiomV (f:=f) Hff HdomE)).
    rewrite Hran in HranE.
    exact (HCw_notEns HranE). }
  assert (Hdom_then_ran : dom(f) = R -> ran(f) = C ~ ω).
  { intros Hdom.
    apply NNPP; intro Hran_ne.
    destruct (MKT91 (x:=C ~ ω) (y:=ran(f)) (r:=E) HfsecCw Hran_ne)
      as [v [HvCw Hran_eq]].
    apply AxiomII in HvCw as [Ev [HvC Hvnω]].
    assert (Hran_sub_v : ran(f) ⊂ v).
    { intros u Hu.
      rewrite Hran_eq in Hu.
      apply AxiomII in Hu as [Eu [HuCw Hurv]].
      apply (Hmemrel u v Eu Ev Hurv). }
    assert (HranE : Ensemble ran(f)) by (apply (MKT33 v ran(f) Ev Hran_sub_v)).
    assert (Hf11 : Function1_1 f) by (apply (MKT96a (f:=f) (r:=E) (s:=E) Hfpr)).
    destruct Hf11 as [Hff0 Hfinv].
    assert (HdominvE : Ensemble dom(f⁻¹)).
    { rewrite MKT_dom_inv. exact HranE. }
    assert (HraninvE : Ensemble ran(f⁻¹)).
    { apply (AxiomV (f:=f⁻¹) Hfinv HdominvE). }
    assert (HR_E : Ensemble R).
    { rewrite MKT_ran_inv in HraninvE. rewrite Hdom in HraninvE. exact HraninvE. }
    exact (MKT113b HR_E). }
  destruct Halt as [Hdom | Hran].
  - assert (Hran' : ran(f) = C ~ ω) by (apply (Hdom_then_ran Hdom)).
    exists f; split; [exact Hfpr | split; [exact Hdom | exact Hran']].
  - assert (Hdom' : dom(f) = R) by (apply (Hran_then_dom Hran)).
    exists f; split; [exact Hfpr | split; [exact Hdom' | exact Hran]].
Qed.

Theorem MKT181b : ∀ f g, Order_Pr f E E -> Order_Pr g E E
  -> dom(f) = R -> dom(g) = R -> ran(f) = C ~ ω
  -> ran(g) = C ~ ω -> f = g.
Proof.
  intros f g Hfpr Hgpr Hfdom Hgdom Hfran Hgran.
  pose proof Hfpr as Hfpr0.
  pose proof Hgpr as Hgpr0.
  destruct Hfpr as [Hff [Hwdf [Hwrf Hordf]]].
  destruct Hgpr as [Hfg [Hwdg [Hwrg Hordg]]].
  assert (HwoR : WellOrdered E R) by (apply MKT107; exact MKT113a).
  assert (HCw_subC : (C ~ ω) ⊂ C).
  { intros z Hz. unfold Setminus in Hz.
    apply AxiomII in Hz as [Ez [HzC _]]. exact HzC. }
  assert (HwoCw : WellOrdered E (C ~ ω)).
  { apply (MKT_wo_sub E (C ~ ω) C HCw_subC MKT150). }
  assert (HsecR_f : rSection dom(f) E R).
  { unfold rSection. split.
    - rewrite Hfdom. apply MKT26a.
    - split; [exact HwoR | intros u v Hu Hv Huv; rewrite Hfdom; exact Hu]. }
  assert (HsecR_g : rSection dom(g) E R).
  { unfold rSection. split.
    - rewrite Hgdom. apply MKT26a.
    - split; [exact HwoR | intros u v Hu Hv Huv; rewrite Hgdom; exact Hu]. }
  assert (HsecCw_f : rSection ran(f) E (C ~ ω)).
  { unfold rSection. split.
    - rewrite Hfran. apply MKT26a.
    - split; [exact HwoCw | intros u v Hu Hv Huv; rewrite Hfran; exact Hu]. }
  assert (HsecCw_g : rSection ran(g) E (C ~ ω)).
  { unfold rSection. split.
    - rewrite Hgran. apply MKT26a.
    - split; [exact HwoCw | intros u v Hu Hv Huv; rewrite Hgran; exact Hu]. }
  assert (Hdomeq : dom(f) = dom(g)) by congruence.
  destruct (MKT97 (f:=f) (g:=g) (r:=E) (s:=E) (x:=R) (y:=C ~ ω)
    Hfpr0 Hgpr0 HsecR_f HsecR_g HsecCw_f HsecCw_g) as [Hfgsub | Hgfsub].
  - apply (proj2 (MKT71 f g Hff Hfg)).
    intros x.
    destruct (classic (x ∈ dom(f))) as [Hx | Hnx].
    + assert (Hxf : [x, f[x]] ∈ f) by (apply (MKT_dom_val f x Hff Hx)).
      assert (Hxg : [x, f[x]] ∈ g) by (apply Hfgsub; exact Hxf).
      symmetry. apply (MKT_fval g x (f[x]) Hfg Hxg).
    + assert (Hnxg : x ∉ dom(g)).
      { intro Hxg. apply Hnx. rewrite <- Hdomeq in Hxg. exact Hxg. }
      rewrite (MKT69a (x:=x) (f:=f) Hnx).
      rewrite (MKT69a (x:=x) (f:=g) Hnxg).
      reflexivity.
  - apply (proj2 (MKT71 f g Hff Hfg)).
    intros x.
    destruct (classic (x ∈ dom(g))) as [Hx | Hnx].
    + assert (Hxg : [x, g[x]] ∈ g) by (apply (MKT_dom_val g x Hfg Hx)).
      assert (Hxf : [x, g[x]] ∈ f) by (apply Hgfsub; exact Hxg).
      apply (MKT_fval f x (g[x]) Hff Hxf).
    + assert (Hnxf : x ∉ dom(f)).
      { intro Hxf. apply Hnx. rewrite Hdomeq in Hxf. exact Hxf. }
      rewrite (MKT69a (x:=x) (f:=f) Hnxf).
      rewrite (MKT69a (x:=x) (f:=g) Hnx).
      reflexivity.
Qed.