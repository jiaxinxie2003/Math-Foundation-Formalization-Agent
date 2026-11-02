# Math Foundation Formalization Agent

## 1. Overview

The **Math Foundation Formalization Agent (MFF-Agent)** is an LLM-based intelligent agent designed to automate the formalization of mathematical foundations using the **Rocq Prover** (formerly Coq).

Unlike general-purpose theorem-proving agents that primarily focus on isolated mathematical problems, this project emphasizes the formalization of foundational mathematical theories, including axiomatic set theory, real numbers, mathematical logic, and fundamental equivalences in mathematics.

The agent integrates Large Language Models (LLMs) with the Rocq proof assistant to generate proof scripts, interact with the proof environment, and iteratively resolve compilation errors. A finite-state machine (FSM) is employed to manage the execution process and track task progress.

By combining LLM-based proof generation with machine-checked verification, this project aims to improve the reliability and automation of mathematical foundations formalization.

## 2. Formalization Results

The project currently covers the following areas of mathematical foundations:

| Mathematical Area | Formalization Content |
|---|---|
| Axiomatic Set Theory | Morse–Kelley (MK) axiomatic set theory |
| Real Numbers | Axiomatic formalization of real numbers and related properties |
| Axiom of Choice | Equivalent formulations of the axiom of choice |
| Mathematical Logic | Propositional logic and related formal results |

## 3. Project Structure

```text
Math-Foundation-Formalization-Agent/
│
├── Code/
│   │
│   ├── Axiom_of_Choice/
│   │   ├── Basic_Definitions.v
│   │   ├── MK.v
│   │   ├── Maximal_Principle.v
│   │   ├── Tukey.v
│   │   ├── Wellordering.v
│   │   └── Zermelo.v
│   │
│   ├── Logic/
│   │   └── L_system_Logic.v
│   │
│   ├── MK/
│   │   └── MK.v
│   │
│   └── R_Axiom/
│       ├── MK.v
│       ├── Real_Axioms1.v
│       └── Real_Axioms_Isomorphism.v
│
├── MFF-Agent.py
│
└── README.md
```

### Directory Description

- **`MFF-Agent.py`**: The main implementation of the Math Foundation Formalization Agent, integrating LLM-based reasoning with Rocq proof checking.
- **`Code/Axiom_of_Choice/`**: Contains formalizations of equivalent formulations of the axiom of choice, including the maximal principle, Tukey's lemma, the well-ordering principle, and Zermelo's theorem.
- **`Code/Logic/`**: Contains formalization files related to propositional logic and logical systems.
- **`Code/MK/`**: Contains the formalization of Morse–Kelley (MK) axiomatic set theory.
- **`Code/R_Axiom/`**: Contains formalization files related to the axiomatic construction of real numbers and related mathematical structures.
