# Math-Foundation-Formalization-Agent

An LLM-based intelligent agent for the automated formalization of mathematical foundations using the Rocq Prover (formerly Coq).

1. Overview

The Math Foundation Formalization Agent (MFF-Agent) is an intelligent agent designed to assist in the formalization and verification of mathematical foundations within the Rocq proof assistant.

Unlike general-purpose theorem-proving agents that focus primarily on isolated mathematical problems, this project emphasizes the formalization of foundational mathematical theories, including axiomatic set theory, real number systems, logical systems, and fundamental equivalences in mathematical logic.

The agent integrates a Large Language Model (LLM) with the Rocq proof assistant to generate proof scripts, interact with the proof environment, and iteratively resolve compilation errors. A finite-state machine (FSM) is employed to manage the execution process and track task progress.

The system aims to improve the reliability of automated formalization by combining LLM-based proof generation with machine-checked verification.

2. Main Features

Mathematical Foundations Formalization: Supports formalization tasks involving axiomatic set theory, real numbers, mathematical logic, and related foundational theories.

Automated Proof Generation: Uses an LLM to generate Rocq definitions, theorem statements, and proof scripts.

Iterative Proof Refinement: Analyzes compilation errors and proof states to guide subsequent proof-generation attempts.

Rocq-Based Verification: Uses the Rocq compiler to check generated formalizations.

Finite-State Task Management: Employs a finite-state machine to manage execution states and distinguish successful compilation from failed attempts.

Task Completion Verification: Evaluates task completion based on machine-verified results and the completion of the specified target theorems, rather than relying solely on the LLM's self-reported status.

3. Formalization Results

The project currently covers the following areas of mathematical foundations:

Mathematical Area

Formalization Content

Axiomatic Set Theory

Morse–Kelley (MK) axiomatic set theory

Real Numbers

Axiomatic formalization of real numbers and related properties

Axiom of Choice

Formalization of equivalent formulations of the axiom of choice

Mathematical Logic

Propositional logic and related formal results

These formalization files are organized under the Code/ directory.

4. Project Structure

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
