(**********************************************************************)
(*  This is part of Base_ML, it is distributed under the terms of the *)
(*          GNU Lesser General Public License version 3               *)
(*             (see file LICENSE for more details)                    *)
(*                                                                    *)
(*                     Copyright 2026-2031                            *)
(*    Dakai Guo, qiming Wang, Xiang Ji, Tingting Ji and Wensheng      *)
(**********************************************************************)

(** Base_ML *)

Require Export Coq.Sets.Ensembles.
Require Import Coq.Logic.Epsilon.
Require Import Coq.micromega.Lia.
Require Import Coq.Logic.Classical.
Require Import Coq.Sets.Finite_sets.
Require Import Coq.Sets.Finite_sets_facts.

Notation "a ∈ A" := (In _ A a) (at level 10).
Notation "B ∪ C" := (Union _ B C) (at level 65, left associativity).
Notation "[ a ]" := (Singleton _ a) (at level 0, right associativity).
Notation "A ⊆ B" := (Included _ A B) (at level 70).

Corollary UnionI : forall {U} (a: U) B C, a ∈ (B ∪ C) <-> a ∈ B \/ a ∈ C.
Proof. split; intros; destruct H; eauto with sets. Qed.

Corollary Single : forall {U} (a x: U), a ∈ [ x ] <-> a = x.
Proof. split; intros. destruct H; auto. rewrite H. split. Qed.


(** formulas_L_System *)

Inductive Formula : Type:=
  | X : nat -> Formula
  | Not : Formula -> Formula
  | Contain : Formula -> Formula -> Formula.

Notation "¬ q" := (Not q)(at level 5,right associativity).
Notation "p → q" := (Contain p q)(at level 8,right associativity).

Definition Φ := @ Empty_set Formula.


(** syntax_L_System *)

Section Propositional_calculus.

Variable Γ : Ensemble Formula.
Inductive deduce_L : Formula -> Prop :=
  | L0 : forall p, p ∈ Γ -> deduce_L p 
  | L1 : forall p q, deduce_L (p → (q → p))
  | L2 : forall p q r, deduce_L ((p → (q → r)) → ((p → q) → (p → r)))
  | L3 : forall p q, deduce_L ((¬p → ¬q)→ (q → p))
  | MP : forall p q, deduce_L (p → q) -> deduce_L p -> deduce_L q.

End Propositional_calculus.

Notation " Γ ├ p " := (deduce_L Γ p)(at level 80).
Global Hint Constructors deduce_L : LD.

Fact Union_l : forall Γ p, Γ ├ p -> forall A, Γ ∪ A ├ p.
Proof. intros. induction H; eauto with LD sets. Qed.

Fact Union_r : forall Γ p , Γ ├ p -> forall A, A ∪ Γ ├ p.
Proof. intros. induction H; eauto with LD sets. Qed.

(* 命题1 同一律 |- p→q *)
Lemma law_identity : forall Γ p, Γ ├ p → p.
Proof.
  intros. eapply MP with (p := p → (p → p)).
  - eapply MP with (p := p → ((p → p) → p)).
    + apply L2.
    + apply L1.
  - apply L1.
Qed.

Fact ded_weaken : forall Γ p q, Γ ├ q -> Γ ├ p → q.
Proof. intros. eapply MP with (p := q). apply L1. assumption. Qed.

Fact ded_2 : forall Γ p q r, Γ ├ p → (q → r) -> Γ ├ p → q -> Γ ├ p → r.
Proof.
  intros. eapply MP with (p := p → q).
  - eapply MP with (p := p → (q → r)).
    + apply L2.
    + assumption.
  - assumption.
Qed.

Fact ded_syl : forall Γ p q r, Γ ├ p → q -> Γ ├ q → r -> Γ ├ p → r.
Proof. intros. eapply ded_2 with (q := q). apply ded_weaken. assumption. assumption. Qed.

(* 命题2 否定前件律 *)
Lemma law_deny_antecedent : forall Γ p q, Γ ├ ¬q → (q → p).
Proof. intros. eapply ded_syl with (q := ¬p → ¬q). apply L1. apply L3. Qed.

Definition Contradiciton Γ := exists q, Γ ├ q /\ Γ ├ ¬q.

Definition No_Contradiciton Γ := forall q, ~ (Γ ├ q /\ Γ ├ ¬q).

Proposition prop_2_3 : forall Γ, Contradiciton Γ ->  forall p, Γ ├ p.
Proof.
  intros Γ [q [Hq Hnq]] p.
  eapply MP with (p := q).
  - eapply MP with (p := ¬q).
    + apply law_deny_antecedent.
    + exact Hnq.
  - exact Hq.
Qed.

(* 演绎定理 p ├ q  <=>  p → q *)
Theorem Deductive_Theorem : forall Γ p q, Γ∪[p] ├ q <-> Γ ├ p → q.
Proof.
  intros Γ p q. split.
  - intros H. induction H as [a Hmem | a b | a b c | a b | a b h1 ih1 h2 ih2].
    + apply UnionI in Hmem. destruct Hmem as [Hmem | Hmem].
      * apply ded_weaken. apply L0. exact Hmem.
      * apply Single in Hmem. subst. apply law_identity.
    + apply ded_weaken. apply L1.
    + apply ded_weaken. apply L2.
    + apply ded_weaken. apply L3.
    + exact (ded_2 _ _ _ _ ih1 ih2).
  - intros H. eapply MP with (p := p).
    + apply Union_l. exact H.
    + apply L0. eauto with sets.
Qed.

Fact DT_intro : forall Γ p q, Γ∪[p] ├ q -> Γ ├ p → q.
Proof. intros. apply (proj1 (Deductive_Theorem Γ p q)). assumption. Qed.

Fact DT_elim : forall Γ p q, Γ ├ p → q -> Γ∪[p] ├ q.
Proof. intros. apply (proj2 (Deductive_Theorem Γ p q)). assumption. Qed.

Corollary syllogism : forall Γ p q r , Γ ∪ [p] ├ q -> Γ ∪ [r] ├ p -> Γ ∪ [r] ├ q.
Proof.
  intros. apply MP with (p := p).
  - apply Union_l. apply DT_intro. assumption.
  - assumption.
Qed.

Fact ded_swap : forall Γ p q r, Γ ├ p → (q → r) -> Γ ├ q → (p → r).
Proof.
  intros Γ p q r H. apply DT_intro. apply DT_intro.
  eapply MP with (p := q).
  - eapply MP with (p := p).
    + apply Union_l. apply Union_l. exact H.
    + apply L0. eauto with sets.
  - apply L0. eauto with sets.
Qed.

(* 命题1 否定肯定律 (¬p→p)→p *)
Proposition law_negetion_affirmation : forall Γ p, Γ ├ (¬p → p) → p.
Proof.
  intros Γ p. apply Deductive_Theorem.
  assert (h : (Γ ∪ [¬p → p]) ├ (¬p → p)) by (apply L0; eauto with sets).
  eapply MP with (p := ¬p → p).
  - eapply MP with (p := ¬p → ¬(¬p → p)).
    + apply L3.
    + eapply MP with (p := ¬p → p).
      * eapply MP with (p := ¬p → (p → ¬(¬p → p))).
        -- apply L2.
        -- apply law_deny_antecedent.
      * exact h.
  - exact h.
Qed.

(* ---- 辅助导出规则 ---- *)

Fact rule_Indirect_h : forall Γ p q, Γ∪[¬p] ├ q -> Γ∪[¬p] ├ ¬q -> Γ ├ p.
Proof.
  intros Γ p q Hq Hnq.
  eapply MP with (p := ¬p → p).
  - apply law_negetion_affirmation.
  - apply DT_intro.
    eapply MP with (p := q).
    + eapply MP with (p := ¬p → ¬q). apply L3. apply ded_weaken. exact Hnq.
    + eapply MP with (p := ¬p). apply ded_weaken. exact Hq. apply L0. eauto with sets.
Qed.

Fact dn_h : forall Γ p, Γ ├ ¬¬p → p.
Proof.
  intros Γ p. apply Deductive_Theorem.
  eapply rule_Indirect_h with (q := ¬p).
  - apply L0. eauto with sets.
  - apply L0. eauto with sets.
Qed.

Fact ra_h : forall Γ p q, Γ∪[p] ├ q -> Γ∪[p] ├ ¬q -> Γ ├ ¬p.
Proof.
  intros Γ p q Hq Hnq.
  eapply rule_Indirect_h with (q := q).
  - eapply MP with (p := p).
    + apply Union_l. apply Deductive_Theorem. exact Hq.
    + eapply MP with (p := ¬¬p).
      * apply Union_l. apply dn_h.
      * apply L0. eauto with sets.
  - eapply MP with (p := p).
    + apply Union_l. apply Deductive_Theorem. exact Hnq.
    + eapply MP with (p := ¬¬p).
      * apply Union_l. apply dn_h.
      * apply L0. eauto with sets.
Qed.

Fact dn2_h : forall Γ p, Γ ├ p → ¬¬p.
Proof.
  intros Γ p. apply Deductive_Theorem.
  eapply ra_h with (q := p).
  - apply L0. eauto with sets.
  - apply L0. eauto with sets.
Qed.

Fact gen_el : forall Γ p q, Γ ├ ¬(p → q) -> Γ ├ p.
Proof.
  intros Γ p q H.
  eapply rule_Indirect_h with (q := p → q).
  - eapply MP with (p := ¬p). apply law_deny_antecedent. apply L0. eauto with sets.
  - apply Union_l. exact H.
Qed.

Fact gen_er : forall Γ p q, Γ ├ ¬(p → q) -> Γ ├ ¬q.
Proof.
  intros Γ p q H.
  eapply ra_h with (q := p → q).
  - apply ded_weaken. apply L0. eauto with sets.
  - apply Union_l. exact H.
Qed.

(* 换位律 *)
Fact law_inverse_prop : forall Γ p q, Γ ├ (q → p) → (¬p → ¬q).
Proof.
  intros. apply DT_intro. apply DT_intro.
  eapply MP with (p := ¬p).
  - eapply MP with (p := ¬¬q → ¬¬p).
    + apply L3.
    + apply DT_intro.
      eapply MP with (p := p).
      * apply dn2_h.
      * eapply MP with (p := q).
        -- apply L0. eauto with sets.
        -- eapply MP with (p := ¬¬q).
          ++ apply dn_h.
          ++ apply L0. eauto with sets.
  - apply L0. eauto with sets.
Qed.

(*Peirce律*)
Fact law_peirce : forall Γ p q , Γ ├ ((p → q) → p) → p.
Proof.
  intros. apply DT_intro.
  eapply MP with (p := ¬p → p).
  - apply law_negetion_affirmation.
  - apply DT_intro.
    eapply MP with (p := p → q).
    + apply L0. eauto with sets.
    + eapply MP with (p := ¬p).
      * apply law_deny_antecedent.
      * apply L0. eauto with sets.
Qed.

(* 反证律与归谬律 *)
(* 反证律 law of indirect proof *)
Theorem rule_Indirect : forall Γ p q, Γ∪[¬p] ├ q -> Γ∪[¬p] ├ ¬q -> Γ ├ p.
Proof. intros Γ p q H1 H2. exact (rule_Indirect_h Γ p q H1 H2). Qed.

(* 反证律推论 双重否定律 *)
Corollary law_double_negation_aux : forall p, [¬¬p] ├ p.
Proof.
  intros. eapply MP with (p := ¬¬p).
  - apply dn_h.
  - apply L0. eauto with sets.
Qed.

Corollary law_double_negation : forall  Γ p, Γ ├ ¬¬p → p.
Proof. intros. apply dn_h. Qed.

(* 定理2 归谬律 law of reduction to absurdity *)
Theorem rule_Reduction_absurdity :
  forall Γ p q, Γ∪[p] ├ q -> Γ∪[p] ├ ¬q -> Γ ├ ¬p.
Proof. intros Γ p q H1 H2. exact (ra_h Γ p q H1 H2). Qed.

(* 第二双重否定律 *)
Corollary law_double_negation_second_aux : forall  p, [p] ├ ¬¬p.
Proof.
  intros. eapply MP with (p := p).
  - apply dn2_h.
  - apply L0. eauto with sets.
Qed.

Corollary law_double_negation_second : forall Γ p , Γ ├ p → ¬¬p.
Proof. intros. apply dn2_h. Qed.

(* 析取 *)
Notation " p ∨ q " := (¬p → q)(at level 7, right associativity).
Notation " p ∧ q " := (¬(p → ¬q))(at level 6, right associativity).
Notation " p ↔ q " := ((p → q)∧(q → p))
  (at level 9, right associativity).

Proposition prop_2_5_1 : forall p q Γ, Γ ├ p → (p ∨ q).
Proof. intros. apply ded_swap. apply law_deny_antecedent. Qed.

Proposition prop_2_5_2 : forall p q Γ, Γ ├ q → (p ∨ q).
Proof. intros. apply L1. Qed.

Proposition prop_2_5_3 : forall p q Γ, Γ ├ (p ∨ q) → (q ∨ p).
Proof.
  intros. apply DT_intro. apply DT_intro.
  eapply rule_Indirect_h with (q := q).
  - eapply MP with (p := ¬p).
    + apply L0. eauto with sets.
    + apply L0. eauto with sets.
  - apply L0. eauto with sets.
Qed.

Proposition prop_2_5_4 : forall p Γ, Γ ├ (p ∨ p) → p.
Proof. intros. apply law_negetion_affirmation. Qed.

Proposition prop_2_5_5 : forall p q r Γ, 
  Γ ├ (q → r) → ((p ∨ q) → (p ∨ r)).
Proof.
  intros. apply DT_intro. apply DT_intro. apply DT_intro.
  eapply MP with (p := q).
  - apply L0. eauto with sets.
  - eapply MP with (p := ¬p).
    + apply L0. eauto with sets.
    + apply L0. eauto with sets.
Qed.

Proposition prop_2_5_6 : forall p Γ, Γ ├ ¬p ∨ p.
Proof. intros. apply dn_h. Qed.

Proposition prop_2_6_1 : forall p q Γ, Γ ├ (p ∧ q) → p.
Proof.
  intros. apply Deductive_Theorem.
  eapply rule_Indirect_h with (q := p → ¬q).
  - eapply MP with (p := ¬p).
    + apply law_deny_antecedent.
    + apply L0. eauto with sets.
  - apply L0. eauto with sets.
Qed.

Proposition prop_2_6_2 : forall p q Γ, Γ ├ (p ∧ q) → q.
Proof.
  intros. apply Deductive_Theorem.
  eapply rule_Indirect_h with (q := p → ¬q).
  - apply ded_weaken. apply L0. eauto with sets.
  - apply L0. eauto with sets.
Qed.

Fact and_el : forall Γ p q, Γ ├ (p ∧ q) -> Γ ├ p.
Proof. intros. eapply MP with (p := p ∧ q). apply prop_2_6_1. assumption. Qed.

Fact and_er : forall Γ p q, Γ ├ (p ∧ q) -> Γ ├ q.
Proof. intros. eapply MP with (p := p ∧ q). apply prop_2_6_2. assumption. Qed.

Proposition prop_2_6_3 : forall p q Γ, Γ ├ (p ∧ q) → (q ∧ p).
Proof.
  intros. apply Deductive_Theorem.
  eapply ra_h with (q := p).
  - eapply MP with (p := ¬(p → ¬q)).
    + apply prop_2_6_1.
    + apply L0. eauto with sets.
  - eapply MP with (p := q).
    + apply L0. eauto with sets.
    + eapply MP with (p := ¬(p → ¬q)).
      * apply prop_2_6_2.
      * apply L0. eauto with sets.
Qed.

Proposition prop_2_6_4 : forall p Γ, Γ ├ p → (p ∧ p).
Proof.
  intros. apply Deductive_Theorem.
  eapply ra_h with (q := p).
  - apply L0. eauto with sets.
  - eapply MP with (p := p).
    + apply L0. eauto with sets.
    + apply L0. eauto with sets.
Qed.

Proposition prop_2_6_5 : forall p q Γ, Γ ├ p → (q → (p ∧ q)).
Proof.
  intros. apply DT_intro. apply DT_intro.
  eapply ra_h with (q := q).
  - apply L0. eauto with sets.
  - eapply MP with (p := p).
    + apply L0. eauto with sets.
    + apply L0. eauto with sets.
Qed.

Fact and_i : forall Γ p q, Γ ├ p -> Γ ├ q -> Γ ├ (p ∧ q).
Proof.
  intros. eapply MP with (p := q).
  - eapply MP with (p := p). apply prop_2_6_5. assumption.
  - assumption.
Qed.

Proposition prop_2_6_6 : forall p Γ, Γ ├ ¬(p ∧ ¬p).
Proof.
  intros. eapply MP with (p := p → ¬¬p).
  - apply dn2_h.
  - apply dn2_h.
Qed.

Proposition prop_2_7_1 : forall p q Γ, Γ ├ (p ↔ q) → (p → q).
Proof. intros. apply prop_2_6_1. Qed.

Proposition prop_2_7_2 : forall p q Γ, Γ ├ (p ↔ q) → (q → p).
Proof. intros. apply prop_2_6_2. Qed.

Proposition prop_2_7_3 : forall p q Γ, Γ ├ (p ↔ q) ↔ (q ↔ p).
Proof.
  intros. apply and_i.
  - apply prop_2_6_3.
  - apply prop_2_6_3.
Qed.

Fact E511: forall Γ p q, Γ ├ (p → ¬q) → (q → ¬p).
Proof.
  intros. apply DT_intro. apply DT_intro.
  eapply MP with (p := q).
  - eapply MP with (p := ¬¬p → ¬q).
    + apply L3.
    + apply DT_intro.
      eapply MP with (p := p).
      * apply L0. eauto with sets.
      * eapply MP with (p := ¬¬p).
        -- apply dn_h.
        -- apply L0. eauto with sets.
  - apply L0. eauto with sets.
Qed.

Proposition prop_2_7_4 : forall p q Γ, Γ ├ (p ↔ q) ↔ (¬p ↔ ¬q).
Proof.
  intros. apply and_i.
  - apply Deductive_Theorem. apply and_i.
    + eapply MP with (p := q → p). apply law_inverse_prop. apply and_er with (p := p → q). apply L0. eauto with sets.
    + eapply MP with (p := p → q). apply law_inverse_prop. apply and_el with (q := q → p). apply L0. eauto with sets.
  - apply Deductive_Theorem. apply and_i.
    + eapply MP with (p := ¬q → ¬p). apply L3. apply and_er with (p := ¬p → ¬q). apply L0. eauto with sets.
    + eapply MP with (p := ¬p → ¬q). apply L3. apply and_el with (q := ¬q → ¬p). apply L0. eauto with sets.
Qed.

Proposition prop_2_7_5 : forall p q Γ,
  Γ ├ (p → q) → ((q → p) → (p ↔ q)).
Proof. intros. apply prop_2_6_5. Qed.

Proposition DeMorgan: forall p q Γ, Γ ├ ¬(p ∧ q) ↔ (¬p ∨ ¬q).
Proof.
  intros. apply and_i.
  - apply DT_intro. apply DT_intro.
    eapply MP with (p := p).
    + eapply MP with (p := ¬¬(p → ¬q)). apply dn_h. apply L0. eauto with sets.
    + eapply MP with (p := ¬¬p). apply dn_h. apply L0. eauto with sets.
  - apply DT_intro.
    eapply MP with (p := p → ¬q).
    + apply dn2_h.
    + eapply ded_syl. apply dn2_h. apply L0. eauto with sets.
Qed.

Proposition DeMorgan': forall p q Γ, Γ ├ ¬(p ∨ q) ↔ (¬p ∧ ¬q).
Proof.
  intros. apply and_i.
  - eapply MP with (p := (¬p → ¬¬q) → (¬p → q)).
    + apply law_inverse_prop.
    + apply DT_intro. apply DT_intro.
      eapply MP with (p := ¬¬q).
      * apply dn_h.
      * eapply MP with (p := ¬p). apply L0. eauto with sets. apply L0. eauto with sets.
  - eapply MP with (p := (¬p → q) → (¬p → ¬¬q)).
    + apply law_inverse_prop.
    + apply DT_intro. apply DT_intro.
      eapply MP with (p := q).
      * apply dn2_h.
      * eapply MP with (p := ¬p). apply L0. eauto with sets. apply L0. eauto with sets.
Qed.



(** semantic_L_System *)

Definition Not_bool p : bool :=
  match p with 
  | true => false
  | false => true
  end.

Definition Or_bool p q : bool :=
  match p, q with 
  | true, true => true
  | true, false => true
  | false, true => true
  | false, false => false
  end.

Definition And_bool p q : bool :=
  match p, q with 
  | true, true => true
  | true, false => false
  | false, true => false
  | false, false => false
  end.

Notation " ¬' p " := (Not_bool p)(at level 5).
Notation "p ∨' q" := (Or_bool p q)(at level 7).
Notation " p ∧' q " := (And_bool p q)(at level 6).

Definition Contain_bool p q : bool :=
  match p, q with 
  | true, true => true
  | true, false => false
  | false, true => true
  | false, false => true
  end.

Definition Equal_bool p q : bool :=
  match p, q with 
  | true, true => true
  | true, false => false
  | false, true => false
  | false, false => true
  end.

Notation "p →' q" := (Contain_bool p q) (at level 8, right associativity).
Notation " p ↔' q " := (Equal_bool p q) (at level 9, right associativity).

Goal forall v, ¬'(¬'v) = v.
Proof. intro v. destruct v; reflexivity. Qed.

Goal forall v, true →' v = v.
Proof. intro v. destruct v; reflexivity. Qed.

Goal forall v, v  →' true = true.
Proof. intro v. destruct v; reflexivity. Qed.

Goal forall v, v  →' false = ¬'v.
Proof. intro v. destruct v; reflexivity. Qed.

Goal forall v, false  →' v = true.
Proof. intro v. destruct v; reflexivity. Qed.

Goal forall v1 v2, v1 ∨' v2 = ¬'v1 →' v2.
Proof. intros v1 v2. destruct v1, v2; reflexivity. Qed.

Goal forall v1 v2, v1 ∧' v2 = ¬'(v1 →' (¬'v2)).
Proof. intros v1 v2. destruct v1, v2; reflexivity. Qed.

Goal forall v1 v2, v1 ↔' v2 = (v1 →' v2) ∧' (v2 →' v1).
Proof. intros v1 v2. destruct v1, v2; reflexivity. Qed.

Goal forall v1 v2, v1 →' v2 = ¬'(v1 ∧' ¬'v2).
Proof. intros v1 v2. destruct v1, v2; reflexivity. Qed.

Goal forall v1 v2, v1 →' v2 = ¬'v1 ∨' v2.
Proof. intros v1 v2. destruct v1, v2; reflexivity. Qed.


(* 定义1 赋值 *)
Definition keep_not v := (forall p, (v (¬p)) = ¬'(v p)).
Definition keep_contain v := (forall p q, (v (p → q)) = (v p) →' (v q)).
Definition value (v : Formula -> bool) := keep_not v /\ keep_contain v.


(* 赋值具有保运算性 *)
Proposition operation_preserved1 : forall v p q,
  value v -> v (p ∨ q) = (v p) ∨' (v q).
Proof.
  intros v p q [Hn Hc]. rewrite Hc. rewrite Hn.
  destruct (v p), (v q); reflexivity.
Qed.

Proposition operation_preserved2 : forall v p q,
  value v -> v (p ∧ q) = (v p) ∧' (v q).
Proof.
  intros v p q [Hn Hc]. rewrite Hn. rewrite Hc. rewrite Hn.
  destruct (v p), (v q); reflexivity.
Qed.

Proposition operation_preserved3 : forall v p q,
  value v -> v (p ↔ q) = (v p) ↔' (v q).
Proof.
  intros v p q [Hn Hc].
  rewrite Hn. rewrite Hc. rewrite Hc. rewrite Hn. rewrite Hc.
  destruct (v p), (v q); reflexivity.
Qed.

(* 永真式 若公式p的真值函数取常值1，
则p叫做命题演算L的永真式或重言式，记作╞ p *)
Definition Tautology p := forall v, value v -> v p = true.

Notation " ╞ p " := (Tautology p)(at level 80).

(* 三种公理模式是重言式 *)
Proposition prop2_10_1: forall p q: Formula, ╞ (p → (q → p)).
Proof.
  intros p q v [Hn Hc]. rewrite Hc. rewrite Hc.
  destruct (v p), (v q); reflexivity.
Qed.

Proposition prop2_10_2: forall p q r: Formula,
  ╞ ((p → (q → r)) → ((p → q) → (p → r))).
Proof.
  intros p q r v [Hn Hc].
  rewrite Hc. rewrite Hc. rewrite Hc. rewrite Hc. rewrite Hc. rewrite Hc.
  destruct (v p), (v q), (v r); reflexivity.
Qed.

Proposition prop2_10_3: forall p q: Formula, ╞ ((¬p → ¬q)→ (q → p)).
Proof.
  intros p q v [Hn Hc].
  rewrite Hc. rewrite Hc. rewrite Hn. rewrite Hn. rewrite Hc.
  destruct (v p), (v q); reflexivity.
Qed.

Definition Contradict p := Tautology (¬p).

Definition Satisfiable p := ~ (Contradict p).

(* 语义推论 *)
Definition Semantic_inference (Γ:Ensemble Formula) p := 
  forall v, value v -> (forall q, q ∈ Γ -> v q = true) -> v p = true.

Notation " Γ ╞ p " := (Semantic_inference Γ p)(at level 80).


(* 空集的语义推论等价于重言式 *)
Corollary Semantic_inference_I : forall p, Φ ╞ p <-> ╞ p.
Proof.
  intros p. split.
  - intros H v Hv. apply H. assumption. intros q Hq. destruct Hq.
  - intros H v Hv _. apply H. assumption.
Qed.

Corollary Semantic_inference_II : forall Γ p, p ∈ Γ -> Γ ╞ p.
Proof.
  intros Γ p H v Hv HΓ. apply HΓ. assumption.
Qed.

Corollary Semantic_inference_III : forall p, ╞ p -> forall Γ, Γ ╞ p.
Proof.
  intros p H Γ v Hv _. apply H. assumption.
Qed.

Corollary Semantic_inference_IV : forall p q, Φ ∪ [p] ╞ q <-> [p] ╞ q.
Proof.
  intros p q. split.
  - intros H v Hv Hp. apply H. assumption.
    intros r Hr. apply UnionI in Hr. destruct Hr as [Hr | Hr].
    + destruct Hr.
    + apply Hp. assumption.
  - intros H v Hv Hmem. apply H. assumption.
    intros r Hr. apply Hmem. apply UnionI. right. assumption.
Qed.

Proposition semantic_deny_front : forall p q, [¬p] ╞ p → q.
Proof.
  intros p q v [Hn Hc] H.
  assert (Hnp : v (¬ p) = true) by (apply H; eauto with sets).
  rewrite Hn in Hnp.
  rewrite Hc.
  destruct (v p).
  - simpl in Hnp. discriminate Hnp.
  - destruct (v q); reflexivity.
Qed.

Proposition semantic_later : forall p q, [q] ╞ p → q.
Proof.
  intros p q v [Hn Hc] H.
  assert (Hq : v q = true) by (apply H; eauto with sets).
  rewrite Hc. rewrite Hq.
  destruct (v p); reflexivity.
Qed.

Proposition semantic_MP : forall Γ p q, Γ ╞ p -> Γ ╞ p → q -> Γ ╞ q.
Proof.
  intros Γ p q H1 H2 v Hv HΓ.
  destruct Hv as [Hn Hc].
  pose proof (H2 v (conj Hn Hc) HΓ) as Hpq.
  pose proof (H1 v (conj Hn Hc) HΓ) as Hp.
  rewrite Hc in Hpq.
  rewrite Hp in Hpq.
  destruct (v q); exact Hpq.
Qed.

(* 语义演绎定理 *)
Proposition semantic_deductive : forall Γ p q, Γ ∪[p] ╞ q <-> Γ ╞ p → q.
Proof.
  intros Γ p q. split.
  - intros H v Hv HΓ.
    destruct Hv as [Hn Hc].
    rewrite Hc.
    destruct (v p) eqn:Ep.
    + assert (Hq : v q = true).
      { apply H.
        - split; assumption.
        - intros r Hr. apply UnionI in Hr. destruct Hr as [Hr | Hr].
          + apply HΓ; assumption.
          + apply Single in Hr. subst. exact Ep. }
      rewrite Hq. reflexivity.
    + destruct (v q); reflexivity.
  - intros H v Hv Hmem.
    destruct Hv as [Hn Hc].
    assert (Hpq : v (p → q) = true).
    { apply H.
      - split; assumption.
      - intros r Hr. apply Hmem. apply UnionI. left. assumption. }
    rewrite Hc in Hpq.
    assert (Hp : v p = true).
    { apply Hmem. apply UnionI. right. apply Single. reflexivity. }
    rewrite Hp in Hpq.
    destruct (v q); exact Hpq.
Qed.

(* 永真式的性质 *)
(*二永真式的合取还是永真式*)
Fact Tautology_and : forall p q ,  ╞ p ->  ╞ q ->  ╞ p ∧ q.
Proof.
  intros p q Hp Hq v Hv.
  destruct Hv as [Hn Hc].
  rewrite Hn. rewrite Hc. rewrite Hn.
  assert (vp : v p = true) by (apply Hp; split; assumption).
  assert (vq : v q = true) by (apply Hq; split; assumption).
  rewrite vp, vq. reflexivity.
Qed.

(*二永真式的析取还是永真式*)
Fact Tautology_or : forall p q ,  ╞ p ->  ╞ q ->  ╞ p ∨ q.
Proof.
  intros p q Hp Hq v Hv.
  destruct Hv as [Hn Hc].
  rewrite Hc. rewrite Hn.
  assert (vp : v p = true) by (apply Hp; split; assumption).
  rewrite vp. destruct (v q); reflexivity.
Qed.

(*后件是永真式的蕴含式还是永真式*)
Fact Tautology_latertrue : forall p q , ╞ q ->  ╞ p → q .
Proof.
  intros p q Hq v Hv.
  destruct Hv as [Hn Hc].
  rewrite Hc.
  assert (vq : v q = true) by (apply Hq; split; assumption).
  rewrite vq.
  destruct (v p); reflexivity.
Qed.

(*前件是永假式的蕴含式是永真式*)
Fact Tautology_frontfalse : forall p q , ╞ p ->  ╞ ¬p → q.
Proof.
  intros p q Hp v Hv.
  destruct Hv as [Hn Hc].
  rewrite Hc. rewrite Hn.
  assert (vp : v p = true) by (apply Hp; split; assumption).
  rewrite vp. destruct (v q); reflexivity.
Qed.


(** Mappings_ML *)

(* 单射函数 *) 
Definition function_injective {A B} (f: A -> B): Prop :=
  forall a1 a2, f a1 = f a2 -> a1 = a2.

(* 满射函数 *)
Definition function_surjective {A B} (f: A -> B): Prop := 
  forall b, exists a, f a = b.

(* 双射函数 *)
Inductive function_bijective {A B} (f: A -> B): Prop :=
  | fun_bij_intro : function_injective f -> function_surjective f 
                      -> function_bijective f.

(* 任意两个类型A、B的单射类型 *)
Record injection (A B: Type): Type := {
  inj_f:> A -> B;
  in_inj: function_injective inj_f }.

(* 满射类型 *)
Record surjection (A B: Type): Type := {
  sur_f:> A -> B;
  su_surj: function_surjective sur_f }.

(* 双射类型 *)
Record bijection (A B: Type): Type := {
  bij_f:> A -> B;
  in_bij: function_injective bij_f;
  su_bij: function_surjective bij_f }.

(* 若A单射B且B单射C, 则A单射C. *)
Definition injection_trans {A B C} (f1: injection A B) (f2: injection B C): 
  injection A C.
  apply (Build_injection _ _ (fun a => f2 (f1 a))). hnf; intros. 
  apply (in_inj _ _ f2) in H. apply (in_inj _ _ f1) in H. auto.
Defined.

(* 若A双射B, 则B双射A. *)
Definition bijection_sym {A B} (f: bijection A B): bijection B A.
  apply (Build_bijection _ _ (fun b => proj1_sig 
  (constructive_indefinite_description _ ((su_bij _ _ f) b)))).
  - hnf; intros. repeat destruct constructive_indefinite_description.
    simpl in H. congruence.
  - hnf; intros. exists (bij_f _ _ f b). 
    destruct constructive_indefinite_description.
    simpl. apply (in_bij _ _ f). auto.
Defined.

(* 若A1单射B1且A2单射B2, (A1+A2)单射(B1+B2). (此处+号代表和类型, 可理解为不相交的并) *)
Definition sum_injection {A1 B1 A2 B2} (f1: injection A1 B1) 
  (f2: injection A2 B2): injection (sum A1 A2) (sum B1 B2).
  apply (Build_injection _ _ (fun a =>
         match a with
         | inl x => inl (f1 x) 
         | inr y => inr (f2 y) end)).
  hnf; intros. destruct a1, a2; try inversion H.
  - inversion H. apply (in_inj _ _ f1) in H1. f_equal; auto.
  - inversion H. apply (in_inj _ _ _) in H1. f_equal; auto.
Defined.

(* 若A1单射B1且A2单射B2, 则(A1*A2)单射(B1*B2).(此处*号代表积类型, 可理解为笛卡尔积) *)
Definition prod_injection {A1 B1 A2 B2} (f1: injection A1 B1)
  (f2: injection A2 B2): injection (prod A1 A2) (prod B1 B2).
  apply (Build_injection _ _ (fun m =>
          match m with
          | (m1, m2) => (f1 m1, f2 m2) end )).
  hnf; intros. destruct a1, a2.
  inversion H. apply in_inj in H1. apply in_inj in H2. congruence.
Defined.

(* 若对任意I类型的项i, 都有A_i单射B, 那么(sigT A)单射(I*B).
(这个引理可理解为对于指标集I,若任意i∈I都存在一个A_i到B的单射, 
那么存在一个从⋃_(i=0)^∞ A_i 到I和B的笛卡尔积的单射) *)
Definition sigT_injection (I: Type) (A: I -> Type) (B: Type)
  (f: forall i: I, injection (A i) B): injection (sigT A) (I * B).
  apply (Build_injection _ _ (fun a => (projT1 a, f (projT1 a) (projT2 a)))).
  hnf; intros. inversion H. destruct a1,a2. simpl in *.
  subst. apply (in_inj _ _ (f x0)) in H2. congruence.
Defined.

(* A类型到B类型存在双射,那么可以构造A类型到B类型的单射. *)
Definition bijection_injection {A B} (f: bijection A B): injection A B :=
  Build_injection _ _ f (in_bij _ _ f).

(*  (nat+nat)双射nat.  *)
Definition nat2_nat_bijection: bijection (sum nat nat) nat.
  apply (Build_bijection _ _ (fun n =>
         match n with 
         | inl n => n + n 
         | inr n => S (n + n) end)).
  - hnf; intros. destruct a1 eqn:Ha1, a2 eqn:Ha2; try lia; f_equal; lia.
  - hnf; intros.
    assert (forall n, exists m, n= m + m \/ n = S (m + m)).
    { intros. induction n. eauto. destruct IHn. destruct H.
      - exists x; lia.
      - exists (S x); lia. }
    destruct (H b) as [n []].
    + exists (inl n). auto.
    + exists (inr n); auto.
Defined.

(* (nat*nat)双射nat. *)
Definition natnat_nat_bijection: bijection (prod nat nat) nat.
  set (fix sum (x : nat) : nat := match x with
       | 0 => 0
       | S x0 => S x0 + sum x0
       end) as f.
  apply (Build_bijection _ _
    (fun n => match n with | (n1, n2) => f (n1+n2) + n1 end)).
  - hnf; intros. destruct a1 as (a11, a12), a2 as (a21, a22).
    assert (forall m1 m2, m1 < m2 -> f m1 + m1 < f m2).
    { intros. remember (m2 - m1 - 1) as d;
      assert (m2 = (S d) + m1) by lia.
      subst m2. clear. induction d; simpl in *; lia. }
    destruct (Compare_dec.le_lt_dec (a11 + a12) (a21 + a22)).
    + destruct (Lt.le_lt_or_eq _ _ l).
      * pose proof H0 _ _ H1. lia.
      * rewrite H1 in *. assert (a11=a21) by lia. subst.
        assert (a12 = a22) by lia. auto.
    + apply H0 in l. lia.
  - hnf; intros. assert ( forall a, exists s, f s <= a < f (S s)).            
    { induction a. exists 0. auto. destruct IHa as [s Hs].
      remember (a - f s) as d.
      destruct (PeanoNat.Nat.lt_ge_cases d s).
      + exists s. simpl in *. lia.
      + exists (S s). simpl in *; lia. }
    destruct (H b) as [s Hs]. remember (b - (f s)) as a1.
    assert (a1 <= s) by (unfold f in *; lia).
    exists (a1, s-a1). replace (a1 + (s - a1)) with s by lia. lia.
Defined.

Definition Countable (A: Type): Type := injection A nat.

(* 若A单射B且B可数, 则A可数.  *)
Definition injection_Countable {A B} (R: injection A B)
  (CB: Countable B): Countable A := injection_trans R CB.

(* 若A双射B且B可数, 则A可数.  *)
Definition bijection_Countable {A B} (R: bijection A B) (CB: Countable B): 
  Countable A := injection_Countable (bijection_injection R) CB.

(* 若A可数且B可数, 则(A+B)可数. *)
Definition sum_Countable {A B} (CA: Countable A) (CB: Countable B): 
  Countable (sum A B) :=injection_trans
  (sum_injection CA CB) (bijection_injection nat2_nat_bijection).

(* 若A可数且B可数, 则(A*B)可数. *)
Definition prod_Countable {A B} (CA: Countable A) (CB: Countable B): 
  Countable (prod A B) :=injection_trans 
  (prod_injection CA CB) (bijection_injection natnat_nat_bijection).

(* (* 若对所有自然数i, 均有A_i可数, 则(sigT A可数). *) 
Definition nCountable_Countable {A: nat -> Type} 
  (CA: forall n, Countable (A n)): Countable (sigT A) :=
  injection_trans (sigT_injection _ _ _ CA)
  (bijection_injection natnat_nat_bijection). *)

(* 自然数可数 *)
Definition nat_Countable : Countable nat.
  apply (Build_injection _ _ (fun n => n )). hnf; intros. eauto.
Defined.

(* sigT A：依赖对类型，等价于存在量词∃i: I, A i表示“存在i使得A i成立”的所有(i, a)对 *)
Definition sigT_Countable {I: Type} {A: I -> Type}
  (CI: Countable I) (CA: forall i, Countable (A i)): Countable (sigT A).
  (* 1. 利用 sigT_injection 将 sigT A 映射到 (I * nat) *)
  (* 注意：CA i 的类型就是 Countable (A i)，即 injection (A i) nat *)
  apply (injection_trans (sigT_injection I A nat CA)).
  (* 2. 证明 (I * nat) 是可数的 *)
  apply prod_Countable. apply CI. apply nat_Countable.
Defined.



(** Bernstein_theorem_ML *)

Theorem classicT : forall (P: Prop), {P} + {~P}.
Proof.
  intro P.
  assert (Hex : exists (b : bool), (b = true <-> P)).
  { destruct (classic P) as [Hp | Hnp].
    - exists true. split; intros; [exact Hp | reflexivity].
    - exists false. split; intros.
      + discriminate H.
      + exfalso. apply Hnp. exact H. }
  destruct (constructive_indefinite_description _ Hex) as [b Hb].
  destruct b.
  - left. apply (proj1 Hb). reflexivity.
  - right. intro Hp. apply (proj2 Hb) in Hp. discriminate Hp.
Qed.

(* 像集 *)
Inductive image_set {A B : Type} (f : A -> B)  (X: Ensemble A) : Ensemble B :=
  image_intro : forall a, a ∈ X -> (f a) ∈ (image_set f X).

(* 反函数 *)
Definition function_rev {A B : Type} (f : A -> B) (g : B -> A) := 
  forall x, g (f x) = x.

(* 根据f构造反函数 *)
Definition fun_rev {A B : Type} (f : A -> B) (a: A) (y:B) : A :=
  match (classicT (exists x, f x = y)) with
  | left l => proj1_sig (constructive_indefinite_description _ l)
  | right _ => a
  end.

Section bernstein.

Context {A B : Type} (f : A -> B) (g : B -> A).
Hypothesis Inj_f : function_injective f.
Hypothesis Inj_g : function_injective g.
Hypothesis Inhabited_B : inhabited B.

(* 令C_0=A \g[B], C_(n+1)=g[f[C_n ]] *)
Fixpoint Cn n : Ensemble A :=
  match n with
  | O => Complement _ (image_set g (Full_set B))
  | S n' => image_set g (image_set f (Cn n'))
  end.

(* ω-并集 C = ∪_n C_n *)
Definition C : Ensemble A := fun a => exists n, a ∈ (Cn n).


(* 伯恩斯坦定理 *)
Theorem Bernstein_Theorem : bijection A B.
Proof.
  assert (HnotCg : forall a, ~ (a ∈ C) -> exists b, g b = a).
  { intros a Ha.
    assert (H0 : ~ (a ∈ (Cn 0))).
    { intro Hc. apply Ha. exists 0. exact Hc. }
    assert (Him : a ∈ (image_set g (Full_set B))).
    { apply NNPP. intro Hn. apply H0. exact Hn. }
    destruct Him as [b0 Hb0]. exists b0. reflexivity. }
  pose (h := fun a : A => match classicT (a ∈ C) with
    | left _ => f a
    | right Ha => proj1_sig (constructive_indefinite_description
                    (fun b => g b = a) (HnotCg a Ha))
    end).
  assert (h_in_C : forall a, a ∈ C -> h a = f a).
  { intros a Ha. unfold h. cbn beta. destruct (classicT (a ∈ C)) as [Hc|Hc].
    - reflexivity.
    - exfalso. apply Hc. exact Ha. }
  assert (h_not_C : forall a (Ha : ~ (a ∈ C)), g (h a) = a).
  { intros a Ha. unfold h. cbn beta. destruct (classicT (a ∈ C)) as [Hc|Hc].
    - exfalso. apply Ha. exact Hc.
    - exact (proj2_sig (constructive_indefinite_description
               (fun b => g b = a) (HnotCg a Hc))). }
  assert (Cn_in_C : forall n a, a ∈ (Cn n) -> a ∈ C).
  { intros n a H. exists n. exact H. }
  assert (Cn0 : forall a, a ∈ (Cn 0) <-> ~ (exists b, g b = a)).
  { intros a. change (~ (a ∈ (image_set g (Full_set B))) <-> ~ (exists b, g b = a)).
    split.
    - intros H [b Hb]. apply H. subst a. apply image_intro. constructor.
    - intros H Him. apply H. destruct Him as [b0 Hb0]. exists b0. reflexivity. }
  assert (CnSS : forall n a, a ∈ (Cn (S n)) <-> exists c, c ∈ (Cn n) /\ g (f c) = a).
  { intros n a.
    change (a ∈ (image_set g (image_set f (Cn n))) <-> exists c, c ∈ (Cn n) /\ g (f c) = a).
    split.
    - intros H. destruct H as [b0 Hb0]. destruct Hb0 as [c Hc].
      exists c. split; [exact Hc | reflexivity].
    - intros [c [Hc Hgfc]]. subst a. apply image_intro. apply image_intro. exact Hc. }
  assert (Hinj : function_injective h).
  { intros a1 a2 Heq.
    destruct (classicT (a1 ∈ C)) as [H1|H1];
    destruct (classicT (a2 ∈ C)) as [H2|H2].
    - apply Inj_f. rewrite <- (h_in_C a1 H1). rewrite Heq.
      rewrite (h_in_C a2 H2). reflexivity.
    - exfalso. apply H2.
      assert (Heq2 : a2 = g (f a1)).
      { rewrite <- (h_not_C a2 H2). rewrite <- Heq. rewrite (h_in_C a1 H1). reflexivity. }
      destruct H1 as [n Hn].
      exists (S n). apply (proj2 (CnSS n a2)). exists a1. split.
      + exact Hn.
      + symmetry. exact Heq2.
    - exfalso. apply H1.
      assert (Heq1 : a1 = g (f a2)).
      { rewrite <- (h_not_C a1 H1). rewrite Heq. rewrite (h_in_C a2 H2). reflexivity. }
      destruct H2 as [n Hn].
      exists (S n). apply (proj2 (CnSS n a1)). exists a2. split.
      + exact Hn.
      + symmetry. exact Heq1.
    - rewrite <- (h_not_C a1 H1). rewrite Heq. rewrite (h_not_C a2 H2). reflexivity. }
  assert (Hsurj : function_surjective h).
  { intro b.
    destruct (classicT ((g b) ∈ C)) as [Hb|Hb].
    - destruct Hb as [n Hn]. destruct n as [|n'].
      + exfalso. apply (proj1 (Cn0 (g b)) Hn). exists b. reflexivity.
      + apply (proj1 (CnSS n' (g b))) in Hn.
        destruct Hn as [c [Hc Hgfc]].
        exists c. rewrite (h_in_C c (Cn_in_C n' c Hc)).
        apply Inj_g. exact Hgfc.
    - exists (g b). apply Inj_g. rewrite (h_not_C (g b) Hb). reflexivity. }
  exact (Build_bijection A B h Hinj Hsurj).
Qed.

End bernstein.


(** bijection_nat_formula_L *)

(* 公式集可数 *)
(* 对于任意自然数n, 层数小于等于n的公式的全体是可数的. *)
Fixpoint rankF (p:Formula): nat :=
  match p with
  | X _ => 0
  | Not x => 1 + rankF x
  | Contain x y => 1 + rankF x + rankF y
  end.

(* 将公式单射到自然数 *)
Fixpoint enc (p : Formula) : nat :=
  match p with
  | X n => 3 * n
  | Not x => 3 * enc x + 1
  | Contain x y => 3 * (bij_f _ _ natnat_nat_bijection (enc x, enc y)) + 2
  end.

(* Formula是可数的. *)
Theorem Formula_contable : Countable Formula.
Proof.
  assert (Hinj : function_injective enc).
  { intros p q H. revert q H.
    induction p as [n | x IHx | x IHx y IHy]; intros q H;
    destruct q as [m | z | z w]; cbn [enc] in H; try (exfalso; lia).
    - f_equal. lia.
    - f_equal. apply IHx. lia.
    - assert (Hp : (enc x, enc y) = (enc z, enc w)).
      { apply (in_bij _ _ natnat_nat_bijection). lia. }
      injection Hp as Hx Hy.
      assert (Ex : x = z) by (apply IHx; exact Hx).
      assert (Ey : y = w) by (apply IHy; exact Hy).
      rewrite Ex, Ey. reflexivity. }
  exact (Build_injection Formula nat enc Hinj).
Qed.

(* 自然数和公式存在一一对应. *)
Corollary bijection_nat_formula : bijection nat Formula.
Proof.
  apply Bernstein_Theorem with (f := X) (g := inj_f _ _ Formula_contable).
  - intros a b H; congruence.
  - exact (in_inj _ _ Formula_contable).
Qed.


(** complete_L_System *)

(* 有矛盾公理集 无矛盾公理集 *)
(* Definition Contradiciton Γ := exists q, Γ ├ q /\ Γ ├ ¬q. *)
Definition consistence Γ := forall q, ~ (Γ ├ q /\ Γ ├ ¬q).

(* 一致集的性质 *)
Proposition redundancy_lemma : forall Γ p, Γ ∪ [¬p] ├ p -> Γ ├ p.
Proof.
  intros Γ p H.
  eapply MP with (p := ¬p → p).
  - apply law_negetion_affirmation.
  - apply DT_intro. exact H.
Qed.

(* 一致集的性质 *)
Proposition boom : forall Γ, ~ consistence Γ -> forall p, Γ ├ p.
Proof.
  intros Γ H p.
  apply prop_2_3.
  apply NNPP. intro Hc.
  apply H. intros q Hconj.
  apply Hc. exists q. exact Hconj.
Qed.

(* 一致集的性质 *)
Proposition No_contra : forall Γ, consistence Γ -> forall p, 
  consistence (Γ ∪ [p]) \/ consistence (Γ ∪ [¬p]).
Proof.
  intros Γ Hcons p.
  destruct (classic (consistence (Γ ∪ [p]))) as [Hc1 | Hc1].
  - left. exact Hc1.
  - right. intros q [Hq Hnq].
    assert (Hpp : Γ ∪ [¬p] ├ p).
    { apply boom. intros Hco. exact (Hco q (conj Hq Hnq)). }
    assert (Himp1 : Γ ├ ¬p → p) by (apply DT_intro; exact Hpp).
    assert (Hp : Γ ├ p)
      by (eapply MP with (p := ¬p → p);
          [apply law_negetion_affirmation | exact Himp1]).
    assert (Hpn : Γ ∪ [p] ├ ¬p) by (apply boom; exact Hc1).
    assert (Himp2 : Γ ├ p → ¬p) by (apply DT_intro; exact Hpn).
    assert (Hnp : Γ ├ ¬p) by (eapply MP; [exact Himp2 | exact Hp]).
    exact (Hcons p (conj Hp Hnp)).
Qed.

(* 极大一致集 *)
Definition maximal_consistent_set Γ := 
  consistence Γ /\ forall p, consistence (Γ ∪ [p]) -> p ∈ Γ.

(*可靠性定理*)
Theorem soundness_PC : forall Γ p, Γ ├ p -> Γ ╞ p.
Proof.
  intros Γ p H.
  induction H as [q Hq | q r | q r s | q r | q r H1 IH1 H2 IH2].
  - intros v Hv Hmem. apply Hmem. exact Hq.
  - intros v Hv _. exact (prop2_10_1 q r v Hv).
  - intros v Hv _. exact (prop2_10_2 q r s v Hv).
  - intros v Hv _. exact (prop2_10_3 q r v Hv).
  - eapply semantic_MP with (p := q). exact IH2. exact IH1.
Qed.

Fixpoint vtrue p :=
  match p with 
  | X _ => true
  | ¬ q => ¬' (vtrue q)
  | q → r => (vtrue q) →' (vtrue r)
  end.

Fixpoint vfalse p :=
  match p with 
  | X _ => false
  | ¬ q => ¬' (vfalse q)
  | q → r => (vfalse q) →' (vfalse r)
  end.

Corollary consistence_PC :  consistence Φ.
Proof.
  intros q [Hq Hnq].
  assert (Hv : value vtrue).
  { unfold value. split.
    - unfold keep_not. intros p. reflexivity.
    - unfold keep_contain. intros p r. reflexivity. }
  assert (Hq' : vtrue q = true).
  { apply (soundness_PC Φ q Hq). exact Hv. intros r Hr. destruct Hr. }
  assert (Hnq' : vtrue (¬q) = true).
  { apply (soundness_PC Φ (¬q) Hnq). exact Hv. intros r Hr. destruct Hr. }
  simpl in Hnq'.
  rewrite Hq' in Hnq'.
  simpl in Hnq'.
  discriminate Hnq'.
Qed.

(* Γ n *)
Fixpoint mapf Γ n (f: nat-> Formula) : Ensemble Formula := 
  match n with
  | O => Γ
  | S m => 
    match (classicT (consistence ((mapf Γ m f) ∪ [f m]))) with
    | left _ => mapf Γ m f ∪ [f m]
    | right _ => mapf Γ m f
    end
  end.

(* Γ n的一些性质 *)
Fact mapfIncluded_aux : forall Γ f m n, m <= n -> (mapf Γ m f) ⊆ (mapf Γ n f).
Proof.
  intros Γ f m n Hle.
  assert (Hstep : forall k, (mapf Γ k f) ⊆ (mapf Γ (S k) f)).
  { intro k. intros x Hx. cbn [mapf].
    destruct (classicT (consistence (mapf Γ k f ∪ [f k]))) as [Hc | Hc].
    - apply UnionI. left. exact Hx.
    - exact Hx. }
  induction Hle as [|n' Hle IH].
  - intros x Hx. exact Hx.
  - intros x Hx. apply Hstep. apply IH. exact Hx.
Qed.

Fact mapfIncluded : forall Γ f m n,
  (mapf Γ m f) ⊆ (mapf Γ n f) \/  (mapf Γ n f) ⊆ (mapf Γ m f).
Proof.
  intros Γ f m n.
  destruct (Compare_dec.le_lt_dec m n) as [H | H].
  - left. apply mapfIncluded_aux. exact H.
  - right. apply mapfIncluded_aux. lia.
Qed.

Fact subsetprove : forall A B p, A ⊆ B -> A ├ p -> B ├ p.
Proof.
  intros A B p Hsub H.
  induction H as [q Hq | q r | q r s | q r | q r H1 IH1 H2 IH2].
  - apply L0. apply Hsub. exact Hq.
  - apply L1.
  - apply L2.
  - apply L3.
  - apply MP with (p := q); [exact IH1 | exact IH2].
Qed.

Fact subsetNocontra : forall A B, A ⊆ B -> consistence B -> consistence A.
Proof.
  intros A B Hsub Hcons q [Hq Hnq].
  apply (Hcons q). split.
  - exact (subsetprove A B q Hsub Hq).
  - exact (subsetprove A B (¬q) Hsub Hnq).
Qed.

(* Γ* *)
Definition maxmapf Γ f : Ensemble Formula := fun p => exists n, p ∈ (mapf Γ n f).

(*  Γ* ├ p -> 存在足够大的n , Γ n ├ p *)
Lemma maxmapfI : forall Γ f p, (maxmapf Γ f) ├ p -> exists n, (mapf Γ n f) ├ p.
Proof.
  intros Γ f p H.
  induction H as [q Hq | q r | q r s | q r | q r H1 IH1 H2 IH2].
  - unfold maxmapf in Hq. destruct Hq as [n Hn]. exists n. apply L0. exact Hn.
  - exists 0. apply L1.
  - exists 0. apply L2.
  - exists 0. apply L3.
  - destruct IH1 as [n1 Hn1]. destruct IH2 as [n2 Hn2].
    exists (Nat.max n1 n2).
    apply MP with (p := q).
    + apply subsetprove with (A := mapf Γ n1 f).
      apply mapfIncluded_aux. lia. exact Hn1.
    + apply subsetprove with (A := mapf Γ n2 f).
      apply mapfIncluded_aux. lia. exact Hn2.
Qed.

(* v赋值 *)
Definition valuemaxf Γ (p: Formula) : bool := 
  match (classicT (p ∈ Γ)) with
  | left _ => true
  | right _ => false
  end.

(* L的完全性 *) 
Theorem complete : forall Γ p, Γ ╞ p -> Γ ├ p.
Proof.
  intros Γ p Hsem.
  destruct (classic (consistence Γ)) as [Hcons | Hncons].
  - destruct (classic (Γ ├ p)) as [Hp | Hp].
    + exact Hp.
    + exfalso.
      pose (Γ0 := Γ ∪ [¬p]).
      assert (Hcons0 : consistence Γ0).
      { intros q [Hq Hnq]. apply Hp. eapply rule_Indirect; [exact Hq | exact Hnq]. }
      pose (f := bij_f _ _ bijection_nat_formula).
      pose (G := maxmapf Γ0 f).
      assert (HGsub : Γ0 ⊆ G).
      { intros q Hq. unfold G, maxmapf. exists 0. exact Hq. }
      assert (Hmapf_cons : forall n, consistence (mapf Γ0 n f)).
      { induction n as [|n IH].
        - change (consistence Γ0). exact Hcons0.
        - change (consistence (match classicT (consistence (mapf Γ0 n f ∪ [f n])) with
             | left _ => mapf Γ0 n f ∪ [f n] | right _ => mapf Γ0 n f end)).
          destruct (classicT (consistence (mapf Γ0 n f ∪ [f n]))) as [Hc | Hnc].
          + exact Hc.
          + exact IH. }
      assert (HGcons : consistence G).
      { intros q [Hq Hnq].
        destruct (maxmapfI Γ0 f q Hq) as [n1 Hn1].
        destruct (maxmapfI Γ0 f (¬q) Hnq) as [n2 Hn2].
        pose proof (Hmapf_cons (Nat.max n1 n2)) as Hc.
        apply (Hc q). split.
        - apply subsetprove with (A := mapf Γ0 n1 f).
          apply mapfIncluded_aux. lia. exact Hn1.
        - apply subsetprove with (A := mapf Γ0 n2 f).
          apply mapfIncluded_aux. lia. exact Hn2. }
      assert (HGmax : forall q, consistence (G ∪ [q]) -> q ∈ G).
      { intros q Hqcons.
        destruct (su_bij _ _ bijection_nat_formula q) as [n0 Hn0].
        destruct (classicT (consistence (mapf Γ0 n0 f ∪ [f n0]))) as [Hc | Hnc] eqn:Ed.
        - unfold G, maxmapf. exists (S n0). rewrite <- Hn0. cbn [mapf]. rewrite Ed.
          apply UnionI. right. apply Single. reflexivity.
        - exfalso. apply Hnc.
          apply (subsetNocontra (mapf Γ0 n0 f ∪ [f n0]) (G ∪ [q])).
          + intros x Hx. apply UnionI in Hx. destruct Hx as [Hx | Hx].
            * apply UnionI. left. unfold G, maxmapf. exists n0. exact Hx.
            * apply Single in Hx. subst x. apply UnionI. right. apply Single. exact Hn0.
          + exact Hqcons. }
      assert (HG_prove : forall q, G ├ q -> q ∈ G).
      { intros q Hq. apply HGmax. intros r [Hr Hnr].
        apply (HGcons q). split.
        - exact Hq.
        - eapply rule_Reduction_absurdity; [exact Hr | exact Hnr]. }
      pose (v := valuemaxf G).
      assert (HvT : forall q, q ∈ G -> v q = true).
      { intros q Hq. unfold v, valuemaxf. destruct (classicT (q ∈ G)) as [Hc | Hc];
          [reflexivity | exfalso; apply Hc; exact Hq]. }
      assert (HvF : forall q, ~ (q ∈ G) -> v q = false).
      { intros q Hq. unfold v, valuemaxf. destruct (classicT (q ∈ G)) as [Hc | Hc];
          [exfalso; apply Hq; exact Hc | reflexivity]. }
      assert (HnotG : forall q, ~ (q ∈ G /\ ¬q ∈ G)).
      { intros q [Hq Hnq]. apply (HGcons q). split; apply L0; assumption. }
      assert (Hnot2 : forall q, ~ (q ∈ G) -> ¬q ∈ G).
      { intros q Hnq. destruct (No_contra G HGcons q) as [Hc | Hc].
        - exfalso. apply Hnq. apply HGmax. exact Hc.
        - apply HGmax. exact Hc. }
      assert (Hv : value v).
      { split.
        - intros q. destruct (classicT (q ∈ G)) as [Hq | Hq].
          + rewrite (HvF (¬q) (fun H => HnotG q (conj Hq H))). rewrite (HvT q Hq). reflexivity.
          + rewrite (HvT (¬q) (Hnot2 q Hq)). rewrite (HvF q Hq). reflexivity.
        - intros q r.
          assert (Himp1 : q ∈ G -> r ∈ G -> q → r ∈ G).
          { intros Hq Hr. apply HG_prove. apply ded_weaken. apply L0. exact Hr. }
          assert (Himp2 : q ∈ G -> ~ (r ∈ G) -> ~ (q → r ∈ G)).
          { intros Hq Hr Hqr. apply Hr. apply HG_prove.
            eapply MP with (p := q); [apply L0; exact Hqr | apply L0; exact Hq]. }
          assert (Himp3 : ~ (q ∈ G) -> q → r ∈ G).
          { intros Hq. apply HG_prove.
            eapply MP with (p := ¬q);
              [apply law_deny_antecedent | apply L0; apply Hnot2; exact Hq]. }
          destruct (classicT (q ∈ G)) as [Hq | Hq];
            destruct (classicT (r ∈ G)) as [Hr | Hr].
          + rewrite (HvT (q → r) (Himp1 Hq Hr)). rewrite (HvT q Hq). rewrite (HvT r Hr). reflexivity.
          + rewrite (HvF (q → r) (Himp2 Hq Hr)). rewrite (HvT q Hq). rewrite (HvF r Hr). reflexivity.
          + rewrite (HvT (q → r) (Himp3 Hq)). rewrite (HvF q Hq). rewrite (HvT r Hr). reflexivity.
          + rewrite (HvT (q → r) (Himp3 Hq)). rewrite (HvF q Hq). rewrite (HvF r Hr). reflexivity. }
      assert (Hmem : forall q, q ∈ Γ -> v q = true).
      { intros q Hq. apply HvT. apply HGsub. apply UnionI. left. exact Hq. }
      assert (Hnp : ¬p ∈ G).
      { apply HGsub. apply UnionI. right. apply Single. reflexivity. }
      assert (HpG : ~ (p ∈ G)).
      { intro Hp'. apply (HGcons p). split; apply L0; assumption. }
      pose proof (Hsem v Hv Hmem) as Hvp.
      rewrite (HvF p HpG) in Hvp. discriminate Hvp.
  - apply boom. exact Hncons.
Qed.
