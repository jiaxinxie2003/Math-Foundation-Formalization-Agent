(***************************************************************************)
(*     This is part of AST_AC, it is distributed under the terms of the    *)
(*             GNU Lesser General Public License version 3                 *)
(*                (see file LICENSE for more details)                      *)
(*                                                                         *)
(*            Copyright 2025-2030: Tianyu Sun, Yaoshun Fu,                 *)
(*                Ce Zhang, Si Chen and Wensheng Yu.                       *)
(***************************************************************************)


Require Export MK.

(** Some necessary and additional definitions for the proof **)

(* Nest *)

Definition Nest f : Prop := forall A B, A∈f /\ B∈f -> A⊂B \/ B⊂A.



(* Finite Characteristic Set *)

Definition FiniteSet f : Prop :=
  Ensemble f /\ (forall F, F∈f -> (forall z, z ⊂ F /\ Finite z -> z∈f))
  /\ (forall F, Ensemble F /\ (forall z, z ⊂ F /\ Finite z -> z∈f) -> F∈f).


(* Property of Finite Characteristic Set *)

Proposition Property_FinSet : forall f: Class,
  FiniteSet f /\ f ≠ Φ -> (forall A B, A ∈ f /\ B ⊂ A -> B ∈ f)
  /\ (forall φ, φ ⊂ f /\ Nest φ -> (∪φ) ∈ f).
Proof.
  intros f [HF Hfne].
  unfold FiniteSet in HF.
  destruct HF as [Ef [Hdown Hup]].
  split.
  - (* f 对包含关系向下封闭 *)
    intros A B [HAf HBA].
    apply Hup. split.
    + assert (EA : Ensemble A) by (unfold Ensemble; eauto).
      exact (MKT33 A B EA HBA).
    + intros z [HzB Hfz].
      apply (Hdown A HAf z). split.
      * intros w Hw. exact (HBA w (HzB w Hw)).
      * exact Hfz.
  - (* 链（Nest）的并仍属于 f *)
    intros phi [Hphi_f Hnest].
    assert (Ephi : Ensemble phi) by (apply (MKT33 f phi Ef Hphi_f)).
    assert (Eunion : Ensemble (∪phi)) by (apply (AxiomVI phi Ephi)).
    assert (HFinPhi : Finite Φ).
    { unfold Finite.
      assert (HΦC : Φ ∈ C) by (apply MKT164; exact MKT135a).
      assert (HpΦ : P[Φ] = Φ) by (exact (proj2 (proj2 (MKT156 Φ) HΦC))).
      rewrite HpΦ. exact MKT135a. }
    assert (HPhi_f : Φ ∈ f).
    { destruct (MKT_nonempty f Hfne) as [F0 HF0].
      apply (Hdown F0 HF0 Φ). split; [apply MKT26 | exact HFinPhi]. }
    assert (EΦ : Ensemble Φ) by (unfold Ensemble; exists ω; exact MKT135a).
    (* 关键引理：链中任一有限子集都包含于链的某个成员中 *)
    set (S := \{ λ n, n ∈ ω /\ (∀ z, z ≈ n -> z ⊂ ∪phi
        -> (∃ t, t ∈ phi /\ z ⊂ t) \/ z ⊂ Φ) \}).
    assert (HSω : S ⊂ ω).
    { intros n Hn. apply AxiomII in Hn as [_ [Hnω _]]. exact Hnω. }
    assert (HΦS : Φ ∈ S).
    { apply AxiomII; split; [exact EΦ | split].
      - exact MKT135a.
      - intros z HzΦ Hzsub. right.
        assert (Hz : z = Φ) by (apply MKT172_empty_equiv; exact HzΦ).
        rewrite Hz. apply MKT26a. }
    assert (HsuccS : ∀ u, u ∈ S -> PlusOne u ∈ S).
    { intros u Hu.
      apply AxiomII in Hu as [Eu [Huω HIH]].
      pose proof (MKT134 Huω) as Hpuω.
      assert (Epu : Ensemble (PlusOne u)).
      { apply AxiomII in Hpuω as [E _]. exact E. }
      apply AxiomII; split; [exact Epu | split; [exact Hpuω |]].
      intros z Hzpo Hzsub.
      destruct (classic (z = Φ)) as [HzΦ | Hzne].
      - right. rewrite HzΦ. apply MKT26.
      - left.
        destruct (MKT_nonempty z Hzne) as [a Haz].
        assert (Haz' : a ∈ ∪phi) by (exact (Hzsub a Haz)).
        apply AxiomII in Haz' as [Ea Haux].
        destruct Haux as [ta [Hata Htaphi]].
        assert (Hrem : (z ~ [a]) ≈ u)
          by (apply (MKT172_remove_any z u Huω Hzpo a Haz)).
        assert (Hrem_sub : (z ~ [a]) ⊂ ∪phi).
        { intros w Hw. apply AxiomII in Hw as [Ew [Hwz _]]. exact (Hzsub w Hwz). }
        destruct (HIH (z ~ [a]) Hrem Hrem_sub) as [[t [Htphi Hzt]] | HsubΦ].
        + destruct (Hnest t ta (conj Htphi Htaphi)) as [Htta | Hatt].
          * exists ta; split; [exact Htaphi |].
            intros w Hwz.
            destruct (classic (w = a)) as [Hwa | Hwna].
            -- rewrite Hwa. exact Hata.
            -- apply Htta. apply Hzt.
               apply AxiomII; split.
               ++ unfold Ensemble; eauto.
               ++ split; [exact Hwz | apply AxiomII; split; [unfold Ensemble; eauto |]].
                  intro Hin. apply Hwna. exact (proj1 (MKT41 a Ea w) Hin).
          * exists t; split; [exact Htphi |].
            intros w Hwz.
            destruct (classic (w = a)) as [Hwa | Hwna].
            -- rewrite Hwa. exact (Hatt a Hata).
            -- apply Hzt.
               apply AxiomII; split.
               ++ unfold Ensemble; eauto.
               ++ split; [exact Hwz | apply AxiomII; split; [unfold Ensemble; eauto |]].
                  intro Hin. apply Hwna. exact (proj1 (MKT41 a Ea w) Hin).
        + exists ta; split; [exact Htaphi |].
          intros w Hwz.
          destruct (classic (w = a)) as [Hwa | Hwna].
          * rewrite Hwa. exact Hata.
          * apply (MKT26 ta).
            apply HsubΦ.
            apply AxiomII; split.
            -- unfold Ensemble; eauto.
            -- split; [exact Hwz | apply AxiomII; split; [unfold Ensemble; eauto |]].
               intro Hin. apply Hwna. exact (proj1 (MKT41 a Ea w) Hin). }
    assert (HS : S = ω) by (apply (MKT137 S HSω HΦS HsuccS)).
    apply Hup. split; [exact Eunion |].
    intros z [Hzsub Hfin].
    assert (Ez : Ensemble z) by (apply (MKT33 (∪phi) z Eunion Hzsub)).
    assert (HzP : z ≈ P[z]) by (apply MKT146; apply MKT153; exact Ez).
    assert (HzS : P[z] ∈ S) by (rewrite HS; exact Hfin).
    apply AxiomII in HzS as [_ [_ HzS']].
    destruct (HzS' z HzP Hzsub) as [[t [Ht Hzt]] | HzΦ].
    + apply (Hdown t (Hphi_f t Ht) z). split; assumption.
    + assert (Hz_eq : z = Φ)
        by (apply (proj1 (MKT27 z Φ)); split; [exact HzΦ | apply MKT26]).
      rewrite Hz_eq. exact HPhi_f.
Qed.

(* MKT A.3 Proper Subset *)

Definition ProperIncluded x y : Prop := x ⊂ y /\ x ≠ y.

Notation "x ⊊ y" := (ProperIncluded x y) (at level 70).

Corollary Property_ProperIncluded : forall (x y: Class),
  x ⊂ y -> (x ⊊ y) \/ x = y.
Proof.
  intros x y H.
  destruct (classic (x = y)) as [Heq | Hne].
  - right; exact Heq.
  - left. unfold ProperIncluded. split; assumption.
Qed.


Proposition imply_to_and : ∀ P Q : Prop, ~ (P -> Q) -> P /\ ~ Q.
Proof.
  intros P Q H. split.
  - destruct (classic P) as [HP | HnP]; [exact HP |].
    exfalso. apply H. intros HP. exfalso. exact (HnP HP).
  - intro HQ. apply H. intros _. exact HQ.
Qed.

(*pre有*)
Proposition not_ex_all_not :
 ∀ U P, ~ (∃ n : U, P n) -> ∀ n : U, ~ P n.
Proof.
  intros U P H n HP. apply H. exists n. exact HP.
Qed.

(* ∀ U (P : U -> Prop) 对； ∀ U P 错*)
Proposition not_all_ex_not :
∀ U (P : U -> Prop), ~ (∀ n : U, P n) -> ∃ n : U, ~ P n.
Proof.
  intros U P H.
  apply NNPP. intro Hn.
  apply H. intros n.
  destruct (classic (P n)) as [HP | HnP]; [exact HP |].
  exfalso. apply Hn. exists n. exact HnP.
Qed.

Corollary Property_ProperIncluded' : forall (x y: Class),
  x ⊊ y -> exists z, z ∈ y /\ z ∉ x.
Proof.
  intros x y H.
  unfold ProperIncluded in H.
  destruct H as [Hsub Hne].
  apply NNPP. intro Hn.
  apply Hne.
  apply AxiomI. intros z. split.
  - exact (Hsub z).
  - intro Hzy.
    destruct (classic (z ∈ x)) as [Hzx | Hnzx]; [exact Hzx |].
    exfalso. apply Hn. exists z. split; assumption.
Qed.

Corollary Property_ProperIncluded'' : forall (x y: Class),
  x ⊂ y \/ y ⊂ x -> ~ (x ⊂ y) -> y ⊊ x.
Proof.
  intros x y [Hxy | Hyx] Hn.
  - exfalso. exact (Hn Hxy).
  - unfold ProperIncluded. split; [exact Hyx |].
    intro Heq. apply Hn. rewrite Heq. apply MKT26a.
Qed.

(* Maximial Member : F is a maximal member of f iff no member of f is properly contained in F. [K55] *)

Definition MaxMember F f : Prop :=
  f ≠ Φ -> F∈f /\ (forall x, x∈f -> ~ F ⊊ x).



(* Minimial Member : Similarly F is a minimal member of f iff no member of f is properly contained in F. [K55] *)

Definition MinMember F f : Prop :=
  f ≠ Φ -> F∈f /\ (forall x, x∈f -> ~ x ⊊ F).



(* Choice Function *)

Definition Choice_Function ε X : Prop :=
  Function ε /\ ran(ε) ⊂ X /\ dom(ε) = pow(X)~[Φ] /\ 
  (forall A, A ∈ dom(ε) -> ε[A] ∈ A).


(** Order **)

(* Partial Order, Partially Ordered Set *)

Definition Reflexivity le X := forall a, a∈X -> Rrelation a le a.

Definition Antisymmetry le X :=
  forall x y, x∈X /\ y∈X -> (Rrelation x le y /\ Rrelation y le x -> x = y).

Definition Transitivity r x : Prop :=
  forall u v w, (u∈x /\ v∈x /\ w∈x) /\
  (Rrelation u r v /\ Rrelation v r w) -> Rrelation u r w.

Definition PartialOrder le X : Prop :=
  Ensemble X /\ (Relation le /\ le ⊂ X × X) /\
  Reflexivity le X /\ Antisymmetry le X /\ Transitivity le X.

Definition PartialOrderSet X le := PartialOrder le X.



(* Upper Bound, Lower Bound *)

Definition BoundU x A X le : Prop :=
  PartialOrder le X /\ X ≠ Φ ->
  x∈X /\ A⊂X /\ (forall a, a∈A -> Rrelation a le x).

Definition BoundD x A X le : Prop :=
  PartialOrder le X /\ X ≠ Φ ->
  x∈X /\ A⊂X /\ (forall a, a∈A -> Rrelation x le a).


(* Maximal Element : We say that x∈X is a maximal element if *)

Definition MaxElement x X le : Prop :=
  X ≠ Φ -> x∈X /\ (forall y, y∈X -> ~ (Rrelation x le y /\ x ≠ y)).

(* Minimal Element *)

Definition MinElement x X le : Prop :=
  X ≠ Φ -> x∈X /\ (forall y, y∈X -> ~ (Rrelation y le x /\ x ≠ y)).



(* Total Order, Totally Ordered Set *)

Definition TotalOrder le X := 
  PartialOrder le X /\ (forall x y, x∈X /\ y∈X ->
  (x ≠ y -> Rrelation x le y \/ Rrelation y le x)).

Definition TotalOrderSet X le := TotalOrder le X.


(* Chain *)

Definition Chain A X le : Prop :=
  PartialOrder le X -> (A ⊂ X /\ A ≠ Φ) /\ TotalOrder (le ∩ (A × A)) A.


(* Well Order Set *)

Definition WellOrder le X :=
  TotalOrder le X /\ (forall A, A⊂X /\ A≠Φ -> exists z, MinElement z A le).

Definition WellOrderSet X le := WellOrder le X.


(* Initial_Segment *)

Definition Initial_Segment Y X le := Y ⊂ X /\ WellOrder le X /\
  (forall u v, (u ∈ X /\ v ∈ Y /\ Rrelation u le v ) -> u ∈ Y).




