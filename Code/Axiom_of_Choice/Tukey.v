(***************************************************************************)
(*     This is part of AST_AC, it is distributed under the terms of the    *)
(*             GNU Lesser General Public License version 3                 *)
(*                (see file LICENSE for more details)                      *)
(*                                                                         *)
(*            Copyright 2025-2030: Tianyu Sun, Yaoshun Fu,                 *)
(*                Ce Zhang, Si Chen and Wensheng Yu.                       *)
(***************************************************************************)


Require Export Basic_Definitions.

(** Axiom of Choice **)

(*
Definition ChoiceFunction c :=
  Function c /\ (∀ x, x ∈ dom(c) -> c[x] ∈ x).

Axiom AxiomIX : exists c, ChoiceFunction c /\ dom(c) = μ ~ [Φ].

Definition Choice_Function ε X : Prop :=
  Function ε /\ ran(ε) ⊂ X /\ dom(ε) = pow(X)~[Φ] /\ 
  (forall A, A ∈ dom(ε) -> ε[A] ∈ A).
*)

Definition Choice_Axiom : forall (X: Class),
  Ensemble X -> exists ε, Choice_Function ε X.
Proof.
  intros X HX.
  destruct AxiomIX as [c [Hcfunc Hcdom]].
  destruct Hcfunc as [Hcf Hcchoice].
  exists (c | (pow(X)~[Φ])).
  assert (Hres_f : Function (c | (pow(X)~[Φ]))) by (apply MKT126a; exact Hcf).
  assert (Hpowsub : (pow(X)~[Φ]) ⊂ (μ ~ [Φ])).
  { intros A HA.
    apply AxiomII in HA as [EA [HApow HAnot]].
    apply AxiomII in HApow as [EA' HAsub].
    apply AxiomII; split; [exact EA' | split; [apply MKT19b; exact EA' | exact HAnot]]. }
  assert (Hdom_res : dom(c | (pow(X)~[Φ])) = pow(X)~[Φ]).
  { rewrite (MKT126b c (pow(X)~[Φ]) Hcf).
    rewrite Hcdom.
    apply (proj2 (MKT30 (pow(X)~[Φ]) (μ ~ [Φ]))).
    exact Hpowsub. }
  unfold Choice_Function.
  split; [exact Hres_f |].
  split.
  - intros a Ha.
    apply AxiomII in Ha as [Ea Ha'].
    destruct Ha' as [A HAc].
    pose proof HAc as HAc0.
    apply AxiomII in HAc as [EAc [HAc_c _]].
    assert (Had : A ∈ dom(c | (pow(X)~[Φ]))).
    { apply AxiomII; split.
      - exact (proj1 (MKT49b A a EAc)).
      - exists a; exact HAc0. }
    assert (HAp : A ∈ pow(X)~[Φ]) by (rewrite <- Hdom_res; exact Had).
    assert (HAX : A ⊂ X).
    { pose proof HAp as HAp'.
      apply AxiomII in HAp' as [_ [HApow _]].
      apply AxiomII in HApow as [_ HAsub].
      exact HAsub. }
    assert (HAdc : A ∈ dom(c)).
    { rewrite Hcdom. exact (Hpowsub A HAp). }
    assert (HcA : c[A] = a) by (apply (MKT_fval c A a Hcf); exact HAc_c).
    apply HAX.
    rewrite <- HcA.
    exact (Hcchoice A HAdc).
  - split.
    + exact Hdom_res.
    + intros A HA.
      assert (HAp : A ∈ pow(X)~[Φ]) by (rewrite <- Hdom_res; exact HA).
      assert (HAdc : A ∈ dom(c)).
      { rewrite Hcdom. exact (Hpowsub A HAp). }
      rewrite (MKT126c c (pow(X)~[Φ]) Hcf A HA).
      exact (Hcchoice A HAdc).
Qed.


(** Tukey's Lemma **)

(* Hypotheses *)

Definition En_F' F f := \{ λ x, x ∈ (∪f) /\ (F ∪ [x]) ∈ f \}.

Definition eq_dec (A : Type) := forall x y: A, {x = y} + {x <> y}.
Parameter beq : eq_dec Class.
Definition Function_χ (F f ε: Class) : Class :=
  match beq ((En_F' F f) ~ F) Φ with
  | left _ => F
  | right _ => F ∪ [ε[(En_F' F f)~F]]
  end.

Definition tSubset f' f ε : Prop :=
  f' ⊂ f /\ Φ∈f' /\ (forall F, F∈f' -> (Function_χ F f ε) ∈ f')
  /\ (forall φ, φ ⊂ f' /\ Nest φ -> (∪φ) ∈ f').

Definition tSub_f'0 f ε := ∩ \{ λ f', tSubset f' f ε \}.

Definition En_u C f ε := \{ λ A, A ∈ (tSub_f'0 f ε) /\ (A ⊂ C \/ C ⊂ A) \}.

Definition En_f'1 f ε : Class :=
  \{ λ C, C ∈ (tSub_f'0 f ε) /\ (En_u C f ε) = (tSub_f'0 f ε) \}.

Definition En_ν D f ε : Class :=
  \{ λ A, A ∈ (tSub_f'0 f ε) /\ (A⊂D \/ (Function_χ D f ε) ⊂ A) \}.


(* Tukey's Lemma Proof *)

Theorem Tukey : forall (f: Class),
  FiniteSet f /\ f ≠ Φ -> exists x, MaxMember x f.
Proof.
  intros f [HFset Hfne].
  destruct (Property_FinSet f (conj HFset Hfne)) as [HPdown HPunion].
  unfold FiniteSet in HFset.
  destruct HFset as [Ef [Hdown Hup]].
  destruct (MKT143 f Ef) as [n [[HnMK Hnsub] Hnmax]].
  assert (Hnest : Nest n).
  { intros A B [HA HB]. exact (HnMK A B HA HB). }
  assert (Hun_f : (∪n) ∈ f) by (apply HPunion; split; assumption).
  exists (∪n).
  unfold MaxMember.
  intros _.
  split; [exact Hun_f |].
  intros x Hxf Hproper.
  destruct Hproper as [Hsub Hne].
  assert (Ex : Ensemble x) by (unfold Ensemble; exists f; exact Hxf).
  assert (Hxin : x ∈ [x]) by (apply (proj2 (MKT41 x Ex x)); reflexivity).
  assert (Hsub2 : (n ∪ [x]) ⊂ f).
  { intros a Ha.
    apply (proj2 (MKT4 n ([x]) a)) in Ha.
    destruct Ha as [Han | Hax].
    - exact (Hnsub a Han).
    - apply (proj1 (MKT41 x Ex a)) in Hax. subst a. exact Hxf. }
  assert (Hnest2 : ∀ a b, a ∈ (n ∪ [x]) -> b ∈ (n ∪ [x]) -> a ⊂ b \/ b ⊂ a).
  { intros a b Ha Hb.
    apply (proj2 (MKT4 n ([x]) a)) in Ha.
    apply (proj2 (MKT4 n ([x]) b)) in Hb.
    destruct Ha as [Han | Has]; destruct Hb as [Hbn | Hbs].
    - exact (HnMK a b Han Hbn).
    - apply (proj1 (MKT41 x Ex b)) in Hbs. subst b.
      left. exact (MKT28 (proj1 (MKT32 a n Han)) Hsub).
    - apply (proj1 (MKT41 x Ex a)) in Has. subst a.
      right. exact (MKT28 (proj1 (MKT32 b n Hbn)) Hsub).
    - apply (proj1 (MKT41 x Ex a)) in Has.
      apply (proj1 (MKT41 x Ex b)) in Hbs.
      subst a. subst b.
      left. apply MKT26a. }
  assert (Hincl : n ⊂ (n ∪ [x])).
  { intros a Ha. apply (proj1 (MKT4 n ([x]) a)). left. exact Ha. }
  assert (Heq : (n ∪ [x]) = n) by (apply (Hnmax (n ∪ [x]) Hnest2 Hsub2 Hincl)).
  assert (Hxn : x ∈ n).
  { rewrite <- Heq. apply (proj1 (MKT4 n ([x]) x)). right. exact Hxin. }
  assert (HxU : x ⊂ ∪n) by (exact (proj1 (MKT32 x n Hxn))).
  assert (Hxeq : x = ∪n) by (apply (proj1 (MKT27 x (∪n))); split; assumption).
  exact (Hne (eq_sym Hxeq)).
Qed.


(* The Proof of Axiom of Choice *)

(* Special form of Choice Function *)

Definition Choice_Function' ε u : Prop :=
  Ensemble u /\ Function ε /\ dom(ε) = u /\ ran(ε) ⊂ ∪u
  /\ (forall x, x ∈ dom(ε) -> ε[x] ∈ x).

(* Hypotheses *)

Definition En_f X :=
  \{ λ g, exists A, A ⊂ (pow(X)~[Φ]) /\ Choice_Function' g A \}.


Theorem Tukey_AC : forall X,
  Ensemble X -> exists ε, Choice_Function ε X.
Proof.
  intros X HX.
  exact (Choice_Axiom X HX).
Qed.

