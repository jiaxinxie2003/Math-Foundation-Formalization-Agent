(***************************************************************************)
(*     This is part of AST_AC, it is distributed under the terms of the    *)
(*             GNU Lesser General Public License version 3                 *)
(*                (see file LICENSE for more details)                      *)
(*                                                                         *)
(*            Copyright 2025-2030: Tianyu Sun, Yaoshun Fu,                 *)
(*                Ce Zhang, Si Chen and Wensheng Yu.                       *)
(***************************************************************************)


Require Export Tukey.


(** Hausdorff Maximal Principle **)

Definition En_f1 f A := \{ λ F, F∈f /\ (F ∪ A) ∈ f \}.

Theorem Hausdorff : forall (A N: Class),
  Ensemble A -> N ⊂ A /\ Nest N ->
  (exists u, MaxMember u \{ λ n, n⊂A /\ Nest n \} /\ N ⊂ u).
Proof.
  intros A N HA [HNA HNest].
  set (f := \{ λ n, n ⊂ A /\ Nest n \}).
  set (g := En_f1 f N).
  assert (EΦ : Ensemble Φ) by (apply (MKT33 A Φ HA); apply MKT26).
  assert (EN : Ensemble N) by (apply (MKT33 A N HA); exact HNA).
  (* ---- every singleton (of a set) is finite ---- *)
  assert (FinSing : ∀ a, Ensemble a -> Finite ([a])).
  { intros a Ea.
    set (h := \{\ λ u v, u = a /\ v = Φ \}\).
    assert (Hh_prop : ∀ u v, [u,v] ∈ h -> u = a /\ v = Φ).
    { intros u v H.
      apply AxiomII in H as [E H].
      destruct H as [u' [v' [Heq [Hu' Hv']]]].
      destruct (MKT49b u v E) as [Eu Ev].
      assert (Eu'v' : Ensemble ([u',v'])) by (rewrite <- Heq; exact E).
      destruct (MKT49b u' v' Eu'v') as [Eu' Ev'].
      destruct (proj1 (MKT55 u v u' v' Eu Ev) Heq) as [Huu' Hvv'].
      split; [rewrite Huu'; exact Hu' | rewrite Hvv'; exact Hv']. }
    assert (Hha : [a,Φ] ∈ h).
    { apply AxiomII; split.
      - apply MKT49a; assumption.
      - exists a; exists Φ; split; [reflexivity | split; [reflexivity | reflexivity]]. }
    assert (Haa : [a] ≈ [Φ]).
    { assert (Hh_dom : dom(h) = [a]).
      { apply AxiomI; intros u; split.
        - intros Hu. apply AxiomII in Hu as [Eu Hu].
          destruct Hu as [v Huv].
          destruct (Hh_prop u v Huv) as [Hua _].
          apply (proj2 (MKT41 a Ea u)). exact Hua.
        - intros Hu.
          apply (proj1 (MKT41 a Ea u)) in Hu. subst u.
          apply AxiomII; split; [exact Ea | exists Φ; exact Hha]. }
      assert (Hh_ran : ran(h) = [Φ]).
      { apply AxiomI; intros v; split.
        - intros Hv. apply AxiomII in Hv as [Ev Hv].
          destruct Hv as [u Huv].
          destruct (Hh_prop u v Huv) as [_ HvΦ].
          apply (proj2 (MKT41 Φ EΦ v)). exact HvΦ.
        - intros Hv.
          apply (proj1 (MKT41 Φ EΦ v)) in Hv. subst v.
          apply AxiomII; split; [exact EΦ | exists a; exact Hha]. }
      assert (Hh_func : Function h).
      { split.
        - intros z Hz. apply AxiomII in Hz as [E Hz].
          destruct Hz as [u [v [Hzuv _]]]. exists u; exists v; exact Hzuv.
        - intros u v w Huv Huw.
          destruct (Hh_prop u v Huv) as [_ Hv].
          destruct (Hh_prop u w Huw) as [_ Hw].
          rewrite Hv. rewrite Hw. reflexivity. }
      assert (Hh_inv : Function (h⁻¹)).
      { split.
        - intros z Hz. apply AxiomII in Hz as [E Hz].
          destruct Hz as [u [v [Hzuv _]]]. exists u; exists v; exact Hzuv.
        - intros u v w Huv Huw.
          assert (Euv : Ensemble ([u,v])) by (unfold Ensemble; exists (h⁻¹); exact Huv).
          destruct (MKT49b u v Euv) as [Eu Ev].
          assert (Euw : Ensemble ([u,w])) by (unfold Ensemble; exists (h⁻¹); exact Huw).
          destruct (MKT49b u w Euw) as [Eu' Ew].
          assert (Hvu : [v,u] ∈ h) by (apply (proj1 (MKT_inv_in h u v Eu Ev)); exact Huv).
          assert (Hwu : [w,u] ∈ h) by (apply (proj1 (MKT_inv_in h u w Eu' Ew)); exact Huw).
          destruct (Hh_prop v u Hvu) as [Hva _].
          destruct (Hh_prop w u Hwu) as [Hwa _].
          rewrite Hva. rewrite Hwa. reflexivity. }
      exists h; split; [split; assumption | split; assumption]. }
    assert (Hsing : [Φ] = PlusOne Φ) by (unfold PlusOne; rewrite MKT17; reflexivity).
    assert (HΦω : [Φ] ∈ ω) by (rewrite Hsing; apply MKT134; exact MKT135a).
    assert (HΦC : [Φ] ∈ C) by (rewrite Hsing; apply MKT164; exact (MKT134 MKT135a)).
    assert (HpΦ : P[[Φ]] = [Φ]) by (exact (proj2 (proj2 (MKT156 ([Φ])) HΦC))).
    assert (Hpp : P[[a]] = P[[Φ]]) by
      (apply (proj2 (MKT154 ([a]) ([Φ]) (MKT42 a Ea) (MKT42 Φ EΦ))); exact Haa).
    unfold Finite. rewrite Hpp. rewrite HpΦ. exact HΦω. }
  (* ---- every unordered pair (of sets) is finite ---- *)
  assert (FinPair : ∀ a b, Ensemble a -> Ensemble b -> Finite ([a|b])).
  { intros a b Ea Eb.
    exact (MKT168 ([a]) ([b]) (FinSing a Ea) (FinSing b Eb)). }
  (* ---- g is a set ---- *)
  assert (Eg : Ensemble g).
  { apply (MKT33 (pow(A)) g (MKT38a HA)).
    intros F HF. unfold g in HF. unfold En_f1 in HF.
    apply AxiomII in HF as [EF [HFf _]].
    unfold f in HFf. apply AxiomII in HFf as [_ [HFA _]].
    apply AxiomII; split; [exact EF | exact HFA]. }
  (* ---- g is of finite character : downward ---- *)
  assert (Gdown : ∀ F, F ∈ g -> ∀ z, z ⊂ F /\ Finite z -> z ∈ g).
  { intros F HF z [HzF Hfin].
    pose proof HF as HF0.
    unfold g in HF0. unfold En_f1 in HF0.
    apply AxiomII in HF0 as [_ [HFf HFN]].
    unfold f in HFf. apply AxiomII in HFf as [_ [HFA HFnest]].
    unfold f in HFN. apply AxiomII in HFN as [_ [_ HFNnest]].
    assert (HzA : z ⊂ A) by (exact (MKT28 HzF HFA)).
    assert (Ez : Ensemble z) by (apply (MKT33 A z HA HzA)).
    assert (Hznest : Nest z).
    { intros a b [Ha Hb]. exact (HFnest a b (conj (HzF a Ha) (HzF b Hb))). }
    assert (HzNnest : Nest (z ∪ N)).
    { intros a b [Ha Hb].
      apply (proj2 (MKT4 z N a)) in Ha.
      apply (proj2 (MKT4 z N b)) in Hb.
      destruct Ha as [Haz | Han]; destruct Hb as [Hbz | Hbn].
      - exact (Hznest a b (conj Haz Hbz)).
      - apply (HFNnest a b). split.
        + apply (proj1 (MKT4 F N a)). left. exact (HzF a Haz).
        + apply (proj1 (MKT4 F N b)). right. exact Hbn.
      - apply (HFNnest a b). split.
        + apply (proj1 (MKT4 F N a)). right. exact Han.
        + apply (proj1 (MKT4 F N b)). left. exact (HzF b Hbz).
      - exact (HNest a b (conj Han Hbn)). }
    assert (HzNA : (z ∪ N) ⊂ A).
    { intros a Ha. apply (proj2 (MKT4 z N a)) in Ha.
      destruct Ha as [Haz | Han]; [exact (HzA a Haz) | exact (HNA a Han)]. }
    assert (EzN : Ensemble (z ∪ N)) by (apply AxiomIV; assumption).
    unfold g, En_f1. apply AxiomII; split; [exact Ez | split].
    - unfold f. apply AxiomII; split; [exact Ez | split; [exact HzA | exact Hznest]].
    - unfold f. apply AxiomII; split; [exact EzN | split; [exact HzNA | exact HzNnest]]. }
  (* ---- g is of finite character : upward ---- *)
  assert (Gup : ∀ F, Ensemble F /\ (∀ z, z ⊂ F /\ Finite z -> z ∈ g) -> F ∈ g).
  { intros F [EF Hall].
    assert (HFA : F ⊂ A).
    { intros a Ha.
      assert (Ea : Ensemble a) by (unfold Ensemble; exists F; exact Ha).
      assert (Hsing : [a] ⊂ F)
        by (intros z Hz; apply (proj1 (MKT41 a Ea z)) in Hz; subst z; exact Ha).
      assert (Hg1 : [a] ∈ g) by (apply Hall; split; [exact Hsing | exact (FinSing a Ea)]).
      unfold g in Hg1. unfold En_f1 in Hg1.
      apply AxiomII in Hg1 as [_ [Hf1 _]].
      unfold f in Hf1. apply AxiomII in Hf1 as [_ [H1A _]].
      apply H1A. apply (proj2 (MKT41 a Ea a)). reflexivity. }
    assert (HFnest : Nest F).
    { intros a b [Ha Hb].
      assert (Ea : Ensemble a) by (unfold Ensemble; exists F; exact Ha).
      assert (Eb : Ensemble b) by (unfold Ensemble; exists F; exact Hb).
      assert (Hpair : [a|b] ⊂ F).
      { intros z Hz. apply (proj1 (MKT46b Ea Eb z)) in Hz.
        destruct Hz as [Hza | Hzb]; subst z; assumption. }
      assert (Hg1 : [a|b] ∈ g)
        by (apply Hall; split; [exact Hpair | exact (FinPair a b Ea Eb)]).
      unfold g in Hg1. unfold En_f1 in Hg1.
      apply AxiomII in Hg1 as [_ [Hf1 _]].
      unfold f in Hf1. apply AxiomII in Hf1 as [_ [_ Hnest1]].
      apply (Hnest1 a b). split.
      - apply (proj2 (MKT46b Ea Eb a)). left. reflexivity.
      - apply (proj2 (MKT46b Ea Eb b)). right. reflexivity. }
    assert (HFNA : (F ∪ N) ⊂ A).
    { intros a Ha. apply (proj2 (MKT4 F N a)) in Ha.
      destruct Ha as [HaF | HaN]; [exact (HFA a HaF) | exact (HNA a HaN)]. }
    assert (HFNnest : Nest (F ∪ N)).
    { intros a b [Ha Hb].
      apply (proj2 (MKT4 F N a)) in Ha.
      apply (proj2 (MKT4 F N b)) in Hb.
      destruct Ha as [HaF | HaN]; destruct Hb as [HbF | HbN].
      - assert (Ea : Ensemble a) by (unfold Ensemble; exists F; exact HaF).
        assert (Eb : Ensemble b) by (unfold Ensemble; exists F; exact HbF).
        assert (Hpair : [a|b] ⊂ F).
        { intros z Hz. apply (proj1 (MKT46b Ea Eb z)) in Hz.
          destruct Hz as [Hza | Hzb]; subst z; assumption. }
        assert (Hg1 : [a|b] ∈ g)
          by (apply Hall; split; [exact Hpair | exact (FinPair a b Ea Eb)]).
        unfold g in Hg1. unfold En_f1 in Hg1.
        apply AxiomII in Hg1 as [_ [Hf1 _]].
        unfold f in Hf1. apply AxiomII in Hf1 as [_ [_ Hnest1]].
        apply (Hnest1 a b). split.
        + apply (proj2 (MKT46b Ea Eb a)). left. reflexivity.
        + apply (proj2 (MKT46b Ea Eb b)). right. reflexivity.
      - assert (Ea : Ensemble a) by (unfold Ensemble; exists F; exact HaF).
        assert (Hsing : [a] ⊂ F)
          by (intros z Hz; apply (proj1 (MKT41 a Ea z)) in Hz; subst z; exact HaF).
        assert (Hg1 : [a] ∈ g) by (apply Hall; split; [exact Hsing | exact (FinSing a Ea)]).
        unfold g in Hg1. unfold En_f1 in Hg1.
        apply AxiomII in Hg1 as [_ [_ Hg1N]].
        unfold f in Hg1N. apply AxiomII in Hg1N as [_ [_ Hg1Nnest]].
        apply (Hg1Nnest a b). split.
        + apply (proj1 (MKT4 ([a]) N a)). left.
          apply (proj2 (MKT41 a Ea a)). reflexivity.
        + apply (proj1 (MKT4 ([a]) N b)). right. exact HbN.
      - assert (Eb : Ensemble b) by (unfold Ensemble; exists F; exact HbF).
        assert (Hsing : [b] ⊂ F)
          by (intros z Hz; apply (proj1 (MKT41 b Eb z)) in Hz; subst z; exact HbF).
        assert (Hg1 : [b] ∈ g) by (apply Hall; split; [exact Hsing | exact (FinSing b Eb)]).
        unfold g in Hg1. unfold En_f1 in Hg1.
        apply AxiomII in Hg1 as [_ [_ Hg1N]].
        unfold f in Hg1N. apply AxiomII in Hg1N as [_ [_ Hg1Nnest]].
        apply (Hg1Nnest a b). split.
        + apply (proj1 (MKT4 ([b]) N a)). right. exact HaN.
        + apply (proj1 (MKT4 ([b]) N b)). left.
          apply (proj2 (MKT41 b Eb b)). reflexivity.
      - exact (HNest a b (conj HaN HbN)). }
    assert (EFN : Ensemble (F ∪ N)) by (apply AxiomIV; assumption).
    unfold g, En_f1. apply AxiomII; split; [exact EF | split].
    - unfold f. apply AxiomII; split; [exact EF | split; [exact HFA | exact HFnest]].
    - unfold f. apply AxiomII; split; [exact EFN | split; [exact HFNA | exact HFNnest]]. }
  (* ---- apply Tukey's lemma ---- *)
  assert (HFset : FiniteSet g).
  { unfold FiniteSet. split; [exact Eg | split; [exact Gdown | exact Gup]]. }
  assert (Hgne : g ≠ Φ).
  { intro H0.
    assert (HΦg : Φ ∈ g).
    { unfold g, En_f1. apply AxiomII; split; [exact EΦ | split].
      - unfold f. apply AxiomII; split; [exact EΦ | split].
        + apply MKT26.
        + intros a b [Ha Hb]. exfalso. apply AxiomII in Ha as [_ Hc]. exact (Hc eq_refl).
      - rewrite (MKT17 N). unfold f.
        apply AxiomII; split; [exact EN | split; [exact HNA | exact HNest]]. }
    rewrite H0 in HΦg. exact (MKT16 HΦg). }
  destruct (Tukey g (conj HFset Hgne)) as [M HM].
  pose proof (HM Hgne) as [HMg HMmax].
  exists (M ∪ N).
  split.
  - unfold MaxMember. intros _.
    split.
    + pose proof HMg as HMg0.
      unfold g in HMg0. unfold En_f1 in HMg0.
      apply AxiomII in HMg0 as [_ [_ HMfN]].
      exact HMfN.
    + intros x Hxf Hproper.
      destruct Hproper as [Hsub Hne].
      pose proof Hxf as Hxf0.
      unfold f in Hxf0. apply AxiomII in Hxf0 as [Ex [HxA HxNest]].
      assert (HNx : N ⊂ x).
      { intros a Ha. apply Hsub. apply (proj1 (MKT4 M N a)). right. exact Ha. }
      assert (Hxg : x ∈ g).
      { unfold g, En_f1. apply AxiomII; split; [exact Ex | split].
        - unfold f. apply AxiomII; split; [exact Ex | split; [exact HxA | exact HxNest]].
        - rewrite (MKT6 x N). rewrite (proj2 (MKT29 N x) HNx). unfold f.
          apply AxiomII; split; [exact Ex | split; [exact HxA | exact HxNest]]. }
      assert (HMx : M ⊂ x).
      { intros a Ha. apply Hsub. apply (proj1 (MKT4 M N a)). left. exact Ha. }
      assert (HMne : M ≠ x).
      { intro HMx0.
        apply Hne.
        assert (HxMN : x ⊂ (M ∪ N)).
        { intros a Ha. rewrite <- HMx0 in Ha.
          apply (proj1 (MKT4 M N a)). left. exact Ha. }
        exact (proj1 (MKT27 (M ∪ N) x) (conj Hsub HxMN)). }
      exact (HMmax x Hxg (conj HMx HMne)).
  - intros a Ha. apply (proj1 (MKT4 M N a)). right. exact Ha.
Qed.


(** Maximal Principle **)

Theorem MaxPrinciple : forall (A: Class),
  Ensemble A ->
  (forall n, n⊂A /\ Nest n -> exists N, N∈A /\ (forall u, u∈n -> u⊂N))  ->
  exists M, MaxMember M A.
Proof.
  intros A HA Hbound.
  destruct (classic (A = Φ)) as [HAΦ | HAne].
  - exists Φ. unfold MaxMember. intros Hc. exfalso. exact (Hc HAΦ).
  - assert (HNestΦ : Nest Φ).
    { intros a b [Ha Hb]. exfalso. apply AxiomII in Ha as [_ Hc]. exact (Hc eq_refl). }
    destruct (Hausdorff A Φ HA (conj (MKT26 A) HNestΦ)) as [u [Hu HΦu]].
    assert (Hfne : \{ λ n, n ⊂ A /\ Nest n \} ≠ Φ).
    { intro H0.
      assert (HΦf : Φ ∈ \{ λ n, n ⊂ A /\ Nest n \}).
      { apply AxiomII; split.
        - apply (MKT33 A Φ HA). apply MKT26.
        - split; [apply MKT26 | exact HNestΦ]. }
      rewrite H0 in HΦf. exact (MKT16 HΦf). }
    pose proof (Hu Hfne) as [Huf Humax].
    apply AxiomII in Huf as [Eu [HuA HuNest]].
    destruct (Hbound u (conj HuA HuNest)) as [N [HNA HNabove]].
    exists N.
    unfold MaxMember. intros _.
    split; [exact HNA |].
    intros x HxA Hproper.
    destruct Hproper as [HNx HNne].
    assert (Ex : Ensemble x) by (unfold Ensemble; exists A; exact HxA).
    assert (Exs : Ensemble ([x])) by (apply MKT42; exact Ex).
    assert (Esing : x ∈ [x]) by (apply (proj2 (MKT41 x Ex x)); reflexivity).
    assert (Eux : Ensemble (u ∪ [x]))
      by (apply AxiomIV; [apply (MKT33 A u HA HuA) | exact Exs]).
    assert (HuxA : (u ∪ [x]) ⊂ A).
    { intros a Ha. apply (proj2 (MKT4 u ([x]) a)) in Ha.
      destruct Ha as [Hau | Has].
      - exact (HuA a Hau).
      - apply (proj1 (MKT41 x Ex a)) in Has. subst a. exact HxA. }
    assert (HuxNest : Nest (u ∪ [x])).
    { intros a b [Ha Hb].
      apply (proj2 (MKT4 u ([x]) a)) in Ha.
      apply (proj2 (MKT4 u ([x]) b)) in Hb.
      destruct Ha as [Hau | Has]; destruct Hb as [Hbu | Hbs].
      - exact (HuNest a b (conj Hau Hbu)).
      - apply (proj1 (MKT41 x Ex b)) in Hbs. subst b.
        left. exact (MKT28 (HNabove a Hau) HNx).
      - apply (proj1 (MKT41 x Ex a)) in Has. subst a.
        right. exact (MKT28 (HNabove b Hbu) HNx).
      - apply (proj1 (MKT41 x Ex a)) in Has.
        apply (proj1 (MKT41 x Ex b)) in Hbs.
        subst a. subst b. left. apply MKT26a. }
    assert (Hug : (u ∪ [x]) ∈ \{ λ n, n ⊂ A /\ Nest n \}).
    { apply AxiomII; split.
      - exact Eux.
      - split; [exact HuxA | exact HuxNest]. }
    assert (Huproper : ProperIncluded u (u ∪ [x])).
    { split.
      - intros a Ha. apply (proj1 (MKT4 u ([x]) a)). left. exact Ha.
      - intro Heq.
        assert (Hxu : x ∈ u).
        { rewrite Heq. apply (proj1 (MKT4 u ([x]) x)). right. exact Esing. }
        assert (HxN : x ⊂ N) by (exact (HNabove x Hxu)).
        assert (HxNeq : x = N) by (apply (proj1 (MKT27 x N)); split; assumption).
        exact (HNne (eq_sym HxNeq)). }
    exact (Humax (u ∪ [x]) Hug Huproper).
Qed.
