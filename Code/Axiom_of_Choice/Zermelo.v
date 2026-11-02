(***************************************************************************)
(*     This is part of AST_AC, it is distributed under the terms of the    *)
(*             GNU Lesser General Public License version 3                 *)
(*                (see file LICENSE for more details)                      *)
(*                                                                         *)
(*            Copyright 2025-2030: Tianyu Sun, Yaoshun Fu,                 *)
(*                Ce Zhang, Si Chen and Wensheng Yu.                       *)
(***************************************************************************)


Require Export Maximal_Principle.


(** Zermelo Postulate **)

Definition En_TB B A : Class :=
  \{ λ k, k ⊂ ∪A /\ (forall a, a ∈ (A ~ B) -> a ∩ k = Φ) /\
  (forall a, a ∈ B -> exists x, a ∩ k = [x]) \}.

Definition En_T A : Class :=
  \{ λ k, exists B, B ⊂ A /\ k ∈ (En_TB B A) \}.

Theorem Zermelo : forall A,
  Ensemble A -> Φ ∉ A ->
  (forall x y, x ∈ A /\ y ∈ A -> x ≠ y -> x ∩ y = Φ) ->
  (exists D, Ensemble D /\ (forall B, B ∈ A -> exists x, B ∩ D = [x])).
Proof.
  intros A HA HPhiA Hdisj.
  set (U := ∪A).
  assert (EU : Ensemble U) by (unfold U; apply AxiomVI; exact HA).
  set (f := \{ λ S, S ⊂ U /\ (∀ B, B ∈ A -> ∀ u, u ∈ S ∩ B -> ∀ v, v ∈ S ∩ B -> u = v) \}).
  assert (Ef : Ensemble f).
  { apply (MKT33 (pow(U)) f (MKT38a EU)).
    intros S HS. unfold f in HS.
    apply AxiomII in HS as [ES [HSU _]].
    apply AxiomII; split; [exact ES | exact HSU]. }
  assert (Efne : f ≠ Φ).
  { intro H0.
    assert (HPhi : Φ ∈ f).
    { unfold f. apply AxiomII; split.
      - exact (MKT33 U Φ EU (MKT26 U)).
      - split.
        + apply MKT26.
        + intros B HB u Hu.
          apply AxiomII in Hu as [Eu [HuP _]].
          exfalso. exact (MKT16 HuP). }
    rewrite H0 in HPhi. exact (MKT16 HPhi). }
  assert (Hbound : ∀ n, n ⊂ f /\ Nest n -> ∃ N, N ∈ f /\ (∀ u, u ∈ n -> u ⊂ N)).
  { intros n [Hnf Hnest].
    assert (En : Ensemble n) by (exact (MKT33 f n Ef Hnf)).
    exists (∪n). split.
    - unfold f. apply AxiomII; split.
      + exact (AxiomVI n En).
      + split.
        * intros s Hs.
          apply AxiomII in Hs as [Es [u [Hsu Hun]]].
          pose proof (Hnf u Hun) as Huf.
          unfold f in Huf. apply AxiomII in Huf as [_ [HuU _]].
          exact (HuU s Hsu).
        * intros B HB u Hu v Hv.
          apply AxiomII in Hu as [Eu [HuU HuB]].
          apply AxiomII in HuU as [_ [u1 [Huu1 Hu1n]]].
          apply AxiomII in Hv as [Ev [HvU HvB]].
          apply AxiomII in HvU as [_ [u2 [Hvv2 Hu2n]]].
          destruct (Hnest u1 u2 (conj Hu1n Hu2n)) as [H12 | H21].
          -- pose proof (Hnf u2 Hu2n) as Hu2f.
             unfold f in Hu2f. apply AxiomII in Hu2f as [_ [_ Hat]].
             assert (Hu' : u ∈ u2 ∩ B)
               by (apply AxiomII; split; [exact Eu | split; [exact (H12 u Huu1) | exact HuB]]).
             assert (Hv' : v ∈ u2 ∩ B)
               by (apply AxiomII; split; [exact Ev | split; [exact Hvv2 | exact HvB]]).
             exact (Hat B HB u Hu' v Hv').
          -- pose proof (Hnf u1 Hu1n) as Hu1f.
             unfold f in Hu1f. apply AxiomII in Hu1f as [_ [_ Hat]].
             assert (Hu' : u ∈ u1 ∩ B)
               by (apply AxiomII; split; [exact Eu | split; [exact Huu1 | exact HuB]]).
             assert (Hv' : v ∈ u1 ∩ B)
               by (apply AxiomII; split; [exact Ev | split; [exact (H21 v Hvv2) | exact HvB]]).
             exact (Hat B HB u Hu' v Hv').
    - intros u Hun. exact (proj1 (MKT32 u n Hun)). }
  destruct (MaxPrinciple f Ef Hbound) as [M HM].
  pose proof (HM Efne) as [HMf HMmax].
  unfold f in HMf.
  apply AxiomII in HMf as [EM [HMU HMat]].
  exists M. split; [exact EM |].
  intros B HB.
  assert (HBne : B ≠ Φ).
  { intro H0. apply HPhiA. rewrite <- H0. exact HB. }
  assert (Hne : B ∩ M ≠ Φ).
  { intro H0.
    destruct (MKT_nonempty B HBne) as [b HbB].
    assert (Eb : Ensemble b) by (unfold Ensemble; exists B; exact HbB).
    assert (HbnM : b ∉ M).
    { intro HbM.
      assert (Hin : b ∈ B ∩ M) by (apply AxiomII; split; [exact Eb | split; [exact HbB | exact HbM]]).
      rewrite H0 in Hin. exact (MKT16 Hin). }
    assert (Ebs : Ensemble ([b])) by (apply MKT42; exact Eb).
    set (M2 := M ∪ [b]).
    assert (EM2 : Ensemble M2) by (unfold M2; apply AxiomIV; [exact EM | exact Ebs]).
    assert (HM2 : M2 ∈ f).
    { unfold f. apply AxiomII; split; [exact EM2 | split].
      - intros s Hs.
        apply AxiomII in Hs as [Es [Hs1 | Hs2]].
        + exact (HMU s Hs1).
        + apply (proj1 (MKT41 b Eb s)) in Hs2. subst s.
          apply AxiomII; split; [exact Eb | exists B; split; [exact HbB | exact HB]].
      - intros C0 HC u Hu v Hv.
        assert (HuC : u ∈ C0) by (apply AxiomII in Hu as [_ [_ Hx]]; exact Hx).
        assert (HvC : v ∈ C0) by (apply AxiomII in Hv as [_ [_ Hx]]; exact Hx).
        destruct (classic (C0 = B)) as [HCB | HCB].
        + subst C0.
          assert (HuB : u = b).
          { apply AxiomII in Hu as [Eu [Hu1 Hu2]].
            apply AxiomII in Hu1 as [_ [HuM | Hub]].
            - exfalso.
              assert (Hin : u ∈ B ∩ M) by (apply AxiomII; split; [exact Eu | split; [exact Hu2 | exact HuM]]).
              rewrite H0 in Hin. exact (MKT16 Hin).
            - exact (proj1 (MKT41 b Eb u) Hub). }
          assert (HvB : v = b).
          { apply AxiomII in Hv as [Ev [Hv1 Hv2]].
            apply AxiomII in Hv1 as [_ [HvM | Hvb]].
            - exfalso.
              assert (Hin : v ∈ B ∩ M) by (apply AxiomII; split; [exact Ev | split; [exact Hv2 | exact HvM]]).
              rewrite H0 in Hin. exact (MKT16 Hin).
            - exact (proj1 (MKT41 b Eb v) Hvb). }
          rewrite HuB. rewrite HvB. reflexivity.
        + assert (HuM : u ∈ M).
          { apply AxiomII in Hu as [Eu [Hu1 Hu2]].
            apply AxiomII in Hu1 as [_ [HuM | Hub]]; [exact HuM |].
            exfalso.
            apply (proj1 (MKT41 b Eb u)) in Hub. subst u.
            assert (Hin : b ∈ B ∩ C0) by (apply AxiomII; split; [exact Eb | split; [exact HbB | exact Hu2]]).
            rewrite (Hdisj B C0 (conj HB HC) (fun Heq => HCB (eq_sym Heq))) in Hin. exact (MKT16 Hin). }
          assert (HvM : v ∈ M).
          { apply AxiomII in Hv as [Ev [Hv1 Hv2]].
            apply AxiomII in Hv1 as [_ [HvM | Hvb]]; [exact HvM |].
            exfalso.
            apply (proj1 (MKT41 b Eb v)) in Hvb. subst v.
            assert (Hin : b ∈ B ∩ C0) by (apply AxiomII; split; [exact Eb | split; [exact HbB | exact Hv2]]).
            rewrite (Hdisj B C0 (conj HB HC) (fun Heq => HCB (eq_sym Heq))) in Hin. exact (MKT16 Hin). }
          assert (HuMC : u ∈ M ∩ C0)
            by (apply AxiomII; split; [unfold Ensemble; exists M; exact HuM | split; [exact HuM | exact HuC]]).
          assert (HvMC : v ∈ M ∩ C0)
            by (apply AxiomII; split; [unfold Ensemble; exists M; exact HvM | split; [exact HvM | exact HvC]]).
          exact (HMat C0 HC u HuMC v HvMC). }
    assert (HbnM2 : b ∈ M2).
    { unfold M2. apply AxiomII; split; [exact Eb | right; apply (proj2 (MKT41 b Eb b)); reflexivity]. }
    assert (Hprop : M ⊊ M2).
    { unfold ProperIncluded. split.
      - intros s Hs. unfold M2. apply AxiomII; split; [unfold Ensemble; exists M; exact Hs | left; exact Hs].
      - intro Heq. apply HbnM. rewrite Heq. exact HbnM2. }
    exact (HMmax M2 HM2 Hprop). }
  destruct (MKT_nonempty (B ∩ M) Hne) as [b Hb].
  apply AxiomII in Hb as [Eb [HbB HbM]].
  exists b.
  apply AxiomI; intros z; split.
  - intros Hz.
    apply AxiomII in Hz as [Ez [HzB HzM]].
    assert (HzM' : z ∈ M ∩ B) by (apply AxiomII; split; [exact Ez | split; [exact HzM | exact HzB]]).
    assert (HbM' : b ∈ M ∩ B) by (apply AxiomII; split; [exact Eb | split; [exact HbM | exact HbB]]).
    apply (proj2 (MKT41 b Eb z)).
    exact (HMat B HB z HzM' b HbM').
  - intros Hz.
    apply (proj1 (MKT41 b Eb z)) in Hz. subst z.
    apply AxiomII; split; [exact Eb | split; [exact HbB | exact HbM]].
Qed.


(** The proof of AC **)

Definition En_p X : Class :=
  \{ λ z, exists A, A ∈ (pow(X)~[Φ]) /\ z = (A × [A]) \}.

Theorem Zermelo_AC : forall (X: Class),
  Ensemble X -> exists c, Choice_Function c X.
Proof.
  intros X HX.
  set (F := pow(X) ~ [Φ]).
  assert (EPhi : Ensemble Φ) by (apply (MKT33 X Φ HX (MKT26 X))).
  assert (EpowX : Ensemble (pow(X))) by (apply MKT38a; exact HX).
  assert (EF : Ensemble F).
  { apply (MKT33 (pow(X)) F EpowX).
    intros A HA. unfold F in HA.
    apply AxiomII in HA as [EA [HAp _]].
    apply AxiomII; split; [exact EA |].
    apply AxiomII in HAp as [_ HAsub]. exact HAsub. }
  assert (HFchar : ∀ A, A ∈ F <-> Ensemble A /\ A ⊂ X /\ A ∉ [Φ]).
  { intros A. unfold F. split.
    - intros H. apply AxiomII in H as [EA [H1 H2]].
      apply AxiomII in H1 as [_ H1']. apply AxiomII in H2 as [_ H2'].
      split; [exact EA | split; [exact H1' | exact H2']].
    - intros [EA [HAX HAn]]. apply AxiomII; split; [exact EA | split].
      + apply AxiomII; split; [exact EA | exact HAX].
      + apply AxiomII; split; [exact EA | exact HAn]. }
  assert (EA0 : Ensemble (En_p X)).
  { apply (MKT33 (pow(X × pow(X))) (En_p X) (MKT38a (MKT74 HX EpowX))).
    intros z Hz. unfold En_p in Hz.
    apply AxiomII in Hz as [Ez [A [HAF HzA]]].
    destruct (proj1 (HFchar A) HAF) as [EA [HAX HAn]].
    apply AxiomII; split; [exact Ez |].
    intros p Hp. rewrite HzA in Hp.
    apply AxiomII in Hp as [Ep [u [v [Hpuv [HuA HvA]]]]].
    apply AxiomII; split; [exact Ep |].
    exists u; exists v; split; [exact Hpuv | split; [exact (HAX u HuA) |]].
    assert (HvA' : v = A) by (exact (proj1 (MKT41 A EA v) HvA)).
    rewrite HvA'. apply AxiomII; split; [exact EA | exact HAX]. }
  assert (HPhiA0 : Φ ∉ (En_p X)).
  { intro H.
    apply AxiomII in H as [_ [A [HAF HzA]]].
    destruct (proj1 (HFchar A) HAF) as [EA [HAX HAn]].
    assert (HAne : A ≠ Φ).
    { intro HEq. apply HAn. rewrite HEq. apply (proj2 (MKT41 Φ EPhi Φ)); reflexivity. }
    destruct (MKT_nonempty A HAne) as [a Ha].
    assert (Ea : Ensemble a) by (unfold Ensemble; exists A; exact Ha).
    assert (Hin : [a,A] ∈ A × [A]).
    { apply AxiomII; split.
      - exact (MKT49a Ea EA).
      - exists a; exists A; split; [reflexivity | split; [exact Ha | apply (proj2 (MKT41 A EA A)); reflexivity]]. }
    rewrite <- HzA in Hin.
    exact (MKT16 Hin). }
  assert (Hmem0 : ∀ A, A ∈ F -> A × [A] ∈ En_p X).
  { intros A HAF. unfold En_p. apply AxiomII; split.
    - destruct (proj1 (HFchar A) HAF) as [EA _].
      apply MKT74; [exact EA | apply MKT42; exact EA].
    - exists A; split; [exact HAF | reflexivity]. }
  assert (Hdisj0 : ∀ S T, S ∈ En_p X /\ T ∈ En_p X -> S ≠ T -> S ∩ T = Φ).
  { intros S T [HS HT] Hne.
    unfold En_p in HS, HT.
    apply AxiomII in HS as [_ [A [HAF HSA]]].
    apply AxiomII in HT as [_ [B [HBF HTB]]].
    destruct (proj1 (HFchar A) HAF) as [EA [HAX HAn]].
    destruct (proj1 (HFchar B) HBF) as [EB [HBX HBn]].
    assert (HAB : A ≠ B).
    { intro HEq. apply Hne. rewrite HSA. rewrite HTB. rewrite HEq. reflexivity. }
    apply AxiomI; intros p; split.
    - intros Hp. apply AxiomII in Hp as [_ [HpS HpT]].
      exfalso.
      rewrite HSA in HpS. rewrite HTB in HpT.
      apply AxiomII in HpS as [_ [u [v [Hpuv [HuA HvA]]]]].
      apply AxiomII in HpT as [_ [u' [v' [Hpuv' [Hu'B Hv'B]]]]].
      assert (Eu : Ensemble u) by (unfold Ensemble; exists A; exact HuA).
      assert (Ev : Ensemble v) by (unfold Ensemble; exists ([A]); exact HvA).
      assert (Huv_eq : [u,v] = [u',v']) by (rewrite <- Hpuv; rewrite <- Hpuv'; reflexivity).
      destruct (proj1 (MKT55 u v u' v' Eu Ev) Huv_eq) as [_ Hvv'].
      assert (HvA' : v = A) by (exact (proj1 (MKT41 A EA v) HvA)).
      assert (Hv'B' : v' = B) by (exact (proj1 (MKT41 B EB v') Hv'B)).
      apply HAB. rewrite <- HvA'. rewrite <- Hv'B'. rewrite Hvv'. reflexivity.
    - intros Hp. exfalso. exact (MKT16 Hp). }
  destruct (Zermelo (En_p X) EA0 HPhiA0 Hdisj0) as [D [ED HD]].
  assert (Hens : ∀ A x, A ∈ F -> (A × [A]) ∩ D = [x] -> Ensemble x).
  { intros A x HAF Hx.
    assert (Einter : Ensemble ((A × [A]) ∩ D)).
    { apply (MKT33 D _ ED). intros p Hp. apply AxiomII in Hp as [_ [_ HpD]]. exact HpD. }
    apply MKT42'. rewrite <- Hx. exact Einter. }
  assert (Hpick : ∀ A, A ∈ F -> ∃ a, a ∈ A /\ [a,A] ∈ D).
  { intros A HAF.
    destruct (proj1 (HFchar A) HAF) as [EA [HAX HAn]].
    destruct (HD (A × [A]) (Hmem0 A HAF)) as [x Hx].
    assert (Ex : Ensemble x) by (exact (Hens A x HAF Hx)).
    assert (Hxin : x ∈ (A × [A]) ∩ D).
    { rewrite Hx. apply (proj2 (MKT41 x Ex x)); reflexivity. }
    apply AxiomII in Hxin as [_ [HxS HxD]].
    apply AxiomII in HxS as [_ [u [v [Hxuv [HuA HvA]]]]].
    assert (HvA' : v = A) by (exact (proj1 (MKT41 A EA v) HvA)).
    exists u. split; [exact HuA |].
    rewrite <- HvA'. rewrite <- Hxuv. exact HxD. }
  assert (Hselx : ∀ A a x, A ∈ F -> a ∈ A -> [a,A] ∈ D
    -> (A × [A]) ∩ D = [x] -> [a,A] = x).
  { intros A a x HAF HaA HaD Hx.
    destruct (proj1 (HFchar A) HAF) as [EA [HAX HAn]].
    assert (Ex : Ensemble x) by (exact (Hens A x HAF Hx)).
    assert (Ea : Ensemble a) by (unfold Ensemble; exists A; exact HaA).
    assert (Hin : [a,A] ∈ A × [A]).
    { apply AxiomII; split.
      - exact (MKT49a Ea EA).
      - exists a; exists A; split; [reflexivity | split; [exact HaA | apply (proj2 (MKT41 A EA A)); reflexivity]]. }
    assert (Hin2 : [a,A] ∈ (A × [A]) ∩ D).
    { apply AxiomII; split; [exact (MKT49a Ea EA) | split; [exact Hin | exact HaD]]. }
    rewrite Hx in Hin2.
    exact (proj1 (MKT41 x Ex ([a,A])) Hin2). }
  set (c := \{ λ z, ∃ A a, z = [A,a] /\ A ∈ F /\ [a,A] ∈ D /\ a ∈ A \}).
  assert (Hcchar : ∀ A a,
    [A,a] ∈ c <-> Ensemble ([A,a]) /\ A ∈ F /\ [a,A] ∈ D /\ a ∈ A).
  { intros A a. unfold c. split.
    - intros H. apply AxiomII in H as [E H].
      destruct H as [A' [a' [Hz [HAF [HaD HaA]]]]].
      assert (E' : Ensemble ([A',a'])) by (rewrite <- Hz; exact E).
      destruct (MKT49b A a E) as [EAa Eaa].
      destruct (MKT49b A' a' E') as [_ _].
      destruct (proj1 (MKT55 A a A' a' EAa Eaa) Hz) as [HAA' Haa'].
      subst A'. subst a'.
      split; [exact E | split; [exact HAF | split; [exact HaD | exact HaA]]].
    - intros [E [HAF [HaD HaA]]]. apply AxiomII; split; [exact E |].
      exists A; exists a; split; [reflexivity | split; [exact HAF | split; [exact HaD | exact HaA]]]. }
  assert (Hc1 : ∀ A a, [A,a] ∈ c -> A ∈ F /\ a ∈ A /\ [a,A] ∈ D).
  { intros A a H. destruct (proj1 (Hcchar A a) H) as [_ [HAF [HaD HaA]]].
    split; [exact HAF | split; [exact HaA | exact HaD]]. }
  assert (Hc2 : ∀ A a, Ensemble ([A,a]) -> A ∈ F -> a ∈ A -> [a,A] ∈ D -> [A,a] ∈ c).
  { intros A a E HAF HaA HaD. apply (proj2 (Hcchar A a)).
    split; [exact E | split; [exact HAF | split; [exact HaD | exact HaA]]]. }
  assert (Hcfunc : Function c).
  { split.
    - intros z Hz. unfold c in Hz. apply AxiomII in Hz as [_ [A [a [HzA _]]]].
      exists A; exists a; exact HzA.
    - intros A a1 a2 H1 H2.
      destruct (proj1 (Hcchar A a1) H1) as [_ [HAF [Ha1D Ha1A]]].
      destruct (proj1 (Hcchar A a2) H2) as [_ [_ [Ha2D Ha2A]]].
      destruct (proj1 (HFchar A) HAF) as [EA [HAX HAn]].
      destruct (HD (A × [A]) (Hmem0 A HAF)) as [x Hx].
      assert (H1x : [a1,A] = x) by (exact (Hselx A a1 x HAF Ha1A Ha1D Hx)).
      assert (H2x : [a2,A] = x) by (exact (Hselx A a2 x HAF Ha2A Ha2D Hx)).
      assert (Ea1 : Ensemble a1) by (unfold Ensemble; exists A; exact Ha1A).
      assert (Ea2 : Ensemble a2) by (unfold Ensemble; exists A; exact Ha2A).
      assert (Heq : [a1,A] = [a2,A]) by (rewrite H1x; rewrite H2x; reflexivity).
      exact (proj1 (proj1 (MKT55 a1 A a2 A Ea1 EA) Heq)). }
  assert (Hdom : dom(c) = F).
  { apply AxiomI; intros A; split.
    - intros HA. apply AxiomII in HA as [_ [a Ha]]. exact (proj1 (Hc1 A a Ha)).
    - intros HAF.
      assert (EA : Ensemble A) by (exact (proj1 (proj1 (HFchar A) HAF))).
      destruct (Hpick A HAF) as [a [HaA HaD]].
      assert (Ea : Ensemble a) by (unfold Ensemble; exists A; exact HaA).
      apply AxiomII; split; [exact EA |].
      exists a. exact (Hc2 A a (MKT49a EA Ea) HAF HaA HaD). }
  assert (Hran : ran(c) ⊂ X).
  { intros y Hy. apply AxiomII in Hy as [_ [A Ha]].
    destruct (Hc1 A y Ha) as [HAF [HyA HyD]].
    destruct (proj1 (HFchar A) HAF) as [_ [HAX _]].
    exact (HAX y HyA). }
  assert (Hchoice : ∀ A, A ∈ dom(c) -> c[A] ∈ A).
  { intros A HA. apply AxiomII in HA as [_ [a Ha]].
    destruct (Hc1 A a Ha) as [_ [HaA _]].
    assert (Hfa : c[A] = a) by (apply (MKT_fval c A a Hcfunc); exact Ha).
    rewrite Hfa. exact HaA. }
  exists c. unfold Choice_Function.
  split; [exact Hcfunc | split; [exact Hran | split; [exact Hdom | exact Hchoice]]].
Qed.
