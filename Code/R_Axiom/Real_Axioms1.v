(**********************************************************************)
(*  This is part of Real_A, it is distributed under the terms of the  *)
(*          GNU Lesser General Public License version 3               *)
(*             (see file LICENSE for more details)                    *)
(*                                                                    *)
(*                     Copyright 2023-2028                            *)
(*    Dakai Guo, Si Chen, Guowei Dou, Shukun Leng and Wensheng Yu     *)
(**********************************************************************)

(** Real_Axioms1 *)

(*基于MK集论，根据Zorich的《数学分析》定义了实数结构和实数公理系统，
  并验证了实数公理系统的诸多性质 *)
Require Export MK.

Declare Scope RR_scope.
Delimit Scope RR_scope with Rr.
Open Scope RR_scope.

Check @Class MKS.

Class Real_struct := {
  R : @Class MKS;
  fp : @Class MKS;
  zeroR : @Class MKS;
  fm : @Class MKS;
  oneR : @Class MKS;
  Leq : @Class MKS; }.

Notation "x + y" := (fp[[x, y]]) : RR_scope.
Notation "0" := zeroR : RR_scope.
Notation "x · y" := (fm[[x, y]])(at level 10) : RR_scope.
Notation "1" := oneR  : RR_scope.
Notation "x ≤ y" := ([x, y] ∈ Leq)(at level 77) : RR_scope.
Notation "- a" := (∩(\{ λ u, u ∈ R /\ u + a = 0 \})) : RR_scope.
Notation "x - y" := (x + (-y)) : RR_scope.
Notation "a ⁻" := (∩(\{ λ u, u ∈ (R ~ [0]) /\ u · a = 1 \})) 
  (at level 5) : RR_scope.
Notation "m / n" := (m · (n⁻)) : RR_scope.

Definition lt {a:Real_struct} (x y:Class) := x ≤ y /\ x <> y.

Notation "x < y" := (@lt _ x y) : RR_scope.

Class Real_axioms (RR : Real_struct):= {
  Ensemble_R : Ensemble R;
  PlusR : (Function fp) /\ (dom(fp) = R × R) /\ (ran(fp) ⊂ R);
  zero_in_R : 0 ∈ R;
  Plus_P1 : ∀ x, x ∈ R -> x + 0 = x;
  Plus_P2 : ∀ x, x ∈ R -> ∃ y, y ∈ R /\ x + y = 0;
  Plus_P3 : ∀ x y z, x ∈ R -> y ∈ R -> z ∈ R -> x + (y + z) = (x + y) + z;
  Plus_P4 : ∀ x y, x ∈ R -> y ∈ R -> x + y = y + x;
  MultR : (Function fm) /\ (dom(fm) = R × R) /\ (ran(fm) ⊂ R);
  one_in_R : 1 ∈ (R ~ [0]);
  Mult_P1 : ∀ x, x ∈ R -> x · 1 = x;
  Mult_P2 : ∀ x, x ∈ (R ~ [0]) -> ∃ y, y ∈ (R ~ [0]) /\ x · y = 1;
  Mult_P3 : ∀ x y z, x ∈ R -> y ∈ R -> z ∈ R -> x · (y · z) = (x · y) · z;
  Mult_P4 : ∀ x y, x ∈ R -> y ∈ R -> x · y = y · x;
  Mult_P5 : ∀ x y z, x ∈ R -> y ∈ R -> z ∈ R 
    -> (x + y) · z = (x · z) + (y · z);
  LeqR : Leq ⊂ R × R;
  Leq_P1 : ∀ x, x ∈ R -> x ≤ x;
  Leq_P2 : ∀ x y, x ∈ R -> y ∈ R -> x ≤ y -> y ≤ x -> x = y;
  Leq_P3 : ∀ x y z, x ∈ R -> y ∈ R -> z ∈ R -> x ≤ y -> y ≤ z -> x ≤ z;
  Leq_P4 : ∀ x y, x ∈ R -> y ∈ R -> x ≤ y \/ y ≤ x;
  Plus_Leq : ∀ x y z, x ∈ R -> y ∈ R -> z ∈ R -> x ≤ y -> x + z ≤ y + z;
  Mult_Leq : ∀ x y, x ∈ R -> y ∈ R -> 0 ≤ x -> 0 ≤ y -> 0 ≤ x · y;
  Completeness : ∀ X Y, X ⊂ R -> Y ⊂ R -> X <> Φ -> Y <> Φ
    -> (∀ x y, x ∈ X -> y ∈ Y -> x ≤ y) -> ∃ c, c ∈ R
    /\ (∀ x y, x ∈ X -> y ∈ Y -> (x ≤ c /\ c ≤ y)); }.

Section R1_reals.

Variable RR : Real_struct.
Variable R1 : Real_axioms RR.

Corollary Plus_close : ∀ x y, x ∈ R -> y ∈ R -> (x + y) ∈ R.
Proof.
  intros x y Hx Hy.
  assert (mu_notin_R : μ ∉ R).
  { intro Hmu.
    assert (Hin : [μ, μ] ∈ R × R) by (exact (LeqR ([μ, μ]) (Leq_P1 μ Hmu))).
    unfold Cartesian in Hin.
    apply AxiomII in Hin as [E _].
    exact (MKT39 (proj1 (MKT49b μ μ E))). }
  assert (Rens : ∀ z, z ∈ R -> Ensemble z).
  { intros z Hz.
    destruct (Plus_P2 z Hz) as [a [HaR Hsum]].
    assert (Hzadom : [z, a] ∈ dom(fp)).
    { destruct (classic ([z, a] ∈ dom(fp))) as [H | H]; [exact H |].
      exfalso.
      assert (Hmu : fp[[z, a]] = μ) by (apply (MKT69a (x:=[z,a]) (f:=fp)); exact H).
      assert (H0mu : 0 = μ) by (exact (eq_trans (eq_sym Hsum) Hmu)).
      assert (H0R : 0 ∈ R) by (apply zero_in_R).
      apply mu_notin_R. rewrite <- H0mu. exact H0R. }
    unfold Domain in Hzadom.
    apply AxiomII in Hzadom as [E _].
    exact (proj1 (MKT49b z a E)). }
  destruct PlusR as [Hf [Hdom Hran]].
  assert (Ex : Ensemble x) by (apply Rens; exact Hx).
  assert (Ey : Ensemble y) by (apply Rens; exact Hy).
  assert (Hxy : [x, y] ∈ R × R).
  { apply AxiomII; split.
    - apply MKT49a; assumption.
    - exists x, y; split; [reflexivity | split; assumption]. }
  assert (Hxydom : [x, y] ∈ dom(fp)) by (rewrite Hdom; exact Hxy).
  assert (Hval : [[x, y], x + y] ∈ fp) by (apply (MKT_dom_val fp ([x, y]) Hf Hxydom)).
  assert (Eval : Ensemble (x + y)) by (apply MKT19a; apply (MKT69b (x:=[x,y]) (f:=fp) Hxydom)).
  apply Hran.
  apply AxiomII; split.
  - exact Eval.
  - exists ([x, y]). exact Hval.
Qed.

Corollary Mult_close : ∀ x y, x ∈ R -> y ∈ R -> (x · y) ∈ R.
Proof.
  intros x y Hx Hy.
  assert (mu_notin_R : μ ∉ R).
  { intro Hmu.
    assert (Hin : [μ, μ] ∈ R × R) by (exact (LeqR ([μ, μ]) (Leq_P1 μ Hmu))).
    unfold Cartesian in Hin.
    apply AxiomII in Hin as [E _].
    exact (MKT39 (proj1 (MKT49b μ μ E))). }
  assert (Rens : ∀ z, z ∈ R -> Ensemble z).
  { intros z Hz.
    destruct (Plus_P2 z Hz) as [a [HaR Hsum]].
    assert (Hzadom : [z, a] ∈ dom(fp)).
    { destruct (classic ([z, a] ∈ dom(fp))) as [H | H]; [exact H |].
      exfalso.
      assert (Hmu : fp[[z, a]] = μ) by (apply (MKT69a (x:=[z,a]) (f:=fp)); exact H).
      assert (H0mu : 0 = μ) by (exact (eq_trans (eq_sym Hsum) Hmu)).
      assert (H0R : 0 ∈ R) by (apply zero_in_R).
      apply mu_notin_R. rewrite <- H0mu. exact H0R. }
    unfold Domain in Hzadom.
    apply AxiomII in Hzadom as [E _].
    exact (proj1 (MKT49b z a E)). }
  destruct MultR as [Hf [Hdom Hran]].
  assert (Ex : Ensemble x) by (apply Rens; exact Hx).
  assert (Ey : Ensemble y) by (apply Rens; exact Hy).
  assert (Hxy : [x, y] ∈ R × R).
  { apply AxiomII; split.
    - apply MKT49a; assumption.
    - exists x, y; split; [reflexivity | split; assumption]. }
  assert (Hxydom : [x, y] ∈ dom(fm)) by (rewrite Hdom; exact Hxy).
  assert (Hval : [[x, y], x · y] ∈ fm) by (apply (MKT_dom_val fm ([x, y]) Hf Hxydom)).
  assert (Eval : Ensemble (x · y)) by (apply MKT19a; apply (MKT69b (x:=[x,y]) (f:=fm) Hxydom)).
  apply Hran.
  apply AxiomII; split.
  - exact Eval.
  - exists ([x, y]). exact Hval.
Qed.

Corollary one_in_R_Co : 1 ∈ R.
Proof.
  pose proof one_in_R as Hin.
  unfold Setminus in Hin.
  apply AxiomII in Hin as [E [H1R _]].
  exact H1R.
Qed.

(* 推论 加法公理的推论 *)
Corollary Plus_Co1 : ∀ x, x ∈ R -> (∀ y, y ∈ R -> y + x = y) -> x = 0.
Proof.
  intros x Hx H.
  assert (H0 : 0 ∈ R) by (apply zero_in_R).
  assert (Hx0 : x + 0 = x) by (exact (Plus_P1 x Hx)).
  assert (H0x : 0 + x = 0) by (exact (H 0 H0)).
  assert (Hcomm : x + 0 = 0 + x) by (exact (Plus_P4 x 0 Hx H0)).
  rewrite <- Hx0. rewrite Hcomm. exact H0x.
Qed.

Corollary Plus_Co2 : ∀ x, x ∈ R -> (exists ! x0, x0 ∈ R /\ x + x0 = 0).
Proof.
  intros x Hx.
  destruct (Plus_P2 x Hx) as [y [HyR Hy0]].
  exists y. split; [split; assumption |].
  intros z [HzR Hz0].
  assert (H0 : 0 ∈ R) by (apply zero_in_R).
  assert (H0z : 0 + z = z) by (exact (eq_trans (Plus_P4 0 z H0 HzR) (Plus_P1 z HzR))).
  rewrite <- (Plus_P1 y HyR). rewrite <- Hz0. rewrite (Plus_P3 y x z HyR Hx HzR).
  rewrite (Plus_P4 y x HyR Hx). rewrite Hy0. exact H0z.
Qed.

Corollary Plus_neg1a : ∀ a, a ∈ R -> (-a) ∈ R.
Proof.
  intros a Ha.
  assert (mu_notin_R : μ ∉ R).
  { intro Hmu.
    assert (Hin : [μ, μ] ∈ R × R) by (exact (LeqR ([μ, μ]) (Leq_P1 μ Hmu))).
    unfold Cartesian in Hin.
    apply AxiomII in Hin as [E _].
    exact (MKT39 (proj1 (MKT49b μ μ E))). }
  assert (Rens : ∀ z, z ∈ R -> Ensemble z).
  { intros z Hz.
    destruct (Plus_P2 z Hz) as [a0 [Ha0R Hsum]].
    assert (Hzadom : [z, a0] ∈ dom(fp)).
    { destruct (classic ([z, a0] ∈ dom(fp))) as [H | H]; [exact H |].
      exfalso.
      assert (Hmu : fp[[z, a0]] = μ) by (apply (MKT69a (x:=[z,a0]) (f:=fp)); exact H).
      assert (H0mu : 0 = μ) by (exact (eq_trans (eq_sym Hsum) Hmu)).
      assert (H0R : 0 ∈ R) by (apply zero_in_R).
      apply mu_notin_R. rewrite <- H0mu. exact H0R. }
    unfold Domain in Hzadom.
    apply AxiomII in Hzadom as [E _].
    exact (proj1 (MKT49b z a0 E)). }
  destruct (Plus_Co2 a Ha) as [x0 [[Hx0R Hx0sum] Huniq]].
  assert (Hx0a : x0 + a = 0) by (exact (eq_trans (Plus_P4 x0 a Hx0R Ha) Hx0sum)).
  assert (Ex0 : Ensemble x0) by (apply Rens; exact Hx0R).
  assert (HS : \{ λ u, u ∈ R /\ u + a = 0 \} = [x0]).
  { apply AxiomI; intros z; split; intros Hz.
    - apply AxiomII in Hz as [Ez [HzR Hza]].
      assert (Haz : a + z = 0) by (exact (eq_trans (Plus_P4 a z Ha HzR) Hza)).
      assert (Hzx0 : z = x0) by (exact (eq_sym (Huniq z (conj HzR Haz)))).
      exact (proj2 (MKT41 x0 Ex0 z) Hzx0).
    - apply (proj1 (MKT41 x0 Ex0 z)) in Hz.
      apply AxiomII; split.
      + rewrite Hz. exact Ex0.
      + split; [rewrite Hz; exact Hx0R | rewrite Hz; exact Hx0a]. }
  assert (Hneg : (-a) = x0).
  { change (∩(\{ λ u, u ∈ R /\ u + a = 0 \}) = x0).
    rewrite HS. exact (proj1 (MKT44 Ex0)). }
  rewrite Hneg. exact Hx0R.
Qed.

Corollary Plus_neg1b : ∀ a, (-a) ∈ R -> a ∈ R.
Proof.
  intros a Hc.
  assert (mu_notin_R : μ ∉ R).
  { intro Hmu.
    assert (Hin : [μ, μ] ∈ R × R) by (exact (LeqR ([μ, μ]) (Leq_P1 μ Hmu))).
    unfold Cartesian in Hin.
    apply AxiomII in Hin as [E _].
    exact (MKT39 (proj1 (MKT49b μ μ E))). }
  assert (Rens : ∀ z, z ∈ R -> Ensemble z).
  { intros z Hz.
    destruct (Plus_P2 z Hz) as [a0 [Ha0R Hsum]].
    assert (Hzadom : [z, a0] ∈ dom(fp)).
    { destruct (classic ([z, a0] ∈ dom(fp))) as [H | H]; [exact H |].
      exfalso.
      assert (Hmu : fp[[z, a0]] = μ) by (apply (MKT69a (x:=[z,a0]) (f:=fp)); exact H).
      assert (H0mu : 0 = μ) by (exact (eq_trans (eq_sym Hsum) Hmu)).
      assert (H0R : 0 ∈ R) by (apply zero_in_R).
      apply mu_notin_R. rewrite <- H0mu. exact H0R. }
    unfold Domain in Hzadom.
    apply AxiomII in Hzadom as [E _].
    exact (proj1 (MKT49b z a0 E)). }
  destruct PlusR as [Hf [Hdom Hran]].
  apply NNPP; intro Hna.
  assert (HS : \{ λ u, u ∈ R /\ u + a = 0 \} = Φ).
  { apply AxiomI; intros u; split; intros Hu.
    - exfalso.
      apply AxiomII in Hu as [_ [HuR Hua]].
      assert (Hud : [u, a] ∈ dom(fp)).
      { destruct (classic ([u, a] ∈ dom(fp))) as [Hd | Hd]; [exact Hd |].
        exfalso.
        assert (Hmu : fp[[u, a]] = μ) by (apply (MKT69a (x:=[u,a]) (f:=fp)); exact Hd).
        assert (H0mu : 0 = μ) by (exact (eq_trans (eq_sym Hua) Hmu)).
        assert (H0R : 0 ∈ R) by (apply zero_in_R).
        apply mu_notin_R. rewrite <- H0mu. exact H0R. }
      assert (Hin : [u, a] ∈ R × R) by (rewrite <- Hdom; exact Hud).
      unfold Cartesian in Hin.
      apply AxiomII in Hin as [Euva [u' [a' [Heq [Hu'R Ha'R]]]]].
      assert (Eu : Ensemble u) by (exact (proj1 (MKT49b u a Euva))).
      assert (Ea : Ensemble a) by (exact (proj2 (MKT49b u a Euva))).
      assert (Ha_eq : a = a') by (exact (proj2 (proj1 (MKT55 u a u' a' Eu Ea) Heq))).
      apply Hna. rewrite Ha_eq. exact Ha'R.
    - exfalso. exact (MKT16 Hu). }
  assert (Hcmu : ∩(\{ λ u, u ∈ R /\ u + a = 0 \}) = μ) by (rewrite HS; exact MKT24).
  apply mu_notin_R. rewrite <- Hcmu. exact Hc.
Qed.

Corollary Plus_neg2 : ∀ a, a ∈ R -> a + (-a) = 0.
Proof.
  intros a Ha.
  assert (mu_notin_R : μ ∉ R).
  { intro Hmu.
    assert (Hin : [μ, μ] ∈ R × R) by (exact (LeqR ([μ, μ]) (Leq_P1 μ Hmu))).
    unfold Cartesian in Hin.
    apply AxiomII in Hin as [E _].
    exact (MKT39 (proj1 (MKT49b μ μ E))). }
  assert (Rens : ∀ z, z ∈ R -> Ensemble z).
  { intros z Hz.
    destruct (Plus_P2 z Hz) as [a0 [Ha0R Hsum]].
    assert (Hzadom : [z, a0] ∈ dom(fp)).
    { destruct (classic ([z, a0] ∈ dom(fp))) as [H | H]; [exact H |].
      exfalso.
      assert (Hmu : fp[[z, a0]] = μ) by (apply (MKT69a (x:=[z,a0]) (f:=fp)); exact H).
      assert (H0mu : 0 = μ) by (exact (eq_trans (eq_sym Hsum) Hmu)).
      assert (H0R : 0 ∈ R) by (apply zero_in_R).
      apply mu_notin_R. rewrite <- H0mu. exact H0R. }
    unfold Domain in Hzadom.
    apply AxiomII in Hzadom as [E _].
    exact (proj1 (MKT49b z a0 E)). }
  destruct (Plus_Co2 a Ha) as [x0 [[Hx0R Hx0sum] Huniq]].
  assert (Hx0a : x0 + a = 0) by (exact (eq_trans (Plus_P4 x0 a Hx0R Ha) Hx0sum)).
  assert (Ex0 : Ensemble x0) by (apply Rens; exact Hx0R).
  assert (HS : \{ λ u, u ∈ R /\ u + a = 0 \} = [x0]).
  { apply AxiomI; intros z; split; intros Hz.
    - apply AxiomII in Hz as [Ez [HzR Hza]].
      assert (Haz : a + z = 0) by (exact (eq_trans (Plus_P4 a z Ha HzR) Hza)).
      assert (Hzx0 : z = x0) by (exact (eq_sym (Huniq z (conj HzR Haz)))).
      exact (proj2 (MKT41 x0 Ex0 z) Hzx0).
    - apply (proj1 (MKT41 x0 Ex0 z)) in Hz.
      apply AxiomII; split.
      + rewrite Hz. exact Ex0.
      + split; [rewrite Hz; exact Hx0R | rewrite Hz; exact Hx0a]. }
  assert (Hneg : (-a) = x0).
  { change (∩(\{ λ u, u ∈ R /\ u + a = 0 \}) = x0).
    rewrite HS. exact (proj1 (MKT44 Ex0)). }
  rewrite Hneg. exact Hx0sum.
Qed.

Corollary Minus_P1 : ∀ a, a ∈ R -> a - a = 0.
Proof.
  intros a Ha. exact (Plus_neg2 a Ha).
Qed.

Corollary Minus_P2 : ∀ a, a ∈ R -> a - 0 = a.
Proof.
  intros a Ha.
  assert (H0 : 0 ∈ R) by (apply zero_in_R).
  assert (Hneg0 : -0 ∈ R) by (apply (Plus_neg1a 0 H0)).
  assert (Hneg00 : -0 = 0).
  { assert (H1 : 0 + 0 = 0) by (apply (Plus_P1 0 H0)).
    assert (H2 : 0 + (-0) = 0) by (apply (Plus_neg2 0 H0)).
    destruct (Plus_Co2 0 H0) as [x0 [[_ _] Huniq]].
    assert (He1 : -0 = x0) by (exact (eq_sym (Huniq (-0) (conj Hneg0 H2)))).
    transitivity x0.
    - exact He1.
    - exact (Huniq 0 (conj H0 H1)). }
  rewrite Hneg00. apply (Plus_P1 a Ha).
Qed.

Corollary Plus_Co3 : ∀ a x b, a ∈ R -> x ∈ R -> b ∈ R -> a + x = b
  -> x = b + (-a).
Proof.
  intros a x b Ha Hx Hb Hab.
  assert (H0 : 0 ∈ R) by (apply zero_in_R).
  assert (Hnega : -a ∈ R) by (apply (Plus_neg1a a Ha)).
  assert (Hchain : b + (-a) = x).
  { transitivity ((a + x) + (-a)).
    - rewrite <- Hab. reflexivity.
    - transitivity (a + (x + (-a))).
      + symmetry. apply (Plus_P3 a x (-a) Ha Hx Hnega).
      + transitivity (a + ((-a) + x)).
        * rewrite (Plus_P4 x (-a) Hx Hnega). reflexivity.
        * transitivity ((a + (-a)) + x).
          -- apply (Plus_P3 a (-a) x Ha Hnega Hx).
          -- transitivity (0 + x).
             ++ rewrite (Plus_neg2 a Ha). reflexivity.
             ++ exact (eq_trans (eq_sym (Plus_P4 x 0 Hx H0)) (Plus_P1 x Hx)). }
  symmetry. exact Hchain.
Qed.

(* 推论 乘法公理的推论 *)
Corollary Mult_Co1 : ∀ x, x ∈ (R ~ [0]) -> (∀ y, y ∈ R -> y · x = y) -> x = 1.
Proof.
  intros x Hx H.
  assert (H1R : 1 ∈ R) by (apply one_in_R_Co).
  assert (HxR : x ∈ R).
  { pose proof Hx as Hx'. unfold Setminus in Hx'. apply AxiomII in Hx' as [Ex [HxR _]]. exact HxR. }
  assert (H1x : 1 · x = 1) by (apply H; exact H1R).
  assert (Hcomm : 1 · x = x · 1) by (apply Mult_P4; assumption).
  assert (Hx1 : x · 1 = x) by (apply Mult_P1; exact HxR).
  rewrite Hcomm in H1x. rewrite Hx1 in H1x. exact H1x.
Qed.

Corollary Mult_Co2 : ∀ x, x ∈ (R ~ [0])
  -> (exists ! x0, x0 ∈ (R ~ [0]) /\ x · x0 = 1).
Proof.
  intros x Hx.
  destruct (Mult_P2 x Hx) as [y [Hy Hy1]].
  exists y. split; [split; assumption |].
  intros z [Hz Hz1].
  assert (H1R : 1 ∈ R) by (apply one_in_R_Co).
  assert (HxR : x ∈ R).
  { pose proof Hx as Hx'. unfold Setminus in Hx'. apply AxiomII in Hx' as [Ex [HxR _]]. exact HxR. }
  assert (HyR : y ∈ R).
  { pose proof Hy as Hy'. unfold Setminus in Hy'. apply AxiomII in Hy' as [Ey [HyR _]]. exact HyR. }
  assert (HzR : z ∈ R).
  { pose proof Hz as Hz'. unfold Setminus in Hz'. apply AxiomII in Hz' as [Ez [HzR _]]. exact HzR. }
  assert (H1z : 1 · z = z) by
    (exact (eq_trans (eq_sym (Mult_P4 z 1 HzR H1R)) (Mult_P1 z HzR))).
  rewrite <- (Mult_P1 y HyR). rewrite <- Hz1. rewrite (Mult_P3 y x z HyR HxR HzR).
  rewrite (Mult_P4 y x HyR HxR). rewrite Hy1. exact H1z.
Qed.

Corollary Mult_inv1 : ∀ a, a ∈ (R ~ [0]) -> (a⁻) ∈ (R ~ [0]).
Proof.
  intros a Ha.
  destruct (Mult_Co2 a Ha) as [x0 [[Hx0 Hx0sum] Huniq]].
  assert (HaR : a ∈ R).
  { pose proof Ha as Ha'. unfold Setminus in Ha'. apply AxiomII in Ha' as [Ea [HaR _]]. exact HaR. }
  assert (Hx0R : x0 ∈ R).
  { pose proof Hx0 as Hx0'. unfold Setminus in Hx0'. apply AxiomII in Hx0' as [Ex0 [Hx0R _]]. exact Hx0R. }
  assert (Ex0 : Ensemble x0).
  { pose proof Hx0 as Hx0'. unfold Setminus in Hx0'. apply AxiomII in Hx0' as [Ex0 _]. exact Ex0. }
  assert (Hx0a : x0 · a = 1) by (exact (eq_trans (Mult_P4 x0 a Hx0R HaR) Hx0sum)).
  assert (HS : \{ λ u, u ∈ (R ~ [0]) /\ u · a = 1 \} = [x0]).
  { apply AxiomI; intros z; split; intros Hz.
    - apply AxiomII in Hz as [Ez [Hz0 Hza]].
      assert (HzR : z ∈ R).
      { pose proof Hz0 as Hz0'. unfold Setminus in Hz0'. apply AxiomII in Hz0' as [Ez' [HzR _]]. exact HzR. }
      assert (Haz : a · z = 1) by (exact (eq_trans (Mult_P4 a z HaR HzR) Hza)).
      assert (Hzx0 : z = x0) by (exact (eq_sym (Huniq z (conj Hz0 Haz)))).
      exact (proj2 (MKT41 x0 Ex0 z) Hzx0).
    - apply (proj1 (MKT41 x0 Ex0 z)) in Hz.
      apply AxiomII; split.
      + rewrite Hz. exact Ex0.
      + split; [rewrite Hz; exact Hx0 | rewrite Hz; exact Hx0a]. }
  assert (Hneg : (a⁻) = x0).
  { change (∩(\{ λ u, u ∈ (R ~ [0]) /\ u · a = 1 \}) = x0).
    rewrite HS. exact (proj1 (MKT44 Ex0)). }
  rewrite Hneg. exact Hx0.
Qed.

Corollary Mult_inv2 : ∀ a, a ∈ (R ~ [0]) -> a · (a⁻) = 1.
Proof.
  intros a Ha.
  destruct (Mult_Co2 a Ha) as [x0 [[Hx0 Hx0sum] Huniq]].
  assert (HaR : a ∈ R).
  { pose proof Ha as Ha'. unfold Setminus in Ha'. apply AxiomII in Ha' as [Ea [HaR _]]. exact HaR. }
  assert (Hx0R : x0 ∈ R).
  { pose proof Hx0 as Hx0'. unfold Setminus in Hx0'. apply AxiomII in Hx0' as [Ex0 [Hx0R _]]. exact Hx0R. }
  assert (Ex0 : Ensemble x0).
  { pose proof Hx0 as Hx0'. unfold Setminus in Hx0'. apply AxiomII in Hx0' as [Ex0 _]. exact Ex0. }
  assert (HS : \{ λ u, u ∈ (R ~ [0]) /\ u · a = 1 \} = [x0]).
  { apply AxiomI; intros z; split; intros Hz.
    - apply AxiomII in Hz as [Ez [Hz0 Hza]].
      assert (HzR : z ∈ R).
      { pose proof Hz0 as Hz0'. unfold Setminus in Hz0'. apply AxiomII in Hz0' as [Ez' [HzR _]]. exact HzR. }
      assert (Haz : a · z = 1) by (exact (eq_trans (Mult_P4 a z HaR HzR) Hza)).
      assert (Hzx0 : z = x0) by (exact (eq_sym (Huniq z (conj Hz0 Haz)))).
      exact (proj2 (MKT41 x0 Ex0 z) Hzx0).
    - apply (proj1 (MKT41 x0 Ex0 z)) in Hz.
      apply AxiomII; split.
      + rewrite Hz. exact Ex0.
      + split; [rewrite Hz; exact Hx0 | rewrite Hz; exact (eq_trans (Mult_P4 x0 a Hx0R HaR) Hx0sum)]. }
  assert (Hneg : (a⁻) = x0).
  { change (∩(\{ λ u, u ∈ (R ~ [0]) /\ u · a = 1 \}) = x0).
    rewrite HS. exact (proj1 (MKT44 Ex0)). }
  rewrite Hneg. exact Hx0sum.
Qed.

Corollary Divide_P1 : ∀ a, a ∈ (R ~ [0]) -> a / a = 1.
Proof.
  intros a Ha. exact (Mult_inv2 a Ha).
Qed.

Corollary Divide_P2 : ∀ a, a ∈ R -> a / 1 = a.
Proof.
  intros a Ha.
  assert (H1 : 1 ∈ (R ~ [0])) by (apply one_in_R).
  destruct (Mult_Co2 1 H1) as [x0 [[Hx0m Hx0s] Huniq]].
  assert (Hinv : (1⁻) = x0).
  { symmetry. apply Huniq. split.
    - apply (Mult_inv1 1 H1).
    - apply (Mult_inv2 1 H1). }
  assert (Hone : 1 = x0).
  { symmetry. apply Huniq. split.
    - exact H1.
    - exact (Mult_P1 1 one_in_R_Co). }
  rewrite Hinv. rewrite <- Hone. apply (Mult_P1 a Ha).
Qed.

Corollary Mult_Co3 : ∀ a x b, a ∈ (R ~ [0]) -> x ∈ R -> b ∈ R
  -> a · x = b -> x = b · (a⁻).
Proof.
  intros a x b Ha Hx Hb Hab.
  assert (HaR : a ∈ R).
  { pose proof Ha as Ha'. unfold Setminus in Ha'. apply AxiomII in Ha' as [Ea [HaR _]]. exact HaR. }
  assert (Hinv : (a⁻) ∈ (R ~ [0])) by (apply (Mult_inv1 a Ha)).
  assert (HinvR : (a⁻) ∈ R).
  { pose proof Hinv as Hinv'. unfold Setminus in Hinv'. apply AxiomII in Hinv' as [E [HinvR _]]. exact HinvR. }
  assert (H1x : 1 · x = x) by (exact (eq_trans (Mult_P4 1 x one_in_R_Co Hx) (Mult_P1 x Hx))).
  assert (Hchain : b · (a⁻) = x).
  { transitivity ((a · x) · (a⁻)).
    - rewrite <- Hab. reflexivity.
    - transitivity (a · (x · (a⁻))).
      + symmetry. apply (Mult_P3 a x (a⁻) HaR Hx HinvR).
      + transitivity (a · ((a⁻) · x)).
        * rewrite (Mult_P4 x (a⁻) Hx HinvR). reflexivity.
        * transitivity ((a · (a⁻)) · x).
          -- apply (Mult_P3 a (a⁻) x HaR HinvR Hx).
          -- transitivity (1 · x).
             ++ rewrite (Mult_inv2 a Ha). reflexivity.
             ++ exact H1x. }
  symmetry. exact Hchain.
Qed.

(* 推论 加法与乘法联系的公理推论 *)
Corollary PlusMult_Co1 : ∀ x, x ∈ R -> x · 0 = 0.
Proof.
  intros x Hx.
  assert (H0 : 0 ∈ R) by (apply zero_in_R).
  assert (Hz : x · 0 ∈ R) by (apply (Mult_close x 0 Hx H0)).
  assert (Hxx : x · 0 + x · 0 = x · 0).
  { transitivity (0 · x + 0 · x).
    - rewrite (Mult_P4 0 x H0 Hx). reflexivity.
    - transitivity ((0 + 0) · x).
      + symmetry. apply (Mult_P5 0 0 x H0 H0 Hx).
      + transitivity (0 · x).
        * rewrite (Plus_P1 0 H0). reflexivity.
        * apply (Mult_P4 0 x H0 Hx). }
  exact (eq_trans (Plus_Co3 (x · 0) (x · 0) (x · 0) Hz Hz Hz Hxx) (Plus_neg2 (x · 0) Hz)).
Qed.

Corollary PlusMult_Co2 : ∀ x y, x ∈ R -> y ∈ R -> x · y = 0 -> x = 0 \/ y = 0.
Proof.
  intros x y Hx Hy Hxy.
  destruct (classic (x = 0)) as [Hx0 | Hx0].
  - left. exact Hx0.
  - right.
    assert (H0 : 0 ∈ R) by (apply zero_in_R).
    assert (Ex : Ensemble x) by (exists R; exact Hx).
    assert (E0 : Ensemble 0) by (exists R; exact H0).
    assert (Hxnot : x ∈ (¬ [0])).
    { apply AxiomII; split.
      - exact Ex.
      - intro Hxsing. apply Hx0. exact (proj1 (MKT41 0 E0 x) Hxsing). }
    assert (HxR0 : x ∈ (R ~ [0])).
    { unfold Setminus. apply AxiomII; split.
      - exact Ex.
      - split; [exact Hx | exact Hxnot]. }
    assert (HinvR : (x⁻) ∈ R).
    { pose proof (Mult_inv1 x HxR0) as Hinv. unfold Setminus in Hinv.
      apply AxiomII in Hinv as [E [HinvR _]]. exact HinvR. }
    assert (H1y : 1 · y = y) by (exact (eq_trans (Mult_P4 1 y one_in_R_Co Hy) (Mult_P1 y Hy))).
    assert (Hinvx : (x⁻) · x = 1) by (exact (eq_trans (Mult_P4 (x⁻) x HinvR Hx) (Mult_inv2 x HxR0))).
    transitivity (1 · y).
    + symmetry. exact H1y.
    + transitivity (((x⁻) · x) · y).
      * rewrite Hinvx. reflexivity.
      * transitivity ((x⁻) · (x · y)).
        -- symmetry. apply (Mult_P3 (x⁻) x y HinvR Hx Hy).
        -- rewrite Hxy. exact (PlusMult_Co1 (x⁻) HinvR).
Qed.

Corollary PlusMult_Co3 : ∀ x, x ∈ R -> -x = (-(1)) · x.
Proof.
  intros x Hx.
  assert (H0 : 0 ∈ R) by (apply zero_in_R).
  assert (H1 : 1 ∈ R) by (apply one_in_R_Co).
  assert (Hne1 : (-(1)) ∈ R) by (apply (Plus_neg1a 1 H1)).
  assert (Hnegx : -x ∈ R) by (apply (Plus_neg1a x Hx)).
  assert (H1x : 1 · x = x) by (exact (eq_trans (Mult_P4 1 x H1 Hx) (Mult_P1 x Hx))).
  assert (Hneg1x : (-(1)) · x ∈ R) by (apply (Mult_close (-(1)) x Hne1 Hx)).
  assert (Hsum : x + (-(1)) · x = 0).
  { transitivity (1 · x + (-(1)) · x).
    - rewrite H1x. reflexivity.
    - transitivity ((1 + (-(1))) · x).
      + symmetry. apply (Mult_P5 1 (-(1)) x H1 Hne1 Hx).
      + transitivity (0 · x).
        * rewrite (Plus_neg2 1 H1). reflexivity.
        * transitivity (x · 0).
          -- apply (Mult_P4 0 x H0 Hx).
          -- apply (PlusMult_Co1 x Hx). }
  assert (Hres : (-(1)) · x = 0 + (-x)) by (exact (Plus_Co3 x ((-(1)) · x) 0 Hx Hneg1x H0 Hsum)).
  assert (Hfin : (-(1)) · x = -x) by
    (exact (eq_trans Hres (eq_trans (Plus_P4 0 (-x) H0 Hnegx) (Plus_P1 (-x) Hnegx)))).
  symmetry. exact Hfin.
Qed.

Corollary PlusMult_Co4 : ∀ x, x ∈ R -> (-(1)) · (-x) = x.
Proof.
  intros x Hx.
  assert (H0 : 0 ∈ R) by (apply zero_in_R).
  assert (H1 : 1 ∈ R) by (apply one_in_R_Co).
  assert (Hnegx : -x ∈ R) by (apply (Plus_neg1a x Hx)).
  assert (Hnegex : -(-x) ∈ R) by (apply (Plus_neg1a (-x) Hnegx)).
  assert (Hn1 : -(-x) = (-(1)) · (-x)) by (apply (PlusMult_Co3 (-x) Hnegx)).
  assert (Hxx : -x + x = 0) by (exact (eq_trans (Plus_P4 (-x) x Hnegx Hx) (Plus_neg2 x Hx))).
  assert (Hres : x = 0 + (-(-x))) by (exact (Plus_Co3 (-x) x 0 Hnegx Hx H0 Hxx)).
  assert (Hfin : x = -(-x)) by
    (exact (eq_trans Hres (eq_trans (Plus_P4 0 (-(-x)) H0 Hnegex) (Plus_P1 (-(-x)) Hnegex)))).
  rewrite <- Hn1. exact (eq_sym Hfin).
Qed.

Corollary PlusMult_Co5 : ∀ x, x ∈ R -> (-x) · (-x) = x · x.
Proof.
  intros x Hx.
  assert (H1 : 1 ∈ R) by (apply one_in_R_Co).
  assert (HaR : (-(1)) ∈ R) by (apply (Plus_neg1a 1 H1)).
  assert (Haa : (-(1)) · (-(1)) = 1) by (exact (PlusMult_Co4 1 H1)).
  assert (HaxR : (-(1)) · x ∈ R) by (apply (Mult_close (-(1)) x HaR Hx)).
  assert (HxxR : x · x ∈ R) by (apply (Mult_close x x Hx Hx)).
  assert (Hneg1 : -x = (-(1)) · x) by (apply (PlusMult_Co3 x Hx)).
  rewrite Hneg1.
  transitivity ((-(1)) · (x · ((-(1)) · x))).
  - symmetry. apply (Mult_P3 (-(1)) x ((-(1)) · x) HaR Hx HaxR).
  - transitivity ((-(1)) · ((x · (-(1))) · x)).
    + rewrite (Mult_P3 x (-(1)) x Hx HaR Hx). reflexivity.
    + transitivity ((-(1)) · (((-(1)) · x) · x)).
      * rewrite (Mult_P4 x (-(1)) Hx HaR). reflexivity.
      * transitivity ((-(1)) · ((-(1)) · (x · x))).
        -- rewrite (Mult_P3 (-(1)) x x HaR Hx Hx). reflexivity.
        -- transitivity (((-(1)) · (-(1))) · (x · x)).
           ++ apply (Mult_P3 (-(1)) (-(1)) (x · x) HaR HaR HxxR).
           ++ transitivity (1 · (x · x)).
              ** rewrite Haa. reflexivity.
              ** exact (eq_trans (Mult_P4 1 (x · x) H1 HxxR) (Mult_P1 (x · x) HxxR)).
Qed.

Corollary PlusMult_Co6 : ∀ x, x ∈ (R ~ [0]) <-> (x⁻) ∈ (R ~ [0]).
Proof.
  intros x. split.
  - intros Hx. exact (Mult_inv1 x Hx).
  - intros h.
    assert (HxinvR : (x⁻) ∈ R).
    { pose proof h as h'. unfold Setminus in h'. apply AxiomII in h' as [E [HxinvR _]]. exact HxinvR. }
    assert (HxinvE : Ensemble (x⁻)) by (exists R; exact HxinvR).
    assert (HSne : \{ λ u, u ∈ (R ~ [0]) /\ u · x = 1 \} ≠ Φ).
    { intro HS0.
      assert (Hmu : (x⁻) = μ).
      { change (∩ \{ λ u, u ∈ (R ~ [0]) /\ u · x = 1 \} = μ).
        rewrite HS0. exact MKT24. }
      rewrite Hmu in HxinvE. exact (MKT39 HxinvE). }
    destruct (MKT_nonempty \{ λ u, u ∈ (R ~ [0]) /\ u · x = 1 \} HSne) as [u HuS].
    apply AxiomII in HuS as [Eu [HuR0 Hux]].
    assert (HuR : u ∈ R).
    { pose proof HuR0 as H. unfold Setminus in H. apply AxiomII in H as [E [HuR _]]. exact HuR. }
    assert (Eone : Ensemble 1) by (exists R; exact one_in_R_Co).
    assert (E0 : Ensemble 0) by (exists R; exact zero_in_R).
    assert (Hud : [u,x] ∈ dom(fm)).
    { apply (MKT69b' (x:=[u,x]) (f:=fm)). rewrite Hux. apply MKT19b. exact Eone. }
    destruct MultR as [_ [Hdomm _]].
    assert (HuxRR : [u,x] ∈ R × R) by (rewrite <- Hdomm; exact Hud).
    assert (HxR : x ∈ R).
    { unfold Cartesian in HuxRR.
      apply AxiomII in HuxRR as [Eux [a [b [Hab [HaR HbR]]]]].
      destruct (MKT49b u x Eux) as [Eu2 Ex2].
      assert (Hb : x = b) by (exact (proj2 (proj1 (MKT55 u x a b Eu2 Ex2) Hab))).
      rewrite Hb. exact HbR. }
    assert (H1not0 : 1 ∉ [0]).
    { pose proof one_in_R as H. unfold Setminus in H. apply AxiomII in H as [E [_ H]].
      apply AxiomII in H as [E' H]. exact H. }
    assert (H1ne0 : 1 ≠ 0).
    { intro H10. apply H1not0. rewrite H10. apply (proj2 (MKT41 0 E0 0)); reflexivity. }
    assert (Hxne0 : x ≠ 0).
    { intro Hx0.
      assert (Hu0 : u · 0 = 0) by (exact (PlusMult_Co1 u HuR)).
      rewrite Hx0 in Hux. rewrite Hu0 in Hux.
      exact (H1ne0 (eq_sym Hux)). }
    unfold Setminus. apply AxiomII. split.
    + exists R; exact HxR.
    + split.
      * exact HxR.
      * apply AxiomII. split.
        -- exists R; exact HxR.
        -- intro Hxsing. apply Hxne0. exact (proj1 (MKT41 0 E0 x) Hxsing).
Qed.

(* 推论 序公理推论 *)
Corollary Order_Co1 : ∀ x y, x ∈ R -> y ∈ R -> x < y \/ y < x \/ x = y.
Proof.
  intros x y Hx Hy.
  destruct (Leq_P4 x y Hx Hy) as [Hxy | Hyx].
  - destruct (classic (x = y)) as [Heq | Hne].
    + right; right; exact Heq.
    + left. split; [exact Hxy | exact Hne].
  - destruct (classic (x = y)) as [Heq | Hne].
    + right; right; exact Heq.
    + right; left. split; [exact Hyx | intro H; exact (Hne (eq_sym H))].
Qed.

Corollary Order_Co2 : ∀ x y z, x ∈ R -> y ∈ R -> z ∈ R
  -> (x < y /\ y ≤ z) \/ (x ≤ y /\ y < z) -> x < z.
Proof.
  intros x y z Hx Hy Hz H.
  destruct H as [[[Hxy_le Hxy_ne] Hyz_le] | [Hxy_le [Hyz_le Hyz_ne]]].
  - split.
    + apply (Leq_P3 x y z Hx Hy Hz Hxy_le Hyz_le).
    + intro Hxz. apply Hxy_ne. apply (Leq_P2 x y Hx Hy Hxy_le).
      rewrite <- Hxz in Hyz_le. exact Hyz_le.
  - split.
    + apply (Leq_P3 x y z Hx Hy Hz Hxy_le Hyz_le).
    + intro Hxz. apply Hyz_ne. apply (Leq_P2 y z Hy Hz Hyz_le).
      rewrite Hxz in Hxy_le. exact Hxy_le.
Qed.

(* 推论 序与加法及乘法联系的公理推论 *)
Corollary OrderPM_Co1 : ∀ x y z, x ∈ R -> y ∈ R -> z ∈ R
  -> x < y -> x + z < y + z.
Proof.
  intros x y z Hx Hy Hz Hxy.
  destruct Hxy as [Hle Hne].
  split.
  - apply (Plus_Leq x y z Hx Hy Hz Hle).
  - intro Hpeq.
    assert (Hzx : z + x = y + z) by (rewrite (Plus_P4 z x Hz Hx); exact Hpeq).
    assert (Hxres : x = (y + z) + (-z)) by (exact (Plus_Co3 z x (y+z) Hz Hx (Plus_close y z Hy Hz) Hzx)).
    assert (Hzy : z + y = y + z) by (exact (Plus_P4 z y Hz Hy)).
    assert (Hyres : y = (y + z) + (-z)) by (exact (Plus_Co3 z y (y+z) Hz Hy (Plus_close y z Hy Hz) Hzy)).
    apply Hne. exact (eq_trans Hxres (eq_sym Hyres)).
Qed.

Corollary OrderPM_Co2a : ∀ x, x ∈ R -> 0 < x -> (-x) < 0.
Proof.
  intros x Hx H0x.
  assert (H0 : 0 ∈ R) by (apply zero_in_R).
  assert (HnegxR : -x ∈ R) by (apply (Plus_neg1a x Hx)).
  assert (Ht : 0 + (-x) < x + (-x)) by (apply (OrderPM_Co1 0 x (-x) H0 Hx HnegxR H0x)).
  assert (H0nx : 0 + (-x) = -x) by (exact (eq_trans (Plus_P4 0 (-x) H0 HnegxR) (Plus_P1 (-x) HnegxR))).
  rewrite H0nx in Ht. rewrite (Plus_neg2 x Hx) in Ht. exact Ht.
Qed.

Corollary OrderPM_Co2b : ∀ x, x ∈ R -> 0 ≤ x -> (-x) ≤ 0.
Proof.
  intros x Hx H0x.
  assert (H0 : 0 ∈ R) by (apply zero_in_R).
  assert (HnegxR : -x ∈ R) by (apply (Plus_neg1a x Hx)).
  assert (Ht : 0 + (-x) ≤ x + (-x)) by (apply (Plus_Leq 0 x (-x) H0 Hx HnegxR H0x)).
  assert (H0nx : 0 + (-x) = -x) by (exact (eq_trans (Plus_P4 0 (-x) H0 HnegxR) (Plus_P1 (-x) HnegxR))).
  rewrite H0nx in Ht. rewrite (Plus_neg2 x Hx) in Ht. exact Ht.
Qed.

Corollary OrderPM_Co3 : ∀ x y z w, x ∈ R -> y ∈ R -> z ∈ R
  -> w ∈ R -> x ≤ y -> z ≤ w -> x + z ≤ y + w.
Proof.
  intros x y z w Hx Hy Hz Hw Hxy Hzw.
  assert (H1 : x + z ≤ y + z) by (apply (Plus_Leq x y z Hx Hy Hz Hxy)).
  assert (H2 : y + z ≤ y + w).
  { assert (H2' : z + y ≤ w + y) by (apply (Plus_Leq z w y Hz Hw Hy Hzw)).
    rewrite (Plus_P4 z y Hz Hy) in H2'. rewrite (Plus_P4 w y Hw Hy) in H2'. exact H2'. }
  exact (Leq_P3 (x+z) (y+z) (y+w) (Plus_close x z Hx Hz) (Plus_close y z Hy Hz) (Plus_close y w Hy Hw) H1 H2).
Qed.

Corollary OrderPM_Co4 : ∀ x y z w, x ∈ R -> y ∈ R -> z ∈ R
  -> w ∈ R -> x ≤ y -> z < w -> x + z < y + w.
Proof.
  intros x y z w Hx Hy Hz Hw Hxy Hzw.
  assert (H1 : x + z ≤ y + z) by (apply (Plus_Leq x y z Hx Hy Hz Hxy)).
  assert (H2 : y + z < y + w).
  { assert (H2' : z + y < w + y) by (apply (OrderPM_Co1 z w y Hz Hw Hy Hzw)).
    rewrite (Plus_P4 z y Hz Hy) in H2'. rewrite (Plus_P4 w y Hw Hy) in H2'. exact H2'. }
  apply (Order_Co2 (x+z) (y+z) (y+w) (Plus_close x z Hx Hz) (Plus_close y z Hy Hz) (Plus_close y w Hy Hw)).
  right. split; assumption.
Qed.

Corollary OrderPM_Co5 : ∀ x y, x ∈ R -> y ∈ R
  -> (0 < x /\ 0 < y) \/ (x < 0 /\ y < 0) -> 0 < x · y.
Proof.
  intros x y Hx Hy H.
  assert (H0 : 0 ∈ R) by (apply zero_in_R).
  assert (Hm1R : (-(1)) ∈ R) by (apply (Plus_neg1a 1 one_in_R_Co)).
  destruct H as [[H0x H0y] | [Hx0 Hy0]].
  - destruct H0x as [H0xle H0xne]. destruct H0y as [H0yle H0yne].
    assert (Hle : 0 ≤ x · y) by (apply (Mult_Leq x y Hx Hy H0xle H0yle)).
    split; [exact Hle |].
    intro Heq.
    destruct (PlusMult_Co2 x y Hx Hy (eq_sym Heq)) as [Hx0' | Hy0'].
    + exact (H0xne (eq_sym Hx0')).
    + exact (H0yne (eq_sym Hy0')).
  - destruct Hx0 as [Hxle Hxne]. destruct Hy0 as [Hyle Hyne].
    assert (HnegxR : -x ∈ R) by (apply (Plus_neg1a x Hx)).
    assert (HnegyR : -y ∈ R) by (apply (Plus_neg1a y Hy)).
    assert (H0mx : 0 ≤ -x).
    { assert (Ht : x + (-x) ≤ 0 + (-x)) by (apply (Plus_Leq x 0 (-x) Hx H0 HnegxR Hxle)).
      rewrite (Plus_neg2 x Hx) in Ht.
      assert (H0nx : 0 + (-x) = -x) by (exact (eq_trans (Plus_P4 0 (-x) H0 HnegxR) (Plus_P1 (-x) HnegxR))).
      rewrite H0nx in Ht. exact Ht. }
    assert (H0my : 0 ≤ -y).
    { assert (Ht : y + (-y) ≤ 0 + (-y)) by (apply (Plus_Leq y 0 (-y) Hy H0 HnegyR Hyle)).
      rewrite (Plus_neg2 y Hy) in Ht.
      assert (H0ny : 0 + (-y) = -y) by (exact (eq_trans (Plus_P4 0 (-y) H0 HnegyR) (Plus_P1 (-y) HnegyR))).
      rewrite H0ny in Ht. exact Ht. }
    assert (Hle : 0 ≤ (-x) · (-y)) by (apply (Mult_Leq (-x) (-y) HnegxR HnegyR H0mx H0my)).
    assert (Hprodeq : (-x) · (-y) = x · y).
    { assert (Hnx : -x = (-(1)) · x) by (apply (PlusMult_Co3 x Hx)).
      assert (Hny : -y = (-(1)) · y) by (apply (PlusMult_Co3 y Hy)).
      assert (HxyR : x · y ∈ R) by (apply (Mult_close x y Hx Hy)).
      assert (HayR : (-(1)) · y ∈ R) by (apply (Mult_close (-(1)) y Hm1R Hy)).
      rewrite Hnx. rewrite Hny.
      transitivity ((-(1)) · (x · ((-(1)) · y))).
      - symmetry. apply (Mult_P3 (-(1)) x ((-(1)) · y) Hm1R Hx HayR).
      - transitivity ((-(1)) · ((x · (-(1))) · y)).
        + rewrite (Mult_P3 x (-(1)) y Hx Hm1R Hy). reflexivity.
        + transitivity ((-(1)) · (((-(1)) · x) · y)).
          * rewrite (Mult_P4 x (-(1)) Hx Hm1R). reflexivity.
          * transitivity ((-(1)) · ((-(1)) · (x · y))).
            -- rewrite (Mult_P3 (-(1)) x y Hm1R Hx Hy). reflexivity.
            -- transitivity (((-(1)) · (-(1))) · (x · y)).
               ++ apply (Mult_P3 (-(1)) (-(1)) (x · y) Hm1R Hm1R HxyR).
               ++ transitivity (1 · (x · y)).
                  ** rewrite (PlusMult_Co4 1 one_in_R_Co). reflexivity.
                  ** exact (eq_trans (Mult_P4 1 (x · y) one_in_R_Co HxyR) (Mult_P1 (x · y) HxyR)). }
    rewrite Hprodeq in Hle.
    split; [exact Hle |].
    intro Heq.
    destruct (PlusMult_Co2 x y Hx Hy (eq_sym Heq)) as [Hx0' | Hy0'].
    + exact (Hxne Hx0').
    + exact (Hyne Hy0').
Qed.

Corollary OrderPM_Co6 : ∀ x y, x ∈ R -> y ∈ R -> x < 0 -> 0 < y -> x · y < 0.
Proof.
  intros x y Hx Hy Hx0 H0y.
  assert (H0 : 0 ∈ R) by (apply zero_in_R).
  assert (HnegxR : -x ∈ R) by (apply (Plus_neg1a x Hx)).
  assert (HprodR : (-x) · y ∈ R) by (apply (Mult_close (-x) y HnegxR Hy)).
  assert (HnegprodR : -((-x)·y) ∈ R) by (apply (Plus_neg1a ((-x)·y) HprodR)).
  assert (H0mx : 0 < -x) by (
    assert (Ht : x + (-x) < 0 + (-x)) by (apply (OrderPM_Co1 x 0 (-x) Hx H0 HnegxR Hx0));
    rewrite (Plus_neg2 x Hx) in Ht;
    assert (H0nx : 0 + (-x) = -x) by (exact (eq_trans (Plus_P4 0 (-x) H0 HnegxR) (Plus_P1 (-x) HnegxR)));
    rewrite H0nx in Ht; exact Ht).
  assert (Hprodpos : 0 < (-x) · y) by (apply (OrderPM_Co5 (-x) y HnegxR Hy); left; split; assumption).
  assert (Hnegprod : -((-x)·y) < 0) by (apply (OrderPM_Co2a ((-x)·y) HprodR Hprodpos)).
  assert (Hxy_eq : x · y = -((-x)·y)).
  { assert (Hsum : (-x) · y + x · y = 0).
    { transitivity (((-x) + x) · y).
      - symmetry. apply (Mult_P5 (-x) x y HnegxR Hx Hy).
      - transitivity ((x + (-x)) · y).
        + rewrite (Plus_P4 (-x) x HnegxR Hx). reflexivity.
        + transitivity (0 · y).
          * rewrite (Plus_neg2 x Hx). reflexivity.
          * transitivity (y · 0).
            -- apply (Mult_P4 0 y H0 Hy).
            -- apply (PlusMult_Co1 y Hy). }
    assert (Hres : x · y = 0 + (-((-x)·y))) by (exact (Plus_Co3 ((-x)·y) (x·y) 0 HprodR (Mult_close x y Hx Hy) H0 Hsum)).
    exact (eq_trans Hres (eq_trans (Plus_P4 0 (-((-x)·y)) H0 HnegprodR) (Plus_P1 (-((-x)·y)) HnegprodR))). }
  rewrite Hxy_eq. exact Hnegprod.
Qed.

Corollary OrderPM_Co7a : ∀ x y z, x ∈ R -> y ∈ R -> z ∈ R -> x < y
  -> 0 < z -> x · z < y · z.
Proof.
  intros x y z Hx Hy Hz Hxy H0z.
  assert (H0 : 0 ∈ R) by (apply zero_in_R).
  assert (HnegxR : -x ∈ R) by (apply (Plus_neg1a x Hx)).
  assert (HdR : y + (-x) ∈ R) by (apply (Plus_close y (-x) Hy HnegxR)).
  assert (H0d : 0 < y + (-x)).
  { assert (Ht : x + (-x) < y + (-x)) by (apply (OrderPM_Co1 x y (-x) Hx Hy HnegxR Hxy)).
    rewrite (Plus_neg2 x Hx) in Ht. exact Ht. }
  assert (H0dz : 0 < (y + (-x)) · z) by (apply (OrderPM_Co5 (y+(-x)) z HdR Hz); left; split; assumption).
  assert (HdzR : (y + (-x)) · z ∈ R) by (apply (Mult_close (y+(-x)) z HdR Hz)).
  assert (HxzR : x · z ∈ R) by (apply (Mult_close x z Hx Hz)).
  assert (Hmain : 0 + x · z < (y + (-x)) · z + x · z) by (apply (OrderPM_Co1 0 ((y+(-x))·z) (x·z) H0 HdzR HxzR H0dz)).
  assert (H0xz : 0 + x · z = x · z) by (exact (eq_trans (Plus_P4 0 (x·z) H0 HxzR) (Plus_P1 (x·z) HxzR))).
  assert (Hyx : (y + (-x)) + x = y).
  { transitivity (y + ((-x) + x)).
    - symmetry. apply (Plus_P3 y (-x) x Hy HnegxR Hx).
    - transitivity (y + 0).
      + rewrite (eq_trans (Plus_P4 (-x) x HnegxR Hx) (Plus_neg2 x Hx)). reflexivity.
      + apply (Plus_P1 y Hy). }
  assert (Hsum : (y + (-x)) · z + x · z = y · z).
  { transitivity (((y + (-x)) + x) · z).
    - symmetry. apply (Mult_P5 (y+(-x)) x z HdR Hx Hz).
    - rewrite Hyx. reflexivity. }
  rewrite H0xz in Hmain. rewrite Hsum in Hmain. exact Hmain.
Qed.

Corollary OrderPM_Co7b : ∀ x y z, x ∈ R -> y ∈ R -> z ∈ R -> x ≤ y
  -> 0 ≤ z -> x · z ≤ y · z.
Proof.
  intros x y z Hx Hy Hz Hxy H0z.
  assert (H0 : 0 ∈ R) by (apply zero_in_R).
  assert (HnegxR : -x ∈ R) by (apply (Plus_neg1a x Hx)).
  assert (HdR : y + (-x) ∈ R) by (apply (Plus_close y (-x) Hy HnegxR)).
  assert (H0d : 0 ≤ y + (-x)).
  { assert (Ht : x + (-x) ≤ y + (-x)) by (apply (Plus_Leq x y (-x) Hx Hy HnegxR Hxy)).
    rewrite (Plus_neg2 x Hx) in Ht. exact Ht. }
  assert (H0dz : 0 ≤ (y + (-x)) · z) by (apply (Mult_Leq (y+(-x)) z HdR Hz H0d H0z)).
  assert (HdzR : (y + (-x)) · z ∈ R) by (apply (Mult_close (y+(-x)) z HdR Hz)).
  assert (HxzR : x · z ∈ R) by (apply (Mult_close x z Hx Hz)).
  assert (Hmain : 0 + x · z ≤ (y + (-x)) · z + x · z) by (apply (Plus_Leq 0 ((y+(-x))·z) (x·z) H0 HdzR HxzR H0dz)).
  assert (H0xz : 0 + x · z = x · z) by (exact (eq_trans (Plus_P4 0 (x·z) H0 HxzR) (Plus_P1 (x·z) HxzR))).
  assert (Hyx : (y + (-x)) + x = y).
  { transitivity (y + ((-x) + x)).
    - symmetry. apply (Plus_P3 y (-x) x Hy HnegxR Hx).
    - transitivity (y + 0).
      + rewrite (eq_trans (Plus_P4 (-x) x HnegxR Hx) (Plus_neg2 x Hx)). reflexivity.
      + apply (Plus_P1 y Hy). }
  assert (Hsum : (y + (-x)) · z + x · z = y · z).
  { transitivity (((y + (-x)) + x) · z).
    - symmetry. apply (Mult_P5 (y+(-x)) x z HdR Hx Hz).
    - rewrite Hyx. reflexivity. }
  rewrite H0xz in Hmain. rewrite Hsum in Hmain. exact Hmain.
Qed.

Corollary OrderPM_Co8a : ∀ x y z, x ∈ R -> y ∈ R -> z ∈ R -> x < y
  -> z < 0 -> y · z < x · z.
Proof.
  intros x y z Hx Hy Hz Hxy Hz0.
  assert (H0 : 0 ∈ R) by (apply zero_in_R).
  assert (Hm1R : (-(1)) ∈ R) by (apply (Plus_neg1a 1 one_in_R_Co)).
  assert (HnegzR : -z ∈ R) by (apply (Plus_neg1a z Hz)).
  assert (H0mz : 0 < -z) by (
    assert (Ht : z + (-z) < 0 + (-z)) by (apply (OrderPM_Co1 z 0 (-z) Hz H0 HnegzR Hz0));
    rewrite (Plus_neg2 z Hz) in Ht;
    assert (H0nz : 0 + (-z) = -z) by (exact (eq_trans (Plus_P4 0 (-z) H0 HnegzR) (Plus_P1 (-z) HnegzR)));
    rewrite H0nz in Ht; exact Ht).
  assert (Hlt : x · (-z) < y · (-z)) by (apply (OrderPM_Co7a x y (-z) Hx Hy HnegzR Hxy H0mz)).
  assert (HxzR : x·z ∈ R) by (apply (Mult_close x z Hx Hz)).
  assert (HyzR : y·z ∈ R) by (apply (Mult_close y z Hy Hz)).
  assert (Hxnegz : x · (-z) = -(x·z)).
  { assert (Hnz : -z = (-(1)) · z) by (apply (PlusMult_Co3 z Hz)).
    rewrite Hnz.
    transitivity ((x · (-(1))) · z).
    - apply (Mult_P3 x (-(1)) z Hx Hm1R Hz).
    - transitivity (((-(1)) · x) · z).
      + rewrite (Mult_P4 x (-(1)) Hx Hm1R). reflexivity.
      + transitivity ((-(1)) · (x · z)).
        * symmetry. apply (Mult_P3 (-(1)) x z Hm1R Hx Hz).
        * exact (eq_sym (PlusMult_Co3 (x·z) HxzR)). }
  assert (Hynegz : y · (-z) = -(y·z)).
  { assert (Hnz : -z = (-(1)) · z) by (apply (PlusMult_Co3 z Hz)).
    rewrite Hnz.
    transitivity ((y · (-(1))) · z).
    - apply (Mult_P3 y (-(1)) z Hy Hm1R Hz).
    - transitivity (((-(1)) · y) · z).
      + rewrite (Mult_P4 y (-(1)) Hy Hm1R). reflexivity.
      + transitivity ((-(1)) · (y · z)).
        * symmetry. apply (Mult_P3 (-(1)) y z Hm1R Hy Hz).
        * exact (eq_sym (PlusMult_Co3 (y·z) HyzR)). }
  rewrite Hxnegz in Hlt. rewrite Hynegz in Hlt.
  assert (Hstep1 : (-(x·z)) + (y·z) < (-(y·z)) + (y·z)) by (apply (OrderPM_Co1 (-(x·z)) (-(y·z)) (y·z) (Plus_neg1a (x·z) HxzR) (Plus_neg1a (y·z) HyzR) HyzR Hlt)).
  assert (Hstep1L : (-(x·z)) + (y·z) = (y·z) + (-(x·z))) by (apply (Plus_P4 (-(x·z)) (y·z) (Plus_neg1a (x·z) HxzR) HyzR)).
  assert (Hstep1R : (-(y·z)) + (y·z) = 0) by (exact (eq_trans (Plus_P4 (-(y·z)) (y·z) (Plus_neg1a (y·z) HyzR) HyzR) (Plus_neg2 (y·z) HyzR))).
  rewrite Hstep1L in Hstep1. rewrite Hstep1R in Hstep1.
  assert (Hstep2 : ((y·z) + (-(x·z))) + (x·z) < 0 + (x·z)) by (apply (OrderPM_Co1 ((y·z)+(-(x·z))) 0 (x·z) (Plus_close (y·z) (-(x·z)) HyzR (Plus_neg1a (x·z) HxzR)) H0 HxzR Hstep1)).
  assert (Hstep2L : ((y·z) + (-(x·z))) + (x·z) = y·z).
  { transitivity ((y·z) + ((-(x·z)) + (x·z))).
    - symmetry. apply (Plus_P3 (y·z) (-(x·z)) (x·z) HyzR (Plus_neg1a (x·z) HxzR) HxzR).
    - transitivity ((y·z) + 0).
      + rewrite (eq_trans (Plus_P4 (-(x·z)) (x·z) (Plus_neg1a (x·z) HxzR) HxzR) (Plus_neg2 (x·z) HxzR)). reflexivity.
      + apply (Plus_P1 (y·z) HyzR). }
  assert (Hstep2R : 0 + (x·z) = x·z) by (exact (eq_trans (Plus_P4 0 (x·z) H0 HxzR) (Plus_P1 (x·z) HxzR))).
  rewrite Hstep2L in Hstep2. rewrite Hstep2R in Hstep2. exact Hstep2.
Qed.

Corollary OrderPM_Co8b : ∀ x y z, x ∈ R -> y ∈ R -> z ∈ R -> x ≤ y
  -> z ≤ 0 -> y · z ≤ x · z.
Proof.
  intros x y z Hx Hy Hz Hxy Hz0.
  assert (H0 : 0 ∈ R) by (apply zero_in_R).
  assert (Hm1R : (-(1)) ∈ R) by (apply (Plus_neg1a 1 one_in_R_Co)).
  assert (HnegzR : -z ∈ R) by (apply (Plus_neg1a z Hz)).
  assert (H0mz : 0 ≤ -z) by (
    assert (Ht : z + (-z) ≤ 0 + (-z)) by (apply (Plus_Leq z 0 (-z) Hz H0 HnegzR Hz0));
    rewrite (Plus_neg2 z Hz) in Ht;
    assert (H0nz : 0 + (-z) = -z) by (exact (eq_trans (Plus_P4 0 (-z) H0 HnegzR) (Plus_P1 (-z) HnegzR)));
    rewrite H0nz in Ht; exact Ht).
  assert (Hle : x · (-z) ≤ y · (-z)) by (apply (OrderPM_Co7b x y (-z) Hx Hy HnegzR Hxy H0mz)).
  assert (HxzR : x·z ∈ R) by (apply (Mult_close x z Hx Hz)).
  assert (HyzR : y·z ∈ R) by (apply (Mult_close y z Hy Hz)).
  assert (Hxnegz : x · (-z) = -(x·z)).
  { assert (Hnz : -z = (-(1)) · z) by (apply (PlusMult_Co3 z Hz)).
    rewrite Hnz.
    transitivity ((x · (-(1))) · z).
    - apply (Mult_P3 x (-(1)) z Hx Hm1R Hz).
    - transitivity (((-(1)) · x) · z).
      + rewrite (Mult_P4 x (-(1)) Hx Hm1R). reflexivity.
      + transitivity ((-(1)) · (x · z)).
        * symmetry. apply (Mult_P3 (-(1)) x z Hm1R Hx Hz).
        * exact (eq_sym (PlusMult_Co3 (x·z) HxzR)). }
  assert (Hynegz : y · (-z) = -(y·z)).
  { assert (Hnz : -z = (-(1)) · z) by (apply (PlusMult_Co3 z Hz)).
    rewrite Hnz.
    transitivity ((y · (-(1))) · z).
    - apply (Mult_P3 y (-(1)) z Hy Hm1R Hz).
    - transitivity (((-(1)) · y) · z).
      + rewrite (Mult_P4 y (-(1)) Hy Hm1R). reflexivity.
      + transitivity ((-(1)) · (y · z)).
        * symmetry. apply (Mult_P3 (-(1)) y z Hm1R Hy Hz).
        * exact (eq_sym (PlusMult_Co3 (y·z) HyzR)). }
  rewrite Hxnegz in Hle. rewrite Hynegz in Hle.
  assert (Hstep1 : (-(x·z)) + (y·z) ≤ (-(y·z)) + (y·z)) by (apply (Plus_Leq (-(x·z)) (-(y·z)) (y·z) (Plus_neg1a (x·z) HxzR) (Plus_neg1a (y·z) HyzR) HyzR Hle)).
  assert (Hstep1L : (-(x·z)) + (y·z) = (y·z) + (-(x·z))) by (apply (Plus_P4 (-(x·z)) (y·z) (Plus_neg1a (x·z) HxzR) HyzR)).
  assert (Hstep1R : (-(y·z)) + (y·z) = 0) by (exact (eq_trans (Plus_P4 (-(y·z)) (y·z) (Plus_neg1a (y·z) HyzR) HyzR) (Plus_neg2 (y·z) HyzR))).
  rewrite Hstep1L in Hstep1. rewrite Hstep1R in Hstep1.
  assert (Hstep2 : ((y·z) + (-(x·z))) + (x·z) ≤ 0 + (x·z)) by (apply (Plus_Leq ((y·z)+(-(x·z))) 0 (x·z) (Plus_close (y·z) (-(x·z)) HyzR (Plus_neg1a (x·z) HxzR)) H0 HxzR Hstep1)).
  assert (Hstep2L : ((y·z) + (-(x·z))) + (x·z) = y·z).
  { transitivity ((y·z) + ((-(x·z)) + (x·z))).
    - symmetry. apply (Plus_P3 (y·z) (-(x·z)) (x·z) HyzR (Plus_neg1a (x·z) HxzR) HxzR).
    - transitivity ((y·z) + 0).
      + rewrite (eq_trans (Plus_P4 (-(x·z)) (x·z) (Plus_neg1a (x·z) HxzR) HxzR) (Plus_neg2 (x·z) HxzR)). reflexivity.
      + apply (Plus_P1 (y·z) HyzR). }
  assert (Hstep2R : 0 + (x·z) = x·z) by (exact (eq_trans (Plus_P4 0 (x·z) H0 HxzR) (Plus_P1 (x·z) HxzR))).
  rewrite Hstep2L in Hstep2. rewrite Hstep2R in Hstep2. exact Hstep2.
Qed.

Corollary OrderPM_Co9 : 0 < 1.
Proof.
  assert (H0 : 0 ∈ R) by (apply zero_in_R).
  assert (H1 : 1 ∈ R) by (apply one_in_R_Co).
  assert (H0E : Ensemble 0) by (exists R; exact H0).
  assert (Hne10 : 1 ≠ 0).
  { pose proof one_in_R as H. unfold Setminus in H. apply AxiomII in H as [E [_ H]].
    apply AxiomII in H as [E' Hnot].
    intro H10. apply Hnot. apply (proj2 (MKT41 0 H0E 1)). exact H10. }
  split.
  - destruct (Leq_P4 0 1 H0 H1) as [H01 | H10]; [exact H01 |].
    exfalso.
    assert (H0m1 : 0 ≤ -(1)).
    { assert (Ht : 1 + (-(1)) ≤ 0 + (-(1))) by (apply (Plus_Leq 1 0 (-(1)) H1 H0 (Plus_neg1a 1 H1) H10)).
      rewrite (Plus_neg2 1 H1) in Ht.
      assert (H0n1 : 0 + (-(1)) = -(1)) by (exact (eq_trans (Plus_P4 0 (-(1)) H0 (Plus_neg1a 1 H1)) (Plus_P1 (-(1)) (Plus_neg1a 1 H1)))).
      rewrite H0n1 in Ht. exact Ht. }
    assert (H01' : 0 ≤ 1).
    { assert (Ht : 0 ≤ (-(1)) · (-(1))) by (apply (Mult_Leq (-(1)) (-(1)) (Plus_neg1a 1 H1) (Plus_neg1a 1 H1) H0m1 H0m1)).
      rewrite (PlusMult_Co4 1 H1) in Ht. exact Ht. }
    exact (Hne10 (eq_sym (Leq_P2 0 1 H0 H1 H01' H10))).
  - intro H01eq. exact (Hne10 (eq_sym H01eq)).
Qed.

Corollary OrderPM_Co10 : ∀ x, x ∈ R -> 0 < x -> 0 < (x⁻).
Proof.
  intros x Hx H0x.
  assert (H0 : 0 ∈ R) by (apply zero_in_R).
  assert (H1 : 1 ∈ R) by (apply one_in_R_Co).
  assert (H0E : Ensemble 0) by (exists R; exact H0).
  assert (Hne10 : 1 ≠ 0).
  { pose proof one_in_R as H. unfold Setminus in H. apply AxiomII in H as [E [_ H]].
    apply AxiomII in H as [E' Hnot].
    intro H10. apply Hnot. apply (proj2 (MKT41 0 H0E 1)). exact H10. }
  assert (Hxne0 : x ≠ 0) by (intro Hx0; exact (proj2 H0x (eq_sym Hx0))).
  assert (HxR0 : x ∈ (R ~ [0])).
  { unfold Setminus. apply AxiomII; split.
    - exists R; exact Hx.
    - split; [exact Hx | apply AxiomII; split; [exists R; exact Hx | intro Hxs; apply Hxne0; exact (proj1 (MKT41 0 H0E x) Hxs)]]. }
  assert (Hinv : (x⁻) ∈ (R ~ [0])) by (apply (Mult_inv1 x HxR0)).
  assert (HinvR : (x⁻) ∈ R).
  { pose proof Hinv as H. unfold Setminus in H. apply AxiomII in H as [E [HinvR _]]. exact HinvR. }
  assert (Hinvne : (x⁻) ≠ 0).
  { intro Hinv0.
    assert (Hprod : x · (x⁻) = 1) by (apply (Mult_inv2 x HxR0)).
    rewrite Hinv0 in Hprod. rewrite (PlusMult_Co1 x Hx) in Hprod.
    exact (Hne10 (eq_sym Hprod)). }
  split.
  - destruct (Leq_P4 (x⁻) 0 HinvR H0) as [Hle | Hge]; [| exact Hge].
    exfalso.
    assert (Hltz : (x⁻) < 0) by (split; [exact Hle | exact Hinvne]).
    assert (Hneg : (x⁻) · x < 0) by (apply (OrderPM_Co6 (x⁻) x HinvR Hx Hltz H0x)).
    assert (Hcomm : (x⁻) · x = x · (x⁻)) by (exact (Mult_P4 (x⁻) x HinvR Hx)).
    assert (Hprod : x · (x⁻) = 1) by (apply (Mult_inv2 x HxR0)).
    rewrite Hcomm in Hneg. rewrite Hprod in Hneg.
    assert (H01 : 0 < 1) by (apply OrderPM_Co9).
    exact (Hne10 (Leq_P2 1 0 H1 H0 (proj1 Hneg) (proj1 H01))).
  - intro H0inv. exact (Hinvne (eq_sym H0inv)).
Qed.

Corollary OrderPM_Co11 : ∀ x y, x ∈ R -> y ∈ R -> 0 < x -> x < y
  -> 0 < (y⁻) /\ (y⁻) < (x⁻).
Proof.
  intros x y Hx Hy H0x Hxy.
  assert (H0 : 0 ∈ R) by (apply zero_in_R).
  assert (H0E : Ensemble 0) by (exists R; exact H0).
  assert (H0y : 0 < y) by (apply (Order_Co2 0 x y H0 Hx Hy); left; split; [exact H0x | exact (proj1 Hxy)]).
  assert (Hyne0 : y ≠ 0) by (intro Hy0; exact (proj2 H0y (eq_sym Hy0))).
  assert (Hxne0 : x ≠ 0) by (intro Hx0; exact (proj2 H0x (eq_sym Hx0))).
  assert (HxR0 : x ∈ (R ~ [0])).
  { unfold Setminus. apply AxiomII; split.
    - exists R; exact Hx.
    - split; [exact Hx | apply AxiomII; split; [exists R; exact Hx | intro Hxs; apply Hxne0; exact (proj1 (MKT41 0 H0E x) Hxs)]]. }
  assert (HyR0 : y ∈ (R ~ [0])).
  { unfold Setminus. apply AxiomII; split.
    - exists R; exact Hy.
    - split; [exact Hy | apply AxiomII; split; [exists R; exact Hy | intro Hys; apply Hyne0; exact (proj1 (MKT41 0 H0E y) Hys)]]. }
  assert (Hxinv : (x⁻) ∈ (R ~ [0])) by (apply (Mult_inv1 x HxR0)).
  assert (Hyinv : (y⁻) ∈ (R ~ [0])) by (apply (Mult_inv1 y HyR0)).
  assert (HxinvR : (x⁻) ∈ R).
  { pose proof Hxinv as H. unfold Setminus in H. apply AxiomII in H as [E [HxinvR _]]. exact HxinvR. }
  assert (HyinvR : (y⁻) ∈ R).
  { pose proof Hyinv as H. unfold Setminus in H. apply AxiomII in H as [E [HyinvR _]]. exact HyinvR. }
  assert (H0yinv : 0 < (y⁻)) by (apply (OrderPM_Co10 y Hy H0y)).
  assert (H0xinv : 0 < (x⁻)) by (apply (OrderPM_Co10 x Hx H0x)).
  split; [exact H0yinv |].
  assert (Hpos : 0 < (x⁻) · (y⁻)) by (apply (OrderPM_Co5 (x⁻) (y⁻) HxinvR HyinvR); left; split; assumption).
  assert (HprodR : (x⁻) · (y⁻) ∈ R) by (apply (Mult_close (x⁻) (y⁻) HxinvR HyinvR)).
  assert (Hlt : x · ((x⁻) · (y⁻)) < y · ((x⁻) · (y⁻))) by (apply (OrderPM_Co7a x y ((x⁻)·(y⁻)) Hx Hy HprodR Hxy Hpos)).
  assert (Hlhs : x · ((x⁻) · (y⁻)) = (y⁻)).
  { transitivity ((x · (x⁻)) · (y⁻)).
    - apply (Mult_P3 x (x⁻) (y⁻) Hx HxinvR HyinvR).
    - transitivity (1 · (y⁻)).
      + rewrite (Mult_inv2 x HxR0). reflexivity.
      + exact (eq_trans (Mult_P4 1 (y⁻) one_in_R_Co HyinvR) (Mult_P1 (y⁻) HyinvR)). }
  assert (Hrhs : y · ((x⁻) · (y⁻)) = (x⁻)).
  { transitivity (y · ((y⁻) · (x⁻))).
    - rewrite (Mult_P4 (x⁻) (y⁻) HxinvR HyinvR). reflexivity.
    - transitivity ((y · (y⁻)) · (x⁻)).
      + apply (Mult_P3 y (y⁻) (x⁻) Hy HyinvR HxinvR).
      + transitivity (1 · (x⁻)).
        * rewrite (Mult_inv2 y HyR0). reflexivity.
        * exact (eq_trans (Mult_P4 1 (x⁻) one_in_R_Co HxinvR) (Mult_P1 (x⁻) HxinvR)). }
  rewrite Hlhs in Hlt. rewrite Hrhs in Hlt. exact Hlt.
Qed.

(* 完备公理与数集确界的存在性 *)
Definition Upper X c := X ⊂ R /\ c ∈ R /\ (∀ x, x ∈ X -> x ≤ c).

Definition Lower X c := X ⊂ R /\ c ∈ R /\ (∀ x, x ∈ X -> c ≤ x).

Definition Bounded X := ∃ c1 c2, Upper X c1 /\ Lower X c2.

Definition Max X c := X ⊂ R /\ c ∈ X /\ (∀ x, x ∈ X -> x ≤ c).

Definition Min X c := X ⊂ R /\ c ∈ X /\ (∀ x, x ∈ X -> c ≤ x).

Corollary Max_Corollary : ∀ X c1 c2, Max X c1 -> Max X c2 -> c1 = c2.
Proof.
  intros X c1 c2 [HX1 [Hc1X Hle1]] [HX2 [Hc2X Hle2]].
  assert (Hc1R : c1 ∈ R) by (apply HX1; exact Hc1X).
  assert (Hc2R : c2 ∈ R) by (apply HX2; exact Hc2X).
  assert (H12 : c1 ≤ c2) by (apply Hle2; exact Hc1X).
  assert (H21 : c2 ≤ c1) by (apply Hle1; exact Hc2X).
  exact (Leq_P2 c1 c2 Hc1R Hc2R H12 H21).
Qed.

Corollary Min_Corollary : ∀ X c1 c2, Min X c1 -> Min X c2 -> c1 = c2.
Proof.
  intros X c1 c2 [HX1 [Hc1X Hle1]] [HX2 [Hc2X Hle2]].
  assert (Hc1R : c1 ∈ R) by (apply HX1; exact Hc1X).
  assert (Hc2R : c2 ∈ R) by (apply HX2; exact Hc2X).
  assert (H12 : c1 ≤ c2) by (apply Hle1; exact Hc2X).
  assert (H21 : c2 ≤ c1) by (apply Hle2; exact Hc1X).
  exact (Leq_P2 c1 c2 Hc1R Hc2R H12 H21).
Qed.

Definition Sup1 X s := Upper X s /\ (∀ s1, s1 ∈ R -> s1 < s
  -> (∃ x1, x1 ∈ X /\ s1 < x1)).

Definition Sup2 X s := Min (\{ λ u, Upper X u \}) s.

Corollary Sup_Corollary : ∀ X s, Sup1 X s <-> Sup2 X s.
Proof.
  intros X s. split.
  - intros [HUpper Hdense].
    unfold Sup2. unfold Min.
    destruct HUpper as [HXsubR [HsR Hles]].
    split.
    + intros u Hu.
      apply AxiomII in Hu as [_ HUpperu].
      destruct HUpperu as [_ [HuR _]].
      exact HuR.
    + split.
      * apply AxiomII; split.
        -- unfold Ensemble; exists R; exact HsR.
        -- exact (conj HXsubR (conj HsR Hles)).
      * intros u Hu.
        apply AxiomII in Hu as [_ HUpperu].
        destruct HUpperu as [_ [HuR Hleu]].
        destruct (Leq_P4 s u HsR HuR) as [Hsu | Hus].
        { exact Hsu. }
        { destruct (classic (u = s)) as [Heq | Hne].
          { rewrite Heq. apply Leq_P1. exact HsR. }
          { exfalso.
            assert (Hult : u < s) by (split; [exact Hus | exact Hne]).
            destruct (Hdense u HuR Hult) as [x1 [Hx1X Hux1]].
            assert (Hx1R : x1 ∈ R) by (apply HXsubR; exact Hx1X).
            assert (Hx1u : x1 ≤ u) by (apply Hleu; exact Hx1X).
            assert (Hux1le : u ≤ x1) by (exact (proj1 Hux1)).
            assert (Hne' : x1 ≠ u) by (intro H; apply (proj2 Hux1); symmetry; exact H).
            exact (Hne' (Leq_P2 x1 u Hx1R HuR Hx1u Hux1le)). } }
  - intros [HYsubR [HsY HYle]].
    apply AxiomII in HsY as [HsEns HsUpper].
    destruct HsUpper as [HXsubR [HsR Hles]].
    split.
    + exact (conj HXsubR (conj HsR Hles)).
    + intros s1 Hs1R Hs1lt.
      apply NNPP; intro Hno.
      assert (Hle_s1 : ∀ x, x ∈ X -> x ≤ s1).
      { intros x HxX.
        assert (HxR : x ∈ R) by (apply HXsubR; exact HxX).
        destruct (Leq_P4 x s1 HxR Hs1R) as [Hxs1 | Hs1x].
        - exact Hxs1.
        - destruct (classic (x = s1)) as [Heq | Hne].
          + rewrite Heq. apply Leq_P1. exact Hs1R.
          + exfalso. apply Hno. exists x.
            split; [exact HxX | split; [exact Hs1x | intro H; apply Hne; symmetry; exact H]]. }
      assert (Hs1Y : s1 ∈ (\{ λ u, Upper X u \})).
      { apply AxiomII; split.
        - unfold Ensemble; exists R; exact Hs1R.
        - exact (conj HXsubR (conj Hs1R Hle_s1)). }
      assert (Hsle : s ≤ s1) by (apply HYle; exact Hs1Y).
      assert (Hs1les : s1 ≤ s) by (exact (proj1 Hs1lt)).
      assert (Hseq : s = s1) by (apply (Leq_P2 s s1 HsR Hs1R Hsle Hs1les)).
      exact ((proj2 Hs1lt) (eq_sym Hseq)).
Qed.

Definition Inf1 X i := Lower X i /\ (∀ i1, i1 ∈ R -> i < i1
  -> (∃ x1, x1 ∈ X /\ x1 < i1)).

Definition Inf2 X i := Max (\{ λ u, Lower X u \}) i.

Corollary Inf_Corollary : ∀ X i, Inf1 X i <-> Inf2 X i.
Proof.
  intros X i. split.
  - intros [HLower Hdense].
    unfold Inf2. unfold Max.
    destruct HLower as [HXsubR [HiR Hles]].
    split.
    + intros u Hu.
      apply AxiomII in Hu as [_ HLoweru].
      destruct HLoweru as [_ [HuR _]].
      exact HuR.
    + split.
      * apply AxiomII; split.
        -- unfold Ensemble; exists R; exact HiR.
        -- exact (conj HXsubR (conj HiR Hles)).
      * intros u Hu.
        apply AxiomII in Hu as [_ HLoweru].
        destruct HLoweru as [_ [HuR Hleu]].
        destruct (Leq_P4 u i HuR HiR) as [Hui | Hiu].
        { exact Hui. }
        { destruct (classic (i = u)) as [Heq | Hne].
          { rewrite Heq. apply Leq_P1. exact HuR. }
          { exfalso.
            assert (Hilt : i < u) by (split; [exact Hiu | exact Hne]).
            destruct (Hdense u HuR Hilt) as [x1 [Hx1X Hx1u]].
            assert (Hx1R : x1 ∈ R) by (apply HXsubR; exact Hx1X).
            assert (Hux1 : u ≤ x1) by (apply Hleu; exact Hx1X).
            assert (Hx1ule : x1 ≤ u) by (exact (proj1 Hx1u)).
            assert (Hne' : x1 ≠ u) by (exact (proj2 Hx1u)).
            exact (Hne' (Leq_P2 x1 u Hx1R HuR Hx1ule Hux1)). } }
  - intros [HYsubR [HiY HYle]].
    apply AxiomII in HiY as [HiEns HiLower].
    destruct HiLower as [HXsubR [HiR Hles]].
    split.
    + exact (conj HXsubR (conj HiR Hles)).
    + intros i1 Hi1R Hi1lt.
      apply NNPP; intro Hno.
      assert (Hle_i1 : ∀ x, x ∈ X -> i1 ≤ x).
      { intros x HxX.
        assert (HxR : x ∈ R) by (apply HXsubR; exact HxX).
        destruct (Leq_P4 i1 x Hi1R HxR) as [Hi1x | Hxi1].
        - exact Hi1x.
        - destruct (classic (x = i1)) as [Heq | Hne].
          + rewrite Heq. apply Leq_P1. exact Hi1R.
          + exfalso. apply Hno. exists x.
            split; [exact HxX | split; [exact Hxi1 | exact Hne]]. }
      assert (Hi1Y : i1 ∈ (\{ λ u, Lower X u \})).
      { apply AxiomII; split.
        - unfold Ensemble; exists R; exact Hi1R.
        - exact (conj HXsubR (conj Hi1R Hle_i1)). }
      assert (Hi1le : i1 ≤ i) by (apply HYle; exact Hi1Y).
      assert (Hile : i ≤ i1) by (exact (proj1 Hi1lt)).
      assert (Hieq : i = i1) by (apply (Leq_P2 i i1 HiR Hi1R Hile Hi1le)).
      exact ((proj2 Hi1lt) Hieq).
Qed.

Theorem SupT : ∀ X, X ⊂ R -> X <> Φ -> (∃ c, Upper X c)
  -> exists ! s, Sup1 X s.
Proof.
  intros X HXsub HXne [c Hub].
  assert (HYsubR : (\{ λ u, Upper X u \}) ⊂ R).
  { intros u Hu.
    apply AxiomII in Hu as [_ HUpperu].
    destruct HUpperu as [_ [HuR _]]. exact HuR. }
  assert (HYne : (\{ λ u, Upper X u \}) <> Φ).
  { intro HY0.
    assert (HcY : c ∈ (\{ λ u, Upper X u \})).
    { apply AxiomII; split.
      - destruct Hub as [_ [HcR _]]. unfold Ensemble; exists R; exact HcR.
      - exact Hub. }
    rewrite HY0 in HcY. exact (MKT16 HcY). }
  assert (Hle : ∀ x y, x ∈ X -> y ∈ (\{ λ u, Upper X u \}) -> x ≤ y).
  { intros x y HxX HyY.
    apply AxiomII in HyY as [_ HUppery].
    destruct HUppery as [_ [_ Hley]]. exact (Hley x HxX). }
  destruct (Completeness X (\{ λ u, Upper X u \}) HXsub HYsubR HXne HYne Hle)
    as [s0 [Hs0R Hs0prop]].
  assert (HSup1_0 : Sup1 X s0).
  { apply (proj2 (Sup_Corollary X s0)).
    unfold Sup2. unfold Min.
    split.
    - exact HYsubR.
    - split.
      + apply AxiomII; split.
        * unfold Ensemble; exists R; exact Hs0R.
        * split.
          -- exact HXsub.
          -- split; [exact Hs0R |].
             intros x HxX.
             assert (HcY : c ∈ (\{ λ u, Upper X u \})).
             { apply AxiomII; split.
               - destruct Hub as [_ [HcR _]]. unfold Ensemble; exists R; exact HcR.
               - exact Hub. }
             exact (proj1 (Hs0prop x c HxX HcY)).
      + intros u Hu.
        destruct (MKT_nonempty X HXne) as [x0 Hx0X].
        exact (proj2 (Hs0prop x0 u Hx0X Hu)). }
  exists s0.
  split; [exact HSup1_0 |].
  intros s' Hs'.
  apply (Min_Corollary (\{ λ u, Upper X u \}) s0 s').
  - apply (proj1 (Sup_Corollary X s0)). exact HSup1_0.
  - apply (proj1 (Sup_Corollary X s')). exact Hs'.
Qed.

Theorem InfT : ∀ X, X ⊂ R -> X <> Φ -> (∃ c, Lower X c)
  -> exists ! i, Inf1 X i.
Proof.
  intros X HXsub HXne [c Hlb].
  assert (HLsubR : (\{ λ u, Lower X u \}) ⊂ R).
  { intros u Hu.
    apply AxiomII in Hu as [_ HLoweru].
    destruct HLoweru as [_ [HuR _]]. exact HuR. }
  assert (HLne : (\{ λ u, Lower X u \}) <> Φ).
  { intro HL0.
    assert (HcL : c ∈ (\{ λ u, Lower X u \})).
    { apply AxiomII; split.
      - destruct Hlb as [_ [HcR _]]. unfold Ensemble; exists R; exact HcR.
      - exact Hlb. }
    rewrite HL0 in HcL. exact (MKT16 HcL). }
  assert (Hle : ∀ l y, l ∈ (\{ λ u, Lower X u \}) -> y ∈ X -> l ≤ y).
  { intros l y HlL HyX.
    apply AxiomII in HlL as [_ HLowerl].
    destruct HLowerl as [_ [_ Hlel]]. exact (Hlel y HyX). }
  destruct (Completeness (\{ λ u, Lower X u \}) X HLsubR HXsub HLne HXne Hle)
    as [i0 [Hi0R Hi0prop]].
  assert (HInf1_0 : Inf1 X i0).
  { apply (proj2 (Inf_Corollary X i0)).
    unfold Inf2. unfold Max.
    split.
    - exact HLsubR.
    - split.
      + apply AxiomII; split.
        * unfold Ensemble; exists R; exact Hi0R.
        * split.
          -- exact HXsub.
          -- split; [exact Hi0R |].
             intros x HxX.
             destruct (MKT_nonempty (\{ λ u, Lower X u \}) HLne) as [l0 Hl0L].
             exact (proj2 (Hi0prop l0 x Hl0L HxX)).
      + intros u Hu.
        destruct (MKT_nonempty X HXne) as [x0 Hx0X].
        exact (proj1 (Hi0prop u x0 Hu Hx0X)). }
  exists i0.
  split; [exact HInf1_0 |].
  intros i' Hi'.
  apply (Max_Corollary (\{ λ u, Lower X u \}) i0 i').
  - apply (proj1 (Inf_Corollary X i0)). exact HInf1_0.
  - apply (proj1 (Inf_Corollary X i')). exact Hi'.
Qed.

(* 自然数集的定义 *)
(* 归纳集的定义 *)
Definition IndSet X := X ⊂ R /\ (∀ x, x ∈ X -> (x + 1) ∈ X).

Proposition IndSet_P1 : ∀ X, X <> Φ -> (∀ x, x ∈ X -> IndSet x) 
  -> IndSet (∩X).
Proof.
  intros X HXne Hall.
  unfold IndSet.
  split.
  - intros z Hz.
    apply AxiomII in Hz as [_ Hz].
    destruct (MKT_nonempty X HXne) as [x0 Hx0].
    destruct (Hall x0 Hx0) as [Hx0sub _].
    exact (Hx0sub z (Hz x0 Hx0)).
  - intros z Hz.
    apply AxiomII in Hz as [_ Hz].
    destruct (MKT_nonempty X HXne) as [x0 Hx0].
    destruct (Hall x0 Hx0) as [_ Hx0ind].
    assert (Hzx0 : z ∈ x0) by (exact (Hz x0 Hx0)).
    assert (Hz1x0 : (z + 1) ∈ x0) by (apply Hx0ind; exact Hzx0).
    apply AxiomII; split.
    + exists x0. exact Hz1x0.
    + intros y Hy.
      destruct (Hall y Hy) as [_ Hyind].
      apply Hyind. exact (Hz y Hy).
Qed.

(* 自然数集 *)
Definition N := ∩(\{ λ u, IndSet u /\ 1 ∈ u \}).

Corollary N_Subset_R : N ⊂ R.
Proof.
  intros z Hz.
  apply AxiomII in Hz as [_ Hz].
  assert (HRY : R ∈ (\{ λ u, IndSet u /\ 1 ∈ u \})).
  { apply AxiomII; split.
    - apply Ensemble_R.
    - split.
      + unfold IndSet. split.
        * intros w Hw. exact Hw.
        * intros x Hx. apply (Plus_close x 1 Hx one_in_R_Co).
      + apply one_in_R_Co. }
  exact (Hz R HRY).
Qed.

Corollary one_in_N : 1 ∈ N.
Proof.
  apply AxiomII; split.
  - exists R; exact one_in_R_Co.
  - intros y Hy.
    apply AxiomII in Hy as [_ [_ H1y]].
    exact H1y.
Qed.

Corollary zero_not_in_N : 0 ∉ N.
Proof.
  intro H0N.
  set (S := (\{ λ x, x ∈ R /\ 1 ≤ x \})).
  assert (HSsubR : S ⊂ R).
  { intros w Hw. apply AxiomII in Hw as [_ [HwR _]]. exact HwR. }
  assert (HSens : Ensemble S) by (apply (MKT33 R S Ensemble_R); exact HSsubR).
  assert (H1S : 1 ∈ S).
  { apply AxiomII; split.
    - exists R; exact one_in_R_Co.
    - split; [exact one_in_R_Co | apply Leq_P1; exact one_in_R_Co]. }
  assert (H0nS : 0 ∉ S).
  { intro H0S. apply AxiomII in H0S as [_ [_ H10]].
    assert (H0 : 0 ∈ R) by (apply zero_in_R).
    assert (H1 : 1 ∈ R) by (apply one_in_R_Co).
    exact ((proj2 OrderPM_Co9) (Leq_P2 0 1 H0 H1 (proj1 OrderPM_Co9) H10)). }
  assert (HSind : IndSet S).
  { unfold IndSet. split; [exact HSsubR |].
    intros x Hx. apply AxiomII in Hx as [_ [HxR H1x]].
    apply AxiomII; split.
    - exists R; apply (Plus_close x 1 HxR one_in_R_Co).
    - split.
      + apply (Plus_close x 1 HxR one_in_R_Co).
      + assert (H0 : 0 ∈ R) by (apply zero_in_R).
        assert (H1 : 1 ∈ R) by (apply one_in_R_Co).
        assert (H11 : 1 ≤ 1 + 1).
        { assert (Ht : 0 + 1 ≤ 1 + 1) by (apply (Plus_Leq 0 1 1 H0 H1 H1 (proj1 OrderPM_Co9))).
          rewrite (eq_trans (Plus_P4 0 1 H0 H1) (Plus_P1 1 H1)) in Ht. exact Ht. }
        assert (Hlt : 1 + 1 ≤ x + 1) by (apply (Plus_Leq 1 x 1 H1 HxR H1 H1x)).
        exact (Leq_P3 1 (1+1) (x+1) H1 (Plus_close 1 1 H1 H1) (Plus_close x 1 HxR H1) H11 Hlt). }
  assert (HSY : S ∈ (\{ λ u, IndSet u /\ 1 ∈ u \})).
  { apply AxiomII; split; [exact HSens | split; [exact HSind | exact H1S]]. }
  apply AxiomII in H0N as [_ H0N].
  exact (H0nS (H0N S HSY)).
Qed.

Corollary IndSet_N : IndSet N.
Proof.
  unfold IndSet. split.
  - exact N_Subset_R.
  - intros x HxN.
    assert (HxR : x ∈ R) by (apply N_Subset_R; exact HxN).
    apply AxiomII in HxN as [_ HxN].
    apply AxiomII; split.
    + exists R; apply (Plus_close x 1 HxR one_in_R_Co).
    + intros y Hy.
      pose proof Hy as HyY.
      apply AxiomII in HyY as [_ [Hyind _]].
      destruct Hyind as [_ Hycl].
      apply Hycl. exact (HxN y Hy).
Qed.

(* 数学归纳原理 *)
Theorem MathInd : ∀ E, E ⊂ N -> 1 ∈ E -> (∀ x, x ∈ E -> (x + 1) ∈ E) 
  -> E = N.
Proof.
  intros E HEsub H1E HEind.
  apply (proj1 (MKT27 E N)). split; [exact HEsub |].
  intros z HzN.
  apply AxiomII in HzN as [_ HzN].
  assert (HRY : R ∈ (\{ λ u, IndSet u /\ 1 ∈ u \})).
  { apply AxiomII; split.
    - apply Ensemble_R.
    - split.
      + unfold IndSet. split.
        * intros w Hw. exact Hw.
        * intros x Hx. apply (Plus_close x 1 Hx one_in_R_Co).
      + apply one_in_R_Co. }
  assert (HYne : (\{ λ u, IndSet u /\ 1 ∈ u \}) <> Φ).
  { intro HY0. rewrite HY0 in HRY. exact (MKT16 HRY). }
  assert (HNens : Ensemble N).
  { unfold N. exact (MKT35 (\{ λ u, IndSet u /\ 1 ∈ u \}) HYne). }
  assert (HEens : Ensemble E) by (apply (MKT33 N E HNens); exact HEsub).
  assert (HEY : E ∈ (\{ λ u, IndSet u /\ 1 ∈ u \})).
  { apply AxiomII; split; [exact HEens |].
    split.
    - unfold IndSet. split.
      + intros w Hw. apply N_Subset_R. apply HEsub. exact Hw.
      + exact HEind.
    - exact H1E. }
  exact (HzN E HEY).
Qed.

(* 自然数的性质 *)
Proposition Nat_P1a : ∀ m n, m ∈ N -> n ∈ N -> (m + n) ∈ N.
Proof.
  intros m n Hm Hn.
  assert (Hsucc : ∀ x, x ∈ N -> (x + 1) ∈ N).
  { intros x Hx. pose proof IndSet_N as HIN. unfold IndSet in HIN. exact (proj2 HIN x Hx). }
  set (E := \{ λ u, u ∈ N /\ (m + u) ∈ N \}).
  assert (HEsub : E ⊂ N).
  { intros z Hz. apply AxiomII in Hz as [_ [HzN _]]. exact HzN. }
  assert (H1E : 1 ∈ E).
  { apply AxiomII; split.
    - exists R; exact one_in_R_Co.
    - split.
      + exact one_in_N.
      + apply Hsucc; exact Hm. }
  assert (Hclos : ∀ x, x ∈ E -> (x + 1) ∈ E).
  { intros x Hx.
    apply AxiomII in Hx as [_ [HxN HmxN]].
    assert (HxR : x ∈ R) by (apply N_Subset_R; exact HxN).
    apply AxiomII; split.
    - exists R; apply (Plus_close x 1 HxR one_in_R_Co).
    - split.
      + apply Hsucc; exact HxN.
      + assert (Hsum : m + (x + 1) = (m + x) + 1)
          by (apply (Plus_P3 m x 1 (N_Subset_R m Hm) HxR one_in_R_Co)).
        rewrite Hsum.
        apply Hsucc; exact HmxN. }
  assert (HE : E = N) by (apply (MathInd E HEsub H1E Hclos)).
  rewrite <- HE in Hn.
  apply AxiomII in Hn as [_ [_ Hmn]].
  exact Hmn.
Qed.

Proposition Nat_P1b : ∀ m n, m ∈ N -> n ∈ N -> (m · n) ∈ N.
Proof.
  intros m n Hm Hn.
  assert (Hsucc : ∀ x, x ∈ N -> (x + 1) ∈ N).
  { intros x Hx. pose proof IndSet_N as HIN. unfold IndSet in HIN. exact (proj2 HIN x Hx). }
  set (E := \{ λ u, u ∈ N /\ (m · u) ∈ N \}).
  assert (HEsub : E ⊂ N).
  { intros z Hz. apply AxiomII in Hz as [_ [HzN _]]. exact HzN. }
  assert (H1E : 1 ∈ E).
  { apply AxiomII; split.
    - exists R; exact one_in_R_Co.
    - split.
      + exact one_in_N.
      + rewrite (Mult_P1 m (N_Subset_R m Hm)). exact Hm. }
  assert (Hclos : ∀ x, x ∈ E -> (x + 1) ∈ E).
  { intros x Hx.
    apply AxiomII in Hx as [_ [HxN HmxN]].
    assert (HxR : x ∈ R) by (apply N_Subset_R; exact HxN).
    apply AxiomII; split.
    - exists R; apply (Plus_close x 1 HxR one_in_R_Co).
    - split.
      + apply Hsucc; exact HxN.
      + assert (Hprod : m · (x + 1) = (m · x) + m).
        { transitivity ((x + 1) · m).
          - apply (Mult_P4 m (x + 1) (N_Subset_R m Hm) (Plus_close x 1 HxR one_in_R_Co)).
          - transitivity ((x · m) + (1 · m)).
            + apply (Mult_P5 x 1 m HxR one_in_R_Co (N_Subset_R m Hm)).
            + rewrite (Mult_P4 1 m one_in_R_Co (N_Subset_R m Hm)).
              rewrite (Mult_P1 m (N_Subset_R m Hm)).
              rewrite (Mult_P4 x m HxR (N_Subset_R m Hm)). reflexivity. }
        rewrite Hprod.
        apply (Nat_P1a (m · x) m HmxN Hm). }
  assert (HE : E = N) by (apply (MathInd E HEsub H1E Hclos)).
  rewrite <- HE in Hn.
  apply AxiomII in Hn as [_ [_ Hmn]].
  exact Hmn.
Qed.

Proposition Nat_P2 : ∀ n, n ∈ N -> n <> 1 -> (n - 1) ∈ N.
Proof.
  intros n Hn Hn1.
  assert (Hsucc : ∀ x, x ∈ N -> (x + 1) ∈ N).
  { intros x Hx. pose proof IndSet_N as HIN. unfold IndSet in HIN. exact (proj2 HIN x Hx). }
  set (E := \{ λ u, u ∈ N /\ (u = 1 \/ (u - 1) ∈ N) \}).
  assert (HEsub : E ⊂ N).
  { intros z Hz. apply AxiomII in Hz as [_ [HzN _]]. exact HzN. }
  assert (H1E : 1 ∈ E).
  { apply AxiomII; split.
    - exists R; exact one_in_R_Co.
    - split; [exact one_in_N | left; reflexivity]. }
  assert (Hclos : ∀ x, x ∈ E -> (x + 1) ∈ E).
  { intros x Hx.
    apply AxiomII in Hx as [_ [HxN _]].
    assert (HxR : x ∈ R) by (apply N_Subset_R; exact HxN).
    assert (Hne1R : (-(1)) ∈ R) by (apply (Plus_neg1a 1 one_in_R_Co)).
    apply AxiomII; split.
    - exists R; apply (Plus_close x 1 HxR one_in_R_Co).
    - split.
      + apply Hsucc; exact HxN.
      + right.
        assert (Hsum : (x + 1) + (-(1)) = x).
        { transitivity (x + (1 + (-(1)))).
          - symmetry. apply (Plus_P3 x 1 (-(1)) HxR one_in_R_Co Hne1R).
          - rewrite (Plus_neg2 1 one_in_R_Co). apply (Plus_P1 x HxR). }
        rewrite Hsum. exact HxN. }
  assert (HE : E = N) by (apply (MathInd E HEsub H1E Hclos)).
  rewrite <- HE in Hn.
  apply AxiomII in Hn as [_ [_ Hdisj]].
  destruct Hdisj as [Heq | Hpred].
  - exfalso. apply Hn1. exact Heq.
  - exact Hpred.
Qed.

Proposition Nat_P3 : ∀ n, n ∈ N -> Min (\{ λ u, u ∈ N /\ n < u \}) (n + 1).
Proof.
  intros n Hn.
  assert (Hsucc : ∀ x, x ∈ N -> (x + 1) ∈ N).
  { intros x Hx. pose proof IndSet_N as HIN. unfold IndSet in HIN. exact (proj2 HIN x Hx). }
  assert (HnR : n ∈ R) by (apply N_Subset_R; exact Hn).
  assert (Hn1N : (n + 1) ∈ N) by (apply Hsucc; exact Hn).
  assert (Hmin : ∀ u, u ∈ N -> 1 ≤ u).
  { intros u Hu.
    set (F := \{ λ w, w ∈ N /\ 1 ≤ w \}).
    assert (HFsub : F ⊂ N).
    { intros z Hz. apply AxiomII in Hz as [_ [HzN _]]. exact HzN. }
    assert (H1F : 1 ∈ F).
    { apply AxiomII; split.
      - exists R; exact one_in_R_Co.
      - split; [exact one_in_N | apply Leq_P1; exact one_in_R_Co]. }
    assert (HFcl : ∀ x, x ∈ F -> (x + 1) ∈ F).
    { intros x Hx.
      apply AxiomII in Hx as [_ [HxN H1x]].
      assert (HxR : x ∈ R) by (apply N_Subset_R; exact HxN).
      assert (Hx1N : (x + 1) ∈ N) by (apply Hsucc; exact HxN).
      assert (Hlt : x < x + 1).
      { assert (Ht : 0 + x < 1 + x) by (apply (OrderPM_Co1 0 1 x zero_in_R one_in_R_Co HxR); exact OrderPM_Co9).
        rewrite (eq_trans (Plus_P4 0 x zero_in_R HxR) (Plus_P1 x HxR)) in Ht.
        rewrite (Plus_P4 1 x one_in_R_Co HxR) in Ht.
        exact Ht. }
      apply AxiomII; split.
      - exists R; exact (N_Subset_R (x + 1) Hx1N).
      - split; [exact Hx1N |].
        exact (Leq_P3 1 x (x + 1) one_in_R_Co HxR (Plus_close x 1 HxR one_in_R_Co) H1x (proj1 Hlt)). }
    assert (HF : F = N) by (apply (MathInd F HFsub H1F HFcl)).
    assert (HuF : u ∈ F) by (rewrite HF; exact Hu).
    apply AxiomII in HuF as [_ [_ H1u]].
    exact H1u. }
  assert (Hno_between : ∀ u, u ∈ N -> ~ (∃ x, x ∈ N /\ u < x /\ x < u + 1)).
  { set (G := \{ λ w, w ∈ N /\ ~ (∃ x, x ∈ N /\ w < x /\ x < w + 1) \}).
    assert (HGsub : G ⊂ N).
    { intros z Hz. apply AxiomII in Hz as [_ [HzN _]]. exact HzN. }
    assert (H1G : 1 ∈ G).
    { apply AxiomII; split.
      - exists R; exact one_in_R_Co.
      - split; [exact one_in_N |].
        intros Hex. destruct Hex as [x [HxN [Hlt1 Hlt2]]].
        assert (HxR : x ∈ R) by (apply N_Subset_R; exact HxN).
        assert (Hne1R : (-(1)) ∈ R) by (apply (Plus_neg1a 1 one_in_R_Co)).
        assert (Hxne : x <> 1).
        { intro He. subst x. exact (proj2 Hlt1 eq_refl). }
        assert (Hxm1N : x - 1 ∈ N) by (apply (Nat_P2 x HxN Hxne)).
        assert (H1xm1 : 1 ≤ x - 1) by (apply Hmin; exact Hxm1N).
        assert (Hxm1R : (x + (-(1))) ∈ R) by (apply (Plus_close x (-(1)) HxR Hne1R)).
        assert (Hltx : x + (-(1)) < 1).
        { assert (Heq : (1 + 1) + (-(1)) = 1).
          { transitivity (1 + (1 + (-(1)))).
            - symmetry. apply (Plus_P3 1 1 (-(1)) one_in_R_Co one_in_R_Co Hne1R).
            - rewrite (Plus_neg2 1 one_in_R_Co). apply (Plus_P1 1 one_in_R_Co). }
          assert (Ht : x + (-(1)) < (1 + 1) + (-(1)))
            by (apply (OrderPM_Co1 x (1 + 1) (-(1)) HxR (Plus_close 1 1 one_in_R_Co one_in_R_Co) Hne1R Hlt2)).
          rewrite Heq in Ht. exact Ht. }
        exact (proj2 Hltx (Leq_P2 (x + (-(1))) 1 Hxm1R one_in_R_Co (proj1 Hltx) H1xm1)). }
    assert (HGcl : ∀ x0, x0 ∈ G -> (x0 + 1) ∈ G).
    { intros x0 Hx0.
      apply AxiomII in Hx0 as [_ [Hx0N Hno]].
      assert (Hx0R : x0 ∈ R) by (apply N_Subset_R; exact Hx0N).
      assert (Hx01N : (x0 + 1) ∈ N) by (apply Hsucc; exact Hx0N).
      assert (Hx01R : (x0 + 1) ∈ R) by (apply (Plus_close x0 1 Hx0R one_in_R_Co)).
      assert (H1x01 : 1 ≤ x0 + 1).
      { assert (Hlt : x0 < x0 + 1).
        { assert (Ht : 0 + x0 < 1 + x0) by (apply (OrderPM_Co1 0 1 x0 zero_in_R one_in_R_Co Hx0R); exact OrderPM_Co9).
          rewrite (eq_trans (Plus_P4 0 x0 zero_in_R Hx0R) (Plus_P1 x0 Hx0R)) in Ht.
          rewrite (Plus_P4 1 x0 one_in_R_Co Hx0R) in Ht.
          exact Ht. }
        exact (Leq_P3 1 x0 (x0 + 1) one_in_R_Co Hx0R Hx01R (Hmin x0 Hx0N) (proj1 Hlt)). }
      apply AxiomII; split.
      - exists R; exact (N_Subset_R (x0 + 1) Hx01N).
      - split; [exact Hx01N |].
        intros Hex. destruct Hex as [x [HxN [Hlt1 Hlt2]]].
        assert (HxR : x ∈ R) by (apply N_Subset_R; exact HxN).
        assert (Hne1R : (-(1)) ∈ R) by (apply (Plus_neg1a 1 one_in_R_Co)).
        assert (Hxne : x <> 1).
        { intro He. subst x.
          exact (proj2 Hlt1 (Leq_P2 (x0 + 1) 1 Hx01R one_in_R_Co (proj1 Hlt1) H1x01)). }
        assert (Hym1N : x - 1 ∈ N) by (apply (Nat_P2 x HxN Hxne)).
        assert (Hux : x0 < x + (-(1))).
        { assert (Ht : (x0 + 1) + (-(1)) < x + (-(1))) by (apply (OrderPM_Co1 (x0 + 1) x (-(1)) Hx01R HxR Hne1R Hlt1)).
          assert (Heq : (x0 + 1) + (-(1)) = x0).
          { transitivity (x0 + (1 + (-(1)))).
            - symmetry. apply (Plus_P3 x0 1 (-(1)) Hx0R one_in_R_Co Hne1R).
            - rewrite (Plus_neg2 1 one_in_R_Co). apply (Plus_P1 x0 Hx0R). }
          rewrite Heq in Ht. exact Ht. }
        assert (Huy : x + (-(1)) < x0 + 1).
        { assert (Ht : x + (-(1)) < ((x0 + 1) + 1) + (-(1))) by (apply (OrderPM_Co1 x ((x0 + 1) + 1) (-(1)) HxR (Plus_close (x0 + 1) 1 Hx01R one_in_R_Co) Hne1R Hlt2)).
          assert (Heq : ((x0 + 1) + 1) + (-(1)) = x0 + 1).
          { transitivity ((x0 + 1) + (1 + (-(1)))).
            - symmetry. apply (Plus_P3 (x0 + 1) 1 (-(1)) Hx01R one_in_R_Co Hne1R).
            - rewrite (Plus_neg2 1 one_in_R_Co). apply (Plus_P1 (x0 + 1) Hx01R). }
          rewrite Heq in Ht. exact Ht. }
        apply Hno. exists (x + (-(1))). split; [exact Hym1N | split; [exact Hux | exact Huy]]. }
    assert (HG : G = N) by (apply (MathInd G HGsub H1G HGcl)).
    intros u Hu.
    assert (HuG : u ∈ G) by (rewrite HG; exact Hu).
    apply AxiomII in HuG as [_ [_ Hno]].
    exact Hno. }
  unfold Min. split.
  - intros z Hz. apply AxiomII in Hz as [_ [HzN _]]. apply N_Subset_R; exact HzN.
  - split.
    + apply AxiomII; split.
      * exists R; exact (N_Subset_R (n + 1) Hn1N).
      * split; [exact Hn1N |].
        assert (Hlt : n < n + 1).
        { assert (Ht : 0 + n < 1 + n) by (apply (OrderPM_Co1 0 1 n zero_in_R one_in_R_Co HnR); exact OrderPM_Co9).
          rewrite (eq_trans (Plus_P4 0 n zero_in_R HnR) (Plus_P1 n HnR)) in Ht.
          rewrite (Plus_P4 1 n one_in_R_Co HnR) in Ht.
          exact Ht. }
        exact Hlt.
    + intros x Hx.
      apply AxiomII in Hx as [_ [HxN Hnx]].
      assert (HxR : x ∈ R) by (apply N_Subset_R; exact HxN).
      destruct (Leq_P4 (n + 1) x (Plus_close n 1 HnR one_in_R_Co) HxR) as [Hle | Hle].
      * exact Hle.
      * destruct (classic (x = n + 1)) as [Heq | Hne].
        { rewrite Heq. apply Leq_P1; exact (Plus_close n 1 HnR one_in_R_Co). }
        { exfalso. apply (Hno_between n Hn). exists x.
          split; [exact HxN | split; [exact Hnx | exact (conj Hle Hne)]]. }
Qed.

Proposition Nat_P4 : ∀ m n, m ∈ N -> n ∈ N -> n < m -> (n + 1) ≤ m.
Proof.
  intros m n Hm Hn Hnm.
  destruct (Nat_P3 n Hn) as [_ [_ Hminle]].
  apply Hminle.
  apply AxiomII; split.
  - exists R; exact (N_Subset_R m Hm).
  - split; [exact Hm | exact Hnm].
Qed.

Proposition Nat_P5 : ∀ n, n ∈ N -> ~ (∃ x, x ∈ N /\ n < x /\ x < (n + 1)).
Proof.
  intros n Hn.
  assert (Hsucc : ∀ x, x ∈ N -> (x + 1) ∈ N).
  { intros x Hx. pose proof IndSet_N as HIN. unfold IndSet in HIN. exact (proj2 HIN x Hx). }
  assert (Hmin : ∀ u, u ∈ N -> 1 ≤ u).
  { intros u Hu.
    set (F := \{ λ w, w ∈ N /\ 1 ≤ w \}).
    assert (HFsub : F ⊂ N).
    { intros z Hz. apply AxiomII in Hz as [_ [HzN _]]. exact HzN. }
    assert (H1F : 1 ∈ F).
    { apply AxiomII; split.
      - exists R; exact one_in_R_Co.
      - split; [exact one_in_N | apply Leq_P1; exact one_in_R_Co]. }
    assert (HFcl : ∀ x, x ∈ F -> (x + 1) ∈ F).
    { intros x Hx.
      apply AxiomII in Hx as [_ [HxN H1x]].
      assert (HxR : x ∈ R) by (apply N_Subset_R; exact HxN).
      assert (Hx1N : (x + 1) ∈ N) by (apply Hsucc; exact HxN).
      assert (Hlt : x < x + 1).
      { assert (Ht : 0 + x < 1 + x) by (apply (OrderPM_Co1 0 1 x zero_in_R one_in_R_Co HxR); exact OrderPM_Co9).
        rewrite (eq_trans (Plus_P4 0 x zero_in_R HxR) (Plus_P1 x HxR)) in Ht.
        rewrite (Plus_P4 1 x one_in_R_Co HxR) in Ht.
        exact Ht. }
      apply AxiomII; split.
      - exists R; exact (N_Subset_R (x + 1) Hx1N).
      - split; [exact Hx1N |].
        exact (Leq_P3 1 x (x + 1) one_in_R_Co HxR (Plus_close x 1 HxR one_in_R_Co) H1x (proj1 Hlt)). }
    assert (HF : F = N) by (apply (MathInd F HFsub H1F HFcl)).
    assert (HuF : u ∈ F) by (rewrite HF; exact Hu).
    apply AxiomII in HuF as [_ [_ H1u]].
    exact H1u. }
  set (G := \{ λ w, w ∈ N /\ ~ (∃ x, x ∈ N /\ w < x /\ x < w + 1) \}).
  assert (HGsub : G ⊂ N).
  { intros z Hz. apply AxiomII in Hz as [_ [HzN _]]. exact HzN. }
  assert (H1G : 1 ∈ G).
  { apply AxiomII; split.
    - exists R; exact one_in_R_Co.
    - split; [exact one_in_N |].
      intros Hex. destruct Hex as [x [HxN [Hlt1 Hlt2]]].
      assert (HxR : x ∈ R) by (apply N_Subset_R; exact HxN).
      assert (Hne1R : (-(1)) ∈ R) by (apply (Plus_neg1a 1 one_in_R_Co)).
      assert (Hxne : x <> 1).
      { intro He. subst x. exact (proj2 Hlt1 eq_refl). }
      assert (Hxm1N : x - 1 ∈ N) by (apply (Nat_P2 x HxN Hxne)).
      assert (H1xm1 : 1 ≤ x - 1) by (apply Hmin; exact Hxm1N).
      assert (Hxm1R : (x + (-(1))) ∈ R) by (apply (Plus_close x (-(1)) HxR Hne1R)).
      assert (Hltx : x + (-(1)) < 1).
      { assert (Heq : (1 + 1) + (-(1)) = 1).
        { transitivity (1 + (1 + (-(1)))).
          - symmetry. apply (Plus_P3 1 1 (-(1)) one_in_R_Co one_in_R_Co Hne1R).
          - rewrite (Plus_neg2 1 one_in_R_Co). apply (Plus_P1 1 one_in_R_Co). }
        assert (Ht : x + (-(1)) < (1 + 1) + (-(1)))
          by (apply (OrderPM_Co1 x (1 + 1) (-(1)) HxR (Plus_close 1 1 one_in_R_Co one_in_R_Co) Hne1R Hlt2)).
        rewrite Heq in Ht. exact Ht. }
      exact (proj2 Hltx (Leq_P2 (x + (-(1))) 1 Hxm1R one_in_R_Co (proj1 Hltx) H1xm1)). }
  assert (HGcl : ∀ x0, x0 ∈ G -> (x0 + 1) ∈ G).
  { intros x0 Hx0.
    apply AxiomII in Hx0 as [_ [Hx0N Hno]].
    assert (Hx0R : x0 ∈ R) by (apply N_Subset_R; exact Hx0N).
    assert (Hx01N : (x0 + 1) ∈ N) by (apply Hsucc; exact Hx0N).
    assert (Hx01R : (x0 + 1) ∈ R) by (apply (Plus_close x0 1 Hx0R one_in_R_Co)).
    assert (H1x01 : 1 ≤ x0 + 1).
    { assert (Hlt : x0 < x0 + 1).
      { assert (Ht : 0 + x0 < 1 + x0) by (apply (OrderPM_Co1 0 1 x0 zero_in_R one_in_R_Co Hx0R); exact OrderPM_Co9).
        rewrite (eq_trans (Plus_P4 0 x0 zero_in_R Hx0R) (Plus_P1 x0 Hx0R)) in Ht.
        rewrite (Plus_P4 1 x0 one_in_R_Co Hx0R) in Ht.
        exact Ht. }
      exact (Leq_P3 1 x0 (x0 + 1) one_in_R_Co Hx0R Hx01R (Hmin x0 Hx0N) (proj1 Hlt)). }
    apply AxiomII; split.
    - exists R; exact (N_Subset_R (x0 + 1) Hx01N).
    - split; [exact Hx01N |].
      intros Hex. destruct Hex as [x [HxN [Hlt1 Hlt2]]].
      assert (HxR : x ∈ R) by (apply N_Subset_R; exact HxN).
      assert (Hne1R : (-(1)) ∈ R) by (apply (Plus_neg1a 1 one_in_R_Co)).
      assert (Hxne : x <> 1).
      { intro He. subst x.
        exact (proj2 Hlt1 (Leq_P2 (x0 + 1) 1 Hx01R one_in_R_Co (proj1 Hlt1) H1x01)). }
      assert (Hym1N : x - 1 ∈ N) by (apply (Nat_P2 x HxN Hxne)).
      assert (Hux : x0 < x + (-(1))).
      { assert (Ht : (x0 + 1) + (-(1)) < x + (-(1))) by (apply (OrderPM_Co1 (x0 + 1) x (-(1)) Hx01R HxR Hne1R Hlt1)).
        assert (Heq : (x0 + 1) + (-(1)) = x0).
        { transitivity (x0 + (1 + (-(1)))).
          - symmetry. apply (Plus_P3 x0 1 (-(1)) Hx0R one_in_R_Co Hne1R).
          - rewrite (Plus_neg2 1 one_in_R_Co). apply (Plus_P1 x0 Hx0R). }
        rewrite Heq in Ht. exact Ht. }
      assert (Huy : x + (-(1)) < x0 + 1).
      { assert (Ht : x + (-(1)) < ((x0 + 1) + 1) + (-(1))) by (apply (OrderPM_Co1 x ((x0 + 1) + 1) (-(1)) HxR (Plus_close (x0 + 1) 1 Hx01R one_in_R_Co) Hne1R Hlt2)).
        assert (Heq : ((x0 + 1) + 1) + (-(1)) = x0 + 1).
        { transitivity ((x0 + 1) + (1 + (-(1)))).
          - symmetry. apply (Plus_P3 (x0 + 1) 1 (-(1)) Hx01R one_in_R_Co Hne1R).
          - rewrite (Plus_neg2 1 one_in_R_Co). apply (Plus_P1 (x0 + 1) Hx01R). }
        rewrite Heq in Ht. exact Ht. }
      apply Hno. exists (x + (-(1))). split; [exact Hym1N | split; [exact Hux | exact Huy]]. }
  assert (HG : G = N) by (apply (MathInd G HGsub H1G HGcl)).
  assert (HnG : n ∈ G) by (rewrite HG; exact Hn).
  apply AxiomII in HnG as [_ [_ Hno]].
  exact Hno.
Qed.

Proposition Nat_P6 : ∀ n, n ∈ N -> n <> 1
  -> ~ (∃ x, x ∈ N /\ (n - 1) < x /\ x < n).
Proof.
  intros n Hn Hn1.
  assert (Hnm1N : n - 1 ∈ N) by (apply (Nat_P2 n Hn Hn1)).
  assert (Hno : ~ (∃ x, x ∈ N /\ (n - 1) < x /\ x < (n - 1) + 1))
    by (apply (Nat_P5 (n - 1) Hnm1N)).
  assert (HnR : n ∈ R) by (apply N_Subset_R; exact Hn).
  assert (Hne1R : (-(1)) ∈ R) by (apply (Plus_neg1a 1 one_in_R_Co)).
  assert (Heq : (n + (-(1))) + 1 = n).
  { transitivity (n + ((-(1)) + 1)).
    - symmetry. apply (Plus_P3 n (-(1)) 1 HnR Hne1R one_in_R_Co).
    - transitivity (n + 0).
      + rewrite (Plus_P4 (-(1)) 1 Hne1R one_in_R_Co). rewrite (Plus_neg2 1 one_in_R_Co). reflexivity.
      + apply (Plus_P1 n HnR). }
  intro Hex. apply Hno. destruct Hex as [x [HxN [Hlt1 Hlt2]]].
  exists x. split; [exact HxN | split; [exact Hlt1 |]].
  rewrite Heq. exact Hlt2.
Qed.

Lemma one_is_min_in_N : Min N 1.
Proof.
  assert (Hsucc : ∀ x, x ∈ N -> (x + 1) ∈ N).
  { intros x Hx. pose proof IndSet_N as HIN. unfold IndSet in HIN. exact (proj2 HIN x Hx). }
  set (F := \{ λ w, w ∈ N /\ 1 ≤ w \}).
  assert (HFsub : F ⊂ N).
  { intros z Hz. apply AxiomII in Hz as [_ [HzN _]]. exact HzN. }
  assert (H1F : 1 ∈ F).
  { apply AxiomII; split.
    - exists R; exact one_in_R_Co.
    - split; [exact one_in_N | apply Leq_P1; exact one_in_R_Co]. }
  assert (HFcl : ∀ x, x ∈ F -> (x + 1) ∈ F).
  { intros x Hx.
    apply AxiomII in Hx as [_ [HxN H1x]].
    assert (HxR : x ∈ R) by (apply N_Subset_R; exact HxN).
    assert (Hx1N : (x + 1) ∈ N) by (apply Hsucc; exact HxN).
    assert (Hlt : x < x + 1).
    { assert (Ht : 0 + x < 1 + x) by (apply (OrderPM_Co1 0 1 x zero_in_R one_in_R_Co HxR); exact OrderPM_Co9).
      rewrite (eq_trans (Plus_P4 0 x zero_in_R HxR) (Plus_P1 x HxR)) in Ht.
      rewrite (Plus_P4 1 x one_in_R_Co HxR) in Ht.
      exact Ht. }
    apply AxiomII; split.
    - exists R; exact (N_Subset_R (x + 1) Hx1N).
    - split; [exact Hx1N |].
      exact (Leq_P3 1 x (x + 1) one_in_R_Co HxR (Plus_close x 1 HxR one_in_R_Co) H1x (proj1 Hlt)). }
  assert (HF : F = N) by (apply (MathInd F HFsub H1F HFcl)).
  unfold Min. split.
  - exact N_Subset_R.
  - split.
    + exact one_in_N.
    + intros u Hu.
      assert (HuF : u ∈ F) by (rewrite HF; exact Hu).
      apply AxiomII in HuF as [_ [_ H1u]].
      exact H1u.
Qed.

Proposition Nat_P7 : ∀ E, E ⊂ N -> E <> Φ -> ∃ n, Min E n.
Proof.
  intros E HE Hne.
  assert (Hsucc : ∀ x, x ∈ N -> (x + 1) ∈ N).
  { intros x Hx. pose proof IndSet_N as HIN. unfold IndSet in HIN. exact (proj2 HIN x Hx). }
  assert (Hmin : ∀ u, u ∈ N -> 1 ≤ u).
  { intros u Hu.
    set (F := \{ λ w, w ∈ N /\ 1 ≤ w \}).
    assert (HFsub : F ⊂ N).
    { intros z Hz. apply AxiomII in Hz as [_ [HzN _]]. exact HzN. }
    assert (H1F : 1 ∈ F).
    { apply AxiomII; split.
      - exists R; exact one_in_R_Co.
      - split; [exact one_in_N | apply Leq_P1; exact one_in_R_Co]. }
    assert (HFcl : ∀ x, x ∈ F -> (x + 1) ∈ F).
    { intros x Hx.
      apply AxiomII in Hx as [_ [HxN H1x]].
      assert (HxR : x ∈ R) by (apply N_Subset_R; exact HxN).
      assert (Hx1N : (x + 1) ∈ N) by (apply Hsucc; exact HxN).
      assert (Hlt : x < x + 1).
      { assert (Ht : 0 + x < 1 + x) by (apply (OrderPM_Co1 0 1 x zero_in_R one_in_R_Co HxR); exact OrderPM_Co9).
        rewrite (eq_trans (Plus_P4 0 x zero_in_R HxR) (Plus_P1 x HxR)) in Ht.
        rewrite (Plus_P4 1 x one_in_R_Co HxR) in Ht.
        exact Ht. }
      apply AxiomII; split.
      - exists R; exact (N_Subset_R (x + 1) Hx1N).
      - split; [exact Hx1N |].
        exact (Leq_P3 1 x (x + 1) one_in_R_Co HxR (Plus_close x 1 HxR one_in_R_Co) H1x (proj1 Hlt)). }
    assert (HF : F = N) by (apply (MathInd F HFsub H1F HFcl)).
    assert (HuF : u ∈ F) by (rewrite HF; exact Hu).
    apply AxiomII in HuF as [_ [_ H1u]].
    exact H1u. }
  assert (HW : ∀ k, k ∈ N -> ∀ E0, E0 ⊂ N -> E0 <> Φ -> (∀ x, x ∈ E0 -> x ≤ k)
      -> ∃ m, m ∈ E0 /\ (∀ x, x ∈ E0 -> m ≤ x)).
  { set (P := \{ λ k, k ∈ N /\ (∀ E0, E0 ⊂ N -> E0 <> Φ -> (∀ x, x ∈ E0 -> x ≤ k)
        -> ∃ m, m ∈ E0 /\ (∀ x, x ∈ E0 -> m ≤ x)) \}).
    assert (HPsub : P ⊂ N).
    { intros z Hz. apply AxiomII in Hz as [_ [HzN _]]. exact HzN. }
    assert (H1P : 1 ∈ P).
    { apply AxiomII; split.
      - exists R; exact one_in_R_Co.
      - split; [exact one_in_N |].
        intros E0 HE0 HE0ne Hbd.
        destruct (MKT_nonempty E0 HE0ne) as [x0 Hx0].
        assert (Hx0N : x0 ∈ N) by (apply HE0; exact Hx0).
        assert (Hx0R : x0 ∈ R) by (apply N_Subset_R; exact Hx0N).
        assert (Hx0le : x0 ≤ 1) by (exact (Hbd x0 Hx0)).
        assert (H1x0 : 1 ≤ x0) by (apply Hmin; exact Hx0N).
        assert (Heq : x0 = 1) by (apply (Leq_P2 x0 1 Hx0R one_in_R_Co Hx0le H1x0)).
        exists 1. split.
        + rewrite <- Heq. exact Hx0.
        + intros x Hx. apply Hmin. apply HE0. exact Hx. }
    assert (HPcl : ∀ k, k ∈ P -> (k + 1) ∈ P).
    { intros k Hk.
      apply AxiomII in Hk as [_ [HkN HWk]].
      assert (HkR : k ∈ R) by (apply N_Subset_R; exact HkN).
      assert (Hk1N : (k + 1) ∈ N) by (apply Hsucc; exact HkN).
      apply AxiomII; split.
      - exists R; exact (N_Subset_R (k + 1) Hk1N).
      - split; [exact Hk1N |].
        intros E0 HE0 HE0ne Hbd.
        set (E1 := \{ λ z, z ∈ E0 /\ z ≤ k \}).
        assert (HE1sub : E1 ⊂ N).
        { intros z Hz. apply AxiomII in Hz as [_ [HzE _]]. apply HE0; exact HzE. }
        destruct (classic (E1 ≠ Φ)) as [HE1ne | HE1eq].
        * assert (Hbd1 : ∀ z, z ∈ E1 -> z ≤ k).
          { intros z Hz. apply AxiomII in Hz as [_ [_ Hzle]]. exact Hzle. }
          destruct (HWk E1 HE1sub HE1ne Hbd1) as [m [HmE1 Hmmin]].
          apply AxiomII in HmE1 as [HmEns [HmE0 Hmlek]].
          assert (HmR : m ∈ R) by (apply N_Subset_R; apply HE0; exact HmE0).
          exists m. split.
          -- exact HmE0.
          -- intros x Hx.
             assert (HxN : x ∈ N) by (apply HE0; exact Hx).
             assert (HxR : x ∈ R) by (apply N_Subset_R; exact HxN).
             assert (Hxle : x ≤ k + 1) by (exact (Hbd x Hx)).
             destruct (Leq_P4 x k HxR HkR) as [Hxk | Hkx].
             ++ assert (HxE1 : x ∈ E1) by (apply AxiomII; split; [exists N; exact HxN | split; [exact Hx | exact Hxk]]).
                exact (Hmmin x HxE1).
             ++ exact (Leq_P3 m k x HmR HkR HxR Hmlek Hkx).
        * assert (HE1 : E1 = Φ) by (apply NNPP; exact HE1eq).
          destruct (MKT_nonempty E0 HE0ne) as [x0 Hx0].
          assert (Hx0N : x0 ∈ N) by (apply HE0; exact Hx0).
          assert (Hx0R : x0 ∈ R) by (apply N_Subset_R; exact Hx0N).
          assert (Hnotle : ~ (x0 ≤ k)).
          { intro Hx0lek.
            assert (Hx0E1 : x0 ∈ E1).
            { apply AxiomII; split.
              - exists N; exact Hx0N.
              - split; [exact Hx0 | exact Hx0lek]. }
            rewrite HE1 in Hx0E1. apply AxiomII in Hx0E1 as [Hx0Ens H0']. exact (H0' eq_refl). }
          assert (Hkltx0 : k < x0).
          { destruct (Leq_P4 k x0 HkR Hx0R) as [Hkx | Hxk].
            - split; [exact Hkx | intro Hke; apply Hnotle; rewrite Hke; apply Leq_P1; exact Hx0R].
            - exfalso. exact (Hnotle Hxk). }
          assert (Hk1le : (k + 1) ≤ x0) by (apply (Nat_P4 x0 k Hx0N HkN Hkltx0)).
          exists (k + 1). split.
          -- assert (Hx0eq : x0 = k + 1) by (apply (Leq_P2 x0 (k + 1) Hx0R (Plus_close k 1 HkR one_in_R_Co) (Hbd x0 Hx0) Hk1le)).
             rewrite <- Hx0eq. exact Hx0.
          -- intros x Hx.
             assert (HxN : x ∈ N) by (apply HE0; exact Hx).
             assert (HxR : x ∈ R) by (apply N_Subset_R; exact HxN).
             assert (Hnotle' : ~ (x ≤ k)).
             { intro Hxlek.
               assert (HxE1 : x ∈ E1) by (apply AxiomII; split; [exists N; exact HxN | split; [exact Hx | exact Hxlek]]).
               rewrite HE1 in HxE1. apply AxiomII in HxE1 as [HxEns H0']. exact (H0' eq_refl). }
             assert (Hkltx : k < x).
             { destruct (Leq_P4 k x HkR HxR) as [Hkx | Hxk].
               - split; [exact Hkx | intro Hke; apply Hnotle'; rewrite Hke; apply Leq_P1; exact HxR].
               - exfalso. exact (Hnotle' Hxk). }
             exact (Nat_P4 x k HxN HkN Hkltx). }
    assert (HP : P = N) by (apply (MathInd P HPsub H1P HPcl)).
    intros k Hk.
    assert (HkP : k ∈ P) by (rewrite HP; exact Hk).
    apply AxiomII in HkP as [_ [_ HWk]]. exact HWk. }
  destruct (MKT_nonempty E Hne) as [n0 Hn0].
  assert (Hn0N : n0 ∈ N) by (apply HE; exact Hn0).
  set (E' := \{ λ x, x ∈ E /\ x ≤ n0 \}).
  assert (HE'sub : E' ⊂ N).
  { intros z Hz. apply AxiomII in Hz as [_ [HzE _]]. apply HE; exact HzE. }
  assert (HE'ne : E' ≠ Φ).
  { intro H0.
    assert (Hn0E' : n0 ∈ E').
    { apply AxiomII; split.
      - exists N; exact Hn0N.
      - split; [exact Hn0 | apply Leq_P1; apply N_Subset_R; exact Hn0N]. }
    rewrite H0 in Hn0E'. apply AxiomII in Hn0E' as [E0 H0']. exact (H0' eq_refl). }
  assert (HE'bd : ∀ x, x ∈ E' -> x ≤ n0).
  { intros z Hz. apply AxiomII in Hz as [_ [_ Hzle]]. exact Hzle. }
  destruct (HW n0 Hn0N E' HE'sub HE'ne HE'bd) as [m [HmE' Hmmin]].
  apply AxiomII in HmE' as [HmEns [HmE Hmle]].
  exists m. unfold Min. split.
  - intros z Hz. apply N_Subset_R. apply HE. exact Hz.
  - split; [exact HmE |].
    intros x Hx.
    assert (HxN : x ∈ N) by (apply HE; exact Hx).
    assert (HxR : x ∈ R) by (apply N_Subset_R; exact HxN).
    assert (HmR : m ∈ R) by (apply N_Subset_R; apply HE; exact HmE).
    destruct (Leq_P4 x n0 HxR (N_Subset_R n0 Hn0N)) as [Hxn | Hnx].
    + assert (HxE' : x ∈ E') by (apply AxiomII; split; [exists N; exact HxN | split; [exact Hx | exact Hxn]]).
      exact (Hmmin x HxE').
    + exact (Leq_P3 m n0 x HmR (N_Subset_R n0 Hn0N) HxR Hmle Hnx).
Qed.

(* 整数的定义 *)
Definition Z := N ∪ \{ λ u, (-u) ∈ N \} ∪ [0].

(* 整数的性质 *)
Corollary N_Subset_Z : N ⊂ Z.
Proof.
  intros z Hz.
  unfold Z.
  apply MKT4. left. exact Hz.
Qed.

Corollary Z_Subset_R : Z ⊂ R.
Proof.
  intros z Hz.
  unfold Z in Hz.
  apply MKT4 in Hz as [HzN | Hz2].
  - apply N_Subset_R; exact HzN.
  - apply MKT4 in Hz2 as [HzA | Hz0].
    + apply AxiomII in HzA as [_ Hneg].
      apply (Plus_neg1b z). apply N_Subset_R; exact Hneg.
    + assert (E0 : Ensemble 0) by (exists R; exact zero_in_R).
      assert (Hzz : z = 0) by (apply (proj1 (MKT41 0 E0 z)); exact Hz0).
      rewrite Hzz. apply zero_in_R.
Qed.

Lemma Int_P1_Lemma : ∀ m n, m ∈ N -> n ∈ N -> m < n -> (n - m) ∈ N.
Proof.
  assert (HminN : ∀ u, u ∈ N -> 1 ≤ u).
  { intros u Hu. pose proof one_is_min_in_N as H. unfold Min in H. exact (proj2 (proj2 H) u Hu). }
  assert (Indsucc : ∀ x, x ∈ N -> (x + 1) ∈ N).
  { intros x Hx. pose proof IndSet_N as HIN. unfold IndSet in HIN. exact (proj2 HIN x Hx). }
  assert (neg_add1 : ∀ a, a ∈ R -> (-(a + 1)) = ((-a) + (-(1)))).
  { intros a Ha.
    assert (H1 : 1 ∈ R) by (apply one_in_R_Co).
    assert (H0 : 0 ∈ R) by (apply zero_in_R).
    assert (Hnega : -a ∈ R) by (apply (Plus_neg1a a Ha)).
    assert (Hneg1 : -(1) ∈ R) by (apply (Plus_neg1a 1 H1)).
    assert (Ha1 : (a + 1) ∈ R) by (apply (Plus_close a 1 Ha H1)).
    assert (HabR : ((-a) + (-(1))) ∈ R) by (apply (Plus_close (-a) (-(1)) Hnega Hneg1)).
    assert (Hmid : (a + 1) + (-a) = 1).
    { transitivity ((1 + a) + (-a)).
      - rewrite (Plus_P4 a 1 Ha H1). reflexivity.
      - transitivity (1 + (a + (-a))).
        + symmetry. apply (Plus_P3 1 a (-a) H1 Ha Hnega).
        + transitivity (1 + 0).
          * rewrite (Plus_neg2 a Ha). reflexivity.
          * apply (Plus_P1 1 H1). }
    assert (Hzero : (a + 1) + ((-a) + (-(1))) = 0).
    { transitivity (((a + 1) + (-a)) + (-(1))).
      - apply (Plus_P3 (a + 1) (-a) (-(1)) Ha1 Hnega Hneg1).
      - transitivity (1 + (-(1))).
        + rewrite Hmid. reflexivity.
        + apply (Plus_neg2 1 H1). }
    assert (Hres : ((-a) + (-(1))) = 0 + (-(a + 1)))
      by (apply (Plus_Co3 (a + 1) ((-a) + (-(1))) 0 Ha1 HabR H0 Hzero)).
    assert (H0y : 0 + (-(a + 1)) = -(a + 1))
      by (exact (eq_trans (Plus_P4 0 (-(a + 1)) H0 (Plus_neg1a (a + 1) Ha1))
                          (Plus_P1 (-(a + 1)) (Plus_neg1a (a + 1) Ha1)))).
    rewrite H0y in Hres. symmetry. exact Hres. }
  assert (pred_lt : ∀ a b, a ∈ N -> b ∈ N -> a + 1 < b -> a < b + (-(1))).
  { intros a b HaN HbN Hlt.
    assert (HaR : a ∈ R) by (apply N_Subset_R; exact HaN).
    assert (HbR : b ∈ R) by (apply N_Subset_R; exact HbN).
    assert (H1 : 1 ∈ R) by (apply one_in_R_Co).
    assert (Hneg1 : -(1) ∈ R) by (apply (Plus_neg1a 1 H1)).
    assert (Hle1 : (a + 1) + (-(1)) ≤ b + (-(1)))
      by (apply (Plus_Leq (a + 1) b (-(1)) (Plus_close a 1 HaR H1) HbR Hneg1 (proj1 Hlt))).
    assert (Heq1 : (a + 1) + (-(1)) = a).
    { transitivity (a + (1 + (-(1)))).
      - symmetry. apply (Plus_P3 a 1 (-(1)) HaR H1 Hneg1).
      - transitivity (a + 0).
        + rewrite (Plus_neg2 1 H1). reflexivity.
        + apply (Plus_P1 a HaR). }
    rewrite Heq1 in Hle1.
    split; [exact Hle1 |].
    intro Heq.
    apply (proj2 Hlt).
    rewrite Heq.
    transitivity (b + ((-(1)) + 1)).
    - symmetry. apply (Plus_P3 b (-(1)) 1 HbR Hneg1 H1).
    - transitivity (b + 0).
      + rewrite (eq_trans (Plus_P4 (-(1)) 1 Hneg1 H1) (Plus_neg2 1 H1)). reflexivity.
      + apply (Plus_P1 b HbR). }
  intros m0 n0 Hm0 Hn0 Hlt0.
  set (E := \{ λ k, k ∈ N /\ (∀ n, n ∈ N -> k < n -> (n + (-k)) ∈ N) \}).
  assert (HEsub : E ⊂ N).
  { intros z Hz. apply AxiomII in Hz as [_ [HzN _]]. exact HzN. }
  assert (H1E : 1 ∈ E).
  { apply AxiomII; split.
    - exists R; exact one_in_R_Co.
    - split; [exact one_in_N |].
      intros n Hn Hlt.
      assert (Hn1 : n <> 1) by (intro Heq; apply (proj2 Hlt); exact (eq_sym Heq)).
      exact (Nat_P2 n Hn Hn1). }
  assert (HEcl : ∀ k, k ∈ E -> (k + 1) ∈ E).
  { intros k HkE.
    apply AxiomII in HkE as [_ [HkN Hprop]].
    assert (HkR : k ∈ R) by (apply N_Subset_R; exact HkN).
    assert (Hk1N : (k + 1) ∈ N) by (apply Indsucc; exact HkN).
    assert (H1 : 1 ∈ R) by (apply one_in_R_Co).
    assert (Hneg1 : -(1) ∈ R) by (apply (Plus_neg1a 1 H1)).
    apply AxiomII; split.
    - exists R; exact (N_Subset_R (k + 1) Hk1N).
    - split; [exact Hk1N |].
      intros n Hn Hlt.
      assert (Hn1 : n <> 1).
      { intro Heq.
        assert (Hk1le : 1 ≤ k + 1) by (apply HminN; exact Hk1N).
        assert (Hk1R : (k + 1) ∈ R) by (apply N_Subset_R; exact Hk1N).
        rewrite Heq in Hlt.
        assert (Hk1le1 : (k + 1) ≤ 1) by (exact (proj1 Hlt)).
        exact (proj2 Hlt (Leq_P2 (k + 1) 1 Hk1R H1 Hk1le1 Hk1le)). }
      assert (Hnm1N : n + (-(1)) ∈ N) by (apply (Nat_P2 n Hn Hn1)).
      assert (Hmlt : k < n + (-(1))) by (apply (pred_lt k n HkN Hn Hlt)).
      assert (HIH : (n + (-(1))) + (-k) ∈ N) by (apply Hprop; [exact Hnm1N | exact Hmlt]).
      assert (Hna : -(k + 1) = (-k) + (-(1))) by (apply (neg_add1 k HkR)).
      assert (Heq_goal : n + (-(k + 1)) = (n + (-(1))) + (-k)).
      { rewrite Hna.
        transitivity (n + ((-(1)) + (-k))).
        - rewrite (Plus_P4 (-k) (-(1)) (Plus_neg1a k HkR) Hneg1). reflexivity.
        - apply (Plus_P3 n (-(1)) (-k) (N_Subset_R n Hn) Hneg1 (Plus_neg1a k HkR)). }
      rewrite Heq_goal. exact HIH. }
  assert (HE : E = N) by (apply (MathInd E HEsub H1E HEcl)).
  assert (Hm0E : m0 ∈ E) by (rewrite HE; exact Hm0).
  apply AxiomII in Hm0E as [_ [_ Hprop0]].
  exact (Hprop0 n0 Hn0 Hlt0).
Qed.

Proposition Int_P1a : ∀ m n, m ∈ Z -> n ∈ Z -> (m + n) ∈ Z.
Proof.
  assert (dblneg : ∀ a, a ∈ R -> -(-a) = a).
  { intros a Ha.
    assert (Hnega : -a ∈ R) by (apply (Plus_neg1a a Ha)).
    assert (H1 : (-a) + a = 0) by (exact (eq_trans (Plus_P4 (-a) a Hnega Ha) (Plus_neg2 a Ha))).
    assert (H2 : (-a) + (-(-a)) = 0) by (apply (Plus_neg2 (-a) Hnega)).
    destruct (Plus_Co2 (-a) Hnega) as [x0 [[_ _] Huniq]].
    assert (He1 : x0 = a) by (exact (Huniq a (conj Ha H1))).
    assert (He2 : x0 = -(-a)) by (exact (Huniq (-(-a)) (conj (Plus_neg1a (-a) Hnega) H2))).
    rewrite <- He2. exact He1. }
  assert (neg_add : ∀ a b, a ∈ R -> b ∈ R -> -(a + b) = (-a) + (-b)).
  { intros a b Ha Hb.
    assert (Hnega : -a ∈ R) by (apply (Plus_neg1a a Ha)).
    assert (Hnegb : -b ∈ R) by (apply (Plus_neg1a b Hb)).
    assert (Hab : (a + b) ∈ R) by (apply (Plus_close a b Ha Hb)).
    assert (HsumR : ((-a) + (-b)) ∈ R) by (apply (Plus_close (-a) (-b) Hnega Hnegb)).
    assert (H0 : 0 ∈ R) by (apply zero_in_R).
    assert (Hzero : (a + b) + ((-a) + (-b)) = 0).
    { transitivity (((a + b) + (-a)) + (-b)).
      - apply (Plus_P3 (a + b) (-a) (-b) Hab Hnega Hnegb).
      - assert (Hmid : (a + b) + (-a) = b).
        { transitivity ((b + a) + (-a)).
          - rewrite (Plus_P4 a b Ha Hb). reflexivity.
          - transitivity (b + (a + (-a))).
            + symmetry. apply (Plus_P3 b a (-a) Hb Ha Hnega).
            + transitivity (b + 0).
              * rewrite (Plus_neg2 a Ha). reflexivity.
              * apply (Plus_P1 b Hb). }
        rewrite Hmid. apply (Plus_neg2 b Hb). }
    assert (Hres : ((-a) + (-b)) = 0 + (-(a + b)))
      by (apply (Plus_Co3 (a + b) ((-a) + (-b)) 0 Hab HsumR H0 Hzero)).
    assert (H0y : 0 + (-(a + b)) = -(a + b))
      by (exact (eq_trans (Plus_P4 0 (-(a + b)) H0 (Plus_neg1a (a + b) Hab))
                          (Plus_P1 (-(a + b)) (Plus_neg1a (a + b) Hab)))).
    rewrite H0y in Hres. symmetry. exact Hres. }
  assert (ZN : ∀ z, z ∈ N -> z ∈ Z) by (intros z Hz; apply N_Subset_Z; exact Hz).
  assert (ZnegN : ∀ z, (-z) ∈ N -> z ∈ Z).
  { intros z Hz. unfold Z. apply MKT4. right. apply MKT4. left. apply AxiomII; split.
    - exists R; apply (Plus_neg1b z); apply N_Subset_R; exact Hz.
    - exact Hz. }
  assert (Zzero : 0 ∈ Z).
  { unfold Z. apply MKT4. right. apply MKT4. right.
    assert (H0 : 0 ∈ R) by (apply zero_in_R).
    assert (E0 : Ensemble 0) by (exists R; exact H0).
    apply (proj2 (MKT41 0 E0 0)). reflexivity. }
  assert (HNN : ∀ m n, m ∈ N -> (-n) ∈ N -> (m + n) ∈ Z).
  { intros m n Hm Hneg.
    assert (HmR : m ∈ R) by (apply N_Subset_R; exact Hm).
    assert (HnegR : (-n) ∈ R) by (apply N_Subset_R; exact Hneg).
    assert (HnR : n ∈ R) by (apply (Plus_neg1b n); apply N_Subset_R; exact Hneg).
    destruct (Leq_P4 (-n) m HnegR HmR) as [Hle | Hle].
    - destruct (classic ((-n) = m)) as [Heq | Hne].
      + assert (Hsum : m + n = 0).
        { rewrite <- Heq. exact (eq_trans (Plus_P4 (-n) n HnegR HnR) (Plus_neg2 n HnR)). }
        rewrite Hsum. exact Zzero.
      + assert (Hlt : (-n) < m) by (split; [exact Hle | exact Hne]).
        assert (Hsub : m - (-n) ∈ N) by (apply (Int_P1_Lemma (-n) m Hneg Hm Hlt)).
        apply ZN. rewrite <- (dblneg n HnR). exact Hsub.
    - destruct (classic (m = (-n))) as [Heq | Hne].
      + assert (Hsum : m + n = 0).
        { rewrite Heq. exact (eq_trans (Plus_P4 (-n) n HnegR HnR) (Plus_neg2 n HnR)). }
        rewrite Hsum. exact Zzero.
      + assert (Hlt : m < -n) by (split; [exact Hle | exact Hne]).
        assert (Hsub : (-n) - m ∈ N) by (apply (Int_P1_Lemma m (-n) Hm Hneg Hlt)).
        assert (Heq2 : -(m + n) = (-n) + (-m))
          by (exact (eq_trans (neg_add m n HmR HnR) (Plus_P4 (-m) (-n) (Plus_neg1a m HmR) (Plus_neg1a n HnR)))).
        apply ZnegN. rewrite Heq2. exact Hsub. }
  assert (NNN : ∀ m n, (-m) ∈ N -> n ∈ N -> (m + n) ∈ Z).
  { intros m n Hneg Hn.
    assert (HmR : m ∈ R) by (apply (Plus_neg1b m); apply N_Subset_R; exact Hneg).
    assert (HnR : n ∈ R) by (apply N_Subset_R; exact Hn).
    assert (Hcomm : m + n = n + m) by (apply (Plus_P4 m n HmR HnR)).
    rewrite Hcomm. apply HNN; [exact Hn | exact Hneg]. }
  assert (NegNeg : ∀ m n, (-m) ∈ N -> (-n) ∈ N -> (m + n) ∈ Z).
  { intros m n Hnegm Hnegn.
    assert (HmR : m ∈ R) by (apply (Plus_neg1b m); apply N_Subset_R; exact Hnegm).
    assert (HnR : n ∈ R) by (apply (Plus_neg1b n); apply N_Subset_R; exact Hnegn).
    assert (Hsum : ((-m) + (-n)) ∈ N) by (apply (Nat_P1a (-m) (-n) Hnegm Hnegn)).
    assert (Heq : -(m + n) = (-m) + (-n)) by (apply neg_add; assumption).
    apply ZnegN. rewrite Heq. exact Hsum. }
  intros m n Hm Hn.
  assert (HmR : m ∈ R) by (apply Z_Subset_R; exact Hm).
  assert (HnR : n ∈ R) by (apply Z_Subset_R; exact Hn).
  assert (H0 : 0 ∈ R) by (apply zero_in_R).
  assert (E0 : Ensemble 0) by (exists R; exact H0).
  unfold Z in Hm. apply MKT4 in Hm as [HmN | HmRest].
  - apply MKT4 in Hn as [HnN | HnRest].
    + apply ZN. apply (Nat_P1a m n HmN HnN).
    + apply MKT4 in HnRest as [HnM0 | Hn0].
      * apply AxiomII in HnM0 as [_ HnM]. apply HNN; [exact HmN | exact HnM].
      * rewrite (proj1 (MKT41 0 E0 n) Hn0). rewrite (Plus_P1 m HmR). apply ZN. exact HmN.
  - apply MKT4 in HmRest as [HmM0 | Hm0].
    + apply AxiomII in HmM0 as [_ HmM].
      apply MKT4 in Hn as [HnN | HnRest].
      * apply NNN; [exact HmM | exact HnN].
      * apply MKT4 in HnRest as [HnM0 | Hn0].
        -- apply AxiomII in HnM0 as [_ HnM]. apply NegNeg; [exact HmM | exact HnM].
        -- rewrite (proj1 (MKT41 0 E0 n) Hn0). rewrite (Plus_P1 m HmR). apply ZnegN. exact HmM.
    + rewrite (proj1 (MKT41 0 E0 m) Hm0).
      apply MKT4 in Hn as [HnN | HnRest].
      * rewrite (eq_trans (Plus_P4 0 n H0 HnR) (Plus_P1 n HnR)). apply ZN. exact HnN.
      * apply MKT4 in HnRest as [HnM0 | Hn0].
        -- apply AxiomII in HnM0 as [_ HnM]. rewrite (eq_trans (Plus_P4 0 n H0 HnR) (Plus_P1 n HnR)). apply ZnegN. exact HnM.
        -- rewrite (proj1 (MKT41 0 E0 n) Hn0). rewrite (Plus_P1 0 H0). exact Zzero.
Qed.

Proposition Int_P1b : ∀ m n, m ∈ Z -> n ∈ Z -> (m · n) ∈ Z.
Proof.
  assert (dblneg : ∀ a, a ∈ R -> -(-a) = a).
  { intros a Ha.
    assert (Hnega : -a ∈ R) by (apply (Plus_neg1a a Ha)).
    assert (H1 : (-a) + a = 0) by (exact (eq_trans (Plus_P4 (-a) a Hnega Ha) (Plus_neg2 a Ha))).
    assert (H2 : (-a) + (-(-a)) = 0) by (apply (Plus_neg2 (-a) Hnega)).
    destruct (Plus_Co2 (-a) Hnega) as [x0 [[_ _] Huniq]].
    assert (He1 : x0 = a) by (exact (Huniq a (conj Ha H1))).
    assert (He2 : x0 = -(-a)) by (exact (Huniq (-(-a)) (conj (Plus_neg1a (-a) Hnega) H2))).
    rewrite <- He2. exact He1. }
  assert (neg_multR : ∀ a b, a ∈ R -> b ∈ R -> -(a · b) = a · (-b)).
  { intros a b Ha Hb.
    assert (Hnegb : -b ∈ R) by (apply (Plus_neg1a b Hb)).
    assert (Hab : a · b ∈ R) by (apply (Mult_close a b Ha Hb)).
    assert (Hanb : a · (-b) ∈ R) by (apply (Mult_close a (-b) Ha Hnegb)).
    assert (H0 : 0 ∈ R) by (apply zero_in_R).
    assert (Hsum : a · b + a · (-b) = 0).
    { transitivity (b · a + (-b) · a).
      - rewrite (Mult_P4 a b Ha Hb). rewrite (Mult_P4 a (-b) Ha Hnegb). reflexivity.
      - transitivity ((b + (-b)) · a).
        + symmetry. apply (Mult_P5 b (-b) a Hb Hnegb Ha).
        + transitivity (0 · a).
          * rewrite (Plus_neg2 b Hb). reflexivity.
          * transitivity (a · 0).
            -- apply (Mult_P4 0 a H0 Ha).
            -- apply (PlusMult_Co1 a Ha). }
    assert (Hres : a · (-b) = 0 + (-(a · b)))
      by (apply (Plus_Co3 (a · b) (a · (-b)) 0 Hab Hanb H0 Hsum)).
    assert (Hfull : a · (-b) = -(a · b))
      by (exact (eq_trans Hres (eq_trans (Plus_P4 0 (-(a · b)) H0 (Plus_neg1a (a · b) Hab))
                                          (Plus_P1 (-(a · b)) (Plus_neg1a (a · b) Hab))))).
    symmetry. exact Hfull. }
  assert (neg_multL : ∀ a b, a ∈ R -> b ∈ R -> -(a · b) = (-a) · b).
  { intros a b Ha Hb.
    assert (Hba : a · b = b · a) by (apply (Mult_P4 a b Ha Hb)).
    rewrite Hba.
    rewrite (neg_multR b a Hb Ha).
    rewrite (Mult_P4 b (-a) Hb (Plus_neg1a a Ha)).
    reflexivity. }
  assert (ZN : ∀ z, z ∈ N -> z ∈ Z) by (intros z Hz; apply N_Subset_Z; exact Hz).
  assert (ZnegN : ∀ z, (-z) ∈ N -> z ∈ Z).
  { intros z Hz. unfold Z. apply MKT4. right. apply MKT4. left. apply AxiomII; split.
    - exists R; apply (Plus_neg1b z); apply N_Subset_R; exact Hz.
    - exact Hz. }
  assert (Zzero : 0 ∈ Z).
  { unfold Z. apply MKT4. right. apply MKT4. right.
    assert (H0 : 0 ∈ R) by (apply zero_in_R).
    assert (E0 : Ensemble 0) by (exists R; exact H0).
    apply (proj2 (MKT41 0 E0 0)). reflexivity. }
  assert (ZpN : ∀ m n, m ∈ N -> n ∈ N -> (m · n) ∈ Z).
  { intros m n Hm Hn. apply ZN. apply (Nat_P1b m n Hm Hn). }
  assert (ZpN0 : ∀ m n, m ∈ N -> (-n) ∈ N -> (m · n) ∈ Z).
  { intros m n Hm Hneg.
    assert (HmR : m ∈ R) by (apply N_Subset_R; exact Hm).
    assert (HnR : n ∈ R) by (apply (Plus_neg1b n); apply N_Subset_R; exact Hneg).
    assert (Hpos : m · (-n) ∈ N) by (apply (Nat_P1b m (-n) Hm Hneg)).
    assert (Heq : -(m · n) = m · (-n)) by (apply (neg_multR m n HmR HnR)).
    apply ZnegN. rewrite Heq. exact Hpos. }
  assert (ZpN0r : ∀ m n, (-m) ∈ N -> n ∈ N -> (m · n) ∈ Z).
  { intros m n Hneg Hn.
    assert (HmR : m ∈ R) by (apply (Plus_neg1b m); apply N_Subset_R; exact Hneg).
    assert (HnR : n ∈ R) by (apply N_Subset_R; exact Hn).
    assert (Hpos : (-m) · n ∈ N) by (apply (Nat_P1b (-m) n Hneg Hn)).
    assert (Heq : -(m · n) = (-m) · n) by (apply (neg_multL m n HmR HnR)).
    apply ZnegN. rewrite Heq. exact Hpos. }
  assert (ZpNegNeg : ∀ m n, (-m) ∈ N -> (-n) ∈ N -> (m · n) ∈ Z).
  { intros m n Hnegm Hnegn.
    assert (HmR : m ∈ R) by (apply (Plus_neg1b m); apply N_Subset_R; exact Hnegm).
    assert (HnR : n ∈ R) by (apply (Plus_neg1b n); apply N_Subset_R; exact Hnegn).
    assert (HnegmR : (-m) ∈ R) by (apply N_Subset_R; exact Hnegm).
    assert (HmnR : (m · n) ∈ R) by (apply (Mult_close m n HmR HnR)).
    assert (Hpos : (-m) · (-n) ∈ N) by (apply (Nat_P1b (-m) (-n) Hnegm Hnegn)).
    assert (Heq : (-m) · (-n) = m · n).
    { assert (H1 : -((-m) · n) = (-m) · (-n)) by (apply (neg_multR (-m) n HnegmR HnR)).
      assert (H2 : (-m) · n = -(m · n)) by (symmetry; apply (neg_multL m n HmR HnR)).
      rewrite <- H1. rewrite H2. apply (dblneg (m · n) HmnR). }
    apply ZN. rewrite <- Heq. exact Hpos. }
  intros m n Hm Hn.
  assert (HmR : m ∈ R) by (apply Z_Subset_R; exact Hm).
  assert (HnR : n ∈ R) by (apply Z_Subset_R; exact Hn).
  assert (H0 : 0 ∈ R) by (apply zero_in_R).
  assert (E0 : Ensemble 0) by (exists R; exact H0).
  unfold Z in Hm. apply MKT4 in Hm as [HmN | HmRest].
  - apply MKT4 in Hn as [HnN | HnRest].
    + apply ZpN; assumption.
    + apply MKT4 in HnRest as [HnM0 | Hn0].
      * apply AxiomII in HnM0 as [_ HnM]. apply ZpN0; [exact HmN | exact HnM].
      * rewrite (proj1 (MKT41 0 E0 n) Hn0). rewrite (PlusMult_Co1 m HmR). exact Zzero.
  - apply MKT4 in HmRest as [HmM0 | Hm0].
    + apply AxiomII in HmM0 as [_ HmM].
      apply MKT4 in Hn as [HnN | HnRest].
      * apply ZpN0r; [exact HmM | exact HnN].
      * apply MKT4 in HnRest as [HnM0 | Hn0].
        -- apply AxiomII in HnM0 as [_ HnM]. apply ZpNegNeg; [exact HmM | exact HnM].
        -- rewrite (proj1 (MKT41 0 E0 n) Hn0). rewrite (PlusMult_Co1 m HmR). exact Zzero.
    + rewrite (proj1 (MKT41 0 E0 m) Hm0).
      apply MKT4 in Hn as [HnN | HnRest].
      * rewrite (Mult_P4 0 n H0 HnR). rewrite (PlusMult_Co1 n HnR). exact Zzero.
      * apply MKT4 in HnRest as [HnM0 | Hn0].
        -- rewrite (Mult_P4 0 n H0 HnR). rewrite (PlusMult_Co1 n HnR). exact Zzero.
        -- rewrite (proj1 (MKT41 0 E0 n) Hn0). rewrite (PlusMult_Co1 0 H0). exact Zzero.
Qed.

Proposition Int_P2 : ∀ n, n ∈ Z -> n + 0 = n /\ 0 + n = n.
Proof.
  intros n Hn.
  assert (HnR : n ∈ R) by (apply Z_Subset_R; exact Hn).
  assert (H0 : 0 ∈ R) by (apply zero_in_R).
  split.
  - apply (Plus_P1 n HnR).
  - exact (eq_trans (Plus_P4 0 n H0 HnR) (Plus_P1 n HnR)).
Qed.

Proposition Int_P3 : ∀ n, n ∈ Z -> (-n) ∈ Z /\ n + (-n) = 0 /\ (-n) + n = 0.
Proof.
  intros n Hn.
  assert (dblneg : ∀ a, a ∈ R -> -(-a) = a).
  { intros a Ha.
    assert (Hnega : -a ∈ R) by (apply (Plus_neg1a a Ha)).
    assert (H1 : (-a) + a = 0) by (exact (eq_trans (Plus_P4 (-a) a Hnega Ha) (Plus_neg2 a Ha))).
    assert (H2 : (-a) + (-(-a)) = 0) by (apply (Plus_neg2 (-a) Hnega)).
    destruct (Plus_Co2 (-a) Hnega) as [x0 [[_ _] Huniq]].
    assert (He1 : x0 = a) by (exact (Huniq a (conj Ha H1))).
    assert (He2 : x0 = -(-a)) by (exact (Huniq (-(-a)) (conj (Plus_neg1a (-a) Hnega) H2))).
    rewrite <- He2. exact He1. }
  assert (neg_zero : -0 = 0).
  { assert (H0 : 0 ∈ R) by (apply zero_in_R).
    assert (Hne0 : -0 ∈ R) by (apply (Plus_neg1a 0 H0)).
    destruct (Plus_Co2 0 H0) as [x0 [[_ _] Huniq]].
    assert (He1 : x0 = -0) by (exact (Huniq (-0) (conj Hne0 (Plus_neg2 0 H0)))).
    assert (He2 : x0 = 0) by (exact (Huniq 0 (conj H0 (Plus_P1 0 H0)))).
    rewrite <- He1. exact He2. }
  assert (HnR : n ∈ R) by (apply Z_Subset_R; exact Hn).
  assert (H0 : 0 ∈ R) by (apply zero_in_R).
  assert (E0 : Ensemble 0) by (exists R; exact H0).
  assert (Hnegn : -n ∈ R) by (apply (Plus_neg1a n HnR)).
  split; [| split].
  - unfold Z in Hn. apply MKT4 in Hn as [HnN | HnRest].
    + unfold Z. apply MKT4. right. apply MKT4. left. apply AxiomII; split.
      { exists R; exact Hnegn. }
      { rewrite (dblneg n HnR). exact HnN. }
    + apply MKT4 in HnRest as [HnNeg | Hn0].
      * unfold Z. apply MKT4. left. apply AxiomII in HnNeg as [_ HnegN]. exact HnegN.
      * assert (Hnz : n = 0) by (exact (proj1 (MKT41 0 E0 n) Hn0)).
        rewrite Hnz. rewrite neg_zero. unfold Z. apply MKT4. right. apply MKT4. right.
        apply (proj2 (MKT41 0 E0 0)). reflexivity.
  - apply (Plus_neg2 n HnR).
  - rewrite (Plus_P4 (-n) n Hnegn HnR). apply (Plus_neg2 n HnR).
Qed.

Proposition Int_P4 : ∀ m n k, m ∈ Z -> n ∈ Z -> k ∈ Z
  -> m + (n + k) = (m + n) + k.
Proof.
  intros m n k Hm Hn Hk.
  assert (HmR : m ∈ R) by (apply Z_Subset_R; exact Hm).
  assert (HnR : n ∈ R) by (apply Z_Subset_R; exact Hn).
  assert (HkR : k ∈ R) by (apply Z_Subset_R; exact Hk).
  apply (Plus_P3 m n k HmR HnR HkR).
Qed.

Proposition Int_P5 : ∀ m n, m ∈ Z -> n ∈ Z -> m + n = n + m.
Proof.
  intros m n Hm Hn.
  assert (HmR : m ∈ R) by (apply Z_Subset_R; exact Hm).
  assert (HnR : n ∈ R) by (apply Z_Subset_R; exact Hn).
  apply (Plus_P4 m n HmR HnR).
Qed.

(* 有理数的定义 *)
Definition Q := \{ λ u, ∃ m n, m ∈ Z /\ n ∈ (Z ~ [0]) /\ u = m / n \}.

Corollary Z_Subset_Q : Z ⊂ Q.
Proof.
  intros z Hz.
  assert (HzR : z ∈ R) by (apply Z_Subset_R; exact Hz).
  assert (H1Z : 1 ∈ Z) by (apply N_Subset_Z; apply one_in_N).
  assert (H1R : 1 ∈ R) by (apply one_in_R_Co).
  assert (H1R0 : 1 ∈ (R ~ [0])) by (apply one_in_R).
  assert (H1not0 : 1 ∉ [0]).
  { pose proof H1R0 as H. unfold Setminus in H. apply AxiomII in H as [_ [_ Hnot]].
    apply AxiomII in Hnot as [_ Hnot']. exact Hnot'. }
  assert (H1Z0 : 1 ∈ (Z ~ [0])).
  { unfold Setminus. apply AxiomII; split.
    - exists R; exact H1R.
    - split; [exact H1Z | apply AxiomII; split; [exists R; exact H1R | exact H1not0]]. }
  apply AxiomII; split.
  - exists R; exact HzR.
  - exists z, 1. split; [exact Hz | split; [exact H1Z0 | symmetry; apply (Divide_P2 z HzR)]].
Qed.

Corollary Q_Subset_R : Q ⊂ R.
Proof.
  intros x Hx.
  assert (Z0_to_R0 : ∀ n, n ∈ (Z ~ [0]) -> n ∈ (R ~ [0])).
  { intros n Hn. unfold Setminus in Hn. apply AxiomII in Hn as [En [HnZ Hnnot]].
    unfold Setminus. apply AxiomII; split.
    - exact En.
    - split; [apply Z_Subset_R; exact HnZ | exact Hnnot]. }
  apply AxiomII in Hx as [Ex [m [n [HmZ [HnZ0 Hxeq]]]]].
  rewrite Hxeq.
  assert (HmR : m ∈ R) by (apply Z_Subset_R; exact HmZ).
  assert (HnR0 : n ∈ (R ~ [0])) by (apply Z0_to_R0; exact HnZ0).
  assert (HninvR : (n⁻) ∈ R).
  { pose proof (Mult_inv1 n HnR0) as H. unfold Setminus in H. apply AxiomII in H as [_ [HninvR _]]. exact HninvR. }
  apply (Mult_close m (n⁻) HmR HninvR).
Qed.

Proposition Frac_P1 : ∀ m n k, m ∈ R -> n ∈ (R ~ [0])
  -> k ∈ (R ~ [0]) -> m / n = (m · k) / (n · k).
Proof.
  intros m n k Hm Hn Hk.
  assert (R0_mul : ∀ a b, a ∈ (R ~ [0]) -> b ∈ (R ~ [0]) -> (a · b) ∈ (R ~ [0])).
  { intros a b Ha Hb.
    unfold Setminus in Ha. apply AxiomII in Ha as [Ea [HaR Hanot]]. apply AxiomII in Hanot as [_ Hanot'].
    unfold Setminus in Hb. apply AxiomII in Hb as [Eb [HbR Hbnot]]. apply AxiomII in Hbnot as [_ Hbnot'].
    assert (H0 : 0 ∈ R) by (apply zero_in_R).
    assert (E0 : Ensemble 0) by (exists R; exact H0).
    assert (HabR : (a · b) ∈ R) by (apply (Mult_close a b HaR HbR)).
    assert (Habne : a · b ≠ 0).
    { intro Heq. destruct (PlusMult_Co2 a b HaR HbR Heq) as [Ha0 | Hb0].
      - exact (Hanot' (proj2 (MKT41 0 E0 a) Ha0)).
      - exact (Hbnot' (proj2 (MKT41 0 E0 b) Hb0)). }
    assert (Habnot : (a · b) ∉ [0]) by (intro Habs; exact (Habne (proj1 (MKT41 0 E0 (a · b)) Habs))).
    unfold Setminus. apply AxiomII; split.
    - exists R; exact HabR.
    - split; [exact HabR | apply AxiomII; split; [exists R; exact HabR | exact Habnot]]. }
  assert (HnR : n ∈ R). { pose proof Hn as H. unfold Setminus in H. apply AxiomII in H as [_ [HnR _]]. exact HnR. }
  assert (HkR : k ∈ R). { pose proof Hk as H. unfold Setminus in H. apply AxiomII in H as [_ [HkR _]]. exact HkR. }
  assert (HninvR : (n⁻) ∈ R).
  { pose proof (Mult_inv1 n Hn) as H. unfold Setminus in H. apply AxiomII in H as [_ [HninvR _]]. exact HninvR. }
  assert (HnkR0 : (n · k) ∈ (R ~ [0])) by (apply (R0_mul n k Hn Hk)).
  assert (HnkR : (n · k) ∈ R).
  { pose proof HnkR0 as H. unfold Setminus in H. apply AxiomII in H as [_ [HnkR _]]. exact HnkR. }
  assert (HmnR : (m · (n⁻)) ∈ R) by (apply (Mult_close m (n⁻) Hm HninvR)).
  assert (HmkR : (m · k) ∈ R) by (apply (Mult_close m k Hm HkR)).
  assert (Hkey : (n · k) · (m · (n⁻)) = m · k).
  { transitivity (((n · k) · m) · (n⁻)).
    { apply (Mult_P3 (n · k) m (n⁻) HnkR Hm HninvR). }
    transitivity ((m · (n · k)) · (n⁻)).
    { rewrite (Mult_P4 (n · k) m HnkR Hm). reflexivity. }
    transitivity (m · ((n · k) · (n⁻))).
    { symmetry. apply (Mult_P3 m (n · k) (n⁻) Hm HnkR HninvR). }
    transitivity (m · (n · (k · (n⁻)))).
    { rewrite (Mult_P3 n k (n⁻) HnR HkR HninvR). reflexivity. }
    transitivity (m · (n · ((n⁻) · k))).
    { rewrite (Mult_P4 k (n⁻) HkR HninvR). reflexivity. }
    transitivity (m · ((n · (n⁻)) · k)).
    { rewrite (Mult_P3 n (n⁻) k HnR HninvR HkR). reflexivity. }
    transitivity (m · (1 · k)).
    { rewrite (Mult_inv2 n Hn). reflexivity. }
    rewrite (Mult_P4 1 k one_in_R_Co HkR). rewrite (Mult_P1 k HkR). reflexivity. }
  apply (Mult_Co3 (n · k) (m · (n⁻)) (m · k) HnkR0 HmnR HmkR Hkey).
Qed.

Proposition Frac_P2 : ∀ m n k t, m ∈ R -> n ∈ (R ~ [0])
  -> k ∈ R -> t ∈ (R ~ [0]) -> (m / n) · (k / t) = (m · k) / (n · t).
Proof.
  intros m n k t Hm Hn Hk Ht.
  assert (R0_mul : ∀ a b, a ∈ (R ~ [0]) -> b ∈ (R ~ [0]) -> (a · b) ∈ (R ~ [0])).
  { intros a b Ha Hb.
    unfold Setminus in Ha. apply AxiomII in Ha as [Ea [HaR Hanot]]. apply AxiomII in Hanot as [_ Hanot'].
    unfold Setminus in Hb. apply AxiomII in Hb as [Eb [HbR Hbnot]]. apply AxiomII in Hbnot as [_ Hbnot'].
    assert (H0 : 0 ∈ R) by (apply zero_in_R).
    assert (E0 : Ensemble 0) by (exists R; exact H0).
    assert (HabR : (a · b) ∈ R) by (apply (Mult_close a b HaR HbR)).
    assert (Habne : a · b ≠ 0).
    { intro Heq. destruct (PlusMult_Co2 a b HaR HbR Heq) as [Ha0 | Hb0].
      - exact (Hanot' (proj2 (MKT41 0 E0 a) Ha0)).
      - exact (Hbnot' (proj2 (MKT41 0 E0 b) Hb0)). }
    assert (Habnot : (a · b) ∉ [0]) by (intro Habs; exact (Habne (proj1 (MKT41 0 E0 (a · b)) Habs))).
    unfold Setminus. apply AxiomII; split.
    - exists R; exact HabR.
    - split; [exact HabR | apply AxiomII; split; [exists R; exact HabR | exact Habnot]]. }
  assert (HnR : n ∈ R). { pose proof Hn as H. unfold Setminus in H. apply AxiomII in H as [_ [HnR _]]. exact HnR. }
  assert (HtR : t ∈ R). { pose proof Ht as H. unfold Setminus in H. apply AxiomII in H as [_ [HtR _]]. exact HtR. }
  assert (HninvR : (n⁻) ∈ R).
  { pose proof (Mult_inv1 n Hn) as H. unfold Setminus in H. apply AxiomII in H as [_ [HninvR _]]. exact HninvR. }
  assert (HtinvR : (t⁻) ∈ R).
  { pose proof (Mult_inv1 t Ht) as H. unfold Setminus in H. apply AxiomII in H as [_ [HtinvR _]]. exact HtinvR. }
  assert (HntR0 : (n · t) ∈ (R ~ [0])) by (apply (R0_mul n t Hn Ht)).
  assert (HntR : (n · t) ∈ R).
  { pose proof HntR0 as H. unfold Setminus in H. apply AxiomII in H as [_ [HntR _]]. exact HntR. }
  assert (HmnR : (m · (n⁻)) ∈ R) by (apply (Mult_close m (n⁻) Hm HninvR)).
  assert (HktR : (k · (t⁻)) ∈ R) by (apply (Mult_close k (t⁻) Hk HtinvR)).
  assert (HlhsR : ((m · (n⁻)) · (k · (t⁻))) ∈ R)
    by (apply (Mult_close (m · (n⁻)) (k · (t⁻)) HmnR HktR)).
  assert (HmkR : (m · k) ∈ R) by (apply (Mult_close m k Hm Hk)).
  assert (HmtR : (m · t) ∈ R) by (apply (Mult_close m t Hm HtR)).
  assert (Hst1 : (n · t) · (m · (n⁻)) = m · t).
  { transitivity ((t · n) · (m · (n⁻))).
    { rewrite (Mult_P4 n t HnR HtR). reflexivity. }
    transitivity (t · (n · (m · (n⁻)))).
    { symmetry. apply (Mult_P3 t n (m · (n⁻)) HtR HnR HmnR). }
    transitivity (t · ((n · m) · (n⁻))).
    { rewrite (Mult_P3 n m (n⁻) HnR Hm HninvR). reflexivity. }
    transitivity (t · ((m · n) · (n⁻))).
    { rewrite (Mult_P4 n m HnR Hm). reflexivity. }
    transitivity (t · (m · (n · (n⁻)))).
    { rewrite <- (Mult_P3 m n (n⁻) Hm HnR HninvR). reflexivity. }
    transitivity (t · (m · 1)).
    { rewrite (Mult_inv2 n Hn). reflexivity. }
    transitivity (t · m).
    { rewrite (Mult_P1 m Hm). reflexivity. }
    rewrite (Mult_P4 t m HtR Hm). reflexivity. }
  assert (Hst2 : (m · t) · (k · (t⁻)) = m · k).
  { transitivity (((m · t) · k) · (t⁻)).
    { apply (Mult_P3 (m · t) k (t⁻) HmtR Hk HtinvR). }
    transitivity ((m · (t · k)) · (t⁻)).
    { rewrite <- (Mult_P3 m t k Hm HtR Hk). reflexivity. }
    transitivity ((m · (k · t)) · (t⁻)).
    { rewrite (Mult_P4 t k HtR Hk). reflexivity. }
    transitivity (((m · k) · t) · (t⁻)).
    { rewrite (Mult_P3 m k t Hm Hk HtR). reflexivity. }
    transitivity ((m · k) · (t · (t⁻))).
    { symmetry. apply (Mult_P3 (m · k) t (t⁻) HmkR HtR HtinvR). }
    transitivity ((m · k) · 1).
    { rewrite (Mult_inv2 t Ht). reflexivity. }
    rewrite (Mult_P1 (m · k) HmkR). reflexivity. }
  assert (Hkey : (n · t) · ((m · (n⁻)) · (k · (t⁻))) = m · k).
  { transitivity (((n · t) · (m · (n⁻))) · (k · (t⁻))).
    { apply (Mult_P3 (n · t) (m · (n⁻)) (k · (t⁻)) HntR HmnR HktR). }
    rewrite Hst1. rewrite Hst2. reflexivity. }
  change ((m · (n⁻)) · (k · (t⁻)) = (m · k) · ((n · t)⁻)).
  apply (Mult_Co3 (n · t) ((m · (n⁻)) · (k · (t⁻))) (m · k) HntR0 HlhsR HmkR Hkey).
Qed.

Proposition Rat_P1a : ∀ x y, x ∈ Q -> y ∈ Q -> (x + y) ∈ Q.
Proof.
  intros x y Hx Hy.
  assert (Z0_to_R0 : ∀ n, n ∈ (Z ~ [0]) -> n ∈ (R ~ [0])).
  { intros n Hn. unfold Setminus in Hn. apply AxiomII in Hn as [En [HnZ Hnnot]].
    unfold Setminus. apply AxiomII; split.
    - exact En.
    - split; [apply Z_Subset_R; exact HnZ | exact Hnnot]. }
  assert (Z0_Z : ∀ n, n ∈ (Z ~ [0]) -> n ∈ Z).
  { intros n Hn. unfold Setminus in Hn. apply AxiomII in Hn as [_ [HnZ _]]. exact HnZ. }
  assert (R0_mul : ∀ a b, a ∈ (R ~ [0]) -> b ∈ (R ~ [0]) -> (a · b) ∈ (R ~ [0])).
  { intros a b Ha Hb.
    unfold Setminus in Ha. apply AxiomII in Ha as [Ea [HaR Hanot]]. apply AxiomII in Hanot as [_ Hanot'].
    unfold Setminus in Hb. apply AxiomII in Hb as [Eb [HbR Hbnot]]. apply AxiomII in Hbnot as [_ Hbnot'].
    assert (H0 : 0 ∈ R) by (apply zero_in_R).
    assert (E0 : Ensemble 0) by (exists R; exact H0).
    assert (HabR : (a · b) ∈ R) by (apply (Mult_close a b HaR HbR)).
    assert (Habne : a · b ≠ 0).
    { intro Heq. destruct (PlusMult_Co2 a b HaR HbR Heq) as [Ha0 | Hb0].
      - exact (Hanot' (proj2 (MKT41 0 E0 a) Ha0)).
      - exact (Hbnot' (proj2 (MKT41 0 E0 b) Hb0)). }
    assert (Habnot : (a · b) ∉ [0]) by (intro Habs; exact (Habne (proj1 (MKT41 0 E0 (a · b)) Habs))).
    unfold Setminus. apply AxiomII; split.
    - exists R; exact HabR.
    - split; [exact HabR | apply AxiomII; split; [exists R; exact HabR | exact Habnot]]. }
  assert (add_frac : ∀ a b c, a ∈ R -> b ∈ R -> c ∈ (R ~ [0]) -> a / c + b / c = (a + b) / c).
  { intros a b c Ha Hb Hc.
    assert (HcinvR : (c⁻) ∈ R).
    { pose proof (Mult_inv1 c Hc) as H. unfold Setminus in H. apply AxiomII in H as [_ [HcinvR _]]. exact HcinvR. }
    change (a · (c⁻) + b · (c⁻) = (a + b) · (c⁻)).
    symmetry. apply (Mult_P5 a b (c⁻) Ha Hb HcinvR). }
  apply AxiomII in Hx as [Ex [m1 [n1 [Hm1 [Hn1 Hxeq]]]]].
  apply AxiomII in Hy as [Ey [m2 [n2 [Hm2 [Hn2 Hyeq]]]]].
  rewrite Hxeq, Hyeq.
  assert (Hm1R : m1 ∈ R) by (apply Z_Subset_R; exact Hm1).
  assert (Hm2R : m2 ∈ R) by (apply Z_Subset_R; exact Hm2).
  assert (Hn1Z : n1 ∈ Z) by (apply Z0_Z; exact Hn1).
  assert (Hn2Z : n2 ∈ Z) by (apply Z0_Z; exact Hn2).
  assert (Hn1R0 : n1 ∈ (R ~ [0])) by (apply Z0_to_R0; exact Hn1).
  assert (Hn2R0 : n2 ∈ (R ~ [0])) by (apply Z0_to_R0; exact Hn2).
  assert (Hn1R : n1 ∈ R) by (apply Z_Subset_R; exact Hn1Z).
  assert (Hn2R : n2 ∈ R) by (apply Z_Subset_R; exact Hn2Z).
  assert (Hn1invR : (n1⁻) ∈ R).
  { pose proof (Mult_inv1 n1 Hn1R0) as H. unfold Setminus in H. apply AxiomII in H as [_ [Hn1invR _]]. exact Hn1invR. }
  assert (Hn2invR : (n2⁻) ∈ R).
  { pose proof (Mult_inv1 n2 Hn2R0) as H. unfold Setminus in H. apply AxiomII in H as [_ [Hn2invR _]]. exact Hn2invR. }
  assert (Hmn1R : (m1 / n1) ∈ R) by (apply (Mult_close m1 (n1⁻) Hm1R Hn1invR)).
  assert (Hmn2R : (m2 / n2) ∈ R) by (apply (Mult_close m2 (n2⁻) Hm2R Hn2invR)).
  assert (Hm1n2Z : (m1 · n2) ∈ Z) by (apply (Int_P1b m1 n2 Hm1 Hn2Z)).
  assert (Hm2n1Z : (m2 · n1) ∈ Z) by (apply (Int_P1b m2 n1 Hm2 Hn1Z)).
  assert (HnumZ : (m1 · n2 + m2 · n1) ∈ Z) by (apply (Int_P1a (m1 · n2) (m2 · n1) Hm1n2Z Hm2n1Z)).
  assert (Hm1n2R : (m1 · n2) ∈ R) by (apply Z_Subset_R; exact Hm1n2Z).
  assert (Hm2n1R : (m2 · n1) ∈ R) by (apply Z_Subset_R; exact Hm2n1Z).
  assert (Hn1n2R0 : (n1 · n2) ∈ (R ~ [0])) by (apply (R0_mul n1 n2 Hn1R0 Hn2R0)).
  assert (Hn1n2Z : (n1 · n2) ∈ Z) by (apply (Int_P1b n1 n2 Hn1Z Hn2Z)).
  assert (Hn1n2Z0 : (n1 · n2) ∈ (Z ~ [0])).
  { pose proof Hn1n2R0 as H. unfold Setminus in H. apply AxiomII in H as [E [_ Hnnot]].
    unfold Setminus. apply AxiomII; split. - exact E. - split; [exact Hn1n2Z | exact Hnnot]. }
  assert (Heq : m1 / n1 + m2 / n2 = (m1 · n2 + m2 · n1) / (n1 · n2)).
  { assert (He1 : m1 / n1 = (m1 · n2) / (n1 · n2)) by (apply (Frac_P1 m1 n1 n2 Hm1R Hn1R0 Hn2R0)).
    assert (He2 : m2 / n2 = (m2 · n1) / (n1 · n2)).
    { transitivity ((m2 · n1) / (n2 · n1)).
      - apply (Frac_P1 m2 n2 n1 Hm2R Hn2R0 Hn1R0).
      - rewrite (Mult_P4 n2 n1 Hn2R Hn1R). reflexivity. }
    rewrite He1. rewrite He2.
    apply (add_frac (m1 · n2) (m2 · n1) (n1 · n2) Hm1n2R Hm2n1R Hn1n2R0). }
  apply AxiomII; split.
  - exists R; apply (Plus_close (m1 / n1) (m2 / n2) Hmn1R Hmn2R).
  - exists (m1 · n2 + m2 · n1), (n1 · n2). split; [exact HnumZ | split; [exact Hn1n2Z0 | exact Heq]].
Qed.

Proposition Rat_P1b : ∀ x y, x ∈ Q -> y ∈ Q -> (x · y) ∈ Q.
Proof.
  intros x y Hx Hy.
  assert (Z0_to_R0 : ∀ n, n ∈ (Z ~ [0]) -> n ∈ (R ~ [0])).
  { intros n Hn. unfold Setminus in Hn. apply AxiomII in Hn as [En [HnZ Hnnot]].
    unfold Setminus. apply AxiomII; split.
    - exact En.
    - split; [apply Z_Subset_R; exact HnZ | exact Hnnot]. }
  assert (Z0_Z : ∀ n, n ∈ (Z ~ [0]) -> n ∈ Z).
  { intros n Hn. unfold Setminus in Hn. apply AxiomII in Hn as [_ [HnZ _]]. exact HnZ. }
  assert (R0_mul : ∀ a b, a ∈ (R ~ [0]) -> b ∈ (R ~ [0]) -> (a · b) ∈ (R ~ [0])).
  { intros a b Ha Hb.
    unfold Setminus in Ha. apply AxiomII in Ha as [Ea [HaR Hanot]]. apply AxiomII in Hanot as [_ Hanot'].
    unfold Setminus in Hb. apply AxiomII in Hb as [Eb [HbR Hbnot]]. apply AxiomII in Hbnot as [_ Hbnot'].
    assert (H0 : 0 ∈ R) by (apply zero_in_R).
    assert (E0 : Ensemble 0) by (exists R; exact H0).
    assert (HabR : (a · b) ∈ R) by (apply (Mult_close a b HaR HbR)).
    assert (Habne : a · b ≠ 0).
    { intro Heq. destruct (PlusMult_Co2 a b HaR HbR Heq) as [Ha0 | Hb0].
      - exact (Hanot' (proj2 (MKT41 0 E0 a) Ha0)).
      - exact (Hbnot' (proj2 (MKT41 0 E0 b) Hb0)). }
    assert (Habnot : (a · b) ∉ [0]) by (intro Habs; exact (Habne (proj1 (MKT41 0 E0 (a · b)) Habs))).
    unfold Setminus. apply AxiomII; split.
    - exists R; exact HabR.
    - split; [exact HabR | apply AxiomII; split; [exists R; exact HabR | exact Habnot]]. }
  apply AxiomII in Hx as [Ex [m1 [n1 [Hm1 [Hn1 Hxeq]]]]].
  apply AxiomII in Hy as [Ey [m2 [n2 [Hm2 [Hn2 Hyeq]]]]].
  rewrite Hxeq, Hyeq.
  assert (Hm1R : m1 ∈ R) by (apply Z_Subset_R; exact Hm1).
  assert (Hm2R : m2 ∈ R) by (apply Z_Subset_R; exact Hm2).
  assert (Hn1Z : n1 ∈ Z) by (apply Z0_Z; exact Hn1).
  assert (Hn2Z : n2 ∈ Z) by (apply Z0_Z; exact Hn2).
  assert (Hn1R0 : n1 ∈ (R ~ [0])) by (apply Z0_to_R0; exact Hn1).
  assert (Hn2R0 : n2 ∈ (R ~ [0])) by (apply Z0_to_R0; exact Hn2).
  assert (Hn1invR : (n1⁻) ∈ R).
  { pose proof (Mult_inv1 n1 Hn1R0) as H. unfold Setminus in H. apply AxiomII in H as [_ [Hn1invR _]]. exact Hn1invR. }
  assert (Hn2invR : (n2⁻) ∈ R).
  { pose proof (Mult_inv1 n2 Hn2R0) as H. unfold Setminus in H. apply AxiomII in H as [_ [Hn2invR _]]. exact Hn2invR. }
  assert (Hmn1R : (m1 / n1) ∈ R) by (apply (Mult_close m1 (n1⁻) Hm1R Hn1invR)).
  assert (Hmn2R : (m2 / n2) ∈ R) by (apply (Mult_close m2 (n2⁻) Hm2R Hn2invR)).
  assert (Hm1m2Z : (m1 · m2) ∈ Z) by (apply (Int_P1b m1 m2 Hm1 Hm2)).
  assert (Hn1n2Z : (n1 · n2) ∈ Z) by (apply (Int_P1b n1 n2 Hn1Z Hn2Z)).
  assert (Hn1n2R0 : (n1 · n2) ∈ (R ~ [0])) by (apply (R0_mul n1 n2 Hn1R0 Hn2R0)).
  assert (Hn1n2Z0 : (n1 · n2) ∈ (Z ~ [0])).
  { pose proof Hn1n2R0 as H. unfold Setminus in H. apply AxiomII in H as [E [_ Hnnot]].
    unfold Setminus. apply AxiomII; split. - exact E. - split; [exact Hn1n2Z | exact Hnnot]. }
  assert (Heq : (m1 / n1) · (m2 / n2) = (m1 · m2) / (n1 · n2))
    by (apply (Frac_P2 m1 n1 m2 n2 Hm1R Hn1R0 Hm2R Hn2R0)).
  apply AxiomII; split.
  - exists R; apply (Mult_close (m1 / n1) (m2 / n2) Hmn1R Hmn2R).
  - exists (m1 · m2), (n1 · n2). split; [exact Hm1m2Z | split; [exact Hn1n2Z0 | exact Heq]].
Qed.

Proposition Rat_P2 : ∀ x, x ∈ Q -> x + 0 = x /\ 0 + x = x.
Proof.
  intros x Hx.
  assert (HxR : x ∈ R) by (apply Q_Subset_R; exact Hx).
  assert (H0 : 0 ∈ R) by (apply zero_in_R).
  split.
  - apply (Plus_P1 x HxR).
  - exact (eq_trans (Plus_P4 0 x H0 HxR) (Plus_P1 x HxR)).
Qed.

Proposition Rat_P3 : ∀ n, n ∈ Q -> (-n) ∈ Q /\ n + (-n) = 0 /\ (-n) + n = 0.
Proof.
  intros n Hn.
  assert (Z0_to_R0 : ∀ k, k ∈ (Z ~ [0]) -> k ∈ (R ~ [0])).
  { intros k Hk. unfold Setminus in Hk. apply AxiomII in Hk as [Ek [HkZ Hknot]].
    unfold Setminus. apply AxiomII; split.
    - exact Ek.
    - split; [apply Z_Subset_R; exact HkZ | exact Hknot]. }
  assert (Z0_Z : ∀ k, k ∈ (Z ~ [0]) -> k ∈ Z).
  { intros k Hk. unfold Setminus in Hk. apply AxiomII in Hk as [_ [HkZ _]]. exact HkZ. }
  apply AxiomII in Hn as [En [m [k [Hm [Hk Hneq]]]]].
  rewrite Hneq.
  assert (HmR : m ∈ R) by (apply Z_Subset_R; exact Hm).
  assert (HkZ : k ∈ Z) by (apply Z0_Z; exact Hk).
  assert (HkR : k ∈ R) by (apply Z_Subset_R; exact HkZ).
  assert (HkR0 : k ∈ (R ~ [0])) by (apply Z0_to_R0; exact Hk).
  assert (HkinvR : (k⁻) ∈ R).
  { pose proof (Mult_inv1 k HkR0) as H. unfold Setminus in H. apply AxiomII in H as [_ [HkinvR _]]. exact HkinvR. }
  assert (HmkR : (m · (k⁻)) ∈ R) by (apply (Mult_close m (k⁻) HmR HkinvR)).
  assert (Hnegs : (-(m · (k⁻))) ∈ Q).
  { apply AxiomII; split.
    - exists R; apply (Plus_neg1a (m · (k⁻)) HmkR).
    - exists (-m), k. split.
      + apply (proj1 (Int_P3 m Hm)).
      + split; [exact Hk |].
        assert (Hm1R : (-(1)) ∈ R) by (apply (Plus_neg1a 1 one_in_R_Co)).
        assert (H1 : -m = (-(1)) · m) by (apply (PlusMult_Co3 m HmR)).
        assert (H2 : -(m · (k⁻)) = (-(1)) · (m · (k⁻))) by (apply (PlusMult_Co3 (m · (k⁻)) HmkR)).
        transitivity ((-(1)) · (m · (k⁻))).
        { exact H2. }
        transitivity (((-(1)) · m) · (k⁻)).
        { apply (Mult_P3 (-(1)) m (k⁻) Hm1R HmR HkinvR). }
        rewrite <- H1. reflexivity. }
  split.
  - exact Hnegs.
  - split.
    + apply (Plus_neg2 (m · (k⁻)) HmkR).
    + rewrite (Plus_P4 (-(m · (k⁻))) (m · (k⁻)) (Plus_neg1a (m · (k⁻)) HmkR) HmkR).
      apply (Plus_neg2 (m · (k⁻)) HmkR).
Qed.

Proposition Rat_P4 : ∀ x y z, x ∈ Q -> y ∈ Q -> z ∈ Q
  -> x + (y + z) = (x + y) + z.
Proof.
  intros x y z Hx Hy Hz.
  apply (Plus_P3 x y z (Q_Subset_R x Hx) (Q_Subset_R y Hy) (Q_Subset_R z Hz)).
Qed.

Proposition Rat_P5 : ∀ x y, x ∈ Q -> y ∈ Q -> x + y = y + x.
Proof.
  intros x y Hx Hy.
  apply (Plus_P4 x y (Q_Subset_R x Hx) (Q_Subset_R y Hy)).
Qed.

Proposition Rat_P6 : ∀ x, x ∈ Q -> x · 1 = x /\ 1 · x = x.
Proof.
  intros x Hx.
  assert (HxR : x ∈ R) by (apply Q_Subset_R; exact Hx).
  split.
  - apply (Mult_P1 x HxR).
  - exact (eq_trans (Mult_P4 1 x one_in_R_Co HxR) (Mult_P1 x HxR)).
Qed.

Proposition Rat_P7 : ∀ x, x ∈ (Q ~ [0]) -> (x⁻) ∈ Q /\ x · (x⁻) = 1.
Proof.
  intros x Hx.
  assert (Z0_to_R0 : ∀ n, n ∈ (Z ~ [0]) -> n ∈ (R ~ [0])).
  { intros n Hn. unfold Setminus in Hn. apply AxiomII in Hn as [En [HnZ Hnnot]].
    unfold Setminus. apply AxiomII; split.
    - exact En.
    - split; [apply Z_Subset_R; exact HnZ | exact Hnnot]. }
  assert (Z0_Z : ∀ n, n ∈ (Z ~ [0]) -> n ∈ Z).
  { intros n Hn. unfold Setminus in Hn. apply AxiomII in Hn as [_ [HnZ _]]. exact HnZ. }
  assert (R0_mul : ∀ a b, a ∈ (R ~ [0]) -> b ∈ (R ~ [0]) -> (a · b) ∈ (R ~ [0])).
  { intros a b Ha Hb.
    unfold Setminus in Ha. apply AxiomII in Ha as [Ea [HaR Hanot]]. apply AxiomII in Hanot as [_ Hanot'].
    unfold Setminus in Hb. apply AxiomII in Hb as [Eb [HbR Hbnot]]. apply AxiomII in Hbnot as [_ Hbnot'].
    assert (H0 : 0 ∈ R) by (apply zero_in_R).
    assert (E0 : Ensemble 0) by (exists R; exact H0).
    assert (HabR : (a · b) ∈ R) by (apply (Mult_close a b HaR HbR)).
    assert (Habne : a · b ≠ 0).
    { intro Heq. destruct (PlusMult_Co2 a b HaR HbR Heq) as [Ha0 | Hb0].
      - exact (Hanot' (proj2 (MKT41 0 E0 a) Ha0)).
      - exact (Hbnot' (proj2 (MKT41 0 E0 b) Hb0)). }
    assert (Habnot : (a · b) ∉ [0]) by (intro Habs; exact (Habne (proj1 (MKT41 0 E0 (a · b)) Habs))).
    unfold Setminus. apply AxiomII; split.
    - exists R; exact HabR.
    - split; [exact HabR | apply AxiomII; split; [exists R; exact HabR | exact Habnot]]. }
  assert (H0 : 0 ∈ R) by (apply zero_in_R).
  assert (E0 : Ensemble 0) by (exists R; exact H0).
  unfold Setminus in Hx. apply AxiomII in Hx as [Ex [HxQ Hxnot]]. apply AxiomII in Hxnot as [_ Hxnot'].
  assert (HxR : x ∈ R) by (apply Q_Subset_R; exact HxQ).
  assert (HxR0 : x ∈ (R ~ [0])).
  { unfold Setminus. apply AxiomII; split.
    - exact Ex.
    - split; [exact HxR | apply AxiomII; split; [exact Ex | exact Hxnot']]. }
  apply AxiomII in HxQ as [Ex2 [m [n [Hm [Hn Hxeq]]]]].
  assert (HnZ : n ∈ Z) by (apply Z0_Z; exact Hn).
  assert (HmR : m ∈ R) by (apply Z_Subset_R; exact Hm).
  assert (HnR : n ∈ R) by (apply Z_Subset_R; exact HnZ).
  assert (HnR0 : n ∈ (R ~ [0])) by (apply Z0_to_R0; exact Hn).
  assert (HninvR : (n⁻) ∈ R).
  { pose proof (Mult_inv1 n HnR0) as H. unfold Setminus in H. apply AxiomII in H as [_ [HninvR _]]. exact HninvR. }
  assert (HmnR : (m · (n⁻)) ∈ R) by (apply (Mult_close m (n⁻) HmR HninvR)).
  assert (Hmne : m ≠ 0).
  { intro Hm0.
    assert (Hxz : x = 0) by (rewrite Hxeq; rewrite Hm0; rewrite (Mult_P4 0 (n⁻) H0 HninvR); apply (PlusMult_Co1 (n⁻) HninvR)).
    exact (Hxnot' (proj2 (MKT41 0 E0 x) Hxz)). }
  assert (HmZ0 : m ∈ (Z ~ [0])).
  { unfold Setminus. apply AxiomII; split.
    - exists R; exact HmR.
    - split; [exact Hm | apply AxiomII; split; [exists R; exact HmR | intro Hmz; exact (Hmne (proj1 (MKT41 0 E0 m) Hmz))]]. }
  assert (HmR0 : m ∈ (R ~ [0])) by (apply Z0_to_R0; exact HmZ0).
  assert (HminvR0 : (m⁻) ∈ (R ~ [0])) by (apply (Mult_inv1 m HmR0)).
  assert (HminvR : (m⁻) ∈ R).
  { pose proof HminvR0 as H. unfold Setminus in H. apply AxiomII in H as [_ [HminvR _]]. exact HminvR. }
  assert (HnmR : (n · (m⁻)) ∈ R) by (apply (Mult_close n (m⁻) HnR HminvR)).
  assert (HnmR0 : (n · (m⁻)) ∈ (R ~ [0])) by (apply (R0_mul n (m⁻) HnR0 HminvR0)).
  assert (Hxy1 : x · (n · (m⁻)) = 1).
  { rewrite Hxeq.
    transitivity (((m · (n⁻)) · n) · (m⁻)).
    { apply (Mult_P3 (m · (n⁻)) n (m⁻) HmnR HnR HminvR). }
    transitivity ((m · ((n⁻) · n)) · (m⁻)).
    { rewrite <- (Mult_P3 m (n⁻) n HmR HninvR HnR). reflexivity. }
    transitivity ((m · (n · (n⁻))) · (m⁻)).
    { rewrite (Mult_P4 (n⁻) n HninvR HnR). reflexivity. }
    transitivity ((m · 1) · (m⁻)).
    { rewrite (Mult_inv2 n HnR0). reflexivity. }
    rewrite (Mult_P1 m HmR). apply (Mult_inv2 m HmR0). }
  destruct (Mult_Co2 x HxR0) as [x0 [[Hx0R0 Hx0inv] Huniq]].
  assert (Hxinv_eq : (x⁻) = x0) by (symmetry; apply Huniq; split; [apply (Mult_inv1 x HxR0) | apply (Mult_inv2 x HxR0)]).
  assert (Hy_eq : (n · (m⁻)) = x0) by (symmetry; apply Huniq; split; [exact HnmR0 | exact Hxy1]).
  assert (Hres : (x⁻) = n · (m⁻)) by (rewrite Hxinv_eq, Hy_eq; reflexivity).
  split.
  - rewrite Hres. apply AxiomII; split.
    + exists R; exact HnmR.
    + exists n, m. split; [exact HnZ | split; [exact HmZ0 | reflexivity]].
  - apply (Mult_inv2 x HxR0).
Qed.

Proposition Rat_P8 : ∀ x y z, x ∈ Q -> y ∈ Q -> z ∈ Q
  -> x · (y · z) = (x · y) · z.
Proof.
  intros x y z Hx Hy Hz.
  apply (Mult_P3 x y z (Q_Subset_R x Hx) (Q_Subset_R y Hy) (Q_Subset_R z Hz)).
Qed.

Proposition Rat_P9 : ∀ x y, x ∈ Q -> y ∈ Q -> x · y = y · x.
Proof.
  intros x y Hx Hy.
  apply (Mult_P4 x y (Q_Subset_R x Hx) (Q_Subset_R y Hy)).
Qed.

Proposition Rat_P10 : ∀ x y z, x ∈ Q -> y ∈ Q -> z ∈ Q
  -> (x + y) · z = (x · z) + (y · z).
Proof.
  intros x y z Hx Hy Hz.
  apply (Mult_P5 x y z (Q_Subset_R x Hx) (Q_Subset_R y Hy) (Q_Subset_R z Hz)).
Qed.

Definition Even n := ∃ k, k ∈ Z /\ n = (1 + 1) · k.

Definition Odd n := ∃ k, k ∈ Z /\ n = (1 + 1) · k + 1.

Proposition Even_and_Odd_P1 : ∀ n, n ∈ N -> Even n \/ Odd n.
Proof.
  intros n Hn.
  assert (distr : ∀ a b c, a ∈ R -> b ∈ R -> c ∈ R -> a · (b + c) = a · b + a · c).
  { intros a b c Ha Hb Hc.
    transitivity ((b + c) · a).
    - apply (Mult_P4 a (b + c) Ha (Plus_close b c Hb Hc)).
    - transitivity (b · a + c · a).
      + apply (Mult_P5 b c a Hb Hc Ha).
      + rewrite (Mult_P4 b a Hb Ha). rewrite (Mult_P4 c a Hc Ha). reflexivity. }
  assert (H1R : 1 ∈ R) by (apply one_in_R_Co).
  assert (H0R : 0 ∈ R) by (apply zero_in_R).
  assert (H2R : (1 + 1) ∈ R) by (apply (Plus_close 1 1 H1R H1R)).
  assert (H1Z : 1 ∈ Z) by (apply N_Subset_Z; apply one_in_N).
  assert (H0Z : 0 ∈ Z).
  { unfold Z. apply MKT4. right. apply MKT4. right.
    assert (E0 : Ensemble 0) by (exists R; exact H0R).
    apply (proj2 (MKT41 0 E0 0)). reflexivity. }
  set (E := \{ λ u, u ∈ N /\ (Even u \/ Odd u) \}).
  assert (HEsub : E ⊂ N).
  { intros z Hz. apply AxiomII in Hz as [_ [HzN _]]. exact HzN. }
  assert (H1E : 1 ∈ E).
  { apply AxiomII; split.
    - exists R; exact H1R.
    - split; [exact one_in_N | right].
      exists 0. split; [exact H0Z |].
      rewrite (PlusMult_Co1 (1 + 1) H2R).
      symmetry. exact (eq_trans (Plus_P4 0 1 H0R H1R) (Plus_P1 1 H1R)). }
  assert (HEcl : ∀ x, x ∈ E -> (x + 1) ∈ E).
  { intros x Hx.
    apply AxiomII in Hx as [_ [HxN Hpar]].
    assert (HxR : x ∈ R) by (apply N_Subset_R; exact HxN).
    assert (Hx1N : (x + 1) ∈ N).
    { pose proof IndSet_N as HIN. unfold IndSet in HIN. exact (proj2 HIN x HxN). }
    apply AxiomII; split.
    - exists R; exact (N_Subset_R (x + 1) Hx1N).
    - split; [exact Hx1N |].
      destruct Hpar as [Hev | Hod].
      + right. destruct Hev as [k [HkZ Hxeq]].
        exists k. split; [exact HkZ | rewrite Hxeq; reflexivity].
      + left. destruct Hod as [k [HkZ Hxeq]].
        exists (k + 1). split.
        * apply (Int_P1a k 1 HkZ H1Z).
        * rewrite Hxeq. symmetry.
          transitivity ((1 + 1) · k + (1 + 1) · 1).
          -- apply (distr (1 + 1) k 1 H2R (Z_Subset_R k HkZ) H1R).
          -- rewrite (Mult_P1 (1 + 1) H2R).
             apply (Plus_P3 ((1 + 1) · k) 1 1 (Mult_close (1 + 1) k H2R (Z_Subset_R k HkZ)) H1R H1R). }
  assert (HE : E = N) by (apply (MathInd E HEsub H1E HEcl)).
  assert (HnE : n ∈ E) by (rewrite HE; exact Hn).
  apply AxiomII in HnE as [_ [_ Hpar]].
  exact Hpar.
Qed.

Lemma Even_and_Odd_P2_Lemma : ∀ m n, m ∈ Z -> n ∈ Z -> n < m -> (n + 1) ≤ m.
Proof.
  assert (HminN : ∀ u, u ∈ N -> 1 ≤ u).
  { pose proof one_is_min_in_N as H. unfold Min in H. exact (proj2 (proj2 H)). }
  assert (posZ_in_N : ∀ d, d ∈ Z -> 0 < d -> d ∈ N).
  { intros d HdZ H0d.
    assert (H0R : 0 ∈ R) by (apply zero_in_R).
    assert (H1R : 1 ∈ R) by (apply one_in_R_Co).
    assert (E0 : Ensemble 0) by (exists R; exact H0R).
    assert (HdR : d ∈ R) by (apply Z_Subset_R; exact HdZ).
    unfold Z in HdZ. apply MKT4 in HdZ as [HdN | HdRest].
    - exact HdN.
    - apply MKT4 in HdRest as [HdNegN | Hd0].
      + exfalso.
        apply AxiomII in HdNegN as [Ed Hneg].
        assert (HnegR : (-d) ∈ R) by (apply (Plus_neg1a d HdR)).
        assert (H1d : 1 ≤ (-d)) by (apply HminN; exact Hneg).
        assert (H0dle : 0 ≤ d) by (exact (proj1 H0d)).
        assert (Hle : 1 + 0 ≤ (-d) + d) by (apply (OrderPM_Co3 1 (-d) 0 d H1R HnegR H0R HdR H1d H0dle)).
        assert (Hle' : 1 ≤ 0).
        { rewrite (Plus_P1 1 H1R) in Hle.
          rewrite (eq_trans (Plus_P4 (-d) d HnegR HdR) (Plus_neg2 d HdR)) in Hle.
          exact Hle. }
        assert (H01 : 0 ≤ 1) by (exact (proj1 OrderPM_Co9)).
        assert (H10eq : 1 = 0) by (apply (Leq_P2 1 0 H1R H0R Hle' H01)).
        exact (proj2 OrderPM_Co9 (eq_sym H10eq)).
      + exfalso.
        assert (Hd0eq : d = 0) by (exact (proj1 (MKT41 0 E0 d) Hd0)).
        exact (proj2 H0d (eq_sym Hd0eq)). }
  intros m n HmZ HnZ Hlt.
  assert (HnR : n ∈ R) by (apply Z_Subset_R; exact HnZ).
  assert (HmR : m ∈ R) by (apply Z_Subset_R; exact HmZ).
  assert (H0R : 0 ∈ R) by (apply zero_in_R).
  assert (H1R : 1 ∈ R) by (apply one_in_R_Co).
  assert (HnegN : (-n) ∈ Z) by (apply (proj1 (Int_P3 n HnZ))).
  assert (HnegR : (-n) ∈ R) by (apply Z_Subset_R; exact HnegN).
  assert (HdZ : (m + (-n)) ∈ Z) by (apply (Int_P1a m (-n) HmZ HnegN)).
  assert (H0d : 0 < (m + (-n))).
  { assert (Ht : n + (-n) < m + (-n)) by (apply (OrderPM_Co1 n m (-n) HnR HmR HnegR Hlt)).
    rewrite (Plus_neg2 n HnR) in Ht. exact Ht. }
  assert (HdN : (m + (-n)) ∈ N) by (apply posZ_in_N; assumption).
  assert (H1d : 1 ≤ m + (-n)) by (apply HminN; exact HdN).
  assert (Hnd : n + (m + (-n)) = m).
  { transitivity ((n + m) + (-n)).
    - apply (Plus_P3 n m (-n) HnR HmR HnegR).
    - transitivity ((m + n) + (-n)).
      + rewrite (Plus_P4 n m HnR HmR). reflexivity.
      + transitivity (m + (n + (-n))).
        * symmetry. apply (Plus_P3 m n (-n) HmR HnR HnegR).
        * rewrite (Plus_neg2 n HnR). apply (Plus_P1 m HmR). }
  assert (Hle0 : 1 + n ≤ (m + (-n)) + n)
    by (apply (Plus_Leq 1 (m + (-n)) n H1R (Plus_close m (-n) HmR HnegR) HnR H1d)).
  rewrite (Plus_P4 1 n H1R HnR) in Hle0.
  rewrite (Plus_P4 (m + (-n)) n (Plus_close m (-n) HmR HnegR) HnR) in Hle0.
  rewrite Hnd in Hle0. exact Hle0.
Qed.

Proposition Even_and_Odd_P2 : ∀ n, n ∈ Z -> ~ (Even n /\ Odd n).
Proof.
  intros n HnZ [Hev Hod].
  assert (distr : ∀ a b c, a ∈ R -> b ∈ R -> c ∈ R -> a · (b + c) = a · b + a · c).
  { intros a b c Ha Hb Hc.
    transitivity ((b + c) · a).
    - apply (Mult_P4 a (b + c) Ha (Plus_close b c Hb Hc)).
    - transitivity (b · a + c · a).
      + apply (Mult_P5 b c a Hb Hc Ha).
      + rewrite (Mult_P4 b a Hb Ha). rewrite (Mult_P4 c a Hc Ha). reflexivity. }
  assert (HminN : ∀ u, u ∈ N -> 1 ≤ u).
  { pose proof one_is_min_in_N as H. unfold Min in H. exact (proj2 (proj2 H)). }
  assert (HposZ : ∀ d, d ∈ Z -> 0 < d -> d ∈ N).
  { intros d HdZ H0d.
    assert (H0R : 0 ∈ R) by (apply zero_in_R).
    assert (H1R : 1 ∈ R) by (apply one_in_R_Co).
    assert (E0 : Ensemble 0) by (exists R; exact H0R).
    assert (HdR : d ∈ R) by (apply Z_Subset_R; exact HdZ).
    unfold Z in HdZ. apply MKT4 in HdZ as [HdN | HdRest].
    - exact HdN.
    - apply MKT4 in HdRest as [HdNegN | Hd0].
      + exfalso.
        apply AxiomII in HdNegN as [Ed Hneg].
        assert (HnegR : (-d) ∈ R) by (apply (Plus_neg1a d HdR)).
        assert (H1d : 1 ≤ (-d)) by (apply HminN; exact Hneg).
        assert (H0dle : 0 ≤ d) by (exact (proj1 H0d)).
        assert (Hle : 1 + 0 ≤ (-d) + d) by (apply (OrderPM_Co3 1 (-d) 0 d H1R HnegR H0R HdR H1d H0dle)).
        assert (Hle' : 1 ≤ 0).
        { rewrite (Plus_P1 1 H1R) in Hle.
          rewrite (eq_trans (Plus_P4 (-d) d HnegR HdR) (Plus_neg2 d HdR)) in Hle.
          exact Hle. }
        assert (H01 : 0 ≤ 1) by (exact (proj1 OrderPM_Co9)).
        assert (H10eq : 1 = 0) by (apply (Leq_P2 1 0 H1R H0R Hle' H01)).
        exact (proj2 OrderPM_Co9 (eq_sym H10eq)).
      + exfalso.
        assert (Hd0eq : d = 0) by (exact (proj1 (MKT41 0 E0 d) Hd0)).
        exact (proj2 H0d (eq_sym Hd0eq)). }
  assert (H0R : 0 ∈ R) by (apply zero_in_R).
  assert (H1R : 1 ∈ R) by (apply one_in_R_Co).
  assert (H2R : (1 + 1) ∈ R) by (apply (Plus_close 1 1 H1R H1R)).
  assert (Hlt11 : 1 < 1 + 1).
  { assert (Ht : 0 + 1 < 1 + 1) by (apply (OrderPM_Co1 0 1 1 H0R H1R H1R OrderPM_Co9)).
    rewrite (eq_trans (Plus_P4 0 1 H0R H1R) (Plus_P1 1 H1R)) in Ht. exact Ht. }
  assert (H2pos : 0 < 1 + 1).
  { apply (Order_Co2 0 1 (1 + 1) H0R H1R H2R). left. split; [exact OrderPM_Co9 | exact (proj1 Hlt11)]. }
  destruct Hev as [k [HkZ Hkeq]].
  destruct Hod as [j [HjZ Hjeq]].
  assert (HkR : k ∈ R) by (apply Z_Subset_R; exact HkZ).
  assert (HjR : j ∈ R) by (apply Z_Subset_R; exact HjZ).
  assert (HnegjZ : (-j) ∈ Z) by (apply (proj1 (Int_P3 j HjZ))).
  assert (HnegjR : (-j) ∈ R) by (apply Z_Subset_R; exact HnegjZ).
  assert (HddZ : (k + (-j)) ∈ Z) by (apply (Int_P1a k (-j) HkZ HnegjZ)).
  assert (HdR : (k + (-j)) ∈ R) by (apply Z_Subset_R; exact HddZ).
  assert (Hsum : (1+1)·k = (1+1)·j + 1) by (exact (eq_trans (eq_sym Hkeq) Hjeq)).
  assert (Hk_jd : j + (k + (-j)) = k).
  { transitivity ((j + k) + (-j)).
    - apply (Plus_P3 j k (-j) HjR HkR HnegjR).
    - transitivity ((k + j) + (-j)).
      + rewrite (Plus_P4 j k HjR HkR). reflexivity.
      + transitivity (k + (j + (-j))).
        * symmetry. apply (Plus_P3 k j (-j) HkR HjR HnegjR).
        * rewrite (Plus_neg2 j HjR). apply (Plus_P1 k HkR). }
  assert (Hex : (1+1)·(j + (k + (-j))) = (1+1)·j + (1+1)·(k + (-j)))
    by (apply (distr (1+1) j (k + (-j)) H2R HjR HdR)).
  assert (H2jR : (1+1)·j ∈ R) by (apply (Mult_close (1+1) j H2R HjR)).
  assert (H2dR : (1+1)·(k + (-j)) ∈ R) by (apply (Mult_close (1+1) (k + (-j)) H2R HdR)).
  assert (H2j1R : (1+1)·j + 1 ∈ R) by (apply (Plus_close ((1+1)·j) 1 H2jR H1R)).
  assert (Hkey : (1+1)·(k + (-j)) = 1).
  { assert (Htmp : (1+1)·j + (1+1)·(k + (-j)) = (1+1)·j + 1).
    { rewrite <- Hex. rewrite Hk_jd. exact Hsum. }
    assert (Hres : (1+1)·(k + (-j)) = ((1+1)·j + 1) + (-((1+1)·j)))
      by (apply (Plus_Co3 ((1+1)·j) ((1+1)·(k + (-j))) ((1+1)·j + 1) H2jR H2dR H2j1R Htmp)).
    assert (Hsimp : ((1+1)·j + 1) + (-((1+1)·j)) = 1).
    { transitivity ((1+1)·j + (1 + (-((1+1)·j)))).
      - symmetry. apply (Plus_P3 ((1+1)·j) 1 (-((1+1)·j)) H2jR H1R (Plus_neg1a ((1+1)·j) H2jR)).
      - transitivity ((1+1)·j + ((-((1+1)·j)) + 1)).
        + rewrite (Plus_P4 1 (-((1+1)·j)) H1R (Plus_neg1a ((1+1)·j) H2jR)). reflexivity.
        + transitivity (((1+1)·j + (-((1+1)·j))) + 1).
          * apply (Plus_P3 ((1+1)·j) (-((1+1)·j)) 1 H2jR (Plus_neg1a ((1+1)·j) H2jR) H1R).
          * rewrite (Plus_neg2 ((1+1)·j) H2jR).
            exact (eq_trans (Plus_P4 0 1 H0R H1R) (Plus_P1 1 H1R)). }
    rewrite Hsimp in Hres. exact Hres. }
  assert (Hdne : (k + (-j)) ≠ 0).
  { intro Hd0. rewrite Hd0 in Hkey. rewrite (PlusMult_Co1 (1+1) H2R) in Hkey.
    exact (proj2 OrderPM_Co9 Hkey). }
  assert (Hdpos : 0 < (k + (-j))).
  { destruct (Leq_P4 (k + (-j)) 0 HdR H0R) as [Hle | Hle].
    - exfalso.
      assert (Hle' : (k + (-j))·(1+1) ≤ 0·(1+1))
        by (apply (OrderPM_Co7b (k + (-j)) 0 (1+1) HdR H0R H2R Hle (proj1 H2pos))).
      rewrite (Mult_P4 (k + (-j)) (1+1) HdR H2R) in Hle'.
      rewrite (Mult_P4 0 (1+1) H0R H2R) in Hle'.
      rewrite Hkey in Hle'.
      rewrite (PlusMult_Co1 (1+1) H2R) in Hle'.
      assert (H01 : 0 ≤ 1) by (exact (proj1 OrderPM_Co9)).
      assert (H10eq : 1 = 0) by (apply (Leq_P2 1 0 H1R H0R Hle' H01)).
      exact (proj2 OrderPM_Co9 (eq_sym H10eq)).
    - exact (conj Hle (fun H0 => Hdne (eq_sym H0))). }
  assert (HdN : (k + (-j)) ∈ N) by (apply HposZ; [exact HddZ | exact Hdpos]).
  assert (Hdge1 : 1 ≤ (k + (-j))) by (apply HminN; exact HdN).
  assert (Hdne1 : (k + (-j)) ≠ 1).
  { intro Heq. rewrite Heq in Hkey. rewrite (Mult_P1 (1+1) H2R) in Hkey.
    rewrite Hkey in Hlt11. exact (proj2 Hlt11 eq_refl). }
  assert (Hdgt1 : 1 < (k + (-j))) by (split; [exact Hdge1 | intro H0; exact (Hdne1 (eq_sym H0))]).
  assert (Hlt : 1·(1+1) < (k + (-j))·(1+1))
    by (apply (OrderPM_Co7a 1 (k + (-j)) (1+1) H1R HdR H2R Hdgt1 H2pos)).
  assert (Hlt2 : (1+1) < 1).
  { rewrite (Mult_P4 (k + (-j)) (1+1) HdR H2R) in Hlt.
    rewrite Hkey in Hlt.
    rewrite (Mult_P4 1 (1+1) H1R H2R) in Hlt.
    rewrite (Mult_P1 (1+1) H2R) in Hlt.
    exact Hlt. }
  assert (Heq : 1 = (1+1)) by (apply (Leq_P2 1 (1+1) H1R H2R (proj1 Hlt11) (proj1 Hlt2))).
  exact (proj2 Hlt11 Heq).
Qed.

Proposition Even_and_Odd_P3 : ∀ r, r ∈ N -> Even (r · r) -> Even r.
Proof.
  intros r Hr Hev.
  assert (distr : ∀ a b c, a ∈ R -> b ∈ R -> c ∈ R -> a · (b + c) = a · b + a · c).
  { intros a b c Ha Hb Hc.
    transitivity ((b + c) · a).
    - apply (Mult_P4 a (b + c) Ha (Plus_close b c Hb Hc)).
    - transitivity (b · a + c · a).
      + apply (Mult_P5 b c a Hb Hc Ha).
      + rewrite (Mult_P4 b a Hb Ha). rewrite (Mult_P4 c a Hc Ha). reflexivity. }
  assert (H1R : 1 ∈ R) by (apply one_in_R_Co).
  assert (H2R : (1+1) ∈ R) by (apply (Plus_close 1 1 H1R H1R)).
  assert (HrR : r ∈ R) by (apply N_Subset_R; exact Hr).
  assert (HrZ : r ∈ Z) by (apply N_Subset_Z; exact Hr).
  assert (HrrZ : (r·r) ∈ Z) by (apply (Int_P1b r r HrZ HrZ)).
  destruct (Even_and_Odd_P1 r Hr) as [Hev' | Hod].
  - exact Hev'.
  - exfalso.
    destruct Hod as [k [HkZ Hkeq]].
    assert (HkR : k ∈ R) by (apply Z_Subset_R; exact HkZ).
    assert (HAR : (1+1)·k ∈ R) by (apply (Mult_close (1+1) k H2R HkR)).
    assert (HkrR : k·r ∈ R) by (apply (Mult_close k r HkR HrR)).
    assert (H3 : r·((1+1)·k) = (1+1)·(k·r)).
    { transitivity (((1+1)·k)·r).
      - apply (Mult_P4 r ((1+1)·k) HrR HAR).
      - symmetry. apply (Mult_P3 (1+1) k r H2R HkR HrR). }
    assert (Hrr : r·r = (1+1)·(k·r + k) + 1).
    { transitivity (r·((1+1)·k + 1)).
      { rewrite <- Hkeq. reflexivity. }
      transitivity (r·((1+1)·k) + r·1).
      { apply (distr r ((1+1)·k) 1 HrR HAR H1R). }
      transitivity (r·((1+1)·k) + r).
      { rewrite (Mult_P1 r HrR). reflexivity. }
      transitivity ((1+1)·(k·r) + r).
      { rewrite H3. reflexivity. }
      transitivity ((1+1)·(k·r) + ((1+1)·k + 1)).
      { rewrite Hkeq. reflexivity. }
      transitivity (((1+1)·(k·r) + (1+1)·k) + 1).
      { apply (Plus_P3 ((1+1)·(k·r)) ((1+1)·k) 1 (Mult_close (1+1) (k·r) H2R HkrR) HAR H1R). }
      { rewrite <- (distr (1+1) (k·r) k H2R HkrR HkR). reflexivity. } }
    assert (Hk'Z : (k·r + k) ∈ Z) by (apply (Int_P1a (k·r) k (Int_P1b k r HkZ HrZ) HkZ)).
    assert (Hodd_rr : Odd (r·r)).
    { exists (k·r + k). split; [exact Hk'Z | exact Hrr]. }
    exact (Even_and_Odd_P2 (r·r) HrrZ (conj Hev Hodd_rr)).
Qed.

Theorem Existence_of_irRational_Number : (R ~ Q) <> Φ.
Proof.
  (* ---------- basic real facts ---------- *)
  assert (H1R : 1 ∈ R) by (apply one_in_R_Co).
  assert (H0R : 0 ∈ R) by (apply zero_in_R).
  assert (H2R : (1 + 1) ∈ R) by (apply (Plus_close 1 1 H1R H1R)).
  assert (H4R : ((1+1) + (1+1)) ∈ R) by (apply (Plus_close (1+1) (1+1) H2R H2R)).
  assert (E0 : Ensemble 0) by (exists R; exact H0R).
  assert (Hlt11 : 1 < (1+1)).
  { assert (Ht : 0 + 1 < 1 + 1) by (apply (OrderPM_Co1 0 1 1 H0R H1R H1R OrderPM_Co9)).
    rewrite (eq_trans (Plus_P4 0 1 H0R H1R) (Plus_P1 1 H1R)) in Ht. exact Ht. }
  assert (H2pos : 0 < (1+1)).
  { apply (Order_Co2 0 1 (1+1) H0R H1R H2R). left. split; [exact OrderPM_Co9 | exact (proj1 Hlt11)]. }
  assert (H2ne : (1+1) <> 0) by (intro H; exact (proj2 H2pos (eq_sym H))).
  assert (H2ge0 : 0 ≤ (1+1)) by (exact (proj1 H2pos)).
  (* 0 ≤ s0*s0 helper later; distr *)
  assert (distr : ∀ a b c, a ∈ R -> b ∈ R -> c ∈ R -> a·(b+c) = a·b + a·c).
  { intros a b c Ha Hb Hc.
    transitivity ((b+c)·a).
    - apply (Mult_P4 a (b+c) Ha (Plus_close b c Hb Hc)).
    - transitivity (b·a + c·a).
      + apply (Mult_P5 b c a Hb Hc Ha).
      + rewrite (Mult_P4 b a Hb Ha). rewrite (Mult_P4 c a Hc Ha). reflexivity. }
  (* cancellation of addition on the right, for strict ineq *)
  assert (cancL : ∀ a b c, a ∈ R -> b ∈ R -> c ∈ R -> a + c < b + c -> a < b).
  { intros a b c Ha Hb Hc Hlt. split.
    - destruct (Leq_P4 a b Ha Hb) as [Hab | Hba]; [exact Hab |].
      exfalso.
      assert (Heq : a + c = b + c)
        by (apply (Leq_P2 (a+c) (b+c) (Plus_close a c Ha Hc) (Plus_close b c Hb Hc) (proj1 Hlt)
                          (Plus_Leq b a c Hb Ha Hc Hba))).
      exact ((proj2 Hlt) Heq).
    - intro Hab. apply (proj2 Hlt). rewrite Hab. reflexivity. }
  assert (cancel2 : ∀ x y, x ∈ R -> y ∈ R -> (1+1)·x = (1+1)·y -> x = y).
  { intros x y HxR HyR Hxy.
    assert (H2R0 : (1+1) ∈ (R ~ [0])).
    { unfold Setminus. apply AxiomII; split.
      - exists R; exact H2R.
      - split; [exact H2R | apply AxiomII; split; [exists R; exact H2R | intro H2in; apply H2ne; exact (proj1 (MKT41 0 E0 (1+1)) H2in)]]. }
    assert (H2invR0 : ((1+1)⁻) ∈ (R ~ [0])) by (apply (Mult_inv1 (1+1) H2R0)).
    assert (H2invR : ((1+1)⁻) ∈ R)
      by (pose proof H2invR0 as H; unfold Setminus in H; apply AxiomII in H as [_ [Hr _]]; exact Hr).
    assert (Hres : x = ((1+1)·y) · ((1+1)⁻))
      by (apply (Mult_Co3 (1+1) x ((1+1)·y) H2R0 HxR (Mult_close (1+1) y H2R HyR) Hxy)).
    assert (Hsim : ((1+1)·y) · ((1+1)⁻) = y).
    { transitivity ((1+1) · (y · (1+1)⁻)).
      - symmetry. apply (Mult_P3 (1+1) y (1+1)⁻ H2R HyR H2invR).
      - transitivity ((1+1) · ((1+1)⁻ · y)).
        + rewrite (Mult_P4 y (1+1)⁻ HyR H2invR). reflexivity.
        + transitivity (((1+1)·(1+1)⁻) · y).
          * apply (Mult_P3 (1+1) (1+1)⁻ y H2R H2invR HyR).
          * rewrite (Mult_inv2 (1+1) H2R0). rewrite (eq_trans (Mult_P4 1 y H1R HyR) (Mult_P1 y HyR)). reflexivity. }
    rewrite Hres. exact Hsim. }
  (* neg multiplication lemmas *)
  assert (neg_multR : ∀ a b, a ∈ R -> b ∈ R -> -(a · b) = a · (-b)).
  { intros a b Ha Hb.
    assert (Hnegb : -b ∈ R) by (apply (Plus_neg1a b Hb)).
    assert (Hab : a · b ∈ R) by (apply (Mult_close a b Ha Hb)).
    assert (Hanb : a · (-b) ∈ R) by (apply (Mult_close a (-b) Ha Hnegb)).
    assert (Hsum : a · b + a · (-b) = 0).
    { transitivity (b · a + (-b) · a).
      - rewrite (Mult_P4 a b Ha Hb). rewrite (Mult_P4 a (-b) Ha Hnegb). reflexivity.
      - transitivity ((b + (-b)) · a).
        + symmetry. apply (Mult_P5 b (-b) a Hb Hnegb Ha).
        + transitivity (0 · a).
          * rewrite (Plus_neg2 b Hb). reflexivity.
          * transitivity (a · 0).
            -- apply (Mult_P4 0 a H0R Ha).
            -- apply (PlusMult_Co1 a Ha). }
    assert (Hres : a · (-b) = 0 + (-(a · b)))
      by (apply (Plus_Co3 (a · b) (a · (-b)) 0 Hab Hanb H0R Hsum)).
    assert (Hfull : a · (-b) = -(a · b))
      by (exact (eq_trans Hres (eq_trans (Plus_P4 0 (-(a · b)) H0R (Plus_neg1a (a · b) Hab))
                                          (Plus_P1 (-(a · b)) (Plus_neg1a (a · b) Hab))))).
    symmetry. exact Hfull. }
  assert (neg_multL : ∀ a b, a ∈ R -> b ∈ R -> -(a · b) = (-a) · b).
  { intros a b Ha Hb.
    assert (Hba : a · b = b · a) by (apply (Mult_P4 a b Ha Hb)).
    rewrite Hba. rewrite (neg_multR b a Hb Ha). rewrite (Mult_P4 b (-a) Hb (Plus_neg1a a Ha)). reflexivity. }
  assert (dblneg : ∀ a, a ∈ R -> -(-a) = a).
  { intros a Ha.
    assert (Hnega : -a ∈ R) by (apply (Plus_neg1a a Ha)).
    assert (Hadd : (-a) + a = 0) by (exact (eq_trans (Plus_P4 (-a) a Hnega Ha) (Plus_neg2 a Ha))).
    assert (Hadd2 : (-a) + (-(-a)) = 0) by (apply (Plus_neg2 (-a) Hnega)).
    destruct (Plus_Co2 (-a) Hnega) as [x0 [[_ _] Huniq]].
    assert (He1 : x0 = a) by (exact (Huniq a (conj Ha Hadd))).
    assert (He2 : x0 = -(-a)) by (exact (Huniq (-(-a)) (conj (Plus_neg1a (-a) Hnega) Hadd2))).
    rewrite <- He2. exact He1. }
  assert (neg_add : ∀ a b, a ∈ R -> b ∈ R -> -(a + b) = (-a) + (-b)).
  { intros a b Ha Hb.
    assert (Hnega : -a ∈ R) by (apply (Plus_neg1a a Ha)).
    assert (Hnegb : -b ∈ R) by (apply (Plus_neg1a b Hb)).
    assert (Hab : (a + b) ∈ R) by (apply (Plus_close a b Ha Hb)).
    assert (HsumR : ((-a) + (-b)) ∈ R) by (apply (Plus_close (-a) (-b) Hnega Hnegb)).
    assert (Hzero : (a + b) + ((-a) + (-b)) = 0).
    { transitivity (((a + b) + (-a)) + (-b)).
      - apply (Plus_P3 (a + b) (-a) (-b) Hab Hnega Hnegb).
      - assert (Hmid : (a + b) + (-a) = b).
        { transitivity ((b + a) + (-a)).
          - rewrite (Plus_P4 a b Ha Hb). reflexivity.
          - transitivity (b + (a + (-a))).
            + symmetry. apply (Plus_P3 b a (-a) Hb Ha Hnega).
            + transitivity (b + 0).
              * rewrite (Plus_neg2 a Ha). reflexivity.
              * apply (Plus_P1 b Hb). }
        rewrite Hmid. apply (Plus_neg2 b Hb). }
    assert (Hres : ((-a) + (-b)) = 0 + (-(a + b)))
      by (apply (Plus_Co3 (a + b) ((-a) + (-b)) 0 Hab HsumR H0R Hzero)).
    assert (H0y : 0 + (-(a + b)) = -(a + b))
      by (exact (eq_trans (Plus_P4 0 (-(a + b)) H0R (Plus_neg1a (a + b) Hab))
                          (Plus_P1 (-(a + b)) (Plus_neg1a (a + b) Hab)))).
    rewrite H0y in Hres. symmetry. exact Hres. }
  assert (sq_expand : ∀ a, a ∈ R -> ((1+1)·a)·((1+1)·a) = (1+1)·((1+1)·(a·a))).
  { intros a Ha.
    assert (HaaR : a·a ∈ R) by (apply (Mult_close a a Ha Ha)).
    assert (H2aR : (1+1)·a ∈ R) by (apply (Mult_close (1+1) a H2R Ha)).
    transitivity ((1+1)·(a·((1+1)·a))).
    - symmetry. apply (Mult_P3 (1+1) a ((1+1)·a) H2R Ha H2aR).
    - transitivity ((1+1)·((a·(1+1))·a)).
      + rewrite (Mult_P3 a (1+1) a Ha H2R Ha). reflexivity.
      + transitivity ((1+1)·(((1+1)·a)·a)).
        * rewrite (Mult_P4 a (1+1) Ha H2R). reflexivity.
        * rewrite (Mult_P3 (1+1) a a H2R Ha Ha). reflexivity. }
  assert (sq_sub : ∀ a b, a ∈ R -> b ∈ R
    -> (a + (-b))·(a + (-b)) = (a·a + (-(a·b))) + ((-(a·b)) + b·b)).
  { intros a b Ha Hb.
    assert (Hnegb : -b ∈ R) by (apply (Plus_neg1a b Hb)).
    assert (HabR : a·b ∈ R) by (apply (Mult_close a b Ha Hb)).
    assert (HbbR : b·b ∈ R) by (apply (Mult_close b b Hb Hb)).
    assert (Hab : (a+(-b)) ∈ R) by (apply (Plus_close a (-b) Ha Hnegb)).
    rewrite (distr (a + (-b)) a (-b) Hab Ha Hnegb).
    rewrite (Mult_P4 (a+(-b)) a Hab Ha).
    rewrite (distr a a (-b) Ha Ha Hnegb).
    rewrite (Mult_P4 (a+(-b)) (-b) Hab Hnegb).
    rewrite (distr (-b) a (-b) Hnegb Ha Hnegb).
    rewrite (eq_sym (neg_multR a b Ha Hb)).
    rewrite (eq_sym (neg_multL b a Hb Ha)).
    rewrite (Mult_P4 b a Hb Ha).
    rewrite (PlusMult_Co5 b Hb).
    reflexivity. }
  (* ---------- min of N : leverage one_is_min_in_N ---------- *)
  assert (HminN : ∀ u, u ∈ N -> 1 ≤ u).
  { pose proof one_is_min_in_N as H. unfold Min in H. exact (proj2 (proj2 H)). }
  assert (posZ_in_N : ∀ d, d ∈ Z -> 0 < d -> d ∈ N).
  { intros d HdZ H0d.
    assert (HdR : d ∈ R) by (apply Z_Subset_R; exact HdZ).
    unfold Z in HdZ. apply MKT4 in HdZ as [HdN | HdRest].
    - exact HdN.
    - apply MKT4 in HdRest as [HdNegN | Hd0].
      + exfalso.
        apply AxiomII in HdNegN as [Ed Hneg].
        assert (HnegR : (-d) ∈ R) by (apply (Plus_neg1a d HdR)).
        assert (H1d : 1 ≤ (-d)) by (apply HminN; exact Hneg).
        assert (H0dle : 0 ≤ d) by (exact (proj1 H0d)).
        assert (Hle : 1 + 0 ≤ (-d) + d)
          by (apply (OrderPM_Co3 1 (-d) 0 d H1R HnegR H0R HdR H1d H0dle)).
        assert (Hle' : 1 ≤ 0).
        { rewrite (Plus_P1 1 H1R) in Hle.
          rewrite (eq_trans (Plus_P4 (-d) d HnegR HdR) (Plus_neg2 d HdR)) in Hle.
          exact Hle. }
        assert (H01 : 0 ≤ 1) by (exact (proj1 OrderPM_Co9)).
        assert (H10eq : 1 = 0) by (apply (Leq_P2 1 0 H1R H0R Hle' H01)).
        exact (proj2 OrderPM_Co9 (eq_sym H10eq)).
      + exfalso.
        assert (Hd0eq : d = 0) by (exact (proj1 (MKT41 0 E0 d) Hd0)).
        exact (proj2 H0d (eq_sym Hd0eq)). }
  (* abs value in N for nonzero integers *)
  assert (absN : ∀ z, z ∈ Z -> z <> 0 -> ∃ z', z' ∈ N /\ z'·z' = z·z /\ z' <> 0).
  { intros z HzZ Hzne.
    assert (HzR : z ∈ R) by (apply Z_Subset_R; exact HzZ).
    unfold Z in HzZ. apply MKT4 in HzZ as [HzN | HzRest].
    - exists z. split; [exact HzN | split; [reflexivity | exact Hzne]].
    - apply MKT4 in HzRest as [HzNeg | Hz0].
      + apply AxiomII in HzNeg as [Ez HznegN].
        exists (-z). split.
        * exact HznegN.
        * split.
          -- rewrite (PlusMult_Co5 z HzR). reflexivity.
          -- intro Hnz0. apply Hzne.
             assert (Ht : (-z) + z = 0) by (exact (eq_trans (Plus_P4 (-z) z (Plus_neg1a z HzR) HzR) (Plus_neg2 z HzR))).
             rewrite Hnz0 in Ht.
             rewrite (eq_trans (Plus_P4 0 z H0R HzR) (Plus_P1 z HzR)) in Ht. exact Ht.
      + assert (Hz0eq : z = 0) by (exact (proj1 (MKT41 0 E0 z) Hz0)).
        exfalso. apply Hzne. exact Hz0eq. }
  idtac. (* ---------- Claim A : no positive natural solution to m^2 = 2 n^2 ---------- *)
  assert (ClaimA : ∀ m n, m ∈ N -> n ∈ N -> m·m = (1+1)·(n·n) -> n = 0).
  { intros m n Hm Hn Heq.
    apply NNPP; intro Hnne.
    set (Bad := \{ λ u, u ∈ N /\ u <> 0 /\ (∃ m', m' ∈ N /\ m'·m' = (1+1)·(u·u)) \}).
    assert (HBadsub : Bad ⊂ N).
    { intros z Hz. apply AxiomII in Hz as [_ [HzN _]]. exact HzN. }
    assert (HBadne : Bad <> Φ).
    { intro HB0.
      assert (Hnin : n ∈ Bad).
      { apply AxiomII; split.
        - exists N; exact Hn.
        - split; [exact Hn | split; [exact Hnne | exists m; split; [exact Hm | exact Heq]]]. }
      rewrite HB0 in Hnin. exact (MKT16 Hnin). }
    destruct (Nat_P7 Bad HBadsub HBadne) as [n0 HMin0].
    destruct HMin0 as [_ [Hn0in HBle]].
    apply AxiomII in Hn0in as [_ [Hn0N [Hn0ne Hwit]]].
    destruct Hwit as [m0 [Hm0N Hm0eq]].
    assert (Hn0Z : n0 ∈ Z) by (apply N_Subset_Z; exact Hn0N).
    assert (Hm0Z : m0 ∈ Z) by (apply N_Subset_Z; exact Hm0N).
    assert (Hn0R : n0 ∈ R) by (apply N_Subset_R; exact Hn0N).
    assert (Hm0R : m0 ∈ R) by (apply N_Subset_R; exact Hm0N).
    assert (Hm0ne : m0 <> 0).
    { intro Hm00.
      rewrite Hm00 in Hm0eq.
      rewrite (PlusMult_Co1 0 H0R) in Hm0eq.
      destruct (PlusMult_Co2 (1+1) (n0·n0) H2R (Mult_close n0 n0 Hn0R Hn0R) (eq_sym Hm0eq)) as [H1 | H2].
      - exact (H2ne H1).
      - destruct (PlusMult_Co2 n0 n0 Hn0R Hn0R H2) as [H3 | H3]; exact (Hn0ne H3). }
    assert (Hevm0sq : Even (m0·m0))
      by (exists (n0·n0); split; [apply (Int_P1b n0 n0 Hn0Z Hn0Z) | exact Hm0eq]).
    assert (Hevm0 : Even m0) by (apply (Even_and_Odd_P3 m0 Hm0N Hevm0sq)).
    destruct Hevm0 as [k [HkZ Hm0k]].
    assert (HkR : k ∈ R) by (apply Z_Subset_R; exact HkZ).
    assert (HkkR : k·k ∈ R) by (apply (Mult_close k k HkR HkR)).
    assert (Hm0ge1 : 1 ≤ m0) by (apply HminN; exact Hm0N).
    assert (Hkpos : 0 < k).
    { destruct (Leq_P4 0 k H0R HkR) as [H0k | Hk0].
      - destruct (classic (k = 0)) as [Hk0eq | Hk0ne].
        + exfalso. rewrite Hk0eq in Hm0k. rewrite (PlusMult_Co1 (1+1) H2R) in Hm0k.
          exact (Hm0ne Hm0k).
        + split; [exact H0k | intro H; exact (Hk0ne (eq_sym H))].
      - exfalso.
        assert (Hle : k·(1+1) ≤ 0·(1+1))
          by (apply (OrderPM_Co7b k 0 (1+1) HkR H0R H2R Hk0 (proj1 H2pos))).
        rewrite (Mult_P4 k (1+1) HkR H2R) in Hle.
        rewrite <- Hm0k in Hle.
        rewrite (Mult_P4 0 (1+1) H0R H2R) in Hle.
        rewrite (PlusMult_Co1 (1+1) H2R) in Hle.
        assert (H0le : 0 ≤ m0) by (apply (Leq_P3 0 1 m0 H0R H1R Hm0R (proj1 OrderPM_Co9) Hm0ge1)).
        assert (Hm0e0 : m0 = 0) by (apply (Leq_P2 m0 0 Hm0R H0R Hle H0le)).
        exact (Hm0ne Hm0e0). }
    assert (HkN : k ∈ N) by (apply posZ_in_N; [exact HkZ | exact Hkpos]).
    (* n0^2 = 2 k^2 *)
    assert (Hsq_eq : n0·n0 = (1+1)·(k·k)).
    { assert (Htmp : ((1+1)·k)·((1+1)·k) = (1+1)·(n0·n0)) by (rewrite <- Hm0k; exact Hm0eq).
      rewrite (sq_expand k HkR) in Htmp.
      symmetry.
      apply (cancel2 ((1+1)·(k·k)) (n0·n0) (Mult_close (1+1) (k·k) H2R HkkR) (Mult_close n0 n0 Hn0R Hn0R)).
      exact Htmp. }
    assert (Hevn0sq : Even (n0·n0))
      by (exists (k·k); split; [apply (Int_P1b k k HkZ HkZ) | exact Hsq_eq]).
    assert (Hevn0 : Even n0) by (apply (Even_and_Odd_P3 n0 Hn0N Hevn0sq)).
    destruct Hevn0 as [j [HjZ Hn0j]].
    assert (HjR : j ∈ R) by (apply Z_Subset_R; exact HjZ).
    assert (HjjR : j·j ∈ R) by (apply (Mult_close j j HjR HjR)).
    assert (Hn0ge1 : 1 ≤ n0) by (apply HminN; exact Hn0N).
    assert (Hjpos : 0 < j).
    { destruct (Leq_P4 0 j H0R HjR) as [H0j | Hj0].
      - destruct (classic (j = 0)) as [Hj0eq | Hj0ne].
        + exfalso. rewrite Hj0eq in Hn0j. rewrite (PlusMult_Co1 (1+1) H2R) in Hn0j.
          exact (Hn0ne Hn0j).
        + split; [exact H0j | intro H; exact (Hj0ne (eq_sym H))].
      - exfalso.
        assert (Hle : j·(1+1) ≤ 0·(1+1))
          by (apply (OrderPM_Co7b j 0 (1+1) HjR H0R H2R Hj0 (proj1 H2pos))).
        rewrite (Mult_P4 j (1+1) HjR H2R) in Hle.
        rewrite <- Hn0j in Hle.
        rewrite (Mult_P4 0 (1+1) H0R H2R) in Hle.
        rewrite (PlusMult_Co1 (1+1) H2R) in Hle.
        assert (H0le : 0 ≤ n0) by (apply (Leq_P3 0 1 n0 H0R H1R Hn0R (proj1 OrderPM_Co9) Hn0ge1)).
        assert (Hn0e0 : n0 = 0) by (apply (Leq_P2 n0 0 Hn0R H0R Hle H0le)).
        exact (Hn0ne Hn0e0). }
    assert (HjN : j ∈ N) by (apply posZ_in_N; [exact HjZ | exact Hjpos]).
    assert (Hsqk_eq : k·k = (1+1)·(j·j)).
    { assert (Htmp : ((1+1)·j)·((1+1)·j) = (1+1)·(k·k)) by (rewrite <- Hn0j; exact Hsq_eq).
      rewrite (sq_expand j HjR) in Htmp.
      symmetry.
      apply (cancel2 ((1+1)·(j·j)) (k·k) (Mult_close (1+1) (j·j) H2R HjjR) (Mult_close k k HkR HkR)).
      exact Htmp. }
    assert (Hjlt : j < n0).
    { assert (Hjj : (1+1)·j = j + j).
      { transitivity ((1·j) + (1·j)).
        - apply (Mult_P5 1 1 j H1R H1R HjR).
        - rewrite (eq_trans (Mult_P4 1 j H1R HjR) (Mult_P1 j HjR)). reflexivity. }
      rewrite Hn0j, Hjj.
      assert (Ht := OrderPM_Co1 0 j j H0R HjR HjR Hjpos).
      rewrite (eq_trans (Plus_P4 0 j H0R HjR) (Plus_P1 j HjR)) in Ht.
      exact Ht. }
    assert (Hjin : j ∈ Bad).
    { apply AxiomII; split.
      - exists N; exact HjN.
      - split; [exact HjN | split; [intro Hj0; exact (proj2 Hjpos (eq_sym Hj0)) | exists k; split; [exact HkN | exact Hsqk_eq]]]. }
    assert (Hn0lej : n0 ≤ j) by (apply HBle; exact Hjin).
    assert (Hn0ltn0 : n0 < n0)
      by (apply (Order_Co2 n0 j n0 Hn0R HjR Hn0R); right; split; [exact Hn0lej | exact Hjlt]).
    exact ((proj2 Hn0ltn0) eq_refl). }
  (* ---------- Claim C : no integer solution ---------- *)
  assert (ClaimC : ∀ m n, m ∈ Z -> n ∈ Z -> m·m = (1+1)·(n·n) -> n = 0).
  { intros m n HmZ HnZ HbEq.
    apply NNPP; intro Hnne.
    assert (HmR : m ∈ R) by (apply Z_Subset_R; exact HmZ).
    assert (HnR : n ∈ R) by (apply Z_Subset_R; exact HnZ).
    assert (Hmne : m <> 0).
    { intro Hm0. rewrite Hm0 in HbEq. rewrite (PlusMult_Co1 0 H0R) in HbEq.
      destruct (PlusMult_Co2 (1+1) (n·n) H2R (Mult_close n n HnR HnR) (eq_sym HbEq)) as [H1 | H2].
      - exact (H2ne H1).
      - destruct (PlusMult_Co2 n n HnR HnR H2) as [H3 | H3]; exact (Hnne H3). }
    destruct (absN m HmZ Hmne) as [m' [Hm'N [Hm'sq Hm'ne]]].
    destruct (absN n HnZ Hnne) as [n' [Hn'N [Hn'sq Hn'ne]]].
    assert (HbEq' : m'·m' = (1+1)·(n'·n')).
    { rewrite Hm'sq. rewrite Hn'sq. exact HbEq. }
    exact (Hn'ne (ClaimA m' n' Hm'N Hn'N HbEq')). }
  (* ---------- the set S and its supremum ---------- *)
  set (SS := (\{ λ x, x ∈ R /\ x · x < 1 + 1 \})).
  assert (HSsub : SS ⊂ R).
  { intros z Hz. apply AxiomII in Hz as [_ [HzR _]]. exact HzR. }
  assert (H0inS : 0 ∈ SS).
  { apply AxiomII; split.
    - exists R; exact H0R.
    - split; [exact H0R |].
      rewrite (PlusMult_Co1 0 H0R). exact H2pos. }
  assert (HSne : SS <> Φ).
  { intro HS0. rewrite HS0 in H0inS. exact (MKT16 H0inS). }
  assert (HSbd : ∃ c, Upper SS c).
  { exists (1+1). unfold Upper. split; [exact HSsub | split; [exact H2R |]].
    intros x HxS. apply AxiomII in HxS as [_ [HxR Hxlt]].
    destruct (Leq_P4 x (1+1) HxR H2R) as [Hle | Hle].
    - exact Hle.
    - exfalso.
      assert (H0x : 0 < x)
        by (apply (Order_Co2 0 (1+1) x H0R H2R HxR); left; split; [exact H2pos | exact Hle]).
      assert (Hsq_le : (1+1)·(1+1) ≤ x·x).
      { assert (Ha : (1+1)·(1+1) ≤ x·(1+1))
          by (apply (OrderPM_Co7b (1+1) x (1+1) H2R HxR H2R Hle (proj1 H2pos))).
        assert (Hb : (1+1)·x ≤ x·x)
          by (apply (OrderPM_Co7b (1+1) x x H2R HxR HxR Hle (proj1 H0x))).
        rewrite (Mult_P4 x (1+1) HxR H2R) in Ha.
        exact (Leq_P3 ((1+1)·(1+1)) ((1+1)·x) (x·x)
                 (Mult_close (1+1) (1+1) H2R H2R) (Mult_close (1+1) x H2R HxR) (Mult_close x x HxR HxR) Ha Hb). }
      assert (Hxx_le : x·x ≤ (1+1)) by (exact (proj1 Hxlt)).
      assert (H2lt2sq : (1+1) < (1+1)·(1+1)).
      { assert (Ht : 1·(1+1) < (1+1)·(1+1))
          by (apply (OrderPM_Co7a 1 (1+1) (1+1) H1R H2R H2R Hlt11 H2pos)).
        rewrite (eq_trans (Mult_P4 1 (1+1) H1R H2R) (Mult_P1 (1+1) H2R)) in Ht. exact Ht. }
      assert (Hc : (1+1) < (1+1))
        by (apply (Order_Co2 (1+1) ((1+1)·(1+1)) (1+1) H2R (Mult_close (1+1) (1+1) H2R H2R) H2R);
            left; split; [exact H2lt2sq |
                          exact (Leq_P3 ((1+1)·(1+1)) (x·x) (1+1) (Mult_close (1+1) (1+1) H2R H2R) (Mult_close x x HxR HxR) H2R Hsq_le Hxx_le)]).
      exact ((proj2 Hc) eq_refl). }
  destruct (SupT SS HSsub HSne HSbd) as [s [HSup1 Huniq]].
  destruct HSup1 as [HUp Hdens].
  destruct HUp as [HSsub2 [HsR HsUp]].
  assert (Hsge0 : 0 ≤ s) by (apply HsUp; exact H0inS).
  assert (HssR : s·s ∈ R) by (apply (Mult_close s s HsR HsR)).
  assert (Hssge0 : 0 ≤ s·s) by (apply (Mult_Leq s s HsR HsR Hsge0 Hsge0)).
  (* s <= 2 *)
  assert (Hsle2 : s ≤ (1+1)).
  { destruct (Leq_P4 s (1+1) HsR H2R) as [Hle | Hle]; [exact Hle |].
    destruct (classic (s = (1+1))) as [Heq | Hne].
    - rewrite Heq. apply Leq_P1. exact H2R.
    - exfalso.
      assert (H2lts : (1+1) < s) by (split; [exact Hle | intro H; exact (Hne (eq_sym H))]).
      destruct (Hdens (1+1) H2R H2lts) as [x1 [Hx1S Hx1gt]].
      apply AxiomII in Hx1S as [_ [Hx1R Hx1lt]].
      assert (H0x1 : 0 < x1) by (apply (Order_Co2 0 (1+1) x1 H0R H2R Hx1R); left; split; [exact H2pos | exact (proj1 Hx1gt)]).
      assert (H4lt : (1+1)·(1+1) < x1·(1+1))
        by (apply (OrderPM_Co7a (1+1) x1 (1+1) H2R Hx1R H2R Hx1gt H2pos)).
      assert (H4lt2 : (1+1)·x1 < x1·x1)
        by (apply (OrderPM_Co7a (1+1) x1 x1 H2R Hx1R Hx1R Hx1gt H0x1)).
      assert (H4lt' : (1+1)·(1+1) < x1·x1).
      { rewrite (Mult_P4 x1 (1+1) Hx1R H2R) in H4lt.
        apply (Order_Co2 ((1+1)·(1+1)) ((1+1)·x1) (x1·x1) (Mult_close (1+1) (1+1) H2R H2R) (Mult_close (1+1) x1 H2R Hx1R) (Mult_close x1 x1 Hx1R Hx1R)).
        left. split; [exact H4lt | exact (proj1 H4lt2)]. }
      assert (H2lt4 : (1+1) < (1+1)·(1+1)).
      { assert (Ht : 1·(1+1) < (1+1)·(1+1)) by (apply (OrderPM_Co7a 1 (1+1) (1+1) H1R H2R H2R Hlt11 H2pos)).
        rewrite (eq_trans (Mult_P4 1 (1+1) H1R H2R) (Mult_P1 (1+1) H2R)) in Ht. exact Ht. }
      assert (Hxx_gt : (1+1) < x1·x1)
        by (apply (Order_Co2 (1+1) ((1+1)·(1+1)) (x1·x1) H2R (Mult_close (1+1) (1+1) H2R H2R) (Mult_close x1 x1 Hx1R Hx1R)); left; split; [exact H2lt4 | exact (proj1 H4lt')]).
      exact ((proj2 Hx1lt) (eq_sym (Leq_P2 (1+1) (x1·x1) H2R (Mult_close x1 x1 Hx1R Hx1R) (proj1 Hxx_gt) (proj1 Hx1lt)))). }
  (* s^2 = 2 *)
  assert (Hss_eq : s·s = (1+1)).
  { destruct (Order_Co1 (s·s) (1+1) HssR H2R) as [Hlt | [Hgt | Heq]].
    - (* s*s < 2 : build q in SS above s *)
      exfalso.
      assert (HepsR : ((1+1) + (-(s·s))) ∈ R)
        by (apply (Plus_close (1+1) (-(s·s)) H2R (Plus_neg1a (s·s) HssR))).
      assert (Heps_pos : 0 < ((1+1) + (-(s·s)))).
      { assert (Ht : s·s + (-(s·s)) < (1+1) + (-(s·s)))
          by (apply (OrderPM_Co1 (s·s) (1+1) (-(s·s)) HssR H2R (Plus_neg1a (s·s) HssR) Hlt)).
        rewrite (Plus_neg2 (s·s) HssR) in Ht.
        exact Ht. }
      assert (Heps_le2 : ((1+1) + (-(s·s))) ≤ (1+1)).
      { assert (Hnegsq : (-(s·s)) ≤ 0) by (apply (OrderPM_Co2b (s·s) HssR Hssge0)).
        assert (Ht := OrderPM_Co3 (1+1) (1+1) (-(s·s)) 0 H2R H2R (Plus_neg1a (s·s) HssR) H0R (Leq_P1 (1+1) H2R) Hnegsq).
        rewrite (Plus_P1 (1+1) H2R) in Ht.
        exact Ht. }
      assert (H4pos : 0 < ((1+1)+(1+1))).
      { assert (Ht := OrderPM_Co4 0 (1+1) 0 (1+1) H0R H2R H0R H2R (proj1 H2pos) H2pos).
        rewrite (eq_trans (Plus_P4 0 0 H0R H0R) (Plus_P1 0 H0R)) in Ht. exact Ht. }
      assert (H4ge : 0 ≤ ((1+1)+(1+1))) by (exact (proj1 H4pos)).
      assert (Hss_ge : 0 ≤ (s+s)).
      { assert (Ht := OrderPM_Co3 0 s 0 s H0R HsR H0R HsR Hsge0 Hsge0).
        rewrite (eq_trans (Plus_P4 0 0 H0R H0R) (Plus_P1 0 H0R)) in Ht. exact Ht. }
      assert (Hss_geR : (s+s) ∈ R) by (apply (Plus_close s s HsR HsR)).
      assert (HDR : (((1+1)+(1+1)) + ((1+1) + (-(s·s)))) ∈ R)
        by (apply (Plus_close ((1+1)+(1+1)) ((1+1) + (-(s·s))) H4R HepsR)).
      set (eps := ((1+1) + (-(s·s)))).
      set (D := (((1+1)+(1+1)) + eps)).
      assert (HDR' : D ∈ R) by (unfold D, eps; exact HDR).
      assert (HDpos : 0 < D).
      { unfold D, eps.
        assert (Ht := OrderPM_Co4 0 ((1+1)+(1+1)) 0 ((1+1)+(-(s·s))) H0R H4R H0R HepsR H4ge Heps_pos).
        rewrite (eq_trans (Plus_P4 0 0 H0R H0R) (Plus_P1 0 H0R)) in Ht.
        exact Ht. }
      set (den := ((s+s) + D)).
      assert (HdenR : den ∈ R) by (unfold den; apply (Plus_close (s+s) D Hss_geR HDR')).
      assert (Hden_pos : 0 < den).
      { unfold den.
        assert (Ht := OrderPM_Co4 0 (s+s) 0 D H0R Hss_geR H0R HDR' Hss_ge HDpos).
        rewrite (eq_trans (Plus_P4 0 0 H0R H0R) (Plus_P1 0 H0R)) in Ht.
        exact Ht. }
      assert (Hden_ne : den <> 0) by (intro H; exact (proj2 Hden_pos (eq_sym H))).
      assert (HdenR0 : den ∈ (R ~ [0])).
      { unfold Setminus. apply AxiomII; split.
        - exists R; exact HdenR.
        - split; [exact HdenR | apply AxiomII; split; [exists R; exact HdenR | intro Hin; apply Hden_ne; exact (proj1 (MKT41 0 E0 den) Hin)]]. }
      assert (HdeninvR0 : (den⁻) ∈ (R ~ [0])) by (apply (Mult_inv1 den HdenR0)).
      assert (HdeninvR : (den⁻) ∈ R)
        by (pose proof HdeninvR0 as H; unfold Setminus in H; apply AxiomII in H as [_ [Hr _]]; exact Hr).
      assert (Hdeninvpos : 0 < (den⁻)) by (apply (OrderPM_Co10 den HdenR Hden_pos)).
      set (t := (eps / den)).
      assert (HtR : t ∈ R) by (unfold t; apply (Mult_close eps (den⁻) HepsR HdeninvR)).
      assert (Htden : t·den = eps).
      { unfold t. transitivity (eps · (den⁻ · den)).
        - exact (eq_sym (Mult_P3 eps (den⁻) den HepsR HdeninvR HdenR)).
        - rewrite (Mult_P4 (den⁻) den HdeninvR HdenR). rewrite (Mult_inv2 den HdenR0). apply (Mult_P1 eps HepsR). }
      assert (Ht_pos : 0 < t).
      { unfold t. apply (OrderPM_Co5 eps (den⁻) HepsR HdeninvR). left. split; [exact Heps_pos | exact Hdeninvpos]. }
      assert (Heps_lt : eps < D·den).
      { assert (HepsD : eps < D).
        { unfold D, eps.
          assert (Ht := OrderPM_Co1 0 ((1+1)+(1+1)) ((1+1)+(-(s·s))) H0R H4R HepsR H4pos).
          rewrite (eq_trans (Plus_P4 0 ((1+1)+(-(s·s))) H0R HepsR) (Plus_P1 ((1+1)+(-(s·s))) HepsR)) in Ht.
          exact Ht. }
        assert (HD_le : D ≤ D·den).
        { assert (H2le4 : (1+1) ≤ ((1+1)+(1+1))).
          { assert (Ht := Plus_Leq 0 (1+1) (1+1) H0R H2R H2R (proj1 H2pos)).
            rewrite (eq_trans (Plus_P4 0 (1+1) H0R H2R) (Plus_P1 (1+1) H2R)) in Ht. exact Ht. }
          assert (H1le4 : 1 ≤ ((1+1)+(1+1))) by (apply (Leq_P3 1 (1+1) ((1+1)+(1+1)) H1R H2R H4R (proj1 Hlt11) H2le4)).
          assert (H4leD : ((1+1)+(1+1)) ≤ D).
          { unfold D.
            assert (Ht := Plus_Leq 0 eps ((1+1)+(1+1)) H0R HepsR H4R (proj1 Heps_pos)).
            rewrite (eq_trans (Plus_P4 0 ((1+1)+(1+1)) H0R H4R) (Plus_P1 ((1+1)+(1+1)) H4R)) in Ht.
            rewrite (Plus_P4 eps ((1+1)+(1+1)) HepsR H4R) in Ht. exact Ht. }
          assert (H1leD : 1 ≤ D) by (apply (Leq_P3 1 ((1+1)+(1+1)) D H1R H4R HDR' H1le4 H4leD)).
          assert (HD_leden : D ≤ den).
          { unfold den.
            assert (Ht := Plus_Leq 0 (s+s) D H0R Hss_geR HDR' Hss_ge).
            rewrite (eq_trans (Plus_P4 0 D H0R HDR') (Plus_P1 D HDR')) in Ht. exact Ht. }
          assert (H1den : 1 ≤ den) by (apply (Leq_P3 1 D den H1R HDR' HdenR H1leD HD_leden)).
          assert (Ht := OrderPM_Co7b 1 den D H1R HdenR HDR' H1den (proj1 HDpos)).
          rewrite (Mult_P4 1 D H1R HDR') in Ht.
          rewrite (Mult_P1 D HDR') in Ht.
          rewrite (Mult_P4 den D HdenR HDR') in Ht.
          exact Ht. }
        assert (Ht := Order_Co2 eps D (D·den) HepsR HDR' (Mult_close D den HDR' HdenR)).
        apply Ht. left. split; [exact HepsD | exact HD_le]. }
      assert (Ht_lt_D : t < D).
      { assert (Ht := OrderPM_Co7a eps (D·den) (den⁻) HepsR (Mult_close D den HDR' HdenR) HdeninvR Heps_lt Hdeninvpos).
        assert (HDeq : (D·den)·(den⁻) = D).
        { transitivity (D·(den·den⁻)).
          - exact (eq_sym (Mult_P3 D den (den⁻) HDR' HdenR HdeninvR)).
          - rewrite (Mult_inv2 den HdenR0). apply (Mult_P1 D HDR'). }
        rewrite HDeq in Ht. unfold t. exact Ht. }
      assert (H2spt : (s+s) + t < den).
      { assert (Ht := OrderPM_Co1 t D (s+s) HtR HDR' Hss_geR Ht_lt_D).
        rewrite (Plus_P4 t (s+s) HtR Hss_geR) in Ht.
        rewrite (Plus_P4 D (s+s) HDR' Hss_geR) in Ht.
        unfold den. exact Ht. }
      assert (Htt_lt : t·((s+s)+t) < eps).
      { assert (Ht := OrderPM_Co7a ((s+s)+t) den t (Plus_close (s+s) t Hss_geR HtR) HdenR HtR H2spt Ht_pos).
        rewrite (Mult_P4 ((s+s)+t) t (Plus_close (s+s) t Hss_geR HtR) HtR) in Ht.
        rewrite (Mult_P4 den t HdenR HtR) in Ht.
        rewrite Htden in Ht. exact Ht. }
      assert (Hsum : s·s + eps = (1+1)).
      { unfold eps.
        rewrite (Plus_P3 (s·s) (1+1) (-(s·s)) HssR H2R (Plus_neg1a (s·s) HssR)).
        rewrite (Plus_P4 (s·s) (1+1) HssR H2R).
        rewrite <- (Plus_P3 (1+1) (s·s) (-(s·s)) H2R HssR (Plus_neg1a (s·s) HssR)).
        rewrite (Plus_neg2 (s·s) HssR). apply (Plus_P1 (1+1) H2R). }
      assert (Hqq_eq : (s+t)·(s+t) = s·s + t·((s+s)+t)).
      { rewrite (distr (s+t) s t (Plus_close s t HsR HtR) HsR HtR).
        rewrite (Mult_P4 (s+t) s (Plus_close s t HsR HtR) HsR).
        rewrite (distr s s t HsR HsR HtR).
        rewrite (Mult_P4 (s+t) t (Plus_close s t HsR HtR) HtR).
        rewrite (distr t s t HtR HsR HtR).
        rewrite (Mult_P4 t s HtR HsR).
        rewrite (distr t (s+s) t HtR (Plus_close s s HsR HsR) HtR).
        rewrite (distr t s s HtR HsR HsR).
        rewrite (Mult_P4 t s HtR HsR).
        rewrite <- (Plus_P3 (s·s) (s·t) (s·t + t·t) HssR (Mult_close s t HsR HtR) (Plus_close (s·t) (t·t) (Mult_close s t HsR HtR) (Mult_close t t HtR HtR))).
        rewrite (Plus_P3 (s·t) (s·t) (t·t) (Mult_close s t HsR HtR) (Mult_close s t HsR HtR) (Mult_close t t HtR HtR)).
        reflexivity. }
      assert (Hqq_lt : (s+t)·(s+t) < (1+1)).
      { rewrite Hqq_eq.
        assert (Hbound : s·s + t·((s+s)+t) < s·s + eps).
        { assert (Ht := OrderPM_Co1 (t·((s+s)+t)) eps (s·s) (Mult_close t ((s+s)+t) HtR (Plus_close (s+s) t Hss_geR HtR)) HepsR HssR Htt_lt).
          rewrite (Plus_P4 (t·((s+s)+t)) (s·s) (Mult_close t ((s+s)+t) HtR (Plus_close (s+s) t Hss_geR HtR)) HssR) in Ht.
          rewrite (Plus_P4 eps (s·s) HepsR HssR) in Ht. exact Ht. }
        rewrite Hsum in Hbound. exact Hbound. }
      assert (HqinS : (s+t) ∈ SS).
      { apply AxiomII; split.
        - exists R; exact (Plus_close s t HsR HtR).
        - split; [exact (Plus_close s t HsR HtR) | exact Hqq_lt]. }
      assert (Hq_gt : s < s + t).
      { assert (Ht := OrderPM_Co1 0 t s H0R HtR HsR Ht_pos).
        rewrite (eq_trans (Plus_P4 0 s H0R HsR) (Plus_P1 s HsR)) in Ht.
        rewrite (Plus_P4 t s HtR HsR) in Ht. exact Ht. }
      assert (Hqle : (s+t) ≤ s) by (apply HsUp; exact HqinS).
      assert (Hseq : s = (s+t)) by (apply (Leq_P2 s (s+t) HsR (Plus_close s t HsR HtR) (proj1 Hq_gt) Hqle)).
      exact ((proj2 Hq_gt) Hseq).
    - (* s*s > 2 : find a smaller upper bound *)
      exfalso.
      assert (Hsne0 : s <> 0).
      { intro Hs0. rewrite Hs0 in Hgt. rewrite (PlusMult_Co1 0 H0R) in Hgt.
        exact (proj2 H2pos (eq_sym (Leq_P2 (1+1) 0 H2R H0R (proj1 Hgt) (proj1 H2pos)))). }
      assert (Hs_pos : 0 < s) by (split; [exact Hsge0 | intro H0s; exact (Hsne0 (eq_sym H0s))]).
      assert (Hsgt1 : 1 < s).
      { destruct (Leq_P4 1 s H1R HsR) as [Hle | Hle].
        - split; [exact Hle |].
          intro Heq1. exfalso.
          rewrite <- Heq1 in Hgt. rewrite (Mult_P1 1 H1R) in Hgt.
          assert (H2lt2 : (1+1) < (1+1)) by (apply (Order_Co2 (1+1) 1 (1+1) H2R H1R H2R); right; split; [exact (proj1 Hgt) | exact Hlt11]).
          exact ((proj2 H2lt2) eq_refl).
        - exfalso.
          assert (Hsq_le : s·s ≤ 1).
          { assert (Ht1 : s·s ≤ 1·s) by (apply (OrderPM_Co7b s 1 s HsR H1R HsR Hle Hsge0)).
            rewrite (eq_trans (Mult_P4 1 s H1R HsR) (Mult_P1 s HsR)) in Ht1.
            exact (Leq_P3 (s·s) s 1 (Mult_close s s HsR HsR) HsR H1R Ht1 Hle). }
          assert (H2le1 : (1+1) ≤ 1) by (apply (Leq_P3 (1+1) (s·s) 1 H2R HssR H1R (proj1 Hgt) Hsq_le)).
          assert (H2lt2 : (1+1) < (1+1)) by (apply (Order_Co2 (1+1) 1 (1+1) H2R H1R H2R); right; split; [exact H2le1 | exact Hlt11]).
          exact ((proj2 H2lt2) eq_refl). }
      assert (Hss_ge2 : 0 ≤ (s+s)).
      { assert (Ht := OrderPM_Co3 0 s 0 s H0R HsR H0R HsR Hsge0 Hsge0).
        rewrite (eq_trans (Plus_P4 0 0 H0R H0R) (Plus_P1 0 H0R)) in Ht. exact Ht. }
      set (eps2 := (s·s + (-(1+1)))).
      assert (Heps2R : eps2 ∈ R) by (unfold eps2; apply (Plus_close (s·s) (-(1+1)) HssR (Plus_neg1a (1+1) H2R))).
      assert (Heps2_pos : 0 < eps2).
      { unfold eps2. assert (Ht := OrderPM_Co1 (1+1) (s·s) (-(1+1)) H2R HssR (Plus_neg1a (1+1) H2R) Hgt).
        rewrite (Plus_neg2 (1+1) H2R) in Ht. exact Ht. }
      assert (H2ssR : ((s+s)+1) ∈ R) by (apply (Plus_close (s+s) 1 (Plus_close s s HsR HsR) H1R)).
      assert (H2ss_pos : 0 < ((s+s)+1)).
      { assert (Ht := OrderPM_Co4 0 (s+s) 0 1 H0R (Plus_close s s HsR HsR) H0R H1R Hss_ge2 OrderPM_Co9).
        rewrite (eq_trans (Plus_P4 0 0 H0R H0R) (Plus_P1 0 H0R)) in Ht. exact Ht. }
      assert (H2ss_ne : ((s+s)+1) <> 0) by (intro H; exact (proj2 H2ss_pos (eq_sym H))).
      assert (H2ssR0 : ((s+s)+1) ∈ (R ~ [0])).
      { unfold Setminus. apply AxiomII; split.
        - exists R; exact H2ssR.
        - split; [exact H2ssR | apply AxiomII; split; [exists R; exact H2ssR | intro Hin; apply H2ss_ne; exact (proj1 (MKT41 0 E0 ((s+s)+1)) Hin)]]. }
      assert (H2ssinvR0 : (((s+s)+1)⁻) ∈ (R ~ [0])) by (apply (Mult_inv1 ((s+s)+1) H2ssR0)).
      assert (H2ssinvR : (((s+s)+1)⁻) ∈ R)
        by (pose proof H2ssinvR0 as H; unfold Setminus in H; apply AxiomII in H as [_ [Hr _]]; exact Hr).
      assert (H2ssinvpos : 0 < (((s+s)+1)⁻)) by (apply (OrderPM_Co10 ((s+s)+1) H2ssR H2ss_pos)).
      set (del := (eps2 / ((s+s)+1))).
      assert (HdelR : del ∈ R) by (unfold del; apply (Mult_close eps2 (((s+s)+1)⁻) Heps2R H2ssinvR)).
      assert (Hdelden : del·((s+s)+1) = eps2).
      { unfold del. transitivity (eps2 · (((s+s)+1)⁻ · ((s+s)+1))).
        - exact (eq_sym (Mult_P3 eps2 (((s+s)+1)⁻) ((s+s)+1) Heps2R H2ssinvR H2ssR)).
        - rewrite (Mult_P4 (((s+s)+1)⁻) ((s+s)+1) H2ssinvR H2ssR). rewrite (Mult_inv2 ((s+s)+1) H2ssR0). apply (Mult_P1 eps2 Heps2R). }
      assert (Hdel_pos : 0 < del).
      { unfold del. apply (OrderPM_Co5 eps2 (((s+s)+1)⁻) Heps2R H2ssinvR). left. split; [exact Heps2_pos | exact H2ssinvpos]. }
      assert (Hdel_lt1 : del < 1).
      { assert (Heps2ltden : eps2 < ((s+s)+1)).
        { assert (Hneg2lt0 : (-(1+1)) < 0) by (apply (OrderPM_Co2a (1+1) H2R H2pos)).
          assert (Heps2ltss : s·s + (-(1+1)) < s·s).
          { assert (Ht := OrderPM_Co1 (-(1+1)) 0 (s·s) (Plus_neg1a (1+1) H2R) H0R HssR Hneg2lt0).
            rewrite (Plus_P4 (-(1+1)) (s·s) (Plus_neg1a (1+1) H2R) HssR) in Ht.
            rewrite (eq_trans (Plus_P4 0 (s·s) H0R HssR) (Plus_P1 (s·s) HssR)) in Ht. exact Ht. }
          assert (H2s_eq : (1+1)·s = s+s).
          { transitivity ((1·s) + (1·s)).
            - apply (Mult_P5 1 1 s H1R H1R HsR).
            - rewrite (eq_trans (Mult_P4 1 s H1R HsR) (Mult_P1 s HsR)). reflexivity. }
          assert (Hsq_le : s·s ≤ (s+s)) by (rewrite <- H2s_eq; apply (OrderPM_Co7b s (1+1) s HsR H2R HsR Hsle2 Hsge0)).
          assert (Hsslt : (s+s) < (s+s) + 1).
          { assert (Ht := OrderPM_Co1 0 1 (s+s) H0R H1R (Plus_close s s HsR HsR) OrderPM_Co9).
            rewrite (eq_trans (Plus_P4 0 (s+s) H0R (Plus_close s s HsR HsR)) (Plus_P1 (s+s) (Plus_close s s HsR HsR))) in Ht.
            rewrite (Plus_P4 1 (s+s) H1R (Plus_close s s HsR HsR)) in Ht. exact Ht. }
          assert (Hsslt' : s·s < (s+s) + 1) by (apply (Order_Co2 (s·s) (s+s) ((s+s)+1) HssR (Plus_close s s HsR HsR) H2ssR); right; split; [exact Hsq_le | exact Hsslt]).
          unfold eps2. apply (Order_Co2 (s·s + (-(1+1))) (s·s) ((s+s)+1) (Plus_close (s·s) (-(1+1)) HssR (Plus_neg1a (1+1) H2R)) HssR H2ssR); left; split; [exact Heps2ltss | exact (proj1 Hsslt')]. }
        assert (Ht := OrderPM_Co7a eps2 ((s+s)+1) (((s+s)+1)⁻) Heps2R H2ssR H2ssinvR Heps2ltden H2ssinvpos).
        rewrite (Mult_inv2 ((s+s)+1) H2ssR0) in Ht. unfold del. exact Ht. }
      assert (HnegdelR : (-del) ∈ R) by (apply (Plus_neg1a del HdelR)).
      assert (Hnegdel1 : (-del) < 1).
      { assert (Ht := OrderPM_Co2a del HdelR Hdel_pos).
        apply (Order_Co2 (-del) 0 1 HnegdelR H0R H1R). left. split; [exact Ht | exact (proj1 OrderPM_Co9)]. }
      assert (Hssd_lt : (s+s)+(-del) < (s+s)+1).
      { assert (Ht := OrderPM_Co1 (-del) 1 (s+s) HnegdelR H1R (Plus_close s s HsR HsR) Hnegdel1).
        rewrite (Plus_P4 (-del) (s+s) HnegdelR (Plus_close s s HsR HsR)) in Ht.
        rewrite (Plus_P4 1 (s+s) H1R (Plus_close s s HsR HsR)) in Ht. exact Ht. }
      assert (HP_lt : del·((s+s)+(-del)) < eps2).
      { assert (Ht := OrderPM_Co7a ((s+s)+(-del)) ((s+s)+1) del (Plus_close (s+s) (-del) (Plus_close s s HsR HsR) HnegdelR) H2ssR HdelR Hssd_lt Hdel_pos).
        rewrite (Mult_P4 ((s+s)+(-del)) del (Plus_close (s+s) (-del) (Plus_close s s HsR HsR) HnegdelR) HdelR) in Ht.
        rewrite (Mult_P4 ((s+s)+1) del H2ssR HdelR) in Ht.
        rewrite Hdelden in Ht. exact Ht. }
      assert (HP_R : del·((s+s)+(-del)) ∈ R)
        by (apply (Mult_close del ((s+s)+(-del)) HdelR (Plus_close (s+s) (-del) (Plus_close s s HsR HsR) HnegdelR))).
      assert (HY_pos : 0 < eps2 + (-(del·((s+s)+(-del))))).
      { assert (Ht := OrderPM_Co1 (del·((s+s)+(-del))) eps2 (-(del·((s+s)+(-del)))) HP_R Heps2R (Plus_neg1a (del·((s+s)+(-del))) HP_R) HP_lt).
        rewrite (Plus_neg2 (del·((s+s)+(-del))) HP_R) in Ht. exact Ht. }
      assert (Huu : (s + (-del))·(s + (-del)) = (1+1) + (eps2 + (-(del·((s+s)+(-del)))))).
      { rewrite (sq_sub s del HsR HdelR).
        symmetry.
        unfold eps2.
        rewrite (distr del (s+s) (-del) HdelR (Plus_close s s HsR HsR) HnegdelR).
        rewrite (distr del s s HdelR HsR HsR).
        rewrite (eq_sym (neg_multR del del HdelR HdelR)).
        rewrite (Mult_P4 del s HdelR HsR).
        rewrite (neg_add (s·del + s·del) (-(del·del)) (Plus_close (s·del) (s·del) (Mult_close s del HsR HdelR) (Mult_close s del HsR HdelR)) (Plus_neg1a (del·del) (Mult_close del del HdelR HdelR))).
        rewrite (neg_add (s·del) (s·del) (Mult_close s del HsR HdelR) (Mult_close s del HsR HdelR)).
        rewrite (dblneg (del·del) (Mult_close del del HdelR HdelR)).
        rewrite (Plus_P3 (1+1) (s·s + (-(1+1))) (((-(s·del)) + (-(s·del))) + del·del) H2R (Plus_close (s·s) (-(1+1)) HssR (Plus_neg1a (1+1) H2R)) (Plus_close ((-(s·del)) + (-(s·del))) (del·del) (Plus_close (-(s·del)) (-(s·del)) (Plus_neg1a (s·del) (Mult_close s del HsR HdelR)) (Plus_neg1a (s·del) (Mult_close s del HsR HdelR))) (Mult_close del del HdelR HdelR))).
        rewrite (Plus_P3 (1+1) (s·s) (-(1+1)) H2R HssR (Plus_neg1a (1+1) H2R)).
        rewrite (Plus_P4 (1+1) (s·s) H2R HssR).
        rewrite <- (Plus_P3 (s·s) (1+1) (-(1+1)) HssR H2R (Plus_neg1a (1+1) H2R)).
        rewrite (Plus_neg2 (1+1) H2R).
        rewrite (Plus_P1 (s·s) HssR).
        rewrite <- (Plus_P3 (-(s·del)) (-(s·del)) (del·del) (Plus_neg1a (s·del) (Mult_close s del HsR HdelR)) (Plus_neg1a (s·del) (Mult_close s del HsR HdelR)) (Mult_close del del HdelR HdelR)).
        apply (Plus_P3 (s·s) (-(s·del)) ((-(s·del)) + del·del) HssR (Plus_neg1a (s·del) (Mult_close s del HsR HdelR)) (Plus_close (-(s·del)) (del·del) (Plus_neg1a (s·del) (Mult_close s del HsR HdelR)) (Mult_close del del HdelR HdelR))). }
      assert (Huu_gt : (1+1) < (s + (-del))·(s + (-del))).
      { rewrite Huu.
        assert (HYR : eps2 + (-(del·((s+s)+(-del)))) ∈ R) by (apply (Plus_close eps2 (-(del·((s+s)+(-del)))) Heps2R (Plus_neg1a (del·((s+s)+(-del))) HP_R))).
        assert (Ht := OrderPM_Co1 0 (eps2 + (-(del·((s+s)+(-del))))) (1+1) H0R HYR H2R HY_pos).
        rewrite (eq_trans (Plus_P4 0 (1+1) H0R H2R) (Plus_P1 (1+1) H2R)) in Ht.
        rewrite (Plus_P4 (eps2 + (-(del·((s+s)+(-del))))) (1+1) HYR H2R) in Ht.
        exact Ht. }
      assert (Hu_pos : 0 < s + (-del)).
      { assert (Hneg1R : (-(1)) ∈ R) by (apply (Plus_neg1a 1 H1R)).
        assert (Hneg1ltnegd : (-(1)) < (-del)).
        { assert (Ht1 := OrderPM_Co1 del 1 (-(1)) HdelR H1R Hneg1R Hdel_lt1).
          rewrite (Plus_neg2 1 H1R) in Ht1.
          assert (Ht2 := OrderPM_Co1 (del + (-(1))) 0 (-del) (Plus_close del (-(1)) HdelR Hneg1R) H0R HnegdelR Ht1).
          rewrite (eq_trans (Plus_P4 0 (-del) H0R HnegdelR) (Plus_P1 (-del) HnegdelR)) in Ht2.
          rewrite <- (Plus_P3 del (-(1)) (-del) HdelR Hneg1R HnegdelR) in Ht2.
          rewrite (Plus_P4 (-(1)) (-del) Hneg1R HnegdelR) in Ht2.
          rewrite (Plus_P3 del (-del) (-(1)) HdelR HnegdelR Hneg1R) in Ht2.
          rewrite (Plus_neg2 del HdelR) in Ht2.
          rewrite (eq_trans (Plus_P4 0 (-(1)) H0R Hneg1R) (Plus_P1 (-(1)) Hneg1R)) in Ht2.
          exact Ht2. }
        assert (Ht := OrderPM_Co4 1 s (-(1)) (-del) H1R HsR Hneg1R HnegdelR (proj1 Hsgt1) Hneg1ltnegd).
        rewrite (Plus_neg2 1 H1R) in Ht. exact Ht. }
      assert (Hu_lt_s : s + (-del) < s).
      { assert (Ht := OrderPM_Co1 (-del) 0 s HnegdelR H0R HsR (OrderPM_Co2a del HdelR Hdel_pos)).
        rewrite (Plus_P4 (-del) s HnegdelR HsR) in Ht.
        rewrite (eq_trans (Plus_P4 0 s H0R HsR) (Plus_P1 s HsR)) in Ht. exact Ht. }
      assert (HuR : (s+(-del)) ∈ R) by (apply (Plus_close s (-del) HsR HnegdelR)).
      assert (Hupper : ∀ x, x ∈ SS -> x ≤ s + (-del)).
      { intros x HxSS. apply AxiomII in HxSS as [_ [HxR Hxlt]].
        assert (HxxR : x·x ∈ R) by (apply (Mult_close x x HxR HxR)).
        assert (HuuR2 : (s+(-del))·(s+(-del)) ∈ R) by (apply (Mult_close (s+(-del)) (s+(-del)) HuR HuR)).
        assert (Hxx_lt_uu : x·x < (s+(-del))·(s+(-del)))
          by (apply (Order_Co2 (x·x) (1+1) ((s+(-del))·(s+(-del))) HxxR H2R HuuR2); left; split; [exact Hxlt | exact (proj1 Huu_gt)]).
        destruct (Leq_P4 x (s+(-del)) HxR HuR) as [Hle | Hle]; [exact Hle |].
        exfalso.
        assert (H0x : 0 ≤ x) by (apply (Leq_P3 0 (s+(-del)) x H0R HuR HxR (proj1 Hu_pos) Hle)).
        assert (Huu_le : (s+(-del))·(s+(-del)) ≤ x·x).
        { assert (Ha : (s+(-del))·(s+(-del)) ≤ x·(s+(-del))) by (apply (OrderPM_Co7b (s+(-del)) x (s+(-del)) HuR HxR HuR Hle (proj1 Hu_pos))).
          assert (Hb : (s+(-del))·x ≤ x·x) by (apply (OrderPM_Co7b (s+(-del)) x x HuR HxR HxR Hle H0x)).
          rewrite (Mult_P4 x (s+(-del)) HxR HuR) in Ha.
          exact (Leq_P3 ((s+(-del))·(s+(-del))) ((s+(-del))·x) (x·x) HuuR2 (Mult_close (s+(-del)) x HuR HxR) HxxR Ha Hb). }
        assert (Heq2 : x·x = (s+(-del))·(s+(-del))) by (apply (Leq_P2 (x·x) ((s+(-del))·(s+(-del))) HxxR HuuR2 (proj1 Hxx_lt_uu) Huu_le)).
        exact ((proj2 Hxx_lt_uu) Heq2). }
      destruct (Hdens (s + (-del)) HuR Hu_lt_s) as [x1 [Hx1SS Hx1gt]].
      assert (Hx1R : x1 ∈ R).
      { pose proof Hx1SS as Hx1SS'. apply AxiomII in Hx1SS' as [_ [Hx1R' _]]. exact Hx1R'. }
      assert (Hx1le : x1 ≤ s + (-del)) by (apply Hupper; exact Hx1SS).
      assert (Hx1eq : x1 = s + (-del)) by (apply (Leq_P2 x1 (s+(-del)) Hx1R HuR Hx1le (proj1 Hx1gt))).
      exact ((proj2 Hx1gt) (eq_sym Hx1eq)).
    - exact Heq. }
  assert (HsnotQ : s ∉ Q).
  { intro HsQ.
    apply AxiomII in HsQ as [_ [m [n [HmZ [HnZ0 Hseqm]]]]].
    assert (HnZ : n ∈ Z).
    { pose proof HnZ0 as H. unfold Setminus in H. apply AxiomII in H as [_ [HnZ _]]. exact HnZ. }
    assert (HnR : n ∈ R) by (apply Z_Subset_R; exact HnZ).
    assert (HmR : m ∈ R) by (apply Z_Subset_R; exact HmZ).
    assert (HnR0 : n ∈ (R ~ [0])).
    { pose proof HnZ0 as H. unfold Setminus in H. apply AxiomII in H as [En [HnZ' Hnnot]].
      unfold Setminus. apply AxiomII; split.
      - exact En.
      - split; [apply Z_Subset_R; exact HnZ' | exact Hnnot]. }
    assert (HninR : (n⁻) ∈ R).
    { pose proof (Mult_inv1 n HnR0) as H. unfold Setminus in H. apply AxiomII in H as [_ [HinvR _]]. exact HinvR. }
    assert (Hnm : s = m · (n⁻)) by (exact Hseqm).
    assert (Hm_sn : m = s · n).
    { transitivity ((m · (n⁻)) · n).
      - symmetry. transitivity (m · ((n⁻) · n)).
        + symmetry. apply (Mult_P3 m (n⁻) n HmR HninR HnR).
        + rewrite (Mult_P4 (n⁻) n HninR HnR). rewrite (Mult_inv2 n HnR0). apply (Mult_P1 m HmR).
      - rewrite <- Hnm. reflexivity. }
    assert (Hmm : m·m = (1+1)·(n·n)).
    { rewrite Hm_sn.
      transitivity (s · (n · (s · n))).
      - symmetry. apply (Mult_P3 s n (s·n) HsR HnR (Mult_close s n HsR HnR)).
      - transitivity (s · ((n · s) · n)).
        + rewrite (Mult_P3 n s n HnR HsR HnR). reflexivity.
        + transitivity (s · ((s · n) · n)).
          * rewrite (Mult_P4 n s HnR HsR). reflexivity.
          * transitivity (s · (s · (n · n))).
            -- rewrite (Mult_P3 s n n HsR HnR HnR). reflexivity.
            -- transitivity ((s · s) · (n · n)).
               ++ apply (Mult_P3 s s (n·n) HsR HsR (Mult_close n n HnR HnR)).
               ++ rewrite Hss_eq. reflexivity. }
    assert (Hnne0 : n ≠ 0).
    { intro Hn0. pose proof HnZ0 as H. unfold Setminus in H. apply AxiomII in H as [_ [_ Hnnot]].
      apply AxiomII in Hnnot as [_ Hnnot'].
      exact (Hnnot' (proj2 (MKT41 0 E0 n) Hn0)). }
    exact (Hnne0 (ClaimC m n HmZ HnZ Hmm)). }
  unfold not. intro HRQ0.
  assert (HsinRQ : s ∈ (R ~ Q)).
  { unfold Setminus. apply AxiomII; split.
    - exists R; exact HsR.
    - split; [exact HsR | apply AxiomII; split; [exists R; exact HsR | exact HsnotQ]]. }
  rewrite HRQ0 in HsinRQ. exact (MKT16 HsinRQ).
Qed.

(* 阿基米德原理 *)
Proposition Arch_P1 : ∀ E, E ⊂ N -> E <> Φ -> Bounded E -> ∃ n, Max E n.
Proof.
  intros E HE Hne Hbnd.
  destruct Hbnd as [c1 [c2 [HUp _]]].
  destruct HUp as [HEsubR [Hc1R Hc1ub]].
  assert (H1R : 1 ∈ R) by (apply one_in_R_Co).
  assert (H0R : 0 ∈ R) by (apply zero_in_R).
  assert (HminN : ∀ u, u ∈ N -> 1 ≤ u)
    by (pose proof one_is_min_in_N as H; unfold Min in H; exact (proj2 (proj2 H))).
  assert (N_unb : ∃ n, n ∈ N /\ c1 < n).
  { apply NNPP. intro Hno.
    assert (Hle : ∀ n, n ∈ N -> n ≤ c1).
    { intros n Hn.
      destruct (Leq_P4 n c1 (N_Subset_R n Hn) Hc1R) as [Hnle | Hc1le]; [exact Hnle |].
      destruct (classic (c1 = n)) as [Heq | Hne2].
      - rewrite Heq. apply Leq_P1. apply N_Subset_R; exact Hn.
      - exfalso. apply Hno. exists n. split; [exact Hn | split; [exact Hc1le | exact Hne2]]. }
    assert (Hbd : ∃ c, Upper N c)
      by (exists c1; exact (conj N_Subset_R (conj Hc1R Hle))).
    assert (HNne : N <> Φ)
      by (intro H0; assert (H1 : 1 ∈ N) by (apply one_in_N); rewrite H0 in H1; exact (MKT16 H1)).
    destruct (SupT N N_Subset_R HNne Hbd) as [s [HSup1 _]].
    destruct HSup1 as [HUpN Hdens].
    destruct HUpN as [HNsubR [HsR HNsle]].
    assert (Hneg1R : (-(1)) ∈ R) by (apply (Plus_neg1a 1 H1R)).
    assert (HtR : s + (-(1)) ∈ R) by (apply (Plus_close s (-(1)) HsR Hneg1R)).
    assert (Ht_lt_s : s + (-(1)) < s).
    { assert (Hlt : (-(1)) < 0) by (apply (OrderPM_Co2a 1 H1R OrderPM_Co9)).
      assert (Ht := OrderPM_Co1 (-(1)) 0 s (Plus_neg1a 1 H1R) H0R HsR Hlt).
      rewrite (Plus_P4 (-(1)) s (Plus_neg1a 1 H1R) HsR) in Ht.
      rewrite (eq_trans (Plus_P4 0 s H0R HsR) (Plus_P1 s HsR)) in Ht.
      exact Ht. }
    destruct (Hdens (s + (-(1))) HtR Ht_lt_s) as [x [HxN Hltx]].
    assert (HxR : x ∈ R) by (apply N_Subset_R; exact HxN).
    assert (Hx1N : (x + 1) ∈ N)
      by (pose proof IndSet_N as HIN; unfold IndSet in HIN; exact (proj2 HIN x HxN)).
    assert (Hx1le : (x + 1) ≤ s) by (apply HNsle; exact Hx1N).
    assert (Hxle : x ≤ s + (-(1))).
    { assert (Ht : (x + 1) + (-(1)) ≤ s + (-(1)))
        by (apply (Plus_Leq (x+1) s (-(1)) (Plus_close x 1 HxR H1R) HsR Hneg1R Hx1le)).
      assert (Heq : (x + 1) + (-(1)) = x)
        by (transitivity (x + (1 + (-(1))));
            [symmetry; apply (Plus_P3 x 1 (-(1)) HxR H1R Hneg1R) |
             rewrite (Plus_neg2 1 H1R); apply (Plus_P1 x HxR)]).
      rewrite Heq in Ht. exact Ht. }
    assert (Heq2 : x = s + (-(1)))
      by (apply (Leq_P2 x (s+(-(1))) HxR HtR Hxle (proj1 Hltx))).
    exact ((proj2 Hltx) (eq_sym Heq2)). }
  destruct N_unb as [m0 [Hm0N Hc1ltm0]].
  set (F := \{ λ k, k ∈ N /\ (∀ x, x ∈ E -> x ≤ k) \}).
  assert (HFsub : F ⊂ N)
    by (intros z Hz; apply AxiomII in Hz as [_ [HzN _]]; exact HzN).
  assert (HFne : F <> Φ).
  { intro H0.
    assert (Hm0F : m0 ∈ F).
    { apply AxiomII; split.
      - exists N; exact Hm0N.
      - split; [exact Hm0N |].
        intros x HxE. assert (Hxle : x ≤ c1) by (apply Hc1ub; exact HxE).
        exact (Leq_P3 x c1 m0 (HEsubR x HxE) Hc1R (N_Subset_R m0 Hm0N) Hxle (proj1 Hc1ltm0)). }
    rewrite H0 in Hm0F. exact (MKT16 Hm0F). }
  destruct (Nat_P7 F HFsub HFne) as [m HminF].
  destruct HminF as [HFsubR [HmF Hminle]].
  apply AxiomII in HmF as [_ [HmN Hmub]].
  exists m. unfold Max. split; [exact HEsubR | split; [| exact Hmub]].
  assert (HmR : m ∈ R) by (apply N_Subset_R; exact HmN).
  destruct (classic (m = 1)) as [Hm1 | Hmne1].
  - destruct (MKT_nonempty E Hne) as [x0 Hx0].
    assert (Hx0N : x0 ∈ N) by (apply HE; exact Hx0).
    assert (Hx0R : x0 ∈ R) by (apply N_Subset_R; exact Hx0N).
    assert (H1le : 1 ≤ x0) by (apply HminN; exact Hx0N).
    assert (Hx0le : x0 ≤ 1) by (rewrite <- Hm1; apply Hmub; exact Hx0).
    assert (Hx0eq : x0 = 1) by (apply (Leq_P2 x0 1 Hx0R H1R Hx0le H1le)).
    rewrite Hm1. rewrite <- Hx0eq. exact Hx0.
  - assert (Hm1N : m + (-(1)) ∈ N) by (apply (Nat_P2 m HmN Hmne1)).
    assert (Hneg1R : (-(1)) ∈ R) by (apply (Plus_neg1a 1 H1R)).
    assert (Hm1R : m + (-(1)) ∈ R) by (apply (Plus_close m (-(1)) HmR Hneg1R)).
    assert (Hm1ltm : m + (-(1)) < m).
    { assert (Hlt : (-(1)) < 0) by (apply (OrderPM_Co2a 1 H1R OrderPM_Co9)).
      assert (Ht := OrderPM_Co1 (-(1)) 0 m Hneg1R H0R HmR Hlt).
      rewrite (Plus_P4 (-(1)) m Hneg1R HmR) in Ht.
      rewrite (eq_trans (Plus_P4 0 m H0R HmR) (Plus_P1 m HmR)) in Ht.
      exact Ht. }
    assert (Hm1notF : ~ ((m + (-(1))) ∈ F)).
    { intro Hin.
      assert (Hmle : m ≤ m + (-(1))) by (apply Hminle; exact Hin).
      exact ((proj2 Hm1ltm) (eq_sym (Leq_P2 m (m+(-(1))) HmR Hm1R Hmle (proj1 Hm1ltm)))). }
    assert (Hex : ∃ x, x ∈ E /\ ~ (x ≤ m + (-(1)))).
    { apply NNPP. intro Hno. apply Hm1notF. apply AxiomII; split.
      - exists N; exact Hm1N.
      - split; [exact Hm1N | intros x HxE].
        apply NNPP. intro Hnx. apply Hno. exists x. split; [exact HxE | exact Hnx]. }
    destruct Hex as [x0 [Hx0E Hx0gt]].
    assert (Hx0N : x0 ∈ N) by (apply HE; exact Hx0E).
    assert (Hx0R : x0 ∈ R) by (apply N_Subset_R; exact Hx0N).
    assert (Hm1lex0 : m + (-(1)) ≤ x0).
    { destruct (Leq_P4 (m + (-(1))) x0 Hm1R Hx0R) as [Hle | Hle]; [exact Hle |].
      exfalso. apply Hx0gt. exact Hle. }
    assert (Hm1ne : m + (-(1)) ≠ x0)
      by (intro Heq; apply Hx0gt; rewrite Heq; apply Leq_P1; exact Hx0R).
    assert (Hm1ltx0 : m + (-(1)) < x0) by (split; [exact Hm1lex0 | exact Hm1ne]).
    assert (Hle' : (m + (-(1))) + 1 ≤ x0) by (apply (Nat_P4 x0 (m + (-(1))) Hx0N Hm1N Hm1ltx0)).
    assert (Hm_simpl : (m + (-(1))) + 1 = m)
      by (transitivity (m + ((-(1)) + 1));
          [symmetry; apply (Plus_P3 m (-(1)) 1 HmR Hneg1R H1R) |
           rewrite (eq_trans (Plus_P4 (-(1)) 1 Hneg1R H1R) (Plus_neg2 1 H1R)); apply (Plus_P1 m HmR)]).
    rewrite Hm_simpl in Hle'.
    assert (Hx0m : x0 = m) by (apply (Leq_P2 x0 m Hx0R HmR (Hmub x0 Hx0E) Hle')).
    rewrite <- Hx0m. exact Hx0E.
Qed.

Proposition Arch_P2 : ~ ∃ n, Upper N n.
Proof.
  intro Hex. destruct Hex as [n [HNsub [HnR HNle]]].
  assert (H1R : 1 ∈ R) by (apply one_in_R_Co).
  assert (H0R : 0 ∈ R) by (apply zero_in_R).
  assert (Hneg1R : (-(1)) ∈ R) by (apply (Plus_neg1a 1 H1R)).
  assert (HNne : N <> Φ)
    by (intro H0; assert (H1 : 1 ∈ N) by (apply one_in_N); rewrite H0 in H1; exact (MKT16 H1)).
  assert (Hbd : ∃ c, Upper N c) by (exists n; exact (conj HNsub (conj HnR HNle))).
  destruct (SupT N N_Subset_R HNne Hbd) as [s [HSup1 _]].
  destruct HSup1 as [HUpN Hdens].
  destruct HUpN as [HNsubR [HsR HNsle]].
  assert (HtR : s + (-(1)) ∈ R) by (apply (Plus_close s (-(1)) HsR Hneg1R)).
  assert (Ht_lt_s : s + (-(1)) < s).
  { assert (Hlt : (-(1)) < 0) by (apply (OrderPM_Co2a 1 H1R OrderPM_Co9)).
    assert (Ht := OrderPM_Co1 (-(1)) 0 s Hneg1R H0R HsR Hlt).
    rewrite (Plus_P4 (-(1)) s Hneg1R HsR) in Ht.
    rewrite (eq_trans (Plus_P4 0 s H0R HsR) (Plus_P1 s HsR)) in Ht.
    exact Ht. }
  destruct (Hdens (s + (-(1))) HtR Ht_lt_s) as [x [HxN Hltx]].
  assert (HxR : x ∈ R) by (apply N_Subset_R; exact HxN).
  assert (Hx1N : (x + 1) ∈ N)
    by (pose proof IndSet_N as HIN; unfold IndSet in HIN; exact (proj2 HIN x HxN)).
  assert (Hx1le : (x + 1) ≤ s) by (apply HNsle; exact Hx1N).
  assert (Hxle : x ≤ s + (-(1))).
  { assert (Ht : (x + 1) + (-(1)) ≤ s + (-(1)))
      by (apply (Plus_Leq (x+1) s (-(1)) (Plus_close x 1 HxR H1R) HsR Hneg1R Hx1le)).
    assert (Heq : (x + 1) + (-(1)) = x)
      by (transitivity (x + (1 + (-(1))));
          [symmetry; apply (Plus_P3 x 1 (-(1)) HxR H1R Hneg1R) |
           rewrite (Plus_neg2 1 H1R); apply (Plus_P1 x HxR)]).
    rewrite Heq in Ht. exact Ht. }
  assert (Heq2 : x = s + (-(1)))
    by (apply (Leq_P2 x (s+(-(1))) HxR HtR Hxle (proj1 Hltx))).
  exact ((proj2 Hltx) (eq_sym Heq2)).
Qed.

Proposition Arch_P3a : ∀ E, E ⊂ Z -> E <> Φ -> (∃ x, Upper E x)
  -> ∃ n, Max E n.
Proof.
  intros E HEZ Hne [cc HUp].
  destruct HUp as [HEsubR [HccR Hccub]].
  assert (H1R : 1 ∈ R) by (apply one_in_R_Co).
  assert (H0R : 0 ∈ R) by (apply zero_in_R).
  assert (HminN : ∀ u, u ∈ N -> 1 ≤ u)
    by (pose proof one_is_min_in_N as H; unfold Min in H; exact (proj2 (proj2 H))).
  assert (ArchN : ∀ y, y ∈ R -> ∃ n, n ∈ N /\ y < n).
  { intros y Hy. apply NNPP. intro Hno.
    assert (Hle : ∀ n, n ∈ N -> n ≤ y).
    { intros n Hn.
      destruct (Leq_P4 n y (N_Subset_R n Hn) Hy) as [Hnle | Hyle]; [exact Hnle |].
      destruct (classic (y = n)) as [Heq | Hne2].
      - rewrite Heq. apply Leq_P1. exact (N_Subset_R n Hn).
      - exfalso. apply Hno. exists n. split; [exact Hn | split; [exact Hyle | exact Hne2]]. }
    apply Arch_P2. exists y. unfold Upper. split; [exact N_Subset_R | split; [exact Hy | exact Hle]]. }
  assert (posZ_in_N : ∀ d, d ∈ Z -> 0 < d -> d ∈ N).
  { intros d HdZ H0d.
    assert (E0 : Ensemble 0) by (exists R; exact H0R).
    assert (HdR : d ∈ R) by (apply Z_Subset_R; exact HdZ).
    unfold Z in HdZ. apply MKT4 in HdZ as [HdN | HdRest].
    - exact HdN.
    - apply MKT4 in HdRest as [HdNegN | Hd0].
      + exfalso.
        apply AxiomII in HdNegN as [Ed Hneg].
        assert (HnegR : (-d) ∈ R) by (apply (Plus_neg1a d HdR)).
        assert (H1d : 1 ≤ (-d)) by (apply HminN; exact Hneg).
        assert (H0dle : 0 ≤ d) by (exact (proj1 H0d)).
        assert (Hle : 1 + 0 ≤ (-d) + d) by (apply (OrderPM_Co3 1 (-d) 0 d H1R HnegR H0R HdR H1d H0dle)).
        assert (Hle' : 1 ≤ 0).
        { rewrite (Plus_P1 1 H1R) in Hle.
          rewrite (eq_trans (Plus_P4 (-d) d HnegR HdR) (Plus_neg2 d HdR)) in Hle.
          exact Hle. }
        assert (H01 : 0 ≤ 1) by (exact (proj1 OrderPM_Co9)).
        assert (H10eq : 1 = 0) by (apply (Leq_P2 1 0 H1R H0R Hle' H01)).
        exact (proj2 OrderPM_Co9 (eq_sym H10eq)).
      + exfalso.
        assert (Hd0eq : d = 0) by (exact (proj1 (MKT41 0 E0 d) Hd0)).
        exact (proj2 H0d (eq_sym Hd0eq)). }
  assert (dblneg : ∀ a, a ∈ R -> -(-a) = a).
  { intros a Ha.
    assert (Hnega : -a ∈ R) by (apply (Plus_neg1a a Ha)).
    assert (Hadd : (-a) + a = 0) by (exact (eq_trans (Plus_P4 (-a) a Hnega Ha) (Plus_neg2 a Ha))).
    assert (Hadd2 : (-a) + (-(-a)) = 0) by (apply (Plus_neg2 (-a) Hnega)).
    destruct (Plus_Co2 (-a) Hnega) as [x0 [[_ _] Huniq]].
    assert (He1 : x0 = a) by (exact (Huniq a (conj Ha Hadd))).
    assert (He2 : x0 = -(-a)) by (exact (Huniq (-(-a)) (conj (Plus_neg1a (-a) Hnega) Hadd2))).
    rewrite <- He2. exact He1. }
  assert (neg_add : ∀ a b, a ∈ R -> b ∈ R -> -(a + b) = (-a) + (-b)).
  { intros a b Ha Hb.
    assert (Hnega : -a ∈ R) by (apply (Plus_neg1a a Ha)).
    assert (Hnegb : -b ∈ R) by (apply (Plus_neg1a b Hb)).
    assert (Hab : (a + b) ∈ R) by (apply (Plus_close a b Ha Hb)).
    assert (HsumR : ((-a) + (-b)) ∈ R) by (apply (Plus_close (-a) (-b) Hnega Hnegb)).
    assert (Hzero : (a + b) + ((-a) + (-b)) = 0).
    { transitivity (((a + b) + (-a)) + (-b)).
      - apply (Plus_P3 (a + b) (-a) (-b) Hab Hnega Hnegb).
      - assert (Hmid : (a + b) + (-a) = b).
        { transitivity ((b + a) + (-a)).
          - rewrite (Plus_P4 a b Ha Hb). reflexivity.
          - transitivity (b + (a + (-a))).
            + symmetry. apply (Plus_P3 b a (-a) Hb Ha Hnega).
            + transitivity (b + 0).
              * rewrite (Plus_neg2 a Ha). reflexivity.
              * apply (Plus_P1 b Hb). }
        rewrite Hmid. apply (Plus_neg2 b Hb). }
    assert (Hres : ((-a) + (-b)) = 0 + (-(a + b)))
      by (apply (Plus_Co3 (a + b) ((-a) + (-b)) 0 Hab HsumR H0R Hzero)).
    assert (H0y : 0 + (-(a + b)) = -(a + b))
      by (exact (eq_trans (Plus_P4 0 (-(a + b)) H0R (Plus_neg1a (a + b) Hab))
                          (Plus_P1 (-(a + b)) (Plus_neg1a (a + b) Hab)))).
    rewrite H0y in Hres. symmetry. exact Hres. }
  assert (sub_self : ∀ a b, a ∈ R -> b ∈ R -> a + (-(a + (-b))) = b).
  { intros a b Ha Hb.
    assert (Hnegb : -b ∈ R) by (apply (Plus_neg1a b Hb)).
    assert (Hab : (a + (-b)) ∈ R) by (apply (Plus_close a (-b) Ha Hnegb)).
    assert (Hnega : -a ∈ R) by (apply (Plus_neg1a a Ha)).
    assert (Hnain : -(a + (-b)) = (-a) + (-(-b))) by (apply (neg_add a (-b) Ha Hnegb)).
    assert (Hdbl : -(-b) = b) by (apply (dblneg b Hb)).
    rewrite Hnain. rewrite Hdbl.
    transitivity ((a + (-a)) + b).
    - apply (Plus_P3 a (-a) b Ha Hnega Hb).
    - rewrite (Plus_neg2 a Ha). exact (eq_trans (Plus_P4 0 b H0R Hb) (Plus_P1 b Hb)). }
  assert (neg_le : ∀ a b, a ∈ R -> b ∈ R -> a ≤ b -> -b ≤ -a).
  { intros a b Ha Hb Hle.
    assert (Hnega : -a ∈ R) by (apply (Plus_neg1a a Ha)).
    assert (Hnegb : -b ∈ R) by (apply (Plus_neg1a b Hb)).
    assert (Ht1 : a + (-b) ≤ b + (-b)) by (apply (Plus_Leq a b (-b) Ha Hb Hnegb Hle)).
    rewrite (Plus_neg2 b Hb) in Ht1.
    assert (Ht2 : (a + (-b)) + (-a) ≤ 0 + (-a))
      by (apply (Plus_Leq (a + (-b)) 0 (-a) (Plus_close a (-b) Ha Hnegb) H0R Hnega Ht1)).
    rewrite (eq_trans (Plus_P4 0 (-a) H0R Hnega) (Plus_P1 (-a) Hnega)) in Ht2.
    assert (Heq : (a + (-b)) + (-a) = -b).
    { transitivity ((-b) + (a + (-a))).
      - rewrite (Plus_P4 a (-b) Ha Hnegb).
        symmetry. apply (Plus_P3 (-b) a (-a) Hnegb Ha Hnega).
      - rewrite (Plus_neg2 a Ha). apply (Plus_P1 (-b) Hnegb). }
    rewrite Heq in Ht2. exact Ht2. }
  destruct (ArchN cc HccR) as [m0 [Hm0N Hccltm0]].
  assert (Hm0ub : ∀ x, x ∈ E -> x ≤ m0).
  { intros x HxE. assert (Hxle : x ≤ cc) by (apply Hccub; exact HxE).
    exact (Leq_P3 x cc m0 (HEsubR x HxE) HccR (N_Subset_R m0 Hm0N) Hxle (proj1 Hccltm0)). }
  destruct (classic (m0 ∈ E)) as [Hm0E | Hm0notE].
  - exists m0. unfold Max. split; [exact HEsubR | split; [exact Hm0E | exact Hm0ub]].
  - set (D := \{ λ j, j ∈ N /\ (m0 + (-j)) ∈ E \}).
    assert (HDsub : D ⊂ N)
      by (intros z Hz; apply AxiomII in Hz as [_ [HzN _]]; exact HzN).
    assert (HDne : D <> Φ).
    { destruct (MKT_nonempty E Hne) as [x0 Hx0E].
      assert (Hx0Z : x0 ∈ Z) by (apply HEZ; exact Hx0E).
      assert (Hx0R : x0 ∈ R) by (apply Z_Subset_R; exact Hx0Z).
      assert (Hnegx0Z : (-x0) ∈ Z) by (apply (proj1 (Int_P3 x0 Hx0Z))).
      assert (HjZ : (m0 + (-x0)) ∈ Z) by (apply (Int_P1a m0 (-x0) (N_Subset_Z m0 Hm0N) Hnegx0Z)).
      assert (Hx0le : x0 ≤ m0) by (apply Hm0ub; exact Hx0E).
      assert (Hx0ne : x0 ≠ m0) by (intro Heq; apply Hm0notE; rewrite <- Heq; exact Hx0E).
      assert (Hjpos : 0 < (m0 + (-x0))).
      { assert (Ht : x0 + (-x0) < m0 + (-x0))
          by (apply (OrderPM_Co1 x0 m0 (-x0) Hx0R (N_Subset_R m0 Hm0N) (Plus_neg1a x0 Hx0R) (conj Hx0le Hx0ne))).
        rewrite (Plus_neg2 x0 Hx0R) in Ht. exact Ht. }
      assert (HjN : (m0 + (-x0)) ∈ N) by (apply posZ_in_N; [exact HjZ | exact Hjpos]).
      assert (Hjmem : (m0 + (-(m0 + (-x0)))) ∈ E)
        by (rewrite (sub_self m0 x0 (N_Subset_R m0 Hm0N) Hx0R); exact Hx0E).
      assert (HjinD : (m0 + (-x0)) ∈ D).
      { apply AxiomII; split.
        - exists N; exact HjN.
        - split; [exact HjN | exact Hjmem]. }
      intro H0. rewrite H0 in HjinD. exact (MKT16 HjinD). }
    destruct (Nat_P7 D HDsub HDne) as [j0 HminD].
    destruct HminD as [HDsubR [Hj0D Hminle]].
    apply AxiomII in Hj0D as [_ [Hj0N Hj0E]].
    exists (m0 + (-j0)). unfold Max. split; [exact HEsubR | split; [exact Hj0E |]].
    intros x HxE.
    assert (HxZ : x ∈ Z) by (apply HEZ; exact HxE).
    assert (HxR : x ∈ R) by (apply Z_Subset_R; exact HxZ).
    assert (HmxR : (m0 + (-x)) ∈ R)
      by (apply (Plus_close m0 (-x) (N_Subset_R m0 Hm0N) (Plus_neg1a x HxR))).
    assert (Hxle : x ≤ m0) by (apply Hm0ub; exact HxE).
    assert (Hxne : x ≠ m0) by (intro Heq; apply Hm0notE; rewrite <- Heq; exact HxE).
    assert (HjZ : (m0 + (-x)) ∈ Z)
      by (apply (Int_P1a m0 (-x) (N_Subset_Z m0 Hm0N) (proj1 (Int_P3 x HxZ)))).
    assert (Hjpos : 0 < (m0 + (-x))).
    { assert (Ht : x + (-x) < m0 + (-x))
        by (apply (OrderPM_Co1 x m0 (-x) HxR (N_Subset_R m0 Hm0N) (Plus_neg1a x HxR) (conj Hxle Hxne))).
      rewrite (Plus_neg2 x HxR) in Ht. exact Ht. }
    assert (HjN : (m0 + (-x)) ∈ N) by (apply posZ_in_N; [exact HjZ | exact Hjpos]).
    assert (HjmemE : (m0 + (-(m0 + (-x)))) ∈ E)
      by (rewrite (sub_self m0 x (N_Subset_R m0 Hm0N) HxR); exact HxE).
    assert (HjinD : (m0 + (-x)) ∈ D).
    { apply AxiomII; split.
      - exists N; exact HjN.
      - split; [exact HjN | exact HjmemE]. }
    assert (Hj0lej : j0 ≤ (m0 + (-x))) by (apply Hminle; exact HjinD).
    assert (Hj0R : j0 ∈ R) by (apply N_Subset_R; exact Hj0N).
    assert (Hnegle : (-(m0 + (-x))) ≤ (-j0))
      by (apply (neg_le j0 (m0 + (-x)) Hj0R HmxR Hj0lej)).
    assert (Hfin : x ≤ m0 + (-j0)).
    { assert (Ht := Plus_Leq (-(m0 + (-x))) (-j0) m0 (Plus_neg1a (m0+(-x)) HmxR) (Plus_neg1a j0 Hj0R) (N_Subset_R m0 Hm0N) Hnegle).
      rewrite (Plus_P4 (-(m0+(-x))) m0 (Plus_neg1a (m0+(-x)) HmxR) (N_Subset_R m0 Hm0N)) in Ht.
      rewrite (Plus_P4 (-j0) m0 (Plus_neg1a j0 Hj0R) (N_Subset_R m0 Hm0N)) in Ht.
      rewrite (sub_self m0 x (N_Subset_R m0 Hm0N) HxR) in Ht.
      exact Ht. }
    exact Hfin.
Qed.

Proposition Arch_P3b : ∀ E, E ⊂ Z -> E <> Φ -> (∃ x, Lower E x)
  -> ∃ n, Min E n.
Proof.
  intros E HEZ Hne [cc HLo].
  destruct HLo as [HEsubR [HccR Hcclb]].
  assert (H1R : 1 ∈ R) by (apply one_in_R_Co).
  assert (H0R : 0 ∈ R) by (apply zero_in_R).
  assert (HminN : ∀ u, u ∈ N -> 1 ≤ u)
    by (pose proof one_is_min_in_N as H; unfold Min in H; exact (proj2 (proj2 H))).
  assert (ArchN : ∀ y, y ∈ R -> ∃ n, n ∈ N /\ y < n).
  { intros y Hy. apply NNPP. intro Hno.
    assert (Hle : ∀ n, n ∈ N -> n ≤ y).
    { intros n Hn.
      destruct (Leq_P4 n y (N_Subset_R n Hn) Hy) as [Hnle | Hyle]; [exact Hnle |].
      destruct (classic (y = n)) as [Heq | Hne2].
      - rewrite Heq. apply Leq_P1. exact (N_Subset_R n Hn).
      - exfalso. apply Hno. exists n. split; [exact Hn | split; [exact Hyle | exact Hne2]]. }
    apply Arch_P2. exists y. unfold Upper. split; [exact N_Subset_R | split; [exact Hy | exact Hle]]. }
  assert (posZ_in_N : ∀ d, d ∈ Z -> 0 < d -> d ∈ N).
  { intros d HdZ H0d.
    assert (E0 : Ensemble 0) by (exists R; exact H0R).
    assert (HdR : d ∈ R) by (apply Z_Subset_R; exact HdZ).
    unfold Z in HdZ. apply MKT4 in HdZ as [HdN | HdRest].
    - exact HdN.
    - apply MKT4 in HdRest as [HdNegN | Hd0].
      + exfalso.
        apply AxiomII in HdNegN as [Ed Hneg].
        assert (HnegR : (-d) ∈ R) by (apply (Plus_neg1a d HdR)).
        assert (H1d : 1 ≤ (-d)) by (apply HminN; exact Hneg).
        assert (H0dle : 0 ≤ d) by (exact (proj1 H0d)).
        assert (Hle : 1 + 0 ≤ (-d) + d) by (apply (OrderPM_Co3 1 (-d) 0 d H1R HnegR H0R HdR H1d H0dle)).
        assert (Hle' : 1 ≤ 0).
        { rewrite (Plus_P1 1 H1R) in Hle.
          rewrite (eq_trans (Plus_P4 (-d) d HnegR HdR) (Plus_neg2 d HdR)) in Hle.
          exact Hle. }
        assert (H01 : 0 ≤ 1) by (exact (proj1 OrderPM_Co9)).
        assert (H10eq : 1 = 0) by (apply (Leq_P2 1 0 H1R H0R Hle' H01)).
        exact (proj2 OrderPM_Co9 (eq_sym H10eq)).
      + exfalso.
        assert (Hd0eq : d = 0) by (exact (proj1 (MKT41 0 E0 d) Hd0)).
        exact (proj2 H0d (eq_sym Hd0eq)). }
  assert (neg_add_cancel : ∀ a b, a ∈ R -> b ∈ R -> (-b) + (a + b) = a).
  { intros a b Ha Hb.
    assert (Hnegb : -b ∈ R) by (apply (Plus_neg1a b Hb)).
    transitivity ((-b + a) + b).
    - apply (Plus_P3 (-b) a b Hnegb Ha Hb).
    - transitivity ((a + (-b)) + b).
      + rewrite (Plus_P4 (-b) a Hnegb Ha). reflexivity.
      + transitivity (a + ((-b) + b)).
        * symmetry. apply (Plus_P3 a (-b) b Ha Hnegb Hb).
        * rewrite (eq_trans (Plus_P4 (-b) b Hnegb Hb) (Plus_neg2 b Hb)). apply (Plus_P1 a Ha). }
  assert (HnegccR : (-cc) ∈ R) by (apply (Plus_neg1a cc HccR)).
  destruct (ArchN (-cc) HnegccR) as [m0 [Hm0N Hlt]].
  assert (Hlb : ∀ x, x ∈ E -> (-m0) ≤ x).
  { intros x HxE. assert (Hccle : cc ≤ x) by (apply Hcclb; exact HxE).
    assert (Hnegm0R : (-m0) ∈ R) by (apply (Plus_neg1a m0 (N_Subset_R m0 Hm0N))).
    assert (Hpos : 0 < cc + m0).
    { assert (Ht := OrderPM_Co1 (-cc) m0 cc HnegccR (N_Subset_R m0 Hm0N) HccR Hlt).
      rewrite (eq_trans (Plus_P4 (-cc) cc HnegccR HccR) (Plus_neg2 cc HccR)) in Ht.
      rewrite <- (Plus_P4 cc m0 HccR (N_Subset_R m0 Hm0N)) in Ht.
      exact Ht. }
    assert (Hnegm0lt : (-m0) < cc).
    { assert (Ht := OrderPM_Co1 0 (cc + m0) (-m0) H0R (Plus_close cc m0 HccR (N_Subset_R m0 Hm0N)) (Plus_neg1a m0 (N_Subset_R m0 Hm0N)) Hpos).
      assert (H0eq : 0 + (-m0) = -m0) by (exact (eq_trans (Plus_P4 0 (-m0) H0R Hnegm0R) (Plus_P1 (-m0) Hnegm0R))).
      rewrite H0eq in Ht.
      assert (Hccm0eq : (cc + m0) + (-m0) = cc).
      { rewrite <- (Plus_P3 cc m0 (-m0) HccR (N_Subset_R m0 Hm0N) Hnegm0R).
        rewrite (Plus_neg2 m0 (N_Subset_R m0 Hm0N)). apply (Plus_P1 cc HccR). }
      rewrite Hccm0eq in Ht. exact Ht. }
    exact (Leq_P3 (-m0) cc x Hnegm0R HccR (HEsubR x HxE) (proj1 Hnegm0lt) Hccle). }
  destruct (classic ((-m0) ∈ E)) as [Hin | Hnotin].
  - exists (-m0). unfold Min. split; [exact HEsubR | split; [exact Hin | exact Hlb]].
  - set (D := \{ λ j, j ∈ N /\ ((-m0) + j) ∈ E \}).
    assert (HDsub : D ⊂ N)
      by (intros z Hz; apply AxiomII in Hz as [_ [HzN _]]; exact HzN).
    assert (HDne : D <> Φ).
    { destruct (MKT_nonempty E Hne) as [x0 Hx0E].
      assert (Hx0Z : x0 ∈ Z) by (apply HEZ; exact Hx0E).
      assert (Hx0R : x0 ∈ R) by (apply Z_Subset_R; exact Hx0Z).
      assert (Hx0lb : (-m0) ≤ x0) by (apply Hlb; exact Hx0E).
      assert (Hx0ne : (-m0) ≠ x0) by (intro Heq; apply Hnotin; rewrite Heq; exact Hx0E).
      assert (HjZ : (x0 + m0) ∈ Z) by (apply (Int_P1a x0 m0 Hx0Z (N_Subset_Z m0 Hm0N))).
      assert (Hjpos : 0 < (x0 + m0)).
      { assert (Ht : (-m0) + m0 < x0 + m0)
          by (apply (OrderPM_Co1 (-m0) x0 m0 (Plus_neg1a m0 (N_Subset_R m0 Hm0N)) Hx0R (N_Subset_R m0 Hm0N) (conj Hx0lb Hx0ne))).
        rewrite (eq_trans (Plus_P4 (-m0) m0 (Plus_neg1a m0 (N_Subset_R m0 Hm0N)) (N_Subset_R m0 Hm0N)) (Plus_neg2 m0 (N_Subset_R m0 Hm0N))) in Ht. exact Ht. }
      assert (HjN : (x0 + m0) ∈ N) by (apply posZ_in_N; [exact HjZ | exact Hjpos]).
      assert (Hjmem : ((-m0) + (x0 + m0)) ∈ E)
        by (rewrite (neg_add_cancel x0 m0 Hx0R (N_Subset_R m0 Hm0N)); exact Hx0E).
      assert (HjinD : (x0 + m0) ∈ D).
      { apply AxiomII; split. - exists N; exact HjN. - split; [exact HjN | exact Hjmem]. }
      intro H0. rewrite H0 in HjinD. exact (MKT16 HjinD). }
    destruct (Nat_P7 D HDsub HDne) as [j0 HminD].
    destruct HminD as [HDsubR [Hj0D Hminle]].
    apply AxiomII in Hj0D as [_ [Hj0N Hj0E]].
    exists ((-m0) + j0). unfold Min. split; [exact HEsubR | split; [exact Hj0E |]].
    intros x HxE.
    assert (HxZ : x ∈ Z) by (apply HEZ; exact HxE).
    assert (HxR : x ∈ R) by (apply Z_Subset_R; exact HxZ).
    assert (Hxlb : (-m0) ≤ x) by (apply Hlb; exact HxE).
    assert (Hxne : (-m0) ≠ x) by (intro Heq; apply Hnotin; rewrite Heq; exact HxE).
    assert (HjZ : (x + m0) ∈ Z) by (apply (Int_P1a x m0 HxZ (N_Subset_Z m0 Hm0N))).
    assert (Hjpos : 0 < (x + m0)).
    { assert (Ht : (-m0) + m0 < x + m0)
        by (apply (OrderPM_Co1 (-m0) x m0 (Plus_neg1a m0 (N_Subset_R m0 Hm0N)) HxR (N_Subset_R m0 Hm0N) (conj Hxlb Hxne))).
      rewrite (eq_trans (Plus_P4 (-m0) m0 (Plus_neg1a m0 (N_Subset_R m0 Hm0N)) (N_Subset_R m0 Hm0N)) (Plus_neg2 m0 (N_Subset_R m0 Hm0N))) in Ht. exact Ht. }
    assert (HjN : (x + m0) ∈ N) by (apply posZ_in_N; [exact HjZ | exact Hjpos]).
    assert (HjmemE : ((-m0) + (x + m0)) ∈ E)
      by (rewrite (neg_add_cancel x m0 HxR (N_Subset_R m0 Hm0N)); exact HxE).
    assert (HjinD : (x + m0) ∈ D).
    { apply AxiomII; split. - exists N; exact HjN. - split; [exact HjN | exact HjmemE]. }
    assert (Hj0lej : j0 ≤ (x + m0)) by (apply Hminle; exact HjinD).
    assert (Hj0R : j0 ∈ R) by (apply N_Subset_R; exact Hj0N).
    assert (Hfin : (-m0) + j0 ≤ x).
    { assert (Ht := Plus_Leq j0 (x + m0) (-m0) Hj0R (Plus_close x m0 HxR (N_Subset_R m0 Hm0N)) (Plus_neg1a m0 (N_Subset_R m0 Hm0N)) Hj0lej).
      rewrite (Plus_P4 j0 (-m0) Hj0R (Plus_neg1a m0 (N_Subset_R m0 Hm0N))) in Ht.
      rewrite (Plus_P4 (x+m0) (-m0) (Plus_close x m0 HxR (N_Subset_R m0 Hm0N)) (Plus_neg1a m0 (N_Subset_R m0 Hm0N))) in Ht.
      rewrite (neg_add_cancel x m0 HxR (N_Subset_R m0 Hm0N)) in Ht.
      exact Ht. }
    exact Hfin.
Qed.

Proposition Arch_P4 : ∀ E, E ⊂ N -> E <> Φ -> Bounded E -> ∃ n, Min E n.
Proof.
  intros E HE Hne _. exact (Nat_P7 E HE Hne).
Qed.

Proposition Arch_P5 : ~ (∃ n, Lower Z n) /\ ~ (∃ n, Upper Z n).
Proof.
  split.
  - intro Hex. destruct Hex as [n [HZsub [HnR Hle]]].
    apply Arch_P2. exists (-n). unfold Upper. split.
    + exact N_Subset_R.
    + split; [apply (Plus_neg1a n HnR) |].
      intros m Hm.
      assert (HmR : m ∈ R) by (apply N_Subset_R; exact Hm).
      assert (HnegmZ : (-m) ∈ Z) by (apply (proj1 (Int_P3 m (N_Subset_Z m Hm)))).
      assert (Hnm : n ≤ -m) by (apply Hle; exact HnegmZ).
      assert (HnegmR : (-m) ∈ R) by (apply (Plus_neg1a m HmR)).
      assert (HnegnR : (-n) ∈ R) by (apply (Plus_neg1a n HnR)).
      assert (Ht : n + m ≤ (-m) + m) by (apply (Plus_Leq n (-m) m HnR HnegmR HmR Hnm)).
      rewrite (eq_trans (Plus_P4 (-m) m HnegmR HmR) (Plus_neg2 m HmR)) in Ht.
      assert (Ht2 : (n + m) + (-n) ≤ 0 + (-n))
        by (apply (Plus_Leq (n+m) 0 (-n) (Plus_close n m HnR HmR) (zero_in_R) HnegnR Ht)).
      assert (Heq : (n + m) + (-n) = m).
      { transitivity (m + (n + (-n))).
        - rewrite (Plus_P4 n m HnR HmR). symmetry. apply (Plus_P3 m n (-n) HmR HnR (Plus_neg1a n HnR)).
        - rewrite (Plus_neg2 n HnR). apply (Plus_P1 m HmR). }
      rewrite Heq in Ht2.
      rewrite (eq_trans (Plus_P4 0 (-n) (zero_in_R) HnegnR) (Plus_P1 (-n) HnegnR)) in Ht2.
      exact Ht2.
  - intro Hex. destruct Hex as [n [HZsub [HnR Hle]]].
    apply Arch_P2. exists n. unfold Upper. split.
    + exact N_Subset_R.
    + split; [exact HnR |].
      intros m Hm. apply Hle. apply N_Subset_Z; exact Hm.
Qed.

Proposition Arch_P6 : ∀ h x, h ∈ R -> 0 < h -> x ∈ R
  -> (exists ! k, k ∈ Z /\ (k - 1) · h ≤ x /\ x < k · h).
Proof.
  intros h x HhR Hhpos HxR.
  assert (H0R : 0 ∈ R) by (apply zero_in_R).
  assert (H1R : 1 ∈ R) by (apply one_in_R_Co).
  assert (Hneg1R : (-(1)) ∈ R) by (apply (Plus_neg1a 1 H1R)).
  assert (E0 : Ensemble 0) by (exists R; exact H0R).
  assert (HhR0 : h ∈ (R ~ [0])).
  { unfold Setminus. apply AxiomII; split.
    - exists R; exact HhR.
    - split; [exact HhR | apply AxiomII; split; [exists R; exact HhR | intro Hin; exact (proj2 Hhpos (eq_sym (proj1 (MKT41 0 E0 h) Hin)))]]. }
  assert (HhinvR : (h⁻) ∈ R).
  { pose proof (Mult_inv1 h HhR0) as H. unfold Setminus in H. apply AxiomII in H as [_ [Hinv _]]. exact Hinv. }
  assert (ArchN : ∀ y, y ∈ R -> ∃ n, n ∈ N /\ y < n).
  { intros y Hy. apply NNPP. intro Hno.
    assert (Hle : ∀ n, n ∈ N -> n ≤ y).
    { intros n Hn.
      destruct (Leq_P4 n y (N_Subset_R n Hn) Hy) as [Hnle | Hyle]; [exact Hnle |].
      destruct (classic (y = n)) as [Heq | Hne2].
      - rewrite Heq. apply Leq_P1. exact (N_Subset_R n Hn).
      - exfalso. apply Hno. exists n. split; [exact Hn | split; [exact Hyle | exact Hne2]]. }
    apply Arch_P2. exists y. unfold Upper. split; [exact N_Subset_R | split; [exact Hy | exact Hle]]. }
  assert (dblneg : ∀ a, a ∈ R -> -(-a) = a).
  { intros a Ha.
    assert (Hnega : -a ∈ R) by (apply (Plus_neg1a a Ha)).
    assert (Hadd : (-a) + a = 0) by (exact (eq_trans (Plus_P4 (-a) a Hnega Ha) (Plus_neg2 a Ha))).
    assert (Hadd2 : (-a) + (-(-a)) = 0) by (apply (Plus_neg2 (-a) Hnega)).
    destruct (Plus_Co2 (-a) Hnega) as [z [[_ _] Huniq]].
    assert (He1 : z = a) by (exact (Huniq a (conj Ha Hadd))).
    assert (He2 : z = -(-a)) by (exact (Huniq (-(-a)) (conj (Plus_neg1a (-a) Hnega) Hadd2))).
    rewrite <- He2. exact He1. }
  assert (neg_lt : ∀ a b, a ∈ R -> b ∈ R -> a < b -> -b < -a).
  { intros a b Ha Hb Hlt.
    assert (Hnega : -a ∈ R) by (apply (Plus_neg1a a Ha)).
    assert (Hnegb : -b ∈ R) by (apply (Plus_neg1a b Hb)).
    assert (HcR : ((-a) + (-b)) ∈ R) by (apply (Plus_close (-a) (-b) Hnega Hnegb)).
    assert (Ht := OrderPM_Co1 a b ((-a) + (-b)) Ha Hb HcR Hlt).
    assert (HeqL : a + ((-a) + (-b)) = -b).
    { rewrite (Plus_P3 a (-a) (-b) Ha Hnega Hnegb).
      rewrite (Plus_neg2 a Ha).
      rewrite (eq_trans (Plus_P4 0 (-b) H0R Hnegb) (Plus_P1 (-b) Hnegb)). reflexivity. }
    assert (HeqR : b + ((-a) + (-b)) = -a).
    { rewrite (Plus_P4 (-a) (-b) Hnega Hnegb).
      rewrite (Plus_P3 b (-b) (-a) Hb Hnegb Hnega).
      rewrite (Plus_neg2 b Hb).
      rewrite (eq_trans (Plus_P4 0 (-a) H0R Hnega) (Plus_P1 (-a) Hnega)). reflexivity. }
    rewrite HeqL in Ht. rewrite HeqR in Ht. exact Ht. }
  assert (Hxheq : (x·(h⁻))·h = x).
  { transitivity (x·((h⁻)·h)).
    - symmetry. apply (Mult_P3 x (h⁻) h HxR HhinvR HhR).
    - rewrite (Mult_P4 (h⁻) h HhinvR HhR). rewrite (Mult_inv2 h HhR0). apply (Mult_P1 x HxR). }
  set (E := \{ λ k, k ∈ Z /\ x < k·h \}).
  assert (HEZ : E ⊂ Z).
  { intros z Hz. apply AxiomII in Hz as [_ [HzZ _]]. exact HzZ. }
  assert (HEne : E <> Φ).
  { assert (HyR : x·(h⁻) ∈ R) by (apply (Mult_close x (h⁻) HxR HhinvR)).
    destruct (ArchN (x·(h⁻)) HyR) as [n [HnN Hnlt]].
    assert (HnR : n ∈ R) by (apply N_Subset_R; exact HnN).
    assert (Hngt : x < n·h).
    { rewrite <- Hxheq. apply (OrderPM_Co7a (x·(h⁻)) n h HyR HnR HhR Hnlt Hhpos). }
    assert (Hnin : n ∈ E).
    { apply AxiomII; split.
      - exists R; exact HnR.
      - split; [exact (N_Subset_Z n HnN) | exact Hngt]. }
    intro H0. rewrite H0 in Hnin. exact (MKT16 Hnin). }
  assert (HElb : ∃ c, Lower E c).
  { assert (HyR : x·(h⁻) ∈ R) by (apply (Mult_close x (h⁻) HxR HhinvR)).
    assert (HnegR : -(x·(h⁻)) ∈ R) by (apply (Plus_neg1a (x·(h⁻)) HyR)).
    destruct (ArchN (-(x·(h⁻))) HnegR) as [n [HnN Hnlt]].
    assert (HnR : n ∈ R) by (apply N_Subset_R; exact HnN).
    assert (HnnR : -n ∈ R) by (apply (Plus_neg1a n HnR)).
    assert (Hlt2 : -n < x·(h⁻)).
    { assert (Ht := neg_lt (-(x·(h⁻))) n HnegR HnR Hnlt).
      rewrite (dblneg (x·(h⁻)) HyR) in Ht. exact Ht. }
    assert (Hlth : (-n)·h < x).
    { assert (Ht := OrderPM_Co7a (-n) (x·(h⁻)) h HnnR HyR HhR Hlt2 Hhpos).
      rewrite Hxheq in Ht. exact Ht. }
    exists (-n). unfold Lower. split.
    - intros z Hz. apply AxiomII in Hz as [_ [HzZ _]]. apply Z_Subset_R; exact HzZ.
    - split; [exact (Z_Subset_R (-n) (proj1 (Int_P3 n (N_Subset_Z n HnN)))) |].
      intros z Hz.
      apply AxiomII in Hz as [_ [HzZ Hzlt]].
      assert (HzR : z ∈ R) by (apply Z_Subset_R; exact HzZ).
      assert (H2 : (-n)·h < z·h)
        by (apply (Order_Co2 ((-n)·h) x (z·h) (Mult_close (-n) h HnnR HhR) HxR (Mult_close z h HzR HhR)); left; split; [exact Hlth | exact (proj1 Hzlt)]).
      destruct (Leq_P4 z (-n) HzR HnnR) as [Hzle | Hnle].
      + exfalso.
        assert (H3 : z·h ≤ (-n)·h) by (apply (OrderPM_Co7b z (-n) h HzR HnnR HhR Hzle (proj1 Hhpos))).
        assert (Heq2 : (-n)·h = z·h) by (apply (Leq_P2 ((-n)·h) (z·h) (Mult_close (-n) h HnnR HhR) (Mult_close z h HzR HhR) (proj1 H2) H3)).
        exact ((proj2 H2) Heq2).
      + exact Hnle. }
  destruct (Arch_P3b E HEZ HEne HElb) as [k0 Hmin0].
  destruct Hmin0 as [HEsubR [Hk0E Hminle]].
  apply AxiomII in Hk0E as [_ [Hk0Z Hk0gt]].
  assert (Hk0R : k0 ∈ R) by (apply Z_Subset_R; exact Hk0Z).
  assert (Hk0m1R : k0 + (-(1)) ∈ R) by (apply (Plus_close k0 (-(1)) Hk0R Hneg1R)).
  assert (Hk0m1Z : k0 + (-(1)) ∈ Z) by (apply (Int_P1a k0 (-(1)) Hk0Z (proj1 (Int_P3 1 (N_Subset_Z 1 one_in_N))))).
  assert (Hle_part : (k0 + (-(1)))·h ≤ x).
  { destruct (Leq_P4 x ((k0 + (-(1)))·h) HxR (Mult_close (k0 + (-(1))) h Hk0m1R HhR)) as [Hxl | Hlx].
    - destruct (classic (x = (k0 + (-(1)))·h)) as [Heq | Hne].
      + rewrite Heq. apply Leq_P1. exact (Mult_close (k0 + (-(1))) h Hk0m1R HhR).
      + exfalso.
        assert (Hlt : x < (k0 + (-(1)))·h) by (split; [exact Hxl | exact Hne]).
        assert (Hin : (k0 + (-(1))) ∈ E).
        { apply AxiomII; split.
          - exists R; exact Hk0m1R.
          - split; [exact Hk0m1Z | exact Hlt]. }
        assert (Hkle : k0 ≤ k0 + (-(1))) by (apply Hminle; exact Hin).
        assert (Hm1lt : k0 + (-(1)) < k0).
        { assert (Hneg1lt0 : (-(1)) < 0) by (apply (OrderPM_Co2a 1 H1R OrderPM_Co9)).
          assert (Ht := OrderPM_Co1 (-(1)) 0 k0 Hneg1R H0R Hk0R Hneg1lt0).
          rewrite (Plus_P4 (-(1)) k0 Hneg1R Hk0R) in Ht.
          rewrite (eq_trans (Plus_P4 0 k0 H0R Hk0R) (Plus_P1 k0 Hk0R)) in Ht.
          exact Ht. }
        assert (Hc : k0 < k0) by (apply (Order_Co2 k0 (k0 + (-(1))) k0 Hk0R Hk0m1R Hk0R); right; split; [exact Hkle | exact Hm1lt]).
        exact ((proj2 Hc) eq_refl).
    - exact Hlx. }
  assert (Huniq : ∀ k', k' ∈ Z /\ (k' + (-(1)))·h ≤ x /\ x < k'·h -> k' = k0).
  { intros k' [Hk'Z [Hk'le Hk'gt]].
    assert (Hk'R : k' ∈ R) by (apply Z_Subset_R; exact Hk'Z).
    destruct (Leq_P4 k0 k' Hk0R Hk'R) as [Hkk' | Hk'k].
    - destruct (classic (k0 = k')) as [Heq | Hne].
      + exact (eq_sym Heq).
      + exfalso.
        assert (Hlt : k0 < k') by (split; [exact Hkk' | exact Hne]).
        assert (Hsucc : k0 + 1 ≤ k') by (apply (Even_and_Odd_P2_Lemma k' k0 Hk'Z Hk0Z Hlt)).
        assert (HsuccR : (k0 + 1) ∈ R) by (apply (Plus_close k0 1 Hk0R H1R)).
        assert (Hk'le2 : k0 ≤ k' + (-(1))).
        { assert (Ht := Plus_Leq (k0+1) k' (-(1)) HsuccR Hk'R Hneg1R Hsucc).
          assert (Heq1 : (k0 + 1) + (-(1)) = k0).
          { transitivity (k0 + (1 + (-(1)))).
            - symmetry. apply (Plus_P3 k0 1 (-(1)) Hk0R H1R Hneg1R).
            - rewrite (Plus_neg2 1 H1R). apply (Plus_P1 k0 Hk0R). }
          rewrite Heq1 in Ht. exact Ht. }
        assert (Hk'm1R : k' + (-(1)) ∈ R) by (apply (Plus_close k' (-(1)) Hk'R Hneg1R)).
        assert (Hle1 : k0·h ≤ (k' + (-(1)))·h) by (apply (OrderPM_Co7b k0 (k' + (-(1))) h Hk0R Hk'm1R HhR Hk'le2 (proj1 Hhpos))).
        assert (Hle2 : k0·h ≤ x) by (apply (Leq_P3 (k0·h) ((k' + (-(1)))·h) x (Mult_close k0 h Hk0R HhR) (Mult_close (k' + (-(1))) h Hk'm1R HhR) HxR Hle1 Hk'le)).
        assert (Hc : k0·h < k0·h) by (apply (Order_Co2 (k0·h) x (k0·h) (Mult_close k0 h Hk0R HhR) HxR (Mult_close k0 h Hk0R HhR)); right; split; [exact Hle2 | exact Hk0gt]).
        exact ((proj2 Hc) eq_refl).
    - destruct (classic (k0 = k')) as [Heq | Hne].
      + exact (eq_sym Heq).
      + exfalso.
        assert (Hlt : k' < k0) by (split; [exact Hk'k | intro H; exact (Hne (eq_sym H))]).
        assert (Hsucc : k' + 1 ≤ k0) by (apply (Even_and_Odd_P2_Lemma k0 k' Hk0Z Hk'Z Hlt)).
        assert (HsuccR : (k' + 1) ∈ R) by (apply (Plus_close k' 1 Hk'R H1R)).
        assert (Hk0le2 : k' ≤ k0 + (-(1))).
        { assert (Ht := Plus_Leq (k'+1) k0 (-(1)) HsuccR Hk0R Hneg1R Hsucc).
          assert (Heq1 : (k' + 1) + (-(1)) = k').
          { transitivity (k' + (1 + (-(1)))).
            - symmetry. apply (Plus_P3 k' 1 (-(1)) Hk'R H1R Hneg1R).
            - rewrite (Plus_neg2 1 H1R). apply (Plus_P1 k' Hk'R). }
          rewrite Heq1 in Ht. exact Ht. }
        assert (Hk0m1R2 : k0 + (-(1)) ∈ R) by (apply (Plus_close k0 (-(1)) Hk0R Hneg1R)).
        assert (Hle1 : k'·h ≤ (k0 + (-(1)))·h) by (apply (OrderPM_Co7b k' (k0 + (-(1))) h Hk'R Hk0m1R2 HhR Hk0le2 (proj1 Hhpos))).
        assert (Hle2 : k'·h ≤ x) by (apply (Leq_P3 (k'·h) ((k0 + (-(1)))·h) x (Mult_close k' h Hk'R HhR) (Mult_close (k0 + (-(1))) h Hk0m1R2 HhR) HxR Hle1 Hle_part)).
        assert (Hc : k'·h < k'·h) by (apply (Order_Co2 (k'·h) x (k'·h) (Mult_close k' h Hk'R HhR) HxR (Mult_close k' h Hk'R HhR)); right; split; [exact Hle2 | exact Hk'gt]).
        exact ((proj2 Hc) eq_refl). }
  exists k0. split.
  - split; [exact Hk0Z | split; [exact Hle_part | exact Hk0gt]].
  - intros k' Hk'. symmetry. apply Huniq. exact Hk'.
Qed.

Proposition Arch_P7 : ∀ x, x ∈ R -> 0 < x 
  -> (∃ n, n ∈ N /\ 0 < 1 / n /\ 1 / n < x).
Proof.
  intros x HxR Hxpos.
  assert (H0R : 0 ∈ R) by (apply zero_in_R).
  assert (H1R : 1 ∈ R) by (apply one_in_R_Co).
  assert (E0 : Ensemble 0) by (exists R; exact H0R).
  assert (HxR0 : x ∈ (R ~ [0])).
  { unfold Setminus. apply AxiomII; split.
    - exists R; exact HxR.
    - split; [exact HxR | apply AxiomII; split; [exists R; exact HxR | intro Hin; exact (proj2 Hxpos (eq_sym (proj1 (MKT41 0 E0 x) Hin)))]]. }
  assert (HxinvR : (x⁻) ∈ R).
  { pose proof (Mult_inv1 x HxR0) as H. unfold Setminus in H. apply AxiomII in H as [_ [Hinv _]]. exact Hinv. }
  assert (ArchN : ∀ y, y ∈ R -> ∃ n, n ∈ N /\ y < n).
  { intros y Hy. apply NNPP. intro Hno.
    assert (Hle : ∀ n, n ∈ N -> n ≤ y).
    { intros n Hn.
      destruct (Leq_P4 n y (N_Subset_R n Hn) Hy) as [Hnle | Hyle]; [exact Hnle |].
      destruct (classic (y = n)) as [Heq | Hne2].
      - rewrite Heq. apply Leq_P1. exact (N_Subset_R n Hn).
      - exfalso. apply Hno. exists n. split; [exact Hn | split; [exact Hyle | exact Hne2]]. }
    apply Arch_P2. exists y. unfold Upper. split; [exact N_Subset_R | split; [exact Hy | exact Hle]]. }
  destruct (ArchN (x⁻) HxinvR) as [n [HnN Hnlt]].
  exists n. split; [exact HnN |].
  assert (HnR : n ∈ R) by (apply N_Subset_R; exact HnN).
  assert (Hnge1 : 1 ≤ n) by (pose proof one_is_min_in_N as H; unfold Min in H; exact (proj2 (proj2 H) n HnN)).
  assert (Hnpos : 0 < n) by (apply (Order_Co2 0 1 n H0R H1R HnR); left; split; [exact OrderPM_Co9 | exact Hnge1]).
  assert (HnR0 : n ∈ (R ~ [0])).
  { unfold Setminus. apply AxiomII; split.
    - exists R; exact HnR.
    - split; [exact HnR | apply AxiomII; split; [exists R; exact HnR | intro Hin; exact (proj2 Hnpos (eq_sym (proj1 (MKT41 0 E0 n) Hin)))]]. }
  assert (HninvR : (n⁻) ∈ R).
  { pose proof (Mult_inv1 n HnR0) as H. unfold Setminus in H. apply AxiomII in H as [_ [Hinv _]]. exact Hinv. }
  assert (Hninvpos : 0 < (n⁻)) by (apply (OrderPM_Co10 n HnR Hnpos)).
  assert (H1lt : 1 < x·n).
  { assert (HxnR : x·n ∈ R) by (apply (Mult_close x n HxR HnR)).
    assert (Ht := OrderPM_Co7a (x⁻) n x HxinvR HnR HxR Hnlt Hxpos).
    rewrite (Mult_P4 n x HnR HxR) in Ht.
    rewrite (eq_trans (Mult_P4 (x⁻) x HxinvR HxR) (Mult_inv2 x HxR0)) in Ht.
    exact Ht. }
  assert (Hninvlt : (n⁻) < x).
  { assert (HxnR : x·n ∈ R) by (apply (Mult_close x n HxR HnR)).
    assert (Ht := OrderPM_Co7a 1 (x·n) (n⁻) H1R HxnR HninvR H1lt Hninvpos).
    rewrite (eq_trans (Mult_P4 1 (n⁻) H1R HninvR) (Mult_P1 (n⁻) HninvR)) in Ht.
    rewrite <- (Mult_P3 x n (n⁻) HxR HnR HninvR) in Ht.
    rewrite (Mult_inv2 n HnR0) in Ht.
    rewrite (Mult_P1 x HxR) in Ht.
    exact Ht. }
  split.
  - change (0 < 1·(n⁻)). rewrite (eq_trans (Mult_P4 1 (n⁻) H1R HninvR) (Mult_P1 (n⁻) HninvR)). exact Hninvpos.
  - change (1·(n⁻) < x). rewrite (eq_trans (Mult_P4 1 (n⁻) H1R HninvR) (Mult_P1 (n⁻) HninvR)). exact Hninvlt.
Qed.

Proposition Arch_P8 : ∀ x, x ∈ R -> 0 ≤ x -> (∀ n, n ∈ N -> x < 1 / n)
  -> x = 0.
Proof.
  intros x HxR Hxge0 Hhyp.
  destruct (classic (x = 0)) as [Heq | Hne].
  - exact Heq.
  - exfalso.
    assert (Hxpos : 0 < x) by (split; [exact Hxge0 | intro H; exact (Hne (eq_sym H))]).
    destruct (Arch_P7 x HxR Hxpos) as [n [HnN [H1npos H1nlt]]].
    assert (H0R : 0 ∈ R) by (apply zero_in_R).
    assert (H1R : 1 ∈ R) by (apply one_in_R_Co).
    assert (E0 : Ensemble 0) by (exists R; exact H0R).
    assert (HnR : n ∈ R) by (apply N_Subset_R; exact HnN).
    assert (Hnge1 : 1 ≤ n) by (pose proof one_is_min_in_N as H; unfold Min in H; exact (proj2 (proj2 H) n HnN)).
    assert (Hnpos : 0 < n) by (apply (Order_Co2 0 1 n H0R H1R HnR); left; split; [exact OrderPM_Co9 | exact Hnge1]).
    assert (HnR0 : n ∈ (R ~ [0])).
    { unfold Setminus. apply AxiomII; split.
      - exists R; exact HnR.
      - split; [exact HnR | apply AxiomII; split; [exists R; exact HnR | intro Hin; exact (proj2 Hnpos (eq_sym (proj1 (MKT41 0 E0 n) Hin)))]]. }
    assert (HninvR : (n⁻) ∈ R).
    { pose proof (Mult_inv1 n HnR0) as H. unfold Setminus in H. apply AxiomII in H as [_ [Hinv _]]. exact Hinv. }
    assert (HinvR : (1/n) ∈ R).
    { change (1·(n⁻) ∈ R). apply (Mult_close 1 (n⁻) H1R HninvR). }
    assert (Hcontra : x < x)
      by (apply (Order_Co2 x (1/n) x HxR HinvR HxR); left; split; [exact (Hhyp n HnN) | exact (proj1 H1nlt)]).
    exact ((proj2 Hcontra) eq_refl).
Qed.

Proposition Arch_P9 : ∀ a b, a ∈ R -> b ∈ R -> a < b
  -> (∃ r, r ∈ Q /\ a < r /\ r < b).
Proof.
  intros a b HaR HbR Hab.
  assert (H0R : 0 ∈ R) by (apply zero_in_R).
  assert (H1R : 1 ∈ R) by (apply one_in_R_Co).
  assert (E0 : Ensemble 0) by (exists R; exact H0R).
  assert (HnegaR : (-a) ∈ R) by (apply (Plus_neg1a a HaR)).
  assert (Hba_pos : 0 < b + (-a)).
  { assert (Hlt : a + (-a) < b + (-a)) by (apply (OrderPM_Co1 a b (-a) HaR HbR HnegaR Hab)).
    rewrite (Plus_neg2 a HaR) in Hlt. exact Hlt. }
  destruct (Arch_P7 (b + (-a)) (Plus_close b (-a) HbR HnegaR) Hba_pos) as [n [HnN [H1npos H1nlt]]].
  assert (HnR : n ∈ R) by (apply N_Subset_R; exact HnN).
  assert (Hnge1 : 1 ≤ n) by (pose proof one_is_min_in_N as H; unfold Min in H; exact (proj2 (proj2 H) n HnN)).
  assert (Hnpos : 0 < n) by (apply (Order_Co2 0 1 n H0R H1R HnR); left; split; [exact OrderPM_Co9 | exact Hnge1]).
  assert (HnZ : n ∈ Z) by (apply N_Subset_Z; exact HnN).
  assert (HnR0 : n ∈ (R ~ [0])).
  { unfold Setminus. apply AxiomII; split.
    - exists R; exact HnR.
    - split; [exact HnR | apply AxiomII; split; [exists R; exact HnR | intro Hin; exact (proj2 Hnpos (eq_sym (proj1 (MKT41 0 E0 n) Hin)))]]. }
  assert (HnZ0 : n ∈ (Z ~ [0])).
  { unfold Setminus. apply AxiomII; split.
    - exists R; exact HnR.
    - split; [exact HnZ | apply AxiomII; split; [exists R; exact HnR | intro Hin; exact (proj2 Hnpos (eq_sym (proj1 (MKT41 0 E0 n) Hin)))]]. }
  assert (HninvR : (n⁻) ∈ R).
  { pose proof (Mult_inv1 n HnR0) as H. unfold Setminus in H. apply AxiomII in H as [_ [Hinv _]]. exact Hinv. }
  assert (H1n_eq : 1/n = n⁻).
  { change (1·(n⁻) = n⁻). rewrite (eq_trans (Mult_P4 1 (n⁻) H1R HninvR) (Mult_P1 (n⁻) HninvR)). reflexivity. }
  assert (Hninvpos : 0 < (n⁻)) by (rewrite <- H1n_eq; exact H1npos).
  assert (Hninvlt : (n⁻) < b + (-a)) by (rewrite <- H1n_eq; exact H1nlt).
  destruct (Arch_P6 (n⁻) a HninvR Hninvpos HaR) as [k [[HkZ [Hk_le Hk_gt]] Huniq]].
  assert (HkR : k ∈ R) by (apply Z_Subset_R; exact HkZ).
  exists (k·(n⁻)). split.
  - apply AxiomII; split.
    + exists R; apply (Mult_close k (n⁻) HkR HninvR).
    + exists k, n. split.
      * exact HkZ.
      * split.
        -- exact HnZ0.
        -- reflexivity.
  - split.
    + exact Hk_gt.
    + assert (HrR : k·(n⁻) ∈ R) by (apply (Mult_close k (n⁻) HkR HninvR)).
      assert (Hk'm1R : (k + (-(1))) ∈ R) by (apply (Plus_close k (-(1)) HkR (Plus_neg1a 1 H1R))).
      assert (Hm1nR : (k + (-(1)))·(n⁻) ∈ R) by (apply (Mult_close (k + (-(1))) (n⁻) Hk'm1R HninvR)).
      assert (Heq : (k + (-(1)))·(n⁻) + (n⁻) = k·(n⁻)).
      { transitivity (((k + (-(1))) + 1)·(n⁻)).
        - symmetry.
          transitivity ((k + (-(1)))·(n⁻) + 1·(n⁻)).
          + apply (Mult_P5 (k + (-(1))) 1 (n⁻) (Plus_close k (-(1)) HkR (Plus_neg1a 1 H1R)) H1R HninvR).
          + rewrite (eq_trans (Mult_P4 1 (n⁻) H1R HninvR) (Mult_P1 (n⁻) HninvR)). reflexivity.
        - assert (Hk_simpl : (k + (-(1))) + 1 = k).
          { transitivity (k + ((-(1)) + 1)).
            - symmetry. apply (Plus_P3 k (-(1)) 1 HkR (Plus_neg1a 1 H1R) H1R).
            - rewrite (eq_trans (Plus_P4 (-(1)) 1 (Plus_neg1a 1 H1R) H1R) (Plus_neg2 1 H1R)). apply (Plus_P1 k HkR). }
          rewrite Hk_simpl. reflexivity. }
      assert (Hr_le : k·(n⁻) ≤ a + (n⁻)).
      { assert (Ht := Plus_Leq ((k + (-(1)))·(n⁻)) a (n⁻) Hm1nR HaR HninvR Hk_le).
        rewrite Heq in Ht. exact Ht. }
      assert (Hab_eq : a + (b + (-a)) = b).
      { rewrite (Plus_P4 b (-a) HbR HnegaR).
        rewrite (Plus_P3 a (-a) b HaR HnegaR HbR).
        rewrite (Plus_neg2 a HaR).
        rewrite (eq_trans (Plus_P4 0 b H0R HbR) (Plus_P1 b HbR)). reflexivity. }
      assert (Ha_add : a + (n⁻) < b).
      { assert (Ht := OrderPM_Co1 (n⁻) (b + (-a)) a HninvR (Plus_close b (-a) HbR HnegaR) HaR Hninvlt).
        rewrite (Plus_P4 (n⁻) a HninvR HaR) in Ht.
        rewrite (Plus_P4 (b + (-a)) a (Plus_close b (-a) HbR HnegaR) HaR) in Ht.
        rewrite Hab_eq in Ht. exact Ht. }
      apply (Order_Co2 (k·(n⁻)) (a + (n⁻)) b HrR (Plus_close a (n⁻) HaR HninvR) HbR).
      right. split; [exact Hr_le | exact Ha_add].
Qed.

Proposition Arch_P10 : ∀ x, x ∈ R
  -> (exists ! k, k ∈ Z /\ k ≤ x /\ x < k + 1).
Proof.
  intros x HxR.
  assert (H0R : 0 ∈ R) by (apply zero_in_R).
  assert (H1R : 1 ∈ R) by (apply one_in_R_Co).
  assert (Hneg1R : (-(1)) ∈ R) by (apply (Plus_neg1a 1 H1R)).
  assert (H1Z : 1 ∈ Z) by (apply N_Subset_Z; apply one_in_N).
  assert (Hneg1Z : (-(1)) ∈ Z) by (apply (proj1 (Int_P3 1 H1Z))).
  assert (H1pos : 0 < 1) by (apply OrderPM_Co9).
  destruct (Arch_P6 1 x H1R H1pos HxR) as [k [[HkZ [Hk_le Hk_gt]] Huniq6]].
  assert (HkR : k ∈ R) by (apply Z_Subset_R; exact HkZ).
  assert (Hk0R : k + (-(1)) ∈ R) by (apply (Plus_close k (-(1)) HkR Hneg1R)).
  assert (Hk0Z : k + (-(1)) ∈ Z) by (apply (Int_P1a k (-(1)) HkZ Hneg1Z)).
  assert (Hk0_le : k + (-(1)) ≤ x).
  { rewrite <- (Mult_P1 (k + (-(1))) Hk0R). exact Hk_le. }
  assert (Hk0_gt : x < (k + (-(1))) + 1).
  { assert (Heq : (k + (-(1))) + 1 = k).
    { transitivity (k + ((-(1)) + 1)).
      - symmetry. apply (Plus_P3 k (-(1)) 1 HkR Hneg1R H1R).
      - rewrite (eq_trans (Plus_P4 (-(1)) 1 Hneg1R H1R) (Plus_neg2 1 H1R)). apply (Plus_P1 k HkR). }
    rewrite Heq. rewrite (Mult_P1 k HkR) in Hk_gt. exact Hk_gt. }
  exists (k + (-(1))). split.
  - split; [exact Hk0Z | split; [exact Hk0_le | exact Hk0_gt]].
  - intros k' [Hk'Z [Hk'_le Hk'_gt]].
    assert (Hk'R : k' ∈ R) by (apply Z_Subset_R; exact Hk'Z).
    assert (Hk'1R : k' + 1 ∈ R) by (apply (Plus_close k' 1 Hk'R H1R)).
    assert (Hk'1Z : k' + 1 ∈ Z) by (apply (Int_P1a k' 1 Hk'Z H1Z)).
    assert (Hsimp : (k' + 1) + (-(1)) = k').
    { transitivity (k' + (1 + (-(1)))).
      - symmetry. apply (Plus_P3 k' 1 (-(1)) Hk'R H1R Hneg1R).
      - rewrite (Plus_neg2 1 H1R). apply (Plus_P1 k' Hk'R). }
    assert (Hk'1_le : ((k' + 1) + (-(1)))·1 ≤ x).
    { rewrite Hsimp. rewrite (Mult_P1 k' Hk'R). exact Hk'_le. }
    assert (Hk'1_gt : x < (k' + 1)·1).
    { rewrite (Mult_P1 (k' + 1) Hk'1R). exact Hk'_gt. }
    assert (Heq1 : k' + 1 = k) by (symmetry; apply Huniq6; split; [exact Hk'1Z | split; [exact Hk'1_le | exact Hk'1_gt]]).
    assert (Hfin : k' = (k' + 1) + (-(1))).
    { symmetry. exact Hsimp. }
    rewrite Hfin. rewrite Heq1. reflexivity.
Qed.

(* 实数的几何解释 *)
(* 有界区间 *)
(* 开区间 *)
Notation "］ a , b ［" := (\{ λ x, x ∈ R /\ a < x /\ x < b \})
  (at level 5, a at level 0, b at level 0).

(* 闭区间 *)
Notation "［ a , b ］" := (\{ λ x, x ∈ R /\ a ≤ x /\ x ≤ b \})
  (at level 5, a at level 0, b at level 0).

(* 左开右闭 *)
Notation "］ a , b ］" := (\{ λ x, x ∈ R /\ a < x /\ x ≤ b \})
  (at level 5, a at level 0, b at level 0).

(* 左闭右开 *)
Notation "［ a , b ［" := (\{ λ x, x ∈ R /\ a ≤ x /\ x < b \})
  (at level 5, a at level 0, b at level 0).

(* 无界区间 *)
Notation "］ a , +∞［" := (\{ λ x, x ∈ R /\ a < x \})
  (at level 5, a at level 0).

Notation "［ a , +∞［" := (\{ λ x, x ∈ R /\ a ≤ x \}) 
  (at level 5, a at level 0).

Notation "］-∞ , b ］" := (\{ λ x, x ∈ R /\ x ≤ b \}) 
  (at level 5, b at level 0).

Notation "］-∞ , b ［" := (\{ λ x, x ∈ R /\ x < b \}) 
  (at level 5, b at level 0).

Notation "]-∞ , +∞[" := (R)(at level 0).

(* 邻域 *)
Definition Neighbourhood x δ := x ∈ R /\ δ ∈ R /\ x ∈ ］(x - δ),(x + δ)［.

(* 绝对值函数 *)
Definition Abs := \{\ λ u v, u ∈ R 
  /\ ((0 ≤ u /\ v = u) \/ (u < 0 /\ v = (-u))) \}\.

Corollary Abs_is_Function : Function Abs /\ dom(Abs) = R
  /\ ran(Abs) = \{ λ x, x ∈ R /\ 0 ≤ x \}.
Proof.
  assert (H0R : 0 ∈ R) by (apply zero_in_R).
  assert (Hchar : ∀ x y, [x,y] ∈ Abs ->
    x ∈ R /\ ((0 ≤ x /\ y = x) \/ (x < 0 /\ y = -x))).
  { intros x y Hxy.
    apply AxiomII in Hxy as [Exy Hxy'].
    destruct Hxy' as [u [v [Hxyuv [HuR Hc]]]].
    destruct (MKT49b x y Exy) as [Ex Ey].
    destruct (proj1 (MKT55 x y u v Ex Ey) Hxyuv) as [Hxu Hyv].
    subst u. subst v.
    split; [exact HuR | exact Hc]. }
  assert (Hin : ∀ x y, x ∈ R ->
    ((0 ≤ x /\ y = x) \/ (x < 0 /\ y = -x)) -> [x,y] ∈ Abs).
  { intros x y HxR Hc.
    assert (Ex : Ensemble x) by (unfold Ensemble; exists R; exact HxR).
    destruct Hc as [[H0x Hyx] | [Hx0 Hyx]].
    - subst y.
      apply AxiomII; split.
      + apply MKT49a; assumption.
      + exists x; exists x; split;
        [reflexivity | split; [exact HxR | left; split; [exact H0x | reflexivity]]].
    - subst y.
      assert (HnxR : -x ∈ R) by (apply (Plus_neg1a x HxR)).
      assert (Enx : Ensemble (-x)) by (unfold Ensemble; exists R; exact HnxR).
      apply AxiomII; split.
      + apply MKT49a; assumption.
      + exists x; exists (-x); split;
        [reflexivity | split; [exact HxR | right; split; [exact Hx0 | reflexivity]]]. }
  assert (Hsingle : ∀ x y z, [x,y] ∈ Abs -> [x,z] ∈ Abs -> y = z).
  { intros x y z Hxy Hxz.
    destruct (Hchar x y Hxy) as [HxR Hyc].
    destruct (Hchar x z Hxz) as [_ Hzc].
    destruct Hyc as [[H0x Hyx] | [Hx0 Hyx]];
    destruct Hzc as [[H0x' Hzx] | [Hx0' Hzx]].
    - rewrite Hyx. rewrite Hzx. reflexivity.
    - exfalso. apply (proj2 Hx0').
      exact (Leq_P2 x 0 HxR H0R (proj1 Hx0') H0x).
    - exfalso. apply (proj2 Hx0).
      exact (Leq_P2 x 0 HxR H0R (proj1 Hx0) H0x').
    - rewrite Hyx. rewrite Hzx. reflexivity. }
  assert (Hrel : Relation Abs).
  { intros z Hz. apply AxiomII in Hz as [Ez Hz'].
    destruct Hz' as [u [v [Hzuv _]]].
    exists u; exists v; exact Hzuv. }
  assert (Hfunc : Function Abs) by (split; [exact Hrel | exact Hsingle]).
  assert (Hdom : dom(Abs) = R).
  { apply AxiomI; intros x; split.
    - intros Hx. apply AxiomII in Hx as [Ex Hx'].
      destruct Hx' as [y Hxy].
      destruct (Hchar x y Hxy) as [HxR _]. exact HxR.
    - intros HxR.
      assert (Ex : Ensemble x) by (unfold Ensemble; exists R; exact HxR).
      apply AxiomII; split; [exact Ex |].
      destruct (classic (0 ≤ x)) as [H0x | Hn0x].
      + exists x. apply (Hin x x HxR). left. split; [exact H0x | reflexivity].
      + assert (Hxle : x ≤ 0)
          by (destruct (Leq_P4 0 x H0R HxR) as [H | H];
              [exfalso; exact (Hn0x H) | exact H]).
        assert (Hxne : x ≠ 0)
          by (intro Heq; apply Hn0x; rewrite Heq; apply Leq_P1; exact H0R).
        assert (Hxlt : x < 0) by (split; [exact Hxle | exact Hxne]).
        exists (-x). apply (Hin x (-x) HxR). right. split; [exact Hxlt | reflexivity]. }
  assert (Hran : ran(Abs) = \{ λ x, x ∈ R /\ 0 ≤ x \}).
  { apply AxiomI; intros y; split.
    - intros Hy. apply AxiomII in Hy as [Ey Hy'].
      destruct Hy' as [x Hxy].
      destruct (Hchar x y Hxy) as [HxR Hc].
      destruct Hc as [[H0x Hyx] | [Hx0 Hyx]].
      + subst y.
        apply AxiomII; split; [exact Ey | split; [exact HxR | exact H0x]].
      + subst y.
        assert (HnxR : -x ∈ R) by (apply (Plus_neg1a x HxR)).
        apply AxiomII; split; [exact Ey | split; [exact HnxR |]].
        assert (Ht : x + (-x) ≤ 0 + (-x))
          by (apply (Plus_Leq x 0 (-x) HxR H0R HnxR (proj1 Hx0))).
        rewrite (Plus_neg2 x HxR) in Ht.
        assert (H0nx : 0 + (-x) = -x)
          by (exact (eq_trans (Plus_P4 0 (-x) H0R HnxR) (Plus_P1 (-x) HnxR))).
        rewrite H0nx in Ht. exact Ht.
    - intros Hy. apply AxiomII in Hy as [Ey [HyR H0y]].
      assert (Ein : [y,y] ∈ Abs)
        by (apply (Hin y y HyR); left; split; [exact H0y | reflexivity]).
      apply AxiomII; split; [exact Ey | exists y; exact Ein]. }
  split; [exact Hfunc | split; [exact Hdom | exact Hran]].
Qed.

Corollary Abs_in_R : ∀ x, x ∈ R -> Abs[x] ∈ R.
Proof.
  intros x HxR.
  assert (Hfunc : Function Abs) by (exact (proj1 Abs_is_Function)).
  assert (H0R : 0 ∈ R) by (apply zero_in_R).
  destruct (classic (0 ≤ x)) as [H0x | Hn0x].
  - assert (Ex : Ensemble x) by (unfold Ensemble; exists R; exact HxR).
    assert (Hin : [x,x] ∈ Abs).
    { apply AxiomII; split.
      - apply MKT49a; assumption.
      - exists x; exists x; split;
        [reflexivity | split; [exact HxR | left; split; [exact H0x | reflexivity]]]. }
    assert (Hval : Abs[x] = x) by (exact (MKT_fval Abs x x Hfunc Hin)).
    rewrite Hval. exact HxR.
  - assert (Hxle : x ≤ 0)
      by (destruct (Leq_P4 0 x H0R HxR) as [H | H]; [exfalso; exact (Hn0x H) | exact H]).
    assert (Hxne : x ≠ 0)
      by (intro Heq; apply Hn0x; rewrite Heq; apply Leq_P1; exact H0R).
    assert (Hxlt : x < 0) by (split; [exact Hxle | exact Hxne]).
    assert (HnxR : -x ∈ R) by (apply (Plus_neg1a x HxR)).
    assert (Ex : Ensemble x) by (unfold Ensemble; exists R; exact HxR).
    assert (Enx : Ensemble (-x)) by (unfold Ensemble; exists R; exact HnxR).
    assert (Hin : [x,-x] ∈ Abs).
    { apply AxiomII; split.
      - apply MKT49a; assumption.
      - exists x; exists (-x); split;
        [reflexivity | split; [exact HxR | right; split; [exact Hxlt | reflexivity]]]. }
    assert (Hval : Abs[x] = -x) by (exact (MKT_fval Abs x (-x) Hfunc Hin)).
    rewrite Hval. exact HnxR.
Qed.

Notation "｜ x ｜" := (Abs[x])(at level 5, x at level 0).

Definition Distance x y := ｜(x - y)｜.

(* 绝对值的性质 *)
Proposition me_zero_Abs : ∀ x, x ∈ R -> 0 ≤ x -> ｜x｜ = x.
Proof.
  intros x HxR H0x.
  assert (Hfunc : Function Abs) by (exact (proj1 Abs_is_Function)).
  assert (Ex : Ensemble x) by (unfold Ensemble; exists R; exact HxR).
  assert (Hin : [x,x] ∈ Abs).
  { apply AxiomII; split.
    - apply MKT49a; assumption.
    - exists x; exists x; split;
      [reflexivity | split; [exact HxR | left; split; [exact H0x | reflexivity]]]. }
  exact (MKT_fval Abs x x Hfunc Hin).
Qed.

Proposition le_zero_Abs : ∀ x, x ∈ R -> x ≤ 0 -> ｜x｜ = -x.
Proof.
  intros x HxR Hxle.
  assert (Hfunc : Function Abs) by (exact (proj1 Abs_is_Function)).
  assert (H0R : 0 ∈ R) by (apply zero_in_R).
  destruct (classic (x = 0)) as [Hx0 | Hxne].
  - subst x.
    assert (neg0 : -0 = 0).
    { assert (Hne0 : -0 ∈ R) by (apply (Plus_neg1a 0 H0R)).
      transitivity (0 + (-0)).
      - symmetry. exact (eq_trans (Plus_P4 0 (-0) H0R Hne0) (Plus_P1 (-0) Hne0)).
      - exact (Minus_P2 0 H0R). }
    assert (E0 : Ensemble 0) by (unfold Ensemble; exists R; exact H0R).
    assert (Hin : [0,0] ∈ Abs).
    { apply AxiomII; split.
      - apply MKT49a; assumption.
      - exists 0; exists 0; split;
        [reflexivity | split; [exact H0R | left; split; [apply Leq_P1; exact H0R | reflexivity]]]. }
    assert (Hval : Abs[0] = 0) by (exact (MKT_fval Abs 0 0 Hfunc Hin)).
    rewrite Hval. exact (eq_sym neg0).
  - assert (Hxlt : x < 0) by (split; [exact Hxle | exact Hxne]).
    assert (HnxR : -x ∈ R) by (apply (Plus_neg1a x HxR)).
    assert (Ex : Ensemble x) by (unfold Ensemble; exists R; exact HxR).
    assert (Enx : Ensemble (-x)) by (unfold Ensemble; exists R; exact HnxR).
    assert (Hin : [x,-x] ∈ Abs).
    { apply AxiomII; split.
      - apply MKT49a; assumption.
      - exists x; exists (-x); split;
        [reflexivity | split; [exact HxR | right; split; [exact Hxlt | reflexivity]]]. }
    exact (MKT_fval Abs x (-x) Hfunc Hin).
Qed.

Proposition Abs_P1 : ∀ x, x ∈ R -> 0 ≤ ｜x｜ /\ (｜x｜ = 0 <-> x = 0).
Proof.
  intros x Hx.
  assert (H0R : 0 ∈ R) by (apply zero_in_R).
  assert (HabsR : ｜x｜ ∈ R) by (apply (Abs_in_R x Hx)).
  assert (dblneg : ∀ a, a ∈ R -> -(-a) = a).
  { intros a Ha.
    assert (Hnega : -a ∈ R) by (apply (Plus_neg1a a Ha)).
    assert (H1 : (-a) + a = 0) by (exact (eq_trans (Plus_P4 (-a) a Hnega Ha) (Plus_neg2 a Ha))).
    assert (H2 : (-a) + (-(-a)) = 0) by (apply (Plus_neg2 (-a) Hnega)).
    destruct (Plus_Co2 (-a) Hnega) as [z [[_ _] Huniq]].
    assert (He1 : z = a) by (exact (Huniq a (conj Ha H1))).
    assert (He2 : z = -(-a)) by (exact (Huniq (-(-a)) (conj (Plus_neg1a (-a) Hnega) H2))).
    rewrite <- He2. exact He1. }
  split.
  - destruct (Leq_P4 0 x H0R Hx) as [H0x | Hxle].
    + rewrite (me_zero_Abs x Hx H0x). exact H0x.
    + rewrite (le_zero_Abs x Hx Hxle).
      assert (HnxR : -x ∈ R) by (apply (Plus_neg1a x Hx)).
      assert (Ht : x + (-x) ≤ 0 + (-x)) by (apply (Plus_Leq x 0 (-x) Hx H0R HnxR Hxle)).
      rewrite (Plus_neg2 x Hx) in Ht.
      rewrite (eq_trans (Plus_P4 0 (-x) H0R HnxR) (Plus_P1 (-x) HnxR)) in Ht.
      exact Ht.
  - split.
    + intros Habs0.
      destruct (Leq_P4 0 x H0R Hx) as [H0x | Hxle].
      * rewrite (me_zero_Abs x Hx H0x) in Habs0. exact Habs0.
      * rewrite (le_zero_Abs x Hx Hxle) in Habs0.
        transitivity (x + 0).
        { symmetry. apply (Plus_P1 x Hx). }
        transitivity (x + (-x)).
        { rewrite Habs0. reflexivity. }
        exact (Plus_neg2 x Hx).
    + intros Hx0. subst x.
      change (｜0｜ = 0).
      apply (me_zero_Abs 0 H0R). apply (Leq_P1 0 H0R).
Qed.

Proposition Abs_P2 : ∀ x, x ∈ R -> ｜x｜ = ｜(-x)｜ /\ -｜x｜ ≤ x /\ x ≤ ｜x｜.
Proof.
  intros x Hx.
  assert (H0R : 0 ∈ R) by (apply zero_in_R).
  assert (HnxR : -x ∈ R) by (apply (Plus_neg1a x Hx)).
  assert (HabsR : ｜x｜ ∈ R) by (apply (Abs_in_R x Hx)).
  assert (Hdblneg : ∀ a, a ∈ R -> -(-a) = a).
  { intros a Ha.
    assert (Hnega : -a ∈ R) by (apply (Plus_neg1a a Ha)).
    assert (H1 : (-a) + a = 0) by (exact (eq_trans (Plus_P4 (-a) a Hnega Ha) (Plus_neg2 a Ha))).
    assert (H2 : (-a) + (-(-a)) = 0) by (apply (Plus_neg2 (-a) Hnega)).
    destruct (Plus_Co2 (-a) Hnega) as [z [[_ _] Huniq]].
    assert (He1 : z = a) by (exact (Huniq a (conj Ha H1))).
    assert (He2 : z = -(-a)) by (exact (Huniq (-(-a)) (conj (Plus_neg1a (-a) Hnega) H2))).
    rewrite <- He2. exact He1. }
  assert (nn_neg : ∀ y, y ∈ R -> y ≤ 0 -> 0 ≤ -y).
  { intros y Hy Hy0.
    assert (HnyR : -y ∈ R) by (apply (Plus_neg1a y Hy)).
    assert (Ht : y + (-y) ≤ 0 + (-y)) by (apply (Plus_Leq y 0 (-y) Hy H0R HnyR Hy0)).
    rewrite (Plus_neg2 y Hy) in Ht.
    rewrite (eq_trans (Plus_P4 0 (-y) H0R HnyR) (Plus_P1 (-y) HnyR)) in Ht.
    exact Ht. }
  split.
  - destruct (Leq_P4 0 x H0R Hx) as [H0x | Hxle].
    + rewrite (me_zero_Abs x Hx H0x).
      assert (Hnx0 : -x ≤ 0) by (apply (OrderPM_Co2b x Hx H0x)).
      rewrite (le_zero_Abs (-x) HnxR Hnx0).
      exact (eq_sym (Hdblneg x Hx)).
    + rewrite (le_zero_Abs x Hx Hxle).
      rewrite (me_zero_Abs (-x) HnxR (nn_neg x Hx Hxle)). reflexivity.
  - split.
    + destruct (Leq_P4 0 x H0R Hx) as [H0x | Hxle].
      * rewrite (me_zero_Abs x Hx H0x).
        assert (Hnx0 : -x ≤ 0) by (apply (OrderPM_Co2b x Hx H0x)).
        exact (Leq_P3 (-x) 0 x (Plus_neg1a x Hx) H0R Hx Hnx0 H0x).
      * rewrite (le_zero_Abs x Hx Hxle).
        rewrite (Hdblneg x Hx). apply (Leq_P1 x Hx).
    + destruct (Leq_P4 0 x H0R Hx) as [H0x | Hxle].
      * rewrite (me_zero_Abs x Hx H0x). apply (Leq_P1 x Hx).
      * rewrite (le_zero_Abs x Hx Hxle).
        exact (Leq_P3 x 0 (-x) Hx H0R (Plus_neg1a x Hx) Hxle (nn_neg x Hx Hxle)).
Qed.

Proposition Abs_P3 : ∀ x y, x ∈ R -> y ∈ R -> ｜(x · y)｜ = ｜x｜ · ｜y｜.
Proof.
  intros x y Hx Hy.
  assert (H0R : 0 ∈ R) by (apply zero_in_R).
  assert (HxyR : x · y ∈ R) by (apply (Mult_close x y Hx Hy)).
  assert (dblneg : ∀ a, a ∈ R -> -(-a) = a).
  { intros a Ha.
    assert (Hnega : -a ∈ R) by (apply (Plus_neg1a a Ha)).
    assert (H1 : (-a) + a = 0) by (exact (eq_trans (Plus_P4 (-a) a Hnega Ha) (Plus_neg2 a Ha))).
    assert (H2 : (-a) + (-(-a)) = 0) by (apply (Plus_neg2 (-a) Hnega)).
    destruct (Plus_Co2 (-a) Hnega) as [z [[_ _] Huniq]].
    assert (He1 : z = a) by (exact (Huniq a (conj Ha H1))).
    assert (He2 : z = -(-a)) by (exact (Huniq (-(-a)) (conj (Plus_neg1a (-a) Hnega) H2))).
    rewrite <- He2. exact He1. }
  assert (neg_multR : ∀ a b, a ∈ R -> b ∈ R -> -(a · b) = a · (-b)).
  { intros a b Ha Hb.
    assert (Hnegb : -b ∈ R) by (apply (Plus_neg1a b Hb)).
    assert (Hab : a · b ∈ R) by (apply (Mult_close a b Ha Hb)).
    assert (Hanb : a · (-b) ∈ R) by (apply (Mult_close a (-b) Ha Hnegb)).
    assert (Hsum : a · b + a · (-b) = 0).
    { transitivity (b · a + (-b) · a).
      - rewrite (Mult_P4 a b Ha Hb). rewrite (Mult_P4 a (-b) Ha Hnegb). reflexivity.
      - transitivity ((b + (-b)) · a).
        + symmetry. apply (Mult_P5 b (-b) a Hb Hnegb Ha).
        + transitivity (0 · a).
          * rewrite (Plus_neg2 b Hb). reflexivity.
          * transitivity (a · 0).
            -- apply (Mult_P4 0 a H0R Ha).
            -- apply (PlusMult_Co1 a Ha). }
    assert (Hres : a · (-b) = 0 + (-(a · b)))
      by (apply (Plus_Co3 (a · b) (a · (-b)) 0 Hab Hanb H0R Hsum)).
    assert (Hfull : a · (-b) = -(a · b))
      by (exact (eq_trans Hres (eq_trans (Plus_P4 0 (-(a · b)) H0R (Plus_neg1a (a · b) Hab))
                                          (Plus_P1 (-(a · b)) (Plus_neg1a (a · b) Hab))))).
    symmetry. exact Hfull. }
  assert (neg_multL : ∀ a b, a ∈ R -> b ∈ R -> -(a · b) = (-a) · b).
  { intros a b Ha Hb.
    assert (Hba : a · b = b · a) by (apply (Mult_P4 a b Ha Hb)).
    rewrite Hba. rewrite (neg_multR b a Hb Ha).
    rewrite (Mult_P4 b (-a) Hb (Plus_neg1a a Ha)). reflexivity. }
  assert (neg_neg_mul : ∀ a b, a ∈ R -> b ∈ R -> (-a) · (-b) = a · b).
  { intros a b Ha Hb.
    assert (E1 : (-a) · (-b) = -(a · (-b))) by (symmetry; apply (neg_multL a (-b) Ha (Plus_neg1a b Hb))).
    assert (E2 : a · (-b) = -(a · b)) by (symmetry; apply (neg_multR a b Ha Hb)).
    rewrite E1. rewrite E2. apply dblneg. apply (Mult_close a b Ha Hb). }
  assert (mul_np : ∀ a b, a ∈ R -> b ∈ R -> 0 ≤ a -> b ≤ 0 -> a · b ≤ 0).
  { intros a b Ha Hb Ha0 Hb0.
    assert (Ht : b · a ≤ 0 · a) by (apply (OrderPM_Co7b b 0 a Hb H0R Ha Hb0 Ha0)).
    rewrite (Mult_P4 b a Hb Ha) in Ht.
    rewrite (Mult_P4 0 a H0R Ha) in Ht.
    rewrite (PlusMult_Co1 a Ha) in Ht.
    exact Ht. }
  assert (mul_nn : ∀ a b, a ∈ R -> b ∈ R -> a ≤ 0 -> b ≤ 0 -> 0 ≤ a · b).
  { intros a b Ha Hb Ha0 Hb0.
    destruct (classic (a = 0)) as [Ha_eq | Ha_ne].
    - subst a. rewrite (Mult_P4 0 b H0R Hb). rewrite (PlusMult_Co1 b Hb). apply (Leq_P1 0 H0R).
    - destruct (classic (b = 0)) as [Hb_eq | Hb_ne].
      + subst b. rewrite (PlusMult_Co1 a Ha). apply (Leq_P1 0 H0R).
      + assert (Ha_lt : a < 0) by (split; [exact Ha0 | exact Ha_ne]).
        assert (Hb_lt : b < 0) by (split; [exact Hb0 | exact Hb_ne]).
        assert (Hna_lt : 0 < -a).
        { assert (Ht : a + (-a) < 0 + (-a)) by (apply (OrderPM_Co1 a 0 (-a) Ha H0R (Plus_neg1a a Ha) Ha_lt)).
          rewrite (Plus_neg2 a Ha) in Ht.
          rewrite (eq_trans (Plus_P4 0 (-a) H0R (Plus_neg1a a Ha)) (Plus_P1 (-a) (Plus_neg1a a Ha))) in Ht.
          exact Ht. }
        assert (Hnb_lt : 0 < -b).
        { assert (Ht : b + (-b) < 0 + (-b)) by (apply (OrderPM_Co1 b 0 (-b) Hb H0R (Plus_neg1a b Hb) Hb_lt)).
          rewrite (Plus_neg2 b Hb) in Ht.
          rewrite (eq_trans (Plus_P4 0 (-b) H0R (Plus_neg1a b Hb)) (Plus_P1 (-b) (Plus_neg1a b Hb))) in Ht.
          exact Ht. }
        assert (Hpos : 0 < (-a) · (-b)) by (apply (OrderPM_Co5 (-a) (-b) (Plus_neg1a a Ha) (Plus_neg1a b Hb)); left; split; assumption).
        rewrite <- (neg_neg_mul a b Ha Hb). exact (proj1 Hpos). }
  destruct (Leq_P4 0 x H0R Hx) as [H0x | Hxle];
  destruct (Leq_P4 0 y H0R Hy) as [H0y | Hyle].
  - rewrite (me_zero_Abs x Hx H0x). rewrite (me_zero_Abs y Hy H0y).
    assert (H0xy : 0 ≤ x · y) by (apply (Mult_Leq x y Hx Hy H0x H0y)).
    exact (me_zero_Abs (x · y) HxyR H0xy).
  - rewrite (me_zero_Abs x Hx H0x). rewrite (le_zero_Abs y Hy Hyle).
    assert (Hle : x · y ≤ 0) by (apply (mul_np x y Hx Hy H0x Hyle)).
    rewrite (le_zero_Abs (x · y) HxyR Hle).
    rewrite (neg_multR x y Hx Hy). reflexivity.
  - rewrite (le_zero_Abs x Hx Hxle). rewrite (me_zero_Abs y Hy H0y).
    assert (Hle : x · y ≤ 0).
    { assert (Ht : x · y ≤ 0 · y) by (apply (OrderPM_Co7b x 0 y Hx H0R Hy Hxle H0y)).
      rewrite (Mult_P4 0 y H0R Hy) in Ht. rewrite (PlusMult_Co1 y Hy) in Ht. exact Ht. }
    rewrite (le_zero_Abs (x · y) HxyR Hle).
    rewrite (neg_multL x y Hx Hy). reflexivity.
  - rewrite (le_zero_Abs x Hx Hxle). rewrite (le_zero_Abs y Hy Hyle).
    assert (Hle : 0 ≤ x · y) by (apply (mul_nn x y Hx Hy Hxle Hyle)).
    rewrite (me_zero_Abs (x · y) HxyR Hle).
    rewrite (neg_neg_mul x y Hx Hy). reflexivity.
Qed.

Proposition Abs_P4 : ∀ x y, x ∈ R -> y ∈ R -> 0 ≤ y
  -> ｜x｜ ≤ y <-> (-y ≤ x /\ x ≤ y).
Proof.
  intros x y Hx Hy H0y.
  assert (H0R : 0 ∈ R) by (apply zero_in_R).
  assert (HabsR : ｜x｜ ∈ R) by (apply (Abs_in_R x Hx)).
  assert (HnyR : -y ∈ R) by (apply (Plus_neg1a y Hy)).
  assert (HnabsR : -｜x｜ ∈ R) by (apply (Plus_neg1a ｜x｜ HabsR)).
  assert (dblneg : ∀ a, a ∈ R -> -(-a) = a).
  { intros a Ha.
    assert (Hnega : -a ∈ R) by (apply (Plus_neg1a a Ha)).
    assert (H1 : (-a) + a = 0) by (exact (eq_trans (Plus_P4 (-a) a Hnega Ha) (Plus_neg2 a Ha))).
    assert (H2 : (-a) + (-(-a)) = 0) by (apply (Plus_neg2 (-a) Hnega)).
    destruct (Plus_Co2 (-a) Hnega) as [z [[_ _] Huniq]].
    assert (He1 : z = a) by (exact (Huniq a (conj Ha H1))).
    assert (He2 : z = -(-a)) by (exact (Huniq (-(-a)) (conj (Plus_neg1a (-a) Hnega) H2))).
    rewrite <- He2. exact He1. }
  assert (ple : ∀ a b, a ∈ R -> b ∈ R -> a ≤ b -> -b ≤ -a).
  { intros a b Ha Hb Hab.
    assert (Hnega : -a ∈ R) by (apply (Plus_neg1a a Ha)).
    assert (Hnegb : -b ∈ R) by (apply (Plus_neg1a b Hb)).
    assert (Ht1 : a + (-b) ≤ b + (-b)) by (apply (Plus_Leq a b (-b) Ha Hb Hnegb Hab)).
    rewrite (Plus_neg2 b Hb) in Ht1.
    assert (Ht2 : (a + (-b)) + (-a) ≤ 0 + (-a))
      by (apply (Plus_Leq (a + (-b)) 0 (-a) (Plus_close a (-b) Ha Hnegb) H0R Hnega Ht1)).
    rewrite (eq_trans (Plus_P4 0 (-a) H0R Hnega) (Plus_P1 (-a) Hnega)) in Ht2.
    assert (Heq : (a + (-b)) + (-a) = -b).
    { transitivity ((-b) + (a + (-a))).
      - rewrite (Plus_P4 a (-b) Ha Hnegb). symmetry. apply (Plus_P3 (-b) a (-a) Hnegb Ha Hnega).
      - rewrite (Plus_neg2 a Ha). apply (Plus_P1 (-b) Hnegb). }
    rewrite Heq in Ht2. exact Ht2. }
  split.
  - intros Hle.
    assert (Hxle_abs : x ≤ ｜x｜) by (exact (proj2 (proj2 (Abs_P2 x Hx)))).
    assert (Hnabs_le_x : -｜x｜ ≤ x) by (exact (proj1 (proj2 (Abs_P2 x Hx)))).
    split.
    + assert (Hny_le_nabs : -y ≤ -｜x｜) by (apply (ple ｜x｜ y HabsR Hy Hle)).
      exact (Leq_P3 (-y) (-｜x｜) x HnyR HnabsR Hx Hny_le_nabs Hnabs_le_x).
    + exact (Leq_P3 x ｜x｜ y Hx HabsR Hy Hxle_abs Hle).
  - intros [Hnyx Hxy].
    destruct (Leq_P4 0 x H0R Hx) as [H0x | Hxle].
    + rewrite (me_zero_Abs x Hx H0x). exact Hxy.
    + rewrite (le_zero_Abs x Hx Hxle).
      assert (HnxR : -x ∈ R) by (apply (Plus_neg1a x Hx)).
      assert (Ht : -x ≤ -(-y)) by (apply (ple (-y) x HnyR Hx Hnyx)).
      rewrite (dblneg y Hy) in Ht. exact Ht.
Qed.

Proposition Abs_P5 : ∀ x y, x ∈ R -> y ∈ R -> ｜(x + y)｜ ≤ ｜x｜ + ｜y｜
  /\ ｜(x - y)｜ ≤ ｜x｜ + ｜y｜ /\ ｜(｜x｜ - ｜y｜)｜ ≤ ｜(x - y)｜.
Proof.
  intros x y Hx Hy.
  assert (H0R : 0 ∈ R) by (apply zero_in_R).
  assert (HxR : ｜x｜ ∈ R) by (apply (Abs_in_R x Hx)).
  assert (HyR : ｜y｜ ∈ R) by (apply (Abs_in_R y Hy)).
  assert (HnyR : -y ∈ R) by (apply (Plus_neg1a y Hy)).
  assert (HnxR : -x ∈ R) by (apply (Plus_neg1a x Hx)).
  assert (Hdblneg : ∀ a, a ∈ R -> -(-a) = a).
  { intros a Ha.
    assert (Hnega : -a ∈ R) by (apply (Plus_neg1a a Ha)).
    assert (H1 : (-a) + a = 0) by (exact (eq_trans (Plus_P4 (-a) a Hnega Ha) (Plus_neg2 a Ha))).
    assert (H2 : (-a) + (-(-a)) = 0) by (apply (Plus_neg2 (-a) Hnega)).
    destruct (Plus_Co2 (-a) Hnega) as [z [[_ _] Huniq]].
    assert (He1 : z = a) by (exact (Huniq a (conj Ha H1))).
    assert (He2 : z = -(-a)) by (exact (Huniq (-(-a)) (conj (Plus_neg1a (-a) Hnega) H2))).
    rewrite <- He2. exact He1. }
  assert (Hneg_add : ∀ a b, a ∈ R -> b ∈ R -> -(a + b) = (-a) + (-b)).
  { intros a b Ha Hb.
    assert (Hnega : -a ∈ R) by (apply (Plus_neg1a a Ha)).
    assert (Hnegb : -b ∈ R) by (apply (Plus_neg1a b Hb)).
    assert (Hab : (a + b) ∈ R) by (apply (Plus_close a b Ha Hb)).
    assert (HsumR : ((-a) + (-b)) ∈ R) by (apply (Plus_close (-a) (-b) Hnega Hnegb)).
    assert (Hzero : (a + b) + ((-a) + (-b)) = 0).
    { transitivity (((a + b) + (-a)) + (-b)).
      - apply (Plus_P3 (a + b) (-a) (-b) Hab Hnega Hnegb).
      - assert (Hmid : (a + b) + (-a) = b).
        { transitivity ((b + a) + (-a)).
          - rewrite (Plus_P4 a b Ha Hb). reflexivity.
          - transitivity (b + (a + (-a))).
            + symmetry. apply (Plus_P3 b a (-a) Hb Ha Hnega).
            + transitivity (b + 0).
              * rewrite (Plus_neg2 a Ha). reflexivity.
              * apply (Plus_P1 b Hb). }
        rewrite Hmid. apply (Plus_neg2 b Hb). }
    assert (Hres : ((-a) + (-b)) = 0 + (-(a + b)))
      by (apply (Plus_Co3 (a + b) ((-a) + (-b)) 0 Hab HsumR H0R Hzero)).
    assert (H0y : 0 + (-(a + b)) = -(a + b))
      by (exact (eq_trans (Plus_P4 0 (-(a + b)) H0R (Plus_neg1a (a + b) Hab))
                          (Plus_P1 (-(a + b)) (Plus_neg1a (a + b) Hab)))).
    rewrite H0y in Hres. symmetry. exact Hres. }
  assert (Hle_abs : ∀ a, a ∈ R -> a ≤ ｜a｜).
  { intros a Ha. exact (proj2 (proj2 (Abs_P2 a Ha))). }
  assert (Hneg_le_abs : ∀ a, a ∈ R -> -a ≤ ｜a｜).
  { intros a Ha.
    assert (HnaR : -a ∈ R) by (apply (Plus_neg1a a Ha)).
    assert (H1 : -a ≤ ｜(-a)｜) by (exact (proj2 (proj2 (Abs_P2 (-a) HnaR)))).
    rewrite <- (proj1 (Abs_P2 a Ha)) in H1. exact H1. }
  assert (abs_tri : ∀ a b, a ∈ R -> b ∈ R -> ｜(a + b)｜ ≤ ｜a｜ + ｜b｜).
  { intros a b Ha Hb.
    assert (HaR : ｜a｜ ∈ R) by (apply (Abs_in_R a Ha)).
    assert (HbR : ｜b｜ ∈ R) by (apply (Abs_in_R b Hb)).
    assert (HabR : a + b ∈ R) by (apply (Plus_close a b Ha Hb)).
    assert (Hnxa : -a ∈ R) by (apply (Plus_neg1a a Ha)).
    assert (Hnxb : -b ∈ R) by (apply (Plus_neg1a b Hb)).
    assert (Hsum1 : a + b ≤ ｜a｜ + ｜b｜)
      by (apply (OrderPM_Co3 a ｜a｜ b ｜b｜ Ha HaR Hb HbR (Hle_abs a Ha) (Hle_abs b Hb))).
    assert (Hsum2 : (-a) + (-b) ≤ ｜a｜ + ｜b｜)
      by (apply (OrderPM_Co3 (-a) ｜a｜ (-b) ｜b｜ Hnxa HaR Hnxb HbR (Hneg_le_abs a Ha) (Hneg_le_abs b Hb))).
    assert (Hsum2' : -(a + b) ≤ ｜a｜ + ｜b｜) by (rewrite (Hneg_add a b Ha Hb); exact Hsum2).
    destruct (Leq_P4 0 (a + b) H0R HabR) as [H0ab | Hable].
    - rewrite (me_zero_Abs (a + b) HabR H0ab). exact Hsum1.
    - rewrite (le_zero_Abs (a + b) HabR Hable). exact Hsum2'. }
  split.
  - exact (abs_tri x y Hx Hy).
  - split.
    + assert (H1 : ｜(x + (-y))｜ ≤ ｜x｜ + ｜(-y)｜) by (apply (abs_tri x (-y) Hx HnyR)).
      rewrite (eq_sym (proj1 (Abs_P2 y Hy))) in H1.
      exact H1.
    + assert (HxyR : x + (-y) ∈ R) by (apply (Plus_close x (-y) Hx HnyR)).
      assert (HD : ｜(x + (-y))｜ ∈ R) by (apply (Abs_in_R (x + (-y)) HxyR)).
      assert (H1 : ｜x｜ ≤ ｜(x + (-y))｜ + ｜y｜).
      { assert (Htmp : ｜((x + (-y)) + y)｜ ≤ ｜(x + (-y))｜ + ｜y｜) by (apply (abs_tri (x + (-y)) y HxyR Hy)).
        assert (Heq : (x + (-y)) + y = x).
        { transitivity (x + ((-y) + y)).
          - symmetry. apply (Plus_P3 x (-y) y Hx HnyR Hy).
          - rewrite (eq_trans (Plus_P4 (-y) y HnyR Hy) (Plus_neg2 y Hy)). apply (Plus_P1 x Hx). }
        rewrite Heq in Htmp. exact Htmp. }
      assert (H2 : ｜y｜ ≤ ｜(x + (-y))｜ + ｜x｜).
      { assert (HnyxR : y + (-x) ∈ R) by (apply (Plus_close y (-x) Hy HnxR)).
        assert (Htmp : ｜((y + (-x)) + x)｜ ≤ ｜(y + (-x))｜ + ｜x｜) by (apply (abs_tri (y + (-x)) x HnyxR Hx)).
        assert (Heq : (y + (-x)) + x = y).
        { transitivity (y + ((-x) + x)).
          - symmetry. apply (Plus_P3 y (-x) x Hy HnxR Hx).
          - rewrite (eq_trans (Plus_P4 (-x) x HnxR Hx) (Plus_neg2 x Hx)). apply (Plus_P1 y Hy). }
        rewrite Heq in Htmp.
        assert (Heq2 : ｜(y + (-x))｜ = ｜(x + (-y))｜).
        { assert (Hn : y + (-x) = -(x + (-y))).
          { rewrite (Hneg_add x (-y) Hx HnyR). rewrite (Hdblneg y Hy).
            rewrite (Plus_P4 (-x) y HnxR Hy). reflexivity. }
          rewrite Hn. exact (eq_sym (proj1 (Abs_P2 (x + (-y)) HxyR))). }
        rewrite Heq2 in Htmp. exact Htmp. }
      assert (HnyRabs : -｜y｜ ∈ R) by (apply (Plus_neg1a ｜y｜ HyR)).
      assert (HnxRabs : -｜x｜ ∈ R) by (apply (Plus_neg1a ｜x｜ HxR)).
      assert (Hm1 : ｜x｜ - ｜y｜ ≤ ｜(x + (-y))｜).
      { assert (Ht : ｜x｜ + (-｜y｜) ≤ (｜(x + (-y))｜ + ｜y｜) + (-｜y｜))
          by (apply (Plus_Leq ｜x｜ (｜(x + (-y))｜ + ｜y｜) (-｜y｜) HxR (Plus_close ｜(x + (-y))｜ ｜y｜ HD HyR) HnyRabs H1)).
        assert (Heq : (｜(x + (-y))｜ + ｜y｜) + (-｜y｜) = ｜(x + (-y))｜).
        { transitivity (｜(x + (-y))｜ + (｜y｜ + (-｜y｜))).
          - symmetry. apply (Plus_P3 ｜(x + (-y))｜ ｜y｜ (-｜y｜) HD HyR HnyRabs).
          - rewrite (Plus_neg2 ｜y｜ HyR). apply (Plus_P1 ｜(x + (-y))｜ HD). }
        rewrite Heq in Ht. exact Ht. }
      assert (Hm2 : -(｜x｜ - ｜y｜) ≤ ｜(x + (-y))｜).
      { assert (Ht : ｜y｜ + (-｜x｜) ≤ (｜(x + (-y))｜ + ｜x｜) + (-｜x｜))
          by (apply (Plus_Leq ｜y｜ (｜(x + (-y))｜ + ｜x｜) (-｜x｜) HyR (Plus_close ｜(x + (-y))｜ ｜x｜ HD HxR) HnxRabs H2)).
        assert (Heq : (｜(x + (-y))｜ + ｜x｜) + (-｜x｜) = ｜(x + (-y))｜).
        { transitivity (｜(x + (-y))｜ + (｜x｜ + (-｜x｜))).
          - symmetry. apply (Plus_P3 ｜(x + (-y))｜ ｜x｜ (-｜x｜) HD HxR HnxRabs).
          - rewrite (Plus_neg2 ｜x｜ HxR). apply (Plus_P1 ｜(x + (-y))｜ HD). }
        rewrite Heq in Ht.
        assert (Heq3 : -(｜x｜ + (-｜y｜)) = ｜y｜ + (-｜x｜)).
        { rewrite (Hneg_add ｜x｜ (-｜y｜) HxR HnyRabs). rewrite (Hdblneg ｜y｜ HyR).
          rewrite (Plus_P4 (-｜x｜) ｜y｜ HnxRabs HyR). reflexivity. }
        rewrite <- Heq3 in Ht. exact Ht. }
      destruct (Leq_P4 0 (｜x｜ + (-｜y｜)) H0R (Plus_close ｜x｜ (-｜y｜) HxR HnyRabs)) as [H0P | HPle].
      { rewrite (me_zero_Abs (｜x｜ + (-｜y｜)) (Plus_close ｜x｜ (-｜y｜) HxR HnyRabs) H0P). exact Hm1. }
      { rewrite (le_zero_Abs (｜x｜ + (-｜y｜)) (Plus_close ｜x｜ (-｜y｜) HxR HnyRabs) HPle). exact Hm2. }
Qed.

Proposition Abs_P6 : ∀ x y, x ∈ R -> y ∈ R -> ｜(x - y)｜ = 0 <-> x = y.
Proof.
  intros x y Hx Hy.
  assert (H0R : 0 ∈ R) by (apply zero_in_R).
  assert (HnyR : -y ∈ R) by (apply (Plus_neg1a y Hy)).
  assert (HxyR : x + (-y) ∈ R) by (apply (Plus_close x (-y) Hx HnyR)).
  split.
  - intros Habs0.
    assert (Hxy0 : x + (-y) = 0) by (exact ((proj1 (proj2 (Abs_P1 (x + (-y)) HxyR))) Habs0)).
    transitivity ((x + (-y)) + y).
    { symmetry.
      transitivity (x + ((-y) + y)).
      - symmetry. apply (Plus_P3 x (-y) y Hx HnyR Hy).
      - rewrite (eq_trans (Plus_P4 (-y) y HnyR Hy) (Plus_neg2 y Hy)). apply (Plus_P1 x Hx). }
    { rewrite Hxy0. rewrite (eq_trans (Plus_P4 0 y H0R Hy) (Plus_P1 y Hy)). reflexivity. }
  - intros Hxy. subst y.
    rewrite (Plus_neg2 x Hx).
    change (｜0｜ = 0).
    apply (me_zero_Abs 0 H0R). apply (Leq_P1 0 H0R).
Qed.

Proposition Abs_P7 : ∀ x y, x ∈ R -> y ∈ R -> ｜(x - y)｜ = ｜(y - x)｜.
Proof.
  intros x y Hx Hy.
  assert (H0R : 0 ∈ R) by (apply zero_in_R).
  assert (HnyR : -y ∈ R) by (apply (Plus_neg1a y Hy)).
  assert (HnxR : -x ∈ R) by (apply (Plus_neg1a x Hx)).
  assert (HxyR : x + (-y) ∈ R) by (apply (Plus_close x (-y) Hx HnyR)).
  assert (Hdblneg : ∀ a, a ∈ R -> -(-a) = a).
  { intros a Ha.
    assert (Hnega : -a ∈ R) by (apply (Plus_neg1a a Ha)).
    assert (H1 : (-a) + a = 0) by (exact (eq_trans (Plus_P4 (-a) a Hnega Ha) (Plus_neg2 a Ha))).
    assert (H2 : (-a) + (-(-a)) = 0) by (apply (Plus_neg2 (-a) Hnega)).
    destruct (Plus_Co2 (-a) Hnega) as [z [[_ _] Huniq]].
    assert (He1 : z = a) by (exact (Huniq a (conj Ha H1))).
    assert (He2 : z = -(-a)) by (exact (Huniq (-(-a)) (conj (Plus_neg1a (-a) Hnega) H2))).
    rewrite <- He2. exact He1. }
  assert (Hneg_add : ∀ a b, a ∈ R -> b ∈ R -> -(a + b) = (-a) + (-b)).
  { intros a b Ha Hb.
    assert (Hnega : -a ∈ R) by (apply (Plus_neg1a a Ha)).
    assert (Hnegb : -b ∈ R) by (apply (Plus_neg1a b Hb)).
    assert (Hab : (a + b) ∈ R) by (apply (Plus_close a b Ha Hb)).
    assert (HsumR : ((-a) + (-b)) ∈ R) by (apply (Plus_close (-a) (-b) Hnega Hnegb)).
    assert (Hzero : (a + b) + ((-a) + (-b)) = 0).
    { transitivity (((a + b) + (-a)) + (-b)).
      - apply (Plus_P3 (a + b) (-a) (-b) Hab Hnega Hnegb).
      - assert (Hmid : (a + b) + (-a) = b).
        { transitivity ((b + a) + (-a)).
          - rewrite (Plus_P4 a b Ha Hb). reflexivity.
          - transitivity (b + (a + (-a))).
            + symmetry. apply (Plus_P3 b a (-a) Hb Ha Hnega).
            + transitivity (b + 0).
              * rewrite (Plus_neg2 a Ha). reflexivity.
              * apply (Plus_P1 b Hb). }
        rewrite Hmid. apply (Plus_neg2 b Hb). }
    assert (Hres : ((-a) + (-b)) = 0 + (-(a + b)))
      by (apply (Plus_Co3 (a + b) ((-a) + (-b)) 0 Hab HsumR H0R Hzero)).
    assert (H0y : 0 + (-(a + b)) = -(a + b))
      by (exact (eq_trans (Plus_P4 0 (-(a + b)) H0R (Plus_neg1a (a + b) Hab))
                          (Plus_P1 (-(a + b)) (Plus_neg1a (a + b) Hab)))).
    rewrite H0y in Hres. symmetry. exact Hres. }
  assert (Hdbl : y + (-x) = -(x + (-y))).
  { rewrite (Hneg_add x (-y) Hx HnyR). rewrite (Hdblneg y Hy).
    rewrite (Plus_P4 (-x) y HnxR Hy). reflexivity. }
  rewrite Hdbl.
  exact (proj1 (Abs_P2 (x + (-y)) HxyR)).
Qed.

Proposition Abs_P8 : ∀ x y z, x ∈ R -> y ∈ R -> z ∈ R
  -> ｜(x - y)｜ ≤ ｜(x - z)｜ + ｜(z - y)｜.
Proof.
  intros x y z Hx Hy Hz.
  assert (H0R : 0 ∈ R) by (apply zero_in_R).
  assert (HnyR : -y ∈ R) by (apply (Plus_neg1a y Hy)).
  assert (HnzR : -z ∈ R) by (apply (Plus_neg1a z Hz)).
  assert (HxzR : x + (-z) ∈ R) by (apply (Plus_close x (-z) Hx HnzR)).
  assert (HzyR : z + (-y) ∈ R) by (apply (Plus_close z (-y) Hz HnyR)).
  assert (Heq : (x + (-z)) + (z + (-y)) = x + (-y)).
  { transitivity (x + ((-z) + (z + (-y)))).
    - symmetry. apply (Plus_P3 x (-z) (z + (-y)) Hx HnzR HzyR).
    - transitivity (x + (((-z) + z) + (-y))).
      + rewrite (Plus_P3 (-z) z (-y) HnzR Hz HnyR). reflexivity.
      + rewrite (eq_trans (Plus_P4 (-z) z HnzR Hz) (Plus_neg2 z Hz)).
        rewrite (eq_trans (Plus_P4 0 (-y) H0R HnyR) (Plus_P1 (-y) HnyR)). reflexivity. }
  rewrite <- Heq.
  exact (proj1 (Abs_P5 (x + (-z)) (z + (-y)) HxzR HzyR)).
Qed.

End R1_reals.
