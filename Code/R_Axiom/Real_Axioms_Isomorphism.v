Require Export Real_Axioms1.

(* ==================== 实数结构同构的概念 ==================== *)
(* 两个满足实数公理体系的结构同构，是指存在一个双射 f : R1 -> R2，
   它保持加法、乘法与序 *)

Definition R_iso (RR1 RR2 : Real_struct) (ax1 : Real_axioms RR1) (ax2 : Real_axioms RR2)
    (f : Class) : Prop :=
  Function f /\
  (∀ x, x ∈ @R RR1 -> f[x] ∈ @R RR2) /\
  (∀ x, x ∈ @R RR1 -> ∀ y, y ∈ @R RR1 ->
      f[(@fp RR1)[[x, y]]] = (@fp RR2)[[f[x], f[y]]]) /\
  (∀ x, x ∈ @R RR1 -> ∀ y, y ∈ @R RR1 ->
      f[(@fm RR1)[[x, y]]] = (@fm RR2)[[f[x], f[y]]]) /\
  (∀ x, x ∈ @R RR1 -> ∀ y, y ∈ @R RR1 ->
      ([x, y] ∈ @Leq RR1 <-> [f[x], f[y]] ∈ @Leq RR2)) /\
  (∀ x, x ∈ @R RR1 -> ∀ y, y ∈ @R RR1 -> f[x] = f[y] -> x = y) /\
  (∀ y, y ∈ @R RR2 -> ∃ x, x ∈ @R RR1 /\ f[x] = y).

Section Isomorphism.

Variable RR1 : Real_struct.
Variable ax1 : Real_axioms RR1.
Variable RR2 : Real_struct.
Variable ax2 : Real_axioms RR2.

Definition car1 : Class := @R RR1.
Definition car2 : Class := @R RR2.
Definition fp1 : Class := @fp RR1.
Definition fp2 : Class := @fp RR2.
Definition fm1 : Class := @fm RR1.
Definition fm2 : Class := @fm RR2.
Definition z1 : Class := @zeroR RR1.
Definition z2 : Class := @zeroR RR2.
Definition o1 : Class := @oneR RR1.
Definition o2 : Class := @oneR RR2.
Definition lq1 : Class := @Leq RR1.
Definition lq2 : Class := @Leq RR2.

Definition add1 (x y:Class) : Class := fp1[[x,y]].
Definition add2 (x y:Class) : Class := fp2[[x,y]].
Definition mul1 (x y:Class) : Class := fm1[[x,y]].
Definition mul2 (x y:Class) : Class := fm2[[x,y]].
Definition le1 (x y:Class) : Prop := [x,y] ∈ lq1.
Definition le2 (x y:Class) : Prop := [x,y] ∈ lq2.
Definition lt1 (x y:Class) : Prop := le1 x y /\ x <> y.
Definition lt2 (x y:Class) : Prop := le2 x y /\ x <> y.

Lemma lt1_rw : ∀ a a' b b', a = a' -> b = b' -> lt1 a b -> lt1 a' b'.
Proof.
  intros a a' b b' H1 H2 H.
  exact (@eq_rect Class b (fun v => lt1 a' v)
           (@eq_rect Class a (fun u => lt1 u b) H a' H1) b' H2).
Qed.

Lemma lt2_rw : ∀ a a' b b', a = a' -> b = b' -> lt2 a b -> lt2 a' b'.
Proof.
  intros a a' b b' H1 H2 H.
  exact (@eq_rect Class b (fun v => lt2 a' v)
           (@eq_rect Class a (fun u => lt2 u b) H a' H1) b' H2).
Qed.

Lemma le1_rw : ∀ a a' b b', a = a' -> b = b' -> le1 a b -> le1 a' b'.
Proof.
  intros a a' b b' H1 H2 H.
  exact (@eq_rect Class b (fun v => le1 a' v)
           (@eq_rect Class a (fun u => le1 u b) H a' H1) b' H2).
Qed.

Lemma le2_rw : ∀ a a' b b', a = a' -> b = b' -> le2 a b -> le2 a' b'.
Proof.
  intros a a' b b' H1 H2 H.
  exact (@eq_rect Class b (fun v => le2 a' v)
           (@eq_rect Class a (fun u => le2 u b) H a' H1) b' H2).
Qed.

Lemma lt1_le1_or : ∀ a b c, lt1 a b -> le1 b c -> (lt1 a b /\ le1 b c) \/ (le1 a b /\ lt1 b c).
Proof. intros a b c H1 H2. left. split; assumption. Qed.

Lemma le1_lt1_or : ∀ a b c, le1 a b -> lt1 b c -> (lt1 a b /\ le1 b c) \/ (le1 a b /\ lt1 b c).
Proof. intros a b c H1 H2. right. split; assumption. Qed.

Lemma lt2_le2_or : ∀ a b c, lt2 a b -> le2 b c -> (lt2 a b /\ le2 b c) \/ (le2 a b /\ lt2 b c).
Proof. intros a b c H1 H2. left. split; assumption. Qed.

Lemma le2_lt2_or : ∀ a b c, le2 a b -> lt2 b c -> (lt2 a b /\ le2 b c) \/ (le2 a b /\ lt2 b c).
Proof. intros a b c H1 H2. right. split; assumption. Qed.

Lemma Ens_car1 : ∀ z, z ∈ car1 -> Ensemble z.
Proof. intros z Hz. unfold Ensemble. exists car1. exact Hz. Qed.
Lemma Ens_car2 : ∀ z, z ∈ car2 -> Ensemble z.
Proof. intros z Hz. unfold Ensemble. exists car2. exact Hz. Qed.
Lemma z1_car : z1 ∈ car1. Proof. apply (@zero_in_R RR1 ax1). Qed.
Lemma z2_car : z2 ∈ car2. Proof. apply (@zero_in_R RR2 ax2). Qed.
Lemma o1_car : o1 ∈ car1. Proof. apply (@one_in_R_Co RR1 ax1). Qed.
Lemma o2_car : o2 ∈ car2. Proof. apply (@one_in_R_Co RR2 ax2). Qed.

(* ---------- 说明：omega 到 car2 的标准嵌入（suit2 / SN2 / phi2）在本证明中未被使用， ---------- *)
(* ---------- 为保证编译轻量与稳定，这里只保留后续真正用到的引理。               ---------- *)

(* ---------- omega 相关的辅助引理 Ens_omega / omega_ord / omega_Ordinal / omega_trans 未使用，已移除 ---------- *)

Lemma lt2_asym : ∀ a b, a ∈ car2 -> b ∈ car2 -> lt2 a b -> lt2 b a -> False.
Proof.
  intros a b Ha Hb [Hab Hne] [Hba _].
  exact (Hne (@Leq_P2 RR2 ax2 a b Ha Hb Hab Hba)).
Qed.

(* ---------------- N1 与 N2 ---------------- *)

Definition N1 : Class := @N RR1.
Definition N2 : Class := @N RR2.
Definition Z1 : Class := @Z RR1.
Definition Z2 : Class := @Z RR2.
Definition Q1 : Class := @Q RR1.
Definition Q2 : Class := @Q RR2.

Lemma N1_sub_car1 : N1 ⊂ car1.
Proof. unfold N1, car1. intros z Hz. apply (@N_Subset_R RR1 ax1 z); exact Hz. Qed.

Lemma N2_sub_car2 : N2 ⊂ car2.
Proof. unfold N2, car2. intros z Hz. apply (@N_Subset_R RR2 ax2 z); exact Hz. Qed.

(* ---------------- 后继与序 ---------------- *)

Lemma lt_add_one1 : ∀ x, x ∈ car1 -> lt1 x (add1 x o1).
Proof.
  intros x Hx.
  assert (Ht : lt1 (add1 z1 x) (add1 o1 x))
    by (apply (@OrderPM_Co1 RR1 ax1 z1 o1 x z1_car o1_car Hx); exact (@OrderPM_Co9 RR1 ax1)).
  assert (Hcomm : add1 o1 x = add1 x o1) by (apply (@Plus_P4 RR1 ax1 o1 x o1_car Hx)).
  assert (Hzx : add1 z1 x = x) by (apply (eq_trans (@Plus_P4 RR1 ax1 z1 x z1_car Hx) (@Plus_P1 RR1 ax1 x Hx))).
  rewrite Hcomm in Ht. rewrite Hzx in Ht. exact Ht.
Qed.

Lemma lt_add_one2 : ∀ x, x ∈ car2 -> lt2 x (add2 x o2).
Proof.
  intros x Hx.
  assert (Ht : lt2 (add2 z2 x) (add2 o2 x))
    by (apply (@OrderPM_Co1 RR2 ax2 z2 o2 x z2_car o2_car Hx); exact (@OrderPM_Co9 RR2 ax2)).
  assert (Hcomm : add2 o2 x = add2 x o2) by (apply (@Plus_P4 RR2 ax2 o2 x o2_car Hx)).
  assert (Hzx : add2 z2 x = x) by (apply (eq_trans (@Plus_P4 RR2 ax2 z2 x z2_car Hx) (@Plus_P1 RR2 ax2 x Hx))).
  rewrite Hcomm in Ht. rewrite Hzx in Ht. exact Ht.
Qed.

(* ---------------- 闭包关系 suitN / SNN ---------------- *)

Definition suitN (A:Class) : Prop :=
  A ⊂ (car1 × car2) /\ [o1, o2] ∈ A
  /\ (∀ m n, m ∈ car1 -> [m,n] ∈ A -> [add1 m o1, add2 n o2] ∈ A).

Definition SNN : Class := \{ λ z, ∀ A, suitN A -> z ∈ A \}.

Lemma suitN_std : suitN (car1 × car2).
Proof.
  unfold suitN. split.
  - intros z Hz. exact Hz.
  - split.
    + apply AxiomII. split.
      * apply MKT49a.
        -- unfold Ensemble. exists car1. exact o1_car.
        -- unfold Ensemble. exists car2. exact o2_car.
      * exists o1, o2. split; [reflexivity | split].
        -- exact o1_car.
        -- exact o2_car.
    + intros m n Hm Hmn.
      apply AxiomII in Hmn as [Emn Hmn'].
      destruct Hmn' as [u [v [Huv [Hu Hv]]]].
      destruct (MKT49b m n Emn) as [Em En].
      assert (H55 := (proj1 (MKT55 m n u v Em En)) Huv).
      destruct H55 as [Hmu Hnv]. subst u. subst v.
      apply AxiomII. split.
      * apply MKT49a.
        -- apply Ens_car1. apply (@Plus_close RR1 ax1 m o1 Hm o1_car).
        -- apply Ens_car2. apply (@Plus_close RR2 ax2 n o2 Hv o2_car).
      * exists (add1 m o1), (add2 n o2). split; [reflexivity | split].
        -- apply (@Plus_close RR1 ax1 m o1 Hm o1_car).
        -- apply (@Plus_close RR2 ax2 n o2 Hv o2_car).
Qed.

(* ---------------- SNN 的基本性质 ---------------- *)

Lemma SNN_sub : ∀ z, z ∈ SNN -> z ∈ (car1 × car2).
Proof.
  intros z Hz. apply AxiomII in Hz as [_ Hbody].
  exact (Hbody (car1 × car2) suitN_std).
Qed.

Lemma SNN_11 : [o1, o2] ∈ SNN.
Proof.
  apply AxiomII. split.
  - apply MKT49a.
    + unfold Ensemble. exists car1. exact o1_car.
    + unfold Ensemble. exists car2. exact o2_car.
  - intros A HsA. exact (proj1 (proj2 HsA)).
Qed.

Lemma cart_mono : ∀ A B C D, A ⊂ C -> B ⊂ D -> (A × B) ⊂ (C × D).
Proof.
  intros A B C D HAC HBD z Hz.
  apply AxiomII in Hz as [Ez Hz'].
  destruct Hz' as [a [b [Hab [Ha Hb]]]].
  apply AxiomII. split; [exact Ez |].
  exists a, b. split; [exact Hab | split; [apply HAC; exact Ha | apply HBD; exact Hb]].
Qed.

Lemma suitN_N1xc2 : suitN (N1 × car2).
Proof.
  unfold suitN. split.
  - apply cart_mono; [exact N1_sub_car1 | intros z Hz; exact Hz].
  - split.
    + apply AxiomII. split.
      * apply MKT49a.
        -- unfold Ensemble. exists car1. exact o1_car.
        -- unfold Ensemble. exists car2. exact o2_car.
      * exists o1, o2. split; [reflexivity | split].
        -- apply (@one_in_N RR1 ax1).
        -- exact o2_car.
    + intros m n Hm Hmn.
      apply AxiomII in Hmn as [Emn Hmn'].
      destruct Hmn' as [u [v [Huv [Hu Hv]]]].
      destruct (MKT49b m n Emn) as [Em En].
      assert (H55 := (proj1 (MKT55 m n u v Em En)) Huv).
      destruct H55 as [Hmu Hnv].
      subst u. subst v.
      apply AxiomII. split.
      * apply MKT49a.
        -- apply Ens_car1. apply (@Plus_close RR1 ax1 m o1 Hm o1_car).
        -- apply Ens_car2. apply (@Plus_close RR2 ax2 n o2 Hv o2_car).
      * exists (add1 m o1), (add2 n o2). split; [reflexivity | split].
        -- assert (HIN := @IndSet_N RR1 ax1); unfold IndSet in HIN; exact (proj2 HIN m Hu).
        -- apply (@Plus_close RR2 ax2 n o2 Hv o2_car).
Qed.

Lemma SNN_fst : ∀ m n, [m,n] ∈ SNN -> m ∈ N1.
Proof.
  intros m n Hmn.
  apply AxiomII in Hmn as [_ Hbody].
  assert (Hin : [m,n] ∈ N1 × car2) by (apply Hbody; exact suitN_N1xc2).
  apply AxiomII in Hin as [Emn Hin'].
  destruct Hin' as [u [v [Huv [Hu Hv]]]].
  destruct (MKT49b m n Emn) as [Em En].
  assert (Hmu := proj1 ((proj1 (MKT55 m n u v Em En)) Huv)).
  rewrite Hmu. exact Hu.
Qed.

Lemma suitN_car1xN2 : suitN (car1 × N2).
Proof.
  unfold suitN. split.
  - apply cart_mono; [intros z Hz; exact Hz | exact N2_sub_car2].
  - split.
    + apply AxiomII. split.
      * apply MKT49a.
        -- unfold Ensemble. exists car1. exact o1_car.
        -- unfold Ensemble. exists car2. exact o2_car.
      * exists o1, o2. split; [reflexivity | split].
        -- exact o1_car.
        -- apply (@one_in_N RR2 ax2).
    + intros m n Hm Hmn.
      apply AxiomII in Hmn as [Emn Hmn'].
      destruct Hmn' as [u [v [Huv [Hu Hv]]]].
      destruct (MKT49b m n Emn) as [Em En].
      assert (H55 := (proj1 (MKT55 m n u v Em En)) Huv).
      destruct H55 as [Hmu Hnv].
      subst u. subst v.
      apply AxiomII. split.
      * apply MKT49a.
        -- apply Ens_car1. apply (@Plus_close RR1 ax1 m o1 Hm o1_car).
        -- apply Ens_car2. apply (@Plus_close RR2 ax2 n o2 (N2_sub_car2 n Hv) o2_car).
      * exists (add1 m o1), (add2 n o2). split; [reflexivity | split].
        -- apply (@Plus_close RR1 ax1 m o1 Hm o1_car).
        -- assert (HIN := @IndSet_N RR2 ax2); unfold IndSet in HIN; exact (proj2 HIN n Hv).
Qed.

Lemma SNN_snd : ∀ m n, [m,n] ∈ SNN -> n ∈ N2.
Proof.
  intros m n Hmn.
  apply AxiomII in Hmn as [_ Hbody].
  assert (Hin : [m,n] ∈ car1 × N2) by (apply Hbody; exact suitN_car1xN2).
  apply AxiomII in Hin as [Emn Hin'].
  destruct Hin' as [u [v [Huv [Hu Hv]]]].
  destruct (MKT49b m n Emn) as [Em En].
  assert (Hnv := proj2 ((proj1 (MKT55 m n u v Em En)) Huv)).
  rewrite Hnv. exact Hv.
Qed.

(* ---------------- 闭包与后继 ---------------- *)

Lemma SNN_clos : ∀ m n, [m,n] ∈ SNN -> [add1 m o1, add2 n o2] ∈ SNN.
Proof.
  intros m n Hmn.
  assert (Hmnc : [m,n] ∈ (car1 × car2)) by (apply SNN_sub; exact Hmn).
  apply AxiomII in Hmnc as [Emn Hmnc'].
  destruct Hmnc' as [u [v [Huv [Hu Hv]]]].
  apply AxiomII in Hmn as [_ Hbody].
  destruct (MKT49b m n Emn) as [Em En].
  assert (H55 := (proj1 (MKT55 m n u v Em En)) Huv).
  destruct H55 as [Hmu Hnv].
  subst u. subst v.
  apply AxiomII. split.
  - apply MKT49a.
    + apply Ens_car1. apply (@Plus_close RR1 ax1 m o1 Hu o1_car).
    + apply Ens_car2. apply (@Plus_close RR2 ax2 n o2 Hv o2_car).
  - intros A HsA. exact ((proj2 (proj2 HsA)) m n Hu (Hbody A HsA)).
Qed.

Lemma sucN_lt : ∀ a, a ∈ N1 -> lt1 a (add1 a o1).
Proof.
  intros a Ha.
  destruct (@Nat_P3 RR1 ax1 a Ha) as [_ [Hin _]].
  apply AxiomII in Hin as [_ Hin2].
  exact (proj2 Hin2).
Qed.

Lemma sucN_ne_one : ∀ a, a ∈ N1 -> add1 a o1 <> o1.
Proof.
  intros a Ha H.
  assert (HaR : a ∈ car1) by (apply N1_sub_car1; exact Ha).
  assert (Hlt : lt1 a (add1 a o1)) by (apply sucN_lt; exact Ha).
  assert (Hmin : le1 o1 a) by (exact (proj2 (proj2 (@one_is_min_in_N RR1 ax1)) a Ha)).
  assert (Hle : le1 (add1 a o1) a) by (rewrite H; exact Hmin).
  exact ((proj2 Hlt) (@Leq_P2 RR1 ax1 a (add1 a o1) HaR (@Plus_close RR1 ax1 a o1 HaR o1_car) (proj1 Hlt) Hle)).
Qed.

Lemma sucN_inj : ∀ a u, a ∈ N1 -> u ∈ N1 -> add1 a o1 = add1 u o1 -> a = u.
Proof.
  intros a u Ha Hu H.
  assert (HaR : a ∈ car1) by (apply N1_sub_car1; exact Ha).
  assert (HuR : u ∈ car1) by (apply N1_sub_car1; exact Hu).
  destruct (@Order_Co1 RR1 ax1 a u HaR HuR) as [Hlt | [Hgt | Heq]].
  - exfalso.
    assert (Hle : le1 (add1 a o1) u) by (apply (@Nat_P4 RR1 ax1 u a Hu Ha Hlt)).
    assert (Hult : lt1 u (add1 u o1)) by (apply sucN_lt; exact Hu).
    assert (Hc : lt1 (add1 a o1) (add1 u o1))
      by (apply (@Order_Co2 RR1 ax1 (add1 a o1) u (add1 u o1) (@Plus_close RR1 ax1 a o1 HaR o1_car) HuR (@Plus_close RR1 ax1 u o1 HuR o1_car)); right; split; [exact Hle | exact Hult]).
    exact ((proj2 Hc) H).
  - exfalso.
    assert (Hle : le1 (add1 u o1) a) by (apply (@Nat_P4 RR1 ax1 a u Ha Hu Hgt)).
    assert (Halt : lt1 a (add1 a o1)) by (apply sucN_lt; exact Ha).
    assert (Hc : lt1 (add1 u o1) (add1 a o1))
      by (apply (@Order_Co2 RR1 ax1 (add1 u o1) a (add1 a o1) (@Plus_close RR1 ax1 u o1 HuR o1_car) HaR (@Plus_close RR1 ax1 a o1 HaR o1_car)); right; split; [exact Hle | exact Halt]).
    exact ((proj2 Hc) (eq_sym H)).
  - exact Heq.
Qed.

(* ---------------- SNN 是函数图（存在唯一） ---------------- *)

Lemma SNN_ex : ∀ m, m ∈ N1 -> ∃ n, n ∈ N2 /\ [m,n] ∈ SNN.
Proof.
  intros m Hm.
  set (E := \{ λ x, x ∈ N1 /\ ∃ n, [x,n] ∈ SNN \}).
  assert (Esub : E ⊂ N1) by (intros z Hz; apply AxiomII in Hz as [_ [Hz _]]; exact Hz).
  assert (H1 : o1 ∈ E).
  { apply AxiomII. split.
    - unfold Ensemble. exists car1. exact o1_car.
    - split; [apply (@one_in_N RR1 ax1) | exists o2; exact SNN_11]. }
  assert (Hclos : ∀ x, x ∈ E -> add1 x o1 ∈ E).
  { intros x Hx. apply AxiomII in Hx as [_ [HxN Hn]].
    destruct Hn as [n Hxn].
    apply AxiomII. split.
    - apply Ens_car1. apply (@Plus_close RR1 ax1 x o1 (N1_sub_car1 x HxN) o1_car).
    - split.
      + assert (HIN := @IndSet_N RR1 ax1); unfold IndSet in HIN; exact (proj2 HIN x HxN).
      + exists (add2 n o2). apply SNN_clos; exact Hxn. }
  assert (HE : E = N1) by (apply (@MathInd RR1 ax1 E Esub H1 Hclos)).
  rewrite <- HE in Hm.
  apply AxiomII in Hm as [_ [_ Hn]].
  destruct Hn as [n Hn].
  exists n. split; [exact (SNN_snd m n Hn) | exact Hn].
Qed.

Lemma SNN_uni : ∀ m, m ∈ N1 -> ∀ n1 n2, [m,n1] ∈ SNN -> [m,n2] ∈ SNN -> n1 = n2.
Proof.
  intros m Hm n1 n2 H1 H2.
  set (Wuni := \{ λ x, x ∈ N1 /\ ∀ n1 n2, [x,n1] ∈ SNN -> [x,n2] ∈ SNN -> n1 = n2 \}).
  assert (Hunsub : Wuni ⊂ N1) by (intros z Hz; apply AxiomII in Hz as [_ [Hz _]]; exact Hz).
  assert (Ho1 : o1 ∈ Wuni).
  { apply AxiomII. split.
    - unfold Ensemble. exists car1. exact o1_car.
    - split; [apply (@one_in_N RR1 ax1) |].
      intros a1 a2 Ha1 Ha2.
      set (A' := \{ λ z, z ∈ SNN /\ ∀ y, z = [o1,y] -> y = o2 \}).
      assert (Hsuit : suitN A').
      { unfold suitN. split.
        - intros z Hz. apply AxiomII in Hz as [_ [Hz _]]. apply SNN_sub; exact Hz.
        - split.
          + apply AxiomII. split.
            * apply MKT49a.
              -- unfold Ensemble. exists car1. exact o1_car.
              -- unfold Ensemble. exists car2. exact o2_car.
            * split; [exact SNN_11 |].
              intros y Hy.
              assert (Eo1 : Ensemble o1) by (apply Ens_car1; exact o1_car).
              assert (Eo2 : Ensemble o2) by (apply Ens_car2; exact o2_car).
              exact (eq_sym (proj2 ((proj1 (MKT55 o1 o2 o1 y Eo1 Eo2)) Hy))).
          + intros a b Ha Hab. apply AxiomII in Hab as [_ [HabSN Hcond]].
            assert (HaN : a ∈ N1) by (exact (SNN_fst a b HabSN)).
            assert (HbN : b ∈ N2) by (exact (SNN_snd a b HabSN)).
            apply AxiomII. split.
            * apply MKT49a.
              -- apply Ens_car1. apply (@Plus_close RR1 ax1 a o1 (N1_sub_car1 a HaN) o1_car).
              -- apply Ens_car2. apply (@Plus_close RR2 ax2 b o2 (N2_sub_car2 b HbN) o2_car).
            * split.
              { exact (SNN_clos a b HabSN). }
              { intros y Hy.
                assert (Ea : Ensemble (add1 a o1)) by (apply Ens_car1; apply (@Plus_close RR1 ax1 a o1 (N1_sub_car1 a HaN) o1_car)).
                assert (Eb : Ensemble (add2 b o2)) by (apply Ens_car2; apply (@Plus_close RR2 ax2 b o2 (N2_sub_car2 b HbN) o2_car)).
                assert (Hp : add1 a o1 = o1) by (exact (proj1 ((proj1 (MKT55 (add1 a o1) (add2 b o2) o1 y Ea Eb)) Hy))).
                exact (False_ind _ (sucN_ne_one a HaN Hp)). } }
      assert (HsubA' : SNN ⊂ A').
      { intros z Hz. apply AxiomII in Hz as [_ Hbody]. exact (Hbody A' Hsuit). }
      assert (H11 : [o1,a1] ∈ A') by (apply HsubA'; exact Ha1).
      assert (H12 : [o1,a2] ∈ A') by (apply HsubA'; exact Ha2).
      apply AxiomII in H11 as [_ [_ Hc1]].
      apply AxiomII in H12 as [_ [_ Hc2]].
      rewrite (Hc1 a1 eq_refl). rewrite (Hc2 a2 eq_refl). reflexivity. }
  assert (Hclos : ∀ u, u ∈ Wuni -> add1 u o1 ∈ Wuni).
  { intros u Hu. apply AxiomII in Hu as [_ [HuN Huniqx]].
    destruct (SNN_ex u HuN) as [y0 [Hy0N Hy0SN]].
    apply AxiomII. split.
    - apply Ens_car1. apply (@Plus_close RR1 ax1 u o1 (N1_sub_car1 u HuN) o1_car).
    - split.
      + assert (HIN := @IndSet_N RR1 ax1); unfold IndSet in HIN; exact (proj2 HIN u HuN).
      + intros b1 b2 Hb1 Hb2.
        set (A' := \{ λ z, z ∈ SNN /\ ∀ y, z = [add1 u o1, y] -> y = add2 y0 o2 \}).
        assert (Hsuit : suitN A').
        { unfold suitN. split.
          - intros z Hz. apply AxiomII in Hz as [_ [Hz _]]. apply SNN_sub; exact Hz.
          - split.
            + apply AxiomII. split.
              * apply MKT49a.
                -- unfold Ensemble. exists car1. exact o1_car.
                -- unfold Ensemble. exists car2. exact o2_car.
              * split; [exact SNN_11 |].
                intros y Hy. exfalso.
                assert (Eo1 : Ensemble o1) by (apply Ens_car1; exact o1_car).
                assert (Eo2 : Ensemble o2) by (apply Ens_car2; exact o2_car).
                assert (Hp : o1 = add1 u o1) by (exact (proj1 ((proj1 (MKT55 o1 o2 (add1 u o1) y Eo1 Eo2)) Hy))).
                exact (sucN_ne_one u HuN (eq_sym Hp)).
            + intros a b Ha Hab. apply AxiomII in Hab as [_ [HabSN Hcond]].
              assert (HaN : a ∈ N1) by (exact (SNN_fst a b HabSN)).
              assert (HbN : b ∈ N2) by (exact (SNN_snd a b HabSN)).
              apply AxiomII. split.
              * apply MKT49a.
                -- apply Ens_car1. apply (@Plus_close RR1 ax1 a o1 (N1_sub_car1 a HaN) o1_car).
                -- apply Ens_car2. apply (@Plus_close RR2 ax2 b o2 (N2_sub_car2 b HbN) o2_car).
              * split.
                { exact (SNN_clos a b HabSN). }
                { intros y Hy.
                  assert (Ea : Ensemble (add1 a o1)) by (apply Ens_car1; apply (@Plus_close RR1 ax1 a o1 (N1_sub_car1 a HaN) o1_car)).
                  assert (Eb : Ensemble (add2 b o2)) by (apply Ens_car2; apply (@Plus_close RR2 ax2 b o2 (N2_sub_car2 b HbN) o2_car)).
                  assert (Hpa : add1 a o1 = add1 u o1) by (exact (proj1 ((proj1 (MKT55 (add1 a o1) (add2 b o2) (add1 u o1) y Ea Eb)) Hy))).
                  assert (Hbr : add2 b o2 = y) by (exact (proj2 ((proj1 (MKT55 (add1 a o1) (add2 b o2) (add1 u o1) y Ea Eb)) Hy))).
                  assert (Hau : a = u) by (apply (sucN_inj a u HaN HuN); exact Hpa).
                  assert (Hub : [u,b] ∈ SNN) by (rewrite <- Hau; exact HabSN).
                  assert (Hby0 : b = y0) by (exact (Huniqx b y0 Hub Hy0SN)).
                  rewrite <- Hbr. rewrite Hby0. reflexivity. } }
        assert (HsubA' : SNN ⊂ A').
        { intros z Hz. apply AxiomII in Hz as [_ Hbody]. exact (Hbody A' Hsuit). }
        assert (H11 : [add1 u o1, b1] ∈ A') by (apply HsubA'; exact Hb1).
        assert (H12 : [add1 u o1, b2] ∈ A') by (apply HsubA'; exact Hb2).
        apply AxiomII in H11 as [_ [_ Hc1]].
        apply AxiomII in H12 as [_ [_ Hc2]].
        rewrite (Hc1 b1 eq_refl). rewrite (Hc2 b2 eq_refl). reflexivity. }
  assert (HE : Wuni = N1) by (apply (@MathInd RR1 ax1 Wuni Hunsub Ho1 Hclos)).
  assert (HmW : m ∈ Wuni) by (rewrite HE; exact Hm).
  apply AxiomII in HmW as [_ [_ Huniq]].
  exact (Huniq n1 n2 H1 H2).
Qed.

(* ---------------- sigN : N1 -> N2 ---------------- *)

Definition sigN (x:Class) : Class := SNN[x].

Lemma sigN_val : ∀ m, m ∈ N1 -> [m, sigN m] ∈ SNN.
Proof.
  intros m Hm.
  destruct (SNN_ex m Hm) as [n0 [Hn0 Hn0SN]].
  assert (Hset : \{ λ z, [m,z] ∈ SNN \} = [n0]).
  { apply AxiomI. intros z. split.
    - intros Hz. apply AxiomII in Hz as [Ez HzS].
      apply AxiomII. split; [exact Ez |].
      intros _. exact (SNN_uni m Hm z n0 HzS Hn0SN).
    - intros Hz. apply AxiomII in Hz as [Ez Hzn0].
      assert (Hn0mu : n0 ∈ μ) by (apply MKT19b; exact (Ens_car2 n0 (N2_sub_car2 n0 Hn0))).
      assert (Hzn : z = n0) by (apply Hzn0; exact Hn0mu).
      subst z. apply AxiomII. split; [exact Ez | exact Hn0SN]. }
  assert (Hsig : sigN m = n0).
  { unfold sigN. unfold Value. rewrite Hset. exact (proj1 (MKT44 (Ens_car2 n0 (N2_sub_car2 n0 Hn0)))). }
  rewrite Hsig. exact Hn0SN.
Qed.

Lemma sigN_N2 : ∀ m, m ∈ N1 -> sigN m ∈ N2.
Proof.
  intros m Hm. exact (SNN_snd m (sigN m) (sigN_val m Hm)).
Qed.

Lemma sigN_one : sigN o1 = o2.
Proof.
  assert (Hset : \{ λ z, [o1,z] ∈ SNN \} = [o2]).
  { apply AxiomI. intros z. split.
    - intros Hz. apply AxiomII in Hz as [Ez HzS].
      apply AxiomII. split; [exact Ez |].
      intros _. exact (SNN_uni o1 (@one_in_N RR1 ax1) z o2 HzS SNN_11).
    - intros Hz. apply AxiomII in Hz as [Ez Hz2].
      assert (Ho2mu : o2 ∈ μ) by (apply MKT19b; apply Ens_car2; exact o2_car).
      assert (Hzz : z = o2) by (apply Hz2; exact Ho2mu).
      subst z. apply AxiomII. split; [exact Ez | exact SNN_11]. }
  unfold sigN. unfold Value. rewrite Hset. exact (proj1 (MKT44 (Ens_car2 o2 o2_car))).
Qed.

Lemma sigN_succ : ∀ m, m ∈ N1 -> sigN (add1 m o1) = add2 (sigN m) o2.
Proof.
  intros m Hm.
  assert (Hm1N : add1 m o1 ∈ N1) by (assert (HIN := @IndSet_N RR1 ax1); unfold IndSet in HIN; exact (proj2 HIN m Hm)).
  assert (Hv : [add1 m o1, add2 (sigN m) o2] ∈ SNN) by (apply SNN_clos; apply sigN_val; exact Hm).
  destruct (SNN_ex (add1 m o1) Hm1N) as [y [Ey Hy]].
  assert (Heqset : \{ λ z, [add1 m o1,z] ∈ SNN \} = [y]).
  { apply AxiomI. intros z. split.
    - intros Hz. apply AxiomII in Hz as [Ez HzS].
      apply AxiomII. split; [exact Ez |].
      intros _. exact (SNN_uni (add1 m o1) Hm1N z y HzS Hy).
    - intros Hz. apply AxiomII in Hz as [Ez Hzy].
      assert (Eymu : y ∈ μ) by (apply MKT19b; exact (Ens_car2 y (N2_sub_car2 y Ey))).
      assert (Hzy' : z = y) by (apply Hzy; exact Eymu).
      subst z. apply AxiomII. split; [exact Ez | exact Hy]. }
  assert (Hpv : sigN (add1 m o1) = y).
  { unfold sigN. unfold Value. rewrite Heqset. exact (proj1 (MKT44 (Ens_car2 y (N2_sub_car2 y Ey)))). }
  assert (Hvy : y = add2 (sigN m) o2) by (exact (SNN_uni (add1 m o1) Hm1N y (add2 (sigN m) o2) Hy Hv)).
  rewrite Hpv. exact Hvy.
Qed.

(* ---------------- sigN 保加法与乘法 ---------------- *)

Lemma sigN_add : ∀ m n, m ∈ N1 -> n ∈ N1 -> sigN (add1 m n) = add2 (sigN m) (sigN n).
Proof.
  intros m n Hm Hn.
  set (E := \{ λ x, x ∈ N1 /\ sigN (add1 m x) = add2 (sigN m) (sigN x) \}).
  assert (Esub : E ⊂ N1) by (intros z Hz; apply AxiomII in Hz as [_ [Hz _]]; exact Hz).
  assert (H1 : o1 ∈ E).
  { apply AxiomII. split.
    - unfold Ensemble. exists car1. exact o1_car.
    - split; [apply (@one_in_N RR1 ax1) |].
      rewrite sigN_one. exact (sigN_succ m Hm). }
  assert (Hclos : ∀ x, x ∈ E -> add1 x o1 ∈ E).
  { intros x Hx. apply AxiomII in Hx as [_ [HxN Hxeq]].
    assert (HxR : x ∈ car1) by (apply N1_sub_car1; exact HxN).
    assert (HmxN : add1 m x ∈ N1) by (apply (@Nat_P1a RR1 ax1 m x Hm HxN)).
    assert (Hx1N : add1 x o1 ∈ N1) by (assert (HIN := @IndSet_N RR1 ax1); unfold IndSet in HIN; exact (proj2 HIN x HxN)).
    apply AxiomII. split.
    - apply Ens_car1. apply (@Plus_close RR1 ax1 x o1 HxR o1_car).
    - split; [exact Hx1N |].
      assert (Hassoc : add1 m (add1 x o1) = add1 (add1 m x) o1)
        by (apply (@Plus_P3 RR1 ax1 m x o1 (N1_sub_car1 m Hm) HxR o1_car)).
      rewrite Hassoc.
      rewrite (sigN_succ (add1 m x) HmxN).
      rewrite Hxeq.
      rewrite (sigN_succ x HxN).
      exact (eq_sym (@Plus_P3 RR2 ax2 (sigN m) (sigN x) o2 (N2_sub_car2 (sigN m) (sigN_N2 m Hm)) (N2_sub_car2 (sigN x) (sigN_N2 x HxN)) o2_car)). }
  assert (HE : E = N1) by (apply (@MathInd RR1 ax1 E Esub H1 Hclos)).
  assert (HnE : n ∈ E) by (rewrite HE; exact Hn).
  apply AxiomII in HnE as [_ [_ Hn']].
  exact Hn'.
Qed.

Lemma sigN_mul : ∀ m n, m ∈ N1 -> n ∈ N1 -> sigN (mul1 m n) = mul2 (sigN m) (sigN n).
Proof.
  intros m n Hm Hn.
  set (E := \{ λ x, x ∈ N1 /\ sigN (mul1 m x) = mul2 (sigN m) (sigN x) \}).
  assert (Esub : E ⊂ N1) by (intros z Hz; apply AxiomII in Hz as [_ [Hz _]]; exact Hz).
  assert (H1 : o1 ∈ E).
  { apply AxiomII. split.
    - unfold Ensemble. exists car1. exact o1_car.
    - split; [apply (@one_in_N RR1 ax1) |].
      assert (Hmm1 : mul1 m o1 = m) by (apply (@Mult_P1 RR1 ax1 m (N1_sub_car1 m Hm))).
      rewrite Hmm1.
      rewrite sigN_one.
      exact (eq_sym (@Mult_P1 RR2 ax2 (sigN m) (N2_sub_car2 (sigN m) (sigN_N2 m Hm)))). }
  assert (Hclos : ∀ x, x ∈ E -> add1 x o1 ∈ E).
  { intros x Hx. apply AxiomII in Hx as [_ [HxN Hxeq]].
    assert (HxR : x ∈ car1) by (apply N1_sub_car1; exact HxN).
    assert (HmxN : mul1 m x ∈ N1) by (apply (@Nat_P1b RR1 ax1 m x Hm HxN)).
    assert (Hx1N : add1 x o1 ∈ N1) by (assert (HIN := @IndSet_N RR1 ax1); unfold IndSet in HIN; exact (proj2 HIN x HxN)).
    apply AxiomII. split.
    - apply Ens_car1. apply (@Plus_close RR1 ax1 x o1 HxR o1_car).
    - split; [exact Hx1N |].
      assert (Hmulstep : mul1 m (add1 x o1) = add1 (mul1 m x) m).
      { transitivity (mul1 (add1 x o1) m).
        - apply (@Mult_P4 RR1 ax1 m (add1 x o1) (N1_sub_car1 m Hm) (@Plus_close RR1 ax1 x o1 HxR o1_car)).
        - transitivity (add1 (mul1 x m) (mul1 o1 m)).
          + apply (@Mult_P5 RR1 ax1 x o1 m HxR o1_car (N1_sub_car1 m Hm)).
          + assert (Hcm : mul1 o1 m = m) by (apply (eq_trans (@Mult_P4 RR1 ax1 o1 m o1_car (N1_sub_car1 m Hm)) (@Mult_P1 RR1 ax1 m (N1_sub_car1 m Hm)))).
            assert (Hcx : mul1 x m = mul1 m x) by (apply (@Mult_P4 RR1 ax1 x m HxR (N1_sub_car1 m Hm))).
            rewrite Hcm. rewrite Hcx. reflexivity. }
      rewrite Hmulstep.
      rewrite (sigN_add (mul1 m x) m HmxN Hm).
      rewrite Hxeq.
      rewrite (sigN_succ x HxN).
      assert (Hdistr : mul2 (sigN m) (add2 (sigN x) o2) = add2 (mul2 (sigN m) (sigN x)) (sigN m)).
      { transitivity (mul2 (add2 (sigN x) o2) (sigN m)).
        - apply (@Mult_P4 RR2 ax2 (sigN m) (add2 (sigN x) o2) (N2_sub_car2 (sigN m) (sigN_N2 m Hm)) (@Plus_close RR2 ax2 (sigN x) o2 (N2_sub_car2 (sigN x) (sigN_N2 x HxN)) o2_car)).
        - transitivity (add2 (mul2 (sigN x) (sigN m)) (mul2 o2 (sigN m))).
          + apply (@Mult_P5 RR2 ax2 (sigN x) o2 (sigN m) (N2_sub_car2 (sigN x) (sigN_N2 x HxN)) o2_car (N2_sub_car2 (sigN m) (sigN_N2 m Hm))).
          + assert (Hcm2 : mul2 o2 (sigN m) = sigN m) by (apply (eq_trans (@Mult_P4 RR2 ax2 o2 (sigN m) o2_car (N2_sub_car2 (sigN m) (sigN_N2 m Hm))) (@Mult_P1 RR2 ax2 (sigN m) (N2_sub_car2 (sigN m) (sigN_N2 m Hm))))).
            assert (Hcx2 : mul2 (sigN x) (sigN m) = mul2 (sigN m) (sigN x)) by (apply (@Mult_P4 RR2 ax2 (sigN x) (sigN m) (N2_sub_car2 (sigN x) (sigN_N2 x HxN)) (N2_sub_car2 (sigN m) (sigN_N2 m Hm)))).
            rewrite Hcm2. rewrite Hcx2. reflexivity. }
      rewrite Hdistr. reflexivity. }
  assert (HE : E = N1) by (apply (@MathInd RR1 ax1 E Esub H1 Hclos)).
  assert (HnE : n ∈ E) by (rewrite HE; exact Hn).
  apply AxiomII in HnE as [_ [_ Hn']].
  exact Hn'.
Qed.

Lemma sigN_lt : ∀ n, n ∈ N1 -> ∀ m, m ∈ N1 -> lt1 m n -> lt2 (sigN m) (sigN n).
Proof.
  set (W := \{ λ n, n ∈ N1 /\ ∀ m, m ∈ N1 -> lt1 m n -> lt2 (sigN m) (sigN n) \}).
  assert (Wsub : W ⊂ N1) by (intros z Hz; apply AxiomII in Hz as [_ [Hz _]]; exact Hz).
  assert (Ho1 : o1 ∈ W).
  { apply AxiomII. split.
    - unfold Ensemble. exists car1. exact o1_car.
    - split; [apply (@one_in_N RR1 ax1) |].
      intros m Hm Hlt.
      assert (Hle : le1 o1 m) by (exact (proj2 (proj2 (@one_is_min_in_N RR1 ax1)) m Hm)).
      exact (False_ind _ ((proj2 Hlt) (@Leq_P2 RR1 ax1 m o1 (N1_sub_car1 m Hm) o1_car (proj1 Hlt) Hle))). }
  assert (Wclos : ∀ n, n ∈ W -> add1 n o1 ∈ W).
  { intros n Hn. apply AxiomII in Hn as [_ [HnN IH]].
    assert (HnR : n ∈ car1) by (apply N1_sub_car1; exact HnN).
    assert (Hn1N : add1 n o1 ∈ N1) by (assert (HIN := @IndSet_N RR1 ax1); unfold IndSet in HIN; exact (proj2 HIN n HnN)).
    apply AxiomII. split.
    - apply Ens_car1. apply (@Plus_close RR1 ax1 n o1 HnR o1_car).
    - split; [exact Hn1N |].
      intros m Hm Hlt.
      assert (HmR : m ∈ car1) by (apply N1_sub_car1; exact Hm).
      assert (H2 : lt2 (sigN n) (sigN (add1 n o1))).
      { rewrite (sigN_succ n HnN). apply lt_add_one2. apply (N2_sub_car2 (sigN n) (sigN_N2 n HnN)). }
      destruct (@Order_Co1 RR1 ax1 m n HmR HnR) as [Hltmn | [Hgtmn | Heqmn]].
      + assert (H1 : lt2 (sigN m) (sigN n)) by (exact (IH m Hm Hltmn)).
        apply (@Order_Co2 RR2 ax2 (sigN m) (sigN n) (sigN (add1 n o1)) (N2_sub_car2 (sigN m) (sigN_N2 m Hm)) (N2_sub_car2 (sigN n) (sigN_N2 n HnN)) (N2_sub_car2 (sigN (add1 n o1)) (sigN_N2 (add1 n o1) Hn1N))).
        left. split; [exact H1 | exact (proj1 H2)].
      + assert (Hle : le1 (add1 n o1) m) by (apply (@Nat_P4 RR1 ax1 m n Hm HnN Hgtmn)).
        assert (Hc : lt1 (add1 n o1) (add1 n o1))
          by (apply (@Order_Co2 RR1 ax1 (add1 n o1) m (add1 n o1) (@Plus_close RR1 ax1 n o1 HnR o1_car) HmR (@Plus_close RR1 ax1 n o1 HnR o1_car)); right; split; [exact Hle | exact Hlt]).
        exact (False_ind _ ((proj2 Hc) eq_refl)).
      + rewrite Heqmn. exact H2. }
  assert (HW : W = N1) by (apply (@MathInd RR1 ax1 W Wsub Ho1 Wclos)).
  intros n Hn m Hm Hlt.
  assert (HnW : n ∈ W) by (rewrite HW; exact Hn).
  apply AxiomII in HnW as [_ [_ Hmm]]. exact (Hmm m Hm Hlt).
Qed.

Lemma sigN_inj : ∀ m n, m ∈ N1 -> n ∈ N1 -> sigN m = sigN n -> m = n.
Proof.
  intros m n Hm Hn Heq.
  destruct (@Order_Co1 RR1 ax1 m n (N1_sub_car1 m Hm) (N1_sub_car1 n Hn)) as [Hlt | [Hgt | Heq2]].
  - exfalso. assert (H1 : lt2 (sigN m) (sigN n)) by (apply (sigN_lt n Hn m Hm Hlt)).
    exact ((proj2 H1) Heq).
  - exfalso. assert (H1 : lt2 (sigN n) (sigN m)) by (apply (sigN_lt m Hm n Hn Hgt)).
    exact ((proj2 H1) (eq_sym Heq)).
  - exact Heq2.
Qed.

(* ---------------- 整数：相反数基本引理 ---------------- *)

Definition neg1 (x:Class) : Class := ∩(\{ λ u, u ∈ car1 /\ add1 u x = z1 \}).
Definition neg2 (x:Class) : Class := ∩(\{ λ u, u ∈ car2 /\ add2 u x = z2 \}).

Lemma neg1_car : ∀ x, x ∈ car1 -> neg1 x ∈ car1.
Proof. intros x Hx. apply (@Plus_neg1a RR1 ax1 x Hx). Qed.
Lemma neg1_back : ∀ x, neg1 x ∈ car1 -> x ∈ car1.
Proof. intros x Hx. apply (@Plus_neg1b RR1 ax1 x Hx). Qed.
Lemma neg2_car : ∀ x, x ∈ car2 -> neg2 x ∈ car2.
Proof. intros x Hx. apply (@Plus_neg1a RR2 ax2 x Hx). Qed.
Lemma neg2_back : ∀ x, neg2 x ∈ car2 -> x ∈ car2.
Proof. intros x Hx. apply (@Plus_neg1b RR2 ax2 x Hx). Qed.

Lemma neg1_add : ∀ a, a ∈ car1 -> add1 (neg1 a) a = z1.
Proof. intros a Ha. apply (eq_trans (@Plus_P4 RR1 ax1 (neg1 a) a (neg1_car a Ha) Ha) (@Plus_neg2 RR1 ax1 a Ha)). Qed.
Lemma neg2_add : ∀ a, a ∈ car2 -> add2 (neg2 a) a = z2.
Proof. intros a Ha. apply (eq_trans (@Plus_P4 RR2 ax2 (neg2 a) a (neg2_car a Ha) Ha) (@Plus_neg2 RR2 ax2 a Ha)). Qed.

Lemma N1_in_Z1 : ∀ z, z ∈ N1 -> z ∈ Z1.
Proof. intros z Hz. unfold Z1, Z. apply MKT4. left. exact Hz. Qed.
Lemma N2_in_Z2 : ∀ z, z ∈ N2 -> z ∈ Z2.
Proof. intros z Hz. unfold Z2, Z. apply MKT4. left. exact Hz. Qed.

Lemma Z1_zero : z1 ∈ Z1.
Proof.
  unfold Z1, Z. apply MKT4. right. apply MKT4. right.
  apply (proj2 (MKT41 z1 (Ens_car1 z1 z1_car) z1) eq_refl).
Qed.
Lemma Z2_zero : z2 ∈ Z2.
Proof.
  unfold Z2, Z. apply MKT4. right. apply MKT4. right.
  apply (proj2 (MKT41 z2 (Ens_car2 z2 z2_car) z2) eq_refl).
Qed.

Lemma Z1_neg : ∀ z, z ∈ Z1 -> neg1 z ∈ Z1.
Proof. intros z Hz. exact (proj1 (@Int_P3 RR1 ax1 z Hz)). Qed.
Lemma Z2_neg : ∀ z, z ∈ Z2 -> neg2 z ∈ Z2.
Proof. intros z Hz. exact (proj1 (@Int_P3 RR2 ax2 z Hz)). Qed.

(* ---------------- 整数的三分解 ---------------- *)

Lemma neg1_z1 : neg1 z1 = z1.
Proof.
  assert (Hsum : add1 z1 (neg1 z1) = z1)
    by (apply (eq_trans (@Plus_P4 RR1 ax1 z1 (neg1 z1) z1_car (neg1_car z1 z1_car)) (neg1_add z1 z1_car))).
  assert (Hres : neg1 z1 = add1 z1 (neg1 z1))
    by (apply (@Plus_Co3 RR1 ax1 z1 (neg1 z1) z1 z1_car (neg1_car z1 z1_car) z1_car Hsum)).
  rewrite Hsum in Hres. exact Hres.
Qed.

Lemma Z1_cases : ∀ z, z ∈ Z1 -> z ∈ N1 \/ neg1 z ∈ N1 \/ z = z1.
Proof.
  intros z Hz. unfold Z1, Z in Hz.
  apply MKT4 in Hz as [HzN | HzRest].
  - left. exact HzN.
  - apply MKT4 in HzRest as [HzB | Hz0].
    + right. left. apply AxiomII in HzB as [_ Hneg]. exact Hneg.
    + right. right.
      exact (proj1 (MKT41 z1 (Ens_car1 z1 z1_car) z) Hz0).
Qed.

Lemma posN_negN_absurd : ∀ z, z ∈ N1 -> neg1 z ∈ N1 -> False.
Proof.
  intros z Hz Hzneg.
  assert (HzR : z ∈ car1) by (apply N1_sub_car1; exact Hz).
  assert (HnR : neg1 z ∈ car1) by (apply N1_sub_car1; exact Hzneg).
  assert (H1z : le1 o1 z) by (exact (proj2 (proj2 (@one_is_min_in_N RR1 ax1)) z Hz)).
  assert (H1n : le1 o1 (neg1 z)) by (exact (proj2 (proj2 (@one_is_min_in_N RR1 ax1)) (neg1 z) Hzneg)).
  assert (Hle : le1 (add1 o1 o1) (add1 z (neg1 z))) by (apply (@OrderPM_Co3 RR1 ax1 o1 z o1 (neg1 z) o1_car HzR o1_car HnR H1z H1n)).
  assert (Hsum : add1 z (neg1 z) = z1) by (apply (eq_trans (@Plus_P4 RR1 ax1 z (neg1 z) HzR HnR) (neg1_add z HzR))).
  rewrite Hsum in Hle.
  assert (H12 : lt1 o1 (add1 o1 o1)).
  { assert (Ht : lt1 (add1 z1 o1) (add1 o1 o1)) by (apply (@OrderPM_Co1 RR1 ax1 z1 o1 o1 z1_car o1_car o1_car); exact (@OrderPM_Co9 RR1 ax1)).
    assert (He : add1 z1 o1 = o1) by (apply (eq_trans (@Plus_P4 RR1 ax1 z1 o1 z1_car o1_car) (@Plus_P1 RR1 ax1 o1 o1_car))).
    rewrite He in Ht. exact Ht. }
  assert (H20 : lt1 z1 (add1 o1 o1))
    by (apply (@Order_Co2 RR1 ax1 z1 o1 (add1 o1 o1) z1_car o1_car (@Plus_close RR1 ax1 o1 o1 o1_car o1_car)); left; split; [exact (@OrderPM_Co9 RR1 ax1) | exact (proj1 H12)]).
  exact ((proj2 H20) (eq_sym (@Leq_P2 RR1 ax1 (add1 o1 o1) z1 (@Plus_close RR1 ax1 o1 o1 o1_car o1_car) z1_car Hle (proj1 H20)))).
Qed.

(* ---------------- sigZ 的定义与基本取值 ---------------- *)

Definition sigZcand (z:Class) : Class :=
  \{ λ w, (z ∈ N1 /\ w = sigN z)
       \/ (z ∉ N1 /\ neg1 z ∈ N1 /\ w = neg2 (sigN (neg1 z)))
       \/ (z ∉ N1 /\ neg1 z ∉ N1 /\ w = z2) \}.

Definition sigZ (z:Class) : Class := ∩(sigZcand z).

Lemma sigZ_eq_N : ∀ z, z ∈ N1 -> sigZ z = sigN z.
Proof.
  intros z Hz.
  assert (Hsig : sigN z ∈ N2) by (apply sigN_N2; exact Hz).
  assert (Esig : Ensemble (sigN z)) by (apply Ens_car2; apply N2_sub_car2; exact Hsig).
  assert (Hset : sigZcand z = [sigN z]).
  { apply AxiomI. intros w. split.
    - intros Hw. apply AxiomII in Hw as [_ Hw'].
      destruct Hw' as [[HzN Hw1] | [[Hzn [Hzneg Hw2]] | [Hzn2 [Hzneg2 Hw3]]]].
      + exact (proj2 (MKT41 (sigN z) Esig w) Hw1).
      + exfalso. exact (Hzn Hz).
      + exfalso. exact (Hzn2 Hz).
    - intros Hw. assert (HwEq : w = sigN z) by (exact (proj1 (MKT41 (sigN z) Esig w) Hw)).
      apply AxiomII in Hw as [Ew _].
      apply AxiomII. split.
      + exact Ew.
      + left. split; [exact Hz | exact HwEq]. }
  unfold sigZ. rewrite Hset. exact (proj1 (MKT44 Esig)).
Qed.

Lemma sigZ_eq_neg : ∀ z, neg1 z ∈ N1 -> z ∉ N1 -> sigZ z = neg2 (sigN (neg1 z)).
Proof.
  intros z Hzneg Hzn.
  assert (Hsig : sigN (neg1 z) ∈ N2) by (apply sigN_N2; exact Hzneg).
  assert (Ea : Ensemble (neg2 (sigN (neg1 z))))
    by (apply Ens_car2; apply neg2_car; apply N2_sub_car2; exact Hsig).
  assert (Hset : sigZcand z = [neg2 (sigN (neg1 z))]).
  { apply AxiomI. intros w. split.
    - intros Hw. apply AxiomII in Hw as [_ Hw'].
      destruct Hw' as [[HzN _] | [[_ [Hzneg2 Hw2]] | [_ [Hzneg3 Hw3]]]].
      + exfalso. exact (Hzn HzN).
      + exact (proj2 (MKT41 (neg2 (sigN (neg1 z))) Ea w) Hw2).
      + exfalso. exact (Hzneg3 Hzneg).
    - intros Hw. assert (HwEq : w = neg2 (sigN (neg1 z))) by (exact (proj1 (MKT41 (neg2 (sigN (neg1 z))) Ea w) Hw)).
      apply AxiomII in Hw as [Ew _].
      apply AxiomII. split.
      + exact Ew.
      + right. left. split; [exact Hzn | split; [exact Hzneg | exact HwEq]]. }
  unfold sigZ. rewrite Hset. exact (proj1 (MKT44 Ea)).
Qed.

Lemma sigZ_eq_zero : ∀ z, z ∉ N1 -> neg1 z ∉ N1 -> sigZ z = z2.
Proof.
  intros z Hzn Hzneg.
  assert (Ez2 : Ensemble z2) by (apply Ens_car2; exact z2_car).
  assert (Hset : sigZcand z = [z2]).
  { apply AxiomI. intros w. split.
    - intros Hw. apply AxiomII in Hw as [_ Hw'].
      destruct Hw' as [[HzN _] | [[_ [Hzneg2 _]] | [_ [Hzneg3 Hw3]]]].
      + exfalso. exact (Hzn HzN).
      + exfalso. exact (Hzneg Hzneg2).
      + exact (proj2 (MKT41 z2 Ez2 w) Hw3).
    - intros Hw. assert (HwEq : w = z2) by (exact (proj1 (MKT41 z2 Ez2 w) Hw)).
      apply AxiomII in Hw as [Ew _].
      apply AxiomII. split.
      + exact Ew.
      + right. right. split; [exact Hzn | split; [exact Hzneg | exact HwEq]]. }
  unfold sigZ. rewrite Hset. exact (proj1 (MKT44 Ez2)).
Qed.

Lemma sigZ_Z2 : ∀ z, z ∈ Z1 -> sigZ z ∈ Z2.
Proof.
  intros z HzZ.
  destruct (Z1_cases z HzZ) as [HzN | [Hzneg | Hz0]].
  - rewrite (sigZ_eq_N z HzN). apply N2_in_Z2. apply sigN_N2. exact HzN.
  - assert (Hzn : z ∉ N1) by (intro H; exact (posN_negN_absurd z H Hzneg)).
    rewrite (sigZ_eq_neg z Hzneg Hzn).
    apply Z2_neg. apply N2_in_Z2. apply sigN_N2. exact Hzneg.
  - subst z.
    assert (Hzn : z1 ∉ N1) by (exact (@zero_not_in_N RR1 ax1)).
    assert (Hneg : neg1 z1 ∉ N1) by (rewrite neg1_z1; exact (@zero_not_in_N RR1 ax1)).
    rewrite (sigZ_eq_zero z1 Hzn Hneg). exact Z2_zero.
Qed.

Lemma sigZ_zero : sigZ z1 = z2.
Proof.
  apply sigZ_eq_zero.
  - exact (@zero_not_in_N RR1 ax1).
  - rewrite neg1_z1. exact (@zero_not_in_N RR1 ax1).
Qed.

Lemma sigZ_one : sigZ o1 = o2.
Proof. rewrite (sigZ_eq_N o1 (@one_in_N RR1 ax1)). apply sigN_one. Qed.

(* ---------------- 相反数的对合与加法 ---------------- *)

Lemma neg1_invol : ∀ x, x ∈ car1 -> neg1 (neg1 x) = x.
Proof.
  intros x Hx.
  assert (HnR : neg1 x ∈ car1) by (apply neg1_car; exact Hx).
  assert (Hsum : add1 (neg1 x) x = z1) by (apply neg1_add; exact Hx).
  assert (Hres : x = add1 z1 (neg1 (neg1 x))) by (apply (@Plus_Co3 RR1 ax1 (neg1 x) x z1 HnR Hx z1_car Hsum)).
  assert (H0 : add1 z1 (neg1 (neg1 x)) = neg1 (neg1 x))
    by (apply (eq_trans (@Plus_P4 RR1 ax1 z1 (neg1 (neg1 x)) z1_car (neg1_car (neg1 x) HnR)) (@Plus_P1 RR1 ax1 (neg1 (neg1 x)) (neg1_car (neg1 x) HnR)))).
  rewrite H0 in Hres. symmetry. exact Hres.
Qed.

Lemma neg2_invol : ∀ x, x ∈ car2 -> neg2 (neg2 x) = x.
Proof.
  intros x Hx.
  assert (HnR : neg2 x ∈ car2) by (apply neg2_car; exact Hx).
  assert (Hsum : add2 (neg2 x) x = z2) by (apply neg2_add; exact Hx).
  assert (Hres : x = add2 z2 (neg2 (neg2 x))) by (apply (@Plus_Co3 RR2 ax2 (neg2 x) x z2 HnR Hx z2_car Hsum)).
  assert (H0 : add2 z2 (neg2 (neg2 x)) = neg2 (neg2 x))
    by (apply (eq_trans (@Plus_P4 RR2 ax2 z2 (neg2 (neg2 x)) z2_car (neg2_car (neg2 x) HnR)) (@Plus_P1 RR2 ax2 (neg2 (neg2 x)) (neg2_car (neg2 x) HnR)))).
  rewrite H0 in Hres. symmetry. exact Hres.
Qed.

Lemma neg_add1 : ∀ a b, a ∈ car1 -> b ∈ car1 -> neg1 (add1 a b) = add1 (neg1 a) (neg1 b).
Proof.
  intros a b Ha Hb.
  assert (Hna : neg1 a ∈ car1) by (apply neg1_car; exact Ha).
  assert (Hnb : neg1 b ∈ car1) by (apply neg1_car; exact Hb).
  assert (Hab : add1 a b ∈ car1) by (apply (@Plus_close RR1 ax1 a b Ha Hb)).
  assert (Habna : add1 (add1 a b) (neg1 a) ∈ car1) by (apply (@Plus_close RR1 ax1 (add1 a b) (neg1 a) Hab Hna)).
  assert (Hnab : add1 (neg1 a) (neg1 b) ∈ car1) by (apply (@Plus_close RR1 ax1 (neg1 a) (neg1 b) Hna Hnb)).
  assert (Hmid : add1 (add1 a b) (neg1 a) = b).
  { transitivity (add1 (add1 b a) (neg1 a)).
    - assert (Hc : add1 a b = add1 b a) by (apply (@Plus_P4 RR1 ax1 a b Ha Hb)).
      rewrite Hc. reflexivity.
    - transitivity (add1 b (add1 a (neg1 a))).
      + symmetry. apply (@Plus_P3 RR1 ax1 b a (neg1 a) Hb Ha Hna).
      + assert (Hc2 : add1 a (neg1 a) = z1) by (apply (@Plus_neg2 RR1 ax1 a Ha)).
        rewrite Hc2. apply (@Plus_P1 RR1 ax1 b Hb). }
  assert (Hsum : add1 (add1 a b) (add1 (neg1 a) (neg1 b)) = z1).
  { transitivity (add1 (add1 (add1 a b) (neg1 a)) (neg1 b)).
    - apply (@Plus_P3 RR1 ax1 (add1 a b) (neg1 a) (neg1 b) Hab Hna Hnb).
    - rewrite Hmid. apply (@Plus_neg2 RR1 ax1 b Hb). }
  assert (Hres : add1 (neg1 a) (neg1 b) = add1 z1 (neg1 (add1 a b)))
    by (apply (@Plus_Co3 RR1 ax1 (add1 a b) (add1 (neg1 a) (neg1 b)) z1 Hab Hnab z1_car Hsum)).
  assert (Hf : add1 z1 (neg1 (add1 a b)) = neg1 (add1 a b))
    by (apply (eq_trans (@Plus_P4 RR1 ax1 z1 (neg1 (add1 a b)) z1_car (neg1_car (add1 a b) Hab)) (@Plus_P1 RR1 ax1 (neg1 (add1 a b)) (neg1_car (add1 a b) Hab)))).
  rewrite Hf in Hres. symmetry. exact Hres.
Qed.

Lemma neg_add2 : ∀ a b, a ∈ car2 -> b ∈ car2 -> neg2 (add2 a b) = add2 (neg2 a) (neg2 b).
Proof.
  intros a b Ha Hb.
  assert (Hna : neg2 a ∈ car2) by (apply neg2_car; exact Ha).
  assert (Hnb : neg2 b ∈ car2) by (apply neg2_car; exact Hb).
  assert (Hab : add2 a b ∈ car2) by (apply (@Plus_close RR2 ax2 a b Ha Hb)).
  assert (Hnab : add2 (neg2 a) (neg2 b) ∈ car2) by (apply (@Plus_close RR2 ax2 (neg2 a) (neg2 b) Hna Hnb)).
  assert (Hmid : add2 (add2 a b) (neg2 a) = b).
  { transitivity (add2 (add2 b a) (neg2 a)).
    - assert (Hc : add2 a b = add2 b a) by (apply (@Plus_P4 RR2 ax2 a b Ha Hb)).
      rewrite Hc. reflexivity.
    - transitivity (add2 b (add2 a (neg2 a))).
      + symmetry. apply (@Plus_P3 RR2 ax2 b a (neg2 a) Hb Ha Hna).
      + assert (Hc2 : add2 a (neg2 a) = z2) by (apply (@Plus_neg2 RR2 ax2 a Ha)).
        rewrite Hc2. apply (@Plus_P1 RR2 ax2 b Hb). }
  assert (Hsum : add2 (add2 a b) (add2 (neg2 a) (neg2 b)) = z2).
  { transitivity (add2 (add2 (add2 a b) (neg2 a)) (neg2 b)).
    - apply (@Plus_P3 RR2 ax2 (add2 a b) (neg2 a) (neg2 b) Hab Hna Hnb).
    - rewrite Hmid. apply (@Plus_neg2 RR2 ax2 b Hb). }
  assert (Hres : add2 (neg2 a) (neg2 b) = add2 z2 (neg2 (add2 a b)))
    by (apply (@Plus_Co3 RR2 ax2 (add2 a b) (add2 (neg2 a) (neg2 b)) z2 Hab Hnab z2_car Hsum)).
  assert (Hf : add2 z2 (neg2 (add2 a b)) = neg2 (add2 a b))
    by (apply (eq_trans (@Plus_P4 RR2 ax2 z2 (neg2 (add2 a b)) z2_car (neg2_car (add2 a b) Hab)) (@Plus_P1 RR2 ax2 (neg2 (add2 a b)) (neg2_car (add2 a b) Hab)))).
  rewrite Hf in Hres. symmetry. exact Hres.
Qed.

Lemma N1_sub : ∀ a b, a ∈ N1 -> b ∈ N1 -> lt1 a b -> add1 b (neg1 a) ∈ N1.
Proof. intros a b Ha Hb Hab. apply (@Int_P1_Lemma RR1 ax1 a b Ha Hb Hab). Qed.

Lemma sigN_sub : ∀ a b, a ∈ N1 -> b ∈ N1 -> lt1 a b
  -> sigN (add1 b (neg1 a)) = add2 (sigN b) (neg2 (sigN a)).
Proof.
  intros a b Ha Hb Hab.
  assert (Hba : add1 b (neg1 a) ∈ N1) by (apply N1_sub; assumption).
  assert (HbR : b ∈ car1) by (apply N1_sub_car1; exact Hb).
  assert (HaR : a ∈ car1) by (apply N1_sub_car1; exact Ha).
  assert (Hb_decomp : add1 (add1 b (neg1 a)) a = b).
  { transitivity (add1 b (add1 (neg1 a) a)).
    - symmetry. apply (@Plus_P3 RR1 ax1 b (neg1 a) a HbR (neg1_car a HaR) HaR).
    - assert (Hc : add1 (neg1 a) a = z1) by (apply neg1_add; exact HaR).
      rewrite Hc. apply (@Plus_P1 RR1 ax1 b HbR). }
  assert (Hadd := sigN_add (add1 b (neg1 a)) a Hba Ha).
  rewrite Hb_decomp in Hadd.
  assert (Hadd2 : add2 (sigN a) (sigN (add1 b (neg1 a))) = sigN b).
  { assert (Hcc : add2 (sigN (add1 b (neg1 a))) (sigN a) = add2 (sigN a) (sigN (add1 b (neg1 a)))) by (apply (@Plus_P4 RR2 ax2 (sigN (add1 b (neg1 a))) (sigN a) (N2_sub_car2 (sigN (add1 b (neg1 a))) (sigN_N2 (add1 b (neg1 a)) Hba)) (N2_sub_car2 (sigN a) (sigN_N2 a Ha)))).
    rewrite Hcc in Hadd. symmetry. exact Hadd. }
  exact (@Plus_Co3 RR2 ax2 (sigN a) (sigN (add1 b (neg1 a))) (sigN b) (N2_sub_car2 (sigN a) (sigN_N2 a Ha)) (N2_sub_car2 (sigN (add1 b (neg1 a))) (sigN_N2 (add1 b (neg1 a)) Hba)) (N2_sub_car2 (sigN b) (sigN_N2 b Hb)) Hadd2).
Qed.

Lemma Z1_sub_car1 : Z1 ⊂ car1.
Proof. unfold Z1, car1. intros z Hz. apply (@Z_Subset_R RR1 ax1 z); exact Hz. Qed.
Lemma Z2_sub_car2 : Z2 ⊂ car2.
Proof. unfold Z2, car2. intros z Hz. apply (@Z_Subset_R RR2 ax2 z); exact Hz. Qed.

(* ---------------- sigZ 保加法 ---------------- *)

Lemma sigZ_add : ∀ z w, z ∈ Z1 -> w ∈ Z1 -> sigZ (add1 z w) = add2 (sigZ z) (sigZ w).
Proof.
  intros z w HzZ HwZ.
  assert (HNN : ∀ za wa, za ∈ N1 -> wa ∈ N1 -> sigZ (add1 za wa) = add2 (sigZ za) (sigZ wa)).
  { intros za wa HzN HwN.
    assert (HzwN : add1 za wa ∈ N1) by (apply (@Nat_P1a RR1 ax1 za wa HzN HwN)).
    rewrite (sigZ_eq_N (add1 za wa) HzwN). rewrite (sigZ_eq_N za HzN). rewrite (sigZ_eq_N wa HwN).
    apply sigN_add; assumption. }
  assert (HNP : ∀ zb wb, zb ∈ N1 -> neg1 wb ∈ N1 -> wb ∉ N1 -> sigZ (add1 zb wb) = add2 (sigZ zb) (sigZ wb)).
  { intros zb wb HzN Hwneg Hwn.
    assert (HzR : zb ∈ car1) by (apply N1_sub_car1; exact HzN).
    assert (HwnR : wb ∈ car1) by (apply neg1_back; apply N1_sub_car1; exact Hwneg).
    assert (HbR : neg1 wb ∈ car1) by (apply N1_sub_car1; exact Hwneg).
    assert (Hsw : sigZ wb = neg2 (sigN (neg1 wb))) by (apply sigZ_eq_neg; assumption).
    rewrite (sigZ_eq_N zb HzN). rewrite Hsw.
    destruct (@Order_Co1 RR1 ax1 zb (neg1 wb) HzR HbR) as [Hzb | [Hlt2 | Heq3]].
    - assert (Hzw : add1 zb wb = neg1 (add1 (neg1 wb) (neg1 zb))).
      { transitivity (add1 wb zb).
        - apply (@Plus_P4 RR1 ax1 zb wb HzR HwnR).
        - rewrite (neg_add1 (neg1 wb) (neg1 zb) HbR (neg1_car zb HzR)).
          rewrite (neg1_invol wb HwnR). rewrite (neg1_invol zb HzR). reflexivity. }
      rewrite Hzw.
      assert (HmN : add1 (neg1 wb) (neg1 zb) ∈ N1) by (apply (N1_sub zb (neg1 wb) HzN Hwneg Hzb)).
      assert (HmR : add1 (neg1 wb) (neg1 zb) ∈ car1) by (apply N1_sub_car1; exact HmN).
      assert (Hmn : neg1 (add1 (neg1 wb) (neg1 zb)) ∉ N1) by (intro Hc; exact (posN_negN_absurd (add1 (neg1 wb) (neg1 zb)) HmN Hc)).
      assert (Hin : neg1 (neg1 (add1 (neg1 wb) (neg1 zb))) ∈ N1) by (rewrite (neg1_invol (add1 (neg1 wb) (neg1 zb)) HmR); exact HmN).
      rewrite (sigZ_eq_neg (neg1 (add1 (neg1 wb) (neg1 zb))) Hin Hmn).
      rewrite (neg1_invol (add1 (neg1 wb) (neg1 zb)) HmR).
      rewrite (sigN_sub zb (neg1 wb) HzN Hwneg Hzb).
      assert (Hsb : sigN (neg1 wb) ∈ car2) by (apply N2_sub_car2; apply sigN_N2; exact Hwneg).
      assert (Hnz : neg2 (sigN zb) ∈ car2) by (apply neg2_car; apply N2_sub_car2; apply sigN_N2; exact HzN).
      assert (Hneg := neg_add2 (sigN (neg1 wb)) (neg2 (sigN zb)) Hsb Hnz).
      assert (Hii : neg2 (neg2 (sigN zb)) = sigN zb) by (apply neg2_invol; apply N2_sub_car2; apply sigN_N2; exact HzN).
      assert (Hkey : neg2 (add2 (sigN (neg1 wb)) (neg2 (sigN zb))) = add2 (neg2 (sigN (neg1 wb))) (sigN zb)) by (rewrite Hneg; rewrite Hii; reflexivity).
      rewrite Hkey.
      apply (eq_sym (@Plus_P4 RR2 ax2 (sigN zb) (neg2 (sigN (neg1 wb))) (N2_sub_car2 (sigN zb) (sigN_N2 zb HzN)) (neg2_car (sigN (neg1 wb)) (N2_sub_car2 (sigN (neg1 wb)) (sigN_N2 (neg1 wb) Hwneg))))).
    - assert (HL : add1 zb wb = add1 zb (neg1 (neg1 wb)))
        by (apply (f_equal (fun u => add1 zb u)); apply (eq_sym (neg1_invol wb HwnR))).
      rewrite HL.
      assert (HmN : add1 zb (neg1 (neg1 wb)) ∈ N1) by (apply (N1_sub (neg1 wb) zb Hwneg HzN Hlt2)).
      rewrite (sigZ_eq_N (add1 zb (neg1 (neg1 wb))) HmN).
      rewrite (sigN_sub (neg1 wb) zb Hwneg HzN Hlt2).
      reflexivity.
    - subst zb.
      assert (Hz1 : add1 (neg1 wb) wb = z1) by (apply neg1_add; exact HwnR).
      rewrite Hz1. rewrite sigZ_zero.
      apply (eq_sym (@Plus_neg2 RR2 ax2 (sigN (neg1 wb)) (N2_sub_car2 (sigN (neg1 wb)) (sigN_N2 (neg1 wb) Hwneg)))). }
  destruct (Z1_cases z HzZ) as [HzN | [Hzneg | Hz0]].
  - destruct (Z1_cases w HwZ) as [HwN | [Hwneg | Hw0]].
    + apply HNN; assumption.
    + apply HNP; [exact HzN | exact Hwneg | intro H; exact (posN_negN_absurd w H Hwneg)].
    + subst w. rewrite sigZ_zero.
      assert (Hzc : add1 z z1 = z) by (apply (@Plus_P1 RR1 ax1 z (N1_sub_car1 z HzN))).
      rewrite Hzc.
      apply (eq_sym (@Plus_P1 RR2 ax2 (sigZ z) (Z2_sub_car2 (sigZ z) (sigZ_Z2 z HzZ)))).
  - assert (Hzn : z ∉ N1) by (intro H; exact (posN_negN_absurd z H Hzneg)).
    destruct (Z1_cases w HwZ) as [HwN | [Hwneg | Hw0]].
    + assert (Hcomm : add1 z w = add1 w z) by (apply (@Plus_P4 RR1 ax1 z w (Z1_sub_car1 z HzZ) (N1_sub_car1 w HwN))).
      rewrite Hcomm. rewrite (HNP w z HwN Hzneg Hzn).
      apply (@Plus_P4 RR2 ax2 (sigZ w) (sigZ z) (Z2_sub_car2 (sigZ w) (sigZ_Z2 w HwZ)) (Z2_sub_car2 (sigZ z) (sigZ_Z2 z HzZ))).
    + assert (Hwn : w ∉ N1) by (intro H; exact (posN_negN_absurd w H Hwneg)).
      assert (Hzw : add1 z w = neg1 (add1 (neg1 z) (neg1 w))).
      { transitivity (add1 (neg1 (neg1 z)) (neg1 (neg1 w))).
        - apply (f_equal2 add1 (eq_sym (neg1_invol z (Z1_sub_car1 z HzZ))) (eq_sym (neg1_invol w (Z1_sub_car1 w HwZ)))).
        - symmetry. apply (neg_add1 (neg1 z) (neg1 w) (N1_sub_car1 (neg1 z) Hzneg) (N1_sub_car1 (neg1 w) Hwneg)). }
      rewrite Hzw.
      assert (HmN : add1 (neg1 z) (neg1 w) ∈ N1) by (apply (@Nat_P1a RR1 ax1 (neg1 z) (neg1 w) Hzneg Hwneg)).
      assert (HmR : add1 (neg1 z) (neg1 w) ∈ car1) by (apply N1_sub_car1; exact HmN).
      assert (Hmn : neg1 (add1 (neg1 z) (neg1 w)) ∉ N1) by (intro Hc; exact (posN_negN_absurd (add1 (neg1 z) (neg1 w)) HmN Hc)).
      assert (Hin : neg1 (neg1 (add1 (neg1 z) (neg1 w))) ∈ N1) by (rewrite (neg1_invol (add1 (neg1 z) (neg1 w)) HmR); exact HmN).
      rewrite (sigZ_eq_neg (neg1 (add1 (neg1 z) (neg1 w))) Hin Hmn).
      rewrite (neg1_invol (add1 (neg1 z) (neg1 w)) HmR).
      rewrite (sigN_add (neg1 z) (neg1 w) Hzneg Hwneg).
      rewrite (sigZ_eq_neg z Hzneg Hzn). rewrite (sigZ_eq_neg w Hwneg Hwn).
      apply (neg_add2 (sigN (neg1 z)) (sigN (neg1 w)) (N2_sub_car2 (sigN (neg1 z)) (sigN_N2 (neg1 z) Hzneg)) (N2_sub_car2 (sigN (neg1 w)) (sigN_N2 (neg1 w) Hwneg))).
    + subst w. rewrite sigZ_zero.
      assert (Hzc : add1 z z1 = z) by (apply (@Plus_P1 RR1 ax1 z (Z1_sub_car1 z HzZ))).
      rewrite Hzc.
      apply (eq_sym (@Plus_P1 RR2 ax2 (sigZ z) (Z2_sub_car2 (sigZ z) (sigZ_Z2 z HzZ)))).
  - subst z. rewrite sigZ_zero.
    destruct (Z1_cases w HwZ) as [HwN | [Hwneg | Hw0]].
    + assert (Hzc : add1 z1 w = w) by (apply (eq_trans (@Plus_P4 RR1 ax1 z1 w z1_car (N1_sub_car1 w HwN)) (@Plus_P1 RR1 ax1 w (N1_sub_car1 w HwN)))).
      rewrite Hzc.
      apply (eq_sym (eq_trans (@Plus_P4 RR2 ax2 z2 (sigZ w) z2_car (Z2_sub_car2 (sigZ w) (sigZ_Z2 w HwZ))) (@Plus_P1 RR2 ax2 (sigZ w) (Z2_sub_car2 (sigZ w) (sigZ_Z2 w HwZ))))).
    + assert (Hwn : w ∉ N1) by (intro H; exact (posN_negN_absurd w H Hwneg)).
      assert (Hzc : add1 z1 w = w) by (apply (eq_trans (@Plus_P4 RR1 ax1 z1 w z1_car (Z1_sub_car1 w HwZ)) (@Plus_P1 RR1 ax1 w (Z1_sub_car1 w HwZ)))).
      rewrite Hzc.
      assert (Hc2 : add2 z2 (sigZ w) = sigZ w) by (apply (eq_trans (@Plus_P4 RR2 ax2 z2 (sigZ w) z2_car (Z2_sub_car2 (sigZ w) (sigZ_Z2 w HwZ))) (@Plus_P1 RR2 ax2 (sigZ w) (Z2_sub_car2 (sigZ w) (sigZ_Z2 w HwZ))))).
      rewrite Hc2. reflexivity.
    + subst w. rewrite sigZ_zero.
      assert (Hzc : add1 z1 z1 = z1) by (apply (@Plus_P1 RR1 ax1 z1 z1_car)).
      rewrite Hzc. rewrite sigZ_zero.
      apply (eq_sym (@Plus_P1 RR2 ax2 z2 z2_car)).
Qed.

(* ---------------- 相反数的乘法 ---------------- *)

Lemma mul_neg1 : ∀ a b, a ∈ car1 -> b ∈ car1 -> neg1 (mul1 a b) = mul1 a (neg1 b).
Proof.
  intros a b Ha Hb.
  assert (Hnb : neg1 b ∈ car1) by (apply neg1_car; exact Hb).
  assert (Hab : mul1 a b ∈ car1) by (apply (@Mult_close RR1 ax1 a b Ha Hb)).
  assert (Hanb : mul1 a (neg1 b) ∈ car1) by (apply (@Mult_close RR1 ax1 a (neg1 b) Ha Hnb)).
  assert (Hsum : add1 (mul1 a b) (mul1 a (neg1 b)) = z1).
  { transitivity (add1 (mul1 b a) (mul1 (neg1 b) a)).
    - assert (Hc1 : mul1 a b = mul1 b a) by (apply (@Mult_P4 RR1 ax1 a b Ha Hb)).
      assert (Hc2 : mul1 a (neg1 b) = mul1 (neg1 b) a) by (apply (@Mult_P4 RR1 ax1 a (neg1 b) Ha Hnb)).
      rewrite Hc1. rewrite Hc2. reflexivity.
    - transitivity (mul1 (add1 b (neg1 b)) a).
      + symmetry. apply (@Mult_P5 RR1 ax1 b (neg1 b) a Hb Hnb Ha).
      + assert (Hc : add1 b (neg1 b) = z1) by (apply (@Plus_neg2 RR1 ax1 b Hb)).
        rewrite Hc.
        assert (Hc2 : mul1 z1 a = mul1 a z1) by (apply (@Mult_P4 RR1 ax1 z1 a z1_car Ha)).
        rewrite Hc2. apply (@PlusMult_Co1 RR1 ax1 a Ha). }
  assert (Hres : mul1 a (neg1 b) = add1 z1 (neg1 (mul1 a b)))
    by (apply (@Plus_Co3 RR1 ax1 (mul1 a b) (mul1 a (neg1 b)) z1 Hab Hanb z1_car Hsum)).
  assert (Hf : add1 z1 (neg1 (mul1 a b)) = neg1 (mul1 a b))
    by (apply (eq_trans (@Plus_P4 RR1 ax1 z1 (neg1 (mul1 a b)) z1_car (neg1_car (mul1 a b) Hab)) (@Plus_P1 RR1 ax1 (neg1 (mul1 a b)) (neg1_car (mul1 a b) Hab)))).
  rewrite Hf in Hres. symmetry. exact Hres.
Qed.

Lemma mul_neg2 : ∀ a b, a ∈ car2 -> b ∈ car2 -> neg2 (mul2 a b) = mul2 a (neg2 b).
Proof.
  intros a b Ha Hb.
  assert (Hnb : neg2 b ∈ car2) by (apply neg2_car; exact Hb).
  assert (Hab : mul2 a b ∈ car2) by (apply (@Mult_close RR2 ax2 a b Ha Hb)).
  assert (Hanb : mul2 a (neg2 b) ∈ car2) by (apply (@Mult_close RR2 ax2 a (neg2 b) Ha Hnb)).
  assert (Hsum : add2 (mul2 a b) (mul2 a (neg2 b)) = z2).
  { transitivity (add2 (mul2 b a) (mul2 (neg2 b) a)).
    - assert (Hc1 : mul2 a b = mul2 b a) by (apply (@Mult_P4 RR2 ax2 a b Ha Hb)).
      assert (Hc2 : mul2 a (neg2 b) = mul2 (neg2 b) a) by (apply (@Mult_P4 RR2 ax2 a (neg2 b) Ha Hnb)).
      rewrite Hc1. rewrite Hc2. reflexivity.
    - transitivity (mul2 (add2 b (neg2 b)) a).
      + symmetry. apply (@Mult_P5 RR2 ax2 b (neg2 b) a Hb Hnb Ha).
      + assert (Hc : add2 b (neg2 b) = z2) by (apply (@Plus_neg2 RR2 ax2 b Hb)).
        rewrite Hc.
        assert (Hc2 : mul2 z2 a = mul2 a z2) by (apply (@Mult_P4 RR2 ax2 z2 a z2_car Ha)).
        rewrite Hc2. apply (@PlusMult_Co1 RR2 ax2 a Ha). }
  assert (Hres : mul2 a (neg2 b) = add2 z2 (neg2 (mul2 a b)))
    by (apply (@Plus_Co3 RR2 ax2 (mul2 a b) (mul2 a (neg2 b)) z2 Hab Hanb z2_car Hsum)).
  assert (Hf : add2 z2 (neg2 (mul2 a b)) = neg2 (mul2 a b))
    by (apply (eq_trans (@Plus_P4 RR2 ax2 z2 (neg2 (mul2 a b)) z2_car (neg2_car (mul2 a b) Hab)) (@Plus_P1 RR2 ax2 (neg2 (mul2 a b)) (neg2_car (mul2 a b) Hab)))).
  rewrite Hf in Hres. symmetry. exact Hres.
Qed.

Lemma mul_negneg1 : ∀ a b, a ∈ car1 -> b ∈ car1 -> mul1 (neg1 a) (neg1 b) = mul1 a b.
Proof.
  intros a b Ha Hb.
  assert (Hna : neg1 a ∈ car1) by (apply neg1_car; exact Ha).
  assert (Hnb : neg1 b ∈ car1) by (apply neg1_car; exact Hb).
  assert (Hab : mul1 a b ∈ car1) by (apply (@Mult_close RR1 ax1 a b Ha Hb)).
  assert (E1 : mul1 (neg1 a) (neg1 b) = neg1 (mul1 (neg1 a) b)) by (apply (eq_sym (mul_neg1 (neg1 a) b Hna Hb))).
  assert (E2 : mul1 (neg1 a) b = neg1 (mul1 a b)).
  { transitivity (mul1 b (neg1 a)).
    - apply (@Mult_P4 RR1 ax1 (neg1 a) b Hna Hb).
    - assert (Hc2 : mul1 b (neg1 a) = neg1 (mul1 b a)) by (apply (eq_sym (mul_neg1 b a Hb Ha))).
      rewrite Hc2.
      assert (Hc3 : mul1 b a = mul1 a b) by (apply (@Mult_P4 RR1 ax1 b a Hb Ha)).
      rewrite Hc3. reflexivity. }
  rewrite E1. rewrite E2.
  exact (neg1_invol (mul1 a b) Hab).
Qed.

Lemma mul_negneg2 : ∀ a b, a ∈ car2 -> b ∈ car2 -> mul2 (neg2 a) (neg2 b) = mul2 a b.
Proof.
  intros a b Ha Hb.
  assert (Hna : neg2 a ∈ car2) by (apply neg2_car; exact Ha).
  assert (Hnb : neg2 b ∈ car2) by (apply neg2_car; exact Hb).
  assert (Hab : mul2 a b ∈ car2) by (apply (@Mult_close RR2 ax2 a b Ha Hb)).
  assert (E1 : mul2 (neg2 a) (neg2 b) = neg2 (mul2 (neg2 a) b)) by (apply (eq_sym (mul_neg2 (neg2 a) b Hna Hb))).
  assert (E2 : mul2 (neg2 a) b = neg2 (mul2 a b)).
  { transitivity (mul2 b (neg2 a)).
    - apply (@Mult_P4 RR2 ax2 (neg2 a) b Hna Hb).
    - assert (Hc2 : mul2 b (neg2 a) = neg2 (mul2 b a)) by (apply (eq_sym (mul_neg2 b a Hb Ha))).
      rewrite Hc2.
      assert (Hc3 : mul2 b a = mul2 a b) by (apply (@Mult_P4 RR2 ax2 b a Hb Ha)).
      rewrite Hc3. reflexivity. }
  rewrite E1. rewrite E2.
  exact (neg2_invol (mul2 a b) Hab).
Qed.

(* ---------------- sigZ 保乘法 ---------------- *)

Lemma sigZ_mul : ∀ z w, z ∈ Z1 -> w ∈ Z1 -> sigZ (mul1 z w) = mul2 (sigZ z) (sigZ w).
Proof.
  intros z w HzZ HwZ.
  assert (HNN : ∀ za wa, za ∈ N1 -> wa ∈ N1 -> sigZ (mul1 za wa) = mul2 (sigZ za) (sigZ wa)).
  { intros za wa HzN HwN.
    assert (HzwN : mul1 za wa ∈ N1) by (apply (@Nat_P1b RR1 ax1 za wa HzN HwN)).
    rewrite (sigZ_eq_N (mul1 za wa) HzwN). rewrite (sigZ_eq_N za HzN). rewrite (sigZ_eq_N wa HwN).
    apply sigN_mul; assumption. }
  assert (HNPm : ∀ za wb, za ∈ N1 -> neg1 wb ∈ N1 -> wb ∉ N1 -> sigZ (mul1 za wb) = mul2 (sigZ za) (sigZ wb)).
  { intros za wb HzN Hwneg Hwn.
    assert (HzR : za ∈ car1) by (apply N1_sub_car1; exact HzN).
    assert (HwbR : wb ∈ car1) by (apply neg1_back; apply N1_sub_car1; exact Hwneg).
    assert (HbR : neg1 wb ∈ car1) by (apply N1_sub_car1; exact Hwneg).
    assert (HzbN : mul1 za (neg1 wb) ∈ N1) by (apply (@Nat_P1b RR1 ax1 za (neg1 wb) HzN Hwneg)).
    assert (Hwb_eq : wb = neg1 (neg1 wb)) by (apply (eq_sym (neg1_invol wb HwbR))).
    assert (Hprod : mul1 za wb = neg1 (mul1 za (neg1 wb))).
    { transitivity (mul1 za (neg1 (neg1 wb))).
      - apply (f_equal (fun u => mul1 za u) Hwb_eq).
      - symmetry. apply (mul_neg1 za (neg1 wb) HzR HbR). }
    rewrite Hprod.
    assert (HbbR : mul1 za (neg1 wb) ∈ car1) by (apply N1_sub_car1; exact HzbN).
    assert (Hin : neg1 (neg1 (mul1 za (neg1 wb))) ∈ N1) by (rewrite (neg1_invol (mul1 za (neg1 wb)) HbbR); exact HzbN).
    assert (Hmn : neg1 (mul1 za (neg1 wb)) ∉ N1) by (intro Hc; exact (posN_negN_absurd (mul1 za (neg1 wb)) HzbN Hc)).
    rewrite (sigZ_eq_neg (neg1 (mul1 za (neg1 wb))) Hin Hmn).
    rewrite (neg1_invol (mul1 za (neg1 wb)) HbbR).
    rewrite (sigN_mul za (neg1 wb) HzN Hwneg).
    rewrite (sigZ_eq_N za HzN). rewrite (sigZ_eq_neg wb Hwneg Hwn).
    apply (mul_neg2 (sigN za) (sigN (neg1 wb)) (N2_sub_car2 (sigN za) (sigN_N2 za HzN)) (N2_sub_car2 (sigN (neg1 wb)) (sigN_N2 (neg1 wb) Hwneg))). }
  destruct (Z1_cases z HzZ) as [HzN | [Hzneg | Hz0]].
  - destruct (Z1_cases w HwZ) as [HwN | [Hwneg | Hw0]].
    + apply HNN; assumption.
    + apply HNPm; [exact HzN | exact Hwneg | intro H; exact (posN_negN_absurd w H Hwneg)].
    + subst w. rewrite sigZ_zero.
      assert (Hzc : mul1 z z1 = z1) by (apply (@PlusMult_Co1 RR1 ax1 z (N1_sub_car1 z HzN))).
      rewrite Hzc. rewrite sigZ_zero.
      apply (eq_sym (@PlusMult_Co1 RR2 ax2 (sigZ z) (Z2_sub_car2 (sigZ z) (sigZ_Z2 z HzZ)))).
  - assert (Hzn : z ∉ N1) by (intro H; exact (posN_negN_absurd z H Hzneg)).
    destruct (Z1_cases w HwZ) as [HwN | [Hwneg | Hw0]].
    + assert (Hcomm : mul1 z w = mul1 w z) by (apply (@Mult_P4 RR1 ax1 z w (Z1_sub_car1 z HzZ) (N1_sub_car1 w HwN))).
      rewrite Hcomm. rewrite (HNPm w z HwN Hzneg Hzn).
      assert (Hcc : mul2 (sigZ w) (sigZ z) = mul2 (sigZ z) (sigZ w)) by (apply (@Mult_P4 RR2 ax2 (sigZ w) (sigZ z) (Z2_sub_car2 (sigZ w) (sigZ_Z2 w HwZ)) (Z2_sub_car2 (sigZ z) (sigZ_Z2 z HzZ)))).
      rewrite Hcc. reflexivity.
    + assert (Hwn : w ∉ N1) by (intro H; exact (posN_negN_absurd w H Hwneg)).
      assert (Hz_eq : z = neg1 (neg1 z)) by (apply (eq_sym (neg1_invol z (Z1_sub_car1 z HzZ)))).
      assert (Hw_eq : w = neg1 (neg1 w)) by (apply (eq_sym (neg1_invol w (Z1_sub_car1 w HwZ)))).
      assert (Hzw : mul1 z w = mul1 (neg1 z) (neg1 w)).
      { transitivity (mul1 (neg1 (neg1 z)) (neg1 (neg1 w))).
        - apply (f_equal2 mul1 Hz_eq Hw_eq).
        - apply (mul_negneg1 (neg1 z) (neg1 w) (N1_sub_car1 (neg1 z) Hzneg) (N1_sub_car1 (neg1 w) Hwneg)). }
      rewrite Hzw.
      assert (HmN : mul1 (neg1 z) (neg1 w) ∈ N1) by (apply (@Nat_P1b RR1 ax1 (neg1 z) (neg1 w) Hzneg Hwneg)).
      rewrite (sigZ_eq_N (mul1 (neg1 z) (neg1 w)) HmN).
      rewrite (sigN_mul (neg1 z) (neg1 w) Hzneg Hwneg).
      rewrite (sigZ_eq_neg z Hzneg Hzn). rewrite (sigZ_eq_neg w Hwneg Hwn).
      apply (eq_sym (mul_negneg2 (sigN (neg1 z)) (sigN (neg1 w)) (N2_sub_car2 (sigN (neg1 z)) (sigN_N2 (neg1 z) Hzneg)) (N2_sub_car2 (sigN (neg1 w)) (sigN_N2 (neg1 w) Hwneg)))).
    + subst w. rewrite sigZ_zero.
      assert (Hzc : mul1 z z1 = z1) by (apply (@PlusMult_Co1 RR1 ax1 z (Z1_sub_car1 z HzZ))).
      rewrite Hzc. rewrite sigZ_zero.
      apply (eq_sym (@PlusMult_Co1 RR2 ax2 (sigZ z) (Z2_sub_car2 (sigZ z) (sigZ_Z2 z HzZ)))).
  - subst z. rewrite sigZ_zero.
    destruct (Z1_cases w HwZ) as [HwN | [Hwneg | Hw0]].
    + assert (Hzc : mul1 z1 w = z1) by (apply (eq_trans (@Mult_P4 RR1 ax1 z1 w z1_car (N1_sub_car1 w HwN)) (@PlusMult_Co1 RR1 ax1 w (N1_sub_car1 w HwN)))).
      rewrite Hzc. rewrite sigZ_zero.
      assert (Hc2 : mul2 z2 (sigZ w) = z2) by (apply (eq_trans (@Mult_P4 RR2 ax2 z2 (sigZ w) z2_car (Z2_sub_car2 (sigZ w) (sigZ_Z2 w HwZ))) (@PlusMult_Co1 RR2 ax2 (sigZ w) (Z2_sub_car2 (sigZ w) (sigZ_Z2 w HwZ))))).
      apply (eq_sym Hc2).
    + assert (Hwn : w ∉ N1) by (intro H; exact (posN_negN_absurd w H Hwneg)).
      assert (Hzc : mul1 z1 w = z1) by (apply (eq_trans (@Mult_P4 RR1 ax1 z1 w z1_car (Z1_sub_car1 w HwZ)) (@PlusMult_Co1 RR1 ax1 w (Z1_sub_car1 w HwZ)))).
      rewrite Hzc. rewrite sigZ_zero.
      assert (Hc2 : mul2 z2 (sigZ w) = z2) by (apply (eq_trans (@Mult_P4 RR2 ax2 z2 (sigZ w) z2_car (Z2_sub_car2 (sigZ w) (sigZ_Z2 w HwZ))) (@PlusMult_Co1 RR2 ax2 (sigZ w) (Z2_sub_car2 (sigZ w) (sigZ_Z2 w HwZ))))).
      apply (eq_sym Hc2).
    + subst w. rewrite sigZ_zero.
      assert (Hzc : mul1 z1 z1 = z1) by (apply (@PlusMult_Co1 RR1 ax1 z1 z1_car)).
      rewrite Hzc. rewrite sigZ_zero.
      assert (Hc2 : mul2 z2 z2 = z2) by (apply (@PlusMult_Co1 RR2 ax2 z2 z2_car)).
      apply (eq_sym Hc2).
Qed.

(* ---------------- 满射性与 sigZ 的负元 ---------------- *)

Lemma sigN_surj : ∀ w, w ∈ N2 -> ∃ n, n ∈ N1 /\ sigN n = w.
Proof.
  intros w Hw.
  set (E := \{ λ y, y ∈ N2 /\ ∃ n, n ∈ N1 /\ sigN n = y \}).
  assert (Esub : E ⊂ N2) by (intros z Hz; apply AxiomII in Hz as [_ [Hz _]]; exact Hz).
  assert (H1 : o2 ∈ E).
  { apply AxiomII. split.
    - unfold Ensemble. exists car2. exact o2_car.
    - split; [apply (@one_in_N RR2 ax2) | exists o1; split; [apply (@one_in_N RR1 ax1) | apply sigN_one]]. }
  assert (Hclos : ∀ y, y ∈ E -> add2 y o2 ∈ E).
  { intros y Hy. apply AxiomII in Hy as [_ [HyN Hn]].
    destruct Hn as [n [HnN Hne]].
    apply AxiomII. split.
    - apply Ens_car2. apply (@Plus_close RR2 ax2 y o2 (N2_sub_car2 y HyN) o2_car).
    - split.
      + assert (HIN := @IndSet_N RR2 ax2); unfold IndSet in HIN; exact (proj2 HIN y HyN).
      + exists (add1 n o1). split.
        * assert (HIN := @IndSet_N RR1 ax1); unfold IndSet in HIN; exact (proj2 HIN n HnN).
        * rewrite (sigN_succ n HnN). rewrite Hne. reflexivity. }
  assert (HE : E = N2) by (apply (@MathInd RR2 ax2 E Esub H1 Hclos)).
  assert (HwE : w ∈ E) by (rewrite HE; exact Hw).
  apply AxiomII in HwE as [_ [_ Hn]].
  destruct Hn as [n [HnN Hne]].
  exists n. split; [exact HnN | exact Hne].
Qed.

Lemma neg2_zero : neg2 z2 = z2.
Proof.
  assert (Hsum : add2 z2 (neg2 z2) = z2)
    by (apply (eq_trans (@Plus_P4 RR2 ax2 z2 (neg2 z2) z2_car (neg2_car z2 z2_car)) (neg2_add z2 z2_car))).
  assert (Hres : neg2 z2 = add2 z2 (neg2 z2))
    by (apply (@Plus_Co3 RR2 ax2 z2 (neg2 z2) z2 z2_car (neg2_car z2 z2_car) z2_car Hsum)).
  rewrite Hsum in Hres. exact Hres.
Qed.

Lemma sigZ_neg : ∀ z, z ∈ Z1 -> sigZ (neg1 z) = neg2 (sigZ z).
Proof.
  intros z HzZ.
  destruct (Z1_cases z HzZ) as [HzN | [Hzneg | Hz0]].
  - assert (Hzn : neg1 z ∉ N1) by (intro Hc; exact (posN_negN_absurd z HzN Hc)).
    assert (Hin : neg1 (neg1 z) ∈ N1) by (rewrite (neg1_invol z (N1_sub_car1 z HzN)); exact HzN).
    rewrite (sigZ_eq_neg (neg1 z) Hin Hzn).
    rewrite (neg1_invol z (N1_sub_car1 z HzN)).
    rewrite (sigZ_eq_N z HzN). reflexivity.
  - assert (Hzn0 : z ∉ N1) by (intro Hc; exact (posN_negN_absurd z Hc Hzneg)).
    rewrite (sigZ_eq_N (neg1 z) Hzneg).
    rewrite (sigZ_eq_neg z Hzneg Hzn0).
    apply (eq_sym (neg2_invol (sigN (neg1 z)) (N2_sub_car2 (sigN (neg1 z)) (sigN_N2 (neg1 z) Hzneg)))).
  - subst z. rewrite neg1_z1. rewrite sigZ_zero.
    apply (eq_sym neg2_zero).
Qed.

Lemma Z2_cases : ∀ z, z ∈ Z2 -> z ∈ N2 \/ neg2 z ∈ N2 \/ z = z2.
Proof.
  intros z Hz. unfold Z2, Z in Hz.
  apply MKT4 in Hz as [HzN | HzRest].
  - left. exact HzN.
  - apply MKT4 in HzRest as [HzB | Hz0].
    + right. left. apply AxiomII in HzB as [_ Hneg]. exact Hneg.
    + right. right.
      exact (proj1 (MKT41 z2 (Ens_car2 z2 z2_car) z) Hz0).
Qed.

Lemma sigZ_surj : ∀ w, w ∈ Z2 -> ∃ z, z ∈ Z1 /\ sigZ z = w.
Proof.
  intros w HwZ.
  destruct (Z2_cases w HwZ) as [HwN | [Hwneg | Hw0]].
  - destruct (sigN_surj w HwN) as [n [HnN Hne]].
    exists n. split; [apply N1_in_Z1; exact HnN | rewrite (sigZ_eq_N n HnN); exact Hne].
  - destruct (sigN_surj (neg2 w) Hwneg) as [n [HnN Hne]].
    exists (neg1 n). split.
    + apply Z1_neg. apply N1_in_Z1. exact HnN.
    + rewrite (sigZ_neg n (N1_in_Z1 n HnN)).
      rewrite (sigZ_eq_N n HnN).
      rewrite Hne.
      exact (neg2_invol w (Z2_sub_car2 w HwZ)).
  - subst w. exists z1. split; [exact Z1_zero | apply sigZ_zero].
Qed.

(* ---------------- sigZ 的单调性 ---------------- *)

Lemma Z1_pos_N : ∀ d, d ∈ Z1 -> lt1 z1 d -> d ∈ N1.
Proof.
  intros d HdZ H0d.
  destruct (Z1_cases d HdZ) as [HdN | [Hdneg | Hd0]].
  - exact HdN.
  - exfalso.
    assert (Hnegn : neg1 d ∈ car1) by (apply N1_sub_car1; exact Hdneg).
    assert (HdR : d ∈ car1) by (apply neg1_back; exact Hnegn).
    assert (H1d : le1 o1 (neg1 d)) by (exact (proj2 (proj2 (@one_is_min_in_N RR1 ax1)) (neg1 d) Hdneg)).
    assert (Hnegneg : lt1 (neg1 d) z1) by (apply (@OrderPM_Co2a RR1 ax1 d HdR H0d)).
    assert (H0lt : lt1 z1 (neg1 d)) by (apply (@Order_Co2 RR1 ax1 z1 o1 (neg1 d) z1_car o1_car Hnegn); left; split; [exact (@OrderPM_Co9 RR1 ax1) | exact H1d]).
    exact ((proj2 Hnegneg) (@Leq_P2 RR1 ax1 (neg1 d) z1 Hnegn z1_car (proj1 Hnegneg) (proj1 H0lt))).
  - subst d. exfalso. exact (proj2 H0d eq_refl).
Qed.

Lemma sigZ_pos : ∀ z, z ∈ Z1 -> lt1 z1 z -> lt2 z2 (sigZ z).
Proof.
  intros z HzZ H0z.
  assert (HzN : z ∈ N1) by (apply Z1_pos_N; assumption).
  rewrite (sigZ_eq_N z HzN).
  assert (Hmin : le2 o2 (sigN z)) by (exact (proj2 (proj2 (@one_is_min_in_N RR2 ax2)) (sigN z) (sigN_N2 z HzN))).
  apply (@Order_Co2 RR2 ax2 z2 o2 (sigN z) z2_car o2_car (N2_sub_car2 (sigN z) (sigN_N2 z HzN))); left; split.
  - exact (@OrderPM_Co9 RR2 ax2).
  - exact Hmin.
Qed.

Lemma sigZ_negpos : ∀ z, z ∈ Z1 -> lt1 z z1 -> lt2 (sigZ z) z2.
Proof.
  intros z HzZ Hz0.
  assert (HzR : z ∈ car1) by (apply Z1_sub_car1; exact HzZ).
  assert (HnzR : neg1 z ∈ car1) by (apply neg1_car; exact HzR).
  assert (HnegzZ : neg1 z ∈ Z1) by (apply Z1_neg; exact HzZ).
  assert (H0nz : lt1 z1 (neg1 z)).
  { assert (Ht : lt1 (add1 z (neg1 z)) (add1 z1 (neg1 z))) by (apply (@OrderPM_Co1 RR1 ax1 z z1 (neg1 z) HzR z1_car HnzR); exact Hz0).
    assert (He : add1 z (neg1 z) = z1) by (apply (@Plus_neg2 RR1 ax1 z HzR)).
    assert (He2 : add1 z1 (neg1 z) = neg1 z) by (apply (eq_trans (@Plus_P4 RR1 ax1 z1 (neg1 z) z1_car HnzR) (@Plus_P1 RR1 ax1 (neg1 z) HnzR))).
    rewrite He in Ht. rewrite He2 in Ht. exact Ht. }
  assert (HnzN : neg1 z ∈ N1) by (apply Z1_pos_N; assumption).
  assert (Hzn : z ∉ N1).
  { intro Hc.
    assert (H1z : le1 o1 z) by (exact (proj2 (proj2 (@one_is_min_in_N RR1 ax1)) z Hc)).
    assert (H0z : le1 z1 z) by (apply (@Leq_P3 RR1 ax1 z1 o1 z z1_car o1_car (N1_sub_car1 z Hc) (proj1 (@OrderPM_Co9 RR1 ax1)) H1z)).
    assert (Hzle0 : le1 z z1) by (exact (proj1 Hz0)).
    exact ((proj2 Hz0) (@Leq_P2 RR1 ax1 z z1 (N1_sub_car1 z Hc) z1_car Hzle0 H0z)). }
  rewrite (sigZ_eq_neg z HnzN Hzn).
  assert (Hmin : le2 o2 (sigN (neg1 z))) by (exact (proj2 (proj2 (@one_is_min_in_N RR2 ax2)) (sigN (neg1 z)) (sigN_N2 (neg1 z) HnzN))).
  assert (Hpos : lt2 z2 (sigN (neg1 z))) by (apply (@Order_Co2 RR2 ax2 z2 o2 (sigN (neg1 z)) z2_car o2_car (N2_sub_car2 (sigN (neg1 z)) (sigN_N2 (neg1 z) HnzN))); left; split; [exact (@OrderPM_Co9 RR2 ax2) | exact Hmin]).
  exact (@OrderPM_Co2a RR2 ax2 (sigN (neg1 z)) (N2_sub_car2 (sigN (neg1 z)) (sigN_N2 (neg1 z) HnzN)) Hpos).
Qed.

Lemma sigZ_mono : ∀ z w, z ∈ Z1 -> w ∈ Z1 -> lt1 z w -> lt2 (sigZ z) (sigZ w).
Proof.
  intros z w HzZ HwZ Hzw.
  assert (HzR : z ∈ car1) by (apply Z1_sub_car1; exact HzZ).
  assert (HwR : w ∈ car1) by (apply Z1_sub_car1; exact HwZ).
  assert (HnzR : neg1 z ∈ car1) by (apply neg1_car; exact HzR).
  assert (HnegzZ : neg1 z ∈ Z1) by (apply Z1_neg; exact HzZ).
  assert (HdZ : add1 w (neg1 z) ∈ Z1) by (apply (@Int_P1a RR1 ax1 w (neg1 z) HwZ HnegzZ)).
  assert (H0d : lt1 z1 (add1 w (neg1 z))).
  { assert (Ht : lt1 (add1 z (neg1 z)) (add1 w (neg1 z))) by (apply (@OrderPM_Co1 RR1 ax1 z w (neg1 z) HzR HwR HnzR); exact Hzw).
    assert (He : add1 z (neg1 z) = z1) by (apply (@Plus_neg2 RR1 ax1 z HzR)).
    rewrite He in Ht. exact Ht. }
  assert (Hpos : lt2 z2 (sigZ (add1 w (neg1 z)))) by (apply sigZ_pos; assumption).
  assert (HPeq : sigZ (add1 w (neg1 z)) = add2 (sigZ w) (neg2 (sigZ z)))
    by (rewrite (sigZ_add w (neg1 z) HwZ HnegzZ); rewrite (sigZ_neg z HzZ); reflexivity).
  rewrite HPeq in Hpos.
  assert (HswR : add2 (sigZ w) (neg2 (sigZ z)) ∈ car2).
  { apply (@Plus_close RR2 ax2 (sigZ w) (neg2 (sigZ z))).
    - apply Z2_sub_car2; apply sigZ_Z2; exact HwZ.
    - apply neg2_car. apply Z2_sub_car2. apply sigZ_Z2. exact HzZ. }
  assert (HszR : sigZ z ∈ car2) by (apply Z2_sub_car2; apply sigZ_Z2; exact HzZ).
  assert (Hw_eq : add2 (add2 (sigZ w) (neg2 (sigZ z))) (sigZ z) = sigZ w).
  { assert (Heqs : add2 (add2 (sigZ w) (neg2 (sigZ z))) (sigZ z) = add2 (sigZ w) (add2 (neg2 (sigZ z)) (sigZ z)))
      by (apply (eq_sym (@Plus_P3 RR2 ax2 (sigZ w) (neg2 (sigZ z)) (sigZ z) (Z2_sub_car2 (sigZ w) (sigZ_Z2 w HwZ)) (neg2_car (sigZ z) (Z2_sub_car2 (sigZ z) (sigZ_Z2 z HzZ))) HszR))).
    rewrite Heqs.
    assert (Hc : add2 (neg2 (sigZ z)) (sigZ z) = z2) by (apply (neg2_add (sigZ z) HszR)).
    rewrite Hc. apply (@Plus_P1 RR2 ax2 (sigZ w) (Z2_sub_car2 (sigZ w) (sigZ_Z2 w HwZ))). }
  assert (Ht : lt2 (add2 z2 (sigZ z)) (add2 (add2 (sigZ w) (neg2 (sigZ z))) (sigZ z)))
    by (apply (@OrderPM_Co1 RR2 ax2 z2 (add2 (sigZ w) (neg2 (sigZ z))) (sigZ z) z2_car HswR HszR); exact Hpos).
  assert (Hz1 : add2 z2 (sigZ z) = sigZ z) by (apply (eq_trans (@Plus_P4 RR2 ax2 z2 (sigZ z) z2_car HszR) (@Plus_P1 RR2 ax2 (sigZ z) HszR))).
  rewrite Hz1 in Ht. rewrite Hw_eq in Ht. exact Ht.
Qed.

Lemma sigZ_inj : ∀ z w, z ∈ Z1 -> w ∈ Z1 -> sigZ z = sigZ w -> z = w.
Proof.
  intros z w HzZ HwZ Heq.
  assert (HzR : z ∈ car1) by (apply Z1_sub_car1; exact HzZ).
  assert (HwR : w ∈ car1) by (apply Z1_sub_car1; exact HwZ).
  destruct (@Order_Co1 RR1 ax1 z w HzR HwR) as [Hlt | [Hgt | Heq2]].
  - exfalso. assert (H1 : lt2 (sigZ z) (sigZ w)) by (apply (sigZ_mono z w HzZ HwZ Hlt)).
    exact ((proj2 H1) Heq).
  - exfalso. assert (H1 : lt2 (sigZ w) (sigZ z)) by (apply (sigZ_mono w z HwZ HzZ Hgt)).
    exact ((proj2 H1) (eq_sym Heq)).
  - exact Heq2.
Qed.

(* ---------------- 有理数：倒数的记号与引理 ---------------- *)

Definition inv1 (x:Class) : Class := ∩(\{ λ u, u ∈ (car1 ~ [z1]) /\ mul1 u x = o1 \}).
Definition inv2 (x:Class) : Class := ∩(\{ λ u, u ∈ (car2 ~ [z2]) /\ mul2 u x = o2 \}).

Lemma in_sm1 : ∀ x, x ∈ car1 -> x ≠ z1 -> x ∈ (car1 ~ [z1]).
Proof.
  intros x Hx Hne. unfold Setminus. apply AxiomII. split.
  - exists car1. exact Hx.
  - split; [exact Hx |].
    apply AxiomII. split.
    + exists car1. exact Hx.
    + intro Hxs. exact (Hne (proj1 (MKT41 z1 (Ens_car1 z1 z1_car) x) Hxs)).
Qed.

Lemma in_sm2 : ∀ x, x ∈ car2 -> x ≠ z2 -> x ∈ (car2 ~ [z2]).
Proof.
  intros x Hx Hne. unfold Setminus. apply AxiomII. split.
  - exists car2. exact Hx.
  - split; [exact Hx |].
    apply AxiomII. split.
    + exists car2. exact Hx.
    + intro Hxs. exact (Hne (proj1 (MKT41 z2 (Ens_car2 z2 z2_car) x) Hxs)).
Qed.

Lemma inv1_car : ∀ x, x ∈ (car1 ~ [z1]) -> inv1 x ∈ car1.
Proof.
  intros x Hx. pose proof (@Mult_inv1 RR1 ax1 x Hx) as H.
  unfold Setminus in H. apply AxiomII in H as [_ [Hr _]]. exact Hr.
Qed.
Lemma inv1_val : ∀ x, x ∈ (car1 ~ [z1]) -> mul1 x (inv1 x) = o1.
Proof. intros x Hx. apply (@Mult_inv2 RR1 ax1 x Hx). Qed.
Lemma sm1_car : ∀ x, x ∈ (car1 ~ [z1]) -> x ∈ car1.
Proof. intros x Hx. unfold Setminus in Hx. apply AxiomII in Hx as [_ [Hr _]]. exact Hr. Qed.
Lemma sm2_car : ∀ x, x ∈ (car2 ~ [z2]) -> x ∈ car2.
Proof. intros x Hx. unfold Setminus in Hx. apply AxiomII in Hx as [_ [Hr _]]. exact Hr. Qed.

Lemma inv1_valc : ∀ x, x ∈ (car1 ~ [z1]) -> mul1 (inv1 x) x = o1.
Proof.
  intros x Hx.
  apply (eq_trans (@Mult_P4 RR1 ax1 (inv1 x) x (inv1_car x Hx) (sm1_car x Hx)) (inv1_val x Hx)).
Qed.
Lemma inv2_valc : ∀ x, x ∈ (car2 ~ [z2]) -> mul2 (inv2 x) x = o2.
Proof.
  intros x Hx.
  assert (Hic : inv2 x ∈ car2) by (pose proof (@Mult_inv1 RR2 ax2 x Hx) as H; unfold Setminus in H; apply AxiomII in H as [_ [Hr _]]; exact Hr).
  apply (eq_trans (@Mult_P4 RR2 ax2 (inv2 x) x Hic (sm2_car x Hx)) (@Mult_inv2 RR2 ax2 x Hx)).
Qed.

Lemma inv2_car : ∀ x, x ∈ (car2 ~ [z2]) -> inv2 x ∈ car2.
Proof.
  intros x Hx. pose proof (@Mult_inv1 RR2 ax2 x Hx) as H.
  unfold Setminus in H. apply AxiomII in H as [_ [Hr _]]. exact Hr.
Qed.
Lemma inv2_val : ∀ x, x ∈ (car2 ~ [z2]) -> mul2 x (inv2 x) = o2.
Proof. intros x Hx. apply (@Mult_inv2 RR2 ax2 x Hx). Qed.

Lemma sigZ_ne_zero : ∀ n, n ∈ Z1 -> n ≠ z1 -> sigZ n ≠ z2.
Proof.
  intros n HnZ Hne H. apply Hne.
  apply (sigZ_inj n z1 HnZ Z1_zero). rewrite H. symmetry. exact sigZ_zero.
Qed.

Lemma cross1 : ∀ m1 n1 m2 n2, m1 ∈ Z1 -> n1 ∈ Z1 -> n1 ≠ z1 -> m2 ∈ Z1 -> n2 ∈ Z1 -> n2 ≠ z1
  -> mul1 m1 (inv1 n1) = mul1 m2 (inv1 n2) -> mul1 m1 n2 = mul1 m2 n1.
Proof.
  intros m1 n1 m2 n2 Hm1 Hn1 Hn1z Hm2 Hn2 Hn2z Heq.
  assert (Hm1R : m1 ∈ car1) by (apply Z1_sub_car1; exact Hm1).
  assert (Hn1R : n1 ∈ car1) by (apply Z1_sub_car1; exact Hn1).
  assert (Hm2R : m2 ∈ car1) by (apply Z1_sub_car1; exact Hm2).
  assert (Hn2R : n2 ∈ car1) by (apply Z1_sub_car1; exact Hn2).
  assert (Hinvn1 : inv1 n1 ∈ car1) by (apply inv1_car; apply in_sm1; assumption).
  assert (Hinvn2 : inv1 n2 ∈ car1) by (apply inv1_car; apply in_sm1; assumption).
  assert (Hq2R : mul1 m2 (inv1 n2) ∈ car1) by (apply (@Mult_close RR1 ax1 m2 (inv1 n2) Hm2R Hinvn2)).
  assert (Hm1eq : m1 = mul1 (mul1 m1 (inv1 n1)) n1).
  { transitivity (mul1 m1 (mul1 (inv1 n1) n1)).
    - symmetry.
      transitivity (mul1 m1 o1).
      + assert (Hc : mul1 (inv1 n1) n1 = o1) by (apply inv1_valc; apply in_sm1; assumption).
        rewrite Hc. reflexivity.
      + apply (@Mult_P1 RR1 ax1 m1 Hm1R).
    - apply (@Mult_P3 RR1 ax1 m1 (inv1 n1) n1 Hm1R Hinvn1 Hn1R). }
  assert (Hm2eq : m2 = mul1 (mul1 m2 (inv1 n2)) n2).
  { transitivity (mul1 m2 (mul1 (inv1 n2) n2)).
    - symmetry.
      transitivity (mul1 m2 o1).
      + assert (Hc : mul1 (inv1 n2) n2 = o1) by (apply inv1_valc; apply in_sm1; assumption).
        rewrite Hc. reflexivity.
      + apply (@Mult_P1 RR1 ax1 m2 Hm2R).
    - apply (@Mult_P3 RR1 ax1 m2 (inv1 n2) n2 Hm2R Hinvn2 Hn2R). }
  transitivity (mul1 (mul1 (mul1 m1 (inv1 n1)) n1) n2).
  - apply (f_equal (fun u => mul1 u n2) Hm1eq).
  - rewrite Heq.
    transitivity (mul1 (mul1 m2 (inv1 n2)) (mul1 n1 n2)).
    + symmetry. apply (@Mult_P3 RR1 ax1 (mul1 m2 (inv1 n2)) n1 n2 Hq2R Hn1R Hn2R).
    + transitivity (mul1 (mul1 m2 (inv1 n2)) (mul1 n2 n1)).
      * assert (Hc : mul1 n1 n2 = mul1 n2 n1) by (apply (@Mult_P4 RR1 ax1 n1 n2 Hn1R Hn2R)).
        rewrite Hc. reflexivity.
      * transitivity (mul1 (mul1 (mul1 m2 (inv1 n2)) n2) n1).
        { apply (@Mult_P3 RR1 ax1 (mul1 m2 (inv1 n2)) n2 n1 Hq2R Hn2R Hn1R). }
        { symmetry. apply (f_equal (fun u => mul1 u n1) Hm2eq). }
Qed.

Lemma mul_shift2 : ∀ a q s, a ∈ car2 -> q ∈ (car2 ~ [z2]) -> s ∈ car2
  -> mul2 a s = mul2 (mul2 a q) (mul2 (inv2 q) s).
Proof.
  intros a q s Ha Hq Hs.
  assert (HqR : q ∈ car2) by (apply sm2_car; exact Hq).
  assert (Hiq : inv2 q ∈ car2) by (apply inv2_car; exact Hq).
  assert (His : mul2 (inv2 q) s ∈ car2) by (apply (@Mult_close RR2 ax2 (inv2 q) s Hiq Hs)).
  assert (Hc : mul2 q (inv2 q) = o2) by (apply inv2_val; exact Hq).
  assert (Hc3 : mul2 o2 s = s) by (apply (eq_trans (@Mult_P4 RR2 ax2 o2 s o2_car Hs) (@Mult_P1 RR2 ax2 s Hs))).
  symmetry.
  assert (E1 : mul2 (mul2 a q) (mul2 (inv2 q) s) = mul2 a (mul2 q (mul2 (inv2 q) s)))
    by (apply (eq_sym (@Mult_P3 RR2 ax2 a q (mul2 (inv2 q) s) Ha HqR His))).
  rewrite E1.
  assert (E2 : mul2 q (mul2 (inv2 q) s) = mul2 (mul2 q (inv2 q)) s)
    by (apply (@Mult_P3 RR2 ax2 q (inv2 q) s HqR Hiq Hs)).
  rewrite E2.
  assert (E3 : mul2 (mul2 q (inv2 q)) s = mul2 o2 s) by (rewrite Hc; reflexivity).
  rewrite E3. rewrite Hc3. reflexivity.
Qed.

Lemma frac_eq2 : ∀ a b c d, a ∈ car2 -> b ∈ car2 -> c ∈ (car2 ~ [z2]) -> d ∈ (car2 ~ [z2])
  -> mul2 a d = mul2 b c -> mul2 a (inv2 c) = mul2 b (inv2 d).
Proof.
  intros a b c d Ha Hb Hc Hd H.
  assert (HcR : c ∈ car2) by (apply sm2_car; exact Hc).
  assert (HdR : d ∈ car2) by (apply sm2_car; exact Hd).
  assert (Hic : inv2 c ∈ car2) by (apply inv2_car; exact Hc).
  assert (Hid : inv2 d ∈ car2) by (apply inv2_car; exact Hd).
  transitivity (mul2 (mul2 a d) (mul2 (inv2 d) (inv2 c))).
  - apply (mul_shift2 a d (inv2 c) Ha Hd Hic).
  - transitivity (mul2 (mul2 b c) (mul2 (inv2 d) (inv2 c))).
    + rewrite H. reflexivity.
    + transitivity (mul2 (mul2 b c) (mul2 (inv2 c) (inv2 d))).
      * assert (Hc2 : mul2 (inv2 d) (inv2 c) = mul2 (inv2 c) (inv2 d)) by (apply (@Mult_P4 RR2 ax2 (inv2 d) (inv2 c) Hid Hic)).
        rewrite Hc2. reflexivity.
      * symmetry. apply (mul_shift2 b c (inv2 d) Hb Hc Hid).
Qed.

Lemma cross2 : ∀ m1 n1 m2 n2, m1 ∈ Z1 -> n1 ∈ Z1 -> n1 ≠ z1 -> m2 ∈ Z1 -> n2 ∈ Z1 -> n2 ≠ z1
  -> mul1 m1 n2 = mul1 m2 n1 -> mul2 (sigZ m1) (inv2 (sigZ n1)) = mul2 (sigZ m2) (inv2 (sigZ n2)).
Proof.
  intros m1 n1 m2 n2 Hm1 Hn1 Hn1z Hm2 Hn2 Hn2z H.
  assert (Hm1n2Z : mul1 m1 n2 ∈ Z1) by (apply (@Int_P1b RR1 ax1 m1 n2 Hm1 Hn2)).
  assert (Hm2n1Z : mul1 m2 n1 ∈ Z1) by (apply (@Int_P1b RR1 ax1 m2 n1 Hm2 Hn1)).
  assert (Hsz : mul2 (sigZ m1) (sigZ n2) = mul2 (sigZ m2) (sigZ n1)).
  { rewrite <- (sigZ_mul m1 n2 Hm1 Hn2). rewrite <- (sigZ_mul m2 n1 Hm2 Hn1). rewrite H. reflexivity. }
  apply (frac_eq2 (sigZ m1) (sigZ m2) (sigZ n1) (sigZ n2)).
  - apply Z2_sub_car2; apply sigZ_Z2; exact Hm1.
  - apply Z2_sub_car2; apply sigZ_Z2; exact Hm2.
  - apply in_sm2; [apply Z2_sub_car2; apply sigZ_Z2; exact Hn1 | apply sigZ_ne_zero; assumption].
  - apply in_sm2; [apply Z2_sub_car2; apply sigZ_Z2; exact Hn2 | apply sigZ_ne_zero; assumption].
  - exact Hsz.
Qed.

(* ---------------- psi : Q1 -> Q2 ---------------- *)

Definition psiCand (q:Class) : Class :=
  \{ λ y, ∃ m n, m ∈ Z1 /\ n ∈ Z1 /\ n ≠ z1
        /\ q = mul1 m (inv1 n) /\ y = mul2 (sigZ m) (inv2 (sigZ n)) \}.

Definition psi (q:Class) : Class := ∩(psiCand q).

Lemma psi_rep : ∀ m n, m ∈ Z1 -> n ∈ Z1 -> n ≠ z1
  -> psi (mul1 m (inv1 n)) = mul2 (sigZ m) (inv2 (sigZ n)).
Proof.
  intros m n Hm Hn Hnz.
  assert (Hsm : sigZ m ∈ car2) by (apply Z2_sub_car2; apply sigZ_Z2; exact Hm).
  assert (Hsn : sigZ n ∈ car2) by (apply Z2_sub_car2; apply sigZ_Z2; exact Hn).
  assert (Hsn0 : sigZ n ≠ z2) by (apply sigZ_ne_zero; assumption).
  assert (Hin : inv2 (sigZ n) ∈ car2) by (apply inv2_car; apply in_sm2; assumption).
  assert (Hvalcar : mul2 (sigZ m) (inv2 (sigZ n)) ∈ car2) by (apply (@Mult_close RR2 ax2 (sigZ m) (inv2 (sigZ n)) Hsm Hin)).
  assert (Hset : psiCand (mul1 m (inv1 n)) = [mul2 (sigZ m) (inv2 (sigZ n))]).
  { apply AxiomI. intros y. split.
    - intros Hy. apply AxiomII in Hy as [Ey Hy'].
      destruct Hy' as [m' [n' [Hm' [Hn' [Hn'z [Hq Hyv]]]]]].
      assert (Hcross : mul1 m' n = mul1 m n').
      { apply (cross1 m' n' m n Hm' Hn' Hn'z Hm Hn Hnz). rewrite Hq. reflexivity. }
      assert (Hvals : mul2 (sigZ m') (inv2 (sigZ n')) = mul2 (sigZ m) (inv2 (sigZ n)))
        by (apply (cross2 m' n' m n Hm' Hn' Hn'z Hm Hn Hnz Hcross)).
      apply AxiomII. split; [exact Ey |].
      intros _. rewrite Hyv. exact Hvals.
    - intros Hy.
      assert (Hyeq : y = mul2 (sigZ m) (inv2 (sigZ n)))
        by (exact (proj1 (MKT41 (mul2 (sigZ m) (inv2 (sigZ n))) (Ens_car2 _ Hvalcar) y) Hy)).
      apply AxiomII in Hy as [Ey _].
      apply AxiomII. split; [exact Ey |].
      exists m, n. split; [exact Hm | split; [exact Hn | split; [exact Hnz | split; [reflexivity | exact Hyeq]]]]. }
  unfold psi. rewrite Hset. exact (proj1 (MKT44 (Ens_car2 _ Hvalcar))).
Qed.

Lemma psi_mem : ∀ q, q ∈ Q1 -> psi q ∈ car2.
Proof.
  intros q Hq.
  apply AxiomII in Hq as [_ Hq'].
  destruct Hq' as [m [n [Hm [Hn0 Hqe]]]].
  assert (Hqe' : q = mul1 m (inv1 n)) by (rewrite Hqe; reflexivity).
  assert (Hn : n ∈ Z1) by (pose proof Hn0 as H; unfold Setminus in H; apply AxiomII in H as [_ [Hn _]]; exact Hn).
  assert (Hnz : n ≠ z1).
  { pose proof Hn0 as H. unfold Setminus in H. apply AxiomII in H as [_ [_ Hnot]].
    apply AxiomII in Hnot as [_ Hnot']. intro He.
    exact (Hnot' (proj2 (MKT41 z1 (Ens_car1 z1 z1_car) n) He)). }
  rewrite Hqe'. rewrite (psi_rep m n Hm Hn Hnz).
  apply (@Mult_close RR2 ax2 (sigZ m) (inv2 (sigZ n))).
  - apply Z2_sub_car2; apply sigZ_Z2; exact Hm.
  - apply inv2_car. apply in_sm2. apply Z2_sub_car2. apply sigZ_Z2. exact Hn. apply sigZ_ne_zero; assumption.
Qed.

Lemma mul_sm2 : ∀ p q, p ∈ (car2 ~ [z2]) -> q ∈ (car2 ~ [z2]) -> mul2 p q ∈ (car2 ~ [z2]).
Proof.
  intros p q Hp Hq.
  assert (Ep : Ensemble p) by (pose proof Hp as H; unfold Setminus in H; apply AxiomII in H as [E _]; exact E).
  assert (EpR : p ∈ car2) by (apply sm2_car; exact Hp).
  assert (EqR : q ∈ car2) by (apply sm2_car; exact Hq).
  assert (HpqR : mul2 p q ∈ car2) by (apply (@Mult_close RR2 ax2 p q EpR EqR)).
  assert (Hpnot : p ∉ [z2]) by (pose proof Hp as H; unfold Setminus in H; apply AxiomII in H as [_ [_ Hnot]]; apply AxiomII in Hnot as [_ Hnot']; exact Hnot').
  assert (Hqnot : q ∉ [z2]) by (pose proof Hq as H; unfold Setminus in H; apply AxiomII in H as [_ [_ Hnot]]; apply AxiomII in Hnot as [_ Hnot']; exact Hnot').
  assert (Hne : mul2 p q ≠ z2).
  { intro He. destruct (@PlusMult_Co2 RR2 ax2 p q EpR EqR He) as [Hp0 | Hq0].
    - exact (Hpnot (proj2 (MKT41 z2 (Ens_car2 z2 z2_car) p) Hp0)).
    - exact (Hqnot (proj2 (MKT41 z2 (Ens_car2 z2 z2_car) q) Hq0)). }
  unfold Setminus. apply AxiomII. split.
  - exists car2. exact HpqR.
  - split; [exact HpqR |].
    apply AxiomII. split.
    + exists car2. exact HpqR.
    + intro Hpqin. exact (Hne (proj1 (MKT41 z2 (Ens_car2 z2 z2_car) (mul2 p q)) Hpqin)).
Qed.

Lemma inv2_mul : ∀ p q, p ∈ (car2 ~ [z2]) -> q ∈ (car2 ~ [z2])
  -> inv2 (mul2 p q) = mul2 (inv2 p) (inv2 q).
Proof.
  intros p q Hp Hq.
  assert (Hpq : mul2 p q ∈ (car2 ~ [z2])) by (apply mul_sm2; assumption).
  assert (Hip : inv2 p ∈ (car2 ~ [z2])) by (apply (@Mult_inv1 RR2 ax2 p Hp)).
  assert (Hiq : inv2 q ∈ (car2 ~ [z2])) by (apply (@Mult_inv1 RR2 ax2 q Hq)).
  assert (Hipiq : mul2 (inv2 p) (inv2 q) ∈ (car2 ~ [z2])) by (apply mul_sm2; assumption).
  assert (Hsum : mul2 (mul2 p q) (mul2 (inv2 p) (inv2 q)) = o2).
  { assert (EpR : p ∈ car2) by (apply sm2_car; exact Hp).
    assert (EqR : q ∈ car2) by (apply sm2_car; exact Hq).
    assert (Eip : inv2 p ∈ car2) by (apply inv2_car; exact Hp).
    assert (Eiq : inv2 q ∈ car2) by (apply inv2_car; exact Hq).
    assert (Epq : mul2 p q ∈ car2) by (apply (@Mult_close RR2 ax2 p q EpR EqR)).
    assert (Eipiq : mul2 (inv2 p) (inv2 q) ∈ car2) by (apply (@Mult_close RR2 ax2 (inv2 p) (inv2 q) Eip Eiq)).
    assert (Hc1 : mul2 p (inv2 p) = o2) by (apply inv2_val; exact Hp).
    assert (Hc2 : mul2 q (inv2 q) = o2) by (apply inv2_val; exact Hq).
    assert (Hre : mul2 (mul2 p q) (mul2 (inv2 p) (inv2 q)) = mul2 (mul2 p (inv2 p)) (mul2 q (inv2 q))).
    { assert (A1 : mul2 (mul2 p q) (mul2 (inv2 p) (inv2 q)) = mul2 p (mul2 q (mul2 (inv2 p) (inv2 q)))) by (apply (eq_sym (@Mult_P3 RR2 ax2 p q (mul2 (inv2 p) (inv2 q)) EpR EqR Eipiq))).
      assert (A2 : mul2 q (mul2 (inv2 p) (inv2 q)) = mul2 (mul2 q (inv2 p)) (inv2 q)) by (apply (@Mult_P3 RR2 ax2 q (inv2 p) (inv2 q) EqR Eip Eiq)).
      assert (A3 : mul2 q (inv2 p) = mul2 (inv2 p) q) by (apply (@Mult_P4 RR2 ax2 q (inv2 p) EqR Eip)).
      assert (A4 : mul2 (mul2 (inv2 p) q) (inv2 q) = mul2 (inv2 p) (mul2 q (inv2 q))) by (apply (eq_sym (@Mult_P3 RR2 ax2 (inv2 p) q (inv2 q) Eip EqR Eiq))).
      assert (A5 : mul2 (mul2 p (inv2 p)) (mul2 q (inv2 q)) = mul2 p (mul2 (inv2 p) (mul2 q (inv2 q)))) by (apply (eq_sym (@Mult_P3 RR2 ax2 p (inv2 p) (mul2 q (inv2 q)) EpR Eip (@Mult_close RR2 ax2 q (inv2 q) EqR Eiq)))).
      rewrite A1. rewrite A2. rewrite A3. rewrite A4.
      assert (A6 : mul2 p (mul2 (inv2 p) (mul2 q (inv2 q))) = mul2 (mul2 p (inv2 p)) (mul2 q (inv2 q))) by (apply (@Mult_P3 RR2 ax2 p (inv2 p) (mul2 q (inv2 q)) EpR Eip (@Mult_close RR2 ax2 q (inv2 q) EqR Eiq))).
      rewrite A6. reflexivity. }
    rewrite Hre. rewrite Hc1. rewrite Hc2.
    assert (Hoo : mul2 o2 o2 = o2) by (apply (eq_trans (@Mult_P4 RR2 ax2 o2 o2 o2_car o2_car) (@Mult_P1 RR2 ax2 o2 o2_car))).
    exact Hoo. }
  destruct (@Mult_Co2 RR2 ax2 (mul2 p q) Hpq) as [x [[Hx0 Hxsum] Huniq]].
  assert (Ha : inv2 (mul2 p q) = x) by (symmetry; apply Huniq; split; [apply (@Mult_inv1 RR2 ax2 (mul2 p q) Hpq) | apply (@Mult_inv2 RR2 ax2 (mul2 p q) Hpq)]).
  assert (Hb : mul2 (inv2 p) (inv2 q) = x) by (symmetry; apply Huniq; split; [exact Hipiq | exact Hsum]).
  rewrite Ha. rewrite Hb. reflexivity.
Qed.

Lemma inv1_one : inv1 o1 = o1.
Proof.
  assert (Hsm : o1 ∈ (car1 ~ [z1])) by (apply in_sm1; [exact o1_car | intro H; exact ((proj2 (@OrderPM_Co9 RR1 ax1)) (eq_sym H))]).
  destruct (@Mult_Co2 RR1 ax1 o1 Hsm) as [x [[Hx0 Hxsum] Huniq]].
  assert (Ha : inv1 o1 = x) by (symmetry; apply Huniq; split; [apply (@Mult_inv1 RR1 ax1 o1 Hsm) | apply (@Mult_inv2 RR1 ax1 o1 Hsm)]).
  assert (Hb : o1 = x) by (symmetry; apply Huniq; split; [exact Hsm | apply (@Mult_P1 RR1 ax1 o1 o1_car)]).
  rewrite Ha. rewrite Hb. reflexivity.
Qed.

Lemma inv2_one : inv2 o2 = o2.
Proof.
  assert (Hsm : o2 ∈ (car2 ~ [z2])) by (apply in_sm2; [exact o2_car | intro H; exact ((proj2 (@OrderPM_Co9 RR2 ax2)) (eq_sym H))]).
  destruct (@Mult_Co2 RR2 ax2 o2 Hsm) as [x [[Hx0 Hxsum] Huniq]].
  assert (Ha : inv2 o2 = x) by (symmetry; apply Huniq; split; [apply (@Mult_inv1 RR2 ax2 o2 Hsm) | apply (@Mult_inv2 RR2 ax2 o2 Hsm)]).
  assert (Hb : o2 = x) by (symmetry; apply Huniq; split; [exact Hsm | apply (@Mult_P1 RR2 ax2 o2 o2_car)]).
  rewrite Ha. rewrite Hb. reflexivity.
Qed.

Lemma psi_one : psi o1 = o2.
Proof.
  assert (Hne : o1 ≠ z1) by (intro H; exact ((proj2 (@OrderPM_Co9 RR1 ax1)) (eq_sym H))).
  assert (Hprod : mul1 o1 (inv1 o1) = o1) by (rewrite inv1_one; apply (@Mult_P1 RR1 ax1 o1 o1_car)).
  rewrite <- Hprod.
  rewrite (psi_rep o1 o1 (N1_in_Z1 o1 (@one_in_N RR1 ax1)) (N1_in_Z1 o1 (@one_in_N RR1 ax1)) Hne).
  rewrite sigZ_one. rewrite inv2_one.
  apply (@Mult_P1 RR2 ax2 o2 o2_car).
Qed.

Lemma psi_zero : psi z1 = z2.
Proof.
  assert (Hne : o1 ≠ z1) by (intro H; exact ((proj2 (@OrderPM_Co9 RR1 ax1)) (eq_sym H))).
  assert (Hprod : mul1 z1 (inv1 o1) = z1)
    by (rewrite inv1_one; apply (eq_trans (@Mult_P4 RR1 ax1 z1 o1 z1_car o1_car) (@PlusMult_Co1 RR1 ax1 o1 o1_car))).
  rewrite <- Hprod.
  rewrite (psi_rep z1 o1 Z1_zero (N1_in_Z1 o1 (@one_in_N RR1 ax1)) Hne).
  rewrite sigZ_zero. rewrite sigZ_one. rewrite inv2_one.
  apply (eq_trans (@Mult_P4 RR2 ax2 z2 o2 z2_car o2_car) (@PlusMult_Co1 RR2 ax2 o2 o2_car)).
Qed.

Lemma add_frac1 : ∀ a b c, a ∈ car1 -> b ∈ car1 -> c ∈ (car1 ~ [z1])
  -> add1 (mul1 a (inv1 c)) (mul1 b (inv1 c)) = mul1 (add1 a b) (inv1 c).
Proof. intros a b c Ha Hb Hc. symmetry. apply (@Mult_P5 RR1 ax1 a b (inv1 c) Ha Hb (inv1_car c Hc)). Qed.

Lemma add_frac2 : ∀ a b c, a ∈ car2 -> b ∈ car2 -> c ∈ (car2 ~ [z2])
  -> add2 (mul2 a (inv2 c)) (mul2 b (inv2 c)) = mul2 (add2 a b) (inv2 c).
Proof. intros a b c Ha Hb Hc. symmetry. apply (@Mult_P5 RR2 ax2 a b (inv2 c) Ha Hb (inv2_car c Hc)). Qed.

Lemma mul_sm1 : ∀ p q, p ∈ (car1 ~ [z1]) -> q ∈ (car1 ~ [z1]) -> mul1 p q ∈ (car1 ~ [z1]).
Proof.
  intros p q Hp Hq.
  assert (Ep : Ensemble p) by (pose proof Hp as H; unfold Setminus in H; apply AxiomII in H as [E _]; exact E).
  assert (EpR : p ∈ car1) by (apply sm1_car; exact Hp).
  assert (EqR : q ∈ car1) by (apply sm1_car; exact Hq).
  assert (HpqR : mul1 p q ∈ car1) by (apply (@Mult_close RR1 ax1 p q EpR EqR)).
  assert (Hpnot : p ∉ [z1]) by (pose proof Hp as H; unfold Setminus in H; apply AxiomII in H as [_ [_ Hnot]]; apply AxiomII in Hnot as [_ Hnot']; exact Hnot').
  assert (Hqnot : q ∉ [z1]) by (pose proof Hq as H; unfold Setminus in H; apply AxiomII in H as [_ [_ Hnot]]; apply AxiomII in Hnot as [_ Hnot']; exact Hnot').
  assert (Hne : mul1 p q ≠ z1).
  { intro He. destruct (@PlusMult_Co2 RR1 ax1 p q EpR EqR He) as [Hp0 | Hq0].
    - exact (Hpnot (proj2 (MKT41 z1 (Ens_car1 z1 z1_car) p) Hp0)).
    - exact (Hqnot (proj2 (MKT41 z1 (Ens_car1 z1 z1_car) q) Hq0)). }
  unfold Setminus. apply AxiomII. split.
  - exists car1. exact HpqR.
  - split; [exact HpqR |].
    apply AxiomII. split.
    + exists car1. exact HpqR.
    + intro Hpqin. exact (Hne (proj1 (MKT41 z1 (Ens_car1 z1 z1_car) (mul1 p q)) Hpqin)).
Qed.

Lemma frac_add1 : ∀ m n m' n', m ∈ Z1 -> n ∈ Z1 -> n ≠ z1 -> m' ∈ Z1 -> n' ∈ Z1 -> n' ≠ z1
  -> add1 (mul1 m (inv1 n)) (mul1 m' (inv1 n'))
     = mul1 (add1 (mul1 m n') (mul1 m' n)) (inv1 (mul1 n n')).
Proof.
  intros m n m' n' Hm Hn Hnz Hm' Hn' Hn'z.
  assert (HmR : m ∈ car1) by (apply Z1_sub_car1; exact Hm).
  assert (HnR : n ∈ car1) by (apply Z1_sub_car1; exact Hn).
  assert (Hm'R : m' ∈ car1) by (apply Z1_sub_car1; exact Hm').
  assert (Hn'R : n' ∈ car1) by (apply Z1_sub_car1; exact Hn').
  assert (Hnn' : mul1 n n' ∈ (car1 ~ [z1])) by (apply mul_sm1; [apply in_sm1; assumption | apply in_sm1; assumption]).
  assert (H1 : mul1 m (inv1 n) = mul1 (mul1 m n') (inv1 (mul1 n n')))
    by (apply (@Frac_P1 RR1 ax1 m n n' HmR (in_sm1 n HnR Hnz) (in_sm1 n' Hn'R Hn'z))).
  assert (H2 : mul1 m' (inv1 n') = mul1 (mul1 m' n) (inv1 (mul1 n n'))).
  { assert (H2a : mul1 m' (inv1 n') = mul1 (mul1 m' n) (inv1 (mul1 n' n)))
      by (apply (@Frac_P1 RR1 ax1 m' n' n Hm'R (in_sm1 n' Hn'R Hn'z) (in_sm1 n HnR Hnz))).
    rewrite H2a.
    assert (Hc : mul1 n' n = mul1 n n') by (apply (@Mult_P4 RR1 ax1 n' n Hn'R HnR)).
    rewrite Hc. reflexivity. }
  rewrite H1. rewrite H2.
  apply (add_frac1 (mul1 m n') (mul1 m' n) (mul1 n n')).
  - apply (@Mult_close RR1 ax1 m n' HmR Hn'R).
  - apply (@Mult_close RR1 ax1 m' n Hm'R HnR).
  - exact Hnn'.
Qed.

Lemma sm1_ne : ∀ x, x ∈ (car1 ~ [z1]) -> x ≠ z1.
Proof. intros x Hx He. pose proof Hx as H; unfold Setminus in H; apply AxiomII in H as [_ [_ Hnot]]; apply AxiomII in Hnot as [_ Hnot']; exact (Hnot' (proj2 (MKT41 z1 (Ens_car1 z1 z1_car) x) He)). Qed.
Lemma sm2_ne : ∀ x, x ∈ (car2 ~ [z2]) -> x ≠ z2.
Proof. intros x Hx He. pose proof Hx as H; unfold Setminus in H; apply AxiomII in H as [_ [_ Hnot]]; apply AxiomII in Hnot as [_ Hnot']; exact (Hnot' (proj2 (MKT41 z2 (Ens_car2 z2 z2_car) x) He)). Qed.

Lemma frac_expand2 : ∀ a b c, a ∈ car2 -> b ∈ (car2 ~ [z2]) -> c ∈ (car2 ~ [z2])
  -> mul2 a (inv2 b) = mul2 (mul2 a c) (inv2 (mul2 b c)).
Proof.
  intros a b c Ha Hb Hc.
  assert (HcR : c ∈ car2) by (apply sm2_car; exact Hc).
  assert (Hib : inv2 b ∈ car2) by (apply inv2_car; exact Hb).
  assert (Hbc : mul2 b c ∈ (car2 ~ [z2])) by (apply mul_sm2; assumption).
  transitivity (mul2 (mul2 a c) (mul2 (inv2 c) (inv2 b))).
  - apply (mul_shift2 a c (inv2 b) Ha Hc Hib).
  - assert (Hmm : mul2 (mul2 a c) (mul2 (inv2 c) (inv2 b)) = mul2 (mul2 a c) (mul2 (inv2 b) (inv2 c)))
      by (apply (f_equal (fun u => mul2 (mul2 a c) u) (@Mult_P4 RR2 ax2 (inv2 c) (inv2 b) (inv2_car c Hc) Hib))).
    rewrite Hmm.
    assert (Hinv : mul2 (inv2 b) (inv2 c) = inv2 (mul2 b c)) by (apply (eq_sym (inv2_mul b c Hb Hc))).
    rewrite Hinv. reflexivity.
Qed.

Lemma psi_add : ∀ q r, q ∈ Q1 -> r ∈ Q1 -> psi (add1 q r) = add2 (psi q) (psi r).
Proof.
  intros q r Hq Hr.
  apply AxiomII in Hq as [_ Hq']. destruct Hq' as [m [n [Hm [Hn0 Hqe]]]].
  apply AxiomII in Hr as [_ Hr']. destruct Hr' as [m' [n' [Hm' [Hn'0 Hr'e]]]].
  assert (Hqe' : q = mul1 m (inv1 n)) by (rewrite Hqe; reflexivity).
  assert (Hr'e' : r = mul1 m' (inv1 n')) by (rewrite Hr'e; reflexivity).
  assert (Hn : n ∈ Z1) by (pose proof Hn0 as H; unfold Setminus in H; apply AxiomII in H as [_ [Hn _]]; exact Hn).
  assert (Hnz : n ≠ z1) by (pose proof Hn0 as H; unfold Setminus in H; apply AxiomII in H as [_ [_ Hnot]]; apply AxiomII in Hnot as [_ Hnot']; intro He; exact (Hnot' (proj2 (MKT41 z1 (Ens_car1 z1 z1_car) n) He))).
  assert (Hn' : n' ∈ Z1) by (pose proof Hn'0 as H; unfold Setminus in H; apply AxiomII in H as [_ [Hn' _]]; exact Hn').
  assert (Hn'z : n' ≠ z1) by (pose proof Hn'0 as H; unfold Setminus in H; apply AxiomII in H as [_ [_ Hnot]]; apply AxiomII in Hnot as [_ Hnot']; intro He; exact (Hnot' (proj2 (MKT41 z1 (Ens_car1 z1 z1_car) n') He))).
  assert (HnR : n ∈ car1) by (apply Z1_sub_car1; exact Hn).
  assert (Hn'R : n' ∈ car1) by (apply Z1_sub_car1; exact Hn').
  assert (Hmn'Z : mul1 m n' ∈ Z1) by (apply (@Int_P1b RR1 ax1 m n' Hm Hn')).
  assert (Hm'nZ : mul1 m' n ∈ Z1) by (apply (@Int_P1b RR1 ax1 m' n Hm' Hn)).
  assert (HnumZ : add1 (mul1 m n') (mul1 m' n) ∈ Z1) by (apply (@Int_P1a RR1 ax1 (mul1 m n') (mul1 m' n) Hmn'Z Hm'nZ)).
  assert (Hnn'Z : mul1 n n' ∈ Z1) by (apply (@Int_P1b RR1 ax1 n n' Hn Hn')).
  assert (Hnn'sm : mul1 n n' ∈ (car1 ~ [z1])) by (apply mul_sm1; [apply in_sm1; assumption | apply in_sm1; assumption]).
  assert (Hnn'z : mul1 n n' ≠ z1) by (apply sm1_ne; exact Hnn'sm).
  rewrite Hqe'. rewrite Hr'e'.
  rewrite (frac_add1 m n m' n' Hm Hn Hnz Hm' Hn' Hn'z).
  rewrite (psi_rep (add1 (mul1 m n') (mul1 m' n)) (mul1 n n') HnumZ Hnn'Z Hnn'z).
  rewrite (sigZ_add (mul1 m n') (mul1 m' n) Hmn'Z Hm'nZ).
  rewrite (sigZ_mul m n' Hm Hn'). rewrite (sigZ_mul m' n Hm' Hn).
  rewrite (sigZ_mul n n' Hn Hn').
  rewrite (psi_rep m n Hm Hn Hnz). rewrite (psi_rep m' n' Hm' Hn' Hn'z).
  assert (Hsm : sigZ m ∈ car2) by (apply Z2_sub_car2; apply sigZ_Z2; exact Hm).
  assert (Hsm' : sigZ m' ∈ car2) by (apply Z2_sub_car2; apply sigZ_Z2; exact Hm').
  assert (Hsn_sm : sigZ n ∈ (car2 ~ [z2])) by (apply in_sm2; [apply Z2_sub_car2; apply sigZ_Z2; exact Hn | apply sigZ_ne_zero; assumption]).
  assert (Hsn'_sm : sigZ n' ∈ (car2 ~ [z2])) by (apply in_sm2; [apply Z2_sub_car2; apply sigZ_Z2; exact Hn' | apply sigZ_ne_zero; assumption]).
  assert (HD_sm : mul2 (sigZ n) (sigZ n') ∈ (car2 ~ [z2])) by (apply mul_sm2; assumption).
  assert (HA : mul2 (sigZ m) (sigZ n') ∈ car2) by (apply (@Mult_close RR2 ax2 (sigZ m) (sigZ n') Hsm (sm2_car _ Hsn'_sm))).
  assert (HB : mul2 (sigZ m') (sigZ n) ∈ car2) by (apply (@Mult_close RR2 ax2 (sigZ m') (sigZ n) Hsm' (sm2_car _ Hsn_sm))).
  assert (E1 : mul2 (sigZ m) (inv2 (sigZ n)) = mul2 (mul2 (sigZ m) (sigZ n')) (inv2 (mul2 (sigZ n) (sigZ n'))))
    by (apply (frac_expand2 (sigZ m) (sigZ n) (sigZ n') Hsm Hsn_sm Hsn'_sm)).
  assert (E2 : mul2 (sigZ m') (inv2 (sigZ n')) = mul2 (mul2 (sigZ m') (sigZ n)) (inv2 (mul2 (sigZ n) (sigZ n')))).
  { assert (E2a : mul2 (sigZ m') (inv2 (sigZ n')) = mul2 (mul2 (sigZ m') (sigZ n)) (inv2 (mul2 (sigZ n') (sigZ n))))
      by (apply (frac_expand2 (sigZ m') (sigZ n') (sigZ n) Hsm' Hsn'_sm Hsn_sm)).
    rewrite E2a.
    assert (E2b : mul2 (sigZ n') (sigZ n) = mul2 (sigZ n) (sigZ n')) by (apply (@Mult_P4 RR2 ax2 (sigZ n') (sigZ n) (sm2_car _ Hsn'_sm) (sm2_car _ Hsn_sm))).
    rewrite E2b. reflexivity. }
  rewrite E1. rewrite E2.
  apply (eq_sym (add_frac2 (mul2 (sigZ m) (sigZ n')) (mul2 (sigZ m') (sigZ n)) (mul2 (sigZ n) (sigZ n')) HA HB HD_sm)).
Qed.

Lemma mul_frac1 : ∀ m n m' n', m ∈ Z1 -> n ∈ Z1 -> n ≠ z1 -> m' ∈ Z1 -> n' ∈ Z1 -> n' ≠ z1
  -> mul1 (mul1 m (inv1 n)) (mul1 m' (inv1 n')) = mul1 (mul1 m m') (inv1 (mul1 n n')).
Proof.
  intros m n m' n' Hm Hn Hnz Hm' Hn' Hn'z.
  assert (HmR : m ∈ car1) by (apply Z1_sub_car1; exact Hm).
  assert (HnR : n ∈ car1) by (apply Z1_sub_car1; exact Hn).
  assert (Hm'R : m' ∈ car1) by (apply Z1_sub_car1; exact Hm').
  assert (Hn'R : n' ∈ car1) by (apply Z1_sub_car1; exact Hn').
  apply (@Frac_P2 RR1 ax1 m n m' n' HmR (in_sm1 n HnR Hnz) Hm'R (in_sm1 n' Hn'R Hn'z)).
Qed.

Lemma mul4_regroup : ∀ a b c d, a ∈ car2 -> b ∈ car2 -> c ∈ car2 -> d ∈ car2
  -> mul2 (mul2 a b) (mul2 c d) = mul2 (mul2 a c) (mul2 b d).
Proof.
  intros a b c d Ha Hb Hc Hd.
  assert (Hcd : mul2 c d ∈ car2) by (apply (@Mult_close RR2 ax2 c d Hc Hd)).
  assert (Hbd : mul2 b d ∈ car2) by (apply (@Mult_close RR2 ax2 b d Hb Hd)).
  transitivity (mul2 a (mul2 b (mul2 c d))).
  - apply (eq_sym (@Mult_P3 RR2 ax2 a b (mul2 c d) Ha Hb Hcd)).
  - transitivity (mul2 a (mul2 (mul2 b c) d)).
    + assert (H1 : mul2 b (mul2 c d) = mul2 (mul2 b c) d) by (apply (@Mult_P3 RR2 ax2 b c d Hb Hc Hd)).
      rewrite H1. reflexivity.
    + transitivity (mul2 a (mul2 (mul2 c b) d)).
      * assert (H2 : mul2 b c = mul2 c b) by (apply (@Mult_P4 RR2 ax2 b c Hb Hc)).
        rewrite H2. reflexivity.
      * transitivity (mul2 a (mul2 c (mul2 b d))).
        { assert (H3 : mul2 (mul2 c b) d = mul2 c (mul2 b d)) by (apply (eq_sym (@Mult_P3 RR2 ax2 c b d Hc Hb Hd))).
          rewrite H3. reflexivity. }
        { apply (@Mult_P3 RR2 ax2 a c (mul2 b d) Ha Hc Hbd). }
Qed.

Lemma psi_mul : ∀ q r, q ∈ Q1 -> r ∈ Q1 -> psi (mul1 q r) = mul2 (psi q) (psi r).
Proof.
  intros q r Hq Hr.
  apply AxiomII in Hq as [_ Hq']. destruct Hq' as [m [n [Hm [Hn0 Hqe]]]].
  apply AxiomII in Hr as [_ Hr']. destruct Hr' as [m' [n' [Hm' [Hn'0 Hr'e]]]].
  assert (Hqe' : q = mul1 m (inv1 n)) by (rewrite Hqe; reflexivity).
  assert (Hr'e' : r = mul1 m' (inv1 n')) by (rewrite Hr'e; reflexivity).
  assert (Hn : n ∈ Z1) by (pose proof Hn0 as H; unfold Setminus in H; apply AxiomII in H as [_ [Hn _]]; exact Hn).
  assert (Hnz : n ≠ z1) by (pose proof Hn0 as H; unfold Setminus in H; apply AxiomII in H as [_ [_ Hnot]]; apply AxiomII in Hnot as [_ Hnot']; intro He; exact (Hnot' (proj2 (MKT41 z1 (Ens_car1 z1 z1_car) n) He))).
  assert (Hn' : n' ∈ Z1) by (pose proof Hn'0 as H; unfold Setminus in H; apply AxiomII in H as [_ [Hn' _]]; exact Hn').
  assert (Hn'z : n' ≠ z1) by (pose proof Hn'0 as H; unfold Setminus in H; apply AxiomII in H as [_ [_ Hnot]]; apply AxiomII in Hnot as [_ Hnot']; intro He; exact (Hnot' (proj2 (MKT41 z1 (Ens_car1 z1 z1_car) n') He))).
  assert (HnR : n ∈ car1) by (apply Z1_sub_car1; exact Hn).
  assert (Hn'R : n' ∈ car1) by (apply Z1_sub_car1; exact Hn').
  assert (Hmm'Z : mul1 m m' ∈ Z1) by (apply (@Int_P1b RR1 ax1 m m' Hm Hm')).
  assert (Hnn'Z : mul1 n n' ∈ Z1) by (apply (@Int_P1b RR1 ax1 n n' Hn Hn')).
  assert (Hnn'z : mul1 n n' ≠ z1) by (apply sm1_ne; apply mul_sm1; [apply in_sm1; assumption | apply in_sm1; assumption]).
  rewrite Hqe'. rewrite Hr'e'.
  rewrite (mul_frac1 m n m' n' Hm Hn Hnz Hm' Hn' Hn'z).
  rewrite (psi_rep (mul1 m m') (mul1 n n') Hmm'Z Hnn'Z Hnn'z).
  rewrite (sigZ_mul m m' Hm Hm'). rewrite (sigZ_mul n n' Hn Hn').
  rewrite (psi_rep m n Hm Hn Hnz). rewrite (psi_rep m' n' Hm' Hn' Hn'z).
  assert (Hsm : sigZ m ∈ car2) by (apply Z2_sub_car2; apply sigZ_Z2; exact Hm).
  assert (Hsm' : sigZ m' ∈ car2) by (apply Z2_sub_car2; apply sigZ_Z2; exact Hm').
  assert (Hsn_sm : sigZ n ∈ (car2 ~ [z2])) by (apply in_sm2; [apply Z2_sub_car2; apply sigZ_Z2; exact Hn | apply sigZ_ne_zero; assumption]).
  assert (Hsn'_sm : sigZ n' ∈ (car2 ~ [z2])) by (apply in_sm2; [apply Z2_sub_car2; apply sigZ_Z2; exact Hn' | apply sigZ_ne_zero; assumption]).
  assert (Hin : inv2 (sigZ n) ∈ car2) by (apply inv2_car; exact Hsn_sm).
  assert (Hin' : inv2 (sigZ n') ∈ car2) by (apply inv2_car; exact Hsn'_sm).
  assert (Hnn'_sm : mul2 (sigZ n) (sigZ n') ∈ (car2 ~ [z2])) by (apply mul_sm2; assumption).
  assert (Einv : inv2 (mul2 (sigZ n) (sigZ n')) = mul2 (inv2 (sigZ n)) (inv2 (sigZ n'))) by (apply (inv2_mul (sigZ n) (sigZ n') Hsn_sm Hsn'_sm)).
  rewrite Einv.
  apply (mul4_regroup (sigZ m) (sigZ m') (inv2 (sigZ n)) (inv2 (sigZ n')) Hsm Hsm' Hin Hin').
Qed.

Lemma neg_mul1 : ∀ a b, a ∈ car1 -> b ∈ car1 -> neg1 (mul1 a b) = mul1 (neg1 a) b.
Proof.
  intros a b Ha Hb.
  assert (Hc : mul1 a b = mul1 b a) by (apply (@Mult_P4 RR1 ax1 a b Ha Hb)).
  rewrite Hc. rewrite (mul_neg1 b a Hb Ha).
  assert (Hc2 : mul1 b (neg1 a) = mul1 (neg1 a) b) by (apply (@Mult_P4 RR1 ax1 b (neg1 a) Hb (neg1_car a Ha))).
  rewrite Hc2. reflexivity.
Qed.

Lemma neg_mul2 : ∀ a b, a ∈ car2 -> b ∈ car2 -> neg2 (mul2 a b) = mul2 (neg2 a) b.
Proof.
  intros a b Ha Hb.
  assert (Hc : mul2 a b = mul2 b a) by (apply (@Mult_P4 RR2 ax2 a b Ha Hb)).
  rewrite Hc. rewrite (mul_neg2 b a Hb Ha).
  assert (Hc2 : mul2 b (neg2 a) = mul2 (neg2 a) b) by (apply (@Mult_P4 RR2 ax2 b (neg2 a) Hb (neg2_car a Ha))).
  rewrite Hc2. reflexivity.
Qed.

Lemma psi_neg : ∀ q, q ∈ Q1 -> psi (neg1 q) = neg2 (psi q).
Proof.
  intros q Hq.
  apply AxiomII in Hq as [_ Hq']. destruct Hq' as [m [n [Hm [Hn0 Hqe]]]].
  assert (Hqe' : q = mul1 m (inv1 n)) by (rewrite Hqe; reflexivity).
  assert (Hn : n ∈ Z1) by (pose proof Hn0 as H; unfold Setminus in H; apply AxiomII in H as [_ [Hn _]]; exact Hn).
  assert (Hnz : n ≠ z1) by (pose proof Hn0 as H; unfold Setminus in H; apply AxiomII in H as [_ [_ Hnot]]; apply AxiomII in Hnot as [_ Hnot']; intro He; exact (Hnot' (proj2 (MKT41 z1 (Ens_car1 z1 z1_car) n) He))).
  assert (HmR : m ∈ car1) by (apply Z1_sub_car1; exact Hm).
  assert (HnR : n ∈ car1) by (apply Z1_sub_car1; exact Hn).
  assert (Hnm : neg1 m ∈ Z1) by (apply Z1_neg; exact Hm).
  assert (Hinvn : inv1 n ∈ car1) by (apply inv1_car; apply in_sm1; assumption).
  rewrite Hqe'.
  assert (Hneg : neg1 (mul1 m (inv1 n)) = mul1 (neg1 m) (inv1 n)) by (apply (neg_mul1 m (inv1 n) HmR Hinvn)).
  rewrite Hneg.
  rewrite (psi_rep (neg1 m) n Hnm Hn Hnz).
  rewrite (psi_rep m n Hm Hn Hnz).
  rewrite (sigZ_neg m Hm).
  assert (Hsm : sigZ m ∈ car2) by (apply Z2_sub_car2; apply sigZ_Z2; exact Hm).
  assert (Hin : inv2 (sigZ n) ∈ car2) by (apply inv2_car; apply in_sm2; [apply Z2_sub_car2; apply sigZ_Z2; exact Hn | apply sigZ_ne_zero; assumption]).
  symmetry. apply (neg_mul2 (sigZ m) (inv2 (sigZ n)) Hsm Hin).
Qed.

Lemma N1_pos : ∀ a, a ∈ N1 -> lt1 z1 a.
Proof. intros a Ha. apply (@Order_Co2 RR1 ax1 z1 o1 a z1_car o1_car (N1_sub_car1 a Ha)); left; split; [exact (@OrderPM_Co9 RR1 ax1) | exact (proj2 (proj2 (@one_is_min_in_N RR1 ax1)) a Ha)]. Qed.
Lemma N2_pos : ∀ a, a ∈ N2 -> lt2 z2 a.
Proof. intros a Ha. apply (@Order_Co2 RR2 ax2 z2 o2 a z2_car o2_car (N2_sub_car2 a Ha)); left; split; [exact (@OrderPM_Co9 RR2 ax2) | exact (proj2 (proj2 (@one_is_min_in_N RR2 ax2)) a Ha)]. Qed.

Lemma negN1_neg : ∀ a, neg1 a ∈ N1 -> lt1 a z1.
Proof.
  intros a Ha.
  assert (H1 : lt1 z1 (neg1 a)) by (apply N1_pos; exact Ha).
  assert (Hac : a ∈ car1) by (apply (neg1_back a); apply N1_sub_car1; exact Ha).
  assert (Hc : lt1 (neg1 (neg1 a)) z1) by (apply (@OrderPM_Co2a RR1 ax1 (neg1 a) (N1_sub_car1 (neg1 a) Ha) H1)).
  rewrite (neg1_invol a Hac) in Hc. exact Hc.
Qed.

Lemma neg2_sm : ∀ x, x ∈ (car2 ~ [z2]) -> neg2 x ∈ (car2 ~ [z2]).
Proof.
  intros x Hx.
  assert (HxR : x ∈ car2) by (apply sm2_car; exact Hx).
  assert (Hxne : x ≠ z2) by (apply sm2_ne; exact Hx).
  assert (HnegR : neg2 x ∈ car2) by (apply neg2_car; exact HxR).
  assert (Hnegne : neg2 x ≠ z2).
  { intro H. apply Hxne. rewrite <- (neg2_invol x HxR). rewrite H. apply neg2_zero. }
  unfold Setminus. apply AxiomII. split.
  - exists car2. exact HnegR.
  - split; [exact HnegR |]. apply AxiomII. split; [exists car2; exact HnegR | intro Hin; exact (Hnegne (proj1 (MKT41 z2 (Ens_car2 z2 z2_car) (neg2 x)) Hin))].
Qed.

Lemma inv2_neg : ∀ x, x ∈ (car2 ~ [z2]) -> inv2 (neg2 x) = neg2 (inv2 x).
Proof.
  intros x Hx.
  assert (Hnx : neg2 x ∈ (car2 ~ [z2])) by (apply neg2_sm; exact Hx).
  assert (Hix : inv2 x ∈ (car2 ~ [z2])) by (apply (@Mult_inv1 RR2 ax2 x Hx)).
  assert (Hnix : neg2 (inv2 x) ∈ (car2 ~ [z2])) by (apply neg2_sm; exact Hix).
  destruct (@Mult_Co2 RR2 ax2 (neg2 x) Hnx) as [y [[Hy0 Hysum] Huniq]].
  assert (Ha : inv2 (neg2 x) = y) by (symmetry; apply Huniq; split; [apply (@Mult_inv1 RR2 ax2 (neg2 x) Hnx) | apply (@Mult_inv2 RR2 ax2 (neg2 x) Hnx)]).
  assert (Hb : neg2 (inv2 x) = y) by (symmetry; apply Huniq; split; [exact Hnix | apply (eq_trans (mul_negneg2 x (inv2 x) (sm2_car x Hx) (inv2_car x Hx)) (inv2_val x Hx))]).
  rewrite Ha. rewrite Hb. reflexivity.
Qed.

Lemma neg1_sm : ∀ x, x ∈ (car1 ~ [z1]) -> neg1 x ∈ (car1 ~ [z1]).
Proof.
  intros x Hx.
  assert (HxR : x ∈ car1) by (apply sm1_car; exact Hx).
  assert (Hxne : x ≠ z1) by (apply sm1_ne; exact Hx).
  assert (HnegR : neg1 x ∈ car1) by (apply neg1_car; exact HxR).
  assert (Hnegne : neg1 x ≠ z1).
  { intro H. apply Hxne. rewrite <- (neg1_invol x HxR). rewrite H. apply neg1_z1. }
  unfold Setminus. apply AxiomII. split.
  - exists car1. exact HnegR.
  - split; [exact HnegR |]. apply AxiomII. split; [exists car1; exact HnegR | intro Hin; exact (Hnegne (proj1 (MKT41 z1 (Ens_car1 z1 z1_car) (neg1 x)) Hin))].
Qed.

Lemma inv1_neg1 : ∀ x, x ∈ (car1 ~ [z1]) -> inv1 (neg1 x) = neg1 (inv1 x).
Proof.
  intros x Hx.
  assert (Hnx : neg1 x ∈ (car1 ~ [z1])) by (apply neg1_sm; exact Hx).
  assert (Hix : inv1 x ∈ (car1 ~ [z1])) by (apply (@Mult_inv1 RR1 ax1 x Hx)).
  assert (Hnix : neg1 (inv1 x) ∈ (car1 ~ [z1])) by (apply neg1_sm; exact Hix).
  destruct (@Mult_Co2 RR1 ax1 (neg1 x) Hnx) as [y [[Hy0 Hysum] Huniq]].
  assert (Ha : inv1 (neg1 x) = y) by (symmetry; apply Huniq; split; [apply (@Mult_inv1 RR1 ax1 (neg1 x) Hnx) | apply (@Mult_inv2 RR1 ax1 (neg1 x) Hnx)]).
  assert (Hb : neg1 (inv1 x) = y) by (symmetry; apply Huniq; split; [exact Hnix | apply (eq_trans (mul_negneg1 x (inv1 x) (sm1_car x Hx) (inv1_car x Hx)) (inv1_val x Hx))]).
  rewrite Ha. rewrite Hb. reflexivity.
Qed.

Lemma negpos1 : ∀ a, a ∈ car1 -> lt1 a z1 -> lt1 z1 (neg1 a).
Proof.
  intros a Ha Ha0.
  assert (HnaR : neg1 a ∈ car1) by (apply neg1_car; exact Ha).
  assert (Ht : lt1 (add1 a (neg1 a)) (add1 z1 (neg1 a))) by (apply (@OrderPM_Co1 RR1 ax1 a z1 (neg1 a) Ha z1_car HnaR); exact Ha0).
  assert (He : add1 a (neg1 a) = z1) by (apply (@Plus_neg2 RR1 ax1 a Ha)).
  assert (He2 : add1 z1 (neg1 a) = neg1 a) by (apply (eq_trans (@Plus_P4 RR1 ax1 z1 (neg1 a) z1_car HnaR) (@Plus_P1 RR1 ax1 (neg1 a) HnaR))).
  rewrite He in Ht. rewrite He2 in Ht. exact Ht.
Qed.

Lemma psi_pos : ∀ q, q ∈ Q1 -> lt1 z1 q -> lt2 z2 (psi q).
Proof.
  intros q Hq H0q.
  apply AxiomII in Hq as [_ Hq']. destruct Hq' as [m [n [Hm [Hn0 Hqe]]]].
  assert (Hqe' : q = mul1 m (inv1 n)) by (rewrite Hqe; reflexivity).
  assert (Hn : n ∈ Z1) by (pose proof Hn0 as H; unfold Setminus in H; apply AxiomII in H as [_ [Hn _]]; exact Hn).
  assert (Hnz : n ≠ z1) by (pose proof Hn0 as H; unfold Setminus in H; apply AxiomII in H as [_ [_ Hnot]]; apply AxiomII in Hnot as [_ Hnot']; intro He; exact (Hnot' (proj2 (MKT41 z1 (Ens_car1 z1 z1_car) n) He))).
  assert (HmR : m ∈ car1) by (apply Z1_sub_car1; exact Hm).
  assert (HnR : n ∈ car1) by (apply Z1_sub_car1; exact Hn).
  assert (Hinvn : inv1 n ∈ car1) by (apply inv1_car; apply in_sm1; assumption).
  assert (HqR : q ∈ car1) by (rewrite Hqe'; apply (@Mult_close RR1 ax1 m (inv1 n) HmR Hinvn)).
  rewrite Hqe'.
  destruct (Z1_cases n Hn) as [HnN | [Hnneg | Hn0z]].
  - assert (Hnpos : lt1 z1 n) by (apply N1_pos; exact HnN).
    assert (Hmq : mul1 (mul1 m (inv1 n)) n = m).
    { transitivity (mul1 m (mul1 (inv1 n) n)).
      - symmetry. apply (@Mult_P3 RR1 ax1 m (inv1 n) n HmR Hinvn HnR).
      - assert (Hc : mul1 (inv1 n) n = o1) by (apply inv1_valc; apply in_sm1; assumption).
        rewrite Hc. apply (@Mult_P1 RR1 ax1 m HmR). }
    assert (Hmeq : m = mul1 q n).
    { transitivity (mul1 (mul1 m (inv1 n)) n).
      - exact (eq_sym Hmq).
      - symmetry. apply (f_equal (fun u => mul1 u n) Hqe'). }
    assert (Hmpos : lt1 z1 m) by (rewrite Hmeq; apply (@OrderPM_Co5 RR1 ax1 q n HqR HnR); left; split; assumption).
    assert (HmN : m ∈ N1) by (apply Z1_pos_N; assumption).
    rewrite (psi_rep m n Hm Hn Hnz).
    rewrite (sigZ_eq_N m HmN). rewrite (sigZ_eq_N n HnN).
    assert (Hsm : lt2 z2 (sigN m)) by (apply N2_pos; apply sigN_N2; exact HmN).
    assert (Hsn : lt2 z2 (sigN n)) by (apply N2_pos; apply sigN_N2; exact HnN).
    assert (Hin : lt2 z2 (inv2 (sigN n))) by (apply (@OrderPM_Co10 RR2 ax2 (sigN n) (N2_sub_car2 (sigN n) (sigN_N2 n HnN)) Hsn)).
    apply (@OrderPM_Co5 RR2 ax2 (sigN m) (inv2 (sigN n)) (N2_sub_car2 (sigN m) (sigN_N2 m HmN)) (inv2_car (sigN n) (in_sm2 (sigN n) (N2_sub_car2 (sigN n) (sigN_N2 n HnN)) (fun H => (proj2 Hsn) (eq_sym H))))).
    left. split; assumption.
  - assert (Hnnlt : lt1 n z1) by (apply negN1_neg; exact Hnneg).
    assert (Hmq : mul1 (mul1 m (inv1 n)) n = m).
    { transitivity (mul1 m (mul1 (inv1 n) n)).
      - symmetry. apply (@Mult_P3 RR1 ax1 m (inv1 n) n HmR Hinvn HnR).
      - assert (Hc : mul1 (inv1 n) n = o1) by (apply inv1_valc; apply in_sm1; assumption).
        rewrite Hc. apply (@Mult_P1 RR1 ax1 m HmR). }
    assert (Hmeq : m = mul1 q n).
    { transitivity (mul1 (mul1 m (inv1 n)) n).
      - exact (eq_sym Hmq).
      - symmetry. apply (f_equal (fun u => mul1 u n) Hqe'). }
    assert (Hmlt : lt1 m z1).
    { rewrite Hmeq.
      assert (Ht : lt1 (mul1 n q) z1) by (apply (@OrderPM_Co6 RR1 ax1 n q HnR HqR Hnnlt H0q)).
      assert (Hc : mul1 n q = mul1 q n) by (apply (@Mult_P4 RR1 ax1 n q HnR HqR)).
      rewrite Hc in Ht. exact Ht. }
    assert (Hnmpos : lt1 z1 (neg1 m)) by (apply negpos1; assumption).
    assert (HnmN : neg1 m ∈ N1) by (apply Z1_pos_N; [apply Z1_neg; exact Hm | exact Hnmpos]).
    assert (HnnN : neg1 n ∈ N1) by (exact Hnneg).
    assert (Hnnz : neg1 n ≠ z1) by (apply sm1_ne; apply in_sm1; [apply N1_sub_car1; exact HnnN | intro He; apply Hnz; rewrite <- (neg1_invol n HnR); rewrite He; apply neg1_z1]).
    assert (Hqe2 : q = mul1 (neg1 m) (inv1 (neg1 n))).
    { transitivity (mul1 m (inv1 n)).
      - exact Hqe'.
      - assert (Hinv : inv1 (neg1 n) = neg1 (inv1 n)) by (apply inv1_neg1; apply in_sm1; assumption).
        rewrite Hinv.
        exact (eq_sym (mul_negneg1 m (inv1 n) HmR Hinvn)). }
    rewrite <- Hqe'.
    rewrite Hqe2.
    rewrite (psi_rep (neg1 m) (neg1 n) (Z1_neg m Hm) (Z1_neg n Hn) Hnnz).
    rewrite (sigZ_eq_N (neg1 m) HnmN). rewrite (sigZ_eq_N (neg1 n) HnnN).
    assert (Hsm : lt2 z2 (sigN (neg1 m))) by (apply N2_pos; apply sigN_N2; exact HnmN).
    assert (Hsn : lt2 z2 (sigN (neg1 n))) by (apply N2_pos; apply sigN_N2; exact HnnN).
    assert (Hin : lt2 z2 (inv2 (sigN (neg1 n)))) by (apply (@OrderPM_Co10 RR2 ax2 (sigN (neg1 n)) (N2_sub_car2 (sigN (neg1 n)) (sigN_N2 (neg1 n) HnnN)) Hsn)).
    assert (Hin' : inv2 (sigN (neg1 n)) ∈ car2) by (apply inv2_car; apply in_sm2; [apply N2_sub_car2; apply sigN_N2; exact HnnN | intro H; exact ((proj2 Hsn) (eq_sym H))]).
    apply (@OrderPM_Co5 RR2 ax2 (sigN (neg1 m)) (inv2 (sigN (neg1 n))) (N2_sub_car2 (sigN (neg1 m)) (sigN_N2 (neg1 m) HnmN)) Hin').
    left. split; assumption.
  - exfalso. exact (Hnz Hn0z).
Qed.

(* ==================== Stage 3 : psi 是 Q1 -> Q2 的序同构 ==================== *)

Lemma psi_mono : ∀ q r, q ∈ Q1 -> r ∈ Q1 -> lt1 q r -> lt2 (psi q) (psi r).
Proof.
  intros q r Hq Hr Hqr.
  assert (HqR : q ∈ car1) by (exact (@Q_Subset_R RR1 ax1 q Hq)).
  assert (HrR : r ∈ car1) by (exact (@Q_Subset_R RR1 ax1 r Hr)).
  assert (Hnq : neg1 q ∈ Q1) by (exact (proj1 (@Rat_P3 RR1 ax1 q Hq))).
  assert (HnqR : neg1 q ∈ car1) by (apply neg1_car; exact HqR).
  assert (Hd : add1 r (neg1 q) ∈ Q1) by (exact (@Rat_P1a RR1 ax1 r (neg1 q) Hr Hnq)).
  assert (Hpos : lt1 z1 (add1 r (neg1 q))).
  { split.
    - assert (Ht : add1 q (neg1 q) = z1) by (apply (@Plus_neg2 RR1 ax1 q HqR)).
      rewrite <- Ht.
      exact (@Plus_Leq RR1 ax1 q r (neg1 q) HqR HrR HnqR (proj1 Hqr)).
    - intro Heq.
      assert (Hqe : q = r).
      { assert (H1 : add1 q (add1 r (neg1 q)) = r).
        { transitivity (add1 (add1 q r) (neg1 q)).
          - apply (@Plus_P3 RR1 ax1 q r (neg1 q) HqR HrR HnqR).
          - transitivity (add1 (add1 r q) (neg1 q)).
            + exact (f_equal (fun u => add1 u (neg1 q)) (@Plus_P4 RR1 ax1 q r HqR HrR)).
            + transitivity (add1 r (add1 q (neg1 q))).
              * symmetry. apply (@Plus_P3 RR1 ax1 r q (neg1 q) HrR HqR HnqR).
              * assert (Hc2 : add1 q (neg1 q) = z1) by (apply (@Plus_neg2 RR1 ax1 q HqR)).
                rewrite Hc2. apply (@Plus_P1 RR1 ax1 r HrR). }
        transitivity (add1 q (add1 r (neg1 q))).
        { symmetry. rewrite <- Heq. apply (@Plus_P1 RR1 ax1 q HqR). }
        { exact H1. } }
      exact ((proj2 Hqr) Hqe). }
  assert (Hpsi : lt2 z2 (psi (add1 r (neg1 q)))) by (apply psi_pos; [exact Hd | exact Hpos]).
  assert (Hr_eq : psi r = add2 (psi q) (psi (add1 r (neg1 q)))).
  { assert (Hrr : r = add1 q (add1 r (neg1 q))).
    { transitivity (add1 (add1 q r) (neg1 q)).
      - transitivity (add1 (add1 r q) (neg1 q)).
        + exact (eq_trans (eq_sym (eq_trans (f_equal (add1 r) (@Plus_neg2 RR1 ax1 q HqR)) (@Plus_P1 RR1 ax1 r HrR))) (@Plus_P3 RR1 ax1 r q (neg1 q) HrR HqR HnqR)).
        + exact (eq_sym (f_equal (fun u => add1 u (neg1 q)) (@Plus_P4 RR1 ax1 q r HqR HrR))).
      - transitivity (add1 q (add1 r (neg1 q))).
        + symmetry. apply (@Plus_P3 RR1 ax1 q r (neg1 q) HqR HrR HnqR).
        + reflexivity. }
    exact (eq_trans (f_equal psi Hrr) (psi_add q (add1 r (neg1 q)) Hq Hd)). }
  assert (Hlt := @OrderPM_Co1 RR2 ax2 z2 (psi (add1 r (neg1 q))) (psi q) z2_car (psi_mem (add1 r (neg1 q)) Hd) (psi_mem q Hq) Hpsi).
  assert (Hz2 : add2 z2 (psi q) = psi q)
    by (apply (eq_trans (@Plus_P4 RR2 ax2 z2 (psi q) z2_car (psi_mem q Hq)) (@Plus_P1 RR2 ax2 (psi q) (psi_mem q Hq)))).
  assert (Hcomm : add2 (psi (add1 r (neg1 q))) (psi q) = add2 (psi q) (psi (add1 r (neg1 q))))
    by (apply (@Plus_P4 RR2 ax2 (psi (add1 r (neg1 q))) (psi q) (psi_mem (add1 r (neg1 q)) Hd) (psi_mem q Hq))).
  exact (eq_rect (add2 z2 (psi q)) (fun u => lt2 u (psi r))
           (eq_rect (add2 (psi (add1 r (neg1 q))) (psi q)) (fun u => lt2 (add2 z2 (psi q)) u) Hlt
              (psi r) (eq_trans Hcomm (eq_sym Hr_eq)))
           (psi q) Hz2).
Qed.

Lemma psi_lt_reflect : ∀ q r, q ∈ Q1 -> r ∈ Q1 -> lt2 (psi q) (psi r) -> lt1 q r.
Proof.
  intros q r Hq Hr Hlt.
  destruct (@Order_Co1 RR1 ax1 q r (@Q_Subset_R RR1 ax1 q Hq) (@Q_Subset_R RR1 ax1 r Hr)) as [Hqr | [Hrq | Heq]].
  - exact Hqr.
  - exfalso. assert (H2 : lt2 (psi r) (psi q)) by (apply (psi_mono r q Hr Hq Hrq)).
    exact (lt2_asym (psi q) (psi r) (psi_mem q Hq) (psi_mem r Hr) Hlt H2).
  - exfalso. apply (proj2 Hlt). rewrite Heq. reflexivity.
Qed.

Lemma psi_surj : ∀ r, r ∈ Q2 -> ∃ q, q ∈ Q1 /\ psi q = r.
Proof.
  intros r Hr.
  apply AxiomII in Hr as [_ Hr'].
  destruct Hr' as [m [n [Hm [Hn Hreq]]]].
  assert (HnZ : n ∈ Z2) by (pose proof Hn as H; unfold Setminus in H; apply AxiomII in H as [_ [HnZ _]]; exact HnZ).
  assert (Hnne : n ≠ z2) by (pose proof Hn as H; unfold Setminus in H; apply AxiomII in H as [_ [_ Hnot]]; apply AxiomII in Hnot as [_ Hnot']; intro He; exact (Hnot' (proj2 (MKT41 z2 (Ens_car2 z2 z2_car) n) He))).
  destruct (sigZ_surj m Hm) as [m' [Hm' Hmval]].
  destruct (sigZ_surj n HnZ) as [n' [Hn' Hnval]].
  assert (Hn'ne : n' ≠ z1).
  { intro He. apply Hnne. rewrite <- Hnval. rewrite He. apply sigZ_zero. }
  assert (Hn'R : n' ∈ car1) by (exact (@Z1_sub_car1 n' Hn')).
  assert (Hn'0 : n' ∈ (Z1 ~ [z1])).
  { unfold Setminus. apply AxiomII. split.
    - exists car1. exact Hn'R.
    - split; [exact Hn' |]. apply AxiomII. split.
      + exists car1. exact Hn'R.
      + intro Hn'in. exact (Hn'ne (proj1 (MKT41 z1 (Ens_car1 z1 z1_car) n') Hn'in)). }
  assert (HinvR : inv1 n' ∈ car1) by (apply inv1_car; apply in_sm1; [exact Hn'R | exact Hn'ne]).
  assert (Hm'R : m' ∈ car1) by (exact (@Z1_sub_car1 m' Hm')).
  assert (Hq : mul1 m' (inv1 n') ∈ Q1).
  { apply AxiomII; split.
    - exists car1; apply (@Mult_close RR1 ax1 m' (inv1 n') Hm'R HinvR).
    - exists m', n'. split; [exact Hm' | split; [exact Hn'0 | reflexivity]]. }
  exists (mul1 m' (inv1 n')). split; [exact Hq |].
  rewrite (psi_rep m' n' Hm' Hn' Hn'ne).
  rewrite Hmval. rewrite Hnval. exact (eq_sym Hreq).
Qed.

Lemma psi_dense : ∀ a b, a ∈ car2 -> b ∈ car2 -> lt2 a b
  -> ∃ q, q ∈ Q1 /\ lt2 a (psi q) /\ lt2 (psi q) b.
Proof.
  intros a b Ha Hb Hab.
  destruct (@Arch_P9 RR2 ax2 a b Ha Hb Hab) as [r [HrQ [Har Hrb]]].
  destruct (psi_surj r HrQ) as [q [Hq Hqr]].
  exists q. split; [exact Hq |]. split.
  - rewrite Hqr. exact Har.
  - rewrite Hqr. exact Hrb.
Qed.

Lemma add1_zero1 : ∀ x, x ∈ car1 -> add1 x z1 = x.
Proof. intros x Hx. apply (@Plus_P1 RR1 ax1 x Hx). Qed.

Lemma exists_rat_lt : ∀ x, x ∈ car1 -> ∃ q, q ∈ Q1 /\ lt1 q x.
Proof.
  intros x Hx.
  assert (Hne1lt : lt1 (neg1 o1) z1) by (apply (@OrderPM_Co2a RR1 ax1 o1 o1_car (@OrderPM_Co9 RR1 ax1))).
  assert (Hx1R : add1 x (neg1 o1) ∈ car1) by (apply (@Plus_close RR1 ax1 x (neg1 o1) Hx (neg1_car o1 o1_car))).
  assert (Hlt : lt1 (add1 x (neg1 o1)) x).
  { assert (Ht : lt1 (add1 (neg1 o1) x) (add1 z1 x))
      by (apply (@OrderPM_Co1 RR1 ax1 (neg1 o1) z1 x (neg1_car o1 o1_car) z1_car Hx); exact Hne1lt).
    assert (Hcomm : add1 (neg1 o1) x = add1 x (neg1 o1))
      by (apply (@Plus_P4 RR1 ax1 (neg1 o1) x (neg1_car o1 o1_car) Hx)).
    assert (Hzx : add1 z1 x = x)
      by (apply (eq_trans (@Plus_P4 RR1 ax1 z1 x z1_car Hx) (@Plus_P1 RR1 ax1 x Hx))).
    assert (Ht1 : lt1 (add1 x (neg1 o1)) (add1 z1 x))
      by (exact (@eq_rect Class (add1 (neg1 o1) x) (fun u => lt1 u (add1 z1 x)) Ht (add1 x (neg1 o1)) Hcomm)).
    exact (lt1_rw (add1 x (neg1 o1)) (add1 x (neg1 o1)) (add1 z1 x) x eq_refl Hzx Ht1). }
  destruct (@Arch_P9 RR1 ax1 (add1 x (neg1 o1)) x Hx1R Hx Hlt) as [q [HqQ [_ Hqx]]].
  exists q. split; [exact HqQ | exact Hqx].
Qed.

Lemma exists_rat_gt : ∀ x, x ∈ car1 -> ∃ q, q ∈ Q1 /\ lt1 x q.
Proof.
  intros x Hx.
  assert (Hx1R : add1 x o1 ∈ car1) by (apply (@Plus_close RR1 ax1 x o1 Hx o1_car)).
  assert (Hlt : lt1 x (add1 x o1)) by (apply lt_add_one1; exact Hx).
  destruct (@Arch_P9 RR1 ax1 x (add1 x o1) Hx Hx1R Hlt) as [q [HqQ [Hxq _]]].
  exists q. split; [exact HqQ | exact Hxq].
Qed.

(* ==================== Stage 4 : 用割扩张到 car1 ==================== *)

Definition lowset (x:Class) : Class := \{ λ a, a ∈ car2 /\ ∃ q, q ∈ Q1 /\ lt1 q x /\ a = psi q \}.

Lemma lowset_sub : ∀ x, lowset x ⊂ car2.
Proof. intros x a Ha. apply AxiomII in Ha as [_ [Ha _]]. exact Ha. Qed.

Lemma lowset_ne : ∀ x, x ∈ car1 -> lowset x <> Φ.
Proof.
  intros x Hx H0.
  destruct (exists_rat_lt x Hx) as [q [Hq Hqx]].
  assert (Hm : psi q ∈ lowset x).
  { apply AxiomII; split.
    - exists car2; exact (psi_mem q Hq).
    - split; [exact (psi_mem q Hq) | exists q; split; [exact Hq | split; [exact Hqx | reflexivity]]]. }
  rewrite H0 in Hm. exact (MKT16 Hm).
Qed.

Lemma lowset_ub : ∀ x, x ∈ car1 -> ∃ c, @Upper RR2 (lowset x) c.
Proof.
  intros x Hx.
  destruct (exists_rat_gt x Hx) as [q [Hq Hxq]].
  assert (HcR : psi q ∈ car2) by (apply psi_mem; exact Hq).
  exists (psi q). unfold Upper. split; [exact (lowset_sub x) |]. split; [exact HcR |].
  intros a Ha. apply AxiomII in Ha as [_ [_ [q0 [Hq0 [Hq0x Haeq]]]]].
  rewrite Haeq.
  assert (Hq0R : q0 ∈ car1) by (exact (@Q_Subset_R RR1 ax1 q0 Hq0)).
  assert (HqR : q ∈ car1) by (exact (@Q_Subset_R RR1 ax1 q Hq)).
  assert (Hq0q : lt1 q0 q) by (apply (@Order_Co2 RR1 ax1 q0 x q Hq0R Hx HqR); left; split; [exact Hq0x | exact (proj1 Hxq)]).
  exact (proj1 (psi_mono q0 q Hq0 Hq Hq0q)).
Qed.

Definition supcand (S:Class) : Class := \{ λ s, s ∈ car2 /\ @Sup1 RR2 S s \}.
Definition Phi (x:Class) : Class := ∩(supcand (lowset x)).

Lemma Phi_val : ∀ x, x ∈ car1 -> @Sup1 RR2 (lowset x) (Phi x).
Proof.
  intros x Hx.
  destruct (@SupT RR2 ax2 (lowset x) (lowset_sub x) (lowset_ne x Hx) (lowset_ub x Hx)) as [s [[HUp Hdens] Huniq]].
  assert (Hsc2 : s ∈ car2) by (exact (proj1 (proj2 HUp))).
  assert (HsE : Ensemble s) by (apply Ens_car2; exact Hsc2).
  assert (Hset : supcand (lowset x) = [s]).
  { apply AxiomI. intros a. split.
    - intros Ha. apply AxiomII in Ha as [_ [Hac2 Hsup]].
      exact (proj2 (MKT41 s HsE a) (eq_sym (Huniq a Hsup))).
    - intros Ha.
      assert (Haeq : a = s) by (exact (proj1 (MKT41 s HsE a) Ha)).
      apply AxiomII in Ha as [Ea _].
      apply AxiomII; split; [exact Ea |].
      rewrite Haeq. exact (conj Hsc2 (conj HUp Hdens)). }
  assert (HPhi : Phi x = s).
  { unfold Phi. rewrite Hset. exact (proj1 (MKT44 HsE)). }
  rewrite HPhi. exact (conj HUp Hdens).
Qed.

Lemma Phi_mem : ∀ x, x ∈ car1 -> Phi x ∈ car2.
Proof. intros x Hx. exact (proj1 (proj2 (proj1 (Phi_val x Hx)))). Qed.

Lemma Phi_ub : ∀ x, x ∈ car1 -> ∀ a, a ∈ lowset x -> le2 a (Phi x).
Proof. intros x Hx a Ha. exact (proj2 (proj2 (proj1 (Phi_val x Hx))) a Ha). Qed.

Lemma Phi_dense : ∀ x, x ∈ car1 -> ∀ s, s ∈ car2 -> lt2 s (Phi x) -> ∃ a, a ∈ lowset x /\ lt2 s a.
Proof. intros x Hx s Hs Hlt. exact (proj2 (Phi_val x Hx) s Hs Hlt). Qed.

(* ---------------- Phi 的割刻画与唯一性 ---------------- *)

Lemma Phi_cut : ∀ x, x ∈ car1 -> ∀ q, q ∈ Q1 -> (lt1 q x <-> lt2 (psi q) (Phi x)).
Proof.
  intros x Hx q Hq. split.
  - intros Hqx.
    assert (Hin : psi q ∈ lowset x).
    { apply AxiomII; split.
      - exists car2; exact (psi_mem q Hq).
      - split; [exact (psi_mem q Hq) | exists q; split; [exact Hq | split; [exact Hqx | reflexivity]]]. }
    assert (Hle : le2 (psi q) (Phi x)) by (apply Phi_ub; assumption).
    assert (Hne : psi q ≠ Phi x).
    { intro Heq.
      destruct (@Arch_P9 RR1 ax1 q x (@Q_Subset_R RR1 ax1 q Hq) Hx Hqx) as [q' [Hq' [Hqq' Hq'x]]].
      assert (Hin' : psi q' ∈ lowset x).
      { apply AxiomII; split.
        - exists car2; exact (psi_mem q' Hq').
        - split; [exact (psi_mem q' Hq') | exists q'; split; [exact Hq' | split; [exact Hq'x | reflexivity]]]. }
      assert (Hle' : le2 (psi q') (Phi x)) by (apply Phi_ub; assumption).
      assert (Hlt' : lt2 (psi q) (psi q')) by (apply psi_mono; assumption).
      rewrite <- Heq in Hle'.
      exact ((proj2 Hlt') (@Leq_P2 RR2 ax2 (psi q) (psi q') (psi_mem q Hq) (psi_mem q' Hq') (proj1 Hlt') Hle')). }
    exact (conj Hle Hne).
  - intros Hlt.
    apply NNPP. intro Hn.
    assert (Hxq_le : le1 x q).
    { destruct (@Order_Co1 RR1 ax1 q x (@Q_Subset_R RR1 ax1 q Hq) Hx) as [Hc | [Hc | Hc]].
      - exfalso. apply Hn. exact Hc.
      - exact (proj1 Hc).
      - rewrite Hc. apply (@Leq_P1 RR1 ax1 x Hx). }
    assert (Hub : ∀ a, a ∈ lowset x -> le2 a (psi q)).
    { intros a Ha. apply AxiomII in Ha as [_ [_ [q0 [Hq0 [Hq0x Haeq]]]]].
      rewrite Haeq.
      assert (Hq0q : lt1 q0 q) by (apply (@Order_Co2 RR1 ax1 q0 x q (@Q_Subset_R RR1 ax1 q0 Hq0) Hx (@Q_Subset_R RR1 ax1 q Hq)); left; split; [exact Hq0x | exact Hxq_le]).
      exact (proj1 (psi_mono q0 q Hq0 Hq Hq0q)). }
    assert (Hle : le2 (Phi x) (psi q)).
    { destruct (@Order_Co1 RR2 ax2 (Phi x) (psi q) (Phi_mem x Hx) (psi_mem q Hq)) as [Hc | [Hc | Hc]].
      - exact (proj1 Hc).
      - exfalso.
        destruct (Phi_dense x Hx (psi q) (psi_mem q Hq) Hc) as [a [Ha Hlta]].
        exact ((proj2 Hlta) (@Leq_P2 RR2 ax2 (psi q) a (psi_mem q Hq) (lowset_sub x a Ha) (proj1 Hlta) (Hub a Ha))).
      - rewrite Hc. apply (@Leq_P1 RR2 ax2 (psi q) (psi_mem q Hq)). }
    exact ((proj2 Hlt) (@Leq_P2 RR2 ax2 (psi q) (Phi x) (psi_mem q Hq) (Phi_mem x Hx) (proj1 Hlt) Hle)).
Qed.

Lemma Phi_uniq : ∀ x, x ∈ car1 -> ∀ a b, a ∈ car2 -> b ∈ car2
  -> (∀ q, q ∈ Q1 -> (lt1 q x <-> lt2 (psi q) a))
  -> (∀ q, q ∈ Q1 -> (lt1 q x <-> lt2 (psi q) b))
  -> a = b.
Proof.
  intros x Hx a b Ha Hb Ha_cut Hb_cut.
  destruct (@Order_Co1 RR2 ax2 a b Ha Hb) as [Hab | [Hba | Heq]].
  - exfalso.
    destruct (psi_dense a b Ha Hb Hab) as [q [Hq [Haq Hqb]]].
    assert (Hqx : lt1 q x) by (exact ((proj2 (Hb_cut q Hq)) Hqb)).
    assert (Hlt : lt2 (psi q) a) by (exact ((proj1 (Ha_cut q Hq)) Hqx)).
    exact ((proj2 Hlt) (@Leq_P2 RR2 ax2 (psi q) a (psi_mem q Hq) Ha (proj1 Hlt) (proj1 Haq))).
  - exfalso.
    destruct (psi_dense b a Hb Ha Hba) as [q [Hq [Hbq Hqa]]].
    assert (Hqx : lt1 q x) by (exact ((proj2 (Ha_cut q Hq)) Hqa)).
    assert (Hlt : lt2 (psi q) b) by (exact ((proj1 (Hb_cut q Hq)) Hqx)).
    exact ((proj2 Hlt) (@Leq_P2 RR2 ax2 (psi q) b (psi_mem q Hq) Hb (proj1 Hlt) (proj1 Hbq))).
  - exact Heq.
Qed.

(* ==================== Part 1 : Phi 严格单调 ==================== *)

Lemma Phi_strict : ∀ x y, x ∈ car1 -> y ∈ car1 -> lt1 x y -> lt2 (Phi x) (Phi y).
Proof.
  intros x y Hx Hy [Hle Hne].
  destruct (@Arch_P9 RR1 ax1 x y Hx Hy (conj Hle Hne)) as [q [HqQ [Hxq Hqy]]].
  assert (Hmemx : Phi x ∈ car2) by (apply Phi_mem; exact Hx).
  assert (Hmemy : Phi y ∈ car2) by (apply Phi_mem; exact Hy).
  assert (Hmemq : psi q ∈ car2) by (apply psi_mem; exact HqQ).
  assert (Hlt_y : lt2 (psi q) (Phi y)).
  { exact ((proj1 (Phi_cut y Hy q HqQ)) Hqy). }
  assert (Hnlt_x : lt2 (psi q) (Phi x) -> False).
  { intro Hc.
    assert (Hqx : lt1 q x) by (exact ((proj2 (Phi_cut x Hx q HqQ)) Hc)).
    exact ((proj2 Hxq) (@Leq_P2 RR1 ax1 x q Hx (@Q_Subset_R RR1 ax1 q HqQ) (proj1 Hxq) (proj1 Hqx))). }
  assert (Hle_x : le2 (Phi x) (psi q)).
  { destruct (@Order_Co1 RR2 ax2 (Phi x) (psi q) Hmemx Hmemq) as [Hc | [Hc | Hc]].
    - exact (proj1 Hc).
    - exfalso. exact (Hnlt_x Hc).
    - rewrite Hc. apply (@Leq_P1 RR2 ax2 (psi q) Hmemq). }
  exact (@Order_Co2 RR2 ax2 (Phi x) (psi q) (Phi y) Hmemx Hmemq Hmemy
           (or_intror (conj Hle_x Hlt_y))).
Qed.

Lemma Phi_mono : ∀ x y, x ∈ car1 -> y ∈ car1 -> le1 x y -> le2 (Phi x) (Phi y).
Proof.
  intros x y Hx Hy Hle.
  destruct (classic (x = y)) as [Heq | Hne].
  - subst y. apply (@Leq_P1 RR2 ax2 (Phi x) (Phi_mem x Hx)).
  - apply (proj1 (Phi_strict x y Hx Hy (conj Hle Hne))).
Qed.

Lemma Phi_inj : ∀ x y, x ∈ car1 -> y ∈ car1 -> Phi x = Phi y -> x = y.
Proof.
  intros x y Hx Hy Heq.
  destruct (@Order_Co1 RR1 ax1 x y Hx Hy) as [Hlt | [Hgt | Heq2]].
  - exfalso. exact ((proj2 (Phi_strict x y Hx Hy Hlt)) Heq).
  - exfalso. exact ((proj2 (Phi_strict y x Hy Hx Hgt)) (eq_sym Heq)).
  - exact Heq2.
Qed.

(* ==================== Part 2 : Phi 满射 ==================== *)

Lemma Phi_surj : ∀ b, b ∈ car2 -> ∃ x, x ∈ car1 /\ Phi x = b.
Proof.
  intros b Hb.
  set (X := \{ λ q, q ∈ Q1 /\ lt2 (psi q) b \}).
  assert (Xmem : ∀ q, q ∈ Q1 -> lt2 (psi q) b -> q ∈ X).
  { intros q HqQ Hqb. apply AxiomII; split.
    - exists car1; exact (@Q_Subset_R RR1 ax1 q HqQ).
    - split; [exact HqQ | exact Hqb]. }
  assert (Xsub : X ⊂ car1).
  { intros q Hq. apply AxiomII in Hq as [_ [HqQ _]]. exact (@Q_Subset_R RR1 ax1 q HqQ). }
  assert (Xne : X <> Φ).
  { assert (Hex : ∃ q, q ∈ Q1 /\ lt2 (psi q) b).
    { assert (Hb1R : add2 b (neg2 o2) ∈ car2)
        by (apply (@Plus_close RR2 ax2 b (neg2 o2) Hb (neg2_car o2 o2_car))).
      assert (Hnelt : lt2 (neg2 o2) z2)
        by (exact (@OrderPM_Co2a RR2 ax2 o2 o2_car (@OrderPM_Co9 RR2 ax2))).
      assert (Hb1lt : lt2 (add2 b (neg2 o2)) b).
      { assert (Ht := @OrderPM_Co1 RR2 ax2 (neg2 o2) z2 b (neg2_car o2 o2_car) z2_car Hb Hnelt).
        assert (Hc1 : add2 (neg2 o2) b = add2 b (neg2 o2))
          by (apply (@Plus_P4 RR2 ax2 (neg2 o2) b (neg2_car o2 o2_car) Hb)).
        assert (Hc2 : add2 z2 b = b)
          by (apply (eq_trans (@Plus_P4 RR2 ax2 z2 b z2_car Hb) (@Plus_P1 RR2 ax2 b Hb))).
        exact (lt2_rw (add2 (neg2 o2) b) (add2 b (neg2 o2)) (add2 z2 b) b Hc1 Hc2 Ht). }
      destruct (@Arch_P9 RR2 ax2 (add2 b (neg2 o2)) b Hb1R Hb Hb1lt) as [r [HrQ2 [_ Hr2]]].
      destruct (psi_surj r HrQ2) as [q [HqQ Hqr]].
      exists q. split; [exact HqQ | rewrite Hqr; exact Hr2]. }
    destruct Hex as [q [HqQ Hqb]].
    intro H0. assert (Hin : q ∈ X) by (apply Xmem; assumption).
    rewrite H0 in Hin. exact (MKT16 Hin). }
  assert (Xbd : ∃ c, @Upper RR1 X c).
  { assert (Hblt2 : lt2 b (add2 b o2)) by (exact (lt_add_one2 b Hb)).
    assert (Hb1R : add2 b o2 ∈ car2) by (apply (@Plus_close RR2 ax2 b o2 Hb o2_car)).
    destruct (@Arch_P9 RR2 ax2 b (add2 b o2) Hb Hb1R Hblt2) as [r [HrQ2 [Hb_r _]]].
    destruct (psi_surj r HrQ2) as [q0 [Hq0Q Hq0r]].
    exists q0. unfold Upper. split.
    - exact Xsub.
    - split; [exact (@Q_Subset_R RR1 ax1 q0 Hq0Q) |].
      intros q Hq. apply AxiomII in Hq as [_ [HqQ Hqb]].
      destruct (@Order_Co1 RR1 ax1 q q0 (@Q_Subset_R RR1 ax1 q HqQ) (@Q_Subset_R RR1 ax1 q0 Hq0Q))
        as [Hltq | [Hlt | Heq]].
      + exact (proj1 Hltq).
      + exfalso.
        assert (H1 : lt2 (psi q0) (psi q))
          by (apply psi_mono; [exact Hq0Q | exact HqQ | exact Hlt]).
        assert (H2 : lt2 (psi q0) b)
          by (apply (@Order_Co2 RR2 ax2 (psi q0) (psi q) b (psi_mem q0 Hq0Q) (psi_mem q HqQ) Hb);
              left; split; [exact H1 | exact (proj1 Hqb)]).
        assert (H3 : lt2 b (psi q0))
          by (exact (lt2_rw b b r (psi q0) eq_refl (eq_sym Hq0r) Hb_r)).
        exact ((proj2 H2) (@Leq_P2 RR2 ax2 (psi q0) b (psi_mem q0 Hq0Q) Hb (proj1 H2) (proj1 H3))).
      + rewrite Heq. apply (@Leq_P1 RR1 ax1 q0 (@Q_Subset_R RR1 ax1 q0 Hq0Q)). }
  destruct (@SupT RR1 ax1 X Xsub Xne Xbd) as [x [HSup _]].
  destruct HSup as [HUpX HdensX].
  destruct HUpX as [_ [HxR Hxub]].
  assert (Hcut : ∀ q, q ∈ Q1 -> (lt1 q x <-> lt2 (psi q) b)).
  { intros q HqQ. split.
    - intros Hqx.
      destruct (HdensX q (@Q_Subset_R RR1 ax1 q HqQ) Hqx) as [x1 [Hx1X Hqx1]].
      apply AxiomII in Hx1X as [_ [Hx1Q Hx1b]].
      assert (H1 : lt2 (psi q) (psi x1))
        by (apply psi_mono; [exact HqQ | exact Hx1Q | exact Hqx1]).
      exact (@Order_Co2 RR2 ax2 (psi q) (psi x1) b (psi_mem q HqQ) (psi_mem x1 Hx1Q) Hb
               (or_introl (conj H1 (proj1 Hx1b)))).
    - intros Hqb.
      destruct (@Order_Co1 RR1 ax1 q x (@Q_Subset_R RR1 ax1 q HqQ) HxR) as [Hlt | [Hgt | Heq]].
      + exact Hlt.
      + exfalso.
        assert (Hqin : q ∈ X) by (apply Xmem; assumption).
        assert (Hle := Hxub q Hqin).
        exact (proj2 Hgt (@Leq_P2 RR1 ax1 x q HxR (@Q_Subset_R RR1 ax1 q HqQ) (proj1 Hgt) Hle)).
      + exfalso.
        assert (HxQ : x ∈ Q1) by (rewrite <- Heq; exact HqQ).
        assert (Hpsix : lt2 (psi x) b) by (rewrite <- Heq; exact Hqb).
        destruct (@Arch_P9 RR2 ax2 (psi x) b (psi_mem x HxQ) Hb Hpsix) as [r [HrQ2 [Hr1 Hr2]]].
        destruct (psi_surj r HrQ2) as [q' [Hq'Q Hq'r]].
        assert (Hq'x : lt1 x q').
        { apply psi_lt_reflect. exact HxQ. exact Hq'Q. rewrite Hq'r. exact Hr1. }
        assert (Hq'notX : q' ∉ X).
        { intro Hin. assert (Hle := Hxub q' Hin).
          exact (proj2 Hq'x (eq_sym (@Leq_P2 RR1 ax1 q' x (@Q_Subset_R RR1 ax1 q' Hq'Q) HxR Hle (proj1 Hq'x)))). }
        assert (Hnb : lt2 (psi q') b -> False).
        { intro Hc. apply Hq'notX. apply Xmem; [exact Hq'Q | exact Hc]. }
        exact (Hnb (lt2_rw r (psi q') b b (eq_sym Hq'r) eq_refl Hr2)). }
  exists x. split; [exact HxR |].
  exact (@Phi_uniq x HxR (Phi x) b (Phi_mem x HxR) Hb (fun q Hq => Phi_cut x HxR q Hq) Hcut).
Qed.

(* ==================== Part 3 : Phi 在有理数上与 psi 一致 ==================== *)

Lemma Phi_q : ∀ q, q ∈ Q1 -> Phi q = psi q.
Proof.
  intros q Hq.
  assert (HqR : q ∈ car1) by (exact (@Q_Subset_R RR1 ax1 q Hq)).
  exact (@Phi_uniq q HqR (Phi q) (psi q) (Phi_mem q HqR) (psi_mem q Hq)
           (fun r Hr => Phi_cut q HqR r Hr)
           (fun r Hr => conj (fun Hrq => psi_mono r q Hr Hq Hrq)
                              (fun Hrq => psi_lt_reflect r q Hr Hq Hrq))).
Qed.

Lemma Phi_zero : Phi z1 = z2.
Proof.
  assert (HzQ : z1 ∈ Q1) by (apply (@Z_Subset_Q RR1 ax1 z1 Z1_zero)).
  rewrite (Phi_q z1 HzQ). apply psi_zero.
Qed.

Lemma Phi_one : Phi o1 = o2.
Proof.
  assert (HoQ : o1 ∈ Q1)
    by (apply (@Z_Subset_Q RR1 ax1 o1); apply (@N_Subset_Z RR1 o1); apply (@one_in_N RR1 ax1)).
  rewrite (Phi_q o1 HoQ). apply psi_one.
Qed.

(* ==================== Part 4 : 加法群中的恒等式 ==================== *)

Lemma sub1_car : ∀ a b, a ∈ car1 -> b ∈ car1 -> add1 a (neg1 b) ∈ car1.
Proof.
  intros a b Ha Hb. apply (@Plus_close RR1 ax1 a (neg1 b) Ha (neg1_car b Hb)).
Qed.

Lemma add1_zero_self : ∀ a, a ∈ car1 -> add1 a z1 = a.
Proof. intros a Ha. apply (@Plus_P1 RR1 ax1 a Ha). Qed.
Lemma add2_zero_self : ∀ a, a ∈ car2 -> add2 a z2 = a.
Proof. intros a Ha. apply (@Plus_P1 RR2 ax2 a Ha). Qed.
Lemma zero_add1 : ∀ a, a ∈ car1 -> add1 z1 a = a.
Proof. intros a Ha. apply (eq_trans (@Plus_P4 RR1 ax1 z1 a z1_car Ha) (@Plus_P1 RR1 ax1 a Ha)). Qed.
Lemma zero_add2 : ∀ a, a ∈ car2 -> add2 z2 a = a.
Proof. intros a Ha. apply (eq_trans (@Plus_P4 RR2 ax2 z2 a z2_car Ha) (@Plus_P1 RR2 ax2 a Ha)). Qed.
Lemma add1_neg_self : ∀ a, a ∈ car1 -> add1 a (neg1 a) = z1.
Proof. intros a Ha. apply (@Plus_neg2 RR1 ax1 a Ha). Qed.
Lemma add2_neg_self : ∀ a, a ∈ car2 -> add2 a (neg2 a) = z2.
Proof. intros a Ha. apply (@Plus_neg2 RR2 ax2 a Ha). Qed.
Lemma add1_comm_gen : ∀ a b, a ∈ car1 -> b ∈ car1 -> add1 a b = add1 b a.
Proof. intros a b Ha Hb. apply (@Plus_P4 RR1 ax1 a b Ha Hb). Qed.
Lemma add2_comm_gen : ∀ a b, a ∈ car2 -> b ∈ car2 -> add2 a b = add2 b a.
Proof. intros a b Ha Hb. apply (@Plus_P4 RR2 ax2 a b Ha Hb). Qed.
Lemma add1_assoc_gen : ∀ a b c, a ∈ car1 -> b ∈ car1 -> c ∈ car1
  -> add1 a (add1 b c) = add1 (add1 a b) c.
Proof. intros a b c Ha Hb Hc. apply (@Plus_P3 RR1 ax1 a b c Ha Hb Hc). Qed.
Lemma add2_assoc_gen : ∀ a b c, a ∈ car2 -> b ∈ car2 -> c ∈ car2
  -> add2 a (add2 b c) = add2 (add2 a b) c.
Proof. intros a b c Ha Hb Hc. apply (@Plus_P3 RR2 ax2 a b c Ha Hb Hc). Qed.
Lemma add2_zero_neg : ∀ a, a ∈ car2 -> add2 z2 (neg2 a) = neg2 a.
Proof.
  intros a Ha.
  apply (eq_trans (@Plus_P4 RR2 ax2 z2 (neg2 a) z2_car (neg2_car a Ha))
             (@Plus_P1 RR2 ax2 (neg2 a) (neg2_car a Ha))).
Qed.

Lemma sub1_self : ∀ a b, a ∈ car1 -> b ∈ car1 -> add1 (add1 a (neg1 b)) b = a.
Proof.
  intros a b Ha Hb.
  assert (Hnb : neg1 b ∈ car1) by (apply neg1_car; exact Hb).
  transitivity (add1 a (add1 (neg1 b) b)).
  - exact (eq_sym (@Plus_P3 RR1 ax1 a (neg1 b) b Ha Hnb Hb)).
  - rewrite (neg1_add b Hb). apply (@Plus_P1 RR1 ax1 a Ha).
Qed.

Lemma add1_cancel_right : ∀ a b, a ∈ car1 -> b ∈ car1 -> add1 (add1 a b) (neg1 b) = a.
Proof.
  intros a b Ha Hb.
  assert (Hnb : neg1 b ∈ car1) by (apply neg1_car; exact Hb).
  transitivity (add1 a (add1 b (neg1 b))).
  - exact (eq_sym (@Plus_P3 RR1 ax1 a b (neg1 b) Ha Hb Hnb)).
  - rewrite (add1_neg_self b Hb). exact (add1_zero_self a Ha).
Qed.

Lemma add1_rot : ∀ a b, a ∈ car1 -> b ∈ car1 -> add1 (add1 a b) (neg1 a) = b.
Proof.
  intros a b Ha Hb.
  assert (Hna : neg1 a ∈ car1) by (apply neg1_car; exact Ha).
  transitivity (add1 a (add1 b (neg1 a))).
  - exact (eq_sym (@Plus_P3 RR1 ax1 a b (neg1 a) Ha Hb Hna)).
  - rewrite (add1_comm_gen b (neg1 a) Hb Hna).
    transitivity (add1 (add1 a (neg1 a)) b).
    + exact (@Plus_P3 RR1 ax1 a (neg1 a) b Ha Hna Hb).
    + rewrite (add1_neg_self a Ha). exact (zero_add1 b Hb).
Qed.

Lemma add1_comm_sub : ∀ q r, q ∈ car1 -> r ∈ car1 -> add1 r (add1 q (neg1 r)) = q.
Proof.
  intros q r Hq Hr.
  assert (Hqr : add1 q (neg1 r) ∈ car1) by (apply sub1_car; assumption).
  rewrite (add1_comm_gen r (add1 q (neg1 r)) Hr Hqr).
  apply sub1_self. exact Hq. exact Hr.
Qed.

Lemma sub2_car : ∀ a b, a ∈ car2 -> b ∈ car2 -> add2 a (neg2 b) ∈ car2.
Proof.
  intros a b Ha Hb. apply (@Plus_close RR2 ax2 a (neg2 b) Ha (neg2_car b Hb)).
Qed.

Lemma sub2_self : ∀ a b, a ∈ car2 -> b ∈ car2 -> add2 (add2 a (neg2 b)) b = a.
Proof.
  intros a b Ha Hb.
  assert (Hnb : neg2 b ∈ car2) by (apply neg2_car; exact Hb).
  transitivity (add2 a (add2 (neg2 b) b)).
  - exact (eq_sym (@Plus_P3 RR2 ax2 a (neg2 b) b Ha Hnb Hb)).
  - rewrite (neg2_add b Hb). apply (@Plus_P1 RR2 ax2 a Ha).
Qed.

Lemma add2_cancel_right : ∀ a b, a ∈ car2 -> b ∈ car2 -> add2 (add2 a b) (neg2 b) = a.
Proof.
  intros a b Ha Hb.
  assert (Hnb : neg2 b ∈ car2) by (apply neg2_car; exact Hb).
  transitivity (add2 a (add2 b (neg2 b))).
  - exact (eq_sym (@Plus_P3 RR2 ax2 a b (neg2 b) Ha Hb Hnb)).
  - rewrite (add2_neg_self b Hb). exact (add2_zero_self a Ha).
Qed.

Lemma add2_rot : ∀ a b, a ∈ car2 -> b ∈ car2 -> add2 (add2 a b) (neg2 a) = b.
Proof.
  intros a b Ha Hb.
  assert (Hna : neg2 a ∈ car2) by (apply neg2_car; exact Ha).
  transitivity (add2 a (add2 b (neg2 a))).
  - exact (eq_sym (@Plus_P3 RR2 ax2 a b (neg2 a) Ha Hb Hna)).
  - rewrite (add2_comm_gen b (neg2 a) Hb Hna).
    transitivity (add2 (add2 a (neg2 a)) b).
    + exact (@Plus_P3 RR2 ax2 a (neg2 a) b Ha Hna Hb).
    + rewrite (add2_neg_self a Ha). exact (zero_add2 b Hb).
Qed.

Lemma Q_sub1 : ∀ a b, a ∈ Q1 -> b ∈ Q1 -> add1 a (neg1 b) ∈ Q1.
Proof.
  intros a b Ha Hb.
  exact (@Rat_P1a RR1 ax1 a (neg1 b) Ha (proj1 (@Rat_P3 RR1 ax1 b Hb))).
Qed.

Lemma psi_sub : ∀ q r, q ∈ Q1 -> r ∈ Q1
  -> psi (add1 q (neg1 r)) = add2 (psi q) (neg2 (psi r)).
Proof.
  intros q r Hq Hr.
  rewrite (psi_add q (neg1 r) Hq (proj1 (@Rat_P3 RR1 ax1 r Hr))).
  rewrite (psi_neg r Hr). reflexivity.
Qed.

(* ==================== Part 5 : Phi 保加法 ==================== *)

Lemma Phi_add_cut : ∀ x y q, x ∈ car1 -> y ∈ car1 -> q ∈ Q1
  -> (lt1 q (add1 x y) <-> lt2 (psi q) (add2 (Phi x) (Phi y))).
Proof.
  intros x y q Hx Hy HqQ.
  assert (HqR : q ∈ car1) by (exact (@Q_Subset_R RR1 ax1 q HqQ)).
  assert (HnyR : neg1 y ∈ car1) by (apply neg1_car; exact Hy).
  assert (HxyR : add1 x y ∈ car1) by (apply (@Plus_close RR1 ax1 x y Hx Hy)).
  assert (HPx : Phi x ∈ car2) by (apply Phi_mem; exact Hx).
  assert (HPy : Phi y ∈ car2) by (apply Phi_mem; exact Hy).
  assert (HPq : psi q ∈ car2) by (apply psi_mem; exact HqQ).
  assert (HsumR : add2 (Phi x) (Phi y) ∈ car2)
    by (apply (@Plus_close RR2 ax2 (Phi x) (Phi y) HPx HPy)).
  split.
  - intros Hlt.
    assert (Hpy : add1 q (neg1 y) ∈ car1)
      by (apply (@Plus_close RR1 ax1 q (neg1 y) HqR HnyR)).
    assert (H1 : lt1 (add1 q (neg1 y)) (add1 (add1 x y) (neg1 y)))
      by (apply (@OrderPM_Co1 RR1 ax1 q (add1 x y) (neg1 y) HqR HxyR HnyR); exact Hlt).
    assert (H2 : add1 (add1 x y) (neg1 y) = x) by (apply add1_cancel_right; assumption).
    assert (Hlty : lt1 (add1 q (neg1 y)) x)
      by (exact (lt1_rw (add1 q (neg1 y)) (add1 q (neg1 y))
                   (add1 (add1 x y) (neg1 y)) x eq_refl H2 H1)).
    destruct (@Arch_P9 RR1 ax1 (add1 q (neg1 y)) x Hpy Hx Hlty) as [r [HrQ [Hr1 Hr2]]].
    assert (HrR : r ∈ car1) by (exact (@Q_Subset_R RR1 ax1 r HrQ)).
    assert (HrPhi : lt2 (psi r) (Phi x)) by (exact ((proj1 (Phi_cut x Hx r HrQ)) Hr2)).
    assert (HqmrQ : add1 q (neg1 r) ∈ Q1) by (apply Q_sub1; assumption).
    assert (HqmrR : add1 q (neg1 r) ∈ car1) by (apply sub1_car; assumption).
    assert (Hqmr_lt : lt1 (add1 q (neg1 r)) y).
    { assert (Ht1 : lt1 (add1 (add1 q (neg1 y)) y) (add1 r y))
        by (apply (@OrderPM_Co1 RR1 ax1 (add1 q (neg1 y)) r y Hpy HrR Hy); exact Hr1).
      rewrite (sub1_self q y HqR Hy) in Ht1.
      assert (Ht2 : lt1 (add1 q (neg1 r)) (add1 (add1 r y) (neg1 r)))
        by (apply (@OrderPM_Co1 RR1 ax1 q (add1 r y) (neg1 r) HqR
                     (@Plus_close RR1 ax1 r y HrR Hy) (neg1_car r HrR)); exact Ht1).
      exact (lt1_rw (add1 q (neg1 r)) (add1 q (neg1 r))
               (add1 (add1 r y) (neg1 r)) y eq_refl (add1_rot r y HrR Hy) Ht2). }
    assert (Hqmr_Phi : lt2 (psi (add1 q (neg1 r))) (Phi y))
      by (exact ((proj1 (Phi_cut y Hy (add1 q (neg1 r)) HqmrQ)) Hqmr_lt)).
    assert (Hpsi_q : psi q = add2 (psi (add1 q (neg1 r))) (psi r)).
    { transitivity (psi (add1 (add1 q (neg1 r)) r)).
      - rewrite (sub1_self q r HqR HrR). reflexivity.
      - rewrite (psi_add (add1 q (neg1 r)) r HqmrQ HrQ). reflexivity. }
    assert (Hfinal : lt2 (add2 (psi (add1 q (neg1 r))) (psi r)) (add2 (Phi y) (Phi x)))
      by (apply (@OrderPM_Co4 RR2 ax2 (psi (add1 q (neg1 r))) (Phi y) (psi r) (Phi x)
                   (psi_mem (add1 q (neg1 r)) HqmrQ) HPy (psi_mem r HrQ) HPx);
          [exact (proj1 Hqmr_Phi) | exact HrPhi]).
    assert (Hcomm : add2 (Phi y) (Phi x) = add2 (Phi x) (Phi y))
      by (apply (@Plus_P4 RR2 ax2 (Phi y) (Phi x) HPy HPx)).
    exact (lt2_rw (add2 (psi (add1 q (neg1 r))) (psi r)) (psi q)
             (add2 (Phi y) (Phi x)) (add2 (Phi x) (Phi y)) (eq_sym Hpsi_q) Hcomm Hfinal).
  - intros Hlt.
    assert (Hny2 : neg2 (Phi y) ∈ car2) by (apply neg2_car; exact HPy).
    assert (Ha2R : add2 (psi q) (neg2 (Phi y)) ∈ car2)
      by (apply (@Plus_close RR2 ax2 (psi q) (neg2 (Phi y)) HPq Hny2)).
    assert (Hlt2 : lt2 (add2 (psi q) (neg2 (Phi y))) (Phi x)).
    { assert (Ht : lt2 (add2 (psi q) (neg2 (Phi y)))
                    (add2 (add2 (Phi x) (Phi y)) (neg2 (Phi y))))
        by (apply (@OrderPM_Co1 RR2 ax2 (psi q) (add2 (Phi x) (Phi y)) (neg2 (Phi y)) HPq HsumR Hny2);
            exact Hlt).
      exact (lt2_rw (add2 (psi q) (neg2 (Phi y))) (add2 (psi q) (neg2 (Phi y)))
               (add2 (add2 (Phi x) (Phi y)) (neg2 (Phi y))) (Phi x) eq_refl
               (add2_cancel_right (Phi x) (Phi y) HPx HPy) Ht). }
    destruct (@Arch_P9 RR2 ax2 (add2 (psi q) (neg2 (Phi y))) (Phi x) Ha2R HPx Hlt2)
      as [s [HsQ2 [Hs1 Hs2]]].
    destruct (psi_surj s HsQ2) as [r [HrQ Hsr]].
    rewrite <- Hsr in Hs1. rewrite <- Hsr in Hs2.
    assert (Hrlt : lt1 r x) by (exact ((proj2 (Phi_cut x Hx r HrQ)) Hs2)).
    assert (HrR : r ∈ car1) by (exact (@Q_Subset_R RR1 ax1 r HrQ)).
    assert (HqmrQ : add1 q (neg1 r) ∈ Q1) by (apply Q_sub1; assumption).
    assert (HqmrR : add1 q (neg1 r) ∈ car1) by (apply sub1_car; assumption).
    assert (Hqmr_y : lt1 (add1 q (neg1 r)) y).
    { apply (proj2 (Phi_cut y Hy (add1 q (neg1 r)) HqmrQ)).
      rewrite (psi_sub q r HqQ HrQ).
      assert (Hstep1 : lt2 (psi q) (add2 (psi r) (Phi y))).
      { assert (Ht : lt2 (add2 (add2 (psi q) (neg2 (Phi y))) (Phi y)) (add2 (psi r) (Phi y)))
          by (apply (@OrderPM_Co1 RR2 ax2 (add2 (psi q) (neg2 (Phi y))) (psi r) (Phi y)
                       Ha2R (psi_mem r HrQ) HPy); exact Hs1).
        exact (lt2_rw (add2 (add2 (psi q) (neg2 (Phi y))) (Phi y)) (psi q)
                 (add2 (psi r) (Phi y)) (add2 (psi r) (Phi y))
                 (sub2_self (psi q) (Phi y) HPq HPy) eq_refl Ht). }
      assert (Hstep2 : lt2 (add2 (psi q) (neg2 (psi r))) (Phi y)).
      { assert (Ht : lt2 (add2 (psi q) (neg2 (psi r)))
                      (add2 (add2 (psi r) (Phi y)) (neg2 (psi r))))
          by (apply (@OrderPM_Co1 RR2 ax2 (psi q) (add2 (psi r) (Phi y)) (neg2 (psi r)) HPq
                       (@Plus_close RR2 ax2 (psi r) (Phi y) (psi_mem r HrQ) HPy)
                       (neg2_car (psi r) (psi_mem r HrQ))); exact Hstep1).
        exact (lt2_rw (add2 (psi q) (neg2 (psi r))) (add2 (psi q) (neg2 (psi r)))
                 (add2 (add2 (psi r) (Phi y)) (neg2 (psi r))) (Phi y) eq_refl
                 (add2_rot (psi r) (Phi y) (psi_mem r HrQ) HPy) Ht). }
      exact Hstep2. }
    assert (Hqt : lt1 (add1 (add1 q (neg1 r)) r) (add1 x y)).
    { assert (Ht : lt1 (add1 (add1 q (neg1 r)) r) (add1 y x))
        by (apply (@OrderPM_Co4 RR1 ax1 (add1 q (neg1 r)) y r x HqmrR Hy HrR Hx);
            [exact (proj1 Hqmr_y) | exact Hrlt]).
      exact (lt1_rw (add1 (add1 q (neg1 r)) r) (add1 (add1 q (neg1 r)) r)
               (add1 y x) (add1 x y) eq_refl (@Plus_P4 RR1 ax1 y x Hy Hx) Ht). }
    exact (lt1_rw (add1 (add1 q (neg1 r)) r) q (add1 x y) (add1 x y)
             (sub1_self q r HqR HrR) eq_refl Hqt).
Qed.

Lemma Phi_add : ∀ x y, x ∈ car1 -> y ∈ car1 -> Phi (add1 x y) = add2 (Phi x) (Phi y).
Proof.
  intros x y Hx Hy.
  assert (HxyR : add1 x y ∈ car1) by (apply (@Plus_close RR1 ax1 x y Hx Hy)).
  assert (HsumR : add2 (Phi x) (Phi y) ∈ car2)
    by (apply (@Plus_close RR2 ax2 (Phi x) (Phi y) (Phi_mem x Hx) (Phi_mem y Hy))).
  exact (@Phi_uniq (add1 x y) HxyR (Phi (add1 x y)) (add2 (Phi x) (Phi y))
          (Phi_mem (add1 x y) HxyR) HsumR
          (fun q Hq => Phi_cut (add1 x y) HxyR q Hq)
          (fun q Hq => Phi_add_cut x y q Hx Hy Hq)).
Qed.

Lemma Phi_neg : ∀ x, x ∈ car1 -> Phi (neg1 x) = neg2 (Phi x).
Proof.
  intros x Hx.
  assert (HnxR : neg1 x ∈ car1) by (apply neg1_car; exact Hx).
  assert (Hsum : add1 x (neg1 x) = z1) by (apply (@Plus_neg2 RR1 ax1 x Hx)).
  assert (Hadd := Phi_add x (neg1 x) Hx HnxR).
  rewrite Hsum in Hadd. rewrite Phi_zero in Hadd.
  assert (Hadd' : add2 (Phi (neg1 x)) (Phi x) = z2).
  { rewrite (add2_comm_gen (Phi (neg1 x)) (Phi x) (Phi_mem (neg1 x) HnxR) (Phi_mem x Hx)).
    exact (eq_sym Hadd). }
  assert (Hun : add2 (Phi (neg1 x)) (Phi x) = add2 (neg2 (Phi x)) (Phi x))
    by (rewrite (neg2_add (Phi x) (Phi_mem x Hx)); exact Hadd').
  transitivity (add2 (add2 (Phi (neg1 x)) (Phi x)) (neg2 (Phi x))).
  - symmetry.
    apply (add2_cancel_right (Phi (neg1 x)) (Phi x) (Phi_mem (neg1 x) HnxR) (Phi_mem x Hx)).
  - rewrite Hun.
    apply (add2_cancel_right (neg2 (Phi x)) (Phi x) (neg2_car (Phi x) (Phi_mem x Hx)) (Phi_mem x Hx)).
Qed.

(* ==================== Part 6 : 乘法记号包装引理 ==================== *)

Lemma mul1_comm_gen : ∀ a b, a ∈ car1 -> b ∈ car1 -> mul1 a b = mul1 b a.
Proof. intros a b Ha Hb. apply (@Mult_P4 RR1 ax1 a b Ha Hb). Qed.
Lemma mul2_comm_gen : ∀ a b, a ∈ car2 -> b ∈ car2 -> mul2 a b = mul2 b a.
Proof. intros a b Ha Hb. apply (@Mult_P4 RR2 ax2 a b Ha Hb). Qed.
Lemma mul1_assoc_gen : ∀ a b c, a ∈ car1 -> b ∈ car1 -> c ∈ car1
  -> mul1 a (mul1 b c) = mul1 (mul1 a b) c.
Proof. intros a b c Ha Hb Hc. apply (@Mult_P3 RR1 ax1 a b c Ha Hb Hc). Qed.
Lemma mul2_assoc_gen : ∀ a b c, a ∈ car2 -> b ∈ car2 -> c ∈ car2
  -> mul2 a (mul2 b c) = mul2 (mul2 a b) c.
Proof. intros a b c Ha Hb Hc. apply (@Mult_P3 RR2 ax2 a b c Ha Hb Hc). Qed.
Lemma mul1_one_self : ∀ a, a ∈ car1 -> mul1 a o1 = a.
Proof. intros a Ha. apply (@Mult_P1 RR1 ax1 a Ha). Qed.
Lemma mul2_one_self : ∀ a, a ∈ car2 -> mul2 a o2 = a.
Proof. intros a Ha. apply (@Mult_P1 RR2 ax2 a Ha). Qed.
Lemma one_mul1 : ∀ a, a ∈ car1 -> mul1 o1 a = a.
Proof. intros a Ha. apply (eq_trans (@Mult_P4 RR1 ax1 o1 a o1_car Ha) (@Mult_P1 RR1 ax1 a Ha)). Qed.
Lemma one_mul2 : ∀ a, a ∈ car2 -> mul2 o2 a = a.
Proof. intros a Ha. apply (eq_trans (@Mult_P4 RR2 ax2 o2 a o2_car Ha) (@Mult_P1 RR2 ax2 a Ha)). Qed.
Lemma mul1_distr_gen : ∀ a b c, a ∈ car1 -> b ∈ car1 -> c ∈ car1
  -> mul1 (add1 a b) c = add1 (mul1 a c) (mul1 b c).
Proof. intros a b c Ha Hb Hc. apply (@Mult_P5 RR1 ax1 a b c Ha Hb Hc). Qed.
Lemma mul2_distr_gen : ∀ a b c, a ∈ car2 -> b ∈ car2 -> c ∈ car2
  -> mul2 (add2 a b) c = add2 (mul2 a c) (mul2 b c).
Proof. intros a b c Ha Hb Hc. apply (@Mult_P5 RR2 ax2 a b c Ha Hb Hc). Qed.
Lemma mul1_zero_left : ∀ a, a ∈ car1 -> mul1 z1 a = z1.
Proof.
  intros a Ha.
  apply (eq_trans (@Mult_P4 RR1 ax1 z1 a z1_car Ha) (@PlusMult_Co1 RR1 ax1 a Ha)).
Qed.
Lemma mul2_zero_left : ∀ a, a ∈ car2 -> mul2 z2 a = z2.
Proof.
  intros a Ha.
  apply (eq_trans (@Mult_P4 RR2 ax2 z2 a z2_car Ha) (@PlusMult_Co1 RR2 ax2 a Ha)).
Qed.
Lemma mul1_lt_mono : ∀ a b c, a ∈ car1 -> b ∈ car1 -> c ∈ car1 -> lt1 a b -> lt1 z1 c
  -> lt1 (mul1 a c) (mul1 b c).
Proof. intros a b c Ha Hb Hc Hab H0. apply (@OrderPM_Co7a RR1 ax1 a b c Ha Hb Hc Hab H0). Qed.
Lemma mul2_lt_mono : ∀ a b c, a ∈ car2 -> b ∈ car2 -> c ∈ car2 -> lt2 a b -> lt2 z2 c
  -> lt2 (mul2 a c) (mul2 b c).
Proof. intros a b c Ha Hb Hc Hab H0. apply (@OrderPM_Co7a RR2 ax2 a b c Ha Hb Hc Hab H0). Qed.
Lemma mul1_pos : ∀ a b, a ∈ car1 -> b ∈ car1 -> lt1 z1 a -> lt1 z1 b -> lt1 z1 (mul1 a b).
Proof. intros a b Ha Hb H0a H0b. apply (@OrderPM_Co5 RR1 ax1 a b Ha Hb); left; split; assumption. Qed.
Lemma mul2_pos : ∀ a b, a ∈ car2 -> b ∈ car2 -> lt2 z2 a -> lt2 z2 b -> lt2 z2 (mul2 a b).
Proof. intros a b Ha Hb H0a H0b. apply (@OrderPM_Co5 RR2 ax2 a b Ha Hb); left; split; assumption. Qed.
Lemma mul2_lt_mul : ∀ a b c d, a ∈ car2 -> b ∈ car2 -> c ∈ car2 -> d ∈ car2
  -> lt2 z2 a -> lt2 a b -> lt2 z2 c -> lt2 c d -> lt2 (mul2 a c) (mul2 b d).
Proof.
  intros a b c d Ha Hb Hc Hd H0a Hab H0c Hcd.
  assert (H0b : lt2 z2 b)
    by (exact (@Order_Co2 RR2 ax2 z2 a b z2_car Ha Hb (or_introl (conj H0a (proj1 Hab))))).
  assert (H1 : lt2 (mul2 a c) (mul2 b c)) by (apply mul2_lt_mono; assumption).
  assert (H2' : lt2 (mul2 c b) (mul2 d b)) by (apply mul2_lt_mono; assumption).
  assert (H2 : lt2 (mul2 b c) (mul2 b d))
    by (exact (lt2_rw (mul2 c b) (mul2 b c) (mul2 d b) (mul2 b d)
                 (eq_sym (mul2_comm_gen b c Hb Hc)) (eq_sym (mul2_comm_gen b d Hb Hd)) H2')).
  apply (@Order_Co2 RR2 ax2 (mul2 a c) (mul2 b c) (mul2 b d)
           (@Mult_close RR2 ax2 a c Ha Hc) (@Mult_close RR2 ax2 b c Hb Hc)
           (@Mult_close RR2 ax2 b d Hb Hd)).
  left. split; [exact H1 | exact (proj1 H2)].
Qed.

(* ==================== Part 7 : 加性映射的整数齐次性 ==================== *)

Lemma N1_to_Q1 : ∀ k, k ∈ N1 -> k ∈ Q1.
Proof. intros k Hk. apply (@Z_Subset_Q RR1 ax1 k (N1_in_Z1 k Hk)). Qed.
Lemma Z1_to_Q1 : ∀ k, k ∈ Z1 -> k ∈ Q1.
Proof. intros k Hk. apply (@Z_Subset_Q RR1 ax1 k Hk). Qed.

Lemma psi_Z : ∀ m, m ∈ Z1 -> psi m = sigZ m.
Proof.
  intros m Hm.
  assert (Hne : o1 ≠ z1) by (intro H; exact ((proj2 (@OrderPM_Co9 RR1 ax1)) (eq_sym H))).
  assert (Hmq : mul1 m (inv1 o1) = m).
  { rewrite inv1_one. apply mul1_one_self. exact (Z1_sub_car1 m Hm). }
  transitivity (psi (mul1 m (inv1 o1))).
  - rewrite Hmq. reflexivity.
  - rewrite (psi_rep m o1 Hm (N1_in_Z1 o1 (@one_in_N RR1 ax1))
               (fun H => (proj2 (@OrderPM_Co9 RR1 ax1)) (eq_sym H))).
    rewrite sigZ_one. rewrite inv2_one.
    rewrite (mul2_one_self (sigZ m) (Z2_sub_car2 (sigZ m) (sigZ_Z2 m Hm))). reflexivity.
Qed.

Lemma psi_ne_zero : ∀ m, m ∈ Z1 -> m ≠ z1 -> psi m ≠ z2.
Proof.
  intros m Hm Hne Heq.
  rewrite (psi_Z m Hm) in Heq.
  exact (sigZ_ne_zero m Hm Hne Heq).
Qed.

Lemma mul2_cancel : ∀ a x y, a ∈ car2 -> a ≠ z2 -> x ∈ car2 -> y ∈ car2
  -> mul2 a x = mul2 a y -> x = y.
Proof.
  intros a x y Ha Hane Hx Hy Heq.
  assert (Ha0 : a ∈ (car2 ~ [z2])) by (apply in_sm2; assumption).
  assert (Hia : inv2 a ∈ car2) by (apply inv2_car; exact Ha0).
  assert (Hx' : mul2 (inv2 a) (mul2 a x) = x).
  { transitivity (mul2 (mul2 (inv2 a) a) x).
    - apply (mul2_assoc_gen (inv2 a) a x Hia Ha Hx).
    - rewrite (mul2_comm_gen (inv2 a) a Hia Ha).
      rewrite (inv2_val a Ha0). exact (one_mul2 x Hx). }
  assert (Hy' : mul2 (inv2 a) (mul2 a y) = y).
  { transitivity (mul2 (mul2 (inv2 a) a) y).
    - apply (mul2_assoc_gen (inv2 a) a y Hia Ha Hy).
    - rewrite (mul2_comm_gen (inv2 a) a Hia Ha).
      rewrite (inv2_val a Ha0). exact (one_mul2 y Hy). }
  rewrite <- Hx'. rewrite Heq. exact Hy'.
Qed.

Lemma add_N_hom : ∀ F : Class -> Class,
  (∀ x, x ∈ car1 -> F x ∈ car2) ->
  (∀ x y, x ∈ car1 -> y ∈ car1 -> F (add1 x y) = add2 (F x) (F y)) ->
  ∀ k, k ∈ N1 -> ∀ z, z ∈ car1 -> F (mul1 k z) = mul2 (psi k) (F z).
Proof.
  intros F HFmem HFadd.
  set (E := \{ λ k, k ∈ N1 /\ ∀ z, z ∈ car1 -> F (mul1 k z) = mul2 (psi k) (F z) \}).
  assert (Esub : E ⊂ N1) by (intros z Hz; apply AxiomII in Hz as [_ [HzN _]]; exact HzN).
  assert (H1 : o1 ∈ E).
  { apply AxiomII; split.
    - exists car1; exact o1_car.
    - split; [apply (@one_in_N RR1 ax1) |].
      intros z Hz.
      rewrite (one_mul1 z Hz). rewrite psi_one. exact (eq_sym (one_mul2 (F z) (HFmem z Hz))). }
  assert (Hclos : ∀ k, k ∈ E -> add1 k o1 ∈ E).
  { intros k Hk. apply AxiomII in Hk as [_ [HkN IH]].
    assert (HkR : k ∈ car1) by (apply N1_sub_car1; exact HkN).
    assert (Hk1N : add1 k o1 ∈ N1)
      by (assert (HIN := @IndSet_N RR1 ax1); unfold IndSet in HIN; exact (proj2 HIN k HkN)).
    apply AxiomII; split.
    - exists car1; apply (@Plus_close RR1 ax1 k o1 HkR o1_car).
    - split; [exact Hk1N |].
      intros z Hz.
      assert (HkzR : mul1 k z ∈ car1) by (apply (@Mult_close RR1 ax1 k z HkR Hz)).
      rewrite (mul1_distr_gen k o1 z HkR o1_car Hz).
      rewrite (one_mul1 z Hz).
      rewrite (HFadd (mul1 k z) z HkzR Hz).
      rewrite (IH z Hz).
      rewrite (psi_add k o1 (N1_to_Q1 k HkN) (N1_to_Q1 o1 (@one_in_N RR1 ax1))).
      rewrite psi_one.
      rewrite (mul2_distr_gen (psi k) o2 (F z)
                 (psi_mem k (N1_to_Q1 k HkN)) o2_car (HFmem z Hz)).
      rewrite (one_mul2 (F z) (HFmem z Hz)). reflexivity. }
  assert (HE : E = N1) by (apply (@MathInd RR1 ax1 E Esub H1 Hclos)).
  intros k HkN z Hz.
  assert (HkE : k ∈ E) by (rewrite HE; exact HkN).
  apply AxiomII in HkE as [_ [_ Hmm]].
  exact (Hmm z Hz).
Qed.

(* ==================== Part 8 : Phi 保乘法 ==================== *)

Lemma mul1_zero_right : ∀ a, a ∈ car1 -> mul1 a z1 = z1.
Proof. intros a Ha. apply (@PlusMult_Co1 RR1 ax1 a Ha). Qed.
Lemma mul2_zero_right : ∀ a, a ∈ car2 -> mul2 a z2 = z2.
Proof. intros a Ha. apply (@PlusMult_Co1 RR2 ax2 a Ha). Qed.

Lemma mul2_div_mul : ∀ a b, a ∈ car2 -> b ∈ car2 -> b ≠ z2 -> mul2 (mul2 a (inv2 b)) b = a.
Proof.
  intros a b Ha Hb Hbne.
  assert (Hb0 : b ∈ (car2 ~ [z2])) by (apply in_sm2; assumption).
  assert (Hib : inv2 b ∈ car2) by (apply inv2_car; exact Hb0).
  transitivity (mul2 a (mul2 (inv2 b) b)).
  - symmetry. apply (mul2_assoc_gen a (inv2 b) b Ha Hib Hb).
  - rewrite (mul2_comm_gen (inv2 b) b Hib Hb). rewrite (inv2_val b Hb0).
    apply mul2_one_self. exact Ha.
Qed.

Lemma mul2_rot : ∀ a b, a ∈ car2 -> b ∈ car2 -> b ≠ z2 -> mul2 (mul2 a b) (inv2 b) = a.
Proof.
  intros a b Ha Hb Hbne.
  assert (Hb0 : b ∈ (car2 ~ [z2])) by (apply in_sm2; assumption).
  assert (Hib : inv2 b ∈ car2) by (apply inv2_car; exact Hb0).
  transitivity (mul2 a (mul2 b (inv2 b))).
  - symmetry. apply (mul2_assoc_gen a b (inv2 b) Ha Hb Hib).
  - rewrite (inv2_val b Hb0). apply mul2_one_self. exact Ha.
Qed.

Lemma Phi_pos_iff : ∀ x, x ∈ car1 -> (lt1 z1 x <-> lt2 z2 (Phi x)).
Proof.
  intros x Hx. split.
  - intros H0. rewrite <- Phi_zero. apply Phi_strict. exact z1_car. exact Hx. exact H0.
  - intros Hlt.
    destruct (@Order_Co1 RR1 ax1 x z1 Hx z1_car) as [Hlt' | [Hgt' | Heq]].
    + exfalso.
      assert (Hle2 : le2 (Phi x) (Phi z1))
        by (apply Phi_mono; [exact Hx | exact z1_car | exact (proj1 Hlt')]).
      rewrite Phi_zero in Hle2.
      exact ((proj2 Hlt) (eq_sym (@Leq_P2 RR2 ax2 (Phi x) z2 (Phi_mem x Hx) z2_car Hle2 (proj1 Hlt)))).
    + exact Hgt'.
    + exfalso. rewrite Heq in Hlt. rewrite Phi_zero in Hlt.
      exact ((proj2 Hlt) eq_refl).
Qed.

Lemma psi_pos_iff : ∀ q, q ∈ Q1 -> (lt1 z1 q <-> lt2 z2 (psi q)).
Proof.
  intros q Hq.
  assert (HqR : q ∈ car1) by (exact (@Q_Subset_R RR1 ax1 q Hq)).
  rewrite <- (Phi_q q Hq). apply Phi_pos_iff. exact HqR.
Qed.

Lemma Phi_Z_hom : ∀ m, m ∈ Z1 -> ∀ z, z ∈ car1 -> Phi (mul1 m z) = mul2 (psi m) (Phi z).
Proof.
  intros m Hm z Hz.
  destruct (Z1_cases m Hm) as [HmN | [Hmneg | Hm0]].
  - apply (add_N_hom Phi Phi_mem Phi_add m HmN z Hz).
  - assert (HmR : m ∈ car1) by (apply Z1_sub_car1; exact Hm).
    assert (Hmm : m = neg1 (neg1 m)) by (exact (eq_sym (neg1_invol m HmR))).
    assert (HmpR : neg1 m ∈ car1) by (apply N1_sub_car1; exact Hmneg).
    assert (HmzR : mul1 (neg1 m) z ∈ car1)
      by (apply (@Mult_close RR1 ax1 (neg1 m) z HmpR Hz)).
    assert (HpsiR : psi m ∈ car2) by (apply psi_mem; exact (Z1_to_Q1 m Hm)).
    assert (Hp : mul1 m z = neg1 (mul1 (neg1 m) z)).
    { transitivity (mul1 (neg1 (neg1 m)) z).
      - apply (f_equal (fun u => mul1 u z) Hmm).
      - rewrite (eq_sym (neg_mul1 (neg1 m) z HmpR Hz)). reflexivity. }
    rewrite Hp.
    rewrite (Phi_neg (mul1 (neg1 m) z) HmzR).
    rewrite (add_N_hom Phi Phi_mem Phi_add (neg1 m) Hmneg z Hz).
    rewrite (psi_neg m (Z1_to_Q1 m Hm)).
    rewrite (neg_mul2 (neg2 (psi m)) (Phi z) (neg2_car (psi m) HpsiR) (Phi_mem z Hz)).
    rewrite (neg2_invol (psi m) HpsiR). reflexivity.
  - rewrite Hm0.
    rewrite (mul1_zero_left z Hz).
    rewrite Phi_zero. rewrite psi_zero.
    rewrite (mul2_zero_left (Phi z) (Phi_mem z Hz)). reflexivity.
Qed.

Lemma Q1_inv : ∀ n, n ∈ Z1 -> n ≠ z1 -> inv1 n ∈ Q1.
Proof.
  intros n Hn Hne.
  assert (HnR : n ∈ car1) by (apply Z1_sub_car1; exact Hn).
  assert (Hn0 : n ∈ (Z1 ~ [z1])).
  { unfold Setminus. apply AxiomII; split.
    - exists car1; exact HnR.
    - split; [exact Hn | apply AxiomII; split; [exists car1; exact HnR | intro Hin;
        exact (Hne (proj1 (MKT41 z1 (Ens_car1 z1 z1_car) n) Hin))]]. }
  apply AxiomII; split.
  - exists car1; apply inv1_car; apply in_sm1; assumption.
  - exists o1, n. split.
    + apply N1_in_Z1; apply (@one_in_N RR1 ax1).
    + split; [exact Hn0 | symmetry; apply one_mul1; apply inv1_car; apply in_sm1; assumption].
Qed.

Lemma Phi_rat_hom : ∀ q, q ∈ Q1 -> ∀ z, z ∈ car1
  -> Phi (mul1 q z) = mul2 (psi q) (Phi z).
Proof.
  intros q Hq z Hz.
  apply AxiomII in Hq as [_ Hq'].
  destruct Hq' as [m [n [Hm [Hn0 Hqe]]]].
  assert (Hn : n ∈ Z1)
    by (pose proof Hn0 as H; unfold Setminus in H; apply AxiomII in H as [_ [Hn _]]; exact Hn).
  assert (Hnz : n ≠ z1).
  { pose proof Hn0 as H. unfold Setminus in H. apply AxiomII in H as [_ [_ Hnot]].
    apply AxiomII in Hnot as [_ Hnot']. intro He.
    exact (Hnot' (proj2 (MKT41 z1 (Ens_car1 z1 z1_car) n) He)). }
  assert (HnR : n ∈ car1) by (apply Z1_sub_car1; exact Hn).
  assert (Hn0' : n ∈ (car1 ~ [z1])) by (apply in_sm1; assumption).
  assert (HinvR : inv1 n ∈ car1) by (apply inv1_car; exact Hn0').
  assert (HmnR : mul1 (inv1 n) z ∈ car1)
    by (apply (@Mult_close RR1 ax1 (inv1 n) z HinvR Hz)).
  assert (HmR : m ∈ car1) by (apply Z1_sub_car1; exact Hm).
  assert (Hq_eq : q = mul1 m (inv1 n)) by (rewrite Hqe; reflexivity).
  rewrite Hq_eq.
  rewrite <- (mul1_assoc_gen m (inv1 n) z HmR HinvR Hz).
  rewrite (Phi_Z_hom m Hm (mul1 (inv1 n) z) HmnR).
  assert (Hkey : Phi (mul1 (inv1 n) z) = mul2 (inv2 (psi n)) (Phi z)).
  { assert (HpsiQ : psi n ∈ car2) by (apply psi_mem; exact (Z1_to_Q1 n Hn)).
    assert (Hpsine : psi n ≠ z2) by (apply psi_ne_zero; assumption).
    assert (Hpsism : psi n ∈ (car2 ~ [z2])) by (apply in_sm2; assumption).
    assert (Hin2R : inv2 (psi n) ∈ car2) by (apply inv2_car; exact Hpsism).
    assert (Hleft : mul2 (psi n) (Phi (mul1 (inv1 n) z)) = Phi z).
    { rewrite <- (Phi_Z_hom n Hn (mul1 (inv1 n) z) HmnR).
      rewrite (mul1_assoc_gen n (inv1 n) z HnR HinvR Hz).
      rewrite (inv1_val n Hn0').
      rewrite (one_mul1 z Hz). reflexivity. }
    assert (Hright : mul2 (psi n) (mul2 (inv2 (psi n)) (Phi z)) = Phi z).
    { rewrite (mul2_assoc_gen (psi n) (inv2 (psi n)) (Phi z) HpsiQ Hin2R (Phi_mem z Hz)).
      rewrite (inv2_val (psi n) Hpsism).
      rewrite (one_mul2 (Phi z) (Phi_mem z Hz)). reflexivity. }
    assert (Heq : mul2 (psi n) (Phi (mul1 (inv1 n) z))
                  = mul2 (psi n) (mul2 (inv2 (psi n)) (Phi z)))
      by (rewrite Hleft; exact (eq_sym Hright)).
    exact (mul2_cancel (psi n) (Phi (mul1 (inv1 n) z)) (mul2 (inv2 (psi n)) (Phi z))
             HpsiQ Hpsine (Phi_mem (mul1 (inv1 n) z) HmnR)
             (@Mult_close RR2 ax2 (inv2 (psi n)) (Phi z) Hin2R (Phi_mem z Hz)) Heq). }
  rewrite Hkey.
  rewrite (mul2_assoc_gen (psi m) (inv2 (psi n)) (Phi z)
             (psi_mem m (Z1_to_Q1 m Hm))
             (inv2_car (psi n) (in_sm2 (psi n) (psi_mem n (Z1_to_Q1 n Hn)) (psi_ne_zero n Hn Hnz)))
             (Phi_mem z Hz)).
  rewrite (psi_rep m n Hm Hn Hnz).
  rewrite (psi_Z m Hm). rewrite (psi_Z n Hn). reflexivity.
Qed.

Lemma mul1_div_lt : ∀ a b c, a ∈ car1 -> b ∈ car1 -> c ∈ car1 -> lt1 z1 c
  -> (lt1 (mul1 a (inv1 c)) b <-> lt1 a (mul1 b c)).
Proof.
  intros a b c Ha Hb Hc H0c.
  assert (Hc0 : c ∈ (car1 ~ [z1]))
    by (apply in_sm1; [exact Hc | intro H; exact (proj2 H0c (eq_sym H))]).
  assert (Hic : inv1 c ∈ car1) by (apply inv1_car; exact Hc0).
  assert (Hicpos : lt1 z1 (inv1 c)) by (apply (@OrderPM_Co10 RR1 ax1 c Hc H0c)).
  assert (Hbc : mul1 b c ∈ car1) by (apply (@Mult_close RR1 ax1 b c Hb Hc)).
  assert (Haic : mul1 a (inv1 c) ∈ car1) by (apply (@Mult_close RR1 ax1 a (inv1 c) Ha Hic)).
  split.
  - intros Hlt.
    assert (H1 : lt1 (mul1 (mul1 a (inv1 c)) c) (mul1 b c))
      by (apply mul1_lt_mono; [exact Haic | exact Hb | exact Hc | exact Hlt | exact H0c]).
    rewrite <- (mul1_assoc_gen a (inv1 c) c Ha Hic Hc) in H1.
    rewrite (inv1_valc c Hc0) in H1.
    rewrite (mul1_one_self a Ha) in H1.
    exact H1.
  - intros Hlt.
    assert (H1 : lt1 (mul1 a (inv1 c)) (mul1 (mul1 b c) (inv1 c)))
      by (apply mul1_lt_mono;
          [exact Ha | exact Hbc | exact Hic | exact Hlt | exact Hicpos]).
    assert (H2 : mul1 (mul1 b c) (inv1 c) = b).
    { transitivity (mul1 b (mul1 c (inv1 c))).
      - symmetry. apply (mul1_assoc_gen b c (inv1 c) Hb Hc Hic).
      - rewrite (inv1_val c Hc0).
        apply mul1_one_self. exact Hb. }
    exact (lt1_rw (mul1 a (inv1 c)) (mul1 a (inv1 c))
             (mul1 (mul1 b c) (inv1 c)) b eq_refl H2 H1).
Qed.

Lemma Phi_mul_cut_pos : ∀ x y q, x ∈ car1 -> y ∈ car1 -> lt1 z1 x -> lt1 z1 y -> q ∈ Q1
  -> (lt1 q (mul1 x y) <-> lt2 (psi q) (mul2 (Phi x) (Phi y))).
Proof.
  intros x y q Hx Hy H0x H0y HqQ.
  assert (HqR : q ∈ car1) by (exact (@Q_Subset_R RR1 ax1 q HqQ)).
  assert (HPhiX : lt2 z2 (Phi x)) by (exact ((proj1 (Phi_pos_iff x Hx)) H0x)).
  assert (HPhiY : lt2 z2 (Phi y)) by (exact ((proj1 (Phi_pos_iff y Hy)) H0y)).
  assert (HPhiYm : Phi y ∈ car2) by (apply Phi_mem; exact Hy).
  assert (Hxy_pos : lt1 z1 (mul1 x y)) by (apply mul1_pos; assumption).
  assert (HxyR : mul1 x y ∈ car1) by (apply (@Mult_close RR1 ax1 x y Hx Hy)).
  assert (HinvY : inv1 y ∈ car1)
    by (apply inv1_car; apply in_sm1; [exact Hy | intro H; exact (proj2 H0y (eq_sym H))]).
  split.
  - intros Hlt.
    assert (H1 : lt1 (mul1 q (inv1 y)) x)
      by (exact ((proj2 (mul1_div_lt q x y HqR Hx Hy H0y)) Hlt)).
    destruct (@Arch_P9 RR1 ax1 (mul1 q (inv1 y)) x
                (@Mult_close RR1 ax1 q (inv1 y) HqR HinvY) Hx H1) as [s [HsQ [Hs1 Hs2]]].
    assert (HsR : s ∈ car1) by (exact (@Q_Subset_R RR1 ax1 s HsQ)).
    assert (H2 : lt1 q (mul1 s y))
      by (exact ((proj1 (mul1_div_lt q s y HqR HsR Hy H0y)) Hs1)).
    assert (H3 : lt2 (psi q) (Phi (mul1 s y)))
      by (exact ((proj1 (Phi_cut (mul1 s y) (@Mult_close RR1 ax1 s y HsR Hy) q HqQ)) H2)).
    rewrite (Phi_rat_hom s HsQ y Hy) in H3.
    assert (H4 : lt2 (psi s) (Phi x))
      by (exact ((proj1 (Phi_cut x Hx s HsQ)) Hs2)).
    assert (H5 : lt2 (mul2 (psi s) (Phi y)) (mul2 (Phi x) (Phi y)))
      by (apply mul2_lt_mono;
          [exact (psi_mem s HsQ) | exact (Phi_mem x Hx) | exact HPhiYm | exact H4 | exact HPhiY]).
    exact (@Order_Co2 RR2 ax2 (psi q) (mul2 (psi s) (Phi y)) (mul2 (Phi x) (Phi y))
             (psi_mem q HqQ) (@Mult_close RR2 ax2 (psi s) (Phi y) (psi_mem s HsQ) HPhiYm)
             (@Mult_close RR2 ax2 (Phi x) (Phi y) (Phi_mem x Hx) HPhiYm)
             (or_introl (conj H3 (proj1 H5)))).
  - intros Hlt.
    destruct (@Order_Co1 RR1 ax1 q z1 HqR z1_car) as [Hqneg | [Hqpos | Hq0]].
    + assert (Hle : le1 q z1) by (exact (proj1 Hqneg)).
      exact (@Order_Co2 RR1 ax1 q z1 (mul1 x y) HqR z1_car HxyR
               (or_introl (conj Hqneg (proj1 Hxy_pos)))).
    + assert (Hpsiq : lt2 z2 (psi q)) by (exact ((proj1 (psi_pos_iff q HqQ)) Hqpos)).
      assert (HPhiY0 : Phi y ≠ z2) by (intro H; exact (proj2 HPhiY (eq_sym H))).
      assert (HPhiYsm : Phi y ∈ (car2 ~ [z2])) by (apply in_sm2; assumption).
      assert (Hinvy : inv2 (Phi y) ∈ car2) by (apply inv2_car; exact HPhiYsm).
      assert (Hinvypos : lt2 z2 (inv2 (Phi y)))
        by (apply (@OrderPM_Co10 RR2 ax2 (Phi y) HPhiYm HPhiY)).
      assert (HqdivR : mul2 (psi q) (inv2 (Phi y)) ∈ car2)
        by (apply (@Mult_close RR2 ax2 (psi q) (inv2 (Phi y)) (psi_mem q HqQ) Hinvy)).
      assert (Ht : lt2 (mul2 (psi q) (inv2 (Phi y))) (Phi x)).
      { assert (Ht' : lt2 (mul2 (psi q) (inv2 (Phi y)))
                      (mul2 (mul2 (Phi x) (Phi y)) (inv2 (Phi y))))
          by (apply mul2_lt_mono;
              [exact (psi_mem q HqQ) | exact (@Mult_close RR2 ax2 (Phi x) (Phi y) (Phi_mem x Hx) HPhiYm)
              | exact Hinvy | exact Hlt | exact Hinvypos]).
        exact (lt2_rw (mul2 (psi q) (inv2 (Phi y))) (mul2 (psi q) (inv2 (Phi y)))
                 (mul2 (mul2 (Phi x) (Phi y)) (inv2 (Phi y))) (Phi x) eq_refl
                 (mul2_rot (Phi x) (Phi y) (Phi_mem x Hx) HPhiYm HPhiY0) Ht'). }
      destruct (@Arch_P9 RR2 ax2 (mul2 (psi q) (inv2 (Phi y))) (Phi x) HqdivR
                  (Phi_mem x Hx) Ht) as [sr [HsrQ [Hsr1 Hsr2]]].
      destruct (psi_surj sr HsrQ) as [s [HsQ Hsr_eq]].
      rewrite <- Hsr_eq in Hsr1. rewrite <- Hsr_eq in Hsr2.
      assert (Hsx : lt1 s x) by (exact ((proj2 (Phi_cut x Hx s HsQ)) Hsr2)).
      assert (Hlt2 : lt2 (psi q) (mul2 (psi s) (Phi y))).
      { assert (Ht1 : lt2 (mul2 (mul2 (psi q) (inv2 (Phi y))) (Phi y))
                        (mul2 (psi s) (Phi y)))
          by (apply mul2_lt_mono;
              [exact HqdivR | exact (psi_mem s HsQ) | exact HPhiYm | exact Hsr1 | exact HPhiY]).
        exact (lt2_rw (mul2 (mul2 (psi q) (inv2 (Phi y))) (Phi y)) (psi q)
                 (mul2 (psi s) (Phi y)) (mul2 (psi s) (Phi y))
                 (mul2_div_mul (psi q) (Phi y) (psi_mem q HqQ) HPhiYm HPhiY0) eq_refl Ht1). }
      assert (H4 : lt1 q (mul1 s y)).
      { apply (proj2 (Phi_cut (mul1 s y) (@Mult_close RR1 ax1 s y (@Q_Subset_R RR1 ax1 s HsQ) Hy) q HqQ)).
        rewrite (Phi_rat_hom s HsQ y Hy). exact Hlt2. }
      assert (H5 : lt1 (mul1 s y) (mul1 x y))
        by (apply mul1_lt_mono;
            [exact (@Q_Subset_R RR1 ax1 s HsQ) | exact Hx | exact Hy | exact Hsx | exact H0y]).
      exact (@Order_Co2 RR1 ax1 q (mul1 s y) (mul1 x y) HqR
               (@Mult_close RR1 ax1 s y (@Q_Subset_R RR1 ax1 s HsQ) Hy) HxyR
               (lt1_le1_or q (mul1 s y) (mul1 x y) H4 (proj1 H5))).
    + rewrite Hq0. exact Hxy_pos.
Qed.

Lemma Phi_mul_pos : ∀ x y, x ∈ car1 -> y ∈ car1 -> lt1 z1 x -> lt1 z1 y
  -> Phi (mul1 x y) = mul2 (Phi x) (Phi y).
Proof.
  intros x y Hx Hy H0x H0y.
  assert (HxyR : mul1 x y ∈ car1) by (apply (@Mult_close RR1 ax1 x y Hx Hy)).
  assert (HsumR : mul2 (Phi x) (Phi y) ∈ car2)
    by (apply (@Mult_close RR2 ax2 (Phi x) (Phi y) (Phi_mem x Hx) (Phi_mem y Hy))).
  exact (@Phi_uniq (mul1 x y) HxyR (Phi (mul1 x y)) (mul2 (Phi x) (Phi y))
          (Phi_mem (mul1 x y) HxyR) HsumR
          (fun q Hq => Phi_cut (mul1 x y) HxyR q Hq)
          (fun q Hq => Phi_mul_cut_pos x y q Hx Hy H0x H0y Hq)).
Qed.

Lemma Phi_mul_pos_right : ∀ x y, x ∈ car1 -> y ∈ car1 -> lt1 z1 y
  -> Phi (mul1 x y) = mul2 (Phi x) (Phi y).
Proof.
  intros x y Hx Hy H0y.
  destruct (@Order_Co1 RR1 ax1 x z1 Hx z1_car) as [Hxneg | [Hxpos | Hx0]].
  - assert (Hx'pos : lt1 z1 (neg1 x)) by (apply negpos1; assumption).
    assert (Hx'R : neg1 x ∈ car1) by (apply neg1_car; exact Hx).
    assert (HxyR : mul1 (neg1 x) y ∈ car1) by (apply (@Mult_close RR1 ax1 (neg1 x) y Hx'R Hy)).
    assert (H1 : Phi (mul1 (neg1 x) y) = mul2 (Phi (neg1 x)) (Phi y))
      by (apply Phi_mul_pos; assumption).
    assert (H2 : mul1 x y = neg1 (mul1 (neg1 x) y)).
    { transitivity (mul1 (neg1 (neg1 x)) y).
      - rewrite (neg1_invol x Hx). reflexivity.
      - rewrite (eq_sym (neg_mul1 (neg1 x) y Hx'R Hy)). reflexivity. }
    rewrite H2.
    rewrite (Phi_neg (mul1 (neg1 x) y) HxyR).
    rewrite H1.
    rewrite (Phi_neg x Hx).
    rewrite (neg_mul2 (neg2 (Phi x)) (Phi y) (neg2_car (Phi x) (Phi_mem x Hx)) (Phi_mem y Hy)).
    rewrite (neg2_invol (Phi x) (Phi_mem x Hx)). reflexivity.
  - apply Phi_mul_pos; assumption.
  - rewrite Hx0. rewrite (mul1_zero_left y Hy). rewrite Phi_zero.
    rewrite (mul2_zero_left (Phi y) (Phi_mem y Hy)). reflexivity.
Qed.

Lemma Phi_mul : ∀ x y, x ∈ car1 -> y ∈ car1 -> Phi (mul1 x y) = mul2 (Phi x) (Phi y).
Proof.
  intros x y Hx Hy.
  destruct (@Order_Co1 RR1 ax1 y z1 Hy z1_car) as [Hyneg | [Hypos | Hy0]].
  - assert (Hy'pos : lt1 z1 (neg1 y)) by (apply negpos1; assumption).
    assert (Hy'R : neg1 y ∈ car1) by (apply neg1_car; exact Hy).
    assert (Hxy'R : mul1 x (neg1 y) ∈ car1)
      by (apply (@Mult_close RR1 ax1 x (neg1 y) Hx Hy'R)).
    assert (H1 : Phi (mul1 x (neg1 y)) = mul2 (Phi x) (Phi (neg1 y)))
      by (apply Phi_mul_pos_right; assumption).
    assert (H2 : mul1 x y = neg1 (mul1 x (neg1 y))).
    { transitivity (mul1 x (neg1 (neg1 y))).
      - rewrite (neg1_invol y Hy). reflexivity.
      - rewrite (eq_sym (mul_neg1 x (neg1 y) Hx Hy'R)). reflexivity. }
    rewrite H2.
    rewrite (Phi_neg (mul1 x (neg1 y)) Hxy'R).
    rewrite H1.
    rewrite (Phi_neg y Hy).
    rewrite (mul_neg2 (Phi x) (neg2 (Phi y)) (Phi_mem x Hx) (neg2_car (Phi y) (Phi_mem y Hy))).
    rewrite (neg2_invol (Phi y) (Phi_mem y Hy)). reflexivity.
  - apply Phi_mul_pos_right; assumption.
  - rewrite Hy0. rewrite (mul1_zero_right x Hx). rewrite Phi_zero.
    rewrite (mul2_zero_right (Phi x) (Phi_mem x Hx)). reflexivity.
Qed.

(* ==================== Part 9 : 同构映射 PhiRel 与主定理 ==================== *)

Definition PhiRel : Class := \{\ λ u v, u ∈ car1 /\ v = Phi u \}\.

Lemma PhiRel_char : ∀ u v, [u,v] ∈ PhiRel -> u ∈ car1 /\ v = Phi u.
Proof.
  intros u v Huv.
  apply AxiomII in Huv as [Euv Huv'].
  destruct Huv' as [a [b [Hab [Ha Hb]]]].
  destruct (MKT49b u v Euv) as [Eu Ev].
  assert (Eab : Ensemble ([a,b])) by (rewrite <- Hab; exact Euv).
  destruct (MKT49b a b Eab) as [Ea Eb].
  destruct (proj1 (MKT55 u v a b Eu Ev) Hab) as [Hua Hvb].
  subst a. subst b.
  split; assumption.
Qed.

Lemma PhiRel_intro : ∀ u v, u ∈ car1 -> v = Phi u -> [u,v] ∈ PhiRel.
Proof.
  intros u v Hu Hv.
  assert (Ev : Ensemble v) by (rewrite Hv; apply Ens_car2; apply Phi_mem; exact Hu).
  assert (Eu : Ensemble u) by (exact (Ens_car1 u Hu)).
  apply AxiomII; split.
  - apply MKT49a; assumption.
  - exists u, v. split; [reflexivity | split; [exact Hu | exact Hv]].
Qed.

Lemma PhiRel_func : Function PhiRel.
Proof.
  assert (Hrel : Relation PhiRel).
  { intros z Hz. apply AxiomII in Hz as [Ez Hz'].
    destruct Hz' as [a [b [Hab _]]]. exists a. exists b. exact Hab. }
  assert (Hsingle : ∀ u v w, [u,v] ∈ PhiRel -> [u,w] ∈ PhiRel -> v = w).
  { intros u v w Huv Huw.
    destruct (PhiRel_char u v Huv) as [_ Hv].
    destruct (PhiRel_char u w Huw) as [_ Hw].
    rewrite Hv. rewrite Hw. reflexivity. }
  split; [exact Hrel | exact Hsingle].
Qed.

Lemma PhiRel_val : ∀ x, x ∈ car1 -> PhiRel[x] = Phi x.
Proof.
  intros x Hx.
  apply (MKT_fval PhiRel x (Phi x) PhiRel_func).
  apply PhiRel_intro. exact Hx. reflexivity.
Qed.

(* ---------------- 零元与单位元的对应关系 ---------------- *)
(* 最终同构映射 PhiRel 把 RR1 的零元/单位元送到 RR2 的零元/单位元 *)

Lemma PhiRel_zero : PhiRel[z1] = z2.
Proof.
  transitivity (Phi z1).
  - exact (PhiRel_val z1 z1_car).
  - apply Phi_zero.
Qed.

Lemma PhiRel_one : PhiRel[o1] = o2.
Proof.
  transitivity (Phi o1).
  - exact (PhiRel_val o1 o1_car).
  - apply Phi_one.
Qed.

Lemma PhiRel_zero_one : PhiRel[z1] = z2 /\ PhiRel[o1] = o2.
Proof.
  split; [apply PhiRel_zero | apply PhiRel_one].
Qed.

Lemma Phi_iso : R_iso RR1 RR2 ax1 ax2 PhiRel.
Proof.
  split; [exact PhiRel_func |].
  split.
  - intros x Hx. rewrite (PhiRel_val x Hx). apply Phi_mem; exact Hx.
  - split.
    + intros x Hx y Hy.
      assert (Hsum : (@fp RR1)[[x, y]] ∈ car1) by (apply (@Plus_close RR1 ax1 x y Hx Hy)).
      rewrite (PhiRel_val ((@fp RR1)[[x, y]]) Hsum).
      rewrite (PhiRel_val x Hx). rewrite (PhiRel_val y Hy).
      apply (@Phi_add x y Hx Hy).
    + split.
      * intros x Hx y Hy.
        assert (Hprod : (@fm RR1)[[x, y]] ∈ car1) by (apply (@Mult_close RR1 ax1 x y Hx Hy)).
        rewrite (PhiRel_val ((@fm RR1)[[x, y]]) Hprod).
        rewrite (PhiRel_val x Hx). rewrite (PhiRel_val y Hy).
        apply (@Phi_mul x y Hx Hy).
      * split.
        { intros x Hx y Hy.
          rewrite (PhiRel_val x Hx). rewrite (PhiRel_val y Hy).
          split.
          - intros Hle. apply Phi_mono; assumption.
          - intros Hle.
            destruct (@Order_Co1 RR1 ax1 x y Hx Hy) as [Hlt | [Hgt | Heq]].
            + exact (proj1 Hlt).
            + exfalso.
              assert (H2 : lt2 (Phi y) (Phi x)) by (apply Phi_strict; assumption).
              exact ((proj2 H2) (@Leq_P2 RR2 ax2 (Phi y) (Phi x) (Phi_mem y Hy)
                       (Phi_mem x Hx) (proj1 H2) Hle)).
            + rewrite Heq. apply (@Leq_P1 RR1 ax1 y Hy). }
        { split.
          - intros x Hx y Hy Heq.
            rewrite (PhiRel_val x Hx) in Heq.
            rewrite (PhiRel_val y Hy) in Heq.
            apply (Phi_inj x y Hx Hy); exact Heq.
          - intros b Hb. destruct (Phi_surj b Hb) as [x [Hx Hxeq]].
            exists x. split; [exact Hx | rewrite (PhiRel_val x Hx); exact Hxeq]. }
Qed.

End Isomorphism.

(* ==================== 主定理 ==================== *)

Theorem Real_struct_isomorphic :
  ∀ (RR1 RR2 : Real_struct) (ax1 : Real_axioms RR1) (ax2 : Real_axioms RR2),
    ∃ f, R_iso RR1 RR2 ax1 ax2 f.
Proof.
  intros RR1 RR2 ax1 ax2.
  eexists.
  apply Phi_iso.
Qed.
