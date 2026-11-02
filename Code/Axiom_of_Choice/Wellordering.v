(***************************************************************************)
(*     This is part of AST_AC, it is distributed under the terms of the    *)
(*             GNU Lesser General Public License version 3                 *)
(*                (see file LICENSE for more details)                      *)
(*                                                                         *)
(*            Copyright 2025-2030: Tianyu Sun, Yaoshun Fu,                 *)
(*                Ce Zhang, Si Chen and Wensheng Yu.                       *)
(***************************************************************************)

Require Export Maximal_Principle.


(** Zorn Lemma **)
Definition F_x X le x:= \{λ u,u∈X /\ Rrelation u le x\}.

Definition FA_a A X le := \{λ u,exists a, a∈A /\ u= F_x X le a \}.

Definition En_A X A le := \{ λ u, u∈X /\ (F_x X le u) ∈ A \}.

Theorem Zorn : forall X le, PartialOrder le X ->
  (forall A, Chain A X le -> exists y, BoundU y A X le) ->
  (exists z, MaxElement z X le).
Proof.
  intros X le HPO Hbound.
  pose proof HPO as HPO'.
  destruct HPO as [HXE [Hle [Href [Hanti Htrans]]]].
  destruct Hle as [HleRel HleSub].
  destruct (classic (X = Φ)) as [HXΦ | HXne].
  - exists Φ. unfold MaxElement. intros H. exfalso. exact (H HXΦ).
  - set (K := \{ λ C, C ⊂ X /\ (∀ a b, a ∈ C -> b ∈ C ->
        a = b \/ Rrelation a le b \/ Rrelation b le a) \}).
    assert (EK : Ensemble K).
    { apply (MKT33 (pow(X)) K (MKT38a HXE)).
      intros C HC. unfold K in HC.
      apply AxiomII in HC as [EC [HCX _]].
      apply AxiomII; split; [exact EC | exact HCX]. }
    assert (HKK : Φ ∈ K).
    { unfold K. apply AxiomII; split.
      - exact (MKT33 X Φ HXE (MKT26 X)).
      - split.
        + apply MKT26.
        + intros a b Ha. exfalso. exact (MKT16 Ha). }
    assert (HKne : K ≠ Φ).
    { intro H0. rewrite H0 in HKK. exact (MKT16 HKK). }
    assert (HKbound : ∀ n, n ⊂ K /\ Nest n -> ∃ N, N ∈ K /\ (∀ u, u ∈ n -> u ⊂ N)).
    { intros n [HnK Hnest].
      assert (En : Ensemble n) by (exact (MKT33 K n EK HnK)).
      exists (∪n). split.
      - unfold K. apply AxiomII; split.
        + exact (AxiomVI n En).
        + split.
          * intros s Hs.
            apply AxiomII in Hs as [_ [u [Hsu Hun]]].
            assert (HuK : u ∈ K) by (exact (HnK u Hun)).
            unfold K in HuK. apply AxiomII in HuK as [_ [HuX _]].
            exact (HuX s Hsu).
          * intros a b Ha Hb.
            apply AxiomII in Ha as [_ [u1 [Hau1 Hu1n]]].
            apply AxiomII in Hb as [_ [u2 [Hbu2 Hu2n]]].
            destruct (Hnest u1 u2 (conj Hu1n Hu2n)) as [H12 | H21].
            -- assert (Hu2K : u2 ∈ K) by (exact (HnK u2 Hu2n)).
               unfold K in Hu2K. apply AxiomII in Hu2K as [_ [_ Ht]].
               exact (Ht a b (H12 a Hau1) Hbu2).
            -- assert (Hu1K : u1 ∈ K) by (exact (HnK u1 Hu1n)).
               unfold K in Hu1K. apply AxiomII in Hu1K as [_ [_ Ht]].
               exact (Ht a b Hau1 (H21 b Hbu2)).
      - intros u Hun. exact (proj1 (MKT32 u n Hun)). }
    destruct (MaxPrinciple K EK HKbound) as [M HM].
    pose proof (HM HKne) as [HMK HMmax].
    unfold K in HMK. apply AxiomII in HMK as [EM [HMX HMtot]].
    assert (HMne : M ≠ Φ).
    { intro H0.
      destruct (MKT_nonempty X HXne) as [x HxX].
      assert (Ex : Ensemble x) by (unfold Ensemble; exists X; exact HxX).
      assert (Esx : Ensemble ([x])) by (apply MKT42; exact Ex).
      assert (HsxK : [x] ∈ K).
      { unfold K. apply AxiomII; split; [exact Esx | split].
        - intros s Hs. apply (proj1 (MKT41 x Ex s)) in Hs. subst s. exact HxX.
        - intros a b Ha Hb.
          apply (proj1 (MKT41 x Ex a)) in Ha.
          apply (proj1 (MKT41 x Ex b)) in Hb.
          rewrite Ha. rewrite Hb. left. reflexivity. }
      assert (Hprop : M ⊊ [x]).
      { unfold ProperIncluded. split.
        - intros s Hs. exfalso. rewrite H0 in Hs. exact (MKT16 Hs).
        - intro Heq.
          assert (Hxin : x ∈ [x]) by (apply (proj2 (MKT41 x Ex x)); reflexivity).
          rewrite <- Heq in Hxin. rewrite H0 in Hxin. exact (MKT16 Hxin). }
      exact (HMmax ([x]) HsxK Hprop). }
    assert (HpairMM : ∀ a b, a ∈ M -> b ∈ M -> [a,b] ∈ M × M).
    { intros a b Ha Hb.
      assert (Ea : Ensemble a) by (unfold Ensemble; exists M; exact Ha).
      assert (Eb : Ensemble b) by (unfold Ensemble; exists M; exact Hb).
      apply AxiomII; split.
      - apply MKT49a; assumption.
      - exists a; exists b; split; [reflexivity | split; assumption]. }
    assert (HpairMMout : ∀ a b, [a,b] ∈ M × M -> a ∈ M /\ b ∈ M).
    { intros a b Hab.
      apply AxiomII in Hab as [_ [u [v [Huv [HuM HvM]]]]].
      assert (Eu : Ensemble u) by (unfold Ensemble; exists M; exact HuM).
      assert (Ev : Ensemble v) by (unfold Ensemble; exists M; exact HvM).
      destruct (proj1 (MKT55 u v a b Eu Ev) (eq_sym Huv)) as [Hua Hvb].
      split; [rewrite <- Hua; exact HuM | rewrite <- Hvb; exact HvM]. }
    assert (HensR : ∀ a b, Rrelation a le b -> Ensemble ([a,b])).
    { intros a b Hab.
      assert (HSub : [a,b] ∈ X × X) by (exact (HleSub ([a,b]) Hab)).
      apply AxiomII in HSub as [E _]. exact E. }
    assert (HRin : ∀ a b, a ∈ M -> b ∈ M -> Rrelation a le b
      -> Rrelation a (le ∩ (M × M)) b).
    { intros a b Ha Hb Hab.
      apply AxiomII; split.
      - exact (HensR a b Hab).
      - split; [exact Hab | exact (HpairMM a b Ha Hb)]. }
    assert (HRout : ∀ a b, Rrelation a (le ∩ (M × M)) b -> Rrelation a le b).
    { intros a b Hab. apply AxiomII in Hab as [_ [H1 _]]. exact H1. }
    assert (HRoutM : ∀ a b, Rrelation a (le ∩ (M × M)) b -> a ∈ M /\ b ∈ M).
    { intros a b Hab. apply AxiomII in Hab as [_ [_ H2]]. exact (HpairMMout a b H2). }
    assert (HtotM : ∀ a b, a ∈ M -> b ∈ M -> a ≠ b ->
      Rrelation a (le ∩ (M × M)) b \/ Rrelation b (le ∩ (M × M)) a).
    { intros a b Ha Hb Hne.
      destruct (HMtot a b Ha Hb) as [Heq | [Hab | Hba]].
      - exfalso. exact (Hne Heq).
      - left. exact (HRin a b Ha Hb Hab).
      - right. exact (HRin b a Hb Ha Hba). }
    assert (Hchain : Chain M X le).
    { unfold Chain. intros Hpo. split.
      - split; [exact HMX | exact HMne].
      - unfold TotalOrder. split.
        + unfold PartialOrder. split.
          * exact EM.
          * split.
            -- split.
               ++ intros z Hz. apply AxiomII in Hz as [_ [Hzle _]].
                  unfold Relation in HleRel. exact (HleRel z Hzle).
               ++ intros z Hz. apply AxiomII in Hz as [_ [_ Hz2]]. exact Hz2.
            -- split.
               ++ intros a Ha. exact (HRin a a Ha Ha (Href a (HMX a Ha))).
               ++ split.
                  ** intros x y [Hx Hy] [Hxy Hyx].
                     exact (Hanti x y (conj (HMX x Hx) (HMX y Hy))
                              (conj (HRout x y Hxy) (HRout y x Hyx))).
                  ** intros u v w [[Hu [Hv Hw]] [Huv Hvw]].
                     exact (HRin u w Hu Hw
                              (Htrans u v w
                                (conj (conj (HMX u Hu) (conj (HMX v Hv) (HMX w Hw)))
                                      (conj (HRout u v Huv) (HRout v w Hvw))))).
        + intros x y [Hx Hy] Hne. exact (HtotM x y Hx Hy Hne). }
    destruct (Hbound M Hchain) as [y Hyb].
    destruct (Hyb (conj HPO' HXne)) as [HyX [HMX' HyUp]].
    exists y. unfold MaxElement. intros _. split; [exact HyX |].
    intros z HzX [Hyz Hyzne].
    exfalso.
    assert (HznM : z ∉ M).
    { intro HzM.
      assert (Hzley : Rrelation z le y) by (exact (HyUp z HzM)).
      assert (Hzy : z = y) by (exact (Hanti z y (conj HzX HyX) (conj Hzley Hyz))).
      exact (Hyzne (eq_sym Hzy)). }
    assert (Ez : Ensemble z) by (unfold Ensemble; exists X; exact HzX).
    assert (Esz : Ensemble ([z])) by (apply MKT42; exact Ez).
    assert (EMz : Ensemble (M ∪ [z])) by (apply AxiomIV; [exact EM | exact Esz]).
    assert (HMzK : M ∪ [z] ∈ K).
    { unfold K. apply AxiomII; split; [exact EMz | split].
      - intros s Hs.
        apply AxiomII in Hs as [Es [Hs1 | Hs2]].
        + exact (HMX s Hs1).
        + apply (proj1 (MKT41 z Ez s)) in Hs2. subst s. exact HzX.
      - intros a b Ha Hb.
        apply AxiomII in Ha as [_ [Ha1 | Ha2]].
        + apply AxiomII in Hb as [_ [Hb1 | Hb2]].
          * exact (HMtot a b Ha1 Hb1).
          * apply (proj1 (MKT41 z Ez b)) in Hb2. subst b.
            right. left.
            exact (Htrans a y z (conj (conj (HMX a Ha1) (conj HyX HzX))
                                      (conj (HyUp a Ha1) Hyz))).
        + apply AxiomII in Hb as [_ [Hb1 | Hb2]].
          * apply (proj1 (MKT41 z Ez a)) in Ha2. subst a.
            right. right.
            exact (Htrans b y z (conj (conj (HMX b Hb1) (conj HyX HzX))
                                      (conj (HyUp b Hb1) Hyz))).
          * apply (proj1 (MKT41 z Ez a)) in Ha2.
            apply (proj1 (MKT41 z Ez b)) in Hb2.
            left. rewrite Ha2. rewrite Hb2. reflexivity. }
    assert (Hprop : M ⊊ (M ∪ [z])).
    { unfold ProperIncluded. split.
      - intros s Hs. apply AxiomII; split; [unfold Ensemble; exists M; exact Hs | left; exact Hs].
      - intro Heq.
        assert (Hzin : z ∈ M ∪ [z]).
        { apply AxiomII; split; [exact Ez | right; apply (proj2 (MKT41 z Ez z)); reflexivity]. }
        apply HznM. rewrite <- Heq in Hzin. exact Hzin. }
    exact (HMmax (M ∪ [z]) HMzK Hprop).
Qed.


(** Well-Ordering MKT **)

Definition En_L X := \{\ λ Y le, Y ⊂ X /\ Y ≠ Φ /\ WellOrder le Y\}\.

Definition lee X: Class :=
  \{\ λ L1 L2, (L1 ∈ (En_L X) /\ L2 ∈ (En_L X)) /\
  (forall x y, x∈(First L1) /\ y∈(First L1) ->
  (Rrelation x (Second L1) y <-> Rrelation x (Second L2) y)) /\
  Initial_Segment (First L1) (First L2) (Second L2) \}\.

Definition En_Z K := \{ λ x, exists Y le, [Y,le] ∈ K /\ x∈Y \}.

Definition leeq K : Class :=
  \{\ λ u v, exists Y le, [Y,le] ∈ K /\ u∈Y /\ v∈Y /\ Rrelation u le v \}\.

Definition leep Y le x :=
  \{\ λ y1 y2, (y1∈Y /\ y2∈Y /\ Rrelation y1 le y2) \/ (y1∈(Y∪[x]) /\ y2=x) \}\.

Definition leq Y := \{\ λ y1 y2, y1∈Y /\ y2∈Y /\ y1 = y2 \}\.

Theorem WellOrderMKT : forall (X: Class),
  Ensemble X -> exists le0: Class, WellOrder le0 X.
Proof.
  intros X HX.
  destruct (MKT140 X HX) as [f [Hf11 [Hfran HfdomR]]].
  destruct Hf11 as [Hf Hfinv].
  set (α := dom(f)).
  set (g := f⁻¹).
  assert (HαR : α ∈ R) by (unfold α; exact HfdomR).
  assert (HαE : Ensemble α).
  { apply AxiomII in HαR as [E _]. exact E. }
  assert (HαOrd : Ordinal α).
  { apply AxiomII in HαR as [_ H]. exact H. }
  assert (Hg : Function g) by (unfold g; exact Hfinv).
  assert (Hgdom : dom(g) = X).
  { unfold g. rewrite MKT_dom_inv. exact Hfran. }
  assert (Hgval : ∀ u, u ∈ X -> [u, g[u]] ∈ g).
  { intros u Hu. apply (MKT_dom_val g u Hg). rewrite Hgdom. exact Hu. }
  assert (HgEns : ∀ u, u ∈ X -> Ensemble (g[u])).
  { intros u Hu.
    assert (Hug : [u, g[u]] ∈ g) by (exact (Hgval u Hu)).
    assert (E : Ensemble ([u, g[u]])) by (unfold Ensemble; exists g; exact Hug).
    exact (proj2 (MKT49b u (g[u]) E)). }
  assert (Hgmem : ∀ u, u ∈ X -> g[u] ∈ α).
  { intros u Hu.
    assert (Hug : [u, g[u]] ∈ g) by (exact (Hgval u Hu)).
    assert (Hr : g[u] ∈ ran(g)).
    { apply AxiomII; split; [exact (HgEns u Hu) | exists u; exact Hug]. }
    unfold g in Hr. rewrite MKT_ran_inv in Hr. exact Hr. }
  assert (Hginj : ∀ u v, u ∈ X -> v ∈ X -> g[u] = g[v] -> u = v).
  { intros u v Hu Hv Heq.
    assert (Hug : [u, g[u]] ∈ g) by (exact (Hgval u Hu)).
    assert (Hvg : [v, g[v]] ∈ g) by (exact (Hgval v Hv)).
    assert (Eu : Ensemble u) by (unfold Ensemble; exists X; exact Hu).
    assert (Ev : Ensemble v) by (unfold Ensemble; exists X; exact Hv).
    assert (Hfu : [g[u], u] ∈ f).
    { unfold g in Hug. apply (proj1 (MKT_inv_in f u (g[u]) Eu (HgEns u Hu))). exact Hug. }
    assert (Hfv : [g[v], v] ∈ f).
    { unfold g in Hvg. apply (proj1 (MKT_inv_in f v (g[v]) Ev (HgEns v Hv))). exact Hvg. }
    rewrite <- Heq in Hfv.
    exact (proj2 Hf (g[u]) u v Hfu Hfv). }
  assert (Hord : ∀ u, u ∈ X -> Ordinal (g[u])).
  { intros u Hu. exact (MKT111 α (g[u]) HαOrd (Hgmem u Hu)). }
  assert (HEmem : ∀ a b, Ensemble a -> Ensemble b -> ([a,b] ∈ E <-> a ∈ b)).
  { intros a b Ea Eb; split.
    - intros Hab. unfold E in Hab. apply AxiomII in Hab as [_ [a' [b' [Ha'b' Ha']]]].
      destruct (proj1 (MKT55 a b a' b' Ea Eb) Ha'b') as [Haa' Hbb'].
      rewrite Haa'. rewrite Hbb'. exact Ha'.
    - intros Hab. unfold E. apply AxiomII; split.
      + apply MKT49a; assumption.
      + exists a; exists b; split; [reflexivity | exact Hab]. }
  set (le0 := \{\ λ u v, u ∈ X /\ v ∈ X /\ (g[u] ∈ g[v] \/ g[u] = g[v]) \}\).
  assert (Hle0in : ∀ u v, u ∈ X -> v ∈ X -> (g[u] ∈ g[v] \/ g[u] = g[v])
    -> [u,v] ∈ le0).
  { intros u v Hu Hv Hr.
    assert (Eu : Ensemble u) by (unfold Ensemble; exists X; exact Hu).
    assert (Ev : Ensemble v) by (unfold Ensemble; exists X; exact Hv).
    assert (Euv : Ensemble ([u,v])) by (apply MKT49a; assumption).
    unfold le0. apply AxiomII; split; [exact Euv |].
    exists u; exists v; split; [reflexivity |
      split; [exact Hu | split; [exact Hv | exact Hr]]]. }
  assert (Hle0out : ∀ u v, [u,v] ∈ le0 ->
    u ∈ X /\ v ∈ X /\ (g[u] ∈ g[v] \/ g[u] = g[v])).
  { intros u v H.
    unfold le0 in H. apply AxiomII in H as [E H].
    destruct H as [u' [v' [Huv Hpred]]].
    assert (Eu : Ensemble u) by (exact (proj1 (MKT49b u v E))).
    assert (Ev : Ensemble v) by (exact (proj2 (MKT49b u v E))).
    destruct (proj1 (MKT55 u v u' v' Eu Ev) Huv) as [Huu' Hvv'].
    subst u'. subst v'. exact Hpred. }
  assert (Hrefl : Reflexivity le0 X).
  { intros a Ha. apply Hle0in; [exact Ha | exact Ha | right; reflexivity]. }
  assert (Hanti0 : Antisymmetry le0 X).
  { intros x y [Hx Hy] [Hxy Hyx].
    destruct (Hle0out x y Hxy) as [_ [_ [H1 | H1]]].
    - destruct (Hle0out y x Hyx) as [_ [_ [H2 | H2]]].
      + exfalso. exact (MKT102 (g[x]) (g[y]) H1 H2).
      + rewrite H2 in H1. exfalso. exact (MKT101 (g[x]) H1).
    - destruct (Hle0out y x Hyx) as [_ [_ [H2 | H2]]].
      + rewrite H1 in H2. exfalso. exact (MKT101 (g[y]) H2).
      + exact (Hginj x y Hx Hy H1). }
  assert (Htrans0 : Transitivity le0 X).
  { intros u v w [[Hu [Hv Hw]] [Huv Hvw]].
    destruct (Hle0out u v Huv) as [_ [_ [H1 | H1]]].
    - destruct (Hle0out v w Hvw) as [_ [_ [H2 | H2]]].
      + assert (Hsub : g[v] ⊂ g[w]).
        { destruct (Hord w Hw) as [_ Hfull]. exact (Hfull (g[v]) H2). }
        apply Hle0in; [exact Hu | exact Hw | left; exact (Hsub (g[u]) H1)].
      + apply Hle0in; [exact Hu | exact Hw | left; rewrite <- H2; exact H1].
    - destruct (Hle0out v w Hvw) as [_ [_ [H2 | H2]]].
      + apply Hle0in; [exact Hu | exact Hw | left; rewrite H1; exact H2].
      + apply Hle0in; [exact Hu | exact Hw | right; rewrite H1; exact H2]. }
  assert (Htot0 : ∀ x y, x ∈ X /\ y ∈ X ->
    (x ≠ y -> Rrelation x le0 y \/ Rrelation y le0 x)).
  { intros x y [Hx Hy] Hne.
    assert (Hne' : g[x] ≠ g[y]) by (intro H; exact (Hne (Hginj x y Hx Hy H))).
    destruct (MKT107 (x:=α) HαOrd) as [Hconn _].
    destruct (Hconn (g[x]) (g[y]) (Hgmem x Hx) (Hgmem y Hy)) as [H1 | [H2 | H3]].
    - left. apply Hle0in; [exact Hx | exact Hy | left].
      exact (proj1 (HEmem (g[x]) (g[y]) (HgEns x Hx) (HgEns y Hy)) H1).
    - right. apply Hle0in; [exact Hy | exact Hx | left].
      exact (proj1 (HEmem (g[y]) (g[x]) (HgEns y Hy) (HgEns x Hx)) H2).
    - exfalso. exact (Hne' H3). }
  assert (Hwo0 : ∀ A, A ⊂ X /\ A ≠ Φ -> exists z, MinElement z A le0).
  { intros A [HAX HANe].
    set (A' := \{ λ w, w ∈ α /\ ∃ a, a ∈ A /\ w = g[a] \}).
    assert (HA'sub : A' ⊂ α).
    { intros w Hw. unfold A' in Hw. apply AxiomII in Hw as [_ [Hwα _]]. exact Hwα. }
    assert (HA'ne : A' ≠ Φ).
    { intro H0.
      destruct (MKT_nonempty A HANe) as [a Ha].
      assert (Hin : g[a] ∈ A').
      { unfold A'. apply AxiomII; split.
        - exact (HgEns a (HAX a Ha)).
        - split; [exact (Hgmem a (HAX a Ha)) | exists a; split; [exact Ha | reflexivity]]. }
      rewrite H0 in Hin. exact (MKT16 Hin). }
    destruct (MKT107 (x:=α) HαOrd) as [_ Hwosub].
    destruct (Hwosub A' HA'sub HA'ne) as [z [HzA' Hzfirst]].
    unfold A' in HzA'. apply AxiomII in HzA' as [_ [Hzα [a [HaA Hza]]]].
    exists a. unfold MinElement. intros HAne'.
    split; [exact HaA |].
    intros y HyA [Hyz Hyne].
    destruct (Hle0out y a Hyz) as [HyX [HaX [H1 | H1]]].
    - assert (HgyA' : g[y] ∈ A').
      { unfold A'. apply AxiomII; split.
        - exact (HgEns y HyX).
        - split; [exact (Hgmem y HyX) | exists y; split; [exact HyA | reflexivity]]. }
      assert (HinE : Rrelation (g[y]) E z).
      { rewrite Hza.
        exact (proj2 (HEmem (g[y]) (g[a]) (HgEns y HyX) (HgEns a HaX)) H1). }
      exact (Hzfirst (g[y]) HgyA' HinE).
    - assert (Hya : y = a) by (exact (Hginj y a HyX HaX H1)).
      apply Hyne. symmetry. exact Hya. }
  exists le0. unfold WellOrder. split.
  - unfold TotalOrder. split.
    + unfold PartialOrder. split.
      * exact HX.
      * split.
        -- split.
           ++ intros z Hz. unfold le0 in Hz. apply AxiomII in Hz as [E Hz].
              destruct Hz as [u [v [Hzuv _]]]. exists u; exists v; exact Hzuv.
           ++ intros z Hz. unfold le0 in Hz. apply AxiomII in Hz as [E Hz].
              destruct Hz as [u [v [Hzuv [Hu [Hv _]]]]].
              apply AxiomII; split; [exact E |].
              exists u; exists v; split; [exact Hzuv | split; [exact Hu | exact Hv]].
        -- split.
           ++ exact Hrefl.
           ++ split; [exact Hanti0 | exact Htrans0].
    + exact Htot0.
  - exact Hwo0.
Qed.


(** The proof of AC **)

Definition En_CF X le := \{\ λ x y, x ∈ (pow(X)~[Φ]) /\ y∈x /\ 
  (exists z0, MinElement z0 x le /\ y = z0) \}\.

Theorem WellOrder_AC : forall (X: Class),
  Ensemble X -> exists c, Choice_Function c X.
Proof.
  intros X HX.
  destruct (WellOrderMKT X HX) as [le HW].
  destruct HW as [HTO Hwo].
  destruct HTO as [HPO Htot].
  set (F := pow(X) ~ [Φ]).
  assert (EPhi : Ensemble Φ) by (apply (MKT33 X Φ HX (MKT26 X))).
  assert (HFchar : ∀ A, A ∈ F <-> Ensemble A /\ A ⊂ X /\ A ∉ [Φ]).
  { intros A. unfold F. split.
    - intros H. apply AxiomII in H as [EA [H1 H2]].
      apply AxiomII in H1 as [_ H1']. apply AxiomII in H2 as [_ H2'].
      split; [exact EA | split; [exact H1' | exact H2']].
    - intros [EA [HAX HAn]]. apply AxiomII; split; [exact EA | split].
      + apply AxiomII; split; [exact EA | exact HAX].
      + apply AxiomII; split; [exact EA | exact HAn]. }
  assert (HFne : ∀ A, A ∈ F -> A ≠ Φ).
  { intros A HA HEq.
    destruct (proj1 (HFchar A) HA) as [EA [HAX HAn]].
    apply HAn. rewrite HEq. apply (proj2 (MKT41 Φ EPhi Φ)); reflexivity. }
  assert (Hminex : ∀ A, A ∈ F -> ∃ z, MinElement z A le).
  { intros A HA.
    destruct (proj1 (HFchar A) HA) as [EA [HAX HAn]].
    exact (Hwo A (conj HAX (HFne A HA))). }
  assert (Hminuniq : ∀ A y1 y2, A ∈ F -> MinElement y1 A le
    -> MinElement y2 A le -> y1 = y2).
  { intros A y1 y2 HAF Hm1 Hm2.
    destruct (proj1 (HFchar A) HAF) as [EA [HAX HAn]].
    assert (HAne : A ≠ Φ) by (exact (HFne A HAF)).
    destruct (Hm1 HAne) as [Hy1A Hm1'].
    destruct (Hm2 HAne) as [Hy2A Hm2'].
    destruct (classic (y1 = y2)) as [Heq | Hne].
    - exact Heq.
    - destruct (Htot y1 y2 (conj (HAX y1 Hy1A) (HAX y2 Hy2A)) Hne) as [H12 | H21].
      + exfalso. exact (Hm2' y1 Hy1A (conj H12 (fun H => Hne (eq_sym H)))).
      + exfalso. exact (Hm1' y2 Hy2A (conj H21 Hne)). }
  set (c := En_CF X le).
  assert (Hc_in : ∀ A y, Ensemble ([A,y]) -> A ∈ F -> y ∈ A ->
    (exists z0 : Class, MinElement z0 A le /\ y = z0) -> [A,y] ∈ c).
  { intros A y E HAF HyA Hex. unfold c, En_CF. apply AxiomII; split; [exact E |].
    exists A; exists y; split; [reflexivity |
      split; [exact HAF | split; [exact HyA | exact Hex]]]. }
  assert (Hc_out : ∀ A y, [A,y] ∈ c ->
    A ∈ F /\ y ∈ A /\ (exists z0 : Class, MinElement z0 A le /\ y = z0)).
  { intros A y H. unfold c, En_CF in H. apply AxiomII in H as [E H].
    destruct H as [A' [y' [Hpair Hpred]]].
    assert (EA : Ensemble A) by (exact (proj1 (MKT49b A y E))).
    assert (Ey : Ensemble y) by (exact (proj2 (MKT49b A y E))).
    destruct (proj1 (MKT55 A y A' y' EA Ey) Hpair) as [HAA' Hyy'].
    subst A'. subst y'. exact Hpred. }
  assert (Hcfunc : Function c).
  { split.
    - intros z Hz. unfold c, En_CF in Hz. apply AxiomII in Hz as [E Hz].
      destruct Hz as [A [y [Hzy _]]]. exists A; exists y; exact Hzy.
    - intros A y1 y2 H1 H2.
      destruct (Hc_out A y1 H1) as [HAF [Hy1A [z1 [Hm1 Heq1]]]].
      destruct (Hc_out A y2 H2) as [_ [_ [z2 [Hm2 Heq2]]]].
      rewrite Heq1. rewrite Heq2.
      exact (Hminuniq A z1 z2 HAF Hm1 Hm2). }
  assert (Hdom : dom(c) = F).
  { apply AxiomI; intros A; split.
    - intros HA. apply AxiomII in HA as [_ [y Hy]]. exact (proj1 (Hc_out A y Hy)).
    - intros HAF.
      assert (EA : Ensemble A) by (exact (proj1 (proj1 (HFchar A) HAF))).
      destruct (Hminex A HAF) as [z Hm].
      assert (HzA : z ∈ A) by (exact (proj1 (Hm (HFne A HAF)))).
      assert (Ez : Ensemble z) by (unfold Ensemble; exists A; exact HzA).
      apply AxiomII; split; [exact EA |].
      exists z. apply (Hc_in A z (MKT49a (x:=A) (y:=z) EA Ez) HAF HzA).
      exists z. split; [exact Hm | reflexivity]. }
  assert (Hran : ran(c) ⊂ X).
  { intros y Hy. apply AxiomII in Hy as [_ [A HA]].
    destruct (Hc_out A y HA) as [HAF [HyA _]].
    destruct (proj1 (HFchar A) HAF) as [_ [HAX _]].
    exact (HAX y HyA). }
  assert (Hchoice : ∀ A, A ∈ dom(c) -> c[A] ∈ A).
  { intros A HA. apply AxiomII in HA as [_ [y Hy]].
    destruct (Hc_out A y Hy) as [_ [HyA _]].
    assert (Hfa : c[A] = y) by (apply (MKT_fval c A y Hcfunc); exact Hy).
    rewrite Hfa. exact HyA. }
  exists c. unfold Choice_Function.
  split; [exact Hcfunc | split; [exact Hran | split; [exact Hdom | exact Hchoice]]].
Qed.
