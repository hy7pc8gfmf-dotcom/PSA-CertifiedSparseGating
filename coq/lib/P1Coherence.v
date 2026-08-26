(* ============================================================
   P1Coherence —— 精确窗口相干下界
   精确窗口口径：coh_T(n,n') = |sin(πd/n')| / (√(nn')·|sin(πd/(nn'))|)，d = n'-n
   P1： d ≤ n'/2、1 ≤ n、n < n' ⟹ coh_T ≥ (2/π)·√(n/n')
        （Jordan 下界 + |sin x| ≤ x 上界；与 P2/P3 保守界口径分层）
   P1'：d ≤ n'/2、1 ≤ n、n < n' ⟹ coh_T ≥ √(n/n')·(1 − π²d²/(6n'²))
        （sin x ≥ x − x³/6）
   意义：近邻大带（如 (216,217)）相干 ≈ 0.997——稠密随机阶梯
   高相干的解析根源。
   纪律：零 Admitted、零自定义公理；仅 Stdlib Reals（自包含）。
   依赖：Stdlib Reals 的 sin_bound（交替级数）、MVT_cor2、cos_decr_1。
   ============================================================ *)
From Stdlib Require Import Reals.
From Stdlib Require Import micromega.Lra.
Open Scope R_scope.

(* ---------- sin 分析引理（纯 Stdlib，不依赖 ca_basis_lemmas） ---------- *)

(* Jordan 不等式：0 ≤ x ≤ π/2 ⟹ (2/π)·x ≤ sin x
   （MVT_cor2 × 2 + cos 在 [0,π] 递减；x=0/π/2 端点单独处理） *)
Lemma jordan_sin_ge (x : R) : 0 <= x -> x <= PI / 2 -> (2 / PI) * x <= sin x.
Proof.
  intros Hx0 Hx2.
  assert (Hpi : 0 < PI) by exact PI_RGT_0.
  destruct (Req_dec x 0) as [Hx0eq | Hx0ne].
  - subst. rewrite sin_0. lra.
  - destruct (Req_dec x (PI / 2)) as [Hx2eq | Hx2ne].
    + subst. rewrite sin_PI2.
      replace (2 / PI * (PI / 2)) with 1 by (field; lra).
      lra.
    + assert (Hx0lt : 0 < x) by lra.
      assert (Hx2lt : x < PI / 2) by lra.
      pose proof (MVT_cor2 sin cos x (PI / 2) Hx2lt (fun c Hc => derivable_pt_lim_sin c)) as [c [HcM Hcin]].
      pose proof (MVT_cor2 sin cos 0 x Hx0lt (fun c Hc => derivable_pt_lim_sin c)) as [d [HdM Hdin]].
      rewrite sin_PI2 in HcM.
      rewrite sin_0 in HdM.
      replace (sin x - 0) with (sin x) in HdM by ring.
      replace (x - 0) with x in HdM by ring.
      assert (Hcos_le : cos c <= cos d).
      { apply cos_decr_1; lra. }
      assert (Hcosc_eq : cos c = (1 - sin x) / (PI / 2 - x)).
      { rewrite HcM. field. lra. }
      assert (Hcosd_eq : cos d = sin x / x).
      { rewrite HdM. field. lra. }
      assert (Hratio : (1 - sin x) / (PI / 2 - x) <= sin x / x).
      { rewrite <- Hcosc_eq, <- Hcosd_eq. exact Hcos_le. }
      assert (Hden : 0 <= (PI / 2 - x) * x) by nra.
      assert (Hmul : ((1 - sin x) / (PI / 2 - x)) * ((PI / 2 - x) * x) <= (sin x / x) * ((PI / 2 - x) * x)).
      { apply Rmult_le_compat_r; [exact Hden | exact Hratio]. }
      assert (Hcross : (1 - sin x) * x <= sin x * (PI / 2 - x)).
      {
        replace ((1 - sin x) / (PI / 2 - x) * ((PI / 2 - x) * x)) with ((1 - sin x) * x) in Hmul by (field; lra).
        replace (sin x / x * ((PI / 2 - x) * x)) with (sin x * (PI / 2 - x)) in Hmul by (field; lra).
        exact Hmul.
      }
      assert (Hxsin : x <= (PI / 2) * sin x).
      { nra. }
      assert (H2pi_pos : 0 <= 2 / PI).
      { apply Rmult_le_pos; [lra | apply Rlt_le, Rinv_0_lt_compat; lra]. }
      assert (Hmul2 : (2 / PI) * x <= (2 / PI) * ((PI / 2) * sin x)).
      { apply Rmult_le_compat_l; [exact H2pi_pos | exact Hxsin]. }
      replace ((2 / PI) * ((PI / 2) * sin x)) with (sin x) in Hmul2 by (field; lra).
      exact Hmul2.
Qed.

(* |sin x| ≤ x 对 0 ≤ x ≤ π/2（P1 分母上界；sin ≥ 0 于 [0,π] ⟹ Rabs = sin） *)
Lemma sin_abs_le_x_half (x : R) : 0 <= x -> x <= PI / 2 -> Rabs (sin x) <= x.
Proof.
  intros Hx0 Hx2.
  assert (Hpi : 0 < PI) by exact PI_RGT_0.
  assert (Hsin_ge : 0 <= sin x) by (apply sin_ge_0; lra).
  rewrite Rabs_pos_eq; [| exact Hsin_ge].
  destruct (Req_dec x 0) as [Hxe | Hxne].
  - subst. rewrite sin_0. lra.
  - apply Rlt_le. apply sin_lt_x. lra.
Qed.

(* P1' 分子下界：x − x³/6 ≤ sin x 对 0 ≤ x ≤ π（sin_bound 交替级数 n=0） *)
Lemma sin_ge_x_minus_x3_6 (x : R) : 0 <= x -> x <= PI -> x - x ^ 3 / 6 <= sin x.
Proof.
  intros Hx0 Hx2.
  pose proof (sin_bound x 0 Hx0 Hx2) as [Hlo _].
  unfold sin_approx in Hlo.
  simpl in Hlo.
  replace (sin_term x 0 + sin_term x 1) with (x - x ^ 3 / 6) in Hlo by (unfold sin_term; simpl; field).
  exact Hlo.
Qed.

(* ---------- 分数不等式（P1 组装） ---------- *)
(* a ≤ A、C ≤ c、全正 ⟹ a/(b·c) ≤ A/(b·C) *)
Lemma frac_le (a A C c b : R) :
  0 < a -> a <= A -> 0 < C -> C <= c -> 0 < c -> 0 < b ->
  a / (b * c) <= A / (b * C).
Proof.
  intros Ha HaA HC HCc Hc Hb.
  assert (HA : 0 < A) by lra.
  assert (HcC : 0 < c * C) by nra.
  apply (Rmult_le_reg_r (c * C) (a / (b * c)) (A / (b * C))).
  - exact HcC.
  - replace ((a / (b * c)) * (c * C)) with (a * C / b) by (field; lra).
    replace ((A / (b * C)) * (c * C)) with (A * c / b) by (field; lra).
    apply (Rmult_le_reg_r b (a * C / b) (A * c / b)); [exact Hb | ].
    replace ((a * C / b) * b) with (a * C) by (field; lra).
    replace ((A * c / b) * b) with (A * c) by (field; lra).
    apply (Rle_trans (a * C) (A * C) (A * c)).
    + apply Rmult_le_compat_r; [lra | exact HaA].
    + apply Rmult_le_compat_l; [lra | exact HCc].
Qed.

(* sqrt(n/n')·sqrt(nn') = n（0 < n、0 < n'） *)
Lemma sqrt_prod (n n' : R) :
  0 < n -> 0 < n' -> sqrt (n / n') * sqrt (n * n') = n.
Proof.
  intros Hn Hn'.
  assert (Hn1 : 0 <= n / n') by (apply Rlt_le; apply Rdiv_lt_0_compat; lra).
  assert (Hn2 : 0 <= n * n') by nra.
  assert (Hm : sqrt (n / n' * (n * n')) = sqrt (n / n') * sqrt (n * n')).
  { apply sqrt_mult; [exact Hn1 | exact Hn2]. }
  assert (Hnn : (n / n') * (n * n') = n * n) by (field; lra).
  rewrite <- Hm.
  rewrite Hnn.
  apply sqrt_square. lra.
Qed.

(* 代数化简：(2/π)·√(n/n') = (2·d/n')/(√(nn')·(πd/(nn'))) *)
Lemma p1_algebra (n n' d : R) :
  0 < n -> 0 < n' -> 0 < d ->
  (2 / PI) * sqrt (n / n') =
  (2 * d / n') / (sqrt (n * n') * (PI * d / (n * n'))).
Proof.
  intros Hn Hn' Hd.
  assert (Hpi : PI <> 0) by (apply Rgt_not_eq; exact PI_RGT_0).
  assert (Hsn : sqrt (n * n') <> 0).
  { apply Rgt_not_eq. apply sqrt_lt_R0. nra. }
  assert (Hn'0 : n' <> 0) by lra.
  assert (Hdiv : sqrt (n / n') = n / sqrt (n * n')).
  {
    apply (Rmult_eq_reg_l (sqrt (n * n')) (sqrt (n / n')) (n / sqrt (n * n'))).
    - rewrite Rmult_comm.
      rewrite (sqrt_prod n n' Hn Hn').
      field. lra.
    - exact Hsn.
  }
  rewrite Hdiv.
  field.
  repeat split; auto; lra.
Qed.

(* ---------- P1 主定理 ---------- *)
(* 相干公式：coh_T(n,n') = |sin(πd/n')| / (√(nn')·|sin(πd/(nn'))|)，d = n'-n *)
Definition coh_T (n n' : R) : R :=
  Rabs (sin (PI * (n' - n) / n')) /
  (sqrt (n * n') * Rabs (sin (PI * (n' - n) / (n * n')))).

(* 分母上界：|sin(πd/(nn'))| ≤ πd/(nn')，前提 0 < πd/(nn') ≤ π/2（1 ≤ n 保 2d ≤ nn'） *)
Lemma den_bound (n n' d : R) :
  0 < PI -> 1 <= n -> 0 < n -> 0 < n' -> 0 < d -> d <= n' / 2 ->
  Rabs (sin (PI * d / (n * n'))) <= PI * d / (n * n').
Proof.
  intros Hpi Hn1 Hn Hn' Hd Hdle.
  apply sin_abs_le_x_half.
  - (* 0 <= PI*d/(nn') *)
    apply Rlt_le.
    apply Rdiv_lt_0_compat; [| nra].
    apply Rmult_lt_0_compat; [exact Hpi | lra].
  - (* PI*d/(nn') <= PI/2：d <= n'/2 <= n·n'/2（1 ≤ n）⟹ 乘 π>0、除 (nn')>0 *)
    assert (Hdle2 : d <= n * n' / 2).
    {
      apply (Rle_trans d (n' / 2) (n * n' / 2)).
      - exact Hdle.
      - unfold Rdiv.
        apply (Rmult_le_compat_r (/ 2) n' (n * n')); [lra | ].
        nra.
    }
    assert (Hmul2 : PI * d <= PI * (n * n' / 2)).
    { apply Rmult_le_compat_l; [lra | exact Hdle2]. }
    assert (Hden2 : 0 < n * n') by nra.
    unfold Rdiv.
    apply (Rmult_le_reg_r (n * n') (PI * d * / (n * n')) (PI / 2)); [exact Hden2 | ].
    replace ((PI * d * / (n * n')) * (n * n')) with (PI * d) by (field; nra).
    replace ((PI / 2) * (n * n')) with (PI * n * n' / 2) by (field; nra).
    apply (Rle_trans (PI * d) (PI * (n * n' / 2)) (PI * n * n' / 2)); [exact Hmul2 | ].
    replace (PI * (n * n' / 2)) with (PI * n * n' / 2) by (field; lra).
    reflexivity.
Qed.

(* 分母正：|sin(πd/(nn'))| > 0，前提 0 < πd/(nn') < π（d < n' 保 d < n·n'） *)
Lemma den_pos (n n' d : R) :
  0 < PI -> 1 <= n -> 0 < n' -> 0 < d -> d < n' ->
  0 < Rabs (sin (PI * d / (n * n'))).
Proof.
  intros Hpi Hn1 Hn' Hd Hdlt.
  assert (Harg0 : 0 < PI * d / (n * n')).
  {
    apply Rdiv_lt_0_compat; [| nra].
    apply Rmult_lt_0_compat; [exact Hpi | lra].
  }
  assert (Hargpi : PI * d / (n * n') < PI).
  {
    (* d < n' ≤ n·n'（1 ≤ n）⟹ πd/(nn') < π *)
    apply Rmult_lt_reg_r with (n * n'); [nra | ].
    replace (PI * d / (n * n') * (n * n')) with (PI * d) by (field; nra).
    apply Rmult_lt_compat_l; [lra | ].
    (* d < n·n'：d < n' ≤ n·n' *)
    assert (Hdlt' : d < n') by lra.
    assert (Hnle : n' <= n * n').
    { nra. }
    lra.
  }
  assert (Hsp : 0 < sin (PI * d / (n * n'))) by (apply sin_gt_0; [lra | exact Hargpi]).
  rewrite Rabs_pos_eq; lra.
Qed.

(* P1：0 < n、1 ≤ n、n < n'、d = n'-n ≤ n'/2 ⟹ coh_T ≥ (2/π)·√(n/n') *)
Theorem p1_coherence_lower (n n' : R) :
  1 <= n -> n < n' -> n' - n <= n' / 2 ->
  (2 / PI) * sqrt (n / n') <= coh_T n n'.
Proof.
  intros Hn1 Hnn' Hd.
  assert (Hpi : 0 < PI) by exact PI_RGT_0.
  assert (Hn : 0 < n) by lra.
  assert (Hn' : 0 < n') by lra.
  set (d := n' - n).
  assert (Hdpos : 0 < d) by (unfold d; lra).
  (* 分子下界：2d/n' ≤ |sin(πd/n')| *)
  assert (Hnum : 2 * d / n' <= Rabs (sin (PI * d / n'))).
  {
    assert (Hx0 : 0 < PI * d / n').
    {
      apply Rdiv_lt_0_compat; [| exact Hn'].
      apply Rmult_lt_0_compat; [exact Hpi | unfold d; lra].
    }
    assert (Hxpi : PI * d / n' <= PI / 2).
    {
      assert (Hmul2 : PI * d <= PI * (n' / 2)).
      { apply Rmult_le_compat_l; [lra | unfold d; lra]. }
      apply (Rmult_le_reg_r n' (PI * d / n') (PI / 2)); [exact Hn' | ].
      replace ((PI * d / n') * n') with (PI * d) by (field; nra).
      replace ((PI / 2) * n') with (PI * (n' / 2)) by (field; nra).
      exact Hmul2.
    }
    pose proof (jordan_sin_ge (PI * d / n') (Rlt_le _ _ Hx0) Hxpi) as Hj.
    assert (Hsin_ge : 0 <= sin (PI * d / n')).
    {
      apply sin_ge_0.
      - exact (Rlt_le _ _ Hx0).
      - apply (Rle_trans (PI * d / n') (PI / 2) PI); [exact Hxpi | lra].
    }
    rewrite Rabs_pos_eq; [| exact Hsin_ge].
    replace ((2 / PI) * (PI * d / n')) with (2 * d / n') in Hj by (field; nra).
    exact Hj.
  }
  (* 分母上界 + 分母正（顶层引理） *)
  assert (Hden : Rabs (sin (PI * d / (n * n'))) <= PI * d / (n * n')).
  { apply den_bound; unfold d; lra. }
  assert (Hcpos : 0 < Rabs (sin (PI * d / (n * n')))).
  { apply den_pos; unfold d; lra. }  (* 组装：frac_le a:=2d/n' A:=|sin(πd/n')| C:=|sin(πd/(nn'))| c:=πd/(nn') b:=√(nn') *)
  assert (Hfl : (2 * d / n') / (sqrt (n * n') * (PI * d / (n * n')))
           <= Rabs (sin (PI * d / n')) / (sqrt (n * n') * Rabs (sin (PI * d / (n * n'))))).
  {
    apply frac_le.
    - apply Rdiv_lt_0_compat; [nra | exact Hn'].
    - exact Hnum.
    - exact Hcpos.
    - exact Hden.
    - apply Rdiv_lt_0_compat; [nra | nra].
    - apply sqrt_lt_R0; nra.
  }
  (* 代数：左边 = (2/π)·√(n/n') *)
  rewrite (p1_algebra n n' d Hn Hn' Hdpos).
  exact Hfl.
Qed.

(* ---------- P1' 精细版 ---------- *)
(* 分子下界：(πd/n')·(1 − π²d²/(6n'²)) ≤ |sin(πd/n')| *)
Lemma p1prime_num (n n' d : R) :
  0 < PI -> 0 < n -> 0 < n' -> 0 < d -> d <= n' / 2 ->
  (PI * d / n') * (1 - PI ^ 2 * d ^ 2 / (6 * n' ^ 2)) <=
  Rabs (sin (PI * d / n')).
Proof.
  intros Hpi Hn Hn' Hdpos Hdle.
  assert (Hx0 : 0 <= PI * d / n').
  { apply Rlt_le. apply Rdiv_lt_0_compat; [| exact Hn']. apply Rmult_lt_0_compat; [exact Hpi | lra]. }
  (* PI*d/n' <= PI/2（d <= n'/2）⟹ <= PI *)
  assert (Hxpi2 : PI * d / n' <= PI / 2).
  {
    assert (Hmul2 : PI * d <= PI * (n' / 2)).
    { apply Rmult_le_compat_l; [lra | exact Hdle]. }
    apply (Rmult_le_reg_r n' (PI * d / n') (PI / 2)); [exact Hn' | ].
    replace ((PI * d / n') * n') with (PI * d) by (field; nra).
    replace ((PI / 2) * n') with (PI * (n' / 2)) by (field; nra).
    exact Hmul2.
  }
  assert (Hxpi : PI * d / n' <= PI) by (apply (Rle_trans (PI * d / n') (PI / 2) PI); [exact Hxpi2 | lra]).
  pose proof (sin_ge_x_minus_x3_6 (PI * d / n') Hx0 Hxpi) as Hs.
  assert (Hsin_ge : 0 <= sin (PI * d / n')).
  {
    apply sin_ge_0.
    - exact Hx0.
    - exact Hxpi.
  }
  rewrite Rabs_pos_eq; [| exact Hsin_ge].
  replace (PI * d / n' - (PI * d / n') ^ 3 / 6)
    with ((PI * d / n') * (1 - PI ^ 2 * d ^ 2 / (6 * n' ^ 2))) in Hs by (field; nra).
  exact Hs.
Qed.

(* P1'：d ≤ n'/2 ⟹ coh_T ≥ √(n/n')·(1 − π²d²/(6n'²)) *)
Theorem p1_prime_coherence_lower (n n' : R) :
  1 <= n -> n < n' -> n' - n <= n' / 2 ->
  sqrt (n / n') * (1 - PI ^ 2 * (n' - n) ^ 2 / (6 * n' ^ 2)) <= coh_T n n'.
Proof.
  intros Hn1 Hnn' Hd.
  assert (Hpi : 0 < PI) by exact PI_RGT_0.
  assert (Hn : 0 < n) by lra.
  assert (Hn' : 0 < n') by lra.
  set (d := n' - n).
  assert (Hdpos : 0 < d) by (unfold d; lra).
  (* 分母上界 + 分母正 *)
  assert (Hden : Rabs (sin (PI * d / (n * n'))) <= PI * d / (n * n')).
  { apply den_bound; unfold d; lra. }
  assert (Hcpos : 0 < Rabs (sin (PI * d / (n * n')))).
  { apply den_pos; unfold d; lra. }  (* 分子下界（P1' 版） *)
  assert (Hnum : (PI * d / n') * (1 - PI ^ 2 * d ^ 2 / (6 * n' ^ 2)) <= Rabs (sin (PI * d / n'))).
  {
    apply (p1prime_num n n' d Hpi Hn Hn' Hdpos).
    unfold d. lra.
  }
  (* 组装 *)
  assert (Hfl : ((PI * d / n') * (1 - PI ^ 2 * d ^ 2 / (6 * n' ^ 2))) /
                  (sqrt (n * n') * (PI * d / (n * n')))
           <= Rabs (sin (PI * d / n')) / (sqrt (n * n') * Rabs (sin (PI * d / (n * n'))))).
  {
    apply frac_le.
    - (* a > 0：需 1 − π²d²/(6n'²) > 0，用 π ≤ 4 与 d ≤ n'/2 *)
      assert (Hpi4 : PI <= 4) by exact PI_4.
      assert (Hmain : 0 < (PI * d / n') * (1 - PI ^ 2 * d ^ 2 / (6 * n' ^ 2))).
      {
        apply Rmult_lt_0_compat.
        - apply Rdiv_lt_0_compat; [nra | exact Hn'].
        - (* 1 - π²d²/(6n'²) > 0 ⟺ π²d² < 6n'²；π≤4、d≤n'/2 ⟹ π²d² ≤ 4n'² < 6n'² *)
          assert (Hd2 : PI ^ 2 * d ^ 2 <= 4 * n' ^ 2).
          {
            assert (Hpi2 : PI ^ 2 <= 16).
            {
              replace (PI ^ 2) with (PI * PI) by (unfold pow; ring).
              replace 16 with (4 * 4) by ring.
              apply Rmult_le_compat; [lra | lra | exact Hpi4 | exact Hpi4].
            }
            assert (Hd' : d ^ 2 <= (n' / 2) ^ 2).
            {
              replace (d ^ 2) with (d * d) by (unfold pow; ring).
              replace ((n' / 2) ^ 2) with ((n' / 2) * (n' / 2)) by (unfold pow; ring).
              apply Rmult_le_compat; [lra | lra | | ].
              - unfold d. lra.
              - unfold d. lra.
            }
            assert (Hpd : PI ^ 2 * d ^ 2 <= 16 * (n' / 2) ^ 2).
            { apply Rmult_le_compat; [apply pow_le; lra | apply pow_le; lra | exact Hpi2 | exact Hd']. }
            replace (16 * (n' / 2) ^ 2) with (4 * n' ^ 2) in Hpd by (field; nra).
            exact Hpd.
          }
          assert (Hlt : 4 * n' ^ 2 < 6 * n' ^ 2) by nra.
          (* π²d²/(6n'²) < 1 ⟸ π²d² < 6n'²（分母正） *)
          assert (Hnumlt : PI ^ 2 * d ^ 2 / (6 * n' ^ 2) < 1).
          {
            apply (Rmult_lt_reg_r (6 * n' ^ 2) (PI ^ 2 * d ^ 2 / (6 * n' ^ 2)) 1); [nra | ].
            replace (PI ^ 2 * d ^ 2 / (6 * n' ^ 2) * (6 * n' ^ 2)) with (PI ^ 2 * d ^ 2) by (field; nra).
            replace (1 * (6 * n' ^ 2)) with (6 * n' ^ 2) by ring.
            apply (Rle_lt_trans (PI ^ 2 * d ^ 2) (4 * n' ^ 2) (6 * n' ^ 2));
              [exact Hd2 | exact Hlt].
          }
          lra.
      }
      exact Hmain.
    - exact Hnum.
    - exact Hcpos.
    - exact Hden.
    - unfold d; nra.
    - apply sqrt_lt_R0; nra.
  }
  (* 代数：左边化简 = √(n/n')·(1 − π²d²/(6n'²)) *)
  assert (Halg : ((PI * d / n') * (1 - PI ^ 2 * d ^ 2 / (6 * n' ^ 2))) /
                   (sqrt (n * n') * (PI * d / (n * n'))) =
                 sqrt (n / n') * (1 - PI ^ 2 * d ^ 2 / (6 * n' ^ 2))).
  {
    assert (Hpi' : PI <> 0) by (apply Rgt_not_eq; exact PI_RGT_0).
    assert (Hsn : sqrt (n * n') <> 0).
    { apply Rgt_not_eq. apply sqrt_lt_R0. nra. }
    assert (Hn'0 : n' <> 0) by lra.
    assert (Hd0 : d <> 0) by lra.
    assert (Hnn'0 : n * n' <> 0) by nra.
    assert (Hdiv : sqrt (n / n') = n / sqrt (n * n')).
    {
      apply (Rmult_eq_reg_l (sqrt (n * n')) (sqrt (n / n')) (n / sqrt (n * n'))).
      - rewrite Rmult_comm.
        rewrite (sqrt_prod n n' Hn Hn').
        field. lra.
      - exact Hsn.
    }
    rewrite Hdiv.
    field.
    repeat split; auto; lra.
  }
  rewrite Halg in Hfl.
  unfold d in Hfl.
  exact Hfl.
Qed.
