(* ============================================================
   ρ^{−3/2} 紧界改进 ③：见证 (2,2C) 精确值 + 紧性封顶（z 工作区，E039）
   数学（交互文档 §19 侦察）：
     精确内积公式 |⟨ψ_a,ψ_b⟩| = sin(πa/b)/(√(ab)·sin(π(b−a)/(ab)))
     固定比率 ρ=b/a 的上确界在 a=2：|⟨ψ_2,ψ_{2C}⟩| = sin(π/(2C))/√C。
   本文件机器检查：
     W1 witness_sum_norm：|Σ_{k<2} e^{ikθw}| = 2·sin(π/(2C))，
        θw = π−π/C——经 |1−ω²| = |1−ω|·|Σ|（PB1）+ 引擎引理两次，
        全程零新复分析引理。
     W2 witness_exact：Fpair 2 (2C) = sin(π/(2C))/√C（精确值，等式）。
     W3 witness_lower：≥ 1/(C√C) = C^{−3/2}（Jordan 下界 sin ≥ 2x/π）。
     W4 witness_tight：((C−1)/C)·[PB4 上界] ≤ 见证值——
        上下界之比 ≥ 1−1/C（sin(π/C) = 2sin(π/(2C))cos(π/(2C))，cos ≤ 1），
        C→∞ 时比 →1：常数演进线 4K → 2K → Θ(C^{−3/2}) 的紧性封顶。
     W5 witness_sandwich：(1−1/C)·upper ≤ Fpair 2 (2C) ≤ upper。
   审计：Print Assumptions 尾部。
   ============================================================ *)
Require Import Stdlib.Reals.Reals.
Require Import Stdlib.Arith.Arith.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.micromega.Lra.
Require Import Stdlib.ZArith.ZArith.
Require Import ca_base.
Require Import ca_complex_foundation.
Require Import ca_basis.
Require Import ca_independence.
Require Import ca_fourier.
Require Import ca_char_ortho.
Require Import ca_zeta_scaffold.
Require Import probe_grid_ortho.
Require Import probe_partial.
Require Import probe_pairbound.
Require Import probe_rowsum.
Import ComplexNumbers.
Import FourierAnalysis.
Import GridOrtho.
Import TPartial.
Import PairBound.
Import RowSum.

Open Scope R_scope.
Open Scope complex_scope.
Open Scope nat_scope.

Module Witness.

(* ---------- W0：三角与分母基础件 ---------- *)

Lemma sin_half_minus (x : R) : (sin (PI / 2 - x))%R = cos x.
Proof.
  replace (PI / 2)%R with PI2 by (unfold PI; field).
  assert (Hs2 : (sin PI2 = 1)%R).
  { replace PI2 with (PI / 2)%R by (unfold PI; field). exact sin_PI2. }
  replace (PI2 - x)%R with (PI2 + (- x))%R by ring.
  rewrite sin_plus, Hs2, cos_pi2, sin_neg, cos_neg. ring.
Qed.

Lemma sin_double' (x : R) : (sin (2 * x) = 2 * sin x * cos x)%R.
Proof.
  replace (2 * x)%R with (x + x)%R by ring.
  rewrite sin_plus. ring.
Qed.

Lemma cos_le_1' (x : R) : (0 <= x)%R -> (x <= PI)%R -> (cos x <= 1)%R.
Proof.
  intros H1 H2.
  assert (HPI : (0 < PI)%R) by apply PI_RGT_0.
  apply (Rle_trans _ (cos 0)).
  - apply cos_decr_1;
      [ apply Rle_refl | apply Rlt_le; exact HPI | exact H1 | exact H2 | exact H1 ].
  - rewrite cos_0. apply Rle_refl.
Qed.

Lemma sin_le_double (x : R) :
  (0 <= x)%R -> (x <= PI / 2)%R -> (sin (2 * x) <= 2 * sin x)%R.
Proof.
  intros H1 H2.
  assert (HPI : (0 < PI)%R) by apply PI_RGT_0.
  assert (Hle : (x <= PI)%R) by nra.
  assert (Hc : (cos x <= 1)%R) by (apply cos_le_1'; assumption).
  assert (Hs : (0 <= sin x)%R) by (apply sin_ge_0; assumption).
  replace (2 * x)%R with (x + x)%R by ring.
  rewrite sin_plus.
  nra.
Qed.

Lemma denom_2C (C : nat) : (1 <= C)%nat ->
  (sqrt (INR 2 * INR (2 * C)) = 2 * sqrt (INR C))%R.
Proof.
  intros HC.
  rewrite <- (mult_INR 2 (2 * C)).
  replace (2 * (2 * C))%nat with (4 * C)%nat by lia.
  rewrite (mult_INR 4 C).
  rewrite (sqrt_mult (INR 4) (INR C))
    by (repeat split; left; apply lt_0_INR; lia).
  rewrite sqrt_INR_4. reflexivity.
Qed.

(* ---------- W1：见证和的精确范数 ---------- *)

Lemma witness_sum_norm (C : nat) : (2 <= C)%nat ->
  (Cnorm (PrimeEmbedding.Csum
            (fun k => rot_atom ((2 * PI * (INR (2 * C) - INR 2)
                                 / (INR 2 * INR (2 * C)))%R) k) 2)
   = 2 * sin (PI / (2 * INR C)))%R.
Proof.
  intros HC.
  assert (HIC : (0 < INR C)%R) by (apply lt_0_INR; lia).
  assert (H2IC : (2 <= INR C)%R) by (rewrite <- INR_two; apply le_INR; lia).
  assert (HPI : (0 < PI)%R) by apply PI_RGT_0.
  set (theta := (2 * PI * (INR (2 * C) - INR 2) / (INR 2 * INR (2 * C)))%R) in *.
  assert (Hin : (INR (2 * C) = 2 * INR C)%R)
    by (rewrite (mult_INR 2 C), INR_two; reflexivity).
  assert (Hth : (theta = PI - PI / INR C)%R).
  { unfold theta. rewrite Hin, INR_two. field; lra. }
  assert (Hth2 : (theta / 2 = PI / 2 - PI / (2 * INR C))%R).
  { unfold theta. rewrite Hin, INR_two. field; lra. }
  pose proof (geom_sum_norm_prod theta 2) as P.
  (* 分子：|1 − ω²| = 2·sin(PI/INR C) *)
  assert (N2 : (Cnorm (C1 -c rot_atom theta 2)
                = 2 * Rabs (sin (INR 2 * theta / 2)))%R).
  { rewrite <- (Cnorm_one_minus_exp_i_theta_eq (INR 2 * theta)).
    reflexivity. }
  assert (Hc2 : (INR 2 * theta / 2 = PI - PI / INR C)%R).
  { rewrite INR_two. replace (2 * theta / 2)%R with theta by (field; lra).
    exact Hth. }
  rewrite Hc2, sin_PI_minus' in N2.
  assert (Hspos : (0 <= sin (PI / INR C))%R).
  { apply sin_ge_0.
    - unfold Rdiv. apply Rmult_le_pos.
      + apply Rlt_le; exact HPI.
      + apply Rlt_le, Rinv_0_lt_compat, HIC.
    - apply (Rmult_le_reg_r (INR C) (PI / INR C) PI HIC).
      replace (PI / INR C * INR C)%R with PI by (field; lra).
      nra. }
  rewrite (Rabs_right _ (Rle_ge _ _ Hspos)) in N2.
  (* 分母：|1 − ω| = 2·cos(PI/(2·INR C)) *)
  assert (N1 : (Cnorm (C1 -c rot_atom theta 1)
                = 2 * Rabs (sin (theta / 2)))%R).
  { rewrite <- (Cnorm_one_minus_exp_i_theta_eq theta).
    change (rot_atom theta 1) with (Cexp (0 +i (INR 1 * theta))).
    rewrite INR_1. repeat f_equal. ring. }
  rewrite Hth2, sin_half_minus in N1.
  assert (Hcpos : (0 < cos (PI / (2 * INR C)))%R).
  { rewrite <- (sin_half_minus (PI / (2 * INR C))).
    assert (Hden : (0 < 2 * INR C)%R)
      by (apply Rmult_lt_0_compat; [ lra | exact HIC ]).
    apply sin_gt_0.
    - apply (Rmult_lt_reg_r (2 * INR C)); [ exact Hden | ].
      rewrite Rmult_0_l.
      replace ((PI / 2 - PI / (2 * INR C)) * (2 * INR C))%R
        with (PI * (INR C - 1))%R by (field; lra).
      apply Rmult_lt_0_compat; [ exact HPI | lra ].
    - apply (Rmult_lt_reg_r (2 * INR C)); [ exact Hden | ].
      replace ((PI / 2 - PI / (2 * INR C)) * (2 * INR C))%R
        with (PI * (INR C - 1))%R by (field; lra).
      nra. }
  rewrite (Rabs_right _ (Rle_ge _ _ (Rlt_le _ _ Hcpos))) in N1.
  (* 合成：2·sin(PI/C) = 2·cos·N ⟹ N = 2·sin(PI/(2C)) *)
  rewrite N2, N1 in P.
  assert (Hd : (sin (PI / INR C)
                = 2 * sin (PI / (2 * INR C)) * cos (PI / (2 * INR C)))%R).
  { replace (PI / INR C)%R with (2 * (PI / (2 * INR C)))%R by (field; lra).
    apply sin_double'. }
  apply (Rmult_eq_reg_r (2 * cos (PI / (2 * INR C)))).
  - lra.
  - intro H0.
    destruct (Rmult_integral _ _ H0) as [E | E]; lra.
Qed.

(* ---------- W2：精确值（主定理一） ---------- *)

Theorem witness_exact (C : nat) : (2 <= C)%nat ->
  (Fpair 2 (2 * C) = sin (PI / (2 * INR C)) / sqrt (INR C))%R.
Proof.
  intros HC.
  assert (HIC : (0 < INR C)%R) by (apply lt_0_INR; lia).
  assert (Hs : (0 < sqrt (INR C))%R) by (apply sqrt_posnat; lia).
  unfold Fpair.
  rewrite (witness_sum_norm C HC).
  rewrite (denom_2C C ltac:(lia)).
  field. lra.
Qed.

(* ---------- W3：C^{−3/2} 下界（Jordan sin ≥ 2x/π） ---------- *)

Lemma witness_lower (C : nat) : (2 <= C)%nat ->
  ((1 / (INR C * sqrt (INR C)) <= Fpair 2 (2 * C)))%R.
Proof.
  intros HC.
  assert (HIC : (0 < INR C)%R) by (apply lt_0_INR; lia).
  assert (Hs : (0 < sqrt (INR C))%R) by (apply sqrt_posnat; lia).
  assert (Hin : (INR (2 * C) = 2 * INR C)%R)
    by (rewrite (mult_INR 2 C), INR_two; reflexivity).
  rewrite (witness_exact C HC).
  apply (Rmult_le_reg_r (sqrt (INR C)) _ _ Hs).
  replace (sin (PI / (2 * INR C)) / sqrt (INR C) * sqrt (INR C))%R
    with (sin (PI / (2 * INR C)))%R by (field; nra).
  replace (1 / (INR C * sqrt (INR C)) * sqrt (INR C))%R
    with (/ INR C)%R by (field; nra).
  pose proof (sin_lower (2 * C) 1 ltac:(lia) ltac:(lia)) as HL.
  rewrite INR_1, Hin in HL.
  replace (2 * 1 / (2 * INR C))%R with (/ INR C)%R in HL by (field; lra).
  replace (PI * 1 / (2 * INR C))%R with (PI / (2 * INR C))%R in HL by (field; lra).
  exact HL.
Qed.

(* ---------- W4：紧性封顶（主定理二） ---------- *)

Theorem witness_tight (C : nat) : (2 <= C)%nat ->
  (((INR C - 1) / INR C)
     * (sin (PI * INR 2 / INR (2 * C)) * sqrt (INR 2 * INR (2 * C))
        / (2 * (INR (2 * C) - INR 2)))
    <= Fpair 2 (2 * C))%R.
Proof.
  intros HC.
  assert (HIC : (0 < INR C)%R) by (apply lt_0_INR; lia).
  assert (H2IC : (2 <= INR C)%R)
    by (rewrite <- INR_two; apply le_INR; lia).
  assert (HIC1 : (1 < INR C)%R) by lra.
  assert (Hs : (0 < sqrt (INR C))%R) by (apply sqrt_posnat; lia).
  assert (HPI : (0 < PI)%R) by apply PI_RGT_0.
  assert (Hin : (INR (2 * C) = 2 * INR C)%R)
    by (rewrite (mult_INR 2 C), INR_two; reflexivity).
  assert (Ha : (PI * INR 2 / INR (2 * C) = PI / INR C)%R)
    by (rewrite Hin, INR_two; field; lra).
  (* 关键不等式：sin(PI/C) ≤ 2·sin(PI/(2C)) *)
  assert (Hkey : (sin (PI / INR C) <= 2 * sin (PI / (2 * INR C)))%R).
  { replace (PI / INR C)%R with (2 * (PI / (2 * INR C)))%R by (field; lra).
    apply sin_le_double.
    - unfold Rdiv. apply Rmult_le_pos.
      + apply Rlt_le; exact HPI.
      + apply Rlt_le, Rinv_0_lt_compat; lra.
    - apply (Rmult_le_reg_r (2 * INR C)); [ lra | ].
      replace (PI / (2 * INR C) * (2 * INR C))%R with PI by (field; lra).
      replace (PI / 2 * (2 * INR C))%R with (PI * INR C)%R by (field; lra).
      nra. }
  rewrite (witness_exact C HC), Ha.
  apply (Rmult_le_reg_r (sqrt (INR C)) _ _ Hs).
  replace (sin (PI / (2 * INR C)) / sqrt (INR C) * sqrt (INR C))%R
    with (sin (PI / (2 * INR C)))%R by (field; nra).
  assert (Hss : (sqrt (INR C) * sqrt (INR C) = INR C)%R)
    by (apply sqrt_sqrt; lra).
  assert (Hbig : (((INR C - 1) / INR C)
                   * (sin (PI / INR C) * sqrt (INR 2 * INR (2 * C))
                      / (2 * (INR (2 * C) - INR 2)))
                   * sqrt (INR C)
                   = sin (PI / INR C) / 2)%R).
  { transitivity (sin (PI / INR C) * (sqrt (INR C) * sqrt (INR C))
                  / (2 * INR C))%R.
    - rewrite (denom_2C C ltac:(lia)), Hin, INR_two. field; lra.
    - rewrite Hss. field; lra. }
  rewrite Hbig.
  nra.
Qed.

(* ---------- W5：三明治（比值 ≥ 1 − 1/C 的合成形） ---------- *)

Corollary witness_sandwich (C : nat) : (2 <= C)%nat ->
  ((((INR C - 1) / INR C)
      * (sin (PI * INR 2 / INR (2 * C)) * sqrt (INR 2 * INR (2 * C))
         / (2 * (INR (2 * C) - INR 2)))
    <= Fpair 2 (2 * C))
   /\ (Fpair 2 (2 * C)
       <= sin (PI * INR 2 / INR (2 * C)) * sqrt (INR 2 * INR (2 * C))
          / (2 * (INR (2 * C) - INR 2))))%R.
Proof.
  intros HC. split.
  - apply (witness_tight C HC).
  - pose proof (pair_inner_norm 2 (2 * C) ltac:(lia) ltac:(lia)) as Hup.
    exact Hup.
Qed.

End Witness.

Print Assumptions Witness.witness_sum_norm.
Print Assumptions Witness.witness_exact.
Print Assumptions Witness.witness_lower.
Print Assumptions Witness.witness_tight.
Print Assumptions Witness.witness_sandwich.
