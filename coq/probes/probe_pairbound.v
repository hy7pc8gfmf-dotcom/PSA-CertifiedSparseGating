(* ============================================================
   ρ^{−3/2} 紧界改进 ①：逐对内积界引擎（z 工作区，E039）
   数学（交互文档 §19 侦察，数值验证 6 位吻合）：
     |⟨ψ_a,ψ_b⟩| = sin(πa/b)/(√(ab)·sin(π(b−a)/(ab)))
   ——固定比率 ρ=b/a 时真实值 Θ(ρ^{−3/2})，上确界在 a=2。
   本文件证 Jordan 版上界：|⟨ψ_a,ψ_b⟩| ≤ sin(πa/b)·√(ab)/(2(b−a))，
   与见证 (2,2C) 之比随 C→∞ → 1（数值 1.23@C=4 → 1.01@C=100）。

   PB0 Cnorm_ge0 / sqrt_pos_strict：非负性基础件。
   PB1 geom_sum_norm_prod：|1−ω^W| = |1−ω|·|Σ rot^k|（复用 probe_partial
       的 geom_sum_identity + Cnorm_mult'）。
   PB2 sin_PI_minus'：sin(π−x) = sin x（sin_add + sin_PI + cos_PI + sin_neg）。
   PB3 pair_S_bound（引擎主定理）：|Σ_{k<a} e^{i·k·θ}| ≤
       sin(πa/b)·(ab)/(2(b−a))，θ = 2π(b−a)/(ab)——
       分子 |1−ω^a| = 2sin(πa/b)（PB2 周期化 + sin_ge_0），
       分母 |1−ω| ≥ 4(b−a)/(ab)（sin_lower Jordan 半带）。
   PB4 pair_inner_norm（归一化系）：|⟨ψ_a,ψ_b⟩| ≤ sin(πa/b)·√(ab)/(2(b−a))
       ——纯 R 层除法。
   审计：Print Assumptions 尾部。
   ============================================================ *)
From mathcomp Require Import ssreflect ssrbool ssrnat seq eqtype div prime.
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
Import ComplexNumbers.
Import FourierAnalysis.
Import GridOrtho.
Import TPartial.

Open Scope R_scope.
Open Scope complex_scope.
Open Scope nat_scope.

Module PairBound.

(* ---------- PB0：非负性基础件 ---------- *)

Lemma sqrt_pos_strict (x : R) : (0 < x)%R -> (0 < sqrt x)%R.
Proof.
  intros Hx.
  assert (Hp : (0 <= sqrt x)%R) by (apply sqrt_pos'; apply Rlt_le; exact Hx).
  destruct (Rle_lt_dec (sqrt x) 0) as [Hle | Hgt]; [ | exact Hgt ].
  exfalso.
  assert (Hs : (sqrt x * sqrt x = x)%R) by (apply sqrt_sqrt; apply Rlt_le; exact Hx).
  assert (Hz : (sqrt x = 0)%R) by lra.
  rewrite Hz Rmult_0_l in Hs. lra.
Qed.

Lemma Cnorm_ge0 (z : Complex) : (0 <= Cnorm z)%R.
Proof. unfold Cnorm. apply sqrt_pos'. apply Cnorm_sq_ge_0. Qed.

(* ---------- PB1：几何和的范数乘法形式 ---------- *)

Lemma geom_sum_norm_prod (theta : R) (W : nat) :
  (Cnorm (C1 -c rot_atom theta W)
   = Cnorm (C1 -c rot_atom theta 1)
     * Cnorm (PrimeEmbedding.Csum (fun k => rot_atom theta k) W))%R.
Proof.
  pose proof (geom_sum_identity theta W) as E.
  rewrite E. apply Cnorm_mult'.
Qed.

(* ---------- PB2：sin(π−x) = sin x ---------- *)

Lemma sin_PI_minus' (x : R) : (sin (PI - x))%R = sin x.
Proof.
  replace (PI - x)%R with (PI + (-x))%R by ring.
  rewrite sin_plus sin_PI cos_PI sin_neg. ring.
Qed.

(* ---------- PB3：引擎主定理 ---------- *)

Theorem pair_S_bound (a b : nat) :
  (2 <= a)%nat -> (a < b)%nat ->
  (Cnorm (PrimeEmbedding.Csum
            (fun k => rot_atom (2 * PI * (INR b - INR a) / (INR a * INR b)) k) a)
   <= sin (PI * INR a / INR b) * (INR a * INR b) / (2 * (INR b - INR a)))%R.
Proof.
  intros Ha Hab.
  assert (HA : (0 < INR a)%R).
  { apply lt_0_INR. move: Ha => /leP Hap. lia. }
  assert (HB : (0 < INR b)%R).
  { apply lt_0_INR. move: Ha => /leP Hap. move: Hab => /ltP Habp. lia. }
  assert (HAB : (INR a < INR b)%R).
  { apply lt_INR. move: Ha => /leP Hap. move: Hab => /ltP Habp. lia. }
  assert (HBinv : (0 < / INR b)%R) by (apply Rinv_0_lt_compat; exact HB).
  assert (HIsub : (INR (b - a) = INR b - INR a)%R).
  { assert (Hs : (INR (b - a) + INR a = INR b)%R).
    { rewrite <- plus_INR. f_equal. exact (subnK (ltnW Hab)). }
    lra. }
  set (theta := (2 * PI * (INR b - INR a) / (INR a * INR b))%R) in *.
  pose proof (geom_sum_norm_prod theta a) as P.
  (* 分子：|1 − ω^a| = 2·sin(πa/b) *)
  assert (Naraw : (Cnorm (C1 -c rot_atom theta a)
                 = 2 * Rabs (sin (INR a * theta / 2)))%R).
  { rewrite <- (Cnorm_one_minus_exp_i_theta_eq (INR a * theta)). reflexivity. }
  assert (Hcalc : (INR a * theta / 2 = PI - PI * INR a / INR b)%R).
  { unfold theta. field; lra. }
  rewrite Hcalc sin_PI_minus' in Naraw.
  assert (Hsinpos : (0 <= sin (PI * INR a / INR b))%R).
  { apply sin_ge_0.
    - unfold Rdiv. apply Rmult_le_pos.
      + apply Rmult_le_pos; [apply Rlt_le; apply PI_RGT_0 | exact (Rlt_le 0 (INR a) HA)].
      + apply Rlt_le; exact HBinv.
    - apply (Rmult_le_reg_r (INR b) (PI * INR a / INR b) PI HB).
      replace (PI * INR a / INR b * INR b)%R with (PI * INR a)%R by (field; lra).
      assert (HP : (0 < PI)%R) by apply PI_RGT_0.
      nra. }
  rewrite (Rabs_right _ (Rle_ge _ _ Hsinpos)) in Naraw.
  (* 分母：|1 − ω| = 2·sin(θ/2) ≥ 2·(2(b−a)/(ab))（Jordan） *)
  assert (Nbraw : (Cnorm (C1 -c rot_atom theta 1)
                 = 2 * Rabs (sin (theta / 2)))%R).
  { rewrite <- (Cnorm_one_minus_exp_i_theta_eq theta).
    change (rot_atom theta 1) with (Cexp (0 +i (INR 1 * theta))).
    rewrite INR_1. repeat f_equal. ring. }
  assert (Hthalf : (theta / 2 = PI * INR (b - a) / INR (a * b))%R).
  { unfold theta. rewrite <- HIsub. rewrite mult_INR. field; lra. }
  assert (Hjor : ((2 * INR (b - a)) / INR (a * b) <= sin (theta / 2))%R).
  { rewrite Hthalf. apply sin_lower.
    - rewrite subn_gt0. exact Hab.
    - have H1 : (2 * (b - a) <= 2 * b)%nat
        by rewrite (@leq_pmul2l 2 (b - a) b (ltn0Sn 1)); exact (leq_subr a b).
      have H2 : (2 * b <= a * b)%nat.
      { rewrite (@leq_pmul2r b 2 a (ltnW (ltn_trans Ha Hab))). exact Ha. }
      exact (leq_trans H1 H2). }
  assert (HabInv : (0 < / INR (a * b))%R).
  { apply Rinv_0_lt_compat. apply lt_0_INR.
    apply Nat.mul_pos_pos.
    - apply/ltP. exact (ltnW Ha).
    - apply/ltP. exact (ltnW (ltn_trans Ha Hab)). }
  assert (Hab2 : (0 < INR (a * b))%R).
  { apply lt_0_INR. apply Nat.mul_pos_pos.
    - apply/ltP. exact (ltnW Ha).
    - apply/ltP. exact (ltnW (ltn_trans Ha Hab)). }
  assert (Hsinpos2 : (0 <= sin (theta / 2))%R).
  { rewrite Hthalf. apply sin_ge_0.
    - unfold Rdiv. apply Rmult_le_pos.
      + apply Rmult_le_pos; [apply Rlt_le; apply PI_RGT_0 | apply (Rlt_le 0 (INR (b - a))); apply lt_0_INR; apply/ltP; rewrite subn_gt0; exact Hab].
      + apply Rlt_le; exact HabInv.
    - apply (Rmult_le_reg_r (INR (a * b)) (PI * INR (b - a) / INR (a * b)) PI Hab2).
      replace (PI * INR (b - a) / INR (a * b) * INR (a * b))%R
        with (PI * INR (b - a))%R by (field; lra).
      assert (HP : (0 < PI)%R) by apply PI_RGT_0.
      assert (Hkey : (INR (b - a) <= INR (a * b))%R).
      { apply le_INR. apply/leP. apply (leq_trans (leq_subr a b)).
        rewrite -[b in b <= _]mul1n. rewrite (@leq_pmul2r b 1 a (ltnW (ltn_trans Ha Hab))). exact (ltnW Ha). }
      nra. }
  rewrite (Rabs_right _ (Rle_ge _ _ Hsinpos2)) in Nbraw.
  rewrite Naraw in P. rewrite Nbraw in P.
  set (d0 := (2 * (2 * INR (b - a) / INR (a * b)))%R) in *.
  assert (Hd0 : (0 < d0)%R).
  { unfold d0, Rdiv.
    apply Rmult_lt_0_compat; [ lra | ].
    apply Rmult_lt_0_compat; [ apply (Rmult_lt_0_compat 2 (INR (b - a))); [ lra | apply lt_0_INR; apply/ltP; rewrite subn_gt0; exact Hab ] | apply Rinv_0_lt_compat; apply lt_0_INR; apply/ltP; rewrite muln_gt0; apply/andP; split; [exact (ltnW Ha) | exact (ltnW (ltn_trans Ha Hab))] ]. }
  assert (Hd0le : (d0 <= 2 * sin (theta / 2))%R)
    by (unfold d0; apply Rmult_le_compat_l; [ lra | exact Hjor ]).
  assert (Hstep : (Cnorm (PrimeEmbedding.Csum (fun k => rot_atom theta k) a) * d0
                   <= 2 * sin (PI * INR a / INR b))%R).
  { apply (Rle_trans _
             (2 * sin (theta / 2)
              * Cnorm (PrimeEmbedding.Csum (fun k => rot_atom theta k) a))).
    - replace (Cnorm (PrimeEmbedding.Csum (fun k => rot_atom theta k) a) * d0)%R
        with (d0 * Cnorm (PrimeEmbedding.Csum (fun k => rot_atom theta k) a))%R
        by ring.
      apply Rmult_le_compat_r; [ apply Cnorm_ge0 | exact Hd0le ].
    - rewrite <- P. apply Rle_refl. }
  apply (Rmult_le_reg_r d0 _ _ Hd0).
  replace (sin (PI * INR a / INR b) * (INR a * INR b) / (2 * (INR b - INR a)) * d0)%R
    with (2 * sin (PI * INR a / INR b))%R
    by (unfold d0, Rdiv; rewrite HIsub mult_INR; field; lra).
  exact Hstep.
Qed.

(* ---------- PB4：归一化系（|⟨ψ_a,ψ_b⟩| 界） ---------- *)

Corollary pair_inner_norm (a b : nat) :
  (2 <= a)%nat -> (a < b)%nat ->
  ((Cnorm (PrimeEmbedding.Csum
             (fun k => rot_atom (2 * PI * (INR b - INR a) / (INR a * INR b)) k) a)
    / sqrt (INR a * INR b))
   <= sin (PI * INR a / INR b) * sqrt (INR a * INR b) / (2 * (INR b - INR a)))%R.
Proof.
  intros Ha Hab.
  assert (H := pair_S_bound a b Ha Hab).
  assert (HIs : (INR (b - a) = INR b - INR a)%R).
  { assert (Hs : (INR (b - a) + INR a = INR b)%R)
      by (rewrite <- plus_INR; f_equal; exact (subnK (ltnW Hab))).
    lra. }
  assert (HBA : (0 < INR b - INR a)%R)
    by (rewrite <- HIs; apply lt_0_INR; apply/ltP; rewrite subn_gt0; exact Hab).
  assert (Hab1 : (0 < INR a)%R)
    by (apply lt_0_INR; move: Ha => /leP Hap; lia).
  assert (Hbb1 : (0 < INR b)%R)
    by (apply lt_0_INR; move: Ha => /leP Hap; move: Hab => /ltP Habp; lia).
  assert (Hsq : (0 < sqrt (INR a * INR b))%R).
  { apply sqrt_pos_strict. nra. }
  assert (Hss : (sqrt (INR a * INR b) * sqrt (INR a * INR b) = INR a * INR b)%R)
    by (apply sqrt_sqrt; nra).
  apply (Rmult_le_reg_r (sqrt (INR a * INR b)) _ _ Hsq).
  replace (Cnorm (PrimeEmbedding.Csum
                    (fun k => rot_atom (2 * PI * (INR b - INR a) / (INR a * INR b)) k) a)
             / sqrt (INR a * INR b) * sqrt (INR a * INR b))%R
    with (Cnorm (PrimeEmbedding.Csum
                    (fun k => rot_atom (2 * PI * (INR b - INR a) / (INR a * INR b)) k) a))%R
    by (unfold Rdiv; field; lra).
  assert (E2 : (sin (PI * INR a / INR b) * sqrt (INR a * INR b)
                  / (2 * (INR b - INR a)) * sqrt (INR a * INR b)
                  = sin (PI * INR a / INR b) * (INR a * INR b) / (2 * (INR b - INR a)))%R).
  { transitivity (sin (PI * INR a / INR b) * (sqrt (INR a * INR b) * sqrt (INR a * INR b))
                    / (2 * (INR b - INR a)))%R.
    - field. lra.
    - rewrite Hss. field. lra. }
  rewrite E2. exact H.
Qed.

End PairBound.

Print Assumptions PairBound.pair_S_bound.
Print Assumptions PairBound.pair_inner_norm.
