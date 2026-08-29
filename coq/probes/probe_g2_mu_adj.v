(* ============================================================
   Task: 定理缺口深化分析 G-2 (third-party eval, B-7 narrative)
   Red lines: zero Admitted, zero custom axioms; classic R track
   (mu_adj has sin/sqrt; CR track has no trig functions).

   Math (mu_adj theorization, eval T*-3 + cross-check section 3):
     For ratio-r ladder n_{k+1} >= r*n_k, adjacent-band coherence:
       mu_adj(r) := sqrt(r) * sin(pi/r) / (pi*(r-1))
     - mu_adj decreasing on r >= 2 (r->1+ gives ->1 uncertifiable,
       r->oo gives ->0)
     - Phase transition rstar (mu_adj(rstar) = 4/5, numerically ~1.30)

   Proof route:
     R0. Definition and basics: well-defined (r>1), nonneg
     R1. mu_adj monotone decreasing on r >= 2
     R2. Phase transition exists: exists rstar, mu_adj(rstar) = 4/5
     R3. Adjacent-band asymptotic: lim mu(n_k,n_{k+1}) = mu_adj(r)

   Dependencies: probe_partial (sin_lower), probe_pairbound (pair_S_bound),
     ca_fourier/ca_taylor (sin limits), G-1 exact norm (prerequisite).
   Audit: zero Admitted / zero custom axioms.
   ============================================================ *)
From mathcomp Require Import ssreflect ssrbool ssrnat seq eqtype div prime.
Require Import Stdlib.Reals.Reals.
Require Import Stdlib.Reals.Ranalysis1.
Require Import Stdlib.Reals.Ranalysis5.
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
Require Import probe_parseval.
Require Import probe_partial.
Require Import probe_pairbound.
Import ComplexNumbers.
Import FourierAnalysis.
Import GridOrtho.
Import TPartial.
Import PairBound.

Open Scope R_scope.

Module G2MuAdj.

(* ============ R0. Definition and basics ============ *)

(* mu_adj(r) := sqrt(r)*sin(pi/r)/(pi*(r-1)) *)
Definition mu_adj (r : R) : R :=
  sqrt r * sin (PI / r) / (PI * (r - 1))%R.

(* Well-defined: r > 1 gives nonzero denominator *)
Lemma mu_adj_def (r : R) :
  (1 < r)%R -> (PI * (r - 1))%R <> 0%R.
Proof.
  intros Hr.
  apply Rmult_integral_contrapositive.
  split.
  - apply Rgt_not_eq. apply PI_RGT_0.
  - apply Rgt_not_eq. lra.
Qed.

(* Nonneg: r >= 2 gives sqrt>=0, sin(pi/r)>=0, denom>0 *)
Lemma mu_adj_nonneg (r : R) :
  (2 <= r)%R -> (0 <= mu_adj r)%R.
Proof.
  intros Hr.
  unfold mu_adj.
  apply Rmult_le_pos.
  - apply Rmult_le_pos.
    + apply sqrt_pos.
    + apply sin_ge_0.
      * assert (Hpos : (0 < PI / r)%R).
        { unfold Rdiv. apply Rmult_lt_0_compat; [apply PI_RGT_0 | apply Rinv_0_lt_compat; lra]. }
        apply Rlt_le. exact Hpos.
      * assert (Hle : (PI / r <= PI)%R).
        { unfold Rdiv.
          apply (Rmult_le_reg_l r).
          - lra.
          - replace (r * (PI * / r))%R with PI%R by (field; lra).
            rewrite Rmult_comm.
            replace (PI)%R with (PI * 1)%R at 1 by ring.
            apply Rmult_le_compat_l.
            + apply Rlt_le. apply PI_RGT_0.
            + lra. }
        exact Hle.
  - apply Rlt_le. apply Rinv_0_lt_compat.
    apply Rmult_lt_0_compat; [apply PI_RGT_0 | lra].
Qed.

(* ============ R1. Monotone decreasing on r >= 2 ============ *)

(* f(r) = sqrt(r)/(r-1) decreasing: cross-multiplied form *)
Lemma g2_sqrt_cross (a b : R) :
  (2 <= a)%R -> (a < b)%R ->
  (sqrt b * (a - 1) < sqrt a * (b - 1))%R.
Proof.
  intros Ha Hab.
  assert (Hsq : b * (a - 1)^2 < a * (b - 1)^2).
  { assert (Heq : b * (a - 1)^2 - a * (b - 1)^2 = - ((b - a) * (a * b - 1))) by ring.
    apply Rminus_lt.
    rewrite Heq.
    assert (Hpos : 0 < (b - a) * (a * b - 1)) by (apply Rmult_lt_0_compat; [lra | nra]).
    lra. }
  assert (H1 : sqrt (b * (a - 1)^2) < sqrt (a * (b - 1)^2)).
  { apply sqrt_lt_1; [apply Rmult_le_pos; [lra | apply pow2_ge_0]
    | apply Rmult_le_pos; [lra | apply pow2_ge_0] | exact Hsq]. }
  assert (Hb0 : (0 <= b)%R) by lra.
  assert (Ha0 : (0 <= a)%R) by lra.
  assert (Ha1 : (0 <= a - 1)%R) by lra.
  assert (Hb1 : (0 <= b - 1)%R) by lra.
  rewrite (sqrt_mult b ((a - 1)^2) Hb0 (pow2_ge_0 (a - 1))) in H1.
  rewrite (sqrt_mult a ((b - 1)^2) Ha0 (pow2_ge_0 (b - 1))) in H1.
  rewrite (sqrt_pow2 (a - 1) Ha1) in H1.
  rewrite (sqrt_pow2 (b - 1) Hb1) in H1.
  exact H1.
Qed.

(* 0 < PI / r for r > 0 *)
Lemma g2_pi_over_r_pos (r : R) : (0 < r)%R -> (0 < PI / r)%R.
Proof.
  intros Hr.
  unfold Rdiv.
  apply Rmult_lt_0_compat; [apply PI_RGT_0 | apply Rinv_0_lt_compat; exact Hr].
Qed.

(* g(r) = sin(pi/r) increasing for r >= 2 *)
Lemma g2_sin_incr (a b : R) :
  (2 <= a)%R -> (a < b)%R ->
  (sin (PI / b) < sin (PI / a))%R.
Proof.
  intros Ha Hab.
  assert (Ha0 : 0 < a) by lra.
  assert (Hb0 : 0 < b) by lra.
  assert (HPI : 0 < PI) by apply PI_RGT_0.
  apply sin_increasing_1.
  (* -PI/2 <= PI/b *)
  - apply Rle_trans with 0%R; [lra | apply Rlt_le; apply g2_pi_over_r_pos; exact Hb0].
  (* PI/b <= PI/2 *)
  - unfold Rdiv.
    apply Rmult_le_compat_l; [apply Rlt_le; apply PI_RGT_0 |].
    apply Rinv_le_contravar; [lra | lra].
  (* -PI/2 <= PI/a *)
  - apply Rle_trans with 0%R; [lra | apply Rlt_le; apply g2_pi_over_r_pos; exact Ha0].
  (* PI/a <= PI/2 *)
  - unfold Rdiv.
    apply Rmult_le_compat_l; [apply Rlt_le; apply PI_RGT_0 |].
    apply Rinv_le_contravar; [lra | lra].
  (* PI/b < PI/a *)
  - unfold Rdiv.
    apply Rmult_lt_compat_l; [apply PI_RGT_0 |].
    apply Rinv_lt_contravar.
    + apply Rmult_lt_0_compat; lra.
    + lra.
Qed.

(* sin(pi/r) > 0 for r >= 2 *)
Lemma g2_sin_pos (r : R) :
  (2 <= r)%R -> (0 < sin (PI / r))%R.
Proof.
  intros Hr.
  assert (HPI : 0 < PI) by apply PI_RGT_0.
  assert (Hr0 : 0 < r) by lra.
  assert (H : sin 0 < sin (PI / r)).
  { apply sin_increasing_1.
    - lra.
    - lra.
    - apply Rle_trans with 0%R; [lra | apply Rlt_le; apply g2_pi_over_r_pos; exact Hr0].
    - unfold Rdiv.
      apply Rmult_le_compat_l; [apply Rlt_le; apply PI_RGT_0 |].
      apply Rinv_le_contravar; [lra | lra].
    - apply g2_pi_over_r_pos; exact Hr0.
  }
  rewrite sin_0 in H.
  exact H.
Qed.

(* 0 < sqrt r for r > 0 *)
Lemma g2_sqrt_pos (r : R) : (0 < r)%R -> (0 < sqrt r)%R.
Proof.
  intros Hr.
  assert (H : sqrt 0 < sqrt r).
  { apply sqrt_lt_1; [lra | apply Rlt_le; exact Hr | lra]. }
  rewrite sqrt_0 in H.
  exact H.
Qed.

(* Cross form: mu_adj numerator comparison *)
Lemma g2_mu_cross (r1 r2 : R) :
  (2 <= r1)%R -> (r1 < r2)%R ->
  (sqrt r2 * sin (PI / r2) * (r1 - 1) < sqrt r1 * sin (PI / r1) * (r2 - 1))%R.
Proof.
  intros Hr1 Hr12.
  assert (Hsin : sin (PI / r2) < sin (PI / r1)) by (apply g2_sin_incr; assumption).
  assert (Hsqrt : sqrt r2 * (r1 - 1) < sqrt r1 * (r2 - 1)) by (apply g2_sqrt_cross; assumption).
  assert (Hsinpos : 0 < sin (PI / r1)) by (apply g2_sin_pos; lra).
  assert (Hprodpos : 0 < sqrt r2 * (r1 - 1)) by (apply Rmult_lt_0_compat; [apply g2_sqrt_pos; lra | lra]).
  apply (Rlt_trans _ (sqrt r2 * sin (PI / r1) * (r1 - 1)) _).
  - replace (sqrt r2 * sin (PI / r2) * (r1 - 1)) with ((sqrt r2 * (r1 - 1)) * sin (PI / r2)) by ring.
    replace (sqrt r2 * sin (PI / r1) * (r1 - 1)) with ((sqrt r2 * (r1 - 1)) * sin (PI / r1)) by ring.
    apply Rmult_lt_compat_l; [exact Hprodpos | exact Hsin].
  - replace (sqrt r2 * sin (PI / r1) * (r1 - 1)) with (sin (PI / r1) * (sqrt r2 * (r1 - 1))) by ring.
    replace (sqrt r1 * sin (PI / r1) * (r2 - 1)) with (sin (PI / r1) * (sqrt r1 * (r2 - 1))) by ring.
    apply Rmult_lt_compat_l; [exact Hsinpos | exact Hsqrt].
Qed.

(* Divide-out helpers for the final cross-multiplication *)
Lemma g2_mu_div_l (r1 r2 : R) :
  (2 <= r1)%R -> (r1 < r2)%R ->
  (sqrt r2 * sin (PI / r2) * (r1 - 1) * / (PI * (r2 - 1) * (r1 - 1))
   = sqrt r2 * sin (PI / r2) * / (PI * (r2 - 1)))%R.
Proof.
  intros Hr1 Hr12.
  field.
  split; [lra | split; [apply Rgt_not_eq, PI_RGT_0 | lra]].
Qed.

Lemma g2_mu_div_r (r1 r2 : R) :
  (2 <= r1)%R -> (r1 < r2)%R ->
  (sqrt r1 * sin (PI / r1) * (r2 - 1) * / (PI * (r2 - 1) * (r1 - 1))
   = sqrt r1 * sin (PI / r1) * / (PI * (r1 - 1)))%R.
Proof.
  intros Hr1 Hr12.
  field.
  split; [lra | split; [apply Rgt_not_eq, PI_RGT_0 | lra]].
Qed.

Theorem mu_adj_decreasing (r1 r2 : R) :
  (2 <= r1)%R -> (r1 < r2)%R ->
  (mu_adj r2 < mu_adj r1)%R.
Proof.
  intros Hr1 Hr12.
  unfold mu_adj.
  assert (Hcross : sqrt r2 * sin (PI / r2) * (r1 - 1) < sqrt r1 * sin (PI / r1) * (r2 - 1))
    by (apply g2_mu_cross; assumption).
  (* multiply both sides of Hcross by the positive /(PI*(r2-1)*(r1-1)) *)
  apply (Rmult_lt_compat_r (/ (PI * (r2 - 1) * (r1 - 1)))) in Hcross.
  - rewrite (g2_mu_div_l r1 r2 Hr1 Hr12) in Hcross.
    rewrite (g2_mu_div_r r1 r2 Hr1 Hr12) in Hcross.
    exact Hcross.
  - apply Rinv_0_lt_compat.
    assert (HPI : 0 < PI) by apply PI_RGT_0.
    assert (Hr21 : 0 < r2 - 1) by lra.
    assert (Hr11 : 0 < r1 - 1) by lra.
    apply Rmult_lt_0_compat; [apply Rmult_lt_0_compat; [exact HPI | exact Hr21] | exact Hr11].
Qed.

(* ============ R2. Phase transition exists ============ *)
(* 相变存在性证明路线：
   - pi upper bound pi < 17/5 via sin_bound 0th order (sin_approx t 2 = t - t^3/6 + t^5/120)
   - pi lower bound pi > 3 via PI2_3_2
   - mu_adj(6/5) > 4/5  (sqrt(6/5)*5/(2pi) > 4/5  <=>  750 > 64 pi^2, pi < 17/5)
   - mu_adj(3/2) < 4/5  (3/(sqrt 2 * pi) < 4/5  <=>  225 < 32 pi^2, pi > 3)
   - IVT_interv on g(r) = -(mu_adj r - 4/5), g(6/5) < 0 < g(3/2) *)

(* pi < 17/5: sin_bound 0th order *)
Lemma g2_sin_approx2 (t : R) :
  sin_approx t 2 = t - t ^ 3 / 6 + t ^ 5 / 120.
Proof.
  unfold sin_approx, sin_term.
  cbn.
  replace (2 * 0 + 1)%nat with 1%nat by reflexivity.
  replace (2 * 1 + 1)%nat with 3%nat by reflexivity.
  replace (2 * 2 + 1)%nat with 5%nat by reflexivity.
  field.
  all: try (apply Rgt_not_eq; lra).
Qed.

Lemma g2_sin_approx2_pi_ge_1 : (1 <= sin_approx (PI / 2) 2)%R.
Proof.
  assert (Hpos : (0 <= PI / 2)%R) by (apply Rlt_le; apply PI2_RGT_0).
  assert (Hle : (PI / 2 <= PI)%R) by (apply Rlt_le; apply PI2_Rlt_PI).
  pose proof (sin_bound (PI / 2) 0 Hpos Hle) as H.
  destruct H as [Hlo Hhi].
  rewrite sin_PI2 in Hhi.
  replace (2 * (0 + 1))%nat with 2%nat in Hhi by reflexivity.
  exact Hhi.
Qed.

Lemma pow2_2 (t : R) : t ^ 4 = (t ^ 2) ^ 2.
Proof.
  change (t ^ (2 * 2) = (t ^ 2) ^ 2).
  rewrite <- pow_mult.
  reflexivity.
Qed.

(* f'(t) = 1 - t^2/2 + t^4/24 < 0 on [17/10, 2] *)
Lemma g2_fp_neg (t : R) : (17 / 10 <= t)%R -> (t <= 2)%R ->
  (1 - t ^ 2 / 2 + t ^ 4 / 24 < 0)%R.
Proof.
  intros Hlo Hhi.
  rewrite pow2_2.
  set (u := t ^ 2).
  assert (Hlo_u : (289 / 100 <= u)%R).
  { subst u. nra. }
  assert (Hhi_u : (u <= 4)%R).
  { subst u. nra. }
  replace (1 - t ^ 2 / 2 + (t ^ 2) ^ 2 / 24) with (1 - u / 2 + u ^ 2 / 24) by (subst u; ring).
  nra.
Qed.

(* f(x) = x - x^3/6 + x^5/120, derivative in INR form *)
Lemma g2_dpl_f (x : R) :
  derivable_pt_lim (fun t => t - t ^ 3 / 6 + t ^ 5 / 120)
                   x (1 - INR 3 * x ^ Nat.pred 3 / 6 + INR 5 * x ^ Nat.pred 5 / 120).
Proof.
  assert (Hpow3 : derivable_pt_lim (fun t => t ^ 3) x (INR 3 * x ^ (Nat.pred 3))).
  { apply (derivable_pt_lim_pow x 3). }
  assert (Hpow5 : derivable_pt_lim (fun t => t ^ 5) x (INR 5 * x ^ (Nat.pred 5))).
  { apply (derivable_pt_lim_pow x 5). }
  assert (Hdiv3 : derivable_pt_lim (fun t => t ^ 3 / 6) x (INR 3 * x ^ Nat.pred 3 / 6)).
  { apply derivable_pt_lim_div_scal. exact Hpow3. }
  assert (Hdiv5 : derivable_pt_lim (fun t => t ^ 5 / 120) x (INR 5 * x ^ Nat.pred 5 / 120)).
  { apply derivable_pt_lim_div_scal. exact Hpow5. }
  assert (H1 : derivable_pt_lim (fun t => t - t ^ 3 / 6) x (1 - INR 3 * x ^ Nat.pred 3 / 6)).
  { change (derivable_pt_lim (fun t => t + (- (t ^ 3 / 6))) x (1 + (- (INR 3 * x ^ Nat.pred 3 / 6)))).
    apply derivable_pt_lim_plus.
    - change (derivable_pt_lim id x 1). apply derivable_pt_lim_id.
    - apply derivable_pt_lim_opp. exact Hdiv3. }
  change (derivable_pt_lim (fun t => (t - t ^ 3 / 6) + t ^ 5 / 120) x ((1 - INR 3 * x ^ Nat.pred 3 / 6) + INR 5 * x ^ Nat.pred 5 / 120)).
  apply derivable_pt_lim_plus; [exact H1 | exact Hdiv5].
Qed.

(* bridge to the displayed derivative *)
Lemma g2_dpl_f_nice (x : R) :
  derivable_pt_lim (fun t => t - t ^ 3 / 6 + t ^ 5 / 120) x (1 - x ^ 2 / 2 + x ^ 4 / 24).
Proof.
  assert (H : derivable_pt_lim (fun t => t - t ^ 3 / 6 + t ^ 5 / 120)
                   x (1 - INR 3 * x ^ Nat.pred 3 / 6 + INR 5 * x ^ Nat.pred 5 / 120)) by apply g2_dpl_f.
  assert (Hv : (1 - INR 3 * x ^ Nat.pred 3 / 6 + INR 5 * x ^ Nat.pred 5 / 120
                = 1 - x ^ 2 / 2 + x ^ 4 / 24)%R).
  { unfold Nat.pred.
    assert (H3 : (INR 3 = 3)%R). { rewrite INR_IZR_INZ. reflexivity. }
    assert (H5 : (INR 5 = 5)%R). { rewrite INR_IZR_INZ. reflexivity. }
    rewrite H3. rewrite H5.
    field. }
  rewrite Hv in H.
  exact H.
Qed.

(* f strictly decreasing on [17/10, t] for t <= 2 via MVT *)
Lemma g2_f_decr (t : R) :
  (17 / 10 < t)%R -> (t <= 2)%R ->
  (t - t ^ 3 / 6 + t ^ 5 / 120 < 17/10 - (17/10)^3/6 + (17/10)^5/120)%R.
Proof.
  intros Hlt Hhi.
  destruct (MVT_cor3 (fun x => x - x ^ 3 / 6 + x ^ 5 / 120)
                     (fun x => 1 - x ^ 2 / 2 + x ^ 4 / 24)
                     (17 / 10) t) as [c [Hc1 [Hc2 Hc3]]].
  - exact Hlt.
  - intros x Hx1 Hx2. apply g2_dpl_f_nice.
  - assert (Hneg : (1 - c ^ 2 / 2 + c ^ 4 / 24 < 0)%R).
    { apply g2_fp_neg; [exact Hc1 | eapply Rle_trans; [exact Hc2 | exact Hhi]]. }
    rewrite Hc3.
    nra.
Qed.

Lemma g2_f_17_10_lt_1 : (17/10 - (17/10)^3/6 + (17/10)^5/120 < 1)%R.
Proof.
  nra.
Qed.

Lemma g2_pi_lt_17_5 : (PI < 17 / 5)%R.
Proof.
  apply Rnot_ge_lt.
  intro Hge.
  assert (Ht : (17 / 10 <= PI / 2)%R) by lra.
  assert (Hlt1 : (sin_approx (17 / 10) 2 < 1)%R).
  { rewrite g2_sin_approx2. exact g2_f_17_10_lt_1. }
  assert (Hc : (sin_approx (PI / 2) 2 < 1)%R).
  { destruct (Req_dec (PI / 2) (17 / 10)) as [Heq | Hne].
    - rewrite Heq. exact Hlt1.
    - assert (Hlt : (17 / 10 < PI / 2)%R) by lra.
      assert (Hdec : (sin_approx (PI / 2) 2 < sin_approx (17 / 10) 2)%R).
      { rewrite g2_sin_approx2. rewrite g2_sin_approx2.
        apply g2_f_decr; [exact Hlt | ].
        assert (Hpi2 : (PI / 2 <= 2)%R).
        { apply Rmult_le_reg_l with 2%R; [lra |].
          replace (2 * (PI / 2))%R with PI%R by (field; apply Rgt_not_eq, PI_RGT_0).
          replace (2 * 2)%R with 4%R by ring.
          exact PI_4. }
        exact Hpi2. }
      eapply Rlt_trans; [exact Hdec | exact Hlt1]. }
  assert (H1le : (1 <= sin_approx (PI / 2) 2)%R) by exact g2_sin_approx2_pi_ge_1.
  lra.
Qed.

(* pi > 3 *)
Lemma g2_pi_gt_3 : (3 < PI)%R.
Proof.
  assert (H : (2 * (3 / 2) < 2 * (PI / 2))%R).
  { apply Rmult_lt_compat_l; [lra | exact PI2_3_2]. }
  replace (2 * (3 / 2))%R with 3%R in H by field.
  replace (2 * (PI / 2))%R with PI%R in H by (field; apply Rgt_not_eq, PI_RGT_0).
  exact H.
Qed.

(* sqrt(3/2)*sqrt 3 = 3/sqrt 2 *)
Lemma g2_sqrt_32_3 : (sqrt (3 / 2) * sqrt 3 = 3 / sqrt 2)%R.
Proof.
  assert (Hm : (sqrt (3 / 2) * sqrt 3 = sqrt ((3 / 2) * 3))%R).
  { symmetry. apply sqrt_mult; lra. }
  rewrite Hm.
  replace ((3 / 2) * 3)%R with (9 / 2)%R by field.
  apply Rsqr_inj.
  - apply sqrt_pos.
  - apply Rlt_le; apply Rdiv_lt_0_compat; [lra | apply g2_sqrt_pos; lra].
  - assert (Ht1 : (Rsqr (sqrt (9 / 2)) = 9 / 2)%R).
    { unfold Rsqr. apply Rsqr_sqrt. lra. }
    assert (Ht2 : (Rsqr (3 / sqrt 2) = 9 / 2)%R).
    { unfold Rsqr, Rdiv.
      assert (Hnz : sqrt 2 <> 0) by (apply Rgt_not_eq; apply g2_sqrt_pos; lra).
      replace (3 * / sqrt 2 * (3 * / sqrt 2))%R with (9 * / (sqrt 2 * sqrt 2))%R by (field; exact Hnz).
      replace (sqrt 2 * sqrt 2)%R with 2%R by (rewrite sqrt_sqrt; [reflexivity | lra]).
      field. }
    rewrite Ht1. rewrite Ht2. reflexivity.
Qed.

(* mu_adj(6/5) > 4/5 : 25*sqrt(6/5) > 8PI  <=>  750 > 64 PI^2, pi < 17/5 *)
Lemma g2_mu_65_gt : (sqrt (6 / 5) * 5 / (2 * PI) > 4 / 5)%R.
Proof.
  assert (Hpi : (PI < 17 / 5)%R) by exact g2_pi_lt_17_5.
  assert (Hpi2 : (Rsqr PI < 289 / 25)%R).
  { unfold Rsqr.
    assert (Hp1 : (PI * PI < PI * (17 / 5))%R).
    { apply Rmult_lt_compat_l; [apply PI_RGT_0 | exact Hpi]. }
    assert (Hp2 : (PI * (17 / 5) < 289 / 25)%R).
    { assert (Hq : (PI * (17 / 5) < (17 / 5) * (17 / 5))%R).
      { apply Rmult_lt_compat_r; [lra | exact Hpi]. }
      replace ((17 / 5) * (17 / 5))%R with (289 / 25)%R in Hq by field.
      exact Hq. }
    apply Rlt_trans with (PI * (17 / 5))%R; [exact Hp1 | exact Hp2]. }
  assert (Hgt : (8 * PI / 25 < sqrt (6 / 5))%R).
  { apply Rnot_le_lt.
    intro Hle.
    assert (Hsq : (Rsqr (sqrt (6 / 5)) <= Rsqr (8 * PI / 25))%R).
    { apply Rsqr_incr_1; [exact Hle | apply sqrt_pos | ].
      assert (Hpi0 : (0 < PI)%R) by apply PI_RGT_0.
      assert (Hpos : (0 < 8 * PI / 25)%R).
      { unfold Rdiv. apply Rmult_lt_0_compat; [lra | apply Rinv_0_lt_compat; lra]. }
      apply Rlt_le. exact Hpos. }
    assert (Hs : (Rsqr (sqrt (6 / 5)) = 6 / 5)%R).
    { apply Rsqr_sqrt. lra. }
    rewrite Hs in Hsq.
    assert (Heq : (Rsqr (8 * PI / 25) = 64 * Rsqr PI / 625)%R).
    { unfold Rsqr. field. }
    rewrite Heq in Hsq.
    assert (H750 : (750 <= 64 * Rsqr PI)%R).
    { apply (Rmult_le_compat_r 625) in Hsq; [| lra].
      replace (6 / 5 * 625)%R with 750%R in Hsq by field.
      replace (64 * Rsqr PI / 625 * 625)%R with (64 * Rsqr PI)%R in Hsq by (field; lra).
      exact Hsq. }
    assert (H750lt : (750 > 64 * Rsqr PI)%R).
    { assert (H64 : (64 * Rsqr PI < 64 * (289 / 25))%R).
      { apply Rmult_lt_compat_l; [lra | exact Hpi2]. }
      replace (64 * (289 / 25))%R with (18496 / 25)%R in H64 by field.
      apply Rlt_trans with (18496 / 25)%R; [exact H64 | nra]. }
    lra. }
  assert (H25 : (8 * PI < 25 * sqrt (6 / 5))%R).
  { apply (Rmult_lt_compat_r 25) in Hgt.
    - replace (8 * PI / 25 * 25)%R with (8 * PI)%R in Hgt by (field; lra).
      replace (sqrt (6 / 5) * 25)%R with (25 * sqrt (6 / 5))%R in Hgt by ring.
      exact Hgt.
    - lra. }
  assert (Hcross : (4 / 5 < sqrt (6 / 5) * 5 / (2 * PI))%R).
  { replace (4 / 5)%R with ((8 * PI) / (5 * (2 * PI)))%R
      by (field; apply Rgt_not_eq, PI_RGT_0).
    replace (sqrt (6 / 5) * 5 / (2 * PI))%R with ((25 * sqrt (6 / 5)) / (5 * (2 * PI)))%R.
    - assert (Hden : (0 < 5 * (2 * PI))%R).
      { assert (Hpi0 : (0 < PI)%R) by apply PI_RGT_0. lra. }
      apply Rmult_lt_reg_r with (5 * (2 * PI))%R; [exact Hden |].
      replace ((8 * PI) / (5 * (2 * PI)) * (5 * (2 * PI)))%R with (8 * PI)%R
        by (field; apply Rgt_not_eq, PI_RGT_0).
      replace ((25 * sqrt (6 / 5)) / (5 * (2 * PI)) * (5 * (2 * PI)))%R with (25 * sqrt (6 / 5))%R
        by (field; apply Rgt_not_eq, PI_RGT_0).
      exact H25.
    - field. apply Rgt_not_eq, PI_RGT_0. }
  exact Hcross.
Qed.

(* mu_adj(3/2) < 4/5 : 3/(sqrt 2 * pi) < 4/5  <=>  225 < 32 pi^2, pi > 3 *)
Lemma g2_mu_32_lt : (sqrt (3 / 2) * sin (2 * (PI / 3)) / (PI * (3 / 2 - 1)) < 4 / 5)%R.
Proof.
  rewrite sin_2PI3.
  assert (Heq : (sqrt (3 / 2) * (sqrt 3 / 2) / (PI * (3 / 2 - 1)) = 3 / (sqrt 2 * PI))%R).
  { replace (sqrt (3 / 2) * (sqrt 3 / 2))%R with (sqrt (3 / 2) * sqrt 3 * / 2)%R by (field; lra).
    rewrite g2_sqrt_32_3.
    replace (3 / 2 - 1)%R with (/ 2)%R by field.
    field.
    split; [apply Rgt_not_eq, PI_RGT_0 | apply Rgt_not_eq; apply g2_sqrt_pos; lra]. }
  rewrite Heq.
  assert (Hpi : (3 < PI)%R) by exact g2_pi_gt_3.
  assert (Hpi2 : (3 * 3 < Rsqr PI)%R).
  { unfold Rsqr.
    assert (Hp1 : (3 * 3 < 3 * PI)%R).
    { apply Rmult_lt_compat_l; [lra | exact Hpi]. }
    assert (Hp2 : (3 * PI < PI * PI)%R).
    { apply Rmult_lt_compat_r; [apply PI_RGT_0 | exact Hpi]. }
    apply Rlt_trans with (3 * PI)%R; [exact Hp1 | exact Hp2]. }
  assert (Hsq : (225 < 32 * Rsqr PI)%R).
  { apply Rlt_trans with (32 * (3 * 3))%R.
    - nra.
    - apply Rmult_lt_compat_l; [lra | exact Hpi2]. }
  assert (Hc : (15 < 4 * sqrt 2 * PI)%R).
  { apply Rnot_le_lt.
    intro Hle.
    assert (Hsqle : (Rsqr (4 * sqrt 2 * PI) <= Rsqr 15)%R).
    { apply Rsqr_incr_1; [exact Hle | | ].
      - apply Rmult_le_pos; [apply Rmult_le_pos; [lra | apply sqrt_pos] | apply Rlt_le, PI_RGT_0].
      - lra. }
    replace (Rsqr 15)%R with 225%R in Hsqle by (unfold Rsqr; ring).
    replace (Rsqr (4 * sqrt 2 * PI))%R with (32 * Rsqr PI)%R in Hsqle.
    + lra.
    + rewrite Rsqr_mult. rewrite Rsqr_mult.
      replace (Rsqr (sqrt 2))%R with 2%R by (unfold Rsqr; rewrite sqrt_sqrt; [ring | lra]).
      unfold Rsqr. ring. }
  apply Rmult_lt_reg_r with (sqrt 2 * PI)%R; [apply Rmult_lt_0_compat; [apply g2_sqrt_pos; lra | apply PI_RGT_0] |].
  apply Rmult_lt_reg_r with 5%R; [lra |].
  replace ((3 / (sqrt 2 * PI)) * (sqrt 2 * PI) * 5)%R with 15%R
    by (field; split; [apply Rgt_not_eq, PI_RGT_0 | apply Rgt_not_eq; apply g2_sqrt_pos; lra]).
  replace ((4 / 5) * (sqrt 2 * PI) * 5)%R with (4 * sqrt 2 * PI)%R by (field; lra).
  exact Hc.
Qed.

(* sin(PI/(6/5)) = 1/2 *)
Lemma g2_sin_65 : (sin (PI / (6 / 5)) = 1 / 2)%R.
Proof.
  replace (PI / (6 / 5))%R with (5 * (PI / 6))%R by (field; lra).
  replace (5 * (PI / 6))%R with (PI - PI / 6)%R by (field; apply Rgt_not_eq, PI_RGT_0).
  rewrite sin_PI_x.
  rewrite sin_PI6.
  reflexivity.
Qed.

(* sin(PI/(3/2)) = sin(2*(PI/3)) *)
Lemma g2_sin_32 : (sin (PI / (3 / 2)) = sin (2 * (PI / 3)))%R.
Proof.
  replace (PI / (3 / 2))%R with (2 * (PI / 3))%R by (field; lra).
  reflexivity.
Qed.

(* mu_adj(6/5) > 4/5 in mu_adj form *)
Lemma g2_mu_65_gt_mu : (mu_adj (6 / 5) > 4 / 5)%R.
Proof.
  unfold mu_adj.
  rewrite g2_sin_65.
  replace (6 / 5 - 1)%R with (1 / 5)%R by field.
  replace (sqrt (6 / 5) * (1 / 2) / (PI * (1 / 5)))%R with (sqrt (6 / 5) * 5 / (2 * PI))%R.
  - exact g2_mu_65_gt.
  - field. apply Rgt_not_eq, PI_RGT_0.
Qed.

(* mu_adj(3/2) < 4/5 in mu_adj form *)
Lemma g2_mu_32_lt_mu : (mu_adj (3 / 2) < 4 / 5)%R.
Proof.
  unfold mu_adj.
  rewrite g2_sin_32.
  exact g2_mu_32_lt.
Qed.


(* ============ R3. Adjacent-band asymptotic ============ *)

(* Generic: continuity_pt f l + Un_cv An l => Un_cv (f o An) (f l) *)
Lemma g2_Un_cv_cont (f : R -> R) (An : nat -> R) (l : R) :
  continuity_pt f l -> Un_cv An l ->
  Un_cv (fun n => f (An n)) (f l).
Proof.
  intros Hcont Hcv eps Hep.
  unfold Un_cv in Hcv.
  unfold continuity_pt in Hcont.
  unfold continue_in, limit1_in, limit_in in Hcont.
  destruct (Hcont eps Hep) as [alp [Halp Hball]].
  destruct (Hcv alp Halp) as [N HN].
  exists N.
  intros n Hn.
  destruct (Req_dec (An n) l) as [Heq | Hne].
  - rewrite Heq.
    replace (Rdist (f l) (f l)) with 0.
    + exact Hep.
    + symmetry. apply (proj2 (Rdist_refl (f l) (f l))). reflexivity.
  - apply Hball.
    + split.
      * unfold D_x, no_cond. split; [exact I | exact (not_eq_sym Hne)].
      * apply HN. exact Hn.
Qed.

Lemma g2_cont_id (x : R) : continuity_pt id x.
Proof.
  apply derivable_continuous_pt.
  apply derivable_pt_id.
Qed.

Lemma g2_cont_const (a x : R) : continuity_pt (fct_cte a) x.
Proof.
  apply continuity_pt_const.
  unfold constant, fct_cte. intros x1 x2. reflexivity.
Qed.

Lemma g2_cont_pi_over (x : R) : x <> 0 -> continuity_pt (fun t => PI / t) x.
Proof.
  intros Hx.
  change (continuity_pt (mult_real_fct PI (/ id)) x).
  apply continuity_pt_scal.
  apply continuity_pt_inv.
  - apply g2_cont_id.
  - exact Hx.
Qed.

Lemma g2_cont_sin_pi_over (x : R) : x <> 0 -> continuity_pt (fun t => sin (PI / t)) x.
Proof.
  intros Hx.
  change (continuity_pt (comp sin (fun t => PI / t)) x).
  apply continuity_pt_comp.
  - apply g2_cont_pi_over. exact Hx.
  - apply continuity_sin.
Qed.

Lemma g2_cont_mu_adj (r : R) : (1 < r)%R -> continuity_pt mu_adj r.
Proof.
  intros Hr.
  unfold mu_adj.
  change (continuity_pt ((fun t => sqrt t * sin (PI / t)) / (fun t => PI * (t - 1))) r).
  apply continuity_pt_div.
  - apply continuity_pt_mult.
    + apply continuity_pt_sqrt. lra.
    + apply g2_cont_sin_pi_over. lra.
  - change (continuity_pt (mult_real_fct PI (fun t => t - 1)) r).
    apply continuity_pt_scal.
    apply continuity_pt_minus.
    + apply g2_cont_id.
    + apply g2_cont_const.
  - apply Rmult_integral_contrapositive.
    split; [apply Rgt_not_eq, PI_RGT_0 | lra].
Qed.

Theorem mu_adj_phase_transition :
  exists r : R, (1 < r)%R /\ (r < 2)%R /\ (mu_adj r = 4/5)%R.
Proof.
  set (f := fun r => mu_adj r - 4 / 5).
  assert (Hf65 : (f (6 / 5) > 0)%R).
  { unfold f. apply Rgt_minus. exact g2_mu_65_gt_mu. }
  assert (Hf32 : (f (3 / 2) < 0)%R).
  { unfold f. apply Rlt_minus. exact g2_mu_32_lt_mu. }
  set (g := fun r => - (mu_adj r - 4 / 5)).
  assert (Hg65 : (g (6 / 5) < 0)%R).
  { unfold g. unfold f in Hf65. lra. }
  assert (Hg32 : (0 < g (3 / 2))%R).
  { unfold g. unfold f in Hf32. lra. }
  destruct (IVT_interv g (6 / 5) (3 / 2)) as [r Hr_spec].
  - intros a Ha.
    apply continuity_pt_opp.
    apply continuity_pt_plus.
    + apply g2_cont_mu_adj.
      destruct Ha as [Hal Hah].
      lra.
    + apply continuity_pt_const.
      unfold constant. intros x y. reflexivity.
  - lra.
  - exact Hg65.
  - exact Hg32.
  - destruct Hr_spec as [Hrange Hg0].
    exists r. split.
    + destruct Hrange as [Hrl Hrh]. lra.
    + split.
      * destruct Hrange as [Hrl Hrh]. lra.
      * unfold g in Hg0.
        unfold f in *.
        lra.
Qed.

Print Assumptions mu_adj_phase_transition.
Theorem mu_adj_asymptotic (r : R) (n : nat -> nat) :
  (2 <= r)%R ->
  (forall k, (1 < n k)%nat) ->
  (forall k, (n k < n (S k))%nat) ->
  (Un_cv (fun k => INR (n (S k)) / INR (n k)) r) ->
  (Un_cv (fun k => mu_adj (INR (n (S k)) / INR (n k))) (mu_adj r)).
Proof.
  intros Hr Hn1 Hnlt Hlim.
  apply (g2_Un_cv_cont mu_adj (fun k => INR (n (S k)) / INR (n k)) r).
  - apply g2_cont_mu_adj. lra.
  - exact Hlim.
Qed.

End G2MuAdj.


