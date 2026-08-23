(* ============================================================
   U4 T-PARTIAL 探针：Dirichlet 部分和界（z 工作区，E039 纪律）
   主定理 dirichlet_partial_bound：N≥2，j mod N ≠ 0，r := j mod N，
   s := min r (N−r)：
     Cnorm (Csum (fun k => grid_atom N j k) W) ≤ INR N / (2 * INR s)
   ——窗口 W 无关（任意部分和统一界）。
   证明设计（消 sin 的 π-回绕）：mod 归约 → WLOG 共轭对称
   （|Σ_{N−r}| = |Σ_r|，无需 sin(π−x)）→ 半带情形 jordan 直接下界。
   引擎：Cnorm_one_minus_exp_i_theta_eq（ca_basis_lemmas:1089）+
        jordan_standard（:1783）。
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
Require Import probe_parseval.
Import ComplexNumbers.
Import FourierAnalysis.
Import GridOrtho.
Import TParseval.

Open Scope R_scope.
Open Scope complex_scope.
Open Scope nat_scope.

Module TPartial.

(* ---------- 基础件 ---------- *)

Lemma i_split (x y : R) : (0 +i (x + y)) = (0 +i x) +c (0 +i y).
Proof. unfold Cadd. apply Complex_eq; simpl; ring. Qed.

Lemma Csub_diag (z : Complex) : z -c z = C0.
Proof. unfold Csub, C0. apply Complex_eq; simpl; ring. Qed.

(* (C1 −c a) *c b = b −c a *c b *)
Lemma Csub_distr (a b : Complex) : (C1 -c a) *c b = b -c (a *c b).
Proof. unfold Csub, Cmul, Cadd, C1. apply Complex_eq; simpl; ring. Qed.

Lemma Cexp_2pi_shift (x : R) (n : Z) :
  Cexp (0 +i (x + 2 * PI * IZR n)) = Cexp (0 +i x).
Proof.
  replace (0 +i (x + 2 * PI * IZR n)) with ((0 +i x) +c (0 +i (2 * PI * IZR n)))
    by (rewrite <- i_split; reflexivity).
  rewrite Cexp_add Cexp_2PI_int.
  rewrite Cmul_1_r. reflexivity.
Qed.

Lemma Cnorm_mult' (z1 z2 : Complex) :
  (Cnorm (z1 *c z2))%R = ((Cnorm z1) * (Cnorm z2))%R.
Proof.
  unfold Cnorm. rewrite Cnorm_sq_mult.
  apply (sqrt_mult (Cnorm_sq z1) (Cnorm_sq z2)); apply Cnorm_sq_ge_0.
Qed.

Lemma Cnorm_one' : (Cnorm C1)%R = 1%R.
Proof. unfold Cnorm. rewrite Cnorm_sq_one. rewrite sqrt_1. reflexivity. Qed.

Lemma rot_atom_one (theta : R) : rot_atom theta 1 = Cexp (0 +i theta).
Proof. unfold rot_atom. rewrite INR_1 Rmult_1_l. reflexivity. Qed.

Lemma rot_atom_zero (theta : R) : rot_atom theta 0 = C1.
Proof. unfold rot_atom. rewrite INR_0 Rmult_0_l. apply Cexp_0. Qed.

Lemma rot_step (theta : R) (W : nat) :
  rot_atom theta (S W) = rot_atom theta W *c rot_atom theta 1.
Proof. rewrite -addn1. apply rot_atom_lag_add. Qed.

(* ---------- Csum 共轭与 Cnorm 共轭 ---------- *)

Lemma Cconj_C0 : Cconj C0 = C0.
Proof. unfold Cconj, C0. apply Complex_eq; simpl; ring. Qed.

Lemma Csum_conj (f : nat -> Complex) (n : nat) :
  PrimeEmbedding.Csum (fun k => Cconj (f k)) n = Cconj (PrimeEmbedding.Csum f n).
Proof.
  induction n as [| n IH].
  - simpl. rewrite Cconj_C0. reflexivity.
  - assert (Hc : PrimeEmbedding.Csum (fun k => Cconj (f k)) (S n)
                 = Cadd (Cconj (f n)) (PrimeEmbedding.Csum (fun k => Cconj (f k)) n))
      by reflexivity.
    assert (Hc2 : PrimeEmbedding.Csum f (S n)
                  = Cadd (f n) (PrimeEmbedding.Csum f n)) by reflexivity.
    rewrite Hc IH Hc2.
    unfold Cadd, Cconj. apply Complex_eq; simpl; ring.
Qed.

Lemma Cnorm_conj (z : Complex) : (Cnorm (Cconj z))%R = (Cnorm z)%R.
Proof. unfold Cnorm. rewrite Cnorm_sq_conj. reflexivity. Qed.

(* ---------- 2D Cauchy-Schwarz 与 Cnorm 三角不等式 ---------- *)

Lemma square_ge_0 (x : R) : ((0 <= x * x))%R.
Proof.
  destruct (Rle_or_lt 0 x) as [H | H].
  - apply (Rle_trans _ (x * 0)%R).
    + replace ((x * 0))%R with 0%R by ring. apply Rle_refl.
    + apply (Rmult_le_compat_l x 0 x); [exact H | exact H].
  - replace ((x * x))%R with ((-x) * (-x))%R by ring.
    assert (Hm : (0 <= -x)%R) by lra.
    apply (Rle_trans _ ((-x) * 0)%R).
    + replace (((-x) * 0))%R with 0%R by ring. apply Rle_refl.
    + apply (Rmult_le_compat_l (-x) 0 (-x)); [exact Hm | exact Hm].
Qed.

Lemma cs2 (a1 b1 a2 b2 : R) :
  (((a1*a2 + b1*b2) * (a1*a2 + b1*b2) <= (a1*a1 + b1*b1) * (a2*a2 + b2*b2))%R).
Proof.
  assert (Hd : (((a1*a1 + b1*b1) * (a2*a2 + b2*b2) - (a1*a2 + b1*b2) * (a1*a2 + b1*b2)) = ((a1*b2 - a2*b1) * (a1*b2 - a2*b1)))%R) by ring.
  assert (Hsq : ((0 <= (a1*b2 - a2*b1) * (a1*b2 - a2*b1)))%R).
  { apply square_ge_0. }
  apply (Rle_trans _ ((a1*a2 + b1*b2) * (a1*a2 + b1*b2) + (a1*b2 - a2*b1) * (a1*b2 - a2*b1))%R).
  - nra.
  - rewrite <- Hd. nra.
Qed.

Lemma sqrt_pos' (x : R) : (0 <= x)%R -> (0 <= sqrt x)%R.
Proof. intros H. apply sqrt_positivity. exact H. Qed.

Lemma sqrt_sq (x : R) : (0 <= x)%R -> ((sqrt x * sqrt x)%R = x)%R.
Proof. intros H. assert (HR := Rsqr_sqrt x H). unfold Rsqr in HR. exact HR. Qed.

(* 平方比较传递 *)
Lemma le_from_sq (a b : R) :
  ((0 <= a)%R -> ((0 <= b)%R) -> ((a * a <= b * b)%R -> ((a <= b)%R))).
Proof.
  intros Ha Hb Hsq.
  destruct (Rle_or_lt a b) as [Hle | Hlt]; [exact Hle | ].
  exfalso.
  assert (Hsq2 : (b * b <= a * a)%R) by nra.
  nra.
Qed.

(* 点积绝对值 ≤ 范数积 *)
Lemma re_dot_abs_le (z1 z2 : Complex) :
  (Rabs ((re z1) * (re z2) + (im z1) * (im z2)) <= (Cnorm z1) * (Cnorm z2))%R.
Proof.
  assert (Hn1 : (0 <= Cnorm z1)%R)
    by (unfold Cnorm; apply sqrt_pos'; apply Cnorm_sq_ge_0).
  assert (Hn2 : (0 <= Cnorm z2)%R)
    by (unfold Cnorm; apply sqrt_pos'; apply Cnorm_sq_ge_0).
  assert (Huv : (0 <= (Cnorm z1) * (Cnorm z2))%R) by nra.
  assert (Hs1 : ((Cnorm z1) * (Cnorm z1))%R = (Cnorm_sq z1)%R)
    by (unfold Cnorm; apply sqrt_sq; apply Cnorm_sq_ge_0).
  assert (Hs2 : ((Cnorm z2) * (Cnorm z2))%R = (Cnorm_sq z2)%R)
    by (unfold Cnorm; apply sqrt_sq; apply Cnorm_sq_ge_0).
  assert (Hkey : ((((Cnorm z1) * (Cnorm z2)) * ((Cnorm z1) * (Cnorm z2))) = ((Cnorm_sq z1) * (Cnorm_sq z2)))%R)
    by (rewrite <- Hs1; rewrite <- Hs2; ring).
  assert (Hcs : (((re z1) * (re z2) + (im z1) * (im z2)) * ((re z1) * (re z2) + (im z1) * (im z2))
             <= (Cnorm_sq z1) * (Cnorm_sq z2))%R)
    by (apply cs2).
  rewrite <- Hkey in Hcs.
  destruct (Rle_or_lt 0 ((re z1) * (re z2) + (im z1) * (im z2))) as [Hpos | Hneg].
  - assert (Hpos' : ((re z1) * (re z2) + (im z1) * (im z2) >= 0)%R) by lra.
    rewrite (Rabs_right _ Hpos').
    apply (le_from_sq ((re z1) * (re z2) + (im z1) * (im z2)) ((Cnorm z1) * (Cnorm z2)));
      [exact Hpos | exact Huv | exact Hcs].
  - rewrite (Rabs_left _ Hneg).
    apply (le_from_sq (- ((re z1) * (re z2) + (im z1) * (im z2))) ((Cnorm z1) * (Cnorm z2))).
    + lra.
    + exact Huv.
    + replace ((- ((re z1) * (re z2) + (im z1) * (im z2))) * (- ((re z1) * (re z2) + (im z1) * (im z2))))%R
        with (((re z1) * (re z2) + (im z1) * (im z2)) * ((re z1) * (re z2) + (im z1) * (im z2)))%R
        by ring.
      exact Hcs.
Qed.

Lemma Cnorm_add_le (z1 z2 : Complex) :
  (Cnorm (z1 +c z2) <= (Cnorm z1) + (Cnorm z2))%R.
Proof.
  assert (Hn1 : (0 <= Cnorm z1)%R) by (unfold Cnorm; apply sqrt_pos'; apply Cnorm_sq_ge_0).
  assert (Hn2 : (0 <= Cnorm z2)%R) by (unfold Cnorm; apply sqrt_pos'; apply Cnorm_sq_ge_0).
  assert (Hs0 : (0 <= Cnorm_sq (z1 +c z2))%R) by apply Cnorm_sq_ge_0.
  assert (Hsx : ((Cnorm (z1 +c z2)) * (Cnorm (z1 +c z2)))%R = (Cnorm_sq (z1 +c z2))%R)
    by (unfold Cnorm; apply sqrt_sq; exact Hs0).
  assert (Hs1 : ((Cnorm z1) * (Cnorm z1))%R = (Cnorm_sq z1)%R)
    by (unfold Cnorm; apply sqrt_sq; apply Cnorm_sq_ge_0).
  assert (Hs2 : ((Cnorm z2) * (Cnorm z2))%R = (Cnorm_sq z2)%R)
    by (unfold Cnorm; apply sqrt_sq; apply Cnorm_sq_ge_0).
  assert (Huv : (0 <= (Cnorm z1) * (Cnorm z2))%R) by nra.
  assert (Hd : (((re z1) * (re z2) + (im z1) * (im z2)) <= ((Cnorm z1) * (Cnorm z2)))%R).
  { destruct (Rle_or_lt 0 ((re z1) * (re z2) + (im z1) * (im z2))) as [Hp | Hn].
    - assert (HA := re_dot_abs_le z1 z2).
      assert (Hp' : ((re z1) * (re z2) + (im z1) * (im z2) >= 0)%R) by lra.
      rewrite (Rabs_right _ Hp') in HA. exact HA.
    - nra. }
  assert (Hadd := Cnorm_sq_add z1 z2).
  unfold Cnorm.
  apply (le_from_sq (sqrt (Cnorm_sq (z1 +c z2))) ((Cnorm z1) + (Cnorm z2))).
  - apply sqrt_pos'. apply Cnorm_sq_ge_0.
  - lra.
  - rewrite (sqrt_sq (Cnorm_sq (z1 +c z2)) (Cnorm_sq_ge_0 (z1 +c z2))).
    rewrite Hadd.
    replace (((Cnorm z1) + (Cnorm z2)) * ((Cnorm z1) + (Cnorm z2)))%R
      with (((Cnorm_sq z1) + (Cnorm_sq z2) + 2 * ((Cnorm z1) * (Cnorm z2))))%R
      by (rewrite <- Hs1; rewrite <- Hs2; ring).
    nra.
Qed.

Lemma Cnorm_sub_le (z1 z2 : Complex) :
  (Cnorm (z1 -c z2) <= (Cnorm z1) + (Cnorm z2))%R.
Proof.
  assert (Hn1 : (0 <= Cnorm z1)%R) by (unfold Cnorm; apply sqrt_pos'; apply Cnorm_sq_ge_0).
  assert (Hn2 : (0 <= Cnorm z2)%R) by (unfold Cnorm; apply sqrt_pos'; apply Cnorm_sq_ge_0).
  assert (Hs0 : (0 <= Cnorm_sq (z1 -c z2))%R) by apply Cnorm_sq_ge_0.
  assert (Hsx : ((Cnorm (z1 -c z2)) * (Cnorm (z1 -c z2)))%R = (Cnorm_sq (z1 -c z2))%R)
    by (unfold Cnorm; apply sqrt_sq; exact Hs0).
  assert (Hs1 : ((Cnorm z1) * (Cnorm z1))%R = (Cnorm_sq z1)%R)
    by (unfold Cnorm; apply sqrt_sq; apply Cnorm_sq_ge_0).
  assert (Hs2 : ((Cnorm z2) * (Cnorm z2))%R = (Cnorm_sq z2)%R)
    by (unfold Cnorm; apply sqrt_sq; apply Cnorm_sq_ge_0).
  assert (HA := re_dot_abs_le z1 z2).
  assert (Hsub : (Cnorm_sq (z1 -c z2))%R
                 = ((Cnorm_sq z1) + (Cnorm_sq z2)
                    - 2 * ((re z1) * (re z2) + (im z1) * (im z2)))%R).
  { unfold Cnorm_sq, Csub. simpl. unfold Rsqr. ring. }
  assert (Hnd : (- ((re z1) * (re z2) + (im z1) * (im z2)) <= (Cnorm z1) * (Cnorm z2))%R).
  { destruct (Rle_or_lt 0 ((re z1) * (re z2) + (im z1) * (im z2))) as [Hp2 | Hn2'].
    - nra.
    - rewrite (Rabs_left _ Hn2') in HA. exact HA. }
  unfold Cnorm.
  apply (le_from_sq (sqrt (Cnorm_sq (z1 -c z2))) ((Cnorm z1) + (Cnorm z2))).
  - apply sqrt_pos'. apply Cnorm_sq_ge_0.
  - lra.
  - rewrite (sqrt_sq (Cnorm_sq (z1 -c z2)) (Cnorm_sq_ge_0 (z1 -c z2))).
    rewrite Hsub.
    replace (((Cnorm z1) + (Cnorm z2)) * ((Cnorm z1) + (Cnorm z2)))%R
      with (((Cnorm_sq z1) + (Cnorm_sq z2) + 2 * ((Cnorm z1) * (Cnorm z2))))%R
      by (rewrite <- Hs1; rewrite <- Hs2; ring).
    nra.
Qed.

(* ---------- 几何和恒等式 ---------- *)

Theorem geom_sum_identity (theta : R) (W : nat) :
  (C1 -c rot_atom theta W)
  = (C1 -c rot_atom theta 1) *c PrimeEmbedding.Csum (fun k => rot_atom theta k) W.
Proof.
  induction W as [| W IH].
  - simpl. rewrite rot_atom_zero Csub_diag Cmul_0_r. reflexivity.
  - assert (Hc : PrimeEmbedding.Csum (fun k => rot_atom theta k) (S W)
                 = Cadd (rot_atom theta W) (PrimeEmbedding.Csum (fun k => rot_atom theta k) W))
      by reflexivity.
    rewrite Hc. rewrite Cmul_add_distr_l. rewrite <- IH.
    rewrite Csub_distr (rot_step theta W).
    unfold Cadd, Csub. apply Complex_eq; simpl; ring.
Qed.

(* ---------- sin 下界（Jordan，半带情形） ---------- *)

Lemma INR_two : (INR 2)%R = 2%R.
Proof. simpl. ring. Qed.

Lemma sin_lower (N r : nat) :
  (1 <= r)%nat -> (2 * r <= N)%nat ->
  ((2 * INR r / INR N <= sin (PI * INR r / INR N))%R).
Proof.
  intros Hr H2r.
  assert (HNz : (0 < INR N)%R).
  { apply lt_0_INR.
    move: H2r => /leP H2rle.
    (* H2rle : ((2 * r)%coq_nat <= N)%coq_nat；由 Hr 得 0 < (2*r)%coq_nat *)
    apply (Nat.lt_le_trans 0 (2 * r)%coq_nat N).
    - (* 0 < (2 * r)%coq_nat：stdlib 记法，lia 可处理 *)
      move: Hr => /leP Hrle.
      lia.
    - exact H2rle. }
  assert (HPI : (0 < PI)%R) by apply PI_RGT_0.
  assert (Hx1 : (0 < PI * INR r / INR N)%R).
  { unfold Rdiv. apply Rmult_lt_0_compat.
    - apply Rmult_lt_0_compat; [exact HPI | apply lt_0_INR; move: Hr => /leP Hrle; lia].
    - apply Rinv_0_lt_compat. exact HNz. }
  assert (HIN : (INR (2 * r) <= INR N)%R) by (apply (le_INR (2 * r) N); move: H2r => /leP H2rle; lia).
  assert (Hx2 : (PI * INR r / INR N <= PI / 2)%R).
  { assert (HIN' : ((2 * INR r) <= INR N)%R)
      by (rewrite <- INR_two; rewrite <- (mult_INR 2 r); apply (le_INR (2 * r) N); move: H2r => /leP H2rle; lia).
    apply (Rmult_le_reg_r (INR N) (PI * INR r / INR N) (PI / 2) HNz).
    replace ((PI * INR r / INR N) * INR N)%R with (PI * INR r)%R by (field; lra).
    replace ((PI / 2) * INR N)%R with ((PI * INR N) / 2)%R by (field; lra).
    nra. }
  assert (Hj' : (((2 / PI) * (PI * INR r / INR N)) <= sin (PI * INR r / INR N))%R).
  { assert (H := jordan_standard (PI * INR r / INR N) (conj (Rlt_le _ _ Hx1) Hx2)). lra. }
  rewrite <- Hj'.
  replace ((2 / PI) * (PI * INR r / INR N))%R with ((2 * INR r / INR N))%R
    by (field; lra).
  apply Rle_refl.
Qed.


(* ---------- mod 归约 ---------- *)

Lemma grid_mod_reduce (N j k : nat) :
  (2 <= N)%nat ->
  (grid_atom N j k = grid_atom N (j mod N)%nat k).
Proof.
  intros HN.
  assert (HNz : (0 < INR N)%R).
  { apply lt_0_INR. move: HN => /leP HNle. lia. }
  assert (Hdj : (j = N * (j / N) + j mod N)%nat) by (apply Nat.div_mod_eq).
  assert (Hjk : (j * k = ((j / N) * k) * N + (j mod N) * k)%nat)
    by (rewrite {1}Hdj; rewrite mulnDl; rewrite -mulnA; rewrite mulnC; reflexivity).
  unfold grid_atom.
  assert (Hval : (2 * PI * INR (j * k) / INR N)%R
    = ((2 * PI * INR ((j mod N) * k) / INR N)
       + 2 * PI * IZR (Z.of_nat ((j / N) * k)))%R).
  { rewrite <- (INR_IZR_INZ ((j / N) * k)). rewrite Hjk. rewrite plus_INR. rewrite !mult_INR.
    field. apply Rgt_not_eq. exact HNz. }
  rewrite Hval. apply Cexp_2pi_shift.
Qed.

(* ---------- 共轭对称 ---------- *)

Lemma grid_conj (N r k : nat) :
  (2 <= N)%nat -> (0 < r)%nat -> (r < N)%nat ->
  (grid_atom N (N - r) k = Cconj (grid_atom N r k)).
Proof.
  intros HN Hr HrN.
  assert (HNz : (0 < INR N)%R).
  { apply lt_0_INR. move: HN => /leP HNle. lia. }
  assert (Hsub : ((N - r) * k = N * k - r * k)%nat) by (rewrite mulnBl; reflexivity).
  unfold grid_atom.
  rewrite Hsub.
  assert (Hval : (2 * PI * INR (N * k - r * k) / INR N)%R
    = ((-(2 * PI * INR (r * k) / INR N)) + 2 * PI * IZR (Z.of_nat k))%R).
  { rewrite <- (INR_IZR_INZ k). rewrite minus_INR. rewrite !mult_INR.
    field. apply Rgt_not_eq; exact HNz.
    (* minus_INR 前提：r*k <= N*k（r < N ⟹ r <= N ⟹ 乘 k 保序） *)
    move: HrN => /ltP HrNp.
    apply Nat.mul_le_mono_r. lia. }
  rewrite Hval (Cconj_Cexp (2 * PI * INR (r * k) / INR N)).
  apply Cexp_2pi_shift.
Qed.

(* ---------- 主界（半带情形） ---------- *)

Theorem partial_bound_half (N r W : nat) :
  (2 <= N)%nat -> (1 <= r)%nat -> (2 * r <= N)%nat ->
  ((Cnorm (PrimeEmbedding.Csum (fun k => grid_atom N r k) W) <= INR N / (2 * INR r))%R).
Proof.
  intros HN Hr H2r.
  assert (HNz : (0 < INR N)%R).
  { apply lt_0_INR. move: HN => /leP HNle. lia. }
  assert (Hrz : (0 < INR r)%R).
  { apply lt_0_INR. move: Hr => /leP Hrle. lia. }
  assert (Hconv : PrimeEmbedding.Csum (fun k => grid_atom N r k) W
                  = PrimeEmbedding.Csum (fun k => rot_atom (2 * PI * INR r / INR N) k) W).
  { apply Csum_ext. intros k Hk. symmetry. apply rot_grid. exact HN. }
  rewrite Hconv.
  set (theta := ((2 * PI * INR r / INR N))%R).
  assert (Hid := geom_sum_identity theta W).
  assert (Hnorm : (Cnorm (C1 -c rot_atom theta W))%R
                  = ((Cnorm (C1 -c rot_atom theta 1))
                     * (Cnorm (PrimeEmbedding.Csum (fun k => rot_atom theta k) W)))%R).
  { rewrite {1}Hid. rewrite Cnorm_mult'. reflexivity. }
  assert (Hub : (Cnorm (C1 -c rot_atom theta W) <= 2)%R).
  { apply (Rle_trans _ ((Cnorm C1) + (Cnorm (rot_atom theta W)))%R).
    - apply Cnorm_sub_le.
    - rewrite Cnorm_one' (rot_Cnorm theta W). lra. }
  assert (Hlb : ((4 * INR r / INR N <= Cnorm (C1 -c rot_atom theta 1))%R)).
  { rewrite rot_atom_one (Cnorm_one_minus_exp_i_theta_eq theta).
    assert (Hhalf : ((theta / 2))%R = ((PI * INR r / INR N))%R)
      by (unfold theta; field; lra).
    rewrite Hhalf.
    assert (Hsinpos : (0 <= sin (PI * INR r / INR N))%R).
    { assert (Hsl := sin_lower N r Hr H2r).
      assert (Hpos2 : (0 < 2 * INR r / INR N)%R).
      { unfold Rdiv. apply Rmult_lt_0_compat.
        - lra.
        - apply Rinv_0_lt_compat. exact HNz. }
      nra. }
    assert (Hge : (2 * sin (PI * INR r / INR N) <= 2 * Rabs (sin (PI * INR r / INR N)))%R).
    { apply Rmult_le_compat_l; [lra | ].
      destruct (Rle_or_lt 0 (sin (PI * INR r / INR N))) as [Hs | Hs].
      - rewrite (Rabs_right _ (Rle_ge 0 (sin (PI * INR r / INR N)) Hs)). apply Rle_refl.
      - rewrite (Rabs_left _ Hs). lra. }
    assert (Hsl := sin_lower N r Hr H2r).
    replace ((4 * INR r / INR N))%R with ((2 * (2 * INR r / INR N)))%R by (field; lra).
    nra. }
  apply (Rmult_le_reg_l (2 * INR r)); [nra | ].
  replace ((2 * INR r) * (INR N / (2 * INR r)))%R with (INR N)%R
    by (field; lra).
  set (XX := (Cnorm (PrimeEmbedding.Csum (fun k => rot_atom theta k) W))%R) in *.
  assert (HX : (0 <= XX)%R)
    by (unfold XX, Cnorm; apply sqrt_pos'; apply Cnorm_sq_ge_0).
  assert (H1 : ((4 * INR r / INR N) * XX <= Cnorm (C1 -c rot_atom theta 1) * XX)%R)
    by (apply Rmult_le_compat_r; [exact HX | exact Hlb]).
  rewrite <- Hnorm in H1.
  assert (H2 : ((4 * INR r / INR N) * XX <= 2)%R)
    by (apply (Rle_trans _ (Cnorm (C1 -c rot_atom theta W))); [exact H1 | exact Hub]).
  assert (H3 : ((4 * INR r) * XX <= 2 * INR N)%R).
  { replace ((4 * INR r) * XX)%R with ((4 * INR r / INR N) * XX * INR N)%R
      by (field; lra).
    apply Rmult_le_compat_r; [apply Rlt_le; exact HNz | exact H2]. }
  assert (Hr4 : ((4 * INR r) * XX)%R = (2 * ((2 * INR r) * XX))%R) by ring.
  nra.
Qed.

(* ---------- 主定理 ---------- *)

Theorem dirichlet_partial_bound (N j W : nat) :
  (2 <= N)%nat -> (j mod N <> 0)%nat ->
  ((Cnorm (PrimeEmbedding.Csum (fun k => grid_atom N j k) W)
    <= INR N / (2 * INR (Nat.min (j mod N) ((N - j mod N)%coq_nat))))%R).
Proof.
  intros HN Hneq.
  assert (Hr0 : (0 < j mod N)%nat).
  { destruct (j mod N) as [| r']; [exfalso; apply Hneq; reflexivity | exact (ltn0Sn r')]. }
  assert (HrN : (j mod N < N)%nat).
  { apply/ltP. apply Nat.mod_upper_bound. move: HN => /leP HNle. lia. }
  assert (Hconv : PrimeEmbedding.Csum (fun k => grid_atom N j k) W
                  = PrimeEmbedding.Csum (fun k => grid_atom N (j mod N) k) W).
  { apply Csum_ext. intros k Hk. apply grid_mod_reduce. exact HN. }
  rewrite Hconv.
  (* 目标含 Nat.min（stdlib），Hle/Hgt 由 leqP 给 bool——用 leP 反映 *)
  case: (leqP (j mod N) (N - j mod N)) => [Hle | Hgt].
  - have HleP : ((j mod N) <= (N - j mod N))%coq_nat.
    { apply/leP. exact Hle. }
    rewrite (Nat.min_l _ _ HleP).
    have Hle2 : (2 * (j mod N) <= N)%nat.
    { rewrite mul2n.
      have Hle3 : (j mod N) + (j mod N) <= (j mod N) + (N - j mod N)
        by rewrite (addnC (j mod N) (N - j mod N)); exact (leq_add Hle (leqnn (j mod N))).
      have Hsub : (j mod N) <= N by exact (leq_trans Hle (leq_subr (j mod N) N)).
      rewrite (subnKC Hsub) in Hle3. rewrite addnn in Hle3. exact Hle3. }
    apply partial_bound_half; [exact HN | exact Hr0 | exact Hle2].
  - have HgeP : ((N - j mod N) <= (j mod N))%coq_nat.
    { apply/leP. exact (ltnW Hgt). }
    rewrite (Nat.min_r _ _ HgeP).
    assert (Hcs : (Cnorm (PrimeEmbedding.Csum (fun k => grid_atom N (j mod N) k) W))%R
                  = (Cnorm (PrimeEmbedding.Csum (fun k => grid_atom N (N - j mod N) k) W))%R).
    { rewrite <- (Cnorm_conj (PrimeEmbedding.Csum (fun k => grid_atom N (j mod N) k) W)).
      rewrite <- Csum_conj.
      f_equal.
      apply Csum_ext. intros k Hk. symmetry.
      apply grid_conj; [exact HN | exact Hr0 | exact HrN]. }
    rewrite Hcs.
    have Hd2 : (2 * (N - j mod N) <= N)%nat.
    { rewrite mul2n.
      have Hn : (N - j mod N) + (N - j mod N) <= (j mod N) + (N - j mod N)
        by exact (leq_add (ltnW Hgt) (leqnn (N - j mod N))).
      rewrite (subnKC (m := j mod N) (n := N) (ltnW HrN)) in Hn. rewrite addnn in Hn. exact Hn. }
    apply partial_bound_half; [exact HN | rewrite subn_gt0; exact HrN | exact Hd2].
Qed.

End TPartial.

(* ---------- 构造性审计 ---------- *)

Print Assumptions TPartial.geom_sum_identity.
Print Assumptions TPartial.partial_bound_half.
Print Assumptions TPartial.dirichlet_partial_bound.
