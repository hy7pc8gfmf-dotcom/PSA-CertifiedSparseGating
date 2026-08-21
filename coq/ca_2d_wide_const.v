(* ============================================================
   库 ca_2d_wide_const（会话 15 新增 · 2D-wide 常数层）
   2D-wide 全覆盖版前置模块①：常数引理 + min4 + 纯量分解。
   依赖：ca_decay 等（同 ca_basis_3d 前件）。
   独立编译：coqc -Q src "" -Q mathcomp mathcomp -Q Coquelicot Coquelicot <本文件>
   零 Admitted、零活动 Axiom、零 classic。
   ============================================================ *)
Require Import Stdlib.Reals.Reals.
Require Import Stdlib.Lists.List.
Require Import Stdlib.Sorting.Sorted.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.micromega.Lra.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Arith.Peano_dec.
Require Import ca_base.
Require Import ca_basis.
Require Import ca_basis_lemmas.
Require Import ca_char_ortho.
Require Import ca_complex_analysis.
Require Import ca_complex_foundation.
Require Import ca_independence.
Require Import ca_sparse_ext.
Require Import ca_decay.
Require Import ca_basis_3d.
Import ComplexNumbers.
Import ExtendedTheorems.
Import UnconditionalBasisLemmas.

Open Scope R_scope.

(* complex_eq_re_im / Cmul_shuffle 复用 ca_basis_3d 定义，防合并版重名冲突 *)


(* ============ 1. 常数引理：1 <= (Rmax 8 C³ / 2) * d_i * d_j（4 分支） ============ *)

Lemma Rmult_le_compat_right_mine_2d : forall c x y : R,
  0 <= c -> x <= y -> x * c <= y * c.
Proof.
  intros c x y Hc Hxy.
  replace (y * c) with (x * c + (y - x) * c) by ring.
  apply Rle_trans with (x * c + 0).
  - replace (x * c + 0) with (x * c) by ring. apply Rle_refl.
  - apply Rplus_le_compat; [apply Rle_refl |].
    apply Rmult_le_pos.
    + assert (Hyx : 0 <= y - x) by lra. exact Hyx.
    + exact Hc.
Qed.

Lemma Rmult_le_compat4_mine_2d : forall a b c d : R,
  0 <= a -> a <= b -> 0 <= c -> c <= d -> a * c <= b * d.
Proof.
  intros a b c d Ha Hab Hc Hcd.
  apply Rle_trans with (b * c).
  - apply Rmult_le_compat_right_mine_2d; [exact Hc | exact Hab].
  - replace (b * c) with (c * b) by ring.
    replace (b * d) with (d * b) by ring.
    apply Rmult_le_compat_right_mine_2d; [lra | exact Hcd].
Qed.

Lemma K0_mult_fin_2d : forall K t x : R,
  0 < x -> 0 < K -> 2 <= t -> x <= K -> 1 <= (K / 2) * (t / x).
Proof.
  intros K t x Hx HK Ht HxK.
  assert (Hkey : (K / 2) * (t / x) * x = (K / 2) * t).
  { field. apply Rgt_not_eq; exact Hx. }
  apply (Rmult_le_reg_r x 1 ((K / 2) * (t / x))); [exact Hx |].
  rewrite Hkey.
  replace (1 * x) with x by ring.
  apply Rle_trans with K; [exact HxK |].
  assert (Hkh : (K / 2) * 2 = K) by (unfold Rdiv; field).
  apply Rle_trans with ((K / 2) * 2).
  - rewrite Hkh. apply Rle_refl.
  - apply Rmult_le_compat4_mine_2d.
    + unfold Rdiv; apply Rmult_le_pos; [apply Rlt_le; exact HK | apply Rlt_le; lra].
    + apply Rle_refl.
    + apply Rlt_le; lra.
    + exact Ht.
Qed.

(* 2D 4 分支常数引理：两轴全不同 → 4；仅轴 1 不同 → 2；仅轴 2 不同 → 2；全同 → 排除（Hdiff） *)
Lemma one_le_half_K0_2dprod :
  forall (C : nat) (HCgt2 : (C > 2)%nat) (r : R) (Hr : r = sqrt (INR C))
    (i1 i2 j1 j2 : nat)
    (Hdiff : i1 <> i2 \/ j1 <> j2)
    (Hidx4 : (Z.abs_nat (Z.of_nat i1 - Z.of_nat i2) +
              Z.abs_nat (Z.of_nat j1 - Z.of_nat j2) <= 6)%nat),
  1%R <= (Rmax 8 (((INR C) ^ 3)%R) / 2) *
         (d_factor r i1 i2 * d_factor r j1 j2).
Proof.
  intros C HCgt2 r Hr i1 i2 j1 j2 Hdiff Hidx4.
  set (di := Z.abs_nat (Z.of_nat i1 - Z.of_nat i2)).
  set (dj := Z.abs_nat (Z.of_nat j1 - Z.of_nat j2)).
  assert (Hr_ge1 : 1 <= r).
  { rewrite Hr, <- sqrt_1.
    apply sqrt_le_1_c; [apply Rle_0_1 | apply pos_INR; lia
                        | change 1 with (INR 1); apply le_INR; lia]. }
  assert (Hr_pos : 0 < r) by lra.
  assert (HRmax_ge : 8 <= Rmax 8 (((INR C) ^ 3)%R)) by apply Rmax_l.
  assert (HRmax_nn : 0 <= Rmax 8 (((INR C) ^ 3)%R))
    by (apply Rle_trans with 8%R; [lra | exact HRmax_ge]).
  assert (HC3_le_Rmax : ((INR C) ^ 3)%R <= Rmax 8 (((INR C) ^ 3)%R)) by apply Rmax_r.
  assert (Hpowdtot_le : (r ^ (di + dj))%R <= ((INR C) ^ 3)%R).
  { apply Rle_trans with ((r ^ 6)%R)%R.
    - apply Rle_pow; [exact Hr_ge1 | lia].
    - rewrite Hr. rewrite (sqrt_pow_6 (INR C)) by (apply pos_INR; lia). apply Rle_refl. }
  assert (Hfin : (r ^ (di + dj))%R <= Rmax 8 (((INR C) ^ 3)%R))
    by (eapply Rle_trans; [exact Hpowdtot_le | exact HC3_le_Rmax]).
  assert (Hdf_neq : forall x y : nat, x <> y -> d_factor r x y = 2 / r ^ Z.abs_nat (Z.of_nat x - Z.of_nat y)).
  { intros x y Hxy. unfold d_factor.
    rewrite (proj2 (Nat.eqb_neq x y) Hxy). reflexivity. }
  destruct (Nat.eq_dec i1 i2) as [Heq_i | Hne_i].
  - (* 轴 1 同：仅轴 2 不同（Hdiff 排除双同） *)
    assert (Hdfi : d_factor r i1 i2 = 1) by (rewrite Heq_i; apply d_factor_diag).
    assert (Hdi0 : di = 0%nat) by (unfold di; rewrite <- Heq_i, Z.sub_diag; reflexivity).
    assert (Hne_j : j1 <> j2)
      by (destruct Hdiff as [H|H]; [contradiction (H Heq_i) | exact H]).
    rewrite Hdfi.
    assert (Hdfj : d_factor r j1 j2 = 2 / (r ^ dj)%R) by (apply Hdf_neq; exact Hne_j).
    rewrite Hdfj.
    assert (Hdt : (r ^ (di + dj))%R = (r ^ dj)%R)
      by (rewrite Hdi0; reflexivity).
    replace (1 * (2 / (r ^ dj)%R)) with (2 / r ^ (di + dj))
      by (rewrite <- Hdt; field; apply Rgt_not_eq; apply pow_lt; exact Hr_pos).
    apply (K0_mult_fin_2d (Rmax 8 (((INR C) ^ 3)%R)) 2 (r ^ (di + dj)));
      [apply pow_lt; exact Hr_pos
      |apply Rlt_le_trans with 8%R; [lra | exact HRmax_ge]
      |lra | exact Hfin].
  - (* 轴 1 不同 *)
    assert (Hdfi : d_factor r i1 i2 = 2 / (r ^ di)%R) by (apply Hdf_neq; exact Hne_i).
    rewrite Hdfi.
    destruct (Nat.eq_dec j1 j2) as [Heq_j | Hne_j].
    + (* 轴 2 同：仅轴 1 不同 → 2 *)
      assert (Hdfj : d_factor r j1 j2 = 1) by (rewrite Heq_j; apply d_factor_diag).
      assert (Hdj0 : dj = 0%nat) by (unfold dj; rewrite <- Heq_j, Z.sub_diag; reflexivity).
      rewrite Hdfj.
      assert (Hdt : (r ^ (di + dj))%R = (r ^ di)%R)
        by (rewrite Hdj0, Nat.add_0_r; reflexivity).
      replace ((2 / (r ^ di)%R) * 1) with (2 / r ^ (di + dj))
        by (rewrite <- Hdt; field; apply Rgt_not_eq; apply pow_lt; exact Hr_pos).
      apply (K0_mult_fin_2d (Rmax 8 (((INR C) ^ 3)%R)) 2 (r ^ (di + dj)));
        [apply pow_lt; exact Hr_pos
        |apply Rlt_le_trans with 8%R; [lra | exact HRmax_ge]
        |lra | exact Hfin].
    + (* 两轴全不同 → 4 *)
      assert (Hdfj : d_factor r j1 j2 = 2 / (r ^ dj)%R) by (apply Hdf_neq; exact Hne_j).
      rewrite Hdfj.
      assert (Hdt : (r ^ (di + dj))%R = (r ^ di)%R * (r ^ dj)%R)
        by (apply pow_add).
      replace ((2 / (r ^ di)%R) * (2 / (r ^ dj)%R)) with (4 / r ^ (di + dj))
        by (rewrite Hdt; field; repeat split; apply Rgt_not_eq; apply pow_lt; exact Hr_pos).
      apply (K0_mult_fin_2d (Rmax 8 (((INR C) ^ 3)%R)) 4 (r ^ (di + dj)));
        [apply pow_lt; exact Hr_pos
        |apply Rlt_le_trans with 8%R; [lra | exact HRmax_ge]
        |lra | exact Hfin].
Qed.

(* min 4 值析取：N0 = min(min a1 a2)(min b1 b2) 必取其一（Nat.min_spec 分层，防 lia 爆炸 E068） *)
Lemma min4_is_one : forall a1 a2 b1 b2 : nat,
  Nat.min (Nat.min a1 a2) (Nat.min b1 b2) = a1 \/
  Nat.min (Nat.min a1 a2) (Nat.min b1 b2) = a2 \/
  Nat.min (Nat.min a1 a2) (Nat.min b1 b2) = b1 \/
  Nat.min (Nat.min a1 a2) (Nat.min b1 b2) = b2.
Proof.
  intros a1 a2 b1 b2.
  destruct (Nat.min_spec (Nat.min a1 a2) (Nat.min b1 b2)) as [[_ H]|[_ H]]; rewrite H.
  - destruct (Nat.min_spec a1 a2) as [[_ H2]|[_ H2]]; rewrite H2.
    + left; reflexivity.
    + right; left; reflexivity.
  - destruct (Nat.min_spec b1 b2) as [[_ H3]|[_ H3]]; rewrite H3.
    + right; right; left; reflexivity.
    + right; right; right; reflexivity.
Qed.

(* N0 ≤ a1（Nat.min 链，防 lia 爆炸） *)
Lemma min4_le_a1 (a1 a2 b1 b2 : nat) :
  (Nat.min (Nat.min a1 a2) (Nat.min b1 b2) <= a1)%nat.
Proof.
  apply Nat.le_trans with (Nat.min a1 a2).
  - apply Nat.le_min_l.
  - apply Nat.le_min_l.
Qed.

(* N0 ≤ a2 *)
Lemma min4_le_a2 (a1 a2 b1 b2 : nat) :
  (Nat.min (Nat.min a1 a2) (Nat.min b1 b2) <= a2)%nat.
Proof.
  apply Nat.le_trans with (Nat.min a1 a2).
  - apply Nat.le_min_l.
  - apply Nat.le_min_r.
Qed.

(* N0 ≤ b1 *)
Lemma min4_le_b1 (a1 a2 b1 b2 : nat) :
  (Nat.min (Nat.min a1 a2) (Nat.min b1 b2) <= b1)%nat.
Proof.
  apply Nat.le_trans with (Nat.min b1 b2).
  - apply Nat.le_min_r.
  - apply Nat.le_min_l.
Qed.

(* N0 ≤ b2 *)
Lemma min4_le_b2 (a1 a2 b1 b2 : nat) :
  (Nat.min (Nat.min a1 a2) (Nat.min b1 b2) <= b2)%nat.
Proof.
  apply Nat.le_trans with (Nat.min b1 b2).
  - apply Nat.le_min_r.
  - apply Nat.le_min_r.
Qed.

(* 2D 纯量分解（任意上界 m；phi3D_inner_scalar_decomposition 的 2 轴对应） *)
Lemma phi2D_inner_scalar_decomposition :
  forall (a1 b1 a2 b2 : nat) (g : nat -> nat -> R) (m : nat),
    Csum (fun k => (Cof_real (/ g a1 b1) *c (psi a1 k *c psi b1 k)) *c
                  Cconj (Cof_real (/ g a2 b2) *c (psi a2 k *c psi b2 k))) m
    = Cof_real (/ g a1 b1 * / g a2 b2) *c
      Csum (fun k => (psi a1 k *c Cconj (psi a2 k)) *c
                     (psi b1 k *c Cconj (psi b2 k))) m.
Proof.
  intros a1 b1 a2 b2 g m.
  assert (HconjCof : Cconj (Cof_real (/ g a2 b2)) = Cof_real (/ g a2 b2))
    by (apply complex_eq_re_im; simpl; ring).
  assert (HCofmul : forall r1 r2 : R, Cof_real r1 *c Cof_real r2 = Cof_real (r1 * r2))
    by (intros r1 r2; apply complex_eq_re_im; simpl; ring).
  assert (Csum_scal_l : forall (c0 : Complex) (f0 : nat -> Complex) (n0 : nat),
    Csum (fun k => c0 *c f0 k) n0 = c0 *c Csum f0 n0).
  { intros c0 f0 n0. induction n0 as [|n0' IH]; simpl.
    - rewrite Cmul_0_r; reflexivity.
    - rewrite IH, Cmul_add_distr_l; reflexivity. }
  rewrite <- (Csum_scal_l (Cof_real (/ g a1 b1 * / g a2 b2))
                 (fun k => (psi a1 k *c Cconj (psi a2 k)) *c
                           (psi b1 k *c Cconj (psi b2 k))) m).
  apply Csum_ext'; intros k Hk.
  rewrite (Cconj_mul (Cof_real (/ g a2 b2))
                     (psi a2 k *c psi b2 k)).
  rewrite HconjCof.
  rewrite (Cconj_mul (psi a2 k) (psi b2 k)).
  rewrite (Cmul_shuffle (Cof_real (/ g a1 b1))
             (psi a1 k *c psi b1 k)
             (Cof_real (/ g a2 b2))
             (Cconj (psi a2 k) *c Cconj (psi b2 k))).
  rewrite (Cmul_shuffle (psi a1 k) (psi b1 k)
             (Cconj (psi a2 k)) (Cconj (psi b2 k))).
  rewrite HCofmul.
  reflexivity.
Qed.
