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
Import ComplexNumbers.
Import ExtendedTheorems.

Open Scope C_scope.

(* ---------------------------------------------------------------------------
   三维归一化常数：min3 / (a·b·c) 的平方根
   --------------------------------------------------------------------------- *)
Definition gamma3 (a b c : nat) : R :=
  sqrt (INR (Nat.min (Nat.min a b) c) / (INR a * INR b * INR c)).

Lemma gamma3_pos (a b c : nat) (Ha : (a >= 2)%nat) (Hb : (b >= 2)%nat) (Hc : (c >= 2)%nat) :
  0 < gamma3 a b c.
Proof.
  unfold gamma3.
  assert (Hmin_pos : (0 < Nat.min (Nat.min a b) c)%nat).
  { apply Nat.min_glb_lt; [| lia]. apply Nat.min_glb_lt; lia. }
  apply sqrt_lt_R0.
  apply Rdiv_lt_0_compat.
  - apply lt_0_INR; exact Hmin_pos.
  - assert (HaR : 0 < INR a) by (apply lt_0_INR; lia).
    assert (HbR : 0 < INR b) by (apply lt_0_INR; lia).
    assert (HcR : 0 < INR c) by (apply lt_0_INR; lia).
    apply Rmult_lt_0_compat; [| exact HcR].
    apply Rmult_lt_0_compat; [exact HaR | exact HbR].
Qed.

Lemma gamma3_sq (a b c : nat) (Ha : (a >= 2)%nat) (Hb : (b >= 2)%nat) (Hc : (c >= 2)%nat) :
  gamma3 a b c * gamma3 a b c = INR (Nat.min (Nat.min a b) c) / (INR a * INR b * INR c).
Proof.
  unfold gamma3.
  set (x := INR (Nat.min (Nat.min a b) c) / (INR a * INR b * INR c)).
  assert (Hx_pos : 0 < x).
  { subst x. apply Rdiv_lt_0_compat.
    - apply lt_0_INR. apply Nat.min_glb_lt; [| lia]. apply Nat.min_glb_lt; lia.
    - assert (HaR : 0 < INR a) by (apply lt_0_INR; lia).
      assert (HbR : 0 < INR b) by (apply lt_0_INR; lia).
      assert (HcR : 0 < INR c) by (apply lt_0_INR; lia).
      apply Rmult_lt_0_compat; [| exact HcR].
      apply Rmult_lt_0_compat; [exact HaR | exact HbR]. }
  assert (Hx_nonneg : 0 <= x) by (apply Rlt_le; exact Hx_pos).
  apply sqrt_def; exact Hx_nonneg.
Qed.

Open Scope nat_scope.

(* ---------------------------------------------------------------------------
   三维混合进制辅助引理（构造性，纯 nat 算术；用于 Hflat 行和重构）
   注：显式 Open Scope nat_scope，使 / 与 mod 解析为 nat 运算，
   否则会被外层 C_scope 解析为复数运算而报 "expected R"。
   --------------------------------------------------------------------------- *)
Lemma nat_div_mod_3d (idx n2 n3 : nat) (Hn2 : (n2 > 0)%nat) (Hn3 : (n3 > 0)%nat) :
  idx = (idx / (n2 * n3)) * (n2 * n3) + ((idx mod (n2 * n3)) / n3) * n3 + (idx mod (n2 * n3)) mod n3.
Proof.
  rewrite (Nat.div_mod idx (n2 * n3)) at 1; [| lia].
  assert (Hr : idx mod (n2 * n3) =
              n3 * ((idx mod (n2 * n3)) / n3) + (idx mod (n2 * n3)) mod n3)
    by (apply Nat.div_mod; lia).
  rewrite Hr at 1.
  rewrite (Nat.mul_comm (n2 * n3) (idx / (n2 * n3))).
  rewrite (Nat.mul_comm n3 ((idx mod (n2 * n3)) / n3)).
  rewrite (Nat.add_assoc ((idx / (n2 * n3)) * (n2 * n3))
                         (((idx mod (n2 * n3)) / n3) * n3)
                         ((idx mod (n2 * n3)) mod n3)).
  reflexivity.
Qed.

Lemma nat_mod_n3_of_mod_n23 (jdx n2 n3 : nat) (Hn2 : (n2 > 0)%nat) (Hn3 : (n3 > 0)%nat) :
  (jdx mod (n2 * n3)) mod n3 = jdx mod n3.
Proof.
  set (r := (jdx mod (n2 * n3)) mod n3).
  assert (Hr_lt : (r < n3)%nat) by (subst r; apply Nat.mod_upper_bound; lia).
  assert (Hjdx : jdx = n3 * (((jdx / (n2 * n3)) * n2) + (jdx mod (n2 * n3) / n3)) + r).
  { rewrite (Nat.div_mod jdx (n2 * n3)) at 1; [| lia].
    rewrite (Nat.mul_comm (n2 * n3) (jdx / (n2 * n3))).
    rewrite (Nat.mul_assoc (jdx / (n2 * n3)) n2 n3).
    assert (Hr : (jdx mod (n2 * n3)) = n3 * ((jdx mod (n2 * n3)) / n3) + r)
      by (subst r; apply Nat.div_mod; lia).
    rewrite Hr at 1.
    rewrite (Nat.mul_comm ((jdx / (n2 * n3)) * n2) n3).
    rewrite (Nat.add_assoc (n3 * ((jdx / (n2 * n3)) * n2)) (n3 * ((jdx mod (n2 * n3)) / n3)) r).
    rewrite <- (Nat.mul_add_distr_l n3 ((jdx / (n2 * n3)) * n2) ((jdx mod (n2 * n3)) / n3)).
    reflexivity. }
  apply (Nat.mod_unique jdx n3
         ((jdx / (n2 * n3)) * n2 + jdx mod (n2 * n3) / n3) r).
  - exact Hr_lt.
  - exact Hjdx.
Qed.

Lemma nat_triple_decode_inj (jdx idx n2 n3 : nat)
      (Hn2 : (n2 > 0)%nat) (Hn3 : (n3 > 0)%nat)
      (i0 j0 k0 : nat)
      (Hi : i0 = (idx / (n2 * n3))%nat) (Hj : j0 = (idx mod (n2 * n3) / n3)%nat) (Hk : k0 = (idx mod n3)%nat)
      (i j k : nat)
      (Hi' : i = (jdx / (n2 * n3))%nat) (Hj' : j = (jdx mod (n2 * n3) / n3)%nat) (Hk' : k = (jdx mod n3)%nat) :
  (i, j, k) = (i0, j0, k0) -> jdx = idx.
Proof.
  intros Hijk. injection Hijk as Hii Hjj Hkk.
  rewrite (nat_div_mod_3d jdx n2 n3 Hn2 Hn3).
  rewrite (nat_div_mod_3d idx n2 n3 Hn2 Hn3).
  rewrite (nat_mod_n3_of_mod_n23 jdx n2 n3 Hn2 Hn3).
  rewrite <- Hi', <- Hj', <- Hk'.
  rewrite Hii, Hjj, Hkk.
  rewrite Hi, Hj, Hk.
  rewrite (nat_mod_n3_of_mod_n23 idx n2 n3 Hn2 Hn3).
  reflexivity.
Qed.

Close Scope nat_scope.

(* ---------------------------------------------------------------------------
   三维基函数
   --------------------------------------------------------------------------- *)
Definition phi3D_norm (a b c : nat) (m : nat) : Complex :=
  Cof_real (/ gamma3 a b c) *c (psi a m *c psi b m *c psi c m).

(* ============================================================================
   第 4 步：phi_flat_decay_general_3d —— 三维离对角衰减一般化引理
   ----------------------------------------------------------------------------
   本段为组装定理提供原 Hdecay_engine 前提所对应的三维衰减界，使主定理
   tensor_product_unconditional_basis_3d 完全自包含（不再依赖外部衰减假设）。

   【常数修正说明（重要）】原 Hdecay_engine 草案取 K0 = Rmax 8 C^3 / 4。
   该常数在「仅 c 轴索引不同（dk = 6）且 a = b <= c1」的配置下不可满足：
   此时归一化三重内积可逼近 1（等轴因子无相消、c 轴相位差被 min(a,c1) 截断），
   而目标界只有 (C^3/4) * 2/C^3 = 1/2。本引擎改用可证的最小常数
   K0' = Rmax 8 C^3 / 2，主定理的 K0 与 M_bound 已相应同步。

   证明结构（三支路直达，不走 2D 引擎嵌套）：
   1) phi3D_inner_scalar_decomposition：归一化三重内积提出纯量
      = (1/G1 * 1/G2) *c 未归一三重 ψ 内积（纯复代数，无前提）；
   2) triple_inner_single_bound：截断 Cauchy-Schwarz（U = A*B, V = C）给出
      Cnorm(未归一三重内积) <= G1 * G2（与 2D inner_product_single_tensor_bound
      同型，仅用 min 的逐轴占优，无稀疏/域条件）；于是归一化内积 <= 1；
   3) one_le_half_K0_dprod：8 分支常数引理——只要有一轴索引不同且
      |di|+|dj|+|dk| <= 6，就有 1 <= (Rmax 8 C^3/2) * d_i * d_j * d_k
      （等轴 d_factor = 1，异轴 = 2/r^d；乘积 >= 2/r^dtot >= 2/C^3 * C^3/2 ... ）。
   稀疏性假设仅用于截断（值 <= seq maxIdx <= pred Mfull）。
   ============================================================================ *)

(* ---- 4.0 复数小引理（记录分域相等 + 乘法交换重排 + 纯量共轭） ---- *)

Lemma complex_eq_re_im : forall z w : Complex, re z = re w -> im z = im w -> z = w.
Proof.
  intros [zr zi] [wr wi] Hre Him; simpl in Hre, Him.
  subst; reflexivity.
Qed.

Lemma Cmul_shuffle : forall (u1 v u2 w : Complex),
  (u1 *c v) *c (u2 *c w) = (u1 *c u2) *c (v *c w).
Proof.
  intros u1 v u2 w.
  rewrite (Cmul_assoc u1 v (u2 *c w)).
  rewrite (Cmul_comm v (u2 *c w)).
  rewrite (Cmul_assoc u2 w v).
  rewrite (Cmul_comm w v).
  rewrite (Cmul_assoc u1 u2 (v *c w)).
  reflexivity.
Qed.

(* ---- 4.1 归一化三重内积的纯量分解（纯代数，无前提） ---- *)

Lemma phi3D_inner_scalar_decomposition :
  forall (a1 b1 c1 a2 b2 c2 : nat) (m : nat),
    Csum (fun k => phi3D_norm a1 b1 c1 k *c Cconj (phi3D_norm a2 b2 c2 k)) m
    = Cof_real (/ gamma3 a1 b1 c1 * / gamma3 a2 b2 c2) *c
      Csum (fun k => (psi a1 k *c Cconj (psi a2 k)) *c
                     (psi b1 k *c Cconj (psi b2 k)) *c
                     (psi c1 k *c Cconj (psi c2 k))) m.
Proof.
  intros a1 b1 c1 a2 b2 c2 m.
  assert (HconjCof : Cconj (Cof_real (/ gamma3 a2 b2 c2)) = Cof_real (/ gamma3 a2 b2 c2))
    by (apply complex_eq_re_im; simpl; ring).
  assert (HCofmul : forall r1 r2 : R, Cof_real r1 *c Cof_real r2 = Cof_real (r1 * r2))
    by (intros r1 r2; apply complex_eq_re_im; simpl; ring).
  assert (Csum_scal_l : forall (c0 : Complex) (f0 : nat -> Complex) (n0 : nat),
    Csum (fun k => c0 *c f0 k) n0 = c0 *c Csum f0 n0).
  { intros c0 f0 n0. induction n0 as [|n0' IH]; simpl.
    - rewrite Cmul_0_r; reflexivity.
    - rewrite IH, Cmul_add_distr_l; reflexivity. }
  rewrite <- (Csum_scal_l (Cof_real (/ gamma3 a1 b1 c1 * / gamma3 a2 b2 c2))
                 (fun k => (psi a1 k *c Cconj (psi a2 k)) *c
                           (psi b1 k *c Cconj (psi b2 k)) *c
                           (psi c1 k *c Cconj (psi c2 k))) m).
  apply Csum_ext'; intros k Hk.
  unfold phi3D_norm.
  rewrite (Cconj_mul (Cof_real (/ gamma3 a2 b2 c2))
                     (psi a2 k *c psi b2 k *c psi c2 k)).
  rewrite HconjCof.
  rewrite (Cconj_mul (psi a2 k *c psi b2 k) (psi c2 k)).
  rewrite (Cmul_shuffle (Cof_real (/ gamma3 a1 b1 c1))
             (psi a1 k *c psi b1 k *c psi c1 k)
             (Cof_real (/ gamma3 a2 b2 c2))
             (Cconj (psi a2 k *c psi b2 k) *c Cconj (psi c2 k))).
  rewrite (Cconj_mul (psi a2 k) (psi b2 k)).
  rewrite (Cmul_shuffle (psi a1 k *c psi b1 k) (psi c1 k)
             (Cconj (psi a2 k) *c Cconj (psi b2 k)) (Cconj (psi c2 k))).
  rewrite (Cmul_shuffle (psi a1 k) (psi b1 k)
             (Cconj (psi a2 k)) (Cconj (psi b2 k))).
  rewrite HCofmul.
  reflexivity.
Qed.

(* ---- 4.2 三重单张量界（截断 Cauchy-Schwarz；与 2D inner_product_single_tensor_bound 同型） ---- *)

Lemma Rsqr_nonneg : forall x : R, 0 <= Rsqr x.
Proof.
  intro x. destruct (Rle_dec 0 x) as [Hx | Hx].
  - unfold Rsqr; apply Rmult_le_pos; [exact Hx | exact Hx].
  - replace (Rsqr x) with (Rsqr (- x)) by (unfold Rsqr; ring).
    unfold Rsqr; apply Rmult_le_pos; lra.
Qed.

Lemma min6_is_one : forall a1 a2 b1 b2 c1 c2 : nat,
  Nat.min (Nat.min (Nat.min a1 a2) (Nat.min b1 b2)) (Nat.min c1 c2) = a1 \/
  Nat.min (Nat.min (Nat.min a1 a2) (Nat.min b1 b2)) (Nat.min c1 c2) = a2 \/
  Nat.min (Nat.min (Nat.min a1 a2) (Nat.min b1 b2)) (Nat.min c1 c2) = b1 \/
  Nat.min (Nat.min (Nat.min a1 a2) (Nat.min b1 b2)) (Nat.min c1 c2) = b2 \/
  Nat.min (Nat.min (Nat.min a1 a2) (Nat.min b1 b2)) (Nat.min c1 c2) = c1 \/
  Nat.min (Nat.min (Nat.min a1 a2) (Nat.min b1 b2)) (Nat.min c1 c2) = c2.
Proof.
  intros a1 a2 b1 b2 c1 c2.
  destruct (Nat.min_spec (Nat.min (Nat.min a1 a2) (Nat.min b1 b2)) (Nat.min c1 c2))
    as [[_ H]|[_ H]]; rewrite H.
  - destruct (Nat.min_spec (Nat.min a1 a2) (Nat.min b1 b2)) as [[_ H4]|[_ H4]]; rewrite H4.
    + destruct (Nat.min_spec a1 a2) as [[_ H2]|[_ H2]]; rewrite H2.
      * left; reflexivity.
      * right; left; reflexivity.
    + destruct (Nat.min_spec b1 b2) as [[_ H3]|[_ H3]]; rewrite H3.
      * right; right; left; reflexivity.
      * right; right; right; left; reflexivity.
  - destruct (Nat.min_spec c1 c2) as [[_ H5]|[_ H5]]; rewrite H5.
    + right; right; right; right; left; reflexivity.
    + right; right; right; right; right; reflexivity.
Qed.

Lemma triple_inner_single_bound :
  forall (a1 b1 c1 a2 b2 c2 : nat),
    (a1 >= 2)%nat -> (b1 >= 2)%nat -> (c1 >= 2)%nat ->
    (a2 >= 2)%nat -> (b2 >= 2)%nat -> (c2 >= 2)%nat ->
    Cnorm (Csum (fun k : nat =>
      (psi a1 k *c Cconj (psi a2 k)) *c
      (psi b1 k *c Cconj (psi b2 k)) *c
      (psi c1 k *c Cconj (psi c2 k)))
      (Nat.min (Nat.min (Nat.min a1 a2) (Nat.min b1 b2)) (Nat.min c1 c2)))
    <= gamma3 a1 b1 c1 * gamma3 a2 b2 c2.
Proof.
  intros a1 b1 c1 a2 b2 c2 Ha1 Hb1 Hc1 Ha2 Hb2 Hc2.
  set (N0 := Nat.min (Nat.min (Nat.min a1 a2) (Nat.min b1 b2)) (Nat.min c1 c2)).
  assert (HNa1 : (N0 <= a1)%nat) by (unfold N0; lia).
  assert (HNa2 : (N0 <= a2)%nat) by (unfold N0; lia).
  assert (HNb1 : (N0 <= b1)%nat) by (unfold N0; lia).
  assert (HNb2 : (N0 <= b2)%nat) by (unfold N0; lia).
  assert (HNc1 : (N0 <= c1)%nat) by (unfold N0; lia).
  assert (HNc2 : (N0 <= c2)%nat) by (unfold N0; lia).
  set (A := fun k : nat => psi a1 k *c Cconj (psi a2 k)).
  set (B := fun k : nat => psi b1 k *c Cconj (psi b2 k)).
  set (C3 := fun k : nat => psi c1 k *c Cconj (psi c2 k)).
  destruct (Nat.eq_dec N0 0) as [Hz | Hpos].
  - rewrite Hz, Csum_0.
    assert (HCnorm0 : Cnorm (C0 : Complex) = 0%R)
      by (unfold Cnorm, Cnorm_sq; simpl; rewrite Rsqr_0, Rplus_0_l; apply sqrt_0).
    rewrite HCnorm0.
    unfold gamma3; apply Rmult_le_pos; apply sqrt_pos.
  - assert (Hzero : A N0 *c B N0 *c C3 N0 = C0).
    { assert (HN0_is : N0 = a1 \/ N0 = a2 \/ N0 = b1 \/ N0 = b2 \/ N0 = c1 \/ N0 = c2)
        by (unfold N0; apply min6_is_one).
      destruct HN0_is as [H|[H|[H|[H|[H|H]]]]]; rewrite H.
      - unfold A. rewrite (psi_ge_n_zero a1 a1) by lia.
        repeat rewrite C0_mul_eq_C0. reflexivity.
      - unfold A. rewrite (psi_ge_n_zero a2 a2) by lia.
        rewrite Cconj_0, C0_mul_eq_C0_r. repeat rewrite C0_mul_eq_C0. reflexivity.
      - unfold B. rewrite (psi_ge_n_zero b1 b1) by lia.
        rewrite C0_mul_eq_C0, C0_mul_eq_C0_r. apply Cmul_0_l.
      - unfold B. rewrite (psi_ge_n_zero b2 b2) by lia.
        rewrite Cconj_0, C0_mul_eq_C0_r, C0_mul_eq_C0_r. apply Cmul_0_l.
      - unfold C3. rewrite (psi_ge_n_zero c1 c1) by lia.
        rewrite C0_mul_eq_C0. apply C0_mul_eq_C0_r.
      - unfold C3. rewrite (psi_ge_n_zero c2 c2) by lia.
        rewrite Cconj_0, C0_mul_eq_C0_r. apply C0_mul_eq_C0_r. }
    assert (Hpos' : (N0 > 0)%nat) by lia.
    pose proof (CauchySchwarz_truncated (fun k : nat => A k *c B k) C3 N0 Hpos' Hzero) as Hcs.
    assert (Hcs' : Cnorm_sq (Csum (fun k : nat => A k *c B k *c C3 k) N0)
                   <= sum_f_R0 (fun k : nat => Cnorm_sq (A k *c B k)) (N0 - 1)
                      * sum_f_R0 (fun k : nat => Cnorm_sq (C3 k)) (N0 - 1))
      by exact Hcs.
    assert (HsumAB : sum_f_R0 (fun k : nat => Cnorm_sq (A k *c B k)) (N0 - 1)
                     = INR N0 / (INR a1 * INR a2 * INR b1 * INR b2)).
    { rewrite (sum_f_R0_ext (fun k : nat => Cnorm_sq (A k *c B k))
                 (fun _ : nat => (1 / (INR a1 * INR a2)) * (1 / (INR b1 * INR b2)))
                 (N0 - 1)).
      - rewrite sum_f_R0_const. replace (S (N0 - 1))%nat with N0 by lia.
        field. repeat split; apply Rgt_not_eq;
          repeat apply Rmult_lt_0_compat; apply lt_0_INR; lia.
      - intros k Hk. assert (Hk' : (k < N0)%nat) by lia.
        unfold A, B.
        rewrite (Cnorm_sq_mult (psi a1 k *c Cconj (psi a2 k))
                               (psi b1 k *c Cconj (psi b2 k))),
                (Cnorm_sq_mult (psi a1 k) (Cconj (psi a2 k))), Cnorm_sq_conj,
                (Cnorm_sq_mult (psi b1 k) (Cconj (psi b2 k))), Cnorm_sq_conj.
        rewrite (Cnorm_sq_psi_exact a1 k), (Cnorm_sq_psi_exact a2 k),
                (Cnorm_sq_psi_exact b1 k), (Cnorm_sq_psi_exact b2 k).
        rewrite (proj2 (Nat.ltb_lt k a1) (Nat.lt_le_trans _ _ _ Hk' HNa1)),
                (proj2 (Nat.ltb_lt k a2) (Nat.lt_le_trans _ _ _ Hk' HNa2)),
                (proj2 (Nat.ltb_lt k b1) (Nat.lt_le_trans _ _ _ Hk' HNb1)),
                (proj2 (Nat.ltb_lt k b2) (Nat.lt_le_trans _ _ _ Hk' HNb2)).
        field. repeat split; apply Rgt_not_eq;
          repeat apply Rmult_lt_0_compat; apply lt_0_INR; lia. }
    assert (HsumC : sum_f_R0 (fun k : nat => Cnorm_sq (C3 k)) (N0 - 1)
                    = INR N0 / (INR c1 * INR c2))
      by (unfold C3; apply sum_sq_psi_product; assumption).
    rewrite HsumAB, HsumC in Hcs'.
    set (P := INR a1 * INR a2 * INR b1 * INR b2 * INR c1 * INR c2).
    assert (HPpos : 0 < P)
      by (unfold P; repeat apply Rmult_lt_0_compat; apply lt_0_INR; lia).
    assert (HXY : INR N0 / (INR a1 * INR a2 * INR b1 * INR b2)
                  * (INR N0 / (INR c1 * INR c2))
                  = INR N0 * INR N0 / P).
    { unfold P. field. repeat split; apply Rgt_not_eq;
        repeat apply Rmult_lt_0_compat; apply lt_0_INR; lia. }
    rewrite HXY in Hcs'.
    set (m1 := Nat.min (Nat.min a1 b1) c1). set (m2 := Nat.min (Nat.min a2 b2) c2).
    set (G1 := gamma3 a1 b1 c1). set (G2 := gamma3 a2 b2 c2).
    assert (HG1pos : 0 < G1) by (unfold G1; apply gamma3_pos; assumption).
    assert (HG2pos : 0 < G2) by (unfold G2; apply gamma3_pos; assumption).
    assert (Hg1sq : G1 * G1 = INR m1 / (INR a1 * INR b1 * INR c1))
      by (unfold G1, m1; apply gamma3_sq; assumption).
    assert (Hg2sq : G2 * G2 = INR m2 / (INR a2 * INR b2 * INR c2))
      by (unfold G2, m2; apply gamma3_sq; assumption).
    assert (HGGsq : G1 * G2 * (G1 * G2) = INR m1 * INR m2 / P).
    { assert (Hex : G1 * G2 * (G1 * G2) = (G1 * G1) * (G2 * G2)) by ring.
      rewrite Hex, Hg1sq, Hg2sq. unfold P. field.
      repeat split; apply Rgt_not_eq;
        repeat apply Rmult_lt_0_compat; apply lt_0_INR; lia. }
    assert (HNm : INR N0 * INR N0 <= INR m1 * INR m2).
    { assert (HN0m1 : (N0 <= m1)%nat) by (unfold N0, m1; lia).
      assert (HN0m2 : (N0 <= m2)%nat) by (unfold N0, m2; lia).
      apply Rmult_le_compat; [apply pos_INR | apply pos_INR
                             | apply le_INR; exact HN0m1 | apply le_INR; exact HN0m2]. }
    assert (Hdiv : INR N0 * INR N0 / P <= INR m1 * INR m2 / P).
    { apply Rmult_le_compat_r;
        [apply Rlt_le; apply Rinv_0_lt_compat; exact HPpos | exact HNm]. }
    assert (Hcsfinal : Cnorm_sq (Csum (fun k : nat => A k *c B k *c C3 k) N0)
                       <= G1 * G2 * (G1 * G2)).
    { rewrite HGGsq. eapply Rle_trans; [exact Hcs' | exact Hdiv]. }
    unfold Cnorm.
    assert (HGnn : 0 <= G1 * G2 * (G1 * G2)).
    { apply Rmult_le_pos; [apply Rmult_le_pos; [apply Rlt_le; exact HG1pos | apply Rlt_le; exact HG2pos]
                          |apply Rmult_le_pos; [apply Rlt_le; exact HG1pos | apply Rlt_le; exact HG2pos]]. }
    apply Rle_trans with (sqrt (G1 * G2 * (G1 * G2))).
    + apply sqrt_le_1_c.
      * unfold Cnorm_sq.
        apply Rle_trans with (0 + 0).
        { replace (0 + 0) with 0 by ring. apply Rle_refl. }
        apply Rplus_le_compat; apply Rsqr_nonneg.
      * exact HGnn.
      * exact Hcsfinal.
    + assert (HGp : 0 <= G1 * G2)
        by (apply Rmult_le_pos; [apply Rlt_le; exact HG1pos | apply Rlt_le; exact HG2pos]).
      rewrite sqrt_square by exact HGp. apply Rle_refl.
Qed.

(* ---- 4.3 常数引理：1 <= (Rmax 8 C^3 / 2) * d_i * d_j * d_k ---- *)

Lemma Rmult_le_compat_right_mine : forall c x y : R,
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

Lemma Rmult_le_compat4_mine : forall a b c d : R,
  0 <= a -> a <= b -> 0 <= c -> c <= d -> a * c <= b * d.
Proof.
  intros a b c d Ha Hab Hc Hcd.
  apply Rle_trans with (b * c).
  - apply Rmult_le_compat_right_mine; [exact Hc | exact Hab].
  - replace (b * c) with (c * b) by ring.
    replace (b * d) with (d * b) by ring.
    apply Rmult_le_compat_right_mine; [lra | exact Hcd].
Qed.

Lemma K0_mult_fin : forall K t x : R,
  0 < x -> 0 < K -> 2 <= t -> x <= K -> 1 <= (K / 2) * (t / x).
Proof.
  intros K t x Hx HK Ht HxK.
  assert (Hkey : (K / 2) * (t / x) * x = (K / 2) * t).
  { unfold Rdiv. rewrite (Rmult_assoc (K * / 2) (t * / x) x).
    rewrite (Rmult_assoc t (/ x) x), (Rinv_l x (Rgt_not_eq x 0 Hx)). ring. }
  apply (Rmult_le_reg_r x 1 ((K / 2) * (t / x))); [exact Hx |].
  rewrite Hkey.
  replace (1 * x) with x by ring.
  apply Rle_trans with K; [exact HxK |].
  assert (Hkh : (K / 2) * 2 = K) by (unfold Rdiv; field).
  apply Rle_trans with ((K / 2) * 2).
  - rewrite Hkh. apply Rle_refl.
  - apply Rmult_le_compat4_mine.
    + unfold Rdiv; apply Rmult_le_pos; [apply Rlt_le; exact HK | apply Rlt_le; lra].
    + apply Rle_refl.
    + apply Rlt_le; lra.
    + exact Ht.
Qed.

Lemma one_le_half_K0_dprod :
  forall (C : nat) (HCgt2 : (C > 2)%nat) (r : R) (Hr : r = sqrt (INR C))
    (i1 i2 j1 j2 k1 k2 : nat)
    (Hdiff : i1 <> i2 \/ j1 <> j2 \/ k1 <> k2)
    (Hidx6 : (Z.abs_nat (Z.of_nat i1 - Z.of_nat i2) +
              Z.abs_nat (Z.of_nat j1 - Z.of_nat j2) +
              Z.abs_nat (Z.of_nat k1 - Z.of_nat k2) <= 6)%nat),
  1%R <= (Rmax 8 (((INR C) ^ 3)%R) / 2) *
         (d_factor r i1 i2 * d_factor r j1 j2 * d_factor r k1 k2).
Proof.
  intros C HCgt2 r Hr i1 i2 j1 j2 k1 k2 Hdiff Hidx6.
  set (di := Z.abs_nat (Z.of_nat i1 - Z.of_nat i2)).
  set (dj := Z.abs_nat (Z.of_nat j1 - Z.of_nat j2)).
  set (dk := Z.abs_nat (Z.of_nat k1 - Z.of_nat k2)).
  assert (Hr_ge1 : 1 <= r).
  { rewrite Hr, <- sqrt_1.
    apply sqrt_le_1_c; [apply Rle_0_1 | apply pos_INR; lia
                        | change 1 with (INR 1); apply le_INR; lia]. }
  assert (Hr_pos : 0 < r) by lra.
  assert (HRmax_ge : 8 <= Rmax 8 (((INR C) ^ 3)%R)) by apply Rmax_l.
  assert (HRmax_nn : 0 <= Rmax 8 (((INR C) ^ 3)%R))
    by (apply Rle_trans with 8%R; [lra | exact HRmax_ge]).
  assert (HC3_le_Rmax : ((INR C) ^ 3)%R <= Rmax 8 (((INR C) ^ 3)%R)) by apply Rmax_r.
  assert (Hpowdtot_le : (r ^ (di + dj + dk))%R <= ((INR C) ^ 3)%R).
  { apply Rle_trans with ((r ^ 6)%R)%R.
    - apply Rle_pow; [exact Hr_ge1 | lia].
    - rewrite Hr. rewrite (sqrt_pow_6 (INR C)) by (apply pos_INR; lia). apply Rle_refl. }
  assert (Hfin : (r ^ (di + dj + dk))%R <= Rmax 8 (((INR C) ^ 3)%R))
    by (eapply Rle_trans; [exact Hpowdtot_le | exact HC3_le_Rmax]).
  (* 异轴 d_factor 的展开式与等轴的 1 *)
  assert (Hdf_neq : forall x y : nat, x <> y -> d_factor r x y = 2 / r ^ Z.abs_nat (Z.of_nat x - Z.of_nat y)).
  { intros x y Hxy. unfold d_factor.
    rewrite (proj2 (Nat.eqb_neq x y) Hxy). reflexivity. }
  destruct (Nat.eq_dec i1 i2) as [Heq_i | Hne_i].
  - assert (Hdfi : d_factor r i1 i2 = 1) by (rewrite Heq_i; apply d_factor_diag).
    assert (Hdi0 : di = 0%nat) by (unfold di; rewrite <- Heq_i, Z.sub_diag; reflexivity).
    rewrite Hdfi.
    destruct (Nat.eq_dec j1 j2) as [Heq_j | Hne_j].
    + assert (Hdfj : d_factor r j1 j2 = 1) by (rewrite Heq_j; apply d_factor_diag).
      assert (Hdj0 : dj = 0%nat) by (unfold dj; rewrite <- Heq_j, Z.sub_diag; reflexivity).
      assert (Hne_k : k1 <> k2)
        by (destruct Hdiff as [H|[H|H]]; [contradiction (H Heq_i) | contradiction (H Heq_j) | exact H]).
      assert (Hdfk : d_factor r k1 k2 = 2 / (r ^ dk)%R) by (apply Hdf_neq; exact Hne_k).
      rewrite Hdfj, Hdfk.
      assert (Hdt : (r ^ (di + dj + dk))%R = (r ^ dk)%R)
        by (rewrite Hdi0, Hdj0; reflexivity).
      replace (1 * 1 * (2 / (r ^ dk)%R)) with (2 / r ^ (di + dj + dk))
        by (rewrite <- Hdt; field; apply Rgt_not_eq; apply pow_lt; exact Hr_pos).
      apply (K0_mult_fin (Rmax 8 (((INR C) ^ 3)%R)) 2 (r ^ (di + dj + dk)));
        [apply pow_lt; exact Hr_pos
        |apply Rlt_le_trans with 8%R; [lra | exact HRmax_ge]
        |lra | exact Hfin].
    + assert (Hdfj : d_factor r j1 j2 = 2 / (r ^ dj)%R) by (apply Hdf_neq; exact Hne_j).
      destruct (Nat.eq_dec k1 k2) as [Heq_k | Hne_k].
      * assert (Hdfk : d_factor r k1 k2 = 1) by (rewrite Heq_k; apply d_factor_diag).
        assert (Hdk0 : dk = 0%nat) by (unfold dk; rewrite <- Heq_k, Z.sub_diag; reflexivity).
        rewrite Hdfj, Hdfk.
        assert (Hdt : (r ^ (di + dj + dk))%R = (r ^ dj)%R)
          by (rewrite Hdi0, Hdk0, Nat.add_0_r; reflexivity).
        replace (1 * (2 / (r ^ dj)%R) * 1) with (2 / r ^ (di + dj + dk))
          by (rewrite <- Hdt; field; apply Rgt_not_eq; apply pow_lt; exact Hr_pos).
        apply (K0_mult_fin (Rmax 8 (((INR C) ^ 3)%R)) 2 (r ^ (di + dj + dk)));
          [apply pow_lt; exact Hr_pos
          |apply Rlt_le_trans with 8%R; [lra | exact HRmax_ge]
          |lra | exact Hfin].
      * assert (Hdfk : d_factor r k1 k2 = 2 / (r ^ dk)%R) by (apply Hdf_neq; exact Hne_k).
        rewrite Hdfj, Hdfk.
        assert (Hdt : (r ^ (di + dj + dk))%R = (r ^ dj)%R * (r ^ dk)%R)
          by (rewrite Hdi0; apply pow_add).
        replace (1 * (2 / (r ^ dj)%R) * (2 / (r ^ dk)%R)) with (4 / r ^ (di + dj + dk))
          by (rewrite Hdt; field; repeat split; apply Rgt_not_eq; apply pow_lt; exact Hr_pos).
        apply (K0_mult_fin (Rmax 8 (((INR C) ^ 3)%R)) 4 (r ^ (di + dj + dk)));
          [apply pow_lt; exact Hr_pos
          |apply Rlt_le_trans with 8%R; [lra | exact HRmax_ge]
          |lra | exact Hfin].
  - assert (Hdfi : d_factor r i1 i2 = 2 / (r ^ di)%R) by (apply Hdf_neq; exact Hne_i).
    rewrite Hdfi.
    destruct (Nat.eq_dec j1 j2) as [Heq_j | Hne_j].
    + assert (Hdfj : d_factor r j1 j2 = 1) by (rewrite Heq_j; apply d_factor_diag).
      assert (Hdj0 : dj = 0%nat) by (unfold dj; rewrite <- Heq_j, Z.sub_diag; reflexivity).
      destruct (Nat.eq_dec k1 k2) as [Heq_k | Hne_k].
      * assert (Hdfk : d_factor r k1 k2 = 1) by (rewrite Heq_k; apply d_factor_diag).
        assert (Hdk0 : dk = 0%nat) by (unfold dk; rewrite <- Heq_k, Z.sub_diag; reflexivity).
        rewrite Hdfj, Hdfk.
        assert (Hdt : (r ^ (di + dj + dk))%R = (r ^ di)%R)
          by (rewrite Hdj0, Hdk0, !Nat.add_0_r; reflexivity).
        replace ((2 / (r ^ di)%R) * 1 * 1) with (2 / r ^ (di + dj + dk))
          by (rewrite <- Hdt; field; apply Rgt_not_eq; apply pow_lt; exact Hr_pos).
        apply (K0_mult_fin (Rmax 8 (((INR C) ^ 3)%R)) 2 (r ^ (di + dj + dk)));
          [apply pow_lt; exact Hr_pos
          |apply Rlt_le_trans with 8%R; [lra | exact HRmax_ge]
          |lra | exact Hfin].
      * assert (Hdfk : d_factor r k1 k2 = 2 / (r ^ dk)%R) by (apply Hdf_neq; exact Hne_k).
        rewrite Hdfj, Hdfk.
        assert (Hdt : (r ^ (di + dj + dk))%R = (r ^ di)%R * (r ^ dk)%R)
          by (rewrite Hdj0, Nat.add_0_r; apply pow_add).
        replace ((2 / (r ^ di)%R) * 1 * (2 / (r ^ dk)%R)) with (4 / r ^ (di + dj + dk))
          by (rewrite Hdt; field; repeat split; apply Rgt_not_eq; apply pow_lt; exact Hr_pos).
        apply (K0_mult_fin (Rmax 8 (((INR C) ^ 3)%R)) 4 (r ^ (di + dj + dk)));
          [apply pow_lt; exact Hr_pos
          |apply Rlt_le_trans with 8%R; [lra | exact HRmax_ge]
          |lra | exact Hfin].
    + assert (Hdfj : d_factor r j1 j2 = 2 / (r ^ dj)%R) by (apply Hdf_neq; exact Hne_j).
      destruct (Nat.eq_dec k1 k2) as [Heq_k | Hne_k].
      * assert (Hdfk : d_factor r k1 k2 = 1) by (rewrite Heq_k; apply d_factor_diag).
        assert (Hdk0 : dk = 0%nat) by (unfold dk; rewrite <- Heq_k, Z.sub_diag; reflexivity).
        rewrite Hdfj, Hdfk.
        assert (Hdt : (r ^ (di + dj + dk))%R = (r ^ di)%R * (r ^ dj)%R)
          by (rewrite Hdk0, Nat.add_0_r; apply pow_add).
        replace ((2 / (r ^ di)%R) * (2 / (r ^ dj)%R) * 1) with (4 / r ^ (di + dj + dk))
          by (rewrite Hdt; field; repeat split; apply Rgt_not_eq; apply pow_lt; exact Hr_pos).
        apply (K0_mult_fin (Rmax 8 (((INR C) ^ 3)%R)) 4 (r ^ (di + dj + dk)));
          [apply pow_lt; exact Hr_pos
          |apply Rlt_le_trans with 8%R; [lra | exact HRmax_ge]
          |lra | exact Hfin].
      * assert (Hdfk : d_factor r k1 k2 = 2 / (r ^ dk)%R) by (apply Hdf_neq; exact Hne_k).
        rewrite Hdfj, Hdfk.
        assert (Hdt : (r ^ (di + dj + dk))%R = (r ^ di)%R * (r ^ dj)%R * (r ^ dk)%R).
        { rewrite <- (pow_add r di dj). apply pow_add. }
        replace ((2 / (r ^ di)%R) * (2 / (r ^ dj)%R) * (2 / (r ^ dk)%R)) with (8 / r ^ (di + dj + dk))
          by (rewrite Hdt; field; repeat split; apply Rgt_not_eq; apply pow_lt; exact Hr_pos).
        apply (K0_mult_fin (Rmax 8 (((INR C) ^ 3)%R)) 8 (r ^ (di + dj + dk)));
          [apply pow_lt; exact Hr_pos
          |apply Rlt_le_trans with 8%R; [lra | exact HRmax_ge]
          |lra | exact Hfin].
Qed.

(* ---- 4.4 主引擎：三维离对角衰减一般化引理 ---- *)

Theorem phi_flat_decay_general_3d :
  forall (C : nat) (HCgt2 : (C > 2)%nat)
    (seq1 seq2 seq3 : nat -> nat)
    (Hsparse1 : forall i : nat, (INR (seq1 (S i)) > INR C * INR (seq1 i))%R)
    (Hsparse2 : forall i : nat, (INR (seq2 (S i)) > INR C * INR (seq2 i))%R)
    (Hsparse3 : forall i : nat, (INR (seq3 (S i)) > INR C * INR (seq3 i))%R)
    (Hge2_1 : forall i : nat, (seq1 i >= 2)%nat)
    (Hge2_2 : forall i : nat, (seq2 i >= 2)%nat)
    (Hge2_3 : forall i : nat, (seq3 i >= 2)%nat)
    (I1 I2 I3 : list nat)
    (n1 n2 n3 : nat) (Hn1 : n1 = length I1) (Hn2 : n2 = length I2) (Hn3 : n3 = length I3)
    (idx1 idx2 : nat) (Hneq : idx1 <> idx2)
    (Hlt1 : (idx1 < n1 * n2 * n3)%nat) (Hlt2 : (idx2 < n1 * n2 * n3)%nat)
    (Hidx6 : (Z.abs_nat (Z.of_nat (idx1 / (n2 * n3)) - Z.of_nat (idx2 / (n2 * n3))) +
              Z.abs_nat (Z.of_nat (idx1 mod (n2 * n3) / n3) - Z.of_nat (idx2 mod (n2 * n3) / n3)) +
              Z.abs_nat (Z.of_nat (idx1 mod n3) - Z.of_nat (idx2 mod n3)) <= 6)%nat),
  Cnorm (Csum (fun k => phi3D_norm
                    (nth (idx1 / (n2 * n3))%nat (map seq1 I1) 0%nat)
                    (nth (idx1 mod (n2 * n3) / n3)%nat (map seq2 I2) 0%nat)
                    (nth (idx1 mod n3)%nat (map seq3 I3) 0%nat) k *c
                  Cconj (phi3D_norm
                    (nth (idx2 / (n2 * n3))%nat (map seq1 I1) 0%nat)
                    (nth (idx2 mod (n2 * n3) / n3)%nat (map seq2 I2) 0%nat)
                    (nth (idx2 mod n3)%nat (map seq3 I3) 0%nat) k))
               (Nat.pred (S (max (max (seq1 (fold_right Nat.max 0%nat I1))
                                     (seq2 (fold_right Nat.max 0%nat I2)))
                              (seq3 (fold_right Nat.max 0%nat I3))))))
  <= (Rmax 8 (((INR C) ^ 3)%R) / 2) *
     (d_factor (sqrt (INR C)) (idx1 / (n2 * n3))%nat (idx2 / (n2 * n3))%nat *
      d_factor (sqrt (INR C)) (idx1 mod (n2 * n3) / n3)%nat (idx2 mod (n2 * n3) / n3)%nat *
      d_factor (sqrt (INR C)) (idx1 mod n3)%nat (idx2 mod n3)%nat).
Proof.
  intros C HCgt2 seq1 seq2 seq3 Hsparse1 Hsparse2 Hsparse3
         Hge2_1 Hge2_2 Hge2_3 I1 I2 I3 n1 n2 n3 Hn1 Hn2 Hn3
         idx1 idx2 Hneq Hlt1 Hlt2 Hidx6.
  assert (HCge2 : (C >= 2)%nat) by lia.
  (* 混合进制解码 *)
  set (i1 := (idx1 / (n2 * n3))%nat). set (rem1 := (idx1 mod (n2 * n3))%nat).
  set (j1 := (rem1 / n3)%nat). set (k1 := (idx1 mod n3)%nat).
  set (i2 := (idx2 / (n2 * n3))%nat). set (rem2 := (idx2 mod (n2 * n3))%nat).
  set (j2 := (rem2 / n3)%nat). set (k2 := (idx2 mod n3)%nat).
  assert (Hn2pos : (n2 > 0)%nat) by (destruct n2 as [|n2']; [exfalso; lia | lia]).
  assert (Hn3pos : (n3 > 0)%nat) by (destruct n3 as [|n3']; [exfalso; lia | lia]).
  assert (Hi1 : (i1 < n1)%nat) by (apply Nat.Div0.div_lt_upper_bound; nia).
  assert (Hrem1 : (rem1 < n2 * n3)%nat) by (apply Nat.mod_upper_bound; lia).
  assert (Hj1 : (j1 < n2)%nat).
  { apply (Nat.Div0.div_lt_upper_bound rem1 n3 n2).
    apply Nat.lt_le_trans with (n2 * n3)%nat; [exact Hrem1 | nia]. }
  assert (Hk1 : (k1 < n3)%nat) by (apply Nat.mod_upper_bound; lia).
  assert (Hi2 : (i2 < n1)%nat) by (apply Nat.Div0.div_lt_upper_bound; nia).
  assert (Hrem2 : (rem2 < n2 * n3)%nat) by (apply Nat.mod_upper_bound; lia).
  assert (Hj2 : (j2 < n2)%nat).
  { apply (Nat.Div0.div_lt_upper_bound rem2 n3 n2).
    apply Nat.lt_le_trans with (n2 * n3)%nat; [exact Hrem2 | nia]. }
  assert (Hk2 : (k2 < n3)%nat) by (apply Nat.mod_upper_bound; lia).
  set (a1 := nth i1 (map seq1 I1) 0%nat). set (a2 := nth i2 (map seq1 I1) 0%nat).
  set (b1 := nth j1 (map seq2 I2) 0%nat). set (b2 := nth j2 (map seq2 I2) 0%nat).
  set (c1 := nth k1 (map seq3 I3) 0%nat). set (c2 := nth k2 (map seq3 I3) 0%nat).
  set (maxIdx1 := fold_right Nat.max 0%nat I1).
  set (maxIdx2 := fold_right Nat.max 0%nat I2).
  set (maxIdx3 := fold_right Nat.max 0%nat I3).
  set (Mfull := max (max (seq1 maxIdx1) (seq2 maxIdx2)) (seq3 maxIdx3)).
  (* 长度与 >= 2 *)
  assert (Hi1_len : (i1 < length I1)%nat) by (rewrite <- Hn1; exact Hi1).
  assert (Hi2_len : (i2 < length I1)%nat) by (rewrite <- Hn1; exact Hi2).
  assert (Hj1_len : (j1 < length I2)%nat) by (rewrite <- Hn2; exact Hj1).
  assert (Hj2_len : (j2 < length I2)%nat) by (rewrite <- Hn2; exact Hj2).
  assert (Hk1_len : (k1 < length I3)%nat) by (rewrite <- Hn3; exact Hk1).
  assert (Hk2_len : (k2 < length I3)%nat) by (rewrite <- Hn3; exact Hk2).
  assert (Ha1_ge2 : (a1 >= 2)%nat).
  { unfold a1. rewrite (H_nth_map nat nat seq1 I1 0%nat 0%nat i1 Hi1_len). apply Hge2_1. }
  assert (Ha2_ge2 : (a2 >= 2)%nat).
  { unfold a2. rewrite (H_nth_map nat nat seq1 I1 0%nat 0%nat i2 Hi2_len). apply Hge2_1. }
  assert (Hb1_ge2 : (b1 >= 2)%nat).
  { unfold b1. rewrite (H_nth_map nat nat seq2 I2 0%nat 0%nat j1 Hj1_len). apply Hge2_2. }
  assert (Hb2_ge2 : (b2 >= 2)%nat).
  { unfold b2. rewrite (H_nth_map nat nat seq2 I2 0%nat 0%nat j2 Hj2_len). apply Hge2_2. }
  assert (Hc1_ge2 : (c1 >= 2)%nat).
  { unfold c1. rewrite (H_nth_map nat nat seq3 I3 0%nat 0%nat k1 Hk1_len). apply Hge2_3. }
  assert (Hc2_ge2 : (c2 >= 2)%nat).
  { unfold c2. rewrite (H_nth_map nat nat seq3 I3 0%nat 0%nat k2 Hk2_len). apply Hge2_3. }
  (* 单调性与全局最大（截断用） *)
  assert (Hseq1_inc : forall x y, (x <= y)%nat -> (seq1 x <= seq1 y)%nat).
  { intros x y Hle; destruct (Nat.eq_dec x y) as [Heq | Hne].
    - subst; apply Nat.le_refl.
    - apply Nat.lt_le_incl. apply (seq_strict_growth_lt seq1 C x y);
        [exact HCge2 | exact Hsparse1 | exact Hge2_1 | lia]. }
  assert (Hseq2_inc : forall x y, (x <= y)%nat -> (seq2 x <= seq2 y)%nat).
  { intros x y Hle; destruct (Nat.eq_dec x y) as [Heq | Hne].
    - subst; apply Nat.le_refl.
    - apply Nat.lt_le_incl. apply (seq_strict_growth_lt seq2 C x y);
        [exact HCge2 | exact Hsparse2 | exact Hge2_2 | lia]. }
  assert (Hseq3_inc : forall x y, (x <= y)%nat -> (seq3 x <= seq3 y)%nat).
  { intros x y Hle; destruct (Nat.eq_dec x y) as [Heq | Hne].
    - subst; apply Nat.le_refl.
    - apply Nat.lt_le_incl. apply (seq_strict_growth_lt seq3 C x y);
        [exact HCge2 | exact Hsparse3 | exact Hge2_3 | lia]. }
  assert (Ha1_le : (a1 <= Mfull)%nat).
  { unfold a1. rewrite (H_nth_map nat nat seq1 I1 0%nat 0%nat i1 Hi1_len).
    apply Nat.le_trans with (seq1 maxIdx1).
    - apply Hseq1_inc; unfold maxIdx1; apply fold_right_max_ge; apply nth_In; exact Hi1_len.
    - unfold Mfull; apply Nat.le_trans with (max (seq1 maxIdx1) (seq2 maxIdx2));
        [apply Nat.le_max_l | apply Nat.le_max_l]. }
  assert (Ha2_le : (a2 <= Mfull)%nat).
  { unfold a2. rewrite (H_nth_map nat nat seq1 I1 0%nat 0%nat i2 Hi2_len).
    apply Nat.le_trans with (seq1 maxIdx1).
    - apply Hseq1_inc; unfold maxIdx1; apply fold_right_max_ge; apply nth_In; exact Hi2_len.
    - unfold Mfull; apply Nat.le_trans with (max (seq1 maxIdx1) (seq2 maxIdx2));
        [apply Nat.le_max_l | apply Nat.le_max_l]. }
  assert (Hb1_le : (b1 <= Mfull)%nat).
  { unfold b1. rewrite (H_nth_map nat nat seq2 I2 0%nat 0%nat j1 Hj1_len).
    apply Nat.le_trans with (seq2 maxIdx2).
    - apply Hseq2_inc; unfold maxIdx2; apply fold_right_max_ge; apply nth_In; exact Hj1_len.
    - unfold Mfull; apply Nat.le_trans with (max (seq1 maxIdx1) (seq2 maxIdx2));
        [apply Nat.le_max_r | apply Nat.le_max_l]. }
  assert (Hb2_le : (b2 <= Mfull)%nat).
  { unfold b2. rewrite (H_nth_map nat nat seq2 I2 0%nat 0%nat j2 Hj2_len).
    apply Nat.le_trans with (seq2 maxIdx2).
    - apply Hseq2_inc; unfold maxIdx2; apply fold_right_max_ge; apply nth_In; exact Hj2_len.
    - unfold Mfull; apply Nat.le_trans with (max (seq1 maxIdx1) (seq2 maxIdx2));
        [apply Nat.le_max_r | apply Nat.le_max_l]. }
  assert (Hc1_le : (c1 <= Mfull)%nat).
  { unfold c1. rewrite (H_nth_map nat nat seq3 I3 0%nat 0%nat k1 Hk1_len).
    apply Nat.le_trans with (seq3 maxIdx3).
    - apply Hseq3_inc; unfold maxIdx3; apply fold_right_max_ge; apply nth_In; exact Hk1_len.
    - unfold Mfull; apply Nat.le_max_r. }
  assert (Hc2_le : (c2 <= Mfull)%nat).
  { unfold c2. rewrite (H_nth_map nat nat seq3 I3 0%nat 0%nat k2 Hk2_len).
    apply Nat.le_trans with (seq3 maxIdx3).
    - apply Hseq3_inc; unfold maxIdx3; apply fold_right_max_ge; apply nth_In; exact Hk2_len.
    - unfold Mfull; apply Nat.le_max_r. }
  (* 截断到 N0 = 六值最小 *)
  set (N0 := Nat.min (Nat.min (Nat.min a1 a2) (Nat.min b1 b2)) (Nat.min c1 c2)).
  assert (Htrunc_eq :
    Csum (fun k => phi3D_norm a1 b1 c1 k *c Cconj (phi3D_norm a2 b2 c2 k)) (Nat.pred (S Mfull))
    = Csum (fun k => phi3D_norm a1 b1 c1 k *c Cconj (phi3D_norm a2 b2 c2 k)) N0).
  { apply (Csum_trunc_tail _ N0 (Nat.pred (S Mfull))).
    - simpl; lia.
    - intros k Hk. destruct Hk as [Hk1' Hk2'].
      assert (HN0_is : N0 = a1 \/ N0 = a2 \/ N0 = b1 \/ N0 = b2 \/ N0 = c1 \/ N0 = c2)
        by (unfold N0; apply min6_is_one).
      destruct HN0_is as [H|[H|[H|[H|[H|H]]]]]; rewrite H in Hk1'.
      + unfold phi3D_norm. rewrite (psi_ge_n_zero a1 k Hk1').
        repeat rewrite C0_mul_eq_C0. rewrite C0_mul_eq_C0_r. apply C0_mul_eq_C0.
      + unfold phi3D_norm. rewrite (psi_ge_n_zero a2 k Hk1').
        repeat rewrite C0_mul_eq_C0. rewrite C0_mul_eq_C0_r, Cconj_0.
        apply C0_mul_eq_C0_r.
      + unfold phi3D_norm. rewrite (psi_ge_n_zero b1 k Hk1').
        rewrite C0_mul_eq_C0_r, C0_mul_eq_C0, C0_mul_eq_C0_r. apply Cmul_0_l.
      + unfold phi3D_norm. rewrite (psi_ge_n_zero b2 k Hk1').
        rewrite C0_mul_eq_C0_r, C0_mul_eq_C0, C0_mul_eq_C0_r, Cconj_0.
        apply C0_mul_eq_C0_r.
      + unfold phi3D_norm. rewrite (psi_ge_n_zero c1 k Hk1').
        rewrite C0_mul_eq_C0_r, C0_mul_eq_C0_r. apply Cmul_0_l.
      + unfold phi3D_norm. rewrite (psi_ge_n_zero c2 k Hk1').
        rewrite C0_mul_eq_C0_r, C0_mul_eq_C0_r, Cconj_0. apply C0_mul_eq_C0_r. }
  rewrite Htrunc_eq.
  (* 纯量分解 + 三重单张量界 *)
  rewrite (phi3D_inner_scalar_decomposition a1 b1 c1 a2 b2 c2 N0).
  set (G1 := gamma3 a1 b1 c1). set (G2 := gamma3 a2 b2 c2).
  assert (HG1pos : 0 < G1) by (unfold G1; apply gamma3_pos; assumption).
  assert (HG2pos : 0 < G2) by (unfold G2; apply gamma3_pos; assumption).
  assert (HGpos : 0 < G1 * G2) by (apply Rmult_lt_0_compat; assumption).
  assert (Hsc_nonneg : 0 <= / G1 * / G2)
    by (apply Rlt_le; apply Rmult_lt_0_compat;
        [apply Rinv_0_lt_compat; exact HG1pos | apply Rinv_0_lt_compat; exact HG2pos]).
  rewrite Cnorm_mult.
  rewrite (Cnorm_Cof_real_pos (/ G1 * / G2) Hsc_nonneg).
  assert (Hinner : / G1 * / G2 *
      Cnorm (Csum (fun k => (psi a1 k *c Cconj (psi a2 k)) *c
                               (psi b1 k *c Cconj (psi b2 k)) *c
                               (psi c1 k *c Cconj (psi c2 k))) N0) <= 1).
  { apply Rle_trans with (/ G1 * / G2 * (G1 * G2)).
    - apply Rmult_le_compat4_mine.
      + apply Rlt_le; apply Rmult_lt_0_compat;
          [apply Rinv_0_lt_compat; exact HG1pos | apply Rinv_0_lt_compat; exact HG2pos].
      + apply Rle_refl.
      + unfold Cnorm; apply sqrt_pos.
      + apply triple_inner_single_bound; assumption.
    - replace (/ G1 * / G2 * (G1 * G2)) with 1.
      + apply Rle_refl.
      + replace (/ G1 * / G2) with (/ (G1 * G2))
          by (field; repeat split;
              try (apply Rgt_not_eq; exact HG1pos);
              try (apply Rgt_not_eq; exact HG2pos);
              try (apply Rgt_not_eq; exact HGpos)).
        symmetry. apply Rinv_l. apply Rgt_not_eq. exact HGpos. }
  eapply Rle_trans; [exact Hinner |].
  (* 常数引理收尾 *)
  assert (Hdiff : i1 <> i2 \/ j1 <> j2 \/ k1 <> k2).
  { destruct (Nat.eq_dec i1 i2) as [Heq_i | Hne_i].
    - destruct (Nat.eq_dec j1 j2) as [Heq_j | Hne_j].
      + destruct (Nat.eq_dec k1 k2) as [Heq_k | Hne_k].
        * exfalso; apply Hneq.
          assert (Hijk : (i1, j1, k1) = (i2, j2, k2))
            by (rewrite Heq_i, Heq_j, Heq_k; reflexivity).
          (* 合并单文件环境中裸 eq_refl 的 elaboration 不稳（Rocq 9 Reflexive 展开），
             改用 reflexivity 显式假设——独立与合并环境均通过（会话 12 修复） *)
          assert (Hi2eq : i2 = (idx2 / (n2 * n3))%nat) by reflexivity.
          assert (Hj2eq : j2 = (idx2 mod (n2 * n3) / n3)%nat) by reflexivity.
          assert (Hk2eq : k2 = (idx2 mod n3)%nat) by reflexivity.
          assert (Hi1eq : i1 = (idx1 / (n2 * n3))%nat) by reflexivity.
          assert (Hj1eq : j1 = (idx1 mod (n2 * n3) / n3)%nat) by reflexivity.
          assert (Hk1eq : k1 = (idx1 mod n3)%nat) by reflexivity.
          exact (nat_triple_decode_inj idx1 idx2 n2 n3 Hn2pos Hn3pos
                   i2 j2 k2 Hi2eq Hj2eq Hk2eq
                   i1 j1 k1 Hi1eq Hj1eq Hk1eq Hijk).
        * right; right; exact Hne_k.
      + right; left; exact Hne_j.
    - left; exact Hne_i. }
  apply (one_le_half_K0_dprod C HCgt2 (sqrt (INR C))).
  - reflexivity.          (* Hr : sqrt (INR C) = sqrt (INR C) —— 合并环境 eq_refl 参数不稳，改用 reflexivity *)
  - exact Hdiff.
  - exact Hidx6.
Qed.




(* ============================================================================
   库 ca_basis_3d（构造性轨道 · 用户 WorkBuddy 工作区）
   三维张量积无条件基 —— 第 5 步组装定理
   依赖：ca_decay（abstract_unconditional_basis / 3D 备料 / triple_prod_row_sum_decomp
                    / Csum_flatten_3d / sum_f_R0_flatten_3d / d_factor / K 等）
   构造性约定（coq-live-repair §6）：避开 Req_EM_T 实数等值排中；显式界与收敛率；
   存在断言给见证；零 Admitted、零活动 Axiom。
   ============================================================================ *)


(* ---------------------------------------------------------------------------
   第 5 步组装定理：三维张量积无条件基
   衰减部分由本文件第 4 步的 phi_flat_decay_general_3d 直接供给（已建成，见上文），
   不再依赖外部 Hdecay_engine 假设——定理完全自包含、构造性闭合。
   注意：K0 = Rmax 8 C^3 / 2（可证最小常数；原 /4 草案在仅单轴不同 + dk=6 时不可满足，
   见第 4 步注释）。
   --------------------------------------------------------------------------- *)
Theorem tensor_product_unconditional_basis_3d :
  forall (C : nat) (HCgt2 : (C > 2)%nat)
    (seq1 seq2 seq3 : nat -> nat)
    (Hsparse1 : forall i : nat, (INR (seq1 (S i)) > INR C * INR (seq1 i))%R)
    (Hsparse2 : forall i : nat, (INR (seq2 (S i)) > INR C * INR (seq2 i))%R)
    (Hsparse3 : forall i : nat, (INR (seq3 (S i)) > INR C * INR (seq3 i))%R)
    (Hge2_1 : forall i : nat, (seq1 i >= 2)%nat)
    (Hge2_2 : forall i : nat, (seq2 i >= 2)%nat)
    (Hge2_3 : forall i : nat, (seq3 i >= 2)%nat)
    (I1 I2 I3 : list nat)
    (Hdup1 : NoDup I1) (Hsorted1 : Sorted Nat.lt I1)
    (Hdup2 : NoDup I2) (Hsorted2 : Sorted Nat.lt I2)
    (Hdup3 : NoDup I3) (Hsorted3 : Sorted Nat.lt I3)
    (coeffs_flat : list Complex)
    (n1 n2 n3 : nat) (Hn1 : n1 = length I1) (Hn2 : n2 = length I2) (Hn3 : n3 = length I3)
    (Hn1_pos : (n1 > 0)%nat) (Hn2_pos : (n2 > 0)%nat) (Hn3_pos : (n3 > 0)%nat)
    (Hlen_flat : length coeffs_flat = (n1 * n2 * n3)%nat)
    (HI1 : I1 = seq 0 n1)
    (HI2 : I2 = seq 0 n2)
    (HI3 : I3 = seq 0 n3)
    (H_dom : forall idx1 idx2 : nat,
        ((idx1 / (n2 * n3))%nat = (idx2 / (n2 * n3))%nat ->
         (seq1 ((idx1 / (n2 * n3))%nat) >=
          Nat.max (seq2 (((idx1 mod (n2 * n3))%nat) / n3)%nat)
                  (seq2 (((idx2 mod (n2 * n3))%nat) / n3)%nat))%nat) /\
        (((idx1 mod (n2 * n3))%nat / n3)%nat = (((idx2 mod (n2 * n3))%nat) / n3)%nat ->
         (seq2 (((idx1 mod (n2 * n3))%nat) / n3)%nat >=
          Nat.max (seq1 ((idx1 / (n2 * n3))%nat)) (seq1 ((idx2 / (n2 * n3))%nat)))%nat) /\
        ((idx1 mod n3)%nat = (idx2 mod n3)%nat ->
         (seq3 (idx1 mod n3)%nat >=
          Nat.max (seq1 ((idx1 / (n2 * n3))%nat)) (seq1 ((idx2 / (n2 * n3))%nat)))%nat))
    (H_index_bound : forall idx1 idx2 : nat,
        (idx1 < n1 * n2 * n3)%nat -> (idx2 < n1 * n2 * n3)%nat ->
        (Z.abs_nat (Z.of_nat (idx1 / (n2 * n3)) - Z.of_nat (idx2 / (n2 * n3))) +
         Z.abs_nat (Z.of_nat (idx1 mod (n2 * n3) / n3) - Z.of_nat (idx2 mod (n2 * n3) / n3)) +
         Z.abs_nat (Z.of_nat (idx1 mod n3) - Z.of_nat (idx2 mod n3)) <= 6)%nat),
  let vals1 := map seq1 I1 in
  let vals2 := map seq2 I2 in
  let vals3 := map seq3 I3 in
  let a i := nth i vals1 0%nat in
  let b j := nth j vals2 0%nat in
  let c k := nth k vals3 0%nat in
  let maxIdx1 := fold_right Nat.max 0%nat I1 in
  let maxIdx2 := fold_right Nat.max 0%nat I2 in
  let maxIdx3 := fold_right Nat.max 0%nat I3 in
  let M := S (max (max (seq1 maxIdx1) (seq2 maxIdx2)) (seq3 maxIdx3)) in
  let phi_flat idx k :=
    phi3D_norm (a (idx / (n2 * n3))%nat)
               (b (idx mod (n2 * n3) / n3)%nat)
               (c (idx mod n3)%nat) k in
  let F_3D k :=
    Csum (fun i => Csum (fun j => Csum (fun k2 => nth (flatten_3d n2 n3 i j k2) coeffs_flat C0 *c
                                         phi3D_norm (a i) (b j) (c k2) k) n3) n2) n1 in
  let S := sum_f_R0 (fun i => sum_f_R0 (fun j => sum_f_R0 (fun k2 => Cnorm_sq (nth (flatten_3d n2 n3 i j k2) coeffs_flat C0)) (n3 - 1)) (n2 - 1)) (n1 - 1) in
  let K_C := K (INR C) in
  let K0 := (Rmax 8 ((INR C) ^ 3)) / 2 in
  let M_bound := K0 * ((1 + 4 * K_C) * (1 + 4 * K_C) * (1 + 4 * K_C) - 1) in
  ((1 - M_bound) * S <= l2_norm_sq F_3D (M - 1) <= (1 + M_bound) * S)%R.
Proof.
  intros C HCgt2 seq1 seq2 seq3 Hsparse1 Hsparse2 Hsparse3
         Hge2_1 Hge2_2 Hge2_3 I1 I2 I3 Hdup1 Hsorted1 Hdup2 Hsorted2 Hdup3 Hsorted3
         coeffs_flat n1 n2 n3 Hn1 Hn2 Hn3 Hn1_pos Hn2_pos Hn3_pos Hlen_flat
         HI1 HI2 HI3 H_dom H_index_bound.
  assert (Hc_ge2 : (C >= 2)%nat) by lia.
  assert (HCgt1_R : 1 < INR C) by (change 1 with (INR 1); apply lt_INR; lia).
  set (r := sqrt (INR C)).
  set (K0 := (Rmax 8 ((INR C) ^ 3)) / 2).
  assert (Hr_gt1 : r > 1).
  { unfold r; rewrite <- sqrt_1. apply sqrt_lt_1; [lra | apply pos_INR | exact HCgt1_R]. }
  assert (Hr_pos : r > 0) by (apply sqrt_lt_R0; apply lt_0_INR; lia).
  set (K_C := K (INR C)).
  assert (HK_pos : 0 < K_C) by (apply K_pos; exact HCgt2).
  set (M_bound := K0 * ((1 + 4 * K_C) * (1 + 4 * K_C) * (1 + 4 * K_C) - 1)).
  assert (HK0_nonneg : 0 <= K0).
  { unfold K0, Rdiv.
    apply Rmult_le_pos.
    - apply Rle_trans with 8%R.
      + lra.
      + apply Rmax_l.
    - apply Rlt_le.
      apply Rinv_0_lt_compat.
      lra. }

  set (n := (n1 * n2 * n3)%nat).
  assert (Hn_pos : (n > 0)%nat) by (apply Nat.mul_pos_pos; [apply Nat.mul_pos_pos |]; assumption).
  assert (Hlen_flat' : length coeffs_flat = n).
  { subst n; exact Hlen_flat. }

  assert (Hseq1_inc : forall x y, (x <= y)%nat -> (seq1 x <= seq1 y)%nat).
  { intros x y Hle; destruct (Nat.eq_dec x y) as [Heq | Hne].
    - subst; apply Nat.le_refl.
    - apply Nat.lt_le_incl; eapply seq_strict_growth_lt; eauto; lia. }
  assert (Hseq2_inc : forall x y, (x <= y)%nat -> (seq2 x <= seq2 y)%nat).
  { intros x y Hle; destruct (Nat.eq_dec x y) as [Heq | Hne].
    - subst; apply Nat.le_refl.
    - apply Nat.lt_le_incl; eapply seq_strict_growth_lt; eauto; lia. }
  assert (Hseq3_inc : forall x y, (x <= y)%nat -> (seq3 x <= seq3 y)%nat).
  { intros x y Hle; destruct (Nat.eq_dec x y) as [Heq | Hne].
    - subst; apply Nat.le_refl.
    - apply Nat.lt_le_incl; eapply seq_strict_growth_lt; eauto; lia. }
  set (vals1 := map seq1 I1).
  set (vals2 := map seq2 I2).
  set (vals3 := map seq3 I3).
  set (a := fun i : nat => nth i vals1 0%nat).
  set (b := fun j : nat => nth j vals2 0%nat).
  set (c := fun k : nat => nth k vals3 0%nat).
  set (maxIdx1 := fold_right Nat.max 0%nat I1).
  set (maxIdx2 := fold_right Nat.max 0%nat I2).
  set (maxIdx3 := fold_right Nat.max 0%nat I3).
  assert (Hmax1 : maxIdx1 = fold_right Nat.max 0%nat I1) by reflexivity.
  assert (Hmax2 : maxIdx2 = fold_right Nat.max 0%nat I2) by reflexivity.
  assert (Hmax3 : maxIdx3 = fold_right Nat.max 0%nat I3) by reflexivity.
  assert (HI1' : I1 = seq 0 n1) by exact HI1.
  assert (HI2' : I2 = seq 0 n2) by exact HI2.
  assert (HI3' : I3 = seq 0 n3) by exact HI3.
  set (M := S (max (max (seq1 maxIdx1) (seq2 maxIdx2)) (seq3 maxIdx3))).
  pose (phi_flat := fun idx k =>
    phi3D_norm (a (idx / (n2 * n3))%nat)
               (b (idx mod (n2 * n3) / n3)%nat)
               (c (idx mod n3)%nat) k).

  set (d1 := d_factor r).
  set (delta_triple := fun idx1 idx2 : nat =>
    let i1 := (idx1 / (n2 * n3))%nat in
    let j1 := (idx1 mod (n2 * n3) / n3)%nat in
    let k1 := (idx1 mod n3)%nat in
    let i2 := (idx2 / (n2 * n3))%nat in
    let j2 := (idx2 mod (n2 * n3) / n3)%nat in
    let k2 := (idx2 mod n3)%nat in
    K0 * (d1 i1 i2 * d1 j1 j2 * d1 k1 k2)).

  (* ---- 截断：k >= pred M 时 phi_flat idx k = C0 ---- *)
  assert (Htrunc : forall idx k, (idx < n)%nat -> (k >= Nat.pred M)%nat -> phi_flat idx k = C0).
  { intros idx k Hidx Hk; unfold phi_flat.
    set (i := (idx / (n2 * n3))%nat); set (rem := (idx mod (n2 * n3))%nat);
    set (j := (rem / n3)%nat); set (kk := (idx mod n3)%nat).
    assert (Hi : (i < n1)%nat) by (apply Nat.Div0.div_lt_upper_bound; nia).
    assert (Hrem_lt : (rem < n2 * n3)%nat)
      by (apply Nat.mod_upper_bound; nia).
    assert (Hj : (j < n2)%nat).
    { apply (Nat.Div0.div_lt_upper_bound rem n3 n2).
      apply Nat.lt_le_trans with (n2 * n3)%nat; [exact Hrem_lt | nia]. }
    assert (Hk2 : (kk < n3)%nat) by (apply Nat.mod_upper_bound; lia).
    unfold phi3D_norm.
    assert (Ha_le_max : (a i <= max (max (seq1 maxIdx1) (seq2 maxIdx2)) (seq3 maxIdx3))%nat).
    { unfold a, vals1.
      assert (Hi_len : (i < length I1)%nat) by (rewrite <- Hn1; exact Hi).
      rewrite (H_nth_map nat nat seq1 I1 0%nat 0%nat i Hi_len).
      apply Nat.le_trans with (seq1 maxIdx1).
      - apply Hseq1_inc; eapply fold_right_max_ge; apply nth_In; exact Hi_len.
      - apply Nat.le_trans with (max (seq1 maxIdx1) (seq2 maxIdx2)).
        + apply Nat.le_max_l.
        + apply Nat.le_max_l. }
    assert (Hb_le_max : (b j <= max (max (seq1 maxIdx1) (seq2 maxIdx2)) (seq3 maxIdx3))%nat).
    { unfold b, vals2.
      assert (Hj_len : (j < length I2)%nat) by (rewrite <- Hn2; exact Hj).
      rewrite (H_nth_map nat nat seq2 I2 0%nat 0%nat j Hj_len).
      apply Nat.le_trans with (seq2 maxIdx2).
      - apply Hseq2_inc; eapply fold_right_max_ge; apply nth_In; exact Hj_len.
      - apply Nat.le_trans with (max (seq1 maxIdx1) (seq2 maxIdx2)).
        + apply Nat.le_max_r.
        + apply Nat.le_max_l. }
    assert (Hc_le_max : (c kk <= max (max (seq1 maxIdx1) (seq2 maxIdx2)) (seq3 maxIdx3))%nat).
    { unfold c, vals3.
      assert (Hk_len : (kk < length I3)%nat) by (rewrite <- Hn3; exact Hk2).
      rewrite (H_nth_map nat nat seq3 I3 0%nat 0%nat kk Hk_len).
      apply Nat.le_trans with (seq3 maxIdx3).
      - apply Hseq3_inc; eapply fold_right_max_ge; apply nth_In; exact Hk_len.
      - apply Nat.le_max_r. }
    assert (Hmax_le_k : (max (max (seq1 maxIdx1) (seq2 maxIdx2)) (seq3 maxIdx3) <= k)%nat).
    { unfold M in Hk; lia. }
    assert (Ha_le_k : (a i <= k)%nat) by lia.
    assert (Hb_le_k : (b j <= k)%nat) by lia.
    assert (Hc_le_k : (c kk <= k)%nat) by lia.
    unfold kk in Hc_le_k |- *.
    rewrite (psi_ge_n_zero (c (idx mod n3)%nat) k Hc_le_k).
    rewrite (psi_ge_n_zero (b j) k Hb_le_k).
    rewrite (psi_ge_n_zero (a i) k Ha_le_k).
    repeat rewrite Cmul_0_l.
    apply Cmul_0_r. }

  (* ---- 自归一：l2_norm_sq (phi_flat idx) (pred M) = 1 ---- *)
  assert (Hnorm1 : forall idx, (idx < n)%nat -> l2_norm_sq (phi_flat idx) (Nat.pred M) = 1%R).
  { intros idx Hlt; unfold phi_flat.
    set (i := (idx / (n2 * n3))%nat); set (rem := (idx mod (n2 * n3))%nat);
    set (j := (rem / n3)%nat); set (kk := (idx mod n3)%nat).
    assert (Hi : (i < n1)%nat) by (apply Nat.Div0.div_lt_upper_bound; nia).
    assert (Hrem_lt : (rem < n2 * n3)%nat)
      by (apply Nat.mod_upper_bound; nia).
    assert (Hj : (j < n2)%nat).
    { apply (Nat.Div0.div_lt_upper_bound rem n3 n2).
      apply Nat.lt_le_trans with (n2 * n3)%nat; [exact Hrem_lt | nia]. }
    assert (Hk : (kk < n3)%nat) by (apply Nat.mod_upper_bound; lia).
    unfold phi3D_norm.
    assert (Ha_ge2 : (a i >= 2)%nat).
    { unfold a, vals1. rewrite Hn1 in Hi.
      rewrite (H_nth_map nat nat seq1 I1 0%nat 0%nat i Hi). apply Hge2_1. }
    assert (Hb_ge2 : (b j >= 2)%nat).
    { unfold b, vals2. rewrite Hn2 in Hj.
      rewrite (H_nth_map nat nat seq2 I2 0%nat 0%nat j Hj). apply Hge2_2. }
    assert (Hc3_ge2 : (c kk >= 2)%nat).
    { unfold c, vals3. rewrite Hn3 in Hk.
      rewrite (H_nth_map nat nat seq3 I3 0%nat 0%nat kk Hk). apply Hge2_3. }
    set (g := gamma3 (a i) (b j) (c kk)).
    assert (Hg_pos : 0 < g) by (apply gamma3_pos; assumption).
    assert (Ha_le_max : (a i <= max (max (seq1 maxIdx1) (seq2 maxIdx2)) (seq3 maxIdx3))%nat).
    { unfold a, vals1. rewrite Hn1 in Hi.
      rewrite (H_nth_map nat nat seq1 I1 0%nat 0%nat i Hi).
      apply Nat.le_trans with (seq1 maxIdx1).
      - apply Hseq1_inc; eapply fold_right_max_ge; apply nth_In; exact Hi.
      - apply Nat.le_trans with (max (seq1 maxIdx1) (seq2 maxIdx2)).
        + apply Nat.le_max_l.
        + apply Nat.le_max_l. }
    assert (Hb_le_max : (b j <= max (max (seq1 maxIdx1) (seq2 maxIdx2)) (seq3 maxIdx3))%nat).
    { unfold b, vals2. rewrite Hn2 in Hj.
      rewrite (H_nth_map nat nat seq2 I2 0%nat 0%nat j Hj).
      apply Nat.le_trans with (seq2 maxIdx2).
      - apply Hseq2_inc; eapply fold_right_max_ge; apply nth_In; exact Hj.
      - apply Nat.le_trans with (max (seq1 maxIdx1) (seq2 maxIdx2)).
        + apply Nat.le_max_r.
        + apply Nat.le_max_l. }
    assert (Hc_le_max : (c kk <= max (max (seq1 maxIdx1) (seq2 maxIdx2)) (seq3 maxIdx3))%nat).
    { unfold c, vals3. rewrite Hn3 in Hk.
      rewrite (H_nth_map nat nat seq3 I3 0%nat 0%nat kk Hk).
      apply Nat.le_trans with (seq3 maxIdx3).
      - apply Hseq3_inc; eapply fold_right_max_ge; apply nth_In; exact Hk.
      - apply Nat.le_max_r. }
    assert (Ha_lt_M : (a i < M)%nat) by (unfold M; apply Nat.lt_succ_r; exact Ha_le_max).
    assert (Hb_lt_M : (b j < M)%nat) by (unfold M; apply Nat.lt_succ_r; exact Hb_le_max).
    assert (Hc_lt_M : (c kk < M)%nat) by (unfold M; apply Nat.lt_succ_r; exact Hc_le_max).
    assert (Hmin3_lt_M : (Nat.min (Nat.min (a i) (b j)) (c kk) < M)%nat).
    { apply Nat.le_lt_trans with (a i).
      - apply Nat.le_trans with (Nat.min (a i) (b j)).
        + apply Nat.le_min_l.
        + apply Nat.le_min_l.
      - exact Ha_lt_M. }
    set (min3 := Nat.min (Nat.min (a i) (b j)) (c kk)).
    set (F m := Cof_real (/ g) *c (psi (a i) m *c psi (b j) m *c psi (c kk) m)).
    assert (HnormF : l2_norm_sq F (Nat.pred M) = 1%R).
    { unfold l2_norm_sq, F.
      assert (Heq : forall m, Cnorm_sq (Cof_real (/ g) *c (psi (a i) m *c psi (b j) m *c psi (c kk) m))
                     = (/ g) ^ 2 * (Cnorm_sq (psi (a i) m) * Cnorm_sq (psi (b j) m) * Cnorm_sq (psi (c kk) m))).
      { intro m.
        rewrite Cnorm_sq_mult, (Cnorm_sq_mult (psi (a i) m *c psi (b j) m) (psi (c kk) m)),
                (Cnorm_sq_mult (psi (a i) m) (psi (b j) m)).
        assert (Hcof_sq : Cnorm_sq (Cof_real ((/ g)%R)) = ((/ g) ^ 2)%R).
        { unfold Cof_real, Cnorm_sq, Rsqr; simpl; ring. }
        rewrite Hcof_sq; reflexivity. }
      rewrite (sum_f_R0_ext _ (fun m => (/ g) ^ 2 *
                 (Cnorm_sq (psi (a i) m) * Cnorm_sq (psi (b j) m) * Cnorm_sq (psi (c kk) m)))).
      - rewrite (sum_f_R0_scal_l ((/ g) ^ 2)
                   (fun m => Cnorm_sq (psi (a i) m) * Cnorm_sq (psi (b j) m) * Cnorm_sq (psi (c kk) m))
                   (Nat.pred M)).
        set (f3 := fun m => Cnorm_sq (psi (a i) m) * Cnorm_sq (psi (b j) m) * Cnorm_sq (psi (c kk) m)).
        (* 截断到 min3：m >= min3 时至少一个 psi 为 0 *)
        assert (Hzero_above : forall m, (min3 <= m)%nat -> f3 m = 0%R).
        { intros m Hm.
          unfold min3 in Hm.
          destruct (Nat.min_spec (a i) (b j)) as [[Hlt_ab Hmin_ab] | [Hle_ba Hmin_ba]];
            destruct (Nat.min_spec (Nat.min (a i) (b j)) (c kk)) as [[Hlt_abc Hmin_abc] | [Hle_c Hmin_c]];
            try rewrite Hmin_abc in Hm;
            try rewrite Hmin_ab in Hm;
            try rewrite Hmin_ba in Hm;
            try rewrite Hmin_c in Hm;
            unfold f3.
          - assert (H : (a i <= m)%nat) by lia.
            rewrite (psi_ge_n_zero (a i) m H), Cnorm_sq_zero; simpl; ring.
          - assert (H : (c kk <= m)%nat) by lia.
            rewrite (psi_ge_n_zero (c kk) m H), Cnorm_sq_zero; simpl; ring.
          - assert (H : (b j <= m)%nat) by lia.
            rewrite (psi_ge_n_zero (b j) m H), Cnorm_sq_zero; simpl; ring.
          - assert (H : (c kk <= m)%nat) by lia.
            rewrite (psi_ge_n_zero (c kk) m H), Cnorm_sq_zero; simpl; ring. }
        assert (Hmin3_pos : (0 < min3)%nat).
        { unfold min3; apply Nat.min_glb_lt; [| lia]. apply Nat.min_glb_lt; lia. }
        assert (Hsum_trunc : sum_f_R0 f3 (Nat.pred M) = sum_f_R0 f3 (Nat.pred min3)).
        { assert (Ht : sum_f_R0 f3 (Nat.pred M) = sum_f_R0 f3 min3).
          { apply sum_f_R0_trunc_tail with (M := min3) (N := Nat.pred M); [lia |].
            intros m [Hm1 Hm2]; apply Hzero_above; lia. }
          rewrite Ht.
          assert (Hf3_min3 : f3 min3 = 0%R) by (apply Hzero_above; lia).
          assert (Hsucc : min3 = S (Nat.pred min3)) by (symmetry; apply Nat.succ_pred; apply Nat.neq_0_lt_0; exact Hmin3_pos).
          rewrite Hsucc, (sum_f_R0_S f3 (Nat.pred min3)).
          rewrite <- Hsucc, Hf3_min3; ring. }
        rewrite Hsum_trunc.
        set (cst3 := (1 / INR (a i)) * (1 / INR (b j)) * (1 / INR (c kk))).
        assert (Hterm_eq : forall m, (m < min3)%nat -> f3 m = cst3).
        { intros m Hm_min.
          assert (Hm_ai : (m < a i)%nat) by (unfold min3 in Hm_min; nia).
          assert (Hm_bj : (m < b j)%nat) by (unfold min3 in Hm_min; nia).
          assert (Hm_ck : (m < c kk)%nat) by (unfold min3 in Hm_min; nia).
          unfold f3.
          rewrite (Cnorm_sq_psi_exact (a i) m), (Cnorm_sq_psi_exact (b j) m), (Cnorm_sq_psi_exact (c kk) m).
          assert (Hltb_ai : (m <? a i)%nat = true) by (apply Nat.ltb_lt; exact Hm_ai).
          assert (Hltb_bj : (m <? b j)%nat = true) by (apply Nat.ltb_lt; exact Hm_bj).
          assert (Hltb_ck : (m <? c kk)%nat = true) by (apply Nat.ltb_lt; exact Hm_ck).
          rewrite Hltb_ai, Hltb_bj, Hltb_ck.
          unfold cst3, Rdiv; field.
          split; [| split]; apply Rgt_not_eq; apply lt_0_INR; lia. }
        assert (Hsum_cst : sum_f_R0 f3 (Nat.pred min3) = sum_f_R0 (fun _ => cst3) (Nat.pred min3)).
        { apply sum_f_R0_ext; intros m Hm; apply Hterm_eq; lia. }
        rewrite Hsum_cst.
        rewrite (sum_f_R0_const cst3 (Nat.pred min3)).
          unfold cst3, min3, g.
          field_simplify.
          set (m3 := Nat.min (Nat.min (a i) (b j)) (c kk)).
          assert (Hm3_pos : (0 < m3)%nat) by (unfold m3; apply Nat.min_glb_lt; [| lia]; apply Nat.min_glb_lt; lia).
          rewrite (Nat.succ_pred m3 (proj2 (Nat.neq_0_lt_0 m3) Hm3_pos)).
          subst m3.
          assert (Hpow2 : (gamma3 (a i) (b j) (c kk) ^ 2)%R = gamma3 (a i) (b j) (c kk) * gamma3 (a i) (b j) (c kk)).
          { unfold pow; simpl; ring. }
          rewrite Hpow2.
          rewrite (gamma3_sq (a i) (b j) (c kk) Ha_ge2 Hb_ge2 Hc3_ge2).
          field.
          all: try (repeat split).
          all: try (apply Rgt_not_eq; apply lt_0_INR; lia).
          all: try (apply Rgt_not_eq; apply gamma3_pos; [exact Ha_ge2 | exact Hb_ge2 | exact Hc3_ge2]).
          all: try (intros i0 Hle; apply Heq). }
    exact HnormF. }

  (* ---- delta 对称 / 非负 ---- *)
  assert (d_factor_sym : forall i j, d_factor r i j = d_factor r j i).
  { intros i j; unfold d_factor.
    destruct (Nat.eq_dec i j) as [Heq | Hneq].
    - subst i; reflexivity.
    - assert (Hij : (i =? j)%nat = false) by (apply Nat.eqb_neq; exact Hneq).
      assert (Hji : (j =? i)%nat = false) by (apply Nat.eqb_neq; auto).
      rewrite Hij, Hji.
      f_equal; f_equal.
      replace (Z.of_nat j - Z.of_nat i)%Z with (- (Z.of_nat i - Z.of_nat j))%Z by lia.
      rewrite Z_abs_nat_opp; reflexivity. }
  assert (d_factor_nonneg : forall i j, 0 <= d_factor r i j).
  { intros i j; unfold d_factor.
    destruct (Nat.eqb_spec i j) as [Heq | Hneq].
    - subst i; lra.
    - apply Rlt_le; apply Rdiv_lt_0_compat; [lra | apply pow_lt; exact Hr_pos]. }

  assert (Hdelta_sym : forall (i j : nat), (i < n)%nat -> (j < n)%nat -> delta_triple i j = delta_triple j i).
  { intros idx1 idx2 Hi Hj; unfold delta_triple.
    repeat (f_equal; try (apply d_factor_sym); try reflexivity). }
  assert (Hdelta_nonneg : forall (i j : nat), (i < n)%nat -> (j < n)%nat -> 0 <= delta_triple i j).
  { intros idx1 idx2 Hi Hj; unfold delta_triple, d1.
    apply Rmult_le_pos.
    - exact HK0_nonneg.
    - repeat (apply Rmult_le_pos; try apply d_factor_nonneg). }

  (* ---- 衰减：由 Hdecay_engine 供给 ---- *)
  assert (Hdecay : forall idx1 idx2, idx1 <> idx2 -> (idx1 < n)%nat -> (idx2 < n)%nat ->
              Cnorm (Csum (fun k => phi_flat idx1 k *c Cconj (phi_flat idx2 k)) (Nat.pred M))
              <= delta_triple idx1 idx2).
  { intros idx1 idx2 Hneq Hlt1 Hlt2.
    unfold delta_triple, phi_flat.
    apply (phi_flat_decay_general_3d C HCgt2 seq1 seq2 seq3 Hsparse1 Hsparse2 Hsparse3
             Hge2_1 Hge2_2 Hge2_3 I1 I2 I3 n1 n2 n3 Hn1 Hn2 Hn3
             idx1 idx2 Hneq Hlt1 Hlt2
             (H_index_bound idx1 idx2 Hlt1 Hlt2)). }

  (* ---- 行和：sum_f_R0_flatten_3d + triple_prod_row_sum_decomp + d_factor_row_sum_le_4K ---- *)
  assert (Hrow_sum : forall idx, (idx < n)%nat ->
              sum_f_R0 (fun jdx => if Nat.eq_dec idx jdx then 0%R else delta_triple idx jdx) (Nat.pred n)
              <= M_bound).
  { intros idx Hidx.
    set (i0 := (idx / (n2 * n3))%nat); set (rem0 := (idx mod (n2 * n3))%nat);
    set (j0 := (rem0 / n3)%nat); set (k0 := (idx mod n3)%nat).
    assert (Hi0 : (i0 < n1)%nat) by (apply Nat.Div0.div_lt_upper_bound; nia).
    assert (Hrem0_lt : (rem0 < n2 * n3)%nat)
      by (apply Nat.mod_upper_bound; nia).
    assert (Hj0 : (j0 < n2)%nat).
    { apply (Nat.Div0.div_lt_upper_bound rem0 n3 n2).
      apply Nat.lt_le_trans with (n2 * n3)%nat; [exact Hrem0_lt | nia]. }
    assert (Hk0 : (k0 < n3)%nat) by (apply Nat.mod_upper_bound; lia).
    assert (Hd1_diag : forall i, d1 i i = 1%R).
    { intros i; unfold d1, d_factor, r; rewrite Nat.eqb_refl; reflexivity. }
    assert (Hflat : sum_f_R0 (fun jdx => if Nat.eq_dec idx jdx then 0%R else delta_triple idx jdx) (Nat.pred n)
        = K0 * sum_f_R0 (fun i => sum_f_R0 (fun j => sum_f_R0 (fun k =>
              if andb (andb (i =? i0)%nat (j =? j0)%nat)%nat
                     (k =? k0)%nat
              then 0%R
              else d1 i0 i * d1 j0 j * d1 k0 k) (n3 - 1)) (n2 - 1)) (n1 - 1)).
    { rewrite (sum_f_R0_ext (fun jdx => if Nat.eq_dec idx jdx then 0%R else delta_triple idx jdx)
                            (fun jdx => K0 * (if Nat.eq_dec idx jdx then 0%R
                                              else d1 i0 (jdx / (n2 * n3))%nat
                                                   * d1 j0 ((jdx mod (n2 * n3)) / n3)%nat
                                                   * d1 k0 (jdx mod n3)%nat))
                            (Nat.pred n))
        by (intros jdx Hjdx; destruct (Nat.eq_dec idx jdx) as [Heq | Hne];
            [ subst jdx; simpl; rewrite Rmult_0_r; reflexivity
            | simpl; unfold delta_triple, d1; cbv zeta; reflexivity ]).
      rewrite (sum_f_R0_scal_l K0
            (fun jdx => if Nat.eq_dec idx jdx then 0%R
                        else d1 i0 (jdx / (n2 * n3))%nat
                             * d1 j0 ((jdx mod (n2 * n3)) / n3)%nat
                             * d1 k0 (jdx mod n3)%nat)
            (Nat.pred n)).
      rewrite (sum_f_R0_ext (fun jdx => if Nat.eq_dec idx jdx then 0%R
                                        else d1 i0 (jdx / (n2 * n3))%nat
                                             * d1 j0 ((jdx mod (n2 * n3)) / n3)%nat
                                             * d1 k0 (jdx mod n3)%nat)
                            (fun jdx => if andb (andb (jdx / (n2 * n3) =? i0)%nat
                                                      ((jdx mod (n2 * n3)) / n3 =? j0)%nat)%nat
                                             ((jdx mod (n2 * n3)) mod n3 =? k0)%nat
                                        then 0%R
                                        else d1 i0 (jdx / (n2 * n3))%nat
                                             * d1 j0 ((jdx mod (n2 * n3)) / n3)%nat
                                             * d1 k0 ((jdx mod (n2 * n3)) mod n3)%nat)
                            (Nat.pred n))
        by (intros jdx Hjdx; destruct (Nat.eq_dec idx jdx) as [Heq | Hne];
            [ subst jdx; unfold i0, j0, k0, rem0;
              rewrite (nat_mod_n3_of_mod_n23 idx n2 n3 Hn2_pos Hn3_pos);
              rewrite !Nat.eqb_refl; simpl; reflexivity
            | assert (Hcf : andb (andb (jdx / (n2 * n3) =? i0)%nat
                                         ((jdx mod (n2 * n3)) / n3 =? j0)%nat)%nat
                                ((jdx mod (n2 * n3)) mod n3 =? k0)%nat = false);
              [ destruct (Nat.eq_dec (jdx / (n2 * n3))%nat i0) as [Ha | Hna];
                [ rewrite Ha, Nat.eqb_refl
                | rewrite (proj2 (Nat.eqb_neq (jdx / (n2 * n3))%nat i0) Hna); simpl; reflexivity ];
                destruct (Nat.eq_dec ((jdx mod (n2 * n3)) / n3)%nat j0) as [Hb | Hnb];
                [ rewrite Hb, Nat.eqb_refl
                | rewrite (proj2 (Nat.eqb_neq ((jdx mod (n2 * n3)) / n3)%nat j0) Hnb); simpl; reflexivity ];
                destruct (Nat.eq_dec ((jdx mod (n2 * n3)) mod n3)%nat k0) as [Hc | Hnc];
                [ rewrite Hc, Nat.eqb_refl
                | rewrite (proj2 (Nat.eqb_neq ((jdx mod (n2 * n3)) mod n3)%nat k0) Hnc); simpl; reflexivity ];
                assert (Heq_triple : jdx = idx);
                [ rewrite (nat_div_mod_3d jdx n2 n3 Hn2_pos Hn3_pos);
                  rewrite (nat_div_mod_3d idx n2 n3 Hn2_pos Hn3_pos);
                  rewrite Ha, Hb, Hc;
                  rewrite (nat_mod_n3_of_mod_n23 idx n2 n3 Hn2_pos Hn3_pos);
                  reflexivity
                | exfalso; apply Hne; exact (eq_sym Heq_triple) ]
              | rewrite Hcf; rewrite <- (nat_mod_n3_of_mod_n23 jdx n2 n3 Hn2_pos Hn3_pos);
                reflexivity ] ]).
      rewrite (sum_f_R0_ext (fun jdx => if andb (andb (jdx / (n2 * n3) =? i0)%nat
                                                      ((jdx mod (n2 * n3)) / n3 =? j0)%nat)%nat
                                             ((jdx mod (n2 * n3)) mod n3 =? k0)%nat
                                        then 0%R
                                        else d1 i0 (jdx / (n2 * n3))%nat
                                             * d1 j0 ((jdx mod (n2 * n3)) / n3)%nat
                                             * d1 k0 ((jdx mod (n2 * n3)) mod n3)%nat)
                            (fun jdx => let i := (jdx / (n2 * n3))%nat in
                                        let rem := (jdx mod (n2 * n3))%nat in
                                        let j := (rem / n3)%nat in
                                        let k := (rem mod n3)%nat in
                                        if andb (andb (i =? i0)%nat (j =? j0)%nat)%nat
                                               (k =? k0)%nat
                                        then 0%R
                                        else d1 i0 i * d1 j0 j * d1 k0 k)
                            (Nat.pred n))
        by (intros jdx Hjdx; cbv beta zeta; reflexivity).
      assert (Hbound : (Nat.pred n = n1 * n2 * n3 - 1)%nat).
      { subst n. rewrite <- Nat.sub_1_r. reflexivity. }
      rewrite Hbound.
      rewrite (sum_f_R0_flatten_3d n1 n2 n3 Hn1_pos Hn2_pos Hn3_pos
            (fun i j k => if andb (andb (i =? i0)%nat (j =? j0)%nat)%nat
                                  (k =? k0)%nat
                          then 0%R
                          else d1 i0 i * d1 j0 j * d1 k0 k)).
      reflexivity. }
    rewrite Hflat.
    rewrite !Nat.sub_1_r.
    pose proof (triple_prod_row_sum_decomp n1 n2 n3 i0 j0 k0 d1 d1 d1 Hi0 Hj0 Hk0 Hd1_diag Hd1_diag Hd1_diag) as H_decomp.
    rewrite H_decomp.
    set (S1 := sum_f_R0 (fun i => if (i =? i0)%nat then 1%R else d1 i0 i) (Nat.pred n1)).
    set (S2 := sum_f_R0 (fun j => if (j =? j0)%nat then 1%R else d1 j0 j) (Nat.pred n2)).
    set (S3 := sum_f_R0 (fun k => if (k =? k0)%nat then 1%R else d1 k0 k) (Nat.pred n3)).
    assert (HS1 : S1 <= 1 + 4 * K_C).
    { unfold S1.
      assert (Htmp : sum_f_R0 (fun i => if Nat.eq_dec i0 i then 0%R else d1 i0 i) (Nat.pred n1) <= 4 * K_C)
        by (apply d_factor_row_sum_le_4K with (C := C); assumption).
      assert (Hrel : sum_f_R0 (fun i => if (i =? i0)%nat then 1%R else d1 i0 i) (Nat.pred n1)
                    = sum_f_R0 (fun i => if Nat.eq_dec i0 i then 0%R else d1 i0 i) (Nat.pred n1) + 1%R).
      { rewrite (sum_f_R0_eq_1_plus_rest n1 i0 (fun i => if (i =? i0)%nat then 1%R else d1 i0 i)).
        - assert (Heq : forall i, (i <= Nat.pred n1)%nat ->
                    (if eq_nat_dec i0 i then 0%R else (if (i =? i0)%nat then 1%R else d1 i0 i))
                    = (if Nat.eq_dec i0 i then 0%R else d1 i0 i)).
          { intros i _. destruct (Nat.eq_dec i0 i) as [-> | Hne]; simpl; [reflexivity |].
            assert (Hb : (i =? i0)%nat = false) by (apply Nat.eqb_neq; intro Heq; apply Hne; symmetry; exact Heq).
            rewrite Hb. reflexivity. }
          rewrite (sum_f_R0_ext
                     (fun i => if eq_nat_dec i0 i then 0%R
                               else (if (i =? i0)%nat then 1%R else d1 i0 i))
                     (fun i => if Nat.eq_dec i0 i then 0%R else d1 i0 i)
                     (Nat.pred n1)).
          + ring.
          + exact Heq.
        - exact Hi0.
        - simpl. rewrite Nat.eqb_refl. reflexivity. }
      rewrite Hrel. replace (1 + 4 * K_C) with (4 * K_C + 1) by ring.
      apply Rplus_le_compat_r; exact Htmp. }
    assert (HS2 : S2 <= 1 + 4 * K_C).
    { unfold S2.
      assert (Htmp : sum_f_R0 (fun j => if Nat.eq_dec j0 j then 0%R else d1 j0 j) (Nat.pred n2) <= 4 * K_C)
        by (apply d_factor_row_sum_le_4K with (C := C); assumption).
      assert (Hrel : sum_f_R0 (fun j => if (j =? j0)%nat then 1%R else d1 j0 j) (Nat.pred n2)
                    = sum_f_R0 (fun j => if Nat.eq_dec j0 j then 0%R else d1 j0 j) (Nat.pred n2) + 1%R).
      { rewrite (sum_f_R0_eq_1_plus_rest n2 j0 (fun j => if (j =? j0)%nat then 1%R else d1 j0 j)).
        - assert (Heq : forall j, (j <= Nat.pred n2)%nat ->
                    (if eq_nat_dec j0 j then 0%R else (if (j =? j0)%nat then 1%R else d1 j0 j))
                    = (if Nat.eq_dec j0 j then 0%R else d1 j0 j)).
          { intros j _. destruct (Nat.eq_dec j0 j) as [-> | Hne]; simpl; [reflexivity |].
            assert (Hb : (j =? j0)%nat = false) by (apply Nat.eqb_neq; intro Heq; apply Hne; symmetry; exact Heq).
            rewrite Hb. reflexivity. }
          rewrite (sum_f_R0_ext
                     (fun j => if eq_nat_dec j0 j then 0%R
                               else (if (j =? j0)%nat then 1%R else d1 j0 j))
                     (fun j => if Nat.eq_dec j0 j then 0%R else d1 j0 j)
                     (Nat.pred n2)).
          + ring.
          + exact Heq.
        - exact Hj0.
        - simpl. rewrite Nat.eqb_refl. reflexivity. }
      rewrite Hrel. replace (1 + 4 * K_C) with (4 * K_C + 1) by ring.
      apply Rplus_le_compat_r; exact Htmp. }
    assert (HS3 : S3 <= 1 + 4 * K_C).
    { unfold S3.
      assert (Htmp : sum_f_R0 (fun k => if Nat.eq_dec k0 k then 0%R else d1 k0 k) (Nat.pred n3) <= 4 * K_C)
        by (apply d_factor_row_sum_le_4K with (C := C); assumption).
      assert (Hrel : sum_f_R0 (fun k => if (k =? k0)%nat then 1%R else d1 k0 k) (Nat.pred n3)
                    = sum_f_R0 (fun k => if Nat.eq_dec k0 k then 0%R else d1 k0 k) (Nat.pred n3) + 1%R).
      { rewrite (sum_f_R0_eq_1_plus_rest n3 k0 (fun k => if (k =? k0)%nat then 1%R else d1 k0 k)).
        - assert (Heq : forall k, (k <= Nat.pred n3)%nat ->
                    (if eq_nat_dec k0 k then 0%R else (if (k =? k0)%nat then 1%R else d1 k0 k))
                    = (if Nat.eq_dec k0 k then 0%R else d1 k0 k)).
          { intros k _. destruct (Nat.eq_dec k0 k) as [-> | Hne]; simpl; [reflexivity |].
            assert (Hb : (k =? k0)%nat = false) by (apply Nat.eqb_neq; intro Heq; apply Hne; symmetry; exact Heq).
            rewrite Hb. reflexivity. }
          rewrite (sum_f_R0_ext
                     (fun k => if eq_nat_dec k0 k then 0%R
                               else (if (k =? k0)%nat then 1%R else d1 k0 k))
                     (fun k => if Nat.eq_dec k0 k then 0%R else d1 k0 k)
                     (Nat.pred n3)).
          + ring.
          + exact Heq.
        - exact Hk0.
        - simpl. rewrite Nat.eqb_refl. reflexivity. }
      rewrite Hrel. replace (1 + 4 * K_C) with (4 * K_C + 1) by ring.
      apply Rplus_le_compat_r; exact Htmp. }
    unfold M_bound, K0.

    (* 局部引理：有限和逐项非负，则和为非负 *)
    assert (sum_f_R0_nonneg_local :
      forall (f : nat -> R) (N : nat),
        (forall i, 0 <= f i) -> 0 <= sum_f_R0 f N).
    {
      intros f N Hf.
      induction N as [| m IH].
      - simpl; apply Hf.
      - rewrite sum_f_R0_S.
        apply Rle_trans with (0 + 0).
        + lra.
        + apply Rplus_le_compat.
          * apply IH.
          * apply Hf.
    }

    assert (HS1_nonneg : 0 <= S1).
    {
      unfold S1.
      apply sum_f_R0_nonneg_local.
      intros m.
      unfold d1.
      destruct (Nat.eq_dec m i0) as [-> | Hm].
      - rewrite Nat.eqb_refl; lra.
      - assert (Hb : (m =? i0)%nat = false) by (apply Nat.eqb_neq; exact Hm).
        rewrite Hb.
        apply d_factor_nonneg.
    }

    assert (HS2_nonneg : 0 <= S2).
    {
      unfold S2.
      apply sum_f_R0_nonneg_local.
      intros m.
      unfold d1.
      destruct (Nat.eq_dec m j0) as [-> | Hm].
      - rewrite Nat.eqb_refl; lra.
      - assert (Hb : (m =? j0)%nat = false) by (apply Nat.eqb_neq; exact Hm).
        rewrite Hb.
        apply d_factor_nonneg.
    }

    assert (HS3_nonneg : 0 <= S3).
    {
      unfold S3.
      apply sum_f_R0_nonneg_local.
      intros m.
      unfold d1.
      destruct (Nat.eq_dec m k0) as [-> | Hm].
      - rewrite Nat.eqb_refl; lra.
      - assert (Hb : (m =? k0)%nat = false) by (apply Nat.eqb_neq; exact Hm).
        rewrite Hb.
        apply d_factor_nonneg.
    }

    assert (Hprod_le :
      S1 * S2 * S3 - 1
      <= (1 + 4 * K_C) * (1 + 4 * K_C) * (1 + 4 * K_C) - 1).
    {
      apply Rplus_le_compat_r.
      assert (H12 :
        S1 * S2 <= (1 + 4 * K_C) * (1 + 4 * K_C)).
      {
        apply Rmult_le_compat.
        - exact HS1_nonneg.
        - exact HS2_nonneg.
        - exact HS1.
        - exact HS2.
      }
      apply Rmult_le_compat.
      - apply Rmult_le_pos; [exact HS1_nonneg | exact HS2_nonneg].
      - exact HS3_nonneg.
      - exact H12.
      - exact HS3.
    }

    apply Rmult_le_compat_l.
    - exact HK0_nonneg.
    - exact Hprod_le.
    }
    
  (* ---- 调用维度无关骨架 ---- *)
  assert (HM_pos : (M > 0)%nat) by (unfold M; lia).
  pose proof (abstract_unconditional_basis n phi_flat M M_bound delta_triple HM_pos Htrunc Hnorm1
                Hdelta_sym Hdelta_nonneg Hdecay Hrow_sum coeffs_flat Hlen_flat') as H_abs.

  (* ---- 收尾：把扁平 F / S 重排成三维嵌套形式 ---- *)
  assert (HF_flat_eq : forall k,
    Csum (fun i => Csum (fun j => Csum (fun k2 =>
      nth (flatten_3d n2 n3 i j k2) coeffs_flat C0 *c
      phi3D_norm (a i) (b j) (c k2) k) n3) n2) n1
    = Csum (fun idx : nat => nth idx coeffs_flat C0 *c phi_flat idx k) n).
  { intros k.
    rewrite <- (Csum_flatten_3d n1 n2 n3 Hn2_pos Hn3_pos
                  (fun i j k2 => nth (flatten_3d n2 n3 i j k2) coeffs_flat C0 *c
                              phi3D_norm (a i) (b j) (c k2) k)).
    apply Csum_ext; intros idx Hidx.
    unfold phi_flat.

    assert (Hflat_idx : flatten_3d n2 n3 (idx / (n2 * n3))%nat
                                      ((idx mod (n2 * n3)) / n3)%nat
                                      (idx mod n3)%nat = idx).
    {
      unfold flatten_3d.
      rewrite <- (nat_mod_n3_of_mod_n23 idx n2 n3 Hn2_pos Hn3_pos).
      rewrite (Nat.mul_add_distr_r (idx / (n2 * n3) * n2)%nat
                                  (idx mod (n2 * n3) / n3)%nat n3).
      rewrite <- (Nat.mul_assoc (idx / (n2 * n3))%nat n2 n3).
      symmetry.
      exact (nat_div_mod_3d idx n2 n3 Hn2_pos Hn3_pos).
    }
    rewrite !(nat_mod_n3_of_mod_n23 idx n2 n3 Hn2_pos Hn3_pos).
    rewrite Hflat_idx.
    reflexivity.
  }


  assert (HS_flat_eq :
    sum_f_R0 (fun i => sum_f_R0 (fun j => sum_f_R0
      (fun k2 => Cnorm_sq (nth (flatten_3d n2 n3 i j k2) coeffs_flat C0)) (n3 - 1)) (n2 - 1)) (n1 - 1)
    = sum_f_R0 (fun idx : nat => Cnorm_sq (nth idx coeffs_flat C0)) (Nat.pred (n1 * n2 * n3))).
  {
    rewrite <- (sum_f_R0_flatten_3d n1 n2 n3 Hn1_pos Hn2_pos Hn3_pos
                  (fun i j k2 => Cnorm_sq (nth (flatten_3d n2 n3 i j k2) coeffs_flat C0))).

    (* 统一求和上界 *)
    rewrite (Nat.sub_1_r (n1 * n2 * n3)%nat).

    apply sum_f_R0_ext; intros idx0 Hlt.
    assert (Hflat_idx0 : flatten_3d n2 n3 (idx0 / (n2 * n3))%nat
                                      ((idx0 mod (n2 * n3)) / n3)%nat
                                      (idx0 mod n3)%nat = idx0).
    {
      unfold flatten_3d.
      rewrite <- (nat_mod_n3_of_mod_n23 idx0 n2 n3 Hn2_pos Hn3_pos).
      rewrite (Nat.mul_add_distr_r (idx0 / (n2 * n3) * n2)%nat
                                  (idx0 mod (n2 * n3) / n3)%nat n3).
      rewrite <- (Nat.mul_assoc (idx0 / (n2 * n3))%nat n2 n3).
      symmetry.
      exact (nat_div_mod_3d idx0 n2 n3 Hn2_pos Hn3_pos).
    }
    simpl.
    rewrite (nat_mod_n3_of_mod_n23 idx0 n2 n3 Hn2_pos Hn3_pos).
    rewrite Hflat_idx0.
    reflexivity.
    }
    
  assert (HM_pred_eq : Nat.pred M = (M - 1)%nat) by (unfold M; lia).

  assert (H_final : (1 - M_bound) *
      (sum_f_R0 (fun i => sum_f_R0 (fun j => sum_f_R0 (fun k2 => Cnorm_sq (nth (flatten_3d n2 n3 i j k2) coeffs_flat C0)) (n3 - 1)) (n2 - 1)) (n1 - 1))
      <= l2_norm_sq (fun k : nat =>
           Csum (fun i => Csum (fun j => Csum (fun k2 => nth (flatten_3d n2 n3 i j k2) coeffs_flat C0 *c
                                            phi3D_norm (a i) (b j) (c k2) k) n3) n2) n1) (M - 1)
      <= (1 + M_bound) *
      (sum_f_R0 (fun i => sum_f_R0 (fun j => sum_f_R0 (fun k2 => Cnorm_sq (nth (flatten_3d n2 n3 i j k2) coeffs_flat C0)) (n3 - 1)) (n2 - 1)) (n1 - 1))).
  { set (F := fun k : nat => Csum (fun idx : nat => nth idx coeffs_flat C0 *c phi_flat idx k) n).
    cbv zeta in H_abs.
    destruct H_abs as [H_low H_high].
    assert (H_eq : l2_norm_sq (fun k : nat =>
        Csum (fun i => Csum (fun j => Csum (fun k2 => nth (flatten_3d n2 n3 i j k2) coeffs_flat C0 *c
                                             phi3D_norm (a i) (b j) (c k2) k) n3) n2) n1) (M - 1)
        = l2_norm_sq F (Nat.pred M)).
    { unfold l2_norm_sq.
      rewrite <- HM_pred_eq.
      apply sum_f_R0_ext; intros k Hk.
      rewrite (HF_flat_eq k); reflexivity. }
    rewrite H_eq, HS_flat_eq.
    unfold F.
    exact (conj H_low H_high). }
  apply H_final.
Qed.


(* ============================================================================
   实例数值紧度（会话 12 追加）：M_bound 的数值裁决
   ----------------------------------------------------------------------------
   三轴梯子实例：[3,13,53]（C=4 梯子的 3 带前缀，三轴各取 → 3³ = 27 个基函数）。
   M_bound_3d(C) = K0'·((1 + 4·K(INR C))³ − 1)，K0' = Rmax 8 C³ / 2，
   K(x) = 1/(√x − 1)（ca_basis_lemmas.v UnconditionalBasisLemmas.K）。
   数值（C=4）：K(4) = 1 ⟹ 4K = 4 ⟹ (1+4)³ − 1 = 124；K0' = 64/2 = 32
   ⟹ M_bound = 32 × 124 = 3968 ≫ 1（引理 M_bound_3d_C4_value 已证）。
   诚实裁决（对齐"数值紧度"纪律）：M_bound > 2 ⟹ 3D 证书目前仅作为
   存在性证明（无条件基 + 显式但巨大的常数），非紧，留给未来收紧
   （联合行和界，而非逐轴乘积 (1+4K_C)³ 的乘法爆炸；M_bound 数值上随 C
   增长：C=3 约 3.6×10³ → C=6 约 5.6×10³，无 C 可使紧）。
   ============================================================================ *)

Definition M_bound_3d (C : nat) : R :=
  (Rmax 8 ((INR C) ^ 3) / 2) *
  ((1 + 4 * K (INR C)) * (1 + 4 * K (INR C)) * (1 + 4 * K (INR C)) - 1).

Lemma K_INR4_eq : K (INR 4) = 1%R.
Proof.
  unfold K.
  assert (Hsqrt : sqrt (INR 4) = 2%R).
  { replace (INR 4) with 4%R by (simpl; ring).
    replace 4%R with (2 * 2)%R by ring.
    rewrite sqrt_square; [reflexivity | lra]. }
  rewrite Hsqrt. field.
Qed.

Lemma M_bound_3d_C4_value : M_bound_3d 4 = 3968%R.
Proof.
  unfold M_bound_3d.
  rewrite K_INR4_eq.
  replace ((INR 4) ^ 3)%R with 64%R by (simpl; ring).
  assert (Hrmax : Rmax 8 64 = 64%R).
  { apply Rle_antisym.
    - apply Rmax_lub; lra.
    - apply Rmax_r. }
  rewrite Hrmax.
  field.
Qed.



