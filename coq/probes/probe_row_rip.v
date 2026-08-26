(* ============================================================

   数学内容： 行非对角和 μ_row（∀i：Σ_{j≠i}|⟨u_i,u_j⟩| ≤ μ_row）蕴含
   对 M+1 原子（k = M+1）的 RIP：
     |‖Σ_{j≤M} c_j u_j‖² − Σ_{j≤M} c_j²| ≤ μ_row·M·Σ_{j≤M} c_j²
   （δ_k = (k−1)·μ_row；交叉项 Σ_{i≠j}|c_i||c_j| ≤ M·Σc² 的 AM-GM 聚合）
   比逐对相干 μ 版更紧：μ_row ≤ M·μ_pair，且行和直接控制。

   F3 组装（经典 R 探针）：
     R0. ipW_combo_r（右线性）+ ipW_double（双重和内积展开）
     R1. norm_sq_split（单位范数：l2 = Σc² + offdiag 交叉项）
     R2. offdiag_abs_le（|交叉项| ≤ μ_row·M·Σc²：|⟨⟩|≤μ_row + AM-GM 聚合）
     R3. row_rip_bound_M（主定理）

   依赖： probe_incoherence（comboM/ipW/ipW_combo_l/norm_sq_comboM_rec 等）。
   审计：零 Admitted / 零自定义公理（同 probe_incoherence 脚印）。
   ============================================================ *)
From mathcomp Require Import ssreflect ssrbool ssrnat seq eqtype div prime.
Require Import Stdlib.Reals.Reals.
Require Import Stdlib.Arith.Arith.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.micromega.Lra.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Logic.FunctionalExtensionality.
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
Require Import probe_rowsum.
Require Import probe_pairdirichlet.
Require Import probe_incoherence.
Import ComplexNumbers.
Import FourierAnalysis.
Import GridOrtho.
Import TParseval.
Import TPartial.
Import PairBound.
Import RowSum.
Import UnconditionalBasis.
Import PairDirichlet.
Import Incoherence.
Import Incoherence2.

Open Scope R_scope.
Open Scope complex_scope.
Open Scope nat_scope.

(* 双重和：Σ_{i≤M} Σ_{j≤M} f i j *)
Definition dsum (M : nat) (f : nat -> nat -> R) : R :=
  sum_f_R0 (fun i => sum_f_R0 (fun j => f i j) M) M.

(* ============ R0：内积双线性 → 双重和 ============ *)

(* 右线性提取：⟨v, Σ_{i≤M} c_i·u_i⟩ = Σ_{i≤M} c_i·⟨v, u_i⟩ *)
Lemma ipW_combo_r (M : nat) (c : nat -> R) (u : nat -> nat -> Complex)
      (v : nat -> Complex) (W : nat) :
  (ipW v (comboM (S M) c u) W)%R
  = (sum_f_R0 (fun i => c i * ipW v (u i) W) M)%R.
Proof.
  rewrite ipW_sym.
  rewrite (ipW_combo_l M c u v W).
  rewrite (sum_f_R0_ext _ (fun i => (c i * ipW v (u i) W)%R) M).
  - reflexivity.
  - intro i. rewrite ipW_sym. ring.
Qed.

(* 行和（对角排除）：row_sum i = Σ_{j≠i, j≤M} |⟨u_i,u_j⟩| *)
Definition row_sum (M : nat) (u : nat -> nat -> Complex) (W : nat) (i : nat) : R :=
  sum_f_R0 (fun j => if Nat.eqb i j then 0%R else Rabs (ipW (u i) (u j) W)) M.

(* 前缀单调：非负 f，m ≤ n ⟹ Σ_{k≤m} f k ≤ Σ_{k≤n} f k *)
Lemma sum_f_R0_le_sub (f : nat -> R) (m n : nat) :
  (forall k, (0 <= f k)%R) -> le m n ->
  (sum_f_R0 f m <= sum_f_R0 f n)%R.
Proof.
  intros Hf Hmn.
  induction Hmn.
  - apply Rle_refl.
  - simpl. apply Rle_trans with (sum_f_R0 f m0)%R.
    + exact IHHmn.
    + apply (Rle_trans _ (sum_f_R0 f m0 + 0)%R).
      * rewrite Rplus_0_r. apply Rle_refl.
      * apply Rplus_le_compat_l. exact (Hf (S m0)).
Qed.

(* 非负 f ⟹ 和 ≥ 0 *)
Lemma row_sum_f_R0_nonneg (f : nat -> R) (M : nat) :
  (forall k, (0 <= f k)%R) -> (0 <= sum_f_R0 f M)%R.
Proof.
  intros Hf. induction M; simpl.
  - exact (Hf 0).
  - rewrite <- (Rplus_0_l 0).
    apply Rplus_le_compat; [exact IHM | exact (Hf (S M))].
Qed.

(* 单项 ≤ 全和：非负 f，j ≤ M ⟹ f j ≤ Σ_{k≤M} f k *)
Lemma sum_f_R0_ge_term (f : nat -> R) (M j : nat) :
  (forall k, (0 <= f k)%R) -> le j M ->
  (f j <= sum_f_R0 f M)%R.
Proof.
  intros Hf HjM.
  induction M as [| M IH].
  - (* M=0：j ≤ 0 ⟹ j=0，f 0 ≤ f 0 *)
    assert (Hj0 : j = 0) by lia. subst. apply Rle_refl.
  - simpl.
    destruct (Nat.eqb_spec j (S M)) as [Hj | Hjne].
    + subst.
      (* f (S M) ≤ sum_f_R0 f M + f (S M)：0 ≤ sum_f_R0 f M（f 非负） *)
      replace (sum_f_R0 f M + f (S M))%R with (f (S M) + sum_f_R0 f M)%R by ring.
      apply (Rle_trans _ (f (S M) + 0)%R).
      * rewrite Rplus_0_r. apply Rle_refl.
      * apply Rplus_le_compat_l. exact (row_sum_f_R0_nonneg f M Hf).
    + apply (Rle_trans _ (sum_f_R0 f M)).
      * apply IH. lia.
      * apply (Rle_trans _ (sum_f_R0 f M + 0)%R).
        -- rewrite Rplus_0_r. apply Rle_refl.
        -- apply Rplus_le_compat_l. exact (Hf (S M)).
Qed.

(* 单对相干 ≤ 行和：i≠j ≤ M ⟹ |⟨u_i,u_j⟩| ≤ row_sum M u W i *)
Lemma row_le_rowsum (M : nat) (u : nat -> nat -> Complex) (W : nat) (i j : nat) :
  le i M -> le j M -> i <> j ->
  (Rabs (ipW (u i) (u j) W) <= row_sum M u W i)%R.
Proof.
  intros Hi Hj Hne.
  unfold row_sum.
  (* 单项 ≤ 项 j（j≠i ⟹ g j = 单项）≤ Σ g（ge_term，非负） *)
  apply (Rle_trans _ (if Nat.eqb i j then 0%R else Rabs (ipW (u i) (u j) W))).
  - (* |⟨u_i,u_j⟩| ≤ g j *)
    destruct (Nat.eqb i j) eqn:Hijb.
    + exfalso. apply Hne. apply Nat.eqb_eq. exact Hijb.
    + simpl. apply Rle_refl.
  - (* g j ≤ Σ_{l≤M} g l：sum_f_R0_ge_term（非负） *)
    apply (sum_f_R0_ge_term (fun l => if Nat.eqb i l then 0%R else Rabs (ipW (u i) (u l) W)) M j).
    + intro l. destruct (Nat.eqb_spec i l) as [Hil | Hil'].
      * subst. right. reflexivity.
      * apply Rabs_pos.
    + exact Hj.
Qed.

(* 交叉项界（行和版，归纳步用）：
   2·|c_{SM}|·|⟨comboM (S M), u_{SM}⟩| ≤ μ_row·(Σ_{j≤M}c_j² + c_{SM}²)
   证明：|⟨comboM,u⟩| ≤ Σ|c_j||⟨u_j,u⟩|（ipW_combo_l + 三角），
   逐项 AM-GM 2|a||b| ≤ a²+b² 分配行和，|⟨⟩| ≤ μ_row（单对 ≤ 行和）。 *)
Lemma row_cross_bound (M : nat) (c : nat -> R) (u : nat -> nat -> Complex)
      (W : nat) (mu_row : R) :
  (forall i, i <= S M ->
    (row_sum (S M) u W i <= mu_row)%R) ->
  ((2%R * Rabs (c (S M)) * Rabs (ipW (comboM (S M) c u) (u (S M)) W))
   <= mu_row * (sum_f_R0 (fun j => c j * c j) M + c (S M) * c (S M)))%R.
Proof.
  intros Hrow.
  (* 1. |⟨comboM,u⟩| ≤ Σ_{j≤M}|c_j||⟨u_j,u⟩| *)
  assert (Hc1 : (Rabs (ipW (comboM (S M) c u) (u (S M)) W)
                 <= sum_f_R0 (fun j => Rabs (c j) * Rabs (ipW (u j) (u (S M)) W)) M)%R).
  { rewrite (ipW_combo_l M c u (u (S M)) W).
    apply (Rle_trans _ (sum_f_R0 (fun j => (Rabs (c j * ipW (u j) (u (S M)) W))%R) M)%R).
    - apply sum_f_R0_abs.
    - apply sum_f_R0_le. intros k Hk. rewrite Rabs_mult. apply Rle_refl. }
  (* 2. 2|c_{SM}|·Σ ≤ Σ(|c_j|²+c_{SM}²)|⟨⟩|（逐项 AM-GM） *)
  assert (Hc2 : ((2%R * Rabs (c (S M)) *
                  sum_f_R0 (fun j => Rabs (c j) * Rabs (ipW (u j) (u (S M)) W)) M)
                 <= sum_f_R0 (fun j =>
                     (Rabs (c j) * Rabs (c j) + c (S M) * c (S M))
                     * Rabs (ipW (u j) (u (S M)) W)) M)%R).
  { rewrite <- (sum_f_R0_scal (2%R * Rabs (c (S M)))
                 (fun j => (Rabs (c j) * Rabs (ipW (u j) (u (S M)) W))%R) M).
    apply sum_f_R0_le. intros k Hk.
    (* 2|c_{SM}||c_k||⟨⟩| ≤ (|c_k|²+c_{SM}²)|⟨⟩|：AM-GM 乘 |⟨⟩| ≥ 0 *)
    rewrite <- (Rmult_assoc (2%R * Rabs (c (S M))) (Rabs (c k)) _).
    replace ((2%R * Rabs (c (S M)) * Rabs (c k))%R)
      with ((2 * Rabs (c k) * Rabs (c (S M)))%R) by ring.
    apply Rmult_le_compat_r.
    + apply Rabs_pos.
    + (* 2|a||b| ≤ a²+b²，a=|c_k|, b=|c_{SM}| *)
      apply (Rle_trans _ (Rabs (c k) * Rabs (c k) + c (S M) * c (S M)))%R.
      * (* |c_k|² = c_k²（Rabs 平方） *)
        replace (Rabs (c k) * Rabs (c k))%R with (c k * c k)%R
          by (rewrite <- Rabs_mult; symmetry; apply Rabs_pos_eq; apply Rle_0_sqr).
        apply (abs_prod_le_sq (c k) (c (S M))).
      * replace (Rabs (c k) * Rabs (c k))%R with (c k * c k)%R
          by (rewrite <- Rabs_mult; symmetry; apply Rabs_pos_eq; apply Rle_0_sqr).
        apply Rle_refl. }
  (* 3. Σ(|c_j|²+c_{SM}²)|⟨⟩| ≤ μ_row·(Σc_j² + c_{SM}²) *)
  apply (Rle_trans _ (2%R * Rabs (c (S M)) *
                      sum_f_R0 (fun j => Rabs (c j) * Rabs (ipW (u j) (u (S M)) W)) M)%R).
  - (* 原目标 ≤ 中间：2|c_{SM}|·|⟨⟩| ≤ 2|c_{SM}|·Σ（Hc1 乘 2|c_{SM}| ≥ 0） *)
    apply Rmult_le_compat_l.
    + apply Rmult_le_pos; [lra | apply Rabs_pos].
    + exact Hc1.
  - (* 中间 ≤ μ_row(Σc² + c_{SM}²)：Hc2 传递 *)
    apply (Rle_trans _ (sum_f_R0 (fun j =>
        (Rabs (c j) * Rabs (c j) + c (S M) * c (S M))
        * Rabs (ipW (u j) (u (S M)) W)) M)%R).
    + exact Hc2.
    + (* Σ(|c_j|²+c²)|⟨⟩| ≤ μ_row·Σc_j² + μ_row·c² *)
      replace (sum_f_R0 (fun j => ((Rabs (c j) * Rabs (c j) + c (S M) * c (S M)) * Rabs (ipW (u j) (u (S M)) W))%R) M)%R
        with (sum_f_R0 (fun j => (Rabs (c j) * Rabs (c j) * Rabs (ipW (u j) (u (S M)) W)
                                  + c (S M) * c (S M) * Rabs (ipW (u j) (u (S M)) W))%R) M)%R
        by (apply sum_f_R0_ext; intro k; ring).
      rewrite (sum_f_R0_plus (fun j => (Rabs (c j) * Rabs (c j) * Rabs (ipW (u j) (u (S M)) W))%R)
                             (fun j => (c (S M) * c (S M) * Rabs (ipW (u j) (u (S M)) W))%R) M).
      rewrite Rmult_plus_distr_l.
      apply Rplus_le_compat.
      * (* Σ|c_j|²|⟨⟩| ≤ μ_row·Σc_j²：逐项 |⟨⟩| ≤ μ_row，|c_j|² = c_j² *)
        rewrite <- (sum_f_R0_scal mu_row (fun j => (c j * c j)%R) M).
        apply sum_f_R0_le. intros k Hk.
        replace (Rabs (c k) * Rabs (c k))%R with (c k * c k)%R
          by (rewrite <- Rabs_mult; symmetry; apply Rabs_pos_eq; apply Rle_0_sqr).
        rewrite (Rmult_comm (c k * c k) (Rabs (ipW (u k) (u (S M)) W))).
        apply Rmult_le_compat_r; [apply Rle_0_sqr | ].
        (* |⟨u_k,u_{SM}⟩| ≤ μ_row：单对 ≤ 行和_{SM} ≤ μ_row（row_le_rowsum + Hrow） *)
        rewrite (ipW_sym (u k) (u (S M)) W).
        apply (Rle_trans _ (row_sum (S M) u W (S M))).
        -- move: Hk => /leP Hk.
           apply (row_le_rowsum (S M) u W (S M) k).
           ++ apply le_n.
           ++ exact (Nat.le_trans _ _ _ Hk (Nat.le_succ_diag_r M)).
           ++ lia.
        -- apply Hrow. by apply leqnn.
      * (* c_{SM}²·Σ|⟨⟩| ≤ μ_row·c_{SM}²：行和 ≤ μ_row *)
        replace (sum_f_R0 (fun j => (c (S M) * c (S M) * Rabs (ipW (u j) (u (S M)) W))%R) M)%R
          with ((c (S M) * c (S M)) * sum_f_R0 (fun j => Rabs (ipW (u j) (u (S M)) W)) M)%R
          by (rewrite <- (sum_f_R0_scal (c (S M) * c (S M)) (fun j => Rabs (ipW (u j) (u (S M)) W)) M); reflexivity).
        rewrite (Rmult_comm (c (S M) * c (S M)) (sum_f_R0 (fun j => Rabs (ipW (u j) (u (S M)) W)) M)).
        apply Rmult_le_compat_r; [apply Rle_0_sqr | ].
        (* Σ_{j≤M}|⟨u_j,u_{SM}⟩| ≤ 行和_{SM} ≤ μ_row *)
        apply (Rle_trans _ (row_sum (S M) u W (S M))).
        ++ (* Σ_{j≤M}|⟨u_j,u_{SM}⟩| ≤ Σ_{j≤M}(if...) ：逐项（对称 + j≠SM） *)
           apply (Rle_trans _ (sum_f_R0 (fun l => if Nat.eqb (S M) l then 0%R else Rabs (ipW (u (S M)) (u l) W)) M)).
           ** apply sum_f_R0_le. intros l Hl.
              rewrite (ipW_sym (u l) (u (S M)) W).
              destruct (Nat.eqb (S M) l) eqn:Hsm.
              -- exfalso. apply (Nat.eqb_eq (S M) l) in Hsm. subst.
                 move: Hl => /leP Hl. lia.
              -- simpl. apply Rle_refl.
           ** (* Σ_{j≤M}(if...) ≤ Σ_{j≤SM}(if...) ：前缀单调（非负） *)
              apply (sum_f_R0_le_sub (fun l => if Nat.eqb (S M) l then 0%R else Rabs (ipW (u (S M)) (u l) W)) M (S M)).
              -- intro l. destruct (Nat.eqb_spec (S M) l) as [Hsm | Hsm'].
                 ++ subst. right. reflexivity.
                 ++ apply Rabs_pos.
              -- lia.
        ++ apply Hrow. by apply leqnn.
Qed.

(* ============ F3 主定理：行和 → RIP（δ = μ_row·(k−1) = μ_row·M） ============ *)

(* RIP 下界（行和版，归纳）：Σ_{j≤M}c_j² ≤ ‖comboM(SM)‖² + μ_row·M·Σ_{j≤M}c_j² *)
Lemma row_rip_lower_M (M : nat) (c : nat -> R) (u : nat -> nat -> Complex)
      (W : nat) (mu_row : R) :
  (0 <= mu_row)%R ->
  (forall i, i <= S M -> (row_sum (S M) u W i <= mu_row)%R) ->
  (forall j, j <= M -> (l2_norm_sq (u j) W)%R = 1%R) ->
  ((sum_f_R0 (fun j => c j * c j) M)
   <= (l2_norm_sq (comboM (S M) c u) W
       + mu_row * INR M * sum_f_R0 (fun j => c j * c j) M))%R.
Proof.
  intros Hmu0 Hrow Hunit.
  induction M as [| M IH].
  - (* base M=0：c₀² ≤ ‖combo 1‖² + 0 *)
    assert (Hu : (l2_norm_sq (u 0%nat) W)%R = 1%R) by (apply Hunit; by apply leqnn).
    change (sum_f_R0 (fun j : nat => c j * c j) 0)%R with (c 0%nat * c 0%nat)%R.
    rewrite (comboM_one c u).
    rewrite l2_norm_sq_scale.
    rewrite Incoherence.Cnorm_sq_Cof_real.
    rewrite Hu.
    replace ((c 0%nat * c 0%nat) * 1)%R with (c 0%nat * c 0%nat)%R by ring.
    replace (INR 0)%R with 0%R by reflexivity.
    lra.
  - (* step：P(SM) *)
    rewrite (sq_sum_step c M).
    rewrite (norm_sq_comboM_rec M c u W).
    assert (Hu' : (l2_norm_sq (u (S M)) W)%R = 1%R) by (apply Hunit; by apply leqnn).
    rewrite Hu'.
    replace ((c (S M) * c (S M)) * 1)%R with (c (S M) * c (S M))%R by ring.
    (* IH（截取到 M） *)
    assert (HIH' : (sum_f_R0 (fun j : nat => c j * c j) M
                    <= l2_norm_sq (comboM (S M) c u) W
                       + mu_row * INR M * sum_f_R0 (fun j => c j * c j) M)%R).
    { apply IH.
      - intros i Hi.
        apply (Rle_trans _ (row_sum (S (S M)) u W i)).
        + unfold row_sum.
          apply (sum_f_R0_le_sub (fun j => if Nat.eqb i j then 0%R else Rabs (ipW (u i) (u j) W)) (S M) (S (S M))).
          * intro j. destruct (Nat.eqb_spec i j) as [Hij | Hij'].
            -- subst. right. reflexivity.
            -- apply Rabs_pos.
          * lia.
        + apply Hrow.
          move: Hi => /leP Hi.
          apply/leP. lia.
      - intros j Hj. apply Hunit.
        move: Hj => /leP Hj.
        apply/leP. lia. }
    (* 截取行和上界到 S M 层：row_cross_bound 需要 (forall i, i <= S M -> row_sum (S M) u W i <= mu_row) *)
    assert (Hrow' : (forall i, i <= S M -> (row_sum (S M) u W i <= mu_row)%R)).
    { intros i Hi.
      apply (Rle_trans _ (row_sum (S (S M)) u W i)).
      + unfold row_sum.
        apply (sum_f_R0_le_sub (fun j => if Nat.eqb i j then 0%R else Rabs (ipW (u i) (u j) W)) (S M) (S (S M))).
        * intro j. destruct (Nat.eqb_spec i j) as [Hij | Hij'].
          -- subst. right. reflexivity.
          -- apply Rabs_pos.
        * lia.
      + apply Hrow.
        move: Hi => /leP Hi.
        apply/leP. lia. }
    (* row_cross_bound：2|c_{SM}|·|⟨comboM,u_{SM}⟩| ≤ μ_row(Σ_M + c_{SM}²) *)
    assert (Hcb := row_cross_bound M c u W mu_row Hrow').
    (* −2c⟨⟩ ≤ 2|c||⟨⟩|（Rle_abs + Rabs_mult） *)
    assert (Hneg2 : (- (2 * c (S M) * ipW (comboM (S M) c u) (u (S M)) W)
                    <= 2 * Rabs (c (S M)) * Rabs (ipW (comboM (S M) c u) (u (S M)) W))%R).
    { apply (Rle_trans _ (Rabs (2 * c (S M) * ipW (comboM (S M) c u) (u (S M)) W))).
      - apply (Rle_trans _ (Rabs (- (2 * c (S M) * ipW (comboM (S M) c u) (u (S M)) W)))).
        + apply Rle_abs.
        + rewrite Rabs_opp. apply Rle_refl.
      - rewrite Rabs_mult. rewrite Rabs_mult.
        replace (Rabs 2)%R with 2%R by (rewrite Rabs_right; [ring | lra]).
        apply Rle_refl. }
    (* 去掉 Rabs：−2c⟨⟩ ≤ μ_row(Σ_M + c_{SM}²)（Hneg2 + Hcb 组合，供 nra 使用） *)
    assert (Hcross : (- (2 * c (S M) * ipW (comboM (S M) c u) (u (S M)) W)
                      <= mu_row * (sum_f_R0 (fun j => c j * c j) M + c (S M) * c (S M)))%R).
    { apply (Rle_trans _ (2 * Rabs (c (S M)) * Rabs (ipW (comboM (S M) c u) (u (S M)) W))).
      - exact Hneg2.
      - exact Hcb. }
    assert (HS : (0 <= sum_f_R0 (fun j => c j * c j) M)%R) by apply sum_sq_nonneg.
    assert (HA : (0 <= c (S M) * c (S M))%R) by apply Rle_0_sqr.
    assert (HM : (0 <= INR M)%R).
    { apply (le_INR 0 M). lia. }
    rewrite (S_INR M).
    (* μm·c_{SM}² ≥ 0：nra 无法自行证明三因子乘积（Rocq 9 nra 证书限制），显式断言 *)
    assert (Hprod : (0 <= mu_row * INR M * (c (S M) * c (S M)))%R).
    { apply Rmult_le_pos.
      - apply Rmult_le_pos; assumption.
      - apply Rle_0_sqr. }
    nra.
Qed.

(* RIP 上界（行和版，归纳）：‖comboM(SM)‖² ≤ Σ_{j≤M}c_j² + μ_row·M·Σ_{j≤M}c_j² *)
Lemma row_rip_upper_M (M : nat) (c : nat -> R) (u : nat -> nat -> Complex)
      (W : nat) (mu_row : R) :
  (0 <= mu_row)%R ->
  (forall i, i <= S M -> (row_sum (S M) u W i <= mu_row)%R) ->
  (forall j, j <= M -> (l2_norm_sq (u j) W)%R = 1%R) ->
  ((l2_norm_sq (comboM (S M) c u) W
    <= sum_f_R0 (fun j => c j * c j) M
       + mu_row * INR M * sum_f_R0 (fun j => c j * c j) M)%R).
Proof.
  intros Hmu0 Hrow Hunit.
  induction M as [| M IH].
  - (* base M=0：‖combo 1‖² ≤ c₀² + 0 *)
    assert (Hu : (l2_norm_sq (u 0%nat) W)%R = 1%R) by (apply Hunit; by apply leqnn).
    change (sum_f_R0 (fun j : nat => c j * c j) 0)%R with (c 0%nat * c 0%nat)%R.
    rewrite (comboM_one c u).
    rewrite l2_norm_sq_scale.
    rewrite Incoherence.Cnorm_sq_Cof_real.
    rewrite Hu.
    replace ((c 0%nat * c 0%nat) * 1)%R with (c 0%nat * c 0%nat)%R by ring.
    replace (INR 0)%R with 0%R by reflexivity.
    lra.
  - (* step：P(SM) *)
    rewrite (norm_sq_comboM_rec M c u W).
    rewrite (sq_sum_step c M).
    assert (Hu' : (l2_norm_sq (u (S M)) W)%R = 1%R) by (apply Hunit; by apply leqnn).
    rewrite Hu'.
    replace ((c (S M) * c (S M)) * 1)%R with (c (S M) * c (S M))%R by ring.
    (* IH 截取到 M 层（行和上界前缀单调） *)
    assert (Hrow' : (forall i, i <= S M -> (row_sum (S M) u W i <= mu_row)%R)).
    { intros i Hi.
      apply (Rle_trans _ (row_sum (S (S M)) u W i)).
      + unfold row_sum.
        apply (sum_f_R0_le_sub (fun j => if Nat.eqb i j then 0%R else Rabs (ipW (u i) (u j) W)) (S M) (S (S M))).
        * intro j. destruct (Nat.eqb_spec i j) as [Hij | Hij'].
          -- subst. right. reflexivity.
          -- apply Rabs_pos.
        * lia.
      + apply Hrow.
        move: Hi => /leP Hi.
        apply/leP. lia. }
    assert (HIH' : (l2_norm_sq (comboM (S M) c u) W
                    <= sum_f_R0 (fun j : nat => c j * c j) M
                       + mu_row * INR M * sum_f_R0 (fun j => c j * c j) M)%R).
    { apply IH.
      - intros i Hi.
        apply (Rle_trans _ (row_sum (S (S M)) u W i)).
        + unfold row_sum.
          apply (sum_f_R0_le_sub (fun j => if Nat.eqb i j then 0%R else Rabs (ipW (u i) (u j) W)) (S M) (S (S M))).
          * intro j. destruct (Nat.eqb_spec i j) as [Hij | Hij'].
            -- subst. right. reflexivity.
            -- apply Rabs_pos.
          * lia.
        + apply Hrow.
          move: Hi => /leP Hi.
          apply/leP. lia.
      - intros j Hj. apply Hunit.
        move: Hj => /leP Hj.
        apply/leP. lia. }
    (* row_cross_bound：2|c_{SM}|·|⟨comboM,u_{SM}⟩| ≤ μ_row(Σ_M + c_{SM}²) *)
    assert (Hcb := row_cross_bound M c u W mu_row Hrow').
    (* 2c⟨⟩ ≤ 2|c||⟨⟩|（Rle_abs 正向） *)
    assert (Hpos : (2 * c (S M) * ipW (comboM (S M) c u) (u (S M)) W
                  <= 2 * Rabs (c (S M)) * Rabs (ipW (comboM (S M) c u) (u (S M)) W))%R).
    { apply (Rle_trans _ (Rabs (2 * c (S M) * ipW (comboM (S M) c u) (u (S M)) W))).
      - apply Rle_abs.
      - rewrite Rabs_mult. rewrite Rabs_mult.
        replace (Rabs 2)%R with 2%R by (rewrite Rabs_right; [ring | lra]).
        apply Rle_refl. }
    (* 去掉 Rabs：2c⟨⟩ ≤ μ_row(Σ_M + c_{SM}²)（Hpos + Hcb 组合，供 nra 使用） *)
    assert (Hcross_pos : (2 * c (S M) * ipW (comboM (S M) c u) (u (S M)) W
                        <= mu_row * (sum_f_R0 (fun j => c j * c j) M + c (S M) * c (S M)))%R).
    { apply (Rle_trans _ (2 * Rabs (c (S M)) * Rabs (ipW (comboM (S M) c u) (u (S M)) W))).
      - exact Hpos.
      - exact Hcb. }
    assert (HS : (0 <= sum_f_R0 (fun j => c j * c j) M)%R) by apply sum_sq_nonneg.
    assert (HA : (0 <= c (S M) * c (S M))%R) by apply Rle_0_sqr.
    assert (HM : (0 <= INR M)%R).
    { apply (le_INR 0 M). lia. }
    rewrite (S_INR M).
    (* μm·c_{SM}² ≥ 0：三因子乘积，显式断言 *)
    assert (Hprod : (0 <= mu_row * INR M * (c (S M) * c (S M)))%R).
    { apply Rmult_le_pos.
      - apply Rmult_le_pos; assumption.
      - apply Rle_0_sqr. }
    nra.
Qed.

(* ============ F3 主定理：行和 → RIP（δ = μ_row·M，M+1 原子） ============ *)
Lemma row_rip_bound_M (M : nat) (c : nat -> R) (u : nat -> nat -> Complex)
      (W : nat) (mu_row : R) :
  (0 <= mu_row)%R ->
  (forall i, i <= S M -> (row_sum (S M) u W i <= mu_row)%R) ->
  (forall j, j <= M -> (l2_norm_sq (u j) W)%R = 1%R) ->
  (Rabs (l2_norm_sq (comboM (S M) c u) W
         - sum_f_R0 (fun j => c j * c j) M)
   <= mu_row * INR M * sum_f_R0 (fun j => c j * c j) M)%R.
Proof.
  intros Hmu0 Hrow Hunit.
  apply Rabs_le.
  split.
  - (* 下界方向：−(μMΣ) ≤ L − Σ ⟸ Σ ≤ L + μMΣ *)
    assert (Hlow := row_rip_lower_M M c u W mu_row Hmu0 Hrow Hunit).
    nra.
  - (* 上界方向：L − Σ ≤ μMΣ ⟸ L ≤ Σ + μMΣ *)
    assert (Hup := row_rip_upper_M M c u W mu_row Hmu0 Hrow Hunit).
    nra.
Qed.
