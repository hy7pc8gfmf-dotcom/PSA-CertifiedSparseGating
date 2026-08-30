(* ============================================================
   CS-18 A-B 桥梁桥墩：psi 核漂移界与截断 TVD（probe_ab_bridge_pier.v）
   （M2 venue 对齐扩展 T4——"无形式化桥梁"负面声明升级为
   "中间桥墩已机器检查"；桥面（端到端 PPL）仍为实证轨道）

   背景：论文 A 证书覆盖基表示层能量稳定（psi 原子系），论文 B 的
   端到端外推性能（PPL）是实证轨道——两者的衔接此前只有负面声明。
   本模块给出中间桥墩：psi 核（逐位内积被加项）的漂移有显式界，
   经 PhaseCoherence 的 kernel_drift_controls_attention（核漂移 dc ⟹
   softmax TVD ≤ exp(2·dc·dd) − 1）组装出"基核窗口截断 ⟹ 注意力
   输出 TVD 界"的机器检查链节。

   数学内容：
     PB0 复数-R 基础件：Rabs_re_le_Cnorm_p（库内同名件为
         Local/inline，自包含复制）+ INR 基础件
     PB1 psi 逐位模长上界：Cnorm (psi n k) ≤ 1/√n（k<n 等号成立、
         k≥n 归零——phi_ge_n_zero）
     PB2 ★ psi 核逐位界与相邻位漂移（venue 原型）：
         psi_kernel n m k := re (psi n k *c Cconj (psi m k))
         psi_kernel_abs_le      : |psi_kernel n m k| ≤ 1/(√n·√m)
         psi_kernel_drift_bound : |psi_kernel n m k − psi_kernel n m (S k)|
                                  ≤ 2/(√n·√m)（三角不等式路线）
     PB3 ★★ 截断 TVD 桥（最终合成）：
         全窗核 K i j = Σ_{k<W} psi_kernel (v_i)(v_j) k、截断核 K' 截至W'，
         |K i j − K' i j| ≤ INR(W−W')·(1/(√v_i·√v_j)) ≤ INR(W−W')·(1/2)
         （带 ≥2）⟹ kernel_drift_controls_attention 实例化：
         TVD(softmax(K·c), softmax(K'·c)) ≤ exp(2·(INR(W−W')·(1/2))·dd) − 1，
         dd = Σ|c_j|——"桥墩已建、桥面（PPL）待铺"。

   纪律（承 probe_robust / probe_c4_instance 经典 R 轨道）：
     - 零 Admitted / 零自定义 Axiom（审计 ≤ Dedekind 脚印）
     - R 层定理（sqrt/softmax——不可提取；提取不适用，如实注明）
   依赖：ca_base/ca_complex_foundation/ca_independence/ca_basis/
         ca_basis_lemmas/ca_decay + PSA_framework（RowTruncation 的
         list_sum_R、SoftmaxStability 的 softmax_l、PhaseCoherence 的
         kernel_drift_controls_attention、InstanceCertificate 的 psi 系）。
   ============================================================ *)
Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.Arith.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.micromega.Lra.
Require Import Stdlib.Reals.Reals.
Require Import ca_base ca_complex_foundation ca_independence ca_basis ca_basis_lemmas ca_decay.
Require Import PSA_framework.
Import ComplexNumbers.
Import ExtendedTheorems.
Import ListNotations.
Open Scope nat_scope.
Open Scope R_scope.

(* ============ PB0：复数-R 基础件 ============ *)

Lemma Rabs_re_le_Cnorm_p (z : Complex) : Rabs (re z) <= Cnorm z.
Proof.
  unfold Cnorm, Cnorm_sq, re; simpl.
  rewrite <- sqrt_Rsqr_abs.
  apply sqrt_le_1_c.
  - apply Rle_0_sqr.
  - apply Rplus_le_le_0_compat; apply Rle_0_sqr.
  - unfold Rsqr; nra.
Qed.

Lemma Cnorm_ge_0_cn (z : Complex) : 0 <= Cnorm z.
Proof.
  unfold Cnorm, Cnorm_sq.
  apply sqrt_positivity.
  apply Rplus_le_le_0_compat; apply Rle_0_sqr.
Qed.

Lemma INR_pos_le (n : nat) : (0 <= INR n)%R.
Proof.
  apply Rle_trans with (INR 0)%R.
  - apply Rle_refl.
  - apply le_INR. lia.
Qed.

Lemma INR_1_lt_ge2 (n : nat) : (2 <= n)%nat -> (1 < INR n)%R.
Proof.
  intros Hn.
  apply Rlt_le_trans with (2%R).
  - lra.
  - assert (H2 : (INR 2 = 2)%R) by (rewrite S_INR, INR_1; reflexivity).
    rewrite <- H2. apply le_INR. lia.
Qed.

Lemma INR_2_two : (INR 2 = 2)%R.
Proof. rewrite S_INR, INR_1. reflexivity. Qed.

Lemma psi_frac_eq (n m : nat) : (2 <= n)%nat -> (2 <= m)%nat ->
  (1 / sqrt (INR n) * (1 / sqrt (INR m))
   = 1 / (sqrt (INR n) * sqrt (INR m)))%R.
Proof.
  intros Hn Hm. field.
  split; apply Rgt_not_eq; apply sqrt_lt_R0; apply lt_0_INR; lia.
Qed.

(* ============ PB1：psi 逐位模长上界 ============ *)

Lemma psi_cnorm_le (n k : nat) : (2 <= n)%nat ->
  Cnorm (psi n k) <= 1 / sqrt (INR n).
Proof.
  intros Hn. unfold psi. rewrite Cnorm_mult.
  destruct (Nat.lt_ge_cases k n) as [Hk | Hk].
  - (* k < n：phi 单位模长 *)
    assert (HC : Cnorm (phi n k) = 1).
    { unfold Cnorm. rewrite (Cnorm_sq_phi n k Hk). apply sqrt_1. }
    rewrite HC. rewrite Rmult_1_r.
    rewrite (Cnorm_Cof_real_pos (1 / sqrt (INR n))).
    + apply Rle_refl.
    + apply Rlt_le. apply Rdiv_lt_0_compat.
      * apply Rlt_0_1.
      * apply sqrt_lt_R0. apply lt_0_INR. lia.
  - (* k ≥ n：phi 归零 *)
    rewrite (phi_ge_n_zero n k Hk).
    assert (HC0 : Cnorm C0 = 0) by (unfold Cnorm; rewrite Cnorm_sq_zero; apply sqrt_0).
    rewrite HC0. rewrite Rmult_0_r.
    apply Rlt_le. apply Rdiv_lt_0_compat.
    * apply Rlt_0_1.
    * apply sqrt_lt_R0. apply lt_0_INR. lia.
Qed.

(* ============ PB2：psi 核逐位界与相邻位漂移（venue 原型） ============ *)

Definition psi_kernel (n m k : nat) : R := re (psi n k *c Cconj (psi m k)).

Lemma psi_kernel_abs_le (n m k : nat) : (2 <= n)%nat -> (2 <= m)%nat ->
  (Rabs (psi_kernel n m k) <= 1 / (sqrt (INR n) * sqrt (INR m)))%R.
Proof.
  intros Hn Hm. unfold psi_kernel.
  eapply Rle_trans; [apply Rabs_re_le_Cnorm_p |].
  rewrite Cnorm_mult. rewrite Cnorm_conj_eq.
  rewrite <- (psi_frac_eq n m Hn Hm).
  apply Rmult_le_compat.
  - apply Cnorm_ge_0_cn.
  - apply Cnorm_ge_0_cn.
  - apply psi_cnorm_le; exact Hn.
  - apply psi_cnorm_le; exact Hm.
Qed.

Theorem psi_kernel_drift_bound (n m k : nat) :
  (2 <= n)%nat -> (2 <= m)%nat ->
  (Rabs (psi_kernel n m k - psi_kernel n m (S k))
   <= 2 / (sqrt (INR n) * sqrt (INR m)))%R.
Proof.
  intros Hn Hm. unfold psi_kernel.
  replace (re (psi n k *c Cconj (psi m k))
          - re (psi n (S k) *c Cconj (psi m (S k))))
     with (re (psi n k *c Cconj (psi m k))
          + - re (psi n (S k) *c Cconj (psi m (S k)))) by ring.
  rewrite Rabs_triang. rewrite Rabs_Ropp.
  apply Rle_trans with
    (Cnorm (psi n k *c Cconj (psi m k))
     + Cnorm (psi n (S k) *c Cconj (psi m (S k))))%R.
  - apply Rplus_le_compat; apply Rabs_re_le_Cnorm_p.
  - rewrite !Cnorm_mult. rewrite !Cnorm_conj_eq.
    apply Rle_trans with
      (1 / (sqrt (INR n) * sqrt (INR m))
       + 1 / (sqrt (INR n) * sqrt (INR m)))%R.
    + rewrite <- !psi_frac_eq by lia.
      apply Rplus_le_compat; apply Rmult_le_compat.
      * apply Cnorm_ge_0_cn.
      * apply Cnorm_ge_0_cn.
      * apply psi_cnorm_le; exact Hn.
      * apply psi_cnorm_le; exact Hm.
      * apply Cnorm_ge_0_cn.
      * apply Cnorm_ge_0_cn.
      * apply psi_cnorm_le; exact Hn.
      * apply psi_cnorm_le; exact Hm.
    + unfold Rdiv. nra.
Qed.

(* ============ PB3：截断漂移与 TVD 桥 ============ *)

(* --- 基础件：list_sum_R 三件（RowTruncation.list_sum_R 上自包含） --- *)

Lemma list_sum_R_app (f : nat -> R) (l1 l2 : list nat) :
  RowTruncation.list_sum_R f (l1 ++ l2)
  = RowTruncation.list_sum_R f l1 + RowTruncation.list_sum_R f l2.
Proof.
  induction l1 as [| a t IH].
  - simpl. rewrite Rplus_0_l. reflexivity.
  - rewrite <- app_comm_cons. simpl. rewrite IH. ring.
Qed.

Lemma list_sum_R_abs_bound (f : nat -> R) (l : list nat) :
  (Rabs (RowTruncation.list_sum_R f l)
   <= RowTruncation.list_sum_R (fun k => Rabs (f k)) l)%R.
Proof.
  induction l as [| a t IH].
  - simpl. rewrite Rabs_R0. apply Rle_refl.
  - simpl. eapply Rle_trans; [apply Rabs_triang |].
    apply Rplus_le_compat.
    + apply Rle_refl.
    + exact IH.
Qed.

Lemma list_sum_R_const_le (f : nat -> R) (c : R) (l : list nat) :
  (forall k, In k l -> (f k <= c)%R) ->
  (RowTruncation.list_sum_R f l <= INR (length l) * c)%R.
Proof.
  induction l as [| a t IH]; intro Hpt.
  - cbn [RowTruncation.list_sum_R fold_right]. rewrite <- INR_0. rewrite Rmult_0_l. apply Rle_refl.
  - assert (Ha : (f a <= c)%R) by (apply Hpt; left; reflexivity).
    assert (Ht : (RowTruncation.list_sum_R f t <= INR (length t) * c)%R)
      by (apply IH; intros k Hk; apply Hpt; right; exact Hk).
  - assert (Hlen : (INR (length (a :: t)) = INR (length t) + 1)%R).
    { cbn [length]. rewrite S_INR. reflexivity. }
    replace (RowTruncation.list_sum_R f (a :: t))
      with (f a + RowTruncation.list_sum_R f t) by reflexivity.
    rewrite Hlen. lra.
Qed.

(* --- 截断漂移：全窗和与截断和之差的绝对值界 --- *)

Lemma psi_kernel_trunc_dc (n m W W' : nat) :
  (2 <= n)%nat -> (2 <= m)%nat -> (W' <= W)%nat ->
  (Rabs (RowTruncation.list_sum_R (psi_kernel n m) (seq 0 W)
         - RowTruncation.list_sum_R (psi_kernel n m) (seq 0 W'))
   <= INR (W - W')%nat * (1 / (sqrt (INR n) * sqrt (INR m))))%R.
Proof.
  intros Hn Hm Hle.
  set (f := psi_kernel n m).
  set (d := (W - W')%nat).
  assert (HW : (W = W' + d)%nat) by (unfold d; lia).
  assert (Hsplit : RowTruncation.list_sum_R f (seq 0 (W' + d))
                   = RowTruncation.list_sum_R f (seq 0 W')
                     + RowTruncation.list_sum_R f (seq W' d)).
  { rewrite seq_app, list_sum_R_app. reflexivity. }
  assert (Habs : (Rabs (RowTruncation.list_sum_R f (seq W' d))
                  <= RowTruncation.list_sum_R (fun k => Rabs (f k)) (seq W' d))%R)
    by apply list_sum_R_abs_bound.
  assert (Hpt : forall k, In k (seq W' d) ->
            (Rabs (f k) <= 1 / (sqrt (INR n) * sqrt (INR m)))%R).
  { intros k _. unfold f. apply psi_kernel_abs_le; assumption. }
  assert (Hconst : (RowTruncation.list_sum_R (fun k => Rabs (f k)) (seq W' d)
                    <= INR (length (seq W' d))
                       * (1 / (sqrt (INR n) * sqrt (INR m))))%R)
    by (apply list_sum_R_const_le; exact Hpt).
  rewrite length_seq in Hconst.
  assert (HK : RowTruncation.list_sum_R f (seq 0 W)
               - RowTruncation.list_sum_R f (seq 0 W')
               = RowTruncation.list_sum_R f (seq W' d)).
  { rewrite HW. rewrite Hsplit. ring. }
  rewrite HK.
  eapply Rle_trans; [exact Habs | exact Hconst].
Qed.

(* --- 带下界：两带 ≥2 ⟹ 模长乘积 ≥ 2 --- *)

Lemma sqrt_pair_ge2 (vi vj : nat) : (2 <= vi)%nat -> (2 <= vj)%nat ->
  (2 <= sqrt (INR vi) * sqrt (INR vj))%R.
Proof.
  intros Hvi Hvj.
  assert (H2 : (INR 2 = 2)%R) by (rewrite S_INR, INR_1; reflexivity).
  assert (Hbi : (2 <= INR vi)%R) by (rewrite <- H2; apply le_INR; lia).
  assert (Hbj : (2 <= INR vj)%R) by (rewrite <- H2; apply le_INR; lia).
  assert (Hb0 : (0 <= INR vi * INR vj)%R) by nra.
  assert (Hb4 : (2 * 2 <= INR vi * INR vj)%R) by nra.
  apply Rle_trans with (sqrt (INR vi * INR vj)).
  - replace 2 with (sqrt (2 * 2)) by (apply sqrt_square; lra).
    apply sqrt_le_1_c.
    + lra.
    + exact Hb0.
    + exact Hb4.
  - rewrite sqrt_mult by apply INR_pos_le. apply Rle_refl.
Qed.

(* --- PB3 ★★ 截断 TVD 桥（最终合成） --- *)

Theorem psi_attention_tvd_trunc (vals : list nat) (coeffs : list R) (W W' : nat) (dd : R) :
  (0 < length vals)%nat ->
  length coeffs = length vals ->
  (forall j, (j < length vals)%nat -> (2 <= nth j vals 0%nat)%nat) ->
  (W' <= W)%nat ->
  (RowTruncation.list_sum_R (fun j => Rabs (nth j coeffs 0%R)) (seq 0 (length vals)) <= dd)%R ->
  let K := fun i j => RowTruncation.list_sum_R
            (fun k => psi_kernel (nth i vals 0%nat) (nth j vals 0%nat) k) (seq 0 W) in
  let K' := fun i j => RowTruncation.list_sum_R
            (fun k => psi_kernel (nth i vals 0%nat) (nth j vals 0%nat) k) (seq 0 W') in
  (RowTruncation.list_sum_R
     (fun i => Rabs
        (SoftmaxStability.softmax_l (fun i0 => RowTruncation.list_sum_R (fun j => nth j coeffs 0%R * K i0 j) (seq 0 (length vals))) (length vals) i
         - SoftmaxStability.softmax_l (fun i0 => RowTruncation.list_sum_R (fun j => nth j coeffs 0%R * K' i0 j) (seq 0 (length vals))) (length vals) i))
     (seq 0 (length vals))
   <= exp (2 * (INR (W - W')%nat * (1 / 2) * dd)) - 1)%R.
Proof.
  intros Hlen0 Hlc Hge2 Hle Hdd K K'.
  cbv zeta.
  apply (PhaseCoherence.kernel_drift_controls_attention K K' (fun j => nth j coeffs 0%R)
           (length vals) (INR (W - W')%nat * (1 / 2)) dd).
  - exact Hlen0.
  - (* 0 ≤ dc *)
    apply Rle_trans with (INR (W - W')%nat * 0)%R.
    + rewrite Rmult_0_r. apply Rle_refl.
    + apply Rmult_le_compat_l.
      * apply INR_pos_le.
      * lra.
  - (* 一致漂移界：dc = INR (W - W')%nat * (1/2) *)
    intros i j Hi Hj.
    assert (H2i : (2 <= nth i vals 0%nat)%nat) by (apply Hge2; exact Hi).
    assert (H2j : (2 <= nth j vals 0%nat)%nat) by (apply Hge2; exact Hj).
    eapply Rle_trans;
      [apply (psi_kernel_trunc_dc (nth i vals 0%nat) (nth j vals 0%nat) W W' H2i H2j Hle) |].
    assert (Hden : (2 <= sqrt (INR (nth i vals 0%nat)) * sqrt (INR (nth j vals 0%nat)))%R)
      by (apply sqrt_pair_ge2; assumption).
    assert (Hinv : (1 / (sqrt (INR (nth i vals 0%nat)) * sqrt (INR (nth j vals 0%nat)))
                    <= 1 / 2)%R).
    { unfold Rdiv. rewrite !Rmult_1_l.
      apply Rinv_le_contravar.
      - lra.
      - exact Hden. }
    apply Rmult_le_compat_l.
    + apply INR_pos_le.
    + exact Hinv.
  - exact Hdd.
Qed.

(* ============ 审计 ============ *)
Print Assumptions psi_kernel_drift_bound.
Print Assumptions psi_attention_tvd_trunc.
