(* ============================================================
   T-QUANT：量化核扰动的注意力稳定性证书（z 工作区，E039）
   部署鲁棒性族第二件（发布仓库增活分析 §3 T-QUANT）：
     Q1 quant_drift_exact：逐项误差 |K_ij − K'_ij| ≤ e_j ⟹
        |logit_i − logit'_i| ≤ Σ_j |c_j|·e_j（异质误差的行加权分账）。
     Q2 quant_column_drift：误差按列（键通道）一致 ⟹ 每行同一界。
     Q3 quant_column_controls_attention（主定理）：per-key 量化误差
        e_j ⟹ softmax ℓ1 TVD ≤ e^{2·Σ_j |c_j|·e_j} − 1
        ——INT8 per-channel 量化误差的显式证书。
     Q4 quant_relative_drift：相对误差 |K−K'| ≤ δ|K| ⟹
        漂移 ≤ δ·Σ_j |c_j·K_ij|（质量型界——行核质量加权）。
     Q5 quant_uniform_controls：均匀 ε ⟹ TVD ≤ e^{2·ε·‖c‖₁}−1
        （与 T4 kernel_drift_controls_attention 同形，直接实例化）。
   依赖：PSA_framework（RowTruncation/SoftmaxStability/PhaseCoherence）
   + probe_kvevict（logit 定义复用）。审计：Print Assumptions 尾部。
   ============================================================ *)
Require Import Stdlib.Reals.Reals.
Require Import Stdlib.Arith.Arith.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.micromega.Lra.
Require Import Stdlib.Lists.List.
Import ListNotations.
Require Import PSA_framework.
Require Import probe_kvevict.
Import PSA_framework.RowTruncation.
Import PSA_framework.SoftmaxStability.
Import PSA_framework.PhaseCoherence.
Import KVEvict.

Open Scope R_scope.
Open Scope nat_scope.

Module Quant.

(* ---------- Q1：异质逐项误差的精确分账 ---------- *)

Lemma quant_drift_exact (K K' : nat -> nat -> R) (c e : nat -> R) (i n : nat) :
  (forall j, (j < n)%nat -> (Rabs (K i j - K' i j) <= e j))%R ->
  (Rabs (logit K c i n - logit K' c i n)
   <= list_sum_R (fun j => (Rabs (c j) * e j)%R) (seq 0%nat n))%R.
Proof.
  intros HK.
  assert (Hd :
     (list_sum_R (fun j => (c j * K i j)%R) (seq 0%nat n)
      - list_sum_R (fun j => (c j * K' i j)%R) (seq 0%nat n)
      = list_sum_R (fun j => (c j * K i j + - (c j * K' i j))%R) (seq 0%nat n))%R).
  { rewrite (list_sum_R_plus (fun j => (c j * K i j)%R)
               (fun j => (- (c j * K' i j))%R) (seq 0%nat n)).
    rewrite (list_sum_R_neg (fun j => (c j * K' i j))%R (seq 0%nat n)).
    ring. }
  unfold logit. rewrite Hd.
  apply (Rle_trans _
           (list_sum_R (fun j => Rabs (c j * K i j - c j * K' i j)) (seq 0%nat n))).
  - apply list_sum_R_abs.
  - apply list_sum_R_le_compat. intros j Hj.
    assert (Hjn : (j < n)%nat) by (apply In_seq_lt_coq; exact Hj).
    assert (HKj : (Rabs (K i j - K' i j) <= e j)%R) by (apply HK; exact Hjn).
    replace ((c j * K i j - c j * K' i j)%R) with ((c j * (K i j - K' i j))%R) by ring.
    rewrite Rabs_mult.
    rewrite (Rmult_comm (Rabs (c j)) (Rabs (K i j - K' i j))).
    rewrite (Rmult_comm (Rabs (c j)) (e j)).
    apply (Rmult_le_compat_r (Rabs (c j)) (Rabs (K i j - K' i j)) (e j));
      [ apply Rabs_pos | exact HKj ].
Qed.

(* ---------- Q2：列一致（键通道）误差 ⟹ 每行同界 ---------- *)

Lemma quant_column_drift (K K' : nat -> nat -> R) (c e : nat -> R) (i n : nat) :
  (i < n)%nat ->
  (forall i0 j, (i0 < n)%nat -> (j < n)%nat -> (Rabs (K i0 j - K' i0 j) <= e j))%R ->
  (Rabs (logit K c i n - logit K' c i n)
   <= list_sum_R (fun j => (Rabs (c j) * e j)%R) (seq 0%nat n))%R.
Proof.
  intros Hi HK.
  apply quant_drift_exact. intros j Hj.
  apply HK; [ exact Hi | exact Hj ].
Qed.

(* ---------- Q3：主定理——per-key 量化误差的 TVD 证书 ---------- *)

Theorem quant_column_controls_attention (K K' : nat -> nat -> R)
        (c e : nat -> R) (n : nat) :
  (0 < n)%nat ->
  (forall j, (0 <= e j))%R ->
  (forall i j, (i < n)%nat -> (j < n)%nat -> (Rabs (K i j - K' i j) <= e j))%R ->
  (list_sum_R (fun i => Rabs
     (softmax_l (fun i0 => logit K c i0 n) n i
      - softmax_l (fun i0 => logit K' c i0 n) n i))
     (seq 0%nat n)
   <= exp (2 * list_sum_R (fun j => (Rabs (c j) * e j)%R) (seq 0%nat n)) - 1)%R.
Proof.
  intros Hn He HK.
  assert (Hm : (0 <= list_sum_R (fun j => (Rabs (c j) * e j)%R) (seq 0%nat n))%R).
  { apply list_sum_R_pos. intros i _. apply Rmult_le_pos; [ apply Rabs_pos | apply He ]. }
  apply (softmax_l1_bound_exp
           (fun i0 => logit K c i0 n)
           (fun i0 => logit K' c i0 n)
           n (list_sum_R (fun j => (Rabs (c j) * e j)%R) (seq 0%nat n)) Hn).
  - exact Hm.
  - intros k Hk. apply quant_column_drift; [ exact Hk | exact HK ].
Qed.

(* ---------- Q4：相对误差的质量型界 ---------- *)

Lemma quant_relative_drift (K K' : nat -> nat -> R) (c : nat -> R)
      (i n : nat) (delta : R) :
  (forall i0 j, (Rabs (K i0 j - K' i0 j) <= delta * Rabs (K i0 j)))%R ->
  (Rabs (logit K c i n - logit K' c i n)
   <= delta * list_sum_R (fun j => Rabs (c j * K i j)) (seq 0%nat n))%R.
Proof.
  intros HK.
  apply (Rle_trans _
           (list_sum_R (fun j => (Rabs (c j) * (delta * Rabs (K i j)))%R)
              (seq 0%nat n))).
  - apply (quant_drift_exact K K' c (fun j => (delta * Rabs (K i j))%R) i n).
    intros j _. apply HK.
  - rewrite <- (list_sum_R_scale_l (fun j => Rabs (c j * K i j)) delta (seq 0%nat n)).
    apply list_sum_R_le_compat. intros j Hj.
    rewrite Rabs_mult. nra.
Qed.

(* ---------- Q5：均匀 ε 的 KD 同形推论 ---------- *)

Corollary quant_uniform_controls (K K' : nat -> nat -> R) (c : nat -> R)
        (n : nat) (eps dd : R) :
  (0 < n)%nat -> (0 <= eps)%R ->
  (forall i j, (i < n)%nat -> (j < n)%nat -> (Rabs (K i j - K' i j) <= eps))%R ->
  (list_sum_R (fun j => Rabs (c j)) (seq 0%nat n) <= dd)%R ->
  (list_sum_R (fun i => Rabs
     (softmax_l (fun i0 => logit K c i0 n) n i
      - softmax_l (fun i0 => logit K' c i0 n) n i))
     (seq 0%nat n) <= exp (2 * (eps * dd)) - 1)%R.
Proof.
  intros Hn Heps HK Hdd.
  apply (kernel_drift_controls_attention K K' c n eps dd); assumption.
Qed.

(* ---------- Q6：决策稳定性 I——logit 序在漂移下的保持（非平凡核心） ---------- *)

Lemma abs_band (x d : R) : (0 <= d)%R -> (Rabs x <= d)%R -> (- d <= x /\ x <= d)%R.
Proof.
  intros Hd H. split.
  - apply (Rle_trans _ (- Rabs x)).
    + lra.
    + pose proof (Rle_abs (- x)) as Hm. rewrite Rabs_Ropp in Hm. lra.
  - apply (Rle_trans _ (Rabs x)); [ apply Rle_abs | exact H ].
Qed.

Lemma drift_logit_order_stable (z z' : nat -> R) (k n : nat) (gap d : R) :
  (k < n)%nat ->
  (forall j, (j < n)%nat -> (z j + gap <= z k))%R ->
  (forall i, (i < n)%nat -> (Rabs (z i - z' i) <= d))%R ->
  (0 <= d)%R -> (2 * d < gap)%R ->
  (forall j, (j < n)%nat -> (z' j + (gap - 2 * d) <= z' k))%R.
Proof.
  intros Hk Htop Hdr Hd Hgap j Hj.
  pose proof (Htop j Hj) as Ht.
  destruct (abs_band _ _ Hd (Hdr j Hj)) as [Hj1 Hj2].
  destruct (abs_band _ _ Hd (Hdr k Hk)) as [Hk1 Hk2].
  lra.
Qed.

(* ---------- Q7：softmax 逐对单调 ---------- *)

Lemma softmax_mono_pair (z : nat -> R) (n a b : nat) :
  (0 < n)%nat -> (z b <= z a)%R ->
  (softmax_l z n b <= softmax_l z n a)%R.
Proof.
  intros Hn Hz.
  assert (Hpos := softmax_denom_pos z n Hn).
  unfold softmax_l. unfold Rdiv.
  apply Rmult_le_compat_r.
  - apply Rlt_le, Rinv_0_lt_compat, Hpos.
  - destruct (Req_dec (z b) (z a)) as [E | E].
    + rewrite E. apply Rle_refl.
    + apply Rlt_le. apply exp_increasing.
      destruct (Rle_lt_dec (z a) (z b)) as [Hge | Hlt].
      * exfalso. apply E. apply Rle_antisym; lra.
      * exact Hlt.
Qed.

(* ---------- Q8：决策稳定性 II——top-1 概率序保持（任意漂移源通用） ---------- *)

Theorem drift_top1_stable (z z' : nat -> R) (k n : nat) (gap d : R) :
  (0 < n)%nat -> (k < n)%nat ->
  (forall j, (j < n)%nat -> (z j + gap <= z k))%R ->
  (forall i, (i < n)%nat -> (Rabs (z i - z' i) <= d))%R ->
  (0 <= d)%R -> (2 * d < gap)%R ->
  (forall j, (j < n)%nat -> (softmax_l z' n j <= softmax_l z' n k))%R.
Proof.
  intros Hn Hk Htop Hdr Hd Hgap j Hj.
  assert (Hzle : (z' j <= z' k)%R).
  { assert (Hord := drift_logit_order_stable z z' k n gap d Hk Htop Hdr Hd Hgap j Hj).
    lra. }
  apply (softmax_mono_pair z' n k j Hn). exact Hzle.
Qed.

(* ---------- Q9：per-key 量化的 top-1 证书（部署级合成） ---------- *)

Corollary quant_column_top1 (K K' : nat -> nat -> R) (c e : nat -> R)
        (k n : nat) (gap : R) :
  (0 < n)%nat -> (k < n)%nat ->
  (forall j, (0 <= e j))%R ->
  (forall i j, (i < n)%nat -> (j < n)%nat -> (Rabs (K i j - K' i j) <= e j))%R ->
  (forall j, (j < n)%nat -> (logit K c j n + gap <= logit K c k n))%R ->
  (2 * list_sum_R (fun j => (Rabs (c j) * e j)%R) (seq 0%nat n) < gap)%R ->
  (forall j, (j < n)%nat ->
     (softmax_l (fun i0 => logit K' c i0 n) n j
      <= softmax_l (fun i0 => logit K' c i0 n) n k))%R.
Proof.
  intros Hn Hk He HK Htop Hgap j Hj.
  apply (drift_top1_stable
           (fun i0 => logit K c i0 n) (fun i0 => logit K' c i0 n) k n gap
           (list_sum_R (fun j0 => (Rabs (c j0) * e j0)%R) (seq 0%nat n))).
  - exact Hn.
  - exact Hk.
  - exact Htop.
  - intros i Hi. apply quant_column_drift; [ exact Hi | exact HK ].
  - apply list_sum_R_pos. intros i _. apply Rmult_le_pos; [ apply Rabs_pos | apply He ].
  - exact Hgap.
  - exact Hj.
Qed.

End Quant.

Print Assumptions Quant.quant_drift_exact.
Print Assumptions Quant.quant_column_drift.
Print Assumptions Quant.quant_column_controls_attention.
Print Assumptions Quant.quant_relative_drift.
Print Assumptions Quant.quant_uniform_controls.
Print Assumptions Quant.drift_top1_stable.
Print Assumptions Quant.quant_column_top1.
