(* ============================================================
   前置：PSA_framework.vo 已对当前 ca_base.vo 重建（2026-08-22，
   本轮执行，EXIT=0）；本文件 Require PSA_framework + probe_kerneldrift。

   SD1 kernel_drift_controls_attention（主定理，T4 完全体）：
     核逐点漂移 ≤ dc（全 i,j）、系数 ℓ1 ≤ dd
     ⟹ softmax 输出 ℓ1 TVD ≤ e^{2·dc·dd} − 1
   ——coherence_controls_attention（PSA_framework:6528）的核漂移姊妹定理：
     原版是"系数漂移 × 固定核"，本版是"固定系数 × 核漂移"（长度外推/
     蒸馏/量化场景的口径）。logit 层直接复用 KernelDrift.kernel_drift_logit。

   SD2 kernel_identical_tvd_zero（网格族实例的退化端点）：
     K = K' ⟹ TVD ≤ e^{2·0·dd} − 1 = 0——"注意力核在长度外推下的
     表示级不变性"（网格/偏移网格族任意 a·N 窗口核相同，T1a）成为
     带 e^{2·dc·dd}−1 证书的陈述的 0 端点。

   归宿建议：并入 PSA_framework 的 PhaseCoherence Module（作
   coherence_controls_attention 姊妹定理，src 侧同事操作）——
   SoftmaxStability/list_sum_R 基础件全在彼处；本探针即验证件。
   ============================================================ *)
Require Import Stdlib.Reals.Reals.
Require Import Stdlib.Arith.Arith.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.micromega.Lra.
Require Import Stdlib.Lists.List.
Require Import PSA_framework.
Require Import probe_kerneldrift.
Import PSA_framework.RowTruncation.
Import PSA_framework.SoftmaxStability.

Open Scope R_scope.

Module SoftmaxDrift.

(* 桥接：KernelDrift 的 Fixpoint 版与 PSA 的 fold_right 版逐点相等 *)
Lemma kd_psa_list_sum_eq (f : nat -> R) (l : list nat) :
  (KernelDrift.list_sum_R f l = list_sum_R f l)%R.
Proof.
  induction l as [| h t IH]; simpl; [reflexivity | rewrite IH; reflexivity].
Qed.

(* ---------- SD1：主定理（T4 完全体） ---------- *)

Theorem kernel_drift_controls_attention (K K' : nat -> nat -> R)
        (c : nat -> R) (n : nat) (dc dd : R) :
  (0 < n)%nat -> (0 <= dc)%R ->
  (forall i j, (i < n)%nat -> (j < n)%nat -> (Rabs (K i j - K' i j) <= dc)%R) ->
  (list_sum_R (fun j => Rabs (c j)) (seq 0%nat n) <= dd)%R ->
  (list_sum_R (fun i => Rabs
     (softmax_l (fun i0 => list_sum_R (fun j => (c j * K i0 j)%R) (seq 0%nat n)) n i
      - softmax_l (fun i0 => list_sum_R (fun j => (c j * K' i0 j)%R) (seq 0%nat n)) n i))
     (seq 0%nat n) <= exp (2 * (dc * dd)) - 1)%R.
Proof.
  intros Hn Hdc HK Hdd.
  assert (Hdd0 : (0 <= dd)%R).
  { apply (Rle_trans _ (list_sum_R (fun j => Rabs (c j)) (seq 0%nat n))).
    - apply list_sum_R_pos. intros i _. apply Rabs_pos.
    - exact Hdd. }
  apply (softmax_l1_bound_exp
           (fun i0 => list_sum_R (fun j => (c j * K i0 j)%R) (seq 0%nat n))
           (fun i0 => list_sum_R (fun j => (c j * K' i0 j)%R) (seq 0%nat n))
           n (dc * dd) Hn).
  - apply Rmult_le_pos; auto.
  - intros k Hk.
    assert (Hddk : (KernelDrift.list_sum_R (fun j => Rabs (c j)) (seq 0%nat n) <= dd)%R).
    { rewrite kd_psa_list_sum_eq. exact Hdd. }
    assert (HKD : (Rabs (KernelDrift.list_sum_R (fun j => (c j * K k j)%R) (seq 0%nat n)
                    - KernelDrift.list_sum_R (fun j => (c j * K' k j)%R) (seq 0%nat n))
                   <= dc * dd)%R)
      by (apply (KernelDrift.kernel_drift_logit K K' c n dc dd Hn Hdc HK Hddk k Hk)).
    rewrite kd_psa_list_sum_eq in HKD.
    rewrite kd_psa_list_sum_eq in HKD.
    exact HKD.
Qed.

(* ---------- SD2：退化端点（K = K' ⟹ TVD 界 = 0） ---------- *)

Corollary kernel_identical_tvd_zero (K : nat -> nat -> R)
        (c : nat -> R) (n : nat) (dd : R) :
  (0 < n)%nat ->
  (list_sum_R (fun j => Rabs (c j)) (seq 0%nat n) <= dd)%R ->
  (list_sum_R (fun i => Rabs
     (softmax_l (fun i0 => list_sum_R (fun j => (c j * K i0 j)%R) (seq 0%nat n)) n i
      - softmax_l (fun i0 => list_sum_R (fun j => (c j * K i0 j)%R) (seq 0%nat n)) n i))
     (seq 0%nat n) <= exp (2 * (0 * dd)) - 1)%R.
Proof.
  intros Hn Hdd.
  apply (kernel_drift_controls_attention K K c n 0 dd Hn (Rle_refl 0%R)).
  - intros i j _ _.
    replace (K i j - K i j) with 0%R by ring.
    rewrite Rabs_R0. apply Rle_refl.
  - exact Hdd.
Qed.

End SoftmaxDrift.

Print Assumptions SoftmaxDrift.kernel_drift_controls_attention.
Print Assumptions SoftmaxDrift.kernel_identical_tvd_zero.
