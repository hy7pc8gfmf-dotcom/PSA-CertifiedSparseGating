(* ============================================================
   T4 核漂移定理（logit 层完整版）（z 工作区，E039；2026-08-22 第二批 ②）
   背景：PSA_framework.vo 当前对重建后的 ca_base.vo 过期
   （"inconsistent assumptions"），故本探针自包含（仅 ca_* 链），
   softmax 组合线留接口注释——PSA 重建后 5 行战术即可封口。

   KD1 list_sum_R 基础件（与 PhaseCoherence 同陈述自证）。
   KD2 drift_logit_bound：|Σ_j c_j·(K_ij − K'_ij)| ≤ dc·dd
        ——核逐点漂移 ≤ dc 且系数 ℓ1 ≤ dd ⟹ logit 漂移界。
   KD3 kernel_drift_logit（主定理）：∀ i<n，两组 logits 的逐点
        漂移 ≤ dc·dd。
   组合线（接口注释）：与 SoftmaxStability.softmax_l1_bound_exp
   （z z' n d：ℓ∞ 漂移 ≤ d ⟹ softmax ℓ1 TVD ≤ e^{2d}−1）合成得
        TVD ≤ e^{2·dc·dd} − 1
   ——对网格族（任意 a·N 窗口核相同，窗口无关性）Δ=0 ⟹ TVD=0。
   ============================================================ *)
Require Import Stdlib.Reals.Reals.
Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.Arith.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.micromega.Lra.
Require Import Stdlib.ZArith.ZArith.
Require Import ca_base.
Require Import ca_complex_foundation.
Require Import ca_independence.
Require Import ca_fourier.
Require Import ca_char_ortho.
Require Import ca_zeta_scaffold.
Import ComplexNumbers.
Import FourierAnalysis.

Open Scope R_scope.
Open Scope nat_scope.

Module KernelDrift.

(* ---------- KD1：list_sum_R 基础件（seq 口径） ---------- *)

Fixpoint list_sum_R (f : nat -> R) (l : list nat) : R :=
  match l with
  | nil => 0%R
  | h :: t => (f h + list_sum_R f t)%R
  end.

Lemma list_sum_R_ext (f g : nat -> R) (l : list nat) :
  (forall i, In i l -> (f i)%R = (g i)%R) -> (list_sum_R f l)%R = (list_sum_R g l)%R.
Proof.
  intros H. induction l as [| h t IH]; simpl; [reflexivity | ].
  rewrite (H h (or_introl eq_refl)), IH; [reflexivity | ].
  intros i Hi. apply H. right. exact Hi.
Qed.

Lemma list_sum_R_plus (f g : nat -> R) (l : list nat) :
  (list_sum_R (fun i => (f i + g i)%R) l)%R
  = ((list_sum_R f l) + (list_sum_R g l))%R.
Proof.
  induction l as [| h t IH]; simpl; [ring | ].
  rewrite IH. ring.
Qed.

Lemma list_sum_R_neg (f : nat -> R) (l : list nat) :
  (list_sum_R (fun i => (- f i)%R) l)%R = ((- list_sum_R f l))%R.
Proof.
  induction l as [| h t IH]; simpl; [ring | ].
  rewrite IH. ring.
Qed.

Lemma list_sum_R_abs (f : nat -> R) (l : list nat) :
  ((Rabs (list_sum_R f l)) <= (list_sum_R (fun i => Rabs (f i)) l))%R.
Proof.
  induction l as [| h t IH]; simpl.
  - rewrite Rabs_R0. apply Rle_refl.
  - apply (Rle_trans _ ((Rabs (f h)) + (Rabs (list_sum_R f t)))%R).
    + apply Rabs_triang.
    + apply Rplus_le_compat_l; exact IH.
Qed.

Lemma list_sum_R_le (f g : nat -> R) (l : list nat) :
  (forall i, In i l -> (f i <= g i)%R) -> ((list_sum_R f l) <= (list_sum_R g l))%R.
Proof.
  intros H. induction l as [| h t IH]; simpl.
  - apply Rle_refl.
  - apply Rplus_le_compat.
    + apply H. left. reflexivity.
    + apply IH. intros i Hi. apply H. right. exact Hi.
Qed.

Lemma list_sum_R_scal (a : R) (f : nat -> R) (l : list nat) :
  (list_sum_R (fun i => (a * f i)%R) l)%R = ((a * list_sum_R f l))%R.
Proof.
  induction l as [| h t IH]; simpl; [ring | rewrite IH; ring].
Qed.

Lemma In_seq_lt (j n : nat) : In j (seq 0 n) -> (j < n)%nat.
Proof.
  intros Hj.
  destruct (In_nth (seq 0 n) j 0%nat Hj) as [k [Hk Hkth]].
  rewrite length_seq in Hk.
  assert (Hkseq : (nth k (seq 0 n) 0%nat = k)%nat)
    by (rewrite (@seq_nth n 0%nat k 0%nat Hk); lia).
  rewrite Hkth in Hkseq. lia.
Qed.

(* ---------- KD2：logit 漂移界 ---------- *)

Theorem drift_logit_bound (K K' : nat -> nat -> R) (c : nat -> R)
          (n i : nat) (dc dd : R) :
  (i < n)%nat -> (0 <= dc)%R ->
  (forall i0 j, (i0 < n)%nat -> (j < n)%nat -> ((Rabs ((K i0 j) - (K' i0 j))) <= dc)%R) ->
  ((list_sum_R (fun j => Rabs (c j)) (seq 0 n)) <= dd)%R ->
  ((Rabs ((list_sum_R (fun j => (c j * K i j)%R) (seq 0 n))
          - (list_sum_R (fun j => (c j * K' i j)%R) (seq 0 n)))) <= (dc * dd))%R.
Proof.
  intros Hi Hdc HK Hdd.
  (* 差 = Σ c_j·(K − K') *)
  assert (Hdiff : ((list_sum_R (fun j => (c j * K i j)%R) (seq 0 n))
                   - (list_sum_R (fun j => (c j * K' i j)%R) (seq 0 n)))%R
                  = (list_sum_R (fun j => (c j * K i j - c j * K' i j)%R) (seq 0 n))%R).
  { apply eq_trans with ((list_sum_R (fun j => ((c j * K i j)%R + (- (c j * K' i j))%R)%R) (seq 0 n))).
    - rewrite (list_sum_R_plus (fun j => (c j * K i j)%R)
                    (fun j => (- (c j * K' i j))%R) (seq 0 n)).
      rewrite (list_sum_R_neg (fun j => (c j * K' i j)%R) (seq 0 n)).
      ring.
    - apply list_sum_R_ext. intros j Hj. ring. }
  rewrite Hdiff.
  apply (Rle_trans _ (list_sum_R (fun j => (Rabs ((c j * K i j) - (c j * K' i j)))%R) (seq 0 n))).
  - apply list_sum_R_abs.
  - apply (Rle_trans _ (list_sum_R (fun j => (dc * Rabs (c j))%R) (seq 0 n))).
    + apply list_sum_R_le. intros j Hj.
      assert (Hjn : (j < n)%nat) by (apply In_seq_lt; exact Hj).
      assert (HKj : (Rabs ((K i j) - (K' i j)) <= dc)%R) by (apply HK; assumption).
      replace (((c j * K i j)) - ((c j * K' i j)))%R with ((c j) * ((K i j) - (K' i j)))%R by ring.
      rewrite Rabs_mult.
      rewrite (Rmult_comm (Rabs (c j)) (Rabs ((K i j) - (K' i j)))).
      apply Rmult_le_compat_r.
      * apply Rabs_pos.
      * exact HKj.
    + rewrite list_sum_R_scal. apply Rmult_le_compat_l; [exact Hdc | exact Hdd].
Qed.

(* ---------- KD3：主定理（∀ i 版） ---------- *)

Theorem kernel_drift_logit (K K' : nat -> nat -> R) (c : nat -> R)
          (n : nat) (dc dd : R) :
  (0 < n)%nat -> (0 <= dc)%R ->
  (forall i j, (i < n)%nat -> (j < n)%nat -> ((Rabs ((K i j) - (K' i j))) <= dc)%R) ->
  ((list_sum_R (fun j => Rabs (c j)) (seq 0 n)) <= dd)%R ->
  (forall i, (i < n)%nat ->
     ((Rabs ((list_sum_R (fun j => (c j * K i j)%R) (seq 0 n))
             - (list_sum_R (fun j => (c j * K' i j)%R) (seq 0 n)))) <= (dc * dd))%R).
Proof.
  intros Hn Hdc HK Hdd i Hi.
  apply drift_logit_bound; assumption.
Qed.

End KernelDrift.

Print Assumptions KernelDrift.drift_logit_bound.
Print Assumptions KernelDrift.kernel_drift_logit.
