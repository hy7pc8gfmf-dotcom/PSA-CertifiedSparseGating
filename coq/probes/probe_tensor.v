(* ============================================================
   T5 一般维张量定理（z 工作区，E039；2026-08-22 第二批 ⑥）
   目标（交互文档 §2-T5）：把 2D/3D/4D 张量三实例合并为 ∀N 定理：
     N 轴张量积族的 Gershgorin 行和界 M^{(N)} = Π_k(1+r_k) − 1；
     均匀轴（r_k ≡ 4K_C）时 = (1+r)^N − 1
   ——"Theoretically Composable" 从评注变定理（论文B §6 跨维推测得证）。

   抽象层定位：abstract_unconditional_basis（ca_decay:4764）只要求
   "delta 行和 ≤ M_bound"；张量实例的全部难度在行和的 N 维增长。
   本探针把这一步抽成纯算术定理（自包含，零 ca_* 依赖）：

   TN0 list_sum_R 基础件 + tsum_ge_0。
   TN1 tsum/tdiag：N 轴张量行和/对角贡献的归纳定义
       （tsum k axes d idx = Σ_{j∈l_k} d·(tsum (S k) rest)，
        tdiag = Π_k d k i_k i_k；rprod k r axes = Π_k (1+r k)）。
   TN2 tsum_step：单轴因子化 Σ_j a_j·X = (Σ a_j)·X。
   TN3 tsum_bound：d ≥ 0、逐轴行和 ≤ r_k ⟹ tsum ≤ Π(1+r_k)。
   TN4 tdiag_one：逐轴对角 d k i i = 1 ⟹ tdiag = 1
       （范数 1 原子的张量积对角内积恰为 1——对角元组贡献无交叉项）。
   TN5 tensor_offdiag_bound（主定理）：
       off-diag 行和（tsum − tdiag）≤ Π(1+r_k) − 1。
   TN6 tensor_bound_uniform_N（均匀轴闭式）：
       N 轴、r_k ≡ r ⟹ ≤ (1+r)^N − 1（rpowN 递归幂）。
   对接：2D/3D/4D 实例 = TN6 的 N=2/3/4 特例 + abstract_unconditional_basis
   的 M_bound := (C³/2)·((1+4K_C)^N − 1)（C³/2 因子来自单轴 decay 常数，
   在实例层引入——本探针只管组合指数增长部分）。
   审计：Print Assumptions 尾部（预期 ≤ Dedekind 两件）。
   ============================================================ *)
Require Import Stdlib.Reals.Reals.
Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.Arith.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.micromega.Lra.
Import ListNotations.

Open Scope R_scope.
Open Scope nat_scope.

Module TensorDim.

(* ---------- TN0：list_sum_R 基础件（自包含复制） ---------- *)

Fixpoint list_sum_R (f : nat -> R) (l : list nat) : R :=
  match l with
  | nil => 0%R
  | h :: t => (f h + list_sum_R f t)%R
  end.

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
  ((list_sum_R (fun i => (a * f i)%R) l))%R = ((a * list_sum_R f l))%R.
Proof.
  induction l as [| h t IH]; simpl; [ring | rewrite IH; ring].
Qed.

Lemma list_sum_R_ge_0 (f : nat -> R) (l : list nat) :
  (forall i, (0 <= f i)%R) -> (0 <= list_sum_R f l)%R.
Proof.
  intros H. induction l as [| h t IH]; simpl.
  - apply Rle_refl.
  - apply Rplus_le_le_0_compat; [apply H | exact IH].
Qed.

(* ---------- TN1：N 轴张量行和 / 对角贡献 / 均匀界乘积 ---------- *)
(* axes : list (list nat)，第 k 轴的指标集（绝对轴号 k，不随归纳漂移）；
   d k i j : 第 k 轴的衰减函数（张量原子内积的绝对值界）；
   idx k : 当前行在第 k 轴的指标。
   tsum = 行和：乘积指标集上的全和（逐轴迭代求和）；
   tdiag = 对角元组的贡献：Π_k d k (idx k) (idx k)；
   rprod = Π_k (1 + r k)。 *)

Fixpoint tsum (k : nat) (axes : list (list nat)) (d : nat -> nat -> nat -> R)
         (idx : nat -> nat) : R :=
  match axes with
  | nil => 1%R
  | l :: rest => list_sum_R (fun j => (d k (idx k) j * tsum (S k) rest d idx)%R) l
  end.

Fixpoint tdiag (k : nat) (axes : list (list nat)) (d : nat -> nat -> nat -> R)
         (idx : nat -> nat) : R :=
  match axes with
  | nil => 1%R
  | _ :: rest => (d k (idx k) (idx k) * tdiag (S k) rest d idx)%R
  end.

Fixpoint rprod (k : nat) (r : nat -> R) (axes : list (list nat)) : R :=
  match axes with
  | nil => 1%R
  | _ :: rest => ((1 + r k) * rprod (S k) r rest)%R
  end.

Fixpoint rpowN (x : R) (N : nat) : R :=
  match N with
  | O => 1%R
  | S m => (x * rpowN x m)%R
  end.

(* ---------- TN0b：非负性 ---------- *)

Lemma rmult_nonneg (a b : R) : (0 <= a)%R -> (0 <= b)%R -> (0 <= a * b)%R.
Proof.
  intros Ha Hb.
  apply (Rle_trans _ (a * 0)%R).
  - rewrite Rmult_0_r. apply Rle_refl.
  - apply Rmult_le_compat_l; [exact Ha | exact Hb].
Qed.

Lemma tsum_ge_0 (k : nat) (axes : list (list nat)) (d : nat -> nat -> nat -> R)
      (idx : nat -> nat) :
  (forall k0 i j, (0 <= d k0 i j)%R) -> (0 <= tsum k axes d idx)%R.
Proof.
  intros Hd. revert k. induction axes as [| l rest IH]; intros k; simpl.
  - apply Rle_0_1.
  - apply list_sum_R_ge_0. intros j.
    apply (rmult_nonneg (d k (idx k) j) (tsum (S k) rest d idx));
      [apply Hd | apply IH; exact Hd].
Qed.

Lemma rprod_ge_1 (r : nat -> R) (axes : list (list nat)) :
  (forall k0, (0 <= r k0)%R) -> (forall k, (1 <= rprod k r axes))%R.
Proof.
  intros Hr. induction axes as [| l rest IH]; intros k; simpl.
  - apply Rle_refl.
  - assert (HP : (1 <= rprod (S k) r rest)%R) by (apply IH; exact Hr).
    apply (Rle_trans _ (1 * rprod (S k) r rest)%R).
    + rewrite Rmult_1_l. exact HP.
    + assert (Hrk : (0 <= r k)%R) by apply Hr.
      rewrite Rmult_1_l.
      apply (Rle_trans _ (rprod (S k) r rest * 1)%R).
      * rewrite Rmult_1_r. apply Rle_refl.
      * rewrite Rmult_1_r.
        replace ((1 + r k) * rprod (S k) r rest)%R
          with (rprod (S k) r rest + r k * rprod (S k) r rest)%R by ring.
        assert (HB : (0 <= r k * rprod (S k) r rest)%R).
        { apply rmult_nonneg; [exact Hrk | ].
          apply (Rle_trans _ 1%R); [apply Rle_0_1 | exact HP]. }
        lra.
Qed.

Lemma list_sum_R_scal_r (f : nat -> R) (a : R) (l : list nat) :
  ((list_sum_R (fun i => (f i * a)%R) l))%R = ((list_sum_R f l) * a)%R.
Proof.
  induction l as [| h t IH]; simpl; [ring | rewrite IH; ring].
Qed.

(* ---------- TN2：单轴因子化 ---------- *)

Lemma tsum_step (k : nat) (l : list nat) (rest : list (list nat))
      (d : nat -> nat -> nat -> R) (idx : nat -> nat) :
  (tsum k (l :: rest) d idx)%R
  = ((list_sum_R (fun j => d k (idx k) j) l) * tsum (S k) rest d idx)%R.
Proof.
  simpl. apply list_sum_R_scal_r.
Qed.

(* ---------- TN2b：轴号平移引理（归纳核心：N+1 维 = N 维 ⊗ 1 维） ---------- *)

Lemma list_sum_R_ext (f g : nat -> R) (l : list nat) :
  (forall i, In i l -> (f i = g i)%R) -> (list_sum_R f l = list_sum_R g l)%R.
Proof.
  intros H. induction l as [| h t IH]; simpl; [reflexivity | ].
  rewrite (H h (or_introl eq_refl)), IH; [reflexivity | ].
  intros i Hi. apply H. right. exact Hi.
Qed.

Lemma tsum_shift : forall (rest : list (list nat)) (k : nat)
      (d : nat -> nat -> nat -> R) (idx : nat -> nat),
  (tsum (S k) rest d idx)%R
  = (tsum k rest (fun a b c => (d (S a) b c)%R) (fun a => idx (S a)))%R.
Proof.
  induction rest as [| l rest' IH]; intros k d idx; simpl; [reflexivity | ].
  rewrite (IH (S k) d idx). apply list_sum_R_ext. intros i _. reflexivity.
Qed.

Lemma rprod_shift : forall (rest : list (list nat)) (k : nat) (r : nat -> R),
  (rprod (S k) r rest)%R = (rprod k (fun k0 => (r (S k0))%R) rest)%R.
Proof.
  induction rest as [| l rest' IH]; intros k r; simpl; [reflexivity | ].
  rewrite (IH (S k) r). reflexivity.
Qed.

(* ---------- TN3：逐轴行和界 ⟹ tsum ≤ Π(1+r_k) ---------- *)

Theorem tsum_bound (axes : list (list nat)) :
  forall (d : nat -> nat -> nat -> R) (idx : nat -> nat) (r : nat -> R),
  (forall k0 i j, (0 <= d k0 i j)%R) ->
  (forall k0, (0 <= r k0)%R) ->
  (forall k0, ((list_sum_R (fun j => d k0 (idx k0) j) (nth k0 axes [])) <= (r k0))%R) ->
  ((tsum 0%nat axes d idx) <= (rprod 0%nat r axes))%R.
Proof.
  induction axes as [| l rest IH]; intros d idx r Hdnn Hr Hrow.
  - simpl. apply Rle_refl.
  - rewrite tsum_step.
    rewrite (tsum_shift rest 0%nat d idx).
    simpl (rprod 0%nat r (l :: rest)).
    rewrite (rprod_shift rest 0%nat r).
    assert (Hdnn' : forall k0 i j, (0 <= (fun a b c => d (S a) b c)%R k0 i j)%R)
      by (intros k0 i j; apply Hdnn).
    assert (Hr' : forall k0, (0 <= (fun k0 => r (S k0))%R k0)%R) by (intros k0; apply Hr).
    assert (Hrow' : forall k0,
      ((list_sum_R (fun j => (fun a b c => d (S a) b c)%R k0
                     ((fun a => idx (S a)) k0) j) (nth k0 rest []))
       <= ((fun k0 => r (S k0))%R k0))%R).
    { intros k0. cbn beta. specialize (Hrow (S k0)).
      exact Hrow. }
    assert (IH' : (tsum 0%nat rest (fun a b c => (d (S a) b c)%R) (fun a => idx (S a))
                   <= rprod 0%nat (fun k0 => (r (S k0))%R) rest)%R)
      by (apply IH; [exact Hdnn' | exact Hr' | exact Hrow']).
    assert (HP' : (0 <= rprod 0%nat (fun k0 => (r (S k0))%R) rest)%R).
    { apply (Rle_trans _ 1%R); [apply Rle_0_1 | ].
      apply rprod_ge_1. intros k0. apply Hr. }
    assert (HA0 : (0 <= list_sum_R (fun j => d 0%nat (idx 0%nat) j) l)%R).
    { apply list_sum_R_ge_0. intros i. apply Hdnn. }
    apply (Rle_trans _ ((list_sum_R (fun j => d 0%nat (idx 0%nat) j) l)
                        * rprod 0%nat (fun k0 => (r (S k0))%R) rest)%R).
    + apply Rmult_le_compat_l; [exact HA0 | exact IH'].
    + apply (Rle_trans _ ((r 0%nat) * rprod 0%nat (fun k0 => (r (S k0))%R) rest)%R).
      * apply Rmult_le_compat_r; [exact HP' | apply Hrow].
      * apply Rmult_le_compat_r; [exact HP' | lra].
Qed.

(* ---------- TN4：对角元组贡献恰为 1 ---------- *)

Lemma tdiag_one_gen : forall (axes : list (list nat)) (k : nat)
      (d : nat -> nat -> nat -> R) (idx : nat -> nat),
  (forall k0 i, (d k0 i i = 1)%R) -> (tdiag k axes d idx = 1)%R.
Proof.
  induction axes as [| l rest IH]; intros k d idx Hd; simpl; [reflexivity | ].
  rewrite (Hd k (idx k)), (IH (S k) d idx Hd). ring.
Qed.

Lemma tdiag_one (axes : list (list nat)) (d : nat -> nat -> nat -> R)
      (idx : nat -> nat) :
  (forall k0 i, (d k0 i i = 1)%R) -> (tdiag 0%nat axes d idx = 1)%R.
Proof.
  intros Hd. apply (tdiag_one_gen axes 0%nat d idx Hd).
Qed.

(* ---------- TN5：主定理——off-diag 行和 ≤ Π(1+r_k) − 1 ---------- *)

Theorem tensor_offdiag_bound (axes : list (list nat))
        (d : nat -> nat -> nat -> R) (idx : nat -> nat) (r : nat -> R) :
  (forall k0 i j, (0 <= d k0 i j)%R) ->
  (forall k0, (0 <= r k0)%R) ->
  (forall k0 i, (d k0 i i = 1)%R) ->
  (forall k0, ((list_sum_R (fun j => d k0 (idx k0) j) (nth k0 axes [])) <= (r k0))%R) ->
  (((tsum 0%nat axes d idx) - (tdiag 0%nat axes d idx)) <= ((rprod 0%nat r axes) - 1))%R.
Proof.
  intros Hdnn Hr Hdiag Hrow.
  assert (H1 : (tsum 0%nat axes d idx <= rprod 0%nat r axes)%R)
    by (apply (tsum_bound axes d idx r Hdnn Hr Hrow)).
  assert (H2 : (tdiag 0%nat axes d idx = 1)%R) by (apply tdiag_one; exact Hdiag).
  assert (H3 : (1 <= rprod 0%nat r axes)%R) by (apply rprod_ge_1; exact Hr).
  lra.
Qed.

(* ---------- TN6：均匀轴闭式——(1+r)^N − 1 ---------- *)

Lemma rprod_const : forall (r : R) (axes : list (list nat)) (k : nat),
  (rprod k (fun _ => r) axes = rpowN (1 + r) (length axes))%R.
Proof.
  intros r. induction axes as [| l rest IH]; intros k.
  - reflexivity.
  - simpl. rewrite (IH (S k)). simpl. reflexivity.
Qed.

Theorem tensor_bound_uniform_N (N : nat) (axes : list (list nat))
        (d : nat -> nat -> nat -> R) (idx : nat -> nat) (r : R) :
  ((length axes) = N)%nat ->
  (forall k0 i j, (0 <= d k0 i j)%R) ->
  (0 <= r)%R ->
  (forall k0 i, (d k0 i i = 1)%R) ->
  (forall k0, ((list_sum_R (fun j => d k0 (idx k0) j) (nth k0 axes [])) <= r)%R) ->
  (((tsum 0%nat axes d idx) - (tdiag 0%nat axes d idx))
   <= ((rpowN (1 + r) N) - 1))%R.
Proof.
  intros Hlen Hdnn Hr Hdiag Hrow.
  apply (Rle_trans _ ((rprod 0%nat (fun _ => r) axes) - 1)%R).
  - apply (tensor_offdiag_bound axes d idx (fun _ => r)).
    + exact Hdnn.
    + intros k0. exact Hr.
    + exact Hdiag.
    + exact Hrow.
  - rewrite (rprod_const r axes 0%nat). rewrite <- Hlen. apply Rle_refl.
Qed.

End TensorDim.

Print Assumptions TensorDim.tsum_bound.
Print Assumptions TensorDim.tdiag_one.
Print Assumptions TensorDim.tensor_offdiag_bound.
Print Assumptions TensorDim.tensor_bound_uniform_N.
