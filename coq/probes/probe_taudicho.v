(* ============================================================
   τ-dichotomy 收尾（z 工作区，E039 纪律；2026-08-22 第二批 ③）
   前置：probe_collision（C2 推论 + C4 τ 刻画）。

   论文B 机制节的形式化闭包：带 n 的碰撞对 (k, k+n) 相对
   训练窗 T 与评估窗 T' 的三分：
   D1 tau_inwindow：n < T ⟺ 窗内可观测碰撞对存在（与 C4 的
      trained_collision_pair_charac 同口径：计数 = T − n）。
   D2 tau_ood：T ≤ T'、n ≥ T 时，n < T' ⟺ 存在"训练外碰撞对"
      k < T ≤ k+n < T'（τ≈0 带的首批碰撞全部 OOD——覆盖梯度
      机制的形式化核心：τ(n)=T−n 截断语义已由 C4 给出）。
   D3 tau_split（三分定理）：任意带 n 恰居其一：窗内可观测 /
      首碰撞 OOD（T ≤ n < T'）/ T' 内无碰撞对。
   ============================================================ *)
Require Import Stdlib.Reals.Reals.
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
Require Import probe_collision.
Import ComplexNumbers.
Import FourierAnalysis.
Import CollisionDistance.

Open Scope R_scope.
Open Scope complex_scope.
Open Scope nat_scope.

Module TauDichotomy.

(* D1：窗内可观测 ⟺ n < T *)
Theorem tau_inwindow (T n : nat) :
  ((n < T)%nat <-> (exists k, ((k + n < T)%nat /\ (k < T)%nat))).
Proof.
  split.
  - intros H. exists 0%nat. lia.
  - intros [k [H1 H2]]. lia.
Qed.

(* D2：τ≈0 带的首碰撞全在 OOD（训练窗 T，评估窗 T' ≥ T） *)
Theorem tau_ood (T T' n : nat) :
  (0 < T)%nat -> (T <= T')%nat -> (T <= n)%nat ->
  ((n < T')%nat <-> (exists k, ((k < T)%nat /\ ((k + n < T')%nat /\ (T <= k + n)%nat)))).
Proof.
  intros HT HTT' Hn.
  split.
  - intros H. exists 0%nat. lia.
  - intros [k [Hk [H1 H2]]].
    apply Nat.le_lt_trans with (k + n)%nat.
    + lia.
    + exact H1.
Qed.

(* D3：三分定理（按"首批碰撞落点"分类） *)
Theorem tau_split (T T' n : nat) :
  (0 < T)%nat -> (T <= T')%nat ->
  (((n < T)%nat /\ (exists k, ((k + n < T)%nat /\ (k < T)%nat)))
   \/ (((T <= n)%nat /\ (n < T')%nat)
       /\ (exists k, ((k < T)%nat /\ ((T <= k + n)%nat /\ (k + n < T')%nat)))
       /\ ~ (exists k, ((k + n < T)%nat /\ (k < T)%nat)))
   \/ ((T' <= n)%nat /\ ~ (exists k, ((k + n < T')%nat)))).
Proof.
  intros HT HTT'.
  destruct (lt_dec n T) as [HnT | HnT].
  - left. split; [exact HnT | exists 0%nat; lia].
  - destruct (lt_dec n T') as [HnT' | HnT'].
    + right; left. split; [split; lia | ].
      split.
      * exists 0%nat. lia.
      * intros [k [H1 H2]]. lia.
    + right; right. split; [lia | ].
      intros [k Hk]. lia.
Qed.

(* 与 C4 的接口：τ 计数 = 窗内碰撞对计数的刻画 *)
Theorem tau_count_link (T n : nat) :
  ((n < T)%nat <-> (exists k, ((k < tau T n)%nat /\ ((k + n < T)%nat /\ (k < T)%nat)))).
Proof.
  split.
  - intros H. exists 0%nat. split; [unfold tau; lia | ].
    split; lia.
  - intros [k [H1 [H2 H3]]]. unfold tau in H1. lia.
Qed.

End TauDichotomy.

Print Assumptions TauDichotomy.tau_ood.
Print Assumptions TauDichotomy.tau_split.
