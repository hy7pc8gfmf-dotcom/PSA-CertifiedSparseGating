(* ============================================================
   CS-5：offset-grid 无关性量化（z 区，2026-08-29）
   任务书：压缩感知定理补齐-CS侦察-20260822.md §2 CS-5

   数学内容（ogrid 实验——论文 B ogrid @4096 = 19.30 恶化——的定理侧）：
     CS5a `cs5_offset_pair`（★offset 无关性）：同族平移 t→t+δ 下任意
         跨网格对的相干界**与 δ 无关**——偏移在同族对的差频中相消
         （pair_eq_rotdiff + R 层消元），pair_dirichlet 直接接管：
         |⟨ψ_{t1+δ}, ψ_{t2+δ}⟩| ≤ N/(2·min(j mod N, N−j mod N))，
         右端不含 δ。这就是"offset-grid 无关性"的定理形式：
         加偏移不改变跨网格对的相干证书。
     CS5b `cs5_golden_moat`（黄金比护城河命名系）：golden 阶梯近碰撞
         下界 1/(3d) ≤ |d·φ_gold − m|（golden_near_collision 实例化）。
     CS5c `cs5_gold_not_grid`（★偏移真离开网格）：φ_gold ∉ ℤ——
         若 phi_gold = IZR m 则 d=1 护城河给 1/3 ≤ 0 矛盾——黄金比
         偏移确实不在纯网格上，offset 语义非空。
     组合语义：跨网格对由 CS5a 的 δ-无关界控制；golden 同族对由 CS5b
         护城河保证非碰撞（近碰分数距离 ≥ 1/(3d)，RIP 证书通道可用）。
   依赖：probe_pairdirichlet（PairDirichlet.pair_dirichlet/pair_eq_rotdiff，
   Dirichlet 跨网格引擎）+ probe_nearcoll（NearColl.phi_gold/
   golden_near_collision_gold，1/(3d) 护城河）。
   审计：Print Assumptions 尾部。
   ============================================================ *)
From Stdlib Require Import Reals.
From Stdlib Require Import QArith.
From Stdlib Require Import ZArith.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.micromega.Lra.
From Stdlib Require Import Arith.
From Stdlib Require Import List.
Import ListNotations.
Require Import ca_base.
Require Import ca_complex_foundation.
Require Import ca_basis.
Import UnconditionalBasis.
Require Import ca_independence.
Require Import Stdlib.Reals.RIneq.
Require Import ca_fourier.
Require Import ca_char_ortho.
Require Import ca_zeta_scaffold.
Require Import ca_log_bounds.
Require Import ca_complex_log.
Require Import probe_grid_ortho.
Require Import probe_parseval.
Require Import probe_partial.
Require Import probe_pairdirichlet.
Require Import probe_nearcoll.
Import ComplexNumbers.
Import FourierAnalysis.
Import GridOrtho.
Import TPartial.
Import PairDirichlet.
Import NearColl.

(* E138①：Notation 注册（8 项，恢复 Stdlib nat 记号——防 mathcomp 污染） *)
Notation "a + b" := (Nat.add a b) (at level 50, left associativity) : nat_scope.
Notation "a - b" := (Nat.sub a b) (at level 50, left associativity) : nat_scope.
Notation "a * b" := (Nat.mul a b) (at level 40, left associativity) : nat_scope.
Notation "a <= b" := (Nat.le a b) (at level 70, no associativity) : nat_scope.
Notation "a < b" := (Nat.lt a b) (at level 70, no associativity) : nat_scope.
Notation "a >= b" := (Nat.le b a) (at level 70, no associativity) : nat_scope.
Notation "a > b" := (Nat.lt b a) (at level 70, no associativity) : nat_scope.

Local Open Scope nat_scope.
Local Open Scope complex_scope.
Local Open Scope R_scope.

(* E152：跨 flavor 桥——Stdlib ≤ → mathcomp leq bool（pair_dirichlet 的
   mathcomp 风味前提专用；leq 展开 eq_op → Nat.eqb_eq → sub_0_le） *)
Lemma le_Prop_to_mc (w1 w2 : nat) : (w1 <= w2)%nat -> ssrnat.leq w1 w2 = true.
Proof.
  intros H. unfold ssrnat.leq, eqtype.eq_op. simpl.
  apply Nat.eqb_eq. apply Nat.sub_0_le. exact H.
Qed.

Module CSFive.

(* ---------- CS5a：offset 无关性（★同族平移下跨网格对界不变） ---------- *)

Theorem cs5_offset_pair (N j W : nat) (t1 t2 delta : R) :
  (2 <= N)%nat -> (j mod N <> 0)%nat ->
  ((t1 - t2) = (2 * PI * INR j / INR N))%R ->
  (Cnorm (PrimeEmbedding.Csum
      (fun k => rot_atom (t1 + delta) k *c Cconj (rot_atom (t2 + delta) k)) W)
    <= INR N / (2 * INR (Nat.min (j mod N) (N - j mod N))))%R.
Proof.
  intros HN Hneq Hdiff.
  apply (pair_dirichlet N j W (t1 + delta) (t2 + delta));
    [ apply (le_Prop_to_mc 2 N HN) | exact Hneq | ].
  replace ((t1 + delta) - (t2 + delta)) with (t1 - t2) by ring.
  exact Hdiff.
Qed.

(* 同款：差频角直接给出（delta 显式相消后的形态） *)
Corollary cs5_offset_diff (N j W : nat) (delta d : R) :
  (2 <= N)%nat -> (j mod N <> 0)%nat ->
  (Cnorm (PrimeEmbedding.Csum
      (fun k => rot_atom (2 * PI * INR j / INR N + delta) k
                 *c Cconj (rot_atom delta k)) W)
    <= INR N / (2 * INR (Nat.min (j mod N) (N - j mod N))))%R.
Proof.
  intros HN Hneq.
  apply (pair_dirichlet N j W (2 * PI * INR j / INR N + delta) delta);
    [ apply (le_Prop_to_mc 2 N HN) | exact Hneq | ].
  replace ((2 * PI * INR j / INR N + delta) - delta)
    with (2 * PI * INR j / INR N) by ring.
  reflexivity.
Qed.

(* ---------- CS5b：黄金比护城河（命名系实例化） ---------- *)

Corollary cs5_golden_moat (d : nat) (m : Z) : (1 <= d)%nat ->
  ((/ (3 * INR d) <= Rabs (INR d * phi_gold - IZR m)))%R.
Proof. intros Hd. apply golden_near_collision_gold. exact Hd. Qed.

(* ---------- CS5c：偏移真离开网格（★offset 语义非空） ---------- *)

Theorem cs5_gold_not_grid (m : Z) : (phi_gold <> IZR m)%R.
Proof.
  intro Heq.
  pose proof (golden_near_collision_gold 1 m (le_n 1)) as H.
  replace (INR 1) with 1%R in H by reflexivity.
  rewrite Heq in H. rewrite Rmult_1_l in H.
  replace (IZR m - IZR m) with 0%R in H by ring.
  rewrite Rabs_R0 in H.
  lra.
Qed.

End CSFive.

Print Assumptions CSFive.cs5_offset_pair.
Print Assumptions CSFive.cs5_offset_diff.
Print Assumptions CSFive.cs5_golden_moat.
Print Assumptions CSFive.cs5_gold_not_grid.
