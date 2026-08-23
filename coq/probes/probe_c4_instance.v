(* ============================================================
   A2：C=4 精确相干 + 3 原子稀疏唯一恢复实例（z 工作区）
   任务源：非平凡定理生成方案-压缩感知无条件基深层支撑-20260823.md §F2

   数学内容： C=4 阶梯 [3,13,53,213] 的逐对相干上界（PSA_framework 的
   pair_3_13/pair_3_53/pair_3_213/pair_13_53/pair_13_213/pair_53_213 已有，
   全部 ≤ 11289/33920 < 1/3）⟹ 实例化 sparse_uniquenessM（M=2，3 原子唯一恢复）。

   A2 组装（经典 R 轨道，探针）：
     PB0. re_Csum / Rabs_re_le_Cnorm / ipW_psi_le_Csum（ipW ↔ pair_* 对接）
     PB1. c4_ip_*（六对 |⟨ψ_a,ψ_b⟩_W| ≤ 有理常数）
     PB2. c4_coherence_3（3 原子 [3,13,53] 两两相干 ≤ 11289/33920）
     PB3. C4_sparse_uniqueness_3（sparse_uniquenessM 实例，主定理）

   依赖： probe_incoherence（sparse_uniquenessM/ipW/comboM）+ PSA_framework
   （pair_*/psi_unit_norm/psi，全局引理）。
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
Require Import PSA_framework.
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
Import InstanceCertificate.

Open Scope R_scope.
Open Scope complex_scope.
Open Scope nat_scope.

(* ============ PB0：ipW（实和，W+1 项）↔ Csum（复和，N 项）对接 ============
   Csum f N = Σ_{k<N} f k（N 项，ca_zeta_scaffold）；sum_f_R0 f W = Σ_{k≤W} f k
   （W+1 项）。故 ipW W = re (Csum f (S W))。 *)

(* re 求和线性：re (Csum f (S W)) = Σ_{k≤W} re (f k) *)
Lemma re_Csum (f : nat -> Complex) (W : nat) :
  re (Csum f (S W)) = sum_f_R0 (fun k => re (f k)) W.
Proof.
  induction W as [| W IH]; simpl.
  - (* W=0：Csum f 1 = Cadd C0 (f 0)（前向），re (Cadd C0 (f 0)) = re (f 0) *)
    change (re (Cadd (Csum f 0) (f 0)) = re (f 0)).
    rewrite Cadd_0_l. reflexivity.
  - (* step：Csum f (S (S W)) = Cadd (Csum f (S W)) (f (S W))（前向） *)
    change (re (Cadd (Csum f (S W)) (f (S W)))
            = sum_f_R0 (fun k => re (f k)) (S W)).
    rewrite re_Cadd.
    rewrite IH.
    simpl. ring.
Qed.

(* |re z| ≤ Cnorm z（复模的实部上界） *)
Lemma Rabs_re_le_Cnorm (z : Complex) : (Rabs (re z) <= Cnorm z)%R.
Proof.
  unfold Cnorm.
  rewrite <- (sqrt_Rsqr_abs (re z)).
  apply sqrt_le_1.
  - apply Rle_0_sqr.
  - apply Cnorm_sq_ge_0.
  - unfold Cnorm_sq. unfold Rsqr.
    assert (Him : (0 <= im z * im z)%R) by apply Rle_0_sqr.
    nra.
Qed.

(* 对接：|ipW (psi a) (psi b) W| ≤ Cnorm (Σ_{k≤W} psi a·conj psi b) *)
Lemma ipW_psi_le_Csum (a b W : nat) :
  (Rabs (ipW (psi a) (psi b) W)
  <= Cnorm (Csum (fun k => psi a k *c Cconj (psi b k)) (S W)))%R.
Proof.
  unfold ipW.
  rewrite <- (re_Csum (fun k => psi a k *c Cconj (psi b k)) W).
  apply Rabs_re_le_Cnorm.
Qed.

(* ============ PB1：C=4 六对相干上界（ipW 形式） ============ *)

(* |⟨ψ_3,ψ_13⟩_W| ≤ 13/40（W ≥ 3） *)
Lemma c4_ip_3_13 (W : nat) : le 3 W ->
  (Rabs (ipW (psi 3) (psi 13) W) <= 13 / 40)%R.
Proof.
  intros HW.
  apply (Rle_trans _ (Cnorm (Csum (fun k => psi 3 k *c Cconj (psi 13 k)) (S W)))).
  - exact (ipW_psi_le_Csum 3 13 W).
  - apply pair_3_13. lia.
Qed.

(* |⟨ψ_3,ψ_53⟩_W| ≤ 53/400（W ≥ 3） *)
Lemma c4_ip_3_53 (W : nat) : le 3 W ->
  (Rabs (ipW (psi 3) (psi 53) W) <= 53 / 400)%R.
Proof.
  intros HW.
  apply (Rle_trans _ (Cnorm (Csum (fun k => psi 3 k *c Cconj (psi 53 k)) (S W)))).
  - exact (ipW_psi_le_Csum 3 53 W).
  - apply pair_3_53. lia.
Qed.

(* |⟨ψ_3,ψ_213⟩_W| ≤ 213/3500（W ≥ 3） *)
Lemma c4_ip_3_213 (W : nat) : le 3 W ->
  (Rabs (ipW (psi 3) (psi 213) W) <= 213 / 3500)%R.
Proof.
  intros HW.
  apply (Rle_trans _ (Cnorm (Csum (fun k => psi 3 k *c Cconj (psi 213 k)) (S W)))).
  - exact (ipW_psi_le_Csum 3 213 W).
  - apply pair_3_213. lia.
Qed.

(* |⟨ψ_13,ψ_53⟩_W| ≤ 689/2080（W ≥ 13） *)
Lemma c4_ip_13_53 (W : nat) : le 13 W ->
  (Rabs (ipW (psi 13) (psi 53) W) <= 689 / 2080)%R.
Proof.
  intros HW.
  apply (Rle_trans _ (Cnorm (Csum (fun k => psi 13 k *c Cconj (psi 53 k)) (S W)))).
  - exact (ipW_psi_le_Csum 13 53 W).
  - apply pair_13_53. lia.
Qed.

(* |⟨ψ_13,ψ_213⟩_W| ≤ 2769/20800（W ≥ 13） *)
Lemma c4_ip_13_213 (W : nat) : le 13 W ->
  (Rabs (ipW (psi 13) (psi 213) W) <= 2769 / 20800)%R.
Proof.
  intros HW.
  apply (Rle_trans _ (Cnorm (Csum (fun k => psi 13 k *c Cconj (psi 213 k)) (S W)))).
  - exact (ipW_psi_le_Csum 13 213 W).
  - apply pair_13_213. lia.
Qed.

(* |⟨ψ_53,ψ_213⟩_W| ≤ 11289/33920（W ≥ 53） *)
Lemma c4_ip_53_213 (W : nat) : le 53 W ->
  (Rabs (ipW (psi 53) (psi 213) W) <= 11289 / 33920)%R.
Proof.
  intros HW.
  apply (Rle_trans _ (Cnorm (Csum (fun k => psi 53 k *c Cconj (psi 213 k)) (S W)))).
  - exact (ipW_psi_le_Csum 53 213 W).
  - apply pair_53_213. lia.
Qed.

(* ============ PB2：ipW 对称 + C=4 三原子相干 ≤ 11289/33920 ============ *)

(* ipW 对称：⟨u,v⟩_W = ⟨v,u⟩_W *)
Lemma ipW_sym (u v : nat -> Complex) (W : nat) :
  ipW u v W = ipW v u W.
Proof.
  unfold ipW.
  apply sum_f_R0_ext.
  intro k. apply inner_sym.
Qed.

(* C=4 前 3 原子 [3,13,53]（索引 0,1,2） *)
Definition c4v3 : nat -> nat :=
  fun j => match j with 0 => 3 | 1 => 13 | _ => 53 end.

(* 三原子两两相干 ≤ 11289/33920（W ≥ 53；11289/33920 = (53,213) 对的界，全局最大） *)
Lemma c4_coherence_3 (W : nat) : le 53 W ->
  forall i j, i <= 2 -> j <= 2 -> i <> j ->
    (Rabs (ipW (psi (c4v3 i)) (psi (c4v3 j)) W) <= 11289 / 33920)%R.
Proof.
  intros HW i j Hi Hj Hne.
  move: Hi => /leP Hi. move: Hj => /leP Hj.
  destruct i as [|[|[|i]]].
  - (* i = 0（ψ_3） *)
    destruct j as [|[|[|j]]];
      try (exfalso; lia); try (exfalso; apply Hne; reflexivity).
    + (* j=1：|⟨ψ_3,ψ_13⟩| ≤ 13/40 ≤ 11289/33920 *)
      apply (Rle_trans _ (13 / 40)).
      * apply c4_ip_3_13. lia.
      * lra.
    + (* j=2：|⟨ψ_3,ψ_53⟩| ≤ 53/400 ≤ 11289/33920 *)
      apply (Rle_trans _ (53 / 400)).
      * apply c4_ip_3_53. lia.
      * lra.
  - (* i = 1（ψ_13） *)
    destruct j as [|[|[|j]]];
      try (exfalso; lia); try (exfalso; apply Hne; reflexivity).
    + (* j=0：|⟨ψ_13,ψ_3⟩| = |⟨ψ_3,ψ_13⟩| ≤ 13/40 *)
      simpl c4v3. rewrite (ipW_sym (psi 13) (psi 3) W).
      apply (Rle_trans _ (13 / 40)).
      * apply c4_ip_3_13. lia.
      * lra.
    + (* j=2：|⟨ψ_13,ψ_53⟩| ≤ 689/2080 ≤ 11289/33920 *)
      apply (Rle_trans _ (689 / 2080)).
      * apply c4_ip_13_53. lia.
      * lra.
  - (* i = 2（ψ_53） *)
    destruct j as [|[|[|j]]];
      try (exfalso; lia); try (exfalso; apply Hne; reflexivity).
    + (* j=0：|⟨ψ_53,ψ_3⟩| = |⟨ψ_3,ψ_53⟩| ≤ 53/400 *)
      simpl c4v3. rewrite (ipW_sym (psi 53) (psi 3) W).
      apply (Rle_trans _ (53 / 400)).
      * apply c4_ip_3_53. lia.
      * lra.
    + (* j=1：|⟨ψ_53,ψ_13⟩| = |⟨ψ_13,ψ_53⟩| ≤ 689/2080 *)
      simpl c4v3. rewrite (ipW_sym (psi 53) (psi 13) W).
      apply (Rle_trans _ (689 / 2080)).
      * apply c4_ip_13_53. lia.
      * lra.
  - exfalso. lia.
Qed.

(* ============ PB3：C4_sparse_uniqueness_3（A2 主定理） ============ *)

(* 0 ≤ 11289/33920 且 11289/33920 · 3 < 1（33867 < 33920） *)
Lemma c4_mu_pos : (0 <= 11289 / 33920)%R.
Proof. lra. Qed.

Lemma c4_mu_lt_third : (11289 / 33920 * INR 3 < 1)%R.
Proof. simpl. lra. Qed.

(* A2 主定理：C=4 阶梯前 3 原子 [3,13,53] 稀疏唯一恢复
   （窗口 W ≥ 53，μ := 11289/33920 < 1/3 ⟹ μ·3 < 1，sparse_uniquenessM M=2 实例） *)
Theorem C4_sparse_uniqueness_3 (c : nat -> R) (W : nat) :
  le 53 W ->
  (forall k, (k <= W)%nat -> (comboM 3 c (fun j => psi (c4v3 j)) k = C0)%C) ->
  forall j, j <= 2 -> c j = 0%R.
Proof.
  intros HW Hzero j Hj.
  apply (sparse_uniquenessM 2 c (fun j => psi (c4v3 j)) W (11289 / 33920)).
  - exact c4_mu_pos.
  - (* 单位范数：∀j≤2，l2_norm_sq (psi (c4v3 j)) W = 1（psi_unit_norm，3/13/53 ≤ W） *)
    intros j0 Hj0.
    apply (psi_unit_norm (c4v3 j0) W).
    + destruct j0 as [|[|[|j0]]]; simpl; lia.
    + destruct j0 as [|[|[|j0]]]; simpl; lia.
  - (* 两两相干 ≤ 11289/33920（c4_coherence_3） *)
    exact (c4_coherence_3 W HW).
  - exact c4_mu_lt_third.
  - (* 零组合（用户前提） *)
    intros k Hk. exact (Hzero k Hk).
  - exact Hj.
Qed.
