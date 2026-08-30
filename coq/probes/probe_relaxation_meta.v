(* ============================================================
   CS-19 松弛链元理论：单调性与组合性（probe_relaxation_meta.v）
   （外部评审建议-05 Should-Fix #4：可判定性松弛链是本文核心方法论，
   需为该链补证——单调性（更紧的超越数界 ⟹ 更紧的有理数界）与
   组合性（各层独立收紧的兼容性），即使作为引理/附录）

   背景：反射检查器的有理证书由逐层松弛合成——
     层 A（分子上界）：Dirichlet 核分子 |sin(πNΔ)| ≤ m（理想 m = 1）
     层 B（分母下界）：sin(πΔ) ≥ sb（Jordan / π 上界改进处）
     层 C（√ 下界）：√(n1·n2) ≥ sq（floor-sqrt 层）
   合成逐对界 relax m sb sq := m·(1/(sb·sq))；行和累加后与 4/5 比较。
   本模块在抽象参数层证明该合成的元理论性质：

     M1 逐层单调：relax 对 m 单调增、对 sb / sq 单调减
        （更紧的层界 ⟹ 更紧的合成界——单调性）
     M2 组合性：三层同时收紧 ⟹ 合成界 ≤ 原界，且可分解为逐层收紧
        的传递链（各层独立收紧互不破坏——组合性）
     M3 行和提升：逐对单调 ⟹ 行和单调（sum_f_R0 上的逐点提升）
     M4 判定保持（主定理）：任一层收紧后，若旧合成界下检查器通过
        （行和 ≤ 4/5），则新合成界下仍通过——松弛链的收紧是
        「只强化不破坏」的单侧操作
     M5 形态实例化：框架反射层 pair_frac_R 恰为 relax 族的一个实例
        （m := INR(n1·n2)、sb := INR(2·(n2−n1))、sq := INR(√(n1·n2))
        的 nat floor 形态），即元理论直接覆盖现有检查器管线；
        又因 nat 分数累加（frac_add）为精确有理加法，R 层行和与
        nat 层行和在值上逐点相等，元理论对 nat 检查器逐字适用

   纪律：零 Admitted / 零自定义 Axiom；纯 R 层（与主线同公理依赖）。
   依赖：Stdlib + ca_* 六库（sum_f_R0 及其归纳引理）+ PSA_framework
   （仅 M5 的 pair_frac_R 形态实例）。
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
Open Scope nat_scope.
Open Scope R_scope.

(* ============ M1：合成界的逐层单调性 ============ *)

Definition relax (m sb sq : R) : R := m * (1 / (sb * sq)).

Lemma relax_pos_den (sb sq : R) : 0 < sb -> 0 < sq -> 0 < sb * sq.
Proof. intros Hsb Hsq. nra. Qed.

Lemma relax_den_pos_inv (sb sq : R) : 0 < sb -> 0 < sq -> 0 <= 1 / (sb * sq).
Proof.
  intros Hsb Hsq.
  apply Rlt_le. apply Rdiv_lt_0_compat.
  - apply Rlt_0_1.
  - apply relax_pos_den; assumption.
Qed.

(* M1a：分子层（上界参数）单调 *)
Lemma relax_mono_m (m1 m2 sb sq : R) :
  0 < sb -> 0 < sq -> m1 <= m2 -> relax m1 sb sq <= relax m2 sb sq.
Proof.
  intros Hsb Hsq Hm. unfold relax.
  apply Rmult_le_compat_r.
  - apply relax_den_pos_inv; assumption.
  - exact Hm.
Qed.

(* M1b：分母下界层单调（sb 越大合成界越小） *)
Lemma relax_mono_sb (m sb1 sb2 sq : R) :
  0 <= m -> 0 < sb1 -> sb1 <= sb2 -> 0 < sq ->
  relax m sb2 sq <= relax m sb1 sq.
Proof.
  intros Hm Hsb1 Hle Hsq. unfold relax.
  apply Rmult_le_compat_l.
  - exact Hm.
  - unfold Rdiv. rewrite !Rmult_1_l.
    apply Rinv_le_contravar.
    + apply relax_pos_den; assumption.
    + apply Rmult_le_compat.
      * lra.
      * lra.
      * exact Hle.
      * apply Rle_refl.
Qed.

(* M1c：√ 下界层单调（sq 越大合成界越小） *)
Lemma relax_mono_sq (m sb sq1 sq2 : R) :
  0 <= m -> 0 < sb -> 0 < sq1 -> sq1 <= sq2 ->
  relax m sb sq2 <= relax m sb sq1.
Proof.
  intros Hm Hsb Hsq1 Hle. unfold relax.
  apply Rmult_le_compat_l.
  - exact Hm.
  - unfold Rdiv. rewrite !Rmult_1_l.
    apply Rinv_le_contravar.
    + apply relax_pos_den; assumption.
    + apply Rmult_le_compat.
      * lra.
      * lra.
      * apply Rle_refl.
      * exact Hle.
Qed.

(* ============ M2：组合性（多层独立收紧的兼容性） ============ *)

Lemma relax_refine (m m1 sb sb1 sq sq1 : R) :
  0 <= m1 -> 0 < sb -> 0 < sb1 -> 0 < sq -> 0 < sq1 ->
  m1 <= m -> sb <= sb1 -> sq <= sq1 ->
  relax m1 sb1 sq1 <= relax m sb sq.
Proof.
  intros Hm1 Hsb Hsb1 Hsq Hsq1 Hm Hle_sb Hle_sq.
  eapply Rle_trans; [apply (relax_mono_sq m1 sb1 sq sq1); assumption |].
  eapply Rle_trans; [apply (relax_mono_sb m1 sb sb1 sq); assumption |].
  apply relax_mono_m; assumption.
Qed.

(* ============ M3：行和提升（逐对单调 ⟹ 行和单调） ============ *)

Definition rowR (g : nat -> nat -> R) (n i : nat) : R :=
  sum_f_R0 (fun j => if Nat.eqb i j then 0 else g i j) (Nat.pred n).

Lemma rowR_mono (g h : nat -> nat -> R) (n : nat) :
  (forall i j, i <> j -> g i j <= h i j) ->
  forall i, rowR g n i <= rowR h n i.
Proof.
  intros Hle i. unfold rowR. apply sum_f_R0_le_compat. intros j Hj.
  destruct (Nat.eqb_spec i j) as [E | E].
  - apply Rle_refl.
  - apply Hle. exact E.
Qed.

(* ============ M4：判定保持（主定理） ============ *)

Theorem checker_preserved_under_refinement (g h : nat -> nat -> R) (n : nat) :
  (forall i j, i <> j -> h i j <= g i j) ->
  (forall i : nat, (i < n)%nat -> rowR g n i <= 4 / 5) ->
  forall i : nat, (i < n)%nat -> rowR h n i <= 4 / 5.
Proof.
  intros Htight Hpass i Hi.
  eapply Rle_trans; [apply (rowR_mono h g n Htight) | apply Hpass; exact Hi].
Qed.

(* ============ M5：形态实例化（元理论覆盖现有检查器管线） ============ *)

Corollary pair_frac_relax_form (a b : nat) :
  FrameCheckInstance.pair_frac_R a b
  = relax (INR (Nat.min a b * Nat.max a b))
          (INR (2 * (Nat.max a b - Nat.min a b)))
          (INR (Nat.sqrt (Nat.min a b * Nat.max a b))).
Proof.
  unfold FrameCheckInstance.pair_frac_R, relax,
         FrameCheckInstance.pair_num, FrameCheckInstance.pair_den, Rdiv.
  rewrite Rmult_1_l.
  rewrite <- (mult_INR (2 * (Nat.max a b - Nat.min a b))
                       (Nat.sqrt (Nat.min a b * Nat.max a b))).
  reflexivity.
Qed.

(* ============ 审计 ============ *)
Print Assumptions checker_preserved_under_refinement.
Print Assumptions pair_frac_relax_form.
