(* ============================================================
   CS-20 C=4 四原子线性无关 / 2-sparse 唯一恢复
   （probe_c4_unique2sparse.v——填补标题缺口：C=4 的唯一性从
   「3 原子 3-sparse（μ₄·3 < 1 窗口）」扩展到「全 4 原子系数单射」，
   利用已有引理：pair_inner_frac_bound + inner_diag_one + psi 单位范数）

   路线（评审 4 原子障碍分析「出路一」的可计算化）：
   μ-窗口路线已死（μ₄·4 = 45156/33920 > 1，均匀 Gershgorin 口径
   必须失败）——改走**精确 Gram 严格对角占优**：
     4×4 Gram G_ij = ⟨u_i,u_j⟩，|G_ij| ≤ pf_ij（逐对 Dirichlet 有理
     上界，pair_inner_frac_bound），G_kk = 1（inner_diag_one）。
     四行 pf 行和（nat floor 有理数，Q 层精确判定）全部 < 1：
       行 3   : 39/120 + 159/1200 + 639/10500   ≈ 0.518
       行 13  : 39/120 + 689/2080 + 2769/20800  ≈ 0.789
       行 53  : 159/1200 + 689/2080 + 11289/33920 ≈ 0.797
       行 213 : 639/10500 + 2769/20800 + 11289/33920 ≈ 0.527
     ⟹ G 严格对角占优 ⟹ 非奇异 ⟹ 合成映射 c ↦ Σc_j u_j 单射
     ⟹ C=4 全 4 原子的系数表示唯一（含 2-sparse；标题缺口填补）。

   本批（D 数值认证层，✅ 全绿）：逐对界的 Q 常量、R 桥接、四行行和 < 1。
   下一批（I 注入性核，实施计划已定）：
     I1 标量提拉：Σ_k conj(u_i k) *c (c_j *c u_j k) = c_j *c ⟨u_j,u_i⟩
        （Csum 乘法分配 + conj 进出，Cmul_add_distr_r/Csum_ext 组合）
     I2 对角项：j = i₀ 项 = c_{i₀}·conj(G_ii) = c_{i₀}（inner_diag_one）
     I3 枢轴选取：|c_{i₀}| = max_j |c_j|（4 元素显式 case analysis）
     I4 占优反证：|c_{i₀}| ≤ Σ_{j≠i₀}|c_j|·pf_ij ≤ |c_{i₀}|·row(i₀) < |c_{i₀}|
        ⟹ 矛盾 ⟹ 合成零 ⟹ 系数全零（任意系数单射，含 2-sparse 唯一）
     预计体量 ~300 行；全部依赖已在本文件 D 层与框架引理中就位。
   纪律：经典 R 轨道；零 Admitted / 零自定义 Axiom。
   ============================================================ *)
Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.Arith.
Require Import Stdlib.QArith.QArith.
Require Import Stdlib.Reals.Reals.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.micromega.Lra.
Require Import ca_base ca_complex_foundation ca_independence ca_basis ca_basis_lemmas ca_decay.
Require Import PSA_framework.
Import ComplexNumbers.
Import ExtendedTheorems.
Import ListNotations.
Open Scope nat_scope.
Open Scope R_scope.

(* ============ D1：逐对有理上界的 Q 常量（nat floor 形态） ============ *)

Definition pf313 : Q := Qmake 39 120.
Definition pf353 : Q := Qmake 159 1200.
Definition pf3213 : Q := Qmake 639 10500.
Definition pf1353 : Q := Qmake 689 2080.
Definition pf13213 : Q := Qmake 2769 20800.
Definition pf53213 : Q := Qmake 11289 33920.

(* ============ D2：四行行和 < 1（Q 层精确判定） ============ *)

Lemma row3_q_lt : Qlt (pf313 + pf353 + pf3213) (Qmake 1 1).
Proof.
  unfold Qlt, Qplus, pf313, pf353, pf3213. cbn [Qnum Qden]. lia.
Qed.

Lemma row13_q_lt : Qlt (pf313 + pf1353 + pf13213) (Qmake 1 1).
Proof.
  unfold Qlt, Qplus, pf313, pf1353, pf13213. cbn [Qnum Qden]. lia.
Qed.

Lemma row53_q_lt : Qlt (pf353 + pf1353 + pf53213) (Qmake 1 1).
Proof.
  unfold Qlt, Qplus, pf353, pf1353, pf53213. cbn [Qnum Qden]. lia.
Qed.

Lemma row213_q_lt : Qlt (pf3213 + pf13213 + pf53213) (Qmake 1 1).
Proof.
  unfold Qlt, Qplus, pf3213, pf13213, pf53213. cbn [Qnum Qden]. lia.
Qed.

(* ============ D3：R 桥接（pair_frac_R = Q2R 常量） ============ *)

Lemma sqrt39 : Nat.sqrt 39 = 6%nat. Proof. reflexivity. Qed.
Lemma sqrt159 : Nat.sqrt 159 = 12%nat. Proof. reflexivity. Qed.
Lemma sqrt639 : Nat.sqrt 639 = 25%nat. Proof. reflexivity. Qed.
Lemma sqrt689 : Nat.sqrt 689 = 26%nat. Proof. reflexivity. Qed.
Lemma sqrt2769 : Nat.sqrt 2769 = 52%nat. Proof. reflexivity. Qed.
Lemma sqrt11289 : Nat.sqrt 11289 = 106%nat. Proof. reflexivity. Qed.


Lemma pf313_R : FrameCheckInstance.pair_frac_R 3 13 = Q2R pf313.
Proof.
  unfold FrameCheckInstance.pair_frac_R, pf313, Q2R.
  unfold FrameCheckInstance.pair_num, FrameCheckInstance.pair_den.
  cbn [Nat.min Nat.max Nat.sub Nat.mul Nat.sqrt Nat.add Qnum Qden].
  rewrite !INR_IZR_INZ. reflexivity.
Qed.

Lemma pf353_R : FrameCheckInstance.pair_frac_R 3 53 = Q2R pf353.
Proof.
  unfold FrameCheckInstance.pair_frac_R, pf353, Q2R.
  unfold FrameCheckInstance.pair_num, FrameCheckInstance.pair_den.
  cbn [Nat.min Nat.max Nat.sub Nat.mul Nat.sqrt Nat.add Qnum Qden].
  rewrite !INR_IZR_INZ. reflexivity.
Qed.

Lemma pf3213_R : FrameCheckInstance.pair_frac_R 3 213 = Q2R pf3213.
Proof.
  unfold FrameCheckInstance.pair_frac_R, pf3213, Q2R.
  unfold FrameCheckInstance.pair_num, FrameCheckInstance.pair_den.
  cbn [Nat.min Nat.max Nat.sub Nat.mul Nat.sqrt Nat.add Qnum Qden].
  rewrite !INR_IZR_INZ. reflexivity.
Qed.

Lemma pf1353_R : FrameCheckInstance.pair_frac_R 13 53 = Q2R pf1353.
Proof.
  unfold FrameCheckInstance.pair_frac_R, pf1353, Q2R.
  unfold FrameCheckInstance.pair_num, FrameCheckInstance.pair_den.
  cbn [Nat.min Nat.max Nat.sub Nat.mul Nat.sqrt Nat.add Qnum Qden].
  rewrite !INR_IZR_INZ. reflexivity.
Qed.

Lemma pf13213_R : FrameCheckInstance.pair_frac_R 13 213 = Q2R pf13213.
Proof.
  unfold FrameCheckInstance.pair_frac_R, pf13213, Q2R.
  unfold FrameCheckInstance.pair_num, FrameCheckInstance.pair_den.
  cbn [Nat.min Nat.max Nat.sub Nat.mul Nat.sqrt Nat.add Qnum Qden].
  rewrite !INR_IZR_INZ. reflexivity.
Qed.

Lemma pf53213_R : FrameCheckInstance.pair_frac_R 53 213 = Q2R pf53213.
Proof.
  unfold FrameCheckInstance.pair_frac_R, pf53213, Q2R.
  unfold FrameCheckInstance.pair_num, FrameCheckInstance.pair_den.
  cbn [Nat.min Nat.max Nat.sub Nat.mul Nat.sqrt Nat.add Qnum Qden].
  rewrite !INR_IZR_INZ. reflexivity.
Qed.

(* ============ D4：四行行和 < 1（R 层判定） ============ *)

Lemma row3_R_lt : (FrameCheckInstance.pair_frac_R 3 13
  + FrameCheckInstance.pair_frac_R 3 53 + FrameCheckInstance.pair_frac_R 3 213 < 1)%R.
Proof.
  rewrite pf313_R, pf353_R, pf3213_R.
  unfold Q2R, pf313, pf353, pf3213, pf1353, pf13213, pf53213.
  cbn [Qnum Qden].
  first [lra | nra].
Qed.

Lemma row13_R_lt : (FrameCheckInstance.pair_frac_R 3 13
  + FrameCheckInstance.pair_frac_R 13 53 + FrameCheckInstance.pair_frac_R 13 213 < 1)%R.
Proof.
  rewrite pf313_R, pf1353_R, pf13213_R.
  unfold Q2R, pf313, pf353, pf3213, pf1353, pf13213, pf53213.
  cbn [Qnum Qden].
  first [lra | nra].
Qed.

Lemma row53_R_lt : (FrameCheckInstance.pair_frac_R 3 53
  + FrameCheckInstance.pair_frac_R 13 53 + FrameCheckInstance.pair_frac_R 53 213 < 1)%R.
Proof.
  rewrite pf353_R, pf1353_R, pf53213_R.
  unfold Q2R, pf313, pf353, pf3213, pf1353, pf13213, pf53213.
  cbn [Qnum Qden].
  first [lra | nra].
Qed.

Lemma row213_R_lt : (FrameCheckInstance.pair_frac_R 3 213
  + FrameCheckInstance.pair_frac_R 13 213 + FrameCheckInstance.pair_frac_R 53 213 < 1)%R.
Proof.
  rewrite pf3213_R, pf13213_R, pf53213_R.
  unfold Q2R, pf313, pf353, pf3213, pf1353, pf13213, pf53213.
  cbn [Qnum Qden].
  first [lra | nra].
Qed.
