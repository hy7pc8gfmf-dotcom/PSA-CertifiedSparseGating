(* ============================================================
   CS-15 构造性四原子分层证书：probe_c4_four_atom_cr.v
   （z 区构造性轨道，2026-08-30，M2 venue 对齐扩展——评审 4.1/主题四
   "C=4 第 4 原子 213 未覆盖"的正面回应）

   目标：把"3 原子唯一、第 4 原子未覆盖"转化为分层正面贡献：
     层 1（全族 4 原子 [3,13,53,213]）：双侧能量稳定
        |‖Σ_{j≤3} c_j·u_j‖² − Σ c_j²| ≤ μ₄·4·Σ c_j²
        （CRrip_bound_k M=3 实例化——能量稳定不要求 μ(M+1)<1）
     层 2（Q 层窗口判定，可计算）：
        μ₄·4 > 1 —— 全族唯一性窗口**关闭**（精确障碍刻画）
        μ₄·3 < 1 —— 3 原子子族 [3,13,53] 唯一性窗口**开启**
     —— 同一常数 μ₄ = 11289/33920（六对公共相干上界，主线
        pair_53_213 / c4_coherence_3 背书）的两个方向判定。

   纪律（承 probe_taugrid_cr.v / probe_recovery_cr.v）：
     - 纯构造性：零经典实数（不用 Stdlib.Reals）、零 Admitted、
       零自定义公理；只用抽象接口 {R : ConstructiveReals}
     - Set 层 CRcarrier 组合；Prop 层 CRle（上界证书无信息内容故
       留 Prop，同 taugrid C-TA3 口径）；Q 层窗口判定（Prop 层 Z，
       lia 收口——序判定下放 Q 层）
     - Q 分母 Pos.of_succ_nat；zpos_of_succ + cbn [Qnum QDen] 定向
       归约（禁 simpl）
     - 可提取：μ₄ 常数与 CR 组合（Set 层对象）
   依赖：ca_rip_cr（CRrip_bound_k/CRcombo/CRnorm_sq/CRsum/CRip/INR/
         CR0_le_INR，均 Closed）。
   审计：Print Assumptions 尾部。
   提取：c4_four_atom_cr.ml。
   ============================================================ *)
Require Import ConstructiveReals.
From Stdlib Require Import ConstructiveRealsMorphisms.
From Stdlib Require Import ConstructiveAbs.
From Stdlib Require Import ConstructiveSum.
Require Import Stdlib.QArith.QArith.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.micromega.Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat seq eqtype div prime.
Require Import ca_rip_cr.

Local Open Scope ConstructiveReals.

(* E138①：Notation 注册（8 项，恢复 Stdlib nat 记号——防 mathcomp 污染，
   合并版双环境兼容硬规则 9） *)
Notation "a + b" := (Nat.add a b) (at level 50, left associativity) : nat_scope.
Notation "a - b" := (Nat.sub a b) (at level 50, left associativity) : nat_scope.
Notation "a * b" := (Nat.mul a b) (at level 40, left associativity) : nat_scope.
Notation "a <= b" := (Nat.le a b) (at level 70, no associativity) : nat_scope.
Notation "a < b" := (Nat.lt a b) (at level 70, no associativity) : nat_scope.
Notation "a >= b" := (Nat.le b a) (at level 70, no associativity) : nat_scope.
Notation "a > b" := (Nat.lt b a) (at level 70, no associativity) : nat_scope.

(* Q 分母桥（定义性——Z.of_nat (S n) ≡ Zpos (Pos.of_succ_nat n)） *)
Lemma zpos_of_succ_c4 (n : nat) :
  Z.pos (Pos.of_succ_nat n) = Z.of_nat (S n).
Proof. destruct n; reflexivity. Qed.

(* 字面量钉值（cbn 对字面量 den 会 iota 展开 of_succ_nat 为 of_num_uint，
   zpos_of_succ 的通用形态无法归约 lia——故用 reflexivity 钉值引理） *)
Lemma zpos_33919 : Z.pos (Pos.of_succ_nat 33919) = 33920%Z.
Proof. reflexivity. Qed.

(* μ₄：C=4 六对公共相干的有理上界 11289/33920
   （主线 pair_53_213 与 c4_coherence_3 同值背书） *)
Definition mu_c4 : Q := Qmake 11289 (Pos.of_succ_nat 33919).

Section C4FourAtomCR.

Context {R : ConstructiveReals}.
Add Ring CR_ring : (CRisRing R).

(* 四原子注入：u 0 ↔ ψ_3，u 1 ↔ ψ_13，u 2 ↔ ψ_53，u 3 ↔ ψ_213
   （抽象梯子——CR 构造性 cos/复指数由 M2E 扩展 plug-in，接口不变） *)
Variable u : nat -> @CRComplex R.

Hypothesis Hu_unit : forall j, le j 3 -> CReq R (CRnorm_sq (u j)) (CR_of_Q R (Qmake 1 1)).
Hypothesis Hu_coh : forall i j, le i 3 -> le j 3 -> i <> j ->
  CRle R (CRabs R (CRip (u i) (u j))) (CR_of_Q R mu_c4).

(* ---------- C4-0 μ₄ ≥ 0 ---------- *)

Lemma c4_mu_c4_nonneg :
  CRle R (CR_of_Q R (Qmake 0 1)) (CR_of_Q R mu_c4).
Proof.
  apply CR_of_Q_le.
  unfold Qle, mu_c4. cbn [Qnum Qden].
  rewrite zpos_33919. lia.
Qed.

(* ---------- C4-1 ★ 核心：四原子双侧能量稳定 ---------- *)

Theorem c4_four_atom_energy_stability :
  forall c : nat -> CRcarrier R,
  CRle R (CRabs R (CRminus R (CRnorm_sq (CRcombo 3 c u))
                             (CRsum (fun j => c j * c j) 3)))
         ((CR_of_Q R mu_c4 * INR 4)%ConstructiveReals
          * CRsum (fun j => c j * c j) 3).
Proof.
  intros c.
  exact (CRrip_bound_k (R := R) 3 c u (CR_of_Q R mu_c4)
                       c4_mu_c4_nonneg Hu_unit Hu_coh).
Qed.

(* ---------- C4-2 Q 层窗口判定（可计算） ---------- *)

(* 全族（4 原子）唯一性窗口**关闭**：μ₄·4 = 45156/33920 > 1 *)
Lemma c4_mu4_times4_gt_one : Qlt (Qmake 1 1) (mu_c4 * Qmake 4 1).
Proof.
  unfold Qlt, Qmult, mu_c4. cbn [Qnum Qden].
  rewrite zpos_33919. lia.
Qed.

(* 子族（3 原子 [3,13,53]）唯一性窗口**开启**：μ₄·3 = 33867/33920 < 1 *)
Lemma c4_mu4_times3_lt_one : Qlt (mu_c4 * Qmake 3 1) (Qmake 1 1).
Proof.
  unfold Qlt, Qmult, mu_c4. cbn [Qnum Qden].
  rewrite zpos_33919. lia.
Qed.

(* ---------- C4-3 ★★ 最终合成：分层证书 ---------- *)

Theorem c4_four_atom_layered_certificate :
  (forall c : nat -> CRcarrier R,
     CRle R (CRabs R (CRminus R (CRnorm_sq (CRcombo 3 c u))
                                (CRsum (fun j => c j * c j) 3)))
            ((CR_of_Q R mu_c4 * INR 4)%ConstructiveReals
             * CRsum (fun j => c j * c j) 3))
  /\ Qlt (Qmake 1 1) (mu_c4 * Qmake 4 1)
  /\ Qlt (mu_c4 * Qmake 3 1) (Qmake 1 1).
Proof.
  split; [exact c4_four_atom_energy_stability
         | split; [exact c4_mu4_times4_gt_one | exact c4_mu4_times3_lt_one]].
Qed.

End C4FourAtomCR.

(* ---------- 审计 ---------- *)
Print Assumptions c4_mu_c4_nonneg.
Print Assumptions c4_four_atom_energy_stability.
Print Assumptions c4_mu4_times4_gt_one.
Print Assumptions c4_mu4_times3_lt_one.
Print Assumptions c4_four_atom_layered_certificate.

(* ---------- 提取（Set 层可执行对象 + 柯西实例具象化） ---------- *)
From Stdlib Require Import Extraction.
From Stdlib Require Import ConstructiveRcomplete.

Definition c4_ladder_zero :
  nat -> @CRComplex CRealConstructive := fun _ => CRzero.

(* eta 展开：常量包装会带弱类型（'_weak1），函数形式可泛化 *)
Definition c4_mu_cauchy : Q -> @CRcarrier CRealConstructive :=
  fun _ => @CR_of_Q CRealConstructive mu_c4.
Definition c4_combo_cauchy :
  (nat -> @CRcarrier CRealConstructive) -> @CRComplex CRealConstructive :=
  fun c => @CRcombo CRealConstructive 3 c c4_ladder_zero.
Definition c4_norm_sq_cauchy :
  (nat -> @CRcarrier CRealConstructive) -> @CRcarrier CRealConstructive :=
  fun c => @CRnorm_sq CRealConstructive (c4_combo_cauchy c).
Definition c4_mu4_window : Z * positive :=
  (Qnum (mu_c4 * Qmake 4 1), Qden (mu_c4 * Qmake 4 1)).

Extraction "c4_four_atom_cr.ml" c4_mu_cauchy c4_combo_cauchy
  c4_norm_sq_cauchy c4_mu4_window.

