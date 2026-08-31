(* ============================================================
   G-10 [0,1] 区间点的构造性代数与 noisy-OR 组合证书：probe_itv_noisyor_cr.v
   （z 区构造性轨道，2026-08-31——消融上游 mathcomp.algebra.interval_inference
   Test1/Test2 elaboration 桩（Goal/Abort）后的非平凡实现承接件）

   背景：上游 Test1/Test2 的四个 Goal/Abort 桩意图演示 %:i01/%:itv 的区间推断
   装配（端点、[-1,0] 负元、补元 1−x、积 x·y 是否落入 [0,1]），其中两条命题
   数学为假不可证，已整节移除（防再合并引入）。本模块以纯 Q 层把其中可实现
   的真实主题非平凡化：
     接口化（Set 层）：iq := { p : Q & iq_ok p = true }——值 + 可判定成员证据
     核心定理 1 补元闭包：p ∈ [0,1] ⟹ 1−p ∈ [0,1]（bool 证据保留）
     核心定理 2 积闭包：  p,q ∈ [0,1] ⟹ p·q ∈ [0,1]
     核心定理 3 noisy-OR 闭包：s(p,q) = 1−(1−p)(1−q) ∈ [0,1]
     核心定理 4 单调性（非平凡核）：p ≤ p' ⟹ s(p,q) ≤ s(p',q)
       （补元反单调 × 正因子乘积单调 × 线性收口——三段链）
     核心定理 5 单位律：s(p,0) = p（上游 s_of_p0 的构造性孪生）
     最终定理（sigT，Set 层可提取）：组合证书——所得 s 携带 bool 闭包证据
        ∧ 与输入值的组合式 bool 相等，全程可运行判定

   纪律（承 probe_z_frame_check.v / probe_g9_pairfrac_cr.v）：
     - 纯构造性：零 Reals、零经典、零 Admitted、零自定义公理；纯 nat/bool/Q
     - Set 层数据 + sigT 最终定理；判定全 bool（Qle_bool/Qeq_bool 可提取运行）
       ——证明分量 Prop（信息无关，同 CS-15/G-9 口径）
     - iq_ 前缀防撞名（E144④）；E138① Notation 注册 + Close Q/Z scope
       （Q 算术一律 %Q 显式标注，E153-C）
   依赖：QArith/ZArith/Lia + micromega.Lqa（Q 线性算术 lra）。
   审计：Print Assumptions 尾部。提取：itv_noisyor_cr.ml。
   ============================================================ *)
Require Import Stdlib.QArith.QArith.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.micromega.Lqa.

(* E138①：Notation 注册（8 项，恢复 Stdlib nat 记号——防 mathcomp 污染） *)
Notation "a + b" := (Nat.add a b) (at level 50, left associativity) : nat_scope.
Notation "a - b" := (Nat.sub a b) (at level 50, left associativity) : nat_scope.
Notation "a * b" := (Nat.mul a b) (at level 40, left associativity) : nat_scope.
Notation "a <= b" := (Nat.le a b) (at level 70, no associativity) : nat_scope.
Notation "a < b" := (Nat.lt a b) (at level 70, no associativity) : nat_scope.
Notation "a >= b" := (Nat.le b a) (at level 70, no associativity) : nat_scope.
Notation "a > b" := (Nat.lt b a) (at level 70, no associativity) : nat_scope.

Close Scope Q_scope.
Close Scope Z_scope.

(* ============ R0：Set 层接口（值 + 可判定成员证据） ============ *)

Definition iq_ok (p : Q) : bool := (Qle_bool 0 p) && (Qle_bool p 1)%Q.
Definition iq := { p : Q & iq_ok p = true }.
Definition iq_val (p : iq) : Q := (projT1 p).

(* bool 判定与 Q 序的互桥（Qle_bool_iff 两侧具名，免 side goal 顺序依赖） *)
Lemma iq_le_of_bool : forall p q : Q, Qle_bool p q = true -> (p <= q)%Q.
Proof. intros p q H. apply (proj1 (Qle_bool_iff p q)). exact H. Qed.

Lemma iq_bool_of_le : forall p q : Q, (p <= q)%Q -> Qle_bool p q = true.
Proof. intros p q H. apply (proj2 (Qle_bool_iff p q)). exact H. Qed.

(* 构造子：端点 0 / 1（字面量钉值走 vm_compute——E190/E180 字面量墙） *)
Lemma iq_ok_zero : iq_ok 0 = true.
Proof. unfold iq_ok. vm_compute. reflexivity. Qed.

Lemma iq_ok_one : iq_ok 1 = true.
Proof. unfold iq_ok. vm_compute. reflexivity. Qed.

Definition iq_zero : iq := existT _ (0%Q) iq_ok_zero.
Definition iq_one : iq := existT _ (1%Q) iq_ok_one.

(* ============ R1：核心定理 1——补元闭包（bool 证据保留） ============ *)

Lemma iq_ok_comp_val : forall p : Q, iq_ok p = true -> iq_ok (1 - p)%Q = true.
Proof.
  unfold iq_ok. intros p Hp. apply andb_true_iff in Hp as [H0 H1].
  apply andb_true_iff. split.
  - apply iq_bool_of_le.
    apply (iq_le_of_bool p 1) in H1. lra.
  - apply iq_bool_of_le.
    apply (iq_le_of_bool 0 p) in H0. lra.
Qed.

(* ============ R2：核心定理 2——积闭包 ============ *)

Lemma iq_ok_mul_val : forall p q : Q, iq_ok p = true -> iq_ok q = true ->
  iq_ok (p * q)%Q = true.
Proof.
  unfold iq_ok. intros p q Hp Hq.
  apply andb_true_iff in Hp as [Hp0 Hp1].
  apply andb_true_iff in Hq as [Hq0 Hq1].
  apply iq_le_of_bool in Hp0. apply iq_le_of_bool in Hp1.
  apply iq_le_of_bool in Hq0. apply iq_le_of_bool in Hq1.
  apply andb_true_iff. split.
  - apply iq_bool_of_le.
    (* 0 ≤ p·q：0 ≤ p 与 0 ≤ q 的乘积正性（Qmult_le_0_compat） *)
    pose proof (Qmult_le_0_compat p q Hp0 Hq0) as Hpos.
    lra.
  - apply iq_bool_of_le.
    (* p·q ≤ 1·q = q ≤ 1：Qmult_le_compat_r（不等式在前，0 ≤ q 在后）+ 单位律 *)
    pose proof (Qmult_le_compat_r p 1%Q q Hp1 Hq0) as Hb.
    rewrite Qmult_1_l in Hb. lra.
Qed.

(* ============ R3：核心定理 3——noisy-OR 闭包 ============ *)

Definition iq_nor_val (p q : Q) : Q := (1 - (1 - p) * (1 - q))%Q.

Lemma iq_ok_nor_val : forall p q : Q, iq_ok p = true -> iq_ok q = true ->
  iq_ok (iq_nor_val p q) = true.
Proof.
  unfold iq_ok, iq_nor_val. intros p q Hp Hq.
  pose proof (iq_ok_comp_val p Hp) as Hcp.   (* 0 ≤ 1−p ≤ 1 *)
  pose proof (iq_ok_comp_val q Hq) as Hcq.   (* 0 ≤ 1−q ≤ 1 *)
  unfold iq_ok in Hcp, Hcq.
  apply andb_true_iff in Hcp as [Hcp0 Hcp1].
  apply andb_true_iff in Hcq as [Hcq0 Hcq1].
  apply iq_le_of_bool in Hcp0. apply iq_le_of_bool in Hcp1.
  apply iq_le_of_bool in Hcq0. apply iq_le_of_bool in Hcq1.
  apply andb_true_iff. split.
  - (* 0 ≤ 1−(1−p)(1−q) ⟸ (1−p)(1−q) ≥ 0 域内线性 *)
    apply iq_bool_of_le.
    assert (Hprod : (0 <= (1 - p) * (1 - q))%Q).
    { exact (Qmult_le_0_compat (1 - p)%Q (1 - q)%Q Hcp0 Hcq0). }
    assert (Hle1 : ((1 - p) * (1 - q) <= 1)%Q).
    { pose proof (Qmult_le_compat_r (1 - p)%Q 1%Q (1 - q)%Q Hcp1 Hcq0) as H1.
      rewrite Qmult_1_l in H1. lra. }
    lra.
  - (* s ≤ 1 即 1−M ≤ 1 ⟺ M ≥ 0——需正性（非上界） *)
    apply iq_bool_of_le.
    assert (Hprod : (0 <= (1 - p) * (1 - q))%Q).
    { exact (Qmult_le_0_compat (1 - p)%Q (1 - q)%Q Hcp0 Hcq0). }
    lra.
Qed.

(* ============ R4：核心定理 4（非平凡核）——noisy-OR 双变量单调 ============ *)

Lemma iq_nor_mono_l : forall p p' q : Q, iq_ok q = true ->
  (p <= p')%Q -> (iq_nor_val p q <= iq_nor_val p' q)%Q.
Proof.
  intros p p' q Hq Hle. unfold iq_nor_val.
  (* 正因子 (1−q) ≥ 0 必须来自 q ∈ [0,1]——负因子会翻转不等号（域诚实前提） *)
  assert (Hfac : (0 <= (1 - q))%Q).
  { unfold iq_ok in Hq. apply andb_true_iff in Hq as [_ Hq1].
    apply iq_le_of_bool in Hq1. lra. }
  (* 补元反单调：1−p' ≤ 1−p *)
  assert (Hcp : ((1 - p') <= (1 - p))%Q) by lra.
  pose proof (Qmult_le_compat_r (1 - p')%Q (1 - p)%Q (1 - q)%Q Hcp Hfac) as Hprod.
  lra.
Qed.

Lemma iq_nor_mono_r : forall p q q' : Q, iq_ok p = true ->
  (q <= q')%Q -> (iq_nor_val p q <= iq_nor_val p q')%Q.
Proof.
  intros p q q' Hp Hle. unfold iq_nor_val.
  assert (Hfac : (0 <= (1 - p))%Q).
  { unfold iq_ok in Hp. apply andb_true_iff in Hp as [_ Hp1].
    apply iq_le_of_bool in Hp1. lra. }
  assert (Hcp : ((1 - q') <= (1 - q))%Q) by lra.
  (* 左乘单调（stdlib 无 Qmult_le_compat_l）：_r + 断言内交换律配平 *)
  pose proof (Qmult_le_compat_r (1 - q')%Q (1 - q)%Q (1 - p)%Q Hcp Hfac) as H0.
  assert (Hprod : ((1 - p) * (1 - q') <= (1 - p) * (1 - q))%Q).
  { rewrite (Qmult_comm (1 - p)%Q (1 - q')%Q).
    rewrite (Qmult_comm (1 - p)%Q (1 - q)%Q).
    exact H0. }
  lra.
Qed.

(* bool 形（可运行判定证据） *)
Lemma iq_nor_mono_l_bool : forall p p' q : Q, iq_ok q = true ->
  Qle_bool p p' = true ->
  Qle_bool (iq_nor_val p q) (iq_nor_val p' q) = true.
Proof.
  intros p p' q Hq H. apply iq_bool_of_le. apply iq_nor_mono_l; [ exact Hq | ].
  apply (iq_le_of_bool p p'). exact H.
Qed.

(* ============ R5：核心定理 5——单位律（上游 s_of_p0 的构造性孪生） ============ *)

Lemma iq_nor_unit_r : forall p : Q, (iq_nor_val p 0 == p)%Q.
Proof.
  intros p. unfold iq_nor_val. apply Qle_antisym; lra.
Qed.

(* ============ R6：最终定理（sigT，Set 层可提取组合证书） ============ *)

Theorem iq_nor_cert (p q : iq) :
  { s : Q & iq_ok s = true
        /\ Qeq_bool s (iq_nor_val (iq_val p) (iq_val q)) = true }.
Proof.
  exists (iq_nor_val (iq_val p) (iq_val q)).
  pose proof (projT2 p) as Hp. pose proof (projT2 q) as Hq.
  split; [ | apply Qeq_bool_refl ].
  apply (iq_ok_nor_val (iq_val p) (iq_val q) Hp Hq).
Qed.

Theorem iq_nor_mono_cert (p p' q : iq) :
  Qle_bool (iq_val p) (iq_val p') = true ->
  { b : bool & Qle_bool (iq_nor_val (iq_val p) (iq_val q))
                        (iq_nor_val (iq_val p') (iq_val q)) = b }.
Proof.
  intros H. exists true.
  apply iq_nor_mono_l_bool; [ exact (projT2 q) | exact H ].
Qed.

(* ============ 审计 ============ *)
Print Assumptions iq_ok_mul_val.
Print Assumptions iq_ok_nor_val.
Print Assumptions iq_nor_mono_l_bool.
Print Assumptions iq_nor_unit_r.
Print Assumptions iq_nor_cert.
Print Assumptions iq_nor_mono_cert.

(* ============ 提取（Set 层全可执行——区间组合运行时入口） ============ *)
From Stdlib Require Import Extraction.

Extraction "itv_noisyor_cr.ml" iq_ok iq_val iq_nor_val iq_nor_cert iq_nor_mono_cert.
