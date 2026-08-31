(* ============================================================
   G-9 有理逐对界渐近闭合形式（构造性轨道）：probe_g9_pairfrac_cr.v
   （z 区构造性轨道，2026-08-31——论文 A §5 松弛链
   "n₁n₂/(2(n₂−n₁)⌊√(n₁n₂)⌋) → √C/(2(C−1))（C=4 时 1/3）"
   的机器检查补强，回应 Coq 专家评审第 6 条）

   目标：把松弛链渐近代价闭合式从纸面推导升级为定理：
     层 1（完全平方 C=c²，精确闭合——论文 C=4 实例的推广）：
        pair_frac(a, c²·a) = c / (2·(c²−1))
        （√C/(2(C−1)) 的有理精确形，C=4 → 1/3）
     层 2（一般 C，双带有理夹逼——s = ⌊√C⌋）：
        C/(2(C−1)(s+1)) ≤ pair_frac(a, C·a) ≤ C/(2(C−1)·s)
        ——比纸面的 √C/(2(C−1)) 更强：全有理、可计算、两侧显式
     最终定理（sigT 可提取）：闭合式证书——计算所得代价 q 同时
        等于 pair_frac 实值与闭合式 c/(2(c²−1))（Qeq_bool 可运行）

   数学内核：pair_frac(a,b) := a·b/(2(b−a)·⌊√(ab)⌋)；b = C·a 时
   化为 C·a/(2(C−1)·isqrt(C·a²))，完全平方 C=c² 下
   isqrt(c²a²) = c·a（Nat.sqrt_unique）精确闭合；一般 C 下
   a·s ≤ isqrt(Ca²) < a(s+1)（sqrt 单调 + 平方规范）两段夹逼。

   纪律（承 probe_z_frame_check.v / probe_c4_four_atom_cr.v）：
     - 纯构造性：零经典实数（不用 Stdlib.Reals）、零 Admitted、
       零自定义公理；无理 √C 不入库——一般 C 用 s=⌊√C⌋ 有理夹逼
     - nat/Z/Q 全 Set 层可计算；序判定 Qeq_bool/Qle 可运行
     - 最终定理 sigT（Set 层）；证明分量 Prop（信息无关，同
       taugrid C-TA3 口径）
     - g9_ 前缀防撞名（E144④）；Nat.sqrt_unique（9.0.1 实测存在）
   依赖：QArith/ZArith/Lia（nia）+ PeanoNat（Nat.sqrt）。
   审计：Print Assumptions 尾部。提取：g9_pairfrac_cr.ml。
   ============================================================ *)
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.QArith.QArith.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.micromega.Lia.

(* E138①：Notation 注册（8 项，恢复 Stdlib nat 记号——防 mathcomp
   污染；合并环境双兼容硬规则 9） *)
Notation "a + b" := (Nat.add a b) (at level 50, left associativity) : nat_scope.
Notation "a - b" := (Nat.sub a b) (at level 50, left associativity) : nat_scope.
Notation "a * b" := (Nat.mul a b) (at level 40, left associativity) : nat_scope.
Notation "a <= b" := (Nat.le a b) (at level 70, no associativity) : nat_scope.
Notation "a < b" := (Nat.lt a b) (at level 70, no associativity) : nat_scope.
Notation "a >= b" := (Nat.le b a) (at level 70, no associativity) : nat_scope.
Notation "a > b" := (Nat.lt b a) (at level 70, no associativity) : nat_scope.

(* QArith/ZArith 自动 Open 的 Q_scope/Z_scope 会以 Qmult/Zadd 卡死裸 nat
   算术（无类型回退）——本文件 Q 用法全为标识符（Qmake/Qeq/Qle/
   Qeq_bool），数字字面量属类型导向 Numeral 记号不受影响，故显式关闭 *)
Close Scope Q_scope.
Close Scope Z_scope.

(* ============ R0：定义（nat 可计算，全 Set 层） ============ *)

(* Q 形；前提 1 ≤ a、a < b、⌊√(ab)⌋ ≥ 1 保证分母 ≥ 2
   （Pos.of_succ_nat(den−1) 表 den，见 g9_pos_succ_nat） *)
Definition g9_pf (a b : nat) : Q :=
  Qmake (Z.of_nat (a * b))
        (Pos.of_succ_nat (2 * (b - a) * Nat.sqrt (a * b) - 1)).

(* 闭合式（有理形）：√C/(2(C−1)) 在 C=c² 时 = c/(2(c²−1)) *)
Definition g9_closed (c : nat) : Q :=
  Qmake (Z.of_nat c) (Pos.of_succ_nat (2 * (c * c - 1) - 1)).

(* Pos 桥（定义性——zfc/E180 同款） *)
Lemma g9_pos_succ : forall n : nat, Z.pos (Pos.of_succ_nat n) = Z.of_nat (S n).
Proof. intros n; destruct n; reflexivity. Qed.

(* Pos 桥（带下界形——den ≥ 1 时 Pos.of_succ_nat(den−1) 表 den） *)
Lemma g9_pos_succ_nat : forall n : nat, (1 <= n)%nat ->
  Z.pos (Pos.of_succ_nat (n - 1)) = Z.of_nat n.
Proof.
  intros n Hn. rewrite g9_pos_succ.
  replace (S (n - 1)) with n by lia. reflexivity.
Qed.

(* ============ R1：isqrt 平方规范（⌊√⌋ 精确件） ============ *)

Lemma g9_isqrt_square : forall a c : nat, Nat.sqrt (c * c * (a * a)) = Nat.mul c a.
Proof.
  intros a c. apply Nat.sqrt_unique. split; nia.
Qed.

(* isqrt 恒等：完全平方的平方根 = 本身 *)
Lemma g9_isqrt_id : forall x : nat, Nat.sqrt (x * x) = x.
Proof.
  intros x. assert (H := g9_isqrt_square x 1).
  rewrite !Nat.mul_1_l in H. exact H.
Qed.

(* 一般 C 的 isqrt 夹逼：a·s ≤ isqrt(C·a²) < a·(s+1)，s = ⌊√C⌋ *)
Lemma g9_isqrt_ladder : forall a C : nat, (1 <= a)%nat ->
  (a * Nat.sqrt C <= Nat.sqrt (C * (a * a))
   /\ Nat.sqrt (C * (a * a)) < a * (S (Nat.sqrt C)))%nat.
Proof.
  intros a C Ha.
  assert (Hs := Nat.sqrt_spec' C).
  destruct Hs as [Hlo Hhi].
  split.
  - replace ((a * Nat.sqrt C)%nat)
      with (Nat.sqrt ((a * Nat.sqrt C) * (a * Nat.sqrt C)))
      by apply g9_isqrt_id.
    apply Nat.sqrt_le_mono. nia.
  - replace ((a * (S (Nat.sqrt C)))%nat)
      with (Nat.sqrt ((a * S (Nat.sqrt C)) * (a * S (Nat.sqrt C))))
      by apply g9_isqrt_id.
    assert (Hlt2 : (C * (a * a) < a * S (Nat.sqrt C) * (a * S (Nat.sqrt C)))%nat)
      by nia.
    destruct (Nat.eq_dec (Nat.sqrt (C * (a * a))) (a * S (Nat.sqrt C))) as [Heq | Hne].
    + exfalso.
      assert (Hsp := Nat.sqrt_spec' (C * (a * a))).
      rewrite Heq in Hsp. nia.
    + assert (Hle2 : (Nat.sqrt (C * (a * a))
                       <= Nat.sqrt (a * S (Nat.sqrt C) * (a * S (Nat.sqrt C))))%nat).
      { apply Nat.sqrt_le_mono. nia. }
      assert (Hid2 := g9_isqrt_id (a * S (Nat.sqrt C))).
      lia.
Qed.

(* ============ R2：层 1——完全平方 C 的精确闭合形式 ============ *)

Lemma g9_pf_square : forall a c : nat, (1 <= a)%nat -> (2 <= c)%nat ->
  Qeq (g9_pf a (c * c * a)) (g9_closed c).
Proof.
  intros a c Ha Hc.
  assert (Hsub : (c * c * a - a = a * (c * c - 1))%nat) by nia.
  assert (Hd1 : (1 <= 2 * (c * c * a - a) * (c * a))%nat) by nia.
  assert (Hd2 : (1 <= 2 * (c * c - 1))%nat) by lia.
  assert (His : (Nat.sqrt (a * (c * c * a)) = c * a)%nat).
  { replace (a * (c * c * a))%nat with ((c * a) * (c * a))%nat by nia.
    apply g9_isqrt_id. }
  unfold g9_pf, g9_closed, Qeq; cbn [Qnum Qden].
  rewrite His.
  rewrite (g9_pos_succ_nat (2 * (c * c * a - a) * (c * a)) Hd1).
  rewrite (g9_pos_succ_nat (2 * (c * c - 1)) Hd2).
  rewrite Hsub.
  nia.
Qed.

(* ============ R3：层 2——一般 C 的双带有理夹逼 ============ *)

Theorem g9_pf_sandwich : forall a C : nat, (1 <= a)%nat -> (2 <= C)%nat ->
  Qle (Qmake (Z.of_nat C) (Pos.of_succ_nat (2 * (C - 1) * S (Nat.sqrt C) - 1)))
      (g9_pf a (C * a))
  /\ Qle (g9_pf a (C * a))
         (Qmake (Z.of_nat C) (Pos.of_succ_nat (2 * (C - 1) * Nat.sqrt C - 1))).
Proof.
  intros a C Ha HC.
  destruct (g9_isqrt_ladder a C Ha) as [Hlo Hhi].
  (* sqrt 原子的下界件必须显式入库：nia 对 Nat.sqrt 无任何内生信息，
     没有 1 <= s / 1 <= IS 时分母正性 assert 必挂（run16 行 149 真因） *)
  assert (Hs1 : (1 <= Nat.sqrt C)%nat).
  { apply (Nat.sqrt_le_mono 1 C). lia. }
  assert (HIS1 : (1 <= Nat.sqrt (C * (a * a)))%nat) by nia.
  assert (Hd1 : (1 <= 2 * (C * a - a) * Nat.sqrt (C * (a * a)))%nat) by nia.
  assert (Hd2 : (1 <= 2 * (C - 1) * S (Nat.sqrt C))%nat) by nia.
  assert (Hd3 : (1 <= 2 * (C - 1) * Nat.sqrt C)%nat) by nia.
  assert (Hsub : (C * a - a = (C - 1) * a)%nat) by lia.
  remember (C - 1)%nat as D eqn:HDc.
  assert (HdD : (1 <= D)%nat) by lia.
  assert (HsubD : (C * a - a = D * a)%nat) by lia.
  assert (HdD1 : (1 <= 2 * D * a * Nat.sqrt (C * (a * a)))%nat) by nia.
  assert (HdD2 : (1 <= 2 * D * S (Nat.sqrt C))%nat) by nia.
  assert (HdD3 : (1 <= 2 * D * Nat.sqrt C)%nat) by nia.
  assert (HeqIS : (Nat.sqrt (a * (C * a)) = Nat.sqrt (C * (a * a)))%nat).
  { f_equal. nia. }
  (* 分母整体换形：若逐段 rewrite HsubD，分母会留成 2 * (D * a) * IS
     （括号连乘形），与假设的 2 * D * a * IS 左结合形 syntactic 不等，
     pos_succ_nat 的 by assumption 必挂（run19 诊断实锤）——整体重写 *)
  assert (Hden : (2 * (C * a - a) * Nat.sqrt (a * (C * a))
                  = 2 * D * a * Nat.sqrt (C * (a * a)))%nat).
  { rewrite HsubD. rewrite HeqIS. nia. }
  (* 终局 nia 的预乘积式：把夹逼端点乘上公共正因子 2·D·C·a，
     zify 后与 Z 目标为同型多项式，nia 只需辨认（免 4 次幂搜索） *)
  assert (Hhi_le : (Nat.sqrt (C * (a * a)) <= a * S (Nat.sqrt C))%nat) by lia.
  assert (HprodL : (2 * D * C * a * Nat.sqrt (C * (a * a))
                    <= 2 * D * C * a * (a * S (Nat.sqrt C)))%nat).
  { apply Nat.mul_le_mono_l. exact Hhi_le. }
  assert (HprodU : (2 * D * C * a * (a * Nat.sqrt C)
                    <= 2 * D * C * a * Nat.sqrt (C * (a * a)))%nat).
  { apply Nat.mul_le_mono_l. exact Hlo. }
  split.
  - unfold Qle, g9_pf; cbn [Qnum Qden].
    rewrite Hden.
    rewrite (g9_pos_succ_nat (2 * D * a * Nat.sqrt (C * (a * a))) HdD1).
    rewrite (g9_pos_succ_nat (2 * D * S (Nat.sqrt C)) HdD2).
    nia.
  - unfold Qle, g9_pf; cbn [Qnum Qden].
    rewrite Hden.
    rewrite (g9_pos_succ_nat (2 * D * a * Nat.sqrt (C * (a * a))) HdD1).
    rewrite (g9_pos_succ_nat (2 * D * Nat.sqrt C) HdD3).
    nia.
Qed.

(* ============ R4：论文实例——C=4 时 1/3（可运行判定） ============ *)

Lemma g9_closed_2_13 : Qeq (g9_closed 2) (Qmake 1 3).
Proof.
  unfold Qeq, g9_closed; cbn [Qnum Qden].
  rewrite g9_pos_succ.
  replace (S (2 * (2 * 2 - 1) - 1))%nat with 6 by lia. lia.
Qed.

Lemma g9_pf_C4_13 : forall a : nat, (1 <= a)%nat ->
  Qeq_bool (g9_pf a (4 * a)) (Qmake 1 3) = true.
Proof.
  intros a Ha.
  apply Qeq_bool_iff.
  eapply Qeq_trans.
  - apply (g9_pf_square a 2); lia.
  - exact g9_closed_2_13.
Qed.

(* ============ R5：最终定理（sigT，Set 层可提取闭合式证书） ============ *)

Theorem g9_closed_form_cert : forall a c : nat, (1 <= a)%nat -> (2 <= c)%nat ->
  { q : Q & Qeq_bool q (g9_closed c) = true /\ q = g9_pf a (c * c * a) }.
Proof.
  intros a c Ha Hc.
  exists (g9_pf a (c * c * a)).
  split; [ | reflexivity ].
  apply Qeq_bool_iff. apply g9_pf_square; assumption.
Qed.

(* ============ 审计 ============ *)
Print Assumptions g9_pf_square.
Print Assumptions g9_pf_sandwich.
Print Assumptions g9_pf_C4_13.
Print Assumptions g9_closed_form_cert.

(* ============ 提取（nat/Q 全可执行——psa_guard 侧闭合式入口） ============ *)
From Stdlib Require Import Extraction.

Extraction "g9_pairfrac_cr.ml" g9_pf g9_closed g9_closed_form_cert g9_pf_C4_13.
