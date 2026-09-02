(* ============================================================
   qset_twin_base.v —— Q 信息性序工具包（C 系列构造性孪生地基）
   PSA/PSA-GSA z 区构造性轨道 · Phase 1（2026-09-02）
   ============================================================

   使命（交接文档 §3 Phase 1）：为 C1/C2/C3 孪生与 C7/RC-real 提供
   「Q 层 + QltT 型 Set 序」的公共地基——结论与数据全部 Set 层，
   存在性 sigT 打包，序事实用信息性 Set 证据，零 Reals 零经典。

   provenance（复刻即升级，双向标注）：
     · 构造方式复刻自 ConstructiveWorld-146.v
       （SHA-256 前 16 位 1866824860dde4c；仅构造方式，内容适配）：
       – Set 层恒等型 Id / id_sym / id_trans / id_cong（CW-146 L62-95）
       – Qlt_bool 判定层 + QltT := Id (…Qlt_bool…) true（CW-146 L2947/L2953）
       – QltT_to_Qlt / Qlt_to_QltT 提级构造（CW-146 L2956-2985）
     · 本项目非平凡升级（CW 侧吸收时对应登记）：
       – ★ QeqT := Id (Qeq_bool x y) true：CW 的 QleT 右支 Id x y
         （配对层恒等）对「不同表示的同一有理数」不可构造
         （1/2 与 2/4 的 QleT 在 CW 式定义下不可证）——改用布尔层
         可判定相等，QleT 右支信息完备且全分支可构造。
       – ★ qtw_tri 信息性三分（Set 层，提取为比较驱动布尔逻辑）。
       – ★ QleT_margin_ltT 正 margin 升级规则 + qtw_margin_witness
         margin 见证提取（sigT 数据件）。

   非平凡核心定理（铁律 4）：
     T1 qtw_tri           —— QltT x y + (QeqT x y + QltT y x) 全分支可构造
     T2 QleT_margin_ltT   —— QleT (x+m) y ∧ QltT 0 m ⟹ QltT x y
     T3 qtw_margin_witness —— QltT x y ⟹ sigT m, 正 margin 数据对
     T4 qtw_le_dec        —— {QleT x y} + {QltT y x} 可判定二分（sumbool）

   验收（铁律 1-3，2026-09-02 实测）：
     ① coqc EXIT=0；Print Assumptions ×27 全部字面
        「Closed under the global context」（零公理零 Admitted）。
     ② Extraction qset_twin_base.ml/.mli，ocamlc（DkMLNative 4.14.2）
        编译 EXIT=0。占位符审计：提取物仅有的 __ 为（i）提取器标准
        擦除原语 type __ = Obj.t（任何提取均含，非信号）；（ii）
        qtw_le_of_NatLe——其结论层为 nat≤ 的 Prop 证明，按设计擦除、
        不在数据路径。全部 Set 层数据件（qtw_tri / qtw_le_dec /
        qtw_half / qtw_margin_witness / qtw_ltT_of_eq_true /
        qtw_eqT_of_eq_true / qtw_NatLe_of_le）均提取为真实布尔逻辑。
     ③ 零 mathcomp / 零 Reals / 零 ConstructiveReals 依赖。

   依赖：QArith / Qabs / Lia / Lqa / Extraction / PeanoNat（为 CW
   反哺对齐，不依赖 mathcomp / Reals / ConstructiveReals）。
   双环境兼容：E138① nat 记号防御注册（合并版 mathcomp 前序劫持）。
   实测坑（记入经验卡）：
     – QArith 导入即打开 Q_scope：nat ≤ 必须 %nat 注解，否则解析为
       Qle 报「expected to have type Q」；
     – Qle 不是 AND-OR 定义（Z.le 基）：不能用 left/right 拆分，走
       Qlt_le_weak / Qle_refl；
     – QleT 目标（Set 层 Or-of-Id）上 rewrite 无 Proper 实例会乱
       展开——Qeq 同一化用 setoid_replace；
     – comparison 构造器序 Eq|Lt|Gt（Eq 在前，CW 注释即此序）；
     – sumbool 两侧须 Prop：Set 结论的二分用纯 sum；
     – -0 ≡ 0 的合一 apply 卡壳——显式参数 exact 走 kernel 转换。
   ============================================================ *)
Require Import Stdlib.QArith.QArith.
Require Import Stdlib.QArith.Qabs.
From Stdlib Require Import Lia.
From Stdlib Require Import Lqa.
From Stdlib Require Import Extraction.
From Stdlib Require Import PeanoNat.

(* E138① 记号防御注册（合并环境 mathcomp 前序劫持覆盖；独立环境同义覆盖仅 warning） *)
Notation "x + y" := (Nat.add x y) : nat_scope.
Notation "x - y" := (Nat.sub x y) : nat_scope.
Notation "x * y" := (Nat.mul x y) : nat_scope.
Notation "x <= y" := (Peano.le x y) : nat_scope.
Notation "x < y" := (Peano.lt x y) : nat_scope.
(* E259①：ssrnotations 全局前缀 #[ x ] 劫持 Q 字面量 # 记号（合并环境 9#5 语法错）——
   照抄 QArith_base L41 注册回 Q_scope（独立环境同义覆盖仅 warning） *)
Notation "x # y" := (Qmake x y) (at level 55, no associativity) : Q_scope.

(* ============================================================
   §0 Set 层逻辑基座（CW-146 L62-95 构造复刻）
   ============================================================ *)

Inductive Id {A : Set} (x : A) : A -> Set :=
| id_refl : Id x x.

Arguments id_refl {A} {x}.

(* Set 层连接词（与 stdlib Prop 层 or/and 区分：T 后缀 = Set/Type 值） *)
Definition And (A B : Set) : Set := A * B.
Definition Or  (A B : Set) : Set := A + B.

Definition id_sym {A : Set} {x y : A} (p : Id x y) : Id y x :=
  match p with
  | id_refl => id_refl
  end.

Definition id_trans {A : Set} {x y z : A} (p : Id x y) (q : Id y z) : Id x z :=
  match p, q with
  | id_refl, id_refl => id_refl
  end.

Definition id_cong {A B : Set} (f : A -> B) {x y : A} (p : Id x y) : Id (f x) (f y) :=
  match p with
  | id_refl => id_refl
  end.

(* stdlib eq（Prop）→ Set 层 Id 桥：bool 判定事实（Qcompare/Qeq_bool/
   Nat.leb 的 = true 证据）提级为 Set 层 Id 的唯一通道 *)
Definition idT_of_eq {A : Set} {x y : A} (p : x = y) : Id x y :=
  match p with
  | eq_refl => id_refl
  end.

(* ============================================================
   §1 bool 判定层与 Set 序关系
   ============================================================ *)

(* Qcompare → bool（CW-146 L2947 构造复刻；qtw_ 前缀防合并撞名） *)
Definition qtw_lt_bool (x y : Q) : bool :=
  match Qcompare x y with
  | Lt => true
  | _ => false
  end.

(* ★ T1 前置：Set 层严格序 *)
Definition QltT (x y : Q) : Set := Id (qtw_lt_bool x y) true.

(* ★ 升级件：布尔层可判定有理相等（Qeq_bool 直接 Z.eqb 交叉相乘，
   可计算、信息完备） *)
Definition QeqT (x y : Q) : Set := Id (Qeq_bool x y) true.

(* Set 层弱序：严格 < 或布尔相等 *)
Definition QleT (x y : Q) : Set := Or (QltT x y) (QeqT x y).

(* Set 层正有理数（存在性 sigT 打包——铁律 2） *)
Definition QposT : Set := sigT (fun q : Q => QltT 0 q).

(* nat ≤ 的 Set 层镜像（CW-146 L109 同型；RC-real T2 包络用） *)
Definition NatLe (n m : nat) : Set := Id (Nat.leb n m) true.

(* ============================================================
   §2 提级/降级桥（Prop ↔ Set 的全部通道，均为全函数）
   ============================================================ *)

(* Qlt (Prop) → QltT (Set)：CW-146 L2965 构造复刻 *)
Lemma Qlt_to_QltT : forall x y : Q, Qlt x y -> QltT x y.
Proof.
  intros x y H.
  unfold QltT, qtw_lt_bool.
  destruct (Qcompare x y) eqn:E.
  - (* Eq：x == y，setoid 重写后 H : y < y 矛盾 *)
    exfalso.
    assert (Heq : x == y) by (apply Qeq_alt; exact E).
    rewrite Heq in H.
    apply (Qlt_irrefl y). exact H.
  - (* Lt *)
    reflexivity.
  - (* Gt：y < x 与 H : x < y 矛盾 *)
    exfalso.
    assert (Hyx : y < x) by (apply Qgt_alt; exact E).
    apply (Qlt_irrefl x). eapply Qlt_trans. exact H. exact Hyx.
Qed.

(* QltT → Qlt：CW-146 L2956 构造复刻 *)
Lemma QltT_to_Qlt : forall x y : Q, QltT x y -> Qlt x y.
Proof.
  intros x y H.
  unfold QltT in H.
  unfold qtw_lt_bool in H.
  destruct (Qcompare x y) eqn:E; try (inversion H).
  apply Qlt_alt. exact E.
Qed.

(* Qeq (Prop) ↔ QeqT (Set) *)
Lemma QeqT_of_Qeq : forall x y : Q, x == y -> QeqT x y.
Proof.
  intros x y H.
  exact (idT_of_eq (Qeq_eq_bool _ _ H)).
Qed.

Lemma QeqT_to_Qeq : forall x y : Q, QeqT x y -> x == y.
Proof.
  intros x y H.
  assert (Hb : Qeq_bool x y = true) by (destruct H; reflexivity).
  apply Qeq_bool_eq. exact Hb.
Qed.

(* Qle (Prop) → QleT (Set)：右支经 QeqT；Gt 支 exfalso
   （False 可向任意 sort 消去——False_rect 通道，非 Prop 消去违规） *)
Lemma Qle_to_QleT : forall x y : Q, Qle x y -> QleT x y.
Proof.
  intros x y H.
  destruct (Qcompare x y) eqn:E.
  - right. apply QeqT_of_Qeq. apply Qeq_alt. exact E.
  - left. apply Qlt_to_QltT. apply Qlt_alt. exact E.
  - exfalso.
    assert (Hyx : y < x) by (apply Qgt_alt; exact E).
    destruct (Qle_lt_or_eq _ _ H) as [Hlt' | Heq'].
    + apply (Qlt_irrefl y). eapply Qlt_trans. exact Hyx. exact Hlt'.
    + rewrite Heq' in Hyx. apply (Qlt_irrefl y). exact Hyx.
Qed.

(* QleT → Qle（Qle 非 AND-OR 定义，走 Qlt_le_weak / Qle_refl） *)
Lemma QleT_to_Qle : forall x y : Q, QleT x y -> Qle x y.
Proof.
  intros x y H.
  destruct H as [Hlt | Heq].
  - apply Qlt_le_weak. apply QltT_to_Qlt. exact Hlt.
  - rewrite (QeqT_to_Qeq _ _ Heq). apply Qle_refl.
Qed.

(* bool 判定事实直接提级（反射封口通道：vm_compute 出 = true 后一行提级） *)
Lemma qtw_ltT_of_eq_true : forall x y : Q, qtw_lt_bool x y = true -> QltT x y.
Proof.
  intros x y H. exact (idT_of_eq H).
Qed.

Lemma qtw_eqT_of_eq_true : forall x y : Q, Qeq_bool x y = true -> QeqT x y.
Proof.
  intros x y H. exact (idT_of_eq H).
Qed.

(* NatLe 桥（注意：QArith 打开 Q_scope，nat ≤ 必须 %nat 注解；
   Nat.leb_le 为 iff，apply 自动取对应方向） *)
Lemma qtw_NatLe_of_le : forall n m : nat, (n <= m)%nat -> NatLe n m.
Proof.
  intros n m H.
  assert (Hb : (Nat.leb n m) = true) by (apply Nat.leb_le; exact H).
  exact (idT_of_eq Hb).
Qed.

Lemma qtw_le_of_NatLe : forall n m : nat, NatLe n m -> (n <= m)%nat.
Proof.
  intros n m H.
  assert (Hb : (Nat.leb n m) = true) by (destruct H; reflexivity).
  apply Nat.leb_le. exact Hb.
Qed.

(* ============================================================
   §3 信息性三分与可判定二分（★ 核心定理 T1/T4）
   ============================================================ *)

(* ★ T1：全分支可构造的信息性三分（comparison 构造器序 Eq|Lt|Gt） *)
Definition qtw_tri (x y : Q) : QltT x y + (QeqT x y + QltT y x).
Proof.
  destruct (Qcompare x y) eqn:E.
  - right. left. apply QeqT_of_Qeq. apply Qeq_alt. exact E.
  - left. apply Qlt_to_QltT. apply Qlt_alt. exact E.
  - right. right. apply Qlt_to_QltT. apply Qgt_alt. exact E.
Defined.

(* ★ T4：可判定二分（Set 层 sum——sumbool 两侧须 Prop，不适用） *)
Definition qtw_le_dec (x y : Q) : QleT x y + QltT y x.
Proof.
  destruct (Qcompare x y) eqn:E.
  - left. right. apply QeqT_of_Qeq. apply Qeq_alt. exact E.
  - left. left. apply Qlt_to_QltT. apply Qlt_alt. exact E.
  - right. apply Qlt_to_QltT. apply Qgt_alt. exact E.
Defined.

(* ============================================================
   §4 传递性与混合（转换 + lra 机械化：Prop 层线性推理 + 提级）
   ============================================================ *)

Lemma QltT_trans : forall x y z : Q, QltT x y -> QltT y z -> QltT x z.
Proof.
  intros x y z H1 H2.
  apply Qlt_to_QltT.
  assert (H1' : Qlt x y) by (apply QltT_to_Qlt; exact H1).
  assert (H2' : Qlt y z) by (apply QltT_to_Qlt; exact H2).
  lra.
Qed.

Lemma QleT_refl : forall x : Q, QleT x x.
Proof. intros x. right. apply QeqT_of_Qeq. apply Qeq_refl. Qed.

Lemma QleT_trans : forall x y z : Q, QleT x y -> QleT y z -> QleT x z.
Proof.
  intros x y z H1 H2.
  apply Qle_to_QleT.
  assert (H1' : Qle x y) by (apply QleT_to_Qle; exact H1).
  assert (H2' : Qle y z) by (apply QleT_to_Qle; exact H2).
  lra.
Qed.

Lemma QltT_leT_trans : forall x y z : Q, QltT x y -> QleT y z -> QltT x z.
Proof.
  intros x y z H1 H2.
  apply Qlt_to_QltT.
  assert (H1' : Qlt x y) by (apply QltT_to_Qlt; exact H1).
  assert (H2' : Qle y z) by (apply QleT_to_Qle; exact H2).
  lra.
Qed.

Lemma QleT_ltT_trans : forall x y z : Q, QleT x y -> QltT y z -> QltT x z.
Proof.
  intros x y z H1 H2.
  apply Qlt_to_QltT.
  assert (H1' : Qle x y) by (apply QleT_to_Qle; exact H1).
  assert (H2' : Qlt y z) by (apply QltT_to_Qlt; exact H2).
  lra.
Qed.

(* QeqT 同一化传递：等式两端替换（代数链收口主力件） *)
Lemma qtw_leT_congr_r : forall x y z : Q, QleT x y -> QeqT y z -> QleT x z.
Proof.
  intros x y z H Heq.
  destruct H as [Hlt | Heqx].
  - left. apply Qlt_to_QltT.
    rewrite <- (QeqT_to_Qeq _ _ Heq).
    apply QltT_to_Qlt. exact Hlt.
  - right. apply QeqT_of_Qeq.
    apply (Qeq_trans x y z).
    + apply QeqT_to_Qeq. exact Heqx.
    + apply QeqT_to_Qeq. exact Heq.
Qed.

Lemma qtw_leT_congr_l : forall x y z : Q, QleT x y -> QeqT z x -> QleT z y.
Proof.
  intros x y z H Heq.
  destruct H as [Hlt | Heqx].
  - left. apply Qlt_to_QltT.
    rewrite (QeqT_to_Qeq _ _ Heq).
    apply QltT_to_Qlt. exact Hlt.
  - right. apply QeqT_of_Qeq.
    apply (Qeq_trans z x y).
    + apply QeqT_to_Qeq. exact Heq.
    + apply QeqT_to_Qeq. exact Heqx.
Qed.

Lemma qtw_ltT_congr_r : forall x y z : Q, QltT x y -> QeqT y z -> QltT x z.
Proof.
  intros x y z H Heq.
  apply Qlt_to_QltT.
  rewrite <- (QeqT_to_Qeq _ _ Heq).
  apply QltT_to_Qlt. exact H.
Qed.

Lemma qtw_ltT_congr_l : forall x y z : Q, QltT x y -> QeqT z x -> QltT z y.
Proof.
  intros x y z H Heq.
  apply Qlt_to_QltT.
  rewrite (QeqT_to_Qeq _ _ Heq).
  apply QltT_to_Qlt. exact H.
Qed.

(* Prop 层辅助件（供 ring/rewrite 的 side condition 使用） *)
Lemma QltT_neq : forall x y : Q, QltT x y -> x <> y.
Proof.
  intros x y H Heq.
  rewrite Heq in H.
  apply (Qlt_irrefl y).
  apply QltT_to_Qlt. exact H.
Qed.

(* ============================================================
   §5 加法单调兼容
   ============================================================ *)

Lemma Qplus_ltT_compat : forall a b c d : Q, QltT a b -> QltT c d -> QltT (a + c) (b + d).
Proof.
  intros a b c d H1 H2.
  apply Qlt_to_QltT.
  assert (H1' : Qlt a b) by (apply QltT_to_Qlt; exact H1).
  assert (H2' : Qlt c d) by (apply QltT_to_Qlt; exact H2).
  lra.
Qed.

Lemma Qplus_leT_compat : forall a b c d : Q, QleT a b -> QleT c d -> QleT (a + c) (b + d).
Proof.
  intros a b c d H1 H2.
  apply Qle_to_QleT.
  assert (H1' : Qle a b) by (apply QleT_to_Qle; exact H1).
  assert (H2' : Qle c d) by (apply QleT_to_Qle; exact H2).
  lra.
Qed.

Lemma Qplus_ltT_compat_l : forall a b c : Q, QltT a b -> QltT (c + a) (c + b).
Proof.
  intros a b c H.
  apply Qlt_to_QltT.
  assert (H' : Qlt a b) by (apply QltT_to_Qlt; exact H).
  lra.
Qed.

Lemma Qplus_ltT_compat_r : forall a b c : Q, QltT a b -> QltT (a + c) (b + c).
Proof.
  intros a b c H.
  apply Qlt_to_QltT.
  assert (H' : Qlt a b) by (apply QltT_to_Qlt; exact H).
  lra.
Qed.

Lemma Qplus_leT_compat_l : forall a b c : Q, QleT a b -> QleT (c + a) (c + b).
Proof.
  intros a b c H.
  apply Qle_to_QleT.
  assert (H' : Qle a b) by (apply QleT_to_Qle; exact H).
  lra.
Qed.

Lemma Qplus_leT_compat_r : forall a b c : Q, QleT a b -> QleT (a + c) (b + c).
Proof.
  intros a b c H.
  apply Qle_to_QleT.
  assert (H' : Qle a b) by (apply QleT_to_Qle; exact H).
  lra.
Qed.

(* 取反反序 *)
Lemma Qopp_ltT_compat : forall x y : Q, QltT x y -> QltT (- y) (- x).
Proof.
  intros x y H.
  apply Qlt_to_QltT.
  assert (H' : Qlt x y) by (apply QltT_to_Qlt; exact H).
  lra.
Qed.

Lemma Qopp_leT_compat : forall x y : Q, QleT x y -> QleT (- y) (- x).
Proof.
  intros x y H.
  apply Qle_to_QleT.
  assert (H' : Qle x y) by (apply QleT_to_Qle; exact H).
  lra.
Qed.

(* ============================================================
   §6 乘法单调兼容与非负性
   ============================================================ *)

Lemma Qmult_ltT_compat_r : forall x y a : Q, QltT 0 a -> QltT x y -> QltT (x * a) (y * a).
Proof.
  intros x y a Ha H.
  apply Qlt_to_QltT.
  apply (Qmult_lt_compat_r x y a).
  - apply QltT_to_Qlt. exact Ha.
  - apply QltT_to_Qlt. exact H.
Qed.

Lemma Qmult_ltT_compat_l : forall x y a : Q, QltT 0 a -> QltT x y -> QltT (a * x) (a * y).
Proof.
  intros x y a Ha H.
  apply Qlt_to_QltT.
  assert (Hlt : a * x < a * y).
  { apply (Qmult_lt_l x y a).
    - apply QltT_to_Qlt. exact Ha.
    - apply QltT_to_Qlt. exact H. }
  exact Hlt.
Qed.

Lemma Qmult_leT_compat_r : forall x y a : Q, QleT 0 a -> QleT x y -> QleT (x * a) (y * a).
Proof.
  intros x y a Ha H.
  apply Qle_to_QleT.
  apply (Qmult_le_compat_r x y a).
  - apply QleT_to_Qle. exact H.
  - apply QleT_to_Qle. exact Ha.
Qed.

Lemma Qmult_leT_compat_l : forall x y a : Q, QleT 0 a -> QleT x y -> QleT (a * x) (a * y).
Proof.
  intros x y a Ha H.
  apply Qle_to_QleT.
  assert (Ha' : Qle 0 a) by (apply QleT_to_Qle; exact Ha).
  assert (H' : Qle x y) by (apply QleT_to_Qle; exact H).
  (* Qeq 同一化走 setoid_replace（Qle 目标上 rewrite 无 Proper 实例） *)
  setoid_replace (a * x) with (x * a) by (apply Qmult_comm).
  setoid_replace (a * y) with (y * a) by (apply Qmult_comm).
  apply (Qmult_le_compat_r x y a H' Ha').
Qed.

Lemma Qmult_leT_0_compat : forall x y : Q, QleT 0 x -> QleT 0 y -> QleT 0 (x * y).
Proof.
  intros x y Hx Hy.
  apply Qle_to_QleT.
  apply (Qmult_le_0_compat x y).
  - apply QleT_to_Qle. exact Hx.
  - apply QleT_to_Qle. exact Hy.
Qed.

Lemma Qmult_ltT_0_compat : forall x y : Q, QltT 0 x -> QltT 0 y -> QltT 0 (x * y).
Proof.
  intros x y Hx Hy.
  apply Qlt_to_QltT.
  apply (Qmult_lt_0_compat x y).
  - apply QltT_to_Qlt. exact Hx.
  - apply QltT_to_Qlt. exact Hy.
Qed.

(* 平方非负（证书链最常用的代数事实）——三分讨论符号 *)
Lemma Qsqr_nonnegT : forall x : Q, QleT 0 (x * x).
Proof.
  intros x.
  destruct (qtw_tri 0 x) as [Hpos | [Heq0 | Hneg]].
  - (* 0 < x：正乘正非负 *)
    apply Qmult_leT_0_compat.
    + left. exact Hpos.
    + left. exact Hpos.
  - (* x == 0：平方同余于 0*0 *)
    right. apply QeqT_of_Qeq.
    assert (Hx0 : x == 0) by (apply QeqT_to_Qeq; exact Heq0).
    rewrite Hx0.
    simpl. apply Qeq_refl.
  - (* x < 0：x*x == (−x)*(−x)，−x > 0 *)
    assert (Hnx : QltT 0 (- x)) by exact (Qopp_ltT_compat x 0 Hneg).
    apply Qle_to_QleT.
    assert (Hsq : x * x == (- x) * (- x)) by ring.
    rewrite Hsq.
    assert (H0nx : 0 <= - x).
    { assert (Hx0 : x < 0) by (apply QltT_to_Qlt; exact Hneg).
      lra. }
    apply (Qmult_le_0_compat (- x) (- x) H0nx H0nx).
Qed.

(* 正因子消去（证书检查双向用） *)
Lemma Qmult_ltT_cancel_r : forall x y a : Q, QltT 0 a -> QltT (x * a) (y * a) -> QltT x y.
Proof.
  intros x y a Ha H.
  apply Qlt_to_QltT.
  apply ((Qmult_lt_r x y a) (proj1 (Qlt_alt 0 a) (QltT_to_Qlt 0 a Ha))).
  apply QltT_to_Qlt. exact H.
Qed.

Lemma Qmult_leT_cancel_r : forall x y a : Q, QltT 0 a -> QleT (x * a) (y * a) -> QleT x y.
Proof.
  intros x y a Ha H.
  apply Qle_to_QleT.
  apply (Qmult_lt_0_le_reg_r x y a).
  - apply QltT_to_Qlt. exact Ha.
  - apply QleT_to_Qle. exact H.
Qed.

(* ============================================================
   §7 绝对值
   ============================================================ *)

Lemma Qabs_nonnegT : forall x : Q, QleT 0 (Qabs x).
Proof.
  intros x. apply Qle_to_QleT. apply Qabs_nonneg.
Qed.

Lemma Qabs_triangle_T : forall x y : Q, QleT (Qabs (x + y)) (Qabs x + Qabs y).
Proof.
  intros x y. apply Qle_to_QleT. apply Qabs_triangle.
Qed.

Lemma Qabs_posT : forall x : Q, QleT 0 x -> QeqT (Qabs x) x.
Proof.
  intros x H.
  apply QeqT_of_Qeq. apply Qabs_pos. apply QleT_to_Qle. exact H.
Qed.

(* ============================================================
   §8 正 margin 见证族（★ 核心定理 T2/T3）
   ============================================================ *)

(* ★ T2：正 margin 升级规则—— exhibited m > 0 且 x + m ≤ y ⟹ x < y。
   证书工作的主力件：代数层凑出正差即得严格序。 *)
Lemma QleT_margin_ltT : forall x y m : Q, QleT (x + m) y -> QltT 0 m -> QltT x y.
Proof.
  intros x y m Hle Hm.
  assert (Hmp : Qlt 0 m) by (apply QltT_to_Qlt; exact Hm).
  destruct Hle as [Hlt | Heq].
  - assert (HltP : Qlt (x + m) y) by (apply QltT_to_Qlt; exact Hlt).
    apply Qlt_to_QltT. lra.
  - assert (HeqP : x + m == y) by (apply QeqT_to_Qeq; exact Heq).
    assert (HleP : x + m <= y) by (rewrite HeqP; apply Qle_refl).
    apply Qlt_to_QltT. lra.
Qed.

(* ★ T3：margin 见证提取（sigT 数据件，Defined 可提取）：
   QltT x y ⟹ 存在正 m 使 x + m ≤ y（取 m := y − x） *)
Definition qtw_margin_witness (x y : Q) (H : QltT x y)
  : sigT (fun m : Q => And (QltT 0 m) (QleT (x + m) y)).
Proof.
  exists (y - x)%Q.
  split.
  - apply Qlt_to_QltT.
    assert (H' : Qlt x y) by (apply QltT_to_Qlt; exact H).
    lra.
  - apply Qle_to_QleT.
    assert (H' : Qlt x y) by (apply QltT_to_Qlt; exact H).
    lra.
Defined.

(* 差刻画：QleT x y ↔ QleT 0 (y − x)（双向） *)
Lemma qtw_leT_diff_r : forall x y : Q, QleT x y -> QleT 0 (y - x).
Proof.
  intros x y H.
  apply Qle_to_QleT.
  assert (H' : Qle x y) by (apply QleT_to_Qle; exact H).
  lra.
Qed.

Lemma qtw_diff_leT_r : forall x y : Q, QleT 0 (y - x) -> QleT x y.
Proof.
  intros x y H.
  apply Qle_to_QleT.
  assert (H' : Qle 0 (y - x)) by (apply QleT_to_Qle; exact H).
  lra.
Qed.

(* half 分解：正数的一半仍正（见证 = 数据 (1#2)*e，提取为乘法） *)
Definition qtw_half (e : Q) (He : QltT 0 e) : sigT (fun h : Q => QltT 0 h).
Proof.
  assert (Hep : Qlt 0 e) by (apply QltT_to_Qlt; exact He).
  exists ((1#2) * e)%Q.
  apply Qlt_to_QltT.
  apply (Qmult_lt_0_compat (1#2)%Q e).
  - unfold Qlt. simpl. lia.
  - exact Hep.
Defined.

(* half 相等（证明侧算术：field 处理 Qeq） *)
Lemma qtw_half_eq : forall e : Q, (e/2 + e/2)%Q == e.
Proof. intros e. field. Qed.

(* ============================================================
   §9 有限求和工具包（含端点约定：qtw_qsum f n = Σ_{k≤n} f k，n+1 项，
   与 CRsum 同约定，便于孪生对照）
   ============================================================ *)

Fixpoint qtw_qsum (f : nat -> Q) (n : nat) : Q :=
  match n with
  | O => f O
  | S n' => qtw_qsum f n' + f (S n')
  end.

(* 逐点 Qeq 同一化（代数变形主力） *)
Lemma qtw_qsum_ext : forall (f g : nat -> Q) (n : nat),
  (forall k : nat, (k <= n)%nat -> f k == g k) ->
  qtw_qsum f n == qtw_qsum g n.
Proof.
  intros f g n H.
  induction n as [| n IH].
  - apply H. apply Nat.le_0_l.
  - cbn [qtw_qsum].
    assert (HIH : qtw_qsum f n == qtw_qsum g n).
    { apply IH. intros k Hk. apply H. lia. }
    rewrite HIH.
    setoid_replace (f (S n)) with (g (S n)) by (apply H; lia).
    reflexivity.
Qed.

(* 加法/减法/数乘分配 *)
Lemma qtw_qsum_plus : forall (f g : nat -> Q) (n : nat),
  qtw_qsum (fun k => f k + g k) n == qtw_qsum f n + qtw_qsum g n.
Proof.
  intros f g n.
  induction n as [| n IH].
  - reflexivity.
  - cbn [qtw_qsum]. rewrite IH. ring.
Qed.

Lemma qtw_qsum_opp : forall (f : nat -> Q) (n : nat),
  qtw_qsum (fun k => - f k) n == - qtw_qsum f n.
Proof.
  intros f n.
  induction n as [| n IH].
  - reflexivity.
  - cbn [qtw_qsum]. rewrite IH. ring.
Qed.

Lemma qtw_qsum_minus : forall (f g : nat -> Q) (n : nat),
  qtw_qsum (fun k => f k - g k) n == qtw_qsum f n - qtw_qsum g n.
Proof.
  intros f g n.
  assert (H1 : qtw_qsum (fun k => f k - g k) n == qtw_qsum (fun k => f k + (- g k)) n).
  { apply qtw_qsum_ext. intros k _. unfold Qminus. ring. }
  rewrite H1.
  rewrite qtw_qsum_plus.
  rewrite qtw_qsum_opp.
  reflexivity.
Qed.

Lemma qtw_qsum_scale : forall (a : Q) (f : nat -> Q) (n : nat),
  qtw_qsum (fun k => a * f k) n == a * qtw_qsum f n.
Proof.
  intros a f n.
  induction n as [| n IH].
  - reflexivity.
  - cbn [qtw_qsum]. rewrite IH. ring.
Qed.

(* 平移：Σ_{k≤n} f (S k) + f 0 == Σ_{k≤S n} f k *)
Lemma qtw_qsum_shift : forall (f : nat -> Q) (n : nat),
  f O + qtw_qsum (fun k => f (S k)) n == qtw_qsum f (S n).
Proof.
  intros f n.
  induction n as [| n IH].
  - reflexivity.
  - cbn [qtw_qsum].
    setoid_replace (f O + (qtw_qsum (fun k => f (S k)) n + f (S (S n))))
      with ((f O + qtw_qsum (fun k => f (S k)) n) + f (S (S n))) by ring.
    rewrite IH.
    reflexivity.
Qed.

(* 双和换序 ★（Frobenius/Gram 展开核心） *)
Lemma qtw_qsum_swap : forall (f : nat -> nat -> Q) (n m : nat),
  qtw_qsum (fun i => qtw_qsum (fun j => f i j) m) n
  == qtw_qsum (fun j => qtw_qsum (fun i => f i j) n) m.
Proof.
  intros f n m.
  induction n as [| n IH].
  - reflexivity.
  - cbn [qtw_qsum].
    rewrite qtw_qsum_plus.
    rewrite IH.
    reflexivity.
Qed.

(* 单行对角分裂：i ≤ n 时 Σ_{j≤n} f i j == f i i + Σ_{j≤n, j≠i} f i j *)
Lemma qtw_qsum_split_dec : forall (f : nat -> nat -> Q) (i n : nat), (i <= n)%nat ->
  qtw_qsum (fun j => f i j) n
  == f i i + qtw_qsum (fun j => if Nat.eq_dec i j then 0%Q else f i j) n.
Proof.
  intros f i n Hin.
  induction n as [| n IH].
  - assert (Hiz : i = 0%nat) by lia. subst i.
    cbn [qtw_qsum].
    destruct (Nat.eq_dec 0 0) as [_ | Hne].
    + ring.
    + exfalso. apply Hne. reflexivity.
  - cbn [qtw_qsum].
    destruct (Nat.eq_dec i (S n)) as [He | Hne].
    + (* i = S n：hole 恰在 S n 位置，前段无洞 *)
      subst i.
      rewrite (qtw_qsum_ext (fun j => f (S n) j)
                            (fun j => if Nat.eq_dec (S n) j then 0%Q else f (S n) j) n).
      2:{ intros k Hk. destruct (Nat.eq_dec (S n) k) as [He2 | _].
          - exfalso. lia.
          - reflexivity. }
      ring.
    + (* i ≤ n：hole 在前段，IH 桥接 *)
      assert (Hin' : (i <= n)%nat) by lia.
      specialize (IH Hin').
      rewrite IH.
      destruct (Nat.eq_dec i (S n)) as [He2 | _].
      * exfalso. lia.
      * ring.
Qed.

(* 双和对角分裂：Σ_{i≤n} Σ_{j≤n} f i j == Σ_i f i i + Σ_{i≠j} f i j *)
Lemma qtw_qsum2_split_dec : forall (f : nat -> nat -> Q) (n : nat),
  qtw_qsum (fun i => qtw_qsum (fun j => f i j) n) n
  == qtw_qsum (fun i => f i i) n
     + qtw_qsum (fun i => qtw_qsum (fun j => if Nat.eq_dec i j then 0%Q else f i j) n) n.
Proof.
  intros f n.
  setoid_replace
    (qtw_qsum (fun i => qtw_qsum (fun j => f i j) n) n)
    with (qtw_qsum (fun i => f i i + qtw_qsum (fun j => if Nat.eq_dec i j then 0%Q else f i j) n) n).
  2:{ apply qtw_qsum_ext. intros i Hi.
      apply qtw_qsum_split_dec. exact Hi. }
  rewrite qtw_qsum_plus.
  ring.
Qed.

(* 逐项非负 ⟹ 和非负 *)
Lemma qtw_qsum_nonneg : forall (f : nat -> Q) (n : nat),
  (forall k : nat, (k <= n)%nat -> QleT 0 (f k)) ->
  QleT 0 (qtw_qsum f n).
Proof.
  intros f n H.
  induction n as [| n IH].
  - apply H. apply Nat.le_0_l.
  - cbn [qtw_qsum].
    apply (qtw_leT_congr_l (0 + 0)%Q (qtw_qsum f n + f (S n)) 0%Q).
    + apply Qplus_leT_compat.
      * apply IH. intros k Hk. apply H. lia.
      * apply H. lia.
    + apply QeqT_of_Qeq. ring.
Qed.

(* 逐项控制 ⟹ 和控制 *)
Lemma qtw_qsum_le : forall (f g : nat -> Q) (n : nat),
  (forall k : nat, (k <= n)%nat -> QleT (f k) (g k)) ->
  QleT (qtw_qsum f n) (qtw_qsum g n).
Proof.
  intros f g n H.
  induction n as [| n IH].
  - apply H. apply Nat.le_0_l.
  - apply Qplus_leT_compat.
    + apply IH. intros k Hk. apply H. lia.
    + apply H. lia.
Qed.

(* 和的绝对值三角：|Σ f| ≤ Σ |f| *)
Lemma qtw_qsum_abs_le : forall (f : nat -> Q) (n : nat),
  QleT (Qabs (qtw_qsum f n)) (qtw_qsum (fun k => Qabs (f k)) n).
Proof.
  intros f n.
  induction n as [| n IH].
  - apply QleT_refl.
  - apply QleT_trans with (Qabs (qtw_qsum f n) + Qabs (f (S n))).
    + apply Qabs_triangle_T.
    + apply Qplus_leT_compat.
      * exact IH.
      * apply QleT_refl.
Qed.

(* ============================================================
   §10 绝对值代数与 AM–GM（平方形态，无开方）
   ============================================================ *)

Lemma qtw_abs_sqr : forall a : Q, Qabs a * Qabs a == a * a.
Proof.
  intros a.
  destruct (qtw_tri a 0) as [Hneg | [Heq | Hpos]].
  - (* a < 0：Qabs a == -a *)
    assert (Ha : Qabs a == - a).
    { rewrite <- (Qabs_opp a).
      apply Qabs_pos.
      assert (Ha' : a < 0) by (apply QltT_to_Qlt; exact Hneg).
      lra. }
    rewrite Ha. ring.
  - (* a == 0 *)
    rewrite (QeqT_to_Qeq _ _ Heq).
    reflexivity.
  - (* a > 0：Qabs a == a *)
    rewrite (Qabs_pos a).
    + reflexivity.
    + assert (Ha' : 0 <= a) by (apply Qlt_le_weak; apply QltT_to_Qlt; exact Hpos).
      exact Ha'.
Qed.

Lemma qtw_le_add_pos : forall x d : Q, Qle 0 d -> Qle x (x + d).
Proof. intros x d H. lra. Qed.

(* AM–GM 绝对值形态：2|a||b| ≤ a² + b²（零开方，证书链主力） *)
Lemma qtw_amgm_abs : forall a b : Q, Qle (2 * (Qabs a * Qabs b)) (a * a + b * b).
Proof.
  intros a b.
  assert (Hsq : Qle 0 ((Qabs a - Qabs b) * (Qabs a - Qabs b))).
  { apply QleT_to_Qle. apply Qsqr_nonnegT. }
  setoid_replace ((Qabs a - Qabs b) * (Qabs a - Qabs b))
    with (Qabs a * Qabs a + Qabs b * Qabs b - 2 * (Qabs a * Qabs b)) in Hsq by ring.
  rewrite (qtw_abs_sqr a) in Hsq.
  rewrite (qtw_abs_sqr b) in Hsq.
  setoid_replace (a * a + b * b)
    with (2 * (Qabs a * Qabs b) + (a * a + b * b - 2 * (Qabs a * Qabs b))) by ring.
  apply qtw_le_add_pos. exact Hsq.
Qed.

(* ============================================================
   §11 提取与审计
   ============================================================ *)

Extraction "qset_twin_base.ml" qtw_tri qtw_le_dec qtw_half qtw_margin_witness
  qtw_ltT_of_eq_true qtw_eqT_of_eq_true qtw_NatLe_of_le qtw_le_of_NatLe
  qtw_qsum.

Print Assumptions qtw_tri.
Print Assumptions qtw_le_dec.
Print Assumptions Qlt_to_QltT.
Print Assumptions QltT_to_Qlt.
Print Assumptions QeqT_of_Qeq.
Print Assumptions QeqT_to_Qeq.
Print Assumptions Qle_to_QleT.
Print Assumptions QleT_to_Qle.
Print Assumptions qtw_leT_congr_r.
Print Assumptions qtw_leT_congr_l.
Print Assumptions qtw_ltT_congr_r.
Print Assumptions qtw_ltT_congr_l.
Print Assumptions QleT_margin_ltT.
Print Assumptions qtw_margin_witness.
Print Assumptions QltT_trans.
Print Assumptions QleT_trans.
Print Assumptions Qplus_ltT_compat.
Print Assumptions Qplus_leT_compat.
Print Assumptions Qmult_ltT_compat_r.
Print Assumptions Qmult_leT_compat_r.
Print Assumptions Qmult_leT_0_compat.
Print Assumptions Qmult_ltT_0_compat.
Print Assumptions Qsqr_nonnegT.
Print Assumptions Qmult_ltT_cancel_r.
Print Assumptions Qmult_leT_cancel_r.
Print Assumptions Qabs_nonnegT.
Print Assumptions Qabs_triangle_T.
Print Assumptions qtw_leT_diff_r.
Print Assumptions qtw_diff_leT_r.
Print Assumptions qtw_NatLe_of_le.
Print Assumptions qtw_le_of_NatLe.
Print Assumptions qtw_qsum_ext.
Print Assumptions qtw_qsum_plus.
Print Assumptions qtw_qsum_minus.
Print Assumptions qtw_qsum_scale.
Print Assumptions qtw_qsum_shift.
Print Assumptions qtw_qsum_swap.
Print Assumptions qtw_qsum_split_dec.
Print Assumptions qtw_qsum2_split_dec.
Print Assumptions qtw_qsum_nonneg.
Print Assumptions qtw_qsum_le.
Print Assumptions qtw_qsum_abs_le.
Print Assumptions qtw_abs_sqr.
Print Assumptions qtw_amgm_abs.
