(* 拆分自 Riemann_Hypothesis_Proof_Framework.v（复分析证明库 v6.0）*)
(* 库: ca_algebra  原文行区间: 294-475  机械拆分，未改动内容 *)

Require Import Stdlib.Reals.Reals.          (* 实数公理系统及全套定理 *)
Require Import Stdlib.Reals.Rdefinitions.  (* 实数的原始定义（0,1,加法,乘法等）*)
Require Import Stdlib.Reals.RIneq.         (* 实数不等式基本引理 *)
Require Import Stdlib.Reals.Rtrigo_def.    (* 三角函数定义（sin, cos, PI）*)
Require Import Stdlib.Reals.Rtrigo1.       (* 三角函数基本性质（恒等式、单调性）*)
Require Import Stdlib.Reals.Rsqrt_def.     (* 平方根函数 sqrt 的定义 *)
Require Import Stdlib.Reals.Ranalysis1.    (* 一元实分析基础（导数、可导性、连续性）*)
Require Import Stdlib.Reals.Ranalysis.     (* 实分析汇总模块（包含 Ranalysis1-5）*)
Require Import Stdlib.Reals.Ranalysis3.    (* 高级导数定理（链式法则、反函数定理等）*)
Require Import Stdlib.Reals.Rpower.        (* 实数幂函数 Rpower 及其性质 *)
Require Import Stdlib.Lists.List.          (* 标准列表库，提供列表类型及常用操作 *)
Require Import Stdlib.Arith.Arith.         (* 自然数算术基础库 *)
Require Import Stdlib.Init.Nat.            (* 自然数初始化模块，定义 nat 类型及基本运算 *)
Require Import Stdlib.Classes.RelationClasses.  (* 关系类，定义 Reflexive, Symmetric, Transitive 等 *)
Require Import Stdlib.Program.Basics.      (* 编程基础，提供 id, compose 等函数 *)
Require Import Stdlib.Reals.R_sqrt.        (* 平方根函数及其性质（与 Rsqrt_def 类似）*)
Require Import Stdlib.Logic.ProofIrrelevance.   (* 证明无关性公理 *)
Require Import Stdlib.Logic.Classical.     (* 经典逻辑（排中律）*)
Require Import Stdlib.Logic.FunctionalExtensionality. (* 函数外延性公理 *)
Require Import Stdlib.Logic.IndefiniteDescription. (* 不定描述原理 *)
Require Import Stdlib.Classes.Morphisms.   (* 态射类，用于 Proper 等 *)
Require Import Stdlib.Classes.RelationPairs. (* 关系对组合 *)
Require Import Stdlib.Arith.PeanoNat.      (* 皮亚诺自然数算术，包含加法、乘法、比较等 *)
Require Import Stdlib.ZArith.ZArith.       (* 整数算术总集 *)
Require Import Stdlib.ZArith.Zdiv.         (* 整数除法 *)
Require Import Stdlib.micromega.Lia.       (* 线性整数算术自动化策略（用于 lia）*)
Require Import Stdlib.Strings.String.      (* 字符串类型及操作（用于调试/注释）*)
Require Import Stdlib.micromega.Lra.       (* 线性实数算术自动化策略（用于 lra）*)
From Stdlib Require Import Lia.            (* 再次导入 Lia，确保可用（冗余）*)
  
Local Open Scope R_scope.               (* 开启实数作用域，使实数运算符自动生效 *)
  
(* 导入 Rolle 定理所需的库 *)
From Stdlib Require Ranalysis5.              (* 包含 Rolle 定理的高级分析模块 *)
Open Scope R_scope.

Require Import ca_base.

Require Import Stdlib.Logic.IndefiniteDescription.

(* ====================================================
   第2章：代数结构 (Level 1)
   说明：
   - 群：添加右单位元、右逆元、逆元 Proper 性；
   - 环：添加右零元、右负元、右乘单位元；
   - 域：添加乘法交换律、1≠0、双侧逆元；
   - 代数整数：完全重写，使用首一整系数多项式。
   ==================================================== *)
  
(* 2.1 群结构 *)
Module GroupTheory.

Import ComplexNumbers.

(* 群结构类定义 *)
Class Group (G : Type) := {
  g_eq : G -> G -> Prop;
  g_mul : G -> G -> G;
  g_inv : G -> G;
  g_one : G;

  (* 结合律 *)
  g_assoc : forall x y z : G,
    g_eq (g_mul (g_mul x y) z) (g_mul x (g_mul y z));

  (* 单位元性质 *)
  g_left_id  : forall x : G, g_eq (g_mul g_one x) x;
  g_right_id : forall x : G, g_eq (g_mul x g_one) x;

  (* 逆元性质 *)
  g_left_inv  : forall x : G, g_eq (g_mul (g_inv x) x) g_one;
  g_right_inv : forall x : G, g_eq (g_mul x (g_inv x)) g_one;

  (* 等价关系 *)
  g_reflexive  : Reflexive g_eq;
  g_symmetric  : Symmetric g_eq;
  g_transitive : Transitive g_eq;

  (* 运算的兼容性 *)
  g_mul_proper : Proper (g_eq ==> g_eq ==> g_eq) g_mul;
  g_inv_proper : Proper (g_eq ==> g_eq) g_inv
}.

(* 伽罗华群记录定义 *)
Record GaloisGroup : Type := {
  base_field : Type;
  extension_field : Type;
  embedding : base_field -> extension_field;
  automorphisms : list (extension_field -> extension_field);
  group_structure : Group (extension_field -> extension_field)
}.

End GroupTheory.

(* 2.2 环与域 *)
Module RingFieldTheory.

(* 环结构类定义 *)
Class Ring (R : Type) := {
  r_eq : R -> R -> Prop;
  r_add : R -> R -> R;
  r_mul : R -> R -> R;
  r_zero : R;
  r_one : R;
  r_neg : R -> R;

  (* 加法结合律 *)
  add_assoc  : forall x y z, r_eq (r_add (r_add x y) z) (r_add x (r_add y z));
  (* 加法交换律 *)
  add_comm   : forall x y, r_eq (r_add x y) (r_add y x);
  (* 左零元 *)
  add_zero_l : forall x, r_eq (r_add r_zero x) x;
  (* 右零元 *)
  add_zero_r : forall x, r_eq (r_add x r_zero) x;
  (* 左负元 *)
  add_neg_l  : forall x, r_eq (r_add (r_neg x) x) r_zero;
  (* 右负元 *)
  add_neg_r  : forall x, r_eq (r_add x (r_neg x)) r_zero;

  (* 乘法结合律 *)
  mul_assoc  : forall x y z, r_eq (r_mul (r_mul x y) z) (r_mul x (r_mul y z));
  (* 左单位元 *)
  mul_one_l  : forall x, r_eq (r_mul r_one x) x;
  (* 右单位元 *)
  mul_one_r  : forall x, r_eq (r_mul x r_one) x;

  (* 左分配律 *)
  left_distrib  : forall x y z, r_eq (r_mul x (r_add y z)) (r_add (r_mul x y) (r_mul x z));
  (* 右分配律 *)
  right_distrib : forall x y z, r_eq (r_mul (r_add x y) z) (r_add (r_mul x z) (r_mul y z));

  (* 等价关系 *)
  r_reflexive  : Reflexive r_eq;
  r_symmetric  : Symmetric r_eq;
  r_transitive : Transitive r_eq;

  (* 运算的兼容性 *)
  r_add_proper : Proper (r_eq ==> r_eq ==> r_eq) r_add;
  r_mul_proper : Proper (r_eq ==> r_eq ==> r_eq) r_mul;
  r_neg_proper : Proper (r_eq ==> r_eq) r_neg
}.

(* 域结构类定义（继承环） *)
Class Field (F : Type) := {
  #[global] field_ring :: Ring F;

  (* 乘法交换律 *)
  field_mul_comm : forall x y, r_eq (r_mul x y) (r_mul y x);
  (* 1 ≠ 0 *)
  field_one_neq_zero : ~ r_eq r_one r_zero;

  (* 乘法逆元存在性（返回逆元及其左右逆等式）*)
  field_inv : forall x, ~ r_eq x r_zero -> { y : F | r_eq (r_mul x y) r_one };

  (* 左逆（由交换律自动成立，此处显式给出）*)
  field_inv_l : forall x (H : ~ r_eq x r_zero),
                let (y, _) := field_inv x H in r_eq (r_mul y x) r_one;
  (* 右逆 *)
  field_inv_r : forall x (H : ~ r_eq x r_zero),
                let (y, _) := field_inv x H in r_eq (r_mul x y) r_one
}.

(* --- 环的基本性质 [补齐 2026-08-16] --- *)
Section RingBasics.
  Context {R : Type} `{RR : Ring R}.
  Local Notation "x == y" := (r_eq x y) (at level 70).
  Local Notation "x + y" := (r_add x y).
  Local Notation "x * y" := (r_mul x y).
  Local Notation "0" := r_zero.
  Local Notation "1" := r_one.
  Local Notation "- x" := (r_neg x).

  Existing Instances r_reflexive r_symmetric r_transitive r_add_proper r_mul_proper r_neg_proper.

  (* 零吸收律：0·x = 0 *)
  Lemma r_zero_absorb_l : forall x, 0 * x == 0.
  Proof.
    intro x.
    assert (H : 0 * x == (0 * x) + (0 * x)).
    { transitivity ((0 + 0) * x).
      - apply r_mul_proper; [apply r_symmetric; apply add_zero_l | reflexivity].
      - apply right_distrib. }
    assert (H1 : (0 * x) + (- (0 * x)) == ((0 * x) + (0 * x)) + (- (0 * x))).
    { apply r_add_proper; [exact H | reflexivity]. }
    rewrite add_neg_r in H1.
    rewrite add_assoc in H1.
    rewrite add_neg_r in H1.
    rewrite add_zero_r in H1.
    symmetry.
    exact H1.
  Qed.

  (* 零吸收律右：x·0 = 0 *)
  Lemma r_zero_absorb_r : forall x, x * 0 == 0.
  Proof.
    intro x.
    assert (H : x * 0 == (x * 0) + (x * 0)).
    { transitivity (x * (0 + 0)).
      - apply r_mul_proper; [reflexivity | apply r_symmetric; apply add_zero_r].
      - apply left_distrib. }
    assert (H1 : (x * 0) + (- (x * 0)) == ((x * 0) + (x * 0)) + (- (x * 0))).
    { apply r_add_proper; [exact H | reflexivity]. }
    rewrite add_neg_r in H1.
    rewrite add_assoc in H1.
    rewrite add_neg_r in H1.
    rewrite add_zero_r in H1.
    symmetry.
    exact H1.
  Qed.

  (* 负元唯一性：若 x + y == 0 则 y == -x *)
  Lemma r_neg_unique : forall x y, x + y == 0 -> y == - x.
  Proof.
    intros x y Hxy.
    rewrite <- (add_zero_l y).
    rewrite <- (add_neg_l x).
    rewrite add_assoc.
    rewrite Hxy.
    rewrite add_zero_r.
    reflexivity.
  Qed.

  (* 负负得正 *)
  Lemma r_neg_neg : forall x, - (- x) == x.
  Proof.
    intro x.
    apply r_symmetric.
    apply r_neg_unique.
    apply add_neg_l.
  Qed.
End RingBasics.

(* --- 域的基本性质 [补齐 2026-08-16] --- *)
Section FieldBasics.
  Context {F : Type} `{FF : Field F}.
  Local Notation "x == y" := (r_eq x y) (at level 70).
  Local Notation "x + y" := (r_add x y).
  Local Notation "x * y" := (r_mul x y).
  Local Notation "0" := r_zero.
  Local Notation "1" := r_one.
  Local Notation "- x" := (r_neg x).

  Existing Instances r_reflexive r_symmetric r_transitive r_add_proper r_mul_proper r_neg_proper.

  (* 乘法逆元唯一性：若 x·y == 1 且 x ≠ 0，则 y == x⁻¹ *)
  Lemma field_inv_unique : forall x (H : ~ x == 0) y,
    x * y == 1 -> y == proj1_sig (field_inv x H).
  Proof.
    intros x H y Hxy.
    destruct (field_inv x H) as [z Hz].
    assert (Hzx : z * x == 1).
    { rewrite (field_mul_comm z x). exact Hz. }
    rewrite <- (mul_one_l y).
    rewrite <- Hzx.
    rewrite mul_assoc.
    rewrite Hxy.
    rewrite mul_one_r.
    reflexivity.
  Qed.

  (* 1 ≠ 0 的对称形式：0 ≠ 1 *)
  Lemma field_zero_neq_one : ~ 0 == 1.
  Proof.
    intro H.
    apply field_one_neq_zero.
    symmetry.
    exact H.
  Qed.

  (* 非零元的逆元非零 *)
  Lemma field_inv_nonzero : forall x (H : ~ x == 0),
    ~ proj1_sig (field_inv x H) == 0.
  Proof.
    intros x H.
    destruct (field_inv x H) as [z Hz].
    intro Hz0.
    apply field_one_neq_zero.
    rewrite <- Hz.
    rewrite Hz0.
    apply r_zero_absorb_r.
  Qed.
End FieldBasics.

End RingFieldTheory.

(* 2.3 代数整数 *)
Module AlgebraicIntegers.

Require Import Stdlib.Lists.List.
Import RingFieldTheory.
Import ListNotations.

Require Import Stdlib.Lists.List.

Local Close Scope R_scope.
Local Close Scope complex_scope.
Local Close Scope string_scope.

(* 多项式求值（给定系数列表和自变量 x，从常数项到最高次计算）*)
Fixpoint eval_poly {R : Type} `{Ring R} (coeffs : list R) (x : R) : R :=
  match coeffs with
  | nil => r_zero
  | c :: cs => r_add c (r_mul x (eval_poly cs x))
  end.

(* 自然数到环的嵌入（将自然数 n 映射为环中单位元累加）*)
Fixpoint nat_to_ring {R : Type} `{Ring R} (n : nat) : R :=
  match n with
  | O => r_zero
  | S m => r_add r_one (nat_to_ring m)
  end.

(* 代数整数的记录定义 *)
Record AlgebraicInteger (K : Type) {F : Field K} : Type := {
  element : K;                                    (* 代数整数元素 *)

  (* 最小多项式系数列表（从常数项到最高次）*)
  minimal_polynomial : list K;

  (* 多项式非空（至少有一个系数）*)
  poly_nonempty : ~ (@eq (list K) minimal_polynomial nil);

  (* 首一性：最高次系数等于环中单位元（翻转列表后取第一个元素）*)
  poly_monic : @List.hd K (@r_one K (F.(field_ring))) (List.rev minimal_polynomial) =
               @r_one K (F.(field_ring));

  (* 所有系数都是整数（即与某个自然数嵌入相等）*)
  coeffs_integer : forall (c : K),
                     @List.In K c minimal_polynomial ->
                     exists n : nat,
                       @r_eq K (F.(field_ring)) c (@nat_to_ring K (F.(field_ring)) n);

  (* 元素是多项式的根（代入后等于零）*)
  is_root : @r_eq K (F.(field_ring))
              (@eval_poly K (F.(field_ring)) minimal_polynomial element)
              (@r_zero K (F.(field_ring)))
}.

(* 整数环（定义为所有代数整数的子集）*)
Definition RingOfIntegers (K : Type) {F : Field K} : Type :=
  { ai : AlgebraicInteger K | True }.

End AlgebraicIntegers.
