(* 拆分自 Riemann_Hypothesis_Proof_Framework.v（复分析证明库 v6.0）*)
(* 库: ca_base  原文行区间: 1-292  机械拆分，未改动内容 *)

(* 
   复分析（Complex Analysis）证明库 - 完整实现版
   Riemann_Hypothesis_Proof_Framework.v
   Version: 6.0
   Description: 复分析（Complex Analysis）证明库
                Riemann Hypothesis Proof Framework based on Infinite-Dimensional Prime Geometry
   Author:  [王宝军、夏挽岚、祖光照、周志农、高雪峰]
   Created: [2026.02.08]
   ==================================================== *)

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
  
(* Rolle 定理的标准形式 *)
Theorem Rolle_theorem_standard :
  forall (f : R -> R) (a b : R) (pr : forall x : R, a < x < b -> derivable_pt f x)
         (cont : forall x : R, a <= x <= b -> continuity_pt f x) (H : a < b) (Heq : f a = f b),
  exists (c : R) (P : a < c < b), derive_pt f c (pr c P) = 0.
Proof.
  exact Rolle.
Qed.

Open Scope R_scope.

(* Rolle 定理的简化版本 *)
Theorem Rolle_simple (f : R -> R) (a b : R) 
        (Hlt : a < b)
        (Hcont : forall x, a <= x <= b -> continuity_pt f x)
        (Hder : forall x, a < x < b -> derivable_pt f x)
        (Heq : f a = f b) :
  exists c : R, exists P : a < c < b, derive_pt f c (Hder c P) = 0.
Proof.
  pose proof (Rolle f a b Hder Hcont Hlt Heq) as [c [Hc Hderiv]].
  exists c, Hc.
  exact Hderiv.
Qed.

(* 针对辅助函数 h 在区间 [0,x] 上应用 Rolle 定理 *)
Lemma rolle_for_h (x : R) (Hx_pos : 0 < x) :
  let A := exp x - (1 + x + x^2/2) in
  let h := fun t : R => exp t - (1 + t + t^2/2) - A * (t/x)^3 in
  forall (Hcont : forall t, 0 <= t <= x -> continuity_pt h t)
         (Hder : forall t, 0 < t < x -> derivable_pt h t)
         (Heq : h 0 = h x),
  exists ξ, 0 < ξ < x /\ 
  (exists P : 0 < ξ < x, derive_pt h ξ (Hder ξ P) = 0).
Proof.
  intros A h Hcont Hder Heq.
  destruct (Rolle_simple h 0 x Hx_pos Hcont Hder Heq) as [c [P Hderiv_zero]].
  exists c.
  split; [exact P|].
  exists P.
  exact Hderiv_zero.
Qed.

(* ====================================================
   第0章：设计原则与架构声明
   ==================================================== *)
  
(* 设计原则1：分层抽象架构 *)
(* 
   层级结构：
   Level 0: 基础数学结构 (Basic Mathematical Structures)
   Level 1: 代数结构 (Algebraic Structures)
   Level 2: 几何结构 (Geometric Structures)
   Level 3: 分析结构 (Analytic Structures)
   Level 4: 质数理论 (Prime Theory)
   Level 5: ζ函数与黎曼猜想 (Zeta Function & Riemann Hypothesis)
*)
(* 设计原则2：有限逼近无限 —— 公理化版本已移除（原 Axiom FiniteApproximation 定义删除，
   构造性版本 FiniteApproximation_constructive 见下，Qed，全库无自定义公理） *)
  
(* 设计原则2：有限逼近无限 *)
Require Import Stdlib.Logic.IndefiniteDescription.
  
(* 有限逼近的构造性版本 *)
Lemma FiniteApproximation_constructive : forall (P : nat -> Prop), 
  (forall n : nat, exists m : nat, (m >= n)%nat /\ P m) -> 
  (exists f : nat -> nat, forall n : nat, P (f n) /\ (f n >= n)%nat).
Proof.
  intros P H.
  (* 使用选择公理构造函数f *)
  exists (fun n => proj1_sig (constructive_indefinite_description _ (H n))).
  intro n.
  destruct (constructive_indefinite_description _ (H n)) as [m [Hge Hp]].
  split; auto.
Qed.

(* 有限逼近的定义（构造性） *)
Definition FiniteApproximation := FiniteApproximation_constructive.

(* [清理] 已移除未使用的公理 ConstructiveChoice（全库 0 处使用，且该命题在经典逻辑下可证） *)

(* 模块定义记录类型 *)
Record ModuleDefinition : Type := {
  module_name : string;
  module_axioms : list Prop;
  module_theorems : list Prop;
  module_verified : bool
}.

(* 依赖关系图类型 *)
Definition DependencyGraph := list (string * list string).
  
(* ====================================================
   第1章：基础数学结构 (Level 0)
   ==================================================== *)
  
(* 1.1 精确定义的复数系统 *)
(* ============================================================
   [构造性轨道 S2-20260818] sqrt 引理构造性替代
   stdlib 的 sqrt_lt_R0（正性）与 sqrt_le_1（实为单调性）证明携带 classic；
   以下 _c 版本以 Req_dec / Rle_dec（框架级可判定）重证，免 classic。
   ============================================================ *)

Lemma Rpos_of_nonneg_neq : forall a : R, 0 <= a -> a <> 0 -> 0 < a.
Proof.
  intros a H0 Hne.
  apply Rnot_le_lt. intros Hle.
  apply Hne. apply Rle_antisym; [exact Hle | exact H0].
Qed.

Lemma sqrt_lt_R0_c : forall x : R, 0 < x -> 0 < sqrt x.
Proof.
  intros x Hx.
  assert (Hge : 0 <= sqrt x) by apply sqrt_pos.
  destruct (Req_dec (sqrt x) 0) as [H0 | Hne].
  - exfalso.
    assert (Hx0 : 0 <= x) by (apply Rlt_le; exact Hx).
    pose proof (sqrt_sqrt x Hx0) as Hs.
    rewrite H0 in Hs. simpl in Hs.
    lra.
  - apply Rpos_of_nonneg_neq; [exact Hge | exact Hne].
Qed.

Lemma sqrt_le_1_c : forall x y : R, 0 <= x -> 0 <= y -> x <= y -> sqrt x <= sqrt y.
Proof.
  intros x y Hx Hy Hxy.
  destruct (Rle_dec (sqrt x) (sqrt y)) as [Hle | Hn]; [exact Hle |].
  exfalso.
  assert (Hyy : sqrt y * sqrt y = y) by exact (sqrt_sqrt y Hy).
  assert (Hxx : sqrt x * sqrt x = x) by exact (sqrt_sqrt x Hx).
  assert (Hy0 : 0 <= sqrt y) by apply sqrt_pos.
  assert (Hx0 : 0 <= sqrt x) by apply sqrt_pos.
  destruct (Req_dec (sqrt y) 0) as [Hy0z | Hyne].
  - (* y = 0 情形：x 亦为 0，两根相等与 Hn 矛盾 *)
    assert (Hy_is_0 : y = 0) by (rewrite <- Hyy; rewrite Hy0z; ring).
    rewrite Hy_is_0 in Hxy.
    assert (Hx_is_0 : x = 0) by (apply Rle_antisym; [exact Hxy | exact Hx]).
    rewrite Hx_is_0 in Hn.
    rewrite Hy_is_0 in Hn.
    pose proof Hxx as Hxx2.
    rewrite Hx_is_0 in Hxx2.
    destruct (Rmult_integral (sqrt 0) (sqrt 0) Hxx2) as [Hz | Hz];
      apply Hn; rewrite Hz; apply Rle_refl.
  - (* 两根皆正：严格单调链 y < x 与 Hxy 矛盾 *)
    assert (Hyp : 0 < sqrt y) by (apply Rpos_of_nonneg_neq; [exact Hy0 | exact Hyne]).
    assert (Hxp : 0 < sqrt x).
    { apply Rpos_of_nonneg_neq; [exact Hx0 |].
      intros Hxz. apply Hn. rewrite Hxz. exact Hy0. }
    assert (Hlt : sqrt y < sqrt x) by (apply Rnot_le_lt; exact Hn).
    assert (Hchain : sqrt y * sqrt y < sqrt x * sqrt x).
    { apply Rlt_trans with (sqrt x * sqrt y).
      - apply Rmult_lt_compat_r; [exact Hyp | exact Hlt].
      - apply Rmult_lt_compat_l; [exact Hxp | exact Hlt]. }
    rewrite Hyy in Hchain. rewrite Hxx in Hchain.
    lra.
Qed.

Module ComplexNumbers.

Require Import Stdlib.micromega.Lra.
Require Import Stdlib.Reals.RIneq.
Require Import Stdlib.Reals.Reals.
Require Import Stdlib.Reals.Rtrigo1.
Require Import Stdlib.Reals.Rpower.
Open Scope R_scope.

(* 复数记录类型定义 *)
Record Complex : Type := {
  re : R;
  im : R
}.

Declare Scope complex_scope.
Notation "x '+i' y" := {| re := x; im := y |}
  (at level 40, no associativity) : complex_scope.

Delimit Scope complex_scope with C.
Bind Scope complex_scope with Complex.
Open Scope complex_scope.

(* 复数常量定义 *)
Definition C0 : Complex := 0 +i 0.
Definition C1 : Complex := 1 +i 0.
Definition CI : Complex := 0 +i 1.

(* 复数近似相等定义 *)
Definition Capprox (z1 z2 : Complex) (ε : R) : Prop :=
  Rabs (re z1 - re z2) < ε /\ Rabs (im z1 - im z2) < ε.

(* 复数精确相等定义 *)
Definition Ceq (z1 z2 : Complex) : Prop :=
  re z1 = re z2 /\ im z1 = im z2.

(* 复数加法定义 *)
Definition Cadd (z1 z2 : Complex) : Complex :=
  (re z1 + re z2) +i (im z1 + im z2).

(* 复数减法定义 *)
Definition Csub (z1 z2 : Complex) : Complex :=
  (re z1 - re z2) +i (im z1 - im z2).

(* 复数乘法定义 *)
Definition Cmul (z1 z2 : Complex) : Complex :=
  (re z1 * re z2 - im z1 * im z2) +i (re z1 * im z2 + im z1 * re z2).

(* 复数共轭定义 *)
Definition Cconj (z : Complex) : Complex :=
  (re z) +i (- im z).

(* 复数模平方定义（使用 Rsqr） *)
Definition Cnorm_sq (z : Complex) : R :=
  Rsqr (re z) + Rsqr (im z).

(* 复数模长定义 *)
Definition Cnorm (z : Complex) : R :=
  sqrt (Cnorm_sq z).

(* 复数逆元定义（需要模平方非零证明） *)
Definition Cinv (z : Complex) (H : Cnorm_sq z <> 0) : Complex :=
  let norm_sq := Cnorm_sq z in
  ((re z) / norm_sq) +i (- (im z) / norm_sq).

(* 复数除法定义（需要分母模平方非零证明） *)
Definition Cdiv (z1 z2 : Complex) (H : Cnorm_sq z2 <> 0) : Complex :=
  Cmul z1 (Cinv z2 H).

(* 复数指数函数定义 *)
Definition Cexp (z : Complex) : Complex :=
  let r := exp (re z) in
  (r * cos (im z)) +i (r * sin (im z)).

(* 辅助 atan2 函数定义（用于复对数） *)
Definition atan2 (y x : R) : R :=
  if Req_EM_T x 0 then
    if Rlt_dec y 0 then -PI/2 else PI/2
  else
    let a := atan (y / x) in
    if Rlt_dec x 0 then
      if Rlt_dec y 0 then a - PI else a + PI
    else
      a.

(* 复对数定义（需要非零证明） *)
Definition Clog (z : Complex) (H : z <> C0) : Complex :=
  (ln (Cnorm z)) +i (atan2 (im z) (re z)).

(* 复数自然数幂定义（递归） *)
Fixpoint Cpow (z : Complex) (n : nat) : Complex :=
  match n with
  | O => C1
  | S m => Cmul z (Cpow z m)
  end.

(* 实数 2 大于 0 的辅助引理 *)
Lemma Rlt_0_2 : (0 : R) < 2. Proof. lra. Qed.

(* 计算 0+2i 的模平方为 4 的引理 *)
Lemma Cnorm_sq_two_i_lemma : Cnorm_sq (0 +i 2) = 4.
Proof.
  unfold Cnorm_sq, Rsqr; simpl.
  field.
Qed.

(* 复数正弦函数定义 *)
Definition Csin (z : Complex) : Complex :=
  let w := CI in
  let e1 := Cexp (Cmul w z) in
  let minus_w := (- re w) +i (- im w) in
  let e2 := Cexp (Cmul minus_w z) in
  let two_i := 0 +i 2 in
  Cdiv (Csub e1 e2) two_i
    (fun (H : Cnorm_sq two_i = 0) =>
      let Hnorm := Cnorm_sq_two_i_lemma in
      let H4 : 4 = 0 := eq_trans (eq_sym Hnorm) H in
      let H2 : 0 < 2 := Rlt_0_2 in
      let H4pos : 0 < 4 := Rmult_lt_0_compat 2 2 H2 H2 in
      Rlt_not_eq 0 4 H4pos (eq_sym H4)).

(* 复数运算符号定义 *)
Infix "+c" := Cadd (at level 50, left associativity) : complex_scope.
Infix "-c" := Csub (at level 50, left associativity) : complex_scope.
Infix "*c" := Cmul (at level 40, left associativity) : complex_scope.
Notation "-c z" := (Csub C0 z) (at level 35) : complex_scope.
Notation "z ⁻¹" := (Cinv z _) (at level 35) : complex_scope.
Notation "z /c w" := (Cdiv z w _) (at level 40, left associativity) : complex_scope.
Notation "∥ z ∥" := (Cnorm z) (at level 35) : complex_scope.
Notation "z ^ n" := (Cpow z n) (at level 30, right associativity) : complex_scope.

(* 复数序列类型定义 *)
Definition ComplexSequence := nat -> Complex.

(* 复数序列极限定义 *)
Definition Cseq_limit (f : ComplexSequence) (l : Complex) : Prop :=
  forall ε : R, ε > 0 -> exists N : nat, forall n : nat,
    (n >= N)%nat -> Capprox (f n) l ε.

(* 复数序列柯西列定义 *)
Definition Cseq_cauchy (f : ComplexSequence) : Prop :=
  forall ε : R, ε > 0 -> exists N : nat, forall n m : nat,
    (n >= N)%nat -> (m >= N)%nat -> Capprox (f n) (f m) ε.

(* ============================================================
   复数域性质 [补齐 2026-08-15]：实虚部公式、加法/乘法运算律、
   共轭、模（含三角不等式）、逆元、指数加法公式。
   此前 ComplexNumbers 只有运算定义、没有性质定理；本区块使其
   成为真正可复用的复数基础库。
   ============================================================ *)

(* --- 实部/虚部线性公式 --- *)
Lemma re_Cadd : forall z w, re (z +c w) = re z + re w.
Proof. intros [a b] [c d]; simpl; ring. Qed.
Lemma im_Cadd : forall z w, im (z +c w) = im z + im w.
Proof. intros [a b] [c d]; simpl; ring. Qed.
Lemma re_Csub : forall z w, re (z -c w) = re z - re w.
Proof. intros [a b] [c d]; simpl; ring. Qed.
Lemma im_Csub : forall z w, im (z -c w) = im z - im w.
Proof. intros [a b] [c d]; simpl; ring. Qed.
Lemma re_Cmul : forall z w, re (z *c w) = re z * re w - im z * im w.
Proof. intros [a b] [c d]; simpl; ring. Qed.
Lemma im_Cmul : forall z w, im (z *c w) = re z * im w + im z * re w.
Proof. intros [a b] [c d]; simpl; ring. Qed.
Lemma re_Cneg : forall z, re (Csub C0 z) = - re z.
Proof. intros [a b]; simpl; ring. Qed.
Lemma im_Cneg : forall z, im (Csub C0 z) = - im z.
Proof. intros [a b]; simpl; ring. Qed.

(* --- 加法群 --- *)
Lemma Cadd_comm : forall z w, z +c w = w +c z.
Proof. intros [a b] [c d]; unfold Cadd, Csub, Cmul, Cconj, C0, C1; simpl; f_equal; ring. Qed.
Lemma Cadd_assoc : forall z w u, (z +c w) +c u = z +c (w +c u).
Proof. intros [a b] [c d] [e f]; unfold Cadd, Csub, Cmul, Cconj, C0, C1; simpl; f_equal; ring. Qed.
Lemma Cadd_0_l : forall z, C0 +c z = z.
Proof. intros [a b]; unfold Cadd, Csub, Cmul, Cconj, C0, C1; simpl; f_equal; ring. Qed.
Lemma Cadd_0_r : forall z, z +c C0 = z.
Proof. intros [a b]; unfold Cadd, Csub, Cmul, Cconj, C0, C1; simpl; f_equal; ring. Qed.
Lemma Cadd_opp_r : forall z, z +c (Csub C0 z) = C0.
Proof. intros [a b]; unfold Cadd, Csub, Cmul, Cconj, C0, C1; simpl; f_equal; ring. Qed.

(* --- 乘法 --- *)
Lemma Cmul_comm : forall z w, z *c w = w *c z.
Proof. intros [a b] [c d]; unfold Cadd, Csub, Cmul, Cconj, C0, C1; simpl; f_equal; ring. Qed.
Lemma Cmul_assoc : forall z w u, (z *c w) *c u = z *c (w *c u).
Proof. intros [a b] [c d] [e f]; unfold Cadd, Csub, Cmul, Cconj, C0, C1; simpl; f_equal; ring. Qed.
Lemma Cmul_1_l : forall z, C1 *c z = z.
Proof. intros [a b]; unfold Cadd, Csub, Cmul, Cconj, C0, C1; simpl; f_equal; ring. Qed.
Lemma Cmul_1_r : forall z, z *c C1 = z.
Proof. intros [a b]; unfold Cadd, Csub, Cmul, Cconj, C0, C1; simpl; f_equal; ring. Qed.
Lemma Cmul_0_l : forall z, C0 *c z = C0.
Proof. intros [a b]; unfold Cadd, Csub, Cmul, Cconj, C0, C1; simpl; f_equal; ring. Qed.
Lemma Cmul_0_r : forall z, z *c C0 = C0.
Proof. intros [a b]; unfold Cadd, Csub, Cmul, Cconj, C0, C1; simpl; f_equal; ring. Qed.
Lemma Cmul_add_distr_l : forall z w u, z *c (w +c u) = z *c w +c z *c u.
Proof. intros [a b] [c d] [e f]; unfold Cadd, Csub, Cmul, Cconj, C0, C1; simpl; f_equal; ring. Qed.
Lemma Cmul_add_distr_r : forall z w u, (z +c w) *c u = z *c u +c w *c u.
Proof. intros [a b] [c d] [e f]; unfold Cadd, Csub, Cmul, Cconj, C0, C1; simpl; f_equal; ring. Qed.

(* --- 共轭 --- *)
Lemma Cconj_conj : forall z, Cconj (Cconj z) = z.
Proof. intros [a b]; unfold Cadd, Csub, Cmul, Cconj, C0, C1; simpl; f_equal; ring. Qed.
Lemma Cconj_add : forall z w, Cconj (z +c w) = Cconj z +c Cconj w.
Proof. intros [a b] [c d]; unfold Cadd, Csub, Cmul, Cconj, C0, C1; simpl; f_equal; ring. Qed.
Lemma Cconj_mul : forall z w, Cconj (z *c w) = Cconj z *c Cconj w.
Proof. intros [a b] [c d]; unfold Cadd, Csub, Cmul, Cconj, C0, C1; simpl; f_equal; ring. Qed.
Lemma re_Cconj : forall z, re (Cconj z) = re z.
Proof. intros [a b]; simpl; ring. Qed.
Lemma im_Cconj : forall z, im (Cconj z) = - im z.
Proof. intros [a b]; simpl; ring. Qed.

(* --- 辅助：实数平方和为 0 推两数皆 0 --- *)
Lemma Rsqr_plus_sq_zero : forall a b : R, a² + b² = 0 -> a = 0 /\ b = 0.
Proof.
  intros a b H.
  assert (Ha2_le : a² <= a² + b²) by (pattern (a²) at 1; rewrite <- (Rplus_0_r (a²)); apply Rplus_le_compat_l; apply Rle_0_sqr).
  assert (Hb2_le : b² <= a² + b²) by (pattern (b²) at 1; rewrite <- (Rplus_0_r (b²)); rewrite (Rplus_comm (a²) (b²)); apply Rplus_le_compat_l; apply Rle_0_sqr).
  assert (Ha2_0 : a² = 0) by (apply Rle_antisym; [apply Rle_trans with (a² + b²); [exact Ha2_le | rewrite H; lra] | apply Rle_0_sqr]).
  assert (Hb2_0 : b² = 0) by (apply Rle_antisym; [apply Rle_trans with (a² + b²); [exact Hb2_le | rewrite H; lra] | apply Rle_0_sqr]).
  split; apply Rsqr_eq_0; assumption.
Qed.

(* 辅助：实数柯西-施瓦茨（二维） *)
Lemma CauchySchwarz_R2 : forall a b c d : R, (a * c + b * d)² <= (a² + b²) * (c² + d²).
Proof.
  intros a b c d.
  assert (H : (a * c + b * d)² + (a * d - b * c)² = (a² + b²) * (c² + d²)) by (unfold Rsqr; ring).
  rewrite <- H.
  pattern ((a * c + b * d)²) at 1.
  rewrite <- (Rplus_0_r ((a * c + b * d)²)).
  apply Rplus_le_compat_l; apply Rle_0_sqr.
Qed.

(* --- 模 --- *)
Lemma Cnorm_sq_zero : Cnorm_sq C0 = 0.
Proof. unfold Cnorm_sq, C0; simpl; unfold Rsqr; ring. Qed.
Lemma Cnorm_sq_zero_iff : forall z, Cnorm_sq z = 0 <-> z = C0.
Proof.
  intros [a b]; split.
  - intro H. unfold Cnorm_sq in H; simpl in H.
    destruct (Rsqr_plus_sq_zero a b H) as [Ha Hb].
    subst; reflexivity.
  - intro H; injection H; intros; subst.
    unfold Cnorm_sq; simpl; unfold Rsqr; ring.
Qed.
Lemma Cnorm_sq_pos_iff : forall z, z <> C0 -> 0 < Cnorm_sq z.
Proof.
  intros [a b] H.
  unfold Cnorm_sq; simpl.
  apply Rnot_le_gt; intro Hle.
  assert (Hn : a² + b² = 0) by (apply Rle_antisym; [exact Hle | apply Rplus_le_le_0_compat; apply Rle_0_sqr]).
  destruct (Rsqr_plus_sq_zero a b Hn) as [Ha Hb].
  apply H; subst; reflexivity.
Qed.
Lemma Cnorm_sq_mul : forall z w, Cnorm_sq (z *c w) = Cnorm_sq z * Cnorm_sq w.
Proof. intros [a b] [c d]; unfold Cnorm_sq, Cmul; simpl; unfold Rsqr; ring. Qed.
Lemma Cnorm_mul : forall z w, Cnorm (z *c w) = Cnorm z * Cnorm w.
Proof.
  intros z w.
  unfold Cnorm.
  rewrite Cnorm_sq_mul.
  apply sqrt_mult; apply Rplus_le_le_0_compat; apply Rle_0_sqr.
Qed.
Lemma Cnorm_nonneg : forall z, 0 <= Cnorm z.
Proof. intro z; unfold Cnorm; apply sqrt_pos. Qed.
Lemma Cnorm_pos_lt : forall z, z <> C0 -> 0 < Cnorm z.
Proof.
  intros z Hz.
  unfold Cnorm.
  apply sqrt_lt_R0_c.
  apply Cnorm_sq_pos_iff; exact Hz.
Qed.
Lemma Cnorm_zero_iff : forall z, Cnorm z = 0 <-> z = C0.
Proof.
  intros z; split.
  - intro H; apply Cnorm_sq_zero_iff; unfold Cnorm in H.
    apply sqrt_eq_0; [apply Rplus_le_le_0_compat; apply Rle_0_sqr | exact H].
  - intro H; rewrite H; unfold Cnorm; rewrite Cnorm_sq_zero; apply sqrt_0.
Qed.

(* 模的三角不等式：|z + w| <= |z| + |w| *)
Lemma Cnorm_triangle : forall z w, Cnorm (z +c w) <= Cnorm z + Cnorm w.
Proof.
  intros [a b] [c d].
  unfold Cnorm, Cnorm_sq; simpl.
  assert (HA : 0 <= Rsqr a + Rsqr b) by (apply Rplus_le_le_0_compat; apply Rle_0_sqr).
  assert (HB : 0 <= Rsqr c + Rsqr d) by (apply Rplus_le_le_0_compat; apply Rle_0_sqr).
  assert (HC : 0 <= Rsqr (a + c) + Rsqr (b + d)) by (apply Rplus_le_le_0_compat; apply Rle_0_sqr).
  assert (Hcs : (a * c + b * d)² <= (Rsqr a + Rsqr b) * (Rsqr c + Rsqr d)).
  { unfold Rsqr; exact (CauchySchwarz_R2 a b c d). }
  assert (Hcs_abs : Rabs (a * c + b * d) <= sqrt ((Rsqr a + Rsqr b) * (Rsqr c + Rsqr d))).
  {
    apply Rle_trans with (sqrt (Rsqr (a * c + b * d))).
    - rewrite sqrt_Rsqr_abs; apply Rle_refl.
    - apply sqrt_le_1_c; [apply Rle_0_sqr | apply Rmult_le_pos; [exact HA | exact HB] |].
      unfold Rsqr; exact Hcs.
  }
  assert (Hs : Rsqr (a + c) + Rsqr (b + d) <=
               (Rsqr a + Rsqr b) + (Rsqr c + Rsqr d) + 2 * sqrt ((Rsqr a + Rsqr b) * (Rsqr c + Rsqr d))).
  {
    assert (Hexp : Rsqr (a + c) + Rsqr (b + d) = (Rsqr a + Rsqr b) + (Rsqr c + Rsqr d) + 2 * (a * c + b * d)).
    { unfold Rsqr; ring. }
    rewrite Hexp.
    assert (Hstep : 2 * (a * c + b * d) <= 2 * sqrt ((Rsqr a + Rsqr b) * (Rsqr c + Rsqr d))).
    { apply Rle_trans with (2 * Rabs (a * c + b * d)).
      - apply Rmult_le_compat_l; [lra | apply Rle_abs].
      - apply Rmult_le_compat_l; [lra | exact Hcs_abs]. }
    lra.
  }
  rewrite (sqrt_mult (Rsqr a + Rsqr b) (Rsqr c + Rsqr d) HA HB) in Hs.
  apply Rsqr_incr_0.
  - rewrite (Rsqr_sqrt (Rsqr (a + c) + Rsqr (b + d)) HC).
    rewrite (Rsqr_plus (sqrt (Rsqr a + Rsqr b)) (sqrt (Rsqr c + Rsqr d))).
    rewrite (Rsqr_sqrt (Rsqr a + Rsqr b) HA).
    rewrite (Rsqr_sqrt (Rsqr c + Rsqr d) HB).
    rewrite Rmult_assoc.
    exact Hs.
  - apply sqrt_pos.
  - apply Rplus_le_le_0_compat; apply sqrt_pos.
Qed.

(* --- 逆元 --- *)
Lemma Cmul_inv_l : forall z (H : Cnorm_sq z <> 0), z *c Cinv z H = C1.
Proof.
  intros [a b] H.
  unfold Cinv, Cnorm_sq, Cmul, C1; simpl in *.
  unfold Rsqr in *.
  f_equal; [field; auto | field; auto].
Qed.
Lemma Cmul_inv_r : forall z (H : Cnorm_sq z <> 0), Cinv z H *c z = C1.
Proof.
  intros z H.
  rewrite Cmul_comm.
  apply Cmul_inv_l.
Qed.

(* --- 指数 --- *)
Lemma Cexp_0 : Cexp C0 = C1.
Proof.
  unfold Cexp, C0, C1; simpl.
  rewrite exp_0, cos_0, sin_0.
  f_equal; ring.
Qed.
Lemma Cexp_add : forall z w, Cexp (z +c w) = Cexp z *c Cexp w.
Proof.
  intros [a b] [c d].
  unfold Cexp, Cadd, Cmul; simpl.
  f_equal.
  - rewrite exp_plus, cos_plus; ring.
  - rewrite exp_plus, sin_plus; ring.
Qed.

(* --- 减法分配律与除法加法（供全纯函数封闭性使用）--- *)
Lemma Csub_self : forall z, Csub z z = C0.
Proof. intros [a b]; unfold Csub, C0; simpl; f_equal; ring. Qed.
Lemma Csub_add : forall a b c d, Csub (a +c b) (c +c d) = Csub a c +c Csub b d.
Proof. intros [a1 a2] [b1 b2] [c1 c2] [d1 d2]; unfold Cadd, Csub; simpl; f_equal; ring. Qed.
Lemma Csub_neg_swap : forall a b, Csub (Csub C0 a) (Csub C0 b) = Csub b a.
Proof. intros [a1 a2] [b1 b2]; unfold Csub, C0; simpl; f_equal; ring. Qed.
Lemma Csub_swap : forall a b, Csub b a = Csub C0 (Csub a b).
Proof. intros [a1 a2] [b1 b2]; unfold Csub, C0; simpl; f_equal; ring. Qed.
Lemma Cmul_neg_l : forall x y, Cmul (Csub C0 x) y = Csub C0 (Cmul x y).
Proof. intros [a b] [c d]; unfold Csub, Cmul, C0; simpl; f_equal; ring. Qed.
Lemma Cdiv_neg : forall x h (H : Cnorm_sq h <> 0), Cdiv (Csub C0 x) h H = Csub C0 (Cdiv x h H).
Proof. intros x h H; unfold Cdiv; rewrite Cmul_neg_l; reflexivity. Qed.
Lemma Cdiv_add : forall x y h (H : Cnorm_sq h <> 0), Cdiv (x +c y) h H = Cdiv x h H +c Cdiv y h H.
Proof. intros x y h H; unfold Cdiv; rewrite Cmul_add_distr_r; reflexivity. Qed.
Lemma Cnorm_0 : Cnorm C0 = 0.
Proof. unfold Cnorm; rewrite Cnorm_sq_zero; apply sqrt_0. Qed.
Lemma Cnorm_sub_swap : forall a b, Cnorm (Csub a b) = Cnorm (Csub b a).
Proof. intros [a1 a2] [b1 b2]; unfold Cnorm, Cnorm_sq, Csub; simpl; f_equal; unfold Rsqr; ring. Qed.

(* --- 乘法对减法分配、除法消去（供全纯函数封闭性与链式法则使用）--- *)
Lemma Cmul_sub_distr_l : forall a b c, a *c (b -c c) = a *c b -c a *c c.
Proof. intros [a1 a2] [b1 b2] [c1 c2]; unfold Csub, Cmul; simpl; f_equal; ring. Qed.
Lemma Cmul_sub_distr_r : forall a b c, (b -c c) *c a = b *c a -c c *c a.
Proof. intros [a1 a2] [b1 b2] [c1 c2]; unfold Csub, Cmul; simpl; f_equal; ring. Qed.
Lemma Csub_mul_mul : forall a b c d, a *c b -c c *c d = a *c (b -c d) +c (a -c c) *c d.
Proof. intros [a1 a2] [b1 b2] [c1 c2] [d1 d2]; unfold Cadd, Csub, Cmul; simpl; f_equal; ring. Qed.
Lemma Csub_mul_mul2 : forall a b c d, a *c b -c c *c d = a *c (b -c c) +c c *c (a -c d).
Proof. intros [a1 a2] [b1 b2] [c1 c2] [d1 d2]; unfold Cadd, Csub, Cmul; simpl; f_equal; ring. Qed.
Lemma Csub_as_add : forall a b, a -c b = a +c (C0 -c b).
Proof. intros [a1 a2] [b1 b2]; unfold Cadd, Csub, C0; simpl; f_equal; ring. Qed.
Lemma Cdiv_scal_l : forall a b h (H : Cnorm_sq h <> 0), Cdiv (a *c b) h H = a *c Cdiv b h H.
Proof. intros a b h H; unfold Cdiv; rewrite Cmul_assoc; reflexivity. Qed.
Lemma Cdiv_zero : forall h (H : Cnorm_sq h <> 0), Cdiv C0 h H = C0.
Proof. intros h H; unfold Cdiv; rewrite Cmul_0_l; reflexivity. Qed.
Lemma Cmul_div_cancel : forall x h (H : Cnorm_sq h <> 0), h *c Cdiv x h H = x.
Proof.
  intros x h H.
  unfold Cdiv.
  rewrite <- Cmul_assoc.
  rewrite (Cmul_comm h x).
  rewrite Cmul_assoc.
  rewrite Cmul_inv_l.
  apply Cmul_1_r.
Qed.
Lemma Cdiv_scal_r : forall a b h (H : Cnorm_sq h <> 0), Cdiv (a *c b) h H = Cdiv a h H *c b.
Proof.
  intros a b h H.
  unfold Cdiv.
  rewrite Cmul_assoc.
  rewrite (Cmul_comm b (Cinv h H)).
  rewrite <- Cmul_assoc.
  reflexivity.
Qed.
Lemma Cdiv_mul_cancel : forall x h (H : Cnorm_sq h <> 0), Cdiv (h *c x) h H = x.
Proof.
  intros x h H.
  unfold Cdiv.
  rewrite (Cmul_comm h x).
  rewrite Cmul_assoc.
  rewrite Cmul_inv_l.
  apply Cmul_1_r.
Qed.
Lemma Csub_add_rev : forall a b, b +c (a -c b) = a.
Proof. intros [a1 a2] [b1 b2]; unfold Cadd, Csub; simpl; f_equal; ring. Qed.
Lemma Csub_0_r : forall z, z -c C0 = z.
Proof. intros [a b]; unfold Csub, C0; simpl; f_equal; ring. Qed.
Lemma Cnorm_neg : forall z, Cnorm (Csub C0 z) = Cnorm z.
Proof.
  intros [a b].
  unfold Cnorm, Cnorm_sq, Csub, C0; simpl.
  f_equal; unfold Rsqr; ring.
Qed.

(* --- 实数辅助：ε/(1+|c|) 缩放界（供数乘封闭性使用）--- *)
Lemma frac_le_1 : forall a : R, 0 <= a -> a / (1 + a) <= 1.
Proof.
  intros a Ha.
  unfold Rdiv.
  rewrite Rmult_comm.
  apply Rle_trans with (/(1 + a) * (1 + a)).
  - apply Rmult_le_compat_l.
    + apply Rlt_le; apply Rinv_0_lt_compat; lra.
    + lra.
  - rewrite Rinv_l; lra.
Qed.
Lemma prod_bound_eps : forall a eps : R, 0 <= a -> 0 < eps -> a * (eps / (1 + a)) <= eps.
Proof.
  intros a eps Ha Heps.
  assert (Hrew : a * (eps / (1 + a)) = (a / (1 + a)) * eps).
  { unfold Rdiv; ring. }
  rewrite Hrew.
  apply Rle_trans with (1 * eps).
  - apply Rmult_le_compat_r; [lra | exact (frac_le_1 a Ha)].
  - lra.
Qed.

(* 混合严格-非严格乘积界：a·c < b·d（a ≤ b 且 c < d，b > 0） *)
Lemma Rmult_le_lt_compat_mix : forall a b c d : R,
  0 <= a -> 0 < b -> 0 <= c -> c < d -> a <= b -> a * c < b * d.
Proof.
  intros a b c d Ha Hb Hc Hcd Hab.
  apply Rle_lt_trans with (b * c).
  - apply Rmult_le_compat_r; [exact Hc | exact Hab].
  - apply Rmult_lt_compat_l; [exact Hb | exact Hcd].
Qed.

End ComplexNumbers.
