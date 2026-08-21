(* 拆分自 Riemann_Hypothesis_Proof_Framework.v（复分析证明库 v6.0）*)
(* 库: ca_complex_foundation  原文行区间: 20322-21084  机械拆分，未改动内容 *)

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

Require Import ca_base ca_algebra ca_primes ca_complex_analysis ca_fourier ca_zeta_scaffold ca_trig ca_gamma ca_taylor ca_zeta_axioms ca_complex_log.

Require Import Stdlib.Logic.IndefiniteDescription.

(* ====================================================
   复数基础模块 (ComplexFoundation)
   包含：复数定义、基本运算、指数、对数、级数及常用性质
   依赖：Coq.Reals, Coq.Logic.ProofIrrelevance
   本模块独立于原框架中的 ComplexNumbers 和 ComplexBasics，可并存使用。
   ==================================================== *)

Require Import Stdlib.Reals.Reals.
Require Import Stdlib.Reals.Rtrigo1.
Require Import Stdlib.Reals.Rpower.
Require Import Stdlib.Reals.Rseries.
Require Import Stdlib.Logic.ProofIrrelevance.
Require Import Stdlib.micromega.Lra.

Local Open Scope R_scope.

Module ComplexFoundation.

Import ComplexLogarithm.

(* 复数类型与基本常数 *)
Record Complex : Type := {
  re : R;
  im : R
}.

Notation "x '+i' y" := {| re := x; im := y |}
  (at level 40, no associativity) : complex_scope.

Delimit Scope complex_scope with C.
Bind Scope complex_scope with Complex.
Open Scope complex_scope.

Definition C0 : Complex := 0 +i 0.
Definition C1 : Complex := 1 +i 0.
Definition CI : Complex := 0 +i 1.

(* 实数嵌入复数 *)
Definition C_of_R (r : R) : Complex := r +i 0.

(* 复数相等 *)
Definition Ceq (z1 z2 : Complex) : Prop :=
  re z1 = re z2 /\ im z1 = im z2.

(* 复数相等判定 *)
Lemma Complex_eq : forall z1 z2,
  re z1 = re z2 -> im z1 = im z2 -> z1 = z2.
Proof.
  intros [re1 im1] [re2 im2] Hre Him; simpl in *.
  subst; reflexivity.
Qed.

(* 复数近似 *)
Definition Capprox (z1 z2 : Complex) (ε : R) : Prop :=
  Rabs (re z1 - re z2) < ε /\ Rabs (im z1 - im z2) < ε.

(* 复数加法 *)
Definition Cadd (z1 z2 : Complex) : Complex :=
  (re z1 + re z2) +i (im z1 + im z2).

(* 复数减法 *)
Definition Csub (z1 z2 : Complex) : Complex :=
  (re z1 - re z2) +i (im z1 - im z2).

(* 复数乘法 *)
Definition Cmul (z1 z2 : Complex) : Complex :=
  (re z1 * re z2 - im z1 * im z2) +i (re z1 * im z2 + im z1 * re z2).

(* 复数共轭 *)
Definition Cconj (z : Complex) : Complex :=
  (re z) +i (- im z).

(* 复数模平方 *)
Definition Cnorm_sq (z : Complex) : R :=
  Rsqr (re z) + Rsqr (im z).

(* 复数模 *)
Definition Cnorm (z : Complex) : R :=
  sqrt (Cnorm_sq z).

(* 复数倒数 *)
Definition Cinv (z : Complex) (H : Cnorm_sq z <> 0) : Complex :=
  let nsq := Cnorm_sq z in
  ((re z) / nsq) +i (- (im z) / nsq).

(* 复数除法 *)
Definition Cdiv (z1 z2 : Complex) (H : Cnorm_sq z2 <> 0) : Complex :=
  Cmul z1 (Cinv z2 H).

(* 复数指数 *)
Definition Cexp (z : Complex) : Complex :=
  let r := exp (re z) in
  (r * cos (im z)) +i (r * sin (im z)).

(* 反正切 atan2 *)
Definition atan2 (y x : R) : R :=
  if Req_EM_T x 0 then
    if Rlt_dec y 0 then -PI/2 else PI/2
  else
    let a := atan (y / x) in
    if Rlt_dec x 0 then
      if Rlt_dec y 0 then a - PI else a + PI
    else
      a.

(* 主支复对数 *)
Definition Clog_principal (z : Complex) (Hz : z <> C0) : Complex :=
  let r := Cnorm z in
  let θ := atan2 (im z) (re z) in
  (ln r) +i θ.

(* 复数自然数幂 *)
Fixpoint Cpow (z : Complex) (n : nat) : Complex :=
  match n with
  | O => C1
  | S m => Cmul z (Cpow z m)
  end.

(* 正实数底复数幂 *)
Definition Cpow_pos_real (n : R) (s : Complex) (Hpos : 0 < n) : Complex :=
  Cexp (Cmul s (C_of_R (ln n))).

(* 复数序列 *)
Definition ComplexSequence := nat -> Complex.

(* 复数序列极限 *)
Definition Cseq_limit (f : ComplexSequence) (l : Complex) : Prop :=
  forall ε : R, ε > 0 -> exists N : nat, forall n : nat,
    (n >= N)%nat -> Capprox (f n) l ε.

(* 复数序列柯西 *)
Definition Cseq_cauchy (f : ComplexSequence) : Prop :=
  forall ε : R, ε > 0 -> exists N : nat, forall n m : nat,
    (n >= N)%nat -> (m >= N)%nat -> Capprox (f n) (f m) ε.

(* 提取实数极限 *)
Definition Rseries_limit (u : nat -> R) (Hcv : {l : R | Un_cv u l}) : R :=
  proj1_sig Hcv.

(* 复数级数 *)
Definition CSeries (f : nat -> Complex)
    (Hcv_re : {l : R | Un_cv (fun n => re (f n)) l})
    (Hcv_im : {l : R | Un_cv (fun n => im (f n)) l}) : Complex :=
  {| re := Rseries_limit _ Hcv_re;
     im := Rseries_limit _ Hcv_im |}.

(* 符号记法 *)
Infix "+c" := Cadd (at level 50, left associativity) : complex_scope.
Infix "-c" := Csub (at level 50, left associativity) : complex_scope.
Infix "*c" := Cmul (at level 40, left associativity) : complex_scope.
Notation "-c z" := (Csub C0 z) (at level 35) : complex_scope.
Notation "z ⁻¹" := (Cinv z _) (at level 35) : complex_scope.
Notation "z /c w" := (Cdiv z w _) (at level 40, left associativity) : complex_scope.
Notation "∥ z ∥" := (Cnorm z) (at level 35) : complex_scope.
Notation "z ^ n" := (Cpow z n) (at level 30, right associativity) : complex_scope.

(* 复数乘法左零元 *)
Lemma Cmul_0_l : forall z, C0 *c z = C0.
Proof.
  intros z; apply Complex_eq; unfold C0, Cmul; destruct z; simpl; ring.
Qed.

(* 复数乘法右零元 *)
Lemma Cmul_0_r : forall z, z *c C0 = C0.
Proof.
  intros z; apply Complex_eq; unfold C0, Cmul; destruct z; simpl; ring.
Qed.

(* 复数加法左单位元 *)
Lemma Cadd_0_l : forall z, C0 +c z = z.
Proof.
  intros z; apply Complex_eq; unfold C0, Cadd; destruct z; simpl; ring.
Qed.

(* 复数加法右单位元 *)
Lemma Cadd_0_r : forall z, z +c C0 = z.
Proof.
  intros z; apply Complex_eq; unfold C0, Cadd; destruct z; simpl; ring.
Qed.

(* 复数加法交换律 *)
Lemma Cadd_comm : forall z1 z2, z1 +c z2 = z2 +c z1.
Proof.
  intros z1 z2; apply Complex_eq; unfold Cadd; simpl; ring.
Qed.

(* 复数加法结合律 *)
Lemma Cadd_assoc : forall z1 z2 z3, (z1 +c z2) +c z3 = z1 +c (z2 +c z3).
Proof.
  intros; apply Complex_eq; unfold Cadd; simpl; ring.
Qed.

(* 复数乘法交换律 *)
Lemma Cmul_comm : forall z1 z2, z1 *c z2 = z2 *c z1.
Proof.
  intros z1 z2; apply Complex_eq; unfold Cmul; simpl; ring.
Qed.

(* 复数乘法结合律 *)
Lemma Cmul_assoc : forall a b c, (a *c b) *c c = a *c (b *c c).
Proof.
  intros; apply Complex_eq; unfold Cmul; simpl; ring.
Qed.

(* 复数乘法左分配律 *)
Lemma Cmul_add_distr_l : forall a b c, a *c (b +c c) = a *c b +c a *c c.
Proof.
  intros; apply Complex_eq; unfold Cadd, Cmul; simpl; ring.
Qed.

(* 复数乘法右分配律 *)
Lemma Cmul_add_distr_r : forall a b c, (a +c b) *c c = a *c c +c b *c c.
Proof.
  intros; apply Complex_eq; unfold Cadd, Cmul; simpl; ring.
Qed.

(* 复数减法与加法的关系 *)
Lemma Csub_add : forall a b, a = b +c (a -c b).
Proof.
  intros; apply Complex_eq; unfold Cadd, Csub; simpl; ring.
Qed.

(* 复数模平方的非负性 *)
Lemma Cnorm_sq_ge_0 : forall z, 0 <= Cnorm_sq z.
Proof.
  intros [x y]; unfold Cnorm_sq; apply Rplus_le_le_0_compat; apply Rle_0_sqr.
Qed.

(* 复数模的非负性 *)
Lemma Cnorm_ge_0 : forall z, 0 <= Cnorm z.
Proof.
  intros z; unfold Cnorm; apply sqrt_pos.
Qed.

(* 非零复数的模平方正性 *)
Lemma Cnorm_sq_pos : forall z, z <> C0 -> 0 < Cnorm_sq z.
Proof.
  intros [x y] Hz.
  unfold Cnorm_sq.
  destruct (Req_EM_T x 0) as [Hx|Hx]; destruct (Req_EM_T y 0) as [Hy|Hy].
  - exfalso; apply Hz; apply Complex_eq; simpl; auto.
  - apply Rplus_le_lt_0_compat; [apply Rle_0_sqr | apply Rlt_0_sqr; exact Hy].
  - apply Rplus_lt_le_0_compat; [apply Rlt_0_sqr; exact Hx | apply Rle_0_sqr].
  - apply Rplus_lt_0_compat; apply Rlt_0_sqr; assumption.
Qed.

(* 非零复数模长正性引理 *)
Lemma Cnorm_pos : forall z, z <> C0 -> 0 < Cnorm z.
Proof.
  intros z Hz.
  unfold Cnorm; apply sqrt_lt_R0_c, Cnorm_sq_pos; assumption.
Qed.

(* 非零复数的模平方非零 *)
Lemma nonzero_norm_sq_nonzero : forall z, z <> C0 -> Cnorm_sq z <> 0.
Proof.
  intros z Hz; apply Rgt_not_eq; apply Cnorm_sq_pos; assumption.
Qed.

(* 模平方乘积公式 *)
Lemma Cnorm_sq_mult : forall z1 z2, Cnorm_sq (z1 *c z2) = Cnorm_sq z1 * Cnorm_sq z2.
Proof.
  intros [a b] [c d]; unfold Cnorm_sq, Cmul; simpl.
  unfold Rsqr; simpl.
  ring.
Qed.

(* 定理：复数模乘法 *)
Theorem Cnorm_mult : forall z1 z2, Cnorm (z1 *c z2) = Cnorm z1 * Cnorm z2.
Proof.
  intros z1 z2.
  unfold Cnorm.
  rewrite Cnorm_sq_mult.
  rewrite sqrt_mult; [| apply Cnorm_sq_ge_0 | apply Cnorm_sq_ge_0].
  reflexivity.
Qed.

(* 复数1的模等于1 *)
Lemma Cnorm_one : Cnorm C1 = 1.
Proof.
  unfold C1, Cnorm, Cnorm_sq; simpl.
  rewrite Rsqr_1, Rsqr_0, Rplus_0_r, sqrt_1; reflexivity.
Qed.

(* 复数逆的模长 *)
Lemma Cnorm_inv : forall z (Hz : z <> C0),
  Cnorm (Cinv z (nonzero_norm_sq_nonzero z Hz)) = / Cnorm z.
Proof.
  intros z Hz.
  set (Hnz := nonzero_norm_sq_nonzero z Hz).
  apply Rmult_eq_reg_l with (Cnorm z).
  - rewrite <- Cnorm_mult.
    assert (Hprod : Cmul z (Cinv z Hnz) = C1).
    {
      destruct z as [x y]; simpl.
      unfold Cinv; simpl.
      set (nsq := Cnorm_sq (x +i y)).
      assert (nsq_neq0 : nsq <> 0) by exact Hnz.
      unfold Cmul; simpl.
      assert (Hnsq_eq : nsq = x * x + y * y).
      { unfold nsq, Cnorm_sq; simpl; unfold Rsqr; ring. }
      apply Complex_eq; simpl.
      - rewrite Hnsq_eq; field; exact nsq_neq0.
      - rewrite Hnsq_eq; field; exact nsq_neq0.
    }
    rewrite Hprod, Cnorm_one.
    assert (Hnz' : Cnorm z <> 0) by (apply Rgt_not_eq, Cnorm_pos; assumption).
    rewrite <- (Rinv_r (Cnorm z) Hnz').
    reflexivity.
  - apply Rgt_not_eq; apply Cnorm_pos; assumption.
Qed.

(* 复指数函数非零 *)
Lemma Cexp_neq_0 : forall w, Cexp w <> C0.
Proof.
  intros w H.
  assert (Hre : re (Cexp w) = 0) by (rewrite H; reflexivity).
  assert (Him : im (Cexp w) = 0) by (rewrite H; reflexivity).
  unfold Cexp in Hre, Him; simpl in Hre, Him.
  assert (exp_pos : exp (re w) > 0) by apply exp_pos.
  apply Rgt_not_eq in exp_pos.
  destruct (Rmult_integral (exp (re w)) (cos (im w)) Hre) as [Hexp | Hcos].
  - contradiction.
  - destruct (Rmult_integral (exp (re w)) (sin (im w)) Him) as [Hexp' | Hsin].
    + contradiction.
    + pose proof (Rtrigo1.sin2_cos2 (im w)) as Htrig.
      unfold Rsqr in Htrig.
      rewrite Hcos, Hsin in Htrig.
      simpl in Htrig; lra.
Qed.

(* 复数指数加法性质 *)
Lemma Cexp_add : forall w1 w2, Cexp (w1 +c w2) = Cexp w1 *c Cexp w2.
Proof.
  intros [a1 b1] [a2 b2]; unfold Cexp, Cadd, Cmul; simpl.
  rewrite exp_plus.
  rewrite cos_plus.
  rewrite sin_plus.
  apply Complex_eq; simpl; ring.
Qed.

(* 指数函数零点恒等式 *)
Lemma Cexp_0 : Cexp C0 = C1.
Proof.
  unfold Cexp, C0, C1; simpl.
  rewrite exp_0, cos_0, sin_0.
  apply Complex_eq; simpl; ring.
Qed.

(* 反正切余弦公式 *)
Lemma cos_atan_eq : forall t, cos (atan t) = 1 / sqrt (1 + t^2).
Proof.
  intro t.
  assert (H : - PI/2 < atan t < PI/2) by apply atan_bound.
  destruct H as [H1 H2].
  assert (H1' : - (PI/2) < atan t) by (replace (- (PI/2)) with (- PI/2); [exact H1 | field; lra]).
  assert (Hcos_pos : 0 < cos (atan t)) by apply (cos_gt_0 (atan t) H1' H2).
  pose proof (tan_atan t) as Htan.
  unfold tan in Htan.
  assert (Hsin_eq : sin (atan t) = t * cos (atan t)).
  { rewrite <- (Rmult_1_r (sin (atan t))).
    replace (sin (atan t)) with (sin (atan t) / cos (atan t) * cos (atan t)).
    2: field; apply Rgt_not_eq, Hcos_pos.
    rewrite Htan; ring. }
  pose proof (sin2_cos2 (atan t)) as Htrig.
  unfold Rsqr in Htrig.
  rewrite Hsin_eq in Htrig.
  replace (t * cos (atan t) * (t * cos (atan t))) with (t * t * (cos (atan t) * cos (atan t))) in Htrig by ring.
  replace (t * t) with (Rsqr t) in Htrig by (unfold Rsqr; ring).
  replace (cos (atan t) * cos (atan t)) with (Rsqr (cos (atan t))) in Htrig by (unfold Rsqr; ring).
  rewrite (Rmult_comm (Rsqr t) (Rsqr (cos (atan t)))) in Htrig.
  assert (Hprod : Rsqr (cos (atan t)) * (1 + Rsqr t) = 1).
  { replace (Rsqr (cos (atan t)) * (1 + Rsqr t))
      with (Rsqr (cos (atan t)) * Rsqr t + Rsqr (cos (atan t))) by ring.
    exact Htrig. }
  assert (Hcos2 : Rsqr (cos (atan t)) = 1 / (1 + Rsqr t)).
  { apply Rmult_eq_reg_l with (1 + Rsqr t).
    - rewrite Rmult_comm; rewrite Hprod; field.
      apply Rgt_not_eq; apply Rplus_lt_le_0_compat; [lra | apply Rle_0_sqr].
    - apply Rgt_not_eq; apply Rplus_lt_le_0_compat; [lra | apply Rle_0_sqr]. }
  rewrite <- (Rsqr_pow2 t).
  assert (Hpos_den : 0 < 1 + Rsqr t) by (apply Rplus_lt_le_0_compat; [lra | apply Rle_0_sqr]).
  apply Rsqr_inj.
  - left; apply Hcos_pos.
  - apply Rlt_le.
    assert (Hsqrt_pos : 0 < sqrt (1 + Rsqr t)) by (apply sqrt_lt_R0_c; exact Hpos_den).
    apply Rdiv_lt_0_compat; [lra | exact Hsqrt_pos].
  - rewrite Hcos2.
    unfold Rsqr.
    set (a := sqrt (1 + t * t)).
    assert (a_pos : 0 < a).
    { unfold a; apply sqrt_lt_R0_c.
      replace (1 + t * t) with (1 + Rsqr t) by (unfold Rsqr; ring).
      exact Hpos_den. }
    assert (a_neq0 : a <> 0) by (apply Rgt_not_eq; exact a_pos).
    replace (1 + t * t) with (a * a) by (apply sqrt_sqrt; apply Rplus_le_le_0_compat; [apply Rle_0_1 | apply Rle_0_sqr]).
    field; auto.
Qed.

(* 平方倒数恒等式 *)
Lemma Rsqr_inv : forall r, r <> 0 -> Rsqr (/ r) = / Rsqr r.
Proof.
  intros; unfold Rsqr; field; assumption.
Qed.

(* 反正切分母有理化 *)
Lemma aux_eq : forall x y, x <> 0 ->
  / sqrt (1 + (y/x)^2) = Rabs x / sqrt (x^2 + y^2).
Proof.
  intros x y Hx.
  apply Rsqr_inj.
  - apply Rlt_le.
    apply Rinv_0_lt_compat.
    apply sqrt_lt_R0_c.
    apply Rplus_lt_le_0_compat; [lra | apply pow2_ge_0].
  - apply Rmult_le_pos.
    + apply Rabs_pos.
    + apply Rlt_le, Rinv_0_lt_compat, sqrt_lt_R0_c.
      replace (x^2 + y^2) with (Rsqr x + Rsqr y) by (unfold Rsqr; ring).
      apply Rplus_lt_le_0_compat.
      * apply Rlt_0_sqr; exact Hx.
      * apply Rle_0_sqr.
  - replace (1 + (y / x) ^ 2) with (1 + Rsqr (y / x)) by (unfold Rsqr; ring).
    replace (x ^ 2 + y ^ 2) with (x * x + y * y) by (unfold pow; simpl; ring).

    assert (Hpos1 : 0 < 1 + Rsqr (y / x)).
    { apply Rplus_lt_le_0_compat; [lra | apply Rle_0_sqr]. }
    assert (Hpos2 : 0 < x * x + y * y).
    { apply Rplus_lt_le_0_compat.
      - apply Rlt_0_sqr; exact Hx.
      - apply Rle_0_sqr. }
    assert (Hsqrt1_neq0 : sqrt (1 + Rsqr (y / x)) <> 0)
      by (apply Rgt_not_eq, sqrt_lt_R0_c; exact Hpos1).
    assert (Hsqrt2_neq0 : sqrt (x * x + y * y) <> 0)
      by (apply Rgt_not_eq, sqrt_lt_R0_c; exact Hpos2).

    unfold pow; simpl.
    replace ((/ sqrt (1 + Rsqr (y/x))) * (/ sqrt (1 + Rsqr (y/x)))) with (Rsqr (/ sqrt (1 + Rsqr (y/x)))) by (unfold Rsqr; reflexivity).
    rewrite Rsqr_inv; [| exact Hsqrt1_neq0].
    rewrite Rsqr_sqrt; [| apply Rlt_le; exact Hpos1].

    unfold pow; simpl.
    replace ((Rabs x / sqrt (x * x + y * y)) * (Rabs x / sqrt (x * x + y * y))) with (Rsqr (Rabs x / sqrt (x * x + y * y))) by (unfold Rsqr; reflexivity).
    assert (Heq_sq : (Rabs x / sqrt (x * x + y * y))² = (Rabs x)² / (sqrt (x * x + y * y))²).
    { unfold Rsqr; field; apply Hsqrt2_neq0. }
    rewrite Heq_sq.
    rewrite Rsqr_abs.
    rewrite Rsqr_sqrt; [| apply Rlt_le; exact Hpos2].

    assert (Hx2_neq0 : x * x <> 0) by (apply Rgt_not_eq; apply Rlt_0_sqr; exact Hx).
    assert (Htmp : 1 + Rsqr (y / x) = (x * x + y * y) / (x * x)).
    { unfold Rsqr; field; auto. }
    rewrite <- (Rsqr_abs (y/x)).
    rewrite Htmp.
    assert (Hpos2_neq0 : x * x + y * y <> 0) by (apply Rgt_not_eq; exact Hpos2).
    assert (Heq : / ((x * x + y * y) / (x * x)) = x * x / (x * x + y * y)).
    { field; split; assumption. }
    rewrite Heq.
    replace (x * x) with (Rsqr x) by (unfold Rsqr; reflexivity).
    rewrite (Rsqr_abs x).
    reflexivity.
Qed.

(* 反正切余弦绝对值公式 *)
Lemma cos_atan2_aux : forall y x, x <> 0 ->
  cos (atan (y/x)) = Rabs x / sqrt (x^2 + y^2).
Proof.
  intros y x Hx.
  rewrite cos_atan_eq.
  unfold Rdiv at 1.
  rewrite Rmult_1_l.
  apply aux_eq; assumption.
Qed.

(* 余弦的 atan2 恒等式 *)
Lemma cos_atan2 : forall y x (H : sqrt (x^2 + y^2) <> 0),
  cos (atan2 y x) = x / sqrt (x^2 + y^2).
Proof.
  intros y x H.
  unfold atan2.
  destruct (Req_EM_T x 0) as [Hx0 | Hxneq0].
  - subst x.
    simpl.
    destruct (Rlt_dec y 0) as [Hy | Hy].
    + replace (- PI / 2) with (- (PI/2)) by (field; lra).
      rewrite cos_neg, cos_PI2.
      replace (sqrt (0 * (0 * 1) + y * (y * 1))) with (sqrt (y^2)) by (f_equal; ring).
      replace (sqrt (0 ^ 2 + y ^ 2)) with (sqrt (y^2)) in H by (f_equal; ring).
      replace (0 / sqrt (y^2)) with 0 by (field; assumption).
      reflexivity.
    + rewrite cos_PI2.
      replace (sqrt (0 * (0 * 1) + y * (y * 1))) with (sqrt (y^2)) by (f_equal; ring).
      replace (sqrt (0 ^ 2 + y ^ 2)) with (sqrt (y^2)) in H by (f_equal; ring).
      replace (0 / sqrt (y^2)) with 0 by (field; assumption).
      reflexivity.
  - set (a := atan (y / x)).
    destruct (Rlt_dec x 0) as [Hxneg | Hxpos].
    + destruct (Rlt_dec y 0) as [Hyneg | Hypos].
      * replace (atan2 y x) with (a - PI).
        2: {
          unfold atan2, a.
          destruct (Req_EM_T x 0) as [Hx0 | _]; [contradiction Hxneq0 | clear Hxneq0].
          destruct (Rlt_dec x 0) as [Hxn | Hxp]; [| contradiction Hxneg].
          destruct (Rlt_dec y 0) as [Hyn | Hyp]; [reflexivity | contradiction Hyneg].
        }
        rewrite cos_minus, cos_PI, sin_PI; simpl.
        replace (cos a * (-1) + sin a * 0) with (- cos a) by ring.
        assert (Hcos : cos a = Rabs x / sqrt (x^2 + y^2)).
        { apply cos_atan2_aux; assumption. }
        assert (Habs : Rabs x = -x) by (apply Rabs_left; assumption).
        rewrite Habs in Hcos.
        rewrite Hcos.
        replace (- (- x / sqrt (x^2 + y^2))) with (x / sqrt (x^2 + y^2)).
        2: { field; apply H. }
        reflexivity.
      * replace (atan2 y x) with (a + PI).
        2: {
          unfold atan2, a.
          destruct (Req_EM_T x 0) as [Hx0 | _]; [contradiction Hxneq0 |].
          destruct (Rlt_dec x 0) as [Hxn | Hxp]; [| contradiction Hxneg].
          destruct (Rlt_dec y 0) as [Hyn | Hyp]; [contradiction Hypos | reflexivity].
        }
        rewrite cos_plus, cos_PI, sin_PI; simpl.
        replace (cos a * (-1) - sin a * 0) with (- cos a) by ring.
        assert (Hcos : cos a = Rabs x / sqrt (x^2 + y^2)).
        { apply cos_atan2_aux; assumption. }
        assert (Habs : Rabs x = -x) by (apply Rabs_left; assumption).
        rewrite Habs in Hcos.
        rewrite Hcos.
        replace (- (- x / sqrt (x^2 + y^2))) with (x / sqrt (x^2 + y^2)).
        2: { field; apply H. }
        reflexivity.
    + replace (atan2 y x) with a.
      2: {
        unfold atan2, a.
        destruct (Req_EM_T x 0) as [Hx0 | _]; [contradiction Hxneq0 |].
        destruct (Rlt_dec x 0) as [Hxn | Hxp]; [contradiction Hxpos | reflexivity].
      }
      unfold a.
      rewrite cos_atan_eq.
      assert (Hxpos' : 0 < x).
      { destruct (total_order_T x 0) as [[Hlt|Heq]|Hgt].
        - exfalso; apply Hxpos; exact Hlt.
        - exfalso; apply Hxneq0; exact Heq.
        - exact Hgt. }
      unfold Rdiv at 1. rewrite Rmult_1_l.
      rewrite (aux_eq x y Hxneq0).
      rewrite Rabs_pos_eq; [reflexivity | left; exact Hxpos'].
Qed.

(* 正弦的 atan2 恒等式 *)
Lemma sin_atan2 : forall y x (H : sqrt (x^2 + y^2) <> 0),
  sin (atan2 y x) = y / sqrt (x^2 + y^2).
Proof.
  intros y x H.
  unfold atan2.
  destruct (Req_EM_T x 0) as [Hx0 | Hxneq0].
  - subst x.
    simpl.
    destruct (Rlt_dec y 0) as [Hy | Hy].
    + replace (0 * (0 * 1) + y * (y * 1)) with (y * y) by ring.
      replace (y * y) with (Rsqr y) by (unfold Rsqr; ring).
      rewrite sqrt_Rsqr_abs.
      rewrite Rabs_left; [ | assumption ].
      replace (- PI / 2) with (- (PI/2)) by (field; lra).
      rewrite sin_neg, sin_PI2.
      assert (y <> 0) by lra.
      field; auto.
    + assert (y <> 0).
      { intro Hy0; rewrite Hy0 in H.
        simpl in H.
        replace (0 * (0 * 1) + 0 * (0 * 1)) with 0 in H by ring.
        rewrite sqrt_0 in H.
        contradiction H; reflexivity. }
      replace (0 * (0 * 1) + y * (y * 1)) with (y * y) by ring.
      replace (y * y) with (Rsqr y) by (unfold Rsqr; ring).
      rewrite sqrt_Rsqr_abs.
      rewrite Rabs_pos_eq; [ | apply Rlt_le; lra ].
      rewrite sin_PI2.
      field; auto.
  - set (a := atan (y / x)).
    destruct (Rlt_dec x 0) as [Hxneg | Hxpos].
    + destruct (Rlt_dec y 0) as [Hy | Hy].
      - replace (atan2 y x) with (a - PI).
        2: {
          unfold atan2, a.
          destruct (Req_EM_T x 0) as [Hx0 | _]; [contradiction Hxneq0 | clear Hxneq0].
          destruct (Rlt_dec x 0) as [Hxn | Hxp]; [| contradiction Hxneg].
          destruct (Rlt_dec y 0) as [Hyn | Hyp]; [reflexivity | contradiction Hy].
        }
        rewrite sin_minus, sin_PI, cos_PI; simpl.
        rewrite Rmult_0_r; rewrite Rminus_0_r.
        assert (Hcos : cos a = Rabs x / sqrt (x^2 + y^2)).
        { apply cos_atan2_aux; assumption. }
        assert (Hxneg' : x < 0) by assumption.
        rewrite (Rabs_left x Hxneg') in Hcos.
        assert (Htan : tan a = y / x) by (apply tan_atan).
        unfold tan in Htan.
        assert (Hcos_nonzero : cos a <> 0).
        {
          apply Rgt_not_eq.
          rewrite Hcos.
          apply Rdiv_lt_0_compat.
          - apply Ropp_gt_lt_0_contravar; lra.
          - apply sqrt_lt_R0_c.
            apply Rplus_lt_le_0_compat.
            + rewrite <- Rsqr_pow2; apply Rlt_0_sqr; lra.
            + rewrite <- Rsqr_pow2; apply Rle_0_sqr.
        }
        assert (Hsin : sin a = (y / x) * cos a).
        { rewrite <- Htan. unfold tan. field. assumption. }
        assert (Htarget : - sin a = y / sqrt (x^2 + y^2)).
        {
          rewrite Hsin, Hcos.
          field.
          split; [apply H | apply Hxneq0].
        }
        replace (sin a * -1) with (- sin a) by ring.
        rewrite Htarget.
        reflexivity.
      - replace (atan2 y x) with (a + PI).
        2: {
          unfold atan2, a.
          destruct (Req_EM_T x 0) as [Hx0 | _]; [contradiction Hxneq0 |].
          destruct (Rlt_dec x 0) as [Hxn | Hxp]; [| contradiction Hxneg].
          destruct (Rlt_dec y 0) as [Hyn | Hyp]; [contradiction Hy | reflexivity].
        }
        rewrite sin_plus, sin_PI, cos_PI; simpl.
        rewrite Rmult_0_r; rewrite Rplus_0_r.
        assert (Hcos : cos a = Rabs x / sqrt (x^2 + y^2)).
        { apply cos_atan2_aux; assumption. }
        assert (Hxneg' : x < 0) by assumption.
        rewrite (Rabs_left x Hxneg') in Hcos.
        assert (Htan : tan a = y / x) by (apply tan_atan).
        unfold tan in Htan.
        assert (Hcos_nonzero : cos a <> 0).
        {
          apply Rgt_not_eq.
          rewrite Hcos.
          apply Rdiv_lt_0_compat.
          - apply Ropp_gt_lt_0_contravar; lra.
          - apply sqrt_lt_R0_c.
            apply Rplus_lt_le_0_compat.
            + rewrite <- Rsqr_pow2; apply Rlt_0_sqr; lra.
            + rewrite <- Rsqr_pow2; apply Rle_0_sqr.
        }
        assert (Hsin : sin a = (y / x) * cos a).
        { rewrite <- Htan. unfold tan. field. assumption. }
        rewrite Hsin, Hcos.
        replace (y / x * (- x / sqrt (x ^ 2 + y ^ 2)) * -1)
          with (y / sqrt (x ^ 2 + y ^ 2)).
        2: {
          field.
          split; [apply H | apply Hxneq0].
        }
        reflexivity.
    + replace (atan2 y x) with a.
      2: {
        unfold atan2, a.
        destruct (Req_EM_T x 0) as [Hx0 | _]; [contradiction Hxneq0 |].
        destruct (Rlt_dec x 0) as [Hxn | Hxp]; [contradiction Hxpos | reflexivity].
      }
      unfold a.
      rewrite sin_atan_eq.
      unfold Rdiv at 1.
      rewrite (aux_eq x y Hxneq0).
      rewrite Rabs_pos_eq; [ | lra ].
      field.
      split; [apply H | apply Hxneq0].
Qed.

(* 指数与主支对数的互逆性 *)
Lemma exp_Clog : forall z Hz, Cexp (Clog_principal z Hz) = z.
Proof.
  intros [x y] Hz.
  unfold Clog_principal, Cexp; simpl.
  set (r := Cnorm (x +i y)).
  assert (r_pos : 0 < r) by (apply Cnorm_pos; exact Hz).
  assert (Hsq : Cnorm_sq (x +i y) = x^2 + y^2).
  { unfold Cnorm_sq, Rsqr; simpl; ring. }
  assert (Hr_eq : sqrt (x^2 + y^2) = r).
  { unfold r; rewrite <- Hsq; reflexivity. }
  assert (Hsqrt_neq : sqrt (x^2 + y^2) <> 0).
  { rewrite Hr_eq; apply Rgt_not_eq; exact r_pos. }
  rewrite exp_ln; [| exact r_pos].
  rewrite (cos_atan2 y x Hsqrt_neq).
  rewrite (sin_atan2 y x Hsqrt_neq).
  replace (x / sqrt (x^2 + y^2)) with (x / r) by (rewrite Hr_eq; reflexivity).
  replace (y / sqrt (x^2 + y^2)) with (y / r) by (rewrite Hr_eq; reflexivity).
  assert (r_neq0 : r <> 0) by (apply Rgt_not_eq, r_pos).
  replace (r * (x / r)) with x by (field; apply r_neq0).
  replace (r * (y / r)) with y by (field; apply r_neq0).
  reflexivity.
Qed.

(* 定理：主支对数与指数互逆 *)
Theorem Clog_exp : forall z, -PI < im z <= PI -> Clog_principal (Cexp z) (Cexp_neq_0 z) = z.
Proof.
  intros z H.
  destruct z as [x y]; simpl in H.
  destruct H as [Hlow Hhigh].
  unfold Clog_principal.
  set (a := exp x * cos y).
  set (b := exp x * sin y).

  assert (Hnorm_eq : Cnorm (a +i b) = exp x).
  {
    unfold Cnorm, Cnorm_sq; simpl.
    unfold a, b.
    rewrite !Rsqr_mult.
    set (e2 := Rsqr (exp x)).
    replace (e2 * Rsqr (cos y) + e2 * Rsqr (sin y)) with (e2 * (Rsqr (cos y) + Rsqr (sin y))) by ring.
    rewrite Rplus_comm; rewrite sin2_cos2.
    rewrite Rmult_1_r.
    apply sqrt_Rsqr.
    apply Rlt_le, exp_pos.
  }

  assert (Harg : atan2 b a = y).
  {
    unfold a, b.
    assert (Hpos : 0 < exp x) by apply exp_pos.
    assert (Harg' : atan2 (exp x * sin y) (exp x * cos y) = atan2 (sin y) (cos y)).
    { apply atan2_scal_pos with (a := exp x); assumption. }
    rewrite Harg'.
    apply atan2_sin_cos.
    split; [exact Hlow | exact Hhigh].
  }

  unfold Cexp; simpl.
  replace ((exp x * cos y) +i (exp x * sin y)) with (a +i b) by (unfold a, b; auto).
  rewrite Hnorm_eq.
  replace (atan2 (exp x * sin y) (exp x * cos y)) with (atan2 b a) by (unfold a, b; auto).
  rewrite Harg.
  rewrite ln_exp.
  reflexivity.
Qed.

(* 单位圆盘内平移非零 *)
Lemma C1_plus_z_neq0 : forall z, Cnorm z <= 1/2 -> C1 +c z <> C0.
Proof.
  intros z H H0.
  apply (f_equal (fun w => w -c C1)) in H0.
  assert (H1 : C1 +c z -c C1 = z).
  { apply Complex_eq; unfold C1, Cadd, Csub; destruct z; simpl; ring. }
  rewrite H1 in H0.
  assert (H2 : Cnorm z = Cnorm (-c C1)).
  { rewrite H0; reflexivity. }
  assert (H3 : Cnorm (-c C1) = 1).
  {
    unfold Cnorm, Cnorm_sq, Csub, C0, C1; simpl.
    unfold Rsqr; simpl.
    replace ((0 - 1) * (0 - 1)) with 1 by ring.
    replace ((0 - 0) * (0 - 0)) with 0 by ring.
    rewrite Rplus_0_r.
    rewrite sqrt_1.
    reflexivity.
  }
  rewrite H3 in H2.
  lra.
Qed.

End ComplexFoundation.
