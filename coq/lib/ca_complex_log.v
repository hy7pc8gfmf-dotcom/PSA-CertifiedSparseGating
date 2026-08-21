(* 拆分自 Riemann_Hypothesis_Proof_Framework.v（复分析证明库 v6.0）*)
(* 库: ca_complex_log  原文行区间: 17733-20320  机械拆分，未改动内容 *)

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

Require Import ca_base ca_algebra ca_primes ca_complex_analysis ca_fourier ca_zeta_scaffold ca_trig ca_gamma ca_taylor ca_zeta_axioms.

Require Import Stdlib.Logic.IndefiniteDescription.

(* ====================================================
   模块：ComplexBasics
   目的：实数到复数的标准嵌入，基本非零性引理
   依赖：ComplexNumbers
   ==================================================== *)
Module ComplexBasics.

Import ComplexNumbers.
Import Coq.Reals.Reals.

Local Open Scope R_scope.
Local Open Scope complex_scope.

(* 实数嵌入复数 *)
Definition C_of_R (r : R) : Complex := {| re := r; im := 0 |}.

(* 实数非零则其对应的复数非零 *)
Lemma C_of_R_neq_0 : forall r, r <> 0 -> C_of_R r <> C0.
Proof.
  intros r Hr H. apply (f_equal re) in H. simpl in H. rewrite H in Hr. contradiction.
Qed.

(* S n 的实部（INR）为正数 *)
Lemma INR_S_pos : forall n, 0 < INR (S n).
Proof. intros n; apply lt_0_INR; lia. Qed.

(* S n 的实部（INR）非零 *)
Lemma INR_S_neq_0 : forall n, INR (S n) <> 0.
Proof. intros n; apply Rgt_not_eq, INR_S_pos. Qed.

(* S n 的实部对应的复数非零 *)
Lemma C_of_R_INR_S_neq_0 : forall n, C_of_R (INR (S n)) <> C0.
Proof. intros n; apply C_of_R_neq_0, INR_S_neq_0. Qed.

(* 2 大于 0 *)
Lemma Rlt_0_2 : 0 < 2. Proof. lra. Qed.

(* 圆周率 PI 大于 0 *)
Lemma Rlt_0_PI : 0 < PI. Proof. exact PI_RGT_0. Qed.

(* 复数 2 非零 *)
Lemma C2_neq_0 : C_of_R 2 <> C0. Proof. apply C_of_R_neq_0; lra. Qed.

End ComplexBasics.

(* ====================================================
   模块：ComplexExponential
   目的：复数指数函数的非零性及其他基本性质
   依赖：ComplexNumbers, ComplexBasics
   ==================================================== *)
Module ComplexExponential.

Import ComplexNumbers.
Import ComplexBasics.
Require Import Stdlib.Reals.Rtrigo1.
Local Open Scope R_scope.
Local Open Scope complex_scope.
Import ComplexNumbers.
Import ComplexBasics.

(* 复指数非零 *)
Lemma Cexp_neq_0 : forall z, Cexp z <> C0.
Proof.
  intros z H.
  assert (Hre : re (Cexp z) = re C0) by (rewrite H; reflexivity).
  assert (Him : im (Cexp z) = im C0) by (rewrite H; reflexivity).
  simpl in Hre, Him.
  assert (Hexp_neq0 : exp (re z) <> 0) by (apply Rgt_not_eq, exp_pos).
  assert (Hcos : cos (im z) = 0).
  { apply Rmult_integral in Hre; destruct Hre as [Hexp_zero | Hcos_zero].
    - exfalso; apply Hexp_neq0; exact Hexp_zero.
    - assumption. }
  assert (Hsin : sin (im z) = 0).
  { apply Rmult_integral in Him; destruct Him as [Hexp_zero | Hsin_zero].
    - exfalso; apply Hexp_neq0; exact Hexp_zero.
    - assumption. }
  pose proof (Rtrigo1.sin2_cos2 (im z)) as Htrig.
  rewrite Hcos, Hsin in Htrig.
  unfold Rsqr in Htrig; repeat rewrite Rmult_0_l in Htrig; repeat rewrite Rmult_0_r in Htrig.
  rewrite Rplus_0_r in Htrig; simpl in Htrig; lra.
Qed.

(* 复指数单位元 *)
Lemma Cexp_0 : Cexp C0 = C1.
Proof.
  unfold Cexp, C0, C1; simpl.
  rewrite exp_0, cos_0, sin_0.
  f_equal; ring.
Qed.

End ComplexExponential.

(* ====================================================
   模块：ComplexLogarithm
   目的：主支对数的定义、基本性质及全纯性
   依赖：ComplexNumbers, ComplexBasics, ComplexExponential
   ==================================================== *)
Module ComplexLogarithm.

Require Import Stdlib.Reals.Rtrigo1.
Require Import Stdlib.Reals.Ratan.
Local Open Scope R_scope.
Local Open Scope complex_scope.
Import ComplexNumbers.
Import ComplexBasics.
Import ComplexExponential.
Import HolomorphicFunctions.

(* 主支对数 *)
Definition Clog_principal (z : Complex) (Hz : z <> C0) : Complex :=
  let r := Cnorm z in
  let θ := atan2 (im z) (re z) in
  (ln r) +i θ.

(* [构造性轨道 S1] 复数等值可判定：Req_dec 分量组合，不引入 classic *)
Lemma Ceq_EM_T : forall z w : Complex, z = w \/ z <> w.
Proof.
  intros z w; destruct z as [x1 y1]; destruct w as [x2 y2].
  destruct (Req_dec x1 x2) as [Hx|Hx].
  - destruct (Req_dec y1 y2) as [Hy|Hy].
    + left; f_equal; assumption.
    + right; intros H; apply Hy.
      pose proof (f_equal im H) as Hi; simpl in Hi; exact Hi.
  - right; intros H; apply Hx.
    pose proof (f_equal re H) as Hr; simpl in Hr; exact Hr.
Qed.

(* [构造性轨道 S1] Clog_principal 与证明参数无关（定义体不使用 Hz） *)
Lemma Clog_principal_irrel : forall z (H1 H2 : z <> C0),
  Clog_principal z H1 = Clog_principal z H2.
Proof. intros z H1 H2; unfold Clog_principal; reflexivity. Qed.


(* 在模块顶部补入 *)
(* 平方和为零则各分量为零 *)
Lemma Rsqr_plus_eq_0 : forall x y : R, x² + y² = 0 -> x = 0 /\ y = 0.
Proof.
  intros x y H.
  assert (Hx2 : x² = 0).
  { apply Rle_antisym.
    - apply (Rle_trans _ (x² + y²)).
      + pattern x² at 1; rewrite <- (Rplus_0_r x²).
        apply Rplus_le_compat_l; apply Rle_0_sqr.
      + rewrite H; right; reflexivity.
    - apply Rle_0_sqr. }
  assert (Hy2 : y² = 0).
  { apply Rle_antisym.
    - apply (Rle_trans _ (x² + y²)).
      + pattern y² at 1; rewrite <- (Rplus_0_l y²).
        apply Rplus_le_compat_r; apply Rle_0_sqr.
      + rewrite H; right; reflexivity.
    - apply Rle_0_sqr. }
  split; apply Rsqr_eq_0; assumption.
Qed.


(* 范数平方为零等价于复数本身为零 *)
Lemma Cnorm_sq_eq_0 : forall z, Cnorm_sq z = 0 -> z = C0.
Proof.
  intros [x y]; unfold Cnorm_sq, C0; simpl; intros H.
  apply Rsqr_plus_eq_0 in H; destruct H as [Hx Hy].
  subst x y; reflexivity.
Qed.

(* 范数平方为零 *)
Lemma Cnorm_sq_C0 : Cnorm_sq C0 = 0.
Proof.
  unfold Cnorm_sq, C0; simpl; unfold Rsqr; ring.
Qed.

(* 范数平方大于零蕴含非零 *)
Lemma Cnorm_sq_pos_nonzero : forall z, 0 < Cnorm_sq z -> z <> C0.
Proof.
  intros z Hpos Heq; subst z.
  rewrite Cnorm_sq_C0 in Hpos; lra.
Qed.


Lemma Cnorm_sq_ge0 : forall z, 0 <= Cnorm_sq z.
Proof.
  intro z; apply Rplus_le_le_0_compat; apply Rle_0_sqr.
Qed.

Definition Clog_total (z : Complex) : Complex :=
  match Rlt_dec 0 (Cnorm_sq z) with
  | left Hpos   => Clog_principal z (Cnorm_sq_pos_nonzero z Hpos)
  | right Hnpos => C0
  end.

(* 复数零的实虚部条件 *)
Lemma C0_eq : forall z, re z = 0 /\ im z = 0 -> z = C0.
Proof.
  intros z [Hre Him]; destruct z; simpl in *; subst; reflexivity.
Qed.

(* 复数模平方正性 *)
Lemma Cnorm_sq_pos : forall z, z <> C0 -> 0 < Cnorm_sq z.
Proof.
  intros z Hz.
  unfold Cnorm_sq.
  destruct z as [a b]; simpl.
  destruct (Req_EM_T a 0) as [Ha|Ha]; destruct (Req_EM_T b 0) as [Hb|Hb].
  - exfalso; apply Hz; apply C0_eq; split; assumption.
  - apply Rplus_le_lt_0_compat.
    + apply Rle_0_sqr.
    + apply Rlt_0_sqr; exact Hb.
  - apply Rplus_lt_le_0_compat.
    + apply Rlt_0_sqr; exact Ha.
    + apply Rle_0_sqr.
  - apply Rplus_lt_0_compat.
    + apply Rlt_0_sqr; exact Ha.
    + apply Rlt_0_sqr; exact Hb.
Qed.

(* 复数模正性 *)
Lemma Cnorm_pos : forall z, z <> C0 -> 0 < Cnorm z.
Proof.
  intros z Hz.
  unfold Cnorm.
  apply sqrt_lt_R0_c.
  apply Cnorm_sq_pos; auto.
Qed.

(* atan2余弦公式 *)
Lemma cos_atan2 : forall y x,
  let r := sqrt (x^2 + y^2) in
  r <> 0 -> cos (atan2 y x) = x / r.
Proof.
  intros y x r Hr.
  unfold atan2.
  destruct (Req_EM_T x 0) as [Hx_zero | Hx_nonzero].
  - rewrite Hx_zero.
    destruct (Rlt_dec y 0) as [Hy_neg | Hy_not_neg].
    + assert (H: - PI / 2 = - (PI / 2)).
      { field; lra. }
      rewrite H, cos_neg, cos_PI2.
      unfold Rdiv; rewrite Rmult_0_l.
      reflexivity.
    + rewrite cos_PI2.
      unfold Rdiv; rewrite Rmult_0_l.
      reflexivity.
  - assert (cos_atan_eq : forall a, cos (atan a) = 1 / sqrt (1 + Rsqr a)).
    { intros a.
      pose proof (atan_bound a) as [Hlb Hub].
      assert (Hcos_pos : 0 < cos (atan a)).
      { assert (Hlb' : - (PI / 2) < atan a).
        { replace (- (PI / 2)) with (- PI / 2) by (field; lra). exact Hlb. }
        apply cos_gt_0; [exact Hlb' | exact Hub]. }
      pose proof (tan_atan a) as Htan.
      unfold tan in Htan.
      assert (Hsin_eq : sin (atan a) = a * cos (atan a)).
      { replace (sin (atan a)) with (sin (atan a) / cos (atan a) * cos (atan a)).
        - rewrite Htan; reflexivity.
        - field; apply Rgt_not_eq, Hcos_pos. }
      pose proof (sin2_cos2 (atan a)) as Htrig.
      unfold Rsqr in Htrig.
      rewrite Hsin_eq in Htrig.
      replace (a * cos (atan a) * (a * cos (atan a))) with (a^2 * (cos (atan a))^2) in Htrig
        by (simpl; ring).
      replace (a^2) with (Rsqr a) in Htrig by (rewrite Rsqr_pow2; reflexivity).
      replace ((cos (atan a))^2) with (Rsqr (cos (atan a))) in Htrig by (rewrite Rsqr_pow2; reflexivity).
      assert (Hprod : (1 + Rsqr a) * Rsqr (cos (atan a)) = 1).
      { replace ((1 + Rsqr a) * Rsqr (cos (atan a))) with (Rsqr a * Rsqr (cos (atan a)) + Rsqr (cos (atan a))) by ring.
        exact Htrig. }
      assert (Hpos_den : 0 < 1 + Rsqr a).
      { assert (0 <= Rsqr a) by apply Rle_0_sqr; lra. }
      assert (Hnz : 1 + Rsqr a <> 0) by (apply Rgt_not_eq; exact Hpos_den).
      assert (Hcos2_eq : Rsqr (cos (atan a)) = 1 / (1 + Rsqr a)).
      { apply Rmult_eq_reg_l with (1 + Rsqr a); [| exact Hnz].
        rewrite Hprod; field; exact Hnz. }
      replace (a²) with (Rsqr a) in * by (rewrite Rsqr_pow2; reflexivity).
      assert (Hcos_eq : cos (atan a) = sqrt (1 / (1 + Rsqr a))).
      { apply Rsqr_inj.
        - apply Rlt_le, Hcos_pos.
        - apply sqrt_pos.
        - rewrite Rsqr_sqrt.
          + exact Hcos2_eq.
          + apply Rlt_le.
            apply Rlt_mult_inv_pos; [lra | exact Hpos_den]. }
      rewrite sqrt_div in Hcos_eq; [| lra | exact Hpos_den ].
      rewrite sqrt_1 in Hcos_eq.
      exact Hcos_eq.
    }
    destruct (Rlt_dec x 0) as [Hx_neg | Hx_pos].
    + destruct (Rlt_dec y 0) as [Hy_neg | Hy_pos].
      * rewrite cos_minus.
        rewrite cos_PI, sin_PI.
        simpl.
        replace (sin (atan (y/x)) * 0) with 0 by ring.
        replace (cos (atan (y/x)) * (-1) + 0) with (- cos (atan (y/x))) by ring.
        rewrite cos_atan_eq with (a := y/x).
        unfold Rdiv.
        rewrite Rmult_1_l.
        unfold Rsqr at 1.
        replace (1 + (y * / x) * (y * / x)) with ((x^2 + y^2) * / x^2) by (field; lra).
        replace ((x^2 + y^2) * / x^2) with ((x^2 + y^2) / x^2) by (field; lra).
        rewrite sqrt_div.
        - rewrite <- (Rsqr_pow2 x).
          rewrite sqrt_Rsqr_abs.
          rewrite Rabs_left; [| lra].
          assert (Hsq: x² = x^2) by (rewrite Rsqr_pow2; reflexivity).
          rewrite Hsq.
          replace (sqrt (x^2 + y^2)) with r by reflexivity.
          field; split; [exact Hr | lra].
        - apply Rplus_le_le_0_compat; [apply pow2_ge_0 | apply pow2_ge_0].
        - unfold pow; simpl; replace (x * (x * 1)) with (x * x) by ring; apply Rlt_0_sqr; lra.
      * rewrite cos_plus.
        rewrite cos_PI, sin_PI.
        simpl.
        rewrite cos_atan_eq with (a := y/x).
        unfold Rdiv; rewrite Rmult_1_l.
        replace (sin (atan (y/x)) * 0) with 0 by ring.
        unfold Rsqr at 1.
        replace (1 + (y * / x) * (y * / x)) with ((x^2 + y^2) * / x^2) by (field; lra).
        replace ((x^2 + y^2) * / x^2) with ((x^2 + y^2) / x^2) by (field; lra).
        rewrite sqrt_div.
        - rewrite <- (Rsqr_pow2 x).
          rewrite sqrt_Rsqr_abs.
          rewrite Rabs_left; [| lra].
          assert (Hsq: x² = x^2) by (rewrite Rsqr_pow2; reflexivity).
          rewrite Hsq.
          replace (sqrt (x^2 + y^2)) with r by reflexivity.
          field; split; [exact Hr | lra].
        - apply Rplus_le_le_0_compat; [apply pow2_ge_0 | apply pow2_ge_0].
        - unfold pow; simpl; replace (x * (x * 1)) with (x * x) by ring; apply Rlt_0_sqr; lra.
    + rewrite cos_atan_eq with (a := y/x).
      unfold Rdiv; rewrite Rmult_1_l.
      unfold Rsqr at 1.
      replace (1 + (y * / x) * (y * / x)) with ((x^2 + y^2) / x^2) by (field; lra).
      assert (Hr_over_x : sqrt ((x^2 + y^2) / x^2) = r / x).
      { rewrite sqrt_div.
        - replace (sqrt (x^2 + y^2)) with r by reflexivity.
          rewrite <- (Rsqr_pow2 x) at 1.
          rewrite sqrt_Rsqr_abs.
          rewrite Rabs_pos_eq; [| lra].
          reflexivity.
        - apply Rplus_le_le_0_compat; [apply pow2_ge_0 | apply pow2_ge_0].
        - unfold pow; simpl; replace (x * (x * 1)) with (x * x) by ring; apply Rlt_0_sqr; lra.
      }
      rewrite Hr_over_x.
      field; split; [exact Hr | lra].
Qed.

(* 复指数非零 *)
Lemma Cexp_neq_0 : forall z, Cexp z <> C0.
Proof.
  intros z H.
  assert (Hre : re (Cexp z) = re C0) by (rewrite H; reflexivity).
  assert (Him : im (Cexp z) = im C0) by (rewrite H; reflexivity).
  simpl in Hre, Him.
  assert (Hexp_neq0 : exp (re z) <> 0) by (apply Rgt_not_eq, exp_pos).
  assert (Hcos : cos (im z) = 0).
  { apply Rmult_integral in Hre; destruct Hre as [Hexp_zero | Hcos_zero].
    - exfalso; apply Hexp_neq0; exact Hexp_zero.
    - assumption. }
  assert (Hsin : sin (im z) = 0).
  { apply Rmult_integral in Him; destruct Him as [Hexp_zero | Hsin_zero].
    - exfalso; apply Hexp_neq0; exact Hexp_zero.
    - assumption. }
  pose proof (Rtrigo1.sin2_cos2 (im z)) as Htrig.
  rewrite Hcos, Hsin in Htrig.
  unfold Rsqr in Htrig; repeat rewrite Rmult_0_l in Htrig; repeat rewrite Rmult_0_r in Htrig.
  rewrite Rplus_0_r in Htrig; simpl in Htrig; lra.
Qed.

(* 复指数单位元 *)
Lemma Cexp_0 : Cexp C0 = C1.
Proof.
  unfold Cexp, C0, C1; simpl.
  rewrite exp_0, cos_0, sin_0.
  f_equal; ring.
Qed.

(* 反正切余弦公式 *)
Lemma cos_atan_eq : forall a : R, cos (atan a) = 1 / sqrt (1 + a^2).
Proof.
  intros a.
  assert (Hr_eq : sqrt (1 ^ 2 + a ^ 2) = sqrt (1 + a ^ 2)).
  { f_equal; replace (1 ^ 2) with 1 by (simpl; ring); reflexivity. }
  assert (Hr_nonzero : sqrt (1 ^ 2 + a ^ 2) <> 0).
  { apply Rgt_not_eq. apply sqrt_lt_R0_c.
    replace (1 ^ 2) with 1 by (simpl; ring).
    apply Rplus_lt_le_0_compat; [lra |].
    replace (a ^ 2) with (Rsqr a) by (now unfold Rsqr; simpl; ring).
    apply Rle_0_sqr. }
  pose proof (cos_atan2 a 1 Hr_nonzero) as H.
  assert (Hatan : atan2 a 1 = atan a).
  { unfold atan2.
    destruct (Req_EM_T 1 0) as [H1_zero | H1_nonzero].
    - exfalso; lra.
    - destruct (Rlt_dec 1 0) as [H1_neg | H1_not_neg].
      + exfalso; lra.
      + rewrite Rdiv_1_r. reflexivity. }
  rewrite Hatan in H.
  rewrite Hr_eq in H.
  exact H.
Qed.

(* 反正切正弦公式 *)
Lemma sin_atan_eq : forall a : R, sin (atan a) = a / sqrt (1 + a^2).
Proof.
  intros a.
  destruct (Req_EM_T a 0) as [Ha0 | Ha_nonzero].
  - rewrite Ha0, atan_0, sin_0.
    unfold Rdiv; rewrite Rmult_0_l; reflexivity.
  - pose proof (tan_atan a) as Htan.
    unfold tan in Htan.
    rewrite cos_atan_eq in Htan.
    assert (Hsqrt_nonzero : sqrt (1 + a^2) <> 0).
    { apply Rgt_not_eq, sqrt_lt_R0_c.
      replace (1 ^ 2) with 1 by (simpl; ring).
      replace (a ^ 2) with (Rsqr a) by (unfold Rsqr; simpl; ring).
      apply Rplus_lt_le_0_compat; [lra | apply Rle_0_sqr]. }
    unfold Rdiv in Htan.
    replace (1 * / sqrt (1 + a^2)) with (/ sqrt (1 + a^2)) in Htan
      by (rewrite Rmult_1_l; reflexivity).
    rewrite (Rinv_inv (sqrt (1 + a^2))) in Htan.
    apply (f_equal (fun x => x * / sqrt (1 + a^2))) in Htan.
    rewrite Rmult_assoc in Htan.
    rewrite (Rinv_r (sqrt (1 + a^2)) Hsqrt_nonzero) in Htan.
    rewrite Rmult_1_r in Htan.
    exact Htan.
Qed.

(* 反正切2正弦公式 *)
Lemma sin_atan2 : forall y x : R,
  let r := sqrt (x^2 + y^2) in
  r <> 0 -> sin (atan2 y x) = y / r.
Proof.
  intros y x r Hr.
  unfold atan2.
  destruct (Req_EM_T x 0) as [Hx_zero | Hx_nonzero].
  - simpl.
    destruct (Rlt_dec y 0) as [Hy_neg | Hy_nonneg].
    + replace ( - PI / 2 ) with ( - (PI/2) ) by (field; lra).
      rewrite sin_neg, sin_PI2.
      assert (r = - y).
      { unfold r.
        rewrite Hx_zero.
        simpl.
        replace (0 * (0 * 1)) with 0 by ring.
        rewrite Rplus_0_l.
        replace (y * (y * 1)) with (y * y) by ring.
        replace (y * y) with (Rsqr y) by (unfold Rsqr; reflexivity).
        rewrite sqrt_Rsqr_abs.
        - rewrite Rabs_left; [| lra]. reflexivity. }
      rewrite H.
      replace (y / (- y)) with (-1).
      * reflexivity.
      * field; lra.
    + rewrite sin_PI2.
      destruct (Req_EM_T y 0) as [Hy_zero | Hy_pos].
      * unfold r in Hr.
        rewrite Hx_zero, Hy_zero in Hr.
        simpl in Hr.
        assert (Htmp : sqrt (0 * (0 * 1) + 0 * (0 * 1)) = 0).
        { replace (0 * (0 * 1) + 0 * (0 * 1)) with 0 by ring.
          apply sqrt_0. }
        rewrite Htmp in Hr.
        contradiction Hr; reflexivity.
      * assert (Hr_eq : r = y).
        { unfold r; rewrite Hx_zero; simpl.
          replace (0 * (0 * 1) + y * (y * 1)) with (y * y) by (rewrite Rmult_0_l; ring).
          apply Rnot_lt_le in Hy_nonneg.
          rewrite sqrt_square; auto. }
        rewrite Hr_eq. field; lra.
  - destruct (Rlt_dec x 0) as [Hx_neg | Hx_pos].
    + destruct (Rlt_dec y 0) as [Hy_neg | Hy_nonneg].
      * replace (atan (y / x) - PI) with ( - (PI - atan (y / x)) ) by ring.
        rewrite sin_neg.
        rewrite sin_minus; rewrite sin_PI, cos_PI.
        simpl.
        replace (cos (atan (y / x)) * 0 + sin (atan (y / x)) * (-1)) with (- sin (atan (y / x))) by ring.
        rewrite sin_atan_eq.
        assert (Hsqrt_nonzero : sqrt (1 + (y / x) ^ 2) <> 0).
        { apply Rgt_not_eq, sqrt_lt_R0_c.
          assert (0 <= (y / x) ^ 2) by (apply pow2_ge_0).
          lra. }
        unfold r.
        assert (Hx_neg' : x < 0) by auto.
        assert (Hx_nonzero' : x <> 0) by lra.
        assert (Hx_neg_nonneg : 0 <= -x) by lra.
        assert (Hx2_nonneg : 0 <= (- x) ^ 2) by (apply pow2_ge_0).
        assert (Hterm_nonneg : 0 <= 1 + (y / x) ^ 2) by (apply Rplus_le_le_0_compat; [lra | apply pow2_ge_0]).
        assert (Heq : x ^ 2 + y ^ 2 = (- x) ^ 2 * (1 + (y / x) ^ 2)).
        { replace ((- x) ^ 2) with (x ^ 2) by ring.
          rewrite Rmult_plus_distr_l.
          rewrite Rmult_1_r.
          assert (Htmp : y ^ 2 = x ^ 2 * (y / x) ^ 2).
          { unfold pow; simpl.
            field; exact Hx_nonzero'. }
          rewrite <- Htmp.
          ring. }
        rewrite Heq.
        rewrite sqrt_mult; [ | exact Hx2_nonneg | exact Hterm_nonneg ].
        rewrite sqrt_pow2.
        2: exact Hx_neg_nonneg.
        simpl.
        field.
        split.
        - exact Hsqrt_nonzero.
        - exact Hx_nonzero'.
      * replace (atan (y / x) + PI) with (PI + atan (y / x)) by ring.
        rewrite sin_plus; rewrite sin_PI, cos_PI.
        simpl; replace (sin (atan (y / x)) * (-1) + cos (atan (y / x)) * 0) with (- sin (atan (y / x))) by ring.
        rewrite sin_atan_eq.
        assert (Hsqrt_nonzero : sqrt (1 + (y / x) ^ 2) <> 0).
        { apply Rgt_not_eq, sqrt_lt_R0_c.
          assert (0 <= (y / x) ^ 2) by (apply pow2_ge_0).
          lra. }
        unfold r.
        assert (Hx_neg' : x < 0) by auto.
        assert (Hx_nonzero' : x <> 0) by lra.
        assert (Hx_neg_nonneg : 0 <= -x) by lra.
        assert (Hx2_nonneg : 0 <= (- x) ^ 2) by (apply pow2_ge_0).
        assert (Hterm_nonneg : 0 <= 1 + (y / x) ^ 2) by (apply Rplus_le_le_0_compat; [lra | apply pow2_ge_0]).
        assert (Heq : x ^ 2 + y ^ 2 = (- x) ^ 2 * (1 + (y / x) ^ 2)).
        { replace ((- x) ^ 2) with (x ^ 2) by ring.
          rewrite Rmult_plus_distr_l.
          rewrite Rmult_1_r.
          assert (Htmp : y ^ 2 = x ^ 2 * (y / x) ^ 2).
          { unfold pow; simpl.
            field; exact Hx_nonzero'. }
          rewrite <- Htmp.
          ring. }
        rewrite Heq.
        rewrite sqrt_mult; [ | exact Hx2_nonneg | exact Hterm_nonneg ].
        rewrite sqrt_pow2.
        2: exact Hx_neg_nonneg.
        simpl.
        field.
        split.
        - exact Hsqrt_nonzero.
        - exact Hx_nonzero'.
    + rewrite sin_atan_eq.
      unfold r.
      assert (Hx_pos' : x > 0) by (apply Rnot_le_lt; intro Hle; apply Hx_pos; lra).
      assert (Hx_nonzero' : x <> 0) by lra.
      assert (Hsqrt_nonzero : sqrt (1 + (y / x) ^ 2) <> 0).
      { apply Rgt_not_eq, sqrt_lt_R0_c.
        assert (0 <= (y / x) ^ 2) by (apply pow2_ge_0).
        lra. }
      assert (Hx2_nonneg : 0 <= x ^ 2) by (apply pow2_ge_0).
      assert (Hterm_nonneg : 0 <= 1 + (y / x) ^ 2) by (apply Rplus_le_le_0_compat; [lra | apply pow2_ge_0]).
      assert (Heq : x ^ 2 + y ^ 2 = x ^ 2 * (1 + (y / x) ^ 2)).
      { rewrite Rmult_plus_distr_l.
        rewrite Rmult_1_r.
        assert (Htmp : y ^ 2 = x ^ 2 * (y / x) ^ 2).
        { unfold pow; simpl.
          field; exact Hx_nonzero'. }
        rewrite <- Htmp.
        ring. }
      rewrite Heq.
      rewrite sqrt_mult; [ | exact Hx2_nonneg | exact Hterm_nonneg ].
      rewrite sqrt_pow2.
      2: lra.
      simpl.
      field.
      split.
      - exact Hsqrt_nonzero.
      - exact Hx_nonzero'.
Qed.

(* 复对数指数互逆 *)
Lemma exp_Clog : forall z Hz, Cexp (Clog_principal z Hz) = z.
Proof.
  intros z Hz.
  unfold Clog_principal, Cexp.
  simpl.
  assert (Hz' : 0 < Cnorm z) by (apply Cnorm_pos; auto).
  rewrite exp_ln; [ | exact Hz' ].
  assert (Hr : Cnorm z <> 0) by (apply Rgt_not_eq, Hz').
  unfold Cnorm in *.
  unfold Cnorm_sq in *.
  assert (Hre : Rsqr (re z) = re z ^ 2) by (unfold Rsqr; ring).
  assert (Him : Rsqr (im z) = im z ^ 2) by (unfold Rsqr; ring).
  rewrite Hre, Him in *.
  rewrite (cos_atan2 (im z) (re z) Hr).
  rewrite (sin_atan2 (im z) (re z) Hr).
  simpl.
  destruct z as [a b]; simpl in *.
  replace (a * (a * 1)) with (a ^ 2) by ring.
  replace (b * (b * 1)) with (b ^ 2) by ring.
  assert (Hreal : sqrt (a ^ 2 + b ^ 2) * (a / sqrt (a ^ 2 + b ^ 2)) = a).
  { field; exact Hr. }
  assert (Himag : sqrt (a ^ 2 + b ^ 2) * (b / sqrt (a ^ 2 + b ^ 2)) = b).
  { field; exact Hr. }
  rewrite Hreal, Himag.
  reflexivity.
Qed.

(* atan2 在 x=0 处的值 *)
Lemma atan2_zero : forall y, atan2 y 0 = if Rlt_dec y 0 then -PI/2 else PI/2.
Proof.
  intros y.
  unfold atan2.
  destruct (Req_EM_T 0 0) as [H0 | H0'].
  - simpl. reflexivity.
  - exfalso; apply H0'; reflexivity.
Qed.

(* atan2 的正标量缩放不变性 *)
Lemma atan2_scal_pos : forall a y x, a > 0 -> atan2 (a * y) (a * x) = atan2 y x.
Proof.
  intros a y x Ha.
  unfold atan2.
  destruct (Req_EM_T (a * x) 0) as [Hax0 | Hax0].
  - apply Rmult_integral in Hax0; destruct Hax0 as [Ha0 | Hx0].
    + exfalso; lra.
    + subst x.
      destruct (Req_EM_T 0 0) as [H0 | H0']; [| exfalso; apply H0'; reflexivity].
      clear H0.
      destruct (Rlt_dec y 0) as [Hy_neg | Hy_nonneg];
      destruct (Rlt_dec (a * y) 0) as [Hay_neg | Hay_nonneg];
      try reflexivity.
      * exfalso.
        assert (a * y < 0) by (replace 0 with (a * 0) by ring; apply Rmult_lt_compat_l; [exact Ha | exact Hy_neg]).
        contradiction.
      * exfalso.
        assert (0 <= a * y) by (apply Rmult_le_pos; [apply Rlt_le; exact Ha | apply Rnot_lt_le; assumption]).
        apply Rlt_not_le in Hay_neg; contradiction.
  - assert (Hx_neq0 : x <> 0) by (intro Hx0; subst x; rewrite Rmult_0_r in Hax0; contradiction Hax0; reflexivity).
    assert (Ha_neq0 : a <> 0) by (apply Rgt_not_eq; exact Ha).
    destruct (Rlt_dec x 0) as [Hx_neg | Hx_nonneg].
    + assert (Hax_neg : a * x < 0).
      { replace 0 with (a * 0) by ring.
        apply Rmult_lt_compat_l; [exact Ha | exact Hx_neg]. }
      destruct (Rlt_dec (a * x) 0) as [Hax_neg' | Hax_not_neg]; [| contradiction Hax_not_neg; exact Hax_neg].
      destruct (Req_EM_T x 0) as [Hx_eq0 | Hx_neq0']; [exfalso; apply Hx_neq0; exact Hx_eq0 |].
      clear Hx_neq0'.
      destruct (Rlt_dec y 0) as [Hy_neg | Hy_nonneg'].
      - assert (Hay_neg : a * y < 0).
        { replace 0 with (a * 0) by ring.
          apply Rmult_lt_compat_l; [exact Ha | exact Hy_neg]. }
        destruct (Rlt_dec (a * y) 0) as [Hay_neg' | Hay_not_neg]; [| contradiction Hay_not_neg; exact Hay_neg].
        destruct (Rlt_dec y 0) as [Hy_neg' | Hy_not_neg]; [| contradiction Hy_not_neg; exact Hy_neg].
        assert (Heq : (a * y) / (a * x) = y / x) by (field; split; [exact Hx_neq0 | exact Ha_neq0]).
        rewrite Heq; reflexivity.
      - assert (Hay_ge0 : 0 <= a * y) by (apply Rmult_le_pos; [apply Rlt_le; exact Ha | apply Rnot_lt_le; assumption]).
        destruct (Rlt_dec (a * y) 0) as [Hay_neg | Hay_not_neg]; [exfalso; lra |].
        destruct (Rlt_dec y 0) as [Hy_neg | Hy_not_neg]; [exfalso; lra |].
        assert (Heq : (a * y) / (a * x) = y / x) by (field; split; [exact Hx_neq0 | exact Ha_neq0]).
        rewrite Heq; reflexivity.
    + assert (Hx_pos : x > 0) by lra.
      assert (Hax_pos : a * x > 0) by (apply Rmult_lt_0_compat; [exact Ha | exact Hx_pos]).
      destruct (Rlt_dec (a * x) 0) as [Hax_neg | Hax_not_neg]; [exfalso; lra |].
      destruct (Req_EM_T x 0) as [Hx_eq0 | Hx_neq0']; [exfalso; apply Hx_neq0; exact Hx_eq0 |].
      clear Hx_neq0'.
      assert (Heq : (a * y) / (a * x) = y / x) by (field; split; [exact Hx_neq0 | exact Ha_neq0]).
      rewrite Heq; reflexivity.
Qed.

(* 定理：反正切2与正余弦的恒等式 *)
Theorem atan2_sin_cos : forall θ, -PI < θ <= PI -> atan2 (sin θ) (cos θ) = θ.
Proof.
  intros θ H.
  destruct H as [Hθ_gt Hθ_le].
  unfold atan2.
  destruct (Req_EM_T (cos θ) 0) as [Hcos0 | Hcos_neq0].

  - pose proof (sin2_cos2 θ) as Hsin2.
    unfold Rsqr in Hsin2; rewrite Hcos0 in Hsin2.
    rewrite Rmult_0_l, Rplus_0_r in Hsin2.
    assert (Hsin2' : Rsqr (sin θ) = 1) by (unfold Rsqr; exact Hsin2).
    assert (Hone_sq : Rsqr 1 = 1) by (unfold Rsqr; ring).
    rewrite <- Hone_sq in Hsin2'.
    apply Rsqr_eq in Hsin2'.
    destruct Hsin2' as [Hsin1 | Hsin_neg1].

    + destruct (Rlt_dec θ 0) as [Hθ_neg | Hθ_nonneg].
      * exfalso.
        assert (0 < -θ < PI) as Hpos by (split; lra).
        destruct Hpos as [Hpos1 Hpos2].
        pose proof (sin_gt_0 (-θ) Hpos1) as Hsin_gt0.
        rewrite sin_neg in Hsin_gt0.
        rewrite Hsin1 in Hsin_gt0.
        simpl in Hsin_gt0.
        lra.
      * destruct (Rlt_dec θ (PI/2)) as [Hθ_lt_half | Hθ_ge_half].
        - exfalso.
          assert (Hrange : - (PI/2) < θ < PI/2) by (split; lra).
          destruct Hrange as [Hlow Hhigh].
          pose proof (cos_gt_0 θ Hlow Hhigh) as Hcos_pos.
          rewrite Hcos0 in Hcos_pos.
          lra.
        - destruct (Req_EM_T θ (PI/2)) as [Hθ_eq_half | Hθ_gt_half].
          + destruct (Rlt_dec (sin θ) 0) as [Hsin_neg | Hsin_nonneg].
            * exfalso; rewrite Hsin1 in Hsin_neg; lra.
            * simpl; rewrite Hθ_eq_half; reflexivity.
          + exfalso.
            destruct (Rtotal_order (PI/2) θ) as [Hlt | [Heq | Hgt]].
            - assert (θ < 3 * (PI/2)) by (apply Rle_lt_trans with PI; [exact Hθ_le | lra]).
              pose proof (cos_lt_0 θ Hlt H) as Hcos_neg.
              rewrite Hcos0 in Hcos_neg.
              lra.
            - contradiction Hθ_gt_half; symmetry; exact Heq.
            - contradiction Hθ_ge_half; exact Hgt.

    + destruct (Rlt_dec θ 0) as [Hθ_neg | Hθ_nonneg].
      - destruct (Rlt_dec θ (-PI/2)) as [Hθ_lt | Hθ_ge].
        + exfalso.
          assert (Hneg_pos : -θ > PI/2) by lra.
          assert (Hneg_lt : -θ < PI) by lra.
          assert (Hrange : PI/2 < -θ < 3 * (PI/2)).
          { split; [exact Hneg_pos | apply Rlt_trans with PI; [exact Hneg_lt | lra]]. }
          pose proof (cos_lt_0 (-θ) (proj1 Hrange) (proj2 Hrange)) as Hcos_neg_neg.
          rewrite cos_neg in Hcos_neg_neg.
          rewrite Hcos0 in Hcos_neg_neg.
          apply (Rlt_irrefl 0) in Hcos_neg_neg; assumption.
        + assert (Hplus : 0 <= θ + PI/2 < PI/2) by lra.
          assert (Hsin_plus : sin (θ + PI/2) = 0).
          {
            rewrite sin_plus.
            rewrite Hsin_neg1, Hcos0.
            rewrite cos_PI2, sin_PI2.
            ring.
          }
          destruct (Rle_lt_or_eq_dec 0 (θ + PI/2) (proj1 Hplus)) as [Hplus_gt0 | Hplus_eq0].
          -- exfalso.
             assert (Hsin_gt : sin (θ + PI/2) > 0).
             { apply sin_gt_0.
               - exact Hplus_gt0.
               - apply Rlt_trans with (PI/2); [exact (proj2 Hplus) | lra]. }
             rewrite Hsin_plus in Hsin_gt.
             apply (Rlt_irrefl 0) in Hsin_gt; assumption.
          -- assert (θ = -PI/2) by lra.
             subst θ.
             destruct (Rlt_dec (sin (-PI/2)) 0) as [Hsin_lt | Hsin_ge].
             ++ reflexivity.
             ++ exfalso; rewrite Hsin_neg1 in Hsin_ge; simpl in Hsin_ge; lra.
      - assert (Hθ_ge0 : 0 <= θ) by (apply Rnot_lt_le; exact Hθ_nonneg).
        destruct (Rle_lt_or_eq_dec 0 θ Hθ_ge0) as [Hθ_gt0 | Hθ_eq0].
        + destruct (Rle_lt_or_eq_dec θ PI Hθ_le) as [Hθ_ltPI | Hθ_eqPI].
          * exfalso.
            pose proof (sin_gt_0 θ Hθ_gt0 Hθ_ltPI) as Hsin_pos.
            rewrite Hsin_neg1 in Hsin_pos; simpl in Hsin_pos.
            lra.
          * exfalso.
            subst θ.
            rewrite sin_PI in Hsin_neg1; simpl in Hsin_neg1.
            lra.
        + exfalso.
          subst θ.
          rewrite sin_0 in Hsin_neg1; simpl in Hsin_neg1.
          lra.

  - set (a := atan (sin θ / cos θ)).
    assert (Htan : tan θ = sin θ / cos θ) by (unfold tan; field; assumption).
    destruct (Rlt_dec (cos θ) 0) as [Hcos_neg | Hcos_pos].

    + destruct (Rlt_dec (sin θ) 0) as [Hsin_neg | Hsin_nonneg].

      * assert (Hθ_range : -PI < θ < -PI/2).
        {
          split.
          - exact Hθ_gt.
          - apply Rnot_le_lt. intros Hle.
            destruct (Rle_lt_or_eq_dec (-PI/2) θ Hle) as [Hgt_mhalf | Heq_mhalf].
            + assert (Hθ_range1 : -PI/2 < θ <= PI) by (split; [assumption | exact Hθ_le]).
              destruct (Rlt_dec θ (PI/2)) as [Hlt_half | Hge_half].
              - assert (Heq_div : - PI / 2 = - (PI/2)) by (field; lra).
                rewrite Heq_div in Hgt_mhalf.
                pose proof (cos_gt_0 θ Hgt_mhalf Hlt_half) as Hcos_pos.
                rewrite Hcos_neg in Hcos_pos.
                apply (Rlt_irrefl 0) in Hcos_pos; assumption.
              - destruct (Req_EM_T θ PI) as [Heq_pi | Hneq_pi].
                + subst; rewrite sin_PI in Hsin_neg; simpl in Hsin_neg; lra.
                + assert (Hge_half' : θ >= PI/2) by exact (Rnot_lt_ge θ (PI/2) Hge_half).
                  apply Rge_le in Hge_half'.
                  assert (Hθ_gt0 : 0 < θ) by (apply Rlt_le_trans with (PI/2); [lra | exact Hge_half']).
                  assert (Hθ_ltPI : θ < PI) by (destruct (Rle_lt_or_eq_dec θ PI Hθ_le) as [Hlt | Heq]; [exact Hlt | contradiction Heq]).
                  pose proof (sin_gt_0 θ Hθ_gt0 Hθ_ltPI) as Hsin_pos.
                  rewrite Hsin_neg in Hsin_pos.
                  apply (Rlt_irrefl 0) in Hsin_pos; assumption.
            + subst.
              replace (- PI / 2) with (- (PI/2)) in * by (field; lra).
              assert (Hcos0_val : cos (- (PI/2)) = 0).
              { rewrite cos_neg, cos_PI2; reflexivity. }
              rewrite Hcos0_val in Hcos_neg.
              lra.
        }
        destruct Hθ_range as [Hlow Hhigh].
        assert (Hplus_range : 0 < θ + PI < PI/2) by (split; lra).
        assert (Htan_eq : tan θ = sin θ / cos θ) by (unfold tan; field; lra).
        assert (Htan_plus : tan (θ + PI) = tan θ).
        {
          unfold tan.
          rewrite sin_plus, cos_plus.
          rewrite sin_PI, cos_PI.
          replace (sin θ * (-1) + cos θ * 0) with (- sin θ) by ring.
          replace (cos θ * (-1) - sin θ * 0) with (- cos θ) by ring.
          field.
          exact Hcos_neq0.
        }
        assert (Hatan : atan (tan (θ + PI)) = θ + PI).
        {
          apply atan_tan.
          split; lra.
        }
        rewrite Htan_plus in Hatan.
        unfold a.
        rewrite <- Htan.
        rewrite Hatan.
        ring.

      * assert (Hθ_ge0 : 0 <= θ).
        {
          apply Rnot_lt_le. intro Hθ_lt0.
          assert (Hneg_pos : 0 < -θ < PI) by lra.
          destruct Hneg_pos as [Hpos1 Hpos2].
          pose proof (sin_gt_0 (-θ) Hpos1 Hpos2) as Hsin_gt0.
          rewrite sin_neg in Hsin_gt0.
          apply Rlt_gt in Hsin_gt0.
          rewrite <- Ropp_0 in Hsin_gt0.
          apply Ropp_lt_cancel in Hsin_gt0.
          contradiction Hsin_nonneg.
        }
        assert (Hθ_gt_half : PI/2 < θ).
        {
          apply Rnot_le_lt. intro Hle.
          assert (θ <= PI/2) by exact Hle.
          destruct (Req_EM_T θ 0) as [Hθ0 | Hθ_neq0].
          - subst; rewrite cos_0 in Hcos_neg; simpl in Hcos_neg; lra.
          - assert (Hθ_gt0 : 0 < θ) by lra.
            destruct (Req_EM_T θ (PI/2)) as [Heq | Hneq].
            + subst; rewrite cos_PI2 in Hcos_neg; simpl in Hcos_neg; lra.
            + assert (Hθ_lt_half : θ < PI/2) by lra.
              assert (Hlow : - (PI/2) < θ) by lra.
              pose proof (cos_gt_0 θ Hlow Hθ_lt_half) as Hcos_gt0.
              rewrite Hcos_neg in Hcos_gt0; lra.
        }
        destruct (Req_EM_T θ PI) as [Hθ_eq_PI | Hθ_neq_PI].
        + subst θ.
          unfold a.
          replace (sin PI / cos PI) with 0.
          * rewrite atan_0; ring.
          * rewrite sin_PI, cos_PI; field; lra.
        + assert (Hθ_lt_PI : θ < PI).
          {
            destruct (Rle_lt_or_eq_dec θ PI Hθ_le) as [Hlt | Heq].
            - exact Hlt.
            - exfalso; apply Hθ_neq_PI; exact Heq.
          }
          assert (Hθ_range : PI/2 < θ < PI) by (split; [exact Hθ_gt_half | exact Hθ_lt_PI]).
          assert (Hθ_minus_range : -PI/2 < θ - PI < 0) by lra.
          assert (Htan_minus : tan (θ - PI) = tan θ).
          {
            unfold tan.
            rewrite sin_minus, cos_minus.
            rewrite sin_PI, cos_PI.
            replace (sin θ * 0 - cos θ * (-1)) with (cos θ) by ring.
            replace (cos θ * 0 + sin θ * (-1)) with (- sin θ) by ring.
            field; assumption.
          }
          assert (Hatan_minus : atan (tan (θ - PI)) = θ - PI).
          {
            apply atan_tan.
            split; lra.
          }
          rewrite Htan_minus in Hatan_minus.
          unfold a.
          rewrite <- Htan.
          rewrite Hatan_minus.
          ring.

    + assert (Hθ_range : -PI/2 < θ < PI/2).
      {
        split.
        - apply Rnot_le_lt; intro Hle.
          destruct (Rle_lt_or_eq_dec θ (-PI/2) Hle) as [Hlt | Heq].
          * assert (Hneg_range : PI/2 < -θ < PI) by lra.
            assert (Hneg_range' : PI/2 < -θ < 3 * (PI/2)).
            { split.
              - exact (proj1 Hneg_range).
              - apply Rlt_trans with (r2 := PI); [exact (proj2 Hneg_range) | lra]. }
            pose proof (cos_lt_0 (-θ) (proj1 Hneg_range') (proj2 Hneg_range')) as Hcos_neg.
            rewrite cos_neg in Hcos_neg.
            contradiction Hcos_pos; auto.
          * rewrite Heq in *.
            replace (- PI / 2) with (- (PI/2)) in * by (field; lra).
            rewrite cos_neg, cos_PI2 in Hcos_neq0.
            simpl in Hcos_neq0; lra.
        - apply Rnot_le_lt; intro Hge.
          destruct (Rle_lt_or_eq_dec (PI/2) θ Hge) as [Hgt | Heq].
          * destruct (Req_EM_T θ PI) as [Heq_pi | Hneq_pi].
            + rewrite Heq_pi in *.
              rewrite cos_PI in *.
              simpl in *.
              assert (Hneg : -1 < 0) by lra.
              contradiction Hcos_pos.
            + assert (Hθ_lt_PI : θ < PI).
              { destruct (Rle_lt_or_eq_dec θ PI Hθ_le) as [Hlt | Heq'];
                  [exact Hlt | exfalso; apply Hneq_pi; exact Heq']. }
              assert (Hpos_range : PI/2 < θ < PI) by (split; [exact Hgt | exact Hθ_lt_PI]).
              assert (Hpos_range' : PI/2 < θ < 3 * (PI/2)).
              { split; [exact Hgt | apply Rlt_trans with (r2 := PI); [exact Hθ_lt_PI | lra]]. }
              pose proof (cos_lt_0 θ (proj1 Hpos_range') (proj2 Hpos_range')) as Hcos_neg.
              contradiction Hcos_pos; auto.
          * subst θ.
            rewrite cos_PI2 in Hcos_neq0.
            simpl in Hcos_neq0; lra.
      }
      destruct Hθ_range as [Hlow Hhigh].
      assert (Hatan_eq : atan (tan θ) = θ).
      { apply atan_tan; split; lra. }
      unfold a.
      rewrite <- Htan.
      rewrite Hatan_eq.
      reflexivity.
Qed.

(* 定理：复指数对数互逆 *)
Theorem Clog_exp : forall z, -PI < im z <= PI -> Clog_principal (Cexp z) (Cexp_neq_0 z) = z.
Proof.
  intros z H.
  unfold Clog_principal, Cexp. simpl.
  assert (Hnorm : Cnorm {| re := exp (re z) * cos (im z); im := exp (re z) * sin (im z) |} = exp (re z)).
  {
    unfold Cnorm, Cnorm_sq; simpl.
    set (r := exp (re z)). set (c := cos (im z)). set (s := sin (im z)).
    assert (Hsq : (r * c) * (r * c) + (r * s) * (r * s) = r * r).
    {
      replace ((r * c) * (r * c)) with (r * r * (c * c)) by ring.
      replace ((r * s) * (r * s)) with (r * r * (s * s)) by ring.
      rewrite <- Rmult_plus_distr_l.
      assert (Htrig : c * c + s * s = 1).
      {
        rewrite Rplus_comm.
        apply sin2_cos2.
      }
      rewrite Htrig.
      rewrite Rmult_1_r.
      reflexivity.
    }
    unfold Rsqr in *.
    rewrite Hsq.
    apply sqrt_square.
    apply Rlt_le.
    apply exp_pos.
  }
  assert (Hre : ln (∥ Cexp z ∥) = re z).
  {
    unfold Cexp.
    rewrite Hnorm.
    apply ln_exp.
  }
  assert (Hpos : 0 < exp (re z)) by apply exp_pos.
  assert (Harg_eq : atan2 (exp (re z) * sin (im z)) (exp (re z) * cos (im z)) = atan2 (sin (im z)) (cos (im z))).
  {
    apply atan2_scal_pos with (a := exp (re z)); auto.
  }
  assert (Harg : atan2 (sin (im z)) (cos (im z)) = im z).
  {
    apply atan2_sin_cos; exact H.
  }
  rewrite Harg_eq. rewrite Harg.
  replace (ln (∥ (exp (re z) * cos (im z)) +i (exp (re z) * sin (im z)) ∥)) with (ln (∥ Cexp z ∥)) by (unfold Cexp; reflexivity).
  rewrite Hre.
  destruct z; simpl; reflexivity.
Qed.

(* 模平方非零 *)
Lemma Cnorm_sq_neq_0 : forall z, z <> C0 -> Cnorm_sq z <> 0.
Proof.
  intros z Hz. unfold Cnorm_sq. intro H.
  assert (Hre1 : 0 <= Rsqr (re z)) by apply Rle_0_sqr.
  assert (Him1 : 0 <= Rsqr (im z)) by apply Rle_0_sqr.
  assert (Hre_le : Rsqr (re z) <= Rsqr (re z) + Rsqr (im z)).
  { replace (Rsqr (re z)) with (Rsqr (re z) + 0) at 1 by ring.
    apply Rplus_le_compat_l. exact Him1. }
  rewrite H in Hre_le.
  assert (Hre0 : Rsqr (re z) = 0).
  { apply Rle_antisym; [exact Hre_le | exact Hre1]. }
  apply Rsqr_eq_0 in Hre0.
  assert (Him_le : Rsqr (im z) <= Rsqr (re z) + Rsqr (im z)).
  { replace (Rsqr (im z)) with (0 + Rsqr (im z)) at 1 by ring.
    apply Rplus_le_compat_r. exact Hre1. }
  rewrite H in Him_le.
  assert (Him0 : Rsqr (im z) = 0).
  { apply Rle_antisym; [exact Him_le | exact Him1]. }
  apply Rsqr_eq_0 in Him0.
  destruct z as [a b].
  simpl in Hre0, Him0.
  subst a b.
  apply Hz.
  reflexivity.
Qed.

(* 非零复数模平方非零 *)
Lemma nonzero_norm_sq_nonzero : forall (z : Complex), z <> C0 -> Cnorm_sq z <> 0.
Proof.
  intros z Hnz.
  apply Cnorm_sq_neq_0; assumption.
Qed.

(* 复指数加法公式 *)
Lemma Cexp_add : forall z1 z2, Cexp (z1 +c z2) = Cexp z1 *c Cexp z2.
Proof.
  intros [a1 b1] [a2 b2]; unfold Cexp, Cadd, Cmul; simpl.
  rewrite exp_plus, cos_plus, sin_plus.
  simpl.
  replace (exp a1 * exp a2 * (cos b1 * cos b2 - sin b1 * sin b2)) with
      (exp a1 * cos b1 * (exp a2 * cos b2) - exp a1 * sin b1 * (exp a2 * sin b2)) by ring.
  replace (exp a1 * exp a2 * (sin b1 * cos b2 + cos b1 * sin b2)) with
      (exp a1 * cos b1 * (exp a2 * sin b2) + exp a1 * sin b1 * (exp a2 * cos b2)) by ring.
  reflexivity.
Qed.

(* 实部绝对值不大于模 *)
Lemma re_le_Cnorm : forall z, Rabs (re z) <= Cnorm z.
Proof.
  intros [a b]; unfold Cnorm, Cnorm_sq; simpl.
  rewrite <- (sqrt_Rsqr_abs a).
  apply sqrt_le_1_c.
  - apply Rle_0_sqr.
  - apply Rplus_le_le_0_compat; apply Rle_0_sqr.
  - rewrite <- Rplus_0_r at 1.
    apply Rplus_le_compat_l.
    apply Rle_0_sqr.
Qed.

(* 模非负 *)
Lemma Cnorm_ge_0 : forall z, 0 <= Cnorm z.
Proof.
  intros z; unfold Cnorm; apply sqrt_pos.
Qed.

(* e的1次方小于3 *)
Lemma exp_1_lt_3 : exp 1 < 3.
Proof.
  exact TaylorTheorem.exp_1_lt_3.
Qed.

(* e的1次方小于等于3 *)
Lemma exp_1_le_3 : exp 1 <= 3.
Proof. apply Rlt_le, exp_1_lt_3. Qed.

Require Import Coquelicot.Coquelicot.

(* 定理：余弦差估计 *)
Theorem cos_est : forall y, Rabs y <= 1/2 -> Rabs (cos y - 1) <= y^2 / 2.
Proof.
  intros y Hy.
  assert (Hgen : forall w, cos (w + w) - 1 = - 2 * (sin w) ^ 2).
  { intro w. rewrite cos_plus.
    pose proof (sin2_cos2 w) as Ht. unfold Rsqr in Ht. lra. }
  assert (Hd : cos y - 1 = - 2 * (sin (y/2)) ^ 2).
  { pose proof (Hgen (y/2)) as H2.
    replace (cos y) with (cos (y/2 + y/2)) by (f_equal; field).
    exact H2. }
  rewrite Hd, Rabs_mult.
  replace (Rabs (- 2)) with 2 by (rewrite Rabs_left; [ring | lra]).
  replace (Rabs 2) with 2 by (rewrite Rabs_right; [reflexivity | lra]).
  assert (Hsq : 0 <= (sin (y/2)) ^ 2).
  { rewrite <- Rsqr_pow2. apply Rle_0_sqr. }
  rewrite (Rabs_pos_eq ((sin (y/2)) ^ 2) Hsq).
  assert (Heq : Rabs (y/2) = Rabs y / 2).
  { unfold Rdiv. rewrite Rabs_mult.
    rewrite (Rabs_pos_eq (/2)) by lra. reflexivity. }
  assert (Hsin : Rabs (sin (y/2)) <= Rabs y / 2).
  { apply Rle_trans with (Rabs (y/2)).
    - apply TaylorTheorem.sin_le_abs. rewrite Heq. lra.
    - rewrite Heq. apply Rle_refl. }
  assert (Hss : Rabs (sin (y/2)) * Rabs (sin (y/2)) = (sin (y/2)) ^ 2).
  { replace (Rabs (sin (y/2)) * Rabs (sin (y/2)))
      with (Rsqr (Rabs (sin (y/2)))) by (unfold Rsqr; reflexivity).
    rewrite <- Rsqr_abs. apply Rsqr_pow2. }
  replace (y ^ 2 / 2) with (2 * ((Rabs y / 2) * (Rabs y / 2))).
  2:{ assert (Hyy : Rabs y * Rabs y = y * y).
      { replace (Rabs y * Rabs y) with (Rsqr (Rabs y)) by (unfold Rsqr; reflexivity).
        rewrite <- Rsqr_abs. unfold Rsqr. reflexivity. }
      replace ((Rabs y / 2) * (Rabs y / 2)) with ((Rabs y * Rabs y) / 4) by field.
      rewrite Hyy. replace (y * y) with (y ^ 2) by (simpl; ring). field. }
  apply Rmult_le_compat_l; [lra |].
  rewrite <- Hss.
  apply Rmult_le_compat;
    [apply Rabs_pos | apply Rabs_pos | exact Hsin | exact Hsin].
Qed.

(* 定理：正弦差估计 *)
Theorem sin_est : forall y, Rabs y <= 1/2 -> Rabs (sin y - y) <= (Rabs y)^3 / 6.
Proof. exact TaylorTheorem.sin_est_series. Qed.

(* 指数上界 *)
Lemma exp_bound : forall x, Rabs x <= 1/2 -> exp x <= 2.
Proof.
  intros x Hx.
  destruct (Rle_lt_dec 0 x) as [Hge|Hlt].
  - assert (Hx2 : x <= 1/2).
    { rewrite (Rabs_pos_eq x Hge) in Hx. exact Hx. }
    destruct (TaylorTheorem.exp_est_pos x Hge Hx2) as [Hlo Hhi].
    replace (x ^ 2) with (x * x) in Hhi by (simpl; ring).
    assert (Hxx : x * x <= 1 / 4).
    { replace (1 / 4) with ((1/2) * (1/2)) by (field; try discrR). apply Rmult_le_compat; lra. }
    assert (H25 : 2 * (x * x) <= 1 / 2).
    { replace (1 / 2) with (2 * (1 / 4)) by field.
      apply Rmult_le_compat_l; [lra | exact Hxx]. }
    assert (Hchain : exp x <= 2 * (x * x) + 1 + x) by lra.
    lra.
  - set (u := - x).
    assert (Hu0 : 0 < u) by (unfold u; lra).
    assert (Hu1 : u <= 1/2).
    { unfold u. rewrite (Rabs_left x) in Hx by lra. lra. }
    assert (Hpos : 0 < exp u) by apply exp_pos.
    assert (Hge1 : 1 <= exp u).
    { destruct (TaylorTheorem.exp_est_pos u (Rlt_le _ _ Hu0) Hu1) as [Hlo _].
      lra. }
    assert (Heq : exp x * exp u = 1).
    { rewrite <- exp_plus. replace x with (- u) by (unfold u; ring).
      replace (- u + u) with 0 by ring. rewrite exp_0. reflexivity. }
    assert (Hne : exp u <> 0) by lra.
    assert (HinvE : exp x = / exp u).
    { rewrite <- (Rmult_1_r (exp x)).
      rewrite <- (Rinv_r (exp u) Hne).
      rewrite <- Rmult_assoc, Heq, Rmult_1_l. reflexivity. }
    assert (Hle : exp x <= 1).
    { rewrite HinvE.
      apply Rle_trans with (/ 1).
      - apply Rinv_le_contravar; lra.
      - replace (/ 1) with 1 by field. apply Rle_refl. }
    lra.
Qed.

(* 复数范数分量不等式 *)
Lemma Cnorm_le_components : forall h,
  Rabs (re h) <= Cnorm h /\ Rabs (im h) <= Cnorm h.
Proof.
  intro h.
  unfold Cnorm, Cnorm_sq.
  split.
  - rewrite <- (sqrt_Rsqr_abs (re h)).
    apply sqrt_le_1_c.
    + apply Rle_0_sqr.
    + apply Rplus_le_le_0_compat; apply Rle_0_sqr.
    + rewrite <- (Rplus_0_r (Rsqr (re h))) at 1.
      apply Rplus_le_compat_l.
      apply Rle_0_sqr.
  - rewrite <- (sqrt_Rsqr_abs (im h)).
    apply sqrt_le_1_c.
    + apply Rle_0_sqr.
    + apply Rplus_le_le_0_compat; apply Rle_0_sqr.
    + rewrite <- (Rplus_0_l (Rsqr (im h))) at 1.
      apply Rplus_le_compat_r.
      apply Rle_0_sqr.
Qed.

(* 复数乘法模等式 *)
Lemma Cnorm_mult : forall z1 z2, Cnorm (z1 *c z2) = Cnorm z1 * Cnorm z2.
Proof.
  intros z1 z2.
  unfold Cnorm.
  apply eq_sym.
  rewrite <- sqrt_mult.
  - f_equal.
    unfold Cnorm_sq, Cmul, Rsqr; simpl.
    destruct z1 as [a1 b1]; destruct z2 as [a2 b2]; simpl.
    ring.
  - apply Rplus_le_le_0_compat; apply Rle_0_sqr.
  - apply Rplus_le_le_0_compat; apply Rle_0_sqr.
Qed.

(* 阶乘下界幂 *)
Lemma fact_ge_pow2 : forall n, (1 <= n)%nat -> INR (fact n) >= 2 ^ (n - 1).
Proof.
  intros n Hn.
  induction n as [| n' IH]; [lia |].
  destruct n' as [| n''].
  - simpl.
    replace (1 - 1)%nat with 0%nat by lia.
    simpl.
    apply Rge_refl.
  - rewrite fact_simpl.
    rewrite mult_INR.
    assert (Hn''_ge_1: (1 <= S n'')%nat) by lia.
    specialize (IH Hn''_ge_1).
    replace (S (S n'') - 1)%nat with (S n'')%nat by lia.
    assert (H_ge_2: INR (S (S n'')) >= 2).
    {
      rewrite !S_INR.
      replace (INR n'' + 1 + 1) with (INR n'' + 2) by ring.
      apply Rle_ge.
      assert (0 <= INR n'') by apply pos_INR.
      lra.
    }
    assert (H1: INR (S (S n'')) * INR (fact (S n'')) >= 2 * INR (fact (S n''))).
    {
      apply Rmult_ge_compat_r.
      - apply Rle_ge. apply pos_INR.
      - exact H_ge_2.
    }
    assert (H2: 2 * INR (fact (S n'')) >= 2 ^ (S n'')).
    {
      replace (2 ^ (S n''))%R with (2 * 2 ^ n'')%R.
      - apply Rmult_ge_compat_l.
        + lra.
        + replace (2 ^ n'')%R with (2 ^ (S n'' - 1))%R.
          * exact IH.
          * f_equal.
            lia.
      - replace (2 ^ S n'')%R with (2 ^ (n'' + 1))%R by (f_equal; lia).
        rewrite pow_add.
        simpl.
        ring.
    }
    apply Rge_trans with (2 * INR (fact (S n''))); [exact H1 | exact H2].
Qed.

(* 绝对值区间估计 *)
Lemma Rabs_le_interval : forall x a, Rabs x <= a -> -a <= x <= a.
Proof.
  intros x a H.
  split.
  - apply Ropp_le_cancel.
    rewrite Ropp_involutive.
    apply Rle_trans with (Rabs x).
    + rewrite <- (Rabs_Ropp x).
      apply Rle_abs.
    + exact H.
  - apply Rle_trans with (Rabs x).
    + apply Rle_abs.
    + exact H.
Qed.

(* 定理：指数差估计 *)
Theorem exp_est : forall x, Rabs x <= 1/2 -> Rabs (exp x - 1 - x) <= 2 * x^2.
Proof. exact TaylorTheorem.exp_est_series. Qed.

Import ComplexNumbers.

(* 复数乘法对减法的右分配律 *)
Lemma Cmul_sub_distr_r : forall a b c, (a -c b) *c c = a*c c -c b*c c.
Proof.
  intros. unfold Csub, Cmul. destruct a, b, c; simpl. f_equal; ring.
Qed.

(* 定理：指数差商极限 *)
Theorem limit_exp_minus_1_over_h : 
  forall eps : R, eps > 0 ->
  exists delta : R, delta > 0 /\
  forall h : Complex, forall Hpos : 0 < Cnorm h,
    Cnorm h < delta ->
    Cnorm (Cdiv (Csub (Cexp h) C1) h (nonzero_if_norm_positive h Hpos) -c C1) < eps.
Proof.
  intros eps Heps.
  set (delta0 := eps / 6).
  assert (delta0_pos : 0 < delta0) by (apply Rdiv_lt_0_compat; [assumption | lra]).
  exists (Rmin (1/2) delta0). split.
  - apply Rmin_glb_lt; [lra | exact delta0_pos].
  - intros h Hpos Hnorm.
    assert (Hh_le_half : Cnorm h <= 1/2).
    { apply Rle_trans with (Rmin (1/2) delta0); [apply Rlt_le; exact Hnorm | apply Rmin_l]. }
    set (a := re h). set (b := im h).

    assert (Hb_abs : Rabs b <= Cnorm h).
    {
      unfold Cnorm, Cnorm_sq; simpl.
      rewrite <- (sqrt_Rsqr_abs b).
      apply sqrt_le_1_c.
      - apply Rle_0_sqr.
      - apply Rplus_le_le_0_compat; [apply Rle_0_sqr | apply Rle_0_sqr].
      - rewrite Rplus_comm.
        replace ((Rabs b)²) with (b²) by apply Rsqr_abs.
        rewrite <- Rplus_0_r at 1.
        apply Rplus_le_compat_l.
        apply Rle_0_sqr.
    }

    assert (Ha_abs : Rabs a <= Cnorm h).
    {
      unfold Cnorm, Cnorm_sq; simpl.
      rewrite <- (sqrt_Rsqr_abs a).
      apply sqrt_le_1_c.
      - apply Rle_0_sqr.
      - apply Rplus_le_le_0_compat; [apply Rle_0_sqr | apply Rle_0_sqr].
      - rewrite Rplus_comm.
        replace ((Rabs a)²) with (a²) by apply Rsqr_abs.
        rewrite <- Rplus_0_l at 1.
        apply Rplus_le_compat_r.
        apply Rle_0_sqr.
    }

    set (r := Cnorm h).
    assert (r_lt_delta0 : r < delta0).
    { apply Rlt_le_trans with (Rmin (1/2) delta0).
      - exact Hnorm.
      - apply Rmin_r. }

    assert (Ha_le_half : Rabs a <= 1/2) by (apply Rle_trans with r; [apply Ha_abs | exact Hh_le_half]).
    assert (Hb_le_half : Rabs b <= 1/2) by (apply Rle_trans with r; [apply Hb_abs | exact Hh_le_half]).

    assert (Hexp_a : Rabs (exp a - 1 - a) <= 2 * a ^ 2).
    { apply exp_est; exact Ha_le_half. }

    assert (Hcos_b : Rabs (cos b - 1) <= b² / 2).
    {
      replace (b² / 2) with (b ^ 2 / 2) by (rewrite Rsqr_pow2; reflexivity).
      apply cos_est; exact Hb_le_half.
    }

    assert (Hsin_b : Rabs (sin b - b) <= (Rabs b) ^ 3 / 6).
    { apply sin_est; exact Hb_le_half. }

    assert (Hexp_a_1 : Rabs (exp a - 1) <= Rabs a + 2 * a ^ 2).
    {
      replace (exp a - 1) with ((exp a - 1 - a) + a) by ring.
      apply Rle_trans with (Rabs (exp a - 1 - a) + Rabs a).
      - apply Rabs_triang.
      - rewrite Rplus_comm. apply Rplus_le_compat.
        + apply Rle_refl.
        + exact Hexp_a.
    }
    assert (Hsin_abs_le_abs : forall x, Rabs x <= 1/2 -> Rabs (sin x) <= Rabs x).
    { exact TaylorTheorem.sin_le_abs. }

    assert (Ha_bound : Rabs a <= r) by exact Ha_abs.
    assert (Hb_bound : Rabs b <= r) by exact Hb_abs.

    assert (H1 : Rabs (exp a * cos b - 1 - a) <= b² + 2 * a ^ 2).
    {
      replace (exp a * cos b - 1 - a) with (exp a * (cos b - 1) + (exp a - 1 - a)) by ring.
      eapply Rle_trans.
      - apply Rabs_triang.
      - apply Rplus_le_compat.
        + rewrite Rabs_mult.
          assert (Hexp_a_le2 : Rabs (exp a) <= 2).
          { rewrite Rabs_pos_eq; [| apply Rlt_le; apply exp_pos].
            apply exp_bound; exact Ha_le_half. }
          apply Rle_trans with (2 * Rabs (cos b - 1)).
          * apply Rmult_le_compat_r; [apply Rabs_pos | exact Hexp_a_le2].
          * apply Rle_trans with (2 * (b² / 2)).
            -- apply Rmult_le_compat_l; [lra | exact Hcos_b].
            -- replace (2 * (b² / 2)) with b² by field.
               apply Rle_refl.
        + exact Hexp_a.
    }

    assert (H2 : Rabs (exp a * sin b - b) <= (Rabs b)^3 / 3 + Rabs b * (Rabs a + 2 * a^2)).
    {
      replace (exp a * sin b - b) with (exp a * (sin b - b) + b * (exp a - 1)) by ring.
      eapply Rle_trans.
      - apply Rabs_triang.
      - apply Rplus_le_compat.
        + rewrite Rabs_mult.
          assert (Hexp_a_le2 : Rabs (exp a) <= 2).
          { rewrite Rabs_pos_eq; [| apply Rlt_le; apply exp_pos].
            apply exp_bound; exact Ha_le_half. }
          apply Rle_trans with (2 * ((Rabs b)^3 / 6)).
          * apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | apply Hexp_a_le2 | apply Hsin_b].
          * replace (2 * ((Rabs b)^3 / 6)) with ((Rabs b)^3 / 3) by field; apply Rle_refl.
        + rewrite Rabs_mult.
          apply Rmult_le_compat_l; [apply Rabs_pos | exact Hexp_a_1].
    }

    assert (r_pos : 0 < r) by exact Hpos.

    assert (Hreal_bound : Rabs (exp a * cos b - 1 - a) <= 3 * r^2).
    {
      apply Rle_trans with (b² + 2 * a ^ 2).
      - exact H1.
      - assert (Hb2_le_r2 : b² <= r^2).
        {
          rewrite Rsqr_abs.
          apply Rle_trans with (r * r).
          + apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | apply Hb_bound | apply Hb_bound].
          + replace (r ^ 2)%R with (r * r)%R by (simpl; ring).
            apply Rle_refl.
        }
        assert (Ha2_le_r2 : a ^ 2 <= r ^ 2).
        {
          rewrite <- (pow2_abs a).
          apply pow_incr.
          split; [apply Rabs_pos | exact Ha_bound].
        }
        apply Rle_trans with (r^2 + 2 * r^2).
        + apply Rplus_le_compat.
          * exact Hb2_le_r2.
          * apply Rmult_le_compat_l; [lra | exact Ha2_le_r2].
        + replace (r^2 + 2 * r^2) with (3 * r^2) by ring.
          apply Rle_refl.
    }

    assert (Himag_bound : Rabs (exp a * sin b - b) <= (13/6) * r^2).
    {
      apply Rle_trans with ((Rabs b)^3 / 3 + Rabs b * (Rabs a + 2 * a^2)).
      - exact H2.
      - assert (Hb_cube_le : (Rabs b)^3 <= r^3).
        {
          apply pow_incr.
          split.
          - apply Rabs_pos.
          - exact Hb_bound.
        }
        assert (Hb_le_r : Rabs b <= r) by exact Hb_bound.
        assert (Ha_le_r : Rabs a <= r) by exact Ha_bound.
        assert (Ha2_le_r2 : a^2 <= r^2).
        {
          rewrite <- (pow2_abs a).
          apply pow_incr.
          split.
          - apply Rabs_pos.
          - exact Ha_bound.
        }
        assert (Htmp1 : (Rabs b)^3 / 3 <= r^3 / 3).
        {
          unfold Rdiv. apply Rmult_le_compat_r.
          - apply Rlt_le, Rinv_0_lt_compat; lra.
          - exact Hb_cube_le.
        }
        assert (Htmp2 : Rabs b * (Rabs a + 2 * a^2) <= r * (r + 2 * r^2)).
        {
          apply Rmult_le_compat.
          - apply Rabs_pos.
          - apply Rplus_le_le_0_compat; [apply Rabs_pos | apply Rmult_le_pos; [lra | apply pow2_ge_0]].
          - exact Hb_le_r.
          - apply Rplus_le_compat.
            + exact Ha_le_r.
            + apply Rmult_le_compat_l; [lra | exact Ha2_le_r2].
        }
        apply Rle_trans with (r^3 / 3 + r * (r + 2 * r^2)).
        + apply Rplus_le_compat; [exact Htmp1 | exact Htmp2].
        + replace (r * (r + 2 * r^2)) with (r^2 + 2 * r^3) by ring.
          replace (r^3 / 3 + (r^2 + 2 * r^3)) with (r^2 + (7/3) * r^3) by (field; lra).
          assert (r_le_half : r <= 1/2) by exact Hh_le_half.
          assert (0 <= r) by (apply Rlt_le; exact r_pos).
          apply Rle_trans with (r^2 + (7/3) * (r^2 * (1/2))).
          + apply Rplus_le_compat_l.
            apply Rmult_le_compat_l.
            * lra.
            * replace (r^3)%R  with (r^2 * r) by ring.
              apply Rmult_le_compat_l.
              - apply pow2_ge_0.
              - exact r_le_half.
          + replace (r^2 + (7/3) * (r^2 * (1/2))) with (r^2 * (1 + 7/6)) by (field; lra).
            replace (1 + 7/6) with (13/6) by (field; lra).
            rewrite Rmult_comm.
            apply Rle_refl.
    }

    assert (total_bound : Rabs (exp a * cos b - 1 - a) + Rabs (exp a * sin b - b) <= (31/6) * r^2).
    {
      apply Rle_trans with (3 * r^2 + (13/6) * r^2).
      - apply Rplus_le_compat; [exact Hreal_bound | exact Himag_bound].
      - replace (3 * r^2 + (13/6) * r^2) with ((31/6) * r^2) by field.
        apply Rle_refl.
    }

    assert (Cnorm_le_sum_abs : forall z, Cnorm z <= Rabs (re z) + Rabs (im z)).
    {
      intros z.
      apply Rsqr_incr_0.
      - unfold Cnorm, Cnorm_sq; rewrite Rsqr_sqrt.
        2: apply Rplus_le_le_0_compat; [apply Rle_0_sqr | apply Rle_0_sqr].
        rewrite (Rsqr_abs (re z)), (Rsqr_abs (im z)).
        assert (Hsq : (Rabs (re z) + Rabs (im z))² = 
                      (Rabs (re z))² + (Rabs (im z))² + 2 * Rabs (re z) * Rabs (im z))
          by (unfold Rsqr; ring).
        rewrite Hsq.
        rewrite Rplus_assoc.
        apply Rplus_le_compat_l.
        replace ((Rabs (im z))²) with ((Rabs (im z))² + 0) by ring.
        apply Rplus_le_compat.
        + rewrite Rplus_0_r. apply Rle_refl.
        + apply Rmult_le_pos.
          * apply Rmult_le_pos; [lra | apply Rabs_pos].
          * apply Rabs_pos.
      - apply Cnorm_ge_0.
      - apply Rplus_le_le_0_compat; apply Rabs_pos.
    }

    assert (bound1 : (31/6) * r^2 <= (31/12) * r).
    {
      replace ((31/12) * r) with ((31/6) * ((1/2) * r)) by (field; lra).
      apply Rmult_le_compat_l; [lra |].
      replace (r^2)%R  with (r * r) by ring.
      apply Rmult_le_compat;
        [apply Rlt_le; exact r_pos | apply Rlt_le; exact r_pos | exact Hh_le_half | apply Rle_refl].
    }

    set (u := Csub (Csub (Cexp h) C1) h).
    assert (re_Cexp_eq : re (Cexp h) = exp a * cos b).
    { unfold Cexp; simpl. reflexivity. }
    assert (im_Cexp_eq : im (Cexp h) = exp a * sin b).
    { unfold Cexp; simpl. reflexivity. }
    assert (Cnorm_u_le : Cnorm u <= (31/6) * r^2).
    {
      apply Rle_trans with (Rabs (re u) + Rabs (im u)).
      - apply Cnorm_le_sum_abs.
      - unfold re, im, u; simpl.
        replace (re h) with a by reflexivity.
        replace (im h) with b by reflexivity.
        rewrite Rminus_0_r.
        replace (r * (r * 1)) with (r^2)%R  by (rewrite Rmult_1_r; ring).
        exact total_bound.
    }

    assert (Cnorm_one : Cnorm C1 = 1).
    {
      unfold Cnorm, Cnorm_sq, C1; simpl.
      replace (Rsqr 1) with 1 by (unfold Rsqr; ring).
      replace (Rsqr 0) with 0 by (unfold Rsqr; ring).
      rewrite Rplus_0_r.
      rewrite sqrt_1.
      reflexivity.
    }

    assert (Cnorm_inv : forall w (Hw : w <> C0),
        Cnorm (Cinv w (nonzero_norm_sq_nonzero w Hw)) = / Cnorm w).
    {
      intros w Hw.
      set (Hnz := nonzero_norm_sq_nonzero w Hw).
      assert (Hw_norm_pos : 0 < Cnorm w) by apply Cnorm_pos, Hw.
      assert (Hw_norm_neq0 : Cnorm w <> 0) by (apply Rgt_not_eq; exact Hw_norm_pos).
      apply Rmult_eq_reg_l with (Cnorm w); [| exact Hw_norm_neq0].
      rewrite <- Cnorm_mult.
      assert (Hprod : Cmul w (Cinv w Hnz) = C1).
      {
        unfold Cmul, Cinv. destruct w as [x y]. simpl.
        unfold Cnorm_sq; simpl.
        set (nsq := Rsqr x + Rsqr y).
        assert (nsq_neq0 : nsq <> 0) by exact Hnz.
        assert (Hre : x * (x / nsq) - y * (- y / nsq) = 1).
        {
          unfold Rdiv.
          replace (x * (x * / nsq) - y * (- y * / nsq)) with (nsq * / nsq).
          - rewrite Rinv_r; [reflexivity | exact nsq_neq0].
          - unfold nsq, Rsqr; ring.
        }
        assert (Him : x * (- y / nsq) + y * (x / nsq) = 0).
        {
          unfold Rdiv.
          ring.
        }
        rewrite Hre, Him.
        unfold C1; reflexivity.
      }
      rewrite Hprod, Cnorm_one.
      field; exact Hw_norm_neq0.
    }

    assert (h_neq0' : h <> C0).
    { intro Heq; rewrite Heq in Hpos; unfold Cnorm, Cnorm_sq, C0 in Hpos; simpl in Hpos; rewrite Rsqr_0, Rplus_0_l, sqrt_0 in Hpos; lra. }
    set (Hnz' := nonzero_if_norm_positive h Hpos).

    assert (Cinv_r : Cmul h (Cinv h Hnz') = C1).
    {
      destruct h as [x y]; simpl.
      unfold Cnorm_sq in Hnz'; simpl in Hnz'.
      set (nsq := Rsqr x + Rsqr y).
      assert (nsq_neq0 : nsq <> 0) by exact Hnz'.
      unfold Cinv; simpl.
      unfold Rdiv.
      unfold Cmul; simpl.
      assert (Hre : x * (x * / nsq) - y * (- y * / nsq) = 1).
      {
        replace (x * (x * / nsq) - y * (- y * / nsq)) with (nsq * / nsq).
        - rewrite Rinv_r; [reflexivity | exact nsq_neq0].
        - unfold nsq, Rsqr; ring.
      }
      assert (Him : x * (- y * / nsq) + y * (x * / nsq) = 0).
      {
        ring.
      }
      replace (Cnorm_sq (x +i y)) with nsq by (unfold Cnorm_sq; simpl; reflexivity).
      rewrite Hre, Him.
      unfold C1; reflexivity.
    }

    assert (Cnorm_target_eq : Cnorm (Cdiv (Cexp h -c C1) h Hnz' -c C1) = Cnorm u / r).
    {
      set (inv_h := Cinv h Hnz').
      assert (Htemp: Cdiv (Cexp h -c C1) h Hnz' -c C1 = Cmul u inv_h).
      {
        unfold Cdiv.
        rewrite <- Cinv_r at 2.
        rewrite <- Cmul_sub_distr_r.
        unfold u; reflexivity.
      }
      rewrite Htemp.
      rewrite Cnorm_mult.
      assert (Cnorm_inv_h : Cnorm inv_h = / r).
      {
        apply Rmult_eq_reg_l with (Cnorm h).
        - unfold inv_h; rewrite <- Cnorm_mult.
          rewrite Cinv_r.
          rewrite Cnorm_one.
          replace (Cnorm h) with r by reflexivity.
          rewrite Rinv_r; [reflexivity | apply Rgt_not_eq; exact r_pos].
        - apply Rgt_not_eq; exact r_pos.
      }
      rewrite Cnorm_inv_h.
      reflexivity.
    }

    rewrite Cnorm_target_eq.

    apply Rle_lt_trans with (((31/6) * r^2) / r).
    - apply Rmult_le_compat_r; [apply Rlt_le; apply Rinv_0_lt_compat; exact r_pos | exact Cnorm_u_le].
    - replace (((31/6) * r^2) / r) with ((31/6) * r) by (field; apply Rgt_not_eq; exact r_pos).
    apply Rlt_trans with ((31/6) * delta0).
    - apply Rmult_lt_compat_l; [lra | exact r_lt_delta0].
    - unfold delta0.
      field_simplify.
      replace (31 * eps / 36) with (31/36 * eps) by field.
      rewrite <- (Rmult_1_l eps) at 2.
      apply Rmult_lt_compat_r; [exact Heps | lra].
Qed.

(* 复数乘法对减法的左分配律 *)
Lemma Csub_mult_distr_r : forall a b c, a *c (b -c c) = a *c b -c a *c c.
Proof.
  intros a b c.
  destruct a as [a1 a2]; destruct b as [b1 b2]; destruct c as [c1 c2].
  unfold Csub, Cmul; simpl.
  f_equal; ring.
Qed.

(* 复数除法乘取消去律 *)
Lemma Cdiv_mult_cancel_l : forall a b (Hb : Cnorm_sq b <> 0), Cdiv (a *c b) b Hb = a.
Proof.
  intros a b Hb.
  destruct a as [a1 a2]; destruct b as [b1 b2].
  unfold Cdiv, Cmul, Cinv, Cnorm_sq; simpl.
  set (nsq := Rsqr b1 + Rsqr b2) in *.
  assert (nsq_neq0 : nsq <> 0) by exact Hb.
  unfold Rdiv.
  f_equal.
  - assert (Htmp: (a1 * b1 - a2 * b2) * (b1 * / nsq) - (a1 * b2 + a2 * b1) * (- b2 * / nsq) =
                  / nsq * ((a1 * b1 - a2 * b2) * b1 + (a1 * b2 + a2 * b1) * b2)).
    { unfold Rdiv; ring. }
    rewrite Htmp.
    replace ((a1 * b1 - a2 * b2) * b1 + (a1 * b2 + a2 * b1) * b2) with (a1 * nsq).
    2: { unfold nsq, Rsqr; ring. }
    rewrite Rmult_comm. rewrite Rmult_assoc. rewrite Rinv_r; [| exact nsq_neq0].
    rewrite Rmult_1_r. reflexivity.
  - assert (Htmp: (a1 * b1 - a2 * b2) * (- b2 * / nsq) + (a1 * b2 + a2 * b1) * (b1 * / nsq) =
                  / nsq * ((a1 * b1 - a2 * b2) * (- b2) + (a1 * b2 + a2 * b1) * b1)).
    { unfold Rdiv; ring. }
    rewrite Htmp.
    replace ((a1 * b1 - a2 * b2) * (- b2) + (a1 * b2 + a2 * b1) * b1) with (a2 * nsq).
    2: { unfold nsq, Rsqr; ring. }
    rewrite Rmult_comm. rewrite Rmult_assoc. rewrite Rinv_r; [| exact nsq_neq0].
    rewrite Rmult_1_r. reflexivity.
Qed.

(* 指数函数全纯性 *)
Lemma Cexp_holomorphic : forall w, Holomorphic Cexp w.
Proof.
  intros w.
  unfold Holomorphic.
  exists (Cexp w).
  intros eps Heps.
  set (M := Cnorm (Cexp w) + 1).
  assert (Hnorm_nonneg : 0 <= Cnorm (Cexp w)) by apply Cnorm_ge_0.
  assert (HM : 0 < M) by (unfold M; lra).
  set (eps1 := eps / M).
  assert (Heps1 : eps1 > 0) by (apply Rdiv_lt_0_compat; [exact Heps | exact HM]).
  destruct (limit_exp_minus_1_over_h eps1 Heps1) as [delta [Hdelta Hbound]].
  exists delta; split; [exact Hdelta |].
  intros h Hpos Hh.
  rewrite Cexp_add.
  set (dh := Cdiv (Csub (Cexp h) C1) h (nonzero_if_norm_positive h Hpos)).
  assert (Heq : Cdiv (Csub (Cexp (w +c h)) (Cexp w)) h (nonzero_if_norm_positive h Hpos) -c Cexp w =
                Cexp w *c (dh -c C1)).
  {
    unfold Cdiv.
    rewrite Cexp_add.
    assert (Cmul_comm : forall u v, u *c v = v *c u).
    { intros u v; destruct u, v; unfold Cmul; simpl; f_equal; ring. }
    assert (Cmul_assoc : forall x y z, (x *c y) *c z = x *c (y *c z)).
    { intros x y z; destruct x, y, z; unfold Cmul; simpl; f_equal; ring. }
    assert (Cmul_1_r : forall z, z *c C1 = z).
    { intros z; destruct z; unfold Cmul, C1; simpl; f_equal; ring. }
    assert (Cmul_1_l : forall z, C1 *c z = z).
    { intros z; destruct z; unfold Cmul, C1; simpl; f_equal; ring. }

    rewrite Cmul_comm with (u := Cexp w *c Cexp h -c Cexp w) (v := h⁻¹).
    rewrite Csub_mult_distr_r.
    rewrite Cmul_comm with (u := h⁻¹) (v := Cexp w *c Cexp h).
    rewrite Cmul_comm with (u := h⁻¹) (v := Cexp w).
    rewrite Cmul_assoc.

    unfold dh.
    unfold Cdiv.
    rewrite Csub_mult_distr_r.
    rewrite Cmul_1_r.
    rewrite Cmul_comm with (u := Cexp h -c C1) (v := h⁻¹).
    rewrite Csub_mult_distr_r.
    rewrite Cmul_comm with (u := h⁻¹) (v := Cexp h).
    rewrite Cmul_comm with (u := h⁻¹) (v := C1).
    rewrite Cmul_1_l.
    rewrite Csub_mult_distr_r.
    reflexivity.
  }
  rewrite <- Cexp_add.
  rewrite Heq.
  rewrite Cnorm_mult.
  apply Rle_lt_trans with (M * Cnorm (dh -c C1)).
  - apply Rmult_le_compat_r.
    + apply Cnorm_ge_0.
    + unfold M; lra.
  - pose proof (Hbound h Hpos Hh) as Hdh.
    assert (Heps_eq : eps = M * eps1) by (unfold eps1; field; lra).
    rewrite Heps_eq.
    apply Rmult_lt_compat_l; [exact HM | exact Hdh].
Qed.

(* 指数函数全纯性 *)
Lemma Cexp_derive : forall w, Holomorphic Cexp w.
Proof.
  exact Cexp_holomorphic.
Qed.

(* 复数自差为零 *)
Lemma Csub_self : forall z, z -c z = C0.
Proof.
  intros z; destruct z as [x y]; unfold Csub, C0; simpl.
  f_equal; ring.
Qed.

(* 模平方非负 *)
Lemma Cnorm_sq_ge_0 : forall z, 0 <= Cnorm_sq z.
Proof.
  intros z; unfold Cnorm_sq; apply Rplus_le_le_0_compat; apply Rle_0_sqr.
Qed.

(* 三角不等式特例 *)
Lemma Cnorm_add_1 : forall z, Cnorm (C1 +c z) <= 1 + Cnorm z.
Proof.
  intros z. destruct z as [x y].
  unfold Cnorm, Cnorm_sq, C1, Cadd; simpl.
  set (r2 := x² + y²).
  assert (Hr2_ge0 : 0 <= r2) by (apply Rplus_le_le_0_compat; apply Rle_0_sqr).

  assert (Hx_le_sqrt : x <= sqrt r2).
  {
    apply Rle_trans with (Rabs x).
    - apply Rle_abs.
    - rewrite <- (sqrt_Rsqr_abs x). apply sqrt_le_1_c.
      + apply Rle_0_sqr.
      + exact Hr2_ge0.
      + assert (H: 0 <= y²) by (apply Rle_0_sqr).
        replace (x²) with (x² + 0) by ring.
        apply Rplus_le_compat_l.
        exact H.
  }

  apply Rsqr_incr_0.
  - rewrite Rsqr_sqrt.
    2: apply Rplus_le_le_0_compat; apply Rle_0_sqr.
    simpl (0 + y); rewrite Rplus_0_l.
    replace ((1 + x)² + y²) with (1 + 2*x + (x² + y²)).
    2: { unfold Rsqr; simpl; ring. }
    replace ((1 + sqrt r2)²) with (1 + 2*sqrt r2 + (sqrt r2)²).
    2: { unfold Rsqr; simpl; ring. }
    replace ((sqrt r2)²) with r2 by (apply eq_sym, Rsqr_sqrt; assumption).
    replace (x² + y²) with r2 by reflexivity.
    replace (1 + 2*x + r2) with (1 + r2 + 2*x) by ring.
    replace (1 + 2*sqrt r2 + r2) with (1 + r2 + 2*sqrt r2) by ring.
    apply Rplus_le_compat_l.
    apply Rmult_le_compat_l; [lra | exact Hx_le_sqrt].

  - apply sqrt_pos.

  - apply Rplus_le_le_0_compat; [lra | apply sqrt_pos].
Qed.

(* 复数加减转换 *)
Lemma Csub_add : forall a b, a = b +c (a -c b).
Proof.
  intros a b; destruct a, b; unfold Cadd, Csub; simpl; f_equal; ring.
Qed.

Import FourierAnalysis.          (* 傅里叶分析模块：构造性傅里叶变换及相关工具 *)

(* 定理：复数指数函数的连续性 *)
Theorem Cexp_continuous : forall w,
  forall eps : R, eps > 0 -> exists delta : R, delta > 0 /\
    forall h : Complex, Cnorm h < delta -> Cnorm (Cexp (w +c h) -c Cexp w) < eps.
Proof.
  intros w eps Heps.
  assert (Hnorm_ge_0 : 0 <= Cnorm (Cexp w)) by apply Cnorm_ge_0.
  assert (Hpos_exp : 0 < Cnorm (Cexp w)).
  { apply Cnorm_pos, Cexp_neq_0. }
  set (N := Cnorm (Cexp w)).
  set (M := N + 1).
  assert (HM : 0 < M).
  { apply Rplus_lt_le_0_compat; [exact Hpos_exp | apply Rle_0_1]. }

  assert (Cmul_1_l : forall z, C1 *c z = z).
  { intros z; apply Complex_eq; destruct z; unfold C1, Cmul; simpl; ring. }
  assert (Cmul_1_r : forall z, z *c C1 = z).
  { intros z; apply Complex_eq; destruct z; unfold C1, Cmul; simpl; ring. }
  assert (Cmul_comm : forall a b, a *c b = b *c a).
  { intros a b; apply Complex_eq; destruct a, b; unfold Cmul; simpl; ring. }
  assert (Cmul_assoc : forall a b c, (a *c b) *c c = a *c (b *c c)).
  { intros a b c; apply Complex_eq; destruct a, b, c; unfold Cmul; simpl; ring. }

  assert (Cinv_r : forall z (Hz : Cnorm_sq z <> 0), z *c Cinv z Hz = C1).
  {
    intros z Hz.
    pose proof (Cdiv_mult_cancel_l C1 z Hz) as Htmp.
    unfold Cdiv in Htmp.
    rewrite Cmul_1_l in Htmp.
    exact Htmp.
  }

  destruct (limit_exp_minus_1_over_h 1 Rlt_0_1) as [delta1 [Hdelta1_pos Hdelta1]].
  set (eps2 := eps / M).
  assert (Heps2 : eps2 > 0) by (apply Rdiv_lt_0_compat; [exact Heps | exact HM]).
  set (delta2 := eps2 / 2).
  assert (Hdelta2_pos : delta2 > 0) by (apply Rdiv_lt_0_compat; [exact Heps2 | lra]).
  set (delta := Rmin delta1 delta2).
  assert (Hdelta_pos : delta > 0) by (apply Rmin_glb_lt; [exact Hdelta1_pos | exact Hdelta2_pos]).
  exists delta; split; [exact Hdelta_pos |].
  intros h Hh.
  destruct (Ceq_EM_T h C0) as [Heq | Hneq].
  - subst h.
    rewrite Cadd_0_r.
    rewrite Csub_self.
    assert (Cnorm_0 : Cnorm C0 = 0).
    { unfold Cnorm, Cnorm_sq, C0; simpl. rewrite Rsqr_0, Rplus_0_r. apply sqrt_0. }
    rewrite Cnorm_0; exact Heps.
  - assert (Hpos : 0 < Cnorm h) by (apply Cnorm_pos; exact Hneq).
    assert (Hh_lt_delta1 : Cnorm h < delta1).
    { apply Rlt_le_trans with delta; [exact Hh | apply Rmin_l]. }
    assert (Hh_lt_delta2 : Cnorm h < delta2).
    { apply Rlt_le_trans with delta; [exact Hh | apply Rmin_r]. }
    specialize (Hdelta1 h Hpos Hh_lt_delta1).
    set (X := Cdiv (Cexp h -c C1) h (nonzero_if_norm_positive h Hpos)).
    assert (HX_eq : X = C1 +c (X -c C1)) by apply Csub_add.
    assert (HnormX_lt_2 : Cnorm X < 2).
    {
      rewrite HX_eq.
      apply Rle_lt_trans with (1 + Cnorm (X -c C1)).
      - apply Cnorm_add_1.
      - apply Rplus_lt_compat_l; exact Hdelta1.
    }

    assert (Hexp_minus_1_eq : Cexp h -c C1 = h *c X).
    {
      unfold X, Cdiv.
      set (term := Cexp h -c C1).
      set (inv_h := Cinv h (nonzero_if_norm_positive h Hpos)).
      assert (Htmp: h *c (term *c inv_h) = term).
      {
        rewrite <- Cmul_assoc.
        rewrite (Cmul_comm h term).
        rewrite Cmul_assoc.
        unfold inv_h.
        rewrite (Cinv_r h (nonzero_if_norm_positive h Hpos)).
        rewrite Cmul_1_r.
        reflexivity.
      }
      rewrite Htmp.
      reflexivity.
    }

    assert (Hbound_exp_h : Cnorm (Cexp h -c C1) < eps2).
    {
      rewrite Hexp_minus_1_eq, Cnorm_mult.
      apply Rlt_trans with (Cnorm h * 2).
      - apply Rmult_lt_compat_l; [exact Hpos | exact HnormX_lt_2].
      - apply Rlt_le_trans with (delta2 * 2).
        + apply (Rmult_lt_compat_r 2 (Cnorm h) delta2); [apply Rlt_0_2 | exact Hh_lt_delta2].
        + assert (Heq : delta2 * 2 = eps2) by (unfold delta2, eps2; field; apply Rgt_not_eq; exact HM).
          rewrite Heq; apply Rle_refl.
    }

    rewrite Cexp_add.
    replace (Cexp w *c Cexp h -c Cexp w) with (Cexp w *c (Cexp h -c C1)).
    - rewrite Cnorm_mult.
      apply Rlt_trans with (N * eps2).
      + apply Rmult_lt_compat_l; [exact Hpos_exp | exact Hbound_exp_h].
      + assert (H_lt_eps : N * eps2 < eps).
        {
          unfold N, M, eps2.
          rewrite Rmult_comm.
          change (eps / M * ∥ Cexp w ∥) with (eps / M * N).
          assert (Heq : eps / M * N = eps * (N / M)).
          { field; apply Rgt_not_eq; exact HM. }
          rewrite Heq.
          rewrite <- Rmult_1_r.
          apply Rmult_lt_compat_l.
          - exact Heps.
          - replace (N / M) with (1 - /M).
            * assert (0 < /M) by (apply Rinv_0_lt_compat; exact HM). lra.
            * unfold M; field; apply Rgt_not_eq; exact HM.
        }
        exact H_lt_eps.
    - apply Complex_eq; destruct w, h; unfold Csub, Cmul, C1; simpl; ring.
Qed.

(* 复数指数函数的局部单射性 *)
Lemma Cexp_local_injective : forall w,
  exists r : R, r > 0 /\ forall u v : Complex,
    Cnorm u < r -> Cnorm v < r ->
    Cexp (w +c u) = Cexp (w +c v) -> u = v.
Proof.
  intros w.
  exists (PI/4). split.
  - apply Rmult_lt_0_compat; [apply PI_RGT_0 | apply Rinv_0_lt_compat; lra].
  - intros u v Hu Hv Heq.

    assert (Hexp_add : forall z1 z2, Cexp (z1 +c z2) = Cexp z1 *c Cexp z2) by apply Cexp_add.
    rewrite Hexp_add in Heq.
    rewrite (Hexp_add w v) in Heq.

    assert (Hw_neq0 : Cexp w <> C0) by apply Cexp_neq_0.
    pose proof (nonzero_norm_sq_nonzero (Cexp w) Hw_neq0) as Hnz.
    set (inv := Cinv (Cexp w) Hnz).

    assert (Hinv_left : inv *c Cexp w = C1).
    {
      destruct (Cexp w) as [a b] eqn:Heq_w.
      unfold inv, Cinv, Cmul, C1, Cnorm_sq; simpl.
      set (nsq := a² + b²).
      unfold Rdiv.
      apply Complex_eq; simpl.
      - replace (a * / nsq * a - (-b) * / nsq * b) with ((a*a + b*b) * / nsq).
        + rewrite Rinv_r; [reflexivity | exact Hnz].
        + field; exact Hnz.
      - replace (a * / nsq * b + (-b) * / nsq * a) with 0.
        + reflexivity.
        + field; exact Hnz.
    }

    apply (f_equal (fun z => inv *c z)) in Heq.
    assert (Cmul_assoc : forall a b c, (a *c b) *c c = a *c (b *c c)).
    { intros a b c; destruct a, b, c; unfold Cmul; simpl; f_equal; ring. }
    assert (Cmul_1_l : forall z, C1 *c z = z).
    { intros z; destruct z as [x y]; unfold Cmul, C1; simpl; f_equal; ring. }
    assert (Heq_right : inv *c (Cexp w *c Cexp v) = (inv *c Cexp w) *c Cexp v).
    { symmetry; apply Cmul_assoc. }
    rewrite Heq_right in Heq.
    rewrite <- Cmul_assoc in Heq.
    rewrite Hinv_left in Heq.
    rewrite Cmul_1_l in Heq.
    rewrite Cmul_1_l in Heq.

    assert (Hu_im_le: Rabs (im u) <= Cnorm u).
    {
      unfold Cnorm, Cnorm_sq; simpl.
      rewrite <- (sqrt_Rsqr_abs (im u)).
      apply sqrt_le_1_c; [apply Rle_0_sqr | apply Rplus_le_le_0_compat; apply Rle_0_sqr |].
      rewrite <- (Rplus_0_l (Rsqr (im u))) at 1.
      apply Rplus_le_compat_r; apply Rle_0_sqr.
    }
    assert (Hv_im_le: Rabs (im v) <= Cnorm v).
    {
      unfold Cnorm, Cnorm_sq; simpl.
      rewrite <- (sqrt_Rsqr_abs (im v)).
      apply sqrt_le_1_c; [apply Rle_0_sqr | apply Rplus_le_le_0_compat; apply Rle_0_sqr |].
      rewrite <- (Rplus_0_l (Rsqr (im v))) at 1.
      apply Rplus_le_compat_r; apply Rle_0_sqr.
    }
    assert (Hu_im_lt: Rabs (im u) < PI/4) by (apply Rle_lt_trans with (Cnorm u); [exact Hu_im_le | exact Hu]).
    assert (Hv_im_lt: Rabs (im v) < PI/4) by (apply Rle_lt_trans with (Cnorm v); [exact Hv_im_le | exact Hv]).

    pose proof PI_RGT_0.
    assert (Hquarter_lt_PI : PI/4 < PI) by lra.

    assert (Hu_im_bounds := Rabs_def2 (im u) (PI/4) Hu_im_lt).
    assert (Hv_im_bounds := Rabs_def2 (im v) (PI/4) Hv_im_lt).

    assert (Hu_im_range: -PI < im u <= PI).
    {
      split.
      - apply Rlt_trans with (- (PI/4)).
        + apply Ropp_lt_contravar; exact Hquarter_lt_PI.
        + destruct Hu_im_bounds as [_ Hlow_u]; exact Hlow_u.
      - apply Rlt_le.
        apply Rlt_trans with (PI/4).
        + destruct Hu_im_bounds as [Hhigh_u _]; exact Hhigh_u.
        + exact Hquarter_lt_PI.
    }
    assert (Hv_im_range: -PI < im v <= PI).
    {
      split.
      - apply Rlt_trans with (- (PI/4)).
        + apply Ropp_lt_contravar; exact Hquarter_lt_PI.
        + destruct Hv_im_bounds as [_ Hlow_v]; exact Hlow_v.
      - apply Rlt_le.
        apply Rlt_trans with (PI/4).
        + destruct Hv_im_bounds as [Hhigh_v _]; exact Hhigh_v.
        + exact Hquarter_lt_PI.
    }

    pose proof (Clog_exp u Hu_im_range) as Hlog_u.
    pose proof (Clog_exp v Hv_im_range) as Hlog_v.

    assert (Hind : forall z (p q : z <> C0), Clog_principal z p = Clog_principal z q).
    { intros z p q. unfold Clog_principal. apply Complex_eq; [simpl; reflexivity | simpl; reflexivity]. }

    assert (Hlog_v_gen : forall p : Cexp v <> C0, Clog_principal (Cexp v) p = v).
    {
      intros p.
      rewrite (Hind (Cexp v) p (Cexp_neq_0 v)).
      exact Hlog_v.
    }

    pose proof (eq_rect (Cexp v) (fun z => forall p : z <> C0, Clog_principal z p = v) Hlog_v_gen (Cexp u) (eq_sym Heq)) as Hlog_u_gen.

    specialize (Hlog_u_gen (Cexp_neq_0 u)).

    apply (eq_trans (eq_sym Hlog_u) Hlog_u_gen).
Qed.

End ComplexLogarithm.
