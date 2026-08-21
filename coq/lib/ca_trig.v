(* 拆分自 Riemann_Hypothesis_Proof_Framework.v（复分析证明库 v6.0）*)
(* 库: ca_trig  原文行区间: 2051-3231  机械拆分，未改动内容 *)

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

Require Import ca_base ca_algebra ca_primes ca_complex_analysis ca_fourier ca_zeta_scaffold.

Require Import Stdlib.Logic.IndefiniteDescription.

(* 三角恒等式 *)
Module TrigonometricLemmas.

Require Import Stdlib.Reals.Reals.
Require Import Stdlib.Reals.Rtrigo1.
Local Open Scope R_scope.

(* 正弦平方加余弦平方等于一 *)
Lemma sin2_cos2 : forall theta, (sin theta)² + (cos theta)² = 1.
Proof.
  intros theta.
  rewrite <- cos_0, <- (Rminus_diag theta), cos_minus.
  unfold Rsqr.
  rewrite Rplus_comm.
  reflexivity.
Qed.

(* 余弦平方加正弦平方等于一 *)
Lemma cos2_sin2 : forall theta : R, (cos theta)² + (sin theta)² = 1.
Proof.
  intros theta; rewrite Rplus_comm; apply sin2_cos2.
Qed.

(* 正弦二倍角公式 *)
Lemma sin_double : forall theta : R, sin (2 * theta) = 2 * sin theta * cos theta.
Proof.
  intros theta.
  rewrite sin_2a.
  reflexivity.
Qed.

(* 余弦二倍角公式 *)
Lemma cos_double : forall theta : R, cos (2 * theta) = (cos theta)² - (sin theta)².
Proof.
  intros theta.
  rewrite cos_2a.
  reflexivity.
Qed.

(* 正弦和角公式 *)
Lemma sin_plus : forall a b : R, sin (a + b) = sin a * cos b + cos a * sin b.
Proof.
  intros a b; apply sin_plus.
Qed.

(* 余弦和角公式 *)
Lemma cos_plus : forall a b : R, cos (a + b) = cos a * cos b - sin a * sin b.
Proof.
  intros a b; apply cos_plus.
Qed.

(* 正弦差角公式 *)
Lemma sin_minus : forall a b : R, sin (a - b) = sin a * cos b - cos a * sin b.
Proof.
  intros a b; apply sin_minus.
Qed.

(* 余弦差角公式 *)
Lemma cos_minus : forall a b : R, cos (a - b) = cos a * cos b + sin a * sin b.
Proof.
  intros a b; apply cos_minus.
Qed.

(* 正弦余角公式 *)
Lemma sin_pi2_minus : forall theta : R, sin (PI/2 - theta) = cos theta.
Proof.
  intros theta.
  rewrite sin_minus.
  rewrite sin_PI2, cos_PI2.
  simpl.
  ring.
Qed.

(* 余弦余角公式 *)
Lemma cos_pi2_minus : forall theta : R, cos (PI/2 - theta) = sin theta.
Proof.
  intros theta; rewrite cos_minus.
  rewrite cos_PI2, sin_PI2; simpl; ring.
Qed.

(* 正弦补角公式 *)
Lemma sin_pi_minus : forall theta : R, sin (PI - theta) = sin theta.
Proof.
  intros theta; rewrite sin_minus.
  rewrite sin_PI, cos_PI; simpl; ring.
Qed.

(* 余弦补角公式 *)
Lemma cos_pi_minus : forall theta : R, cos (PI - theta) = - cos theta.
Proof.
  intros theta; rewrite cos_minus.
  rewrite cos_PI, sin_PI; simpl; ring.
Qed.

(* 正弦加派公式 *)
Lemma sin_plus_pi : forall theta : R, sin (theta + PI) = - sin theta.
Proof.
  intros theta; rewrite sin_plus.
  rewrite sin_PI, cos_PI; simpl; ring.
Qed.

(* 余弦加派公式 *)
Lemma cos_plus_pi : forall theta : R, cos (theta + PI) = - cos theta.
Proof.
  intros theta; rewrite cos_plus.
  rewrite cos_PI, sin_PI; simpl; ring.
Qed.

(* 正弦加半派公式 *)
Lemma sin_plus_pi2 : forall theta : R, sin (theta + PI/2) = cos theta.
Proof.
  intros theta; rewrite sin_plus.
  rewrite sin_PI2, cos_PI2.
  ring.
Qed.

(* 余弦加半派公式 *)
Lemma cos_plus_pi2 : forall theta : R, cos (theta + PI/2) = - sin theta.
Proof.
  intros theta; rewrite cos_plus.
  rewrite cos_PI2, sin_PI2.
  ring.
Qed.

(* 正弦加两派公式 *)
Lemma sin_plus_2pi : forall theta : R, sin (theta + 2*PI) = sin theta.
Proof.
  intros theta; rewrite sin_plus.
  rewrite sin_2PI, cos_2PI.
  ring.
Qed.

(* 余弦加两派公式 *)
Lemma cos_plus_2pi : forall theta : R, cos (theta + 2*PI) = cos theta.
Proof.
  intros theta; rewrite cos_plus.
  rewrite cos_2PI, sin_2PI.
  ring.
Qed.

(* 正弦半角平方公式 *)
Lemma sin_half_sq' : forall theta,
  (sin (theta / 2))² = (1 - cos theta) / 2.
Proof.
  intros theta.
  assert (H2 : 2 * (theta / 2) = theta) by (field; lra).
  rewrite <- H2.
  rewrite cos_double.
  rewrite <- (cos2_sin2 (theta/2)).
  replace (2 * (theta / 2) / 2) with (theta / 2) by field.
  field.
Qed.

(* 余弦半角平方公式 *)
Lemma cos_half_sq : forall theta,
  (cos (theta / 2))² = (1 + cos theta) / 2.
Proof.
  intros theta.
  assert (H2 : 2 * (theta / 2) = theta) by (field; lra).
  rewrite <- H2.
  rewrite cos_double.
  rewrite <- (cos2_sin2 (theta/2)).
  replace (2 * (theta / 2) / 2) with (theta / 2) by field.
  field.
Qed.

(* 正弦余弦积化和差 *)
Lemma sin_cos_product : forall a b,
  sin a * cos b = (sin (a + b) + sin (a - b)) / 2.
Proof.
  intros a b.
  rewrite sin_plus, sin_minus.
  field.
Qed.

(* 余弦正弦积化和差 *)
Lemma cos_sin_product : forall a b,
  cos a * sin b = (sin (a + b) - sin (a - b)) / 2.
Proof.
  intros a b.
  rewrite sin_plus, sin_minus.
  field.
Qed.

(* 余弦余弦积化和差 *)
Lemma cos_cos_product : forall a b,
  cos a * cos b = (cos (a + b) + cos (a - b)) / 2.
Proof.
  intros a b.
  rewrite cos_plus, cos_minus.
  field.
Qed.

(* 正弦正弦积化和差 *)
Lemma sin_sin_product : forall a b,
  sin a * sin b = (cos (a - b) - cos (a + b)) / 2.
Proof.
  intros a b.
  rewrite cos_plus, cos_minus.
  field.
Qed.

(* 正弦和化积 *)
Lemma sin_plus_sin : forall a b,
  sin a + sin b = 2 * sin ((a + b) / 2) * cos ((a - b) / 2).
Proof.
  intros a b.
  set (p := (a + b) / 2).
  set (q := (a - b) / 2).
  assert (H : a = p + q) by (unfold p, q; field; lra).
  assert (H' : b = p - q) by (unfold p, q; field; lra).
  rewrite H, H'.
  rewrite sin_plus, sin_minus.
  ring.
Qed.

(* 正弦差化积 *)
Lemma sin_minus_sin : forall a b,
  sin a - sin b = 2 * cos ((a + b) / 2) * sin ((a - b) / 2).
Proof.
  intros a b.
  set (p := (a + b) / 2).
  set (q := (a - b) / 2).
  assert (H : a = p + q) by (unfold p, q; field; lra).
  assert (H' : b = p - q) by (unfold p, q; field; lra).
  rewrite H, H'.
  rewrite sin_plus, sin_minus.
  ring.
Qed.

(* 余弦和化积 *)
Lemma cos_plus_cos : forall a b,
  cos a + cos b = 2 * cos ((a + b) / 2) * cos ((a - b) / 2).
Proof.
  intros a b.
  set (p := (a + b) / 2).
  set (q := (a - b) / 2).
  assert (H : a = p + q) by (unfold p, q; field; lra).
  assert (H' : b = p - q) by (unfold p, q; field; lra).
  rewrite H, H'.
  rewrite cos_plus, cos_minus.
  ring.
Qed.

(* 余弦差化积 *)
Lemma cos_minus_cos : forall a b,
  cos a - cos b = -2 * sin ((a + b) / 2) * sin ((a - b) / 2).
Proof.
  intros a b.
  set (p := (a + b) / 2).
  set (q := (a - b) / 2).
  assert (H : a = p + q) by (unfold p, q; field; lra).
  assert (H' : b = p - q) by (unfold p, q; field; lra).
  rewrite H, H'.
  rewrite cos_plus, cos_minus.
  ring.
Qed.

(* 正切定义 *)
Lemma tan_def : forall theta,
  tan theta = sin theta / cos theta.
Proof.
  intros theta; reflexivity.
Qed.

(* 倍角正切 *)
Lemma tan_double : forall theta,
  cos theta <> 0 -> cos (2 * theta) <> 0 ->
  tan (2 * theta) = (2 * tan theta) / (1 - (tan theta)^2).
Proof.
  intros theta Hc Hc2.
  unfold tan.
  rewrite sin_2a, cos_2a.
  field.
  split.
  - exact Hc.
  - rewrite <- (Rsqr_pow2 (cos theta)), <- (Rsqr_pow2 (sin theta)).
    unfold Rsqr.
    rewrite <- cos_2a.
    exact Hc2.
Qed.

(* 和角正切 *)
Lemma tan_plus : forall a b,
  cos a <> 0 -> cos b <> 0 -> cos (a + b) <> 0 ->
  tan (a + b) = (tan a + tan b) / (1 - tan a * tan b).
Proof.
  intros a b Ha Hb Hab.
  unfold tan.
  rewrite sin_plus, cos_plus.
  field.
  split; [exact Hb | split; [exact Ha | rewrite <- cos_plus; exact Hab]].
Qed.

(* 平方根为零推出实部虚部为零 *)
Lemma r_zero_implies_a_b_zero : forall a b : R,
  sqrt (a² + b²) = 0 -> a = 0 /\ b = 0.
Proof.
  intros a b H.
  assert (Hsq_nonneg : 0 <= a² + b²) by (apply Rplus_le_le_0_compat; apply Rle_0_sqr).
  assert (H_sq_zero : a² + b² = 0).
  { apply sqrt_eq_0 in H; auto. }
  apply Rplus_eq_0 in H_sq_zero.
  - destruct H_sq_zero as [Ha2 Hb2].
    apply Rsqr_eq_0 in Ha2.
    apply Rsqr_eq_0 in Hb2.
    split; assumption.
  - apply Rle_0_sqr.
  - apply Rle_0_sqr.
Qed.

(* 正数时 atan2 化简 *)
Import ComplexNumbers.
Lemma atan2_gt0 : forall a b : R,
  0 < a -> atan2 b a = atan (b / a).
Proof.
  intros a b Ha.
  unfold atan2.
  destruct (Req_EM_T a 0) as [Ha_eq0 | Ha_neq0].
  - exfalso; lra.
  - destruct (Rlt_dec a 0) as [Ha_lt0 | Ha_ge0].
    + exfalso; lra.
    + reflexivity.
Qed.

(* 负数时 atan2 分段表达式 *)
Lemma atan2_lt0 : forall a b : R,
  a < 0 ->
  atan2 b a = if Rlt_dec b 0 then atan (b / a) - PI else atan (b / a) + PI.
Proof.
  intros a b Ha.
  unfold atan2.
  destruct (Req_EM_T a 0) as [H0 | Hn0].
  - rewrite H0 in Ha; lra.
  - destruct (Rlt_dec a 0) as [Ha_lt0 | Ha_ge0].
    + destruct (Rlt_dec b 0) as [Hb_lt0 | Hb_ge0]; reflexivity.
    + lra.
Qed.

(* 零时 atan2 表达式 *)
Lemma atan2_eq0 : forall b : R,
  atan2 b 0 = if Rlt_dec b 0 then - PI / 2 else PI / 2.
Proof.
  intros b.
  unfold atan2.
  destruct (Req_EM_T 0 0) as [H_eq | H_neq].
  - reflexivity.
  - exfalso; apply H_neq; reflexivity.
Qed.

(* 正系数正弦线性组合化简 *)
Lemma linear_combination_sin_a_gt0 : forall a b theta : R,
  0 < a ->
  a * sin theta + b * cos theta =
  sqrt (a² + b²) * sin (theta + atan2 b a).
Proof.
  intros a b theta Ha.
  rewrite atan2_gt0 by auto.
  set (r := sqrt (a² + b²)).
  set (t := b / a).
  assert (Hr_pos : 0 < r).
  { apply sqrt_lt_R0_c.
    apply Rplus_lt_le_0_compat.
    - apply Rlt_0_sqr; lra.
    - apply Rle_0_sqr. }
  assert (H1 : 1 + t² = (a² + b²) / a²).
  { unfold t; unfold Rsqr; field; lra. }
  assert (H2 : sqrt (1 + t²) = r / a).
  { rewrite H1.
    rewrite sqrt_div; [| apply Rplus_le_le_0_compat; apply Rle_0_sqr | apply Rlt_0_sqr; lra].
    rewrite sqrt_Rsqr_abs; rewrite Rabs_pos_eq; [| apply Rlt_le; auto].
    unfold r; field; lra. }
  assert (H3 : a = r * cos (atan t)).
  { rewrite (cos_atan t).
    rewrite H2; field; lra. }
  assert (H4 : b = r * sin (atan t)).
  { rewrite (sin_atan t).
    rewrite H2.
    unfold t; field; lra. }
  rewrite H3, H4.
  rewrite (Rmult_assoc r (cos (atan t)) (sin theta)).
  rewrite (Rmult_assoc r (sin (atan t)) (cos theta)).
  rewrite <- Rmult_plus_distr_l.
  rewrite (Rmult_comm (cos (atan t)) (sin theta)).
  rewrite (Rmult_comm (sin (atan t)) (cos theta)).
  rewrite sin_plus.
  reflexivity.
Qed.

(* 负a时余弦极坐标表示 *)
Lemma polar_coord_cos_when_a_lt0 : forall a b : R,
  a < 0 ->
  let r := sqrt (a² + b²) in
  a = r * cos (atan2 b a).
Proof.
  intros a b Ha.
  set (r := sqrt (a² + b²)).
  assert (Hr_pos : 0 < r).
  { apply sqrt_lt_R0_c.
    apply Rplus_lt_le_0_compat.
    - apply Rlt_0_sqr; lra.
    - apply Rle_0_sqr. }
  rewrite atan2_lt0 by auto.
  destruct (Rlt_dec b 0) as [Hb_neg | Hb_ge0].
  - (* b < 0 *)
    rewrite cos_minus.
    rewrite cos_PI, sin_PI.
    simpl.
    replace (cos (atan (b / a)) * (-1) + sin (atan (b / a)) * 0) with (- cos (atan (b / a))) by ring.
    rewrite cos_atan.
    set (t := b / a).
    assert (H1 : 1 + t² = (a² + b²) / a²).
    { unfold t; unfold Rsqr; field; lra. }
    assert (H2 : sqrt (1 + t²) = r / (-a)).
    { rewrite H1.
      rewrite sqrt_div; [| apply Rplus_le_le_0_compat; apply Rle_0_sqr | apply Rlt_0_sqr; lra].
      rewrite sqrt_Rsqr_abs; rewrite Rabs_left; [| lra].
      unfold r; field; lra. }
    rewrite H2.
    unfold t.
    field; lra.
  - (* b >= 0 *)
    rewrite cos_plus.
    rewrite cos_PI, sin_PI.
    simpl.
    replace (cos (atan (b / a)) * (-1) - sin (atan (b / a)) * 0) with (- cos (atan (b / a))) by ring.
    rewrite cos_atan.
    set (t := b / a).
    assert (H1 : 1 + t² = (a² + b²) / a²).
    { unfold t; unfold Rsqr; field; lra. }
    assert (H2 : sqrt (1 + t²) = r / (-a)).
    { rewrite H1.
      rewrite sqrt_div; [| apply Rplus_le_le_0_compat; apply Rle_0_sqr | apply Rlt_0_sqr; lra].
      rewrite sqrt_Rsqr_abs; rewrite Rabs_left; [| lra].
      unfold r; field; lra. }
    rewrite H2.
    unfold t.
    field; lra.
Qed.

(* 负a时正弦极坐标表示 *)
Lemma polar_coord_sin_when_a_lt0 : forall a b : R,
  a < 0 ->
  let r := sqrt (a² + b²) in
  b = r * sin (atan2 b a).
Proof.
  intros a b Ha.
  set (r := sqrt (a² + b²)).
  assert (Hr_pos : 0 < r).
  { apply sqrt_lt_R0_c.
    apply Rplus_lt_le_0_compat.
    - apply Rlt_0_sqr; lra.
    - apply Rle_0_sqr. }
  rewrite atan2_lt0 by auto.
  destruct (Rlt_dec b 0) as [Hb_neg | Hb_ge0].
  - (* b < 0 *)
    rewrite sin_minus.
    rewrite sin_PI, cos_PI.
    simpl.
    replace (sin (atan (b / a)) * (-1) + cos (atan (b / a)) * 0) with (- sin (atan (b / a))) by ring.
    rewrite sin_atan.
    set (t := b / a).
    assert (H1 : 1 + t² = (a² + b²) / a²).
    { unfold t; unfold Rsqr; field; lra. }
    assert (H2 : sqrt (1 + t²) = r / (-a)).
    { rewrite H1.
      rewrite sqrt_div; [| apply Rplus_le_le_0_compat; apply Rle_0_sqr | apply Rlt_0_sqr; lra].
      rewrite sqrt_Rsqr_abs; rewrite Rabs_left; [| lra].
      unfold r; field; lra. }
    rewrite H2.
    unfold t.
    field; lra.
  - (* b >= 0 *)
    rewrite sin_plus.
    rewrite sin_PI, cos_PI.
    simpl.
    replace (sin (atan (b / a)) * (-1) + cos (atan (b / a)) * 0) with (- sin (atan (b / a))) by ring.
    rewrite sin_atan.
    set (t := b / a).
    assert (H1 : 1 + t² = (a² + b²) / a²).
    { unfold t; unfold Rsqr; field; lra. }
    assert (H2 : sqrt (1 + t²) = r / (-a)).
    { rewrite H1.
      rewrite sqrt_div; [| apply Rplus_le_le_0_compat; apply Rle_0_sqr | apply Rlt_0_sqr; lra].
      rewrite sqrt_Rsqr_abs; rewrite Rabs_left; [| lra].
      unfold r; field; lra. }
    rewrite H2.
    unfold t.
    field; lra.
Qed.

(* 负系数正弦线性组合化简 *)
Lemma linear_combination_sin_a_lt0 : forall a b theta : R,
  a < 0 ->
  a * sin theta + b * cos theta =
  sqrt (a² + b²) * sin (theta + atan2 b a).
Proof.
  intros a b theta Ha.
  set (r := sqrt (a² + b²)).
  set (φ := atan2 b a).
  assert (Hr_pos : 0 < r).
  { apply sqrt_lt_R0_c.
    apply Rplus_lt_le_0_compat.
    - apply Rlt_0_sqr; lra.
    - apply Rle_0_sqr. }
  assert (Ha_eq : a = r * cos φ).
  { unfold r, φ; apply polar_coord_cos_when_a_lt0; assumption. }
  assert (Hb_eq : b = r * sin φ).
  { unfold r, φ; apply polar_coord_sin_when_a_lt0; assumption. }
  rewrite Ha_eq, Hb_eq.
  rewrite Rmult_assoc.
  rewrite Rmult_assoc.
  rewrite <- Rmult_plus_distr_l.
  apply f_equal.
  rewrite sin_plus.
  ring.
Qed.

(* 零系数正弦线性组合化简 *)
Lemma linear_combination_sin_a_eq0 : forall b theta : R,
  0 * sin theta + b * cos theta = sqrt (0² + b²) * sin (theta + atan2 b 0).
Proof.
  intros b theta.
  simpl.
  rewrite Rsqr_0, Rplus_0_l.
  destruct (Rlt_dec b 0) as [Hb_neg | Hb_ge0].
  - (* b < 0 *)
    assert (H_atan2 : atan2 b 0 = - PI / 2).
    { rewrite atan2_eq0. destruct (Rlt_dec b 0) as [H|H]; [reflexivity | lra]. }
    rewrite H_atan2.
    rewrite sin_plus.
    replace (- PI / 2) with (- (PI / 2)) by field.
    rewrite sin_neg, cos_neg.
    rewrite sin_PI2, cos_PI2.
    simpl.
    rewrite sqrt_Rsqr_abs.
    rewrite Rabs_left1; [| lra].
    ring.
  - (* b ≥ 0 *)
    assert (H_atan2 : atan2 b 0 = PI / 2).
    { rewrite atan2_eq0. destruct (Rlt_dec b 0) as [H|H]; [lra | reflexivity]. }
    rewrite H_atan2.
    rewrite sin_plus.
    rewrite sin_PI2, cos_PI2.
    simpl.
    rewrite sqrt_Rsqr_abs.
    rewrite Rabs_pos_eq; [| lra].
    ring.
Qed.

(* 正弦线性组合化为正弦形式 *)
Lemma linear_combination_sin : forall a b theta : R,
  a * sin theta + b * cos theta =
  sqrt (a² + b²) * sin (theta + atan2 b a).
Proof.
  intros a b theta.
  destruct (Req_dec (sqrt (a² + b²)) 0) as [Hr0 | Hr_neq].
  - apply r_zero_implies_a_b_zero in Hr0.
    destruct Hr0 as [Ha0 Hb0].
    rewrite Ha0, Hb0.
    rewrite !Rsqr_0.
    rewrite Rplus_0_l.
    rewrite sqrt_0.
    ring.
  - destruct (Rgt_dec a 0) as [Ha_gt0 | Ha_not_gt0].
    + apply linear_combination_sin_a_gt0; auto.
    + destruct (Req_dec a 0) as [Ha_eq0 | Ha_lt0].
      * rewrite Ha_eq0.
        apply linear_combination_sin_a_eq0.
      * assert (Ha_le_0 : a <= 0) by (apply Rnot_gt_le; exact Ha_not_gt0).
        destruct (Rle_lt_or_eq_dec a 0 Ha_le_0) as [Ha_lt_0 | Ha_eq_0].
        - apply linear_combination_sin_a_lt0; auto.
        - contradiction.
Qed.

(* 平方和为零等价于各项为零 *)
Lemma sum_sq_zero : forall a b : R, a² + b² = 0 <-> a = 0 /\ b = 0.
Proof.
  split.
  - intros H.
    assert (Ha_ge0 : 0 <= a²) by apply Rle_0_sqr.
    assert (Hb_ge0 : 0 <= b²) by apply Rle_0_sqr.
    assert (Ha_le0 : a² <= a² + b²).
    { rewrite <- Rplus_0_r at 1. apply Rplus_le_compat_l. exact Hb_ge0. }
    rewrite H in Ha_le0.
    assert (Ha_eq0 : a² = 0) by (apply Rle_antisym; [exact Ha_le0 | exact Ha_ge0]).
    assert (Hb_le0 : b² <= a² + b²).
    { rewrite <- Rplus_0_l at 1. apply Rplus_le_compat_r. exact Ha_ge0. }
    rewrite H in Hb_le0.
    assert (Hb_eq0 : b² = 0) by (apply Rle_antisym; [exact Hb_le0 | exact Hb_ge0]).
    apply Rsqr_eq_0 in Ha_eq0.
    apply Rsqr_eq_0 in Hb_eq0.
    auto.
  - intros [Ha Hb]; rewrite Ha, Hb; unfold Rsqr; ring.
Qed.

(* 平方和的平方根为零等价于平方和为零 *)
Lemma sqrt_sum_sq_zero : forall a b : R, sqrt (a² + b²) = 0 <-> a² + b² = 0.
Proof.
  intros a b.
  split.
  - intros H.
    assert (H_nonneg : 0 <= a² + b²) by (apply Rplus_le_le_0_compat; apply Rle_0_sqr).
    apply sqrt_eq_0 in H; auto.
  - intros H; rewrite H; apply sqrt_0.
Qed.

(* 余弦的atan2恒等式 *)
Lemma cos_atan2 : forall y x,
      let r := sqrt (x^2 + y^2) in
      r <> 0 -> cos (atan2 y x) = x / r.
Proof.
  intros y x r Hr.
  Local Open Scope R_scope.
  unfold atan2.
  destruct (Req_EM_T x 0) as [Hx_zero | Hx_nonzero].
  - (* x = 0 *)
    rewrite Hx_zero.
    destruct (Rlt_dec y 0) as [Hy_neg | Hy_not_neg].
    + (* y < 0 *)
      assert (H: - PI / 2 = - (PI / 2)).
      { field; lra. }
      rewrite H, cos_neg, cos_PI2.
      unfold Rdiv; rewrite Rmult_0_l.
      reflexivity.
    + (* y >= 0 *)
      rewrite cos_PI2.
      unfold Rdiv; rewrite Rmult_0_l.
      reflexivity.
  - (* x ≠ 0 *)
    assert (cos_atan_eq : forall a, cos (atan a) = 1 / sqrt (1 + Rsqr a)).
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
      replace (a * cos (atan a) * (a * cos (atan a))) with ((a ^ 2) * (cos (atan a)) ^ 2) in Htrig
        by (simpl; ring).
      replace (a ^ 2) with (Rsqr a) in Htrig by (rewrite Rsqr_pow2; reflexivity).
      replace ((cos (atan a)) ^ 2) with (Rsqr (cos (atan a))) in Htrig by (rewrite Rsqr_pow2; reflexivity).
      assert (Hprod : (1 + Rsqr a) * Rsqr (cos (atan a)) = 1).
      { replace ((1 + Rsqr a) * Rsqr (cos (atan a))) with (Rsqr a * Rsqr (cos (atan a)) + Rsqr (cos (atan a))) by ring.
        exact Htrig. }
      assert (Hpos_den : 0 < 1 + Rsqr a).
      { assert (0 <= Rsqr a) by apply Rle_0_sqr; lra. }
      assert (Hnz : 1 + Rsqr a <> 0) by (apply Rgt_not_eq; exact Hpos_den).
      assert (Hcos2_eq : Rsqr (cos (atan a)) = 1 / (1 + Rsqr a)).
      { apply Rmult_eq_reg_l with (1 + Rsqr a); [| exact Hnz].
        rewrite Hprod; field; exact Hnz. }
      assert (Hcos_eq : cos (atan a) = sqrt (1 / (1 + Rsqr a))).
      { apply Rsqr_inj.
        - apply Rlt_le, Hcos_pos.
        - apply sqrt_pos.
        - rewrite Rsqr_sqrt.
          + exact Hcos2_eq.
          + apply Rlt_le; apply Rdiv_lt_0_compat; lra. }
      rewrite sqrt_div in Hcos_eq; [| lra | exact Hpos_den ].
      rewrite sqrt_1 in Hcos_eq.
      exact Hcos_eq.
    }
    destruct (Rlt_dec x 0) as [Hx_neg | Hx_pos].
    + (* x < 0 *)
      destruct (Rlt_dec y 0) as [Hy_neg | Hy_pos].
      * (* y < 0 *)
        rewrite cos_minus.
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
          unfold Rdiv.
          assert (Hr_neq : r <> 0) by exact Hr.
          assert (Hnx_neq : -x <> 0) by (apply Ropp_neq_0_compat; lra).
          rewrite (Rinv_mult r (/ - x)).
          rewrite Rinv_inv.
          rewrite Rmult_comm.
          rewrite <- Ropp_mult_distr_l.
          rewrite Ropp_involutive.
          reflexivity.
        - apply Rplus_le_le_0_compat; [apply pow2_ge_0 | apply pow2_ge_0].
        - unfold pow; simpl; replace (x * (x * 1)) with (x * x) by ring; apply Rlt_0_sqr; lra.
      * (* y >= 0 *)
        rewrite cos_plus.
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
          unfold Rdiv.
          assert (Hr_neq : r <> 0) by exact Hr.
          assert (Hnx_neq : -x <> 0) by (apply Ropp_neq_0_compat; lra).
          rewrite (Rinv_mult r (/ - x)).
          rewrite Rinv_inv.
          rewrite Rmult_comm.
          rewrite Rmult_0_r.
          replace (-1 * (/ r * - x)) with (x * / r) by (field; lra).
          rewrite Rminus_0_r.
          reflexivity.
        - apply Rplus_le_le_0_compat; [apply pow2_ge_0 | apply pow2_ge_0].
        - unfold pow; simpl; replace (x * (x * 1)) with (x * x) by ring; apply Rlt_0_sqr; lra.
    + (* x > 0 *)
      rewrite cos_atan_eq with (a := y/x).
      unfold Rdiv; rewrite Rmult_1_l.
      unfold Rsqr at 1.
      replace (1 + (y * / x) * (y * / x)) with ((x^2 + y^2) / x^2) by (field; lra).
      assert (Hr_over_x : sqrt ((x^2 + y^2) / x^2) = r / x).
      {
        rewrite sqrt_div.
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

(* 反正切的正弦公式 *)
Lemma sin_atan_eq : forall a : R, sin (atan a) = a / sqrt (1 + a^2).
Proof.
  intros a.
  destruct (Req_EM_T a 0) as [Ha0 | Ha_nonzero].
  - (* a = 0 *)
    rewrite Ha0, atan_0, sin_0.
    unfold Rdiv; rewrite Rmult_0_l; reflexivity.
  - (* a ≠ 0 *)
    pose proof (tan_atan a) as Htan.
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
    unfold Rdiv.
    exact Htan.
Qed.

(* 二参数反正切的正弦公式 *)
Lemma sin_atan2 : forall y x : R,
      let r := sqrt (x^2 + y^2) in
      r <> 0 -> sin (atan2 y x) = y / r.
Proof.
  intros y x r Hr.
  unfold atan2.
  destruct (Req_EM_T x 0) as [Hx_zero | Hx_nonzero].
  - (* x = 0 *)
    simpl.
    destruct (Rlt_dec y 0) as [Hy_neg | Hy_nonneg].
    + (* y < 0 *)
      replace ( - PI / 2 ) with ( - (PI/2) ) by (field; lra).
      rewrite sin_neg, sin_PI2.
      assert (r = - y).
      {
        unfold r.
        rewrite Hx_zero.
        simpl.
        replace (0 * (0 * 1)) with 0 by ring.
        rewrite Rplus_0_l.
        replace (y * (y * 1)) with (y * y) by ring.
        replace (y * y) with (Rsqr y) by (unfold Rsqr; reflexivity).
        rewrite sqrt_Rsqr_abs.
        - rewrite Rabs_left; [| lra]. reflexivity.
      }
      rewrite H.
      replace (y / (- y)) with (-1).
      * reflexivity.
      * field; lra.
    + (* y >= 0 *)
      rewrite sin_PI2.
      destruct (Req_EM_T y 0) as [Hy_zero | Hy_pos].
      * (* y = 0 *)
        unfold r in Hr.
        rewrite Hx_zero, Hy_zero in Hr.
        simpl in Hr.
        assert (Htmp : sqrt (0 * (0 * 1) + 0 * (0 * 1)) = 0).
        { replace (0 * (0 * 1) + 0 * (0 * 1)) with 0 by ring.
          apply sqrt_0. }
        rewrite Htmp in Hr.
        contradiction Hr; reflexivity.
      * (* y > 0 *)
        assert (Hr_eq : r = y).
        {
          unfold r; rewrite Hx_zero; simpl.
          replace (0 * (0 * 1) + y * (y * 1)) with (y * y) by (rewrite Rmult_0_l; ring).
          apply Rnot_lt_le in Hy_nonneg.
          rewrite sqrt_square; auto.
        }
        rewrite Hr_eq. field; lra.

  - (* x ≠ 0 *)
    destruct (Rlt_dec x 0) as [Hx_neg | Hx_pos].
    + (* x < 0 *)
      destruct (Rlt_dec y 0) as [Hy_neg | Hy_nonneg].
      * (* y < 0 *)
        replace (atan (y / x) - PI) with ( - (PI - atan (y / x)) ) by ring.
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
        {
          replace ((- x) ^ 2) with (x ^ 2) by ring.
          rewrite Rmult_plus_distr_l.
          rewrite Rmult_1_r.
          assert (Htmp : y ^ 2 = x ^ 2 * (y / x) ^ 2).
          {
            unfold pow; simpl.
            field; exact Hx_nonzero'.
          }
          rewrite <- Htmp.
          ring.
        }
        rewrite Heq.
        rewrite sqrt_mult; [ | exact Hx2_nonneg | exact Hterm_nonneg ].
        rewrite sqrt_pow2.
        2: exact Hx_neg_nonneg.
        simpl.
        field.
        split.
        - exact Hsqrt_nonzero.
        - exact Hx_nonzero'.

      * (* y >= 0 *)
        replace (atan (y / x) + PI) with (PI + atan (y / x)) by ring.
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
        {
          replace ((- x) ^ 2) with (x ^ 2) by ring.
          rewrite Rmult_plus_distr_l.
          rewrite Rmult_1_r.
          assert (Htmp : y ^ 2 = x ^ 2 * (y / x) ^ 2).
          {
            unfold pow; simpl.
            field; exact Hx_nonzero'.
          }
          rewrite <- Htmp.
          ring.
        }
        rewrite Heq.
        rewrite sqrt_mult; [ | exact Hx2_nonneg | exact Hterm_nonneg ].
        rewrite sqrt_pow2.
        2: exact Hx_neg_nonneg.
        simpl.
        field.
        split.
        - exact Hsqrt_nonzero.
        - exact Hx_nonzero'.

    + (* x > 0 *)
      rewrite sin_atan_eq.
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
      {
        rewrite Rmult_plus_distr_l.
        rewrite Rmult_1_r.
        assert (Htmp : y ^ 2 = x ^ 2 * (y / x) ^ 2).
        {
          unfold pow; simpl.
          field; exact Hx_nonzero'.
        }
        rewrite <- Htmp.
        ring.
      }
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

(* 实部虚部为零推出等于零 *)
Lemma C0_eq : forall z, re z = 0 /\ im z = 0 -> z = C0.
Proof.
  intros z [Hre Him]; destruct z; simpl in *; subst; reflexivity.
Qed.

(* 非零复数的模平方严格为正 *)
Lemma Cnorm_sq_pos : forall z, z <> C0 -> 0 < Cnorm_sq z.
Proof.
  intros z Hz.
  unfold Cnorm_sq.
  destruct z as [a b]; simpl.
  destruct (Req_EM_T a 0) as [Ha|Ha]; destruct (Req_EM_T b 0) as [Hb|Hb].
  - (* a = 0, b = 0 *)
    exfalso; apply Hz; apply C0_eq; split; assumption.
  - (* a = 0, b <> 0 *)
    apply Rplus_le_lt_0_compat.
    + apply Rle_0_sqr.
    + apply Rlt_0_sqr; exact Hb.
  - (* a <> 0, b = 0 *)
    apply Rplus_lt_le_0_compat.
    + apply Rlt_0_sqr; exact Ha.
    + apply Rle_0_sqr.
  - (* a <> 0, b <> 0 *)
    apply Rplus_lt_0_compat.
    + apply Rlt_0_sqr; exact Ha.
    + apply Rlt_0_sqr; exact Hb.
Qed.

(* 非零复数的模为正 *)
Lemma Cnorm_pos : forall z, z <> C0 -> 0 < Cnorm z.
Proof.
  intros z Hz.
  unfold Cnorm.
  apply sqrt_lt_R0_c.
  apply Cnorm_sq_pos; auto.
Qed.

(* 将 Rsqr 转换为 pow 形式 *)
Lemma pow2_sqr : forall x, x^2 = Rsqr x.
Proof. intros x; unfold Rsqr, pow; simpl; ring. Qed.

(* 余弦线性组合的振幅相位形式 *)
Lemma linear_combination_cos : forall a b theta : R,
  a * sin theta + b * cos theta =
  sqrt (a² + b²) * cos (theta - atan2 a b).
Proof.
  intros a b theta.
  set (r := sqrt (a² + b²)).
  assert (Hr_nonneg : 0 <= r) by (unfold r; apply sqrt_pos).
  destruct (Req_dec r 0) as [Hz | Hnz].
  - assert (Hsq_zero : a² + b² = 0) by (apply sqrt_sum_sq_zero; exact Hz).
    assert (Hab_zero : a = 0 /\ b = 0) by (apply sum_sq_zero; exact Hsq_zero).
    destruct Hab_zero as [Ha Hb].
    rewrite Ha, Hb.
    rewrite Rmult_0_l, Rmult_0_l, Rplus_0_l.
    rewrite Hz, Rmult_0_l.
    reflexivity.
  - set (r' := sqrt (a^2 + b^2)).
    assert (H_eq_r : r' = r).
    { unfold r, r'.
      rewrite (pow2_sqr a), (pow2_sqr b).
      reflexivity. }
    assert (Hr'_neq : r' <> 0) by (rewrite H_eq_r; assumption).
    assert (Hsqrt_comm : sqrt (b^2 + a^2) = r').
    { rewrite Rplus_comm; reflexivity. }
    assert (Hcos : cos (atan2 a b) = b / sqrt (b^2 + a^2)).
    { apply cos_atan2 with (y := a) (x := b).
      rewrite Hsqrt_comm; assumption. }
    assert (Hsin : sin (atan2 a b) = a / sqrt (b^2 + a^2)).
    { apply sin_atan2 with (y := a) (x := b).
      rewrite Hsqrt_comm; assumption. }
    rewrite Hsqrt_comm in Hcos, Hsin.
    rewrite H_eq_r in Hcos, Hsin.
    rewrite cos_minus.
    rewrite Hcos, Hsin.
    field; exact Hnz.
Qed.

(* 三倍角正弦公式 *)
Lemma sin_triple : forall theta,
  sin (3 * theta) = 3 * sin theta - 4 * (sin theta) ^ 3.
Proof.
  intros theta.
  replace (3 * theta) with (2 * theta + theta) by ring.
  rewrite sin_plus.
  rewrite sin_2a, cos_2a.
  simpl.
  assert (Hcos2 : cos theta * cos theta = 1 - sin theta * sin theta).
  { rewrite <- (sin2_cos2 theta). unfold Rsqr. ring. }
  ring [Hcos2].
Qed.

(* 三倍角余弦公式 *)
Lemma cos_triple : forall theta,
  cos (3 * theta) = 4 * (cos theta) ^ 3 - 3 * cos theta.
Proof.
  intros theta.
  replace (3 * theta) with (2 * theta + theta) by ring.
  rewrite cos_plus.
  rewrite sin_2a, cos_2a.
  simpl.
  assert (Hsin2 : sin theta * sin theta = 1 - cos theta * cos theta).
  { rewrite <- (sin2_cos2 theta). unfold Rsqr. ring. }
  assert (Heq : 2 * sin theta * cos theta * sin theta = 2 * cos theta * (sin theta * sin theta)).
  { ring. }
  rewrite Heq.
  rewrite Hsin2.
  ring.
Qed.

(* 正切平方加一等于正割平方 *)
Lemma one_plus_tan_sq : forall theta,
  cos theta <> 0 -> 1 + (tan theta)² = 1 / (cos theta)².
Proof.
  intros theta Hc.
  unfold tan.
  rewrite Rsqr_div'.
  assert (Hc2 : (cos theta)² <> 0) by (apply Rgt_not_eq, Rsqr_pos_lt, Hc).
  rewrite <- (Rmult_1_l (1 / (cos theta)²)).
  apply Rmult_eq_reg_l with (r := (cos theta)²); [| assumption].
  rewrite Rmult_plus_distr_l.
  rewrite Rmult_1_r.
  rewrite (Rmult_comm (cos theta)² ((sin theta)² / (cos theta)²)).
  rewrite (Rdiv_def (sin theta)² (cos theta)²).
  rewrite Rmult_assoc.
  rewrite (Rmult_comm (/ (cos theta)²) (cos theta)²).
  rewrite Rinv_r; [| assumption].
  rewrite Rmult_1_r.
  rewrite Rmult_1_l.
  replace (1 / (cos theta)²) with (1 * / (cos theta)²) by (unfold Rdiv; reflexivity).
  rewrite Rmult_1_l.
  rewrite Rinv_r; [| assumption].
  rewrite Rplus_comm.
  rewrite sin2_cos2.
  reflexivity.
Qed.

(* 余切、正割、余割定义 *)
Definition cot (θ : R) : R := cos θ / sin θ.
Definition sec (θ : R) : R := 1 / cos θ.
Definition csc (θ : R) : R := 1 / sin θ.

(* 余切平方加一等于余割平方 *)
Lemma one_plus_cot_sq : forall θ,
  sin θ <> 0 -> 1 + (cot θ)² = 1 / (sin θ)².
Proof.
  intros θ Hs.
  unfold cot.
  rewrite Rsqr_div'.
  assert (Hs2 : (sin θ)² <> 0) by (apply Rgt_not_eq, Rsqr_pos_lt, Hs).
  rewrite <- (Rmult_1_l (1 / (sin θ)²)).
  apply Rmult_eq_reg_l with (r := (sin θ)²); [| assumption].
  rewrite Rmult_plus_distr_l.
  rewrite Rmult_1_r.
  rewrite (Rmult_comm (sin θ)² ((cos θ)² / (sin θ)²)).
  rewrite (Rdiv_def (cos θ)² (sin θ)²).
  rewrite Rmult_assoc.
  rewrite (Rmult_comm (/ (sin θ)²) (sin θ)²).
  rewrite Rinv_r; [| assumption].
  rewrite Rmult_1_r.
  rewrite Rmult_1_l.
  replace (1 / (sin θ)²) with (1 * / (sin θ)²) by (unfold Rdiv; reflexivity).
  rewrite Rmult_1_l.
  rewrite Rinv_r; [| assumption].
  rewrite sin2_cos2.
  reflexivity.
Qed.

(* 正割平方等于正切平方加一 *)
Lemma sec_sq_eq_one_plus_tan_sq : forall θ,
  cos θ <> 0 -> (sec θ)² = 1 + (tan θ)².
Proof.
  intros θ Hc.
  unfold sec.
  rewrite Rsqr_div'.
  rewrite one_plus_tan_sq; auto.
  rewrite Rsqr_1.
  reflexivity.
Qed.

(* 余割平方等于余切平方加一 *)
Lemma csc_sq_eq_one_plus_cot_sq : forall θ,
  sin θ <> 0 -> (csc θ)² = 1 + (cot θ)².
Proof.
  intros θ Hs.
  unfold csc, cot.
  rewrite Rsqr_div'.
  rewrite Rsqr_1.
  rewrite <- one_plus_cot_sq; auto.
Qed.

(* 余切定义展开 *)
Lemma cot_eq : forall θ, sin θ <> 0 -> cot θ = cos θ / sin θ.
Proof. intros; unfold cot; reflexivity. Qed.

(* 正割定义展开 *)
Lemma sec_eq : forall θ, cos θ <> 0 -> sec θ = 1 / cos θ.
Proof. intros; unfold sec; reflexivity. Qed.

(* 余割定义展开 *)
Lemma csc_eq : forall θ, sin θ <> 0 -> csc θ = 1 / sin θ.
Proof. intros; unfold csc; reflexivity. Qed.

End TrigonometricLemmas.

Export TrigonometricLemmas.
