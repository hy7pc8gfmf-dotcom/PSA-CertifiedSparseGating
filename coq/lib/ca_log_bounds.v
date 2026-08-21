(* 拆分自 Riemann_Hypothesis_Proof_Framework.v（复分析证明库 v6.0）*)
(* 库: ca_log_bounds  原文行区间: 21086-23433  机械拆分，未改动内容 *)

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

Require Import ca_base ca_algebra ca_primes ca_complex_analysis ca_fourier ca_zeta_scaffold ca_trig ca_gamma ca_taylor ca_zeta_axioms ca_complex_log ca_complex_foundation.

Require Import Stdlib.Logic.IndefiniteDescription.
Require Import Stdlib.Reals.Reals.
Require Import Stdlib.Reals.Rtrigo1.
Require Import Stdlib.Reals.Rpower.
Require Import Stdlib.Reals.Rseries.
Require Import Stdlib.Logic.ProofIrrelevance.
Require Import Stdlib.micromega.Lra.
Local Open Scope R_scope.


Module ClogBoundModule.

Require Import Stdlib.Reals.Reals.
Require Import Stdlib.micromega.Lra.

Require Import Stdlib.Reals.Ranalysis1.  (* 提供 continuity_pt, derivable_pt 等 *)
Require Import Stdlib.Reals.Rtrigo1.     (* 提供 atan *)
Require Import Stdlib.Reals.Rpower.      (* 提供 ln *)

Import ComplexNumbers.
Import ComplexLogarithm.
Import HolomorphicFunctions.
Import ComplexLogarithm.
Open Scope complex_scope.

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

(* [构造性轨道 S1] Cinv 与证明参数无关（定义体不使用 H） *)
Lemma Cinv_irrel : forall (z : Complex) (H1 H2 : Cnorm_sq z <> 0),
  Cinv z H1 = Cinv z H2.
Proof. intros z H1 H2; unfold Cinv; reflexivity. Qed.



Definition Clog_total (z : Complex) : Complex :=
  match Rlt_dec 0 (Cnorm_sq z) with
  | left Hpos   => Clog_principal z (Cnorm_sq_pos_nonzero z Hpos)
  | right Hnpos => C0
  end.


(* 实部大于0的复数非零 *)
Lemma re_pos_implies_neq0 : forall z, re z > 0 -> z <> C0.
Proof.
  intros z H H0; rewrite H0 in H; simpl in H; lra.
Qed.

(* re 函数的 Lipschitz 性质 *)
Lemma re_le_Cnorm : forall z, Rabs (re z) <= Cnorm z.
Proof.
  intros z; unfold Cnorm, Cnorm_sq; rewrite <- (sqrt_Rsqr_abs (re z)).
  apply sqrt_le_1_c; [apply Rle_0_sqr | apply Rplus_le_le_0_compat; apply Rle_0_sqr |].
  rewrite <- Rplus_0_r at 1; apply Rplus_le_compat_l; apply Rle_0_sqr.
Qed.

(* re 函数的连续性（复数意义下）*)
Lemma re_continuous : forall w,
  forall eps : R, eps > 0 ->
  exists delta : R, delta > 0 /\
  forall z, Cnorm (z -c w) < delta -> Rabs (re z - re w) < eps.
Proof.
  intros w eps Heps.
  exists eps; split; [exact Heps |].
  intros z H.
  assert (Hsub : re (z -c w) = re z - re w).
  { destruct z, w; unfold Csub; simpl; ring. }
  rewrite <- Hsub.
  apply Rle_lt_trans with (Cnorm (z -c w)).
  - apply re_le_Cnorm.
  - exact H.
Qed.

(* im 函数的 Lipschitz 性质 *)
Lemma im_le_Cnorm : forall z, Rabs (im z) <= Cnorm z.
Proof.
  intros z; unfold Cnorm, Cnorm_sq; rewrite <- (sqrt_Rsqr_abs (im z)).
  apply sqrt_le_1_c; [apply Rle_0_sqr | apply Rplus_le_le_0_compat; apply Rle_0_sqr |].
  rewrite <- Rplus_0_l at 1; apply Rplus_le_compat_r; apply Rle_0_sqr.
Qed.

(* im 函数的连续性（复数意义下）*)
Lemma im_continuous : forall w,
  forall eps : R, eps > 0 ->
  exists delta : R, delta > 0 /\
  forall z, Cnorm (z -c w) < delta -> Rabs (im z - im w) < eps.
Proof.
  intros w eps Heps.
  exists eps; split; [exact Heps |].
  intros z H.
  assert (Hsub : im (z -c w) = im z - im w).
  { destruct z, w; unfold Csub; simpl; ring. }
  rewrite <- Hsub.
  apply Rle_lt_trans with (Cnorm (z -c w)).
  - apply im_le_Cnorm.
  - exact H.
Qed.

(* 绝对值幂等性 *)
Lemma Rabs_idem : forall x : R, Rabs (Rabs x) = Rabs x.
Proof.
  intros x; apply Rabs_pos_eq; apply Rabs_pos.
Qed.

(* 柯西施瓦茨不等式绝对值形式 *)
Lemma CauchySchwarz_abs : forall z w,
  Rabs (re z * re w + im z * im w) <= Cnorm z * Cnorm w.
Proof.
  intros z w.
  apply Rsqr_incr_0.
  - rewrite Rsqr_abs.
    unfold Cnorm.
    rewrite !Rsqr_mult.
    rewrite (Rsqr_sqrt (Cnorm_sq z)) by apply Cnorm_sq_ge_0.
    rewrite (Rsqr_sqrt (Cnorm_sq w)) by apply Cnorm_sq_ge_0.
    destruct z as [z1 z2]; destruct w as [w1 w2]; simpl.
    unfold Cnorm_sq; simpl.
    set (A := z1 * w1 + z2 * w2).
    set (B := z1 * w2 - z2 * w1).
    assert (H: (Rsqr z1 + Rsqr z2)*(Rsqr w1 + Rsqr w2) = Rsqr A + Rsqr B).
    { unfold Rsqr, A, B; ring. }
    rewrite H.
    rewrite Rabs_idem.
    replace (Rabs A)² with (A²) by (rewrite Rsqr_abs; reflexivity).
    rewrite <- (Rplus_0_r A²) at 1.
    apply Rplus_le_compat_l.
    apply Rle_0_sqr.
  - apply Rabs_pos.
  - apply Rmult_le_pos; apply Cnorm_ge_0.
Qed.

(* 柯西施瓦茨不等式平方形式 *)
Lemma CauchySchwarz_sq : forall z w,
  Rsqr (re z * re w + im z * im w) <= Cnorm_sq z * Cnorm_sq w.
Proof.
  intros [z1 z2] [w1 w2].
  unfold Cnorm_sq; simpl.
  apply Rminus_le.
  replace ((z1 * w1 + z2 * w2)² - (z1² + z2²) * (w1² + w2²))
    with (- (z1 * w2 - z2 * w1)²) by (unfold Rsqr; ring).
  assert (H : 0 <= (z1 * w2 - z2 * w1)²) by apply Rle_0_sqr.
  apply Ropp_le_contravar in H.
  rewrite Ropp_0 in H.
  exact H.
Qed.

(* 范数连续性 *)
Lemma Cnorm_continuous : forall w,
  forall eps : R, eps > 0 ->
  exists delta : R, delta > 0 /\
  forall z, Cnorm (z -c w) < delta -> Rabs (Cnorm z - Cnorm w) < eps.
Proof.
  intros w eps Heps.
  exists eps; split; [exact Heps |].
  intros z H.
  assert (Hrev : Rabs (Cnorm z - Cnorm w) <= Cnorm (z -c w)).
  {
    unfold Cnorm.
    destruct z as [x1 y1]; destruct w as [x2 y2]; simpl.
    set (a := Rsqr x1 + Rsqr y1).
    set (b := Rsqr x2 + Rsqr y2).
    set (c := Rsqr (x1 - x2) + Rsqr (y1 - y2)).
    assert (Ha : 0 <= a) by (apply Rplus_le_le_0_compat; apply Rle_0_sqr).
    assert (Hb : 0 <= b) by (apply Rplus_le_le_0_compat; apply Rle_0_sqr).
    assert (Hc : 0 <= c) by (apply Rplus_le_le_0_compat; apply Rle_0_sqr).

    assert (Ha' : Cnorm_sq (x1 +i y1) = a) by (unfold Cnorm_sq; simpl; auto).
    assert (Hb' : Cnorm_sq (x2 +i y2) = b) by (unfold Cnorm_sq; simpl; auto).
    assert (Hc' : Cnorm_sq (x1 +i y1 -c x2 +i y2) = c).
    {
      unfold Cnorm_sq, Csub; simpl.
      unfold c; rewrite Rsqr_minus, Rsqr_minus; ring.
    }

    rewrite Ha', Hb', Hc'.

    assert (Hcs : (x1 * x2 + y1 * y2)² <= a * b).
    {
      apply CauchySchwarz_sq with (z := (x1 +i y1)) (w := (x2 +i y2)).
    }

    assert (Hle : x1 * x2 + y1 * y2 <= sqrt (a * b)).
    {
      apply Rle_trans with (Rabs (x1 * x2 + y1 * y2)).
      - apply Rle_abs.
      - apply Rsqr_incr_0.
        + rewrite (Rsqr_sqrt (a * b)); [| apply Rmult_le_pos; assumption].
          replace (Rsqr (Rabs (x1 * x2 + y1 * y2))) with ((x1 * x2 + y1 * y2)²)
            by (rewrite Rsqr_abs; reflexivity).
          exact Hcs.
        + apply Rabs_pos.
        + apply sqrt_pos.
    }

    assert (Hsqdiff : (sqrt a - sqrt b)² = a + b - 2 * sqrt (a * b)).
    {
      unfold Rsqr.
      replace ((sqrt a - sqrt b) * (sqrt a - sqrt b))
        with (sqrt a * sqrt a - 2 * sqrt a * sqrt b + sqrt b * sqrt b) by ring.
      assert (Haa : sqrt a * sqrt a = a) by (apply Rsqr_sqrt; assumption).
      assert (Hbb : sqrt b * sqrt b = b) by (apply Rsqr_sqrt; assumption).
      assert (Hab : sqrt a * sqrt b = sqrt (a * b)) by (symmetry; apply sqrt_mult; assumption).
      rewrite Haa, Hbb.
      replace (2 * sqrt a * sqrt b) with (2 * (sqrt a * sqrt b))
        by (rewrite Rmult_assoc; ring).
      rewrite Hab.
      ring.
    }

    assert (Hc_eq : c = a + b - 2 * (x1 * x2 + y1 * y2)).
    {
      unfold c, a, b; rewrite Rsqr_minus, Rsqr_minus; ring.
    }

    apply Rsqr_incr_0.
    - rewrite (Rsqr_sqrt c Hc).
      rewrite <- Rsqr_abs.
      rewrite Hsqdiff, Hc_eq.
      apply Rplus_le_compat_l.
      apply Ropp_le_contravar.
      apply Rmult_le_compat_l; [lra | exact Hle].
    - apply Rabs_pos.
    - apply sqrt_pos.
  }
  apply Rle_lt_trans with (Cnorm (z -c w)); [exact Hrev | exact H].
Qed.

(* 范数不大于绝对值之和 *)
Lemma Cnorm_le_sum_abs : forall z, Cnorm z <= Rabs (re z) + Rabs (im z).
Proof.
  intros [x y]; unfold Cnorm, Cnorm_sq; simpl.
  apply Rsqr_incr_0.
  - rewrite Rsqr_plus.
    replace ((Rabs x)²) with (x²) by apply Rsqr_abs.
    replace ((Rabs y)²) with (y²) by apply Rsqr_abs.
    rewrite Rsqr_sqrt.
    2: apply Rplus_le_le_0_compat; apply Rle_0_sqr.
    assert (H : 0 <= 2 * Rabs x * Rabs y).
    {
      apply Rmult_le_pos.
      - apply Rmult_le_pos.
        + lra.
        + apply Rabs_pos.
      - apply Rabs_pos.
    }
    replace (x² + y² + 2 * Rabs x * Rabs y) with ((x² + y²) + (2 * Rabs x * Rabs y)) by ring.
    lra.
  - apply sqrt_pos.
  - apply Rplus_le_le_0_compat; apply Rabs_pos.
Qed.

(* 正数一半为正 *)
Lemma Rlt_0_eps_div2 : forall eps, eps > 0 -> eps/2 > 0.
Proof. intros; lra. Qed.

(* 反向三角不等式 *)
Lemma Cnorm_triangle_rev : forall u v,
  Rabs (Cnorm u - Cnorm v) <= Cnorm (u -c v).
Proof.
  intros u v.
  destruct u as [x1 y1]; destruct v as [x2 y2].
  unfold Cnorm; simpl.
  set (a := Rsqr x1 + Rsqr y1).
  set (b := Rsqr x2 + Rsqr y2).
  set (c := Rsqr (x1 - x2) + Rsqr (y1 - y2)).
  assert (Ha : 0 <= a) by (apply Rplus_le_le_0_compat; apply Rle_0_sqr).
  assert (Hb : 0 <= b) by (apply Rplus_le_le_0_compat; apply Rle_0_sqr).
  assert (Hc : 0 <= c) by (apply Rplus_le_le_0_compat; apply Rle_0_sqr).

  assert (Ha' : Cnorm_sq (x1 +i y1) = a) by (unfold Cnorm_sq; simpl; auto).
  assert (Hb' : Cnorm_sq (x2 +i y2) = b) by (unfold Cnorm_sq; simpl; auto).
  assert (Hc' : Cnorm_sq (x1 +i y1 -c x2 +i y2) = c).
  {
    unfold Cnorm_sq, Csub; simpl.
    unfold c; rewrite Rsqr_minus, Rsqr_minus; ring.
  }

  rewrite Ha', Hb', Hc' in *; clear Ha' Hb' Hc'.

  assert (Hcs : (x1 * x2 + y1 * y2)² <= a * b).
  { apply CauchySchwarz_sq with (z := (x1 +i y1)) (w := (x2 +i y2)). }

  assert (Hle : x1 * x2 + y1 * y2 <= sqrt (a * b)).
  {
    apply Rle_trans with (Rabs (x1 * x2 + y1 * y2)).
    - apply Rle_abs.
    - apply Rsqr_incr_0.
      + rewrite (Rsqr_sqrt (a * b)); [| apply Rmult_le_pos; assumption].
        replace (Rsqr (Rabs (x1 * x2 + y1 * y2))) with ((x1 * x2 + y1 * y2)²)
          by (rewrite Rsqr_abs; reflexivity).
        exact Hcs.
      + apply Rabs_pos.
      + apply sqrt_pos.
  }

  assert (Hsqdiff : (sqrt a - sqrt b)² = a + b - 2 * sqrt (a * b)).
  {
    unfold Rsqr.
    replace ((sqrt a - sqrt b) * (sqrt a - sqrt b))
      with (sqrt a * sqrt a - 2 * sqrt a * sqrt b + sqrt b * sqrt b) by ring.
    assert (Haa : sqrt a * sqrt a = a) by (apply Rsqr_sqrt; assumption).
    assert (Hbb : sqrt b * sqrt b = b) by (apply Rsqr_sqrt; assumption).
    assert (Hab : sqrt a * sqrt b = sqrt (a * b)) by (symmetry; apply sqrt_mult; assumption).
    rewrite Haa, Hbb.
    replace (2 * sqrt a * sqrt b) with (2 * (sqrt a * sqrt b)) by (rewrite Rmult_assoc; ring).
    rewrite Hab.
    ring.
  }

  assert (Hc_eq : c = a + b - 2 * (x1 * x2 + y1 * y2)).
  {
    unfold c, a, b; rewrite Rsqr_minus, Rsqr_minus; ring.
  }

  apply Rsqr_incr_0.
  - rewrite (Rsqr_sqrt c Hc).
    rewrite <- Rsqr_abs.
    rewrite Hsqdiff, Hc_eq.
    apply Rplus_le_compat_l.
    apply Ropp_le_contravar.
    apply Rmult_le_compat_l; [lra | exact Hle].
  - apply Rabs_pos.
  - apply sqrt_pos.
Qed.

(* 自然对数可导 *)
Lemma derivable_pt_ln : forall x, 0 < x -> derivable_pt ln x.
Proof.
  intros x H.
  exists (/ x).
  apply derivable_pt_lim_ln; assumption.
Qed.

(* 自然对数连续 *)
Lemma ln_continuous : forall x, 0 < x -> continuity_pt ln x.
Proof.
  intros x H.
  apply derivable_continuous_pt.
  apply derivable_pt_ln; assumption.
Qed.

(* 定理：主支复对数的连续性 *)
Theorem Clog_principal_continuous : forall w (Hw : w <> C0) (Hre : re w > 0),
  forall eps : R, eps > 0 ->
  exists delta : R, delta > 0 /\
  forall h : Complex, Cnorm h < delta -> forall (Hpos : re (w +c h) > 0),
    Cnorm (Clog_principal (w +c h) (re_pos_implies_neq0 (w +c h) Hpos) -c Clog_principal w Hw) < eps.
Proof.
  intros w Hw Hre eps Heps.
  destruct w as [xw yw]; simpl in *.
  set (rw := Cnorm (xw +i yw)).
  assert (rw_pos : (rw > 0)%R) by (apply Cnorm_pos; exact Hw).
  set (eps1 := (eps / 2)%R).
  assert (eps1_pos : (eps1 > 0)%R) by (unfold eps1; lra).

  pose proof (ln_continuous rw rw_pos) as Hcont_ln.
  destruct (Hcont_ln eps1 eps1_pos) as [delta_ln [Hdelta_ln_pos Hdelta_ln]].

  assert (xw_neq0 : xw <> 0%R) by lra.
  set (z0 := (yw / xw)%R).
  assert (cont_atan : continuity_pt atan z0).
  {
    apply derivable_continuous_pt.
    apply derivable_pt_atan.
  }
  destruct (cont_atan eps1 eps1_pos) as [eta [Heta_pos Heta]].

  set (M := (Rabs xw + Rabs yw)%R).
  assert (xw_pos : (0 < xw)%R) by exact Hre.
  set (delta2 := Rmin ((xw / 2)%R) ((eta * Rsqr xw / (2 * M))%R)).
  assert (delta2_pos : (delta2 > 0)%R).
  {
    apply Rmin_glb_lt.
    - apply Rdiv_lt_0_compat; [exact xw_pos | lra].
    - apply Rdiv_lt_0_compat.
      + apply Rmult_lt_0_compat.
        * exact Heta_pos.
        * apply Rlt_0_sqr; exact xw_neq0.
      + assert (M_pos : (0 < M)%R).
        { unfold M.
          assert (Hxw_ge0 : (0 <= xw)%R) by (left; exact xw_pos).
          rewrite (Rabs_pos_eq xw Hxw_ge0).
          apply Rplus_lt_le_0_compat; [exact xw_pos | apply Rabs_pos]. }
        apply Rmult_lt_0_compat; [lra | exact M_pos].
  }
  set (delta := Rmin delta_ln delta2).
  assert (delta_pos : (delta > 0)%R) by (apply Rmin_glb_lt; [exact Hdelta_ln_pos | exact delta2_pos]).
  exists delta; split; [exact delta_pos |].
  intros h Hh Hpos'.
  destruct h as [dx dy]; simpl in *.
  set (x := (xw + dx)%R); set (y := (yw + dy)%R).
  assert (Hx_pos : (x > 0)%R) by exact Hpos'.
  assert (Hx_neq0 : x <> 0%R) by lra.

  assert (Hrw_le : Rabs ((Cnorm (x +i y) - rw)%R) <= Cnorm (dx +i dy)).
  {
    unfold rw.
    assert (Heq : Cnorm (dx +i dy) = Cnorm ((x +i y) -c (xw +i yw))).
    {
      unfold Csub; simpl.
      replace (x - xw)%R with dx by (unfold x; ring).
      replace (y - yw)%R with dy by (unfold y; ring).
      reflexivity.
    }
    rewrite Heq.
    apply Cnorm_triangle_rev.
  }
  assert (Hrw_diff : (Rabs ((Cnorm (x +i y) - rw)%R) < delta_ln)%R).
  {
    apply Rle_lt_trans with (Cnorm (dx +i dy)).
    - exact Hrw_le.
    - apply Rlt_le_trans with delta; [exact Hh | apply Rmin_l].
  }

  assert (atan2_eq : atan2 y x = atan (y / x)%R).
  {
    unfold atan2.
    destruct (Req_EM_T x 0%R) as [Hx0 | Hx_neq0'].
    - exfalso; apply Hx_neq0; exact Hx0.
    - destruct (Rlt_dec x 0%R) as [Hx_lt0 | Hx_ge0].
      + exfalso; lra.
      + reflexivity.
  }
  assert (atan2_eq0 : atan2 yw xw = atan (yw / xw)%R).
  {
    unfold atan2.
    destruct (Req_EM_T xw 0%R) as [Hxw0 | _]; [contradiction |].
    destruct (Rlt_dec xw 0%R) as [Hxw_lt0 | Hxw_ge0]; [lra | reflexivity].
  }

  assert (Hdx_bound : (Rabs dx < delta2)%R).
  {
    apply Rle_lt_trans with (Cnorm (dx +i dy)).
    - apply (re_le_Cnorm (dx +i dy)).
    - apply Rlt_le_trans with delta.
      + exact Hh.
      + apply Rmin_r.
  }
  assert (Hdy_bound : (Rabs dy < delta2)%R).
  {
    apply Rle_lt_trans with (Cnorm (dx +i dy)).
    - apply (im_le_Cnorm (dx +i dy)).
    - apply Rlt_le_trans with delta.
      + exact Hh.
      + apply Rmin_r.
  }
  assert (Hdx_lt_xw_half : (Rabs dx < xw / 2)%R).
  {
    apply Rlt_le_trans with delta2.
    - exact Hdx_bound.
    - apply Rmin_l.
  }

  assert (Hx_lower : (x > xw / 2)%R).
  {
    assert (Hx_ge : (x >= xw - Rabs dx)%R).
    {
      unfold x.
      apply Rle_ge.
      apply Rplus_le_compat_l.
      apply Ropp_le_cancel.
      rewrite Ropp_involutive.
      rewrite <- (Rabs_Ropp dx).
      apply Rle_abs.
    }
    assert (Htmp : (xw - Rabs dx > xw / 2)%R).
    {
      lra.
    }
    apply Rlt_le_trans with (xw - Rabs dx)%R.
    - exact Htmp.
    - apply Rge_le; exact Hx_ge.
  }

  assert (Hratio_bound : Rabs ((y / x - yw / xw)%R) <= ((Cnorm (dx +i dy) * M) / ((xw ^ 2)%R / 2)%R)%R).
  {
    set (d := Cnorm (dx +i dy)).
    assert (Hdx_le : (Rabs dx <= d)%R) by apply (re_le_Cnorm (dx +i dy)).
    assert (Hdy_le : (Rabs dy <= d)%R) by apply (im_le_Cnorm (dx +i dy)).
    assert (Hxw_pos : (0 < xw)%R) by exact Hre.
    assert (Hxw_neq0 : xw <> 0%R) by lra.

    set (num := Rabs ((dy * xw - yw * dx)%R)).
    assert (Hnum_le : (num <= d * M)%R).
    {
      unfold num.
      rewrite Rabs_minus_sym.
      replace ((yw * dx - dy * xw)%R) with ((yw * dx + - (dy * xw))%R) by ring.
      apply Rle_trans with (Rabs (yw * dx)%R + Rabs (- (dy * xw))%R)%R.
      - apply Rabs_triang.
      - rewrite Rabs_Ropp, !Rabs_mult.
        apply Rle_trans with ((d * Rabs yw + d * Rabs xw)%R).
        + apply Rplus_le_compat.
          * rewrite Rmult_comm.
            apply (Rmult_le_compat_r (Rabs yw)).
            -- apply Rabs_pos.
            -- exact Hdx_le.
          * replace (Rabs xw * Rabs dy)%R with (Rabs dy * Rabs xw)%R by (rewrite Rmult_comm; reflexivity).
            apply (Rmult_le_compat_r (Rabs xw)).
            -- apply Rabs_pos.
            -- exact Hdy_le.
        + rewrite <- Rmult_plus_distr_l.
          replace (Rabs yw + Rabs xw)%R with M by (unfold M; ring).
          apply Rle_refl.
    }

    assert (Hdenom_pos : ((x * xw)%R > 0)%R) by (apply Rmult_lt_0_compat; lra).
    assert (Hdenom_abs : Rabs (x * xw)%R = (x * xw)%R) by (apply Rabs_pos_eq; left; exact Hdenom_pos).
    assert (Hdenom_lower : ((x * xw)%R >= (xw / 2)%R * xw)%R).
    {
      apply Rle_ge.
      apply Rmult_le_compat_r.
      - apply Rlt_le; exact Hxw_pos.
      - apply Rlt_le; exact Hx_lower.
    }

    apply Rle_trans with (num / ((xw/2)%R * xw)%R)%R.
    - replace ((y / x - yw / xw)%R) with (((y * xw - yw * x) / (x * xw))%R).
      2: {
        field; split; lra.
      }
      assert (Hd_pos : ((x * xw)%R > 0)%R) by lra.
      assert (Habs_div : Rabs ((y * xw - yw * x) / (x * xw))%R = (Rabs (y * xw - yw * x)%R * / (x * xw)%R)%R).
      {
        unfold Rdiv.
        rewrite Rabs_mult.
        rewrite (Rabs_pos_eq (/ (x * xw)%R)).
        - reflexivity.
        - apply Rlt_le, Rinv_0_lt_compat; lra.
      }
      rewrite Habs_div.
      replace (Rabs (y * xw - yw * x)%R) with num.
      2: {
        unfold num.
        replace ((y * xw - yw * x)%R) with ((dy * xw - yw * dx)%R) by (unfold x, y; ring).
        reflexivity.
      }
      assert (Hdenom2_pos : (((xw/2)%R * xw)%R > 0)%R).
      {
        apply Rmult_lt_0_compat.
        - apply Rdiv_lt_0_compat; lra.
        - exact xw_pos.
      }
      unfold Rdiv at 2.
      apply Rmult_le_compat_l.
      + apply Rabs_pos.
      + apply Rinv_le_contravar.
        * exact Hdenom2_pos.
        * apply Rge_le; exact Hdenom_lower.

    - replace (((xw/2)%R * xw)%R) with (((xw ^ 2)%R / 2)%R) by (field; lra).
      unfold Rdiv.
      apply Rmult_le_compat_r.
      + apply Rlt_le, Rinv_0_lt_compat.
        apply Rmult_lt_0_compat.
        * assert (Hpow_eq : (xw ^ 2)%R = (xw * xw)%R).
          { unfold pow; simpl; ring. }
          rewrite Hpow_eq.
          apply Rmult_lt_0_compat; [exact xw_pos | exact xw_pos].
        * lra.
      + exact Hnum_le.
  }

  assert (Hd_lt_delta2 : (Cnorm (dx +i dy) < delta2)%R).
  {
    apply Rlt_le_trans with delta; [exact Hh | apply Rmin_r].
  }

  assert (Hdiff_lt_eta : (Rabs ((y / x - yw / xw)%R) < eta)%R).
  {
    apply Rle_lt_trans with ((Cnorm (dx +i dy) * M / ((xw ^ 2)%R / 2)%R)%R).
    - exact Hratio_bound.
    - assert (Hpos_den : (0 < (xw ^ 2)%R / 2)%R).
      {
        unfold Rdiv.
        apply Rmult_lt_0_compat.
        + replace ((xw ^ 2)%R) with (xw * xw)%R by (simpl; ring).
          apply Rmult_lt_0_compat; exact xw_pos.
        + lra.
      }
      assert (Hinv_pos : (0 < / ((xw ^ 2)%R / 2)%R)%R) by (apply Rinv_0_lt_compat; exact Hpos_den).
      assert (M_pos : (0 < M)%R).
      {
        unfold M.
        apply Rplus_lt_le_0_compat.
        - apply Rabs_pos_lt; lra.
        - apply Rabs_pos.
      }
      assert (Hprod_lt : (Cnorm (dx +i dy) * M < delta2 * M)%R).
      { apply Rmult_lt_compat_r; [exact M_pos | exact Hd_lt_delta2]. }
      apply Rlt_le_trans with ((delta2 * M / ((xw ^ 2)%R / 2)%R)%R).
      + unfold Rdiv. apply Rmult_lt_compat_r; [exact Hinv_pos | exact Hprod_lt].
      + assert (Hdelta2_le : (delta2 <= (eta * (xw ^ 2)%R / (2 * M))%R)%R).
        { unfold delta2; rewrite Rsqr_pow2; apply Rmin_r. }
        assert (Hc_pos : (0 < M * / ((xw ^ 2)%R / 2)%R)%R).
        { apply Rmult_lt_0_compat; [exact M_pos | exact Hinv_pos]. }
        apply Rle_trans with (((eta * (xw ^ 2)%R / (2 * M))%R * (M * / ((xw ^ 2)%R / 2)%R)%R)%R).
        * unfold Rdiv at 1.
          rewrite Rmult_assoc.
          apply Rmult_le_compat_r.
          + apply Rlt_le; exact Hc_pos.
          + exact Hdelta2_le.
        * replace (((eta * (xw ^ 2)%R / (2 * M))%R * (M * / ((xw ^ 2)%R / 2)%R)%R)%R) with eta.
          -- apply Rle_refl.
          -- field.
             split; [apply Rgt_not_eq; exact xw_pos | apply Rgt_not_eq; lra].
  }

  assert (Hnorm_log_diff : Cnorm (Clog_principal (x +i y) (re_pos_implies_neq0 (x +i y) Hx_pos)
                                      -c Clog_principal (xw +i yw) Hw) <=
            (Rabs ((ln (Cnorm (x +i y)) - ln (Cnorm (xw +i yw)))%R) + Rabs (atan2 y x - atan2 yw xw)%R)%R).
  {
    unfold Clog_principal; simpl.
    apply Cnorm_le_sum_abs.
  }

  assert (Hln_diff_lt_eps1 : (Rabs ((ln (Cnorm (x +i y)) - ln rw)%R) < eps1)%R).
  {
    destruct (Req_EM_T (Cnorm (x +i y)) rw) as [Heq | Hneq].
    - rewrite Heq, Rminus_diag, Rabs_R0; exact eps1_pos.
    - apply Hdelta_ln.
      split.
      + unfold D_x, no_cond; split; [trivial | exact (not_eq_sym Hneq)].
      + unfold Rdist; exact Hrw_diff.
  }

  assert (Hatan_diff_lt_eps1 : (Rabs ((atan (y / x)%R - atan (yw / xw)%R)%R) < eps1)%R).
  {
    destruct (Req_EM_T (y / x)%R (yw / xw)%R) as [Heq | Hneq].
    - rewrite Heq, Rminus_diag, Rabs_R0; exact eps1_pos.
    - apply Heta.
      split.
      + unfold D_x, no_cond; split.
        * exact I.
        * unfold z0; apply not_eq_sym; exact Hneq.
      + unfold Rdist; exact Hdiff_lt_eta.
  }

  assert (Hatan2_diff_lt_eps1 : (Rabs (atan2 y x - atan2 yw xw) < eps1)%R).
  {
    rewrite atan2_eq, atan2_eq0; exact Hatan_diff_lt_eps1.
  }

  assert (Hsum_lt : ((Rabs ((ln (Cnorm (x +i y)) - ln rw)%R) + Rabs (atan2 y x - atan2 yw xw)%R) < eps)%R).
  {
    replace eps with (eps1 + eps1)%R by (unfold eps1; field).
    apply Rplus_lt_compat; [exact Hln_diff_lt_eps1 | exact Hatan2_diff_lt_eps1].
  }
  apply Rle_lt_trans with ((Rabs ((ln (Cnorm (x +i y)) - ln rw)%R) + Rabs (atan2 y x - atan2 yw xw)%R)%R);
    [exact Hnorm_log_diff | exact Hsum_lt].
Qed.

(* 主支复对数在右半平面的局部单射性 *)
Lemma Clog_principal_local_injective : forall w (Hw : w <> C0) (Hre : re w > 0),
  exists r : R, r > 0 /\
  forall (u v : Complex) (Hru : re u > 0) (Hrv : re v > 0),
    Cnorm (u -c w) < r -> Cnorm (v -c w) < r ->
    Clog_principal u (re_pos_implies_neq0 u Hru) = Clog_principal v (re_pos_implies_neq0 v Hrv) -> u = v.
Proof.
  intros w Hw Hre.
  exists 1. split; [lra |].
  intros u v Hru Hrv Hu Hv Heq.
  rewrite <- (ComplexLogarithm.exp_Clog u (re_pos_implies_neq0 u Hru)).
  rewrite <- (ComplexLogarithm.exp_Clog v (re_pos_implies_neq0 v Hrv)).
  rewrite Heq.
  reflexivity.
Qed.

(* 主支对数范数上界 *)
Lemma Clog_norm_bound : forall u (Hu : u <> C0),
  Cnorm (Clog_principal u Hu) <= Rabs (ln (Cnorm u)) + PI.
Proof.
  intros u Hu.
  unfold Clog_principal.
  set (r := Cnorm u).
  set (θ := atan2 (im u) (re u)).
  assert (Hθ : Rabs θ <= PI).
  {
    assert (Hpi : 0 < PI) by apply PI_RGT_0.
    unfold θ, atan2.
    destruct (Req_EM_T (re u) 0) as [Hx0 | Hxneq0].
    - destruct (Rlt_dec (im u) 0) as [Hy | Hy].
      + simpl. rewrite Rabs_left; [lra | lra].
      + simpl. rewrite Rabs_pos_eq; [lra | lra].
    - destruct (Rlt_dec (re u) 0) as [Hrneg | Hrpos].
      + destruct (Rlt_dec (im u) 0) as [Himgneg | Himgpos].
        * simpl.
          assert (Hdiv_pos : 0 < im u / re u).
          {
            replace (im u / re u) with ((- im u) / (- re u)).
            - apply Rdiv_lt_0_compat; lra.
            - field; lra.
          }
          pose proof (atan_bound (im u / re u)) as Hbound.
          destruct Hbound as [Hlow Hhigh].
          assert (Hatan_pos : 0 < atan (im u / re u)).
          { rewrite <- atan_0; apply atan_increasing; lra. }
          assert (Hθ_neg : atan (im u / re u) - PI < 0) by (apply Rlt_minus; lra).
          rewrite Rabs_left1; [| left; exact Hθ_neg].
          replace (- (atan (im u / re u) - PI)) with (PI - atan (im u / re u)) by ring.
          apply Rle_trans with (PI - 0); [apply Rplus_le_compat_l; apply Ropp_le_contravar; apply Rlt_le; exact Hatan_pos | lra].
        * simpl.
          destruct (Req_EM_T (im u / re u) 0) as [Ht0 | Ht0'].
          -- rewrite Ht0, atan_0.
             rewrite Rabs_pos_eq; [lra | lra].
          -- assert (Him_neq0 : im u <> 0).
             {
               intro H.
               rewrite H in Ht0'.
               rewrite Rdiv_0_l in Ht0' by exact Hxneq0.
               exfalso; apply Ht0'; reflexivity.
             }
             assert (Him_ge0 : 0 <= im u) by (apply Rnot_lt_le; exact Himgpos).
             assert (Him_gt0 : im u > 0) by lra.
             assert (Hinv_neg : / re u < 0) by (apply Rinv_neg; exact Hrneg).
             assert (Ht_lt0 : im u / re u < 0).
             {
               unfold Rdiv.
               apply Ropp_lt_cancel.
               rewrite Ropp_0.
               rewrite Ropp_mult_distr_r.
               apply Rmult_lt_0_compat; [exact Him_gt0 | lra].
             }
             pose proof (atan_bound (im u / re u)) as [Hlow Hhigh].
             assert (Hatan_lt_0 : atan (im u / re u) < 0).
             { rewrite <- atan_0; apply atan_increasing; exact Ht_lt0. }
             assert (Hpos_sum : 0 < atan (im u / re u) + PI) by lra.
             assert (Hsum_lt_PI : atan (im u / re u) + PI < PI) by lra.
             rewrite Rabs_pos_eq; [| left; exact Hpos_sum].
             apply Rlt_le; exact Hsum_lt_PI.
      + simpl.
        pose proof (atan_bound (im u / re u)) as [Hlow Hhigh].
        assert (Habs_lt : Rabs (atan (im u / re u)) < PI/2).
        {
          destruct (Rle_lt_dec 0 (atan (im u / re u))) as [Hnonneg | Hneg].
          - rewrite Rabs_pos_eq; [| exact Hnonneg].
            exact Hhigh.
          - rewrite Rabs_left; [| exact Hneg].
            replace (PI/2) with (- (-PI/2)) by (field; lra).
            apply Ropp_lt_contravar; exact Hlow.
        }
        apply Rle_trans with (PI/2); [apply Rlt_le; exact Habs_lt | lra].
  }
  (* 主证明部分：使用 Cnorm_le_sum_abs 得到 Cnorm <= |re| + |im| *)
  assert (Hnorm_le : Cnorm (ln r +i θ) <= Rabs (ln r) + Rabs θ).
  {
    apply Cnorm_le_sum_abs.
  }
  apply Rle_trans with (Rabs (ln r) + Rabs θ).
  - exact Hnorm_le.
  - apply Rplus_le_compat_l; exact Hθ.
Qed.

(* 范数正性推出平方范数正性 *)
Lemma Cnorm_sq_pos_imp : forall z, 0 < Cnorm z -> Cnorm_sq z > 0.
Proof. intros z H; apply sqrt_pos_implies_pos; [apply Cnorm_sq_ge_0 | exact H]. Qed.

(* 定理：主值对数函数在右半平面全纯-构造性 *)
Theorem holomorphic_Clog_total : forall w (Hre : re w > 0),
  Holomorphic Clog_total w.
Proof.
  intros w Hre.
  assert (w_neq0 : w <> C0) by (intro H; rewrite H in Hre; simpl in Hre; lra).
  (* 改：用 Rlt_dec 展开 Clog_total，并利用范数平方正性消除不可能分支 *)
  unfold Clog_total.
  destruct (Rlt_dec 0 (Cnorm_sq w)) as [Hpos_w | Hnpos_w].
  - (* w 确实非零，获取与定义中一致的证明项 *)
    clear w_neq0.
    pose proof (Cnorm_sq_pos_nonzero w Hpos_w) as w_neq0.
    exists (Cinv w (nonzero_norm_sq_nonzero w w_neq0)).
    intros eps Heps.
    set (M := Cnorm w).
    assert (M_pos : 0 < M) by (apply Cnorm_pos; exact w_neq0).
    assert (epsM_pos : 0 < eps * M) by (apply Rmult_lt_0_compat; [exact Heps | exact M_pos]).
    set (eps2 := eps * M / (2 * (1 + eps * M))).
    assert (eps2_pos : 0 < eps2).
    {
      unfold eps2; apply Rdiv_lt_0_compat; [exact epsM_pos |].
      apply Rmult_lt_0_compat; [lra |].
      apply Rplus_lt_le_0_compat; [lra | apply Rmult_le_pos; [apply Rlt_le; exact Heps | apply Rlt_le; exact M_pos]].
    }
    assert (Hden_pos : 0 < 2 * (1 + eps * M)).
    {
      apply Rmult_lt_0_compat; [apply Rlt_0_2 |].
      apply Rplus_lt_le_0_compat; [lra | apply Rmult_le_pos; [apply Rlt_le; exact Heps | apply Rlt_le; exact M_pos]].
    }
    assert (eps2_lt_1 : eps2 < 1).
    {
      apply Rmult_lt_reg_l with (2 * (1 + eps * M)).
      - exact Hden_pos.
      - rewrite Rmult_1_r.
        replace (2 * (1 + eps * M) * eps2) with (eps * M).
        2: { unfold eps2; field; lra. }
        lra.
    }
    assert (eps2_le_half : eps2 <= / 2).
    {
      unfold eps2.
      apply Rmult_le_reg_l with (2 * (1 + eps * M)).
      - exact Hden_pos.
      - replace (2 * (1 + eps * M) * (eps * M / (2 * (1 + eps * M)))) with (eps * M) by (field; lra).
        replace (/ 2 * (2 * (1 + eps * M))) with (1 + eps * M) by (field; lra).
        lra.
    }
    assert (H1_minus_eps2_gt0 : 0 < 1 - eps2) by lra.
    assert (H1_eps2_ge_half : 1 - eps2 >= / 2) by lra.
    assert (H1_plus_epsM_ge_1 : 1 + eps * M >= 1) by lra.
    assert (H2_1_eps2_ge_1 : 2 * (1 - eps2) >= 1).
    {
      apply Rge_trans with (2 * / 2).
      - apply Rmult_ge_compat_l; [lra | exact H1_eps2_ge_half].
      - replace (2 * / 2) with 1 by field; apply Rge_refl.
    }
    assert (H2_ge : 2 * (1 + eps * M) >= 2) by lra.
    assert (Hden_ge_1 : 2 * (1 + eps * M) * (1 - eps2) >= 1).
    {
      assert (Htemp : 2 * (1 + eps * M) * (1 - eps2) >= 2 * (1 - eps2)).
      { apply Rmult_ge_compat_r; [lra | exact H2_ge]. }
      apply Rge_trans with (2 * (1 - eps2)); [exact Htemp | exact H2_1_eps2_ge_1].
    }
    destruct (limit_exp_minus_1_over_h eps2 eps2_pos) as [delta_exp [Hdelta_exp_pos Hdelta_exp]].
    destruct (Clog_principal_continuous w w_neq0 Hre delta_exp Hdelta_exp_pos) as [delta_log [Hdelta_log_pos Hdelta_log]].
    destruct (re_continuous w (re w / 2)) as [delta_re [Hdelta_re_pos Hdelta_re]].
    { apply Rdiv_lt_0_compat; [exact Hre | lra]. }
    set (delta := Rmin delta_log (Rmin delta_re (delta_exp / 2))).
    assert (delta_pos : 0 < delta).
    {
      apply Rmin_glb_lt; [exact Hdelta_log_pos | apply Rmin_glb_lt; [exact Hdelta_re_pos | apply Rdiv_lt_0_compat; [exact Hdelta_exp_pos | lra]]].
    }
    exists delta; split; [exact delta_pos |].
    intros h Hpos Hh.
    assert (Hh_lt_log : Cnorm h < delta_log) by (eapply Rlt_le_trans; [exact Hh | apply Rmin_l]).
    assert (Hh_lt_re : Cnorm h < delta_re).
    {
      eapply Rlt_le_trans; [exact Hh |].
      apply Rle_trans with (Rmin delta_re (delta_exp / 2)).
      - apply Rmin_r.
      - apply Rmin_l.
    }
    assert (Hh_lt_exp_half : Cnorm h < delta_exp / 2).
    {
      eapply Rlt_le_trans; [exact Hh |].
      apply Rle_trans with (Rmin delta_re (delta_exp / 2)).
      - apply Rmin_r.
      - apply Rmin_r.
    }
    set (z := w +c h).
    assert (Hzw : z -c w = h).
    {
      unfold z, Csub, Cadd; destruct w as [xw yw], h as [xh yh]; simpl; f_equal; ring.
    }
    assert (Hre_z : re z > 0).
    {
      specialize (Hdelta_re z).
      rewrite Hzw in Hdelta_re.
      apply Hdelta_re in Hh_lt_re.
      apply Rabs_def2 in Hh_lt_re as [Hupper Hlower].
      apply Rplus_lt_compat_r with (r := re w) in Hlower.
      replace (- (re w / 2) + re w) with (re w - re w / 2) in Hlower by ring.
      replace (re z - re w + re w) with (re z) in Hlower by ring.
      apply Rlt_trans with (re w - re w / 2).
      - lra.
      - exact Hlower.
    }
    assert (z_neq0 : z <> C0) by (apply re_pos_implies_neq0; exact Hre_z).
    set (u := Clog_principal z z_neq0 -c Clog_principal w w_neq0).
    assert (Hu_lt_delta_exp : Cnorm u < delta_exp).
    {
      pose proof (Hdelta_log h Hh_lt_log Hre_z) as Htmp.
      change (w +c h) with z in Htmp.
      rewrite (Clog_principal_irrel z (re_pos_implies_neq0 z Hre_z) z_neq0) in Htmp.
      exact Htmp.
    }
    assert (u_neq0 : u <> C0).
    {
      intro Hu0.
      unfold u in Hu0.
      assert (Heq : Clog_principal z z_neq0 = Clog_principal w w_neq0).
      {
        destruct (Clog_principal z z_neq0) as [rz iz], (Clog_principal w w_neq0) as [rw iw];
        unfold Csub in Hu0; simpl in Hu0;
        injection Hu0 as Hrz Hiz;
        apply Rminus_diag_uniq in Hrz;
        apply Rminus_diag_uniq in Hiz;
        rewrite Hrz, Hiz; reflexivity.
      }
      assert (Hexp_eq : Cexp (Clog_principal z z_neq0) = Cexp (Clog_principal w w_neq0)) by (rewrite Heq; reflexivity).
      rewrite !exp_Clog in Hexp_eq.
      assert (Hh_zero : h = C0).
      { rewrite <- Hzw; rewrite Hexp_eq; rewrite Csub_self; reflexivity. }
      rewrite Hh_zero in Hpos.
      assert (Cnorm_0 : Cnorm C0 = 0).
      { unfold Cnorm, Cnorm_sq; simpl; rewrite Rsqr_0, Rplus_0_l, sqrt_0; reflexivity. }
      rewrite Cnorm_0 in Hpos; lra.
    }
    assert (Hpos_u : 0 < Cnorm u) by (apply Cnorm_pos; exact u_neq0).
    set (inv_w := Cinv w (nonzero_norm_sq_nonzero w w_neq0)).
    set (target := (match Rlt_dec 0 (Cnorm_sq z) with
                    | left Hpos_z   => Clog_principal z (Cnorm_sq_pos_nonzero z Hpos_z)
                    | right Hnpos_z => C0
                    end -c
                    match Rlt_dec 0 (Cnorm_sq w) with
                    | left Hpos_w0   => Clog_principal w (Cnorm_sq_pos_nonzero w Hpos_w0)
                    | right Hnpos_w0 => C0
                    end) /c h -c inv_w).
    (* 注意：以上 target 是原证明中根据 Clog_total 展开得到的表达式，但我们可以直接利用 z_neq0 和 w_neq0 来简化 *)
    assert (Htarget_simp : target = Cdiv u h (nonzero_if_norm_positive h Hpos) -c inv_w).
    {
      unfold target.
      assert (Hz_sq_pos : 0 < Cnorm_sq z).
      { apply Cnorm_sq_pos_imp; apply Cnorm_pos; exact z_neq0. }
      destruct (Rlt_dec 0 (Cnorm_sq z)) as [Hz_pos|]; [| exfalso; lra].
      destruct (Rlt_dec 0 (Cnorm_sq w)) as [Hw_pos|]; [| exfalso; lra].
      simpl.
      unfold u.
      rewrite (Clog_principal_irrel z (Cnorm_sq_pos_nonzero z Hz_pos) z_neq0).
      rewrite (Clog_principal_irrel w (Cnorm_sq_pos_nonzero w Hw_pos) w_neq0).
      reflexivity.
    }
    set (u_div_h := Cdiv u h (nonzero_if_norm_positive h Hpos)).
    (* 以下代数恒等式与原证明完全一致 *)
    assert (Cmul_assoc_temp : forall a b c, (a *c b) *c c = a *c (b *c c)).
    { intros a b c; destruct a as [a1 a2], b as [b1 b2], c as [c1 c2]; unfold Cmul; simpl; f_equal; ring. }
    assert (Cmul_comm_temp : forall a b, a *c b = b *c a).
    { intros [a1 a2] [b1 b2]; unfold Cmul; simpl; f_equal; ring. }
    assert (Cmul_1_r_temp : forall a, a *c C1 = a).
    { intros [a1 a2]; unfold Cmul, C1; simpl; f_equal; ring. }
    assert (Cmul_1_l_temp : forall a, C1 *c a = a).
    { intros a; rewrite Cmul_comm_temp; apply Cmul_1_r_temp. }
    assert (Cmul_sub_distr_r_local : forall a b c, a *c (b -c c) = a*c b -c a*c c).
    { intros; destruct a,b,c; unfold Csub, Cmul; simpl; f_equal; ring. }
    assert (Cmul_add_distr_r_temp : forall a b c, (a +c b) *c c = a *c c +c b *c c).
    { intros [a1 a2] [b1 b2] [c1 c2]; unfold Cadd, Cmul; simpl; f_equal; ring. }
    assert (Cadd_sub_temp : forall a b, (a +c b) -c b = a).
    { intros a b; destruct a, b; unfold Cadd, Csub; simpl; f_equal; ring. }
    assert (Csub_opp_temp : forall a b, a -c b = -c (b -c a)).
    { intros a b; destruct a, b; unfold Csub, Cadd, C0; simpl; f_equal; ring. }
    assert (Cneg_invol : forall a, -c (-c a) = a).
    { intros a; destruct a; unfold Csub, Cadd, C0; simpl; f_equal; ring. }
    assert (Cmul_opp_l_temp : forall a b, (-c a) *c b = -c (a *c b)).
    { intros a b; destruct a, b; unfold Csub, C0, Cadd, Cmul; simpl; f_equal; ring. }
    assert (Cadd_comm_temp : forall a b, a +c b = b +c a).
    { intros [a1 a2] [b1 b2]; unfold Cadd; simpl; f_equal; ring. }
    assert (Complex_eq_local : forall z1 z2, re z1 = re z2 -> im z1 = im z2 -> z1 = z2).
    { intros [r1 i1] [r2 i2] Hre_eq Him_eq; simpl in *; rewrite Hre_eq, Him_eq; reflexivity. }
    assert (Cnorm_opp : forall z0, Cnorm (-c z0) = Cnorm z0).
    {
      intros z0; destruct z0 as [x y]; unfold Cnorm, Cnorm_sq, Csub, C0, Cadd; simpl.
      replace ((0 - x)²) with (x²) by (unfold Rsqr; ring).
      replace ((0 - y)²) with (y²) by (unfold Rsqr; ring).
      reflexivity.
    }
    assert (Cnorm_sq_mult_local : forall a b, Cnorm_sq (a *c b) = Cnorm_sq a * Cnorm_sq b).
    { intros a b; destruct a, b; unfold Cnorm_sq, Cmul; simpl; unfold Rsqr; ring. }
    assert (Cnorm_mult_local : forall a b, Cnorm (a *c b) = Cnorm a * Cnorm b).
    { intros a b; unfold Cnorm; rewrite Cnorm_sq_mult_local; apply sqrt_mult; apply Cnorm_sq_ge_0. }
    assert (Cnorm_triangle_rev_local : forall a b, Rabs (Cnorm a - Cnorm b) <= Cnorm (a -c b)).
    { intros a b; apply Cnorm_triangle_rev. }
    assert (Hexp_u_mul_w : Cexp u *c w = z).
    {
      unfold u; replace (Clog_principal z z_neq0 -c Clog_principal w w_neq0) with (Clog_principal z z_neq0 +c (-c Clog_principal w w_neq0)).
      2: { unfold Csub, Cadd; destruct (Clog_principal z z_neq0) as [x1 y1], (Clog_principal w w_neq0) as [x2 y2]; simpl; f_equal; ring. }
      rewrite Cexp_add; rewrite exp_Clog.
      assert (Htmp : Cexp (-c Clog_principal w w_neq0) *c w = C1).
      {
        rewrite <- (exp_Clog w w_neq0) at 2.
        rewrite <- Cexp_add.
        replace (-c Clog_principal w w_neq0 +c Clog_principal w w_neq0) with C0.
        - apply Cexp_0.
        - unfold Csub, Cadd, C0; destruct (Clog_principal w w_neq0) as [rw iw]; simpl.
          f_equal; ring.
      }
      rewrite Cmul_assoc_temp; rewrite Htmp; rewrite Cmul_1_r_temp; reflexivity.
    }
    assert (Hexp_u_eq : Cexp u = Cdiv z w (nonzero_norm_sq_nonzero w w_neq0)).
    { rewrite <- (Cdiv_mult_cancel_l (Cexp u) w (nonzero_norm_sq_nonzero w w_neq0)); rewrite Hexp_u_mul_w; reflexivity. }
    specialize (Hdelta_exp u Hpos_u Hu_lt_delta_exp).
    rename Hdelta_exp into Hnorm_D.
    set (D := Cdiv (Cexp u -c C1) u (nonzero_if_norm_positive u Hpos_u) -c C1).
    assert (Hnorm_D_lt : Cnorm D < eps2) by exact Hnorm_D.
    assert (Cexp_u_minus_1_neq0 : Cexp u -c C1 <> C0).
    {
      intro Hcontra; rewrite Hcontra in Hnorm_D.
      assert (Cdiv_0 : Cdiv C0 u (nonzero_if_norm_positive u Hpos_u) = C0).
      { unfold Cdiv, C0; set (inv_u := Cinv u (nonzero_if_norm_positive u Hpos_u)); destruct inv_u as [x y]; unfold Cmul; simpl; f_equal; ring. }
      rewrite Cdiv_0 in Hnorm_D.
      assert (Hnorm_neg_one : Cnorm (-c C1) = 1).
      {
        unfold Cnorm, Cnorm_sq, Csub, C0, C1; simpl.
        replace ((0 - 1)²) with 1 by (unfold Rsqr; ring).
        replace ((0 - 0)²) with 0 by (unfold Rsqr; ring).
        rewrite Rplus_0_r, sqrt_1; reflexivity.
      }
      rewrite Hnorm_neg_one in Hnorm_D; lra.
    }
    assert (Cnorm_C1_eq_1 : Cnorm C1 = 1).
    {
      unfold Cnorm, Cnorm_sq, C1.
      simpl.
      assert (H1 : (1² + 0²) = 1).
      { unfold Rsqr. ring. }
      rewrite H1.
      rewrite sqrt_1.
      reflexivity.
    }
    assert (C1_plus_D_neq0 : C1 +c D <> C0).
    {
      intro Hfalse; apply (f_equal Cnorm) in Hfalse.
      assert (Cnorm_0 : Cnorm C0 = 0) by (unfold Cnorm, Cnorm_sq, C0; simpl; rewrite Rsqr_0, Rplus_0_l, sqrt_0; reflexivity).
      rewrite Cnorm_0 in Hfalse.
      pose proof (Cnorm_triangle_rev_local (C1 +c D) C1) as Hrev.
      replace ((C1 +c D) -c C1) with D in Hrev.
      2: { destruct C1 as [r1 i1], D as [rd id]; unfold Cadd, Csub; simpl; f_equal; ring. }
      rewrite Hfalse, Cnorm_C1_eq_1 in Hrev; rewrite Rminus_0_l, Rabs_Ropp, Rabs_pos_eq in Hrev; [| lra].
      lra.
    }
    set (inv_CD := Cinv (C1 +c D) (nonzero_norm_sq_nonzero (C1 +c D) C1_plus_D_neq0)).
    set (inv_u := Cinv u (nonzero_norm_sq_nonzero u u_neq0)).
    set (inv_CE := Cinv (Cexp u -c C1) (nonzero_norm_sq_nonzero (Cexp u -c C1) Cexp_u_minus_1_neq0)).
    set (inv_h := Cinv h (nonzero_if_norm_positive h Hpos)).
    assert (Hfac : (Cexp u -c C1) *c inv_u = C1 +c D).
    {
      unfold inv_u; rewrite (Cinv_irrel u (nonzero_norm_sq_nonzero u u_neq0) (nonzero_if_norm_positive u Hpos_u)).
      unfold D; set (X := (Cexp u -c C1) /c u); replace (C1 +c (X -c C1)) with X.
      2: { destruct X as [x y]; unfold C1, Cadd, Csub; simpl; f_equal; ring. }
      reflexivity.
    }
    assert (u_inv_r : u *c inv_u = C1).
    {
      set (Hw_nz := nonzero_norm_sq_nonzero u u_neq0).
      rewrite <- (Cdiv_mult_cancel_l C1 u Hw_nz).
      rewrite Cmul_1_l_temp.
      reflexivity.
    }
    assert (inv_u_l : inv_u *c u = C1) by (rewrite Cmul_comm_temp; exact u_inv_r).
    assert (Hfac2 : Cexp u -c C1 = (C1 +c D) *c u).
    { rewrite <- (Cmul_1_r_temp (Cexp u -c C1)); rewrite <- inv_u_l at 2; rewrite <- Cmul_assoc_temp; rewrite Hfac; reflexivity. }
    assert (w_inv_r : w *c inv_w = C1).
    { set (Hw_nz := nonzero_norm_sq_nonzero w w_neq0); rewrite <- (Cdiv_mult_cancel_l C1 w Hw_nz); rewrite Cmul_1_l_temp; reflexivity. }
    assert (h_eq : h = w *c (Cexp u -c C1)).
    { rewrite <- Hzw; rewrite <- Hexp_u_mul_w; rewrite Cmul_comm_temp; rewrite Cmul_sub_distr_r_local; rewrite Cmul_1_r_temp; reflexivity. }
    assert (h_inv_r : h *c inv_h = C1).
    { rewrite <- (Cdiv_mult_cancel_l C1 h (nonzero_if_norm_positive h Hpos)); rewrite Cmul_1_l_temp; reflexivity. }
    assert (CE_inv_r : (Cexp u -c C1) *c inv_CE = C1).
    { pose proof (Cdiv_mult_cancel_l C1 (Cexp u -c C1) (nonzero_norm_sq_nonzero (Cexp u -c C1) Cexp_u_minus_1_neq0)) as H; rewrite Cmul_1_l_temp in H; exact H. }
    assert (inv_CE_l : inv_CE *c (Cexp u -c C1) = C1) by (rewrite Cmul_comm_temp; exact CE_inv_r).
    assert (CD_inv_r : (C1 +c D) *c inv_CD = C1).
    { pose proof (Cdiv_mult_cancel_l C1 (C1 +c D) (nonzero_norm_sq_nonzero (C1 +c D) C1_plus_D_neq0)) as H; rewrite Cmul_1_l_temp in H; unfold Cdiv in H; exact H. }
    assert (inv_h_w_eq_inv_CE : inv_h *c w = inv_CE).
    {
      assert (Hprod_eq : (inv_h *c w) *c (Cexp u -c C1) = C1).
      { rewrite Cmul_assoc_temp; rewrite <- h_eq; rewrite Cmul_comm_temp; exact h_inv_r. }
      assert (Htmp : ((inv_h *c w) *c (Cexp u -c C1)) *c inv_CE = inv_CE).
      { rewrite Hprod_eq; rewrite Cmul_1_l_temp; reflexivity. }
      rewrite Cmul_assoc_temp in Htmp; rewrite CE_inv_r in Htmp; rewrite Cmul_1_r_temp in Htmp; exact Htmp.
    }
    assert (inv_h_eq : inv_h = inv_CE *c inv_w).
    {
      assert (h_inv_CE_inv_w : h *c (inv_CE *c inv_w) = C1).
      { rewrite h_eq; rewrite Cmul_assoc_temp; rewrite <- Cmul_assoc_temp with (a := Cexp u -c C1) (b := inv_CE) (c := inv_w); rewrite CE_inv_r; rewrite Cmul_1_l_temp; rewrite w_inv_r; reflexivity. }
      assert (Hmul_eq : h *c inv_h = h *c (inv_CE *c inv_w)) by (rewrite h_inv_r; symmetry; exact h_inv_CE_inv_w).
      apply (f_equal (fun x => inv_h *c x)) in Hmul_eq.
      rewrite h_inv_r in Hmul_eq; rewrite Cmul_1_r_temp in Hmul_eq.
      rewrite Hmul_eq; rewrite <- Cmul_assoc_temp; rewrite (Cmul_comm_temp inv_h h), h_inv_r; rewrite Cmul_1_l_temp; reflexivity.
    }
    assert (u_inv_CE_eq_inv_CD : u *c inv_CE = inv_CD).
    {
      assert (inv_u_eq : inv_u = inv_CE *c (C1 +c D)).
      { rewrite <- (Cmul_1_l_temp inv_u); rewrite <- inv_CE_l at 1; rewrite Cmul_assoc_temp; rewrite Hfac; reflexivity. }
      assert (u_inv_CE_times_CD : u *c inv_CE *c (C1 +c D) = C1).
      { rewrite Cmul_assoc_temp; rewrite <- inv_u_eq; rewrite u_inv_r; reflexivity. }
      rewrite <- (Cmul_1_r_temp (u *c inv_CE)); rewrite <- CD_inv_r; rewrite <- Cmul_assoc_temp; rewrite u_inv_CE_times_CD; rewrite Cmul_1_l_temp; reflexivity.
    }
    assert (u_div_h_eq : u_div_h = inv_w *c inv_CD).
    {
      unfold u_div_h; assert (u_div_h_eq1 : Cdiv u h (nonzero_if_norm_positive h Hpos) = u *c inv_h) by (unfold Cdiv; reflexivity).
      rewrite u_div_h_eq1; rewrite inv_h_eq; rewrite <- Cmul_assoc_temp; rewrite u_inv_CE_eq_inv_CD; rewrite Cmul_comm_temp; reflexivity.
    }
    assert (Htarget_eq : target = inv_w *c (inv_CD -c C1)).
    { rewrite Htarget_simp; replace (Cdiv u h (nonzero_if_norm_positive h Hpos)) with u_div_h by (unfold u_div_h; reflexivity).
      rewrite u_div_h_eq; rewrite Cmul_sub_distr_r_local; rewrite Cmul_1_r_temp; reflexivity. }
    assert (Hinv_CD_minus_C1 : inv_CD -c C1 = -c D *c inv_CD).
    {
      assert (Hmul_eq : (C1 +c D) *c inv_CD = C1) by exact CD_inv_r.
      rewrite Cmul_add_distr_r_temp in Hmul_eq; rewrite Cmul_1_l_temp in Hmul_eq.
      apply (f_equal (fun x => x -c inv_CD)) in Hmul_eq.
      rewrite (Cadd_comm_temp inv_CD (D *c inv_CD)) in Hmul_eq; rewrite Cadd_sub_temp in Hmul_eq.
      rewrite (Csub_opp_temp C1 inv_CD) in Hmul_eq; apply (f_equal (fun x => -c x)) in Hmul_eq.
      rewrite Cneg_invol in Hmul_eq; rewrite <- Cmul_opp_l_temp in Hmul_eq; symmetry; exact Hmul_eq.
    }
    assert (Hnorm_inv_CD_minus_C1 : Cnorm (inv_CD -c C1) = Cnorm D * Cnorm inv_CD).
    { rewrite Hinv_CD_minus_C1; rewrite Cnorm_mult_local; rewrite Cnorm_opp; reflexivity. }
    assert (Hnorm_inv_CD : Cnorm inv_CD = / Cnorm (C1 +c D)).
    {
      apply (f_equal Cnorm) in CD_inv_r; rewrite Cnorm_mult_local in CD_inv_r.
      rewrite Cnorm_C1_eq_1 in CD_inv_r.
      apply Rmult_eq_reg_l with (Cnorm (C1 +c D)).
      - rewrite CD_inv_r; rewrite Rinv_r; [reflexivity | apply Rgt_not_eq; apply Cnorm_pos; exact C1_plus_D_neq0].
      - apply Rgt_not_eq; apply Cnorm_pos; exact C1_plus_D_neq0.
    }
    assert (Hnorm_inv_w : Cnorm inv_w = / M).
    {
      apply (Rmult_eq_reg_l M).
      - unfold M; rewrite Rinv_r; [| apply Rgt_not_eq; exact M_pos].
        rewrite <- Cnorm_mult_local; rewrite w_inv_r.
        rewrite Cnorm_C1_eq_1; reflexivity.
      - apply Rgt_not_eq; exact M_pos.
    }
    pose proof (Cnorm_triangle_rev_local (C1 +c D) C1) as Hrev.
    replace ((C1 +c D) -c C1) with D in Hrev.
    2: { destruct C1 as [r1 i1], D as [rd id]; unfold Cadd, Csub; simpl; f_equal; ring. }
    rewrite Cnorm_C1_eq_1 in Hrev.
    (* 修改点：Hnorm_D_nonneg 的构造性证明 *)
    assert (Hnorm_D_nonneg : 0 <= Cnorm D).
    { apply Cnorm_ge_0. }
    assert (Habs_decomp : - (Cnorm D) <= Cnorm (C1 +c D) - 1 <= Cnorm D).
    {
      unfold Rabs in Hrev; simpl in Hrev.
      case (Rcase_abs (Cnorm (C1 +c D) - 1)) as [H_abs_neg | H_abs_pos]; simpl in Hrev.
      - split; [lra | lra].
      - split; [lra | exact Hrev].
    }
    assert (H_main1 : Cnorm (C1 +c D) >= 1 - Cnorm D).
    { destruct Habs_decomp as [H_lower _]; lra. }
    assert (H_pos1 : 1 - Cnorm D > 0).
    {
      assert (H3 : Cnorm D < eps2) by exact Hnorm_D_lt.
      assert (H4 : eps2 <= 1 - 1/2).
      { apply Rle_trans with (1 := eps2_le_half); lra. }
      lra.
    }
    assert (H_main2 : 1 / Cnorm (C1 +c D) <= 1 / (1 - Cnorm D)).
    {
      assert (H_den1_pos : 0 < Cnorm (C1 +c D)) by lra.
      assert (H_den2_pos : 0 < 1 - Cnorm D) by exact H_pos1.
      assert (H5 : 1 - Cnorm D <= Cnorm (C1 +c D)) by lra.
      assert (H_pos_prod : 0 < (1 - Cnorm D) * Cnorm (C1 +c D)).
      { apply Rmult_lt_0_compat; exact H_den2_pos || exact H_den1_pos. }
      assert (H_nz1 : Cnorm (C1 +c D) <> 0).
      { intro H_contra; rewrite H_contra in H_den1_pos; lra. }
      assert (H_nz2 : (1 - Cnorm D) <> 0).
      { intro H_contra; rewrite H_contra in H_den2_pos; lra. }
      apply (Rmult_le_reg_r ((1 - Cnorm D) * Cnorm (C1 +c D))).
      - exact H_pos_prod.
      - assert (H_left : (1 / Cnorm (C1 +c D)) * ((1 - Cnorm D) * Cnorm (C1 +c D)) = (1 - Cnorm D)).
        { field; exact H_nz1. }
        assert (H_right : (1 / (1 - Cnorm D)) * ((1 - Cnorm D) * Cnorm (C1 +c D)) = Cnorm (C1 +c D)).
        { field; exact H_nz2. }
        rewrite H_left, H_right. exact H5.
    }
    assert (H_norm_target : Cnorm target = Cnorm inv_w * (Cnorm D * Cnorm inv_CD)).
    { rewrite Htarget_eq; rewrite Cnorm_mult_local; rewrite Hnorm_inv_CD_minus_C1; ring. }
    rewrite H_norm_target; rewrite Hnorm_inv_w; rewrite Hnorm_inv_CD.
    assert (H_final1 : Cnorm D * (1 / Cnorm (C1 +c D)) <= Cnorm D * (1 / (1 - Cnorm D))).
    { apply Rmult_le_compat_l with (r := Cnorm D); [exact Hnorm_D_nonneg | exact H_main2]. }
    assert (H_eq1 : 1 / Cnorm (C1 +c D) = / Cnorm (C1 +c D)).
    {
      field.
      intro H_contra.
      assert (H_contradiction : 0 >= 1 - Cnorm D).
      { rewrite H_contra in H_main1; exact H_main1. }
      lra.
    }
    assert (H_eq2 : 1 / (1 - Cnorm D) = / (1 - Cnorm D)).
    {
      field.
      intro H_contra.
      rewrite H_contra in H_pos1; lra.
    }
    assert (H_final1' : Cnorm D * / Cnorm (C1 +c D) <= Cnorm D * / (1 - Cnorm D)).
    { rewrite <- H_eq1, <- H_eq2; exact H_final1. }
    assert (H_step1 : / M * (Cnorm D * / Cnorm (C1 +c D)) <= / M * (Cnorm D * / (1 - Cnorm D))).
    {
      assert (H_pos_M : 0 <= / M).
      { apply Rlt_le; apply Rinv_0_lt_compat; exact M_pos. }
      apply Rmult_le_compat_l; [exact H_pos_M | exact H_final1'].
    }
    assert (H_one_minus_bound : 1 / (1 - Cnorm D) <= 2 * (1 + eps * M)).
    {
      assert (H_half_eq : 1 / 2 = / 2) by field.
      assert (H1 : Cnorm D <= 1 / 2).
      { apply Rle_trans with (eps2); [apply Rlt_le; exact Hnorm_D_lt | rewrite H_half_eq; exact eps2_le_half]. }
      assert (H2 : 1 - Cnorm D >= 1 / 2) by lra.
      assert (H3 : 1 / (1 - Cnorm D) <= 2).
      {
        assert (H_inv_D_eq : 1 / (1 - Cnorm D) = / (1 - Cnorm D)) by (field; lra).
        assert (H_inv_half_eq : 2 = / (1 / 2)) by field.
        rewrite H_inv_half_eq; rewrite H_inv_D_eq.
        apply Rinv_le_contravar with (x := 1 / 2) (y := 1 - Cnorm D); [lra | lra].
      }
      assert (H4 : 2 <= 2 * (1 + eps * M)).
      { assert (H5 : 0 < eps * M) by exact epsM_pos; lra. }
      lra.
    }
    assert (H_step2 : / M * (Cnorm D * / (1 - Cnorm D)) <= / M * (Cnorm D * (2 * (1 + eps * M)))).
    {
      assert (H_pos_M : 0 <= / M).
      { apply Rlt_le; apply Rinv_0_lt_compat; exact M_pos. }
      apply Rmult_le_compat_l.
      - exact H_pos_M.
      - apply Rmult_le_compat_l.
        + exact Hnorm_D_nonneg.
        + assert (H_eq3 : 1 / (1 - Cnorm D) = / (1 - Cnorm D)) by (field; lra).
          rewrite <- H_eq3; exact H_one_minus_bound.
    }
    assert (H_simp_eq : / M * (Cnorm D * (2 * (1 + eps * M))) = 2 * Cnorm D * (1 + eps * M) / M).
    {
      field.
      intro H_contra.
      rewrite H_contra in M_pos; lra.
    }
    rewrite H_simp_eq in H_step2.
    assert (H_final_ineq : 2 * Cnorm D * (1 + eps * M) / M < eps).
    {
      set (r := 2 * (1 + eps * M)).
      assert (H_eps2_unfold : Cnorm D < eps * M / r).
      { simpl in Hnorm_D_lt; unfold eps2, r in Hnorm_D_lt; exact Hnorm_D_lt. }
      assert (Hr_pos : 0 < r) by (unfold r; exact Hden_pos).
      assert (Hr_nonzero : r <> 0) by (intro H; lra).
      assert (H_mul_l : r * Cnorm D < r * (eps * M / r)).
      { apply Rmult_lt_compat_l; [exact Hr_pos | exact H_eps2_unfold]. }
      assert (H_cancel : r * (eps * M / r) = eps * M).
      { field; exact Hr_nonzero. }
      assert (H1 : r * Cnorm D < eps * M) by (rewrite H_cancel in H_mul_l; exact H_mul_l).
      assert (H_comm : Cnorm D * r = r * Cnorm D) by ring.
      assert (H1' : Cnorm D * r < eps * M) by (rewrite H_comm; exact H1).
      assert (H_inv_M_pos : 0 < / M).
      { apply Rinv_0_lt_compat; exact M_pos. }
      assert (H_mul_inv : (Cnorm D * r) * / M < (eps * M) * / M).
      { apply Rmult_lt_compat_r; [exact H_inv_M_pos | exact H1']. }
      assert (H_rhs_simp : (eps * M) * / M = eps).
      { field; intro H; rewrite H in M_pos; lra. }
      assert (H2 : (Cnorm D * r) * / M < eps).
      { rewrite H_rhs_simp in H_mul_inv; exact H_mul_inv. }
      unfold r in H2.
      assert (H_final_eq : (2 * Cnorm D * (1 + eps * M)) / M = (Cnorm D * (2 * (1 + eps * M))) / M).
      { f_equal; ring. }
      rewrite H_final_eq; exact H2.
    }
    assert (H_intermediate : / M * (Cnorm D * / (1 - Cnorm D)) < eps).
    { eapply Rle_lt_trans; [eexact H_step2 | eexact H_final_ineq]. }
    eapply Rle_lt_trans; [eexact H_step1 | eexact H_intermediate].
  - (* 不可能分支：Cnorm_sq w <= 0 与 re w > 0 矛盾 *)
    exfalso.
    assert (Hnorm_sq_w_pos : 0 < Cnorm_sq w).
    { apply Cnorm_sq_pos_imp; apply Cnorm_pos; exact w_neq0. }
    lra.
Qed.

(* 范数取反不变 *)
Lemma Cnorm_neg : forall z, Cnorm (-c z) = Cnorm z.
Proof.
  intros [x y]; unfold Cnorm, Cnorm_sq, Csub, C0; simpl.
  replace (0 - x) with (-x) by ring.
  replace (0 - y) with (-y) by ring.
  assert (H: (-x)² + (-y)² = x² + y²).
  { unfold Rsqr; ring. }
  rewrite H; reflexivity.
Qed.

(* C1的范数为1 *)
Lemma Cnorm_one : Cnorm C1 = 1.
Proof.
  unfold C1, Cnorm, Cnorm_sq; simpl.
  rewrite Rsqr_1, Rsqr_0, Rplus_0_r, sqrt_1; reflexivity.
Qed.

(* C0的范数为0 *)
Lemma Cnorm_0 : Cnorm C0 = 0.
Proof.
  unfold C0, Cnorm, Cnorm_sq; simpl.
  rewrite Rsqr_0, Rplus_0_l, sqrt_0; reflexivity.
Qed.




(* ============================================================
   左半平面（不含负实轴）主支对数全纯性
   依赖：ComplexNumbers, HolomorphicFunctions, ComplexLogarithm
   ============================================================ *)

Import ComplexNumbers.
Import HolomorphicFunctions.
Import ComplexLogarithm.
Import ComplexBasics.
Require Import Stdlib.Reals.Reals.
Local Open Scope complex_scope.
Local Open Scope R_scope.

(* 右半平面主支对数全纯 *)
Theorem holomorphic_Clog_total_right : forall w (Hre : re w > 0),
  Holomorphic ClogBoundModule.Clog_total w.
Proof. exact holomorphic_Clog_total. Qed.

(* ----------------------------------------------------------- *)
(* 1. 辐角 atan2 在左半平面的平移公式                        *)
(* ----------------------------------------------------------- *)

(* 左上半平面辐角平移加π *)
Lemma atan2_left_upper_plus_pi : forall v (Hre : re v < 0) (Him : im v > 0),
  atan2 (im v) (re v) = atan2 (im (-c v)) (re (-c v)) + PI.
Proof.
  intros [x y] Hx Hy.
  simpl in Hx, Hy.
  unfold atan2; simpl.
  replace (0 - x) with (-x) by ring.
  replace (0 - y) with (-y) by ring.
  assert (Hx_neq0 : x <> 0) by lra.
  assert (Hmx_gt0 : -x > 0) by lra.
  destruct (Req_dec_T x 0) as [Hx0|Hx_neq0'].
  - exfalso; auto.
  - destruct (Rlt_dec x 0) as [Hx_lt0|].
    + destruct (Rlt_dec y 0) as [Hy_lt0|Hy_ge0].
      * exfalso; lra.
      * destruct (Req_dec_T (- x) 0) as [Hmx0|].
        { exfalso; lra. }
        destruct (Rlt_dec (- x) 0) as [Hmx_lt0|].
        { exfalso; lra. }
        simpl.
        replace ((-y) / (-x)) with (y / x) by (field; lra).
        ring.
    + exfalso; lra.
Qed.

(* 左下半平面辐角平移减π *)
Lemma atan2_left_lower_minus_pi : forall v (Hre : re v < 0) (Him : im v < 0),
  atan2 (im v) (re v) = atan2 (im (-c v)) (re (-c v)) - PI.
Proof.
  intros [x y] Hx Hy.
  simpl in Hx, Hy.
  unfold atan2; simpl.
  replace (0 - x) with (-x) by ring.
  replace (0 - y) with (-y) by ring.
  assert (Hx_neq0 : x <> 0) by lra.
  assert (Hmx_gt0 : -x > 0) by lra.
  destruct (Req_dec_T x 0) as [Hx0|Hx_neq0'].
  - exfalso; auto.
  - destruct (Rlt_dec x 0) as [Hx_lt0|].
    + destruct (Rlt_dec y 0) as [Hy_lt0|Hy_ge0].
      * destruct (Req_dec_T (- x) 0) as [Hmx0|].
        { exfalso; lra. }
        destruct (Rlt_dec (- x) 0) as [Hmx_lt0|].
        { exfalso; lra. }
        simpl.
        replace ((-y) / (-x)) with (y / x) by (field; lra).
        ring.
      * exfalso; lra.
    + exfalso; lra.
Qed.

(* 负号对合 *)
Local Lemma Cneg_involutive : forall z : Complex, -c (-c z) = z.
Proof.
  intros [x y]; unfold Csub, Cadd, C0; simpl; f_equal; ring.
Qed.

(* 负零推出原零 *)
Local Lemma neg_eq_0_impl_eq_0 : forall v : Complex, -c v = C0 -> v = C0.
Proof.
  intros [x y] H.
  unfold Csub, C0 in H; simpl in H.
  pose proof (f_equal re H) as Hx; simpl in Hx.
  pose proof (f_equal im H) as Hy; simpl in Hy.
  unfold C0; f_equal; lra.
Qed.

(* 实部虚部相等决定复数相等 *)
Local Lemma complex_eq_re_im (z w : Complex) : re z = re w -> im z = im w -> z = w.
Proof.
  destruct z as [x1 y1], w as [x2 y2]; simpl; intros Hre Him; subst; reflexivity.
Qed.

(* 左上半平面主支对数平移公式 *)
Lemma Clog_principal_left_upper_shift :
  forall v (Hre : re v < 0) (Him : im v > 0) (Hv : v <> C0),
  let Hminusv : (-c v) <> C0 := fun H => Hv (neg_eq_0_impl_eq_0 v H) in
  Clog_principal v Hv = Clog_principal (-c v) Hminusv +c CI *c C_of_R PI.
Proof.
  intros v Hre Him Hv Hminusv.
  unfold Clog_principal.
  apply complex_eq_re_im.
  - simpl. rewrite Cnorm_neg. ring_simplify. reflexivity.
  - simpl.
    replace (0 - im v) with (im (-c v)) by (unfold Csub; simpl; ring).
    replace (0 - re v) with (re (-c v)) by (unfold Csub; simpl; ring).
    replace (0 * 0 + 1 * PI) with PI by ring.
    rewrite (atan2_left_upper_plus_pi v Hre Him). reflexivity.
Qed.

(* 左下半平面主支对数平移公式 *)
Lemma Clog_principal_left_lower_shift :
  forall v (Hre : re v < 0) (Him : im v < 0) (Hv : v <> C0),
  let Hminusv : (-c v) <> C0 := fun H => Hv (neg_eq_0_impl_eq_0 v H) in
  Clog_principal v Hv = Clog_principal (-c v) Hminusv -c CI *c C_of_R PI.
Proof.
  intros v Hre Him Hv Hminusv.
  unfold Clog_principal.
  apply complex_eq_re_im.
  - simpl; rewrite Cnorm_neg.
    replace (0 * PI - 1 * 0) with 0 by ring.
    rewrite Rminus_0_r; reflexivity.
  - simpl.
    replace (0 - im v) with (im (-c v)) by (unfold Csub; simpl; ring).
    replace (0 - re v) with (re (-c v)) by (unfold Csub; simpl; ring).
    replace (0 * 0 + 1 * PI) with PI by ring.
    rewrite (atan2_left_lower_minus_pi v Hre Him); reflexivity.
Qed.

(* 实部小于零推出非零 *)
Lemma neq0_from_re_lt0 : forall v, re v < 0 -> v <> C0.
Proof.
  intros v Hre Heq; rewrite Heq in Hre; simpl in Hre; lra.
Qed.

(* 局部邻域定义 *)
Definition locally (w : Complex) (P : Complex -> Prop) : Prop :=
  exists eps : R, eps > 0 /\ forall v : Complex, Cnorm (v -c w) < eps -> P v.

(* 左上半平面局部平移恒等式 *)
Lemma Clog_total_left_upper_shift_locally :
  forall w (Hre : re w < 0) (Him : im w > 0),
  locally w (fun v => Clog_total v = Clog_total (-c v) +c CI *c C_of_R PI).
Proof.
  intros w Hre Him.
  set (eps0 := Rmin ((- re w) / 2) (im w / 2)).
  assert (Heps0 : eps0 > 0) by (apply Rmin_pos; lra).
  exists eps0; split; [exact Heps0 |].
  intros v Hv.
  assert (Hre_diff : Rabs (re v - re w) < eps0).
  {
    assert (Hre_sub : re (v -c w) = re v - re w).
    { destruct v, w; unfold Csub; simpl; ring. }
    rewrite <- Hre_sub.
    apply Rle_lt_trans with (Cnorm (v -c w)).
    - apply re_le_Cnorm.
    - exact Hv.
  }
  assert (Him_diff : Rabs (im v - im w) < eps0).
  {
    assert (Him_sub : im (v -c w) = im v - im w).
    { destruct v, w; unfold Csub; simpl; ring. }
    rewrite <- Him_sub.
    apply Rle_lt_trans with (Cnorm (v -c w)).
    - apply im_le_Cnorm.
    - exact Hv.
  }
  pose proof (Rabs_def2 _ _ Hre_diff) as [Hre_low Hre_high].
  pose proof (Rabs_def2 _ _ Him_diff) as [Him_low Him_high].
  assert (Hre_v : re v < 0).
  {
    assert (Heps0_le : eps0 <= (- re w) / 2) by (unfold eps0; apply Rmin_l).
    lra.
  }
  assert (Him_v : im v > 0).
  {
    assert (Heps0_le_im : eps0 <= im w / 2) by (unfold eps0; apply Rmin_r).
    lra.
  }
  assert (Hv_neq0 : v <> C0) by (apply neq0_from_re_lt0; exact Hre_v).
  assert (Hminusv_neq0 : (-c v) <> C0). {
    intro H; apply Hv_neq0; apply neg_eq_0_impl_eq_0; exact H.
  }
  unfold Clog_total.
  destruct (Rlt_dec 0 (Cnorm_sq v)) as [Hv_pos | Hv_nonpos].
  - (* v 非零 *)
    destruct (Rlt_dec 0 (Cnorm_sq (-c v))) as [Hmv_pos | Hmv_nonpos].
    + (* -c v 非零 *)
      pose proof (Clog_principal_left_upper_shift v Hre_v Him_v (Cnorm_sq_pos_nonzero v Hv_pos)) as Hshift.
      simpl in Hshift.
      rewrite (Clog_principal_irrel (-c v)
        (fun H : -c v = C0 => Cnorm_sq_pos_nonzero v Hv_pos (neg_eq_0_impl_eq_0 v H))
        (Cnorm_sq_pos_nonzero (-c v) Hmv_pos)) in Hshift.
      exact Hshift.
    + (* -c v 为零，矛盾 *)
      exfalso.
      assert (Cnorm_sq (-c v) = 0) by (apply Rle_antisym; [lra | apply Cnorm_sq_ge0]).
      apply Hminusv_neq0; apply Cnorm_sq_eq_0; assumption.
  - (* v 为零，矛盾 *)
    exfalso.
    assert (Cnorm_sq v = 0) by (apply Rle_antisym; [lra | apply Cnorm_sq_ge0]).
    apply Hv_neq0; apply Cnorm_sq_eq_0; assumption.
Qed.


(* 左下半平面局部平移恒等式 *)
Lemma Clog_total_left_lower_shift_locally :
  forall w (Hre : re w < 0) (Him : im w < 0),
  locally w (fun v => Clog_total v = Clog_total (-c v) -c CI *c C_of_R PI).
Proof.
  intros w Hre Him.
  set (eps0 := Rmin ((- re w) / 2) ((- im w) / 2)).
  assert (Heps0 : eps0 > 0) by (apply Rmin_pos; lra).
  exists eps0; split; [exact Heps0 |].
  intros v Hv.
  assert (Hre_diff : Rabs (re v - re w) < eps0).
  {
    assert (Hre_sub : re (v -c w) = re v - re w).
    { destruct v, w; unfold Csub; simpl; ring. }
    rewrite <- Hre_sub.
    apply Rle_lt_trans with (Cnorm (v -c w)).
    - apply re_le_Cnorm.
    - exact Hv.
  }
  assert (Him_diff : Rabs (im v - im w) < eps0).
  {
    assert (Him_sub : im (v -c w) = im v - im w).
    { destruct v, w; unfold Csub; simpl; ring. }
    rewrite <- Him_sub.
    apply Rle_lt_trans with (Cnorm (v -c w)).
    - apply im_le_Cnorm.
    - exact Hv.
  }
  pose proof (Rabs_def2 _ _ Hre_diff) as [Hre_low Hre_high].
  pose proof (Rabs_def2 _ _ Him_diff) as [Him_low Him_high].
  assert (Hre_v : re v < 0).
  {
    assert (Heps0_le : eps0 <= (- re w) / 2) by (unfold eps0; apply Rmin_l).
    lra.
  }
  assert (Him_v : im v < 0).
  {
    assert (Heps0_le_im : eps0 <= (- im w) / 2) by (unfold eps0; apply Rmin_r).
    lra.
  }
  assert (Hv_neq0 : v <> C0) by (apply neq0_from_re_lt0; exact Hre_v).
  assert (Hminusv_neq0 : (-c v) <> C0). {
    intro H; apply Hv_neq0; apply neg_eq_0_impl_eq_0; exact H.
  }
  unfold Clog_total.
  destruct (Rlt_dec 0 (Cnorm_sq v)) as [Hv_pos | Hv_nonpos].
  - (* v 非零 *)
    destruct (Rlt_dec 0 (Cnorm_sq (-c v))) as [Hmv_pos | Hmv_nonpos].
    + (* -c v 非零 *)
      pose proof (Clog_principal_left_lower_shift v Hre_v Him_v (Cnorm_sq_pos_nonzero v Hv_pos)) as Hshift.
      simpl in Hshift.   (* 展开 let *)
      rewrite (Clog_principal_irrel (-c v)
        (fun H : -c v = C0 => Cnorm_sq_pos_nonzero v Hv_pos (neg_eq_0_impl_eq_0 v H))
        (Cnorm_sq_pos_nonzero (-c v) Hmv_pos)) in Hshift.
      exact Hshift.
    + (* -c v 为零，与 Hminusv_neq0 矛盾 *)
      exfalso.
      assert (Hc0 : Cnorm_sq (-c v) = 0) by (apply Rle_antisym; [lra | apply Cnorm_sq_ge0]).
      apply Hminusv_neq0; apply Cnorm_sq_eq_0; exact Hc0.
  - (* v 为零，与 Hv_neq0 矛盾 *)
    exfalso.
    assert (Hc0 : Cnorm_sq v = 0) by (apply Rle_antisym; [lra | apply Cnorm_sq_ge0]).
    apply Hv_neq0; apply Cnorm_sq_eq_0; exact Hc0.
Qed.

(* 复数范数非负 *)
Lemma Cnorm_ge_0 : forall z : Complex, 0 <= Cnorm z.
Proof. intro z; unfold Cnorm; apply sqrt_pos; apply Cnorm_sq_ge_0. Qed.

(* 平方不等式反推原数不等式 *)
Lemma Rsqr_le_0 : forall x y, 0 <= x -> 0 <= y -> x * x <= y * y -> x <= y.
Proof.
  intros x y Hx Hy Hsq.
  destruct (Rle_dec x y); auto.
  assert (Hlt : y < x) by lra.
  assert (Hx_gt0 : 0 < x) by lra.
  assert (Hsq_lt : y * y < x * x).
  { destruct (Rlt_dec 0 y) as [Hy_pos | Hy_not_pos].
    - apply Rlt_trans with (y * x).
      + apply Rmult_lt_compat_l; [exact Hy_pos | exact Hlt].
      + apply Rmult_lt_compat_r; [exact Hx_gt0 | exact Hlt].
    - assert (Hy0 : y = 0) by lra.
      rewrite Hy0; ring_simplify.
      apply Rmult_lt_0_compat; lra. }
  lra.
Qed.

(* 复数加法与减法的结合律： (a + b) - b = a *)
Lemma Cadd_sub : forall a b : Complex, (a +c b) -c b = a.
Proof.
  intros [xa ya] [xb yb]; unfold Cadd, Csub; simpl; f_equal; ring.
Qed.

(* 绝对值平方等于原数平方 *)
Lemma Rabs_sq_eq : forall x : R, Rabs x * Rabs x = x * x.
Proof.
  intros x.
  assert (H := Rsqr_abs x).
  unfold Rsqr in H.
  symmetry. exact H.
Qed.

(* 复数范数的三角不等式 *)
Lemma Cnorm_triangle : forall z1 z2 : Complex, Cnorm (z1 +c z2) <= Cnorm z1 + Cnorm z2.
Proof.
  intros z1 z2.
  set (a := Cnorm (z1 +c z2)).
  set (b := Cnorm z1 + Cnorm z2).
  assert (Ha_nonneg : 0 <= a) by (unfold a; apply Cnorm_ge_0).
  assert (Hb_nonneg : 0 <= b) by (apply Rplus_le_le_0_compat; apply Cnorm_ge_0).
  assert (H_sq : a * a <= b * b).
  {
    unfold a, b.
    assert (H_sq_a : Cnorm_sq (z1 +c z2) = (Cnorm (z1 +c z2)) * (Cnorm (z1 +c z2))).
    { symmetry; apply Rsqr_sqrt; apply Cnorm_sq_ge_0. }
    assert (H_sq_b : (Cnorm z1 + Cnorm z2) * (Cnorm z1 + Cnorm z2) =
                     Cnorm_sq z1 + Cnorm_sq z2 + 2 * (Cnorm z1 * Cnorm z2)).
    {
      replace ((Cnorm z1 + Cnorm z2) * (Cnorm z1 + Cnorm z2))
        with ((Cnorm z1)^2 + (Cnorm z2)^2 + 2 * Cnorm z1 * Cnorm z2) by ring.
      unfold Cnorm at 1 2 3 4.
      replace (sqrt (Cnorm_sq z1) ^ 2) with (sqrt (Cnorm_sq z1) * sqrt (Cnorm_sq z1)) by ring.
      replace (sqrt (Cnorm_sq z2) ^ 2) with (sqrt (Cnorm_sq z2) * sqrt (Cnorm_sq z2)) by ring.
      replace (sqrt (Cnorm_sq z1) * sqrt (Cnorm_sq z1)) with (Cnorm_sq z1).
      2: { symmetry; apply Rsqr_sqrt; apply Cnorm_sq_ge_0. }
      replace (sqrt (Cnorm_sq z2) * sqrt (Cnorm_sq z2)) with (Cnorm_sq z2).
      2: { symmetry; apply Rsqr_sqrt; apply Cnorm_sq_ge_0. }
      unfold Cnorm; ring.
    }
    rewrite <- H_sq_a.
    rewrite H_sq_b.
    clear H_sq_a H_sq_b.
    assert (HCnorm_sq_add : Cnorm_sq (z1 +c z2) = Cnorm_sq z1 + Cnorm_sq z2 + 2 * (re z1 * re z2 + im z1 * im z2)).
    { unfold Cnorm_sq, Cadd; simpl; unfold Rsqr; ring. }
    rewrite HCnorm_sq_add.
    set (S := re z1 * re z2 + im z1 * im z2).
    assert (H_abs_S : Rabs S <= Cnorm z1 * Cnorm z2).
    {
      apply Rsqr_le_0; [apply Rabs_pos | apply Rmult_le_pos; apply Cnorm_ge_0 |].
      rewrite (Rabs_sq_eq S).
      replace ((Cnorm z1 * Cnorm z2) * (Cnorm z1 * Cnorm z2))
        with ((Cnorm z1 * Cnorm z1) * (Cnorm z2 * Cnorm z2)) by ring.
      replace (Cnorm z1 * Cnorm z1) with (Cnorm_sq z1).
      2: { unfold Cnorm; symmetry; apply Rsqr_sqrt; apply Cnorm_sq_ge_0. }
      replace (Cnorm z2 * Cnorm z2) with (Cnorm_sq z2).
      2: { unfold Cnorm; symmetry; apply Rsqr_sqrt; apply Cnorm_sq_ge_0. }
      apply CauchySchwarz_sq with (z := z1) (w := z2).
    }
    assert (H_S_le : S <= Cnorm z1 * Cnorm z2).
    { apply Rle_trans with (Rabs S); [apply Rle_abs | exact H_abs_S]. }
    lra.
  }
  apply Rsqr_le_0; assumption.
Qed.

(* 复数减法自反性 *)
Lemma Csub_self (z : Complex) : z -c z = C0.
Proof.
  destruct z as [x y]; unfold Csub, C0; simpl; f_equal; ring.
Qed.

(* 复数左乘零元 *)
Lemma Cmul_0_l (z : Complex) : C0 *c z = C0.
Proof.
  destruct z as [x y]; unfold Cmul, C0; simpl; f_equal; ring.
Qed.

(* 零除以非零复数为零 *)
Lemma Cdiv_0_l (z : Complex) (H : Cnorm_sq z <> 0) : Cdiv C0 z H = C0.
Proof.
  unfold Cdiv; rewrite Cmul_0_l; reflexivity.
Qed.

(* 全纯函数组合子 *)
Section HolomorphicCombinators.
Variable (f g : Complex -> Complex).
Variable (w : Complex).

Hypothesis (Hf : Holomorphic f w).
Hypothesis (Hg : Holomorphic g w).

(* 乘法结合律 *)
Lemma Cmul_assoc_temp : forall a b c : Complex, (a *c b) *c c = a *c (b *c c).
Proof. intros [a1 a2] [b1 b2] [c1 c2]; unfold Cmul; simpl; f_equal; ring. Qed.

(* 右乘单位元 *)
Lemma Cmul_1_r_temp : forall a : Complex, a *c (1 +i 0) = a.
Proof. intros [a1 a2]; unfold Cmul, Cadd, C0; simpl; f_equal; ring. Qed.

(* 逆元右乘 *)
Lemma Cinv_r (z : Complex) (H : Cnorm_sq z <> 0) : z *c Cinv z H = (1 +i 0).
Proof.
  destruct z as [x y]; unfold Cinv, Cnorm_sq, Cmul, Cadd, C0; simpl.
  unfold Rsqr in *.
  apply complex_eq_re_im; simpl.
  - field. assumption.
  - field. assumption.
Qed.

(* 右消去律 *)
Lemma Cdiv_mul_cancel_r (a h : Complex) (H : Cnorm_sq h <> 0) : (a *c h) *c Cinv h H = a.
Proof.
  transitivity (a *c (h *c Cinv h H)).
  - rewrite Cmul_assoc_temp. reflexivity.
  - rewrite (Cinv_r h H). apply Cmul_1_r_temp.
Qed.

(* 负数函数全纯 *)
Local Lemma holomorphic_neg : Holomorphic (fun z => -c z) w.
Proof.
  exists (-c (1 +i 0)); intros eps Heps.
  exists 1; split; [lra |].
  intros h Hpos Hh_lt.
  assert (H_nz_sq : Cnorm_sq h <> 0) by (apply nonzero_if_norm_positive; exact Hpos).
  replace ((-c (w +c h) -c (-c w)) /c h -c (-c (1 +i 0))) with C0.
  - rewrite Cnorm_0; exact Heps.
  - assert (H_numer : -c (w +c h) -c (-c w) = -c h).
    { destruct w as [xw yw], h as [xh yh]; unfold Cadd, Csub; simpl; f_equal; ring. }
    rewrite H_numer.
    unfold Cdiv, Cinv.
    destruct h as [x y]; simpl.
    unfold Cnorm_sq, Rsqr; simpl.
    assert (Hnorm : x * x + y * y <> 0).
    { intro Hz; apply H_nz_sq; unfold Cnorm_sq; simpl; exact Hz. }
    apply complex_eq_re_im; simpl; field; assumption.
Qed.

(* 常数函数全纯 *)
Local Lemma holomorphic_const (c : Complex) : Holomorphic (fun _ => c) w.
Proof.
  exists C0; intros eps Heps.
  exists 1; split; [lra |].
  intros h Hpos Hh_lt.
  assert (H_nz_sq : Cnorm_sq h <> 0) by (apply nonzero_if_norm_positive; exact Hpos).
  replace ((c -c c) /c h -c C0) with C0.
  - rewrite Cnorm_0; exact Heps.
  - rewrite (Csub_self c).
    replace (C0 /c h) with C0.
    + rewrite (Csub_self C0); reflexivity.
    + symmetry; apply (Cdiv_0_l h H_nz_sq).
Qed.

(* 右分配律 *)
Lemma Cmul_add_distr_r (a b c : Complex) : (a +c b) *c c = a *c c +c b *c c.
Proof.
  destruct a as [a1 a2], b as [b1 b2], c as [c1 c2].
  apply complex_eq_re_im; simpl; ring.
Qed.

(* 除法对加法分配 *)
Lemma Cdiv_add_distr (a b h : Complex) (H : Cnorm_sq h <> 0) :
  Cdiv (a +c b) h H = Cdiv a h H +c Cdiv b h H.
Proof. unfold Cdiv; rewrite Cmul_add_distr_r; reflexivity. Qed.

(* 除法对减法分配 *)
Lemma Cdiv_sub_distr (a b h : Complex) (H : Cnorm_sq h <> 0) :
  Cdiv (a -c b) h H = Cdiv a h H -c Cdiv b h H.
Proof. unfold Cdiv; rewrite Cmul_sub_distr_r; reflexivity. Qed.

(* 除法证明的无关性 [构造性轨道 S1] 改用 Cinv_irrel，免 ProofIrrelevance *)
Lemma Cdiv_irrel (a h : Complex) (H1 H2 : Cnorm_sq h <> 0) : Cdiv a h H1 = Cdiv a h H2.
Proof.
  unfold Cdiv; apply f_equal; apply Cinv_irrel.
Qed.

(* 右减分配律 *)
Lemma Cmul_sub_distr_r (a b c : Complex) : (a -c b) *c c = a *c c -c b *c c.
Proof.
  destruct a as [a1 a2], b as [b1 b2], c as [c1 c2].
  apply complex_eq_re_im; simpl; ring.
Qed.

(* 线性组合等式 *)
Lemma Cexpr_eq (A B C D inv Lf Lg : Complex) :
  (A +c B -c (C +c D)) *c inv -c (Lf +c Lg) = ((A -c C) *c inv -c Lf) +c ((B -c D) *c inv -c Lg).
Proof.
  destruct A as [A1 A2], B as [B1 B2], C as [C1 C2], D as [D1 D2],
           inv as [inv1 inv2], Lf as [Lf1 Lf2], Lg as [Lg1 Lg2];
  apply complex_eq_re_im; simpl; ring.
Qed.

(* 除法证明的无关性（范数） *)
Lemma Cdiv_irrel_norm (A h : Complex) (H1 H2 : Cnorm_sq h <> 0) (L : Complex) :
  Cnorm (Cdiv A h H1 -c L) = Cnorm (Cdiv A h H2 -c L).
Proof.
  rewrite (Cdiv_irrel A h H1 H2); reflexivity.
Qed.

(* 除法证明的无关性（保持严格不等式） *)
Lemma Cdiv_irrel_norm_lt (A h : Complex) (H1 H2 : Cnorm_sq h <> 0) (L : Complex) (eps : R) :
  Cnorm (Cdiv A h H1 -c L) < eps -> Cnorm (Cdiv A h H2 -c L) < eps.
Proof. rewrite (Cdiv_irrel_norm A h H1 H2 L); trivial. Qed.

(* 函数和的全纯性 *)
Lemma holomorphic_plus : Holomorphic (fun z => f z +c g z) w.
Proof.
  destruct Hf as [Lf Hk].
  destruct Hg as [Lg Hm].
  exists (Lf +c Lg); intros eps Heps.
  assert (eps2_pos : eps / 2 > 0) by lra.
  destruct (Hk (eps / 2) eps2_pos) as [delta_f [Hdelta_f_pos Hf_est]].
  destruct (Hm (eps / 2) eps2_pos) as [delta_g [Hdelta_g_pos Hg_est]].
  set (delta := Rmin delta_f delta_g).
  assert (Hdelta_pos : 0 < delta) by (apply Rmin_pos; assumption).
  exists delta; split; [exact Hdelta_pos |].
  intros h Hpos Hh_lt_delta.
  assert (Hh_lt_f : Cnorm h < delta_f) by (eapply Rlt_le_trans; [exact Hh_lt_delta | apply Rmin_l]).
  assert (Hh_lt_g : Cnorm h < delta_g) by (eapply Rlt_le_trans; [exact Hh_lt_delta | apply Rmin_r]).
  assert (Hh_neq0 : h <> C0) by (intro H; rewrite H in Hpos; rewrite Cnorm_0 in Hpos; lra).
  assert (H_nz_sq : Cnorm_sq h <> 0) by (apply nonzero_if_norm_positive; exact Hpos).
  specialize (Hf_est h Hpos Hh_lt_f).
  specialize (Hg_est h Hpos Hh_lt_g).
  apply (Cdiv_irrel_norm_lt (f (w +c h) -c f w) h _ H_nz_sq Lf (eps/2)) in Hf_est.
  apply (Cdiv_irrel_norm_lt (g (w +c h) -c g w) h _ H_nz_sq Lg (eps/2)) in Hg_est.
  assert (Hsum : Cdiv (f (w +c h) +c g (w +c h) -c (f w +c g w)) h H_nz_sq -c (Lf +c Lg)
                 = (Cdiv (f (w +c h) -c f w) h H_nz_sq -c Lf) +c (Cdiv (g (w +c h) -c g w) h H_nz_sq -c Lg)).
  { rewrite Cdiv_sub_distr; rewrite !Cdiv_add_distr; apply complex_eq_re_im; simpl; ring. }
  rewrite (Cdiv_irrel (f (w +c h) +c g (w +c h) -c (f w +c g w)) h _ H_nz_sq).
  rewrite Hsum.
  apply (Rle_lt_trans _ (Cnorm (Cdiv (f (w +c h) -c f w) h H_nz_sq -c Lf) + Cnorm (Cdiv (g (w +c h) -c g w) h H_nz_sq -c Lg)) _).
  - apply Cnorm_triangle.
  - lra.
Qed.

(* 局部相等保持全纯 *)
Lemma holomorphic_ext_loc :
  (exists eps : R, eps > 0 /\ forall z, Cnorm (z -c w) < eps -> f z = g z) ->
  Holomorphic f w -> Holomorphic g w.
Proof.
  intros [eps [Heps Heq]] [Lf Hk].
  exists Lf; intros eps' Heps'.
  destruct (Hk eps' Heps') as [delta [Hdelta Hf_est]].
  set (delta' := Rmin delta eps).
  assert (Hdelta'_pos : 0 < delta') by (apply Rmin_pos; assumption).
  exists delta'; split; [exact Hdelta'_pos |].
  intros h Hpos Hh_lt_delta'.
  assert (Hh_lt_delta : Cnorm h < delta) by (eapply Rlt_le_trans; [exact Hh_lt_delta' | apply Rmin_l]).
  assert (Hh_lt_eps : Cnorm h < eps) by (eapply Rlt_le_trans; [exact Hh_lt_delta' | apply Rmin_r]).
  assert (Hz_in_neigh : Cnorm ((w +c h) -c w) < eps).
  { (* (w + h) - w = h *)
    assert (H_eq : (w +c h) -c w = h).
    { apply complex_eq_re_im; simpl; ring. }
    rewrite H_eq; exact Hh_lt_eps. }
  assert (Hz0_in_neigh : Cnorm (w -c w) < eps).
  { rewrite Csub_self, Cnorm_0; exact Heps. }
  pose proof (Heq (w +c h) Hz_in_neigh) as Heq_wh.
  pose proof (Heq w Hz0_in_neigh) as Heq_w.
  rewrite <- Heq_wh, <- Heq_w.
  apply Hf_est; auto.
Qed.

End HolomorphicCombinators.

(* 取负函数的全局全纯性 *)
Lemma holomorphic_neg_global (w : Complex) : Holomorphic (fun z => -c z) w.
Proof.
  exists (-c (1 +i 0)); intros eps Heps.
  exists 1; split; [lra |].
  intros h Hpos Hh_lt.
  assert (H_nz_sq : Cnorm_sq h <> 0) by (apply nonzero_if_norm_positive; exact Hpos).
  replace ((-c (w +c h) -c (-c w)) /c h -c (-c (1 +i 0))) with C0.
  - rewrite Cnorm_0; exact Heps.
  - assert (H_numer : -c (w +c h) -c (-c w) = -c h).
    { destruct w as [xw yw], h as [xh yh]; unfold Cadd, Csub; simpl; f_equal; ring. }
    rewrite H_numer.
    unfold Cdiv, Cinv.
    destruct h as [x y]; simpl.
    unfold Cnorm_sq, Rsqr; simpl.
    assert (Hnorm : x * x + y * y <> 0).
    { intro Hz; apply H_nz_sq; unfold Cnorm_sq; simpl; exact Hz. }
    apply complex_eq_re_im; simpl; field; assumption.
Qed.

(* 常数函数的全局全纯性 *)
Lemma holomorphic_const_global (w : Complex) (c : Complex) : Holomorphic (fun _ => c) w.
Proof.
  exists C0; intros eps Heps.
  exists 1; split; [lra |].
  intros h Hpos Hh_lt.
  assert (H_nz_sq : Cnorm_sq h <> 0) by (apply nonzero_if_norm_positive; exact Hpos).
  replace ((c -c c) /c h -c C0) with C0.
  - rewrite Cnorm_0; exact Heps.
  - rewrite (Csub_self c).
    replace (C0 /c h) with C0.
    + rewrite (Csub_self C0); reflexivity.
    + symmetry; apply (Cdiv_0_l h H_nz_sq).
Qed.

(* 全局复数乘法交换律 *)
Lemma Cmul_comm_global (a b : Complex) : a *c b = b *c a.
Proof.
  destruct a as [x1 y1], b as [x2 y2].
  unfold Cmul; simpl; f_equal; ring.
Qed.

(* 全局复数相等引理 *)
Lemma complex_eq_re_im_global (z w : Complex) : re z = re w -> im z = im w -> z = w.
Proof.
  destruct z as [x1 y1], w as [x2 y2]; simpl; intros Hre Him; subst; reflexivity.
Qed.

(* 全局复数乘法结合律 *)
Lemma Cmul_assoc_global (a b c : Complex) : (a *c b) *c c = a *c (b *c c).
Proof.
  apply complex_eq_re_im_global; simpl; ring.
Qed.

(* 全局右单位元 *)
Lemma Cmul_1_r_global (a : Complex) : a *c (1 +i 0) = a.
Proof.
  apply complex_eq_re_im_global; simpl; ring.
Qed.

(* 全局左单位元 *)
Lemma Cmul_1_l_global (a : Complex) : (1 +i 0) *c a = a.
Proof.
  apply complex_eq_re_im_global; simpl; ring.
Qed.

(* 全局逆元右乘 *)
Lemma Cinv_r_global (z : Complex) (H : Cnorm_sq z <> 0) : z *c Cinv z H = (1 +i 0).
Proof.
  destruct z as [x y]; unfold Cinv; simpl.
  unfold Cnorm_sq, Rsqr in *; simpl in H.
  apply complex_eq_re_im_global; simpl; field; assumption.
Qed.

(* 全局右消去律 *)
Lemma Cdiv_mul_cancel_r_global (a h : Complex) (H : Cnorm_sq h <> 0) : (a *c h) *c Cinv h H = a.
Proof.
  rewrite Cmul_assoc_global; rewrite Cinv_r_global; apply Cmul_1_r_global.
Qed.

(* 全局左消去律 *)
Lemma Cdiv_mul_cancel_l_global (a h : Complex) (H : Cnorm_sq h <> 0) : Cdiv a h H *c h = a.
Proof.
  unfold Cdiv.
  rewrite Cmul_assoc_global.
  rewrite (Cmul_comm_global (Cinv h H) h).
  rewrite Cinv_r_global.
  apply Cmul_1_r_global.
Qed.

(* 范数乘法性质 *)
Lemma Cnorm_mult_global (a b : Complex) : Cnorm (a *c b) = Cnorm a * Cnorm b.
Proof.
  destruct a as [x1 y1], b as [x2 y2].
  unfold Cnorm, Cnorm_sq, Cmul; simpl.
  unfold Rsqr.
  assert (H1 : 0 <= x1*x1 + y1*y1) by (apply Rplus_le_le_0_compat; apply Rle_0_sqr).
  assert (H2 : 0 <= x2*x2 + y2*y2) by (apply Rplus_le_le_0_compat; apply Rle_0_sqr).
  replace ((x1*x2 - y1*y2)*(x1*x2 - y1*y2) + (x1*y2 + y1*x2)*(x1*y2 + y1*x2))
    with ((x1*x1 + y1*y1)*(x2*x2 + y2*y2)) by ring.
  rewrite sqrt_mult; auto.
Qed.

(* 减法等于零等价于相等 *)
Lemma Csub_eq_0_iff (a b : Complex) : a -c b = C0 <-> a = b.
Proof.
  split; intros H.
  - apply complex_eq_re_im_global.
    + pose proof (f_equal re H) as Hre. simpl in Hre; lra.
    + pose proof (f_equal im H) as Him. simpl in Him; lra.
  - subst; apply Csub_self.
Qed.

(* 零减复数等于负元 *)
Lemma Csub_0_l (z : Complex) : C0 -c z = -c z.
Proof.
  apply complex_eq_re_im_global; simpl; ring.
Qed.

(* 全局加法交换律 *)
Lemma Cadd_comm_global : forall a b : Complex, a +c b = b +c a.
Proof.
  intros a b; apply complex_eq_re_im; simpl; ring.
Qed.

(* 全局加法结合律 *)
Lemma Cadd_assoc_global : forall a b c : Complex, a +c b +c c = a +c (b +c c).
Proof.
  intros a b c; apply complex_eq_re_im; simpl; ring.
Qed.

(* 负元加自身等于零 *)
Lemma Cadd_opp_diag : forall a : Complex, -c a +c a = C0.
Proof.
  intros a; apply complex_eq_re_im; simpl; ring.
Qed.

(* 零左加元不变 *)
Lemma Cadd_0_l : forall a : Complex, C0 +c a = a.
Proof.
  intros a; apply complex_eq_re_im; simpl; ring.
Qed.

(* 复数左逆元引理 *)
Lemma Cinv_l_global : forall (z : Complex) (H : Cnorm_sq z <> 0), Cinv z H *c z = (1 +i 0).
Proof.
  intros z H. rewrite (Cmul_comm_global (Cinv z H) z). apply Cinv_r_global.
Qed.

(* 局部辅助引理：X - Y + (Y - Z) = X - Z *)
Lemma sub_add_sub_simp : forall X Y Z : Complex,
  X -c Y +c (Y -c Z) = X -c Z.
Proof.
  intros; apply complex_eq_re_im; simpl; ring.
Qed.

(* 局部辅助引理：一次完成目标的重组和化简 *)
Local Lemma sub_add_sub_eq2 : forall a b c d : Complex,
  (a -c b) +c (c -c d) = a *c (1 +i 0) +c (-c b +c c) -c d.
Proof.
  intros; apply complex_eq_re_im; simpl; ring.
Qed.

(* 局部辅助引理：X - Y + (Y - Z) = X - Z *)
Local Lemma sub_add_sub_simp' : forall X Y Z : Complex,
  X -c Y +c (Y -c Z) = X -c Z.
Proof.
  intros; apply complex_eq_re_im; simpl; ring.
Qed.

(* 局部辅助引理：整理 (a - b) + (c - d) = a + (-b + c) - d *)
Local Lemma sub_add_sub_eq : forall a b c d : Complex,
  (a -c b) +c (c -c d) = a +c ((-c b) +c c) -c d.
Proof.
  intros; apply complex_eq_re_im; simpl; ring.
Qed.

(* 减法转加法的引理（本地使用，无需全局） *)
Local Lemma Csub_eq_add_opp : forall a b : Complex, a -c b = a +c (-c b).
Proof.
  intros a b; apply complex_eq_re_im; simpl; ring.
Qed.

(* 左消去律 *)
Lemma Cdiv_mul_cancel_l (a h : Complex) (H : Cnorm_sq h <> 0) : Cdiv a h H *c h = a.
Proof.
  unfold Cdiv.
  rewrite Cmul_assoc_global.
  rewrite (Cmul_comm_global (Cinv h H) h).
  rewrite Cinv_r_global.
  apply Cmul_1_r_global.
Qed.

(* 全局左分配律引理 *)
Lemma Cmul_sub_distr_l : forall a b c : Complex, a *c (b -c c) = a *c b -c a *c c.
Proof.
  intros a b c.
  rewrite (Cmul_comm_global a (b -c c)).
  rewrite (Cmul_sub_distr_r b c a).
  rewrite (Cmul_comm_global b a).
  rewrite (Cmul_comm_global c a).
  reflexivity.
Qed.

(* 核心代数恒等式（展开为 Cinv 形式） *)
Lemma holomorphic_comp_aux : forall (Fk Lf Lg k inv_k inv_h : Complex),
  inv_k *c k = (1 +i 0) ->
  Fk *c inv_h -c Lf *c Lg = (Fk *c inv_k -c Lf) *c (k *c inv_h) +c Lf *c (k *c inv_h -c Lg).
Proof.
  intros Fk Lf Lg k inv_k inv_h Hin.
  rewrite (Cmul_sub_distr_l Lf (k *c inv_h) Lg).
  rewrite (Cmul_sub_distr_r (Fk *c inv_k) Lf (k *c inv_h)).
  rewrite (sub_add_sub_simp ((Fk *c inv_k) *c (k *c inv_h)) (Lf *c (k *c inv_h)) (Lf *c Lg)).
  rewrite (Cmul_assoc_global Fk inv_k (k *c inv_h)).
  rewrite <- (Cmul_assoc_global inv_k k inv_h).
  rewrite Hin.
  rewrite (Cmul_comm_global (1 +i 0) inv_h).
  rewrite Cmul_1_r_global.
  reflexivity.
Qed.

(* 将 holomorphic_comp_aux 包装为 Cdiv 形式，显式提供除法证明项 *)
Lemma holomorphic_comp_aux_div : forall (Fk Lf Lg h0 k0 : Complex) (Hh0 : Cnorm_sq h0 <> 0) (Hk0 : Cnorm_sq k0 <> 0),
  Cinv k0 Hk0 *c k0 = (1 +i 0) ->
  Cdiv Fk h0 Hh0 -c Lf *c Lg = (Cdiv Fk k0 Hk0 -c Lf) *c (Cdiv k0 h0 Hh0) +c Lf *c (Cdiv k0 h0 Hh0 -c Lg).
Proof.
  intros Fk Lf Lg h0 k0 Hh0 Hk0 Hin.
  unfold Cdiv.
  apply holomorphic_comp_aux with (inv_h := Cinv h0 Hh0) (inv_k := Cinv k0 Hk0).
  exact Hin.
Qed.

(* 定理：复合函数全纯性-构造性 *)
Theorem holomorphic_comp (f g : Complex -> Complex) (w : Complex) :
  Holomorphic f (g w) -> Holomorphic g w -> Holomorphic (fun z => f (g z)) w.
Proof.
  intros [Lf Hf] [Lg Hg].
  exists (Lf *c Lg).
  intros eps Heps.
  set (A := Cnorm Lf + 1).
  set (B := Cnorm Lg + 1).
  assert (HA_pos : 0 <= A) by (unfold A; pose proof (Cnorm_ge_0 Lf); lra).
  assert (HB_pos : 0 <= B) by (unfold B; pose proof (Cnorm_ge_0 Lg); lra).
  assert (Hsum_pos : 0 < A + B) by (unfold A, B; pose proof (Cnorm_ge_0 Lf); pose proof (Cnorm_ge_0 Lg); lra).
  set (eps1 := Rmin (eps / (2 * (A + B))) 1).
  assert (Heps1_pos : eps1 > 0).
  { unfold eps1; apply Rmin_pos; [apply Rdiv_lt_0_compat; [exact Heps | lra] | lra]. }
  assert (Heps1_bound : eps1 * (A + B) <= eps / 2).
  { unfold eps1; apply Rle_trans with ((eps / (2*(A+B))) * (A+B)).
    - apply Rmult_le_compat_r; [nra | apply Rmin_l].
    - field_simplify; lra. }
  assert (Heps1_le_1 : eps1 <= 1) by (unfold eps1; apply Rmin_r).
  destruct (Hg eps1 Heps1_pos) as [delta_g [Hdelta_g Hg_est]].
  destruct (Hf eps1 Heps1_pos) as [delta_f [Hdelta_f Hf_est]].
  set (delta := Rmin delta_g (delta_f / (A + B))).
  assert (Hdelta_pos : 0 < delta).
  { apply Rmin_pos; [exact Hdelta_g | apply Rdiv_lt_0_compat; [exact Hdelta_f | lra]]. }
  exists delta; split; [exact Hdelta_pos |].
  intros h Hpos Hh_lt.
  assert (h_neq0 : h <> C0) by (intro H; rewrite H in Hpos; rewrite Cnorm_0 in Hpos; lra).
  assert (h_nz_sq : Cnorm_sq h <> 0) by (apply nonzero_if_norm_positive; exact Hpos).
  set (k := g (w +c h) -c g w).
  assert (Hh_lt_delta_g : Cnorm h < delta_g) by (eapply Rlt_le_trans; [exact Hh_lt | apply Rmin_l]).
  pose proof (Hg_est h Hpos Hh_lt_delta_g) as Hk_div.
  (* ===== 替换点：使用 Rlt_dec 判定 k 是否为 0 ===== *)
  destruct (Rlt_dec 0 (Cnorm_sq k)) as [Hk_pos | Hk_nonpos].
  - (* k ≠ 0 *)
    assert (Hk_neq0 : k <> C0) by exact (Cnorm_sq_pos_nonzero k Hk_pos).
    assert (Hk_nz_sq : Cnorm_sq k <> 0) by (apply nonzero_if_norm_positive; apply Cnorm_pos; exact Hk_neq0).
    assert (Hk_div' : Cnorm (Cdiv k h h_nz_sq -c Lg) < eps1).
    {
      apply (Cdiv_irrel_norm_lt k h (nonzero_if_norm_positive h Hpos) h_nz_sq Lg eps1).
      exact Hk_div.
    }
    assert (HCdiv_norm : Cnorm (Cdiv k h h_nz_sq) <= B).
    {
      replace (Cdiv k h h_nz_sq) with (Lg +c (Cdiv k h h_nz_sq -c Lg)).
      - apply Rle_trans with (Cnorm Lg + Cnorm (Cdiv k h h_nz_sq -c Lg)).
        + apply Cnorm_triangle.
        + apply Rle_trans with (Cnorm Lg + eps1).
          * apply Rplus_le_compat_l; apply Rlt_le; exact Hk_div'.
          * unfold B; nra.
      - apply complex_eq_re_im; simpl; ring.
    }
    assert (Hh_lt_delta_f_div : Cnorm h < delta_f / (A + B)).
    { eapply Rlt_le_trans; [exact Hh_lt | apply Rmin_r]. }
    assert (Hk_norm_lt : Cnorm k < delta_f).
    {
      assert (Hk_eq : k = Cdiv k h h_nz_sq *c h).
      { symmetry; exact (Cdiv_mul_cancel_l_global k h h_nz_sq). }
      rewrite Hk_eq; rewrite Cnorm_mult_global.
      apply Rlt_le_trans with ((A + B) * Cnorm h).
      - apply Rmult_lt_compat_r.
        + exact Hpos.
        + apply Rle_lt_trans with (r2 := B).
          * exact HCdiv_norm.
          * unfold A, B; pose proof (Cnorm_ge_0 Lf); lra.
      - assert (Htemp : Cnorm h <= delta_f / (A + B)).
        { apply Rlt_le; exact Hh_lt_delta_f_div. }
        apply (Rle_trans _ ((A + B) * (delta_f / (A + B))) _).
        + apply Rmult_le_compat_l; [nra | exact Htemp].
        + replace ((A + B) * (delta_f / (A + B))) with delta_f.
          * apply Rle_refl.
          * field; apply Rgt_not_eq; exact Hsum_pos.
    }
    assert (Hk_pos_norm : 0 < Cnorm k) by (apply Cnorm_pos; exact Hk_neq0).
    pose proof (Hf_est k Hk_pos_norm Hk_norm_lt) as Hphi_raw.
    apply (Cdiv_irrel_norm_lt (f (g w +c k) -c f (g w)) k
            (nonzero_if_norm_positive k Hk_pos_norm) Hk_nz_sq Lf eps1) in Hphi_raw.
    set (phi := Cdiv (f (g w +c k) -c f (g w)) k Hk_nz_sq -c Lf).
    assert (HP : Cnorm phi < eps1) by (unfold phi; exact Hphi_raw).
    set (Q := Cnorm (Cdiv k h h_nz_sq)).
    set (R := Cnorm (Cdiv k h h_nz_sq -c Lg)).
    assert (HQ : Q <= B) by (unfold Q; exact HCdiv_norm).
    assert (HR : R < eps1) by (unfold R; exact Hk_div').
    assert (Hgk : g (w +c h) = g w +c k).
    { subst k; apply complex_eq_re_im; simpl; ring. }
    rewrite Hgk.

    assert (Hinv : Cinv k Hk_nz_sq *c k = (1 +i 0)).
    { apply Cinv_l_global. }
    pose proof (holomorphic_comp_aux_div
      (f (g w +c k) -c f (g w)) Lf Lg h k h_nz_sq Hk_nz_sq Hinv) as Hmain.
    apply (Cdiv_irrel_norm_lt (f (g w +c k) -c f (g w)) h h_nz_sq _ (Lf *c Lg) eps).
    rewrite Hmain.
    apply Rle_lt_trans with (r2 := Cnorm (phi *c Cdiv k h h_nz_sq) + Cnorm (Lf *c (Cdiv k h h_nz_sq -c Lg))).
    - apply Cnorm_triangle.
    - rewrite !Cnorm_mult_global.
      unfold Q, R.
      assert (H_bound : Cnorm phi * Cnorm (Cdiv k h h_nz_sq) + Cnorm Lf * Cnorm (Cdiv k h h_nz_sq -c Lg) < eps).
      {
        apply Rle_lt_trans with (eps1 * B + Cnorm Lf * eps1).
        - apply Rplus_le_compat.
          + apply Rmult_le_compat; [apply Cnorm_ge_0 | apply Cnorm_ge_0 | apply Rlt_le; exact HP | exact HCdiv_norm].
          + apply Rmult_le_compat_l; [apply Cnorm_ge_0 | apply Rlt_le; exact HR].
        - replace (eps1 * B + Cnorm Lf * eps1) with (eps1 * (B + Cnorm Lf)) by ring.
          replace (B + Cnorm Lf) with (A + B - 1) by (unfold A, B; lra).
          assert (Hle : A + B - 1 <= A + B) by lra.
          apply Rle_lt_trans with (eps1 * (A + B)).
          + apply Rmult_le_compat_l; [lra | exact Hle].
          + nra.
      }
      exact H_bound.
  - (* k = 0 *)
    assert (Hk0 : k = C0).
    {
      apply Rnot_lt_le in Hk_nonpos.                  (* Hk_nonpos : Cnorm_sq k <= 0 *)
      assert (Hk_sq0 : Cnorm_sq k = 0) by
        (apply Rle_antisym; [exact Hk_nonpos | apply Cnorm_sq_ge0]).
      apply Cnorm_sq_eq_0; exact Hk_sq0.
    }
    assert (Hg_eq : g (w +c h) = g w).
    { apply (proj1 (Csub_eq_0_iff (g (w +c h)) (g w)) Hk0). }
    rewrite Hg_eq.
    rewrite Csub_self.
    unfold Cdiv; rewrite Cmul_0_l.
    replace (C0 -c Lf *c Lg) with (-c (Lf *c Lg)).
    { rewrite Cnorm_neg, Cnorm_mult_global.
      assert (Hk_div_simp : Cnorm Lg < eps1).
      {
        rewrite Hg_eq in Hk_div.
        rewrite (Csub_self (g w)) in Hk_div.
        unfold Cdiv in Hk_div; rewrite Cmul_0_l in Hk_div.
        replace (C0 -c Lg) with (-c Lg) in Hk_div.
        - rewrite Cnorm_neg in Hk_div; exact Hk_div.
        - apply complex_eq_re_im; simpl; ring.
      }
      assert (H_bound : Cnorm Lf * eps1 <= eps).
      {
        apply Rle_trans with (eps1 * A).
        - unfold A; nra.
        - apply Rle_trans with (eps1 * (A + B)).
          + apply Rmult_le_compat_l; [lra | nra].
          + nra.
      }
      destruct (Rlt_dec 0 (Cnorm Lf)) as [HposLf | HnotposLf].
      - assert (H_prod_lt : Cnorm Lf * Cnorm Lg < Cnorm Lf * eps1).
        { apply Rmult_lt_compat_l; [exact HposLf | exact Hk_div_simp]. }
        eapply Rlt_le_trans; [exact H_prod_lt | exact H_bound].
      - assert (HzLf : Cnorm Lf = 0).
        { apply Rle_antisym; [apply Rnot_lt_le; exact HnotposLf | apply Cnorm_ge_0]. }
        rewrite HzLf, Rmult_0_l; exact Heps.
    }
    { apply complex_eq_re_im; simpl; ring. }
Qed.

(* 定理：左上半平面主支对数全纯 *)
Theorem holomorphic_Clog_total_left_upper :
  forall w (Hre : re w < 0) (Him : im w > 0),
  Holomorphic Clog_total w.
Proof.
  intros wk Hre Him.
  set (h := fun v => Clog_total (-c v) +c CI *c C_of_R PI).
  assert (Hh : Holomorphic h wk).
  { unfold h.
    apply (holomorphic_plus (fun v => Clog_total (-c v)) (fun _ => CI *c C_of_R PI) wk).
    - apply (holomorphic_comp Clog_total (fun v => -c v) wk).
      + apply (holomorphic_Clog_total (-c wk)); simpl; lra.   (* 修复处 *)
      + apply holomorphic_neg_global with (w := wk).
    - apply holomorphic_const_global with (c := CI *c C_of_R PI) (w := wk).
  }
  destruct (Clog_total_left_upper_shift_locally wk Hre Him) as [eps [Heps Heq]].
  assert (Hloc : locally wk (fun v => Clog_total v = h v)).
  { exists eps; split; [exact Heps | intros v Hv; rewrite Heq; auto; unfold h; reflexivity]. }
  apply (holomorphic_ext_loc h Clog_total wk).
  - destruct Hloc as [eps' [Heps' Heq']].
    exists eps'; split; [exact Heps' | intros v Hv; apply Heq' in Hv; symmetry; exact Hv].
  - exact Hh.
Qed.

(* 复数减法等于加负元 *)
Lemma Csub_eq_Cadd_opp (a b : Complex) : a -c b = a +c (-c b).
Proof.
  apply complex_eq_re_im; simpl; ring.
Qed.

(* 定理：左下半平面主支对数全纯 *)
Theorem holomorphic_Clog_total_left_lower :
  forall w (Hre : re w < 0) (Him : im w < 0),
  Holomorphic Clog_total w.
Proof.
  intros wk Hre Him.
  set (h := fun v => Clog_total (-c v) -c CI *c C_of_R PI).
  assert (Hh_aux : Holomorphic (fun v => Clog_total (-c v) +c -c (CI *c C_of_R PI)) wk).
  {
    apply (holomorphic_plus (fun v => Clog_total (-c v)) (fun _ => -c (CI *c C_of_R PI)) wk).
    - apply holomorphic_comp with (f := Clog_total) (g := fun v => -c v) (w := wk).
      + apply holomorphic_Clog_total_right; simpl; lra.
      + apply holomorphic_neg_global with (w := wk).
    - apply holomorphic_const_global with (c := -c (CI *c C_of_R PI)) (w := wk).
  }
  assert (Hh : Holomorphic h wk).
  { unfold h.
    set (F := fun v => Clog_total (-c v) -c CI *c C_of_R PI).
    set (G := fun v => Clog_total (-c v) +c -c (CI *c C_of_R PI)).
    assert (Heq_global : forall v, F v = G v).
    { intros v; unfold F, G; apply Csub_eq_Cadd_opp. }
    apply (holomorphic_ext_loc G F wk).
    - exists 1; split; [lra | intros z _; symmetry; apply Heq_global].
    - exact Hh_aux. }
  destruct (Clog_total_left_lower_shift_locally wk Hre Him) as [eps [Heps Heq]].
  assert (Hloc : locally wk (fun v => Clog_total v = h v)).
  { exists eps; split; [exact Heps | intros v Hv; rewrite Heq; auto; unfold h; reflexivity]. }
  apply (holomorphic_ext_loc h Clog_total wk).
  - destruct Hloc as [eps' [Heps' Heq']].
    exists eps'; split; [exact Heps' | intros v Hv; apply Heq' in Hv; symmetry; exact Hv].
  - exact Hh.
Qed.

(* 定理：左半平面主支对数全纯（虚部非零） *)
Theorem holomorphic_Clog_total_left :
  forall w (Hre : re w < 0) (Him : im w <> 0),
  Holomorphic Clog_total w.
Proof.
  intros w Hre Him.
  destruct (Rlt_le_dec 0 (im w)) as [Hpos|Hneg].
  - apply holomorphic_Clog_total_left_upper; auto; lra.
  - assert (Him_neg : im w < 0) by lra.
    apply holomorphic_Clog_total_left_lower; auto.
Qed.

(* 主支对数的定义域：右半平面 或 左半平面且虚部非零 *)
Definition Clog_domain (w : Complex) : Prop :=
  re w > 0 \/ (re w < 0 /\ im w <> 0).

(* 定理：主支对数在定义域内全纯 *)
Theorem holomorphic_Clog_total_on_domain : forall w,
  Clog_domain w -> Holomorphic Clog_total w.
Proof.
  intros w [Hpos | [Hneg Hnim]].
  - apply holomorphic_Clog_total_right; exact Hpos.
  - apply holomorphic_Clog_total_left; auto.
Qed.

End ClogBoundModule.

Export ClogBoundModule.
