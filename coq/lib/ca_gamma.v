(* 拆分自 Riemann_Hypothesis_Proof_Framework.v（复分析证明库 v6.0）*)
(* 库: ca_gamma  原文行区间: 3233-16482  机械拆分，未改动内容 *)

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

Require Import ca_base ca_algebra ca_primes ca_complex_analysis ca_fourier ca_zeta_scaffold ca_trig.

Require Import Stdlib.Logic.IndefiniteDescription.

Module GammaIntegralConverges.

Require Import Coquelicot.Coquelicot.
Require Import Stdlib.Reals.Reals.
Require Import Stdlib.Reals.RIneq.
Require Import Stdlib.micromega.Lra.
Require Import Coquelicot.Coquelicot.
Require Import Coquelicot.Rbar.  (* 扩充实数轴核心模块，包含mkbar构造函数 *)
Require Import Coquelicot.RInt.
Require Import Stdlib.Reals.Reals.
Import Rbar.
Import Coquelicot. (* 辅助类，保证Proper性 *)
Import ComplexNumbers.    (* 复数系统 *)
Import TrigonometricLemmas. (* 三角恒等式模块 *)
(* Coq标准库（复数、实数、不等式证明） *)
Import Reals Complex Psatz.
(* Coq标准库（复数、实数基础） *)
Import Reals Complex.

Open Scope R_scope.
Open Scope complex_scope.

(* 扩充实数投影函数（提取实数值） *)
Definition Rbar_proj (t : Rbar) : R :=
  match t with
  | Rbar.Finite x => x
  | Rbar.p_infty => 0
  | Rbar.m_infty => 0
  end.

(* 扩充实数大于0的谓词 *)
Definition Rbar_is_pos (t : Rbar) : Prop :=
  match t with
  | Rbar.Finite x => 0 < x
  | Rbar.p_infty => True
  | Rbar.m_infty => False
  end.

Section GammaIntegralConverges.

Require Import Stdlib.Reals.RIneq.
Require Import Coquelicot.Coquelicot.
Require Import Coquelicot.Rbar.
Require Import Coquelicot.RInt.
Require Import Stdlib.Reals.Reals Coq.micromega.Lra.
Require Import Coquelicot.Rbar Coquelicot.RInt Coquelicot.Coquelicot.
Require Import Coquelicot.RInt_gen.
Require Import Stdlib.Reals.Reals Coq.Reals.RIneq Coq.micromega.Lra Coq.micromega.Psatz.
Require Import Coquelicot.Coquelicot Coquelicot.Rbar Coquelicot.RInt.
Import Rbar RInt.  (* 显式导入作用域 *)
Import PrimeEmbedding.
Import ComplexNumbers. (* 原框架中的复数模块 *)
Import Rbar.

Open Scope R_scope.
Open Scope complex_scope.

(* 复数s及其实部大于1的上下文 *)
Context (s : Complex) (Hre : 1 < ComplexNumbers.re s).
(* 实部σ的定义 *)
Let σ := ComplexNumbers.re s.
(* 指数a = σ - 1，由Hre知a>0 *)
Let a := σ - 1.  (* 由 Hre 可知 a > 0 *)
(* 被积函数实部f的定义 *)
Let f (t : R) : R :=
  match Rlt_dec 0 t with
  | left H => gamma_integrand_real s t H
  | right _ => 0
  end.

(* f在(0,1)上的简化形式 *)
Lemma f_simpl_01 :
  forall t (Ht : 0 < t < 1),
    f t = exp (-t) * Rpower t a.
Proof.
  intros t [Ht_gt0 Ht_lt1].
  unfold f.
  destruct (Rlt_dec 0 t) as [Hpos | Hnotpos].
  - rewrite (proof_irrelevance _ Hpos Ht_gt0).
    unfold gamma_integrand_real; simpl.
    unfold real_pow, Rpower.
    reflexivity.
  - exfalso; apply Hnotpos; exact Ht_gt0.
Qed.

(* f在(0,1)上的非负性 *)
Lemma f_nonneg_01 :
  forall t (Ht : 0 < t < 1),
    0 <= f t.
Proof.
  intros t Ht.
  rewrite f_simpl_01 by auto.
  apply Rmult_le_pos.
  - apply Rlt_le, exp_pos.
  - apply Rlt_le.
    unfold Rpower.
    destruct (Req_EM_T t 0) as [Heq | Hneq].
    + exfalso; lra.
    + apply exp_pos.
Qed.

(* f在(0,1)上被Rpower t a控制 *)
Lemma f_bound_01 :
  forall t (Ht : 0 < t < 1),
    f t <= Rpower t a.
Proof.
  intros t Ht.
  rewrite f_simpl_01 by auto.
  assert (exp (-t) <= 1).
  {
    apply Rlt_le.
    assert (H_neg_t_lt_0 : -t < 0) by lra.
    apply exp_increasing in H_neg_t_lt_0.
    rewrite exp_0 in H_neg_t_lt_0.
    exact H_neg_t_lt_0.
  }
  assert (Rpower_nonneg : 0 <= Rpower t a).
  {
    apply Rlt_le.
    unfold Rpower.
    destruct (Req_EM_T t 0) as [Heq | Hneq].
    - exfalso; lra.
    - apply exp_pos.
  }
  apply Rle_trans with (1 * Rpower t a).
  - apply Rmult_le_compat_r; [exact Rpower_nonneg | exact H].
  - rewrite Rmult_1_l; apply Rle_refl.
Qed.

(* Rpower t a在t>0处的连续性 *)
Lemma Rpower_continuous_gt0 :
  forall t, 0 < t -> continuity_pt (fun t => Rpower t a) t.
Proof.
  intros t Ht.
  unfold Rpower.
  apply continuity_pt_comp with (f1 := fun x => a * ln x) (f2 := exp).
  - apply continuity_pt_scal.
    clear -Ht.
    unfold continuity_pt, continue_in, limit1_in, limit_in.
    intros eps Heps.
    set (u0 := ln t).
    assert (Hexp_incr : forall x y, x < y -> exp x < exp y) by apply exp_increasing.
    set (t1 := exp (u0 - eps)).
    set (t2 := exp (u0 + eps)).
    assert (Ht1_lt_t : t1 < t).
    {
      unfold t1.
      rewrite <- (exp_ln t Ht).
      apply Hexp_incr.
      apply Rminus_lt.
      replace (u0 - eps - ln t) with (-eps).
      - assert (Hneg : -eps < -0).
        { apply Ropp_lt_gt_contravar; exact Heps. }
        rewrite Ropp_0 in Hneg.
        exact Hneg.
      - unfold u0; ring.
    }
    assert (Ht2_gt_t : t < t2).
    {
      unfold t2.
      rewrite <- (exp_ln t Ht).
      apply Hexp_incr.
      apply Rminus_lt.
      replace (ln t - (u0 + eps)) with (-eps) by (unfold u0; ring).
      apply Ropp_lt_gt_contravar in Heps.
      rewrite Ropp_0 in Heps.
      exact Heps.
    }
    set (delta := Rmin (Rmin (t - t1) (t2 - t)) (t/2)).
    assert (Hdelta_pos : 0 < delta).
    {
      apply Rmin_pos; [apply Rmin_pos | lra].
      - apply Rgt_minus; lra.
      - apply Rgt_minus; lra.
    }
    exists delta; split; [exact Hdelta_pos | ].
    intros x [Hx_def Hx_dist].
    assert (Hx_gt_0 : 0 < x).
    {
      apply Rnot_le_lt; intros Hle.
      assert (Hx_le_0 : x <= 0) by exact Hle.
      assert (Hx_le_t : x <= t) by lra.
      assert (Hx_minus_t_le_0 : x - t <= 0) by lra.
      unfold dist, R_met, Rdist in Hx_dist.
      rewrite (Rabs_left1 (x - t) Hx_minus_t_le_0) in Hx_dist.
      replace (- (x - t)) with (t - x) in Hx_dist by ring.
      assert (Hdelta_le_half : delta <= t / 2).
      { unfold delta; apply Rmin_r. }
      assert (Ht_minus_x_lt_half : t - x < t / 2).
      { apply Rlt_le_trans with delta; [exact Hx_dist | exact Hdelta_le_half]. }
      assert (Hx_gt_half : x > t / 2) by lra.
      exfalso; lra.
    }
    assert (Hdelta_le_t_minus_t1 : delta <= t - t1).
    {
      unfold delta.
      eapply Rle_trans.
      - apply Rmin_l.
      - apply Rmin_l.
    }
    assert (Hdelta_le_t2_minus_t : delta <= t2 - t).
    {
      unfold delta.
      eapply Rle_trans.
      - apply Rmin_l.
      - apply Rmin_r.
    }
    assert (Hx_gt_t1 : t1 < x).
    {
      apply Rnot_le_lt; intros Hx_le_t1.
      assert (Hx_le_t1' : x <= t1) by exact Hx_le_t1.
      assert (Hx_minus_t_neg : x - t < 0) by lra.
      unfold dist, R_met, Rdist in Hx_dist.
      rewrite (Rabs_left1 (x - t) (Rlt_le _ _ Hx_minus_t_neg)) in Hx_dist.
      replace (- (x - t)) with (t - x) in Hx_dist by ring.
      assert (t_minus_x_ge_t_minus_t1 : t - x >= t - t1) by lra.
      assert (t - x < t - t1) by (eapply Rlt_le_trans; [eassumption | apply Hdelta_le_t_minus_t1]).
      lra.
    }
    assert (Hx_lt_t2 : x < t2).
    {
      apply Rnot_le_lt; intros Hx_ge_t2.
      assert (Hx_minus_t_pos : x - t > 0) by lra.
      unfold dist, R_met, Rdist in Hx_dist.
      rewrite (Rabs_right (x - t)) in Hx_dist.
      2: { apply Rle_ge. left. exact Hx_minus_t_pos. }
      assert (x_minus_t_ge_t2_minus_t : x - t >= t2 - t) by lra.
      assert (x - t < t2 - t) by (eapply Rlt_le_trans; [eassumption | apply Hdelta_le_t2_minus_t]).
      lra.
    }
    unfold t1, t2 in *.
    assert (Hln_gt : u0 - eps < ln x).
    {
      rewrite <- (ln_exp (u0 - eps)).
      apply ln_increasing.
      - apply exp_pos.
      - exact Hx_gt_t1.
    }
    assert (Hln_lt : ln x < u0 + eps).
    {
      rewrite <- (ln_exp (u0 + eps)).
      apply ln_increasing.
      - exact Hx_gt_0.
      - exact Hx_lt_t2.
    }
    unfold dist, R_met, Rdist.
    apply Rabs_def1; lra.
  - apply derivable_continuous_pt.
    apply derivable_pt_exp.
Qed.

End GammaIntegralConverges.

Section G_integrable.

Require Import Coquelicot.Coquelicot.
Require Import Stdlib.Reals.Reals.
Require Import Stdlib.Reals.Ranalysis1.
Open Scope R_scope.

(* 函数 G *)
Variable G : R -> R.
(* G 在 [0,1] 上连续的假设 *)
Hypothesis Hcont_G : forall x, 0 <= x <= 1 -> continuity_pt G x.

(* G 在 [0,1] 上可积 *)
Lemma G_integrable : ex_RInt G 0 1.
Proof.
  apply ex_RInt_continuous with (f := G) (a := 0) (b := 1).
  intros z Hz.
  destruct Hz as [H1 H2].
  assert (Hmin : Rmin 0 1 = 0). { apply Rmin_left; lra. }
  assert (Hmax : Rmax 0 1 = 1). { apply Rmax_right; lra. }
  assert (H_interval : 0 <= z <= 1).
  { split; [rewrite Hmin in H1 | rewrite Hmax in H2]; assumption. }
  assert (H_std_cont : continuity_pt G z) by (apply Hcont_G; exact H_interval).
  unfold continuous.
  intros Q HQ.
  destruct HQ as [eps_posreal H].
  destruct eps_posreal as [eps Heps_pos].
  unfold continuity_pt, continue_in, limit1_in, limit_in in H_std_cont.
  specialize (H_std_cont eps Heps_pos) as [alp [Halp_pos Hdelta]].
  exists ({| pos := alp; cond_pos := Halp_pos |} : posreal).
  intros y Hy.
  simpl in Hy |- *.
  assert (H_main : Rdist (G y) (G z) < eps).
  {
    destruct (Req_dec y z) as [Hy_eq | Hy_neq].
    - subst y.
      assert (H_zero : Rdist (G z) (G z) = 0).
      {
        simpl.
        (try reflexivity); (try apply Rdist_refl); (try apply metric_refl); (try ring).
      }
      rewrite H_zero.
      exact Heps_pos.
    - eapply Hdelta.
      split.
      + split.
        * simpl. (try trivial); (try tauto); (try constructor); (try exact I).
        * intro H_contra. apply Hy_neq. symmetry. exact H_contra.
      + simpl in Hy. exact Hy.
  }
  eapply H.
  simpl.
  exact H_main.
Qed.

(* 任意实函数基于 ε-δ 连续性的 Coquelicot 连续性 *)
Lemma continuity_eps_delta (h : R -> R) (x : R) :
  (forall eps : R, eps > 0 -> exists delta : R, delta > 0 /\ forall y : R, Rabs (y - x) < delta -> Rabs (h y - h x) < eps) ->
  continuous h x.
Proof.
  intros H_eps_delta.
  unfold continuous.
  intros Q HQ.
  destruct HQ as [eps_posreal H].
  destruct eps_posreal as [eps Heps_pos].

  specialize (H_eps_delta eps Heps_pos) as [delta [Hdelta_pos Hdelta]].

  exists ({| pos := delta; cond_pos := Hdelta_pos |} : posreal).
  intros y Hy.
  simpl in Hy |- *.

  assert (H_main : Rabs (h y - h x) < eps).
  {
    destruct (Req_dec y x) as [Hy_eq | Hy_neq].
    - subst y.
      assert (H_zero : Rabs (h x - h x) = 0).
      { simpl. rewrite Rminus_diag. rewrite Rabs_R0. reflexivity. }
      rewrite H_zero. exact Heps_pos.
    - eapply Hdelta.
      simpl in Hy. exact Hy.
  }

  eapply H.
  simpl. exact H_main.
Qed.

(* 当 a > 0 时，幂函数 t^a 在 0+ 处的极限为 0 *)
Lemma Rpower_lim0 : forall a : R, a > 0 -> limit1_in (fun t => Rpower t a) (fun t => 0 < t) 0 0.
Proof.
  intros a Ha.
  unfold limit1_in, limit_in, continue_in.
  intros eps Heps.

  (* Simplify Rpower and Rdist *)
  unfold Rpower, Rdist.
  simpl.

  (* Manually prove Rabs (exp x) = exp x (since exp x > 0) *)
  assert (exp_pos : forall x : R, 0 < exp x) by apply exp_pos.
  assert (abs_pos_exp : forall x : R, Rabs (exp x) = exp x).
  {
    intros x.
    assert (H : 0 < exp x) by apply exp_pos.
    unfold Rabs.
    assert (not_exp_neg : ~ (exp x < 0)).
    { intros Hneg; apply (Rlt_irrefl 0); apply (Rlt_trans 0 (exp x) 0); auto. }
    destruct (Rcase_abs (exp x)) as [Hcase | Hcase].
    - exfalso; apply not_exp_neg; exact Hcase.
    - reflexivity.
  }

  (* Choose delta = exp (ln eps / a) *)
  exists (exp (ln eps / a)).
  split.
  - (* delta > 0 *)
    apply exp_pos.
  - (* Main proof: for t with 0 < t < delta, |Rpower t a| < eps *)
    intros t Ht.
    destruct Ht as [Ht_pos Ht_lt].
    unfold Rdist in *.
    rewrite (Rminus_0_r (exp (a * ln t))) in *.
    rewrite (Rminus_0_r t) in Ht_lt.
    rewrite (abs_pos_exp (a * ln t)).

    (* Now goal: exp (a * ln t) < eps *)
    rewrite Rabs_pos_eq in Ht_lt; [| left; exact Ht_pos].
    (* Ht_lt: t < exp (ln eps / a) *)

    assert (Hexp_pos : 0 < exp (ln eps / a)) by apply exp_pos.
    assert (Hln_lt : ln t < ln (exp (ln eps / a))).
    { apply ln_increasing with (x := t) (y := exp (ln eps / a));
        auto using Ht_pos, Hexp_pos, Ht_lt. }

    rewrite ln_exp in Hln_lt.  (* ln t < ln eps / a *)

    assert (Ha_ln : a * ln t < ln eps).
    { replace (ln eps) with (a * (ln eps / a)) by (field; apply Rgt_not_eq; exact Ha).
      apply Rmult_lt_compat_l; auto. }

    apply exp_increasing in Ha_ln.
    assert (H_exp_ln : exp (ln eps) = eps) by (apply exp_ln; exact Heps).
    rewrite H_exp_ln in Ha_ln.
    exact Ha_ln.
Qed.

(* 右极限定义 *)
Definition right_limit (f : R -> R) (x l : R) : Prop :=
  limit1_in f (fun t => x < t) x l.

(* 幂函数在 0 处的右极限为 0 *)
Lemma Rpower_right_lim0 : forall a : R, a > 0 -> right_limit (fun t => Rpower t a) 0 0.
Proof.
  intros a Ha; unfold right_limit; apply Rpower_lim0; exact Ha.
Qed.

End G_integrable.

(* 幂函数导数 *)
Lemma is_derive_power (a : R) (x : R) (Ha : a > 0) (Hx : x > 0) :
  is_derive (fun t => Rpower t (a+1) / (a+1)) x (Rpower x a).
Proof.
  assert (Hapos : a+1 > 0) by lra.
  assert (Haneq : a+1 <> 0) by lra.
  assert (H_Rpower_pos : forall t : R, t > 0 -> Rpower t (a+1) = exp ((a+1) * ln t)).
  { intros t Ht; unfold Rpower; reflexivity. }
  assert (H_Rpower_x : Rpower x a = exp (a * ln x)).
  { unfold Rpower; reflexivity. }

  assert (Hder_f : is_derive (fun t => (a+1) * ln t) x ((a+1)/x)).
  { apply is_derive_scal with (k := a+1); apply is_derive_ln; assumption. }
  assert (Hder_g : is_derive exp ((a+1)*ln x) (exp ((a+1)*ln x)))
    by apply is_derive_exp.
  assert (Hcomp : is_derive (fun t => exp ((a+1)*ln t)) x
                            ((a+1)/x * exp ((a+1)*ln x))).
  { apply (is_derive_comp exp (fun t => (a+1)*ln t) x
                           (exp ((a+1)*ln x)) ((a+1)/x) Hder_g Hder_f). }
  assert (Hscaled : is_derive (fun t => (1/(a+1)) * exp ((a+1)*ln t)) x
                              ((1/(a+1)) * ((a+1)/x * exp ((a+1)*ln x)))).
  { apply is_derive_scal with (k := 1/(a+1)); exact Hcomp. }
  assert (Hsimp : (1/(a+1)) * ((a+1)/x * exp ((a+1)*ln x)) = exp (a * ln x)).
  {
    replace ((a+1)*ln x) with (a*ln x + ln x) by (field; lra).
    rewrite exp_plus, exp_ln by assumption.
    field; lra.
  }
  rewrite Hsimp in Hscaled.

  assert (Hdelta_pos : 0 < x / 2) by lra.
  assert (Hfunc_eq_loc : forall t : R, Rabs (t - x) < x / 2 -> 
    (Rpower t (a + 1) / (a + 1)) = (1 / (a + 1) * exp ((a + 1) * ln t))).
  {
    intros t Ht_abs.
    assert (Ht_pos : t > 0).
    {
      apply Rabs_lt_between in Ht_abs.
      lra.
    }
    rewrite (H_Rpower_pos t Ht_pos).
    unfold Rdiv.
    ring.
  }

  assert (Hex : exists delta : R, 0 < delta /\ forall t, Rabs (t - x) < delta ->
               Rpower t (a+1)/(a+1) = 1/(a+1) * exp((a+1)*ln t)).
  { exists (x/2); split; [exact Hdelta_pos | exact Hfunc_eq_loc]. }

  assert (Heq_loc : locally x (fun t => Rpower t (a+1)/(a+1) = 1/(a+1) * exp ((a+1)*ln t))).
  { destruct Hex as [d [Hd Hcond]].
    exists (mkposreal d Hd).
    intros y Hy.
    apply Hcond; exact Hy. }

  assert (Heq_loc_sym : locally x (fun t => 1/(a+1) * exp ((a+1)*ln t) = Rpower t (a+1)/(a+1))).
  { destruct Heq_loc as [eps Heq].
    exists eps.
    intros y Hy.
    symmetry; apply Heq; exact Hy. }

  assert (Htemp : is_derive (fun t => Rpower t (a+1)/(a+1)) x (exp (a * ln x))).
  { apply (is_derive_ext_loc (fun t => 1/(a+1) * exp ((a+1)*ln t))
                             (fun t => Rpower t (a+1)/(a+1))
                             x (exp (a * ln x))
                             Heq_loc_sym Hscaled). }

  rewrite <- H_Rpower_x in Htemp.
  exact Htemp.
Qed.

(* 自然对数在正点可导 *)
Lemma derivable_pt_ln_manual : forall x, x > 0 -> derivable_pt ln x.
Proof.
  intros x Hx.
  unfold derivable_pt.
  exists (/ x).
  apply (derivable_pt_lim_ln x Hx).
Qed.

(* 指数函数可导性 *)
Lemma derivable_pt_exp_manual : forall x, derivable_pt exp x.
Proof.
  intros x.
  exists (exp x).
  apply derivable_pt_lim_exp.
Qed.

(* 幂函数的可导性 *)
Lemma derivable_pt_power (a x : R) (Ha : a > 0) (Hx : x > 0) :
  derivable_pt (fun t => Rpower t (a+1) / (a+1)) x.
Proof.
  assert (Ha1 : a+1 > 0) by lra.
  replace (fun t => Rpower t (a+1) / (a+1))
     with (fun t => (/(a+1)) * Rpower t (a+1))
    by (extensionality t; unfold Rdiv; rewrite Rmult_comm; reflexivity).
  apply derivable_pt_scal.
  unfold Rpower.
  apply derivable_pt_comp with (f1 := fun t => (a+1) * ln t) (f2 := exp).
  - apply derivable_pt_scal.
    apply derivable_pt_ln_manual; assumption.
  - apply derivable_pt_exp_manual.
Qed.

(* 幂函数的导数极限 *)
Lemma derivable_pt_lim_power (a x : R) (Ha : a > 0) (Hx : x > 0) :
  derivable_pt_lim (fun t => Rpower t (a+1) / (a+1)) x (Rpower x a).
Proof.
  assert (Hapos : a+1 > 0) by lra.
  assert (Hxpos : x > 0) by assumption.
  unfold Rpower.
  set (f := fun t => exp ((a+1) * ln t)).
  replace (fun t => f t / (a+1)) with (fun t => (/(a+1)) * f t) by
    (extensionality t; unfold Rdiv; ring).

  assert (Hder_ln : derivable_pt_lim (fun t => (a+1) * ln t) x ((a+1) / x)).
  { apply derivable_pt_lim_scal; apply derivable_pt_lim_ln; assumption. }

  assert (Hder_exp : derivable_pt_lim exp ((a+1)*ln x) (exp ((a+1)*ln x)))
    by apply derivable_pt_lim_exp.

  pose proof (derivable_pt_lim_comp (fun t => (a+1) * ln t) exp x ((a+1)/x) (exp ((a+1)*ln x)) Hder_ln Hder_exp) as Hcomp.

  assert (Hcomp_f : derivable_pt_lim f x (exp ((a+1)*ln x) * ((a+1)/x))).
  {
    apply (derivable_pt_lim_ext (comp exp (fun t => (a+1) * ln t)) f x (exp ((a+1)*ln x) * ((a+1)/x))).
    - intro t. unfold comp, f. reflexivity.
    - exact Hcomp.
  }

  assert (Hscaled : derivable_pt_lim (fun t => /(a+1) * f t) x (/(a+1) * (exp ((a+1)*ln x) * ((a+1)/x)))).
  { apply derivable_pt_lim_scal; exact Hcomp_f. }

  assert (Heq : /(a+1) * (exp ((a+1)*ln x) * ((a+1)/x)) = exp (a * ln x)).
  {
    unfold Rdiv.
    replace (/(a+1) * (exp ((a+1)*ln x) * ((a+1) * /x)))
      with ((/(a+1) * (a+1)) * (exp ((a+1)*ln x) * /x)) by ring.
    rewrite Rinv_l; [|apply Rgt_not_eq, Hapos].
    rewrite Rmult_1_l.
    assert (Hinv : exp (- ln x) = / x).
    { rewrite exp_Ropp, exp_ln; auto. }
    rewrite <- Hinv.
    rewrite <- exp_plus.
    replace ((a+1)*ln x + (- ln x)) with (a * ln x) by ring.
    reflexivity.
  }
  rewrite Heq in Hscaled.

  apply (derivable_pt_lim_ext (fun t => /(a+1) * f t) (fun t => f t / (a+1)) x (exp (a * ln x))).
  - intro t. unfold f, Rdiv. rewrite Rmult_comm. reflexivity.
  - exact Hscaled.
Qed.

(* 幂函数的导数求值 *)
Lemma derive_pt_power (a x : R) (Ha : a > 0) (Hx : x > 0) :
  let d := derivable_pt_power a x Ha Hx in
  derive_pt (fun t => Rpower t (a+1) / (a+1)) x d = Rpower x a.
Proof.
  intros d.
  apply derive_pt_eq_0.
  apply derivable_pt_lim_power; assumption.
Qed.

(* 正实数幂函数的连续性 *)
Lemma continuity_pt_Rpower_pos (a x : R) (Ha : a > 0) (Hx : x > 0) :
  continuity_pt (fun t => Rpower t a) x.
Proof.
  unfold Rpower.
  assert (Hcont_ln : continuity_pt ln x).
  { apply derivable_continuous_pt. apply derivable_pt_ln_manual; assumption. }
  assert (Hcont_scaled : continuity_pt (fun t => a * ln t) x).
  { apply continuity_pt_scal; assumption. }
  apply continuity_pt_comp with (f1 := fun t => a * ln t) (f2 := exp).
  - exact Hcont_scaled.
  - apply derivable_continuous_pt.
    apply derivable_pt_exp_manual.
Qed.

(* 除以常数的幂函数的连续性 *)
Lemma continuity_pt_div_power (a x : R) (Ha : a+1 > 0) (Hx : x > 0) :
  continuity_pt (fun t => Rpower t (a+1) / (a+1)) x.
Proof.
  replace (fun t => Rpower t (a+1) / (a+1)) with (fun t => (/(a+1)) * Rpower t (a+1)).
  - apply continuity_pt_scal.
    apply continuity_pt_Rpower_pos; assumption.
  - extensionality t; unfold Rdiv; rewrite Rmult_comm; reflexivity.
Qed.

(* 幂函数的定积分公式 *)
Lemma RInt_power (a u v : R) (Ha : a > 0) (Hu : 0 < u) (Hv : v <= 1) (Huv : u <= v) :
  RInt (fun t => Rpower t a) u v = (Rpower v (a+1) - Rpower u (a+1)) / (a+1).
Proof.
  assert (Ha1_pos : a + 1 > 0) by lra.
  assert (Ha1_neq0 : a + 1 <> 0) by lra.
  assert (Hmin : Rmin u v = u) by (rewrite Rmin_left; lra).
  assert (Hmax : Rmax u v = v) by (rewrite Rmax_right; lra).

  set (f := fun t => Rpower t a).
  set (g := fun t => Rpower t (a + 1) / (a + 1)).

  assert (Hcont_f : forall t, Rmin u v <= t <= Rmax u v -> continuous f t).
  {
    intros t Ht.
    rewrite Hmin, Hmax in Ht.
    apply continuity_eps_delta.
    intros eps Heps.
    assert (Hcont_pt : continuity_pt f t).
    { unfold f; apply continuity_pt_Rpower_pos; [exact Ha |].
      destruct Ht as [Ht_ge_u Ht_le_v].
      apply Rlt_le_trans with u; [exact Hu | exact Ht_ge_u]. }
    destruct (Hcont_pt eps Heps) as [delta [Hdelta_pos Hdelta]].
    exists delta; split; [exact Hdelta_pos |].
    intros y Hy.
    destruct (Req_dec y t) as [Heq|Hneq]; [subst y; rewrite Rminus_diag, Rabs_R0; exact Heps |].
    apply Hdelta; split; [split; [exact I | intro Hcontra; apply Hneq; symmetry; exact Hcontra] | exact Hy].
  }

  assert (Hder_g : forall t, Rmin u v <= t <= Rmax u v -> is_derive g t (f t)).
  {
    intros t Ht.
    rewrite Hmin, Hmax in Ht.
    destruct Ht as [Ht_ge_u Ht_le_v].
    assert (Ht_pos : 0 < t) by (apply Rlt_le_trans with u; [exact Hu | exact Ht_ge_u]).
    apply is_derive_power; [exact Ha | exact Ht_pos].
  }

  assert (Hex : ex_RInt f u v).
  { apply ex_RInt_continuous with (f := f) (a := u) (b := v). exact Hcont_f. }

  assert (H_int : is_RInt f u v (g v - g u)).
  { apply (is_RInt_derive g f u v Hder_g Hcont_f). }

  pose proof (RInt_correct f u v Hex) as H_RInt.

  pose proof (is_RInt_unique f u v (g v - g u) H_int) as Heq.
  rewrite Heq.
  unfold g.
  rewrite <- (Rdiv_minus_distr (Rpower v (a+1)) (Rpower u (a+1)) (a+1)).
  reflexivity.
Qed.

(* 正实数幂函数的正值性 *)
Lemma Rpower_pos : forall x a, 0 < x -> 0 < Rpower x a.
Proof.
  intros x a Hx. unfold Rpower. apply exp_pos.
Qed.

(* 幂函数的严格单调性 *)
Lemma Rpower_lt : forall x y a, 0 < x < y -> 0 < a -> Rpower x a < Rpower y a.
Proof.
  intros x y a [Hx Hxy] Ha.
  unfold Rpower. apply exp_increasing.
  apply Rmult_lt_compat_l; [exact Ha | apply ln_increasing; auto].
Qed.

(* 指数函数的单调性 *)
Lemma exp_le : forall x y, x <= y -> exp x <= exp y.
Proof.
  intros x y Hle.
  destruct Hle as [Hlt | Heq].
  - left; apply exp_increasing; auto.
  - right; rewrite Heq; auto.
Qed.

(* 幂函数严格单调的逆 *)
Lemma Rpower_lt_inv : forall x y a, 0 < x -> 0 < y -> 0 < a -> Rpower x a < Rpower y a -> x < y.
Proof.
  intros x y a Hx Hy Ha H.
  unfold Rpower in H.
  assert (H1 : a * ln x < a * ln y).
  {
    apply Rnot_le_lt.
    intros Hle.
    assert (exp (a * ln y) <= exp (a * ln x)).
    {
      destruct (Rle_lt_or_eq_dec _ _ Hle) as [Hlt | Heq].
      - apply Rlt_le. apply exp_increasing. exact Hlt.
      - rewrite Heq. apply Rle_refl.
    }
    apply Rle_not_lt in H0.
    contradiction.
  }
  apply Rmult_lt_reg_l in H1; try lra.
  apply exp_increasing in H1.
  rewrite exp_ln in H1; auto.
  rewrite exp_ln in H1; auto.
Qed.

(* 局部邻域与开球的等价性 *)
Lemma locally_iff_open_ball : forall (z : R) (Q : R -> Prop),
  locally z Q <-> exists (eps : R), eps > 0 /\ forall y : R, Rabs (y - z) < eps -> Q y.
Proof.
  intros z Q.
  split.
  - intros HQ.
    unfold locally in HQ.
    destruct HQ as [pr Hpr].
    exists (pos pr).
    split.
    + apply cond_pos.
    + intros y Hlt.
      apply Hpr.
      exact Hlt.
  - intros [eps [Hpos Hball]].
    unfold locally.
    exists (mkposreal eps Hpos).
    intros y Hball'.
    apply Hball.
    exact Hball'.
Qed.

(* 标准库连续性到Coquelicot连续性的简单转化 *)
Lemma continuity_pt_to_continuous_simple : forall (f : R -> R) (x : R),
  continuity_pt f x -> continuous f x.
Proof.
  intros f x Hcont.
  unfold continuity_pt, continue_in, limit1_in, limit_in in Hcont.
  simpl in Hcont.

  assert (H_eps_delta : forall eps : R, eps > 0 -> 
    exists delta : R, delta > 0 /\ forall y : R, Rabs (y - x) < delta -> Rabs (f y - f x) < eps).
  {
    intros eps Heps.
    specialize (Hcont eps Heps) as [alp [Halp_pos Hcond]].
    exists alp.
    split.
    - exact Halp_pos.
    - intros y Hy_abs.
      destruct (Req_dec y x) as [Hy_eq | Hy_neq].
      + subst y.
        rewrite Rminus_diag, Rabs_R0.
        exact Heps.
      + assert (H_Dx : D_x no_cond x y).
        {
          unfold D_x.
          split.
          * unfold no_cond.
            trivial.
          * intro H_contra.
            apply Hy_neq.
            symmetry.
            exact H_contra.
        }
        assert (H_main : (D_x no_cond x y) /\ Rdist y x < alp).
        {
          split.
          * exact H_Dx.
          * unfold Rdist.
            simpl.
            exact Hy_abs.
        }
        apply Hcond in H_main.
        unfold Rdist in H_main.
        simpl in H_main.
        exact H_main.
  }
  unfold continuous.
  intros Q HQ.
  destruct HQ as [eps_posreal H].
  destruct eps_posreal as [eps Heps_pos].
  specialize (H_eps_delta eps Heps_pos) as [delta [Hdelta_pos Hdelta]].
  exists (mkposreal delta Hdelta_pos).
  intros y Hy.
  simpl in Hy |- *.
  assert (Hres : Rabs (f y - f x) < eps) by apply Hdelta, Hy.
  eapply H.
  simpl.
  exact Hres.
Qed.

(* 标准库连续性到Coquelicot连续性的转化（滤子版本） *)
Lemma continuity_pt_to_continuous : forall (f : R -> R) (x : R),
  continuity_pt f x -> continuous f x.
Proof.
  intros f x Hcont.
  unfold continuous, filterlim, filtermap.
  intros P HP.
  destruct HP as [eps Heps].
  pose (eps_R := pos eps).
  pose (eps_pos := cond_pos eps).
  specialize (Hcont eps_R eps_pos) as Hdelta_exists.
  destruct Hdelta_exists as [delta [Hdelta_pos Hdelta]].
  assert (H_main : forall y : R, Rabs (y - x) < delta -> P (f y)).
  {
    intros y Hy_lt.
    destruct (Req_dec y x) as [Hy_eq | Hy_neq].
    - subst y.
      assert (Hball : ball (f x) eps (f x)) by apply ball_center.
      apply Heps in Hball.
      exact Hball.
    - assert (Hball : ball (f x) eps (f y)).
      {
        unfold ball. simpl.
        apply Hdelta; split; [split; [exact I | intro Hcontra; apply Hy_neq; symmetry; exact Hcontra] | exact Hy_lt].
      }
      apply Heps in Hball.
      exact Hball.
  }
  exists (mkposreal delta Hdelta_pos).
  intros y Hy.
  apply H_main.
  simpl in Hy; assumption.
Qed.

(* 右邻域局部性质的开球表示 *)
Lemma at_right_has_eps_simple : forall (x : R) (P : R -> Prop),
  locally x (fun x0 : R => x < x0 -> P x0) -> 
  exists eps : posreal, forall y, x < y < x + pos eps -> P y.
Proof.
  intros x P H.
  unfold locally in H.
  destruct H as [delta Hdelta].
  exists delta.
  intros y [Hy_gt_x Hy_lt_bound].
  assert (H_in_ball : ball x delta y).
  {
    assert (H4 : Rabs (y - x) < pos delta).
    {
      assert (H1 : 0 <= y - x) by lra.
      assert (H2 : Rabs (y - x) = y - x).
      { apply Rabs_pos_eq. exact H1. }
      rewrite H2.
      lra.
    }
    unfold ball, AbsRing_ball; simpl.
    change (Rabs (y - x) < pos delta).
    exact H4.
  }
  apply Hdelta.
  - exact H_in_ball.
  - exact Hy_gt_x.
Qed.

(* 右邻域存在性 *)
Lemma at_right_has_eps : forall (x : R_UniformSpace) (P : R -> Prop),
  locally x (fun x0 : R => x < x0 -> P x0) -> 
  exists eps : posreal, forall y, x < y < x + pos eps -> P y.
Proof.
  intros x P H.
  unfold locally in H.
  destruct H as [delta Hdelta].
  exists delta.
  intros y [Hy_gt_x Hy_lt_bound].

  assert (H_in_ball : ball x delta y).
  {
    unfold ball; simpl.
    assert (H4 : Rabs (y - x) < pos delta).
    {
      assert (H1 : (y - x) < pos delta) by lra.
      assert (H2 : 0 <= y - x) by lra.
      assert (H3 : Rabs (y - x) = y - x).
      {
        apply Rabs_pos_eq.
        exact H2.
      }
      rewrite H3.
      exact H1.
    }
    unfold AbsRing_ball; simpl.
    exact H4.
  }
  apply Hdelta.
  - exact H_in_ball.
  - exact Hy_gt_x.
Qed.

(* 幂函数在(0,1)上的广义可积性 *)
Lemma Rpower_integrable_01 : forall a : R, a > 0 ->
  ex_RInt_gen (fun t => Rpower t a) (at_right 0) (at_left 1).
Proof.
  intros a Ha.
  set (f := fun t : R => Rpower t a).
  set (F := fun t : R => Rpower t (a + 1) / (a + 1)).
  assert (Ha1 : a + 1 > 0) by lra.
  assert (Ha1_neq0 : a + 1 <> 0) by lra.

  assert (Hder_pow : forall t, t > 0 ->
          is_derive (fun t : R => Rpower t (a + 1)) t ((a + 1) * Rpower t a)).
  {
    intros t Ht.
    unfold Rpower.
    assert (Hinner : is_derive (fun u : R => (a + 1) * ln u) t ((a + 1) / t)).
    { apply is_derive_scal with (k := a + 1). apply is_derive_ln; exact Ht. }
    assert (Houter : is_derive exp ((a + 1) * ln t) (exp ((a + 1) * ln t))) by apply is_derive_exp.
    assert (Hcomp : is_derive (fun u : R => exp ((a + 1) * ln u)) t (((a + 1) / t) * exp ((a + 1) * ln t))).
    { apply (is_derive_comp exp (fun u : R => (a + 1) * ln u) t _ _ Houter Hinner). }
    assert (Heq : ((a + 1) / t) * exp ((a + 1) * ln t) = (a + 1) * exp (a * ln t)).
    {
      unfold Rdiv.
      replace (exp ((a + 1) * ln t)) with (exp (a * ln t + ln t)) by (f_equal; ring).
      rewrite exp_plus.
      assert (Htmp : / t * (exp (ln t) * exp (a * ln t)) = exp (a * ln t)).
      {
        rewrite <- Rmult_assoc, (exp_ln t Ht), Rinv_l; [| lra].
        rewrite Rmult_1_l; reflexivity.
      }
      rewrite Rmult_assoc, (Rmult_comm (exp (a * ln t)) (exp (ln t))), Htmp; ring.
    }
    rewrite <- Heq; exact Hcomp.
  }

  assert (Hder : forall t, t > 0 -> is_derive F t (f t)).
  {
    intros t Ht.
    unfold F, f.
    replace (Rpower t (a + 1) / (a + 1)) with (/ (a + 1) * Rpower t (a + 1)) by (field; lra).
    assert (Hpow := Hder_pow t Ht).
    apply is_derive_scal with (k := / (a + 1)) in Hpow.
    rewrite <- Rmult_assoc in Hpow.
    rewrite (Rinv_l (a + 1)) in Hpow; [| lra].
    rewrite Rmult_1_l in Hpow.
    apply (is_derive_ext (fun x => / (a + 1) * Rpower x (a + 1)) F t (Rpower t a)).
    - intros y; unfold Rdiv; rewrite Rmult_comm; reflexivity.
    - exact Hpow.
  }

  assert (Hcont_f : forall t, 0 < t < 1 -> continuous f t).
  {
    intros t [Ht_pos Ht_lt1].
    apply continuity_pt_to_continuous_simple.
    apply continuity_pt_Rpower_pos; lra.
  }

  assert (Hlim_F0 : filterlim F (at_right 0) (locally 0)).
  {
    intros P [eps Heps].
    set (eps' := (a + 1) * eps).
    assert (Heps' : eps' > 0) by (apply Rmult_gt_0_compat; [lra | apply cond_pos]).
    assert (Hlim_pow : limit1_in (fun t => Rpower t (a + 1)) (fun t => 0 < t) 0 0).
    { apply Rpower_lim0; lra. }
    unfold limit1_in, limit_in in Hlim_pow.
    specialize (Hlim_pow eps' Heps') as [delta [Hdelta_pos Hdelta]].
    exists (mkposreal delta Hdelta_pos).
    intros y Hy Hgt.
    simpl in Hy.
    assert (Hdelta_cond : 0 < y /\ dist R_met y 0 < delta) by (split; [exact Hgt | exact Hy]).
    specialize (Hdelta y Hdelta_cond).
    unfold dist in Hdelta; simpl in Hdelta.
    assert (Habs : Rabs (F y) < eps).
    {
      unfold F.
      rewrite Rabs_div; [| lra].
      rewrite Rabs_pos_eq; [| apply Rlt_le, Rpower_pos; lra].

      assert (Hpos_pow : 0 < Rpower y (a + 1)) by (apply Rpower_pos; lra).
      assert (Heq_abs : Rabs (Rpower y (a + 1) - 0) = Rpower y (a + 1)).
      { rewrite Rminus_0_r. apply Rabs_pos_eq. apply Rlt_le; exact Hpos_pow. }

      unfold Rdist in Hdelta.
      rewrite Heq_abs in Hdelta.
      assert (Hpow_lt : Rpower y (a + 1) < (a + 1) * eps) by exact Hdelta.

      rewrite Rabs_pos_eq; [| apply Rlt_le; exact Ha1].

      apply (Rmult_lt_compat_r (/ (a+1))) in Hpow_lt; [| apply Rinv_0_lt_compat; lra].

      assert (Heq_eps : (a + 1) * eps * / (a + 1) = eps).
      { field; lra. }
      rewrite Heq_eps in Hpow_lt.
      exact Hpow_lt.
    }
    apply Heps.
    change (Rabs (F y - 0) < eps).
    rewrite Rminus_0_r.
    exact Habs.
  }

  assert (Hder1 : is_derive F 1 (f 1)) by (apply Hder; lra).
  apply is_derive_Reals in Hder1 as Hder_pt_lim.
  assert (Hder_pt : derivable_pt F 1) by (exists (f 1); exact Hder_pt_lim).
  apply derivable_continuous_pt in Hder_pt.
  rename Hder_pt into Hcont_pt_F1.
  apply continuity_pt_to_continuous_simple in Hcont_pt_F1.
  assert (Hlim_F1 : filterlim F (at_left 1) (locally (F 1))).
  {
    intros P HP.
    destruct (Hcont_pt_F1 P HP) as [delta Hdelta].
    exists delta.
    intros y Hy_ball Hlt.
    apply Hdelta.
    exact Hy_ball.
  }

  assert (H_RInt_eq : forall u v, 0 < u /\ u < v /\ v < 1 -> RInt f u v = F v - F u).
  {
    intros u v [Hu [Huv Hv]].
    assert (Hcont_int : forall x, u <= x <= v -> continuous f x).
    { intros x [Hx1 Hx2]; apply Hcont_f; split.
      - apply Rlt_le_trans with u; [exact Hu | exact Hx1].
      - apply Rle_lt_trans with v; [exact Hx2 | exact Hv]. }
    assert (Hcont_int' : forall z, Rmin u v <= z <= Rmax u v -> continuous f z).
    { intros z Hz.
      rewrite Rmin_left in Hz; [| lra].
      rewrite Rmax_right in Hz; [| lra].
      apply Hcont_int; exact Hz. }
    assert (Hex : ex_RInt f u v).
    { apply ex_RInt_continuous with (f := f) (a := u) (b := v).
      exact Hcont_int'. }
    assert (Hder_int : forall x, u <= x <= v -> is_derive F x (f x)).
    { intros x [Hx1 Hx2]; apply Hder; apply Rlt_le_trans with u; [exact Hu | exact Hx1]. }
    assert (Hder_int' : forall x, Rmin u v <= x <= Rmax u v -> is_derive F x (f x)).
    { intros x Hx.
      rewrite Rmin_left, Rmax_right in Hx; [| lra | lra].
      apply Hder_int; exact Hx. }
    assert (HInt : is_RInt f u v (F v - F u)).
    { apply (is_RInt_derive F f u v Hder_int' Hcont_int'). }
    apply (is_RInt_unique f u v (F v - F u) HInt).
  }

  exists (F 1).
  intros P HP.
  destruct HP as [eps Hball].
  set (eps' := pos eps) in *.
  assert (Heps_pos : 0 < eps') by apply (cond_pos eps).
  assert (Heps2 : 0 < eps' / 2) by lra.

  destruct (Hlim_F0 (fun y => ball 0 (mkposreal (eps' / 2) Heps2) y)) as [delta1 Hdelta1].
  { exists (mkposreal (eps' / 2) Heps2). intros y Hy; exact Hy. }

  destruct (Hlim_F1 (fun y => ball (F 1) (mkposreal (eps' / 2) Heps2) y)) as [delta2 Hdelta2].
  { exists (mkposreal (eps' / 2) Heps2). intros y Hy; exact Hy. }

  assert (Hdelta1_abs : forall y, 0 < y < delta1 -> Rabs (F y) < eps' / 2).
  {
    intros y [Hpos Hlt].
    assert (Hball_y : ball 0 delta1 y).
    { unfold ball; simpl; unfold AbsRing_ball; rewrite Rminus_0_r; rewrite Rabs_pos_eq; [| lra]; exact Hlt. }
    specialize (Hdelta1 y Hball_y Hpos) as H.
    unfold ball in H; simpl in H; unfold AbsRing_ball in H; simpl in H.
    rewrite Rminus_0_r in H.
    exact H.
  }

  assert (Hdelta2_abs : forall y, 1 - delta2 < y < 1 -> Rabs (F y - F 1) < eps' / 2).
  {
    intros y [Hgt Hlt].
    assert (Hball_y : ball 1 delta2 y).
    {
      unfold ball; simpl; unfold AbsRing_ball.
      rewrite Rabs_minus_sym.
      rewrite Rabs_pos_eq.
      - lra.
      - lra.
    }
    specialize (Hdelta2 y Hball_y Hlt) as H.
    unfold ball in H; simpl in H; unfold AbsRing_ball in H; simpl in H.
    exact H.
  }

  set (d1 := Rmin delta1 (1/2)).
  set (d2 := Rmin delta2 (1/2)).
  assert (Hd1_pos : 0 < d1) by (apply Rmin_pos; [apply cond_pos | lra]).
  assert (Hd2_pos : 0 < d2) by (apply Rmin_pos; [apply cond_pos | lra]).
  assert (Hd1_le : d1 <= delta1) by apply Rmin_l.
  assert (Hd2_le : d2 <= delta2) by apply Rmin_l.
  assert (Hd1_lt_half : d1 <= 1/2) by apply Rmin_r.
  assert (Hd2_lt_half : d2 <= 1/2) by apply Rmin_r.

  pose (Q := fun u => 0 < u < d1).
  pose (R := fun v => 1 - d2 < v < 1).

  assert (HU : at_right 0 Q).
  {
    exists (mkposreal d1 Hd1_pos).
    intros x Hx Hpos.
    split; [exact Hpos |].
    unfold ball in Hx; simpl in Hx; unfold AbsRing_ball in Hx.
    rewrite Rminus_0_r in Hx.
    rewrite Rabs_pos_eq in Hx; [| left; exact Hpos].
    exact Hx.
  }

  assert (HV : at_left 1 R).
  {
    exists (mkposreal d2 Hd2_pos).
    intros y Hy Hlt.
    split.
    - unfold ball in Hy; simpl in Hy; unfold AbsRing_ball in Hy.
      rewrite Rabs_minus_sym, Rabs_pos_eq in Hy; [| lra].
      lra.
    - exact Hlt.
  }

  assert (HQR : filter_prod (at_right 0) (at_left 1) (fun ab => Q (fst ab) /\ R (snd ab))).
  { apply Filter_prod with (Q := Q) (R := R); [exact HU | exact HV | intros u v Hu Hv; split; auto]. }

  apply filter_imp with (2 := HQR).
  intros [u v] [HQu HRv]; simpl.
  assert (Hu_pos : 0 < u) by (exact (proj1 HQu)).
  assert (Hu_lt_d1 : u < d1) by (exact (proj2 HQu)).
  assert (Hv_gt_1md2 : 1 - d2 < v) by (exact (proj1 HRv)).
  assert (Hv_lt_1 : v < 1) by (exact (proj2 HRv)).

  assert (Hlt : u < v).
  {
    apply Rlt_trans with (1 - d2); [| exact Hv_gt_1md2].
    apply Rlt_le_trans with d1; [exact Hu_lt_d1 |].
    assert (Hd1_half : d1 <= 1/2) by apply Rmin_r.
    assert (Hd2_half : d2 <= 1/2) by apply Rmin_r.
    lra.
  }

  assert (Hex : ex_RInt f u v).
  {
    apply ex_RInt_continuous with (f := f) (a := u) (b := v).
    intros z Hz.
    assert (Hmin_eq : Rmin u v = u) by (apply Rmin_left; lra).
    assert (Hmax_eq : Rmax u v = v) by (apply Rmax_right; lra).
    rewrite Hmin_eq, Hmax_eq in Hz.
    apply Hcont_f; split.
    - apply Rlt_le_trans with u; [exact Hu_pos | exact (proj1 Hz)].
    - apply Rle_lt_trans with v; [exact (proj2 Hz) | exact Hv_lt_1].
  }

  exists (RInt f u v).
  split.
  - exact (RInt_correct f u v Hex).
  - apply Hball.
    unfold ball, AbsRing_ball.
    simpl.
    rewrite H_RInt_eq with (u:=u) (v:=v); [| split; [exact Hu_pos | split; [exact Hlt | exact Hv_lt_1]]].

    assert (Hu_lt_delta1 : u < delta1).
    {
      apply Rlt_le_trans with (r1 := u) (r2 := d1) (r3 := delta1).
      - exact Hu_lt_d1.
      - exact Hd1_le.
    }

    assert (H_Fu_bound : Rabs (F u) < eps' / 2).
    {
      apply Hdelta1_abs.
      split.
      - exact Hu_pos.
      - exact Hu_lt_delta1.
    }

    assert (H_eq : (F v - F u) - F 1 = (F v - F 1) + (- F u)).
    {
      ring.
    }

    assert (H_tri : Rabs ((F v - F 1) + (- F u)) <= Rabs (F v - F 1) + Rabs (- F u)).
    {
      apply Rabs_triang.
    }

    assert (H_ropp : Rabs (- F u) = Rabs (F u)).
    {
      apply Rabs_Ropp.
    }
    rewrite H_ropp in H_tri.

    assert (Hv_gt_1mdelta2 : 1 - delta2 < v).
    {
      assert (H1 : 1 - delta2 <= 1 - d2).
      { lra. }
      apply Rle_lt_trans with (r1 := 1 - delta2) (r2 := 1 - d2) (r3 := v).
      - exact H1.
      - exact Hv_gt_1md2.
    }

    assert (H_Fv_bound : Rabs (F v - F 1) < eps' / 2).
    {
      apply Hdelta2_abs.
      split.
      - exact Hv_gt_1mdelta2.
      - exact Hv_lt_1.
    }

    assert (H_sum : Rabs (F v - F 1) + Rabs (F u) < eps').
    {
      lra.
    }

    assert (H_main : Rabs ((F v - F 1) + (- F u)) < eps').
    {
      apply Rle_lt_trans with (r2 := Rabs (F v - F 1) + Rabs (F u)).
      - exact H_tri.
      - exact H_sum.
    }

    assert (H_final : Rabs ((F v - F u) - F 1) < eps').
    {
      assert (H9 : Rabs ((F v - F u) - F 1) = Rabs (F v - F 1 + - F u)).
      {
        f_equal.
        exact H_eq.
      }
      rewrite H9.
      exact H_main.
    }

    unfold AbsRing_ball, ball.
    simpl.
    exact H_final.
Qed.

(* 幂函数在(0,1]上以1为界 *)
Lemma Rpower_le_1 (x a : R) (Hx : 0 < x) (Ha : 0 < a) (Hx_le_1 : x <= 1) :
  Rpower x a <= 1.
Proof.
  apply Rle_trans with (Rpower 1 a).
  - (* 证明 Rpower x a <= Rpower 1 a *)
    assert (Hx_lt_1 : x < 1 \/ x = 1) by lra.
    destruct Hx_lt_1 as [Hx_lt | Hx_eq].
    + (* x < 1 *)
      assert (Hln_le : ln x <= ln 1).
      { apply (ln_le x 1 Hx Hx_le_1). }
      rewrite ln_1 in Hln_le.
      assert (Ha_nonneg : 0 <= a) by (apply Rlt_le; exact Ha).
      assert (Ha_ln_le : a * ln x <= 0).
      { rewrite <- (Rmult_0_r a). apply Rmult_le_compat_l; [exact Ha_nonneg | exact Hln_le]. }
      unfold Rpower.
      replace (a * ln 1) with 0 by (rewrite ln_1; ring).
      apply exp_le.
      exact Ha_ln_le.
    + (* x = 1 *)
      rewrite Hx_eq.
      apply Rle_refl.
  - (* 证明 Rpower 1 a <= 1 *)
    unfold Rpower; rewrite ln_1, Rmult_0_r, exp_0; apply Rle_refl.
Qed.

(* 左邻域区间构造 *)
Lemma at_left_interval : forall x d, d > 0 -> at_left x (fun y => x - d < y < x).
Proof.
  intros x d Hd.
  unfold at_left, within.
  exists (mkposreal d Hd).
  intros y Hy Hlt.
  split.
  - assert (Habs : Rabs (y - x) < d) by exact Hy.
    assert (Hneg : y - x < 0) by lra.
    rewrite (Rabs_left (y - x) Hneg) in Habs.
    lra.
  - exact Hlt.
Qed.

(* 点滤子单点集合 *)
Lemma at_point_singleton : forall x : R_UniformSpace, at_point x (fun y => y = x).
Proof.
  intros x.
  unfold at_point.
  apply eq_refl.
Qed.

(* 幂函数在正区间上不大于1 *)
Lemma Rpower_le_2 (x a : R) : 0 < x <= 1 -> 0 < a -> Rpower x a <= 1.
Proof.
  intros [Hx Hx1] Ha.
  apply Rle_trans with (Rpower 1 a).
  - apply Rle_Rpower_l; [apply Rlt_le; exact Ha | lra].
  - assert (H1 : Rpower 1 a = 1).
    { unfold Rpower. rewrite ln_1, Rmult_0_r, exp_0. reflexivity. }
    rewrite H1. apply Rle_refl.
Qed.

(* 正实数的幂为正 *)
Lemma Rpower_pos_1 (x a : R) : 0 < x -> 0 < Rpower x a.
Proof.
  intros Hx. unfold Rpower. apply exp_pos.
Qed.

(* 幂函数在左端点1处的广义可积性 *)
Lemma Rpower_integrable_left1 (a : R) (Ha : 0 < a) :
  ex_RInt_gen (fun t => Rpower t a) (at_left 1) (at_point 1).
Proof.
  exists 0.
  unfold is_RInt_gen, filterlim.
  intros P HP.
  destruct HP as [eps Heps]. 
  set (δ := Rmin eps (1/2)).
  assert (Hδ : 0 < δ) by (apply Rmin_pos; [apply cond_pos | lra]).
  assert (Hδ_le_eps : δ <= eps) by apply Rmin_l.
  assert (Hδ_lt_half : δ <= 1/2) by apply Rmin_r.

  assert (HA : at_left 1 (fun x => 1 - δ < x < 1)).
  { apply at_left_interval; exact Hδ. }
  assert (HB : at_point 1 (fun y => y = 1)) by apply at_point_singleton.

  apply Filter_prod with (Q := fun x => 1 - δ < x < 1) (R := fun y => y = 1).
  - exact HA.
  - exact HB.
  - intros x y Hx Hy.
    assert (Hx' : 1 - δ < x < 1) by exact Hx.
    subst y.
    assert (Hx_pos : 0 < x) by (apply Rlt_le_trans with (1-δ); lra).
    assert (Hx_lt_1 : x < 1) by lra.

    (* 证明实值函数在 [x,1] 上连续，从而黎曼可积 *)
    assert (Hcont_std : forall t, x <= t <= 1 -> continuity_pt (fun t => Rpower t a) t).
    { intros t Ht. apply continuity_pt_Rpower_pos; [exact Ha | lra]. }
    assert (Hriem : Riemann_integrable (fun t => Rpower t a) x 1).
    { apply RiemannInt_P6; [lra | exact Hcont_std]. }

    pose proof (ex_RInt_Reals_aux_1 (fun t => Rpower t a) x 1 Hriem) as His.
    set (r := RiemannInt Hriem).

    assert (Hle1 : forall t, x <= t <= 1 -> Rpower t a <= 1).
    { intros t Ht. apply Rpower_le_1; [apply Rlt_le_trans with x; [lra | apply Ht] | exact Ha | apply Ht]. }

    assert (Hex_f : ex_RInt (fun t => Rpower t a) x 1) by (exists r; exact His).
    assert (Hex_g : ex_RInt (fun _ => 1) x 1) by apply ex_RInt_const.

    assert (Hle : RInt (fun t => Rpower t a) x 1 <= RInt (fun _ => 1) x 1).
    {
      apply RInt_le; [lra | exact Hex_f | exact Hex_g | ].
      intros t Ht.
      apply Hle1.
      split; [apply Rlt_le; apply (proj1 Ht) | apply Rlt_le; apply (proj2 Ht)].
    }

    pose proof (RInt_Reals (fun t => Rpower t a) x 1 Hriem) as Heq.
    rewrite Heq in Hle.
    rewrite RInt_const in Hle; simpl in Hle.
    change (scal (1 - x) 1) with ((1 - x) * 1) in Hle.
    rewrite Rmult_1_r in Hle.

    assert (Hr_ge_0 : 0 <= r).
    {
      assert (H0 : 0 <= RInt (fun t => Rpower t a) x 1).
      { apply RInt_ge_0; [lra | exact Hex_f | intros t Ht; apply Rlt_le; apply Rpower_pos; lra]. }
      rewrite Heq in H0; exact H0.
    }

    assert (Hr_abs_lt_eps : Rabs r < eps).
    {
      rewrite Rabs_pos_eq; [| exact Hr_ge_0].
      apply Rlt_le_trans with δ.
      - apply Rle_lt_trans with (1 - x).
        + exact Hle.
        + apply Rminus_lt; lra.
      - exact Hδ_le_eps.
    }

    exists r.
    split; [exact His | ].
    apply Heps.
    apply norm_compat1.
    rewrite Rminus_0_r.
    exact Hr_abs_lt_eps.
Qed.

(** Gamma积分收敛性证明 *)

Require Import Stdlib.Reals.Reals.
Require Import Stdlib.micromega.Lra.
Require Import Coquelicot.Coquelicot.
Require Import Coquelicot.Rbar.
Require Import Coquelicot.RInt_gen.
Require Import Coquelicot.RInt.

Import ComplexNumbers.
Import PrimeEmbedding.
Import Rbar.
Open Scope R_scope.
Open Scope complex_scope.

Section GammaIntegralFacts.

(** 定义：上下文变量和局部定义 *)
Context (s : Complex) (Hre : 1 < ComplexNumbers.re s).

Let a := ComplexNumbers.re s - 1.
Let c := (1/2)%R.
Let f := fun t : R => match Rlt_dec 0 t with
                      | left H => gamma_integrand_real s t H
                      | right _ => 0
                      end.

(** 确保a大于0 *)
Lemma a_pos : 0 < a.
Proof. unfold a; apply Rgt_minus; assumption. Qed.

(** 确保c为正 *)
Lemma c_pos : 0 < c.
Proof. unfold c; apply Rmult_lt_0_compat; [apply Rlt_0_1 | apply Rinv_0_lt_compat, Rlt_0_2]. Qed.

(** c小于1 *)
Lemma c_lt_1 : c < 1.
Proof. unfold c; lra. Qed.

(** f(t)在t>0时等于指数与幂函数的乘积 *)
Lemma f_eq_exp_times_Rpower : forall t (Ht : 0 < t), f t = exp (-t) * Rpower t a.
Proof.
  intros t Ht.
  unfold f.
  destruct (Rlt_dec 0 t) as [Hpos|Hnotpos]; [| contradiction].
  rewrite (proof_irrelevance _ Hpos Ht).
  unfold gamma_integrand_real; simpl.
  unfold real_pow, Rpower; reflexivity.
Qed.

(** f在区间[c,1]上连续 *)
Lemma cont_f_c1 : forall t, c <= t <= 1 -> continuous f t.
Proof.
  intros t [Ht_low Ht_high].
  assert (Ht0 : 0 < t).
  { apply Rlt_le_trans with c; [apply c_pos | exact Ht_low]. }
  pose (g := fun x : R => exp (-x) * Rpower x a).
  assert (Hloc_eq : locally t (fun x : R_UniformSpace => f x = g x)).
  {
    exists (mkposreal (t/2) (Rlt_mult_inv_pos t 2 Ht0 Rlt_0_2)).
    intros x Hball.
    unfold ball, AbsRing_ball in Hball; simpl in Hball.
    assert (Habs : Rabs (x - t) < t / 2) by exact Hball.
    assert (Hbetween : - (t / 2) < x - t /\ x - t < t / 2).
    { apply Rabs_lt_between; exact Habs. }
    destruct Hbetween as [Hleft Hright].
    assert (Hx_gt_half_t : x > t / 2) by lra.
    assert (Hx_pos : 0 < x).
    { apply Rlt_trans with (t / 2); [| exact Hx_gt_half_t].
      apply Rmult_lt_0_compat; [exact Ht0 | lra]. }
    destruct (Rlt_dec 0 x) as [Hpos | Hneg].
    - simpl.
      rewrite (f_eq_exp_times_Rpower x Hpos).
      unfold g.
      reflexivity.
    - exfalso.
      apply Hneg.
      exact Hx_pos.
  }
  assert (Hcont_neg : continuity_pt (fun x : R => - x) t).
  { apply continuity_pt_opp. apply continuity_pt_id. }
  assert (Hcont_exp_at_neg_t : continuity_pt exp (- t)).
  { apply derivable_continuous_pt. apply derivable_pt_exp. }
  assert (Hcont_exp_neg : continuity_pt (fun x : R => exp (-x)) t).
  { apply continuity_pt_comp with (f1 := fun x : R => -x) (f2 := exp).
    - exact Hcont_neg.
    - exact Hcont_exp_at_neg_t. }
  assert (Hcont_Rpower : continuity_pt (fun x : R => Rpower x a) t).
  { apply continuity_pt_Rpower_pos.
    - apply a_pos.
    - exact Ht0. }
  assert (Hcont_g_pt : continuity_pt g t).
  { unfold g.
    apply continuity_pt_mult.
    - exact Hcont_exp_neg.
    - exact Hcont_Rpower. }
  assert (Hcont_g : continuous g t).
  { apply continuity_pt_to_continuous_simple. exact Hcont_g_pt. }
  assert (Hloc_eq_sym : locally t (fun y : R_UniformSpace => g y = f y)).
  {
    apply filter_imp with (P := fun x : R_UniformSpace => f x = g x).
    - intros x H_eq.
      apply eq_sym.
      exact H_eq.
    - exact Hloc_eq.
  }
  apply continuous_ext_loc with (g := g) (x := t).
  - exact Hloc_eq_sym.
  - exact Hcont_g.
Qed.

(** f在区间(0,c]上的绝对值有界 *)
Lemma bound_f : forall t, 0 < t <= c -> Rabs (f t) <= Rpower t a.
Proof.
  intros t [Ht0 Ht1].
  rewrite (f_eq_exp_times_Rpower t Ht0).
  rewrite Rabs_mult.
  assert (Hexp_pos : 0 < exp (-t)) by apply exp_pos.
  assert (HRpower_pos : 0 < Rpower t a).
  { unfold Rpower; apply exp_pos. }
  rewrite (Rabs_pos_eq (exp (-t))) by (left; exact Hexp_pos).
  rewrite (Rabs_pos_eq (Rpower t a)) by (left; exact HRpower_pos).
  assert (Hexp_le_1 : exp (-t) <= 1).
  { apply Rlt_le. assert (-t < 0) by lra. apply exp_increasing in H; rewrite exp_0 in H; exact H. }
  rewrite <- Rmult_1_l.
  apply Rmult_le_compat_r.
  - apply Rlt_le; exact HRpower_pos.
  - exact Hexp_le_1.
Qed.

End GammaIntegralFacts.

(** Rpower在[c,1]上的正常可积性 *)
Lemma Rpower_integrable_c1 (a c : R) (Ha : 0 < a) (Hc_pos : 0 < c) (Hc_lt1 : c < 1) :
  ex_RInt (fun t : R => Rpower t a) c 1.
Proof.
  apply ex_RInt_continuous with (f := fun t : R => Rpower t a) (a := c) (b := 1).
  intros z Hz.
  destruct Hz as [Hlow Hhigh].
  rewrite (Rmin_left c 1) in Hlow by lra.
  rewrite (Rmax_right c 1) in Hhigh by lra.
  assert (Hz_pos : 0 < z) by (apply Rlt_le_trans with c; [exact Hc_pos | exact Hlow]).
  apply continuity_pt_to_continuous.
  apply continuity_pt_Rpower_pos; [exact Ha | exact Hz_pos].
Qed.

(** 积分区间分割等式 *)
Lemma RInt_interval_split_eq (f : R -> R) (u c : R) 
  (Hu_pos : 0 < u) (Huc : u < c) (Hc_lt1 : c < 1)
  (Hex_uc : ex_RInt f u c) (Hex_c1 : ex_RInt f c 1) :
  RInt f u 1 - RInt f c 1 = RInt f u c.
Proof.
  rewrite <- (RInt_Chasles f u c 1 Hex_uc Hex_c1).
  unfold Rminus.
  rewrite Rplus_assoc, Rplus_opp_r, Rplus_0_r.
  reflexivity.
Qed.

(** 从广义可积推出的区间可积性 *)
Lemma interval_integrable_from_improper (f : R -> R) :
  (forall t : R, 0 < t <= 1 -> continuous f t) ->
  forall u : R, 0 < u < 1 -> ex_RInt f u 1.
Proof.
  intros Hcont_f u [Hu_pos Hu_lt1].
  assert (Hmin_eq : Rmin u 1 = u) by (apply Rmin_left; lra).
  assert (Hmax_eq : Rmax u 1 = 1) by (apply Rmax_right; lra).
  assert (Hcont_interval : forall z : R, u <= z <= 1 -> continuous f z).
  { intros z Hz.
    apply Hcont_f.
    split.
    - apply Rlt_le_trans with u; [exact Hu_pos | apply Hz].
    - apply Hz. }
  apply (ex_RInt_continuous f u 1).
  intros x Hx.
  rewrite Hmin_eq, Hmax_eq in Hx.
  apply Hcont_interval; exact Hx.
Qed.

(** 从广义积分定义提取ε-δ形式 *)
Lemma is_RInt_gen_P : forall (f : R -> R) (I0 : R),
  is_RInt_gen f (at_right 0) (at_left 1) I0 ->
  forall eps : posreal,
  exists A : R -> Prop, exists B : R -> Prop,
    at_right 0 A /\ at_left 1 B /\
    forall (a b : R), A a -> B b -> Rabs (RInt f a b - I0) < pos eps.
Proof.
  intros f I0 Hgen [eps Heps].
  set (P := fun y : R => Rabs (y - I0) < eps).
  assert (HP : locally I0 P) by (exists (mkposreal eps Heps); intros y Hy; apply Hy).
  unfold is_RInt_gen, filterlim in Hgen.
  specialize (Hgen P HP).
  apply filter_prod_ind with
    (P0 := exists A B : R -> Prop,
           at_right 0 A /\ at_left 1 B /\
           forall a b, A a -> B b -> Rabs (RInt f a b - I0) < eps) in Hgen.
  - exact Hgen.
  - intros A B HA HB HAB.
    exists A, B.
    split; [exact HA | split; [exact HB | ]].
    intros a b Ha Hb.
    specialize (HAB a b Ha Hb) as [y [HyP HyP0]].
    rewrite (is_RInt_unique f a b y HyP).
    exact HyP0.
Qed.

(** 定积分值的唯一性 *)
Lemma is_RInt_unique : forall (f : R -> R) (a b l1 l2 : R),
  is_RInt f a b l1 -> is_RInt f a b l2 -> l1 = l2.
Proof.
  intros f a b l1 l2 H1 H2.
  assert (H1' : RInt f a b = l1) by apply (is_RInt_unique f a b l1 H1).
  assert (H2' : RInt f a b = l2) by apply (is_RInt_unique f a b l2 H2).
  rewrite H1' in H2'; auto.
Qed.

(** 构造满足邻域条件的点a *)
Lemma A_eps_a :
  forall (u : R) (Hu_pos : 0 < u) (delta_eps : posreal)
    (A_eps : R -> Prop) (Hdelta_eps : forall y, ball 0 delta_eps y -> 0 < y -> A_eps y),
  let a := Rmin (u / 2) (pos delta_eps / 2) in
  A_eps a.
Proof.
  intros u Hu_pos delta_eps A_eps Hdelta_eps.
  set (a := Rmin (u / 2) (pos delta_eps / 2)).
  assert (Ha_pos : 0 < a).
  {
    apply Rmin_pos.
    - apply Rmult_lt_0_compat; [exact Hu_pos | lra].
    - apply Rmult_lt_0_compat; [apply cond_pos | lra].
  }
  assert (Ha_lt_delta_eps : a < pos delta_eps).
  {
    apply Rle_lt_trans with (pos delta_eps / 2).
    - apply Rmin_r.
    - assert (0 < pos delta_eps) by apply cond_pos; lra.
  }
  apply Hdelta_eps.
  - unfold ball; simpl; unfold AbsRing_ball.
    rewrite Rminus_0_r.
    rewrite Rabs_pos_eq; [| left; exact Ha_pos].
    exact Ha_lt_delta_eps.
  - exact Ha_pos.
Qed.

(** 获取初始的delta0 *)
Lemma get_initial_delta : forall (f : R -> R) (I0 : R)
  (Hgen : is_RInt_gen f (at_right 0) (at_left 1) I0),
  exists delta0 : R, 0 < delta0 <= 1.
Proof.
  intros f I0 Hgen.
  destruct (is_RInt_gen_P f I0 Hgen (mkposreal 1 Rlt_0_1)) as [A1 [B1 [HA1 [HB1 HAB1]]]].
  destruct HA1 as [delta1 Hdelta1].
  exists (Rmin (pos delta1) 1).
  split.
  - apply Rmin_pos; [apply cond_pos | apply Rlt_0_1].
  - apply Rmin_r.
Qed.

(** 构造左邻域1中的谓词 *)
Lemma at_left_1_inter :
  forall (u : R) (Hu_lt_1 : u < 1) (B_eps : R -> Prop) (delta_b : posreal)
    (Hdelta_b : forall y, ball 1 delta_b y -> y < 1 -> B_eps y),
  at_left 1 (fun x => B_eps x /\ u < x < 1).
Proof.
  intros u Hu_lt_1 B_eps delta_b Hdelta_b.
  unfold at_left, within.
  set (delta_P := Rmin (pos delta_b) ((1 - u) / 2)).
  assert (Hdelta_P_pos : 0 < delta_P).
  { apply Rmin_pos; [apply cond_pos | lra]. }
  exists (mkposreal delta_P Hdelta_P_pos).
  intros y Hy Hlt.
  split.
  - apply Hdelta_b.
    + unfold ball in Hy; simpl in Hy; unfold AbsRing_ball in Hy.
      eapply Rlt_le_trans; [exact Hy | apply Rmin_l].
    + exact Hlt.
  - split; [| exact Hlt].
    unfold ball, AbsRing_ball in Hy; simpl in Hy.
    assert (Habs : Rabs (y - 1) < delta_P) by exact Hy.
    assert (H_neg : y - 1 < 0) by lra.
    assert (H_nonpos : y - 1 <= 0) by lra.
    assert (Habs_eq : Rabs (y - 1) = 1 - y).
    { rewrite Rabs_left1; [ring | exact H_nonpos]. }
    rewrite Habs_eq in Habs.
    assert (Hdelta_P_bound : delta_P <= (1 - u) / 2) by apply Rmin_r.
    assert (H1_minus_y_lt : 1 - y < (1 - u) / 2).
    { eapply Rlt_le_trans; [exact Habs | exact Hdelta_P_bound]. }
    lra.
Qed.

(** 构造点a并证明其基本性质 *)
Lemma a_properties :
  forall (u : R) (Hu_pos : 0 < u) (delta_eps : posreal),
  let a := Rmin (u / 2) (pos delta_eps / 2) in
  0 < a /\ a < pos delta_eps /\ a < u.
Proof.
  intros u Hu_pos delta_eps.
  set (a := Rmin (u / 2) (pos delta_eps / 2)).
  assert (Ha_pos : 0 < a).
  { apply Rmin_pos.
    - apply Rmult_lt_0_compat; [exact Hu_pos | lra].
    - apply Rmult_lt_0_compat; [apply cond_pos | lra]. }
  assert (Ha_lt_delta_eps : a < pos delta_eps).
  { apply Rle_lt_trans with (pos delta_eps / 2).
    - apply Rmin_r.
    - assert (0 < pos delta_eps) by apply cond_pos; lra. }
  assert (Ha_lt_u : a < u).
  { apply Rle_lt_trans with (u / 2).
    - apply Rmin_l.
    - lra. }
  repeat split; assumption.
Qed.

(** 1的任意实数次幂恒为1 *)
Lemma Rpower_1_r : forall b : R, Rpower 1 b = 1.
Proof.
  intros b.
  unfold Rpower.
  rewrite ln_1.
  rewrite Rmult_0_r.
  rewrite exp_0.
  reflexivity.
Qed.

Require Import Coquelicot.RInt.

(** 广义积分的柯西准则 *)
Lemma RInt_gen_cauchy_criterion : forall (f : R -> R) (I0 : R),
  is_RInt_gen f (at_right 0) (at_left 1) I0 ->
  forall eps : R, eps > 0 -> exists delta : R, delta > 0 /\
  forall a1 a2 : R, 0 < a1 /\ a1 < a2 /\ a2 < delta -> Rabs (RInt f a1 a2) < eps.
Proof.
  intros f I0 Hgen eps Heps.
  assert (Hhalf : 0 < eps / 2) by lra.

  set (P := fun x : R => Rabs (x - I0) < eps / 2).

  assert (Hloc : locally I0 P).
  {
    exists (mkposreal (eps / 2) Hhalf).
    intros y Hy.
    unfold P, ball, AbsRing_ball in *; simpl in *.
    exact Hy.
  }

  assert (Hprod : filter_prod (at_right 0) (at_left 1)
    (fun x : R * R => exists y : R, is_RInt f (fst x) (snd x) y /\ P y)).
  {
    exact (Hgen P Hloc).
  }

  apply (filter_prod_ind R R (at_right 0) (at_left 1)
    (fun p => exists y, is_RInt f (fst p) (snd p) y /\ P y)
    (exists delta : R, delta > 0 /\
      forall a1 a2 : R, 0 < a1 /\ a1 < a2 /\ a2 < delta -> Rabs (RInt f a1 a2) < eps)).
  - intros A B HA HB HAB_orig.
    destruct HA as [d1 Hd1].
    destruct HB as [d2 Hd2].
    set (delta1 := pos d1). set (delta2 := pos d2).
    assert (Hdelta1_pos : 0 < delta1) by apply (cond_pos d1).
    assert (Hdelta2_pos : 0 < delta2) by apply (cond_pos d2).

    assert (Hmin_pos : 0 < Rmin (1/2) (delta2 / 2)).
    { apply Rmin_pos; [lra | apply Rmult_lt_0_compat; [exact Hdelta2_pos | lra]]. }
    set (b := 1 - Rmin (1/2) (delta2 / 2)).
    assert (Hb_gt_0 : 0 < b).
    { apply Rlt_le_trans with (1 - 1/2). lra. unfold b. apply Rplus_le_compat_l. apply Ropp_le_contravar. apply Rmin_l. }
    assert (Hb_lt_1 : b < 1) by (unfold b; lra).

    assert (Hb_in_ball : ball 1 d2 b).
    {
      unfold ball; simpl; unfold AbsRing_ball.
      rewrite Rabs_minus_sym.
      replace (1 - b) with (Rmin (1/2) (delta2/2)) by (unfold b; ring).
      assert (Hpos : 0 < Rmin (1/2) (delta2/2)) by exact Hmin_pos.
      rewrite (Rabs_pos_eq (Rmin (1/2) (delta2/2)) (Rlt_le _ _ Hpos)).
      apply Rle_lt_trans with (delta2/2).
      - apply Rmin_r.
      - unfold delta2 in *; lra.
    }
    assert (HBb : B b) by (apply Hd2; [exact Hb_in_ball | exact Hb_lt_1]).

    set (delta := Rmin (Rmin delta1 (delta2 / 2)) b).
    assert (Hdelta_le_d1 : delta <= delta1).
    { unfold delta; apply Rle_trans with (Rmin delta1 (delta2 / 2));
        [apply Rmin_l | apply Rmin_l]. }
    assert (Hdelta_le_d2_half : delta <= delta2 / 2).
    { unfold delta; apply Rle_trans with (Rmin delta1 (delta2 / 2));
        [apply Rmin_l | apply Rmin_r]. }
    assert (Hdelta_le_b : delta <= b) by apply Rmin_r.

    assert (Hdelta_pos : 0 < delta).
    {
      apply Rmin_pos.
      - apply Rmin_pos.
        + exact Hdelta1_pos.
        + apply Rmult_lt_0_compat; [exact Hdelta2_pos | lra].
      - exact Hb_gt_0.
    }

    exists delta.
    split.
    + exact Hdelta_pos.
    + intros a1 a2 [Ha1 [Hlt Ha2]].
      assert (Ha1_pos : 0 < a1) by exact Ha1.
      assert (Ha2_lt_delta : a2 < delta) by exact Ha2.
      assert (Ha1_lt_delta : a1 < delta) by (apply Rlt_trans with a2; auto).

      assert (Aa1 : A a1).
      {
        apply Hd1.
        - unfold ball; simpl; unfold AbsRing_ball.
          rewrite Rminus_0_r.
          rewrite Rabs_pos_eq; [| left; exact Ha1].
          apply Rlt_le_trans with delta.
          + apply Rlt_trans with a2; [exact Hlt | exact Ha2].
          + exact Hdelta_le_d1.
        - exact Ha1.
      }

      assert (Ha2_pos : 0 < a2) by (apply Rlt_trans with a1; [exact Ha1 | exact Hlt]).
      assert (Aa2 : A a2).
      {
        apply Hd1.
        - unfold ball; simpl; unfold AbsRing_ball.
          rewrite Rminus_0_r.
          assert (H_nonneg : 0 <= a2) by (apply Rlt_le; exact Ha2_pos).
          rewrite Rabs_pos_eq; [| exact H_nonneg].
          apply Rlt_le_trans with delta.
          + exact Ha2.
          + exact Hdelta_le_d1.
        - exact Ha2_pos.
      }

      destruct (HAB_orig a1 b Aa1 HBb) as [y1 [Hint1 HP1]].
      destruct (HAB_orig a2 b Aa2 HBb) as [y2 [Hint2 HP2]].

      assert (Hlt_b : a2 < b) by (apply Rlt_le_trans with delta; [exact Ha2 | exact Hdelta_le_b]).

      assert (HChasles : is_RInt f a1 a2 (minus y1 y2)).
      {
        apply is_RInt_Chasles_1 with (c := b) (l1 := y1) (l2 := y2).
        - split; [exact Hlt | exact Hlt_b].
        - exact Hint1.
        - exact Hint2.
      }

      rewrite (is_RInt_unique f a1 a2 (minus y1 y2) HChasles).

      unfold minus.
      replace (y1 + opp y2) with (y1 - y2) by (unfold minus; reflexivity).
      assert (Htriangle : Rabs (y1 - y2) <= Rabs (y1 - I0) + Rabs (I0 - y2)).
      {
        replace (y1 - y2) with ((y1 - I0) + (I0 - y2)) by ring.
        apply Rabs_triang.
      }
      rewrite (Rabs_minus_sym I0 y2) in Htriangle.
      apply Rle_lt_trans with (Rabs (y1 - I0) + Rabs (y2 - I0)).
      * exact Htriangle.
      * assert (Hsum: Rabs (y1 - I0) + Rabs (y2 - I0) < eps/2 + eps/2).
        { apply Rplus_lt_compat; [exact HP1 | exact HP2]. }
        replace (eps/2 + eps/2) with eps in Hsum by (field; lra).
        exact Hsum.

  - exact Hprod.
Qed.

(** 右极限积分上限的收敛性 *)
Lemma RInt_gen_limit_at_right_0 (f : R -> R) (I0 : R)
  (Hcont_f : forall t : R, 0 < t <= 1 -> continuous f t)
  (Hgen : is_RInt_gen f (at_right 0) (at_left 1) I0) :
  filterlim (fun u : R => RInt f u 1) (at_right 0) (locally I0).
Proof.
  intros P [eps Hball].
  set (eps1 := pos eps / 3).
  assert (Heps1 : 0 < eps1).
  { unfold eps1.
    apply Rmult_lt_0_compat.
    - apply cond_pos.
    - apply Rinv_0_lt_compat. lra. }

  destruct (is_RInt_gen_P f I0 Hgen eps) as [A1 [B1 [HA1 [HB1 HAB1]]]].
  destruct (is_RInt_gen_P f I0 Hgen (mkposreal eps1 Heps1)) as [A2 [B2 [HA2 [HB2 HAB2]]]].

  assert (exists A, at_right 0 A /\ forall a, A a -> A1 a /\ A2 a).
  { exists (fun a => A1 a /\ A2 a). split.
    - apply filter_and; [exact HA1 | exact HA2].
    - intros a H; split; [apply H | apply H]. }
  destruct H as [A [HA Hinter]].

  unfold at_right in HA.
  destruct HA as [delta Hdelta].
  set (delta0 := Rmin (pos delta) (1/2)).
  assert (Hdelta0 : 0 < delta0).
  { apply Rmin_pos.
    - apply cond_pos.
    - lra. }

  exists (mkposreal delta0 Hdelta0).
  intros u Hu_in_ball Hu_pos.

  assert (Hu_lt : u < delta0).
  {
    unfold ball, AbsRing_ball in Hu_in_ball; simpl in Hu_in_ball.
    change (Rabs (u - 0) < delta0) in Hu_in_ball.
    rewrite Rminus_0_r in Hu_in_ball.
    rewrite Rabs_pos_eq in Hu_in_ball by lra.
    exact Hu_in_ball.
  }

  assert (Hu_A : A u).
  { apply Hdelta.
    - unfold ball, AbsRing_ball; simpl.
      change (Rabs (u - 0) < pos delta).
      rewrite Rminus_0_r.
      rewrite Rabs_pos_eq by lra.
      apply Rlt_le_trans with (r2 := delta0).
      + exact Hu_lt.
      + unfold delta0; apply Rmin_l.
    - exact Hu_pos. }
  destruct (Hinter u Hu_A) as [Hu_A1 Hu_A2].

  assert (Hdelta0_le_half : delta0 <= 1/2).
  { unfold delta0; apply Rmin_r. }
  assert (Hhalf_le_one : (1/2 : R) <= 1) by lra.
  assert (Hdelta0_le_one : delta0 <= 1) by lra.
  assert (Hu_lt1 : u < 1).
  {
    apply Rlt_le_trans with (r2 := delta0).
    - exact Hu_lt.
    - exact Hdelta0_le_one.
  }

  assert (Hex : ex_RInt f u 1).
  {
    apply interval_integrable_from_improper with (f := f).
    - exact Hcont_f.
    - split; [exact Hu_pos | exact Hu_lt1].
  }
  pose (L := RInt f u 1).

  (* 积分上限函数的左极限 *)
  assert (Hlim : filterlim (fun v : R => RInt f u v) (at_left 1) (locally L)).
  {
    intros P' [eps_pos Hball'].
    set (eps' := pos eps_pos).
    assert (Heps'_pos : 0 < eps').
    { apply cond_pos. }

    assert (Hcont_f1 : continuous f 1) by (apply Hcont_f; split; [lra | apply Rle_refl]).
    assert (Hball_f1 : locally (f 1) (fun y => Rabs (y - f 1) < 1)).
    { exists (mkposreal 1 Rlt_0_1); intros y Hy; exact Hy. }
    specialize (Hcont_f1 (fun y => Rabs (y - f 1) < 1) Hball_f1) as Hloc.
    apply locally_iff_open_ball in Hloc.
    destruct Hloc as [delta_loc [Hdelta_loc_pos Hdelta_loc]].
    set (M := Rabs (f 1) + 1).
    assert (M_pos : 0 < M).
    { unfold M; apply Rplus_le_lt_0_compat; [apply Rabs_pos | apply Rlt_0_1]. }
    assert (Hf_bound : forall t, Rabs (t - 1) < delta_loc -> Rabs (f t) < M).
    {
      intros t Ht.
      specialize (Hdelta_loc t Ht).
      assert (Hf_eq : f t = f 1 + (f t - f 1)) by ring.
      rewrite Hf_eq.
      apply Rle_lt_trans with (Rabs (f 1) + Rabs (f t - f 1)).
      - apply Rabs_triang.
      - apply Rplus_lt_compat_l; exact Hdelta_loc.
    }

    assert (Heps'_M_pos : 0 < eps' / M) by (apply Rdiv_lt_0_compat; auto).
    set (delta_v := Rmin (Rmin (delta_loc / 2) (eps' / (2 * M))) (1/2)).
    assert (Hdelta_v_pos : 0 < delta_v).
    {
      unfold delta_v.
      apply Rmin_pos.
      - apply Rmin_pos.
        + apply Rdiv_lt_0_compat; [exact Hdelta_loc_pos | lra].
        + apply Rdiv_lt_0_compat; [exact Heps'_pos | apply Rmult_lt_0_compat; [lra | exact M_pos]].
      - lra.
    }
    exists (mkposreal delta_v Hdelta_v_pos).
    intros v Hv_in_ball Hv_lt1.
    assert (Habs_v1 : Rabs (v - 1) < delta_v).
    { unfold ball, AbsRing_ball in Hv_in_ball; simpl in Hv_in_ball; exact Hv_in_ball. }
    assert (Hv_gt : v > 1 - delta_v).
    {
      rewrite Rabs_left1 in Habs_v1; [| lra].
      replace (- (v - 1)) with (1 - v) in Habs_v1 by ring.
      lra.
    }
    assert (Hdelta_v_le_half : delta_v <= 1/2) by (unfold delta_v; apply Rmin_r).
    assert (H1_minus_delta_v_pos : 0 < 1 - delta_v) by lra.
    assert (Hv_pos : 0 < v) by lra.

    assert (Hex_v1 : ex_RInt f v 1).
    { apply interval_integrable_from_improper with (f:=f); [exact Hcont_f | split; [exact Hv_pos | exact Hv_lt1]]. }

    assert (Hv_le_1 : v <= 1) by lra.
    assert (Habs_v1_le : Rabs (RInt f v 1) <= RInt (fun t => Rabs (f t)) v 1).
    { apply abs_RInt_le; [exact Hv_le_1 | exact Hex_v1]. }

    assert (H1_minus_v_lt_delta_v : 1 - v < delta_v) by lra.

    assert (Hdelta_v_le_delta_loc : delta_v <= delta_loc).
    {
      unfold delta_v.
      eapply Rle_trans.
      - apply Rmin_l.
      - apply Rle_trans with (delta_loc / 2).
        + apply Rmin_l.
        + lra.
    }

    assert (Habs_cont : forall t, v <= t <= 1 -> Rabs (f t) <= M).
    {
      intros t [Ht_low Ht_high].
      apply Rlt_le, Hf_bound.
      rewrite Rabs_minus_sym.
      rewrite Rabs_pos_eq; [| lra].
      apply Rlt_le_trans with delta_v.
      - apply Rle_lt_trans with (1 - v); [lra | exact H1_minus_v_lt_delta_v].
      - exact Hdelta_v_le_delta_loc.
    }

    assert (Habs_v1_le_M : Rabs (RInt f v 1) <= M * (1 - v)).
    {
      pose proof (abs_RInt_le_const f v 1 M Hv_le_1 Hex_v1 Habs_cont) as Htmp.
      rewrite Rmult_comm in Htmp.
      exact Htmp.
    }

    assert (Habs_final : Rabs (RInt f v 1) < eps').
    {
      apply Rle_lt_trans with (M * (1 - v)).
      - exact Habs_v1_le_M.
      - apply Rle_lt_trans with (M * delta_v).
        + apply Rmult_le_compat_l; [apply Rlt_le; exact M_pos | apply Rlt_le; exact H1_minus_v_lt_delta_v].
        + assert (Hdelta_v_le_eps_over_2M : delta_v <= eps' / (2 * M)).
          { unfold delta_v.
            apply Rle_trans with (Rmin (delta_loc / 2) (eps' / (2 * M))).
            - apply Rmin_l.
            - apply Rmin_r. }
          assert (Hmult_le : M * delta_v <= M * (eps' / (2 * M))).
          { apply Rmult_le_compat_l; [apply Rlt_le; exact M_pos | exact Hdelta_v_le_eps_over_2M]. }
          assert (Heq : M * (eps' / (2 * M)) = eps' / 2).
          { unfold Rdiv; field; lra. }
          rewrite Heq in Hmult_le.
          apply Rle_lt_trans with (eps' / 2).
          * exact Hmult_le.
          * lra.
    }

    assert (Hu_half : u < 1/2) by (apply Rlt_le_trans with delta0; [exact Hu_lt | exact Hdelta0_le_half]).
    assert (Hv_half : 1/2 < v).
    {
      destruct (Req_dec delta_v (1/2)) as [Hdv_eq | Hdv_neq].
      - rewrite Hdv_eq in Hv_gt.
        assert (Htmp : 1 - 1/2 = 1/2) by field.
        rewrite <- Htmp.
        exact Hv_gt.
      - assert (Hdv_lt : delta_v < 1/2) by lra.
        assert (H1_minus_delta_v_gt_half : 1 - delta_v > 1/2) by lra.
        apply Rlt_trans with (1 - delta_v); [exact H1_minus_delta_v_gt_half | exact Hv_gt].
    }
    assert (Huv : u < v) by (apply Rlt_trans with (1/2); [exact Hu_half | exact Hv_half]).

    assert (Hex_uv : ex_RInt f u v).
    {
      apply ex_RInt_continuous with (f := f) (a := u) (b := v).
      intros z Hz.
      rewrite (Rmin_left u v) in Hz by lra.
      rewrite (Rmax_right u v) in Hz by lra.
      apply Hcont_f.
      split.
      - apply Rlt_le_trans with u; [exact Hu_pos | apply Hz].
      - apply Rle_trans with v; [apply Hz | apply Rlt_le; exact Hv_lt1].
    }

    assert (Heq_chasles : RInt f u 1 = RInt f u v + RInt f v 1).
    { symmetry. apply (RInt_Chasles f u v 1 Hex_uv Hex_v1). }

    assert (Htarget_eq : RInt f u v - L = - RInt f v 1).
    { unfold L. rewrite Heq_chasles. ring. }

    assert (Hball_uv : ball L eps_pos (RInt f u v)).
    {
      change (Rabs (RInt f u v - L) < pos eps_pos).
      rewrite Htarget_eq.
      rewrite Rabs_Ropp.
      exact Habs_final.
    }
    apply Hball' in Hball_uv.
    exact Hball_uv.
  }

  assert (Hlim_eps1 : exists delta_L : posreal,
            forall v, ball 1 delta_L v -> v < 1 -> Rabs (RInt f u v - L) < eps1).
  {
    pose (P'' := fun y => ball L (mkposreal eps1 Heps1) y).
    assert (Hloc : locally L P'') by (exists (mkposreal eps1 Heps1); intros; assumption).
    specialize (Hlim P'' Hloc) as [delta_L Hdelta_L].
    exists delta_L.
    intros v Hball_v Hlt_v.
    specialize (Hdelta_L v Hball_v Hlt_v).
    unfold P'' in Hdelta_L; simpl in Hdelta_L.
    exact Hdelta_L.
  }
  destruct Hlim_eps1 as [delta_L Hcond_L].

  destruct HB2 as [delta2 Hdelta2].
  set (delta_b := Rmin (Rmin (pos delta_L) (pos delta2)) 1).
  assert (Hdelta_b_pos : 0 < delta_b).
  { apply Rmin_pos.
    - apply Rmin_pos; [apply cond_pos | apply cond_pos].
    - lra. }
  set (b := 1 - delta_b/2).
  assert (Hdelta_b_le_1 : delta_b <= 1) by (unfold delta_b; apply Rmin_r).

  assert (Hb_gt_0 : 0 < b).
  {
    assert (Hdelta_b_half_lt_1 : delta_b / 2 < 1).
    {
      assert (Hle_half : delta_b / 2 <= 1/2).
      { apply Rmult_le_compat_r; [lra | exact Hdelta_b_le_1]. }
      assert (Hhalf_lt_1 : 1/2 < 1) by lra.
      apply Rle_lt_trans with (1/2); [exact Hle_half | exact Hhalf_lt_1].
    }
    unfold b; lra.
  }
  assert (Hb_lt_1 : b < 1) by (unfold b; lra).

  assert (Habs_eq : Rabs (b - 1) = delta_b / 2).
  {
    unfold b.
    replace (1 - delta_b/2 - 1) with (- (delta_b/2)) by ring.
    rewrite Rabs_Ropp.
    assert (Hpos : 0 <= delta_b/2) by (apply Rlt_le, Rmult_lt_0_compat; [exact Hdelta_b_pos | lra]).
    apply Rabs_pos_eq.
    exact Hpos.
  }

  assert (Hb_in_ball_L : ball 1 delta_L b).
  {
    unfold ball, AbsRing_ball; simpl.
    assert (Hdelta_b_le_delta_L : delta_b <= pos delta_L).
    { unfold delta_b; apply Rle_trans with (Rmin (pos delta_L) (pos delta2)); [apply Rmin_l | apply Rmin_l]. }
    change (Rabs (b - 1) < pos delta_L).
    rewrite Habs_eq.
    apply Rlt_le_trans with delta_b.
    - lra.
    - exact Hdelta_b_le_delta_L.
  }

  assert (Hdelta_b_le_delta2 : delta_b <= pos delta2).
  { unfold delta_b; apply Rle_trans with (Rmin (pos delta_L) (pos delta2)); [apply Rmin_l | apply Rmin_r]. }
  assert (Hb_in_ball2 : ball 1 delta2 b).
  {
    unfold ball, AbsRing_ball; simpl.
    change (Rabs (b - 1) < pos delta2).
    rewrite Habs_eq.
    apply Rlt_le_trans with delta_b.
    - lra.
    - exact Hdelta_b_le_delta2.
  }

  assert (Hb_B2 : B2 b) by (apply Hdelta2; [exact Hb_in_ball2 | exact Hb_lt_1]).
  assert (Hcond_L_b : Rabs (RInt f u b - L) < eps1) by (apply Hcond_L; [exact Hb_in_ball_L | exact Hb_lt_1]).

  assert (Hfinal : Rabs (RInt f u 1 - I0) < eps).
  {
    replace (RInt f u 1 - I0) with ((RInt f u 1 - RInt f u b) + (RInt f u b - I0)) by ring.
    apply Rle_lt_trans with (Rabs (RInt f u 1 - RInt f u b) + Rabs (RInt f u b - I0)).
    - apply Rabs_triang.
    - replace (RInt f u 1) with L by (unfold L; reflexivity).
      assert (H1 : Rabs (L - RInt f u b) = Rabs (RInt f u b - L)) by (apply Rabs_minus_sym).
      rewrite H1.
      apply Rlt_trans with (eps1 + eps1).
      + apply Rplus_lt_compat.
        * exact Hcond_L_b.
        * specialize (HAB2 u b Hu_A2 Hb_B2) as Htmp.
          unfold eps1 in Htmp; simpl in Htmp.
          exact Htmp.
      + replace (pos eps) with (3 * eps1) by (unfold eps1; field).
        assert (0 < eps1) by exact Heps1.
        lra.
  }

  apply Hball.
  unfold ball, AbsRing_ball; simpl.
  exact Hfinal.
Qed.

(* 存在性: 右极限积分 *)
Lemma RInt_gen_limit_at_right_0_exist (f : R -> R)
  (Hcont_f : forall t : R, 0 < t <= 1 -> continuous f t)
  (Hgen : ex_RInt_gen f (at_right 0) (at_left 1)) :
  exists I : R, filterlim (fun u : R => RInt f u 1) (at_right 0) (locally I).
Proof.
  destruct Hgen as [I0 Hgen].
  exists I0.
  exact (RInt_gen_limit_at_right_0 f I0 Hcont_f Hgen).
Qed.

(* 连续映射: 两点差 *)
Lemma continuous_2_minus {V : NormedModule R_AbsRing} (a b : V) :
  continuous (fun p : V * V => plus (fst p) (opp (snd p))) (a, b).
Proof.
  eapply continuous_plus.
  - apply continuous_fst.
  - apply continuous_opp, continuous_snd.
Qed.

(* 幂函数在(0,c]上的广义可积性 *)
Lemma Rpower_integrable_0c (a c : R) (Ha : 0 < a) (Hc_pos : 0 < c) (Hc_lt1 : c < 1) :
  ex_RInt_gen (fun t : R => Rpower t a) (at_right 0) (at_point c).
Proof.
  assert (Hcont : forall t, 0 < t <= 1 -> continuous (fun t => Rpower t a) t).
  { intros t Ht.
    apply continuity_pt_to_continuous.
    apply continuity_pt_Rpower_pos; [exact Ha | lra]. }

  destruct (Rpower_integrable_01 a Ha) as [I01 Hgen01].

  assert (H_lim1 : filterlim (fun u : R => RInt (fun t => Rpower t a) u 1)
                             (at_right 0) (locally I01)).
  { apply RInt_gen_limit_at_right_0 with (I0 := I01); [exact Hcont | exact Hgen01]. }

  assert (Hex_c1 : ex_RInt (fun t => Rpower t a) c 1).
  { apply Rpower_integrable_c1; assumption. }
  set (Ic1 := RInt (fun t => Rpower t a) c 1).

  assert (Heq_loc : at_right 0 (fun u =>
      RInt (fun t => Rpower t a) u c =
      RInt (fun t => Rpower t a) u 1 - Ic1)).
  {
    exists (mkposreal c Hc_pos). intros u Hball Hpos.
    unfold ball, AbsRing_ball in Hball; simpl in Hball.
    unfold AbsRing_ball in Hball; simpl in Hball.
    rewrite Rminus_0_r in Hball.
    rewrite Rabs_pos_eq in Hball; [| apply Rlt_le; exact Hpos].
    assert (Hu_lt_c : u < c) by exact Hball.

    assert (ex_RInt (fun t => Rpower t a) u c) as Hex_uc.
    { apply ex_RInt_continuous with (f := fun t => Rpower t a) (a := u) (b := c).
      intros z Hz.
      destruct Hz as [Hz1 Hz2].
      rewrite Rmin_left in Hz1 by lra.
      rewrite Rmax_right in Hz2 by lra.
      apply continuity_pt_to_continuous.
      apply continuity_pt_Rpower_pos; [exact Ha |].
      apply Rlt_le_trans with u; [exact Hpos | exact Hz1]. }

    assert (ex_RInt (fun t => Rpower t a) u 1) as Hex_u1.
    { apply ex_RInt_continuous with (f := fun t => Rpower t a) (a := u) (b := 1).
      intros z Hz.
      destruct Hz as [Hz1 Hz2].
      rewrite Rmin_left in Hz1 by lra.
      rewrite Rmax_right in Hz2 by lra.
      apply continuity_pt_to_continuous.
      apply continuity_pt_Rpower_pos; [exact Ha |].
      apply Rlt_le_trans with u; [exact Hpos | exact Hz1]. }

    pose proof (RInt_Chasles (fun t => Rpower t a) u c 1 Hex_uc Hex_c1) as Hchasles.

    unfold minus.
    rewrite <- Hchasles.
    replace (RInt (fun t => Rpower t a) c 1) with Ic1 by reflexivity.
    assert (Htemp: forall (A B : R), (A + B) + - B = A).
    { intros A B; ring. }
    rewrite Rminus_def.
    replace (plus (RInt (fun t => Rpower t a) u c) Ic1) with (RInt (fun t => Rpower t a) u c + Ic1) by reflexivity.
    rewrite (Htemp (RInt (fun t => Rpower t a) u c) Ic1).
    reflexivity.
  }

  assert (Heq_loc_sym : at_right 0 (fun u =>
      RInt (fun t => Rpower t a) u 1 - Ic1 = RInt (fun t => Rpower t a) u c)).
  {
    eapply filter_imp.
    - intros u Heq. symmetry. exact Heq.
    - exact Heq_loc.
  }

  assert (H_const : filterlim (fun _ : R => - Ic1) (at_right 0) (locally (- Ic1))).
  { apply filterlim_const. }

  assert (H_pair : filterlim (fun u => (RInt (fun t => Rpower t a) u 1, - Ic1))
                             (at_right 0)
                             (filter_prod (locally I01) (locally (- Ic1)))).
  {
    apply filterlim_pair.
    - exact H_lim1.
    - exact H_const.
  }

  assert (H_plus : filterlim (fun u => RInt (fun t => Rpower t a) u 1 + - Ic1)
                             (at_right 0)
                             (locally (plus I01 (- Ic1)))).
  {
    apply (@filterlim_comp R (R * R) R
           (fun u => (RInt (fun t => Rpower t a) u 1, - Ic1))
           (fun p => plus (fst p) (snd p))
           (at_right 0)
           (filter_prod (locally I01) (locally (- Ic1)))
           (locally (plus I01 (- Ic1)))
           H_pair
           (filterlim_plus I01 (- Ic1))).
  }

  assert (H_lim_c : filterlim (fun u : R => RInt (fun t => Rpower t a) u c)
                               (at_right 0) (locally (I01 + (- Ic1)))).
  {
    apply filterlim_ext_loc with (f := fun u : R => (RInt (fun t => Rpower t a) u 1) + (- Ic1)).
    - exact Heq_loc_sym.
    - exact H_plus.
  }

  assert (H_gen : is_RInt_gen (fun t : R => Rpower t a) (at_right 0) (at_point c) (I01 + (- Ic1))).
  {
    unfold is_RInt_gen.
    intros P HP.
    specialize (H_lim_c P HP) as [A HA].

    apply Filter_prod with
      (Q := fun u => 0 < u < A)
      (R := fun v => v = c).

    - unfold at_right.
      exists (mkposreal A (cond_pos A)).
      intros u Hu Hpos.
      split; [exact Hpos |].
      unfold ball, AbsRing_ball in Hu; simpl in Hu.
      unfold AbsRing_ball in Hu.
      rewrite Rminus_0_r in Hu.
      rewrite Rabs_pos_eq in Hu; [| left; exact Hpos].
      exact Hu.

    - unfold at_point; exact (eq_refl c).

    - intros x y Hx Hy; subst y.
      destruct Hx as [Hx_pos Hx_lt_A].
      assert (Hex_uc : ex_RInt (fun t => Rpower t a) x c).
      {
        apply ex_RInt_continuous with (f := fun t => Rpower t a) (a := x) (b := c).
        intros z Hz.
        destruct Hz as [Hz_low Hz_high].
        assert (Hmin_pos : 0 < Rmin x c) by (apply Rmin_glb_lt; [exact Hx_pos | exact Hc_pos]).
        assert (Hz_pos : 0 < z) by (apply Rlt_le_trans with (Rmin x c); [exact Hmin_pos | exact Hz_low]).
        apply continuity_pt_to_continuous.
        apply continuity_pt_Rpower_pos; [exact Ha | exact Hz_pos].
      }
      pose proof (RInt_correct (fun t => Rpower t a) x c Hex_uc) as H_RInt.
      exists (RInt (fun t => Rpower t a) x c).
      split.
      + exact H_RInt.
      + apply HA.
        * unfold ball, AbsRing_ball; simpl.
          unfold AbsRing_ball.
          simpl.
          rewrite Rminus_0_r.
          rewrite Rabs_pos_eq; [| left; exact Hx_pos].
          exact Hx_lt_A.
        * exact Hx_pos.
  }

  exists (I01 + (- Ic1)); exact H_gen.
Qed.

(* 伽马被积函数实部在[c,1]上的常义可积性 *)
Lemma f_integrable_c1 (s : Complex) (c : R) (Hre : 1 < ComplexNumbers.re s) (Hc_pos : 0 < c) (Hc_lt1 : c < 1) :
  let f := fun t : R => match Rlt_dec 0 t with left H => gamma_integrand_real s t H | right _ => 0 end in
  ex_RInt f c 1.
Proof.
  intros f.
  apply ex_RInt_continuous with (f := f) (a := c) (b := 1).
  intros z Hz.
  rewrite (Rmin_left c 1) in Hz by lra.
  rewrite (Rmax_right c 1) in Hz by lra.
  assert (Hz_pos : 0 < z) by (apply Rlt_le_trans with c; [exact Hc_pos | apply Hz]).
  unfold f.
  destruct (Rlt_dec 0 z) as [Hlt | Hnot]; [| contradiction].

  unfold gamma_integrand_real; simpl.
  unfold real_pow.
  set (exponent := ComplexNumbers.re s - 1).

  assert (Hder_ln : derivable_pt ln z) by apply derivable_pt_ln_manual, Hlt.
  assert (Hcont_ln : continuity_pt ln z) by apply derivable_continuous_pt, Hder_ln.

  assert (Hcont_scaled : continuity_pt (fun t => exponent * ln t) z).
  { apply continuity_pt_scal. exact Hcont_ln. }

  assert (Hder_exp_inner : derivable_pt exp (exponent * ln z)) by apply derivable_pt_exp.
  assert (Hcont_exp_inner : continuity_pt exp (exponent * ln z)) by apply derivable_continuous_pt, Hder_exp_inner.

  assert (Hcont_exp_comp : continuity_pt (fun t => exp (exponent * ln t)) z).
  { apply continuity_pt_comp with (f1 := fun t => exponent * ln t) (f2 := exp).
    - exact Hcont_scaled.
    - exact Hcont_exp_inner. }

  assert (Hcont_exp_neg : continuity_pt (fun t => exp (-t)) z).
  { apply continuity_pt_comp with (f1 := fun t => -t) (f2 := exp).
    - apply continuity_pt_opp. apply continuity_pt_id.
    - apply derivable_continuous_pt. apply derivable_pt_exp. }

  assert (Hcont_prod_pt : continuity_pt (fun t => exp (-t) * exp (exponent * ln t)) z).
  { apply continuity_pt_mult; assumption. }

  apply continuity_pt_to_continuous_simple in Hcont_prod_pt.

  set (g := fun t => exp (-t) * exp (exponent * ln t)).
  set (h := fun t => if Rlt_dec 0 t then g t else 0).

  assert (Hloc_eq : locally z (fun t => h t = g t)).
  {
    exists (mkposreal (z/2) (Rlt_mult_inv_pos z 2 Hlt Rlt_0_2)).
    intros t Hball.
    unfold h, g.
    destruct (Rlt_dec 0 t) as [Ht | Hf]; [reflexivity | ].
    exfalso.
    unfold ball, AbsRing_ball in Hball; simpl in Hball.
    apply Rabs_lt_between in Hball.
    destruct Hball as [Hlow Hhigh].
    unfold minus in *; simpl in *.
    unfold plus, opp in *; simpl in *.
    replace (t + - z) with (t - z) in * by ring.
    assert (Ht_gt_half : t > z/2) by lra.
    assert (Hz2_pos : 0 < z/2) by lra.
    assert (Ht_pos : 0 < t) by (apply Rlt_trans with (z/2); [exact Hz2_pos | apply Rlt_gt; exact Ht_gt_half]).
    apply Hf in Ht_pos; contradiction.
  }

  assert (Hloc_eq_sym : locally z (fun t => g t = h t)).
  { apply filter_imp with (P := fun t => h t = g t); [intros t Heq; symmetry; exact Heq | exact Hloc_eq]. }

  assert (Heq_gz_hz : g z = h z).
  {
    unfold h.
    destruct (Rlt_dec 0 z) as [Hpos | Hneg].
    - reflexivity.
    - contradict Hneg; exact Hlt.
  }

  assert (Hcont_prod_pt' : filterlim g (locally z) (locally (h z))) by (rewrite <- Heq_gz_hz; exact Hcont_prod_pt).

  exact (filterlim_ext_loc g h Hloc_eq_sym Hcont_prod_pt').
Qed.

Section GammaIntegrand0c.

(* 变量声明 *)
Variables (s : Complex) (c : R)
          (Hre : 1 < ComplexNumbers.re s)
          (Hc_pos : 0 < c)
          (Hc_lt1 : c < 1).

(* 定义 a *)
Let a := ComplexNumbers.re s - 1.
(* 定义 f *)
Let f := fun t : R =>
  match Rlt_dec 0 t with
  | left H => gamma_integrand_real s t H
  | right _ => 0
  end.
(* 定义 F *)
Let F := fun u : R =>
  if Rlt_dec 0 u then
    if Rlt_dec u c then RInt f u c else 0
  else 0.
(* 定义 S *)
Let S := fun x : R => exists u : R, 0 < u < c /\ x = F u.

(* 假设：幂函数在(0,c]上可积 *)
Hypothesis Rpower_integrable_0c :
  forall (a c : R), 0 < a -> 0 < c -> c < 1 ->
  ex_RInt_gen (fun t : R => Rpower t a) (at_right 0) (at_point c).

(* 假设：广义积分的柯西准则 *)
Hypothesis RInt_gen_cauchy_criterion :
  forall (g : R -> R) (I : R),
  is_RInt_gen g (at_right 0) (at_point c) I ->
  forall eps : R, eps > 0 ->
  exists delta : R, delta > 0 /\
    forall u1 u2 : R, 0 < u1 /\ u1 < u2 /\ u2 < delta ->
    Rabs (RInt g u1 u2) < eps.

(* 下确界定义 *)
Definition is_glb (S : R -> Prop) (I : R) : Prop :=
  (forall x : R, S x -> I <= x) /\
  (forall eps : R, eps > 0 -> exists x : R, S x /\ x < I + eps).

(* a 为正 *)
Local Lemma Ha : 0 < a.
Proof. unfold a; lra. Qed.

(* 函数界估计 *)
Lemma f_bound : forall t, 0 < t <= c -> Rabs (f t) <= Rpower t a.
Proof.
  intros t [Ht_pos Ht_le].
  unfold f.
  destruct (Rlt_dec 0 t) as [Hlt | Hnot]; [| contradiction].
  rewrite (proof_irrelevance _ Hlt Ht_pos).
  unfold gamma_integrand_real; simpl.
  rewrite Rabs_mult.
  assert (H1 : Rabs (exp (-t)) = exp (-t)).
  { apply Rabs_pos_eq, Rlt_le, exp_pos. }
  assert (H2 : Rabs (Rpower t (ComplexNumbers.re s - 1)) =
              Rpower t (ComplexNumbers.re s - 1)).
  { unfold Rpower; apply Rabs_pos_eq, Rlt_le, exp_pos. }
  rewrite H1, H2.
  unfold real_pow, Rpower.
  rewrite <- (Rmult_1_l (exp (a * ln t))).
  apply Rmult_le_compat_r.
  - apply Rlt_le, exp_pos.
  - assert (H_exp_lt_1 : exp (-t) < 1).
    { rewrite <- exp_0. apply exp_increasing. lra. }
    apply Rlt_le, H_exp_lt_1.
Qed.

(* f在(0,c]上连续 *)
Lemma f_continuous : forall t, 0 < t <= c -> continuous f t.
Proof.
  intros t [Ht_pos Ht_le].
  set (g := fun t0 : R => exp (-t0) * Rpower t0 a).
  assert (Hcont_g_pt : continuity_pt g t).
  {
    apply continuity_pt_mult.
    - apply continuity_pt_comp with (f1 := fun t0 : R => -t0) (f2 := exp).
      + apply continuity_pt_opp; apply continuity_pt_id.
      + apply derivable_continuous_pt; apply derivable_pt_exp_manual.
    - apply continuity_pt_Rpower_pos; [exact Ha | exact Ht_pos].
  }
  assert (Hcont_g : continuous g t) by
    (apply continuity_pt_to_continuous_simple; exact Hcont_g_pt).
  assert (Hdelta_pos : 0 < t / 2) by lra.
  assert (Hloc_eq' : locally t (fun y : R_UniformSpace => f y = g y)).
  {
    exists (mkposreal (t / 2) Hdelta_pos).
    intros y Hball.
    unfold f, g.
    unfold ball, AbsRing_ball in Hball; simpl in Hball.
    assert (Habs : Rabs (y - t) < t / 2) by exact Hball.
    assert (Hy_pos : 0 < y).
    { apply Rabs_lt_between in Habs; lra. }
    destruct (Rlt_dec 0 y) as [Hy_lt | Hnot]; [| contradiction].
    simpl.
    unfold gamma_integrand_real; simpl.
    unfold real_pow, Rpower; reflexivity.
  }
  assert (Hloc_eq_sym : locally t (fun y : R_UniformSpace => g y = f y)).
  {
    apply filter_imp with (P := fun y : R_UniformSpace => f y = g y).
    - intros y Heq. exact (eq_sym Heq).
    - exact Hloc_eq'.
  }
  apply (continuous_ext_loc f g t Hloc_eq_sym).
  exact Hcont_g.
Qed.

(* f在任意[u,c]上正常可积 *)
Lemma f_integrable_uc : forall u : R, 0 < u < c -> ex_RInt f u c.
Proof.
  intros u [Hu_pos Hu_lt_c].
  apply ex_RInt_continuous with (f := f) (a := u) (b := c).
  intros z Hz.
  rewrite (Rmin_left u c) in Hz by lra.
  rewrite (Rmax_right u c) in Hz by lra.
  apply f_continuous; split; [lra | lra].
Qed.

(* f非负性 *)
Lemma f_nonneg : forall t : R, 0 < t -> 0 <= f t.
Proof.
  intros t Ht_pos.
  unfold f.
  destruct (Rlt_dec 0 t) as [Hlt | Hnot]; [| contradiction].
  rewrite (proof_irrelevance _ Hlt Ht_pos).
  unfold gamma_integrand_real; simpl.
  unfold real_pow, Rpower.
  apply Rmult_le_pos.
  - apply Rlt_le, exp_pos.
  - apply Rlt_le, exp_pos.
Qed.

(* F的单调性 *)
Lemma F_mono : forall u1 u2 : R, (0 < u1 /\ u1 < u2 /\ u2 < c) -> F u2 <= F u1.
Proof.
  intros u1 u2 [Hu1_pos [Hu1_lt_u2 Hu2_lt_c]].
  unfold F.
  destruct (Rlt_dec 0 u1) as [H1|H1]; [| lra].
  destruct (Rlt_dec u1 c) as [H2|H2]; [| lra].
  destruct (Rlt_dec 0 u2) as [H3|H3]; [| lra].
  destruct (Rlt_dec u2 c) as [H4|H4]; [| lra].
  simpl.
  assert (Hex_u1u2 : ex_RInt f u1 u2).
  { apply ex_RInt_continuous with (f := f) (a := u1) (b := u2).
    intros z Hz.
    rewrite (Rmin_left u1 u2) in Hz by lra.
    rewrite (Rmax_right u1 u2) in Hz by lra.
    apply f_continuous; split; [lra | lra]. }
  assert (Hex_u2c : ex_RInt f u2 c).
  { apply f_integrable_uc; split; [lra | lra]. }
  pose proof (RInt_Chasles f u1 u2 c Hex_u1u2 Hex_u2c) as Hchasles.
  assert (Hnonneg : 0 <= RInt f u1 u2).
  { apply RInt_ge_0; [lra | exact Hex_u1u2 | intros t Ht; apply f_nonneg; destruct Ht as [Hlow Hhigh]; lra]. }

  assert (Hchasles' : RInt f u1 u2 + RInt f u2 c = RInt f u1 c).
  { rewrite <- Hchasles. unfold plus. reflexivity. }

  rewrite <- Hchasles'.
  apply Rplus_le_compat_l with (r := RInt f u2 c) in Hnonneg.
  rewrite Rplus_0_r in Hnonneg.
  rewrite Rplus_comm in Hnonneg.
  exact Hnonneg.
Qed.

(* F有下界0 *)
Lemma F_bound_below : forall u : R, 0 < u < c -> 0 <= F u.
Proof.
  intros u [Hu_pos Hu_lt_c].
  unfold F.
  destruct (Rlt_dec 0 u) as [H1|H1]; [| lra].
  destruct (Rlt_dec u c) as [H2|H2]; [| lra].
  simpl.
  apply RInt_ge_0; [lra | apply f_integrable_uc; split; lra |].
  intros t Ht.
  apply f_nonneg.
  lra.
Qed.

(* F满足柯西收敛准则 *)
Lemma F_cauchy : forall eps : R, eps > 0 ->
  exists delta : R, delta > 0 /\
    forall u1 u2 : R, 0 < u1 /\ u1 < u2 /\ u2 < delta ->
    Rabs (F u1 - F u2) < eps.
Proof.
  intros eps Heps.
  assert (H_Rpower_integrable : ex_RInt_gen (fun t : R => Rpower t a) (at_right 0) (at_point c)).
  { apply Rpower_integrable_0c; [exact Ha | exact Hc_pos | exact Hc_lt1]. }
  destruct H_Rpower_integrable as [I_Rpower Hgen_Rpower].
  pose proof (RInt_gen_cauchy_criterion (fun t : R => Rpower t a) I_Rpower Hgen_Rpower eps Heps)
    as [delta [Hdelta_pos Hdelta]].
  exists (Rmin delta c).
  split.
  - apply Rmin_pos; [exact Hdelta_pos | exact Hc_pos].
  - intros u1 u2 [Hu1_pos [Hu1_lt_u2 Hu2_lt_delta]].
    assert (Hu2_lt_c : u2 < c) by (apply Rlt_le_trans with (Rmin delta c); [exact Hu2_lt_delta | apply Rmin_r]).
    assert (Hu1_lt_c : u1 < c) by lra.
    assert (Hu2_lt_delta0 : u2 < delta) by (apply Rlt_le_trans with (Rmin delta c); [exact Hu2_lt_delta | apply Rmin_l]).
    unfold F.
    destruct (Rlt_dec 0 u1) as [H1|H1]; [| lra].
    destruct (Rlt_dec u1 c) as [H2|H2]; [| lra].
    destruct (Rlt_dec 0 u2) as [H3|H3]; [| lra].
    destruct (Rlt_dec u2 c) as [H4|H4]; [| lra].
    simpl.
    assert (Hex_u1u2 : ex_RInt f u1 u2).
    {
      apply ex_RInt_continuous with (f := f) (a := u1) (b := u2).
      intros z Hz.
      rewrite (Rmin_left u1 u2) in Hz by lra.
      rewrite (Rmax_right u1 u2) in Hz by lra.
      apply f_continuous; split; [lra | lra].
    }
    assert (Hex_u2c : ex_RInt f u2 c).
    {
      apply ex_RInt_continuous with (f := f) (a := u2) (b := c).
      intros z Hz.
      rewrite (Rmin_left u2 c) in Hz by lra.
      rewrite (Rmax_right u2 c) in Hz by lra.
      apply f_continuous; split; [lra | lra].
    }
    pose proof (RInt_Chasles f u1 u2 c Hex_u1u2 Hex_u2c) as Hchasles.
    assert (Hdiff : RInt f u1 c - RInt f u2 c = RInt f u1 u2).
    {
      rewrite <- Hchasles.
      unfold plus, minus, opp in *.
      simpl.
      ring.
    }
    rewrite Hdiff.
    assert (Hex_Rpower_u1u2 : ex_RInt (fun t : R => Rpower t a) u1 u2).
    {
      apply ex_RInt_continuous with (f := fun t : R => Rpower t a) (a := u1) (b := u2).
      intros z Hz.
      rewrite (Rmin_left u1 u2) in Hz by lra.
      rewrite (Rmax_right u1 u2) in Hz by lra.
      apply continuity_pt_to_continuous_simple.
      apply continuity_pt_Rpower_pos; [exact Ha | lra].
    }
    assert (Hf_le_Rpower : forall t, u1 <= t <= u2 -> f t <= Rpower t a).
    {
      intros t Ht.
      assert (Ht_pos : 0 < t) by lra.
      assert (Ht_le_c : t <= c) by lra.
      pose proof (f_bound t (conj Ht_pos Ht_le_c)) as Hbound_t.
      assert (Hf_nonneg_t : 0 <= f t) by apply f_nonneg, Ht_pos.
      rewrite Rabs_pos_eq in Hbound_t; [| exact Hf_nonneg_t].
      exact Hbound_t.
    }
    assert (Hf_nonneg_int : 0 <= RInt f u1 u2).
    {
      apply RInt_ge_0; [lra | exact Hex_u1u2 |].
      intros t Ht.
      apply f_nonneg; lra.
    }
    assert (HRpower_nonneg_int : 0 <= RInt (fun t : R => Rpower t a) u1 u2).
    {
      apply RInt_ge_0; [lra | exact Hex_Rpower_u1u2 |].
      intros t Ht.
      apply Rlt_le, Rpower_pos; lra.
    }
    assert (Hint_le : RInt f u1 u2 <= RInt (fun t : R => Rpower t a) u1 u2).
    {
      apply RInt_le; [lra | exact Hex_u1u2 | exact Hex_Rpower_u1u2 |].
      intros t Ht.
      apply Hf_le_Rpower.
      split; [apply Rlt_le, Ht | apply Rlt_le, Ht].
    }
    rewrite Rabs_pos_eq; [| exact Hf_nonneg_int].
    apply Rle_lt_trans with (RInt (fun t : R => Rpower t a) u1 u2); [exact Hint_le |].
    rewrite <- (Rabs_pos_eq (RInt (fun t : R => Rpower t a) u1 u2) HRpower_nonneg_int).
    apply Hdelta; split; [exact Hu1_pos | split; [exact Hu1_lt_u2 | exact Hu2_lt_delta0]].
Qed.

(* 集合S非空且有下界 *)

(* 上确界定义 *)
Definition is_lub (S : R -> Prop) (I : R) : Prop :=
  (forall x : R, S x -> x <= I) /\
  (forall eps : R, eps > 0 -> exists x : R, S x /\ x > I - eps).

(* 收敛到上确界 *)
Lemma F_limit_to_lub_at_0 (I : R) (HI : is_lub S I) :
  filterlim F (at_right 0) (locally I).
Proof.
  intros P [eps Heps].
  destruct HI as [Hub Hmin_ub].

  destruct (Hmin_ub (pos eps) (cond_pos eps)) as [x0 [Hx0_S Hx0_gt]].
  destruct Hx0_S as [u0 [Hu0_range Hx0_eq]].
  destruct Hu0_range as [Hu0_pos Hu0_lt_c].
  rewrite Hx0_eq in Hx0_gt.

  set (delta := u0).
  assert (Hdelta_pos : 0 < delta) by (unfold delta; lra).

  assert (H_main : forall (u : R), 0 < u < delta -> Rabs (F u - I) < pos eps).
  {
    intros u [Hu_pos Hu_lt_delta].
    unfold delta in Hu_lt_delta.
    assert (Hu_lt_u0 : u < u0) by lra.
    assert (Hu_in_domain : 0 < u /\ u < c) by (split; lra).

    assert (H_mono_prem : 0 < u /\ u < u0 /\ u0 < c).
    { split; [exact Hu_pos | split; [exact Hu_lt_u0 | exact Hu0_lt_c]]. }
    assert (H_F_ge : F u0 <= F u) by (apply F_mono; exact H_mono_prem).

    assert (H_F_le : F u <= I).
    { apply Hub; unfold S; exists u; split; [exact Hu_in_domain | reflexivity]. }

    assert (H_abs_eq : Rabs (F u - I) = I - F u).
    {
      rewrite Rabs_minus_sym.
      apply Rabs_pos_eq; lra.
    }
    rewrite H_abs_eq.
    lra.
  }

  unfold at_right, within.
  exists (mkposreal delta Hdelta_pos).
  intros u Hu_in_ball Hu_pos.

  assert (Hu_lt_delta : u < delta).
  {
    unfold ball, AbsRing_ball, Rdist, R_met in Hu_in_ball.
    simpl in Hu_in_ball.
    apply Rabs_lt_between in Hu_in_ball.
    destruct Hu_in_ball as [Hlow Hhigh].
    simpl in Hlow, Hhigh.
    rewrite Rminus_0_r in Hhigh.
    exact Hhigh.
  }

  assert (H_range : 0 < u < delta) by (split; [exact Hu_pos | exact Hu_lt_delta]).

  specialize (H_main u H_range).

  apply Heps.
  unfold AbsRing_ball, ball, Rdist, R_met.
  simpl.
  exact H_main.
Qed.

(* F在u→0⁺时收敛到下确界I *)
Lemma F_limit_to_glb (I : R) (HI : is_glb S I) :
  (exists K, forall u, 0 < u < c -> F u = K) ->
  filterlim F (at_right 0) (locally I).
Proof.
  intros Hconst P [eps Heps].
  destruct Hconst as [K Hconst].

  assert (I = K).
  {
    destruct HI as [Hlb Hglb].

    assert (Hc2 : 0 < c/2 < c) by (split; lra).
    specialize (Hconst (c/2) Hc2) as Heq.
    assert (HS_K : S K) by (exists (c/2); split; [exact Hc2 | symmetry; exact Heq]).

    apply Hlb in HS_K as Hle1.

    assert (Hle2 : K <= I).
    {
      destruct (Rlt_le_dec I K) as [Hlt | Hge].
      - set (eps0 := K - I).
        assert (Heps0 : eps0 > 0) by (apply Rlt_0_minus; exact Hlt).
        destruct (Hglb eps0 Heps0) as [x [Hx_S Hx_lt]].
        destruct Hx_S as [u [Hu Hx_eq]].
        rewrite Hx_eq in Hx_lt.
        rewrite Hconst in Hx_lt; [| exact Hu].
        simpl in Hx_lt.
        assert (H_sum : I + eps0 = K) by (unfold eps0; ring).
        rewrite H_sum in Hx_lt.
        exfalso; apply (Rlt_irrefl K); exact Hx_lt.
      - auto.
    }

    apply Rle_antisym; [exact Hle1 | exact Hle2].
  }
  subst K.

  unfold at_right, within.
  exists (mkposreal c Hc_pos).
  intros u Hu_ball Hu_pos.
  simpl in Hu_ball.
  assert (Hu_lt_c : u < c).
  {
    apply Rabs_lt_between in Hu_ball.
    destruct Hu_ball as [_ Hhigh].
    rewrite Rminus_0_r in Hhigh.
    exact Hhigh.
  }
  assert (F u = I) by (apply Hconst; split; lra).
  rewrite H.
  apply Heps.
  apply ball_center.
Qed.

(* 从极限推出广义可积性 *)
Lemma main_is_RInt_gen (I : R)
  (HI : is_glb S I)
  (Hlim : filterlim F (at_right 0) (locally I)) :
  is_RInt_gen f (at_right 0) (at_point c) I.
Proof.
  unfold is_RInt_gen.
  intros P HP.
  specialize (Hlim P HP) as [delta Hdelta].
  set (d := pos delta).
  set (A := fun u : R => 0 < u < d /\ u < c).
  set (B := fun y : R => y = c).

  assert (HA : at_right 0 A).
  {
    unfold at_right, within.
    assert (Hc_half : 0 < c/2).
    { apply Rmult_lt_0_compat; [exact Hc_pos | apply Rinv_0_lt_compat; apply Rlt_0_2]. }
    exists (mkposreal (Rmin d (c/2)) (Rmin_pos d (c/2) (cond_pos delta) Hc_half)).
    intros u Hu_ball Hu_pos.
    simpl in Hu_ball.
    apply Rabs_lt_between in Hu_ball.
    destruct Hu_ball as [_ Hu_lt_radius].
    rewrite Rminus_0_r in Hu_lt_radius.
    split.
    - split; [exact Hu_pos | apply Rlt_le_trans with (Rmin d (c/2)); [exact Hu_lt_radius | apply Rmin_l]].
    - apply Rlt_le_trans with (Rmin d (c/2)); [exact Hu_lt_radius | apply Rle_trans with (c/2); [apply Rmin_r | lra]].
  }

  assert (HB : at_point c B) by (unfold at_point; reflexivity).
  apply Filter_prod with (Q := A) (R := B); [exact HA | exact HB |].
  intros u v Hu Hv.
  assert (Heq : v = c) by exact Hv.
  subst v.
  destruct Hu as [Hu_cond Hu_lt_c].
  destruct Hu_cond as [Hu_pos Hu_lt_d].

  assert (F_u_eq : F u = RInt f u c).
  {
    unfold F.
    destruct (Rlt_dec 0 u) as [Hlt | Hnot].
    - destruct (Rlt_dec u c) as [Hltc | Hnotc].
      + reflexivity.
      + exfalso; apply Hnotc; exact Hu_lt_c.
    - exfalso; apply Hnot; exact Hu_pos.
  }

  assert (Hf : ex_RInt f u c) by (apply f_integrable_uc; split; lra).

  assert (Hd : (d : R) = delta).
  { reflexivity. }
  assert (Habs : Rabs u < delta).
  { assert (Hpos : 0 < u) by exact Hu_pos.
    assert (Hlt : u < (d : R)) by exact Hu_lt_d.
    assert (H1 : (d : R) = delta) by exact Hd.
    assert (H2 : u < delta) by lra.
    assert (H3 : Rabs u = u).
    { apply Rabs_right; lra. }
    rewrite H3.
    lra. }
  assert (H_eq1 : norm (minus u 0) = Rabs (u - 0)).
  { reflexivity. }
  assert (H_eq2 : u - 0 = u).
  { ring. }
  assert (H_eq3 : Rabs (u - 0) = Rabs u).
  { rewrite H_eq2; reflexivity. }
  assert (H_main : norm (minus u 0) < delta).
  { rewrite H_eq1.
    rewrite H_eq3.
    exact Habs. }
  assert (Hball : ball 0 delta u).
  { apply (@norm_compat1 R_AbsRing R_CompleteNormedModule 0 u delta).
    exact H_main. }

  assert (H_P_Fu : P (F u)).
  { apply Hdelta.
    - exact Hball.
    - exact Hu_pos. }

  assert (H_P_RInt : P (RInt f u c)).
  { rewrite <- F_u_eq.
    exact H_P_Fu. }

  destruct Hf as [y Hfy].
  exists y.
  split.
  - simpl.
    exact Hfy.
  - assert (H_RInt_eq : RInt f u c = y).
    { apply (is_RInt_unique f u c y Hfy). }
    rewrite H_RInt_eq in H_P_RInt.
    exact H_P_RInt.
Qed.

(* 定理：伽马被积函数在(0,c]上的广义积分存在 *)
Theorem f_integrable_0c :
  let f := fun t : R => match Rlt_dec 0 t with left H => gamma_integrand_real s t H | right _ => 0 end in
  ex_RInt_gen f (at_right 0) (at_point c).
Proof.
  assert (H_cauchy : cauchy (filtermap F (at_right 0))).
  {
    unfold cauchy.
    intros eps.
    destruct (F_cauchy (pos eps) (cond_pos eps)) as [delta [Hdelta_pos Hdelta]].
    set (u0 := delta / 2).
    assert (Hu0_pos : 0 < u0) by (unfold u0; apply Rlt_mult_inv_pos; [exact Hdelta_pos | lra]).
    assert (Hu0_lt_delta : u0 < delta) by (unfold u0; lra).
    exists (F u0).
    unfold filtermap; simpl.
    apply (filter_imp (fun u => 0 < u < delta) (fun u => ball (F u0) eps (F u))).
    - intros u Hu.
      destruct (Rle_dec u u0) as [Hle | Hle'].
      + destruct (Rle_lt_or_eq_dec u u0 Hle) as [Hult | Heq].
        * assert (Hcase : 0 < u /\ u < u0 < delta)
            by (split; [exact (proj1 Hu) | split; [exact Hult | exact Hu0_lt_delta]]).
          specialize (Hdelta u u0 Hcase).
          unfold ball, AbsRing_ball; simpl; exact Hdelta.
        * subst u; apply ball_center.
      + assert (Hult : u0 < u) by (apply Rnot_le_lt; exact Hle').
        assert (Hcase : 0 < u0 /\ u0 < u < delta)
          by (split; [exact Hu0_pos | split; [exact Hult | exact (proj2 Hu)]]).
        specialize (Hdelta u0 u Hcase).
        unfold ball, AbsRing_ball; simpl; unfold AbsRing_ball; rewrite Rabs_minus_sym; exact Hdelta.
    - exists (mkposreal delta Hdelta_pos).
      intros u Hu_ball Hu_pos.
      split; [exact Hu_pos |].
      apply Rabs_lt_between in Hu_ball; destruct Hu_ball as [_ Hhigh]; rewrite Rminus_0_r in Hhigh; exact Hhigh.
  }

  assert (H_proper : ProperFilter (filtermap F (at_right 0))).
  { apply filtermap_proper_filter. exact (at_right_proper_filter 0). }

  set (L := lim (filtermap F (at_right 0))).
  assert (Hlim : filterlim F (at_right 0) (locally L)).
  {
    intros P [eps Heps].
    pose proof (complete_cauchy (filtermap F (at_right 0)) H_proper H_cauchy eps) as Hball.
    unfold filtermap in Hball; simpl in Hball.
    apply filter_imp with (2 := Hball).
    intros u Hu. apply Heps. exact Hu.
  }

  assert (H_RInt_gen : is_RInt_gen f (at_right 0) (at_point c) L).
  {
    unfold is_RInt_gen.
    intros P HP.
    specialize (Hlim P HP) as [delta Hdelta].
    set (d := pos delta).
    set (A := fun u : R => 0 < u < d /\ u < c).
    set (B := fun y : R => y = c).

    assert (HA : at_right 0 A).
    {
      unfold at_right, within.
      assert (Hc_half : 0 < c/2).
      { apply Rmult_lt_0_compat; [exact Hc_pos | apply Rinv_0_lt_compat; apply Rlt_0_2]. }
      exists (mkposreal (Rmin d (c/2)) (Rmin_pos d (c/2) (cond_pos delta) Hc_half)).
      intros u Hu_ball Hu_pos.
      simpl in Hu_ball.
      apply Rabs_lt_between in Hu_ball.
      destruct Hu_ball as [_ Hu_lt_radius].
      rewrite Rminus_0_r in Hu_lt_radius.
      split.
      - split; [exact Hu_pos | apply Rlt_le_trans with (Rmin d (c/2)); [exact Hu_lt_radius | apply Rmin_l]].
      - apply Rlt_le_trans with (Rmin d (c/2)); [exact Hu_lt_radius | apply Rle_trans with (c/2); [apply Rmin_r | lra]].
    }

    assert (HB : at_point c B) by (unfold at_point; reflexivity).
    apply Filter_prod with (Q := A) (R := B); [exact HA | exact HB |].
    intros u v Hu Hv.
    assert (Heq : v = c) by exact Hv.
    subst v.
    destruct Hu as [Hu_cond Hu_lt_c].
    destruct Hu_cond as [Hu_pos Hu_lt_d].

    assert (F_u_eq : F u = RInt f u c).
    {
      unfold F.
      destruct (Rlt_dec 0 u) as [Hlt | Hnot].
      - destruct (Rlt_dec u c) as [Hltc | Hnotc].
        + reflexivity.
        + exfalso; apply Hnotc; exact Hu_lt_c.
      - exfalso; apply Hnot; exact Hu_pos.
    }

    assert (Hf : ex_RInt f u c) by (apply f_integrable_uc; split; lra).

    assert (Hd : (d : R) = delta).
    { reflexivity. }
    assert (Habs : Rabs u < delta).
    { assert (Hpos : 0 < u) by exact Hu_pos.
      assert (Hlt : u < (d : R)) by exact Hu_lt_d.
      assert (H1 : (d : R) = delta) by exact Hd.
      assert (H2 : u < delta) by lra.
      assert (H3 : Rabs u = u).
      { apply Rabs_right; lra. }
      rewrite H3.
      lra. }
    assert (H_eq1 : norm (minus u 0) = Rabs (u - 0)).
    { reflexivity. }
    assert (H_eq2 : u - 0 = u).
    { ring. }
    assert (H_eq3 : Rabs (u - 0) = Rabs u).
    { rewrite H_eq2; reflexivity. }
    assert (H_main : norm (minus u 0) < delta).
    { rewrite H_eq1.
      rewrite H_eq3.
      exact Habs. }
    assert (Hball : ball 0 delta u).
    { apply (@norm_compat1 R_AbsRing R_CompleteNormedModule 0 u delta).
      exact H_main. }

    assert (H_P_Fu : P (F u)).
    { apply Hdelta.
      - exact Hball.
      - exact Hu_pos. }

    assert (H_P_RInt : P (RInt f u c)).
    { rewrite <- F_u_eq.
      exact H_P_Fu. }

    destruct Hf as [y Hfy].
    exists y.
    split.
    - simpl.
      exact Hfy.
    - assert (H_RInt_eq : RInt f u c = y).
      { apply (is_RInt_unique f u c y Hfy). }
      rewrite H_RInt_eq in H_P_RInt.
      exact H_P_RInt.
  }

  exact (ex_intro _ L H_RInt_gen).
Qed.

End GammaIntegrand0c.

(* 加法交换律 *)

Section IntegralLemmas.
  (* 公共变量和假设 *)
  Variable a c I_Rpower : R.
  Variable f : R -> R.
  Hypothesis Ha : -1 < a.
  Hypothesis Hc_pos : 0 < c.
  Hypothesis Hf_nonneg : forall t, 0 < t -> 0 <= f t.
  Hypothesis H_bound : forall t, 0 < t <= c -> f t <= Rpower t a.
  Hypothesis H_f_integrable_uc : forall u, 0 < u < c -> ex_RInt f u c.
  Hypothesis Hgen_Rpower : is_RInt_gen (fun t => Rpower t a) (at_right 0) (at_point c) I_Rpower.
  Hypothesis ex_RInt_restrict : forall (f : R -> R) (a b c : R),
      a <= b <= c -> ex_RInt f a c -> ex_RInt f a b.

(* Rpower 在正数上连续 *)
Hypothesis H_Rpower_continuous : forall x, 0 < x -> continuity_pt (fun t => Rpower t a) x.

(* F 递减性 *)
Lemma F_decreasing :
  forall u v : R,
    0 < u /\ u < v /\ v < c ->
    RInt f v c <= RInt f u c.
Proof.
  intros u v (Huv_pos & Huv_lt & Hv_lt_c).
  assert (Hex_f_uv : ex_RInt f u v).
  { apply ex_RInt_restrict with (c := c); [lra | apply H_f_integrable_uc; lra]. }
  assert (Hchasles : RInt f u c = RInt f u v + RInt f v c).
  {
    symmetry.
    apply (RInt_Chasles f u v c).
    - exact Hex_f_uv.
    - apply H_f_integrable_uc. split; [lra | exact Hv_lt_c].
  }
  assert (H_nonneg_uv : 0 <= RInt f u v).
  { apply RInt_ge_0; [lra | exact Hex_f_uv | intros t Ht; apply Hf_nonneg; lra]. }
  lra.
Qed.

(* Rmin 正性 *)
Lemma Rmin_pos : forall x y, 0 < x -> 0 < y -> 0 < Rmin x y.
Proof.
  intros x y Hx Hy.
  unfold Rmin; case (Rle_dec x y); intro; [exact Hx | exact Hy].
Qed.

(* 连续点蕴含连续 *)
Lemma continuity_pt_continuous (f1 : R -> R) (x : R) : continuity_pt f x -> continuous f x.
Proof.
  intros H.
  apply continuity_pt_filterlim.
  apply H.
Qed.

(* Rpower 积分递减 *)
Lemma Rpower_integral_decreasing :
  let G := fun v : R => RInt (fun t : R => Rpower t a) v c in
  forall v1 v2 : R,
    0 < v1 /\ v1 < v2 /\ v2 < c ->
    G v2 <= G v1.
Proof.
  intros G v1 v2 (Hv1_pos & Hv1_lt_v2 & Hv2_lt_c).
  unfold G.
  assert (Hv2_pos : 0 < v2) by lra.
  assert (Hv1_lt_c : v1 < c) by lra.
  assert (Hv2_lt_c' : v2 < c) by lra.

  assert (H_Rpower_pos : forall t, 0 < t -> 0 < Rpower t a).
  { intros t Ht. unfold Rpower. apply exp_pos. }

  assert (cont_Rpower : forall x, 0 < x -> continuity_pt (fun t => Rpower t a) x)
    by exact H_Rpower_continuous.

  assert (H_cont_v1 : forall x, v1 <= x <= c -> continuity_pt (fun t => Rpower t a) x).
  { intros x (Hx1, Hx2). apply cont_Rpower. apply Rlt_le_trans with v1; [exact Hv1_pos | exact Hx1]. }
  assert (H_cont_v1' : forall x, v1 <= x <= c -> continuous (fun t => Rpower t a) x).
  { intros x Hx. apply continuity_pt_filterlim. apply H_cont_v1; exact Hx. }

  assert (Hex_v1_c : ex_RInt (fun t => Rpower t a) v1 c).
  { apply (@ex_RInt_continuous R_CompleteNormedModule (fun t => Rpower t a) v1 c).
    intros z Hz.
    apply H_cont_v1'.
    unfold Rmin, Rmax in Hz.
    destruct (Rle_dec v1 c) as [Hle|Hgt]; [|lra].
    simpl in Hz; split; lra. }

  assert (H_cont_v2 : forall x, v2 <= x <= c -> continuity_pt (fun t => Rpower t a) x).
  { intros x (Hx1, Hx2). apply cont_Rpower. apply Rlt_le_trans with v2; [exact Hv2_pos | exact Hx1]. }
  assert (H_cont_v2' : forall x, v2 <= x <= c -> continuous (fun t => Rpower t a) x).
  { intros x Hx. apply continuity_pt_filterlim. apply H_cont_v2; exact Hx. }
  assert (Hex_v2_c : ex_RInt (fun t => Rpower t a) v2 c).
  { apply (@ex_RInt_continuous R_CompleteNormedModule (fun t => Rpower t a) v2 c).
    intros z Hz.
    apply H_cont_v2'.
    unfold Rmin, Rmax in Hz.
    destruct (Rle_dec v2 c) as [Hle|Hgt]; [|lra].
    simpl in Hz; split; lra. }

  assert (Hex_v1_v2 : ex_RInt (fun t => Rpower t a) v1 v2).
  {
    apply ex_RInt_restrict with (c := c).
    - split; [lra | lra].
    - exact Hex_v1_c.
  }

  assert (H_chasles : RInt (fun t => Rpower t a) v1 c =
                      RInt (fun t => Rpower t a) v1 v2 + RInt (fun t => Rpower t a) v2 c).
  {
    symmetry.
    apply RInt_Chasles with (f := fun t => Rpower t a) (a := v1) (b := v2) (c := c).
    - exact Hex_v1_v2.
    - exact Hex_v2_c.
  }

  assert (H_nonneg_v1v2 : 0 <= RInt (fun t => Rpower t a) v1 v2).
  {
    apply RInt_ge_0; [lra | exact Hex_v1_v2 |].
    intros t Ht; destruct Ht as (Ht1, Ht2).
    apply Rlt_le, H_Rpower_pos; lra.
  }

  lra.
Qed.

(* Rpower 在正区间上可积 *)
Lemma Rpower_integrable_on_pos : forall v, 0 < v < c -> ex_RInt (fun t => Rpower t a) v c.
Proof.
  intros v (Hv_pos, Hv_lt_c).
  apply (@ex_RInt_continuous R_CompleteNormedModule (fun t => Rpower t a) v c).
  intros z Hz.
  unfold Rmin, Rmax in Hz.
  destruct (Rle_dec v c) as [Hle|Hgt]; [|lra].
  simpl in Hz.
  destruct Hz as [Hz1 Hz2].
  assert (Hz_pos : 0 < z) by (apply Rlt_le_trans with v; [exact Hv_pos | exact Hz1]).
  apply continuity_pt_filterlim.
  apply H_Rpower_continuous.
  exact Hz_pos.
Qed.

(* 广义积分滤子极限 *)
Lemma is_RInt_gen_filterlim : forall (f : R -> R) (Fa Fb : (R -> Prop) -> Prop) (l : R),
  Filter Fa ->
  Filter Fb ->
  is_RInt_gen f Fa Fb l ->
  filterlim (fun ab : R * R => RInt f (fst ab) (snd ab)) (filter_prod Fa Fb) (locally l).
Proof.
  intros g Fa Fb l HFa HFb H_is_RInt_gen.

  unfold filterlim.
  intros P HP.

  specialize (H_is_RInt_gen P HP) as H_filtermapi.

  assert (H_impl : forall x : R * R,
    (exists y : R, is_RInt g (fst x) (snd x) y /\ P y) ->
    P (RInt g (fst x) (snd x))).
  {
    intros x [y [H_is_RInt_y H_P_y]].
    assert (H_eq : RInt g (fst x) (snd x) = y) by (apply is_RInt_unique; exact H_is_RInt_y).
    assert (H_eq_sym : y = RInt g (fst x) (snd x)) by (symmetry; exact H_eq).
    rewrite H_eq_sym in H_P_y.
    exact H_P_y.
  }

  assert (H_filter_prod : Filter (filter_prod Fa Fb)).
  {
    apply filter_prod_filter.
    - exact HFa.
    - exact HFb.
  }

  exact (@filter_imp (R * R) (filter_prod Fa Fb) H_filter_prod
           (fun x : R * R => exists y : R, is_RInt g (fst x) (snd x) y /\ P y)
           (fun x : R * R => P (RInt g (fst x) (snd x)))
           H_impl H_filtermapi).
Qed.

(* F 的上界 I_Rpower *)
Lemma F_upper_bound :
  forall u : R,
    0 < u < c ->
    RInt f u c <= I_Rpower.
Proof.
  intros u [Hu_pos Hu_lt_c].
  set (G := fun v : R => RInt (fun t : R => Rpower t a) v c).

  assert (H_cont_u : forall x, u <= x <= c -> continuous (fun t : R => Rpower t a) x).
  {
    intros x (Hx1, Hx2).
    apply continuity_pt_filterlim.
    apply H_Rpower_continuous.
    lra.
  }
  assert (Hex_Rpower_uc : ex_RInt (fun t : R => Rpower t a) u c).
  {
    apply (@ex_RInt_continuous R_CompleteNormedModule (fun t : R => Rpower t a) u c).
    intros z Hz.
    apply H_cont_u.
    unfold Rmin, Rmax in Hz.
    destruct (Rle_dec u c) as [Hle|Hgt]; [|lra].
    simpl in Hz; split; lra.
  }

  assert (H_int_le_u : RInt f u c <= G u).
  {
    apply RInt_le with (f := f) (g := fun t : R => Rpower t a) (a := u) (b := c); try lra.
    - apply H_f_integrable_uc; split; [exact Hu_pos | exact Hu_lt_c].
    - exact Hex_Rpower_uc.
    - intros t Ht.
      apply H_bound; lra.
  }

  assert (H_G_monotone : forall v1 v2 : R, 0 < v1 <= v2 -> v2 < c -> G v1 >= G v2).
  {
    intros v1 v2 Hv12 Hv2_lt_c.
    assert (Hv1_pos : 0 < v1) by lra.
    assert (Hv2_pos : 0 < v2) by lra.
    assert (H_v1_le_v2 : v1 <= v2) by lra.
    assert (Hmin : Rmin v1 v2 = v1) by (apply Rmin_left; exact H_v1_le_v2).
    assert (Hmax : Rmax v1 v2 = v2) by (apply Rmax_right; exact H_v1_le_v2).

    assert (Hex1 : ex_RInt (fun t : R => Rpower t a) v1 v2).
    {
      apply (@ex_RInt_continuous R_CompleteNormedModule (fun t : R => Rpower t a) v1 v2).
      intros x (Hx1, Hx2).
      rewrite Hmin in Hx1; rewrite Hmax in Hx2.
      apply continuity_pt_filterlim.
      apply H_Rpower_continuous.
      lra.
    }
    assert (Hex2 : ex_RInt (fun t : R => Rpower t a) v2 c).
    {
      apply (@ex_RInt_continuous R_CompleteNormedModule (fun t : R => Rpower t a) v2 c).
      intros x (Hx1, Hx2).
      assert (Hmin2 : Rmin v2 c = v2) by (apply Rmin_left; lra).
      assert (Hmax2 : Rmax v2 c = c) by (apply Rmax_right; lra).
      rewrite Hmin2 in Hx1; rewrite Hmax2 in Hx2.
      apply continuity_pt_filterlim.
      apply H_Rpower_continuous.
      lra.
    }
    assert (H_chasles : G v1 = RInt (fun t : R => Rpower t a) v1 v2 + G v2).
    {
      unfold G.
      symmetry.
      apply RInt_Chasles with (f := fun t : R => Rpower t a) (a := v1) (b := v2) (c := c).
      - exact Hex1.
      - exact Hex2.
    }
    assert (H_nonneg : 0 <= RInt (fun t : R => Rpower t a) v1 v2).
    {
      apply RInt_ge_0; [lra | exact Hex1 |].
      intros t Ht.
      apply Rlt_le, exp_pos.
    }
    lra.
  }
  
  assert (HFa : Filter (at_right 0)).
  {
    exact filter_filter.
  }

  assert (HFb : Filter (at_point c)).
  {
    exact filter_filter.
  }

  assert (Hfilterlim_prod : filterlim (fun ab : R * R => RInt (fun t : R => Rpower t a) (fst ab) (snd ab))
                                      (filter_prod (at_right 0) (at_point c))
                                      (locally I_Rpower)).
  {
    apply is_RInt_gen_filterlim with (f := fun t : R => Rpower t a) (Fa := at_right 0) (Fb := at_point c) (l := I_Rpower); assumption.
  }

  assert (Hfilterlim : filterlim G (at_right 0) (locally I_Rpower)).
  {
    unfold filterlim in *.
    intros P HP.
    specialize (Hfilterlim_prod P HP).
    inversion Hfilterlim_prod as [Q R' HQ HR' Himp].
    simpl in HR'.
    assert (H_main_impl : forall (x : R), Q x -> P (G x)).
    {
      intros x Hx.
      unfold G.
      simpl in *.
      exact (Himp x c Hx HR').
    }
    exact (@filter_imp R (at_right 0) HFa Q (fun v : R => P (G v)) H_main_impl HQ).
  }

  assert (H_main : G u <= I_Rpower).
  {
    apply Rnot_lt_le.
    intro H_contra.
    
    assert (H_eps_pos : 0 < (G u - I_Rpower) / 2) by lra.
    set (eps := (G u - I_Rpower) / 2) in *.
    
    assert (H_ball : at_right 0 (fun v : R => Rabs (G v - I_Rpower) < eps)).
    {
      pose proof (@filterlim_locally_ball_norm R_AbsRing R R_CompleteNormedModule (at_right 0) HFa G I_Rpower) as H_iff.
      destruct H_iff as [H_impl _].
      pose proof (H_impl Hfilterlim) as H_forall_eps.
      pose proof (H_forall_eps (mkposreal eps H_eps_pos)) as H_spec.
      assert (H_ball_equiv : forall x : R, ball_norm I_Rpower (mkposreal eps H_eps_pos) (G x) <-> Rabs (G x - I_Rpower) < eps).
      {
        intros x; reflexivity.
      }
      assert (H_imp : forall x : R, ball_norm I_Rpower (mkposreal eps H_eps_pos) (G x) -> Rabs (G x - I_Rpower) < eps).
      {
        intros x Hx.
        destruct (H_ball_equiv x) as [H1 H2].
        apply H2.
        exact Hx.
      }
      exact (@filter_imp R (at_right 0) HFa
        (fun x : R => ball_norm I_Rpower (mkposreal eps H_eps_pos) (G x))
        (fun v : R => Rabs (G v - I_Rpower) < eps)
        H_imp
        H_spec).
    }
    
    unfold at_right, within in H_ball.
    set (Q := (fun v : R => 0 < v -> Rabs (G v - I_Rpower) < eps)) in *.
    
    assert (H_dec_Q : forall x0 : R, Q x0 \/ ~ Q x0).
    {
      intros x0; unfold Q; tauto.
    }
    assert (H_exists_delta : {d : posreal | forall y : R, ball 0 d y -> Q y}).
    {
      apply locally_ex_dec with (x := 0) (P := Q).
      - exact H_dec_Q.
      - exact H_ball.
    }
    destruct H_exists_delta as [delta_eps Hdelta_eps_spec].
    
    assert (H_A_eps_a_prem : forall (y : R_UniformSpace), ball 0 delta_eps y -> 0 < y -> Rabs (G y - I_Rpower) < eps).
    {
      intros y Hyball Hy_pos.
      assert (H1 : Q y) by (apply Hdelta_eps_spec; exact Hyball).
      unfold Q in H1.
      apply H1.
      exact Hy_pos.
    }
    assert (H_A_eps_a_result : let a := Rmin (u / 2) (delta_eps / 2) in Rabs (G a - I_Rpower) < eps).
    {
      apply A_eps_a with (u := u) (delta_eps := delta_eps) (A_eps := fun v : R => Rabs (G v - I_Rpower) < eps).
      - exact Hu_pos.
      - exact H_A_eps_a_prem.
    }
    
    set (v := Rmin (u / 2) (delta_eps / 2)) in *.
    assert (Hv_prop : Rabs (G v - I_Rpower) < eps).
    {
      exact H_A_eps_a_result.
    }
    
    assert (H_delta_eps_pos' : 0 < pos delta_eps) by (exact (cond_pos delta_eps)).
    assert (H_half_u_pos : 0 < u / 2) by lra.
    assert (H_half_delta_pos : 0 < delta_eps / 2) by lra.
    
    assert (H_v_pos : 0 < v).
    {
      unfold v.
      apply Rmin_pos.
      - exact H_half_u_pos.
      - exact H_half_delta_pos.
    }
    
    pose proof (a_properties u Hu_pos delta_eps) as [H_v_pos2 [H_v_lt_delta H_v_lt_u]].
    
    assert (H_v_le_u : v <= u).
    {
      exact (Rlt_le _ _ H_v_lt_u).
    }
    
    assert (H_Gv_ge_Gu : G v >= G u).
    {
      apply H_G_monotone with (v1 := v) (v2 := u).
      - split; lra.
      - lra.
    }
    
    assert (H1 : G v - I_Rpower < eps).
    {
      apply Rabs_lt_between' in Hv_prop.
      lra.
    }
    assert (H2 : -eps < G v - I_Rpower).
    {
      apply Rabs_lt_between' in Hv_prop.
      lra.
    }
    
    assert (H3 : G v < (I_Rpower + G u) / 2).
    {
      unfold eps in H1.
      lra.
    }
    
    assert (H4 : (I_Rpower + G u) / 2 < G u).
    {
      lra.
    }
    
    assert (H5 : G v >= G u) by exact H_Gv_ge_Gu.
    
    lra.
  }
  lra.
Qed.

(* 值集 *)
Definition F_set := fun x : R => exists u : R, 0 < u < c /\ x = RInt f u c.

Require Import Stdlib.Reals.Reals.

(* 上确界存在性 *)
Lemma lub_F_exists : { l : R | is_lub F_set l }.
Proof.
  apply completeness.
  - exists I_Rpower.
    intros x (u & Hu & ->).
    apply F_upper_bound; assumption.
  - exists (RInt f (c/2) c).
    exists (c/2).
    split; [lra | reflexivity].
Qed.

(* 右极限等于上确界 *)

End IntegralLemmas.

(* 减法三角不等式 *)
Lemma Rabs_triang_sub : forall (a b : R), Rabs (a - b) <= Rabs a + Rabs b.
Proof.
  intros a b.
  assert (H1 : a - b = a + (-b)). { lra. }
  rewrite H1.
  assert (H2 : Rabs (a + (-b)) <= Rabs a + Rabs (-b)). { apply Rabs_triang. }
  assert (H3 : Rabs (-b) = Rabs b). { apply Rabs_Ropp. }
  rewrite H3 in H2.
  exact H2.
Qed.

(* 广义积分蕴含存在性 *)
Lemma is_RInt_gen_to_ex_RInt_gen : forall {V : NormedModule R_AbsRing} (g : R -> V) (Fa Fb : (R -> Prop) -> Prop) (I : V),
  is_RInt_gen g Fa Fb I -> ex_RInt_gen g Fa Fb.
Proof.
  intros. exists I; assumption.
Qed.

(* 积分区间对称性 *)
Lemma ex_RInt_sym : forall (g : R -> R) (a b : R),
  ex_RInt g a b -> ex_RInt g b a.
Proof.
  intros g a b [I HI].
  pose proof (is_RInt_swap g b a I HI) as Hswapped.
  exists (-I).
  exact Hswapped.
Qed.

(* at_right 0 的区间刻画 *)
Lemma at_right_0_interval (Q : R -> Prop) :
  at_right 0 Q ->
  exists delta : R, delta > 0 /\ forall x, 0 < x < delta -> Q x.
Proof.
  intros H.
  apply at_right_has_eps in H.
  destruct H as [eps H].
  exists (pos eps).
  split.
  - apply cond_pos.
  - intros x Hx.
    specialize (H x).
    apply H.
    rewrite Rplus_0_l.
    exact Hx.
Qed.

(* 乘积滤子分解 *)
Lemma filter_prod_at_right_at_point_decompose
      (c : R) (P0 : R -> R -> Prop) :
  filter_prod (at_right 0) (at_point c) (fun ab => P0 (fst ab) (snd ab)) ->
  exists (Q1 Q2 : R -> Prop),
    at_right 0 Q1 /\ at_point c Q2 /\
    forall x y, Q1 x -> Q2 y -> P0 x y.
Proof.
  intros H.
  change (filter_prod (at_right 0) (at_point c) (fun ab : R * R => P0 (fst ab) (snd ab))) in H.
  
  assert (H_ind : forall (Q1 : R -> Prop) (Q2 : R -> Prop),
             at_right 0 Q1 ->
             at_point c Q2 ->
             (forall (x : R) (y : R), Q1 x -> Q2 y -> P0 (fst (x, y)) (snd (x, y))) ->
             (exists (Q1 Q2 : R -> Prop), at_right 0 Q1 /\ at_point c Q2 /\ forall x y : R, Q1 x -> Q2 y -> P0 x y)).
  {
    intros Q1 Q2 HQ1 HQ2 Hmain.
    exists Q1, Q2.
    split; [ exact HQ1 | split; [ exact HQ2 | simpl in Hmain; exact Hmain ] ].
  }

  exact (@filter_prod_ind R R (at_right 0) (at_point c)
                           (fun ab : R * R => P0 (fst ab) (snd ab))
                           (exists (Q1 Q2 : R -> Prop), at_right 0 Q1 /\ at_point c Q2 /\ forall x y : R, Q1 x -> Q2 y -> P0 x y)
                           (fun (Q1 : R -> Prop) (Q2 : R -> Prop) (HQ1 : at_right 0 Q1) (HQ2 : at_point c Q2) (Hmain : _) =>
                              H_ind Q1 Q2 HQ1 HQ2 Hmain)
                           H).
Qed.

(* 广义积分得到滤子近似 *)
Lemma is_RInt_gen_to_filter_prod_approx
      (g : R -> R) (I c : R) (eps : R) (Heps : eps > 0)
      (Hgen : is_RInt_gen g (at_right 0) (at_point c) I) :
  filter_prod (at_right 0) (at_point c)
    (fun ab => Rabs (RInt g (fst ab) (snd ab) - I) < eps).
Proof.
  assert (HFa : Filter (at_right 0)) by apply filter_filter.
  assert (HFb : Filter (at_point c)) by apply filter_filter.
  pose proof (is_RInt_gen_filterlim g (at_right 0) (at_point c) I HFa HFb Hgen) as Hlim.
  rewrite filterlim_locally in Hlim.
  specialize (Hlim (mkposreal eps Heps)).
  simpl in Hlim.
  exact Hlim.
Qed.

(* at_point 包含自身 *)
Lemma at_point_contains_self (c : R) (Q : R -> Prop) :
  at_point c Q -> Q c.
Proof.
  intros HQ.
  assert (Hsing : at_point c (fun y : R_UniformSpace => y = c)).
  {
    apply at_point_singleton.
  }
  assert (Hproper : ProperFilter (at_point c)).
  {
    apply at_point_filter.
  }
  assert (Hfil : Filter (at_point c)).
  {
    apply filter_filter.
  }
  assert (Hinter : at_point c (fun y : R_UniformSpace => Q y /\ y = c)).
  {
    apply (@filter_and R_UniformSpace (at_point c) Hfil Q (fun y : R_UniformSpace => y = c)).
    - exact HQ.
    - exact Hsing.
  }
  assert (Hex : exists (y : R_UniformSpace), Q y /\ y = c).
  {
    apply (@filter_ex R_UniformSpace (at_point c) Hproper (fun y : R_UniformSpace => Q y /\ y = c)).
    exact Hinter.
  }
  destruct Hex as [y [HyQ Hy_eq]].
  rewrite Hy_eq in HyQ.
  exact HyQ.
Qed.

(* 广义积分得到存在性滤子 *)
Lemma is_RInt_gen_to_filter_prod_ex
      (g : R -> R) (c I : R)
      (Hgen : is_RInt_gen g (at_right 0) (at_point c) I) :
  filter_prod (at_right 0) (at_point c) (fun ab : R * R => ex_RInt g (fst ab) (snd ab)).
Proof.
  assert (Htrue : locally I (fun _ => True)). { apply filter_true. }
  unfold is_RInt_gen in Hgen.
  specialize (Hgen (fun _ => True) Htrue) as Hf.
  eapply filter_imp with
    (P := fun x => exists y, is_RInt g (fst x) (snd x) y /\ True)
    (Q := fun x => ex_RInt g (fst x) (snd x)).
  - intros [a b] [y [Hy _]]; unfold ex_RInt; exists y; exact Hy.
  - exact Hf.
Qed.

(* 从广义积分存在性导出右邻域内常义可积 *)
Lemma ex_RInt_from_RInt_gen (g : R -> R) (c I : R) :
  is_RInt_gen g (at_right 0) (at_point c) I ->
  exists delta : R, 0 < delta /\
    forall u : R, 0 < u < delta -> ex_RInt g u c.
Proof.
  intros Hgen.
  pose proof (is_RInt_gen_to_filter_prod_ex g c I Hgen) as Hprod.
  apply filter_prod_at_right_at_point_decompose in Hprod.
  destruct Hprod as [Q1 [Q2 [HQ1 [HQ2 Hex]]]].
  apply at_right_0_interval in HQ1.
  destruct HQ1 as [delta [Hdelta_pos Hdelta]].
  exists delta.
  split; [exact Hdelta_pos |].
  intros u [Hu_pos Hu_lt].
  assert (HQ1_u : Q1 u) by (apply Hdelta; split; lra).
  assert (HQ2_c : Q2 c) by (apply at_point_contains_self, HQ2).
  apply Hex; assumption.
Qed.

(* 实数差分解 *)
Lemma real_sub_sub (a b i : R) : a - b = (a - i) - (b - i).
Proof. lra. Qed.

(* 积分差分的 Chasles 关系 *)
Lemma RInt_sub_Chasles (g : R -> R) (a b c : R) :
  a <= b <= c -> ex_RInt g a c ->
  RInt g a b = RInt g a c - RInt g b c.
Proof.
  intros Hle Hex_ac.
  assert (Hex_ab := ex_RInt_Chasles_1 g a b c Hle Hex_ac).
  assert (Hex_bc := ex_RInt_Chasles_2 g a b c Hle Hex_ac).
  pose proof (RInt_Chasles g a b c Hex_ab Hex_bc) as Heq.
  unfold minus.
  rewrite <- Heq.
  unfold plus, opp in *; simpl in *.
  lra.
Qed.

(* 子区间可积性 *)
Lemma ex_RInt_subinterval (g : R -> R) (a b c : R) :
  a <= b <= c -> ex_RInt g a c -> ex_RInt g a b /\ ex_RInt g b c.
Proof.
  intros Hle Hex.
  assert (Hex_ab := ex_RInt_Chasles_1 g a b c Hle Hex).
  assert (Hex_bc := ex_RInt_Chasles_2 g a b c Hle Hex).
  split; assumption.
Qed.

(* 广义积分柯西收敛准则（点 c 版本） *)
Lemma RInt_gen_cauchy_criterion_at_point_c
      (c : R) (g : R -> R) (I : R)
      (Hc_pos : 0 < c)
      (Hgen : is_RInt_gen g (at_right 0) (at_point c) I) :
  forall eps : R, eps > 0 ->
  exists delta : R, delta > 0 /\
    forall u1 u2 : R, 0 < u1 /\ u1 < u2 /\ u2 < delta ->
    Rabs (RInt g u1 u2) < eps.
Proof.
  intros eps Heps.
  set (half_eps := eps / 2).
  assert (Hhalf_pos : 0 < half_eps) by (unfold half_eps; lra).

  assert (Hfilter_Rabs : filter_prod (at_right 0) (at_point c) (fun ab : R * R => Rabs (RInt g (fst ab) (snd ab) - I) < half_eps)).
  { exact (is_RInt_gen_to_filter_prod_approx g I c half_eps Hhalf_pos Hgen). }
  
  assert (Hfilter_ex : filter_prod (at_right 0) (at_point c) (fun ab : R * R => ex_RInt g (fst ab) (snd ab))).
  { exact (is_RInt_gen_to_filter_prod_ex g c I Hgen). }

  destruct (filter_prod_at_right_at_point_decompose c (fun x y => Rabs (RInt g x y - I) < half_eps) Hfilter_Rabs)
    as [Q1_eps [Q2_eps [HQ1_eps [HQ2_eps Hmain_Rabs]]]].
  destruct (filter_prod_at_right_at_point_decompose c (fun x y => ex_RInt g x y) Hfilter_ex)
    as [Q1_ex [Q2_ex [HQ1_ex [HQ2_ex Hmain_ex]]]].

  assert (Q2_eps_c : Q2_eps c) by (apply at_point_contains_self, HQ2_eps).
  assert (Q2_ex_c : Q2_ex c) by (apply at_point_contains_self, HQ2_ex).

  apply at_right_0_interval in HQ1_eps.
  destruct HQ1_eps as [delta1 [Hd1_pos Hd1]].
  apply at_right_0_interval in HQ1_ex.
  destruct HQ1_ex as [delta2 [Hd2_pos Hd2]].

  set (delta := Rmin (Rmin delta1 delta2) c).
  assert (Hdelta_pos : 0 < delta) by (apply Rmin_pos; [apply Rmin_pos; lra | exact Hc_pos]).
  exists delta.
  split; [exact Hdelta_pos |].
  intros u1 u2 [Hu1_pos [Hu1_lt_u2 Hu2_lt_delta]].

  assert (Hu2_lt_c : u2 < c) by (apply Rlt_le_trans with delta; [exact Hu2_lt_delta | apply Rmin_r]).
  assert (Hu1_lt_c : u1 < c) by lra.
  assert (Hu1_lt_delta1 : u1 < delta1) by (apply Rlt_le_trans with delta; [| apply Rle_trans with (Rmin delta1 delta2); [apply Rmin_l | apply Rmin_l]]; lra).
  assert (Hu2_lt_delta1 : u2 < delta1) by (apply Rlt_le_trans with delta; [| apply Rle_trans with (Rmin delta1 delta2); [apply Rmin_l | apply Rmin_l]]; lra).
  assert (Hu1_lt_delta2 : u1 < delta2) by (apply Rlt_le_trans with delta; [| apply Rle_trans with (Rmin delta1 delta2); [apply Rmin_l | apply Rmin_r]]; lra).
  assert (Hu2_lt_delta2 : u2 < delta2) by (apply Rlt_le_trans with delta; [| apply Rle_trans with (Rmin delta1 delta2); [apply Rmin_l | apply Rmin_r]]; lra).

  assert (Q1_eps_u1 : Q1_eps u1) by (apply Hd1; split; lra).
  assert (Q1_eps_u2 : Q1_eps u2) by (apply Hd1; split; lra).
  assert (Q1_ex_u1 : Q1_ex u1) by (apply Hd2; split; lra).
  assert (Q1_ex_u2 : Q1_ex u2) by (apply Hd2; split; lra).

  assert (HR1 : Rabs (RInt g u1 c - I) < half_eps) by (apply Hmain_Rabs; [exact Q1_eps_u1 | exact Q2_eps_c]).
  assert (HR2 : Rabs (RInt g u2 c - I) < half_eps) by (apply Hmain_Rabs; [exact Q1_eps_u2 | exact Q2_eps_c]).
  assert (Hex1 : ex_RInt g u1 c) by (apply Hmain_ex; [exact Q1_ex_u1 | exact Q2_ex_c]).
  assert (Hex2 : ex_RInt g u2 c) by (apply Hmain_ex; [exact Q1_ex_u2 | exact Q2_ex_c]).

  assert (Hle : u1 < u2 < c) by (split; [exact Hu1_lt_u2 | exact Hu2_lt_c]).
  assert (Hle' : u1 <= u2 <= c) by lra.
  pose proof (RInt_Chasles g u1 u2 c) as Hch.
  assert (Hex_12 : ex_RInt g u1 u2).
  { apply (ex_RInt_Chasles_1 g u1 u2 c Hle' Hex1). }
  assert (Hex_2c : ex_RInt g u2 c) by exact Hex2.
  specialize (Hch Hex_12 Hex_2c).

  assert (H_eq : RInt g u1 u2 = RInt g u1 c - RInt g u2 c).
  {
    rewrite <- Hch.
    unfold plus, AbelianMonoid.plus.
    simpl.
    replace (RInt g u1 u2 + RInt g u2 c - RInt g u2 c) with (RInt g u1 u2) by lra.
    reflexivity.
  }
  rewrite H_eq.
  replace (RInt g u1 c - RInt g u2 c) with ((RInt g u1 c - I) - (RInt g u2 c - I)) by ring.
  apply Rle_lt_trans with (Rabs (RInt g u1 c - I) + Rabs (RInt g u2 c - I)).
  - apply Rabs_triang_sub.
  - assert (Hsum_lt : Rabs (RInt g u1 c - I) + Rabs (RInt g u2 c - I) < half_eps + half_eps).
    { apply Rplus_lt_compat; assumption. }
    assert (Hhalf_sum_eq : half_eps + half_eps = eps).
    { unfold half_eps. field. }
    rewrite Hhalf_sum_eq in Hsum_lt.
    exact Hsum_lt.
Qed.

(* 在点1处函数f的连续性证明 *)
Section Fix_f_continuity_at_1.
Context (s : Complex) (Hre : 1 < ComplexNumbers.re s).
Let a := ComplexNumbers.re s - 1.
Let f : R -> R := fun t => 
  match Rlt_dec 0 t with
  | left Ht_pos => exp (-t) * Rpower t a
  | right _ => 0
  end.
Let g : R -> R := fun t => exp (-t) * Rpower t a.

(* a大于0 *)
Lemma Ha_pos : 0 < a.
Proof. unfold a; lra. Qed.

(* exp(-t)在点1处连续 *)
Lemma Hcont_exp_neg : continuous (fun t : R => exp (-t)) 1.
Proof.
  assert (H1 : continuous (fun t : R => -t) 1).
  {
    assert (H_id : continuous (fun t : R => t) 1).
    { apply continuous_id. }
    exact (continuous_opp (fun t : R => t) 1 H_id).
  }
  assert (H2 : continuous exp (-1)).
  { apply continuous_exp. }
  exact (continuous_comp (fun t : R => -t) exp 1 H1 H2).
Qed.

(* Rpower t a在t=1处连续 *)
Lemma Hcont_Rpower : continuous (fun t : R => Rpower t a) 1.
Proof.
  assert (Ha_pos : 0 < a).
  { unfold a; lra. }
  assert (H1_pos : (0 : R) < 1).
  { lra. }
  assert (Hcont_pt : continuity_pt (fun t : R => Rpower t a) 1).
  { apply continuity_pt_Rpower_pos; assumption. }
  apply continuity_pt_to_continuous_simple.
  exact Hcont_pt.
Qed.

(* g(t)=exp(-t)*Rpower t a在t=1处连续 *)
Lemma Hcont_g_at_1 : continuous g 1.
Proof.
  unfold g.
  assert (Hcont_f1 : continuous (fun t : R => exp (-t)) 1).
  { exact Hcont_exp_neg. }
  assert (Hcont_f2 : continuous (fun t : R => Rpower t a) 1).
  { exact Hcont_Rpower. }
  apply continuous_mult with 
    (f := fun t : R => exp (-t)) 
    (g := fun t : R => Rpower t a) 
    (x := (1 : R)).
  - exact Hcont_f1.
  - exact Hcont_f2.
Qed.

(* 1的邻域内所有点都满足t>0 *)
Lemma Hloc_pos_at_1 : locally 1 (fun t : R => 0 < t).
Proof.
  apply locally_iff_open_ball with (z := 1) (Q := fun t : R => 0 < t).
  exists (0.5 : R).
  split.
  - lra.
  - intros y Hy.
    assert (Heq : (0.5 : R) = / 2).
    { lra. }
    assert (Hy' : Rabs (y - 1) < / 2).
    { rewrite <- Heq. exact Hy. }
    assert (Habs : y - 1 < / 2 /\ - / 2 < y - 1).
    { apply Rabs_def2. exact Hy'. }
    assert (H2 : - / 2 < y - 1).
    { destruct Habs as [_ H2]. exact H2. }
    lra.
Qed.

(* t>0时f(t)=g(t) *)
Lemma Hf_eq_g_when_pos : forall t : R, 0 < t -> f t = g t.
Proof.
  intros t Ht_pos.
  unfold f, g.
  destruct (Rlt_dec 0 t) as [Hpos | Hneg].
  - reflexivity.
  - exfalso; apply Hneg; exact Ht_pos.
Qed.

(* 1的邻域内f(t)=g(t) *)
Lemma Hloc_eq_fg_at_1 : locally 1 (fun t : R => f t = g t).
Proof.
  apply filter_imp with (P := fun t : R => 0 < t).
  - exact Hf_eq_g_when_pos.
  - exact Hloc_pos_at_1.
Qed.

(* f在点1处连续 *)
Theorem Hcont_f_at_1 : continuous f 1.
Proof.
  apply continuous_ext_loc with (g := g) (x := 1).
  - assert (H_aux : locally 1 (fun y : R_UniformSpace => g y = f y)).
    {
      apply filter_imp with (P := fun t : R => f t = g t).
      - intros t Ht. symmetry. exact Ht.
      - exact Hloc_eq_fg_at_1.
    }
    exact H_aux.
  - exact Hcont_g_at_1.
Qed.

End Fix_f_continuity_at_1.

(* 广义可积性：f 在 (0,1) 上广义可积 *)
Lemma f_integrable_01 (s : Complex) (Hre : 1 < ComplexNumbers.re s) :
  ex_RInt_gen (fun t => match Rlt_dec 0 t with left H => gamma_integrand_real s t H | right _ => 0 end)
              (at_right 0) (at_left 1).
Proof.
  set (f := fun t : R => match Rlt_dec 0 t with left H => gamma_integrand_real s t H | right _ => 0 end).
  set (c := (1/2)%R).
  set (a := ComplexNumbers.re s - 1).

  assert (Hc_pos : 0 < c) by (unfold c; lra).
  assert (Hc_lt1 : c < 1) by (unfold c; lra).
  assert (Ha_pos : 0 < a) by (unfold a; lra).
  assert (Hc_le1 : c <= 1) by lra.
  assert (Hc_lt1_strict : c < 1) by lra.

  assert (Hf_eq : forall t : R, 0 < t -> f t = exp (- t) * Rpower t a).
  {
    intros t Ht_pos.
    exact (f_eq_exp_times_Rpower s t Ht_pos).
  }

  assert (Hcont_f_pos : forall t : R, 0 < t <= 1 -> continuous f t).
  {
    intros t [Ht_pos Ht_le1].
    assert (Hderiv_neg : derivable_pt (fun t : R => - t) t).
    { apply derivable_pt_opp; apply derivable_pt_id. }
    assert (Hcont_neg_pt : continuity_pt (fun t : R => - t) t).
    { exact (derivable_continuous_pt (fun t : R => - t) t Hderiv_neg). }
    assert (Hcont_neg : continuous (fun t : R => - t) t).
    { exact (continuity_pt_to_continuous (fun t : R => - t) t Hcont_neg_pt). }

    assert (Hderiv_exp : derivable_pt exp (- t)).
    { exact (derivable_pt_exp_manual (- t)). }
    assert (Hcont_exp_pt : continuity_pt exp (- t)).
    { exact (derivable_continuous_pt exp (- t) Hderiv_exp). }
    assert (Hcont_exp : continuous exp (- t)).
    { exact (continuity_pt_to_continuous exp (- t) Hcont_exp_pt). }

    assert (Hcont_exp_neg_pt : continuity_pt (fun t : R => exp (- t)) t).
    {
      apply continuity_pt_comp with (f1 := fun t : R => - t) (f2 := exp) (x := t).
      - exact Hcont_neg_pt.
      - exact Hcont_exp_pt.
    }
    assert (Hcont_exp_neg : continuous (fun t : R => exp (- t)) t).
    { exact (continuity_pt_to_continuous (fun t : R => exp (- t)) t Hcont_exp_neg_pt). }

    assert (Hcont_rpower_pt : continuity_pt (fun t : R => Rpower t a) t).
    { apply continuity_pt_Rpower_pos; [exact Ha_pos | exact Ht_pos]. }
    assert (Hcont_rpower : continuous (fun t : R => Rpower t a) t).
    { exact (continuity_pt_to_continuous (fun t : R => Rpower t a) t Hcont_rpower_pt). }

    assert (Hcont_prod_pt : continuity_pt (fun t : R => exp (- t) * Rpower t a) t).
    { apply continuity_pt_mult; [exact Hcont_exp_neg_pt | exact Hcont_rpower_pt]. }
    assert (Hcont_prod : continuous (fun t : R => exp (- t) * Rpower t a) t).
    { exact (continuity_pt_to_continuous (fun t : R => exp (- t) * Rpower t a) t Hcont_prod_pt). }

    assert (H_pos_half : 0 < t / 2) by lra.
    assert (Hloc_pos : locally t (fun t : R => 0 < t)).
    {
      apply locally_iff_open_ball.
      exists (t / 2).
      split.
      - exact H_pos_half.
      - intros y Hy.
        assert (H_rab_iff : Rabs (y - t) < t / 2 <-> - (t / 2) < y - t < t / 2).
        { apply Rabs_lt_between. }
        assert (H1 : - (t / 2) < y - t /\ y - t < t / 2).
        { apply H_rab_iff. exact Hy. }
        destruct H1 as [H1_left _].
        lra.
    }
    assert (Hloc_pos_unfold : exists eps : R, eps > 0 /\ forall y : R, Rabs (y - t) < eps -> 0 < y).
    { apply locally_iff_open_ball in Hloc_pos. exact Hloc_pos. }
    destruct Hloc_pos_unfold as [eps [Heps_pos Heps_ball]].
    assert (H_eq_in_ball : forall y : R, Rabs (y - t) < eps -> f y = exp (- y) * Rpower y a).
    { intros y Hy.
      assert (Hy_pos : 0 < y). { exact (Heps_ball y Hy). }
      exact (Hf_eq y Hy_pos). }
    assert (Hloc_eq : locally t (fun t : R => f t = exp (- t) * Rpower t a)).
    { apply locally_iff_open_ball. exists eps. split.
      - exact Heps_pos.
      - exact H_eq_in_ball. }
    assert (Hcont_f_pt : continuity_pt f t).
    {
      apply continuity_pt_ext_loc with
        (f := fun t : R => exp (- t) * Rpower t a)
        (g := f)
        (x := t).
      - rewrite locally_iff_open_ball in Hloc_eq |- *.
        destruct Hloc_eq as [eps' [Heps'_pos Heq']].
        exists eps'. split; [exact Heps'_pos |].
        intros y Hy. symmetry. exact (Heq' y Hy).
      - exact Hcont_prod_pt.
    }
    exact (continuity_pt_to_continuous f t Hcont_f_pt).
  }

  assert (H_f_int_0c : ex_RInt_gen f (at_right 0) (at_point c)).
  {
    apply (f_integrable_0c s c Hre Hc_pos Hc_lt1
             Rpower_integrable_0c
             (fun (g : R -> R) (I : R) (Hgen : is_RInt_gen g (at_right 0) (at_point c) I) =>
                RInt_gen_cauchy_criterion_at_point_c c g I Hc_pos Hgen)).
  }
  destruct H_f_int_0c as [I0 H_is0].

  assert (H_f_int_c1 : ex_RInt f c 1).
  { apply f_integrable_c1 with (s := s) (c := c); assumption. }
  destruct H_f_int_c1 as [I1 H_is1].

  assert (Hcont_f1 : continuous f 1).
  { exact (Hcont_f_at_1 s Hre). }

  assert (H_RInt_eq : RInt f c 1 = I1).
  { apply (is_RInt_unique f c 1 I1 H_is1). }

  assert (H_ex_RInt_cu : forall u : R, c <= u <= 1 -> ex_RInt f c u).
  {
    intros u [Hcu Hu1].
    assert (H_ex_RInt_c1 : ex_RInt f c 1).
    { exists I1; exact H_is1. }
    assert (H_order : c <= u <= 1) by (split; [exact Hcu | exact Hu1]).
    exact (ex_RInt_Chasles_1 f c u 1 H_order H_ex_RInt_c1).
  }

  assert (H_ex_RInt_u1 : forall u0 : R, 0 < u0 < 1 -> ex_RInt f u0 1).
  {
    intros u0 [Hu0_pos Hu0_lt1].
    destruct (Rle_or_lt u0 c) as [Hu0c | Hcu0].
    - (* 情况1：u0 ≤ c，拼接 [u0,c] 和 [c,1] *)
      assert (H_ex_RInt_u0c : ex_RInt f u0 c).
      {
        assert (H_ex : exists delta : R, 0 < delta /\ forall u' : R, 0 < u' < delta -> ex_RInt f u' c).
        { apply ex_RInt_from_RInt_gen with (g := f) (c := c) (I := I0). exact H_is0. }
        destruct H_ex as [delta [Hdelta_pos Hdelta_int]].
        destruct (Rlt_or_le u0 delta) as [Hud | Hdu].
        + exact (Hdelta_int u0 (conj Hu0_pos Hud)).
        + assert (Hdelta_half_pos : 0 < delta / 2) by lra.
          assert (Hdelta_half_lt_delta : delta / 2 < delta) by lra.
          assert (Hcont_interval2 : forall z : R, Rmin (delta / 2) u0 <= z <= Rmax (delta / 2) u0 -> continuous f z).
          {
            intros z Hz.
            assert (Hmin2 : Rmin (delta / 2) u0 = delta / 2) by (apply Rmin_left; lra).
            assert (Hmax2 : Rmax (delta / 2) u0 = u0) by (apply Rmax_right; lra).
            rewrite Hmin2, Hmax2 in Hz.
            destruct Hz as [Hz1 Hz2].
            assert (Hz_pos : 0 < z) by lra.
            assert (Hz_le1 : z <= 1) by lra.
            exact (Hcont_f_pos z (conj Hz_pos Hz_le1)).
          }
          assert (H_ex_RInt_half_u0 : ex_RInt f (delta / 2) u0).
          {
            apply (@ex_RInt_continuous R_CompleteNormedModule (fun t => f t) (delta / 2) u0).
            exact Hcont_interval2.
          }
          assert (H_ex_RInt_u0_half : ex_RInt f u0 (delta / 2)).
          { apply ex_RInt_swap. exact H_ex_RInt_half_u0. }
          assert (H_ex_RInt_half_c : ex_RInt f (delta / 2) c).
          { apply Hdelta_int. split; lra. }
          apply ex_RInt_Chasles with (b := delta / 2); assumption.
      }
      apply ex_RInt_Chasles with (b := c).
      - exact H_ex_RInt_u0c.
      - exists I1; exact H_is1.
    - (* 情况2：c < u0，直接证明 [u0,1] 上连续必可积 *)
      assert (Hcont_interval3 : forall z : R, Rmin u0 1 <= z <= Rmax u0 1 -> continuous f z).
      {
        intros z Hz.
        assert (Hmin3 : Rmin u0 1 = u0) by (apply Rmin_left; lra).
        assert (Hmax3 : Rmax u0 1 = 1) by (apply Rmax_right; lra).
        rewrite Hmin3, Hmax3 in Hz.
        destruct Hz as [Hz1 Hz2].
        assert (Hz_pos : 0 < z) by lra.
        assert (Hz_le1 : z <= 1) by lra.
        exact (Hcont_f_pos z (conj Hz_pos Hz_le1)).
      }
      apply (@ex_RInt_continuous R_CompleteNormedModule (fun t => f t) u0 1).
      exact Hcont_interval3.
  }

  assert (H_filter_prod_iff : forall Q : R * R -> Prop,
    filter_prod (at_point c) (at_left 1) Q <-> at_left 1 (fun b : R => Q (c, b))).
  {
    intros Q.
    split.
    - intros H_prod.
      inversion H_prod as [Q1 R1 H_Q1 H_R1 H_incl].
      clear H_prod.
      unfold at_point in H_Q1; simpl in H_Q1.
      assert (R1_subset : forall y : R, R1 y -> Q (c, y)).
      { intros y HR1. apply (H_incl c y); [exact H_Q1 | exact HR1]. }
      unfold at_left in H_R1.
      unfold within in H_R1.
      apply locally_iff_open_ball in H_R1.
      destruct H_R1 as [delta [Hdelta_pos Hdelta]].
      apply locally_iff_open_ball.
      exists delta. split. exact Hdelta_pos.
      intros y Hy Hlt.
      specialize (Hdelta y Hy).
      apply Hdelta in Hlt.
      apply R1_subset in Hlt. exact Hlt.
    - intros H_left.
      apply (Filter_prod (at_point c) (at_left 1) Q (fun x => x = c) (fun y => Q (c, y))).
      + unfold at_point; trivial.
      + exact H_left.
      + intros x y Hx Hy. subst x. exact Hy.
  }

  assert (H_gen_c_left : is_RInt_gen f (at_point c) (at_left 1) I1).
  {
    unfold is_RInt_gen.
    intros P HP.
    apply locally_iff_open_ball in HP. destruct HP as [eps [Heps_pos Hball]].

    assert (Hlim : forall eps0 : R, eps0 > 0 ->
            exists delta0 : R, delta0 > 0 /\ delta0 <= (1 - c)/2 /\
            forall y, 1 - delta0 < y < 1 -> Rabs (RInt f c y - I1) < eps0).
    {
      intros eps0 Heps0.
      assert (Hcont1_eps : forall eps1 : R, eps1 > 0 ->
              exists delta1 : R, delta1 > 0 /\
              forall t, Rabs (t - 1) < delta1 -> Rabs (f t - f 1) < eps1).
      {
        intros eps1 Heps1.
        set (Q := fun z => Rabs (z - f 1) < eps1).
        assert (HQ : locally (f 1) Q).
        { apply locally_iff_open_ball. exists eps1; split; [exact Heps1 | intros; auto]. }
        assert (Hf := Hcont_f1 Q HQ).
        apply locally_iff_open_ball in Hf.
        destruct Hf as [delta1 [Hdelta1_pos Hdelta1]].
        exists delta1; split; [exact Hdelta1_pos |].
        intros t Ht. apply Hdelta1; assumption.
      }
      destruct (Hcont1_eps 1 Rlt_0_1) as [delta1 [Hdelta1_pos Hbound1]].
      set (M := Rabs (f 1) + 1).
      assert (M_pos : 0 < M) by (unfold M; apply Rplus_le_lt_0_compat; [apply Rabs_pos | lra]).
      pose (delta2 := eps0 / M).
      assert (delta2_pos : 0 < delta2) by (apply Rdiv_lt_0_compat; lra).
      pose (delta_c := (1 - c)/2).
      pose (delta0 := Rmin (Rmin delta1 delta2) delta_c).
      exists delta0.
      split.
      - unfold delta0; apply Rmin_pos.
        + apply Rmin_pos; [exact Hdelta1_pos | exact delta2_pos].
        + unfold delta_c; apply Rdiv_lt_0_compat; [lra | lra].
      split.
      - unfold delta0; apply Rle_trans with delta_c; [apply Rmin_r | apply Rle_refl].
      - intros y Hy.
        assert (y_range : 1 - delta0 < y < 1) by exact Hy.
        assert (H_delta_le : delta0 <= delta_c) by (unfold delta0; apply Rmin_r).
        assert (delta_le_delta1 : delta0 <= delta1).
        { unfold delta0. apply Rle_trans with (Rmin delta1 delta2); [apply Rmin_l | apply Rmin_l]. }
        assert (c_plus_delta_lt_1 : c + delta0 < 1).
        {
          apply Rle_lt_trans with (c + delta_c).
          - apply Rplus_le_compat_l. exact H_delta_le.
          - unfold delta_c; lra.
        }
        assert (y_gt_c : c < y).
        {
          apply Rlt_trans with (1 - delta0).
          - lra.
          - exact (proj1 y_range).
        }
        assert (H_ex_cy : ex_RInt f c y) by (apply H_ex_RInt_cu; split; [lra | apply Rlt_le; lra]).
        assert (H_ex_y1 : ex_RInt f y 1) by (apply H_ex_RInt_u1; split; lra).

        assert (H_sub : RInt f c y = RInt f c 1 - RInt f y 1).
        {
          apply RInt_sub_Chasles with (a := c) (b := y) (c := 1); [split; lra | exists I1; exact H_is1].
        }
        assert (H_eq : RInt f c y - I1 = - RInt f y 1).
        {
          rewrite <- H_RInt_eq, H_sub; ring.
        }
        rewrite H_eq, Rabs_Ropp.

        assert (H_bound_t : forall t, y <= t <= 1 -> Rabs (f t) <= M).
        {
          intros t Ht.
          assert (f t = f 1 + (f t - f 1)) by ring.
          rewrite H.
          apply Rle_trans with (Rabs (f 1) + Rabs (f t - f 1)).
          - apply Rabs_triang.
          - apply Rplus_le_compat_l.
            apply Rlt_le.
            apply Hbound1.
            rewrite Rabs_minus_sym.
            assert (0 <= 1 - t) by lra.
            rewrite Rabs_pos_eq; [| lra].
            apply Rle_lt_trans with (1 - y); [lra |].
            apply Rlt_le_trans with delta0; [lra | exact delta_le_delta1].
        }
        assert (H_abs_y1 : Rabs (RInt f y 1) <= (1 - y) * M).
        {
          apply abs_RInt_le_const with (f := f) (a := y) (b := 1) (M := M); [lra | exact H_ex_y1 | intros t Ht; apply H_bound_t; assumption].
        }
        assert (H_1m_y_lt_delta0 : 1 - y < delta0) by lra.
        assert (delta0_le_delta2 : delta0 <= delta2).
        {
          unfold delta0. apply Rle_trans with (Rmin delta1 delta2); [apply Rmin_l | apply Rmin_r].
        }
        assert (H_1m_y_lt_delta2 : 1 - y < delta2).
        {
          apply Rlt_le_trans with delta0; [exact H_1m_y_lt_delta0 | exact delta0_le_delta2].
        }
        assert (H_RInt_y1_lt_eps0 : Rabs (RInt f y 1) < eps0).
        {
          apply Rle_lt_trans with ((1 - y) * M).
          - exact H_abs_y1.
          - assert (H_prod_lt : (1 - y) * M < delta2 * M).
            { apply Rmult_lt_compat_r; [exact M_pos | exact H_1m_y_lt_delta2]. }
            assert (Heq : delta2 * M = eps0) by (unfold delta2; field; lra).
            rewrite <- Heq.
            exact H_prod_lt.
        }
        exact H_RInt_y1_lt_eps0.
    }

    destruct (Hlim eps Heps_pos) as [delta [Hdelta_pos [Hdelta_bound Hdelta]]].

    pose (A := fun a => a = c).
    pose (B := fun b => 1 - delta < b < 1).
    assert (HA : at_point c A).
    { unfold at_point; exact (eq_refl c). }
    assert (HB : at_left 1 B).
    {
      apply locally_iff_open_ball.
      exists delta; split; [exact Hdelta_pos |].
      intros y Hy Hlt.
      split.
      - assert (Habs : 1 - y = Rabs (y - 1)).
        { rewrite Rabs_left1; lra. }
        rewrite <- Habs in Hy.
        lra.
      - exact Hlt.
    }

    set (P' := fun ab : R * R => A (fst ab) /\ B (snd ab)).
    assert (HP' : filter_prod (at_point c) (at_left 1) P').
    {
      apply (Filter_prod (at_point c) (at_left 1) P' A B).
      - exact HA.
      - exact HB.
      - intros x y Hx Hy; split; assumption.
    }

    assert (Himp : forall ab : R * R, P' ab ->
                 exists z : R, is_RInt f (fst ab) (snd ab) z /\ P z).
    {
      intros [x0 y] [Hx Hy]; simpl in Hx, Hy.
      rewrite Hx; clear Hx.
      destruct Hy as [Hy1 Hy2].

      assert (x0_lt_y : c < y).
      {
        assert (c + delta < 1).
        {
          apply Rle_lt_trans with (c + (1 - c)/2).
          - apply Rplus_le_compat_l; exact Hdelta_bound.
          - unfold Rdiv; lra.
        }
        apply Rlt_trans with (1 - delta); [lra | exact Hy1].
      }

      assert (H_ex_xy : ex_RInt f c y) by (apply H_ex_RInt_cu; split; [lra | apply Rlt_le; lra]).
      destruct H_ex_xy as [z H_is].

      exists z.
      split; [exact H_is |].
      assert (H_z_eq : z = RInt f c y).
      { symmetry. apply (is_RInt_unique f c y z H_is). }
      rewrite H_z_eq.
      apply Hball.
      apply Hdelta.
      split; [exact Hy1 | exact Hy2].
    }

    exact (filter_imp _ _ Himp HP').
  }

  exists (I0 + I1).
  change (is_RInt_gen f (at_right 0) (at_left 1) (plus I0 I1)).
  apply is_RInt_gen_Chasles with (b := c).
  - exact H_is0.
  - exact H_gen_c_left.
Qed.

(* 伽马被积函数实部在 (0,1] 上的连续性 *)
Lemma f_continuity_on_positive_le1 (s : Complex) (Hre : 1 < ComplexNumbers.re s) :
  forall t : R, 0 < t <= 1 ->
    continuous (fun t : R => match Rlt_dec 0 t with left H => gamma_integrand_real s t H | right _ => 0 end) t.
Proof.
  intros t [Ht_pos Ht_le1].
  set (f := fun t : R => match Rlt_dec 0 t with left H => gamma_integrand_real s t H | right _ => 0 end).
  set (a := ComplexNumbers.re s - 1).
  set (g := fun t' : R => exp (- t') * Rpower t' a).
  assert (Ha_pos : 0 < a) by (unfold a; lra).
  assert (Hf_eq : forall t' : R, 0 < t' -> f t' = g t').
  { intros t' Ht'_pos.
    unfold g, f.
    rewrite (f_eq_exp_times_Rpower s t' Ht'_pos).
    reflexivity. }

  assert (Hcont_id : continuous (fun t' : R => t') t).
  { apply continuous_id. }

  assert (Hcont_neg : continuous (fun t' : R => - t') t).
  {
    apply continuous_opp with (f := fun t' : R => t').
    exact Hcont_id.
  }

  assert (Hcont_exp_neg : continuous (fun t' : R => exp (- t')) t).
  { apply continuous_comp with (f := fun t' : R => - t') (g := exp) (x := t).
    - exact Hcont_neg.
    - apply continuous_exp. }

  assert (Hcont_Rpower : continuous (fun t' : R => Rpower t' a) t).
  { apply continuity_pt_to_continuous.
    apply continuity_pt_Rpower_pos.
    - exact Ha_pos.
    - exact Ht_pos. }

  assert (Hcont_g : continuous g t).
  { unfold g.
    apply continuous_mult with (f := fun t' : R => exp (- t')) (g := fun t' : R => Rpower t' a) (x := t).
    - exact Hcont_exp_neg.
    - exact Hcont_Rpower. }

  assert (Hloc_eq : locally t (fun y : R => f y = g y)).
  {
    apply locally_iff_open_ball.
    exists (t / 2).
    split.
    - lra.
    - intros y Hy.
      assert (Ht2_pos : 0 < t / 2) by lra.
      assert (H_rab_lt : - (t / 2) < y - t < t / 2).
      {
        destruct (Rcase_abs (y - t)) as [Hneg | Hnonneg].
        - assert (Hrab_eq : Rabs (y - t) = - (y - t)) by (apply Rabs_left; exact Hneg).
          rewrite Hrab_eq in Hy.
          split; lra.
        - assert (Hrab_eq : Rabs (y - t) = y - t) by (apply Rabs_right; exact Hnonneg).
          rewrite Hrab_eq in Hy.
          split; lra.
      }
      assert (Hy_pos : 0 < y) by lra.
      exact (Hf_eq y Hy_pos).
  }

  assert (Hloc_eq_sym : locally t (fun y : R_UniformSpace => g y = f y)).
  {
    assert (H_eps_ex : exists eps : R, eps > 0 /\ forall (y : R), Rabs (y - t) < eps -> f y = g y).
    {
      apply locally_iff_open_ball with (z := t) (Q := fun y : R => f y = g y).
      exact Hloc_eq.
    }
    destruct H_eps_ex as [eps [Heps_pos Heps_impl]].
    assert (H_eps_sym : forall (y : R_UniformSpace), Rabs (y - t) < eps -> g y = f y).
    {
      intros y Hy_lt.
      assert (H_eq_fg : f y = g y) by exact (Heps_impl y Hy_lt).
      apply eq_sym.
      exact H_eq_fg.
    }
    apply locally_iff_open_ball with (z := t) (Q := fun y : R_UniformSpace => g y = f y).
    exists eps.
    split.
    - exact Heps_pos.
    - exact H_eps_sym.
  }

  assert (Hcont_f : continuous f t).
  {
    apply continuous_ext_loc with (g := g) (x := t).
    - exact Hloc_eq_sym.
    - exact Hcont_g.
  }

  exact Hcont_f.
Qed.

(* 函数在 (u0,1] 上的可积性 *)
Lemma f_integrable_on_u1 (s : Complex) (Hre : 1 < ComplexNumbers.re s) :
  forall u0 : R, 0 < u0 < 1 ->
    ex_RInt (fun t : R => match Rlt_dec 0 t with left H => gamma_integrand_real s t H | right _ => 0 end) u0 1.
Proof.
  intros u0 [Hu0_pos Hu0_lt1].
  set (f := fun t : R => match Rlt_dec 0 t with left H => gamma_integrand_real s t H | right _ => 0 end).
  set (c := (1/2)%R).

  assert (Hcont_f_pos : forall t : R, 0 < t <= 1 -> continuous f t).
  { exact (f_continuity_on_positive_le1 s Hre). }

  destruct (Rle_or_lt u0 c) as [Hu0_le_c | Hc_lt_u0].

  - (* 情形1：u0 ≤ c，将区间拆分为 [u0,c] 和 [c,1] *)
    assert (Hc_le_1 : c <= 1) by (unfold c; lra).

    assert (Hcont_c1 : forall t, c <= t <= 1 -> continuous f t).
    { intros t [Ht_ge_c Ht_le_1]; apply Hcont_f_pos; split; lra. }
    assert (H_f_int_c1 : ex_RInt f c 1).
    {
      apply ex_RInt_continuous with (f := f) (a := c) (b := 1).
      intros z Hz.
      rewrite (Rmin_left c 1 Hc_le_1) in Hz.
      rewrite (Rmax_right c 1 Hc_le_1) in Hz.
      exact (Hcont_c1 z Hz).
    }

    assert (Hcont_u0c : forall t, u0 <= t <= c -> continuous f t).
    { intros t [Ht_ge_u0 Ht_le_c]; apply Hcont_f_pos; split; lra. }
    assert (H_f_int_u0c : ex_RInt f u0 c).
    {
      apply ex_RInt_continuous with (f := f) (a := u0) (b := c).
      intros z Hz.
      rewrite (Rmin_left u0 c Hu0_le_c) in Hz.
      rewrite (Rmax_right u0 c Hu0_le_c) in Hz.
      exact (Hcont_u0c z Hz).
    }

    apply ex_RInt_Chasles with (f := f) (a := u0) (b := c) (c := 1);
      [exact H_f_int_u0c | exact H_f_int_c1].

  - (* 情形2：u0 > c，直接证明 [u0,1] 上的连续性 *)
    assert (Hu0_le_1 : u0 <= 1) by lra.

    assert (Hcont_u01 : forall t, u0 <= t <= 1 -> continuous f t).
    { intros t [Ht_ge_u0 Ht_le_1]; apply Hcont_f_pos; split; lra. }

    apply ex_RInt_continuous with (f := f) (a := u0) (b := 1).
    intros z Hz.
    rewrite (Rmin_left u0 1 Hu0_le_1) in Hz.
    rewrite (Rmax_right u0 1 Hu0_le_1) in Hz.
    exact (Hcont_u01 z Hz).
Qed.

(* 积分上限函数在 1 处的左极限为零 *)
Lemma RInt_f_y1_limit_to_zero_at_1 (s : Complex) (Hre : 1 < ComplexNumbers.re s) :
  filterlim (fun y : R => RInt (fun t : R => match Rlt_dec 0 t with left H => gamma_integrand_real s t H | right _ => 0 end) y 1)
            (at_left 1) (locally 0).
Proof.
  set (f := fun t : R => match Rlt_dec 0 t with left H => gamma_integrand_real s t H | right _ => 0 end).
  assert (Hcont_f1 : continuous f 1) by (exact (Hcont_f_at_1 s Hre)).
  assert (H_integrable : forall y : R, 0 < y < 1 -> ex_RInt f y 1)
    by (exact (f_integrable_on_u1 s Hre)).

  intros P [eps Heps].
  set (e := pos eps).
  assert (He_pos : 0 < e) by (apply cond_pos).

  assert (H_eps_delta : exists d1 : R, d1 > 0 /\ forall t : R, Rabs (t - 1) < d1 -> Rabs (f t - f 1) < e / 2).
  {
    set (P' := fun y : R => Rabs (y - f 1) < e / 2).
    assert (HP' : locally (f 1) P').
    { apply locally_iff_open_ball. exists (e / 2); split; [lra | intros y Hy; exact Hy]. }
    apply Hcont_f1 in HP'.
    apply locally_iff_open_ball in HP'.
    destruct HP' as [d1 [Hd1_pos Hd1]].
    exists d1; split; [exact Hd1_pos |].
    intros t Ht. apply Hd1 in Ht. exact Ht.
  }
  destruct H_eps_delta as [d1 [Hd1_pos Hd1]].

  set (M := Rabs (f 1) + e / 2).
  assert (M_pos : 0 < M).
  {
    unfold M.
    apply Rplus_le_lt_0_compat.
    - apply Rabs_pos.
    - lra.
  }

  set (d2 := e / M).
  assert (Hd2_pos : 0 < d2).
  {
    unfold d2.
    apply Rdiv_lt_0_compat; [apply cond_pos | exact M_pos].
  }
  set (d := Rmin (Rmin d1 d2) (1/2)).
  assert (Hd_pos : 0 < d).
  {
    apply Rmin_pos.
    - apply Rmin_pos; [exact Hd1_pos | exact Hd2_pos].
    - lra.
  }
  assert (Hd_le_d1 : d <= d1).
  {
    unfold d.
    apply Rle_trans with (Rmin d1 d2); [apply Rmin_l | apply Rmin_l].
  }
  assert (Hd_le_d2 : d <= d2).
  {
    unfold d.
    apply Rle_trans with (Rmin d1 d2); [apply Rmin_l | apply Rmin_r].
  }
  assert (Hd_le_half : d <= 1/2).
  {
    unfold d.
    apply Rmin_r.
  }
  assert (H1_minus_d_pos : 0 < 1 - d).
  {
    lra.
  }

  exists (mkposreal d Hd_pos).
  intros y Hy Hlt.
  unfold ball, AbsRing_ball, Rdist, R_met in Hy; simpl in Hy.
  assert (Habs_y1 : Rabs (y - 1) < d) by exact Hy.
  assert (Hy_lt_1 : y < 1) by exact Hlt.
  assert (Hy_gt_1md : 1 - d < y).
  {
    rewrite Rabs_left1 in Habs_y1; [lra | lra].
  }
  assert (Hy_pos : 0 < y).
  {
    lra.
  }
  assert (Hy_in_domain : 0 < y < 1) by (split; [exact Hy_pos | exact Hy_lt_1]).
  assert (Hex_RInt : ex_RInt f y 1) by (apply H_integrable; exact Hy_in_domain).

  assert (Ht_bound1 : forall t : R, y <= t <= 1 -> Rabs (t - 1) < d1).
  {
    intros t [Ht_ge_y Ht_le_1].
    assert (H1 : 1 - t < d).
    { lra. }
    destruct (Rle_lt_or_eq _ _ Ht_le_1) as [Ht_lt_1 | Ht_eq_1].
    - assert (Ht_sub1_lt_0 : t - 1 < 0) by lra.
      assert (H21 : Rabs (t - 1) = -(t - 1)).
      { apply Rabs_left; exact Ht_sub1_lt_0. }
      assert (H22 : -(t - 1) = 1 - t) by ring.
      assert (H2 : Rabs (t - 1) = 1 - t).
      { rewrite H21, H22; reflexivity. }
      rewrite H2.
      apply Rlt_le_trans with (r2 := d).
      + exact H1.
      + exact Hd_le_d1.
    - rewrite Ht_eq_1, Rminus_diag, Rabs_R0; exact Hd1_pos.
  }

  assert (Hf_bound : forall t : R, y <= t <= 1 -> Rabs (f t) <= M).
  {
    intros t Ht_range.
    assert (Habs_t1 : Rabs (t - 1) < d1) by (apply Ht_bound1; exact Ht_range).
    assert (Hdiff : Rabs (f t - f 1) < e / 2) by (apply Hd1; exact Habs_t1).
    assert (H_tri : Rabs (f t) <= Rabs (f t - f 1) + Rabs (f 1)).
    {
      assert (Heq : f t = f t - f 1 + f 1) by ring.
      rewrite Heq.
      replace (Rabs (f t - f 1 + f 1 - f 1)) with (Rabs (f t - f 1)).
      - apply (Rabs_triang (f t - f 1) (f 1)).
      - assert (H : f t - f 1 + f 1 - f 1 = f t - f 1) by ring. rewrite H; reflexivity.
    }
    apply Rle_trans with (Rabs (f t - f 1) + Rabs (f 1)).
    - exact H_tri.
    - unfold M. replace (Rabs (f 1) + e / 2) with (e/2 + Rabs (f 1)) by ring.
      apply Rplus_le_compat.
      + apply Rlt_le; exact Hdiff.
      + apply Rle_refl.
  }

  assert (H_abs_y1_le : Rabs (RInt f y 1) <= M * (1 - y)).
  {
    assert (H_le : Rabs (RInt f y 1) <= (1 - y) * M).
    { apply abs_RInt_le_const with (f := f) (a := y) (b := 1) (M := M);
        [lra | exact Hex_RInt | intros t Ht; apply Hf_bound; assumption]. }
    replace (M * (1 - y)) with ((1 - y) * M) by (symmetry; apply Rmult_comm).
    exact H_le.
  }

  assert (H_final : Rabs (RInt f y 1) < e).
  {
    apply Rle_lt_trans with (M * (1 - y)).
    - exact H_abs_y1_le.
    - assert (H1_minus_y_lt_d : 1 - y < d) by lra.
      apply Rlt_le_trans with (M * d).
      + apply Rmult_lt_compat_l; [exact M_pos | exact H1_minus_y_lt_d].
      + assert (H_prod_le : M * d <= e).
        {
          apply Rle_trans with (M * (e / M)).
          - apply Rmult_le_compat_l. apply Rlt_le; exact M_pos. exact Hd_le_d2.
          - replace (M * (e / M)) with e by (field; lra). apply Rle_refl.
        }
        exact H_prod_le.
  }

  assert (H_ball : ball 0 eps (RInt f y 1)).
  {
    unfold ball; simpl; unfold AbsRing_ball; simpl.
    rewrite Rminus_0_r.
    exact H_final.
  }
  apply Heps in H_ball.
  exact H_ball.
Qed.

(* 左邻域存在正半径引理 *)
Lemma at_left_has_eps : forall (P : R -> Prop) (H : at_left 1 P),
  exists delta : R, delta > 0 /\ forall x, 1 - delta < x < 1 -> P x.
Proof.
  intros P H.
  unfold at_left, within in H.
  apply locally_iff_open_ball in H.
  destruct H as [eps [Heps_pos Heps]].
  exists eps.
  split.
  - exact Heps_pos.
  - intros x Hx.
    assert (Hx_abs : Rabs (x - 1) < eps).
    { rewrite Rabs_left1; [| lra]. replace (-(x-1)) with (1-x) by ring. lra. }
    apply Heps; [exact Hx_abs | lra].
Qed.

(* 广义积分区间拼接引理 *)
Lemma ex_RInt_gen_concat_0c_c1 (s : Complex) (Hre : 1 < ℜ(s)) (f : R -> R) (c : R)
      (Hc_pos : 0 < c) (Hc_lt1 : c < 1)
      (Hcont_f : forall t, 0 < t <= 1 -> continuous f t)
      (H_int_0c : ex_RInt_gen f (at_right 0) (at_point c))
      (H_int_c1 : ex_RInt f c 1) :
  ex_RInt_gen f (at_right 0) (at_left 1).
Proof.
  destruct H_int_0c as [I0 H_is0].
  destruct H_int_c1 as [I1 H_is1].
  set (I_total := I0 + I1).

  assert (Hlim1_0 : filterlim (fun y => RInt f y 1) (at_left 1) (locally 0)).
  {
    intros P' [eps' Heps'].
    set (e' := pos eps'). assert (He'_pos : 0 < e') by apply cond_pos.
    assert (Hcont_f1 : continuous f 1) by (apply Hcont_f; split; lra).
    assert (H_bound_loc : exists delta1 : R, delta1 > 0 /\
                           forall t, Rabs (t - 1) < delta1 -> Rabs (f t) < Rabs (f 1) + 1).
    {
      set (Q := fun y => Rabs (y - f 1) < 1).
      assert (HQ : locally (f 1) Q) by (exists (mkposreal 1 Rlt_0_1); intros y Hy; exact Hy).
      assert (Hf_local := Hcont_f1 Q HQ).
      apply locally_iff_open_ball in Hf_local.
      destruct Hf_local as [delta [Hdelta_pos Hdelta]].
      exists delta; split; [exact Hdelta_pos |].
      intros t Ht.
      specialize (Hdelta t Ht).
      assert (H_eq : f t = f 1 + (f t - f 1)) by ring.
      rewrite H_eq.
      apply Rle_lt_trans with (Rabs (f 1) + Rabs (f t - f 1)).
      - apply Rabs_triang.
      - rewrite <- (Rplus_0_r (Rabs (f 1))). apply Rplus_lt_compat_l. exact Hdelta.
    }
    destruct H_bound_loc as [delta1_loc [Hdelta1_loc_pos Hdelta1_loc]].

    assert (Hpos1 : 0 < e' / (2 * (Rabs (f 1) + 1))).
    { apply Rdiv_lt_0_compat; [exact He'_pos | apply Rmult_lt_0_compat; [lra | apply Rplus_le_lt_0_compat; [apply Rabs_pos | lra]]]. }
    assert (Hpos2 : 0 < 1/2) by lra.
    assert (Hpos_mid : 0 < Rmin (e' / (2 * (Rabs (f 1) + 1))) (1/2)).
    { apply Rmin_pos; [exact Hpos1 | exact Hpos2]. }
    set (delta := Rmin delta1_loc (Rmin (e' / (2 * (Rabs (f 1) + 1))) (1/2))).
    assert (Hdelta_pos : 0 < delta) by (apply Rmin_pos; [exact Hdelta1_loc_pos | exact Hpos_mid]).

    exists (mkposreal delta Hdelta_pos).
    intros y Hy Hlt.
    simpl in Hy.
    assert (Hy_abs : Rabs (y - 1) < delta) by exact Hy.
    assert (H_range : 1 - delta < y < 1) by (apply Rabs_lt_between in Hy_abs; lra).
    assert (Hdelta_le_half : delta <= 1/2).
    { unfold delta. apply Rle_trans with (Rmin (e' / (2 * (Rabs (f 1) + 1))) (1/2)).
      - apply Rmin_r.
      - apply Rmin_r. }
    assert (H1_delta_pos : 0 < 1 - delta) by lra.
    assert (Hy_pos : 0 < y) by (apply Rlt_trans with (1 - delta); [exact H1_delta_pos | exact (proj1 H_range)]).

    assert (Hex_y1 : ex_RInt f y 1).
    { apply ex_RInt_continuous with (f := f) (a := y) (b := 1).
      intros z Hz.
      assert (Hmin : Rmin y 1 = y) by (apply Rmin_left; lra).
      assert (Hmax : Rmax y 1 = 1) by (apply Rmax_right; lra).
      rewrite Hmin, Hmax in Hz.
      destruct Hz as [Hz1 Hz2].
      assert (Hz_pos : 0 < z) by (apply Rlt_le_trans with y; [exact Hy_pos | exact Hz1]).
      assert (Hz_le1 : z <= 1) by exact Hz2.
      apply Hcont_f; split; lra. }

    assert (H_bound_t : forall t, y <= t <= 1 -> Rabs (f t) < Rabs (f 1) + 1).
    {
      intros t Ht.
      assert (Ht_abs : Rabs (t - 1) < delta).
      {
        rewrite Rabs_left1; [| lra].
        replace (- (t - 1)) with (1 - t) by ring.
        apply Rle_lt_trans with (1 - y).
        - assert (H : 1 - t <= 1 - y) by lra. exact H.
        - lra.
      }
      assert (Ht_abs_lt_delta1 : Rabs (t - 1) < delta1_loc) by (apply Rlt_le_trans with delta; [exact Ht_abs | apply Rmin_l]).
      apply Hdelta1_loc in Ht_abs_lt_delta1; exact Ht_abs_lt_delta1.
    }

    assert (H_abs : Rabs (RInt f y 1) <= (1 - y) * (Rabs (f 1) + 1)).
    { apply abs_RInt_le_const with (M := Rabs (f 1) + 1); [lra | exact Hex_y1 | intros t Ht; apply Rlt_le, H_bound_t; exact Ht]. }

    assert (H_1my_lt_delta : 1 - y < delta) by lra.
    assert (H_prod : delta * (Rabs (f 1) + 1) <= e' / 2).
    {
      assert (Hle' : delta <= e' / (2 * (Rabs (f 1) + 1))).
      {
        unfold delta.
        apply Rle_trans with (Rmin (e' / (2 * (Rabs (f 1) + 1))) (1/2)).
        - apply Rmin_r.
        - apply Rmin_l.
      }
      assert (Hpos : 0 < Rabs (f 1) + 1) by (apply Rplus_le_lt_0_compat; [apply Rabs_pos | lra]).
      apply Rmult_le_compat_r with (r := Rabs (f 1) + 1) in Hle'; [| apply Rlt_le; exact Hpos].
      rewrite Rmult_comm in Hle'.
      replace ((e' / (2 * (Rabs (f 1) + 1))) * (Rabs (f 1) + 1)) with (e' / 2) in Hle'.
      - rewrite Rmult_comm. exact Hle'.
      - field; lra.
    }

    assert (H_final : Rabs (RInt f y 1) < e').
    {
      apply Rle_lt_trans with ((1 - y) * (Rabs (f 1) + 1)).
      - exact H_abs.
      - apply Rle_lt_trans with (delta * (Rabs (f 1) + 1)).
        + apply Rmult_le_compat_r.
          * apply Rplus_le_le_0_compat; [apply Rabs_pos | apply Rle_0_1].
          * apply Rlt_le; exact H_1my_lt_delta.
        + apply Rle_lt_trans with (e' / 2); [exact H_prod | lra].
    }

    apply Heps'.
    unfold ball; simpl.
    change (Rabs (RInt f y 1 - 0) < pos eps').
    rewrite Rminus_0_r.
    exact H_final.
  }

  assert (Hlim_c1 : filterlim (fun v => RInt f c v) (at_left 1) (locally I1)).
  {
    intros P [eps Heps].
    set (e := pos eps). assert (He_pos : 0 < e) by apply cond_pos.
    assert (H_filtermap : filtermap (fun y => RInt f y 1) (at_left 1) (fun z => Rabs (z - 0) < e)).
    {
      apply Hlim1_0.
      exists (mkposreal e He_pos); intros y Hy; exact Hy.
    }
    unfold filtermap in H_filtermap.
    simpl in H_filtermap.
    rename H_filtermap into H_at_left1_raw.

    assert (H_at_left1 : at_left 1 (fun y => Rabs (RInt f y 1) < e)).
    {
      apply filter_imp with (2 := H_at_left1_raw).
      intros x Hx.
      rewrite <- (Rminus_0_r (RInt f x 1)).
      exact Hx.
    }

    destruct (at_left_has_eps (fun y => Rabs (RInt f y 1) < e) H_at_left1) as [delta1 [Hd1_pos Hd1]].

    set (delta := Rmin delta1 (1 - c) / 2).
    assert (Hdelta_pos : 0 < delta).
    { apply Rdiv_lt_0_compat; [apply Rmin_pos; [exact Hd1_pos | lra] | lra]. }
    exists (mkposreal delta Hdelta_pos).
    intros v Hv_ball Hlt.
    simpl in Hv_ball.
    assert (Hv_abs : Rabs (v - 1) < delta) by exact Hv_ball.
    assert (Hv_range : 1 - delta < v < 1) by (apply Rabs_lt_between in Hv_abs; lra).

    assert (Hv_gt_c : c < v).
    {
      assert (Hdelta_le_half : delta <= (1 - c) / 2).
      { unfold delta. apply Rmult_le_compat_r with (r := /2); [lra |]. apply Rmin_r. }
      apply Rlt_trans with (1 - delta).
      - assert (Hc_lt_half_sum : c < (1 + c) / 2).
        {
          apply Rmult_lt_reg_r with 2; [lra |].
          replace (c * 2) with (2 * c) by ring.
          replace ((1 + c)/2 * 2) with (1 + c) by (field; lra).
          lra.
        }
        assert (Hle : (1 + c)/2 <= 1 - delta).
        {
          apply Rle_minus_l.
          lra.
        }
        apply Rlt_le_trans with (1 := Hc_lt_half_sum).
        exact Hle.
      - exact (proj1 Hv_range).
    }

    assert (Hv_in_delta1 : Rabs (v - 1) < delta1).
    {
      apply Rlt_trans with (r2 := delta).
      - exact Hv_abs.
      - unfold delta.
        apply Rle_lt_trans with (r2 := delta1 / 2).
        + apply Rmult_le_compat_r; [lra |]. apply Rmin_l.
        + lra.
    }

    assert (Hex_cv : ex_RInt f c v).
    { apply ex_RInt_continuous with (f := f) (a := c) (b := v).
      intros z Hz.
      assert (Hmin : Rmin c v = c) by (apply Rmin_left; lra).
      assert (Hmax : Rmax c v = v) by (apply Rmax_right; lra).
      rewrite Hmin, Hmax in Hz.
      destruct Hz as [Hz1 Hz2].
      assert (Hz_pos : 0 < z) by (apply Rlt_le_trans with c; [exact Hc_pos | exact Hz1]).
      apply Hcont_f; split; [exact Hz_pos | apply Rlt_le; lra]. }

    assert (Hex_v1 : ex_RInt f v 1).
    { apply ex_RInt_continuous with (f := f) (a := v) (b := 1).
      intros z Hz.
      assert (Hmin : Rmin v 1 = v) by (apply Rmin_left; lra).
      assert (Hmax : Rmax v 1 = 1) by (apply Rmax_right; lra).
      rewrite Hmin, Hmax in Hz.
      destruct Hz as [Hz1 Hz2].
      assert (Hv_pos : 0 < v) by (apply Rlt_trans with c; [exact Hc_pos | exact Hv_gt_c]).
      assert (Hz_pos : 0 < z) by (apply Rlt_le_trans with v; [exact Hv_pos | exact Hz1]).
      apply Hcont_f; split; [exact Hz_pos | exact Hz2]. }

    assert (H_chasles : RInt f c 1 = RInt f c v + RInt f v 1).
    {
      symmetry.
      apply (RInt_Chasles f c v 1); assumption.
    }

    assert (H_RInt_c1 : RInt f c 1 = I1).
    {
      apply (is_RInt_unique f c 1 I1). 
      exact H_is1.
    }
    rewrite H_RInt_c1 in H_chasles.
    assert (H_eq : RInt f c v = I1 - RInt f v 1) by lra.

    assert (Hv_cond : 1 - delta1 < v < 1).
    {
      split.
      - rewrite Rabs_left1 in Hv_in_delta1; [| lra].
        replace (- (v - 1)) with (1 - v) in Hv_in_delta1 by ring.
        lra.
      - exact (proj2 Hv_range).
    }
    specialize (Hd1 v Hv_cond).

    assert (Hball : ball I1 eps (RInt f c v)).
    {
      unfold ball; simpl.
      change (Rabs (RInt f c v - I1) < eps).
      rewrite H_eq.
      replace (I1 - RInt f v 1 - I1) with (- RInt f v 1) by ring.
      rewrite Rabs_Ropp.
      exact Hd1.
    }
    apply Heps in Hball.
    exact Hball.
  }

  assert (H_is_total : is_RInt_gen f (at_right 0) (at_left 1) I_total).
  {
    intros P [eps Heps].
    set (e := pos eps). assert (He_pos : 0 < e) by apply cond_pos.
    set (e3 := e / 3).
    assert (He3_pos : 0 < e3) by (unfold e3; apply Rdiv_lt_0_compat; lra).

    assert (Hloc0 : locally I0 (fun y => Rabs (y - I0) < e3)).
    { exists (mkposreal e3 He3_pos); intros y Hy; exact Hy. }
    assert (Hprod0 : filter_prod (at_right 0) (at_point c)
                      (fun ab => Rabs (RInt f (fst ab) (snd ab) - I0) < e3)).
    { exact (is_RInt_gen_filterlim f (at_right 0) (at_point c) I0 _ _ H_is0 (fun y => Rabs (y - I0) < e3) Hloc0). }
    pose proof (filter_prod_at_right_at_point_decompose c
                   (fun x y => Rabs (RInt f x y - I0) < e3) Hprod0) as Hdecomp.
    destruct Hdecomp as [A0 [B0 [HA0 [HB0 HAB0]]]].
    apply at_right_0_interval in HA0.
    destruct HA0 as [delta0 [Hdelta0_pos Hdelta0_int]].
    assert (Hc_in_B0 : B0 c) by (apply at_point_contains_self, HB0).

    assert (Hloc1 : locally I1 (fun y => Rabs (y - I1) < e3)).
    { exists (mkposreal e3 He3_pos); intros y Hy; exact Hy. }
    assert (Hat_left1 : at_left 1 (fun y => Rabs (RInt f c y - I1) < e3)).
    { exact (Hlim_c1 (fun y => Rabs (y - I1) < e3) Hloc1). }
    unfold at_left, within in Hat_left1.
    apply locally_iff_open_ball in Hat_left1.
    destruct Hat_left1 as [delta1 [Hdelta1_pos Hdelta1_imp]].
    set (d1 := delta1) in *.
    assert (Hd1 : forall v, 1 - d1 < v < 1 -> Rabs (RInt f c v - I1) < e3).
    {
      intros v [Hgt Hlt].
      assert (Hball : Rabs (v - 1) < d1).
      { rewrite Rabs_left1; lra. }
      specialize (Hdelta1_imp v Hball).
      apply Hdelta1_imp. exact Hlt.
    }

    set (delta_u := Rmin delta0 c).
    set (delta_v := Rmin d1 (1 - c)).
    assert (Hdelta_u_pos : 0 < delta_u) by (apply Rmin_pos; [exact Hdelta0_pos | exact Hc_pos]).
    assert (Hdelta_v_pos : 0 < delta_v) by (apply Rmin_pos; [exact Hdelta1_pos | lra]).

    set (U := fun u => 0 < u < delta_u).
    set (V := fun v => 1 - delta_v < v < 1).

    assert (HU : at_right 0 U).
    {
      unfold at_right, within.
      exists (mkposreal delta_u Hdelta_u_pos).
      intros y Hy Hy_pos.
      unfold ball, AbsRing_ball in Hy; simpl in Hy.
      apply Rabs_lt_between in Hy.
      destruct Hy as [Hlow Hhigh].
      rewrite Rminus_0_r in Hhigh.
      split; [exact Hy_pos | exact Hhigh].
    }

    assert (HV : at_left 1 V).
    {
      unfold at_left, within.
      exists (mkposreal delta_v Hdelta_v_pos).
      intros y Hy_ball Hy_lt.
      unfold ball, AbsRing_ball in Hy_ball; simpl in Hy_ball.
      apply Rabs_lt_between in Hy_ball.
      destruct Hy_ball as [Hlow Hhigh].
      split.
      - assert (Hequiv : - delta_v < y - 1 <-> 1 - delta_v < y) by lra.
        apply Hequiv; exact Hlow.
      - exact Hy_lt.
    }

    apply Filter_prod with (Q := U) (R := V); [exact HU | exact HV | ].
    intros u v Hu Hv.
    destruct Hu as [Hu_pos Hu_lt_delta_u].
    destruct Hv as [Hv_gt_1md Hv_lt_1].
    assert (Hu_lt_c : u < c) by (apply Rlt_le_trans with delta_u; [exact Hu_lt_delta_u | apply Rmin_r]).
    assert (Hc_le_1md : c <= 1 - delta_v).
    { assert (Hdelta_v_le_1mc : delta_v <= 1 - c) by (unfold delta_v; apply Rmin_r). lra. }
    assert (Hv_gt_c : c < v) by (apply Rle_lt_trans with (1 - delta_v); [exact Hc_le_1md | exact Hv_gt_1md]).
    assert (Hu_pos' : 0 < u) by exact Hu_pos.
    assert (Hv_lt_1' : v < 1) by exact Hv_lt_1.

    assert (Hex_uc : ex_RInt f u c).
    { apply ex_RInt_continuous with (f := f) (a := u) (b := c).
      intros z Hz.
      assert (Hmin : Rmin u c = u) by (apply Rmin_left; lra).
      assert (Hmax : Rmax u c = c) by (apply Rmax_right; lra).
      rewrite Hmin, Hmax in Hz.
      destruct Hz as [Hz1 Hz2].
      assert (Hz_pos : 0 < z) by (apply Rlt_le_trans with u; [exact Hu_pos | exact Hz1]).
      assert (Hz_le_c : z <= c) by exact Hz2.
      apply Hcont_f; split; [exact Hz_pos | apply Rlt_le; lra]. }
    assert (Hex_cv : ex_RInt f c v).
    { apply ex_RInt_continuous with (f := f) (a := c) (b := v).
      intros z Hz.
      assert (Hmin : Rmin c v = c) by (apply Rmin_left; lra).
      assert (Hmax : Rmax c v = v) by (apply Rmax_right; lra).
      rewrite Hmin, Hmax in Hz.
      destruct Hz as [Hz1 Hz2].
      assert (Hz_pos : 0 < z) by (apply Rlt_le_trans with c; [exact Hc_pos | exact Hz1]).
      assert (Hz_le_v : z <= v) by exact Hz2.
      apply Hcont_f; split; [exact Hz_pos | apply Rlt_le; lra]. }
    assert (H_eq : RInt f u v = RInt f u c + RInt f c v).
    { symmetry. apply (RInt_Chasles f u c v Hex_uc Hex_cv). }

    assert (Habs : Rabs (RInt f u c + RInt f c v - I_total) < e).
    {
      unfold I_total.
      replace (RInt f u c + RInt f c v - (I0 + I1)) with
          ((RInt f u c - I0) + (RInt f c v - I1)) by ring.
      apply Rle_lt_trans with (Rabs (RInt f u c - I0) + Rabs (RInt f c v - I1)).
      - apply Rabs_triang.
      - assert (Hlt_u : Rabs (RInt f u c - I0) < e3).
        { apply HAB0 with (y := c).
          - apply Hdelta0_int; split; [exact Hu_pos | apply Rlt_le_trans with delta_u; [exact Hu_lt_delta_u | apply Rmin_l]].
          - exact Hc_in_B0. }
        assert (Hlt_v : Rabs (RInt f c v - I1) < e3).
        {
          assert (H1_d1_le_1_dv : 1 - d1 <= 1 - delta_v).
          { apply Rplus_le_compat_l. apply Ropp_le_contravar. unfold delta_v; apply Rmin_l. }
          assert (H1_d1_lt_v : 1 - d1 < v).
          { apply Rle_lt_trans with (1 - delta_v); [exact H1_d1_le_1_dv | exact Hv_gt_1md]. }
          apply Hd1; split; [exact H1_d1_lt_v | exact Hv_lt_1].
        }
        apply Rlt_trans with (e3 + e3).
        + apply Rplus_lt_compat; [exact Hlt_u | exact Hlt_v].
        + unfold e3; lra.
    }

    assert (Habs' : Rabs (RInt f u v - I_total) < e).
    { rewrite H_eq. exact Habs. }
    assert (Hball : ball I_total eps (RInt f u v)).
    { unfold ball, AbsRing_ball; simpl. exact Habs'. }
    apply Heps in Hball.

    assert (Hex_uv : ex_RInt f u v).
    { apply ex_RInt_Chasles with (b := c); [exact Hex_uc | exact Hex_cv]. }
    assert (H_RInt_uv : is_RInt f u v (RInt f u v)).
    { apply (RInt_correct (V := R_CompleteNormedModule) f u v Hex_uv). }

    exists (RInt f u v). split.
    - exact H_RInt_uv.
    - exact Hball.
  }

  exists I_total; exact H_is_total.
Qed.

(* 广义可积性（第二种形式） *)
Lemma f_integrable_02 (s : Complex) (Hre : 1 < ComplexNumbers.re s) :
  ex_RInt_gen (fun t => match Rlt_dec 0 t with
                        | left H => gamma_integrand_real s t H
                        | right _ => 0
                        end)
              (at_right 0) (at_left 1).
Proof.
  set (f := fun t : R =>
              match Rlt_dec 0 t with
              | left H => gamma_integrand_real s t H
              | right _ => 0
              end).
  set (c := (1/2)%R).
  set (a := ComplexNumbers.re s - 1).

  assert (Hc_pos : 0 < c) by (unfold c; lra).
  assert (Hc_lt1 : c < 1) by (unfold c; lra).
  assert (Ha_pos : 0 < a) by (unfold a; lra).

  assert (Hcont_f : forall t : R, 0 < t <= 1 -> continuous f t).
  { exact (f_continuity_on_positive_le1 s Hre). }

  assert (H_f_int_0c : ex_RInt_gen f (at_right 0) (at_point c)).
  {
    apply (f_integrable_0c s c Hre Hc_pos Hc_lt1
             Rpower_integrable_0c
             (fun (g : R -> R) (I : R) (Hgen : is_RInt_gen g (at_right 0) (at_point c) I) =>
                RInt_gen_cauchy_criterion_at_point_c c g I Hc_pos Hgen)).
  }

  assert (H_f_int_c1 : ex_RInt f c 1).
  {
    apply f_integrable_c1 with (s := s) (c := c); [lra | lra | lra].
  }

  apply (ex_RInt_gen_concat_0c_c1 s Hre f c Hc_pos Hc_lt1 Hcont_f H_f_int_0c H_f_int_c1).
Qed.

(* 常义可积到左端点固定的广义可积性转换 *)
Lemma is_RInt_gen_at_point_at_left (f : R -> R) (c : R) (I1 : R)
      (Hc_lt_1 : c < 1)
      (Hcont : forall t : R, c <= t <= 1 -> continuous f t)
      (H_is1 : is_RInt f c 1 I1) :
  is_RInt_gen f (at_point c) (at_left 1) I1.
Proof.
  unfold is_RInt_gen.
  intros P HP.

  assert (H_eps : exists eps : posreal, forall y : R, ball I1 eps y -> P y).
  {
    destruct (locally_iff_open_ball I1 P) as [H1 H2].
    apply H1 in HP.
    destruct HP as [eps [Heps_pos Heps_prop]].
    exists (mkposreal eps Heps_pos).
    exact Heps_prop.
  }
  destruct H_eps as [eps Heps].
  set (e := pos eps).
  assert (He_pos : 0 < e) by (apply cond_pos).

  assert (Hc_le_1 : c <= 1) by (apply Rlt_le; exact Hc_lt_1).
  assert (Hbound : {M : R | forall t : R, c <= t <= 1 -> Rabs (f t) < M}).
  {
    apply bounded_continuity with (f := f) (a := c) (b := 1).
    intros x Hx. apply Hcont. exact Hx.
  }
  destruct Hbound as [M HM].

  assert (HM_nonneg : 0 <= M).
  {
    assert (Ht : c <= c <= 1) by (split; [apply Rle_refl | exact Hc_le_1]).
    specialize (HM c Ht) as Hlt.
    apply Rle_trans with (Rabs (f c)).
    - apply Rabs_pos.
    - apply Rlt_le; exact Hlt.
  }

  assert (Hex_c1 : ex_RInt f c 1).
  {
    unfold ex_RInt.
    exists I1.
    exact H_is1.
  }

  assert (H_main_ineq : forall y : R, c < y < 1 -> Rabs (RInt f c y - I1) <= M * (1 - y)).
  {
    intros y Hy.
    assert (Hy_c_lt : c < y) by lra.
    assert (Hy_lt_1 : y < 1) by lra.
    assert (Hc_le_y : c <= y) by lra.
    assert (Hy_le_1 : y <= 1) by lra.
    assert (Hc_y_1 : c <= y <= 1) by lra.

    assert (Hex_cy : ex_RInt f c y).
    {
      apply (ex_RInt_Chasles_1 (V := R_CompleteNormedModule) f c y 1).
      - exact Hc_y_1.
      - exact Hex_c1.
    }

    assert (Hex_y1 : ex_RInt f y 1).
    {
      apply (ex_RInt_Chasles_2 (V := R_CompleteNormedModule) f c y 1).
      - exact Hc_y_1.
      - exact Hex_c1.
    }

    assert (H_chasles : RInt f c 1 = RInt f c y + RInt f y 1).
    {
      symmetry.
      apply (RInt_Chasles (V := R_CompleteNormedModule) f c y 1 Hex_cy Hex_y1).
    }

    assert (H_RInt_c1_eq : RInt f c 1 = I1).
    {
      pose proof (RInt_correct f c 1 Hex_c1) as Hr.
      exact (GammaIntegralConverges.is_RInt_unique f c 1 (RInt f c 1) I1 Hr H_is1).
    }

    assert (H_eq : RInt f c y - I1 = - RInt f y 1).
    {
      rewrite <- H_RInt_c1_eq. rewrite H_chasles. ring.
    }

    rewrite H_eq.
    rewrite Rabs_Ropp.

    rewrite Rmult_comm.
    apply (abs_RInt_le_const f y 1 M).
    - apply Rlt_le; exact Hy_lt_1.
    - exact Hex_y1.
    - intros t [Ht1 Ht2].
      apply Rlt_le.
      apply HM.
      split.
      + apply Rle_trans with y.
        * apply Rlt_le; exact Hy_c_lt.
        * exact Ht1.
      + exact Ht2.
  }

  assert (H_delta : exists delta : R, 0 < delta /\ delta <= 1 - c /\ forall y : R, 1 - delta < y < 1 -> Rabs (RInt f c y - I1) < e).
  {
    destruct (Rle_lt_dec M 0) as [Hm_neg | Hm_pos].
    - assert (Hm_zero : M = 0) by lra.
      exists (1 - c).
      split. { lra. }
      split. { lra. }
      intros y Hy.
      destruct Hy as [Hlow Hhigh].
      assert (H : c < y) by lra.
      pose proof (H_main_ineq y (conj H Hhigh)) as H_ineq.
      rewrite Hm_zero in H_ineq.
      rewrite Rmult_0_l in H_ineq.
      assert (Habs0 : Rabs (RInt f c y - I1) = 0) by (apply Rle_antisym; [exact H_ineq | apply Rabs_pos]).
      rewrite Habs0; exact He_pos.
    - assert (Hm_pos' : 0 < M) by lra.
      set (delta := Rmin (e / M) (1 - c)).
      exists delta.
      split.
      + apply Rmin_pos; [apply Rdiv_lt_0_compat; [exact He_pos | exact Hm_pos'] | lra].
      + split.
        * apply Rmin_r.
        * intros y Hy.
          destruct Hy as [Hlow Hhigh].
          assert (Hdelta_le_1c : delta <= 1 - c) by apply Rmin_r.
          assert (Hc_le_1md : c <= 1 - delta) by lra.
          assert (Hc_lt_y : c < y) by (apply Rle_lt_trans with (1 - delta); [exact Hc_le_1md | exact Hlow]).
          pose proof (H_main_ineq y (conj Hc_lt_y Hhigh)) as H_ineq.
          assert (H1 : 1 - y < delta) by lra.
          assert (H2 : delta <= e / M) by apply Rmin_l.
          assert (H3 : 1 - y < e / M) by (apply Rlt_le_trans with delta; [exact H1 | exact H2]).
          assert (H4 : M * (1 - y) < e).
          { replace e with (M * (e / M)) by (field; apply Rgt_not_eq, Hm_pos').
            apply Rmult_lt_compat_l; [exact Hm_pos' | exact H3]. }
          apply Rle_lt_trans with (M * (1 - y)); [exact H_ineq | exact H4].
  }
  destruct H_delta as [delta [Hdelta_pos [Hdelta_le Hdelta_prop]]].

  set (Q := fun y : R => 1 - delta < y < 1).
  assert (HQ_at_left : at_left 1 Q).
  {
    unfold at_left, within.
    exists (mkposreal delta Hdelta_pos).
    intros y Hy Hy_lt.
    simpl in Hy.
    unfold AbsRing_ball in Hy; simpl in Hy.
    split.
    - assert (Habs : Rabs (y - 1) < delta) by exact Hy.
      rewrite Rabs_left1 in Habs; [| lra].
      replace (- (y - 1)) with (1 - y) in Habs by ring.
      lra.
    - exact Hy_lt.
  }

  apply Filter_prod with (Q := fun x => x = c) (R := Q).
  - unfold at_point; reflexivity.
  - exact HQ_at_left.
  - intros x y Hx Hy.
    subst x.
    assert (Hc_lt_y : c < y) by (destruct Hy as [Hlow Hhigh]; apply Rle_lt_trans with (1 - delta); [| exact Hlow]; lra).
    assert (Hy_lt_1 : y < 1) by (destruct Hy as [Hlow Hhigh]; exact Hhigh).
    assert (Hc_y_1 : c <= y <= 1) by (split; [apply Rlt_le; exact Hc_lt_y | apply Rlt_le; exact Hy_lt_1]).
    assert (Hex_cy : ex_RInt f c y) by (apply (ex_RInt_Chasles_1 f c y 1 Hc_y_1 Hex_c1)).
    pose proof (RInt_correct f c y Hex_cy) as H_is.
    exists (RInt f c y).
    split.
    + exact H_is.
    + apply Heps.
      unfold ball, AbsRing_ball; simpl.
      apply Hdelta_prop.
      exact Hy.
Qed.

(* 积分上限函数的左连续性 *)
Lemma RInt_upper_left_continuous (f : R -> R) (c : R) (I1 : R)
  (Hc_lt_1 : c < 1)
  (Hbound : exists M : R, 0 < M /\ forall t : R, c <= t <= 1 -> Rabs (f t) <= M)
  (H_is1 : is_RInt f c 1 I1) :
  filterlim (fun y : R => RInt f c y) (at_left 1) (locally I1).
Proof.
  intros P [eps Heps].
  set (e := pos eps).
  assert (He_pos : 0 < e) by apply cond_pos.
  destruct Hbound as [M [HM_pos Hbound]].
  set (delta := Rmin (e / M) (1 - c)).
  assert (Hdelta_pos : 0 < delta).
  { apply Rmin_pos.
    - apply Rdiv_lt_0_compat; lra.
    - lra. }
  assert (Hdelta_le_1c : delta <= 1 - c) by apply Rmin_r.
  assert (H_main : forall y : R, c <= y < 1 -> 1 - y < delta -> Rabs (RInt f c y - I1) < e).
  {
    intros y [Hcy Hylt1] H1my_lt_delta.
    assert (Hex_c1 : ex_RInt f c 1) by (exists I1; exact H_is1).
    assert (Hc_y_1 : c <= y <= 1) by (split; [exact Hcy | apply Rlt_le; exact Hylt1]).
    assert (Hex_cy : ex_RInt f c y) by (apply (ex_RInt_Chasles_1 f c y 1 Hc_y_1 Hex_c1)).
    assert (Hex_y1 : ex_RInt f y 1) by (apply (ex_RInt_Chasles_2 f c y 1 Hc_y_1 Hex_c1)).
    pose proof (RInt_Chasles f c y 1 Hex_cy Hex_y1) as Hch.
    assert (H_RInt_c1_eq : RInt f c 1 = I1).
    {
      pose proof (RInt_correct f c 1 Hex_c1) as Hr.
      exact (GammaIntegralConverges.is_RInt_unique f c 1 (RInt f c 1) I1 Hr H_is1).
    }
    assert (H_eq : RInt f c y - I1 = - RInt f y 1).
    {
      rewrite <- H_RInt_c1_eq.
      rewrite <- Hch.
      replace (plus (RInt f c y) (RInt f y 1)) with (RInt f c y + RInt f y 1) by reflexivity.
      ring.
    }
    rewrite H_eq, Rabs_Ropp.
    apply Rle_lt_trans with (M * (1 - y)).
    - rewrite Rmult_comm.
      apply abs_RInt_le_const with (M := M).
      + apply Rlt_le; exact Hylt1.
      + exact Hex_y1.
      + intros t Ht. apply Hbound. split; [lra | exact (proj2 Ht)].
    - replace e with (M * (e / M)) by (field; lra).
      apply Rmult_lt_compat_l; [exact HM_pos | ].
      eapply Rlt_le_trans.
      + apply H1my_lt_delta.
      + apply Rmin_l.
  }
  exists (mkposreal delta Hdelta_pos).
  intros y Hy Hy_lt.
  simpl in Hy.
  assert (H_abs : Rabs (y - 1) < delta) by exact Hy.
  apply Rabs_lt_between in H_abs; destruct H_abs as [Hlow Hhigh].
  assert (H_range : 1 - delta < y < 1) by (split; [lra | exact Hy_lt]).
  assert (H1my_lt_delta : 1 - y < delta) by lra.   (* 从 Hlow 推导 *)
  apply Heps.
  apply H_main.
  - split.
    + assert (Hc_le_1md : c <= 1 - delta) by lra.
      apply Rle_trans with (1 - delta); [exact Hc_le_1md | apply Rlt_le, (proj1 H_range)].
    + exact (proj2 H_range).
  - exact H1my_lt_delta.
Qed.

(* 点滤子是真滤子 *)
Lemma ProperFilter'_at_point (x : R) : ProperFilter' (at_point x).
Proof.
  split.
  - intro H; contradiction.
  - constructor.
    + easy.
    + intros P Q HP HQ; split; assumption.
    + intros P Q Himp HP; apply Himp; assumption.
Qed.

(* 在 (1,∞) 上被积函数的简化形式 *)
Lemma f_simpl_inf (s : Complex) (Hre : 1 < ComplexNumbers.re s) :
  forall t, 1 < t ->
    (match Rlt_dec 0 t with left H => gamma_integrand_real s t H | right _ => 0 end) =
    exp (-t) * Rpower t (ComplexNumbers.re s - 1).
Proof.
  intros t Ht.
  rewrite f_eq_exp_times_Rpower; [| lra].
  reflexivity.
Qed.

(* 在 (1,∞) 上被积函数的非负性 *)
Lemma f_nonneg_inf (s : Complex) (Hre : 1 < ComplexNumbers.re s) :
  forall t, 1 < t ->
    match Rlt_dec 0 t with
    | left H => gamma_integrand_real s t H
    | right _ => 0
    end >= 0.
Proof.
  intros t Ht.
  rewrite f_simpl_inf; auto.
  apply Rle_ge.
  apply Rmult_le_pos.
  - apply Rlt_le, exp_pos.
  - apply Rlt_le, Rpower_pos_1; lra.
Qed.

(* 指数衰减辅助函数 *)
Definition g_inf (t : R) : R := exp (-t / 2).

(* 平方根减对数函数的导数极限 *)
Lemma derivable_pt_lim_f : forall y, 0 < y ->
  derivable_pt_lim (fun x => 2 * sqrt x - ln x) y ((sqrt y - 1) / y).
Proof.
  intros y Hy.
  assert (Hsqrt : derivable_pt_lim sqrt y (/(2 * sqrt y))) by
    (apply derivable_pt_lim_sqrt; exact Hy).
  assert (H2sqrt : derivable_pt_lim (fun x => 2 * sqrt x) y (2 * (/(2 * sqrt y)))).
  { apply derivable_pt_lim_scal with (f := sqrt) (a := 2); exact Hsqrt. }
  assert (Hln : derivable_pt_lim ln y (/ y)) by
    (apply derivable_pt_lim_ln; exact Hy).
  pose proof (derivable_pt_lim_minus
                (fun x => 2 * sqrt x) ln y
                (2 * / (2 * sqrt y)) (/ y) H2sqrt Hln) as Hf.

  assert (Hsqrt_pos : 0 < sqrt y) by (apply sqrt_lt_R0_c; exact Hy).
  assert (H2_sqrt_pos : 0 < 2 * sqrt y) by (apply Rmult_lt_0_compat; [lra | exact Hsqrt_pos]).
  assert (H2_sqrt_neq : 2 * sqrt y <> 0) by (apply Rgt_not_eq; exact H2_sqrt_pos).
  assert (Hsqrt_neq : sqrt y <> 0) by (apply Rgt_not_eq; exact Hsqrt_pos).
  assert (Hy_neq : y <> 0) by (apply Rgt_not_eq; exact Hy).

  assert (Htmp : 2 * / (2 * sqrt y) = / sqrt y).
  {
    rewrite (Rinv_mult 2 (sqrt y)).
    rewrite <- Rmult_assoc.
    rewrite (Rinv_r 2); [| lra].
    rewrite Rmult_1_l.
    reflexivity.
  }
  rewrite Htmp in Hf.

  assert (Htmp2 : sqrt y * / y = / sqrt y).
  {
    apply (Rmult_eq_reg_l (sqrt y)).
    - rewrite <- Rmult_assoc.
      rewrite (sqrt_def y (Rlt_le 0 y Hy)).
      rewrite Rinv_r; [| exact Hy_neq].
      rewrite Rinv_r; [| exact Hsqrt_neq].
      reflexivity.
    - exact Hsqrt_neq.
  }

  assert (Heq : / sqrt y - / y = (sqrt y - 1) / y).
  {
    rewrite <- Htmp2.
    replace (sqrt y * / y - / y) with (sqrt y * / y - 1 * / y).
    - rewrite <- Rmult_minus_distr_r.
      unfold Rdiv; reflexivity.
    - rewrite Rmult_1_l; reflexivity.
  }
  rewrite Heq in Hf.
  exact Hf.
Qed.

(* 平方根减对数函数的可导性 *)
Lemma derivable_pt_f : forall y, 0 < y ->
  derivable_pt (fun x => 2 * sqrt x - ln x) y.
Proof.
  intros y Hy.
  unfold derivable_pt.
  exists ((sqrt y - 1) / y).
  apply derivable_pt_lim_f; assumption.
Qed.

(* 平方根减对数函数的导数值公式 *)
Lemma Hder_val : forall y (Hy : 0 < y),
  derive_pt (fun x => 2 * sqrt x - ln x) y (derivable_pt_f y Hy) = (sqrt y - 1) / y.
Proof.
  intros y Hy.
  apply derive_pt_eq.
  apply derivable_pt_lim_f; assumption.
Qed.

Require Import Stdlib.Reals.Reals.

(* 对数小于等于二倍平方根 *)
Lemma ln_le_2_sqrt : forall t, 0 < t -> ln t <= 2 * sqrt t.
Proof.
  intros t Ht.
  destruct (Rlt_le_dec t 1) as [Ht_lt1 | Ht_ge1].
  - (* t < 1 *)
    assert (Hln_le_ln1 : ln t <= ln 1).
    { apply Rlt_le. apply ln_increasing; [assumption | lra]. }
    rewrite ln_1 in Hln_le_ln1.
    assert (Hsqrt_nonneg : 0 <= 2 * sqrt t) by (apply Rmult_le_pos; [lra | apply sqrt_pos]).
    apply Rle_trans with 0; [assumption | assumption].
  - (* t >= 1 *)
    destruct (Req_dec t 1) as [Ht_eq1 | Ht_gt1].
    + rewrite Ht_eq1; rewrite ln_1, sqrt_1; lra.
    + assert (Ht_gt1' : 1 < t) by lra.
      set (f := fun x => 2 * sqrt x - ln x).
      assert (Hf1 : f 1 = 2) by (unfold f; rewrite sqrt_1, ln_1; ring).
      assert (Hcont_int : forall x, 1 <= x <= t -> continuity_pt f x).
      { intros x Hx. apply derivable_continuous_pt. apply derivable_pt_f; lra. }
      assert (Hder_int : forall x, 1 < x < t -> derivable_pt f x).
      { intros x Hx. apply derivable_pt_f; lra. }
      assert (Hder_eq : forall x (Hx : 1 < x < t), derive_pt f x (Hder_int x Hx) = (sqrt x - 1) / x).
      {
        intros x Hx.
        apply derive_pt_eq.
        assert (Hx_pos : 0 < x) by lra.
        pose proof (derivable_pt_lim_sqrt x Hx_pos) as Hder_sqrt.
        assert (Hder_f1 : derivable_pt_lim (fun y => 2 * sqrt y) x (2 * (/(2 * sqrt x)))).
        { apply (derivable_pt_lim_scal (fun y => sqrt y) 2 x (/(2 * sqrt x))); assumption. }
        assert (H2_neq : 2 <> 0) by lra.
        assert (H_sqrt_neq : sqrt x <> 0) by (apply Rgt_not_eq; apply sqrt_lt_R0_c; lra).
        rewrite (Rinv_mult 2 (sqrt x)) in Hder_f1.
        rewrite <- Rmult_assoc in Hder_f1.
        rewrite (Rinv_r 2 H2_neq) in Hder_f1.
        rewrite Rmult_1_l in Hder_f1.
        pose proof (derivable_pt_lim_ln x Hx_pos) as Hder_ln.
        assert (Hder_f : derivable_pt_lim f x (/ sqrt x - / x)) by (apply derivable_pt_lim_minus; assumption).
        assert (Htmp2 : / sqrt x - / x = (sqrt x - 1) / x).
        {
          assert (Hx_neq0 : x <> 0) by (apply Rgt_not_eq; lra).
          assert (Hsqrt_neq0 : sqrt x <> 0) by (apply Rgt_not_eq; apply sqrt_lt_R0_c; lra).
          assert (Hx_sq : x = sqrt x * sqrt x) by (symmetry; apply sqrt_def; lra).
          replace (/ sqrt x) with (sqrt x / x).
          - rewrite Rdiv_minus_distr.
            unfold Rdiv.
            replace ( - / x) with ( - (1 * / x)) by (rewrite Rmult_1_l; reflexivity).
            rewrite <- Rmult_minus_distr_r.
            ring.
          - unfold Rdiv.
            rewrite Hx_sq.
            rewrite Rinv_mult.
            rewrite <- Rmult_assoc.
            replace (sqrt (sqrt x * sqrt x)) with (sqrt x).
            * rewrite (Rinv_r (sqrt x) Hsqrt_neq0).
              rewrite Rmult_1_l.
              reflexivity.
            * symmetry; apply sqrt_square; apply sqrt_pos.
        }
        rewrite Htmp2 in Hder_f.
        exact Hder_f.
      }
      assert (Hf_inc : forall a b, 1 <= a -> a <= b -> b <= t -> f a <= f b).
      {
        intros a b Ha Hab Hb.
        destruct (Req_dec a b) as [Heq | Hneq].
        - subst; apply Rle_refl.
        - assert (Hlt : a < b) by lra.
          assert (Hcont_ab : forall c, a <= c <= b -> continuity_pt f c).
          { intros c Hc. apply Hcont_int. split; [apply Rle_trans with a; lra | apply Rle_trans with b; lra]. }
          assert (Hder_ab : forall c, a < c < b -> derivable_pt f c).
          { intros c Hc. apply Hder_int. split; [lra | apply Rlt_le_trans with b; lra]. }
          assert (Hder_id : forall c, a < c < b -> derivable_pt (fun x => x) c).
          { intros c _; apply derivable_pt_id. }
          assert (Hcont_id : forall c, a <= c <= b -> continuity_pt (fun x => x) c).
          { intros c _; apply continuity_pt_id. }
          destruct (MVT f (fun x => x) a b Hder_ab Hder_id Hlt Hcont_ab Hcont_id) as [c [Hc1 Hc2]].
          assert (Hder_id_val : derive_pt (fun x => x) c (Hder_id c Hc1) = 1).
          { apply derive_pt_eq; apply derivable_pt_lim_id. }
          rewrite Hder_id_val, Rmult_1_r in Hc2.
          assert (Hfb_fa_eq : f b - f a = (b - a) * derive_pt f c (Hder_ab c Hc1)).
          { rewrite <- Hc2; ring. }
          assert (Hder_c_pos : derive_pt f c (Hder_ab c Hc1) >= 0).
          {
            assert (Hc_gt_1 : 1 < c) by lra.
            assert (Hc_lt_t : c < t) by lra.
            specialize (Hder_eq c (conj Hc_gt_1 Hc_lt_t)) as Heq_c.
            pose proof (pr_nu f c (Hder_ab c Hc1) (Hder_int c (conj Hc_gt_1 Hc_lt_t))) as Heq_der.
            rewrite Heq_der, Heq_c.
            apply Rle_ge.
            apply Rdiv_le_0_compat.
            - assert (1 <= sqrt c).
              { rewrite <- sqrt_1.
                apply sqrt_le_1_c.
                - apply Rle_0_1.
                - apply Rlt_le; lra.
                - apply Rlt_le; exact Hc_gt_1.
              }
              lra.
            - lra.
          }
          assert (Hder_c_pos_le : 0 <= derive_pt f c (Hder_ab c Hc1)) by apply Rge_le, Hder_c_pos.
          assert (0 <= (b - a) * derive_pt f c (Hder_ab c Hc1)).
          { apply Rmult_le_pos; [lra | exact Hder_c_pos_le]. }
          lra.
      }
      pose proof (Hf_inc 1 t (Rle_refl 1) Ht_ge1 (Rle_refl t)) as H_inc.
      unfold f in H_inc.
      rewrite sqrt_1, ln_1 in H_inc.
      lra.
Qed.

(* 对数除以 t 趋于零 *)
Lemma ln_over_t_0 : filterlim (fun t => ln t / t) (Rbar_locally p_infty) (locally 0).
Proof.
  intros P [eps Hball].
  simpl in Hball.
  assert (Heps : 0 < eps) by apply cond_pos.
  set (M := Rmax 1 (Rsqr (2 / eps))).
  assert (HM : forall t, t > M -> t > 1 /\ t > Rsqr (2 / eps)).
  {
    intros t Ht.
    split.
    - apply Rle_lt_trans with M; [apply Rmax_l | exact Ht].
    - apply Rle_lt_trans with M; [apply Rmax_r | exact Ht].
  }
  assert (Hmain : forall t, t > M -> Rabs (ln t / t) < eps).
  {
    intros t Ht.
    destruct (HM t Ht) as [Ht1 Ht2].
    assert (Ht_pos : 0 < t) by lra.
    pose proof (ln_le_2_sqrt t Ht_pos) as Hln_le.
    assert (sqrt_t_neq : sqrt t <> 0) by (apply Rgt_not_eq, sqrt_lt_R0_c, Ht_pos).
    assert (Ht_sq : t = sqrt t * sqrt t) by (symmetry; apply sqrt_def; left; exact Ht_pos).
    assert (Hdiv_eq : / sqrt t = sqrt t * / t).
    {
      apply (Rmult_eq_reg_r (sqrt t)).
      - rewrite Rinv_l; [| exact sqrt_t_neq].
        rewrite Rmult_assoc, (Rmult_comm (/ t) (sqrt t)), <- Rmult_assoc, <- Ht_sq.
        rewrite Rinv_r; [| apply Rgt_not_eq; exact Ht_pos].
        reflexivity.
      - exact sqrt_t_neq.
    }
    assert (Heq : 2 / sqrt t = (2 * sqrt t) * /t) by (unfold Rdiv; rewrite Hdiv_eq; ring).
    assert (Hdiv : ln t / t <= 2 / sqrt t).
    { rewrite Heq; apply Rmult_le_compat_r; [apply Rlt_le, Rinv_0_lt_compat, Ht_pos | exact Hln_le]. }
    assert (Hsqrt_gt : sqrt t > 2 / eps).
    {
      assert (Hpos : 0 < 2 / eps) by (apply Rdiv_lt_0_compat; [lra | apply Heps]).
      assert (Hsqr_ge0 : 0 <= (2 / eps)²) by (apply Rle_0_sqr).
      pose proof (sqrt_lt_1 (2 / eps)² t Hsqr_ge0 (Rlt_le _ _ Ht_pos) Ht2) as Htmp.
      rewrite sqrt_Rsqr in Htmp; [| apply Rlt_le; exact Hpos].
      exact Htmp.
    }
    assert (H2_sqrt : 2 / sqrt t < eps).
    {
      apply Rmult_lt_reg_r with (r := sqrt t); [apply sqrt_lt_R0_c, Ht_pos |].
      unfold Rdiv; rewrite Rmult_assoc, Rinv_l; [| exact sqrt_t_neq].
      rewrite Rmult_1_r, Rmult_comm.
      apply Rmult_lt_compat_r with (r := eps) in Hsqrt_gt; [| apply Heps].
      replace (2 / eps * eps) with 2 in Hsqrt_gt by (field; lra).
      exact Hsqrt_gt.
    }
    assert (Hln_pos : 0 < ln t) by (rewrite <- ln_1; apply ln_increasing; [apply Rlt_0_1 | lra]).
    rewrite Rabs_right.
    - apply Rle_lt_trans with (2 / sqrt t); [exact Hdiv | exact H2_sqrt].
    - apply Rle_ge; apply Rdiv_le_0_compat; [apply Rlt_le, Hln_pos | lra].
  }
  exists M.
  intros t Ht.
  apply Hball.
  unfold ball; simpl.
  unfold AbsRing_ball.
  simpl.
  rewrite Rminus_0_r.
  apply Hmain; assumption.
Qed.

(* 指数函数负无穷极限为零 *)
Lemma filterlim_exp_m_infty : filterlim exp (Rbar_locally m_infty) (locally 0).
Proof.
  apply filterlim_locally.
  intros eps.
  assert (Heps : 0 < pos eps) by apply cond_pos.
  unfold Rbar_locally.
  exists (Rmin (ln (pos eps)) 0).
  intros t Ht.
  unfold ball; simpl.
  unfold AbsRing_ball; simpl.
  rewrite Rminus_0_r.
  rewrite Rabs_pos_eq.
  - destruct (Rle_or_lt (pos eps) 1) as [Heps_le1 | Heps_gt1].
    + assert (Hln_le0 : ln (pos eps) <= ln 1).
      { apply ln_le; [apply Heps | apply Heps_le1]. }
      rewrite ln_1 in Hln_le0.
      assert (Ht_lt_ln : t < ln (pos eps)).
      { eapply Rlt_le_trans; [apply Ht | apply Rmin_l]. }
      rewrite <- (exp_ln (pos eps) Heps).
      apply exp_increasing.
      exact Ht_lt_ln.
    + assert (Ht_lt_0 : t < 0) by (eapply Rlt_le_trans; [apply Ht | apply Rmin_r]).
      assert (exp t < 1).
      { apply exp_increasing in Ht_lt_0. rewrite exp_0 in Ht_lt_0. exact Ht_lt_0. }
      apply Rlt_trans with (1 := H) (2 := Heps_gt1).
  - apply Rlt_le, exp_pos.
Qed.

(* 正幂指数衰减的无穷远极限 *)
Lemma phi_limit_0 (a : R) (Ha : 0 < a) :
  filterlim (fun t => Rpower t a * exp (- t / 2)) (Rbar_locally p_infty) (locally 0).
Proof.
  assert (Heq_loc : Rbar_locally p_infty (fun t => Rpower t a * exp (- t / 2) = exp (a * ln t - t / 2))).
  {
    apply filter_imp with (P := fun t => 0 < t).
    - intros t Ht_pos.
      unfold Rpower.
      rewrite <- exp_plus.
      f_equal.
      rewrite Rminus_def.
      rewrite <- Rdiv_opp_l.
      reflexivity.
    - unfold Rbar_locally; exists 0; intros t Ht; exact Ht.
  }
  assert (Hlim_exp : filterlim (fun t => exp (a * ln t - t / 2)) (Rbar_locally p_infty) (locally 0)).
  {
    assert (H1 : filterlim (fun t => a * ln t - t / 2) (Rbar_locally p_infty) (Rbar_locally m_infty)).
    {
      intros P [M HM].
      assert (Heps : 0 < 1 / (4 * a)).
      { apply Rdiv_lt_0_compat; [lra | apply Rmult_lt_0_compat; [lra | lra]]. }
      pose proof (ln_over_t_0) as Hln0.
      assert (Hball0 : locally 0 (ball 0 (mkposreal (1/(4*a)) Heps))) by (apply locally_ball).
      specialize (Hln0 (ball 0 (mkposreal (1/(4*a)) Heps)) Hball0).
      unfold Rbar_locally in Hln0; destruct Hln0 as [T1 Hcond].
      set (T := Rmax T1 (4 * Rabs M)).
      assert (T_ge_0 : 0 <= T).
      { unfold T. apply Rle_trans with (4 * Rabs M).
        - apply Rmult_le_pos; [lra | apply Rabs_pos].
        - apply Rmax_r. }
      exists T.
      intros t Ht.
      assert (Ht_ge_T1 : t > T1) by (apply Rle_lt_trans with T; [apply Rmax_l | exact Ht]).
      assert (Ht_ge_4Mabs : t > 4 * Rabs M) by (apply Rle_lt_trans with T; [apply Rmax_r | exact Ht]).
      assert (Ht_pos : 0 < t) by (apply Rle_lt_trans with T; [exact T_ge_0 | exact Ht]).
      
      specialize (Hcond t Ht_ge_T1).
      unfold ball, AbsRing_ball, minus, opp in Hcond; simpl in Hcond.
      apply Rabs_lt_between' in Hcond.
      destruct Hcond as [Hln_neg Hln_pos].

      rewrite Rplus_0_l in Hln_pos.
      apply Rmult_lt_compat_l with (r := a) in Hln_pos; [| lra].
      replace (a * (1 / (4 * a))) with (1/4) in Hln_pos by (field; lra).
      apply Rmult_lt_compat_r with (r := t) in Hln_pos; [| lra].
      replace (a * (ln t / t) * t) with (a * ln t) in Hln_pos by (field; lra).
      replace (1 / 4 * t) with (t / 4) in Hln_pos by (field; lra).

      assert (Htmp : a * ln t - t / 2 < - t / 4) by lra.

      assert (Hcmp : - t / 4 < M).
      {
        destruct (Rle_lt_dec 0 M) as [Hpos | Hneg].
        - lra.
        - assert (Habs : Rabs M = - M) by (apply Rabs_left; lra).
          assert (Ht4_gt_abs : t / 4 > Rabs M).
          {
            apply Rmult_lt_reg_l with 4; [lra |].
            replace (4 * (t / 4)) with t by field.
            exact Ht_ge_4Mabs.
          }
          rewrite Habs in Ht4_gt_abs.
          lra.
      }
      assert (Hfinal : a * ln t - t / 2 < M) by (apply Rlt_trans with (- t / 4); [exact Htmp | exact Hcmp]).
      apply HM; exact Hfinal.
    }
    apply filterlim_comp with (f := fun t => a * ln t - t / 2) (g := exp) (G := Rbar_locally m_infty).
    + exact H1.
    + exact filterlim_exp_m_infty.
  }
  apply filterlim_ext_loc with (f := fun t => exp (a * ln t - t / 2)) (g := fun t => Rpower t a * exp (- t / 2)).
  - apply filter_imp with (P := fun t => Rpower t a * exp (- t / 2) = exp (a * ln t - t / 2)).
    + intros t Heq; symmetry; exact Heq.
    + exact Heq_loc.
  - exact Hlim_exp.
Qed.

(* 积分核实部的指数上界估计 *)
Lemma f_bound_by_g_inf (s : Complex) (Hre : 1 < ComplexNumbers.re s) :
  exists C : R, 0 < C /\
    forall t, 1 <= t ->
      match Rlt_dec 0 t with left H => gamma_integrand_real s t H | right _ => 0 end
      <= C * g_inf t.
Proof.
  set (a := ComplexNumbers.re s - 1).
  assert (Ha : 0 < a) by (unfold a; lra).

  assert (Hf_eq : forall t, 1 <= t -> 
    match Rlt_dec 0 t with left H => gamma_integrand_real s t H | right _ => 0 end = exp (-t) * Rpower t a).
  {
    intros t Ht.
    assert (Ht_pos : 0 < t) by lra.
    rewrite f_eq_exp_times_Rpower; [| exact Ht_pos].
    reflexivity.
  }

  pose (phi := fun t => Rpower t a * exp (-t/2)).
  pose (g_inf := fun t => exp (-t/2)).

  pose proof (phi_limit_0 a Ha) as Hlim.

  assert (Hlim_eps : forall eps : posreal, exists T, forall t, t > T -> Rabs (phi t) < eps).
  {
    intros eps.
    assert (Hball : locally 0 (ball 0 eps)) by apply locally_ball.
    specialize (Hlim (ball 0 eps) Hball).
    unfold Rbar_locally in Hlim.
    destruct Hlim as [T HT].
    exists T.
    intros t Ht.
    specialize (HT t Ht).
    unfold ball in HT; simpl in HT.
    rewrite <- (Rminus_0_r (phi t)).
    exact HT.
  }
  specialize (Hlim_eps (mkposreal 1 Rlt_0_1)) as [T HT].
  simpl in HT.
  assert (HT' : forall t, t > T -> phi t <= 1).
  {
    intros t Ht.
    specialize (HT t Ht).
    apply Rabs_lt_between in HT.
    destruct HT as [_ Hpos].
    apply Rlt_le, Hpos.
  }

  assert (Hcont_phi : forall t, 1 <= t <= T -> continuous phi t).
  {
    intros t0 [Hlow Hhigh].
    apply continuity_pt_to_continuous.
    apply continuity_pt_mult.
    - apply continuity_pt_Rpower_pos; [exact Ha | lra].
    - apply continuity_pt_comp with (f1 := fun t => - t / 2) (f2 := exp).
      + apply derivable_continuous_pt.
        apply (derivable_pt_div (fun t => - t) (fun t => 2) t0).
        * apply derivable_pt_opp; apply derivable_pt_id.
        * apply derivable_pt_const.
        * apply Rgt_not_eq; lra.
      + apply derivable_continuous_pt.
        apply derivable_pt_exp.
  }

  assert (Hbound : exists C, 0 < C /\ forall t, 1 <= t -> phi t <= C).
  {
    destruct (Rle_or_lt T 1) as [Hle | Hgt].
    - exists 1.
      split; [lra |].
      intros t Ht.
      destruct (Rle_or_lt t T) as [Hle_t | Hgt_t].
      + assert (t = 1).
        { apply Rle_antisym.
          - apply Rle_trans with T; [exact Hle_t | exact Hle].
          - exact Ht.
        }
        subst t.
        unfold phi.
        rewrite Rpower_1_r.
        rewrite Rmult_1_l.
        apply Rlt_le.
        rewrite <- exp_0.
        apply exp_increasing.
        rewrite exp_0.
        lra.
      + apply HT' in Hgt_t; assumption.
    - Import PrimeEmbedding.
      assert (Hphi_nonneg : forall t, 1 <= t -> 0 <= phi t).
      { intros t0 Ht0. unfold phi. apply Rmult_le_pos; [apply Rlt_le, Rpower_pos; lra | apply Rlt_le, exp_pos]. }
      destruct (bounded_continuity phi 1 T Hcont_phi) as [M HM].
      exists (Rmax M 1).
      split.
      { apply Rlt_le_trans with 1; [apply Rlt_0_1 | apply Rmax_r]. }
      intros t Ht.
      destruct (Rle_or_lt t T) as [Hle_t | Hgt_t].
      + specialize (HM t (conj Ht Hle_t)) as Hlt.
        assert (phi_nonneg_t : 0 <= phi t) by (apply Hphi_nonneg; exact Ht).
        rewrite Rabs_pos_eq in Hlt; [| exact phi_nonneg_t].
        apply Rle_trans with M; [apply Rlt_le; exact Hlt | apply Rmax_l].
      + apply HT' in Hgt_t.
        apply Rle_trans with 1; [exact Hgt_t | apply Rmax_r].
  }

  destruct Hbound as [C [HC Hphi_bound]].
  exists C.
  split; [exact HC |].
  intros t Ht.
  rewrite Hf_eq; [| exact Ht].
  unfold phi, g_inf.
  assert (Hexp : exp (-t) = exp (-t/2) * exp (-t/2)).
  { rewrite <- exp_plus. f_equal. lra. }
  rewrite Hexp.
  rewrite Rmult_assoc.
  replace (exp (-t/2) * Rpower t a) with (phi t) by (unfold phi; ring).
  rewrite (Rmult_comm (exp (-t/2)) (phi t)).
  apply Rmult_le_compat_r.
  - apply Rlt_le, exp_pos.
  - exact (Hphi_bound t Ht).
Qed.

(* 通用上界估计 *)
Lemma f_bound_inf_general (s : Complex) (Hre : 1 < ℜ(s)) :
  let f := fun t => match Rlt_dec 0 t with left H => gamma_integrand_real s t H | right _ => 0 end in
  let g_inf := fun t => exp (- t / 2) in
  exists M, forall t, 1 <= t -> f t <= M * g_inf t.
Proof.
  destruct (f_bound_by_g_inf s Hre) as [M [HM Hbound]].
  exists M.
  exact Hbound.
Qed.

(* g_inf的连续性 *)
Lemma continuous_g_inf : forall x, continuous g_inf x.
Proof.
  intros x.
  apply continuity_pt_to_continuous.
  apply derivable_continuous_pt.
  set (l1 := - /2).
  set (l2 := exp (- x / 2)).

  assert (Hder1 : derivable_pt_lim (fun t => - t / 2) x l1).
  {
    assert (Htmp : derivable_pt_lim (fun t => l1 * t) x (l1 * 1)).
    { apply derivable_pt_lim_scal with (a := l1) (f := fun t => t) (x := x).
      apply derivable_pt_lim_id. }
    rewrite Rmult_1_r in Htmp.
    apply (derivable_pt_lim_ext (fun t => l1 * t) (fun t => - t / 2) x l1).
    - intros t; unfold l1; field.
    - exact Htmp.
  }

  assert (Hder2 : derivable_pt_lim exp (- x / 2) l2).
  { apply derivable_pt_lim_exp. }

  pose proof (derivable_pt_lim_comp (fun t => - t / 2) exp x l1 l2 Hder1 Hder2) as Hcomp.
  exists (l2 * l1).
  exact Hcomp.
Qed.

(* g_inf在区间上的可积性 *)
Lemma g_inf_integrable_on_interval (a b : R) : ex_RInt g_inf a b.
Proof.
  apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
  intros z _; apply continuous_g_inf.
Qed.

(* g_inf的可积性 *)
Lemma g_inf_integrable :
  ex_RInt_gen g_inf (Rbar_locally 1) (Rbar_locally p_infty).
Proof.
  set (F := fun t : R => -2 * exp (- t / 2)).
  assert (Hder : forall t : R, is_derive F t (g_inf t)).
  {
    intros t.
    apply is_derive_Reals.
    unfold F, g_inf.

    assert (H_id : derivable_pt_lim (fun u => u) t 1) by apply derivable_pt_lim_id.
    assert (H_opp : derivable_pt_lim (fun u => - u) t (-1))
      by (apply derivable_pt_lim_opp; exact H_id).
    assert (H_u_scaled : derivable_pt_lim (fun u => /2 * (- u)) t ((/2) * (-1))).
      apply derivable_pt_lim_scal with (a := /2); exact H_opp.
    assert (H_u_eq : forall u, /2 * (- u) = - u / 2).
      intros; unfold Rdiv; rewrite Rmult_comm; reflexivity.

    assert (H_u : derivable_pt_lim (fun u => - u / 2) t (-/2)).
    {
      replace (-/2) with (/2 * -1) by (field; lra).
      apply (derivable_pt_lim_ext _ _ _ _ H_u_eq H_u_scaled).
    }

    assert (H_exp_u : derivable_pt_lim (fun t => exp (- t / 2)) t (exp (- t / 2) * (-/2))).
      apply derivable_pt_lim_comp with (f1 := fun u => - u / 2) (f2 := exp) (x := t);
        [exact H_u | apply derivable_pt_lim_exp].

    assert (H_F : derivable_pt_lim (fun t => -2 * exp (- t / 2)) t
                (-2 * (exp (- t / 2) * (-/2)))).
      apply derivable_pt_lim_scal with (a := -2); exact H_exp_u.

    assert (Heq : -2 * (exp (- t / 2) * (-/2)) = exp (- t / 2)).
    { field; lra. }
    rewrite Heq in H_F.
    exact H_F.
  }

  assert (Hcont_g : forall x : R_UniformSpace, continuous g_inf x) by apply continuous_g_inf.

  assert (g_integrable_on_interval : forall a b, ex_RInt g_inf a b).
  {
    intros a b.
    apply (ex_RInt_continuous (V := R_CompleteNormedModule) g_inf a b).
    intros z _; apply Hcont_g.
  }

  assert (H_RInt_eq : forall a b, ex_RInt g_inf a b -> RInt g_inf a b = F b - F a).
  {
    intros a b Hex.
    assert (H_is : is_RInt g_inf a b (F b - F a)).
    {
      apply is_RInt_derive with (f := F) (df := g_inf) (a := a) (b := b).
      - intros x _. apply Hder.
      - intros x _. apply Hcont_g.
    }
    apply (is_RInt_unique g_inf a b (F b - F a) H_is).
  }

  set (I := 2 * exp (- (1/2))).
  assert (I_eq : I = - F 1).
  {
    unfold I, F.
    simpl.
    replace (- (1)/2) with (- (1/2)) by lra.
    rewrite Ropp_mult_distr_l.
    assert (H_opp2 : - -2 = 2) by apply Ropp_involutive.
    rewrite H_opp2.
    reflexivity.
  }

  assert (HcontF : forall x, continuity_pt F x).
  { intros x; apply derivable_continuous_pt; exists (g_inf x); apply is_derive_Reals, Hder. }

  assert (Hlim_right : filterlim (fun y => RInt g_inf 1 y) (Rbar_locally p_infty) (locally I)).
  {
    assert (Hlim_F0 : filterlim F (Rbar_locally p_infty) (locally 0)).
    {
      unfold F.
      assert (H_neg_half : filterlim (fun y => - y / 2) (Rbar_locally p_infty) (Rbar_locally m_infty)).
      {
        intros P HP. simpl in HP.
        destruct HP as [M HM].
        exists (-2 * M).
        intros y Hy.
        apply HM.
        lra.
      }
      assert (H1 : filterlim (fun y => exp (- y / 2)) (Rbar_locally p_infty) (locally 0)).
      {
        eapply filterlim_comp.
        - exact H_neg_half.
        - exact filterlim_exp_m_infty.
      }
      assert (H_scal : filterlim (fun x => -2 * x) (locally 0) (locally 0)).
      {
        apply filterlim_locally.
        intros eps.
        set (d := pos eps / 2).
        assert (Hd : 0 < d).
        { unfold d; apply Rdiv_lt_0_compat; [apply cond_pos | lra]. }
        exists (mkposreal d Hd).
        intros x Hx.
        unfold ball, AbsRing_ball in *; simpl in *.
        replace (AbsRing_ball R_AbsRing 0 eps (-2 * x)) with (Rabs (-2 * x - 0) < eps) by reflexivity.
        rewrite Rminus_0_r.
        rewrite Rabs_mult.
        assert (Hr : Rabs (-2) = Rabs 2) by apply Rabs_Ropp.
        rewrite Hr.
        rewrite Rabs_pos_eq; [| lra].
        replace (Rabs 2) with 2; [| rewrite Rabs_pos_eq; [reflexivity | lra]].
        unfold AbsRing_ball in Hx; rewrite Rminus_0_r in Hx.
        apply Rmult_lt_compat_l with (r := 2) in Hx; [| apply Rlt_0_2].
        replace (2 * d) with (pos eps) in Hx by (unfold d; field; lra).
        exact Hx.
      }
      eapply filterlim_comp.
      - exact H1.
      - exact H_scal.
    }

    intros P [eps Hball]; simpl in Hball.
    assert (Heps : 0 < pos eps) by apply cond_pos.
    assert (Hloc0 : locally 0 (ball 0 eps)).
    { exists eps; intros y Hy; exact Hy. }
    specialize (Hlim_F0 (ball 0 eps) Hloc0) as [A HA].
    exists A.
    intros y Hy.
    assert (Hex_1y : ex_RInt g_inf 1 y) by apply g_integrable_on_interval.
    rewrite (H_RInt_eq 1 y Hex_1y).
    apply Hball.
    assert (Hball_abs : forall x e y, ball x e y <-> Rabs (y - x) < e).
    { intros; unfold ball, AbsRing_ball; reflexivity. }
    rewrite Hball_abs.
    rewrite I_eq.
    replace ((F y - F 1) - (- F 1)) with (F y) by ring.
    specialize (HA y Hy).
    rewrite Hball_abs in HA.
    rewrite Rminus_0_r in HA.
    exact HA.
  }

  assert (Hlim_left : filterlim (fun x => RInt g_inf x 1) (Rbar_locally 1) (locally 0)).
  {
    intros Q [eps Hball]; simpl in Hball.
    assert (Heps : 0 < pos eps) by apply cond_pos.
    destruct (HcontF 1 (pos eps) Heps) as [delta [Hdelta_pos Hdelta]].
    exists (mkposreal delta Hdelta_pos).
    intros x Hx.
    assert (Hex : ex_RInt g_inf x 1) by apply g_integrable_on_interval.
    rewrite (H_RInt_eq x 1 Hex).
    destruct (Req_dec x 1) as [Heq | Hneq].
    - subst x.
      replace (F 1 - F 1) with 0 by ring.
      apply Hball.
      apply ball_center.
    - apply Hball.
      unfold ball; simpl.
      unfold AbsRing_ball; simpl.
      rewrite Rminus_0_r.
      rewrite Rabs_minus_sym.
      apply Hdelta.
      split; [split; [exact Logic.I | exact (not_eq_sym Hneq)] |].
      unfold dist, R_met; simpl.
      exact Hx.
  }

  assert (H_is_left : is_RInt_gen g_inf (Rbar_locally 1) (at_point 1) 0).
  {
    unfold is_RInt_gen.
    intros P HP.
    specialize (Hlim_left P HP) as [A HA].
    set (Q := fun x => ball 1 A x).
    set (R := fun y => y = 1).
    assert (HQ : Rbar_locally 1 Q).
    { unfold Rbar_locally; exists A; intros x Hx; exact Hx. }
    assert (HR : at_point 1 R) by (unfold at_point; reflexivity).
    apply Filter_prod with (Q := Q) (R := R); [exact HQ | exact HR | ].
    intros x y Hx Hy.
    rewrite Hy.
    assert (Hex : ex_RInt g_inf x 1) by apply g_integrable_on_interval.
    pose proof (RInt_correct g_inf x 1 Hex) as H_is.
    exists (RInt g_inf x 1); split; [exact H_is | apply HA; exact Hx].
  }

  assert (H_is_right : is_RInt_gen g_inf (at_point 1) (Rbar_locally p_infty) I).
  {
    unfold is_RInt_gen.
    intros P HP.
    specialize (Hlim_right P HP) as [A HA].
    set (Q := fun x => x = 1).
    set (R := fun y => y > A).
    assert (HQ : at_point 1 Q) by (unfold at_point; reflexivity).
    assert (HR : Rbar_locally p_infty R).
    { unfold Rbar_locally; exists A; intros y Hy; exact Hy. }
    apply Filter_prod with (Q := Q) (R := R); [exact HQ | exact HR | ].
    intros x y Hx Hy.
    rewrite Hx.
    assert (Hex : ex_RInt g_inf 1 y) by apply g_integrable_on_interval.
    pose proof (RInt_correct g_inf 1 y Hex) as H_is.
    exists (RInt g_inf 1 y); split; [exact H_is | apply HA; exact Hy].
  }

  apply (ex_RInt_gen_Chasles g_inf 1).
  - apply (is_RInt_gen_to_ex_RInt_gen _ _ _ 0 H_is_left).
  - apply (is_RInt_gen_to_ex_RInt_gen _ _ _ I H_is_right).
Qed.


(* f的柯西收敛性(比较法) *)
Lemma f_cauchy_from_comparison (s : Complex) (Hre : 1 < ℜ(s)) :
  let f := fun t => match Rlt_dec 0 t with left H => gamma_integrand_real s t H | right _ => 0 end in
  let g := fun t => exp (- t / 2) in
  exists C : R, 0 < C /\ (forall t, 1 <= t -> f t <= C * g t) /\
  forall eps : R, eps > 0 -> exists M : R, M > 1 /\
    forall a b, a > M -> b > a -> RInt f a b < eps.
Proof.
  intros f g.
  destruct (f_bound_by_g_inf s Hre) as [C [HC Hbound]].
  assert (g_eq : g_inf = g). {
    apply functional_extensionality; intros t.
    unfold g, g_inf; reflexivity.
  }
  rewrite g_eq in Hbound.
  exists C. split; [exact HC | split; [exact Hbound | ]].
  intros eps Heps.
  set (eps1 := eps / (2 * C)).
  assert (Heps1 : 0 < eps1) by (apply Rdiv_lt_0_compat; [exact Heps | apply Rmult_lt_0_compat; [lra | exact HC]]).
  assert (HF1 : Filter (Rbar_locally 1)) by apply filter_filter.
  assert (HF2 : Filter (Rbar_locally p_infty)) by apply filter_filter.
  destruct (g_inf_integrable) as [Ig HIsg].
  rewrite g_eq in HIsg.
  pose proof (is_RInt_gen_filterlim g (Rbar_locally 1) (Rbar_locally p_infty) Ig HF1 HF2 HIsg) as Hlim_g.
  set (φ := fun y : R => (1, y)).
  assert (H_φ : filterlim φ (Rbar_locally p_infty) (filter_prod (Rbar_locally 1) (Rbar_locally p_infty))).
  {
    apply filterlim_pair.
    - apply filterlim_const.
    - apply filterlim_id.
  }
  assert (H_lim_g1 : filterlim (fun y => RInt g 1 y) (Rbar_locally p_infty) (locally Ig)).
  {
    apply (filterlim_comp R (R * R) R φ (fun ab => RInt g (fst ab) (snd ab))
                          (Rbar_locally p_infty)
                          (filter_prod (Rbar_locally 1) (Rbar_locally p_infty))
                          (locally Ig)).
    - exact H_φ.
    - exact Hlim_g.
  }
  rewrite filterlim_locally in H_lim_g1.
  specialize (H_lim_g1 (mkposreal eps1 Heps1)).
  destruct H_lim_g1 as [M0 HM0].
  set (M := Rmax M0 1 + 1).
  exists M.
  split.
  - assert (H1_le_max : 1 <= Rmax M0 1) by apply Rmax_r.
    unfold M; lra.
  - intros a b Ha Hb.
    pose proof (Rmax_l M0 1) as Hmax_ge.
    pose proof (Rmax_r M0 1) as Hmax_ge1.
    assert (M_gt_M0 : M > M0) by (unfold M; lra).
    assert (M_gt_1 : M > 1) by (unfold M; lra).
    assert (Ha_gt_M0 : a > M0) by lra.
    assert (Hb_gt_M0 : b > M0) by lra.
    assert (Ha_gt_1 : a > 1) by lra.
    assert (Hb_gt_1 : b > 1) by lra.
    assert (Hage1 : a >= 1) by lra.
    assert (Hbge1 : b >= 1) by lra.

    assert (Hcont_g : forall x, continuous g x) by (intros x; rewrite <- g_eq; apply continuous_g_inf).
    assert (Hex_f_ab : ex_RInt f a b).
    {
      apply ex_RInt_continuous with (f := f) (a := a) (b := b).
      intros z Hz.
      assert (a_le_b : a <= b) by lra.
      assert (Hmin_eq : Rmin a b = a) by (apply Rmin_left; exact a_le_b).
      rewrite Hmin_eq in Hz.
      assert (Ha_pos : 0 < a) by lra.
      assert (Hz_pos : 0 < z).
      {
        apply Rlt_le_trans with a.
        - exact Ha_pos.
        - destruct Hz as [H1 _]; exact H1.
      }
      pose (h := fun t => exp (-t) * Rpower t (ℜ(s) - 1)).
      assert (Hloc_eq : locally z (fun t => f t = h t)).
      {
        apply locally_iff_open_ball.
        exists (z/2).
        split; [lra |].
        intros y Hy.
        assert (H_abs : Rabs (y - z) < z/2) by exact Hy.
        apply Rabs_lt_between in H_abs.
        destruct H_abs as [Hlow Hhigh].
        assert (Hz2_pos : 0 < z/2) by lra.
        assert (H_y_gt_z2 : z/2 < y) by lra.
        assert (H_y_pos : 0 < y) by lra.
        unfold f.
        destruct (Rlt_dec 0 y) as [Hpos|Hneg]; [|lra].
        unfold gamma_integrand_real, real_pow, h; simpl.
        unfold Rpower.
        rewrite <- exp_plus.
        f_equal.
      }
      assert (Hcont_h_pt : continuity_pt h z).
      {
        unfold h.
        apply continuity_pt_mult.
        - apply continuity_pt_comp with (f1 := fun t => -t) (f2 := exp) (x := z).
          + apply continuity_pt_opp; apply continuity_pt_id.
          + apply derivable_continuous_pt; apply derivable_pt_exp.
        - apply continuity_pt_Rpower_pos.
          * apply Rgt_minus; exact Hre.
          * exact Hz_pos.
      }
      assert (Hcont_h : continuous h z) by (apply continuity_pt_to_continuous; exact Hcont_h_pt).
      apply continuous_ext_loc with (g := h) (x := z).
      - apply filter_imp with (P := fun t => f t = h t).
        + intros t Heq. symmetry. exact Heq.
        + exact Hloc_eq.
      - exact Hcont_h.
    }
    assert (Hex_g_ab : ex_RInt g a b).
    { apply ex_RInt_continuous with (f := g) (a := a) (b := b).
      intros z Hz; apply Hcont_g. }
    assert (Hex_g_1a : ex_RInt g 1 a).
    { apply ex_RInt_continuous with (f := g) (a := 1) (b := a).
      intros z Hz; apply Hcont_g. }
    assert (Hex_g_1b : ex_RInt g 1 b).
    { apply ex_RInt_continuous with (f := g) (a := 1) (b := b).
      intros z Hz; apply Hcont_g. }

    assert (Hle_fg : RInt f a b <= C * RInt g a b).
    {
      assert (Htemp : RInt f a b <= RInt (fun t => C * g t) a b).
      {
        apply RInt_le with (f := f) (g := fun t => C * g t) (a := a) (b := b); try lra.
        - exact Hex_f_ab.
        - apply ex_RInt_scal with (k := C) in Hex_g_ab; exact Hex_g_ab.
        - intros t Ht. destruct Ht as [Ht1 Ht2].
          assert (H1_le_a : 1 <= a) by apply Rge_le, Hage1.
          assert (H1_le_t : 1 <= t).
          { apply Rle_trans with a; [exact H1_le_a | apply Rlt_le; exact Ht1]. }
          apply (Hbound t H1_le_t).
      }
      assert (Heq : RInt (fun t => C * g t) a b = C * RInt g a b).
      { apply (RInt_scal g a b C Hex_g_ab). }
      rewrite Heq in Htemp; exact Htemp.
    }

    assert (H_chasles_g : RInt g a b = RInt g 1 b - RInt g 1 a).
    {
      pose proof (RInt_Chasles g 1 a b Hex_g_1a Hex_g_ab) as H1.
      rewrite Rplus_comm in H1.
      rewrite <- H1.
      lra.
    }

    assert (Hpos_diff : RInt g 1 b - RInt g 1 a >= 0).
    {
      rewrite <- H_chasles_g.
      apply Rle_ge.
      apply RInt_ge_0; [lra | exact Hex_g_ab |].
      intros t Ht; apply Rlt_le, exp_pos.
    }

    assert (H1 : RInt f a b <= C * (Rabs (RInt g 1 b - Ig) + Rabs (RInt g 1 a - Ig))).
    {
      apply Rle_trans with (C * (RInt g 1 b - RInt g 1 a)).
      - rewrite <- H_chasles_g. exact Hle_fg.
      - apply Rmult_le_compat_l; [apply Rlt_le, HC |].
        assert (Htemp : RInt g 1 b - RInt g 1 a <= Rabs (RInt g 1 b - Ig) + Rabs (RInt g 1 a - Ig)).
        {
          apply Rle_trans with (Rabs (RInt g 1 b - RInt g 1 a)).
          * apply Rle_abs.
          * apply Rle_trans with (Rabs (RInt g 1 b - Ig) + Rabs (Ig - RInt g 1 a)).
            + replace (RInt g 1 b - RInt g 1 a) with ((RInt g 1 b - Ig) + (Ig - RInt g 1 a)) by ring.
              apply Rabs_triang.
            + apply Rplus_le_compat_l.
              rewrite Rabs_minus_sym.
              apply Rle_refl.
        }
        exact Htemp.
    }

    apply Rle_lt_trans with (C * (Rabs (RInt g 1 b - Ig) + Rabs (RInt g 1 a - Ig))).
    - exact H1.
    - replace eps with (C * (eps / C)).
      + apply Rmult_lt_compat_l; [exact HC |].
        replace (eps / C) with (2 * eps1) by (unfold eps1; field; lra).
        replace (2 * eps1) with (eps1 + eps1) by lra.
        assert (Habs_b : Rabs (RInt g 1 b - Ig) < eps1) by (apply HM0, Hb_gt_M0).
        assert (Habs_a : Rabs (RInt g 1 a - Ig) < eps1) by (apply HM0, Ha_gt_M0).
        apply Rplus_lt_compat; [exact Habs_b | exact Habs_a].
      + field; lra.
Qed.

(* Gamma积分上极限存在 *)
Lemma f_upper_limit_exists (s : Complex) (Hre : 1 < ℜ(s)) :
  let f := fun t => match Rlt_dec 0 t with left H => gamma_integrand_real s t H | right _ => 0 end in
  exists L : R, filterlim (fun y => RInt f 1 y) (Rbar_locally p_infty) (locally L).
Proof.
  intros f.
  pose proof (f_cauchy_from_comparison s Hre) as [C [HC [Hbound Hcauchy]]].
  assert (HF : ProperFilter (Rbar_locally p_infty)) by apply Rbar_locally_filter.
  set (F := filtermap (fun y => RInt f 1 y) (Rbar_locally p_infty)).

  assert (Hcont_f_gt0 : forall t, 0 < t -> continuous f t).
  {
    intros t Ht.
    set (a := ℜ(s) - 1).
    assert (Ha : 0 < a) by (apply Rgt_minus; exact Hre).
    set (g := fun x => exp (- x) * Rpower x a).

    assert (Hloc_eq : locally t (fun x => f x = g x)).
    {
      apply locally_iff_open_ball.
      exists (t / 2). split; [lra |].
      intros y Hy.
      assert (Hy_pos : 0 < y) by (apply Rabs_lt_between in Hy; lra).
      unfold f.
      destruct (Rlt_dec 0 y) as [Hpos | Hneg]; [| contradiction Hneg].
      unfold gamma_integrand_real; simpl.
      unfold real_pow, Rpower.
      unfold g, a.
      reflexivity.
    }

    assert (Hcont_g : continuous g t).
    {
      apply continuity_pt_to_continuous.
      apply continuity_pt_mult.
      - apply continuity_pt_comp with (f1 := fun x => - x) (f2 := exp).
        + apply continuity_pt_opp; apply continuity_pt_id.
        + apply derivable_continuous_pt; apply derivable_pt_exp.
      - apply continuity_pt_Rpower_pos; [exact Ha | exact Ht].
    }

    apply continuous_ext_loc with (g := g) (x := t).
    - apply filter_imp with (P := fun x => f x = g x) (Q := fun x => g x = f x).
      + intros x Heq; symmetry; exact Heq.
      + exact Hloc_eq.
    - exact Hcont_g.
  }

  assert (Hf_nonneg : forall t, 0 < t -> 0 <= f t).
  {
    intros t Ht.
    unfold f.
    destruct (Rlt_dec 0 t) as [Hpos | Hneg]; [| contradiction Hneg].
    unfold gamma_integrand_real; simpl.
    unfold real_pow, Rpower.
    apply Rmult_le_pos; apply Rlt_le, exp_pos.
  }

  assert (H_cauchy_f : cauchy F).
  {
    intros eps.
    destruct (Hcauchy (pos eps) (cond_pos eps)) as [M [Hgt1 Hcond]].
    set (N0 := M + 1).
    assert (N0_gt_M : N0 > M) by (unfold N0; lra).
    set (x := RInt f 1 N0).
    exists x.
    unfold F, filtermap.
    unfold Rbar_locally.
    exists N0.
    intros y Hy.
    assert (Hy_gt_N0 : y > N0) by exact Hy.
    assert (Hy_gt_M : y > M) by lra.

    assert (Hex_1N0 : ex_RInt f 1 N0).
    {
      apply (@ex_RInt_continuous R_CompleteNormedModule f 1 N0).
      intros z Hz.
      assert (Hmin : Rmin 1 N0 = 1) by (apply Rmin_left; lra).
      assert (Hmax : Rmax 1 N0 = N0) by (apply Rmax_right; lra).
      rewrite Hmin, Hmax in Hz.
      destruct Hz as [Hz1 Hz2].
      assert (Hz_pos : 0 < z) by lra.
      apply Hcont_f_gt0; exact Hz_pos.
    }
    assert (Hex_N0y : ex_RInt f N0 y).
    {
      apply (@ex_RInt_continuous R_CompleteNormedModule f N0 y).
      intros z Hz.
      assert (Hmin : Rmin N0 y = N0) by (apply Rmin_left; lra).
      assert (Hmax : Rmax N0 y = y) by (apply Rmax_right; lra).
      rewrite Hmin, Hmax in Hz.
      destruct Hz as [Hz1 Hz2].
      assert (Hz_pos : 0 < z) by (apply Rlt_le_trans with N0; [lra | exact Hz1]).
      apply Hcont_f_gt0; exact Hz_pos.
    }

    assert (H_chasles : RInt f 1 y = RInt f 1 N0 + RInt f N0 y).
    {
      symmetry.
      apply (RInt_Chasles f 1 N0 y Hex_1N0 Hex_N0y).
    }
    unfold x.
    rewrite H_chasles.
    unfold ball; simpl.
    replace (RInt f 1 N0 + RInt f N0 y - RInt f 1 N0) with (RInt f N0 y) by lra.
    assert (Hlt : RInt f N0 y < pos eps) by (apply Hcond; [exact N0_gt_M | exact Hy_gt_N0]).
    assert (Hge0 : 0 <= RInt f N0 y).
    {
      apply RInt_ge_0; [lra | exact Hex_N0y | intros t Ht; apply Hf_nonneg; lra].
    }
    unfold AbsRing_ball.
    set (A := RInt f 1 N0).
    set (B := RInt f N0 y).
    unfold minus.
    change (A + B) with (plus A B).
    rewrite (plus_comm A B).
    rewrite <- plus_assoc.
    unfold plus, opp, zero in *.
    rewrite Rplus_opp_r.
    rewrite Rplus_0_r.
    rewrite Rabs_pos_eq; [exact Hlt | exact Hge0].
  }

  assert (H_proper_F : ProperFilter F).
  { apply filtermap_proper_filter. exact HF. }

  set (L := lim F).
  exists L.

  intros P [eps Hball].
  pose proof (complete_cauchy F H_proper_F H_cauchy_f eps) as H.
  apply (filter_imp (ball L eps) P (fun y => Hball y) H).
Qed.

(* 伽马积分下极限为零 *)
Lemma f_lower_limit_zero (s : Complex) (Hre : 1 < ℜ(s)) :
  let f := fun t => match Rlt_dec 0 t with left H => gamma_integrand_real s t H | right _ => 0 end in
  filterlim (fun a => RInt f a 1) (Rbar_locally 1) (locally 0).
Proof.
  intros f.
  assert (Hcont_f1 : continuous f 1) by (apply Hcont_f_at_1; exact Hre).
  assert (Hcont_f_pos : forall t, 0 < t -> continuous f t).
  {
    intros t Ht.
    set (g := fun x => exp (- x) * Rpower x (ℜ(s) - 1)).
    assert (Hcont_g : continuous g t).
    {
      apply continuity_pt_to_continuous.
      apply continuity_pt_mult.
      - apply continuity_pt_comp with (f1 := fun x => - x) (f2 := exp).
        + apply continuity_pt_opp; apply continuity_pt_id.
        + apply derivable_continuous_pt; apply derivable_pt_exp.
      - apply continuity_pt_Rpower_pos; [apply Rgt_minus; exact Hre | exact Ht].
    }
    assert (Hloc_eq : locally t (fun x => f x = g x)).
    {
      apply locally_iff_open_ball.
      exists (t / 2). split; [lra |].
      intros y Hy.
      assert (Hy_pos : 0 < y) by (apply Rabs_lt_between in Hy; lra).
      unfold f, g.
      destruct (Rlt_dec 0 y) as [Hpos | Hneg]; [| contradiction Hneg].
      unfold gamma_integrand_real; simpl; unfold real_pow, Rpower; reflexivity.
    }
    apply continuous_ext_loc with (g := g) (x := t).
    - apply filter_imp with (P := fun x => f x = g x) (Q := fun x => g x = f x).
      + intros x Heq; symmetry; exact Heq.
      + exact Hloc_eq.
    - exact Hcont_g.
  }

  intros P [eps Hball].
  set (e := pos eps); assert (He : 0 < e) by apply cond_pos.
  assert (H1_pos : 0 < 1) by lra.
  destruct (Hcont_f1 (fun y => Rabs (y - f 1) < 1)
                     (locally_ball (f 1) (mkposreal 1 H1_pos))) as [d Hd].
  set (d1 := pos d) in *.
  assert (Hd1_pos : 0 < d1) by apply cond_pos.
  set (M := Rabs (f 1) + 1); assert (HM_pos : 0 < M) by (apply Rplus_le_lt_0_compat; [apply Rabs_pos | lra]).
  set (delta0 := Rmin d1 (e / M)).
  assert (Hdelta0_pos : 0 < delta0) by (apply Rmin_pos; [exact Hd1_pos | apply Rdiv_lt_0_compat; lra]).
  set (delta := Rmin delta0 (1/2)).
  assert (Hdelta_pos : 0 < delta) by (apply Rmin_pos; [exact Hdelta0_pos | lra]).
  exists (mkposreal delta Hdelta_pos).
  intros a Ha.
  assert (Ha_abs : Rabs (a - 1) < delta) by auto.
  assert (Ha_gt0 : a > 0).
  {
    apply Rabs_lt_between in Ha_abs; destruct Ha_abs as [H_low _].
    assert (H_delta_le_half : delta <= 1/2) by (unfold delta; apply Rmin_r).
    assert (0 < 1 - delta) by lra.
    lra.
  }
  assert (Hex_a1 : ex_RInt f a 1).
  {
    apply ex_RInt_continuous with (f := f) (a := a) (b := 1).
    intros z Hz.
    assert (Hz_pos : 0 < z).
    { apply Rlt_le_trans with (Rmin a 1).
      - apply Rmin_pos; [exact Ha_gt0 | exact H1_pos].
      - apply Hz.
    }
    apply Hcont_f_pos; exact Hz_pos.
  }
  assert (Hbound : forall t, Rmin a 1 <= t <= Rmax a 1 -> Rabs (f t) <= M).
  {
    intros t Ht.
    assert (Ht_abs : Rabs (t - 1) < d1).
    {
      destruct (Rle_or_lt a 1) as [Ha_le1 | Ha_gt1].
      - rewrite (Rmin_left a 1) in Ht; [| lra].
        rewrite (Rmax_right a 1) in Ht; [| lra].
        destruct Ht as [Ht1 Ht2].
        rewrite Rabs_left1; [| lra].
        replace (-(t - 1)) with (1 - t) by ring.
        apply Rle_lt_trans with (1 - a); [lra |].
        rewrite Rabs_left1 in Ha_abs; [| lra].
        replace (-(a - 1)) with (1 - a) in Ha_abs by ring.
        apply Rlt_le_trans with delta; [exact Ha_abs |].
        apply Rle_trans with delta0; [apply Rmin_l | apply Rmin_l].
      - rewrite (Rmin_right a 1) in Ht; [| lra].
        rewrite (Rmax_left a 1) in Ht; [| lra].
        destruct Ht as [Ht1 Ht2].
        rewrite Rabs_pos_eq; [| lra].
        apply Rle_lt_trans with (a - 1); [lra |].
        rewrite Rabs_pos_eq in Ha_abs; [| lra].
        apply Rlt_le_trans with delta; [exact Ha_abs |].
        apply Rle_trans with delta0; [apply Rmin_l | apply Rmin_l].
    }
    specialize (Hd t).
    assert (Hball_t : ball 1 d t) by (unfold ball; simpl; unfold AbsRing_ball; exact Ht_abs).
    specialize (Hd Hball_t).
    replace (f t) with ((f t - f 1) + f 1) by ring.
    apply Rle_trans with (Rabs (f t - f 1) + Rabs (f 1)).
    - apply Rabs_triang.
    - replace M with (1 + Rabs (f 1)) by (unfold M; ring).
      apply Rplus_le_compat.
      * apply Rlt_le, Hd.
      * apply Rle_refl.
  }
  assert (H_RInt_bound : Rabs (RInt f a 1) < e).
  {
    apply Rle_lt_trans with (M * Rabs (1 - a)).
    - rewrite Rmult_comm.
      pose proof (RInt_correct f a 1 Hex_a1) as H_is.
      apply norm_RInt_le_const_abs with (f := f) (a := a) (b := 1) (lf := RInt f a 1) (M := M).
      + intros x Hx.
        apply Hbound in Hx.
        unfold norm in *; simpl in *.
        exact Hx.
      + exact H_is.
    - rewrite Rmult_comm.
      assert (H1 : delta <= delta0) by (unfold delta; apply Rmin_l).
      assert (H2 : delta0 <= e / M) by apply Rmin_r.
      assert (Hdelta_le_eM : delta <= e / M) by (apply Rle_trans with (r2 := delta0); [exact H1 | exact H2]).
      assert (Habs_lt_eM : Rabs (a - 1) < e / M) by (apply Rlt_le_trans with delta; [exact Ha_abs | exact Hdelta_le_eM]).
      rewrite Rabs_minus_sym in Habs_lt_eM.
      apply Rmult_lt_compat_r with (r := M) in Habs_lt_eM; [| exact HM_pos].
      replace (e / M * M) with e in Habs_lt_eM by (field; lra).
      exact Habs_lt_eM.
  }
  apply Hball.
  unfold ball; simpl; unfold AbsRing_ball; simpl.
  rewrite Rminus_0_r.
  exact H_RInt_bound.
Qed.

(* Gamma被积函数无穷可积性 *)
Lemma f_integrable_inf (s : Complex) (Hre : 1 < ComplexNumbers.re s) :
  ex_RInt_gen (fun t : R =>
                 match Rlt_dec 0 t with
                 | left H => gamma_integrand_real s t H
                 | right _ => 0
                 end)
              (Rbar_locally 1)
              (Rbar_locally p_infty).
Proof.
  set (f := fun t => match Rlt_dec 0 t with left H => gamma_integrand_real s t H | right _ => 0 end).
  destruct (f_upper_limit_exists s Hre) as [L H_lim1].
  pose proof (f_lower_limit_zero s Hre) as H_zero.

  assert (Hcont_f_pos : forall t, 0 < t -> continuous f t).
  {
    intros t Ht.
    set (g := fun t => exp (-t) * Rpower t (ℜ(s) - 1)).
    assert (Hcont_g_pt : continuity_pt g t).
    {
      apply continuity_pt_mult.
      - apply continuity_pt_comp with (f1 := fun t => -t) (f2 := exp).
        + apply continuity_pt_opp; apply continuity_pt_id.
        + apply derivable_continuous_pt; apply derivable_pt_exp.
      - apply continuity_pt_Rpower_pos; [apply Rgt_minus; exact Hre | exact Ht].
    }
    assert (Hloc_eq : locally t (fun u => f u = g u)).
    {
      apply locally_iff_open_ball.
      exists (t/2); split; [lra |].
      intros u Hu.
      assert (Hu_pos : 0 < u) by (apply Rabs_lt_between in Hu; lra).
      unfold f; destruct (Rlt_dec 0 u) as [Hpos | Hneg]; [| lra].
      simpl; unfold gamma_integrand_real; simpl; unfold real_pow, Rpower; reflexivity.
    }
    assert (Hloc_eq_sym : locally t (fun u => g u = f u)).
    {
      apply filter_imp with (P := fun u => f u = g u) (Q := fun u => g u = f u);
        [intros u Heq; symmetry; exact Heq | exact Hloc_eq].
    }
    apply continuous_ext_loc with (g := g) (x := t).
    - exact Hloc_eq_sym.
    - apply continuity_pt_to_continuous_simple; exact Hcont_g_pt.
  }

  assert (H_int_1p : is_RInt_gen f (at_point 1) (Rbar_locally p_infty) L).
  {
    unfold is_RInt_gen.
    intros P HP.
    specialize (H_lim1 P HP) as H_Rbar.
    destruct H_Rbar as [M HM].
    set (M0 := Rmax M 1).
    assert (H_M0_ge_M : M <= M0) by apply Rmax_l.
    assert (H_M0_le : forall y, M0 < y -> M < y).
    { intros y Hy. apply Rle_lt_trans with (r2 := M0); [exact H_M0_ge_M | exact Hy]. }
    set (Q1 := fun x => x = 1).
    set (Q2 := fun y => M0 < y).
    assert (HQ1 : at_point 1 Q1) by (unfold at_point; reflexivity).
    assert (HQ2 : Rbar_locally p_infty Q2).
    { unfold Rbar_locally; exists M0; intros y Hy; exact Hy. }
    apply Filter_prod with (Q := Q1) (R := Q2); [exact HQ1 | exact HQ2 | ].
    intros x y Hx Hy.
    rewrite Hx.
    specialize (HM y (H_M0_le y Hy)) as HyP.

    assert (H1_le_y : 1 <= y).
    { apply Rle_trans with M0; [apply Rmax_r | apply Rlt_le; exact Hy]. }
    assert (Hex_1y : ex_RInt f 1 y).
    {
      apply ex_RInt_continuous with (f := f) (a := 1) (b := y).
      intros z Hz.
      destruct Hz as [Hlow Hhigh].
      rewrite Rmin_left in Hlow by exact H1_le_y.
      rewrite Rmax_right in Hhigh by exact H1_le_y.
      apply Hcont_f_pos.
      apply Rlt_le_trans with 1; [apply Rlt_0_1 | exact Hlow].
    }
    pose proof (RInt_correct f 1 y Hex_1y) as H_is.
    exists (RInt f 1 y). split; [exact H_is | exact HyP].
  }

  assert (H_int_01 : is_RInt_gen f (Rbar_locally 1) (at_point 1) 0).
  {
    unfold is_RInt_gen.
    intros P HP.
    specialize (H_zero P HP) as H_Rbar.
    apply locally_iff_open_ball in H_Rbar.
    destruct H_Rbar as [eps [Heps_pos Hball]].
    set (eps0 := Rmin eps (1/2)).
    assert (Heps0_pos : 0 < eps0) by (apply Rmin_pos; [exact Heps_pos | lra]).
    assert (Heps0_le_eps : eps0 <= eps) by apply Rmin_l.
    assert (Heps0_le_half : eps0 <= 1/2) by (apply Rmin_r).
    set (Q1 := fun x => Rabs (x - 1) < eps0).
    set (Q2 := fun y => y = 1).
    assert (HQ1 : Rbar_locally 1 Q1).
    { apply locally_iff_open_ball; exists eps0; split; [exact Heps0_pos | intros; auto]. }
    assert (HQ2 : at_point 1 Q2) by (unfold at_point; reflexivity).
    apply Filter_prod with (Q := Q1) (R := Q2); [exact HQ1 | exact HQ2 | ].
    intros x y Hx Hy.
    unfold Q2 in Hy; subst y.
    assert (Hx_lt_eps : Rabs (x - 1) < eps) by (apply Rlt_le_trans with eps0; [exact Hx | apply Heps0_le_eps]).
    specialize (Hball x Hx_lt_eps) as HxP.

    assert (Hx_pos : 0 < x).
    {
      destruct (Rabs_def2 (x - 1) eps0 Hx) as [_ H_gt].
      apply (Rplus_lt_compat_r 1) in H_gt.
      rewrite Rplus_comm in H_gt.
      lra.
    }

    assert (Hex_x1 : ex_RInt f x 1).
    {
      apply ex_RInt_continuous with (f := f) (a := x) (b := 1).
      intros z Hz.
      assert (Hmin_pos : 0 < Rmin x 1) by (apply Rmin_pos; [exact Hx_pos | lra]).
      assert (Hz_pos : 0 < z) by (apply Rlt_le_trans with (Rmin x 1); [exact Hmin_pos | apply Hz]).
      apply Hcont_f_pos; exact Hz_pos.
    }
    pose proof (RInt_correct f x 1 Hex_x1) as H_is.
    exists (RInt f x 1). split; [exact H_is | exact HxP].
  }

  assert (H_int : is_RInt_gen f (Rbar_locally 1) (Rbar_locally p_infty) (plus 0 L)).
  {
    apply is_RInt_gen_Chasles with (f := f) (b := 1) (l1 := 0) (l2 := L).
    - exact H_int_01.
    - exact H_int_1p.
  }
  exists (plus 0 L); exact H_int.
Qed.

(* 定理：Gamma积分收敛 *)
Theorem gamma_integral_converges (s : Complex) (Hre : 1 < ComplexNumbers.re s) :
  ex_RInt_gen (fun t => match Rlt_dec 0 t with left H => gamma_integrand_real s t H | right _ => 0 end)
              (at_right 0) (Rbar_locally p_infty).
Proof.
  set (f := fun t => match Rlt_dec 0 t with left H => gamma_integrand_real s t H | right _ => 0 end).

  assert (Hcont_f_pos : forall t, 0 < t -> continuous f t).
  {
    intros t Ht.
    set (g := fun t => exp (-t) * Rpower t (ℜ(s) - 1)).
    assert (Hcont_g_pt : continuity_pt g t).
    {
      apply continuity_pt_mult.
      - apply continuity_pt_comp with (f1 := fun t => -t) (f2 := exp).
        + apply continuity_pt_opp; apply continuity_pt_id.
        + apply derivable_continuous_pt; apply derivable_pt_exp.
      - apply continuity_pt_Rpower_pos; [apply Rgt_minus; exact Hre | exact Ht].
    }
    assert (Hloc_eq : locally t (fun u => f u = g u)).
    {
      apply locally_iff_open_ball.
      exists (t/2); split; [lra |].
      intros u Hu.
      assert (Hu_pos : 0 < u) by (apply Rabs_lt_between in Hu; lra).
      unfold f; destruct (Rlt_dec 0 u) as [Hpos | Hneg]; [| lra].
      simpl; unfold gamma_integrand_real; simpl; unfold real_pow, Rpower; reflexivity.
    }
    assert (Hloc_eq_sym : locally t (fun u => g u = f u)).
    {
      apply filter_imp with (P := fun u => f u = g u) (Q := fun u => g u = f u);
        [intros u Heq; symmetry; exact Heq | exact Hloc_eq].
    }
    apply continuous_ext_loc with (g := g) (x := t).
    - exact Hloc_eq_sym.
    - apply continuity_pt_to_continuous_simple; exact Hcont_g_pt.
  }

  destruct (f_integrable_01 s Hre) as [I01 H01].
  pose proof (RInt_gen_limit_at_right_0 f I01) as Hlim.
  assert (Hcont_f_pos01 : forall t, 0 < t <= 1 -> continuous f t).
  { exact (f_continuity_on_positive_le1 s Hre). }
  specialize (Hlim Hcont_f_pos01 H01).

  assert (H_int_01 : is_RInt_gen f (at_right 0) (at_point 1) I01).
  {
    unfold is_RInt_gen.
    intros P HP.
    specialize (Hlim P HP) as [delta Hdelta].
    set (A := fun u => 0 < u < delta).
    assert (HA : at_right 0 A).
    {
      exists (mkposreal delta (cond_pos delta)).
      intros u Hu Hpos.
      split; [exact Hpos |].
      assert (Hu_abs : Rabs (u - 0) < delta) by exact Hu.
      rewrite Rminus_0_r in Hu_abs.
      rewrite Rabs_pos_eq in Hu_abs; [exact Hu_abs | left; exact Hpos].
    }
    set (B := fun v => v = 1).
    assert (HB : at_point 1 B) by (unfold at_point; reflexivity).
    apply Filter_prod with (Q := A) (R := B); [exact HA | exact HB | ].
    intros u v Hu Hv.
    unfold B in Hv; subst v.
    destruct Hu as [Hu_pos Hu_lt_delta].

    assert (Hex_u1 : ex_RInt f u 1).
    {
      apply ex_RInt_continuous with (f := f) (a := u) (b := 1).
      intros z Hz.
      destruct Hz as [Hlow Hhigh].
      assert (Hz_pos : 0 < z).
      { apply Rlt_le_trans with (Rmin u 1).
        - apply Rmin_glb_lt; [exact Hu_pos | lra].
        - exact Hlow. }
      apply Hcont_f_pos; exact Hz_pos.
    }
    pose proof (RInt_correct f u 1 Hex_u1) as H_is.
    exists (RInt f u 1). split; [exact H_is |].

    assert (Hball_u : AbsRing_ball R_AbsRing 0 delta u).
    {
      unfold AbsRing_ball, R_AbsRing; simpl.
      rewrite Rminus_0_r.
      rewrite Rabs_pos_eq by lra.
      lra.
    }
    exact (Hdelta u Hball_u Hu_pos).
  }

  destruct (f_upper_limit_exists s Hre) as [L H_lim1].

  assert (H_int_1p : is_RInt_gen f (at_point 1) (Rbar_locally p_infty) L).
  {
    unfold is_RInt_gen.
    intros P HP.
    specialize (H_lim1 P HP) as H_Rbar.
    destruct H_Rbar as [M HM].
    set (M0 := Rmax M 1).
    assert (H_M0_ge_M : M <= M0) by apply Rmax_l.
    assert (H_M0_le : forall y, M0 < y -> M < y).
    { intros y Hy. apply Rle_lt_trans with (r2 := M0); [exact H_M0_ge_M | exact Hy]. }
    set (Q1 := fun x => x = 1).
    set (Q2 := fun y => M0 < y).
    assert (HQ1 : at_point 1 Q1) by (unfold at_point; reflexivity).
    assert (HQ2 : Rbar_locally p_infty Q2).
    { unfold Rbar_locally; exists M0; intros y Hy; exact Hy. }
    apply Filter_prod with (Q := Q1) (R := Q2); [exact HQ1 | exact HQ2 | ].
    intros x y Hx Hy.
    unfold Q1 in Hx; subst x.
    specialize (HM y (H_M0_le y Hy)) as HyP.

    assert (Hex_1y : ex_RInt f 1 y).
    {
      apply ex_RInt_continuous with (f := f) (a := 1) (b := y).
      intros z Hz.
      destruct Hz as [Hlow Hhigh].
      assert (H1_le_y : 1 <= y).
      { apply Rlt_le; apply Rle_lt_trans with M0; [apply Rmax_r | exact Hy]. }
      rewrite Rmin_left in Hlow by exact H1_le_y.
      rewrite Rmax_right in Hhigh by exact H1_le_y.
      assert (Hz_pos : 0 < z) by (apply Rlt_le_trans with 1; [apply Rlt_0_1 | exact Hlow]).
      apply Hcont_f_pos; exact Hz_pos.
    }
    pose proof (RInt_correct f 1 y Hex_1y) as H_is.
    exists (RInt f 1 y). split; [exact H_is | exact HyP].
  }

  assert (H_int : is_RInt_gen f (at_right 0) (Rbar_locally p_infty) (plus I01 L)).
  {
    apply is_RInt_gen_Chasles with (f := f) (b := 1) (l1 := I01) (l2 := L).
    - exact H_int_01.
    - exact H_int_1p.
  }
  exists (plus I01 L); exact H_int.
Qed.

(* 平方根小于等于绝对值之和 *)
Lemma sqrt_le_plus_abs : forall a b, sqrt (a*a + b*b) <= Rabs a + Rabs b.
Proof.
  intros a b.
  set (s := sqrt (a*a + b*b)).
  set (t := Rabs a + Rabs b).

  assert (Hpos_s : 0 <= s) by apply sqrt_pos.
  assert (Hpos_t : 0 <= t).
  { apply Rplus_le_le_0_compat; apply Rabs_pos. }

  assert (Hs2 : s * s = a*a + b*b).
  { apply sqrt_sqrt. apply Rplus_le_le_0_compat; apply Rle_0_sqr. }

  assert (Ht2 : t * t = (Rabs a)*(Rabs a) + (Rabs b)*(Rabs b) + 2 * Rabs a * Rabs b).
  { unfold t; ring. }

  assert (Habs_sq : forall x : R, Rabs x * Rabs x = x * x).
  { intro x.
    assert (H1 : (Rabs x)² = x²) by (symmetry; apply Rsqr_abs).
    unfold Rsqr in H1.
    exact H1. }

  assert (Ha2 : a*a = Rabs a * Rabs a).
  { rewrite <- (Habs_sq a); ring. }
  assert (Hb2 : b*b = Rabs b * Rabs b).
  { rewrite <- (Habs_sq b); ring. }

  assert (Hsq_le : s*s <= t*t).
  { rewrite Hs2, Ht2, Ha2, Hb2.
    ring_simplify.
    assert (H1 : 0 <= Rabs a) by apply Rabs_pos.
    assert (H2 : 0 <= Rabs b) by apply Rabs_pos.
    assert (H3 : 0 <= Rabs a * Rabs b).
    { apply Rmult_le_pos; assumption. }
    assert (H4 : 0 <= 2 * (Rabs a * Rabs b)).
    { apply Rmult_le_pos; [lra | assumption]. }
    assert (H5 : 2 * (Rabs a * Rabs b) = 2 * Rabs a * Rabs b) by ring.
    rewrite H5 in H4.
    lra. }

  assert (Hfinal : s <= t).
  { assert (H2 : Rabs s <= Rabs t).
    { apply Rsqr_le_abs_0. exact Hsq_le. }
    assert (Hge_s : s >= 0) by lra.
    assert (Hge_t : t >= 0) by lra.
    assert (H3 : Rabs s = s) by (apply Rabs_right; exact Hge_s).
    assert (H4 : Rabs t = t) by (apply Rabs_right; exact Hge_t).
    rewrite H3, H4 in H2.
    exact H2. }

  exact Hfinal.
Qed.

(* 复数加法的实部/虚部投影 *)
Lemma re_Cadd : forall z1 z2, re (z1 +c z2) = re z1 + re z2. Proof. intros; reflexivity. Qed.
Lemma im_Cadd : forall z1 z2, im (z1 +c z2) = im z1 + im z2. Proof. intros; reflexivity. Qed.

Section ZetaTermRealPart.
  Variable s : Complex.

(* 实部项定义 [修复]：角度改用 ℑ(s)·ln n（n^{-s} 实部 = n^{-σ}·cos(τ·ln n)） *)
Definition re_term (s : Complex) (n : nat) : R :=
  let n_R := INR (S n) in
  Rpower n_R (- re s) * cos (im s * ln n_R).

(** * ζ函数级数项实部公式 *)
Lemma re_zeta_term_eq (n : nat) :
  re (zeta_series_term s n) = re_term s n.
Proof.
  unfold zeta_series_term.
  set (n_R := INR (S n)).
  set (z := n_R +i 0).
  assert (Hz : z <> C0).
  { unfold z; intros H; apply (f_equal re) in H; simpl in H.
    assert (Hpos : 0 < n_R) by (apply lt_0_INR, Nat.lt_0_succ).
    rewrite H in Hpos; lra. }
  unfold my_complex_pow.
  assert (Habs : complex_abs z = n_R).
  { unfold complex_abs, z; simpl.
    rewrite Rmult_1_r, Rmult_0_l, Rplus_0_r.
    apply sqrt_square.
    apply pos_INR. }
  assert (Harg : complex_arg z Hz = 0).
  { unfold complex_arg, my_arctan2; simpl.
    destruct (Rgt_dec n_R 0) as [Hgt|Hnot].
    - rewrite Rdiv_0_l by (apply Rgt_not_eq; exact Hgt).
      rewrite atan_0; reflexivity.
    - exfalso.
      assert (Hn0 : n_R = 0).
      { apply Rle_antisym; [apply Rnot_lt_le, Hnot | apply pos_INR]. }
      apply Hz; unfold z; rewrite Hn0; reflexivity. }
  unfold real_pow.
  rewrite Habs.
  unfold complex_arg in *.
  rewrite Harg.
  simpl.
  replace ((0 - ℜ(s)) * 0 + (0 - ℑ(s)) * ln n_R) with ((0 - ℑ(s)) * ln n_R) by ring.
  rewrite Rmult_0_r.
  rewrite exp_0.
  rewrite Rmult_1_r.
  replace ((0 - ℑ(s)) * ln n_R) with (- ℑ(s) * ln n_R) by ring.
  replace (- ℑ(s) * ln n_R) with (- (ℑ(s) * ln n_R)) by ring.
  rewrite cos_neg.
  replace ((0 - ℜ(s)) * ln n_R) with (- ℜ(s) * ln n_R) by ring.
  unfold re_term.
  unfold Rpower.
  unfold n_R.
  rewrite <- Ropp_mult_distr_l.
  reflexivity.
Qed.

End ZetaTermRealPart.

(* 虚部项定义 [修复]：角度改用 ℑ(s)·ln n（n^{-s} 虚部 = −n^{-σ}·sin(τ·ln n)） *)
Definition im_term (s : Complex) (n : nat) : R :=
  let n_R := INR (S n) in
  - Rpower n_R (- re s) * sin (im s * ln n_R).

(** ζ函数级数项的模公式 *)
Lemma zeta_term_norm (s : Complex) (n : nat) :
  Cnorm (zeta_series_term s n) = Rpower (INR (S n)) (- ℜ(s)).
Proof.
  unfold zeta_series_term.
  set (x := INR (S n)).
  set (z := x +i 0).
  assert (Hz : z <> C0).
  { intro Heq; apply (Rgt_not_eq x 0 (lt_0_INR (S n) (Nat.lt_0_succ n))); apply (f_equal re Heq). }

  unfold my_complex_pow.

  assert (Habs : complex_abs z = x).
  {
    unfold complex_abs; simpl.
    rewrite Rmult_1_r.
    rewrite Rmult_0_l.
    rewrite Rplus_0_r.
    rewrite sqrt_square; [| apply pos_INR].
    reflexivity.
  }

  unfold real_pow.
  rewrite Habs.

  assert (Harg : forall H : z <> C0, complex_arg z H = 0).
  {
    intros H.
    unfold complex_arg, my_arctan2; simpl.
    destruct (Rgt_dec x 0) as [Hgt|Hnot].
    - rewrite Rdiv_0_l by (apply Rgt_not_eq, Hgt).
      rewrite atan_0.
      reflexivity.
    - exfalso; apply Hnot; apply lt_0_INR, Nat.lt_0_succ.
  }

  rewrite Harg. simpl.

  rewrite Rmult_0_r.
  rewrite exp_0.
  rewrite Rmult_1_r.
  rewrite Rmult_0_r.
  rewrite Rplus_0_l.

  set (A := exp ((0 - ℜ(s)) * ln x)).
  set (B := cos ((0 - ℑ(s)) * ln x)).
  set (C := sin ((0 - ℑ(s)) * ln x)).

  unfold Cnorm, Cnorm_sq; simpl.
  rewrite !Rsqr_mult.
  rewrite <- Rmult_plus_distr_l.

  replace (Rsqr B + Rsqr C) with 1.
  - rewrite Rmult_1_r.
    rewrite sqrt_Rsqr_abs.
    rewrite Rabs_pos_eq; [| apply Rlt_le; apply exp_pos].
    unfold Rpower.
    unfold A.
    apply f_equal.
    ring.
  - unfold B, C.
    rewrite cos_sq_plus_sin_sq.
    reflexivity.
Qed.

(* 实部绝对值不超过模 *)
Lemma Rabs_re_le_norm (z : Complex) : Rabs (re z) <= Cnorm z.
Proof.
  unfold Cnorm, Cnorm_sq.
  rewrite <- sqrt_Rsqr_abs.
  apply sqrt_le_1_c.
  - apply Rle_0_sqr.
  - apply Rplus_le_le_0_compat; apply Rle_0_sqr.
  - rewrite <- Rplus_0_r at 1.
    apply Rplus_le_compat_l.
    apply Rle_0_sqr.
Qed.

(* 自身加非负数 *)
Lemma Rle_self_plus : forall a b : R, 0 <= b -> a <= a + b.
Proof.
  intros a b Hb.
  rewrite <- Rplus_0_r at 1.
  apply Rplus_le_compat_l.
  exact Hb.
Qed.

(* 虚部绝对值不超过模 *)
Lemma Rabs_im_le_norm (z : Complex) : Rabs (im z) <= Cnorm z.
Proof.
  unfold Cnorm, Cnorm_sq.
  rewrite <- sqrt_Rsqr_abs.
  apply sqrt_le_1_c.
  - apply Rle_0_sqr.
  - apply Rplus_le_le_0_compat; apply Rle_0_sqr.
  - rewrite Rplus_comm.
    apply Rle_self_plus.
    apply Rle_0_sqr.
Qed.

(* 复数累加和的虚部等于虚部的累加和 *)
Lemma im_Csum_eq (s : Complex) (N : nat) :
  im (Csum (zeta_series_term s) N) =
    match N with
    | 0 => 0
    | S N' => sum_f_R0 (fun n => im (zeta_series_term s n)) N'
    end.
Proof.
  induction N as [|N IH].
  - reflexivity.
  - simpl. rewrite IH.
    destruct N as [|N'].
    + simpl. ring.
    + simpl. ring.
Qed.

(* 若复数序列 u 的实部收敛到 l_re，虚部收敛到 l_im，则 u 收敛到 l_re +i l_im *)
Lemma Cseq_limit_from_components (u : nat -> Complex) (l_re l_im : R) :
  (forall ε : R, ε > 0 -> exists N : nat, forall n : nat, (n >= N)%nat -> Rabs (re (u n) - l_re) < ε) ->
  (forall ε : R, ε > 0 -> exists N : nat, forall n : nat, (n >= N)%nat -> Rabs (im (u n) - l_im) < ε) ->
  Cseq_limit u (l_re +i l_im).
Proof.
  intros H_re H_im.
  unfold Cseq_limit.
  intros ε Hε.
  assert (Hε2 : 0 < ε/2) by lra.
  destruct (H_re (ε/2) Hε2) as [N1 HN1].
  destruct (H_im (ε/2) Hε2) as [N2 HN2].
  set (N := Nat.max N1 N2).
  exists N.
  intros n Hn.
  pose proof (HN1 n (Nat.le_trans _ _ _ (Nat.le_max_l _ _) Hn)) as H_re_n.
  pose proof (HN2 n (Nat.le_trans _ _ _ (Nat.le_max_r _ _) Hn)) as H_im_n.
  unfold Capprox; split.
  - apply Rlt_le_trans with (ε/2); [exact H_re_n | lra].
  - apply Rlt_le_trans with (ε/2); [exact H_im_n | lra].
Qed.

Section ZetaTermLemmas.

Import ComplexNumbers.
Local Open Scope complex_scope.

(* zeta级数项虚部公式 *)
Lemma im_zeta_term_eq : forall (s : Complex) (n : nat),
  im (zeta_series_term s n) = im_term s n.
Proof.
  intros s n.
  unfold zeta_series_term.
  set (x := INR (S n)).
  set (z := x +i 0).
  assert (Hz : z <> C0).
  { intro H; apply (f_equal re) in H; simpl in H.
    assert (Hpos : 0 < x) by (apply lt_0_INR, Nat.lt_0_succ).
    rewrite H in Hpos; lra. }
  unfold my_complex_pow; simpl.
  assert (Habs : complex_abs z = x).
  { unfold complex_abs, z; simpl.
    rewrite Rmult_1_r, Rmult_0_l, Rplus_0_r.
    apply sqrt_square; apply pos_INR. }
  assert (Harg : complex_arg z Hz = 0).
  { unfold complex_arg, my_arctan2; simpl.
    destruct (Rgt_dec x 0) as [Hgt|Hnot].
    - rewrite Rdiv_0_l by (apply Rgt_not_eq, Hgt).
      rewrite atan_0; reflexivity.
    - exfalso; apply Hnot; apply lt_0_INR; lia. }
  assert (Harg' : forall H : z <> C0, complex_arg z H = 0).
  { intros H. rewrite <- Harg. apply f_equal. apply proof_irrelevance. }
  unfold real_pow.
  rewrite Habs, Harg'; simpl.
  replace ((0 - re s) * 0 + (0 - im s) * ln x) with ((0 - im s) * ln x) by ring.
  rewrite Rmult_0_r.
  rewrite exp_0.
  rewrite Rmult_1_r.
  replace (0 - re s) with (- re s) by ring.
  rewrite <- Ropp_mult_distr_l.
  replace ((0 - im s) * ln x) with (- im s * ln x) by ring.
  replace (- im s * ln x) with (- (im s * ln x)) by ring.
  rewrite sin_neg.
  unfold im_term.
  rewrite Rpower_Ropp.
  unfold Rpower.
  replace (INR (S n)) with x by reflexivity.
  rewrite <- exp_Ropp.
  apply Rmult_eq_reg_l with (exp (- (re s * ln x))).
  - ring.
  - apply Rgt_not_eq, exp_pos.
Qed.

(* 虚部加零不变 *)
Lemma im_Cadd_0_r : forall (a : Complex), im (Cadd a C0) = im a.
Proof.
  intros a. unfold Cadd, C0. simpl. ring.
Qed.

(* 单位复数的模 *)
Lemma complex_abs_one : complex_abs (1 +i 0) = 1.
Proof.
  unfold complex_abs; simpl.
  rewrite Rmult_1_r, Rmult_0_l, Rplus_0_r.
  apply sqrt_square; lra.
Qed.

(* 单位复数的幅角 *)
Lemma complex_arg_one : forall H : (1 +i 0) <> C0,
  complex_arg (1 +i 0) H = 0.
Proof.
  intros H.
  unfold complex_arg, my_arctan2; simpl.
  destruct (Rgt_dec 1 0) as [Hgt|Hnot].
  - rewrite Rdiv_0_l by (apply Rgt_not_eq, Hgt).
    rewrite atan_0; reflexivity.
  - exfalso; apply Hnot; lra.
Qed.

(* 虚部部分和 *)
Lemma im_Csum_zeta : forall (s : Complex) (n : nat),
  im (Csum (zeta_series_term s) (S n)) = sum_f_R0 (im_term s) n.
Proof.
  induction n as [|n IH].
  - simpl.
    unfold real_pow.
    rewrite complex_abs_one.
    rewrite complex_arg_one.
    simpl.
    rewrite ln_1, Rmult_0_r, exp_0.
    rewrite Rmult_0_r, exp_0.
    rewrite Rmult_0_r, Rplus_0_l.
    rewrite sin_0, Rmult_0_r, Rplus_0_r.
    unfold im_term; simpl.
    replace (INR 1) with 1 by (simpl; ring).
    rewrite Rpower_1_r, ln_1, Rmult_0_r, sin_0, Rmult_0_r.
    ring.
  - assert (Hrec : Csum (zeta_series_term s) (S (S n)) =
                   Cadd (zeta_series_term s (S n)) (Csum (zeta_series_term s) (S n))).
    { reflexivity. }
    rewrite Hrec.
    rewrite im_Cadd.
    rewrite im_zeta_term_eq.
    rewrite IH.
    rewrite sum_f_R0_S.
    ring.
Qed.

(* 实部部分和 *)
Lemma re_Csum_zeta : forall (s : Complex) (n : nat),
  re (Csum (zeta_series_term s) (S n)) = sum_f_R0 (re_term s) n.
Proof.
  induction n as [|n IH].
  - simpl.
    unfold real_pow.
    rewrite complex_abs_one.
    rewrite complex_arg_one.
    simpl.
    rewrite ln_1, Rmult_0_r, exp_0.
    rewrite Rmult_0_r, exp_0.
    rewrite Rmult_0_r, Rplus_0_l.
    rewrite cos_0, Rmult_1_r, Rplus_0_r.
    unfold re_term; simpl.
    replace (INR 1) with 1 by (simpl; ring).
    rewrite Rpower_1_r, ln_1, Rmult_0_r, cos_0, Rmult_1_r.
    ring.
  - assert (Hrec : Csum (zeta_series_term s) (S (S n)) =
                   Cadd (zeta_series_term s (S n)) (Csum (zeta_series_term s) (S n))).
    { reflexivity. }
    rewrite Hrec.
    rewrite re_Cadd.
    rewrite re_zeta_term_eq.
    rewrite IH.
    rewrite sum_f_R0_S.
    ring.
Qed.

End ZetaTermLemmas.

(* 部分和逐项相等 *)

(* 复数求和递推公式 *)
Lemma Csum_rec (s : Complex) (m : nat) :
  Csum (zeta_series_term s) (S m) = Csum (zeta_series_term s) m +c zeta_series_term s m.
Proof.
  simpl.
  apply FourierAnalysis.Cadd_comm.
Qed.

(* Csum 为零 *)
Lemma Csum_0 (s : Complex) : Csum (zeta_series_term s) 0 = C0.
Proof. reflexivity. Qed.

(* 部分和递增性 *)
Lemma sum_f_R0_incr (a : nat -> R) :
  (forall n : nat, sum_f_R0 a n <= sum_f_R0 a (S n)) ->
  forall i j : nat, (i <= j)%nat -> sum_f_R0 a i <= sum_f_R0 a j.
Proof.
  intros Hinc i j Hle.
  induction Hle as [| j' Hle' IH].
  - apply Rle_refl.
  - apply Rle_trans with (sum_f_R0 a j').
    + exact IH.
    + apply Hinc.
Qed.

(* 绝对值三角不等式 *)
Lemma Rabs_sum_f_R0 (f : nat -> R) (n : nat) :
  Rabs (sum_f_R0 f n) <= sum_f_R0 (fun k : nat => Rabs (f k)) n.
Proof.
  induction n as [|n IH].
  - simpl; lra.
  - simpl sum_f_R0.
    rewrite Rabs_triang.
    apply Rplus_le_compat.
    + apply IH.
    + apply Rle_refl.
Qed.

(* 复数级数部分和实部公式 *)

(* 部分和逐项相等 *)
Lemma sum_f_R0_ext : forall (f g : nat -> R) (n : nat),
  (forall k, f k = g k) -> sum_f_R0 f n = sum_f_R0 g n.
Proof.
  intros f g n H.
  induction n as [| n IHn].
  - simpl. rewrite H. reflexivity.
  - simpl. rewrite H. rewrite IHn. reflexivity.
Qed.

(* 递归求和函数 *)
Fixpoint my_sum_f_R0 (f : nat -> R) (n : nat) : R :=
  match n with
  | 0 => 0%R
  | S n' => (my_sum_f_R0 f n' + f n')%R
  end.

(* 部分和对加法的分配性质 *)
Lemma my_sum_f_R0_add (f : nat -> R) (n p : nat) :
  my_sum_f_R0 f (n + p) = (my_sum_f_R0 f n + my_sum_f_R0 (fun k : nat => f (n + k)%nat) p)%R.
Proof.
  induction p as [| p IHp].
  - rewrite Nat.add_0_r.
    simpl my_sum_f_R0.
    rewrite Rplus_0_r.
    reflexivity.
  - rewrite Nat.add_succ_r.
    simpl my_sum_f_R0.
    rewrite IHp.
    rewrite Rplus_assoc.
    reflexivity.
Qed.

(* 部分和偏移公式 *)
Lemma sum_f_R0_shift (f : nat -> R) (m n : nat) (H : (m >= n)%nat) :
  my_sum_f_R0 f m = (my_sum_f_R0 f n + my_sum_f_R0 (fun k : nat => f (n + k)%nat) (m - n)%nat)%R.
Proof.
  assert (H_eq : m = (n + (m - n))%nat). { lia. }
  rewrite H_eq.
  assert (H_sub : (n + (m - n) - n)%nat = (m - n)%nat). { lia. }
  rewrite H_sub.
  apply my_sum_f_R0_add.
Qed.

(* 部分和单调性 *)
Lemma sum_f_R0_le (f g : nat -> R) (n : nat) (H : forall k : nat, f k <= g k) :
  sum_f_R0 f n <= sum_f_R0 g n.
Proof.
  induction n as [|n IH].
  - simpl. apply H.
  - simpl. apply Rplus_le_compat; [apply IH | apply H].
Qed.

(* 柯西序列定义 *)
Definition cauchy_seq (u : nat -> R) : Prop :=
  forall eps : R, eps > 0 -> exists N : nat, forall n m : nat,
    (n >= N)%nat -> (m >= N)%nat -> Rabs (u n - u m) < eps.

(* 柯西序列收敛 *)
Lemma cauchy_seq_converges (u : nat -> R) (Hcauchy : cauchy_seq u) :
  exists l : R, Un_cv u l.
Proof.
  destruct (R_complete u Hcauchy) as [l Hl].
  exists l.
  exact Hl.
Qed.

(* 实部项上界 *)
Lemma re_term_bound (s : Complex) (n : nat) (Hre : 1 < ℜ(s)) :
  Rabs (re_term s n) <= Rpower (INR (S n)) (- ℜ(s)).
Proof.
  set (σ := ℜ(s)).
  set (n_R := INR (S n)).
  assert (Hn_pos : 0 < n_R) by (apply lt_0_INR; lia).
  assert (Hpow_pos : 0 < Rpower n_R (- σ)) by (apply Rpower_pos; exact Hn_pos).
  unfold re_term.
  rewrite Rabs_mult.
  rewrite Rabs_pos_eq; [| apply Rlt_le; exact Hpow_pos].
  rewrite <- (Rmult_1_r (Rpower n_R (-σ))).
  apply Rmult_le_compat_l.
  - apply Rlt_le; exact Hpow_pos.
  - set (x := ℑ(s) * ln n_R).
    rewrite <- sqrt_Rsqr_abs.
    rewrite <- sqrt_1.
    apply sqrt_le_1_c.
    + apply Rle_0_sqr.
    + apply Rle_0_1.
    + rewrite <- (cos2_sin2 x).
      apply Rle_self_plus.
      apply Rle_0_sqr.
Qed.

(* 虚部项上界 *)
Lemma im_term_bound (s : Complex) (n : nat) (Hre : 1 < ℜ(s)) :
  Rabs (im_term s n) <= Rpower (INR (S n)) (- ℜ(s)).
Proof.
  set (σ := ℜ(s)).
  set (n_R := INR (S n)).
  assert (Hn_pos : 0 < n_R).
  { apply lt_0_INR; lia. }
  assert (Hpow_pos : 0 < Rpower n_R (- σ)).
  { apply Rpower_pos; exact Hn_pos. }
  unfold im_term.
  rewrite Rabs_mult.
  rewrite Rabs_Ropp, Rabs_pos_eq; [| apply Rlt_le; exact Hpow_pos].
  assert (Hsin_le : Rabs (sin (ℑ(s) * ln n_R)) <= 1).
  { rewrite <- sqrt_Rsqr_abs.
    rewrite <- sqrt_1.
    apply sqrt_le_1_c.
    - apply Rle_0_sqr.
    - apply Rle_0_1.
    - apply Rle_trans with ((sin (ℑ(s) * ln n_R))² + (cos (ℑ(s) * ln n_R))²).
      + apply Rle_self_plus; apply Rle_0_sqr.
      + rewrite sin2_cos2; apply Rle_refl. }
  apply Rle_trans with (Rpower n_R (- σ) * 1).
  - apply Rmult_le_compat_l; [apply Rlt_le; exact Hpow_pos | exact Hsin_le].
  - ring_simplify; apply Rle_refl.
Qed.

(* 负指数幂函数递减性 *)
Lemma Rpower_neg_decreasing (a : R) (x y : R) :
  0 < x < y -> 0 < a -> Rpower x (-a) > Rpower y (-a).
Proof.
  intros Hxy Ha.
  destruct Hxy as [Hx Hy].
  unfold Rpower.
  apply exp_increasing.
  rewrite <- !Ropp_mult_distr_l.
  apply Ropp_lt_contravar.
  apply Rmult_lt_compat_l.
  - exact Ha.
  - apply ln_increasing; [exact Hx | exact Hy].
Qed.

(* 负指数幂趋于零 *)
Lemma Rpower_neg_exp_tends_to_0 (p : R) (Hp : p < 0) :
  forall eps : R, eps > 0 -> exists M : R, forall x : R, x > M -> Rpower x p < eps.
Proof.
  intros eps Heps.
  set (M := exp (ln eps / p)).
  exists M.
  intros x Hx.
  unfold Rpower.
  rewrite <- (exp_ln eps Heps).
  apply exp_increasing.
  assert (HM_pos : 0 < M) by apply exp_pos.
  assert (Hx_pos : 0 < x) by (apply Rlt_trans with M; [exact HM_pos | exact Hx]).
  assert (Hln : ln M < ln x) by (apply ln_increasing; [exact HM_pos | exact Hx]).
  unfold M in Hln.
  rewrite ln_exp in Hln.
  assert (Htmp : p * (ln eps / p) = ln eps) by (field; lra).
  assert (H : p * ln x < p * (ln eps / p)).
  {
    apply Ropp_lt_cancel.
    rewrite !Ropp_mult_distr_l.
    apply Rmult_lt_compat_l with (r := -p).
    - apply Ropp_0_gt_lt_contravar, Hp.
    - exact Hln.
  }
  rewrite Htmp in H.
  exact H.
Qed.

(* 部分和之差公式 *)
Lemma sum_f_R0_plus (a : nat -> R) (n m : nat) (Hnm : (n <= m)%nat) :
  sum_f_R0 a m - sum_f_R0 a n =
    if n <? m then sum_f_R0 (fun i => a (S n + i)%nat) (m - S n) else 0.
Proof.
  revert n Hnm.
  induction m as [|m IH]; intros n Hnm.
  - assert (n = 0%nat) by lia.
    subst n.
    simpl.
    ring.
  - destruct (Nat.ltb_spec n (S m)) as [Hlt | Hge].
    + destruct (Nat.ltb_spec n m) as [Hlt' | Hge'].
      * assert (Hle : (n <= m)%nat) by lia.
        specialize (IH n Hle).
        rewrite sum_f_R0_S.
        replace (sum_f_R0 a m + a (S m) - sum_f_R0 a n)
           with ((sum_f_R0 a m - sum_f_R0 a n) + a (S m)) by ring.
        rewrite IH.
        replace (S m - S n)%nat with (S (m - S n)) by lia.
        rewrite sum_f_R0_S.
        replace (S n + S (m - S n))%nat with (S m) by lia.
        assert (Heq : (n <? m) = true) by (apply Nat.ltb_lt; exact Hlt').
        rewrite Heq.
        reflexivity.
      * assert (n = m) by lia.
        subst m.
        replace (S n - S n)%nat with 0%nat by lia.
        simpl.
        rewrite Nat.add_0_r.
        ring.
    + assert (n = S m) by lia.
      subst n.
      simpl.
      ring.
Qed.

(* 端点处可积性 *)
Lemma my_ex_RInt_point {V : NormedModule R_AbsRing} (f : R -> V) (a : R) : ex_RInt f a a.
Proof.
  apply ex_RInt_point.
Qed.

(* 端点处积分为零 *)
Lemma my_RInt_point {V : CompleteNormedModule R_AbsRing} (f : R -> V) (a : R) : RInt f a a = zero.
Proof.
  apply RInt_point.
Qed.

(* 伽马积分实部表达式 *)
Lemma H_f_eq_lemma (s : Complex) :
  forall t : R, 0 < t ->
  (let f := fun t : R =>
            match Rlt_dec 0 t with
            | left H => gamma_integrand_real s t H
            | right _ => 0
            end in
   f t) = exp (-t) * Rpower t (ℜ(s) - 1).
Proof.
  intros t Ht.
  set (f := fun t : R =>
            match Rlt_dec 0 t with
            | left H => gamma_integrand_real s t H
            | right _ => 0
            end).
  unfold f.
  destruct (Rlt_dec 0 t) as [Ht'|Hnt].
  - unfold gamma_integrand_real.
    simpl.
    unfold real_pow, Rpower.
    reflexivity.
  - contradiction.
Qed.

(* 指数乘幂函数连续 *)
Lemma exp_neg_times_Rpower_continuous (a : R) (t : R) (Ht : 0 < t) :
  continuity_pt (fun t => exp (-t) * Rpower t a) t.
Proof.
  apply continuity_pt_mult.
  - apply continuity_pt_comp with (f1 := fun t => -t) (f2 := exp).
    + apply continuity_pt_opp; apply continuity_pt_id.
    + apply derivable_continuous_pt; apply derivable_pt_exp.
  - unfold Rpower.
    apply continuity_pt_comp with (f1 := fun t => a * ln t) (f2 := exp).
    + apply continuity_pt_scal.
      apply derivable_continuous_pt.
      apply derivable_pt_ln_manual; assumption.
    + apply derivable_continuous_pt; apply derivable_pt_exp.
Qed.

(* 伽马积分实部函数在正实数上连续 *)
Lemma f_continuous_positive (s : Complex) (t : R) (Ht : 0 < t) :
  let f := fun t => match Rlt_dec 0 t with left H => gamma_integrand_real s t H | right _ => 0 end in
  continuity_pt f t.
Proof.
  intros f.
  assert (H_eq : forall y : R, 0 < y -> f y = exp (- y) * Rpower y (ℜ(s) - 1)).
  { intros y Hy. exact (H_f_eq_lemma s y Hy). }
  assert (H_g_cont : continuity_pt (fun t => exp (-t) * Rpower t (ℜ(s) - 1)) t).
  { apply exp_neg_times_Rpower_continuous with (a := ℜ(s) - 1); auto. }
  assert (H_loc_eq : locally t (fun y => f y = exp (- y) * Rpower y (ℜ(s) - 1))).
  { assert (Hhalf : 0 < t / 2) by lra.
    exists (mkposreal (t / 2) Hhalf).
    intros y Hy.
    simpl in Hy.
    apply Rabs_lt_between' in Hy.
    destruct Hy as [Hy_low Hy_high].
    assert (Hy_pos : 0 < y) by lra.
    rewrite (H_eq y Hy_pos); reflexivity. }
  apply continuity_pt_ext_loc with (f := (fun t => exp(-t) * Rpower t (ℜ(s)-1))) (g := f).
  - apply filter_imp with (P := fun y => f y = exp (- y) * Rpower y (ℜ(s)-1)).
    + intros y Heq. symmetry; exact Heq.
    + exact H_loc_eq.
  - exact H_g_cont.
Qed.

(* 积分区间可加性 *)
Lemma RInt_add_interval (f : R -> R) (a b c : R) :
  a <= b -> b <= c ->
  ex_RInt f a b -> ex_RInt f b c ->
  RInt f a b + RInt f b c = RInt f a c.
Proof.
  intros _ _ H1 H2.
  apply (RInt_Chasles f a b c); assumption.
Qed.

(* 自然数后继的实数表示 *)
Lemma INR_S_eq : forall k, INR (S k) = match k with 0 => 1 | S _ => INR k + 1 end.
Proof. intros [|k]; simpl; auto. Qed.

(* f 在自然数区间上的可积性 *)
Lemma ex_RInt_f_on_nat_interval (s : Complex) (Hre : 1 < ℜ(s)) (a b : nat) (Ha : (0 < a)%nat) (Hab : (a <= b)%nat) :
  let f := fun t : R => match Rlt_dec 0 t with left H => gamma_integrand_real s t H | right _ => 0 end in
  ex_RInt f (INR a) (INR b).
Proof.
  intros f.
  apply ex_RInt_continuous with (f := f) (a := INR a) (b := INR b).
  intros x Hx.
  destruct Hx as [Hlow Hhigh].
  assert (Hle_ab : INR a <= INR b) by (apply le_INR; lia).
  rewrite (Rmin_left (INR a) (INR b) Hle_ab) in Hlow.
  rewrite (Rmax_right (INR a) (INR b) Hle_ab) in Hhigh.
  assert (Hx_pos : 0 < x).
  { apply Rlt_le_trans with (INR a); [apply lt_0_INR; lia | exact Hlow]. }
  apply continuity_pt_to_continuous_simple.
  apply f_continuous_positive; auto.
Qed.

(* f 在自然数区间上的积分 Chasles 关系 *)
Lemma RInt_f_nat_Chasles (s : Complex) (Hre : 1 < ℜ(s)) (a b c : nat) (Ha : (0 < a)%nat) (Hab : (a <= b)%nat) (Hbc : (b <= c)%nat) :
  let f := fun t : R => match Rlt_dec 0 t with left H => gamma_integrand_real s t H | right _ => 0 end in
  RInt f (INR a) (INR c) = RInt f (INR a) (INR b) + RInt f (INR b) (INR c).
Proof.
  intros f.
  pose proof (ex_RInt_f_on_nat_interval s Hre a b Ha Hab) as Hex_ab.
  assert (Hb_pos : (0 < b)%nat) by lia.
  pose proof (ex_RInt_f_on_nat_interval s Hre b c Hb_pos Hbc) as Hex_bc.
  rewrite <- (RInt_Chasles f (INR a) (INR b) (INR c) Hex_ab Hex_bc).
  unfold plus; reflexivity.
Qed.

(* g 的定义等式 *)
Lemma g_eq_definition (s : Complex) (Hre : 1 < ℜ(s)) (k : nat) :
  let f := fun t : R => match Rlt_dec 0 t with left H => gamma_integrand_real s t H | right _ => 0 end in
  let g := fun k => RInt f (INR k) (INR (S k)) in
  RInt f (INR k) (match k with 0%nat => 1 | S _ => INR k + 1 end) = g k.
Proof.
  intros f g.
  unfold g.
  destruct k.
  - simpl. reflexivity.
  - simpl. rewrite <- S_INR. reflexivity.
Qed.

(* [清理] 已删除 gamma_integrand_norm_eq：其陈述（含 sqrt(1+(τ ln t)²) 因子）基于旧的截断
   被积函数，对修复后的真被积函数不成立；真被积函数的模等式见本文件末尾新模块
   GammaIntegrandComplex.gamma_integrand_norm（= e^{-t}·Rpower t (σ-1)）。 *)

(* 定理：广义积分的单调收敛 *)
Theorem RInt_gen_monotone_convergence (f : R -> R) (c : R) (Hc_pos : 0 < c) :
  (forall t, 0 < t <= c -> 0 <= f t) ->
  (forall u, 0 < u < c -> ex_RInt f u c) ->
  (exists M : R, forall u, 0 < u < c -> RInt f u c <= M) ->
  ex_RInt_gen f (at_right 0) (at_point c).
Proof.
  intros Hf_nonneg Hf_integrable_uc Hf_bounded.
  set (F := fun u : R => if Rlt_dec 0 u then if Rlt_dec u c then RInt f u c else 0 else 0).
  set (S := fun x : R => exists u : R, 0 < u < c /\ x = F u).

  assert (F_decreasing : forall u1 u2, 0 < u1 /\ u1 < u2 /\ u2 < c -> F u2 <= F u1).
  {
    intros u1 u2 [Hu1_pos [Hu1_lt_u2 Hu2_lt_c]].
    unfold F.
    destruct (Rlt_dec 0 u1) as [|H1_not]; [|exfalso; lra].
    destruct (Rlt_dec u1 c) as [|H2_not]; [|exfalso; lra].
    destruct (Rlt_dec 0 u2) as [|H3_not]; [|exfalso; lra].
    destruct (Rlt_dec u2 c) as [|H4_not]; [|exfalso; lra].
    simpl.
    assert (Hex_u1c : ex_RInt f u1 c) by (apply Hf_integrable_uc; split; lra).
    assert (Hex_u2c : ex_RInt f u2 c) by (apply Hf_integrable_uc; split; lra).
    assert (Hex_u1u2 : ex_RInt f u1 u2).
      apply (ex_RInt_Chasles_1 f u1 u2 c); [split; lra | exact Hex_u1c].
    assert (H_nonneg : 0 <= RInt f u1 u2).
      apply RInt_ge_0; [lra | exact Hex_u1u2 | intros t Ht; apply Hf_nonneg; split; lra].
    assert (H_chasles : RInt f u1 c = RInt f u1 u2 + RInt f u2 c).
      symmetry; apply (RInt_Chasles f u1 u2 c); assumption.
    lra.
  }

  assert (S_bounded : exists M0 : R, forall x, S x -> x <= M0).
  {
    destruct Hf_bounded as [M HM].
    exists M.
    intros x [u [Hu_range ->]].
    unfold F.
    destruct (Rlt_dec 0 u) as [|H1_not]; [|exfalso; lra].
    destruct (Rlt_dec u c) as [|H2_not]; [|exfalso; lra].
    simpl; apply HM; exact Hu_range.
  }
  assert (S_nonempty : exists x, S x).
  {
    exists (F (c/2)).
    unfold S; exists (c/2); split; [lra | reflexivity].
  }

  pose proof (completeness S S_bounded S_nonempty) as [l Hl_lub].
  destruct Hl_lub as [Hsup Hlub].

  assert (Hlim : filterlim F (at_right 0) (locally l)).
  {
    intros P [eps Heps].
    set (e := pos eps). assert (He : 0 < e) by apply cond_pos.

    assert (exists x, S x /\ x > l - e).
    {
      destruct (classic (exists x, S x /\ x > l - e)) as [H|H]; [exact H|].
      exfalso.
      assert (H_ub : is_upper_bound S (l - e)).
      { intros x Hx. apply Rnot_lt_le; intro Hlt. apply H; exists x; auto. }
      specialize (Hlub (l - e) H_ub).
      lra.
    }
    destruct H as [x [Hx_S Hx_gt]].
    destruct Hx_S as [u0 [Hu0_range ->]].
    destruct Hu0_range as [Hu0_pos Hu0_lt_c].
    unfold F in *.
    destruct (Rlt_dec 0 u0) as [|H1_not]; [|exfalso; lra].
    destruct (Rlt_dec u0 c) as [|H2_not]; [|exfalso; lra].
    simpl in *.

    assert (H_le : forall u, 0 < u < u0 -> F u <= l).
    {
      intros u Hu.
      apply Hsup.
      exists u.
      split; [split; lra | reflexivity].
    }

    assert (H_ge : forall u, 0 < u < u0 -> F u > l - e).
    {
      intros u Hu.
      assert (Fu_eq : F u = RInt f u c).
      { unfold F. destruct (Rlt_dec 0 u) as [Hpos|Hneg]; [|exfalso; lra].
        destruct (Rlt_dec u c) as [Hltc|Hgec]; [|exfalso; lra].
        reflexivity. }
      assert (Fu0_eq : F u0 = RInt f u0 c).
      { unfold F. destruct (Rlt_dec 0 u0) as [Hpos|Hneg]; [|exfalso; lra].
        destruct (Rlt_dec u0 c) as [Hltc|Hgec]; [|exfalso; lra].
        reflexivity. }
      rewrite Fu_eq.
      assert (F_u0_le_F_u : RInt f u0 c <= RInt f u c).
      {
        assert (F_u0_le_F_u' : F u0 <= F u) by (apply F_decreasing with (u1 := u) (u2 := u0); split; [| split]; lra).
        rewrite Fu_eq, Fu0_eq in F_u0_le_F_u'.
        exact F_u0_le_F_u'.
      }
      apply Rlt_le_trans with (RInt f u0 c); [exact Hx_gt | exact F_u0_le_F_u].
    }

    exists (mkposreal u0 Hu0_pos).
    intros u Hu_ball Hu_pos.
    simpl in Hu_ball.
    apply Rabs_lt_between in Hu_ball; destruct Hu_ball as [_ Hu_lt].
    rewrite Rminus_0_r in Hu_lt.
    assert (H_range : 0 < u < u0) by (split; [exact Hu_pos | exact Hu_lt]).
    apply Heps.
    unfold ball, AbsRing_ball; simpl.
    apply Rabs_def1.
    - apply Rle_lt_trans with 0.
      + apply Rle_minus. apply H_le; exact H_range.
      + exact He.
    - assert (H_ge_u : l - e < F u) by (apply H_ge; exact H_range).
      apply (Rplus_lt_compat_r (-l)) in H_ge_u.
      replace (l - e + - l) with (-e) in H_ge_u by lra.
      exact H_ge_u.
  }

  assert (H_is_RInt_gen : is_RInt_gen f (at_right 0) (at_point c) l).
  {
    intros P HP.
    destruct (locally_iff_open_ball l P) as [H_ball _].
    destruct (H_ball HP) as [eps [Heps_pos Heps]].
    set (e := mkposreal eps Heps_pos) in *.
    specialize (Hlim (fun y => ball l e y) (locally_ball l e)) as [delta Hdelta].
    simpl in Hdelta.

    set (delta' := Rmin (pos delta) (c/2)).
    assert (Hdelta'_pos : 0 < delta') by (apply Rmin_pos; [apply cond_pos | lra]).
    set (delta_pos := mkposreal delta' Hdelta'_pos).

    set (Q' := fun u => 0 < u /\ ball 0 delta_pos u).
    assert (HQ' : at_right 0 Q').
    {
      exists delta_pos.
      intros u Hu_ball Hu_pos.
      split; [exact Hu_pos | exact Hu_ball].
    }

    assert (H_ball_lt : forall u, 0 < u -> ball 0 delta_pos u -> u < delta').
    {
      intros u Hu_pos Hu_ball.
      unfold ball, AbsRing_ball in Hu_ball; simpl in Hu_ball.
      apply Rabs_lt_between in Hu_ball.
      destruct Hu_ball as [_ Hhigh].
      rewrite Rminus_0_r in Hhigh.
      exact Hhigh.
    }

    set (Q := fun u => 0 < u < delta').
    assert (HQ : at_right 0 Q).
    {
      apply filter_imp with (P := Q').
      - intros u [Hu_pos Hu_ball]; split; [exact Hu_pos | apply H_ball_lt; auto].
      - exact HQ'.
    }
    
    set (R := fun v => v = c).
    assert (HR : at_point c R) by (unfold at_point; reflexivity).

    apply Filter_prod with (Q := Q) (R := R); [exact HQ | exact HR |].
    intros u v Hu Hv.
    unfold R in Hv; subst v.
    destruct Hu as [Hu_pos Hu_lt_delta'].
    assert (Hu_lt_c : u < c).
    {
      apply Rlt_trans with (c/2).
      - apply Rlt_le_trans with delta'; [exact Hu_lt_delta' |].
        unfold delta'; apply Rmin_r.
      - lra.
    }
    assert (Hex_uc : ex_RInt f u c) by (apply Hf_integrable_uc; split; [exact Hu_pos | exact Hu_lt_c]).
    pose proof (RInt_correct f u c Hex_uc) as H_is.
    exists (RInt f u c).
    split; [exact H_is |].
    assert (Hu_lt_delta : u < delta).
    {
      apply Rlt_le_trans with delta'; [exact Hu_lt_delta' |].
      unfold delta'; apply Rmin_l.
    }
    assert (H_ball_u : ball 0 delta u).
    {
      unfold ball, AbsRing_ball; simpl.
      unfold AbsRing_ball.
      rewrite Rminus_0_r.
      rewrite Rabs_pos_eq.
      - exact Hu_lt_delta.
      - left; exact Hu_pos.
    }
    assert (H_F_u : F u = RInt f u c).
    {
      unfold F.
      destruct (Rlt_dec 0 u) as [Hpos|Hneg]; [|exfalso; lra].
      destruct (Rlt_dec u c) as [Hltc|Hgec]; [|exfalso; lra].
      reflexivity.
    }
    specialize (Hdelta u H_ball_u Hu_pos).
    rewrite H_F_u in Hdelta.
    apply Heps.
    exact Hdelta.
  }

  exists l; exact H_is_RInt_gen.
Qed.

(* g 的非负性 *)
Lemma g_nonneg_from_f_bound (f g : R -> R) (a : R)
  (Hf_bound : forall t, t >= a -> 0 <= f t <= g t) :
  forall t, t >= a -> 0 <= g t.
Proof.
  intros t Ht.
  specialize (Hf_bound t Ht) as [Hf_nonneg Hf_le_g].
  apply Rle_trans with (f t); auto.
Qed.

(* f 在 [a,b] 上的可积性 *)
Lemma f_integrable_on_interval (f : R -> R) (a : R)
  (Hf_cont : forall t, t >= a -> continuous f t) :
  forall b, b >= a -> ex_RInt f a b.
Proof.
  intros b Hb.
  apply ex_RInt_continuous with (f := f) (a := a) (b := b).
  intros z Hz.
  rewrite (Rmin_left a b) in Hz by lra.
  rewrite (Rmax_right a b) in Hz by lra.
  destruct Hz as [H1 H2]; apply Hf_cont; lra.
Qed.

(* g 在 [a,b] 上的可积性 *)
Lemma g_integrable_on_interval (g : R -> R) (a : R)
  (Hg_cont : forall t, t >= a -> continuous g t) :
  forall b, b >= a -> ex_RInt g a b.
Proof.
  intros b Hb.
  apply ex_RInt_continuous with (f := g) (a := a) (b := b).
  intros z Hz.
  rewrite (Rmin_left a b) in Hz by lra.
  rewrite (Rmax_right a b) in Hz by lra.
  destruct Hz as [H1 H2]; apply Hg_cont; lra.
Qed.

(* g 的积分上限函数的单调性 *)
Lemma g_integral_monotone (g : R -> R) (a : R)
  (Hg_cont : forall t, t >= a -> continuous g t)
  (Hg_nonneg : forall t, t >= a -> 0 <= g t) :
  let G := fun b => RInt g a b in
  forall b1 b2, a <= b1 <= b2 -> G b1 <= G b2.
Proof.
  intros G b1 b2 [Hle1 Hle2].
  assert (Hg_int_ab := g_integrable_on_interval g a Hg_cont).
  assert (Hex_g_b1b2 : ex_RInt g b1 b2).
  {
    apply ex_RInt_continuous with (f := g) (a := b1) (b := b2).
    intros z Hz.
    assert (Hmin : Rmin b1 b2 = b1) by (apply Rmin_left; lra).
    assert (Hmax : Rmax b1 b2 = b2) by (apply Rmax_right; lra).
    rewrite Hmin, Hmax in Hz.
    destruct Hz as [Hz1 Hz2].
    apply Hg_cont.
    apply Rle_ge.
    apply (Rle_trans a b1 z); [exact Hle1 | exact Hz1].
  }
  pose proof (RInt_Chasles g a b1 b2 (Hg_int_ab b1 (Rle_ge a b1 Hle1)) Hex_g_b1b2) as Hch.
  assert (H_nonneg : 0 <= RInt g b1 b2).
  {
    apply RInt_ge_0; [lra | exact Hex_g_b1b2 | intros t Ht; apply Hg_nonneg; lra].
  }
  unfold G.
  rewrite <- Hch.
  apply Rle_self_plus.
  exact H_nonneg.
Qed.

(* g 的积分上限函数收敛到 Ig *)
Lemma g_integral_limit (g : R -> R) (a : R) (Ig : R)
  (H_is_g : is_RInt_gen g (Rbar_locally a) (Rbar_locally p_infty) Ig) :
  filterlim (fun b => RInt g a b) (Rbar_locally p_infty) (locally Ig).
Proof.
  assert (HFa : Filter (Rbar_locally a)) by apply filter_filter.
  assert (HFb : Filter (Rbar_locally p_infty)) by apply filter_filter.
  pose proof (is_RInt_gen_filterlim g (Rbar_locally a) (Rbar_locally p_infty) Ig HFa HFb H_is_g) as Hlim_prod.
  set (phi := fun y => @pair R R a y).
  assert (Hlim_phi : filterlim phi (Rbar_locally p_infty) (filter_prod (Rbar_locally a) (Rbar_locally p_infty))).
  { apply filterlim_pair; [apply filterlim_const | apply filterlim_id]. }
  eapply filterlim_comp with (f := phi) (g := fun ab : R * R => RInt g (fst ab) (snd ab)).
  - exact Hlim_phi.
  - exact Hlim_prod.
Qed.

(* g 的积分上限函数被 Ig 控制 *)
Lemma g_integral_bounded (g : R -> R) (a : R) (Ig : R)
  (Hg_cont : forall t, t >= a -> continuous g t)
  (Hg_nonneg : forall t, t >= a -> 0 <= g t)
  (Hlim_G : filterlim (fun b => RInt g a b) (Rbar_locally p_infty) (locally Ig)) :
  forall b, b >= a -> RInt g a b <= Ig.
Proof.
  intros b Hb.
  destruct (Rle_or_lt (RInt g a b) Ig) as [Hle | Hgt]; [exact Hle |].
  set (eps := (RInt g a b - Ig) / 2).
  assert (Heps_pos : 0 < eps) by (unfold eps; lra).
  assert (Hloc : locally Ig (fun y => Rabs (y - Ig) < eps)).
  { apply locally_iff_open_ball; exists eps; split; [exact Heps_pos | intros y Hy; exact Hy]. }
  specialize (Hlim_G _ Hloc) as [M HM].
  set (y0 := Rmax b (M + 1)).
  assert (Hy0_ge_b : b <= y0) by apply Rmax_l.
  assert (Hy0_gt_M : M < y0) by (apply Rlt_le_trans with (M+1); [lra | apply Rmax_r]).
  assert (G_mono := g_integral_monotone g a Hg_cont Hg_nonneg).
  assert (H_G_b_le_G_y0 : RInt g a b <= RInt g a y0) by (apply G_mono; split; [lra | exact Hy0_ge_b]).
  assert (H_abs : Rabs (RInt g a y0 - Ig) < eps) by (apply HM; exact Hy0_gt_M).
  apply Rabs_lt_between' in H_abs; destruct H_abs as [_ Hpos]; unfold eps in Hpos; lra.
Qed.

(* f 的积分上限函数被 Ig 控制 *)
Lemma f_integral_upper_bound (f g : R -> R) (a : R) (Ig : R)
  (Hf_cont : forall t, t >= a -> continuous f t)
  (Hg_cont : forall t, t >= a -> continuous g t)
  (Hf_bound : forall t, t >= a -> 0 <= f t <= g t)
  (Hg_bounded : forall b, b >= a -> RInt g a b <= Ig) :
  forall b, b >= a -> RInt f a b <= Ig.
Proof.
  intros b Hb.
  apply Rle_trans with (RInt g a b).
  - apply RInt_le; try lra.
    + apply f_integrable_on_interval with (a := a); [exact Hf_cont | exact Hb].
    + apply g_integrable_on_interval with (a := a); [exact Hg_cont | exact Hb].
    + intros t Ht; destruct (Hf_bound t) as [_ Hle]; lra.
  - apply Hg_bounded; exact Hb.
Qed.

(* f 的积分上限函数单调递增 *)
Lemma f_integral_monotone (f : R -> R) (a : R)
  (Hf_cont : forall t, t >= a -> continuous f t)
  (Hf_nonneg : forall t, t >= a -> 0 <= f t) :
  let F := fun b => RInt f a b in
  forall b1 b2, a <= b1 <= b2 -> F b1 <= F b2.
Proof.
  intros F b1 b2 [Hle1 Hle2].
  assert (Hf_int_ab := f_integrable_on_interval f a Hf_cont).
  assert (Hex_f_b1b2 : ex_RInt f b1 b2).
  {
    apply ex_RInt_continuous with (f := f) (a := b1) (b := b2).
    intros z Hz.
    assert (Hmin : Rmin b1 b2 = b1) by (apply Rmin_left; lra).
    assert (Hmax : Rmax b1 b2 = b2) by (apply Rmax_right; lra).
    rewrite Hmin, Hmax in Hz.
    destruct Hz as [Hz1 Hz2].
    apply Hf_cont.
    apply Rle_ge.
    apply (Rle_trans a b1 z); [exact Hle1 | exact Hz1].
  }
  pose proof (RInt_Chasles f a b1 b2 (Hf_int_ab b1 (Rle_ge a b1 Hle1)) Hex_f_b1b2) as Hch.
  assert (H_nonneg : 0 <= RInt f b1 b2).
  {
    apply RInt_ge_0; [lra | exact Hex_f_b1b2 | intros t Ht; apply Hf_nonneg; lra].
  }
  unfold F.
  rewrite <- Hch.
  apply Rle_self_plus.
  exact H_nonneg.
Qed.

(* f 的积分上限函数的上确界存在 *)
Lemma f_sup_exists (f : R -> R) (a : R) (Ig : R)
  (Hf_ub : forall b, b >= a -> RInt f a b <= Ig) :
  { l : R | is_upper_bound (fun x => exists b, b >= a /\ x = RInt f a b) l /\
            forall M, is_upper_bound (fun x => exists b, b >= a /\ x = RInt f a b) M -> l <= M }.
Proof.
  set (S := fun x => exists b, b >= a /\ x = RInt f a b).
  assert (S_nonempty : exists x, S x) by (exists (RInt f a a); exists a; split; [lra | reflexivity]).
  assert (S_ub : exists M, forall x, S x -> x <= M) by (exists Ig; intros x [b [Hb ->]]; apply Hf_ub; exact Hb).
  destruct (completeness S S_ub S_nonempty) as [l [Hl_ub Hl_least]].
  exists l; split; [exact Hl_ub | exact Hl_least].
Qed.

(* f 的积分上限函数收敛到上确界 *)
Lemma f_limit_to_sup (f : R -> R) (a l : R)
  (F_mono : forall b1 b2, a <= b1 <= b2 -> RInt f a b1 <= RInt f a b2)
  (F_ub : forall b, b >= a -> RInt f a b <= l)
  (F_sup : forall eps : posreal, exists b0, b0 >= a /\ RInt f a b0 > l - eps) :
  filterlim (fun b => RInt f a b) (Rbar_locally p_infty) (locally l).
Proof.
  intros P [eps Heps].
  destruct (F_sup eps) as [b0 [Hb0_ge_a Hgt]].
  exists b0.
  intros b Hb.
  assert (a <= b) by (apply Rle_trans with b0; [apply Rge_le; exact Hb0_ge_a | apply Rlt_le; exact Hb]).
  assert (F_b0_le_F_b : RInt f a b0 <= RInt f a b) by (apply F_mono; split; [apply Rge_le; exact Hb0_ge_a | apply Rlt_le; exact Hb]).
  assert (F_b_le_l : RInt f a b <= l) by (apply F_ub; apply Rle_ge; assumption).
  apply Heps.
  unfold ball, AbsRing_ball; simpl.
  change (Rabs (RInt f a b - l) < pos eps).
  rewrite Rabs_minus_sym.
  assert (H_nonneg : 0 <= l - RInt f a b) by lra.
  rewrite Rabs_pos_eq; [| exact H_nonneg].
  apply Rle_lt_trans with (l - RInt f a b0).
  - apply Rplus_le_compat_l, Ropp_le_contravar; exact F_b0_le_F_b.
  - lra.
Qed.

(* f 在 a 附近的积分小量估计 *)
Lemma f_integral_near_a (f : R -> R) (a : R) (eps : posreal)
  (Hf_cont_on : forall t, a <= t <= a+1 -> continuous f t)
  (Hf_nonneg : forall t, a <= t <= a+1 -> 0 <= f t) :
  exists delta : posreal,
    forall x, Rabs (x - a) < pos delta -> x >= a ->
              Rabs (RInt f x a) < pos eps.
Proof.
  assert (exists K, forall t, a <= t <= a+1 -> Rabs (f t) <= K).
  {
    destruct (bounded_continuity f a (a+1)) as [K HK].
    - intros x Hx; apply Hf_cont_on; exact Hx.
    - exists K; intros t Ht; apply Rlt_le, HK; exact Ht.
  }
  destruct H as [K HK].
  destruct (Rle_or_lt K 0) as [HK0 | HKpos].
  - assert (H_K0 : forall t, a <= t <= a+1 -> f t = 0).
    {
      intros t Ht.
      apply Rle_antisym.
      - apply Rle_trans with (Rabs (f t)).
        + apply Rle_abs.
        + apply Rle_trans with K; [apply HK; exact Ht | exact HK0].
      - apply Hf_nonneg; exact Ht.
    }
    exists (mkposreal 1 Rlt_0_1).
    intros x Hx Hge.
    assert (Hax : a <= x) by lra.
    assert (Hx_lt_a1 : x < a + 1).
    { rewrite Rabs_pos_eq in Hx; [| lra]; simpl in Hx; lra. }
    assert (Hx_le_a1 : x <= a+1) by lra.
    assert (Hex_ax : ex_RInt f a x).
    {
      apply ex_RInt_continuous with (f := f) (a := a) (b := x).
      intros z Hz.
      destruct Hz as [Hz1 Hz2].
      assert (Hmin : Rmin a x = a) by (apply Rmin_left; lra).
      assert (Hmax : Rmax a x = x) by (apply Rmax_right; lra).
      rewrite Hmin in Hz1; rewrite Hmax in Hz2.
      assert (Ht_range : a <= z <= a+1).
      { split; [exact Hz1 | apply Rle_trans with x; [exact Hz2 | exact Hx_le_a1]]. }
      apply Hf_cont_on; exact Ht_range.
    }
    assert (H_swap : RInt f x a = - RInt f a x).
    { rewrite <- (opp_RInt_swap f a x Hex_ax). reflexivity. }
    assert (H_int_ax_eq : RInt f a x = RInt (fun _ => 0) a x).
    {
      apply RInt_ext with (f:=f) (g:=fun _ => 0) (a:=a) (b:=x).
      intros t0 Ht0.
      destruct Ht0 as [Ht0_low Ht0_high].
      assert (Hmin2 : Rmin a x = a) by (apply Rmin_left; lra).
      assert (Hmax2 : Rmax a x = x) by (apply Rmax_right; lra).
      rewrite Hmin2 in Ht0_low; rewrite Hmax2 in Ht0_high.
      assert (Ht0_range : a <= t0 <= a+1).
      {
        split.
        - apply Rlt_le; exact Ht0_low.
        - apply Rle_trans with x; [apply Rlt_le; exact Ht0_high | exact Hx_le_a1].
      }
      apply H_K0; exact Ht0_range.
    }
    assert (H_zero : RInt (fun _ => 0) a x = 0).
    { rewrite RInt_const; rewrite Rmult_0_r; reflexivity. }
    rewrite H_int_ax_eq, H_zero in H_swap.
    rewrite H_swap, Ropp_0, Rabs_R0.
    exact (cond_pos eps).
  - set (delta0 := pos eps / (2 * K)).
    assert (Hdelta0_pos : 0 < delta0) by (apply Rdiv_lt_0_compat; [apply cond_pos | apply Rmult_lt_0_compat; [lra | exact HKpos]]).
    set (delta := Rmin delta0 1).
    assert (Hdelta_pos : 0 < delta) by (apply Rmin_pos; [exact Hdelta0_pos | lra]).
    exists (mkposreal delta Hdelta_pos).
    intros x Hx Hge.
    assert (Hax : a <= x) by lra.
    rewrite Rabs_pos_eq in Hx; [| lra].
    simpl in Hx.
    assert (Hx_lt_a_delta : x < a + delta) by lra.
    assert (Hdelta_le_1 : delta <= 1) by apply Rmin_r.
    assert (Hx_le_a1 : x <= a+1) by (apply Rle_trans with (a + delta); [apply Rlt_le; exact Hx_lt_a_delta | apply Rplus_le_compat_l; exact Hdelta_le_1]).
    assert (Hex_ax : ex_RInt f a x).
    {
      apply ex_RInt_continuous with (f := f) (a := a) (b := x).
      intros z Hz.
      destruct Hz as [Hz1 Hz2].
      assert (Hmin : Rmin a x = a) by (apply Rmin_left; lra).
      assert (Hmax : Rmax a x = x) by (apply Rmax_right; lra).
      rewrite Hmin in Hz1; rewrite Hmax in Hz2.
      assert (Ht_range : a <= z <= a+1).
      { split; [exact Hz1 | apply Rle_trans with x; [exact Hz2 | exact Hx_le_a1]]. }
      apply Hf_cont_on; exact Ht_range.
    }
    assert (Hx_ge0 : 0 <= x - a) by lra.
    assert (Habs_ax : Rabs (RInt f a x) <= (x - a) * K).
    {
      apply (abs_RInt_le_const f a x K).
      - lra.
      - exact Hex_ax.
      - intros t Ht.
        apply HK.
        split; [apply Ht | apply Rle_trans with x; [apply Ht | exact Hx_le_a1]].
    }
    rewrite Rmult_comm in Habs_ax.
    assert (H_lt : K * (x - a) < pos eps / 2).
    {
      replace (pos eps / 2) with (K * delta0) by (unfold delta0; field; lra).
      apply Rmult_lt_compat_l; [exact HKpos |].
      apply Rlt_le_trans with delta; [exact Hx | apply Rmin_l].
    }
    assert (H_abs_lt_half : Rabs (RInt f a x) < pos eps / 2).
    { apply Rle_lt_trans with (K * (x - a)); [exact Habs_ax | exact H_lt]. }
    assert (H_swap : RInt f x a = - RInt f a x).
    { rewrite <- (opp_RInt_swap f a x Hex_ax). reflexivity. }
    rewrite H_swap, Rabs_Ropp.
    apply Rlt_trans with (pos eps / 2).
    - exact H_abs_lt_half.
    - assert (0 < pos eps) by apply cond_pos.
      lra.
Qed.

(* 从极限和局部小量构造广义积分 *)
Lemma build_is_RInt_gen (f : R -> R) (a l : R)
  (Hf_cont : forall t, t >= a -> continuous f t)
  (Hf_int_ab : forall b, b >= a -> ex_RInt f a b)
  (Hlim_F : filterlim (fun b => RInt f a b) (Rbar_locally p_infty) (locally l))
  (Hdelta : forall eps : posreal, exists delta : posreal,
              forall x, Rabs (x - a) < pos delta -> x >= a ->
                        Rabs (RInt f x a) < pos eps) :
  is_RInt_gen f (at_right a) (Rbar_locally p_infty) l.
Proof.
  unfold is_RInt_gen.
  intros P HP.
  destruct (locally_iff_open_ball l P) as [Hball_iff _].
  destruct (Hball_iff HP) as [eps0 [Heps0_pos Heps0]].
  set (e := mkposreal eps0 Heps0_pos) in *.
  set (e_half := mkposreal (eps0 / 2) (Rdiv_lt_0_compat eps0 2 Heps0_pos Rlt_0_2)).

  assert (exists M, forall y, y > M -> Rabs (RInt f a y - l) < pos e_half).
  {
    apply Hlim_F with (P := fun y => ball l e_half y).
    exists e_half; intros y Hy; exact Hy.
  }
  destruct H as [M HM].

  set (M' := Rmax M a).

  destruct (Hdelta e_half) as [delta Hdelta1].

  set (Q1 := fun x => a < x < a + pos delta).
  set (Q2 := fun y => y > M').

  assert (HQ1 : at_right a Q1).
  {
    unfold at_right, within.
    exists (mkposreal (pos delta) (cond_pos delta)).
    intros x Hx Hgt.
    simpl in Hx.
    apply Rabs_lt_between in Hx; destruct Hx as [H_low H_high].
    split; [exact Hgt |].
    apply (Rplus_lt_compat_r a) in H_high.
    change (minus x a) with (x - a) in H_high; lra.
  }

  assert (HQ2 : Rbar_locally p_infty Q2) by (unfold Rbar_locally; exists M'; intros y Hy; exact Hy).

  apply (Filter_prod (at_right a) (Rbar_locally p_infty)
        (fun ab => exists y0, is_RInt f (fst ab) (snd ab) y0 /\ P y0)
        Q1 Q2).
  - exact HQ1.
  - exact HQ2.
  - intros x y Hx Hy.
    destruct Hx as [Hx_gt_a Hx_lt_adelta].
    assert (Hx_ge_a : x >= a) by lra.
    assert (Hx_abs : Rabs (x - a) < pos delta).
    { rewrite Rabs_pos_eq; [| lra]; lra. }
    specialize (Hdelta1 x Hx_abs Hx_ge_a) as Hx_le.

    assert (Hy_gt_M : y > M).
    { apply (Rle_lt_trans M M' y).
      - apply Rmax_l.
      - exact Hy.
    }
    assert (Hy_ge_a : y >= a).
    { apply Rle_ge.
      apply Rle_trans with M'.
      - apply Rmax_r.
      - apply Rlt_le; exact Hy.
    }

    assert (Hy_le' : Rabs (RInt f a y - l) < pos e_half) by (apply HM; exact Hy_gt_M).

    assert (Hex_xy : ex_RInt f x y).
    {
      apply ex_RInt_continuous with (f := f) (a := x) (b := y).
      intros z Hz.
      destruct Hz as [Hz1 Hz2].
      assert (Hz_ge_a : a <= z).
      {
        assert (H_min_le : a <= Rmin x y).
        destruct (Rle_dec x y) as [Hxy|Hxy].
        - rewrite Rmin_left; [|exact Hxy].
          apply (Rge_le x a); exact Hx_ge_a.
        - rewrite Rmin_right.
          + apply (Rge_le y a); exact Hy_ge_a.
          + apply Rlt_le. apply Rnot_le_lt. exact Hxy.
        apply Rle_trans with (Rmin x y); [exact H_min_le | exact Hz1].
      }
      apply Hf_cont; apply Rle_ge; exact Hz_ge_a.
    }

    assert (Hch : RInt f a x + RInt f x y = RInt f a y).
    { apply RInt_Chasles with (f := f) (a := a) (b := x) (c := y);
      [apply Hf_int_ab; exact Hx_ge_a | exact Hex_xy]. }
    assert (H_eq : RInt f x y = RInt f a y - RInt f a x).
    { rewrite <- Hch. apply eq_sym. lra. }

    assert (H_abs_le : Rabs (RInt f x y - l) <=
                       Rabs (RInt f a y - l) + Rabs (RInt f a x)).
    {
      rewrite H_eq.
      replace (RInt f a y - RInt f a x - l) with
               ((RInt f a y - l) + (- RInt f a x)) by ring.
      apply Rle_trans with (Rabs (RInt f a y - l) + Rabs (- RInt f a x)).
      - apply Rabs_triang.
      - apply Rplus_le_compat_l.
        rewrite Rabs_Ropp.
        apply Rle_refl.
    }

    assert (Hx_le' : Rabs (RInt f a x) < e_half).
    { rewrite <- Rabs_Ropp.
      change (- RInt f a x) with (opp (RInt f a x)).
      rewrite opp_RInt_swap; [|exact (Hf_int_ab x Hx_ge_a)].
      exact Hx_le. }

    assert (H_abs_lt : Rabs (RInt f x y - l) < eps0).
    {
      apply Rle_lt_trans with (Rabs (RInt f a y - l) + Rabs (RInt f a x)).
      - exact H_abs_le.
      - apply Rlt_le_trans with (pos e_half + pos e_half).
        + apply Rplus_lt_compat; [exact Hy_le' | exact Hx_le'].
        + unfold e_half; simpl; lra.
    }

    pose proof (RInt_correct f x y Hex_xy) as H_is.
    exists (RInt f x y); split; [exact H_is |].
    apply Heps0.
    unfold ball, AbsRing_ball; simpl.
    exact H_abs_lt.
Qed.

(* 定理：广义积分比较检验 *)
Theorem RInt_gen_comparison_test (f g : R -> R) (a : R)
  (Hf_cont : forall t, t >= a -> continuous f t)
  (Hg_cont : forall t, t >= a -> continuous g t)
  (Hf_bound : forall t, t >= a -> 0 <= f t <= g t)
  (Hgen_g : ex_RInt_gen g (Rbar_locally a) (Rbar_locally p_infty)) :
  ex_RInt_gen f (at_right a) (Rbar_locally p_infty).
Proof.
  destruct Hgen_g as [Ig H_is_g].

  assert (Hf_int_ab := f_integrable_on_interval f a Hf_cont).
  assert (Hg_int_ab := g_integrable_on_interval g a Hg_cont).

  assert (Hg_nonneg := g_nonneg_from_f_bound f g a Hf_bound).
  assert (Hf_nonneg : forall t, t >= a -> 0 <= f t)
    by (intros t Ht; destruct (Hf_bound t Ht) as [H _]; exact H).

  assert (F_mono := f_integral_monotone f a Hf_cont Hf_nonneg).

  assert (Hlim_G := g_integral_limit g a Ig H_is_g).
  assert (Hg_bounded := g_integral_bounded g a Ig Hg_cont Hg_nonneg Hlim_G).

  assert (F_ub : forall b, b >= a -> RInt f a b <= Ig).
  { apply f_integral_upper_bound with (g := g); auto. }

  set (S := fun x => exists b, b >= a /\ x = RInt f a b).
  assert (S_nonempty : exists x, S x)
    by (exists (RInt f a a); exists a; split; [lra | reflexivity]).
  assert (S_ub : exists M, forall x, S x -> x <= M)
    by (exists Ig; intros x [b [Hb ->]]; apply F_ub; exact Hb).
  destruct (completeness S S_ub S_nonempty) as [l [Hl_ub Hl_least]].

  assert (F_sup : forall eps : posreal, exists b0, b0 >= a /\ RInt f a b0 > l - eps).
  {
    intros eps.
    destruct (classic (exists b0, b0 >= a /\ RInt f a b0 > l - eps)) as [H|H]; [exact H|].
    exfalso.
    assert (H_ub : is_upper_bound S (l - eps)).
    { intros x [b [Hb ->]]; apply Rnot_lt_le; intro Hlt; apply H; exists b; split; [exact Hb | exact Hlt]. }
    apply Hl_least in H_ub.
    assert (Hpos : 0 < eps) by apply cond_pos; lra.
  }
  assert (F_ub_l : forall b, b >= a -> RInt f a b <= l).
  { intros b Hb; apply Hl_ub; exists b; split; [exact Hb | reflexivity]. }
  assert (Hlim_F := f_limit_to_sup f a l F_mono F_ub_l F_sup).

  assert (Hf_cont_local : forall t, a <= t <= a+1 -> continuous f t).
  { intros t Ht; apply Hf_cont; lra. }
  assert (Hf_nonneg_local : forall t, a <= t <= a+1 -> 0 <= f t)
    by (intros t Ht; apply Hf_nonneg; lra).
  assert (Hdelta := fun eps => f_integral_near_a f a eps Hf_cont_local Hf_nonneg_local).

  assert (H_is := build_is_RInt_gen f a l Hf_cont Hf_int_ab Hlim_F Hdelta).

  exists l; exact H_is.
Qed.

(* 定义：保证半下界的 ε₀ *)
Definition eps0_choice (a b : R) (Hb_pos : 0 < b) : R := b / (2 * Rmax (Rabs a) 1).

(* ε₀ 为正 *)
Lemma eps0_pos (a b : R) (Hb_pos : 0 < b) :
  0 < eps0_choice a b Hb_pos.
Proof.
  unfold eps0_choice.
  apply Rdiv_lt_0_compat; [exact Hb_pos |].
  apply Rmult_lt_0_compat; [lra |].
  apply Rlt_le_trans with 1; [apply Rlt_0_1 | apply Rmax_r].
Qed.

(* ε₀ 下界保持引理 *)
Lemma b_minus_abs_a_eps0_ge_b_half (a b : R) (Hb_pos : 0 < b) :
  b - Rabs a * (b / (2 * Rmax (Rabs a) 1)) >= b / 2.
Proof.
  destruct (Rle_or_lt (Rabs a) 1) as [Ha_le1 | Ha_gt1].
  - assert (Hrmax : Rmax (Rabs a) 1 = 1).
    { apply Rmax_right. lra. }
    rewrite Hrmax.
    assert (H_b2_pos : 0 < b / 2) by lra.
    assert (H_step : Rabs a * (b / 2) <= 1 * (b / 2)).
    { apply Rmult_le_compat_r; lra. }
    assert (H_main : Rabs a * (b / 2) <= b / 2).
    { rewrite (Rmult_1_l (b / 2)) in H_step; exact H_step. }
    lra.
  - assert (Hrmax : Rmax (Rabs a) 1 = Rabs a).
    { apply Rmax_left; lra. }
    rewrite Hrmax.
    assert (Hra_pos : 0 < Rabs a) by lra.
    assert (Hra_ne_zero : Rabs a <> 0) by lra.
    assert (H_eq : Rabs a * (b / (2 * Rabs a)) = b / 2).
    { field; lra. }
    rewrite H_eq; lra.
Qed.

(* 绝对值估计 |a * ln t / t| ≤ |a| * ε *)
Lemma Rabs_a_ln_t_over_t_bound (a t eps : R) (Ht_pos : 0 < t) (Hln_pos : 0 < ln t) (H_abs_lt : Rabs (ln t / t) < eps) :
  Rabs (a * ln t / t) <= Rabs a * eps.
Proof.
  unfold Rdiv.
  rewrite Rabs_mult, Rabs_inv, Rabs_mult.
  rewrite (Rabs_pos_eq (ln t)); [| apply Rlt_le, Hln_pos].
  rewrite (Rabs_pos_eq t); [| apply Rlt_le, Ht_pos].
  rewrite Rmult_assoc.
  apply Rmult_le_compat_l; [apply Rabs_pos |].
  assert (H_pos : 0 < ln t * / t) by (apply Rdiv_lt_0_compat; auto).
  rewrite <- (Rabs_pos_eq (ln t * / t) (Rlt_le _ _ H_pos)).
  apply Rlt_le, H_abs_lt.
Qed.

(* 由绝对值上界得到 a·ln t / t 的下界 *)
Lemma a_ln_t_over_t_lower_bound (a t eps0 : R) (Ht_pos : 0 < t) (Hln_pos : 0 < ln t)
      (Habs : Rabs (ln t / t) < eps0) :
  a * ln t / t >= - Rabs a * eps0.
Proof.
  assert (H_abs_le : Rabs (a * ln t / t) <= Rabs a * eps0).
  { apply Rabs_a_ln_t_over_t_bound; auto. }
  apply Ropp_le_contravar in H_abs_le.
  assert (H_opp_abs_le : - Rabs (a * ln t / t) <= a * ln t / t).
  {
    destruct (Rle_or_lt 0 (a * ln t / t)) as [Hnonneg|Hneg].
    - rewrite Rabs_right; [| apply Rle_ge, Hnonneg]; lra.
    - rewrite (Rabs_left (a * ln t / t) Hneg); rewrite Ropp_involutive; apply Rle_refl.
  }
  assert (H_eq : - (Rabs a * eps0) = - Rabs a * eps0)
    by (rewrite <- Ropp_mult_distr_l; reflexivity).
  rewrite H_eq in H_abs_le.
  apply Rle_ge.
  apply Rle_trans with ( - Rabs (a * ln t / t) ); [exact H_abs_le | exact H_opp_abs_le].
Qed.

(* 由 a·ln t / t 上界推出指数衰减估计 *)
Lemma a_ln_t_minus_b_t_le_neg_t_times_b_minus_abs_a_eps0
  (a b t eps0 : R) (Ht_pos : 0 < t) (Hle : a * ln t / t <= Rabs a * eps0) :
  a * ln t - b * t <= - t * (b - Rabs a * eps0).
Proof.
  replace (a * ln t) with (t * (a * ln t / t)) by (field; lra).
  rewrite (Rmult_comm b t).
  rewrite <- Rmult_minus_distr_l.
  replace (- t * (b - Rabs a * eps0)) with (t * (Rabs a * eps0 - b)) by ring.
  rewrite !Rmult_minus_distr_l.
  apply (Rplus_le_compat_r (- (t * b))).
  apply Rmult_le_compat_l with (r := t) in Hle; [| lra].
  exact Hle.
Qed.

(* 当 t 足够大时 a·ln t - b·t 的上界 *)
Lemma a_ln_t_minus_b_t_upper_bound (a b t : R) (Hb_pos : 0 < b) (Ht_gt_1 : 1 < t)
  (Habs_ln_over_t : Rabs (ln t / t) < eps0_choice a b Hb_pos) :
  a * ln t - b * t <= - t * (b / 2).
Proof.
  set (eps0 := eps0_choice a b Hb_pos).
  assert (Ht_pos : 0 < t) by lra.
  assert (Hln_pos : 0 < ln t) by (rewrite <- ln_1; apply ln_increasing; lra).
  assert (H_abs_le : Rabs (a * ln t / t) <= Rabs a * eps0).
  { apply Rabs_a_ln_t_over_t_bound with (eps := eps0); auto. }
  assert (H_a_ln_t_over_t_le : a * ln t / t <= Rabs a * eps0).
  { apply Rle_trans with (Rabs (a * ln t / t)); [apply Rle_abs | exact H_abs_le]. }
  assert (H1 : a * ln t - b * t <= - t * (b - Rabs a * eps0)).
  { apply a_ln_t_minus_b_t_le_neg_t_times_b_minus_abs_a_eps0 with (eps0 := eps0); auto. }
  assert (Heps0_def : eps0 = b / (2 * Rmax (Rabs a) 1)).
  { unfold eps0, eps0_choice; reflexivity. }
  assert (H_ge' : b - Rabs a * eps0 >= b / 2).
  { rewrite Heps0_def; exact (b_minus_abs_a_eps0_ge_b_half a b Hb_pos). }
  assert (Ht_nonneg : 0 <= t) by lra.
  assert (H_le' : b / 2 <= b - Rabs a * eps0) by (apply Rge_le; exact H_ge').
  apply Rle_trans with (- t * (b - Rabs a * eps0)).
  - exact H1.
  - rewrite <- !Ropp_mult_distr_l.
    apply Ropp_le_contravar.
    apply Rmult_le_compat_l; [exact Ht_nonneg | exact H_le'].
Qed.

(* 当 t 足够大时 -t·(b/2) < M *)
Lemma neg_t_times_half_lt_M (t M b : R) (Hb_pos : 0 < b) (Ht_gt_2M : t > 2 * Rabs M / b) :
  - t * (b / 2) < M.
Proof.
  destruct (Rle_or_lt M 0) as [H_M_le0 | H_M_gt0].
  - rewrite Rabs_left1 in Ht_gt_2M; [| exact H_M_le0].
    rewrite <- Ropp_mult_distr_r in Ht_gt_2M.
    rewrite Rdiv_opp_l in Ht_gt_2M.
    apply Ropp_lt_cancel.
    rewrite Ropp_mult_distr_l.
    rewrite Ropp_involutive.
    apply Rmult_lt_compat_r with (r := b/2) in Ht_gt_2M.
    + assert (Heq : - (2 * M / b) * (b / 2) = - M).
        { field; lra. }
      rewrite Heq in Ht_gt_2M.
      exact Ht_gt_2M.
    + lra.
  - rewrite Rabs_right in Ht_gt_2M; [| apply Rle_ge, Rlt_le, H_M_gt0].
    apply Ropp_lt_cancel.
    replace (- (- t * (b / 2))) with (t * (b / 2)) by ring.
    apply Rlt_trans with 0.
    + rewrite <- Ropp_0; apply Ropp_lt_contravar; exact H_M_gt0.
    + assert (Ht_pos : 0 < t).
        { apply Rgt_lt.
          apply Rgt_trans with (2 * M / b).
          - exact Ht_gt_2M.
          - apply Rmult_lt_0_compat; [lra | apply Rinv_0_lt_compat, Hb_pos]. }
      apply Rmult_lt_0_compat; [exact Ht_pos | apply Rdiv_lt_0_compat; [exact Hb_pos | lra]].
Qed.

(* a·ln t - b·t 趋于 -∞ *)
Lemma a_ln_t_minus_b_t_tends_to_m_infty (a b : R) (Hb_pos : 0 < b) :
  filterlim (fun t => a * ln t - b * t) (Rbar_locally p_infty) (Rbar_locally m_infty).
Proof.
  intros Q HQ.
  destruct HQ as [M HM].
  set (eps0 := eps0_choice a b Hb_pos).
  assert (Heps0_pos : 0 < eps0) by apply eps0_pos.
  assert (Hball0 : locally 0 (ball 0 (mkposreal eps0 Heps0_pos))) by apply locally_ball.
  assert (Hlim_ln_over_t : filterlim (fun t => ln t / t) (Rbar_locally p_infty) (locally 0)) by exact ln_over_t_0.
  specialize (Hlim_ln_over_t (ball 0 (mkposreal eps0 Heps0_pos)) Hball0) as [T1 HT1].
  set (T := Rmax T1 (Rmax 1 (2 * Rabs M / b))).
  exists T.
  intros t Ht.
  assert (Ht_gt_T1 : t > T1) by (apply Rle_lt_trans with T; [apply Rmax_l | exact Ht]).
  assert (Hge1 : 1 <= T) by (apply Rle_trans with (Rmax 1 (2 * Rabs M / b)); [apply Rmax_l | apply Rmax_r]).
  assert (Hge2 : 2 * Rabs M / b <= T) by (apply Rle_trans with (Rmax 1 (2 * Rabs M / b)); [apply Rmax_r | apply Rmax_r]).
  assert (Ht_gt_1 : 1 < t) by (apply Rle_lt_trans with T; [exact Hge1 | exact Ht]).
  assert (Ht_gt_2M : t > 2 * Rabs M / b) by (apply Rle_lt_trans with T; [exact Hge2 | exact Ht]).
  assert (Habs_ln_over_t : Rabs (ln t / t) < eps0).
  { rewrite <- (Rminus_0_r (ln t / t)). apply HT1; exact Ht_gt_T1. }
  pose proof (a_ln_t_minus_b_t_upper_bound a b t Hb_pos Ht_gt_1 Habs_ln_over_t) as H_le.
  pose proof (neg_t_times_half_lt_M t M b Hb_pos Ht_gt_2M) as H_lt.
  apply HM.
  apply Rle_lt_trans with (- t * (b / 2)).
  - exact H_le.
  - exact H_lt.
Qed.

(* 指数乘幂函数趋于零 *)
Lemma Rpower_exp_neg_tends_to_0 (a b : R) (Hb_pos : 0 < b) :
  filterlim (fun t : R => Rpower t a * exp (-b * t)) (Rbar_locally p_infty) (locally 0).
Proof.
  intros P [eps Heps].
  set (e := pos eps).
  assert (He_pos : 0 < e) by apply cond_pos.
  assert (Hlim_inner := a_ln_t_minus_b_t_tends_to_m_infty a b Hb_pos).
  assert (Hlim_exp : filterlim (fun t => exp (a * ln t - b * t)) (Rbar_locally p_infty) (locally 0)).
  { apply filterlim_comp with (f := fun t => a * ln t - b * t) (g := exp) (G := Rbar_locally m_infty).
    - exact Hlim_inner.
    - apply filterlim_exp_m_infty. }
  assert (Heq_loc : Rbar_locally p_infty (fun t => Rpower t a * exp (-b * t) = exp (a * ln t - b * t))).
  {
    unfold Rbar_locally; exists 0.
    intros t Ht.
    assert (Ht_pos : 0 < t) by lra.
    unfold Rpower.
    rewrite <- exp_plus.
    f_equal.
    ring.
  }
  destruct (Hlim_exp (ball 0 eps) (locally_ball 0 eps)) as [T1 HT1].
  unfold Rbar_locally in Heq_loc; destruct Heq_loc as [T2 HT2].
  exists (Rmax T1 T2).
  intros t Ht.
  assert (Ht_gt_T1 : t > T1) by (apply Rle_lt_trans with (Rmax T1 T2); [apply Rmax_l | exact Ht]).
  assert (Ht_gt_T2 : t > T2) by (apply Rle_lt_trans with (Rmax T1 T2); [apply Rmax_r | exact Ht]).
  rewrite (HT2 t Ht_gt_T2).
  apply Heps.
  apply HT1; exact Ht_gt_T1.
Qed.

(* (0,1] 上 Gamma 积分的上界估计 *)
Lemma gamma_integral_01_upper_bound (s : Complex) (Hre : 1 < ComplexNumbers.re s) (c : R) (Hc_pos : 0 < c) (Hc_le1 : c <= 1) :
  let f := fun t : R => match Rlt_dec 0 t with left H => gamma_integrand_real s t H | right _ => 0 end in
  forall u, 0 < u < c -> RInt f u c <= 1 / (ComplexNumbers.re s - 1).
Proof.
  intros f u [Hu_pos Hu_lt_c].
  set (a := ComplexNumbers.re s - 1).
  assert (Ha_pos : 0 < a).
  { unfold a; lra. }
  assert (Ha1_pos : 0 < a + 1).
  { lra. }
  assert (Huc_le : u <= c).
  { lra. }

  assert (Hf_bound : forall t, 0 < t <= c -> f t <= Rpower t a).
  {
    intros t [Ht_pos Ht_le_c].
    assert (H_eq : f t = exp (-t) * Rpower t a).
    {
      apply H_f_eq_lemma with (s := s) (t := t).
      exact Ht_pos.
    }
    assert (H_neg_t : -t < 0) by lra.
    assert (H_exp0 : exp 0 = 1) by apply exp_0.
    assert (H_exp_strict_mono : exp (-t) < exp 0) by (apply exp_increasing; exact H_neg_t).
    assert (H_exp_lt_one : exp (-t) < 1).
    { rewrite H_exp0 in H_exp_strict_mono; exact H_exp_strict_mono. }
    assert (H_exp_le1 : exp (-t) <= 1) by (apply Rlt_le; exact H_exp_lt_one).
    assert (H_Rpower_pos : 0 < Rpower t a) by (apply Rpower_pos; lra).
    rewrite H_eq.
    assert (H_mul_le : exp (-t) * Rpower t a <= 1 * Rpower t a).
    { apply Rmult_le_compat_r; lra. }
    assert (H_one_simp : 1 * Rpower t a = Rpower t a) by ring.
    rewrite H_one_simp in H_mul_le.
    exact H_mul_le.
  }

  assert (Hex_f_uc : ex_RInt f u c).
  {
    apply ex_RInt_continuous with (f := f) (a := u) (b := c).
    intros z Hz.
    assert (Hmin : Rmin u c = u) by (apply Rmin_left; lra).
    assert (Hmax : Rmax u c = c) by (apply Rmax_right; lra).
    rewrite Hmin, Hmax in Hz.
    assert (Hz_pos : 0 < z) by lra.
    assert (Hloc_eq : locally z (fun y : R_UniformSpace => exp (- y) * Rpower y a = f y)).
    {
      apply locally_iff_open_ball.
      exists (z / 2).
      split.
      - lra.
      - intros y Hy.
        destruct (Rabs_def2 (y - z) (z/2) Hy) as [H_lt H_gt].
        assert (Hy_pos : 0 < y) by lra.
        assert (Heq : f y = exp (- y) * Rpower y a) by (apply H_f_eq_lemma; exact Hy_pos).
        rewrite <- Heq; reflexivity.
    }
    assert (Hcont_exp_neg_pt : continuity_pt (fun t => exp (-t)) z).
    {
      apply continuity_pt_comp with (f1 := fun t => -t) (f2 := exp).
      - apply continuity_pt_opp; apply continuity_pt_id.
      - apply derivable_continuous_pt; apply derivable_pt_exp.
    }
    assert (Hcont_Rpower_pt : continuity_pt (fun t => Rpower t a) z).
    { apply continuity_pt_Rpower_pos; lra. }
    assert (Hcont_prod_pt : continuity_pt (fun t => exp (-t) * Rpower t a) z).
    { apply continuity_pt_mult; assumption. }
    assert (Hg_cont : continuous (fun t => exp (-t) * Rpower t a) z).
    { apply continuity_pt_to_continuous_simple; exact Hcont_prod_pt. }
    apply continuous_ext_loc with (g := fun t => exp (-t) * Rpower t a) (x := z).
    - exact Hloc_eq.
    - exact Hg_cont.
  }

  assert (Hex_Rpower_uc : ex_RInt (fun t => Rpower t a) u c).
  {
    apply ex_RInt_continuous with (f := fun t => Rpower t a) (a := u) (b := c).
    intros z Hz.
    assert (Hmin : Rmin u c = u) by (apply Rmin_left; lra).
    assert (Hmax : Rmax u c = c) by (apply Rmax_right; lra).
    rewrite Hmin, Hmax in Hz.
    assert (Hz_pos : 0 < z) by lra.
    apply continuity_pt_filterlim.
    apply continuity_pt_Rpower_pos; lra.
  }

  assert (H_int_le : RInt f u c <= RInt (fun t => Rpower t a) u c).
  {
    apply RInt_le with (f := f) (g := fun t => Rpower t a) (a := u) (b := c).
    - lra.
    - exact Hex_f_uc.
    - exact Hex_Rpower_uc.
    - intros t Ht.
      assert (Ht_in : u < t < c) by (unfold Rmin, Rmax in Ht; lra).
      apply Hf_bound; split; lra.
  }

  assert (H_RInt_Rpower : RInt (fun t => Rpower t a) u c = (Rpower c (a + 1) - Rpower u (a + 1)) / (a + 1)).
  { apply RInt_power with (a := a) (u := u) (v := c); lra. }

  assert (H_Rpower_c_le1 : Rpower c (a + 1) <= 1).
  {
    destruct (Rle_lt_or_eq c 1 Hc_le1) as [Hc_lt1 | Hc_eq1].
    - apply Rpower_le_1; [exact Hc_pos | exact Ha1_pos | apply Rlt_le; exact Hc_lt1].
    - rewrite Hc_eq1, Rpower_1_r; apply Rle_refl.
  }
  assert (H_Rpower_u_nonneg : 0 <= Rpower u (a + 1)) by (apply Rlt_le, Rpower_pos; lra).
  assert (H_num_le1 : Rpower c (a + 1) - Rpower u (a + 1) <= 1) by lra.

  assert (H_inv_pos : 0 < / (a + 1)) by (apply Rinv_0_lt_compat; lra).
  assert (H_div_le : (Rpower c (a + 1) - Rpower u (a + 1)) / (a + 1) <= 1 / (a + 1)).
  { apply Rmult_le_compat_r with (r := / (a + 1)) in H_num_le1.
    - exact H_num_le1.
    - apply Rlt_le; exact H_inv_pos. }

  rewrite H_RInt_Rpower in H_int_le.
  assert (H_le_half : RInt f u c <= 1 / (a + 1)).
  { apply Rle_trans with (2 := H_div_le); exact H_int_le. }

  assert (H_a_lt_a1 : a < a + 1) by lra.
  assert (H_pos_mult : 0 < a * (a + 1)).
  { apply Rmult_pos_pos; [exact Ha_pos | exact Ha1_pos]. }
  assert (H4 : / (a + 1) < / a).
  { apply Rinv_lt_contravar; [exact H_pos_mult | exact H_a_lt_a1]. }
  assert (H_final_ineq : 1 / (a + 1) < 1 / a).
  { unfold Rdiv; repeat rewrite Rmult_1_l; exact H4. }
  apply Rle_trans with (1 / (a + 1)).
  - exact H_le_half.
  - apply Rlt_le; exact H_final_ineq.
Qed.

(* Gamma 被积函数实部非负性 *)
Lemma gamma_integrand_real_nonneg (s : Complex) (Hre : 1 < ComplexNumbers.re s) :
  forall t : R, 0 < t ->
  (match Rlt_dec 0 t with left H => gamma_integrand_real s t H | right _ => 0 end) >= 0.
Proof.
  intros t Ht_pos.
  destruct (Rlt_dec 0 t) as [Hlt | Hnot]; [| contradiction Hnot; exact Ht_pos].
  unfold gamma_integrand_real; simpl.
  set (a := ComplexNumbers.re s - 1).
  assert (Ha_pos : 0 < a) by (unfold a; lra).
  replace (real_pow t a Hlt) with (Rpower t a) by reflexivity.
  apply Rle_ge.
  apply Rmult_le_pos.
  - apply Rlt_le, exp_pos.
  - apply Rlt_le, Rpower_pos; lra.
Qed.

(* 积分分段求和引理（自定义版） *)
Lemma H_int_sum (s : Complex) (Hre : 1 < ℜ(s)) :
  forall N0 M0 : nat, (0 < N0)%nat -> (N0 <= M0)%nat ->
  let f := fun t : R =>
            match Rlt_dec 0 t with
            | left H => gamma_integrand_real s t H
            | right _ => 0
            end in
  let g := fun k : nat => RInt f (INR k) (INR (S k)) in
  my_sum_f_R0 g M0 - my_sum_f_R0 g N0 = RInt f (INR N0) (INR M0).
Proof.
  intros N0 M0 HNpos Hle.
  set (f := fun t : R =>
            match Rlt_dec 0 t with
            | left H => gamma_integrand_real s t H
            | right _ => 0
            end).
  set (g := fun k : nat => RInt f (INR k) (INR (S k)) : R).

  assert (H_cont_f_pos : forall t : R, 0 < t -> continuous f t).
  {
    intros t Ht_pos.
    apply continuity_pt_to_continuous_simple.
    exact (f_continuous_positive s t Ht_pos).
  }

  assert (H_ex_RInt_nat : forall k : nat, (0 < k)%nat -> ex_RInt f (INR k) (INR (S k))).
  {
    intros k Hk_pos.
    apply (ex_RInt_f_on_nat_interval s Hre k (S k) Hk_pos).
    apply Nat.le_succ_diag_r.
  }

  assert (H_ex_RInt_le : forall n m : nat, (0 < n)%nat -> (n <= m)%nat -> ex_RInt f (INR n) (INR m)).
  {
    intros n m Hn_pos Hnm_le.
    induction m as [|m IHm].
    - inversion Hnm_le; lia.
    - destruct (Nat.eq_dec n (S m)) as [Heq | Hne].
      + subst n. apply ex_RInt_point.
      + assert (Hle' : (n <= m)%nat) by lia.
        assert (Hn_pos' : (0 < n)%nat) by exact Hn_pos.
        specialize (IHm Hle').
        apply ex_RInt_Chasles with (b := INR m).
        * exact IHm.
        * apply H_ex_RInt_nat. lia.
  }

  revert N0 Hle HNpos.
  induction M0 as [|M' IH].
  - intros N0 Hle HNpos.
    exfalso. lia.
  - intros N0 Hle HNpos.
    destruct (Nat.eq_dec N0 (S M')) as [Heq | Hne].
    + subst N0.
      cbv zeta.
      rewrite Rminus_diag.
      rewrite RInt_point.
      reflexivity.
    + assert (Hle' : (N0 <= M')%nat) by lia.
      assert (IH_eq : my_sum_f_R0 g M' - my_sum_f_R0 g N0 = RInt f (INR N0) (INR M')).
      { specialize (IH N0 Hle' HNpos); exact IH. }

      assert (H_rec : my_sum_f_R0 g (S M') = my_sum_f_R0 g M' + g M').
      { unfold my_sum_f_R0; simpl; reflexivity. }

      assert (H_ex1 : ex_RInt f (INR N0) (INR M')) by (apply H_ex_RInt_le; lia).
      assert (H_ex2 : ex_RInt f (INR M') (INR (S M'))) by (apply H_ex_RInt_nat; lia).
      assert (H_chasles : RInt f (INR N0) (INR (S M')) =
                         RInt f (INR N0) (INR M') + RInt f (INR M') (INR (S M'))).
      { symmetry. apply RInt_Chasles with (f := f) (a := INR N0) (b := INR M') (c := INR (S M')); assumption. }

      cbv zeta.
      change (my_sum_f_R0 g (S M') - my_sum_f_R0 g N0 = RInt f (INR N0) (INR (S M'))).
      rewrite H_rec.
      rewrite H_chasles.
      replace (my_sum_f_R0 g M' + g M' - my_sum_f_R0 g N0)
         with ((my_sum_f_R0 g M' - my_sum_f_R0 g N0) + g M') by ring.
      rewrite IH_eq.
      reflexivity.
Qed.

(* 积分分段求和引理（标准版） *)

(* 部分和与自定义求和的转换关系 *)
Lemma sum_f_R0_eq_my_plus : forall (f : nat -> R) n,
  sum_f_R0 f n = my_sum_f_R0 f (S n).
Proof.
  intros f n.
  induction n as [|n IH].
  - simpl; unfold my_sum_f_R0; simpl; rewrite Rplus_0_l; reflexivity.
  - simpl sum_f_R0; rewrite IH; unfold my_sum_f_R0 at 2; simpl; reflexivity.
Qed.

(* 积分分段求和（专业版） *)

(* 积分望远镜求和 *)
Lemma integral_telescoping_sum (f : R -> R) (N0 M0 : nat)
  (Hpos : (0 < N0)%nat) (Hle : (N0 <= M0)%nat)
  (Hcont : forall t, INR N0 <= t <= INR M0 -> continuity_pt f t)
  (Ht_pos : forall t, INR N0 <= t <= INR M0 -> 0 < t) :
  sum_f_R0 (fun k => RInt f (INR k) (INR (S k))) (M0 - 1) -
  sum_f_R0 (fun k => RInt f (INR k) (INR (S k))) (N0 - 1) =
  RInt f (INR N0) (INR M0).
Proof.
  induction M0 as [|M0' IH] in Hle, Hcont, Ht_pos |- *.
  - exfalso; lia.
  - destruct (Nat.eq_dec N0 (S M0')) as [Heq | Hne].
    + subst N0. rewrite Rminus_diag. rewrite RInt_point. reflexivity.
    + assert (Hle' : (N0 <= M0')%nat) by lia.
      assert (Hcont' : forall t, INR N0 <= t <= INR M0' -> continuity_pt f t).
      { intros t Ht. apply Hcont. split.
        - apply (proj1 Ht).
        - apply Rle_trans with (INR M0'); [apply (proj2 Ht) | apply le_INR; lia]. }
      assert (Ht_pos' : forall t, INR N0 <= t <= INR M0' -> 0 < t).
      { intros t Ht. apply Ht_pos. split.
        - apply (proj1 Ht).
        - apply Rle_trans with (INR M0'); [apply (proj2 Ht) | apply le_INR; lia]. }
      assert (H_idx : (S M0' - 1)%nat = M0') by lia.
      rewrite H_idx.
      assert (M0'_ge_1 : (M0' >= 1)%nat) by lia.
      replace M0' with (S (M0' - 1))%nat by lia.
      rewrite sum_f_R0_S.
      rewrite Rplus_comm.
      replace (RInt f (INR (S (M0' - 1))) (INR (S (S (M0' - 1)))) +
               sum_f_R0 (fun k => RInt f (INR k) (INR (S k))) (M0' - 1) -
               sum_f_R0 (fun k => RInt f (INR k) (INR (S k))) (N0 - 1))
        with (RInt f (INR (S (M0' - 1))) (INR (S (S (M0' - 1)))) +
              (sum_f_R0 (fun k => RInt f (INR k) (INR (S k))) (M0' - 1) -
               sum_f_R0 (fun k => RInt f (INR k) (INR (S k))) (N0 - 1))) by ring.
      rewrite (IH Hle' Hcont' Ht_pos').
      replace (INR (S (M0' - 1))) with (INR M0') by (apply f_equal; lia).
      replace (INR (S (S (M0' - 1)))) with (INR (S M0')) by (apply f_equal; lia).
      assert (H_ex1 : ex_RInt f (INR N0) (INR M0')).
      { apply (@ex_RInt_continuous R_CompleteNormedModule f (INR N0) (INR M0')).
        intros z Hz.
        apply continuity_pt_to_continuous_simple.
        apply Hcont'.
        destruct Hz as [Hz1 Hz2].
        rewrite (Rmin_left (INR N0) (INR M0')) in Hz1 by (apply le_INR; lia).
        rewrite (Rmax_right (INR N0) (INR M0')) in Hz2 by (apply le_INR; lia).
        split; [exact Hz1 | exact Hz2]. }
      assert (H_ex2 : ex_RInt f (INR M0') (INR (S M0'))).
      { apply (@ex_RInt_continuous R_CompleteNormedModule f (INR M0') (INR (S M0'))).
        intros z Hz.
        apply continuity_pt_to_continuous_simple.
        destruct Hz as [Hz1 Hz2].
        rewrite (Rmin_left (INR M0') (INR (S M0'))) in Hz1 by (apply le_INR; lia).
        rewrite (Rmax_right (INR M0') (INR (S M0'))) in Hz2 by (apply le_INR; lia).
        assert (H_ge_N0 : INR N0 <= z).
        { apply Rle_trans with (INR M0'); [apply le_INR; exact Hle' | exact Hz1]. }
        apply Hcont; split; [exact H_ge_N0 | exact Hz2]. }
      rewrite Rplus_comm.
      apply (RInt_Chasles f (INR N0) (INR M0') (INR (S M0')) H_ex1 H_ex2).
Qed.

(* 求和偏移公式 *)
Lemma sum_f_R0_shift_std (f : nat -> R) (n m : nat) :
  (S n <= m)%nat ->
  sum_f_R0 f m - sum_f_R0 f n = sum_f_R0 (fun i => f (S n + i)%nat) (m - S n).
Proof.
  intros H.
  induction m as [|m' IH] in H |- *.
  - exfalso; lia.
  - destruct (Nat.eq_dec n (S m')) as [Heq | Hne].
    + exfalso; lia.
    + destruct (Nat.eq_dec n m') as [Heq2 | Hne2].
      * 
        subst n.
        simpl.
        rewrite Nat.sub_diag.
        simpl.
        rewrite Nat.add_0_r.
        ring.
      * 
        assert (Hle : (S n <= m')%nat) by lia.
        specialize (IH Hle).
        rewrite sum_f_R0_S.
        replace (sum_f_R0 f m' + f (S m') - sum_f_R0 f n)
          with ((sum_f_R0 f m' - sum_f_R0 f n) + f (S m')) by ring.
        rewrite IH.
        replace (S m' - S n)%nat with (S (m' - S n))%nat by lia.
        rewrite sum_f_R0_S.
        replace (S n + S (m' - S n))%nat with (S m') by lia.
        reflexivity.
Qed.

(* 幂级数尾部积分上界 *)
Lemma power_series_tail_bound (σ : R) (Hσ : 1 < σ) (N M : nat) :
  (0 < N)%nat -> (N <= M)%nat ->
  sum_f_R0 (fun k => Rpower (INR (S k)) (-σ)) M -
  sum_f_R0 (fun k => Rpower (INR (S k)) (-σ)) N
    <= RInt (fun x => Rpower x (-σ)) (INR N) (INR M).
Proof.
  intros HNpos Hle.
  set (f := fun x => Rpower x (-σ)).

  assert (Hdec : forall x y, 0 < x < y -> f y <= f x).
  { intros x y Hxy.
    apply Rlt_le.
    apply Rpower_neg_decreasing.
    - exact Hxy.
    - lra. }

  assert (Hcont : forall x, 0 < x -> continuous f x).
  {
    intros x Hx.
    unfold f.
    assert (Hcont_pow_pt : continuity_pt (fun t => Rpower t σ) x).
    { apply continuity_pt_Rpower_pos; [lra | exact Hx]. }
    assert (Hpow_neq : Rpower x σ <> 0) by (apply Rgt_not_eq, Rpower_pos; exact Hx).
    pose proof (continuity_pt_inv (fun t => Rpower t σ) x Hcont_pow_pt Hpow_neq) as Hcont_inv_pt.
    assert (Hcont_inv : continuous (fun t => / Rpower t σ) x).
    { apply continuity_pt_to_continuous_simple; exact Hcont_inv_pt. }
    assert (Hloc_eq : locally x (fun t => Rpower t (-σ) = / Rpower t σ)).
    {
      apply locally_iff_open_ball.
      exists (x/2); split; [lra |].
      intros y Hy.
      assert (Hy_pos : 0 < y) by (apply Rabs_lt_between in Hy; lra).
      rewrite (Rpower_Ropp y σ).
      reflexivity.
    }
    apply continuous_ext_loc with (g := fun t => / Rpower t σ) (x := x).
    - apply filter_imp with (P := fun t => Rpower t (-σ) = / Rpower t σ).
      + intros t Heq; symmetry; exact Heq.
      + exact Hloc_eq.
    - exact Hcont_inv.
  }

  assert (H_int : ex_RInt f (INR N) (INR M)).
  { apply ex_RInt_continuous with (f := f) (a := INR N) (b := INR M).
    intros z Hz.
    rewrite (Rmin_left (INR N) (INR M)) in Hz by (apply le_INR; lia).
    rewrite (Rmax_right (INR N) (INR M)) in Hz by (apply le_INR; lia).
    assert (Hz_pos : 0 < z).
    { apply Rlt_le_trans with (INR N); [apply lt_0_INR; exact HNpos | exact (proj1 Hz)]. }
    apply Hcont.
    exact Hz_pos. }

  assert (H_step : forall k : nat, (N <= k < M)%nat ->
    f (INR (S k)) <= RInt f (INR k) (INR (S k))).
  {
    intros k Hk.
    assert (Hk_pos : 0 < INR k) by (apply lt_0_INR; lia).
    assert (Hk1_pos : 0 < INR (S k)) by (apply lt_0_INR; lia).
    assert (Hex : ex_RInt f (INR k) (INR (S k))).
    { apply ex_RInt_continuous with (f := f) (a := INR k) (b := INR (S k)).
      intros z Hz.
      rewrite (Rmin_left (INR k) (INR (S k))) in Hz by (apply le_INR; lia).
      rewrite (Rmax_right (INR k) (INR (S k))) in Hz by (apply le_INR; lia).
      apply Hcont.
      apply Rlt_le_trans with (INR k); [exact Hk_pos | exact (proj1 Hz)]. }
    assert (H_min : forall x, INR k <= x <= INR (S k) -> f (INR (S k)) <= f x).
    {
      intros x Hx.
      assert (Hx_gt_0 : 0 < x) by (apply Rlt_le_trans with (INR k); [exact Hk_pos | apply Hx]).
      destruct (Rlt_dec x (INR (S k))) as [Hlt | Hge].
      - apply (Hdec x (INR (S k)) (conj Hx_gt_0 Hlt)).
      - assert (x = INR (S k)).
        { apply Rle_antisym.
          - apply Hx.
          - apply Rnot_lt_le in Hge. exact Hge. }
        rewrite H; apply Rle_refl.
    }
    assert (H_const_int : ex_RInt (fun _ => f (INR (S k))) (INR k) (INR (S k))) by apply ex_RInt_const.
    assert (H_le : RInt (fun _ => f (INR (S k))) (INR k) (INR (S k)) <= RInt f (INR k) (INR (S k))).
    {
      apply RInt_le.
      - apply le_INR; lia.
      - exact H_const_int.
      - exact Hex.
      - intros t Ht; apply H_min; split; apply Rlt_le; apply Ht.
    }
    rewrite RInt_const in H_le.
    rewrite S_INR in H_le.
    replace (INR k + 1 - INR k) with 1 in H_le by lra.
    replace (INR k + 1) with (INR (S k)) in H_le by (rewrite S_INR; reflexivity).
    simpl in H_le; rewrite Rmult_1_l in H_le.
    exact H_le.
  }

  assert (H_left_eq : sum_f_R0 (fun k => f (INR (S k))) M - sum_f_R0 (fun k => f (INR (S k))) N
                = sum_f_R0 (fun k => f (INR (S k))) (M-1) - sum_f_R0 (fun k => f (INR (S k))) (N-1)
                  + (f (INR (S M)) - f (INR (S N)))).
  {
    destruct N as [|N'], M as [|M'].
    - lia.
    - simpl; lia.
    - simpl; lia.
    - simpl.
      rewrite Nat.sub_0_r.
      rewrite Nat.sub_0_r.
      ring.
  }

  replace (sum_f_R0 (fun k => Rpower (INR (S k)) (-σ)) M)
    with (sum_f_R0 (fun k => f (INR (S k))) M)
    by (apply sum_f_R0_ext; intros k; unfold f; reflexivity).
  replace (sum_f_R0 (fun k => Rpower (INR (S k)) (-σ)) N)
    with (sum_f_R0 (fun k => f (INR (S k))) N)
    by (apply sum_f_R0_ext; intros k; unfold f; reflexivity).
  rewrite H_left_eq.

  assert (H_neg : f (INR (S M)) - f (INR (S N)) <= 0).
  {
    destruct (lt_dec N M) as [Hlt | Heq].
    - apply Rle_minus.
      apply Hdec.
      split.
      + apply lt_0_INR, Nat.lt_0_succ.
      + apply lt_INR; lia.
    - assert (N = M) by lia.
      subst N.
      rewrite Rminus_diag.
      apply Rle_refl.
  }

  assert (Ht_pos_for_int : forall t, INR N <= t <= INR M -> 0 < t).
  { intros t Ht. apply Rlt_le_trans with (INR N); [apply lt_0_INR; exact HNpos | apply Ht]. }
  assert (Hcont_for_int : forall t, INR N <= t <= INR M -> continuity_pt f t).
  { intros t Ht. apply continuity_pt_filterlim. apply Hcont. apply (Ht_pos_for_int t Ht). }

  assert (H_sum_le : sum_f_R0 (fun k => f (INR (S k))) (M-1) - sum_f_R0 (fun k => f (INR (S k))) (N-1)
                    <= sum_f_R0 (fun k => RInt f (INR k) (INR (S k))) (M-1) - sum_f_R0 (fun k => RInt f (INR k) (INR (S k))) (N-1)).
  {
    set (g := fun k => f (INR (S k))).
    set (h := fun k => RInt f (INR k) (INR (S k))).
    destruct (Nat.eq_dec N M) as [Heq | Hne].
    - 
      subst N.
      rewrite Rminus_diag.
      replace (sum_f_R0 h (M-1) - sum_f_R0 h (M-1)) with 0 by ring.
      apply Rle_refl.
    - 
      assert (Hle_shift : (S (N-1) <= M-1)%nat).
      { rewrite Nat.sub_1_r. lia. }
      rewrite (sum_f_R0_shift_std g (N-1) (M-1) Hle_shift).
      rewrite (sum_f_R0_shift_std h (N-1) (M-1) Hle_shift).
      set (len := ((M-1) - S (N-1))%nat).
      assert (H_ineq : forall i : nat, (i <= len)%nat -> g ((S (N-1) + i)%nat) <= h ((S (N-1) + i)%nat)).
      {
        intros i Hi.
        assert (Hk_range : (N <= (S (N-1) + i)%nat < M)%nat).
        {
          rewrite Nat.sub_1_r.
          replace (S (N-1)) with N by lia.
          lia.
        }
        apply H_step in Hk_range.
        exact Hk_range.
      }
      induction len as [|len' IH].
      + simpl. apply H_ineq. lia.
      + simpl sum_f_R0.
        apply Rplus_le_compat.
        * apply IH; intros i Hi; apply H_ineq; lia.
        * apply H_ineq; lia.
  }

  assert (Heq_int : sum_f_R0 (fun k => RInt f (INR k) (INR (S k))) (M-1) - sum_f_R0 (fun k => RInt f (INR k) (INR (S k))) (N-1) = RInt f (INR N) (INR M)).
  { apply integral_telescoping_sum; auto. }

  set (A := sum_f_R0 (fun k => f (INR (S k))) (M-1) - sum_f_R0 (fun k => f (INR (S k))) (N-1)).
  set (B := f (INR (S M)) - f (INR (S N))).
  set (C := sum_f_R0 (fun k => RInt f (INR k) (INR (S k))) (M-1) - sum_f_R0 (fun k => RInt f (INR k) (INR (S k))) (N-1)).

  assert (A + B <= A) as H_AB_le_A.
  { apply Rle_trans with (A + 0).
    - apply Rplus_le_compat_l. exact H_neg.
    - rewrite Rplus_0_r; apply Rle_refl. }
  assert (A <= C) as H_A_le_C. { exact H_sum_le. }

  apply Rle_trans with (r2 := C).
  - apply Rle_trans with (r2 := A); [exact H_AB_le_A | exact H_A_le_C].
  - unfold C; rewrite Heq_int; apply Rle_refl.
Qed.

(* 尾部差上界 *)
Lemma tail_difference_bound (σ : R) (Hσ : 1 < σ) (N M : nat) :
  (0 < N)%nat -> (N <= M)%nat ->
  sum_f_R0 (fun k => Rpower (INR (S k)) (-σ)) M -
  sum_f_R0 (fun k => Rpower (INR (S k)) (-σ)) N
    <= (Rpower (INR N) (1 - σ)) / (σ - 1).
Proof.
  intros HNpos Hle.
  pose proof (power_series_tail_bound σ Hσ N M HNpos Hle) as Hbound.

  assert (H_int_eq : RInt (fun x => Rpower x (-σ)) (INR N) (INR M) =
                     (Rpower (INR N) (1 - σ) - Rpower (INR M) (1 - σ)) / (σ - 1)).
  {
    set (a := 1 - σ).
    assert (Ha_neg : a < 0) by (apply Rlt_minus; exact Hσ).
    assert (Ha_neq0 : a <> 0) by (apply Rlt_not_eq; exact Ha_neg).
    set (F := fun x => Rpower x a / a).

    assert (H_der_int : forall x, INR N <= x <= INR M -> is_derive F x (Rpower x (-σ))).
    {
      intros x Hx.
      assert (Hx_pos : 0 < x) by (apply Rlt_le_trans with (INR N); [apply lt_0_INR; lia | apply Hx]).
      unfold F.
      assert (H_pow : is_derive (fun x => Rpower x a) x (a * Rpower x (a-1))).
      { apply is_derive_Reals; apply derivable_pt_lim_power; auto. }
      apply is_derive_scal with (k := /a) in H_pow.
      rewrite <- Rmult_assoc in H_pow.
      rewrite Rinv_l in H_pow; [| exact Ha_neq0].
      rewrite Rmult_1_l in H_pow.
      assert (Heq : a - 1 = -σ) by (unfold a; lra).
      rewrite Heq in H_pow.
      assert (Heq_fun : (fun x0 => Rpower x0 a / a) = (fun x0 => /a * Rpower x0 a)).
      { apply functional_extensionality; intros t; unfold Rdiv; rewrite Rmult_comm; reflexivity. }
      rewrite Heq_fun.
      exact H_pow.
    }

    assert (H_cont_der : forall x, INR N <= x <= INR M -> continuous (fun x => Rpower x (-σ)) x).
    {
      intros x Hx.
      assert (Hx_pos : 0 < x) by (apply Rlt_le_trans with (INR N); [apply lt_0_INR; lia | apply Hx]).
      apply continuity_pt_to_continuous.
      unfold Rpower.
      assert (Hder_ln : derivable_pt ln x) by (apply derivable_pt_ln_manual; exact Hx_pos).
      assert (Hcont_ln : continuity_pt ln x) by (apply derivable_continuous_pt; exact Hder_ln).
      assert (Hcont_scaled : continuity_pt (fun t => (-σ) * ln t) x)
        by (apply continuity_pt_scal; exact Hcont_ln).
      apply continuity_pt_comp with (f1 := fun t => (-σ) * ln t) (f2 := exp).
      - exact Hcont_scaled.
      - apply derivable_continuous_pt; apply derivable_pt_exp.
    }

    assert (H_is : is_RInt (fun x => Rpower x (-σ)) (INR N) (INR M) (F (INR M) - F (INR N))).
    {
      apply is_RInt_derive with (f := F) (df := fun x => Rpower x (-σ)).
      - intros x Hx.
        apply H_der_int.
        destruct Hx as [Hlow Hhigh].
        rewrite (Rmin_left (INR N) (INR M)) in Hlow by (apply le_INR; lia).
        rewrite (Rmax_right (INR N) (INR M)) in Hhigh by (apply le_INR; lia).
        split; lra.
      - intros x Hx.
        apply H_cont_der.
        destruct Hx as [Hlow Hhigh].
        rewrite (Rmin_left (INR N) (INR M)) in Hlow by (apply le_INR; lia).
        rewrite (Rmax_right (INR N) (INR M)) in Hhigh by (apply le_INR; lia).
        split; lra.
    }

    assert (H_eq : RInt (fun x => Rpower x (-σ)) (INR N) (INR M) = F (INR M) - F (INR N)).
    {
      apply (is_RInt_unique _ _ _ _ H_is).
    }

    unfold F in H_eq.
    rewrite H_eq.
    unfold Rdiv.
    rewrite (Rmult_comm (Rpower (INR M) a) (/a)).
    rewrite (Rmult_comm (Rpower (INR N) a) (/a)).
    rewrite <- Rmult_minus_distr_l.
    replace a with (- (σ - 1)) by (unfold a; lra).
    rewrite Rinv_opp.
    lra.
  }

  apply Rle_trans with (RInt (fun x => Rpower x (-σ)) (INR N) (INR M)).
  - exact Hbound.
  - rewrite H_int_eq.
    assert (H_pos : 0 <= Rpower (INR M) (1-σ)).
    { apply Rlt_le, Rpower_pos; apply lt_0_INR; lia. }
    assert (H_ineq : Rpower (INR N) (1-σ) - Rpower (INR M) (1-σ) <= Rpower (INR N) (1-σ)).
    { lra. }
    assert (H_denom : 0 < σ - 1) by lra.
    apply Rmult_le_compat_r with (r := / (σ - 1)).
    - apply Rlt_le, Rinv_0_lt_compat; exact H_denom.
    - exact H_ineq.
Qed.

(* 负指数幂定积分公式 *)
Lemma integral_of_x_neg_sigma (σ : R) (Hσ : 1 < σ) (a b : R) :
  0 < a <= b ->
  RInt (fun x => Rpower x (-σ)) a b =
  (Rpower a (1 - σ) - Rpower b (1 - σ)) / (σ - 1).
Proof.
  intros [Ha Hab].
  set (F := fun x => - Rpower x (1 - σ) / (σ - 1)).
  assert (Hder : forall x, 0 < x -> is_derive F x (Rpower x (-σ))).
  {
    intros x Hx.
    unfold F.
    set (c := - / (σ - 1)).
    assert (Heq : (fun x0 => - Rpower x0 (1-σ) / (σ-1)) = (fun x0 => c * Rpower x0 (1-σ))).
    { apply functional_extensionality; intros t; unfold c; field; lra. }
    rewrite Heq.
    assert (Hpow_lim : derivable_pt_lim (fun x => Rpower x (1-σ)) x
                                       ((1-σ) * Rpower x ((1-σ)-1))).
    { apply derivable_pt_lim_power; auto. }
    assert (H_exp_eq : (1-σ) * Rpower x ((1-σ)-1) = (1-σ) * Rpower x (-σ)).
    { f_equal; unfold Rpower; f_equal; lra. }
    rewrite H_exp_eq in Hpow_lim.
    assert (Hpow : is_derive (fun x => Rpower x (1-σ)) x ((1-σ) * Rpower x (-σ))).
    { apply is_derive_Reals; exact Hpow_lim. }
    apply is_derive_scal with (k := c) in Hpow.
    assert (H_eq_deriv : c * ((1-σ) * Rpower x (-σ)) = Rpower x (-σ)).
    { unfold c; field; lra. }
    rewrite H_eq_deriv in Hpow.
    exact Hpow.
  }

  assert (Hcont : forall x, 0 < x -> continuous (fun x => Rpower x (-σ)) x).
  {
    intros x Hx.
    unfold Rpower.
    assert (H_ln_cont : continuous ln x).
    { apply continuity_pt_to_continuous.
      apply derivable_continuous_pt; apply derivable_pt_ln_manual; exact Hx. }
    assert (H_scaled_cont : continuous (fun t => (-σ) * ln t) x).
    { apply continuous_mult with (f := fun _ => (-σ)) (g := ln) (x := x).
      - apply continuous_const.
      - exact H_ln_cont. }
    assert (H_exp_cont : continuous exp ((-σ) * ln x)).
    { apply continuity_pt_to_continuous.
      apply derivable_continuous_pt; apply derivable_pt_exp. }
    apply continuous_comp with (f := fun t => (-σ) * ln t) (g := exp) (x := x).
    - exact H_scaled_cont.
    - exact H_exp_cont.
  }

  assert (Hex : ex_RInt (fun x => Rpower x (-σ)) a b).
  { apply ex_RInt_continuous with (f := fun x => Rpower x (-σ)) (a := a) (b := b).
    intros z Hz.
    rewrite (Rmin_left a b Hab) in Hz.
    rewrite (Rmax_right a b Hab) in Hz.
    destruct Hz as [Hz1 Hz2].
    apply Hcont.
    apply Rlt_le_trans with a; [exact Ha | exact Hz1]. }

  assert (H_is_RInt : is_RInt (fun x => Rpower x (-σ)) a b (F b - F a)).
  { apply is_RInt_derive with (f := F) (df := fun x => Rpower x (-σ)) (a := a) (b := b).
    - intros x Hx.
      apply Hder.
      rewrite (Rmin_left a b Hab) in Hx.
      rewrite (Rmax_right a b Hab) in Hx.
      destruct Hx as [Hx1 Hx2].
      apply Rlt_le_trans with a; [exact Ha | exact Hx1].
    - intros x Hx.
      apply Hcont.
      rewrite (Rmin_left a b Hab) in Hx.
      rewrite (Rmax_right a b Hab) in Hx.
      destruct Hx as [Hx1 Hx2].
      apply Rlt_le_trans with a; [exact Ha | exact Hx1]. }

  rewrite (is_RInt_unique _ _ _ _ H_is_RInt).
  unfold F.
  simpl.
  field; lra.
Qed.

(* 差非负 *)
Lemma Rle_minus_swap : forall r1 r2 : R, r1 <= r2 -> 0 <= r2 - r1.
Proof.
  intros r1 r2 H.
  rewrite <- (Ropp_involutive (r2 - r1)), <- Ropp_0.
  apply Ropp_le_contravar.
  rewrite Ropp_minus_distr.
  apply Rle_minus; auto.
Qed.

Require Import Stdlib.Reals.RIneq.

(* 实部部分和的柯西列 *)
Lemma re_partial_sum_cauchy (s : Complex) (Hre : 1 < ℜ(s)) :
  cauchy_seq (fun N : nat => re (Csum (zeta_series_term s) N)).
Proof.
  set (σ := ℜ(s)).
  set (a := fun n : nat => Rpower (INR (S n)) (-σ)).
  assert (Ha_pos : forall n : nat, 0 <= a n).
  { intro n; apply Rlt_le; apply Rpower_pos; apply lt_0_INR; lia. }

  assert (H_cauchy_a : forall eps : R, eps > 0 -> exists N : nat, forall m n : nat, (m >= N)%nat -> (n >= N)%nat -> Rabs (sum_f_R0 a m - sum_f_R0 a n) < eps).
  { intros eps Heps.
    assert (σ_gt_1 : 1 < σ) by exact Hre.
    assert (σ_minus_1_pos : 0 < σ - 1) by lra.
    set (f := fun x : R => Rpower x (-σ)).
    set (F := fun x => - Rpower x (1-σ) / (σ-1)).

    assert (Hder_F : forall t, 0 < t -> is_derive F t (f t)).
    { intros t Ht.
      unfold F, f.
      pose proof (derivable_pt_lim_power t (1-σ) Ht) as Hpow.
      replace ((1-σ)-1) with (-σ) in Hpow by lra.
      apply is_derive_Reals in Hpow.
      replace (fun x => - Rpower x (1-σ) / (σ-1))
         with (fun x => (- / (σ-1)) * Rpower x (1-σ)).
      - apply is_derive_scal with (k := - / (σ-1)) in Hpow.
        simpl in Hpow.
        replace (- / (σ-1) * ((1-σ) * Rpower t (-σ))) with (Rpower t (-σ)) in Hpow by (field; lra).
        exact Hpow.
      - extensionality x; unfold Rdiv; field; lra.
    }

    assert (Hlim_power : forall eps1 : R, eps1 > 0 -> exists M0 : R, M0 > 0 /\ forall t : R, t > M0 -> Rpower t (1-σ) < eps1).
    { intros eps1 Heps1.
      set (M0 := exp (ln eps1 / (1-σ))).
      exists M0.
      split.
      - apply exp_pos.
      - intros t Ht.
        unfold Rpower.
        rewrite <- (exp_ln eps1 Heps1).
        apply exp_increasing.
        assert (HM0_pos : 0 < M0) by (apply exp_pos).
        assert (Ht_pos : 0 < t) by (apply Rlt_trans with M0; [exact HM0_pos | exact Ht]).
        assert (Hln_gt : ln t > ln M0).
        { apply Rlt_gt, ln_increasing; [exact HM0_pos | apply Rgt_lt; exact Ht]. }
        unfold M0 in Hln_gt.
        rewrite ln_exp in Hln_gt.
        apply Ropp_lt_cancel.
        rewrite Ropp_mult_distr_l.
        replace (- ln eps1) with (- (1-σ) * (ln eps1/(1-σ))) by (field; lra).
        apply Rmult_lt_compat_l with (r := - (1-σ)).
        - apply Ropp_0_gt_lt_contravar; lra.
        - exact Hln_gt.
    }

    destruct (Hlim_power (eps * (σ-1))) as [M0 [HM0_pos HM0]].
    { apply Rmult_lt_0_compat; [exact Heps | exact σ_minus_1_pos]. }
    set (N := Nat.max (Z.to_nat (up M0)) 1%nat).
    assert (HN_ge_1 : (1 <= N)%nat) by lia.
    assert (H_N_gt_M0 : INR N > M0).
    { unfold N.
      assert (H_up : IZR (up M0) > M0) by (destruct (archimed M0) as [H _]; exact H).
      assert (H_up_gt_0 : (0 < up M0)%Z).
      { apply lt_IZR.
        apply Rlt_trans with M0; [exact HM0_pos | exact H_up].
      }
      assert (H_up_ge_0 : (0 <= up M0)%Z) by lia.
      assert (H_aux : INR (Z.to_nat (up M0)) = IZR (up M0)).
      { rewrite (INR_IZR_INZ (Z.to_nat (up M0))).
        rewrite Z2Nat.id by exact H_up_ge_0.
        reflexivity. }
      assert (H_ge : (N >= Z.to_nat (up M0))%nat) by (apply Nat.le_max_l).
      apply Rlt_le_trans with (INR (Z.to_nat (up M0))).
      - rewrite H_aux. exact H_up.
      - apply le_INR; exact H_ge.
    }

    exists N.
    intros m n Hm Hn.
    set (p := Nat.min m n).
    set (q := Nat.max m n).

    assert (Hp_ge_N : (p >= N)%nat).
    { unfold p.
      destruct (le_lt_dec m n) as [Hle | Hlt].
      - rewrite Nat.min_l; [exact Hm | exact Hle].
      - rewrite Nat.min_r; [exact Hn | apply Nat.lt_le_incl, Hlt]. }
    assert (Hq_ge_N : (q >= N)%nat).
    { unfold q.
      apply Nat.le_trans with m; [exact Hm | apply Nat.le_max_l]. }

    assert (Hp_pos : (0 < p)%nat) by lia.
    assert (Hq_pos : (0 < q)%nat) by lia.
    assert (Hle_pq : (p <= q)%nat).
    { unfold p, q.
      destruct (le_lt_dec m n) as [Hle | Hlt].
      - rewrite Nat.min_l, Nat.max_r; lia.
      - rewrite Nat.min_r, Nat.max_l; lia. }

    pose proof (tail_difference_bound σ σ_gt_1 p q Hp_pos Hle_pq) as Hbound.

    assert (Heq_abs : Rabs (sum_f_R0 a m - sum_f_R0 a n) = sum_f_R0 a q - sum_f_R0 a p).
    {
      destruct (le_lt_dec m n) as [Hle | Hlt].
      - 
        assert (Hp_eq : p = m) by (apply Nat.min_l; exact Hle).
        assert (Hq_eq : q = n) by (apply Nat.max_r; exact Hle).
        rewrite Hp_eq, Hq_eq.
        rewrite Rabs_minus_sym.
        apply Rabs_pos_eq.
        assert (Hmono : sum_f_R0 a m <= sum_f_R0 a n).
        { apply sum_f_R0_incr; [intros k; apply Rle_self_plus, Ha_pos | exact Hle]. }
        apply Rle_minus in Hmono.
        apply Ropp_le_contravar in Hmono.
        rewrite Ropp_minus_distr in Hmono.
        rewrite Ropp_0 in Hmono.
        exact Hmono.
      - 
        assert (Hp_eq : p = n) by (apply Nat.min_r; apply Nat.lt_le_incl, Hlt).
        assert (Hq_eq : q = m) by (apply Nat.max_l; apply Nat.lt_le_incl, Hlt).
        rewrite Hp_eq, Hq_eq.
        apply Rabs_pos_eq.
        assert (Hmono : sum_f_R0 a n <= sum_f_R0 a m).
        { apply sum_f_R0_incr; [intros k; apply Rle_self_plus, Ha_pos | lia]. }
        apply Rle_minus in Hmono.
        apply Ropp_le_contravar in Hmono.
        rewrite Ropp_minus_distr in Hmono.
        rewrite Ropp_0 in Hmono.
        exact Hmono.
    }

    rewrite Heq_abs.
    apply Rle_lt_trans with (Rpower (INR p) (1-σ) / (σ-1)).
    - exact Hbound.
    - assert (Hp_gt_M0 : INR p > M0).
      { apply Rlt_le_trans with (INR N); [exact H_N_gt_M0 | apply le_INR, Hp_ge_N]. }
      specialize (HM0 (INR p) Hp_gt_M0).
      assert (Hinv_pos : 0 < / (σ-1)) by (apply Rinv_0_lt_compat, σ_minus_1_pos).
      apply (Rmult_lt_compat_r (/ (σ-1)) (Rpower (INR p) (1-σ)) (eps * (σ-1)) Hinv_pos) in HM0.
      rewrite Rmult_assoc in HM0.
      rewrite Rinv_r in HM0; [| lra].
      simpl in HM0.
      rewrite Rmult_1_r in HM0.
      exact HM0.
    }

  intros eps Heps.
  destruct (H_cauchy_a eps Heps) as [N0 HN0].
  set (N := S N0).
  exists N.
  intros m n Hm Hn.
  assert (Hm1 : (m >= 1)%nat) by lia.
  assert (Hn1 : (n >= 1)%nat) by lia.
  replace m with (S (pred m)) by lia.
  replace n with (S (pred n)) by lia.
  rewrite !re_Csum_zeta.
  set (p := pred m). set (q := pred n).
  assert (Hp_ge_N0 : (p >= N0)%nat) by lia.
  assert (Hq_ge_N0 : (q >= N0)%nat) by lia.

  assert (Habs_le : Rabs (sum_f_R0 (re_term s) p - sum_f_R0 (re_term s) q) <=
                    Rabs (sum_f_R0 a p - sum_f_R0 a q)).
  {
    destruct (le_lt_dec p q) as [Hle | Hlt].
    - 
      destruct (Nat.eq_dec p q) as [Heq | Hneq].
      + 
        rewrite Heq; rewrite Rminus_diag, Rabs_R0.
        apply Rabs_pos.
      + 
        rewrite Rabs_minus_sym.
        rewrite (sum_f_R0_plus (re_term s) p q Hle).
        rewrite Rabs_minus_sym.
        rewrite (sum_f_R0_plus a p q Hle).
        assert (Hlt_true : (p <? q) = true) by (apply Nat.ltb_lt; lia).
        rewrite !Hlt_true.
        assert (Hsum_nonneg : 0 <= sum_f_R0 (fun i => a (S p + i)%nat) (q - S p)).
        { induction (q - S p)%nat as [|k IH]; simpl.
          - apply Ha_pos.
          - apply Rplus_le_le_0_compat; [exact IH | apply Ha_pos]. }
        rewrite (Rabs_pos_eq _ Hsum_nonneg).
        apply Rle_trans with (sum_f_R0 (fun i => Rabs (re_term s (S p + i))) (q - S p)).
        { apply Rabs_sum_f_R0. }
        apply sum_f_R0_le.
        intros k; apply re_term_bound; exact Hre.
    - 
      assert (Hqp : (q <= p)%nat) by lia.
      rewrite (sum_f_R0_plus (re_term s) q p Hqp).
      rewrite (sum_f_R0_plus a q p Hqp).
      assert (Hlt_true : (q <? p) = true) by (apply Nat.ltb_lt; lia).
      rewrite !Hlt_true.
      assert (Hsum_nonneg : 0 <= sum_f_R0 (fun i => a (S q + i)%nat) (p - S q)).
      { induction (p - S q)%nat as [|k IH]; simpl.
        - apply Ha_pos.
        - apply Rplus_le_le_0_compat; [exact IH | apply Ha_pos]. }
      rewrite (Rabs_pos_eq _ Hsum_nonneg).
      apply Rle_trans with (sum_f_R0 (fun i => Rabs (re_term s (S q + i))) (p - S q)).
      { apply Rabs_sum_f_R0. }
      apply sum_f_R0_le.
      intros k; apply re_term_bound; exact Hre.
  }
  apply Rle_lt_trans with (Rabs (sum_f_R0 a p - sum_f_R0 a q)).
  - exact Habs_le.
  - apply HN0; assumption.
Qed.

(* 虚部部分和的柯西列 *)
Lemma im_partial_sum_cauchy (s : Complex) (Hre : 1 < ℜ(s)) :
  cauchy_seq (fun N : nat => im (Csum (zeta_series_term s) N)).
Proof.
  set (σ := ℜ(s)).
  set (a := fun n : nat => Rpower (INR (S n)) (-σ)).
  assert (Ha_pos : forall n : nat, 0 <= a n).
  { intro n; apply Rlt_le; apply Rpower_pos; apply lt_0_INR; lia. }

  assert (H_cauchy_a : forall eps : R, eps > 0 -> exists N : nat, forall m n : nat, (m >= N)%nat -> (n >= N)%nat -> Rabs (sum_f_R0 a m - sum_f_R0 a n) < eps).
  { intros eps Heps.
    assert (σ_gt_1 : 1 < σ) by exact Hre.
    assert (σ_minus_1_pos : 0 < σ - 1) by lra.
    set (f := fun x : R => Rpower x (-σ)).
    set (F := fun x => - Rpower x (1-σ) / (σ-1)).

    assert (Hder_F : forall t, 0 < t -> is_derive F t (f t)).
    { intros t Ht.
      unfold F, f.
      pose proof (derivable_pt_lim_power t (1-σ) Ht) as Hpow.
      replace ((1-σ)-1) with (-σ) in Hpow by lra.
      apply is_derive_Reals in Hpow.
      replace (fun x => - Rpower x (1-σ) / (σ-1))
         with (fun x => (- / (σ-1)) * Rpower x (1-σ)).
      - apply is_derive_scal with (k := - / (σ-1)) in Hpow.
        simpl in Hpow.
        replace (- / (σ-1) * ((1-σ) * Rpower t (-σ))) with (Rpower t (-σ)) in Hpow by (field; lra).
        exact Hpow.
      - extensionality x; unfold Rdiv; field; lra.
    }

    assert (Hlim_power : forall eps1 : R, eps1 > 0 -> exists M0 : R, M0 > 0 /\ forall t : R, t > M0 -> Rpower t (1-σ) < eps1).
    { intros eps1 Heps1.
      set (M0 := exp (ln eps1 / (1-σ))).
      exists M0.
      split.
      - apply exp_pos.
      - intros t Ht.
        unfold Rpower.
        rewrite <- (exp_ln eps1 Heps1).
        apply exp_increasing.
        assert (HM0_pos : 0 < M0) by (apply exp_pos).
        assert (Ht_pos : 0 < t) by (apply Rlt_trans with M0; [exact HM0_pos | exact Ht]).
        assert (Hln_gt : ln t > ln M0).
        { apply Rlt_gt, ln_increasing; [exact HM0_pos | apply Rgt_lt; exact Ht]. }
        unfold M0 in Hln_gt.
        rewrite ln_exp in Hln_gt.
        apply Ropp_lt_cancel.
        rewrite Ropp_mult_distr_l.
        replace (- ln eps1) with (- (1-σ) * (ln eps1/(1-σ))) by (field; lra).
        apply Rmult_lt_compat_l with (r := - (1-σ)).
        - apply Ropp_0_gt_lt_contravar; lra.
        - exact Hln_gt.
    }

    destruct (Hlim_power (eps * (σ-1))) as [M0 [HM0_pos HM0]].
    { apply Rmult_lt_0_compat; [exact Heps | exact σ_minus_1_pos]. }
    set (N := Nat.max (Z.to_nat (up M0)) 1%nat).
    assert (HN_ge_1 : (1 <= N)%nat) by lia.
    assert (H_N_gt_M0 : INR N > M0).
    { unfold N.
      assert (H_up : IZR (up M0) > M0) by (destruct (archimed M0) as [H _]; exact H).
      assert (H_up_gt_0 : (0 < up M0)%Z).
      { apply lt_IZR.
        apply Rlt_trans with M0; [exact HM0_pos | exact H_up].
      }
      assert (H_up_ge_0 : (0 <= up M0)%Z) by lia.
      assert (H_aux : INR (Z.to_nat (up M0)) = IZR (up M0)).
      { rewrite (INR_IZR_INZ (Z.to_nat (up M0))).
        rewrite Z2Nat.id by exact H_up_ge_0.
        reflexivity. }
      assert (H_ge : (N >= Z.to_nat (up M0))%nat) by (apply Nat.le_max_l).
      apply Rlt_le_trans with (INR (Z.to_nat (up M0))).
      - rewrite H_aux. exact H_up.
      - apply le_INR; exact H_ge.
    }

    exists N.
    intros m n Hm Hn.
    set (p := Nat.min m n).
    set (q := Nat.max m n).

    assert (Hp_ge_N : (p >= N)%nat).
    { unfold p.
      destruct (le_lt_dec m n) as [Hle | Hlt].
      - rewrite Nat.min_l; [exact Hm | exact Hle].
      - rewrite Nat.min_r; [exact Hn | apply Nat.lt_le_incl, Hlt]. }
    assert (Hq_ge_N : (q >= N)%nat).
    { unfold q.
      apply Nat.le_trans with m; [exact Hm | apply Nat.le_max_l]. }

    assert (Hp_pos : (0 < p)%nat) by lia.
    assert (Hq_pos : (0 < q)%nat) by lia.
    assert (Hle_pq : (p <= q)%nat).
    { unfold p, q.
      destruct (le_lt_dec m n) as [Hle | Hlt].
      - rewrite Nat.min_l, Nat.max_r; lia.
      - rewrite Nat.min_r, Nat.max_l; lia. }

    pose proof (tail_difference_bound σ σ_gt_1 p q Hp_pos Hle_pq) as Hbound.

    assert (Heq_abs : Rabs (sum_f_R0 a m - sum_f_R0 a n) = sum_f_R0 a q - sum_f_R0 a p).
    {
      destruct (le_lt_dec m n) as [Hle | Hlt].
      - 
        assert (Hp_eq : p = m) by (apply Nat.min_l; exact Hle).
        assert (Hq_eq : q = n) by (apply Nat.max_r; exact Hle).
        rewrite Hp_eq, Hq_eq.
        rewrite Rabs_minus_sym.
        apply Rabs_pos_eq.
        assert (Hmono : sum_f_R0 a m <= sum_f_R0 a n).
        { apply sum_f_R0_incr; [intros k; apply Rle_self_plus, Ha_pos | exact Hle]. }
        apply Rle_minus in Hmono.
        apply Ropp_le_contravar in Hmono.
        rewrite Ropp_minus_distr in Hmono.
        rewrite Ropp_0 in Hmono.
        exact Hmono.
      - 
        assert (Hp_eq : p = n) by (apply Nat.min_r; apply Nat.lt_le_incl, Hlt).
        assert (Hq_eq : q = m) by (apply Nat.max_l; apply Nat.lt_le_incl, Hlt).
        rewrite Hp_eq, Hq_eq.
        apply Rabs_pos_eq.
        assert (Hmono : sum_f_R0 a n <= sum_f_R0 a m).
        { apply sum_f_R0_incr; [intros k; apply Rle_self_plus, Ha_pos | lia]. }
        apply Rle_minus in Hmono.
        apply Ropp_le_contravar in Hmono.
        rewrite Ropp_minus_distr in Hmono.
        rewrite Ropp_0 in Hmono.
        exact Hmono.
    }

    rewrite Heq_abs.
    apply Rle_lt_trans with (Rpower (INR p) (1-σ) / (σ-1)).
    - exact Hbound.
    - assert (Hp_gt_M0 : INR p > M0).
      { apply Rlt_le_trans with (INR N); [exact H_N_gt_M0 | apply le_INR, Hp_ge_N]. }
      specialize (HM0 (INR p) Hp_gt_M0).
      assert (Hinv_pos : 0 < / (σ-1)) by (apply Rinv_0_lt_compat, σ_minus_1_pos).
      apply (Rmult_lt_compat_r (/ (σ-1)) (Rpower (INR p) (1-σ)) (eps * (σ-1)) Hinv_pos) in HM0.
      rewrite Rmult_assoc in HM0.
      rewrite Rinv_r in HM0; [| lra].
      simpl in HM0.
      rewrite Rmult_1_r in HM0.
      exact HM0.
    }

  intros eps Heps.
  destruct (H_cauchy_a eps Heps) as [N0 HN0].
  set (N := S N0).
  exists N.
  intros m n Hm Hn.
  assert (Hm1 : (m >= 1)%nat) by lia.
  assert (Hn1 : (n >= 1)%nat) by lia.
  replace m with (S (pred m)) by lia.
  replace n with (S (pred n)) by lia.
  rewrite !im_Csum_zeta.
  set (p := pred m). set (q := pred n).
  assert (Hp_ge_N0 : (p >= N0)%nat) by lia.
  assert (Hq_ge_N0 : (q >= N0)%nat) by lia.

  assert (Habs_le : Rabs (sum_f_R0 (im_term s) p - sum_f_R0 (im_term s) q) <=
                    Rabs (sum_f_R0 a p - sum_f_R0 a q)).
  {
    destruct (le_lt_dec p q) as [Hle | Hlt].
    - 
      destruct (Nat.eq_dec p q) as [Heq | Hneq].
      + 
        rewrite Heq; rewrite Rminus_diag, Rabs_R0.
        apply Rabs_pos.
      + 
        rewrite Rabs_minus_sym.
        rewrite (sum_f_R0_plus (im_term s) p q Hle).
        rewrite Rabs_minus_sym.
        rewrite (sum_f_R0_plus a p q Hle).
        assert (Hlt_true : (p <? q) = true) by (apply Nat.ltb_lt; lia).
        rewrite !Hlt_true.
        assert (Hsum_nonneg : 0 <= sum_f_R0 (fun i => a (S p + i)%nat) (q - S p)).
        { induction (q - S p)%nat as [|k IH]; simpl.
          - apply Ha_pos.
          - apply Rplus_le_le_0_compat; [exact IH | apply Ha_pos]. }
        rewrite (Rabs_pos_eq _ Hsum_nonneg).
        apply Rle_trans with (sum_f_R0 (fun i => Rabs (im_term s (S p + i))) (q - S p)).
        { apply Rabs_sum_f_R0. }
        apply sum_f_R0_le.
        intros k; apply im_term_bound; exact Hre.
    - 
      assert (Hqp : (q <= p)%nat) by lia.
      rewrite (sum_f_R0_plus (im_term s) q p Hqp).
      rewrite (sum_f_R0_plus a q p Hqp).
      assert (Hlt_true : (q <? p) = true) by (apply Nat.ltb_lt; lia).
      rewrite !Hlt_true.
      assert (Hsum_nonneg : 0 <= sum_f_R0 (fun i => a (S q + i)%nat) (p - S q)).
      { induction (p - S q)%nat as [|k IH]; simpl.
        - apply Ha_pos.
        - apply Rplus_le_le_0_compat; [exact IH | apply Ha_pos]. }
      rewrite (Rabs_pos_eq _ Hsum_nonneg).
      apply Rle_trans with (sum_f_R0 (fun i => Rabs (im_term s (S q + i))) (p - S q)).
      { apply Rabs_sum_f_R0. }
      apply sum_f_R0_le.
      intros k; apply im_term_bound; exact Hre.
  }
  apply Rle_lt_trans with (Rabs (sum_f_R0 a p - sum_f_R0 a q)).
  - exact Habs_le.
  - apply HN0; assumption.
Qed.

(* 定理：黎曼ζ函数级数收敛 *)
Theorem zeta_series_converges (s : Complex) (Hre : 1 < ℜ(s)) :
  exists L : Complex, Cseq_limit (fun N : nat => Csum (zeta_series_term s) N) L.
Proof.
  assert (Hre_cauchy : cauchy_seq (fun N : nat => re (Csum (zeta_series_term s) N)))
    by (apply re_partial_sum_cauchy; exact Hre).
  assert (Him_cauchy : cauchy_seq (fun N : nat => im (Csum (zeta_series_term s) N)))
    by (apply im_partial_sum_cauchy; exact Hre).
  assert (Hre_cv : exists l_re : R, Un_cv (fun N : nat => re (Csum (zeta_series_term s) N)) l_re)
    by (apply cauchy_seq_converges; exact Hre_cauchy).
  assert (Him_cv : exists l_im : R, Un_cv (fun N : nat => im (Csum (zeta_series_term s) N)) l_im)
    by (apply cauchy_seq_converges; exact Him_cauchy).
  destruct Hre_cv as [l_re Hre_lim], Him_cv as [l_im Him_lim].
  exists (l_re +i l_im).
  apply Cseq_limit_from_components; [exact Hre_lim | exact Him_lim].
Qed.

Require Import Coquelicot.Coquelicot.    (* Coquelicot积分库核心 *)

(* 主定理：Re(s) > 1 时级数收敛 *)
Theorem zeta_series_converges_0_1 (s : Complex) (Hre : re s > 1) :
  exists l : Complex, Cseries_sum (zeta_series_term s) l.
Proof.
  unfold zeta_series_term, Cseries_sum.
  set (σ := re s) in *.
  set (τ := im s) in *.
  assert (Hσ : σ > 1) by auto.
  set (a := σ - 1) in *.
  assert (Ha : a > 0) by (unfold a; lra).

  set (u n := Rpower (INR (S n)) σ).
  assert (Hpos : forall n, u n > 0).
  { intros n. unfold u. apply Rpower_pos.
    apply lt_0_INR, Nat.lt_0_succ. }

  set (re_pos_term := fun n : nat => / u n).

  assert (H_re_pos_lim : exists l_re_pos : R,
            Un_cv (fun N => sum_f_R0 re_pos_term N) l_re_pos).
  {
    set (f := fun t : R => Rpower t (-σ)).
    assert (Hf_pos : forall t, 0 < t -> 0 < f t).
    { intros t Ht. unfold f. apply Rpower_pos; lra. }
    assert (Hf_decr : forall x y, 1 <= x <= y -> f x >= f y).
    { intros x y [Hx Hxy].
      unfold f, Rpower.
      apply Rle_ge.
      apply exp_le.
      assert (Hneg : -σ < 0) by lra.
      assert (Hln_le : ln x <= ln y) by (apply ln_le; lra).
      apply Rmult_le_compat_neg_l; [apply Rlt_le, Hneg | exact Hln_le]. }

    assert (Hf_int : exists I : R,
                is_RInt_gen f (at_point 1) (Rbar_locally p_infty) I).
    {
      set (F := fun t : R => Rpower t (1 - σ) / (1 - σ)).
      assert (Hder : forall t, 1 < t -> is_derive F t (f t)).
      { intros t Ht.
        apply is_derive_Reals.
        assert (Ht_pos : 0 < t) by lra.
        pose proof (derivable_pt_lim_power t (1 - σ) Ht_pos) as Hpow.
        replace (1 - σ - 1) with (-σ) in Hpow by ring.
        apply derivable_pt_lim_scal with (a := / (1 - σ)) in Hpow.
        assert (Hrew : / (1 - σ) * ((1 - σ) * Rpower t (-σ)) = Rpower t (-σ)).
        { field; lra. }
        rewrite Hrew in Hpow.
        apply (derivable_pt_lim_ext
                 (fun x => / (1 - σ) * Rpower x (1 - σ))
                 (fun x => Rpower x (1 - σ) / (1 - σ))
                 t (Rpower t (-σ))).
        - intros x; unfold Rdiv; rewrite Rmult_comm; reflexivity.
        - exact Hpow. }

      assert (Hlim : filterlim F (Rbar_locally p_infty) (locally 0)).
      {
        assert (Hln_p : filterlim ln (Rbar_locally p_infty) (Rbar_locally p_infty)).
        { apply is_lim_ln_p. }
        assert (Hmult_temp : filterlim (fun t => (1 - σ) * ln t) (Rbar_locally p_infty) (Rbar_locally (Rbar_mult (1 - σ) p_infty))).
        { apply filterlim_comp with (f := ln) (g := fun x => (1 - σ) * x) (G := Rbar_locally p_infty).
          - exact Hln_p.
          - apply filterlim_Rbar_mult_l with (a := 1 - σ) (l := p_infty). }
        assert (Hmult_eq : Rbar_mult (1 - σ) p_infty = m_infty).
        { assert (Hneg : (1 - σ) < 0) by lra.
          pose proof (is_Rbar_mult_p_infty_neg (1 - σ) Hneg) as His.
          apply is_Rbar_mult_unique in His.
          rewrite Rbar_mult_comm; exact His. }
        assert (Hmult : filterlim (fun t => (1 - σ) * ln t) (Rbar_locally p_infty) (Rbar_locally m_infty)).
        { rewrite <- Hmult_eq; exact Hmult_temp. }
        assert (Hexp_comp : filterlim (fun t => exp ((1 - σ) * ln t)) (Rbar_locally p_infty) (locally 0)).
        { apply filterlim_comp with (f := fun t => (1 - σ) * ln t) (g := exp) (G := Rbar_locally m_infty).
          - exact Hmult.
          - apply filterlim_exp_m_infty. }
        assert (H_scal_lim : filterlim (fun y => / (1 - σ) * y) (locally 0) (locally 0)).
        { apply (eq_ind_r (fun l => filterlim (fun y => / (1 - σ) * y) (locally 0) (locally l))
                    (filterlim_scal_r (/(1-σ)) 0)).
          rewrite Rmult_0_r; reflexivity. }
        assert (Hlim_tmp : filterlim (fun t => / (1 - σ) * exp ((1 - σ) * ln t))
                                      (Rbar_locally p_infty) (locally 0)).
        { apply filterlim_comp with (f := fun t => exp ((1 - σ) * ln t))
                                     (g := fun y => / (1 - σ) * y)
                                     (F := Rbar_locally p_infty)
                                     (G := locally 0)
                                     (H := locally 0).
          - exact Hexp_comp.
          - exact H_scal_lim. }
        assert (H_eq : forall t, t > 0 -> F t = / (1 - σ) * exp ((1 - σ) * ln t)).
        { intros t Ht.
          unfold F, Rdiv.
          replace (Rpower t (1 - σ)) with (exp ((1 - σ) * ln t)).
          - rewrite Rmult_comm; reflexivity.
          - unfold Rpower; reflexivity. }
        assert (H_pos : Rbar_locally p_infty (fun t => t > 0)).
        { exists 0; intros t Ht; lra. }
        assert (H_eq_loc : Rbar_locally p_infty (fun t => / (1 - σ) * exp ((1 - σ) * ln t) = F t)).
        { apply filter_imp with (P := fun t => t > 0).
          - intros t Ht. symmetry. apply H_eq, Ht.
          - exact H_pos. }
        apply filterlim_ext_loc with (f := fun t => / (1 - σ) * exp ((1 - σ) * ln t)) (g := F).
        - exact H_eq_loc.
        - exact Hlim_tmp.
      }

      exists (- F 1).
      unfold is_RInt_gen.
      intros P0 HP0.
      apply locally_iff_open_ball in HP0.
      destruct HP0 as [eps [Heps_pos Hball]].
      pose (eps2 := mkposreal (eps/2) (Rdiv_lt_0_compat eps 2 Heps_pos Rlt_0_2)).
      destruct (Hlim (ball 0 eps2)) as [M HM]; [apply locally_ball |].
      set (M1 := Rmax M 1).
      assert (HM1 : forall x, M1 < x -> ball 0 eps2 (F x)).
      { intros x Hx. apply HM. eapply Rle_lt_trans; [apply Rmax_l | exact Hx]. }
      apply Filter_prod with
        (Q := fun t => t = 1)
        (R := fun v => v > M1).
      - apply at_point_singleton.
      - unfold Rbar_locally; exists M1; intros v Hv; exact Hv.
      - intros t v Ht Hv.
        subst t.
        assert (Hv_gt_M1 : v > M1) by exact Hv.
        assert (Hv_gt_0 : 0 < v).
        { apply Rlt_trans with M1.
          - apply Rlt_le_trans with 1; [apply Rlt_0_1 | apply Rmax_r].
          - exact Hv_gt_M1. }
        assert (Hex : ex_RInt f 1 v).
        { apply ex_RInt_continuous with (f := f) (a := 1) (b := v).
          intros z Hz.
          assert (H1_le_v : 1 <= v).
          { apply Rle_trans with M1.
            - apply Rmax_r.
            - apply Rlt_le. exact Hv_gt_M1. }
          assert (Hmin : Rmin 1 v = 1) by (apply Rmin_left; exact H1_le_v).
          assert (Hmax : Rmax 1 v = v) by (apply Rmax_right; exact H1_le_v).
          rewrite Hmin, Hmax in Hz.
          destruct Hz as [Hz1 Hz2].
          assert (Hz_pos : 0 < z) by (apply Rlt_le_trans with 1; [apply Rlt_0_1 | exact Hz1]).
          apply continuity_pt_to_continuous.
          apply continuity_pt_comp with (f1 := fun t => (-σ) * ln t) (f2 := exp).
          - apply continuity_pt_scal.
            apply derivable_continuous_pt.
            apply derivable_pt_ln_manual.
            exact Hz_pos.
          - apply derivable_continuous_pt.
            apply derivable_pt_exp_manual. }
        assert (Hder1 : is_derive F 1 (f 1)).
        {
          unfold F, f.
          assert (Ht_pos : 0 < 1) by lra.
          pose proof (derivable_pt_lim_power 1 (1 - σ) Ht_pos) as Hpow.
          replace ((1 - σ) - 1) with (-σ) in Hpow by ring.
          apply derivable_pt_lim_scal with (a := / (1 - σ)) in Hpow.
          assert (Hrew : / (1 - σ) * ((1 - σ) * Rpower 1 (-σ)) = Rpower 1 (-σ)).
          { field; lra. }
          rewrite Hrew in Hpow.
          assert (Hder_pt_lim_target : derivable_pt_lim
                                          (fun t => Rpower t (1 - σ) / (1 - σ))
                                          1 (Rpower 1 (-σ))).
          {
            apply (derivable_pt_lim_ext
                     (fun t => / (1 - σ) * Rpower t (1 - σ))
                     (fun t => Rpower t (1 - σ) / (1 - σ))
                     1 (Rpower 1 (-σ))).
            - intros t; unfold Rdiv; rewrite Rmult_comm; reflexivity.
            - exact Hpow.
          }
          apply is_derive_Reals.
          exact Hder_pt_lim_target.
        }
        assert (Hder_interval : forall x, 1 <= x <= v -> is_derive F x (f x)).
        {
          intros x [Hx_low Hx_high].
          destruct (Req_dec x 1) as [Hx_eq_1 | Hx_gt_1].
          - subst x; exact Hder1.
          - assert (Hx_gt_1' : 1 < x) by lra.
            apply Hder; exact Hx_gt_1'.
        }
        assert (HInt_eq : RInt f 1 v = F v - F 1).
        {
          apply is_RInt_unique with (f := f) (a := 1) (b := v) (l := F v - F 1).
          apply is_RInt_derive with (f := F) (df := f) (a := 1) (b := v).
          - intros x Hx.
            assert (Hv_gt_1 : v > 1) by (apply Rle_lt_trans with M1; [apply Rmax_r | assumption]).
            rewrite Rmin_left, Rmax_right in Hx; [| apply Rlt_le; assumption | apply Rlt_le; assumption].
            apply Hder_interval.
            exact Hx.
          - intros x Hx.
            apply continuity_pt_to_continuous.
            assert (Hx_pos : 0 < x).
            {
              assert (Hv_gt_1 : v > 1) by (apply Rle_lt_trans with M1; [apply Rmax_r | assumption]).
              apply Rlt_le_trans with (Rmin 1 v).
              - apply Rmin_glb_lt; [apply Rlt_0_1 | assumption].
              - destruct Hx as [Hlow _]; exact Hlow.
            }
            unfold f.
            apply continuity_pt_comp with (f1 := fun t => (-σ) * ln t) (f2 := exp).
            + apply continuity_pt_scal.
              apply derivable_continuous_pt.
              apply derivable_pt_ln_manual.
              exact Hx_pos.
            + apply derivable_continuous_pt.
              apply derivable_pt_exp_manual.
        }
        assert (Habs_Fv : Rabs (F v) < eps/2).
        { specialize (HM1 v Hv_gt_M1).
          unfold AbsRing_ball in HM1.
          change (Rabs (F v) < eps / 2).
          replace (Rabs (F v)) with (Rabs (F v - 0)).
          - exact HM1.
          - rewrite Rminus_0_r; reflexivity. }
        assert (Habs_RInt : Rabs (RInt f 1 v - (- F 1)) < eps).
        {
          rewrite HInt_eq.
          replace (F v - F 1 - (- F 1)) with (F v) by ring.
          apply Rlt_trans with (eps/2); [exact Habs_Fv | lra].
        }
        exists (RInt f 1 v).
        split.
        + apply (RInt_correct (V := R_CompleteNormedModule) f 1 v Hex).
        + apply Hball; exact Habs_RInt.
    }

    destruct Hf_int as [I_f Hf_int].

    set (part_sum := fun N => sum_f_R0 re_pos_term N).
    assert (part_sum_incr : forall N, part_sum N <= part_sum (S N)).
    { intros N.
      unfold part_sum; rewrite sum_f_R0_S.
      assert (Hre_pos : 0 <= re_pos_term (S N)).
      { unfold re_pos_term; apply Rlt_le, Rinv_0_lt_compat, Hpos. }
      apply Rplus_le_compat_l with (r := sum_f_R0 re_pos_term N) in Hre_pos.
      rewrite Rplus_0_r in Hre_pos.
      exact Hre_pos.
    }

    assert (Hcont_f_pos : forall t, 0 < t -> continuous f t).
    {
      intros t Ht.
      apply continuity_pt_to_continuous.
      unfold f.
      apply continuity_pt_comp with (f1 := fun t => (-σ) * ln t) (f2 := exp).
      - apply continuity_pt_scal.
        apply derivable_continuous_pt, derivable_pt_ln_manual; exact Ht.
      - apply derivable_continuous_pt, derivable_pt_exp_manual.
    }

    assert (Hineq : forall n m : nat, (1 <= n <= m)%nat ->
              part_sum m - part_sum n <= RInt f (INR n) (INR m)).
    {
      intros n m Hnm.
      revert n Hnm.
      induction m as [m IH] using lt_wf_ind.
      intros n Hnm.
      destruct (le_lt_dec n m) as [Hle | Hlt].
      - destruct (eq_nat_dec n m) as [Heq | Hneq].
        + rewrite Heq.
          replace (part_sum m - part_sum m) with 0 by ring.
          apply Rle_trans with 0; [apply Rle_refl | apply RInt_ge_0; [apply Rle_refl | apply ex_RInt_point | intros; exfalso; lra]].
        + assert (Hlt' : (n < m)%nat) by lia.
          set (m' := (m - 1)%nat).
          assert (Hm_eq : m = S m') by lia.
          assert (Hnm' : (1 <= n <= m')%nat).
          { split. exact (proj1 Hnm). lia. }
          assert (Hm'_lt_m : (m' < m)%nat) by lia.
          specialize (IH m' Hm'_lt_m n Hnm') as IH_nm'.

          assert (Hex_nm' : ex_RInt f (INR n) (INR m')).
          {
            apply ex_RInt_continuous with (f := f) (a := INR n) (b := INR m').
            intros z Hz.
            destruct Hz as [Hz_low Hz_high].
            assert (Hn_le_m' : (n <= m')%nat) by lia.
            rewrite (Rmin_left (INR n) (INR m')) in Hz_low by (apply le_INR; exact Hn_le_m').
            rewrite (Rmax_right (INR n) (INR m')) in Hz_high by (apply le_INR; exact Hn_le_m').
            assert (Hz_pos : 0 < z).
            {
              apply Rlt_le_trans with (INR n).
              - apply lt_0_INR; lia.
              - exact Hz_low.
            }
            apply Hcont_f_pos; exact Hz_pos.
          }

          assert (Hex_m'm : ex_RInt f (INR m') (INR m)).
          {
            apply ex_RInt_continuous with (f := f) (a := INR m') (b := INR m).
            intros z Hz.
            destruct Hz as [Hz_low Hz_high].
            assert (Hm'_le_m : (m' <= m)%nat) by lia.
            rewrite (Rmin_left (INR m') (INR m)) in Hz_low by (apply le_INR; exact Hm'_le_m).
            rewrite (Rmax_right (INR m') (INR m)) in Hz_high by (apply le_INR; exact Hm'_le_m).
            assert (Hz_pos : 0 < z).
            {
              apply Rlt_le_trans with (INR m').
              - apply lt_0_INR; lia.
              - exact Hz_low.
            }
            apply Hcont_f_pos; exact Hz_pos.
          }

          assert (H_Chasles : RInt f (INR n) (INR m) = RInt f (INR n) (INR m') + RInt f (INR m') (INR m)).
          {
            symmetry.
            apply RInt_Chasles with (f := f) (a := INR n) (b := INR m') (c := INR m);
              [exact Hex_nm' | exact Hex_m'm].
          }

          assert (Hf_min : forall x y, 1 <= x <= y -> RInt f x y >= f y * (y - x)).
          {
            intros x y Hxy.
            destruct (Req_dec x y) as [Heq | Hne].
            - subst y.
              rewrite Rminus_eq_0, Rmult_0_r.
              apply Rle_ge.
              apply RInt_ge_0; [apply Rle_refl | apply ex_RInt_point | intros t Ht; exfalso; lra].
            - assert (Hlt : x < y) by lra.
              set (g := fun _ : R => f y).
              assert (Hg_le_f : forall t, x <= t <= y -> g t <= f t).
              {
                intros t Ht. unfold g.
                assert (Ht_le_y : t <= y) by apply Ht.
                assert (H1_le_t : 1 <= t) by (apply Rle_trans with x; [apply Hxy | apply Ht]).
                assert (Hge : f t >= f y) by (apply Hf_decr; split; [exact H1_le_t | exact Ht_le_y]).
                apply Rge_le in Hge; exact Hge.
              }
              assert (Hex_g : ex_RInt g x y) by (apply ex_RInt_const).
              assert (Hex_f : ex_RInt f x y).
              {
                apply ex_RInt_continuous with (f := f) (a := x) (b := y).
                intros z Hz.
                rewrite (Rmin_left x y) in Hz by lra.
                rewrite (Rmax_right x y) in Hz by lra.
                destruct Hz as [Hz1 Hz2].
                assert (Hz_pos : 0 < z) by (apply Rlt_le_trans with x; [lra | exact Hz1]).
                apply Hcont_f_pos; exact Hz_pos.
              }
              assert (H_le : RInt g x y <= RInt f x y).
              {
                apply RInt_le; [lra | exact Hex_g | exact Hex_f | ].
                intros t Ht.
                apply Hg_le_f.
                split.
                - apply Rlt_le; apply (proj1 Ht).
                - apply Rlt_le; apply (proj2 Ht).
              }
              assert (H_eq : RInt g x y = f y * (y - x)).
              {
                unfold g.
                rewrite RInt_const.
                unfold scal.
                rewrite Rmult_comm.
                reflexivity.
              }
              rewrite H_eq in H_le.
              apply Rle_ge; exact H_le.
          }

          assert (H_re_le_int : re_pos_term (S m') <= RInt f (INR m') (INR (S m'))).
          {
            set (x := INR m') in *.
            set (y := INR (S m')) in *.
            assert (Hm'_ge_1_nat : (1 <= m')%nat).
            { clear - Hnm Hlt' Hm_eq.
              enough (1 < m)%nat by (rewrite Hm_eq in *; lia).
              apply Nat.le_lt_trans with n.
              - apply (proj1 Hnm).
              - apply Hlt'.
            }
            apply le_INR in Hm'_ge_1_nat.
            assert (Hxy : 1 <= x <= y).
            { split.
              - exact Hm'_ge_1_nat.
              - apply le_INR; lia.
            }
            specialize (Hf_min x y Hxy).
            simpl in Hf_min.
            assert (Hdiff : y - x = 1) by (unfold y; rewrite S_INR; unfold x; ring).
            rewrite Hdiff, Rmult_1_r in Hf_min.

            unfold re_pos_term, f.
            assert (Hpow_pos_y : 0 < Rpower y σ) by (apply Rpower_pos; apply lt_0_INR; lia).
            assert (Hpow_pos_z : 0 < Rpower (INR (S (S m'))) σ) by (apply Rpower_pos; apply lt_0_INR; lia).
            assert (Hσ_pos : 0 < σ) by lra.
            assert (Hpow_le : Rpower y σ <= Rpower (INR (S (S m'))) σ).
            {
              apply Rle_Rpower_l.
              - apply Rlt_le, Hσ_pos.
              - split.
                + apply lt_0_INR; lia.
                + apply le_INR; lia.
            }
            assert (Hinv_le : / (Rpower (INR (S (S m'))) σ) <= / (Rpower y σ)).
            { apply Rinv_le_contravar; [exact Hpow_pos_y | exact Hpow_le]. }
            assert (Hy_pos : 0 < y) by (apply lt_0_INR; lia).
            assert (Hr : / (Rpower (INR (S (S m'))) σ) <= Rpower y (- σ)).
            {
              rewrite Rpower_Ropp.
              exact Hinv_le.
            }
            apply Rle_trans with (Rpower y (-σ)).
            - exact Hr.
            - apply Rge_le. exact Hf_min.
          }

          rewrite Hm_eq.
          rewrite Hm_eq in H_Chasles.
          replace (part_sum (S m')) with (part_sum m' + re_pos_term (S m')) in *.
          2: { unfold part_sum; rewrite sum_f_R0_S; reflexivity. }
          replace (part_sum m' + re_pos_term (S m') - part_sum n) with ((part_sum m' - part_sum n) + re_pos_term (S m')) in * by ring.
          rewrite H_Chasles.
          apply Rplus_le_compat.
          - exact IH_nm'.
          - exact H_re_le_int.
      - exfalso; lia.
    }

    assert (H_int_cauchy : forall eps : R, eps > 0 ->
            exists A : R, forall x y : R, A < x <= y -> Rabs (RInt f x y) < eps).
    {
      intros eps Heps.
      set (eps2 := eps / 2).
      assert (Heps2 : 0 < eps2) by (unfold eps2; apply Rdiv_lt_0_compat; [exact Heps | apply Rlt_0_2]).
      pose proof (is_RInt_gen_filterlim f (at_point 1) (Rbar_locally p_infty) I_f) as Hlim.
      specialize (Hlim (at_point_filter 1).(filter_filter) (Rbar_locally_filter p_infty).(filter_filter) Hf_int).
      rewrite filterlim_locally in Hlim.
      specialize (Hlim (mkposreal eps2 Heps2)) as H_prod.
      destruct H_prod as [Q1 Q2 HQ1 HQ2 Hmain].
      assert (Q1_1 : Q1 1) by (apply GammaIntegralConverges.at_point_contains_self, HQ1).
      destruct HQ2 as [A HA].
      set (A0 := Rmax A 1).
      exists A0.
      intros x y [Hx_gt_A0 Hle].
      assert (Hx_gt_A : x > A) by (apply Rle_lt_trans with A0; [apply Rmax_l | exact Hx_gt_A0]).
      assert (Hx_gt_1 : 1 < x) by (apply Rle_lt_trans with A0; [apply Rmax_r | exact Hx_gt_A0]).
      assert (Hx_ge_1 : 1 <= x) by (apply Rlt_le; exact Hx_gt_1).
      assert (Hy_gt_A : y > A) by (apply Rlt_le_trans with x; [exact Hx_gt_A | exact Hle]).
      assert (Hy_gt_1 : 1 < y) by (apply Rlt_le_trans with x; [exact Hx_gt_1 | exact Hle]).
      assert (Hy_ge_1 : 1 <= y) by (apply Rlt_le; exact Hy_gt_1).

      assert (Hball_x : ball I_f (mkposreal eps2 Heps2) (RInt f 1 x)).
      { apply Hmain; [exact Q1_1 | apply HA; exact Hx_gt_A]. }
      assert (Hball_y : ball I_f (mkposreal eps2 Heps2) (RInt f 1 y)).
      { apply Hmain; [exact Q1_1 | apply HA; exact Hy_gt_A]. }
      unfold ball in Hball_x, Hball_y; simpl in Hball_x, Hball_y.

      assert (Hex_1x : ex_RInt f 1 x).
      {
        apply ex_RInt_continuous with (f := f) (a := 1) (b := x).
        intros z Hz.
        destruct Hz as [Hz_low Hz_high].
        rewrite (Rmin_left 1 x) in Hz_low by (apply Rlt_le; exact Hx_gt_1).
        rewrite (Rmax_right 1 x) in Hz_high by (apply Rlt_le; exact Hx_gt_1).
        assert (Hz_pos : 0 < z) by (apply Rlt_le_trans with 1; [apply Rlt_0_1 | exact Hz_low]).
        apply Hcont_f_pos; exact Hz_pos.
      }

      assert (Hex_1y : ex_RInt f 1 y).
      {
        apply ex_RInt_continuous with (f := f) (a := 1) (b := y).
        intros z Hz.
        destruct Hz as [Hz_low Hz_high].
        rewrite (Rmin_left 1 y) in Hz_low by (apply Rlt_le; exact Hy_gt_1).
        rewrite (Rmax_right 1 y) in Hz_high by (apply Rlt_le; exact Hy_gt_1).
        assert (Hz_pos : 0 < z) by (apply Rlt_le_trans with 1; [apply Rlt_0_1 | exact Hz_low]).
        apply Hcont_f_pos; exact Hz_pos.
      }

      assert (Hex_xy : ex_RInt f x y).
      {
        apply ex_RInt_continuous with (f := f) (a := x) (b := y).
        intros z Hz.
        destruct Hz as [Hz_low Hz_high].
        rewrite (Rmin_left x y) in Hz_low by (exact Hle).
        rewrite (Rmax_right x y) in Hz_high by (exact Hle).
        assert (Hx_pos : 0 < x) by (apply Rlt_le_trans with 1; [apply Rlt_0_1 | exact Hx_ge_1]).
        assert (Hz_pos : 0 < z) by (apply Rlt_le_trans with x; [exact Hx_pos | exact Hz_low]).
        apply Hcont_f_pos; exact Hz_pos.
      }

      assert (H_Chasles : RInt f 1 x + RInt f x y = RInt f 1 y).
      { apply (RInt_Chasles f 1 x y Hex_1x Hex_xy). }
      replace (RInt f x y) with (RInt f 1 y - RInt f 1 x) by lra.
      replace (RInt f 1 y - RInt f 1 x) with ((RInt f 1 y - I_f) - (RInt f 1 x - I_f)) by ring.
      eapply Rle_lt_trans.
      - apply Rabs_triang_sub.
      - simpl in Hball_x, Hball_y.
        assert (Hx : Rabs (RInt f 1 x - I_f) < eps2) by exact Hball_x.
        assert (Hy : Rabs (RInt f 1 y - I_f) < eps2) by exact Hball_y.
        assert (Hsum : eps2 + eps2 = eps) by (unfold eps2; field).
        rewrite <- Hsum.
        apply Rplus_lt_compat; [exact Hy | exact Hx].
    }

    assert (part_sum_mono : forall n m, (n <= m)%nat -> part_sum n <= part_sum m).
    {
      induction 1 as [| p Hle IHle].
      - apply Rle_refl.
      - apply Rle_trans with (part_sum p).
        + exact IHle.
        + apply part_sum_incr.
    }

    assert (H_cauchy : forall eps : R, eps > 0 -> exists N : nat,
              forall n m : nat, (n >= N)%nat -> (m >= n)%nat ->
              Rabs (part_sum m - part_sum n) < eps).
    {
      intros eps Heps.
      destruct (H_int_cauchy eps Heps) as [A HA].
      destruct (archimed A) as [Hlow Hhigh].
      set (q := Z.max (up A) 1%Z).
      set (N := Z.to_nat q).
      assert (H_N_gt_A : INR N > A).
      {
        unfold N.
        assert (Hq_nonneg : Z.le 0 q).
        { apply Z.le_trans with 1%Z.
          - apply Z.le_0_1.
          - apply Z.le_max_r.
        }
        rewrite INR_IZR_INZ, Z2Nat.id; [| exact Hq_nonneg].
        apply Rlt_le_trans with (IZR (up A)).
        - exact Hlow.
        - apply IZR_le. apply Z.le_max_l.
      }
      exists N.
      intros n m Hn Hnm.
      assert (Hn_ge_A : A < INR n).
      { apply Rlt_le_trans with (INR N).
        - exact H_N_gt_A.
        - apply le_INR; lia.
      }
      assert (Hm_ge_A : A < INR m).
      { apply Rlt_le_trans with (INR n).
        - exact Hn_ge_A.
        - apply le_INR; lia.
      }
      assert (Hle_INR : INR n <= INR m) by (apply le_INR; lia).
      assert (H1_nm : (1 <= n <= m)%nat) by lia.
      assert (Hex_nm : ex_RInt f (INR n) (INR m)).
      {
        apply ex_RInt_continuous with (f := f) (a := INR n) (b := INR m).
        intros z Hz.
        destruct Hz as [Hz1 Hz2].
        rewrite (Rmin_left (INR n) (INR m)) in Hz1 by (apply le_INR; lia).
        rewrite (Rmax_right (INR n) (INR m)) in Hz2 by (apply le_INR; lia).
        assert (Hz_pos : 0 < z).
        {
          apply Rlt_le_trans with (INR n).
          - apply lt_0_INR; lia.
          - exact Hz1.
        }
        apply Hcont_f_pos; exact Hz_pos.
      }
      assert (H_RInt_bound : Rabs (RInt f (INR n) (INR m)) < eps).
      { apply HA; split; [exact Hn_ge_A | exact Hle_INR]. }
      assert (HRInt_nonneg : 0 <= RInt f (INR n) (INR m)).
      {
        apply RInt_ge_0.
        - apply le_INR; lia.
        - exact Hex_nm.
        - intros t Ht.
          apply Rlt_le, Hf_pos.
          destruct Ht as [Ht1 Ht2].
          apply Rlt_le_trans with (INR n).
          + apply lt_0_INR; lia.
          + apply Rlt_le; exact Ht1.
      }
      assert (H_part_sum_bound : part_sum m - part_sum n <= RInt f (INR n) (INR m)).
      { apply Hineq; exact H1_nm. }
      destruct H1_nm as [_ Hn0_le_m0].
      assert (Hdiff_ge0 : 0 <= part_sum m - part_sum n).
      { pose proof (part_sum_mono n m Hn0_le_m0) as Hle; lra. }
      rewrite Rabs_pos_eq; [| exact Hdiff_ge0].
      eapply Rle_lt_trans.
      - exact H_part_sum_bound.
      - rewrite <- (Rabs_pos_eq (RInt f (INR n) (INR m)) HRInt_nonneg).
        exact H_RInt_bound.
    }

    assert (H_cauchy_series : Cauchy_crit_series re_pos_term).
    {
      intros eps Heps.
      destruct (H_cauchy eps Heps) as [N HN].
      exists N.
      intros n m Hn Hm.
      destruct (le_ge_dec n m) as [Hle | Hge].
      - assert (Htmp : Rabs (part_sum m - part_sum n) < eps).
        { apply HN with (n := n) (m := m); [exact Hn | lia]. }
        rewrite <- (Rabs_minus_sym (part_sum n) (part_sum m)) in Htmp.
        exact Htmp.
      - assert (Htmp : Rabs (part_sum n - part_sum m) < eps).
        { apply HN with (n := m) (m := n); [exact Hm | lia]. }
        exact Htmp.
    }

    pose (F := filtermap part_sum eventually).
    assert (H_proper : ProperFilter F).
    { apply filtermap_proper_filter; apply eventually_filter. }
    assert (H_cauchy_cond : forall eps : posreal, exists x : R, F (ball x eps)).
    {
      intros eps.
      destruct (H_cauchy_series eps (cond_pos eps)) as [N HN].
      exists (part_sum N).
      unfold F.
      exists N.
      intros n Hn.
      unfold ball, AbsRing_ball.
      apply HN; [exact Hn | apply le_n].
    }
    pose (l_re_pos := R_complete_lim F).
    assert (H_lim : forall eps : posreal, F (ball l_re_pos eps)).
    { apply R_complete; [exact H_proper | exact H_cauchy_cond]. }
    exists l_re_pos.
    intros eps Heps.
    pose (eps' := mkposreal eps Heps).
    destruct (H_lim eps') as [N HN].
    exists N; intros n Hn.
    specialize (HN n Hn).
    assumption.
  }

  destruct H_re_pos_lim as [l_re_pos H_re_pos].

  set (re_term := fun n : nat => Rpower (INR (S n)) (-σ) * cos (τ * ln (INR (S n)))).

  assert (H_cauchy_pos : Cauchy_crit_series re_pos_term).
  { apply cv_cauchy_1; exists l_re_pos; exact H_re_pos. }

  assert (H_re_cauchy : Cauchy_crit_series re_term).
  {
    intros eps Heps.
    destruct (H_cauchy_pos eps Heps) as [N HN].
    exists N.
    intros n m Hn Hm.
    set (f := fun i => Rabs (re_term i)).
    set (g := re_pos_term).

    assert (Hfg : forall i, f i <= g i).
    {
      intros i.
      unfold f, g, re_term, re_pos_term, u.
      rewrite Rabs_mult.
      assert (Hpower_pos : 0 < Rpower (INR (S i)) (-σ)).
      { apply Rpower_pos. apply lt_0_INR. lia. }
      assert (Hpower_nonneg : 0 <= Rpower (INR (S i)) (-σ)) by lra.
      rewrite (Rabs_pos_eq (Rpower (INR (S i)) (-σ)) Hpower_nonneg).

      assert (Hcos_abs : Rabs (cos (τ * ln (INR (S i)))) <= 1).
      {
        assert (Hcos_sq_le_1 : (cos (τ * ln (INR (S i))))² <= 1).
        {
          rewrite <- (cos_sq_plus_sin_sq (τ * ln (INR (S i)))).
          apply Rle_trans with ((cos (τ * ln (INR (S i))))² + (sin (τ * ln (INR (S i))))²).
          - rewrite <- Rplus_0_r at 1. apply Rplus_le_compat_l; apply Rle_0_sqr.
          - rewrite cos_sq_plus_sin_sq; apply Rle_refl.
        }
        rewrite <- sqrt_Rsqr_abs.
        rewrite <- sqrt_1.
        apply sqrt_le_1_c.
        - apply Rle_0_sqr.
        - apply Rle_0_1.
        - exact Hcos_sq_le_1.
      }

      assert (Heq : Rpower (INR (S i)) (-σ) = / Rpower (INR (S i)) σ).
      { rewrite Rpower_Ropp. reflexivity. }
      rewrite Heq.

      apply Rmult_le_reg_l with (r := Rpower (INR (S i)) σ).
      - apply Rpower_pos; apply lt_0_INR; lia.
      - rewrite <- Rmult_assoc.
        rewrite Rinv_r.
        + rewrite Rmult_1_l. exact Hcos_abs.
        + apply Rgt_not_eq; apply Rpower_pos; apply lt_0_INR; lia.
    }

    assert (Habs_sum_diff : forall x y,
        Rabs (sum_f_R0 re_term x - sum_f_R0 re_term y) <=
          sum_f_R0 f (Nat.max x y) - sum_f_R0 f (Nat.min x y)).
    {
      assert (Hdiff_abs : forall (A : nat -> R) (i j : nat),
          (i <= j)%nat -> Rabs (sum_f_R0 A j - sum_f_R0 A i) <=
            sum_f_R0 (fun k => Rabs (A k)) j - sum_f_R0 (fun k => Rabs (A k)) i).
      {
        intros A i j Hle.
        revert i Hle.
        induction j as [|j IH].
        - intros i Hle. destruct i; [| lia].
          simpl.
          rewrite Rminus_diag, Rabs_R0.
          replace (Rabs (A 0%nat) - Rabs (A 0%nat)) with 0 by ring.
          apply Rle_refl.
        - intros i Hle.
          destruct (le_gt_dec i (S j)) as [Hle'|Hgt]; [| lia].
          destruct (eq_nat_dec i (S j)) as [Heq|Hneq].
          + subst i.
            simpl.
            rewrite Rminus_diag, Rabs_R0.
            rewrite Rminus_diag.
            apply Rle_refl.
          + assert (Hlt : (i <= j)%nat) by lia.
            simpl (sum_f_R0 A (S j)).
            replace (sum_f_R0 A j + A (S j) - sum_f_R0 A i)
              with ((sum_f_R0 A j - sum_f_R0 A i) + A (S j)) by ring.
            rewrite (Rabs_triang (sum_f_R0 A j - sum_f_R0 A i) (A (S j))).
            rewrite sum_f_R0_S with (f := fun k => Rabs (A k)) (n := j).
            replace (sum_f_R0 (fun k => Rabs (A k)) j + Rabs (A (S j)) - sum_f_R0 (fun k => Rabs (A k)) i)
              with ((sum_f_R0 (fun k => Rabs (A k)) j - sum_f_R0 (fun k => Rabs (A k)) i) + Rabs (A (S j))) by ring.
            apply Rplus_le_compat.
            * apply IH; auto.
            * apply Rle_refl.
      }
      intros x y.
      destruct (le_ge_dec x y) as [Hle | Hge].
      - rewrite (Rabs_minus_sym (sum_f_R0 re_term x) (sum_f_R0 re_term y)).
        assert (Hmax : Nat.max x y = y) by (apply Nat.max_r; auto).
        assert (Hmin : Nat.min x y = x) by (apply Nat.min_l; auto).
        rewrite Hmax, Hmin.
        apply Hdiff_abs with (A := re_term) (i := x) (j := y); auto.
      - assert (Hmax : Nat.max x y = x) by (apply Nat.max_l; lia).
        assert (Hmin : Nat.min x y = y) by (apply Nat.min_r; lia).
        rewrite Hmax, Hmin.
        apply Hdiff_abs with (A := re_term) (i := y) (j := x); lia.
    }

    assert (Hsum_le : forall i j, (i <= j)%nat ->
        sum_f_R0 f j - sum_f_R0 f i <= sum_f_R0 re_pos_term j - sum_f_R0 re_pos_term i).
    {
      intros i j Hij.
      revert i Hij.
      induction j as [|j IH].
      - intros i Hij. destruct i; [| lia]. simpl. lra.
      - intros i Hij.
        destruct (le_gt_dec i (S j)) as [Hle|Hgt]; [| lia].
        destruct (eq_nat_dec i (S j)) as [Heq|Hneq].
        + subst. simpl. lra.
        + assert (Hlt : (i <= j)%nat) by lia.
          rewrite sum_f_R0_S, sum_f_R0_S.
          replace (sum_f_R0 f j + f (S j) - sum_f_R0 f i)
            with ((sum_f_R0 f j - sum_f_R0 f i) + f (S j)) by ring.
          replace (sum_f_R0 re_pos_term j + re_pos_term (S j) - sum_f_R0 re_pos_term i)
            with ((sum_f_R0 re_pos_term j - sum_f_R0 re_pos_term i) + re_pos_term (S j)) by ring.
          apply Rplus_le_compat.
          * apply IH; auto.
          * apply Hfg.
    }

    apply Rle_lt_trans with (sum_f_R0 f (Nat.max n m) - sum_f_R0 f (Nat.min n m)).
    - apply Habs_sum_diff.
    - apply Rle_lt_trans with (sum_f_R0 re_pos_term (Nat.max n m) - sum_f_R0 re_pos_term (Nat.min n m)).
      + apply Hsum_le with (i := Nat.min n m) (j := Nat.max n m).
        * apply Nat.le_trans with n; [apply Nat.le_min_l | apply Nat.le_max_l].
      + assert (Hmin_le_max : (Nat.min n m <= Nat.max n m)%nat).
        { apply Nat.le_trans with n; [apply Nat.le_min_l | apply Nat.le_max_l]. }
        assert (Hnonneg : 0 <= sum_f_R0 re_pos_term (Nat.max n m) - sum_f_R0 re_pos_term (Nat.min n m)).
        { rewrite <- Rminus_le_0.
          apply sum_f_R0_incr.
          - intros k. rewrite sum_f_R0_S.
            assert (Hposk : 0 <= re_pos_term (S k)).
            { unfold re_pos_term. apply Rlt_le, Rinv_0_lt_compat, Hpos. }
            apply Rle_trans with (sum_f_R0 re_pos_term k + 0).
            + rewrite Rplus_0_r; apply Rle_refl.
            + apply Rplus_le_compat_l. exact Hposk.
          - exact Hmin_le_max.
        }
        rewrite <- (Rabs_pos_eq _ Hnonneg).
        apply HN.
        * apply Nat.le_trans with n; [exact Hn | apply Nat.le_max_l].
        * apply Nat.min_glb; [exact Hn | exact Hm].
  }

  destruct (cv_cauchy_2 re_term H_re_cauchy) as [l_re H_re_conv].

  set (im_term := fun n : nat => - Rpower (INR (S n)) (-σ) * sin (τ * ln (INR (S n)))).

  assert (Habs_im_le_re_pos : forall n, Rabs (im_term n) <= re_pos_term n).
  {
    intros i.
    unfold im_term, re_pos_term, u.
    rewrite Rabs_mult.
    rewrite Rabs_Ropp.
    assert (Hpower_pos_neg : 0 < Rpower (INR (S i)) (-σ)).
    { apply Rpower_pos. apply lt_0_INR. lia. }
    assert (Hpower_nonneg : 0 <= Rpower (INR (S i)) (-σ)) by lra.
    rewrite (Rabs_pos_eq (Rpower (INR (S i)) (-σ)) Hpower_nonneg).
    rewrite Rpower_Ropp.
    assert (Hsin_abs : Rabs (sin (τ * ln (INR (S i)))) <= 1).
    {
      destruct (SIN_bound (τ * ln (INR (S i)))) as [Hlb Hub].
      apply Rabs_le; split; [exact Hlb | exact Hub].
    }
    set (r := / Rpower (INR (S i)) σ).
    assert (Hr_ge_0 : 0 <= r).
    { apply Rlt_le. apply Rinv_0_lt_compat. apply Rpower_pos. apply lt_0_INR. lia. }
    apply (Rmult_le_compat_l r (Rabs (sin (τ * ln (INR (S i))))) 1) in Hr_ge_0;
      [| exact Hsin_abs].
    rewrite Rmult_1_r in Hr_ge_0.
    exact Hr_ge_0.
  }

  set (f_im := fun i => Rabs (im_term i)).

  assert (Habs_sum_diff_im : forall x y,
      Rabs (sum_f_R0 im_term x - sum_f_R0 im_term y) <=
        sum_f_R0 f_im (Nat.max x y) - sum_f_R0 f_im (Nat.min x y)).
  {
    assert (Hdiff_abs : forall (A : nat -> R) (i j : nat),
        (i <= j)%nat -> Rabs (sum_f_R0 A j - sum_f_R0 A i) <=
          sum_f_R0 (fun k => Rabs (A k)) j - sum_f_R0 (fun k => Rabs (A k)) i).
    {
      intros A i j Hle.
      revert i Hle.
      induction j as [|j IH].
      - intros i Hle. destruct i; [| lia].
        simpl.
        rewrite Rminus_diag, Rabs_R0.
        replace (Rabs (A 0%nat) - Rabs (A 0%nat)) with 0 by ring.
        apply Rle_refl.
      - intros i Hle.
        destruct (le_gt_dec i (S j)) as [Hle'|Hgt]; [| lia].
        destruct (eq_nat_dec i (S j)) as [Heq|Hneq].
        + subst i.
          simpl.
          rewrite Rminus_diag, Rabs_R0.
          rewrite Rminus_diag.
          apply Rle_refl.
        + assert (Hlt : (i <= j)%nat) by lia.
          simpl (sum_f_R0 A (S j)).
          replace (sum_f_R0 A j + A (S j) - sum_f_R0 A i)
            with ((sum_f_R0 A j - sum_f_R0 A i) + A (S j)) by ring.
          rewrite (Rabs_triang (sum_f_R0 A j - sum_f_R0 A i) (A (S j))).
          rewrite sum_f_R0_S with (f := fun k => Rabs (A k)) (n := j).
          replace (sum_f_R0 (fun k => Rabs (A k)) j + Rabs (A (S j)) - sum_f_R0 (fun k => Rabs (A k)) i)
            with ((sum_f_R0 (fun k => Rabs (A k)) j - sum_f_R0 (fun k => Rabs (A k)) i) + Rabs (A (S j))) by ring.
          apply Rplus_le_compat.
          * apply IH; auto.
          * apply Rle_refl.
    }
    intros x y.
    destruct (le_ge_dec x y) as [Hle | Hge].
    - rewrite (Rabs_minus_sym (sum_f_R0 im_term x) (sum_f_R0 im_term y)).
      assert (Hmax : Nat.max x y = y) by (apply Nat.max_r; auto).
      assert (Hmin : Nat.min x y = x) by (apply Nat.min_l; auto).
      rewrite Hmax, Hmin.
      apply Hdiff_abs with (A := im_term) (i := x) (j := y); auto.
    - assert (Hmax : Nat.max x y = x) by (apply Nat.max_l; lia).
      assert (Hmin : Nat.min x y = y) by (apply Nat.min_r; lia).
      rewrite Hmax, Hmin.
      apply Hdiff_abs with (A := im_term) (i := y) (j := x); lia.
  }

  assert (Hsum_le_im : forall i j, (i <= j)%nat ->
      sum_f_R0 f_im j - sum_f_R0 f_im i <= sum_f_R0 re_pos_term j - sum_f_R0 re_pos_term i).
  {
    intros i j Hij.
    revert i Hij.
    induction j as [|j IH].
    - intros i Hij. destruct i; [| lia]. simpl. lra.
    - intros i Hij.
      destruct (le_gt_dec i (S j)) as [Hle|Hgt]; [| lia].
      destruct (eq_nat_dec i (S j)) as [Heq|Hneq].
      + subst. simpl. lra.
      + assert (Hlt : (i <= j)%nat) by lia.
        rewrite sum_f_R0_S, sum_f_R0_S.
        replace (sum_f_R0 f_im j + f_im (S j) - sum_f_R0 f_im i)
          with ((sum_f_R0 f_im j - sum_f_R0 f_im i) + f_im (S j)) by ring.
        replace (sum_f_R0 re_pos_term j + re_pos_term (S j) - sum_f_R0 re_pos_term i)
          with ((sum_f_R0 re_pos_term j - sum_f_R0 re_pos_term i) + re_pos_term (S j)) by ring.
        apply Rplus_le_compat.
        * apply IH; auto.
        * apply Habs_im_le_re_pos.
  }

  assert (H_incr_re_pos : forall k, sum_f_R0 re_pos_term k <= sum_f_R0 re_pos_term (S k)).
  { intros k. rewrite sum_f_R0_S.
    pose proof (Rinv_0_lt_compat _ (Hpos (S k))) as H0.
    apply Rle_trans with (sum_f_R0 re_pos_term k + 0).
    - rewrite Rplus_0_r; apply Rle_refl.
    - apply Rplus_le_compat_l. apply Rlt_le, H0. }

  assert (Hinc_re_pos : forall i j, (i <= j)%nat -> sum_f_R0 re_pos_term i <= sum_f_R0 re_pos_term j).
  {
    intros i j Hle.
    induction Hle as [| j' Hle' IH].
    - apply Rle_refl.
    - apply Rle_trans with (sum_f_R0 re_pos_term j').
      + exact IH.
      + apply H_incr_re_pos.
  }

  assert (H_im_cauchy : Cauchy_crit_series im_term).
  {
    intros eps' Heps'.
    destruct (H_cauchy_pos eps' Heps') as [N' HN'].
    exists N'.
    intros n' m' Hn' Hm'.
    unfold Rdist.

    assert (Hstep1 :
      Rabs (sum_f_R0 im_term n' - sum_f_R0 im_term m')
      <= sum_f_R0 f_im (Nat.max n' m') - sum_f_R0 f_im (Nat.min n' m')).
    { apply Habs_sum_diff_im. }

    assert (Hmin_le_max : (Nat.min n' m' <= Nat.max n' m')%nat).
    { apply Nat.le_trans with (m := n'); [apply Nat.le_min_l | apply Nat.le_max_l]. }

    assert (Hsum_incr : sum_f_R0 re_pos_term (Nat.min n' m') <= sum_f_R0 re_pos_term (Nat.max n' m')).
    { apply Hinc_re_pos. exact Hmin_le_max. }

    assert (Hstep3 :
      sum_f_R0 re_pos_term (Nat.max n' m') - sum_f_R0 re_pos_term (Nat.min n' m')
      = Rdist (sum_f_R0 re_pos_term (Nat.max n' m')) (sum_f_R0 re_pos_term (Nat.min n' m'))).
    { unfold Rdist.
      rewrite Rabs_pos_eq; [ring | lra]. }

    assert (Hmax_ge_N' : (Nat.max n' m' >= N')%nat).
    { apply Nat.le_trans with n'; [exact Hn' | apply Nat.le_max_l]. }
    assert (Hmin_ge_N' : (Nat.min n' m' >= N')%nat).
    { apply Nat.min_glb; [exact Hn' | exact Hm']. }

    assert (Hstep4 :
      Rdist (sum_f_R0 re_pos_term (Nat.max n' m')) (sum_f_R0 re_pos_term (Nat.min n' m')) < eps').
    { apply HN'; [exact Hmax_ge_N' | exact Hmin_ge_N']. }

    apply Rle_lt_trans with (sum_f_R0 f_im (Nat.max n' m') - sum_f_R0 f_im (Nat.min n' m')).
    - exact Hstep1.
    - apply Rle_lt_trans with (sum_f_R0 re_pos_term (Nat.max n' m') - sum_f_R0 re_pos_term (Nat.min n' m')).
      + apply Hsum_le_im. exact Hmin_le_max.
      + rewrite Hstep3. exact Hstep4.
  }

  destruct (cv_cauchy_2 im_term H_im_cauchy) as [l_im H_im_conv].

  destruct (cauchy_seq_converges (fun N => re (Csum (zeta_series_term s) N))
                                 (re_partial_sum_cauchy s Hre)) as [l_re_correct H_re_correct].
  destruct (cauchy_seq_converges (fun N => im (Csum (zeta_series_term s) N))
                                 (im_partial_sum_cauchy s Hre)) as [l_im_correct H_im_correct].

  exists (l_re_correct +i l_im_correct).
  unfold Cseq_limit.
  intros eps Heps.
  set (eps2 := eps / 2).
  assert (Heps2 : 0 < eps2) by (apply Rdiv_lt_0_compat; [exact Heps | lra]).

  destruct (H_re_correct eps2 Heps2) as [N1 HN1].
  destruct (H_im_correct eps2 Heps2) as [N2 HN2].
  set (N := S (Nat.max N1 N2)).
  exists N.
  intros n Hn.
  assert (Hn_gt_0 : (n > 0)%nat) by lia.
  replace n with (S (pred n)) by lia.

  assert (H_re_sub : forall z1 z2, re (z1 -c z2) = re z1 - re z2).
  { intros; unfold Csub; simpl; ring. }
  assert (H_im_sub : forall z1 z2, im (z1 -c z2) = im z1 - im z2).
  { intros; unfold Csub; simpl; ring. }
  rewrite H_re_sub, H_im_sub.

change (fun k : nat => my_complex_pow (INR (S k) +i 0) (-c s) _) with (zeta_series_term s) in *.

  rewrite (re_Csum_zeta s (pred n)), (im_Csum_zeta s (pred n)).
  unfold GammaIntegralConverges.re_term, GammaIntegralConverges.im_term.

  assert (H_re : ℜ(l_re_correct +i l_im_correct) = l_re_correct) by reflexivity.
  assert (H_im : ℑ(l_re_correct +i l_im_correct) = l_im_correct) by reflexivity.
  rewrite H_re, H_im.

  apply Rle_lt_trans with (Rabs (sum_f_R0 (GammaIntegralConverges.re_term s) (pred n) - l_re_correct) +
                           Rabs (sum_f_R0 (GammaIntegralConverges.im_term s) (pred n) - l_im_correct)).
  - rewrite !pow2_sqr.
    apply sqrt_le_plus_abs.
  - rewrite <- re_Csum_zeta, <- im_Csum_zeta.
    replace (S (pred n)) with n by lia.
    apply Rlt_le_trans with (eps2 + eps2).
    + apply Rplus_lt_compat; [apply HN1 | apply HN2]; lia.
    + replace (eps2 + eps2) with eps by (unfold eps2; field; lra).
      apply Rle_refl.
Qed.

(* 定理：p级数收敛 *)

(* 定理：p‑级数收敛(Set 类型(Σ-类型)) *)

(* 绝对值比较判别法的柯西形式 *)
Lemma abs_comparison_cauchy (a b : nat -> R) :
  (forall n, Rabs (a n) <= b n) ->
  Cauchy_crit_series b ->
  Cauchy_crit_series a.
Proof.
  intros Hab H_cauchy_b eps Heps.
  destruct (H_cauchy_b eps Heps) as [N HN].
  exists N.
  intros n m Hn Hm.
  pose (p := Nat.min n m). pose (q := Nat.max n m).
  assert (Hp_le_q : (p <= q)%nat) by (apply (Nat.le_trans p n q); [apply Nat.le_min_l | apply Nat.le_max_l]).
  assert (Habs : Rabs (sum_f_R0 a q - sum_f_R0 a p) <= sum_f_R0 b q - sum_f_R0 b p).
  { revert p Hp_le_q.
    induction q as [|q IHq]; intros p Hle.
    - destruct p; [|lia]. simpl. rewrite Rminus_diag, Rabs_R0. rewrite Rminus_diag. lra.
    - destruct (eq_nat_dec p (S q)) as [Heq|Hneq].
      + subst p. simpl. rewrite Heq. rewrite Rminus_diag, Rabs_R0. rewrite Rminus_diag. apply Rle_refl.
      + assert (Hp_le_q' : (p <= q)%nat) by lia.
        simpl (sum_f_R0 a (S q)). simpl (sum_f_R0 b (S q)).
        replace (sum_f_R0 a q + a (S q) - sum_f_R0 a p)
          with ((sum_f_R0 a q - sum_f_R0 a p) + a (S q)) by ring.
        replace (sum_f_R0 b q + b (S q) - sum_f_R0 b p)
          with ((sum_f_R0 b q - sum_f_R0 b p) + b (S q)) by ring.
        apply Rle_trans with (Rabs (sum_f_R0 a q - sum_f_R0 a p) + Rabs (a (S q))).
        + apply Rabs_triang.
        + apply Rplus_le_compat.
          * apply IHq; auto.
          * apply Hab.
  }
  destruct (Nat.leb_spec n m) as [Hle|Hgt].
  - 
    assert (p = n /\ q = m) as [Hp_eq Hq_eq].
    { unfold p, q. rewrite Nat.min_l, Nat.max_r; auto. }
    rewrite Hp_eq, Hq_eq in Habs.
    unfold Rdist.
    rewrite Rabs_minus_sym.
    apply Rle_lt_trans with (sum_f_R0 b m - sum_f_R0 b n).
    + exact Habs.
    + assert (Hb_nonneg : forall k, 0 <= b k).
      { intros k. apply Rle_trans with (Rabs (a k)); [apply Rabs_pos | apply Hab]. }
      assert (Hsum_incr : forall i j, (i <= j)%nat -> sum_f_R0 b i <= sum_f_R0 b j).
      { intros i j Hij. induction Hij; [apply Rle_refl | apply Rle_trans with (sum_f_R0 b m0); [apply IHHij |]].
        simpl. apply Rle_self_plus. apply Hb_nonneg. }
      assert (H_le : sum_f_R0 b n <= sum_f_R0 b m) by (apply Hsum_incr; lia).
      assert (H_diff_nonneg : 0 <= sum_f_R0 b m - sum_f_R0 b n).
      { apply Rplus_le_compat_l with (r := - sum_f_R0 b n) in H_le.
        rewrite Rplus_opp_l in H_le.
        rewrite Rplus_comm in H_le.
        exact H_le. }
      rewrite <- (Rabs_pos_eq _ H_diff_nonneg).
      apply HN; assumption.
  - 
    assert (p = m /\ q = n) as [Hp_eq Hq_eq].
    { unfold p, q. rewrite Nat.min_r, Nat.max_l; lia. }
    rewrite Hp_eq, Hq_eq in Habs.
    unfold Rdist.
    apply Rle_lt_trans with (sum_f_R0 b n - sum_f_R0 b m).
    + exact Habs.
    + assert (Hb_nonneg : forall k, 0 <= b k).
      { intros k. apply Rle_trans with (Rabs (a k)); [apply Rabs_pos | apply Hab]. }
      assert (Hsum_incr : forall i j, (i <= j)%nat -> sum_f_R0 b i <= sum_f_R0 b j).
      { intros i j Hij. induction Hij; [apply Rle_refl | apply Rle_trans with (sum_f_R0 b m0); [apply IHHij |]].
        simpl. apply Rle_self_plus. apply Hb_nonneg. }
      assert (H_le : sum_f_R0 b m <= sum_f_R0 b n) by (apply Hsum_incr; lia).
      assert (H_diff_nonneg : 0 <= sum_f_R0 b n - sum_f_R0 b m).
      { apply Rplus_le_compat_l with (r := - sum_f_R0 b m) in H_le.
        rewrite Rplus_opp_l in H_le.
        rewrite Rplus_comm in H_le.
        exact H_le. }
      rewrite <- (Rabs_pos_eq _ H_diff_nonneg).
      apply HN; assumption.
Qed.

(* 标量乘法的球映射 *)
Lemma scal_ball : forall (c : R) (Hc : c <> 0) (eps delta : R),
  0 < eps -> 0 < delta -> delta = eps / Rabs c ->
  forall y, AbsRing_ball R_AbsRing 0 delta y ->
          AbsRing_ball R_AbsRing 0 eps (c * y).
Proof.
  intros c Hc eps delta Heps Hdelta Heq y Hy.
  unfold AbsRing_ball in *; simpl in *.
  rewrite Rminus_0_r in Hy; rewrite Rminus_0_r.
  unfold abs.
  rewrite Rabs_mult.
  replace eps with (Rabs c * (eps / Rabs c)) by (field; apply Rgt_not_eq, Rabs_pos_lt; auto).
  apply Rmult_lt_compat_l.
  - apply Rabs_pos_lt; auto.
  - rewrite <- Heq; exact Hy.
Qed.

(* 非零标量乘法在零处的滤子极限 *)
Lemma filterlim_scal_zero : forall (c : R), c <> 0 ->
  filterlim (fun y : R => c * y) (locally 0) (locally 0).
Proof.
  intros c Hc.
  unfold filterlim, locally.
  intros V HV.
  destruct HV as [eps Hsub].
  pose (eps_r := pos eps).
  assert (Heps_pos : 0 < eps_r) by apply cond_pos.
  assert (Habs_c_pos : 0 < Rabs c) by (apply Rabs_pos_lt; exact Hc).
  pose (delta_r := eps_r / Rabs c).
  assert (Hdelta_pos : 0 < delta_r).
  { apply Rdiv_lt_0_compat; [exact Heps_pos | exact Habs_c_pos]. }
  exists (mkposreal delta_r Hdelta_pos).
  intros y Hy.
  apply Hsub.
  apply (@scal_ball c Hc eps_r delta_r Heps_pos Hdelta_pos eq_refl y Hy).
Qed.

(* 幂函数导数公式 *)
Lemma Derive_F_eq_f : forall (σ : R) (Hσ : 1 < σ),
  let f := fun t => Rpower t (-σ) in
  let F := fun t => - Rpower t (1 - σ) / (σ - 1) in
  forall x, 1 <= x -> Derive F x = f x.
Proof.
  intros σ Hσ f F x Hx.
  assert (Hx_pos : 0 < x) by lra.
  pose proof (derivable_pt_lim_power x (1-σ) Hx_pos) as Hpow.
  replace (1-σ-1) with (-σ) in Hpow by ring.
  set (c := - / (σ - 1)).
  pose proof (derivable_pt_lim_scal (fun t => Rpower t (1-σ)) c x ((1-σ) * Rpower x (-σ)) Hpow) as Hscal.
  simpl in Hscal.
  replace (c * ((1-σ) * Rpower x (-σ))) with (Rpower x (-σ)) in Hscal
    by (unfold c; field; lra).
  assert (Heq : forall t, c * Rpower t (1-σ) = - Rpower t (1-σ) / (σ - 1)).
  { intros t; unfold c; field; lra. }
  apply (derivable_pt_lim_ext (fun t => c * Rpower t (1-σ)) F x (Rpower x (-σ)) Heq) in Hscal.
  apply is_derive_Reals in Hscal.
  pose proof (is_derive_unique F x (Rpower x (-σ)) Hscal) as H_eq.
  unfold f; exact H_eq.
Qed.

(* 左端点广义积分点滤子判定 *)
Lemma is_RInt_gen_point_left (f : R -> R) (a : R) (G : (R -> Prop) -> Prop) (l : R) :
  (forall y, ex_RInt f a y) ->
  filterlim (fun b => RInt f a b) G (locally l) ->
  is_RInt_gen f (at_point a) G l.
Proof.
  intros Hex H. unfold is_RInt_gen. intros P HP.
  apply Filter_prod with (Q := fun x => x = a) (R := fun y => P (RInt f a y)).
  - unfold at_point; reflexivity.
  - apply H; exact HP.
  - intros x y Hx Hy. subst x.
    pose proof (Hex y) as Hex_ay.
    pose proof (RInt_correct f a y Hex_ay) as H_is.
    exists (RInt f a y). split.
    + exact H_is.
    + exact Hy.
Qed.

(* 负指数幂函数在正区间上的黎曼可积性 *)
Lemma ex_RInt_power_neg (σ : R) (Hσ : 1 < σ) (y : R) (Hy_pos : 0 < y) :
  ex_RInt (fun t => Rpower t (-σ)) 1 y.
Proof.
  destruct (Rle_lt_dec 1 y) as [Hle | Hlt].
  - (* 1 ≤ y *)
    apply ex_RInt_continuous with (f := fun t => Rpower t (-σ)) (a := 1) (b := y).
    intros z Hz.
    rewrite Rmin_left, Rmax_right in Hz by lra.
    assert (Hz_pos : 0 < z) by lra.
    apply continuity_pt_to_continuous_simple.
    apply continuity_pt_ext_loc with (f := fun t => exp ((-σ) * ln t)) (g := fun t => Rpower t (-σ)).
    + apply locally_iff_open_ball.
      exists (z/2). split. lra.
      intros t Ht.
      apply Rabs_lt_between' in Ht.
      destruct Ht as [Hlow Hhigh].
      assert (Ht_pos : 0 < t). { lra. }
      unfold Rpower.
      destruct (Rlt_dec 0 t) as [H|H]; [| contradiction].
      reflexivity.
    + apply continuity_pt_comp with (f1 := fun t => (-σ) * ln t) (f2 := exp).
      * apply continuity_pt_scal.
        apply derivable_continuous_pt.
        apply derivable_pt_ln_manual; exact Hz_pos.
      * apply derivable_continuous_pt.
        apply derivable_pt_exp.
  - (* y < 1 *)
    apply ex_RInt_swap.
    apply ex_RInt_continuous with (f := fun t => Rpower t (-σ)) (a := y) (b := 1).
    intros z Hz.
    rewrite Rmin_left, Rmax_right in Hz by lra.
    assert (Hz_pos : 0 < z). { apply Rlt_le_trans with y; [exact Hy_pos | apply Hz]. }
    apply continuity_pt_to_continuous_simple.
    apply continuity_pt_ext_loc with (f := fun t => exp ((-σ) * ln t)) (g := fun t => Rpower t (-σ)).
    + apply locally_iff_open_ball.
      exists (z/2). split. lra.
      intros t Ht.
      apply Rabs_lt_between' in Ht.
      destruct Ht as [Hlow Hhigh].
      assert (Ht_pos : 0 < t). { lra. }
      unfold Rpower.
      destruct (Rlt_dec 0 t) as [H|H]; [| contradiction].
      reflexivity.
    + apply continuity_pt_comp with (f1 := fun t => (-σ) * ln t) (f2 := exp).
      * apply continuity_pt_scal.
        apply derivable_continuous_pt.
        apply derivable_pt_ln_manual; exact Hz_pos.
      * apply derivable_continuous_pt.
        apply derivable_pt_exp.
Qed.

(* 幂函数可积性 *)
Lemma ex_RInt_power (a c d : R) (Hc_pos : 0 < c) (Hd_pos : 0 < d) :
  ex_RInt (fun t => Rpower t a) c d.
Proof.
  apply ex_RInt_continuous with (f := fun t => Rpower t a) (a := c) (b := d).
  intros z Hz.
  assert (Hz_pos : 0 < z).
  { apply Rlt_le_trans with (Rmin c d).
    - apply Rmin_pos; [exact Hc_pos | exact Hd_pos].
    - apply (proj1 Hz). }
  apply continuity_pt_to_continuous_simple.
  set (g := fun t => a * ln t).
  set (h := exp).
  apply continuity_pt_comp with (f1 := g) (f2 := h).
  - apply continuity_pt_scal.
    apply derivable_continuous_pt.
    apply derivable_pt_ln_manual; exact Hz_pos.
  - apply derivable_continuous_pt.
    apply derivable_pt_exp.
Qed.

(* 幂函数积分公式 *)
Lemma RInt_power_general (a c d : R) (Hc_pos : 0 < c) (Hcd : c <= d) (Ha : a <> -1) :
  RInt (fun t => Rpower t a) c d = (Rpower d (a+1) - Rpower c (a+1)) / (a+1).
Proof.
  set (F := fun t => Rpower t (a+1) / (a+1)).
  assert (Hd_pos : 0 < d) by lra.
  assert (Ha1_neq0 : a+1 <> 0) by (intros H; apply Ha; lra).

  assert (Hder : forall t, c <= t <= d -> is_derive F t (Rpower t a)).
  {
    intros t Ht.
    assert (Ht_pos : 0 < t) by lra.
    pose proof (derivable_pt_lim_power t (a+1) Ht_pos) as Hder_G.
    assert (Heq : Rpower t (a+1-1) = Rpower t a) by (f_equal; lra).
    rewrite Heq in Hder_G.
    apply is_derive_Reals in Hder_G.
    apply is_derive_scal with (k := / (a+1)) in Hder_G.
    rewrite <- Rmult_assoc in Hder_G.
    rewrite (Rinv_l (a+1) Ha1_neq0) in Hder_G.
    rewrite Rmult_1_l in Hder_G.
    assert (H_eq : forall x, F x = / (a+1) * Rpower x (a+1)).
    { intros x; unfold F; unfold Rdiv; rewrite Rmult_comm; reflexivity. }
    assert (H_fun_eq : (fun x => / (a+1) * Rpower x (a+1)) = F).
    { extensionality x; symmetry; apply H_eq. }
    rewrite H_fun_eq in Hder_G.
    exact Hder_G.
  }

  assert (Hcont : forall t, c <= t <= d -> continuous (fun t => Rpower t a) t).
  {
    intros t Ht.
    assert (Ht_pos : 0 < t) by lra.
    apply continuity_pt_to_continuous_simple.
    apply continuity_pt_comp with (f1 := fun t => a * ln t) (f2 := exp).
    - apply continuity_pt_scal.
      apply derivable_continuous_pt.
      apply derivable_pt_ln_manual; exact Ht_pos.
    - apply derivable_continuous_pt.
      apply derivable_pt_exp.
  }

  assert (Hex : ex_RInt (fun t => Rpower t a) c d).
  {
    apply (@ex_RInt_continuous R_CompleteNormedModule).
    intros z Hz.
    rewrite (Rmin_left c d Hcd) in Hz.
    rewrite (Rmax_right c d Hcd) in Hz.
    apply Hcont; exact Hz.
  }

  assert (H_int : is_RInt (fun t => Rpower t a) c d (F d - F c)).
  {
    apply is_RInt_derive with (f := F) (df := fun t => Rpower t a) (a := c) (b := d).
    - intros x Hx.
      rewrite (Rmin_left c d Hcd) in Hx.
      rewrite (Rmax_right c d Hcd) in Hx.
      apply Hder; exact Hx.
    - intros x Hx.
      rewrite (Rmin_left c d Hcd) in Hx.
      rewrite (Rmax_right c d Hcd) in Hx.
      apply Hcont; exact Hx.
  }

  rewrite (is_RInt_unique _ _ _ _ H_int).
  unfold F.
  replace (Rpower d (a+1) / (a+1) - Rpower c (a+1) / (a+1))
    with ((Rpower d (a+1) - Rpower c (a+1)) / (a+1)).
  - reflexivity.
  - field; exact Ha1_neq0.
Qed.

(* 倒数函数积分公式 *)
Lemma RInt_power_minus1 (c d : R) (Hc_pos : 0 < c) (Hcd : c <= d) :
  RInt (fun t => / t) c d = ln d - ln c.
Proof.
  set (F := fun t => ln t).
  assert (Hder : forall t, c <= t <= d -> is_derive F t (/ t)).
  {
    intros t Ht.
    apply is_derive_ln.
    lra.
  }
  assert (Hcont : forall t, c <= t <= d -> continuous (fun t => / t) t).
  {
    intros t Ht.
    apply continuity_pt_to_continuous_simple.
    apply continuity_pt_inv.
    - apply derivable_continuous_pt; apply derivable_pt_id.
    - lra.
  }
  assert (Hex : ex_RInt (fun t => / t) c d).
  {
    apply ex_RInt_continuous with (f := fun t => / t) (a := c) (b := d).
    intros z Hz.
    apply Hcont.
    destruct (Rle_dec c d) as [Hle|Hgt]; [|lra].
    rewrite Rmin_left, Rmax_right in Hz by lra.
    assumption.
  }
  assert (H_int : is_RInt (fun t => / t) c d (F d - F c)).
  {
    apply is_RInt_derive with (f := F) (df := fun t => / t) (a := c) (b := d).
    - intros x Hx.
      rewrite Rmin_left, Rmax_right in Hx by lra.
      apply Hder; assumption.
    - intros x Hx.
      rewrite Rmin_left, Rmax_right in Hx by lra.
      apply Hcont; assumption.
  }
  rewrite (is_RInt_unique _ _ _ _ H_int).
  unfold F; simpl.
  reflexivity.
Qed.

(* 指数复合函数的可积性 *)
Lemma ex_RInt_exp_comp (φ : R -> R) (c d : R) (Hc_pos : 0 < c)
  (Hcont_φ : forall t, c <= t <= d -> continuous φ t) :
  c <= d ->
  ex_RInt (fun t => exp (φ t)) c d.
Proof.
  intros Hcd.
  apply ex_RInt_continuous with (f := fun t => exp (φ t)) (a := c) (b := d).
  intros z Hz.
  rewrite Rmin_left, Rmax_right in Hz by auto.
  apply continuous_comp with (f := φ) (g := exp) (x := z).
  - apply Hcont_φ; split; [apply Hz | apply Hz].
  - apply continuous_exp.
Qed.

(* 负幂次广义积分公式 *)
Lemma integral_power_neg (σ : R) (Hσ : 1 < σ) :
  let f := fun t => Rpower t (-σ) in
  exists I : R,
    is_RInt_gen f (at_point 1) (Rbar_locally p_infty) I /\
    I = / (σ - 1).
Proof.
  intros f.
  set (F := fun t => - Rpower t (1 - σ) / (σ - 1)).

  assert (Hder : forall t, 1 <= t -> is_derive F t (f t)).
  {
    intros t Ht.
    destruct (Rle_lt_or_eq _ _ Ht) as [Ht_gt_1 | Ht_eq_1].
    - assert (Ht_pos : 0 < t) by lra.
      pose proof (derivable_pt_lim_power t (1 - σ) Ht_pos) as Hpow.
      simpl in Hpow.
      replace (1 - σ - 1) with (-σ) in Hpow by ring.
      assert (Hscal : derivable_pt_lim (fun x => - / (σ - 1) * Rpower x (1 - σ)) t
                                     (- / (σ - 1) * ((1 - σ) * Rpower t (-σ)))).
      { apply derivable_pt_lim_scal with (a := - / (σ - 1)); exact Hpow. }
      replace (- / (σ - 1) * ((1 - σ) * Rpower t (-σ))) with (Rpower t (-σ)) in Hscal
        by (field; lra).
      apply is_derive_Reals.
      apply (derivable_pt_lim_ext
               (fun x => - / (σ - 1) * Rpower x (1 - σ))
               (fun x => - Rpower x (1 - σ) / (σ - 1))
               t (Rpower t (-σ))).
      + intros x; unfold Rdiv; field; lra.
      + exact Hscal.
    - subst t.
      assert (Ht_pos : 0 < 1) by lra.
      pose proof (derivable_pt_lim_power 1 (1 - σ) Ht_pos) as Hpow.
      replace (1 - σ - 1) with (-σ) in Hpow by ring.
      assert (Hscal : derivable_pt_lim (fun x => - / (σ - 1) * Rpower x (1 - σ)) 1
                                     (- / (σ - 1) * ((1 - σ) * Rpower 1 (-σ)))).
      { apply derivable_pt_lim_scal with (a := - / (σ - 1)); exact Hpow. }
      replace (- / (σ - 1) * ((1 - σ) * Rpower 1 (-σ))) with (Rpower 1 (-σ)) in Hscal
        by (field; lra).
      apply is_derive_Reals.
      apply (derivable_pt_lim_ext
               (fun x => - / (σ - 1) * Rpower x (1 - σ))
               (fun x => - Rpower x (1 - σ) / (σ - 1))
               1 (Rpower 1 (-σ))).
      + intros x; unfold Rdiv; field; lra.
      + exact Hscal.
  }

  assert (Hcont_F : forall t, 1 <= t -> continuous F t).
  {
    intros t Ht.
    specialize (Hder t Ht) as Hder_t.
    apply is_derive_Reals in Hder_t.
    assert (Hder_pt : derivable_pt F t) by (exists (f t); exact Hder_t).
    assert (Hcont_pt : continuity_pt F t) by (apply derivable_continuous_pt, Hder_pt).
    apply continuity_pt_to_continuous_simple; exact Hcont_pt.
  }

  assert (Hcont_f : forall t, 1 <= t -> continuous f t).
  {
    intros t Ht.
    assert (Ht_pos : 0 < t) by (apply Rlt_le_trans with 1; [apply Rlt_0_1 | exact Ht]).
    apply continuity_pt_to_continuous_simple.
    apply continuity_pt_comp with (f1 := fun t => (-σ) * ln t) (f2 := exp).
    - apply continuity_pt_scal.
      apply derivable_continuous_pt, derivable_pt_ln_manual; exact Ht_pos.
    - apply derivable_continuous_pt, derivable_pt_exp.
  }

  assert (Hlim_F_infty : filterlim F (Rbar_locally p_infty) (locally 0)).
  {
    unfold F.
    assert (Hlim_pow : filterlim (fun t => Rpower t (1-σ)) (Rbar_locally p_infty) (locally 0)).
    {
      set (p := σ - 1).
      assert (Hp_pos : 0 < p) by (unfold p; lra).

      assert (Hlim_ln_p : filterlim ln (Rbar_locally p_infty) (Rbar_locally p_infty)).
      {
        intros P [M HM].
        exists (exp M).
        intros t Ht.
        apply HM.
        rewrite <- (ln_exp M).
        apply ln_increasing.
        - apply exp_pos.
        - exact Ht.
      }

      assert (Hlim_mul : filterlim (fun t => -p * ln t) (Rbar_locally p_infty) (Rbar_locally m_infty)).
      {
        apply filterlim_comp with (f := ln) (g := fun y => -p * y)
          (G := Rbar_locally p_infty) (H := Rbar_locally m_infty).
        - exact Hlim_ln_p.
        - intros P [M HM].
          set (M' := - M / p).
          exists M'.
          intros y Hy.
          apply HM.
          unfold M' in Hy.
          apply (Rmult_lt_compat_l p) in Hy; [| exact Hp_pos].
          assert (H_eq : p * (- M / p) = - M) by (field; lra).
          rewrite H_eq in Hy.
          apply Ropp_lt_contravar in Hy.
          rewrite Ropp_mult_distr_l, Ropp_involutive in Hy.
          exact Hy.
      }

      assert (Heq : forall t, -p * ln t = (1-σ) * ln t) by (intros t; unfold p; lra).
      assert (Hlim_mul' : filterlim (fun t => (1-σ) * ln t) (Rbar_locally p_infty) (Rbar_locally m_infty)).
      { apply filterlim_ext with (f := fun t => -p * ln t); [exact Heq | exact Hlim_mul]. }

      apply filterlim_comp with (f := fun t => (1-σ) * ln t) (g := exp)
        (G := Rbar_locally m_infty) (H := locally 0).
      - exact Hlim_mul'.
      - apply filterlim_exp_m_infty.
    }

    set (c := - / (σ - 1)).
    assert (Hc_neq0 : c <> 0).
    { unfold c; apply Rlt_not_eq; rewrite <- Ropp_0; apply Ropp_lt_contravar; apply Rinv_0_lt_compat; lra. }

    assert (Hlim_scaled : filterlim (fun t => c * Rpower t (1-σ)) (Rbar_locally p_infty) (locally 0)).
    {
      apply filterlim_comp with (f := fun t => Rpower t (1-σ)) (g := fun y => c * y)
        (F := Rbar_locally p_infty) (G := locally 0) (H := locally 0).
      - exact Hlim_pow.
      - apply filterlim_scal_zero; auto.
    }

    assert (Heq : forall t, c * Rpower t (1-σ) = F t).
    { intros t; unfold F, c; field; lra. }

    apply filterlim_ext with (f := fun t => c * Rpower t (1-σ)) (g := F).
    - exact Heq.
    - exact Hlim_scaled.
  }

  assert (H_RInt : forall b, 1 < b -> is_RInt f 1 b (F b - F 1)).
  {
    intros b Hb.
    assert (Hcont_f_1b : forall x, 1 <= x <= b -> continuous f x).
    { intros x Hx; apply Hcont_f; lra. }
    assert (Hder_F_1b : forall x, 1 <= x <= b -> is_derive F x (f x)).
    { intros x Hx; apply Hder; lra. }
    apply is_RInt_derive with (f := F) (df := f) (a := 1) (b := b).
    - intros x Hx.
      simpl in Hx.
      rewrite Rmin_left, Rmax_right in Hx by lra.
      apply Hder_F_1b. exact Hx.
    - intros x Hx.
      simpl in Hx.
      rewrite Rmin_left, Rmax_right in Hx by lra.
      apply Hcont_f_1b. exact Hx.
  }

  assert (F1_val : - F 1 = / (σ - 1)).
  {
    unfold F.
    rewrite Rpower_1_r.
    field; lra.
  }

  exists ( / (σ - 1) ).
  split.
  - assert (Hlim_1 : filterlim (fun b => RInt f 1 b) (Rbar_locally p_infty) (locally ( / (σ - 1) ))).
    {
      intros P_goal HP_goal.
      destruct HP_goal as [eps_goal Hball_goal].
      unfold filterlim in Hlim_F_infty.
      specialize (Hlim_F_infty (ball 0 eps_goal) (locally_ball 0 eps_goal)).
      destruct Hlim_F_infty as [A_ex HA_ex].
      set (A_upper := Rmax A_ex 1).
      exists A_upper.
      intros b Hb.
      assert (A_ex < b).
      { apply Rle_lt_trans with A_upper; [apply Rmax_l | exact Hb]. }
      assert (1 < b) as H1_lt_b.
      { apply Rle_lt_trans with A_upper; [apply Rmax_r | exact Hb]. }
      pose proof (H_RInt b H1_lt_b) as His.
      assert (RInt f 1 b = F b - F 1) by (apply (is_RInt_unique f 1 b (F b - F 1) His)).
      apply Hball_goal.
      rewrite H0.
      unfold ball, AbsRing_ball; simpl.
      rewrite <- F1_val.
      unfold AbsRing_ball.
      unfold minus, opp; simpl.
      rewrite Ropp_involutive.
      unfold plus; simpl.
      replace ((F b - F 1) + F 1) with (F b) by ring.
      rewrite <- (Rminus_0_r (F b)).
      apply HA_ex; exact H.
    }
    unfold is_RInt_gen.
    intros P_goal HP_goal.
    destruct HP_goal as [eps_goal Hball_goal].
    specialize (Hlim_1 (ball ( / (σ - 1) ) eps_goal) (locally_ball ( / (σ - 1) ) eps_goal)).
    destruct Hlim_1 as [A_upper HA_upper].
    set (A_upper' := Rmax A_upper 1).
    set (Q_left := fun x => x = 1).
    set (Q_right := fun y => y > A_upper').
    assert (HQ_left : at_point 1 Q_left) by (unfold at_point; reflexivity).
    assert (HQ_right : Rbar_locally p_infty Q_right) by (unfold Rbar_locally; exists A_upper'; intros; auto).
    apply Filter_prod with (Q := Q_left) (R := Q_right); [exact HQ_left | exact HQ_right |].
    intros x y Hx Hy.
    rewrite Hx; simpl.
    assert (y > A_upper') as Hy' by exact Hy.
    assert (H1_lt_y : 1 < y) by (apply Rle_lt_trans with A_upper'; [apply Rmax_r | exact Hy']).
    pose proof (H_RInt y H1_lt_y) as His.
    exists (F y - F 1). split.
    + exact His.
    + apply Hball_goal.
      rewrite <- (is_RInt_unique f 1 y (F y - F 1) His).
      apply HA_upper.
      apply Rle_lt_trans with A_upper'.
      * apply Rmax_l.
      * exact Hy'.
  - reflexivity.
Qed.

(* 积分判别法 *)
Lemma integral_test (f : R -> R) (σ : R) :
  (forall t, 1 <= t -> 0 <= f t) ->
  (forall x y, 1 <= x <= y -> f x >= f y) ->
  (forall t, 1 <= t -> continuous f t) ->
  ex_RInt_gen f (at_point 1) (Rbar_locally p_infty) ->
  exists l : R, Un_cv (fun N => sum_f_R0 (fun n => f (INR (S n))) N) l.
Proof.
  intros Hnonneg Hdec Hcont [I H_is].
  set (g := fun N => sum_f_R0 (fun n => f (INR (S n))) N).

  assert (Hmono : forall N, g N <= g (S N)).
  { intros N; unfold g; rewrite sum_f_R0_S.
    apply Rle_self_plus.
    apply Hnonneg.
    apply le_INR with (n:=1%nat) (m:=S (S N)); simpl; lia. }

  assert (RInt_incr : forall a b, 1 <= a <= b -> RInt f 1 a <= RInt f 1 b).
  {
    intros a b [Ha Hab].
    assert (Hex1 : ex_RInt f 1 a).
    { apply ex_RInt_continuous with (f := f) (a := 1) (b := a).
      intros z Hz.
      destruct Hz as [Hz1 Hz2].
      assert (Hmin_eq : Rmin 1 a = 1) by (apply Rmin_left; lra).
      assert (Hmax_eq : Rmax 1 a = a) by (apply Rmax_right; lra).
      rewrite Hmin_eq in Hz1. rewrite Hmax_eq in Hz2.
      apply Hcont; exact Hz1. }
    assert (Hex2 : ex_RInt f a b).
    { apply ex_RInt_continuous with (f := f) (a := a) (b := b).
      intros z Hz.
      destruct Hz as [Hz1 Hz2].
      assert (Hmin_eq : Rmin a b = a) by (apply Rmin_left; lra).
      assert (Hmax_eq : Rmax a b = b) by (apply Rmax_right; lra).
      rewrite Hmin_eq in Hz1. rewrite Hmax_eq in Hz2.
      apply Hcont.
      apply Rle_trans with a; [exact Ha | exact Hz1]. }
    assert (Hex3 : ex_RInt f 1 b).
    { apply ex_RInt_continuous with (f := f) (a := 1) (b := b).
      intros z Hz.
      destruct Hz as [Hz1 Hz2].
      assert (Hmin_eq : Rmin 1 b = 1) by (apply Rmin_left; lra).
      assert (Hmax_eq : Rmax 1 b = b) by (apply Rmax_right; lra).
      rewrite Hmin_eq in Hz1. rewrite Hmax_eq in Hz2.
      apply Hcont; exact Hz1. }
    assert (Heq : RInt f 1 b = RInt f 1 a + RInt f a b).
    { rewrite <- (RInt_Chasles f 1 a b Hex1 Hex2); reflexivity. }
    rewrite Heq.
    apply Rle_self_plus.
    apply RInt_ge_0; [lra | exact Hex2 | intros t Ht; apply Hnonneg; lra].
  }

  assert (Hlim : filterlim (fun b => RInt f 1 b) (Rbar_locally p_infty) (locally I)).
  {
    intros P HP.
    destruct HP as [eps Hball].
    set (Q := fun y => ball I eps y).
    assert (HQ : locally I Q) by (exists (mkposreal eps (cond_pos eps)); intros; auto).
    destruct (H_is Q HQ) as [Q1 Q2 HQ1 HQ2 Hmain].
    assert (Q1_1 : Q1 1). { exact HQ1. }
    destruct HQ2 as [M HM].
    exists M.
    intros y Hy.
    specialize (Hmain 1 y Q1_1 (HM y Hy)).
    destruct Hmain as [z [Hz Hball']].
    assert (Hex : ex_RInt f 1 y) by (exists z; exact Hz).
    pose proof (RInt_correct f 1 y Hex) as Hr.
    assert (Hz' : is_RInt f 1 y z) by (simpl in Hz; exact Hz).
    assert (Heq : z = RInt f 1 y).
    { symmetry. apply (is_RInt_unique f 1 y z Hz'). }
    rewrite Heq in Hball'.
    apply Hball.
    exact Hball'.
  }

  assert (Hineq : forall n, (1 <= n)%nat -> f (INR (S n)) <= RInt f (INR n) (INR (S n))).
  {
    intros n Hn.
    set (a := INR n). set (b := INR (S n)).
    assert (Hle : a <= b) by (apply le_INR; lia).

    assert (Hex_f : ex_RInt f a b).
    {
      apply ex_RInt_continuous with (f := f) (a := a) (b := b).
      intros z Hz.
      destruct Hz as [Hz1 Hz2].
      rewrite (Rmin_left a b Hle) in Hz1.
      rewrite (Rmax_right a b Hle) in Hz2.
      apply Hcont.
      assert (Hge1 : INR 1 <= a) by (apply le_INR; exact Hn).
      apply Rle_trans with a; [exact Hge1 | exact Hz1].
    }

    assert (Hex_const : ex_RInt (fun _ => f b) a b) by apply ex_RInt_const.
    assert (H_le_const : RInt (fun _ => f b) a b <= RInt f a b).
    {
      apply RInt_le; [lra | exact Hex_const | exact Hex_f | ].
      intros t Ht.
      assert (Hab : a <= t <= b) by (split; [apply Rlt_le; apply Ht | apply Rlt_le; apply Ht]).
      assert (H1 : 1 <= a) by (rewrite <- INR_1; apply le_INR; exact Hn).
      assert (Ht_ge_1 : 1 <= t) by (apply Rle_trans with a; [exact H1 | apply Hab]).
      apply Rge_le.
      apply Hdec; split; [exact Ht_ge_1 | apply Hab].
    }

    rewrite RInt_const in H_le_const.
    unfold scal in H_le_const.
    assert (Hb_minus_a_eq_1 : b - a = 1) by (unfold b, a; rewrite S_INR; ring).
    rewrite Hb_minus_a_eq_1 in H_le_const.
    rewrite Rmult_1_l in H_le_const.
    exact H_le_const.
  }

  assert (Hsum : forall N, g N <= RInt f 1 (INR (S N)) + f 1).
  {
    induction N as [|N IH].
    - simpl; rewrite RInt_point; rewrite Rplus_0_l; unfold g; simpl; apply Rle_refl.
    - unfold g at 1; rewrite sum_f_R0_S.
      set (sN := sum_f_R0 (fun n => f (INR (S n))) N).
      set (term := f (INR (S (S N)))).

      assert (Hex1 : ex_RInt f 1 (INR (S N))).
      { apply ex_RInt_continuous with (f := f) (a := 1) (b := INR (S N)).
        intros z Hz.
        assert (Hle : 1 <= INR (S N)) by (rewrite <- INR_1; apply le_INR; lia).
        rewrite (Rmin_left 1 (INR (S N)) Hle) in Hz.
        rewrite (Rmax_right 1 (INR (S N)) Hle) in Hz.
        destruct Hz as [Hz1 Hz2]; apply Hcont; exact Hz1. }

      assert (Hex2 : ex_RInt f (INR (S N)) (INR (S (S N)))).
      { apply ex_RInt_continuous with (f := f) (a := INR (S N)) (b := INR (S (S N))).
        intros z Hz.
        assert (Hle : INR (S N) <= INR (S (S N))) by (apply le_INR; lia).
        rewrite (Rmin_left (INR (S N)) (INR (S (S N))) Hle) in Hz.
        rewrite (Rmax_right (INR (S N)) (INR (S (S N))) Hle) in Hz.
        destruct Hz as [Hz1 Hz2].
        assert (H1 : 1 <= INR (S N)) by (rewrite <- INR_1; apply le_INR; lia).
        apply Hcont; apply Rle_trans with (INR (S N)); [exact H1 | exact Hz1]. }

      rewrite <- (RInt_Chasles f 1 (INR (S N)) (INR (S (S N))) Hex1 Hex2).

      assert (Hterm : term <= RInt f (INR (S N)) (INR (S (S N)))).
      { apply Hineq; lia. }

      apply Rle_trans with ((RInt f 1 (INR (S N)) + f 1) + RInt f (INR (S N)) (INR (S (S N)))).
      - apply Rplus_le_compat; [exact IH | exact Hterm].
      - replace ((RInt f 1 (INR (S N)) + f 1) + RInt f (INR (S N)) (INR (S (S N))))
           with ((RInt f 1 (INR (S N)) + RInt f (INR (S N)) (INR (S (S N)))) + f 1) by ring.
        apply Rle_refl.
  }

  assert (Hbounded : forall b, 1 <= b -> RInt f 1 b <= I).
  {
    intros b Hb.
    apply Rnot_lt_le; intros Hgt.
    set (delta := RInt f 1 b - I).
    assert (Hdelta_pos : 0 < delta) by (apply Rlt_0_minus; exact Hgt).

    assert (Hloc : locally I (fun y => Rabs (y - I) < delta/2)).
    { exists (mkposreal (delta/2) (Rdiv_lt_0_compat delta 2 Hdelta_pos Rlt_0_2)).
      intros y Hy; exact Hy. }
    destruct (Hlim (fun y => Rabs (y - I) < delta/2) Hloc) as [M HM].

    set (b' := Rmax (b + 1) (M + 1)).
    assert (Hb'_ge_M1 : M+1 <= b') by apply Rmax_r.
    assert (Hb'_ge_b1 : b+1 <= b') by apply Rmax_l.
    assert (Hb'_gt_M : M < b') by lra.
    assert (Hb'_ge_b : b <= b') by lra.
    specialize (HM b' Hb'_gt_M).

    assert (H_mono : RInt f 1 b <= RInt f 1 b').
    { apply RInt_incr; split; [exact Hb | exact Hb'_ge_b]. }

    apply Rabs_lt_between' in HM.
    destruct HM as [Hleft Hright].

    assert (Heq : I + delta = RInt f 1 b) by (unfold delta; ring).

    assert (I + delta <= RInt f 1 b') by (rewrite Heq; exact H_mono).
    assert (I + delta < I + delta/2) by (apply Rle_lt_trans with (RInt f 1 b'); [exact H | exact Hright]).
    apply (Rlt_irrefl (I + delta)); apply Rlt_le_trans with (I + delta/2); [exact H0 | lra].
  }

  assert (Hbounded_series : forall N, g N <= I + f 1).
  {
    intros N. apply Rle_trans with (RInt f 1 (INR (S N)) + f 1).
    - apply Hsum.
    - apply Rplus_le_compat_r.
      apply Hbounded.
      rewrite <- INR_1.
      apply le_INR.
      lia.
  }

  assert (Hmono_inc : forall n m, (n <= m)%nat -> g n <= g m).
  {
    intros n m Hle.
    induction Hle as [| m' Hle' IH].
    - apply Rle_refl.
    - apply Rle_trans with (g m'); [exact IH | apply Hmono].
  }

  set (S := fun x : R => exists N : nat, x = g N).

  assert (S_ub : exists M, forall x, S x -> x <= M).
  { exists (I + f 1). intros x [N ->]. apply Hbounded_series. }

  assert (S_nonempty : exists x, S x).
  { exists (g 0%nat). exists 0%nat. reflexivity. }

  destruct (completeness S S_ub S_nonempty) as [l Hl].
  destruct Hl as [Hl_ub Hl_least].

  exists l.
  intros eps Heps.
  assert (exists N0, l - eps < g N0).
  {
    destruct (classic (exists N, l - eps < g N)) as [H|H].
    - destruct H as [N H]; exists N; exact H.
    - assert (H_ub : forall x, S x -> x <= l - eps).
      { intros x [N ->]; apply Rnot_lt_le; intro Hlt; apply H; exists N; exact Hlt. }
      apply Hl_least in H_ub.
      lra.
  }
  destruct H as [N0 Hlt].
  exists N0.
  intros n Hn.
  assert (H1 : g N0 <= g n) by (apply Hmono_inc; lia).
  assert (H2 : g n <= l) by (apply Hl_ub; exists n; reflexivity).

  assert (Hge0 : 0 <= l - g n).
  { apply Rplus_le_compat_r with (r := -g n) in H2.
    rewrite Rplus_opp_r in H2.
    exact H2. }
  unfold Rdist; simpl.
  rewrite Rabs_minus_sym.
  rewrite (Rabs_pos_eq (l - g n) Hge0).
  lra.
Qed.

(* 幂级数收敛性 *)

(* 比较判别法 *)
Lemma comparison_test (a b : nat -> R) :
  (forall n, 0 <= a n <= b n) ->
  (exists l : R, Un_cv (fun N => sum_f_R0 b N) l) ->
  exists l : R, Un_cv (fun N => sum_f_R0 a N) l.
Proof.
  intros Hle [lb Hlb].
  set (A := fun N => sum_f_R0 a N).
  set (B := fun N => sum_f_R0 b N).

  assert (Hmono_A : forall N, A N <= A (S N)).
  { intros N; unfold A; rewrite sum_f_R0_S.
    apply Rle_self_plus; apply (proj1 (Hle (S N))). }

  assert (Hmono_B : forall N, B N <= B (S N)).
  { intros N; unfold B; rewrite sum_f_R0_S.
    assert (Hb_nonneg : 0 <= b (S N)).
    { apply Rle_trans with (a (S N)); [apply (proj1 (Hle (S N))) | apply (proj2 (Hle (S N)))]. }
    apply Rle_self_plus; exact Hb_nonneg. }

  assert (HAB : forall N, A N <= B N).
  {
    induction N.
    - simpl; destruct (Hle 0%nat) as [_ H0]; exact H0.
    - simpl; apply Rplus_le_compat; [exact IHN | apply (proj2 (Hle (S N)))].
  }

  assert (Hmono_B_incr : forall i j, (i <= j)%nat -> B i <= B j).
  {
    intros i j H; induction H as [| m Hle1 IH].
    - apply Rle_refl.
    - apply Rle_trans with (B m); [exact IH | apply Hmono_B].
  }

  assert (Hbound_B : forall N, B N <= lb).
  {
    intros N.
    destruct (classic (lb < B N)) as [Hlt | Hle1].
    - set (eps := (B N - lb) / 2).
      assert (Heps : eps > 0) by (unfold eps; lra).
      destruct (Hlb eps Heps) as [N0 HN0].
      set (M := max N N0).
      assert (Hge : B N <= B M) by (apply Hmono_B_incr; lia).
      assert (Habs : Rabs (B M - lb) < eps) by (apply HN0; lia).
      apply Rabs_lt_between' in Habs; destruct Habs as [Hlow Hhigh].
      assert (Hcontra : B N < lb + eps) by (apply Rle_lt_trans with (B M); auto).
      exfalso; unfold eps in Hcontra; lra.
    - apply Rnot_lt_le in Hle1; exact Hle1.
  }

  assert (Hbound_A : forall N, A N <= lb).
  { intros N; apply Rle_trans with (B N); [apply HAB | apply Hbound_B]. }

  assert (Hmono_A_incr : forall i j, (i <= j)%nat -> A i <= A j).
  {
    intros i j H; induction H as [| m Hle1 IH].
    - apply Rle_refl.
    - apply Rle_trans with (A m); [exact IH | apply Hmono_A].
  }

  set (E := fun x => exists N, x = A N).
  assert (E_nonempty : exists x, E x) by (exists (A 0%nat); exists 0%nat; reflexivity).
  assert (E_bound : bound E).
  { exists lb; intros x [N ->]; apply Hbound_A. }
  destruct (completeness E E_bound E_nonempty) as [l Hl].
  destruct Hl as [Hl_ub Hl_least].

  exists l.
  unfold Un_cv.
  intros eps Heps.

  assert (exists N0, A N0 > l - eps).
  {
    destruct (classic (exists N0, A N0 > l - eps)) as [H0|H0]; auto.
    exfalso.
    assert (H_all : forall N, A N <= l - eps).
    { intros N. apply Rnot_gt_le. intros Hgt; apply H0; exists N; exact Hgt. }
    assert (H_ub : is_upper_bound E (l - eps)).
    { intros x [M ->]; apply H_all. }
    apply Hl_least in H_ub.
    lra.
  }
  destruct H as [N0 HN0].

  exists N0.
  intros n Hn.
  assert (Hle_n : (N0 <= n)%nat) by lia.
  assert (H_ge : A N0 <= A n) by (apply Hmono_A_incr; exact Hle_n).
  assert (H_le : A n <= l) by (apply Hl_ub; exists n; reflexivity).

  unfold Rdist.
  rewrite Rabs_minus_sym.
  rewrite Rabs_pos_eq; [| lra].
  apply Rle_lt_trans with (l - A N0).
  - apply Rplus_le_compat_l, Ropp_le_contravar, H_ge.
  - lra.
Qed.

(* 绝对收敛蕴涵收敛 *)
Lemma abs_conv_implies_conv (a : nat -> R) :
  (exists l : R, Un_cv (fun N => sum_f_R0 (fun n => Rabs (a n)) N) l) ->
  exists l : R, Un_cv (fun N => sum_f_R0 a N) l.
Proof.
  intros [l_abs H_abs].
  assert (Hcauchy_abs : Cauchy_crit_series (fun n => Rabs (a n))).
  {
    intros eps Heps.
    destruct (H_abs (eps/2) (Rdiv_lt_0_compat eps 2 Heps Rlt_0_2)) as [N HN].
    exists N.
    intros n m Hn Hm.
    set (S n := sum_f_R0 (fun k => Rabs (a k)) n).
    unfold Rdist.
    replace (S n - S m) with ((S n - l_abs) - (S m - l_abs)) by ring.
    apply Rle_lt_trans with (Rabs (S n - l_abs) + Rabs (S m - l_abs)).
    - apply Rabs_triang_sub.
    - apply Rlt_le_trans with (eps/2 + eps/2).
      + apply Rplus_lt_compat; [apply HN; assumption | apply HN; assumption].
      + lra.
  }
  assert (Hcauchy : Cauchy_crit_series a).
  { apply (abs_comparison_cauchy a (fun n => Rabs (a n))).
    - intros n; apply Rle_refl.
    - exact Hcauchy_abs. }
  destruct (cv_cauchy_2 a Hcauchy) as [l Hl].
  exists l; exact Hl.
Qed.

Import FourierAnalysis.

(* 复数部分和实部公式 *)
Lemma re_Csum_eq : forall (u : nat -> Complex) (N : nat),
  re (Csum u (S N)) = sum_f_R0 (fun n => re (u n)) N.
Proof.
  induction N as [|N IH].
  - simpl; ring.
  - simpl.
    rewrite Rplus_comm.
    rewrite (Rplus_comm (re (u N)) (re (Csum u N))).
    rewrite <- (re_Cadd (Csum u N) (u N)).
    rewrite (Cadd_comm (Csum u N) (u N)).
    assert (H : Csum u (S N) = u N +c Csum u N) by (simpl; reflexivity).
    rewrite <- H.
    rewrite IH.
    reflexivity.
Qed.

(* 复数部分和虚部公式 *)
Lemma im_Csum_SN_eq : forall (u : nat -> Complex) (N : nat),
  im (Csum u (S N)) = sum_f_R0 (fun n => im (u n)) N.
Proof.
  induction N as [|N IH].
  - simpl; ring.
  - simpl.
    rewrite Rplus_comm.
    rewrite (Rplus_comm (im (u N)) (im (Csum u N))).
    rewrite <- (im_Cadd (Csum u N) (u N)).
    rewrite (Cadd_comm (Csum u N) (u N)).
    assert (H : Csum u (S N) = u N +c Csum u N) by (simpl; reflexivity).
    rewrite <- H.
    rewrite IH.
    reflexivity.
Qed.

(* ζ级数部分和虚部公式 *)
Lemma im_zeta_series_Csum_eq (s : Complex) (N : nat) :
  im (Csum (zeta_series_term s) N) =
    match N with
    | 0 => 0
    | S N' => sum_f_R0 (fun n => im (zeta_series_term s n)) N'
    end.
Proof.
  induction N as [|N IH].
  - reflexivity.
  - simpl. rewrite IH.
    destruct N as [|N'].
    + simpl. ring.
    + simpl. ring.
Qed.

(* 复数绝对收敛蕴涵收敛 *)
Lemma complex_abs_conv_implies_conv (u : nat -> Complex) :
  (exists l_re : R, Un_cv (fun N => sum_f_R0 (fun n => Rabs (re (u n))) N) l_re) ->
  (exists l_im : R, Un_cv (fun N => sum_f_R0 (fun n => Rabs (im (u n))) N) l_im) ->
  exists l : Complex, Cseq_limit (fun N => Csum u N) l.
Proof.
  intros [l_re H_re_abs] [l_im H_im_abs].
  set (a := fun n => re (u n)).
  set (b := fun n => im (u n)).
  assert (Ha_abs : exists l, Un_cv (fun N => sum_f_R0 (fun n => Rabs (a n)) N) l) by (exists l_re; exact H_re_abs).
  assert (Hb_abs : exists l, Un_cv (fun N => sum_f_R0 (fun n => Rabs (b n)) N) l) by (exists l_im; exact H_im_abs).

  destruct (abs_conv_implies_conv a Ha_abs) as [l_re_cv H_re_cv].
  destruct (abs_conv_implies_conv b Hb_abs) as [l_im_cv H_im_cv].

  assert (H_re_cv' : Un_cv (fun N => re (Csum u (S N))) l_re_cv).
  {
    intros eps Heps.
    destruct (H_re_cv eps Heps) as [N0 HN0].
    exists N0; intros n Hn.
    rewrite (re_Csum_eq u n).
    apply HN0; assumption.
  }
  assert (H_im_cv' : Un_cv (fun N => im (Csum u (S N))) l_im_cv).
  {
    intros eps Heps.
    destruct (H_im_cv eps Heps) as [N0 HN0].
    exists N0; intros n Hn.
    rewrite (im_Csum_SN_eq u n).
    apply HN0; assumption.
  }

  assert (H_re_cv_final : Un_cv (fun N => re (Csum u N)) l_re_cv).
  {
    intros eps Heps.
    destruct (H_re_cv eps Heps) as [N0 HN0].
    exists (S N0).
    intros n Hn.
    assert (Hn' : (pred n >= N0)%nat) by lia.
    assert (n_eq : n = S (pred n)) by lia.
    rewrite n_eq.
    rewrite (re_Csum_eq u (pred n)).
    apply HN0; assumption.
  }
  assert (H_im_cv_final : Un_cv (fun N => im (Csum u N)) l_im_cv).
  {
    intros eps Heps.
    destruct (H_im_cv eps Heps) as [N0 HN0].
    exists (S N0).
    intros n Hn.
    assert (Hn' : (pred n >= N0)%nat) by lia.
    assert (n_eq : n = S (pred n)) by lia.
    rewrite n_eq.
    rewrite (im_Csum_SN_eq u (pred n)).
    apply HN0; assumption.
  }

  exists (l_re_cv +i l_im_cv).
  apply Cseq_limit_from_components; [exact H_re_cv_final | exact H_im_cv_final].
Qed.

(* 交错级数收敛（狄利克雷判别法） *)
Lemma alternating_series_converges (a : nat -> R) :
  (forall n, 0 <= a n) ->
  (forall n, a (S n) <= a n) ->
  (Un_cv a 0) ->
  exists l : R, Un_cv (fun N => sum_f_R0 (fun n => (-1)^n * a n) N) l.
Proof.
  intros Hnonneg Hdec Hlim.
  destruct (CV_ALT a Hdec Hnonneg Hlim) as [l Hcv].
  exists l; exact Hcv.
Qed.

End GammaIntegralConverges.

Export GammaIntegralConverges.

(* ============================================================
   新模块 GammaIntegrandComplex（2026-08-15 追加）
   配合 gamma_integrand 修复：真复被积函数 t^{s-1}·e^{-t} 的性质。
   - gamma_integrand_re_eq / im_eq：实部/虚部公式（e^{-t}·t^{σ-1}·cos/sin(τ·ln t)）
   - gamma_integrand_norm：模 = e^{-t}·t^{σ-1}（不再有伪 sqrt(1+(τ ln t)²) 因子）
   - gamma_integrand_re_abs_bound：|Re| ≤ 实数 Γ 被积函数
   - gamma_integral_abs_converges：Re(s) > 1 时 ∫₀^∞ |Re(t^{s-1}e^{-t})| 收敛（绝对收敛）
   注：本模块依赖 GammaIntegralConverges 中"实数 Γ 被积函数 e^{-t}·t^{σ-1} 可积"
   的既有证明（gamma_integral_converges / f_integrable_01 / f_integrable_inf /
   RInt_gen_monotone_convergence / RInt_gen_comparison_test）。
   ============================================================ *)
Module GammaIntegrandComplex.

Require Import Coquelicot.Coquelicot.
Import ComplexNumbers.
Import PrimeEmbedding.
Import TrigonometricLemmas.
Import GammaIntegralConverges.
Local Open Scope R_scope.
Local Open Scope complex_scope.

(* |cos x| <= 1（Stdlib 无现成引理，就地证明） *)
Lemma Rabs_cos_le_1_l : forall x : R, Rabs (cos x) <= 1.
Proof.
  intro x.
  rewrite <- sqrt_Rsqr_abs.
  rewrite <- sqrt_1.
  apply sqrt_le_1_c.
  - apply Rle_0_sqr.
  - lra.
  - apply Rle_trans with ((cos x)² + (sin x)²).
    + apply Rle_self_plus; apply Rle_0_sqr.
    + rewrite cos2_sin2; lra.
Qed.

(* Rabs 的连续性（Stdlib 无现成引理，就地证明） *)
Lemma continuity_pt_Rabs_l (x : R) : continuity_pt Rabs x.
Proof.
  intros eps Heps.
  exists eps; split; [exact Heps |].
  intros y Hy.
  destruct Hy as [_ Hy_ball].
  apply Rle_lt_trans with (Rabs (y - x)).
  - simpl. apply Rabs_triang_inv2.
  - unfold Rdist in Hy_ball; exact Hy_ball.
Qed.

(* 实部公式 *)
Lemma gamma_integrand_re_eq (s : Complex) (t : R) (Ht : 0 < t) :
  re (gamma_integrand s t Ht) =
  exp (-t) * real_pow t (re s - 1) Ht * cos (im s * ln t).
Proof.
  unfold gamma_integrand; simpl; unfold real_pow; reflexivity.
Qed.

(* 虚部公式 *)
Lemma gamma_integrand_im_eq (s : Complex) (t : R) (Ht : 0 < t) :
  im (gamma_integrand s t Ht) =
  exp (-t) * real_pow t (re s - 1) Ht * sin (im s * ln t).
Proof.
  unfold gamma_integrand; simpl; unfold real_pow; reflexivity.
Qed.

(* 模公式：|t^{s-1}·e^{-t}| = e^{-t}·t^{σ-1} *)
Lemma gamma_integrand_norm (s : Complex) (t : R) (Ht : 0 < t) :
  Cnorm (gamma_integrand s t Ht) = exp (-t) * Rpower t (re s - 1).
Proof.
  unfold gamma_integrand, Cnorm, Cnorm_sq; simpl.
  set (A := exp (-t) * real_pow t (re s - 1) Ht).
  rewrite !Rsqr_mult.
  rewrite <- Rmult_plus_distr_l.
  replace (Rsqr (cos (im s * ln t)) + Rsqr (sin (im s * ln t))) with 1.
  - rewrite Rmult_1_r.
    rewrite sqrt_Rsqr_abs.
    rewrite Rabs_pos_eq; [| apply Rlt_le; apply Rmult_lt_0_compat; apply exp_pos].
    unfold A.
    unfold real_pow.
    unfold Rpower.
    reflexivity.
  - rewrite cos2_sin2; reflexivity.
Qed.

(* |实部| <= 实数 Γ 被积函数 *)
Lemma gamma_integrand_re_abs_bound (s : Complex) (t : R) (Ht : 0 < t) :
  Rabs (re (gamma_integrand s t Ht)) <= gamma_integrand_real s t Ht.
Proof.
  rewrite gamma_integrand_re_eq.
  unfold gamma_integrand_real.
  rewrite Rabs_mult, Rabs_mult.
  rewrite (Rabs_pos_eq (exp (-t))) by (apply Rlt_le, exp_pos).
  rewrite (Rabs_pos_eq (real_pow t (re s - 1) Ht)) by (unfold real_pow; apply Rlt_le, exp_pos).
  unfold real_pow, Rpower.
  rewrite <- (Rmult_1_r (exp (-t) * exp ((re s - 1) * ln t))) at 2.
  apply Rmult_le_compat_l; [apply Rmult_le_pos; [apply Rlt_le, exp_pos | apply Rlt_le, exp_pos] |].
  exact (Rabs_cos_le_1_l (im s * ln t)).
Qed.

(* |Re(t^{s-1}·e^{-t})| 在正半轴连续（局部等于连续函数；需 re s > 1 以保证 t^{σ-1} 连续） *)
Lemma gamma_integrand_re_abs_continuous (s : Complex) (Hre : 1 < re s) (t : R) (Ht : 0 < t) :
  continuity_pt
    (fun t0 : R => match Rlt_dec 0 t0 with
                   | left H => Rabs (re (gamma_integrand s t0 H))
                   | right _ => 0 end) t.
Proof.
  set (f_abs := fun t0 : R => match Rlt_dec 0 t0 with
                             | left H => Rabs (re (gamma_integrand s t0 H))
                             | right _ => 0 end).
  set (g := fun t0 : R => exp (-t0) * Rpower t0 (re s - 1) * Rabs (cos (im s * ln t0))).
  assert (Hloc_eq : locally t (fun u => f_abs u = g u)).
  {
    apply locally_iff_open_ball.
    exists (t/2); split; [lra |].
    intros u Hu.
    assert (Hu_pos : 0 < u) by (apply Rabs_lt_between in Hu; lra).
    unfold f_abs; destruct (Rlt_dec 0 u) as [Hpos | Hneg]; [| lra].
    rewrite (proof_irrelevance _ Hpos Hu_pos).
    unfold g.
    rewrite gamma_integrand_re_eq.
    rewrite Rabs_mult, Rabs_mult.
    rewrite (Rabs_pos_eq (exp (-u))) by (apply Rlt_le, exp_pos).
    rewrite (Rabs_pos_eq (real_pow u (re s - 1) Hu_pos)) by (unfold real_pow; apply Rlt_le, exp_pos).
    unfold real_pow.
    unfold Rpower.
    reflexivity.
  }
  assert (Hcont_g : continuity_pt g t).
  {
    unfold g.
    apply continuity_pt_mult.
    - apply continuity_pt_mult.
      + apply continuity_pt_comp with (f1 := fun t0 => -t0) (f2 := exp).
        * apply continuity_pt_opp; apply continuity_pt_id.
        * apply derivable_continuous_pt; apply derivable_pt_exp.
      + apply continuity_pt_Rpower_pos; [lra | exact Ht].
    - (* 第三个因子: Rabs (cos (im s * ln t0)) = (Rabs ∘ cos ∘ (im s · ln)) *)
      apply continuity_pt_comp with (f1 := fun t0 : R => cos (im s * ln t0)) (f2 := Rabs).
      + apply continuity_pt_comp with (f1 := fun t0 : R => im s * ln t0) (f2 := cos).
        * apply continuity_pt_scal.
          apply derivable_continuous_pt.
          apply derivable_pt_ln_manual; exact Ht.
        * apply derivable_continuous_pt; apply derivable_pt_cos.
      + apply continuity_pt_Rabs_l.
  }
  (* 直接 ε-δ：f_abs 与 g 局部相等，连续性由 g 传递 *)
  intros eps Heps.
  destruct (Hcont_g eps Heps) as [alp [Halp_pos Halp]].
  apply locally_iff_open_ball in Hloc_eq.
  destruct Hloc_eq as [delta [Hdelta_pos Hdelta]].
  exists (Rmin alp delta); split; [apply Rmin_pos; [exact Halp_pos | exact Hdelta_pos] |].
  intros y Hy.
  destruct Hy as [Hy_dom Hy_ball].
  simpl in Hy_ball.
  assert (Hy_lt_alp : Rabs (y - t) < alp) by (apply Rlt_le_trans with (Rmin alp delta); [exact Hy_ball | apply Rmin_l]).
  assert (Hy_lt_delta : Rabs (y - t) < delta) by (apply Rlt_le_trans with (Rmin alp delta); [exact Hy_ball | apply Rmin_r]).
  specialize (Halp y (conj Hy_dom Hy_lt_alp)) as Hg_ball.
  specialize (Hdelta y Hy_lt_delta) as Heq.
  assert (Ht_lt_delta : Rabs (t - t) < delta).
  { rewrite Rminus_diag, Rabs_R0; exact Hdelta_pos. }
  specialize (Hdelta t Ht_lt_delta) as Hteq.
  rewrite Heq, Hteq.
  exact Hg_ball.
Qed.

(* 被积函数绝对值的连续性（Coquelicot 形式） *)
Lemma f_abs_continuous (s : Complex) (Hre : 1 < re s) (t : R) (Ht : 0 < t) :
  continuous
    (fun t0 : R => match Rlt_dec 0 t0 with
                   | left H => Rabs (re (gamma_integrand s t0 H))
                   | right _ => 0 end) t.
Proof.
  apply continuity_pt_to_continuous_simple.
  apply gamma_integrand_re_abs_continuous; [exact Hre | exact Ht].
Qed.

(* 主定理：Re(s) > 1 时 ∫₀^∞ |Re(t^{s-1}·e^{-t})| dt 绝对收敛 *)
Theorem gamma_integral_abs_converges (s : Complex) (Hre : 1 < re s) :
  ex_RInt_gen (fun t => match Rlt_dec 0 t with
                        | left H => Rabs (re (gamma_integrand s t H))
                        | right _ => 0 end)
              (at_right 0) (Rbar_locally p_infty).
Proof.
  set (f_abs := fun t : R => match Rlt_dec 0 t with
                            | left H => Rabs (re (gamma_integrand s t H))
                            | right _ => 0 end).
  set (g := fun t : R => match Rlt_dec 0 t with
                        | left H => gamma_integrand_real s t H
                        | right _ => 0 end).

  (* --- 连续性事实 --- *)
  assert (Hcont_f_abs : forall t, 0 < t -> continuous f_abs t).
  { intros t Ht; apply f_abs_continuous; [exact Hre | exact Ht]. }
  assert (Hcont_g : forall t, 0 < t -> continuous g t).
  { intros t Ht; unfold g.
    apply continuity_pt_to_continuous_simple.
    apply (f_continuous_positive s t Ht). }

  (* --- (0,1] 段：单调收敛 --- *)
  destruct (f_integrable_01 s Hre) as [I01 H_is01].
  assert (Hlim_g0 : filterlim (fun u => RInt g u 1) (at_right 0) (locally I01)).
  {
    apply RInt_gen_limit_at_right_0 with (f := g).
    - intros t Ht.
      destruct Ht as [Ht_pos Ht_le1].
      apply Hcont_g; exact Ht_pos.
    - exact H_is01.
  }
  assert (H_bounded : exists M : R, forall u : R, 0 < u < 1 -> RInt f_abs u 1 <= M).
  {
    specialize (Hlim_g0 (fun y : R => Rabs (y - I01) < 1)) as HA0.
    assert (Hloc1 : locally I01 (fun y : R => Rabs (y - I01) < 1)).
    { exists (mkposreal 1 Rlt_0_1). intros y Hy. unfold ball in Hy; simpl in Hy.
      exact Hy. }
    specialize (HA0 Hloc1) as H_A0.
    destruct H_A0 as [delta Hdelta].
    set (delta0 := Rmin delta (1/2)).
    assert (Hdelta0_pos : 0 < delta0) by (unfold delta0; apply Rmin_pos; [apply cond_pos | lra]).
    assert (Hdelta0_lt1 : delta0 < 1) by (unfold delta0; apply Rle_lt_trans with (1/2); [apply Rmin_r | lra]).
    set (M := Rmax (I01 + 1) (RInt g delta0 1)).
    exists M.
    intros u Hu.
    destruct Hu as [Hu_pos Hu_lt1].
    destruct (Rlt_le_dec u delta0) as [Hu_lt_d0 | Hd0_le_u].
    - apply Rle_trans with (RInt g u 1).
      + (* RInt f_abs u 1 <= RInt g u 1 *)
        apply RInt_le; [lra | | |].
        * apply ex_RInt_continuous with (f := f_abs).
          intros z Hz.
          destruct Hz as [Hz1 Hz2].
          assert (Hz_pos : 0 < z) by (apply Rlt_le_trans with (Rmin u 1); [apply Rmin_glb_lt; [exact Hu_pos | lra] | exact Hz1]).
          apply Hcont_f_abs; exact Hz_pos.
        * apply ex_RInt_continuous with (f := g).
          intros z Hz.
          destruct Hz as [Hz1 Hz2].
          assert (Hz_pos : 0 < z) by (apply Rlt_le_trans with (Rmin u 1); [apply Rmin_glb_lt; [exact Hu_pos | lra] | exact Hz1]).
          apply Hcont_g; exact Hz_pos.
        * intros x Hx.
          destruct Hx as [Hx1 Hx2].
          assert (Hx_pos : 0 < x) by lra.
          unfold f_abs, g; destruct (Rlt_dec 0 x) as [Hpos | Hneg]; [| lra].
          rewrite (proof_irrelevance _ Hpos Hx_pos).
          exact (gamma_integrand_re_abs_bound s x Hx_pos).
      + (* RInt g u 1 < I01 + 1 <= M *)
        apply Rle_trans with (I01 + 1).
        * apply Rlt_le.
          specialize (Hdelta u) as Hd.
          assert (Hu_delta : ball 0 delta u).
          { unfold ball; simpl.
            change (Rabs (u - 0) < pos delta).
            rewrite Rminus_0_r.
            rewrite Rabs_pos_eq; [| left; exact Hu_pos].
            apply Rlt_le_trans with delta0; [exact Hu_lt_d0 | unfold delta0; apply Rmin_l]. }
          assert (Hu_pos' : 0 < u) by exact Hu_pos.
          specialize (Hd Hu_delta Hu_pos') as Hr.
          apply Rabs_def2 in Hr.
          destruct Hr as [Hr1 _].
          lra.
        * unfold M; apply Rmax_l.
    - apply Rle_trans with (RInt g u 1).
      + apply RInt_le; [lra | | |].
        * apply ex_RInt_continuous with (f := f_abs).
          intros z Hz.
          destruct Hz as [Hz1 Hz2].
          assert (Hz_pos : 0 < z) by (apply Rlt_le_trans with (Rmin u 1); [apply Rmin_glb_lt; [exact Hu_pos | lra] | exact Hz1]).
          apply Hcont_f_abs; exact Hz_pos.
        * apply ex_RInt_continuous with (f := g).
          intros z Hz.
          destruct Hz as [Hz1 Hz2].
          assert (Hz_pos : 0 < z) by (apply Rlt_le_trans with (Rmin u 1); [apply Rmin_glb_lt; [exact Hu_pos | lra] | exact Hz1]).
          apply Hcont_g; exact Hz_pos.
        * intros x Hx.
          destruct Hx as [Hx1 Hx2].
          assert (Hx_pos : 0 < x) by lra.
          unfold f_abs, g; destruct (Rlt_dec 0 x) as [Hpos | Hneg]; [| lra].
          rewrite (proof_irrelevance _ Hpos Hx_pos).
          exact (gamma_integrand_re_abs_bound s x Hx_pos).
      + (* RInt g u 1 <= RInt g delta0 1 <= M *)
        apply Rle_trans with (RInt g delta0 1).
        * (* g >= 0 -> ∫_u^1 g <= ∫_delta0^1 g，因 u >= delta0 *)
          assert (Hex1 : ex_RInt g u 1) by (apply ex_RInt_continuous with (f := g); intros z Hz; destruct Hz as [Hz1 Hz2]; assert (Hz_pos : 0 < z) by (apply Rlt_le_trans with (Rmin u 1); [apply Rmin_glb_lt; [exact Hu_pos | lra] | exact Hz1]); apply Hcont_g; exact Hz_pos).
          assert (Hex2 : ex_RInt g delta0 1) by (apply ex_RInt_continuous with (f := g); intros z Hz; destruct Hz as [Hz1 Hz2]; assert (Hz_pos : 0 < z) by (apply Rlt_le_trans with (Rmin delta0 1); [apply Rmin_glb_lt; [exact Hdelta0_pos | lra] | exact Hz1]); apply Hcont_g; exact Hz_pos).
          assert (Hex3 : ex_RInt g delta0 u) by (apply ex_RInt_continuous with (f := g); intros z Hz; destruct Hz as [Hz1 Hz2]; assert (Hz_pos : 0 < z) by (apply Rlt_le_trans with (Rmin delta0 u); [apply Rmin_glb_lt; [exact Hdelta0_pos | exact Hu_pos] | exact Hz1]); apply Hcont_g; exact Hz_pos).
          assert (Hnonneg : 0 <= RInt g delta0 u).
          { apply RInt_ge_0; [lra | exact Hex3 |].
            intros t Ht.
            unfold g; destruct (Rlt_dec 0 t) as [Hpos | Hneg]; [| lra].
            unfold gamma_integrand_real; apply Rmult_le_pos; [apply Rlt_le, exp_pos | apply Rlt_le; unfold Rpower; apply exp_pos]. }
          assert (Hsplit : RInt g delta0 u + RInt g u 1 = RInt g delta0 1).
          { apply (RInt_Chasles g delta0 u 1 Hex3 Hex1). }
          lra.
        * unfold M; apply Rmax_r.
  }
  assert (H_01_abs : ex_RInt_gen f_abs (at_right 0) (at_point 1)).
  {
    apply (RInt_gen_monotone_convergence f_abs 1 Rlt_0_1).
    - intros t Ht.
      unfold f_abs; destruct (Rlt_dec 0 t) as [Hpos | Hneg]; [apply Rabs_pos | lra].
    - intros u Hu.
      destruct Hu as [Hu_pos Hu_lt1].
      apply ex_RInt_continuous with (f := f_abs).
      intros z Hz.
      destruct Hz as [Hz1 Hz2].
      assert (Hz_pos : 0 < z) by (apply Rlt_le_trans with (Rmin u 1); [apply Rmin_glb_lt; [exact Hu_pos | lra] | exact Hz1]).
      apply Hcont_f_abs; exact Hz_pos.
    - exact H_bounded.
  }

  (* --- [1,∞) 段：比较检验 --- *)
  assert (H_cmp : ex_RInt_gen f_abs (at_right 1) (Rbar_locally p_infty)).
  {
    apply RInt_gen_comparison_test with (g := g) (a := 1).
    - intros t Ht.
      apply Hcont_f_abs; lra.
    - intros t Ht.
      apply Hcont_g; lra.
    - intros t Ht.
      destruct (Rlt_dec 0 t) as [Hpos | Hneg]; [| lra].
      assert (Ht_pos : 0 < t) by lra.
      split.
      + unfold f_abs; destruct (Rlt_dec 0 t) as [Hpos' | Hneg']; [| lra].
        rewrite (proof_irrelevance _ Hpos' Ht_pos).
        apply Rabs_pos.
      + unfold f_abs, g.
        destruct (Rlt_dec 0 t) as [Hpos' | Hneg']; [| lra].
        rewrite (proof_irrelevance _ Hpos' Ht_pos).
        exact (gamma_integrand_re_abs_bound s t Ht_pos).
    - exact (f_integrable_inf s Hre).
  }

  (* --- [1,∞) 段：sup 机器构造 (at_point 1, Rbar_locally p_infty) --- *)
  assert (H_lim1_abs : exists L : R,
            filterlim (fun y => RInt f_abs 1 y) (Rbar_locally p_infty) (locally L)).
  {
    assert (Hcont_f_abs_ge1 : forall t, t >= 1 -> continuous f_abs t).
    { intros t Ht; apply Hcont_f_abs; lra. }
    assert (Hcont_g_ge1 : forall t, t >= 1 -> continuous g t).
    { intros t Ht; apply Hcont_g; lra. }
    assert (Hg_nonneg_ge1 : forall t, t >= 1 -> 0 <= g t).
    { intros t Ht.
      unfold g; destruct (Rlt_dec 0 t) as [Hpos | Hneg]; [| lra].
      unfold gamma_integrand_real; apply Rmult_le_pos; [apply Rlt_le, exp_pos | apply Rlt_le; unfold Rpower; apply exp_pos]. }
    assert (Hf_bound_ge1 : forall t, t >= 1 -> 0 <= f_abs t <= g t).
    { intros t Ht.
      destruct (Rlt_dec 0 t) as [Hpos | Hneg]; [| lra].
      assert (Ht_pos : 0 < t) by lra.
      split.
      + unfold f_abs; destruct (Rlt_dec 0 t) as [Hpos' | Hneg']; [| lra].
        rewrite (proof_irrelevance _ Hpos' Ht_pos).
        apply Rabs_pos.
      + unfold f_abs, g.
        destruct (Rlt_dec 0 t) as [Hpos' | Hneg']; [| lra].
        rewrite (proof_irrelevance _ Hpos' Ht_pos).
        exact (gamma_integrand_re_abs_bound s t Ht_pos). }
    destruct (f_integrable_inf s Hre) as [Ig H_is_g].
    assert (Hlim_G := g_integral_limit g 1 Ig H_is_g).
    assert (Hg_bounded := g_integral_bounded g 1 Ig Hcont_g_ge1 Hg_nonneg_ge1 Hlim_G).
    assert (F_ub : forall b, b >= 1 -> RInt f_abs 1 b <= Ig).
    { apply f_integral_upper_bound with (g := g); [exact Hcont_f_abs_ge1 | exact Hcont_g_ge1 | exact Hf_bound_ge1 | exact Hg_bounded]. }
    destruct (f_sup_exists f_abs 1 Ig F_ub) as [l [Hl_ub Hl_least]].
    exists l.
    apply f_limit_to_sup with (a := 1) (l := l).
    - intros b1 b2 Hb12.
      apply f_integral_monotone with (a := 1); [exact Hcont_f_abs_ge1 | intros t Ht; destruct (Hf_bound_ge1 t Ht) as [H _]; exact H | exact Hb12].
    - intros b Hb; apply Hl_ub; exists b; split; [exact Hb | reflexivity].
    - intros eps.
    (* [经典引理区 ClassicalMonotoneConvergence · EM 7/7] 存在命题排中律（上确界可达性二分）；
       构造性替代 = S2-α 计划的 Σ 强化前提版（见 构造性轨道/公理基线审计.md） *)
      destruct (classic (exists b0, b0 >= 1 /\ RInt f_abs 1 b0 > l - pos eps)) as [H | Hnot]; [exact H |].
      exfalso.
      assert (H_ub : is_upper_bound (fun x => exists b, b >= 1 /\ x = RInt f_abs 1 b) (l - pos eps)).
      { intros x [b [Hb ->]]; apply Rnot_lt_le; intro Hlt; apply Hnot; exists b; split; [exact Hb | exact Hlt]. }
      apply Hl_least in H_ub.
      assert (Hpos : 0 < pos eps) by apply cond_pos; lra.
  }
  destruct H_lim1_abs as [L_abs Hlim_abs].
  assert (H_1p_abs : is_RInt_gen f_abs (at_point 1) (Rbar_locally p_infty) L_abs).
  {
    unfold is_RInt_gen.
    intros P HP.
    specialize (Hlim_abs P HP) as H_Rbar.
    destruct H_Rbar as [M HM].
    set (M0 := Rmax M 1).
    assert (H_M0_ge_M : M <= M0) by apply Rmax_l.
    assert (H_M0_le : forall y, M0 < y -> M < y).
    { intros y Hy. apply Rle_lt_trans with (r2 := M0); [exact H_M0_ge_M | exact Hy]. }
    set (Q1 := fun x => x = 1).
    set (Q2 := fun y => M0 < y).
    assert (HQ1 : at_point 1 Q1) by (unfold at_point; reflexivity).
    assert (HQ2 : Rbar_locally p_infty Q2).
    { unfold Rbar_locally; exists M0; intros y Hy; exact Hy. }
    apply Filter_prod with (Q := Q1) (R := Q2); [exact HQ1 | exact HQ2 |].
    intros x y Hx Hy.
    unfold Q1 in Hx; subst x.
    specialize (HM y (H_M0_le y Hy)) as HyP.
    assert (Hex_1y : ex_RInt f_abs 1 y).
    {
      apply ex_RInt_continuous with (f := f_abs) (a := 1) (b := y).
      intros z Hz.
      destruct Hz as [Hz1 Hz2].
      assert (H1_le_y : 1 <= y).
      { apply Rlt_le; apply Rle_lt_trans with M0; [apply Rmax_r | exact Hy]. }
      rewrite Rmin_left in Hz1 by exact H1_le_y.
      rewrite Rmax_right in Hz2 by exact H1_le_y.
      assert (Hz_pos : 0 < z) by (apply Rlt_le_trans with 1; [apply Rlt_0_1 | exact Hz1]).
      apply Hcont_f_abs; exact Hz_pos.
    }
    pose proof (RInt_correct f_abs 1 y Hex_1y) as H_is.
    exists (RInt f_abs 1 y). split; [exact H_is | exact HyP].
  }

  (* --- 拼接 --- *)
  destruct H_01_abs as [I_01 H_is_01].
  assert (H_final : is_RInt_gen f_abs (at_right 0) (Rbar_locally p_infty) (plus I_01 L_abs)).
  {
    apply is_RInt_gen_Chasles with (f := f_abs) (b := 1) (l1 := I_01) (l2 := L_abs).
    - exact H_is_01.
    - exact H_1p_abs.
  }
  exists (plus I_01 L_abs); exact H_final.
Qed.

End GammaIntegrandComplex.

Export GammaIntegrandComplex.
