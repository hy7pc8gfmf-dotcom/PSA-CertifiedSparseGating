(* 拆分自 Riemann_Hypothesis_Proof_Framework.v（复分析证明库 v6.0）*)
(* 库: ca_fourier  原文行区间: 826-1299  机械拆分，未改动内容 *)
(* 诚实定位 [2026-08-16 更新]：本库 = 「有限傅里叶和引理库」 + 「连续傅里叶积分理论」。
   有限和部分：fourier_sum / FourierTransform_approx 的线性性质与复等比级数主定理
   （伸缩恒等式、求和公式、抽象单位根正交性）。
   连续部分（Rocq 9 + Coquelicot 广义积分，零自定义公理）：
   - 第 10 轮：广义积分构造机（build_is_RInt_gen）、∫₀^∞ e^{-ax}cos(bx)dx = a/(a²+b²)、
     ∫₀^∞ e^{-ax}sin(bx)dx = b/(a²+b²)、双边 ∫_{-∞}^{∞} dξ/(a²+4π²ξ²) = 1/(2a)；
   - 第 11 轮：FourierTransform 定义、F(f_a)(ξ) = 1/(a + 2πiξ)（f_a = e^{-at}·1_{t≥0}）、
     Parseval 频率域 ∫|F(f_a)|²dξ = 1/(2a)、时域 ∫|f_a|²dt = 1/(2a)。
   - 第 12 轮：连续 FT 基本性质——线性性 F(a·f+b·g) = a·F(f)+b·F(g)（在积分存在条件下）、
     共轭对称 F(f)(−ξ) = conj(F(f)(ξ))（f 实值）；配套广义积分辅助引理 8 个
     （RInt_gen 的线性/外延包装，ProperFilter/Filter 版本）。
   未含：反演公式（下一阶段，需深引理 ∫₀^∞ cos(γu)/(1+u²)du = (π/2)e^{-γ}）。 *)

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

Require Import ca_base ca_algebra ca_primes ca_complex_analysis.

Require Import Stdlib.Logic.IndefiniteDescription.

(* 5.2 傅里叶分析 *)

Module FourierAnalysis.

Import ComplexNumbers.
Import ListNotations.
Import ConstructivePrimes.
Local Open Scope complex_scope.
Open Scope R_scope.

Require Import Stdlib.Reals.Reals.
Require Import Stdlib.Reals.RiemannInt.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.Reals.RIneq.
Require Import Stdlib.Reals.R_sqrt.
Require Import Stdlib.Reals.Reals.
Require Import Stdlib.micromega.Lra.
Require Import Stdlib.Reals.Reals.
Require Import Stdlib.setoid_ring.RealField.
Require Import Stdlib.micromega.Psatz.
Require Import Stdlib.Logic.ProofIrrelevance.
Require Import Stdlib.Strings.String.
Require Import Stdlib.Logic.ProofIrrelevance.
Require Import Stdlib.Program.Equality.

(* [清理] 已移除占位定义 finite_fourier_transform（原恒返回 C0，全库 0 处使用） *)

(* [清理] 已移除未解释算子 Parameter FourierTransform / InverseFourierTransform
   及公理 FourierTransform_zero / FourierInversion_at_zero / FourierTransform_linear /
   FourierTransform_shift / ConvolutionTheorem（均 0 处使用，且作用于未解释算子）。
   保留下方构造性的有限求和近似 FourierTransform_approx / InverseFourierTransform_approx。 *)

(* 3. 傅里叶近似（有限求和） *)
Fixpoint fourier_sum (f : R -> Complex) (ξ : R) (k : nat) (step : R) (acc : Complex) : Complex :=
  match k with
  | O => acc
  | S k' => 
      let x := INR k' * step in
      let term := Cmul (f x) (Cexp ((-c CI) *c ((2 * PI * ξ * x) +i 0))) in
      fourier_sum f ξ k' step (Cadd acc term)
  end.

Definition FourierTransform_approx (f : R -> Complex) (ξ : R) (n : nat) : Complex :=
  let step := 1.0 in
  fourier_sum f ξ n step C0.

Fixpoint inverse_fourier_sum (F : R -> Complex) (x : R) (k : nat) (step : R) (acc : Complex) : Complex :=
  match k with
  | O => acc
  | S k' => 
      let ξ := INR k' * step in
      let term := Cmul (F ξ) (Cexp (CI *c ((2 * PI * ξ * x) +i 0))) in
      inverse_fourier_sum F x k' step (Cadd acc term)
  end.

Definition InverseFourierTransform_approx (F : R -> Complex) (x : R) (n : nat) : Complex :=
  let step := 1.0 in
  inverse_fourier_sum F x n step C0.

(* 4. 复数运算辅助引理 *)
Lemma zero_eq_zero : 0 = 0.
Proof. reflexivity. Qed.

(* 复数相等判定 *)
Lemma Complex_eq : forall (z1 z2 : Complex),
  re z1 = re z2 -> im z1 = im z2 -> z1 = z2.
Proof.
  intros z1 z2 Hre Him.
  destruct z1 as [re1 im1].
  destruct z2 as [re2 im2].
  simpl in Hre, Him.
  subst re2 im2.
  reflexivity.
Qed.

(* C0 *c z = C0 *)
Lemma Cmul_0_l : forall (z : Complex), C0 *c z = C0.
Proof.
  intros z.
  apply Complex_eq.
  - unfold C0, Cmul; destruct z; simpl; ring.
  - unfold C0, Cmul; destruct z; simpl; ring.
Qed.

(* C0 +c C0 = C0 *)
Lemma Cadd_0_0 : C0 +c C0 = C0.
Proof.
  apply Complex_eq; unfold C0, Cadd; simpl; ring.
Qed.

(* C0 +c z = z *)
Lemma Cadd_0_l : forall (z : Complex), C0 +c z = z.
Proof.
  intros z.
  apply Complex_eq.
  - unfold C0, Cadd; destruct z; simpl; ring.
  - unfold C0, Cadd; destruct z; simpl; ring.
Qed.

(* z *c C0 = C0 *)
Lemma Cmul_0_r : forall (z : Complex), z *c C0 = C0.
Proof.
  intros z.
  apply Complex_eq.
  - unfold C0, Cmul; destruct z; simpl; ring.
  - unfold C0, Cmul; destruct z; simpl; ring.
Qed.

(* 复数加法结合律 *)
Lemma Cadd_assoc : forall (z1 z2 z3 : Complex),
  (z1 +c z2) +c z3 = z1 +c (z2 +c z3).
Proof.
  intros z1 z2 z3.
  apply Complex_eq; unfold Cadd; simpl; ring.
Qed.

(* 复数乘法左分配律 *)
Lemma Cmul_add_distr_l : forall (a b c : Complex),
  a *c (b +c c) = a *c b +c a *c c.
Proof.
  intros a b c.
  apply Complex_eq; unfold Cadd, Cmul; simpl; ring.
Qed.

(* 复数乘法右分配律 *)
Lemma Cmul_add_distr_r : forall (a b c : Complex),
  (a +c b) *c c = a *c c +c b *c c.
Proof.
  intros a b c.
  apply Complex_eq; unfold Cadd, Cmul; simpl; ring.
Qed.

(* 复数乘法结合律 *)
Lemma Cmul_assoc : forall (a b c : Complex),
  (a *c b) *c c = a *c (b *c c).
Proof.
  intros a b c.
  apply Complex_eq; unfold Cmul; simpl; ring.
Qed.

(* 复数加法交换律 *)
Lemma Cadd_comm : forall (z1 z2 : Complex), z1 +c z2 = z2 +c z1.
Proof.
  intros z1 z2.
  apply Complex_eq; unfold Cadd; simpl; ring.
Qed.

(* z +c C0 = z *)
Lemma Cadd_0_r : forall (z : Complex), z +c C0 = z.
Proof.
  intros z.
  apply Complex_eq.
  - unfold C0, Cadd; destruct z; simpl; ring.
  - unfold C0, Cadd; destruct z; simpl; ring.
Qed.

(* [构造性轨道 S1] 已删除 exist_eq（零引用；其陈述在无 ProofIrrelevance 时不可证） *)

(* 5. 傅里叶求和的性质 *)
Lemma fourier_sum_zero_v1 (f : R -> Complex) (n : nat) :
  FourierTransform_approx f 0 n = fourier_sum f 0 n 1.0 C0.
Proof. unfold FourierTransform_approx; reflexivity. Qed.

(* 零函数傅里叶近似为零 *)
Lemma fourier_sum_zero (f : R -> Complex) (n : nat) :
  (forall x : R, f x = C0) -> FourierTransform_approx f 0 n = C0.
Proof.
  intros Hzero. unfold FourierTransform_approx.
  induction n as [|n IH]; [reflexivity|].
  simpl. rewrite Hzero. rewrite Cmul_0_l. rewrite Cadd_0_l.
  exact IH.
Qed.

(* 零函数傅里叶近似为零（简化版） *)
Lemma fourier_sum_zero_simplified (f : R -> Complex) (n : nat) :
  (forall x : R, f x = C0) -> FourierTransform_approx f 0 n = C0.
Proof.
  intros Hzero; unfold FourierTransform_approx.
  induction n as [|n IH]; [reflexivity|].
  simpl; rewrite Hzero; rewrite Cmul_0_l; rewrite Cadd_0_0; exact IH.
Qed.

(* 累加器分解 *)
Lemma fourier_sum_add_accumulator (h : R -> Complex) (ξ : R) (n : nat) (acc1 acc2 : Complex) :
  fourier_sum h ξ n 1.0 (acc1 +c acc2) = fourier_sum h ξ n 1.0 acc1 +c acc2.
Proof.
  revert acc1 acc2; induction n as [|n IH]; intros acc1 acc2.
  - simpl; reflexivity.
  - simpl; set (x := INR n * 1.0); set (exp_term := Cexp ((-c CI) *c ((2 * PI * ξ * x) +i 0))).
    rewrite Cadd_assoc; rewrite (Cadd_comm acc2 (h x *c exp_term)); rewrite <- Cadd_assoc.
    rewrite (IH (Cadd acc1 (h x *c exp_term)) acc2); reflexivity.
Qed.

(* 和的可加性 *)
Lemma fourier_sum_additive (f g : R -> Complex) (ξ : R) (n : nat) (acc : Complex) :
  fourier_sum (fun x => f x +c g x) ξ n 1.0 acc =
  fourier_sum f ξ n 1.0 (fourier_sum g ξ n 1.0 acc).
Proof.
  revert acc; induction n as [|n IH]; intros acc.
  - simpl; reflexivity.
  - simpl; set (x := INR n * 1.0); set (exp_term := Cexp ((-c CI) *c ((2 * PI * ξ * x) +i 0))).
    rewrite Cmul_add_distr_r; rewrite <- Cadd_assoc.
    rewrite (IH ((Cadd acc (f x *c exp_term)) +c (g x *c exp_term))).
    assert (H_eq: ((acc +c f x *c exp_term) +c g x *c exp_term) =
                  ((acc +c g x *c exp_term) +c f x *c exp_term)).
    { rewrite Cadd_assoc; rewrite (Cadd_comm (f x *c exp_term) (g x *c exp_term));
      rewrite <- Cadd_assoc; reflexivity. }
    rewrite H_eq; rewrite (fourier_sum_add_accumulator g ξ n (acc +c g x *c exp_term) (f x *c exp_term)).
    reflexivity.
Qed.

(* 齐次性 *)
Lemma fourier_sum_homogeneous (f : R -> Complex) (a : Complex) (ξ : R) (n : nat) (acc : Complex) :
  fourier_sum (fun x => a *c f x) ξ n 1.0 (a *c acc) =
  a *c fourier_sum f ξ n 1.0 acc.
Proof.
  revert acc; induction n as [|n IH]; intros acc.
  - simpl; reflexivity.
  - simpl; set (x := INR n * 1.0); set (exp_term := Cexp ((-c CI) *c ((2 * PI * ξ * x) +i 0))).
    rewrite (Cmul_assoc a (f x) exp_term); rewrite <- Cmul_add_distr_l.
    rewrite (IH (acc +c f x *c exp_term)); reflexivity.
Qed.

(* 齐次性（零累加器版本1） *)
Lemma fourier_sum_homogeneous_zero_v1 (f : R -> Complex) (a : Complex) (ξ : R) (n : nat) :
  fourier_sum (fun x => a *c f x) ξ n 1.0 C0 = a *c fourier_sum f ξ n 1.0 C0.
Proof.
  rewrite <- (fourier_sum_homogeneous f a ξ n C0); rewrite Cmul_0_r; reflexivity.
Qed.

(* 齐次性（零累加器版本2） *)
Lemma fourier_sum_homogeneous_zero_v2 (f : R -> Complex) (a : Complex) (ξ : R) (n : nat) :
  fourier_sum (fun x => a *c f x) ξ n 1.0 C0 = a *c fourier_sum f ξ n 1.0 C0.
Proof.
  rewrite <- (Cmul_0_r a) at 1; exact (fourier_sum_homogeneous f a ξ n C0).
Qed.

(* 齐次性（零累加器） *)
Lemma fourier_sum_homogeneous_zero (f : R -> Complex) (a : Complex) (ξ : R) (n : nat) :
  fourier_sum (fun x => a *c f x) ξ n 1.0 C0 = a *c fourier_sum f ξ n 1.0 C0.
Proof.
  rewrite <- (Cmul_0_r a) at 1; exact (fourier_sum_homogeneous f a ξ n C0).
Qed.

(* 线性组合的简单形式 *)
Lemma fourier_sum_linear_simple (f g : R -> Complex) (a b : Complex) (ξ : R) (n : nat) :
  fourier_sum (fun x => a *c f x +c b *c g x) ξ n 1.0 C0 =
  a *c fourier_sum f ξ n 1.0 C0 +c b *c fourier_sum g ξ n 1.0 C0.
Proof.
  induction n as [|n IH].
  - simpl; rewrite Cmul_0_r, Cmul_0_r; rewrite Cadd_0_0; reflexivity.
  - simpl; set (x := INR n * 1.0); set (exp_term := Cexp ((-c CI) *c ((2 * PI * ξ * x) +i 0))).
    rewrite Cmul_add_distr_r; rewrite (Cmul_assoc a (f x) exp_term); rewrite (Cmul_assoc b (g x) exp_term).
    rewrite (fourier_sum_add_accumulator (fun x => a *c f x +c b *c g x) ξ n C0
              (Cadd (Cmul a (Cmul (f x) exp_term)) (Cmul b (Cmul (g x) exp_term)))).
    rewrite IH; rewrite (fourier_sum_add_accumulator f ξ n C0 (Cmul (f x) exp_term));
    rewrite (fourier_sum_add_accumulator g ξ n C0 (Cmul (g x) exp_term));
    rewrite Cmul_add_distr_l; rewrite Cmul_add_distr_l.
    repeat rewrite Cadd_assoc; f_equal.
    rewrite <- (Cadd_assoc (b *c fourier_sum g ξ n 1.0 C0) (a *c (f x *c exp_term)) (b *c (g x *c exp_term))).
    rewrite (Cadd_comm (b *c fourier_sum g ξ n 1.0 C0) (a *c (f x *c exp_term))).
    rewrite Cadd_assoc; reflexivity.
Qed.

(* 累加器分解展开 *)
Lemma fourier_sum_acc_decompose (f : R -> Complex) (ξ : R) (n : nat) (acc : Complex) :
  fourier_sum f ξ n 1.0 acc = fourier_sum f ξ n 1.0 C0 +c acc.
Proof.
  revert acc; induction n as [|n IH]; intros acc.
  - simpl; rewrite Cadd_0_l; reflexivity.
  - simpl; set (x := INR n * 1.0); set (exp_term := Cexp ((-c CI) *c ((2 * PI * ξ * x) +i 0))).
    rewrite IH; rewrite (IH (C0 +c f x *c exp_term)); rewrite Cadd_0_l;
    rewrite Cadd_assoc; rewrite (Cadd_comm (f x *c exp_term) acc); reflexivity.
Qed.

(* 线性组合的一般形式 *)
Lemma fourier_sum_linear (f g : R -> Complex) (a b : Complex) (ξ : R) (n : nat) (acc : Complex) :
  fourier_sum (fun x => a *c f x +c b *c g x) ξ n 1.0 acc =
  a *c fourier_sum f ξ n 1.0 C0 +c b *c fourier_sum g ξ n 1.0 C0 +c acc.
Proof.
  rewrite (fourier_sum_acc_decompose (fun x => a *c f x +c b *c g x) ξ n acc);
  rewrite fourier_sum_linear_simple; reflexivity.
Qed.

(* 线性组合直接形式 *)
Lemma fourier_sum_linear_direct (f g : R -> Complex) (a b : Complex) 
       (ξ : R) (n : nat) (acc : Complex) :
  fourier_sum (fun x => a *c f x +c b *c g x) ξ n 1.0 (a *c acc) =
  a *c fourier_sum f ξ n 1.0 acc +c b *c fourier_sum g ξ n 1.0 C0.
Proof.
  revert acc; induction n as [|n IH]; intros acc.
  - simpl; rewrite Cmul_0_r, Cadd_0_r; reflexivity.
  - simpl; set (x := INR n * 1.0); set (exp_term := Cexp ((-c CI) *c ((2 * PI * ξ * x) +i 0))).
    rewrite Cmul_add_distr_r; rewrite (Cmul_assoc a (f x) exp_term); rewrite (Cmul_assoc b (g x) exp_term).
    rewrite <- (Cadd_assoc (a *c acc) (a *c (f x *c exp_term)) (b *c (g x *c exp_term))).
    rewrite <- (Cmul_add_distr_l a acc (f x *c exp_term)).
    rewrite (fourier_sum_add_accumulator (fun x => a *c f x +c b *c g x) ξ n
              (a *c (acc +c f x *c exp_term)) (b *c (g x *c exp_term))).
    rewrite (IH (acc +c f x *c exp_term)); simpl.
    rewrite (fourier_sum_add_accumulator f ξ n acc (f x *c exp_term));
    rewrite (fourier_sum_add_accumulator g ξ n C0 (g x *c exp_term));
    rewrite Cmul_add_distr_l; rewrite Cmul_add_distr_l.
    repeat rewrite Cadd_assoc; reflexivity.
Qed.

(* 累加器加法引理 *)
Lemma fourier_sum_add_lemma : forall (f : R -> Complex) (ξ : R) (n : nat) (term : Complex),
  fourier_sum f ξ n 1.0 (C0 +c term) = fourier_sum f ξ n 1.0 C0 +c term.
Proof.
  induction n as [|n IH].
  - simpl; reflexivity.
  - intros term; simpl; set (x := INR n * 1.0); set (exp_term := Cexp ((-c CI) *c ((2 * PI * ξ * x) +i 0))).
    replace (C0 +c term +c f x *c exp_term) with (C0 +c (term +c f x *c exp_term))
      by (rewrite <- Cadd_assoc; reflexivity).
    rewrite IH; rewrite (IH (f x *c exp_term)); rewrite Cadd_assoc;
    rewrite (Cadd_comm (f x *c exp_term) term); reflexivity.
Qed.

(* 累加器通用形式 *)
Lemma fourier_sum_acc : forall (f : R -> Complex) (ξ : R) (n : nat) (step : R) (acc term : Complex),
  fourier_sum f ξ n step (Cadd acc term) = Cadd (fourier_sum f ξ n step C0) term +c acc.
Proof.
  induction n as [|n IH]; intros step acc term.
  - simpl; rewrite Cadd_comm, Cadd_assoc, Cadd_0_l; reflexivity.
  - simpl; set (x := INR n * step); set (current_term := Cmul (f x) (Cexp ((-c CI) *c ((2 * PI * ξ * x) +i 0)))).
    rewrite IH; rewrite (IH step C0 current_term); rewrite Cadd_0_r.
    repeat rewrite Cadd_assoc; rewrite (Cadd_comm acc term); repeat rewrite <- Cadd_assoc; reflexivity.
Qed.

(* 傅里叶近似的线性性质 *)
Lemma FourierTransform_approx_linear (f g : R -> Complex) (a b : Complex) (ξ : R) (n : nat) :
  FourierTransform_approx (fun x => a *c f x +c b *c g x) ξ n =
  a *c FourierTransform_approx f ξ n +c b *c FourierTransform_approx g ξ n.
Proof.
  unfold FourierTransform_approx; rewrite fourier_sum_linear; rewrite Cadd_0_r; reflexivity.
Qed.

(* [清理] 已移除公理 FourierTransform_linear / FourierTransform_shift（0 处使用） *)

Lemma Cpow_succ : forall z n, Cpow z (S n) = z *c Cpow z n.
Proof. intros z n; reflexivity. Qed.

(* 等比级数：Σ_{k=0}^{n-1} z^k *)
Fixpoint geom_sum (z : Complex) (n : nat) : Complex :=
  match n with
  | O => ComplexNumbers.C0
  | S m => Cadd (geom_sum z m) (Cpow z m)
  end.

(* 主定理 1（伸缩恒等式，无条件）：(z-1)·Σ_{k<n} z^k = z^n - 1 *)
Lemma geom_sum_telescope : forall z n,
  Cmul (Csub z ComplexNumbers.C1) (geom_sum z n) = Csub (Cpow z n) ComplexNumbers.C1.
Proof.
  intro z.
  induction n.
  - simpl.
    unfold Csub, Cpow, Cmul, ComplexNumbers.C0, ComplexNumbers.C1; simpl.
    f_equal; ring.
  - simpl.
    rewrite Cmul_add_distr_l.
    rewrite IHn.
    rewrite Cmul_sub_distr_r.
    rewrite <- Cpow_succ.
    rewrite Cmul_1_l.
    unfold Cadd, Csub, ComplexNumbers.C0, ComplexNumbers.C1; simpl.
    f_equal; ring.
Qed.

(* 辅助：z ≠ 1 蕴含 z-1 的模平方非零 *)
Lemma geom_sum_nonzero_den : forall z, z <> ComplexNumbers.C1 -> Cnorm_sq (Csub z ComplexNumbers.C1) <> 0.
Proof.
  intros z H.
  apply Rgt_not_eq.
  apply Cnorm_sq_pos_iff.
  intro Hzc.
  apply H.
  rewrite <- (Csub_add_rev z ComplexNumbers.C1).
  rewrite Hzc.
  apply Cadd_0_r.
Qed.

(* 主定理 2（几何级数求和公式）：z ≠ 1 时 Σ_{k<n} z^k = (z^n - 1)/(z - 1) *)
Lemma geom_sum_formula : forall z (H : z <> ComplexNumbers.C1) n,
  geom_sum z n = Cdiv (Csub (Cpow z n) ComplexNumbers.C1) (Csub z ComplexNumbers.C1) (geom_sum_nonzero_den z H).
Proof.
  intros z H n.
  rewrite <- (geom_sum_telescope z n).
  symmetry.
  apply Cdiv_mul_cancel.
Qed.

(* 主定理 3（抽象单位根正交性）：若 z^n = 1 且 z ≠ 1，则 Σ_{k<n} z^k = 0 *)
Lemma geom_sum_root_unity : forall z n, Cpow z n = ComplexNumbers.C1 -> z <> ComplexNumbers.C1 -> geom_sum z n = ComplexNumbers.C0.
Proof.
  intros z n Hzpow Hzneq.
  (* (z-1)·S = 0 *)
  assert (Htel0 : Cmul (Csub z ComplexNumbers.C1) (geom_sum z n) = ComplexNumbers.C0).
  { rewrite geom_sum_telescope.
    rewrite Hzpow.
    apply Csub_self. }
  (* |z-1| > 0 *)
  assert (Hzm1 : Csub z ComplexNumbers.C1 <> ComplexNumbers.C0).
  { intro Hzc.
    apply Hzneq.
    rewrite <- (Csub_add_rev z ComplexNumbers.C1).
    rewrite Hzc.
    apply Cadd_0_r. }
  assert (Hnz : 0 < Cnorm (Csub z ComplexNumbers.C1)) by (apply Cnorm_pos_lt; exact Hzm1).
  (* |S| = 0 *)
  assert (HnormS : Cnorm (geom_sum z n) = 0).
  { assert (Hnorm : Cnorm (Cmul (Csub z ComplexNumbers.C1) (geom_sum z n)) = 0).
    { rewrite Htel0. apply Cnorm_0. }
    rewrite Cnorm_mul in Hnorm.
    destruct (Rmult_integral _ _ Hnorm) as [Hl | Hr].
    - exfalso.
      apply (Rlt_irrefl 0).
      apply Rlt_le_trans with (Cnorm (Csub z ComplexNumbers.C1)); [exact Hnz | lra].
    - exact Hr. }
  apply Cnorm_zero_iff.
  exact HnormS.
Qed.

(* ============ 连续傅里叶积分理论（Rocq 9 + Coquelicot 广义积分） ============ *)
Require Import Coquelicot.Coquelicot.

(* ============ 1. 从 ca_gamma 复制的通用机器（只依赖 Coquelicot 原生） ============ *)

(* 局部邻域与开球的等价性（ca_gamma 745 行，原样复制） *)
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

(* exp 无界（test_ft_exp.v 已证） *)
Lemma exp_unbounded : forall M : R, exists x : R, M < exp x.
Proof.
  intro M.
  exists (ln (Rmax 1 (M + 1))).
  apply Rlt_le_trans with (M + 1).
  - lra.
  - assert (Hpos : 0 < Rmax 1 (M + 1)) by (apply Rlt_le_trans with 1; [lra | apply Rmax_l]).
    apply Rle_trans with (Rmax 1 (M + 1)).
    + apply Rmax_r.
    + rewrite (exp_ln (Rmax 1 (M + 1)) Hpos).
      apply Rle_refl.
Qed.

(* exp(-x) → 0 当 x → +∞（test_ft_exp.v 已证） *)
Lemma filterlim_exp_neg_p_infty : filterlim (fun x => exp (- x)) (Rbar_locally p_infty) (locally 0).
Proof.
  unfold filterlim, Rbar_locally, locally.
  intros P HP.
  destruct HP as [eps Hball].
  destruct (exp_unbounded (/ (pos eps))) as [x0 Hx0].
  exists (Rmax 0 x0).
  intros x Hx.
  apply Hball.
  change (Rabs (exp (- x) - 0) < pos eps).
  rewrite Rminus_0_r.
  apply Rabs_def1.
  - assert (Hx0lt : / (pos eps) < exp x).
    { apply Rlt_le_trans with (exp x0).
      - exact Hx0.
      - apply Rlt_le.
        apply exp_increasing.
        apply Rle_lt_trans with (Rmax 0 x0); [apply Rmax_r | exact Hx]. }
    rewrite exp_Ropp.
    rewrite <- (Rinv_inv (pos eps)).
    apply Rinv_lt_contravar.
    + apply Rmult_lt_0_compat; [apply Rinv_0_lt_compat; apply (cond_pos eps) | apply exp_pos].
    + exact Hx0lt.
  - apply Rlt_le_trans with 0.
    + assert (Hc : 0 < pos eps) by exact (cond_pos eps); lra.
    + apply Rlt_le; apply exp_pos.
Qed.

(* exp(-a·t) → 0 当 t → +∞（a > 0） *)
Lemma filterlim_exp_scal : forall a : R, 0 < a ->
  filterlim (fun t => exp (- a * t)) (Rbar_locally p_infty) (locally 0).
Proof.
  intros a Ha.
  unfold filterlim.
  intros P HP.
  destruct (locally_iff_open_ball 0 P) as [Hiff _].
  destruct (Hiff HP) as [eps [Heps_pos Hball]].
  destruct (exp_unbounded (/ eps)) as [x0 Hx0].
  exists (x0 / a).
  intros t Ht.
  apply Hball.
  unfold ball, AbsRing_ball; simpl.
  change (Rabs (exp (- a * t) - 0) < eps).
  rewrite Rminus_0_r.
  rewrite Rabs_pos_eq; [| apply Rlt_le; apply exp_pos].
  replace (- a * t) with (- (a * t)) by ring.
  rewrite exp_Ropp.
  rewrite <- (Rinv_inv eps).
  apply Rinv_lt_contravar.
  - apply Rmult_lt_0_compat; [apply Rinv_0_lt_compat; exact Heps_pos | apply exp_pos].
  - apply Rlt_trans with (exp x0).
    + exact Hx0.
    + apply exp_increasing.
      assert (Heq : x0 = a * (x0 / a)) by (field; apply Rgt_not_eq; exact Ha).
      rewrite Heq.
      apply Rmult_lt_compat_l; [exact Ha | exact Ht].
Qed.

(* 指数衰减 × 有界函数 → 0（a > 0） *)
Lemma filterlim_exp_scal_bounded : forall (a : R) (g : R -> R), 0 < a ->
  (exists M : R, 0 <= M /\ forall t, Rabs (g t) <= M) ->
  filterlim (fun t => exp (- a * t) * g t) (Rbar_locally p_infty) (locally 0).
Proof.
  intros a g Ha [M [HM0 Hbound]].
  unfold filterlim.
  intros P HP.
  destruct (locally_iff_open_ball 0 P) as [Hiff _].
  destruct (Hiff HP) as [eps [Heps_pos Hball]].
  assert (Heps' : 0 < eps / (M + 1)).
  { apply Rdiv_lt_0_compat; [exact Heps_pos | lra]. }
  assert (Hlim1 := filterlim_exp_scal a Ha (fun y => Rabs y < eps / (M + 1))).
  assert (Hloc1 : locally 0 (fun y : R => Rabs y < eps / (M + 1))).
  { apply locally_iff_open_ball; exists (eps / (M + 1)); split; [exact Heps' | intros y Hy; rewrite Rminus_0_r in Hy; exact Hy]. }
  destruct (Hlim1 Hloc1) as [M1 HM1].
  exists M1.
  intros t Ht.
  apply Hball.
  unfold ball, AbsRing_ball; simpl.
  change (Rabs (exp (- a * t) * g t - 0) < eps).
  rewrite Rminus_0_r.
  rewrite Rabs_mult.
  apply Rle_lt_trans with (Rabs (exp (- a * t)) * M).
  - apply Rmult_le_compat_l; [apply Rabs_pos | apply Hbound].
  - apply Rlt_le_trans with (Rabs (exp (- a * t)) * (M + 1)).
    + apply Rmult_lt_compat_l.
      * apply Rabs_pos_lt.
        apply Rgt_not_eq; apply exp_pos.
      * lra.
    + apply Rle_trans with (eps / (M + 1) * (M + 1)).
      * apply Rmult_le_compat_r.
        -- lra.
        -- apply Rlt_le; apply HM1; exact Ht.
      * replace (eps / (M + 1) * (M + 1)) with eps by (field; lra).
        apply Rle_refl.
Qed.

(* |sin x| <= 1，|cos x| <= 1（由 sin² + cos² = 1） *)
Lemma Rabs_sin_le_1 : forall x : R, Rabs (sin x) <= 1.
Proof.
  intro x.
  assert (Hsq : 0 <= sin x * sin x) by apply Rle_0_sqr.
  assert (Hcos2 : 0 <= cos x * cos x) by apply Rle_0_sqr.
  assert (Hsin2 : sin x * sin x <= 1).
  { rewrite <- (sin2_cos2 x).
    rewrite <- (Rplus_0_r (sin x * sin x)).
    apply Rplus_le_compat_l.
    exact Hcos2. }
  assert (Habs2 : Rabs (sin x) * Rabs (sin x) <= 1).
  { rewrite <- Rabs_mult.
    rewrite Rabs_pos_eq; [exact Hsin2 | exact Hsq]. }
  apply Rle_trans with (sqrt (Rabs (sin x) * Rabs (sin x))).
  - assert (Hs : sqrt (Rabs (sin x) * Rabs (sin x)) = Rabs (sin x)).
    { apply sqrt_square; apply Rabs_pos. }
    rewrite Hs.
    apply Rle_refl.
  - apply Rle_trans with (sqrt 1).
    + apply sqrt_le_1_c; [apply Rle_0_sqr | lra | exact Habs2].
    + rewrite sqrt_1; apply Rle_refl.
Qed.

Lemma Rabs_cos_le_1 : forall x : R, Rabs (cos x) <= 1.
Proof.
  intro x.
  assert (Hsq : 0 <= cos x * cos x) by apply Rle_0_sqr.
  assert (Hsin2 : 0 <= sin x * sin x) by apply Rle_0_sqr.
  assert (Hcos2 : cos x * cos x <= 1).
  { rewrite <- (sin2_cos2 x).
    rewrite <- (Rplus_0_l (cos x * cos x)).
    apply Rplus_le_compat_r.
    exact Hsin2. }
  assert (Habs2 : Rabs (cos x) * Rabs (cos x) <= 1).
  { rewrite <- Rabs_mult.
    rewrite Rabs_pos_eq; [exact Hcos2 | exact Hsq]. }
  apply Rle_trans with (sqrt (Rabs (cos x) * Rabs (cos x))).
  - assert (Hs : sqrt (Rabs (cos x) * Rabs (cos x)) = Rabs (cos x)).
    { apply sqrt_square; apply Rabs_pos. }
    rewrite Hs.
    apply Rle_refl.
  - apply Rle_trans with (sqrt 1).
    + apply sqrt_le_1_c; [apply Rle_0_sqr | lra | exact Habs2].
    + rewrite sqrt_1; apply Rle_refl.
Qed.

(* 从极限和局部小量构造广义积分（ca_gamma 8104-8232 行，原样复制） *)
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

(* ============ 2. e^{-ax}·cos(bx) / e^{-ax}·sin(bx) 的积分 ============ *)

(* R 上的加法连续（R_UniformSpace 版，eps 论证） *)
Lemma filterlim_Rplus : forall x y : R,
  filterlim (fun z : R * R => fst z + snd z) (filter_prod (locally x) (locally y)) (locally (x + y)).
Proof.
  intros x y.
  unfold filterlim.
  intros P HP.
  destruct (locally_iff_open_ball (x + y) P) as [Hiff _].
  destruct (Hiff HP) as [eps [Heps_pos Hball]].
  assert (Heps2 : 0 < eps / 2) by lra.
  apply (Filter_prod (locally x) (locally y)
        (fun z => P (fst z + snd z))
        (fun a => Rabs (a - x) < eps / 2)
        (fun b => Rabs (b - y) < eps / 2)).
  - apply locally_iff_open_ball; exists (eps / 2); split; [exact Heps2 | intros a Ha; exact Ha].
  - apply locally_iff_open_ball; exists (eps / 2); split; [exact Heps2 | intros b Hb; exact Hb].
  - intros a b Ha Hb.
    apply Hball.
    unfold ball, AbsRing_ball; simpl.
    change (Rabs (a + b - (x + y)) < eps).
    apply Rle_lt_trans with (Rabs (a - x) + Rabs (b - y)).
    + replace (a + b - (x + y)) with ((a - x) + (b - y)) by ring.
      apply Rabs_triang.
    + apply Rlt_le_trans with (eps / 2 + eps / 2).
      * apply Rplus_lt_compat; [exact Ha | exact Hb].
      * lra.
Qed.

(* M·(eps/(2(M+1))) < eps/2（0 <= M，0 < eps，0 < M+1） *)
Lemma Rmult_div_lt_aux : forall (M eps : R), 0 <= M -> 0 < eps -> 0 < M + 1 ->
  M * (eps / (2 * (M + 1))) < eps / 2.
Proof.
  intros M eps HM0 Heps HM1.
  assert (Hnn : 2 * (M + 1) <> 0).
  { apply Rgt_not_eq. lra. }
  assert (Hn2 : 2 <> 0) by (apply Rgt_not_eq; apply Rlt_0_2).
  assert (Hnn1 : M + 1 <> 0) by (apply Rgt_not_eq; exact HM1).
  apply Rmult_lt_reg_r with (2 * (M + 1)).
  - lra.
  - replace (M * (eps / (2 * (M + 1))) * (2 * (M + 1))) with (M * eps) by (field; auto).
    replace (eps / 2 * (2 * (M + 1))) with ((M + 1) * eps).
    + apply Rmult_lt_compat_r with (r := eps); [exact Heps | lra].
    + field; auto.
Qed.

(* R 上的乘法连续（R_UniformSpace 版，eps 论证） *)
Lemma filterlim_Rmult : forall x y : R,
  filterlim (fun z : R * R => fst z * snd z) (filter_prod (locally x) (locally y)) (locally (x * y)).
Proof.
  intros x y.
  unfold filterlim.
  intros P HP.
  destruct (locally_iff_open_ball (x * y) P) as [Hiff _].
  destruct (Hiff HP) as [eps [Heps_pos Hball]].
  set (M := Rmax (Rabs x + 1) (Rabs y + 1)).
  assert (HM0 : 0 <= M).
  { unfold M.
    apply Rle_trans with (Rabs x + 1).
    - assert (Hrx : 0 <= Rabs x) by apply Rabs_pos. lra.
    - apply Rmax_l.
  }
  assert (HM1 : 0 < M + 1) by lra.
  assert (HxM : Rabs x <= M - 1).
  { unfold M.
    apply Rle_trans with (Rabs x + 1 - 1).
    - lra.
    - apply Rplus_le_compat_r.
      apply Rmax_l.
  }
  assert (HyM : Rabs y <= M - 1).
  { unfold M.
    apply Rle_trans with (Rabs y + 1 - 1).
    - lra.
    - apply Rplus_le_compat_r.
      apply Rmax_r.
  }
  set (e := Rmin (eps / (2 * (M + 1))) 1).
  assert (He_pos : 0 < e).
  { unfold e. apply Rmin_pos.
    - apply Rdiv_lt_0_compat; [exact Heps_pos | lra].
    - lra.
  }
  assert (He_le : e <= eps / (2 * (M + 1))).
  { unfold e; apply Rmin_l. }
  assert (He_1 : e <= 1) by (unfold e; apply Rmin_r).
  apply (Filter_prod (locally x) (locally y)
        (fun z => P (fst z * snd z))
        (fun a => Rabs (a - x) < e)
        (fun b => Rabs (b - y) < e)).
  - apply locally_iff_open_ball; exists e; split; [exact He_pos | intros a Ha; exact Ha].
  - apply locally_iff_open_ball; exists e; split; [exact He_pos | intros b Hb; exact Hb].
  - intros a b Ha Hb.
    apply Hball.
    unfold ball, AbsRing_ball; simpl.
    change (Rabs (a * b - x * y) < eps).
    replace (a * b - x * y) with (a * (b - y) + y * (a - x)) by ring.
    apply Rle_lt_trans with (Rabs (a * (b - y)) + Rabs (y * (a - x))).
    + apply Rabs_triang.
    + assert (HaM : Rabs a <= M).
      { apply Rle_trans with (Rabs x + Rabs (a - x)).
        - assert (Haa : a = x + (a - x)) by lra.
          rewrite Haa at 1.
          apply Rabs_triang.
        - apply Rle_trans with ((M - 1) + e).
          * apply Rplus_le_compat; [exact HxM | apply Rlt_le; exact Ha].
          * assert (He1 : e <= 1) by exact He_1.
            lra.
      }
      apply Rle_lt_trans with (M * Rabs (b - y) + M * Rabs (a - x)).
      * apply Rplus_le_compat.
        -- rewrite Rabs_mult.
           apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | exact HaM | apply Rle_refl].
        -- rewrite Rabs_mult.
           apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | | apply Rle_refl].
           apply Rle_trans with (M - 1); [exact HyM | lra].
      * apply Rle_lt_trans with (M * e + M * e).
        -- apply Rplus_le_compat.
           ++ apply Rmult_le_compat_l; [apply HM0 | apply Rlt_le; assumption].
           ++ apply Rmult_le_compat_l; [apply HM0 | apply Rlt_le; assumption].
        -- apply Rlt_le_trans with (eps / 2 + eps / 2).
           ++ apply Rplus_lt_compat.
              ** apply Rle_lt_trans with (M * (eps / (2 * (M + 1)))).
                 --- apply Rmult_le_compat_l; [apply HM0 | exact He_le].
                 --- apply Rmult_div_lt_aux; [exact HM0 | exact Heps_pos | exact HM1].
              ** apply Rle_lt_trans with (M * (eps / (2 * (M + 1)))).
                 --- apply Rmult_le_compat_l; [apply HM0 | exact He_le].
                 --- apply Rmult_div_lt_aux; [exact HM0 | exact Heps_pos | exact HM1].
           ++ lra.
Qed.

(* R 上的取负连续（R_UniformSpace 版，eps 论证） *)
Lemma filterlim_Ropp : forall x : R,
  filterlim (fun z => - z) (locally x) (locally (- x)).
Proof.
  intros x.
  unfold filterlim.
  intros P HP.
  destruct (locally_iff_open_ball (- x) P) as [Hiff _].
  destruct (Hiff HP) as [eps [Heps_pos Hball]].
  apply locally_iff_open_ball.
  exists eps; split; [exact Heps_pos |].
  intros z Hz.
  apply Hball.
  unfold ball, AbsRing_ball; simpl.
  change (Rabs (- z - (- x)) < eps).
  replace (- z - (- x)) with (x - z) by lra.
  rewrite Rabs_minus_sym.
  exact Hz.
Qed.

(* 标准库连续性到 Coquelicot 连续性的转化（ca_gamma 768-824 行，原样复制） *)
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

(* 线性函数 c·t 的连续性（标准库组合） *)
Lemma continuity_pt_scal_id : forall (c : R) (x : R),
  continuity_pt (fun t => c * t) x.
Proof.
  intros c x.
  apply continuity_pt_mult.
  - apply continuity_pt_const; unfold constant; intros; reflexivity.
  - apply derivable_continuous_pt; apply derivable_pt_id.
Qed.

(* 常函数连续性 *)
Lemma continuity_pt_const_R : forall (c : R) (x : R),
  continuity_pt (fun _ : R => c) x.
Proof.
  intros c x. apply continuity_pt_const. unfold constant; intros; reflexivity.
Qed.

Lemma continuous_exp_cos : forall a b x, continuous (fun t => exp (- a * t) * cos (b * t)) x.
Proof.
  intros a b x.
  apply continuity_pt_to_continuous_simple.
  apply continuity_pt_mult.
  - apply (continuity_pt_comp (fun t => - a * t) exp x).
    + apply continuity_pt_scal_id.
    + apply derivable_continuous; apply derivable_exp.
  - apply (continuity_pt_comp (fun t => b * t) cos x).
    + apply continuity_pt_scal_id.
    + apply continuity_cos.
Qed.

Lemma continuous_exp_sin : forall a b x, continuous (fun t => exp (- a * t) * sin (b * t)) x.
Proof.
  intros a b x.
  apply continuity_pt_to_continuous_simple.
  apply continuity_pt_mult.
  - apply (continuity_pt_comp (fun t => - a * t) exp x).
    + apply continuity_pt_scal_id.
    + apply derivable_continuous; apply derivable_exp.
  - apply (continuity_pt_comp (fun t => b * t) sin x).
    + apply continuity_pt_scal_id.
    + apply continuity_sin.
Qed.

(* ∫₀^T e^{-ax}cos(bx)dx = (e^{-aT}(b sin(bT) - a cos(bT)) + a)/(a²+b²)（a>0） *)
Lemma is_RInt_exp_cos : forall a b T : R, 0 < a ->
  is_RInt (fun x => exp (- a * x) * cos (b * x)) 0 T
    ((exp (- a * T) * (b * sin (b * T) - a * cos (b * T)) + a) / (a * a + b * b)).
Proof.
  intros a b T Ha.
  assert (Hden : a * a + b * b <> 0).
  { apply Rgt_not_eq.
    assert (Haa : 0 < a * a) by (apply Rmult_lt_0_compat; exact Ha; exact Ha).
    assert (Hbb : 0 <= b * b) by (apply Rle_0_sqr).
    lra.
  }
  set (F := fun x => / (a * a + b * b) * (exp (- a * x) * (b * sin (b * x) - a * cos (b * x)))).
  assert (Hval : F T - F 0 =
      (exp (- a * T) * (b * sin (b * T) - a * cos (b * T)) + a) / (a * a + b * b)).
  { unfold F.
    replace (- a * 0) with 0 by ring.
    replace (b * 0) with 0 by ring.
    rewrite exp_0, sin_0, cos_0.
    field; exact Hden.
  }
  rewrite <- Hval.
  apply (is_RInt_derive F (fun x => exp (- a * x) * cos (b * x)) 0 T).
  - intros x Hx.
    unfold is_derive.
    assert (Hg1 : is_derive (fun x => - a * x) x (- a)).
    { assert (Hscal : is_derive (fun x => - a * x) x ((- a) * 1)).
      { apply (is_derive_scal id x (- a) 1).
        change (is_derive (fun t : R => t) x one).
        apply (is_derive_id (K := R_AbsRing)). }
      assert (Hv1 : (- a) * 1 = - a) by ring.
      rewrite Hv1 in Hscal.
      exact Hscal.
    }
    assert (Hg2 : is_derive (fun x => b * x) x b).
    { assert (Hscal : is_derive (fun x => b * x) x (b * 1)).
      { apply (is_derive_scal id x b 1).
        change (is_derive (fun t : R => t) x one).
        apply (is_derive_id (K := R_AbsRing)). }
      assert (Hv1 : b * 1 = b) by ring.
      rewrite Hv1 in Hscal.
      exact Hscal.
    }
    assert (Hexp1 : is_derive (fun x => exp (- a * x)) x (- a * exp (- a * x))).
    { apply (is_derive_comp exp (fun x => - a * x) x (exp (- a * x)) (- a)).
      - apply is_derive_exp.
      - exact Hg1.
    }
    assert (Hsin1 : is_derive (fun x => sin (b * x)) x (b * cos (b * x))).
    { apply (is_derive_comp sin (fun x => b * x) x (cos (b * x)) b).
      - apply is_derive_sin.
      - exact Hg2.
    }
    assert (Hcos1 : is_derive (fun x => cos (b * x)) x (- b * sin (b * x))).
    { assert (Hcomp : is_derive (fun x => cos (b * x)) x (b * (- sin (b * x)))).
      { apply (is_derive_comp cos (fun x => b * x) x (- sin (b * x)) b).
        - apply is_derive_cos.
        - exact Hg2. }
      assert (Hv3 : b * (- sin (b * x)) = - b * sin (b * x)) by ring.
      rewrite <- Hv3; exact Hcomp.
    }
    assert (Hexpcos : is_derive (fun x => exp (- a * x) * (b * sin (b * x) - a * cos (b * x))) x
              ((- a * exp (- a * x)) * (b * sin (b * x) - a * cos (b * x)) +
               exp (- a * x) * (b * (b * cos (b * x)) - a * (- b * sin (b * x))))).
    { apply (is_derive_mult (fun x => exp (- a * x)) (fun x => b * sin (b * x) - a * cos (b * x)) x
             (- a * exp (- a * x))
             (b * (b * cos (b * x)) - a * (- b * sin (b * x)))).
      - exact Hexp1.
      - apply (is_derive_minus (fun x => b * sin (b * x)) (fun x => a * cos (b * x)) x
               (b * (b * cos (b * x))) (a * (- b * sin (b * x)))).
        + apply (is_derive_scal (fun x => sin (b * x)) x b (b * cos (b * x))).
          exact Hsin1.
        + apply (is_derive_scal (fun x => cos (b * x)) x a (- b * sin (b * x))).
          exact Hcos1.
      - intros n m; apply Rmult_comm.
    }
    assert (HderF' : is_derive F x (/ (a * a + b * b) *
        ((- a * exp (- a * x)) * (b * sin (b * x) - a * cos (b * x)) +
         exp (- a * x) * (b * (b * cos (b * x)) - a * (- b * sin (b * x)))))).
    { unfold F.
      apply (is_derive_scal (fun x => exp (- a * x) * (b * sin (b * x) - a * cos (b * x))) x
             (/ (a * a + b * b)) _ Hexpcos). }
    assert (Hv : / (a * a + b * b) *
        ((- a * exp (- a * x)) * (b * sin (b * x) - a * cos (b * x)) +
         exp (- a * x) * (b * (b * cos (b * x)) - a * (- b * sin (b * x)))) =
        exp (- a * x) * cos (b * x)).
    { field; exact Hden. }
    rewrite <- Hv; exact HderF'.
  - intros x Hx.
    apply continuous_exp_cos.
Qed.

(* ∫₀^∞ e^{-ax}cos(bx)dx = a/(a²+b²)（a>0） *)
Lemma RInt_gen_exp_cos : forall a b : R, 0 < a ->
  is_RInt_gen (fun x => exp (- a * x) * cos (b * x)) (at_right 0) (Rbar_locally p_infty)
    (a / (a * a + b * b)).
Proof.
  intros a b Ha.
  assert (Hden : a * a + b * b <> 0).
  { apply Rgt_not_eq.
    assert (Haa : 0 < a * a) by (apply Rmult_lt_0_compat; exact Ha; exact Ha).
    assert (Hbb : 0 <= b * b) by (apply Rle_0_sqr).
    lra.
  }
  set (f := fun x => exp (- a * x) * cos (b * x)).
  apply (build_is_RInt_gen f 0 (a / (a * a + b * b))).
  - (* Hf_cont *)
    intros t Ht; unfold f; apply continuous_exp_cos.
  - (* Hf_int_ab *)
    intros b0 Hb0.
    apply (ex_RInt_continuous f 0 b0).
    intros z Hz; unfold f; apply continuous_exp_cos.
  - (* Hlim_F *)
    assert (Hrim : forall T, RInt f 0 T =
        (exp (- a * T) * (b * sin (b * T) - a * cos (b * T)) + a) / (a * a + b * b)).
    { intros T. unfold f. apply is_RInt_unique. apply is_RInt_exp_cos; exact Ha. }
    assert (HlimV : filterlim
        (fun T => (exp (- a * T) * (b * sin (b * T) - a * cos (b * T)) + a) / (a * a + b * b))
        (Rbar_locally p_infty) (locally (a / (a * a + b * b)))).
    {
      assert (Hden_pos : 0 < a * a + b * b).
      { assert (Haa : 0 < a * a) by (apply Rmult_lt_0_compat; exact Ha; exact Ha).
        assert (Hbb : 0 <= b * b) by (apply Rle_0_sqr).
        lra. }
      assert (HlimE : filterlim (fun T => exp (- a * T) * (b * sin (b * T) - a * cos (b * T)))
                        (Rbar_locally p_infty) (locally 0)).
      { apply filterlim_exp_scal_bounded.
        - exact Ha.
        - exists (Rabs b + Rabs a).
          split.
          * apply Rplus_le_le_0_compat; apply Rabs_pos.
          * intros t.
            apply Rle_trans with (Rabs (b * sin (b * t)) + Rabs (a * cos (b * t))).
            -- rewrite <- (Rabs_Ropp (a * cos (b * t))).
               apply Rabs_triang.
            -- apply Rplus_le_compat.
               ++ rewrite Rabs_mult.
                  apply Rle_trans with (Rabs b * 1).
                  ** apply Rmult_le_compat_l; [apply Rabs_pos | apply Rabs_sin_le_1].
                  ** rewrite Rmult_1_r; apply Rle_refl.
               ++ rewrite Rabs_mult.
                  apply Rle_trans with (Rabs a * 1).
                  ** apply Rmult_le_compat_l; [apply Rabs_pos | apply Rabs_cos_le_1].
                  ** rewrite Rmult_1_r; apply Rle_refl.
      }
      unfold filterlim.
      intros P HP.
      destruct (locally_iff_open_ball (a / (a * a + b * b)) P) as [Hiff _].
      destruct (Hiff HP) as [eps [Heps_pos Hball]].
      assert (Heps' : 0 < eps * (a * a + b * b)).
      { apply Rmult_lt_0_compat; [exact Heps_pos | exact Hden_pos]. }
      specialize (HlimE (fun y => Rabs y < eps * (a * a + b * b))).
      assert (HlocE : locally 0 (fun y : R => Rabs y < eps * (a * a + b * b))).
      { apply locally_iff_open_ball; exists (eps * (a * a + b * b)); split; [exact Heps' | intros y Hy; rewrite Rminus_0_r in Hy; exact Hy]. }
      destruct (HlimE HlocE) as [M HM].
      unfold Rbar_locally.
      exists M.
      intros T HT.
      apply Hball.
      unfold ball, AbsRing_ball; simpl.
      change (Rabs ((exp (- a * T) * (b * sin (b * T) - a * cos (b * T)) + a) / (a * a + b * b)
                    - a / (a * a + b * b)) < eps).
      replace ((exp (- a * T) * (b * sin (b * T) - a * cos (b * T)) + a) / (a * a + b * b)
               - a / (a * a + b * b))
        with ((exp (- a * T) * (b * sin (b * T) - a * cos (b * T))) / (a * a + b * b))
        by (field; exact Hden).
      rewrite Rabs_div; [| exact Hden].
      rewrite Rabs_pos_eq with (x := a * a + b * b); [| apply Rlt_le; exact Hden_pos].
      apply Rmult_lt_reg_l with (a * a + b * b).
      - exact Hden_pos.
      - replace ((a * a + b * b) * (Rabs (exp (- a * T) * (b * sin (b * T) - a * cos (b * T))) / (a * a + b * b)))
          with (Rabs (exp (- a * T) * (b * sin (b * T) - a * cos (b * T)))) by (field; exact Hden).
        replace ((a * a + b * b) * eps) with (eps * (a * a + b * b)) by (apply Rmult_comm).
        exact (HM T HT).
    }
    apply (filterlim_ext
             (fun T => (exp (- a * T) * (b * sin (b * T) - a * cos (b * T)) + a) / (a * a + b * b))
             (fun T => RInt f 0 T)).
    + intros T; symmetry; apply Hrim.
    + exact HlimV.
  - (* Hdelta *)
    intros eps.
    set (F0 := fun x => (exp (- a * x) * (b * sin (b * x) - a * cos (b * x)) + a) / (a * a + b * b)).
    assert (Hcont0 : continuous F0 0).
    { unfold F0.
      apply continuity_pt_to_continuous_simple.
      apply continuity_pt_mult.
      - apply continuity_pt_plus.
        + apply continuity_pt_mult.
          * apply (continuity_pt_comp (fun t => - a * t) exp 0).
            -- apply continuity_pt_scal_id.
            -- apply derivable_continuous; apply derivable_exp.
          * apply continuity_pt_minus.
            -- apply continuity_pt_mult; [apply continuity_pt_const_R |
                 apply (continuity_pt_comp (fun t => b * t) sin 0)].
               ++ apply continuity_pt_scal_id.
               ++ apply continuity_sin.
            -- apply continuity_pt_mult; [apply continuity_pt_const_R |
                 apply (continuity_pt_comp (fun t => b * t) cos 0)].
               ++ apply continuity_pt_scal_id.
               ++ apply continuity_cos.
        + apply continuity_pt_const_R.
      - apply continuity_pt_const_R.
    }
    assert (H0 : F0 0 = 0).
    { unfold F0.
      replace (- a * 0) with 0 by ring.
      replace (b * 0) with 0 by ring.
      rewrite exp_0, sin_0, cos_0.
      field; exact Hden. }
    assert (Hloc0 : locally 0 (fun x => Rabs (F0 x) < pos eps)).
    {
      assert (Hloc0' : locally 0 (fun x => Rabs (F0 x - F0 0) < pos eps)).
      {
        assert (HlocP : locally (F0 0) (fun y => Rabs (y - F0 0) < pos eps)).
        { apply locally_iff_open_ball; exists (pos eps); split; [apply cond_pos | intros y Hy; exact Hy]. }
        apply (Hcont0 (fun y => Rabs (y - F0 0) < pos eps) HlocP).
      }
      apply (filter_imp (fun x => Rabs (F0 x - F0 0) < pos eps)
                        (fun x => Rabs (F0 x) < pos eps)).
      - intros x Hx.
        rewrite H0 in Hx.
        rewrite Rminus_0_r in Hx.
        exact Hx.
      - exact Hloc0'.
    }
    destruct (locally_iff_open_ball 0 (fun x => Rabs (F0 x) < pos eps)) as [Hiff _].
    destruct (Hiff Hloc0) as [delta [Hdelta_pos Hdelta_ball]].
    exists (mkposreal delta Hdelta_pos).
    intros x Hx_abs Hx_ge.
    assert (Hex0x : ex_RInt f 0 x).
    { apply (ex_RInt_continuous f 0 x); intros z Hz; unfold f; apply continuous_exp_cos. }
    assert (Hexx0 : ex_RInt f x 0).
    { apply (ex_RInt_continuous f x 0); intros z Hz; unfold f; apply continuous_exp_cos. }
    rewrite <- (opp_RInt_swap f 0 x Hex0x).
    rewrite Rabs_Ropp.
    assert (Hfx : RInt f 0 x = F0 x).
    { apply is_RInt_unique. unfold f. apply is_RInt_exp_cos; exact Ha. }
    rewrite Hfx.
    apply Hdelta_ball.
    simpl; exact Hx_abs.
Qed.

(* ∫₀^T e^{-ax}sin(bx)dx = (e^{-aT}(-a sin(bT) - b cos(bT)) + b)/(a²+b²)（a>0） *)
Lemma is_RInt_exp_sin : forall a b T : R, 0 < a ->
  is_RInt (fun x => exp (- a * x) * sin (b * x)) 0 T
    ((exp (- a * T) * (- a * sin (b * T) - b * cos (b * T)) + b) / (a * a + b * b)).
Proof.
  intros a b T Ha.
  assert (Hden : a * a + b * b <> 0).
  { apply Rgt_not_eq.
    assert (Haa : 0 < a * a) by (apply Rmult_lt_0_compat; exact Ha; exact Ha).
    assert (Hbb : 0 <= b * b) by (apply Rle_0_sqr).
    lra.
  }
  set (F := fun x => / (a * a + b * b) * (exp (- a * x) * (- a * sin (b * x) - b * cos (b * x)))).
  assert (Hval : F T - F 0 =
      (exp (- a * T) * (- a * sin (b * T) - b * cos (b * T)) + b) / (a * a + b * b)).
  { unfold F.
    replace (- a * 0) with 0 by ring.
    replace (b * 0) with 0 by ring.
    rewrite exp_0, sin_0, cos_0.
    field; exact Hden.
  }
  rewrite <- Hval.
  apply (is_RInt_derive F (fun x => exp (- a * x) * sin (b * x)) 0 T).
  - intros x Hx.
    unfold is_derive.
    assert (Hg1 : is_derive (fun x => - a * x) x (- a)).
    { assert (Hscal : is_derive (fun x => - a * x) x ((- a) * 1)).
      { apply (is_derive_scal id x (- a) 1).
        change (is_derive (fun t : R => t) x one).
        apply (is_derive_id (K := R_AbsRing)). }
      assert (Hv1 : (- a) * 1 = - a) by ring.
      rewrite Hv1 in Hscal.
      exact Hscal.
    }
    assert (Hg2 : is_derive (fun x => b * x) x b).
    { assert (Hscal : is_derive (fun x => b * x) x (b * 1)).
      { apply (is_derive_scal id x b 1).
        change (is_derive (fun t : R => t) x one).
        apply (is_derive_id (K := R_AbsRing)). }
      assert (Hv1 : b * 1 = b) by ring.
      rewrite Hv1 in Hscal.
      exact Hscal.
    }
    assert (Hexp1 : is_derive (fun x => exp (- a * x)) x (- a * exp (- a * x))).
    { apply (is_derive_comp exp (fun x => - a * x) x (exp (- a * x)) (- a)).
      - apply is_derive_exp.
      - exact Hg1.
    }
    assert (Hsin1 : is_derive (fun x => sin (b * x)) x (b * cos (b * x))).
    { apply (is_derive_comp sin (fun x => b * x) x (cos (b * x)) b).
      - apply is_derive_sin.
      - exact Hg2.
    }
    assert (Hcos1 : is_derive (fun x => cos (b * x)) x (- b * sin (b * x))).
    { assert (Hcomp : is_derive (fun x => cos (b * x)) x (b * (- sin (b * x)))).
      { apply (is_derive_comp cos (fun x => b * x) x (- sin (b * x)) b).
        - apply is_derive_cos.
        - exact Hg2. }
      assert (Hv3 : b * (- sin (b * x)) = - b * sin (b * x)) by ring.
      rewrite <- Hv3; exact Hcomp.
    }
    assert (Hexpcos : is_derive (fun x => exp (- a * x) * (- a * sin (b * x) - b * cos (b * x))) x
              ((- a * exp (- a * x)) * (- a * sin (b * x) - b * cos (b * x)) +
               exp (- a * x) * (- a * (b * cos (b * x)) - b * (- b * sin (b * x))))).
    { apply (is_derive_mult (fun x => exp (- a * x)) (fun x => - a * sin (b * x) - b * cos (b * x)) x
             (- a * exp (- a * x))
             (- a * (b * cos (b * x)) - b * (- b * sin (b * x)))).
      - exact Hexp1.
      - apply (is_derive_minus (fun x => - a * sin (b * x)) (fun x => b * cos (b * x)) x
               (- a * (b * cos (b * x))) (b * (- b * sin (b * x)))).
        + apply (is_derive_scal (fun x => sin (b * x)) x (- a) (b * cos (b * x))).
          exact Hsin1.
        + apply (is_derive_scal (fun x => cos (b * x)) x b (- b * sin (b * x))).
          exact Hcos1.
      - intros n m; apply Rmult_comm.
    }
    assert (HderF' : is_derive F x (/ (a * a + b * b) *
        ((- a * exp (- a * x)) * (- a * sin (b * x) - b * cos (b * x)) +
         exp (- a * x) * (- a * (b * cos (b * x)) - b * (- b * sin (b * x)))))).
    { unfold F.
      apply (is_derive_scal (fun x => exp (- a * x) * (- a * sin (b * x) - b * cos (b * x))) x
             (/ (a * a + b * b)) _ Hexpcos). }
    assert (Hv : / (a * a + b * b) *
        ((- a * exp (- a * x)) * (- a * sin (b * x) - b * cos (b * x)) +
         exp (- a * x) * (- a * (b * cos (b * x)) - b * (- b * sin (b * x)))) =
        exp (- a * x) * sin (b * x)).
    { field; exact Hden. }
    rewrite <- Hv; exact HderF'.
  - intros x Hx.
    apply continuous_exp_sin.
Qed.

(* ∫₀^∞ e^{-ax}sin(bx)dx = b/(a²+b²)（a>0） *)
Lemma RInt_gen_exp_sin : forall a b : R, 0 < a ->
  is_RInt_gen (fun x => exp (- a * x) * sin (b * x)) (at_right 0) (Rbar_locally p_infty)
    (b / (a * a + b * b)).
Proof.
  intros a b Ha.
  assert (Hden : a * a + b * b <> 0).
  { apply Rgt_not_eq.
    assert (Haa : 0 < a * a) by (apply Rmult_lt_0_compat; exact Ha; exact Ha).
    assert (Hbb : 0 <= b * b) by (apply Rle_0_sqr).
    lra.
  }
  set (f := fun x => exp (- a * x) * sin (b * x)).
  apply (build_is_RInt_gen f 0 (b / (a * a + b * b))).
  - intros t Ht; unfold f; apply continuous_exp_sin.
  - intros b0 Hb0.
    apply (ex_RInt_continuous f 0 b0).
    intros z Hz; unfold f; apply continuous_exp_sin.
  - (* Hlim_F *)
    assert (Hrim : forall T, RInt f 0 T =
        (exp (- a * T) * (- a * sin (b * T) - b * cos (b * T)) + b) / (a * a + b * b)).
    { intros T. unfold f. apply is_RInt_unique. apply is_RInt_exp_sin; exact Ha. }
    assert (HlimV : filterlim
        (fun T => (exp (- a * T) * (- a * sin (b * T) - b * cos (b * T)) + b) / (a * a + b * b))
        (Rbar_locally p_infty) (locally (b / (a * a + b * b)))).
    {
      assert (Hden_pos : 0 < a * a + b * b).
      { assert (Haa : 0 < a * a) by (apply Rmult_lt_0_compat; exact Ha; exact Ha).
        assert (Hbb : 0 <= b * b) by (apply Rle_0_sqr).
        lra. }
      assert (HlimE : filterlim (fun T => exp (- a * T) * (- a * sin (b * T) - b * cos (b * T)))
                        (Rbar_locally p_infty) (locally 0)).
      { apply filterlim_exp_scal_bounded.
        - exact Ha.
        - exists (Rabs a + Rabs b).
          split.
          * apply Rplus_le_le_0_compat; apply Rabs_pos.
          * intros t.
            apply Rle_trans with (Rabs (- a * sin (b * t)) + Rabs (b * cos (b * t))).
            -- rewrite <- (Rabs_Ropp (b * cos (b * t))).
               apply Rabs_triang.
            -- apply Rplus_le_compat.
               ++ rewrite Rabs_mult, Rabs_Ropp.
                  apply Rle_trans with (Rabs a * 1).
                  ** apply Rmult_le_compat_l; [apply Rabs_pos | apply Rabs_sin_le_1].
                  ** rewrite Rmult_1_r; apply Rle_refl.
               ++ rewrite Rabs_mult.
                  apply Rle_trans with (Rabs b * 1).
                  ** apply Rmult_le_compat_l; [apply Rabs_pos | apply Rabs_cos_le_1].
                  ** rewrite Rmult_1_r; apply Rle_refl.
      }
      unfold filterlim.
      intros P HP.
      destruct (locally_iff_open_ball (b / (a * a + b * b)) P) as [Hiff _].
      destruct (Hiff HP) as [eps [Heps_pos Hball]].
      assert (Heps' : 0 < eps * (a * a + b * b)).
      { apply Rmult_lt_0_compat; [exact Heps_pos | exact Hden_pos]. }
      specialize (HlimE (fun y => Rabs y < eps * (a * a + b * b))).
      assert (HlocE : locally 0 (fun y : R => Rabs y < eps * (a * a + b * b))).
      { apply locally_iff_open_ball; exists (eps * (a * a + b * b)); split; [exact Heps' | intros y Hy; rewrite Rminus_0_r in Hy; exact Hy]. }
      destruct (HlimE HlocE) as [M HM].
      unfold Rbar_locally.
      exists M.
      intros T HT.
      apply Hball.
      unfold ball, AbsRing_ball; simpl.
      change (Rabs ((exp (- a * T) * (- a * sin (b * T) - b * cos (b * T)) + b) / (a * a + b * b)
                    - b / (a * a + b * b)) < eps).
      replace ((exp (- a * T) * (- a * sin (b * T) - b * cos (b * T)) + b) / (a * a + b * b)
               - b / (a * a + b * b))
        with ((exp (- a * T) * (- a * sin (b * T) - b * cos (b * T))) / (a * a + b * b))
        by (field; exact Hden).
      rewrite Rabs_div; [| exact Hden].
      rewrite Rabs_pos_eq with (x := a * a + b * b); [| apply Rlt_le; exact Hden_pos].
      apply Rmult_lt_reg_l with (a * a + b * b).
      - exact Hden_pos.
      - replace ((a * a + b * b) * (Rabs (exp (- a * T) * (- a * sin (b * T) - b * cos (b * T))) / (a * a + b * b)))
          with (Rabs (exp (- a * T) * (- a * sin (b * T) - b * cos (b * T)))) by (field; exact Hden).
        replace ((a * a + b * b) * eps) with (eps * (a * a + b * b)) by (apply Rmult_comm).
        exact (HM T HT).
    }
    apply (filterlim_ext
             (fun T => (exp (- a * T) * (- a * sin (b * T) - b * cos (b * T)) + b) / (a * a + b * b))
             (fun T => RInt f 0 T)).
    + intros T; symmetry; apply Hrim.
    + exact HlimV.
  - (* Hdelta *)
    intros eps.
    set (F0 := fun x => (exp (- a * x) * (- a * sin (b * x) - b * cos (b * x)) + b) / (a * a + b * b)).
    assert (Hcont0 : continuous F0 0).
    { unfold F0.
      apply continuity_pt_to_continuous_simple.
      apply continuity_pt_mult.
      - apply continuity_pt_plus.
        + apply continuity_pt_mult.
          * apply (continuity_pt_comp (fun t => - a * t) exp 0).
            -- apply continuity_pt_scal_id.
            -- apply derivable_continuous; apply derivable_exp.
          * apply continuity_pt_minus.
            -- apply continuity_pt_mult; [apply continuity_pt_const_R |
                 apply (continuity_pt_comp (fun t => b * t) sin 0)].
               ++ apply continuity_pt_scal_id.
               ++ apply continuity_sin.
            -- apply continuity_pt_mult; [apply continuity_pt_const_R |
                 apply (continuity_pt_comp (fun t => b * t) cos 0)].
               ++ apply continuity_pt_scal_id.
               ++ apply continuity_cos.
        + apply continuity_pt_const_R.
      - apply continuity_pt_const_R.
    }
    assert (H0 : F0 0 = 0).
    { unfold F0.
      replace (- a * 0) with 0 by ring.
      replace (b * 0) with 0 by ring.
      rewrite exp_0, sin_0, cos_0.
      field; exact Hden. }
    assert (Hloc0 : locally 0 (fun x => Rabs (F0 x) < pos eps)).
    {
      assert (Hloc0' : locally 0 (fun x => Rabs (F0 x - F0 0) < pos eps)).
      {
        assert (HlocP : locally (F0 0) (fun y => Rabs (y - F0 0) < pos eps)).
        { apply locally_iff_open_ball; exists (pos eps); split; [apply cond_pos | intros y Hy; exact Hy]. }
        apply (Hcont0 (fun y => Rabs (y - F0 0) < pos eps) HlocP).
      }
      apply (filter_imp (fun x => Rabs (F0 x - F0 0) < pos eps)
                        (fun x => Rabs (F0 x) < pos eps)).
      - intros x Hx.
        rewrite H0 in Hx.
        rewrite Rminus_0_r in Hx.
        exact Hx.
      - exact Hloc0'.
    }
    destruct (locally_iff_open_ball 0 (fun x => Rabs (F0 x) < pos eps)) as [Hiff _].
    destruct (Hiff Hloc0) as [delta [Hdelta_pos Hdelta_ball]].
    exists (mkposreal delta Hdelta_pos).
    intros x Hx_abs Hx_ge.
    assert (Hex0x : ex_RInt f 0 x).
    { apply (ex_RInt_continuous f 0 x); intros z Hz; unfold f; apply continuous_exp_sin. }
    assert (Hexx0 : ex_RInt f x 0).
    { apply (ex_RInt_continuous f x 0); intros z Hz; unfold f; apply continuous_exp_sin. }
    rewrite <- (opp_RInt_swap f 0 x Hex0x).
    rewrite Rabs_Ropp.
    assert (Hfx : RInt f 0 x = F0 x).
    { apply is_RInt_unique. unfold f. apply is_RInt_exp_sin; exact Ha. }
    rewrite Hfx.
    apply Hdelta_ball.
    simpl; exact Hx_abs.
Qed.

(* ============ 3. atan 的极限 ============ *)

(* atan(c·x) → PI/2 当 x → +∞（c > 0） *)
Lemma filterlim_atan_scal_p_infty : forall c : R, 0 < c ->
  filterlim (fun x => atan (c * x)) (Rbar_locally p_infty) (locally (PI / 2)).
Proof.
  intros c Hc.
  unfold filterlim.
  intros P HP.
  destruct (locally_iff_open_ball (PI / 2) P) as [Hiff _].
  destruct (Hiff HP) as [eps [Heps_pos Hball]].
  assert (Hcont_atan0 : continuity_pt atan 0).
  { apply derivable_continuous_pt; apply derivable_pt_atan. }
  unfold continuity_pt, continue_in, limit1_in, limit_in in Hcont_atan0.
  simpl in Hcont_atan0.
  destruct (Hcont_atan0 eps Heps_pos) as [delta [Hdelta_pos Hdelta_cond]].
  assert (Hdelta_main : forall y, Rabs (y - 0) < delta -> Rabs (atan y - atan 0) < eps).
  { intros y Hy.
    destruct (Req_dec y 0) as [Hy0 | Hyn0].
    - subst y.
      rewrite (Rminus_diag (atan 0)), Rabs_R0.
      exact Heps_pos.
    - apply Hdelta_cond.
      split.
      + unfold D_x, no_cond; split; [trivial | symmetry; exact Hyn0].
      + change (Rdist y 0 < delta).
        exact Hy.
  }
  exists (/ (c * delta)).
  intros x Hx.
  apply Hball.
  unfold ball, AbsRing_ball; simpl.
  change (Rabs (atan (c * x) - PI / 2) < eps).
  assert (Hcx_pos : 0 < c * x).
  { apply Rmult_lt_0_compat; [exact Hc |].
    apply Rlt_trans with (/ (c * delta)).
    - apply Rinv_0_lt_compat.
      apply Rmult_lt_0_compat; [exact Hc | exact Hdelta_pos].
    - exact Hx.
  }
  assert (Hswap : atan (c * x) - PI / 2 = - (PI / 2 - atan (c * x))) by lra.
  rewrite Hswap.
  rewrite Rabs_Ropp.
  rewrite <- (atan_inv (c * x) Hcx_pos).
  replace (atan (/ (c * x))) with (atan (/ (c * x)) - 0) by lra.
  rewrite <- atan_0.
  apply Hdelta_main.
  rewrite Rminus_0_r.
  rewrite Rabs_pos_eq; [| apply Rlt_le; apply Rinv_0_lt_compat; exact Hcx_pos].
  rewrite <- (Rinv_inv delta).
  apply Rinv_lt_contravar.
  - apply Rmult_lt_0_compat; [apply Rinv_0_lt_compat; exact Hdelta_pos | exact Hcx_pos].
  - assert (Heq : / delta = c * (/ (c * delta))).
    { field. split; [apply Rgt_not_eq; exact Hdelta_pos | apply Rgt_not_eq; exact Hc]. }
    rewrite Heq.
    apply Rmult_lt_compat_l; [exact Hc | exact Hx].
Qed.

(* atan(c·x) → -PI/2 当 x → -∞（c > 0） *)
Lemma filterlim_atan_scal_m_infty : forall c : R, 0 < c ->
  filterlim (fun x => atan (c * x)) (Rbar_locally m_infty) (locally (- (PI / 2))).
Proof.
  intros c Hc.
  apply filterlim_ext with (f := fun x => - atan (c * - x)).
  - intros x.
    assert (Hneg : c * - x = - (c * x)) by ring.
    rewrite Hneg.
    rewrite atan_opp.
    ring.
  - apply filterlim_comp with (f := fun x => - x) (g := fun y => - atan (c * y))
                              (G := Rbar_locally p_infty) (H := locally (- (PI / 2))).
    + unfold filterlim, Rbar_locally.
      intros Q HQ.
      destruct HQ as [M HM].
      exists (- M).
      intros x Hx.
      apply HM.
      lra.
    + apply filterlim_comp with (f := fun y => atan (c * y)) (g := fun z => - z)
                                (G := locally (PI / 2)) (H := locally (- (PI / 2))).
      * apply filterlim_atan_scal_p_infty; exact Hc.
      * apply filterlim_Ropp.
Qed.

(* ============ 4. 双边积分 ∫_{-∞}^∞ dξ/(a² + 4π²ξ²) = 1/(2a) ============ *)

Lemma RInt_gen_atan_bilateral : forall a : R, 0 < a ->
  is_RInt_gen (fun xi => / (a * a + (2 * PI * xi) * (2 * PI * xi)))
              (Rbar_locally m_infty) (Rbar_locally p_infty) (/ (2 * a)).
Proof.
  intros a Ha.
  assert (Hpi : 0 < PI) by apply PI_RGT_0.
  assert (Hden_pos : 0 < 2 * PI * a).
  { apply Rmult_lt_0_compat; [apply Rmult_lt_0_compat; [apply Rlt_0_2 | exact Hpi] | exact Ha]. }
  set (c := 2 * PI / a).
  assert (Hc : 0 < c).
  { unfold c. apply Rdiv_lt_0_compat.
    - apply Rmult_lt_0_compat; [apply Rlt_0_2 | exact Hpi].
    - exact Ha.
  }
  set (F := fun x => atan (c * x) / (2 * PI * a)).
  set (f := fun xi => / (a * a + (2 * PI * xi) * (2 * PI * xi))).
  (* 原函数：F' = f *)
  assert (Hprim : forall x y : R, is_RInt f x y (F y - F x)).
  {
    intros x y.
    apply (is_RInt_derive F f x y).
    - intros t Ht.
      unfold is_derive.
      assert (Hgc : is_derive (fun u => c * u) t (c * 1)).
      { apply (is_derive_scal id t c 1).
        change (is_derive (fun t : R => t) t one).
        apply (is_derive_id (K := R_AbsRing)). }
      assert (Hd3' : is_derive (fun u => atan (c * u)) t (/ (1 + (c * t) * (c * t)) * (c * 1))).
      { assert (Hraw : is_derive (fun u => atan (c * u)) t ((c * 1) * (/ (1 + (c * t) * (c * t))))).
        { apply (is_derive_comp atan (fun u => c * u) t (/ (1 + (c * t) * (c * t))) (c * 1)).
          - apply is_derive_atan.
          - exact Hgc. }
        assert (Hv3 : (c * 1) * (/ (1 + (c * t) * (c * t))) =
                      / (1 + (c * t) * (c * t)) * (c * 1)) by ring.
        rewrite <- Hv3; exact Hraw.
      }
      assert (Hd4' : is_derive F t (/ (2 * PI * a) * (/ (1 + (c * t) * (c * t)) * (c * 1)))).
      { unfold F.
        apply (is_derive_ext
                 (fun u => / (2 * PI * a) * atan (c * u))
                 (fun u => atan (c * u) * / (2 * PI * a))
                 t
                 (/ (2 * PI * a) * (/ (1 + (c * t) * (c * t)) * (c * 1)))).
        - intros u; apply Rmult_comm.
        - apply (is_derive_scal (fun u => atan (c * u)) t (/ (2 * PI * a)) _ Hd3').
      }
      assert (Hval : / (2 * PI * a) * (/ (1 + (c * t) * (c * t)) * (c * 1)) =
                      / (a * a + (2 * PI * t) * (2 * PI * t))).
      { unfold c.
        assert (H1 : a * a + 2 * PI * t * (2 * PI * t) <> 0).
        { apply Rgt_not_eq.
          assert (Haa : 0 < a * a) by (apply Rmult_lt_0_compat; exact Ha; exact Ha).
          assert (Hsq : 0 <= 2 * PI * t * (2 * PI * t)) by (apply Rle_0_sqr).
          lra. }
        assert (H2 : a <> 0) by (apply Rgt_not_eq; exact Ha).
        assert (H3 : 1 + (c * t) * (c * t) <> 0).
        { apply Rgt_not_eq.
          apply Rlt_le_trans with 1; [lra |].
          assert (Hsq : 0 <= (c * t) * (c * t)) by (apply Rle_0_sqr).
          lra. }
        assert (H4 : 2 * PI * a <> 0) by (apply Rgt_not_eq; exact Hden_pos).
        field.
        split; [exact H1 |].
        split; [exact H2 |].
        apply Rgt_not_eq; exact Hpi.
      }
      unfold f.
      rewrite <- Hval.
      exact Hd4'.
    - intros t Ht.
      unfold f.
      apply continuity_pt_to_continuous_simple.
      apply continuity_pt_inv.
      + apply continuity_pt_plus.
        * apply continuity_pt_const_R.
        * apply continuity_pt_mult; [apply continuity_pt_mult; [apply continuity_pt_const_R | apply derivable_continuous_pt; apply derivable_pt_id] |
                                     apply continuity_pt_mult; [apply continuity_pt_const_R | apply derivable_continuous_pt; apply derivable_pt_id]].
      + intros z.
        assert (Hpos : 0 < a * a + (2 * PI * t) * (2 * PI * t)).
        { assert (Haa : 0 < a * a) by (apply Rmult_lt_0_compat; exact Ha; exact Ha).
          assert (Hsq : 0 <= (2 * PI * t) * (2 * PI * t)) by (apply Rle_0_sqr).
          lra. }
        apply Rlt_not_eq in Hpos.
        apply Hpos.
        symmetry; exact z.
  }
  (* f 处处连续 → 处处可积 *)
  assert (Hex : forall x y : R, ex_RInt f x y).
  {
    intros x y.
    apply (ex_RInt_continuous f x y).
    intros z Hz.
    apply continuity_pt_to_continuous_simple.
    apply continuity_pt_inv.
    + apply continuity_pt_plus.
      * apply continuity_pt_const_R.
      * apply continuity_pt_mult; [apply continuity_pt_mult; [apply continuity_pt_const_R | apply derivable_continuous_pt; apply derivable_pt_id] |
                                   apply continuity_pt_mult; [apply continuity_pt_const_R | apply derivable_continuous_pt; apply derivable_pt_id]].
    + intros w.
      assert (Hpos : 0 < a * a + (2 * PI * z) * (2 * PI * z)).
      { assert (Haa : 0 < a * a) by (apply Rmult_lt_0_compat; exact Ha; exact Ha).
        assert (Hsq : 0 <= (2 * PI * z) * (2 * PI * z)) by (apply Rle_0_sqr).
        lra. }
      apply Rlt_not_eq in Hpos.
      apply Hpos.
      symmetry; exact w.
  }
  assert (Hlim_p : filterlim (fun y => atan (c * y)) (Rbar_locally p_infty) (locally (PI / 2)))
    by (apply filterlim_atan_scal_p_infty; exact Hc).
  assert (Hlim_m : filterlim (fun x => atan (c * x)) (Rbar_locally m_infty) (locally (- (PI / 2))))
    by (apply filterlim_atan_scal_m_infty; exact Hc).
  (* F(y) → 1/(4a) as y → +∞ *)
  assert (Htarget_p : filterlim F (Rbar_locally p_infty) (locally (/ (4 * a)))).
  {
    unfold filterlim.
    intros Q HQ.
    destruct (locally_iff_open_ball (/ (4 * a)) Q) as [HiffQ _].
    destruct (HiffQ HQ) as [epsQ [HepsQ_pos HballQ]].
    assert (HepsQ' : 0 < epsQ * (2 * PI * a)).
    { apply Rmult_lt_0_compat; [exact HepsQ_pos | exact Hden_pos]. }
    specialize (Hlim_p (fun y => Rabs (y - PI / 2) < epsQ * (2 * PI * a))).
    assert (HlocP : locally (PI / 2) (fun y : R => Rabs (y - PI / 2) < epsQ * (2 * PI * a))).
    { apply locally_iff_open_ball; exists (epsQ * (2 * PI * a)); split; [exact HepsQ' | intros y Hy; exact Hy]. }
    destruct (Hlim_p HlocP) as [M HM].
    unfold Rbar_locally.
    exists M.
    intros y Hy.
    apply HballQ.
    unfold ball, AbsRing_ball; simpl.
    change (Rabs (F y - / (4 * a)) < epsQ).
    unfold F.
    replace (atan (c * y) / (2 * PI * a) - / (4 * a)) with
            ((atan (c * y) - PI / 2) / (2 * PI * a)) by (field; split; [apply Rgt_not_eq; exact Ha | apply Rgt_not_eq; exact Hpi]).
    rewrite Rabs_div; [| apply Rgt_not_eq; exact Hden_pos].
    rewrite Rabs_pos_eq with (x := 2 * PI * a); [| apply Rlt_le; exact Hden_pos].
    apply Rmult_lt_reg_l with (2 * PI * a).
    - exact Hden_pos.
    - assert (Hne_a : a <> 0) by (apply Rgt_not_eq; exact Ha).
      assert (Hne_pi : PI <> 0) by (apply Rgt_not_eq; exact Hpi).
      replace ((2 * PI * a) * (Rabs (atan (c * y) - PI / 2) / (2 * PI * a)))
        with (Rabs (atan (c * y) - PI / 2)) by (field; split; [exact Hne_a | exact Hne_pi]).
      replace ((2 * PI * a) * epsQ) with (epsQ * (2 * PI * a)) by (apply Rmult_comm).
      exact (HM y Hy).
  }
  (* F(x) → -1/(4a) as x → -∞ *)
  assert (Htarget_m : filterlim F (Rbar_locally m_infty) (locally (- / (4 * a)))).
  {
    unfold filterlim.
    intros Q HQ.
    destruct (locally_iff_open_ball (- / (4 * a)) Q) as [HiffQ _].
    destruct (HiffQ HQ) as [epsQ [HepsQ_pos HballQ]].
    assert (HepsQ' : 0 < epsQ * (2 * PI * a)).
    { apply Rmult_lt_0_compat; [exact HepsQ_pos | exact Hden_pos]. }
    specialize (Hlim_m (fun y => Rabs (y - (- (PI / 2))) < epsQ * (2 * PI * a))).
    assert (HlocP : locally (- (PI / 2)) (fun y : R => Rabs (y - (- (PI / 2))) < epsQ * (2 * PI * a))).
    { apply locally_iff_open_ball; exists (epsQ * (2 * PI * a)); split; [exact HepsQ' | intros y Hy; exact Hy]. }
    destruct (Hlim_m HlocP) as [M HM].
    unfold Rbar_locally.
    exists M.
    intros y Hy.
    apply HballQ.
    unfold ball, AbsRing_ball; simpl.
    change (Rabs (F y - (- / (4 * a))) < epsQ).
    unfold F.
    replace (atan (c * y) / (2 * PI * a) - (- / (4 * a))) with
            ((atan (c * y) - (- (PI / 2))) / (2 * PI * a)) by (field; split; [apply Rgt_not_eq; exact Ha | apply Rgt_not_eq; exact Hpi]).
    rewrite Rabs_div; [| apply Rgt_not_eq; exact Hden_pos].
    rewrite Rabs_pos_eq with (x := 2 * PI * a); [| apply Rlt_le; exact Hden_pos].
    apply Rmult_lt_reg_l with (2 * PI * a).
    - exact Hden_pos.
    - assert (Hne_a : a <> 0) by (apply Rgt_not_eq; exact Ha).
      assert (Hne_pi : PI <> 0) by (apply Rgt_not_eq; exact Hpi).
      replace ((2 * PI * a) * (Rabs (atan (c * y) - (- (PI / 2))) / (2 * PI * a)))
        with (Rabs (atan (c * y) - (- (PI / 2)))) by (field; split; [exact Hne_a | exact Hne_pi]).
      replace ((2 * PI * a) * epsQ) with (epsQ * (2 * PI * a)) by (apply Rmult_comm).
      exact (HM y Hy).
  }
  (* 组装：is_RInt_gen 展开 *)
  unfold is_RInt_gen.
  intros P HP.
  destruct (locally_iff_open_ball (/ (2 * a)) P) as [Hiff _].
  destruct (Hiff HP) as [eps [Heps_pos Hball]].
  assert (Heps2 : 0 < eps / 2) by lra.
  specialize (Htarget_p (fun y => Rabs (y - / (4 * a)) < eps / 2)).
  assert (HlocP : locally (/ (4 * a)) (fun y : R => Rabs (y - / (4 * a)) < eps / 2)).
  { apply locally_iff_open_ball; exists (eps / 2); split; [exact Heps2 | intros y Hy; exact Hy]. }
  destruct (Htarget_p HlocP) as [Mp HMp].
  specialize (Htarget_m (fun y => Rabs (y - (- / (4 * a))) < eps / 2)).
  assert (HlocM : locally (- / (4 * a)) (fun y : R => Rabs (y - (- / (4 * a))) < eps / 2)).
  { apply locally_iff_open_ball; exists (eps / 2); split; [exact Heps2 | intros y Hy; exact Hy]. }
  destruct (Htarget_m HlocM) as [Mm HMm].
  apply (Filter_prod (Rbar_locally m_infty) (Rbar_locally p_infty)
        (fun ab => exists y0, is_RInt f (fst ab) (snd ab) y0 /\ P y0)
        (fun x => Rabs (F x - (- / (4 * a))) < eps / 2)
        (fun y => Rabs (F y - / (4 * a)) < eps / 2)).
  - unfold Rbar_locally; exists Mm; intros x Hx; apply HMm; exact Hx.
  - unfold Rbar_locally; exists Mp; intros y Hy; apply HMp; exact Hy.
  - intros x y Hx Hy.
    exists (F y - F x).
    split.
    + apply Hprim.
    + apply Hball.
      unfold ball, AbsRing_ball; simpl.
      change (Rabs (F y - F x - / (2 * a)) < eps).
      replace (F y - F x - / (2 * a)) with ((F y - / (4 * a)) + (- (F x + / (4 * a))))
        by (field; apply Rgt_not_eq; exact Ha).
      apply Rle_lt_trans with (Rabs (F y - / (4 * a)) + Rabs (- (F x + / (4 * a)))).
      * apply Rabs_triang.
      * apply Rlt_le_trans with (eps / 2 + eps / 2).
        -- apply Rplus_lt_compat.
           ++ exact Hy.
           ++ rewrite Rabs_Ropp.
              replace (F x + / (4 * a)) with (F x - (- / (4 * a))) by (field; apply Rgt_not_eq; exact Ha).
              exact Hx.
        -- lra.
Qed.


(* 连续傅里叶变换（实值函数 → 复值，半轴广义积分） *)
Definition FourierTransform (f : R -> R) (xi : R) : Complex :=
  (RInt_gen (fun t => f t * cos (2 * PI * xi * t)) (at_right 0) (Rbar_locally p_infty)) +i
  (opp (RInt_gen (fun t => f t * sin (2 * PI * xi * t)) (at_right 0) (Rbar_locally p_infty))).

(* 分母 a² + (2πξ)² 非零（a > 0） *)
Lemma fa_den_nonzero : forall a xi : R, 0 < a -> Cnorm_sq (a +i (2 * PI * xi)) <> 0.
Proof.
  intros a xi Ha.
  apply Rgt_not_eq.
  unfold Cnorm_sq, Rsqr; simpl.
  assert (Haa : 0 < a * a) by (apply Rmult_lt_0_compat; exact Ha; exact Ha).
  assert (Hsq : 0 <= (2 * PI * xi) * (2 * PI * xi)) by (apply Rle_0_sqr).
  lra.
Qed.

(* 主定理：F(f_a)(ξ) = 1/(a + 2πiξ)，f_a(t) = e^{-at}·1_{t≥0} *)
Lemma FourierTransform_fa : forall (a xi : R) (Ha : 0 < a),
  FourierTransform (fun t => exp (- a * t)) xi =
    ComplexNumbers.Cinv (a +i (2 * PI * xi)) (fa_den_nonzero a xi Ha).
Proof.
  intros a xi Ha.
  unfold FourierTransform.
  assert (Hcos : RInt_gen (fun t => exp (- a * t) * cos (2 * PI * xi * t))
                          (at_right 0) (Rbar_locally p_infty) =
                 a / (a * a + (2 * PI * xi) * (2 * PI * xi))).
  { eapply is_RInt_gen_unique.
    apply RInt_gen_exp_cos; exact Ha.
  }
  assert (Hsin : RInt_gen (fun t => exp (- a * t) * sin (2 * PI * xi * t))
                          (at_right 0) (Rbar_locally p_infty) =
                 (2 * PI * xi) / (a * a + (2 * PI * xi) * (2 * PI * xi))).
  { eapply is_RInt_gen_unique.
    apply RInt_gen_exp_sin; exact Ha.
  }
  rewrite Hcos.
  rewrite Hsin.
  unfold ComplexNumbers.Cinv, Cnorm_sq; simpl.
  unfold Rsqr; simpl.
  apply Complex_eq; simpl.
  - reflexivity.
  - rewrite <- Rdiv_opp_l.
    reflexivity.
Qed.

(* |C1|² = 1 *)
Lemma Cnorm_sq_C1 : Cnorm_sq ComplexNumbers.C1 = 1.
Proof.
  unfold Cnorm_sq, Rsqr, ComplexNumbers.C1; simpl.
  ring.
Qed.

(* |Cinv z|² = 1/|z|² *)
Lemma Cnorm_sq_Cinv : forall z (H : Cnorm_sq z <> 0), Cnorm_sq (ComplexNumbers.Cinv z H) = / Cnorm_sq z.
Proof.
  intros z H.
  assert (Hm : Cnorm_sq z * Cnorm_sq (ComplexNumbers.Cinv z H) = 1).
  { rewrite <- Cnorm_sq_mul.
    rewrite Cmul_inv_l.
    apply Cnorm_sq_C1.
  }
  apply Rmult_eq_reg_l with (Cnorm_sq z).
  rewrite Hm.
  symmetry; apply Rinv_r.
  exact H.
  exact H.
Qed.

(* Parseval（频域）：∫_{-∞}^∞ |F(f_a)(ξ)|² dξ = 1/(2a) *)
Lemma Parseval_fa_freq : forall (a : R) (Ha : 0 < a),
  RInt_gen (fun xi => Cnorm_sq (FourierTransform (fun t => exp (- a * t)) xi))
           (Rbar_locally m_infty) (Rbar_locally p_infty) = / (2 * a).
Proof.
  intros a Ha.
  assert (Hpt : forall xi,
    Cnorm_sq (FourierTransform (fun t => exp (- a * t)) xi) =
    / (a * a + (2 * PI * xi) * (2 * PI * xi))).
  { intros xi.
    rewrite (FourierTransform_fa a xi Ha).
    rewrite Cnorm_sq_Cinv.
    unfold Cnorm_sq, Rsqr; simpl.
    reflexivity.
  }
  assert (Hex : ex_RInt_gen
      (fun xi => Cnorm_sq (FourierTransform (fun t => exp (- a * t)) xi))
      (Rbar_locally m_infty) (Rbar_locally p_infty)).
  { eapply ex_RInt_gen_ext_eq.
    - intros xi; symmetry; apply Hpt.
    - exists (/ (2 * a)).
      apply RInt_gen_atan_bilateral; exact Ha.
  }
  assert (Hstep : RInt_gen
      (fun xi => Cnorm_sq (FourierTransform (fun t => exp (- a * t)) xi))
      (Rbar_locally m_infty) (Rbar_locally p_infty) =
      RInt_gen (fun xi => / (a * a + (2 * PI * xi) * (2 * PI * xi)))
      (Rbar_locally m_infty) (Rbar_locally p_infty)).
  { eapply (RInt_gen_ext (fun xi => Cnorm_sq (FourierTransform (fun t => exp (- a * t)) xi))
                         (fun xi => / (a * a + (2 * PI * xi) * (2 * PI * xi)))).
    - apply (Filter_prod (Rbar_locally m_infty) (Rbar_locally p_infty)
                         (fun ab => forall x, Rmin (fst ab) (snd ab) < x < Rmax (fst ab) (snd ab) ->
                                    Cnorm_sq (FourierTransform (fun t => exp (- a * t)) x) =
                                    / (a * a + (2 * PI * x) * (2 * PI * x)))
                         (fun _ : R => True) (fun _ : R => True)).
      + apply filter_true; exact (Rbar_locally_filter m_infty).
      + apply filter_true; exact (Rbar_locally_filter p_infty).
      + intros x y _ _ z Hz. exact (Hpt z).
    - exact Hex.
  }
  rewrite Hstep.
  eapply is_RInt_gen_unique.
  apply RInt_gen_atan_bilateral; exact Ha.
Qed.

(* Parseval（时域）：∫₀^∞ |f_a(t)|² dt = ∫₀^∞ e^{-2at}dt = 1/(2a) *)
Lemma Parseval_fa_time : forall (a : R) (Ha : 0 < a),
  RInt_gen (fun t => exp (- (2 * a) * t)) (at_right 0) (Rbar_locally p_infty) = / (2 * a).
Proof.
  intros a Ha.
  assert (Ha2 : 0 < 2 * a) by lra.
  assert (Hcos0 : RInt_gen (fun t => exp (- (2 * a) * t) * cos (0 * t))
                           (at_right 0) (Rbar_locally p_infty) =
                  (2 * a) / ((2 * a) * (2 * a) + 0 * 0)).
  { eapply is_RInt_gen_unique.
    apply RInt_gen_exp_cos; exact Ha2.
  }
  assert (Hex : ex_RInt_gen (fun t => exp (- (2 * a) * t) * cos (0 * t))
                            (at_right 0) (Rbar_locally p_infty)).
  { exists ((2 * a) / ((2 * a) * (2 * a) + 0 * 0)).
    apply RInt_gen_exp_cos; exact Ha2.
  }
  assert (Hstep : RInt_gen (fun t => exp (- (2 * a) * t))
                           (at_right 0) (Rbar_locally p_infty) =
                  RInt_gen (fun t => exp (- (2 * a) * t) * cos (0 * t))
                           (at_right 0) (Rbar_locally p_infty)).
  { eapply (RInt_gen_ext (fun t => exp (- (2 * a) * t))
                         (fun t => exp (- (2 * a) * t) * cos (0 * t))).
    - apply (Filter_prod (at_right 0) (Rbar_locally p_infty)
                         (fun ab => forall t, Rmin (fst ab) (snd ab) < t < Rmax (fst ab) (snd ab) ->
                                    exp (- (2 * a) * t) = exp (- (2 * a) * t) * cos (0 * t))
                         (fun _ : R => True) (fun _ : R => True)).
      + apply filter_true; exact (at_right_proper_filter 0).
      + apply filter_true; exact (Rbar_locally_filter p_infty).
      + intros x y _ _ t Ht.
        assert (H0t : 0 * t = 0) by (apply Rmult_0_l).
        rewrite H0t.
        rewrite cos_0.
        rewrite Rmult_1_r.
        reflexivity.
    - eapply (ex_RInt_gen_ext_eq
                (fun t => exp (- (2 * a) * t) * cos (0 * t))
                (fun t => exp (- (2 * a) * t))).
      + intros t.
        assert (H0t : 0 * t = 0) by (apply Rmult_0_l).
        rewrite H0t.
        rewrite cos_0.
        rewrite Rmult_1_r.
        reflexivity.
      + exact Hex.
  }
  rewrite Hstep.
  rewrite Hcos0.
  assert (Hden : (2 * a) * (2 * a) + 0 * 0 = (2 * a) * (2 * a)).
  { rewrite Rmult_0_l. apply Rplus_0_r. }
  rewrite Hden.
  unfold Rdiv.
  assert (Hnz : 2 * a <> 0) by (apply Rgt_not_eq; exact Ha2).
  rewrite (Rinv_mult (2 * a) (2 * a)).
  rewrite <- Rmult_assoc.
  rewrite (Rinv_r (2 * a) Hnz).
  rewrite Rmult_1_l.
  reflexivity.
Qed.

(* ---------------- 基础界 ---------------- *)

Lemma Rabs_sin_le_abs_nonneg : forall x : R, 0 <= x -> Rabs (sin x) <= Rabs x.
Proof.
  intros x Hx.
  destruct (Req_dec x 0) as [Hx0 | Hxn0].
  - subst x; rewrite sin_0; rewrite Rabs_R0; apply Rle_refl.
  - assert (Hx_pos : 0 < x) by lra.
    destruct (MVT_cor2 sin cos 0 x Hx_pos) as [c [Hmv Hc]].
    * intros c0 Hc0; apply derivable_pt_lim_sin.
    * assert (Hsin : sin x = cos c * x).
      { rewrite sin_0 in Hmv.
        rewrite Rminus_0_r in Hmv.
        replace (x - 0) with x in Hmv by ring.
        exact Hmv. }
      rewrite Hsin.
      rewrite Rabs_mult.
      apply Rle_trans with (1 * Rabs x).
      - apply Rmult_le_compat_r; [apply Rabs_pos | apply Rabs_cos_le_1].
      - rewrite Rmult_1_l; apply Rle_refl.
Qed.

Lemma Rabs_sin_le_abs : forall x : R, Rabs (sin x) <= Rabs x.
Proof.
  intro x.
  destruct (Rle_lt_dec 0 x) as [Hx | Hx].
  - apply Rabs_sin_le_abs_nonneg; exact Hx.
  - assert (He : Rabs (sin x) = Rabs (sin (- x))).
    { rewrite sin_neg. rewrite Rabs_Ropp. reflexivity. }
    apply Rle_trans with (Rabs (- x)).
    + rewrite He.
      apply Rabs_sin_le_abs_nonneg; lra.
    + rewrite Rabs_Ropp. apply Rle_refl.
Qed.

Lemma Rabs_atan_le_abs_nonneg : forall x : R, 0 <= x -> Rabs (atan x) <= Rabs x.
Proof.
  intros x Hx.
  destruct (Req_dec x 0) as [Hx0 | Hxn0].
  - subst x; rewrite atan_0; rewrite Rabs_R0; apply Rle_refl.
  - assert (Hx_pos : 0 < x) by lra.
    destruct (MVT_cor2 atan (fun c => / (1 + c ^ 2)) 0 x Hx_pos) as [c [Hmv Hc]].
    * intros c0 Hc0; apply derivable_pt_lim_atan.
    * assert (Hatan : atan x = / (1 + c ^ 2) * x).
      { rewrite atan_0 in Hmv.
        rewrite Rminus_0_r in Hmv.
        replace (x - 0) with x in Hmv by ring.
        exact Hmv. }
      rewrite Hatan.
      rewrite Rabs_mult.
      apply Rle_trans with (1 * Rabs x).
      - apply Rmult_le_compat_r; [apply Rabs_pos |].
        assert (Hden_ge1 : 1 <= 1 + c ^ 2).
        { replace (c ^ 2) with (c * c) by ring.
          assert (Hsq : 0 <= c * c) by apply Rle_0_sqr.
          lra. }
        assert (Hden_pos : 0 < 1 + c ^ 2).
        { replace (c ^ 2) with (c * c) by ring.
          assert (Hsq : 0 <= c * c) by apply Rle_0_sqr.
          lra. }
        rewrite Rabs_pos_eq.
        * apply Rle_trans with (/ 1).
          -- apply Rinv_le_contravar; [lra | exact Hden_ge1].
          -- rewrite Rinv_1; apply Rle_refl.
        * apply Rlt_le; apply Rinv_0_lt_compat; exact Hden_pos.
      - rewrite Rmult_1_l; apply Rle_refl.
Qed.

Lemma Rabs_atan_le_abs : forall x : R, Rabs (atan x) <= Rabs x.
Proof.
  intro x.
  destruct (Rle_lt_dec 0 x) as [Hx | Hx].
  - apply Rabs_atan_le_abs_nonneg; exact Hx.
  - assert (He : Rabs (atan x) = Rabs (atan (- x))).
    { rewrite atan_opp. rewrite Rabs_Ropp. reflexivity. }
    apply Rle_trans with (Rabs (- x)).
    + rewrite He.
      apply Rabs_atan_le_abs_nonneg; lra.
    + rewrite Rabs_Ropp. apply Rle_refl.
Qed.

(* ---------------- 极限辅助 ---------------- *)

(* 有界函数 × 趋于 0 → 趋于 0（沿 p_infty） *)
Lemma filterlim_bounded_mul_zero : forall (g h : R -> R),
  filterlim h (Rbar_locally p_infty) (locally 0) ->
  (exists M : R, Rbar_locally p_infty (fun x => Rabs (g x) <= M)) ->
  filterlim (fun x => g x * h x) (Rbar_locally p_infty) (locally 0).
Proof.
  intros g h Hh [M HM].
  unfold filterlim.
  intros P HP.
  destruct (locally_iff_open_ball 0 P) as [Hiff _].
  destruct (Hiff HP) as [eps [Heps_pos Hball]].
  destruct (Rle_lt_dec M 0) as [HMneg | HM_pos].
  - (* M ≤ 0: 最终 g = 0 *)
    destruct HM as [M1 HM1].
    exists M1.
    intros x Hx.
    apply Hball.
    unfold ball, AbsRing_ball; simpl.
    assert (Hg0 : g x = 0).
    { apply Rabs_eq_0.
      apply Rle_antisym.
      - apply Rle_trans with M; [exact (HM1 x Hx) | lra].
      - apply Rabs_pos. }
    rewrite Hg0.
    rewrite Rmult_0_l.
    rewrite Rminus_0_r.
    rewrite Rabs_R0.
    exact Heps_pos.
  - (* M > 0 *)
    assert (HM_pos' : 0 < M) by lra.
    destruct (Hh (fun y => Rabs (y - 0) < eps / M)) as [M2 HM2].
    { apply locally_iff_open_ball; exists (eps / M); split; [apply Rdiv_lt_0_compat; [exact Heps_pos | exact HM_pos'] | intros y Hy; exact Hy]. }
    destruct HM as [M1 HM1].
    exists (Rmax M1 M2).
    intros x Hx.
    apply Hball.
    unfold ball, AbsRing_ball; simpl.
    rewrite Rminus_0_r.
    rewrite Rabs_mult.
    apply Rlt_le_trans with (M * (eps / M)).
    + apply Rle_lt_trans with (M * Rabs (h x)).
      * apply Rmult_le_compat_r; [apply Rabs_pos |].
        apply (HM1 x).
        apply (Rle_lt_trans M1 (Rmax M1 M2) x); [apply Rmax_l | exact Hx].
      * apply Rmult_lt_compat_l; [exact HM_pos' |].
        replace (Rabs (h x)) with (Rabs (h x - 0)) by (rewrite Rminus_0_r; reflexivity).
        apply HM2.
        apply (Rle_lt_trans M2 (Rmax M1 M2) x); [apply Rmax_r | exact Hx].
    + replace (M * (eps / M)) with eps by (unfold Rdiv; field; apply Rgt_not_eq; exact HM_pos').
      apply Rle_refl.
Qed.

(* 1/(1+T²) → 0 *)
Lemma filterlim_1_over_1px2_p_infty :
  filterlim (fun T => / (1 + T * T)) (Rbar_locally p_infty) (locally 0).
Proof.
  unfold filterlim.
  intros P HP.
  destruct (locally_iff_open_ball 0 P) as [Hiff _].
  destruct (Hiff HP) as [eps [Heps_pos Hball]].
  exists (Rmax 1 (/ eps)).
  intros T HT.
  apply Hball.
  unfold ball, AbsRing_ball; simpl.
  rewrite Rminus_0_r.
  assert (HT2 : 0 < T).
  { apply Rlt_trans with (Rmax 1 (/ eps)).
    - apply Rlt_le_trans with 1; [lra | apply Rmax_l].
    - exact HT. }
  assert (Hpos : 0 < 1 + T * T).
  { assert (Hsq : 0 <= T * T) by apply Rle_0_sqr. lra. }
  rewrite Rabs_pos_eq; [| apply Rlt_le; apply Rinv_0_lt_compat; exact Hpos].
  replace (/ (1 + T * T) - 0) with (/ (1 + T * T)) by ring.
  apply Rlt_le_trans with (/ T).
  - (* /(1+T²) < 1/T *)
    apply Rinv_lt_contravar.
    + apply Rmult_lt_0_compat; [exact HT2 | exact Hpos].
    + assert (HT1 : 1 < T).
      { apply (Rle_lt_trans 1 (Rmax 1 (/ eps)) T); [apply Rmax_l | exact HT]. }
      assert (Hle : T <= T * T).
      { apply Rle_trans with (T * 1).
        - rewrite Rmult_1_r; apply Rle_refl.
        - apply Rmult_le_compat_l; [apply Rlt_le; exact HT2 | apply Rlt_le; exact HT1]. }
      lra.
  - (* /T ≤ eps *)
    replace eps with (/ (/ eps)) by (symmetry; rewrite (Rinv_inv eps); reflexivity).
    apply Rlt_le.
    apply Rinv_lt_contravar.
    + apply Rmult_lt_0_compat; [apply Rinv_0_lt_compat; exact Heps_pos | exact HT2].
    + apply (Rle_lt_trans (/ eps) (Rmax 1 (/ eps)) T); [apply Rmax_r | exact HT].
Qed.

(* T/(1+T²) → 0 *)
Lemma filterlim_x_over_1px2_p_infty :
  filterlim (fun T => T / (1 + T * T)) (Rbar_locally p_infty) (locally 0).
Proof.
  unfold filterlim.
  intros P HP.
  destruct (locally_iff_open_ball 0 P) as [Hiff _].
  destruct (Hiff HP) as [eps [Heps_pos Hball]].
  exists (Rmax 1 (/ eps)).
  intros T HT.
  apply Hball.
  unfold ball, AbsRing_ball; simpl.
  rewrite Rminus_0_r.
  assert (HT2 : 0 < T).
  { apply Rlt_trans with (Rmax 1 (/ eps)).
    - apply Rlt_le_trans with 1; [lra | apply Rmax_l].
    - exact HT. }
  assert (Hpos : 0 < 1 + T * T).
  { assert (Hsq : 0 <= T * T) by apply Rle_0_sqr. lra. }
  replace (Rabs (T / (1 + T * T))) with (T / (1 + T * T)) by
    (rewrite Rabs_pos_eq; [reflexivity | apply Rlt_le; unfold Rdiv; apply Rmult_lt_0_compat; [exact HT2 | apply Rinv_0_lt_compat; exact Hpos]]).
  apply Rlt_le_trans with (/ T).
  - (* T/(1+T²) < 1/T：T² < 1 + T² *)
    apply Rmult_lt_reg_l with (1 + T * T); [exact Hpos |].
    replace ((1 + T * T) * (T / (1 + T * T))) with T by (unfold Rdiv; field; apply Rgt_not_eq; exact Hpos).
    apply Rmult_lt_reg_l with T; [exact HT2 |].
    replace (T * ((1 + T * T) * / T)) with (1 + T * T) by (field; apply Rgt_not_eq; exact HT2).
    assert (Hsq : 0 <= T * T) by apply Rle_0_sqr.
    lra.
  - (* /T ≤ eps *)
    replace eps with (/ (/ eps)) by (symmetry; rewrite (Rinv_inv eps); reflexivity).
    apply Rlt_le.
    apply Rinv_lt_contravar.
    + apply Rmult_lt_0_compat; [apply Rinv_0_lt_compat; exact Heps_pos | exact HT2].
    + apply (Rle_lt_trans (/ eps) (Rmax 1 (/ eps)) T); [apply Rmax_r | exact HT].
Qed.

(* 和/数乘的组合极限 *)
Lemma filterlim_sum_comp : forall (f g : R -> R) (lf lg : R) (F : (R -> Prop) -> Prop),
  Filter F ->
  filterlim f F (locally lf) -> filterlim g F (locally lg) ->
  filterlim (fun x => f x + g x) F (locally (lf + lg)).
Proof.
  intros f g lf lg F HF Hf Hg.
  apply (filterlim_ext (fun x => fst (f x, g x) + snd (f x, g x)) (fun x => f x + g x)).
  - intros x; reflexivity.
  - apply (filterlim_comp R (R * R) R
            (fun x => (f x, g x)) (fun z => fst z + snd z) F
            (filter_prod (locally lf) (locally lg)) (locally (lf + lg))).
    + apply (filterlim_pair f g); [exact Hf | exact Hg].
    + apply (filterlim_Rplus lf lg).
Qed.

Lemma filterlim_scal_comp : forall (f : R -> R) (c l : R) (F : (R -> Prop) -> Prop),
  Filter F ->
  filterlim f F (locally l) ->
  filterlim (fun x => c * f x) F (locally (c * l)).
Proof.
  intros f c l F HF Hf.
  apply (filterlim_ext (fun x => fst (c, f x) * snd (c, f x)) (fun x => c * f x)).
  - intros x; reflexivity.
  - apply (filterlim_comp R (R * R) R
            (fun x => (c, f x)) (fun z => fst z * snd z) F
            (filter_prod (locally c) (locally l)) (locally (c * l))).
    + apply (filterlim_pair (fun _ : R => c) f); [apply filterlim_const | exact Hf].
    + apply (filterlim_Rmult c l).
Qed.

Lemma filterlim_opp_comp : forall (f : R -> R) (l : R) (F : (R -> Prop) -> Prop),
  Filter F -> filterlim f F (locally l) -> filterlim (fun x => - f x) F (locally (- l)).
Proof.
  intros f l F HF Hf.
  eapply filterlim_comp; [exact Hf | apply (filterlim_Ropp l)].
Qed.

(* ---------------- 连续性辅助 ---------------- *)

Lemma cont_1px2 : forall t : R, continuous (fun u => / (1 + u * u)) t.
Proof.
  intro t.
  apply continuity_pt_to_continuous_simple.
  apply continuity_pt_inv.
  - apply continuity_pt_plus; [apply continuity_pt_const_R | apply continuity_pt_mult; [apply derivable_continuous_pt; apply derivable_pt_id | apply derivable_continuous_pt; apply derivable_pt_id]].
  - intros z.
    assert (Hpos : 0 < 1 + t * t).
    { assert (Hsq : 0 <= t * t) by apply Rle_0_sqr. lra. }
    apply Rlt_not_eq in Hpos.
    apply Hpos.
    symmetry; exact z.
Qed.

Lemma cont_1px2_sq : forall t : R, continuous (fun u => / ((1 + u * u) * (1 + u * u))) t.
Proof.
  intro t.
  apply continuity_pt_to_continuous_simple.
  apply continuity_pt_inv.
  - apply continuity_pt_mult.
    + apply continuity_pt_plus; [apply continuity_pt_const_R | apply continuity_pt_mult; [apply derivable_continuous_pt; apply derivable_pt_id | apply derivable_continuous_pt; apply derivable_pt_id]].
    + apply continuity_pt_plus; [apply continuity_pt_const_R | apply continuity_pt_mult; [apply derivable_continuous_pt; apply derivable_pt_id | apply derivable_continuous_pt; apply derivable_pt_id]].
  - intros z.
    assert (Hpos : 0 < (1 + t * t) * (1 + t * t)).
    { apply Rmult_lt_0_compat.
      + assert (Hsq : 0 <= t * t) by apply Rle_0_sqr. lra.
      + assert (Hsq : 0 <= t * t) by apply Rle_0_sqr. lra. }
    apply Rlt_not_eq in Hpos.
    apply Hpos.
    symmetry; exact z.
Qed.

(* u/(1+u²)² 的连续性 *)
Lemma cont_u_over_1p2sq : forall t : R, continuous (fun u => u / ((1 + u * u) * (1 + u * u))) t.
Proof.
  intro t.
  unfold Rdiv.
  apply (continuous_mult id (fun u => / ((1 + u * u) * (1 + u * u))) t).
  - apply continuous_id.
  - apply cont_1px2_sq.
Qed.

(* d/du [u/(1+u²)] = (1-u²)/(1+u²)² *)
Lemma is_derive_u_over_1pu2 : forall x : R,
  is_derive (fun u => u / (1 + u * u)) x ((1 - x * x) / ((1 + x * x) * (1 + x * x))).
Proof.
  intro x.
  assert (Hraw : is_derive (fun u => u / (1 + u * u)) x
                   ((1 * (1 + x * x) - x * (2 * x)) / (1 + x * x) ^ 2)).
  { apply (is_derive_div (fun u => u) (fun u => 1 + u * u) x 1 (2 * x)).
    - change (is_derive (fun u : R => u) x one).
      apply (is_derive_id (K := R_AbsRing)).
    - assert (Hd_sq : is_derive (fun u : R => u * u) x (2 * x)).
      { assert (Hraw2 : is_derive (fun u : R => u * u) x (1 * x + x * 1)).
        { apply (is_derive_mult id id x 1 1).
          - change (is_derive (fun u : R => u) x one).
            apply (is_derive_id (K := R_AbsRing)).
          - change (is_derive (fun u : R => u) x one).
            apply (is_derive_id (K := R_AbsRing)).
          - intros n m; apply Rmult_comm. }
        replace (1 * x + x * 1) with (2 * x) in Hraw2 by ring.
        exact Hraw2. }
      assert (Hplus : is_derive (fun u => 1 + u * u) x (0 + 2 * x)).
      { apply (is_derive_plus (fun _ : R => 1) (fun u => u * u) x 0 (2 * x)).
        + change (is_derive (fun _ : R => 1) x zero).
          apply (is_derive_const 1 x).
        + exact Hd_sq. }
      replace (0 + 2 * x) with (2 * x) in Hplus by ring.
      exact Hplus.
    - apply Rgt_not_eq.
      assert (Hsq : 0 <= x * x) by apply Rle_0_sqr. lra.
  }
  replace ((1 * (1 + x * x) - x * (2 * x)) / (1 + x * x) ^ 2)
    with ((1 - x * x) / ((1 + x * x) * (1 + x * x))) in Hraw.
  - exact Hraw.
  - replace ((1 + x * x) ^ 2) with ((1 + x * x) * (1 + x * x)) by (unfold pow; ring).
    replace (1 * (1 + x * x) - x * (2 * x)) with (1 - x * x) by ring.
    reflexivity.
Qed.

(* (1/2)·((1-x²)/(1+x²)² + 1/(1+x²)) = 1/(1+x²)² *)
Lemma sq1_value_ident : forall x : R,
  (1 / 2) * ((1 - x * x) / ((1 + x * x) * (1 + x * x)) + / (1 + x * x)) =
  / ((1 + x * x) * (1 + x * x)).
Proof.
  intro x.
  field.
  all: try (apply Rgt_not_eq; apply Rmult_lt_0_compat;
            [assert (Hsq : 0 <= x * x) by apply Rle_0_sqr; lra |
             assert (Hsq : 0 <= x * x) by apply Rle_0_sqr; lra]).
  all: try (apply Rgt_not_eq; assert (Hsq : 0 <= x * x) by apply Rle_0_sqr; lra).
  all: lra.
Qed.

(* -(1/2)·(-(2x)/(1+x²)²) = x/(1+x²)² *)
Lemma sq2_value_ident : forall x : R,
  - (1 / 2) * (- (2 * x) / (1 + x * x) ^ 2) = x / ((1 + x * x) * (1 + x * x)).
Proof.
  intro x.
  replace ((1 + x * x) ^ 2) with ((1 + x * x) * (1 + x * x)) by (unfold pow; ring).
  field.
  all: try (apply Rgt_not_eq; apply Rmult_lt_0_compat;
            [assert (Hsq : 0 <= x * x) by apply Rle_0_sqr; lra |
             assert (Hsq : 0 <= x * x) by apply Rle_0_sqr; lra]).
  all: try (apply Rgt_not_eq; assert (Hsq : 0 <= x * x) by apply Rle_0_sqr; lra).
  all: lra.
Qed.

(* (1/2)·/(1+u²) = 1/(2(1+u²)) *)
Lemma inv_2_1px2 : forall u : R, (1 / 2) * / (1 + u * u) = / (2 * (1 + u * u)).
Proof.
  intro u.
  unfold Rdiv.
  assert (Hnz1 : 2 <> 0) by lra.
  assert (Hnz2 : 1 + u * u <> 0) by (apply Rgt_not_eq; assert (Hsq : 0 <= u * u) by apply Rle_0_sqr; lra).
  rewrite (Rinv_mult 2 (1 + u * u)).
  rewrite Rmult_assoc.
  rewrite Rmult_1_l.
  reflexivity.
Qed.

(* ---------------- 1. ∫₀^∞ du/(1+u²) = π/2 ---------------- *)

Lemma RInt_gen_atan_half :
  is_RInt_gen (fun u => / (1 + u * u)) (at_right 0) (Rbar_locally p_infty) (PI / 2).
Proof.
  apply (build_is_RInt_gen (fun u => / (1 + u * u)) 0 (PI / 2)).
  - intros t Ht; apply cont_1px2.
  - intros b Hb.
    apply (ex_RInt_continuous (fun u => / (1 + u * u)) 0 b).
    intros z Hz; apply cont_1px2.
  - (* 极限：RInt f 0 T = atan T - atan 0 = atan T → π/2 *)
    assert (Hprim0 : forall T : R, RInt (fun u => / (1 + u * u)) 0 T = atan T - atan 0).
    { intro T.
      apply is_RInt_unique.
      apply (is_RInt_derive atan (fun u => / (1 + u * u)) 0 T).
      - intros x Hx; apply is_derive_atan.
      - intros x Hx; apply cont_1px2. }
    apply (filterlim_ext (fun T => atan T) (fun T => RInt (fun u => / (1 + u * u)) 0 T)).
    + intro T; rewrite (Hprim0 T); rewrite atan_0; rewrite Rminus_0_r; reflexivity.
    + apply (filterlim_ext (fun T => atan (1 * T)) (fun T => atan T)).
      * intro T; rewrite Rmult_1_l; reflexivity.
      * apply (filterlim_atan_scal_p_infty 1); lra.
  - (* 局部小量：|RInt f x 0| = |atan 0 - atan x| ≤ |x| *)
    intros eps.
    exists (mkposreal (pos eps) (cond_pos eps)).
    intros x Hx Hx_ge0.
    assert (Hprim_x : RInt (fun u => / (1 + u * u)) x 0 = atan 0 - atan x).
    { apply is_RInt_unique.
      apply (is_RInt_derive atan (fun u => / (1 + u * u)) x 0).
      - intros z Hz; apply is_derive_atan.
      - intros z Hz; apply cont_1px2. }
    rewrite Hprim_x.
    rewrite atan_0.
    rewrite Rminus_0_l.
    rewrite Rabs_Ropp.
    apply Rle_lt_trans with (Rabs x).
    + apply Rabs_atan_le_abs.
    + rewrite Rabs_pos_eq; [| lra].
      replace x with (Rabs (x - 0)).
      * exact Hx.
      * rewrite Rabs_pos_eq; [rewrite Rminus_0_r; reflexivity | lra].
Qed.

(* ---------------- 2. ∫₀^∞ du/(1+u²)² = π/4 ---------------- *)

Lemma RInt_gen_sq1 :
  is_RInt_gen (fun u => / ((1 + u * u) * (1 + u * u))) (at_right 0) (Rbar_locally p_infty) (PI / 4).
Proof.
  set (F1 := fun u => (1 / 2) * (u / (1 + u * u) + atan u)).
  apply (build_is_RInt_gen (fun u => / ((1 + u * u) * (1 + u * u))) 0 (PI / 4)).
  - intros t Ht; apply cont_1px2_sq.
  - intros b Hb.
    apply (ex_RInt_continuous (fun u => / ((1 + u * u) * (1 + u * u))) 0 b).
    intros z Hz; apply cont_1px2_sq.
  - (* 极限：RInt f 0 T = F1 T - F1 0 → (1/2)(0 + π/2) = π/4 *)
    assert (Hprim0 : forall T : R, RInt (fun u => / ((1 + u * u) * (1 + u * u))) 0 T = F1 T - F1 0).
    { intro T.
      apply is_RInt_unique.
      apply (is_RInt_derive F1 (fun u => / ((1 + u * u) * (1 + u * u))) 0 T).
      - intros x Hx.
        (* F1' = 1/(1+x²)² *)
        unfold F1.
        assert (Hd_quot : is_derive (fun u => u / (1 + u * u)) x ((1 - x * x) / ((1 + x * x) * (1 + x * x)))).
        { apply is_derive_u_over_1pu2. }
        assert (Hd_plus : is_derive (fun u => u / (1 + u * u) + atan u) x
            ((1 - x * x) / ((1 + x * x) * (1 + x * x)) + / (1 + x * x))).
        { apply (is_derive_plus (fun u => u / (1 + u * u)) atan x
                  ((1 - x * x) / ((1 + x * x) * (1 + x * x))) (/ (1 + x * x))).
          - exact Hd_quot.
          - apply is_derive_atan. }
        assert (Hd_F1 : is_derive F1 x ((1 / 2) * ((1 - x * x) / ((1 + x * x) * (1 + x * x)) + / (1 + x * x)))).
        { unfold F1.
          apply (is_derive_scal (fun u => u / (1 + u * u) + atan u) x (1 / 2) _ Hd_plus). }
        replace ((1 / 2) * ((1 - x * x) / ((1 + x * x) * (1 + x * x)) + / (1 + x * x)))
          with (/ ((1 + x * x) * (1 + x * x))) in Hd_F1 by (symmetry; apply sq1_value_ident).
        exact Hd_F1.
      - intros x Hx; apply cont_1px2_sq.
    }
    assert (HF1_0 : F1 0 = 0).
    { unfold F1; rewrite atan_0.
      replace (0 / (1 + 0 * 0)) with 0 by (unfold Rdiv; rewrite Rmult_0_l; reflexivity).
      rewrite Rplus_0_l; rewrite Rmult_0_r; reflexivity. }
    (* F1 T → (1/2)(0 + π/2) = π/4 *)
    apply (filterlim_ext (fun T => (1 / 2) * (T / (1 + T * T) + atan T)) (fun T => RInt (fun u => / ((1 + u * u) * (1 + u * u))) 0 T)).
    + intro T; rewrite (Hprim0 T); rewrite HF1_0; rewrite Rminus_0_r; reflexivity.
    + assert (Hlim : filterlim (fun T => (1 / 2) * (T / (1 + T * T) + atan T))
                 (Rbar_locally p_infty) (locally ((1 / 2) * (0 + PI / 2)))).
      { apply (filterlim_scal_comp (fun T => T / (1 + T * T) + atan T) (1 / 2) (0 + PI / 2)
                 (Rbar_locally p_infty)).
        * apply Rbar_locally_filter.
        * apply (filterlim_sum_comp (fun T => T / (1 + T * T)) (fun T => atan T) 0 (PI / 2)
                   (Rbar_locally p_infty)).
          -- apply Rbar_locally_filter.
          -- apply filterlim_x_over_1px2_p_infty.
          -- apply (filterlim_ext (fun T => atan (1 * T)) (fun T => atan T)).
             ++ intro T; rewrite Rmult_1_l; reflexivity.
             ++ apply (filterlim_atan_scal_p_infty 1); lra.
      }
      replace ((1 / 2) * (0 + PI / 2)) with (PI / 4) in Hlim by (symmetry; field).
      exact Hlim.
  - (* 局部小量：|RInt f x 0| = |F1 0 - F1 x| = |F1 x| ≤ |x| *)
    intros eps.
    exists (mkposreal (pos eps) (cond_pos eps)).
    intros x Hx Hx_ge0.
    assert (Hprim_x : RInt (fun u => / ((1 + u * u) * (1 + u * u))) x 0 = F1 0 - F1 x).
    { apply is_RInt_unique.
      apply (is_RInt_derive F1 (fun u => / ((1 + u * u) * (1 + u * u))) x 0).
      - intros z Hz.
        unfold F1.
        assert (Hd_quot : is_derive (fun u => u / (1 + u * u)) z ((1 - z * z) / ((1 + z * z) * (1 + z * z)))).
        { apply is_derive_u_over_1pu2. }
        assert (Hd_plus : is_derive (fun u => u / (1 + u * u) + atan u) z
            ((1 - z * z) / ((1 + z * z) * (1 + z * z)) + / (1 + z * z))).
        { apply (is_derive_plus (fun u => u / (1 + u * u)) atan z
                  ((1 - z * z) / ((1 + z * z) * (1 + z * z))) (/ (1 + z * z))).
          - exact Hd_quot.
          - apply is_derive_atan. }
        assert (Hd_F1 : is_derive F1 z ((1 / 2) * ((1 - z * z) / ((1 + z * z) * (1 + z * z)) + / (1 + z * z)))).
        { unfold F1.
          apply (is_derive_scal (fun u => u / (1 + u * u) + atan u) z (1 / 2) _ Hd_plus). }
        replace ((1 / 2) * ((1 - z * z) / ((1 + z * z) * (1 + z * z)) + / (1 + z * z)))
          with (/ ((1 + z * z) * (1 + z * z))) in Hd_F1 by (symmetry; apply sq1_value_ident).
        exact Hd_F1.
      - intros z Hz; apply cont_1px2_sq.
    }
    rewrite Hprim_x.
    assert (HF1_0 : F1 0 = 0).
    { unfold F1; rewrite atan_0.
      replace (0 / (1 + 0 * 0)) with 0 by (unfold Rdiv; rewrite Rmult_0_l; reflexivity).
      rewrite Rplus_0_l; rewrite Rmult_0_r; reflexivity. }
    rewrite HF1_0.
    rewrite Rminus_0_l.
    assert (Hbound : Rabs (F1 x) <= Rabs x).
    { unfold F1.
      apply Rle_trans with ((1 / 2) * (Rabs (x / (1 + x * x)) + Rabs (atan x))).
      - rewrite Rabs_mult.
        replace (Rabs (1 / 2)) with (1 / 2) by (rewrite Rabs_pos_eq; [reflexivity | lra]).
        apply Rmult_le_compat_l; [lra |].
        apply Rabs_triang.
      - apply Rle_trans with ((1 / 2) * (Rabs x + Rabs x)).
        * apply Rmult_le_compat_l; [lra |].
          apply Rplus_le_compat.
          + rewrite Rabs_div; [| apply Rgt_not_eq; assert (Hsq : 0 <= x * x) by apply Rle_0_sqr; lra].
            rewrite (Rabs_pos_eq (1 + x * x) (Rplus_le_le_0_compat 1 (x * x) (Rle_0_1) (Rle_0_sqr x))).
            apply Rle_trans with (Rabs x * 1).
            -- apply Rmult_le_compat_l; [apply Rabs_pos |].
               apply Rle_trans with (/ 1).
               ++ apply Rinv_le_contravar; [lra |].
                  assert (Hsq : 0 <= x * x) by apply Rle_0_sqr. lra.
               ++ rewrite Rinv_1; apply Rle_refl.
            -- rewrite Rmult_1_r; apply Rle_refl.
          + apply Rabs_atan_le_abs.
        * replace (Rabs x + Rabs x) with (2 * Rabs x) by ring.
          replace ((1 / 2) * (2 * Rabs x)) with (Rabs x) by (field; lra).
          apply Rle_refl.
    }
    apply Rle_lt_trans with (Rabs x).
    + rewrite Rabs_Ropp; exact Hbound.
    + rewrite Rabs_pos_eq; [| lra].
      replace x with (Rabs (x - 0)).
      * exact Hx.
      * rewrite Rabs_pos_eq; [rewrite Rminus_0_r; reflexivity | lra].
Qed.

(* ---------------- 3. ∫₀^∞ u du/(1+u²)² = 1/2 ---------------- *)

Lemma RInt_gen_sq2 :
  is_RInt_gen (fun u => u / ((1 + u * u) * (1 + u * u))) (at_right 0) (Rbar_locally p_infty) (/ 2).
Proof.
  set (F2 := fun u => - / (2 * (1 + u * u))).
  apply (build_is_RInt_gen (fun u => u / ((1 + u * u) * (1 + u * u))) 0 (/ 2)).
  - intros t Ht.
    apply cont_u_over_1p2sq.
  - intros b Hb.
    apply (ex_RInt_continuous (fun u => u / ((1 + u * u) * (1 + u * u))) 0 b).
    intros z Hz.
    apply cont_u_over_1p2sq.
  - (* 极限：RInt f 0 T = F2 T - F2 0 → 0 - (-1/2) = 1/2 *)
    assert (Hprim0 : forall T : R, RInt (fun u => u / ((1 + u * u) * (1 + u * u))) 0 T = F2 T - F2 0).
    { intro T.
      apply is_RInt_unique.
      apply (is_RInt_derive F2 (fun u => u / ((1 + u * u) * (1 + u * u))) 0 T).
      - intros x Hx.
        unfold F2.
        assert (Hd_inv : is_derive (fun u => / (1 + u * u)) x (- (2 * x) / (1 + x * x) ^ 2)).
        { apply (is_derive_inv (fun u => 1 + u * u) x (2 * x)).
          - assert (Hd_sq : is_derive (fun u : R => u * u) x (2 * x)).
            { assert (Hraw : is_derive (fun u : R => u * u) x (1 * x + x * 1)).
              { apply (is_derive_mult id id x 1 1).
                - change (is_derive (fun u : R => u) x one).
                  apply (is_derive_id (K := R_AbsRing)).
                - change (is_derive (fun u : R => u) x one).
                  apply (is_derive_id (K := R_AbsRing)).
                - intros n m; apply Rmult_comm. }
              replace (1 * x + x * 1) with (2 * x) in Hraw by ring.
              exact Hraw. }
            assert (Hplus : is_derive (fun u => 1 + u * u) x (0 + 2 * x)).
            { apply (is_derive_plus (fun _ : R => 1) (fun u => u * u) x 0 (2 * x)).
              + change (is_derive (fun _ : R => 1) x zero).
                apply (is_derive_const 1 x).
              + exact Hd_sq. }
            replace (0 + 2 * x) with (2 * x) in Hplus by ring.
            exact Hplus.
          - apply Rgt_not_eq.
            assert (Hsq : 0 <= x * x) by apply Rle_0_sqr. lra.
        }
        assert (Hd_scal0 : is_derive (fun u => - (1 / 2) * / (1 + u * u)) x
            (- (1 / 2) * (- (2 * x) / (1 + x * x) ^ 2))).
        { apply (is_derive_scal (fun u => / (1 + u * u)) x (- (1 / 2)) _ Hd_inv). }
        assert (Hd_scal : is_derive (fun u => - / (2 * (1 + u * u))) x
            (- (1 / 2) * (- (2 * x) / (1 + x * x) ^ 2))).
        { apply (is_derive_ext (fun u => - (1 / 2) * / (1 + u * u)) (fun u => - / (2 * (1 + u * u)))).
          - intro u.
            rewrite <- Ropp_mult_distr_l.
            apply Ropp_eq_compat.
            apply inv_2_1px2.
          - exact Hd_scal0. }
        apply (is_derive_ext (fun u => - (1 / 2) * / (1 + u * u)) F2 x
                 (x / ((1 + x * x) * (1 + x * x)))).
        + intro u. unfold F2.
          rewrite <- Ropp_mult_distr_l.
          apply Ropp_eq_compat.
          apply inv_2_1px2.
        + replace (- (1 / 2) * (- (2 * x) / (1 + x * x) ^ 2))
            with (x / ((1 + x * x) * (1 + x * x))) in Hd_scal0 by (symmetry; apply sq2_value_ident).
          exact Hd_scal0.
      - intros x Hx.
        apply cont_u_over_1p2sq.
    }
    assert (HF2_0 : F2 0 = - / 2).
    { unfold F2. rewrite Rmult_0_l. rewrite Rplus_0_r. rewrite Rmult_1_r. reflexivity. }
    apply (filterlim_ext (fun T => F2 T - F2 0) (fun T => RInt (fun u => u / ((1 + u * u) * (1 + u * u))) 0 T)).
    + intro T; symmetry; apply (Hprim0 T).
    + (* F2 T → 0; F2 T - F2 0 → -F2 0 = 1/2 *)
      assert (Hlim_F2 : filterlim (fun u : R => F2 u) (Rbar_locally p_infty) (locally 0)).
      { unfold F2.
        apply (filterlim_ext (fun u => - ((1 / 2) * / (1 + u * u))) (fun u => - / (2 * (1 + u * u)))).
        - intro u. apply Ropp_eq_compat. apply inv_2_1px2.
        - assert (Hmid : filterlim (fun u => - ((1 / 2) * / (1 + u * u))) (Rbar_locally p_infty) (locally (- 0))).
          { apply (filterlim_opp_comp (fun u => (1 / 2) * / (1 + u * u)) 0 (Rbar_locally p_infty)).
            + apply Rbar_locally_filter.
            + assert (Hmid2 : filterlim (fun u => (1 / 2) * / (1 + u * u)) (Rbar_locally p_infty) (locally ((1 / 2) * 0))).
              { apply (filterlim_scal_comp (fun u => / (1 + u * u)) (1 / 2) 0 (Rbar_locally p_infty)).
                * apply Rbar_locally_filter.
                * apply filterlim_1_over_1px2_p_infty.
              }
              replace ((1 / 2) * 0) with 0 in Hmid2 by (rewrite Rmult_0_r; reflexivity).
              exact Hmid2.
          }
          replace (- 0) with 0 in Hmid by (rewrite Ropp_0; reflexivity).
          exact Hmid.
      }
      apply (filterlim_ext (fun T => F2 T + - F2 0) (fun T => F2 T - F2 0)).
      * intro T; reflexivity.
      * assert (Hsum : filterlim (fun T => F2 T + - F2 0) (Rbar_locally p_infty) (locally (0 + - F2 0))).
        { apply (filterlim_sum_comp (fun u => F2 u) (fun _ : R => - F2 0) 0 (- F2 0) (Rbar_locally p_infty)).
          -- apply Rbar_locally_filter.
          -- exact Hlim_F2.
          -- apply filterlim_const.
        }
        replace (0 + - F2 0) with (/ 2) in Hsum.
        -- exact Hsum.
        -- unfold F2.
           replace (1 + 0 * 0) with 1 by (rewrite Rmult_0_l; rewrite Rplus_0_r; reflexivity).
           replace (2 * 1) with 2 by (rewrite Rmult_1_r; reflexivity).
           field; lra.
  - (* 局部小量：|RInt f x 0| = |F2 0 - F2 x| = x²/(2(1+x²)) ≤ x/2 < eps *)
    intros eps.
    assert (Hd : 0 < Rmin 1 (2 * pos eps)).
    { apply Rmin_pos; [lra |].
      apply Rmult_lt_0_compat; [lra | exact (cond_pos eps)]. }
    exists (mkposreal (Rmin 1 (2 * pos eps)) Hd).
    intros x Hx Hx_ge0.
    apply Rge_le in Hx_ge0.
    assert (Hprim_x : RInt (fun u => u / ((1 + u * u) * (1 + u * u))) x 0 = F2 0 - F2 x).
    { apply is_RInt_unique.
      apply (is_RInt_derive F2 (fun u => u / ((1 + u * u) * (1 + u * u))) x 0).
      - intros z Hz.
        unfold F2.
        assert (Hd_inv : is_derive (fun u => / (1 + u * u)) z (- (2 * z) / (1 + z * z) ^ 2)).
        { apply (is_derive_inv (fun u => 1 + u * u) z (2 * z)).
          - assert (Hd_sq : is_derive (fun u : R => u * u) z (2 * z)).
            { assert (Hraw : is_derive (fun u : R => u * u) z (1 * z + z * 1)).
              { apply (is_derive_mult id id z 1 1).
                - change (is_derive (fun u : R => u) z one).
                  apply (is_derive_id (K := R_AbsRing)).
                - change (is_derive (fun u : R => u) z one).
                  apply (is_derive_id (K := R_AbsRing)).
                - intros n m; apply Rmult_comm. }
              replace (1 * z + z * 1) with (2 * z) in Hraw by ring.
              exact Hraw. }
            assert (Hplus : is_derive (fun u => 1 + u * u) z (0 + 2 * z)).
            { apply (is_derive_plus (fun _ : R => 1) (fun u => u * u) z 0 (2 * z)).
              + change (is_derive (fun _ : R => 1) z zero).
                apply (is_derive_const 1 z).
              + exact Hd_sq. }
            replace (0 + 2 * z) with (2 * z) in Hplus by ring.
            exact Hplus.
          - apply Rgt_not_eq.
            assert (Hsq : 0 <= z * z) by apply Rle_0_sqr. lra.
        }
        assert (Hd_scal0 : is_derive (fun u => - (1 / 2) * / (1 + u * u)) z
            (- (1 / 2) * (- (2 * z) / (1 + z * z) ^ 2))).
        { apply (is_derive_scal (fun u => / (1 + u * u)) z (- (1 / 2)) _ Hd_inv). }
        assert (Hd_scal : is_derive (fun u => - / (2 * (1 + u * u))) z
            (- (1 / 2) * (- (2 * z) / (1 + z * z) ^ 2))).
        { apply (is_derive_ext (fun u => - (1 / 2) * / (1 + u * u)) (fun u => - / (2 * (1 + u * u)))).
          - intro u.
            rewrite <- Ropp_mult_distr_l.
            apply Ropp_eq_compat.
            apply inv_2_1px2.
          - exact Hd_scal0. }
        apply (is_derive_ext (fun u => - (1 / 2) * / (1 + u * u)) F2 z
                 (z / ((1 + z * z) * (1 + z * z)))).
        + intro u. unfold F2.
          rewrite <- Ropp_mult_distr_l.
          apply Ropp_eq_compat.
          apply inv_2_1px2.
        + replace (- (1 / 2) * (- (2 * z) / (1 + z * z) ^ 2))
            with (z / ((1 + z * z) * (1 + z * z))) in Hd_scal0 by (symmetry; apply sq2_value_ident).
          exact Hd_scal0.
      - intros z Hz.
        apply cont_u_over_1p2sq.
    }
    rewrite Hprim_x.
    assert (Hx_lt_delta : Rabs x < Rmin 1 (2 * pos eps)).
    { replace (Rabs (x - 0)) with (Rabs x) in Hx by (rewrite Rminus_0_r; reflexivity).
      exact Hx. }
    assert (Hx1 : x < 1).
    { apply Rlt_le_trans with (Rmin 1 (2 * pos eps)).
      - replace (Rabs x) with x in Hx_lt_delta by (rewrite Rabs_pos_eq; [reflexivity | exact Hx_ge0]).
        exact Hx_lt_delta.
      - apply Rmin_l. }
    assert (Hx2 : x < 2 * pos eps).
    { apply Rlt_le_trans with (Rmin 1 (2 * pos eps)).
      - replace (Rabs x) with x in Hx_lt_delta by (rewrite Rabs_pos_eq; [reflexivity | exact Hx_ge0]).
        exact Hx_lt_delta.
      - apply Rmin_r. }
    (* |F2 0 - F2 x| = x²/(2(1+x²)) *)
    assert (Hval : Rabs (F2 0 - F2 x) = x * x / (2 * (1 + x * x))).
    { unfold F2.
      replace (1 + 0 * 0) with 1 in |- * by (rewrite Rmult_0_l; rewrite Rplus_0_r; reflexivity).
      assert (Hpos : 0 < 1 + x * x).
      { assert (Hsq : 0 <= x * x) by apply Rle_0_sqr. lra. }
      assert (Hneg : - / (2 * 1) - - / (2 * (1 + x * x)) <= 0).
      { assert (Hinv : / (2 * (1 + x * x)) <= / (2 * 1)).
        { apply Rinv_le_contravar.
          - lra.
          - apply Rmult_le_compat_l; [lra |].
            assert (Hsq : 0 <= x * x) by apply Rle_0_sqr. lra. }
        replace (2 * 1) with 2 in Hinv by (rewrite Rmult_1_r; reflexivity).
        replace (2 * 1) with 2 in |- * by (rewrite Rmult_1_r; reflexivity).
        lra. }
      rewrite Rabs_left1; [| exact Hneg].
      field.
      all: try (apply Rgt_not_eq; apply Rmult_lt_0_compat;
                [lra | assert (Hsq : 0 <= x * x) by apply Rle_0_sqr; lra]).
      all: try (apply Rgt_not_eq; assert (Hsq : 0 <= x * x) by apply Rle_0_sqr; lra).
      all: lra.
    }
    rewrite Hval.
    destruct (Req_dec x 0) as [Hx0 | Hxn0].
    - subst x. field_simplify. lra.
    - assert (Hx_pos : 0 < x).
      { apply Rnot_le_lt.
        intro Hxle0.
        apply Hxn0.
        apply Rle_antisym; [exact Hxle0 | exact Hx_ge0]. }
      (* x²/(2(1+x²)) < x/2 *)
      apply Rlt_le_trans with (x / 2).
      + assert (Hsq0 : 0 <= x * x) by apply Rle_0_sqr.
        assert (Hden : 0 < 2 * (1 + x * x)).
        { apply Rmult_lt_0_compat; [lra |].
          assert (Hs : 0 <= 1 + x * x) by (apply Rplus_le_le_0_compat; [apply Rle_0_1 | exact Hsq0]).
          lra. }
        apply Rmult_lt_reg_l with (2 * (1 + x * x)); [exact Hden |].
        replace ((2 * (1 + x * x)) * (x * x / (2 * (1 + x * x)))) with (x * x)
          by (field; apply Rgt_not_eq; assert (Hs : 0 <= x * x) by apply Rle_0_sqr; lra).
        replace ((2 * (1 + x * x)) * (x / 2)) with (x * (1 + x * x)) by (unfold Rdiv; field; lra).
        apply Rmult_lt_compat_l; [exact Hx_pos |].
        assert (Hs : 1 <= 1 + x * x).
        { assert (Hs2 : 0 <= x * x) by apply Rle_0_sqr. lra. }
        apply Rlt_le_trans with 1; [exact Hx1 | exact Hs].
      + unfold Rdiv.
        apply Rlt_le.
        apply Rlt_le_trans with (2 * pos eps * / 2).
        * apply Rmult_lt_compat_r; [lra | exact Hx2].
        * replace (2 * pos eps * / 2) with (pos eps) by (unfold Rdiv; field; lra).
          apply Rle_refl.
Qed.

(* ---------------- 4. ∫₀^∞ u² du/(1+u²)² = π/4 ---------------- *)

Lemma RInt_gen_sq3 :
  is_RInt_gen (fun u => (u * u) / ((1 + u * u) * (1 + u * u))) (at_right 0) (Rbar_locally p_infty) (PI / 4).
Proof.
  (* u²/(1+u²)² = 1/(1+u²) − 1/(1+u²)² *)
  eapply is_RInt_gen_ext with (f := fun u => / (1 + u * u) - / ((1 + u * u) * (1 + u * u))).
  - apply (Filter_prod (at_right 0) (Rbar_locally p_infty)
        (fun ab => forall u : R,
           Rmin (fst ab) (snd ab) < u < Rmax (fst ab) (snd ab) ->
           / (1 + u * u) - / ((1 + u * u) * (1 + u * u)) =
           (u * u) / ((1 + u * u) * (1 + u * u)))
        (fun _ => True) (fun _ => True)).
    + apply filter_true; apply at_right_proper_filter.
    + apply filter_true; apply Rbar_locally_filter.
    + intros x y Hx Hy u Hu.
      field.
      apply Rgt_not_eq.
      assert (Hsq : 0 <= u * u) by apply Rle_0_sqr. lra.
  - assert (Hm : is_RInt_gen (fun u => / (1 + u * u) - / ((1 + u * u) * (1 + u * u)))
                 (at_right 0) (Rbar_locally p_infty) (PI / 2 - PI / 4)).
    { apply (is_RInt_gen_minus (fun u => / (1 + u * u)) (fun u => / ((1 + u * u) * (1 + u * u)))).
      + apply RInt_gen_atan_half.
      + apply RInt_gen_sq1. }
    replace (PI / 2 - PI / 4) with (PI / 4) in Hm by field.
    exact Hm.
Qed.


(* ============================================================
    第 12 轮（第二部分 + 第三部分）：广义积分存在性机器、
    核函数 IBP 恒等式与边界值（实分析，无围道积分）
    ============================================================ *)
(* 柯西性质 ⇒ 广义积分存在（完备空间 + build_is_RInt_gen） *)
Lemma ex_RInt_gen_cauchy (f : R -> R) (a : R)
  (Hf_cont : forall t, a <= t -> continuous f t)
  (Hf_int_ab : forall b, b >= a -> ex_RInt f a b)
  (Hdelta : forall eps : posreal, exists delta : posreal,
              forall x, Rabs (x - a) < pos delta -> x >= a ->
                        Rabs (RInt f x a) < pos eps)
  (Hcauchy : forall eps : posreal, exists M, forall x y, M <= x -> M <= y ->
              Rabs (RInt f a x - RInt f a y) < pos eps) :
  ex_RInt_gen f (at_right a) (Rbar_locally p_infty).
Proof.
  assert (Hlim : exists l : R,
            filterlim (fun T => RInt f a T) (Rbar_locally p_infty) (locally l)).
  { apply (filterlim_locally_cauchy (U := R_CompleteSpace) (F := Rbar_locally p_infty)
             (fun T : R => RInt f a T)).
    - intro eps.
      destruct (Hcauchy eps) as [M HM].
      exists (fun T => M <= T).
      split.
      + unfold Rbar_locally; exists M; intros y Hy; lra.
      + intros u v Hu Hv.
        unfold ball, AbsRing_ball; simpl.
        change (Rabs (RInt f a v - RInt f a u) < eps).
        rewrite Rabs_minus_sym.
        exact (HM u v Hu Hv).
  }
  destruct Hlim as [l Hl].
  exists l.
  apply (build_is_RInt_gen f a l).
  - intros t Ht. apply Hf_cont. lra.
  - exact Hf_int_ab.
  - exact Hl.
  - exact Hdelta.
Qed.

(* 局部有界（f 在 a 处连续 ⇒ 存在邻域上 |f| ≤ |f a| + 1） *)
Lemma locally_bounded_continuous : forall (f : R -> R) (a : R),
  continuous f a ->
  exists B : R, 0 < B /\
    forall t, a <= t <= a + B -> Rabs (f t) <= Rabs (f a) + 1.
Proof.
  intros f a Hc.
  unfold continuous in Hc.
  assert (Hball : exists eps0 : posreal,
            forall t, ball a eps0 t -> ball (f a) 1 (f t)).
  { apply Hc with (P := ball (f a) 1).
    apply locally_iff_open_ball; exists (mkposreal 1 Rlt_0_1); split; [exact (cond_pos (mkposreal 1 Rlt_0_1)) | intros y Hy; exact Hy]. }
  destruct Hball as [eps0 Heps0].
  exists (pos eps0 / 2).
  split; [apply Rdiv_lt_0_compat; [exact (cond_pos eps0) | lra] |].
  intros t Ht.
  assert (Ht_a : a <= t) by (destruct Ht; lra).
  assert (Ht_b : t <= a + pos eps0 / 2) by (destruct Ht; lra).
  assert (Hball_t : ball a eps0 t).
  { unfold ball, AbsRing_ball; simpl.
    change (Rabs (t - a) < pos eps0).
    assert (Habs : Rabs (t - a) <= pos eps0 / 2).
    { assert (Ht_ge : 0 <= t - a) by lra.
      rewrite Rabs_pos_eq; [lra | exact Ht_ge]. }
    apply Rle_lt_trans with (pos eps0 / 2); [exact Habs |].
    assert (Hhalf : pos eps0 / 2 < pos eps0).
    { apply Rmult_lt_reg_l with 2; [lra |].
      replace (2 * (pos eps0 / 2)) with (pos eps0) by (unfold Rdiv; field; lra).
      replace (2 * pos eps0) with (pos eps0 + pos eps0) by ring.
      assert (Hc0 : 0 < pos eps0) by exact (cond_pos eps0).
      lra. }
    exact Hhalf.
  }
  assert (Hf_abs : Rabs (f t - f a) < 1) by (apply Heps0; exact Hball_t).
  apply Rle_trans with (Rabs (f a) + Rabs (f t - f a)).
  - assert (Heq : f t = f a + (f t - f a)) by lra.
    rewrite Heq at 1; apply Rabs_triang.
  - apply Rplus_le_compat_l; apply Rlt_le; exact Hf_abs.
Qed.

(* [p,q] ⊆ [a,∞) 上的连续性（用于 ex_RInt_continuous 的前提） *)
Lemma cont_on_Rmin_Rmax (h : R -> R) (a : R) :
  (forall t, a <= t -> continuous h t) ->
  forall p q, a <= p -> a <= q ->
  forall z, Rmin p q <= z -> continuous h z.
Proof.
  intros Hh p q Hp Hq z Hz.
  apply Hh.
  apply Rle_trans with (Rmin p q); [apply Rmin_glb; [exact Hp | exact Hq] | exact Hz].
Qed.

(* 比较判定：|f| ≤ g 且 g 可积 ⇒ f 可积 *)
Lemma ex_RInt_gen_abs_le (f g : R -> R) (a : R)
  (Hf_cont : forall t, a <= t -> continuous f t)
  (Hg_cont : forall t, a <= t -> continuous g t)
  (Hg0 : forall t, a <= t -> 0 <= g t)
  (Hfg : forall t, a <= t -> Rabs (f t) <= g t)
  (Hg : ex_RInt_gen g (at_right a) (Rbar_locally p_infty)) :
  ex_RInt_gen f (at_right a) (Rbar_locally p_infty).
Proof.
  apply (ex_RInt_gen_cauchy f a).
  - exact Hf_cont.
  - intros b Hb.
    apply (ex_RInt_continuous f a b).
    intros z Hz; apply Hf_cont.
    rewrite (Rmin_left a b) in Hz; [lra | lra].
  - (* 局部小量 *)
    intro eps.
    assert (Hb : exists B : R, 0 < B /\
              forall t, a <= t <= a + B -> Rabs (f t) <= Rabs (f a) + 1)
      by (apply locally_bounded_continuous; apply Hf_cont; lra).
    destruct Hb as [B [HB_pos HB]].
    set (M := Rabs (f a) + 1).
    assert (HM_pos : 0 < M).
    { unfold M. assert (Hr : 0 <= Rabs (f a)) by apply Rabs_pos. lra. }
    assert (Hdelta0 : 0 < Rmin B (pos eps / M)).
    { apply Rmin_pos; [exact HB_pos | apply Rdiv_lt_0_compat; [exact (cond_pos eps) | exact HM_pos]]. }
    exists (mkposreal (Rmin B (pos eps / M)) Hdelta0).
    intros x Hx Hx_ge_a.
    (* |∫_x^a f| ≤ (a-x)·M < eps *)
    assert (Hf_bnd : forall t, x <= t <= a -> Rabs (f t) <= M).
    { intros t Ht.
      unfold M.
      assert (Ht_a : a <= t <= a + B).
      { split.
        - apply Rle_trans with x; [lra | exact (proj1 Ht)].
        - apply Rle_trans with a; [exact (proj2 Ht) |].
          assert (Hx_a : Rabs (x - a) < Rmin B (pos eps / M)).
          { exact Hx. }
          assert (Hd' : x - a <= B).
          { apply Rle_trans with (Rmin B (pos eps / M)); [lra | apply Rmin_l]. }
          lra. }
      exact (HB t Ht_a). }
    assert (Hval : Rabs (RInt f x a) <= (x - a) * M).
    { assert (Hch : RInt f a x + RInt f x a = RInt f a a).
      { apply (RInt_Chasles f a x a).
        - apply (ex_RInt_continuous f a x); intros z Hz; apply Hf_cont.
          rewrite (Rmin_left a x) in Hz; [lra | lra].
        - apply (ex_RInt_continuous f x a); intros z Hz; apply Hf_cont.
          rewrite (Rmin_right x a) in Hz; [lra | lra]. }
      assert (Haa : RInt f a a = 0).
      { apply is_RInt_unique.
        exact (is_RInt_point f a). }
      assert (Hneg : RInt f x a = - RInt f a x) by lra.
      rewrite Hneg.
      rewrite Rabs_Ropp.
      apply (abs_RInt_le_const f a x M); [lra | | ].
      - apply (ex_RInt_continuous f a x); intros z Hz; apply Hf_cont.
        rewrite (Rmin_left a x) in Hz; [lra | lra].
      - intros t Ht.
        apply HB.
        split.
        + exact (proj1 Ht).
        + apply Rle_trans with x; [exact (proj2 Ht) |].
          assert (Ht0 : 0 <= x - a) by lra.
          assert (Hx_a : Rabs (x - a) < Rmin B (pos eps / M)) by exact Hx.
          rewrite Rabs_pos_eq in Hx_a; [| exact Ht0].
          apply Rlt_le in Hx_a.
          apply Rle_trans with (a + Rmin B (pos eps / M)); [lra | apply Rplus_le_compat_l; apply Rmin_l]. }
    apply Rle_lt_trans with ((x - a) * M).
    - exact Hval.
    - assert (Hax : x - a < pos eps / M).
      { assert (Ht0 : 0 <= x - a) by lra.
        assert (Hd : Rabs (x - a) < Rmin B (pos eps / M)) by exact Hx.
        rewrite Rabs_pos_eq in Hd; [| exact Ht0].
        apply Rlt_le_trans with (Rmin B (pos eps / M)); [exact Hd | apply Rmin_r]. }
      unfold Rdiv.
      apply Rlt_le_trans with ((pos eps / M) * M).
      - apply Rmult_lt_compat_r; [exact HM_pos | exact Hax].
      - replace ((pos eps / M) * M) with (pos eps) by (unfold Rdiv; field; apply Rgt_not_eq; exact HM_pos).
        apply Rle_refl.
  - (* 柯西：|RInt f a x − RInt f a y| ≤ RInt g (min) (max) < eps *)
    intro eps.
    destruct Hg as [lg Hlg].
    assert (Hgi' : forall eps0 : posreal,
              filter_prod (at_right a) (Rbar_locally p_infty)
                (fun ab => exists y0, is_RInt g (fst ab) (snd ab) y0 /\ ball lg eps0 y0)).
    { intro eps0.
      unfold is_RInt_gen in Hlg.
      apply filterlimi_locally; exact Hlg. }
    set (e2 := mkposreal (pos eps / 2) (Rdiv_lt_0_compat (pos eps) 2 (cond_pos eps) Rlt_0_2)).
    destruct (Hgi' e2) as [Q R HQ HR Hcomb].
    destruct HQ as [delta1 Hdelta1].
    destruct HR as [M2 HM2].
    set (x0 := a + pos delta1 / 2).
    assert (Hx0_ball : ball a delta1 x0).
    { unfold x0, ball, AbsRing_ball; simpl.
      change (Rabs (a + pos delta1 / 2 - a) < pos delta1).
      replace (a + pos delta1 / 2 - a) with (pos delta1 / 2) by lra.
      assert (Hhalf : pos delta1 / 2 < pos delta1).
      { apply Rmult_lt_reg_l with 2; [lra |].
        replace (2 * (pos delta1 / 2)) with (pos delta1) by (unfold Rdiv; field; lra).
        replace (2 * pos delta1) with (pos delta1 + pos delta1) by ring.
        assert (Hc0 : 0 < pos delta1) by exact (cond_pos delta1).
        lra. }
      rewrite Rabs_pos_eq; [exact Hhalf | lra]. }
    assert (Hx0_gt : a < x0).
    { unfold x0.
      assert (Hhalf0 : 0 < pos delta1 / 2).
      { apply Rdiv_lt_0_compat; [exact (cond_pos delta1) | lra]. }
      lra. }
    assert (HP1x0 : Q x0) by (apply Hdelta1; [exact Hx0_ball | exact Hx0_gt]).
    assert (HM : forall y, M2 < y -> Rabs (RInt g x0 y - lg) < pos eps / 2).
    { intros y Hy.
      specialize (Hcomb x0 y HP1x0 (HM2 y Hy)) as [y0 [Hy0 Hy0ball]].
      assert (Hy0eq : RInt g x0 y = y0) by (apply is_RInt_unique; exact Hy0).
      rewrite Hy0eq.
      unfold ball in Hy0ball; unfold AbsRing_ball in Hy0ball; simpl in Hy0ball.
      exact Hy0ball. }
    exists (Rmax (a + 1) (M2 + 1)).
    intros x y Hx_ge Hy_ge.
    assert (Hx_big : M2 < x).
    { apply Rlt_le_trans with (Rmax (a + 1) (M2 + 1)); [| exact Hx_ge].
      apply Rlt_le_trans with (M2 + 1); [lra | apply Rmax_r]. }
    assert (Hy_big : M2 < y).
    { apply Rlt_le_trans with (Rmax (a + 1) (M2 + 1)); [| exact Hy_ge].
      apply Rlt_le_trans with (M2 + 1); [lra | apply Rmax_r]. }
    assert (Hx_gt_a : a < x).
    { apply Rlt_le_trans with (Rmax (a + 1) (M2 + 1)); [| exact Hx_ge].
      apply Rlt_le_trans with (a + 1); [lra | apply Rmax_l]. }
    assert (Hy_gt_a : a < y).
    { apply Rlt_le_trans with (Rmax (a + 1) (M2 + 1)); [| exact Hy_ge].
      apply Rlt_le_trans with (a + 1); [lra | apply Rmax_l]. }
    destruct (Rle_dec x y) as [Hxy | Hyx].
    + (* x ≤ y：|∫_a^x − ∫_a^y| = |∫_x^y| ≤ ∫_x^y g = |∫_x^y g| < eps *)
      assert (Hg_ge0_xy : 0 <= RInt g x y).
      { assert (Hex : ex_RInt g x y).
        { apply (ex_RInt_continuous g x y).
          intros z Hz; apply Hg_cont.
          rewrite (Rmin_left x y) in Hz; [lra | lra]. }
        destruct Hex as [l Hl].
        assert (Hlge : 0 <= l).
        { apply (is_RInt_ge_0 g x y l).
          - exact Hxy.
          - exact Hl.
          - intros t Ht; apply Hg0; lra. }
        rewrite (is_RInt_unique g x y l Hl).
        exact Hlge. }
      assert (Hg_small : RInt g x y < pos eps).
      { assert (Hchg : RInt g x0 y - RInt g x0 x = RInt g x y).
        { assert (Hch : RInt g x0 x + RInt g x y = RInt g x0 y).
          { apply (RInt_Chasles g x0 x y).
            - apply (ex_RInt_continuous g x0 x).
              intros z Hz; apply (cont_on_Rmin_Rmax g a Hg_cont x0 x); [lra | lra | exact (proj1 Hz)].
            - apply (ex_RInt_continuous g x y).
              intros z Hz; apply (cont_on_Rmin_Rmax g a Hg_cont x y); [lra | lra | exact (proj1 Hz)]. }
          lra. }
        rewrite <- Hchg.
        apply Rle_lt_trans with (Rabs (RInt g x0 y - RInt g x0 x)).
        - rewrite Rabs_pos_eq; [apply Rle_refl |].
          assert (Hchg2 : RInt g x0 y - RInt g x0 x = RInt g x y) by exact Hchg.
          rewrite Hchg2; exact Hg_ge0_xy.
        - apply Rle_lt_trans with (Rabs (RInt g x0 y - lg) + Rabs (lg - RInt g x0 x)).
          + replace (RInt g x0 y - RInt g x0 x) with
              (RInt g x0 y - lg + (lg - RInt g x0 x)) by lra.
            apply Rabs_triang.
          + apply Rlt_le_trans with (pos eps / 2 + pos eps / 2).
            * apply Rplus_lt_compat.
              -- exact (HM y Hy_big).
              -- rewrite Rabs_minus_sym; exact (HM x Hx_big).
            * lra.
      }
      apply Rle_lt_trans with (RInt g x y).
      * rewrite Rabs_minus_sym.
        assert (Hch : RInt f a y - RInt f a x = RInt f x y).
        { assert (Hch' : RInt f a x + RInt f x y = RInt f a y).
          { apply (RInt_Chasles f a x y).
            - apply (ex_RInt_continuous f a x).
              intros z Hz; apply Hf_cont.
              rewrite (Rmin_left a x) in Hz; [lra | lra].
            - apply (ex_RInt_continuous f x y).
              intros z Hz; apply (cont_on_Rmin_Rmax f a Hf_cont x y); [lra | lra | exact (proj1 Hz)]. }
          lra. }
        rewrite Hch.
        apply Rle_trans with (RInt (fun t => Rabs (f t)) x y).
        -- apply (abs_RInt_le f x y); [exact Hxy |].
           apply (ex_RInt_continuous f x y).
           intros z Hz; apply (cont_on_Rmin_Rmax f a Hf_cont x y); [lra | lra | exact (proj1 Hz)].
        -- apply RInt_le; [exact Hxy | | | intros t Ht; apply Hfg; lra].
           ++ apply (ex_RInt_continuous (fun t => Rabs (f t)) x y).
              intros z Hz.
              apply (continuous_comp f Rabs z).
              ** apply Hf_cont.
                 apply Rle_trans with (Rmin x y); [apply Rmin_glb; [lra | lra] | exact (proj1 Hz)].
              ** apply continuous_Rabs.
           ++ apply (ex_RInt_continuous g x y).
              intros z Hz; apply (cont_on_Rmin_Rmax g a Hg_cont x y); [lra | lra | exact (proj1 Hz)].
      * exact Hg_small.
    + (* y < x：对称 *)
      assert (Hyx_le : y <= x) by lra.
      assert (Hg_ge0_yx : 0 <= RInt g y x).
      { assert (Hex : ex_RInt g y x).
        { apply (ex_RInt_continuous g y x).
          intros z Hz; apply (cont_on_Rmin_Rmax g a Hg_cont y x); [lra | lra | exact (proj1 Hz)]. }
        destruct Hex as [l Hl].
        assert (Hlge : 0 <= l).
        { apply (is_RInt_ge_0 g y x l).
          - exact Hyx_le.
          - exact Hl.
          - intros t Ht; apply Hg0; lra. }
        rewrite (is_RInt_unique g y x l Hl).
        exact Hlge. }
      assert (Hg_small : RInt g y x < pos eps).
      { assert (Hchg : RInt g x0 x - RInt g x0 y = RInt g y x).
        { assert (Hch : RInt g x0 y + RInt g y x = RInt g x0 x).
          { apply (RInt_Chasles g x0 y x).
            - apply (ex_RInt_continuous g x0 y).
              intros z Hz; apply (cont_on_Rmin_Rmax g a Hg_cont x0 y); [lra | lra | exact (proj1 Hz)].
            - apply (ex_RInt_continuous g y x).
              intros z Hz; apply (cont_on_Rmin_Rmax g a Hg_cont y x); [lra | lra | exact (proj1 Hz)]. }
          lra. }
        rewrite <- Hchg.
        apply Rle_lt_trans with (Rabs (RInt g x0 x - RInt g x0 y)).
        - rewrite Rabs_pos_eq; [apply Rle_refl |].
          assert (Hchg2 : RInt g x0 x - RInt g x0 y = RInt g y x) by exact Hchg.
          rewrite Hchg2; exact Hg_ge0_yx.
        - apply Rle_lt_trans with (Rabs (RInt g x0 x - lg) + Rabs (lg - RInt g x0 y)).
          + replace (RInt g x0 x - RInt g x0 y) with
              (RInt g x0 x - lg + (lg - RInt g x0 y)) by lra.
            apply Rabs_triang.
          + apply Rlt_le_trans with (pos eps / 2 + pos eps / 2).
            * apply Rplus_lt_compat.
              -- exact (HM x Hx_big).
              -- rewrite Rabs_minus_sym; exact (HM y Hy_big).
            * lra.
      }
      apply Rle_lt_trans with (RInt g y x).
      * assert (Hch : RInt f a x - RInt f a y = RInt f y x).
        { assert (Hch' : RInt f a y + RInt f y x = RInt f a x).
          { apply (RInt_Chasles f a y x).
            - apply (ex_RInt_continuous f a y).
              intros z Hz; apply Hf_cont.
              rewrite (Rmin_left a y) in Hz; [lra | lra].
            - apply (ex_RInt_continuous f y x).
              intros z Hz; apply (cont_on_Rmin_Rmax f a Hf_cont y x); [lra | lra | exact (proj1 Hz)]. }
          lra. }
        rewrite Hch.
        apply Rle_trans with (RInt (fun t => Rabs (f t)) y x).
        -- apply (abs_RInt_le f y x); [exact Hyx_le |].
           apply (ex_RInt_continuous f y x).
           intros z Hz; apply (cont_on_Rmin_Rmax f a Hf_cont y x); [lra | lra | exact (proj1 Hz)].
        -- apply RInt_le; [exact Hyx_le | | | intros t Ht; apply Hfg; lra].
           ++ apply (ex_RInt_continuous (fun t => Rabs (f t)) y x).
              intros z Hz.
              apply (continuous_comp f Rabs z).
              ** apply Hf_cont.
                 apply Rle_trans with (Rmin y x); [apply Rmin_glb; [lra | lra] | exact (proj1 Hz)].
              ** apply continuous_Rabs.
           ++ apply (ex_RInt_continuous g y x).
              intros z Hz; apply (cont_on_Rmin_Rmax g a Hg_cont y x); [lra | lra | exact (proj1 Hz)].
      * exact Hg_small.
Qed.

(* is_RInt_gen（at_point a 形式）⇒ filterlim (fun y => RInt f a y) *)
Lemma is_RInt_gen_at_point_filterlim : forall (f : R -> R) (a l : R)
  (Fb : (R -> Prop) -> Prop),
  ProperFilter Fb ->
  is_RInt_gen f (at_point a) Fb l ->
  filterlim (fun y => RInt f a y) Fb (locally l).
Proof.
  intros f a l Fb HFb His.
  unfold filterlim.
  intros P HP.
  destruct (locally_iff_open_ball l P) as [Hiff _].
  destruct (Hiff HP) as [eps [Heps_pos Hball]].
  unfold is_RInt_gen in His.
  rewrite filterlimi_locally in His.
  specialize (His (mkposreal eps Heps_pos)).
  (* filter_prod (at_point a) Fb (fun ab => exists z, is_RInt f (fst ab) (snd ab) z /\ ball l eps z) *)
  destruct His as [Q R HQ HR Hcomb].
  (* at_point a Q = Q a *)
  assert (Hcomb_a : forall y, R y -> exists z, is_RInt f a y z /\ ball l eps z).
  { intros y Hy.
    exact (Hcomb a y HQ Hy). }
  apply (filter_imp R (fun y => P (RInt f a y))).
  - intros y Hy.
    change (P (RInt f a y)).
    destruct (Hcomb a y HQ Hy) as [z [Hz Hballz]].
    assert (Hz_eq : RInt f a y = z) by (apply is_RInt_unique; exact Hz).
    rewrite Hz_eq.
    apply Hball.
    unfold ball in Hballz; unfold AbsRing_ball in Hballz; simpl in Hballz.
    exact Hballz.
  - exact HR.
Qed.

(* ============================================================
   第 12 轮（第三部分）：IBP 恒等式与边界引理
   F(γ)=∫₀^∞ cos(γu)/(1+u²)du，G(γ)=∫₀^∞ u sin(γu)/(1+u²)du，
   A(γ)=∫₀^∞ u sin(γu)/(1+u²)²du，B₀(γ)=∫₀^∞ cos(γu)/(1+u²)²du，
   C(γ)=∫₀^∞ u²cos(γu)/(1+u²)²du，B(γ)=2B₀(γ)。
   恒等式（γ>0）：γF=2A、γG=B−F、2C=F−γG、C=F−B₀。
   基础值：F(0)=π/2、A(0)=0、C(0)=π/4、G(0)=0。
   ============================================================ *)

(* |sin x| ≤ 1、|cos x| ≤ 1（由 sin²+cos²=1） *)
Lemma Rabs_sin_le_one : forall x : R, Rabs (sin x) <= 1.
Proof.
  intro x.
  assert (Hs : 0 <= (sin x) * (sin x)) by apply Rle_0_sqr.
  assert (Hc : 0 <= (cos x) * (cos x)) by apply Rle_0_sqr.
  assert (H1 : (sin x) * (sin x) <= 1).
  { assert (Hs2c2 : (sin x) * (sin x) + (cos x) * (cos x) = 1).
    { rewrite <- (sin2_cos2 x).
      unfold Rsqr.
      ring. }
    lra. }
  rewrite <- (Rabs_pos_eq 1 (Rlt_le 0 1 Rlt_0_1)).
  apply (Rsqr_le_abs_0 (sin x) 1).
  replace (Rsqr (sin x)) with ((sin x) * (sin x)) by reflexivity.
  replace (Rsqr 1) with 1 by (unfold Rsqr; rewrite Rmult_1_r; reflexivity).
  exact H1.
Qed.

Lemma Rabs_cos_le_one : forall x : R, Rabs (cos x) <= 1.
Proof.
  intro x.
  assert (Hs : 0 <= (sin x) * (sin x)) by apply Rle_0_sqr.
  assert (Hc : 0 <= (cos x) * (cos x)) by apply Rle_0_sqr.
  assert (H1 : (cos x) * (cos x) <= 1).
  { assert (Hs2c2 : (sin x) * (sin x) + (cos x) * (cos x) = 1).
    { rewrite <- (sin2_cos2 x).
      unfold Rsqr.
      ring. }
    lra. }
  rewrite <- (Rabs_pos_eq 1 (Rlt_le 0 1 Rlt_0_1)).
  apply (Rsqr_le_abs_0 (cos x) 1).
  replace (Rsqr (cos x)) with ((cos x) * (cos x)) by reflexivity.
  replace (Rsqr 1) with 1 by (unfold Rsqr; rewrite Rmult_1_r; reflexivity).
  exact H1.
Qed.

(* 0 ≤ u ⇒ |u·sin(γu)| ≤ u *)
Lemma Rabs_u_sin_le_u : forall gamma u : R, 0 <= u -> Rabs (u * sin (gamma * u)) <= u.
Proof.
  intros gamma u Hu.
  rewrite Rabs_mult.
  rewrite (Rmult_comm (Rabs u) (Rabs (sin (gamma * u)))).
  rewrite (Rabs_pos_eq u Hu).
  assert (Hp : Rabs (sin (gamma * u)) * u <= 1 * u).
  { apply Rmult_le_compat_r; [exact Hu | exact (Rabs_sin_le_one (gamma * u))]. }
  rewrite (Rmult_1_l u) in Hp.
  exact Hp.
Qed.

(* 0 ≤ u ⇒ |u²·cos(γu)| ≤ u² *)
Lemma Rabs_u2_cos_le_u2 : forall gamma u : R, 0 <= u ->
  Rabs ((u * u) * cos (gamma * u)) <= u * u.
Proof.
  intros gamma u Hu.
  rewrite Rabs_mult.
  rewrite (Rmult_comm (Rabs (u * u)) (Rabs (cos (gamma * u)))).
  rewrite (Rabs_pos_eq (u * u) (Rle_0_sqr u)).
  assert (Hp : Rabs (cos (gamma * u)) * (u * u) <= 1 * (u * u)).
  { apply Rmult_le_compat_r; [apply Rle_0_sqr | exact (Rabs_cos_le_one (gamma * u))]. }
  rewrite (Rmult_1_l (u * u)) in Hp.
  exact Hp.
Qed.

(* ---------------- 定义 ---------------- *)

Definition kcos (gamma u : R) : R := cos (gamma * u) / (1 + u * u).
Definition kusin (gamma u : R) : R := u * sin (gamma * u) / (1 + u * u).
Definition kusin_sq (gamma u : R) : R := u * sin (gamma * u) / ((1 + u * u) * (1 + u * u)).
Definition kcos_sq (gamma u : R) : R := cos (gamma * u) / ((1 + u * u) * (1 + u * u)).
Definition ku2cos_sq (gamma u : R) : R := (u * u) * cos (gamma * u) / ((1 + u * u) * (1 + u * u)).

Definition Fcos (gamma : R) : R :=
  RInt_gen (kcos gamma) (at_right 0) (Rbar_locally p_infty).
Definition Gsin (gamma : R) : R :=
  RInt_gen (kusin gamma) (at_right 0) (Rbar_locally p_infty).
Definition Aint (gamma : R) : R :=
  RInt_gen (kusin_sq gamma) (at_right 0) (Rbar_locally p_infty).
Definition B0int (gamma : R) : R :=
  RInt_gen (kcos_sq gamma) (at_right 0) (Rbar_locally p_infty).
Definition Cint (gamma : R) : R :=
  RInt_gen (ku2cos_sq gamma) (at_right 0) (Rbar_locally p_infty).
Definition Bint (gamma : R) : R := 2 * B0int gamma.

(* ---------------- 连续性 ---------------- *)

Lemma cont_sin_scal : forall gamma t : R, continuous (fun u => sin (gamma * u)) t.
Proof.
  intros gamma t.
  apply (continuous_comp (fun u => gamma * u) sin t).
  - apply (continuous_mult (fun _ : R => gamma) id t).
    + apply continuous_const.
    + apply continuous_id.
  - apply continuous_sin.
Qed.

Lemma cont_cos_scal : forall gamma t : R, continuous (fun u => cos (gamma * u)) t.
Proof.
  intros gamma t.
  apply (continuous_comp (fun u => gamma * u) cos t).
  - apply (continuous_mult (fun _ : R => gamma) id t).
    + apply continuous_const.
    + apply continuous_id.
  - apply continuous_cos.
Qed.

Lemma cont_kcos : forall gamma t : R, continuous (kcos gamma) t.
Proof.
  intros gamma t.
  unfold kcos.
  apply (continuous_mult (fun u => cos (gamma * u)) (fun u => / (1 + u * u)) t).
  - apply cont_cos_scal.
  - apply cont_1px2.
Qed.

Lemma cont_kusin : forall gamma t : R, continuous (kusin gamma) t.
Proof.
  intros gamma t.
  unfold kusin.
  apply (continuous_mult (fun u => u * sin (gamma * u)) (fun u => / (1 + u * u)) t).
  - apply (continuous_mult id (fun u => sin (gamma * u)) t).
    + apply continuous_id.
    + apply cont_sin_scal.
  - apply cont_1px2.
Qed.

Lemma cont_kusin_sq : forall gamma t : R, continuous (kusin_sq gamma) t.
Proof.
  intros gamma t.
  unfold kusin_sq.
  apply (continuous_mult (fun u => u * sin (gamma * u)) (fun u => / ((1 + u * u) * (1 + u * u))) t).
  - apply (continuous_mult id (fun u => sin (gamma * u)) t).
    + apply continuous_id.
    + apply cont_sin_scal.
  - apply cont_1px2_sq.
Qed.

Lemma cont_kcos_sq : forall gamma t : R, continuous (kcos_sq gamma) t.
Proof.
  intros gamma t.
  unfold kcos_sq.
  apply (continuous_mult (fun u => cos (gamma * u)) (fun u => / ((1 + u * u) * (1 + u * u))) t).
  - apply cont_cos_scal.
  - apply cont_1px2_sq.
Qed.

Lemma cont_ku2cos_sq : forall gamma t : R, continuous (ku2cos_sq gamma) t.
Proof.
  intros gamma t.
  unfold ku2cos_sq.
  apply (continuous_mult (fun u => (u * u) * cos (gamma * u)) (fun u => / ((1 + u * u) * (1 + u * u))) t).
  - apply (continuous_mult (fun u => u * u) (fun u => cos (gamma * u)) t).
    + apply (continuous_mult id id t); apply continuous_id.
    + apply cont_cos_scal.
  - apply cont_1px2_sq.
Qed.

(* ---------------- 存在性（绝对收敛核） ---------------- *)

Lemma ex_RInt_gen_kcos : forall gamma : R,
  ex_RInt_gen (kcos gamma) (at_right 0) (Rbar_locally p_infty).
Proof.
  intro gamma.
  apply (ex_RInt_gen_abs_le (kcos gamma) (fun u => / (1 + u * u)) 0).
  - intros t Ht; apply cont_kcos.
  - intros t Ht; apply cont_1px2.
  - intros t Ht; apply Rlt_le; apply Rinv_0_lt_compat;
    assert (Hsq : 0 <= t * t) by apply Rle_0_sqr; lra.
  - intros t Ht.
    unfold kcos.
    unfold Rdiv.
    rewrite Rabs_mult.
    rewrite (Rabs_pos_eq (/ (1 + t * t))).
    + assert (Hp : Rabs (cos (gamma * t)) * / (1 + t * t) <= 1 * / (1 + t * t)).
      { apply Rmult_le_compat_r; [apply Rlt_le; apply Rinv_0_lt_compat;
          assert (Hsq : 0 <= t * t) by apply Rle_0_sqr; lra | apply Rabs_cos_le_one]. }
      rewrite (Rmult_1_l (/ (1 + t * t))) in Hp.
      exact Hp.
    + apply Rlt_le; apply Rinv_0_lt_compat;
      assert (Hsq : 0 <= t * t) by apply Rle_0_sqr; lra.
  - exact (ex_intro _ (PI / 2) RInt_gen_atan_half).
Qed.

Lemma ex_RInt_gen_kusin_sq : forall gamma : R,
  ex_RInt_gen (kusin_sq gamma) (at_right 0) (Rbar_locally p_infty).
Proof.
  intro gamma.
  apply (ex_RInt_gen_abs_le (kusin_sq gamma) (fun u => u / ((1 + u * u) * (1 + u * u))) 0).
  - intros t Ht; apply cont_kusin_sq.
  - intros t Ht; apply cont_u_over_1p2sq.
  - intros t Ht.
    assert (Hsq : 0 <= t * t) by apply Rle_0_sqr.
    unfold Rdiv.
    apply Rmult_le_pos; [exact Ht | apply Rlt_le; apply Rinv_0_lt_compat;
      apply Rmult_lt_0_compat; lra].
  - intros t Ht.
    unfold kusin_sq.
    unfold Rdiv.
    rewrite Rabs_mult.
    rewrite (Rabs_pos_eq (/ ((1 + t * t) * (1 + t * t)))).
    + apply Rmult_le_compat_r; [apply Rlt_le; apply Rinv_0_lt_compat;
        apply Rmult_lt_0_compat;
        [assert (Hsq : 0 <= t * t) by apply Rle_0_sqr; lra |
         assert (Hsq : 0 <= t * t) by apply Rle_0_sqr; lra] |].
      exact (Rabs_u_sin_le_u gamma t Ht).
    + apply Rlt_le; apply Rinv_0_lt_compat; apply Rmult_lt_0_compat;
      [assert (Hsq : 0 <= t * t) by apply Rle_0_sqr; lra |
       assert (Hsq : 0 <= t * t) by apply Rle_0_sqr; lra].
  - exact (ex_intro _ (/ 2) RInt_gen_sq2).
Qed.

Lemma ex_RInt_gen_kcos_sq : forall gamma : R,
  ex_RInt_gen (kcos_sq gamma) (at_right 0) (Rbar_locally p_infty).
Proof.
  intro gamma.
  apply (ex_RInt_gen_abs_le (kcos_sq gamma) (fun u => / ((1 + u * u) * (1 + u * u))) 0).
  - intros t Ht; apply cont_kcos_sq.
  - intros t Ht; apply cont_1px2_sq.
  - intros t Ht; apply Rlt_le; apply Rinv_0_lt_compat; apply Rmult_lt_0_compat;
    [assert (Hsq : 0 <= t * t) by apply Rle_0_sqr; lra |
     assert (Hsq : 0 <= t * t) by apply Rle_0_sqr; lra].
  - intros t Ht.
    unfold kcos_sq.
    unfold Rdiv.
    rewrite Rabs_mult.
    rewrite (Rabs_pos_eq (/ ((1 + t * t) * (1 + t * t)))).
    + assert (Hp : Rabs (cos (gamma * t)) * / ((1 + t * t) * (1 + t * t)) <=
                   1 * / ((1 + t * t) * (1 + t * t))).
      { apply Rmult_le_compat_r; [apply Rlt_le; apply Rinv_0_lt_compat; apply Rmult_lt_0_compat;
          [assert (Hsq : 0 <= t * t) by apply Rle_0_sqr; lra |
           assert (Hsq : 0 <= t * t) by apply Rle_0_sqr; lra] | apply Rabs_cos_le_one]. }
      rewrite (Rmult_1_l (/ ((1 + t * t) * (1 + t * t)))) in Hp.
      exact Hp.
    + apply Rlt_le; apply Rinv_0_lt_compat; apply Rmult_lt_0_compat;
      [assert (Hsq : 0 <= t * t) by apply Rle_0_sqr; lra |
       assert (Hsq : 0 <= t * t) by apply Rle_0_sqr; lra].
  - exact (ex_intro _ (PI / 4) RInt_gen_sq1).
Qed.

Lemma ex_RInt_gen_ku2cos_sq : forall gamma : R,
  ex_RInt_gen (ku2cos_sq gamma) (at_right 0) (Rbar_locally p_infty).
Proof.
  intro gamma.
  apply (ex_RInt_gen_abs_le (ku2cos_sq gamma) (fun u => (u * u) / ((1 + u * u) * (1 + u * u))) 0).
  - intros t Ht; apply cont_ku2cos_sq.
  - intros t Ht.
    apply (continuous_mult (fun u => u * u) (fun u => / ((1 + u * u) * (1 + u * u))) t).
    + apply (continuous_mult id id t); apply continuous_id.
    + apply cont_1px2_sq.
  - intros t Ht.
    assert (Hsq : 0 <= t * t) by apply Rle_0_sqr.
    unfold Rdiv.
    apply Rmult_le_pos; [exact Hsq | apply Rlt_le; apply Rinv_0_lt_compat;
      apply Rmult_lt_0_compat; lra].
  - intros t Ht.
    unfold ku2cos_sq.
    unfold Rdiv.
    rewrite Rabs_mult.
    rewrite (Rabs_pos_eq (/ ((1 + t * t) * (1 + t * t)))).
    + apply Rmult_le_compat_r; [apply Rlt_le; apply Rinv_0_lt_compat; apply Rmult_lt_0_compat;
        [assert (Hsq : 0 <= t * t) by apply Rle_0_sqr; lra |
         assert (Hsq : 0 <= t * t) by apply Rle_0_sqr; lra] |].
      exact (Rabs_u2_cos_le_u2 gamma t Ht).
    + apply Rlt_le; apply Rinv_0_lt_compat; apply Rmult_lt_0_compat;
      [assert (Hsq : 0 <= t * t) by apply Rle_0_sqr; lra |
       assert (Hsq : 0 <= t * t) by apply Rle_0_sqr; lra].
  - exact (ex_intro _ (PI / 4) RInt_gen_sq3).
Qed.

(* 零函数可积 *)
Lemma ex_RInt_gen_zero_fun : ex_RInt_gen (fun _ : R => 0) (at_right 0) (Rbar_locally p_infty).
Proof.
  exists 0.
  unfold is_RInt_gen.
  rewrite filterlimi_locally.
  intro eps0.
  apply (Filter_prod (at_right 0) (Rbar_locally p_infty)
           (fun ab : R * R => exists z, is_RInt (fun _ : R => 0) (fst ab) (snd ab) z /\ ball 0 eps0 z)
           (fun _ : R => True) (fun _ : R => True)).
  - exists (mkposreal 1 Rlt_0_1).
    intros x Hx Hx0.
    trivial.
  - exists 0; intros y Hy; trivial.
  - intros x y Hx Hy.
    exists 0.
    split.
    + assert (Hz : scal (y - x) 0 = 0).
      { change ((y - x) * 0 = 0). rewrite Rmult_0_r. reflexivity. }
      assert (Hc : is_RInt (fun _ : R => 0) x y (scal (y - x) 0)).
      { exact (is_RInt_const x y 0). }
      rewrite Hz in Hc.
      exact Hc.
    + unfold ball, AbsRing_ball; simpl.
      change (Rabs (0 - 0) < pos eps0).
      rewrite Rminus_diag.
      rewrite Rabs_R0.
      exact (cond_pos eps0).
Qed.

(* 零函数的广义积分值恰为 0 *)
Lemma is_RInt_gen_zero_fun : is_RInt_gen (fun _ : R => 0) (at_right 0) (Rbar_locally p_infty) 0.
Proof.
  unfold is_RInt_gen.
  rewrite filterlimi_locally.
  intro eps0.
  apply (Filter_prod (at_right 0) (Rbar_locally p_infty)
           (fun ab : R * R => exists z, is_RInt (fun _ : R => 0) (fst ab) (snd ab) z /\ ball 0 eps0 z)
           (fun _ : R => True) (fun _ : R => True)).
  - exists (mkposreal 1 Rlt_0_1).
    intros x Hx Hx0.
    trivial.
  - exists 0; intros y Hy; trivial.
  - intros x y Hx Hy.
    exists 0.
    split.
    + assert (Hz : scal (y - x) 0 = 0).
      { change ((y - x) * 0 = 0). rewrite Rmult_0_r. reflexivity. }
      assert (Hc : is_RInt (fun _ : R => 0) x y (scal (y - x) 0)).
      { exact (is_RInt_const x y 0). }
      rewrite Hz in Hc.
      exact Hc.
    + unfold ball, AbsRing_ball; simpl.
      change (Rabs (0 - 0) < pos eps0).
      rewrite Rminus_diag.
      rewrite Rabs_R0.
      exact (cond_pos eps0).
Qed.

(* G 核在 γ=0：恒为零 *)
Lemma ex_RInt_gen_kusin_0 : ex_RInt_gen (kusin 0) (at_right 0) (Rbar_locally p_infty).
Proof.
  apply (ex_RInt_gen_abs_le (kusin 0) (fun _ : R => 0) 0).
  - intros t Ht; apply cont_kusin.
  - intros t Ht; apply continuous_const.
  - intros t Ht; apply Rle_refl.
  - intros t Ht.
    unfold kusin.
    rewrite (Rmult_0_l t).
    rewrite sin_0.
    rewrite (Rmult_0_r t).
    unfold Rdiv.
    rewrite Rmult_0_l.
    rewrite Rabs_R0.
    apply Rle_refl.
  - exact ex_RInt_gen_zero_fun.
Qed.

(* x/(1+x²) 在 [1,∞) 递减 *)
Lemma x_over_1px2_decreasing : forall x y : R, 1 <= x -> x <= y ->
  y / (1 + y * y) <= x / (1 + x * x).
Proof.
  intros x y Hx Hxy.
  assert (Hx_pos : 0 < x) by lra.
  assert (Hpos_x : 0 < 1 + x * x) by (assert (Hsq : 0 <= x * x) by apply Rle_0_sqr; lra).
  assert (Hpos_y : 0 < 1 + y * y) by (assert (Hsq : 0 <= y * y) by apply Rle_0_sqr; lra).
  assert (Hxx : 1 <= x * x).
  { apply Rle_trans with (x * 1).
    - rewrite Rmult_1_r. exact Hx.
    - apply Rmult_le_compat_l; [apply Rlt_le; exact Hx_pos | exact Hx]. }
  assert (Hxy1 : 1 <= x * y).
  { apply Rle_trans with (x * x); [exact Hxx |].
    apply Rmult_le_compat_l; [apply Rlt_le; exact Hx_pos | exact Hxy]. }
  assert (Hone : 1 - x * y <= 0).
  { apply Rle_minus. exact Hxy1. }
  assert (Hmain : y * (1 + x * x) <= x * (1 + y * y)).
  { replace (y * (1 + x * x)) with (x * (1 + y * y) + ((y - x) * (1 - x * y))) by ring.
    assert (Hxy1ge : 0 <= x * y - 1) by lra.
    assert (Hp : 0 <= (y - x) * (x * y - 1)).
    { apply Rmult_le_pos; [lra | exact Hxy1ge]. }
    assert (Hd : (y - x) * (1 - x * y) <= 0).
    { replace (1 - x * y) with (- (x * y - 1)) by ring.
      replace ((y - x) * (- (x * y - 1))) with (- ((y - x) * (x * y - 1))) by ring.
      apply Rle_trans with (- 0).
      - apply Ropp_le_contravar. exact Hp.
      - rewrite Ropp_0. apply Rle_refl. }
    lra. }
  apply (Rmult_le_reg_r ((1 + y * y) * (1 + x * x))).
  - apply Rmult_lt_0_compat; [exact Hpos_y | exact Hpos_x].
  - unfold Rdiv.
    replace ((y * / (1 + y * y)) * ((1 + y * y) * (1 + x * x)))
      with (y * (1 + x * x)) by (field; apply Rgt_not_eq; exact Hpos_y).
    replace ((x * / (1 + x * x)) * ((1 + y * y) * (1 + x * x)))
      with (x * (1 + y * y)) by (field; apply Rgt_not_eq; exact Hpos_x).
    exact Hmain.
Qed.

(* /u → 0 *)
Lemma filterlim_Rinv_p_infty : filterlim (fun u : R => / u) (Rbar_locally p_infty) (locally 0).
Proof.
  unfold filterlim.
  intros P HP.
  destruct (locally_iff_open_ball 0 P) as [Hiff _].
  destruct (Hiff HP) as [eps [Heps_pos Hball]].
  exists (Rmax 1 (/ eps + 1)).
  intros u Hu.
  apply Hball.
  unfold ball, AbsRing_ball; simpl.
  rewrite Rminus_0_r.
  assert (Hu1 : 0 < u).
  { apply Rlt_trans with (Rmax 1 (/ eps + 1)).
    - apply Rlt_le_trans with 1; [lra | apply Rmax_l].
    - exact Hu. }
  assert (Hupos : 0 < / u) by (apply Rinv_0_lt_compat; exact Hu1).
  rewrite Rabs_pos_eq; [| apply Rlt_le; exact Hupos].
  apply Rlt_le_trans with (/ (Rmax 1 (/ eps + 1))).
  - apply Rinv_lt_contravar.
    + apply Rmult_lt_0_compat.
      * apply Rlt_le_trans with 1; [lra | apply Rmax_l].
      * exact Hu1.
    + exact Hu.
  - apply Rle_trans with (/ (/ eps + 1)).
    + apply Rinv_le_contravar.
      * apply Rlt_le_trans with (/ eps); [apply Rinv_0_lt_compat; exact Heps_pos | lra].
      * apply Rmax_r.
    + apply Rlt_le.
      apply Rlt_le_trans with (/ (/ eps)).
      * apply (Rinv_lt_contravar (/ eps) (/ eps + 1)).
        -- apply Rmult_lt_0_compat.
           ++ apply Rinv_0_lt_compat; exact Heps_pos.
           ++ apply Rlt_le_trans with (/ eps); [apply Rinv_0_lt_compat; exact Heps_pos | lra].
        -- lra.
      * rewrite (Rinv_inv eps). apply Rle_refl.
Qed.

(* d/du [−(cos(γu)·u)/(γ(1+u²))] = u sin(γu)/(1+u²) − (1/γ)cos(γu)(1−u²)/(1+u²)² *)
Lemma is_derive_psi_gkernel : forall gamma x : R, 0 < gamma ->
  is_derive (fun u => - (cos (gamma * u) * u) / (gamma * (1 + u * u))) x
    (x * sin (gamma * x) / (1 + x * x) -
     (1 / gamma) * (cos (gamma * x) * (1 - x * x) / ((1 + x * x) * (1 + x * x)))).
Proof.
  intros gamma x Hgamma.
  assert (Hnum : is_derive (fun u => - (cos (gamma * u) * u)) x
                     (gamma * (x * sin (gamma * x)) - cos (gamma * x))).
  { assert (Hcos_scal : is_derive (fun u => cos (gamma * u)) x (gamma * (- sin (gamma * x)))).
    { assert (Hmid : is_derive (fun u => cos (gamma * u)) x (scal gamma (- sin (gamma * x)))).
      { apply (is_derive_comp cos (fun u => gamma * u) x (- sin (gamma * x)) gamma).
        - apply is_derive_cos.
        - assert (Hid : is_derive (fun u : R => u) x one)
            by (change (is_derive (fun u : R => u) x one); apply (is_derive_id (K := R_AbsRing))).
          assert (Hsc : is_derive (fun u => gamma * u) x (gamma * 1)).
          { apply (is_derive_scal (fun u : R => u) x gamma 1). exact Hid. }
          replace (gamma * 1) with gamma in Hsc by ring.
          exact Hsc. }
      exact Hmid. }
    assert (Hmult : is_derive (fun u => cos (gamma * u) * u) x
                      ((gamma * (- sin (gamma * x))) * x + cos (gamma * x) * 1)).
    { apply (is_derive_mult (fun u => cos (gamma * u)) id x
               (gamma * (- sin (gamma * x))) 1).
      - exact Hcos_scal.
      - change (is_derive (fun u : R => u) x one).
        apply (is_derive_id (K := R_AbsRing)).
      - intros n m; apply Rmult_comm. }
    replace (gamma * (x * sin (gamma * x)) - cos (gamma * x))
      with (- (((gamma * (- sin (gamma * x))) * x + cos (gamma * x) * 1))) by ring.
    apply (is_derive_opp (fun u => cos (gamma * u) * u) x
             ((gamma * (- sin (gamma * x))) * x + cos (gamma * x) * 1)).
    exact Hmult.
  }
  assert (Hden : is_derive (fun u => gamma * (1 + u * u)) x (gamma * (2 * x))).
  { apply (is_derive_scal (fun u => 1 + u * u) x gamma (2 * x)).
    assert (Hd_sq : is_derive (fun u : R => u * u) x (2 * x)).
    { assert (Hraw2 : is_derive (fun u : R => u * u) x (1 * x + x * 1)).
      { apply (is_derive_mult id id x 1 1).
        - change (is_derive (fun u : R => u) x one).
          apply (is_derive_id (K := R_AbsRing)).
        - change (is_derive (fun u : R => u) x one).
          apply (is_derive_id (K := R_AbsRing)).
        - intros n m; apply Rmult_comm. }
      replace (1 * x + x * 1) with (2 * x) in Hraw2 by ring.
      exact Hraw2. }
    assert (Hplus : is_derive (fun u => 1 + u * u) x (0 + 2 * x)).
    { apply (is_derive_plus (fun _ : R => 1) (fun u => u * u) x 0 (2 * x)).
      - change (is_derive (fun _ : R => 1) x zero).
        apply (is_derive_const 1 x).
      - exact Hd_sq. }
    replace (0 + 2 * x) with (2 * x) in Hplus by ring.
    exact Hplus.
  }
  assert (Hraw : is_derive (fun u => - (cos (gamma * u) * u) / (gamma * (1 + u * u))) x
                   (((gamma * (x * sin (gamma * x)) - cos (gamma * x)) * (gamma * (1 + x * x)) -
                     (- (cos (gamma * x) * x)) * (gamma * (2 * x))) / (gamma * (1 + x * x)) ^ 2)).
  { apply (is_derive_div (fun u => - (cos (gamma * u) * u)) (fun u => gamma * (1 + u * u)) x
             (gamma * (x * sin (gamma * x)) - cos (gamma * x)) (gamma * (2 * x))).
    - exact Hnum.
    - exact Hden.
    - apply Rgt_not_eq.
      apply Rmult_lt_0_compat.
      + exact Hgamma.
      + assert (Hsq : 0 <= x * x) by apply Rle_0_sqr. lra.
  }
  replace (((gamma * (x * sin (gamma * x)) - cos (gamma * x)) * (gamma * (1 + x * x)) -
            (- (cos (gamma * x) * x)) * (gamma * (2 * x))) / (gamma * (1 + x * x)) ^ 2)
    with (x * sin (gamma * x) / (1 + x * x) -
          (1 / gamma) * (cos (gamma * x) * (1 - x * x) / ((1 + x * x) * (1 + x * x)))) in Hraw.
  - exact Hraw.
  - replace ((gamma * (1 + x * x)) ^ 2) with ((gamma * (1 + x * x)) * (gamma * (1 + x * x))) by (unfold pow; ring).
    assert (Hg0 : gamma <> 0) by (apply Rgt_not_eq; exact Hgamma).
    assert (Hp0 : 1 + x * x <> 0) by (apply Rgt_not_eq; assert (Hsq : 0 <= x * x) by apply Rle_0_sqr; lra).
    assert (Hgp0 : gamma * (1 + x * x) <> 0) by (apply Rgt_not_eq; apply Rmult_lt_0_compat;
      [exact Hgamma | assert (Hsq : 0 <= x * x) by apply Rle_0_sqr; lra]).
    field; auto.
Qed.

(* ============================================================
   第 12 轮（第三部分 · 续）：G 核条件收敛、边界引理、IBP 恒等式
   ============================================================ *)

(* |1 − t²| ≤ 1 + t² *)
Lemma Rabs_1_minus_sq_le : forall t : R, Rabs (1 - t * t) <= 1 + t * t.
Proof.
  intro t.
  replace (1 - t * t) with (1 + - (t * t)) by lra.
  apply Rle_trans with (Rabs 1 + Rabs (- (t * t))).
  - apply Rabs_triang.
  - rewrite Rabs_Ropp.
    rewrite (Rabs_pos_eq 1 (Rlt_le 0 1 Rlt_0_1)).
    rewrite (Rabs_pos_eq (t * t) (Rle_0_sqr t)).
    apply Rle_refl.
Qed.

(* k2(u) := cos(γu)(1−u²)/(1+u²)² *)
Definition k2fun (gamma u : R) : R :=
  cos (gamma * u) * (1 - u * u) / ((1 + u * u) * (1 + u * u)).

Lemma cont_k2fun : forall gamma t : R, continuous (k2fun gamma) t.
Proof.
  intros gamma t.
  unfold k2fun.
  unfold Rdiv.
  apply (continuous_mult (fun u => cos (gamma * u) * (1 - u * u)) (fun u => / ((1 + u * u) * (1 + u * u))) t).
  - apply (continuous_mult (fun u => cos (gamma * u)) (fun u => 1 - u * u) t).
    + apply cont_cos_scal.
    + apply (continuous_plus (fun _ : R => 1) (fun u => - (u * u)) t).
      * apply continuous_const.
      * apply (continuous_opp (fun u => u * u) t).
        apply (continuous_mult id id t); apply continuous_id.
  - apply cont_1px2_sq.
Qed.

(* 1 ≤ t ⇒ |k2(γ,t)| ≤ 1/t² *)
Lemma k2fun_abs_le : forall gamma t : R, 1 <= t -> Rabs (k2fun gamma t) <= / (t * t).
Proof.
  intros gamma t Ht1.
  assert (Ht_pos : 0 < t) by lra.
  assert (Hpos : 0 < 1 + t * t) by (assert (Hsq : 0 <= t * t) by apply Rle_0_sqr; lra).
  assert (Hpos2 : 0 < (1 + t * t) * (1 + t * t)) by (apply Rmult_lt_0_compat; [exact Hpos | exact Hpos]).
  unfold k2fun.
  unfold Rdiv.
  rewrite Rabs_mult.
  rewrite Rabs_mult.
  rewrite (Rabs_pos_eq (/ ((1 + t * t) * (1 + t * t)))).
  - apply Rle_trans with ((1 + t * t) * / ((1 + t * t) * (1 + t * t))).
    + apply Rmult_le_compat_r; [apply Rlt_le; apply Rinv_0_lt_compat; exact Hpos2 |].
      apply Rle_trans with (1 * Rabs (1 - t * t)).
      * apply Rmult_le_compat_r; [apply Rabs_pos | exact (Rabs_cos_le_one (gamma * t))].
      * rewrite <- (Rmult_1_l (1 + t * t)).
        apply Rmult_le_compat_l; [lra | exact (Rabs_1_minus_sq_le t)].
    + apply Rle_trans with (/ (1 + t * t)).
      * replace ((1 + t * t) * / ((1 + t * t) * (1 + t * t))) with (/ (1 + t * t))
          by (field; try (apply Rgt_not_eq; exact Hpos); try (apply Rgt_not_eq; exact Hpos2)).
        apply Rle_refl.
      * apply Rinv_le_contravar; [apply Rmult_lt_0_compat; [exact Ht_pos | exact Ht_pos] | lra].
  - apply Rlt_le; apply Rinv_0_lt_compat; exact Hpos2.
Qed.

(* ∫_x^y 1/t² dt = 1/x − 1/y（1 ≤ x ≤ y） *)
Lemma RInt_recip_sq : forall x y : R, 1 <= x -> x <= y ->
  RInt (fun t => / (t * t)) x y = / x - / y.
Proof.
  intros x y Hx1 Hxy.
  assert (Hder : is_RInt (fun t => - (- 1 / (t ^ 2))) x y (- / y - - / x)).
  { apply (is_RInt_derive (fun t => - / t) (fun t => - (- 1 / (t ^ 2))) x y).
    - intros t Ht.
      assert (Ht1 : 1 <= t).
      { destruct Ht as [Ht1' Ht2'].
        rewrite (Rmin_left x y Hxy) in Ht1'.
        lra. }
      assert (Ht_pos : 0 < t) by lra.
      assert (Hdinv : is_derive (fun t0 : R => / t0) t (- 1 / (t ^ 2))).
      { apply (is_derive_inv id t 1).
        - change (is_derive (fun u : R => u) t one).
          apply (is_derive_id (K := R_AbsRing)).
        - apply Rgt_not_eq. exact Ht_pos. }
      apply (is_derive_opp (fun t0 : R => / t0) t (- 1 / (t ^ 2))).
      exact Hdinv.
    - intros t Ht.
      apply (continuous_opp (fun t0 => - 1 / (t0 ^ 2)) t).
      apply (continuity_pt_to_continuous_simple (fun t0 => - 1 / (t0 ^ 2)) t).
      apply continuity_pt_div.
      + apply continuity_pt_const.
        intros u v; reflexivity.
      + apply (continuity_pt_ext (fun t0 : R => t0 * t0) (fun t0 : R => t0 ^ 2) t).
        * intro z0. rewrite <- (Rsqr_pow2 z0). reflexivity.
        * apply (continuity_pt_mult id id t); apply continuity_pt_id.
      + intro Hz0.
        assert (Ht1 : 1 <= t).
        { destruct Ht as [Ht1' Ht2'].
          rewrite (Rmin_left x y Hxy) in Ht1'.
          lra. }
        assert (Ht_pos : 0 < t) by lra.
        assert (Hsq_pos : 0 < t ^ 2).
        { replace (t ^ 2) with (t * t) by (rewrite <- (Rsqr_pow2 t); reflexivity).
          apply Rmult_lt_0_compat; [exact Ht_pos | exact Ht_pos]. }
        rewrite Hz0 in Hsq_pos.
        lra.
  }
  assert (Hext : RInt (fun t => / (t * t)) x y = RInt (fun t => - (- 1 / (t ^ 2))) x y).
  { apply RInt_ext.
    intros z Hz.
    simpl.
    field.
    all: try (apply Rgt_not_eq;
              assert (Hz1 : 1 <= z) by (destruct Hz as [Hz1' Hz2'];
                rewrite (Rmin_left x y Hxy) in Hz1'; lra);
              lra).
    all: try (apply Rmult_integral_contrapositive;
              [apply Rgt_not_eq;
                assert (Hz1 : 1 <= z) by (destruct Hz as [Hz1' Hz2'];
                  rewrite (Rmin_left x y Hxy) in Hz1'; lra);
                lra |
               apply Rgt_not_eq;
                assert (Hz1 : 1 <= z) by (destruct Hz as [Hz1' Hz2'];
                  rewrite (Rmin_left x y Hxy) in Hz1'; lra);
                lra]).
  }
  assert (Hval : RInt (fun t => - (- 1 / (t ^ 2))) x y = - / y - - / x).
  { apply is_RInt_unique. exact Hder. }
  rewrite Hext.
  rewrite Hval.
  lra.
Qed.

(* 1 ≤ x ≤ y ⇒ |∫_x^y k2| ≤ 1/x − 1/y *)
Lemma RInt_k2_abs_le : forall gamma x y : R, 1 <= x -> x <= y ->
  Rabs (RInt (k2fun gamma) x y) <= / x - / y.
Proof.
  intros gamma x y Hx1 Hxy.
  apply Rle_trans with (RInt (fun t => Rabs (k2fun gamma t)) x y).
  - apply (abs_RInt_le (k2fun gamma) x y); [exact Hxy |].
    apply (ex_RInt_continuous (k2fun gamma) x y).
    intros z Hz.
    apply cont_k2fun.
  - apply Rle_trans with (RInt (fun t => / (t * t)) x y).
    + apply RInt_le; [exact Hxy | | | intros t Ht; apply (k2fun_abs_le gamma t); lra].
      * apply (ex_RInt_continuous (fun t => Rabs (k2fun gamma t)) x y).
        intros z Hz.
        apply (continuous_comp (k2fun gamma) Rabs z).
        -- apply cont_k2fun.
        -- apply continuous_Rabs.
      * apply (ex_RInt_continuous (fun t => / (t * t)) x y).
        intros z Hz.
        apply (continuity_pt_to_continuous_simple (fun t => / (t * t)) z).
        apply continuity_pt_inv.
        -- apply (continuity_pt_mult id id z); apply continuity_pt_id.
        -- intro Hz0.
           assert (Hz1 : 1 <= z).
           { destruct Hz as [Hz1' Hz2'].
             rewrite (Rmin_left x y Hxy) in Hz1'.
             lra. }
           assert (Hz_pos : 0 < z) by lra.
           assert (Hsq_pos : 0 < z * z).
           { apply Rmult_lt_0_compat; [exact Hz_pos | exact Hz_pos]. }
           simpl in Hz0.
           rewrite Hz0 in Hsq_pos.
           lra.
    + rewrite (RInt_recip_sq x y Hx1 Hxy).
      apply Rle_refl.
Qed.

(* G 核有限区间 IBP 界（x ≤ y） *)
Lemma RInt_usin_ibp_bound_le : forall gamma x y : R, 0 < gamma -> 1 <= x -> x <= y ->
  Rabs (RInt (fun u => u * sin (gamma * u) / (1 + u * u)) x y) <=
  (1 / gamma) * (y / (1 + y * y) + x / (1 + x * x) + (1 / x - 1 / y)).
Proof.
  intros gamma x y Hgamma Hx1 Hxy.
  set (f := fun u => u * sin (gamma * u) / (1 + u * u)).
  set (psi := fun u => - (cos (gamma * u) * u) / (gamma * (1 + u * u))).
  assert (Hdpsi : forall u : R, 0 < u -> is_derive psi u (f u - (1 / gamma) * k2fun gamma u)).
  { intros u Hu.
    unfold psi, f.
    exact (is_derive_psi_gkernel gamma u Hgamma). }
  assert (Hibp : RInt f x y = psi y - psi x + (1 / gamma) * RInt (k2fun gamma) x y).
  { assert (Hder : is_RInt (fun t => f t - (1 / gamma) * k2fun gamma t) x y (psi y - psi x)).
    { apply (is_RInt_derive psi (fun t => f t - (1 / gamma) * k2fun gamma t) x y).
      - intros t Ht.
        apply Hdpsi.
        destruct Ht as [Ht1 Ht2].
        rewrite (Rmin_left x y Hxy) in Ht1.
        rewrite (Rmax_right x y Hxy) in Ht2.
        lra.
      - intros t Ht.
        apply (continuous_plus (fun t0 => f t0) (fun t0 => - ((1 / gamma) * k2fun gamma t0)) t).
        + unfold f; apply cont_kusin.
        + apply (continuous_opp (fun t0 => (1 / gamma) * k2fun gamma t0) t).
          apply (continuous_mult (fun _ : R => 1 / gamma) (fun t0 => k2fun gamma t0) t).
          * apply continuous_const.
          * apply cont_k2fun.
    }
    assert (Hsplit : RInt f x y = RInt (fun t => f t - (1 / gamma) * k2fun gamma t) x y +
                                    RInt (fun t => (1 / gamma) * k2fun gamma t) x y).
    { assert (Hext : RInt f x y =
                     RInt (fun t => (f t - (1 / gamma) * k2fun gamma t) + (1 / gamma) * k2fun gamma t) x y).
      { apply RInt_ext.
        intros z Hz.
        lra. }
      rewrite Hext.
      apply (RInt_plus (fun t => f t - (1 / gamma) * k2fun gamma t) (fun t => (1 / gamma) * k2fun gamma t) x y).
      - apply (ex_RInt_continuous (fun t => f t - (1 / gamma) * k2fun gamma t) x y).
        intros z Hz.
        apply (continuous_plus (fun t0 => f t0) (fun t0 => - ((1 / gamma) * k2fun gamma t0)) z).
        + unfold f; apply cont_kusin.
        + apply (continuous_opp (fun t0 => (1 / gamma) * k2fun gamma t0) z).
          apply (continuous_mult (fun _ : R => 1 / gamma) (fun t0 => k2fun gamma t0) z).
          * apply continuous_const.
          * apply cont_k2fun.
      - apply (ex_RInt_continuous (fun t => (1 / gamma) * k2fun gamma t) x y).
        intros z Hz.
        apply (continuous_mult (fun _ : R => 1 / gamma) (fun t0 => k2fun gamma t0) z).
        + apply continuous_const.
        + apply cont_k2fun.
    }
    assert (Hval : RInt (fun t => f t - (1 / gamma) * k2fun gamma t) x y = psi y - psi x).
    { apply is_RInt_unique. exact Hder. }
    assert (Hscal : RInt (fun t => (1 / gamma) * k2fun gamma t) x y = (1 / gamma) * RInt (k2fun gamma) x y).
    { apply (RInt_scal (k2fun gamma) x y (1 / gamma)).
      apply (ex_RInt_continuous (k2fun gamma) x y).
      intros z Hz.
      apply cont_k2fun.
    }
    rewrite Hval in Hsplit.
    rewrite Hscal in Hsplit.
    lra.
  }
  rewrite Hibp.
  assert (Hpsy : forall u : R, 1 <= u -> Rabs (psi u) <= (1 / gamma) * (u / (1 + u * u))).
  { intros u Hu.
    unfold psi.
    unfold Rdiv.
    rewrite Rabs_mult.
    rewrite (Rabs_pos_eq (/ (gamma * (1 + u * u)))).
    + rewrite Rabs_Ropp.
      rewrite Rabs_mult.
      rewrite (Rabs_pos_eq u (Rlt_le 0 u (Rlt_le_trans 0 1 u Rlt_0_1 Hu))).
      apply Rle_trans with (u * / (gamma * (1 + u * u))).
      - apply Rmult_le_compat_r; [apply Rlt_le; apply Rinv_0_lt_compat;
          apply Rmult_lt_0_compat; [exact Hgamma |
            assert (Hsq : 0 <= u * u) by apply Rle_0_sqr; lra] |].
        assert (Hp : Rabs (cos (gamma * u)) * u <= 1 * u).
        { apply Rmult_le_compat_r; [apply Rlt_le; lra | exact (Rabs_cos_le_one (gamma * u))]. }
        rewrite (Rmult_1_l u) in Hp.
        exact Hp.
      - assert (Hg0 : gamma <> 0) by (apply Rgt_not_eq; exact Hgamma).
        assert (Hp0 : 1 + u * u <> 0) by (apply Rgt_not_eq; assert (Hsq : 0 <= u * u) by apply Rle_0_sqr; lra).
        assert (Hinv : / (gamma * (1 + u * u)) = / gamma * / (1 + u * u)).
        { apply Rinv_mult. }
        assert (Heq2 : u * / (gamma * (1 + u * u)) = (1 / gamma) * (u / (1 + u * u))).
        { rewrite Hinv.
          unfold Rdiv.
          rewrite <- (Rmult_assoc u (/ gamma) (/ (1 + u * u))).
          replace (u * / gamma) with ((1 / gamma) * u) by (rewrite Rmult_comm; unfold Rdiv; rewrite Rmult_1_l; reflexivity).
          rewrite Rmult_assoc.
          reflexivity. }
        rewrite Heq2.
        apply Rle_refl.
    + apply Rlt_le; apply Rinv_0_lt_compat; apply Rmult_lt_0_compat;
      [exact Hgamma | assert (Hsq : 0 <= u * u) by apply Rle_0_sqr; lra].
  }
  apply Rle_trans with (Rabs (psi y) + Rabs (psi x) + Rabs ((1 / gamma) * RInt (k2fun gamma) x y)).
  - replace (psi y - psi x + (1 / gamma) * RInt (k2fun gamma) x y)
      with ((psi y + - psi x) + (1 / gamma) * RInt (k2fun gamma) x y) by lra.
    apply Rle_trans with (Rabs (psi y + - psi x) + Rabs ((1 / gamma) * RInt (k2fun gamma) x y)).
    + apply Rabs_triang.
    + apply Rplus_le_compat_r.
      apply Rle_trans with (Rabs (psi y) + Rabs (- psi x)).
      * apply Rabs_triang.
      * rewrite Rabs_Ropp. apply Rle_refl.
  - apply Rle_trans with ((1 / gamma) * (y / (1 + y * y)) + (1 / gamma) * (x / (1 + x * x)) +
                          (1 / gamma) * (1 / x - 1 / y)).
    + apply Rplus_le_compat.
      * apply Rplus_le_compat; [apply Hpsy; lra | apply Hpsy; lra].
      * rewrite Rabs_mult.
        rewrite (Rabs_pos_eq (1 / gamma)).
        -- apply Rmult_le_compat_l; [apply Rlt_le; unfold Rdiv; rewrite Rmult_1_l; apply Rinv_0_lt_compat; exact Hgamma |].
           replace (1 / x - 1 / y) with (/ x - / y) by (unfold Rdiv; rewrite Rmult_1_l; rewrite Rmult_1_l; reflexivity).
           apply (RInt_k2_abs_le gamma x y Hx1 Hxy).
        -- apply Rlt_le; unfold Rdiv; rewrite Rmult_1_l; apply Rinv_0_lt_compat; exact Hgamma.
    + replace ((1 / gamma) * (y / (1 + y * y)) + (1 / gamma) * (x / (1 + x * x)) +
               (1 / gamma) * (1 / x - 1 / y))
        with ((1 / gamma) * (y / (1 + y * y) + x / (1 + x * x) + (1 / x - 1 / y)))
        by (rewrite (Rmult_plus_distr_l (1 / gamma) (y / (1 + y * y) + x / (1 + x * x)) (1 / x - 1 / y));
            rewrite (Rmult_plus_distr_l (1 / gamma) (y / (1 + y * y)) (x / (1 + x * x)));
            reflexivity).
      apply Rle_refl.
Qed.

(* G 核有限区间 IBP 界（对称形式） *)
Lemma RInt_usin_ibp_bound : forall gamma x y : R, 0 < gamma -> 1 <= x -> 1 <= y ->
  Rabs (RInt (fun u => u * sin (gamma * u) / (1 + u * u)) x y) <=
  (1 / gamma) * (y / (1 + y * y) + x / (1 + x * x) + Rabs (1 / x - 1 / y)).
Proof.
  intros gamma x y Hgamma Hx1 Hy1.
  destruct (Rle_dec x y) as [Hxy | Hyx].
  - apply Rle_trans with ((1 / gamma) * (y / (1 + y * y) + x / (1 + x * x) + (1 / x - 1 / y))).
    + apply (RInt_usin_ibp_bound_le gamma x y Hgamma Hx1 Hxy).
    + assert (Hge : 0 <= 1 / x - 1 / y).
      { assert (H1 : 1 / y <= 1 / x).
        { unfold Rdiv. rewrite Rmult_1_l. rewrite Rmult_1_l.
          apply Rinv_le_contravar; [lra | exact Hxy]. }
        lra. }
      assert (Habs : Rabs (1 / x - 1 / y) = 1 / x - 1 / y) by (apply Rabs_pos_eq; exact Hge).
      rewrite Habs.
      apply Rle_refl.
  - assert (Hyx_le : y <= x) by lra.
    assert (Hch : RInt (fun u => u * sin (gamma * u) / (1 + u * u)) x y =
                  - RInt (fun u => u * sin (gamma * u) / (1 + u * u)) y x).
    { assert (Hch' : RInt (fun u => u * sin (gamma * u) / (1 + u * u)) x y +
                    RInt (fun u => u * sin (gamma * u) / (1 + u * u)) y x =
                    RInt (fun u => u * sin (gamma * u) / (1 + u * u)) x x).
      { apply (RInt_Chasles (fun u => u * sin (gamma * u) / (1 + u * u)) x y x).
        - apply (ex_RInt_continuous (fun u => u * sin (gamma * u) / (1 + u * u)) x y).
          intros z Hz; apply cont_kusin.
        - apply (ex_RInt_continuous (fun u => u * sin (gamma * u) / (1 + u * u)) y x).
          intros z Hz; apply cont_kusin. }
      assert (Hxx : RInt (fun u => u * sin (gamma * u) / (1 + u * u)) x x = 0).
      { apply is_RInt_unique.
        apply (is_RInt_point (fun u => u * sin (gamma * u) / (1 + u * u)) x). }
      lra. }
    rewrite Hch.
    rewrite Rabs_Ropp.
    apply Rle_trans with ((1 / gamma) * (x / (1 + x * x) + y / (1 + y * y) + (1 / y - 1 / x))).
    + apply (RInt_usin_ibp_bound_le gamma y x Hgamma Hy1 Hyx_le).
    + assert (Hle : 1 / x - 1 / y <= 0).
      { assert (H1 : 1 / x <= 1 / y).
        { unfold Rdiv. rewrite Rmult_1_l. rewrite Rmult_1_l.
          apply Rinv_le_contravar; [lra | exact Hyx_le]. }
        lra. }
      assert (Habs : Rabs (1 / x - 1 / y) = 1 / y - 1 / x).
      { rewrite (Rabs_left1 (1 / x - 1 / y) Hle). lra. }
      replace (y / (1 + y * y) + x / (1 + x * x)) with (x / (1 + x * x) + y / (1 + y * y)) by (apply Rplus_comm).
      rewrite Habs.
      apply Rle_refl.
Qed.

(* G 核的柯西尾巴 *)
Lemma RInt_usin_1p1p2_cauchy : forall gamma : R, 0 < gamma ->
  forall eps : posreal, exists M : R,
    forall x y : R, M <= x -> M <= y ->
      Rabs (RInt (fun u => u * sin (gamma * u) / (1 + u * u)) 0 x -
            RInt (fun u => u * sin (gamma * u) / (1 + u * u)) 0 y) < pos eps.
Proof.
  intros gamma Hgamma eps.
  set (f := fun u => u * sin (gamma * u) / (1 + u * u)).
  assert (Hlim0 : filterlim (fun u : R => 2 * (u / (1 + u * u)) + 2 * / u)
                    (Rbar_locally p_infty) (locally (0 + 0))).
  { apply (filterlim_sum_comp (fun u => 2 * (u / (1 + u * u))) (fun u => 2 * / u) 0 0 (Rbar_locally p_infty)).
    - apply Rbar_locally_filter.
    - replace 0 with (2 * 0) by ring.
      apply (filterlim_scal_comp (fun u => u / (1 + u * u)) 2 0 (Rbar_locally p_infty)).
      + apply Rbar_locally_filter.
      + exact filterlim_x_over_1px2_p_infty.
    - replace 0 with (2 * 0) by ring.
      apply (filterlim_scal_comp (fun u => / u) 2 0 (Rbar_locally p_infty)).
      + apply Rbar_locally_filter.
      + exact filterlim_Rinv_p_infty. }
  assert (Hlim : filterlim (fun u : R => 2 * (u / (1 + u * u)) + 2 * / u)
                   (Rbar_locally p_infty) (locally 0)).
  { replace (0 + 0) with 0 in Hlim0 by ring.
    exact Hlim0. }
  assert (Hepsg : 0 < pos eps * gamma) by (apply Rmult_lt_0_compat; [exact (cond_pos eps) | exact Hgamma]).
  assert (HP : locally 0 (fun y => Rabs (y - 0) < pos eps * gamma)).
  { apply locally_iff_open_ball.
    exists (pos eps * gamma).
    split.
    - exact Hepsg.
    - intros y Hy.
      exact Hy. }
  destruct (Hlim (fun y => Rabs (y - 0) < pos eps * gamma) HP) as [M0 HM0].
  exists (Rmax 1 (M0 + 1)).
  intros x y HxM HyM.
  assert (Hx1 : 1 <= x) by (apply Rle_trans with (Rmax 1 (M0 + 1)); [apply Rmax_l | exact HxM]).
  assert (Hy1 : 1 <= y) by (apply Rle_trans with (Rmax 1 (M0 + 1)); [apply Rmax_l | exact HyM]).
  assert (Hch : RInt f 0 y - RInt f 0 x = RInt f x y).
  { assert (Hch' : RInt f 0 x + RInt f x y = RInt f 0 y).
    { apply (RInt_Chasles f 0 x y).
      - apply (ex_RInt_continuous f 0 x). intros z Hz; unfold f; apply cont_kusin.
      - apply (ex_RInt_continuous f x y). intros z Hz; unfold f; apply cont_kusin. }
    lra. }
  rewrite Rabs_minus_sym.
  rewrite Hch.
  set (M := Rmax 1 (M0 + 1)).
  assert (HxM' : M <= x) by (unfold M; exact HxM).
  assert (HyM' : M <= y) by (unfold M; exact HyM).
  assert (HM1 : 1 <= M) by (unfold M; apply Rmax_l).
  assert (HM0_M : M0 < M) by (unfold M; apply Rlt_le_trans with (M0 + 1); [lra | apply Rmax_r]).
  assert (HM_le : forall u : R, M <= u -> u / (1 + u * u) <= M / (1 + M * M)).
  { intros u Hu.
    apply (x_over_1px2_decreasing M u); [exact HM1 | exact Hu]. }
  assert (Hsum1 : y / (1 + y * y) + x / (1 + x * x) <= 2 * (M / (1 + M * M))).
  { apply Rle_trans with (M / (1 + M * M) + M / (1 + M * M)).
    - apply Rplus_le_compat; [apply HM_le; exact HyM' | apply HM_le; exact HxM'].
    - rewrite <- (Rplus_diag (M / (1 + M * M))).
      apply Rle_refl. }
  assert (Habs : Rabs (1 / x - 1 / y) <= 2 * / M).
  { apply Rle_trans with (1 / x + 1 / y).
    - replace (1 / x - 1 / y) with (1 / x + - (1 / y)) by lra.
      apply Rle_trans with (Rabs (1 / x) + Rabs (- (1 / y))); [apply Rabs_triang |].
      rewrite Rabs_Ropp.
      rewrite (Rabs_pos_eq (1 / x)); [| apply Rlt_le; unfold Rdiv; rewrite Rmult_1_l; apply Rinv_0_lt_compat; lra].
      rewrite (Rabs_pos_eq (1 / y)); [| apply Rlt_le; unfold Rdiv; rewrite Rmult_1_l; apply Rinv_0_lt_compat; lra].
      apply Rle_refl.
    - assert (HxM_le : 1 / x <= 1 / M).
      { replace (1 / x) with (/ x) by (unfold Rdiv; rewrite Rmult_1_l; reflexivity).
        replace (1 / M) with (/ M) by (unfold Rdiv; rewrite Rmult_1_l; reflexivity).
        apply Rinv_le_contravar; [lra | exact HxM']. }
      assert (HyM_le : 1 / y <= 1 / M).
      { replace (1 / y) with (/ y) by (unfold Rdiv; rewrite Rmult_1_l; reflexivity).
        replace (1 / M) with (/ M) by (unfold Rdiv; rewrite Rmult_1_l; reflexivity).
        apply Rinv_le_contravar; [lra | exact HyM']. }
      replace (2 * / M) with (1 / M + 1 / M) by (unfold Rdiv; rewrite Rmult_1_l; rewrite <- (Rplus_diag (/ M)); reflexivity).
      lra. }
  apply Rle_lt_trans with ((1 / gamma) * (y / (1 + y * y) + x / (1 + x * x) + Rabs (1 / x - 1 / y))).
  - apply (RInt_usin_ibp_bound gamma x y Hgamma Hx1 Hy1).
  - apply Rle_lt_trans with ((1 / gamma) * (2 * (M / (1 + M * M)) + 2 * / M)).
    + apply Rmult_le_compat_l; [apply Rlt_le; unfold Rdiv; rewrite Rmult_1_l; apply Rinv_0_lt_compat; exact Hgamma |].
      apply Rplus_le_compat; [exact Hsum1 | exact Habs].
    + apply Rmult_lt_reg_l with gamma; [exact Hgamma |].
      assert (Hg0 : gamma <> 0) by (apply Rgt_not_eq; exact Hgamma).
      assert (HM0nz : M <> 0) by (apply Rgt_not_eq; lra).
      assert (Hp0 : 1 + M * M <> 0) by (apply Rgt_not_eq; assert (Hsq : 0 <= M * M) by apply Rle_0_sqr; lra).
      replace (gamma * ((1 / gamma) * (2 * (M / (1 + M * M)) + 2 * / M)))
        with (2 * (M / (1 + M * M)) + 2 * / M) by (field; auto).
      replace (gamma * (pos eps)) with (pos eps * gamma) by ring.
      specialize (HM0 M HM0_M).
      rewrite Rminus_0_r in HM0.
      rewrite Rabs_pos_eq in HM0.
      * exact HM0.
      * apply Rplus_le_le_0_compat.
        -- apply Rmult_le_pos; [lra |].
           unfold Rdiv.
           apply Rmult_le_pos; [lra | apply Rlt_le; apply Rinv_0_lt_compat;
             assert (Hsq : 0 <= M * M) by apply Rle_0_sqr; lra].
        -- apply Rmult_le_pos; [lra | apply Rlt_le; apply Rinv_0_lt_compat; lra].
Qed.

(* G 核存在（条件收敛） *)
Lemma ex_RInt_gen_kusin : forall gamma : R, 0 < gamma ->
  ex_RInt_gen (kusin gamma) (at_right 0) (Rbar_locally p_infty).
Proof.
  intros gamma Hgamma.
  apply (ex_RInt_gen_cauchy (kusin gamma) 0).
  - intros t Ht; apply cont_kusin.
  - intros b Hb.
    apply (ex_RInt_continuous (kusin gamma) 0 b).
    intros z Hz; apply cont_kusin.
  - (* 局部小量 *)
    intro eps.
    assert (Hb : exists B : R, 0 < B /\
              forall t, 0 <= t <= 0 + B -> Rabs (kusin gamma t) <= Rabs (kusin gamma 0) + 1)
      by (apply locally_bounded_continuous; apply cont_kusin).
    destruct Hb as [B [HB_pos HB]].
    set (M := Rabs (kusin gamma 0) + 1).
    assert (HM_pos : 0 < M).
    { unfold M. assert (Hr : 0 <= Rabs (kusin gamma 0)) by apply Rabs_pos. lra. }
    assert (Hdelta0 : 0 < Rmin B (pos eps / M)).
    { apply Rmin_pos; [exact HB_pos | apply Rdiv_lt_0_compat; [exact (cond_pos eps) | exact HM_pos]]. }
    exists (mkposreal (Rmin B (pos eps / M)) Hdelta0).
    intros x Hx Hx_ge_a.
    assert (Hf_bnd : forall t, x <= t <= 0 -> Rabs (kusin gamma t) <= M).
    { intros t Ht.
      unfold M.
      apply HB.
      split.
      - apply Rle_trans with x; [lra | exact (proj1 Ht)].
      - apply Rle_trans with 0; [exact (proj2 Ht) |].
        assert (Hd' : x - 0 <= B).
        { apply Rle_trans with (Rmin B (pos eps / M)); [lra | apply Rmin_l]. }
        lra. }
    assert (Hval : Rabs (RInt (kusin gamma) x 0) <= (x - 0) * M).
    { assert (Hch : RInt (kusin gamma) 0 x + RInt (kusin gamma) x 0 = RInt (kusin gamma) 0 0).
      { apply (RInt_Chasles (kusin gamma) 0 x 0).
        - apply (ex_RInt_continuous (kusin gamma) 0 x); intros z Hz; apply cont_kusin.
        - apply (ex_RInt_continuous (kusin gamma) x 0); intros z Hz; apply cont_kusin. }
      assert (Haa : RInt (kusin gamma) 0 0 = 0).
      { apply is_RInt_unique. exact (is_RInt_point (kusin gamma) 0). }
      assert (Hneg : RInt (kusin gamma) x 0 = - RInt (kusin gamma) 0 x) by lra.
      rewrite Hneg.
      rewrite Rabs_Ropp.
      apply (abs_RInt_le_const (kusin gamma) 0 x M); [lra | | ].
      - apply (ex_RInt_continuous (kusin gamma) 0 x); intros z Hz; apply cont_kusin.
      - intros t Ht.
        apply HB.
        split.
        + exact (proj1 Ht).
        + apply Rle_trans with x; [exact (proj2 Ht) |].
          assert (Ht0 : 0 <= x - 0) by lra.
          assert (Hx_a : Rabs (x - 0) < Rmin B (pos eps / M)) by exact Hx.
          rewrite Rabs_pos_eq in Hx_a; [| exact Ht0].
          apply Rlt_le in Hx_a.
          apply Rle_trans with (0 + Rmin B (pos eps / M)); [lra | apply Rplus_le_compat_l; apply Rmin_l]. }
    apply Rle_lt_trans with ((x - 0) * M).
    - exact Hval.
    - assert (Hax : x - 0 < pos eps / M).
      { assert (Ht0 : 0 <= x - 0) by lra.
        assert (Hd : Rabs (x - 0) < Rmin B (pos eps / M)) by exact Hx.
        rewrite Rabs_pos_eq in Hd; [| exact Ht0].
        apply Rlt_le_trans with (Rmin B (pos eps / M)); [exact Hd | apply Rmin_r]. }
      unfold Rdiv.
      apply Rlt_le_trans with ((pos eps / M) * M).
      - apply Rmult_lt_compat_r; [exact HM_pos | exact Hax].
      - replace ((pos eps / M) * M) with (pos eps) by (unfold Rdiv; field; apply Rgt_not_eq; exact HM_pos).
        apply Rle_refl.
  - (* 柯西尾巴 *)
    intros eps. apply (RInt_usin_1p1p2_cauchy gamma Hgamma eps).
Qed.

(* ============================================================
   第 12 轮（第三部分 · 三）：边界引理、导数恒等式、IBP 恒等式
   ============================================================ *)

(* d/du [−(cos(γu)·u)] = γx sin(γx) − cos(γx) *)
Lemma is_derive_neg_cos_u : forall gamma x : R,
  is_derive (fun u => - (cos (gamma * u) * u)) x
    (gamma * (x * sin (gamma * x)) - cos (gamma * x)).
Proof.
  intros gamma x.
  assert (Hcos_scal : is_derive (fun u => cos (gamma * u)) x (gamma * (- sin (gamma * x)))).
  { assert (Hmid : is_derive (fun u => cos (gamma * u)) x (scal gamma (- sin (gamma * x)))).
    { apply (is_derive_comp cos (fun u => gamma * u) x (- sin (gamma * x)) gamma).
      - apply is_derive_cos.
      - assert (Hid : is_derive (fun u : R => u) x one)
          by (change (is_derive (fun u : R => u) x one); apply (is_derive_id (K := R_AbsRing))).
        assert (Hsc : is_derive (fun u => gamma * u) x (gamma * 1)).
        { apply (is_derive_scal (fun u : R => u) x gamma 1). exact Hid. }
        replace (gamma * 1) with gamma in Hsc by ring.
        exact Hsc. }
    exact Hmid. }
  assert (Hmult : is_derive (fun u => cos (gamma * u) * u) x
                    ((gamma * (- sin (gamma * x))) * x + cos (gamma * x) * 1)).
  { apply (is_derive_mult (fun u => cos (gamma * u)) id x (gamma * (- sin (gamma * x))) 1).
    - exact Hcos_scal.
    - change (is_derive (fun u : R => u) x one).
      apply (is_derive_id (K := R_AbsRing)).
    - intros n m; apply Rmult_comm. }
  replace (gamma * (x * sin (gamma * x)) - cos (gamma * x))
    with (- (((gamma * (- sin (gamma * x))) * x + cos (gamma * x) * 1))) by ring.
  apply (is_derive_opp (fun u => cos (gamma * u) * u) x
           ((gamma * (- sin (gamma * x))) * x + cos (gamma * x) * 1)).
  exact Hmult.
Qed.

(* d/du [sin(γu)/(1+u²)] = γcos(γu)/(1+u²) − 2u sin(γu)/(1+u²)² *)
Lemma is_derive_sin_over_1p1p2 : forall gamma x : R,
  is_derive (fun u => sin (gamma * u) / (1 + u * u)) x
    (gamma * cos (gamma * x) / (1 + x * x) -
     2 * (x * sin (gamma * x) / ((1 + x * x) * (1 + x * x)))).
Proof.
  intros gamma x.
  assert (Hnum : is_derive (fun u => sin (gamma * u)) x (gamma * cos (gamma * x))).
  { assert (Hmid : is_derive (fun u => sin (gamma * u)) x (scal gamma (cos (gamma * x)))).
    { apply (is_derive_comp sin (fun u => gamma * u) x (cos (gamma * x)) gamma).
      - apply is_derive_sin.
      - assert (Hid : is_derive (fun u : R => u) x one)
          by (change (is_derive (fun u : R => u) x one); apply (is_derive_id (K := R_AbsRing))).
        assert (Hsc : is_derive (fun u => gamma * u) x (gamma * 1)).
        { apply (is_derive_scal (fun u : R => u) x gamma 1). exact Hid. }
        replace (gamma * 1) with gamma in Hsc by ring.
        exact Hsc. }
    exact Hmid. }
  assert (Hden : is_derive (fun u => 1 + u * u) x (2 * x)).
  { assert (Hd_sq : is_derive (fun u : R => u * u) x (2 * x)).
    { assert (Hraw2 : is_derive (fun u : R => u * u) x (1 * x + x * 1)).
      { apply (is_derive_mult id id x 1 1).
        - change (is_derive (fun u : R => u) x one).
          apply (is_derive_id (K := R_AbsRing)).
        - change (is_derive (fun u : R => u) x one).
          apply (is_derive_id (K := R_AbsRing)).
        - intros n m; apply Rmult_comm. }
      replace (1 * x + x * 1) with (2 * x) in Hraw2 by ring.
      exact Hraw2. }
    assert (Hplus : is_derive (fun u => 1 + u * u) x (0 + 2 * x)).
    { apply (is_derive_plus (fun _ : R => 1) (fun u => u * u) x 0 (2 * x)).
      - change (is_derive (fun _ : R => 1) x zero).
        apply (is_derive_const 1 x).
      - exact Hd_sq. }
    replace (0 + 2 * x) with (2 * x) in Hplus by ring.
    exact Hplus.
  }
  assert (Hraw : is_derive (fun u => sin (gamma * u) / (1 + u * u)) x
                   (((gamma * cos (gamma * x)) * (1 + x * x) - sin (gamma * x) * (2 * x)) / (1 + x * x) ^ 2)).
  { apply (is_derive_div (fun u => sin (gamma * u)) (fun u => 1 + u * u) x
             (gamma * cos (gamma * x)) (2 * x)).
    - exact Hnum.
    - exact Hden.
    - apply Rgt_not_eq.
      assert (Hsq : 0 <= x * x) by apply Rle_0_sqr.
      lra.
  }
  replace ((((gamma * cos (gamma * x)) * (1 + x * x) - sin (gamma * x) * (2 * x)) / (1 + x * x) ^ 2))
    with (gamma * cos (gamma * x) / (1 + x * x) -
          2 * (x * sin (gamma * x) / ((1 + x * x) * (1 + x * x)))) in Hraw.
  - exact Hraw.
  - replace ((1 + x * x) ^ 2) with ((1 + x * x) * (1 + x * x)) by (unfold pow; ring).
    assert (Hp0 : 1 + x * x <> 0) by (apply Rgt_not_eq; assert (Hsq : 0 <= x * x) by apply Rle_0_sqr; lra).
    assert (Hp02 : (1 + x * x) * (1 + x * x) <> 0) by (apply Rgt_not_eq; apply Rmult_lt_0_compat;
      [assert (Hsq : 0 <= x * x) by apply Rle_0_sqr; lra |
       assert (Hsq : 0 <= x * x) by apply Rle_0_sqr; lra]).
    field; auto.
Qed.

(* d/du [−(cos(γu)·u)/(1+u²)] = γu sin(γu)/(1+u²) − cos(γu)(1−u²)/(1+u²)² *)
Lemma is_derive_neg_cos_u_over_1p1p2 : forall gamma x : R,
  is_derive (fun u => - (cos (gamma * u) * u) / (1 + u * u)) x
    (gamma * (x * sin (gamma * x) / (1 + x * x)) -
     cos (gamma * x) * (1 - x * x) / ((1 + x * x) * (1 + x * x))).
Proof.
  intros gamma x.
  assert (Hnum : is_derive (fun u => - (cos (gamma * u) * u)) x
                     (gamma * (x * sin (gamma * x)) - cos (gamma * x))).
  { exact (is_derive_neg_cos_u gamma x). }
  assert (Hden : is_derive (fun u => 1 + u * u) x (2 * x)).
  { assert (Hd_sq : is_derive (fun u : R => u * u) x (2 * x)).
    { assert (Hraw2 : is_derive (fun u : R => u * u) x (1 * x + x * 1)).
      { apply (is_derive_mult id id x 1 1).
        - change (is_derive (fun u : R => u) x one).
          apply (is_derive_id (K := R_AbsRing)).
        - change (is_derive (fun u : R => u) x one).
          apply (is_derive_id (K := R_AbsRing)).
        - intros n m; apply Rmult_comm. }
      replace (1 * x + x * 1) with (2 * x) in Hraw2 by ring.
      exact Hraw2. }
    assert (Hplus : is_derive (fun u => 1 + u * u) x (0 + 2 * x)).
    { apply (is_derive_plus (fun _ : R => 1) (fun u => u * u) x 0 (2 * x)).
      - change (is_derive (fun _ : R => 1) x zero).
        apply (is_derive_const 1 x).
      - exact Hd_sq. }
    replace (0 + 2 * x) with (2 * x) in Hplus by ring.
    exact Hplus.
  }
  assert (Hraw : is_derive (fun u => - (cos (gamma * u) * u) / (1 + u * u)) x
                   (((gamma * (x * sin (gamma * x)) - cos (gamma * x)) * (1 + x * x) -
                     (- (cos (gamma * x) * x)) * (2 * x)) / (1 + x * x) ^ 2)).
  { apply (is_derive_div (fun u => - (cos (gamma * u) * u)) (fun u => 1 + u * u) x
             (gamma * (x * sin (gamma * x)) - cos (gamma * x)) (2 * x)).
    - exact Hnum.
    - exact Hden.
    - apply Rgt_not_eq.
      assert (Hsq : 0 <= x * x) by apply Rle_0_sqr.
      lra.
  }
  replace (((gamma * (x * sin (gamma * x)) - cos (gamma * x)) * (1 + x * x) -
            (- (cos (gamma * x) * x)) * (2 * x)) / (1 + x * x) ^ 2)
    with (gamma * (x * sin (gamma * x) / (1 + x * x)) -
          cos (gamma * x) * (1 - x * x) / ((1 + x * x) * (1 + x * x))) in Hraw.
  - exact Hraw.
  - replace ((1 + x * x) ^ 2) with ((1 + x * x) * (1 + x * x)) by (unfold pow; ring).
    assert (Hp0 : 1 + x * x <> 0) by (apply Rgt_not_eq; assert (Hsq : 0 <= x * x) by apply Rle_0_sqr; lra).
    assert (Hp02 : (1 + x * x) * (1 + x * x) <> 0) by (apply Rgt_not_eq; apply Rmult_lt_0_compat;
      [assert (Hsq : 0 <= x * x) by apply Rle_0_sqr; lra |
       assert (Hsq : 0 <= x * x) by apply Rle_0_sqr; lra]).
    field; auto.
Qed.

(* d/du [u·cos(γu)/(1+u²)] = cos(γu)/(1+u²) − γu sin(γu)/(1+u²) − 2u²cos(γu)/(1+u²)² *)
Lemma is_derive_u_cos_over_1p1p2 : forall gamma x : R,
  is_derive (fun u => u * cos (gamma * u) / (1 + u * u)) x
    (cos (gamma * x) / (1 + x * x) -
     gamma * (x * sin (gamma * x) / (1 + x * x)) -
     2 * ((x * x) * cos (gamma * x) / ((1 + x * x) * (1 + x * x)))).
Proof.
  intros gamma x.
  assert (Hnum : is_derive (fun u => u * cos (gamma * u)) x
                     (cos (gamma * x) - gamma * (x * sin (gamma * x)))).
  { assert (Hcos_scal : is_derive (fun u => cos (gamma * u)) x (gamma * (- sin (gamma * x)))).
    { assert (Hmid : is_derive (fun u => cos (gamma * u)) x (scal gamma (- sin (gamma * x)))).
      { apply (is_derive_comp cos (fun u => gamma * u) x (- sin (gamma * x)) gamma).
        - apply is_derive_cos.
        - assert (Hid : is_derive (fun u : R => u) x one)
            by (change (is_derive (fun u : R => u) x one); apply (is_derive_id (K := R_AbsRing))).
          assert (Hsc : is_derive (fun u => gamma * u) x (gamma * 1)).
          { apply (is_derive_scal (fun u : R => u) x gamma 1). exact Hid. }
          replace (gamma * 1) with gamma in Hsc by ring.
          exact Hsc. }
      exact Hmid. }
    assert (Hmult : is_derive (fun u => u * cos (gamma * u)) x
                      (1 * cos (gamma * x) + x * (gamma * (- sin (gamma * x))))).
    { apply (is_derive_mult id (fun u => cos (gamma * u)) x 1 (gamma * (- sin (gamma * x)))).
      - change (is_derive (fun u : R => u) x one).
        apply (is_derive_id (K := R_AbsRing)).
      - exact Hcos_scal.
      - intros n m; apply Rmult_comm. }
    replace (1 * cos (gamma * x) + x * (gamma * (- sin (gamma * x))))
      with (cos (gamma * x) - gamma * (x * sin (gamma * x))) in Hmult by ring.
    exact Hmult.
  }
  assert (Hden : is_derive (fun u => 1 + u * u) x (2 * x)).
  { assert (Hd_sq : is_derive (fun u : R => u * u) x (2 * x)).
    { assert (Hraw2 : is_derive (fun u : R => u * u) x (1 * x + x * 1)).
      { apply (is_derive_mult id id x 1 1).
        - change (is_derive (fun u : R => u) x one).
          apply (is_derive_id (K := R_AbsRing)).
        - change (is_derive (fun u : R => u) x one).
          apply (is_derive_id (K := R_AbsRing)).
        - intros n m; apply Rmult_comm. }
      replace (1 * x + x * 1) with (2 * x) in Hraw2 by ring.
      exact Hraw2. }
    assert (Hplus : is_derive (fun u => 1 + u * u) x (0 + 2 * x)).
    { apply (is_derive_plus (fun _ : R => 1) (fun u => u * u) x 0 (2 * x)).
      - change (is_derive (fun _ : R => 1) x zero).
        apply (is_derive_const 1 x).
      - exact Hd_sq. }
    replace (0 + 2 * x) with (2 * x) in Hplus by ring.
    exact Hplus.
  }
  assert (Hraw : is_derive (fun u => u * cos (gamma * u) / (1 + u * u)) x
                   (((cos (gamma * x) - gamma * (x * sin (gamma * x))) * (1 + x * x) -
                     (x * cos (gamma * x)) * (2 * x)) / (1 + x * x) ^ 2)).
  { apply (is_derive_div (fun u => u * cos (gamma * u)) (fun u => 1 + u * u) x
             (cos (gamma * x) - gamma * (x * sin (gamma * x))) (2 * x)).
    - exact Hnum.
    - exact Hden.
    - apply Rgt_not_eq.
      assert (Hsq : 0 <= x * x) by apply Rle_0_sqr.
      lra.
  }
  replace (((cos (gamma * x) - gamma * (x * sin (gamma * x))) * (1 + x * x) -
            (x * cos (gamma * x)) * (2 * x)) / (1 + x * x) ^ 2)
    with (cos (gamma * x) / (1 + x * x) -
          gamma * (x * sin (gamma * x) / (1 + x * x)) -
          2 * ((x * x) * cos (gamma * x) / ((1 + x * x) * (1 + x * x)))) in Hraw.
  - exact Hraw.
  - replace ((1 + x * x) ^ 2) with ((1 + x * x) * (1 + x * x)) by (unfold pow; ring).
    assert (Hp0 : 1 + x * x <> 0) by (apply Rgt_not_eq; assert (Hsq : 0 <= x * x) by apply Rle_0_sqr; lra).
    assert (Hp02 : (1 + x * x) * (1 + x * x) <> 0) by (apply Rgt_not_eq; apply Rmult_lt_0_compat;
      [assert (Hsq : 0 <= x * x) by apply Rle_0_sqr; lra |
       assert (Hsq : 0 <= x * x) by apply Rle_0_sqr; lra]).
    field; auto.
Qed.

(* ---------------- φ → 0 at ∞（有界 × 趋于 0） ---------------- *)

Lemma filterlim_phi1_p_infty : forall gamma : R,
  filterlim (fun u => sin (gamma * u) / (1 + u * u)) (Rbar_locally p_infty) (locally 0).
Proof.
  intro gamma.
  apply (filterlim_ext (fun u => sin (gamma * u) * (/ (1 + u * u)))
                       (fun u => sin (gamma * u) / (1 + u * u))).
  - intro u. unfold Rdiv. reflexivity.
  - apply (filterlim_bounded_mul_zero (fun u => sin (gamma * u)) (fun u => / (1 + u * u))).
    + apply filterlim_1_over_1px2_p_infty.
    + exists 1.
      exists 0. intros y Hy.
      exact (Rabs_sin_le_one (gamma * y)).
Qed.

Lemma filterlim_phi2_p_infty : forall gamma : R,
  filterlim (fun u => - (cos (gamma * u) * u) / (1 + u * u)) (Rbar_locally p_infty) (locally 0).
Proof.
  intro gamma.
  apply (filterlim_ext (fun u => (- cos (gamma * u)) * (u * / (1 + u * u)))
                       (fun u => - (cos (gamma * u) * u) / (1 + u * u))).
  - intro u.
    unfold Rdiv.
    rewrite Ropp_mult_distr_l.
    rewrite Rmult_assoc.
    reflexivity.
  - apply (filterlim_bounded_mul_zero (fun u => - cos (gamma * u)) (fun u => u / (1 + u * u))).
    + apply filterlim_x_over_1px2_p_infty.
    + exists 1.
      exists 0. intros y Hy.
      rewrite Rabs_Ropp.
      exact (Rabs_cos_le_one (gamma * y)).
Qed.

Lemma filterlim_phi3_p_infty : forall gamma : R,
  filterlim (fun u => u * cos (gamma * u) / (1 + u * u)) (Rbar_locally p_infty) (locally 0).
Proof.
  intro gamma.
  apply (filterlim_ext (fun u => cos (gamma * u) * (u * / (1 + u * u)))
                       (fun u => u * cos (gamma * u) / (1 + u * u))).
  - intro u.
    unfold Rdiv.
    rewrite (Rmult_comm u (cos (gamma * u))).
    rewrite Rmult_assoc.
    reflexivity.
  - apply (filterlim_bounded_mul_zero (fun u => cos (gamma * u)) (fun u => u / (1 + u * u))).
    + apply filterlim_x_over_1px2_p_infty.
    + exists 1.
      exists 0. intros y Hy.
      exact (Rabs_cos_le_one (gamma * y)).
Qed.

(* ---------------- 边界引理 ---------------- *)

(* at_right x ⊆ locally x *)
Lemma filter_le_at_right_locally : forall x : R, filter_le (at_right x) (locally x).
Proof.
  intros x P HP.
  destruct (locally_iff_open_ball x P) as [Hiff _].
  destruct (Hiff HP) as [eps [Heps_pos Hball]].
  exists (mkposreal eps Heps_pos).
  intros y Hy Hy0.
  apply Hball.
  unfold ball, AbsRing_ball in Hy; simpl in Hy.
  change (Rabs (y - x) < eps) in Hy.
  exact Hy.
Qed.

(* 连续 ⇒ 沿 at_right 的极限 *)
Lemma filterlim_at_right_cont : forall (f : R -> R) (x : R),
  continuous f x -> filterlim f (at_right x) (locally (f x)).
Proof.
  intros f x Hc.
  apply (filterlim_filter_le_1 (F := locally x) f).
  - apply filter_le_at_right_locally.
  - unfold continuous in Hc. exact Hc.
Qed.

(* 边界引理：∫₀^∞ φ'(u)du = lim_{∞}φ − φ(0) *)
Lemma RInt_gen_deriv_boundary : forall (phi dphi : R -> R) (L : R),
  (forall x, 0 <= x -> is_derive phi x (dphi x)) ->
  (forall x, 0 <= x -> continuous dphi x) ->
  filterlim phi (at_right 0) (locally (phi 0)) ->
  filterlim phi (Rbar_locally p_infty) (locally L) ->
  is_RInt_gen dphi (at_right 0) (Rbar_locally p_infty) (L - phi 0).
Proof.
  intros phi dphi L Hd Hcont Hright Hinfty.
  assert (Hder : is_RInt_gen (Derive phi) (at_right 0) (Rbar_locally p_infty) (L - phi 0)).
  { apply (is_RInt_gen_Derive (Fa := at_right 0) (Fb := Rbar_locally p_infty)).
    - (* filter_prod：ex_derive on [Rmin,Rmax] *)
      apply (Filter_prod (at_right 0) (Rbar_locally p_infty)
               (fun ab : R * R => forall x : R,
                  Rmin (fst ab) (snd ab) <= x <= Rmax (fst ab) (snd ab) -> ex_derive phi x)
               (fun a : R => 0 < a) (fun b : R => 1 <= b)).
      + exists (mkposreal 1 Rlt_0_1).
        intros y Hy Hy0.
        lra.
      + exists 1.
        intros y Hy.
        lra.
      + intros a b Ha Hb x Hx.
        exists (dphi x).
        apply Hd.
        assert (Hmin : 0 < Rmin a b).
        { apply Rmin_pos; [exact Ha | lra]. }
        apply Rlt_le in Hmin.
        apply Rle_trans with (Rmin a b); [exact Hmin | exact (proj1 Hx)].
    - (* filter_prod：continuous (Derive phi) on [Rmin,Rmax] *)
      apply (Filter_prod (at_right 0) (Rbar_locally p_infty)
               (fun ab : R * R => forall x : R,
                  Rmin (fst ab) (snd ab) <= x <= Rmax (fst ab) (snd ab) -> continuous (Derive phi) x)
               (fun a : R => 0 < a) (fun b : R => 1 <= b)).
      + exists (mkposreal 1 Rlt_0_1).
        intros y Hy Hy0.
        lra.
      + exists 1.
        intros y Hy.
        lra.
      + intros a b Ha Hb x Hx.
        assert (Hx0 : 0 < x).
        { assert (Hmin : 0 < Rmin a b).
          { destruct (Rle_dec a b) as [Hab | Hba].
            - rewrite (Rmin_left a b Hab). exact Ha.
            - assert (Hba_le : b <= a) by lra.
              rewrite (Rmin_right a b Hba_le). lra. }
          destruct Hx as [Hx1 Hx2].
          simpl in Hx1, Hx2.
          lra. }
        unfold continuous.
        unfold filterlim.
        intros P HP.
        assert (Hdx : Derive phi x = dphi x) by (apply is_derive_unique; apply Hd; lra).
        assert (Hpos : locally x (fun y : R => 0 < y)).
        { exists (mkposreal (x / 2) (Rdiv_lt_0_compat x 2 Hx0 Rlt_0_2)).
          intros y Hy.
          unfold ball, AbsRing_ball in Hy; simpl in Hy.
          change (Rabs (y - x) < x / 2) in Hy.
          apply Rabs_def2 in Hy.
          destruct Hy as [Hy1 Hy2].
          lra. }
        assert (Hloc : locally x (fun y : R => P (dphi y))).
        { unfold continuous, filterlim in Hcont.
          apply (Hcont x (Rlt_le 0 x Hx0) P).
          rewrite Hdx in HP.
          exact HP. }
        apply (filter_imp (fun y : R => 0 < y /\ P (dphi y)) (fun y : R => P (Derive phi y))).
        * intros y [Hy0 HPy].
          replace (Derive phi y) with (dphi y) by (symmetry; apply is_derive_unique; apply Hd; apply Rlt_le; exact Hy0).
          exact HPy.
        * apply (filter_and (fun y : R => 0 < y) (fun y : R => P (dphi y))).
          -- exact Hpos.
          -- exact Hloc.
    - exact Hright.
    - exact Hinfty.
  }
  apply (is_RInt_gen_ext (Derive phi) dphi (L - phi 0)).
  - apply (Filter_prod (at_right 0) (Rbar_locally p_infty)
             (fun ab : R * R => forall x : R,
                Rmin (fst ab) (snd ab) < x < Rmax (fst ab) (snd ab) -> Derive phi x = dphi x)
             (fun a : R => 0 <= a) (fun b : R => 0 <= b)).
    + exists (mkposreal 1 Rlt_0_1).
      intros y Hy Hy0.
      lra.
    + exists 0.
      intros y Hy.
      lra.
    + intros a b Ha Hb x Hx.
      apply is_derive_unique.
      apply Hd.
      apply Rle_trans with (Rmin a b); [apply Rmin_glb; [exact Ha | exact Hb] | apply Rlt_le; exact (proj1 Hx)].
  - exact Hder.
Qed.

(* ---------------- IBP 恒等式 ---------------- *)

Lemma RInt_gen_cos_ibp : forall gamma : R, 0 < gamma -> gamma * Fcos gamma = 2 * Aint gamma.
Proof.
  intros gamma Hgamma.
  set (phi1 := fun u => sin (gamma * u) / (1 + u * u)).
  set (dphi1 := fun u => gamma * cos (gamma * u) / (1 + u * u) -
                          2 * (u * sin (gamma * u) / ((1 + u * u) * (1 + u * u)))).
  assert (Hbd : is_RInt_gen dphi1 (at_right 0) (Rbar_locally p_infty) 0).
  { assert (Hb : is_RInt_gen dphi1 (at_right 0) (Rbar_locally p_infty) (0 - phi1 0)).
    { apply (RInt_gen_deriv_boundary phi1 dphi1 0).
      - intros x Hx.
        unfold phi1, dphi1.
        apply (is_derive_sin_over_1p1p2 gamma x).
      - intros x Hx.
        unfold dphi1.
        apply (continuous_plus (fun u => gamma * cos (gamma * u) / (1 + u * u))
                               (fun u => - (2 * (u * sin (gamma * u) / ((1 + u * u) * (1 + u * u))))) x).
        + apply (continuous_mult (fun u => gamma * cos (gamma * u)) (fun u => / (1 + u * u)) x).
          * apply (continuous_mult (fun _ : R => gamma) (fun u => cos (gamma * u)) x).
            - apply continuous_const.
            - apply cont_cos_scal.
          * apply cont_1px2.
        + apply (continuous_opp (fun u => 2 * (u * sin (gamma * u) / ((1 + u * u) * (1 + u * u)))) x).
          apply (continuous_mult (fun _ : R => 2) (fun u => u * sin (gamma * u) / ((1 + u * u) * (1 + u * u))) x).
          * apply continuous_const.
          * apply cont_kusin_sq.
      - apply (filterlim_at_right_cont phi1 0).
        unfold phi1.
        apply (continuous_mult (fun u => sin (gamma * u)) (fun u => / (1 + u * u)) 0).
        + apply cont_sin_scal.
        + apply cont_1px2.
      - unfold phi1.
        apply filterlim_phi1_p_infty.
    }
    replace (0 - phi1 0) with 0 in Hb.
    - exact Hb.
    - unfold phi1.
      replace (gamma * 0) with 0 by ring.
      rewrite sin_0.
      unfold Rdiv.
      rewrite Rmult_0_l.
      ring.
  }
  destruct (ex_RInt_gen_kcos gamma) as [lc Hlc].
  destruct (ex_RInt_gen_kusin_sq gamma) as [la Hla].
  assert (Hsplit : is_RInt_gen (fun u => gamma * (cos (gamma * u) / (1 + u * u)) -
                                         2 * (u * sin (gamma * u) / ((1 + u * u) * (1 + u * u))))
                       (at_right 0) (Rbar_locally p_infty) (gamma * lc - 2 * la)).
  { apply (is_RInt_gen_minus (fun u => gamma * (cos (gamma * u) / (1 + u * u)))
                             (fun u => 2 * (u * sin (gamma * u) / ((1 + u * u) * (1 + u * u))))
                             (gamma * lc) (2 * la)).
    - apply (is_RInt_gen_scal (fun u => cos (gamma * u) / (1 + u * u)) gamma lc).
      exact Hlc.
    - apply (is_RInt_gen_scal (fun u => u * sin (gamma * u) / ((1 + u * u) * (1 + u * u))) 2 la).
      exact Hla.
  }
  assert (Hu1 : RInt_gen (fun u => gamma * (cos (gamma * u) / (1 + u * u)) -
                                  2 * (u * sin (gamma * u) / ((1 + u * u) * (1 + u * u))))
               (at_right 0) (Rbar_locally p_infty) = 0).
  { apply (is_RInt_gen_unique (fun u => gamma * (cos (gamma * u) / (1 + u * u)) -
                                        2 * (u * sin (gamma * u) / ((1 + u * u) * (1 + u * u)))) 0).
    apply (is_RInt_gen_ext dphi1 (fun u => gamma * (cos (gamma * u) / (1 + u * u)) -
                                           2 * (u * sin (gamma * u) / ((1 + u * u) * (1 + u * u)))) 0).
    - apply (Filter_prod (at_right 0) (Rbar_locally p_infty)
               (fun ab : R * R => forall x : R,
                  Rmin (fst ab) (snd ab) < x < Rmax (fst ab) (snd ab) ->
                  dphi1 x = gamma * (cos (gamma * x) / (1 + x * x)) -
                            2 * (x * sin (gamma * x) / ((1 + x * x) * (1 + x * x))))
               (fun a : R => 0 <= a) (fun b : R => 0 <= b)).
      + exists (mkposreal 1 Rlt_0_1).
        intros y Hy Hy0.
        lra.
      + exists 0.
        intros y Hy.
        lra.
      + intros a b Ha Hb x Hx.
        unfold dphi1.
        unfold Rdiv.
        ring.
    - exact Hbd.
  }
  assert (Hu2 : RInt_gen (fun u => gamma * (cos (gamma * u) / (1 + u * u)) -
                                  2 * (u * sin (gamma * u) / ((1 + u * u) * (1 + u * u))))
               (at_right 0) (Rbar_locally p_infty) = gamma * lc - 2 * la).
  { apply (is_RInt_gen_unique (fun u => gamma * (cos (gamma * u) / (1 + u * u)) -
                                        2 * (u * sin (gamma * u) / ((1 + u * u) * (1 + u * u))))
                              (gamma * lc - 2 * la)); exact Hsplit. }
  assert (Heq : gamma * lc - 2 * la = 0).
  { rewrite Hu2 in Hu1.
    exact Hu1. }
  assert (Hfc : Fcos gamma = lc)
    by (apply (is_RInt_gen_unique (fun u => cos (gamma * u) / (1 + u * u)) lc); exact Hlc).
  assert (Hfa : Aint gamma = la)
    by (apply (is_RInt_gen_unique (fun u => u * sin (gamma * u) / ((1 + u * u) * (1 + u * u))) la); exact Hla).
  rewrite Hfc.
  rewrite Hfa.
  lra.
Qed.

(* C = F − B₀：u²/(1+u²)² + 1/(1+u²)² = 1/(1+u²) 逐点 *)
Lemma RInt_gen_u2cos_decomp : forall gamma : R, Cint gamma = Fcos gamma - B0int gamma.
Proof.
  intro gamma.
  destruct (ex_RInt_gen_ku2cos_sq gamma) as [lc Hlc].
  destruct (ex_RInt_gen_kcos_sq gamma) as [lb Hlb].
  destruct (ex_RInt_gen_kcos gamma) as [lf Hlf].
  assert (Hplus : is_RInt_gen (fun u => (u * u) * cos (gamma * u) / ((1 + u * u) * (1 + u * u)) +
                                       cos (gamma * u) / ((1 + u * u) * (1 + u * u)))
                       (at_right 0) (Rbar_locally p_infty) (lc + lb)).
  { apply (is_RInt_gen_plus (fun u => (u * u) * cos (gamma * u) / ((1 + u * u) * (1 + u * u)))
                            (fun u => cos (gamma * u) / ((1 + u * u) * (1 + u * u))) lc lb).
    - exact Hlc.
    - exact Hlb.
  }
  assert (Hp : forall u : R, (u * u) * cos (gamma * u) / ((1 + u * u) * (1 + u * u)) +
                              cos (gamma * u) / ((1 + u * u) * (1 + u * u)) =
                              cos (gamma * u) / (1 + u * u)).
  { intro u.
    field.
    all: try (apply Rgt_not_eq; assert (Hsq : 0 <= u * u) by apply Rle_0_sqr; lra).
    all: try (apply Rgt_not_eq; apply Rmult_lt_0_compat;
              [assert (Hsq : 0 <= u * u) by apply Rle_0_sqr; lra |
               assert (Hsq : 0 <= u * u) by apply Rle_0_sqr; lra]).
    all: try lra.
  }
  assert (Hext : is_RInt_gen (fun u => cos (gamma * u) / (1 + u * u))
                       (at_right 0) (Rbar_locally p_infty) (lc + lb)).
  { apply (is_RInt_gen_ext (fun u => (u * u) * cos (gamma * u) / ((1 + u * u) * (1 + u * u)) +
                                     cos (gamma * u) / ((1 + u * u) * (1 + u * u)))
                           (fun u => cos (gamma * u) / (1 + u * u)) (lc + lb)).
    - apply (Filter_prod (at_right 0) (Rbar_locally p_infty)
               (fun ab : R * R => forall x : R,
                  Rmin (fst ab) (snd ab) < x < Rmax (fst ab) (snd ab) ->
                  (x * x) * cos (gamma * x) / ((1 + x * x) * (1 + x * x)) +
                  cos (gamma * x) / ((1 + x * x) * (1 + x * x)) =
                  cos (gamma * x) / (1 + x * x))
               (fun _ : R => True) (fun _ : R => True)).
      + exists (mkposreal 1 Rlt_0_1).
        intros y Hy Hy0.
        trivial.
      + exists 0.
        intros y Hy.
        trivial.
      + intros a b Ha Hb x Hx; apply Hp.
    - exact Hplus.
  }
  assert (Heq : lf = lc + lb).
  { assert (Hu1 : RInt_gen (fun u => cos (gamma * u) / (1 + u * u)) (at_right 0) (Rbar_locally p_infty) = lf).
    { apply (is_RInt_gen_unique (fun u => cos (gamma * u) / (1 + u * u)) lf); exact Hlf. }
    assert (Hu2 : RInt_gen (fun u => cos (gamma * u) / (1 + u * u)) (at_right 0) (Rbar_locally p_infty) = lc + lb).
    { apply (is_RInt_gen_unique (fun u => cos (gamma * u) / (1 + u * u)) (lc + lb)); exact Hext. }
    lra. }
  assert (Hc : Cint gamma = lc)
    by (apply (is_RInt_gen_unique (fun u => (u * u) * cos (gamma * u) / ((1 + u * u) * (1 + u * u))) lc); exact Hlc).
  assert (Hb0 : B0int gamma = lb)
    by (apply (is_RInt_gen_unique (fun u => cos (gamma * u) / ((1 + u * u) * (1 + u * u))) lb); exact Hlb).
  assert (Hf : Fcos gamma = lf)
    by (apply (is_RInt_gen_unique (fun u => cos (gamma * u) / (1 + u * u)) lf); exact Hlf).
  rewrite <- Hf in Heq.
  rewrite <- Hc in Heq.
  rewrite <- Hb0 in Heq.
  lra.
Qed.

(* 2C = F − γG *)
Lemma RInt_gen_u_cos_ibp : forall gamma : R, 0 < gamma -> 2 * Cint gamma = Fcos gamma - gamma * Gsin gamma.
Proof.
  intros gamma Hgamma.
  set (phi3 := fun u => u * cos (gamma * u) / (1 + u * u)).
  set (dphi3 := fun u => cos (gamma * u) / (1 + u * u) -
                         gamma * (u * sin (gamma * u) / (1 + u * u)) -
                         2 * ((u * u) * cos (gamma * u) / ((1 + u * u) * (1 + u * u)))).
  assert (Hbd : is_RInt_gen dphi3 (at_right 0) (Rbar_locally p_infty) 0).
  { assert (Hb : is_RInt_gen dphi3 (at_right 0) (Rbar_locally p_infty) (0 - phi3 0)).
    { apply (RInt_gen_deriv_boundary phi3 dphi3 0).
      - intros x Hx.
        unfold phi3, dphi3.
        apply (is_derive_u_cos_over_1p1p2 gamma x).
      - intros x Hx.
        unfold dphi3.
        apply (continuous_plus (fun u => cos (gamma * u) / (1 + u * u) -
                                         gamma * (u * sin (gamma * u) / (1 + u * u)))
                               (fun u => - (2 * ((u * u) * cos (gamma * u) / ((1 + u * u) * (1 + u * u))))) x).
        + apply (continuous_plus (fun u => cos (gamma * u) / (1 + u * u))
                                 (fun u => - (gamma * (u * sin (gamma * u) / (1 + u * u)))) x).
          * apply cont_kcos.
          * apply (continuous_opp (fun u => gamma * (u * sin (gamma * u) / (1 + u * u))) x).
            apply (continuous_mult (fun _ : R => gamma) (fun u => u * sin (gamma * u) / (1 + u * u)) x).
            -- apply continuous_const.
            -- apply cont_kusin.
        + apply (continuous_opp (fun u => 2 * ((u * u) * cos (gamma * u) / ((1 + u * u) * (1 + u * u)))) x).
          apply (continuous_mult (fun _ : R => 2) (fun u => (u * u) * cos (gamma * u) / ((1 + u * u) * (1 + u * u))) x).
          * apply continuous_const.
          * apply cont_ku2cos_sq.
      - apply (filterlim_at_right_cont phi3 0).
        unfold phi3.
        apply (continuous_mult (fun u => u * cos (gamma * u)) (fun u => / (1 + u * u)) 0).
        + apply (continuous_mult id (fun u => cos (gamma * u)) 0).
          * apply continuous_id.
          * apply cont_cos_scal.
        + apply cont_1px2.
      - unfold phi3.
        apply filterlim_phi3_p_infty.
    }
    replace (0 - phi3 0) with 0 in Hb.
    - exact Hb.
    - unfold phi3.
      replace (gamma * 0) with 0 by ring.
      rewrite cos_0.
      rewrite Rmult_1_r.
      unfold Rdiv.
      ring.
  }
  destruct (ex_RInt_gen_ku2cos_sq gamma) as [lc Hlc].
  destruct (ex_RInt_gen_kcos gamma) as [lf Hlf].
  destruct (ex_RInt_gen_kusin gamma Hgamma) as [lg Hlg].
  assert (Hmid : is_RInt_gen (fun u => cos (gamma * u) / (1 + u * u) - gamma * (u * sin (gamma * u) / (1 + u * u)))
                       (at_right 0) (Rbar_locally p_infty) (lf - gamma * lg)).
  { apply (is_RInt_gen_minus (fun u => cos (gamma * u) / (1 + u * u))
                             (fun u => gamma * (u * sin (gamma * u) / (1 + u * u))) lf (gamma * lg)).
    - exact Hlf.
    - apply (is_RInt_gen_scal (fun u => u * sin (gamma * u) / (1 + u * u)) gamma lg).
      exact Hlg.
  }
  assert (Hsplit : is_RInt_gen dphi3 (at_right 0) (Rbar_locally p_infty) (lf - gamma * lg - 2 * lc)).
  { unfold dphi3.
    apply (is_RInt_gen_minus (fun u => cos (gamma * u) / (1 + u * u) - gamma * (u * sin (gamma * u) / (1 + u * u)))
                             (fun u => 2 * ((u * u) * cos (gamma * u) / ((1 + u * u) * (1 + u * u))))
                             (lf - gamma * lg) (2 * lc)).
    - exact Hmid.
    - apply (is_RInt_gen_scal (fun u => (u * u) * cos (gamma * u) / ((1 + u * u) * (1 + u * u))) 2 lc).
      exact Hlc.
  }
  assert (Hu1 : RInt_gen dphi3 (at_right 0) (Rbar_locally p_infty) = 0).
  { apply (is_RInt_gen_unique dphi3 0); exact Hbd. }
  assert (Hu2 : RInt_gen dphi3 (at_right 0) (Rbar_locally p_infty) = lf - gamma * lg - 2 * lc).
  { apply (is_RInt_gen_unique dphi3 (lf - gamma * lg - 2 * lc)); exact Hsplit. }
  assert (Heq : lf - gamma * lg - 2 * lc = 0).
  { rewrite Hu2 in Hu1.
    exact Hu1. }
  assert (Hc : Cint gamma = lc)
    by (apply (is_RInt_gen_unique (fun u => (u * u) * cos (gamma * u) / ((1 + u * u) * (1 + u * u))) lc); exact Hlc).
  assert (Hf : Fcos gamma = lf)
    by (apply (is_RInt_gen_unique (fun u => cos (gamma * u) / (1 + u * u)) lf); exact Hlf).
  assert (Hg : Gsin gamma = lg)
    by (apply (is_RInt_gen_unique (fun u => u * sin (gamma * u) / (1 + u * u)) lg); exact Hlg).
  rewrite <- Hf in Heq.
  rewrite <- Hg in Heq.
  rewrite <- Hc in Heq.
  lra.
Qed.

(* γG = B − F（B := 2B₀） *)
Lemma RInt_gen_sin_ibp : forall gamma : R, 0 < gamma -> gamma * Gsin gamma = Bint gamma - Fcos gamma.
Proof.
  intros gamma Hgamma.
  set (phi2 := fun u => - (cos (gamma * u) * u) / (1 + u * u)).
  set (dphi2 := fun u => gamma * (u * sin (gamma * u) / (1 + u * u)) -
                         cos (gamma * u) * (1 - u * u) / ((1 + u * u) * (1 + u * u))).
  assert (Hbd : is_RInt_gen dphi2 (at_right 0) (Rbar_locally p_infty) 0).
  { assert (Hb : is_RInt_gen dphi2 (at_right 0) (Rbar_locally p_infty) (0 - phi2 0)).
    { apply (RInt_gen_deriv_boundary phi2 dphi2 0).
      - intros x Hx.
        unfold phi2, dphi2.
        apply (is_derive_neg_cos_u_over_1p1p2 gamma x).
      - intros x Hx.
        unfold dphi2.
        apply (continuous_plus (fun u => gamma * (u * sin (gamma * u) / (1 + u * u)))
                               (fun u => - (cos (gamma * u) * (1 - u * u) / ((1 + u * u) * (1 + u * u)))) x).
        + apply (continuous_mult (fun _ : R => gamma) (fun u => u * sin (gamma * u) / (1 + u * u)) x).
          * apply continuous_const.
          * apply cont_kusin.
        + apply (continuous_opp (fun u => cos (gamma * u) * (1 - u * u) / ((1 + u * u) * (1 + u * u))) x).
          apply cont_k2fun.
      - apply (filterlim_at_right_cont phi2 0).
        unfold phi2.
        apply (continuous_mult (fun u => - (cos (gamma * u) * u)) (fun u => / (1 + u * u)) 0).
        + apply (continuous_opp (fun u => cos (gamma * u) * u) 0).
          apply (continuous_mult (fun u => cos (gamma * u)) id 0).
          * apply cont_cos_scal.
          * apply continuous_id.
        + apply cont_1px2.
      - unfold phi2.
        apply filterlim_phi2_p_infty.
    }
    replace (0 - phi2 0) with 0 in Hb.
    - exact Hb.
    - unfold phi2.
      replace (gamma * 0) with 0 by ring.
      rewrite cos_0.
      unfold Rdiv.
      ring.
  }
  destruct (ex_RInt_gen_kusin gamma Hgamma) as [lg Hlg].
  destruct (ex_RInt_gen_kcos_sq gamma) as [lb Hlb].
  destruct (ex_RInt_gen_kcos gamma) as [lf Hlf].
  destruct (ex_RInt_gen_ku2cos_sq gamma) as [lc Hlc].
  assert (Hp2 : forall u : R, cos (gamma * u) * (1 - u * u) / ((1 + u * u) * (1 + u * u)) =
                             cos (gamma * u) / ((1 + u * u) * (1 + u * u)) -
                             (u * u) * cos (gamma * u) / ((1 + u * u) * (1 + u * u))).
  { intro u.
    field.
    all: try (apply Rgt_not_eq; assert (Hsq : 0 <= u * u) by apply Rle_0_sqr; lra).
    all: try (apply Rgt_not_eq; apply Rmult_lt_0_compat;
              [assert (Hsq : 0 <= u * u) by apply Rle_0_sqr; lra |
               assert (Hsq : 0 <= u * u) by apply Rle_0_sqr; lra]).
    all: try lra.
  }
  assert (Hmid : is_RInt_gen (fun u => cos (gamma * u) / ((1 + u * u) * (1 + u * u)) -
                                       (u * u) * cos (gamma * u) / ((1 + u * u) * (1 + u * u)))
                       (at_right 0) (Rbar_locally p_infty) (lb - lc)).
  { apply (is_RInt_gen_minus (fun u => cos (gamma * u) / ((1 + u * u) * (1 + u * u)))
                             (fun u => (u * u) * cos (gamma * u) / ((1 + u * u) * (1 + u * u))) lb lc).
    - exact Hlb.
    - exact Hlc.
  }
  assert (Hmid2 : is_RInt_gen (fun u => cos (gamma * u) * (1 - u * u) / ((1 + u * u) * (1 + u * u)))
                       (at_right 0) (Rbar_locally p_infty) (lb - lc)).
  { apply (is_RInt_gen_ext (fun u => cos (gamma * u) / ((1 + u * u) * (1 + u * u)) -
                                     (u * u) * cos (gamma * u) / ((1 + u * u) * (1 + u * u)))
                           (fun u => cos (gamma * u) * (1 - u * u) / ((1 + u * u) * (1 + u * u))) (lb - lc)).
    - apply (Filter_prod (at_right 0) (Rbar_locally p_infty)
               (fun ab : R * R => forall x : R,
                  Rmin (fst ab) (snd ab) < x < Rmax (fst ab) (snd ab) ->
                  cos (gamma * x) / ((1 + x * x) * (1 + x * x)) -
                  (x * x) * cos (gamma * x) / ((1 + x * x) * (1 + x * x)) =
                  cos (gamma * x) * (1 - x * x) / ((1 + x * x) * (1 + x * x)))
               (fun _ : R => True) (fun _ : R => True)).
      + exists (mkposreal 1 Rlt_0_1).
        intros y Hy Hy0.
        trivial.
      + exists 0.
        intros y Hy.
        trivial.
      + intros a b Ha Hb x Hx.
        symmetry.
        apply Hp2.
    - exact Hmid.
  }
  assert (Hsplit : is_RInt_gen dphi2 (at_right 0) (Rbar_locally p_infty) (gamma * lg - (lb - lc))).
  { unfold dphi2.
    apply (is_RInt_gen_minus (fun u => gamma * (u * sin (gamma * u) / (1 + u * u)))
                             (fun u => cos (gamma * u) * (1 - u * u) / ((1 + u * u) * (1 + u * u)))
                             (gamma * lg) (lb - lc)).
    - apply (is_RInt_gen_scal (fun u => u * sin (gamma * u) / (1 + u * u)) gamma lg).
      exact Hlg.
    - exact Hmid2.
  }
  assert (Hu1 : RInt_gen dphi2 (at_right 0) (Rbar_locally p_infty) = 0).
  { apply (is_RInt_gen_unique dphi2 0); exact Hbd. }
  assert (Hu2 : RInt_gen dphi2 (at_right 0) (Rbar_locally p_infty) = gamma * lg - (lb - lc)).
  { apply (is_RInt_gen_unique dphi2 (gamma * lg - (lb - lc))); exact Hsplit. }
  assert (Heq : gamma * lg - (lb - lc) = 0).
  { rewrite Hu2 in Hu1.
    exact Hu1. }
  assert (Hdec : lc = lf - lb).
  { assert (Hc : Cint gamma = lc)
    by (apply (is_RInt_gen_unique (fun u => (u * u) * cos (gamma * u) / ((1 + u * u) * (1 + u * u))) lc); exact Hlc).
    assert (Hf : Fcos gamma = lf)
      by (apply (is_RInt_gen_unique (fun u => cos (gamma * u) / (1 + u * u)) lf); exact Hlf).
    assert (Hb0 : B0int gamma = lb)
      by (apply (is_RInt_gen_unique (fun u => cos (gamma * u) / ((1 + u * u) * (1 + u * u))) lb); exact Hlb).
    rewrite <- Hc.
    rewrite <- Hf.
    rewrite <- Hb0.
    exact (RInt_gen_u2cos_decomp gamma).
  }
  assert (Hg : Gsin gamma = lg)
    by (apply (is_RInt_gen_unique (fun u => u * sin (gamma * u) / (1 + u * u)) lg); exact Hlg).
  assert (Hf : Fcos gamma = lf)
    by (apply (is_RInt_gen_unique (fun u => cos (gamma * u) / (1 + u * u)) lf); exact Hlf).
  assert (Hb0 : B0int gamma = lb)
    by (apply (is_RInt_gen_unique (fun u => cos (gamma * u) / ((1 + u * u) * (1 + u * u))) lb); exact Hlb).
  assert (Hfin : gamma * lg = 2 * lb - lf) by lra.
  unfold Bint.
  rewrite Hg, Hf, Hb0.
  lra.
Qed.

(* ---------------- 基础值 ---------------- *)

Lemma Fcos_zero : Fcos 0 = PI / 2.
Proof.
  destruct (ex_RInt_gen_kcos 0) as [l Hl].
  assert (Hext : is_RInt_gen (fun u => cos (0 * u) / (1 + u * u)) (at_right 0) (Rbar_locally p_infty) (PI / 2)).
  { apply (is_RInt_gen_ext (fun u => / (1 + u * u)) (fun u => cos (0 * u) / (1 + u * u)) (PI / 2)).
    - apply (Filter_prod (at_right 0) (Rbar_locally p_infty)
               (fun ab : R * R => forall x : R,
                  Rmin (fst ab) (snd ab) < x < Rmax (fst ab) (snd ab) ->
                  / (1 + x * x) = cos (0 * x) / (1 + x * x))
               (fun _ : R => True) (fun _ : R => True)).
      + exists (mkposreal 1 Rlt_0_1).
        intros y Hy Hy0.
        trivial.
      + exists 0.
        intros y Hy.
        trivial.
      + intros a b Ha Hb x Hx.
        rewrite (Rmult_0_l x).
        rewrite cos_0.
        field.
        apply Rgt_not_eq.
        assert (Hsq : 0 <= x * x) by apply Rle_0_sqr.
        lra.
    - exact RInt_gen_atan_half.
  }
  assert (Heq : l = PI / 2).
  { assert (Hu1 : RInt_gen (fun u => cos (0 * u) / (1 + u * u)) (at_right 0) (Rbar_locally p_infty) = PI / 2).
    { apply (is_RInt_gen_unique (fun u => cos (0 * u) / (1 + u * u)) (PI / 2)); exact Hext. }
    assert (Hu2 : RInt_gen (fun u => cos (0 * u) / (1 + u * u)) (at_right 0) (Rbar_locally p_infty) = l).
    { apply (is_RInt_gen_unique (fun u => cos (0 * u) / (1 + u * u)) l); exact Hl. }
    lra. }
  unfold Fcos.
  apply (is_RInt_gen_unique (fun u => cos (0 * u) / (1 + u * u)) (PI / 2)).
  exact Hext.
Qed.

Lemma Aint_zero : Aint 0 = 0.
Proof.
  destruct (ex_RInt_gen_kusin_sq 0) as [l Hl].
  assert (Hext : is_RInt_gen (fun u => u * sin (0 * u) / ((1 + u * u) * (1 + u * u))) (at_right 0) (Rbar_locally p_infty) 0).
  { apply (is_RInt_gen_ext (fun _ : R => 0) (fun u => u * sin (0 * u) / ((1 + u * u) * (1 + u * u))) 0).
    - apply (Filter_prod (at_right 0) (Rbar_locally p_infty)
               (fun ab : R * R => forall x : R,
                  Rmin (fst ab) (snd ab) < x < Rmax (fst ab) (snd ab) ->
                  0 = x * sin (0 * x) / ((1 + x * x) * (1 + x * x)))
               (fun _ : R => True) (fun _ : R => True)).
      + exists (mkposreal 1 Rlt_0_1).
        intros y Hy Hy0.
        trivial.
      + exists 0.
        intros y Hy.
        trivial.
      + intros a b Ha Hb x Hx.
        rewrite (Rmult_0_l x).
        rewrite sin_0.
        rewrite (Rmult_0_r x).
        unfold Rdiv.
        rewrite Rmult_0_l.
        reflexivity.
    - exact is_RInt_gen_zero_fun.
  }
  assert (Heq : l = 0).
  { assert (Hu1 : RInt_gen (fun u => u * sin (0 * u) / ((1 + u * u) * (1 + u * u))) (at_right 0) (Rbar_locally p_infty) = 0).
    { apply (is_RInt_gen_unique (fun u => u * sin (0 * u) / ((1 + u * u) * (1 + u * u))) 0); exact Hext. }
    assert (Hu2 : RInt_gen (fun u => u * sin (0 * u) / ((1 + u * u) * (1 + u * u))) (at_right 0) (Rbar_locally p_infty) = l).
    { apply (is_RInt_gen_unique (fun u => u * sin (0 * u) / ((1 + u * u) * (1 + u * u))) l); exact Hl. }
    lra. }
  unfold Aint.
  apply (is_RInt_gen_unique (fun u => u * sin (0 * u) / ((1 + u * u) * (1 + u * u))) 0).
  exact Hext.
Qed.

Lemma Cint_zero : Cint 0 = PI / 4.
Proof.
  destruct (ex_RInt_gen_ku2cos_sq 0) as [l Hl].
  assert (Hext : is_RInt_gen (fun u => (u * u) * cos (0 * u) / ((1 + u * u) * (1 + u * u))) (at_right 0) (Rbar_locally p_infty) (PI / 4)).
  { apply (is_RInt_gen_ext (fun u => (u * u) / ((1 + u * u) * (1 + u * u)))
                           (fun u => (u * u) * cos (0 * u) / ((1 + u * u) * (1 + u * u))) (PI / 4)).
    - apply (Filter_prod (at_right 0) (Rbar_locally p_infty)
               (fun ab : R * R => forall x : R,
                  Rmin (fst ab) (snd ab) < x < Rmax (fst ab) (snd ab) ->
                  (x * x) / ((1 + x * x) * (1 + x * x)) =
                  (x * x) * cos (0 * x) / ((1 + x * x) * (1 + x * x)))
               (fun _ : R => True) (fun _ : R => True)).
      + exists (mkposreal 1 Rlt_0_1).
        intros y Hy Hy0.
        trivial.
      + exists 0.
        intros y Hy.
        trivial.
      + intros a b Ha Hb x Hx.
        rewrite (Rmult_0_l x).
        rewrite cos_0.
        field.
        apply Rgt_not_eq.
        assert (Hsq : 0 <= x * x) by apply Rle_0_sqr.
        lra.
    - exact RInt_gen_sq3.
  }
  assert (Heq : l = PI / 4).
  { assert (Hu1 : RInt_gen (fun u => (u * u) * cos (0 * u) / ((1 + u * u) * (1 + u * u))) (at_right 0) (Rbar_locally p_infty) = PI / 4).
    { apply (is_RInt_gen_unique (fun u => (u * u) * cos (0 * u) / ((1 + u * u) * (1 + u * u))) (PI / 4)); exact Hext. }
    assert (Hu2 : RInt_gen (fun u => (u * u) * cos (0 * u) / ((1 + u * u) * (1 + u * u))) (at_right 0) (Rbar_locally p_infty) = l).
    { apply (is_RInt_gen_unique (fun u => (u * u) * cos (0 * u) / ((1 + u * u) * (1 + u * u))) l); exact Hl. }
    lra. }
  unfold Cint.
  apply (is_RInt_gen_unique (fun u => (u * u) * cos (0 * u) / ((1 + u * u) * (1 + u * u))) (PI / 4)).
  exact Hext.
Qed.

Lemma Gsin_zero : Gsin 0 = 0.
Proof.
  destruct (ex_RInt_gen_kusin_0) as [l Hl].
  assert (Hext : is_RInt_gen (fun u => u * sin (0 * u) / (1 + u * u)) (at_right 0) (Rbar_locally p_infty) 0).
  { apply (is_RInt_gen_ext (fun _ : R => 0) (fun u => u * sin (0 * u) / (1 + u * u)) 0).
    - apply (Filter_prod (at_right 0) (Rbar_locally p_infty)
               (fun ab : R * R => forall x : R,
                  Rmin (fst ab) (snd ab) < x < Rmax (fst ab) (snd ab) ->
                  0 = x * sin (0 * x) / (1 + x * x))
               (fun _ : R => True) (fun _ : R => True)).
      + exists (mkposreal 1 Rlt_0_1).
        intros y Hy Hy0.
        trivial.
      + exists 0.
        intros y Hy.
        trivial.
      + intros a b Ha Hb x Hx.
        rewrite (Rmult_0_l x).
        rewrite sin_0.
        rewrite (Rmult_0_r x).
        unfold Rdiv.
        rewrite Rmult_0_l.
        reflexivity.
    - exact is_RInt_gen_zero_fun.
  }
  assert (Heq : l = 0).
  { assert (Hu1 : RInt_gen (fun u => u * sin (0 * u) / (1 + u * u)) (at_right 0) (Rbar_locally p_infty) = 0).
    { apply (is_RInt_gen_unique (fun u => u * sin (0 * u) / (1 + u * u)) 0); exact Hext. }
    assert (Hu2 : RInt_gen (fun u => u * sin (0 * u) / (1 + u * u)) (at_right 0) (Rbar_locally p_infty) = l).
    { apply (is_RInt_gen_unique (fun u => u * sin (0 * u) / (1 + u * u)) l); exact Hl. }
    lra. }
  unfold Gsin.
  apply (is_RInt_gen_unique (fun u => u * sin (0 * u) / (1 + u * u)) 0).
  exact Hext.
Qed.




(* ============ 第 12 轮（第四部分）：连续傅里叶深引理基础设施 ============ *)
(* 块 1：sin/cos 的 Lipschitz 与 Taylor 界；块 2：DCT 基础设施（RInt_gen_lim 等）；
   块 3：导数辅助引理（含 is_derive_from_quotient：商一致 ⇒ 可导） *)

(* ============================================================
   第 12 轮（第四部分，块 1）：sin/cos 的 Lipschitz 与 Taylor 界
   用 MVT_abs（Stdlib 中值定理）证明：
     |sin a - sin b| <= |a - b|          （sin 1-Lipschitz）
     |cos a - cos b| <= |a - b|          （cos 1-Lipschitz）
     |sin(a+d) - sin a - d cos a| <= d²  （sin Taylor 一阶余项）
     |cos(a+d) - cos a + d sin a| <= d²  （cos Taylor 一阶余项）
   ============================================================ *)

Lemma Rabs_sin_sub_le : forall a b : R, Rabs (sin a - sin b) <= Rabs (a - b).
Proof.
  intros a b.
  destruct (MVT_abs sin (fun x : R => cos x) a b) as [c [Hc1 Hc2]].
  - intros c0 Hc0.
    apply derivable_pt_lim_sin.
  - rewrite Rabs_minus_sym in Hc1.
    rewrite Hc1.
    rewrite Rabs_minus_sym.
    assert (Hc : Rabs (cos c) <= 1) by apply Rabs_cos_le_one.
    assert (Hp : 0 <= Rabs (a - b)) by apply Rabs_pos.
    nra.
Qed.

Lemma Rabs_cos_sub_le : forall a b : R, Rabs (cos a - cos b) <= Rabs (a - b).
Proof.
  intros a b.
  destruct (MVT_abs cos (fun x : R => - sin x) a b) as [c [Hc1 Hc2]].
  - intros c0 Hc0.
    apply derivable_pt_lim_cos.
  - rewrite Rabs_minus_sym in Hc1.
    rewrite Hc1.
    rewrite Rabs_minus_sym.
    rewrite Rabs_Ropp.
    assert (Hc : Rabs (sin c) <= 1) by apply Rabs_sin_le_one.
    assert (Hp : 0 <= Rabs (a - b)) by apply Rabs_pos.
    nra.
Qed.

(* 夹在 Rmin 0 d 与 Rmax 0 d 之间的数 c 满足 |c| <= |d| *)
Lemma Rmin_Rmax_abs_le : forall c d : R, Rmin 0 d <= c <= Rmax 0 d -> Rabs c <= Rabs d.
Proof.
  intros c d [H1 H2].
  apply Rabs_le.
  split.
  - destruct (Rle_dec 0 d) as [Hd | Hd].
    + assert (Hr : Rabs d = d) by (apply Rabs_right; apply Rle_ge; exact Hd).
      assert (Hm : Rmin 0 d = 0) by (apply Rmin_left; exact Hd).
      assert (Hmx : Rmax 0 d = d) by (apply Rmax_right; exact Hd).
      rewrite Hm in H1. rewrite Hmx in H2.
      rewrite Hr.
      lra.
    + assert (Hd' : d <= 0) by (apply Rlt_le; apply Rnot_le_lt; exact Hd).
      assert (Hr : Rabs d = - d) by (apply Rabs_left; apply Rnot_le_lt; exact Hd).
      assert (Hm : Rmin 0 d = d) by (apply Rmin_right; exact Hd').
      assert (Hmx : Rmax 0 d = 0) by (apply Rmax_left; exact Hd').
      rewrite Hm in H1. rewrite Hmx in H2.
      rewrite Hr.
      lra.
  - destruct (Rle_dec 0 d) as [Hd | Hd].
    + assert (Hr : Rabs d = d) by (apply Rabs_right; apply Rle_ge; exact Hd).
      assert (Hm : Rmin 0 d = 0) by (apply Rmin_left; exact Hd).
      assert (Hmx : Rmax 0 d = d) by (apply Rmax_right; exact Hd).
      rewrite Hm in H1. rewrite Hmx in H2.
      rewrite Hr.
      lra.
    + assert (Hd' : d <= 0) by (apply Rlt_le; apply Rnot_le_lt; exact Hd).
      assert (Hr : Rabs d = - d) by (apply Rabs_left; apply Rnot_le_lt; exact Hd).
      assert (Hm : Rmin 0 d = d) by (apply Rmin_right; exact Hd').
      assert (Hmx : Rmax 0 d = 0) by (apply Rmax_left; exact Hd').
      rewrite Hm in H1. rewrite Hmx in H2.
      rewrite Hr.
      lra.
Qed.

(* |sin(a+d) - sin a - d cos a| <= d * d *)
Lemma Rabs_sin_lin : forall a d : R, Rabs (sin (a + d) - sin a - d * cos a) <= d * d.
Proof.
  intros a d.
  set (phi := fun t : R => sin (a + t) - cos a * t).
  assert (Hphi : Rabs (phi d - phi 0) = Rabs (sin (a + d) - sin a - d * cos a)).
  { unfold phi.
    replace (a + 0) with a by ring.
    replace (sin (a + d) - cos a * d - (sin a - cos a * 0)) with (sin (a + d) - sin a - d * cos a) by ring.
    reflexivity. }
  rewrite <- Hphi.
  destruct (MVT_abs phi (fun t : R => cos (a + t) - cos a) 0 d) as [c [Hc1 Hc2]].
  - intros c0 Hc0.
    unfold phi.
    apply (derivable_pt_lim_minus (fun t : R => sin (a + t)) (fun t : R => cos a * t)
                                  c0 (cos (a + c0)) (cos a)).
    + replace (cos (a + c0)) with (cos (a + c0) * 1) by ring.
      apply (derivable_pt_lim_comp (fun t : R => a + t) sin c0 1 (cos (a + c0))).
      * replace 1 with (0 + 1) by ring.
        apply (derivable_pt_lim_plus (fun _ : R => a) id c0 0 1).
        -- apply derivable_pt_lim_const.
        -- apply derivable_pt_lim_id.
      * apply derivable_pt_lim_sin.
    + assert (Hm : derivable_pt_lim (fun t : R => cos a * t) c0 (0 * c0 + cos a * 1)).
      { apply (derivable_pt_lim_mult (fun _ : R => cos a) id c0 0 1).
        - apply derivable_pt_lim_const.
        - apply derivable_pt_lim_id. }
      replace (0 * c0 + cos a * 1) with (cos a) in Hm by ring.
      exact Hm.
  - rewrite Hc1.
    rewrite (Rminus_0_r d).
    apply Rle_trans with (Rabs c * Rabs d).
    + apply Rmult_le_compat_r.
      * apply Rabs_pos.
      * assert (Hrew : Rabs (a + c - a) = Rabs c) by (f_equal; ring).
        rewrite <- Hrew.
        apply Rabs_cos_sub_le.
    + apply Rle_trans with (Rabs d * Rabs d).
      * apply Rmult_le_compat_r.
        -- apply Rabs_pos.
        -- apply Rmin_Rmax_abs_le.
           exact Hc2.
      * rewrite <- Rabs_mult.
        rewrite Rabs_right; [reflexivity | apply Rle_ge; apply Rle_0_sqr].
Qed.

(* |cos(a+d) - cos a + d sin a| <= d * d *)
Lemma Rabs_cos_lin : forall a d : R, Rabs (cos (a + d) - cos a + d * sin a) <= d * d.
Proof.
  intros a d.
  set (psi := fun t : R => cos (a + t) + sin a * t).
  assert (Hpsi : Rabs (psi d - psi 0) = Rabs (cos (a + d) - cos a + d * sin a)).
  { unfold psi.
    replace (a + 0) with a by ring.
    replace (cos (a + d) + sin a * d - (cos a + sin a * 0)) with (cos (a + d) - cos a + d * sin a) by ring.
    reflexivity. }
  rewrite <- Hpsi.
  destruct (MVT_abs psi (fun t : R => - sin (a + t) + sin a) 0 d) as [c [Hc1 Hc2]].
  - intros c0 Hc0.
    unfold psi.
    apply (derivable_pt_lim_plus (fun t : R => cos (a + t)) (fun t : R => sin a * t)
                                 c0 (- sin (a + c0)) (sin a)).
    + replace (- sin (a + c0)) with ((- sin (a + c0)) * 1) by ring.
      apply (derivable_pt_lim_comp (fun t : R => a + t) cos c0 1 (- sin (a + c0))).
      * replace 1 with (0 + 1) by ring.
        apply (derivable_pt_lim_plus (fun _ : R => a) id c0 0 1).
        -- apply derivable_pt_lim_const.
        -- apply derivable_pt_lim_id.
      * apply derivable_pt_lim_cos.
    + assert (Hm : derivable_pt_lim (fun t : R => sin a * t) c0 (0 * c0 + sin a * 1)).
      { apply (derivable_pt_lim_mult (fun _ : R => sin a) id c0 0 1).
        - apply derivable_pt_lim_const.
        - apply derivable_pt_lim_id. }
      replace (0 * c0 + sin a * 1) with (sin a) in Hm by ring.
      exact Hm.
  - rewrite Hc1.
    rewrite (Rminus_0_r d).
    apply Rle_trans with (Rabs c * Rabs d).
    + apply Rmult_le_compat_r.
      * apply Rabs_pos.
      * replace (- sin (a + c) + sin a) with (- (sin (a + c) - sin a)) by ring.
        rewrite Rabs_Ropp.
        assert (Hrew : Rabs (a + c - a) = Rabs c) by (f_equal; ring).
        rewrite <- Hrew.
        apply Rabs_sin_sub_le.
    + apply Rle_trans with (Rabs d * Rabs d).
      * apply Rmult_le_compat_r.
        -- apply Rabs_pos.
        -- apply Rmin_Rmax_abs_le.
           exact Hc2.
      * rewrite <- Rabs_mult.
        rewrite Rabs_right; [reflexivity | apply Rle_ge; apply Rle_0_sqr].
Qed.
(* ============================================================
   第 12 轮（第四部分，块 2）：DCT 基础设施
     RInt_minus_val            ：积分线性（差）
     is_RInt_gen_pair_bounds   ：从 is_RInt_gen 提取 (a,b) 双端一致界
     ex_RInt_gen_tails         ：可积 ⇒ 尾部积分趋于 0（一致）
     RInt_gen_lim              ：控制收敛（DCT）：lim_h ∫ f_h = ∫ lim_h f_h
   ============================================================ *)

(* 积分之差 = 差的积分（值等式） *)
Lemma RInt_minus_val : forall (f g : R -> R) (a b : R),
  ex_RInt f a b -> ex_RInt g a b ->
  RInt (fun u : R => f u - g u) a b = RInt f a b - RInt g a b.
Proof.
  intros f g a b Hf Hg.
  destruct Hf as [lf Hlf].
  destruct Hg as [lg Hlg].
  assert (Hlf_eq : RInt f a b = lf) by (apply is_RInt_unique; exact Hlf).
  assert (Hlg_eq : RInt g a b = lg) by (apply is_RInt_unique; exact Hlg).
  assert (Hm : is_RInt (fun u : R => f u - g u) a b (lf - lg)).
  { unfold Rminus.
    apply (is_RInt_plus f (fun u : R => - g u) a b lf (- lg)).
    - exact Hlf.
    - exact (is_RInt_opp g a b lg Hlg). }
  assert (Hm_eq : RInt (fun u : R => f u - g u) a b = lf - lg)
    by (apply is_RInt_unique; exact Hm).
  rewrite Hm_eq, Hlf_eq, Hlg_eq.
  reflexivity.
Qed.

(* 从 is_RInt_gen 提取一致界：∃ d, M, ∀ a ∈ (0,d), ∀ b > M, |RInt f a b - l| < eps *)
Lemma is_RInt_gen_pair_bounds :
  forall (f : R -> R) (l : R) (eps : R),
    0 < eps ->
    is_RInt_gen f (at_right 0) (Rbar_locally p_infty) l ->
    exists (d : posreal) (M : R),
      forall (a : R) (b : R),
        0 < a -> a < pos d -> M < b ->
        Rabs (RInt f a b - l) < eps.
Proof.
  intros f l eps Heps Hl.
  unfold is_RInt_gen in Hl.
  rewrite filterlimi_locally in Hl.
  specialize (Hl (mkposreal eps Heps)).
  destruct Hl as [Q R HQ HR Hcomb].
  destruct HQ as [d Hd].
  destruct HR as [M HM].
  exists d, M.
  intros a b Ha Hab HMb.
  assert (HQa : Q a).
  { apply Hd.
    - unfold ball, AbsRing_ball; simpl.
      change (Rabs (a - 0) < pos d).
      assert (Ha0' : 0 <= a - 0) by lra.
      rewrite Rabs_pos_eq; [| exact Ha0'].
      lra.
    - exact Ha. }
  assert (HRb : R b) by (apply HM; exact HMb).
  destruct (Hcomb a b HQa HRb) as [z [Hz Hballz]].
  assert (Hz_eq : RInt f a b = z) by (apply is_RInt_unique; exact Hz).
  rewrite Hz_eq.
  unfold ball, AbsRing_ball in Hballz; simpl in Hballz.
  change (Rabs (z - l) < eps) in Hballz.
  exact Hballz.
Qed.

(* 尾部消失：可积 g（连续）⇒ 对任意 eps，存在 M ≥ 1，∀ b ≥ M，|RInt g M b| < eps *)
Lemma ex_RInt_gen_tails :
  forall (g : R -> R) (eps : R),
    0 < eps ->
    (forall u : R, continuous g u) ->
    ex_RInt_gen g (at_right 0) (Rbar_locally p_infty) ->
    exists M : R, 1 <= M /\
      forall b : R, M <= b -> Rabs (RInt g M b) < eps.
Proof.
  intros g eps Heps Hgcont [l Hl].
  destruct (is_RInt_gen_pair_bounds g l (eps / 2)) as [d [M0 Hpair]].
  - lra.
  - exact Hl.
  set (a0 := pos d / 2).
  assert (Ha0_pos : 0 < a0).
  { unfold a0. apply Rdiv_lt_0_compat; [exact (cond_pos d) | lra]. }
  assert (Ha0_lt : a0 < pos d).
  { unfold a0.
    assert (Hd_pos : 0 < pos d) by exact (cond_pos d).
    apply Rmult_lt_reg_l with 2; [lra |].
    replace (2 * (pos d / 2)) with (pos d) by (unfold Rdiv; field; lra).
    replace (2 * pos d) with (pos d + pos d) by ring.
    lra. }
  set (M := Rmax 1 (M0 + 1)).
  assert (HM1 : 1 <= M) by (unfold M; apply Rmax_l).
  assert (HM0_M : M0 < M).
  { apply Rlt_le_trans with (M0 + 1); [lra | unfold M; apply Rmax_r]. }
  exists M.
  split; [exact HM1 |].
  intros b Hb.
  assert (HbM0 : M0 < b) by (apply Rlt_le_trans with M; [exact HM0_M | exact Hb]).
  assert (Hbd2 : Rabs (RInt g a0 b - l) < eps / 2)
    by (apply Hpair; [exact Ha0_pos | exact Ha0_lt | exact HbM0]).
  assert (Hbd3 : Rabs (RInt g a0 M - l) < eps / 2)
    by (apply Hpair; [exact Ha0_pos | exact Ha0_lt | exact HM0_M]).
  assert (Hch : RInt g a0 M + RInt g M b = RInt g a0 b).
  { apply (RInt_Chasles g a0 M b).
    - apply (ex_RInt_continuous g a0 M); intros z Hz; apply Hgcont.
    - apply (ex_RInt_continuous g M b); intros z Hz; apply Hgcont. }
  assert (Heq2 : RInt g M b = RInt g a0 b - RInt g a0 M) by lra.
  rewrite Heq2.
  apply Rle_lt_trans with (Rabs (RInt g a0 b - l) + Rabs (l - RInt g a0 M)).
  + replace (RInt g a0 b - RInt g a0 M) with ((RInt g a0 b - l) + (l - RInt g a0 M)) by ring.
    apply Rabs_triang.
  + assert (Hbd3' : Rabs (l - RInt g a0 M) < eps / 2).
    { rewrite Rabs_minus_sym. exact Hbd3. }
    lra.
Qed.

(* |RInt f a b| ≤ RInt |f| a b（a ≤ b，连续） *)
Lemma RInt_abs_val : forall (f : R -> R) (a b : R),
  a <= b ->
  (forall u : R, continuous f u) ->
  Rabs (RInt f a b) <= RInt (fun u : R => Rabs (f u)) a b.
Proof.
  intros f a b Hab Hfcont.
  apply abs_RInt_le.
  - exact Hab.
  - apply (ex_RInt_continuous f a b); intros z Hz; apply Hfcont.
Qed.

(* 控制收敛（DCT）：lim_h RInt_gen (f h) = RInt_gen f0 *)
Lemma RInt_gen_lim :
  forall (f : R -> R -> R) (f0 : R -> R) (g : R -> R) (e : R -> R -> R)
    (Fh : (R -> Prop) -> Prop),
  ProperFilter Fh ->
  (forall u : R, Rabs (f0 u) <= g u) ->
  (forall h u : R, Rabs (f h u) <= g u) ->
  (forall h u : R, Rabs (f h u - f0 u) <= e h u) ->
  (forall h u : R, 0 <= e h u) ->
  (forall u : R, 0 <= g u) ->
  (forall u : R, continuous g u) ->
  ex_RInt_gen g (at_right 0) (Rbar_locally p_infty) ->
  (forall h u : R, continuous (f h) u) ->
  (forall u : R, continuous f0 u) ->
  (forall h u : R, continuous (e h) u) ->
  (forall M : R, 0 <= M ->
     filterlim (fun h : R => RInt (fun u : R => e h u) 0 M) Fh (locally 0)) ->
  filterlim (fun h : R => RInt_gen (f h) (at_right 0) (Rbar_locally p_infty)) Fh
    (locally (RInt_gen f0 (at_right 0) (Rbar_locally p_infty))).
Proof.
  intros f f0 g e Fh HFh Hf0g Hfg Hfe He0 Hg0 Hgcont Hgex Hfcont Hf0cont Hecont Heconv.
  assert (Hf0ex : ex_RInt_gen f0 (at_right 0) (Rbar_locally p_infty)).
  { apply (ex_RInt_gen_abs_le f0 g 0).
    - intros t Ht; apply Hf0cont.
    - intros t Ht; apply Hgcont.
    - intros t Ht; apply Hg0.
    - intros t Ht; apply Hf0g.
    - exact Hgex. }
  destruct Hf0ex as [l0 Hl0].
  assert (Hl0eq : RInt_gen f0 (at_right 0) (Rbar_locally p_infty) = l0)
    by (apply is_RInt_gen_unique; exact Hl0).
  unfold filterlim.
  intros P HP.
  rewrite Hl0eq in HP.
  destruct (locally_iff_open_ball l0 P) as [Hiff _].
  destruct (Hiff HP) as [eps [Heps_pos Hball]].
  (* 尾部 b0：g 的尾积分 < eps/7 *)
  destruct (ex_RInt_gen_tails g (eps / 7)) as [b0 [Hb0_1 Hb0_tail]].
  - lra.
  - exact Hgcont.
  - exact Hgex.
  (* e 在 [0, b0] 上的积分 → 0（Fh 邻域） *)
  assert (Heneigh : Fh (fun h : R => RInt (fun u : R => e h u) 0 b0 < eps / 7)).
  { assert (Heconv0 : filterlim (fun h : R => RInt (fun u : R => e h u) 0 b0) Fh (locally 0)).
    { apply Heconv. lra. }
    unfold filterlim in Heconv0.
    apply (Heconv0 (fun x : R => x < eps / 7)).
    assert (H7 : 0 < 7) by lra.
    exists (mkposreal (eps / 7) (Rdiv_lt_0_compat eps 7 Heps_pos H7)).
    intros y Hy.
    unfold ball, AbsRing_ball in Hy; simpl in Hy.
    change (Rabs (y - 0) < eps / 7) in Hy.
    rewrite Rminus_0_r in Hy.
    apply Rle_lt_trans with (Rabs y); [apply Rle_abs | exact Hy]. }
  assert (HeRInt_pos : forall h M : R, 0 <= M ->
           0 <= RInt (fun u : R => e h u) 0 M).
  { intros h M HM.
    assert (Hzero : RInt (fun _ : R => 0) 0 M = 0).
    { assert (Hzc : is_RInt (fun _ : R => 0) 0 M (scal (M - 0) 0)).
      { exact (is_RInt_const 0 M 0). }
      assert (Hsz : scal (M - 0) 0 = 0).
      { change ((M - 0) * 0 = 0). rewrite Rmult_0_r. reflexivity. }
      rewrite Hsz in Hzc.
      apply is_RInt_unique.
      exact Hzc. }
    assert (He0_int : RInt (fun _ : R => 0) 0 M <= RInt (fun u : R => e h u) 0 M).
    { apply RInt_le; [lra | | | intros x Hx; apply He0].
      - apply (ex_RInt_continuous (fun _ : R => 0) 0 M).
        intros z Hz; apply continuous_const.
      - apply (ex_RInt_continuous (fun u : R => e h u) 0 M).
        intros z Hz; apply Hecont. }
    rewrite Hzero in He0_int.
    exact He0_int. }
  (* Fh 邻域装配 *)
  apply (filter_imp (fun h : R => RInt (fun u : R => e h u) 0 b0 < eps / 7)
                    (fun h : R => P (RInt_gen (f h) (at_right 0) (Rbar_locally p_infty)))).
  - intros h Heneigh_h.
    assert (Hfh : ex_RInt_gen (f h) (at_right 0) (Rbar_locally p_infty)).
    { apply (ex_RInt_gen_abs_le (f h) g 0).
      - intros t Ht; apply Hfcont.
      - intros t Ht; apply Hgcont.
      - intros t Ht; apply Hg0.
      - intros t Ht; apply Hfg.
      - exact Hgex. }
    destruct Hfh as [lh Hlh].
    assert (Hlheq : RInt_gen (f h) (at_right 0) (Rbar_locally p_infty) = lh)
      by (apply is_RInt_gen_unique; exact Hlh).
    destruct (is_RInt_gen_pair_bounds (f h) lh (eps / 7)) as [dh [Mh Hpair_h]].
    + lra.
    + exact Hlh.
    destruct (is_RInt_gen_pair_bounds f0 l0 (eps / 7)) as [d0 [M0 Hpair_0]].
    + lra.
    + exact Hl0.
    set (a := Rmin 1 (Rmin (pos dh / 2) (pos d0 / 2))).
    set (b := Rmax b0 (Rmax (Mh + 1) (M0 + 1))).
    assert (Ha_pos : 0 < a).
    { unfold a. apply Rmin_pos.
      - lra.
      - apply Rmin_pos.
        + apply Rdiv_lt_0_compat; [exact (cond_pos dh) | lra].
        + apply Rdiv_lt_0_compat; [exact (cond_pos d0) | lra]. }
    assert (Ha_le_1 : a <= 1).
    { unfold a. apply Rmin_l. }
    assert (Ha_lt_dh : a < pos dh).
    { unfold a.
      apply Rle_lt_trans with (Rmin (pos dh / 2) (pos d0 / 2)).
      - apply Rmin_r.
      - apply Rle_lt_trans with (pos dh / 2).
        + apply Rmin_l.
        + assert (Hd_pos : 0 < pos dh) by exact (cond_pos dh).
          lra. }
    assert (Ha_lt_d0 : a < pos d0).
    { unfold a.
      apply Rle_lt_trans with (Rmin (pos dh / 2) (pos d0 / 2)).
      - apply Rmin_r.
      - apply Rle_lt_trans with (pos d0 / 2).
        + apply Rmin_r.
        + assert (Hd_pos : 0 < pos d0) by exact (cond_pos d0).
          lra. }
    assert (Hb_ge_b0 : b0 <= b) by (unfold b; apply Rmax_l).
    assert (Hb_gt_Mh : Mh < b).
    { apply Rlt_le_trans with (Mh + 1); [lra |].
      apply Rle_trans with (Rmax (Mh + 1) (M0 + 1)); [apply Rmax_l | apply Rmax_r]. }
    assert (Hb_gt_M0 : M0 < b).
    { apply Rlt_le_trans with (M0 + 1); [lra |].
      apply Rle_trans with (Rmax (Mh + 1) (M0 + 1)); [apply Rmax_r | apply Rmax_r]. }
    assert (Hpair1 : Rabs (RInt (f h) a b - lh) < eps / 7)
      by (apply Hpair_h; [exact Ha_pos | exact Ha_lt_dh | exact Hb_gt_Mh]).
    assert (Hpair2 : Rabs (RInt f0 a b - l0) < eps / 7)
      by (apply Hpair_0; [exact Ha_pos | exact Ha_lt_d0 | exact Hb_gt_M0]).
    (* 尾部小块 *)
    assert (Htail1 : Rabs (RInt (f h) b0 b) <= RInt g b0 b).
    { apply Rle_trans with (RInt (fun u : R => Rabs (f h u)) b0 b).
      - apply RInt_abs_val; [lra | intros z Hz; apply Hfcont].
      - apply RInt_le; [lra | | | intros x Hx; apply Hfg].
        + apply (ex_RInt_continuous (fun u : R => Rabs (f h u)) b0 b).
          intros z Hz.
          apply (continuous_comp (f h) Rabs z); [apply Hfcont | apply continuous_Rabs].
        + apply (ex_RInt_continuous g b0 b); intros z Hz; apply Hgcont. }
    assert (Htail1' : RInt g b0 b < eps / 7).
    { apply Rle_lt_trans with (Rabs (RInt g b0 b)).
      - apply Rle_abs.
      - apply Hb0_tail; exact Hb_ge_b0. }
    assert (Htail2 : Rabs (RInt f0 b0 b) <= RInt g b0 b).
    { apply Rle_trans with (RInt (fun u : R => Rabs (f0 u)) b0 b).
      - apply RInt_abs_val; [lra | intros z Hz; apply Hf0cont].
      - apply RInt_le; [lra | | | intros x Hx; apply Hf0g].
        + apply (ex_RInt_continuous (fun u : R => Rabs (f0 u)) b0 b).
          intros z Hz.
          apply (continuous_comp f0 Rabs z); [apply Hf0cont | apply continuous_Rabs].
        + apply (ex_RInt_continuous g b0 b); intros z Hz; apply Hgcont. }
    (* 中段（在 [a, b0] 上由 e 控制） *)
    assert (Hmid : Rabs (RInt (f h) a b0 - RInt f0 a b0) <= RInt (fun u : R => e h u) a b0).
    { assert (Hmv : RInt (fun u : R => f h u - f0 u) a b0 = RInt (f h) a b0 - RInt f0 a b0).
      { apply RInt_minus_val.
        - apply (ex_RInt_continuous (f h) a b0); intros z Hz; apply Hfcont.
        - apply (ex_RInt_continuous f0 a b0); intros z Hz; apply Hf0cont. }
      rewrite <- Hmv.
      apply Rle_trans with (RInt (fun u : R => Rabs (f h u - f0 u)) a b0).
      - apply RInt_abs_val; [lra |].
        intros z Hz.
        apply (continuous_plus (f h) (fun u : R => - f0 u) z).
        + apply Hfcont.
        + apply (continuous_opp f0 z); apply Hf0cont.
      - apply RInt_le; [lra | | | intros x Hx; apply Hfe].
        + apply (ex_RInt_continuous (fun u : R => Rabs (f h u - f0 u)) a b0).
          intros z Hz.
          apply (continuous_comp (fun u : R => f h u - f0 u) Rabs z).
          * apply (continuous_plus (f h) (fun u : R => - f0 u) z).
            -- apply Hfcont.
            -- apply (continuous_opp f0 z); apply Hf0cont.
          * apply continuous_Rabs.
        + apply (ex_RInt_continuous (fun u : R => e h u) a b0).
          intros z Hz; apply Hecont. }
    assert (Hmid_mono : RInt (fun u : R => e h u) a b0 <= RInt (fun u : R => e h u) 0 b0).
    { assert (Hch : RInt (fun u : R => e h u) 0 a + RInt (fun u : R => e h u) a b0 =
                   RInt (fun u : R => e h u) 0 b0).
      { apply (RInt_Chasles (fun u : R => e h u) 0 a b0).
        - apply (ex_RInt_continuous (fun u : R => e h u) 0 a).
          intros z Hz; apply Hecont.
        - apply (ex_RInt_continuous (fun u : R => e h u) a b0).
          intros z Hz; apply Hecont. }
      rewrite <- Hch.
      assert (Hpos_a : 0 <= RInt (fun u : R => e h u) 0 a) by (apply HeRInt_pos; lra).
      lra. }
    (* 三段（a→b0 拆开） *)
    assert (Hmid_bound : Rabs (RInt (f h) a b - RInt f0 a b) <=
            RInt (fun u : R => e h u) 0 b0 +
            Rabs (RInt (f h) b0 b) + Rabs (RInt f0 b0 b)).
    { assert (Hch1 : RInt (f h) a b0 + RInt (f h) b0 b = RInt (f h) a b).
      { apply (RInt_Chasles (f h) a b0 b).
        - apply (ex_RInt_continuous (f h) a b0); intros z Hz; apply Hfcont.
        - apply (ex_RInt_continuous (f h) b0 b); intros z Hz; apply Hfcont. }
      assert (Hch2 : RInt f0 a b0 + RInt f0 b0 b = RInt f0 a b).
      { apply (RInt_Chasles f0 a b0 b).
        - apply (ex_RInt_continuous f0 a b0); intros z Hz; apply Hf0cont.
        - apply (ex_RInt_continuous f0 b0 b); intros z Hz; apply Hf0cont. }
      assert (Heq : RInt (f h) a b - RInt f0 a b =
                    (RInt (f h) a b0 - RInt f0 a b0) + (RInt (f h) b0 b - RInt f0 b0 b)).
      { lra. }
      rewrite Heq.
      apply Rle_trans with (Rabs (RInt (f h) a b0 - RInt f0 a b0) +
                            Rabs (RInt (f h) b0 b - RInt f0 b0 b)).
      - apply Rabs_triang.
      - assert (Hp1 : Rabs (RInt (f h) a b0 - RInt f0 a b0) <= RInt (fun u : R => e h u) 0 b0).
        { apply Rle_trans with (RInt (fun u : R => e h u) a b0).
          - exact Hmid.
          - exact Hmid_mono. }
        assert (Hp2 : Rabs (RInt (f h) b0 b - RInt f0 b0 b) <=
                      Rabs (RInt (f h) b0 b) + Rabs (RInt f0 b0 b)).
        { replace (RInt (f h) b0 b - RInt f0 b0 b) with (RInt (f h) b0 b + (- RInt f0 b0 b)) by ring.
          apply Rle_trans with (Rabs (RInt (f h) b0 b) + Rabs (- RInt f0 b0 b)).
          - apply Rabs_triang.
          - apply Rplus_le_compat_l.
            rewrite Rabs_Ropp.
            apply Rle_refl. }
        lra. }
    (* 主装配 *)
    assert (Hmain : Rabs (lh - l0) < eps).
    { apply Rle_lt_trans with
        (Rabs (lh - RInt (f h) a b) + Rabs (RInt (f h) a b - RInt f0 a b) +
         Rabs (RInt f0 a b - l0)).
      - assert (Htri1 : Rabs (lh - RInt f0 a b) <=
                        Rabs (lh - RInt (f h) a b) + Rabs (RInt (f h) a b - RInt f0 a b)).
        { replace (lh - RInt f0 a b) with ((lh - RInt (f h) a b) + (RInt (f h) a b - RInt f0 a b)) by ring.
          apply Rabs_triang. }
        replace (lh - l0) with ((lh - RInt f0 a b) + (RInt f0 a b - l0)) by ring.
        apply Rle_trans with (Rabs (lh - RInt f0 a b) + Rabs (RInt f0 a b - l0)).
        + apply Rabs_triang.
        + apply Rplus_le_compat.
          * exact Htri1.
          * apply Rle_refl.
      - assert (Hbd3 : Rabs (lh - RInt (f h) a b) < eps / 7).
        { rewrite Rabs_minus_sym. exact Hpair1. }
        assert (Hbd4 : Rabs (RInt f0 a b - l0) < eps / 7) by exact Hpair2.
        assert (Hbd2 : Rabs (RInt (f h) a b - RInt f0 a b) < 3 * (eps / 7)).
        { apply Rle_lt_trans with
            (RInt (fun u : R => e h u) 0 b0 + Rabs (RInt (f h) b0 b) + Rabs (RInt f0 b0 b)).
          - exact Hmid_bound.
          - assert (Ht1 : Rabs (RInt (f h) b0 b) < eps / 7)
              by (apply Rle_lt_trans with (RInt g b0 b); [exact Htail1 | exact Htail1']).
            assert (Ht2 : Rabs (RInt f0 b0 b) < eps / 7)
              by (apply Rle_lt_trans with (RInt g b0 b); [exact Htail2 | exact Htail1']).
            lra. }
        lra. }
    rewrite Hlheq.
    apply Hball.
    unfold ball, AbsRing_ball; simpl.
    exact Hmain.
  - exact Heneigh.
Qed.
(* ============================================================
   第 12 轮（第四部分，块 3）：核函数积分对参数的导数
     Aint_derive    ：A′(γ) = C(γ)      （DCT，控制收敛）
     B0int_derive   ：B₀′(γ) = −A(γ)    （DCT）
     Bint_derive    ：B′(γ) = −2A(γ)
     Fcos_derive    ：F′(γ) = −G(γ)     （由 γF = 2A 与 A′ = C）
     Gsin_derive    ：G′(γ) = −F(γ)     （由 γG = B − F 与 B′ = −2A）
     Fcos_derive_derive ：F″(γ) = F(γ)
   ============================================================ *)

(* |b·c/d| ≤ b/d （0 ≤ b，0 < d，|c| ≤ 1） *)
Lemma Rabs_prod_le_quot : forall (b c d : R), 0 <= b -> 0 < d -> Rabs c <= 1 ->
  Rabs (b * c / d) <= b / d.
Proof.
  intros b c d Hb Hd Hc.
  unfold Rdiv.
  rewrite Rabs_mult.
  rewrite Rabs_mult.
  rewrite (Rabs_pos_eq b Hb).
  rewrite (Rabs_pos_eq (/ d) (Rlt_le _ _ (Rinv_0_lt_compat d Hd))).
  assert (Hinv : 0 <= / d) by (apply Rlt_le; apply Rinv_0_lt_compat; exact Hd).
  apply Rmult_le_compat_r.
  - exact Hinv.
  - assert (Hm : b * Rabs c <= b * 1) by (apply Rmult_le_compat_l; [exact Hb | exact Hc]).
    replace (b * 1) with b in Hm by ring.
    exact Hm.
Qed.

(* |a/d| ≤ b/d （0 < d，|a| ≤ b） *)
Lemma Rabs_div_le : forall (a b d : R), 0 < d -> Rabs a <= b ->
  Rabs (a / d) <= b / d.
Proof.
  intros a b d Hd Hab.
  unfold Rdiv.
  rewrite Rabs_mult.
  rewrite (Rabs_pos_eq (/ d) (Rlt_le _ _ (Rinv_0_lt_compat d Hd))).
  assert (Hinv : 0 <= / d) by (apply Rlt_le; apply Rinv_0_lt_compat; exact Hd).
  apply Rmult_le_compat_r.
  - exact Hinv.
  - exact Hab.
Qed.

(* |u·(sin a − sin b)| ≤ |h|·u²   （|sin| 1-Lipschitz） *)
Lemma Rabs_u_sin_sub_h : forall (u gamma h : R),
  Rabs (u * sin ((gamma + h) * u) - u * sin (gamma * u)) <= Rabs h * (u * u).
Proof.
  intros u gamma h.
  replace (u * sin ((gamma + h) * u) - u * sin (gamma * u))
    with (u * (sin ((gamma + h) * u) - sin (gamma * u))) by ring.
  rewrite Rabs_mult.
  assert (Hl : Rabs (sin ((gamma + h) * u) - sin (gamma * u)) <= Rabs ((gamma + h) * u - gamma * u)).
  { apply Rabs_sin_sub_le. }
  replace ((gamma + h) * u - gamma * u) with (h * u) in Hl by ring.
  assert (Habs_comm : Rabs (h * u) = Rabs h * Rabs u) by apply Rabs_mult.
  assert (Huu : Rabs u * Rabs u = u * u).
  { rewrite <- Rabs_mult.
    rewrite Rabs_pos_eq; [reflexivity | apply Rle_0_sqr]. }
  assert (Habs_u : 0 <= Rabs u) by apply Rabs_pos.
  assert (Habs_s : 0 <= Rabs (sin ((gamma + h) * u) - sin (gamma * u))) by apply Rabs_pos.
  rewrite Habs_comm in Hl.
  apply Rle_trans with (Rabs u * (Rabs h * Rabs u)).
  - apply Rmult_le_compat_l; [exact Habs_u | exact Hl].
  - replace (Rabs u * (Rabs h * Rabs u)) with (Rabs h * (Rabs u * Rabs u)) by ring.
    rewrite Huu.
    apply Rle_refl.
Qed.

(* |u·(sin a − sin b − h·u·cos b)| ≤ h²·|u³|  （sin Taylor 一阶余项） *)
Lemma Rabs_u_sin_lin_h : forall (u gamma h : R),
  Rabs (u * sin ((gamma + h) * u) - u * sin (gamma * u) -
        h * (u * u) * cos (gamma * u)) <= h * h * Rabs (u * u * u).
Proof.
  intros u gamma h.
  replace (u * sin ((gamma + h) * u) - u * sin (gamma * u) -
           h * (u * u) * cos (gamma * u))
    with (u * (sin ((gamma + h) * u) - sin (gamma * u) - h * u * cos (gamma * u))) by ring.
  rewrite Rabs_mult.
  assert (Hl : Rabs (sin (gamma * u + ((gamma + h) * u - gamma * u)) - sin (gamma * u) -
                     ((gamma + h) * u - gamma * u) * cos (gamma * u))
               <= ((gamma + h) * u - gamma * u) * ((gamma + h) * u - gamma * u)).
  { apply Rabs_sin_lin. }
  replace (gamma * u + ((gamma + h) * u - gamma * u)) with ((gamma + h) * u) in Hl by ring.
  replace ((gamma + h) * u - gamma * u) with (h * u) in Hl by ring.
  assert (Habs3 : Rabs (u * u * u) = Rabs u * (u * u)).
  { replace (u * u * u) with (u * (u * u)) by ring.
    rewrite Rabs_mult.
    rewrite Rabs_mult.
    rewrite <- Rabs_mult.
    rewrite (Rabs_pos_eq (u * u) (Rle_0_sqr u)).
    reflexivity. }
  assert (Habs_u : 0 <= Rabs u) by apply Rabs_pos.
  assert (Hsq : 0 <= u * u) by apply Rle_0_sqr.
  apply Rle_trans with (Rabs u * ((h * u) * (h * u))).
  - apply Rmult_le_compat_l; [exact Habs_u | exact Hl].
  - replace (Rabs u * ((h * u) * (h * u))) with (h * h * (Rabs u * (u * u))) by ring.
    rewrite <- Habs3.
    apply Rle_refl.
Qed.

(* |cos a − cos b + h·u·sin b| ≤ h²·u²  （cos Taylor 一阶余项） *)
Lemma Rabs_cos_lin_h : forall (u gamma h : R),
  Rabs (cos ((gamma + h) * u) - cos (gamma * u) + h * u * sin (gamma * u)) <= h * h * (u * u).
Proof.
  intros u gamma h.
  assert (Hl : Rabs (cos (gamma * u + ((gamma + h) * u - gamma * u)) - cos (gamma * u) +
                     ((gamma + h) * u - gamma * u) * sin (gamma * u))
               <= ((gamma + h) * u - gamma * u) * ((gamma + h) * u - gamma * u)).
  { apply Rabs_cos_lin. }
  replace (gamma * u + ((gamma + h) * u - gamma * u)) with ((gamma + h) * u) in Hl by ring.
  replace ((gamma + h) * u - gamma * u) with (h * u) in Hl by ring.
  replace ((h * u) * (h * u)) with (h * h * (u * u)) in Hl by ring.
  exact Hl.
Qed.

(* RInt (fun u => |h|·E u) 0 M → 0 as h → 0 *)
Lemma filterlim_RInt_abs_scal : forall (E : R -> R) (M : R),
  0 <= M ->
  (forall u : R, continuous E u) ->
  filterlim (fun h : R => RInt (fun u : R => Rabs h * E u) 0 M) (locally 0) (locally 0).
Proof.
  intros E M HM Hcont.
  unfold filterlim.
  intros P HP.
  destruct (locally_iff_open_ball 0 P) as [Hiff _].
  destruct (Hiff HP) as [eps [Heps_pos Hball]].
  assert (Hval : forall h : R, RInt (fun u : R => Rabs h * E u) 0 M = Rabs h * RInt E 0 M).
  { intro h.
    destruct (ex_RInt_continuous E 0 M) as [l Hl].
    - intros z Hz; apply Hcont.
    - assert (Hs : is_RInt (fun u : R => Rabs h * E u) 0 M (scal (Rabs h) l)).
      { apply (is_RInt_scal E 0 M (Rabs h) l); exact Hl. }
      assert (Hv : RInt (fun u : R => Rabs h * E u) 0 M = scal (Rabs h) l)
        by (apply is_RInt_unique; exact Hs).
      assert (Hl_eq : RInt E 0 M = l) by (apply is_RInt_unique; exact Hl).
      rewrite Hv, Hl_eq.
      change ((Rabs h) * l = Rabs h * l). reflexivity. }
  set (K := Rabs (RInt E 0 M) + 1).
  assert (HK_pos : 0 < K) by (unfold K; assert (Hr : 0 <= Rabs (RInt E 0 M)) by apply Rabs_pos; lra).
  assert (HepsK : 0 < eps / K) by (apply Rdiv_lt_0_compat; [exact Heps_pos | exact HK_pos]).
  exists (mkposreal (eps / K) HepsK).
  intros h Hh.
  unfold ball, AbsRing_ball in Hh; simpl in Hh.
  change (Rabs (h - 0) < eps / K) in Hh.
  rewrite Rminus_0_r in Hh.
  rewrite Hval.
  apply Hball.
  unfold ball, AbsRing_ball; simpl.
  change (Rabs (Rabs h * RInt E 0 M - 0) < eps).
  rewrite Rminus_0_r.
  rewrite Rabs_mult.
  rewrite (Rabs_pos_eq (Rabs h) (Rabs_pos h)).
  apply Rle_lt_trans with (Rabs h * (Rabs (RInt E 0 M) + 1)).
  - apply Rmult_le_compat_l.
    + apply Rabs_pos.
    + lra.
  - replace (Rabs (RInt E 0 M) + 1) with K by (unfold K; ring).
    apply Rlt_le_trans with ((eps / K) * K).
    + apply Rmult_lt_compat_r.
      * exact HK_pos.
      * exact Hh.
    + replace ((eps / K) * K) with eps by (unfold Rdiv; field; apply Rgt_not_eq; exact HK_pos).
      apply Rle_refl.
Qed.

(* 商一致（h ≠ 0）⇒ 可导：由商极限给出 is_derive *)
Lemma is_derive_from_quotient : forall (f : R -> R) (x l : R),
  (forall eps : R, 0 < eps ->
     locally 0 (fun h : R => h <> 0 -> Rabs (/ h * (f (x + h) - f x) - l) < eps)) ->
  is_derive f x l.
Proof.
  intros f x l Hq.
  unfold is_derive, filterdiff.
  split.
  - (* is_linear (fun y : R => scal y l) *)
    apply Build_is_linear.
    + intros y1 y2.
      change (scal (plus y1 y2) l = plus (scal y1 l) (scal y2 l)).
      rewrite Rmult_plus_distr_r.
      reflexivity.
    + intros k y.
      change (scal (scal k y) l = scal k (scal y l)).
      rewrite Rmult_assoc.
      reflexivity.
    + exists (Rabs l + 1).
      split.
      - assert (HR : 0 <= Rabs l) by apply Rabs_pos; lra.
      - intros y.
        change (Rabs (y * l) <= (Rabs l + 1) * Rabs y).
        rewrite Rabs_mult.
        rewrite Rmult_comm.
        apply Rmult_le_compat_r; [apply Rabs_pos | lra].
  - intros x0 Hfl.
    assert (Hx0 : x0 = x).
    {
      destruct (Req_dec x0 x) as [Heq | Hne]; [exact Heq | exfalso].
      pose (P := fun z : R => Rabs (z - x0) < Rabs (x - x0) / 2).
      assert (Hloc0 : locally x0 P).
      { unfold locally, P.
        assert (Habs_gt0 : 0 < Rabs (x - x0)) by (apply Rabs_pos_lt; lra).
        assert (Hhalf : 0 < Rabs (x - x0) / 2) by lra.
        exists (mkposreal (Rabs (x - x0) / 2) Hhalf).
        intros y Hy.
        unfold ball, AbsRing_ball in Hy; simpl in Hy.
        exact Hy. }
      assert (Hlocx : locally x P) by (apply Hfl; exact Hloc0).
      destruct Hlocx as [d Hd].
      assert (HPx : P x).
      { apply Hd. apply ball_center. }
      unfold P in HPx.
      rewrite Rabs_minus_sym in HPx.
      assert (HR : 0 <= Rabs (x0 - x)) by apply Rabs_pos.
      lra.
    }
    subst x0.
    intros eps.
    destruct (Hq (pos eps) (cond_pos eps)) as [d Hd].
    exists d.
    intros y Hy.
    change (Rabs (f y - f x - (y - x) * l) <= pos eps * Rabs (y - x)).
    destruct (Req_dec y x) as [Hyx | Hyx].
    + subst y.
      replace (f x - f x - (x - x) * l) with 0 by ring.
      replace (x - x) with 0 by ring.
      rewrite Rabs_R0, Rmult_0_r.
      lra.
    + assert (Hh0 : y - x <> 0) by lra.
      change (Rabs (y - x) < pos d) in Hy.
      assert (Hball0 : ball 0 d (y - x)).
      { unfold ball, AbsRing_ball; simpl.
        change (Rabs ((y - x) - 0) < pos d).
        rewrite Rminus_0_r.
        exact Hy. }
      assert (Hy_eq : x + (y - x) = y) by (unfold plus, minus, opp; simpl; ring).
      assert (Hbd_raw : Rabs (/ (y - x) * (f (x + (y - x)) - f x) - l) < pos eps)
        by (apply Hd; [exact Hball0 | exact Hh0]).
      assert (Hbd : Rabs (/ (y - x) * (f y - f x) - l) < pos eps).
      { rewrite Hy_eq in Hbd_raw. exact Hbd_raw. }
      replace (f y - f x - (y - x) * l)
        with ((y - x) * (/ (y - x) * (f y - f x) - l)).
      * change (Rabs (Rmult (Rminus y x) (/ (Rminus y x) * (f y - f x) - l)) <=
                Rmult (pos eps) (Rabs (Rminus y x))).
        rewrite (Rabs_mult (Rminus y x) (/ (Rminus y x) * (f y - f x) - l)).
        rewrite Rmult_comm.
        apply (Rmult_le_compat_r (Rabs (Rminus y x))
                                (Rabs (/ (Rminus y x) * (f y - f x) - l)) (pos eps)).
        - apply Rabs_pos.
        - apply Rlt_le. exact Hbd.
      * field. exact Hh0.
Qed.


Definition PFa : ProperFilter' (at_right 0) :=
  @Proper_StrongProper R (at_right 0) (at_right_proper_filter 0).
Definition PFb : ProperFilter' (Rbar_locally p_infty) :=
  @Proper_StrongProper R (Rbar_locally p_infty) (Rbar_locally_filter p_infty).
Definition PFa_pf : ProperFilter (at_right 0) := at_right_proper_filter 0.
Definition PFb_pf : ProperFilter (Rbar_locally p_infty) := Rbar_locally_filter p_infty.
Definition FFa : Filter (at_right 0) := @filter_filter R (at_right 0) PFa_pf.
Definition FFb : Filter (Rbar_locally p_infty) := @filter_filter R (Rbar_locally p_infty) PFb_pf.

(* 包装：RInt_gen 外延（ProperFilter 版） *)
Lemma RInt_gen_ext_pf : forall (f g : R -> R) (Fa Fb : (R -> Prop) -> Prop),
  ProperFilter Fa -> ProperFilter Fb ->
  (forall x : R, f x = g x) -> ex_RInt_gen f Fa Fb ->
  RInt_gen f Fa Fb = RInt_gen g Fa Fb.
Proof.
  intros f g Fa Fb HFa HFb Heq Hex.
  apply (@RInt_gen_ext_eq R_CompleteNormedModule Fa Fb HFa HFb f g Heq Hex).
Qed.

Lemma ex_RInt_gen_ext_pf : forall (f g : R -> R) (Fa Fb : (R -> Prop) -> Prop),
  ProperFilter Fa -> ProperFilter Fb ->
  (forall x : R, f x = g x) -> ex_RInt_gen f Fa Fb ->
  ex_RInt_gen g Fa Fb.
Proof.
  intros f g Fa Fb HFa HFb Heq Hex.
  apply (@ex_RInt_gen_ext_eq R_NormedModule Fa Fb
          (@filter_filter R Fa HFa) (@filter_filter R Fb HFb) f g Heq Hex).
Qed.

(* 辅助：广义积分数乘与加法（ProperFilter' 版，用于 RInt_gen_correct/unique） *)
Lemma RInt_gen_scal_l : forall (f : R -> R) (k : R) (Fa Fb : (R -> Prop) -> Prop),
  ProperFilter' Fa -> ProperFilter' Fb ->
  ex_RInt_gen f Fa Fb ->
  RInt_gen (fun t => k * f t) Fa Fb = k * RInt_gen f Fa Fb.
Proof.
  intros f k Fa Fb HFa HFb Hex.
  pose proof (@RInt_gen_correct R_CompleteNormedModule Fa Fb HFa HFb f Hex) as Hf.
  pose proof (@is_RInt_gen_scal R_NormedModule Fa Fb
                              (@filter_filter' R Fa HFa) (@filter_filter' R Fb HFb)
                              f k (RInt_gen f Fa Fb) Hf) as Hk.
  eapply (@is_RInt_gen_unique R_CompleteNormedModule Fa Fb); [exact HFa | exact HFb | exact Hk].
Qed.

Lemma RInt_gen_plus_l : forall (f g : R -> R) (Fa Fb : (R -> Prop) -> Prop),
  ProperFilter' Fa -> ProperFilter' Fb ->
  ex_RInt_gen f Fa Fb -> ex_RInt_gen g Fa Fb ->
  RInt_gen (fun t => f t + g t) Fa Fb = RInt_gen f Fa Fb + RInt_gen g Fa Fb.
Proof.
  intros f g Fa Fb HFa HFb Hexf Hexg.
  pose proof (@RInt_gen_correct R_CompleteNormedModule Fa Fb HFa HFb f Hexf) as Hf.
  pose proof (@RInt_gen_correct R_CompleteNormedModule Fa Fb HFa HFb g Hexg) as Hg.
  pose proof (@is_RInt_gen_plus R_NormedModule Fa Fb
                              (@filter_filter' R Fa HFa) (@filter_filter' R Fb HFb)
                              f g (RInt_gen f Fa Fb) (RInt_gen g Fa Fb) Hf Hg) as Hp.
  eapply (@is_RInt_gen_unique R_CompleteNormedModule Fa Fb); [exact HFa | exact HFb | exact Hp].
Qed.

Lemma ex_RInt_gen_plus_l : forall (f g : R -> R) (Fa Fb : (R -> Prop) -> Prop),
  ProperFilter' Fa -> ProperFilter' Fb ->
  ex_RInt_gen f Fa Fb -> ex_RInt_gen g Fa Fb ->
  ex_RInt_gen (fun t => f t + g t) Fa Fb.
Proof.
  intros f g Fa Fb HFa HFb Hexf Hexg.
  pose proof (@RInt_gen_correct R_CompleteNormedModule Fa Fb HFa HFb f Hexf) as Hf.
  pose proof (@RInt_gen_correct R_CompleteNormedModule Fa Fb HFa HFb g Hexg) as Hg.
  pose proof (@is_RInt_gen_plus R_NormedModule Fa Fb
                              (@filter_filter' R Fa HFa) (@filter_filter' R Fb HFb)
                              f g (RInt_gen f Fa Fb) (RInt_gen g Fa Fb) Hf Hg) as Hp.
  exists (RInt_gen f Fa Fb + RInt_gen g Fa Fb).
  exact Hp.
Qed.

Lemma ex_RInt_gen_scal_l : forall (f : R -> R) (k : R) (Fa Fb : (R -> Prop) -> Prop),
  ProperFilter' Fa -> ProperFilter' Fb ->
  ex_RInt_gen f Fa Fb ->
  ex_RInt_gen (fun t => k * f t) Fa Fb.
Proof.
  intros f k Fa Fb HFa HFb Hex.
  pose proof (@RInt_gen_correct R_CompleteNormedModule Fa Fb HFa HFb f Hex) as Hf.
  pose proof (@is_RInt_gen_scal R_NormedModule Fa Fb
                              (@filter_filter' R Fa HFa) (@filter_filter' R Fb HFb)
                              f k (RInt_gen f Fa Fb) Hf) as Hk.
  exists (k * RInt_gen f Fa Fb).
  exact Hk.
Qed.

Lemma RInt_gen_lin_l : forall (f g : R -> R) (a b : R) (Fa Fb : (R -> Prop) -> Prop),
  ProperFilter' Fa -> ProperFilter' Fb ->
  ex_RInt_gen f Fa Fb -> ex_RInt_gen g Fa Fb ->
  RInt_gen (fun t => a * f t + b * g t) Fa Fb =
    a * RInt_gen f Fa Fb + b * RInt_gen g Fa Fb.
Proof.
  intros f g a b Fa Fb HFa HFb Hexf Hexg.
  rewrite RInt_gen_plus_l; [| exact HFa | exact HFb | | ].
  - rewrite (RInt_gen_scal_l f a Fa Fb); [| exact HFa | exact HFb | exact Hexf ].
    rewrite (RInt_gen_scal_l g b Fa Fb); [| exact HFa | exact HFb | exact Hexg ].
    reflexivity.
  - eapply ex_RInt_gen_scal_l; [exact HFa | exact HFb | exact Hexf ].
  - eapply ex_RInt_gen_scal_l; [exact HFa | exact HFb | exact Hexg ].
Qed.

Lemma ex_RInt_gen_lin_l : forall (f g : R -> R) (a b : R) (Fa Fb : (R -> Prop) -> Prop),
  ProperFilter' Fa -> ProperFilter' Fb ->
  ex_RInt_gen f Fa Fb -> ex_RInt_gen g Fa Fb ->
  ex_RInt_gen (fun t => a * f t + b * g t) Fa Fb.
Proof.
  intros f g a b Fa Fb HFa HFb Hexf Hexg.
  eapply ex_RInt_gen_plus_l; [exact HFa | exact HFb | | ].
  - eapply ex_RInt_gen_scal_l; [exact HFa | exact HFb | exact Hexf ].
  - eapply ex_RInt_gen_scal_l; [exact HFa | exact HFb | exact Hexg ].
Qed.

(* FT 线性性：F(a·f + b·g)(ξ) = a·F(f)(ξ) + b·F(g)(ξ)（在积分存在条件下） *)
Lemma FourierTransform_linear (f g : R -> R) (a b xi : R)
  (Hfcos : ex_RInt_gen (fun t => f t * cos (2 * PI * xi * t)) (at_right 0) (Rbar_locally p_infty))
  (Hfsin : ex_RInt_gen (fun t => f t * sin (2 * PI * xi * t)) (at_right 0) (Rbar_locally p_infty))
  (Hgcos : ex_RInt_gen (fun t => g t * cos (2 * PI * xi * t)) (at_right 0) (Rbar_locally p_infty))
  (Hgsin : ex_RInt_gen (fun t => g t * sin (2 * PI * xi * t)) (at_right 0) (Rbar_locally p_infty)) :
  FourierTransform (fun t => a * f t + b * g t) xi =
    (a +i 0) *c FourierTransform f xi +c (b +i 0) *c FourierTransform g xi.
Proof.
  Check cos_neg.
  Check sin_neg.
  unfold FourierTransform.
  apply Complex_eq; simpl.
  - (* re *)
    assert (Hre_ext :
      RInt_gen (fun t => (a * f t + b * g t) * cos (2 * PI * xi * t))
               (at_right 0) (Rbar_locally p_infty) =
      RInt_gen (fun t => a * (f t * cos (2 * PI * xi * t)) + b * (g t * cos (2 * PI * xi * t)))
               (at_right 0) (Rbar_locally p_infty)).
    { eapply RInt_gen_ext_pf.
      - exact PFa_pf.
      - exact PFb_pf.
      - intros t; ring.
      - eapply (ex_RInt_gen_ext_pf (fun t => a * (f t * cos (2 * PI * xi * t)) + b * (g t * cos (2 * PI * xi * t)))).
        + exact PFa_pf.
        + exact PFb_pf.
        + intros t; ring.
        + apply (ex_RInt_gen_lin_l (fun t => f t * cos (2 * PI * xi * t)) (fun t => g t * cos (2 * PI * xi * t)) a b (at_right 0) (Rbar_locally p_infty)); [exact PFa | exact PFb | exact Hfcos | exact Hgcos ]. }
    assert (Hre_lin :
      RInt_gen (fun t => a * (f t * cos (2 * PI * xi * t)) + b * (g t * cos (2 * PI * xi * t)))
               (at_right 0) (Rbar_locally p_infty) =
      a * RInt_gen (fun t => f t * cos (2 * PI * xi * t)) (at_right 0) (Rbar_locally p_infty) +
      b * RInt_gen (fun t => g t * cos (2 * PI * xi * t)) (at_right 0) (Rbar_locally p_infty)).
    { eapply RInt_gen_lin_l; [exact PFa | exact PFb | exact Hfcos | exact Hgcos ]. }
    rewrite Hre_ext, Hre_lin.
    unfold plus, minus, opp, scal.
    simpl.
    ring.
  - (* im *)
    assert (Him_ext :
      RInt_gen (fun t => (a * f t + b * g t) * sin (2 * PI * xi * t))
               (at_right 0) (Rbar_locally p_infty) =
      RInt_gen (fun t => a * (f t * sin (2 * PI * xi * t)) + b * (g t * sin (2 * PI * xi * t)))
               (at_right 0) (Rbar_locally p_infty)).
    { eapply RInt_gen_ext_pf.
      - exact PFa_pf.
      - exact PFb_pf.
      - intros t; ring.
      - eapply (ex_RInt_gen_ext_pf (fun t => a * (f t * sin (2 * PI * xi * t)) + b * (g t * sin (2 * PI * xi * t)))).
        + exact PFa_pf.
        + exact PFb_pf.
        + intros t; ring.
        + apply (ex_RInt_gen_lin_l (fun t => f t * sin (2 * PI * xi * t)) (fun t => g t * sin (2 * PI * xi * t)) a b (at_right 0) (Rbar_locally p_infty)); [exact PFa | exact PFb | exact Hfsin | exact Hgsin ]. }
    assert (Him_lin :
      RInt_gen (fun t => a * (f t * sin (2 * PI * xi * t)) + b * (g t * sin (2 * PI * xi * t)))
               (at_right 0) (Rbar_locally p_infty) =
      a * RInt_gen (fun t => f t * sin (2 * PI * xi * t)) (at_right 0) (Rbar_locally p_infty) +
      b * RInt_gen (fun t => g t * sin (2 * PI * xi * t)) (at_right 0) (Rbar_locally p_infty)).
    { eapply RInt_gen_lin_l; [exact PFa | exact PFb | exact Hfsin | exact Hgsin ]. }
    rewrite Him_ext, Him_lin.
    unfold plus, minus, opp, scal.
    simpl.
    ring.
Qed.

(* FT 共轭对称：F(f)(−ξ) = conj(F(f)(ξ))（f 为实值；需积分存在） *)
Lemma FourierTransform_conj_sym (f : R -> R) (xi : R)
  (Hfcos : ex_RInt_gen (fun t => f t * cos (2 * PI * xi * t)) (at_right 0) (Rbar_locally p_infty))
  (Hfsin : ex_RInt_gen (fun t => f t * sin (2 * PI * xi * t)) (at_right 0) (Rbar_locally p_infty))
  (Hfcos_neg : ex_RInt_gen (fun t => f t * cos (2 * PI * (- xi) * t)) (at_right 0) (Rbar_locally p_infty))
  (Hfsin_neg : ex_RInt_gen (fun t => f t * sin (2 * PI * (- xi) * t)) (at_right 0) (Rbar_locally p_infty)) :
  FourierTransform f (- xi) = ComplexNumbers.Cconj (FourierTransform f xi).
Proof.
  unfold FourierTransform.
  apply Complex_eq; simpl.
  - (* re: cos 偶性 → ∫ f cos(2π(−ξ)t) = ∫ f cos(2πξt) *)
    rewrite (RInt_gen_ext_pf (fun t => f t * cos (2 * PI * (- xi) * t))
                             (fun t => f t * cos (2 * PI * xi * t))
                             (at_right 0) (Rbar_locally p_infty)
                             PFa_pf PFb_pf
                             (fun t => ltac:(simpl; assert (Ht : 2 * PI * (- xi) * t = - (2 * PI * xi * t)) by ring;
                                             rewrite Ht; rewrite cos_neg; reflexivity))
                             Hfcos_neg).
    reflexivity.
  - (* im: sin 奇性 → opp(∫f sin(2π(−ξ)t)) = ∫f sin(2πξt) *)
    assert (Hsin_odd :
      RInt_gen (fun t => f t * sin (2 * PI * (- xi) * t)) (at_right 0) (Rbar_locally p_infty) =
      (-1) * RInt_gen (fun t => f t * sin (2 * PI * xi * t)) (at_right 0) (Rbar_locally p_infty)).
    { rewrite (RInt_gen_ext_pf (fun t => f t * sin (2 * PI * (- xi) * t))
                             (fun t => (-1) * (f t * sin (2 * PI * xi * t)))
                             (at_right 0) (Rbar_locally p_infty)
                             PFa_pf PFb_pf
                             (fun t => ltac:(simpl;
                                             assert (Ht : 2 * PI * (- xi) * t = - (2 * PI * xi * t)) by ring;
                                             rewrite Ht; rewrite sin_neg; ring))
                             Hfsin_neg).
      rewrite (RInt_gen_scal_l (fun t => f t * sin (2 * PI * xi * t)) (-1)
                        (at_right 0) (Rbar_locally p_infty) PFa PFb Hfsin).
      unfold plus, minus, opp, scal.
      simpl.
      ring. }
    unfold minus, plus, opp, scal.
    simpl.
    rewrite Hsin_odd.
    ring.
Qed.

Lemma RInt_gen_minus_l : forall (f g : R -> R) (Fa Fb : (R -> Prop) -> Prop),
  ProperFilter' Fa -> ProperFilter' Fb ->
  ex_RInt_gen f Fa Fb -> ex_RInt_gen g Fa Fb ->
  RInt_gen (fun t => f t - g t) Fa Fb = RInt_gen f Fa Fb - RInt_gen g Fa Fb.
Proof.
  intros f g Fa Fb HFa HFb Hexf Hexg.
  pose proof (RInt_gen_lin_l f g 1 (-1) Fa Fb HFa HFb Hexf Hexg) as Hl.
  change (RInt_gen (fun t => 1 * f t + (-1) * g t) Fa Fb =
          1 * RInt_gen f Fa Fb + (-1) * RInt_gen g Fa Fb) in Hl.
  replace (fun t => 1 * f t + (-1) * g t) with (fun t => f t - g t) in Hl by
    (apply functional_extensionality; intro t; ring).
  replace (1 * RInt_gen f Fa Fb + (-1) * RInt_gen g Fa Fb)
    with (RInt_gen f Fa Fb - RInt_gen g Fa Fb) in Hl by ring.
  exact Hl.
Qed.

(* A 核差商的被积函数（h=0 延拓为导核） *)
Definition A_diff (gamma u h : R) : R :=
  if Req_EM_T h 0 then ku2cos_sq gamma u
  else (kusin_sq (gamma + h) u - kusin_sq gamma u) / h.

(* u ↦ A_diff gamma u h 连续（对固定 h） *)
Lemma cont_A_diff : forall (gamma u h : R), continuous (fun v => A_diff gamma v h) u.
Proof.
  intros gamma u h.
  unfold A_diff.
  destruct (Req_EM_T h 0) as [Hh0 | Hhn0].
  - (* h=0 分支：u ↦ ku2cos_sq gamma u 连续 *)
    subst h.
    apply (continuous_ext (fun v => ku2cos_sq gamma v) (fun v => ku2cos_sq gamma v)).
    + intro v; reflexivity.
    + intro v; apply cont_ku2cos_sq.
  - (* h≠0 分支：u ↦ 差商 连续 *)
    assert (Hfun : (fun v => A_diff gamma v h) = (fun v => (kusin_sq (gamma + h) v - kusin_sq gamma v) / h)).
    { apply functional_extensionality.
      intro v.
      unfold A_diff.
      destruct (Req_EM_T h 0) as [Hh0' | Hhn0'].
      - exfalso. exact (Hhn0 Hh0').
      - reflexivity. }
    apply (continuous_mult (fun v => kusin_sq (gamma + h) v - kusin_sq gamma v)
                            (fun _ => / h) u).
    + apply (continuous_minus (fun v => kusin_sq (gamma + h) v) (fun v => kusin_sq gamma v) u).
      * exact (cont_kusin_sq (gamma + h) u).
      * exact (cont_kusin_sq gamma u).
    + apply continuous_const.
Qed.

(* |A_diff γ h u − ku2cos_sq γ u| ≤ |h|·u³/(1+u²)²  (u ≥ 0) *)
Lemma Rabs_A_diff_lin : forall (gamma u h : R), 0 <= u ->
  Rabs (A_diff gamma u h - ku2cos_sq gamma u)
  <= Rabs h * (u * u * u) / ((1 + u * u) * (1 + u * u)).
Proof.
  intros gamma u h Hu.
  unfold A_diff.
  destruct (Req_EM_T h 0) as [Hh0 | Hhn0].
  - (* h = 0：平凡 *)
    subst h.
    rewrite Rminus_diag, Rabs_R0.
    simpl.
    assert (Hnz : (1 + u * u) * (1 + u * u) <> 0).
    { apply Rgt_not_eq.
      assert (Hsq : 0 <= u * u) by apply Rle_0_sqr.
      assert (H1 : 0 < 1 + u * u) by lra.
      apply Rmult_lt_0_compat; exact H1; exact H1. }
    unfold Rdiv.
    rewrite Rmult_0_l.
    lra.
  - (* h ≠ 0 *)
    unfold kusin_sq, ku2cos_sq.
    set (A := u * sin ((gamma + h) * u) - u * sin (gamma * u) - h * (u * u) * cos (gamma * u)).
    set (D := (1 + u * u) * (1 + u * u)).
    assert (Hlin : Rabs A <= h * h * Rabs (u * u * u)).
    { unfold A. apply Rabs_u_sin_lin_h. }
    assert (Hu3 : Rabs (u * u * u) = u * u * u).
    { rewrite Rabs_pos_eq; [reflexivity |
        apply Rmult_le_pos; [apply Rle_0_sqr | exact Hu ] ]. }
    assert (Hh2 : h * h = Rabs h * Rabs h).
    { rewrite <- Rabs_mult. rewrite Rabs_pos_eq; [reflexivity | apply Rle_0_sqr]. }
    assert (HposD : 0 < D).
    { unfold D. apply Rmult_lt_0_compat; [assert (H : 0 <= u * u) by apply Rle_0_sqr; lra |
                                             assert (H : 0 <= u * u) by apply Rle_0_sqr; lra]. }
    assert (HnzD : D <> 0) by (apply Rgt_not_eq; exact HposD).
    assert (Heq1 : (u * sin ((gamma + h) * u) / D - u * sin (gamma * u) / D) / h =
                   (u * sin ((gamma + h) * u) - u * sin (gamma * u)) / (h * D)).
    { field. split; [exact HnzD | exact Hhn0]. }
    assert (Heq2 : (u * sin ((gamma + h) * u) - u * sin (gamma * u)) / (h * D) -
                   (u * u) * cos (gamma * u) / D = A / (h * D)).
    { unfold A. field. split; [exact HnzD | exact Hhn0]. }
    assert (Heq : (u * sin ((gamma + h) * u) / D - u * sin (gamma * u) / D) / h -
                 (u * u) * cos (gamma * u) / D = A / (h * D)).
    { rewrite Heq1. exact Heq2. }
    rewrite Heq.
    assert (Hpos_hD : 0 < Rabs h * D).
    { apply Rmult_lt_0_compat; [apply Rabs_pos_lt; exact Hhn0 | exact HposD]. }
    apply Rle_trans with (Rabs A / (Rabs h * D)).
    - (* Rabs (A/(h·D)) ≤ Rabs A/(|h|·D) *)
      assert (Hnz_hD : h * D <> 0).
      { apply Rmult_integral_contrapositive. split; [exact Hhn0 | exact HnzD]. }
      rewrite (Rabs_div A (h * D) Hnz_hD).
      match goal with |- ?G => idtac G end.
      rewrite Rabs_mult.
      match goal with |- ?G => idtac G end.
      rewrite (Rabs_pos_eq D (Rlt_le _ _ HposD)).
      reflexivity.
    - (* Rabs A/(|h|·D) ≤ |h|·u³/D：两边乘 |h|·D > 0 *)
      apply (Rmult_le_reg_r (Rabs h * D)).
      + exact Hpos_hD.
      + assert (Hl1 : Rabs A / (Rabs h * D) * (Rabs h * D) = Rabs A).
        { field. split; [apply Rgt_not_eq; exact HposD | apply Rabs_no_R0; exact Hhn0]. }
        rewrite Hl1.
        assert (Hr1 : Rabs h * (u * u * u) / D * (Rabs h * D) = Rabs h * (u * u * u) * Rabs h).
        { field. exact HnzD. }
        rewrite Hr1.
        rewrite Hu3 in Hlin.
        (* 目标：Rabs A ≤ Rabs h·u³·Rabs h；用 Hlin 桥接 *)
        apply Rle_trans with (h * h * (u * u * u)).
        * exact Hlin.
        * assert (Heq3 : Rabs h * (u * u * u) * Rabs h = h * h * (u * u * u)).
          { rewrite Hh2. ring. }
          rewrite Heq3.
          apply Rle_refl.
Qed.
Lemma Rabs_A_diff_lin_all : forall (gamma u h : R),
  Rabs (A_diff gamma u h - ku2cos_sq gamma u)
  <= Rabs h * Rabs (u * u * u) / ((1 + u * u) * (1 + u * u)).
Proof.
  intros gamma u h.
  unfold A_diff.
  destruct (Req_EM_T h 0) as [Hh0 | Hhn0].
  - (* h = 0：平凡 *)
    subst h.
    rewrite Rminus_diag, Rabs_R0.
    simpl.
    assert (Hnz : (1 + u * u) * (1 + u * u) <> 0).
    { apply Rgt_not_eq.
      assert (Hsq : 0 <= u * u) by apply Rle_0_sqr.
      assert (H1 : 0 < 1 + u * u) by lra.
      apply Rmult_lt_0_compat; exact H1; exact H1. }
    unfold Rdiv.
    rewrite Rmult_0_l.
    lra.
  - (* h ≠ 0 *)
    unfold kusin_sq, ku2cos_sq.
    set (A := u * sin ((gamma + h) * u) - u * sin (gamma * u) - h * (u * u) * cos (gamma * u)).
    set (D := (1 + u * u) * (1 + u * u)).
    assert (Hlin : Rabs A <= h * h * Rabs (u * u * u)).
    { unfold A. apply Rabs_u_sin_lin_h. }
    assert (Hh2 : h * h = Rabs h * Rabs h).
    { rewrite <- Rabs_mult. rewrite Rabs_pos_eq; [reflexivity | apply Rle_0_sqr]. }
    assert (HposD : 0 < D).
    { unfold D. apply Rmult_lt_0_compat; [assert (H : 0 <= u * u) by apply Rle_0_sqr; lra |
                                             assert (H : 0 <= u * u) by apply Rle_0_sqr; lra]. }
    assert (HnzD : D <> 0) by (apply Rgt_not_eq; exact HposD).
    assert (Heq1 : (u * sin ((gamma + h) * u) / D - u * sin (gamma * u) / D) / h =
                   (u * sin ((gamma + h) * u) - u * sin (gamma * u)) / (h * D)).
    { field. split; [exact HnzD | exact Hhn0]. }
    assert (Heq2 : (u * sin ((gamma + h) * u) - u * sin (gamma * u)) / (h * D) -
                   (u * u) * cos (gamma * u) / D = A / (h * D)).
    { unfold A. field. split; [exact HnzD | exact Hhn0]. }
    assert (Heq : (u * sin ((gamma + h) * u) / D - u * sin (gamma * u) / D) / h -
                 (u * u) * cos (gamma * u) / D = A / (h * D)).
    { rewrite Heq1. exact Heq2. }
    rewrite Heq.
    assert (Hpos_hD : 0 < Rabs h * D).
    { apply Rmult_lt_0_compat; [apply Rabs_pos_lt; exact Hhn0 | exact HposD]. }
    apply Rle_trans with (Rabs A / (Rabs h * D)).
    - (* Rabs (A/(h·D)) ≤ Rabs A/(|h|·D) *)
      assert (Hnz_hD : h * D <> 0).
      { apply Rmult_integral_contrapositive. split; [exact Hhn0 | exact HnzD]. }
      rewrite (Rabs_div A (h * D) Hnz_hD).
      rewrite Rabs_mult.
      rewrite (Rabs_pos_eq D (Rlt_le _ _ HposD)).
      reflexivity.
    - (* Rabs A/(|h|·D) ≤ |h|·|u³|/D：两边乘 |h|·D > 0 *)
      apply (Rmult_le_reg_r (Rabs h * D)).
      + exact Hpos_hD.
      + assert (Hl1 : Rabs A / (Rabs h * D) * (Rabs h * D) = Rabs A).
        { field. split; [apply Rgt_not_eq; exact HposD | apply Rabs_no_R0; exact Hhn0]. }
        rewrite Hl1.
        assert (Hr1 : Rabs h * Rabs (u * u * u) / D * (Rabs h * D) =
                      Rabs h * Rabs (u * u * u) * Rabs h).
        { field. exact HnzD. }
        rewrite Hr1.
        apply Rle_trans with (h * h * Rabs (u * u * u)).
        * exact Hlin.
        * assert (Heq3 : Rabs h * Rabs (u * u * u) * Rabs h = h * h * Rabs (u * u * u)).
          { rewrite Hh2. ring. }
          rewrite Heq3.
          apply Rle_refl.
Qed.
(* ============================================================
   块 3 落地（2026-08-18）：Aint_derive  A'(γ) = C(γ)  （DCT，控制收敛，完整证明）
   配套：scal/Rmult 桥接引理（exact 模式，规避 apply RInt_scal 实例统一挂死）、
         |u³|/D 连续性、e(h,u) 连续性、|f(h,u)| ≤ g(u)、RInt_gen_A_diff
   ============================================================ *)

(* R 连续运算辅助 *)
Lemma continuous_Rplus : forall (f g : R -> R) (x : R),
  continuous f x -> continuous g x -> continuous (fun y => f y + g y) x.
Proof.
  intros f g x Hf Hg.
  apply (continuous_ext (fun y => plus (f y) (g y)) (fun y => f y + g y) x).
  - intro y. simpl. reflexivity.
  - apply (continuous_plus f g x Hf Hg).
Qed.

Lemma continuous_Rmult : forall (f g : R -> R) (x : R),
  continuous f x -> continuous g x -> continuous (fun y => f y * g y) x.
Proof.
  intros f g x Hf Hg.
  apply (continuous_ext (fun y => mult (f y) (g y)) (fun y => f y * g y) x).
  - intro y. simpl. reflexivity.
  - apply (continuous_mult f g x Hf Hg).
Qed.

(* ===== 桥接引理：scal/Rmult 转换（必须用 exact，禁用 apply RInt_scal —— 会挂死） ===== *)
Lemma scal_is_mult : forall (k x : R), scal k x = k * x.
Proof. intros. reflexivity. Qed.

Lemma RInt_Rmult_l : forall (f : R -> R) (a b k : R),
  ex_RInt f a b -> RInt (fun x => k * f x) a b = k * RInt f a b.
Proof.
  intros f a b k Hex.
  rewrite <- (scal_is_mult k).
  change (RInt (fun x => scal k (f x)) a b = scal k (RInt f a b)).
  exact (RInt_scal f a b k Hex).
Qed.

(* |u^3|/D 的连续性（原证明内联 3 次，抽出复用） *)
Lemma e_paren_eq : forall (h u : R),
  Rabs h * (Rabs (u * u * u) / ((1 + u * u) * (1 + u * u))) =
  Rabs h * Rabs (u * u * u) / ((1 + u * u) * (1 + u * u)).
Proof. intros. unfold Rdiv. ring. Qed.

Lemma cont_abs_u3_over_D : forall u : R,
  continuous (fun v => Rabs (v * v * v) / ((1 + v * v) * (1 + v * v))) u.
Proof.
  intros u.
  apply (continuous_Rmult (fun v => Rabs (v * v * v))
                          (fun v => / ((1 + v * v) * (1 + v * v))) u).
  - apply (continuous_comp (fun v => v * v * v) Rabs u).
    + apply (continuous_Rmult (fun v => v * v) (fun v => v) u).
      * apply (continuous_Rmult (fun v => v) (fun v => v) u); apply continuous_id.
      * apply continuous_id.
    + apply continuous_Rabs.
  - apply (continuous_Rinv_comp (fun v => (1 + v * v) * (1 + v * v)) u).
    + apply (continuous_Rmult (fun v => 1 + v * v) (fun v => 1 + v * v) u).
      * apply (continuous_Rplus (fun _ => 1) (fun v => v * v) u).
        -- apply continuous_const.
        -- apply (continuous_Rmult (fun v => v) (fun v => v) u); apply continuous_id.
      * apply (continuous_Rplus (fun _ => 1) (fun v => v * v) u).
        -- apply continuous_const.
        -- apply (continuous_Rmult (fun v => v) (fun v => v) u); apply continuous_id.
    + assert (Hsq : 0 <= u * u) by apply Rle_0_sqr.
      assert (H1 : 0 < 1 + u * u) by lra.
      apply Rgt_not_eq.
      apply Rmult_lt_0_compat; exact H1; exact H1.
Qed.

(* 支配函数 g(u) = u²/(1+u²)² 可积：Cint 0 = π/4 *)
Lemma ex_RInt_gen_u2_sq : ex_RInt_gen (fun u => (u * u) / ((1 + u * u) * (1 + u * u)))
                            (at_right 0) (Rbar_locally p_infty).
Proof.
  apply (ex_RInt_gen_ext_eq (fun u => ku2cos_sq 0 u) (fun u => (u * u) / ((1 + u * u) * (1 + u * u)))).
  + intro u. unfold ku2cos_sq. replace (0 * u) with 0 by ring. rewrite cos_0. unfold Rdiv. ring_simplify. reflexivity.
  + exact (ex_RInt_gen_ku2cos_sq 0).
Qed.


(* 连续性：u ↦ e(h,u) = |h|·|u³|/D *)
Lemma cont_e_diff : forall (h u : R), continuous
  (fun v => Rabs h * Rabs (v * v * v) / ((1 + v * v) * (1 + v * v))) u.
Proof.
  intros h u.
  apply (continuous_Rmult (fun v => Rabs h * Rabs (v * v * v))
                          (fun v => / ((1 + v * v) * (1 + v * v))) u).
  - apply (continuous_Rmult (fun v => Rabs h) (fun v => Rabs (v * v * v)) u).
    + apply continuous_const.
    + apply (continuous_comp (fun v => v * v * v) Rabs u).
      * apply (continuous_Rmult (fun v => v * v) (fun v => v) u).
        -- apply (continuous_Rmult (fun v => v) (fun v => v) u); apply continuous_id.
        -- apply continuous_id.
      * apply continuous_Rabs.
  - apply (continuous_Rinv_comp (fun v => (1 + v * v) * (1 + v * v)) u).
    + apply (continuous_Rmult (fun v => 1 + v * v) (fun v => 1 + v * v) u).
      * apply (continuous_Rplus (fun _ => 1) (fun v => v * v) u).
        -- apply continuous_const.
        -- apply (continuous_Rmult (fun v => v) (fun v => v) u); apply continuous_id.
      * apply (continuous_Rplus (fun _ => 1) (fun v => v * v) u).
        -- apply continuous_const.
        -- apply (continuous_Rmult (fun v => v) (fun v => v) u); apply continuous_id.
    + assert (Hsq : 0 <= u * u) by apply Rle_0_sqr.
      assert (H1 : 0 < 1 + u * u) by lra.
      apply Rgt_not_eq.
      apply Rmult_lt_0_compat; exact H1; exact H1.
Qed.

(* |f(h,u)| ≤ g(u)：分 h=0 / h≠0 *)
(* |f(h,u)| ≤ g(u)：分 h=0 / h≠0 *)
(* |f(h,u)| ≤ g(u)：分 h=0 / h≠0 *)
Lemma Rabs_A_diff_le_g : forall (gamma u h : R),
  Rabs (A_diff gamma u h) <= (u * u) / ((1 + u * u) * (1 + u * u)).
Proof.
  intros gamma u h.
  unfold A_diff.
  destruct (Req_EM_T h 0) as [Hh0 | Hhn0].
  - (* h = 0：|ku2cos_sq γ u| ≤ u²/D *)
    subst h.
    unfold ku2cos_sq.
    assert (HposD : 0 < (1 + u * u) * (1 + u * u)).
    { assert (Hsq : 0 <= u * u) by apply Rle_0_sqr.
      assert (H1 : 0 < 1 + u * u) by lra.
      apply Rmult_lt_0_compat; exact H1; exact H1. }
    change (Rabs (((u * u) * cos (gamma * u)) / ((1 + u * u) * (1 + u * u)))
            <= (u * u) / ((1 + u * u) * (1 + u * u))).
    apply (Rabs_div_le ((u * u) * cos (gamma * u)) (u * u)
                        ((1 + u * u) * (1 + u * u)) HposD).
    rewrite (Rabs_mult (u * u) (cos (gamma * u))).
    rewrite (Rabs_pos_eq (u * u) (Rle_0_sqr u)).
    rewrite Rmult_comm.
    apply Rle_trans with (1 * (u * u)).
    - apply Rmult_le_compat_r.
      + apply Rle_0_sqr.
      + apply Rabs_cos_le_1.
    - rewrite Rmult_1_l. apply Rle_refl.
  - (* h ≠ 0：|u(sin((γ+h)u)−sin(γu))/h|/D ≤ u²/D *)
    unfold kusin_sq.
    assert (Hsub : Rabs (u * sin ((gamma + h) * u) - u * sin (gamma * u))
                    <= Rabs h * (u * u)).
    { apply Rabs_u_sin_sub_h. }
    assert (Hnz_D : (1 + u * u) * (1 + u * u) <> 0).
    { apply Rgt_not_eq.
      assert (Hsq : 0 <= u * u) by apply Rle_0_sqr.
      assert (H1 : 0 < 1 + u * u) by lra.
      apply Rmult_lt_0_compat; exact H1; exact H1. }
    assert (Hnz_1pu2 : 1 + u * u <> 0).
    { apply Rgt_not_eq. assert (Hsq : 0 <= u * u) by apply Rle_0_sqr. lra. }
    assert (Hnz_hD : h * ((1 + u * u) * (1 + u * u)) <> 0)
      by (apply Rmult_integral_contrapositive; split; [exact Hhn0 | exact Hnz_D]).
    assert (Hcomb : (u * sin ((gamma + h) * u) / ((1 + u * u) * (1 + u * u)) -
                     u * sin (gamma * u) / ((1 + u * u) * (1 + u * u))) / h =
                    (u * sin ((gamma + h) * u) - u * sin (gamma * u)) /
                    (h * ((1 + u * u) * (1 + u * u)))).
    { field. split; [exact Hnz_1pu2 | exact Hhn0]. }
    rewrite Hcomb.
    rewrite (Rabs_div (u * sin ((gamma + h) * u) - u * sin (gamma * u))
                      (h * ((1 + u * u) * (1 + u * u))) Hnz_hD).
    rewrite Rabs_mult.
    assert (HposD : 0 <= (1 + u * u) * (1 + u * u)).
    { apply Rlt_le.
      apply Rmult_lt_0_compat; [assert (H : 0 <= u * u) by apply Rle_0_sqr; lra |
                                 assert (H : 0 <= u * u) by apply Rle_0_sqr; lra]. }
    rewrite (Rabs_pos_eq ((1 + u * u) * (1 + u * u)) HposD).
    assert (HposD_lt : 0 < (1 + u * u) * (1 + u * u)).
    { apply Rmult_lt_0_compat; [assert (H : 0 <= u * u) by apply Rle_0_sqr; lra |
                                 assert (H : 0 <= u * u) by apply Rle_0_sqr; lra]. }
    assert (Hpos_hD : 0 < Rabs h * ((1 + u * u) * (1 + u * u))).
    { apply Rmult_lt_0_compat; [apply Rabs_pos_lt; exact Hhn0 | exact HposD_lt]. }
    apply (Rmult_le_reg_r (Rabs h * ((1 + u * u) * (1 + u * u)))).
    + exact Hpos_hD.
    + assert (Hl1 : Rabs (u * sin ((gamma + h) * u) - u * sin (gamma * u)) /
                    (Rabs h * ((1 + u * u) * (1 + u * u))) *
                    (Rabs h * ((1 + u * u) * (1 + u * u))) =
                    Rabs (u * sin ((gamma + h) * u) - u * sin (gamma * u))).
      { field. split; [exact Hnz_1pu2 | apply Rabs_no_R0; exact Hhn0]. }
      rewrite Hl1.
      assert (Hrepl : u * u / ((1 + u * u) * (1 + u * u)) *
                      (Rabs h * ((1 + u * u) * (1 + u * u))) = Rabs h * (u * u)).
      { field. exact Hnz_1pu2. }
      rewrite Hrepl.
      exact Hsub.
Qed.
(* RInt_gen (A_diff γ · h) = (Aint(γ+h) − Aint γ)/h，h≠0 *)
(* RInt_gen (A_diff γ · h) = (Aint(γ+h) − Aint γ)/h，h≠0 *)
(* RInt_gen (A_diff γ · h) = (Aint(γ+h) − Aint γ)/h，h≠0 *)
(* RInt_gen (A_diff γ · h) = (Aint(γ+h) − Aint γ)/h，h≠0 *)
Lemma RInt_gen_A_diff : forall (gamma h : R), h <> 0 ->
  RInt_gen (fun u => A_diff gamma u h) (at_right 0) (Rbar_locally p_infty) =
  (Aint (gamma + h) - Aint gamma) / h.
Proof.
  intros gamma h Hhn0.
  unfold Aint, Rdiv.
  assert (Hminus : RInt_gen (kusin_sq (gamma + h)) (at_right 0) (Rbar_locally p_infty) -
                   RInt_gen (kusin_sq gamma) (at_right 0) (Rbar_locally p_infty) =
                   RInt_gen (fun u => kusin_sq (gamma + h) u - kusin_sq gamma u)
                            (at_right 0) (Rbar_locally p_infty)).
  { symmetry. apply (RInt_gen_minus_l (kusin_sq (gamma + h)) (kusin_sq gamma)
                      (at_right 0) (Rbar_locally p_infty)).
    - apply (@Proper_StrongProper R (at_right 0) (at_right_proper_filter 0)).
    - apply (@Proper_StrongProper R (Rbar_locally p_infty) (Rbar_locally_filter p_infty)).
    - apply (ex_RInt_gen_ext_eq (kusin_sq (gamma + h)) (kusin_sq (gamma + h))).
      + intro u; reflexivity.
      + apply (ex_RInt_gen_kusin_sq (gamma + h)).
    - apply (ex_RInt_gen_ext_eq (kusin_sq gamma) (kusin_sq gamma)).
      + intro u; reflexivity.
      + apply (ex_RInt_gen_kusin_sq gamma). }
  rewrite Hminus.
  rewrite (Rmult_comm (RInt_gen (fun u => kusin_sq (gamma + h) u - kusin_sq gamma u)
                     (at_right 0) (Rbar_locally p_infty)) (/ h)).
  rewrite <- (RInt_gen_scal_l (fun u => kusin_sq (gamma + h) u - kusin_sq gamma u) (/ h)
                (at_right 0) (Rbar_locally p_infty)
                (@Proper_StrongProper R (at_right 0) (at_right_proper_filter 0))
                (@Proper_StrongProper R (Rbar_locally p_infty) (Rbar_locally_filter p_infty))
                (ex_RInt_gen_plus_l (kusin_sq (gamma + h)) (fun u => - kusin_sq gamma u)
                     (at_right 0) (Rbar_locally p_infty)
                     (@Proper_StrongProper R (at_right 0) (at_right_proper_filter 0))
                     (@Proper_StrongProper R (Rbar_locally p_infty) (Rbar_locally_filter p_infty))
                     (ex_RInt_gen_ext_eq (kusin_sq (gamma + h)) (kusin_sq (gamma + h))
                          (fun u => eq_refl) (ex_RInt_gen_kusin_sq (gamma + h)))
                       (ex_RInt_gen_ext_eq (fun u => scal (opp one) (kusin_sq gamma u)) (fun u => - kusin_sq gamma u)
                            (fun u => scal_opp_one (kusin_sq gamma u))
                            (ex_RInt_gen_scal_l (kusin_sq gamma) (-1)
                                (at_right 0) (Rbar_locally p_infty)
                                (@Proper_StrongProper R (at_right 0) (at_right_proper_filter 0))
                                (@Proper_StrongProper R (Rbar_locally p_infty) (Rbar_locally_filter p_infty))
                                 (ex_RInt_gen_kusin_sq gamma))))).
  apply (RInt_gen_ext_pf (fun u => A_diff gamma u h)
                         (fun u => / h * (kusin_sq (gamma + h) u - kusin_sq gamma u))).
  - apply at_right_proper_filter.
  - apply Rbar_locally_filter.
  - intro u.
    unfold A_diff.
    destruct (Req_EM_T h 0) as [Hh0 | Hhn0'].
    + exfalso. exact (Hhn0 Hh0).
    + unfold Rdiv. rewrite Rmult_comm. reflexivity.
  - apply (ex_RInt_gen_ext_eq (fun u => / h * (kusin_sq (gamma + h) u - kusin_sq gamma u))
                               (fun u => A_diff gamma u h)).
    + intro u. unfold A_diff.
      destruct (Req_EM_T h 0) as [Hh0 | Hhn0'].
      * exfalso. exact (Hhn0 Hh0).
      * unfold Rdiv. rewrite Rmult_comm. reflexivity.
    + apply (ex_RInt_gen_scal_l (fun u => kusin_sq (gamma + h) u - kusin_sq gamma u) (/ h)
                (at_right 0) (Rbar_locally p_infty)).
      * apply (@Proper_StrongProper R (at_right 0) (at_right_proper_filter 0)).
      * apply (@Proper_StrongProper R (Rbar_locally p_infty) (Rbar_locally_filter p_infty)).
      * apply (ex_RInt_gen_plus_l (kusin_sq (gamma + h)) (fun u => - kusin_sq gamma u)
                   (at_right 0) (Rbar_locally p_infty)).
        -- apply (@Proper_StrongProper R (at_right 0) (at_right_proper_filter 0)).
        -- apply (@Proper_StrongProper R (Rbar_locally p_infty) (Rbar_locally_filter p_infty)).
        -- apply (ex_RInt_gen_ext_eq (kusin_sq (gamma + h)) (kusin_sq (gamma + h))).
           ++ intro u; reflexivity.
           ++ apply (ex_RInt_gen_kusin_sq (gamma + h)).
        -- apply (ex_RInt_gen_ext_eq (fun u => - kusin_sq gamma u) (fun u => - kusin_sq gamma u)).
           ++ intro u; reflexivity.
           ++ apply (ex_RInt_gen_abs_le (fun u => - kusin_sq gamma u)
                      (fun u => u / ((1 + u * u) * (1 + u * u))) 0).
               ** intros t Ht. unfold kusin_sq.
                  apply (continuous_opp (fun u => u * sin (gamma * u) / ((1 + u * u) * (1 + u * u))) t).
                  apply (continuous_Rmult (fun u => u * sin (gamma * u))
                             (fun u => / ((1 + u * u) * (1 + u * u))) t).
                  --- apply (continuous_Rmult (fun u => u) (fun u => sin (gamma * u)) t).
                      ++++ apply continuous_id.
                      ++++ apply (continuous_comp (fun u => gamma * u) sin t).
                           +++++ apply (continuous_scal_r gamma (fun u => u) t).
                                apply continuous_id.
                           +++++ apply continuous_sin.
                  --- apply (continuous_Rinv_comp (fun u => (1 + u * u) * (1 + u * u)) t).
                      ++++ apply (continuous_mult (fun u => 1 + u * u) (fun u => 1 + u * u) t).
                           +++++ apply (continuous_Rplus (fun _ => 1) (fun u => u * u) t).
                                ++++++ apply continuous_const.
                                ++++++ apply (continuous_Rmult (fun u => u) (fun u => u) t); apply continuous_id.
                           +++++ apply (continuous_Rplus (fun _ => 1) (fun u => u * u) t).
                                ++++++ apply continuous_const.
                                ++++++ apply (continuous_Rmult (fun u => u) (fun u => u) t); apply continuous_id.
                      ++++ assert (Hsq : 0 <= t * t) by apply Rle_0_sqr.
                           assert (H1 : 0 < 1 + t * t) by lra.
                           apply Rgt_not_eq.
                           apply Rmult_lt_0_compat; exact H1; exact H1.
               ** intros t Ht. apply cont_u_over_1p2sq.
               ** intros t Ht. apply Rdiv_le_0_compat; [exact Ht | assert (Hsq : 0 <= t * t) by apply Rle_0_sqr; assert (H1 : 0 < 1 + t * t) by lra; apply Rmult_lt_0_compat; exact H1; exact H1].
               ** intros t Ht. unfold kusin_sq.
                  assert (HposD : 0 < (1 + t * t) * (1 + t * t)).
                  { assert (Hsq : 0 <= t * t) by apply Rle_0_sqr.
                    assert (H1 : 0 < 1 + t * t) by lra.
                    apply Rmult_lt_0_compat; exact H1; exact H1. }
                  rewrite Rabs_Ropp.
                  apply (Rabs_div_le (t * sin (gamma * t)) t
                                      ((1 + t * t) * (1 + t * t)) HposD).
                  rewrite Rabs_mult.
                  rewrite (Rabs_pos_eq t Ht).
                  rewrite Rmult_comm.
                  apply Rle_trans with (1 * t).
                  --- apply Rmult_le_compat_r.
                      ++++ apply Ht.
                      ++++ apply Rabs_sin_le_1.
                  --- rewrite Rmult_1_l. apply Rle_refl.
              ** apply (ex_RInt_gen_abs_le (fun u => u / ((1 + u * u) * (1 + u * u)))
                          (fun u => u / ((1 + u * u) * (1 + u * u))) 0).
                 --- intros t Ht. apply cont_u_over_1p2sq.
                 --- intros t Ht. apply cont_u_over_1p2sq.
                  --- intros t Ht. apply Rdiv_le_0_compat; [exact Ht | assert (Hsq : 0 <= t * t) by apply Rle_0_sqr; assert (H1 : 0 < 1 + t * t) by lra; apply Rmult_lt_0_compat; exact H1; exact H1].
                  --- intros t Ht. rewrite Rabs_pos_eq; [reflexivity | apply Rdiv_le_0_compat; [exact Ht | assert (Hsq : 0 <= t * t) by apply Rle_0_sqr; assert (H1 : 0 < 1 + t * t) by lra; apply Rmult_lt_0_compat; exact H1; exact H1] ].
                 --- exists (/ 2). exact RInt_gen_sq2.
Qed.
(* A'(γ) = C(γ)：DCT *)
Lemma Aint_derive : forall (gamma : R), 0 < gamma ->
  is_derive Aint gamma (Cint gamma).
Proof.
  intros gamma Hgamma.
  apply is_derive_from_quotient.
  intros eps Heps.
  set (f := fun h u => A_diff gamma u h).
  set (f0 := fun u => ku2cos_sq gamma u).
  set (g := fun u => (u * u) / ((1 + u * u) * (1 + u * u))).
  set (e := fun h u => Rabs h * Rabs (u * u * u) / ((1 + u * u) * (1 + u * u))).
  assert (Hlim : filterlim (fun h : R => RInt_gen (f h) (at_right 0) (Rbar_locally p_infty))
                  (locally 0) (locally (RInt_gen f0 (at_right 0) (Rbar_locally p_infty)))).
  { apply (RInt_gen_lim f f0 g e (locally 0)).
    - apply locally_filter.
    - intros u. unfold f0, g, ku2cos_sq.
      assert (HposD : 0 < (1 + u * u) * (1 + u * u)).
      { assert (Hsq : 0 <= u * u) by apply Rle_0_sqr.
        assert (H1 : 0 < 1 + u * u) by lra.
        apply Rmult_lt_0_compat; exact H1; exact H1. }
      change (Rabs (((u * u) * cos (gamma * u)) / ((1 + u * u) * (1 + u * u)))
              <= (u * u) / ((1 + u * u) * (1 + u * u))).
      apply (Rabs_div_le ((u * u) * cos (gamma * u)) (u * u)
                          ((1 + u * u) * (1 + u * u)) HposD).
      rewrite (Rabs_mult (u * u) (cos (gamma * u))).
      rewrite (Rabs_pos_eq (u * u) (Rle_0_sqr u)).
      rewrite Rmult_comm.
      apply Rle_trans with (1 * (u * u)).
      + apply Rmult_le_compat_r.
        * apply Rle_0_sqr.
        * apply Rabs_cos_le_1.
      + rewrite Rmult_1_l. apply Rle_refl.
    - intros h u. unfold f. apply (Rabs_A_diff_le_g gamma u h).
    - intros h u. unfold f, f0, e. apply Rabs_A_diff_lin_all.
    - intros h u. unfold e.
      apply Rdiv_le_0_compat.
      + apply Rmult_le_pos; [apply Rabs_pos | apply Rabs_pos].
      + assert (Hsq : 0 <= u * u) by apply Rle_0_sqr. assert (H1 : 0 < 1 + u * u) by lra. apply Rmult_lt_0_compat; exact H1; exact H1.
    - intros u. unfold g. apply Rdiv_le_0_compat; [apply Rle_0_sqr | assert (Hsq2 : 0 <= u * u) by apply Rle_0_sqr; assert (H12 : 0 < 1 + u * u) by lra; apply Rmult_lt_0_compat; exact H12; exact H12].
    - intros u. unfold g.
      apply (continuous_Rmult (fun v => v * v) (fun v => / ((1 + v * v) * (1 + v * v))) u).
      + apply (continuous_Rmult (fun v => v) (fun v => v) u); apply continuous_id.
      + apply (continuous_Rinv_comp (fun v => (1 + v * v) * (1 + v * v)) u).
        * apply (continuous_Rmult (fun v => 1 + v * v) (fun v => 1 + v * v) u).
          -- apply (continuous_Rplus (fun _ => 1) (fun v => v * v) u).
             ++ apply continuous_const.
             ++ apply (continuous_Rmult (fun v => v) (fun v => v) u); apply continuous_id.
          -- apply (continuous_Rplus (fun _ => 1) (fun v => v * v) u).
             ++ apply continuous_const.
             ++ apply (continuous_Rmult (fun v => v) (fun v => v) u); apply continuous_id.
        * assert (Hsq : 0 <= u * u) by apply Rle_0_sqr.
          assert (H1 : 0 < 1 + u * u) by lra.
          apply Rgt_not_eq.
          apply Rmult_lt_0_compat; exact H1; exact H1.
    - exact ex_RInt_gen_u2_sq.
    - intros h u. unfold f. apply cont_A_diff.
    - intros u. unfold f0. apply cont_ku2cos_sq.
    - intros h u. unfold e. apply cont_e_diff.
    - intros M HM.
      unfold e.
      apply (filterlim_ext (fun h : R => RInt (fun u : R => Rabs h * (Rabs (u * u * u) / ((1 + u * u) * (1 + u * u)))) 0 M)
                           (fun h : R => RInt (fun u : R => Rabs h * Rabs (u * u * u) / ((1 + u * u) * (1 + u * u))) 0 M)).
      { intro h. apply RInt_ext. intros u _. cbv beta. exact (e_paren_eq h u). }
      { exact (filterlim_RInt_abs_scal (fun u : R => Rabs (u * u * u) / ((1 + u * u) * (1 + u * u))) M HM
                 (fun u => cont_abs_u3_over_D u)). }
  }
  assert (HCint : RInt_gen f0 (at_right 0) (Rbar_locally p_infty) = Cint gamma).
  { unfold f0, Cint. reflexivity. }
  assert (Hfl : filterlim (fun h : R => RInt_gen (f h) (at_right 0) (Rbar_locally p_infty))
                  (locally 0) (locally (Cint gamma))).
  { rewrite HCint in Hlim. exact Hlim. }
  unfold filterlim in Hfl.
  assert (Hloc : locally (Cint gamma) (fun x => Rabs (x - Cint gamma) < eps)).
  { unfold locally.
    exists (mkposreal eps Heps).
    intros y Hy.
    exact Hy. }
  destruct (Hfl _ Hloc) as [d Hd].
  exists d.
  intros h Hh Hh0.
  replace (/ h * (Aint (gamma + h) - Aint gamma))
    with ((Aint (gamma + h) - Aint gamma) / h)
    by (unfold Rdiv; ring).
  rewrite <- (RInt_gen_A_diff gamma h Hh0).
  exact (Hd h Hh).
Qed.

End FourierAnalysis.
