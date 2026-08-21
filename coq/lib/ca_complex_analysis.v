(* 拆分自 Riemann_Hypothesis_Proof_Framework.v（复分析证明库 v6.0）*)
(* 库: ca_complex_analysis  原文行区间: 574-824  机械拆分，未改动内容 *)

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

Require Import ca_base ca_algebra ca_primes.

Require Import Stdlib.Logic.IndefiniteDescription.

(* ====================================================
   第4章：几何结构 (Level 2)
   ==================================================== *)

(* 4.1 希尔伯特空间 *)
Module HilbertSpace.

Import ComplexNumbers.          (* 导入复数模块 *)
Local Open Scope complex_scope. (* 打开复数作用域 *)

(* 有限索引类型：fin n 表示小于 n 的自然数集合 *)
Inductive fin : nat -> Type :=
| fin_0 : forall n, fin (S n)
| fin_S : forall n, fin n -> fin (S n).

(* 希尔伯特空间结构定义 *)
Record HilbertSpace : Type := {
  points : Type;
  inner_product : points -> points -> Complex;
  zero_vector : points;
  add_vectors : points -> points -> points;
  scale_vector : Complex -> points -> points;

  (* 内积共轭对称性 *)
  inner_conj_sym : forall x y,
    inner_product x y = Cconj (inner_product y x);
  (* 内积对第一参数的线性性 *)
  inner_linear_left : forall a x y z,
    inner_product (add_vectors (scale_vector a x) (scale_vector a y)) z =
      a *c (inner_product x z) +c a *c (inner_product y z);
  (* 内积正定性 *)
  inner_pos_def : forall x,
    (x = zero_vector) \/ (re (inner_product x x) > 0);

  (* 完备性公理：柯西序列收敛 *)
  inner_complete : forall (f : nat -> points),
    (forall ε : R,
        ε > 0 ->
        exists N : nat,
          forall (m n : nat),
            (m > N)%nat ->
            (n > N)%nat ->
            let diff := add_vectors (f m) (scale_vector (-c C1) (f n)) in
            sqrt (re (inner_product diff diff)) < ε) ->
    exists limit : points,
      forall ε : R,
        ε > 0 ->
        exists N : nat,
          forall (n : nat),
            (n > N)%nat ->
            let diff := add_vectors (f n) (scale_vector (-c C1) limit) in
            sqrt (re (inner_product diff diff)) < ε
}.

(* 有限索引上的求和函数 *)
Fixpoint sum_over_fin {n : nat} : (fin n -> Complex) -> Complex :=
  match n with
  | 0 => fun _ => C0
  | S m => fun f =>
      let last := f (fin_0 m) in
      let rest := sum_over_fin (fun i : fin m => f (fin_S m i)) in
      last +c rest
  end.

(* 有限维希尔伯特空间结构定义 *)
Record FiniteHilbertSpace (dim : nat) : Type := {
  point_finite : Type;
  coord_finite : point_finite -> fin dim -> Complex;
  add_vectors_finite : point_finite -> point_finite -> point_finite;
  scale_vector_finite : Complex -> point_finite -> point_finite;
  zero_vector_finite : point_finite;

  (* 加法与坐标的相容性 *)
  add_compat_finite : forall (p q : point_finite) (i : fin dim),
    coord_finite (add_vectors_finite p q) i =
      (coord_finite p i) +c (coord_finite q i);
  (* 数乘与坐标的相容性 *)
  scale_compat_finite : forall (c : Complex) (p : point_finite) (i : fin dim),
    coord_finite (scale_vector_finite c p) i = c *c (coord_finite p i);
  (* 零向量的坐标 *)
  zero_compat_finite : forall (i : fin dim),
    coord_finite zero_vector_finite i = C0;

  (* 有限维内积定义 *)
  inner_product_finite : point_finite -> point_finite -> Complex;
  inner_product_def_finite : forall (p q : point_finite),
    inner_product_finite p q =
      sum_over_fin (fun i : fin dim => (coord_finite p i) *c (Cconj (coord_finite q i)))
}.

End HilbertSpace.
  
(* ====================================================
   第4章：几何结构 (Level 2)
   ==================================================== *)

(* 4.2 流形结构 *)

Module Manifold.

Import ComplexNumbers.          (* 复数模块：复数定义、运算及性质 *)
Import ListNotations.           (* 列表记法：提供 [ ]、++ 等语法糖 *)
Import ConstructivePrimes.      (* 构造性质数模块：质数判定、质数序列及计数函数 *)

Require Import Stdlib.Lists.List.          (* 标准列表库：列表类型及常用操作 *)
Require Import Stdlib.Reals.Reals.         (* 实数公理系统，定义实数类型及基本定理 *)
Require Import Stdlib.Reals.Rdefinitions.  (* 实数基本定义：0,1,加法,乘法等原始定义 *)
Require Import Stdlib.ZArith.BinInt.       (* 二进制整数，Z 类型及其算术运算 *)
Require Import Stdlib.ZArith.Znumtheory.   (* 整数数论：整除、素数等定义与判定 *)
Require Import Stdlib.Init.Nat.            (* 自然数初始化模块：nat 类型及基本运算 *)
Require Import Stdlib.Arith.PeanoNat.      (* 皮亚诺自然数算术：加法、乘法、比较等 *)
Require Import Stdlib.NArith.NArith.       (* 二进制自然数，N 类型及其算术运算 *)
Require Import Stdlib.ZArith.ZArith.       (* 整数算术总集，包含 ZArith 所有模块 *)

(* 流形记录定义 *)
Record Manifold : Type := {
  (* 流形上的点类型 *)
  points_manifold : Type;
  (* 图册：局部坐标映射 *)
  charts_manifold : nat -> (points_manifold -> list R);
  (* 转移映射 *)
  transition_maps_manifold : nat -> nat -> (list R -> list R);

  (* 覆盖性公理 *)
  charts_cover_manifold : forall p : points_manifold,
    exists n, exists coords, charts_manifold n p = coords /\ coords <> nil;

  (* 转移映射光滑性公理（强化为恒等函数） *)
  transition_smooth_manifold : forall n m,
    exists f : list R -> list R,
      (forall x, transition_maps_manifold n m x = f x) /\ f = (fun x => x);

  (* 相容性公理 *)
  compatibility_manifold : forall n m p,
    charts_manifold m p = transition_maps_manifold n m (charts_manifold n p)
}.

(* 质数流形构造 *)
Definition PrimeManifold : Manifold.
  refine {|
    points_manifold := nat;
    charts_manifold := fun (n : nat) (p : nat) =>
      if ConstructivePrimes.prime p then [INR p] else [INR 0];
    transition_maps_manifold := fun (n m : nat) (x : list R) => x
  |}.

  (* 覆盖性证明 *)
  - intros p.
    exists 0%nat.
    exists (if ConstructivePrimes.prime p then [INR p] else [INR 0]).
    split.
    + reflexivity.
    + destruct (ConstructivePrimes.prime p); simpl; discriminate.

  (* 转移映射光滑性证明 *)
  - intros n m.
    exists (fun x : list R => x).
    split.
    + intros x. reflexivity.
    + reflexivity.

  (* 相容性证明 *)
  - intros n m p.
    reflexivity.
Defined.

End Manifold.
  
(* ====================================================
   第5章：分析结构 (Level 3)
   ==================================================== *)

(* 5.1 全纯函数 *)
Module HolomorphicFunctions.

Import ComplexNumbers.
Import ListNotations.
Import ConstructivePrimes.
Local Open Scope complex_scope.
Open Scope R_scope.

Require Import Stdlib.micromega.Lia.
Require Import Stdlib.Reals.RIneq.
Require Import Stdlib.Reals.R_sqrt.
Require Import Stdlib.Reals.Reals.
Require Import Stdlib.micromega.Lra.
Require Import Stdlib.Reals.Reals.
Require Import Stdlib.setoid_ring.RealField.
Require Import Stdlib.micromega.Psatz.

(* 平方根正蕴含原数正 *)
Lemma sqrt_pos_implies_pos : forall x : R, 0 <= x -> 0 < sqrt x -> 0 < x.
Proof.
  intros x Hnonneg Hsqrt.
  assert (x <> 0) as Hx_nonzero.
  { intro Hx_zero.
    rewrite Hx_zero, sqrt_0 in Hsqrt.
    apply (Rlt_irrefl 0) in Hsqrt.
    contradiction. }
  destruct (Rle_dec x 0) as [Hle|Hgt].
  - assert (x = 0) as Hx0 by (apply Rle_antisym; assumption).
    apply Hx_nonzero in Hx0; contradiction.
  - apply Rnot_le_lt in Hgt; exact Hgt.
Qed.

(* 范数正蕴含模平方非零 *)
Lemma nonzero_if_norm_positive : forall (h : Complex), (0 : R) < Cnorm h -> Cnorm_sq h <> 0.
Proof.
  intros h Hpos.
  unfold Cnorm in Hpos.
  assert (Hnonneg : 0 <= Cnorm_sq h).
  { unfold Cnorm_sq; apply Rplus_le_le_0_compat; apply Rle_0_sqr. }
  apply sqrt_pos_implies_pos in Hpos; [| exact Hnonneg].
  apply Rgt_not_eq; exact Hpos.
Qed.

(* 全纯函数 *)
Definition Holomorphic (f : Complex -> Complex) (z : Complex) : Prop :=
  exists deriv : Complex,
    forall epsilon : R,
      epsilon > 0 ->
      exists delta : R,
        delta > 0 /\
        forall h : Complex,
          forall (Hpos : 0 < Cnorm h),
            Cnorm h < delta ->
            Cnorm (Csub (Cdiv (Csub (f (z +c h)) (f z)) h
                              (nonzero_if_norm_positive h Hpos))
                        deriv) < epsilon.

(* 亚纯函数 [修复]：原定义 f w = (w−z)^n · g(w) 描述的是 n 阶**零点**（若 g(z)≠0），
   不是极点。极点定义为：存在全纯 g，使得 (w−z)^n · f(w) = g(w) 在 z 附近成立
   （即 f 与 g/(w−z)^n 一致，g(z)≠0 时为 n 阶极点）。 *)
Definition Meromorphic (f : Complex -> Complex) (z : Complex) : Prop :=
  exists g : Complex -> Complex,
    Holomorphic g z /\
    exists n : nat, forall w,
      (0 < Cnorm (Csub w z)) ->
      Cmul (Cpow (Csub w z) n) (f w) = g w.

(* 解析延拓 *)
Definition AnalyticContinuation
  (f1 : Complex -> Complex) (D1 : Complex -> Prop)
  (f2 : Complex -> Complex) (D2 : Complex -> Prop) : Prop :=
  exists D : Complex -> Prop,
    (forall z, D1 z -> D z) /\
    (forall z, D2 z -> D z) /\
    exists F : Complex -> Complex,
      (forall z, D z -> Holomorphic F z) /\
      (forall z, D1 z -> F z = f1 z) /\
      (forall z, D2 z -> F z = f2 z).

(* --- 全纯函数封闭性 [补齐 2026-08-15] --- *)

(* 常函数全纯，导数为 0 *)
Lemma Holomorphic_const : forall (c : Complex) (z : Complex), Holomorphic (fun _ => c) z.
Proof.
  intros c z.
  unfold Holomorphic.
  exists C0.
  intros epsilon Heps.
  exists 1.
  split; [lra |].
  intros h Hpos Hlt.
  rewrite Csub_self.
  unfold Cdiv.
  rewrite Cmul_0_l.
  rewrite Csub_self.
  rewrite Cnorm_0.
  lra.
Qed.

(* 全纯函数之和全纯，导数为两导数之和 *)
Lemma Holomorphic_add : forall f1 f2 z, Holomorphic f1 z -> Holomorphic f2 z ->
  Holomorphic (fun w => f1 w +c f2 w) z.
Proof.
  intros f1 f2 z [d1 Hd1] [d2 Hd2].
  unfold Holomorphic.
  exists (d1 +c d2).
  intros epsilon Heps.
  assert (Heps2 : epsilon / 2 > 0) by lra.
  destruct (Hd1 (epsilon / 2) Heps2) as [delta1 [Hd1pos Hd1b]].
  destruct (Hd2 (epsilon / 2) Heps2) as [delta2 [Hd2pos Hd2b]].
  exists (Rmin delta1 delta2).
  split.
  - apply Rmin_pos; assumption.
  - intros h Hpos Hlt.
    assert (Hlt1 : Cnorm h < delta1).
    { apply Rlt_le_trans with (Rmin delta1 delta2); [exact Hlt | apply Rmin_l]. }
    assert (Hlt2 : Cnorm h < delta2).
    { apply Rlt_le_trans with (Rmin delta1 delta2); [exact Hlt | apply Rmin_r]. }
    rewrite Csub_add.
    rewrite Cdiv_add.
    rewrite Csub_add.
    apply Rle_lt_trans with (Cnorm (Cdiv (Csub (f1 (z +c h)) (f1 z)) h (nonzero_if_norm_positive h Hpos) -c d1) +
                             Cnorm (Cdiv (Csub (f2 (z +c h)) (f2 z)) h (nonzero_if_norm_positive h Hpos) -c d2)).
    - apply Cnorm_triangle.
    - apply Rlt_le_trans with (epsilon / 2 + epsilon / 2).
      + apply Rplus_lt_compat.
        * exact (Hd1b h Hpos Hlt1).
        * exact (Hd2b h Hpos Hlt2).
      + lra.
Qed.

(* 全纯函数取负仍全纯，导数为导数取负 *)
Lemma Holomorphic_opp : forall f z, Holomorphic f z ->
  Holomorphic (fun w => Csub C0 (f w)) z.
Proof.
  intros f z [d Hd].
  unfold Holomorphic.
  exists (Csub C0 d).
  intros epsilon Heps.
  destruct (Hd epsilon Heps) as [delta [Hdpos Hdb]].
  exists delta.
  split; [exact Hdpos |].
  intros h Hpos Hlt.
  assert (Hnum : Csub (Csub C0 (f (z +c h))) (Csub C0 (f z)) =
                 Csub C0 (Csub (f (z +c h)) (f z))).
  { transitivity (Csub (f z) (f (z +c h))); [apply Csub_neg_swap | apply Csub_swap]. }
  rewrite Hnum.
  rewrite Cdiv_neg.
  rewrite Csub_neg_swap.
  rewrite <- Cnorm_sub_swap.
  exact (Hdb h Hpos Hlt).
Qed.

(* 全纯性是逐点性质：逐点相等的函数同时全纯或不全纯 *)
Lemma Holomorphic_ext : forall f g z, (forall w, f w = g w) -> Holomorphic f z -> Holomorphic g z.
Proof.
  intros f g z Hext [d Hd].
  unfold Holomorphic.
  exists d.
  intros eps Heps.
  destruct (Hd eps Heps) as [delta [Hdpos Hdb]].
  exists delta; split; [exact Hdpos |].
  intros h Hpos Hlt.
  rewrite <- (Hext (z +c h)).
  rewrite <- (Hext z).
  exact (Hdb h Hpos Hlt).
Qed.

(* 全纯函数乘以复常数仍全纯，导数为常数乘导数 *)
Lemma Holomorphic_scal : forall c f z, Holomorphic f z ->
  Holomorphic (fun w => c *c f w) z.
Proof.
  intros c f z [d Hd].
  unfold Holomorphic.
  exists (c *c d).
  intros epsilon Heps.
  assert (Hc0 : 0 <= Cnorm c) by apply Cnorm_nonneg.
  assert (Heps' : epsilon / (1 + Cnorm c) > 0).
  { apply Rdiv_lt_0_compat; [exact Heps | lra]. }
  destruct (Hd (epsilon / (1 + Cnorm c)) Heps') as [delta [Hdpos Hdb]].
  exists delta.
  split; [exact Hdpos |].
  intros h Hpos Hlt.
  rewrite <- Cmul_sub_distr_l.
  rewrite Cdiv_scal_l.
  rewrite <- Cmul_sub_distr_l.
  rewrite Cnorm_mul.
  destruct (Req_dec (Cnorm c) 0) as [Hc0eq | Hc0gt].
  - rewrite Hc0eq; lra.
  - apply Rlt_le_trans with (Cnorm c * (epsilon / (1 + Cnorm c))).
    + apply Rmult_lt_compat_l; [lra | exact (Hdb h Hpos Hlt)].
    + apply prod_bound_eps; assumption.
Qed.

(* 全纯函数之差全纯，导数为导数之差（由加法与取负推出） *)
Lemma Holomorphic_sub : forall f1 f2 z, Holomorphic f1 z -> Holomorphic f2 z ->
  Holomorphic (fun w => f1 w -c f2 w) z.
Proof.
  intros f1 f2 z H1 H2.
  apply Holomorphic_ext with (fun w => f1 w +c (Csub C0 (f2 w))).
  - intro w; symmetry; apply Csub_as_add.
  - apply Holomorphic_add; [exact H1 | apply Holomorphic_opp; exact H2].
Qed.

Lemma Holomorphic_mul : forall f1 f2 z, Holomorphic f1 z -> Holomorphic f2 z ->
  Holomorphic (fun w => f1 w *c f2 w) z.
Proof.
  intros f1 f2 z [d1 Hd1] [d2 Hd2].
  unfold Holomorphic.
  exists (Cadd (Cmul (f1 z) d2) (Cmul (f2 z) d1)).
  intros epsilon Heps.
  (* M := 1 + |f1 z| + |f2 z| + |d1| + |d2| *)
  set (M := 1 + Cnorm (f1 z) + Cnorm (f2 z) + Cnorm d1 + Cnorm d2).
  assert (Hf1z : 0 <= Cnorm (f1 z)) by apply Cnorm_nonneg.
  assert (Hf2z : 0 <= Cnorm (f2 z)) by apply Cnorm_nonneg.
  assert (Hd1n : 0 <= Cnorm d1) by apply Cnorm_nonneg.
  assert (Hd2n : 0 <= Cnorm d2) by apply Cnorm_nonneg.
  assert (Mpos : 0 < M) by (unfold M; lra).
  assert (Hf1zM : Cnorm (f1 z) < M) by (unfold M; lra).
  assert (Hf2zM : Cnorm (f2 z) < M) by (unfold M; lra).
  assert (Hd1M : Cnorm d1 < M) by (unfold M; lra).
  assert (Hd2M : Cnorm d2 < M) by (unfold M; lra).
  (* eps0 := min 1 (eps/(8M)) *)
  assert (Heps0 : Rmin 1 (epsilon / (8 * M)) > 0).
  { apply Rmin_pos; [lra | apply Rdiv_lt_0_compat; [exact Heps | lra]]. }
  destruct (Hd1 (Rmin 1 (epsilon / (8 * M))) Heps0) as [delta1 [Hd1pos Hd1b]].
  destruct (Hd2 (Rmin 1 (epsilon / (8 * M))) Heps0) as [delta2 [Hd2pos Hd2b]].
  assert (Heps3 : epsilon / (4 * M * M) > 0).
  { apply Rdiv_lt_0_compat; [exact Heps |].
    apply Rmult_lt_0_compat; [lra | exact Mpos]. }
  exists (Rmin 1 (Rmin delta1 (Rmin delta2 (epsilon / (4 * M * M))))).
  split.
  - apply Rmin_pos; [lra | apply Rmin_pos; [exact Hd1pos | apply Rmin_pos; [exact Hd2pos | exact Heps3]]].
  - intros h Hpos Hlt.
    (* 从 delta 中析出各分量界 *)
    assert (Hlt0 : Cnorm h < 1).
    { apply Rlt_le_trans with (Rmin 1 (Rmin delta1 (Rmin delta2 (epsilon / (4 * M * M))))).
      - exact Hlt.
      - apply Rmin_l. }
    assert (Hlt1 : Cnorm h < delta1).
    { apply Rlt_le_trans with (Rmin 1 (Rmin delta1 (Rmin delta2 (epsilon / (4 * M * M))))).
      - exact Hlt.
      - apply Rle_trans with (Rmin delta1 (Rmin delta2 (epsilon / (4 * M * M)))).
        + apply Rmin_r.
        + apply Rmin_l. }
    assert (Hlt2 : Cnorm h < delta2).
    { apply Rlt_le_trans with (Rmin 1 (Rmin delta1 (Rmin delta2 (epsilon / (4 * M * M))))).
      - exact Hlt.
      - apply Rle_trans with (Rmin delta1 (Rmin delta2 (epsilon / (4 * M * M)))).
        + apply Rmin_r.
        + apply Rle_trans with (Rmin delta2 (epsilon / (4 * M * M))).
          * apply Rmin_r.
          * apply Rmin_l. }
    assert (Hlt3 : Cnorm h < epsilon / (4 * M * M)).
    { apply Rlt_le_trans with (Rmin 1 (Rmin delta1 (Rmin delta2 (epsilon / (4 * M * M))))).
      - exact Hlt.
      - apply Rle_trans with (Rmin delta1 (Rmin delta2 (epsilon / (4 * M * M)))).
        + apply Rmin_r.
        + apply Rle_trans with (Rmin delta2 (epsilon / (4 * M * M))).
          * apply Rmin_r.
          * apply Rmin_r. }
    (* 商差界 *)
    assert (HQ1 : Cnorm (Cdiv (Csub (f1 (z +c h)) (f1 z)) h (nonzero_if_norm_positive h Hpos) -c d1) < Rmin 1 (epsilon / (8 * M)))
      by (exact (Hd1b h Hpos Hlt1)).
    assert (HQ2 : Cnorm (Cdiv (Csub (f2 (z +c h)) (f2 z)) h (nonzero_if_norm_positive h Hpos) -c d2) < Rmin 1 (epsilon / (8 * M)))
      by (exact (Hd2b h Hpos Hlt2)).    (* 代数展开 *)
    assert (Hnum : Csub (Cmul (f1 (z +c h)) (f2 (z +c h))) (Cmul (f1 z) (f2 z)) =
                   Cadd (Cmul (f1 (z +c h)) (Csub (f2 (z +c h)) (f2 z)))
                        (Cmul (Csub (f1 (z +c h)) (f1 z)) (f2 z))).
    { apply Csub_mul_mul. }
    rewrite Hnum.
    rewrite Cdiv_add.
    rewrite Cdiv_scal_l.
    rewrite Cdiv_scal_r.
    rewrite Csub_add.
    assert (Hsplit1 : Csub (Cmul (f1 (z +c h)) (Cdiv (Csub (f2 (z +c h)) (f2 z)) h (nonzero_if_norm_positive h Hpos)))
                           (Cmul (f1 z) d2) =
                     Cadd (Cmul (f1 (z +c h)) (Csub (Cdiv (Csub (f2 (z +c h)) (f2 z)) h (nonzero_if_norm_positive h Hpos)) d2))
                          (Cmul (Csub (f1 (z +c h)) (f1 z)) d2)).
    { apply Csub_mul_mul. }
    rewrite Hsplit1.
    assert (Hsplit2 : Csub (Cmul (Cdiv (Csub (f1 (z +c h)) (f1 z)) h (nonzero_if_norm_positive h Hpos)) (f2 z))
                           (Cmul (f2 z) d1) =
                     Cmul (Csub (Cdiv (Csub (f1 (z +c h)) (f1 z)) h (nonzero_if_norm_positive h Hpos)) d1) (f2 z)).
    { rewrite (Cmul_comm (f2 z) d1).
      symmetry; apply Cmul_sub_distr_r. }
    rewrite Hsplit2.
    (* 三角不等式：Cnorm ((A +c B) +c C) <= |A| + |B| + |C| *)
    apply Rle_lt_trans with
      (Cnorm (Cadd (Cmul (f1 (z +c h)) (Csub (Cdiv (Csub (f2 (z +c h)) (f2 z)) h (nonzero_if_norm_positive h Hpos)) d2))
                   (Cmul (Csub (f1 (z +c h)) (f1 z)) d2)) +
       Cnorm (Cmul (Csub (Cdiv (Csub (f1 (z +c h)) (f1 z)) h (nonzero_if_norm_positive h Hpos)) d1) (f2 z))).
    { apply Cnorm_triangle. }
    { apply Rle_lt_trans with
        (Cnorm (Cmul (f1 (z +c h)) (Csub (Cdiv (Csub (f2 (z +c h)) (f2 z)) h (nonzero_if_norm_positive h Hpos)) d2)) +
         Cnorm (Cmul (Csub (f1 (z +c h)) (f1 z)) d2) +
         Cnorm (Cmul (Csub (Cdiv (Csub (f1 (z +c h)) (f1 z)) h (nonzero_if_norm_positive h Hpos)) d1) (f2 z))).
      { apply Rplus_le_compat_r.
        apply Cnorm_triangle. }
      { (* 下面进入三项界 *)
    (* 模的乘性 *)
    rewrite Cnorm_mul.
    rewrite Cnorm_mul.
    rewrite Cnorm_mul.
    (* 记 A1 := Cnorm (f1 (z+h))，A2 := Cnorm (f1 (z+h) -c f1 z)，X := Cnorm (Q1 -c d1)，Y := Cnorm (Q2 -c d2) *)
    (* |Q1| < M 且 |f1(z+h)-f1 z| = |h|·|Q1| *)
    assert (HQ1M : Cnorm (Cdiv (Csub (f1 (z +c h)) (f1 z)) h (nonzero_if_norm_positive h Hpos)) < M).
    { apply Rle_lt_trans with (Cnorm d1 + Cnorm (Cdiv (Csub (f1 (z +c h)) (f1 z)) h (nonzero_if_norm_positive h Hpos) -c d1)).
      - pattern (Cdiv (Csub (f1 (z +c h)) (f1 z)) h (nonzero_if_norm_positive h Hpos)) at 1.
        rewrite <- (Csub_add_rev (Cdiv (Csub (f1 (z +c h)) (f1 z)) h (nonzero_if_norm_positive h Hpos)) d1).
        apply Cnorm_triangle.
      - apply Rlt_le_trans with (Cnorm d1 + 1).
        + apply Rplus_lt_compat_l.
          apply Rlt_le_trans with (Rmin 1 (epsilon / (8 * M))); [exact HQ1 | apply Rmin_l].
        + unfold M; lra. }
    assert (Hf1diff : Cnorm (Csub (f1 (z +c h)) (f1 z)) =
                      Cnorm h * Cnorm (Cdiv (Csub (f1 (z +c h)) (f1 z)) h (nonzero_if_norm_positive h Hpos))).
    { pattern (Csub (f1 (z +c h)) (f1 z)) at 1.
      rewrite <- (Cmul_div_cancel (Csub (f1 (z +c h)) (f1 z)) h (nonzero_if_norm_positive h Hpos)).
      apply Cnorm_mul. }
    (* |f1(z+h)| < 2M *)
    assert (Hf1h2M : Cnorm (f1 (z +c h)) < 2 * M).
    { apply Rle_lt_trans with (Cnorm (f1 z) + Cnorm (Csub (f1 (z +c h)) (f1 z))).
      - pattern (f1 (z +c h)) at 1.
        rewrite <- (Csub_add_rev (f1 (z +c h)) (f1 z)).
        apply Cnorm_triangle.
      - rewrite Hf1diff.
        replace (2 * M) with (M + M) by lra.
        apply Rplus_lt_le_compat.
        + exact Hf1zM.
        + apply Rle_trans with (1 * M).
          * apply Rmult_le_compat.
            -- apply Rlt_le; exact Hpos.
            -- apply Cnorm_nonneg.
            -- apply Rlt_le; exact Hlt0.
            -- apply Rlt_le; exact HQ1M.
          * lra. }
    (* 三项分别 < eps/4, eps/4, eps/8 *)
    apply Rlt_le_trans with (epsilon / 4 + epsilon / 4 + epsilon / 8).
    - repeat apply Rplus_lt_compat.
      + (* 项1：|f1(z+h)|·Y < 2M · min 1 (eps/(8M)) <= eps/4 *)
        apply Rlt_le_trans with (2 * M * Rmin 1 (epsilon / (8 * M))).
        * apply Rmult_le_lt_compat_mix.
          -- apply Cnorm_nonneg.
          -- lra.
          -- apply Cnorm_nonneg.
          -- exact HQ2.
          -- apply Rlt_le; exact Hf1h2M.
        * apply Rle_trans with (2 * M * (epsilon / (8 * M))).
          -- apply Rmult_le_compat_l; [lra | apply Rmin_r].
          -- assert (Hrew : 2 * M * (epsilon / (8 * M)) = epsilon / 4) by (field; lra).
             rewrite Hrew; lra.
      + (* 项2：|f1(z+h)-f1 z|·|d2| < eps/4 *)
        apply Rlt_le_trans with (Cnorm h * M * M).
        * (* |f1diff|·|d2| < |h|·M·M *)
          apply Rmult_le_lt_compat_mix.
          -- apply Cnorm_nonneg.
          -- apply Rmult_lt_0_compat; [exact Hpos | exact Mpos].
          -- apply Cnorm_nonneg.
          -- exact Hd2M.
          -- rewrite Hf1diff.
             apply Rmult_le_compat_l; [apply Rlt_le; exact Hpos | apply Rlt_le; exact HQ1M].
        * (* |h|·M·M <= eps/4 *)
          apply Rle_trans with (epsilon / (4 * M * M) * M * M).
          -- apply Rmult_le_compat_r; [lra |].
             apply Rmult_le_compat_r; [lra | apply Rlt_le; exact Hlt3].
          -- assert (Hrew : epsilon / (4 * M * M) * M * M = epsilon / 4) by (field; lra).
             rewrite Hrew; lra.
      + (* 项3：X·|f2 z| < min 1 (eps/(8M)) · M <= eps/8 *)
        apply Rlt_le_trans with (Rmin 1 (epsilon / (8 * M)) * M).
        * apply Rmult_le_lt_compat_mix.
          -- apply Cnorm_nonneg.
          -- apply Rmin_pos; [lra | apply Rdiv_lt_0_compat; [exact Heps | lra]].
          -- apply Cnorm_nonneg.
          -- exact Hf2zM.
          -- apply Rlt_le; exact HQ1.
        * apply Rle_trans with (epsilon / (8 * M) * M).
          -- apply Rmult_le_compat_r; [lra | apply Rmin_r].
          -- assert (Hrew : epsilon / (8 * M) * M = epsilon / 8) by (field; lra).
             rewrite Hrew; lra.
    - lra. }
  }
Qed.


Definition Ccontinuous (f : Complex -> Complex) (z : Complex) : Prop :=
  forall epsilon : R, epsilon > 0 -> exists delta : R, delta > 0 /\
    forall h : Complex, Cnorm h < delta ->
      Cnorm (Csub (f (z +c h)) (f z)) < epsilon.

Lemma Holomorphic_continuous : forall f z, Holomorphic f z -> Ccontinuous f z.
Proof.
  intros f z [d Hd].
  unfold Ccontinuous.
  intros eps Heps.
  destruct (Hd 1 Rlt_0_1) as [delta1 [Hd1pos Hd1b]].
  assert (Hdnn : 0 <= Cnorm d) by apply Cnorm_nonneg.
  assert (Hden : 0 < 1 + Cnorm d) by lra.
  assert (Heps' : eps / (1 + Cnorm d) > 0) by (apply Rdiv_lt_0_compat; [exact Heps | exact Hden]).
  exists (Rmin delta1 (eps / (1 + Cnorm d))).
  split.
  - apply Rmin_pos; [exact Hd1pos | exact Heps'].
  - intros h Hlt.
    assert (Hlt1 : Cnorm h < delta1).
    { apply Rlt_le_trans with (Rmin delta1 (eps / (1 + Cnorm d))); [exact Hlt | apply Rmin_l]. }
    assert (Hlt2 : Cnorm h < eps / (1 + Cnorm d)).
    { apply Rlt_le_trans with (Rmin delta1 (eps / (1 + Cnorm d))); [exact Hlt | apply Rmin_r]. }
    destruct (Req_dec (Cnorm h) 0) as [Hh0 | Hh0n].
    + assert (Hhzero : h = C0).
      { apply Cnorm_zero_iff; exact Hh0. }
      subst h.
      rewrite Cadd_0_r.
      rewrite Csub_self.
      rewrite Cnorm_0.
      exact Heps.
    + assert (Hnn : 0 <= Cnorm h) by apply Cnorm_nonneg.
      assert (Hpos : 0 < Cnorm h) by lra.
      set (Q := Cdiv (Csub (f (z +c h)) (f z)) h (nonzero_if_norm_positive h Hpos)).
      assert (HQd : Cnorm (Csub Q d) < 1).
      { unfold Q; exact (Hd1b h Hpos Hlt1). }
      assert (Hfd : Cnorm (Csub (f (z +c h)) (f z)) = Cnorm h * Cnorm Q).
      { unfold Q.
        pattern (Csub (f (z +c h)) (f z)) at 1.
        rewrite <- (Cmul_div_cancel (Csub (f (z +c h)) (f z)) h (nonzero_if_norm_positive h Hpos)).
        apply Cnorm_mul. }
      assert (HQM : Cnorm Q < 1 + Cnorm d).
      { apply Rle_lt_trans with (Cnorm (Csub Q d) + Cnorm d).
        - pattern Q at 1.
          rewrite <- (Csub_add_rev Q d).
          rewrite (Rplus_comm (Cnorm (Csub Q d)) (Cnorm d)).
          apply Cnorm_triangle.
        - apply Rplus_lt_le_compat; [exact HQd | lra]. }
      rewrite Hfd.
      apply Rlt_le_trans with (Cnorm h * (1 + Cnorm d)).
      { apply Rmult_lt_compat_l; [exact Hpos | exact HQM]. }
      { apply Rle_trans with ((eps / (1 + Cnorm d)) * (1 + Cnorm d)).
        - apply Rmult_le_compat_r; [lra | apply Rlt_le; exact Hlt2].
        - assert (Hrew : eps / (1 + Cnorm d) * (1 + Cnorm d) = eps) by (field; lra).
          rewrite Hrew; lra. }
Qed.

Lemma Holomorphic_compose : forall f g z, Holomorphic f (g z) -> Holomorphic g z ->
  Holomorphic (fun w => f (g w)) z.
Proof.
  intros f g z [df Hf] [dg Hg].
  unfold Holomorphic.
  exists (df *c dg).
  intros eps Heps.
  (* M := 1 + |df| + |dg| *)
  assert (Hdfn : 0 <= Cnorm df) by apply Cnorm_nonneg.
  assert (Hdgn : 0 <= Cnorm dg) by apply Cnorm_nonneg.
  assert (Mpos : 0 < 1 + Cnorm df + Cnorm dg) by lra.
  assert (HdfM : Cnorm df < 1 + Cnorm df + Cnorm dg) by lra.
  assert (HdgM : Cnorm dg < 1 + Cnorm df + Cnorm dg) by lra.
  assert (Heps1 : Rmin 1 (eps / (4 * (1 + Cnorm df + Cnorm dg))) > 0).
  { apply Rmin_pos; [lra | apply Rdiv_lt_0_compat; [exact Heps | lra]]. }
  assert (Heps2 : eps / (4 * (1 + Cnorm df + Cnorm dg)) > 0).
  { apply Rdiv_lt_0_compat; [exact Heps | lra]. }
  destruct (Hg (Rmin 1 (eps / (4 * (1 + Cnorm df + Cnorm dg)))) Heps1) as [delta_g [Hgpos Hgb]].
  destruct (Hf (eps / (4 * (1 + Cnorm df + Cnorm dg))) Heps2) as [delta_f [Hfpos Hfb]].
  assert (Hd3pos : delta_f / (1 + Cnorm df + Cnorm dg) > 0)
    by (apply Rdiv_lt_0_compat; [exact Hfpos | lra]).
  exists (Rmin delta_g (Rmin 1 (delta_f / (1 + Cnorm df + Cnorm dg)))).
  split.
  - apply Rmin_pos; [exact Hgpos | apply Rmin_pos; [lra | exact Hd3pos]].
  - intros h Hpos Hlt.
    assert (Hltg : Cnorm h < delta_g).
    { apply Rlt_le_trans with (Rmin delta_g (Rmin 1 (delta_f / (1 + Cnorm df + Cnorm dg)))).
      - exact Hlt.
      - apply Rmin_l. }
    assert (Hlt1 : Cnorm h < 1).
    { apply Rlt_le_trans with (Rmin delta_g (Rmin 1 (delta_f / (1 + Cnorm df + Cnorm dg)))).
      - exact Hlt.
      - apply Rle_trans with (Rmin 1 (delta_f / (1 + Cnorm df + Cnorm dg))).
        + apply Rmin_r.
        + apply Rmin_l. }
    assert (Hltf : Cnorm h < delta_f / (1 + Cnorm df + Cnorm dg)).
    { apply Rlt_le_trans with (Rmin delta_g (Rmin 1 (delta_f / (1 + Cnorm df + Cnorm dg)))).
      - exact Hlt.
      - apply Rle_trans with (Rmin 1 (delta_f / (1 + Cnorm df + Cnorm dg))).
        + apply Rmin_r.
        + apply Rmin_r. }
    set (Qg := Cdiv (Csub (g (z +c h)) (g z)) h (nonzero_if_norm_positive h Hpos)).
    assert (HQgd : Cnorm (Csub Qg dg) < Rmin 1 (eps / (4 * (1 + Cnorm df + Cnorm dg))))
      by (unfold Qg; exact (Hgb h Hpos Hltg)).
    assert (HQgM : Cnorm Qg < 1 + Cnorm df + Cnorm dg).
    { apply Rle_lt_trans with (Cnorm (Csub Qg dg) + Cnorm dg).
      - apply Rle_trans with (Cnorm dg + Cnorm (Csub Qg dg)).
        + pattern Qg at 1.
          rewrite <- (Csub_add_rev Qg dg).
          apply Cnorm_triangle.
        + lra.
      - apply Rplus_lt_le_compat.
        + apply Rlt_le_trans with 1.
          * apply Rlt_le_trans with (Rmin 1 (eps / (4 * (1 + Cnorm df + Cnorm dg)))); [exact HQgd | apply Rmin_l].
          * lra.
        + lra. }
    set (k := Csub (g (z +c h)) (g z)).
    assert (Hk : k = h *c Qg).
    { unfold k, Qg.
      symmetry.
      apply Cmul_div_cancel. }
    assert (Hknorm : Cnorm k = Cnorm h * Cnorm Qg).
    { rewrite Hk. apply Cnorm_mul. }
    assert (Hkf : Cnorm k < delta_f).
    { rewrite Hknorm.
      apply Rlt_le_trans with (Cnorm h * (1 + Cnorm df + Cnorm dg)).
      - apply Rmult_lt_compat_l; [exact Hpos | exact HQgM].
      - apply Rle_trans with (delta_f / (1 + Cnorm df + Cnorm dg) * (1 + Cnorm df + Cnorm dg)).
        + apply Rmult_le_compat_r; [lra | apply Rlt_le; exact Hltf].
        + assert (Hrew : delta_f / (1 + Cnorm df + Cnorm dg) * (1 + Cnorm df + Cnorm dg) = delta_f) by (field; lra).
          rewrite Hrew; lra. }
    (* 分情况：Cnorm k = 0（k = C0）或 Cnorm k ≠ 0 *)
    destruct (Req_dec (Cnorm k) 0) as [Hk0 | Hk0n].
    { (* k = C0：商为 0，|df·dg| < eps *)
      assert (Hkeq : k = C0) by (apply Cnorm_zero_iff; exact Hk0).
      assert (HQg0 : Qg = C0).
      { apply Cnorm_zero_iff.
        assert (Hprod : Cnorm h * Cnorm Qg = 0).
        { rewrite <- Hknorm.
          rewrite Hkeq.
          rewrite Cnorm_0.
          lra. }
        destruct (Rmult_integral _ _ Hprod) as [Hh0 | HQ0].
        - exfalso.
          apply (Rlt_irrefl 0).
          apply Rlt_le_trans with (Cnorm h); [exact Hpos | lra].
        - exact HQ0. }
      (* 目标：|Cdiv (Csub (f (g (z+h))) (f (g z))) h H -c df·dg| < eps *)
      (* g (z+h) = g z +c k = g z *)
      assert (Hgz : g (z +c h) = g z).
      { rewrite <- (Csub_add_rev (g (z +c h)) (g z)).
        fold k.
        rewrite Hkeq.
        apply Cadd_0_r. }
      rewrite Hgz.
      rewrite Csub_self.
      rewrite Cdiv_zero.
      (* 目标：|C0 -c df·dg| < eps *)
      rewrite Cnorm_neg.
      rewrite Cnorm_mul.
      (* |dg| = |Qg - dg| < eps1 *)
      assert (Hdgb : Cnorm dg < Rmin 1 (eps / (4 * (1 + Cnorm df + Cnorm dg)))).
      { rewrite HQg0 in HQgd.
        rewrite (Cnorm_neg dg) in HQgd.
        exact HQgd. }
      destruct (Req_dec (Cnorm df) 0) as [Hdf0 | Hdf0n].
      * rewrite Hdf0; lra.
      * assert (Hdfpos : 0 < Cnorm df) by lra.
        apply Rlt_le_trans with (Cnorm df * Rmin 1 (eps / (4 * (1 + Cnorm df + Cnorm dg)))).
        -- apply Rmult_lt_compat_l; [exact Hdfpos | exact Hdgb].
        -- apply Rle_trans with (Cnorm df * (eps / (4 * (1 + Cnorm df + Cnorm dg)))).
           ++ apply Rmult_le_compat_l; [lra | apply Rmin_r].
           ++ apply Rle_trans with ((1 + Cnorm df + Cnorm dg) * (eps / (4 * (1 + Cnorm df + Cnorm dg)))).
              ** apply Rmult_le_compat_r; [lra | lra].
              ** assert (Hrw : (1 + Cnorm df + Cnorm dg) * (eps / (4 * (1 + Cnorm df + Cnorm dg))) = eps / 4) by (field; lra).
                 rewrite Hrw; lra.
    }
    { (* k ≠ C0 *)
      assert (Hkneq : k <> C0).
      { intro Hkc0.
        apply Hk0n.
        rewrite Hkc0.
        apply Cnorm_0. }
      assert (Hkpos : 0 < Cnorm k) by (apply Cnorm_pos_lt; exact Hkneq).
      (* Qf := (f (g z +c k) - f (g z)) / k *)
      set (Qf := Cdiv (Csub (f (g z +c k)) (f (g z))) k (nonzero_if_norm_positive k Hkpos)).
      assert (HQfd : Cnorm (Csub Qf df) < eps / (4 * (1 + Cnorm df + Cnorm dg)))
        by (unfold Qf; exact (Hfb k Hkpos Hkf)).
      (* 目标：|Cdiv (f (g(z+h)) - f (g z)) h -c df·dg| < eps *)
      rewrite <- (Csub_add_rev (g (z +c h)) (g z)).
      fold k.
      (* 分子 = k *c Qf *)
      rewrite <- (Cmul_div_cancel (Csub (f (g z +c k)) (f (g z))) k (nonzero_if_norm_positive k Hkpos)).
      fold Qf.
      rewrite Cdiv_scal_r.
      (* Cdiv k h H = Qg *)
      rewrite Hk.
      rewrite Cdiv_mul_cancel.
      (* 目标：|Qg·Qf - df·dg| < eps *)
      rewrite Csub_mul_mul2.
      apply Rle_lt_trans with
        (Cnorm (Cmul Qg (Csub Qf df)) + Cnorm (Cmul df (Csub Qg dg))).
      - apply Cnorm_triangle.
      - rewrite Cnorm_mul.
        rewrite Cnorm_mul.
        apply Rlt_le_trans with ((1 + Cnorm df + Cnorm dg) * (eps / (4 * (1 + Cnorm df + Cnorm dg))) +
                                 (1 + Cnorm df + Cnorm dg) * (Rmin 1 (eps / (4 * (1 + Cnorm df + Cnorm dg))))).
        + apply Rplus_lt_compat.
          * apply Rmult_le_lt_compat_mix.
            -- apply Cnorm_nonneg.
            -- lra.
            -- apply Cnorm_nonneg.
            -- exact HQfd.
            -- apply Rlt_le; exact HQgM.
          * apply Rmult_le_lt_compat_mix.
            -- apply Cnorm_nonneg.
            -- lra.
            -- apply Cnorm_nonneg.
            -- exact HQgd.
            -- apply Rlt_le; exact HdfM.
        + apply Rle_trans with (eps / 4 + eps / 4).
          * apply Rplus_le_compat.
            -- assert (Hrw1 : (1 + Cnorm df + Cnorm dg) * (eps / (4 * (1 + Cnorm df + Cnorm dg))) <= eps / 4).
               { assert (Heq : (1 + Cnorm df + Cnorm dg) * (eps / (4 * (1 + Cnorm df + Cnorm dg))) = eps / 4) by (field; lra).
                 rewrite Heq; lra. }
               exact Hrw1.
            -- assert (Hrw2 : (1 + Cnorm df + Cnorm dg) * Rmin 1 (eps / (4 * (1 + Cnorm df + Cnorm dg))) <= eps / 4).
               { apply Rle_trans with ((1 + Cnorm df + Cnorm dg) * (eps / (4 * (1 + Cnorm df + Cnorm dg)))).
                 - apply Rmult_le_compat_l; [lra | apply Rmin_r].
                 - assert (Heq : (1 + Cnorm df + Cnorm dg) * (eps / (4 * (1 + Cnorm df + Cnorm dg))) = eps / 4) by (field; lra).
                   rewrite Heq; lra. }
               exact Hrw2.
          * lra.
    }
Qed.

End HolomorphicFunctions.



