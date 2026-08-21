(* 拆分自 Riemann_Hypothesis_Proof_Framework.v（复分析证明库 v6.0）*)
(* 库: ca_taylor  原文行区间: 16484-17471  机械拆分，未改动内容 *)

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

Require Import ca_base ca_algebra ca_primes ca_complex_analysis ca_fourier ca_zeta_scaffold ca_trig ca_gamma.

Require Import Stdlib.Logic.IndefiniteDescription.

(* ====================================================
   泰勒定理的证明（针对指数函数，拉格朗日余项）
   ==================================================== *)

Module TaylorTheorem.

Import PrimeEmbedding.                   (* 导入质数嵌入模块：将质数嵌入无限维希尔伯特空间，关联ζ函数零点 *)

Require Import Stdlib.Reals.Reals.                    (* 标准实数库，自动加载 Rdefinitions, Raxioms, Rbasic_fun 等 *)
Require Import Stdlib.micromega.Lra.                      (* 线性实数算术自动化策略，简写导入（实际为 Coq.micromega.Lra）*)
From Stdlib Require Ranalysis5.                (* 实分析第5部分，包含 Rolle 定理、中值定理等高级分析内容 *)
Require Import Stdlib.Reals.Rtrigo.                   (* 三角函数基础理论，定义 sin, cos, tan 等 *)
Require Import Stdlib.Reals.Rpower.                   (* 实数幂函数 Rpower，基于 ln 和 exp 的定义 *)
Require Import Stdlib.Reals.R_sqrt.                   (* 平方根函数 sqrt 及其性质 *)
Require Import Stdlib.Reals.Ranalysis3.               (* 实分析第3部分，高级导数定理、链式法则、反函数定理等 *)
Require Import Stdlib.Reals.Rfunctions.               (* 实数函数补充库，包含 sum_f_R0（有限项求和）等实用函数 *)
Require Import Stdlib.Reals.Rseries.                  (* 实数序列收敛理论，定义 Un_cv 及收敛极限的唯一性 *)
Require Import Stdlib.Reals.SeqProp.                  (* 序列性质定理，如有界性、单调收敛等（标准库补充）*)
Require Import Stdlib.Reals.Rlimit.                   (* 实数函数极限理论，定义极限、连续性等 *)
Require Import Coquelicot.Coquelicot.    (* Coquelicot 分析库，提供更现代化的实数分析形式化 *)
Require Import mathcomp.analysis.derive. (* MathComp 分析库的导数定义与定理 *)
Require Import Stdlib.Reals.Reals.          (* 实数公理系统及全套定理（重复导入，保证完备性）*)
Require Import Stdlib.Reals.Ranalysis1.     (* 实分析第1部分，导数、可导性、连续性基础 *)
Require Import Stdlib.Reals.Ranalysis5.     (* 实分析第5部分（重复导入），含 Rolle 定理等 *)
Require Import Stdlib.Logic.FunctionalExtensionality. (* 函数外延性公理：∀ f g, (∀ x, f x = g x) → f = g *)
Require Import Stdlib.micromega.Lra.        (* 线性实数算术自动化策略，提供 lra 策略（显式全名导入）*)
Require Import Stdlib.Reals.Rpower.         (* 实数幂函数 Rpower（重复导入，确保可用）*)
Require Import Coquelicot.Coquelicot.    (* Coquelicot 分析库：提供极限、导数、级数、积分等现代化分析形式化 *)
Require Import mathcomp.analysis.derive. (* MathComp 分析库的导数模块：基于滤子的导数定义及相关定理 *)
Open Scope R_scope.                      (* 开启实数作用域，使实数运算符自动生效 *)

(* 阶乘函数 *)
Fixpoint fact (n : nat) : nat :=
  match n with
  | O => 1
  | S n' => (S n') * fact n'
  end.

(* 自然数乘法INR分配律 *)
Lemma INR_mult : forall n m : nat, INR (n * m) = INR n * INR m.
Proof.
  intros n m.
  induction n as [|n IH].
  - simpl. ring.
  - rewrite S_INR.
    simpl.
    rewrite plus_INR.
    rewrite IH.
    ring.
Qed.

(* 阶乘的正实数性 *)
Lemma fact_pos : forall n : nat, 0 < INR (fact n).
Proof.
  intro n.
  induction n as [|n IH].
  - simpl. lra.
  - simpl fact.
    rewrite plus_INR.
    rewrite INR_mult.
    apply Rplus_lt_le_0_compat.
    + exact IH.
    + apply Rmult_le_pos.
      * apply pos_INR.
      * apply Rlt_le, IH.
Qed.

(* 指数函数的泰勒多项式 *)
Definition taylor_poly_exp (a x : R) (n : nat) : R :=
  sum_f_R0 (fun k => exp a / INR (fact k) * (x - a) ^ k) n.

(* 指数函数的拉格朗日余项 *)
Definition lagrange_remainder_exp (a x : R) (n : nat) (theta : R) : R :=
  exp (a + theta * (x - a)) / INR (fact (S n)) * (x - a) ^ (S n).

(* 指数函数中值定理辅助函数 *)
Definition phi (a x : R) (n : nat) (t : R) : R :=
  exp x - taylor_poly_exp a x n - (exp (a + t * (x - a)) / INR (fact (S n)) * (x - a) ^ (S n)) * ((x - a) - t * (x - a)) ^ (S n).

(* INR阶乘非零 *)
Lemma INR_fact_neq_0 : forall n : nat, INR (fact n) <> 0.
Proof.
  intro n.
  apply Rgt_not_eq.
  apply fact_pos.
Qed.

(* 泰勒多项式0,1,5取值 *)
Lemma taylor_poly_exp_0_1_5_value :
  taylor_poly_exp 0 1 5 = 163/60.
Proof.
  unfold taylor_poly_exp.
  rewrite exp_0.
  simpl sum_f_R0.
  replace (fact 0) with 1%nat by reflexivity.
  replace (fact 1) with 1%nat by reflexivity.
  replace (fact 2) with 2%nat by reflexivity.
  replace (fact 3) with 6%nat by reflexivity.
  replace (fact 4) with 24%nat by reflexivity.
  replace (fact 5) with 120%nat by reflexivity.
  compute.
  lra.
Qed.

(* 指数函数单调性 *)
Lemma exp_le : forall x y, x <= y -> exp x <= exp y.
Proof.
  intros x y H.
  destruct H as [H|H].
  - left; apply exp_increasing; exact H.
  - rewrite H; right; reflexivity.
Qed.

(* 阶乘6等于720 *)
Lemma fact6 : fact 6 = 720%nat.
Proof.
  reflexivity.
Qed.

(* 拉格朗日余项上界 *)
Lemma lagrange_remainder_exp_bound_0_1_5 :
  forall theta : R, 0 <= theta <= 1 ->
    lagrange_remainder_exp 0 1 5 theta <= exp 1 / 720.
Proof.
  intros theta [Htheta_low Htheta_high].
  unfold lagrange_remainder_exp.
  replace (1 - 0) with 1 by ring.
  replace (0 + theta * 1) with theta by ring.
  replace (1 ^ 6) with 1 by ring.
  rewrite Rmult_1_r.
  rewrite fact6.
  unfold Rdiv.
  assert (H720: INR 720 = 720).
  { rewrite INR_IZR_INZ.
    compute.
    reflexivity. }
  rewrite H720.
  apply Rmult_le_compat_r.
  - apply Rlt_le, Rinv_0_lt_compat.
    lra.
  - apply exp_le.
    lra.
Qed.

(* 指数函数的导数 *)
Lemma derive_pt_exp_eq : forall x : R,
    derive_pt exp x (derivable_pt_exp x) = exp x.
Proof.
  intros x. apply derive_pt_exp.
Qed.

(* 几何级数部分和公式 *)
Lemma sum_geom : forall n, sum_f_R0 (fun k => (1/6)^k) n = (6/5) * (1 - (1/6)^(S n)).
Proof.
  intro n.
  induction n as [|n IH].
  - compute; lra.
  - rewrite sum_f_R0_S.
    rewrite IH.
    change ((1/6) ^ S (S n)) with ((1/6) * (1/6) ^ S n).
    lra.
Qed.

(* 几何级数部分和上界 *)
Lemma sum_geom_le : forall n, sum_f_R0 (fun k => (1/6)^k) n <= 6/5.
Proof.
  intro n.
  rewrite sum_geom.
  assert (Hpow : 0 <= (1/6) ^ (S n)).
  {
    induction (S n) as [|m IH].
    - compute; lra.
    - apply Rmult_le_pos.
      + lra.
      + exact IH.
  }
  lra.
Qed.

(* 几何级数缩放上界 *)
Lemma geometric_bound : forall n, sum_f_R0 (fun k => / (720 * 6^k)) n <= 1/600.
Proof.
  intro n.

  assert (Hinv_pow : forall k, / (6^k) = (1/6)^k).
  {
    intro k.
    induction k as [|k IH].
    - compute; lra.
    - change ((1/6) ^ S k) with ((1/6) * (1/6)^k).
      change (6 ^ S k) with (6 * 6^k).
      rewrite Rinv_mult.
      rewrite IH.
      replace (/6) with (1/6) by lra.
      reflexivity.
  }

  assert (Hterm : forall k, / (720 * 6^k) = (1/720) * (1/6)^k).
  {
    intro k.
    rewrite Rinv_mult.
    rewrite Hinv_pow.
    replace (/720) with (1/720) by lra.
    reflexivity.
  }

  assert (Hsum_eq : sum_f_R0 (fun k => / (720 * 6^k)) n =
                   sum_f_R0 (fun k => (1/720) * (1/6)^k) n).
  {
    induction n as [|n IHn].
    - simpl. apply (Hterm 0%nat).
    - rewrite !sum_f_R0_S.
      rewrite IHn.
      rewrite (Hterm (S n)).
      reflexivity.
  }
  rewrite Hsum_eq.

  assert (Hfactor : forall n, sum_f_R0 (fun k => (1/720) * (1/6)^k) n =
                              (1/720) * sum_f_R0 (fun k => (1/6)^k) n).
  {
    intro m.
    induction m as [|m IHm].
    - compute; lra.
    - rewrite !sum_f_R0_S.
      rewrite IHm.
      lra.
  }
  rewrite Hfactor.

  apply Rle_trans with ((1/720) * (6/5)).
  - apply Rmult_le_compat_l; [lra | apply sum_geom_le].
  - compute; lra.
Qed.

(* 阶乘倒数求和受几何级数控制 *)
Lemma sum_fact_le_geometric : forall n,
  sum_f_R0 (fun k => / INR (fact (6 + k))) n <= 
  sum_f_R0 (fun k => / (720 * 6^k)) n.
Proof.
  intro n.
  induction n as [|n IH].
  - simpl.
    unfold fact; simpl.
    compute; lra.
  - rewrite !sum_f_R0_S.
    apply Rplus_le_compat.
    + exact IH.
    + assert (Hpos1: 0 < 720 * 6 ^ S n).
      { apply Rmult_lt_0_compat; [lra|]. apply pow_lt; lra. }
      assert (Hpos2: 0 < INR (fact (6 + S n))).
      { apply fact_pos. }
      assert (Hineq: 720 * 6 ^ S n <= INR (fact (6 + S n))).
      { assert (Hge: (6 + S n >= 6)%nat) by lia.
        pose proof (INR_fact_ge_6_pow_n_minus_6 (6 + S n) Hge) as H.
        replace ((6 + S n) - 6)%nat with (S n) in H by lia.
        apply Rge_le in H.
        replace (INR 6) with 6 in H by (simpl; ring).
        exact H.
      }
      apply Rinv_le_contravar with (x := 720 * 6 ^ S n) (y := INR (fact (6 + S n))).
      * exact Hpos1.
      * exact Hineq.
Qed.

(* 从第六项起的阶乘倒数求和上界 *)
Lemma sum_fact_from_6_le : forall n,
  sum_f_R0 (fun k => / INR (fact (6 + k))) n <= 1/600.
Proof.
  intro n.
  apply Rle_trans with (sum_f_R0 (fun k => / (720 * 6^k)) n).
  - apply sum_fact_le_geometric.
  - apply geometric_bound.
Qed.

(* 求和第六项分割 *)
Lemma sum_f_R0_split_at_6 : forall (f : nat -> R) (m : nat),
  sum_f_R0 f (Nat.add 6 m) = sum_f_R0 f 5 + sum_f_R0 (fun i => f (Nat.add 6 i)) m.
Proof.
  intros f m.
  induction m as [|m IH].
  - simpl. ring.
  - replace (Nat.add 6 (S m)) with (S (Nat.add 6 m)) by lia.
    rewrite !sum_f_R0_S.
    rewrite IH.
    replace (S (Nat.add 6 m)) with (Nat.add 6 (S m)) by lia.
    replace (sum_f_R0 f 5) with (sum_f_R0 f 0%nat + f 1%nat + f 2%nat + f 3%nat + f 4%nat + f 5%nat) by (simpl; ring).
    ring.
Qed.

(* 指数级数部分和上界 *)
Lemma exp_1_series_bound : forall n,
  sum_f_R0 (fun k => / INR (fact k)) n <= 163/60 + 1/600.
Proof.
  intro n.
  destruct (le_lt_dec 6 n) as [Hn|Hn].
  - assert (H : n = (6 + (n - 6))%nat) by lia.
    rewrite H.
    rewrite sum_f_R0_split_at_6.
    replace (sum_f_R0 (fun k : nat => / INR (fact k)) 5) with (163/60) by (compute; lra).
    apply Rplus_le_compat_l.
    apply sum_fact_from_6_le.
  - destruct n as [|n]; [compute; lra|].
    destruct n as [|n]; [compute; lra|].
    destruct n as [|n]; [compute; lra|].
    destruct n as [|n]; [compute; lra|].
    destruct n as [|n]; [compute; lra|].
    destruct n as [|n]; [compute; lra|].
    lia.
Qed.

(* 收敛序列极限小于等于一致上界 *)
Lemma Un_cv_le : forall (Un : nat -> R) (l : R) (M : R),
  Un_cv Un l -> (forall n, Un n <= M) -> l <= M.
Proof.
  intros Un l M Hcv Hbound.
  apply Rnot_gt_le; intro H.
  assert (Heps : 0 < l - M) by lra.
  destruct (Hcv (l - M) Heps) as [N HN].
  specialize (HN N (le_n N)).
  unfold R_dist in HN.
  destruct (Rle_dec (Un N) M) as [Hle | Hgt].
  - assert (Hneg : Un N - l < 0) by lra.
    rewrite Rabs_left in HN; [|lra].
    lra.
  - specialize (Hbound N).
    lra.
Qed.

(* 幂乘项求和等式 *)
Lemma sum_eq_lemma : forall n,
  sum_f_R0 (fun n0 : nat => / INR (fact n0) * 1 ^ n0) n = sum_f_R0 (fun n0 : nat => / INR (fact n0)) n.
Proof.
  intro n.
  induction n as [|n IH].
  - simpl. ring.
  - rewrite !sum_f_R0_S.
    rewrite IH.
    assert (H : (1 : R) ^ S n = 1).
    { simpl. rewrite (pow1 n). ring. }
    rewrite H.
    ring.
Qed.

(* 一之幂恒为一 *)
Lemma pow1 : forall n, (1 : R) ^ n = 1.
Proof.
  intro n.
  induction n as [|n IH].
  - reflexivity.
  - simpl. rewrite IH. ring.
Qed.

(* 级数求和重排等式 *)
Lemma sum_eq_lemma_aux : forall n,
  sum_f_R0 (fun k => / INR (fact k)) n = 
  sum_f_R0 (fun k => 1 ^ k / INR (fact k)) n.
Proof.
  intro n.
  induction n as [|n IH].
  - simpl. field.
  - rewrite !sum_f_R0_S.
    rewrite IH.
    rewrite pow1.
    field. apply INR_fact_neq_0.
Qed.

(* 逐点相等序列极限等价 *)
Lemma seq_ext : forall (Un Vn : nat -> R) l, 
  (forall n, Un n = Vn n) -> Un_cv Un l -> Un_cv Vn l.
Proof.
  intros Un Vn l Heq Hcv.
  unfold Un_cv in *.
  intros eps Heps.
  destruct (Hcv eps Heps) as [N HN].
  exists N; intros n Hn.
  rewrite <- Heq.
  apply HN; exact Hn.
Qed.

(* 指数函数在1处的泰勒级数收敛 *)
Lemma exp_1_series_cv : Un_cv (sum_f_R0 (fun k => / INR (fact k))) (exp 1).
Proof.
  unfold exp.
  pose proof (proj2_sig (exist_exp 1)) as H.
  unfold exp_in, infinite_sum in H.
  unfold Un_cv.
  intros eps Heps.
  destruct (H eps Heps) as [N HN].
  exists N.
  intros n Hn.
  specialize (HN n Hn).
  unfold R_dist in *.
  rewrite <- sum_eq_lemma.
  exact HN.
Qed.

(* exp 1 小于3 *)
Lemma exp_1_lt_3 : exp 1 < 3.
Proof.
  assert (Hcalc2 : 1631/600 < 3) by (compute; lra).
  assert (Hcv : Un_cv (sum_f_R0 (fun k => / INR (fact k))) (exp 1)).
  { apply exp_1_series_cv. }
  assert (Hexp_le : exp 1 <= 163/60 + 1/600).
  {
    apply Un_cv_le with (Un := sum_f_R0 (fun k => / INR (fact k))) (M := 163/60 + 1/600).
    - exact Hcv.
    - apply exp_1_series_bound.
  }
  assert (Hsum_eq : 163/60 + 1/600 = 1631/600) by lra.
  rewrite Hsum_eq in Hexp_le.
  apply Rle_lt_trans with (r2 := 1631/600); assumption.
Qed.

(* exp 1 不大于3 *)
Lemma exp_1_le_3 : exp 1 <= 3.
Proof.
  apply Rlt_le.
  exact exp_1_lt_3.
Qed.

(* ============================================================
   S2-Taylor：级数余项路线（构造性，去 Rolle/MVT）
   exp_est_series / sin_est_series 及配套级数机器
   思路：exp/sin 均为幂级数定义（exist_exp/exist_sin），
   部分和夹逼 + 几何/交错级数界，绕开 Lagrange 余项。
   ==================================================== *)

(* ---- 阶乘桥接：模块 fact 与 stdlib fact 等值 ---- *)

Lemma fact_eq_stdlib : forall n, fact n = Stdlib.Arith.Factorial.fact n.
Proof.
  induction n as [|n IH]; simpl; [reflexivity | rewrite IH; reflexivity].
Qed.

Lemma fact_ge_1 : forall n, (1 <= fact n)%nat.
Proof. induction n as [|n IH]; simpl; nia. Qed.

Lemma fact_ge_2 : forall n, (2 <= n)%nat -> (2 <= fact n)%nat.
Proof.
  intros n Hn. destruct n as [|[|n]].
  - lia.
  - lia.
  - assert (H1 : (1 <= fact (S n))%nat) by apply fact_ge_1.
    assert (H2 : (2 <= S (S n))%nat) by lia.
    assert (H3 : (fact (S (S n)) = S (S n) * fact (S n))%nat) by reflexivity.
    nia.
Qed.

Lemma INR_fact_ge_2 : forall n, (2 <= n)%nat -> 2 <= INR (fact n).
Proof. intros n H. change 2 with (INR 2). apply le_INR. apply fact_ge_2. exact H. Qed.

(* ---- 有限求和辅助 ---- *)

Lemma sum_snoc : forall (f : nat -> R) (n : nat),
  sum_f_R0 f (S n) = sum_f_R0 f n + f (S n).
Proof. reflexivity. Qed.

Lemma sum_nonneg : forall (f : nat -> R) (n : nat),
  (forall i, 0 <= f i) -> 0 <= sum_f_R0 f n.
Proof.
  intros f n H. induction n as [|n IH].
  - apply H.
  - rewrite sum_snoc. apply Rplus_le_le_0_compat; [exact IH | apply H].
Qed.

Lemma sum_scal : forall (c : R) (u : nat -> R) (n : nat),
  sum_f_R0 (fun i => c * u i) n = c * sum_f_R0 u n.
Proof.
  intros c u n. induction n as [|n IH].
  - simpl. ring.
  - rewrite !sum_snoc, IH. ring.
Qed.

Lemma sum_f_R0_split_at_2 : forall (f : nat -> R) (m : nat),
  sum_f_R0 f (Nat.add 2 m) = sum_f_R0 f 1 + sum_f_R0 (fun i => f (Nat.add 2 i)) m.
Proof.
  intros f m. induction m as [|m IH].
  - change (Nat.add 2 0%nat) with 2%nat.
    change (sum_f_R0 f 2%nat) with (sum_f_R0 f 1 + f 2%nat).
    change (sum_f_R0 (fun i => f (Nat.add 2 i)) 0%nat) with (f 2%nat).
    ring.
  - replace (Nat.add 2 (S m)) with (S (Nat.add 2 m)) by lia.
    rewrite !sum_snoc.
    rewrite IH.
    cbn beta.
    replace (Nat.add 2 (S m)) with (S (Nat.add 2 m)) by lia.
    replace (sum_f_R0 f 1) with (f 0%nat + f 1%nat) by (simpl; ring).
    change (sum_f_R0 f 0) with (f 0%nat).
    ring.
Qed.

Lemma geom_sum_le_2 : forall (x : R) (n : nat),
  0 <= x -> x <= 1/2 -> sum_f_R0 (fun i => x ^ i) n <= 2.
Proof.
  intros x n Hx0 Hx1.
  assert (Hx_neq1 : x <> 1) by lra.
  rewrite (tech3 x n Hx_neq1).
  assert (H1x : 0 < 1 - x) by lra.
  apply Rle_trans with (1 / (1 - x)).
  - unfold Rdiv.
    assert (Hxp : 0 <= x ^ S n) by (apply pow_le; exact Hx0).
    apply Rmult_le_compat_r.
    + apply Rlt_le. apply Rinv_0_lt_compat. exact H1x.
    + lra.
  - assert (Hinv : 0 < / (1 - x)) by (apply Rinv_0_lt_compat; exact H1x).
    assert (Hne : 1 - x <> 0) by (intro Hc; lra).
    assert (H2x : 2 * x <= 1) by lra.
    assert (Hfinal : 1 / (1 - x) <= 2).
    { unfold Rdiv.
      apply Rle_trans with (2 * (1 - x) * / (1 - x)).
      - apply Rmult_le_compat_r; [apply Rlt_le; exact Hinv | lra].
      - replace (2 * (1 - x) * / (1 - x)) with (2 * ((1 - x) * / (1 - x))) by ring.
        rewrite Rinv_r by exact Hne. rewrite Rmult_1_r. apply Rle_refl. }
    exact Hfinal.
Qed.

(* ---- 序列收敛辅助 ---- *)

Lemma Un_cv_ge : forall (Un : nat -> R) (l : R) (m : R),
  Un_cv Un l -> (forall n, m <= Un n) -> m <= l.
Proof.
  intros Un l m Hcv Hbound.
  apply Rnot_lt_le. intro Hlt.
  assert (Heps : 0 < m - l) by lra.
  destruct (Hcv (m - l) Heps) as [N HN].
  specialize (HN N (le_n N)). specialize (Hbound N).
  unfold R_dist in HN.
  rewrite Rabs_right in HN; [| lra].
  lra.
Qed.

Lemma Un_cv_minus_const : forall (U : nat -> R) (l c : R),
  Un_cv U l -> Un_cv (fun n => U n - c) (l - c).
Proof.
  intros U l c Hcv. unfold Un_cv. intros eps Heps.
  destruct (Hcv eps Heps) as [N HN]. exists N. intros n Hn.
  unfold R_dist in *.
  replace (U n - c - (l - c)) with (U n - l) by ring.
  apply HN. exact Hn.
Qed.

Lemma Un_cv_scal : forall (U : nat -> R) (l k : R),
  Un_cv U l -> Un_cv (fun n => k * U n) (k * l).
Proof.
  intros U l k Hcv. unfold Un_cv. intros eps Heps.
  destruct (Req_dec k 0) as [Hk0|Hk0].
  - exists 0%nat. intros n _. rewrite Hk0, !Rmult_0_l.
    unfold R_dist. replace (0 - 0) with 0 by ring.
    rewrite Rabs_R0. exact Heps.
  - assert (Hkp : 0 < Rabs k) by (apply Rabs_pos_lt; exact Hk0).
    assert (Heps2 : 0 < eps / (2 * Rabs k)).
    { unfold Rdiv. apply Rmult_lt_0_compat; [exact Heps|].
      apply Rinv_0_lt_compat.
      apply Rmult_lt_0_compat; [lra | exact Hkp]. }
    destruct (Hcv (eps / (2 * Rabs k)) Heps2) as [N HN].
    exists N. intros n Hn. unfold R_dist in *.
    replace (k * U n - k * l) with (k * (U n - l)) by ring.
    rewrite Rabs_mult.
    apply Rlt_trans with (Rabs k * (eps / (2 * Rabs k))).
    + apply Rmult_lt_compat_l; [exact Hkp | exact (HN n Hn)].
    + assert (H2k : 2 * Rabs k <> 0)
        by (apply prod_neq_R0; [discrR | apply Rabs_no_R0; exact Hk0]).
      assert (Heq : Rabs k * (eps / (2 * Rabs k)) = eps / 2).
      { unfold Rdiv. field.
        all: try exact H2k; try discrR;
             try (apply Rabs_no_R0; exact Hk0);
             try (apply prod_neq_R0; [discrR | apply Rabs_no_R0; exact Hk0]). }
      rewrite Heq. lra.
Qed.

Lemma Un_cv_subseq : forall (U : nat -> R) (l : R) (g : nat -> nat),
  (forall m, (m <= g m)%nat) -> Un_cv U l -> Un_cv (fun m => U (g m)) l.
Proof.
  intros U l g Hg Hcv. unfold Un_cv. intros eps Heps.
  destruct (Hcv eps Heps) as [N HN]. exists N. intros m Hm.
  apply HN. apply Nat.le_trans with (m := m); [exact Hm | exact (Hg m)].
Qed.

(* ---- exp 级数桥（任意 x） ---- *)

Lemma exp_series_cv : forall x : R,
  Un_cv (fun n => sum_f_R0 (fun i => / INR (fact i) * x ^ i) n) (exp x).
Proof.
  intro x. unfold exp.
  assert (Hs : forall n,
    sum_f_R0 (fun i => / INR (Stdlib.Arith.Factorial.fact i) * x ^ i) n
    = sum_f_R0 (fun i => / INR (fact i) * x ^ i) n).
  { intro n. apply sum_f_R0_ext. intro i.
    rewrite <- fact_eq_stdlib. reflexivity. }
  pose proof (proj2_sig (exist_exp x)) as H.
  unfold exp_in, infinite_sum in H.
  unfold Un_cv. intros eps Heps.
  destruct (H eps Heps) as [N HN]. exists N. intros n Hn.
  rewrite <- (Hs n). apply HN. exact Hn.
Qed.

(* ---- exp_est（级数路线，正负两分支） ---- *)

Lemma exp_est_pos : forall x : R, 0 <= x -> x <= 1/2 ->
  0 <= exp x - 1 - x /\ exp x - 1 - x <= 2 * x ^ 2.
Proof.
  intros x Hx0 Hx1.
  set (S_ := fun n => sum_f_R0 (fun i => / INR (fact i) * x ^ i) n).
  assert (HcvS : Un_cv S_ (exp x)) by (apply exp_series_cv).
  assert (HcvV : Un_cv (fun n => S_ n - (1 + x)) (exp x - 1 - x)).
  { replace (exp x - 1 - x) with (exp x - (1 + x)) by ring.
    apply Un_cv_minus_const. exact HcvS. }
  assert (Htail : forall (m : nat), S_ ((2 + m)%nat) - (1 + x)
                  = sum_f_R0 (fun i => / INR (fact (2 + i)) * x ^ (2 + i)) m).
  { intro m. unfold S_.
    rewrite sum_f_R0_split_at_2. cbn beta.
    change (sum_f_R0 (fun i => / INR (fact i) * x ^ i) 1)
      with (/ (INR (fact 0)) * x ^ 0 + / (INR (fact 1)) * x ^ 1).
    assert (Hone : / (INR (fact 0)) * x ^ 0 = 1) by (simpl; field).
    assert (Hfone : / (INR (fact 1)) * x ^ 1 = x) by (simpl; field).
    rewrite Hone, Hfone. ring. }
  assert (Htnn : forall m,
    0 <= sum_f_R0 (fun i => / INR (fact (2 + i)) * x ^ (2 + i)) m).
  { intro m. apply sum_nonneg. intro i. unfold Rdiv.
    apply Rmult_le_pos; [| apply pow_le; exact Hx0].
    apply Rlt_le. apply Rinv_0_lt_compat. apply fact_pos. }
  assert (Hlo : 0 <= exp x - 1 - x).
  { apply (Un_cv_ge (fun m : nat => S_ ((2 + m)%nat) - (1 + x))).
    - apply Un_cv_subseq with (U := fun n => S_ n - (1 + x));
        [intro m; lia | exact HcvV].
    - intro m. rewrite Htail. apply Htnn. }
  assert (Htb : forall m,
    sum_f_R0 (fun i => / INR (fact (2 + i)) * x ^ (2 + i)) m <= x ^ 2).
  { intro m.
    assert (H1 : sum_f_R0 (fun i => / INR (fact (2 + i)) * x ^ (2 + i)) m
                <= sum_f_R0 (fun i => x ^ (2 + i) / 2) m).
    { apply sum_Rle. intros i _.
      assert (Hf2i : 2 <= INR (fact (2 + i))) by (apply INR_fact_ge_2; lia).
      unfold Rdiv.
      replace (x ^ (2 + i) * /2) with (/2 * x ^ (2 + i)) by ring.
      apply Rmult_le_compat_r; [apply pow_le; exact Hx0 |].
      apply Rinv_le_contravar; lra. }
    assert (H2 : sum_f_R0 (fun i => x ^ (2 + i) / 2) m
                = /2 * (x ^ 2 * sum_f_R0 (fun i => x ^ i) m)).
    { assert (Heq : forall i, x ^ (2 + i) / 2 = /2 * (x ^ 2 * x ^ i))
        by (intro i; unfold Rdiv; rewrite pow_add; ring).
      rewrite (sum_f_R0_ext (fun i => x ^ (2 + i) / 2)
                 (fun i => /2 * (x ^ 2 * x ^ i)) m Heq).
      rewrite sum_scal, sum_scal. reflexivity. }
    assert (H3 : sum_f_R0 (fun i => x ^ i) m <= 2)
      by (apply geom_sum_le_2; assumption).
    assert (Hx2 : 0 <= x ^ 2) by (apply pow_le; exact Hx0).
    assert (Hle2 : x ^ 2 * sum_f_R0 (fun i => x ^ i) m <= x ^ 2 * 2)
      by (apply Rmult_le_compat_l; [exact Hx2 | exact H3]).
    apply Rle_trans with (sum_f_R0 (fun i => x ^ (2 + i) / 2) m); [exact H1 |].
    rewrite H2.
    apply Rle_trans with (/2 * (x ^ 2 * 2)).
    - apply Rmult_le_compat_l; [lra | exact Hle2].
    - replace (x ^ 2 * 2) with (2 * x ^ 2) by ring.
      replace (/2 * (2 * x ^ 2)) with ((/2 * 2) * x ^ 2) by ring.
      replace (/2 * 2) with 1
        by (symmetry; rewrite Rmult_comm; apply Rinv_r; discrR).
      rewrite Rmult_1_l. apply Rle_refl. }
  assert (Hhi : exp x - 1 - x <= 2 * x ^ 2).
  { apply (Un_cv_le (fun m : nat => S_ ((2 + m)%nat) - (1 + x))).
    - apply Un_cv_subseq with (U := fun n => S_ n - (1 + x));
        [intro m; lia | exact HcvV].
    - intro m. rewrite Htail. apply Rle_trans with (x ^ 2); [apply Htb |].
      assert (Hx2 : 0 <= x ^ 2) by (apply pow_le; exact Hx0). lra. }
  split; [exact Hlo | exact Hhi].
Qed.

Lemma exp_est_series : forall x : R, Rabs x <= 1/2 ->
  Rabs (exp x - 1 - x) <= 2 * x ^ 2.
Proof.
  intros x Hx.
  assert (Habs : - (1/2) <= x <= 1/2).
  { destruct (Rle_lt_dec 0 x) as [Hge|Hlt].
    - assert (Hxr : Rabs x = x) by (apply Rabs_pos_eq; exact Hge).
      rewrite Hxr in Hx. lra.
    - assert (Hxr : Rabs x = - x) by (apply Rabs_left; lra).
      rewrite Hxr in Hx. lra. }
  destruct (Rle_lt_dec 0 x) as [Hx_ge0 | Hx_lt0].
  - destruct (exp_est_pos x Hx_ge0 (proj2 Habs)) as [Hlo Hhi].
    apply Rabs_le. split; [lra | exact Hhi].
  - set (u := - x).
    assert (Hu0 : 0 < u) by (unfold u; lra).
    assert (Hu1 : u <= 1/2) by (unfold u; lra).
    destruct (exp_est_pos u (Rlt_le _ _ Hu0) Hu1) as [Hlo Hhi].
    assert (Hexp_ge : 1 + u <= exp u) by lra.
    assert (Hexp_le : exp u <= 1 + u + 2 * u * u).
    { assert (Huu : u ^ 2 = u * u) by (simpl; ring).
      rewrite Huu in Hhi. lra. }
    assert (Hpos : 0 < exp u) by apply exp_pos.
    assert (Hne : exp u <> 0) by lra.
    assert (Heq : exp (- u) * exp u = 1).
    { rewrite <- exp_plus. replace (- u + u) with 0 by ring.
      rewrite exp_0. reflexivity. }
    replace x with (- u) by (unfold u; ring).
    assert (HN : exp (- u) - 1 - - u = (1 - (1 - u) * exp u) / exp u).
    { assert (HinvE : exp (- u) = / exp u).
      { rewrite <- (Rmult_1_r (exp (- u))).
        rewrite <- (Rinv_r (exp u) Hne).
        rewrite <- Rmult_assoc, Heq, Rmult_1_l. reflexivity. }
      rewrite HinvE. unfold Rdiv. field. exact Hne. }
    assert (HNum_bnd : Rabs (1 - (1 - u) * exp u) <= u * u).
    { apply Rabs_le. split.
      - assert (H1 : (1 - u) * exp u <= (1 - u) * (1 + u + 2 * u * u))
          by (apply Rmult_le_compat_l; [lra | lra]).
        assert (Hcalc : (1 - u) * (1 + u + 2 * u * u) = 1 + u * u * (1 - 2 * u))
          by ring.
        assert (Huu : 0 <= u * u) by (apply Rmult_le_pos; lra).
        assert (H12 : u * u * (1 - 2 * u) <= u * u * 1)
          by (apply Rmult_le_compat_l; [exact Huu | lra]).
        lra.
      - assert (H2 : (1 - u) * (1 + u) <= (1 - u) * exp u)
          by (apply Rmult_le_compat_l; [lra | lra]).
        assert (Hcalc2 : (1 - u) * (1 + u) = 1 - u * u) by ring.
        lra. }
    rewrite HN.
    unfold Rdiv.
    rewrite Rabs_mult.
    rewrite (Rabs_pos_eq (/ exp u)).
    2:{ apply Rlt_le. apply Rinv_0_lt_compat. exact Hpos. }
    apply Rle_trans with (u * u).
    + apply Rle_trans with (u * u * / exp u).
      * apply Rmult_le_compat_r;
          [apply Rlt_le, Rinv_0_lt_compat, Hpos | exact HNum_bnd].
      * apply Rle_trans with (u * u * 1).
        -- apply Rmult_le_compat_l;
             [apply Rmult_le_pos; [lra | lra] |].
           assert (Hge1 : 1 <= exp u) by lra.
           assert (Hinv1 : / exp u <= / 1)
             by (apply Rinv_le_contravar; lra).
           replace (/ 1) with 1 in Hinv1 by field.
           exact Hinv1.
        -- rewrite Rmult_1_r. apply Rle_refl.
    + replace ((- u) ^ 2) with (u * u) by (simpl; ring).
      lra.
Qed.

(* ---- sin 级数机器（交错配对法） ---- *)

Lemma pow_2_mult : forall (x : R) (n : nat), (x * x) ^ n = x ^ (2 * n).
Proof.
  intros x n. induction n as [|n IH].
  - reflexivity.
  - replace (2 * S n)%nat with (S (S (2 * n))) by lia.
    change ((x * x) ^ S n) with (x * x * (x * x) ^ n).
    rewrite IH.
    change (x ^ (S (S (2 * n)))) with (x * (x * x ^ (2 * n))).
    ring.
Qed.

Lemma pow_m1_even : forall k : nat, (-1 : R) ^ (2 * k) = 1.
Proof.
  induction k as [|k IH].
  - reflexivity.
  - replace (2 * S k)%nat with (2 * k + 2)%nat by lia.
    rewrite pow_add, IH. simpl. ring.
Qed.

Lemma pow_m1_odd : forall k : nat, (-1 : R) ^ (2 * k + 1) = -1.
Proof.
  intro k. rewrite pow_add, pow_m1_even. simpl. ring.
Qed.

Lemma sin_b_formula : forall (x : R) (j : nat),
  x * (sin_n (S j) * Rsqr x ^ S j)
  = - (-1) ^ j * (x ^ (2 * j + 3) / INR (fact (2 * j + 3))).
Proof.
  intros x j.
  unfold sin_n, Rsqr, Rdiv.
  rewrite <- (fact_eq_stdlib (2 * S j + 1)).
  replace (2 * S j + 1)%nat with (2 * j + 3)%nat by lia.
  change ((-1) ^ S j) with (-1 * (-1) ^ j).
  change ((x * x) ^ S j) with (x * x * (x * x) ^ j).
  rewrite pow_2_mult.
  rewrite (pow_add x (2 * j) 3).
  ring.
Qed.

Lemma sin_b_pos : forall (x : R) (i : nat), 0 <= x ->
  0 <= x ^ (2 * i + 3) / INR (fact (2 * i + 3)).
Proof.
  intros x i Hx0. unfold Rdiv.
  apply Rmult_le_pos; [apply pow_le; exact Hx0 |].
  apply Rlt_le. apply Rinv_0_lt_compat. apply fact_pos.
Qed.

Lemma sin_b_decr : forall (x : R) (i : nat), 0 <= x -> x <= 1/2 ->
  x ^ (2 * S i + 3) / INR (fact (2 * S i + 3))
  <= x ^ (2 * i + 3) / INR (fact (2 * i + 3)).
Proof.
  intros x i Hx0 Hx1.
  assert (Hstep : forall n, INR (fact (S n)) = INR (S n) * INR (fact n)).
  { intro n. change (fact (S n)) with (S n * fact n)%nat. apply mult_INR. }
  assert (HID : x ^ (2 * S i + 3) / INR (fact (2 * S i + 3))
                * INR ((2 * i + 4) * (2 * i + 5))
              = x ^ (2 * i + 3) / INR (fact (2 * i + 3)) * x ^ 2).
  { replace (2 * S i + 3)%nat with (S (S (2 * i + 3)))%nat by lia.
    rewrite Hstep, Hstep.
    replace ((2 * i + 4) * (2 * i + 5))%nat
      with (S (S (2 * i + 3)) * S (2 * i + 3))%nat by lia.
    rewrite mult_INR.
    replace (x ^ (S (S (2 * i + 3))))
      with (x ^ ((2 * i + 3) + 2)%nat).
    2:{ f_equal. lia. }
    rewrite pow_add.
    unfold Rdiv.
    field.
    split; [| split].
    - apply INR_fact_neq_0.
    - apply not_O_INR; discriminate.
    - apply not_O_INR; discriminate. }
  assert (Hb0 : 0 <= x ^ (2 * i + 3) / INR (fact (2 * i + 3)))
    by (apply sin_b_pos; exact Hx0).
  assert (HbS0 : 0 <= x ^ (2 * S i + 3) / INR (fact (2 * S i + 3)))
    by (apply sin_b_pos; exact Hx0).
  assert (Hxx : x ^ 2 <= 1 / 4).
  { replace (x ^ 2) with (x * x) by (simpl; ring).
    replace (1 / 4) with ((1/2) * (1/2)) by (field; try discrR).
    apply Rmult_le_compat; lra. }
  assert (HD : 4 <= INR ((2 * i + 4) * (2 * i + 5))).
  { assert (Hc : (4:R) = INR 4) by (simpl; ring).
    rewrite Hc.
    apply le_INR.
    assert (Hm : (4 <= 2 * i + 4)%nat) by lia.
    assert (Hone : (1 <= 2 * i + 5)%nat) by lia.
    nia. }
  assert (Hkey : x ^ (2 * S i + 3) / INR (fact (2 * S i + 3)) * 4
               <= x ^ (2 * i + 3) / INR (fact (2 * i + 3))).
  { assert (Hle1 : x ^ (2 * i + 3) / INR (fact (2 * i + 3)) * x ^ 2
                 <= x ^ (2 * i + 3) / INR (fact (2 * i + 3)) * (1 / 4))
      by (apply Rmult_le_compat_l; [exact Hb0 | exact Hxx]).
    set (bS := x ^ (2 * S i + 3) / INR (fact (2 * S i + 3))) in *.
    set (bI := x ^ (2 * i + 3) / INR (fact (2 * i + 3))) in *.
    set (D := INR ((2 * i + 4) * (2 * i + 5))) in *.
    assert (H1 : bS * 4 <= 4 * (bS * D)).
    { apply Rle_trans with (4 * bS).
      - rewrite (Rmult_comm bS 4). apply Rle_refl.
      - apply Rmult_le_compat_l; [lra |].
        apply Rle_trans with (bS * 1);
          [rewrite Rmult_1_r; apply Rle_refl
          | apply Rmult_le_compat_l; [exact HbS0 | lra]]. }
    rewrite HID in H1.
    assert (H3 : 4 * (bI * x ^ 2) <= 4 * (bI * (1 / 4)))
      by (apply Rmult_le_compat_l; [lra | exact Hle1]).
    assert (H4 : 4 * (bI * (1 / 4)) <= bI).
    { unfold Rdiv.
      replace (4 * (bI * (1 * /4))) with (bI * (4 * (1 * /4))) by ring.
      replace (4 * (1 * /4)) with (4 * /4) by ring.
      rewrite Rinv_r by discrR.
      rewrite Rmult_1_r. apply Rle_refl. }
    apply Rle_trans with (4 * (bI * x ^ 2)); [exact H1 |].
    apply Rle_trans with (4 * (bI * (1 / 4))); [exact H3 | exact H4]. }
  set (bS2 := x ^ (2 * S i + 3) / INR (fact (2 * S i + 3))).
  apply Rle_trans with (bS2 * 4).
  - assert (Hs1 : bS2 * 1 <= bS2 * 4)
      by (apply Rmult_le_compat_l; [exact HbS0 | lra]).
    lra.
  - exact Hkey.
Qed.

Lemma sin_series_bounds : forall x : R, 0 <= x -> x <= 1/2 ->
  0 <= x - sin x /\ x - sin x <= x ^ 3 / 6.
Proof.
  intros x Hx0 Hx1.
  unfold sin.
  destruct (exist_sin (Rsqr x)) as [a Ha].
  cbn beta iota.
  set (R_ := fun n => sum_f_R0 (fun i => sin_n i * Rsqr x ^ i) n).
  set (b := fun i => x ^ (2 * i + 3) / INR (fact (2 * i + 3))).
  set (Q := fun m => sum_f_R0 (fun i => b ((2 * i)%nat) - b ((2 * i + 1)%nat)) m).
  assert (HRcv : Un_cv R_ a).
  { unfold R_. unfold sin_in, infinite_sum in Ha. exact Ha. }
  assert (Hxt : forall j, - x * (sin_n (S j) * Rsqr x ^ S j) = (-1) ^ j * b j).
  { intro j. unfold b.
    pose proof (sin_b_formula x j) as H. lra. }
  assert (Hbridge : forall (m : nat), x * (1 - R_ ((2 * m + 2)%nat)) = Q m).
  { intro m. induction m as [|m IH].
    - unfold Q, R_.
      change (2 * 0 + 2)%nat with (S (S 0)).
      rewrite !sum_snoc. cbn beta.
      assert (Hf0 : sin_n 0 * Rsqr x ^ 0 = 1) by (unfold sin_n; simpl; field).
      change (sum_f_R0 (fun i : nat => sin_n i * Rsqr x ^ i) 0)
        with (sin_n 0 * Rsqr x ^ 0).
      rewrite Hf0.
      replace (x * (1 - (1 + sin_n 1 * Rsqr x ^ 1 + sin_n 2 * Rsqr x ^ 2)))
        with (- x * (sin_n 1 * Rsqr x ^ 1)
              + - x * (sin_n 2 * Rsqr x ^ 2)) by ring.
      rewrite (Hxt 0%nat), (Hxt 1%nat).
      simpl. ring.
    - unfold Q, R_.
      replace (2 * S m + 2)%nat with (S (S ((2 * m + 2)%nat))) by lia.
      rewrite !sum_snoc. cbn beta.
      change (sum_f_R0 (fun i : nat => sin_n i * Rsqr x ^ i) ((2 * m + 2)%nat))
        with (R_ ((2 * m + 2)%nat)).
      change (sum_f_R0 (fun i : nat => b (2 * i)%nat - b (2 * i + 1)%nat) m)
        with (Q m).
      replace (x * (1 - (R_ ((2 * m + 2)%nat)
                          + sin_n (S ((2 * m + 2)%nat))
                              * Rsqr x ^ S ((2 * m + 2)%nat)
                          + sin_n (S (S ((2 * m + 2)%nat)))
                              * Rsqr x ^ S (S ((2 * m + 2)%nat)))))
        with (x * (1 - R_ ((2 * m + 2)%nat))
              + (- x * (sin_n (S ((2 * m + 2)%nat))
                        * Rsqr x ^ S ((2 * m + 2)%nat))
                 + - x * (sin_n (S (S ((2 * m + 2)%nat)))
                          * Rsqr x ^ S (S ((2 * m + 2)%nat))))) by ring.
      rewrite IH.
      rewrite (Hxt ((2 * m + 2)%nat)), (Hxt (S ((2 * m + 2)%nat))).
      assert (Hs1 : (-1 : R) ^ (2 * m + 2) = 1)
        by (replace (2 * m + 2)%nat with (2 * (m + 1))%nat by lia;
            apply pow_m1_even).
      assert (Hs2 : (-1 : R) ^ (S (2 * m + 2)) = -1)
        by (replace (S (2 * m + 2))%nat with (2 * (m + 1) + 1)%nat by lia;
            apply pow_m1_odd).
      rewrite Hs1, Hs2.
      replace (2 * S m + 1)%nat with (2 * m + 3)%nat by lia.
      replace (S ((2 * m + 2)%nat)) with ((2 * m + 3)%nat) by lia.
      replace (2 * S m)%nat with (2 * m + 2)%nat by lia.
      ring. }
  assert (Hqeq : (fun m : nat => x * (1 - R_ ((2 * m + 2)%nat))) = Q)
    by (apply functional_extensionality; intro m; apply Hbridge).
  assert (Hcv1 : Un_cv (fun n => 1 - R_ n) (1 - a)).
  { unfold Un_cv. intros eps Heps.
    destruct (HRcv eps Heps) as [N HN]. exists N. intros n Hn.
    unfold R_dist in *.
    replace (1 - R_ n - (1 - a)) with (- (R_ n - a)) by ring.
    rewrite Rabs_Ropp. apply HN. exact Hn. }
  assert (Hcv2 : Un_cv (fun n => x * (1 - R_ n)) (x * (1 - a)))
    by (apply Un_cv_scal; exact Hcv1).
  assert (Hcv3 : Un_cv (fun m : nat => x * (1 - R_ ((2 * m + 2)%nat))) (x * (1 - a)))
    by (apply Un_cv_subseq with (U := fun n => x * (1 - R_ n));
        [intro m; lia | exact Hcv2]).
  rewrite Hqeq in Hcv3.
  assert (Hc_nn : forall i, 0 <= b ((2 * i)%nat) - b ((2 * i + 1)%nat)).
  { intro i.
    assert (Hd : b ((2 * i + 1)%nat) <= b ((2 * i)%nat)).
    { unfold b. pose proof (sin_b_decr x ((2 * i)%nat) Hx0 Hx1) as H.
      replace (2 * S ((2 * i)%nat) + 3)%nat with (2 * (2 * i + 1) + 3)%nat in H by lia.
      exact H. }
    lra. }
  assert (HQ_nn : forall m, 0 <= Q m) by (intro; apply sum_nonneg; exact Hc_nn).
  assert (HQ_main : forall m, Q m + b ((2 * m + 1)%nat) <= b 0%nat).
  { intro m. induction m as [|m IH].
    - unfold Q. simpl. lra.
    - unfold Q. rewrite sum_snoc. cbn beta.
      change (sum_f_R0 (fun i : nat => b (2 * i)%nat - b (2 * i + 1)%nat) m)
        with (Q m).
      replace (2 * S m + 1)%nat with (2 * m + 3)%nat by lia.
      replace (S ((2 * m + 2)%nat)) with ((2 * m + 3)%nat) by lia.
      replace (2 * S m)%nat with (2 * m + 2)%nat by lia.
      assert (Hd2 : b ((2 * m + 2)%nat) <= b ((2 * m + 1)%nat)).
      { unfold b. pose proof (sin_b_decr x ((2 * m + 1)%nat) Hx0 Hx1) as Hd.
        replace (2 * S ((2 * m + 1)%nat) + 3)%nat
          with (2 * (2 * m + 2) + 3)%nat in Hd by lia.
        exact Hd. }
      lra. }
  assert (HQ_le : forall m, Q m <= b 0%nat).
  { intro m. specialize (HQ_main m).
    assert (Hbn : 0 <= b ((2 * m + 1)%nat)) by (unfold b; apply sin_b_pos; exact Hx0).
    lra. }
  assert (Hlo : 0 <= x - x * a).
  { replace (x - x * a) with (x * (1 - a)) by ring.
    apply (Un_cv_ge Q); [exact Hcv3 | exact HQ_nn]. }
  assert (Hhi : x - x * a <= b 0%nat).
  { replace (x - x * a) with (x * (1 - a)) by ring.
    apply (Un_cv_le Q); [exact Hcv3 | exact HQ_le]. }
  assert (Hb0 : b 0%nat = x ^ 3 / 6) by (unfold b; simpl; field).
  split; [exact Hlo |].
  rewrite <- Hb0. exact Hhi.
Qed.

Lemma sin_est_series : forall y : R, Rabs y <= 1/2 ->
  Rabs (sin y - y) <= (Rabs y) ^ 3 / 6.
Proof.
  intros y Hy.
  assert (Habs : - (1/2) <= y <= 1/2).
  { destruct (Rle_lt_dec 0 y) as [Hge|Hlt].
    - assert (Hyr : Rabs y = y) by (apply Rabs_pos_eq; exact Hge).
      rewrite Hyr in Hy. lra.
    - assert (Hyr : Rabs y = - y) by (apply Rabs_left; lra).
      rewrite Hyr in Hy. lra. }
  destruct (Rle_lt_dec 0 y) as [Hy0 | Hy0].
  - destruct (sin_series_bounds y Hy0 (proj2 Habs)) as [Hlo Hhi].
    rewrite (Rabs_pos_eq y Hy0).
    replace (sin y - y) with (- (y - sin y)) by ring.
    rewrite Rabs_Ropp, (Rabs_pos_eq (y - sin y) Hlo).
    exact Hhi.
  - set (x := - y).
    assert (Hx0 : 0 < x) by (unfold x; lra).
    assert (Hx1 : x <= 1/2) by (unfold x; lra).
    destruct (sin_series_bounds x (Rlt_le _ _ Hx0) Hx1) as [Hlo Hhi].
    replace (sin y - y) with (x - sin x)
      by (unfold x; rewrite sin_neg; ring).
    replace ((Rabs y) ^ 3) with (x ^ 3).
    + rewrite (Rabs_pos_eq (x - sin x) Hlo).
      apply Hhi.
    + assert (Hax : Rabs y = x).
      { unfold x. rewrite (Rabs_left y) by lra. ring. }
      rewrite Hax. reflexivity.
Qed.

(* |sin t| <= |t|（构造性，由交错级数界直接推出） *)
Lemma sin_le_abs : forall t : R, Rabs t <= 1/2 -> Rabs (sin t) <= Rabs t.
Proof.
  assert (Hpos : forall u, 0 <= u -> u <= 1/2 -> Rabs (sin u) <= u).
  { intros u Hu0 Hu1.
    destruct (sin_series_bounds u Hu0 Hu1) as [Hlo Hhi].
    assert (H3 : u ^ 3 <= u).
    { replace (u ^ 3) with (u * (u * u)) by (simpl; ring).
      assert (Huu : u * u <= 1).
      { replace 1 with (1 * 1) by ring.
        apply Rmult_le_compat; lra. }
      apply Rle_trans with (u * 1).
      - apply Rmult_le_compat_l; [exact Hu0 | exact Huu].
      - rewrite Rmult_1_r. apply Rle_refl. }
    apply Rabs_le. split; lra. }
  intros t Ht.
  destruct (Rle_lt_dec 0 t) as [Hge|Hlt].
  - rewrite (Rabs_pos_eq t Hge). apply Hpos; [exact Hge |].
    rewrite (Rabs_pos_eq t Hge) in Ht. exact Ht.
  - rewrite (Rabs_left t) by lra.
    replace (sin t) with (- sin (- t)) by (rewrite sin_neg; ring).
    rewrite Rabs_Ropp.
    apply Hpos; [lra |].
    rewrite (Rabs_left t) in Ht by lra. exact Ht.
Qed.

(* exp 1 不大于3（第三种证法） *)

(* 常数函数1在任意点可导（简证） *)

(* 常数函数1在任意点可导 *)
Lemma derivable_pt_const_1 : forall t : R, derivable_pt (fun _ : R => 1) t.
Proof.
  intro t.
  exists 0.
  unfold derivable_pt_lim.
  intros eps Heps.
  assert (Hpos : 0 < 1) by lra.
  exists (mkposreal 1 Hpos).
  intros h Hh_neq0 Hh_abs.
  replace (1 - 1) with 0 by ring.
  unfold Rdiv.
  rewrite Rmult_0_l.
  rewrite Rminus_0_r.
  rewrite Rabs_R0.
  exact Heps.
Qed.

(* 常数函数可导 *)
Lemma derivable_pt_const : forall (c t : R), derivable_pt (fun _ => c) t.
Proof.
  intros c t.
  exists 0.
  unfold derivable_pt_lim.
  intros eps Heps.
  exists (mkposreal 1 Rlt_0_1).
  intros h Hh_neq0 Hh_abs.
  unfold Rdiv.
  replace (c - c) with 0 by ring.
  rewrite Rmult_0_l.
  rewrite Rminus_0_r.
  rewrite Rabs_R0.
  exact Heps.
Qed.

(* 0小于1 *)
Lemma zero_lt_one : 0 < 1.
Proof. lra. Qed.

(* 常数函数可导（简化） *)
Lemma derivable_pt_const_simple (c : R) : forall t : R, derivable_pt (fun _ : R => c) t.
Proof.
  intros t.
  exists 0.
  unfold derivable_pt_lim.
  intros eps Heps.
  exists (mkposreal 1 zero_lt_one).
  intros h Hh_neq0 Hh_abs.
  unfold Rdiv.
  replace (c - c) with 0 by ring.
  rewrite Rmult_0_l.
  rewrite Rminus_0_r.
  rewrite Rabs_R0.
  exact Heps.
Qed.

(* 常数函数1在任意点可导（最终版） *)

(* 平方函数除以2可导 *)
Lemma derivable_pt_sq_div2 : forall t : R, derivable_pt (fun u : R => u^2 / 2) t.
Proof.
  intro t.
  apply derivable_pt_div.
  - apply derivable_pt_pow.
  - apply derivable_pt_const_simple.
  - intro H.
    lra.
Qed.

(* 多项式P(t)=1+t+t^2/2可导 *)
Lemma derivable_pt_P : forall t : R, derivable_pt (fun u : R => 1 + u + u^2/2) t.
Proof.
  intro t.
  apply derivable_pt_plus.
  - apply derivable_pt_plus.
    + apply derivable_pt_const_simple.
    + apply derivable_pt_id.
  - apply derivable_pt_sq_div2.
Qed.

(* M乘以t^3可导 *)
Lemma derivable_pt_M_t3 : forall (M t : R), derivable_pt (fun u : R => M * u^3) t.
Proof.
  intros M t.
  apply derivable_pt_mult.
  - apply derivable_pt_const_simple.
  - apply derivable_pt_pow.
Qed.

(* 部分和比较引理 *)
Lemma sum_Rle : forall (f g : nat -> R) (n : nat),
    (forall i, (i <= n)%nat -> f i <= g i) ->
    sum_f_R0 f n <= sum_f_R0 g n.
Proof.
  intros f g n H.
  induction n as [|n IH].
  - simpl. apply H. lia.
  - rewrite !sum_f_R0_S.
    apply Rplus_le_compat.
    + apply IH.
      intros i Hi. apply H. lia.
    + apply H. lia.
Qed.

(* 常数序列的部分和公式 *)
Lemma sum_f_R0_const : forall (c : R) (n : nat),
    sum_f_R0 (fun k => c) n = c * INR (S n).
Proof.
  intros c n.
  induction n as [|n IH].
  - simpl.
    rewrite Rmult_1_r.
    reflexivity.
  - simpl.
    rewrite IH.
    replace (INR (S (S n))) with (INR (S n) + 1).
    + rewrite Rmult_plus_distr_l.
      rewrite Rmult_1_r.
      reflexivity.
    + rewrite (S_INR (S n)).
      reflexivity.
Qed.

(* 部分和的外延相等 *)
Lemma sum_f_R0_ext : forall (f g : nat -> R) (n : nat),
    (forall i, f i = g i) ->
    sum_f_R0 f n = sum_f_R0 g n.
Proof.
  intros f g n H.
  induction n as [|n IH].
  - simpl. apply H.
  - rewrite !sum_f_R0_S. rewrite H. rewrite IH. reflexivity.
Qed.

(* 构造辅助函数并验证边界条件 *)
Lemma construct_aux_function (x : R) (Hx_pos : 0 < x) (Hx_high : x <= 1) :
  let A := exp x - (1 + x + x^2/2) in
  let h := fun t : R => exp t - (1 + t + t^2/2) - A * (t/x)^3 in
  h 0 = 0 /\ h x = 0.
Proof.
  intros A h.
  assert (Hx_neq0 : x <> 0) by lra.
  split.
  - unfold h, A.
    rewrite exp_0.
    replace (0 ^ 2) with 0 by ring.
    replace (0 / 2) with 0 by field.
    replace (0 / x) with 0 by (field; lra).
    replace (0 ^ 3) with 0 by ring.
    ring.
  - unfold h, A.
    replace (x / x) with 1 by (field; lra).
    replace (1 ^ 3) with 1 by ring.
    ring.
Qed.

(* 辅助函数在区间上可导 *)
Lemma aux_function_derivable (x : R) (Hx_pos : 0 < x) (Hx_high : x <= 1) :
  let A := exp x - (1 + x + x^2/2) in
  let h := fun t : R => exp t - (1 + t + t^2/2) - A * (t/x)^3 in
  forall t, 0 <= t <= x -> derivable_pt h t.
Proof.
  intros A h t Ht.
  assert (Hx_neq0 : x <> 0) by lra.
  unfold h, A.
  apply derivable_pt_minus.
  - apply derivable_pt_minus.
    + apply derivable_pt_exp.
    + apply derivable_pt_P.
  - apply derivable_pt_mult.
    + apply derivable_pt_const.
    + assert (Hdiv_derivable : derivable_pt (fun u => u / x) t).
      {
        apply derivable_pt_div.
        - apply derivable_pt_id.
        - apply derivable_pt_const.
        - exact Hx_neq0.
      }
      assert (Hpow_derivable : derivable_pt (fun u => u^3) (t/x)).
      {
        apply derivable_pt_pow.
      }
      exact (derivable_pt_comp (fun u => u / x) (fun u => u^3) t Hdiv_derivable Hpow_derivable).
Qed.

(* 辅助函数在开区间内可导 *)
Lemma aux_function_derivable_open (x : R) (Hx_pos : 0 < x) (Hx_high : x <= 1) :
  let A := exp x - (1 + x + x^2/2) in
  let h := fun t : R => exp t - (1 + t + t^2/2) - A * (t/x)^3 in
  forall t, 0 < t < x -> derivable_pt h t.
Proof.
  intros A h t Ht.
  destruct Ht as [Ht_left Ht_right].
  assert (Hx_neq0 : x <> 0) by lra.
  unfold h, A.
  apply derivable_pt_minus.
  - apply derivable_pt_minus.
    + apply derivable_pt_exp.
    + apply derivable_pt_P.
  - apply derivable_pt_mult.
    + apply derivable_pt_const.
    + assert (Hdiv_derivable : derivable_pt (fun u => u / x) t).
      {
        apply derivable_pt_div.
        - apply derivable_pt_id.
        - apply derivable_pt_const.
        - exact Hx_neq0.
      }
      assert (Hpow_derivable : derivable_pt (fun u => u^3) (t/x)).
      {
        apply derivable_pt_pow.
      }
      exact (derivable_pt_comp (fun u => u / x) (fun u => u^3) t Hdiv_derivable Hpow_derivable).
Qed.

(* 辅助函数在区间上连续 *)
Lemma aux_function_continuous (x : R) (Hx_pos : 0 < x) (Hx_high : x <= 1) :
  let A := exp x - (1 + x + x^2/2) in
  let h := fun t : R => exp t - (1 + t + t^2/2) - A * (t/x)^3 in
  forall t, 0 <= t <= x -> continuity_pt h t.
Proof.
  intros A h t Ht.
  assert (Hx_neq0 : x <> 0) by lra.
  unfold h, A.
  apply derivable_continuous_pt.
  apply derivable_pt_minus.
  - apply derivable_pt_minus.
    + apply derivable_pt_exp.
    + apply derivable_pt_P.
  - apply derivable_pt_mult.
    + apply derivable_pt_const.
    + assert (Hdiv_derivable : derivable_pt (fun u => u / x) t).
      {
        apply derivable_pt_div.
        - apply derivable_pt_id.
        - apply derivable_pt_const.
        - exact Hx_neq0.
      }
      assert (Hpow_derivable : derivable_pt (fun u => u^3) (t/x)).
      {
        apply derivable_pt_pow.
      }
      exact (derivable_pt_comp (fun u => u / x) (fun u => u^3) t Hdiv_derivable Hpow_derivable).
Qed.

(* 定理：指数函数三阶泰勒展开 *)
Theorem exp_taylor_3_direct (x : R) (Hx : 0 <= x <= 1) :
  exists ξ, 0 <= ξ <= x /\ exp x = 1 + x + x^2/2 + exp ξ * x^3/6.
Proof.
  destruct Hx as [Hx_low Hx_high].
  
  destruct (Req_EM_T x 0) as [Hx0 | Hx_neq0].
  { subst x. exists 0. split; [split; lra |]. rewrite exp_0. compute; lra. }
  
  assert (Hx_pos : 0 < x) by lra.
  
  set (A := exp x - (1 + x + x^2/2)).
  set (h := fun t : R => exp t - (1 + t + t^2/2) - A * (t / x)^3).
  
  assert (Hx_neq0' : x <> 0) by lra.
  assert (Hh0 : h 0 = 0).
  { unfold h, A. rewrite exp_0.
    replace (0^2) with 0 by ring.
    replace (0/2) with 0 by field.
    replace (0/x) with 0 by (field; lra).
    replace (0^3) with 0 by ring.
    ring. }
  assert (Hhx : h x = 0).
  { unfold h, A.
    replace (x / x) with 1 by (field; lra).
    replace (1^3) with 1 by ring.
    ring. }
  
  assert (Hder_h : forall t, 0 <= t <= x -> derivable_pt h t).
  { intros t Ht. unfold h, A.
    apply derivable_pt_minus.
    - apply derivable_pt_minus.
      + apply derivable_pt_exp.
      + apply derivable_pt_P.
    - apply derivable_pt_mult.
      + apply derivable_pt_const.
      + assert (Hdiv_derivable : derivable_pt (fun u => u / x) t).
        { apply derivable_pt_div.
          - apply derivable_pt_id.
          - apply derivable_pt_const.
          - exact Hx_neq0'. }
        assert (Hpow_derivable : derivable_pt (fun u => u^3) (t/x)).
        { apply derivable_pt_pow. }
        exact (derivable_pt_comp (fun u => u / x) (fun u => u^3) t
                Hdiv_derivable Hpow_derivable). }
  
  assert (Hder_open : forall t, 0 < t < x -> derivable_pt h t).
  { intros t Ht. apply Hder_h. split; lra. }
  
  assert (Hcont_01 : forall t, 0 <= t <= x -> continuity_pt h t).
  { intros t Ht. apply derivable_continuous_pt, Hder_h; exact Ht. }
  
  assert (Heq : h 0 = h x) by (rewrite Hh0, Hhx; reflexivity).
  
  destruct (Rolle_simple h 0 x Hx_pos Hcont_01 Hder_open Heq)
    as [ξ1 [Hξ1 Hder_h_ξ1]].
  destruct Hξ1 as [Hξ1_low Hξ1_high].
  
  assert (h_derive_eq : forall t (D : derivable_pt h t),
            derive_pt h t D = exp t - (1 + t) - 3 * A * t^2 / x^3).
  { intros t D. unfold h, A.
    replace (A * (t / x) ^ 3) with (A / x^3 * t ^ 3).
    2: { assert (x <> 0) by lra; field; lra. }
    replace (t ^ 2 / 2) with (1/2 * t ^ 2) by (field; lra).
  
    assert (H_exp   : derivable_pt_lim exp t (exp t))
      by apply derivable_pt_lim_exp.
    assert (H_const1: derivable_pt_lim (fun _ => 1) t 0)
      by apply derivable_pt_lim_const.
    assert (H_id    : derivable_pt_lim (fun x0 => x0) t 1)
      by apply derivable_pt_lim_id.
    assert (H_plus1 : derivable_pt_lim (fun x0 => 1 + x0) t (0 + 1)).
    { apply derivable_pt_lim_plus; [exact H_const1 | exact H_id]. }
    replace (0+1) with 1 in H_plus1 by ring.
  
    assert (H_sq    : derivable_pt_lim (fun x0 => x0^2) t (2 * t)).
    { pose proof (derivable_pt_lim_pow t 2%nat) as H.
      simpl in H; rewrite Rmult_1_r in H; exact H. }
    assert (H_sq_div2 : derivable_pt_lim (fun x0 => x0^2 / 2) t t).
    { replace (fun x0 => x0^2 / 2) with (fun x0 => (1/2) * x0^2).
      2: { apply functional_extensionality; intro; unfold Rdiv; ring. }
      assert (H_const_half : derivable_pt_lim (fun _ => 1/2) t 0)
        by apply derivable_pt_lim_const.
      pose proof (derivable_pt_lim_mult (fun _ => 1/2) (fun x0 => x0^2) t 0 (2*t)
                  H_const_half H_sq) as Hmult.
      simpl in Hmult; rewrite Rmult_0_l, Rplus_0_l in Hmult.
      replace (1/2 * (2 * t)) with t in Hmult by (field; lra); exact Hmult. }
    assert (H_cube  : derivable_pt_lim (fun x0 => x0^3) t (3 * t^2)).
    { pose proof (derivable_pt_lim_pow t 3%nat) as H.
      replace (INR 3) with 3 in H.
      - replace (t ^ pred 3) with (t ^ 2) in H.
        + exact H.
        + unfold pred; simpl; reflexivity.
      - rewrite INR_IZR_INZ; simpl; reflexivity. }
    assert (H_cube_scaled : derivable_pt_lim (fun x0 => A / x^3 * x0^3) t
                                              (A / x^3 * (3 * t^2))).
    { apply derivable_pt_lim_scal with (a := A / x^3); exact H_cube. }
    assert (H_poly : derivable_pt_lim (fun x0 => 1 + x0 + x0^2/2) t (1 + t)).
    { apply derivable_pt_lim_plus; [exact H_plus1 | exact H_sq_div2]. }
    assert (H_minus1 : derivable_pt_lim (fun x0 => exp x0 - (1 + x0 + x0^2/2)) t
                                         (exp t - (1 + t))).
    { apply derivable_pt_lim_minus; [exact H_exp | exact H_poly]. }
    assert (H_cube_scaled' : derivable_pt_lim (fun t0 => A * (t0 / x) ^ 3) t
                                               (3 * A * t^2 / x^3)).
    { replace (fun t0 => A * (t0 / x) ^ 3) with (fun t0 => A / x^3 * t0 ^ 3).
      2: { apply functional_extensionality; intros; unfold Rdiv; field; lra. }
      replace (A / x^3 * (3 * t^2)) with (3 * A * t^2 / x^3) in H_cube_scaled
        by (field; lra).
      exact H_cube_scaled. }
    assert (H_h_lim : derivable_pt_lim h t (exp t - (1 + t) - 3 * A * t^2 / x^3)).
    { unfold h; apply derivable_pt_lim_minus;
        [exact H_minus1 | exact H_cube_scaled']. }
    apply derive_pt_eq_0 with (l := exp t - (1 + t) - 3 * A * t^2 / x^3);
      exact H_h_lim.
  }
  
  assert (Hder0 : derivable_pt h 0) by (apply Hder_h; split; lra).
  assert (Hh'_0 : derive_pt h 0 Hder0 = 0).
  { rewrite h_derive_eq with (t := 0) (D := Hder0).
    rewrite exp_0. simpl.
    assert (Hx3_nonzero : x ^ 3 <> 0) by (apply pow_nonzero; lra).
    field; lra. }
  
  set (g := fun t => exp t - (1 + t) - 3 * A * t^2 / x^3).
  
  assert (Hh'_eq_g : forall t (D : derivable_pt h t) (Ht : 0 <= t <= x),
            derive_pt h t D = g t).
  { intros; rewrite h_derive_eq; auto. }
  
  assert (Hx3_nonzero : x ^ 3 <> 0) by (apply pow_nonzero; lra).
  assert (g_der : forall t, 0 < t < ξ1 -> derivable_pt g t).
  { intros t Ht. unfold g.
    apply derivable_pt_minus.
    - apply derivable_pt_minus.
      + apply derivable_pt_exp.
      + apply derivable_pt_plus.
        * apply derivable_pt_const.
        * apply derivable_pt_id.
    - replace (fun t0 => 3 * A * t0 ^ 2 / x ^ 3)
         with (fun t0 => (3 * A / x ^ 3) * t0 ^ 2).
      2: { apply functional_extensionality; intros y;
             unfold Rdiv; field; lra. }
      apply derivable_pt_scal.
      apply (derivable_pt_pow 2%nat t). }
  
  assert (g_cont : forall t, 0 <= t <= ξ1 -> continuity_pt g t).
  { intros t Ht. unfold g.
    apply continuity_pt_minus.
    - apply continuity_pt_minus.
      + apply derivable_continuous_pt, derivable_pt_exp.
      + apply continuity_pt_plus.
        * apply derivable_continuous_pt, derivable_pt_const.
        * apply derivable_continuous_pt, derivable_pt_id.
    - apply derivable_continuous_pt.
      replace (fun t0 => 3 * A * t0 ^ 2 / x ^ 3)
         with (fun t0 => (3 * A / x ^ 3) * t0 ^ 2).
      + apply derivable_pt_scal with (a := 3 * A / x ^ 3).
        apply (derivable_pt_pow 2%nat t).
      + apply functional_extensionality; intros y;
          unfold Rdiv; field; lra. }
  
  assert (g_0 : g 0 = 0).
  { unfold g. rewrite exp_0. field; try exact Hx3_nonzero; lra. }
  
  assert (g_derive_eq : forall t (D : derivable_pt g t),
            derive_pt g t D = exp t - 1 - 6 * A * t / x ^ 3).
  { intros t D.
    apply derive_pt_eq.
    unfold g.
    apply derivable_pt_lim_minus.
    - apply derivable_pt_lim_minus.
      + apply derivable_pt_lim_exp.
      + assert (H_plus : derivable_pt_lim (fun x => 1 + x) t (0 + 1)).
        { apply derivable_pt_lim_plus;
          [apply derivable_pt_lim_const | apply derivable_pt_lim_id]. }
        replace (0+1) with 1 in H_plus by ring; exact H_plus.
    - replace (fun t0 => 3 * A * t0 ^ 2 / x ^ 3)
         with (fun t0 => (3 * A / x ^ 3) * t0 ^ 2).
      + assert (Hpow : derivable_pt_lim (fun y => y ^ 2) t (2 * t)).
        { pose proof (derivable_pt_lim_pow t 2%nat) as Hpow_raw.
          simpl in Hpow_raw; rewrite Rmult_1_r in Hpow_raw; exact Hpow_raw. }
        assert (Hscal : derivable_pt_lim (fun y => (3 * A / x ^ 3) * y ^ 2) t
                                        ((3 * A / x ^ 3) * (2 * t))).
        { apply derivable_pt_lim_scal with (a := 3 * A / x ^ 3); exact Hpow. }
        replace ((3 * A / x ^ 3) * (2 * t)) with (6 * A * t / x ^ 3) in Hscal
          by (field; lra).
        exact Hscal.
      + apply functional_extensionality; intros y;
          unfold Rdiv; field; lra. }
  
  assert (g_ξ1 : g ξ1 = 0).
  { unfold g.
    rewrite <- h_derive_eq with (t := ξ1)
        (D := Hder_open ξ1 (conj Hξ1_low Hξ1_high)).
    exact Hder_h_ξ1. }
  
  assert (Heq_g : g 0 = g ξ1) by (rewrite g_0, g_ξ1; reflexivity).
  destruct (Rolle_simple g 0 ξ1 Hξ1_low g_cont g_der Heq_g)
    as [ξ2 [Hξ2 Hder_g_ξ2]].
  destruct Hξ2 as [Hξ2_low Hξ2_high].
  
  set (g' := fun t => exp t - 1 - 6 * A * t / x ^ 3).
  
  assert (g'_cont : forall t, 0 <= t <= ξ2 -> continuity_pt g' t).
  { intros t Ht. apply derivable_continuous_pt.
    unfold g'.
    apply derivable_pt_minus.
    - apply derivable_pt_minus.
      + apply derivable_pt_exp.
      + apply derivable_pt_const.
    - replace (fun t0 => 6 * A * t0 / x ^ 3)
         with (fun t0 => (6 * A / x ^ 3) * t0).
      2: { apply functional_extensionality; intros y;
             unfold Rdiv; field; lra. }
      apply derivable_pt_scal with (a := 6 * A / x ^ 3).
      apply derivable_pt_id. }
  
  assert (g'_der : forall t, 0 < t < ξ2 -> derivable_pt g' t).
  { intros t Ht.
    unfold g'.
    apply derivable_pt_minus.
    - apply derivable_pt_minus.
      + apply derivable_pt_exp.
      + apply derivable_pt_const.
    - replace (fun t0 => 6 * A * t0 / x ^ 3)
         with (fun t0 => (6 * A / x ^ 3) * t0).
      2: { apply functional_extensionality; intros y;
             unfold Rdiv; field; lra. }
      apply derivable_pt_scal with (a := 6 * A / x ^ 3).
      apply derivable_pt_id. }
  
  assert (g'_0 : g' 0 = 0).
  { unfold g'. rewrite exp_0. field; try exact Hx3_nonzero; lra. }
  assert (g'_ξ2 : g' ξ2 = 0).
  { unfold g'.
    rewrite <- (g_derive_eq ξ2 (g_der ξ2 (conj Hξ2_low Hξ2_high))).
    exact Hder_g_ξ2. }
  
  assert (Heq_g' : g' 0 = g' ξ2) by (rewrite g'_0, g'_ξ2; reflexivity).
  destruct (Rolle_simple g' 0 ξ2 Hξ2_low g'_cont g'_der Heq_g')
    as [ξ3 [Hξ3 Hder_g'_ξ3]].
  destruct Hξ3 as [Hξ3_low Hξ3_high].
  
  assert (Hder_g'_ξ3_val :
    derive_pt g' ξ3 (g'_der ξ3 (conj Hξ3_low Hξ3_high)) = exp ξ3 - 6 * A / x ^ 3).
  { apply derive_pt_eq_0.
    unfold g'.
    replace (fun t => exp t - 1 - 6 * A * t / x ^ 3)
       with (fun t => (exp t - 1) - (6 * A / x ^ 3) * t).
    2: { apply functional_extensionality; intros y;
           unfold Rdiv; field; lra. }
    apply derivable_pt_lim_minus with
      (f1 := fun t => exp t - 1)
      (f2 := fun t => (6 * A / x ^ 3) * t)
      (x := ξ3) (l1 := exp ξ3) (l2 := 6 * A / x ^ 3).
    - replace (exp ξ3) with (exp ξ3 - 0) by ring.
      apply derivable_pt_lim_minus with
        (f1 := fun t => exp t) (f2 := fun _ => 1)
        (x := ξ3) (l1 := exp ξ3) (l2 := 0).
      + apply derivable_pt_lim_exp.
      + apply derivable_pt_lim_const.
    - unfold derivable_pt_lim.
      intros eps Heps.
      exists (mkposreal 1 Rlt_0_1).
      intros h0 Hh_neq0 Hh_abs.
      replace ((6 * A / x ^ 3 * (ξ3 + h0) - 6 * A / x ^ 3 * ξ3) / h0
                - 6 * A / x ^ 3) with 0.
      2: { field; split; [exact Hx_neq0' | exact Hh_neq0]. }
      rewrite Rabs_R0; exact Heps. }
  
  rewrite Hder_g'_ξ3_val in Hder_g'_ξ3.
  clear Hder_g'_ξ3_val.
  assert (H_eq : exp ξ3 - 6 * A / x ^ 3 = 0) by exact Hder_g'_ξ3.
  clear Hder_g'_ξ3.
  
  assert (exp_eq : exp ξ3 = 6 * A / x ^ 3) by lra.
  assert (A_eq : A = exp ξ3 * x ^ 3 / 6).
  { rewrite exp_eq.
    assert (Htemp: 6 * A / x ^ 3 * x ^ 3 / 6 = A).
    { replace (6 * A / x ^ 3 * x ^ 3) with (6 * A).
      2: { field; exact Hx_neq0'. }
      replace (6 * A / 6) with A.
      2: { field; lra. }
      reflexivity. }
    rewrite Htemp; reflexivity. }
  
  exists ξ3.
  split.
  - split.
    + lra.
    + apply Rlt_le.
      apply Rlt_trans with (r2 := ξ2).
      * exact Hξ3_high.
      * apply Rlt_trans with (r2 := ξ1); [exact Hξ2_high | exact Hξ1_high].
  - rewrite <- A_eq.
    unfold A.
    ring.
Qed.

End TaylorTheorem.
