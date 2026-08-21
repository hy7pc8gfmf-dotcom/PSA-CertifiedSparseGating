(* 拆分自 Riemann_Hypothesis_Proof_Framework.v（复分析证明库 v6.0）*)
(* 库: ca_independence  原文行区间: 23435-25246  机械拆分，未改动内容 *)

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

Require Import ca_base ca_algebra ca_primes ca_complex_analysis ca_fourier ca_zeta_scaffold ca_trig ca_gamma ca_taylor ca_zeta_axioms ca_complex_log ca_complex_foundation ca_log_bounds.

Require Import Stdlib.Logic.IndefiniteDescription.
Require Import Stdlib.Reals.Reals.
Require Import Stdlib.Reals.Rtrigo1.
Require Import Stdlib.Reals.Rpower.
Require Import Stdlib.Reals.Rseries.
Require Import Stdlib.Logic.ProofIrrelevance.
Require Import Stdlib.micromega.Lra.
Local Open Scope R_scope.

(* ====================================================
   模块：independent
   目的：基于质数无限维几何嵌入构造的定理
   依赖：ComplexNumbers, ConstructivePrimes, Coq.Reals.Reals, Coq.Lists.List
   作者：  [王宝军、夏挽岚、祖光照、周志农、高雪峰]
   ==================================================== *)

Import ComplexNumbers.
Import ConstructivePrimes.
Import PrimeEmbedding.
Import FourierAnalysis.
Import ComplexLogarithm.
Require Import Stdlib.Reals.Reals.
Require Import Stdlib.Reals.Rtrigo1.
Require Import Stdlib.Lists.List.
Require Import Stdlib.micromega.Lra.

From Stdlib Require List.

Local Open Scope R_scope.
Local Open Scope complex_scope.

Module independent.

(* ---------- 辅助定义 ---------- *)

(* 质数特征序列（与 prime_characteristic_sequence 一致）*)
Definition phi (p : Prime) (k : nat) : Complex :=
  let n := prime_value p in
  if Nat.ltb k n then Cexp (0 +i (2 * PI * INR k / INR n)) else C0.

(* 平方可和序列类型（ℓ²）*)
Definition l2_sequence' : Type :=
  { f : nat -> Complex | exists M : R, forall N : nat,
      sum_f_R0 (fun k => Cnorm_sq (f k)) N <= M }.

(* 内积 *)
Definition inner_phi (p q : Prime) : Complex :=
  let n := min (prime_value p) (prime_value q) in
  Csum (fun k => phi p k *c Cconj (phi q k)) (n - 1).

(* 前n项索引不变性引理 *)
Lemma nth_firstn_lt : forall (A : Type) (n : nat) (l : list A) (i : nat) (d : A),
  (i < n)%nat -> nth i (firstn n l) d = nth i l d.
Proof.
  intros. rewrite nth_firstn.
  rewrite (proj2 (Nat.ltb_lt i n) H).
  reflexivity.
Qed.

(* ---------- 定理 1：线性无关性 ---------- *)

(* ---------- 局部引理：Csum 的扩展性 ---------- *)
Local Lemma Csum_ext_lemma : forall (f g : nat -> Complex) (n : nat),
  (forall i, f i = g i) -> Csum f n = Csum g n.
Proof.
  intros f g n Heq.
  induction n as [| n IH].
  - (* n = 0 *)
    simpl; reflexivity.
  - (* n = S n *)
    simpl.
    rewrite IH.          (* 递归部分替换 *)
    rewrite Heq.         (* 当前项替换 *)
    reflexivity.
Qed.

(* ---------- 辅助引理：match k 与 INR (S k) 的关系 ---------- *)
Lemma match_S_eq (p : Prime) (k : nat) :
  2 * PI * match k with 0 => 1 | S _ => INR k + 1 end / INR (prime_value p) =
  2 * PI * INR (S k) / INR (prime_value p).
Proof.
  assert (Hp_ge2 : (prime_value p >= 2)%nat) by apply prime_value_ge_2.
  assert (Hp_pos : (0 < prime_value p)%nat) by lia.
  assert (Hp_nz : INR (prime_value p) <> 0) by (apply Rgt_not_eq, lt_0_INR, Hp_pos).
  destruct k as [|k'].
  - simpl. field; auto.
  - simpl. field; auto.
Qed.

(* ---------- 独立引理：单位根的幂 ---------- *)
Lemma Cpow_unit_root (p : Prime) (k : nat) :
  Cpow (Cexp (0 +i (2 * PI / INR (prime_value p)))) k =
  Cexp (0 +i (2 * PI * INR k / INR (prime_value p))).
Proof.
  assert (Hp_ge2 : (prime_value p >= 2)%nat) by apply prime_value_ge_2.
  assert (Hp_pos : (0 < prime_value p)%nat) by lia.
  assert (Hp_nz : INR (prime_value p) <> 0) by (apply Rgt_not_eq, lt_0_INR, Hp_pos).

  induction k as [|k IH].
  - (* k = 0 *)
    simpl.
    unfold Cexp; simpl.
    replace (2 * PI * 0 / INR (prime_value p)) with 0.
    + rewrite exp_0, cos_0, sin_0.
      apply Complex_eq; simpl; ring.
    + field; auto.
  - (* k = S k *)
    simpl.
    rewrite IH.
    rewrite <- Cexp_add.
    apply Complex_eq; simpl.
    + (* 实部相等 *)
      assert (H_eq: 2 * PI / INR (prime_value p) + 2 * PI * INR k / INR (prime_value p) =
                    2 * PI * INR (S k) / INR (prime_value p)).
      { rewrite S_INR. field; auto. }
      rewrite H_eq.
      rewrite Rplus_0_l.  (* 将 exp (0+0) 变为 exp 0 *)
      replace (2 * PI * match k with 0 => 1 | S _ => INR k + 1 end / INR (prime_value p))
        with (2 * PI * INR (S k) / INR (prime_value p)).
      - reflexivity.
      - destruct k.
        + simpl. unfold INR; simpl. rewrite Rmult_1_r. reflexivity.
        + rewrite S_INR. simpl. field; auto.
    + (* 虚部相等 *)
      assert (H_eq': 2 * PI / INR (prime_value p) + 2 * PI * INR k / INR (prime_value p) =
                     2 * PI * INR (S k) / INR (prime_value p)).
      { rewrite S_INR. field; auto. }
      rewrite H_eq'.
      rewrite Rplus_0_l.
      rewrite match_S_eq.
      reflexivity.
Qed.

(* [构造性轨道 S1-20260818] 已删除 Cnorm_sq_eq_0_by_classical（零引用，且为全库唯一
   classic 依赖点之一）；构造性版本 Cnorm_sq_eq_0 见下方。 *)

(* 构造性分解实部虚部 *)
Lemma Cnorm_sq_eq_0 : forall z, Cnorm_sq z = 0 <-> z = C0.
Proof.
  split.
  - intros H. destruct z as [x y]; unfold Cnorm_sq in H; simpl in H.
    apply Rplus_eq_0 in H; [| apply Rle_0_sqr | apply Rle_0_sqr].
    destruct H as [Hx Hy]; apply Rsqr_eq_0 in Hx; apply Rsqr_eq_0 in Hy.
    subst; reflexivity.
  - intros ->. apply Cnorm_sq_zero.
Qed.

(* ====================================================
   引理：复数乘法无零因子（整环性质）
   若 a *c b = C0，则 a = C0 或 b = C0。
   反之，若 a = C0 或 b = C0，则 a *c b = C0。
   ==================================================== *)

Lemma Cmul_no_zero_divisors : forall a b : Complex,
  a *c b = C0 <-> a = C0 \/ b = C0.
Proof.
  split.
  - (* 正向：乘积为零推出至少一个因子为零 *)
    intros H.
    assert (Hsq : Cnorm_sq (a *c b) = Cnorm_sq a * Cnorm_sq b).
    { destruct a, b; unfold Cnorm_sq, Cmul; simpl; unfold Rsqr; ring. }
    apply (f_equal Cnorm_sq) in H.
    assert (Hc0 : Cnorm_sq C0 = 0) by (unfold Cnorm_sq, C0; simpl; rewrite Rsqr_0, Rplus_0_l; reflexivity).
    rewrite Hc0 in H; rewrite Hsq in H.
    apply Rmult_integral in H.
    destruct H as [Ha | Hb].
    + left; apply Cnorm_sq_eq_0; assumption.
    + right; apply Cnorm_sq_eq_0; assumption.
  - (* 反向：若 a 或 b 为零，则乘积为零 *)
    intros [-> | ->].
    + rewrite Cmul_0_l. reflexivity.
    + rewrite Cmul_0_r. reflexivity.
Qed.

(* 附：上述证明中使用的辅助引理（已在 ComplexNumbers 模块中定义或可轻易证明）*)

Lemma Cnorm_sq_zero : Cnorm_sq C0 = 0.
Proof.
  unfold Cnorm_sq, C0; simpl.
  rewrite Rsqr_0, Rplus_0_l; reflexivity.
Qed.

Lemma Cnorm_sq_mult : forall a b, Cnorm_sq (a *c b) = Cnorm_sq a * Cnorm_sq b.
Proof.
  intros [a1 a2] [b1 b2]; unfold Cnorm_sq, Cmul; simpl.
  unfold Rsqr; ring.
Qed.

Lemma Cnorm_sq_ge_0 : forall z, 0 <= Cnorm_sq z.
Proof.
  intros [x y]; unfold Cnorm_sq; apply Rplus_le_le_0_compat; apply Rle_0_sqr.
Qed.

Lemma Cmul_0_l : forall z, C0 *c z = C0.
Proof.
  intros [x y]; unfold C0, Cmul; simpl; f_equal; ring.
Qed.

Lemma Cmul_0_r : forall z, z *c C0 = C0.
Proof.
  intros [x y]; unfold C0, Cmul; simpl; f_equal; ring.
Qed.

(* 辅助引理：非空列表的 fold_right max 结果一定在列表中 *)
Lemma max_fold_right_in : forall l, l <> nil -> In (fold_right Init.Nat.max 0%nat l) l.
Proof.
  induction l as [|h t IH].
  - intros H; contradiction H; reflexivity.
  - intros _.
    destruct t as [|h2 t2].
    + (* t = nil *) simpl. left. rewrite Nat.max_0_r. reflexivity.
    + (* t = h2 :: t2 *) simpl.
      set (m := fold_right Init.Nat.max 0%nat (h2 :: t2)).
      change (max h (max h2 (fold_right Init.Nat.max 0%nat t2))) with (Nat.max h m).
      destruct (Nat.max_dec h m) as [Hmax|Hmax].
      * rewrite Hmax; left; reflexivity.
      * rewrite Hmax; right.
        apply IH; discriminate.
Qed.

(* 有限和逐项相等 *)
Lemma Csum_ext : forall (f g : nat -> Complex) (n : nat),
  (forall i, (i < n)%nat -> f i = g i) -> Csum f n = Csum g n.
Proof.
  induction n as [|n IH]; intros H.
  - reflexivity.
  - simpl. rewrite IH.
    + f_equal. apply H; lia.
    + intros i Hi. apply H; lia.
Qed.

(* 单个非零项的求和 *)
Lemma Csum_single : forall (f : nat -> Complex) (n i : nat) (c : Complex),
  (i < n)%nat ->
  (forall j, (j < n)%nat -> (j = i -> f j = c) /\ (j <> i -> f j = C0)) ->
  Csum f n = c.
Proof.
  induction n as [|n IH]; intros i c Hlt H.
  - lia.
  - simpl.
    destruct (eq_nat_dec i n).
    + subst.
      assert (Hn_lt_Sn : (n < S n)%nat) by lia.
      assert (f n = c) by (destruct (H n Hn_lt_Sn) as [Heq _]; apply Heq; reflexivity).
      rewrite H0.
      destruct n as [|n'].
      * simpl. rewrite Cadd_0_r. reflexivity.
      * (* n = S n' *)
        assert (forall j, (j < S n')%nat -> f j = C0) as Hzero.
        { intros j Hj.
          assert (Hj_lt_Sn : (j < S (S n'))%nat) by lia.
          destruct (H j Hj_lt_Sn) as [_ Hnz]; apply Hnz; lia.
        }
        assert (Csum f (S n') = C0).
        { apply IH with (i := 0%nat) (c := C0).
          - lia.
          - intros j Hj. split.
            + intros Heq; subst; apply Hzero; assumption.
            + intros _; apply Hzero; assumption.
        }
        rewrite H1.
        rewrite Cadd_0_r.
        reflexivity.
    + assert (Hn_lt_Sn : (n < S n)%nat) by lia.
      assert (f n = C0) by (destruct (H n Hn_lt_Sn) as [_ Hnz]; apply Hnz; lia).
      rewrite H0.
      assert (forall j, (j < n)%nat -> (j = i -> f j = c) /\ (j <> i -> f j = C0)) as H'.
      { intros j Hj.
        assert (Hj_lt_Sn : (j < S n)%nat) by lia.
        destruct (H j Hj_lt_Sn) as [H1 H2]; split; auto.
      }
      assert (i_lt_n : (i < n)%nat) by lia.
      rewrite (IH i c i_lt_n H').
      rewrite Cadd_0_l.
      reflexivity.
Qed.

(* 折叠最大值不小于列表元素 *)
(* fold_right max 0 的结果不小于列表中的任意元素 *)
Lemma fold_right_max_ge : forall (l : list nat) (x : nat),
  In x l -> Nat.le x (fold_right Init.Nat.max 0%nat l).
Proof.
  induction l as [|h t IH]; intros x H; [inversion H |].
  simpl. destruct (Nat.max_dec h (fold_right Init.Nat.max 0%nat t)) as [Hmax|Hmax];
    rewrite Hmax.
  - (* 最大值是 h *)
    destruct H as [Heq|Hin].
    + subst x; apply Nat.le_refl.
    + apply Nat.le_trans with (fold_right Init.Nat.max 0%nat t).
      * apply IH; exact Hin.
      * rewrite <- Hmax. apply Nat.le_max_r.
  - (* 最大值是 fold_right max t *)
    destruct H as [Heq|Hin].
    + subst x. rewrite <- Hmax. apply Nat.le_max_l.
    + apply IH; exact Hin.
Qed.

(* 质数列表最大值索引存在性 *)
Lemma max_prime_index_exists : forall (p_list : list Prime),
  p_list <> nil ->
  exists i0, (i0 < length p_list)%nat /\
    (forall j, (j < length p_list)%nat -> (prime_value (nth j p_list prime_2) <= prime_value (nth i0 p_list prime_2))%nat).
Proof.
  intros p_list Hnonnil.
  set (vals := map prime_value p_list).
  set (max_val := fold_right Init.Nat.max 0%nat vals).
  assert (In max_val vals).
  { apply max_fold_right_in. destruct p_list; [contradiction | simpl; discriminate]. }
  apply in_map_iff in H as [p [Hp Hin]].
  (* 找到 p 在 p_list 中的索引 *)
  assert (exists i, nth i p_list prime_2 = p /\ (i < length p_list)%nat) as H_idx.
  { clear - Hin. induction p_list as [|h t IH]; [inversion Hin |].
    destruct Hin as [Heq|Hin'].
    - subst h. exists 0%nat. split; [reflexivity | simpl; lia].
    - destruct (IH Hin') as [i [Heq' Hi]]. exists (S i). split; [simpl; rewrite Heq'; reflexivity | simpl; lia]. }
  destruct H_idx as [i0 [Heq_i0 Hi0]].
  exists i0. split; [exact Hi0 |].
  intros j Hj.
  rewrite Heq_i0.
  assert (H_in_vals : In (prime_value (nth j p_list prime_2)) vals).
  { apply in_map_iff. exists (nth j p_list prime_2). split; [reflexivity | apply nth_In; auto]. }
  apply Nat.le_trans with max_val.
  - apply fold_right_max_ge with (l := vals); exact H_in_vals.
  - rewrite Hp; apply Nat.le_refl.
Qed.

(* 无重复列表中不同索引对应不同元素 *)
Lemma NoDup_nth : forall A (l : list A) (i j : nat) d,
  NoDup l -> (i < length l)%nat -> (j < length l)%nat -> nth i l d = nth j l d -> i = j.
Proof.
  induction l as [|h t IH]; intros i j d Hnd Hi Hj Heq.
  - (* l = nil *)
    exfalso. apply Nat.nlt_0_r in Hi. contradiction.
  - simpl in Hi, Hj. destruct i, j.
    + reflexivity.
    + (* i = 0, j = S j' *)
      exfalso.
      inversion Hnd as [|? ? Hnin Hnd'].
      assert (Hj_lt : (j < length t)%nat) by lia.
      replace (nth (S j) (h :: t) d) with (nth j t d) in Heq by (simpl; reflexivity).
      simpl in Heq. rewrite Heq in Hnin.
      apply Hnin. apply nth_In; exact Hj_lt.
    + (* i = S i', j = 0 *)
      exfalso.
      inversion Hnd as [|? ? Hnin Hnd'].
      assert (Hi_lt : (i < length t)%nat) by lia.
      replace (nth (S i) (h :: t) d) with (nth i t d) in Heq by (simpl; reflexivity).
      simpl in Heq. rewrite <- Heq in Hnin.
      apply Hnin. apply nth_In; exact Hi_lt.
    + (* i = S i', j = S j' *)
      inversion Hnd as [|? ? Hnin Hnd'].
      assert (Hi' : (i < length t)%nat) by lia.
      assert (Hj' : (j < length t)%nat) by lia.
      simpl in Heq.
      apply f_equal.
      apply IH with (d := d); [exact Hnd' | exact Hi' | exact Hj' | exact Heq].
Qed.

(* 最大值严格大于引理 *)
Lemma max_prime_strict_ineq : forall (p_list : list Prime) (i0 : nat),
  NoDup (map prime_value p_list) ->
  (i0 < length p_list)%nat ->
  (forall j, (j < length p_list)%nat -> (prime_value (nth j p_list prime_2) <= prime_value (nth i0 p_list prime_2))%nat) ->
  forall j, j <> i0 -> (j < length p_list)%nat -> (prime_value (nth j p_list prime_2) < prime_value (nth i0 p_list prime_2))%nat.
Proof.
  intros p_list i0 Hdup Hi0 Hmax j Hneq Hj.
  specialize (Hmax j Hj).
  destruct (Nat.lt_ge_cases (prime_value (nth j p_list prime_2)) (prime_value (nth i0 p_list prime_2))) as [Hlt|Hge].
  - exact Hlt.
  - assert (Heq : prime_value (nth j p_list prime_2) = prime_value (nth i0 p_list prime_2)) by lia.
    assert (j = i0).
    { apply NoDup_nth with (l := map prime_value p_list) (i := j) (j := i0) (d := prime_value prime_2).
      - exact Hdup.
      - rewrite length_map; apply Hj.
      - rewrite length_map; apply Hi0.
      - rewrite map_nth with (f := prime_value) (d := prime_2) (n := j).
        rewrite map_nth with (f := prime_value) (d := prime_2) (n := i0).
        simpl. exact Heq. }
    contradiction.
Qed.

(* 非最大质数项消零引理 *)
(** 对于给定的 k0 = M-1，所有 j ≠ i0 的项 c_j * φ(p_j, k0) 为零（无论 c_j 是否为 0）*)
Lemma term_zero_for_others : forall (p_list : list Prime) (coeffs : list Complex) (i0 : nat),
  (forall j, (j < length p_list)%nat -> (prime_value (nth j p_list prime_2) <= prime_value (nth i0 p_list prime_2))%nat) ->
  (forall j, j <> i0 -> (j < length p_list)%nat -> (prime_value (nth j p_list prime_2) < prime_value (nth i0 p_list prime_2))%nat) ->
  let M := prime_value (nth i0 p_list prime_2) in
  let k0 := (M - 1)%nat in
  forall j, (j < length p_list)%nat -> j <> i0 ->
    nth j coeffs C0 *c prime_characteristic_sequence (nth j p_list prime_2) k0 = C0.
Proof.
  intros p_list coeffs i0 Hle Hlt M k0 j Hj Hneq.
  unfold prime_characteristic_sequence.
  assert (Hlt_j : (prime_value (nth j p_list prime_2) < M)%nat) by (apply Hlt; auto).
  apply Nat.lt_le_pred in Hlt_j.
  assert (Hk0_ge : (k0 >= prime_value (nth j p_list prime_2))%nat).
  { apply Nat.le_trans with (Nat.pred M); [exact Hlt_j | unfold k0; lia]. }
  assert (Hfalse : (k0 <? prime_value (nth j p_list prime_2))%nat = false).
  { apply Nat.ltb_ge. assumption. }
  rewrite Hfalse.
  rewrite Cmul_0_r.
  reflexivity.
Qed.

(* 单非零项求和化简引理 *)
(** 当 i0 < n-1 时，Csum g n 等于唯一的非零项 *)
Lemma Csum_reduce_to_single : forall (coeffs : list Complex) (i0 m' : nat) (phi0 : Complex),
  (i0 < m')%nat ->
  let g := fun j => if Nat.eqb j i0 then nth i0 coeffs C0 *c phi0 else C0 in
  Csum g m' = nth i0 coeffs C0 *c phi0.
Proof.
  intros coeffs i0 m' phi0 Hi0.
  apply Csum_single with (i := i0) (c := nth i0 coeffs C0 *c phi0).
  - exact Hi0.
  - intros j Hj.
    split.
    + intros ->. destruct (Nat.eqb_spec i0 i0) as [H|H]; [reflexivity | lia].
    + intros Hneq. destruct (Nat.eqb_spec j i0) as [Heq|Hneq']; [lia | reflexivity].
Qed.

(* 复数域无零因子引理 *)
(** 若 c * phi = C0 且 phi ≠ C0，则 c = C0 *)
Lemma product_zero_implies_factor_zero : forall (c phi : Complex),
  c *c phi = C0 -> phi <> C0 -> c = C0.
Proof.
  intros c phi Hprod Hphi.
  apply Cnorm_sq_eq_0.
  apply f_equal with (f := Cnorm_sq) in Hprod.
  rewrite Cnorm_sq_mult in Hprod.
  rewrite Cnorm_sq_zero in Hprod.
  apply Rmult_integral in Hprod.
  destruct Hprod as [Hc | Hphi_sq].
  - exact Hc.
  - exfalso. apply Hphi. apply Cnorm_sq_eq_0. auto.
Qed.

(* 前段成员必在原列表 *)
(** 辅助引理：若元素出现在 firstn n l 中，则必出现在 l 中 *)
Lemma In_firstn : forall A (a : A) (l : list A) (n : nat),
  In a (firstn n l) -> In a l.
Proof.
  intros A a l n.
  revert n.
  induction l as [|b l IH]; intros n H.
  - (* l = [] *)
    destruct n; simpl in H; contradiction.
  - (* l = b :: l *)
    destruct n as [|n']; simpl in H.
    + (* n = 0: firstn 0 (b::l) = [] *) contradiction.
    + (* n = S n' *)
      destruct H as [Heq | Hin].
      * (* a = b *) subst b; left; reflexivity.
      * (* a in firstn n' l *) right; apply IH with (n:=n'); exact Hin.
Qed.

Local Close Scope R_scope.

(* 后缀成员必在原列表 *)
(** 辅助引理：若元素出现在 skipn n l 中，则必出现在 l 中 *)
Lemma In_skipn : forall A (a : A) (l : list A) (n : nat),
  In a (skipn n l) -> In a l.
Proof.
  intros A a l n.
  revert n.
  induction l as [|b l IH]; intros n H.
  - destruct n; simpl in H; destruct H.
  - destruct n; simpl in H.
    + destruct H as [Heq|Hin]; [left; exact Heq | right; apply IH with (n:=0); exact Hin].
    + right; apply IH with (n:=n); exact H.
Qed.

(* 无重复列表删除元素后保持无重复 *)
(** 从无重复列表中删除第 i 个元素后，剩余部分仍无重复 *)
Lemma NoDup_remove_at : forall A (l : list A) (i : nat),
  NoDup l -> i < length l -> NoDup (firstn i l ++ skipn (S i) l).
Proof.
  induction l as [|a l IH]; intros i Hdup Hlen.
  - inversion Hlen.
  - simpl in Hlen.
    destruct i as [|i'].
    + (* i = 0 *)
      simpl.
      inversion Hdup as [|? ? Hnin Hdup_tail].
      exact Hdup_tail.
    + (* i = S i' *)
      simpl.
      inversion Hdup as [|? ? Hnin Hdup_tail].
      apply NoDup_cons.
      * intros Hcontra.
        apply in_app_iff in Hcontra; destruct Hcontra as [Hfirst | Hskip].
        -- apply Hnin; apply In_firstn with (n:=i'); exact Hfirst.
        -- apply Hnin; apply In_skipn with (n:=S i'); exact Hskip.
      * apply IH with (i := i'); [exact Hdup_tail | lia].
Qed.

Local Open Scope R_scope.

(* 映射保前段 *)
Lemma map_firstn : forall A B (f : A -> B) n l,
  map f (firstn n l) = firstn n (map f l).
Proof.
  induction n as [|n IH]; simpl; auto.
  destruct l; simpl; auto.
  f_equal; apply IH.
Qed.

(* 映射保后段 *)
Lemma map_skipn : forall A B (f : A -> B) n l,
  map f (skipn n l) = skipn n (map f l).
Proof.
  induction n as [|n IH]; simpl; auto.
  destruct l; simpl; auto.
Qed.

(* 复数部分和加法拆分 *)
(* 将求和拆分为前 n 项和后 m 项 *)
Lemma Csum_split : forall (f : nat -> Complex) (n m : nat),
  Csum f (n + m) = Csum f n +c Csum (fun i => f (n + i)%nat) m.
Proof.
  induction m as [|m IH]; simpl.
  - (* base case m = 0 *)
    rewrite Nat.add_0_r. rewrite Cadd_0_r. reflexivity.
  - (* inductive step *)
    rewrite (Nat.add_succ_r n m). simpl.
    rewrite IH.
    rewrite <- Cadd_assoc.
    rewrite (Cadd_comm (f (n + m)%nat) (Csum f n)).
    rewrite Cadd_assoc.
    reflexivity.
Qed.

(* 复数部分和拆分末项 *)
Lemma Csum_split_last : forall (f : nat -> Complex) (n : nat),
  Csum f (S n) = Csum f n +c f n.
Proof.
  induction n as [|n IH]; simpl.
  - (* 基础情况 n = 0 *)
    rewrite Cadd_0_r, Cadd_0_l. reflexivity.
  - (* 归纳步骤 *)
    rewrite (Cadd_comm (f (S n)) (f n +c Csum f n)).
    reflexivity.
Qed.

(* 前n项索引取值引理 *)
Lemma nth_firstn : forall A (l : list A) (n i : nat) (d : A),
  (i < n)%nat -> nth i (firstn n l) d = nth i l d.
Proof.
  intros A l n i d Hi.
  revert i l Hi.
  induction n as [|n IH]; intros i l Hi.
  - lia. (* n = 0 时 i < 0 不可能 *)
  - destruct i as [|i'].
    + (* i = 0 *)
      simpl. destruct l; reflexivity.
    + (* i = S i' *)
      simpl. destruct l as [|a l'].
      * (* l = nil：两边都是 d *)
        reflexivity.
      * (* l = a :: l' *)
        simpl. apply IH. lia.
Qed.

(* 跳过 n 后取第 i 个元素引理 *)
Lemma nth_skipn : forall A (l : list A) (n i : nat) (d : A),
  nth i (skipn n l) d = nth (n + i) l d.
Proof.
  intros A l n i d.
  revert i l.
  induction n as [|n IH]; intros i l.
  - simpl. reflexivity.
  - simpl. destruct l as [|a l'].
    + (* l = nil *)
      simpl. destruct i; reflexivity.
    + (* l = a :: l' *)
      simpl. rewrite IH. reflexivity.
Qed.

(* 删除元素保持无重复引理 *)
Lemma reduced_system_nodup : forall (p_list : list Prime) (i0 : nat),
  NoDup (map prime_value p_list) ->
  (i0 < length p_list)%nat ->
  NoDup (map prime_value (firstn i0 p_list ++ skipn (S i0) p_list)).
Proof.
  intros p_list i0 Hdup Hi0.
  rewrite map_app, map_firstn, map_skipn.
  apply NoDup_remove_at with (l := map prime_value p_list) (i := i0).
  - exact Hdup.
  - rewrite length_map. exact Hi0.
Qed.

(*约化系统长度保持引理 *)
Lemma reduced_system_length : forall (p_list : list Prime) (coeffs : list Complex) (i0 : nat),
  length p_list = length coeffs ->
  length (firstn i0 p_list ++ skipn (S i0) p_list) =
  length (firstn i0 coeffs ++ skipn (S i0) coeffs).
Proof.
  intros p_list coeffs i0 Hlen.
  rewrite !length_app, !length_firstn, !length_skipn.
  lia.
Qed.

(* 前段索引引理 *)

Close Scope R_scope.

(* 列表索引有效取值唯一性 *)
Lemma nth_indep' : forall (A : Type) (l : list A) (n : nat) (d d' : A),
  n < length l -> List.nth n l d = List.nth n l d'.
Proof.
  intros A l n d d' H.
  revert n H.
  induction l as [|a l IH].
  - intros n H; simpl in H; lia.
  - intros n H.
    destruct n as [|n']; simpl.
    + reflexivity.
    + apply IH. simpl in H; lia.
Qed.

Open Scope R_scope.

(* 删除最后一个元素时，方程保持 *)
Lemma reduced_system_equation_last : forall (p_list : list Prime) (coeffs : list Complex) (idx : nat)
  (Hlen : List.length p_list = List.length coeffs)
  (Hidx : (idx < List.length p_list)%nat)
  (Heq_last : idx = (List.length p_list - 1)%nat)
  (Hc0 : nth idx coeffs C0 = C0)
  (Heq : forall k, Csum (fun i => nth i coeffs C0 *c prime_characteristic_sequence (nth i p_list prime_2) k)
                         (List.length p_list - 1) = C0),
  forall k,
    Csum (fun i => nth i (firstn ((List.length p_list - 1)%nat) coeffs) C0 *c
                   prime_characteristic_sequence (nth i (firstn ((List.length p_list - 1)%nat) p_list) prime_2) k)
         (List.length (firstn ((List.length p_list - 1)%nat) p_list)) = C0.
Proof.
  intros p_list coeffs idx Hlen Hidx Heq_last Hc0 Heq k.
  set (m := length p_list).
  rewrite Heq_last in *.
  assert (m > 0)%nat by lia.
  destruct (Nat.eq_dec m 1) as [Hm1 | Hm_gt1].
  - (* m = 1 *)
    rewrite Hm1 in *; rewrite firstn_0, length_nil; simpl; reflexivity.
  - (* m > 1 *)
    assert (Hlen_firstn_p : length (firstn (m - 1)%nat p_list) = (m - 1)%nat).
    { rewrite length_firstn, Nat.min_l; [reflexivity | lia]. }
    assert (Hlen_firstn_c : length (firstn (m - 1)%nat coeffs) = (m - 1)%nat).
    { rewrite length_firstn, Nat.min_l; [reflexivity | rewrite <- Hlen; lia]. }
    rewrite Hlen_firstn_p.
    assert (Hsum_eq : Csum (fun i => nth i (firstn (m-1)%nat coeffs) C0 *c
                                 prime_characteristic_sequence (nth i (firstn (m-1)%nat p_list) prime_2) k) (m-1)%nat =
                      Csum (fun i => nth i coeffs C0 *c
                                 prime_characteristic_sequence (nth i p_list prime_2) k) (m-1)%nat).
    { apply Csum_ext; intros i Hi.
      rewrite nth_firstn_lt with (n := (m-1)%nat) (l := coeffs) (d := C0); [| lia].
      rewrite nth_firstn_lt with (n := (m-1)%nat) (l := p_list) (d := prime_2); [| lia].
      reflexivity. }
    rewrite Hsum_eq.
    unfold m.
    apply Heq.
Qed.

(** 列表拼接的 nth 性质（显式使用自然数比较） *)
Lemma nth_app_left : forall (A : Type) (l1 l2 : list A) (i : nat) (d : A),
  (i < length l1)%nat -> nth i (l1 ++ l2) d = nth i l1 d.
Proof.
  intros A l1 l2 i d Hi.
  revert i Hi.
  induction l1 as [|a l1 IH].
  - intros i Hi. simpl in Hi. inversion Hi.
  - intros i Hi. simpl. destruct i as [|i'].
    + reflexivity.
    + simpl in Hi. apply IH. lia.
Qed.

(* 列表拼接右段索引 *)
Lemma nth_app_right : forall (A : Type) (l1 l2 : list A) (i : nat) (d : A),
  (i >= length l1)%nat -> nth i (l1 ++ l2) d = nth (i - length l1) l2 d.
Proof.
  intros A l1 l2 i d Hi. revert i Hi.
  induction l1 as [|a l1 IH]; simpl.
  - intros; rewrite Nat.sub_0_r; reflexivity.
  - intros i Hi. destruct i; [lia|].
    simpl. apply IH. lia.
Qed.

(** 主引理：删除中间元素后的方程保持 *)
Lemma reduced_system_equation_middle : forall (p_list : list Prime) (coeffs : list Complex) (i0 : nat)
  (Hlen : length p_list = length coeffs)
  (Hi0 : (i0 < length p_list)%nat) (Hne_last : (i0 < Nat.pred (length p_list))%nat)
  (Hc0 : nth i0 coeffs C0 = C0)
  (Heq : forall k, Csum (fun i => nth i coeffs C0 *c prime_characteristic_sequence (nth i p_list prime_2) k)
                         (Nat.pred (length p_list)) = C0),
  forall k,
    Csum (fun i =>
            let idx := if (i <? i0)%nat then i else (S i)%nat in
            nth idx coeffs C0 *c prime_characteristic_sequence (nth idx p_list prime_2) k)
         (Nat.pred (length (List.app (List.firstn i0 p_list) (List.skipn (S i0) p_list)))) = C0.
Proof.
  intros p_list coeffs i0 Hlen Hi0 Hne_last Hc0 Heq k.
  set (m := length p_list).
  set (p_list' := List.app (List.firstn i0 p_list) (List.skipn (S i0) p_list)).
  set (coeffs' := List.app (List.firstn i0 coeffs) (List.skipn (S i0) coeffs)).

  (* 新列表的长度 *)
  assert (Hlen_new : length p_list' = pred m).
  { unfold p_list'. rewrite length_app, length_firstn, length_skipn.
    rewrite min_l by lia. lia. }

  (* 定义新求和的上界 N = pred (length p_list') = m - 2 *)
  set (N := (m - 2)%nat).  (* natural subtraction *)
  assert (HN_eq : N = (m - 2)%nat) by reflexivity.
  assert (Hi0_bound : (i0 <= N)%nat) by (unfold N; lia).

  (* 重写求和上界为 N *)
  rewrite Hlen_new.
  assert (Heq_bound : Nat.pred (pred m) = N) by (unfold N; lia).
  rewrite Heq_bound.

  (* 将 N 重写为 i0 + (N - i0) 形式，以便使用 Csum_split *)
  assert (Hsum_eq : N = (i0 + (N - i0))%nat) by lia.
  rewrite Hsum_eq.
  rewrite (Csum_split (fun i => let idx := if (i <? i0)%nat then i else S i in
                                nth idx coeffs C0 *c prime_characteristic_sequence (nth idx p_list prime_2) k)
                     i0 (N - i0)%nat); try lia.

  (* 前 i0 项等于原系统的前 i0 项 *)
  assert (H1 : Csum (fun i => nth i coeffs' C0 *c prime_characteristic_sequence (nth i p_list' prime_2) k) i0 =
               Csum (fun i => nth i coeffs C0 *c prime_characteristic_sequence (nth i p_list prime_2) k) i0).
  { apply Csum_ext; intros j Hj.
    unfold coeffs', p_list'.
    assert (Hlen_firstn_coeffs : length (firstn i0 coeffs) = i0).
    { rewrite length_firstn, min_l; [reflexivity | rewrite <- Hlen; lia]. }
    assert (Hlen_firstn_p_list : length (firstn i0 p_list) = i0).
    { rewrite length_firstn, min_l; [reflexivity | lia]. }
    rewrite nth_app_left with (l1 := firstn i0 coeffs) (l2 := skipn (S i0) coeffs) (i := j) (d := C0);
      [| rewrite Hlen_firstn_coeffs; lia].
    rewrite nth_firstn_lt with (n := i0) (l := coeffs) (i := j) (d := C0); [| lia].
    rewrite nth_app_left with (l1 := firstn i0 p_list) (l2 := skipn (S i0) p_list) (i := j) (d := prime_2);
      [| rewrite Hlen_firstn_p_list; lia].
    rewrite nth_firstn_lt with (n := i0) (l := p_list) (i := j) (d := prime_2); [| lia].
    reflexivity. }

  (* 后 (N - i0) 项对应原系统中从 i0+1 开始的项 *)
  assert (H2 : Csum (fun j => nth (i0 + j) coeffs' C0 *c prime_characteristic_sequence (nth (i0 + j) p_list' prime_2) k) (N - i0)%nat =
               Csum (fun j => nth (S i0 + j) coeffs C0 *c prime_characteristic_sequence (nth (S i0 + j) p_list prime_2) k) (N - i0)%nat).
  { apply Csum_ext; intros j Hj.
    unfold coeffs', p_list'.
    assert (Hlen_firstn_coeffs : length (firstn i0 coeffs) = i0).
    { rewrite length_firstn, min_l; [reflexivity | rewrite <- Hlen; lia]. }
    assert (Hlen_firstn_p_list : length (firstn i0 p_list) = i0).
    { rewrite length_firstn, min_l; [reflexivity | lia]. }
    (* 使用 nth_app_right 处理 coeffs' *)
    assert (Hge_coeffs : ((i0 + j)%nat >= length (firstn i0 coeffs))%nat).
    { rewrite Hlen_firstn_coeffs; lia. }
    rewrite nth_app_right with (l1 := firstn i0 coeffs) (l2 := skipn (S i0) coeffs) (i := (i0 + j)%nat) (d := C0);
      [| exact Hge_coeffs].
    (* 简化索引：i0 + j - length (firstn i0 coeffs) = j *)
    assert (Hidx_eq_coeffs : (i0 + j - length (firstn i0 coeffs))%nat = j).
    { rewrite Hlen_firstn_coeffs; lia. }
    rewrite Hidx_eq_coeffs.
    rewrite nth_skipn.
    (* 使用 nth_app_right 处理 p_list' *)
    assert (Hge_p_list : ((i0 + j)%nat >= length (firstn i0 p_list))%nat).
    { rewrite Hlen_firstn_p_list; lia. }
    rewrite nth_app_right with (l1 := firstn i0 p_list) (l2 := skipn (S i0) p_list) (i := (i0 + j)%nat) (d := prime_2);
      [| exact Hge_p_list].
    (* 简化索引：i0 + j - length (firstn i0 p_list) = j *)
    assert (Hidx_eq_p_list : (i0 + j - length (firstn i0 p_list))%nat = j).
    { rewrite Hlen_firstn_p_list; lia. }
    rewrite Hidx_eq_p_list.
    rewrite nth_skipn.
    reflexivity. }

  (* 原方程中 pred m = i0 + 1 + (N - i0) *)
  assert (Hpred : pred m = (i0 + S (N - i0))%nat) by (unfold N; lia).
  (* 将 Heq 中的 length p_list 替换为 m *)
  assert (Hlen_eq : length p_list = m) by reflexivity.
  rewrite Hlen_eq in Heq.
  specialize (Heq k).
  rewrite Hpred in Heq.
  (* 将 S (N - i0) 显式写成 1 + (N - i0) *)
  replace (S (N - i0))%nat with (1 + (N - i0))%nat in Heq by lia.

  (* 将原方程拆分为三部分 *)
  rewrite (Csum_split (fun i => nth i coeffs C0 *c prime_characteristic_sequence (nth i p_list prime_2) k)
                     i0 (1 + (N - i0))%nat) in Heq; try lia.
  rewrite (Csum_split (fun j => nth (i0 + j) coeffs C0 *c prime_characteristic_sequence (nth (i0 + j) p_list prime_2) k)
                     1 (N - i0)%nat) in Heq; try lia.
  simpl in Heq.

  (* 消除多余的 C0 项：Csum (fun j => ...) 0 被化简为 C0，而 X +c C0 = X *)
  rewrite Cadd_0_r in Heq.

  (* 简化 (i0+0) 为 i0 *)
  replace (i0 + 0)%nat with i0 in Heq by lia.
  (* 现在 Heq 中出现了 nth i0 coeffs ... *)
  rewrite Hc0, Cmul_0_l, Cadd_0_l in Heq.

  (* 证明第一项的条件等价 *)
  assert (Hfirst_eq : forall i, (i < i0)%nat ->
           let idx := if (i <? i0)%nat then i else S i in
           nth idx coeffs C0 *c prime_characteristic_sequence (nth idx p_list prime_2) k =
           nth i coeffs C0 *c prime_characteristic_sequence (nth i p_list prime_2) k).
  { intros i Hi. destruct (Nat.ltb_spec i i0) as [Hlt|Hge]; [reflexivity | lia]. }

  rewrite (Csum_ext (fun i => let idx := if (i <? i0)%nat then i else S i in
                              nth idx coeffs C0 *c prime_characteristic_sequence (nth idx p_list prime_2) k)
                    (fun i => nth i coeffs C0 *c prime_characteristic_sequence (nth i p_list prime_2) k)
                    i0 Hfirst_eq).

  (* 证明第二项的条件等价 *)
  assert (Hsecond_eq : forall i, (i < N - i0)%nat ->
           let idx := if (i0 + i <? i0)%nat then (i0 + i)%nat else S (i0 + i) in
           nth idx coeffs C0 *c prime_characteristic_sequence (nth idx p_list prime_2) k =
           nth (i0 + S i) coeffs C0 *c prime_characteristic_sequence (nth (i0 + S i) p_list prime_2) k).
  { intros i Hi.
    destruct (Nat.ltb_spec (i0 + i) i0) as [Hlt|Hge].
    - lia. (* 不可能 *)
    - replace (S (i0 + i))%nat with (i0 + S i)%nat by lia.
      reflexivity. }

  rewrite (Csum_ext (fun i => let idx := if (i0 + i <? i0)%nat then (i0 + i)%nat else S (i0 + i) in
                              nth idx coeffs C0 *c prime_characteristic_sequence (nth idx p_list prime_2) k)
                    (fun i => nth (i0 + S i) coeffs C0 *c prime_characteristic_sequence (nth (i0 + S i) p_list prime_2) k)
                    (N - i0) Hsecond_eq).

  (* 现在目标左边与 Heq 左边完全相同 *)
  rewrite Heq.
  reflexivity.
Qed.

(* 定理：约化系统的方程保持 *)
Theorem build_reduced_system : forall (p_list : list Prime) (coeffs : list Complex) (i0 : nat),
  NoDup (map prime_value p_list) ->
  length p_list = length coeffs ->
  (i0 < length p_list)%nat ->
  (i0 < Nat.pred (length p_list))%nat ->  (* 确保 i0 不是最后一个元素 *)
  (forall k, Csum (fun i => let p := nth i p_list prime_2 in
                            let c := nth i coeffs C0 in
                            c *c prime_characteristic_sequence p k) (pred (length p_list)) = C0) ->
  nth i0 coeffs C0 = C0 ->
  let p_list' := List.firstn i0 p_list ++ List.skipn (S i0) p_list in
  let coeffs' := List.firstn i0 coeffs ++ List.skipn (S i0) coeffs in
  NoDup (map prime_value p_list') /\
  length p_list' = length coeffs' /\
  (forall k, Csum (fun i => let p := nth i p_list' prime_2 in
                            let c := nth i coeffs' C0 in
                            c *c prime_characteristic_sequence p k) (pred (length p_list')) = C0).
Proof.
  intros p_list coeffs i0 Hdup Hlen Hi0 Hne_last Hsum_all Hc0.
  split; [| split].
  - apply reduced_system_nodup with (i0 := i0); assumption.
  - apply reduced_system_length with (i0 := i0); assumption.
  - intros k.
    assert (Heq_sum : forall i, (i < pred (length (firstn i0 p_list ++ skipn (S i0) p_list)))%nat ->
                let p := nth i (firstn i0 p_list ++ skipn (S i0) p_list) prime_2 in
                let c := nth i (firstn i0 coeffs ++ skipn (S i0) coeffs) C0 in
                c *c prime_characteristic_sequence p k =
                let idx := if (i <? i0)%nat then i else S i in
                nth idx coeffs C0 *c prime_characteristic_sequence (nth idx p_list prime_2) k).
    { intros i Hi.
      destruct (Nat.ltb_spec i i0) as [Hlt|Hge].
      - (* i < i0 *)
        rewrite (nth_app_left Prime (firstn i0 p_list) (skipn (S i0) p_list) i prime_2);
          [| rewrite length_firstn; rewrite min_l by lia; lia].
        rewrite (nth_firstn_lt Prime i0 p_list i prime_2 Hlt).
        rewrite (nth_app_left Complex (firstn i0 coeffs) (skipn (S i0) coeffs) i C0);
          [| rewrite length_firstn; rewrite min_l by (rewrite <- Hlen; lia); lia].
        rewrite (nth_firstn_lt Complex i0 coeffs i C0 Hlt).
        reflexivity.
      - (* i >= i0 *)
        assert (Hlen_firstn_p : length (firstn i0 p_list) = i0).
        { rewrite length_firstn; rewrite min_l by lia; reflexivity. }
        assert (Hlen_firstn_c : length (firstn i0 coeffs) = i0).
        { rewrite length_firstn; rewrite min_l by (rewrite <- Hlen; lia); reflexivity. }
        rewrite (nth_app_right Prime (firstn i0 p_list) (skipn (S i0) p_list) i prime_2);
          [| rewrite Hlen_firstn_p; lia].
        rewrite nth_skipn.
        rewrite Hlen_firstn_p.
        rewrite (nth_app_right Complex (firstn i0 coeffs) (skipn (S i0) coeffs) i C0);
          [| rewrite Hlen_firstn_c; lia].
        rewrite nth_skipn.
        rewrite Hlen_firstn_c.
        replace (S i0 + (i - i0))%nat with (S i) by lia.
        reflexivity.
    }
    rewrite (Csum_ext (fun i => let p := nth i (firstn i0 p_list ++ skipn (S i0) p_list) prime_2 in
                                let c := nth i (firstn i0 coeffs ++ skipn (S i0) coeffs) C0 in
                                c *c prime_characteristic_sequence p k)
                      (fun i => let idx := if (i <? i0)%nat then i else S i in
                                nth idx coeffs C0 *c prime_characteristic_sequence (nth idx p_list prime_2) k)
                      (pred (length (firstn i0 p_list ++ skipn (S i0) p_list))) Heq_sum).
    apply reduced_system_equation_middle with (i0 := i0); auto.
Qed.

From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq prime.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq prime div.

(* 素数整除相等 *)
Lemma prime_div_prime_eq : forall (p q : Prime),
  Nat.divide (prime_value p) (prime_value q) -> prime_value p = prime_value q.
Proof.
  intros p q Hdiv.
  destruct p as [n Hp], q as [m Hq]; simpl in *.
  destruct Hdiv as [k Hk].
  assert (Hn_gt1 : (1 < n)%nat) by (apply prime_gt1; exact Hp).
  assert (Hm_gt1 : (1 < m)%nat) by (apply prime_gt1; exact Hq).
  assert (Hn_dvd_m : (n %| m)%nat).
  { apply/dvdnP. exists k. rewrite Hk. reflexivity. }
  move/primeP: Hq => Hq_prop.
  destruct Hq_prop as [Hm_gt1' Hm_div].
  specialize (Hm_div n Hn_dvd_m).
  case/orP: Hm_div => [/eqP Heq1 | /eqP Heq2].
  - rewrite Heq1 in Hn_gt1; inversion Hn_gt1.
  - rewrite Heq2; reflexivity.
Qed.

Require Import Stdlib.Lists.List.

(* 无重复列表的不同索引对应不同元素 *)
Lemma NoDup_nth_neq : forall {A : Type} (l : list A) (d : A) (i j : nat),
  NoDup l ->
  (i < length l)%nat ->
  (j < length l)%nat ->
  i <> j ->
  nth i l d <> nth j l d.
Proof.
  intros A l d i j Hnd Hi Hj Hne.
  induction l as [|a l IH] in i, j, Hnd, Hi, Hj, Hne |- *.
  - (* l = [] *)
    simpl in Hi; inversion Hi.
  - (* l = a :: l *)
    simpl in Hi, Hj.
    inversion Hnd as [|? ? Hnin Hnd'].
    destruct i as [|i'], j as [|j'].
    + (* i = 0, j = 0 *)
      contradiction.
    + (* i = 0, j = S j' *)
      intros Heq.
      simpl in Heq.
      apply Hnin.
      rewrite Heq.
      apply nth_In.
      simpl in Hj.
      rewrite ltnS in Hj.   (* 将 (S j' < S (length l)) 转为 (j' < length l) *)
      apply/ltP: Hj.         (* 将 mathcomp 布尔命题转为标准库命题 *)
    + (* i = S i', j = 0 *)
      intros Heq.
      simpl in Heq.
      apply Hnin.
      rewrite <- Heq.
      apply nth_In.
      simpl in Hi.
      rewrite ltnS in Hi.
      apply/ltP: Hi.
    + (* i = S i', j = S j' *)
      intros Heq.
      simpl in Heq.
      apply IH with (i:=i') (j:=j'); auto.
Qed.

Import PrimeEmbedding.

(* 素数特征函数在索引 0 处等于 1 *)
Lemma prime_characteristic_zero : forall (p : Prime),
  prime_characteristic_sequence p 0 = C1.
Proof.
  intros p.
  unfold prime_characteristic_sequence.
  assert (H : (0 <? prime_value p)%nat = true).
  { apply Nat.ltb_lt.
    apply Nat.lt_le_trans with 2%nat.
    - lia.
    - apply prime_value_ge_2.
  }
  rewrite H.
  unfold Cexp; simpl.
  replace (2 * PI * 0 / INR (prime_value p)) with 0.
  - rewrite exp_0; rewrite cos_0; rewrite sin_0.
    simpl.
    unfold C1.
    f_equal; ring.
- (* 证明分母非零，从而分数为零 *)
  field.
  apply Rgt_not_eq.
  apply lt_0_INR.
  apply Nat.ltb_lt in H.
  exact H.
Qed.

(* 素数特征函数在互异素数值处取0 *)
Lemma prime_characteristic_diff : forall (p q : Prime),
  (prime_value p < prime_value q)%nat ->
  prime_characteristic_sequence p (prime_value q) = C0.
Proof.
  intros p q Hlt.
  unfold prime_characteristic_sequence.
  (* 将 mathcomp 的布尔小于转换为标准库的命题 *)
  have Hprop : (prime_value p < prime_value q)%coq_nat.
  { by apply/ltP; exact Hlt. }   (* 使用 ltP 视图 *)
  (* 由严格小于得到小于等于 *)
  have Hle : (prime_value p <= prime_value q)%coq_nat.
  { apply Nat.lt_le_incl, Hprop. }
  (* 因此 prime_value q <? prime_value p 为 false *)
  assert (H : (prime_value q <? prime_value p)%nat = false).
  { apply Nat.ltb_ge. exact Hle. }
  rewrite H.
  reflexivity.
Qed.

Require Import Stdlib.Reals.RIneq.          (* 实数不等式 *)

(* 质数特征序列单位根非零性 *)
Lemma goal : forall (p : Prime) (k : nat),
  (N.of_nat k < N.of_nat (prime_value p))%N ->
  (if (N.of_nat k <? N.of_nat (prime_value p))%N
   then Cexp (0 +i (2 * PI * INR k / INR (prime_value p)))
   else ComplexNumbers.C0) <> C0.
Proof.
  intros p k Hlt.
  apply N.ltb_lt in Hlt.
  rewrite Hlt.
  set (theta := 2 * PI * INR k / INR (prime_value p)).
  assert (Hnorm_sq : Cnorm_sq (Cexp (0 +i theta)) = 1).
  { unfold Cexp, Cnorm_sq; simpl.
    rewrite exp_0.
    rewrite Rmult_1_l.
    rewrite Rmult_1_l.
    rewrite Rplus_comm.
    apply sin2_cos2. }
  intro H; rewrite H in Hnorm_sq.
  rewrite Cnorm_sq_zero in Hnorm_sq.
  lra.
Qed.

(* 质数特征序列非零性 *)
Lemma prime_characteristic_nonzero' : forall p k,
  Nat.lt k (prime_value p) -> prime_characteristic_sequence p k <> C0.
Proof.
  intros p k Hlt.
  unfold prime_characteristic_sequence.
  assert (Hcond : (k <? prime_value p)%nat = true).
  { apply Nat.ltb_lt. exact Hlt. }
  rewrite Hcond.
  apply Cexp_neq_0.
Qed.

(* 空列表零系数 *)
Lemma base_case_empty :
  forall (p_list : list Prime) (coeffs : list Complex),
    List.length p_list = 0%nat ->
    NoDup (map prime_value p_list) ->
    List.length p_list = List.length coeffs ->
    (forall k : nat,
        Csum (fun i => let p := nth i p_list prime_2 in
                       let c := nth i coeffs C0 in
                       c *c prime_characteristic_sequence p k)
             (Nat.pred (List.length p_list)) = C0) ->
    forall i : nat, (i < List.length p_list)%nat -> nth i coeffs C0 = C0.
Proof.
  intros p_list coeffs Hlen Hdup Hlen_eq Heq i Hi.
  rewrite Hlen in Hi.
  inversion Hi.
Qed.

Local Open Scope complex_scope.

(* 复数部分和函数：Csum *)
Fixpoint Csum (f : nat -> Complex) (n : nat) : Complex :=
  match n with
  | 0 => C0
  | S k => Cadd (Csum f k) (f k)
  end.

(* 复数部分和拆分反向引理 *)
Lemma Csum_split_rev (f : nat -> Complex) (n m : nat) :
  Csum f n +c Csum (fun i => f (Nat.add n i)) m = Csum f (Nat.add n m).
Proof.
  induction m as [| m IH].
  - rewrite (Nat.add_0_r n). simpl. rewrite Cadd_0_r. reflexivity.
  - simpl. rewrite <- Cadd_assoc.
    rewrite IH.
    rewrite (Nat.add_succ_r n m).
    symmetry.
    pose proof (Csum_split_last f (Nat.add n m)) as Heq.
    symmetry in Heq.
    unfold Csum at 1 2.
    reflexivity.
Qed.

(* 辅助求和拆分 *)
Lemma sum_split_aux (f : nat -> Complex) (N i0 : nat) :
  (i0 < N)%nat ->
  Csum f (Nat.sub N 1) = C0 ->
  Csum f i0 +c Csum (fun j : nat => f (Nat.add i0 j)) (Nat.sub (Nat.sub N 1) i0) = C0.
Proof.
  intros Hlt Hsum.
  move/ltP: Hlt => Hlt_std.                    (* 布尔 → Prop *)
  apply Nat.lt_le_pred in Hlt_std.            (* i0 <= N-1 *)
  rewrite (Csum_split_rev f i0 (Nat.sub (Nat.sub N 1) i0)).
  - assert (Heq : Nat.add i0 (Nat.sub (Nat.sub N 1) i0) = Nat.sub N 1) by lia.
    rewrite Heq.
    rewrite Hsum.
    reflexivity.
Qed.

(* 必需引理：质数特征序列在 k = p-1 处非零（显式%coq_nat+零mathcomp+零污染版） *)
Lemma prime_characteristic_pred_nonzero : forall (p : Prime),
  prime_characteristic_sequence p (Nat.pred (prime_value p)) <> C0.
Proof.
  intros p.
  (* 步骤1：显式%coq_nat，完全匹配真实prime_value_ge_2签名 *)
  assert (Hp_ge2_nat : (prime_value p >= 2)%coq_nat).
  {
    apply prime_value_ge_2.
  }
  (* 步骤2：显式%coq_nat，推导 p>0 *)
  assert (Hp_pos : (0 < prime_value p)%coq_nat).
  {
    lia.
  }
  (* 步骤3：显式%coq_nat，推导 p-1 < p（标准lia自动完成） *)
  assert (Hlt : (Nat.pred (prime_value p) < prime_value p)%coq_nat).
  {
    lia.
  }
  (* 步骤4：直接复用模块内已通过的通用非零引理，一步得证 *)
  apply prime_characteristic_nonzero' with (p := p) (k := Nat.pred (prime_value p)).
  exact Hlt.
Qed.

End independent.

Export independent.

Module independent'.

(* 删除第i个元素 *)
Definition removelist (A : Type) (i : nat) (l : list A) : list A :=
  firstn i l ++ skipn (S i) l.

(* 删除元素长度减一引理 *)
Lemma length_removelist_lt : forall A (l : list A) i,
  (i < length l)%nat -> length (removelist A i l) = pred (length l).
Proof.
  intros A l i Hi.
  unfold removelist.
  rewrite length_app, length_firstn, length_skipn.
  rewrite min_l by lia.
  lia.
Qed.

(* 删除元素前缀保持 *)
Lemma nth_removelist_lt : forall A (l : list A) i j d,
  (i < length l)%nat ->
  (j < i)%nat -> nth j (removelist A i l) d = nth j l d.
Proof.
  intros A l i j d Hi Hj.
  unfold removelist.
  rewrite nth_app_left; [| rewrite length_firstn; rewrite min_l by lia; lia].
  rewrite nth_firstn_lt with (n := i) (l := l) (i := j) (d := d); auto.
Qed.

(* 删除元素后索引右移 *)
Lemma nth_removelist_ge : forall A (l : list A) i j d,
  (i < length l)%nat ->
  (j >= i)%nat -> nth j (removelist A i l) d = nth (S j) l d.
Proof.
  intros A l i j d Hi Hj.
  unfold removelist.
  rewrite nth_app_right; [| rewrite length_firstn; rewrite min_l by lia; lia].
  rewrite nth_skipn.
  rewrite length_firstn, min_l by lia.
  replace (S i + (j - i))%nat with (S j) by lia.
  reflexivity.
Qed.

(* 质数特征序列末项非零 *)
Lemma prime_characteristic_pred_nonzero : forall p,
  prime_characteristic_sequence p (prime_value p - 1) <> C0.
Proof.
  intros p.
  set (n := prime_value p).
  assert (Hn_ge2 : (2 <= n)%nat) by apply prime_value_ge_2.
  assert (Hk_lt_n : (n - 1 < n)%nat) by lia.
  unfold prime_characteristic_sequence.
  replace (prime_value p) with n by reflexivity.
  destruct (Nat.ltb_spec (n - 1) n) as [Hlt|Hge].
  - apply Cexp_neq_0.
  - exfalso; lia.
Qed.

(* 右零因子消去 *)
Lemma Cmult_zero_r_inv : forall c v, c *c v = C0 -> v <> C0 -> c = C0.
Proof.
  intros c v H Hv.
  apply Cnorm_sq_eq_0.
  apply f_equal with (f := Cnorm_sq) in H.
  rewrite Cnorm_sq_mult, Cnorm_sq_zero in H.
  apply Rmult_integral in H.
  destruct H as [Hc | Hv_sq].
  - exact Hc.
  - exfalso; apply Hv; apply Cnorm_sq_eq_0; auto.
Qed.

(* Csum等价性 *)
Lemma Csum_equiv_PrimeEmbedding :
  forall (f : nat -> Complex) (n : nat),
    Csum f n = PrimeEmbedding.Csum f n.
Proof.
  intros f n.
  induction n as [|n IH].
  - reflexivity.
  - simpl.
    rewrite IH.
    apply Cadd_comm.   (* 交换加法顺序 *)
Qed.

(* 复数求和转换到嵌入模块 *)
Lemma Csum_convert_to_PrimeEmbedding :
  forall (p_list : list Prime) (coeffs : list Complex) (k : nat)
    (Heq : Csum (fun i => nth i coeffs C0 *c prime_characteristic_sequence (nth i p_list prime_2) k)
                (length p_list) = C0),
    PrimeEmbedding.Csum (fun i => nth i coeffs C0 *c prime_characteristic_sequence (nth i p_list prime_2) k)
                       (length p_list) = C0.
Proof.
  intros p_list coeffs k Heq.
  rewrite <- Csum_equiv_PrimeEmbedding.
  exact Heq.
Qed.

(* 删除元素后长度及分解 *)
Lemma removelist_length_properties :
  forall (p_list : list Prime) (i0 : nat) (Hi0 : (i0 < length p_list)%nat),
    let N := length p_list in
    let p_list' := removelist Prime i0 p_list in
    length p_list' = pred N /\
    pred N = (i0 + (N - S i0))%nat.
Proof.
  intros p_list i0 Hi0.
  set (N := length p_list).
  set (p_list' := removelist Prime i0 p_list).
  split.
  - unfold p_list', removelist.
    rewrite !length_app, !length_firstn, !length_skipn.
    lia.
  - lia.
Qed.

(* 移除列表元素长度 *)
Lemma removelist_coeffs_length :
  forall (coeffs : list Complex) (i0 : nat) (Hi0 : (i0 < length coeffs)%nat),
    let N := length coeffs in
    length (removelist Complex i0 coeffs) = pred N.
Proof.
  intros coeffs i0 Hi0.
  unfold removelist.
  rewrite !length_app, !length_firstn, !length_skipn.
  lia.
Qed.

(* 前缀保持 *)
Lemma G_eq_F_prefix :
  forall (p_list : list Prime) (coeffs : list Complex) (i0 k : nat)
    (Hi0 : (i0 < length p_list)%nat)
    (Hlen : length p_list = length coeffs),
    let p_list' := removelist Prime i0 p_list in
    let coeffs' := removelist Complex i0 coeffs in
    let F i := nth i coeffs C0 *c prime_characteristic_sequence (nth i p_list prime_2) k in
    let G i := let p := nth i p_list' prime_2 in
               let c := nth i coeffs' C0 in
               c *c prime_characteristic_sequence p k in
    forall i, (i < i0)%nat -> G i = F i.
Proof.
  intros p_list coeffs i0 k Hi0 Hlen p_list' coeffs' F G i Hi.
  unfold G, F, p_list', coeffs', removelist.
  rewrite nth_app_left; [| rewrite length_firstn; lia].
  rewrite nth_firstn by lia.
  rewrite nth_app_left; [| rewrite length_firstn; lia].
  rewrite nth_firstn by lia.
  reflexivity.
Qed.

(* 后缀项对应 *)
Lemma G_eq_F_suffix :
  forall (p_list : list Prime) (coeffs : list Complex) (i0 k : nat)
    (Hi0 : (i0 < length p_list)%nat)
    (Hlen : length p_list = length coeffs),
    let N := length p_list in
    let p_list' := removelist Prime i0 p_list in
    let coeffs' := removelist Complex i0 coeffs in
    let F i := nth i coeffs C0 *c prime_characteristic_sequence (nth i p_list prime_2) k in
    let G i := let p := nth i p_list' prime_2 in
               let c := nth i coeffs' C0 in
               c *c prime_characteristic_sequence p k in
    forall j, (j < N - S i0)%nat -> G (i0 + j)%nat = F (S i0 + j)%nat.
Proof.
  intros p_list coeffs i0 k Hi0 Hlen N p_list' coeffs' F G j Hj.
  unfold G, F, p_list', coeffs', removelist.
  assert (Hlen_firstn_p : length (firstn i0 p_list) = i0).
  { rewrite length_firstn. apply Nat.min_l. lia. }
  assert (Hlen_firstn_c : length (firstn i0 coeffs) = i0).
  { rewrite length_firstn. apply Nat.min_l. rewrite <- Hlen; lia. }

  (* 处理 p 部分 *)
  assert (Hge_p : (i0 + j >= length (firstn i0 p_list))%nat) by (rewrite Hlen_firstn_p; lia).
  rewrite (@nth_app_right Prime (firstn i0 p_list) (skipn (S i0) p_list) (i0 + j) prime_2 Hge_p).
  rewrite nth_skipn.
  rewrite Hlen_firstn_p.
  assert (H_sub_p : (i0 + j - i0)%nat = j) by lia.
  rewrite H_sub_p.

  (* 处理 c 部分 *)
  assert (Hge_c : (i0 + j >= length (firstn i0 coeffs))%nat) by (rewrite Hlen_firstn_c; lia).
  rewrite (@nth_app_right Complex (firstn i0 coeffs) (skipn (S i0) coeffs) (i0 + j) C0 Hge_c).
  rewrite nth_skipn.
  rewrite Hlen_firstn_c.
  assert (H_sub_c : (i0 + j - i0)%nat = j) by lia.
  rewrite H_sub_c.

  reflexivity.
Qed.

(* 删除元素后长度减一 *)
Lemma length_removelist : forall {A} (i : nat) (l : list A),
  (i < length l)%nat -> length (removelist A i l) = pred (length l).
Proof.
  intros A i l H.
  Local Close Scope R_scope.  (* 确保使用 nat 算术 *)
  unfold removelist.
  rewrite length_app, length_firstn, length_skipn.
  rewrite Nat.min_l by lia.
  lia.
Qed.

(* 删除元素前缀保持 *)
Lemma nth_removelist_prefix : forall {A} (i j : nat) (l : list A) (d : A),
  (j < i)%nat -> (j < length l)%nat ->
  nth j (removelist A i l) d = nth j l d.
Proof.
  induction i as [|i IH]; intros j l d Hj Hlen.
  - lia.
  - destruct l as [|h t]; [simpl in Hlen; lia |].
    simpl. destruct j as [|j'].
    + reflexivity.
    + simpl in Hj; apply IH; [lia | simpl in Hlen; lia].
Qed.

(* 删除列表后缀索引 *)
Lemma nth_removelist_suffix : forall {A} (i j : nat) (l : list A) (d : A),
  (j >= i)%nat -> (j < length l)%nat -> (S j < length l)%nat ->
  nth j (removelist A i l) d = nth (S j) l d.
Proof.
  intros A i j l d Hge Hj_len Hj_len_S.
  unfold removelist.
  rewrite nth_app_right.
  - rewrite nth_skipn.
    rewrite length_firstn. rewrite Nat.min_l by lia.
    replace (j - length (firstn i l)) with (j - i) by (rewrite length_firstn, Nat.min_l; lia).
    f_equal. lia.
  - rewrite length_firstn. rewrite Nat.min_l by lia. lia.
Qed.

(* 复数部分和分段求和 *)
Lemma Csum_split' (f : nat -> Complex) (n m : nat) :
  Csum f (n + m) = Csum f n +c Csum (fun i => f (n + i)) m.
Proof.
  induction m as [|m IH].
  - rewrite Nat.add_0_r. simpl. rewrite Cadd_0_r. reflexivity.
  - rewrite Nat.add_succ_r. simpl.
    rewrite IH.
    rewrite Cadd_assoc.
    reflexivity.
Qed.

(* 有限和逐项相等 *)
Lemma Csum_ext' : forall (f g : nat -> Complex) (n : nat),
  (forall i, i < n -> f i = g i) -> Csum f n = Csum g n.
Proof.
  induction n as [|n IH]; intros H.
  - (* n = 0 *)
    simpl. reflexivity.
  - (* n = S n *)
    simpl. rewrite IH.
    + f_equal. apply H. lia.
    + intros i Hi. apply H. lia.
Qed.

(* 定理：零系数删除保持零和 *)
Theorem reduced_sum_eq_zero :
  forall (p_list : list Prime) (coeffs : list Complex) i0
    (Hlen : length p_list = length coeffs)
    (Hi0 : (i0 < length p_list)%nat)
    (Hc0 : nth i0 coeffs C0 = C0)
    (Heq : forall k,
        Csum (fun i => nth i coeffs C0 *c prime_characteristic_sequence (nth i p_list prime_2) k)
             (length p_list) = C0),
    forall k,
    Csum (fun i =>
            let p := nth i (removelist Prime i0 p_list) prime_2 in
            let c := nth i (removelist Complex i0 coeffs) C0 in
            c *c prime_characteristic_sequence p k)
         (length (removelist Prime i0 p_list)) = C0.
Proof.
  intros p_list coeffs i0 Hlen Hi0 Hc0 Heq k.
  set (N := length p_list).
  set (p_list' := removelist Prime i0 p_list).
  set (coeffs' := removelist Complex i0 coeffs).
  set (F := fun i : nat => nth i coeffs C0 *c prime_characteristic_sequence (nth i p_list prime_2) k).
  set (G := fun i : nat => let p := nth i p_list' prime_2 in
                     let c := nth i coeffs' C0 in
                     c *c prime_characteristic_sequence p k).

  assert (Hlen_p' : length p_list' = pred N).
  { apply length_removelist; exact Hi0. }
  rewrite Hlen_p'.

  specialize (Heq k).
  fold F in Heq.
  change (length p_list) with N in Heq.

  set (m := N - i0) in *.
  assert (Hadd : N = i0 + m) by lia.
  assert (Hm_pos : 1 <= m) by lia.
  assert (Hm_split : m = 1 + (m - 1)) by lia.

  assert (Hsplit1 : Csum F (i0 + m) = Csum F i0 +c Csum (fun j => F (i0 + j)) m).
  { apply Csum_split'. }
  rewrite Hadd in Heq.
  rewrite Hsplit1 in Heq.

  assert (Hsplit2 : Csum (fun j => F (i0 + j)) m =
                    Csum (fun j => F (i0 + j)) 1 +c
                    Csum (fun i => F (i0 + (1 + i))) (m - 1)).
  { rewrite Hm_split.
    rewrite (Csum_split' (fun j => F (i0 + j)) 1 (m - 1)).
    replace (1 + (m - 1) - 1) with (m - 1) by lia.
    reflexivity. }
  rewrite Hsplit2 in Heq.

  assert (Hsum1_eq : Csum (fun j => F (i0 + j)) 1 = F i0).
  { simpl. rewrite Nat.add_0_r. rewrite Cadd_0_l. reflexivity. }
  rewrite Hsum1_eq in Heq.

  assert (F_i0_zero : F i0 = C0).
  { unfold F. rewrite Hc0. apply Cmul_0_l. }
  rewrite F_i0_zero in Heq.
  rewrite Cadd_0_l in Heq.

  replace (pred N) with (i0 + (m - 1))%nat by (unfold N; lia).
  rewrite Csum_split'.

  (* 前缀相等 *)
  assert (Hprefix : forall i, (i < i0)%nat -> G i = F i).
  { intros i Hi. unfold G, F, p_list', coeffs', removelist.
    rewrite nth_app_left; [| rewrite length_firstn; lia].
    rewrite nth_firstn by lia.
    rewrite nth_app_left; [| rewrite length_firstn; lia].
    rewrite nth_firstn by lia.
    reflexivity. }

  (* 后缀相等 *)
  assert (Hsuffix : forall j, (j < m - 1)%nat -> G (i0 + j) = F (i0 + 1 + j)).
  { intros j Hj. unfold G, F, p_list', coeffs', removelist.
    assert (Hlen_firstn_p : length (firstn i0 p_list) = i0).
    { rewrite length_firstn. apply Nat.min_l. lia. }
    assert (Hlen_firstn_c : length (firstn i0 coeffs) = i0).
    { rewrite length_firstn. apply Nat.min_l. rewrite <- Hlen; lia. }
    assert (Hge_p : (i0 + j >= length (firstn i0 p_list))%nat) by lia.
    assert (Hge_c : (i0 + j >= length (firstn i0 coeffs))%nat) by lia.
    rewrite (nth_app_right _ (firstn i0 p_list) (skipn (S i0) p_list) (i0 + j) prime_2 Hge_p).
    rewrite nth_skipn.
    rewrite Hlen_firstn_p.
    replace (i0 + j - i0) with j by lia.
    rewrite (nth_app_right _ (firstn i0 coeffs) (skipn (S i0) coeffs) (i0 + j) C0 Hge_c).
    rewrite nth_skipn.
    rewrite Hlen_firstn_c.
    replace (i0 + j - i0) with j by lia.
    rewrite Nat.add_1_r.
    replace (S i0 + j) with (i0 + 1 + j) by lia.
    reflexivity. }

  (* 使用 Csum_ext' 证明前缀部分相等 *)
  assert (Heq1 : Csum G i0 = Csum F i0).
  { apply Csum_ext'. intros i Hi. apply Hprefix. exact Hi. }

  (* 使用 Csum_ext' 证明后缀部分相等 *)
  assert (Heq2 : Csum (fun j => G (i0 + j)) (m - 1) = Csum (fun j => F (i0 + 1 + j)) (m - 1)).
  { apply Csum_ext'. intros j Hj. rewrite Hsuffix; auto. }

  (* 重写目标中的两部分 *)
  rewrite Heq1, Heq2.
  assert (Heq3 : Csum (fun j => F (i0 + 1 + j)) (m - 1) = Csum (fun i => F (i0 + (1 + i))) (m - 1)).
  { apply Csum_ext'. intros j Hj. f_equal. lia. }
  rewrite Heq3.
  exact Heq.
Qed.

(* 零和引理 *)
Lemma sum_zero : forall (f : nat -> Complex) (n : nat),
  (forall j, (j < n)%nat -> f j = C0) -> Csum f n = C0.
Proof.
  induction n; intros H; simpl.
  - reflexivity.
  - rewrite IHn; [rewrite H; [rewrite Cadd_0_l; reflexivity | lia] | intros; apply H; lia].
Qed.

(* 单点求和化简引理 *)
Lemma Csum_reduce_to_single : forall (f : nat -> Complex) (n : nat) (idx : nat),
  (idx < n)%nat ->
  (forall j, (j < n)%nat -> (j = idx -> f j = f idx) /\ (j <> idx -> f j = C0)) ->
  Csum f n = f idx.
Proof.
  induction n as [|n IH]; intros idx Hlt Hprop.
  - lia.
  - simpl.
    destruct (Nat.eq_dec idx n) as [Heq|Hne].
    + (* idx = n *)
      subst idx.
      assert (Hsum_n : Csum f n = C0).
      { apply sum_zero. intros j Hj.
        destruct (Hprop j) as [_ Hnz]; [lia | apply Hnz; lia]. }
      rewrite Hsum_n, Cadd_0_l; reflexivity.
    + (* idx <> n *)
      assert (Hlt' : (idx < n)%nat) by lia.
      assert (Hfn : f n = C0).
      { destruct (Hprop n) as [_ Hnz]; [lia | apply Hnz; lia]. }
      rewrite Hfn, Cadd_0_r.  (* 现在目标是 Csum f n = f idx *)
      apply IH with (idx := idx).
      - exact Hlt'.
      - intros j Hj. apply Hprop. lia.
Qed.

(* 质数特征序列零系数判定引理 *)

(* 质数特征序列线性无关定理 *)
Theorem phi_linear_independent :
  forall (p_list : list Prime) (coeffs : list Complex),
    NoDup (map prime_value p_list) ->
    length p_list = length coeffs ->
    (forall k : nat,
        Csum (fun i => let p := nth i p_list prime_2 in
                       let c := nth i coeffs C0 in
                       c *c prime_characteristic_sequence p k) (length p_list) = C0) ->
    forall i, (i < length p_list)%nat -> nth i coeffs C0 = C0.
Proof.
  assert (H_main : forall (n : nat),
    forall (p_list : list Prime) (coeffs : list Complex),
      length p_list = n ->
      NoDup (map prime_value p_list) ->
      length p_list = length coeffs ->
      (forall k : nat, Csum (fun i => let p := nth i p_list prime_2 in let c := nth i coeffs C0 in c *c prime_characteristic_sequence p k) (length p_list) = C0) ->
      forall i, (i < length p_list)%nat -> nth i coeffs C0 = C0).
  {
    intros n.
    induction n as [n IH] using lt_wf_ind.
    intros p_list coeffs Hlen_n Hdup Hlen Heq i Hi.

    destruct n as [|m'].
    - simpl in Hlen_n. subst. simpl in Hi. lia.
    - assert (Hnonnil : p_list <> nil).
      { intro Hcontra. rewrite Hcontra in Hlen_n. simpl in Hlen_n. lia. }

      destruct (max_prime_index_exists p_list Hnonnil) as [i0 [Hi0_lt_m Hmax_le]].
      assert (Hmax_strict : forall j, j <> i0 -> (j < length p_list)%nat ->
        (prime_value (nth j p_list prime_2) < prime_value (nth i0 p_list prime_2))%nat).
      { apply max_prime_strict_ineq with (p_list:=p_list) (i0:=i0); auto. }

      set (M := prime_value (nth i0 p_list prime_2)).
      set (k0 := Nat.pred M).
      assert (Hk0_alt : k0 = (prime_value (nth i0 p_list prime_2) - 1)%nat).
      { unfold k0, M. assert (Hp_ge2 : (prime_value (nth i0 p_list prime_2) >= 2)%nat) by apply prime_value_ge_2. lia. }

      assert (Heq_k0 : Csum (fun i => nth i coeffs C0 *c
                               prime_characteristic_sequence (nth i p_list prime_2) k0)
                           (length p_list) = C0).
      { apply Heq. }

      set (f := fun j => nth j coeffs C0 *c prime_characteristic_sequence (nth j p_list prime_2) k0).

      assert (Hterm_zero : forall j, (j < length p_list)%nat -> j <> i0 -> f j = C0).
      { intros j Hj Hneq. unfold f. rewrite Hk0_alt.
        apply term_zero_for_others with (p_list:=p_list) (coeffs:=coeffs) (i0:=i0); auto. }

      assert (Hsum_reduce : Csum f (length p_list) = f i0).
      {
        rewrite Hlen_n.
        apply Csum_reduce_to_single with (f := f) (n := S m') (idx := i0).
        - rewrite Hlen_n in Hi0_lt_m. exact Hi0_lt_m.
        - intros j Hj. split.
          + intros ->. reflexivity.
          + intros Hneq. apply Hterm_zero; [rewrite Hlen_n; exact Hj | exact Hneq].
      }

      assert (Hfi0 : nth i0 coeffs C0 = C0).
      {
        assert (Hfi0_eq : f i0 = C0).
        { rewrite <- Hsum_reduce. exact Heq_k0. }
        unfold f in Hfi0_eq.
        assert (Hnonzero : prime_characteristic_sequence (nth i0 p_list prime_2) k0 <> C0).
        { rewrite Hk0_alt. apply prime_characteristic_pred_nonzero. }
        apply Cmult_zero_r_inv in Hfi0_eq; auto.
      }

      set (p_list' := removelist Prime i0 p_list).
      set (coeffs' := removelist Complex i0 coeffs).
      assert (Hlen' : length p_list' = length coeffs').
      { unfold p_list', coeffs', removelist.
        rewrite !length_app, !length_firstn, !length_skipn.
        rewrite <- Hlen. rewrite !Nat.min_l; lia. }
      assert (Hdup' : NoDup (map prime_value p_list')).
      { apply reduced_system_nodup; [exact Hdup | exact Hi0_lt_m]. }
      assert (Hlen_lt : length p_list' < length p_list).
      { unfold p_list', removelist.
        rewrite length_app, length_firstn, length_skipn.
        rewrite Nat.min_l by lia. lia. }

      assert (Hlen_lt_Sm' : length p_list' < S m').
      { rewrite Hlen_n in Hlen_lt. exact Hlen_lt. }
      assert (Hlen_p'_eq : length p_list' = pred (length p_list)).
      { apply length_removelist. exact Hi0_lt_m. }

      assert (Heq' : forall k, Csum (fun i =>
                 let p := nth i p_list' prime_2 in
                 let c := nth i coeffs' C0 in
                 c *c prime_characteristic_sequence p k) (length p_list') = C0).
      {
        intros k.
        apply reduced_sum_eq_zero with (p_list:=p_list) (coeffs:=coeffs) (i0:=i0); auto.
      }

      assert (H_ind : forall j, (j < length p_list')%nat -> nth j coeffs' C0 = C0).
      {
        apply (IH (length p_list') Hlen_lt_Sm' p_list' coeffs' eq_refl Hdup' Hlen' Heq').
      }

      assert (Hi0_lt_len : (i0 < length p_list)%nat) by exact Hi0_lt_m.
      assert (Hi0_lt_coeffs : (i0 < length coeffs)%nat).
      { rewrite <- Hlen. exact Hi0_lt_len. }
      destruct (eq_nat_dec i i0) as [->|Hne].
      + exact Hfi0.
      + destruct (lt_dec i i0) as [Hlt | Hgt].
        * assert (Hi' : (i < length p_list')%nat).
          { rewrite Hlen_p'_eq. lia. }
          assert (Hnth_eq : nth i coeffs' C0 = nth i coeffs C0).
          { unfold coeffs', removelist. apply nth_removelist_lt; auto. }
          rewrite <- Hnth_eq. apply H_ind; exact Hi'.
        * assert (Hineq : (i > i0)%nat) by lia.
          assert (Hi' : ((i - 1) < length p_list')%nat).
          { rewrite Hlen_p'_eq. lia. }
          assert (Hnth_eq : nth (i - 1) coeffs' C0 = nth i coeffs C0).
          {
            assert (Hj_ge_i0 : ((i - 1) >= i0)%nat) by lia.
            assert (H_Sj_eq : S (i - 1) = i) by lia.
            assert (H_lemma : nth (i - 1) coeffs' C0 = nth (S (i - 1)) coeffs C0).
            {
              apply nth_removelist_ge with (A := Complex) (l := coeffs) (i := i0) (j := (i - 1)) (d := C0).
              - exact Hi0_lt_coeffs.
              - exact Hj_ge_i0.
            }
            rewrite H_lemma. rewrite H_Sj_eq. reflexivity.
          }
          rewrite <- Hnth_eq. apply H_ind; exact Hi'.
  }
  intros p_list coeffs Hdup Hlen Heq i Hi.
  apply (H_main (length p_list) p_list coeffs eq_refl Hdup Hlen Heq i Hi).
Qed.

End independent'.

Export independent'.
