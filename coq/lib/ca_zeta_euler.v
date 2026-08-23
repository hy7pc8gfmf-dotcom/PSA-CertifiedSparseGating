(* ============================================================
   库: ca_zeta_euler —— 欧拉乘积式的构造性证明（2026-08-22 新建）
   ============================================================
   目标：在构造性实数（Stdlib.Reals.Abstract.ConstructiveCauchyReals）上
         证明欧拉乘积式：对整数 s ≥ 2，
           ζ(s) = Σ_{n≥1} n^{-s} = ∏_p (1 - p^{-s})^{-1}
         全部 Qed、零 Admitted、零经典实数公理。
   纪律（用户红线）：
     - 数学对象在 Set 层构造（CRcarrier）
     - 极限/收敛在 Prop 层（CR_cv），不用排中律
     - n^{-s} = CRpow (CR_of_Q (1/n)) s（整数幂，无超越函数）
     - 唯一分解用 mathcomp prime/div（可计算）
   记号注意：mathcomp ssrnat 把 <= / < 重载为布尔 leq/ltn（is_true 形式），
             文件内统一用 mathcomp 记号（如 (1 <= n)%nat = 0 < n 的 leq）。
   ============================================================ *)

Require Import Stdlib.QArith.QArith.
Require Import Stdlib.QArith.Qabs.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Arith.Arith.
Require Import Stdlib.Lists.List.
Require Import Stdlib.micromega.Lia.
Require Import ConstructiveReals.
Require Import ConstructiveRealsMorphisms.
Require Import ConstructiveAbs.
Require Import ConstructiveLimits.
Require Import ConstructiveSum.
Require Import ConstructivePower.
From mathcomp Require Import ssreflect ssreflect.ssrbool ssreflect.ssrfun ssreflect.ssrnat ssreflect.eqtype ssreflect.seq ssreflect.prime ssreflect.div.

(* 合并版防御：前序分区（CRTResolve 等）可能 Set Implicit Arguments 并污染本分区
   （E067/E071：合并单文件是全局命名空间 + 全局设置，不随 Require 隔离）。
   显式恢复默认：所有参数按源文件声明（显式/命名隐式）解析，杜绝自动隐式化导致
   位置传参错位（如 prime_ge1 的 p、CR_of_Q_inv_pos 的 n 被隐式化）。独立编译无副作用。 *)
Unset Implicit Arguments.

Local Open Scope ConstructiveReals.
(* 注意：不打开 Q_scope —— Q 值全部通过 Q0q/Q1q/Qinv_n 辅助构造，
   避免 Q_scope 劫持 nat 的 + / ^ / <= 记号（mathcomp 下多次出错）。 *)

(* ============================================================
   P0. 基础构造：正整数的倒数、n^{-s}、素数性质
   ============================================================ *)

(* Q 常量（避免 %positive 记号被 mathcomp 劫持） *)
Definition Q0q : Q := Stdlib.QArith.QArith_base.Qmake Z0 (Pos.of_succ_nat 0).
Definition Q1q : Q := Stdlib.QArith.QArith_base.Qmake (Zpos xH) (Pos.of_succ_nat 0).

(* 1/n 的 Q 值（n ≥ 1 时分母正确） *)
Definition Qinv_n (n : nat) : Q := Stdlib.QArith.QArith_base.Qmake 1 (Z.to_pos (Z.of_nat n)).

(* 辅助：n ≥ 2 ⟹ 1/n < 1（Q 层，纯 Z 数值证明） *)
Lemma Qinv_n_lt_1 (n : nat) (Hn : (2 <= n)%nat) :
  Qlt (Qinv_n n) (Qmake 1 1%positive).
Proof.
  unfold Qinv_n, Qlt. simpl.
  (* 目标 (1 < Z.pos (Z.to_pos (Z.of_nat n)))%Z。n ≥ 2 ⟹ Z.of_nat n ≥ 2。 *)
  (* Z.to_pos (Z.of_nat n) 当 n ≥ 1 时 = Pos.of_nat n，Z.pos 包回 = Z.of_nat n。 *)
  destruct n as [|[|n'']].
  - exfalso. rewrite leqn0 in Hn. discriminate.
  - exfalso. simpl in Hn. discriminate.
  - simpl. lia.
Qed.

(* n ≥ 1 ⟹ 1/n 是良定义的正构造实数（CR_of_Q 正性）
   前提用 mathcomp (1 <= n)%nat（= leq 1 n，is_true 形式） *)
Lemma CR_of_Q_inv_pos {R : ConstructiveReals} (n : nat) (Hn : (1 <= n)%nat) :
  CRlt R (CR_of_Q R Q0q) (CR_of_Q R (Qinv_n n)).
Proof.
  destruct n as [|n'].
  - exfalso. rewrite leqn0 in Hn. discriminate.
  - apply CR_of_Q_lt.
    simpl. unfold Qinv_n, Q0q, Qlt. simpl.
    (* 0 < 1/(n'+1)：Q 上显然，因分母为正 *)
    lia.
Qed.

(* n ≥ 1 ⟹ CR_of_Q (1#n) 与 0 相离（可逆） *)
Lemma CR_of_Q_inv_apart {R : ConstructiveReals} (n : nat) (Hn : (1 <= n)%nat) :
  CRapart R (CR_of_Q R (Qinv_n n)) (CR_of_Q R Q0q).
Proof.
  right. eapply CR_of_Q_inv_pos. exact Hn.
Qed.

(* n^{-s}：构造性整数幂（s ≥ 1，n ≥ 1）。 *)
Definition inv_n_pow {R : ConstructiveReals} (n s : nat) : CRcarrier R :=
  CRpow (CR_of_Q R (Qinv_n n)) s.

(* 素数 ≥ 2（mathcomp：prime p ⟹ 1 < p，即 2 ≤ p） *)
Lemma prime_gt1_mc (p : nat) (Hp : prime p) : (1 < p)%nat.
Proof. exact (prime_gt1 (p:=p) Hp). Qed.

(* 素数 ≥ 1（用于 CR_of_Q_inv_pos 前提） *)
Lemma prime_ge1 (p : nat) (Hp : prime p) : (1 <= p)%nat.
Proof.
  apply ltnW.
  exact (prime_gt1 (p:=p) Hp).
Qed.

(* 素数的倒数正性：p 素数 ⟹ 1/p > 0 *)
Lemma inv_prime_pos {R : ConstructiveReals} (p : nat) (Hp : prime p) :
  CRlt R (CR_of_Q R Q0q) (CR_of_Q R (Qinv_n p)).
Proof.
  apply CR_of_Q_inv_pos. exact (prime_ge1 p Hp).
Qed.

(* 素数幂 ≥ 2：p 素数，s ≥ 1 ⟹ 2 ≤ p^s（纯 nat 层，全 %nat 标注） *)
Lemma prime_pow_ge2 (p s : nat) (Hp : prime p) (Hs : (1 <= s)%nat) : (2 <= p ^ s)%nat.
Proof.
  move: Hp => /primeP [Hp_gt _].
  (* Hp_gt : (1 < p)%nat。s ≥ 1 ⟹ p^s ≥ p ≥ 2。 *)
  destruct s as [|s'].
  - exfalso. by rewrite ltn0 in Hs.
  - (* p^(S s') = p * p^s' ≥ p * 1 ≥ p ≥ 2 *)
    apply (leq_trans (m := 2) (n := p) (p := p ^ S s')).
    + exact Hp_gt.
    + (* 目标 p <= p ^ S s'。先展开 p ^ S s' = p * p ^ s'。 *)
      rewrite expnS.
      (* 目标 p <= p * p ^ s'。用 leq_pmulr：1 <= p^s'（= 0 < p^s'）。 *)
      apply leq_pmulr.
      rewrite expn_gt0. apply/orP. left. apply ltnW. exact Hp_gt.
Qed.

(* 素数的倒数与 1 相离：p ≥ 2 ⟹ 1/p^s ≶ 1（用于 1 - 1/p^s 可逆） *)
Lemma inv_prime_apart_one {R : ConstructiveReals} (p s : nat) (Hp : prime p) (Hs : (1 <= s)%nat) :
  CRapart R (CR_of_Q R (Qinv_n (p ^ s))) (CR_of_Q R Q1q).
Proof.
  left.
  apply CR_of_Q_lt.
  apply Qinv_n_lt_1.
  exact (prime_pow_ge2 p s Hp Hs).
Qed.

(* ============================================================
   L1. 几何级数（构造性）
   ============================================================ *)

(* 有限部分和：Σ_{k=0}^{K} x^k *)
Definition geom_partial {R : ConstructiveReals} (x : CRcarrier R) (K : nat) : CRcarrier R :=
  CRsum (fun k => CRpow x k) K.

(* L1a. 几何级数闭式恒等式：(1 - x) · Σ_{k=0}^K x^k == 1 - x^{K+1}
   纯代数（环公理 + 归纳），构造性。 *)

(* 辅助：- x * y == - (x * y)（负号提取，CRopp_mult_distr_l 应用） *)
Lemma CRopp_mult_l_morph {R : ConstructiveReals} (x y : CRcarrier R) :
  CReq R (CRmult R (CRopp R x) y) (CRopp R (CRmult R x y)).
Proof.
  symmetry. apply CRopp_mult_distr_l.
Qed.

(* 辅助：(1 - x) · x^{K+1} == x^{K+1} - x^{K+2} *)
Lemma geom_step {R : ConstructiveReals} (x : CRcarrier R) (K : nat) :
  CReq R (CRmult R (CRminus R (CR_of_Q R Q1q) x) (CRpow x (S K)))
       (CRminus R (CRpow x (S K)) (CRpow x (S (S K)))).
Proof.
  unfold CRminus.
  rewrite CRmult_plus_distr_r.
  - rewrite CRmult_1_l.
    (* 目标 x^(K+1) + - x * x^(K+1) == x^(K+1) + - (x * x^(K+1)) *)
    (* 展开右侧 x^(K+2) = x * x^(K+1) 成乘积形式以匹配 *)
    change (CRpow x (S (S K))) with (CRmult R x (CRpow x (S K))).
    (* 现在 - x * x^(K+1) == - (x * x^(K+1))，用负号提取 *)
    rewrite (CRopp_mult_l_morph x (CRpow x (S K))).
    reflexivity.
Qed.
Lemma geom_partial_closed {R : ConstructiveReals} (x : CRcarrier R) (K : nat) :
  CReq R (CRmult R (CRminus R (CR_of_Q R Q1q) x) (geom_partial x K))
       (CRminus R (CR_of_Q R Q1q) (CRpow x (S K))).
Proof.
  unfold geom_partial.
  induction K as [|K IH].
  - (* K=0：Σ = x^0 = 1，(1-x)·1 = 1-x *)
    simpl. unfold CRminus.
    rewrite CRmult_1_r.  (* x * 1 = x *)
    rewrite CRmult_1_r.  (* (1-x) * 1 = 1-x *)
    reflexivity.
  - (* 归纳步：Σ_{0}^{K+1} = Σ_{0}^{K} + x^{K+1} *)
    unfold geom_partial.
    (* 展开 CRsum 的递归一步（不动 CRpow） *)
    change (CRsum (fun k : nat => CRpow x k) (S K))
      with (CRsum (fun k : nat => CRpow x k) K + CRpow x (S K)).
    unfold CRminus.
    (* (1-x)·(Σ_K + x^{K+1}) == 1 - x^{K+2} *)
    rewrite CRmult_plus_distr_l.
    rewrite IH.
    (* (1 - x^{K+1}) + (1-x)·x^{K+1} == 1 - x^{K+2} *)
    rewrite (geom_step x K).
    (* (1 - x^{K+1}) + (x^{K+1} - x^{K+2}) == 1 - x^{K+2}
       展开 CRminus，用加法消去律 + 相消。 *)
    unfold CRminus.
    (* 目标 1 + -x^{K+1} + (x^{K+1} + -x^{K+2}) == 1 + -x^{K+2}
       先结合左边成 1 + (-x^{K+1} + (x^{K+1} + -x^{K+2}))。 *)
    rewrite (CRplus_assoc (CR_of_Q R Q1q) (- (CRpow x (S K))) (CRpow x (S K) + - (CRpow x (S (S K))))).
    (* 证内部相消：-x^{K+1} + (x^{K+1} + -x^{K+2}) == -x^{K+2} *)
    assert (Hc : CReq R (- (CRpow x (S K)) + (CRpow x (S K) + - (CRpow x (S (S K)))))
                  (- (CRpow x (S (S K))))).
    { (* assoc 反向：(-x^{K+1} + x^{K+1}) + -x^{K+2} *)
      rewrite <- (CRplus_assoc (- (CRpow x (S K))) (CRpow x (S K)) (- (CRpow x (S (S K))))).
      rewrite (CRplus_opp_l (CRpow x (S K))).
      rewrite (CRplus_0_l (- (CRpow x (S (S K))))).
      reflexivity. }
    (* 用 Hc 替换：1 + r1 == 1 + r2，rewrite Hc 把 r1 变 r2。 *)
    rewrite Hc.
    reflexivity.
Qed.

(* ============================================================
   L1b. 几何级数收敛（|x| < 1 ⟹ Σ x^k 收敛）
   ============================================================ *)

(* L1b0. 0 <= x < 1 ⟹ x^{k+1} <= x^k（幂序列 CRle 递减，无需 0<x 分情况）
   用 CRmult_le_compat_r：x·x^k <= 1·x^k（x <= 1，右乘 x^k ≥ 0）。 *)
Lemma CRpow_decreasing {R : ConstructiveReals} (x : CRcarrier R)
  (Hx0 : CRle R (CR_of_Q R (Qmake 0 1%positive)) x)
  (Hx1 : CRle R x (CR_of_Q R Q1q)) (k : nat) :
  CRle R (CRpow x (S k)) (CRpow x k).
Proof.
  induction k as [|k IH].
  - (* x^1 = x，x^0 = 1：x <= 1 *)
    simpl. rewrite CRmult_1_r. exact Hx1.
  - (* x^{S(S k)} = x · x^{S k}，x^{S k} = x · x^k。
       目标 x·x^{S k} <= x·x^k，即 x·(x·x^k) <= x·x^k。
       用 CRmult_le_compat_r（x <= 1，右乘 x^{S k} >= 0）：
       x·x^{S k} <= 1·x^{S k} = x^{S k}，再 IH。 *)
    simpl.
    (* 目标 x * (x * x^k) <= x * x^k。
       用 CRmult_le_compat_l（0 <= x）：x^(S k) <= x^k ⟹ x·x^(S k) <= x·x^k。 *)
    apply (CRmult_le_compat_l x (CRpow x (S k)) (CRpow x k)).
    + exact Hx0.
    + exact IH.
Qed.

(* ============================================================
   L1b. 几何级数收敛（|x| ≤ 1/2 ⟹ Σ_{k≥0} x^k 收敛，极限 (1-x)^{-1}）
   —— 构造性版本（纯 Set、零经典公理、零 Admitted）。
   范围说明：覆盖 |x| ≤ 1/2（L2 素数幂项只需 |p^{-s}| ≤ 1/2，
   p ≥ 2, s ≥ 1 ⟹ |p^{-s}| = 1/p^s ≤ 1/2）。更强的 |x| < 1 版本
   需 Q 层 q^n 衰减（Bernoulli 型），留待需要时推广（见进度文档）。
   工具链：GeoCvZero（(1/2)^n → 0）、series_cv_abs（绝对收敛 ⟹ 收敛）、
          geom_partial_closed（闭式）、x^{K+1} → 0（极限识别）。
   ============================================================ *)

(* 1/2 与 2 的 Q 常量（避开 %positive 记号被 mathcomp 劫持） *)
Definition Qhalfq : Q := Stdlib.QArith.QArith_base.Qmake (Zpos xH) (Pos.of_succ_nat 1).
Definition Qtwoq : Q := Stdlib.QArith.QArith_base.Qmake (Zpos (xO xH)) (Pos.of_succ_nat 0).

(* CRlt 不可自反（isLinearOrder 第一分量）。
   注意：CRlt 是 Set 类型的二元关系（记录字段），不能直接取 ~（需 Prop），
   故陈述为函数箭头 CRlt x x -> False。 *)
Lemma CRlt_irrefl {R : ConstructiveReals} (x : CRcarrier R) :
  CRlt R x x -> False.
Proof.
  intro H.
  exact (fst (fst (CRltLinear R)) x x H H).
Qed.

Lemma CRle_refl {R : ConstructiveReals} (x : CRcarrier R) : CRle R x x.
Proof.
  unfold CRle. exact (CRlt_irrefl (R := R) x).
Qed.

(* 0 ≤ 1 *)
Lemma CRle_0_one {R : ConstructiveReals} : CRle R (CR_of_Q R Q0q) (CR_of_Q R Q1q).
Proof.
  apply CRlt_asym. exact (CRzero_lt_one R).
Qed.

(* CReq 左乘同态：0 ≤ a ⟹ x == y ⟹ a·x == a·y *)
Lemma CRmult_eq_compat_l {R : ConstructiveReals} (a x y : CRcarrier R)
  (Ha : CRle R (CR_of_Q R Q0q) a) :
  CReq R x y -> CReq R (CRmult R a x) (CRmult R a y).
Proof.
  intro Hxy.
  destruct Hxy as [Hyx Hxy].
  unfold CReq. split.
  - exact (CRmult_le_compat_l a y x Ha Hyx).
  - exact (CRmult_le_compat_l a x y Ha Hxy).
Qed.

(* 幂单调：0 ≤ x ≤ y ⟹ x^n ≤ y^n *)
Lemma CRpow_le_compat {R : ConstructiveReals} (x y : CRcarrier R) (n : nat)
  (Hx0 : CRle R (CR_of_Q R Q0q) x)
  (Hy0 : CRle R (CR_of_Q R Q0q) y)
  (Hxy : CRle R x y) :
  CRle R (CRpow x n) (CRpow y n).
Proof.
  induction n as [|n IH].
  - simpl. apply CRle_refl.
  - simpl.
    apply (CRle_trans (R := R) (CRmult R x (CRpow x n)) (CRmult R x (CRpow y n))).
    + apply (CRmult_le_compat_l x (CRpow x n) (CRpow y n)).
      * exact Hx0.
      * exact IH.
    + apply (CRmult_le_compat_r (CRpow y n) x y).
      * exact (CRpow_ge_zero y n Hy0).
      * exact Hxy.
Qed.

(* |x^n| == |x|^n *)
Lemma CRabs_pow {R : ConstructiveReals} (x : CRcarrier R) (n : nat) :
  CReq R (CRabs R (CRpow x n)) (CRpow (CRabs R x) n).
Proof.
  induction n as [|n IH].
  - simpl.
    rewrite (CRabs_right (R := R) (CR_of_Q R Q1q) (CRle_0_one (R := R))).
    reflexivity.
  - simpl.
    rewrite (CRabs_mult (R := R) x (CRpow x n)).
    rewrite IH.
    reflexivity.
Qed.

(* CRplus 左保序（≤ 版，自建；库只有 < 版） *)
Lemma CRplus_le_compat_l {R : ConstructiveReals} (r r1 r2 : CRcarrier R)
  (H : CRle R r1 r2) : CRle R (CRplus R r r1) (CRplus R r r2).
Proof.
  unfold CRle. intro H'.
  apply H.
  exact (CRplus_lt_reg_l R r r2 r1 H').
Qed.

(* 0 < -b ⟹ b < 0 *)
Lemma CRlt_opp_0 {R : ConstructiveReals} (b : CRcarrier R) :
  CRlt R (CR_of_Q R Q0q) (CRopp R b) -> CRlt R b (CR_of_Q R Q0q).
Proof.
  intro H.
  (* H : 0 < -b。由 CRplus_lt_reg_l（左加 -b）：(-b)+b < (-b)+0 ⟹ b < 0。
     改写 (-b)+b == 0、(-b)+0 == -b 后即得 H。 *)
  apply (CRplus_lt_reg_l R (CRopp R b) b (CR_of_Q R Q0q)).
  rewrite (CRplus_opp_l b).
  rewrite (CRplus_0_r (R := R) (CRopp R b)).
  exact H.
Qed.

(* 0 ≤ b ⟹ -b ≤ 0 *)
Lemma CRopp_le_compat {R : ConstructiveReals} (b : CRcarrier R)
  (Hb0 : CRle R (CR_of_Q R Q0q) b) :
  CRle R (CRopp R b) (CR_of_Q R Q0q).
Proof.
  unfold CRle. intro H.
  apply Hb0.
  exact (CRlt_opp_0 (R := R) b H).
Qed.

(* 0 ≤ b ⟹ a - b ≤ a *)
Lemma CRle_minus_compat {R : ConstructiveReals} (a b : CRcarrier R)
  (Hb0 : CRle R (CR_of_Q R Q0q) b) :
  CRle R (CRminus R a b) a.
Proof.
  unfold CRminus.
  eapply CRle_trans.
  - apply (CRplus_le_compat_l (R := R) a (CRopp R b) (CR_of_Q R Q0q)).
    exact (CRopp_le_compat (R := R) b Hb0).
  - rewrite (CRplus_0_r (R := R) a). apply CRle_refl.
Qed.

(* x - 0 == x *)
Lemma CRminus_0_r {R : ConstructiveReals} (x : CRcarrier R) :
  CReq R (CRminus R x (CR_of_Q R Q0q)) x.
Proof.
  unfold CRminus.
  rewrite (CRopp_0 (R := R)).
  rewrite (CRplus_0_r (R := R) x).
  reflexivity.
Qed.

(* CR_of_Q 保 Qeq（Qeq 是交叉乘积的 Z 相等 ⟹ 双向 Qle ⟹ 双向 CRle） *)
Lemma CR_of_Q_Qeq {R : ConstructiveReals} (q r : Q) (H : Qeq q r) :
  CReq R (CR_of_Q R q) (CR_of_Q R r).
Proof.
  unfold CReq. split.
  - apply (CR_of_Q_le (R := R) r q). unfold Qle. unfold Qeq in H. lia.
  - apply (CR_of_Q_le (R := R) q r). unfold Qle. unfold Qeq in H. lia.
Qed.

(* 2·(1/2) == 1 *)
Lemma CR_of_Q_two_half {R : ConstructiveReals} :
  CReq R (CRmult R (CR_of_Q R Qtwoq) (CR_of_Q R Qhalfq)) (CR_of_Q R Q1q).
Proof.
  rewrite <- (CR_of_Q_mult R Qtwoq Qhalfq).
  apply CR_of_Q_Qeq.
  unfold Qeq, Qmult, Qhalfq, Qtwoq, Q1q. compute. reflexivity.
Qed.

(* 1 - 1/2 == 1/2 *)
Lemma CR_of_Q_half_minus {R : ConstructiveReals} :
  CReq R (CRminus R (CR_of_Q R Q1q) (CR_of_Q R Qhalfq)) (CR_of_Q R Qhalfq).
Proof.
  unfold CRminus, Qhalfq, Q1q.
  rewrite <- (CR_of_Q_opp (R := R) (Qmake (Zpos xH) (Pos.of_succ_nat 1))).
  rewrite <- (CR_of_Q_plus R (Qmake (Zpos xH) (Pos.of_succ_nat 0))
                            (Qopp (Qmake (Zpos xH) (Pos.of_succ_nat 1)))).
  reflexivity.
Qed.

(* 0 ≤ 2 *)
Lemma CRle_0_two {R : ConstructiveReals} : CRle R (CR_of_Q R Q0q) (CR_of_Q R Qtwoq).
Proof.
  apply CRlt_asym. apply CR_of_Q_pos.
  unfold Qtwoq. compute. reflexivity.
Qed.

(* 0 ≤ 1/2 *)
Lemma CRle_0_half {R : ConstructiveReals} : CRle R (CR_of_Q R Q0q) (CR_of_Q R Qhalfq).
Proof.
  apply CRlt_asym. apply CR_of_Q_pos.
  unfold Qhalfq. compute. reflexivity.
Qed.

(* x·(-y) == -(x·y)（由 (-x)·y == -(x·y) 与交换律推出） *)
Lemma CRopp_mult_r_morph {R : ConstructiveReals} (x y : CRcarrier R) :
  CReq R (CRmult R x (CRopp R y)) (CRopp R (CRmult R x y)).
Proof.
  rewrite (CRmult_comm (R := R) x (CRopp R y)).
  rewrite (CRmult_comm (R := R) x y).
  apply (CRopp_mult_l_morph (R := R) y x).
Qed.

(* a·x - a·y == a·(x - y) *)
Lemma CRmult_minus_distr_l {R : ConstructiveReals} (a x y : CRcarrier R) :
  CReq R (CRminus R (CRmult R a x) (CRmult R a y)) (CRmult R a (CRminus R x y)).
Proof.
  unfold CRminus.
  rewrite <- (CRopp_mult_r_morph (R := R) a y).
  rewrite <- (CRmult_plus_distr_l (R := R) a x (CRopp R y)).
  reflexivity.
Qed.

(* (1 - a) - (1 - b) == b - a（纯环代数） *)
Lemma CRminus_minus_morph {R : ConstructiveReals} (a b : CRcarrier R) :
  CReq R (CRminus R (CRminus R (CR_of_Q R Q1q) a) (CRminus R (CR_of_Q R Q1q) b))
         (CRminus R b a).
Proof.
  unfold CRminus.
  rewrite (CRopp_plus_distr (R := R) (CR_of_Q R Q1q) (CRopp R b)).
  rewrite (CRopp_involutive (R := R) b).
  (* (1 + -a) + (-1 + b) == b + -a *)
  rewrite <- (CRplus_assoc (R := R) (CRplus R (CR_of_Q R Q1q) (CRopp R a))
                            (CRopp R (CR_of_Q R Q1q)) b).
  rewrite (CRplus_assoc (R := R) (CR_of_Q R Q1q) (CRopp R a) (CRopp R (CR_of_Q R Q1q))).
  rewrite (CRplus_comm (R := R) (CRopp R a) (CRopp R (CR_of_Q R Q1q))).
  rewrite <- (CRplus_assoc (R := R) (CR_of_Q R Q1q) (CRopp R (CR_of_Q R Q1q)) (CRopp R a)).
  rewrite (CRplus_opp_r (R := R) (CR_of_Q R Q1q)).
  rewrite (CRplus_0_l (R := R) (CRopp R a)).
  rewrite (CRplus_comm (R := R) (CRopp R a) b).
  reflexivity.
Qed.

(* 2·(1/2)^(S m) == (1/2)^m *)
Lemma CR_of_Q_half_double {R : ConstructiveReals} (m : nat) :
  CReq R (CRmult R (CR_of_Q R Qtwoq) (CRpow (CR_of_Q R Qhalfq) (S m)))
         (CRpow (CR_of_Q R Qhalfq) m).
Proof.
  change (CRpow (CR_of_Q R Qhalfq) (S m))
    with (CRmult R (CR_of_Q R Qhalfq) (CRpow (CR_of_Q R Qhalfq) m)).
  rewrite <- (CRmult_assoc (R := R) (CR_of_Q R Qtwoq) (CR_of_Q R Qhalfq) (CRpow (CR_of_Q R Qhalfq) m)).
  rewrite (CR_of_Q_two_half (R := R)).
  rewrite CRmult_1_l.
  reflexivity.
Qed.

(* Σ_{k=0}^{m} (1/2)^k == 2·(1 - (1/2)^{m+1}) —— 闭式（geom_partial_closed 特化） *)
Lemma geom_sum_half_closed {R : ConstructiveReals} (m : nat) :
  CReq R (CRsum (fun k => CRpow (CR_of_Q R Qhalfq) k) m)
         (CRmult R (CR_of_Q R Qtwoq)
                  (CRminus R (CR_of_Q R Q1q) (CRpow (CR_of_Q R Qhalfq) (S m)))).
Proof.
  (* (1/2)·Σ == 1 - h^{S m}：由 geom_partial_closed 与 (1-1/2)==1/2 双向 ≤ 构造
     （避免 setoid 改写——CRpow 内嵌 1/2 的 Proper 实例未注册） *)
  assert (H : CReq R (CRmult R (CR_of_Q R Qhalfq)
                               (CRsum (fun k => CRpow (CR_of_Q R Qhalfq) k) m))
                      (CRminus R (CR_of_Q R Q1q) (CRpow (CR_of_Q R Qhalfq) (S m)))).
  { pose (G := geom_partial_closed (R := R) (CR_of_Q R Qhalfq) m).
    pose (Hm := CR_of_Q_half_minus (R := R)).
    destruct G as [GRL GLR]. destruct Hm as [Hmc Hm].
    assert (Hpos : CRle R (CR_of_Q R Q0q)
                        (CRsum (fun k => CRpow (CR_of_Q R Qhalfq) k) m)).
    { apply cond_pos_sum. intro k. exact (CRpow_ge_zero (CR_of_Q R Qhalfq) k (CRle_0_half (R := R))). }
    unfold CReq. split.
    - (* (1 - h^{S m}) ≤ (1/2)·Σ：经 L = (1-1/2)·Σ *)
      apply (CRle_trans (R := R) (CRminus R (CR_of_Q R Q1q) (CRpow (CR_of_Q R Qhalfq) (S m)))
                         (CRmult R (CRminus R (CR_of_Q R Q1q) (CR_of_Q R Qhalfq))
                                   (CRsum (fun k => CRpow (CR_of_Q R Qhalfq) k) m))
                         (CRmult R (CR_of_Q R Qhalfq)
                                  (CRsum (fun k => CRpow (CR_of_Q R Qhalfq) k) m))).
      + exact GRL.
      + apply (CRmult_le_compat_r (CRsum (fun k => CRpow (CR_of_Q R Qhalfq) k) m)
                                  (CRminus R (CR_of_Q R Q1q) (CR_of_Q R Qhalfq))
                                  (CR_of_Q R Qhalfq)).
        * exact Hpos.
        * exact Hm.
    - (* (1/2)·Σ ≤ (1 - h^{S m})：经 L *)
      apply (CRle_trans (R := R) (CRmult R (CR_of_Q R Qhalfq)
                                  (CRsum (fun k => CRpow (CR_of_Q R Qhalfq) k) m))
                         (CRmult R (CRminus R (CR_of_Q R Q1q) (CR_of_Q R Qhalfq))
                                   (CRsum (fun k => CRpow (CR_of_Q R Qhalfq) k) m))
                         (CRminus R (CR_of_Q R Q1q) (CRpow (CR_of_Q R Qhalfq) (S m)))).
      + apply (CRmult_le_compat_r (CRsum (fun k => CRpow (CR_of_Q R Qhalfq) k) m)
                                  (CR_of_Q R Qhalfq)
                                  (CRminus R (CR_of_Q R Q1q) (CR_of_Q R Qhalfq))).
        * exact Hpos.
        * exact Hmc.
      + exact GLR.
  }
  (* 两边乘 2：2·((1/2)·Σ) == 2·(1 - h^{S m}) *)
  pose (H2 := CRmult_eq_compat_l (R := R) (CR_of_Q R Qtwoq)
             (CRmult R (CR_of_Q R Qhalfq) (CRsum (fun k => CRpow (CR_of_Q R Qhalfq) k) m))
             (CRminus R (CR_of_Q R Q1q) (CRpow (CR_of_Q R Qhalfq) (S m)))
             (CRle_0_two (R := R)) H).
  (* 目标 Σ == 2(1-h^{S m})：先证 Σ == 2·(1/2·Σ)（H3，对 1/2 左消去），再与 H2 合并 *)
  assert (H3 : CReq R (CRsum (fun k => CRpow (CR_of_Q R Qhalfq) k) m)
                       (CRmult R (CR_of_Q R Qtwoq)
                                (CRmult R (CR_of_Q R Qhalfq) (CRsum (fun k => CRpow (CR_of_Q R Qhalfq) k) m)))).
  { assert (Hq : Qlt Q0q Qhalfq).
    { unfold Qhalfq. compute. reflexivity. }
    apply (CRmult_eq_reg_l (R := R) (CR_of_Q R Qhalfq)
            (CRsum (fun k => CRpow (CR_of_Q R Qhalfq) k) m)
            (CRmult R (CR_of_Q R Qtwoq)
                     (CRmult R (CR_of_Q R Qhalfq) (CRsum (fun k => CRpow (CR_of_Q R Qhalfq) k) m)))
            (inr (CR_of_Q_pos (R := R) Qhalfq Hq))).
    (* 目标：1/2·Σ == 1/2·(2·(1/2·Σ))。改写右端：== (2·1/2)·(1/2·Σ) == 1·(1/2·Σ) == 1/2·Σ *)
    rewrite <- (CRmult_assoc (R := R) (CR_of_Q R Qhalfq) (CR_of_Q R Qtwoq)
                             (CRmult R (CR_of_Q R Qhalfq) (CRsum (fun k => CRpow (CR_of_Q R Qhalfq) k) m))).
    rewrite (CRmult_comm (R := R) (CR_of_Q R Qhalfq) (CR_of_Q R Qtwoq)).
    rewrite (CR_of_Q_two_half (R := R)).
    rewrite CRmult_1_l.
    reflexivity.
  }
  rewrite H3.
  exact H2.
Qed.

(* Σ_{k=0}^{m} (1/2)^k ≤ 2 *)
Lemma geom_sum_half_le {R : ConstructiveReals} (m : nat) :
  CRle R (CRsum (fun k => CRpow (CR_of_Q R Qhalfq) k) m) (CR_of_Q R Qtwoq).
Proof.
  rewrite (geom_sum_half_closed (R := R) m).
  (* 2·(1 - h^{S m}) ≤ 2：夹到 2·1 —— 2·(1-h^{S m}) ≤ 2·1 ≤ 2 *)
  eapply CRle_trans.
  - apply (CRmult_le_compat_l (CR_of_Q R Qtwoq)
          (CRminus R (CR_of_Q R Q1q) (CRpow (CR_of_Q R Qhalfq) (S m)))
          (CR_of_Q R Q1q)).
    + exact (CRle_0_two (R := R)).
    + apply (CRle_minus_compat (R := R) (CR_of_Q R Q1q) (CRpow (CR_of_Q R Qhalfq) (S m))).
      exact (CRpow_ge_zero (CR_of_Q R Qhalfq) (S m) (CRle_0_half (R := R))).
  - rewrite (CRmult_1_r (R := R) (CR_of_Q R Qtwoq)). apply CRle_refl.
Qed.

(* Σh (max n p) - Σh (min n p) ≤ (1/2)^{min n p} —— 柯西尾部界 *)
Lemma geom_sum_half_diff {R : ConstructiveReals} (n p : nat) :
  CRle R (CRminus R (CRsum (fun k => CRpow (CR_of_Q R Qhalfq) k) (Nat.max n p))
                      (CRsum (fun k => CRpow (CR_of_Q R Qhalfq) k) (Nat.min n p)))
         (CRpow (CR_of_Q R Qhalfq) (Nat.min n p)).
Proof.
  rewrite (geom_sum_half_closed (R := R) (Nat.max n p)).
  rewrite (geom_sum_half_closed (R := R) (Nat.min n p)).
  rewrite (CRmult_minus_distr_l (R := R) (CR_of_Q R Qtwoq)
            (CRminus R (CR_of_Q R Q1q) (CRpow (CR_of_Q R Qhalfq) (S (Nat.max n p))))
            (CRminus R (CR_of_Q R Q1q) (CRpow (CR_of_Q R Qhalfq) (S (Nat.min n p))))).
  rewrite (CRminus_minus_morph (R := R) (CRpow (CR_of_Q R Qhalfq) (S (Nat.max n p)))
                                (CRpow (CR_of_Q R Qhalfq) (S (Nat.min n p)))).
  rewrite <- (CR_of_Q_half_double (R := R) (Nat.min n p)).
  apply (CRmult_le_compat_l (CR_of_Q R Qtwoq)
          (CRminus R (CRpow (CR_of_Q R Qhalfq) (S (Nat.min n p)))
                   (CRpow (CR_of_Q R Qhalfq) (S (Nat.max n p))))
          (CRpow (CR_of_Q R Qhalfq) (S (Nat.min n p)))).
  - exact (CRle_0_two (R := R)).
  - apply (CRle_minus_compat (R := R) (CRpow (CR_of_Q R Qhalfq) (S (Nat.min n p)))
                              (CRpow (CR_of_Q R Qhalfq) (S (Nat.max n p)))).
    exact (CRpow_ge_zero (CR_of_Q R Qhalfq) (S (Nat.max n p)) (CRle_0_half (R := R))).
Qed.

(* |x| ≤ 1/2 ⟹ x < 1（x ≤ |x| ≤ 1/2 < 1） *)
Lemma geom_x_lt_one {R : ConstructiveReals} (x : CRcarrier R)
  (Hx : CRle R (CRabs R x) (CR_of_Q R Qhalfq)) :
  CRlt R x (CR_of_Q R Q1q).
Proof.
  apply (CRle_lt_trans (R := R) x (CRabs R x) (CR_of_Q R Q1q)).
  - exact (CRle_abs (R := R) x).
  - apply (CRle_lt_trans (R := R) (CRabs R x) (CR_of_Q R Qhalfq) (CR_of_Q R Q1q)).
    + exact Hx.
    + apply CR_of_Q_lt. unfold Qhalfq, Q1q. compute. reflexivity.
Qed.

(* |x| ≤ 1/2 ⟹ x^n → 0（GeoCvZero 显式模 + |x^n| == |x|^n ≤ (1/2)^n） *)
Lemma geom_pow_zero {R : ConstructiveReals} (x : CRcarrier R)
  (Hx : CRle R (CRabs R x) (CR_of_Q R Qhalfq)) :
  CR_cv R (fun n => CRpow x n) (CR_of_Q R Q0q).
Proof.
  intro p.
  destruct (GeoCvZero (R := R) p) as [N HN].
  exists N.
  intro i. intro Hi.
  eapply CRle_trans.
  - rewrite (CRminus_0_r (R := R) (CRpow x i)).
    rewrite (CRabs_pow (R := R) x i).
    apply CRle_refl.
  - eapply CRle_trans.
    + apply (CRpow_le_compat (R := R) (CRabs R x) (CR_of_Q R Qhalfq) i).
      * exact (CRabs_pos (R := R) x).
      * exact (CRle_0_half (R := R)).
      * exact Hx.
    + have HNi := HN i Hi.
      rewrite (CRminus_0_r (R := R) (CRpow (CR_of_Q R Qhalfq) i)) in HNi.
      rewrite (CRabs_right (R := R) (CRpow (CR_of_Q R Qhalfq) i)
               (CRpow_ge_zero (CR_of_Q R Qhalfq) i (CRle_0_half (R := R)))) in HNi.
      exact HNi.
Qed.

(* |x| ≤ 1/2 ⟹ Σ_k |x^k| 柯西（Abs_sum_maj + 闭式尾部界 + GeoCvZero 模） *)
Lemma geom_abs_cauchy {R : ConstructiveReals} (x : CRcarrier R)
  (Hx : CRle R (CRabs R x) (CR_of_Q R Qhalfq)) :
  CR_cauchy R (CRsum (fun k => CRabs R (CRpow x k))).
Proof.
  intro p.
  destruct (GeoCvZero (R := R) p) as [N HN].
  exists N.
  intros i j Hi Hj.
  assert (Hc : forall n : nat,
          CRle R (CRabs R (CRabs R (CRpow x n))) (CRpow (CR_of_Q R Qhalfq) n)).
  { intro n.
    rewrite (CRabs_right (R := R) (CRabs R (CRpow x n)) (CRabs_pos (R := R) (CRpow x n))).
    rewrite (CRabs_pow (R := R) x n).
    apply (CRpow_le_compat (R := R) (CRabs R x) (CR_of_Q R Qhalfq) n).
    - exact (CRabs_pos (R := R) x).
    - exact (CRle_0_half (R := R)).
    - exact Hx.
  }
  pose (Hb := Abs_sum_maj (R := R) (fun k => CRabs R (CRpow x k))
                           (fun k => CRpow (CR_of_Q R Qhalfq) k) Hc i j).
  eapply CRle_trans.
  - exact Hb.
  - eapply CRle_trans.
    + exact (geom_sum_half_diff (R := R) i j).
    + have Hmin : (N <= Nat.min i j)%coq_nat.
      { exact (Nat.min_glb i j N Hi Hj). }
      have HNi := HN (Nat.min i j) Hmin.
      rewrite (CRminus_0_r (R := R) (CRpow (CR_of_Q R Qhalfq) (Nat.min i j))) in HNi.
      rewrite (CRabs_right (R := R) (CRpow (CR_of_Q R Qhalfq) (Nat.min i j))
               (CRpow_ge_zero (CR_of_Q R Qhalfq) (Nat.min i j) (CRle_0_half (R := R)))) in HNi.
      exact HNi.
Qed.

(* 主引理：|x| ≤ 1/2 ⟹ Σ x^k 收敛，极限 (1-x)^{-1}（纯构造性） *)
Lemma geom_series_cv {R : ConstructiveReals} (x : CRcarrier R)
  (Hx : CRle R (CRabs R x) (CR_of_Q R Qhalfq)) :
  { l : CRcarrier R & prod (series_cv (fun k => CRpow x k) l)
                           (CReq R l (CRinv R (CRminus R (CR_of_Q R Q1q) x)
                          (inr (CRlt_minus (R := R) x (CR_of_Q R Q1q) (geom_x_lt_one (R := R) x Hx))))) }.
Proof.
  pose (Hap := (inr (CRlt_minus (R := R) x (CR_of_Q R Q1q) (geom_x_lt_one (R := R) x Hx))
                : CRapart R (CRminus R (CR_of_Q R Q1q) x) (CR_of_Q R Q0q))).
  pose (Habs := series_cv_abs (R := R) (fun k => CRpow x k) (geom_abs_cauchy (R := R) x Hx)).
  destruct Habs as [l Hl].
  (* (1-x)·S_K → l·(1-x)（scale + 交换律） *)
  pose (Hscale := CR_cv_scale (R := R) (CRsum (fun k => CRpow x k))
                               (CRminus R (CR_of_Q R Q1q) x) l Hl).
  pose (Hscale' := CR_cv_extens (R := R)
                     (fun K : nat => CRmult R (CRsum (fun k => CRpow x k) K) (CRminus R (CR_of_Q R Q1q) x))
                     (fun K : nat => CRmult R (CRminus R (CR_of_Q R Q1q) x) (CRsum (fun k => CRpow x k) K))
                     (CRmult R l (CRminus R (CR_of_Q R Q1q) x))
                     (fun K : nat => CRmult_comm (R := R) (CRsum (fun k => CRpow x k) K) (CRminus R (CR_of_Q R Q1q) x))
                     Hscale).
  (* (1-x)·S_K → 1（闭式 + x^{S K} → 0） *)
  (* x^{S n} → 0：由 geom_pow_zero（x^n → 0）移位；
     注意 CR_cv_shift' 给出 (n + 1)%coq_nat，需与文件内 S n（mathcomp 记法）桥接 *)
  pose (Hpow0raw := CR_cv_shift' (R := R) (fun n => CRpow x n) 1 (CR_of_Q R Q0q) (geom_pow_zero (R := R) x Hx)).
  assert (Hext : forall n : nat, CReq R (CRpow x (n + 1)%coq_nat) (CRpow x (S n))).
  { intro n. rewrite (Nat.add_1_r n). reflexivity. }
  pose (Hpow0 := CR_cv_eq (R := R) (fun n : nat => CRpow x (S n))
                            (fun n : nat => CRpow x (n + 1)%coq_nat)
                            (CR_of_Q R Q0q) Hext Hpow0raw).
  pose (Hcon := CR_cv_const (R := R) (CR_of_Q R Q1q)).
  pose (Hminus := CR_cv_minus (R := R) (fun _ : nat => CR_of_Q R Q1q)
                               (fun n : nat => CRpow x (S n))
                               (CR_of_Q R Q1q) (CR_of_Q R Q0q) Hcon Hpow0).
  pose (Hproper := CR_cv_proper (R := R) (fun n : nat => CRminus R (CR_of_Q R Q1q) (CRpow x (S n)))
                                  (CRminus R (CR_of_Q R Q1q) (CR_of_Q R Q0q))
                                  (CR_of_Q R Q1q) Hminus (CRminus_0_r (R := R) (CR_of_Q R Q1q))).
  pose (Hclose := fun K : nat => geom_partial_closed (R := R) x K).
  pose (Hcv1 := CR_cv_eq (R := R)
                 (fun K : nat => CRmult R (CRminus R (CR_of_Q R Q1q) x) (CRsum (fun k => CRpow x k) K))
                 (fun K : nat => CRminus R (CR_of_Q R Q1q) (CRpow x (S K)))
                 (CR_of_Q R Q1q)
                 (fun K : nat => match Hclose K with conj H1 H2 => conj H2 H1 end)
                 Hproper).
  (* l·(1-x) == 1（极限唯一） *)
  pose (Huniq := CR_cv_unique (R := R)
                   (fun K : nat => CRmult R (CRminus R (CR_of_Q R Q1q) x) (CRsum (fun k => CRpow x k) K))
                   (CRmult R l (CRminus R (CR_of_Q R Q1q) x))
                   (CR_of_Q R Q1q) Hscale' Hcv1).
  (* l == (1-x)^{-1}：l·(1-x) == 1 == (1-x)^{-1}·(1-x)，右消元 *)
  pose (Hinv := CRinv_l R (CRminus R (CR_of_Q R Q1q) x) Hap).
  pose (Heq := conj (CRle_trans (R := R) (CRmult R (CRinv R (CRminus R (CR_of_Q R Q1q) x) Hap)
                                         (CRminus R (CR_of_Q R Q1q) x))
                                  (CR_of_Q R Q1q)
                                  (CRmult R l (CRminus R (CR_of_Q R Q1q) x))
                                  (proj2 Hinv) (proj1 Huniq))
                    (CRle_trans (R := R) (CRmult R l (CRminus R (CR_of_Q R Q1q) x))
                                  (CR_of_Q R Q1q)
                                  (CRmult R (CRinv R (CRminus R (CR_of_Q R Q1q) x) Hap)
                                          (CRminus R (CR_of_Q R Q1q) x))
                                  (proj2 Huniq) (proj1 Hinv))).
  assert (Hap0 : CRapart R (CR_of_Q R Q0q) (CRminus R (CR_of_Q R Q1q) x)).
  { exact (match Hap with inl h => inr h | inr h => inl h end). }
  pose (Hcanc := CRmult_eq_reg_r (R := R) (CRminus R (CR_of_Q R Q1q) x) l
                    (CRinv R (CRminus R (CR_of_Q R Q1q) x) Hap) Hap0 Heq).
  exists l. split.
  - exact Hl.
  - exact Hcanc.
Qed.

(* ============================================================
   L2. 素数幂项：p 素数, s ≥ 1 ⟹ Σ_k (p^{-s})^k 收敛到 (1-p^{-s})^{-1}
   —— 直接应用 L1b（|p^{-s}| = (1/p)^s ≤ 1/p ≤ 1/2）。
   ============================================================ *)

(* 0 ≤ x ≤ 1 ⟹ x^n ≤ x^m（m ≤ n，幂随指数递减；L4 尾部界也用） *)
Lemma CRpow_decreasing_ge {R : ConstructiveReals} (x : CRcarrier R) (n m : nat)
  (Hx0 : CRle R (CR_of_Q R Q0q) x)
  (Hx1 : CRle R x (CR_of_Q R Q1q))
  (Hmn : (m <= n)%nat) :
  CRle R (CRpow x n) (CRpow x m).
Proof.
  (* n = m + (n - m)：x^n == x^m·x^{n-m} ≤ x^m·1 == x^m *)
  rewrite <- (subnKC Hmn).
  rewrite <- (CRpow_plus_distr (R := R) x m (n - m)).
  eapply CRle_trans.
  - apply (CRmult_le_compat_l (CRpow x m) (CRpow x (n - m)) (CR_of_Q R Q1q)).
    + exact (CRpow_ge_zero x m Hx0).
    + rewrite <- (CRpow_one (R := R) (n - m)).
      apply (CRpow_le_compat (R := R) x (CR_of_Q R Q1q) (n - m)).
      * exact Hx0.
      * exact (CRle_0_one (R := R)).
      * exact Hx1.
  - rewrite (CRmult_1_r (R := R) (CRpow x m)). apply CRle_refl.
Qed.

(* |(1/p)^s| == (1/p)^s（1/p > 0 ⟹ 非负，绝对值可去）
   用 ≤-pair 构造（避免 setoid 改写 CRpow Proper 未注册） *)
Lemma CRabs_inv_pow {R : ConstructiveReals} (p s : nat) :
  CReq R (CRabs R (inv_n_pow p s)) (inv_n_pow p s).
Proof.
  unfold inv_n_pow.
  (* x := CR_of_Q (Qinv_n p)；0 ≤ x；|x| == x *)
  assert (Hx0 : CRle R (CR_of_Q R Q0q) (CR_of_Q R (Qinv_n p))).
  { apply CR_of_Q_le. unfold Qinv_n, Q0q, Qle. simpl. lia. }
  assert (Habsx : CReq R (CRabs R (CR_of_Q R (Qinv_n p))) (CR_of_Q R (Qinv_n p))).
  { rewrite (CR_of_Q_abs (R := R) (Qinv_n p)).
    apply (CR_of_Q_Qeq (R := R) (Qabs.Qabs (Qinv_n p)) (Qinv_n p)).
    apply Qabs.Qabs_pos.
    unfold Qinv_n, Qle. simpl. lia. }
  (* |x^s| == |x|^s（CRabs_pow）== x^s：双向 ≤ *)
  unfold CReq. split.
  - (* x^s ≤ |x^s|：x^s ≤ |x|^s ≤ |x^s| *)
    eapply CRle_trans.
    + apply (CRpow_le_compat (R := R) (CR_of_Q R (Qinv_n p)) (CRabs R (CR_of_Q R (Qinv_n p))) s).
      * exact Hx0.
      * exact (CRabs_pos (R := R) (CR_of_Q R (Qinv_n p))).
      * exact (CRle_abs (R := R) (CR_of_Q R (Qinv_n p))).
    + exact (proj1 (CRabs_pow (R := R) (CR_of_Q R (Qinv_n p)) s)).
  - (* |x^s| ≤ x^s：|x^s| ≤ |x|^s ≤ x^s *)
    eapply CRle_trans.
    + exact (proj2 (CRabs_pow (R := R) (CR_of_Q R (Qinv_n p)) s)).
    + apply (CRpow_le_compat (R := R) (CRabs R (CR_of_Q R (Qinv_n p))) (CR_of_Q R (Qinv_n p)) s).
      * exact (CRabs_pos (R := R) (CR_of_Q R (Qinv_n p))).
      * exact Hx0.
      * exact (proj2 Habsx).
Qed.

(* Q 层：p ≥ 1 ⟹ 1/p ≤ 1 *)
Lemma Qinv_n_le_one (p : nat) (Hp1 : (1 <= p)%nat) : Qle (Qinv_n p) Q1q.
Proof.
  destruct p as [|p'].
  - exfalso. rewrite leqn0 in Hp1. discriminate.
  - unfold Qinv_n, Q1q, Qle. simpl. apply (Pos2Z.pos_le_pos xH (Pos.of_succ_nat p')). apply Pos.le_1_l.
Qed.

(* Q 层：p ≥ 2 ⟹ 1/p ≤ 1/2 *)
Lemma Qinv_n_le_half (p : nat) (Hp2 : (2 <= p)%nat) : Qle (Qinv_n p) Qhalfq.
Proof.
  destruct p as [|[|p']].
  - exfalso. rewrite leqn0 in Hp2. discriminate.
  - exfalso. simpl in Hp2. discriminate.
  - unfold Qinv_n, Qhalfq, Qle. simpl.
    apply (Pos2Z.pos_le_pos (xO xH) (Pos.of_succ_nat (S p'))).
    change (Pos.succ xH <= Pos.succ (Pos.of_succ_nat p'))%positive.
    apply (proj1 (Pos.succ_le_mono xH (Pos.of_succ_nat p'))). apply Pos.le_1_l.
Qed.

(* p 素数, s ≥ 1 ⟹ |p^{-s}| ≤ 1/2
   （|p^{-s}| == (1/p)^s ≤ (1/p)^1 == 1/p ≤ 1/2） *)
Lemma inv_prime_pow_le_half {R : ConstructiveReals} (p s : nat)
  (Hp : prime p) (Hs : (1 <= s)%nat) :
  CRle R (CRabs R (inv_n_pow p s)) (CR_of_Q R Qhalfq).
Proof.
  rewrite (CRabs_inv_pow (R := R) p s).
  eapply CRle_trans.
  - apply (CRpow_decreasing_ge (R := R) (CR_of_Q R (Qinv_n p)) s 1).
    + apply CR_of_Q_le. unfold Qinv_n, Qle. simpl. lia.
    + apply CR_of_Q_le. exact (Qinv_n_le_one p (prime_ge1 p Hp)).
    + exact Hs.
  - simpl.
    rewrite (CRmult_1_r (R := R) (CR_of_Q R (Qinv_n p))).
    apply CR_of_Q_le. exact (Qinv_n_le_half p (prime_gt1_mc p Hp)).
Qed.

(* 主引理 L2：p 素数, s ≥ 1 ⟹ Σ_k (p^{-s})^k 收敛，极限 (1-p^{-s})^{-1} *)
Lemma prime_power_series {R : ConstructiveReals} (p s : nat)
  (Hp : prime p) (Hs : (1 <= s)%nat) :
  { l : CRcarrier R &
    prod (series_cv (fun k => CRpow (inv_n_pow p s) k) l)
         (CReq R l (CRinv R (CRminus R (CR_of_Q R Q1q) (inv_n_pow p s))
                          (inr (CRlt_minus (R := R) (inv_n_pow p s) (CR_of_Q R Q1q)
                                           (geom_x_lt_one (R := R) (inv_n_pow p s)
                                                          (inv_prime_pow_le_half (R := R) p s Hp Hs)))))) }.
Proof.
  exact (geom_series_cv (R := R) (inv_n_pow p s) (inv_prime_pow_le_half (R := R) p s Hp Hs)).
Qed.

(* ============================================================
   L3/L4 地基：ζ 级数收敛（s ≥ 2）
   —— Σ_{n≥1} n^{-s} 柯西收敛，尾部界 Σ_{n>A} n^{-s} ≤ 1/A（望远镜）。
   关键链：n^{-s} = (1/n)^s ≤ (1/n)^2 = 1/n² ≤ 1/(n(n-1)) = 1/(n-1) - 1/n。
   ============================================================ *)

(* Pos.of_succ_nat 单调（nat ≤ → positive ≤） *)
Lemma Pos_of_succ_nat_le (n m : nat) (Hnm : (n <= m)%nat) :
  (Pos.of_succ_nat n <= Pos.of_succ_nat m)%positive.
Proof.
  move/leP: Hnm => Hnm.
  induction Hnm as [| m' IH].
  - apply Pos.le_refl.
  - apply (Pos.le_trans _ (Pos.of_succ_nat m') _).
    + exact IHIH.
    + apply Pos.lt_le_incl. apply Pos.lt_succ_diag_r.
Qed.

(* Q 层：1/a ≤ 1/b ⟺ b ≤ a（a, b ≥ 1） *)
Lemma Qinv_n_le (a b : nat) (Ha : (1 <= a)%nat) (Hb : (1 <= b)%nat) :
  (b <= a)%nat -> Qle (Qinv_n a) (Qinv_n b).
Proof.
  intro Hba.
  destruct a as [|a'], b as [|b'].
  - exfalso. rewrite leqn0 in Ha. discriminate.
  - exfalso. rewrite leqn0 in Ha. discriminate.
  - (* a = S a', b = 0：1/(S a') ≤ 1/0 = 1（junk 值） *)
    unfold Qinv_n, Qle. simpl.
    apply (Pos2Z.pos_le_pos xH (Pos.of_succ_nat a')). apply Pos.le_1_l.
  - (* a = S a', b = S b' *)
    unfold Qinv_n, Qle. simpl.
    apply (Pos2Z.pos_le_pos (Pos.of_succ_nat b') (Pos.of_succ_nat a')).
    apply (Pos_of_succ_nat_le b' a'). exact Hba.
Qed.

(* k ≥ 1 ⟹ Z.to_pos (Z.of_nat k) = Pos.of_nat k *)
Lemma Zto_pos_of_nat (k : nat) (Hk : (1 <= k)%nat) :
  Z.to_pos (Z.of_nat k) = Pos.of_nat k.
Proof.
  destruct k as [|k'].
  - exfalso. rewrite leqn0 in Hk. discriminate.
  - rewrite <- (Pos.of_nat_succ k'). simpl. reflexivity.
Qed.

(* mathcomp (1 <= n) ⟹ n ≠ 0（stdlib） *)
Lemma one_le_neq0 (n : nat) (Hn : (1 <= n)%nat) : n <> 0%nat.
Proof.
  move=> Hn0. subst n. done.
Qed.

(* Q 层：1/(n·m) == 1/n · 1/m（n, m ≥ 1） *)
Lemma Qinv_n_mul (n m : nat) (Hn : (1 <= n)%nat) (Hm : (1 <= m)%nat) :
  Qeq (Qmult (Qinv_n n) (Qinv_n m)) (Qinv_n (n * m)).
Proof.
  unfold Qinv_n, Qmult, Qeq. simpl.
  rewrite (Zto_pos_of_nat (n * m) (leq_mul Hn Hm)).
  rewrite (Zto_pos_of_nat n Hn).
  rewrite (Zto_pos_of_nat m Hm).
  rewrite (Nat2Pos.inj_mul n m (one_le_neq0 n Hn) (one_le_neq0 m Hm)).
  reflexivity.
Qed.

(* Z.pos_sub (Pos.succ p) p = 1（分子 d2-d1 的化简） *)
Lemma Zpos_sub_succ (p : positive) : Z.pos_sub (Pos.succ p) p = 1%Z.
Proof.
  induction p as [p IH | p IH |].
  - simpl. rewrite IH. simpl. reflexivity.
  - simpl. rewrite Z.pos_sub_diag. simpl. reflexivity.
  - simpl. reflexivity.
Qed.

(* 望远镜项：n ≥ 2 ⟹ 1/(n(n-1)) == 1/(n-1) - 1/n（Q 层） *)
Lemma Qinv_n_telescope (n : nat) (Hn2 : (2 <= n)%nat) :
  Qeq (Qinv_n (n * (n - 1)))
      (Qplus (Qinv_n (n - 1)) (Qopp (Qinv_n n))).
Proof.
  destruct n as [|[|m]].
  - exfalso. rewrite leqn0 in Hn2. discriminate.
  - exfalso. simpl in Hn2. discriminate.
  - have Hp1 : (1 <= (S (S m)) * (S m))%nat := leq_mul (ltn0Sn (S m)) (ltn0Sn m).
    have Hp2 : (1 <= S m)%nat := ltn0Sn m.
    have Hp3 : (1 <= S (S m))%nat := ltn0Sn (S m).
    have Hnz : S m <> 0%nat := proj2 (Nat.neq_0_lt_0 (S m)) (Nat.lt_0_succ m).
    unfold Qinv_n, Qmult, Qplus, Qopp, Qeq.
    rewrite (Zto_pos_of_nat ((S (S m)) * (S m)) Hp1).
    rewrite (Zto_pos_of_nat (S m) Hp2).
    rewrite (Zto_pos_of_nat (S (S m)) Hp3).
    rewrite (Nat2Pos.inj_mul (S (S m)) (S m)
            (proj2 (Nat.neq_0_lt_0 (S (S m))) (Nat.lt_0_succ (S m))) Hnz).
    rewrite (Nat2Pos.inj_succ (S m) Hnz).
    rewrite (Pos.mul_comm (Pos.of_nat (S (S m))) (Pos.of_nat (S m))).
    simpl.
    rewrite (Zpos_sub_succ (Pos.of_nat (S m))).
    ring.
Qed.

(* ============================================================
   Part 1（续）：ζ 级数收敛 —— 望远镜和、尾部界、柯西、收敛
   ============================================================ *)

(* 代数：(a - b) + (b - c) == a - c（望远镜消中间项） *)
Lemma CRminus_add_cancel {R : ConstructiveReals} (a b c : CRcarrier R) :
  CReq R (CRplus R (CRminus R a b) (CRminus R b c)) (CRminus R a c).
Proof.
  unfold CRminus.
  rewrite (CRplus_assoc (R := R) a (CRopp R b) (CRplus R b (CRopp R c))).
  rewrite <- (CRplus_assoc (R := R) (CRopp R b) b (CRopp R c)).
  rewrite (CRplus_opp_l b).
  rewrite (CRplus_0_l (CRopp R c)).
  reflexivity.
Qed.

(* 移位望远镜和：Σ_{k=0}^{p} (1/(S A + k) - 1/(S (S A + k))) == 1/(S A) - 1/(S (S A + p)) *)
Lemma telescope_shift {R : ConstructiveReals} (A p : nat) :
  CReq R (CRsum (fun k : nat => CRminus R (CR_of_Q R (Qinv_n (S A + k)))
                                        (CR_of_Q R (Qinv_n (S (S A + k))))) p)
         (CRminus R (CR_of_Q R (Qinv_n (S A)))
                   (CR_of_Q R (Qinv_n (S (S A + p))))).
Proof.
  induction p as [|p IH].
  - simpl. rewrite (addn0 (S A)). reflexivity.
  - rewrite (addnS (S A) p).
    simpl.
    rewrite IH.
    (* term (S p) = 1/(S (S A + p)) - 1/(S (S (S A + p)))（addnS 已对齐指数）
       (1/(S A) - 1/(S (S A + p))) + (1/(S (S A + p)) - 1/(S (S (S A + p))))
       == 1/(S A) - 1/(S (S A + S p))；S (S A + S p) == S (S (S A + p)) *)
    rewrite (addnS (S A) p).
    apply (CRminus_add_cancel (R := R) (CR_of_Q R (Qinv_n (S A)))
                              (CR_of_Q R (Qinv_n (S (S A + p))))
                              (CR_of_Q R (Qinv_n (S (S (S A + p)))))).
Qed.

(* CRlt 0 b ⟹ CRle 0 b（CRle 是 CRlt 反向的否定式） *)
Lemma CRle_of_lt {R : ConstructiveReals} (b : CRcarrier R) :
  CRlt R (CR_of_Q R Q0q) b -> CRle R (CR_of_Q R Q0q) b.
Proof.
  intro H. unfold CRle. intro Hba.
  apply (CRlt_asym (R := R) (CR_of_Q R Q0q) b H Hba).
Qed.

(* 尾部差 ≤ 首项：Σ_{k=0}^{p} (1/(S (S N + k)) - 1/(S (S (S N + k)))) ≤ 1/(S (S N))
   —— telescope_shift (S N) 的闭式（proj2 方向）+ b ≥ 0 时 a - b ≤ a *)
Lemma zeta_tail_sum_le {R : ConstructiveReals} (N p : nat) :
  CRle R (CRsum (fun k : nat => CRminus R (CR_of_Q R (Qinv_n (S (S N + k))))
                                         (CR_of_Q R (Qinv_n (S (S (S N + k)))))) p)
         (CR_of_Q R (Qinv_n (S (S N)))).
Proof.
  eapply CRle_trans.
  - apply (proj2 (telescope_shift (R := R) (S N) p)).
  - apply (CRle_minus_compat (R := R) (CR_of_Q R (Qinv_n (S (S N))))
                                      (CR_of_Q R (Qinv_n (S (S (S N + p)))))).
    apply CRle_of_lt. apply CR_of_Q_inv_pos. exact (ltn0Sn (S (S N + p))).
Qed.

(* 差 == 尾部：S N ≤ M（stdlib le）⟹ Σ v M - Σ v N == Σ_{k=0}^{M-S N} v (S N + k)
   —— 全 stdlib nat 运算（%coq_nat），与库 sum_assoc 的 plus/minus 定义性一致；
     mathcomp addn/subn 与 stdlib plus/minus 非定义性相等，不可混用（卡点 #16 延伸） *)
Lemma CRsum_diff_tail {R : ConstructiveReals} (v : nat -> CRcarrier R) (N M : nat)
  (HNM : le (S N) M) :
  CReq R (CRminus R (CRsum v M) (CRsum v N))
         (CRsum (fun k : nat => v ((S N + k)%coq_nat)) ((M - S N)%coq_nat)).
Proof.
  have Hsplit : CReq R (CRsum v M)
          (CRplus R (CRsum v N) (CRsum (fun k : nat => v ((S N + k)%coq_nat)) ((M - S N)%coq_nat))).
  { have Hs0 := sum_assoc (R := R) v N ((M - S N)%coq_nat).
    rewrite (Nat.add_comm (S N) ((M - S N)%coq_nat)) in Hs0.
    rewrite (Nat.sub_add (S N) M HNM) in Hs0.
    exact Hs0.
  }
  unfold CRminus.
  rewrite Hsplit.
  rewrite (CRplus_assoc (R := R) (CRsum v N) (CRsum (fun k : nat => v ((S N + k)%coq_nat)) ((M - S N)%coq_nat)) (CRopp R (CRsum v N))).
  rewrite (CRplus_comm (R := R) (CRsum (fun k : nat => v ((S N + k)%coq_nat)) ((M - S N)%coq_nat)) (CRopp R (CRsum v N))).
  rewrite <- (CRplus_assoc (R := R) (CRsum v N) (CRopp R (CRsum v N)) (CRsum (fun k : nat => v ((S N + k)%coq_nat)) ((M - S N)%coq_nat))).
  rewrite (CRplus_opp_r (R := R) (CRsum v N)).
  rewrite (CRplus_0_l (R := R) (CRsum (fun k : nat => v ((S N + k)%coq_nat)) ((M - S N)%coq_nat))).
  reflexivity.
Qed.

(* 柯西尾部（max/min 版）：Σ v (max i j) - Σ v (min i j) ≤ 1/(S (S (min i j)))
   —— Abs_sum_maj 的输出形态；i = j 时尾部为 0 ≤ 正数 *)
Lemma zeta_tail_bound_v {R : ConstructiveReals} (i j : nat) :
  CRle R (CRminus R (CRsum (fun n => CRminus R (CR_of_Q R (Qinv_n (S n)))
                                           (CR_of_Q R (Qinv_n (S (S n))))) (Init.Nat.max i j))
                    (CRsum (fun n => CRminus R (CR_of_Q R (Qinv_n (S n)))
                                           (CR_of_Q R (Qinv_n (S (S n))))) (Init.Nat.min i j)))
         (CR_of_Q R (Qinv_n (S (S (Init.Nat.min i j))))).
Proof.
  destruct (le_lt_dec i j) as [Hij | Hji].
  - rewrite (Nat.max_r i j Hij).
    rewrite (Nat.min_l i j Hij).
    destruct (proj1 (Nat.lt_eq_cases i j) Hij) as [Hilt | Heq].
    + eapply CRle_trans.
      * apply (proj2 (CRsum_diff_tail (R := R) (fun n => CRminus R (CR_of_Q R (Qinv_n (S n)))
                                                            (CR_of_Q R (Qinv_n (S (S n))))) i j Hilt)).
      * apply (zeta_tail_sum_le (R := R) i ((j - S i)%N)).
    + rewrite Heq.
      eapply CRle_trans.
      * apply (proj2 (CRplus_opp_r (R := R) (CRsum (fun n => CRminus R (CR_of_Q R (Qinv_n (S n)))
                                                            (CR_of_Q R (Qinv_n (S (S n))))) j))).
      * apply CRle_of_lt. apply CR_of_Q_inv_pos. exact (ltn0Sn (S j)).
  - rewrite (Nat.max_l i j (Nat.lt_le_incl j i Hji)).
    rewrite (Nat.min_r i j (Nat.lt_le_incl j i Hji)).
    eapply CRle_trans.
    + apply (proj2 (CRsum_diff_tail (R := R) (fun n => CRminus R (CR_of_Q R (Qinv_n (S n)))
                                                          (CR_of_Q R (Qinv_n (S (S n))))) j i Hji)).
    + apply (zeta_tail_sum_le (R := R) j ((i - S j)%N)).
Qed.

(* ============================================================
   Part 1（续）：ζ 级数收敛 —— 尾部界
   对 s ≥ 2，|n^{-s}| ≤ 1/n² ≤ 1/(n(n-1))，后者望远镜。
   ============================================================ *)

(* n ≥ 2 ⟹ 1 ≤ n(n-1)（1 = 1·1 ≤ n·(n-1)：1≤n 且 1≤n-1） *)
Lemma Qmult1_ge1 (n : nat) (Hn2 : (2 <= n)%nat) : (1 <= n * (n - 1))%nat.
Proof.
  (* (1 <= k) 在 mathcomp 下即 (0 < k)。0 < n·(n-1) ⟺ 0 < n ∧ 0 < n-1。 *)
  rewrite muln_gt0. apply/andP. split.
  - exact (ltnW Hn2).
  - rewrite (subn_gt0 1 n). exact Hn2.
Qed.

(* n ≥ 2 ⟹ 1/n² ≤ 1/(n(n-1))（Q 层：n(n-1) ≤ n·n ⟹ 倒数反向） *)
Lemma Qinv_sq_le_telescope (n : nat) (Hn2 : (2 <= n)%nat) :
  Qle (Qinv_n (n * n)) (Qinv_n (n * (n - 1))).
Proof.
  apply (Qinv_n_le (n * n) (n * (n - 1))).
  - rewrite muln_gt0. apply/andP. split. exact (ltnW Hn2). exact (ltnW Hn2).
  - exact (Qmult1_ge1 n Hn2).
  - rewrite leq_mul2l. apply/orP. right. exact (leq_subr 1 n).
Qed.

(* n ≥ 1 ⟹ (1/n)^2 == 1/n²（CR 层，Qinv_n_mul 桥） *)
Lemma inv_n_pow_sq {R : ConstructiveReals} (n : nat) (Hn : (1 <= n)%nat) :
  CReq R (CRpow (CR_of_Q R (Qinv_n n)) 2) (CR_of_Q R (Qinv_n (n * n))).
Proof.
  simpl.
  rewrite (CRmult_1_r (R := R) (CR_of_Q R (Qinv_n n))).
  rewrite <- (CR_of_Q_mult R (Qinv_n n) (Qinv_n n)).
  apply (CR_of_Q_Qeq (R := R) (Qmult (Qinv_n n) (Qinv_n n)) (Qinv_n (n * n))).
  exact (Qinv_n_mul n n Hn Hn).
Qed.

(* n ≥ 2, s ≥ 2 ⟹ n^{-s} = (1/n)^s ≤ 1/n² *)
Lemma inv_n_pow_le_sq {R : ConstructiveReals} (n s : nat)
  (Hn2 : (2 <= n)%nat) (Hs2 : (2 <= s)%nat) :
  CRle R (inv_n_pow n s) (CR_of_Q R (Qinv_n (n * n))).
Proof.
  unfold inv_n_pow.
  eapply CRle_trans.
  - apply (CRpow_decreasing_ge (R := R) (CR_of_Q R (Qinv_n n)) s 2).
    + apply CR_of_Q_le. unfold Qinv_n, Qle. simpl. lia.
    + apply CR_of_Q_le. exact (Qinv_n_le n 1 (ltnW Hn2) (leqnn 1) (ltnW Hn2)).
    + exact Hs2.
  - (* (1/n)^2 ≤ 1/n²：先 ≤ 再 == *)
    eapply CRle_trans.
    + apply CRle_refl.
    + rewrite (inv_n_pow_sq (R := R) n (ltnW Hn2)). apply CRle_refl.
Qed.

(* |n^{-s}| ≤ 1/(n(n-1))（n≥2, s≥2） *)
Lemma zeta_tail_abs_le {R : ConstructiveReals} (n s : nat)
  (Hn2 : (2 <= n)%nat) (Hs2 : (2 <= s)%nat) :
  CRle R (CRabs R (inv_n_pow n s)) (CR_of_Q R (Qinv_n (n * (n - 1)))).
Proof.
  rewrite (CRabs_inv_pow (R := R) n s).
  unfold inv_n_pow.
  eapply CRle_trans.
  - apply (inv_n_pow_le_sq (R := R) n s Hn2 Hs2).
  - apply CR_of_Q_le. exact (Qinv_sq_le_telescope n Hn2).
Qed.

(* 小端尾部界：Σ_{k=1}^{N} |(S k)^{-s}| ≤ 1（s≥2；1/k² 望远镜部分和 < 2）
   —— 仅用于柯西尾部下界的辅助；实际柯西用 rest 界。 *)

(* 单点：|(S k)^{-s}| ≤ 1/k - 1/(S k)（正确望远镜配对：1/(k(k+1)) = 1/k - 1/(k+1)）
   主尾部界：A ≤ B ⟹ Σ_{k=A}^{B} |(S k)^{-s}| ≤ 1/A（telescope_unshift） *)

(* CR_of_Q 保 Q 减法：CR_of_Q (a - b) == CR_of_Q a - CR_of_Q b（CR 层桥）
   —— CR_of_Q 不是定义性环同态，Qminus 必须显式桥到 CRminus *)
Lemma CR_of_Q_minus {R : ConstructiveReals} (a b : Q) :
  CReq R (CR_of_Q R (Qminus a b))
         (CRminus R (CR_of_Q R a) (CR_of_Q R b)).
Proof.
  unfold Qminus, CRminus, CReq. split.
  - eapply CRle_trans.
    + apply (CRplus_le_compat_l (R := R) (CR_of_Q R a)
               (CRopp R (CR_of_Q R b)) (CR_of_Q R (Qopp b))).
      apply (proj1 (CR_of_Q_opp (R := R) b)).
    + apply (proj1 (CR_of_Q_plus R a (Qopp b))).
  - eapply CRle_trans.
    + apply (proj2 (CR_of_Q_plus R a (Qopp b))).
    + apply (CRplus_le_compat_l (R := R) (CR_of_Q R a)
               (CR_of_Q R (Qopp b)) (CRopp R (CR_of_Q R b))).
      apply (proj2 (CR_of_Q_opp (R := R) b)).
Qed.

(* Q 层：n ≥ 1 ⟹ 1/((S n)((S n)-1)) ≤ 1/n - 1/(S n)
   （destruct n 后 (S (S m)) - 1 对构造子可计算，Qinv_n_telescope 直接对齐；
     注意 mathcomp subn 在变量上不化简——不可在 destruct 前 rewrite） *)
Lemma Qinv_n_tail_term (n : nat) (Hn1 : (1 <= n)%nat) :
  Qle (Qinv_n ((S n) * ((S n) - 1))) (Qminus (Qinv_n n) (Qinv_n (S n))).
Proof.
  destruct n as [|m].
  - exfalso. rewrite leqn0 in Hn1. discriminate.
  - have Hsm2 : (2 <= S (S m))%nat := (leq_ltn_trans Hn1 (ltnSn (S m))).
    rewrite (Qinv_n_telescope (S (S m)) Hsm2).
    apply Qle_refl.
Qed.

(* 逐项 ≤：|(S n)^{-s}| ≤ 1/n - 1/(S n)（n ≥ 1, s ≥ 2；正确的望远镜配对）
   —— 注意：|(S n)^{-s}| 不可用 1/(S n) - 1/(S (S n)) 界（数学为假：
   1/(n+1)² ≥ 1/((n+1)(n+2))），必须配 1/n - 1/(S n)。 *)
Lemma zeta_tail_term_le {R : ConstructiveReals} (n s : nat) (Hs2 : (2 <= s)%nat)
  (Hn1 : (1 <= n)%nat) :
  CRle R (CRabs R (inv_n_pow (S n) s))
         (CRminus R (CR_of_Q R (Qinv_n n)) (CR_of_Q R (Qinv_n (S n)))).
Proof.
  have Hsn2 : (2 <= S n)%nat := (leq_ltn_trans Hn1 (ltnSn n)).
  (* |(S n)^{-s}| ≤ 1/((S n)((S n)-1)) == 1/n - 1/(S n) *)
  eapply CRle_trans.
  - apply (zeta_tail_abs_le (R := R) (S n) s Hsn2 Hs2).
  - eapply CRle_trans.
    + apply (CR_of_Q_le (R := R) (Qinv_n ((S n) * ((S n) - 1)))
                                 (Qminus (Qinv_n n) (Qinv_n (S n)))).
      exact (Qinv_n_tail_term n Hn1).
    + apply (proj2 (CR_of_Q_minus (R := R) (Qinv_n n) (Qinv_n (S n)))).
Qed.

(* ============================================================
   Part 1（续）：ζ 级数收敛 —— 柯西条件与收敛
   ============================================================ *)

(* 1/(S (S (Pos.to_nat p))) ≤ 1/p（Q 层；S(S(Pos.to_nat p)) 作为 positive = succ(succ p) ≥ p）
   —— CR_cauchy 的界是 CR_of_Q (1#p)，柯西取点 N = Pos.to_nat p 时收口 *)
Lemma Qinv_n_S2_to_nat_le (p : positive) :
  Qle (Qinv_n (S (S (Pos.to_nat p)))) (Qmake 1 p).
Proof.
  unfold Qinv_n, Qle. simpl.
  apply (Pos2Z.pos_le_pos p (Pos.succ (Pos.of_succ_nat (Pos.to_nat p)))).
  rewrite (Pos.of_nat_succ (Pos.to_nat p)).
  rewrite <- (Pos2Nat.inj_succ p).
  rewrite (Pos2Nat.id (Pos.succ p)).
  apply (Pos.le_trans p (Pos.succ p) (Pos.succ (Pos.succ p))).
  - apply Pos.lt_le_incl. exact (Pos.lt_succ_diag_r p).
  - apply Pos.lt_le_incl. exact (Pos.lt_succ_diag_r (Pos.succ p)).
Qed.

(* ζ 级数（项 2 起）的绝对值级数柯西：
   CRsum (fun n => |(S (S n))^{-s}|) 是柯西列（CR_cauchy，p 取 N = Pos.to_nat p）
   —— 镜像 geom_abs_cauchy：逐点界 zeta_tail_term_le + Abs_sum_maj +
     zeta_tail_bound_v + 1/(min+2) ≤ 1/(N+2) ≤ 1/p *)
Lemma zeta_abs_cauchy {R : ConstructiveReals} (s : nat) (Hs2 : (2 <= s)%nat) :
  CR_cauchy R (CRsum (fun n => CRabs R (inv_n_pow (S (S n)) s))).
Proof.
  intro p.
  exists (Pos.to_nat p).
  intros i j Hi Hj.
  assert (Hc : forall n : nat,
          CRle R (CRabs R (CRabs R (inv_n_pow (S (S n)) s)))
                 (CRminus R (CR_of_Q R (Qinv_n (S n))) (CR_of_Q R (Qinv_n (S (S n)))))).
  { intro n.
    rewrite (CRabs_right (R := R) (CRabs R (inv_n_pow (S (S n)) s))
                         (CRabs_pos (R := R) (inv_n_pow (S (S n)) s))).
    apply (zeta_tail_term_le (R := R) (S n) s Hs2 (ltn0Sn n)).
  }
  pose (Hb := Abs_sum_maj (R := R) (fun n => CRabs R (inv_n_pow (S (S n)) s))
                           (fun n => CRminus R (CR_of_Q R (Qinv_n (S n))) (CR_of_Q R (Qinv_n (S (S n))))) Hc i j).
  eapply CRle_trans.
  - exact Hb.
  - eapply CRle_trans.
    + apply (zeta_tail_bound_v (R := R) i j).
    + eapply CRle_trans.
      * apply (CR_of_Q_le (R := R) (Qinv_n (S (S (Init.Nat.min i j))))
                                   (Qinv_n (S (S (Pos.to_nat p))))).
        apply (Qinv_n_le (S (S (Init.Nat.min i j))) (S (S (Pos.to_nat p)))
                         (ltn0Sn (S (Init.Nat.min i j))) (ltn0Sn (S (Pos.to_nat p)))).
        apply/leP. apply le_n_S. apply le_n_S.
        exact (Nat.min_glb i j (Pos.to_nat p) Hi Hj).
      * apply (CR_of_Q_le (R := R) (Qinv_n (S (S (Pos.to_nat p)))) (Qmake 1 p)).
        exact (Qinv_n_S2_to_nat_le p).
Qed.

(* ζ 级数（项 2 起）收敛：Σ_{n≥0} (S (S n))^{-s}（s ≥ 2）
   —— 绝对收敛（series_cv_abs）⟹ 收敛（series_cv_abs_cv）
   ★ 可复用：ζ 部分和/主定理 L3/L4 的收敛性基础 *)
Lemma zeta_series_cv {R : ConstructiveReals} (s : nat) (Hs2 : (2 <= s)%nat) :
  { l : CRcarrier R & series_cv (fun n => inv_n_pow (S (S n)) s) l }.
Proof.
  exists (projT1 (series_cv_abs (R := R) (fun n => inv_n_pow (S (S n)) s)
                                 (zeta_abs_cauchy (R := R) s Hs2))).
  apply (series_cv_abs_cv (R := R) (fun n => inv_n_pow (S (S n)) s)
                           (zeta_abs_cauchy (R := R) s Hs2)).
Qed.

(* ============================================================
   L3 基础件：有限乘积 CRprod 与分布律
   （欧拉乘积 ∏_p (Σ_e p^{-es}) 的展开需要「乘积 × 和 = 逐项积之和」）
   ============================================================ *)

(* 有限乘积：CRprod f n = f 0 * f 1 * ... * f n（构造性实数的有限积） *)
Fixpoint CRprod {R : ConstructiveReals} (f : nat -> CRcarrier R) (n : nat) : CRcarrier R :=
  match n with
  | O => f O
  | S n' => CRmult R (CRprod f n') (f (S n'))
  end.

(* 有限乘积 ≥ 0：逐项 ≥ 0 ⟹ CRprod f n ≥ 0 *)
Lemma CRprod_ge_zero {R : ConstructiveReals} (f : nat -> CRcarrier R) (n : nat)
  (Hf : forall k, CRle R (CR_of_Q R Q0q) (f k)) :
  CRle R (CR_of_Q R Q0q) (CRprod f n).
Proof.
  induction n as [|n IH].
  - simpl. apply Hf.
  - simpl. apply (CRmult_le_0_compat (R := R) (CRprod f n) (f (S n)) IH (Hf (S n))).
Qed.

(* 分布律（核心）：(Σ_{i=0}^{N} f i) * x == Σ_{i=0}^{N} (f i * x) *)
Lemma CRsum_mult_r {R : ConstructiveReals} (f : nat -> CRcarrier R) (N : nat) (x : CRcarrier R) :
  CReq R (CRmult R (CRsum f N) x) (CRsum (fun i => CRmult R (f i) x) N).
Proof.
  induction N as [|N IH].
  - simpl. reflexivity.
  - simpl.
    rewrite (CRmult_plus_distr_r (R := R) x (CRsum f N) (f (S N))).
    rewrite IH.
    reflexivity.
Qed.

(* 乘入和（右）：x * (Σ f) == Σ (x * f i) *)
Lemma CRsum_mult_l {R : ConstructiveReals} (f : nat -> CRcarrier R) (N : nat) (x : CRcarrier R) :
  CReq R (CRmult R x (CRsum f N)) (CRsum (fun i => CRmult R x (f i)) N).
Proof.
  induction N as [|N IH].
  - simpl. reflexivity.
  - simpl.
    rewrite (CRmult_plus_distr_l (R := R) x (CRsum f N) (f (S N))).
    rewrite IH.
    reflexivity.
Qed.

(* 欧拉乘积展开的原子步：CRprod f N * (Σ_{e=0}^{M} g e) == Σ_e (CRprod f N * g e)
   —— 逐步乘入每个素因子（1-p^{-s})^{-1} = Σ_e p^{-es} 的和式 *)
Lemma CRprod_sum_expand {R : ConstructiveReals} (f : nat -> CRcarrier R) (N : nat)
  (g : nat -> CRcarrier R) (M : nat) :
  CReq R (CRmult R (CRprod f N) (CRsum g M))
         (CRsum (fun e => CRmult R (CRprod f N) (g e)) M).
Proof.
  apply (CRsum_mult_l (R := R) g M (CRprod f N)).
Qed.

(* K+1 重嵌套和：Σ_{e_K=0}^{E} ... Σ_{e_0=0}^{E} ∏_{i=0}^{K} f i e_i
   —— 展开等价于 ∏_{i=0}^{K} (Σ_{e=0}^{E} f i e)（CRprod_expand 归纳）
   ★ 可复用：欧拉乘积 ∏_p (Σ_e p^{-es}) 的展开骨架（指数元组和） *)
Fixpoint nested_prod_sum {R : ConstructiveReals} (f : nat -> nat -> CRcarrier R) (K E : nat) : CRcarrier R :=
  match K with
  | O => CRsum (fun e => f O e) E
  | S K' => CRsum (fun e => CRmult R (nested_prod_sum f K' E) (f (S K') e)) E
  end.

(* ∏_{i=0}^{K} (Σ_{e=0}^{E} f i e) == nested_prod_sum f K E
   —— 逐步乘入：IH + CRsum_mult_l 反向（Σ (x·f) == x·(Σ f)） *)
Lemma CRprod_expand {R : ConstructiveReals} (f : nat -> nat -> CRcarrier R) (K E : nat) :
  CReq R (CRprod (fun i => CRsum (fun e => f i e) E) K)
         (nested_prod_sum f K E).
Proof.
  induction K as [|K IH].
  - simpl. reflexivity.
  - simpl.
    rewrite IH.
    rewrite <- (CRsum_mult_l (R := R) (fun e => f (S K) e) E (nested_prod_sum f K E)).
    reflexivity.
Qed.

(* (n·m)^{-s} == n^{-s} · m^{-s}（s ≥ 0，n, m ≥ 1）
   —— smooth 数配对的核心项等式：n^{-s} · p^{-es} = (n·p^e)^{-s} *)
Lemma inv_n_pow_mult {R : ConstructiveReals} (n m s : nat)
  (Hn : (1 <= n)%nat) (Hm : (1 <= m)%nat) :
  CReq R (inv_n_pow (n * m) s) (CRmult R (inv_n_pow n s) (inv_n_pow m s)).
Proof.
  unfold inv_n_pow.
  rewrite (CRpow_mult (R := R) (CR_of_Q R (Qinv_n n)) (CR_of_Q R (Qinv_n m)) s).
  apply (CRpow_proper (R := R) (CR_of_Q R (Qinv_n (n * m)))
                                (CRmult R (CR_of_Q R (Qinv_n n)) (CR_of_Q R (Qinv_n m))) s).
  eapply CReq_trans.
  - apply (CR_of_Q_Qeq (R := R) (Qinv_n (n * m)) (Qmult (Qinv_n n) (Qinv_n m))).
    exact (Qeq_sym (Qmult (Qinv_n n) (Qinv_n m)) (Qinv_n (n * m)) (Qinv_n_mul n m Hn Hm)).
  - exact (CR_of_Q_mult R (Qinv_n n) (Qinv_n m)).
Qed.

(* 双重和分布律：(Σ_{i=0}^{N} f i) · (Σ_{j=0}^{M} g j) == Σ_{i=0}^{N} Σ_{j=0}^{M} (f i · g j)
   —— 欧拉乘积展开的核心：每步把新因子的和式乘入已展开的和式 *)
Lemma CRsum_mult_sum {R : ConstructiveReals} (f g : nat -> CRcarrier R) (N M : nat) :
  CReq R (CRmult R (CRsum f N) (CRsum g M))
         (CRsum (fun i => CRsum (fun j => CRmult R (f i) (g j)) M) N).
Proof.
  rewrite (CRsum_mult_r (R := R) f N (CRsum g M)).
  apply (CRsum_eq (R := R) (fun i => CRmult R (f i) (CRsum g M))
                            (fun i => CRsum (fun j => CRmult R (f i) (g j)) M) N).
  intros k Hk.
  apply (CRsum_mult_l (R := R) g M (f k)).
Qed.

(* 展开核心：Σ_{n=0}^{N} Σ_{e=0}^{E} (S n · p^e)^{-s}
      == (Σ_{n=0}^{N} (S n)^{-s}) · (Σ_{e=0}^{E} (p^e)^{-s})
   —— 分布律（CRsum_mult_sum）+ inv_n_pow_mult；L3 每步乘入新素因子 p 的代数核心 *)
Lemma geom_shift_expand {R : ConstructiveReals} (p s N E : nat) (Hp : (1 <= p)%nat) :
  CReq R (CRsum (fun n => CRsum (fun e => inv_n_pow (S n * p ^ e) s) E) N)
         (CRmult R (CRsum (fun n => inv_n_pow (S n) s) N)
                       (CRsum (fun e => inv_n_pow (p ^ e) s) E)).
Proof.
  rewrite (CRsum_mult_sum (R := R) (fun n => inv_n_pow (S n) s)
                           (fun e => inv_n_pow (p ^ e) s) N E).
  apply (CRsum_eq (R := R)
     (fun n => CRsum (fun e => inv_n_pow (S n * p ^ e) s) E)
     (fun n => CRsum (fun e => CRmult R (inv_n_pow (S n) s) (inv_n_pow (p ^ e) s)) E) N).
  intros n Hn.
  apply (CRsum_eq (R := R)
     (fun e => inv_n_pow (S n * p ^ e) s)
     (fun e => CRmult R (inv_n_pow (S n) s) (inv_n_pow (p ^ e) s)) E).
  intros e He.
  apply (inv_n_pow_mult (R := R) (S n) (p ^ e) s (ltn0Sn n)).
  rewrite expn_gt0. rewrite Hp. simpl. reflexivity.
Qed.

(* smooth 判定：n 的所有素因子 ≤ P（mathcomp primes = prime_decomp 的素数列表）
   —— L3 配对层的 smooth 数集合谓词；乘入保持引理（smooth_le_mul_pow）见交接文档 §L3 配对层 *)
Definition smooth_le (P n : nat) : bool :=
  all (fun p => (p <= P)%nat) (primes n).

(* p ≤ P、n smooth、p ∉ primes n、p 素数 ⟹ n·p^e smooth（乘入 p 保持）
   —— 配对「LHS 展开项 ⊆ RHS smooth 项」的一侧：
     q ∈ primes (n·p^e)：q = p ⟹ q ≤ P；q ≠ p ⟹ q ∤ p^e（素因子唯一）⟹
     Gauss 消去 q | n ⟹ q ∈ primes n ⟹ q ≤ P。
   —— 注意 mathcomp 引理（lognM/prime_coprime 等）的 nat 参数是命名隐式的，
     必须用 @ 全显式调用（Check 显示会误导）。 *)
Lemma smooth_le_mul_pow (P p n e : nat) (Hp : prime p) (HpP : (p <= P)%nat)
  (Hs : smooth_le P n) (Hpn : ~~ (p \in primes n)) : smooth_le P (n * p ^ e).
Proof.
  apply/allP. move => q Hq.
  rewrite mem_primes in Hq.
  move/andP : Hq => [Hqpr /andP [Hqpos Hqdvd]].
  destruct (Nat.eqb_spec q p) as [Heq | Hne].
  - move: Heq => ->. exact HpP.
  - have Hqcop_p : coprime q p.
    { rewrite (@prime_coprime q p Hqpr).
      rewrite (@dvdn_prime2 q p Hqpr Hp).
      apply/eqP. exact Hne. }
    have Hqcop : coprime q (p ^ e).
    { rewrite coprime_sym.
      apply (@coprimeXl e p q).
      rewrite coprime_sym. exact Hqcop_p. }
    have Hqdvdn : q %| n.
    { rewrite (mulnC n (p ^ e)%N) in Hqdvd.
      move: Hqdvd. rewrite (@Gauss_dvdr q (p ^ e)%N n Hqcop). exact id. }
    have Hqin : q \in primes n.
    { rewrite mem_primes. apply/andP. split. exact Hqpr. apply/andP. split.
      - rewrite muln_gt0 in Hqpos. destruct (andP Hqpos) as [Hqn0 _]. exact Hqn0.
      - exact Hqdvdn. }
    move: Hs. rewrite /smooth_le. move => /allP Hs'. exact (Hs' q Hqin).
Qed.

(* n·p^e smooth 且 p ∤ n（p 素数）⟹ n smooth（去掉 p 因子仍 smooth）
   —— 配对反向：q ∈ primes n ⟹ q | n ⟹ q | n·p^e ⟹ q ∈ primes (n·p^e) ⟹ q ≤ P *)
Lemma smooth_le_div_pow (P p n e : nat) (Hp : prime p)
  (Hs : smooth_le P (n * p ^ e)) (Hpn : ~~ (p %| n)) : smooth_le P n.
Proof.
  apply/allP. move => q Hq.
  rewrite mem_primes in Hq.
  move/andP : Hq => [Hqpr /andP [Hqn0 Hqdvd]].
  have Hqdvd' : q %| n * p ^ e.
  { rewrite (mulnC n (p ^ e)%N). apply (dvdn_mull (p ^ e)%N). exact Hqdvd. }
  have Hpe0 : (0 < p ^ e)%nat.
  { rewrite expn_gt0. rewrite (@prime_gt0 p Hp). simpl. reflexivity. }
  have Hqin : q \in primes (n * p ^ e).
  { rewrite mem_primes. apply/andP. split. exact Hqpr. apply/andP. split.
    - rewrite muln_gt0. apply/andP. split. exact Hqn0. exact Hpe0.
    - exact Hqdvd'. }
  move: Hs. rewrite /smooth_le. move => /allP Hs'. exact (Hs' q Hqin).
Qed.

(* 配对单射：p 素数、p∤n1、p∤n2 ⟹ n1·p^{e1} = n2·p^{e2} ⟹ n1 = n2 ∧ e1 = e2
   —— logn p 两侧：logn p (ni·p^{ei}) = logn p ni + ei·(p==p) = ei；
     再消去 p^{e1}（eqn_pmul2l）得 n1 = n2。这是 (n,e) ↦ n·p^e 双射的单射半边。 *)
Lemma smooth_pair_inj (p n1 n2 e1 e2 : nat) (Hp : prime p)
  (Hpn1 : ~~ (p %| n1)) (Hpn2 : ~~ (p %| n2))
  (H : (n1 * p ^ e1)%N = (n2 * p ^ e2)%N) : n1 = n2 /\ e1 = e2.
Proof.
  have Hn10 : (0 < n1)%nat.
  { destruct n1 as [|n1'].
    - exfalso. move/negP : Hpn1 => Hpn1'. apply Hpn1'. exact (dvdn0 p).
    - apply ltn0Sn. }
  have Hn20 : (0 < n2)%nat.
  { destruct n2 as [|n2'].
    - exfalso. move/negP : Hpn2 => Hpn2'. apply Hpn2'. exact (dvdn0 p).
    - apply ltn0Sn. }
  have Hpe10 : (0 < p ^ e1)%nat.
  { rewrite expn_gt0. rewrite (@prime_gt0 p Hp). simpl. reflexivity. }
  have Hpe20 : (0 < p ^ e2)%nat.
  { rewrite expn_gt0. rewrite (@prime_gt0 p Hp). simpl. reflexivity. }
  have Hcop1 : coprime p n1.
  { rewrite (@prime_coprime p n1 Hp). exact Hpn1. }
  have Hcop2 : coprime p n2.
  { rewrite (@prime_coprime p n2 Hp). exact Hpn2. }
  have Hlg1 : logn p (n1 * p ^ e1) = e1.
  { rewrite (@lognM p n1 (p ^ e1)%N Hn10 Hpe10).
    rewrite (@logn_coprime p n1 Hcop1).
    rewrite (@lognX p p e1).
    rewrite (@logn_prime p p Hp).
    rewrite eqxx. rewrite muln1. rewrite add0n. reflexivity. }
  have Hlg2 : logn p (n2 * p ^ e2) = e2.
  { rewrite (@lognM p n2 (p ^ e2)%N Hn20 Hpe20).
    rewrite (@logn_coprime p n2 Hcop2).
    rewrite (@lognX p p e2).
    rewrite (@logn_prime p p Hp).
    rewrite eqxx. rewrite muln1. rewrite add0n. reflexivity. }
  have Heq : logn p (n1 * p ^ e1) = logn p (n2 * p ^ e2).
  { rewrite H. reflexivity. }
  have Hlg : e1 = e2.
  { rewrite Hlg1 in Heq. rewrite Hlg2 in Heq. exact Heq. }
  have Hmul : (n1 * p ^ e1)%N = (n2 * p ^ e1)%N.
  { rewrite <- Hlg in H. exact H. }
  have Hn1n2 : n1 = n2.
  { apply/eqP.
    rewrite <- (@eqn_pmul2l (p ^ e1)%N n1 n2 Hpe10).
    apply/eqP.
    rewrite (mulnC (p ^ e1)%N n1) (mulnC (p ^ e1)%N n2).
    exact Hmul. }
  split; assumption.
Qed.

(* ============================================================
   L3 配对层（续）：smooth 数列表枚举与列表求和
   有限欧拉乘积 ∏_{p∈ps} (Σ_{e≤E} p^{-es}) == Σ_{x∈smooth_list E ps} x^{-s}
   ============================================================ *)

(* 列表求和（CR 层）：Σ_{x ∈ l} f x（元素类型泛化 A） *)
Fixpoint CRsum_list {R : ConstructiveReals} {A : Type} (f : A -> CRcarrier R) (l : seq A) : CRcarrier R :=
  match l with
  | [::] => CR_of_Q R Q0q
  | x :: xs => CRplus R (f x) (CRsum_list f xs)
  end.

(* 列表乘积（CR 层）：∏_{x ∈ l} f x（空积 = 1） *)
Fixpoint CRprod_list {R : ConstructiveReals} (f : nat -> CRcarrier R) (l : seq nat) : CRcarrier R :=
  match l with
  | [::] => CR_of_Q R Q1q
  | p :: ps => CRmult R (f p) (CRprod_list f ps)
  end.

(* 指数 ≤ E 且素因子 ⊆ ps 的数列表（递归构造；唯一分解保证元素互异）
   —— smooth_list E [] = [1]；smooth_list E (p::ps) = [x·p^e | x ∈ smooth_list E ps, e ≤ E] *)
Fixpoint smooth_list (E : nat) (ps : seq nat) : seq nat :=
  match ps with
  | [::] => [:: 1%nat]
  | p :: ps' => [seq (x * p ^ e)%N | x <- smooth_list E ps', e <- iota 0 (E + 1)%N]
  end.

(* 列表求和对 ++ 的分配：Σ_{y ∈ l1++l2} f y == Σ_{y∈l1} f y + Σ_{y∈l2} f y *)
Lemma CRsum_list_cat {R : ConstructiveReals} {A : Type} (f : A -> CRcarrier R) (l1 l2 : seq A) :
  CReq R (CRsum_list f (l1 ++ l2)) (CRplus R (CRsum_list f l1) (CRsum_list f l2)).
Proof.
  elim: l1 => [| x l1' IH] /=.
  - rewrite (CRplus_0_l (R := R) (CRsum_list f l2)). reflexivity.
  - rewrite IH. rewrite (CRplus_assoc (R := R) (f x) (CRsum_list f l1') (CRsum_list f l2)). reflexivity.
Qed.

(* 列表求和分配（concat/map）：Σ_{y ∈ flatten l} f y == Σ_{s ∈ l} (Σ_{y ∈ s} f y) *)
Lemma CRsum_list_flatten {R : ConstructiveReals} {A : Type} (f : A -> CRcarrier R) (l : seq (seq A)) :
  CReq R (CRsum_list f (flatten l)) (CRsum_list (fun s => CRsum_list f s) l).
Proof.
  elim: l => [| s l IH] /=.
  - reflexivity.
  - rewrite (CRsum_list_cat (R := R) f s (flatten l)).
    rewrite IH.
    reflexivity.
Qed.

(* map 求和：Σ_{y ∈ map g l} f y == Σ_{x ∈ l} f (g x) *)
Lemma CRsum_list_map {R : ConstructiveReals} {A B : Type} (f : B -> CRcarrier R) (g : A -> B) (l : seq A) :
  CReq R (CRsum_list f (map g l)) (CRsum_list (fun x => f (g x)) l).
Proof.
  elim: l => [| x l IH] /=.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

(* iota 求和：Σ_{k ∈ iota 0 (E+1)} f k == CRsum f E（CRsum 的列表等价）
   —— iotaD 从后展开：iota 0 (S E + 1) = iota 0 (S E) ++ [S E] *)
Lemma CRsum_list_iota {R : ConstructiveReals} (f : nat -> CRcarrier R) (E : nat) :
  CReq R (CRsum_list f (iota 0 (E + 1)%N)) (CRsum f E).
Proof.
  elim: E => [| E IH].
  - simpl. rewrite (CRplus_0_r (R := R) (f 0%nat)). reflexivity.
  - rewrite (iotaD 0 (S E) 1).
    rewrite (CRsum_list_cat (R := R) f (iota 0 (S E)) (iota (0 + S E) 1)).
    rewrite (addn1 E) in IH.
    rewrite IH.
    rewrite add0n. simpl.
    rewrite (CRplus_0_r (R := R) (f (S E))).
    reflexivity.
Qed.

(* 列表求和逐项相等：forall x ∈ l, f x == g x ⟹ Σ_{x∈l} f x == Σ_{x∈l} g x（A 需 eqType） *)
Lemma CRsum_eq_list {R : ConstructiveReals} {A : eqType} (f g : A -> CRcarrier R) (l : seq A) :
  (forall x, x \in l -> CReq R (f x) (g x)) -> CReq R (CRsum_list f l) (CRsum_list g l).
Proof.
  intro H. revert H. induction l as [| x l IH]; intro H; simpl.
  - apply CReq_refl.
  - have Htail : forall y, y \in l -> CReq R (f y) (g y).
    { move => y Hy. apply (H y). rewrite in_cons. apply/orP. right. exact Hy. }
    unfold CReq. split.
    + apply (CRplus_le_compat (g x) (f x) (CRsum_list g l) (CRsum_list f l)).
      * exact (proj1 (H x (mem_head x l))).
      * exact (proj1 (IH Htail)).
    + apply (CRplus_le_compat (f x) (g x) (CRsum_list f l) (CRsum_list g l)).
      * exact (proj2 (H x (mem_head x l))).
      * exact (proj2 (IH Htail)).
Qed.

(* 双重列表推导求和：Σ_{y ∈ [seq g x e | x <- l, e <- iota 0 (E+1)]} f y
   == Σ_{x ∈ l} Σ_{e ≤ E} f (g x e)（smooth_list 展开的求和） *)
Lemma CRsum_list_2d {R : ConstructiveReals} (f : nat -> CRcarrier R) (g : nat -> nat -> nat)
  (l : seq nat) (E : nat) :
  CReq R (CRsum_list f [seq g x e | x <- l, e <- iota 0 (E + 1)%N])
         (CRsum_list (fun x => CRsum_list (fun e => f (g x e)) (iota 0 (E + 1)%N)) l).
Proof.
  rewrite (CRsum_list_flatten (R := R) f (map (fun x => map (fun e => g x e) (iota 0 (E + 1)%N)) l)).
  rewrite (CRsum_list_map (R := R) (fun s => CRsum_list f s)
            (fun x => map (fun e => g x e) (iota 0 (E + 1)%N)) l).
  apply (CRsum_eq_list (R := R) _ _ l).
  intros x Hx.
  rewrite (CRsum_list_map (R := R) f (fun e => g x e) (iota 0 (E + 1)%N)).
  reflexivity.
Qed.

(* smooth_list E ps 的元素 ≥ 1（ps 全素数；用于 inv_n_pow_mult 前提） *)
Lemma smooth_list_ge1 (E : nat) (ps : seq nat) (Hps : all prime ps) :
  forall x, x \in smooth_list E ps -> (1 <= x)%nat.
Proof.
  elim: ps Hps => [| p ps' IH] Hps x Hx /=.
  - rewrite mem_seq1 in Hx. move/eqP : Hx => Hx'.
    rewrite Hx'. apply leqnn.
  - have Hp : prime p := allP Hps p (mem_head p ps').
    have Hps' : all prime ps'.
    { apply/allP. move => y Hy.
      apply (allP Hps y).
      rewrite in_cons. apply/orP. right. exact Hy. }
    move: Hx.
    rewrite /smooth_list.
    move/flattenP => [s Hs Hxs].
    move/mapP : Hs => [y Hy Hs'].
    move: Hxs. rewrite Hs'. move/mapP => [e He Hxe].
    rewrite Hxe.
    rewrite muln_gt0. apply/andP. split.
    + exact (IH Hps' y Hy).
    + rewrite expn_gt0. rewrite (@prime_gt0 p Hp). simpl. reflexivity.
Qed.

(* 列表版分布律：(Σ_{x∈l} f x)·y == Σ_{x∈l} (f x·y) *)
Lemma CRsum_list_mult_r {R : ConstructiveReals} (f : nat -> CRcarrier R) (l : seq nat) (y : CRcarrier R) :
  CReq R (CRmult R (CRsum_list f l) y) (CRsum_list (fun x => CRmult R (f x) y) l).
Proof.
  elim: l => [| x l IH] /=.
  - rewrite (CRmult_0_l (R := R) y). reflexivity.
  - rewrite (CRmult_plus_distr_r (R := R) y (f x) (CRsum_list f l)).
    rewrite IH. reflexivity.
Qed.

(* 列表 × CRsum 分布：(Σ_{x∈l} f x)·(Σ_{e≤E} g e) == Σ_{x∈l} Σ_{e≤E} (f x·g e)
   —— smooth_step 的分布律反向基础 *)
Lemma CRsum_list_mult_sum {R : ConstructiveReals} (f : nat -> CRcarrier R) (l : seq nat)
  (g : nat -> CRcarrier R) (E : nat) :
  CReq R (CRmult R (CRsum_list f l) (CRsum g E))
         (CRsum_list (fun x => CRsum (fun e => CRmult R (f x) (g e)) E) l).
Proof.
  rewrite (CRsum_list_mult_r (R := R) f l (CRsum g E)).
  apply (CRsum_eq_list (R := R) (fun x => CRmult R (f x) (CRsum g E))
                                  (fun x => CRsum (fun e => CRmult R (f x) (g e)) E) l).
  intros x Hx.
  apply (CRsum_mult_l (R := R) g E (f x)).
Qed.

(* 逐步乘入：Σ_{y∈smooth_list E (p::ps)} y^{-s}
   == (Σ_{x∈smooth_list E ps} x^{-s})·(Σ_{e≤E} p^{-es})
   —— 展开 smooth_list + 双重和（CRsum_list_2d）+ 每项 inv_n_pow_mult + 分布律反向
   ★ 可复用：欧拉乘积逐步乘入新素因子的原子步 *)
Lemma smooth_step {R : ConstructiveReals} (s p E : nat) (ps : seq nat)
  (Hp : prime p) (Hps : all prime ps) :
  CReq R (CRsum_list (fun y => inv_n_pow y s) (smooth_list E (p :: ps)))
         (CRmult R (CRsum_list (fun x => inv_n_pow x s) (smooth_list E ps))
                   (CRsum (fun e => inv_n_pow (p ^ e) s) E)).
Proof.
  rewrite (CRsum_list_2d (R := R) (fun y => inv_n_pow y s) (fun x e => (x * p ^ e)%N)
                         (smooth_list E ps) E).
  rewrite (CRsum_list_mult_sum (R := R) (fun x => inv_n_pow x s) (smooth_list E ps)
                                (fun e => inv_n_pow (p ^ e) s) E).
  apply (CRsum_eq_list (R := R) _ _ (smooth_list E ps)).
  intros x Hx.
  rewrite (CRsum_list_iota (R := R) (fun e => inv_n_pow (x * p ^ e) s) E).
  apply (CRsum_eq (R := R) _ _ E).
  intros e He.
  apply (inv_n_pow_mult (R := R) x (p ^ e) s (smooth_list_ge1 E ps Hps x Hx)).
  rewrite expn_gt0. rewrite (@prime_gt0 p Hp). simpl. reflexivity.
Qed.

(* 1^{-s} == 1（s ≥ 0；空积 = 1 的基础） *)
Lemma inv_n_pow_one {R : ConstructiveReals} (s : nat) :
  CReq R (inv_n_pow 1 s) (CR_of_Q R Q1q).
Proof.
  unfold inv_n_pow. simpl.
  rewrite (CRpow_one (R := R) s). reflexivity.
Qed.

(* ============================================================
   L3 主引理：有限欧拉乘积 = smooth 数和
   ∏_{p ∈ ps} (Σ_{e≤E} p^{-es}) == Σ_{x ∈ smooth_list E ps} x^{-s}（ps 全素数）
   —— 归纳 on ps：空积 = 1^{-s} = 1；逐步乘入（smooth_step）
   ★ 里程碑：欧拉乘积展开的核心代数（L4 双极限的前置） *)
Lemma euler_finite_expand {R : ConstructiveReals} (ps : seq nat) (s E : nat)
  (Hps : all prime ps) :
  CReq R (CRprod_list (fun p => CRsum (fun e => inv_n_pow (p ^ e) s) E) ps)
         (CRsum_list (fun x => inv_n_pow x s) (smooth_list E ps)).
Proof.
  elim: ps Hps => [| p ps' IH] Hps /=.
  - rewrite (CRplus_0_r (R := R) (inv_n_pow 1 s)).
    rewrite (inv_n_pow_one (R := R) s). reflexivity.
  - have Hp : prime p := allP Hps p (mem_head p ps').
    have Hps' : all prime ps'.
    { apply/allP. move => y Hy.
      apply (allP Hps y).
      rewrite in_cons. apply/orP. right. exact Hy. }
    rewrite (CRmult_comm (R := R) (CRsum (fun e => inv_n_pow (p ^ e) s) E)
                         (CRprod_list (fun p => CRsum (fun e => inv_n_pow (p ^ e) s) E) ps')).
    rewrite (IH Hps').
    symmetry.
    apply (smooth_step (R := R) s p E ps' Hp Hps').
Qed.

(* ============================================================
   L4 分析件：CR_cv 对乘法的连续性（构造性 eps-N）
   E→∞ 极限：∏_{p∈ps} (Σ_{e≤E} p^{-es}) → ∏_{p∈ps} (1-p^{-s})^{-1}
   ============================================================ *)

(* x < y ⟹ x ≤ y（CRle 是 CRlt 反向的否定；CRle_of_lt 的泛化） *)
Lemma CRlt_le {R : ConstructiveReals} (x y : CRcarrier R) (H : CRlt R x y) : CRle R x y.
Proof. unfold CRle. intro Hyx. exact (CRlt_asym (R := R) x y H Hyx). Qed.

(* v → b ⟹ 存在 N，n ≥ N ⟹ |v n| ≤ |b| + 1（收敛 ⟹ 尾部有界） *)
Lemma CR_cv_abs_bounded {R : ConstructiveReals} (v : nat -> CRcarrier R) (b : CRcarrier R)
  (Hv : CR_cv R v b) :
  { N : nat | forall n, le N n -> CRle R (CRabs R (v n)) (CRplus R (CRabs R b) (CR_of_Q R Q1q)) }.
Proof.
  destruct (Hv 1%positive) as [N HN].
  exists N.
  intros n Hn.
  have Hvnab : CReq R (CRabs R (v n))
                      (CRplus R (CRabs R b) (CRminus R (CRabs R (v n)) (CRabs R b))).
  { unfold CRminus.
    rewrite <- (CRplus_assoc (R := R) (CRabs R b) (CRabs R (v n)) (CRopp R (CRabs R b))).
    rewrite (CRplus_comm (R := R) (CRabs R b) (CRabs R (v n))).
    rewrite (CRplus_assoc (R := R) (CRabs R (v n)) (CRabs R b) (CRopp R (CRabs R b))).
    rewrite (CRplus_opp_r (R := R) (CRabs R b)).
    rewrite (CRplus_0_r (R := R) (CRabs R (v n))).
    reflexivity. }
  eapply CRle_trans.
  - exact (proj2 Hvnab).
  - eapply CRle_trans.
    + apply (CRplus_le_compat_l (R := R) (CRabs R b) (CRminus R (CRabs R (v n)) (CRabs R b))
                                 (CRabs R (CRminus R (v n) b))).
      exact (CRabs_triang_inv (R := R) (v n) b).
    + apply (CRplus_le_compat_l (R := R) (CRabs R b) (CRabs R (CRminus R (v n) b))
                                   (CR_of_Q R Q1q)).
      exact (HN n Hn).
Qed.

(* |u v - a b| ≤ |u-a||v| + |a||v-b| —— 乘法连续的核心代数 *)
Lemma CRabs_mult_diff {R : ConstructiveReals} (u v a b : CRcarrier R) :
  CRle R (CRabs R (CRminus R (CRmult R u v) (CRmult R a b)))
         (CRplus R (CRmult R (CRabs R (CRminus R u a)) (CRabs R v))
                   (CRmult R (CRabs R a) (CRabs R (CRminus R v b)))).
Proof.
  have Halg : CReq R (CRminus R (CRmult R u v) (CRmult R a b))
                     (CRplus R (CRmult R (CRminus R u a) v) (CRmult R a (CRminus R v b))).
  { have H1 : CReq R (CRmult R (CRminus R u a) v) (CRminus R (CRmult R u v) (CRmult R a v)).
    { unfold CRminus.
      rewrite (CRmult_plus_distr_r (R := R) v u (CRopp R a)).
      rewrite (CRopp_mult_distr_l (R := R) a v).
      reflexivity. }
    have H2 : CReq R (CRmult R a (CRminus R v b)) (CRminus R (CRmult R a v) (CRmult R a b)).
    { unfold CRminus.
      rewrite (CRmult_plus_distr_l (R := R) a v (CRopp R b)).
      rewrite (CRopp_mult_distr_r (R := R) a b).
      reflexivity. }
    rewrite H1 H2.
    symmetry.
    exact (CRminus_add_cancel (R := R) (CRmult R u v) (CRmult R a v) (CRmult R a b)).
  }
  eapply CRle_trans.
  - rewrite Halg.
    apply (CRabs_triang (R := R) (CRmult R (CRminus R u a) v) (CRmult R a (CRminus R v b))).
  - apply (CRplus_le_compat (CRabs R (CRmult R (CRminus R u a) v))
                            (CRmult R (CRabs R (CRminus R u a)) (CRabs R v))
                            (CRabs R (CRmult R a (CRminus R v b)))
                            (CRmult R (CRabs R a) (CRabs R (CRminus R v b)))).
    + exact (proj2 (CRabs_mult (R := R) (CRminus R u a) v)).
    + exact (proj2 (CRabs_mult (R := R) a (CRminus R v b))).
Qed.

(* X·p < q ⟹ X·(1/q) < 1/p —— archimedean 界到 eps（p q positive，X 任意） *)
Lemma CR_arch_eps {R : ConstructiveReals} (X : CRcarrier R) (p q : positive)
  (H : CRlt R (CRmult R X (CR_of_Q R (Qmake (Zpos p) 1))) (CR_of_Q R (Qmake (Zpos q) 1))) :
  CRlt R (CRmult R X (CR_of_Q R (Qmake 1 q))) (CR_of_Q R (Qmake 1 p)).
Proof.
  have Hpos : CRlt R (CR_of_Q R Q0q) (CR_of_Q R (Qmake 1 (Pos.mul p q))).
  { apply CR_of_Q_lt. unfold Q0q, Qlt. simpl. lia. }
  have Hpq : CReq R (CRmult R (CR_of_Q R (Qmake (Zpos p) 1)) (CR_of_Q R (Qmake 1 (Pos.mul p q))))
                    (CR_of_Q R (Qmake 1 q)).
  { rewrite <- (CR_of_Q_mult R (Qmake (Zpos p) 1) (Qmake 1 (Pos.mul p q))).
    apply (CR_of_Q_Qeq (R := R) (Qmult (Qmake (Zpos p) 1) (Qmake 1 (Pos.mul p q))) (Qmake 1 q)).
    unfold Qmult, Qeq. simpl. lia. }
  have Hq1 : CReq R (CRmult R (CR_of_Q R (Qmake (Zpos q) 1)) (CR_of_Q R (Qmake 1 (Pos.mul p q))))
                    (CR_of_Q R (Qmake 1 p)).
  { rewrite <- (CR_of_Q_mult R (Qmake (Zpos q) 1) (Qmake 1 (Pos.mul p q))).
    apply (CR_of_Q_Qeq (R := R) (Qmult (Qmake (Zpos q) 1) (Qmake 1 (Pos.mul p q))) (Qmake 1 p)).
    unfold Qmult, Qeq. simpl. lia. }
  pose (Hm := CRmult_lt_compat_r (R := R) (CR_of_Q R (Qmake 1 (Pos.mul p q)))
                                 (CRmult R X (CR_of_Q R (Qmake (Zpos p) 1)))
                                 (CR_of_Q R (Qmake (Zpos q) 1))
                                 Hpos H).
  rewrite <- Hpq.
  rewrite <- (CRmult_assoc (R := R) X (CR_of_Q R (Qmake (Zpos p) 1)) (CR_of_Q R (Qmake 1 (Pos.mul p q)))).
  eapply CRlt_le_trans.
  - exact Hm.
  - rewrite <- Hq1. apply CRle_refl.
Qed.

(* CR_cv 对乘法的连续性：u → a、v → b ⟹ u·v → a·b（构造性 eps-N）
   —— CR_archimedean 选 q 使 (|b|+1+|a|)·p < q，eps 分割 1/q
   ★ 可复用：L4 双极限的乘积极限连续性基础 *)
Lemma CR_cv_mult {R : ConstructiveReals} (u v : nat -> CRcarrier R) (a b : CRcarrier R)
  (Hu : CR_cv R u a) (Hv : CR_cv R v b) : CR_cv R (fun n => CRmult R (u n) (v n)) (CRmult R a b).
Proof.
  intro p.
  destruct (CR_cv_abs_bounded (R := R) v b Hv) as [N0 HN0].
  destruct (CR_archimedean R
             (CRmult R (CRplus R (CRplus R (CRabs R b) (CR_of_Q R Q1q)) (CRabs R a))
                       (CR_of_Q R (Qmake (Zpos p) 1)))) as [q Hq].
  destruct (Hu q) as [N1 HN1].
  destruct (Hv q) as [N2 HN2].
  exists (Init.Nat.max N0 (Init.Nat.max N1 N2)).
  intros n Hn.
  have Hn0 : le N0 n := Nat.le_trans N0 (Init.Nat.max N0 (Init.Nat.max N1 N2)) n (Nat.le_max_l N0 (Init.Nat.max N1 N2)) Hn.
  have Hn2 : le N2 n := Nat.le_trans N2 (Init.Nat.max N1 N2) n (Nat.le_max_r N1 N2) (Nat.le_trans (Init.Nat.max N1 N2) (Init.Nat.max N0 (Init.Nat.max N1 N2)) n (Nat.le_max_r N0 (Init.Nat.max N1 N2)) Hn).
  have Hn1 : le N1 n := Nat.le_trans N1 (Init.Nat.max N1 N2) n (Nat.le_max_l N1 N2) (Nat.le_trans (Init.Nat.max N1 N2) (Init.Nat.max N0 (Init.Nat.max N1 N2)) n (Nat.le_max_r N0 (Init.Nat.max N1 N2)) Hn).
  eapply CRle_trans.
  - exact (CRabs_mult_diff (R := R) (u n) (v n) a b).
  - eapply CRle_trans.
    + apply (CRplus_le_compat (CRmult R (CRabs R (CRminus R (u n) a)) (CRabs R (v n)))
                              (CRmult R (CR_of_Q R (Qmake 1 q)) (CRabs R (v n)))
                              (CRmult R (CRabs R a) (CRabs R (CRminus R (v n) b)))
                              (CRmult R (CRabs R a) (CR_of_Q R (Qmake 1 q)))).
      * apply (CRmult_le_compat_r (R := R) (CRabs R (v n))
                                   (CRabs R (CRminus R (u n) a)) (CR_of_Q R (Qmake 1 q))).
        -- apply CRabs_pos.
        -- exact (HN1 n Hn1).
      * apply (CRmult_le_compat_l (R := R) (CRabs R a)
                                   (CRabs R (CRminus R (v n) b)) (CR_of_Q R (Qmake 1 q))).
        -- apply CRabs_pos.
        -- exact (HN2 n Hn2).
    + eapply CRle_trans.
      * apply (CRplus_le_compat (CRmult R (CR_of_Q R (Qmake 1 q)) (CRabs R (v n)))
                                (CRmult R (CR_of_Q R (Qmake 1 q)) (CRplus R (CRabs R b) (CR_of_Q R Q1q)))
                                (CRmult R (CRabs R a) (CR_of_Q R (Qmake 1 q)))
                                (CRmult R (CRabs R a) (CR_of_Q R (Qmake 1 q)))).
        -- apply (CRmult_le_compat_l (R := R) (CR_of_Q R (Qmake 1 q))
                                     (CRabs R (v n)) (CRplus R (CRabs R b) (CR_of_Q R Q1q))).
           ++ apply (CRlt_le (R := R) (CR_of_Q R Q0q) (CR_of_Q R (Qmake 1 q))).
              apply CR_of_Q_lt. unfold Q0q, Qlt. simpl. lia.
           ++ exact (HN0 n Hn0).
        -- apply CRle_refl.
      * eapply CRle_trans.
        -- rewrite (CRmult_comm (R := R) (CRabs R a) (CR_of_Q R (Qmake 1 q))).
           rewrite <- (CRmult_plus_distr_l (R := R) (CR_of_Q R (Qmake 1 q))
                                           (CRplus R (CRabs R b) (CR_of_Q R Q1q)) (CRabs R a)).
           apply CRle_refl.
        -- apply CRlt_le.
           rewrite (CRmult_comm (R := R) (CR_of_Q R (Qmake 1 q))
                                (CRplus R (CRplus R (CRabs R b) (CR_of_Q R Q1q)) (CRabs R a))).
           exact (CR_arch_eps (R := R) (CRplus R (CRplus R (CRabs R b) (CR_of_Q R Q1q)) (CRabs R a))
                                   p q Hq).
Qed.

(* ============================================================
   L4 E→∞ 极限：∏_{p∈ps} (Σ_{e≤E} p^{-es}) →_{E} ∏_{p∈ps} (1-p^{-s})^{-1}
   ============================================================ *)

(* p ≥ 1 ⟹ p^e ≥ 1（e 任意） *)
Lemma expn_ge1 (p e : nat) (Hp : (1 <= p)%nat) : (1 <= p ^ e)%nat.
Proof.
  elim: e => [| e' IH'] /=.
  - rewrite expn0. apply leqnn.
  - rewrite expnS. rewrite muln_gt0. apply/andP. split. exact Hp. exact IH'.
Qed.

(* (p^e)^{-s} == (p^{-s})^e —— 素数幂项 = 几何级数项（归纳 + inv_n_pow_mult） *)
Lemma inv_n_pow_pow {R : ConstructiveReals} (p s e : nat) (Hp : (1 <= p)%nat) :
  CReq R (inv_n_pow (p ^ e) s) (CRpow (inv_n_pow p s) e).
Proof.
  induction e as [| e IH].
  - simpl. rewrite (inv_n_pow_one (R := R) s). reflexivity.
  - rewrite (expnS p e). simpl.
    rewrite (inv_n_pow_mult (R := R) p (p ^ e) s Hp (expn_ge1 p e Hp)).
    rewrite IH.
    rewrite (CRmult_comm (R := R) (inv_n_pow p s) (CRpow (inv_n_pow p s) e)).
    reflexivity.
Qed.

(* 逐因子极限 ⟹ 有限乘积极限（CRprod_list 归纳 + CR_cv_mult） *)
Lemma CRprod_list_cv {R : ConstructiveReals} (f : nat -> nat -> CRcarrier R) (g : nat -> CRcarrier R)
  (ps : seq nat) (Hcv : forall i, i \in ps -> CR_cv R (fun E => f i E) (g i)) :
  CR_cv R (fun E => CRprod_list (fun i => f i E) ps) (CRprod_list g ps).
Proof.
  revert Hcv. induction ps as [| p ps' IH]; intro Hcv; simpl.
  - apply (CR_cv_extens (R := R) (fun E : nat => CR_of_Q R Q1q)
                          (fun E : nat => CR_of_Q R Q1q) (CR_of_Q R Q1q)).
    + intros E. reflexivity.
    + apply CR_cv_const.
  - apply (CR_cv_mult (R := R) (fun E => f p E) (fun E => CRprod_list (fun i => f i E) ps')
                         (g p) (CRprod_list g ps')).
    + exact (Hcv p (mem_head p ps')).
    + have Hps'cv : forall i, i \in ps' -> CR_cv R (fun E => f i E) (g i).
      { move => i Hi. apply (Hcv i). rewrite in_cons. apply/orP. right. exact Hi. }
      exact (IH Hps'cv).
Qed.

(* 每因子极限：Σ_{e≤E} (p^e)^{-s} → (1-p^{-s})^{-1}（prime_power_series + 项重写 inv_n_pow_pow） *)
Lemma prime_pow_sum_cv {R : ConstructiveReals} (p s : nat) (Hp : prime p) (Hs : (1 <= s)%nat) :
  { l : CRcarrier R & CR_cv R (fun E => CRsum (fun e => inv_n_pow (p ^ e) s) E) l }.
Proof.
  destruct (prime_power_series (R := R) p s Hp Hs) as [l Hl].
  exists l.
  apply (CR_cv_extens (R := R) (fun E => CRsum (fun k => CRpow (inv_n_pow p s) k) E)
                              (fun E => CRsum (fun e => inv_n_pow (p ^ e) s) E) l).
  - intros E.
    apply (CRsum_eq (R := R) (fun k => CRpow (inv_n_pow p s) k)
                             (fun e => inv_n_pow (p ^ e) s) E).
    intros k Hk.
    symmetry.
    apply (inv_n_pow_pow (R := R) p s k (prime_ge1 p Hp)).
  - exact (fst Hl).
Qed.

(* 有限欧拉乘积的 E 极限：∏_{p∈ps} (Σ_{e≤E} p^{-es}) →_{E} ∏_{p∈ps} (1-p^{-s})^{-1}
   —— 归纳 on ps 构造极限（每步 prime_pow_sum_cv + CR_cv_mult）
   ★ 里程碑：L4 E→∞ 极限完成（L3 euler_finite_expand 的极限闭合） *)
Lemma euler_E_cv {R : ConstructiveReals} (ps : seq nat) (s : nat)
  (Hps : all prime ps) (Hs : (1 <= s)%nat) :
  { l : CRcarrier R & CR_cv R (fun E => CRprod_list (fun p => CRsum (fun e => inv_n_pow (p ^ e) s) E) ps) l }.
Proof.
  revert Hps. induction ps as [| p ps' IH]; intro Hps.
  - exists (CR_of_Q R Q1q).
    apply (CR_cv_extens (R := R) (fun E : nat => CR_of_Q R Q1q)
                          (fun E : nat => CR_of_Q R Q1q) (CR_of_Q R Q1q)).
    + intros E. reflexivity.
    + apply CR_cv_const.
  - have Hp : prime p := allP Hps p (mem_head p ps').
    have Hps' : all prime ps'.
    { apply/allP. move => y Hy.
      apply (allP Hps y).
      rewrite in_cons. apply/orP. right. exact Hy. }
    destruct (prime_pow_sum_cv (R := R) p s Hp Hs) as [lp Hlp].
    destruct (IH Hps') as [lps' Hlps'].
    exists (CRmult R lp lps').
    apply (CR_cv_mult (R := R) (fun E => CRsum (fun e => inv_n_pow (p ^ e) s) E)
                                (fun E => CRprod_list (fun p => CRsum (fun e => inv_n_pow (p ^ e) s) E) ps')
                                lp lps').
    + exact Hlp.
    + exact Hlps'.
Qed.

(* ============================================================
   L4 P→∞：smooth 子级数 → ζ（夹逼）
   ============================================================ *)

(* nat 层列表乘积（smooth 数界的上限构造） *)
Definition nat_prod_list (f : nat -> nat) (ps : seq nat) : nat :=
  foldr (fun p acc => (f p * acc)%N) 1%nat ps.

(* x ∈ smooth_list E ps、ps 全素数 ⟹ x ≤ ∏_{p∈ps} p^E（E 界 + 素因子界）
   —— 正向不等式「∏(Σ_e) ≤ ζ 部分和」的基础（每项 x^{-s} 落入 ζ 部分和的项集） *)
Lemma smooth_list_bound (E : nat) (ps : seq nat) (Hps : all prime ps) :
  forall x, x \in smooth_list E ps -> (x <= nat_prod_list (fun p => (p ^ E)%N) ps)%nat.
Proof.
  elim: ps Hps => [| p ps' IH] Hps x Hx /=.
  - rewrite mem_seq1 in Hx. move/eqP : Hx => Hx'.
    rewrite Hx'. apply leqnn.
  - have Hp : prime p := allP Hps p (mem_head p ps').
    have Hps' : all prime ps'.
    { apply/allP. move => y Hy.
      apply (allP Hps y).
      rewrite in_cons. apply/orP. right. exact Hy. }
    move: Hx.
    rewrite /smooth_list.
    move/flattenP => [s Hs Hxs].
    move/mapP : Hs => [y Hy Hs'].
    move: Hxs. rewrite Hs'. move/mapP => [e He Hxe].
    rewrite Hxe.
    have HeE : (e <= E)%nat.
    { rewrite mem_iota in He. destruct (andP He) as [_ He1].
      rewrite add0n in He1.
      rewrite (addn1 E) in He1.
      rewrite (ltnS e E) in He1.
      exact He1. }
    have Hpgt1 : (1 < p)%nat := prime_gt1_mc p Hp.
    have Hpe : (p ^ e <= p ^ E)%nat.
    { rewrite (@leq_exp2l p e E Hpgt1). exact HeE. }
    apply (leq_trans (leq_mul (IH Hps' y Hy) Hpe)).
    rewrite (mulnC (nat_prod_list (fun p : nat => (p ^ E)%N) ps') (p ^ E)%N). apply leqnn.
Qed.

(* x ∈ smooth_list E ps、ps 全素数 ⟹ x 的素因子 ⊆ ps
   —— 配对「p ∤ y（y smooth 且 p 不在 ps）」的关键 *)
Lemma smooth_list_prime_sub (E : nat) (ps : seq nat) (Hps : all prime ps) :
  forall x, x \in smooth_list E ps -> all (fun q => q \in ps) (primes x).
Proof.
  elim: ps Hps => [| p ps' IH] Hps x Hx /=.
  - rewrite mem_seq1 in Hx. move/eqP : Hx => Hx'.
    rewrite Hx'. reflexivity.
  - have Hp : prime p := allP Hps p (mem_head p ps').
    have Hps' : all prime ps'.
    { apply/allP. move => y Hy.
      apply (allP Hps y).
      rewrite in_cons. apply/orP. right. exact Hy. }
    move: Hx.
    rewrite /smooth_list.
    move/flattenP => [s Hs Hxs].
    move/mapP : Hs => [y Hy Hs'].
    move: Hxs. rewrite Hs'. move/mapP => [e He Hxe].
    rewrite Hxe.
    apply/allP. move => q Hq.
    rewrite mem_primes in Hq.
    move/andP : Hq => [Hqpr /andP [_ Hqdvd]].
    destruct (Nat.eqb_spec q p) as [Heq | Hne].
    + rewrite Heq. apply mem_head.
    + have Hqnp : ~~ (q %| p).
      { rewrite (@dvdn_prime2 q p Hqpr Hp). apply/eqP. exact Hne. }
      have Hqcop_p : coprime q p.
      { rewrite (@prime_coprime q p Hqpr). exact Hqnp. }
      have Hqcop : coprime q (p ^ e).
      { rewrite coprime_sym.
        apply (@coprimeXl e p q).
        rewrite coprime_sym. exact Hqcop_p. }
      have Hqdvdn : q %| y.
      { rewrite (mulnC y (p ^ e)%N) in Hqdvd.
        move: Hqdvd. rewrite (@Gauss_dvdr q (p ^ e)%N y Hqcop). exact id. }
      have Hqiny : q \in primes y.
      { rewrite mem_primes. apply/andP. split. exact Hqpr. apply/andP. split.
        - exact (smooth_list_ge1 E ps' Hps' y Hy).
        - exact Hqdvdn. }
      have Hqps' : q \in ps'.
      { move: (IH Hps' y Hy) => /allP HIH. exact (HIH q Hqiny). }
      rewrite in_cons. apply/orP. right. exact Hqps'.
Qed.

(* ============================================================
   L4 P→∞：smooth_list 互异（夹逼「反向分解」的基础）
   —— uniq_flatten 组合：cat_uniq + smooth_expand_uniq + smooth_list_uniq
   ============================================================ *)

(* s1、s2 uniq 且 s1 的元素不在 s2 ⟹ s1++s2 uniq（bool 计算版） *)
Lemma cat_uniq {A : eqType} (s1 s2 : seq A) :
  uniq s1 -> uniq s2 -> (forall x, x \in s1 -> x \notin s2) -> uniq (s1 ++ s2).
Proof.
  elim: s1 => [| x s1' IH] /=.
  - intros _ Hs2 _. exact Hs2.
  - move => H1 Hs2 Hsep.
    have [Hxnotin H1'] := andP H1.
    rewrite /uniq. simpl.
    rewrite (mem_cat x s1' s2). rewrite negb_or. rewrite Hxnotin.
    rewrite (Hsep x (mem_head x s1')). simpl.
    apply (IH H1' Hs2).
    intros y Hy. apply Hsep. rewrite in_cons. apply/orP. right. exact Hy.
Qed.

(* 对任意 uniq 且 p∤元素、元素≥1 的列表 l：展开 [seq y·p^e | y <- l, e <- iota] 仍 uniq
   —— 内层（固定 y，e 单射）+ 外层（不同 y，smooth_pair_inj） *)
Lemma smooth_expand_uniq (E p : nat) (Hp : prime p) (l : seq nat)
  (Hluniq : uniq l)
  (Hpndvd : forall y, y \in l -> ~~ (p %| y))
  (Hyge : forall y, y \in l -> (1 <= y)%nat) :
  uniq [seq (y * p ^ e)%N | y <- l, e <- iota 0 (E + 1)%N].
Proof.
  revert Hluniq Hpndvd Hyge.
  induction l as [| y l' IH]; intros Hluniq Hpndvd Hyge; simpl.
  - done.
  - have Hpgt1 : (1 < p)%nat := prime_gt1_mc p Hp.
    have Hy0 : (0 < y)%nat.
    { move: (Hyge y (mem_head y l')) => H. exact H. }
    have Hinj : injective (fun e : nat => (y * p ^ e)%N).
    { move => e1 e2 He.
      apply/eqP.
      rewrite <- (@eqn_exp2l p e1 e2 Hpgt1).
      rewrite <- (@eqn_pmul2l y (p ^ e1)%N (p ^ e2)%N Hy0).
      apply/eqP. exact He. }
    have Hinner : uniq [seq (y * p ^ e)%N | e <- iota 0 (E + 1)%N].
    { rewrite (@map_inj_uniq _ _ (fun e : nat => (y * p ^ e)%N) Hinj (iota 0 (E + 1)%N)).
      apply iota_uniq. }
    have Hl' : uniq l' := proj2 (andP Hluniq).
    (* 外层：cat_uniq (f y) (flatten (map f l')) *)
    apply (cat_uniq [seq (y * p ^ e)%N | e <- iota 0 (E + 1)%N]
                    (flatten (map (fun y0 => [seq (y0 * p ^ e)%N | e <- iota 0 (E + 1)%N]) l'))).
    + exact Hinner.
    + (* uniq (flatten (map f l'))——IH（对 l'）*)
      apply (IH Hl'
                (fun y0 Hy0 => Hpndvd y0 (@mem_behead nat (y :: l') y0 Hy0))
                (fun y0 Hy0 => Hyge y0 (@mem_behead nat (y :: l') y0 Hy0))).
    + (* 不重叠：f y 的元素（y·p^e）∉ flatten（= y0·p^{e'}，y0 ∈ l'）*)
      move => x Hx.
      apply/negP => Hxfl.
      move: Hx => /mapP [e0 _ Hxe0].
      move/flattenP : Hxfl => [s0 Hs0 Hxs0].
      move: Hs0 => /mapP [y1 Hy1 Hs0'].
      move: Hxs0. rewrite Hs0'. move/mapP => [e' _ Hxe'].
      have Heq : (y * p ^ e0)%N = (y1 * p ^ e')%N.
      { rewrite <- Hxe0. exact Hxe'. }
      have Hpair := smooth_pair_inj p y y1 e0 e' Hp
                     (Hpndvd y (mem_head y l')) (Hpndvd y1 (@mem_behead nat (y :: l') y1 Hy1)) Heq.
      have Hyy0 : y = y1 := proj1 Hpair.
      move/negP : (proj1 (andP Hluniq)) => Hn.
      apply Hn. rewrite Hyy0. exact Hy1.
Qed.

(* smooth_list E ps 元素互异（ps 全素数且去重）
   —— 夹逼反向分解「每 n ∈ smooth 至多出现一次」的保证 *)
Lemma smooth_list_uniq (E : nat) (ps : seq nat) (Hps : all prime ps) (Huniq : uniq ps) :
  uniq (smooth_list E ps).
Proof.
  revert Hps Huniq. induction ps as [| p ps' IH]; intros Hps Huniq; simpl.
  - done.
  - have Hp : prime p := allP Hps p (mem_head p ps').
    have Hps' : all prime ps'.
    { apply/allP. move => y Hy.
      apply (allP Hps y).
      rewrite in_cons. apply/orP. right. exact Hy. }
    have Huniq' : uniq ps' := proj2 (andP Huniq).
    have Hpnotin : p \notin ps' := proj1 (andP Huniq).
    have Hpndvd : forall y, y \in smooth_list E ps' -> ~~ (p %| y).
    { move => y Hy.
      apply/negP => Hpdvd.
      have Hsub := smooth_list_prime_sub E ps' Hps' y Hy.
      have Hpin : p \in primes y.
      { rewrite mem_primes. apply/andP. split. exact Hp. apply/andP. split.
        - exact (smooth_list_ge1 E ps' Hps' y Hy).
        - exact Hpdvd. }
      move: Hsub => /allP Hsub'. move: (Hsub' p Hpin) => Hpinps'.
      move/negP : Hpnotin => Hnot'. apply Hnot'. exact Hpinps'. }
    apply (smooth_expand_uniq E p Hp (smooth_list E ps')
              (IH Hps' Huniq')
              Hpndvd
              (fun y Hy => smooth_list_ge1 E ps' Hps' y Hy)).
Qed.

(* ============================================================
   L4 P→∞：正向不等式子引理（Σ_{x∈smooth} x^{-s} ≤ ζ 的砖块）
   —— filter 不增和 / perm 下和不变 / 互异子集和 ≤ 全和
   —— 分析层：非负级数部分和 ≤ 极限
   ============================================================ *)

(* f ≥ 0 时，filter 只删元素 ⟹ 和不增 *)
Lemma CRsum_list_filter_le {R : ConstructiveReals} {A : eqType} (f : A -> CRcarrier R)
  (l : seq A) (P : pred A)
  (Hpos : forall x, x \in l -> CRle R (CR_of_Q R Q0q) (f x)) :
  CRle R (CRsum_list f [seq x <- l | P x]) (CRsum_list f l).
Proof.
  induction l as [| x l' IH].
  - simpl. apply CRle_refl.
  - simpl. case: (P x).
    + have Hpos' : forall y, y \in l' -> CRle R (CR_of_Q R Q0q) (f y).
      { move => y Hy. apply (Hpos y). rewrite in_cons. apply/orP. right. exact Hy. }
      apply (CRplus_le_compat_l (R := R) (f x) (CRsum_list f [seq y <- l' | P y])
                                 (CRsum_list f l')).
      exact (IH Hpos').
    + have Hpos'' : forall y, y \in l' -> CRle R (CR_of_Q R Q0q) (f y).
      { move => y Hy. apply (Hpos y). rewrite in_cons. apply/orP. right. exact Hy. }
      apply (CRle_trans (R := R)
               (CRsum_list f [seq y <- l' | P y])
               (CRsum_list f l')
               (CRplus R (f x) (CRsum_list f l'))).
      * exact (IH Hpos'').
      * have Hposx : CRle R (CR_of_Q R Q0q) (f x) := Hpos x (mem_head x l').
        have H01 : CRle R (CRplus R (CRsum_list f l') (CR_of_Q R Q0q))
                           (CRplus R (CRsum_list f l') (f x)).
        { apply (CRplus_le_compat_l (R := R) (CRsum_list f l') (CR_of_Q R Q0q) (f x)).
          exact Hposx. }
        apply (proj1 (CRle_morph R
                        (CRplus R (CRsum_list f l') (CR_of_Q R Q0q))
                        (CRsum_list f l')
                        (CRplus_0_r (R := R) (CRsum_list f l'))
                        (CRplus R (CRsum_list f l') (f x))
                        (CRplus R (f x) (CRsum_list f l'))
                        (CRplus_comm (R := R) (CRsum_list f l') (f x)))).
        exact H01.
Qed.

(* perm_eq ⟹ 和不变（CReq）—— catCA_perm_ind + CRsum_list_cat + 加法交换/结合 *)
Lemma CRsum_list_perm {R : ConstructiveReals} {A : eqType} (f : A -> CRcarrier R)
  (l1 l2 : seq A) (Hp : perm_eq l1 l2) :
  CReq R (CRsum_list f l1) (CRsum_list f l2).
Proof.
  pose P := fun (s : seq A) => CReq R (CRsum_list f s) (CRsum_list f l2).
  have Hstep : forall s1 s2 s3 : seq A, P (s1 ++ s2 ++ s3) -> P (s2 ++ s1 ++ s3).
  { move => s1 s2 s3 HP.
    (* 先证中间等式 Hmid：Σ(s1++s2++s3) == Σ(s2++s1++s3) *)
    have Hmid : CReq R (CRsum_list f (s1 ++ s2 ++ s3)) (CRsum_list f (s2 ++ s1 ++ s3)).
    { (* 链：A == Σs1 + Σ(s2++s3) == Σs1 + (Σs2+Σs3) == (Σs1+Σs2)+Σs3
               == (Σs2+Σs1)+Σs3 == Σs2 + (Σs1+Σs3) == Σs2 + Σ(s1++s3) == B *)
      apply (CReq_trans (R := R) (CRsum_list f (s1 ++ s2 ++ s3))
                        (CRplus R (CRsum_list f s1) (CRsum_list f (s2 ++ s3)))
                        (CRsum_list f (s2 ++ s1 ++ s3))).
      - apply (CRsum_list_cat (R := R) f s1 (s2 ++ s3)).
      - apply (CReq_trans (R := R)
                (CRplus R (CRsum_list f s1) (CRsum_list f (s2 ++ s3)))
                (CRplus R (CRsum_list f s1) (CRplus R (CRsum_list f s2) (CRsum_list f s3)))
                (CRsum_list f (s2 ++ s1 ++ s3))).
        + apply (CRplus_morph R (CRsum_list f s1) (CRsum_list f s1)
                               (CReq_refl (R := R) (CRsum_list f s1))
                               (CRsum_list f (s2 ++ s3))
                               (CRplus R (CRsum_list f s2) (CRsum_list f s3))
                               (CRsum_list_cat (R := R) f s2 s3)).
        + apply (CReq_trans (R := R)
                  (CRplus R (CRsum_list f s1) (CRplus R (CRsum_list f s2) (CRsum_list f s3)))
                  (CRplus R (CRplus R (CRsum_list f s1) (CRsum_list f s2)) (CRsum_list f s3))
                  (CRsum_list f (s2 ++ s1 ++ s3))).
          * apply (CReq_sym (CRplus R (CRplus R (CRsum_list f s1) (CRsum_list f s2)) (CRsum_list f s3))
                            (CRplus R (CRsum_list f s1) (CRplus R (CRsum_list f s2) (CRsum_list f s3)))
                            (CRplus_assoc (R := R) (CRsum_list f s1)
                                          (CRsum_list f s2) (CRsum_list f s3))).
          * apply (CReq_trans (R := R)
                    (CRplus R (CRplus R (CRsum_list f s1) (CRsum_list f s2)) (CRsum_list f s3))
                    (CRplus R (CRplus R (CRsum_list f s2) (CRsum_list f s1)) (CRsum_list f s3))
                    (CRsum_list f (s2 ++ s1 ++ s3))).
            -- apply (CRplus_morph R
                       (CRplus R (CRsum_list f s1) (CRsum_list f s2))
                       (CRplus R (CRsum_list f s2) (CRsum_list f s1))
                       (CRplus_comm (R := R) (CRsum_list f s1) (CRsum_list f s2))
                       (CRsum_list f s3) (CRsum_list f s3)
                       (CReq_refl (R := R) (CRsum_list f s3))).
            -- apply (CReq_trans (R := R)
                      (CRplus R (CRplus R (CRsum_list f s2) (CRsum_list f s1)) (CRsum_list f s3))
                      (CRplus R (CRsum_list f s2) (CRplus R (CRsum_list f s1) (CRsum_list f s3)))
                      (CRsum_list f (s2 ++ s1 ++ s3))).
               ++ apply (CRplus_assoc (R := R) (CRsum_list f s2)
                                      (CRsum_list f s1) (CRsum_list f s3)).
               ++ apply (CReq_trans (R := R)
                         (CRplus R (CRsum_list f s2) (CRplus R (CRsum_list f s1) (CRsum_list f s3)))
                         (CRplus R (CRsum_list f s2) (CRsum_list f (s1 ++ s3)))
                         (CRsum_list f (s2 ++ s1 ++ s3))).
                   ** apply (CRplus_morph R (CRsum_list f s2) (CRsum_list f s2)
                                          (CReq_refl (R := R) (CRsum_list f s2))
                                          (CRplus R (CRsum_list f s1) (CRsum_list f s3))
                                          (CRsum_list f (s1 ++ s3))
                                          (CReq_sym (CRsum_list f (s1 ++ s3))
                                                    (CRplus R (CRsum_list f s1) (CRsum_list f s3))
                                                    (CRsum_list_cat (R := R) f s1 s3))).
                   ** apply (CReq_sym (CRsum_list f (s2 ++ s1 ++ s3))
                                     (CRplus R (CRsum_list f s2) (CRsum_list f (s1 ++ s3)))
                                     (CRsum_list_cat (R := R) f s2 (s1 ++ s3))).

    }
    unfold P in HP.
    apply (CReq_trans (R := R) (CRsum_list f (s2 ++ s1 ++ s3))
                      (CRsum_list f (s1 ++ s2 ++ s3))
                      (CRsum_list f l2)).
    - exact (CReq_sym (CRsum_list f (s1 ++ s2 ++ s3))
                      (CRsum_list f (s2 ++ s1 ++ s3)) Hmid).
    - exact HP.
  }
  have Hp2 : perm_eq l2 l1.
  { move: Hp. rewrite (perm_sym l1 l2). done. }
  exact (@catCA_perm_ind A P Hstep l2 l1 Hp2
                        (CReq_refl (R := R) (CRsum_list f l2))).
Qed.

(* uniq l 且 l 的元素都在 [1..B] 内，f ≥ 0 ⟹ Σ_{x∈l} f x ≤ Σ_{n=1}^{B} f n
   —— 正向不等式核心：smooth 数（互异、≤∏p^E、≥1）求和 ≤ [1..B] 全和 *)
Lemma CRsum_list_uniq_subset_le {R : ConstructiveReals} (f : nat -> CRcarrier R)
  (l : seq nat) (B : nat)
  (Huniq : uniq l)
  (Hge1 : forall x, x \in l -> (1 <= x)%nat)
  (HleB : forall x, x \in l -> (x <= B)%nat)
  (Hpos : forall n, CRle R (CR_of_Q R Q0q) (f n)) :
  CRle R (CRsum_list f l) (CRsum_list f (iota 1 B)).
Proof.
  pose lf := [seq n <- iota 1 B | n \in l].
  have Hflt : CRle R (CRsum_list f lf) (CRsum_list f (iota 1 B)).
  { unfold lf. apply (CRsum_list_filter_le (R := R) f (iota 1 B) (fun n => n \in l)).
    move => x Hx. apply Hpos. }
  have Hperm : perm_eq l lf.
  { apply (@uniq_perm nat l lf).
    - exact Huniq.
    - unfold lf. apply (subseq_uniq (filter_subseq (fun n => n \in l) (iota 1 B))).
      apply iota_uniq.
    - move => x.
      rewrite mem_filter. apply/idP/idP.
      + move => Hx.
        apply/andP. split.
        * exact Hx.
        * rewrite mem_iota. apply/andP. split.
          -- exact (Hge1 x Hx).
          -- rewrite addnC. rewrite addn1. rewrite ltnS.
             exact (HleB x Hx).
      + move/andP => [Hxl Hxiota].
        exact Hxl. }
  have Heq : CReq R (CRsum_list f l) (CRsum_list f lf) :=
    CRsum_list_perm (R := R) f l lf Hperm.
  apply (CRle_trans (R := R) (CRsum_list f l) (CRsum_list f lf)
                    (CRsum_list f (iota 1 B))).
  - exact (proj2 Heq).
  - exact Hflt.
Qed.

(* ============ 分析层：部分和 ≤ 级数极限 ============ *)

(* 非负项级数的部分和 ≤ 极限：u ≥ 0、CRsum u → l ⟹ CRsum u N ≤ l
   —— 用 CR_cv_bound_down（A ≤ u n 尾部 ⟹ A ≤ l）取 A := CRsum u N *)
Lemma CRsum_le_lim {R : ConstructiveReals} (u : nat -> CRcarrier R) (l : CRcarrier R)
  (Hpos : forall n, CRle R (CR_of_Q R Q0q) (u n))
  (Hcv : CR_cv R (CRsum u) l) :
  forall N : nat, CRle R (CRsum u N) l.
Proof.
  move => N.
  apply (CR_cv_bound_down (R := R) (CRsum u) (CRsum u N) l N).
  - move => n Hn.
    (* CRsum u N ≤ CRsum u n（N ≤ n）：n = N + (n-N)，对 d := n-N 归纳 *)
    move/leP: Hn => Hn'.
    have Hmono : forall d, CRle R (CRsum u N) (CRsum u (N + d)).
    { induction d as [| d IH].
      - rewrite addn0. apply CRle_refl.
      - (* CRsum u (N + d) ≤ CRsum u (N + d.+1) *)
        apply (CRle_trans (R := R) (CRsum u N)
                          (CRsum u (N + d))
                          (CRsum u (N + d.+1))).
        + exact IH.
        + rewrite addnS.
          (* 目标: CRsum u (S (N+d)) = CRsum u (N+d) + u (S(N+d)) *)
          change (CRle R (CRsum u (N + d))
                         (CRplus R (CRsum u (N + d)) (u (N + d).+1))).
          apply (CRle_trans (R := R) (CRsum u (N + d))
                            (CRplus R (CRsum u (N + d)) (CR_of_Q R Q0q))
                            (CRplus R (CRsum u (N + d)) (u (N + d).+1))).
          * rewrite (CRplus_0_r (R := R) (CRsum u (N + d))).
            apply CRle_refl.
          * apply (CRplus_le_compat_l (R := R) (CRsum u (N + d))
                                       (CR_of_Q R Q0q) (u (N + d).+1)).
            apply Hpos. }
    move: (Hmono (n - N)%N).
    (* 目标: CRle (CRsum u N) (CRsum u (N + (n - N))) → 把 N+(n-N) 写成 n *)
    rewrite (subnKC Hn').
    exact id.
  - exact Hcv.
Qed.

(* 非负项级数部分和的单调性：u ≥ 0 ⟹ CRsum u N ≤ CRsum u n（N ≤ n）
   —— CRsum_le_lim 的 N ≤ n 形式，正向不等式 ζ 部分和比较用 *)
Lemma CRsum_mono_le {R : ConstructiveReals} (u : nat -> CRcarrier R)
  (Hpos : forall n, CRle R (CR_of_Q R Q0q) (u n)) :
  forall N n : nat, (N <= n)%N -> CRle R (CRsum u N) (CRsum u n).
Proof.
  move => N n Hn.
  have Hmono : forall d, CRle R (CRsum u N) (CRsum u (N + d)).
  { induction d as [| d IH].
    - rewrite addn0. apply CRle_refl.
    - apply (CRle_trans (R := R) (CRsum u N)
                        (CRsum u (N + d))
                        (CRsum u (N + d.+1))).
      + exact IH.
      + rewrite addnS.
        change (CRle R (CRsum u (N + d))
                       (CRplus R (CRsum u (N + d)) (u (N + d).+1))).
        apply (CRle_trans (R := R) (CRsum u (N + d))
                          (CRplus R (CRsum u (N + d)) (CR_of_Q R Q0q))
                          (CRplus R (CRsum u (N + d)) (u (N + d).+1))).
        * rewrite (CRplus_0_r (R := R) (CRsum u (N + d))).
          apply CRle_refl.
        * apply (CRplus_le_compat_l (R := R) (CRsum u (N + d))
                                     (CR_of_Q R Q0q) (u (N + d).+1)).
          apply Hpos. }
  move: (Hmono (n - N)%N).
  rewrite (subnKC Hn).
  exact id.
Qed.


(* ============================================================
   L4 P→∞：组合正向主引理（∏_{p∈ps}(Σ_{e≤E} p^{-es}) ≤ ζ = 1 + l）
   —— 链：euler_finite_expand → uniq_subset_le → iota1_le_zeta
   ★ 里程碑：正向不等式完成（P→∞ 夹逼的下界侧）
   ============================================================ *)
(* iota 1 B 的拆解：B ≥ 1 ⟹ iota 1 B = iota 1 1 ++ iota 2 (B-1) *)
Lemma iota1_split (B : nat) (HB : (1 <= B)%N) :
  iota 1 B = iota 1 1 ++ iota 2 (B - 1).
Proof.
  rewrite -(iotaD 1 1 (B - 1)).
  f_equal.
  (* 1 + (B - 1) = B：subnKC 正是这个方向 *)
  rewrite (subnKC HB). reflexivity.
Qed.

(* iota 2 (B-1) = map (fun k => 2 + k) (iota 0 (B-1)) = map S(S) (iota 0 (B-1)) *)
Lemma iota2_map (B : nat) :
  iota 2 (B - 1) = [seq (2 + k)%N | k <- iota 0 (B - 1)].
Proof.
  rewrite -(iotaDl 2 0 (B - 1)). rewrite addn0. reflexivity.
Qed.

(* Σ_{n∈iota 1 B} inv_n_pow n s == 1 + Σ_{k=0}^{B-2} inv_n_pow (S(S k)) s（B ≥ 2） *)
Lemma iota1_sum_eq {R : ConstructiveReals} (s B : nat) (HB : (2 <= B)%N) :
  CReq R (CRsum_list (fun n => inv_n_pow n s) (iota 1 B))
         (CRplus R (CR_of_Q R Q1q)
                 (CRsum (fun k => inv_n_pow (S (S k)) s) (B - 2))).
Proof.
  have HB1 : (1 <= B)%N := ltnW HB.
  rewrite (iota1_split B HB1).
  rewrite (CRsum_list_cat (R := R) (fun n => inv_n_pow n s) (iota 1 1) (iota 2 (B - 1))).
  simpl. (* iota 1 1 = [1]，Σ[1] = inv_n_pow 1 s + 0 *)
  rewrite (CRplus_0_r (R := R) (inv_n_pow 1 s)). (* 消掉 + 0 *)
  (* Σ(iota 2 (B-1)) = Σ_{k} (2+k)^{-s} *)
  rewrite (iota2_map B).
  rewrite (CRsum_list_map (R := R) (fun n => inv_n_pow n s) (fun k => (2 + k)%N)
                          (iota 0 (B - 1))).
  apply (CRplus_morph R (inv_n_pow 1 s) (CR_of_Q R Q1q)
                       (inv_n_pow_one (R := R) s)
                       (CRsum_list (fun k => inv_n_pow (2 + k) s) (iota 0 (B - 1)))
                       (CRsum (fun k => inv_n_pow (S (S k)) s) (B - 2))).
  - (* 目标: CRsum_list (fun k => inv_n_pow (2+k) s) (iota 0 (B-1))
          == CRsum (fun k => inv_n_pow (S(S k)) s) (B-2)
        iota 0 (B-1) = iota 0 ((B-2)+1)（B ≥ 2 ⟹ 1 < B） *)
    rewrite -[iota 0 (B - 1)](congr1 (iota 0) (subnSK HB)).
    rewrite -[iota 0 ((B - 2).+1)](congr1 (iota 0) (addn1 (B - 2))).
    rewrite (CRsum_list_iota (R := R) (fun k => inv_n_pow (2 + k) s) (B - 2)).
    apply (CRsum_eq (R := R) (fun k => inv_n_pow (2 + k) s)
                    (fun k => inv_n_pow (S (S k)) s) (B - 2)).
    move => k Hk.
    apply CReq_refl.
Qed.

(* ============ 组合正向主引理 ============ *)

(* inv_n_pow 非负：0 ≤ n^{-s}（Qinv_n 0 = 1 ⟹ 0^{-s} = 1^s = 1 ≥ 0；用于 CRsum_le_lim Hpos） *)
Lemma inv_n_pow_ge0 {R : ConstructiveReals} (n s : nat) :
  CRle R (CR_of_Q R Q0q) (inv_n_pow n s).
Proof.
  unfold inv_n_pow.
  apply (CRpow_ge_zero (CR_of_Q R (Qinv_n n)) s).
  apply CR_of_Q_le.
  unfold Qinv_n, Q0q, Qle. simpl. lia.
Qed.

(* Σ_{n=1}^{B} n^{-s} ≤ 1 + l（l = ζ 级数 Σ_{n≥0}(S(S n))^{-s} 的极限）
   —— iota1_sum_eq（拆 1 与 2..B）+ CRsum_le_lim（部分和 ≤ 极限） *)
Lemma iota1_le_zeta {R : ConstructiveReals} (s B : nat) (Hs2 : (2 <= s)%nat)
  (HB : (2 <= B)%N) :
  CRle R (CRsum_list (fun n => inv_n_pow n s) (iota 1 B))
         (CRplus R (CR_of_Q R Q1q) (projT1 (zeta_series_cv (R := R) s Hs2))).
Proof.
  (* Σ_{n=1}^{B} n^{-s} == 1 + Σ_{k=0}^{B-2} (S(S k))^{-s} *)
  have Heq := iota1_sum_eq (R := R) s B HB.
  (* Σ_{k=0}^{B-2} (S(S k))^{-s} ≤ l（部分和 ≤ 极限，项非负） *)
  have Hle : CRle R
    (CRsum (fun k => inv_n_pow (S (S k)) s) (B - 2))
    (projT1 (zeta_series_cv (R := R) s Hs2)).
  { apply (CRsum_le_lim (R := R) (fun k => inv_n_pow (S (S k)) s)
                        (projT1 (zeta_series_cv (R := R) s Hs2))).
    - move => k. apply (inv_n_pow_ge0 (R := R) (S (S k)) s).
    - exact (projT2 (zeta_series_cv (R := R) s Hs2)). }
  (* 用 Heq 把左边换成 1 + Σ，然后 1 + (Σ ≤ l) ≤ 1 + l *)
  apply (CRle_trans (R := R)
          (CRsum_list (fun n => inv_n_pow n s) (iota 1 B))
          (CRplus R (CR_of_Q R Q1q) (CRsum (fun k => inv_n_pow (S (S k)) s) (B - 2)))
          (CRplus R (CR_of_Q R Q1q) (projT1 (zeta_series_cv (R := R) s Hs2)))).
  - exact (proj1 (CReq_sym (CRsum_list (fun n => inv_n_pow n s) (iota 1 B))
                           (CRplus R (CR_of_Q R Q1q)
                                   (CRsum (fun k => inv_n_pow (S (S k)) s) (B - 2)))
                           Heq)).
  - apply (CRplus_le_compat_l (R := R) (CR_of_Q R Q1q)
                               (CRsum (fun k => inv_n_pow (S (S k)) s) (B - 2))
                               (projT1 (zeta_series_cv (R := R) s Hs2))).
    exact Hle.
Qed.

(* ============ 正向主引理：∏_{p∈ps}(Σ_{e≤E} p^{-es}) ≤ ζ = 1 + l ============ *)

(* ps 全素数且去重、s ≥ 2、E 任意：
   ∏_{p∈ps}(Σ_{e≤E} p^{-es}) ≤ 1 + Σ_{n≥2} n^{-s}（ζ 值）
   链：euler_finite_expand（∏==Σ_smooth x^{-s}）
     → CRsum_list_uniq_subset_le（Σ_smooth ≤ Σ_{n=1}^{B} n^{-s}，B=∏p^E）
     → iota1_le_zeta（Σ_{n=1}^{B} n^{-s} ≤ 1 + l） *)
Lemma euler_prod_le_zeta {R : ConstructiveReals} (ps : seq nat) (s E : nat)
  (Hs2 : (2 <= s)%nat) (Hps : all prime ps) (Huniq : uniq ps) :
  CRle R (CRprod_list (fun p => CRsum (fun e => inv_n_pow (p ^ e) s) E) ps)
         (CRplus R (CR_of_Q R Q1q) (projT1 (zeta_series_cv (R := R) s Hs2))).
Proof.
  (* 1) ∏(Σ_e) == Σ_{x∈smooth} x^{-s} *)
  have Hexpand := euler_finite_expand (R := R) ps s E Hps.
  (* 2) Σ_{x∈smooth} x^{-s} ≤ Σ_{n=1}^{B} n^{-s}（B = ∏p^E，smooth 互异且 ⊆[1..B]） *)
  pose B := nat_prod_list (fun p => (p ^ E)%N) ps.
  have Hsmooth_le : CRle R (CRsum_list (fun x => inv_n_pow x s) (smooth_list E ps))
                           (CRsum_list (fun n => inv_n_pow n s) (iota 1 B)).
  { apply (CRsum_list_uniq_subset_le (R := R) (fun n => inv_n_pow n s)
                                     (smooth_list E ps) B).
    - exact (smooth_list_uniq E ps Hps Huniq).
    - move => x Hx. exact (smooth_list_ge1 E ps Hps x Hx).
    - move => x Hx. exact (smooth_list_bound E ps Hps x Hx).
    - move => n. apply (inv_n_pow_ge0 (R := R) n s). }
  (* 3) Σ_{n=1}^{B} n^{-s} ≤ 1 + l：对 B case（0/1/≥2） *)
  have Hiota : CRle R (CRsum_list (fun n => inv_n_pow n s) (iota 1 B))
                       (CRplus R (CR_of_Q R Q1q) (projT1 (zeta_series_cv (R := R) s Hs2))).
  { destruct B as [| [| B'] ].
    - (* B = 0：iota 1 0 = []，Σ = 0 ≤ 1 + l *)
      simpl. apply (CRle_trans (R := R) (CR_of_Q R Q0q)
                                (CR_of_Q R Q1q)
                                (CRplus R (CR_of_Q R Q1q)
                                        (projT1 (zeta_series_cv (R := R) s Hs2)))).
      + exact (CRle_0_one (R := R)).
      + (* 1 ≤ 1 + l：1 + 0 ≤ 1 + l 归一化（0 ≤ l） *)
        have H10 : CRle R (CRplus R (CR_of_Q R Q1q) (CR_of_Q R Q0q))
                           (CRplus R (CR_of_Q R Q1q) (projT1 (zeta_series_cv (R := R) s Hs2))).
        { apply (CRplus_le_compat_l (R := R) (CR_of_Q R Q1q)
                                     (CR_of_Q R Q0q) (projT1 (zeta_series_cv (R := R) s Hs2))).
          apply (series_cv_nonneg (R := R)
                   (fun n => inv_n_pow (S (S n)) s)
                   (projT1 (zeta_series_cv (R := R) s Hs2))).
          * move => n. apply (inv_n_pow_ge0 (R := R) (S (S n)) s).
          * exact (projT2 (zeta_series_cv (R := R) s Hs2)). }
        apply (proj2 (CRle_morph R
                        (CR_of_Q R Q1q)
                        (CRplus R (CR_of_Q R Q1q) (CR_of_Q R Q0q))
                        (CReq_sym (CRplus R (CR_of_Q R Q1q) (CR_of_Q R Q0q))
                                  (CR_of_Q R Q1q)
                                  (CRplus_0_r (R := R) (CR_of_Q R Q1q)))
                        (CRplus R (CR_of_Q R Q1q) (projT1 (zeta_series_cv (R := R) s Hs2)))
                        (CRplus R (CR_of_Q R Q1q) (projT1 (zeta_series_cv (R := R) s Hs2)))
                        (CReq_refl (R := R) (CRplus R (CR_of_Q R Q1q)
                                                      (projT1 (zeta_series_cv (R := R) s Hs2)))))).
        exact H10.
    - (* B = 1：iota 1 1 = [1]，Σ = inv_n_pow 1 s + 0 == inv_n_pow 1 s == 1 ≤ 1 + l *)
      simpl. (* CRsum_list f [1] = inv_n_pow 1 s + 0 *)
      apply (CRle_trans (R := R)
              (CRplus R (inv_n_pow 1 s) (CR_of_Q R Q0q))
              (inv_n_pow 1 s)
              (CRplus R (CR_of_Q R Q1q)
                      (projT1 (zeta_series_cv (R := R) s Hs2)))).
      + apply (proj2 (CRplus_0_r (R := R) (inv_n_pow 1 s))).
      + apply (CRle_trans (R := R) (inv_n_pow 1 s)
                                (CR_of_Q R Q1q)
                                (CRplus R (CR_of_Q R Q1q)
                                        (projT1 (zeta_series_cv (R := R) s Hs2)))).
        * exact (proj2 (inv_n_pow_one (R := R) s)).
        * (* 1 ≤ 1 + l：1 + 0 ≤ 1 + l 归一化（0 ≤ l） *)
          have H11 : CRle R (CRplus R (CR_of_Q R Q1q) (CR_of_Q R Q0q))
                             (CRplus R (CR_of_Q R Q1q) (projT1 (zeta_series_cv (R := R) s Hs2))).
          { apply (CRplus_le_compat_l (R := R) (CR_of_Q R Q1q)
                                       (CR_of_Q R Q0q) (projT1 (zeta_series_cv (R := R) s Hs2))).
            apply (series_cv_nonneg (R := R)
                     (fun n => inv_n_pow (S (S n)) s)
                     (projT1 (zeta_series_cv (R := R) s Hs2))).
            * move => n. apply (inv_n_pow_ge0 (R := R) (S (S n)) s).
            * exact (projT2 (zeta_series_cv (R := R) s Hs2)). }
          exact (proj2 (CRle_morph R
                          (CR_of_Q R Q1q)
                          (CRplus R (CR_of_Q R Q1q) (CR_of_Q R Q0q))
                          (CReq_sym (CRplus R (CR_of_Q R Q1q) (CR_of_Q R Q0q))
                                    (CR_of_Q R Q1q)
                                    (CRplus_0_r (R := R) (CR_of_Q R Q1q)))
                          (CRplus R (CR_of_Q R Q1q) (projT1 (zeta_series_cv (R := R) s Hs2)))
                          (CRplus R (CR_of_Q R Q1q) (projT1 (zeta_series_cv (R := R) s Hs2)))
                          (CReq_refl (R := R) (CRplus R (CR_of_Q R Q1q)
                                                        (projT1 (zeta_series_cv (R := R) s Hs2)))))
                  H11).
    - (* B ≥ 2：iota1_le_zeta *)
      have HB2 : (2 <= (S (S B')))%N.
      { apply/leP. apply le_n_S. apply le_n_S. exact (Nat.le_0_l B'). }
      exact (iota1_le_zeta (R := R) s (S (S B')) Hs2 HB2). }
  (* 4) 组合：∏ == Σ_smooth ≤ Σ_{n=1}^{B} ≤ 1 + l *)
  apply (CRle_trans (R := R)
          (CRprod_list (fun p => CRsum (fun e => inv_n_pow (p ^ e) s) E) ps)
          (CRsum_list (fun x => inv_n_pow x s) (smooth_list E ps))
          (CRplus R (CR_of_Q R Q1q) (projT1 (zeta_series_cv (R := R) s Hs2)))).
  - exact (proj2 Hexpand).
  - apply (CRle_trans (R := R)
           (CRsum_list (fun x => inv_n_pow x s) (smooth_list E ps))
           (CRsum_list (fun n => inv_n_pow n s) (iota 1 B))
           (CRplus R (CR_of_Q R Q1q) (projT1 (zeta_series_cv (R := R) s Hs2)))).
    + exact Hsmooth_le.
    + exact Hiota.
Qed.


(* ============================================================
   L4 P→∞：反向分解砖块（ζ ≤ ∏(1-p^{-s})^{-1} + 尾部）
   —— not_smooth_has_big_prime / not_smooth_le_gt / logn_split / mul_in_smooth
   —— smooth_in（素因子 ⊆ ps ⟹ ∈ smooth_list）与反向主引理待续
   ============================================================ *)
(* ¬smooth_le P n ⟹ ∃ q ∈ primes n, q > P（非 smooth ⟹ 有素因子 > P）
   —— smooth_le 的定义是 all (≤ P)，否定展开后有元素 > P
   —— 结论用 Prop exists（Set sig 无法从 allPn 消除） *)
Lemma not_smooth_has_big_prime (P n : nat) :
  ~~ (smooth_le P n) -> exists q : nat, q \in primes n /\ (P < q)%nat.
Proof.
  rewrite /smooth_le.
  move => H.
  move: H => /allPn [q Hq Hnot].
  exists q. split.
  - exact Hq.
  - move: Hnot. rewrite -ltnNge. move => Hqgt. exact Hqgt.
Qed.

(* q ∈ primes n ⟹ q | n ⟹ n ≥ q（q > 0）⟹ n > P（q > P）
   —— 非 smooth ⟹ n 有素因子 > P ⟹ n > P *)
Lemma not_smooth_le_gt (P n : nat) (Hn1 : (1 <= n)%nat) :
  ~~ (smooth_le P n) -> (P < n)%nat.
Proof.
  move => Hnot.
  destruct (not_smooth_has_big_prime P n Hnot) as [q [Hq Hqgt]].
  rewrite mem_primes in Hq.
  move/andP : Hq => [Hqpr /andP [Hq0 Hqdvd]].
  (* q | n 且 n > 0 ⟹ q ≤ n；P < q ≤ n ⟹ P < n *)
  have Hqle : (q <= n)%nat := @dvdn_leq q n Hq0 Hqdvd.
  (* case q = n：P < n 直接由 Hqgt；case q < n：ltn_trans *)
  destruct (Nat.eqb_spec q n) as [Hqn | Hqn'].
  - rewrite Hqn in Hqgt. exact Hqgt.
  - have Hqlt : (q < n)%nat.
    { rewrite ltn_neqAle. apply/andP. split.
      - apply/eqP. exact Hqn'.
      - exact Hqle. }
    exact (ltn_trans Hqgt Hqlt).
Qed.


(* ============ smooth 覆盖：n ≤ N 且素因子 ⊆ ps ⟹ n ∈ smooth_list N ps ============ *)

(* 核心：n = (n 去 p 部分) · p^{logn p n}（pfactor_dvdn + divnK） *)
Lemma logn_split (p n : nat) (Hp : prime p) (Hn0 : (0 < n)%nat) :
  (n = (divn n (p ^ logn p n)) * p ^ logn p n)%N.
Proof.
  have Hdvd : p ^ logn p n %| n.
  { rewrite (@pfactor_dvdn p (logn p n) n Hp Hn0). apply leqnn. }
  rewrite (divnK Hdvd). reflexivity.
Qed.

(* 乘入保持：x ∈ smooth_list E ps'、e ≤ E ⟹ x·p^e ∈ smooth_list E (p::ps') *)
(* 乘入保持：x ∈ smooth_list E ps'、e ≤ E ⟹ x·p^e ∈ smooth_list E (p::ps') —— allpairs_f 一行 *)
Lemma mul_in_smooth (E p : nat) (ps' : seq nat) (x : nat) (e : nat)
  (Hx : x \in smooth_list E ps') (He : (e <= E)%N) :
  (x * p ^ e)%N \in smooth_list E (p :: ps').
Proof.
  rewrite /smooth_list.
  apply (@allpairs_f nat nat nat (fun x0 e0 => (x0 * p ^ e0)%N)
                     (smooth_list E ps') (iota 0 (E + 1)) x e).
  - exact Hx.
  - rewrite mem_iota. apply/andP. split. done.
    rewrite add0n. rewrite addn1. rewrite ltnS. exact He.
Qed.

(* smooth_in：n ≥ 1、素因子(n) ⊆ ps、∀p∈ps logn p n ≤ E ⟹ n ∈ smooth_list E ps
   —— L4 P→∞ 反向分解的核心：每个素因子在 ps 内且指数 ≤ E 的 n 一定被
      smooth_list E ps 枚举到（唯一分解 + 归纳展开）
   —— 对 ps 归纳：
      * 基础 []：素因子 ⊆ [] ⟹ primes n = []（eq_all+all_pred0+size_eq0）
        ⟹ n < 2（primes_eq0）⟹ n = 1 ∈ [::1]（mem_seq1）
      * 归纳 p::ps'：logn_split 剥离 n = x·p^e（x = n %/ p^e, e = logn p n），
        p ∤ x（logn_div: logn p x = logn p n - logn p (p^e) = e - e = 0），
        x 素因子 ⊆ ps'（q|x ⟹ q|n ⟹ q∈p::ps'，q≠p ⟹ q∈ps'），
        指数 logn q x ≤ logn q n（lognM 单调）≤ E（Hexp），
        IH 给 x ∈ smooth_list E ps'，mul_in_smooth 乘回 x·p^e ∈ smooth_list E (p::ps')。 *)
Lemma smooth_in (E : nat) (ps : seq nat) (n : nat)
  (Hps : all prime ps) (Hn1 : (1 <= n)%nat)
  (Hsub : all (fun q => q \in ps) (primes n))
  (Hexp : forall p, p \in ps -> (logn p n <= E)%nat) :
  n \in smooth_list E ps.
Proof.
  revert n Hn1 Hsub Hexp.
  elim: ps Hps => [| p ps' IH] Hps n Hn1 Hsub Hexp.
  - (* 基础：ps = [] ⟹ smooth_list E [] = [:: 1]，需证 n = 1 *)
    rewrite /smooth_list.
    (* 素因子(n) ⊆ [] ⟹ primes n = [] *)
    have Hpr : primes n = [::].
    { have Hpred : (fun q : nat => q \in [::]) =1 pred0.
      { move => q. rewrite in_nil. reflexivity. }
      move: Hsub. rewrite (eq_all Hpred). rewrite all_pred0.
      move => Hsz0. apply/eqP. rewrite -size_eq0. exact Hsz0. }
    (* primes n = [] ⟹ n < 2（primes_eq0） *)
    have Hn2 : (n < 2)%nat.
    { rewrite -(primes_eq0 n). apply/eqP. exact Hpr. }
    (* n < 2 且 1 ≤ n ⟹ n = 1 *)
    have Hn1eq : n = 1%nat.
    { apply/eqP. rewrite eqn_leq. apply/andP. split.
      - move: Hn2. rewrite ltnS. exact id.
      - exact Hn1. }
    (* n ∈ [:: 1] ⟺ n == 1 *)
    rewrite Hn1eq. rewrite mem_seq1. reflexivity.
  - (* 归纳：ps = p :: ps' *)
    have Hp : prime p := allP Hps p (mem_head p ps').
    have Hps' : all prime ps'.
    { apply/allP. move => y Hy.
      apply (allP Hps y).
      rewrite in_cons. apply/orP. right. exact Hy. }
    have Hn0 : (0 < n)%nat := Hn1.
    (* 剥离：n = x·p^e，x = n %/ p^e，e = logn p n（logn_split 已 Qed） *)
    have Hsplit := logn_split p n Hp Hn0.
    pose x := n %/ p ^ logn p n.
    pose e := logn p n.
    have Hsplit' : (n = x * p ^ e)%N.
    { rewrite /x /e. exact Hsplit. }
    (* 0 < x：n = x·p^e > 0 且 p^e > 0 ⟹ x > 0 *)
    have Hpe0 : (0 < p ^ e)%nat.
    { rewrite expn_gt0. rewrite (@prime_gt0 p Hp). simpl. reflexivity. }
    have Hx0 : (0 < x)%nat.
    { move: Hn0. rewrite Hsplit'. rewrite muln_gt0.
      move/andP => [Hx _]. exact Hx. }
    (* p ∤ x：logn p x = logn p n - logn p (p^e) = e - e = 0 ⟹ p ∉ primes x *)
    have Hlogx : logn p x = 0%nat.
    { rewrite /x.
      have Hdvd : p ^ e %| n.
      { rewrite (@pfactor_dvdn p e n Hp Hn0). apply leqnn. }
      rewrite (@logn_div p (p ^ e) n Hdvd).
      rewrite /e.
      rewrite (@lognX p p (logn p n)).
      rewrite (@logn_prime p p Hp).
      rewrite eqxx.
      rewrite muln1.
      rewrite subnn. reflexivity. }
    have Hpx : ~~ (p %| x).
    { apply/negP. move => Hpdvd.
      have Hlg : (0 < logn p x)%nat.
      { rewrite logn_gt0. rewrite mem_primes. apply/andP. split. exact Hp.
        apply/andP. split. exact Hx0. exact Hpdvd. }
      rewrite Hlogx in Hlg. done. }
    (* x | n：n = x·p^e ⟹ x | n *)
    have Hxdn : x %| n.
    { rewrite Hsplit'. apply dvdn_mulr. apply dvdnn. }
    (* 素因子(x) ⊆ ps' *)
    have Hxsub : all (fun q => q \in ps') (primes x).
    { apply/allP. move => q Hq.
      rewrite mem_primes in Hq. move/andP : Hq => [Hqpr /andP [Hqx0 Hqdx]].
      have Hqdn : q %| n := dvdn_trans Hqdx Hxdn.
      have Hqin : q \in primes n.
      { rewrite mem_primes. apply/andP. split. exact Hqpr. apply/andP. split.
        exact Hn0. exact Hqdn. }
      have Hqps : q \in p :: ps' := allP Hsub q Hqin.
      rewrite in_cons in Hqps. move/orP : Hqps => [Hqp | Hqps'].
      - (* q == p：与 p ∤ x 矛盾 *)
        move/eqP : Hqp => Hqp'. rewrite Hqp' in Hqdx.
        move/negP : Hpx => Hpx'. exfalso. exact (Hpx' Hqdx).
      - exact Hqps'. }
    (* 指数：∀q∈ps', logn q x ≤ E（logn q x ≤ logn q n ≤ E） *)
    have Hxexp : forall q, q \in ps' -> (logn q x <= E)%nat.
    { move => q Hqps'.
      have Hqps : q \in p :: ps'.
      { rewrite in_cons. apply/orP. right. exact Hqps'. }
      have Hle : (logn q x <= logn q n)%nat.
      { (* logn q n = logn q (x·p^e) = logn q x + logn q (p^e) ≥ logn q x *)
        rewrite Hsplit'.
        rewrite (@lognM q x (p ^ e) Hx0 Hpe0).
        apply leq_addr. }
      exact (leq_trans Hle (Hexp q Hqps)). }
    (* IH：x ∈ smooth_list E ps'（Hx0 : 0 < x 即 1 ≤ x） *)
    have Hx : x \in smooth_list E ps' := IH Hps' x Hx0 Hxsub Hxexp.
    (* e ≤ E：Hexp p（p ∈ p::ps'） *)
    have HeE : (e <= E)%nat := Hexp p (mem_head p ps').
    (* 乘回：x·p^e ∈ smooth_list E (p::ps')，rewrite n = x·p^e *)
    have Hnins : (x * p ^ e)%N \in smooth_list E (p :: ps') :=
      mul_in_smooth E p ps' x e Hx HeE.
    rewrite Hsplit'. exact Hnins.
Qed.

(* ============================================================
   L4 P→∞：反向主引理砖块（smooth_cover）
   —— logn_le_exp_bound（指数界）+ smooth_cover（n≤N 素因子⊆ps ⟹ ∈smooth_list）
   ============================================================ *)

(* 指数界：n ≤ 2^E、p 素数、p ∈ primes n ⟹ logn p n ≤ E
   —— 反向主引理调用 smooth_in 的关键：smooth_in 需要 ∀p∈ps, logn p n ≤ E，
     而这里从「n 被 2^E 界住」给出。证明链：
     p^{logn p n} | n（pfactor_dvdn）⟹ p^{logn p n} ≤ n（dvdn_leq）
     ⟹ 2^{logn p n} ≤ p^{logn p n}（leq_exp2r，p≥2）⟹ 2^{logn p n} ≤ 2^E
     ⟹ logn p n ≤ E（leq_exp2l）。 *)
Lemma logn_le_exp_bound (p n E : nat) (Hp : prime p)
  (Hpn : p \in primes n) (HnE : (n <= 2 ^ E)%N) : (logn p n <= E)%N.
Proof.
  (* p^{logn p n} | n（pfactor_dvdn 取 n = logn p n）⟹ p^{logn p n} ≤ n *)
  have Hn0 : (0 < n)%N.
  { rewrite mem_primes in Hpn. move/andP : Hpn => [_ /andP [Hn0 _]].
    exact Hn0. }
  have Hpe : (p ^ logn p n <= n)%N.
  { have Hdvd : p ^ logn p n %| n.
    { rewrite (@pfactor_dvdn p (logn p n) n Hp Hn0).
      apply leqnn. }
    exact (dvdn_leq Hn0 Hdvd). }
  (* p ≥ 2 ⟹ p^{logn p n} ≥ 2^{logn p n}（leq_exp2r：0<e ⟹ (m^e≤n^e)=(m≤n)） *)
  have Hp2 : (2 <= p)%N := prime_gt1_mc p Hp.
  have H2le : (2 ^ logn p n <= p ^ logn p n)%N.
  { have Hlg0 : (0 < logn p n)%N.
    { rewrite logn_gt0. exact Hpn. }
    rewrite (@leq_exp2r 2 p (logn p n) Hlg0). exact Hp2. }
  (* 2^{logn p n} ≤ p^{logn p n} ≤ n ≤ 2^E ⟹ logn p n ≤ E（leq_exp2l） *)
  have H2E : (2 ^ logn p n <= 2 ^ E)%N.
  { exact (leq_trans H2le (leq_trans Hpe HnE)). }
  (* leq_exp2l：1<2 ⟹ (2^a ≤ 2^b) = (a ≤ b) *)
  have H2gt1 : (1 < 2)%N := ltnSn 1.
  move: H2E. rewrite (@leq_exp2l 2 (logn p n) E H2gt1). exact id.
Qed.

(* smooth_cover：n ≤ N、素因子(n) ⊆ ps、N ≤ 2^E、ps 全素数
   ⟹ n ∈ smooth_list E ps
   —— smooth_in 的直接实例化：logn_le_exp_bound 提供指数条件
     （p ∈ ps ⟹ prime p（Hps）；logn p n = 0 平凡或 p|n ⟹ p∈primes n ⟹ 指数界）。 *)
Lemma smooth_cover (E N : nat) (ps : seq nat) (n : nat)
  (Hps : all prime ps) (Hn1 : (1 <= n)%N)
  (Hsub : all (fun q => q \in ps) (primes n))
  (HnN : (n <= N)%N) (HNE : (N <= 2 ^ E)%N) :
  n \in smooth_list E ps.
Proof.
  apply (smooth_in E ps n Hps Hn1 Hsub).
  move => p Hpin.
  (* p ∈ ps ⟹ prime p（Hps）；指数界：logn p n = 0 平凡，或 p|n ⟹ logn_le_exp_bound *)
  have Hpp : prime p := allP Hps p Hpin.
  destruct (logn p n) as [| lg'] eqn:Hlg.
  - (* logn p n = 0 ≤ E *)
    exact (leq0n E).
  - (* logn p n = lg'.+1 > 0 ⟹ p | n（logn_gt0 反向）⟹ p ∈ primes n ⟹ 用 logn_le_exp_bound *)
    have Hpos : (0 < logn p n)%N.
    { rewrite Hlg. apply ltn0Sn. }
    have Hpn : p \in primes n.
    { rewrite -logn_gt0. exact Hpos. }
    have Hn2E : (n <= 2 ^ E)%N := leq_trans HnN HNE.
    rewrite -Hlg.
    exact (logn_le_exp_bound p n E Hpp Hpn Hn2E).
Qed.

(* ============================================================
   L4 P→∞：反向主引理地基（subset_le + primes_leq）
   —— CRsum_list_subset_le：列表子集和 ≤（反向夹逼核心）
   —— primes_leq：≤P 素数列表（smooth 判定与素因子⊆ps 桥接）
   ============================================================ *)

(* l 的元素 ⊆ m 的元素、两者 uniq、f ≥ 0 ⟹ Σf l ≤ Σf m
   —— 反向主引理核心工具：smooth 段（∈smooth_list 的 n）≤ Σ_{smooth_list}；
      非 smooth 段 ≤ Σ_{尾部}。m uniq 保证不重计。
   —— 证明：m 中属于 l 的部分 mf = filter(∈l) m；Σf mf ≤ Σf m（filter_le）；
      l 与 mf 置换（都是 uniq 且元素相同 ⟹ uniq_perm）。 *)
Lemma CRsum_list_subset_le {R : ConstructiveReals} (f : nat -> CRcarrier R)
  (l m : seq nat)
  (Huniql : uniq l) (Huniqm : uniq m)
  (Hsub : forall x, x \in l -> x \in m)
  (Hpos : forall n, CRle R (CR_of_Q R Q0q) (f n)) :
  CRle R (CRsum_list f l) (CRsum_list f m).
Proof.
  pose mf := [seq x <- m | x \in l].
  have Hflt : CRle R (CRsum_list f mf) (CRsum_list f m).
  { unfold mf. apply (CRsum_list_filter_le (R := R) f m (fun x => x \in l)).
    move => x Hx. apply Hpos. }
  have Hperm : perm_eq l mf.
  { apply (@uniq_perm nat l mf).
    - exact Huniql.
    - unfold mf. apply (subseq_uniq (filter_subseq (fun x => x \in l) m)).
      exact Huniqm.
    - move => x.
      rewrite mem_filter. apply/idP/idP.
      + move => Hx. apply/andP. split. exact Hx. exact (Hsub x Hx).
      + move/andP => [Hxl _]. exact Hxl. }
  have Heq : CReq R (CRsum_list f l) (CRsum_list f mf) :=
    CRsum_list_perm (R := R) f l mf Hperm.
  apply (CRle_trans (R := R) (CRsum_list f l) (CRsum_list f mf)
                    (CRsum_list f m)).
  - exact (proj2 Heq).
  - exact Hflt.
Qed.

(* ≤P 素数列表：1..P 中的素数（去重、全素数）
   —— 反向主引理里 smooth 判定 smooth_le P（素因子 ≤ P）与
      smooth_cover 的素因子⊆ps 之间的桥：ps := primes_leq P 时二者一致。 *)
Definition primes_leq (P : nat) : seq nat :=
  [seq p <- iota 1 P | prime p].

(* 全素数（filter 保证） *)
Lemma primes_leq_all_prime (P : nat) : all prime (primes_leq P).
Proof.
  apply/allP. move => p Hp. rewrite /primes_leq mem_filter in Hp.
  move/andP : Hp => [Hp _]. exact Hp.
Qed.

(* 去重（iota 去重 + filter 保去重） *)
Lemma primes_leq_uniq (P : nat) : uniq (primes_leq P).
Proof.
  apply (subseq_uniq (filter_subseq (fun p : nat => prime p) (iota 1 P))).
  apply iota_uniq.
Qed.

(* 关键：p ∈ primes_leq P ⟹ p ≤ P（bool 蕴含直接证） *)
Lemma mem_primes_leq_le (p P : nat) (Hin : p \in primes_leq P) : (p <= P)%N.
Proof.
  rewrite /primes_leq mem_filter in Hin.
  move/andP : Hin => [_ Hiota].
  rewrite mem_iota in Hiota.
  move/andP : Hiota => [_ Hlt].
  move: Hlt. rewrite addnC. rewrite addn1. rewrite ltnS. exact id.
Qed.

(* 关键：prime p ∧ p ≤ P ⟹ p ∈ primes_leq P（bool 蕴含直接证） *)
Lemma primes_leq_mem (p P : nat) (Hp : prime p) (HpP : (p <= P)%N) :
  p \in primes_leq P.
Proof.
  rewrite /primes_leq mem_filter. apply/andP. split. exact Hp.
  rewrite mem_iota. apply/andP. split.
  - apply (@prime_gt0 p Hp).
  - rewrite addnC. rewrite addn1. rewrite ltnS. exact HpP.
Qed.

(* ============================================================
   L4 P→∞：反向主引理（ζ 部分和 ≤ ∏(Σ_e) + 尾部）
   —— le_smooth_le / smooth_prefix_cover / iota_prefix_tail /
      zeta_partial_le_euler_prod_tail
   —— 结构：Σ_{n=1}^{N} = Σ_{n=1}^{P} + Σ_{n=P+1}^{N}（iota 拆分）；
      [1..P] 全 smooth（n ≤ P ⟹ 素因子 ≤ n ≤ P）⟹ smooth_cover 覆盖进
      smooth_list E ps ⟹ ∏ 展开；[P+1..N] 即尾部（n > P）。
   ============================================================ *)

(* n ≤ P ⟹ smooth_le P n（素因子 q | n ⟹ q ≤ n ≤ P） *)
Lemma le_smooth_le (P n : nat) (Hn : (n <= P)%N) : smooth_le P n.
Proof.
  apply/allP. move => q Hq.
  rewrite mem_primes in Hq. move/andP : Hq => [Hqpr /andP [Hq0 Hqdvd]].
  have Hqle : (q <= n)%N := dvdn_leq Hq0 Hqdvd.
  exact (leq_trans Hqle Hn).
Qed.

(* n ≤ P ≤ N ≤ 2^E ⟹ n ∈ smooth_list E (primes_leq P)
   —— smooth_cover 实例化：n ≤ P 时素因子自动 ≤ P（le_smooth_le），
     且 n ≤ N ≤ 2^E 给指数界。 *)
Lemma smooth_prefix_cover (E N P n : nat) (Hn1 : (1 <= n)%N)
  (HnP : (n <= P)%N) (HPN : (P <= N)%N) (HNE : (N <= 2 ^ E)%N) :
  n \in smooth_list E (primes_leq P).
Proof.
  apply (smooth_cover E N (primes_leq P) n (primes_leq_all_prime P) Hn1).
  - apply/allP. move => q Hq.
    have Hqpr : prime q.
    { rewrite mem_primes in Hq. move/andP : Hq => [Hqpr _]. exact Hqpr. }
    have Hqle : (q <= P)%N.
    { move: (le_smooth_le P n HnP). rewrite /smooth_le. move => /allP Hs'.
      exact (Hs' q Hq). }
    exact (primes_leq_mem q P Hqpr Hqle).
  - exact (leq_trans HnP HPN).
  - exact HNE.
Qed.

(* iota 1 N = iota 1 P ++ iota (P+1) (N-P)（P ≤ N）
   —— iotaD：iota 1 (P+(N-P)) = iota 1 P ++ iota (1+P) (N-P) *)
Lemma iota_prefix_tail (N P : nat) (HPN : (P <= N)%N) :
  iota 1 N = iota 1 P ++ iota (P + 1) (N - P).
Proof.
  rewrite addnC. (* RHS：iota (P+1) 参数 P+1 → 1+P *)
  rewrite -(iotaD 1 P (N - P)). (* RHS：iota 1 P ++ iota (1+P) (N-P) → iota 1 (P + (N-P)) *)
  rewrite (subnKC HPN). (* RHS：iota 1 (P + (N-P)) → iota 1 N *)
  reflexivity.
Qed.

(* 反向主引理：Σ_{n=1}^{N} n^{-s} ≤ Σ_{x∈smooth_list E (primes_leq P)} x^{-s} + Σ_{n=P+1}^{N} n^{-s}
   —— P ≤ N ≤ 2^E；[1..P] 全被 smooth_list 覆盖（smooth_prefix_cover），
     [P+1..N] 即尾部（n > P）。
   —— 这是 euler_product 主定理的上界侧：ζ_N ≤ ∏(Σ_e) + 尾部。 *)
Lemma zeta_partial_le_euler_prod_tail {R : ConstructiveReals} (s E N P : nat)
  (Hs2 : (2 <= s)%N) (HPN : (P <= N)%N) (HNE : (N <= 2 ^ E)%N) :
  CRle R (CRsum_list (fun n => inv_n_pow n s) (iota 1 N))
         (CRplus R
            (CRsum_list (fun n => inv_n_pow n s)
                        (smooth_list E (primes_leq P)))
            (CRsum_list (fun n => inv_n_pow n s) (iota (P + 1) (N - P)))).
Proof.
  rewrite (iota_prefix_tail N P HPN).
  apply (CRle_trans (R := R)
           (CRsum_list (fun n => inv_n_pow n s)
                       (iota 1 P ++ iota (P + 1) (N - P)))
           (CRplus R (CRsum_list (fun n => inv_n_pow n s) (iota 1 P))
                    (CRsum_list (fun n => inv_n_pow n s) (iota (P + 1) (N - P))))
           (CRplus R (CRsum_list (fun n => inv_n_pow n s)
                                 (smooth_list E (primes_leq P)))
                    (CRsum_list (fun n => inv_n_pow n s) (iota (P + 1) (N - P))))).
  - apply (proj2 (CRsum_list_cat (R := R) (fun n => inv_n_pow n s)
                                 (iota 1 P) (iota (P + 1) (N - P)))).
  - apply (CRplus_le_compat_r (R := R)
             (CRsum_list (fun n => inv_n_pow n s) (iota (P + 1) (N - P)))
             (CRsum_list (fun n => inv_n_pow n s) (iota 1 P))
             (CRsum_list (fun n => inv_n_pow n s)
                         (smooth_list E (primes_leq P)))).
    apply (CRsum_list_subset_le (R := R) (fun n => inv_n_pow n s)
            (iota 1 P) (smooth_list E (primes_leq P))).
    + apply iota_uniq.
    + exact (smooth_list_uniq E (primes_leq P) (primes_leq_all_prime P)
                             (primes_leq_uniq P)).
    + move => n Hn.
      have Hn1 : (1 <= n)%N.
      { rewrite mem_iota in Hn. move/andP : Hn => [Hn1 _]. exact Hn1. }
      have HnP : (n <= P)%N.
      { rewrite mem_iota in Hn. move/andP : Hn => [_ Hlt].
        move: Hlt. rewrite addnC. rewrite addn1. rewrite ltnS. exact id. }
      exact (smooth_prefix_cover E N P n Hn1 HnP HPN HNE).
    + move => n. apply (inv_n_pow_ge0 (R := R) n s).
Qed.

(* ============================================================
   L4 P→∞：尾部界（Σ_{n=P+1}^{N} n^{-s} ≤ 1/P）
   —— iota_succ_plus / telescope_unshift / CRsum_le_pointwise /
      zeta_tail_bound_list / zeta_tail_bound_list_noabs
   —— 链：iota (P+1) (N-P) 的元素 = S(P+k)；逐项 zeta_tail_term_le
      ≤ 1/(P+k) - 1/(S(P+k))；telescope_unshift 求和 = 1/P - 1/(S(P+m)) ≤ 1/P。
   —— 注意：本区段大量 nat 算术，临时打开 nat_scope 让 + / - / <= 解析为
      mathcomp nat 运算（CR 表达式已全限定 CRle/CRplus 等，不受影响）。 *)
Local Open Scope nat_scope.

(* iota (P+1) m = [seq S (P+k) | k <- iota 0 m]
   —— 元素形式：iota 平移 = map S∘(加P)
   —— 逐项：S(P+k) = P + S k（addnS 反向）→ P + (1+k)（S k 定义性 = 1+k）→ P+1+k（addnA 反向） *)
Lemma iota_succ_plus (P m : nat) :
  iota (P + 1)%N m = [seq S (P + k)%N | k <- iota 0 m].
Proof.
  rewrite -[(P + 1)%N]addn0.
  rewrite (iotaDl (P + 1)%N 0 m).
  apply (proj1 (eq_in_map (fun i : nat => (P + 1 + i)%N) (fun k : nat => S (P + k)%N)
                          (iota 0 m))).
  move => k Hk.
  rewrite -addnS. (* S(P+k) → P+S k *)
  change (P + S k)%N with (P + (1 + k))%N. (* S k 定义性 = 1+k，得 P+(1+k) *)
  rewrite -addnA. (* P+(1+k) → P+1+k *)
  reflexivity.
Qed.

(* 非移位望远镜和：Σ_{k=0}^{p} (1/(A+k) - 1/(S(A+k))) == 1/A - 1/(S(A+p))
   —— 直接归纳（镜像 telescope_shift，A+k 而非 S A + k） *)
Lemma telescope_unshift {R : ConstructiveReals} (A p : nat) :
  CReq R (CRsum (fun k : nat => CRminus R (CR_of_Q R (Qinv_n (A + k)))
                                        (CR_of_Q R (Qinv_n (S (A + k))))) p)
         (CRminus R (CR_of_Q R (Qinv_n A))
                   (CR_of_Q R (Qinv_n (S (A + p))))).
Proof.
  induction p as [|p IH].
  - simpl. rewrite (addn0 A). reflexivity.
  - rewrite (addnS A p).
    simpl.
    rewrite IH.
    rewrite (addnS A p).
    apply (CRminus_add_cancel (R := R) (CR_of_Q R (Qinv_n A))
                              (CR_of_Q R (Qinv_n (S (A + p))))
                              (CR_of_Q R (Qinv_n (S (S (A + p)))))).
Qed.

(* 逐项 ≤ ⟹ 求和 ≤：∀k ≤ N, u k ≤ v k ⟹ Σu N ≤ Σv N（归纳） *)
Lemma CRsum_le_pointwise {R : ConstructiveReals} (u v : nat -> CRcarrier R) (N : nat)
  (H : forall k : nat, (k <= N)%N -> CRle R (u k) (v k)) :
  CRle R (CRsum u N) (CRsum v N).
Proof.
  induction N as [|N IH].
  - simpl. apply (H 0%nat). apply leqnn.
  - simpl.
    apply (CRplus_le_compat (R := R) (CRsum u N) (CRsum v N) (u N.+1) (v N.+1)).
    + apply IH. move => k Hk. apply H. exact (leq_trans Hk (leqnSn N)).
    + apply (H N.+1). apply leqnn.
Qed.

(* 尾部界（绝对值版）：Σ_{n=P+1}^{N} |n^{-s}| ≤ 1/P（P ≥ 1, s ≥ 2）
   —— iota (P+1) (N-P) 的元素 = S(P+k)（iota_succ_plus），
     逐项 zeta_tail_term_le：|(S(P+k))^{-s}| ≤ 1/(P+k) - 1/(S(P+k))，
     CRsum_list_iota 桥 + CRsum_le_pointwise 逐项 + telescope_unshift 求和 ≤ 1/P。 *)
Lemma zeta_tail_bound_list {R : ConstructiveReals} (s N P : nat)
  (Hs2 : (2 <= s)%N) (HP1 : (1 <= P)%N) :
  CRle R (CRsum_list (fun n => CRabs R (inv_n_pow n s)) (iota (P + 1) (N - P)))
         (CR_of_Q R (Qinv_n P)).
Proof.
  destruct (N - P) as [| m] eqn:Hm.
  - simpl. apply CRle_of_lt. apply CR_of_Q_inv_pos. exact HP1.
  - rewrite (iota_succ_plus P (S m)).
    rewrite -(addn1 m).
    rewrite (CRsum_list_map (R := R) (fun n => CRabs R (inv_n_pow n s))
                            (fun k => S (P + k)) (iota 0 (m + 1))).
    rewrite (CRsum_list_iota (R := R)
               (fun k => CRabs R (inv_n_pow (S (P + k)) s)) m).
    eapply CRle_trans.
    + apply (CRsum_le_pointwise (R := R)
               (fun k => CRabs R (inv_n_pow (S (P + k)) s))
               (fun k => CRminus R (CR_of_Q R (Qinv_n (P + k)))
                                   (CR_of_Q R (Qinv_n (S (P + k))))) m).
      move => k Hk.
      apply (zeta_tail_term_le (R := R) (P + k) s Hs2).
      exact (leq_trans HP1 (leq_addr k P)).
    + eapply CRle_trans.
      * apply (proj2 (telescope_unshift (R := R) P m)).
      * apply (CRle_minus_compat (R := R) (CR_of_Q R (Qinv_n P))
                                        (CR_of_Q R (Qinv_n (S (P + m))))).
        apply CRle_of_lt. apply CR_of_Q_inv_pos. exact (ltn0Sn (P + m)).
Qed.

(* 尾部界（无绝对值版）：Σ_{n=P+1}^{N} n^{-s} ≤ 1/P
   —— inv_n_pow n s ≥ 0（inv_n_pow_ge0）⟹ inv_n_pow == |inv_n_pow|（CRabs_right 反向），
     再套 zeta_tail_bound_list。 *)
Lemma zeta_tail_bound_list_noabs {R : ConstructiveReals} (s N P : nat)
  (Hs2 : (2 <= s)%N) (HP1 : (1 <= P)%N) :
  CRle R (CRsum_list (fun n => inv_n_pow n s) (iota (P + 1) (N - P)))
         (CR_of_Q R (Qinv_n P)).
Proof.
  apply (CRle_trans (R := R)
           (CRsum_list (fun n => inv_n_pow n s) (iota (P + 1) (N - P)))
           (CRsum_list (fun n => CRabs R (inv_n_pow n s)) (iota (P + 1) (N - P)))
           (CR_of_Q R (Qinv_n P))).
  - apply (proj2 (CRsum_eq_list (R := R)
                    (fun n => inv_n_pow n s)
                    (fun n => CRabs R (inv_n_pow n s))
                    (iota (P + 1) (N - P))
                    (fun n Hn => CReq_sym (CRabs R (inv_n_pow n s))
                                          (inv_n_pow n s)
                                          (CRabs_right (R := R) (inv_n_pow n s)
                                                       (inv_n_pow_ge0 (R := R) n s))))).
  - exact (zeta_tail_bound_list (R := R) s N P Hs2 HP1).
Qed.

(* ============================================================
   L4 P→∞：组合引理（Σ_{n=1}^{N} n^{-s} ≤ ∏(Σ_e) + 1/P）
   —— zeta_partial_le_euler_prod：反向主引理 + 尾部界 + 有限展开
   —— euler_product 主定理的上界侧核心（P→∞ 时尾部 → 0）
   ============================================================ *)

(* 组合引理：Σ_{n=1}^{N} n^{-s} ≤ ∏_{p∈primes_leq P}(Σ_{e≤E} p^{-es}) + 1/P
   —— P ≤ N ≤ 2^E、s ≥ 2、P ≥ 1
   —— 链：zeta_partial_le_euler_prod_tail（Σ ≤ Σ_smooth + 尾部）
     + zeta_tail_bound_list_noabs（尾部 ≤ 1/P）
     + euler_finite_expand 反向（Σ_smooth == ∏） *)
Lemma zeta_partial_le_euler_prod {R : ConstructiveReals} (s E N P : nat)
  (Hs2 : (2 <= s)%N) (HPN : (P <= N)%N) (HNE : (N <= 2 ^ E)%N) (HP1 : (1 <= P)%N) :
  CRle R (CRsum_list (fun n => inv_n_pow n s) (iota 1 N))
         (CRplus R
            (CRprod_list (fun p => CRsum (fun e => inv_n_pow (p ^ e) s) E)
                         (primes_leq P))
            (CR_of_Q R (Qinv_n P))).
Proof.
  apply (CRle_trans (R := R)
           (CRsum_list (fun n => inv_n_pow n s) (iota 1 N))
           (CRplus R
              (CRsum_list (fun n => inv_n_pow n s) (smooth_list E (primes_leq P)))
              (CRsum_list (fun n => inv_n_pow n s) (iota (P + 1) (N - P))))
           (CRplus R
              (CRprod_list (fun p => CRsum (fun e => inv_n_pow (p ^ e) s) E)
                           (primes_leq P))
              (CR_of_Q R (Qinv_n P)))).
  - exact (zeta_partial_le_euler_prod_tail (R := R) s E N P Hs2 HPN HNE).
  - apply (CRplus_le_compat (R := R)
             (CRsum_list (fun n => inv_n_pow n s) (smooth_list E (primes_leq P)))
             (CRprod_list (fun p => CRsum (fun e => inv_n_pow (p ^ e) s) E)
                          (primes_leq P))
             (CRsum_list (fun n => inv_n_pow n s) (iota (P + 1) (N - P)))
             (CR_of_Q R (Qinv_n P))).
    + apply (proj1 (euler_finite_expand (R := R) (primes_leq P) s E
                                         (primes_leq_all_prime P))).
    + exact (zeta_tail_bound_list_noabs (R := R) s N P Hs2 HP1).
Qed.

(* ============================================================
   L4 P→∞：主定理预备（2^n 无界 + 子列收敛）
   —— pow2_ge_one / pow2_ge_succ / pow2_unbounded / CRsum_subseq_pow2_cv
   —— euler_product 上界侧（ζ ≤ ∏_P(1-p^{-s})^{-1}）取极限需要
     ζ 部分和沿 2^E 子列收敛（CRsum_subseq_pow2_cv）。
   —— 本区段大量 nat 算术，临时打开 nat_scope。 *)
Local Open Scope nat_scope.

(* 1 ≤ 2^n（即 0 < 2^n；expn_gt0） *)
Lemma pow2_ge_one (n : nat) : (1 <= 2 ^ n)%N.
Proof.
  rewrite expn_gt0. apply/orP. left. apply ltnW. exact (ltn0Sn 1).
Qed.

(* 2^n ≥ n+1（归纳：n+1 ≤ 2^n；step 目标 S n + 1 ≤ 2^n·2，用 IH（addn1 桥）+ pow2_ge_one 加和） *)
Lemma pow2_ge_succ (n : nat) : (n + 1 <= 2 ^ n)%N.
Proof.
  elim: n => [|n IH]; simpl.
  - apply leqnn.
  - rewrite expnSr. (* 2^n.+1 = 2^n · 2 *)
    rewrite (addn1 n) in IH. (* IH : n+1 ≤ 2^n → S n ≤ 2^n *)
    apply (leq_trans (m := S n + 1) (n := 2 ^ n + 2 ^ n) (p := 2 ^ n * 2)).
    + apply (leq_add IH (pow2_ge_one n)).
    + rewrite addnn. rewrite muln2. apply leqnn.
Qed.

(* 2^E 无界：对任意 N，{E | N ≤ 2^E}（sig，Set 层供 CR_cv 用；取 E = N） *)
Lemma pow2_unbounded (N : nat) : {E : nat | (N <= 2 ^ E)%N}.
Proof.
  exists N.
  have Hsucc : (S N <= 2 ^ N)%N.
  { rewrite -[S N](addn1 N). exact (pow2_ge_succ N). } (* S N → N+1（addn1 反向） *)
  exact (leq_trans (leqnSn N) Hsucc).
Qed.

(* 部分和沿无界子列收敛：CR_cv (CRsum g) l ⟹ CR_cv (fun E => CRsum g (2^E)) l
   —— CR_cv 的 ε-N：给定 p，取 N0（Hcv 的 witness）；pow2_unbounded N0 给 E0 使 N0 ≤ 2^{E0}；
     对 E ≥ E0：2^E ≥ 2^{E0}（leq_exp2l）≥ N0 ⟹ |x_{2^E} - l| ≤ 1/p。 *)
Lemma CRsum_subseq_pow2_cv {R : ConstructiveReals} (g : nat -> CRcarrier R) (l : CRcarrier R)
  (Hcv : CR_cv R (CRsum g) l) :
  CR_cv R (fun E => CRsum g (2 ^ E)) l.
Proof.
  move => p.
  destruct (Hcv p) as [N0 HN0].
  destruct (pow2_unbounded N0) as [E0 HE0].
  exists E0.
  move => E HE.
  apply (HN0 (2 ^ E)).
  apply/leP.
  apply (leq_trans HE0).
  rewrite (@leq_exp2l 2 E0 E (ltnSn 1)). (* (2^{E0} ≤ 2^E) = (E0 ≤ E) *)
  move/leP: HE => HE'. exact HE'.
Qed.

(* ============================================================
   L4 P→∞：Step 1 —— zeta_le_euler_prod_P（euler_product 上界侧核心）
   —— 目标：1 + l ≤ ∏_{p∈primes_leq P}(1-p^{-s})^{-1} + 1/P（固定 P ≥ 1）
   —— 探针：zz_probe_euler_step1.v（EXIT=0，Print Assumptions Closed）
   —— 结构：E0 := pow2_unbounded P（P ≤ 2^{E0}）；沿 E 序列（索引 S E0 + E）：
       u E = Σ_{n=1}^{2^{S E0 + E}} n^{-s}（左端，经 iota1_sum_eq 桥 = 1 + 子列）
       v E = ∏_P(Σ_{e≤S E0+E} p^{-es}) + 1/P（右端）
      逐点 u ≤ v（zeta_partial_le_euler_prod，N = 2^{S E0+E} ≥ 2^{E0} ≥ P）；
      u → 1+l（子列 + shift + CR_cv_plus）；v → ∏ + 1/P（shift + CR_cv_plus）；
      CR_cv_le ⟹ 1+l ≤ ∏ + 1/P。
   ============================================================ *)

(* 收敛的右平移保持：CR_cv f l ⟹ CR_cv (fun n => f (n + k)) l
   —— ε-N：Hcv 的 N0 对 n + k ≥ N0 直接可用（n ≥ N0 ⟹ n + k ≥ N0）。 *)
Lemma CR_cv_shift_right {R : ConstructiveReals} (f : nat -> CRcarrier R) (k : nat) (l : CRcarrier R)
  (Hcv : CR_cv R f l) :
  CR_cv R (fun n => f (n + k)) l.
Proof.
  move => p.
  destruct (Hcv p) as [N0 HN0].
  exists N0.
  move => n Hn.
  apply (HN0 (n + k)).
  apply/leP.
  apply (leq_trans (introT leP Hn)).
  exact (leq_addr k n).
Qed.

(* 部分和沿 2^E - 2 子列收敛：CR_cv (CRsum g) l ⟹ CR_cv (fun E => CRsum g (2^E - 2)) l
   —— iota1_sum_eq 桥（B = 2^E 时尾项到 B-2）需要的子列形式。
   —— ε-N：Hcv 给 N0；pow2_unbounded (N0+2) 给 E' 使 N0+2 ≤ 2^{E'}；
      对 E ≥ E'：2^E ≥ 2^{E'} ≥ N0+2 ⟹ N0 ≤ 2^E - 2。 *)
Lemma CRsum_subseq_pow2_minus2_cv {R : ConstructiveReals} (g : nat -> CRcarrier R) (l : CRcarrier R)
  (Hcv : CR_cv R (CRsum g) l) :
  CR_cv R (fun E => CRsum g (2 ^ E - 2)) l.
Proof.
  move => p.
  destruct (Hcv p) as [N0 HN0].
  destruct (pow2_unbounded (N0 + 2)) as [E' HE'].
  exists E'.
  move => E HE.
  apply (HN0 (2 ^ E - 2)).
  apply/leP.
  (* N0 ≤ 2^E - 2 ⟸ N0 + 2 ≤ (2^E - 2) + 2 = 2^E（消去 +2） *)
  rewrite -(leq_add2r 2 N0 (2 ^ E - 2)).
  (* N0 + 2 ≤ (2^E - 2) + 2 = 2^E：需 2 ≤ 2^E（subnKC） *)
  have H2 : (2 <= 2 ^ E)%N.
  { rewrite (@leq_exp2l 2 1 E (ltnSn 1)).
    (* 1 ≤ E：E' ≤ E 且 1 ≤ E'（2 ≤ N0+2 ≤ 2^{E'} ⟹ 1 ≤ E'） *)
    have HE'1 : (1 <= E')%N.
    { rewrite -(@leq_exp2l 2 1 E' (ltnSn 1)).
      exact (leq_trans (leq_addl N0 2) HE'). }
    exact (leq_trans HE'1 (introT leP HE)).
  }
  rewrite (addnC (2 ^ E - 2) 2).
  rewrite (subnKC H2).
  (* N0 + 2 ≤ 2^E：N0+2 ≤ 2^{E'} ≤ 2^E *)
  apply (leq_trans HE').
  rewrite (@leq_exp2l 2 E' E (ltnSn 1)).
  move/leP: HE. exact id.
Qed.

(* 固定 P ≥ 1：1 + l ≤ ∏_{p∈primes_leq P}(1-p^{-s})^{-1} + 1/P
   —— l = projT1 (zeta_series_cv s Hs2)（ζ(s) = 1 + l）；
     右端 = projT1 (euler_E_cv (primes_leq P) ...)（∏_P(1-p^{-s})^{-1}）+ 1/P。
   —— euler_product 主定理上界侧的核心：P 固定时 ∏_P 已「封顶」为极限值，
     只剩 P→∞ 尾部 1/P → 0（Step 2）。 *)
Lemma zeta_le_euler_prod_P {R : ConstructiveReals} (s P : nat)
  (Hs2 : (2 <= s)%N) (HP1 : (1 <= P)%N) :
  CRle R (CRplus R (CR_of_Q R Q1q) (projT1 (zeta_series_cv (R := R) s Hs2)))
         (CRplus R
            (projT1 (euler_E_cv (primes_leq P) s (primes_leq_all_prime P)
                                (leq_trans (leqnSn 1) Hs2)))
            (CR_of_Q R (Qinv_n P))).
Proof.
  pose l := projT1 (zeta_series_cv (R := R) s Hs2).
  destruct (euler_E_cv (primes_leq P) s (primes_leq_all_prime P)
                       (leq_trans (leqnSn 1) Hs2)) as [lp Hlp].
  destruct (pow2_unbounded P) as [E0 HE0].
  pose u := fun E : nat => CRsum_list (R := R) (fun n => inv_n_pow (R := R) n s)
                                      (iota 1 (2 ^ (S E0 + E))).
  pose v := fun E : nat =>
             CRplus R
               (CRprod_list (R := R)
                            (fun p => CRsum (R := R) (fun e => inv_n_pow (R := R) (p ^ e) s)
                                            (S E0 + E))
                            (primes_leq P))
               (CR_of_Q R (Qinv_n P)).
  (* 逐点 u E ≤ v E（所有 E）：zeta_partial_le_euler_prod s (S E0+E) (2^{S E0+E}) P *)
  have Hpt : forall E, CRle R (u E) (v E).
  { move => E. unfold u, v.
    apply (zeta_partial_le_euler_prod (R := R) s (S E0 + E) (2 ^ (S E0 + E)) P Hs2).
    - (* P ≤ 2^{S E0 + E}：P ≤ 2^{E0} ≤ 2^{S E0+E} *)
      apply (leq_trans HE0).
      rewrite (@leq_exp2l 2 E0 (S E0 + E) (ltnSn 1)).
      (* 目标: E0 <= S E0 + E，addSn 展开 S 后 addnS 归一为 E0 + S E *)
      rewrite addSn. rewrite -addnS.
      exact (leq_addr (S E) E0).
    - (* 2^{S E0+E} ≤ 2^{S E0+E} *)
      apply leqnn.
    - exact HP1. }
  (* u → 1 + l（沿 E） *)
  have Hucv : CR_cv R u (CRplus R (CR_of_Q R Q1q) l).
  { apply (CR_cv_extens (R := R)
            (fun E : nat => CRplus R (CR_of_Q R Q1q)
                              (CRsum (fun k => inv_n_pow (S (S k)) s) (2 ^ (S E0 + E) - 2)))
            u (CRplus R (CR_of_Q R Q1q) l)).
    - (* 逐点 ==：iota1_sum_eq（B = 2^{S E0+E} ≥ 2） *)
      move => E. unfold u. symmetry.
      apply (iota1_sum_eq (R := R) s (2 ^ (S E0 + E))).
      (* 目标: 2 <= 2^{S E0 + E}（bool）；1 ≤ S E0 + E ⟹ 2^1 ≤ 2^{S E0+E} *)
      rewrite (@leq_exp2l 2 1 (S E0 + E) (ltnSn 1)).
      (* 1 ≤ S E0 + E = S (E0 + E) *)
      rewrite addSn. exact (ltn0Sn (E0 + E)).
    - (* 1 + 子列(2^{S E0+E} - 2) → 1 + l *)
      apply (CR_cv_plus (R := R) (fun _ : nat => CR_of_Q R Q1q)
              (fun E : nat => CRsum (fun k => inv_n_pow (S (S k)) s) (2 ^ (S E0 + E) - 2))
              (CR_of_Q R Q1q) l).
      + apply CR_cv_const.
      + (* 子列(2^{E} - 2) → l，然后右移 S E0（n + S E0 = S E0 + n 桥） *)
        apply (CR_cv_extens (R := R)
                (fun n : nat => CRsum (fun k => inv_n_pow (S (S k)) s) (2 ^ (n + S E0) - 2))
                (fun n : nat => CRsum (fun k => inv_n_pow (S (S k)) s) (2 ^ (S E0 + n) - 2)) l).
        * move => n. rewrite addnC. reflexivity.
        * apply (CR_cv_shift_right (R := R)
                   (fun E : nat => CRsum (fun k => inv_n_pow (S (S k)) s) (2 ^ E - 2)) (S E0) l).
          apply (CRsum_subseq_pow2_minus2_cv (R := R)
                   (fun k => inv_n_pow (S (S k)) s) l).
          exact (projT2 (zeta_series_cv (R := R) s Hs2)). }
  (* v → lp + 1/P（沿 E） *)
  have Hvcv : CR_cv R v (CRplus R lp (CR_of_Q R (Qinv_n P))).
  { unfold v.
    apply (CR_cv_plus (R := R)
            (fun E : nat => CRprod_list (R := R)
                                        (fun p => CRsum (R := R) (fun e => inv_n_pow (R := R) (p ^ e) s)
                                                        (S E0 + E))
                                        (primes_leq P))
            (fun _ : nat => CR_of_Q R (Qinv_n P)) lp (CR_of_Q R (Qinv_n P))).
    - (* ∏_P(Σ_e) 右移 S E0（n + S E0 = S E0 + n 桥） *)
      apply (CR_cv_extens (R := R)
              (fun n : nat => CRprod_list (R := R)
                                          (fun p => CRsum (R := R) (fun e => inv_n_pow (R := R) (p ^ e) s)
                                                          (n + S E0))
                                          (primes_leq P))
              (fun n : nat => CRprod_list (R := R)
                                          (fun p => CRsum (R := R) (fun e => inv_n_pow (R := R) (p ^ e) s)
                                                          (S E0 + n))
                                          (primes_leq P)) lp).
      + move => n. rewrite addnC. reflexivity.
      + apply (CR_cv_shift_right (R := R)
                 (fun E : nat => CRprod_list (R := R)
                                             (fun p => CRsum (R := R) (fun e => inv_n_pow (R := R) (p ^ e) s)
                                                             E)
                                             (primes_leq P))
                 (S E0) lp).
        exact Hlp.
    - apply CR_cv_const. }
  (* CR_cv_le ⟹ 1 + l ≤ lp + 1/P *)
  apply (CR_cv_le (R := R) u v (CRplus R (CR_of_Q R Q1q) l)
                   (CRplus R lp (CR_of_Q R (Qinv_n P))) Hpt Hucv Hvcv).
Qed.

(* ============================================================
   L4 P→∞：Step 2 —— euler_product 主定理（P→∞ 夹逼）
   —— 目标：CR_cv (fun P => ∏_{p∈primes_leq P}(1-p^{-s})^{-1}) (1 + l)
   —— 探针：zz_probe_euler_step2.v（EXIT=0，Print Assumptions Closed）
   —— 链：euler_prod_leq_zeta（F(P) ≤ 1+l，euler_prod_le_zeta + CR_cv_bound_up）
        + euler_prod_err_le（|F(P)-(1+l)| ≤ 1/P，夹逼误差界）
        + ε-N（P0 = Pos.to_nat p，1/P ≤ 1/p 当 P ≥ p）
   ============================================================ *)

(* F(P) ≤ 1 + l（逐 P 下界封顶）
   —— euler_prod_le_zeta（∏_P(Σ_e) ≤ 1+l 对任意 E）+ CR_cv_bound_up（E→∞ 极限）。 *)
Lemma euler_prod_leq_zeta {R : ConstructiveReals} (s P : nat)
  (Hs2 : (2 <= s)%N) (HP1 : (1 <= P)%N) :
  CRle R (projT1 (euler_E_cv (primes_leq P) s (primes_leq_all_prime P)
                              (leq_trans (leqnSn 1) Hs2)))
         (CRplus R (CR_of_Q R Q1q) (projT1 (zeta_series_cv (R := R) s Hs2))).
Proof.
  destruct (euler_E_cv (primes_leq P) s (primes_leq_all_prime P)
                       (leq_trans (leqnSn 1) Hs2)) as [lp Hlp].
  apply (CR_cv_bound_up (R := R)
           (fun E => CRprod_list (R := R)
                                 (fun p => CRsum (R := R) (fun e => inv_n_pow (R := R) (p ^ e) s) E)
                                 (primes_leq P))
           (CRplus R (CR_of_Q R Q1q) (projT1 (zeta_series_cv (R := R) s Hs2))) lp 0).
  - move => n Hn.
    apply (euler_prod_le_zeta (R := R) (primes_leq P) s n Hs2
                              (primes_leq_all_prime P) (primes_leq_uniq P)).
  - exact Hlp.
Qed.

(* |F(P) - (1+l)| ≤ 1/P（夹逼误差界）
   —— F(P) ≤ 1+l（euler_prod_leq_zeta）且 1+l ≤ F(P) + 1/P（zeta_le_euler_prod_P）：
     CRabs_minus_sym + CRabs_right（0 ≤ (1+l)-F(P)，CRle_minus）
     + CRplus_le_compat_r 加 (-F(P)) 消去（(1+l)-F(P) ≤ 1/P）。 *)
Lemma euler_prod_err_le {R : ConstructiveReals} (s P : nat)
  (Hs2 : (2 <= s)%N) (HP1 : (1 <= P)%N) :
  CRle R (CRabs R (CRminus R
                     (projT1 (euler_E_cv (primes_leq P) s (primes_leq_all_prime P)
                                         (leq_trans (leqnSn 1) Hs2)))
                     (CRplus R (CR_of_Q R Q1q) (projT1 (zeta_series_cv (R := R) s Hs2)))))
         (CR_of_Q R (Qinv_n P)).
Proof.
  pose F := projT1 (euler_E_cv (R := R) (primes_leq P) s (primes_leq_all_prime P)
                               (leq_trans (leqnSn 1) Hs2)).
  pose l := projT1 (zeta_series_cv (R := R) s Hs2).
  have H1 : CRle R F (CRplus R (CR_of_Q R Q1q) l) :=
    euler_prod_leq_zeta (R := R) s P Hs2 HP1.
  have H2 : CRle R (CRplus R (CR_of_Q R Q1q) l)
                   (CRplus R F (CR_of_Q R (Qinv_n P))) :=
    zeta_le_euler_prod_P (R := R) s P Hs2 HP1.
  (* 0 ≤ (1+l) - F：CRle_minus *)
  have H0le : CRle R (CR_of_Q R Q0q) (CRminus R (CRplus R (CR_of_Q R Q1q) l) F).
  { apply (CRle_minus F (CRplus R (CR_of_Q R Q1q) l)). exact H1. }
  (* |F - (1+l)| == (1+l) - F *)
  have Ha : CReq R (CRabs R (CRminus R F (CRplus R (CR_of_Q R Q1q) l)))
                   (CRminus R (CRplus R (CR_of_Q R Q1q) l) F).
  { eapply CReq_trans.
    - apply (CRabs_minus_sym F (CRplus R (CR_of_Q R Q1q) l)).
    - apply (CRabs_right (CRminus R (CRplus R (CR_of_Q R Q1q) l) F)).
      exact H0le. }
  apply (proj2 (CRle_morph R
                 (CRabs R (CRminus R F (CRplus R (CR_of_Q R Q1q) l)))
                 (CRminus R (CRplus R (CR_of_Q R Q1q) l) F) Ha
                 (CR_of_Q R (Qinv_n P)) (CR_of_Q R (Qinv_n P))
                 (CReq_refl (R := R) (CR_of_Q R (Qinv_n P))))).
  (* (1+l) - F ≤ 1/P：H2 加 (-F)，RHS 代数化简 *)
  have Hstep : CRle R (CRminus R (CRplus R (CR_of_Q R Q1q) l) F)
                      (CR_of_Q R (Qinv_n P)).
  { apply (CRle_trans (R := R)
             (CRminus R (CRplus R (CR_of_Q R Q1q) l) F)
             (CRplus R (CRplus R F (CR_of_Q R (Qinv_n P))) (CRopp R F))
             (CR_of_Q R (Qinv_n P))).
    - (* (1+l) - F ≤ (F + 1/P) + (-F)：CRplus_le_compat_r (-F) H2 *)
      unfold CRminus.
      apply (CRplus_le_compat_r (R := R) (CRopp R F)
                                (CRplus R (CR_of_Q R Q1q) l)
                                (CRplus R F (CR_of_Q R (Qinv_n P)))).
      exact H2.
    - (* (F + 1/P) + (-F) == 1/P：交换 + 结合 + 消去 *)
      have Hnorm : CReq R (CRplus R (CRplus R F (CR_of_Q R (Qinv_n P))) (CRopp R F))
                          (CR_of_Q R (Qinv_n P)).
      { rewrite (CRplus_comm (R := R) F (CR_of_Q R (Qinv_n P))).
        rewrite (CRplus_assoc (R := R) (CR_of_Q R (Qinv_n P)) F (CRopp R F)).
        rewrite (CRplus_opp_r (R := R) F).
        rewrite (CRplus_0_r (R := R) (CR_of_Q R (Qinv_n P))).
        reflexivity. }
      apply (proj2 (CRle_morph R
                     (CRplus R (CRplus R F (CR_of_Q R (Qinv_n P))) (CRopp R F))
                     (CR_of_Q R (Qinv_n P)) Hnorm
                     (CR_of_Q R (Qinv_n P)) (CR_of_Q R (Qinv_n P))
                     (CReq_refl (R := R) (CR_of_Q R (Qinv_n P))))).
      apply CRle_refl. }
  exact Hstep.
Qed.

(* 辅助：CR_of_Q (Qinv_n (Pos.to_nat p)) == CR_of_Q (Qmake 1 p)
   —— Qinv_n (Pos.to_nat p) = Qmake 1 (Z.to_pos (Z.of_nat (Pos.to_nat p)))
     = Qmake 1 p（Zto_pos_of_nat + Pos2Nat.id）。 *)
Lemma Qinv_n_pos_to_nat_bridge {R : ConstructiveReals} (p : positive) :
  CReq R (CR_of_Q R (Qinv_n (Pos.to_nat p))) (CR_of_Q R (Qmake 1 p)).
Proof.
  apply (CR_of_Q_Qeq (R := R) (Qinv_n (Pos.to_nat p)) (Qmake 1 p)).
  unfold Qinv_n, Qeq. simpl.
  (* 目标: 1 * Zpos p = 1 * Zpos (Z.to_pos (Z.of_nat (Pos.to_nat p)))
     ⟺ Zpos p = Zpos (Z.to_pos (Z.of_nat (Pos.to_nat p)))
     ⟺ p = Z.to_pos (Z.of_nat (Pos.to_nat p)) *)
  rewrite (Zto_pos_of_nat (Pos.to_nat p) (introT leP (Pos2Nat.is_pos p))).
  (* Z.to_pos (Z.of_nat (Pos.to_nat p)) = Pos.of_nat (Pos.to_nat p) = p *)
  rewrite (Pos2Nat.id p). reflexivity.
Qed.

(* ★★★ 主定理：ζ(s) = ∏_p (1-p^{-s})^{-1}（s ≥ 2，构造性实数，零公理）
   —— ε-N：取 P0 = Pos.to_nat p（1/P ≤ 1/p 当 P ≥ p）；
      |F(P) - (1+l)| ≤ 1/P ≤ 1/p（euler_prod_err_le + Qinv_n_le + Qeq 桥）。 *)
Theorem euler_product {R : ConstructiveReals} (s : nat) (Hs2 : (2 <= s)%N) :
  CR_cv R (fun P => projT1 (euler_E_cv (primes_leq P) s (primes_leq_all_prime P)
                                       (leq_trans (leqnSn 1) Hs2)))
          (CRplus R (CR_of_Q R Q1q) (projT1 (zeta_series_cv (R := R) s Hs2))).
Proof.
  move => p.
  exists (Pos.to_nat p).
  move => P HP.
  (* HP : (Pos.to_nat p <= P)%coq_nat；P ≥ 1 *)
  have HP1 : (1 <= P)%N.
  { apply (leq_trans (introT leP (Pos2Nat.is_pos p)) (introT leP HP)). }
  (* |F(P) - (1+l)| ≤ 1/P ≤ 1/p *)
  apply (CRle_trans (R := R)
           (CRabs R (CRminus R
                      (projT1 (euler_E_cv (primes_leq P) s (primes_leq_all_prime P)
                                          (leq_trans (leqnSn 1) Hs2)))
                      (CRplus R (CR_of_Q R Q1q) (projT1 (zeta_series_cv (R := R) s Hs2)))))
           (CR_of_Q R (Qinv_n P))
           (CR_of_Q R (Qmake 1 p))).
  - exact (euler_prod_err_le (R := R) s P Hs2 HP1).
  - (* 1/P ≤ 1/p：Qinv_n_le（P ≥ p）+ CR_of_Q_le + Qeq 桥 *)
    apply (proj2 (CRle_morph R
                   (CR_of_Q R (Qinv_n P)) (CR_of_Q R (Qinv_n P))
                   (CReq_refl (R := R) (CR_of_Q R (Qinv_n P)))
                   (CR_of_Q R (Qmake 1 p)) (CR_of_Q R (Qinv_n (Pos.to_nat p)))
                   (CReq_sym (CR_of_Q R (Qinv_n (Pos.to_nat p))) (CR_of_Q R (Qmake 1 p))
                             (Qinv_n_pos_to_nat_bridge (R := R) p)))).
    apply (CR_of_Q_le (R := R) (Qinv_n P) (Qinv_n (Pos.to_nat p))).
    apply (Qinv_n_le P (Pos.to_nat p)).
    + exact HP1.
    + exact (introT leP (Pos2Nat.is_pos p)).
    + move/leP: HP. exact id.
Qed.






