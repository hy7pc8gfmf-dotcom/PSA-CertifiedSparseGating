(* ============================================================
   库 ca_rip_cr —— 构造性 k-原子 RIP（受限等距性质）
   ============================================================
   目标：在构造性实数（Stdlib ConstructiveReals 抽象接口）上证明
         k-原子 RIP：对 M+1 个单位范数、两两相干 ≤ μ 的原子族，
         任意实系数 c_0..c_M 满足
           |‖Σ_{j≤M} c_j·u_j‖² − Σ_{j≤M} c_j²| ≤ μ·(M+1)·Σ_{j≤M} c_j²
         全部 Qed、零 Admitted、零自定义公理（仅依赖 Stdlib 构造性实数）。
   纪律：
     - 数学对象在 Set 层构造（CRcarrier R）
     - 序/极限在 Prop 层（CRle / CR_cv），不用排中律
     - 零经典实数公理（不 Require Stdlib.Reals 的 R 公理）
     - 只用抽象接口 {R : ConstructiveReals}
   结构：
     P0. CR 基础代数（平方非负、非正×非负 ≤ 0、绝对值平方恒等式）
     P1. 构造性复数 CRComplex
     P2. 范数平方 / 内积 / 线性组合 / 范数平方展开律
   ============================================================ *)
From Stdlib Require Import ConstructiveReals.
From Stdlib Require Import ConstructiveRealsMorphisms.
From Stdlib Require Import ConstructiveAbs.
From Stdlib Require Import ConstructiveSum.
From Stdlib Require Import QArith.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq div.

(* 合并版防御：显式恢复默认参数解析（与 ca_zeta_euler 相同） *)
Unset Implicit Arguments.

Local Open Scope ConstructiveReals.
(* 不打开 Q_scope —— Q 值全部通过 Qmake 辅助构造 *)

Section CRSqr.

Context {R : ConstructiveReals}.
Add Ring CR_ring : (CRisRing R).

(* ============================================================
   P0. CR 基础代数
   ============================================================ *)

(* 0 ≤ -a 从 a ≤ 0（加法平移） *)
Lemma CR0_le_opp (a : CRcarrier R) :
  CRle R a (CR_of_Q R (Qmake 0 1)) ->
  CRle R (CR_of_Q R (Qmake 0 1)) (CRopp R a).
Proof.
  intros Ha.
  apply (CRplus_le_reg_r (R:=R) a).
  rewrite CRplus_0_l. rewrite CRplus_opp_l.
  exact Ha.
Qed.

(* 非正 × 非负 ≤ 0（CRmult_le_0_compat 的推论） *)
Lemma CRmult_le0 (a b : CRcarrier R) :
  CRle R a (CR_of_Q R (Qmake 0 1)) ->
  CRle R (CR_of_Q R (Qmake 0 1)) b ->
  CRle R (CRmult R a b) (CR_of_Q R (Qmake 0 1)).
Proof.
  intros Ha Hb.
  (* 0 <= -a *)
  assert (Hna : CRle R (CR_of_Q R (Qmake 0 1)) (CRopp R a)).
  { exact (CR0_le_opp a Ha). }
  (* 0 <= (-a) * b == -(a*b)（CRopp_mult_distr_l） *)
  assert (Hprod : CRle R (CR_of_Q R (Qmake 0 1)) (CRmult R (CRopp R a) b)).
  { apply CRmult_le_0_compat; [exact Hna | exact Hb]. }
  (* 目标 a*b <= 0，即 ¬(0 < a*b)。反证。 *)
  unfold CRle.
  intro Habs.
  assert (Hneg : CRlt R (CRopp R (CRmult R a b)) (CR_of_Q R (Qmake 0 1))).
  { rewrite <- (CRopp_0 (R:=R)).
    apply (CRopp_gt_lt_contravar (R:=R) (CRmult R a b) (CR_of_Q R (Qmake 0 1))).
    exact Habs. }
  apply Hprod.
  rewrite <- (CRopp_mult_distr_l (R:=R) a b).
  exact Hneg.
Qed.

(* 0 < -a 从 a < 0（加法平移，严格版） *)
Lemma CR0_lt_opp (a : CRcarrier R) :
  CRlt R a (CR_of_Q R (Qmake 0 1)) ->
  CRlt R (CR_of_Q R (Qmake 0 1)) (CRopp R a).
Proof.
  intros Ha.
  apply (CRplus_lt_reg_r (R:=R) a).
  rewrite CRplus_0_l. rewrite CRplus_opp_l.
  exact Ha.
Qed.

(* 平方非负：0 ≤ x·x（A1 的 AM-GM 地基。
   反证 x·x < 0 ⟹ 0 < -(x·x) == x·(-x) ⟹ x ≶ 0 ⟹ 分情况矛盾。 *)
Lemma CRsqr_nonneg (x : CRcarrier R) :
  CRle R (CR_of_Q R (Qmake 0 1)) (CRmult R x x).
Proof.
  unfold CRle. intro H. (* H : x*x < 0 *)
  assert (Hpos : CRlt R (CR_of_Q R (Qmake 0 1)) (CRmult R x (CRopp R x))).
  { rewrite <- (CRopp_mult_distr_r (R:=R) x x). (* x*(-x) == -(x*x) 反向 *)
    apply (CRplus_lt_reg_r (R:=R) (CRmult R x x)).
    rewrite CRplus_0_l. rewrite CRplus_opp_l.
    exact H. }
  destruct (CRmult_pos_appart_zero (R:=R) x (CRopp R x) Hpos) as [Hxgt|Hxlt].
  - (* 0 < x ⟹ x·x > 0，矛盾 H *)
    assert (Hsq : CRlt R (CR_of_Q R (Qmake 0 1)) (CRmult R x x)).
    { apply (CRmult_lt_0_compat R x x Hxgt Hxgt). }
    exact (fst (fst (CRltLinear R)) (CR_of_Q R (Qmake 0 1)) (CRmult R x x) Hsq H).
  - (* x < 0 ⟹ -x > 0 ⟹ (-x)·(-x) == x·x > 0，矛盾 H *)
    assert (Hnx : CRlt R (CR_of_Q R (Qmake 0 1)) (CRopp R x)).
    { exact (CR0_lt_opp x Hxlt). }
    assert (Hsq : CRlt R (CR_of_Q R (Qmake 0 1)) (CRmult R (CRopp R x) (CRopp R x))).
    { apply (CRmult_lt_0_compat R (CRopp R x) (CRopp R x) Hnx Hnx). }
    assert (Hsq' : CRlt R (CR_of_Q R (Qmake 0 1)) (CRmult R x x)).
    { rewrite <- (CRopp_mult_distr_r (R:=R) (CRopp R x) x) in Hsq.
      rewrite (CRopp_mult_distr_l (R:=R) (CRopp R x) x) in Hsq.
      rewrite (CRopp_involutive (R:=R) x) in Hsq.
      exact Hsq. }
    exact (fst (fst (CRltLinear R)) (CR_of_Q R (Qmake 0 1)) (CRmult R x x) Hsq' H).
Qed.

(* x ≤ |x|（CRabs_def2 自反 proj1） *)
Lemma CRle_abs_self (x : CRcarrier R) :
  CRle R x (CRabs R x).
Proof.
  apply (proj1 (CRabs_def2 (R:=R) x (CRabs R x) (CRle_refl (R:=R) (CRabs R x)))).
Qed.

(* -|x| ≤ x（CRabs_def2 自反 proj2） *)
Lemma CRopp_abs_le_self (x : CRcarrier R) :
  CRle R (CRopp R (CRabs R x)) x.
Proof.
  apply (proj2 (CRabs_def2 (R:=R) x (CRabs R x) (CRle_refl (R:=R) (CRabs R x)))).
Qed.

(* x − |x| ≤ 0（由 x ≤ |x|） *)
Lemma CRminus_abs_le0 (x : CRcarrier R) :
  CRle R (CRminus R x (CRabs R x)) (CR_of_Q R (Qmake 0 1)).
Proof.
  (* 目标 x - |x| <= 0。加 |x| 两边：x <= |x|。 *)
  apply (CRplus_le_reg_r (R:=R) (CRabs R x)).
  unfold CRminus.
  ring_simplify.
  exact (CRle_abs_self x).
Qed.

(* 0 ≤ x + |x|（由 -|x| ≤ x） *)
Lemma CR0_le_plus_abs (x : CRcarrier R) :
  CRle R (CR_of_Q R (Qmake 0 1)) (CRplus R x (CRabs R x)).
Proof.
  (* -|x| <= x ⟹ (-|x|) + |x| <= x + |x|，左边 == 0。
     改写目标左端 0 == (-|x|) + |x|。 *)
  rewrite <- (CRplus_opp_l (R:=R) (CRabs R x)).
  apply (CRplus_le_compat_r (R:=R) (CRabs R x) (CRopp R (CRabs R x)) x).
  exact (CRopp_abs_le_self x).
Qed.

(* 0 < |x|·|x| ⟹ x ≶ 0（CRmult_pos_appart_zero + CRabs_appart_0 + |x|≥0） *)
Lemma CRabs_apart_0_of_sq_pos (x : CRcarrier R) :
  CRlt R (CR_of_Q R (Qmake 0 1)) (CRmult R (CRabs R x) (CRabs R x)) ->
  CRapart R x (CR_of_Q R (Qmake 0 1)).
Proof.
  intro H.
  pose (Hap := CRmult_pos_appart_zero (R:=R) (CRabs R x) (CRabs R x) H).
  destruct Hap as [Hpos|Hneg].
  - exact (CRabs_appart_0 (R:=R) x Hpos).
  - (* |x| < 0 矛盾 CRabs_pos : 0 <= |x| = ¬(|x| < 0) *)
    exfalso.
    exact (CRabs_pos (R:=R) x Hneg).
Qed.

(* 代数恒等式：(x-|x|)(x+|x|) == x²-|x|²（ring 战术） *)
Lemma CRsqr_minus_abs (x : CRcarrier R) :
  CReq R (CRmult R (CRminus R x (CRabs R x)) (CRplus R x (CRabs R x)))
         (CRminus R (CRmult R x x) (CRmult R (CRabs R x) (CRabs R x))).
Proof.
  unfold CRminus.
  ring.
Qed.

(* 绝对值平方恒等式：x² == |x|²（双向 ≤，AM-GM 的关键）
   方向1：x²-|x|² = (x-|x|)(x+|x|) ≤ 0（x-|x| ≤ 0、x+|x| ≥ 0，CRmult_le0）
   方向2：反证 x² < |x|² ⟹ 稠密 q：x² < q < |x|² ⟹ 0 < |x|² ⟹ x ≶ 0 ⟹ x=±|x| 矛盾 *)
Lemma CRabs_sqr (x : CRcarrier R) :
  CReq R (CRmult R x x) (CRmult R (CRabs R x) (CRabs R x)).
Proof.
  split.
  - (* 方向1：|x|*|x| <= x*x。反证 x*x < |x|*|x|。 *)
    unfold CRle. intro H.
    (* 稠密：x*x < |x|*|x| ⟹ ∃q : Q，x*x < q < |x|*|x| *)
    destruct (CR_Q_dense R (CRmult R x x) (CRmult R (CRabs R x) (CRabs R x)) H)
      as [q [Hxq Hqabs]].
    (* 0 <= x*x（CRsqr_nonneg）且 x*x < q ⟹ 0 < q *)
    assert (Hqpos : CRlt R (CR_of_Q R (Qmake 0 1)) (CR_of_Q R q)).
    { apply (CRle_lt_trans (R:=R) (CR_of_Q R (Qmake 0 1)) (CRmult R x x) (CR_of_Q R q)).
      - exact (CRsqr_nonneg x).
      - exact Hxq. }
    (* 0 < q < |x|*|x| ⟹ 0 < |x|*|x| *)
    assert (Hsqpos : CRlt R (CR_of_Q R (Qmake 0 1)) (CRmult R (CRabs R x) (CRabs R x))).
    { apply (CRlt_trans (R:=R) (CR_of_Q R (Qmake 0 1)) (CR_of_Q R q)
             (CRmult R (CRabs R x) (CRabs R x)) Hqpos Hqabs). }
    (* x ≶ 0 *)
    destruct (CRabs_apart_0_of_sq_pos x Hsqpos) as [Hxlt|Hxgt].
    + (* x < 0 ⟹ |x| == -x ⟹ |x|*|x| == x*x，矛盾 H *)
      assert (Hxle0 : CRle R x (CR_of_Q R (Qmake 0 1))).
      { apply CRlt_asym. exact Hxlt. }
      assert (Habs_eq : CReq R (CRmult R (CRabs R x) (CRabs R x))
                               (CRmult R x x)).
      { rewrite (CRabs_left (R:=R) x Hxle0). ring. }
      (* H : x*x < |x|*|x|，Habs_eq : |x|*|x| == x*x。
         矛盾：x*x < |x|*|x| <= x*x ⟹ x*x < x*x。 *)
      exact (fst (fst (CRltLinear R)) (CRmult R x x) (CRmult R x x)
        (CRlt_le_trans (R:=R) (CRmult R x x) (CRmult R (CRabs R x) (CRabs R x)) (CRmult R x x)
          H (proj2 Habs_eq))
        (CRlt_le_trans (R:=R) (CRmult R x x) (CRmult R (CRabs R x) (CRabs R x)) (CRmult R x x)
          H (proj2 Habs_eq))).
    + (* 0 < x ⟹ |x| == x ⟹ |x|*|x| == x*x，矛盾 H *)
      assert (Hxge0 : CRle R (CR_of_Q R (Qmake 0 1)) x).
      { apply CRlt_asym. exact Hxgt. }
      assert (Habs_eq : CReq R (CRmult R (CRabs R x) (CRabs R x))
                               (CRmult R x x)).
      { rewrite (CRabs_right (R:=R) x Hxge0). reflexivity. }
      exact (fst (fst (CRltLinear R)) (CRmult R x x) (CRmult R x x)
        (CRlt_le_trans (R:=R) (CRmult R x x) (CRmult R (CRabs R x) (CRabs R x)) (CRmult R x x)
          H (proj2 Habs_eq))
        (CRlt_le_trans (R:=R) (CRmult R x x) (CRmult R (CRabs R x) (CRabs R x)) (CRmult R x x)
          H (proj2 Habs_eq))).
  - (* 方向2：x*x <= |x|*|x|，即 ¬( |x|*|x| < x*x )。
     x²-|x|² == (x-|x|)(x+|x|) <= 0（CRmult_le0 + 两因子符号）。 *)
    assert (Hprod_le : CRle R (CRmult R (CRminus R x (CRabs R x))
                                    (CRplus R x (CRabs R x)))
                             (CR_of_Q R (Qmake 0 1))).
    { apply (CRmult_le0 (CRminus R x (CRabs R x)) (CRplus R x (CRabs R x))).
      - exact (CRminus_abs_le0 x).
      - exact (CR0_le_plus_abs x). }
    (* 目标 x*x <= |x|*|x|，即 |x|*|x| < x*x -> False。反证。 *)
    unfold CRle. intro Habs.
    (* 由 Habs : |x|*|x| < x*x，加 -( |x|*|x| ) 于左侧：-( |x|²)+|x|² < -( |x|²)+x²。
       左边 = 0，右边 = x²-|x|²。故 0 < x²-|x|² == (x-|x|)(x+|x|)。 *)
    assert (Hsqpos : CRlt R (CR_of_Q R (Qmake 0 1))
             (CRmult R (CRminus R x (CRabs R x)) (CRplus R x (CRabs R x)))).
    { rewrite (CRsqr_minus_abs x).
      rewrite <- (CRplus_opp_l (R:=R) (CRmult R (CRabs R x) (CRabs R x))).
      unfold CRminus.
      rewrite (CRplus_comm (R:=R) (CRmult R x x)
               (CRopp R (CRmult R (CRabs R x) (CRabs R x)))).
      apply (CRplus_lt_compat_l R (CRopp R (CRmult R (CRabs R x) (CRabs R x)))
               (CRmult R (CRabs R x) (CRabs R x)) (CRmult R x x)).
      exact Habs. }
    (* Hsqpos : 0 < (x-|x|)(x+|x|) 与 Hprod_le : (x-|x|)(x+|x|) <= 0 矛盾。 *)
    exact (Hprod_le Hsqpos).
Qed.

(* ============================================================
   P1. 构造性复数 CRComplex（借鉴 WBJ ComplexNumbers_Constructive
        的数学结构：re/im 分量 record + Cadd/Cmul/Cconj/Cnorm_sq，
        但零 Parameter —— 剔除 WBJ 的 Cnorm/Cexp/Cinv 未实现公设，
        也剔除 ConstructiveExtra 的临时公理）。
   ============================================================ *)

Record CRComplex : Set :=
  { cre : CRcarrier R; cim : CRcarrier R }.

(* 加法：分量加 *)
Definition CRadd (z w : CRComplex) : CRComplex :=
  {| cre := cre z + cre w; cim := cim z + cim w |}.

(* 乘法：(ac−bd) +i (ad+bc) *)
Definition CRmul (z w : CRComplex) : CRComplex :=
  {| cre := cre z * cre w - cim z * cim w;
     cim := cre z * cim w + cim z * cre w |}.

(* 共轭 *)
Definition CRconj (z : CRComplex) : CRComplex :=
  {| cre := cre z; cim := - cim z |}.

(* 范数平方：re² + im²（CR 上非负，P0 的 CRsqr_nonneg 保证） *)
Definition CRnorm_sq (z : CRComplex) : CRcarrier R :=
  cre z * cre z + cim z * cim z.

(* 零与一 *)
Definition CRzero : CRComplex :=
  {| cre := CR_of_Q R (Qmake 0 1); cim := CR_of_Q R (Qmake 0 1) |}.
Definition CRone : CRComplex :=
  {| cre := CR_of_Q R (Qmake 1 1); cim := CR_of_Q R (Qmake 0 1) |}.

(* 实内积：⟨z,w⟩ = re(z)·re(w) + im(z)·im(w)（RIP 用实内积） *)
Definition CRip (z w : CRComplex) : CRcarrier R :=
  cre z * cre w + cim z * cim w.

(* 复数相等（分量 CReq） *)
Definition CReq_cplx (z w : CRComplex) : Prop :=
  CReq R (cre z) (cre w) /\ CReq R (cim z) (cim w).

(* 范数平方非负：0 ≤ ‖z‖² *)
Lemma CRnorm_sq_nonneg (z : CRComplex) :
  CRle R (CR_of_Q R (Qmake 0 1)) (CRnorm_sq z).
Proof.
  unfold CRnorm_sq.
  rewrite <- (CRplus_0_l (R:=R) (CR_of_Q R (Qmake 0 1))).
  apply (CRplus_le_compat (R:=R)
           (CR_of_Q R (Qmake 0 1)) (cre z * cre z)
           (CR_of_Q R (Qmake 0 1)) (cim z * cim z)).
  - exact (CRsqr_nonneg (cre z)).
  - exact (CRsqr_nonneg (cim z)).
Qed.

(* 线性组合（递归）：comboM 0 = c_0·u_0；comboM (S M) = comboM M + c_{SM}·u_{SM}。
   返回"索引 M 的原子"（即组合前 M+1 项）。 *)
Fixpoint CRcombo (M : nat) (c : nat -> CRcarrier R) (u : nat -> CRComplex) : CRComplex :=
  match M with
  | O => {| cre := c 0%nat * cre (u 0%nat); cim := c 0%nat * cim (u 0%nat) |}
  | S M' =>
      {| cre := cre (CRcombo M' c u) + c (S M') * cre (u (S M'));
         cim := cim (CRcombo M' c u) + c (S M') * cim (u (S M')) |}
  end.

(* 组合的范数平方展开律（Pythagoras 型）：‖combo (S M)‖² == ‖combo M‖²
   + c_{SM}²·‖u_{SM}‖² + 2·c_{SM}·⟨combo M, u_{SM}⟩ *)
Lemma CRcombo_norm_sq_rec (M : nat) (c : nat -> CRcarrier R) (u : nat -> CRComplex) :
  CReq R (CRnorm_sq (CRcombo (S M) c u))
         (CRnorm_sq (CRcombo M c u)
          + c (S M) * c (S M) * CRnorm_sq (u (S M))
          + (1 + 1) * c (S M) * CRip (CRcombo M c u) (u (S M))).
Proof.
  unfold CRnorm_sq, CRip.
  cbn [CRcombo cre cim].
  ring.
Qed.

(* 单原子范数（M=0 基）：‖combo 0‖² == c_0²·‖u_0‖² *)
Lemma CRcombo_norm_sq_one (c : nat -> CRcarrier R) (u : nat -> CRComplex) :
  CReq R (CRnorm_sq (CRcombo 0 c u))
         (c 0%nat * c 0%nat * CRnorm_sq (u 0%nat)).
Proof.
  unfold CRnorm_sq.
  cbn [CRcombo cre cim].
  ring.
Qed.

(* 内积对组合的线性：⟨combo (S M), v⟩ == ⟨combo M, v⟩ + c_{SM}·⟨u_{SM}, v⟩ *)
Lemma CRcombo_ip_rec (M : nat) (c : nat -> CRcarrier R) (u : nat -> CRComplex) (v : CRComplex) :
  CReq R (CRip (CRcombo (S M) c u) v)
         (CRip (CRcombo M c u) v + c (S M) * CRip (u (S M)) v).
Proof.
  unfold CRip.
  cbn [CRcombo cre cim].
  ring.
Qed.

(* ============================================================
   P3. cross_abs_le / sum_abs_cross_le / sum_sq_nonneg（CR 版）
   ============================================================ *)

(* 平方和 ≥ 0（逐项 CRsqr_nonneg + cond_pos_sum） *)
Lemma CRsum_sq_nonneg (M : nat) (c : nat -> CRcarrier R) :
  CRle R (CR_of_Q R (Qmake 0 1)) (CRsum (fun j => c j * c j) M).
Proof.
  apply cond_pos_sum.
  intro k.
  exact (CRsqr_nonneg (c k)).
Qed.

(* AM-GM 单步：2·|a|·|c| ≤ a² + c²
   来自 (|a|−|c|)² ≥ 0（CRsqr_nonneg）展开，|a|² == a²（CRabs_sqr）。
   即 a²+c² == 2|a||c| + (|a|−|c|)²，且 (|a|−|c|)² ≥ 0（Rplus_le_pos）。 *)
Lemma CRabs_amgm (a c : CRcarrier R) :
  CRle R ((1 + 1) * (CRabs R a * CRabs R c))
         (a * a + c * c).
Proof.
  (* (|a|−|c|)² ≥ 0 *)
  assert (H0 : CRle R (CR_of_Q R (Qmake 0 1))
                   (CRmult R (CRminus R (CRabs R a) (CRabs R c))
                             (CRminus R (CRabs R a) (CRabs R c)))).
  { exact (CRsqr_nonneg (CRminus R (CRabs R a) (CRabs R c))). }
  (* 恒等式：a²+c² == 2|a||c| + (|a|−|c|)²。
     用 ring 展开 + CRabs_sqr 替换 |a|²==a²、|c|²==c²。 *)
  assert (Heq : CReq R (a * a + c * c)
         ((1 + 1) * (CRabs R a * CRabs R c)
          + CRmult R (CRminus R (CRabs R a) (CRabs R c))
                      (CRminus R (CRabs R a) (CRabs R c)))).
  { rewrite (CRabs_sqr a). rewrite (CRabs_sqr c).
    unfold CRminus.
    ring. }
  (* 目标 2|a||c| <= a²+c²。改写 a²+c² 为 2|a||c| + (|a|-|c|)²，
     由 Rplus_le_pos 从 0 <= (|a|-|c|)² 得 2|a||c| <= 2|a||c| + (...)。 *)
  rewrite Heq.
  apply (Rplus_le_pos (R:=R) ((1 + 1) * (CRabs R a * CRabs R c))
             (CRmult R (CRminus R (CRabs R a) (CRabs R c))
                       (CRminus R (CRabs R a) (CRabs R c)))).
  exact H0.
Qed.

(* AM-GM 求和：2·Σ_{j≤M} |a|·|c_j| ≤ (M+1)·a² + Σ_{j≤M} c_j²
   逐项 CRabs_amgm（2|a||c_j| ≤ a²+c_j²）求和：
   Σ_j 2|a||c_j| ≤ Σ_j (a²+c_j²) == (M+1)·a² + Σ_j c_j²。
   表述用 INR：RHS := a²·INR(S M) + Σc_j²（INR == CR_of_Q (Z.of_nat · #1)）。 *)
Lemma CRsum_abs_cross_le
  (M : nat) (a : CRcarrier R) (c : nat -> CRcarrier R) :
  CRle R ((1 + 1) * CRsum (fun j => CRabs R a * CRabs R (c j)) M)
         (a * a * INR (S M) + CRsum (fun j => c j * c j) M).
Proof.
  (* 逐项：2|a||c_j| <= a²+c_j²（CRabs_amgm）⟹ sum_Rle。 *)
  assert (Hsum : CRle R
           (CRsum (fun j => (1 + 1) * (CRabs R a * CRabs R (c j))) M)
           (CRsum (fun j => a * a + c j * c j) M)).
  { apply (sum_Rle (R:=R)
           (fun j => (1 + 1) * (CRabs R a * CRabs R (c j)))
           (fun j => a * a + c j * c j) M).
    intro k. intro Hk.
    exact (CRabs_amgm a (c k)). }
  (* LHS：2·Σ_j (|a||c_j|) == Σ_j (2·|a||c_j|)。
     sum_scale 给 Σ_j(u k·a) == Σu·a。目标 (1+1)·Σu == Σu·(1+1)（comm）== Σ_j(u k·(1+1))。
     而 Hsum 是 Σ_j((1+1)·u k)。逐项交换：(1+1)·u k == u k·(1+1)。 *)
  rewrite (CRmult_comm (R:=R) (1 + 1)
           (CRsum (fun j => CRabs R a * CRabs R (c j)) M)).
  rewrite <- (sum_scale (R:=R) (fun j => CRabs R a * CRabs R (c j)) (1 + 1) M).
  (* 目标 Σ_j (u k·(1+1)) <= ...。Hsum 是 Σ_j((1+1)·u k)。用 sum_Rle 的逐项交换
     或直接 eapply 到 Hsum 前先转换。用 CRsum_eq + CRmult_comm 逐项。
     注意：CRsum_eq 的前提显式传入（第 4 参），避免 rewrite 生成的子目标顺序
     在不同环境（本地 mathcomp<2.6 vs CI mathcomp≥2.6）下不一致（E114 变体）。 *)
  rewrite (CRsum_eq (R:=R)
    (fun j => CRabs R a * CRabs R (c j) * (1 + 1))
    (fun j => (1 + 1) * (CRabs R a * CRabs R (c j))) M
    (fun j Hj => symmetry (CRmult_comm (R:=R) (1 + 1) (CRabs R a * CRabs R (c j))))).
  rewrite (sum_plus (R:=R) (fun j => a * a) (fun j => c j * c j) M) in Hsum.
  rewrite (sum_const (R:=R) (a * a) M) in Hsum.
  exact Hsum.
Qed.

(* ============================================================
   P4. rip_lower_M / rip_upper_M / rip_bound_k（A1 主定理，CR 版）
   ============================================================ *)

(* 辅助：0 ≤ 1+1（CR 加法中的 2，不用 ring 记法 "2"） *)
Lemma CR0_le_two :
  CRle R (CR_of_Q R (Qmake 0 1)) ((1 + 1)).
Proof.
  assert (H1 : CRle R (CR_of_Q R (Qmake 0 1)) 1).
  { apply CRlt_asym. exact (CRzero_lt_one R). }
  rewrite <- (CRplus_0_l (R:=R) (CR_of_Q R (Qmake 0 1))).
  apply (CRplus_le_compat (R:=R)
    (CR_of_Q R (Qmake 0 1)) 1
    (CR_of_Q R (Qmake 0 1)) 1).
  - exact H1.
  - exact H1.
Qed.

(* 辅助：0 ≤ INR n（构造性整数非负，经 CR_of_Q_le + Nat2Z.is_nonneg） *)
Lemma CR0_le_INR (n : nat) :
  CRle R (CR_of_Q R (Qmake 0 1)) (INR n).
Proof.
  unfold INR.
  apply CR_of_Q_le.
  unfold Qle. cbn [Qnum Qden]. repeat rewrite Z.mul_1_r.
  apply Nat2Z.is_nonneg.
Qed.

(* 辅助：INR (S n) == INR n + 1（S_INR 的构造性版） *)
Lemma CR_INR_S (n : nat) :
  CReq R (INR (S n)) (INR n + 1).
Proof.
  unfold INR.
  rewrite <- (CR_of_Q_plus R (Z.of_nat n # 1) (1 # 1)).
  apply (CR_of_Q_morph R (Z.of_nat (S n) # 1) ((Z.of_nat n # 1) + (1 # 1))).
  unfold Qeq. cbn [Qnum Qden Qplus].
  repeat rewrite Z.mul_1_r.
  rewrite Z.add_1_r.
  apply Nat2Z.inj_succ.
Qed.

(* 辅助：INR 保序 *)
Lemma CRle_INR (m n : nat) : le m n -> CRle R (INR m) (INR n).
Proof.
  intros H. unfold INR.
  apply CR_of_Q_le.
  unfold Qle. cbn [Qnum Qden]. repeat rewrite Z.mul_1_r.
  apply Nat2Z.inj_le. exact H.
Qed.

(* 组装引理（替代经典版 nra 的 rip_final，全手动 CR 链）：
   Sv+A ≤ L + A + 2·IP + Y + mu·N1·Sv（Y 为交叉项绝对值上界）、
   Y ≤ mu·(N1·A+Sv)、N2 == N1+1、mu·N1·A ≤ mu·N2·A，
   则 Sv+A ≤ L + A + 2·IP + mu·N2·(Sv+A)。 *)
Lemma CRrip_final_cr (L A Sv IP Y mu N1 N2 : CRcarrier R) :
  (CRle R (CR_of_Q R (Qmake 0 1)) mu) ->
  (CRle R (Sv + A)
         (L + A + (1 + 1) * IP + Y + mu * N1 * Sv)) ->
  (CRle R Y (mu * (N1 * A + Sv))) ->
  (CReq R N2 (N1 + 1)) ->
  (CRle R (mu * N1 * A) (mu * N2 * A)) ->
  CRle R (Sv + A) (L + A + (1 + 1) * IP + mu * N2 * (Sv + A)).
Proof.
  intros Hmu0 H3 H2 HN2 HmA.
  (* 链：
     Sv+A ≤ M1 [H3]
          ≤ M2 [H2：Y ≤ mu(N1A+Sv)，公共前缀左加]
          == M3 [ring 分配]
          ≤ M4 [HmA + mu·Sv+mu·N1·Sv == mu·N2·Sv]
          == M5 [ring] *)
  apply (CRle_trans (R:=R) (Sv + A)
    (L + A + (1 + 1) * IP + Y + mu * N1 * Sv)
    (L + A + (1 + 1) * IP + mu * N2 * (Sv + A))).
  - exact H3.
  - apply (CRle_trans (R:=R)
      (L + A + (1 + 1) * IP + Y + mu * N1 * Sv)
      (L + A + (1 + 1) * IP + (mu * (N1 * A + Sv)) + mu * N1 * Sv)
      (L + A + (1 + 1) * IP + mu * N2 * (Sv + A))).
    + (* M1 ≤ M2：前缀 L+A+2IP+mu·N1·Sv，Y ≤ mu(N1A+Sv) *)
      assert (Hl : CReq R (L + A + (1 + 1) * IP + Y + mu * N1 * Sv)
                           (L + A + (1 + 1) * IP + mu * N1 * Sv + Y)).
      { ring. }
      rewrite Hl.
      assert (Hr : CReq R (L + A + (1 + 1) * IP + (mu * (N1 * A + Sv)) + mu * N1 * Sv)
                           (L + A + (1 + 1) * IP + mu * N1 * Sv + mu * (N1 * A + Sv))).
      { ring. }
      rewrite Hr.
      apply (CRplus_le_compat_l (R:=R) (L + A + (1 + 1) * IP + mu * N1 * Sv)).
      exact H2.
    + (* M2 → M5 *)
      apply (CRle_trans (R:=R)
        (L + A + (1 + 1) * IP + (mu * (N1 * A + Sv)) + mu * N1 * Sv)
        (L + A + (1 + 1) * IP + (mu * N1 * A + (mu * Sv + mu * N1 * Sv)))
        (L + A + (1 + 1) * IP + mu * N2 * (Sv + A))).
      * (* M2 == M3：分配 *)
        assert (Hd : CReq R
          (L + A + (1 + 1) * IP + (mu * (N1 * A + Sv)) + mu * N1 * Sv)
          (L + A + (1 + 1) * IP + (mu * N1 * A + (mu * Sv + mu * N1 * Sv)))).
        { ring. }
        rewrite Hd. apply CRle_refl.
      * (* M3 → M5：经 M4 == L+A+2IP+mu·N2·A+mu·N2·Sv *)
        apply (CRle_trans (R:=R)
          (L + A + (1 + 1) * IP + (mu * N1 * A + (mu * Sv + mu * N1 * Sv)))
          (L + A + (1 + 1) * IP + (mu * N2 * A + mu * N2 * Sv))
          (L + A + (1 + 1) * IP + mu * N2 * (Sv + A))).
        -- (* M3 ≤ M4 *)
           apply (CRplus_le_compat_l (R:=R) (L + A + (1 + 1) * IP)).
           apply (CRplus_le_compat (R:=R)
             (mu * N1 * A) (mu * N2 * A)
             (mu * Sv + mu * N1 * Sv) (mu * N2 * Sv)).
           ++ exact HmA.
           ++ assert (He : CReq R (mu * Sv + mu * N1 * Sv) (mu * N2 * Sv)).
              { assert (Hring : CReq R (mu * Sv + mu * N1 * Sv)
                                        (mu * ((N1 + 1) * Sv))).
                { ring. }
                rewrite Hring.
                rewrite <- HN2.
                ring. }
              apply (proj2 He).
        -- (* M4 == M5：ring（右结合 Sv+A） *)
           assert (Hf : CReq R
             (L + A + (1 + 1) * IP + (mu * N2 * A + mu * N2 * Sv))
             (L + A + (1 + 1) * IP + mu * N2 * (Sv + A))).
           { ring. }
           apply (proj2 Hf).
Qed.


(* 组合内积的绝对值上界（三角不等式归纳）：
   |⟨combo M c u, v⟩| ≤ Σ_{j≤M} |c_j|·|⟨u_j, v⟩| *)
Lemma CRcombo_ip_abs_le_sum
  (M : nat) (c : nat -> CRcarrier R) (u : nat -> CRComplex) (v : CRComplex) :
  CRle R (CRabs R (CRip (CRcombo M c u) v))
         (CRsum (fun j => CRabs R (c j) * CRabs R (CRip (u j) v)) M).
Proof.
  induction M as [| M IH].
  - (* M=0：CRip (combo 0) v == c_0·CRip(u_0,v)，|·| == |c_0|·|⟨u_0,v⟩|（CRabs_mult）。 *)
    cbn [CRcombo].
    unfold CRip.
    (* 目标：|A| <= |c_0|·|⟨u_0,v⟩|，其中 A == c_0·⟨u_0,v⟩。
       先证 A 的 CReq 等价，再 CRabs_morph + CRabs_mult。 *)
    assert (Heq : CReq R
      (cre {| cre := c 0%nat * cre (u 0%nat);
              cim := c 0%nat * cim (u 0%nat) |} * cre v
       + cim {| cre := c 0%nat * cre (u 0%nat);
                cim := c 0%nat * cim (u 0%nat) |} * cim v)
      (c 0%nat * (cre (u 0%nat) * cre v + cim (u 0%nat) * cim v))).
    { cbn [cre cim]. ring. }
    (* 目标：|A| <= |c_0|·|⟨u_0,v⟩|，A := cre{...}·cre v + cim{...}·cim v。
       Heq : A == c_0·⟨u_0,v⟩。CRabs_morph_prop ⟹ |A| == |c_0·⟨u_0,v⟩|。
       CRabs_mult ⟹ |c_0·⟨u_0,v⟩| == |c_0|·|⟨u_0,v⟩|。 *)
    apply (CRle_trans (R:=R)
      (CRabs R (cre {| cre := c 0%nat * cre (u 0%nat);
                       cim := c 0%nat * cim (u 0%nat) |} * cre v
                + cim {| cre := c 0%nat * cre (u 0%nat);
                         cim := c 0%nat * cim (u 0%nat) |} * cim v))
      (CRabs R (CRmult R (c 0%nat) (CRip (u 0%nat) v)))
      (CRmult R (CRabs R (c 0%nat)) (CRabs R (CRip (u 0%nat) v)))).
    - (* |A| <= |c_0·⟨u_0,v⟩|：Heq 经 CRabs_morph_prop 得 |A| == |B|，proj2 给 |A| <= |B| *)
      apply (proj2 (CRabs_morph_prop R
        (cre {| cre := c 0%nat * cre (u 0%nat);
                cim := c 0%nat * cim (u 0%nat) |} * cre v
         + cim {| cre := c 0%nat * cre (u 0%nat);
                  cim := c 0%nat * cim (u 0%nat) |} * cim v)
        (CRmult R (c 0%nat) (CRip (u 0%nat) v)) Heq)).
    - (* |c_0·⟨u_0,v⟩| <= |c_0||⟨u_0,v⟩|：CRabs_mult 的 proj2（|B| == |c_0||⟨u_0,v⟩|） *)
      apply (proj2 (CRabs_mult (R:=R) (c 0%nat) (CRip (u 0%nat) v))).
  - (* 归纳步：|⟨combo(SM),v⟩| = |⟨combo M,v⟩ + c_{SM}⟨u_{SM},v⟩|
       ≤ |⟨combo M,v⟩| + |c_{SM}||⟨u_{SM},v⟩|（三角 + CRabs_mult）
       ≤ Σ_{j≤M} + |c_{SM}||⟨u_{SM},v⟩| = Σ_{j≤SM}。 *)
    rewrite (CRcombo_ip_rec M c u v).
    apply (CRle_trans (R:=R)
      (CRabs R (CRplus R (CRip (CRcombo M c u) v)
                            (CRmult R (c (S M)) (CRip (u (S M)) v))))
      (CRplus R (CRabs R (CRip (CRcombo M c u) v))
                (CRabs R (CRmult R (c (S M)) (CRip (u (S M)) v))))
      (CRsum (fun j => CRabs R (c j) * CRabs R (CRip (u j) v)) (S M))).
    + exact (CRabs_triang (R:=R) (CRip (CRcombo M c u) v)
              (CRmult R (c (S M)) (CRip (u (S M)) v))).
    + rewrite (CRabs_mult (R:=R) (c (S M)) (CRip (u (S M)) v)).
      change (CRsum (fun j => CRabs R (c j) * CRabs R (CRip (u j) v)) (S M))
        with (CRsum (fun j => CRabs R (c j) * CRabs R (CRip (u j) v)) M
             + CRabs R (c (S M)) * CRabs R (CRip (u (S M)) v)).
      apply (CRplus_le_compat (R:=R)
        (CRabs R (CRip (CRcombo M c u) v))
        (CRsum (fun j => CRabs R (c j) * CRabs R (CRip (u j) v)) M)
        (CRabs R (c (S M)) * CRabs R (CRip (u (S M)) v))
        (CRabs R (c (S M)) * CRabs R (CRip (u (S M)) v))).
      * exact IH.
      * apply CRle_refl.
Qed.

(* 内积相干上界：若所有 |⟨u_j, v⟩| ≤ μ（j ≤ M），则
   |⟨combo M c u, v⟩| ≤ μ·Σ_{j≤M} |c_j| *)
Lemma CRcross_abs_le
  (M : nat) (c : nat -> CRcarrier R) (u : nat -> CRComplex)
  (v : CRComplex) (mu : CRcarrier R) :
  (CRle R (CR_of_Q R (Qmake 0 1)) mu) ->
  (forall j, le j M ->
    CRle R (CRabs R (CRip (u j) v)) mu) ->
  CRle R (CRabs R (CRip (CRcombo M c u) v))
         (mu * CRsum (fun j => CRabs R (c j)) M).
Proof.
  intros Hmu0 Hcoh.
  (* 由 CRcombo_ip_abs_le_sum：|⟨combo,v⟩| ≤ Σ|c_j||⟨u_j,v⟩|。
     逐项 |⟨u_j,v⟩| ≤ μ（Hcoh）⟹ |c_j|·|⟨u_j,v⟩| ≤ |c_j|·μ
     （CRmult_le_compat_l，r := |c_j| ≥ 0）。
     求和：Σ|c_j|·μ == (Σ|c_j|)·μ（sum_scale 的 proj2）
     再交换 == μ·Σ|c_j|（CRmult_comm 的 proj2）。 *)
  apply (CRle_trans (R:=R)
    (CRabs R (CRip (CRcombo M c u) v))
    (CRsum (fun j => CRabs R (c j) * CRabs R (CRip (u j) v)) M)
    (mu * CRsum (fun j => CRabs R (c j)) M)).
  - exact (CRcombo_ip_abs_le_sum M c u v).
  - (* Σ_j |c_j|·|⟨u_j,v⟩| ≤ μ·Σ_j |c_j|。 *)
    apply (CRle_trans (R:=R)
      (CRsum (fun j => CRabs R (c j) * CRabs R (CRip (u j) v)) M)
      (CRsum (fun j => CRabs R (c j) * mu) M)
      (mu * CRsum (fun j => CRabs R (c j)) M)).
    + (* 逐项 |c_k|·|⟨u_k,v⟩| ≤ |c_k|·μ（CRmult_le_compat_l） *)
      apply (sum_Rle (R:=R)
        (fun j => CRabs R (c j) * CRabs R (CRip (u j) v))
        (fun j => CRabs R (c j) * mu) M).
      intro k. intro Hk.
      apply (CRmult_le_compat_l (R:=R) (CRabs R (c k))
        (CRabs R (CRip (u k) v)) mu).
      * exact (CRabs_pos (R:=R) (c k)).
      * exact (Hcoh k Hk).
    + (* Σ_j |c_j|·μ ≤ μ·Σ_j |c_j|：sum_scale 后交换 *)
      apply (CRle_trans (R:=R)
        (CRsum (fun j => CRabs R (c j) * mu) M)
        (CRsum (fun j => CRabs R (c j)) M * mu)
        (mu * CRsum (fun j => CRabs R (c j)) M)).
      * (* Σ|c_j|·μ == (Σ|c_j|)·μ：sum_scale proj2 *)
        apply (proj2 (sum_scale (R:=R) (fun j => CRabs R (c j)) mu M)).
      * (* (Σ|c_j|)·μ == μ·(Σ|c_j|)：CRmult_comm proj2 *)
        apply (proj2 (CRmult_comm (R:=R)
          (CRsum (fun j => CRabs R (c j)) M) mu)).
Qed.

(* RIP 下界（归纳）：Σ_{j≤M} c_j² ≤ ‖combo M‖² + μ·(M+1)·Σ_{j≤M} c_j²
   （注：CRcombo M 组合 0..M 共 M+1 项，对应经典版 comboM (S M)；CRsum (c²) M 同取 0..M。 *)
Lemma CRrip_lower_M
  (M : nat) (c : nat -> CRcarrier R) (u : nat -> CRComplex) (mu : CRcarrier R) :
  (CRle R (CR_of_Q R (Qmake 0 1)) mu) ->
  (forall j, le j M -> CReq R (CRnorm_sq (u j)) (CR_of_Q R (Qmake 1 1))) ->
  (forall i j, le i M -> le j M -> i <> j ->
    CRle R (CRabs R (CRip (u i) (u j))) mu) ->
  CRle R (CRsum (fun j => c j * c j) M)
         (CRnorm_sq (CRcombo M c u)
          + mu * INR (S M) * CRsum (fun j => c j * c j) M).
Proof.
  intros Hmu0.
  induction M as [| M IH].
  - (* M=0：S_0 = c_0²，‖combo 0‖² == c_0²·‖u_0‖² == c_0²·1 == c_0²。 *)
    intros Hunit Hcoh.
    assert (Hu0 : CReq R (CRnorm_sq (u 0%nat)) (CR_of_Q R (Qmake 1 1)))
      by (apply Hunit; apply le_n).
    (* ‖combo 0‖² == c_0² *)
    assert (Heq1 : CReq R (CRnorm_sq (CRcombo 0 c u)) (c 0%nat * c 0%nat)).
    { eapply CReq_trans.
      - exact (CRcombo_norm_sq_one c u).
      - rewrite Hu0. ring. }
    (* 0 ≤ mu·INR 1·c_0² *)
    assert (Hm : CRle R (CR_of_Q R (Qmake 0 1))
                     (mu * INR (S 0) * (c 0%nat * c 0%nat))).
    { apply CRmult_le_0_compat.
      - apply CRmult_le_0_compat.
        + exact Hmu0.
        + exact (CR0_le_INR (S 0)).
      - exact (CRsqr_nonneg (c 0%nat)). }
    (* c_0² ≤ ‖combo 0‖² ≤ ‖combo 0‖² + mu·INR 1·c_0² *)
    apply (CRle_trans (R:=R)
      (c 0%nat * c 0%nat)
      (CRnorm_sq (CRcombo 0 c u))
      (CRnorm_sq (CRcombo 0 c u) + mu * INR (S 0) * (c 0%nat * c 0%nat))).
    + exact (proj1 Heq1).
    + apply (Rplus_le_pos (R:=R) (CRnorm_sq (CRcombo 0 c u))
             (mu * INR (S 0) * (c 0%nat * c 0%nat))).
      exact Hm.
  - (* 归纳步：S + A² ≤ ‖combo (S M)‖² + μ·(M+2)·(S + A²)。
       链条（镜像经典版）：
       S + A² ≤ L + A² + mu·INR(SM)·S            [HIH 加 A²]
             == L + A² + (1+1)(A·IP) + (−(1+1)(A·IP)) + mu·INR(SM)·S
             ≤ L + A² + (1+1)(A·IP) + Y + mu·INR(SM)·S   [Hneg：−(1+1)(A·IP) ≤ Y]
             ≤ L + A² + (1+1)(A·IP) + mu·(INR(SM)·A² + S) + mu·INR(SM)·S [H2']
             == L + A² + (1+1)(A·IP) + mu·INR(S(SM))·(S + A²)   [CRrip_final_cr]
       其中 L := ‖combo M‖²，A := c(SM)，IP := ⟨combo M, u(SM)⟩，S := Σ_{j≤M}c_j²，
       Y := 2|A||IP|。 *)
    intros Hunit Hcoh.
    set (L := CRnorm_sq (CRcombo M c u)).
    set (A := c (S M)).
    set (IP := CRip (CRcombo M c u) (u (S M))).
    set (Sv := CRsum (fun j => c j * c j) M).
    set (Sabs := CRsum (fun j => CRabs R (c j)) M).
    (* 单原子单位范数：‖u(SM)‖² == 1 *)
    assert (Hu' : CReq R (CRnorm_sq (u (S M))) (CR_of_Q R (Qmake 1 1)))
      by (apply Hunit; apply le_n).
    (* IH 截取到 M *)
    assert (HIH : CRle R Sv (L + mu * INR (S M) * Sv)).
    { apply IH.
      - intros j Hj. apply Hunit.
        exact (Nat.le_trans _ M (S M) Hj (Nat.le_succ_diag_r M)).
      - intros i j Hi Hj Hne. apply Hcoh.
        + exact (Nat.le_trans _ M (S M) Hi (Nat.le_succ_diag_r M)).
        + exact (Nat.le_trans _ M (S M) Hj (Nat.le_succ_diag_r M)).
        + exact Hne. }
    (* Lp == L + A² + (1+1)(A·IP)（norm_sq_rec + Hu'） *)
    assert (Hnorm : CReq R (CRnorm_sq (CRcombo (S M) c u))
                           (L + A * A + (1 + 1) * (A * IP))).
    { eapply CReq_trans.
      - exact (CRcombo_norm_sq_rec M c u).
      - rewrite Hu'. unfold L, A, IP. ring. }
    (* Hneg：−((1+1)(A·IP)) ≤ (1+1)|A||IP|（−x ≤ |x| == (1+1)|A||IP|） *)
    assert (Hneg : CRle R (CRopp R ((1 + 1) * (A * IP)))
                         ((1 + 1) * CRabs R A * CRabs R IP)).
    { apply (CRle_trans (R:=R) (CRopp R ((1 + 1) * (A * IP)))
                        (CRabs R ((1 + 1) * (A * IP)))
                        ((1 + 1) * CRabs R A * CRabs R IP)).
      - apply (CRle_trans (R:=R) (CRopp R ((1 + 1) * (A * IP)))
                          (CRabs R (CRopp R ((1 + 1) * (A * IP))))
                          (CRabs R ((1 + 1) * (A * IP)))).
        + exact (CRle_abs_self (CRopp R ((1 + 1) * (A * IP)))).
        + apply (proj2 (CRabs_opp (R:=R) ((1 + 1) * (A * IP)))).
      - (* |(1+1)(A·IP)| == (1+1)|A||IP|（CRabs_mult + |1+1|==1+1） *)
        rewrite (CRabs_mult (R:=R) (1 + 1) (A * IP)).
        rewrite (CRabs_right (R:=R) (1 + 1) (CR0_le_two)).
        rewrite (CRabs_mult (R:=R) A IP).
        assert (Hr : CReq R ((1 + 1) * (CRabs R A * CRabs R IP))
                             ((1 + 1) * CRabs R A * CRabs R IP)). { ring. }
        apply (proj2 Hr). }
    (* H1L：S + A² ≤ L + A² + (1+1)(A·IP) + Y + mu·INR(SM)·S *)
    assert (H1L : CRle R (Sv + A * A)
         (L + A * A + (1 + 1) * (A * IP)
          + (1 + 1) * CRabs R A * CRabs R IP + mu * INR (S M) * Sv)).
    { apply (CRle_trans (R:=R) (Sv + A * A)
        (L + A * A + mu * INR (S M) * Sv)
        (L + A * A + (1 + 1) * (A * IP)
         + (1 + 1) * CRabs R A * CRabs R IP + mu * INR (S M) * Sv)).
      - (* S + A² ≤ L + A² + mu·INR(SM)·S：由 HIH 加 A² *)
        apply (CRle_trans (R:=R) (Sv + A * A)
          (A * A + (L + mu * INR (S M) * Sv))
          (L + A * A + mu * INR (S M) * Sv)).
        + assert (Hc : CReq R (Sv + A * A) (A * A + Sv)). { ring. }
          rewrite Hc.
          apply (CRplus_le_compat_l (R:=R) (A * A)).
          exact HIH.
        + assert (Hc2 : CReq R (A * A + (L + mu * INR (S M) * Sv))
                                (L + A * A + mu * INR (S M) * Sv)). { ring. }
          apply (proj2 Hc2).
      - (* L + A² + mu·INR(SM)·S ≤ L + A² + (1+1)(A·IP) + Y + mu·INR(SM)·S *)
        apply (CRplus_le_compat_r (R:=R) (mu * INR (S M) * Sv)).
        (* 目标 L + A² ≤ (L + A² + (1+1)(A·IP)) + Y：
           L + A² == L + A² + (1+1)(A·IP) + (−(1+1)(A·IP))，且 −(1+1)(A·IP) ≤ Y *)
        assert (Hlinv : CReq R (L + A * A)
           (L + A * A + (1 + 1) * (A * IP) + CRopp R ((1 + 1) * (A * IP)))).
        { ring. }
        apply (CRle_trans (R:=R) (L + A * A)
          (L + A * A + (1 + 1) * (A * IP) + CRopp R ((1 + 1) * (A * IP)))
          (L + A * A + (1 + 1) * (A * IP) + (1 + 1) * CRabs R A * CRabs R IP)).
        + apply (proj2 Hlinv).
        + apply (CRplus_le_compat_l (R:=R)
            (L + A * A + (1 + 1) * (A * IP))).
          exact Hneg. }
    (* H2：Y ≤ (1+1)|A|·(mu·Sabs)（cross_abs_le 乘 (1+1)|A| ≥ 0） *)
    assert (H2 : CRle R ((1 + 1) * CRabs R A * CRabs R IP)
                        ((1 + 1) * CRabs R A * (mu * Sabs))).
    { apply (CRmult_le_compat_l (R:=R) ((1 + 1) * CRabs R A)
        (CRabs R IP) (mu * Sabs)).
      - apply CRmult_le_0_compat.
        + exact CR0_le_two.
        + apply CRabs_pos.
      - (* |IP| ≤ mu·Sabs：CRcross_abs_le（v := u(SM)，相干截取到 M） *)
        exact (CRcross_abs_le M c u (u (S M)) mu Hmu0
          (fun j Hj => Hcoh j (S M)
            (Nat.le_trans _ M (S M) Hj (Nat.le_succ_diag_r M))
            (le_n (S M))
            (Nat.lt_neq j (S M)
              (Nat.le_lt_trans j M (S M) Hj (Nat.lt_succ_diag_r M))))). }
    (* H3：(1+1)|A|·(mu·Sabs) ≤ mu·(INR(SM)·A² + S)（sum_abs_cross_le 乘 mu ≥ 0） *)
    assert (H3 : CRle R ((1 + 1) * CRabs R A * (mu * Sabs))
                        (mu * (INR (S M) * (A * A) + Sv))).
    { apply (CRle_trans (R:=R)
        ((1 + 1) * CRabs R A * (mu * Sabs))
        (mu * ((1 + 1) * CRsum (fun j => CRabs R A * CRabs R (c j)) M))
        (mu * (INR (S M) * (A * A) + Sv))).
      - (* LHS == mu·((1+1)·Σ_j |A||c_j|) *)
        (* (1+1)(|A|·Sabs) == (1+1)Σ_j(|A||c_j|) *)
        assert (HsumA : CReq R
          (CRsum (fun j => CRabs R A * CRabs R (c j)) M)
          (CRabs R A * Sabs)).
        { rewrite (CRsum_eq (R:=R)
            (fun j => CRabs R A * CRabs R (c j))
            (fun j => CRabs R (c j) * CRabs R A) M
            (fun j Hj => CRmult_comm (R:=R) (CRabs R A) (CRabs R (c j)))).
          rewrite (sum_scale (R:=R) (fun j => CRabs R (c j)) (CRabs R A) M).
          rewrite (CRmult_comm (R:=R) Sabs (CRabs R A)).
          reflexivity. }
        assert (Hscale : CReq R ((1 + 1) * (CRabs R A * Sabs))
                                 ((1 + 1) * CRsum (fun j => CRabs R A * CRabs R (c j)) M)).
        { rewrite HsumA. reflexivity. }
        (* 改写目标 RHS：mu·((1+1)Σ) == mu·((1+1)(|A|·Sabs)) *)
        rewrite <- Hscale.
        assert (Hm1 : CReq R ((1 + 1) * CRabs R A * (mu * Sabs))
                              (mu * ((1 + 1) * (CRabs R A * Sabs)))).
        { ring. }
        apply (proj2 Hm1).
      - apply (CRmult_le_compat_l (R:=R) mu
          ((1 + 1) * CRsum (fun j => CRabs R A * CRabs R (c j)) M)
          (INR (S M) * (A * A) + Sv)).
        + exact Hmu0.
        + (* (1+1)·Σ|A||c_j| ≤ A²·INR(SM) + Σc²（CRsum_abs_cross_le），再变形 RHS *)
          assert (Hr : CReq R (A * A * INR (S M) + CRsum (fun j => c j * c j) M)
                               (INR (S M) * (A * A) + Sv)).
          { unfold Sv. ring. }
          rewrite <- Hr.
          exact (CRsum_abs_cross_le M A c). }
    (* H2'：Y ≤ mu·(INR(SM)·A² + S)（H2 + H3 合成） *)
    assert (H2' : CRle R ((1 + 1) * CRabs R A * CRabs R IP)
                         (mu * (INR (S M) * (A * A) + Sv))).
    { apply (CRle_trans (R:=R)
        ((1 + 1) * CRabs R A * CRabs R IP)
        ((1 + 1) * CRabs R A * (mu * Sabs))
        (mu * (INR (S M) * (A * A) + Sv))).
      - exact H2.
      - exact H3. }
    (* HmA：mu·INR(SM)·A² ≤ mu·INR(S(SM))·A² *)
    assert (HmA : CRle R (mu * INR (S M) * (A * A))
                         (mu * INR (S (S M)) * (A * A))).
    { apply (CRmult_le_compat_r (R:=R) (A * A)
        (mu * INR (S M)) (mu * INR (S (S M)))).
      - exact (CRsqr_nonneg A).
      - apply (CRmult_le_compat_l (R:=R) mu
          (INR (S M)) (INR (S (S M)))).
        + exact Hmu0.
        + apply (CRle_INR (S M) (S (S M))). lia. }
    (* 组装：CRrip_final_cr *)
    assert (Hfin : CRle R (Sv + A * A)
         (L + A * A + (1 + 1) * (A * IP) + mu * INR (S (S M)) * (Sv + A * A))).
    { apply (CRrip_final_cr L (A * A) Sv (A * IP)
             ((1 + 1) * CRabs R A * CRabs R IP) mu
             (INR (S M)) (INR (S (S M)))).
      - exact Hmu0.
      - exact H1L.
      - exact H2'.
      - exact (CR_INR_S (S M)).
      - exact HmA. }
    (* 收尾：目标 LHS == S+A²，目标 RHS == Hfin 的 RHS（Hnorm） *)
    change (CRsum (fun j => c j * c j) (S M)) with (Sv + A * A).
    change (mu * INR (S (S M)) * CRsum (fun j => c j * c j) (S M))
      with (mu * INR (S (S M)) * (Sv + A * A)).
    apply (CRle_trans (R:=R) (Sv + A * A)
      (L + A * A + (1 + 1) * (A * IP) + mu * INR (S (S M)) * (Sv + A * A))
      (CRnorm_sq (CRcombo (S M) c u) + mu * INR (S (S M)) * (Sv + A * A))).
    - exact Hfin.
    - (* Hfin RHS ≤ 目标 RHS：‖combo(SM)‖² == L + A² + (1+1)(A·IP)（Hnorm proj1） *)
      rewrite (CRplus_comm (R:=R) (L + A * A + (1 + 1) * (A * IP))
                           (mu * INR (S (S M)) * (Sv + A * A))).
      rewrite (CRplus_comm (R:=R) (CRnorm_sq (CRcombo (S M) c u))
                           (mu * INR (S (S M)) * (Sv + A * A))).
      apply (CRplus_le_compat_l (R:=R) (mu * INR (S (S M)) * (Sv + A * A))).
      apply (proj1 Hnorm).
Qed.

(* ============================================================
   RIP 上界与 A1 主定理（bound_k）
   ============================================================ *)

(* 组装引理（RIP 上界，镜像 rip_final 但无负数项）：
   X ≤ L + A + 2·IP（norm_sq_rec 展开）、2·IP ≤ Y ≤ mu·(N1·A+Sv)、
   L ≤ Sv + mu·N1·Sv（IH）、mu·N1·A ≤ mu·N2·A、N2 == N1+1，
   则 X ≤ Sv + A + mu·N2·(Sv+A)。 *)
Lemma CRrip_upper_final_cr (L A Sv IP Y mu N1 N2 X : CRcarrier R) :
  (CRle R X (L + A + (1 + 1) * IP)) ->
  (CRle R ((1 + 1) * IP) Y) ->
  (CRle R Y (mu * (N1 * A + Sv))) ->
  (CRle R L (Sv + mu * N1 * Sv)) ->
  (CRle R (mu * N1 * A) (mu * N2 * A)) ->
  (CReq R N2 (N1 + 1)) ->
  CRle R X (Sv + A + mu * N2 * (Sv + A)).
Proof.
  intros Hx Hip HY HIH HmA HN2.
  (* 链：
     X ≤ L + A + 2IP            [Hx]
       ≤ L + A + Y              [Hip 加前缀 L+A]
       ≤ L + A + mu(N1A+Sv)     [HY 加前缀 L+A]
       ≤ (Sv+muN1Sv) + A + mu(N1A+Sv)   [HIH 加 A+mu(N1A+Sv)]
        == Sv + A + muN1Sv + muN1A + muSv   [ring]
       ≤ Sv + A + muN2Sv + muN2A            [muN1Sv+muSv==muN2Sv；muN1A≤muN2A]
        == Sv + A + muN2(Sv+A)              [ring] *)
  apply (CRle_trans (R:=R) X (L + A + (1 + 1) * IP) (Sv + A + mu * N2 * (Sv + A))).
  - exact Hx.
  - apply (CRle_trans (R:=R)
      (L + A + (1 + 1) * IP)
      (L + A + Y)
      (Sv + A + mu * N2 * (Sv + A))).
    + apply (CRplus_le_compat_l (R:=R) (L + A)).
      exact Hip.
    + apply (CRle_trans (R:=R)
        (L + A + Y)
        (L + A + mu * (N1 * A + Sv))
        (Sv + A + mu * N2 * (Sv + A))).
      * apply (CRplus_le_compat_l (R:=R) (L + A)).
        exact HY.
      * apply (CRle_trans (R:=R)
          (L + A + mu * (N1 * A + Sv))
          ((Sv + mu * N1 * Sv) + A + mu * (N1 * A + Sv))
          (Sv + A + mu * N2 * (Sv + A))).
        -- (* L + A + mu(N1A+Sv) ≤ (Sv+muN1Sv) + A + mu(N1A+Sv)：HIH 加 A+mu(N1A+Sv) *)
           assert (Hb : CReq R (L + A + mu * (N1 * A + Sv))
                                (L + (A + mu * (N1 * A + Sv)))). { ring. }
           rewrite Hb.
           assert (Hb2 : CReq R ((Sv + mu * N1 * Sv) + A + mu * (N1 * A + Sv))
                                ((Sv + mu * N1 * Sv) + (A + mu * (N1 * A + Sv)))). { ring. }
           rewrite Hb2.
           apply (CRplus_le_compat_r (R:=R) (A + mu * (N1 * A + Sv))).
           exact HIH.
        -- (* (Sv+muN1Sv)+A+mu(N1A+Sv) ≤ Sv + A + muN2(Sv+A) *)
           apply (CRle_trans (R:=R)
             ((Sv + mu * N1 * Sv) + A + mu * (N1 * A + Sv))
             (Sv + A + mu * N1 * Sv + mu * N1 * A + mu * Sv)
             (Sv + A + mu * N2 * (Sv + A))).
           ++ (* == ring 展开 *)
              assert (Hr1 : CReq R ((Sv + mu * N1 * Sv) + A + mu * (N1 * A + Sv))
                                   (Sv + A + mu * N1 * Sv + mu * N1 * A + mu * Sv)). { ring. }
              rewrite Hr1. apply CRle_refl.
           ++ (* ≤ 目标 *)
              assert (Hg1 : CReq R (Sv + A + mu * N1 * Sv + mu * N1 * A + mu * Sv)
                                   (Sv + A + ((mu * N1 * Sv + mu * Sv) + mu * N1 * A))). { ring. }
              rewrite Hg1.
              assert (Hg2 : CReq R (Sv + A + mu * N2 * (Sv + A))
                                   (Sv + A + (mu * N2 * Sv + mu * N2 * A))). { ring. }
              rewrite Hg2.
              apply (CRplus_le_compat_l (R:=R) (Sv + A)).
              apply (CRplus_le_compat (R:=R)
                (mu * N1 * Sv + mu * Sv) (mu * N2 * Sv)
                (mu * N1 * A) (mu * N2 * A)).
              -- assert (He : CReq R (mu * N1 * Sv + mu * Sv) (mu * N2 * Sv)).
                 { assert (Hring : CReq R (mu * N1 * Sv + mu * Sv) (mu * ((N1 + 1) * Sv))). { ring. }
                   rewrite Hring. rewrite <- HN2. ring. }
                 apply (proj2 He).
              -- exact HmA.
Qed.

(* RIP 上界（归纳）：‖combo M‖² ≤ Σ_{j≤M} c_j² + μ·(M+1)·Σ_{j≤M} c_j² *)
Lemma CRrip_upper_M
  (M : nat) (c : nat -> CRcarrier R) (u : nat -> CRComplex) (mu : CRcarrier R) :
  (CRle R (CR_of_Q R (Qmake 0 1)) mu) ->
  (forall j, le j M -> CReq R (CRnorm_sq (u j)) (CR_of_Q R (Qmake 1 1))) ->
  (forall i j, le i M -> le j M -> i <> j ->
    CRle R (CRabs R (CRip (u i) (u j))) mu) ->
  CRle R (CRnorm_sq (CRcombo M c u))
         (CRsum (fun j => c j * c j) M
          + mu * INR (S M) * CRsum (fun j => c j * c j) M).
Proof.
  intros Hmu0.
  induction M as [| M IH].
  - (* M=0：‖combo 0‖² == c_0²·1 == c_0² ≤ c_0² + mu·INR 1·c_0² *)
    intros Hunit Hcoh.
    assert (Hu0 : CReq R (CRnorm_sq (u 0%nat)) (CR_of_Q R (Qmake 1 1)))
      by (apply Hunit; apply le_n).
    assert (Heq1 : CReq R (CRnorm_sq (CRcombo 0 c u)) (c 0%nat * c 0%nat)).
    { eapply CReq_trans.
      - exact (CRcombo_norm_sq_one c u).
      - rewrite Hu0. ring. }
    assert (Hm : CRle R (CR_of_Q R (Qmake 0 1))
                     (mu * INR (S 0) * (c 0%nat * c 0%nat))).
    { apply CRmult_le_0_compat.
      - apply CRmult_le_0_compat.
        + exact Hmu0.
        + exact (CR0_le_INR (S 0)).
      - exact (CRsqr_nonneg (c 0%nat)). }
    apply (CRle_trans (R:=R)
      (CRnorm_sq (CRcombo 0 c u))
      (c 0%nat * c 0%nat)
      (c 0%nat * c 0%nat + mu * INR (S 0) * (c 0%nat * c 0%nat))).
    + exact (proj2 Heq1).
    + apply (Rplus_le_pos (R:=R) (c 0%nat * c 0%nat)
             (mu * INR (S 0) * (c 0%nat * c 0%nat))).
      exact Hm.
  - (* 归纳步：X ≤ Sv + A² + mu·INR(S(SM))·(Sv+A²)。
       链条：X == L + A² + 2(A·IP)（norm_sq_rec）
             ≤ L + A² + 2|A||IP|        [2(A·IP) ≤ 2|A||IP|]
             ≤ L + A² + mu(INR(SM)·A² + Sv)  [cross_abs_le + sum_abs_cross_le]
             ≤ (Sv+mu·INR(SM)·Sv) + A² + mu(INR(SM)·A²+Sv)  [IH]
              == Sv + A² + mu·INR(S(SM))·(Sv+A²)  [CRrip_upper_final_cr] *)
    intros Hunit Hcoh.
    set (L := CRnorm_sq (CRcombo M c u)).
    set (A := c (S M)).
    set (IP := CRip (CRcombo M c u) (u (S M))).
    set (Sv := CRsum (fun j => c j * c j) M).
    set (Sabs := CRsum (fun j => CRabs R (c j)) M).
    assert (Hu' : CReq R (CRnorm_sq (u (S M))) (CR_of_Q R (Qmake 1 1)))
      by (apply Hunit; apply le_n).
    (* IH 截取到 M *)
    assert (HIH : CRle R L (Sv + mu * INR (S M) * Sv)).
    { apply IH.
      - intros j Hj. apply Hunit.
        exact (Nat.le_trans _ M (S M) Hj (Nat.le_succ_diag_r M)).
      - intros i j Hi Hj Hne. apply Hcoh.
        + exact (Nat.le_trans _ M (S M) Hi (Nat.le_succ_diag_r M)).
        + exact (Nat.le_trans _ M (S M) Hj (Nat.le_succ_diag_r M)).
        + exact Hne. }
    (* X == L + A² + 2(A·IP)（norm_sq_rec + Hu'） *)
    assert (Hnorm : CReq R (CRnorm_sq (CRcombo (S M) c u))
                           (L + A * A + (1 + 1) * (A * IP))).
    { eapply CReq_trans.
      - exact (CRcombo_norm_sq_rec M c u).
      - rewrite Hu'. unfold L, A, IP. ring. }
    (* Hip：2(A·IP) ≤ 2|A||IP|（A·IP ≤ |A·IP| == |A||IP|，乘 2 ≥ 0） *)
    assert (Hip : CRle R ((1 + 1) * (A * IP))
                         ((1 + 1) * CRabs R A * CRabs R IP)).
    { assert (Hr : CReq R ((1 + 1) * (CRabs R A * CRabs R IP))
                          ((1 + 1) * CRabs R A * CRabs R IP)). { ring. }
      rewrite <- Hr.
      apply (CRmult_le_compat_l (R:=R) (1 + 1)
        (A * IP) (CRabs R A * CRabs R IP)).
      - exact CR0_le_two.
      - apply (CRle_trans (R:=R) (A * IP)
          (CRabs R (A * IP)) (CRabs R A * CRabs R IP)).
        + exact (CRle_abs_self (A * IP)).
        + apply (proj2 (CRabs_mult (R:=R) A IP)). }
    (* H2：Y := 2|A||IP| ≤ 2|A|·(mu·Sabs)（cross_abs_le 乘 2|A| ≥ 0） *)
    assert (H2 : CRle R ((1 + 1) * CRabs R A * CRabs R IP)
                        ((1 + 1) * CRabs R A * (mu * Sabs))).
    { apply (CRmult_le_compat_l (R:=R) ((1 + 1) * CRabs R A)
        (CRabs R IP) (mu * Sabs)).
      - apply CRmult_le_0_compat.
        + exact CR0_le_two.
        + apply CRabs_pos.
      - exact (CRcross_abs_le M c u (u (S M)) mu Hmu0
          (fun j Hj => Hcoh j (S M)
            (Nat.le_trans _ M (S M) Hj (Nat.le_succ_diag_r M))
            (le_n (S M))
            (Nat.lt_neq j (S M)
              (Nat.le_lt_trans j M (S M) Hj (Nat.lt_succ_diag_r M))))). }
    (* H3：2|A|·(mu·Sabs) ≤ mu·(INR(SM)·A² + Sv)（sum_abs_cross_le 乘 mu ≥ 0） *)
    assert (H3 : CRle R ((1 + 1) * CRabs R A * (mu * Sabs))
                        (mu * (INR (S M) * (A * A) + Sv))).
    { apply (CRle_trans (R:=R)
        ((1 + 1) * CRabs R A * (mu * Sabs))
        (mu * ((1 + 1) * CRsum (fun j => CRabs R A * CRabs R (c j)) M))
        (mu * (INR (S M) * (A * A) + Sv))).
      - (* LHS == mu·((1+1)·Σ_j |A||c_j|) *)
        assert (HsumA : CReq R
          (CRsum (fun j => CRabs R A * CRabs R (c j)) M)
          (CRabs R A * Sabs)).
        { rewrite (CRsum_eq (R:=R)
            (fun j => CRabs R A * CRabs R (c j))
            (fun j => CRabs R (c j) * CRabs R A) M
            (fun j Hj => CRmult_comm (R:=R) (CRabs R A) (CRabs R (c j)))).
          rewrite (sum_scale (R:=R) (fun j => CRabs R (c j)) (CRabs R A) M).
          rewrite (CRmult_comm (R:=R) Sabs (CRabs R A)).
          reflexivity. }
        assert (Hscale : CReq R ((1 + 1) * (CRabs R A * Sabs))
                                 ((1 + 1) * CRsum (fun j => CRabs R A * CRabs R (c j)) M)).
        { rewrite HsumA. reflexivity. }
        rewrite <- Hscale.
        assert (Hm1 : CReq R ((1 + 1) * CRabs R A * (mu * Sabs))
                              (mu * ((1 + 1) * (CRabs R A * Sabs)))).
        { ring. }
        apply (proj2 Hm1).
      - apply (CRmult_le_compat_l (R:=R) mu
          ((1 + 1) * CRsum (fun j => CRabs R A * CRabs R (c j)) M)
          (INR (S M) * (A * A) + Sv)).
        + exact Hmu0.
        + assert (Hr : CReq R (A * A * INR (S M) + CRsum (fun j => c j * c j) M)
                               (INR (S M) * (A * A) + Sv)).
          { unfold Sv. ring. }
          rewrite <- Hr.
          exact (CRsum_abs_cross_le M A c). }
    (* H2'：Y ≤ mu·(INR(SM)·A² + Sv) *)
    assert (H2' : CRle R ((1 + 1) * CRabs R A * CRabs R IP)
                         (mu * (INR (S M) * (A * A) + Sv))).
    { apply (CRle_trans (R:=R)
        ((1 + 1) * CRabs R A * CRabs R IP)
        ((1 + 1) * CRabs R A * (mu * Sabs))
        (mu * (INR (S M) * (A * A) + Sv))).
      - exact H2.
      - exact H3. }
    (* HmA：mu·INR(SM)·A² ≤ mu·INR(S(SM))·A² *)
    assert (HmA : CRle R (mu * INR (S M) * (A * A))
                         (mu * INR (S (S M)) * (A * A))).
    { apply (CRmult_le_compat_r (R:=R) (A * A)
        (mu * INR (S M)) (mu * INR (S (S M)))).
      - exact (CRsqr_nonneg A).
      - apply (CRmult_le_compat_l (R:=R) mu
          (INR (S M)) (INR (S (S M)))).
        + exact Hmu0.
        + apply (CRle_INR (S M) (S (S M))). lia. }
    (* 组装：CRrip_upper_final_cr *)
    assert (Hfin : CRle R (CRnorm_sq (CRcombo (S M) c u))
         (Sv + A * A + mu * INR (S (S M)) * (Sv + A * A))).
    { apply (CRrip_upper_final_cr L (A * A) Sv (A * IP)
             ((1 + 1) * CRabs R A * CRabs R IP) mu
             (INR (S M)) (INR (S (S M)))
             (CRnorm_sq (CRcombo (S M) c u))).
      - apply (proj2 Hnorm).
      - exact Hip.
      - exact H2'.
      - exact HIH.
      - exact HmA.
      - exact (CR_INR_S (S M)). }
    (* 收尾：Σ_{SM} == Sv+A² *)
    change (CRsum (fun j => c j * c j) (S M)) with (Sv + A * A).
    change (mu * INR (S (S M)) * CRsum (fun j => c j * c j) (S M))
      with (mu * INR (S (S M)) * (Sv + A * A)).
    exact Hfin.
Qed.

(* A1 主定理（k-原子 RIP）：|‖combo M‖² − Σ_{j≤M} c_j²| ≤ μ·(M+1)·Σ_{j≤M} c_j²
   （由 lower 与 upper 组合：−t ≤ X−S 且 X−S ≤ t，t := μ·(M+1)·S） *)
Lemma CRrip_bound_k
  (M : nat) (c : nat -> CRcarrier R) (u : nat -> CRComplex) (mu : CRcarrier R) :
  (CRle R (CR_of_Q R (Qmake 0 1)) mu) ->
  (forall j, le j M -> CReq R (CRnorm_sq (u j)) (CR_of_Q R (Qmake 1 1))) ->
  (forall i j, le i M -> le j M -> i <> j ->
    CRle R (CRabs R (CRip (u i) (u j))) mu) ->
  CRle R (CRabs R (CRminus R (CRnorm_sq (CRcombo M c u))
                              (CRsum (fun j => c j * c j) M)))
         (mu * INR (S M) * CRsum (fun j => c j * c j) M).
Proof.
  intros Hmu0 Hunit Hcoh.
  (* lower：S ≤ X + mu·INR(SM)·S；upper：X ≤ S + mu·INR(SM)·S *)
  assert (Hlower := CRrip_lower_M M c u mu Hmu0 Hunit Hcoh).
  assert (Hupper := CRrip_upper_M M c u mu Hmu0 Hunit Hcoh).
  set (X := CRnorm_sq (CRcombo M c u)).
  set (Sv := CRsum (fun j => c j * c j) M).
  set (t := mu * INR (S M) * Sv).
  (* 目标 |X − Sv| ≤ t ⟺ X−Sv ≤ t 且 −t ≤ X−Sv（CRabs_def） *)
  apply (proj1 (CRabs_def R (CRminus R X Sv) t)).
  split.
  - (* X − Sv ≤ t：由 Hupper（X ≤ Sv + t） *)
    apply (CRplus_le_reg_r (R:=R) Sv).
    assert (H1 : CReq R (X - Sv + Sv) X). { unfold CRminus. ring. }
    rewrite H1.
    assert (H2 : CReq R (t + Sv) (Sv + t)). { ring. }
    rewrite H2.
    (* 目标 X ≤ Sv + t = Hupper（展开 X、Sv、t） *)
    unfold X, Sv, t in Hupper. exact Hupper.
  - (* −t ≤ X − Sv：由 Hlower（Sv ≤ X + t） *)
    assert (Hm : CReq R (CRopp R (CRminus R X Sv)) (CRminus R Sv X)). { unfold CRminus. ring. }
    rewrite Hm.
    apply (CRplus_le_reg_r (R:=R) X).
    assert (Hn : CReq R (CRminus R Sv X + X) Sv). { unfold CRminus. ring. }
    rewrite Hn.
    assert (Ho : CReq R (CRplus R t X) (CRplus R X t)). { ring. }
    rewrite Ho.
    unfold X, Sv, t in Hlower. exact Hlower.
Qed.

(* ============================================================
   P5. 唯一性收尾代数（F7 恢复正确性 R4 主定理的地基：
       Σd² ≤ μ(M+1)·Σd² 且 μ(M+1) < 1 ⟹ Σd² == 0 ⟹ 逐项零）
   ============================================================ *)

(* 收缩引理：t ≤ k·t 且 k < 1 ⟹ t ≤ 0（构造性反证：
   若 0 < t，则 0 < t 且 k < 1 ⟹ k·t < 1·t == t（CRmult_lt_compat_r + 1·t==t），
   与 t ≤ k·t（即 ¬(k·t < t)）矛盾。无 t ≥ 0 前提。 *)
Lemma CRle_scaled_le_zero (t k : CRcarrier R) :
  CRle R t (k * t) ->
  CRlt R k (CR_of_Q R (Qmake 1 1)) ->
  CRle R t (CR_of_Q R (Qmake 0 1)).
Proof.
  intros Htk Hk1.
  unfold CRle. intro H0t.
  apply Htk.
  assert (Hkt : CRlt R (k * t) (CR_of_Q R (Qmake 1 1) * t)).
  { apply (CRmult_lt_compat_r (R:=R) t k (CR_of_Q R (Qmake 1 1)) H0t Hk1). }
  rewrite (CRmult_1_l (R:=R) t) in Hkt.
  exact Hkt.
Qed.

(* 平方为零 ⟹ 元为零（构造性反证：
   0 ≤ x 的反证：x < 0 ⟹ 0 < −x ⟹ 0 < (−x)² == x²（CRopp_mult_distr_*），
   矛盾 x² ≤ 0；x ≤ 0 的反证：0 < x ⟹ 0 < x²（CRmult_lt_0_compat），矛盾。 *)
Lemma CRsqr_eq_zero (x : CRcarrier R) :
  CReq R (CRmult R x x) (CR_of_Q R (Qmake 0 1)) ->
  CReq R x (CR_of_Q R (Qmake 0 1)).
Proof.
  intros Hsq.
  assert (Hsq_le0 : CRle R (CRmult R x x) (CR_of_Q R (Qmake 0 1))).
  { exact (proj2 Hsq). }
  split; unfold CRle; intro.
  - assert (Hnx : CRlt R (CR_of_Q R (Qmake 0 1)) (CRopp R x)).
    { apply (CRplus_lt_reg_r (R:=R) x).
      rewrite CRplus_0_l. rewrite CRplus_opp_l. exact H. }
    assert (Hnxsq : CRlt R (CR_of_Q R (Qmake 0 1))
                     (CRmult R (CRopp R x) (CRopp R x))).
    { apply (CRmult_lt_0_compat R (CRopp R x) (CRopp R x) Hnx Hnx). }
    apply Hsq_le0.
    rewrite <- (CRopp_mult_distr_r (R:=R) (CRopp R x) x) in Hnxsq.
    rewrite (CRopp_mult_distr_l (R:=R) (CRopp R x) x) in Hnxsq.
    rewrite (CRopp_involutive (R:=R) x) in Hnxsq.
    exact Hnxsq.
  - apply Hsq_le0.
    apply (CRmult_lt_0_compat R x x H H).
Qed.

(* 辅助：非负逐项 ⟹ 任一项 ≤ 和（j ≤ M ⟹ f j ≤ Σ_{k≤M} f k，归纳：
   尾项情形 0 ≤ Σ_{k≤M-1} f k ⟹ f_M ≤ Σ_{k≤M-1} f k + f_M；
   前段情形 IH + Rplus_le_pos（0 ≤ f_M）。 *)
Lemma CRsum_nonneg_term_le (M : nat) (f : nat -> CRcarrier R) :
  (forall k, CRle R (CR_of_Q R (Qmake 0 1)) (f k)) ->
  forall j, le j M -> CRle R (f j) (CRsum f M).
Proof.
  intros Hnonneg.
  induction M as [| M IH].
  - intros j Hj.
    assert (Hj0 : j = 0%nat) by lia.
    subst j.
    apply CRle_refl.
  - intros j Hj.
    assert (Hj2 : j = S M \/ le j M) by lia.
    destruct Hj2 as [HjS | Hjle].
    + subst j.
      change (CRsum f (S M)) with (CRsum f M + f (S M)).
      apply (CRle_trans (R:=R) (f (S M)) (f (S M) + CRsum f M)
             (CRsum f M + f (S M))).
      * apply (Rplus_le_pos (R:=R) (f (S M)) (CRsum f M)).
        exact (cond_pos_sum f M Hnonneg).
      * assert (Hc : CReq R (f (S M) + CRsum f M) (CRsum f M + f (S M))).
        { ring. }
        exact (proj2 Hc).
    + change (CRsum f (S M)) with (CRsum f M + f (S M)).
      apply (CRle_trans (R:=R) (f j) (CRsum f M) (CRsum f M + f (S M))).
      * exact (IH j Hjle).
      * apply (Rplus_le_pos (R:=R) (CRsum f M) (f (S M))).
        exact (Hnonneg (S M)).
Qed.

(* 平方和为零 ⟹ 逐项为零（零和非负项：
   每项 c_j² ≤ Σc² == 0（CRsum_nonneg_term_le + CRle_trans），且 0 ≤ c_j²
   （CRsqr_nonneg）⟹ c_j² == 0 ⟹ c_j == 0（CRsqr_eq_zero）。 *)
Lemma CRsum_sq_zero_terms (M : nat) (c : nat -> CRcarrier R)
  (Hsq : CReq R (CRsum (fun j => c j * c j) M) (CR_of_Q R (Qmake 0 1))) :
  forall j, le j M -> CReq R (c j) (CR_of_Q R (Qmake 0 1)).
Proof.
  intros j Hj.
  assert (Hsum_le0 : CRle R (CRsum (fun j => c j * c j) M) (CR_of_Q R (Qmake 0 1))).
  { exact (proj2 Hsq). }
  assert (Hj_le : CRle R (c j * c j) (CRsum (fun j => c j * c j) M)).
  { apply (CRsum_nonneg_term_le M (fun k => c k * c k)).
    - intro k. exact (CRsqr_nonneg (c k)).
    - exact Hj. }
  assert (Hj_le0 : CRle R (c j * c j) (CR_of_Q R (Qmake 0 1))).
  { apply (CRle_trans (R:=R) (c j * c j)
           (CRsum (fun j => c j * c j) M) (CR_of_Q R (Qmake 0 1))).
    - exact Hj_le.
    - exact Hsum_le0. }
  apply (CRsqr_eq_zero (c j)).
  split; [exact (CRsqr_nonneg (c j)) | exact Hj_le0].
Qed.

End CRSqr.
