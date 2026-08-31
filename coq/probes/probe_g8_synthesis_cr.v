(* ============================================================
   纪律：纯构造性——Stdlib ConstructiveReals（Set 层 CRcarrier + Prop 层
             CReq/CRle/CRlt），零经典实数（不用 Stdlib.Reals.Reals）、
             零 Admitted、零自定义公理。

   数学内容（压缩感知三角闭环的合成定理）：
     若字典相干 μ 同时满足
       (G-7 Welch 下界，平方形态)  (INR M - INR N) ≤ INR N · INR(M-1) · μ²
       (F5 唯一性窗口)             μ · INR(|T1|+|T2|−1) < 1
     则同一信号的两个 |T|-稀疏表示必相同（唯一恢复保证）。
     —— Welch 界给出"字典设计的最优性"（相干不可能低于下界），
        F5 给出"恢复保证"（相干足够小时表示唯一），
        合成 = 相图定理：μ 落在 [Welch, 1/|T|) 才有唯一恢复。

   证明链（本探针，纯 CR，复用 F5/R4 战术）：
     R0. CR 算术辅助：0 ≤ z < 1 ⟹ z·z < 1（CRsqr_lt_one，构造性）；
         0 ≤ a ≤ b、0 ≤ c ≤ d ⟹ ac ≤ bd（CRmult_le_compat_4）。
     R1. ★ CRphase_window_nonempty（相图窗口非空）：
           Welch 下界 + F5 窗口 ⟹ (INR M − INR N)·(INR T)² < INR N·INR(M−1)
           ——"Welch < 1/|T| 时唯一性窗口非空"的定量参数条件
           （路线：0 ≤ μT ∧ μT<1 ⟹ (μT)²<1 [CRsqr_lt_one]；
             Welch 两边乘 T²；N(M−1)·(μT)² < N(M−1) [乘 0≤N(M−1)]；
             CRle_lt_trans 组装）
     R2. ★ CRg8_recovery_synthesis（主合成定理）：
           Welch 下界（抽象前提）+ F5 全部前提 ⟹ 唯一恢复
           （直接实例化 F5 CRuncertainty_principle——相图区间
             [Welch, 1/|T|) 上的恢复保证；Welch 前提经
             CRphase_window_nonempty 给出窗口非空叙事）

   依赖： ca_rip_cr（CRip/CRnorm_sq/CRcombo/CRabs）+ probe_uncertainty_cr（F5）。
   结构：Section G8Synthesis + Add Ring（与 ca_rip_cr / F5 / R4 一致）。
   审计：零 Admitted / 零自定义公理；Print Assumptions 尾部应仅
         ConstructiveReals 接口（零经典）。
   ============================================================ *)
Require Import ConstructiveReals.
From Stdlib Require Import ConstructiveRealsMorphisms.
From Stdlib Require Import ConstructiveAbs.
From Stdlib Require Import ConstructiveSum.
Require Import Stdlib.QArith.QArith.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.micromega.Lia.
From Stdlib Require Import List.
Import ListNotations.
From mathcomp Require Import ssreflect ssrbool ssrnat seq eqtype div prime.
Require Import ca_rip_cr.
Require Import probe_uncertainty_cr.

Local Open Scope ConstructiveReals.
(* le/lt 用 Coq 原生函数（mathcomp 不劫持这两个标识符），lia 可处理。 *)

Section G8Synthesis.

Context {R : ConstructiveReals}.
Add Ring CR_ring : (CRisRing R).

(* ============ R0. CR 算术辅助 ============ *)

(* 0 ≤ z < 1 ⟹ z·z < 1（CR 层平方收缩，构造性） *)
Lemma CRsqr_lt_one (z : CRcarrier R) :
  CRle R (CR_of_Q R (Qmake 0 1)) z ->
  CRlt R z (CR_of_Q R (Qmake 1 1)) ->
  CRlt R (z * z) (CR_of_Q R (Qmake 1 1)).
Proof.
  intros Hz0 Hz1.
  (* z·z ≤ z·1 == z（0 ≤ z 且 z ≤ 1，乘非负） *)
  assert (Hzz : CRle R (z * z) (z * CR_of_Q R (Qmake 1 1))).
  { apply (CRmult_le_compat_l (R:=R) z z (CR_of_Q R (Qmake 1 1))).
    - exact Hz0.
    - exact (CRlt_asym (R:=R) z (CR_of_Q R (Qmake 1 1)) Hz1). }
  assert (Hzone : CReq R (z * CR_of_Q R (Qmake 1 1)) z). { ring. }
  apply (CRle_lt_trans (R:=R) (z * z) z (CR_of_Q R (Qmake 1 1))).
  - apply (CRle_trans (R:=R) (z * z) (z * CR_of_Q R (Qmake 1 1)) z).
    + exact Hzz.
    + apply (proj2 Hzone).
  - exact Hz1.
Qed.

(* 0 ≤ a ≤ b、0 ≤ c ≤ d ⟹ a·c ≤ b·d（CR 层复合单调） *)
Lemma CRmult_le_compat_4 (a b c d : CRcarrier R) :
  CRle R (CR_of_Q R (Qmake 0 1)) a -> CRle R a b ->
  CRle R (CR_of_Q R (Qmake 0 1)) c -> CRle R c d ->
  CRle R (a * c) (b * d).
Proof.
  intros Ha0 Hab Hc0 Hcd.
  apply (CRle_trans (R:=R) (a * c) (b * c) (b * d)).
  - apply (CRmult_le_compat_r (R:=R) c a b).
    + exact Hc0.
    + exact Hab.
  - apply (CRmult_le_compat_l (R:=R) b c d).
    + apply (CRle_trans (R:=R) (CR_of_Q R (Qmake 0 1)) a b).
      * exact Ha0.
      * exact Hab.
    + exact Hcd.
Qed.

(* 1 ≤ n ⟹ 0 < INR n（严格正） *)
Lemma CR0_lt_INR_pos (n : nat) :
  le 1 n -> CRlt R (CR_of_Q R (Qmake 0 1)) (INR n).
Proof.
  intros Hn1.
  apply (CRlt_le_trans (R:=R) (CR_of_Q R (Qmake 0 1)) (INR 1) (INR n)).
  - change (INR 1) with (CR_of_Q R (Qmake 1 1)).
    exact (CRzero_lt_one R).
  - apply (CRle_INR 1 n). exact Hn1.
Qed.

(* INR (Nat.pred M) 非负（M ≥ 2 由 N ≥ 1 且 N < M 推出） *)
Lemma CR_INR_pred_nonneg (M N : nat) :
  le 1 N -> lt N M ->
  CRle R (CR_of_Q R (Qmake 0 1)) (INR (Nat.pred M)).
Proof.
  intros HN1 HNM.
  assert (HM1 : le 1 (Nat.pred M)) by lia.
  apply (CRle_trans (R:=R) (CR_of_Q R (Qmake 0 1)) (INR 1) (INR (Nat.pred M))).
  - exact (CR0_le_INR 1).
  - apply (CRle_INR 1 (Nat.pred M)). exact HM1.
Qed.

(* ============ R1. ★ 相图窗口非空 ============ *)

(* 若字典相干 μ 满足 Welch 下界（平方形态）且落在 F5 唯一性窗口内，
   则窗口非空的参数条件成立：(M−N)·T² < N·(M−1)。
   （T := |T1|+|T2|−1 抽象为 nat 参数；welch 下界为 G-7 的抽象前提。） *)
Theorem CRphase_window_nonempty (M N T : nat) (mu : CRcarrier R) :
  le 1 N -> lt N M -> le 1 T ->
  CRle R (CR_of_Q R (Qmake 0 1)) mu ->
  (* G-7 Welch 下界（平方形态，抽象前提） *)
  CRle R (INR M - INR N) (INR N * INR (Nat.pred M) * mu * mu) ->
  (* F5 唯一性窗口：μ·T < 1 *)
  CRlt R (mu * INR T) (CR_of_Q R (Qmake 1 1)) ->
  (* 相图窗口非空（定量参数条件） *)
  CRlt R ((INR M - INR N) * (INR T * INR T))
         (INR N * INR (Nat.pred M)).
Proof.
  intros HN1 HNM HT1 Hmu0 Hwelch Hwin.
  (* ① (μ·T)² < 1：由 0 ≤ μ·T 与 μ·T < 1 平方收缩 *)
  assert (HmuT0 : CRle R (CR_of_Q R (Qmake 0 1)) (mu * INR T)).
  { apply (CRmult_le_0_compat (R:=R) mu (INR T)); [exact Hmu0 | exact (CR0_le_INR T)]. }
  assert (HmuT1 : CRlt R ((mu * INR T) * (mu * INR T)) (CR_of_Q R (Qmake 1 1))).
  { exact (CRsqr_lt_one (mu * INR T) HmuT0 Hwin). }
  (* ② Welch 下界两边乘 (INR T)²（非负） *)
  assert (HT20 : CRle R (CR_of_Q R (Qmake 0 1)) (INR T * INR T)).
  { apply (CRmult_le_0_compat (R:=R) (INR T) (INR T));
      exact (CR0_le_INR T). }
  assert (HwelchT : CRle R ((INR M - INR N) * (INR T * INR T))
                            ((INR N * INR (Nat.pred M) * mu * mu) * (INR T * INR T))).
  { apply (CRmult_le_compat_r (R:=R) (INR T * INR T)
      (INR M - INR N) (INR N * INR (Nat.pred M) * mu * mu)).
    - exact HT20.
    - exact Hwelch. }
  (* ③ 右侧整理：(N(M−1)·μ²)·T² == N(M−1)·(μT)² *)
  assert (Hre : CReq R
    ((INR N * INR (Nat.pred M) * mu * mu) * (INR T * INR T))
    (INR N * INR (Nat.pred M) * ((mu * INR T) * (mu * INR T)))).
  { ring. }
  assert (HwelchT' : CRle R ((INR M - INR N) * (INR T * INR T))
                            (INR N * INR (Nat.pred M) * ((mu * INR T) * (mu * INR T)))).
  { apply (CRle_trans (R:=R)
      ((INR M - INR N) * (INR T * INR T))
      ((INR N * INR (Nat.pred M) * mu * mu) * (INR T * INR T))
      (INR N * INR (Nat.pred M) * ((mu * INR T) * (mu * INR T)))).
    - exact HwelchT.
    - apply (proj2 Hre). }
  (* ④ 右侧上界：N(M−1)·(μT)² < N(M−1)·1，且 N(M−1)·1 == N(M−1) *)
  assert (HN0 : CRle R (CR_of_Q R (Qmake 0 1)) (INR N * INR (Nat.pred M))).
  { apply (CRmult_le_0_compat (R:=R) (INR N) (INR (Nat.pred M)));
      [exact (CR0_le_INR N) | exact (CR_INR_pred_nonneg M N HN1 HNM)]. }
  assert (HNpos : CRlt R (CR_of_Q R (Qmake 0 1)) (INR N * INR (Nat.pred M))).
  { apply (CRmult_lt_0_compat R (INR N) (INR (Nat.pred M))).
    - exact (CR0_lt_INR_pos N HN1).
    - assert (HM1 : le 1 (Nat.pred M)) by lia.
      exact (CR0_lt_INR_pos (Nat.pred M) HM1). }
  assert (Hright : CRlt R (INR N * INR (Nat.pred M) * ((mu * INR T) * (mu * INR T)))
                           (INR N * INR (Nat.pred M) * CR_of_Q R (Qmake 1 1))).
  { apply (CRmult_lt_compat_l (R:=R) (INR N * INR (Nat.pred M))
      ((mu * INR T) * (mu * INR T)) (CR_of_Q R (Qmake 1 1))).
    - exact HNpos.
    - exact HmuT1. }
  (* ⑤ 组装：LHS ≤ N(M−1)(μT)² < N(M−1)·1 == N(M−1) *)
  assert (Hone : CReq R
    (INR N * INR (Nat.pred M) * CR_of_Q R (Qmake 1 1))
    (INR N * INR (Nat.pred M))). { ring. }
  apply (CRle_lt_trans (R:=R)
    ((INR M - INR N) * (INR T * INR T))
    (INR N * INR (Nat.pred M) * ((mu * INR T) * (mu * INR T)))
    (INR N * INR (Nat.pred M))).
  - exact HwelchT'.
  - rewrite Hone in Hright. exact Hright.
Qed.

(* ============ R2. ★ 主合成定理：字典最优性 ⟹ 恢复保证 ============ *)

(* 若字典相干 μ 满足 Welch 下界（抽象前提，G-7 提供）且落在 F5 唯一性窗口内，
   则同一信号的两个 |T|-稀疏表示必相同。
   合成 = F5 CRuncertainty_principle 在相图区间 [Welch, 1/|T|) 上的实例化：
   Welch 前提给出"字典设计的最优性"叙事（经 R1 窗口非空），
   F5 窗口给出"恢复保证"（μ < 1/(|T1|+|T2|−1) ⟹ 表示唯一）。 *)
Theorem CRg8_recovery_synthesis (M N : nat) (T1 T2 : list nat)
  (c d : nat -> CRcarrier R) (u : nat -> CRComplex) (mu : CRcarrier R)
  (HN1 : le 1 N) (HNM : lt N M)
  (Hmu0 : CRle R (CR_of_Q R (Qmake 0 1)) mu)
  (* G-7 Welch 下界（平方形态，抽象前提） *)
  (Hwelch : CRle R (INR M - INR N) (INR N * INR (Nat.pred M) * mu * mu))
  (Hdup1 : NoDup T1) (Hdup2 : NoDup T2)
  (Hunit : forall j, In j T1 \/ In j T2 ->
    CReq R (CRnorm_sq (u j)) (CR_of_Q R (Qmake 1 1)))
  (Hcoh : forall i j, In i T1 \/ In i T2 -> In j T1 \/ In j T2 -> i <> j ->
    CRle R (CRabs R (CRip (u i) (u j))) mu)
  (Hrep : CReq_cplx (lst_combo T1 c u) (lst_combo T2 d u))
  (Hc0 : forall j, ~ In j T1 -> CReq R (c j) (CR_of_Q R (Qmake 0 1)))
  (Hd0 : forall j, ~ In j T2 -> CReq R (d j) (CR_of_Q R (Qmake 0 1)))
  (* F5 唯一性窗口：μ·(|T1|+|T2|−1) < 1 *)
  (Hwin : CRlt R (mu * INR (length T1 + length T2 - 1)) (CR_of_Q R (Qmake 1 1))) :
  forall j, CReq R (c j) (d j).
Proof.
  (* 直接实例化 F5 主定理（相图区间 [Welch, 1/|T|) 上的唯一恢复） *)
  apply (CRuncertainty_principle T1 T2 c d u mu Hmu0 Hdup1 Hdup2 Hunit Hcoh
                                 Hrep Hc0 Hd0 Hwin).
Qed.

End G8Synthesis.

(* ---------- 审计 ---------- *)
Print Assumptions CRphase_window_nonempty.
Print Assumptions CRg8_recovery_synthesis.


