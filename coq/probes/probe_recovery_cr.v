(* ============================================================
   用户红线：纯构造性——Stdlib ConstructiveReals（Set 层 CRcarrier + Prop 层 CReq/CRle/CRlt），
             零经典实数（不用 Stdlib.Reals.Reals）、零 Admitted、零自定义公理。

   数学内容： 若字典 {u_j} 满足相干唯一性条件（μ(M+1) < 1），则同一信号的两个
   （前缀支撑）构造性表示必相同：
     x = Σ_{j≤M} c_j·u_j == Σ_{j≤M} c'_j·u_j  ⟹  ∀j≤M: c_j == c'_j
   —— 即"唯一性 ⟹ 恢复正确性"的确定性骨架（不碰 OMP/基追踪算法本体）。

   证明链（本探针，纯 CR）：
     R0. CRcombo_diff_re/im/diff：CRcombo M (c−c') u == CRcombo M c u − CRcombo M c' u
         （分量级差分线性，归纳 M + ring）
     R1. CRcombo_zero_from_eq_cplx：两表示相等 ⟹ 差组合 == 0（CReq_cplx 级）
     R2. CRcombo_diff_norm_sq_zero：差组合范数平方 == 0（由 R1）
     R3. CRcombo_diff_rip_bound：差组合范数平方界（CRrip_bound_k 实例化）
     R4. ★ CRrecovery_correct_prefix（主定理）：唯一性 ⟹ 系数相等
         （路线：范数零（R2）+ RIP 界（R3）+ CRle_scaled_le_zero（μ(M+1)<1 收缩）
          ⟹ Σd²≤0；CRsum_sq_nonneg + CReq ⟹ Σd²==0；
          CRsum_sq_zero_terms（ca_rip_cr P5）⟹ 逐项零 ⟹ c==c'）

   依赖： ca_rip_cr（CRcombo/CRnorm_sq/CRrip_bound_k/CRsum_sq_nonneg/CRip/CRisRing）。
   结构：Section F7Recovery + Add Ring（与 ca_rip_cr 一致，ring 可用）。
   审计： Print Assumptions 尾部（应仅 ConstructiveReals 接口，零经典）。
   ============================================================ *)
Require Import ConstructiveReals.
From Stdlib Require Import ConstructiveRealsMorphisms.
From Stdlib Require Import ConstructiveAbs.
From Stdlib Require Import ConstructiveSum.
Require Import Stdlib.QArith.QArith.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.micromega.Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat seq eqtype div prime.
Require Import ca_rip_cr.

Local Open Scope ConstructiveReals.
(* 注：mathcomp leq/ltn 经 ssrbool 默认可用（`le j M` = leq）。 *)

Section F7Recovery.

Context {R : ConstructiveReals}.
Add Ring CR_ring : (CRisRing R).

(* ============ R0. CRcombo 差分线性 ============ *)

(* 实部差分线性 *)
Lemma CRcombo_diff_re (M : nat) (c c' : nat -> CRcarrier R) (u : nat -> CRComplex) :
  CReq R (cre (CRcombo M (fun j => (c j - c' j)%ConstructiveReals) u))
         (cre (CRcombo M c u) - cre (CRcombo M c' u))%ConstructiveReals.
Proof.
  elim: M => [| M IH].
  - cbn [CRcombo cre cim]. unfold CRminus. ring.
  - cbn [CRcombo cre cim]. rewrite IH. unfold CRminus. ring.
Qed.

(* 虚部差分线性 *)
Lemma CRcombo_diff_im (M : nat) (c c' : nat -> CRcarrier R) (u : nat -> CRComplex) :
  CReq R (cim (CRcombo M (fun j => (c j - c' j)%ConstructiveReals) u))
         (cim (CRcombo M c u) - cim (CRcombo M c' u))%ConstructiveReals.
Proof.
  elim: M => [| M IH].
  - cbn [CRcombo cre cim]. unfold CRminus. ring.
  - cbn [CRcombo cre cim]. rewrite IH. unfold CRminus. ring.
Qed.

(* ============ R1. 两表示相等 ⟹ 差组合 == 0（分量级） ============ *)

(* 实部：两表示实部相等 ⟹ 差组合实部 == 0 *)
Lemma CRcombo_zero_from_eq_re (M : nat) (c c' : nat -> CRcarrier R) (u : nat -> CRComplex)
  (Heq : CReq R (cre (CRcombo M c u)) (cre (CRcombo M c' u))) :
  CReq R (cre (CRcombo M (fun j => (c j - c' j)%ConstructiveReals) u))
         (cre CRzero).
Proof.
  pose (Hr := CRcombo_diff_re M c c' u).
  apply (CReq_trans (R := R) (cre (CRcombo M (fun j => (c j - c' j)%ConstructiveReals) u))
                        (cre (CRcombo M c u) - cre (CRcombo M c' u))%ConstructiveReals
                        (cre CRzero)).
  - exact Hr.
  - unfold CRminus. rewrite Heq. unfold CRzero. cbn. ring.
Qed.

(* 虚部：两表示虚部相等 ⟹ 差组合虚部 == 0 *)
Lemma CRcombo_zero_from_eq_im (M : nat) (c c' : nat -> CRcarrier R) (u : nat -> CRComplex)
  (Heq : CReq R (cim (CRcombo M c u)) (cim (CRcombo M c' u))) :
  CReq R (cim (CRcombo M (fun j => (c j - c' j)%ConstructiveReals) u))
         (cim CRzero).
Proof.
  pose (Hi := CRcombo_diff_im M c c' u).
  apply (CReq_trans (R := R) (cim (CRcombo M (fun j => (c j - c' j)%ConstructiveReals) u))
                        (cim (CRcombo M c u) - cim (CRcombo M c' u))%ConstructiveReals
                        (cim CRzero)).
  - exact Hi.
  - unfold CRminus. rewrite Heq. unfold CRzero. cbn. ring.
Qed.

(* R1 复数级（由 re/im 组装） *)
Lemma CRcombo_zero_from_eq_cplx (M : nat) (c c' : nat -> CRcarrier R) (u : nat -> CRComplex)
  (Heq : CReq_cplx (CRcombo M c u) (CRcombo M c' u)) :
  CReq_cplx (CRcombo M (fun j => (c j - c' j)%ConstructiveReals) u) CRzero.
Proof.
  unfold CReq_cplx in *. destruct Heq as [Here Him].
  split.
  - apply (CRcombo_zero_from_eq_re M c c' u Here).
  - apply (CRcombo_zero_from_eq_im M c c' u Him).
Qed.

(* ============ R2. 差组合范数平方 == 0（由 R1） ============ *)

Lemma CRcombo_diff_norm_sq_zero (M : nat) (c c' : nat -> CRcarrier R) (u : nat -> CRComplex)
  (Heq : CReq_cplx (CRcombo M c u) (CRcombo M c' u)) :
  CReq R (CRnorm_sq (CRcombo M (fun j => (c j - c' j)%ConstructiveReals) u))
         (CR_of_Q R (Qmake 0 1)).
Proof.
  pose (Hz := CRcombo_zero_from_eq_cplx M c c' u Heq).
  unfold CReq_cplx in Hz. destruct Hz as [Hzre Hzim].
  unfold CRnorm_sq.
  rewrite Hzre Hzim.
  cbn. unfold CRminus. ring.
Qed.

(* ============ R3. 差组合范数平方界（CRrip_bound_k 实例化） ============ *)
(* 注：CRrip_bound_k 直接给出 RIP 界（无需 μ(M+1)<1 前提）；μ(M+1)<1 在 R4 用于
   从界推出 Σd²==0（唯一性收尾）。 *)

Lemma CRcombo_diff_rip_bound (M : nat) (c c' : nat -> CRcarrier R) (u : nat -> CRComplex)
  (mu : CRcarrier R) (Hmu0 : CRle R (CR_of_Q R (Qmake 0 1)) mu)
  (Hunit : forall j, le j M -> CReq R (CRnorm_sq (u j)) (CR_of_Q R (Qmake 1 1)))
  (Hcoh : forall i j, le i M -> le j M -> i <> j ->
    CRle R (CRabs R (CRip (u i) (u j))) mu) :
  CRle R (CRabs R (CRminus R
      (CRnorm_sq (CRcombo M (fun j => (c j - c' j)%ConstructiveReals) u))
      (CRsum (fun j => ((c j - c' j) * (c j - c' j))%ConstructiveReals) M)))
         ((mu * INR (S M))%ConstructiveReals * CRsum (fun j => ((c j - c' j) * (c j - c' j))%ConstructiveReals) M).
Proof.
  exact (CRrip_bound_k (R := R) M (fun j => (c j - c' j)%ConstructiveReals) u mu Hmu0 Hunit Hcoh).
Qed.

(* ============ R4. ★ 主定理：唯一性 ⟹ 恢复正确性（前缀支撑版） ============ *)
(* 陈述：若字典满足唯一性条件（μ(M+1)<1），同一信号两个表示相等 ⟹ 系数逐点相等。
   证明路线（R2 + R3 + ca_rip_cr P5 代数收尾）：
     1. R2：‖d·u‖² == 0（CRcombo_diff_norm_sq_zero）；
     2. R3：|‖d·u‖² − Σd²| ≤ μ(M+1)·Σd²（CRcombo_diff_rip_bound）；
     3. 改写 ‖d·u‖² == 0，|0−Σd²| == |−Σd²| == |Σd²|（CRminus 0 == −、CRabs_opp），
        CRabs_def proj2（|Sv| ≤ k·Sv ⟹ Sv ≤ k·Sv）⟹ Σd² ≤ μ(M+1)·Σd²；
     4. CRle_scaled_le_zero：Σd² ≤ μ(M+1)·Σd² 且 μ(M+1)<1 ⟹ Σd² ≤ 0；
     5. CRsum_sq_nonneg（0 ≤ Σd²）+ CReq split ⟹ Σd² == 0；
     6. CRsum_sq_zero_terms（平方和零 ⟹ 逐项零）⟹ c_j == c'_j（ring 收尾）。 *)

Theorem CRrecovery_correct_prefix (M : nat) (c c' : nat -> CRcarrier R) (u : nat -> CRComplex)
  (mu : CRcarrier R)
  (Hmu0 : CRle R (CR_of_Q R (Qmake 0 1)) mu)
  (Hmu1 : CRlt R (mu * INR (S M)) (CR_of_Q R (Qmake 1 1)))
  (Hunit : forall j, le j M -> CReq R (CRnorm_sq (u j)) (CR_of_Q R (Qmake 1 1)))
  (Hcoh : forall i j, le i M -> le j M -> i <> j ->
    CRle R (CRabs R (CRip (u i) (u j))) mu)
  (Heq : CReq_cplx (CRcombo M c u) (CRcombo M c' u)) :
  forall j, le j M -> CReq R (c j) (c' j).
Proof.
  intros j Hj.
  set (Sv := CRsum (fun j => (c j - c' j) * (c j - c' j)) M).
  (* R2：‖d·u‖² == 0（assert := 形式：真假设，可被 rewrite 代入） *)
  assert (Hnorm0 := CRcombo_diff_norm_sq_zero M c c' u Heq).
  (* R3：RIP 界 *)
  assert (Hbound := CRcombo_diff_rip_bound M c c' u mu Hmu0 Hunit Hcoh).
  (* 改写 Hbound 中 ‖d·u‖² == 0，并把 Σd² 统一为 Sv *)
  rewrite Hnorm0 in Hbound.
  change (CRsum (fun j => (c j - c' j) * (c j - c' j)) M) with Sv in Hbound.
  (* |0 − Sv| == |−Sv| == |Sv| *)
  assert (Hm0 : CReq R (CRminus R (CR_of_Q R (Qmake 0 1)) Sv) (CRopp R Sv)).
  { unfold CRminus. rewrite (CRplus_0_l (R:=R) (CRopp R Sv)). reflexivity. }
  rewrite Hm0 in Hbound.
  rewrite (CRabs_opp (R:=R) Sv) in Hbound.
  (* Sv ≤ μ(M+1)·Sv：CRabs_def proj2（|Sv| ≤ k·Sv ⟹ Sv ≤ k·Sv） *)
  assert (Hsv_le : CRle R Sv ((mu * INR (S M)) * Sv)).
  { exact (proj1 (proj2 (CRabs_def R Sv ((mu * INR (S M)) * Sv)) Hbound)). }
  (* Sv ≤ 0：CRle_scaled_le_zero（ca_rip_cr P5） *)
  assert (Hsv_le0 : CRle R Sv (CR_of_Q R (Qmake 0 1))).
  { apply (CRle_scaled_le_zero Sv (mu * INR (S M))).
    - exact Hsv_le.
    - exact Hmu1. }
  (* 0 ≤ Sv：CRsum_sq_nonneg *)
  assert (Hsv_ge0 : CRle R (CR_of_Q R (Qmake 0 1)) Sv).
  { exact (CRsum_sq_nonneg M (fun j => (c j - c' j)%ConstructiveReals)). }
  (* Sv == 0 *)
  assert (Hsv0 : CReq R Sv (CR_of_Q R (Qmake 0 1))).
  { split; [exact Hsv_ge0 | exact Hsv_le0]. }
  (* 逐项零：(c j - c' j) == 0 ⟹ c j == c' j（ring 收尾） *)
  apply (CReq_trans (R:=R) (c j) ((c j - c' j) + c' j) (c' j)).
  - unfold CRminus. ring.
  - pose (Ht := CRsum_sq_zero_terms M (fun k => (c k - c' k)%ConstructiveReals) Hsv0).
    rewrite (Ht j Hj). unfold CRminus. ring.
Qed.

End F7Recovery.
