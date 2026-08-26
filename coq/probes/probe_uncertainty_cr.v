(* ============================================================
   F5 不确定性原理（纯构造性 CR 版，probe_uncertainty_cr）
   纪律：纯构造性——Stdlib ConstructiveReals，零经典实数、
         零 Admitted、零自定义公理；35 定理全 Qed，
         Print Assumptions 全部 Closed under the global context。
   主定理 CRuncertainty_principle：相干字典不确定原理（唯一性正形式，
   Donoho-Stark 标准，常数 1+1/μ）。
   数学内容：若字典 {u_j}（单位范数、相干 ≤ μ）上同一信号 x 有两个稀疏表示，
   则两表示在支撑上逐点相同（|T1|+|T2|−1 的相干窗口）。
   ============================================================ *)
Require Import ConstructiveReals.
From Stdlib Require Import ConstructiveRealsMorphisms.
From Stdlib Require Import ConstructiveAbs.
From Stdlib Require Import ConstructiveSum.
From Stdlib Require Import QArith.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
Import ListNotations.
From mathcomp Require Import ssreflect ssrbool ssrnat seq eqtype div prime.
Require Import ca_rip_cr.

Local Open Scope ConstructiveReals.

Section F5Uncertainty.

Context {R : ConstructiveReals}.
Add Ring CR_ring : (CRisRing R).

(* ============ A. 列表基础设施 ============ *)

(* 标量乘复数 *)
Definition scal (c : CRcarrier R) (z : CRComplex) : CRComplex :=
  {| cre := c * cre z; cim := c * cim z |}.

(* 列表和（尾部优先；顺序由 ring 交换律吸收） *)
Fixpoint lst_sum (T : list nat) (f : nat -> CRcarrier R) : CRcarrier R :=
  match T with
  | nil => CR_of_Q R (Qmake 0 1)
  | j :: T' => lst_sum T' f + f j
  end.

(* 平方和 / 绝对值 ℓ1 和 *)
Definition lst_sqsum (T : list nat) (e : nat -> CRcarrier R) : CRcarrier R :=
  lst_sum T (fun j => e j * e j).
Definition lst_abs_sum (T : list nat) (e : nat -> CRcarrier R) : CRcarrier R :=
  lst_sum T (fun j => CRabs R (e j)).

(* 列表线性组合 *)
Fixpoint lst_combo (T : list nat) (e : nat -> CRcarrier R) (u : nat -> CRComplex) : CRComplex :=
  match T with
  | nil => CRzero
  | j :: T' => CRadd (lst_combo T' e u) (scal (e j) (u j))
  end.

(* lst_sum 单调（逐点 ≤ ⟹ 和 ≤） *)
Lemma lst_sum_le (T : list nat) (f g : nat -> CRcarrier R) :
  (forall j, In j T -> CRle R (f j) (g j)) ->
  CRle R (lst_sum T f) (lst_sum T g).
Proof.
  induction T as [| j T' IH]; intros Hle.
  - apply CRle_refl.
  - cbn [lst_sum].
    apply (CRle_trans (R:=R) (lst_sum T' f + f j) (lst_sum T' g + f j) (lst_sum T' g + g j)).
    + apply (CRplus_le_compat_r (R:=R) (f j)).
      apply IH. intros k Hk. apply Hle. right. exact Hk.
    + apply (CRplus_le_compat_l (R:=R) (lst_sum T' g)).
      apply Hle. left. reflexivity.
Qed.

(* lst_sum 逐点相等（CReq） *)
Lemma lst_sum_morph (T : list nat) (f g : nat -> CRcarrier R) :
  (forall j, In j T -> CReq R (f j) (g j)) ->
  CReq R (lst_sum T f) (lst_sum T g).
Proof.
  induction T as [| j T' IH]; intros Heq.
  - reflexivity.
  - cbn [lst_sum].
    split.
    + apply (CRplus_le_compat (R:=R) (lst_sum T' g) (lst_sum T' f) (g j) (f j)).
      * exact (proj1 (IH (fun k Hk => Heq k (or_intror Hk)))).
      * exact (proj1 (Heq j (or_introl Logic.eq_refl))).
    + apply (CRplus_le_compat (R:=R) (lst_sum T' f) (lst_sum T' g) (f j) (g j)).
      * exact (proj2 (IH (fun k Hk => Heq k (or_intror Hk)))).
      * exact (proj2 (Heq j (or_introl Logic.eq_refl))).
Qed.

(* lst_sum 非负（逐项非负 ⟹ 和非负） *)
Lemma lst_sum_nonneg (T : list nat) (f : nat -> CRcarrier R) :
  (forall j, In j T -> CRle R (CR_of_Q R (Qmake 0 1)) (f j)) ->
  CRle R (CR_of_Q R (Qmake 0 1)) (lst_sum T f).
Proof.
  induction T as [| j T' IH]; intros Hn.
  - apply CRle_refl.
  - cbn [lst_sum].
    rewrite <- (CRplus_0_l (R:=R) (CR_of_Q R (Qmake 0 1))).
    apply (CRplus_le_compat (R:=R)
      (CR_of_Q R (Qmake 0 1)) (lst_sum T' f)
      (CR_of_Q R (Qmake 0 1)) (f j)).
    + apply IH. intros k Hk. apply Hn. right. exact Hk.
    + apply Hn. left. reflexivity.
Qed.

(* lst_sum 缩放：Σ (a·f j) == a·Σ f *)
Lemma lst_sum_scale (T : list nat) (f : nat -> CRcarrier R) (a : CRcarrier R) :
  CReq R (lst_sum T (fun j => a * f j)) (a * lst_sum T f).
Proof.
  induction T as [| j T' IH].
  - cbn [lst_sum]. ring.
  - cbn [lst_sum]. rewrite IH. ring.
Qed.

(* lst_sum 常数：Σ (fun _ => a) == a·INR(|T|) *)
(* 辅助：INR 0 == 0 *)
Lemma INR0_eq :
  CReq R (INR 0) (CR_of_Q R (Qmake 0 1)).
Proof.
  unfold INR.
  apply (CR_of_Q_morph R (Z.of_nat 0 # 1) (0 # 1)).
  unfold Qeq. cbn. reflexivity.
Qed.

Lemma lst_sum_const (T : list nat) (a : CRcarrier R) :
  CReq R (lst_sum T (fun _ : nat => a)) (a * INR (length T)).
Proof.
  induction T as [| j T' IH].
  - cbn [lst_sum length]. rewrite INR0_eq. ring.
  - cbn [lst_sum length].
    rewrite IH. rewrite (CR_INR_S (length T')). ring.
Qed.

(* 平方和 ≥ 0 *)
Lemma lst_sqsum_nonneg (T : list nat) (e : nat -> CRcarrier R) :
  CRle R (CR_of_Q R (Qmake 0 1)) (lst_sqsum T e).
Proof.
  unfold lst_sqsum.
  apply lst_sum_nonneg.
  intro j. intro Hj.
  exact (CRsqr_nonneg (e j)).
Qed.

(* AM-GM 列表求和：2|a|·Σ_{j∈T}|e_j| ≤ |T|·a² + Σ_{j∈T} e_j²
   （CRabs_amgm 逐项 2|a||e_j| ≤ a²+e_j²，求和 + 常数项 = |T|a²） *)
Lemma lst_sum_amgm (T : list nat) (a : CRcarrier R) (e : nat -> CRcarrier R) :
  CRle R ((1 + 1) * CRabs R a * lst_abs_sum T e)
         (a * a * INR (length T) + lst_sqsum T e).
Proof.
  unfold lst_abs_sum, lst_sqsum.
  assert (Hl : CReq R ((1 + 1) * CRabs R a * lst_sum T (fun j => CRabs R (e j)))
                       (lst_sum T (fun j => (1 + 1) * (CRabs R a * CRabs R (e j))))).
  { assert (Hcomm : CReq R ((1 + 1) * CRabs R a * lst_sum T (fun j => CRabs R (e j)))
                            ((1 + 1) * (CRabs R a * lst_sum T (fun j => CRabs R (e j))))). { ring. }
    rewrite Hcomm.
    rewrite <- (lst_sum_scale T (fun j => CRabs R (e j)) (CRabs R a)).
    rewrite <- (lst_sum_scale T (fun j => CRabs R a * CRabs R (e j)) (1 + 1)).
    reflexivity. }
  rewrite Hl.
  clear Hl.
  apply (CRle_trans (R:=R)
    (lst_sum T (fun j => (1 + 1) * (CRabs R a * CRabs R (e j))))
    (lst_sum T (fun j => a * a + e j * e j))
    (a * a * INR (length T) + lst_sum T (fun j => e j * e j))).
  - apply lst_sum_le. intro j. intro Hj. exact (CRabs_amgm a (e j)).
  - induction T as [| k T'' IH2].
    + cbn [lst_sum length]. rewrite INR0_eq.
      assert (Hz : CReq R (a * a * CR_of_Q R (Qmake 0 1) + CR_of_Q R (Qmake 0 1))
                           (CR_of_Q R (Qmake 0 1))). { ring. }
      apply (proj1 Hz).
    + cbn [lst_sum length].
      apply (CRle_trans (R:=R)
        (lst_sum T'' (fun j => a * a + e j * e j) + (a * a + e k * e k))
        ((a * a * INR (length T'') + lst_sum T'' (fun j => e j * e j)) + (a * a + e k * e k))
        (a * a * INR (S (length T'')) + (lst_sum T'' (fun j => e j * e j) + e k * e k))).
      * apply (CRplus_le_compat (R:=R)
          (lst_sum T'' (fun j => a * a + e j * e j))
          (a * a * INR (length T'') + lst_sum T'' (fun j => e j * e j))
          (a * a + e k * e k) (a * a + e k * e k)).
        -- exact IH2.
        -- apply CRle_refl.
      * assert (Hr : CReq R
          ((a * a * INR (length T'') + lst_sum T'' (fun j => e j * e j)) + (a * a + e k * e k))
          (a * a * INR (S (length T'')) + (lst_sum T'' (fun j => e j * e j) + e k * e k))).
        { rewrite (CR_INR_S (length T'')). ring. }
        apply (proj2 Hr).
Qed.

(* ============ B. 范数平方展开 ============ *)

(* 标量范数：‖c·z‖² == c²·‖z‖² *)
Lemma scal_norm_sq (c : CRcarrier R) (z : CRComplex) :
  CReq R (CRnorm_sq (scal c z)) (c * c * CRnorm_sq z).
Proof.
  unfold CRnorm_sq, scal. cbn [cre cim]. ring.
Qed.

(* ‖lst_combo (j::T)‖² == ‖lst_combo T‖² + e_j²·‖u_j‖² + 2e_j·⟨lst_combo T, u_j⟩ *)
Lemma lst_combo_norm_sq_cons (j : nat) (T : list nat) (e : nat -> CRcarrier R) (u : nat -> CRComplex) :
  CReq R (CRnorm_sq (lst_combo (j :: T) e u))
         (CRnorm_sq (lst_combo T e u)
          + e j * e j * CRnorm_sq (u j)
          + (1 + 1) * e j * CRip (lst_combo T e u) (u j)).
Proof.
  cbn [lst_combo].
  unfold CRnorm_sq, CRip, scal, CRadd.
  cbn [cre cim].
  ring.
Qed.

(* ============ C. 列表三角 + 相干上界 ============ *)

(* 辅助：−x ≤ |x| *)
Lemma CRopp_abs_le (x : CRcarrier R) :
  CRle R (CRopp R x) (CRabs R x).
Proof.
  apply (CRle_trans (R:=R) (CRopp R x) (CRabs R (CRopp R x)) (CRabs R x)).
  - exact (CRle_abs_self (CRopp R x)).
  - apply (proj2 (CRabs_opp (R:=R) x)).
Qed.

(* 辅助：−(a·ip) ≤ |a||ip| ⟹ 0 ≤ 2a·ip + 2|a||ip| *)
Lemma zero_le_two_ip (a ip : CRcarrier R) :
  CRle R (CRopp R (a * ip)) (CRabs R a * CRabs R ip) ->
  CRle R (CR_of_Q R (Qmake 0 1))
         ((1 + 1) * (a * ip) + (1 + 1) * (CRabs R a * CRabs R ip)).
Proof.
  intros Hle.
  apply (CRplus_le_reg_l (R:=R) (CRopp R ((1 + 1) * (a * ip)))).
  assert (Hl1 : CReq R (CRopp R ((1 + 1) * (a * ip)) + CR_of_Q R (Qmake 0 1))
                       (CRopp R ((1 + 1) * (a * ip)))). { ring. }
  rewrite Hl1.
  assert (Hl2 : CReq R (CRopp R ((1 + 1) * (a * ip))
                         + ((1 + 1) * (a * ip) + (1 + 1) * (CRabs R a * CRabs R ip)))
                       ((1 + 1) * (CRabs R a * CRabs R ip))). { ring. }
  rewrite Hl2.
  (* 目标：−((1+1)(a·ip)) ≤ (1+1)(|a||ip|)；由 Hle 乘 (1+1) ≥ 0 *)
  assert (Hring : CReq R (CRopp R ((1 + 1) * (a * ip)))
                           ((1 + 1) * (CRopp R (a * ip)))). { ring. }
  rewrite Hring.
  apply (CRmult_le_compat_l (R:=R) (1 + 1) (CRopp R (a * ip)) (CRabs R a * CRabs R ip)).
  - exact CR0_le_two.
  - exact Hle.
Qed.

(* |⟨Σ_T e_k u_k, v⟩| ≤ Σ_T |e_k|·|⟨u_k,v⟩| *)
Lemma lst_combo_ip_abs_le_sum (T : list nat) (e : nat -> CRcarrier R) (u : nat -> CRComplex) (v : CRComplex) :
  CRle R (CRabs R (CRip (lst_combo T e u) v))
         (lst_sum T (fun j => CRabs R (e j) * CRabs R (CRip (u j) v))).
Proof.
  induction T as [| j T' IH].
  - cbn [lst_combo lst_sum].
    unfold CRip. cbn [cre cim].
    assert (Hz : CReq R (cre CRzero * cre v + cim CRzero * cim v) (CR_of_Q R (Qmake 0 1))).
    { unfold CRzero. cbn. ring. }
    rewrite Hz.
    rewrite (CRabs_right (R:=R) (CR_of_Q R (Qmake 0 1)) (CRle_refl (R:=R) (CR_of_Q R (Qmake 0 1)))).
    apply CRle_refl.
  - cbn [lst_combo].
    assert (Hlin : CReq R (CRip (CRadd (lst_combo T' e u) (scal (e j) (u j))) v)
                           (CRip (lst_combo T' e u) v + CRip (scal (e j) (u j)) v)).
    { unfold CRip, CRadd, scal. cbn [cre cim]. ring. }
    apply (CRle_trans (R:=R)
      (CRabs R (CRip (CRadd (lst_combo T' e u) (scal (e j) (u j))) v))
      (CRabs R (CRip (lst_combo T' e u) v) + CRabs R (CRip (scal (e j) (u j)) v))
      (lst_sum T' (fun j0 => CRabs R (e j0) * CRabs R (CRip (u j0) v))
       + CRabs R (e j) * CRabs R (CRip (u j) v))).
    + rewrite Hlin.
      exact (CRabs_triang (R:=R) (CRip (lst_combo T' e u) v) (CRip (scal (e j) (u j)) v)).
    + apply (CRplus_le_compat (R:=R)
        (CRabs R (CRip (lst_combo T' e u) v))
        (lst_sum T' (fun j0 => CRabs R (e j0) * CRabs R (CRip (u j0) v)))
        (CRabs R (CRip (scal (e j) (u j)) v))
        (CRabs R (e j) * CRabs R (CRip (u j) v))).
      * exact IH.
      * assert (Heq : CReq R (CRip (scal (e j) (u j)) v) (e j * CRip (u j) v)).
        { unfold CRip, scal. cbn [cre cim]. ring. }
        apply (CRle_trans (R:=R)
          (CRabs R (CRip (scal (e j) (u j)) v))
          (CRabs R (e j * CRip (u j) v))
          (CRabs R (e j) * CRabs R (CRip (u j) v))).
        -- apply (proj2 (CRabs_morph_prop R (CRip (scal (e j) (u j)) v) (e j * CRip (u j) v) Heq)).
        -- apply (proj2 (CRabs_mult (R:=R) (e j) (CRip (u j) v))).
Qed.

(* 相干上界（列表版）：∀k∈T: |⟨u_k,v⟩| ≤ μ ⟹ |⟨Σ_T e_k u_k, v⟩| ≤ μ·Σ_T |e_k| *)
Lemma lst_cross_abs_le (T : list nat) (e : nat -> CRcarrier R) (u : nat -> CRComplex)
  (v : CRComplex) (mu : CRcarrier R) :
  (CRle R (CR_of_Q R (Qmake 0 1)) mu) ->
  (forall j, In j T ->
    CRle R (CRabs R (CRip (u j) v)) mu) ->
  CRle R (CRabs R (CRip (lst_combo T e u) v))
         (mu * lst_abs_sum T e).
Proof.
  intros Hmu0 Hcoh.
  apply (CRle_trans (R:=R)
    (CRabs R (CRip (lst_combo T e u) v))
    (lst_sum T (fun j => CRabs R (e j) * CRabs R (CRip (u j) v)))
    (mu * lst_abs_sum T e)).
  - exact (lst_combo_ip_abs_le_sum T e u v).
  - unfold lst_abs_sum.
    apply (CRle_trans (R:=R)
      (lst_sum T (fun j => CRabs R (e j) * CRabs R (CRip (u j) v)))
      (lst_sum T (fun j => CRabs R (e j) * mu))
      (mu * lst_sum T (fun j => CRabs R (e j)))).
    + apply lst_sum_le. intro j. intro Hj.
      apply (CRmult_le_compat_l (R:=R) (CRabs R (e j))
        (CRabs R (CRip (u j) v)) mu).
      * exact (CRabs_pos (R:=R) (e j)).
      * exact (Hcoh j Hj).
    + assert (Hc : CReq R (lst_sum T (fun j => CRabs R (e j) * mu))
                           (lst_sum T (fun j => mu * CRabs R (e j)))).
      { apply lst_sum_morph. intro j. intro Hj.
        apply (CRmult_comm (R:=R) (CRabs R (e j)) mu). }
      rewrite Hc.
      apply (proj2 (lst_sum_scale T (fun j => CRabs R (e j)) mu)).
Qed.

(* 逐点 CReq ⟹ 组合 CReq_cplx *)
Lemma lst_combo_ext (T : list nat) (e f : nat -> CRcarrier R) (u : nat -> CRComplex) :
  (forall j, In j T -> CReq R (e j) (f j)) ->
  CReq_cplx (lst_combo T e u) (lst_combo T f u).
Proof.
  induction T as [| j T' IH]; intros Heq.
  - cbn [lst_combo].
    unfold CReq_cplx. split; split; apply CRle_refl.
  - cbn [lst_combo].
    assert (Hje : CReq R (e j) (f j)) by (exact (Heq j (or_introl Logic.eq_refl))).
    assert (Hjf : CReq R (f j) (e j)).
    { split; [exact (proj2 Hje) | exact (proj1 Hje)]. }
    assert (Hre : CReq R (e j * cre (u j)) (f j * cre (u j))).
    { apply (CRmult_morph R (e j) (f j) Hje (cre (u j)) (cre (u j))).
      reflexivity. }
    assert (Hrf : CReq R (f j * cre (u j)) (e j * cre (u j))).
    { apply (CRmult_morph R (f j) (e j) Hjf (cre (u j)) (cre (u j))).
      reflexivity. }
    assert (Hie : CReq R (e j * cim (u j)) (f j * cim (u j))).
    { apply (CRmult_morph R (e j) (f j) Hje (cim (u j)) (cim (u j))).
      reflexivity. }
    assert (Hif : CReq R (f j * cim (u j)) (e j * cim (u j))).
    { apply (CRmult_morph R (f j) (e j) Hjf (cim (u j)) (cim (u j))).
      reflexivity. }
    unfold CReq_cplx. split.
    + cbn [cre].
      split.
      * apply (CRplus_le_compat (R:=R)
          (cre (lst_combo T' f u)) (cre (lst_combo T' e u))
          (f j * cre (u j)) (e j * cre (u j))).
        -- exact (proj1 (proj1 (IH (fun j0 Hj0 => Heq j0 (or_intror Hj0))))).
        -- exact (proj2 Hrf).
      * apply (CRplus_le_compat (R:=R)
          (cre (lst_combo T' e u)) (cre (lst_combo T' f u))
          (e j * cre (u j)) (f j * cre (u j))).
        -- exact (proj2 (proj1 (IH (fun j0 Hj0 => Heq j0 (or_intror Hj0))))).
        -- exact (proj2 Hre).
    + cbn [cim].
      split.
      * apply (CRplus_le_compat (R:=R)
          (cim (lst_combo T' f u)) (cim (lst_combo T' e u))
          (f j * cim (u j)) (e j * cim (u j))).
        -- exact (proj1 (proj2 (IH (fun j0 Hj0 => Heq j0 (or_intror Hj0))))).
        -- exact (proj2 Hif).
      * apply (CRplus_le_compat (R:=R)
          (cim (lst_combo T' e u)) (cim (lst_combo T' f u))
          (e j * cim (u j)) (f j * cim (u j))).
        -- exact (proj2 (proj2 (IH (fun j0 Hj0 => Heq j0 (or_intror Hj0))))).
        -- exact (proj2 Hie).
Qed.

(* ============ E. 核心：列表 RIP 下界（常数 |T|−1） ============ *)

(* Σ_T e² ≤ ‖lst_combo T e u‖² + μ·(|T|−1)·Σ_T e²
   归纳：cons 步 = 范数展开（B）+ |⟨u_j,R⟩|≤μΣ'|e|（C）+ AM-GM 逐对（D）；
   链尾 n=0（T'=[]）与 n≥1 分情形（INR(n−1)+1 == INR n 需 n≥1）。 *)
Lemma lst_rip_lower (T : list nat) (e : nat -> CRcarrier R) (u : nat -> CRComplex) (mu : CRcarrier R) :
  NoDup T ->
  (CRle R (CR_of_Q R (Qmake 0 1)) mu) ->
  (forall j, In j T -> CReq R (CRnorm_sq (u j)) (CR_of_Q R (Qmake 1 1))) ->
  (forall i j, In i T -> In j T -> i <> j ->
    CRle R (CRabs R (CRip (u i) (u j))) mu) ->
  CRle R (lst_sqsum T e)
         (CRnorm_sq (lst_combo T e u) + mu * INR (length T - 1) * lst_sqsum T e).
Proof.
  induction T as [| j T' IH]; intros Hdup Hmu0 Hunit Hcoh.
  - (* T=[]：0 ≤ 0 + mu·INR 0·0 *)
    cbn [lst_sqsum lst_sum lst_combo length].
    unfold CRnorm_sq. cbn [cre cim].
    assert (Hz : CReq R (CR_of_Q R (Qmake 0 1))
                         (CR_of_Q R (Qmake 0 1) * CR_of_Q R (Qmake 0 1) + CR_of_Q R (Qmake 0 1) * CR_of_Q R (Qmake 0 1)
                          + mu * INR (0 - 1) * CR_of_Q R (Qmake 0 1))).
    { change (@INR R (0 - 1)) with (@INR R 0). rewrite INR0_eq. ring. }
    apply (proj2 Hz).
  - destruct T' as [| j' T''].
    + (* T = [j]（T'=[]）：0+a² ≤ ‖lst_combo [j]‖² + mu·INR 0·(0+a²)，且 ‖·‖² == a² *)
      cbn [lst_sqsum lst_sum length].
      assert (Hnorm : CReq R (CRnorm_sq (lst_combo (j :: []) e u)) (e j * e j)).
      { cbn [lst_combo]. unfold CRnorm_sq, CRadd, scal. cbn [cre cim].
        assert (Hring : CReq R
          ((CR_of_Q R (Qmake 0 1) + e j * cre (u j)) * (CR_of_Q R (Qmake 0 1) + e j * cre (u j))
           + (CR_of_Q R (Qmake 0 1) + e j * cim (u j)) * (CR_of_Q R (Qmake 0 1) + e j * cim (u j)))
          (e j * e j * (cre (u j) * cre (u j) + cim (u j) * cim (u j)))). { ring. }
        rewrite Hring.
        change (cre (u j) * cre (u j) + cim (u j) * cim (u j)) with (CRnorm_sq (u j)).
        rewrite (Hunit j (or_introl Logic.eq_refl)).
        ring. }
      assert (Hl0 : CReq R (CR_of_Q R (Qmake 0 1) + e j * e j) (e j * e j)).
      { ring. }
      apply (CRle_trans (R:=R) (CR_of_Q R (Qmake 0 1) + e j * e j)
        (e j * e j)
        (CRnorm_sq (lst_combo (j :: []) e u)
         + mu * INR (0 - 1) * (CR_of_Q R (Qmake 0 1) + e j * e j))).
      * rewrite Hl0. apply CRle_refl.
      * apply (CRle_trans (R:=R) (e j * e j)
          (CRnorm_sq (lst_combo (j :: []) e u))
          (CRnorm_sq (lst_combo (j :: []) e u)
           + mu * INR (0 - 1) * (CR_of_Q R (Qmake 0 1) + e j * e j))).
        -- apply (proj1 Hnorm).
        -- apply (Rplus_le_pos (R:=R) (CRnorm_sq (lst_combo (j :: []) e u))
             (mu * INR (0 - 1) * (CR_of_Q R (Qmake 0 1) + e j * e j))).
           assert (Hz : CReq R (CR_of_Q R (Qmake 0 1))
                                (mu * INR (0 - 1) * (CR_of_Q R (Qmake 0 1) + e j * e j))).
           { change (@INR R (0 - 1)) with (@INR R 0). rewrite INR0_eq. ring. }
           apply (proj2 Hz).
    + (* T = j :: j' :: T''：|(j' :: T'')| = S(length T'') ≥ 1 *)
      assert (Hnj : ~ In j (j' :: T'')) by (inversion Hdup; assumption).
      assert (Hdup' : NoDup (j' :: T'')) by (inversion Hdup; assumption).
      cbn [length].
      set (a := e j).
      set (S' := lst_sqsum (j' :: T'') e).
      set (R' := lst_combo (j' :: T'') e u).
      set (L1' := lst_abs_sum (j' :: T'') e).
      (* IH 截取到 (j' :: T'') *)
      assert (HIH : CRle R S' (CRnorm_sq R' + mu * INR (length (j' :: T'') - 1) * S')).
      { unfold S', R'.
        apply IH.
        - exact Hdup'.
        - exact Hmu0.
        - intros j0 Hj0. apply Hunit. right. exact Hj0.
        - intros i j0 Hi Hj0 Hne. apply Hcoh.
          + right. exact Hi.
          + right. exact Hj0.
          + exact Hne. }
      (* [2]：|⟨R', u_j⟩| ≤ mu·L1' *)
      assert (Hcross : CRle R (CRabs R (CRip R' (u j))) (mu * L1')).
      { unfold R', L1'.
        apply (lst_cross_abs_le (j' :: T'') e u (u j) mu Hmu0).
        intros k Hk. apply Hcoh.
        - right. exact Hk.
        - left. reflexivity.
        - intro Hkj. subst k. exact (Hnj Hk). }
      assert (Hcross2 : CRle R ((1 + 1) * CRabs R a * CRabs R (CRip R' (u j)))
                               ((1 + 1) * CRabs R a * (mu * L1'))).
      { apply (CRmult_le_compat_l (R:=R) ((1 + 1) * CRabs R a)
          (CRabs R (CRip R' (u j))) (mu * L1')).
        - apply CRmult_le_0_compat.
          + exact CR0_le_two.
          + apply CRabs_pos.
        - exact Hcross. }
      (* [3]：‖R'‖² + a² ≤ ‖lst_combo (j::(j' :: T''))‖² + 2|a|·|⟨R',u_j⟩| *)
      assert (H3 : CRle R (CRnorm_sq R' + a * a)
                   (CRnorm_sq (lst_combo (j :: j' :: T'') e u)
                    + (1 + 1) * CRabs R a * CRabs R (CRip R' (u j)))).
      { unfold R'.
        rewrite (lst_combo_norm_sq_cons j (j' :: T'') e u).
        rewrite (Hunit j (or_introl Logic.eq_refl)).
        (* 目标：‖·‖²+a² ≤ ‖·‖²+e_j²+2e_j⟨⟩+2|a||⟨⟩|
           链：X ≤ X+Y [Rplus_le_pos] == 目标 RHS [ring] *)
        apply (CRle_trans (R:=R) (CRnorm_sq (lst_combo (j' :: T'') e u) + a * a)
          (CRnorm_sq (lst_combo (j' :: T'') e u) + a * a
           + ((1 + 1) * (a * CRip (lst_combo (j' :: T'') e u) (u j))
              + (1 + 1) * (CRabs R a * CRabs R (CRip (lst_combo (j' :: T'') e u) (u j)))))
          (CRnorm_sq (lst_combo (j' :: T'') e u) + e j * e j * CR_of_Q R (Qmake 1 1)
           + (1 + 1) * e j * CRip (lst_combo (j' :: T'') e u) (u j)
           + (1 + 1) * CRabs R a * CRabs R (CRip (lst_combo (j' :: T'') e u) (u j)))).
        - apply (Rplus_le_pos (R:=R) (CRnorm_sq (lst_combo (j' :: T'') e u) + a * a)
            ((1 + 1) * (a * CRip (lst_combo (j' :: T'') e u) (u j))
             + (1 + 1) * (CRabs R a * CRabs R (CRip (lst_combo (j' :: T'') e u) (u j))))).
          apply (zero_le_two_ip a (CRip (lst_combo (j' :: T'') e u) (u j))).
          apply (CRle_trans (R:=R)
            (CRopp R (a * CRip (lst_combo (j' :: T'') e u) (u j)))
            (CRabs R (a * CRip (lst_combo (j' :: T'') e u) (u j)))
            (CRabs R a * CRabs R (CRip (lst_combo (j' :: T'') e u) (u j)))).
          * exact (CRopp_abs_le (a * CRip (lst_combo (j' :: T'') e u) (u j))).
          * apply (proj2 (CRabs_mult (R:=R) a (CRip (lst_combo (j' :: T'') e u) (u j)))).
        - assert (Hr : CReq R (CRnorm_sq (lst_combo (j' :: T'') e u) + a * a
                                + ((1 + 1) * (a * CRip (lst_combo (j' :: T'') e u) (u j))
                                   + (1 + 1) * (CRabs R a * CRabs R (CRip (lst_combo (j' :: T'') e u) (u j)))))
                              (CRnorm_sq (lst_combo (j' :: T'') e u) + e j * e j * CR_of_Q R (Qmake 1 1)
                               + (1 + 1) * e j * CRip (lst_combo (j' :: T'') e u) (u j)
                               + (1 + 1) * CRabs R a * CRabs R (CRip (lst_combo (j' :: T'') e u) (u j)))).
          { unfold a. ring. }
          apply (proj2 Hr). }
      (* [4]：2|a|·mu·L1' ≤ mu·(|T'|a² + S')（AM-GM 乘 mu） *)
      assert (H4 : CRle R (mu * ((1 + 1) * CRabs R a * lst_abs_sum (j' :: T'') e))
                           (mu * (a * a * INR (length (j' :: T'')) + S'))).
      { apply (CRmult_le_compat_l (R:=R) mu
          ((1 + 1) * CRabs R a * lst_abs_sum (j' :: T'') e)
          (a * a * INR (length (j' :: T'')) + lst_sqsum (j' :: T'') e)).
        - exact Hmu0.
        - unfold S'. exact (lst_sum_amgm (j' :: T'') a e). }
      (* 组装：M1 ≤ M2 ≤ M3 ≤ M4 == M5
         M1 := S'+a²；M2 := (‖R'‖²+a²)+mu·INR(n)·S'；
         M3 := (‖L‖²+2|a|muL1')+mu·INR(n)·S'；M4 := (‖L‖²+mu(|T'|a²+S'))+mu·INR(n)·S'；
         M5 := ‖L‖²+mu·INR(Sn)·(S'+a²)，n := length (j'::T'')−1，L := lst_combo (j::j'::T'') e u *)
      apply (CRle_trans (R:=R) (S' + a * a)
        ((CRnorm_sq R' + a * a) + mu * INR (length (j' :: T'') - 1) * S')
        (CRnorm_sq (lst_combo (j :: j' :: T'') e u) + mu * INR (length (j' :: T'')) * (S' + a * a))).
      - (* M1 ≤ M2：HIH 加 a² + ring 对齐 *)
        apply (CRle_trans (R:=R) (S' + a * a)
          ((CRnorm_sq R' + mu * INR (length (j' :: T'') - 1) * S') + a * a)
          ((CRnorm_sq R' + a * a) + mu * INR (length (j' :: T'') - 1) * S')).
        + apply (CRplus_le_compat_r (R:=R) (a * a)).
          exact HIH.
        + assert (Hc : CReq R
            ((CRnorm_sq R' + mu * INR (length (j' :: T'') - 1) * S') + a * a)
            ((CRnorm_sq R' + a * a) + mu * INR (length (j' :: T'') - 1) * S')). { ring. }
          apply (proj2 Hc).
      - (* M2 ≤ M5 *)
        apply (CRle_trans (R:=R)
          ((CRnorm_sq R' + a * a) + mu * INR (length (j' :: T'') - 1) * S')
          ((CRnorm_sq (lst_combo (j :: j' :: T'') e u) + (1 + 1) * CRabs R a * (mu * L1'))
           + mu * INR (length (j' :: T'') - 1) * S')
          (CRnorm_sq (lst_combo (j :: j' :: T'') e u) + mu * INR (length (j' :: T'')) * (S' + a * a))).
        + (* M2 ≤ M3：H3 + Hcross2 合成 Htmp，再 CRplus_le_compat_r *)
          assert (Htmp : CRle R (CRnorm_sq R' + a * a)
               (CRnorm_sq (lst_combo (j :: j' :: T'') e u)
                + (1 + 1) * CRabs R a * (mu * L1'))).
          { apply (CRle_trans (R:=R) (CRnorm_sq R' + a * a)
              (CRnorm_sq (lst_combo (j :: j' :: T'') e u) + (1 + 1) * CRabs R a * CRabs R (CRip R' (u j)))
              (CRnorm_sq (lst_combo (j :: j' :: T'') e u) + (1 + 1) * CRabs R a * (mu * L1'))).
            - exact H3.
            - apply (CRplus_le_compat_l (R:=R) (CRnorm_sq (lst_combo (j :: j' :: T'') e u))).
              exact Hcross2. }
          apply (CRplus_le_compat_r (R:=R) (mu * INR (length (j' :: T'') - 1) * S')).
          exact Htmp.
        + (* M3 ≤ M5：H4 + ring 组装（INR(|T'|−1)+1 == INR(|T'|)，|T'| ≥ 1） *)
          apply (CRle_trans (R:=R)
            ((CRnorm_sq (lst_combo (j :: j' :: T'') e u) + (1 + 1) * CRabs R a * (mu * L1'))
             + mu * INR (length (j' :: T'') - 1) * S')
            ((CRnorm_sq (lst_combo (j :: j' :: T'') e u) + mu * (a * a * INR (length (j' :: T'')) + S'))
             + mu * INR (length (j' :: T'') - 1) * S')
            (CRnorm_sq (lst_combo (j :: j' :: T'') e u) + mu * INR (length (j' :: T'')) * (S' + a * a))).
          * (* M3 ≤ M4：Hring 换序 + H4 *)
            assert (Hring : CReq R ((1 + 1) * CRabs R a * (mu * L1'))
                                     (mu * ((1 + 1) * CRabs R a * lst_abs_sum (j' :: T'') e))).
            { unfold L1'. ring. }
            rewrite Hring.
            apply (CRplus_le_compat_r (R:=R) (mu * INR (length (j' :: T'') - 1) * S')).
            apply (CRplus_le_compat_l (R:=R) (CRnorm_sq (lst_combo (j :: j' :: T'') e u))).
            exact H4.
          * (* M4 == M5：INR 恒等（subSS/subn0 证 subn）+ ring *)
            assert (Hsub : subn (length (j' :: T'')) 1 = length T'').
            { cbn [length].
              rewrite (subSS 0 (length T'')).
              apply subn0. }
            assert (Hlen : S (subn (length (j' :: T'')) 1) = length (j' :: T'')).
            { rewrite Hsub. reflexivity. }
            assert (Hinr : CReq R (INR (length (j' :: T''))) (INR (length (j' :: T'') - 1) + 1)).
            { assert (Hmid : CReq R (INR (S (subn (length (j' :: T'')) 1))) (INR (length (j' :: T'')))).
              { rewrite Hlen. reflexivity. }
              apply (CReq_trans (R := R) (INR (length (j' :: T''))) (INR (S (subn (length (j' :: T'')) 1))) (INR (subn (length (j' :: T'')) 1) + 1)).
              - apply (CReq_sym (R := R) (INR (S (subn (length (j' :: T'')) 1))) (INR (length (j' :: T'')))).
                exact Hmid.
              - exact (CR_INR_S (subn (length (j' :: T'')) 1)). }
            assert (Hfin : CReq R
              ((CRnorm_sq (lst_combo (j :: j' :: T'') e u) + mu * (a * a * INR (length (j' :: T'')) + S'))
               + mu * INR (length (j' :: T'') - 1) * S')
              (CRnorm_sq (lst_combo (j :: j' :: T'') e u) + mu * INR (length (j' :: T'')) * (S' + a * a))).
            { rewrite Hinr. ring. }
            exact (proj2 Hfin).
Qed.

(* ============ F. 差分线性 + 分量线性 + 零项吸收 ============ *)

(* lst_combo 实部线性：re (Σ_T e_j u_j) == Σ_T e_j·re(u_j) *)
Lemma lst_combo_re_lin (T : list nat) (e : nat -> CRcarrier R) (u : nat -> CRComplex) :
  CReq R (cre (lst_combo T e u)) (lst_sum T (fun j => e j * cre (u j))).
Proof.
  induction T as [| j T' IH].
  - cbn [lst_combo lst_sum]. reflexivity.
  - cbn [lst_combo lst_sum]. unfold CRadd, scal. cbn [cre].
    split.
    + apply (CRplus_le_compat (R:=R)
        (lst_sum T' (fun j => e j * cre (u j))) (cre (lst_combo T' e u))
        (e j * cre (u j)) (e j * cre (u j))).
      * exact (proj1 IH).
      * apply CRle_refl.
    + apply (CRplus_le_compat (R:=R)
        (cre (lst_combo T' e u)) (lst_sum T' (fun j => e j * cre (u j)))
        (e j * cre (u j)) (e j * cre (u j))).
      * exact (proj2 IH).
      * apply CRle_refl.
Qed.

(* lst_combo 虚部线性 *)
Lemma lst_combo_im_lin (T : list nat) (e : nat -> CRcarrier R) (u : nat -> CRComplex) :
  CReq R (cim (lst_combo T e u)) (lst_sum T (fun j => e j * cim (u j))).
Proof.
  induction T as [| j T' IH].
  - cbn [lst_combo lst_sum]. reflexivity.
  - cbn [lst_combo lst_sum]. unfold CRadd, scal. cbn [cim].
    split.
    + apply (CRplus_le_compat (R:=R)
        (lst_sum T' (fun j => e j * cim (u j))) (cim (lst_combo T' e u))
        (e j * cim (u j)) (e j * cim (u j))).
      * exact (proj1 IH).
      * apply CRle_refl.
    + apply (CRplus_le_compat (R:=R)
        (cim (lst_combo T' e u)) (lst_sum T' (fun j => e j * cim (u j)))
        (e j * cim (u j)) (e j * cim (u j))).
      * exact (proj2 IH).
      * apply CRle_refl.
Qed.

(* lst_sum 对差的线性：Σ (f j − g j) == Σ f − Σ g *)
Lemma lst_sum_sub_morph (T : list nat) (f g : nat -> CRcarrier R) :
  CReq R (lst_sum T (fun j => f j - g j)) (lst_sum T f - lst_sum T g).
Proof.
  induction T as [| j T' IH].
  - cbn [lst_sum]. unfold CRminus. ring.
  - cbn [lst_sum].
    rewrite IH. unfold CRminus. ring.
Qed.

(* lst_sum 对 ++ 分配：Σ_{A++B} == Σ_A + Σ_B *)
Lemma lst_sum_cat (A B : list nat) (f : nat -> CRcarrier R) :
  CReq R (lst_sum (A ++ B) f) (lst_sum A f + lst_sum B f).
Proof.
  induction A as [| j A' IH].
  - cbn [lst_sum]. change ([] ++ B) with B. ring.
  - cbn [lst_sum]. change ((j :: A') ++ B) with (j :: (A' ++ B)).
    cbn [lst_sum]. rewrite IH. ring.
Qed.

(* 辅助：NoDup_cons 投影（inversion 版，避免 ssr destruct 索引问题） *)
Lemma NoDup_cons_inv (x : nat) (l : list nat) :
  NoDup (x :: l) -> ~ In x l /\ NoDup l.
Proof.
  intro H. inversion H. split; assumption.
Qed.

(* cat 版 In 引理（mathcomp cat ≠ stdlib app，in_app_iff 不匹配） *)
Lemma In_cat_l (a : nat) (l1 l2 : list nat) :
  In a l1 -> In a (l1 ++ l2).
Proof.
  induction l1 as [| j l1' IH]; intro Ha.
  - exfalso. exact Ha.
  - destruct Ha as [Haj | Ha'].
    + left. exact Haj.
    + right. exact (IH Ha').
Qed.

Lemma In_cat_r (a : nat) (l1 l2 : list nat) :
  In a l2 -> In a (l1 ++ l2).
Proof.
  induction l1 as [| j l1' IH]; intro Ha.
  - exact Ha.
  - right. exact (IH Ha).
Qed.

Lemma In_app_or_cat (a : nat) (l1 l2 : list nat) :
  In a (l1 ++ l2) -> In a l1 \/ In a l2.
Proof.
  induction l1 as [| j l1' IH]; intro Ha.
  - right. exact Ha.
  - destruct Ha as [Haj | Ha'].
    + left. left. exact Haj.
    + destruct (IH Ha') as [Hl | Hr].
      * left. right. exact Hl.
      * right. exact Hr.
Qed.

(* 辅助：NoDup (A ++ [j] ++ B) ⟹ NoDup (A ++ B)（删中间元素保持无重复） *)
Lemma NoDup_app_remove_mid (A B : list nat) (j : nat) :
  NoDup (A ++ [j] ++ B) -> NoDup (A ++ B).
Proof.
  induction A as [| a A' IH].
  - intro H.
    change ([j] ++ B) with (j :: B) in H.
    exact (proj2 (NoDup_cons_inv j B H)).
  - intro H.
    change ((a :: A') ++ [j] ++ B) with (a :: (A' ++ [j] ++ B)) in H.
    destruct (NoDup_cons_inv a (A' ++ [j] ++ B) H) as [Hnotin Hnodup].
    apply NoDup_cons.
    + intro Ha.
      apply Hnotin.
      destruct (In_app_or_cat a A' B Ha) as [Ha' | Ha''].
      * apply (In_cat_l a A' ([j] ++ B)). exact Ha'.
      * apply (In_cat_r a A' ([j] ++ B)).
        apply (In_cat_r a [j] B). exact Ha''.
    + exact (IH Hnodup).
Qed.

(* 辅助：NoDup (A ++ [j] ++ B) ⟹ ¬In j (A ++ B)（j 只在中间出现一次） *)
Lemma NoDup_mid_notin (A B : list nat) (j : nat) :
  NoDup (A ++ [j] ++ B) -> ~ In j (A ++ B).
Proof.
  induction A as [| a A' IH].
  - intro H.
    change ([j] ++ B) with (j :: B) in H.
    exact (proj1 (NoDup_cons_inv j B H)).
  - intro H.
    change ((a :: A') ++ [j] ++ B) with (a :: (A' ++ [j] ++ B)) in H.
    destruct (NoDup_cons_inv a (A' ++ [j] ++ B) H) as [Hnotin Hnodup].
    intro Hj.
    destruct (In_app_or_cat j (a :: A') B Hj) as [Hja | Hjb].
    + destruct Hja as [Hja' | Hja''].
      * subst a. apply Hnotin.
        apply (In_cat_r j A' ([j] ++ B)).
        apply (In_cat_l j [j] B).
        left. reflexivity.
      * exfalso. exact (IH Hnodup (In_cat_l j A' B Hja'')).
    + exfalso. exact (IH Hnodup (In_cat_r j A' B Hjb)).
Qed.

(* lst_sum 限制：T1 ⊆ T（NoDup）且 f 在 T\T1 为零 ⟹ Σ_T f == Σ_{T1} f *)
Lemma lst_sum_restrict (T T1 : list nat) (f : nat -> CRcarrier R) :
  NoDup T -> NoDup T1 ->
  (forall j, In j T1 -> In j T) ->
  (forall j, In j T -> ~ In j T1 -> CReq R (f j) (CR_of_Q R (Qmake 0 1))) ->
  CReq R (lst_sum T f) (lst_sum T1 f).
Proof.
  revert T1.
  induction T as [| j T' IH]; intros T1 HdupT HdupT1 Hincl Hzero.
  - (* T=[]：T1=[] *)
    destruct T1 as [| j0 T1'].
    + reflexivity.
    + exfalso. apply (Hincl j0 (or_introl Logic.eq_refl)).
  - (* T = j::T' *)
    destruct (NoDup_cons_inv j T' HdupT) as [Hnj HdupT'].
    destruct (List.In_dec Nat.eq_dec j T1) as [Hj1 | Hj1n].
    + (* j ∈ T1：In_split ⟹ T1 = l1 ++ [j] ++ l2 *)
      destruct (In_split j T1 Hj1) as [l1 [l2 HT1]].
      assert (Hnodup_mid : NoDup (l1 ++ [j] ++ l2)).
      { rewrite HT1 in HdupT1. exact HdupT1. }
      assert (Hnotin : ~ In j (l1 ++ l2)) by (exact (NoDup_mid_notin l1 l2 j Hnodup_mid)).
      (* IH 于 T' 与 l1++l2 *)
      assert (HIH' : CReq R (lst_sum T' f) (lst_sum (l1 ++ l2) f)).
      { apply IH.
        - exact HdupT'.
        - exact (NoDup_app_remove_mid l1 l2 j Hnodup_mid).
        - (* l1++l2 ⊆ T' *)
          intros k Hk.
          assert (Hk1 : In k T1).
          { rewrite HT1.
            destruct (In_app_or_cat k l1 l2 Hk) as [Hk_l1 | Hk_l2].
            - apply (In_cat_l k l1 ([j] ++ l2)). exact Hk_l1.
            - apply (In_cat_r k l1 ([j] ++ l2)).
              apply (In_cat_r k [j] l2). exact Hk_l2. }
          assert (Hkt : In k (j :: T')) by (apply Hincl; exact Hk1).
          destruct Hkt as [Hkj | Hkt'].
          + subst k. exfalso. exact (Hnotin Hk).
          + exact Hkt'.
        - (* f 在 T'\(l1++l2) 零 *)
          intros k Hk Hkn.
          apply Hzero; [right; exact Hk |].
          intro Hk1.
          rewrite HT1 in Hk1.
          destruct (In_app_or_cat k l1 ([j] ++ l2) Hk1) as [Hk_l1 | Hk_rest].
          + apply Hkn. apply (In_cat_l k l1 l2). exact Hk_l1.
          + destruct (In_app_or_cat k [j] l2 Hk_rest) as [Hk_j | Hk_l2].
            * destruct Hk_j as [Hkj | Hknil].
              -- subst k. exact (Hnj Hk).
              -- exfalso. exact Hknil.
            * apply Hkn. apply (In_cat_r k l1 l2). exact Hk_l2. }
      (* 组装：lst_sum (j::T') f == lst_sum T1 f *)
      assert (Htarget : CReq R (lst_sum (j :: T') f) (lst_sum T1 f)).
      { cbn [lst_sum].
        rewrite HT1.
        rewrite (lst_sum_cat l1 ([j] ++ l2) f).
        rewrite (lst_sum_cat [j] l2 f).
        cbn [lst_sum].
        rewrite HIH'.
        rewrite (lst_sum_cat l1 l2 f).
        ring. }
      exact Htarget.
    + (* j ∉ T1：f j == 0，删头部 *)
      cbn [lst_sum].
      assert (Hfj : CReq R (f j) (CR_of_Q R (Qmake 0 1))).
      { apply Hzero. left. reflexivity. exact Hj1n. }
      rewrite Hfj.
      assert (H0 : CReq R (lst_sum T' f + CR_of_Q R (Qmake 0 1)) (lst_sum T' f)). { ring. }
      apply (CReq_trans (R := R) (lst_sum T' f + CR_of_Q R (Qmake 0 1)) (lst_sum T' f) (lst_sum T1 f)).
      * exact H0.
      * apply IH.
        -- exact HdupT'.
        -- exact HdupT1.
        -- (* T1 ⊆ T' *)
           intros k Hk.
           assert (Hkt : In k (j :: T')) by (apply Hincl; exact Hk).
           destruct Hkt as [Hkj | Hkt'].
           ++ subst k. exfalso. exact (Hj1n Hk).
           ++ exact Hkt'.
        -- (* f 在 T'\T1 零 *)
           intros k Hk Hkn.
           apply Hzero; [right; exact Hk | exact Hkn].
Qed.

(* 辅助：非负逐项 ⟹ 每项 ≤ 和（列表版） *)
Lemma lst_sum_nonneg_term_le (T : list nat) (f : nat -> CRcarrier R) :
  (forall k, In k T -> CRle R (CR_of_Q R (Qmake 0 1)) (f k)) ->
  forall j, In j T -> CRle R (f j) (lst_sum T f).
Proof.
  induction T as [| k T' IH]; intros Hn j Hj.
  - exfalso. exact Hj.
  - cbn [lst_sum].
    destruct Hj as [Hjk | HjT'].
    + subst j.
      apply (CRle_trans (R:=R) (f k) (f k + lst_sum T' f) (lst_sum T' f + f k)).
      * apply (Rplus_le_pos (R:=R) (f k) (lst_sum T' f)).
        apply (lst_sum_nonneg T' f).
        intros j0 Hj0. apply Hn. right. exact Hj0.
      * assert (Hc : CReq R (f k + lst_sum T' f) (lst_sum T' f + f k)). { ring. }
        apply (proj2 Hc).
    + apply (CRle_trans (R:=R) (f j) (lst_sum T' f) (lst_sum T' f + f k)).
      * exact (IH (fun j0 Hj0 => Hn j0 (or_intror Hj0)) j HjT').
      * apply (Rplus_le_pos (R:=R) (lst_sum T' f) (f k)).
        apply Hn. left. reflexivity.
Qed.

(* 平方和零 ⟹ 逐项零（列表版） *)
Lemma lst_sqsum_zero_terms (T : list nat) (e : nat -> CRcarrier R)
  (Hsq : CReq R (lst_sqsum T e) (CR_of_Q R (Qmake 0 1))) :
  forall j, In j T -> CReq R (e j) (CR_of_Q R (Qmake 0 1)).
Proof.
  intros j Hj.
  assert (Hsum_le0 : CRle R (lst_sqsum T e) (CR_of_Q R (Qmake 0 1))).
  { exact (proj2 Hsq). }
  assert (Hj_le : CRle R (e j * e j) (lst_sqsum T e)).
  { unfold lst_sqsum.
    apply (lst_sum_nonneg_term_le T (fun k => e k * e k)).
    - intro k. intro Hk. exact (CRsqr_nonneg (e k)).
    - exact Hj. }
  assert (Hj_le0 : CRle R (e j * e j) (CR_of_Q R (Qmake 0 1))).
  { apply (CRle_trans (R:=R) (e j * e j) (lst_sqsum T e) (CR_of_Q R (Qmake 0 1))).
    - exact Hj_le.
    - exact Hsum_le0. }
  apply (CRsqr_eq_zero (e j)).
  split; [exact (CRsqr_nonneg (e j)) | exact Hj_le0].
Qed.

(* ============ G. undup 合并两支撑 ============ *)

(* 列表去重（保序） *)
Fixpoint list_undup (l : list nat) : list nat :=
  match l with
  | nil => nil
  | j :: t => if List.In_dec Nat.eq_dec j (list_undup t) then list_undup t else j :: list_undup t
  end.

Lemma list_undup_NoDup (l : list nat) :
  NoDup (list_undup l).
Proof.
  induction l as [| j t IH].
  - apply NoDup_nil.
  - cbn [list_undup].
    destruct (List.In_dec Nat.eq_dec j (list_undup t)) as [Hj | Hjn].
    + exact IH.
    + apply NoDup_cons. exact Hjn. exact IH.
Qed.

Lemma list_undup_In (l : list nat) (j : nat) :
  In j l -> In j (list_undup l).
Proof.
  induction l as [| k t IH]; intro Hj.
  - exfalso. exact Hj.
  - destruct Hj as [Hjk | Hjt].
    + subst k.
      change (list_undup (j :: t)) with
        (if List.In_dec Nat.eq_dec j (list_undup t) then list_undup t else j :: list_undup t).
      destruct (List.In_dec Nat.eq_dec j (list_undup t)) as [Hj' | Hjn'].
      * cbn [is_left]. exact Hj'.
      * cbn [is_left]. left. reflexivity.
    + change (list_undup (k :: t)) with
        (if List.In_dec Nat.eq_dec k (list_undup t) then list_undup t else k :: list_undup t).
      destruct (List.In_dec Nat.eq_dec k (list_undup t)) as [Hk' | Hkn'].
      * cbn [is_left]. exact (IH Hjt).
      * cbn [is_left]. right. exact (IH Hjt).
Qed.

Lemma list_undup_inv (l : list nat) (j : nat) :
  In j (list_undup l) -> In j l.
Proof.
  induction l as [| k t IH]; intro Hj.
  - exfalso. exact Hj.
  - change (list_undup (k :: t)) with
      (if List.In_dec Nat.eq_dec k (list_undup t) then list_undup t else k :: list_undup t) in Hj.
    destruct (List.In_dec Nat.eq_dec k (list_undup t)) as [Hk | Hkn].
    + cbn [is_left]. right. exact (IH Hj).
    + cbn [is_left]. destruct Hj as [Hjk | Hjt'].
      * left. exact Hjk.
      * right. exact (IH Hjt').
Qed.

Lemma list_undup_size_le (l : list nat) :
  leq (length (list_undup l)) (length l).
Proof.
  induction l as [| j t IH].
  - apply leqnn.
  - change (list_undup (j :: t)) with
      (if List.In_dec Nat.eq_dec j (list_undup t) then list_undup t else j :: list_undup t).
    destruct (List.In_dec Nat.eq_dec j (list_undup t)) as [Hj | Hjn].
    + cbn [is_left]. cbn [length].
      apply (leq_trans IH (leqnSn (length t))).
    + cbn [is_left]. cbn [length].
      rewrite (leq_add2l 1 (length (list_undup t)) (length t)).
      exact IH.
Qed.

Lemma length_cat (A B : list nat) :
  length (A ++ B) = (length A + length B)%N.
Proof.
  induction A as [| j A' IH].
  - change ([] ++ B) with B. cbn [length]. reflexivity.
  - change ((j :: A') ++ B) with (j :: (A' ++ B)).
    cbn [length].
    rewrite IH.
    reflexivity.
Qed.

(* ============ H. ★ 主定理：相干字典不确定原理（唯一性正形式） ============ *)

(* 若字典 {u_j}（单位范数、相干 ≤ μ）上同一信号 x 有两个稀疏表示
     x = Σ_{j∈T1} c_j·u_j == Σ_{j∈T2} d_j·u_j
   （c 在 T1 外为零、d 在 T2 外为零，T1/T2 无重复），且 μ·(|T1|+|T2|−1) < 1，
   则 ∀j: c_j == d_j（表示唯一——Donoho-Stark 不确定原理的构造性正形式）。 *)
Theorem CRuncertainty_principle (T1 T2 : list nat) (c d : nat -> CRcarrier R)
  (u : nat -> CRComplex) (mu : CRcarrier R)
  (Hmu0 : CRle R (CR_of_Q R (Qmake 0 1)) mu)
  (Hdup1 : NoDup T1) (Hdup2 : NoDup T2)
  (Hunit : forall j, In j T1 \/ In j T2 -> CReq R (CRnorm_sq (u j)) (CR_of_Q R (Qmake 1 1)))
  (Hcoh : forall i j, In i T1 \/ In i T2 -> In j T1 \/ In j T2 -> i <> j ->
    CRle R (CRabs R (CRip (u i) (u j))) mu)
  (Hrep : CReq_cplx (lst_combo T1 c u) (lst_combo T2 d u))
  (Hc0 : forall j, ~ In j T1 -> CReq R (c j) (CR_of_Q R (Qmake 0 1)))
  (Hd0 : forall j, ~ In j T2 -> CReq R (d j) (CR_of_Q R (Qmake 0 1)))
  (Hmu1 : CRlt R (mu * INR (length T1 + length T2 - 1)) (CR_of_Q R (Qmake 1 1))) :
  forall j, CReq R (c j) (d j).
Proof.
  (* T := undup(T1++T2)（覆盖两支撑） *)
  set (T := list_undup (T1 ++ T2)).
  assert (T_dup : NoDup T) by (unfold T; exact (list_undup_NoDup (T1 ++ T2))).
  assert (T_cov1 : forall j, In j T1 -> In j T).
  { intros j Hj. unfold T. apply (list_undup_In (T1 ++ T2) j). apply (In_cat_l j T1 T2). exact Hj. }
  assert (T_cov2 : forall j, In j T2 -> In j T).
  { intros j Hj. unfold T. apply (list_undup_In (T1 ++ T2) j). apply (In_cat_r j T1 T2). exact Hj. }
  assert (T_inv : forall j, In j T -> In j T1 \/ In j T2).
  { intros j Hj. unfold T in Hj.
    destruct (In_app_or_cat j T1 T2 (list_undup_inv (T1 ++ T2) j Hj)) as [Hj1 | Hj2].
    - left. exact Hj1.
    - right. exact Hj2. }
  assert (t_le : leq (length T) ((length T1 + length T2)%N)).
  { unfold T. apply (leq_trans (list_undup_size_le (T1 ++ T2))).
    rewrite (length_cat T1 T2). apply leqnn. }
  (* HunitT / HcohT 截取到 T *)
  assert (HunitT : forall j, In j T -> CReq R (CRnorm_sq (u j)) (CR_of_Q R (Qmake 1 1))).
  { intros j Hj. apply Hunit. exact (T_inv j Hj). }
  assert (HcohT : forall i j, In i T -> In j T -> i <> j ->
    CRle R (CRabs R (CRip (u i) (u j))) mu).
  { intros i j Hi Hj Hne. apply Hcoh.
    - exact (T_inv i Hi).
    - exact (T_inv j Hj).
    - exact Hne. }
  (* 分 t=0 / t≥1：Hmu1'（mu·INR(t−1) < 1） *)
  assert (Hmu1' : CRlt R (mu * INR (length T - 1)) (CR_of_Q R (Qmake 1 1))).
  { destruct (Nat.eq_dec (length T) 0) as [Ht0 | Htne].
    - (* t=0：mu·INR 0 == 0 < 1 *)
      rewrite Ht0. change (@INR R (0 - 1)) with (@INR R 0).
      rewrite INR0_eq.
      assert (Hz : CReq R (mu * CR_of_Q R (Qmake 0 1)) (CR_of_Q R (Qmake 0 1))). { ring. }
      rewrite Hz. exact (CRzero_lt_one R).
    - (* t ≥ 1：t−1 ≤ L−1 ⟹ INR ⟹ mu· ⟹ < 1 *)
      assert (Hsuble : leq ((length T - 1)%N) ((length T1 + length T2 - 1)%N)).
      { exact (@leq_sub (length T) ((length T1 + length T2)%N) 1 1 t_le (leqnn 1)). }
      apply (CRle_lt_trans (R:=R)
        (mu * INR (length T - 1))
        (mu * INR (length T1 + length T2 - 1))
        (CR_of_Q R (Qmake 1 1))).
      * apply (CRmult_le_compat_l (R:=R) mu
          (INR (length T - 1)) (INR (length T1 + length T2 - 1))).
        -- exact Hmu0.
        -- apply (CRle_INR ((length T - 1)%N) ((length T1 + length T2 - 1)%N)).
           apply/leP. exact Hsuble.
      * exact Hmu1. }
  (* 步骤 6：cre (lst_combo T (c−d) u) == 0 *)
  assert (Hzre : CReq R (cre (lst_combo T (fun j => c j - d j) u)) (CR_of_Q R (Qmake 0 1))).
  { rewrite (lst_combo_re_lin T (fun j => c j - d j) u).
    (* lst_sum T ((c−d)·re(u)) == lst_sum T (c·re(u)) − lst_sum T (d·re(u)) *)
    assert (Hsub : CReq R (lst_sum T (fun j => (c j - d j) * cre (u j)))
                           (lst_sum T (fun j => c j * cre (u j)) - lst_sum T (fun j => d j * cre (u j)))).
    { apply (CReq_trans (R := R)
        (lst_sum T (fun j => (c j - d j) * cre (u j)))
        (lst_sum T (fun j => c j * cre (u j) - d j * cre (u j)))
        (lst_sum T (fun j => c j * cre (u j)) - lst_sum T (fun j => d j * cre (u j)))).
      - apply lst_sum_morph. intro j. intro Hj. unfold CRminus. ring.
      - exact (lst_sum_sub_morph T (fun j => c j * cre (u j)) (fun j => d j * cre (u j))). }
    rewrite Hsub.
    (* restrict ×2：Σ_T c·re == Σ_{T1} c·re；Σ_T d·re == Σ_{T2} d·re *)
    assert (Hr1 : CReq R (lst_sum T (fun j => c j * cre (u j)))
                          (lst_sum T1 (fun j => c j * cre (u j)))).
    { apply (lst_sum_restrict T T1 (fun j => c j * cre (u j))).
      - exact T_dup.
      - exact Hdup1.
      - intros j Hj. apply T_cov1. exact Hj.
      - intros j Hj Hjn.
        rewrite (Hc0 j Hjn). ring. }
    assert (Hr2 : CReq R (lst_sum T (fun j => d j * cre (u j)))
                          (lst_sum T2 (fun j => d j * cre (u j)))).
    { apply (lst_sum_restrict T T2 (fun j => d j * cre (u j))).
      - exact T_dup.
      - exact Hdup2.
      - intros j Hj. apply T_cov2. exact Hj.
      - intros j Hj Hjn.
        rewrite (Hd0 j Hjn). ring. }
    rewrite Hr1 Hr2.
    (* Σ_{T1} c·re − Σ_{T2} d·re == 0：由 Hrep 实部 + re_lin *)
    assert (Hrep_re : CReq R (lst_sum T1 (fun j => c j * cre (u j)))
                              (lst_sum T2 (fun j => d j * cre (u j)))).
    { apply (CReq_trans (R := R)
        (lst_sum T1 (fun j => c j * cre (u j)))
        (cre (lst_combo T1 c u))
        (lst_sum T2 (fun j => d j * cre (u j)))).
      - apply (CReq_sym (R := R) (cre (lst_combo T1 c u)) (lst_sum T1 (fun j => c j * cre (u j)))).
        exact (lst_combo_re_lin T1 c u).
      - apply (CReq_trans (R := R)
          (cre (lst_combo T1 c u)) (cre (lst_combo T2 d u))
          (lst_sum T2 (fun j => d j * cre (u j)))).
        + exact (proj1 Hrep).
        + exact (lst_combo_re_lin T2 d u). }
    rewrite Hrep_re. unfold CRminus. ring. }
  (* 同 cim *)
  assert (Hzim : CReq R (cim (lst_combo T (fun j => c j - d j) u)) (CR_of_Q R (Qmake 0 1))).
  { rewrite (lst_combo_im_lin T (fun j => c j - d j) u).
    assert (Hsub : CReq R (lst_sum T (fun j => (c j - d j) * cim (u j)))
                           (lst_sum T (fun j => c j * cim (u j)) - lst_sum T (fun j => d j * cim (u j)))).
    { apply (CReq_trans (R := R)
        (lst_sum T (fun j => (c j - d j) * cim (u j)))
        (lst_sum T (fun j => c j * cim (u j) - d j * cim (u j)))
        (lst_sum T (fun j => c j * cim (u j)) - lst_sum T (fun j => d j * cim (u j)))).
      - apply lst_sum_morph. intro j. intro Hj. unfold CRminus. ring.
      - exact (lst_sum_sub_morph T (fun j => c j * cim (u j)) (fun j => d j * cim (u j))). }
    rewrite Hsub.
    assert (Hr1 : CReq R (lst_sum T (fun j => c j * cim (u j)))
                          (lst_sum T1 (fun j => c j * cim (u j)))).
    { apply (lst_sum_restrict T T1 (fun j => c j * cim (u j))).
      - exact T_dup.
      - exact Hdup1.
      - intros j Hj. apply T_cov1. exact Hj.
      - intros j Hj Hjn.
        rewrite (Hc0 j Hjn). ring. }
    assert (Hr2 : CReq R (lst_sum T (fun j => d j * cim (u j)))
                          (lst_sum T2 (fun j => d j * cim (u j)))).
    { apply (lst_sum_restrict T T2 (fun j => d j * cim (u j))).
      - exact T_dup.
      - exact Hdup2.
      - intros j Hj. apply T_cov2. exact Hj.
      - intros j Hj Hjn.
        rewrite (Hd0 j Hjn). ring. }
    rewrite Hr1 Hr2.
    assert (Hrep_im : CReq R (lst_sum T1 (fun j => c j * cim (u j)))
                              (lst_sum T2 (fun j => d j * cim (u j)))).
    { apply (CReq_trans (R := R)
        (lst_sum T1 (fun j => c j * cim (u j)))
        (cim (lst_combo T1 c u))
        (lst_sum T2 (fun j => d j * cim (u j)))).
      - apply (CReq_sym (R := R) (cim (lst_combo T1 c u)) (lst_sum T1 (fun j => c j * cim (u j)))).
        exact (lst_combo_im_lin T1 c u).
      - apply (CReq_trans (R := R)
          (cim (lst_combo T1 c u)) (cim (lst_combo T2 d u))
          (lst_sum T2 (fun j => d j * cim (u j)))).
        + exact (proj2 Hrep).
        + exact (lst_combo_im_lin T2 d u). }
    rewrite Hrep_im. unfold CRminus. ring. }
  (* 范数平方零 *)
  assert (Hnorm0 : CReq R (CRnorm_sq (lst_combo T (fun j => c j - d j) u)) (CR_of_Q R (Qmake 0 1))).
  { unfold CRnorm_sq.
    rewrite Hzre Hzim. ring. }
  (* lst_rip_lower + 范数零 ⟹ lst_sqsum ≤ mu(t−1)·lst_sqsum *)
  assert (Hrip := lst_rip_lower T (fun j => c j - d j) u mu T_dup Hmu0 HunitT HcohT).
  rewrite Hnorm0 in Hrip.
  assert (Hsq_le : CRle R (lst_sqsum T (fun j => c j - d j))
                          (mu * INR (length T - 1) * lst_sqsum T (fun j => c j - d j))).
  { apply (CRle_trans (R:=R) (lst_sqsum T (fun j => c j - d j))
      (CR_of_Q R (Qmake 0 1) + mu * INR (length T - 1) * lst_sqsum T (fun j => c j - d j))
      (mu * INR (length T - 1) * lst_sqsum T (fun j => c j - d j))).
    - exact Hrip.
    - assert (Hc : CReq R (CR_of_Q R (Qmake 0 1) + mu * INR (length T - 1) * lst_sqsum T (fun j => c j - d j))
                          (mu * INR (length T - 1) * lst_sqsum T (fun j => c j - d j))). { ring. }
      apply (proj2 Hc). }
  (* 收缩：lst_sqsum ≤ 0 ⟹ == 0 ⟹ 逐项零 *)
  assert (Hsq_le0 : CRle R (lst_sqsum T (fun j => c j - d j)) (CR_of_Q R (Qmake 0 1))).
  { apply (CRle_scaled_le_zero (lst_sqsum T (fun j => c j - d j)) (mu * INR (length T - 1))).
    - exact Hsq_le.
    - exact Hmu1'. }
  assert (Hsq0 : CReq R (lst_sqsum T (fun j => c j - d j)) (CR_of_Q R (Qmake 0 1))).
  { split.
    - exact (lst_sqsum_nonneg T (fun j => c j - d j)).
    - exact Hsq_le0. }
  (* 结论：∀j *)
  intro j.
  destruct (List.In_dec Nat.eq_dec j T) as [HjT | HjnT].
  - (* j ∈ T：e j == 0 ⟹ c j == d j *)
    assert (Hej : CReq R (c j - d j) (CR_of_Q R (Qmake 0 1))).
    { exact (lst_sqsum_zero_terms T (fun j => c j - d j) Hsq0 j HjT). }
    apply (CReq_trans (R := R) (c j) ((c j - d j) + d j) (d j)).
    + unfold CRminus. ring.
    + rewrite Hej. unfold CRminus. ring.
  - (* j ∉ T：j∉T1 且 j∉T2 ⟹ c j == 0 == d j *)
    assert (Hj1n : ~ In j T1).
    { intro Hj1. apply HjnT. apply T_cov1. exact Hj1. }
    assert (Hj2n : ~ In j T2).
    { intro Hj2. apply HjnT. apply T_cov2. exact Hj2. }
    apply (CReq_trans (R := R) (c j) (CR_of_Q R (Qmake 0 1)) (d j)).
    + exact (Hc0 j Hj1n).
    + apply (CReq_sym (R := R) (d j) (CR_of_Q R (Qmake 0 1))).
      exact (Hd0 j Hj2n).
Qed.

End F5Uncertainty.
