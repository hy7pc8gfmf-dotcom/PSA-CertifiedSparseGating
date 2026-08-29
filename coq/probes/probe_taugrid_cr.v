(* ============================================================
   CS-4 构造性孪生：probe_taugrid_cr.v（z 区构造性轨道，2026-08-28）
   主线：z/probe_taugrid.v（Stdlib R 版，17 Qed）——本文件为其
   "只减经典依赖"平行实现（构造性轨道政策：不回灌主线）。

   纪律（承 ca_rip_cr.v）：
     - 数学对象在 Set 层构造（CRcarrier R：窗口和/债值/行和/kept-pruned 划分）
     - ★严格序 CRlt 本身是 Set 值（ConstructiveReals.v:88——柯西实数在
       CRlt 证明中存储信息，供 Set 层算法使用）：覆盖债的界定定理以
       **信息性形式 CRlt R 0 d * CRlt R d 1**（Set 值 prod，证明项可提取）
       陈述——这是"序尽量放 Set"的库内原生落点
     - ≤（CRle := CRlt y x -> False）与相等（CReq := CRle /\ CRle）
       不可判定化（bool 化 ⟹ LPO），保持 Prop——数学边界非风格选择
     - 存在量词一律 sigT（cr_debt_witness——谓词 Set 值时 sig 非法，
       sigT 被类型系统强制）
     - 序判定下放 Q 层：债值经覆盖率引理 CReq 于有理数，Qlt 判定
       （Prop 层 Z <，lia 收口）经 CR_of_Q_lt 提升为带数据的 CRlt 项，
       沿 CReq 的搬运用 CRlt_proper（respectful CReq ==> iffT，信息性双向）
     - 零经典实数公理；只用抽象接口 {R : ConstructiveReals}
     - 禁 vm_compute/trivial 封口；恒等式 ring/lia 代数收口
     - Q 分母一律 Pos.of_succ_nat（Qden 是 positive 类型，Z.of_nat 非法）；
       Pos↔Z 桥用定义性引理 zpos_of_succ + cbn [Qnum QDen] 定向归约
       （禁 simpl——会把 Z.of_nat (S x) 拆成不同原子破坏 ring/lia）

   数学内容（与主线 TA0–TA4/CA5 对应，接口化）：
     接口：抽象归一梯子 u（Set 层）+ Hu_norm（‖u n k‖² == 1/n，k<n）
           + Hu_tail（u n k == 0，k≥n）——cos/复指数/√n 构造性未实现
           （M2E 只到 sin∈[0,2]），接口与主线 psi_norm_sq_pt 数学一致，
           trig 未来由 M2E 扩展 plug-in，接口不变。
     C-TA1 支撑分类 / C-TA2 覆盖率（窗 [0,T] 能量 == (T+1)/n）/
     C-TA2' ★覆盖债（信息性：0 < debt < 1 为 Set 值 CRlt 对 + sigT 见证）/
     C-TA3 行和单调（CRle，上界证书无信息内容故留 Prop）/
     C-TA4 稀疏化保 C-比（纯 nat，与主线同款）/ C-CA5 三连最优性合成。
   依赖：ConstructiveReals + ca_rip_cr（CRComplex/CRnorm_sq/_nonneg，
   已 Closed）+ ConstructiveRcomplete（CRealConstructive 柯西实例，
   CRlt 信息性——提取目标；DRealConstructive 的 CRlt ≡ Rlt 被
   经典公理阻断，不用于信息性提取）。
   提取：taugrid_cr.ml（窗口和/债值/行和/划分——Set 层可执行）。
   审计：Print Assumptions 尾部。
   ============================================================ *)
From Stdlib Require Import ConstructiveReals.
From Stdlib Require Import QArith.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Arith.
From Stdlib Require Import List.
Import ListNotations.
Require Import ca_rip_cr.

(* E138①：Notation 注册（8 项，恢复 Stdlib nat 记号——防 mathcomp 污染，
   合并版双环境兼容硬规则 9） *)
Notation "a + b" := (Nat.add a b) (at level 50, left associativity) : nat_scope.
Notation "a - b" := (Nat.sub a b) (at level 50, left associativity) : nat_scope.
Notation "a * b" := (Nat.mul a b) (at level 40, left associativity) : nat_scope.
Notation "a <= b" := (Nat.le a b) (at level 70, no associativity) : nat_scope.
Notation "a < b" := (Nat.lt a b) (at level 70, no associativity) : nat_scope.
Notation "a >= b" := (Nat.le b a) (at level 70, no associativity) : nat_scope.
Notation "a > b" := (Nat.lt b a) (at level 70, no associativity) : nat_scope.

Unset Implicit Arguments.
Local Open Scope ConstructiveReals.

(* ---------- Q 分母桥（定义性——Z.of_nat (S n) ≡ Zpos (Pos.of_succ_nat n)） ---------- *)
Lemma zpos_of_succ (n : nat) :
  Z.pos (Pos.of_succ_nat n) = Z.of_nat (S n).
Proof. destruct n; reflexivity. Qed.

Section TauGridCR.

Context {R : ConstructiveReals}.

(* ---------- 接口：抽象归一梯子（Set 层数据 + Prop 层序/等） ---------- *)
Variable u : nat -> nat -> @CRComplex R.
Hypothesis Hu_norm : forall n k : nat, (k < n)%nat ->
  CRnorm_sq (u n k) == CR_of_Q R (Qmake 1 (Pos.of_succ_nat n)).
Hypothesis Hu_tail : forall n k : nat, (n <= k)%nat ->
  CReq_cplx (u n k) CRzero.

(* ---------- C-TA1：支撑分类 ---------- *)
Lemma c_ta1_support (n T k : nat) :
  (n <= T)%nat -> (T <= k)%nat -> CReq_cplx (u n k) CRzero.
Proof.
  intros HnT Htk. apply Hu_tail. lia.
Qed.

(* ---------- Set 层窗口和（可提取主对象） ---------- *)
Fixpoint cr_win_sum (f : nat -> CRcarrier R) (T : nat) : CRcarrier R :=
  match T with
  | O => f 0%nat
  | S i => cr_win_sum f i + f (S i)
  end.

(* Q 层关键恒等式（E114 显式化：ring 代数收口，非计算反射） *)
Definition qwin_aux (T n : nat) : Q :=
  Qmake (Z.of_nat (S T)) (Pos.of_succ_nat n).

Lemma qwin_succ (T n : nat) :
  Qeq (Qplus (qwin_aux T n) (Qmake 1 (Pos.of_succ_nat n)))
      (qwin_aux (S T) n).
Proof.
  unfold Qeq, Qplus, qwin_aux.
  rewrite !Nat2Z.inj_succ.
  cbn [Qnum Qden]. nia.
Qed.

(* ---------- C-TA2：覆盖率（★窗 [0,T] 能量 == (T+1)/n） ---------- *)
Lemma c_ta2_coverage (n T : nat) : (S T < n)%nat ->
  cr_win_sum (fun k => CRnorm_sq (u n k)) T == CR_of_Q R (qwin_aux T n).
Proof.
  intros Htn.
  induction T as [| T IHT].
  - change (cr_win_sum (fun k => CRnorm_sq (u n k)) 0)
      with (CRnorm_sq (u n 0%nat)).
    unfold qwin_aux. apply Hu_norm. lia.
  - change (cr_win_sum (fun k => CRnorm_sq (u n k)) (S T))
      with (CRplus R (cr_win_sum (fun k => CRnorm_sq (u n k)) T)
                     (CRnorm_sq (u n (S T)))).
    apply CReq_trans
      with (CRplus R (CR_of_Q R (qwin_aux T n))
                     (CR_of_Q R (Qmake 1 (Pos.of_succ_nat n)))).
    + apply CRplus_morph.
      * apply IHT. lia.
      * apply Hu_norm. lia.
    + transitivity (CR_of_Q R (Qplus (qwin_aux T n)
                                     (Qmake 1 (Pos.of_succ_nat n)))).
      * apply CReq_sym. apply CR_of_Q_plus.
      * apply CR_of_Q_morph. apply qwin_succ.
Qed.

(* ---------- C-TA2'：覆盖债（★信息性——Set 值 CRlt 对） ---------- *)

(* 债值本体：Set 层可提取项 1 − 窗能量 *)
Definition cr_debt (n T : nat) : CRcarrier R :=
  CRplus R (CR_of_Q R (Qmake 1 1))
           (CRopp R (cr_win_sum (fun k => CRnorm_sq (u n k)) T)).

(* 债的有理化：CReq 于 CR_of_Q (1 − (T+1)/n)（Q 层判定入口） *)
Definition qdebt (T n : nat) : Q :=
  Qplus (Qmake 1 1) (Qopp (qwin_aux T n)).

Lemma cr_debt_rational (n T : nat) : (S T < n)%nat ->
  cr_debt n T == CR_of_Q R (qdebt T n).
Proof.
  intros Htn. unfold cr_debt.
  apply CReq_trans
    with (CRplus R (CR_of_Q R (Qmake 1 1))
                   (CRopp R (CR_of_Q R (qwin_aux T n)))).
  - apply CRplus_morph.
    + apply CReq_refl.
    + apply CRopp_morph. apply c_ta2_coverage. exact Htn.
  - apply CReq_trans
      with (CR_of_Q R (Qplus (Qmake 1 1) (Qopp (qwin_aux T n)))).
    + (* y1 == y2：CR_of_Q_opp 直向 + CR_of_Q_plus 直向 *)
      apply CReq_trans
        with (CRplus R (CR_of_Q R (Qmake 1 1))
                       (CR_of_Q R (Qopp (qwin_aux T n)))).
      * apply CRplus_morph.
        -- apply CReq_refl.
        -- apply CReq_sym. apply CR_of_Q_opp.
      * apply CReq_sym. apply CR_of_Q_plus.
    + (* y2 == z：qdebt 与中点定义性同一 *)
      apply CR_of_Q_morph. unfold qdebt, Qeq. reflexivity.
Qed.

(* Q 层判定（Prop 层 Z <，lia 代数收口）——序判定的 Set 下放落点 *)
Lemma qdebt_bounds (n T : nat) : (S T < n)%nat ->
  Qlt (Qmake 0 1) (qdebt T n) /\ Qlt (qdebt T n) (Qmake 1 1).
Proof.
  intros Htn.
  destruct n as [| n']; [ lia | ].
  split.
  - unfold Qlt, qdebt, Qplus, Qopp, qwin_aux.
    cbn [Qnum Qden].
    rewrite (zpos_of_succ (S n')).
    rewrite !Nat2Z.inj_succ.
    lia.
  - unfold Qlt, qdebt, Qplus, Qopp, qwin_aux.
    cbn [Qnum Qden].
    rewrite (zpos_of_succ (S n')).
    rewrite !Nat2Z.inj_succ.
    lia.
Qed.

(* ★信息性界定定理：CRlt 是 Set 值（ConstructiveReals.v:88），
   本定理的证明项本身是 Set 层数据（可提取），非 Prop 压缩 *)
Theorem cr_debt_bounds (n T : nat) : (S T < n)%nat ->
  CR_of_Q R (Qmake 0 1) < cr_debt n T < CR_of_Q R (Qmake 1 1).
Proof.
  intros Htn.
  destruct (qdebt_bounds n T Htn) as [Hq0 Hq1].
  split.
  - (* 0 < debt：Q 层判定经 CR_of_Q_lt 提升，CRlt_proper 沿 CReq 信息性搬运 *)
    apply (fst (CRlt_proper R (CR_of_Q R (Qmake 0 1)) (CR_of_Q R (Qmake 0 1))
                 (CReq_refl (CR_of_Q R (Qmake 0 1)))
                 (CR_of_Q R (qdebt T n)) (cr_debt n T)
                 (CReq_sym (cr_debt n T) (CR_of_Q R (qdebt T n))
                           (cr_debt_rational n T Htn)))).
    apply CR_of_Q_lt. exact Hq0.
  - (* debt < 1：同路线 *)
    apply (fst (CRlt_proper R (CR_of_Q R (qdebt T n)) (cr_debt n T)
                 (CReq_sym (cr_debt n T) (CR_of_Q R (qdebt T n))
                           (cr_debt_rational n T Htn))
                 (CR_of_Q R (Qmake 1 1)) (CR_of_Q R (Qmake 1 1))
                 (CReq_refl (CR_of_Q R (Qmake 1 1))))).
    apply CR_of_Q_lt. exact Hq1.
Qed.

(* sigT 信息性见证：谓词为 Set 值（CRlt），sig 非法，sigT 被类型系统强制 *)
Theorem cr_debt_witness (n T : nat) : (S T < n)%nat ->
  { d : CRcarrier R &
    ((CR_of_Q R (Qmake 0 1) < d < CR_of_Q R (Qmake 1 1)) *
     (CReq R d (cr_debt n T) *
      CRlt R d (CR_of_Q R (Qmake 1 1))))%type }.
Proof.
  intros Htn. exists (cr_debt n T).
  split.
  - exact (cr_debt_bounds n T Htn).
  - split.
    + apply CReq_refl.
    + exact (snd (cr_debt_bounds n T Htn)).
Qed.

(* ---------- C-TA3：行和单调（CRle——上界证书无信息内容，留 Prop） ---------- *)
Fixpoint cr_list_sum (g : nat -> CRcarrier R) (l : list nat) : CRcarrier R :=
  match l with
  | [] => CR_of_Q R (Qmake 0 1)
  | x :: xs => CRplus R (g x) (cr_list_sum g xs)
  end.

Lemma cr_list_sum_mono (g : nat -> CRcarrier R) (P : nat -> bool)
      (l : list nat) :
  (forall i, CR_of_Q R (Qmake 0 1) <= g i) ->
  cr_list_sum g (filter P l) <= cr_list_sum g l.
Proof.
  intros Hg. induction l as [| x xs IH].
  - simpl. apply CRle_refl.
  - simpl. destruct (P x); simpl.
    + apply CRplus_le_compat_l. exact IH.
    + apply CRle_trans
        with (CRplus R (CR_of_Q R (Qmake 0 1)) (cr_list_sum g xs)).
      * rewrite CRplus_0_l. exact IH.
      * apply CRplus_le_compat_r. apply Hg.
Qed.

(* ---------- C-TA4：稀疏化保 C-比（纯 nat，与主线同款） ---------- *)
Lemma chain_step_std (C : nat) (v : nat -> nat) :
  (2 <= C)%nat -> (forall j, (v j * C <= v (S j)))%nat ->
  (forall j, (v j <= v (S j)))%nat.
Proof.
  intros HC Hv j. apply Nat.le_trans with (v j * C)%nat.
  - assert (H1 : (v j * 1 <= v j * C)%nat)
      by (apply Nat.mul_le_mono_l; lia).
    rewrite Nat.mul_1_r in H1. exact H1.
  - apply Hv.
Qed.

Lemma chain_mono_std (v : nat -> nat) :
  (forall j, (v j <= v (S j)))%nat ->
  forall a b, (a <= b)%nat -> (v a <= v b)%nat.
Proof.
  intros Hv a b Hab.
  assert (Hgen : forall d a0, (v a0 <= v (a0 + d))%nat).
  { intro d. induction d as [| d IH]; intro a0.
    - rewrite Nat.add_0_r. apply Nat.le_refl.
    - rewrite Nat.add_succ_r.
      apply Nat.le_trans with (v (a0 + d))%nat; [ exact (IH a0) | apply Hv ]. }
  replace b with (a + (b - a))%nat by lia.
  apply Hgen.
Qed.

Lemma thinning_preserves_ratio (C : nat) (v : nat -> nat) (P : nat -> bool)
        (a b : nat) :
  (2 <= C)%nat ->
  (forall j, (v j * C <= v (S j)))%nat ->
  In a (filter P (seq 0 (S b))) -> In b (filter P (seq 0 (S b))) ->
  (a < b)%nat ->
  (v a * C <= v b)%nat.
Proof.
  intros HC Hv Ha Hb Hab.
  apply Nat.le_trans with (v (S a)).
  - apply Hv.
  - assert (Hsa : (S a <= b)%nat) by lia.
    apply (chain_mono_std v (chain_step_std C v HC Hv)).
    exact Hsa.
Qed.

(* ---------- C-CA5：τ-裁剪最优性合成（★主定理） ---------- *)
Definition cr_kept (v : nat -> nat) (T : nat) (I : list nat) : list nat :=
  filter (fun i => Nat.leb (v i) T) I.
Definition cr_pruned (v : nat -> nat) (T : nat) (I : list nat) : list nat :=
  filter (fun i => negb (Nat.leb (v i) T)) I.

Theorem tau_prune_optimality_cr (C T : nat) (v : nat -> nat) (I : list nat) :
  (2 <= C)%nat ->
  (forall j, (v j * C <= v (S j)))%nat ->
  ( (* 主结论为 prod（%type）：三分信息整体是 Set 值可提取项——
       信息性 (iii) 不能进 Prop 的 /\，这是"序放 Set"的结构性后果 *)
    ( (* (i)+(ii)：Prop 层（证书单调 + 支撑完备） *)
      ( (* (i) 证书单调：kept 子族 ‖·‖² 行和 ≤ 全族行和（C-TA3 实例） *)
        forall j0, In j0 (cr_kept v T I) ->
          cr_list_sum (fun i => CRnorm_sq (u (v i) i))
            (filter (fun i => Nat.leb (v i) T) (filter (fun x => Nat.eqb x j0) I))
          <= cr_list_sum (fun i => CRnorm_sq (u (v i) i))
            (filter (fun x => Nat.eqb x j0) I) )
      /\ ( (* (ii) kept 带完全支撑在训练窗 [0,T]（C-TA1） *)
          forall j0, In j0 (cr_kept v T I) ->
            forall k, (T <= k)%nat -> CReq_cplx (u (v j0) k) CRzero ) )
    * ( (* (iii) ★pruned 严格超窗带携带信息性覆盖债（Set 值 CRlt 链） *)
        forall i, In i (cr_pruned v T I) -> (S T < v i)%nat ->
          (CR_of_Q R (Qmake 0 1) < cr_debt (v i) T < CR_of_Q R (Qmake 1 1))%ConstructiveReals ) )%type.
Proof.
  intros HC Hv.
  split.
  - split.
    + intros j0 Hj0.
      apply (cr_list_sum_mono (fun i => CRnorm_sq (u (v i) i))
                (fun i => Nat.leb (v i) T)
                (filter (fun x => Nat.eqb x j0) I)).
      intros i. apply CRnorm_sq_nonneg.
    + intros j0 Hj0 k Hk.
      apply (c_ta1_support (v j0) T k).
      * apply (proj1 (Nat.leb_le (v j0) T)).
        apply filter_In in Hj0. destruct Hj0 as [_ Hle]. exact Hle.
      * exact Hk.
  - intros i Hi Hlt.
    exact (cr_debt_bounds (v i) T Hlt).
Qed.

End TauGridCR.

(* ---------- 审计 ---------- *)
Print Assumptions c_ta2_coverage.
Print Assumptions cr_debt_bounds.
Print Assumptions cr_debt_witness.
Print Assumptions cr_list_sum_mono.
Print Assumptions tau_prune_optimality_cr.

(* ---------- 提取（Set 层可执行对象 + 柯西实例具象化） ---------- *)
(* 信息性提取目标 = CRealConstructive（柯西实例，CRealLt 存储逼近数据；
   DRealConstructive 的 CRlt ≡ Rlt 被经典公理阻断，不采用） *)
From Stdlib Require Import Extraction.
From Stdlib Require Import ConstructiveRcomplete.

Definition tau_cr_ladder_zero :
  nat -> nat -> @CRComplex CRealConstructive := fun _ _ => CRzero.

(* eta 展开：常量包装会带弱类型（'_weak1），函数形式可泛化 *)
Definition cr_win_sum_cauchy := fun f T => @cr_win_sum CRealConstructive f T.
Definition cr_debt_cauchy := fun n T => @cr_debt CRealConstructive tau_cr_ladder_zero n T.
Definition cr_list_sum_cauchy := fun g l => @cr_list_sum CRealConstructive g l.

Extraction "taugrid_cr.ml" cr_win_sum_cauchy cr_debt_cauchy
  cr_list_sum_cauchy cr_kept cr_pruned.
