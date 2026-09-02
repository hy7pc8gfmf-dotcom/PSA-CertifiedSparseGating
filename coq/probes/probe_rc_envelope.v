(* ============================================================
   probe_rc_envelope.v —— RC-real T2：区间包络（追加件形态）
   PSA/PSA-GSA z 区构造性轨道 · Phase 3（2026-09-02，对齐 CW-151）
   ============================================================

   使命（交接工作流 §J T2 + 协同留言 PSA 侧追记）：在 CW-151 的
   Bishop 正则化（regularize_uniform_mod 一致模）之上构建区间包络
   lo/hi : Real -> nat -> Q——证书型有理比较原生可判定，反哺形态
   为「关于 CW 原载体（Real/cauchy/real_eq/real_lt/regularize）的
   追加段」。

   provenance（复刻件/改造件分标）：
     · [CW151-BASE] 块：ConstructiveWorld-151.v 最小闭包 verbatim
       复刻（仅构造方式，名字与 CW 原件一致）——Id/And/Or、
       QltT/QleT、载体 Real 族、q_arch_inv 正则化全套。
       **CW 侧吸收 = 整块删除**（其原生定义已在）。
     · [T2-SEGMENT] 块起为本项目非平凡改造（吸收 = 原样 append）：
       – ★ T2-① env_contains         包络可靠性（尾部包含，一致模直推）
       – ★ T2-② env_witness_complete 序见证完备性：real_lt x y ⟹
         可计算 n 使 hi x n < lo y n（证书型有理比较可判定的核心，
         CW-151 无此件）
       – ★ T2-③ env_check_sound + rc_lt_dec   检查健全性 ⟕ 分离双侧
         闭合（env_lt_check 通过 ⟺ real_lt 可证）
       – ★ T2-④ env_plus_prop / env_opp_prop  四则传播（+/−，宽化
         3·env_w n / 2·env_w n——逐点三角链，零 real_eq 兼容引理依赖）

   与 CW-151 的关系：q_arch_inv 走 stdlib Qarchimedean（较 PSA 首版
   rc_dyo_small 的 Z.log2 路线省力，已采纳为基座）；一致模
   |v a − v b| < 1/(min a b + 2) 是包络的直接基底——T2 是 CW-151
   正则化的第一消费者，非重复建设。

   验收（铁律 1-3，2026-09-02 实测）：
     ① coqc EXIT=0；Print Assumptions ×10 全部字面
        「Closed under the global context」（含 CW-151 基座块）。
     ② Extraction rc_envelope_t2.ml/.mli，ocamlc（DkMLNative）EXIT=0；
        占位符审计：仅提取器擦除原语 type __ = Obj.t 与 cauchy 类型
        中 Prop 箭头位（nat≤ 证明参）的按设计擦除——QltT 数据载荷
        与全部包络函数（env_lo/hi/check）均为真实布尔逻辑。
     ③ 结论与数据全 Set 层（QltT/And/sigT）；零 Reals/零经典。
   实测坑（当日沉淀 E251 方向）：lra(Lqa) 不吃 Q 除法（含常数除法
   /4——改乘字面量逆元 * (1#4) 即线性化）；exact 只做项转换，
   QltT→Qlt 必须走 QltT_to_Qlt 引理层；destruct 后 change 目标
   要用 existT 形态（原变量名已出 scope）；CW 式 QleT 右支不可
   构造——QleT 只能经 left(严格) 构造，全部链保持严格至收口。
   ============================================================ *)
Require Import Stdlib.QArith.QArith.
Require Import Stdlib.QArith.Qabs.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia.
From Stdlib Require Import Lqa.
From Stdlib Require Import Extraction.
From Stdlib Require Import PeanoNat.

(* ############ [CW151-BASE-BEGIN] ############
   CW-151 最小闭包 verbatim 复刻。CW 侧吸收时整块删除
   （从本行到 [CW151-BASE-END]），T2 段直接使用 CW 原生定义。 ############ *)

(* ---- B0：Set 层恒等与逻辑（CW-146/151 L62-95） ---- *)

Inductive Id {A : Set} (x : A) : A -> Set :=
| id_refl : Id x x.

Arguments id_refl {A} {x}.

Definition And (A B : Set) : Set := A * B.
Definition Or  (A B : Set) : Set := A + B.

Definition id_sym {A : Set} {x y : A} (p : Id x y) : Id y x :=
  match p with
  | id_refl => id_refl
  end.

Definition id_trans {A : Set} {x y z : A} (p : Id x y) (q : Id y z) : Id x z :=
  match p, q with
  | id_refl, id_refl => id_refl
  end.

(* ---- B0'：QltT/QleT（CW-146/151 L2947-2985） ---- *)

Definition Qlt_bool (x y : Q) : bool :=
  match Qcompare x y with
  | Lt => true
  | _ => false
  end.

Definition QltT (x y : Q) : Set := Id (Qlt_bool x y) true.
Definition QleT (x y : Q) : Set := Or (QltT x y) (Id x y).

Lemma QltT_to_Qlt : forall x y : Q, QltT x y -> Qlt x y.
Proof.
  intros x y H.
  unfold QltT in H.
  unfold Qlt_bool in H.
  destruct (Qcompare x y) eqn:E; try (inversion H).
  apply Qlt_alt. exact E.
Qed.

Lemma Qlt_to_QltT : forall x y : Q, Qlt x y -> QltT x y.
Proof.
  intros x y H.
  unfold QltT, Qlt_bool.
  destruct (Qcompare x y) eqn:E.
  - exfalso.
    assert (Heq : x == y) by (apply Qeq_alt; exact E).
    rewrite Heq in H.
    apply (Qlt_irrefl y). exact H.
  - reflexivity.
  - exfalso.
    assert (Hyx : y < x) by (apply Qgt_alt; exact E).
    apply (Qlt_irrefl x). eapply Qlt_trans. exact H. exact Hyx.
Qed.

(* ---- B1：载体（CW-146/151 L2945-3053, L3063-3065） ---- *)

Definition Qseq := nat -> Q.

Definition cauchy (u : Qseq) : Set :=
  forall eps : Q, QltT 0 eps ->
    sigT (fun N : nat => forall m n : nat, (N <= m)%nat -> (N <= n)%nat ->
        QltT (Qabs (u m - u n)) eps).

Definition Real : Set := sigT (fun u : Qseq => cauchy u).

Definition real_eq (x y : Real) : Set :=
  forall eps : Q, QltT 0 eps ->
    sigT (fun N : nat => forall n : nat, (N <= n)%nat ->
        QltT (Qabs (projT1 x n - projT1 y n)) eps).

Definition real_lt (x y : Real) : Set :=
  sigT (fun eps : Q => And (QltT 0 eps) (sigT (fun N : nat => forall n, (N <= n)%nat ->
        QltT eps (projT1 y n - projT1 x n)))).

Definition real_plus (x y : Real) : Real.
Proof.
  destruct x as [u Hu]. destruct y as [v Hv].
  exists (fun n => (u n + v n)%Q).
  intros eps Heps.
  destruct (Hu (eps/2)%Q) as [N1 HN1].
  { assert (Hhalf : Qlt 0 (eps / 2)).
    { apply Qlt_shift_div_l.
      - reflexivity.
      - simpl. apply QltT_to_Qlt. exact Heps. }
    apply Qlt_to_QltT. exact Hhalf. }
  destruct (Hv (eps/2)%Q) as [N2 HN2].
  { assert (Hhalf2 : Qlt 0 (eps / 2)).
    { apply Qlt_shift_div_l.
      - reflexivity.
      - simpl. apply QltT_to_Qlt. exact Heps. }
    apply Qlt_to_QltT. exact Hhalf2. }
  exists (max N1 N2).
  intros m n Hm Hn.
  assert (HN1' := HN1 m n).
  assert (HN2' := HN2 m n).
  apply Qlt_to_QltT.
  apply Qle_lt_trans with (Qabs (u m - u n) + Qabs (v m - v n)).
  - assert (Hsum : u m + v m - (u n + v n) == (u m - u n) + (v m - v n)).
    { ring. }
    setoid_rewrite Hsum.
    apply Qabs_triangle.
  - assert (Heps_sum : eps/2 + eps/2 == eps). { field. }
    setoid_rewrite <- Heps_sum.
    apply Qplus_lt_compat.
    * apply QltT_to_Qlt. apply HN1'.
      -- apply Nat.le_trans with (max N1 N2); [apply Nat.le_max_l | exact Hm].
      -- apply Nat.le_trans with (max N1 N2); [apply Nat.le_max_l | exact Hn].
    * apply QltT_to_Qlt. apply HN2'.
      -- apply Nat.le_trans with (max N1 N2); [apply Nat.le_max_r | exact Hm].
      -- apply Nat.le_trans with (max N1 N2); [apply Nat.le_max_r | exact Hn].
Defined.

Definition real_opp (x : Real) : Real.
Proof.
  destruct x as [u Hu].
  exists (fun n => (- u n)%Q).
  intros eps Heps.
  destruct (Hu eps Heps) as [N HN].
  exists N.
  intros m n Hm Hn.
  specialize (HN m n Hm Hn).
  assert (H1 : - u m - - u n == -(u m - u n)).
  { ring. }
  assert (H2 : Qabs (- u m - - u n) == Qabs (u m - u n)).
  { setoid_rewrite H1. apply Qabs_opp. }
  apply Qlt_to_QltT.
  setoid_rewrite H2.
  apply QltT_to_Qlt. exact HN.
Defined.

(* ---- B2：Bishop 正则化全套（CW-151 L4284-4561） ---- *)

Lemma q_arch_inv : forall eps : Q, Qlt 0 eps ->
  sigT (fun N : nat => Qlt (1 / (Z.of_nat (N + 2) # 1)) eps).
Proof.
  intros eps Heps.
  destruct (Qarchimedean (1 / eps)) as [p Hp].
  set (N := (Z.to_nat (Z.pos p) * 2)%nat).
  exists N.
  apply Qlt_shift_div_r; [ | ].
  - unfold Qlt. simpl.
    assert (Hnz : (0 < Z.of_nat (N + 2))%Z) by (unfold N; lia).
    lia.
  - apply (Qlt_trans _ (eps * (Z.pos p # 1)) _).
    + assert (Hmul : Qlt ((1 / eps) * eps) ((Z.pos p # 1) * eps)).
      { apply (Qmult_lt_compat_r (1 / eps) (Z.pos p # 1) eps Heps). exact Hp. }
      setoid_replace ((1 / eps) * eps) with 1%Q in Hmul.
      2: { field. intro Hz. apply (Qlt_not_eq 0 eps Heps). exact (Qeq_sym _ _ Hz). }
      setoid_replace ((Z.pos p # 1) * eps) with (eps * (Z.pos p # 1)) in Hmul by ring.
      exact Hmul.
    + setoid_replace (eps * (Z.pos p # 1)) with ((Z.pos p # 1) * eps) by ring.
      setoid_replace (eps * (Z.of_nat (N + 2) # 1)) with ((Z.of_nat (N + 2) # 1) * eps) by ring.
      apply (Qmult_lt_compat_r (Z.pos p # 1) (Z.of_nat (N + 2) # 1) eps Heps).
      unfold Qlt. simpl.
      assert (Hz : (Z.pos p < Z.of_nat (N + 2))%Z).
      { unfold N. lia. }
      lia.
Qed.

Lemma q_arch_inv_mono : forall (eps : Q) (N M : nat),
  (N <= M)%nat -> Qlt (1 / (Z.of_nat (N + 2) # 1)) eps ->
  Qlt (1 / (Z.of_nat (M + 2) # 1)) eps.
Proof.
  intros eps N M Hle Harch.
  destruct (Nat.eq_dec M N) as [Heq | Hne].
  - subst. exact Harch.
  - assert (Hlt : (N < M)%nat) by lia.
    apply (Qlt_trans _ (1 / (Z.of_nat (N + 2) # 1)) _).
    + setoid_replace (1 / (Z.of_nat (M + 2) # 1)) with (/ (Z.of_nat (M + 2) # 1))
        by (unfold Qdiv; apply Qmult_1_l).
      setoid_replace (1 / (Z.of_nat (N + 2) # 1)) with (/ (Z.of_nat (N + 2) # 1))
        by (unfold Qdiv; apply Qmult_1_l).
      assert (HposN : Qlt 0 (Z.of_nat (N + 2) # 1)) by (unfold Qlt; simpl; lia).
      assert (HposM : Qlt 0 (Z.of_nat (M + 2) # 1)) by (unfold Qlt; simpl; lia).
      apply (proj1 (Qinv_lt_contravar (Z.of_nat (N + 2) # 1) (Z.of_nat (M + 2) # 1)
                    HposN HposM)).
      unfold Qlt. simpl. lia.
    + exact Harch.
Qed.

Lemma q_arch_inv_pos : forall (N : nat), Qlt 0 (1 / (Z.of_nat (N + 2) # 1)).
Proof.
  intro N.
  apply Qlt_shift_div_l; [ | ].
  - unfold Qlt. simpl. lia.
  - setoid_replace (0 * (Z.of_nat (N + 2) # 1)) with 0%Q by ring.
    reflexivity.
Qed.

Lemma nat_min_l : forall a b : nat, (a <= b)%nat -> Nat.min a b = a.
Proof. intros a b H. apply Nat.min_l. exact H. Qed.
Lemma nat_min_r : forall a b : nat, (b <= a)%nat -> Nat.min a b = b.
Proof. intros a b H. apply Nat.min_r. exact H. Qed.

Fixpoint reg_index (fmod : nat -> nat) (k : nat) : nat :=
  match k with
  | O => fmod O
  | Datatypes.S k' => max (Datatypes.S (reg_index fmod k')) (fmod (Datatypes.S k'))
  end.

Lemma reg_index_mono : forall (fmod : nat -> nat) (a b : nat),
  (a <= b)%nat -> (reg_index fmod a <= reg_index fmod b)%nat.
Proof.
  intros fmod. induction b as [| b' IHb]; intros Ha.
  - destruct a; simpl; lia.
  - destruct (Nat.eq_dec a (Datatypes.S b')) as [Heq | Hne].
    + subst. lia.
    + assert (Ha_le : (a <= b')%nat) by lia.
      apply (Nat.le_trans _ (reg_index fmod b') _ (IHb Ha_le)).
      change ((reg_index fmod b' <=
              Nat.max (Datatypes.S (reg_index fmod b')) (fmod (Datatypes.S b')))%nat).
      apply Nat.le_trans with (Nat.max (Datatypes.S (reg_index fmod b')) (fmod (Datatypes.S b'))).
      * apply Nat.le_trans with (Datatypes.S (reg_index fmod b')).
        -- apply Nat.le_succ_diag_r.
        -- apply Nat.le_max_l.
      * reflexivity.
Qed.

Lemma reg_index_ge : forall (fmod : nat -> nat) (k : nat),
  (k <= reg_index fmod k)%nat.
Proof.
  intros fmod. induction k; [ lia | ].
  apply (Nat.le_trans _ (Datatypes.S (reg_index fmod k)) _).
  - exact (le_n_S k (reg_index fmod k) IHk).
  - change ((Datatypes.S (reg_index fmod k) <=
            Nat.max (Datatypes.S (reg_index fmod k)) (fmod (Datatypes.S k)))%nat).
    apply Nat.le_max_l.
Qed.

Lemma reg_index_fmod : forall (fmod : nat -> nat) (k : nat),
  (fmod k <= reg_index fmod k)%nat.
Proof.
  intros fmod k. induction k; [ simpl; lia | ].
  change ((fmod (Datatypes.S k) <=
           Nat.max (Datatypes.S (reg_index fmod k)) (fmod (Datatypes.S k)))%nat).
  apply Nat.le_max_r.
Qed.

Definition reg_mod (u : Qseq) (Hu : cauchy u) (j : nat) : nat :=
  projT1 (Hu (1 / (Z.of_nat (j + 2) # 1))
              (Qlt_to_QltT 0 (1 / (Z.of_nat (j + 2) # 1)) (q_arch_inv_pos j))).

Definition regularize (u : Qseq) (Hu : cauchy u) : Qseq :=
  fun k => u (reg_index (fun j => reg_mod u Hu j) k).

Lemma q_abs_minus_sym : forall a b : Q, Qabs (a - b) == Qabs (b - a).
Proof.
  intros a b.
  assert (H : b - a == - (a - b)). { ring. }
  setoid_rewrite H.
  symmetry.
  apply Qabs_opp.
Qed.

Lemma q_half_lt : forall eps : Q, Qlt 0 eps -> Qlt (eps / 2) eps.
Proof.
  intros eps Heps.
  apply Qlt_shift_div_r; [reflexivity | ].
  setoid_replace (eps * 2) with (eps + eps) by ring.
  apply Qlt_minus_iff.
  setoid_replace (eps + eps + - eps) with eps by ring.
  exact Heps.
Qed.

Lemma regularize_uniform_mod : forall (u : Qseq) (Hu : cauchy u) (a b : nat),
  Qlt (Qabs (regularize u Hu a - regularize u Hu b)) (1 / (Z.of_nat (Nat.min a b + 2) # 1)).
Proof.
  intros u Hu a b.
  destruct (Nat.le_gt_cases a b) as [Hab | Hba].
  - rewrite (nat_min_l a b Hab).
    unfold regularize.
    set (fmod := fun j : nat => reg_mod u Hu j).
    set (fa := reg_index fmod a).
    set (fb := reg_index fmod b).
    assert (Hfa_fmod : (fmod a <= fa)%nat) by (unfold fa; apply reg_index_fmod).
    assert (Hfa_le_fb : (fa <= fb)%nat) by (unfold fa, fb; apply reg_index_mono; exact Hab).
    assert (Hc : QltT (Qabs (u fa - u fb)) (1 / (Z.of_nat (a + 2) # 1))).
    { apply (projT2 (Hu (1 / (Z.of_nat (a + 2) # 1))
                        (Qlt_to_QltT 0 (1 / (Z.of_nat (a + 2) # 1)) (q_arch_inv_pos a)))
                    fa fb Hfa_fmod).
      apply (Nat.le_trans _ fa _ Hfa_fmod Hfa_le_fb). }
    unfold fa, fb in Hc.
    exact (QltT_to_Qlt _ _ Hc).
  - rewrite (nat_min_r a b (Nat.lt_le_incl _ _ Hba)).
    unfold regularize.
    set (fmod := fun j : nat => reg_mod u Hu j).
    set (fa := reg_index fmod a).
    set (fb := reg_index fmod b).
    assert (Hfb_fmod : (fmod b <= fb)%nat) by (unfold fb; apply reg_index_fmod).
    assert (Hfb_le_fa : (fb <= fa)%nat) by (unfold fa, fb; apply reg_index_mono; lia).
    assert (Hc : QltT (Qabs (u fb - u fa)) (1 / (Z.of_nat (b + 2) # 1))).
    { apply (projT2 (Hu (1 / (Z.of_nat (b + 2) # 1))
                        (Qlt_to_QltT 0 (1 / (Z.of_nat (b + 2) # 1)) (q_arch_inv_pos b)))
                    fb fa Hfb_fmod).
      apply (Nat.le_trans _ fb _ Hfb_fmod Hfb_le_fa). }
    assert (Hsym : Qabs (u fa - u fb) == Qabs (u fb - u fa)).
    { apply q_abs_minus_sym. }
    setoid_rewrite Hsym.
    exact (QltT_to_Qlt _ _ Hc).
Qed.

Lemma regularize_cauchy : forall (u : Qseq) (Hu : cauchy u),
  cauchy (regularize u Hu).
Proof.
  intros u Hu eps Heps.
  destruct (q_arch_inv eps (QltT_to_Qlt 0 eps Heps)) as [N HN].
  exists N.
  intros a b Ha Hb.
  assert (Hmin : (N <= Nat.min a b)%nat).
  { destruct (Nat.le_gt_cases a b) as [Hab' | Hba'].
    - rewrite (nat_min_l a b Hab'). exact Ha.
    - rewrite (nat_min_r a b (Nat.lt_le_incl _ _ Hba')). exact Hb. }
  assert (Hum : Qlt (Qabs (regularize u Hu a - regularize u Hu b))
                    (1 / (Z.of_nat (Nat.min a b + 2) # 1))) by (apply regularize_uniform_mod).
  assert (Hmono : Qlt (1 / (Z.of_nat (Nat.min a b + 2) # 1)) eps).
  { apply (q_arch_inv_mono eps N (Nat.min a b) Hmin). exact HN. }
  apply Qlt_to_QltT.
  exact (Qlt_trans _ _ _ Hum Hmono).
Qed.

Lemma regularize_same_real : forall (u : Qseq) (Hu : cauchy u),
  real_eq (existT _ (regularize u Hu) (regularize_cauchy u Hu))
          (existT _ u Hu).
Proof.
  intros u Hu eps Heps.
  assert (Hhalf0 : QltT 0 (eps / 2)%Q).
  {
    assert (Hq : Qlt 0 (eps / 2)).
    { apply Qlt_shift_div_l; [reflexivity | simpl; apply QltT_to_Qlt; exact Heps]. }
    exact (Qlt_to_QltT 0 (eps / 2) Hq).
  }
  destruct (Hu (eps / 2)%Q Hhalf0) as [C HC].
  exists C.
  intros k Hk.
  assert (Hfk : (C <= reg_index (fun j => reg_mod u Hu j) k)%nat).
  {
    apply (Nat.le_trans _ k _ Hk).
    apply reg_index_ge.
  }
  assert (Hc : QltT (Qabs (u k - u (reg_index (fun j => reg_mod u Hu j) k))) (eps / 2)%Q).
  { apply (HC k (reg_index (fun j => reg_mod u Hu j) k) Hk Hfk). }
  assert (Hgoal : Qlt (Qabs (regularize u Hu k - u k)) eps).
  {
    unfold regularize.
    assert (Hd : Qabs (u (reg_index (fun j => reg_mod u Hu j) k) - u k)
                  == Qabs (u k - u (reg_index (fun j => reg_mod u Hu j) k))).
    { apply q_abs_minus_sym. }
    setoid_rewrite Hd.
    exact (Qlt_trans _ (eps / 2)%Q _ (QltT_to_Qlt _ _ Hc) (q_half_lt eps (QltT_to_Qlt 0 eps Heps))).
  }
  apply Qlt_to_QltT.
  exact Hgoal.
Qed.

(* ############ [CW151-BASE-END] ############ *)

(* ============================================================
   [T2-SEGMENT] 区间包络（本项目非平凡改造；CW 吸收 = 从此行
   起原样 append 进 v152+）
   ============================================================ *)

(* ---- T2.0 辅助件 ---- *)

(* Id → Qeq 桥 *)
Lemma env_Id_Qeq : forall x y : Q, Id x y -> x == y.
Proof. intros x y H. destruct H. apply Qeq_refl. Qed.

(* QleT → Qle（使用侧：左支转严格、右支经 Id 同一化） *)
Lemma env_Qle_of_QleT : forall x y : Q, QleT x y -> Qle x y.
Proof.
  intros x y H. destruct H as [Hlt | Heq].
  - apply Qlt_le_weak. apply QltT_to_Qlt. exact Hlt.
  - rewrite (env_Id_Qeq _ _ Heq). apply Qle_refl.
Qed.

(* |a − b| < c 的双侧解包：b − c < a ∧ a − c < b *)
Lemma env_abs_bounds : forall a b c : Q, Qlt (Qabs (a - b)) c ->
  And (Qlt (b - c) a) (Qlt (a - c) b).
Proof.
  intros a b c H.
  assert (Hle1 : Qle (a - b) (Qabs (a - b))).
  { destruct (Qcompare (a - b) 0) eqn:E.
    - assert (Hz : (a - b)%Q == 0) by (apply Qeq_alt; exact E).
      rewrite Hz. apply Qle_refl.
    - assert (Hx0 : Qle (a - b) 0) by (apply Qlt_le_weak; apply Qlt_alt; exact E).
      rewrite (Qabs_neg (a - b)) by exact Hx0.
      lra.
    - assert (Hx0 : Qle 0 (a - b)).
      { apply Qlt_le_weak. apply Qgt_alt. exact E. }
      rewrite (Qabs_pos (a - b)) by exact Hx0.
      apply Qle_refl. }
  assert (Hle2 : Qle (b - a) (Qabs (a - b))).
  { assert (Hle2' : Qle (b - a) (Qabs (b - a))).
    { destruct (Qcompare (b - a) 0) eqn:E.
      - assert (Hz : (b - a)%Q == 0) by (apply Qeq_alt; exact E).
        rewrite Hz. apply Qle_refl.
      - assert (Hx0 : Qle (b - a) 0) by (apply Qlt_le_weak; apply Qlt_alt; exact E).
        rewrite (Qabs_neg (b - a)) by exact Hx0.
        lra.
      - assert (Hx0 : Qle 0 (b - a)).
        { apply Qlt_le_weak. apply Qgt_alt. exact E. }
        rewrite (Qabs_pos (b - a)) by exact Hx0.
        apply Qle_refl. }
    setoid_rewrite <- (q_abs_minus_sym a b) in Hle2'.
    exact Hle2'. }
  assert (Hlt1 : Qlt (b - a) c) by (apply Qle_lt_trans with (Qabs (a - b)); assumption).
  assert (Hlt2 : Qlt (a - b) c) by (apply Qle_lt_trans with (Qabs (a - b)); assumption).
  split; lra.
Qed.

(* ---- T2.1 包络定义 ---- *)

(* 包络半宽：1/(n+2)（与 CW-151 一致模同尺度） *)
Definition env_w (n : nat) : Q := 1 / (Z.of_nat (n + 2) # 1).

(* 实数的正则代表元序列 *)
Definition reg_of (x : Real) : Qseq := regularize (projT1 x) (projT2 x).

(* 正则代表元包装成实数 *)
Definition reg_real (x : Real) : Real :=
  existT (fun u : Qseq => cauchy u) (reg_of x)
         (regularize_cauchy (projT1 x) (projT2 x)).

Lemma reg_same : forall x : Real, real_eq (reg_real x) x.
Proof.
  intros x. destruct x as [u Hu]. simpl.
  apply regularize_same_real.
Qed.

(* 下/上包络 *)
Definition env_lo (x : Real) : nat -> Q := fun n => reg_of x n - env_w n.
Definition env_hi (x : Real) : nat -> Q := fun n => reg_of x n + env_w n.

(* 可判定分离检查（运行时布尔镜像） *)
Definition env_lt_check (x y : Real) (n : nat) : bool :=
  Qlt_bool (env_hi x n) (env_lo y n).

Lemma env_w_pos : forall n : nat, QltT 0 (env_w n).
Proof. intros n. unfold env_w. apply Qlt_to_QltT. apply q_arch_inv_pos. Qed.

(* env_w 单调递减：m ≤ n ⟹ env_w n ≤ env_w m *)
Lemma env_w_le : forall m n : nat, (m <= n)%nat -> Qle (env_w n) (env_w m).
Proof.
  intros m n H.
  destruct (Nat.eq_dec m n) as [Heq | Hne].
  - subst. apply Qle_refl.
  - assert (Hlt : (m < n)%nat) by lia.
    unfold env_w.
    setoid_replace (1 / (Z.of_nat (n + 2) # 1)) with (/ (Z.of_nat (n + 2) # 1))
      by (unfold Qdiv; apply Qmult_1_l).
    setoid_replace (1 / (Z.of_nat (m + 2) # 1)) with (/ (Z.of_nat (m + 2) # 1))
      by (unfold Qdiv; apply Qmult_1_l).
    assert (Hposm : Qlt 0 (Z.of_nat (m + 2) # 1)) by (unfold Qlt; simpl; lia).
    assert (Hposn : Qlt 0 (Z.of_nat (n + 2) # 1)) by (unfold Qlt; simpl; lia).
    apply Qlt_le_weak.
    apply (proj1 (Qinv_lt_contravar (Z.of_nat (m + 2) # 1) (Z.of_nat (n + 2) # 1)
                  Hposm Hposn)).
    unfold Qlt. simpl. lia.
Qed.

(* ---- T2.2 ★ 包络可靠性（尾部包含） ---- *)

Theorem env_contains : forall (x : Real) (n k : nat), (n <= k)%nat ->
  And (QltT (env_lo x n) (reg_of x k)) (QltT (reg_of x k) (env_hi x n)).
Proof.
  intros x n k Hn.
  destruct x as [u Hu].
  assert (Hum := regularize_uniform_mod u Hu n k).
  rewrite (nat_min_l n k Hn) in Hum.
  change (1 / (Z.of_nat (n + 2) # 1)) with (env_w n) in Hum.
  assert (Hb := env_abs_bounds (regularize u Hu n) (regularize u Hu k)
                  (env_w n) Hum).
  destruct Hb as [Hl Hr].
  split.
  - apply Qlt_to_QltT.
    change (env_lo (existT (fun u0 : Qseq => cauchy u0) u Hu) n)
      with (regularize u Hu n - env_w n).
    change (reg_of (existT (fun u0 : Qseq => cauchy u0) u Hu) k)
      with (regularize u Hu k).
    exact Hr.
  - apply Qlt_to_QltT.
    change (reg_of (existT (fun u0 : Qseq => cauchy u0) u Hu) k)
      with (regularize u Hu k).
    change (env_hi (existT (fun u0 : Qseq => cauchy u0) u Hu) n)
      with (regularize u Hu n + env_w n).
    lra.
Qed.

(* ---- T2.3 包络接口（弱形式，可传播）与规范实例 ---- *)

Definition env_ok (x : Real) (lo hi : nat -> Q) : Set :=
  forall n : nat, sigT (fun N0 : nat => forall k : nat, (N0 <= k)%nat ->
    And (QleT (lo n) (reg_of x k)) (QleT (reg_of x k) (hi n))).

Theorem env_ok_canonical : forall x : Real, env_ok x (env_lo x) (env_hi x).
Proof.
  intros x n. exists n. intros k Hk.
  destruct (env_contains x n k Hk) as [H1 H2].
  split.
  - left. exact H1.
  - left. exact H2.
Qed.

(* ---- T2.4 ★ 序见证完备性 ---- *)

Theorem env_witness_complete : forall x y : Real, real_lt x y ->
  sigT (fun n : nat => QltT (env_hi x n) (env_lo y n)).
Proof.
  intros x y Hlt.
  destruct Hlt as [eps [Heps [N HN]]].
  assert (Hep : Qlt 0 eps) by (apply QltT_to_Qlt; exact Heps).
  assert (Heps4 : Qlt 0 (eps * (1#4))%Q) by lra.
  destruct (q_arch_inv (eps * (1#4))%Q Heps4) as [n0 Hn0].
  change (1 / (Z.of_nat (n0 + 2) # 1)) with (env_w n0) in Hn0.
  assert (Hd0pos : QltT 0 (env_w n0)) by apply env_w_pos.
  destruct (reg_same x (env_w n0) Hd0pos) as [Cx HCx].
  destruct (reg_same y (env_w n0) Hd0pos) as [Cy HCy].
  exists (Nat.max N (Nat.max n0 (Nat.max Cx Cy))).
  set (n := Nat.max N (Nat.max n0 (Nat.max Cx Cy))).
  assert (HnN : (N <= Nat.max N (Nat.max n0 (Nat.max Cx Cy)))%nat) by lia.
  assert (Hnn0 : (n0 <= Nat.max N (Nat.max n0 (Nat.max Cx Cy)))%nat) by lia.
  assert (HnCx : (Cx <= Nat.max N (Nat.max n0 (Nat.max Cx Cy)))%nat) by lia.
  assert (HnCy : (Cy <= Nat.max N (Nat.max n0 (Nat.max Cx Cy)))%nat) by lia.
  assert (Hwn : Qle (env_w n) (env_w n0)) by (apply env_w_le; exact Hnn0).
  specialize (HN _ HnN).
  specialize (HCx _ HnCx).
  specialize (HCy _ HnCy).
  assert (HCx' : Qlt (Qabs (reg_of x n - projT1 x n)) (env_w n0))
    by (apply QltT_to_Qlt; exact HCx).
  assert (HCy' : Qlt (Qabs (reg_of y n - projT1 y n)) (env_w n0))
    by (apply QltT_to_Qlt; exact HCy).
  assert (H1 : Qlt eps (projT1 y n - projT1 x n)) by (apply QltT_to_Qlt; exact HN).
  assert (Hd0lt : Qlt (env_w n0) (eps * (1#4))%Q) by exact Hn0.
  apply Qlt_to_QltT.
  change (env_hi x n) with (reg_of x n + env_w n).
  change (env_lo y n) with (reg_of y n - env_w n).
  destruct (env_abs_bounds (reg_of x n) (projT1 x n) (env_w n0) HCx')
    as [_ Hx1].
  destruct (env_abs_bounds (reg_of y n) (projT1 y n) (env_w n0) HCy')
    as [Hy2 _].
  lra.
Qed.

(* ---- T2.5 ★ 检查健全性 + 可判定分离证书 ---- *)

Theorem env_check_sound : forall (x y : Real) (n : nat),
  QltT (env_hi x n) (env_lo y n) -> real_lt x y.
Proof.
  intros x y n Hsep.
  assert (Hd : Qlt (env_hi x n) (env_lo y n)) by (apply QltT_to_Qlt; exact Hsep).
  assert (Hd4 : Qlt 0 ((env_lo y n - env_hi x n) * (1#4))%Q) by lra.
  assert (Hd4' : QltT 0 ((env_lo y n - env_hi x n) * (1#4))%Q)
    by (apply Qlt_to_QltT; exact Hd4).
  destruct (reg_same x ((env_lo y n - env_hi x n) * (1#4))%Q Hd4') as [Cx HCx].
  destruct (reg_same y ((env_lo y n - env_hi x n) * (1#4))%Q Hd4') as [Cy HCy].
  exists ((env_lo y n - env_hi x n) * (1#2))%Q.
  split.
  - apply Qlt_to_QltT. lra.
  - exists (Nat.max n (Nat.max Cx Cy)). intros k Hk.
    assert (Hkn : (n <= k)%nat) by lia.
    assert (HkCx : (Cx <= k)%nat) by lia.
    assert (HkCy : (Cy <= k)%nat) by lia.
    destruct (env_contains x n k Hkn) as [_ Hxh].
    destruct (env_contains y n k Hkn) as [Hyl _].
    specialize (HCx k HkCx). specialize (HCy k HkCy).
    assert (HCx' : Qlt (Qabs (reg_of x k - projT1 x k))
                     ((env_lo y n - env_hi x n) * (1#4))%Q)
      by (apply QltT_to_Qlt; exact HCx).
    assert (HCy' : Qlt (Qabs (reg_of y k - projT1 y k))
                     ((env_lo y n - env_hi x n) * (1#4))%Q)
      by (apply QltT_to_Qlt; exact HCy).
    destruct (env_abs_bounds (reg_of x k) (projT1 x k)
              ((env_lo y n - env_hi x n) * (1#4))%Q HCx') as [Hx1 _].
    destruct (env_abs_bounds (reg_of y k) (projT1 y k)
              ((env_lo y n - env_hi x n) * (1#4))%Q HCy') as [_ Hy1].
    assert (A1 : Qle (reg_of x k) (env_hi x n)) by (apply env_Qle_of_QleT; left; exact Hxh).
    assert (A2 : Qle (env_lo y n) (reg_of y k)) by (apply env_Qle_of_QleT; left; exact Hyl).
    apply Qlt_to_QltT.
    lra.
Qed.

(* 可判定分离证书：real_lt 可证 ⟹ 运行时检查在某 n 处通过 *)
Corollary rc_lt_dec : forall x y : Real, real_lt x y ->
  sigT (fun n : nat => Id (env_lt_check x y n) true).
Proof.
  intros x y H.
  destruct (env_witness_complete x y H) as [n Hn].
  exists n. exact Hn.
Qed.

(* ---- T2.6 ★ 四则传播（+ 与 −，逐点三角链） ---- *)

Theorem env_plus_prop : forall (x y : Real) (lox hix loy hiy : nat -> Q),
  env_ok x lox hix -> env_ok y loy hiy ->
  env_ok (real_plus x y)
    (fun n => lox n + loy n - 3 * env_w n)%Q
    (fun n => hix n + hiy n + 3 * env_w n)%Q.
Proof.
  intros x y lox hix loy hiy Hx Hy.
  destruct x as [u Hu]. destruct y as [v Hv].
  intros n.
  destruct (Hx n) as [N0x HN0x].
  destruct (Hy n) as [N0y HN0y].
  assert (Hwp : Qlt 0 (env_w n)) by (apply QltT_to_Qlt; apply env_w_pos).
  assert (Hdpos : QltT 0 (env_w n)) by apply env_w_pos.
  assert (Hdpos2q : Qlt 0 (env_w n * (1#2))%Q) by lra.
  assert (Hdpos2 : QltT 0 (env_w n * (1#2))%Q) by (apply Qlt_to_QltT; exact Hdpos2q).
  destruct (reg_same (real_plus (existT (fun u0 : Qseq => cauchy u0) u Hu)
                        (existT (fun u1 : Qseq => cauchy u1) v Hv))
            (env_w n) Hdpos) as [N1 HN1].
  destruct (reg_same (existT (fun u0 : Qseq => cauchy u0) u Hu)
            (env_w n * (1#2))%Q Hdpos2) as [N2 HN2].
  destruct (reg_same (existT (fun u0 : Qseq => cauchy u0) v Hv)
            (env_w n * (1#2))%Q Hdpos2) as [N3 HN3].
  exists (Nat.max N1 (Nat.max N2 (Nat.max N3 (Nat.max N0x N0y)))).
  intros k Hk.
  assert (Hk1 : (N1 <= k)%nat) by lia.
  assert (Hk2 : (N2 <= k)%nat) by lia.
  assert (Hk3 : (N3 <= k)%nat) by lia.
  assert (Hkx : (N0x <= k)%nat) by lia.
  assert (Hky : (N0y <= k)%nat) by lia.
  specialize (HN1 k Hk1). specialize (HN2 k Hk2). specialize (HN3 k Hk3).
  destruct (HN0x k Hkx) as [Hxa Hxb].
  destruct (HN0y k Hky) as [Hya Hyb].
  (* exact 桥：projT1 归约到 reg_of / 逐点 u k + v k *)
  assert (HN1' : Qlt (Qabs (reg_of (real_plus (existT (fun u0 : Qseq => cauchy u0) u Hu)
                                   (existT (fun u1 : Qseq => cauchy u1) v Hv)) k
                          - (u k + v k)%Q))
                   (env_w n)) by (apply QltT_to_Qlt; exact HN1).
  assert (HN2' : Qlt (Qabs (reg_of (existT (fun u0 : Qseq => cauchy u0) u Hu) k - u k))
                   (env_w n * (1#2))%Q) by (apply QltT_to_Qlt; exact HN2).
  assert (HN3' : Qlt (Qabs (reg_of (existT (fun u1 : Qseq => cauchy u1) v Hv) k - v k))
                   (env_w n * (1#2))%Q) by (apply QltT_to_Qlt; exact HN3).
  destruct (env_abs_bounds (reg_of (real_plus (existT (fun u0 : Qseq => cauchy u0) u Hu)
                                   (existT (fun u1 : Qseq => cauchy u1) v Hv)) k)
              (u k + v k)%Q (env_w n) HN1') as [Hs1 Hs2].
  destruct (env_abs_bounds (reg_of (existT (fun u0 : Qseq => cauchy u0) u Hu) k)
              (u k) (env_w n * (1#2))%Q HN2') as [H2l H2r].
  destruct (env_abs_bounds (reg_of (existT (fun u1 : Qseq => cauchy u1) v Hv) k)
              (v k) (env_w n * (1#2))%Q HN3') as [H3l H3r].
  assert (A0x : Qle (lox n) (reg_of (existT (fun u0 : Qseq => cauchy u0) u Hu) k))
    by (apply env_Qle_of_QleT; exact Hxa).
  assert (A0y : Qle (loy n) (reg_of (existT (fun u1 : Qseq => cauchy u1) v Hv) k))
    by (apply env_Qle_of_QleT; exact Hya).
  assert (A1 : Qle (reg_of (existT (fun u0 : Qseq => cauchy u0) u Hu) k) (hix n))
    by (apply env_Qle_of_QleT; exact Hxb).
  assert (A2 : Qle (reg_of (existT (fun u1 : Qseq => cauchy u1) v Hv) k) (hiy n))
    by (apply env_Qle_of_QleT; exact Hyb).
  split.
  - left. apply Qlt_to_QltT. lra.
  - left. apply Qlt_to_QltT. lra.
Qed.

Theorem env_opp_prop : forall (x : Real) (lox hix : nat -> Q),
  env_ok x lox hix ->
  env_ok (real_opp x)
    (fun n => - hix n - 2 * env_w n)%Q
    (fun n => - lox n + 2 * env_w n)%Q.
Proof.
  intros x lox hix Hx.
  destruct x as [u Hu]. intros n.
  destruct (Hx n) as [N0x HN0x].
  assert (Hwp : Qlt 0 (env_w n)) by (apply QltT_to_Qlt; apply env_w_pos).
  assert (Hdpos : QltT 0 (env_w n)) by apply env_w_pos.
  assert (Hdpos2q : Qlt 0 (env_w n * (1#2))%Q) by lra.
  assert (Hdpos2 : QltT 0 (env_w n * (1#2))%Q) by (apply Qlt_to_QltT; exact Hdpos2q).
  destruct (reg_same (real_opp (existT (fun u0 : Qseq => cauchy u0) u Hu))
            (env_w n) Hdpos) as [N1 HN1].
  destruct (reg_same (existT (fun u0 : Qseq => cauchy u0) u Hu)
            (env_w n * (1#2))%Q Hdpos2) as [N2 HN2].
  exists (Nat.max N1 (Nat.max N2 N0x)).
  intros k Hk.
  assert (Hk1 : (N1 <= k)%nat) by lia.
  assert (Hk2 : (N2 <= k)%nat) by lia.
  assert (Hkx : (N0x <= k)%nat) by lia.
  specialize (HN1 k Hk1). specialize (HN2 k Hk2).
  destruct (HN0x k Hkx) as [Hxa Hxb].
  assert (HN1' : Qlt (Qabs (reg_of (real_opp (existT (fun u0 : Qseq => cauchy u0) u Hu)) k
                          - (- u k)%Q))
                   (env_w n)) by (apply QltT_to_Qlt; exact HN1).
  assert (HN2' : Qlt (Qabs (reg_of (existT (fun u0 : Qseq => cauchy u0) u Hu) k - u k))
                   (env_w n * (1#2))%Q) by (apply QltT_to_Qlt; exact HN2).
  destruct (env_abs_bounds (reg_of (real_opp (existT (fun u0 : Qseq => cauchy u0) u Hu)) k)
              (- u k)%Q (env_w n) HN1') as [Hs1 Hs2].
  destruct (env_abs_bounds (reg_of (existT (fun u0 : Qseq => cauchy u0) u Hu) k)
              (u k) (env_w n * (1#2))%Q HN2') as [H2l H2r].
  assert (A0 : Qle (lox n) (reg_of (existT (fun u0 : Qseq => cauchy u0) u Hu) k))
    by (apply env_Qle_of_QleT; exact Hxa).
  assert (A1 : Qle (reg_of (existT (fun u0 : Qseq => cauchy u0) u Hu) k) (hix n))
    by (apply env_Qle_of_QleT; exact Hxb).
  split.
  - left. apply Qlt_to_QltT. lra.
  - left. apply Qlt_to_QltT. lra.
Qed.

(* ---- T2.7 提取与审计 ---- *)

Extraction "rc_envelope_t2.ml" env_w env_lo env_hi env_lt_check reg_of.

Print Assumptions env_contains.
Print Assumptions env_ok_canonical.
Print Assumptions env_witness_complete.
Print Assumptions env_check_sound.
Print Assumptions rc_lt_dec.
Print Assumptions env_plus_prop.
Print Assumptions env_opp_prop.
Print Assumptions env_abs_bounds.
Print Assumptions env_w_le.
Print Assumptions reg_same.
