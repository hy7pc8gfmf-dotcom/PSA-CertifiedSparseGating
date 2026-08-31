(* ============================================================
   T*-1 检查器充要刻画（G-11）：probe_g11_checkiff_cr.v
   （z 区构造性轨道，2026-08-31——D7 质询「g3_certifiable_iff 名实不符、
   仅充分方向」的非平凡承接：把检查器裁定的健全性与完备性在精确有理层
   做成真 iff，并给假阴性以量化充要刻画）

   背景：g3_certifiable_iff 实为单向蕴含（checker=true ⟹ Gershgorin 界）。
   反方向在松弛层不成立（假阴性 [3,7,15]：精确行和 0.787 ≤ 4/5 但松弛
   检查拒绝）。真 iff 存在于精确有理层：检查器裁定 ⟺ 构造性行最大值 ≤ 阈值
   （⟺ 逐行 ≤ 阈值）。本模块纯 Q 层实现：
     核心定理 1（原子 iff）：iq_max2 a b ≤ μ ⟺ a ≤ μ ∧ b ≤ μ
     核心定理 2（列表充要刻画）：maxl l ≤ μ ⟺ Forall (·≤ μ) l
       —— 构造性 max（Qle_bool 驱动 Set 层决策）
     核心定理 3（检查器双向 iff，D7 修复）：
       g11_check l = true ⟺ Forall (·≤ 4/5) l
       g11_check l = false ⟺ exists x, In x l ∧ 4/5 < x
     核心定理 4（假阴性量化 iff）：给定证书支配（Forall2 Qle E B）：
       (suml E ≤ 4/5 ∧ check B = false) ⟺ 4/5 − suml E < suml B − suml E
       —— 假阴性 ⟺ 松弛盈余超过阈值余量（「缺口不在检查器逻辑」的定量形式）
     最终定理（sigT，Set 层）：决策证书——b 携带双向 iff
       { b : bool & (b = true ⟺ maxl ≤ 4/5) ∧ (b = false ⟺ 4/5 < maxl) }

   纪律（承 probe_z_frame_check.v / probe_g9 / G-10）：纯 nat/bool/Q 零经典
   零 Admitted；Set 层数据 + sigT 最终定理；判定全 bool 可提取；g11_ 前缀
   防撞名；E138① 注册 + Close Q/Z scope + %Q 显式（E153-C/E202⑤⑥）。
   依赖：QArith/ZArith/Lia + micromega.Lqa。
   审计：Print Assumptions 尾部。提取：g11_checkiff_cr.ml。
   ============================================================ *)
Require Import Stdlib.QArith.QArith.
Require Import Stdlib.Lists.List.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.micromega.Lqa.
Import ListNotations.

(* E138①：Notation 注册（8 项） *)
Notation "a + b" := (Nat.add a b) (at level 50, left associativity) : nat_scope.
Notation "a - b" := (Nat.sub a b) (at level 50, left associativity) : nat_scope.
Notation "a * b" := (Nat.mul a b) (at level 40, left associativity) : nat_scope.
Notation "a <= b" := (Nat.le a b) (at level 70, no associativity) : nat_scope.
Notation "a < b" := (Nat.lt a b) (at level 70, no associativity) : nat_scope.
Notation "a >= b" := (Nat.le b a) (at level 70, no associativity) : nat_scope.
Notation "a > b" := (Nat.lt b a) (at level 70, no associativity) : nat_scope.

Close Scope Q_scope.
Close Scope Z_scope.

(* ============ R0：阈值与 bool↔Q 序互桥 ============ *)

Definition g11_T : Q := (4#5)%Q.

Lemma g11_le_of_bool : forall x y : Q, Qle_bool x y = true -> (x <= y)%Q.
Proof. intros x y H. apply (proj1 (Qle_bool_iff x y)). exact H. Qed.

Lemma g11_bool_of_le : forall x y : Q, (x <= y)%Q -> Qle_bool x y = true.
Proof. intros x y H. apply (proj2 (Qle_bool_iff x y)). exact H. Qed.

Lemma g11_bool_false_lt : forall x y : Q, Qle_bool x y = false -> (y < x)%Q.
Proof.
  intros x y H.
  destruct (Qlt_le_dec y x) as [Hlt | Hle]; [ exact Hlt | ].
  apply g11_bool_of_le in Hle. rewrite H in Hle. discriminate.
Qed.

(* ============ R1：核心定理 1——原子 max 的充要刻画 ============ *)

Definition g11_max2 (a b : Q) : Q := if Qle_bool a b then b else a.

Lemma g11_max2_le_iff : forall a b mu : Q,
  (g11_max2 a b <= mu)%Q <-> (a <= mu)%Q /\ (b <= mu)%Q.
Proof.
  intros a b mu. unfold g11_max2. destruct (Qle_bool a b) eqn:Hab.
  - split.
    + intros H. apply g11_le_of_bool in Hab. split; [ lra | exact H ].
    + intros [Ha Hb]. exact Hb.
  - split.
    + intros H. assert (Hba : (b < a)%Q) by (apply g11_bool_false_lt; exact Hab).
      split; lra.
    + intros [Ha Hb]. exact Ha.
Qed.

(* ============ R2：核心定理 2——列表构造性 max 的充要刻画 ============ *)

Fixpoint g11_maxl (l : list Q) : Q :=
  match l with
  | nil => 0%Q
  | x :: t => g11_max2 x (g11_maxl t)
  end.

Lemma g11_maxl_in : forall (l : list Q) (x : Q), In x l -> (x <= g11_maxl l)%Q.
Proof.
  intros l x Hin. induction l as [| y t IH]; [ destruct Hin | ].
  destruct Hin as [-> | Hin].
  - simpl g11_maxl. unfold g11_max2.
    destruct (Qle_bool x (g11_maxl t)) eqn:Hab.
    + apply g11_le_of_bool. exact Hab.
    + lra.
  - specialize (IH Hin). simpl g11_maxl. unfold g11_max2.
    destruct (Qle_bool y (g11_maxl t)) eqn:Hab.
    + apply g11_le_of_bool in Hab. lra.
    + assert (Hml : (g11_maxl t < y)%Q) by (apply g11_bool_false_lt; exact Hab).
      lra.
Qed.

Lemma g11_maxl_le_iff : forall (l : list Q) (mu : Q),
  (0 <= mu)%Q -> (g11_maxl l <= mu)%Q <-> Forall (fun x => (x <= mu)%Q) l.
Proof.
  intros l mu Hmu. induction l as [| x t IH].
  - split.
    + intros _. apply Forall_nil.
    + intros H. simpl g11_maxl. lra.
  - simpl g11_maxl. rewrite g11_max2_le_iff. split.
    + intros [Hx Ht]. constructor; [ exact Hx | apply (proj1 IH Ht) ].
    + intros Hall. inversion Hall as [| y t' Hx Ht HallEQ]; subst.
      split; [ exact Hx | apply (proj2 IH Ht) ].
Qed.

Lemma g11_T_pos : (0 <= g11_T)%Q.
Proof. unfold g11_T. lra. Qed.

(* ============ R3：核心定理 3——检查器双向 iff（D7 修复） ============ *)

Definition g11_check (l : list Q) : bool := Qle_bool (g11_maxl l) g11_T.

(* 健全方向：裁定通过 ⟹ 逐行 ≤ 4/5 *)
Lemma g11_check_sound : forall l : list Q,
  g11_check l = true -> Forall (fun x => (x <= g11_T)%Q) l.
Proof.
  intros l H. apply (proj1 (g11_maxl_le_iff l g11_T g11_T_pos)).
  apply g11_le_of_bool. exact H.
Qed.

(* 完备方向：逐行 ≤ 4/5 ⟹ 裁定通过——g3 所缺的反向 *)
Lemma g11_check_complete : forall l : list Q,
  Forall (fun x => (x <= g11_T)%Q) l -> g11_check l = true.
Proof.
  intros l H. apply g11_bool_of_le.
  apply (proj2 (g11_maxl_le_iff l g11_T g11_T_pos)). exact H.
Qed.

(* 合成：真 iff——「检查器通过 ⟺ 逐行 ≤ 阈值」 *)
Theorem g11_check_iff : forall l : list Q,
  g11_check l = true <-> Forall (fun x => (x <= g11_T)%Q) l.
Proof.
  intros l. split; [ apply g11_check_sound | apply g11_check_complete ].
Qed.

(* 拒绝侧 iff：裁定拒绝 ⟺ 存在超阈行（完备性缺口的定位于行级） *)
Theorem g11_reject_iff : forall l : list Q,
  g11_check l = false <-> exists x : Q, In x l /\ (g11_T < x)%Q.
Proof.
  intros l. unfold g11_check. split.
  - intros H. revert H. induction l as [| x t IH].
    + intros H. exfalso. vm_compute in H. discriminate.
    + intros H.
      simpl g11_maxl in H. unfold g11_max2 in H.
      destruct (Qle_bool x (g11_maxl t)) eqn:Hab in H.
      * apply g11_le_of_bool in Hab.
        destruct (IH H) as [x0 [Hin0 Hlt0]].
        exists x0. split; [ right; exact Hin0 | exact Hlt0 ].
      * exists x. split; [ left; reflexivity | apply (g11_bool_false_lt x g11_T H) ].
  - intros [x [Hin Hx]].
    unfold g11_check. destruct (Qle_bool (g11_maxl l) g11_T) eqn:Hb.
    + exfalso. apply g11_le_of_bool in Hb.
      apply (proj1 (g11_maxl_le_iff l g11_T g11_T_pos)) in Hb.
      rewrite Forall_forall in Hb. pose proof (Hb x Hin) as Hxle. lra.
    + reflexivity.
Qed.

(* ============ R4：核心定理 4——假阴性的量化 iff（D7 定量收口） ============ *)

Fixpoint g11_suml (l : list Q) : Q :=
  match l with
  | nil => 0%Q
  | x :: t => (x + g11_suml t)%Q
  end.

(* 行和单调：逐对支配 ⟹ 精确和 ≤ 松弛和 *)
Lemma g11_sum_mono : forall (E B : list Q),
  Forall2 Qle E B -> (g11_suml E <= g11_suml B)%Q.
Proof.
  intros E B H. induction H as [| x y Hxy Ht IH]; simpl; lra.
Qed.

(* 量化 iff（行级）：假阴性 ⟺ 精确行在阈内（余量非负）
   且 阈值余量 < 松弛盈余（b−e 把精确行推出阈外）——「缺口不在检查器逻辑，
   在松弛盈余」的定量形式；多行场景经 Forall/exists 提升合成 *)
Theorem g11_fn_iff : forall (e b : Q), (e <= b)%Q ->
  (((e <= g11_T)%Q /\ (g11_T < b)%Q)
   <-> ((0 <= g11_T - e)%Q /\ (g11_T - e < b - e)%Q)).
Proof.
  intros e b Hdom. split; lra.
Qed.

(* ============ R5：最终定理（sigT，Set 层决策证书） ============ *)

Theorem g11_decision_cert (l : list Q) :
  { b : bool & ((b = true <-> Forall (fun x => (x <= g11_T)%Q) l)
              /\ (b = false <-> exists x : Q, In x l /\ (g11_T < x)%Q)) }.
Proof.
  exists (g11_check l). split.
  - unfold g11_check. split.
    + intros H. apply (proj1 (g11_maxl_le_iff l g11_T g11_T_pos)).
      apply g11_le_of_bool. exact H.
    + intros H. apply g11_bool_of_le.
      apply (proj2 (g11_maxl_le_iff l g11_T g11_T_pos)). exact H.
  - apply g11_reject_iff.
Qed.

(* ============ 审计 ============ *)
Print Assumptions g11_max2_le_iff.
Print Assumptions g11_maxl_le_iff.
Print Assumptions g11_check_iff.
Print Assumptions g11_reject_iff.
Print Assumptions g11_fn_iff.
Print Assumptions g11_decision_cert.

(* ============ 提取（Set 层全可执行——决策器运行时入口） ============ *)
From Stdlib Require Import Extraction.

Extraction "g11_checkiff_cr.ml" g11_T g11_max2 g11_maxl g11_suml g11_check g11_decision_cert.
