(* ============================================================
   T2（G-13）：cert_optimize 反射收紧器——probe_g13_certtight_cr.v
   （z 区构造性轨道，2026-08-31——CS-19 松弛链元理论的搜索器变现）

   论文 A §5：「松弛链的每一环（floor-sqrt / Jordan / Dirichlet）都可枚举、
   可单独收紧、可机械组合（cert_optimize 方向，future work）」。本模块把该
   承诺定理化（纯 Q 层 Set + sigT + 可提取）：

     接口化（Set 层）：证书链 = 三层松弛参数 { m, sb, sq : Q }
       （分子上界 m、sin 下界 sb、√ 下界 sq；合成界 rel = m/(sb·sq)，
         域约定：m ≥ 0、sb ≥ 1、sq ≥ 1——比较全走交叉相乘，无除法）
     收紧关系 ref a b（bool）：m_b ≤ m_a ∧ sb_a ≤ sb_b ∧ sq_a ≤ sq_b
     核心定理 1 收紧保序：ref a b ⟹ rel b ≤ rel a（交叉相乘序，三段链）
     核心定理 2 裁定保持：ref a b + check a ⟹ check b
       （「只强化不破坏」——CS-19 M4 checker_preserved 的收紧器实例）
     核心定理 3 贪心收紧器（fold+传递性）：ref cur (tighten cur l) = true
     最终定理（sigT，Set 层）：{ c' & 正性 ∧ ref input c' ∧ check c' }
       ——收紧免费、裁定不丢、输出自带正性证据

   纪律（承 G-9/G-10/G-11）：纯 nat/bool/Q 零经典零 Admitted；ct_ 前缀
   防撞名；E138① 注册 + Close Q/Z scope + %Q 显式（E153-C/E202⑤⑥）。
   依赖：QArith/ZArith/Lia + micromega.Lqa。审计：Print Assumptions 尾部。
   提取：g13_certtight_cr.ml。
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

(* ============ R0：证书链（Set 层数据） ============ *)

Record ct_cert : Type := CtCert { ct_m : Q; ct_sb : Q; ct_sq : Q }.

(* 域约定（bool 可判定）：m ≥ 0、sb ≥ 1、sq ≥ 1 *)
Definition ct_pos (c : ct_cert) : bool :=
  (Qle_bool 0 (ct_m c)) && (Qle_bool 1 (ct_sb c)) && (Qle_bool 1 (ct_sq c)).

(* 收紧关系（bool）：分子更小、两个下界更大 *)
Definition ct_ref (a b : ct_cert) : bool :=
  (Qle_bool (ct_m b) (ct_m a)) && (Qle_bool (ct_sb a) (ct_sb b))
  && (Qle_bool (ct_sq a) (ct_sq b)).

(* 合成界比较：rel b ≤ rel a 的交叉相乘形（无除法） *)
Definition ct_le (a b : ct_cert) : bool :=
  Qle_bool (ct_m b * (ct_sb a * ct_sq a)) (ct_m a * (ct_sb b * ct_sq b)).

(* 阈值裁定：rel c ≤ 4/5 ⟺ 5·m ≤ 4·(sb·sq) *)
Definition ct_check (c : ct_cert) : bool :=
  Qle_bool (5 * ct_m c) (4 * (ct_sb c * ct_sq c)).

(* Qle 互桥 *)
Lemma ct_le_of_bool : forall x y : Q, Qle_bool x y = true -> (x <= y)%Q.
Proof. intros x y H. apply (proj1 (Qle_bool_iff x y)). exact H. Qed.

Lemma ct_bool_of_le : forall x y : Q, (x <= y)%Q -> Qle_bool x y = true.
Proof. intros x y H. apply (proj2 (Qle_bool_iff x y)). exact H. Qed.

(* 左乘单调（stdlib 无 Qmult_le_compat_l——E203 同款绕法） *)
Lemma ct_mult_le_l : forall x y z : Q, (0 <= z)%Q -> (x <= y)%Q -> (z * x <= z * y)%Q.
Proof.
  intros x y z Hz Hxy.
  pose proof (Qmult_le_compat_r x y z Hxy Hz) as H.
  rewrite (Qmult_comm x z) in H. rewrite (Qmult_comm y z) in H.
  exact H.
Qed.

(* 分母链（R1/R2 共用）：下界收紧 ⟹ 分母乘积收紧（两步 Qmult 链） *)
Lemma ct_den_le : forall a b : ct_cert,
  (1 <= ct_sb a)%Q -> (1 <= ct_sq a)%Q ->
  (1 <= ct_sb b)%Q -> (1 <= ct_sq b)%Q ->
  (ct_sb a <= ct_sb b)%Q -> (ct_sq a <= ct_sq b)%Q ->
  (ct_sb a * ct_sq a <= ct_sb b * ct_sq b)%Q.
Proof.
  intros a b Hsa1 Hqa1 Hsb1 Hqb1 Hsb Hsq.
  assert (Hqa0 : (0 <= ct_sq a)%Q) by lra.
  assert (Hsb0 : (0 <= ct_sb b)%Q) by lra.
  apply (Qle_trans (ct_sb a * ct_sq a) (ct_sb b * ct_sq a) (ct_sb b * ct_sq b)).
  - apply (Qmult_le_compat_r (ct_sb a) (ct_sb b) (ct_sq a) Hsb Hqa0).
  - apply (ct_mult_le_l (ct_sq a) (ct_sq b) (ct_sb b) Hsb0 Hsq).
Qed.

(* ============ R1：核心定理 1——收紧保序（三段 Qmult 链） ============ *)

Lemma ct_ref_rel_le : forall a b : ct_cert,
  (0 <= ct_m a)%Q -> (1 <= ct_sb a)%Q -> (1 <= ct_sq a)%Q ->
  (0 <= ct_m b)%Q -> (1 <= ct_sb b)%Q -> (1 <= ct_sq b)%Q ->
  ct_ref a b = true -> ct_le a b = true.
Proof.
  intros a b Hma0 Hsba1 Hsqa1 Hmb0 Hsbb1 Hsqb1 Href.
  unfold ct_ref in Href. apply andb_true_iff in Href as [Href1 Href2].
  apply andb_true_iff in Href1 as [Hm Hsb].
  apply ct_le_of_bool in Hm. apply ct_le_of_bool in Hsb.
  apply ct_le_of_bool in Href2.
  assert (Hden : (ct_sb a * ct_sq a <= ct_sb b * ct_sq b)%Q)
    by (apply ct_den_le; assumption).
  assert (Hpos : (0 <= ct_sb a * ct_sq a)%Q).
  { apply (Qmult_le_0_compat (ct_sb a) (ct_sq a)).
    - lra.
    - lra. }
  unfold ct_le. apply ct_bool_of_le.
  apply (Qle_trans (ct_m b * (ct_sb a * ct_sq a))
                   (ct_m a * (ct_sb a * ct_sq a))
                   (ct_m a * (ct_sb b * ct_sq b))).
  - apply (Qmult_le_compat_r (ct_m b) (ct_m a) (ct_sb a * ct_sq a) Hm Hpos).
  - apply (ct_mult_le_l (ct_sb a * ct_sq a) (ct_sb b * ct_sq b) (ct_m a) Hma0 Hden).
Qed.

(* ============ R2：核心定理 2——裁定保持（三步线性链，无消去） ============ *)

Lemma ct_check_pres : forall a b : ct_cert,
  ct_pos a = true -> ct_pos b = true ->
  ct_ref a b = true -> ct_check a = true -> ct_check b = true.
Proof.
  intros a b Ha Hb Href Hca.
  apply andb_true_iff in Ha as [Ha1 Ha2].
  apply andb_true_iff in Ha1 as [Hma0 Hsba1].
  apply andb_true_iff in Hb as [Hb1 Hb2].
  apply andb_true_iff in Hb1 as [Hmb0 Hsbb1].
  apply ct_le_of_bool in Hma0. apply ct_le_of_bool in Hsba1.
  apply ct_le_of_bool in Ha2. apply ct_le_of_bool in Hmb0.
  apply ct_le_of_bool in Hsbb1. apply ct_le_of_bool in Hb2.
  apply andb_true_iff in Href as [Href1 Href2].
  apply andb_true_iff in Href1 as [Hm Hsb].
  apply ct_le_of_bool in Hm. apply ct_le_of_bool in Hsb.
  apply ct_le_of_bool in Href2.
  assert (Hden : (ct_sb a * ct_sq a <= ct_sb b * ct_sq b)%Q)
    by (apply ct_den_le; assumption).
  unfold ct_check in Hca. apply ct_le_of_bool in Hca.
  unfold ct_check. apply ct_bool_of_le.
  apply (Qle_trans (5 * ct_m b) (5 * ct_m a) (4 * (ct_sb b * ct_sq b))).
  - apply (ct_mult_le_l (ct_m b) (ct_m a) 5).
    + lra.
    + exact Hm.
  - apply (Qle_trans (5 * ct_m a) (4 * (ct_sb a * ct_sq a)) (4 * (ct_sb b * ct_sq b))).
    + exact Hca.
    + apply (ct_mult_le_l (ct_sb a * ct_sq a) (ct_sb b * ct_sq b) 4).
      * lra.
      * exact Hden.
Qed.

(* ============ R3：收紧关系传递 + 自反 ============ *)

Lemma ct_ref_refl : forall c : ct_cert, ct_ref c c = true.
Proof.
  intros c. unfold ct_ref.
  apply andb_true_iff. split.
  - apply andb_true_iff. split.
    + apply ct_bool_of_le. apply Qle_refl.
    + apply ct_bool_of_le. apply Qle_refl.
  - apply ct_bool_of_le. apply Qle_refl.
Qed.

Lemma ct_ref_trans : forall a b c : ct_cert,
  ct_ref a b = true -> ct_ref b c = true -> ct_ref a c = true.
Proof.
  intros a b c H1 H2. unfold ct_ref in H1, H2.
  apply andb_true_iff in H1 as [Hm12 Hq1].
  apply andb_true_iff in Hm12 as [Hm1 Hs1].
  apply andb_true_iff in H2 as [Hm23 Hq23].
  apply andb_true_iff in Hm23 as [Hm2 Hs2].
  apply ct_le_of_bool in Hm1. apply ct_le_of_bool in Hs1.
  apply ct_le_of_bool in Hq1. apply ct_le_of_bool in Hm2.
  apply ct_le_of_bool in Hs2. apply ct_le_of_bool in Hq23.
  unfold ct_ref. apply andb_true_iff. split.
  - apply andb_true_iff. split.
    + apply ct_bool_of_le. lra.
    + apply ct_bool_of_le. lra.
  - apply ct_bool_of_le. lra.
Qed.

(* ============ R4：核心定理 3——贪心收紧器（fold + 传递性） ============ *)

Fixpoint ct_tighten (cur : ct_cert) (l : list ct_cert) : ct_cert :=
  match l with
  | nil => cur
  | c :: t => if andb (ct_ref cur c) (ct_pos c) then ct_tighten c t
              else ct_tighten cur t
  end.

Lemma ct_tighten_ref : forall (l : list ct_cert) (cur : ct_cert),
  ct_ref cur (ct_tighten cur l) = true.
Proof.
  intros l. induction l as [| c t IH]; intros cur; [ simpl; apply ct_ref_refl | ].
  simpl. destruct (andb (ct_ref cur c) (ct_pos c)) eqn:H.
  - apply andb_true_iff in H as [Href _].
    apply (ct_ref_trans cur c (ct_tighten c t)); [exact Href | apply IH].
  - apply IH.
Qed.

Lemma ct_tighten_pos : forall (l : list ct_cert) (cur : ct_cert),
  ct_pos cur = true -> ct_pos (ct_tighten cur l) = true.
Proof.
  intros l. induction l as [| c t IH]; intros cur Hpos.
  - exact Hpos.
  - simpl. destruct (andb (ct_ref cur c) (ct_pos c)) eqn:H.
    + apply andb_true_iff in H as [_ Hpc]. apply IH. exact Hpc.
    + apply IH. exact Hpos.
Qed.

Lemma ct_tighten_check : forall (l : list ct_cert) (cur : ct_cert),
  ct_pos cur = true -> ct_check cur = true ->
  ct_check (ct_tighten cur l) = true.
Proof.
  intros l. induction l as [| c t IH]; intros cur Hpos Hchk.
  - exact Hchk.
  - simpl. destruct (andb (ct_ref cur c) (ct_pos c)) eqn:H.
    + apply andb_true_iff in H as [Href Hpc].
      apply IH.
      * exact Hpc.
      * apply (ct_check_pres cur c Hpos Hpc Href Hchk).
    + apply IH; assumption.
Qed.

(* ============ R5：最终定理（sigT，Set 层收紧证书） ============ *)

Theorem ct_opt_cert (c0 : ct_cert) (l : list ct_cert) :
  ct_pos c0 = true -> ct_check c0 = true ->
  { c' : ct_cert & ct_pos c' = true
              /\ ct_ref c0 c' = true
              /\ ct_check c' = true }.
Proof.
  intros Hpos Hchk. exists (ct_tighten c0 l).
  split; [ apply ct_tighten_pos; exact Hpos | ].
  split; [ apply ct_tighten_ref | ].
  apply ct_tighten_check; assumption.
Qed.

(* ============ 审计 ============ *)
Print Assumptions ct_ref_rel_le.
Print Assumptions ct_check_pres.
Print Assumptions ct_tighten_ref.
Print Assumptions ct_tighten_pos.
Print Assumptions ct_tighten_check.
Print Assumptions ct_opt_cert.

(* ============ 提取（Set 层全可执行——cert_optimize 运行时入口） ============ *)
From Stdlib Require Import Extraction.

Extraction "g13_certtight_cr.ml" ct_pos ct_ref ct_check ct_tighten ct_opt_cert.
