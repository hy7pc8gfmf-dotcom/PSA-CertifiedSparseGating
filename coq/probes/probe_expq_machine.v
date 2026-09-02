(* ============================================================
probe_expq_machine.v —— C7-A：Q 层 exp 部分和窗口机
z 区纯构造性轨道 · C 系列（2026-09-02 启动）
============================================================

使命（推进次序 #1，见 z/交接文档-C3-相干下界孪生启动与推进次序-20260902.md）：
为"注意力扰动轨全构造化"与 T-EXP（TVD 有理常数）提供纯 Q/nat 的 exp 部分和
窗口机：部分和 Fixpoint、逐项差分公式、项非负、单调窗口——结论 Set 层，
可提取 ocamlc。

设计（语义诚实）：
- 本模块只操作有理数：expP(N,x) = Σ_{k≤N} x^k / k!（有理部分和）；
- "实值 exp 的语义界"（收敛/极限/指向 exp）由后续 CR/语义层承担（C7-B 及 CRexp），
  本模块交付可提取的有限窗口计算与单调结构——证明侧零 Reals、零经典；
- 铁律对齐：① 核心结论 Set 层（QleT/QeqT）；② 非平凡核心定理 = 逐项差分公式、
  项非负与单调窗口（量词在前）；③ 终态零 Admitted 零 Axiom；④ Extraction。

依赖：QArith + micromega.Lqa + qset_twin_base（z）。坑卡：E251/E258 适用条目。
============================================================ *)
From Stdlib Require Import QArith.
From Stdlib Require Import micromega.Lqa.
From Stdlib Require Import Lia.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Extraction.
Require Import qset_twin_base.

(* ============ E138①/E259 合并防御块（照抄 qset_twin_base L65-72）============
   合并版内 mathcomp 前序劫持 nat_scope 记号（subn/muln/leq）与 Q 字面量 # 记号
   （ssrnotations 全局前缀 #[ x ]）——本块注册回 Stdlib 形态；独立环境同义覆盖仅 warning *)
Notation "x + y" := (Nat.add x y) : nat_scope.
Notation "x - y" := (Nat.sub x y) : nat_scope.
Notation "x * y" := (Nat.mul x y) : nat_scope.
Notation "x <= y" := (Peano.le x y) : nat_scope.
Notation "x < y" := (Peano.lt x y) : nat_scope.
Notation "x # y" := (Qmake x y) (at level 55, no associativity) : Q_scope.

Local Open Scope Q_scope.

(* ---------- nat → Q 注入 ---------- *)
Definition nq (n : nat) : Q := (Z.of_nat n # 1)%Q.

(* nat 序 → Q 序（Prop 桥；C2 同款：cbn [Qnum Qden] + lia） *)
Lemma nq_le (a b : nat) (Hab : (a <= b)%nat) : Qle (nq a) (nq b).
Proof.
  assert (HZ : (Z.of_nat a <= Z.of_nat b)%Z) by lia.
  unfold nq, Qle. cbn [Qnum Qden]. repeat rewrite Zmult_1_r. exact HZ.
Qed.

Lemma nq_nonneg (i : nat) : Qle 0 (nq i).
Proof.
  assert (HZ : (0 <= Z.of_nat i)%Z) by lia.
  unfold nq, Qle. cbn [Qnum Qden]. repeat rewrite Zmult_1_r. exact HZ.
Qed.

(* 严格正（Prop：Qcompare → Z.compare 展开，同 C2 的 Qle 展开模式） *)
Lemma nq_pos (n : nat) (Hn : (0 < n)%nat) : Qlt 0 (nq n).
Proof.
  destruct n as [| m]; [lia |].
  unfold nq, Qlt. cbn [Qnum Qden]. repeat rewrite Zmult_1_r.
  assert (HZ : (0 < Z.of_nat (S m))%Z) by lia. exact HZ.
Qed.

(* 严格正（Set 抬升） *)
Lemma nq_gt0T (n : nat) (Hn : (0 < n)%nat) : QltT 0 (nq n).
Proof. apply Qlt_to_QltT. apply nq_pos. exact Hn. Qed.

(* ---------- 阶乘与幂 ---------- *)
Fixpoint qfact (k : nat) : Q :=
  match k with 0%nat => 1#1 | S m => nq (S m) * qfact m end.

Fixpoint qpow (x : Q) (k : nat) : Q :=
  match k with 0%nat => 1#1 | S m => x * qpow x m end.

(* exp 项与部分和：Σ_{k ≤ N} x^k / k! *)
Definition expT (k : nat) (x : Q) : Q := qpow x k / qfact k.

Fixpoint expP (N : nat) (x : Q) : Q :=
  match N with 0%nat => expT 0%nat x | S m => expP m x + expT (S m) x end.

(* ---------- 基础：阶乘正 / 幂非负 ---------- *)
Lemma qfact_pos (k : nat) : Qlt 0 (qfact k).
Proof.
  induction k as [| k IH].
  - unfold qfact. lra.
  - simpl. apply (Qmult_lt_0_compat (nq (S k)) (qfact k)).
    + apply QltT_to_Qlt. apply nq_gt0T. lia.
    + exact IH.
Qed.

Lemma qpow_nonneg (x : Q) (k : nat) : Qle 0 x -> Qle 0 (qpow x k).
Proof.
  intros Hx. induction k as [| k IH].
  - simpl. lra.
  - simpl. apply Qmult_le_0_compat; [exact Hx | exact IH].
Qed.

(* Set 层抬升件（提级通道，不含新内容） *)
Lemma qpow_nonnegT : forall (x : Q) (k : nat), QleT 0 x -> QleT 0 (qpow x k).
Proof. intros x k Hx. apply Qle_to_QleT. apply qpow_nonneg. apply QleT_to_Qle. exact Hx. Qed.

Lemma qfact_posT : forall k : nat, QltT 0 (qfact k).
Proof. intros k. apply Qlt_to_QltT. apply qfact_pos. Qed.

Lemma qinv_fact_nonneg : forall k : nat, Qle 0 (/ qfact k).
Proof.
  intros k. apply Qlt_le_weak. apply Qinv_lt_0_compat. apply qfact_pos.
Qed.

(* 项非负（Prop 层证明，Set 层结论） *)
Lemma expT_nonnegT : forall (k : nat) (x : Q), QleT 0 x -> QleT 0 (expT k x).
Proof.
  intros k x Hx. unfold expT. apply Qle_to_QleT.
  apply Qmult_le_0_compat.
  - apply qpow_nonneg. apply QleT_to_Qle. exact Hx.
  - apply qinv_fact_nonneg.
Qed.

(* ---------- 非平凡核心：逐项差分与单调窗口 ---------- *)

(* 逐项差分公式（定义展开） *)
Lemma expP_delta : forall (N : nat) (x : Q), expP (S N) x == expP N x + expT (S N) x.
Proof. intros N x. reflexivity. Qed.

(* 单调窗口：0 ≤ x ⟹ expP N x ≤ expP (S N) x（N 任意、Set 层） *)
Lemma expP_mono_stepT : forall (N : nat) (x : Q), QleT 0 x -> QleT (expP N x) (expP (S N) x).
Proof.
  intros N x Hx.
  apply Qle_to_QleT.
  assert (Ht : Qle 0 (expT (S N) x)) by (apply QleT_to_Qle; apply expT_nonnegT; exact Hx).
  cbn [expP].
  apply (Qle_trans _ (expP N x + 0) _).
  - rewrite Qplus_0_r. apply Qle_refl.
  - apply (Qplus_le_compat (expP N x) (expP N x) 0 (expT (S N) x)).
    + apply Qle_refl.
    + exact Ht.
Qed.

(* 多步单调：m ≤ n ⟹ expP m x ≤ expP n x（归纳 + 传递；非平凡核心之二） *)
Lemma expP_monoT : forall (m n : nat) (x : Q), (m <= n)%nat -> QleT 0 x -> QleT (expP m x) (expP n x).
Proof.
  intros m n x Hmn Hx.
  revert m Hmn. induction n as [| n IH].
  - intros m Hm. destruct m; [apply QleT_refl | lia].
  - intros m Hm. destruct (Nat.eq_dec m (S n)) as [Heq | Hne].
    + subst. apply QleT_refl.
    + assert (Hle : (m <= n)%nat) by lia.
      assert (Hs : QleT (expP n x) (expP (S n) x)) by (apply expP_mono_stepT; exact Hx).
      apply (QleT_trans _ (expP n x) _); [ apply (IH m Hle) | exact Hs ].
Qed.

(* ============ C7-B1：正因子消去与项比率（几何尾前置件） ============ *)

(* Prop 侧正因子消去（stdlib QArith 无现成；CompareSpec 三分 + 严格单调反证） *)
Lemma qle_cancel_pos (a b c : Q) : Qlt 0 c -> Qle (a * c) (b * c) -> Qle a b.
Proof.
  intros Hc Hab.
  destruct (Qcompare_spec a b) as [Heq | Hlt | Hgt].
  - apply (proj2 (Qle_lteq a b)). right. exact Heq.
  - apply (proj2 (Qle_lteq a b)). left. exact Hlt.
  - exfalso. exact (Qle_not_lt (a * c) (b * c) Hab (Qmult_lt_compat_r b a c Hc Hgt)).
Qed.

(* nq (S k) 非零（Qeq 形，Qmult_inv_r 侧条件） *)
Lemma nq_neq0 (k : nat) : ~ nq (S k) == 0.
Proof.
  intro Heq.
  assert (Hp : Qlt 0 (nq (S k))) by (apply nq_pos; lia).
  rewrite Heq in Hp.
  exact (Qle_not_lt 0 0 (Qle_refl 0) Hp).
Qed.

(* nq (S k) 与其逆之积为 1 *)
Lemma qmul_inv_nq_r (k : nat) : nq (S k) * / nq (S k) == 1.
Proof. apply Qmult_inv_r. apply nq_neq0. Qed.

(* 阶乘与 (nq·阶乘) 非零（field 侧条件） *)
Lemma qfact_neq0 (k : nat) : ~ qfact k == 0.
Proof.
  intro H.
  assert (Hp : Qlt 0 (qfact k)) by (apply qfact_pos).
  rewrite H in Hp.
  exact (Qle_not_lt 0 0 (Qle_refl 0) Hp).
Qed.

Lemma qprod_neq0 (k : nat) : ~ (nq (S k) * qfact k) == 0.
Proof.
  intro H.
  assert (Hp : Qlt 0 (nq (S k) * qfact k)).
  { apply Qmult_lt_0_compat; [ apply nq_pos; lia | apply qfact_pos ]. }
  rewrite H in Hp.
  exact (Qle_not_lt 0 0 (Qle_refl 0) Hp).
Qed.

(* 项比率恒等式（乘 nq(S k) 形，免符号除法）：expT (S k) x · nq (S k) == x · expT k x *)
Lemma expT_ratio_ident (k : nat) (x : Q) : expT (S k) x * nq (S k) == x * expT k x.
Proof.
  unfold expT.
  change (qpow x (S k)) with (x * qpow x k).
  change (qfact (S k)) with (nq (S k) * qfact k).
  unfold Qdiv.
  field.
  all: try (split; [ exact (qfact_neq0 k) | exact (nq_neq0 k) ]).
  all: try (exact (qprod_neq0 k)).
  all: try (exact (qfact_neq0 k)).
  all: try (exact (nq_neq0 k)).
Qed.

(* 双倍比率恒等式（field 版）：((2#1)·expT (S k) x) · nq (S k) == (2#1)·(x·expT k x) *)
Lemma expT_ratio_ident2 (k : nat) (x : Q) :
  ((2#1) * expT (S k) x) * nq (S k) == (2#1) * (x * expT k x).
Proof.
  unfold expT.
  change (qpow x (S k)) with (x * qpow x k).
  change (qfact (S k)) with (nq (S k) * qfact k).
  unfold Qdiv.
  field.
  all: try (split; [ exact (qfact_neq0 k) | exact (nq_neq0 k) ]).
  all: try (exact (qprod_neq0 k)).
  all: try (exact (qfact_neq0 k)).
  all: try (exact (nq_neq0 k)).
Qed.

(* 2#1 非零（field/消去侧条件） *)
Lemma qtwo_neq0 : ~ (2#1) == 0.
Proof.
  intro H.
  assert (Hp : Qlt 0 (2#1)) by lra.
  rewrite H in Hp.
  exact (Qle_not_lt 0 0 (Qle_refl 0) Hp).
Qed.

(* 结合律反向件（setoid_replace 侧证用；stdlib 方向为 a·(b·c) == (a·b)·c） *)
Lemma qmul_assoc_rev (a b c : Q) : (a * b) * c == a * (b * c).
Proof. exact (Qeq_sym (a * (b * c)) ((a * b) * c) (Qmult_assoc a b c)). Qed.

(* (1/2)·b·2 == b（消去装配用） *)
Lemma qhalf_mul2 (b : Q) : (((1#2) * b) * (2#1)) == b.
Proof.
  unfold Qdiv. field; try exact qtwo_neq0.
Qed.

(* 项比率半化（C7-B2 核心）：k≥1、0≤x≤1 ⟹ (2#1)·expT (S k) x ≤ expT k x
   装配纪律：== 项重排一律 setoid_replace by exact（plain rewrite 触发 Z 回退，E267） *)
Lemma expT_ratio_halve (k : nat) (x : Q) : (1 <= k)%nat -> Qle 0 x -> Qle x 1
  -> Qle ((2#1) * expT (S k) x) (expT k x).
Proof.
  intros Hk Hx0 Hx1.
  apply (qle_cancel_pos ((2#1) * expT (S k) x) (expT k x) (nq (S k))).
  - apply nq_pos. lia.
  - assert (He0 : Qle 0 (expT k x)) by (apply QleT_to_Qle; apply expT_nonnegT; apply Qle_to_QleT; exact Hx0).
    assert (H2x : Qle ((2#1) * x) (2#1)).
    { setoid_replace ((2#1) * x) with (x * (2#1)) by (exact (Qmult_comm (2#1) x)).
      apply (Qle_trans _ ((1#1) * (2#1)) _).
      - apply (Qmult_le_compat_r x (1#1) (2#1) Hx1). lra.
      - setoid_replace ((1#1) * (2#1)) with (2#1) by (vm_compute; reflexivity).
        apply Qle_refl. }
    setoid_replace (((2#1) * expT (S k) x) * nq (S k)) with ((2#1) * (x * expT k x))
      by (exact (expT_ratio_ident2 k x)).
    setoid_replace ((2#1) * (x * expT k x)) with (((2#1) * x) * expT k x)
      by (exact (Qmult_assoc (2#1) x (expT k x))).
    apply (Qle_trans _ ((2#1) * expT k x) _).
    + apply (Qmult_le_compat_r ((2#1) * x) (2#1) (expT k x) H2x He0).
    + setoid_replace (expT k x * nq (S k)) with (nq (S k) * expT k x)
        by (exact (Qmult_comm (expT k x) (nq (S k)))).
      apply (Qmult_le_compat_r (2#1) (nq (S k)) (expT k x)).
      * change (Qle (nq 2) (nq (S k))). apply nq_le. lia.
      * exact He0.
Qed.

(* ============ C7-B3：hpow((1/2) 幂) 族与几何和上界 ============ *)

Definition hpow (j : nat) : Q := qpow (1#2) j.

(* Σ_{j<K} hpow j *)
Fixpoint sumh (K : nat) : Q :=
  match K with 0%nat => 0 | S m => sumh m + hpow m end.

Lemma qtwo_pos : Qlt 0 (2#1). Proof. lra. Qed.

Lemma qone_mul (x : Q) : (1#1) * x == x. Proof. field. Qed.

Lemma hpow0 : hpow 0 == (1#1). Proof. unfold hpow. reflexivity. Qed.

Lemma hpowS (j : nat) : hpow (S j) == (1#2) * hpow j. Proof. unfold hpow. reflexivity. Qed.

Lemma hpow_nonneg (j : nat) : Qle 0 (hpow j).
Proof. unfold hpow. apply qpow_nonneg. lra. Qed.

Lemma hpow_nonnegT (j : nat) : QleT 0 (hpow j).
Proof. apply Qle_to_QleT. apply hpow_nonneg. Qed.

(* (2#1)·hpow (S j) == hpow j（几何步进的核心恒等式） *)
Lemma hpow_double (j : nat) : (2#1) * hpow (S j) == hpow j.
Proof.
  unfold hpow. change (qpow (1#2) (S j)) with ((1#2) * qpow (1#2) j).
  setoid_replace ((2#1) * ((1#2) * qpow (1#2) j)) with (((2#1) * (1#2)) * qpow (1#2) j)
    by (exact (Qmult_assoc (2#1) (1#2) (qpow (1#2) j))).
  setoid_replace (((2#1) * (1#2)) * qpow (1#2) j) with (qpow (1#2) j)
    by (setoid_replace ((2#1) * (1#2)) with ((1#1)) by (vm_compute; reflexivity);
        exact (qone_mul (qpow (1#2) j))).
  reflexivity.
Qed.

(* hpow 0 · t == t *)
Lemma hpow0_mul (t : Q) : hpow 0 * t == t.
Proof. unfold hpow. exact (qone_mul t). Qed.

(* (1#2)·(hpow j · t) == hpow (S j) · t *)
Lemma hpow_mulS (j : nat) (t : Q) : (1#2) * (hpow j * t) == hpow (S j) * t.
Proof.
  unfold hpow. change (qpow (1#2) (S j)) with ((1#2) * qpow (1#2) j).
  setoid_replace ((1#2) * (qpow (1#2) j * t)) with (((1#2) * qpow (1#2) j) * t)
    by (exact (Qmult_assoc (1#2) (qpow (1#2) j) t)).
  reflexivity.
Qed.

(* 分配律（== 侧证件） *)
Lemma qdistr (a b c : Q) : (a + b) * c == a * c + b * c. Proof. field. Qed.

(* 几何和上界（不变量：sumh K + 2·hpow K ≤ 2） *)
Lemma sumh_bound (K : nat) : sumh K + (2#1) * hpow K <= 2.
Proof.
  induction K as [| K IH].
  - setoid_replace (sumh 0 + (2#1) * hpow 0) with ((2#1))
      by (unfold sumh, hpow; vm_compute; reflexivity).
    apply Qle_refl.
  - setoid_replace (sumh (S K) + (2#1) * hpow (S K)) with (sumh K + (2#1) * hpow K).
    + exact IH.
    + cbn [sumh].
      setoid_replace (hpow K) with ((2#1) * hpow (S K))
        by (exact (Qeq_sym ((2#1) * hpow (S K)) (hpow K) (hpow_double K))).
      field.
Qed.

(* sumh K ≤ 2（窗口上界装配件） *)
Lemma sumh_le2 (K : nat) : sumh K <= 2.
Proof.
  apply (Qle_trans (sumh K) (sumh K + 0) 2).
  - setoid_replace (sumh K + 0) with (sumh K) by (exact (Qplus_0_r (sumh K))).
    apply Qle_refl.
  - apply (Qle_trans _ (sumh K + (2#1) * hpow K) _).
    + apply (Qplus_le_compat (sumh K) (sumh K) 0 ((2#1) * hpow K)).
      * apply Qle_refl.
      * apply Qmult_le_0_compat; [ lra | apply hpow_nonneg ].
    + exact (sumh_bound K).
Qed.

(* ============ C7-B4：几何尾窗口（expTail ≤ 2·首项） ============ *)

(* expTail k L x = Σ_{i<L} expT (k + i) x *)
Fixpoint expTail (k : nat) (L : nat) (x : Q) : Q :=
  match L with 0%nat => 0 | S m => expTail k m x + expT (k + m) x end.

(* 从 (2#1)·e_{S k} ≤ e_k 到 e_{S k} ≤ (1#2)·e_k（qle_cancel_pos + 半化） *)
Lemma halve_div2 (k : nat) (x : Q) : (1 <= k)%nat -> Qle 0 x -> Qle x 1
  -> Qle (expT (S k) x) ((1#2) * expT k x).
Proof.
  intros Hk Hx0 Hx1.
  apply (qle_cancel_pos (expT (S k) x) ((1#2) * expT k x) (2#1)).
  - exact qtwo_pos.
  - setoid_replace (expT (S k) x * (2#1)) with ((2#1) * expT (S k) x)
      by (exact (Qmult_comm (expT (S k) x) (2#1))).
    setoid_replace (((1#2) * expT k x) * (2#1)) with (expT k x)
      by (exact (qhalf_mul2 (expT k x))).
    exact (expT_ratio_halve k x Hk Hx0 Hx1).
Qed.

(* 逐项几何界：expT (N+1+j) x ≤ hpow j · expT (N+1) x *)
Lemma term_hpow_le (N j : nat) (x : Q) : Qle 0 x -> Qle x 1
  -> Qle (expT (N + 1 + j) x) (hpow j * expT (N + 1) x).
Proof.
  intros Hx0 Hx1. induction j as [| j IH].
  - replace (N + 1 + 0)%nat with (N + 1)%nat by lia.
    setoid_replace (hpow 0 * expT (N + 1) x) with (expT (N + 1) x)
      by (exact (hpow0_mul (expT (N + 1) x))).
    apply Qle_refl.
  - replace (N + 1 + S j)%nat with (S (N + 1 + j))%nat by lia.
    assert (Hh : Qle (expT (S (N + 1 + j)) x) ((1#2) * expT (N + 1 + j) x)).
    { apply halve_div2; [ lia | exact Hx0 | exact Hx1 ]. }
    apply (Qle_trans _ ((1#2) * expT (N + 1 + j) x) _).
    + exact Hh.
    + assert (Hm : Qle (expT (N + 1 + j) x * (1#2))
                     ((hpow j * expT (N + 1) x) * (1#2))).
      { apply (Qmult_le_compat_r (expT (N + 1 + j) x) (hpow j * expT (N + 1) x) (1#2) IH). lra. }
      setoid_replace ((1#2) * expT (N + 1 + j) x) with (expT (N + 1 + j) x * (1#2))
        by (exact (Qmult_comm (1#2) (expT (N + 1 + j) x))).
      apply (Qle_trans _ ((hpow j * expT (N + 1) x) * (1#2)) _).
      * exact Hm.
      * setoid_replace ((hpow j * expT (N + 1) x) * (1#2))
          with ((1#2) * (hpow j * expT (N + 1) x))
          by (exact (Qmult_comm (hpow j * expT (N + 1) x) (1#2))).
        setoid_replace ((1#2) * (hpow j * expT (N + 1) x)) with (hpow (S j) * expT (N + 1) x)
          by (exact (hpow_mulS j (expT (N + 1) x))).
        apply Qle_refl.
Qed.

(* 窗口 ≤ sumh(L)·首项（归纳装配） *)
Lemma window_le_sum (N L : nat) (x : Q) : Qle 0 x -> Qle x 1
  -> Qle (expTail (N + 1) L x) (sumh L * expT (N + 1) x).
Proof.
  intros Hx0 Hx1. induction L as [| L IH].
  - simpl.
    setoid_replace (sumh 0 * expT (N + 1) x) with 0 by (unfold sumh; field).
    apply Qle_refl.
  - change (expTail (N + 1) (S L) x)
      with (expTail (N + 1) L x + expT (N + 1 + L) x).
    apply (Qle_trans _ (sumh L * expT (N + 1) x + hpow L * expT (N + 1) x) _).
    + apply (Qplus_le_compat (expTail (N + 1) L x) (sumh L * expT (N + 1) x)
                             (expT (N + 1 + L) x) (hpow L * expT (N + 1) x)).
      * exact IH.
      * apply (term_hpow_le N L x Hx0 Hx1).
    + setoid_replace (sumh L * expT (N + 1) x + hpow L * expT (N + 1) x)
        with ((sumh L + hpow L) * expT (N + 1) x)
        by (exact (Qeq_sym ((sumh L + hpow L) * expT (N + 1) x)
                           (sumh L * expT (N + 1) x + hpow L * expT (N + 1) x)
                           (qdistr (sumh L) (hpow L) (expT (N + 1) x)))).
      setoid_replace ((sumh L + hpow L) * expT (N + 1) x)
        with (sumh (S L) * expT (N + 1) x) by reflexivity.
      apply Qle_refl.
Qed.

(* 窗口上界（Set 层最终定理）：expTail (N+1) L x ≤ (2#1)·expT (N+1) x *)
Lemma window_bound (N L : nat) (x : Q) : QleT 0 x -> QleT x 1
  -> QleT (expTail (N + 1) L x) ((2#1) * expT (N + 1) x).
Proof.
  intros Hx0 Hx1. apply Qle_to_QleT.
  apply (Qle_trans (expTail (N + 1) L x) (sumh L * expT (N + 1) x) ((2#1) * expT (N + 1) x)).
  - apply window_le_sum; [ apply QleT_to_Qle; exact Hx0 | apply QleT_to_Qle; exact Hx1 ].
  - assert (He : Qle 0 (expT (N + 1) x)) by (apply QleT_to_Qle; apply expT_nonnegT; exact Hx0).
    apply (Qmult_le_compat_r (sumh L) (2#1) (expT (N + 1) x)).
    + exact (sumh_le2 L).
    + exact He.
Qed.

(* ============ C7-B5：括号定理与数值决策实例 ============ *)

(* expP 分裂：expP (N+d) == expP N + expTail (N+1) d *)
Lemma expP_split (N d : nat) (x : Q) :
  expP (N + d) x == expP N x + expTail (N + 1) d x.
Proof.
  induction d as [| d IH].
  - replace (N + 0)%nat with N%nat by lia.
    setoid_replace (expTail (N + 1) 0 x) with 0 by reflexivity.
    setoid_replace (expP N x + 0) with (expP N x) by (exact (Qplus_0_r (expP N x))).
    reflexivity.
  - replace (N + S d)%nat with (S (N + d))%nat by lia.
    change (expP (S (N + d)) x) with (expP (N + d) x + expT (S (N + d)) x).
    change (expTail (N + 1) (S d) x) with (expTail (N + 1) d x + expT (N + 1 + d) x).
    setoid_replace (expT (S (N + d)) x) with (expT (N + 1 + d) x)
      by (replace (S (N + d))%nat with (N + 1 + d)%nat by lia; reflexivity).
    setoid_replace (expP (N + d) x) with (expP N x + expTail (N + 1) d x) by (exact IH).
    setoid_replace ((expP N x + expTail (N + 1) d x) + expT (N + 1 + d) x)
      with (expP N x + (expTail (N + 1) d x + expT (N + 1 + d) x))
      by (exact (Qeq_sym (expP N x + (expTail (N + 1) d x + expT (N + 1 + d) x))
                         ((expP N x + expTail (N + 1) d x) + expT (N + 1 + d) x)
                         (Qplus_assoc (expP N x) (expTail (N + 1) d x) (expT (N + 1 + d) x)))).
    reflexivity.
Qed.

(* 上括号（Set）：0≤x≤1、N≤M ⟹ expP M ≤ expP N + 2·expT (N+1) *)
Lemma expP_upper (N M : nat) (x : Q) : QleT 0 x -> QleT x 1 -> (N <= M)%nat
  -> QleT (expP M x) (expP N x + (2#1) * expT (N + 1) x).
Proof.
  intros Hx0 Hx1 HNM. apply Qle_to_QleT.
  setoid_replace (expP M x) with (expP N x + expTail (N + 1) (M - N) x)
    by (replace M%nat with (N + (M - N))%nat by lia;
        replace (N + (M - N) - N)%nat with (M - N)%nat by lia;
        exact (expP_split N (M - N) x)).
  apply (Qplus_le_compat (expP N x) (expP N x)
                         (expTail (N + 1) (M - N) x) ((2#1) * expT (N + 1) x)).
  - apply Qle_refl.
  - apply QleT_to_Qle. apply window_bound. exact Hx0. exact Hx1.
Qed.

(* 数值决策实例与冒烟（vm_compute 判定封口） *)
Lemma expq_smoke_mono_bool : Qle_bool (expP 8 (1#2)) (expP 10 (1#2)) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma expq_smoke_upper_bool :
  Qle_bool (expP 10 (1#2)) ((expP 8 (1#2)) + (2#1) * expT 9 (1#2)) = true.
Proof. vm_compute. reflexivity. Qed.

(* 实例 corollary：x=1/2、N=8 的 ∀M 上括号 *)
Theorem expq_cert_12 (M : nat) (HM : (8 <= M)%nat) :
  QleT (expP M (1#2)) ((expP 8 (1#2)) + (2#1) * expT 9 (1#2)).
Proof.
  apply (expP_upper 8 M (1#2)).
  - apply Qle_to_QleT. lra.
  - apply Qle_to_QleT. lra.
  - exact HM.
Qed.

(* ============ C7-C：x 单调族与 [0,1] 均匀上界（T-EXP 引用件） ============ *)

(* qpow 单调：0≤x≤y ⟹ x^k ≤ y^k *)
Lemma qpow_le_mono (x y : Q) (k : nat) : Qle 0 x -> Qle x y -> Qle (qpow x k) (qpow y k).
Proof.
  intros Hx0 Hxy. induction k as [| k IH].
  - simpl. apply Qle_refl.
  - simpl. apply (Qle_trans _ (y * qpow x k) _).
    + apply (Qmult_le_compat_r x y (qpow x k) Hxy). apply qpow_nonneg. exact Hx0.
    + setoid_replace (y * qpow x k) with (qpow x k * y) by (exact (Qmult_comm y (qpow x k))).
      apply (Qle_trans _ (qpow y k * y) _).
      * apply (Qmult_le_compat_r (qpow x k) (qpow y k) y IH).
        apply (Qle_trans 0 x y Hx0 Hxy).
      * setoid_replace (qpow y k * y) with (y * qpow y k) by (exact (Qmult_comm (qpow y k) y)).
        apply Qle_refl.
Qed.

(* 项单调：0≤x≤y ⟹ expT k x ≤ expT k y *)
Lemma expT_le_x (k : nat) (x y : Q) : Qle 0 x -> Qle x y -> Qle (expT k x) (expT k y).
Proof.
  intros Hx0 Hxy. unfold expT.
  apply (Qmult_le_compat_r (qpow x k) (qpow y k) (/ qfact k)).
  - apply qpow_le_mono. exact Hx0. exact Hxy.
  - apply qinv_fact_nonneg.
Qed.

(* 部分和单调于 x：0≤x≤y ⟹ expP N x ≤ expP N y *)
Lemma expP_le_x (N : nat) (x y : Q) : Qle 0 x -> Qle x y -> Qle (expP N x) (expP N y).
Proof.
  intros Hx0 Hxy. induction N as [| N IH].
  - simpl. apply Qle_refl.
  - cbn [expP]. apply (Qplus_le_compat (expP N x) (expP N y) (expT (S N) x) (expT (S N) y)).
    + exact IH.
    + apply expT_le_x. exact Hx0. exact Hxy.
Qed.

(* x=1 处上界：M≥1 ⟹ expP M 1 ≤ 3（经窗口括号，RHS 闭式） *)
Lemma expq_one_le3 (M : nat) : (1 <= M)%nat -> Qle (expP M (1#1)) (3#1).
Proof.
  intros HM.
  apply (Qle_trans (expP M (1#1)) ((expP 1 (1#1)) + (2#1) * expT 2 (1#1)) (3#1)).
  - apply QleT_to_Qle. apply (expP_upper 1 M (1#1)).
    + apply Qle_to_QleT. lra.
    + apply Qle_to_QleT. lra.
    + exact HM.
  - setoid_replace ((expP 1 (1#1)) + (2#1) * expT 2 (1#1)) with ((3#1)) by (vm_compute; reflexivity).
    apply Qle_refl.
Qed.

(* 均匀上界（Set 最终定理）：0≤x≤1 ⟹ expP N x ≤ 3（T-EXP/TVD 直接引用） *)
Lemma expq_uniform3 (N : nat) (x : Q) : QleT 0 x -> QleT x 1 -> QleT (expP N x) (3#1).
Proof.
  intros Hx0 Hx1. destruct N as [| p].
  - apply Qle_to_QleT.
    setoid_replace (expP 0 x) with ((1#1)) by (vm_compute; reflexivity).
    lra.
  - apply Qle_to_QleT.
    apply (Qle_trans (expP (S p) x) (expP (S p) (1#1)) (3#1)).
    + apply expP_le_x; [ apply QleT_to_Qle; exact Hx0 | apply QleT_to_Qle; exact Hx1 ].
    + apply expq_one_le3. lia.
Qed.

(* ============ 提取与审计（铁律 ③④） ============ *)
Extraction "expq_machine.ml" expP expT qfact qpow.

Print Assumptions qpow_nonnegT.
Print Assumptions expT_nonnegT.
Print Assumptions expP_mono_stepT.
Print Assumptions expP_monoT.
Print Assumptions qle_cancel_pos.
Print Assumptions expT_ratio_ident.
Print Assumptions expT_ratio_ident2.
Print Assumptions expT_ratio_halve.
Print Assumptions term_hpow_le.
Print Assumptions window_bound.
Print Assumptions expP_split.
Print Assumptions expP_upper.
Print Assumptions expq_cert_12.
Print Assumptions expP_le_x.
Print Assumptions expq_uniform3.
