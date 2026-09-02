(* ============================================================
probe_collision_qtw.v —— C6：碰撞最小 lag 数论孪生（Z 层）
z 区纯构造性轨道 · C 系列（2026-09-02 启动）
============================================================

使命（推进次序 #3，见 z/交接文档-C3-相干下界孪生启动与推进次序-20260902.md）：
旋转阶梯通道对 (n,m)（θ_n = 2π/n, θ_m = 2π/m，整数波长 n<m）在 lag d 处"碰撞"
（d·(1/n − 1/m) ∈ ℤ ⟺ n·m | d·(m−n)）的最小正 lag 的数论刻画：
  d_min = (n·m) / gcd(n·m, m−n)
本模块（C6 核心，纯 Z 层，零 Reals 零经典）：
- 共素（gcd(prod,dif)=1）情形的 iff 刻画与最小性 sigT——多数几何阶梯对
  （[3,13]、[7,15]、[13,53]、[53,213] …）即属此情形；
- 广义情形（2026-09-02 续）：g_char（g 分解 iff，Z.gcd_div_gcd 装配）、
  g_sig（d_min = prod/g = cx 的最小性 sigT）、cx_cop（g=1 时回落共素特例）。
铁律对齐：① 核心结论 Set/Prop 判定可提取（Z 整除性全部可计算）；
② 非平凡核心定理 = z_euclid（Euclid 引理）+ cop_char（iff）+ cop_sig（最小性 sigT）
  + g_char/g_sig（广义装配）；
③ 零 Admitted 零 Axiom；④ Extraction。
============================================================ *)
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Extraction.
From Stdlib Require Import Znumtheory.

Local Open Scope Z_scope.

(* ============ E138①/E259 合并防御块（nat 五行；纯 Z 文件无 Q 字面量，# 行省略）==== *)
Notation "x + y" := (Nat.add x y) : nat_scope.
Notation "x - y" := (Nat.sub x y) : nat_scope.
Notation "x * y" := (Nat.mul x y) : nat_scope.
Notation "x <= y" := (Peano.le x y) : nat_scope.
Notation "x < y" := (Peano.lt x y) : nat_scope.

(* ---------- 基本件 ---------- *)
Definition zc_prod (n m : Z) : Z := n * m.
Definition zc_dif (n m : Z) : Z := m - n.

Lemma zc_prod_pos (n m : Z) : 0 < n -> 0 < m -> 0 < zc_prod n m.
Proof.
  intros Hn Hm. unfold zc_prod.
  assert (H1n : 1 <= n) by lia.
  assert (Hmn : 1 * m <= n * m) by (apply Z.mul_le_mono_nonneg_r; lia).
  lia.
Qed.

Lemma zc_dif_pos (n m : Z) : 0 < n -> n < m -> 0 < zc_dif n m.
Proof. intros Hn Hlt. unfold zc_dif. lia. Qed.

(* ---------- Euclid 引理（核心一）：gcd x y = 1、x | d·y ⟹ x | d ---------- *)
Lemma z_euclid (x y d : Z) : Z.gcd x y = 1 -> (x | d * y) -> (x | d).
Proof.
  intros Hg Hdiv. destruct Hdiv as [k Hk].
  pose proof (Z.gcd_bezout x y 1 Hg) as Hb.
  destruct Hb as [u [v Heq]].
  exists (d * u + v * k).
  assert (Hone1 : d = d * (u * x + v * y)).
  { setoid_rewrite <- (Z.mul_1_r d) at 1. rewrite <- Heq. reflexivity. }
  setoid_rewrite Hone1 at 1.
  rewrite (Z.mul_add_distr_l d (u * x) (v * y)).
  assert (Ha : d * (u * x) + v * (d * y) = (d * u + v * k) * x).
  { rewrite Hk. ring. }
  assert (Hcv : d * (v * y) = v * (d * y)) by ring.
  rewrite Hcv. exact Ha.
Qed.

(* ---------- 共素 iff 刻画（核心二）---------- *)
Lemma cop_char (n m d : Z) : 0 < n -> n < m -> Z.gcd (n * m) (m - n) = 1
  -> ((n * m | d * (m - n)) <-> (n * m | d)).
Proof.
  intros Hn Hlt Hg. split.
  - intro Hc. eapply z_euclid; [ exact Hg | exact Hc ].
  - intro Hd. destruct Hd as [q Hq].
    exists (q * (m - n)).
    rewrite Hq. ring.
Qed.

(* 最小性（共素）：0<t、(prod | t·dif) ⟹ prod ≤ t *)
Lemma cop_min_ge (n m t : Z) : 0 < n -> n < m -> Z.gcd (n * m) (m - n) = 1
  -> 0 < t -> (n * m | t * (m - n)) -> n * m <= t.
Proof.
  intros Hn Hlt Hg Htpos Hdiv.
  assert (Hprod : 0 < n * m) by (apply zc_prod_pos; lia).
  assert (Hd : (n * m | t)) by (apply (proj1 (cop_char n m t Hn Hlt Hg)); exact Hdiv).
  destruct Hd as [k Hk].
  assert (Hkpos : 0 < k).
  { apply (proj1 (Z.mul_pos_cancel_r k (n * m) Hprod)).
    rewrite <- Hk. exact Htpos. }
  assert (Hk1 : 1 <= k) by lia.
  rewrite Hk.
  assert (Hle : 1 * (n * m) <= k * (n * m))
    by (apply Z.mul_le_mono_nonneg_r; [ lia | exact Hk1 ]).
  lia.
Qed.

(* ---------- 最小 lag sigT（共素，核心三/最终定理）---------- *)
Theorem cop_sig (n m : Z) : 0 < n -> n < m -> Z.gcd (n * m) (m - n) = 1
  -> { d : Z & (0 < d) /\ (n * m | d * (m - n)) /\
       (forall t : Z, 0 < t -> (n * m | t * (m - n)) -> d <= t) }.
Proof.
  intros Hn Hlt Hg.
  exists (n * m).
  split; [ | split ].
  - apply zc_prod_pos; lia.
  - exists (m - n). ring.
  - intros t Htpos Hdiv. apply (cop_min_ge n m t Hn Hlt Hg Htpos Hdiv).
Qed.

(* ---------- 广义装配件：d_min = prod / g（split/互素；iff+sigT 下一轮接装） ---------- *)
Definition cg (n m : Z) : Z := Z.gcd (n * m) (m - n).
Definition cx (n m : Z) : Z := (n * m) / cg n m.
Definition cy (n m : Z) : Z := (m - n) / cg n m.

Lemma cg_pos (n m : Z) : 0 < n -> n < m -> 0 < cg n m.
Proof.
  intros Hn Hlt. unfold cg.
  assert (Hnn : 0 <= Z.gcd (n * m) (m - n)) by apply Z.gcd_nonneg.
  destruct (Z.eq_dec (Z.gcd (n * m) (m - n)) 0) as [Hz | Hnz].
  - exfalso.
    assert (Hprod : 0 < n * m) by (apply zc_prod_pos; lia).
    apply (proj1 (Z.gcd_eq_0 (n * m) (m - n))) in Hz.
    destruct Hz as [Hp0 _].
    rewrite Hp0 in Hprod. lia.
  - lia.
Qed.

Lemma cg_divides_p (n m : Z) : (cg n m | n * m).
Proof. unfold cg. apply Z.gcd_divide_l. Qed.

Lemma cg_divides_d (n m : Z) : (cg n m | m - n).
Proof. unfold cg. apply Z.gcd_divide_r. Qed.

(* 分解：cg·cx = n·m *)
Lemma split_p (n m : Z) (Hg : cg n m <> 0) : cg n m * cx n m = n * m.
Proof.
  intros. unfold cx, cg.
  assert (Hdiv : (Z.gcd (n * m) (m - n) | n * m)) by (unfold cg in *; exact (cg_divides_p n m)).
  assert (Hm0 : (n * m) mod Z.gcd (n * m) (m - n) = 0)
    by (apply (proj2 (Z.mod_divide (n * m) (Z.gcd (n * m) (m - n)) Hg)); exact Hdiv).
  symmetry. exact (proj2 (Z.div_exact (n * m) (Z.gcd (n * m) (m - n)) Hg) Hm0).
Qed.

(* 分解：cg·cy = m−n *)
Lemma split_d (n m : Z) (Hg : cg n m <> 0) : cg n m * cy n m = m - n.
Proof.
  intros. unfold cy, cg.
  assert (Hdiv : (Z.gcd (n * m) (m - n) | m - n)) by (unfold cg in *; exact (cg_divides_d n m)).
  assert (Hm0 : (m - n) mod Z.gcd (n * m) (m - n) = 0)
    by (apply (proj2 (Z.mod_divide (m - n) (Z.gcd (n * m) (m - n)) Hg)); exact Hdiv).
  symmetry. exact (proj2 (Z.div_exact (m - n) (Z.gcd (n * m) (m - n)) Hg) Hm0).
Qed.

(* 商互素：gcd(cx, cy) = 1（Euclid 前置件） *)
Lemma cop_quot (n m : Z) (Hg : cg n m <> 0) : Z.gcd (cx n m) (cy n m) = 1.
Proof.
  unfold cx, cy, cg.
  apply (Z.gcd_div_gcd (n * m) (m - n) (Z.gcd (n * m) (m - n))).
  - exact Hg.
  - reflexivity.
Qed.

(* ---------- 广义装配（续，2026-09-02）：g_char / g_min / g_sig ---------- *)

(* 商正：0 < cx（= prod/g 仍为最小 lag 的候选值） *)
Lemma cx_pos (n m : Z) : 0 < n -> n < m -> 0 < cx n m.
Proof.
  intros Hn Hlt.
  pose proof (cg_pos n m Hn Hlt) as Hcgp.
  assert (Hgnz : cg n m <> 0) by lia.
  pose proof (split_p n m Hgnz) as Hsp.            (* cg*cx = n*m *)
  assert (Hprod : 0 < n * m) by (apply zc_prod_pos; lia).
  assert (Hcgcx : 0 < cg n m * cx n m) by (rewrite Hsp; exact Hprod).
  assert (Hcxc : 0 < cx n m * cg n m)
    by (rewrite (Z.mul_comm (cx n m) (cg n m)); exact Hcgcx).
  apply (proj1 (Z.mul_pos_cancel_r (cx n m) (cg n m) Hcgp)). exact Hcxc.
Qed.

(* 广义 iff（核心四）：(n·m | d·(m−n)) ⟺ (cx | d)，g 分解 + Euclid 装配 *)
Theorem g_char (n m d : Z) : 0 < n -> n < m
  -> ((n * m | d * (m - n)) <-> (cx n m | d)).
Proof.
  intros Hn Hlt. split.
  - intro Hdiv.
    pose proof (cg_pos n m Hn Hlt) as Hcgp.
    assert (Hgnz : cg n m <> 0) by lia.
    pose proof (split_p n m Hgnz) as Hsp.          (* cg*cx = n*m *)
    pose proof (split_d n m Hgnz) as Hsd.          (* cg*cy = m−n *)
    destruct Hdiv as [q Hq].                      (* d*(m−n) = q*(n*m) *)
    rewrite <- Hsd in Hq. rewrite <- Hsp in Hq.   (* d*(cg*cy) = q*(cg*cx) *)
    assert (Hq2 : cg n m * (d * cy n m) = cg n m * (q * cx n m)).
    { assert (Hl : cg n m * (d * cy n m) = d * (cg n m * cy n m)) by ring.
      rewrite Hl. rewrite Hq.
      assert (Hr : q * (cg n m * cx n m) = cg n m * (q * cx n m)) by ring.
      rewrite Hr. reflexivity. }
    assert (Hc : d * cy n m = q * cx n m)
      by exact (proj1 (Z.mul_cancel_l (d * cy n m) (q * cx n m) (cg n m) Hgnz) Hq2).
    assert (Hdiv2 : (cx n m | d * cy n m)) by (exists q; exact Hc).
    pose proof (cop_quot n m Hgnz) as Hcq.
    exact (z_euclid (cx n m) (cy n m) d Hcq Hdiv2).
  - intro Hdiv. destruct Hdiv as [q Hq].          (* d = q*cx *)
    pose proof (cg_pos n m Hn Hlt) as Hcgp.
    assert (Hgnz : cg n m <> 0) by lia.
    pose proof (split_p n m Hgnz) as Hsp.
    pose proof (split_d n m Hgnz) as Hsd.
    exists (q * cy n m).
    rewrite Hq. rewrite <- Hsd. rewrite <- Hsp. ring.
Qed.

(* 广义最小性：0<t、(prod | t·dif) ⟹ cx ≤ t *)
Lemma g_min (n m t : Z) : 0 < n -> n < m -> 0 < t
  -> (n * m | t * (m - n)) -> cx n m <= t.
Proof.
  intros Hn Hlt Htpos Hdiv.
  pose proof (cx_pos n m Hn Hlt) as Hcx.
  apply (proj1 (g_char n m t Hn Hlt)) in Hdiv.    (* (cx | t) *)
  destruct Hdiv as [q Hq].                        (* t = q*cx *)
  assert (Hqpos : 0 < q).
  { apply (proj1 (Z.mul_pos_cancel_r q (cx n m) Hcx)).
    rewrite <- Hq. exact Htpos. }
  assert (Hq1 : 1 <= q) by lia.
  rewrite Hq.
  assert (Hle : 1 * (cx n m) <= q * (cx n m))
    by (apply Z.mul_le_mono_nonneg_r; [ lia | exact Hq1 ]).
  rewrite (Z.mul_1_l (cx n m)) in Hle. exact Hle.
Qed.

(* 广义最小 lag sigT（核心五/最终定理）：d_min = prod/g = cx *)
Theorem g_sig (n m : Z) : 0 < n -> n < m
  -> { d : Z & 0 < d /\ (n * m | d * (m - n)) /\
       (forall t : Z, 0 < t -> (n * m | t * (m - n)) -> d <= t) }.
Proof.
  intros Hn Hlt. exists (cx n m).
  split; [ | split ].
  - exact (cx_pos n m Hn Hlt).
  - apply (proj2 (g_char n m (cx n m) Hn Hlt)).
    exists 1. ring.
  - intros t Htpos Hdiv. exact (g_min n m t Hn Hlt Htpos Hdiv).
Qed.

(* 回落：gcd(prod,dif)=1 时 cx = prod（共素特例与广义一致） *)
Lemma cx_cop (n m : Z) : Z.gcd (n * m) (m - n) = 1 -> cx n m = n * m.
Proof.
  intros Hg. unfold cx, cg. rewrite Hg.
  exact (Z.div_1_r (n * m)).
Qed.

(* 提取与审计 *)
Extraction "collision_qtw.ml" zc_prod zc_dif cg cx cy.

Print Assumptions z_euclid.
Print Assumptions cop_char.
Print Assumptions cop_sig.
Print Assumptions cg_pos.
Print Assumptions split_p.
Print Assumptions split_d.
Print Assumptions cop_quot.
Print Assumptions cx_pos.
Print Assumptions g_char.
Print Assumptions g_min.
Print Assumptions g_sig.
Print Assumptions cx_cop.

