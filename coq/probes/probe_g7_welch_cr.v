(* ============================================================
   探针 probe_g7_welch_cr —— G-7 Welch 下界（构造性，实数原子版）
   ============================================================
   纪律：纯构造性——Stdlib ConstructiveReals（Set 层 CRcarrier + Prop 层
             CReq/CRle/CRlt），零经典实数、零 Admitted（终态）、零自定义公理。

   数学内容（Welch 下界，平方形态）：
     M+1 个单位范数原子（v i : R^{N+1}，i ≤ M），维度 N+1 < M+1，
     逐对相干 |⟨v_i, v_j⟩| ≤ mu（i ≠ j），则
       (M+1) − (N+1)  ≤  (N+1) · M · mu²
     即消费方 G-8（probe_g8_synthesis_cr）的抽象前提形态：
       INR M' − INR N' ≤ INR N' · INR (Nat.pred M') · mu · mu
     （M' = S M 原子数，N' = S N 维度，Nat.pred M' = M。）

   数学路线（Frobenius / Cauchy–Schwarz，避特征值——构造性友好）：
     1. 帧算子（函数表示，免矩阵库）g7S k l = Σ_{i≤M} v i k · v i l；
        Gram 矩阵 g7G i j = Σ_{k≤N} v i k · v j k。
     2. trace 恒等式：Σ_{k≤N} g7S k k = Σ_{i≤M} Σ_{k≤N} (v i k)²
        = Σ_{i≤M} 1 = INR (S M)（单位范数）。
     3. Cauchy–Schwarz（Lagrange 恒等式路线，零开方零特征值）：
        (Σ a_p b_p)² ≤ (Σ a_p²)(Σ b_p²)，取 a_k = g7S k k, b_k = 1：
        (INR (S M))² ≤ (Σ_k g7S k k²) · INR (S N)。
     4. 部分和 ≤ 全和：Σ_k g7S k k² ≤ Σ_{k,l} g7S k l²。
     5. Frobenius 恒等式（fourway）：
        Σ_{k,l} g7S k l² = Σ_{i,j} g7G i j²（双和换序 + 双和分配）。
     6. 相干聚束（bunching，对最大原子索引归纳，增量精确闭合）：
        Σ_{i,j} g7G i j² ≤ INR (S M) + INR (S M) · INR M · mu²。
     7. 组装（CR 代数）：(S M)² ≤ (S N)·[(S M) + (S M)·M·mu²]
        ⟹ (S M)·((S M) − (S N)) ≤ (S N)·M·mu²
        ⟹（除以正数 S M，乘法消去引理）(S M) − (S N) ≤ (S N)·M·mu²。

   与 G-8 衔接：包装定理 g7_welch_lower 以
     CRle R (INR M - INR N) (INR N * INR (Nat.pred M) * mu * mu)
   逐字给出 G-8 的 Hwelch 前提形态。

   结构：Section G7Sum（纯求和工具，无前提）
         Section G7Welch（Context：M N v mu + 单位范数 + 相干上界）
         顶层包装（G-8 签名对齐）。
   依赖： ca_rip_cr（CRsqr_nonneg / CRabs_sqr / CRsum_nonneg_term_le /
         CRmult_le_compat_l/r / CRmult_lt_compat_r / CRle_INR / CR_INR_S 等）。
   审计：零 Admitted / 零自定义公理；Print Assumptions 全 Closed。
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
From Stdlib Require Import Extraction.
Require Import ca_rip_cr.

Local Open Scope ConstructiveReals.
(* le/lt 用 Coq 原生函数（mathcomp 不劫持这两个标识符），lia 可处理。 *)

Section G7Sum.
Context {R : ConstructiveReals}.
Add Ring CR_ring : (CRisRing R).

(* ============ P0. 双和工具 ============ *)

(* 单层减法分离：Σ(x_k − y_k) == Σx − Σy *)
Lemma sum_minus (n : nat) (x y : nat -> CRcarrier R) :
  CReq R (CRsum (fun k => x k - y k) n) (CRsum x n - CRsum y n).
Proof.
  unfold CRminus.
  rewrite (sum_plus (R:=R) x (fun k => CRopp R (y k)) n).
  rewrite (sum_opp (R:=R) y n).
  reflexivity.
Qed.

(* 单层 scale（因子在前）：Σ(a·u_k) == a·Σu *)
Lemma sum_scale_l (n : nat) (a : CRcarrier R) (u : nat -> CRcarrier R) :
  CReq R (CRsum (fun k => a * u k) n) (a * CRsum u n).
Proof.
  rewrite (CRsum_eq (R:=R) (fun k => a * u k) (fun k => u k * a) n
    (fun k _ => CRmult_comm (R:=R) a (u k))).
  rewrite (sum_scale (R:=R) u a n).
  exact (CRmult_comm (R:=R) (CRsum u n) a).
Qed.

(* 双和分配律：(Σ_{p≤P} f p)·(Σ_{p≤P} g p) == Σ_{i≤P} Σ_{j≤P} f i·g j *)
Lemma sum2_mult (P : nat) (f g : nat -> CRcarrier R) :
  CReq R (CRsum f P * CRsum g P)
         (CRsum (fun i => CRsum (fun j => f i * g j) P) P).
Proof.
  induction P as [| P IH].
  - reflexivity.
  - assert (Hrhs : CReq R
      (CRsum (fun i => CRsum (fun j => f i * g j) (S P)) (S P))
      (CRsum f P * CRsum g P
       + (g (S P) * CRsum f P + f (S P) * CRsum g P
          + f (S P) * g (S P)))).
    { change (CRsum (fun i => CRsum (fun j => f i * g j) (S P)) (S P))
        with (CRsum (fun i => CRsum (fun j => f i * g j) (S P)) P
              + CRsum (fun j => f (S P) * g j) (S P)).
      assert (Hin : CReq R
        (CRsum (fun i => CRsum (fun j => f i * g j) (S P)) P)
        (CRsum (fun i => CRsum (fun j => f i * g j) P + f i * g (S P)) P)).
      { apply CRsum_eq. intro i. intro Hle.
        change (CRsum (fun j => f i * g j) (S P))
          with (CRsum (fun j => f i * g j) P + f i * g (S P)).
        reflexivity. }
      rewrite Hin.
      rewrite (sum_plus (R:=R)
                 (fun i => CRsum (fun j => f i * g j) P)
                 (fun i => f i * g (S P)) P).
      rewrite IH.
      rewrite (sum_scale (R:=R) f (g (S P)) P).
      change (CRsum (fun j => f (S P) * g j) (S P))
        with (CRsum (fun j => f (S P) * g j) P + f (S P) * g (S P)).
      assert (Hcomm : CReq R
        (CRsum (fun j => f (S P) * g j) P)
        (CRsum (fun j => g j * f (S P)) P)).
      { apply CRsum_eq. intro j. intro Hle. apply CRmult_comm. }
      rewrite Hcomm.
      rewrite (sum_scale (R:=R) g (f (S P)) P).
      ring. }
    change (CRsum f (S P)) with (CRsum f P + f (S P)).
    change (CRsum g (S P)) with (CRsum g P + g (S P)).
    rewrite Hrhs.
    ring.
Qed.

(* 双和换序：Σ_{k≤K} Σ_{l≤L} f k l == Σ_{l≤L} Σ_{k≤K} f k l *)
Lemma sum2_swap (K L : nat) (f : nat -> nat -> CRcarrier R) :
  CReq R (CRsum (fun k => CRsum (fun l => f k l) L) K)
         (CRsum (fun l => CRsum (fun k => f k l) K) L).
Proof.
  induction K as [| K IH].
  - reflexivity.
  - assert (Hin : CReq R
      (CRsum (fun l => CRsum (fun k => f k l) (S K)) L)
      (CRsum (fun l => CRsum (fun k => f k l) K + f (S K) l) L)).
    { apply CRsum_eq. intro l. intro Hle.
      change (CRsum (fun k => f k l) (S K))
        with (CRsum (fun k => f k l) K + f (S K) l).
      reflexivity. }
    rewrite Hin.
    rewrite (sum_plus (R:=R)
               (fun l => CRsum (fun k => f k l) K)
               (fun l => f (S K) l) L).
    change (CRsum (fun k => CRsum (fun l => f k l) L) (S K))
      with (CRsum (fun k => CRsum (fun l => f k l) L) K
            + CRsum (fun l => f (S K) l) L).
    rewrite IH.
    reflexivity.
Qed.

(* 双和非负：逐项非负 ⟹ 双和 ≥ 0 *)
Lemma sum2_nonneg (K L : nat) (f : nat -> nat -> CRcarrier R) :
  (forall k l, CRle R (CR_of_Q R (Qmake 0 1)) (f k l)) ->
  CRle R (CR_of_Q R (Qmake 0 1))
         (CRsum (fun k => CRsum (fun l => f k l) L) K).
Proof.
  intros Hf.
  apply cond_pos_sum.
  intro k.
  apply cond_pos_sum.
  intro l.
  apply Hf.
Qed.

(* 三层和换位（最前层移到最后）：Σ_{a≤A} Σ_{b≤B} Σ_{c≤C} f a b c
   == Σ_{b≤B} Σ_{c≤C} Σ_{a≤A} f a b c——fourway 四层换位的基本构件 *)
Lemma sum3_swap (A B C : nat) (f : nat -> nat -> nat -> CRcarrier R) :
  CReq R
    (CRsum (fun a => CRsum (fun b => CRsum (fun c => f a b c) C) B) A)
    (CRsum (fun b => CRsum (fun c => CRsum (fun a => f a b c) A) C) B).
Proof.
  induction A as [| A IH].
  - reflexivity.
  - assert (Hin : CReq R
      (CRsum (fun b => CRsum (fun c => CRsum (fun a => f a b c) (S A)) C) B)
      (CRsum (fun b => CRsum (fun c => CRsum (fun a => f a b c) A
                               + f (S A) b c) C) B)).
    { apply CRsum_eq.
      intro b. intro Hb.
      apply CRsum_eq.
      intro c. intro Hc.
      change (CRsum (fun a => f a b c) (S A))
        with (CRsum (fun a => f a b c) A + f (S A) b c).
      reflexivity. }
    rewrite Hin.
    assert (Hc2 : CReq R
      (CRsum (fun b => CRsum (fun c => CRsum (fun a => f a b c) A
                               + f (S A) b c) C) B)
      (CRsum (fun b => CRsum (fun c => CRsum (fun a => f a b c) A) C
               + CRsum (fun c => f (S A) b c) C) B)).
    { apply CRsum_eq.
      exact (fun b _ => sum_plus (fun c => CRsum (fun a => f a b c) A)
                                 (fun c => f (S A) b c) C). }
    rewrite Hc2.
    rewrite (sum_plus
               (fun b => CRsum (fun c => CRsum (fun a => f a b c) A) C)
               (fun b => CRsum (fun c => f (S A) b c) C) B).
    change (CRsum (fun a => CRsum (fun b => CRsum (fun c => f a b c) C) B) (S A))
      with (CRsum (fun a => CRsum (fun b => CRsum (fun c => f a b c) C) B) A
            + CRsum (fun b => CRsum (fun c => f (S A) b c) C) B).
    rewrite IH.
    reflexivity.
Qed.

(* 乘正消去：0 < c ⟹ c·x ≤ c·y ⟹ x ≤ y（构造性反证：y < x ⟹ c·y < c·x 矛盾） *)
Lemma CRmult_le_reg_r (c x y : CRcarrier R) :
  CRlt R (CR_of_Q R (Qmake 0 1)) c ->
  CRle R (c * x) (c * y) ->
  CRle R x y.
Proof.
  intros Hc0 Hxy.
  unfold CRle. intro Hneg.
  exact (Hxy (CRmult_lt_compat_l c y x Hc0 Hneg)).
Qed.

(* 半量引理：0 ≤ (1+1)·x ⟹ 0 ≤ x（构造性反证：x < 0 ⟹ (1+1)·x < (1+1)·0 == 0
   矛盾；全程静态装配，零 rewrite——CRplus_0_l 参与 rewrite 触发 build_signature
   报错，改用 CReq 投影 + CRle_lt_trans/CRlt_le_trans 串接） *)
Lemma CRle_half (x : CRcarrier R) :
  CRle R (CR_of_Q R (Qmake 0 1)) ((1 + 1) * x) ->
  CRle R (CR_of_Q R (Qmake 0 1)) x.
Proof.
  intros H2x.
  assert (H02 : CRlt R (CR_of_Q R (Qmake 0 1)) (1 + 1)).
  { apply (CRlt_trans (R:=R) _ (CR_of_Q R (Qmake 1 1))).
    - exact (CRzero_lt_one R).
    - apply (CRle_lt_trans (R:=R) (CR_of_Q R (Qmake 1 1))
               (CRplus R (CR_of_Q R (Qmake 0 1)) (CR_of_Q R (Qmake 1 1))) (1 + 1)).
      + exact (proj1 (CRplus_0_l (CR_of_Q R (Qmake 1 1)))).
      + exact (CRplus_lt_compat_r (CR_of_Q R (Qmake 1 1))
                 (CR_of_Q R (Qmake 0 1)) (CR_of_Q R (Qmake 1 1))
                 (CRzero_lt_one R)). }
  unfold CRle in H2x.
  unfold CRle. intro Hneg.
  assert (Hlt1 : CRlt R ((1 + 1) * x) ((1 + 1) * CR_of_Q R (Qmake 0 1))).
  { exact (CRmult_lt_compat_l (1 + 1) x (CR_of_Q R (Qmake 0 1)) H02 Hneg). }
  assert (Hlt2 : CRlt R ((1 + 1) * x) (CR_of_Q R (Qmake 0 1))).
  { apply (CRlt_le_trans (R:=R) _ ((1 + 1) * CR_of_Q R (Qmake 0 1))).
    - exact Hlt1.
    - exact (proj2 (CRmult_0_r (1 + 1))). }
  exact (H2x Hlt2).
Qed.

(* ============ P1. 单指标 Cauchy–Schwarz（Lagrange 恒等式） ============ *)

(* (Σ a_p·b_p)² ≤ (Σ a_p²)·(Σ b_p²)——零开方、零特征值，构造性。
   路线：双和 L = Σ_{i,j} (a i·b j − a j·b i)² ≥ 0，且
   L == 2·(SA·SB − X)，其中 X = (Σab)²，故 X ≤ X + 2(SA·SB − X) == SA·SB。 *)
Lemma cs_core (P : nat) (a b : nat -> CRcarrier R) :
  CRle R ((CRsum (fun p => a p * b p) P) * (CRsum (fun p => a p * b p) P))
         ((CRsum (fun p => a p * a p) P) * (CRsum (fun p => b p * b p) P)).
Proof.
  assert (Hlag : CReq R
    (CRsum (fun i => CRsum (fun j =>
              (a i * b j - a j * b i) * (a i * b j - a j * b i)) P) P)
    ((1 + 1) * (CRsum (fun p => a p * a p) P * CRsum (fun p => b p * b p) P
                - CRsum (fun p => a p * b p) P * CRsum (fun p => a p * b p) P))).
  { (* 纯装配策略：全部中间等式独立 assert（目标纯净无双向污染），
       最后 CReq_trans 串接 + ring 收口。 *)
    (* 逐项展开 (x−y)² == A + (B − 2C) *)
    assert (Hterm : forall i j,
      CReq R ((a i * b j - a j * b i) * (a i * b j - a j * b i))
             (a i * a i * (b j * b j)
              + (a j * a j * (b i * b i)
                 - (1 + 1) * (a i * b i * (a j * b j))))).
    { intros i j. unfold CRminus. ring. }
    (* 内层求和分离（逐 i）：Σ_j (A + (B − D)) == Σ_j A + (Σ_j B − Σ_j D) *)
    assert (Hsplit : forall i,
      CReq R
        (CRsum (fun j => a i * a i * (b j * b j)
                  + (a j * a j * (b i * b i)
                     - (1 + 1) * (a i * b i * (a j * b j)))) P)
        (CRsum (fun j => a i * a i * (b j * b j)) P
         + (CRsum (fun j => a j * a j * (b i * b i)) P
            - CRsum (fun j => (1 + 1) * (a i * b i * (a j * b j))) P))).
    { intro i.
      rewrite (sum_plus (fun j => a i * a i * (b j * b j))
        (fun j => a j * a j * (b i * b i)
                  - (1 + 1) * (a i * b i * (a j * b j))) P).
      apply CRplus_morph.
      + apply CReq_refl.
      + apply (sum_minus P (fun j => a j * a j * (b i * b i))
                 (fun j => (1 + 1) * (a i * b i * (a j * b j)))). }
    (* E01：逐项替换 *)
    assert (E01 : CReq R
      (CRsum (fun i => CRsum (fun j =>
         (a i * b j - a j * b i) * (a i * b j - a j * b i)) P) P)
      (CRsum (fun i => CRsum (fun j =>
         a i * a i * (b j * b j)
         + (a j * a j * (b i * b i)
            - (1 + 1) * (a i * b i * (a j * b j)))) P) P)).
    { apply CRsum_eq.
      intro i. intro Hi.
      apply CRsum_eq.
      exact (fun j _ => Hterm i j). }
    (* E12：内层分离（逐 i 应用 Hsplit） *)
    assert (E12 : CReq R
      (CRsum (fun i => CRsum (fun j =>
         a i * a i * (b j * b j)
         + (a j * a j * (b i * b i)
            - (1 + 1) * (a i * b i * (a j * b j)))) P) P)
      (CRsum (fun i => CRsum (fun j => a i * a i * (b j * b j)) P
                + (CRsum (fun j => a j * a j * (b i * b i)) P
                   - CRsum (fun j => (1 + 1) * (a i * b i * (a j * b j))) P)) P)).
    { apply CRsum_eq. exact (fun i _ => Hsplit i). }
    (* E23：外层 sum_plus（加法函数体拆分） *)
    assert (E23 : CReq R
      (CRsum (fun i => CRsum (fun j => a i * a i * (b j * b j)) P
                + (CRsum (fun j => a j * a j * (b i * b i)) P
                   - CRsum (fun j => (1 + 1) * (a i * b i * (a j * b j))) P)) P)
      (CRsum (fun i => CRsum (fun j => a i * a i * (b j * b j)) P) P
       + CRsum (fun i => CRsum (fun j => a j * a j * (b i * b i)) P
                 - CRsum (fun j => (1 + 1) * (a i * b i * (a j * b j))) P) P)).
    { apply (sum_plus
        (fun i => CRsum (fun j => a i * a i * (b j * b j)) P)
        (fun i => CRsum (fun j => a j * a j * (b i * b i)) P
                  - CRsum (fun j => (1 + 1) * (a i * b i * (a j * b j))) P) P). }
    (* E3：外层 sum_minus（减法分离） *)
    assert (E3 : CReq R
      (CRsum (fun i => CRsum (fun j => a i * a i * (b j * b j)) P) P
       + CRsum (fun i => CRsum (fun j => a j * a j * (b i * b i)) P
                 - CRsum (fun j => (1 + 1) * (a i * b i * (a j * b j))) P) P)
      (CRsum (fun i => CRsum (fun j => a i * a i * (b j * b j)) P) P
       + (CRsum (fun i => CRsum (fun j => a j * a j * (b i * b i)) P) P
          - CRsum (fun i => CRsum (fun j => (1 + 1) * (a i * b i * (a j * b j))) P) P))).
    { apply CRplus_morph.
      - apply CReq_refl.
      - apply (sum_minus P
          (fun i => CRsum (fun j => a j * a j * (b i * b i)) P)
          (fun i => CRsum (fun j => (1 + 1) * (a i * b i * (a j * b j))) P)). }
    (* E4：scale 提出（(1+1)·ΣΣC）：内层逐 i + 外层 *)
    assert (E4 : CReq R
      (CRsum (fun i => CRsum (fun j => a i * a i * (b j * b j)) P) P
       + (CRsum (fun i => CRsum (fun j => a j * a j * (b i * b i)) P) P
          - CRsum (fun i => CRsum (fun j => (1 + 1) * (a i * b i * (a j * b j))) P) P))
      (CRsum (fun i => CRsum (fun j => a i * a i * (b j * b j)) P) P
       + (CRsum (fun i => CRsum (fun j => a j * a j * (b i * b i)) P) P
          - (1 + 1) * CRsum (fun i => CRsum (fun j => a i * b i * (a j * b j)) P) P))).
    { apply CRplus_morph.
      - apply CReq_refl.
      - apply CRplus_morph.
        + apply CReq_refl.
        + apply CRopp_morph.
          eapply CReq_trans.
          * apply CRsum_eq.
            exact (fun i _ => sum_scale_l P (1 + 1)
                     (fun j => a i * b i * (a j * b j))).
          * apply (sum_scale_l P (1 + 1)
                     (fun i => CRsum (fun j => a i * b i * (a j * b j)) P)). }
    (* 块闭合：EA / EB / EC *)
    assert (EA : CReq R
      (CRsum (fun i => CRsum (fun j => a i * a i * (b j * b j)) P) P)
      (CRsum (fun i => a i * a i) P * CRsum (fun j => b j * b j) P)).
    { apply CReq_sym.
      apply (sum2_mult P (fun i => a i * a i) (fun j => b j * b j)). }
    assert (EB : CReq R
      (CRsum (fun i => CRsum (fun j => a j * a j * (b i * b i)) P) P)
      (CRsum (fun i => a i * a i) P * CRsum (fun j => b j * b j) P)).
    { eapply CReq_trans.
      - apply (sum2_swap P P (fun i j => a j * a j * (b i * b i))).
      - apply CReq_sym.
        apply (sum2_mult P (fun i => a i * a i) (fun j => b j * b j)). }
    assert (EC : CReq R
      (CRsum (fun i => CRsum (fun j => a i * b i * (a j * b j)) P) P)
      (CRsum (fun p => a p * b p) P * CRsum (fun p => a p * b p) P)).
    { apply CReq_sym.
      apply (sum2_mult P (fun p => a p * b p) (fun p => a p * b p)). }
    (* E5：块闭合组装（加法/减法/乘法 morph） *)
    assert (E5 : CReq R
      (CRsum (fun i => CRsum (fun j => a i * a i * (b j * b j)) P) P
       + (CRsum (fun i => CRsum (fun j => a j * a j * (b i * b i)) P) P
          - (1 + 1) * CRsum (fun i => CRsum (fun j => a i * b i * (a j * b j)) P) P))
      (CRsum (fun p => a p * a p) P * CRsum (fun p => b p * b p) P
       + (CRsum (fun p => a p * a p) P * CRsum (fun p => b p * b p) P
          - (1 + 1) * (CRsum (fun p => a p * b p) P * CRsum (fun p => a p * b p) P)))).
    { apply CRplus_morph.
      - exact EA.
      - unfold CRminus.
        apply CRplus_morph.
        + exact EB.
        + apply CRopp_morph.
          apply CRmult_morph.
          * apply CReq_refl.
          * exact EC. }
    (* E6：代数收口 *)
    assert (E6 : CReq R
      (CRsum (fun p => a p * a p) P * CRsum (fun p => b p * b p) P
       + (CRsum (fun p => a p * a p) P * CRsum (fun p => b p * b p) P
          - (1 + 1) * (CRsum (fun p => a p * b p) P * CRsum (fun p => a p * b p) P)))
      ((1 + 1) * (CRsum (fun p => a p * a p) P * CRsum (fun p => b p * b p) P
                  - CRsum (fun p => a p * b p) P * CRsum (fun p => a p * b p) P))).
    { unfold CRminus. ring. }
    (* 串接 *)
    eapply CReq_trans. exact E01.
    eapply CReq_trans. exact E12.
    eapply CReq_trans. exact E23.
    eapply CReq_trans. exact E3.
    eapply CReq_trans. exact E4.
    eapply CReq_trans. exact E5.
    exact E6. }
  assert (Hnonneg : CRle R (CR_of_Q R (Qmake 0 1))
    (CRsum (fun i => CRsum (fun j =>
       (a i * b j - a j * b i) * (a i * b j - a j * b i)) P) P)).
  { apply sum2_nonneg. intro k. intro l. apply CRsqr_nonneg. }
  (* 0 ≤ L == 2·D ⟹ 0 ≤ D，其中 D = SA·SB − X *)
  assert (H0D : CRle R (CR_of_Q R (Qmake 0 1))
    (CRsum (fun p => a p * a p) P * CRsum (fun p => b p * b p) P
     - CRsum (fun p => a p * b p) P * CRsum (fun p => a p * b p) P)).
  { apply CRle_half.
    rewrite <- Hlag. exact Hnonneg. }
  (* X ≤ X + D == SA·SB *)
  assert (Hring : CReq R
    (CRsum (fun p => a p * b p) P * CRsum (fun p => a p * b p) P
     + (CRsum (fun p => a p * a p) P * CRsum (fun p => b p * b p) P
        - CRsum (fun p => a p * b p) P * CRsum (fun p => a p * b p) P))
    (CRsum (fun p => a p * a p) P * CRsum (fun p => b p * b p) P)).
  { unfold CRminus. ring. }
  rewrite <- Hring.
  apply (Rplus_le_pos (R:=R)
    (CRsum (fun p => a p * b p) P * CRsum (fun p => a p * b p) P)
    (CRsum (fun p => a p * a p) P * CRsum (fun p => b p * b p) P
     - CRsum (fun p => a p * b p) P * CRsum (fun p => a p * b p) P)).
  exact H0D.
Qed.

End G7Sum.

(* ============ P2/P3. Welch 组件与主定理（带前提 Context） ============ *)

Section G7Welch.
Context {R : ConstructiveReals}.
Add Ring CR_ring : (CRisRing R).

Context (M N : nat) (v : nat -> nat -> CRcarrier R) (mu : CRcarrier R).
(* 单位范数：每个原子 i ≤ M 的分量平方和（k ≤ N）为 1 *)
Context (Hunit : forall i, le i M ->
  CReq R (CRsum (fun k => v i k * v i k) N) (CR_of_Q R (Qmake 1 1))).
(* 逐对相干上界：i ≠ j（均 ≤ M）时 |⟨v_i, v_j⟩| ≤ mu *)
Context (Hcoh : forall i j, le i M -> le j M -> i <> j ->
  CRle R (CRabs R (CRsum (fun k => v i k * v j k) N)) mu).

(* 帧算子条目（函数表示，免矩阵库）：S k l = ⟨v_·k, v_·l⟩ *)
Definition g7S (k l : nat) : CRcarrier R := CRsum (fun i => v i k * v i l) M.
(* Gram 矩阵条目：G i j = ⟨v_i, v_j⟩ *)
Definition g7G (i j : nat) : CRcarrier R := CRsum (fun k => v i k * v j k) N.

(* P2a. trace 恒等式：Σ_{k≤N} S k k == INR (S M)（单位范数）
   链：换序（内层 i 提前）⟹ 逐 i 单位范数 == 1 ⟹ sum_const ⟹ 乘 1 *)
Lemma g7_trace :
  CReq R (CRsum (fun k => g7S k k) N) (INR (S M)).
Proof.
  unfold g7S.
  rewrite (sum2_swap N M (fun k i => v i k * v i k)).
  rewrite (CRsum_eq
             (fun i => CRsum (fun k => v i k * v i k) N)
             (fun i => CR_of_Q R (Qmake 1 1)) M
             (fun i Hle => Hunit i Hle)).
  rewrite (sum_const (CR_of_Q R (Qmake 1 1)) M).
  apply CRmult_1_l.
Qed.

(* P2b. Frobenius 恒等式：Σ_{k,l≤N} S k l² == Σ_{i,j≤M} G i j²
   链：两侧各自展开为四层和（sum2_mult 逐项）⟹ sum3_swap × 2 换位 (k,l,i,j)→(i,j,k,l) *)
Lemma g7_fourway :
  CReq R (CRsum (fun k => CRsum (fun l => g7S k l * g7S k l) N) N)
         (CRsum (fun i => CRsum (fun j => g7G i j * g7G i j) M) M).
Proof.
  (* 内层积拆双和：S k l² == Σ_{i,j} P k l i j（逐项 ring 重排） *)
  assert (E_inner : forall k l,
    CReq R (g7S k l * g7S k l)
           (CRsum (fun i => CRsum (fun j => (v i k * v j k) * (v i l * v j l)) M) M)).
  { intros k l. unfold g7S.
    eapply CReq_trans.
    - exact (sum2_mult M (fun i => v i k * v i l) (fun j => v j k * v j l)).
    - apply CRsum_eq.
      intro i. intro Hi.
      apply CRsum_eq.
      intro j. intro Hj.
      ring. }
  (* G 侧内层积拆双和（因子序天然匹配 P，无 ring） *)
  assert (E_Rin : forall i j,
    CReq R (g7G i j * g7G i j)
           (CRsum (fun k => CRsum (fun l => (v i k * v j k) * (v i l * v j l)) N) N)).
  { intros i j. unfold g7G.
    apply (sum2_mult N (fun k => v i k * v j k) (fun l => v i l * v j l)). }
  (* 左侧两层 CRsum_eq 展开 *)
  assert (E_L : CReq R
    (CRsum (fun k => CRsum (fun l => g7S k l * g7S k l) N) N)
    (CRsum (fun k => CRsum (fun l =>
       CRsum (fun i => CRsum (fun j => (v i k * v j k) * (v i l * v j l)) M) M) N) N)).
  { apply CRsum_eq.
    intro k. intro Hk.
    apply CRsum_eq.
    intro l. intro Hl.
    exact (E_inner k l). }
  (* 右侧两层 CRsum_eq 展开 *)
  assert (E_R : CReq R
    (CRsum (fun i => CRsum (fun j => g7G i j * g7G i j) M) M)
    (CRsum (fun i => CRsum (fun j =>
       CRsum (fun k => CRsum (fun l => (v i k * v j k) * (v i l * v j l)) N) N) M) M)).
  { apply CRsum_eq.
    intro i. intro Hi.
    apply CRsum_eq.
    intro j. intro Hj.
    exact (E_Rin i j). }
  (* 四层换位 (k,l,i,j) → (i,j,k,l)：sum3_swap × 2 *)
  assert (E_s1 : CReq R
    (CRsum (fun k => CRsum (fun l =>
       CRsum (fun i => CRsum (fun j => (v i k * v j k) * (v i l * v j l)) M) M) N) N)
    (CRsum (fun l => CRsum (fun i => CRsum (fun k =>
       CRsum (fun j => (v i k * v j k) * (v i l * v j l)) M) N) M) N)).
  { exact (sum3_swap N N M
             (fun k l i => CRsum (fun j => (v i k * v j k) * (v i l * v j l)) M)). }
  assert (E_s2 : CReq R
    (CRsum (fun l => CRsum (fun i => CRsum (fun k =>
       CRsum (fun j => (v i k * v j k) * (v i l * v j l)) M) N) M) N)
    (CRsum (fun l => CRsum (fun i => CRsum (fun j =>
       CRsum (fun k => (v i k * v j k) * (v i l * v j l)) N) M) M) N)).
  { apply CRsum_eq.
    intro l. intro Hl.
    apply CRsum_eq.
    intro i. intro Hi.
    apply (sum2_swap N M (fun k j => (v i k * v j k) * (v i l * v j l))). }
  assert (E_s3 : CReq R
    (CRsum (fun l => CRsum (fun i => CRsum (fun j =>
       CRsum (fun k => (v i k * v j k) * (v i l * v j l)) N) M) M) N)
    (CRsum (fun i => CRsum (fun j => CRsum (fun l =>
       CRsum (fun k => (v i k * v j k) * (v i l * v j l)) N) N) M) M)).
  { exact (sum3_swap N M M
             (fun l i j => CRsum (fun k => (v i k * v j k) * (v i l * v j l)) N)). }
  assert (E_s4 : CReq R
    (CRsum (fun i => CRsum (fun j => CRsum (fun l =>
       CRsum (fun k => (v i k * v j k) * (v i l * v j l)) N) N) M) M)
    (CRsum (fun i => CRsum (fun j =>
       CRsum (fun k => CRsum (fun l => (v i k * v j k) * (v i l * v j l)) N) N) M) M)).
  { apply CRsum_eq.
    intro i. intro Hi.
    apply CRsum_eq.
    intro j. intro Hj.
    apply (sum2_swap N N (fun l k => (v i k * v j k) * (v i l * v j l))). }
  eapply CReq_trans. exact E_L.
  eapply CReq_trans. exact E_s1.
  eapply CReq_trans. exact E_s2.
  eapply CReq_trans. exact E_s3.
  eapply CReq_trans. exact E_s4.
  apply CReq_sym. exact E_R.
Qed.

(* P2c. 相干聚束：Σ_{i,j≤M} G i j² ≤ INR (S M) + INR (S M)·INR M·mu²
   归纳（最大原子索引 M）：增量 = 对角 1 + 行内 mu²·INR (S M) + 列 mu²·INR (S M)，
   恰好等于 RHS 增量 1 + 2·INR (S M)·mu²（先手算闭合，E144⑨） *)
Lemma g7_bunching :
  CRle R (CRsum (fun i => CRsum (fun j => g7G i j * g7G i j) M) M)
         (INR (S M) + INR (S M) * INR M * mu * mu).
Proof.
  revert Hcoh. revert Hunit.
  induction M as [| Mp IH].
  - intros Hunit Hcoh.
    assert (Hgg : CReq R (g7G 0 0) (CR_of_Q R (Qmake 1 1))).
    { unfold g7G. apply Hunit. apply le_n. }
    assert (Hz : CReq R (INR 1 * INR 0 * mu * mu) (CR_of_Q R (Qmake 0 1))).
    { change (INR 1) with (CR_of_Q R (Qmake 1 1)).
      change (INR 0) with (CR_of_Q R (Qmake 0 1)).
      ring. }
    assert (Hone : CReq R (CR_of_Q R (Qmake 1 1) * CR_of_Q R (Qmake 1 1))
                           (CR_of_Q R (Qmake 1 1))) by ring.
    assert (Hp : CReq R (CR_of_Q R (Qmake 1 1) + CR_of_Q R (Qmake 0 1))
                         (CR_of_Q R (Qmake 1 1))) by ring.
    change (CRsum (fun i => CRsum (fun j => g7G i j * g7G i j) 0) 0)
      with (g7G 0 0 * g7G 0 0).
    rewrite Hgg. rewrite Hone. rewrite Hz. rewrite Hp.
    change (INR 1) with (CR_of_Q R (Qmake 1 1)).
    apply CRle_refl.
  - intros Hunit Hcoh.
    assert (Heq_split : CReq R
      (CRsum (fun i => CRsum (fun j => g7G i j * g7G i j) (S Mp)) (S Mp))
      ((CRsum (fun i => CRsum (fun j => g7G i j * g7G i j) Mp) Mp
        + CRsum (fun i => g7G i (S Mp) * g7G i (S Mp)) Mp)
       + (CRsum (fun j => g7G (S Mp) j * g7G (S Mp) j) Mp
          + g7G (S Mp) (S Mp) * g7G (S Mp) (S Mp)))).
    { change (CRsum (fun i => CRsum (fun j => g7G i j * g7G i j) (S Mp)) (S Mp))
        with (CRsum (fun i => CRsum (fun j => g7G i j * g7G i j) (S Mp)) Mp
              + CRsum (fun j => g7G (S Mp) j * g7G (S Mp) j) (S Mp)).
      assert (Hin : CReq R
        (CRsum (fun i => CRsum (fun j => g7G i j * g7G i j) (S Mp)) Mp)
        (CRsum (fun i => CRsum (fun j => g7G i j * g7G i j) Mp
                 + g7G i (S Mp) * g7G i (S Mp)) Mp)).
      { apply CRsum_eq. intro i. intro Hi.
        change (CRsum (fun j => g7G i j * g7G i j) (S Mp))
          with (CRsum (fun j => g7G i j * g7G i j) Mp + g7G i (S Mp) * g7G i (S Mp)).
        reflexivity. }
      rewrite Hin.
      rewrite (sum_plus (fun i => CRsum (fun j => g7G i j * g7G i j) Mp)
                        (fun i => g7G i (S Mp) * g7G i (S Mp)) Mp).
      change (CRsum (fun j => g7G (S Mp) j * g7G (S Mp) j) (S Mp))
        with (CRsum (fun j => g7G (S Mp) j * g7G (S Mp) j) Mp
              + g7G (S Mp) (S Mp) * g7G (S Mp) (S Mp)).
      reflexivity. }
    assert (Hdiag : CReq R (g7G (S Mp) (S Mp) * g7G (S Mp) (S Mp))
                           (CR_of_Q R (Qmake 1 1))).
    { unfold g7G. rewrite (Hunit (S Mp) (le_n (S Mp))). apply CRmult_1_l. }
    assert (Hsq : forall g : CRcarrier R,
      CRle R (CRabs R g) mu -> CRle R (g * g) (mu * mu)).
    { intros g Hg.
      assert (H0g : CRle R (CR_of_Q R (Qmake 0 1)) (CRabs R g)).
      { exact (CRabs_pos g). }
      assert (H0mu : CRle R (CR_of_Q R (Qmake 0 1)) mu).
      { apply (CRle_trans (R:=R) _ (CRabs R g)).
        - exact (CRabs_pos g).
        - exact Hg. }
      assert (Hs1 : CRle R (CRabs R g * CRabs R g) (CRabs R g * mu)).
      { exact (CRmult_le_compat_l (CRabs R g) (CRabs R g) mu H0g Hg). }
      assert (Hs2 : CRle R (mu * CRabs R g) (mu * mu)).
      { exact (CRmult_le_compat_l mu (CRabs R g) mu H0mu Hg). }
      assert (Hcm : CReq R (CRabs R g * mu) (mu * CRabs R g)).
      { apply CRmult_comm. }
      eapply CRle_trans.
      - apply (proj2 (CRabs_sqr g)).
      - eapply CRle_trans.
        + exact Hs1.
        + eapply CRle_trans.
          * apply (proj2 Hcm).
          * exact Hs2. }
    assert (Hpair : forall i, le i Mp ->
      CRle R (g7G i (S Mp) * g7G i (S Mp)) (mu * mu)).
    { intro i. intro Hi.
      assert (Hne : i <> S Mp) by lia.
      apply Hsq. exact (Hcoh i (S Mp) (le_S i Mp Hi) (le_n (S Mp)) Hne). }
    assert (Hpair2 : forall j, le j Mp ->
      CRle R (g7G (S Mp) j * g7G (S Mp) j) (mu * mu)).
    { intro j. intro Hj.
      assert (Hne : S Mp <> j) by lia.
      apply Hsq. exact (Hcoh (S Mp) j (le_n (S Mp)) (le_S j Mp Hj) Hne). }
    assert (HCol : CRle R (CRsum (fun i => g7G i (S Mp) * g7G i (S Mp)) Mp)
                           (mu * mu * INR (S Mp))).
    { rewrite <- (sum_const (mu * mu) Mp).
      apply sum_Rle. intro k. intro Hk. apply Hpair. exact Hk. }
    assert (HRow : CRle R (CRsum (fun j => g7G (S Mp) j * g7G (S Mp) j) Mp)
                           (mu * mu * INR (S Mp))).
    { rewrite <- (sum_const (mu * mu) Mp).
      apply sum_Rle. intro k. intro Hk. apply Hpair2. exact Hk. }
    assert (HIH : CRle R (CRsum (fun i => CRsum (fun j => g7G i j * g7G i j) Mp) Mp)
                         (INR (S Mp) + INR (S Mp) * INR Mp * mu * mu)).
    { apply IH.
      - intros i Hi. apply Hunit. exact (le_S i Mp Hi).
      - intros i j Hi Hj Hne. apply Hcoh.
        + exact (le_S i Mp Hi).
        + exact (le_S j Mp Hj).
        + exact Hne. }
    rewrite (CR_INR_S (S Mp)).
    rewrite (CR_INR_S Mp).
    rewrite (CR_INR_S Mp) in HCol.
    rewrite (CR_INR_S Mp) in HRow.
    rewrite (CR_INR_S Mp) in HIH.
    rewrite Heq_split.
    eapply CRle_trans.
    + apply (CRplus_le_compat
               (CRsum (fun i => CRsum (fun j => g7G i j * g7G i j) Mp) Mp
                + CRsum (fun i => g7G i (S Mp) * g7G i (S Mp)) Mp)
               (INR Mp + 1 + (INR Mp + 1) * INR Mp * mu * mu
                + mu * mu * (INR Mp + 1))
               (CRsum (fun j => g7G (S Mp) j * g7G (S Mp) j) Mp
                + g7G (S Mp) (S Mp) * g7G (S Mp) (S Mp))
               (mu * mu * (INR Mp + 1) + CR_of_Q R (Qmake 1 1))).
      * apply (CRplus_le_compat
                 (CRsum (fun i => CRsum (fun j => g7G i j * g7G i j) Mp) Mp)
                 (INR Mp + 1 + (INR Mp + 1) * INR Mp * mu * mu)
                 (CRsum (fun i => g7G i (S Mp) * g7G i (S Mp)) Mp)
                 (mu * mu * (INR Mp + 1))).
        -- exact HIH.
        -- exact HCol.
      * apply (CRplus_le_compat
                 (CRsum (fun j => g7G (S Mp) j * g7G (S Mp) j) Mp)
                 (mu * mu * (INR Mp + 1))
                 (g7G (S Mp) (S Mp) * g7G (S Mp) (S Mp))
                 (CR_of_Q R (Qmake 1 1))).
        -- exact HRow.
        -- rewrite Hdiag. apply CRle_refl.
    assert (Hring : CReq R
      (INR Mp + 1 + (INR Mp + 1) * INR Mp * mu * mu + mu * mu * (INR Mp + 1)
       + (mu * mu * (INR Mp + 1) + CR_of_Q R (Qmake 1 1)))
      (INR Mp + 1 + 1 + (INR Mp + 1 + 1) * (INR Mp + 1) * mu * mu)) by ring.
    rewrite Hring. apply CRle_refl.
Qed.

(* P3. 主定理（内部形态）：(M+1) − (N+1) ≤ (N+1)·M·mu²
   链：trace == INR (S M) ⟹ cs_core（a = 对角，b = 1）⟹ 部分和 ≤ 全和
       ⟹ fourway ⟹ bunching ⟹ CR 代数移项（A·(A−B) ≤ Cq 时反证 Cq < A−B：
       Cq·1 ≤ Cq·A < A·(A−B) ≤ Cq 矛盾——免乘正消去引理） *)
Theorem g7_welch_core :
  CRle R (INR (S M) - INR (S N)) (INR (S N) * INR M * mu * mu).
Proof.
  assert (Hcs0 : CRle R
    ((CRsum (fun k => g7S k k * CR_of_Q R (Qmake 1 1)) N)
     * (CRsum (fun k => g7S k k * CR_of_Q R (Qmake 1 1)) N))
    ((CRsum (fun k => g7S k k * g7S k k) N)
     * (CRsum (fun k => CR_of_Q R (Qmake 1 1) * CR_of_Q R (Qmake 1 1)) N))).
  { exact (cs_core N (fun k => g7S k k) (fun _ => CR_of_Q R (Qmake 1 1))). }
  assert (Hs1 : CReq R (CRsum (fun k => g7S k k * CR_of_Q R (Qmake 1 1)) N)
                       (CRsum (fun k => g7S k k) N)).
  { apply CRsum_eq. exact (fun k _ => CRmult_1_r (g7S k k)). }
  assert (Hs2 : CReq R (CRsum (fun k => CR_of_Q R (Qmake 1 1) * CR_of_Q R (Qmake 1 1)) N)
                       (INR (S N))).
  { rewrite (sum_const (CR_of_Q R (Qmake 1 1) * CR_of_Q R (Qmake 1 1)) N).
    assert (Hr : CReq R ((CR_of_Q R (Qmake 1 1) * CR_of_Q R (Qmake 1 1)) * INR (S N))
                        (INR (S N))) by ring.
    rewrite Hr. apply CReq_refl. }
  rewrite Hs1 in Hcs0. rewrite Hs2 in Hcs0.
  assert (Hpart : CRle R (CRsum (fun k => g7S k k * g7S k k) N)
                         (CRsum (fun k => CRsum (fun l => g7S k l * g7S k l) N) N)).
  { apply sum_Rle. intro k. intro Hk.
    apply (CRsum_nonneg_term_le N (fun l => g7S k l * g7S k l)).
    - intro l. apply CRsqr_nonneg.
    - exact Hk. }
  assert (Hle1 : CRle R (CRsum (fun k => g7S k k * g7S k k) N)
                         (CRsum (fun i => CRsum (fun j => g7G i j * g7G i j) M) M)).
  { eapply CRle_trans.
    - exact Hpart.
    - apply (proj2 g7_fourway). }
  assert (Htr : CReq R (CRsum (fun k => g7S k k) N) (INR (S M))).
  { exact g7_trace. }
  assert (Htr2 : CReq R (INR (S M) * INR (S M))
                        (CRsum (fun k => g7S k k) N * CRsum (fun k => g7S k k) N)).
  { rewrite Htr. apply CReq_refl. }
  assert (Hstep1 : CRle R (INR (S M) * INR (S M))
      (CRsum (fun i => CRsum (fun j => g7G i j * g7G i j) M) M * INR (S N))).
  { eapply CRle_trans.
    - apply (proj2 Htr2).
    - eapply CRle_trans.
      + exact Hcs0.
      + apply (CRmult_le_compat_r (INR (S N))
                  (CRsum (fun k => g7S k k * g7S k k) N)
                  (CRsum (fun i => CRsum (fun j => g7G i j * g7G i j) M) M)).
        * exact (CR0_le_INR (S N)).
        * exact Hle1. }
  assert (Hle2 : CRle R
      (CRsum (fun i => CRsum (fun j => g7G i j * g7G i j) M) M * INR (S N))
      (INR (S N) * (INR (S M) + INR (S M) * INR M * mu * mu))).
  { apply (CRle_trans (R:=R) _ (INR (S N) * CRsum (fun i => CRsum (fun j => g7G i j * g7G i j) M) M)).
    - apply (proj1 (CRmult_comm (INR (S N))
               (CRsum (fun i => CRsum (fun j => g7G i j * g7G i j) M) M))).
    - apply (CRmult_le_compat_l (INR (S N))).
      + exact (CR0_le_INR (S N)).
      + exact g7_bunching. }
  assert (Hstep2 : CRle R (INR (S M) * INR (S M))
      (INR (S N) * (INR (S M) + INR (S M) * INR M * mu * mu))).
  { eapply CRle_trans.
    - exact Hstep1.
    - exact Hle2. }
  assert (H0A : CRlt R (CR_of_Q R (Qmake 0 1)) (INR (S M))).
  { apply (CRlt_le_trans (R:=R) _ (CR_of_Q R (Qmake 1 1))).
    - exact (CRzero_lt_one R).
    - apply (CRle_INR 1 (S M)). lia. }
  assert (Hr1 : CReq R
    ((INR (S M) * (INR (S M) - INR (S N)))
     + INR (S M) * INR (S N))
    (INR (S M) * INR (S M))).
  { unfold CRminus. ring. }
  assert (Hr2 : CReq R (INR (S N) * (INR (S M) + INR (S M) * INR M * mu * mu))
    (INR (S M) * (INR (S N) * INR M * (mu * mu))
     + INR (S M) * INR (S N))) by ring.
  assert (Hvi0 : CRle R (INR (S M) * (INR (S M) - INR (S N)))
                        (INR (S M) * (INR (S N) * INR M * (mu * mu)))).
  { apply (CRplus_le_reg_r (INR (S M) * INR (S N))
             (INR (S M) * (INR (S M) - INR (S N)))
             (INR (S M) * (INR (S N) * INR M * (mu * mu)))).
    eapply CRle_trans.
    - apply (proj2 Hr1).
    - eapply CRle_trans.
      + exact Hstep2.
      + apply (proj2 Hr2). }
  apply (CRmult_le_reg_r (INR (S M)) (INR (S M) - INR (S N))
           (INR (S N) * INR M * mu * mu)).
  - exact H0A.
  - assert (Hq : CReq R (INR (S N) * INR M * mu * mu)
                        (INR (S N) * INR M * (mu * mu))) by ring.
    rewrite Hq. exact Hvi0.
Qed.

End G7Welch.

(* ============ P4. 顶层包装：G-8 消费签名逐字对齐 ============ *)

(* 消费方形态：M' 个原子（M' ≥ 1）、维度 N'、N' < M'，
   结论 CRle R (INR M' - INR N') (INR N' * INR (Nat.pred M') * mu * mu)
   ——即 probe_g8_synthesis_cr 的 Hwelch 前提。
   前提的求和上界为 Nat.pred（CRsum 含端点：k ≤ N'−1 共 N' 项）。 *)
Theorem g7_welch_lower {R : ConstructiveReals} (M N : nat)
  (v : nat -> nat -> CRcarrier R)
  (mu : CRcarrier R)
  (HN1 : le 1 N) (HNM : lt N M)
  (Hunit : forall i, lt i M ->
    CReq R (CRsum (fun k => v i k * v i k) (Nat.pred N)) (CR_of_Q R (Qmake 1 1)))
  (Hcoh : forall i j, lt i M -> lt j M -> i <> j ->
    CRle R (CRabs R (CRsum (fun k => v i k * v j k) (Nat.pred N))) mu) :
  CRle R (INR M - INR N) (INR N * INR (Nat.pred M) * mu * mu).
Proof.
  assert (HM1 : le 1 M) by lia.
  assert (Hm0 : S (Nat.pred M) = M) by lia.
  assert (Hn0 : S (Nat.pred N) = N) by lia.
  assert (Hn0m0 : lt (Nat.pred N) (Nat.pred M)) by lia.
  assert (Hunit' : forall i, le i (Nat.pred M) ->
    CReq R (CRsum (fun k => v i k * v i k) (Nat.pred N)) (CR_of_Q R (Qmake 1 1))).
  { intros i Hi. apply Hunit. lia. }
  assert (Hcoh' : forall i j, le i (Nat.pred M) -> le j (Nat.pred M) -> i <> j ->
    CRle R (CRabs R (CRsum (fun k => v i k * v j k) (Nat.pred N))) mu).
  { intros i j Hi Hj Hne. apply Hcoh.
    - lia.
    - lia.
    - exact Hne. }
  assert (Hgoal : CRle R (INR (S (Nat.pred M)) - INR (S (Nat.pred N)))
                         (INR (S (Nat.pred N)) * INR (Nat.pred M) * mu * mu)).
  { exact (g7_welch_core (Nat.pred M) (Nat.pred N) v mu Hunit' Hcoh'). }
  rewrite Hm0 in Hgoal. rewrite Hn0 in Hgoal.
  exact Hgoal.
Qed.

Print Assumptions g7_welch_lower.
Print Assumptions g7_welch_core.
Print Assumptions g7_bunching.
Print Assumptions g7_fourway.
Print Assumptions g7_trace.
Print Assumptions cs_core.

(* 提取验证（Set 层帧算子/Gram 函数可提取；CRcarrier 为抽象类型参数） *)
Extraction "g7_welch_cr.ml" g7S g7G g7_welch_lower.

(* 审计：Print Assumptions g7_welch_lower.（终态应为 Closed under the global
   context；骨架阶段 Admitted 未清前不开启。） *)
