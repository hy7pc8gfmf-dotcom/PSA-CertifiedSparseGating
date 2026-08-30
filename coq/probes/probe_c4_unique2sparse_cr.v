(* ============================================================
   CS-21 构造性 C=4 四原子合成单射 / 2-sparse 唯一恢复
   （probe_c4_unique2sparse_cr.v——待办 #1 的 I 注入性核，
   2026-08-30。经典 R 轨道 probe_c4_unique2sparse.v 的 D 层数值
   认证在先；本文件按 M2 红线以纯构造性路线给出最终定理。）

   数学内容（严格对角占优 ⟹ 合成映射单射，零经典排中）：
     四原子 u 0..3（ψ3/ψ13/ψ53/ψ213 抽象梯子），逐对相干
     |⟨u_i,u_j⟩| ≤ pfb4 i j（六对有理上界，与经典 D 层同数值），
     对角 ⟨u_i,u_i⟩ = 1。列和 C_j = Σ_i pfb4 i j 全部 < 1，
     最大列 ρ = C_2 = 159/1200 + 689/2080 + 11289/33920 ≈ 0.797。
     若 Σ_j c_j·u_j = 0：与 u_i 内积提拉出四行线性方程
       |c_i| ≤ Σ_j |c_j|·pfb4 j i（逐行；对角项被方程吸收，
       pfb i i = 0 补零进四项陈述），
     求和得 S := Σ_j |c_j| ≤ Σ_j C_j·|c_j| ≤ ρ·S（列重组经
     ring + CR_of_Q_plus 分配桥）⟹（CRle_scaled_le_zero）
     S ≤ 0 ⟹ S ≡ 0 ⟹ 逐项 |c_j| ≤ S = 0 ⟹ c_j ≡ 0
     （CRle_abs_self / −|c| ≤ c 夹逼）。
     ★ 经典轨道的「max 枢轴 4 元素 case analysis」被求和技巧
     消灭——CR 上序不可判定，本路线不需要任何分情形。

   纪律（M2 红线）：纯构造性——零经典逻辑、零经典实数公理，
   不 Require Stdlib.Reals；Set 层 CRcarrier/CRComplex；Prop 层
   仅 CRle/CReq 界与相等（无信息内容，同 taugrid C-TA3 口径）；
   接口化 {R : ConstructiveReals}；Q 层字面量判定 lia 收口；
   可提取（ρ 窗口 + pfb4 表 + 列检查 bool）。
   非平凡核心定理 = row_abs_le（行占优）+ c4u_sum_abs_zero
   （列收缩坍缩）；最终定理 = c4u_synthesis_injective（含
   c4u_2sparse_unique 推论）。
   依赖：ca_rip_cr（CRcombo_ip_rec/CRle_scaled_le_zero/CRsum 系，
   全 Closed）。
   ============================================================ *)
Require Import ConstructiveReals.
From Stdlib Require Import ConstructiveRealsMorphisms.
From Stdlib Require Import ConstructiveAbs.
From Stdlib Require Import ConstructiveSum.
Require Import Stdlib.QArith.QArith.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.micromega.Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat seq eqtype div.
Require Import ca_rip_cr.

Unset Implicit Arguments.

Local Open Scope ConstructiveReals.
(* 不打开 Q_scope——Q 值全部通过 Qmake 辅助构造（同 ca_rip_cr） *)

(* ============ Q 层：逐对有理上界表（与经典 D 层同数值） ============ *)

(* pfb4 i j：|⟨u_i,u_j⟩| 的有理上界（六对，对称填充；对角支置 0——
   行引理统一四项陈述用）。
   u 0 ↔ ψ_3，u 1 ↔ ψ_13，u 2 ↔ ψ_53，u 3 ↔ ψ_213。 *)
Definition pfb4 (i j : nat) : Q :=
  match i with
  | 0%nat =>
      match j with
      | 1%nat => Qmake 39 120
      | 2%nat => Qmake 159 1200
      | 3%nat => Qmake 639 10500
      | _ => Qmake 0 1
      end
  | 1%nat =>
      match j with
      | 0%nat => Qmake 39 120
      | 2%nat => Qmake 689 2080
      | 3%nat => Qmake 2769 20800
      | _ => Qmake 0 1
      end
  | 2%nat =>
      match j with
      | 0%nat => Qmake 159 1200
      | 1%nat => Qmake 689 2080
      | 3%nat => Qmake 11289 33920
      | _ => Qmake 0 1
      end
  | _ =>
      match j with
      | 0%nat => Qmake 639 10500
      | 1%nat => Qmake 2769 20800
      | 2%nat => Qmake 11289 33920
      | _ => Qmake 0 1
      end
  end.

(* 列和 C_j = Σ_i pfb4 i j（对角为 0）与最大列 ρ = C_2（ψ53 列） *)
Definition col4 (j : nat) : Q := pfb4 0 j + pfb4 1 j + pfb4 2 j + pfb4 3 j.
Definition rho4 : Q := col4 2.

(* ρ < 1：0.797... < 1（Q 层精确判定）
   unfold 顺序：定义（rho4/col4/pfb4）先行，谓词（Qlt/Qplus）在后——
   后展开的节点才能被覆盖（Qplus 节点由 col4 展开产生） *)
Lemma rho4_lt_one : Qlt rho4 (Qmake 1 1).
Proof.
  unfold rho4, col4, pfb4, Qlt, Qplus. cbn [Qnum Qden]. lia.
Qed.

(* 各列 ≤ ρ（ρ 即最大列） *)
Lemma col4_le_rho4 : forall j, le j 3 -> Qle (col4 j) rho4.
Proof.
  intros j Hj.
  destruct j as [|[|[|[|j4]]]].
  - unfold rho4, col4, pfb4, Qle, Qplus. cbn [Qnum Qden]. lia.
  - unfold rho4, col4, pfb4, Qle, Qplus. cbn [Qnum Qden]. lia.
  - unfold rho4, col4, pfb4, Qle, Qplus. cbn [Qnum Qden]. lia.
  - unfold rho4, col4, pfb4, Qle, Qplus. cbn [Qnum Qden]. lia.
  - exfalso. lia.
Qed.

(* ============ CR 层：四原子注入性核 ============ *)

Section C4Unique2SparseCR.

Context {R : ConstructiveReals}.
Add Ring CR_ring : (CRisRing R).

Variable u : nat -> @CRComplex R.

(* 单位范数：⟨u_j,u_j⟩ = 1 *)
Hypothesis Hu_unit : forall j, le j 3 ->
  CReq R (CRip (u j) (u j)) (CR_of_Q R (Qmake 1 1)).

(* 逐对相干上界：|⟨u_i,u_j⟩| ≤ pfb4 i j（i ≠ j） *)
Hypothesis Hu_pf : forall i j, le i 3 -> le j 3 -> i <> j ->
  CRle R (CRabs R (CRip (u i) (u j))) (CR_of_Q R (pfb4 i j)).

(* ---------- I1 组合内积线性展开 ---------- *)

(* ⟨combo 3, v⟩ ≡ Σ_j c_j·⟨u_j,v⟩（CRcombo_ip_rec 三步 + ring） *)
Lemma combo3_ip_expand (c : nat -> CRcarrier R) (v : CRComplex) :
  CReq R (CRip (CRcombo 3 c u) v)
    (c 0%nat * CRip (u 0%nat) v
     + (c 1%nat * CRip (u 1%nat) v
     + (c 2%nat * CRip (u 2%nat) v
     +  c 3%nat * CRip (u 3%nat) v))).
Proof.
  setoid_rewrite (CRcombo_ip_rec (R:=R) 2 c u v).
  setoid_rewrite (CRcombo_ip_rec (R:=R) 1 c u v).
  setoid_rewrite (CRcombo_ip_rec (R:=R) 0 c u v).
  unfold CRip. cbn [CRcombo cre cim]. ring.
Qed.

(* ---------- I2 零组合的内积坍缩 ---------- *)

(* 零组合 ⟹ 0 ≡ Σ_j c_j·⟨u_j,u_i⟩（含对角项） *)
Lemma row_ip_zero (c : nat -> CRcarrier R) (Hcombo : CRcombo 3 c u = CRzero) :
  forall i, le i 3 ->
  CReq R (CR_of_Q R (Qmake 0 1))
    (c 0%nat * CRip (u 0%nat) (u i)
     + (c 1%nat * CRip (u 1%nat) (u i)
     + (c 2%nat * CRip (u 2%nat) (u i)
     +  c 3%nat * CRip (u 3%nat) (u i)))).
Proof.
  intros i Hi.
  apply (CReq_trans (CR_of_Q R (Qmake 0 1))
           (CRip (u i) (CRcombo 3 c u))
           (c 0%nat * CRip (u 0%nat) (u i)
            + (c 1%nat * CRip (u 1%nat) (u i)
            + (c 2%nat * CRip (u 2%nat) (u i)
            +  c 3%nat * CRip (u 3%nat) (u i))))).
  - (* 0 ≡ ⟨u_i, combo⟩ *)
    rewrite Hcombo. unfold CRip, CRzero. cbn [cre cim]. ring.
  - (* ⟨u_i, combo⟩ ≡ 展开 *)
    apply (CReq_trans (CRip (u i) (CRcombo 3 c u))
             (CRip (CRcombo 3 c u) (u i))
             (c 0%nat * CRip (u 0%nat) (u i)
              + (c 1%nat * CRip (u 1%nat) (u i)
              + (c 2%nat * CRip (u 2%nat) (u i)
              +  c 3%nat * CRip (u 3%nat) (u i))))).
    + unfold CRip. ring.
    + exact (combo3_ip_expand c (u i)).
Qed.

(* ---------- 行占优三工具（通用，全节共用） ---------- *)

(* 解出自变量：0 ≡ self + y ⟹ |self| ≤ |y| *)
Lemma c4u_solve_self (self y : CRcarrier R) :
  CReq R (CR_of_Q R (Qmake 0 1)) (self + y) ->
  CRle R (CRabs R self) (CRabs R y).
Proof.
  intros Hz.
  assert (Hs : CReq R self (CRopp R y)).
  { apply (CRplus_eq_reg_l (R:=R) y self (CRopp R y)).
    apply (CReq_trans (y + self) (CR_of_Q R (Qmake 0 1)) (y + CRopp R y)).
    - apply (CReq_trans (y + self) (self + y) (CR_of_Q R (Qmake 0 1))).
      + ring.
      + exact (CReq_sym (CR_of_Q R (Qmake 0 1)) (self + y) Hz).
    - ring. }
  setoid_rewrite Hs. setoid_rewrite (CRabs_opp y). apply CRle_refl.
Qed.

(* 三项三角不等式：|b1 + (b2 + b3)| ≤ |b1| + (|b2| + |b3|) *)
Lemma c4u_abs_tri3 (b1 b2 b3 : CRcarrier R) :
  CRle R (CRabs R (b1 + (b2 + b3)))
         (CRabs R b1 + (CRabs R b2 + CRabs R b3)).
Proof.
  apply (CRle_trans (R:=R) (CRabs R (b1 + (b2 + b3)))
           (CRabs R b1 + CRabs R (b2 + b3))
           (CRabs R b1 + (CRabs R b2 + CRabs R b3))).
  - apply CRabs_triang.
  - apply CRplus_le_compat; [apply CRle_refl | apply CRabs_triang].
Qed.

(* 三项逐对收口 *)
Lemma c4u_term3_le (a b1 b2 b3 w1 w2 w3 : CRcarrier R) :
  CRle R (CRabs R a) (CRabs R b1 + (CRabs R b2 + CRabs R b3)) ->
  CRle R (CRabs R b1) w1 ->
  CRle R (CRabs R b2) w2 ->
  CRle R (CRabs R b3) w3 ->
  CRle R (CRabs R a) (w1 + (w2 + w3)).
Proof.
  intros Ha H1 H2 H3.
  apply (CRle_trans (R:=R) (CRabs R a)
           (CRabs R b1 + (CRabs R b2 + CRabs R b3))
           (w1 + (w2 + w3))).
  - exact Ha.
  - apply CRplus_le_compat; [exact H1 | apply CRplus_le_compat; [exact H2 | exact H3]].
Qed.

(* 零对角项并入：a ≤ t ⟹ a ≤ a·0 + t *)
Lemma c4u_zero_term_absorb (a t : CRcarrier R) :
  CRle R a t -> CRle R a (a * CR_of_Q R (Qmake 0 1) + t).
Proof.
  intros Ha.
  assert (Hz : CReq R (a * CR_of_Q R (Qmake 0 1) + t) t) by ring.
  apply (CRle_trans (R:=R) a t (a * CR_of_Q R (Qmake 0 1) + t)).
  - exact Ha.
  - exact (proj1 Hz).
Qed.

(* ---------- I3+I4 ★ 核心定理一：行占优 ---------- *)

Lemma row_abs_le (c : nat -> CRcarrier R) (Hcombo : CRcombo 3 c u = CRzero) :
  forall i, le i 3 ->
  CRle R (CRabs R (c i))
    (CRabs R (c 0%nat) * CR_of_Q R (pfb4 0%nat i)
     + (CRabs R (c 1%nat) * CR_of_Q R (pfb4 1%nat i)
     + (CRabs R (c 2%nat) * CR_of_Q R (pfb4 2%nat i)
     +  CRabs R (c 3%nat) * CR_of_Q R (pfb4 3%nat i)))).
Proof.
  intros i Hi.
  destruct i as [|[|[|[|i4]]]].
  - (* i = 0 *)
    assert (H03 : le 0 3) by lia. assert (H13 : le 1 3) by lia.
    assert (H23 : le 2 3) by lia. assert (H33 : le 3 3) by lia.
    assert (H10 : (1 <> 0)%nat) by discriminate.
    assert (H20 : (2 <> 0)%nat) by discriminate.
    assert (H30 : (3 <> 0)%nat) by discriminate.
    pose proof (row_ip_zero c Hcombo 0 H03) as Hz.
    setoid_rewrite (Hu_unit 0 H03) in Hz.
    setoid_rewrite (CRmult_1_r (c 0%nat)) in Hz.
    pose proof (c4u_solve_self (c 0%nat)
      (c 1%nat * CRip (u 1%nat) (u 0%nat)
       + (c 2%nat * CRip (u 2%nat) (u 0%nat)
       +  c 3%nat * CRip (u 3%nat) (u 0%nat))) Hz) as Hab.
    pose proof (c4u_abs_tri3
      (c 1%nat * CRip (u 1%nat) (u 0%nat))
      (c 2%nat * CRip (u 2%nat) (u 0%nat))
      (c 3%nat * CRip (u 3%nat) (u 0%nat))) as Htri.
    pose proof (Hu_pf 1 0 H13 H03 H10) as Hp1.
    pose proof (Hu_pf 2 0 H23 H03 H20) as Hp2.
    pose proof (Hu_pf 3 0 H33 H03 H30) as Hp3.
    apply (CRle_trans (R:=R) (CRabs R (c 0%nat))
      (CRabs R (c 1%nat) * CR_of_Q R (pfb4 1 0)
       + (CRabs R (c 2%nat) * CR_of_Q R (pfb4 2 0)
       +  CRabs R (c 3%nat) * CR_of_Q R (pfb4 3 0)))
      (CRabs R (c 0%nat) * CR_of_Q R (pfb4 0 0)
       + (CRabs R (c 1%nat) * CR_of_Q R (pfb4 1 0)
       + (CRabs R (c 2%nat) * CR_of_Q R (pfb4 2 0)
       +  CRabs R (c 3%nat) * CR_of_Q R (pfb4 3 0))))).
    - apply (c4u_term3_le (c 0%nat)
      (c 1%nat * CRip (u 1%nat) (u 0%nat))
      (c 2%nat * CRip (u 2%nat) (u 0%nat))
      (c 3%nat * CRip (u 3%nat) (u 0%nat))
      (CRabs R (c 1%nat) * CR_of_Q R (pfb4 1 0))
      (CRabs R (c 2%nat) * CR_of_Q R (pfb4 2 0))
      (CRabs R (c 3%nat) * CR_of_Q R (pfb4 3 0))).
    + apply (CRle_trans (R:=R) (CRabs R (c 0%nat))
             (CRabs R (c 1%nat * CRip (u 1%nat) (u 0%nat)
               + (c 2%nat * CRip (u 2%nat) (u 0%nat)
               +  c 3%nat * CRip (u 3%nat) (u 0%nat))))
             (CRabs R (c 1%nat * CRip (u 1%nat) (u 0%nat))
              + (CRabs R (c 2%nat * CRip (u 2%nat) (u 0%nat))
              +  CRabs R (c 3%nat * CRip (u 3%nat) (u 0%nat))))).
      * exact Hab.
      * exact Htri.
    + setoid_rewrite (CRabs_mult (c 1%nat) (_)).
      apply (CRmult_le_compat_l (R:=R) (CRabs R (c 1%nat)));
        [apply CRabs_pos | exact Hp1].
    + setoid_rewrite (CRabs_mult (c 2%nat) (_)).
      apply (CRmult_le_compat_l (R:=R) (CRabs R (c 2%nat)));
        [apply CRabs_pos | exact Hp2].
    + setoid_rewrite (CRabs_mult (c 3%nat) (_)).
      apply (CRmult_le_compat_l (R:=R) (CRabs R (c 3%nat)));
        [apply CRabs_pos | exact Hp3].
    - assert (Hz4 : CReq R
        (CRabs R (c 1%nat) * CR_of_Q R (pfb4 1 0)
         + (CRabs R (c 2%nat) * CR_of_Q R (pfb4 2 0)
         +  CRabs R (c 3%nat) * CR_of_Q R (pfb4 3 0)))
        (CRabs R (c 0%nat) * CR_of_Q R (pfb4 0 0)
         + (CRabs R (c 1%nat) * CR_of_Q R (pfb4 1 0)
         + (CRabs R (c 2%nat) * CR_of_Q R (pfb4 2 0)
         +  CRabs R (c 3%nat) * CR_of_Q R (pfb4 3 0)))))
        by (unfold pfb4; ring).
      exact (proj2 Hz4).
  - (* i = 1 *)
    assert (H03 : le 0 3) by lia. assert (H13 : le 1 3) by lia.
    assert (H23 : le 2 3) by lia. assert (H33 : le 3 3) by lia.
    assert (H01 : (0 <> 1)%nat) by discriminate.
    assert (H21 : (2 <> 1)%nat) by discriminate.
    assert (H31 : (3 <> 1)%nat) by discriminate.
    pose proof (row_ip_zero c Hcombo 1 H13) as Hz.
    setoid_rewrite (Hu_unit 1 H13) in Hz.
    setoid_rewrite (CRmult_1_r (c 1%nat)) in Hz.
    assert (Hz2 : CReq R (CR_of_Q R (Qmake 0 1))
      (c 1%nat + (c 0%nat * CRip (u 0%nat) (u 1%nat)
       + (c 2%nat * CRip (u 2%nat) (u 1%nat)
       +  c 3%nat * CRip (u 3%nat) (u 1%nat))))).
    { apply (CReq_trans (CR_of_Q R (Qmake 0 1))
             (c 0%nat * CRip (u 0%nat) (u 1%nat)
              + (c 1%nat + (c 2%nat * CRip (u 2%nat) (u 1%nat)
              +  c 3%nat * CRip (u 3%nat) (u 1%nat))))).
      - exact Hz.
      - ring. }
    pose proof (c4u_solve_self (c 1%nat)
      (c 0%nat * CRip (u 0%nat) (u 1%nat)
       + (c 2%nat * CRip (u 2%nat) (u 1%nat)
       +  c 3%nat * CRip (u 3%nat) (u 1%nat))) Hz2) as Hab.
    pose proof (c4u_abs_tri3
      (c 0%nat * CRip (u 0%nat) (u 1%nat))
      (c 2%nat * CRip (u 2%nat) (u 1%nat))
      (c 3%nat * CRip (u 3%nat) (u 1%nat))) as Htri.
    pose proof (Hu_pf 0 1 H03 H13 H01) as Hp0.
    pose proof (Hu_pf 2 1 H23 H13 H21) as Hp2.
    pose proof (Hu_pf 3 1 H33 H13 H31) as Hp3.
    apply (CRle_trans (R:=R) (CRabs R (c 1%nat))
      (CRabs R (c 0%nat) * CR_of_Q R (pfb4 0 1)
       + (CRabs R (c 2%nat) * CR_of_Q R (pfb4 2 1)
       +  CRabs R (c 3%nat) * CR_of_Q R (pfb4 3 1)))
      (CRabs R (c 0%nat) * CR_of_Q R (pfb4 0 1)
       + (CRabs R (c 1%nat) * CR_of_Q R (pfb4 1 1)
       + (CRabs R (c 2%nat) * CR_of_Q R (pfb4 2 1)
       +  CRabs R (c 3%nat) * CR_of_Q R (pfb4 3 1))))).
    - apply (c4u_term3_le (c 1%nat)
      (c 0%nat * CRip (u 0%nat) (u 1%nat))
      (c 2%nat * CRip (u 2%nat) (u 1%nat))
      (c 3%nat * CRip (u 3%nat) (u 1%nat))
      (CRabs R (c 0%nat) * CR_of_Q R (pfb4 0 1))
      (CRabs R (c 2%nat) * CR_of_Q R (pfb4 2 1))
      (CRabs R (c 3%nat) * CR_of_Q R (pfb4 3 1))).
    + apply (CRle_trans (R:=R) (CRabs R (c 1%nat))
             (CRabs R (c 0%nat * CRip (u 0%nat) (u 1%nat)
               + (c 2%nat * CRip (u 2%nat) (u 1%nat)
               +  c 3%nat * CRip (u 3%nat) (u 1%nat))))
             (CRabs R (c 0%nat * CRip (u 0%nat) (u 1%nat))
              + (CRabs R (c 2%nat * CRip (u 2%nat) (u 1%nat))
              +  CRabs R (c 3%nat * CRip (u 3%nat) (u 1%nat))))).
      * exact Hab.
      * exact Htri.
    + setoid_rewrite (CRabs_mult (c 0%nat) (_)).
      apply (CRmult_le_compat_l (R:=R) (CRabs R (c 0%nat)));
        [apply CRabs_pos | exact Hp0].
    + setoid_rewrite (CRabs_mult (c 2%nat) (_)).
      apply (CRmult_le_compat_l (R:=R) (CRabs R (c 2%nat)));
        [apply CRabs_pos | exact Hp2].
    + setoid_rewrite (CRabs_mult (c 3%nat) (_)).
      apply (CRmult_le_compat_l (R:=R) (CRabs R (c 3%nat)));
        [apply CRabs_pos | exact Hp3].
    - assert (Hz4 : CReq R
        (CRabs R (c 0%nat) * CR_of_Q R (pfb4 0 1)
         + (CRabs R (c 2%nat) * CR_of_Q R (pfb4 2 1)
         +  CRabs R (c 3%nat) * CR_of_Q R (pfb4 3 1)))
        (CRabs R (c 0%nat) * CR_of_Q R (pfb4 0 1)
         + (CRabs R (c 1%nat) * CR_of_Q R (pfb4 1 1)
         + (CRabs R (c 2%nat) * CR_of_Q R (pfb4 2 1)
         +  CRabs R (c 3%nat) * CR_of_Q R (pfb4 3 1)))))
        by (unfold pfb4; ring).
      exact (proj2 Hz4).
  - (* i = 2 *)
    assert (H03 : le 0 3) by lia. assert (H13 : le 1 3) by lia.
    assert (H23 : le 2 3) by lia. assert (H33 : le 3 3) by lia.
    assert (H02 : (0 <> 2)%nat) by discriminate.
    assert (H12 : (1 <> 2)%nat) by discriminate.
    assert (H32 : (3 <> 2)%nat) by discriminate.
    pose proof (row_ip_zero c Hcombo 2 H23) as Hz.
    setoid_rewrite (Hu_unit 2 H23) in Hz.
    setoid_rewrite (CRmult_1_r (c 2%nat)) in Hz.
    assert (Hz2 : CReq R (CR_of_Q R (Qmake 0 1))
      (c 2%nat + (c 0%nat * CRip (u 0%nat) (u 2%nat)
       + (c 1%nat * CRip (u 1%nat) (u 2%nat)
       +  c 3%nat * CRip (u 3%nat) (u 2%nat))))).
    { apply (CReq_trans (CR_of_Q R (Qmake 0 1))
             (c 0%nat * CRip (u 0%nat) (u 2%nat)
              + (c 1%nat * CRip (u 1%nat) (u 2%nat)
              + (c 2%nat + c 3%nat * CRip (u 3%nat) (u 2%nat))))).
      - exact Hz.
      - ring. }
    pose proof (c4u_solve_self (c 2%nat)
      (c 0%nat * CRip (u 0%nat) (u 2%nat)
       + (c 1%nat * CRip (u 1%nat) (u 2%nat)
       +  c 3%nat * CRip (u 3%nat) (u 2%nat))) Hz2) as Hab.
    pose proof (c4u_abs_tri3
      (c 0%nat * CRip (u 0%nat) (u 2%nat))
      (c 1%nat * CRip (u 1%nat) (u 2%nat))
      (c 3%nat * CRip (u 3%nat) (u 2%nat))) as Htri.
    pose proof (Hu_pf 0 2 H03 H23 H02) as Hp0.
    pose proof (Hu_pf 1 2 H13 H23 H12) as Hp1.
    pose proof (Hu_pf 3 2 H33 H23 H32) as Hp3.
    apply (CRle_trans (R:=R) (CRabs R (c 2%nat))
      (CRabs R (c 0%nat) * CR_of_Q R (pfb4 0 2)
       + (CRabs R (c 1%nat) * CR_of_Q R (pfb4 1 2)
       +  CRabs R (c 3%nat) * CR_of_Q R (pfb4 3 2)))
      (CRabs R (c 0%nat) * CR_of_Q R (pfb4 0 2)
       + (CRabs R (c 1%nat) * CR_of_Q R (pfb4 1 2)
       + (CRabs R (c 2%nat) * CR_of_Q R (pfb4 2 2)
       +  CRabs R (c 3%nat) * CR_of_Q R (pfb4 3 2))))).
    - apply (c4u_term3_le (c 2%nat)
      (c 0%nat * CRip (u 0%nat) (u 2%nat))
      (c 1%nat * CRip (u 1%nat) (u 2%nat))
      (c 3%nat * CRip (u 3%nat) (u 2%nat))
      (CRabs R (c 0%nat) * CR_of_Q R (pfb4 0 2))
      (CRabs R (c 1%nat) * CR_of_Q R (pfb4 1 2))
      (CRabs R (c 3%nat) * CR_of_Q R (pfb4 3 2))).
    + apply (CRle_trans (R:=R) (CRabs R (c 2%nat))
             (CRabs R (c 0%nat * CRip (u 0%nat) (u 2%nat)
               + (c 1%nat * CRip (u 1%nat) (u 2%nat)
               +  c 3%nat * CRip (u 3%nat) (u 2%nat))))
             (CRabs R (c 0%nat * CRip (u 0%nat) (u 2%nat))
              + (CRabs R (c 1%nat * CRip (u 1%nat) (u 2%nat))
              +  CRabs R (c 3%nat * CRip (u 3%nat) (u 2%nat))))).
      * exact Hab.
      * exact Htri.
    + setoid_rewrite (CRabs_mult (c 0%nat) (_)).
      apply (CRmult_le_compat_l (R:=R) (CRabs R (c 0%nat)));
        [apply CRabs_pos | exact Hp0].
    + setoid_rewrite (CRabs_mult (c 1%nat) (_)).
      apply (CRmult_le_compat_l (R:=R) (CRabs R (c 1%nat)));
        [apply CRabs_pos | exact Hp1].
    + setoid_rewrite (CRabs_mult (c 3%nat) (_)).
      apply (CRmult_le_compat_l (R:=R) (CRabs R (c 3%nat)));
        [apply CRabs_pos | exact Hp3].
    - assert (Hz4 : CReq R
        (CRabs R (c 0%nat) * CR_of_Q R (pfb4 0 2)
         + (CRabs R (c 1%nat) * CR_of_Q R (pfb4 1 2)
         +  CRabs R (c 3%nat) * CR_of_Q R (pfb4 3 2)))
        (CRabs R (c 0%nat) * CR_of_Q R (pfb4 0 2)
         + (CRabs R (c 1%nat) * CR_of_Q R (pfb4 1 2)
         + (CRabs R (c 2%nat) * CR_of_Q R (pfb4 2 2)
         +  CRabs R (c 3%nat) * CR_of_Q R (pfb4 3 2)))))
        by (unfold pfb4; ring).
      exact (proj2 Hz4).
  - (* i = 3 *)
    assert (H03 : le 0 3) by lia. assert (H13 : le 1 3) by lia.
    assert (H23 : le 2 3) by lia. assert (H33 : le 3 3) by lia.
    assert (H03n : (0 <> 3)%nat) by discriminate.
    assert (H13n : (1 <> 3)%nat) by discriminate.
    assert (H23n : (2 <> 3)%nat) by discriminate.
    pose proof (row_ip_zero c Hcombo 3 H33) as Hz.
    setoid_rewrite (Hu_unit 3 H33) in Hz.
    setoid_rewrite (CRmult_1_r (c 3%nat)) in Hz.
    assert (Hz2 : CReq R (CR_of_Q R (Qmake 0 1))
      (c 3%nat + (c 0%nat * CRip (u 0%nat) (u 3%nat)
       + (c 1%nat * CRip (u 1%nat) (u 3%nat)
       +  c 2%nat * CRip (u 2%nat) (u 3%nat))))).
    { apply (CReq_trans (CR_of_Q R (Qmake 0 1))
             (c 0%nat * CRip (u 0%nat) (u 3%nat)
              + (c 1%nat * CRip (u 1%nat) (u 3%nat)
              + (c 2%nat * CRip (u 2%nat) (u 3%nat) + c 3%nat)))).
      - exact Hz.
      - ring. }
    pose proof (c4u_solve_self (c 3%nat)
      (c 0%nat * CRip (u 0%nat) (u 3%nat)
       + (c 1%nat * CRip (u 1%nat) (u 3%nat)
       +  c 2%nat * CRip (u 2%nat) (u 3%nat))) Hz2) as Hab.
    pose proof (c4u_abs_tri3
      (c 0%nat * CRip (u 0%nat) (u 3%nat))
      (c 1%nat * CRip (u 1%nat) (u 3%nat))
      (c 2%nat * CRip (u 2%nat) (u 3%nat))) as Htri.
    pose proof (Hu_pf 0 3 H03 H33 H03n) as Hp0.
    pose proof (Hu_pf 1 3 H13 H33 H13n) as Hp1.
    pose proof (Hu_pf 2 3 H23 H33 H23n) as Hp2.
    apply (CRle_trans (R:=R) (CRabs R (c 3%nat))
      (CRabs R (c 0%nat) * CR_of_Q R (pfb4 0 3)
       + (CRabs R (c 1%nat) * CR_of_Q R (pfb4 1 3)
       +  CRabs R (c 2%nat) * CR_of_Q R (pfb4 2 3)))
      (CRabs R (c 0%nat) * CR_of_Q R (pfb4 0 3)
       + (CRabs R (c 1%nat) * CR_of_Q R (pfb4 1 3)
       + (CRabs R (c 2%nat) * CR_of_Q R (pfb4 2 3)
       +  CRabs R (c 3%nat) * CR_of_Q R (pfb4 3 3))))).
    - apply (c4u_term3_le (c 3%nat)
      (c 0%nat * CRip (u 0%nat) (u 3%nat))
      (c 1%nat * CRip (u 1%nat) (u 3%nat))
      (c 2%nat * CRip (u 2%nat) (u 3%nat))
      (CRabs R (c 0%nat) * CR_of_Q R (pfb4 0 3))
      (CRabs R (c 1%nat) * CR_of_Q R (pfb4 1 3))
      (CRabs R (c 2%nat) * CR_of_Q R (pfb4 2 3))).
    + apply (CRle_trans (R:=R) (CRabs R (c 3%nat))
             (CRabs R (c 0%nat * CRip (u 0%nat) (u 3%nat)
               + (c 1%nat * CRip (u 1%nat) (u 3%nat)
               +  c 2%nat * CRip (u 2%nat) (u 3%nat))))
             (CRabs R (c 0%nat * CRip (u 0%nat) (u 3%nat))
              + (CRabs R (c 1%nat * CRip (u 1%nat) (u 3%nat))
              +  CRabs R (c 2%nat * CRip (u 2%nat) (u 3%nat))))).
      * exact Hab.
      * exact Htri.
    + setoid_rewrite (CRabs_mult (c 0%nat) (_)).
      apply (CRmult_le_compat_l (R:=R) (CRabs R (c 0%nat)));
        [apply CRabs_pos | exact Hp0].
    + setoid_rewrite (CRabs_mult (c 1%nat) (_)).
      apply (CRmult_le_compat_l (R:=R) (CRabs R (c 1%nat)));
        [apply CRabs_pos | exact Hp1].
    + setoid_rewrite (CRabs_mult (c 2%nat) (_)).
      apply (CRmult_le_compat_l (R:=R) (CRabs R (c 2%nat)));
        [apply CRabs_pos | exact Hp2].
    - assert (Hz4 : CReq R
        (CRabs R (c 0%nat) * CR_of_Q R (pfb4 0 3)
         + (CRabs R (c 1%nat) * CR_of_Q R (pfb4 1 3)
         +  CRabs R (c 2%nat) * CR_of_Q R (pfb4 2 3)))
        (CRabs R (c 0%nat) * CR_of_Q R (pfb4 0 3)
         + (CRabs R (c 1%nat) * CR_of_Q R (pfb4 1 3)
         + (CRabs R (c 2%nat) * CR_of_Q R (pfb4 2 3)
         +  CRabs R (c 3%nat) * CR_of_Q R (pfb4 3 3)))))
        by (unfold pfb4; ring).
      exact (proj2 Hz4).
  - (* i ≥ 4：与 le i 3 矛盾 *)
    exfalso. lia.
Qed.

(* ---------- 列重组（16 项 12 项，ring + CR_of_Q_plus） ---------- *)

(* 两行合并（各 8 单项式——ring 插件对 16 单项式目标失效，全程小步） *)
Lemma c4u_rows_merge01 (c : nat -> CRcarrier R) :
  CReq R (((CRabs R (c 0%nat) * CR_of_Q R (pfb4 0 0)) + ((CRabs R (c 1%nat) * CR_of_Q R (pfb4 0 1)) + ((CRabs R (c 2%nat) * CR_of_Q R (pfb4 0 2)) + (CRabs R (c 3%nat) * CR_of_Q R (pfb4 0 3))))) + ((CRabs R (c 0%nat) * CR_of_Q R (pfb4 1 0)) + ((CRabs R (c 1%nat) * CR_of_Q R (pfb4 1 1)) + ((CRabs R (c 2%nat) * CR_of_Q R (pfb4 1 2)) + (CRabs R (c 3%nat) * CR_of_Q R (pfb4 1 3))))))
         ((CRabs R (c 0%nat) * (CR_of_Q R (pfb4 0 0) + CR_of_Q R (pfb4 0 1))) + ((CRabs R (c 1%nat) * (CR_of_Q R (pfb4 1 0) + CR_of_Q R (pfb4 1 1))) + ((CRabs R (c 2%nat) * (CR_of_Q R (pfb4 2 0) + CR_of_Q R (pfb4 2 1))) + (CRabs R (c 3%nat) * (CR_of_Q R (pfb4 3 0) + CR_of_Q R (pfb4 3 1)))))).
Proof. unfold pfb4. ring. Qed.

Lemma c4u_rows_merge23 (c : nat -> CRcarrier R) :
  CReq R (((CRabs R (c 0%nat) * CR_of_Q R (pfb4 2 0)) + ((CRabs R (c 1%nat) * CR_of_Q R (pfb4 2 1)) + ((CRabs R (c 2%nat) * CR_of_Q R (pfb4 2 2)) + (CRabs R (c 3%nat) * CR_of_Q R (pfb4 2 3))))) + ((CRabs R (c 0%nat) * CR_of_Q R (pfb4 3 0)) + ((CRabs R (c 1%nat) * CR_of_Q R (pfb4 3 1)) + ((CRabs R (c 2%nat) * CR_of_Q R (pfb4 3 2)) + (CRabs R (c 3%nat) * CR_of_Q R (pfb4 3 3))))))
         ((CRabs R (c 0%nat) * (CR_of_Q R (pfb4 0 2) + CR_of_Q R (pfb4 0 3))) + ((CRabs R (c 1%nat) * (CR_of_Q R (pfb4 1 2) + CR_of_Q R (pfb4 1 3))) + ((CRabs R (c 2%nat) * (CR_of_Q R (pfb4 2 2) + CR_of_Q R (pfb4 2 3))) + (CRabs R (c 3%nat) * (CR_of_Q R (pfb4 3 2) + CR_of_Q R (pfb4 3 3)))))).
Proof. unfold pfb4. ring. Qed.

(* 两半按系数归位 *)
Lemma c4u_pairs_merge (c : nat -> CRcarrier R) :
  CReq R (((CRabs R (c 0%nat) * (CR_of_Q R (pfb4 0 0) + CR_of_Q R (pfb4 0 1))) + ((CRabs R (c 1%nat) * (CR_of_Q R (pfb4 1 0) + CR_of_Q R (pfb4 1 1))) + ((CRabs R (c 2%nat) * (CR_of_Q R (pfb4 2 0) + CR_of_Q R (pfb4 2 1))) + (CRabs R (c 3%nat) * (CR_of_Q R (pfb4 3 0) + CR_of_Q R (pfb4 3 1)))))) + ((CRabs R (c 0%nat) * (CR_of_Q R (pfb4 0 2) + CR_of_Q R (pfb4 0 3))) + ((CRabs R (c 1%nat) * (CR_of_Q R (pfb4 1 2) + CR_of_Q R (pfb4 1 3))) + ((CRabs R (c 2%nat) * (CR_of_Q R (pfb4 2 2) + CR_of_Q R (pfb4 2 3))) + (CRabs R (c 3%nat) * (CR_of_Q R (pfb4 3 2) + CR_of_Q R (pfb4 3 3)))))))
         (((CRabs R (c 0%nat) * (CR_of_Q R (pfb4 0 0) + CR_of_Q R (pfb4 0 1))) + (CRabs R (c 0%nat) * (CR_of_Q R (pfb4 0 2) + CR_of_Q R (pfb4 0 3)))) + (((CRabs R (c 1%nat) * (CR_of_Q R (pfb4 1 0) + CR_of_Q R (pfb4 1 1))) + (CRabs R (c 1%nat) * (CR_of_Q R (pfb4 1 2) + CR_of_Q R (pfb4 1 3)))) + (((CRabs R (c 2%nat) * (CR_of_Q R (pfb4 2 0) + CR_of_Q R (pfb4 2 1))) + (CRabs R (c 2%nat) * (CR_of_Q R (pfb4 2 2) + CR_of_Q R (pfb4 2 3)))) + ((CRabs R (c 3%nat) * (CR_of_Q R (pfb4 3 0) + CR_of_Q R (pfb4 3 1))) + (CRabs R (c 3%nat) * (CR_of_Q R (pfb4 3 2) + CR_of_Q R (pfb4 3 3))))))).
Proof. unfold pfb4. ring. Qed.

(* 每列配对坍缩：pair 和 ≤ ρ·|c_j| *)
Lemma c4u_pair_col_0 (c : nat -> CRcarrier R) :
  CRle R ((CRabs R (c 0%nat) * (CR_of_Q R (pfb4 0 0) + CR_of_Q R (pfb4 0 1))) + (CRabs R (c 0%nat) * (CR_of_Q R (pfb4 0 2) + CR_of_Q R (pfb4 0 3)))) (CR_of_Q R rho4 * CRabs R (c 0%nat)).
Proof.
  assert (Hq : CReq R (CR_of_Q R (col4 0%nat))
             ((CR_of_Q R (pfb4 0 0) + CR_of_Q R (pfb4 0 1)) + (CR_of_Q R (pfb4 0 2) + CR_of_Q R (pfb4 0 3)))).
  { unfold col4. repeat setoid_rewrite (CR_of_Q_plus R). unfold pfb4. ring. }
  apply (CRle_trans (R:=R) _ (CR_of_Q R (col4 0%nat) * CRabs R (c 0%nat))).
  - apply (CRle_trans (R:=R) _
             (((CR_of_Q R (pfb4 0 0) + CR_of_Q R (pfb4 0 1)) + (CR_of_Q R (pfb4 0 2) + CR_of_Q R (pfb4 0 3))) * CRabs R (c 0%nat))).
    + assert (Hr : CReq R ((CRabs R (c 0%nat) * (CR_of_Q R (pfb4 0 0) + CR_of_Q R (pfb4 0 1))) + (CRabs R (c 0%nat) * (CR_of_Q R (pfb4 0 2) + CR_of_Q R (pfb4 0 3))))
             (((CR_of_Q R (pfb4 0 0) + CR_of_Q R (pfb4 0 1)) + (CR_of_Q R (pfb4 0 2) + CR_of_Q R (pfb4 0 3))) * CRabs R (c 0%nat)))
        by ring.
      exact (proj2 Hr).
    + apply CRmult_le_compat_r.
      * apply CRabs_pos.
      * exact (proj1 Hq).
  - apply CRmult_le_compat_r.
    + apply CRabs_pos.
    + apply CR_of_Q_le. apply col4_le_rho4. lia.
Qed.

Lemma c4u_pair_col_1 (c : nat -> CRcarrier R) :
  CRle R ((CRabs R (c 1%nat) * (CR_of_Q R (pfb4 1 0) + CR_of_Q R (pfb4 1 1))) + (CRabs R (c 1%nat) * (CR_of_Q R (pfb4 1 2) + CR_of_Q R (pfb4 1 3)))) (CR_of_Q R rho4 * CRabs R (c 1%nat)).
Proof.
  assert (Hq : CReq R (CR_of_Q R (col4 1%nat))
             ((CR_of_Q R (pfb4 1 0) + CR_of_Q R (pfb4 1 1)) + (CR_of_Q R (pfb4 1 2) + CR_of_Q R (pfb4 1 3)))).
  { unfold col4. repeat setoid_rewrite (CR_of_Q_plus R). unfold pfb4. ring. }
  apply (CRle_trans (R:=R) _ (CR_of_Q R (col4 1%nat) * CRabs R (c 1%nat))).
  - apply (CRle_trans (R:=R) _
             (((CR_of_Q R (pfb4 1 0) + CR_of_Q R (pfb4 1 1)) + (CR_of_Q R (pfb4 1 2) + CR_of_Q R (pfb4 1 3))) * CRabs R (c 1%nat))).
    + assert (Hr : CReq R ((CRabs R (c 1%nat) * (CR_of_Q R (pfb4 1 0) + CR_of_Q R (pfb4 1 1))) + (CRabs R (c 1%nat) * (CR_of_Q R (pfb4 1 2) + CR_of_Q R (pfb4 1 3))))
             (((CR_of_Q R (pfb4 1 0) + CR_of_Q R (pfb4 1 1)) + (CR_of_Q R (pfb4 1 2) + CR_of_Q R (pfb4 1 3))) * CRabs R (c 1%nat)))
        by ring.
      exact (proj2 Hr).
    + apply CRmult_le_compat_r.
      * apply CRabs_pos.
      * exact (proj1 Hq).
  - apply CRmult_le_compat_r.
    + apply CRabs_pos.
    + apply CR_of_Q_le. apply col4_le_rho4. lia.
Qed.

Lemma c4u_pair_col_2 (c : nat -> CRcarrier R) :
  CRle R ((CRabs R (c 2%nat) * (CR_of_Q R (pfb4 2 0) + CR_of_Q R (pfb4 2 1))) + (CRabs R (c 2%nat) * (CR_of_Q R (pfb4 2 2) + CR_of_Q R (pfb4 2 3)))) (CR_of_Q R rho4 * CRabs R (c 2%nat)).
Proof.
  assert (Hq : CReq R (CR_of_Q R (col4 2%nat))
             ((CR_of_Q R (pfb4 2 0) + CR_of_Q R (pfb4 2 1)) + (CR_of_Q R (pfb4 2 2) + CR_of_Q R (pfb4 2 3)))).
  { unfold col4. repeat setoid_rewrite (CR_of_Q_plus R). unfold pfb4. ring. }
  apply (CRle_trans (R:=R) _ (CR_of_Q R (col4 2%nat) * CRabs R (c 2%nat))).
  - apply (CRle_trans (R:=R) _
             (((CR_of_Q R (pfb4 2 0) + CR_of_Q R (pfb4 2 1)) + (CR_of_Q R (pfb4 2 2) + CR_of_Q R (pfb4 2 3))) * CRabs R (c 2%nat))).
    + assert (Hr : CReq R ((CRabs R (c 2%nat) * (CR_of_Q R (pfb4 2 0) + CR_of_Q R (pfb4 2 1))) + (CRabs R (c 2%nat) * (CR_of_Q R (pfb4 2 2) + CR_of_Q R (pfb4 2 3))))
             (((CR_of_Q R (pfb4 2 0) + CR_of_Q R (pfb4 2 1)) + (CR_of_Q R (pfb4 2 2) + CR_of_Q R (pfb4 2 3))) * CRabs R (c 2%nat)))
        by ring.
      exact (proj2 Hr).
    + apply CRmult_le_compat_r.
      * apply CRabs_pos.
      * exact (proj1 Hq).
  - apply CRmult_le_compat_r.
    + apply CRabs_pos.
    + apply CR_of_Q_le. apply col4_le_rho4. lia.
Qed.

Lemma c4u_pair_col_3 (c : nat -> CRcarrier R) :
  CRle R ((CRabs R (c 3%nat) * (CR_of_Q R (pfb4 3 0) + CR_of_Q R (pfb4 3 1))) + (CRabs R (c 3%nat) * (CR_of_Q R (pfb4 3 2) + CR_of_Q R (pfb4 3 3)))) (CR_of_Q R rho4 * CRabs R (c 3%nat)).
Proof.
  assert (Hq : CReq R (CR_of_Q R (col4 3%nat))
             ((CR_of_Q R (pfb4 3 0) + CR_of_Q R (pfb4 3 1)) + (CR_of_Q R (pfb4 3 2) + CR_of_Q R (pfb4 3 3)))).
  { unfold col4. repeat setoid_rewrite (CR_of_Q_plus R). unfold pfb4. ring. }
  apply (CRle_trans (R:=R) _ (CR_of_Q R (col4 3%nat) * CRabs R (c 3%nat))).
  - apply (CRle_trans (R:=R) _
             (((CR_of_Q R (pfb4 3 0) + CR_of_Q R (pfb4 3 1)) + (CR_of_Q R (pfb4 3 2) + CR_of_Q R (pfb4 3 3))) * CRabs R (c 3%nat))).
    + assert (Hr : CReq R ((CRabs R (c 3%nat) * (CR_of_Q R (pfb4 3 0) + CR_of_Q R (pfb4 3 1))) + (CRabs R (c 3%nat) * (CR_of_Q R (pfb4 3 2) + CR_of_Q R (pfb4 3 3))))
             (((CR_of_Q R (pfb4 3 0) + CR_of_Q R (pfb4 3 1)) + (CR_of_Q R (pfb4 3 2) + CR_of_Q R (pfb4 3 3))) * CRabs R (c 3%nat)))
        by ring.
      exact (proj2 Hr).
    + apply CRmult_le_compat_r.
      * apply CRabs_pos.
      * exact (proj1 Hq).
  - apply CRmult_le_compat_r.
    + apply CRabs_pos.
    + apply CR_of_Q_le. apply col4_le_rho4. lia.
Qed.

(* ---------- ★ 核心定理二：列收缩坍缩 S ≤ ρ·S ⟹ S ≤ 0 ---------- *)

Lemma c4u_sum_abs_zero (c : nat -> CRcarrier R)
  (Hcombo : CRcombo 3 c u = CRzero) :
  CRle R (CRsum (fun j => CRabs R (c j)) 3) (CR_of_Q R (Qmake 0 1)).
Proof.
  assert (H03 : le 0 3) by lia. assert (H13 : le 1 3) by lia.
  assert (H23 : le 2 3) by lia. assert (H33 : le 3 3) by lia.
  pose proof (row_abs_le c Hcombo 0 H03) as Hr0.
  pose proof (row_abs_le c Hcombo 1 H13) as Hr1.
  pose proof (row_abs_le c Hcombo 2 H23) as Hr2.
  pose proof (row_abs_le c Hcombo 3 H33) as Hr3.
  (* 行求和：S ≤ (r0+r1)+(r2+r3)（左生长链，直接对齐合并形态） *)
  assert (Hsum : CRle R (CRsum (fun j => CRabs R (c j)) 3)
    ((((CRabs R (c 0%nat) * CR_of_Q R (pfb4 0 0)) + ((CRabs R (c 1%nat) * CR_of_Q R (pfb4 1 0)) + ((CRabs R (c 2%nat) * CR_of_Q R (pfb4 2 0)) + (CRabs R (c 3%nat) * CR_of_Q R (pfb4 3 0))))) + ((CRabs R (c 0%nat) * CR_of_Q R (pfb4 0 1)) + ((CRabs R (c 1%nat) * CR_of_Q R (pfb4 1 1)) + ((CRabs R (c 2%nat) * CR_of_Q R (pfb4 2 1)) + (CRabs R (c 3%nat) * CR_of_Q R (pfb4 3 1)))))) + (((CRabs R (c 0%nat) * CR_of_Q R (pfb4 0 2)) + ((CRabs R (c 1%nat) * CR_of_Q R (pfb4 1 2)) + ((CRabs R (c 2%nat) * CR_of_Q R (pfb4 2 2)) + (CRabs R (c 3%nat) * CR_of_Q R (pfb4 3 2))))) + ((CRabs R (c 0%nat) * CR_of_Q R (pfb4 0 3)) + ((CRabs R (c 1%nat) * CR_of_Q R (pfb4 1 3)) + ((CRabs R (c 2%nat) * CR_of_Q R (pfb4 2 3)) + (CRabs R (c 3%nat) * CR_of_Q R (pfb4 3 3)))))))).
  { change (CRsum (fun j => CRabs R (c j)) 3) with
      (((CRabs R (c 0%nat) + CRabs R (c 1%nat)) + CRabs R (c 2%nat)) + CRabs R (c 3%nat)).
    apply (CRle_trans (R:=R)
             (((CRabs R (c 0%nat) + CRabs R (c 1%nat)) + CRabs R (c 2%nat)) + CRabs R (c 3%nat))
             ((CRabs R (c 0%nat) + CRabs R (c 1%nat)) + (CRabs R (c 2%nat) + CRabs R (c 3%nat)))
             ((((CRabs R (c 0%nat) * CR_of_Q R (pfb4 0 0)) + ((CRabs R (c 1%nat) * CR_of_Q R (pfb4 1 0)) + ((CRabs R (c 2%nat) * CR_of_Q R (pfb4 2 0)) + (CRabs R (c 3%nat) * CR_of_Q R (pfb4 3 0))))) + ((CRabs R (c 0%nat) * CR_of_Q R (pfb4 0 1)) + ((CRabs R (c 1%nat) * CR_of_Q R (pfb4 1 1)) + ((CRabs R (c 2%nat) * CR_of_Q R (pfb4 2 1)) + (CRabs R (c 3%nat) * CR_of_Q R (pfb4 3 1)))))) + (((CRabs R (c 0%nat) * CR_of_Q R (pfb4 0 2)) + ((CRabs R (c 1%nat) * CR_of_Q R (pfb4 1 2)) + ((CRabs R (c 2%nat) * CR_of_Q R (pfb4 2 2)) + (CRabs R (c 3%nat) * CR_of_Q R (pfb4 3 2))))) + ((CRabs R (c 0%nat) * CR_of_Q R (pfb4 0 3)) + ((CRabs R (c 1%nat) * CR_of_Q R (pfb4 1 3)) + ((CRabs R (c 2%nat) * CR_of_Q R (pfb4 2 3)) + (CRabs R (c 3%nat) * CR_of_Q R (pfb4 3 3)))))))).
    - assert (Hsa : CReq R
        (((CRabs R (c 0%nat) + CRabs R (c 1%nat)) + CRabs R (c 2%nat)) + CRabs R (c 3%nat))
        ((CRabs R (c 0%nat) + CRabs R (c 1%nat)) + (CRabs R (c 2%nat) + CRabs R (c 3%nat))))
        by ring.
      exact (proj2 Hsa).
    - apply CRplus_le_compat.
      + apply CRplus_le_compat; [exact Hr0 | exact Hr1].
      + apply CRplus_le_compat; [exact Hr2 | exact Hr3].
  }
  (* 列收缩主链（全程 ≤8 单项式小步——ring 插件对 16 单项式目标失效）：
     S ≤ (r0+r1)+(r2+r3) ≤ M01 + M23 ≡ P ≤ ρ·逐列 ≤ ρ·S ⟹（ρ<1）S ≤ 0 *)
  assert (Hrho : CReq R (CR_of_Q R rho4 * CRabs R (c 0%nat) + (CR_of_Q R rho4 * CRabs R (c 1%nat) + (CR_of_Q R rho4 * CRabs R (c 2%nat) + CR_of_Q R rho4 * CRabs R (c 3%nat)))) (CR_of_Q R rho4 * CRsum (fun j => CRabs R (c j)) 3))
    by (cbn [CRsum]; ring).
  apply (CRle_scaled_le_zero (R:=R) (CRsum (fun j => CRabs R (c j)) 3) (CR_of_Q R rho4)).
  - apply (CRle_trans (R:=R) (CRsum (fun j => CRabs R (c j)) 3) (((CRabs R (c 0%nat) * (CR_of_Q R (pfb4 0 0) + CR_of_Q R (pfb4 0 1))) + ((CRabs R (c 1%nat) * (CR_of_Q R (pfb4 1 0) + CR_of_Q R (pfb4 1 1))) + ((CRabs R (c 2%nat) * (CR_of_Q R (pfb4 2 0) + CR_of_Q R (pfb4 2 1))) + (CRabs R (c 3%nat) * (CR_of_Q R (pfb4 3 0) + CR_of_Q R (pfb4 3 1)))))) + ((CRabs R (c 0%nat) * (CR_of_Q R (pfb4 0 2) + CR_of_Q R (pfb4 0 3))) + ((CRabs R (c 1%nat) * (CR_of_Q R (pfb4 1 2) + CR_of_Q R (pfb4 1 3))) + ((CRabs R (c 2%nat) * (CR_of_Q R (pfb4 2 2) + CR_of_Q R (pfb4 2 3))) + (CRabs R (c 3%nat) * (CR_of_Q R (pfb4 3 2) + CR_of_Q R (pfb4 3 3))))))) (CR_of_Q R rho4 * CRsum (fun j => CRabs R (c j)) 3)).
    + apply (CRle_trans (R:=R) (CRsum (fun j => CRabs R (c j)) 3)
             ((((CRabs R (c 0%nat) * CR_of_Q R (pfb4 0 0)) + ((CRabs R (c 1%nat) * CR_of_Q R (pfb4 1 0)) + ((CRabs R (c 2%nat) * CR_of_Q R (pfb4 2 0)) + (CRabs R (c 3%nat) * CR_of_Q R (pfb4 3 0))))) + ((CRabs R (c 0%nat) * CR_of_Q R (pfb4 0 1)) + ((CRabs R (c 1%nat) * CR_of_Q R (pfb4 1 1)) + ((CRabs R (c 2%nat) * CR_of_Q R (pfb4 2 1)) + (CRabs R (c 3%nat) * CR_of_Q R (pfb4 3 1)))))) + (((CRabs R (c 0%nat) * CR_of_Q R (pfb4 0 2)) + ((CRabs R (c 1%nat) * CR_of_Q R (pfb4 1 2)) + ((CRabs R (c 2%nat) * CR_of_Q R (pfb4 2 2)) + (CRabs R (c 3%nat) * CR_of_Q R (pfb4 3 2))))) + ((CRabs R (c 0%nat) * CR_of_Q R (pfb4 0 3)) + ((CRabs R (c 1%nat) * CR_of_Q R (pfb4 1 3)) + ((CRabs R (c 2%nat) * CR_of_Q R (pfb4 2 3)) + (CRabs R (c 3%nat) * CR_of_Q R (pfb4 3 3)))))))
             (((CRabs R (c 0%nat) * (CR_of_Q R (pfb4 0 0) + CR_of_Q R (pfb4 0 1))) + ((CRabs R (c 1%nat) * (CR_of_Q R (pfb4 1 0) + CR_of_Q R (pfb4 1 1))) + ((CRabs R (c 2%nat) * (CR_of_Q R (pfb4 2 0) + CR_of_Q R (pfb4 2 1))) + (CRabs R (c 3%nat) * (CR_of_Q R (pfb4 3 0) + CR_of_Q R (pfb4 3 1)))))) + ((CRabs R (c 0%nat) * (CR_of_Q R (pfb4 0 2) + CR_of_Q R (pfb4 0 3))) + ((CRabs R (c 1%nat) * (CR_of_Q R (pfb4 1 2) + CR_of_Q R (pfb4 1 3))) + ((CRabs R (c 2%nat) * (CR_of_Q R (pfb4 2 2) + CR_of_Q R (pfb4 2 3))) + (CRabs R (c 3%nat) * (CR_of_Q R (pfb4 3 2) + CR_of_Q R (pfb4 3 3)))))))).
      * exact Hsum.
      * apply CRplus_le_compat;
             [ exact (proj2 (c4u_rows_merge01 c))
             | exact (proj2 (c4u_rows_merge23 c)) ].
    + apply (CRle_trans (R:=R) (((CRabs R (c 0%nat) * (CR_of_Q R (pfb4 0 0) + CR_of_Q R (pfb4 0 1))) + ((CRabs R (c 1%nat) * (CR_of_Q R (pfb4 1 0) + CR_of_Q R (pfb4 1 1))) + ((CRabs R (c 2%nat) * (CR_of_Q R (pfb4 2 0) + CR_of_Q R (pfb4 2 1))) + (CRabs R (c 3%nat) * (CR_of_Q R (pfb4 3 0) + CR_of_Q R (pfb4 3 1)))))) + ((CRabs R (c 0%nat) * (CR_of_Q R (pfb4 0 2) + CR_of_Q R (pfb4 0 3))) + ((CRabs R (c 1%nat) * (CR_of_Q R (pfb4 1 2) + CR_of_Q R (pfb4 1 3))) + ((CRabs R (c 2%nat) * (CR_of_Q R (pfb4 2 2) + CR_of_Q R (pfb4 2 3))) + (CRabs R (c 3%nat) * (CR_of_Q R (pfb4 3 2) + CR_of_Q R (pfb4 3 3))))))) ((CRabs R (c 0%nat) * (CR_of_Q R (pfb4 0 0) + CR_of_Q R (pfb4 0 1)) + CRabs R (c 0%nat) * (CR_of_Q R (pfb4 0 2) + CR_of_Q R (pfb4 0 3))) + ((CRabs R (c 1%nat) * (CR_of_Q R (pfb4 1 0) + CR_of_Q R (pfb4 1 1)) + CRabs R (c 1%nat) * (CR_of_Q R (pfb4 1 2) + CR_of_Q R (pfb4 1 3))) + ((CRabs R (c 2%nat) * (CR_of_Q R (pfb4 2 0) + CR_of_Q R (pfb4 2 1)) + CRabs R (c 2%nat) * (CR_of_Q R (pfb4 2 2) + CR_of_Q R (pfb4 2 3))) + (CRabs R (c 3%nat) * (CR_of_Q R (pfb4 3 0) + CR_of_Q R (pfb4 3 1)) + CRabs R (c 3%nat) * (CR_of_Q R (pfb4 3 2) + CR_of_Q R (pfb4 3 3)))))) (CR_of_Q R rho4 * CRsum (fun j => CRabs R (c j)) 3)).
      * exact (proj2 (c4u_pairs_merge c)).
      * apply (CRle_trans (R:=R) ((CRabs R (c 0%nat) * (CR_of_Q R (pfb4 0 0) + CR_of_Q R (pfb4 0 1)) + CRabs R (c 0%nat) * (CR_of_Q R (pfb4 0 2) + CR_of_Q R (pfb4 0 3))) + ((CRabs R (c 1%nat) * (CR_of_Q R (pfb4 1 0) + CR_of_Q R (pfb4 1 1)) + CRabs R (c 1%nat) * (CR_of_Q R (pfb4 1 2) + CR_of_Q R (pfb4 1 3))) + ((CRabs R (c 2%nat) * (CR_of_Q R (pfb4 2 0) + CR_of_Q R (pfb4 2 1)) + CRabs R (c 2%nat) * (CR_of_Q R (pfb4 2 2) + CR_of_Q R (pfb4 2 3))) + (CRabs R (c 3%nat) * (CR_of_Q R (pfb4 3 0) + CR_of_Q R (pfb4 3 1)) + CRabs R (c 3%nat) * (CR_of_Q R (pfb4 3 2) + CR_of_Q R (pfb4 3 3)))))) (CR_of_Q R rho4 * CRabs R (c 0%nat) + (CR_of_Q R rho4 * CRabs R (c 1%nat) + (CR_of_Q R rho4 * CRabs R (c 2%nat) + CR_of_Q R rho4 * CRabs R (c 3%nat)))) (CR_of_Q R rho4 * CRsum (fun j => CRabs R (c j)) 3)).
        -- apply CRplus_le_compat.
           ++ exact (c4u_pair_col_0 c).
           ++ apply CRplus_le_compat.
              ** exact (c4u_pair_col_1 c).
              ** apply CRplus_le_compat.
                 --- exact (c4u_pair_col_2 c).
                 --- exact (c4u_pair_col_3 c).
        -- exact (proj2 Hrho).
  - exact (CR_of_Q_lt R rho4 (Qmake 1 1) rho4_lt_one).
Qed.

(* ---------- ★★ 最终定理：四原子合成单射 ---------- *)

Theorem c4u_synthesis_injective (c : nat -> CRcarrier R)
  (Hcombo : CRcombo 3 c u = CRzero) :
  forall j, le j 3 -> CReq R (c j) (CR_of_Q R (Qmake 0 1)).
Proof.
  intros j Hj.
  pose proof (c4u_sum_abs_zero c Hcombo) as Hs0.
  assert (HS0 : CReq R (CRsum (fun k => CRabs R (c k)) 3)
                  (CR_of_Q R (Qmake 0 1))).
  { split.
    - apply (cond_pos_sum (fun k => CRabs R (c k)) 3).
      intro k. apply CRabs_pos.
    - exact Hs0. }
  (* |c j| ≤ S ≤ 0 *)
  assert (Haj : CRle R (CRabs R (c j)) (CR_of_Q R (Qmake 0 1))).
  { apply (CRle_trans (R:=R) (CRabs R (c j))
             (CRsum (fun k => CRabs R (c k)) 3)
             (CR_of_Q R (Qmake 0 1))).
    - apply (CRsum_nonneg_term_le 3 (fun k => CRabs R (c k))).
      + intro k. apply CRabs_pos.
      + exact Hj.
    - exact (proj2 HS0). }
  assert (Heqj : CReq R (CRabs R (c j)) (CR_of_Q R (Qmake 0 1))).
  { split; [apply CRabs_pos | exact Haj]. }
  split.
  - (* 0 ≤ c j：−|c j| ≤ c j 且 |c j| ≡ 0 *)
    pose proof (CRopp_abs_le_self (R:=R) (c j)) as Hneg.
    setoid_rewrite Heqj in Hneg.
    setoid_rewrite CRopp_0 in Hneg.
    exact Hneg.
  - (* c j ≤ 0：c j ≤ |c j| ≡ 0 *)
    pose proof (CRle_abs_self (R:=R) (c j)) as Hpos.
    setoid_rewrite Heqj in Hpos.
    exact Hpos.
Qed.

(* ---------- 推论：2-sparse 唯一恢复 ---------- *)

Corollary c4u_2sparse_unique (ca cb : CRcarrier R)
  (Hcombo : CRcombo 3
              (fun j => match j with
                        | 0%nat => ca
                        | 1%nat => cb
                        | _ => CR_of_Q R (Qmake 0 1)
                        end) u = CRzero) :
  CReq R ca (CR_of_Q R (Qmake 0 1))
  /\ CReq R cb (CR_of_Q R (Qmake 0 1)).
Proof.
  split.
  - apply (c4u_synthesis_injective _ Hcombo 0%nat). lia.
  - apply (c4u_synthesis_injective _ Hcombo 1%nat). lia.
Qed.

End C4Unique2SparseCR.

(* ============ 审计 ============ *)
Print Assumptions combo3_ip_expand.
Print Assumptions row_ip_zero.
Print Assumptions row_abs_le.
Print Assumptions c4u_sum_abs_zero.
Print Assumptions c4u_synthesis_injective.
Print Assumptions c4u_2sparse_unique.

(* ============ 提取（证书表 + 可执行检查器） ============ *)
From Stdlib Require Import Extraction.
From Stdlib Require Import ConstructiveRcomplete.

(* ρ 窗口：Qnum/Qden 具象化（Z * positive） *)
Definition c4u_rho4_window : Z * positive :=
  (Qnum rho4, Qden rho4).

(* 逐对上界表（nat -> nat -> Q 可执行） *)
Definition c4u_pfb4_table : nat -> nat -> Q := pfb4.

(* 列和窗口 *)
Definition c4u_col_window : nat -> Z * positive :=
  fun j => (Qnum (col4 j), Qden (col4 j)).

(* 可执行检查器：列 ≤ ρ 与 ρ < 1 的 bool 判定 *)
Definition c4u_col_ok : nat -> bool := fun j => Qle_bool (col4 j) rho4.
Definition c4u_rho4_ok : bool := negb (Qle_bool (Qmake 1 1) rho4).  (* ρ < 1 *)

Extraction "c4_unique2sparse_cr.ml"
  c4u_rho4_window c4u_pfb4_table c4u_col_window
  c4u_col_ok c4u_rho4_ok.
