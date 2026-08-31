(* ============================================================
   CS-23 构造性四原子 Gram 特征值口径唯一性：probe_c4_gram_unique_cr.v
   （z 区构造性轨道，2026-08-31——"四原子扩展不在 Artifact"负面结论
   的正面翻转：四原子稀疏唯一性经 Gram 特征值（二次型下界）口径
   数学上可行且可构造，本文件给出完整形式化。）

   数学内容（Gram 谱下界 ⟹ 合成映射单射，零经典排中）：
     CS-15 判定"全族唯一性窗口关闭"用的是公共相干 μ₄ 均匀化：
       ‖Σc_j u_j‖² ≥ (1 − 4μ₄)Σc_j²，而 4μ₄ = 45156/33920 > 1。
     本文件换 Gram 特征值（Gershgorin 行和 / 二次型）口径：
       Gram 矩阵 G_ij = ⟨u_i,u_j⟩，对角 1，|G_ij| ≤ pfb4 i j
       （六对有理逐对上界表，与经典 D 层同数值）。
       ★ 核心定理一（二次型展开=能量恒等式）：
          ‖Σc_j u_j‖² ≡ Σ_j c_j·Σ_i c_i·G_ij（Gram 双线性）
       ★ 核心定理二（Gershgorin 型谱下界，AM-GM 逐对收口）：
          |Σ_{i≠j} c_i c_j G_ij| ≤ ρ₄·Σc_j²，
          ρ₄ = 最大行和 = col4 2 = 159/1200+689/2080+11289/33920
             ≈ 0.797（逐对表信息量 > 公共 μ₄：0.797 < 4μ₄ ≈ 1.331）
       ⟹ Σc² ≤ ‖combo‖² + ρ₄·Σc²，且 ρ₄ < 1（Q 层精确判定）
       ⟹（CRle_scaled_le_zero 收缩）combo = 0 ⟹ Σc² ≡ 0
       ⟹（CRsum_sq_zero_terms）逐项 c_j ≡ 0。
     ★ 谱下界常数（可提取）：λ* = 1 − ρ₄ = 651/3200 > 0
       （特征值口径构造性"最小特征值下界"—— witness 以数据给出）：
       c4g_lam_lower : λ*·Σc² ≤ ‖combo‖²，sigT 打包
       c4g_lam_sigT : {λ : CR & 0 < λ × ∀c, λ·Σc² ≤ ‖combo c‖²}。
     对比：均匀 μ₄ 口径唯一性需 4μ₄ < 1（关闭，53/33920 是 3μ₄
       窗口的能量稳定常数而非唯一性常数）；Gram 行和口径只需
       ρ₄ < 1（开启）——负面结论翻转为正面。

   纪律（M2 红线，承 CS-15/CS-21）：纯构造性——零经典逻辑、
   零经典实数公理（不 Require Stdlib.Reals）、零 Admitted、
   零自定义 Axiom；Set 层 CRcarrier/CRComplex；Prop 层仅
   CRle/CRlt/CReq 界与相等（无信息内容，同 taugrid C-TA3 口径）；
   接口化 {R : ConstructiveReals}；Q 层字面量判定 lia 收口；
   sigT 见证（λ* 特征值下界以 Set 层数据给出）；
   可提取（ρ₄/λ* 窗口 + pfb4 表 + bool 证书链）。
   非平凡核心定理 = c4g_E_abs_bound（Gershgorin 二次型谱下界，
   AM-GM 逐对）+ c4g_lam_lower（λ*·‖c‖² ≤ ‖combo‖²）；
   最终定理 = c4g_synthesis_injective（含 c4g_2sparse_unique 推论）。
   依赖：ca_rip_cr（CRrip 系工具：CRle_scaled_le_zero /
         CRsum_sq_zero_terms / CRabs_amgm / CRcombo_ip_rec，全 Closed）。
   ============================================================ *)
Require Import ConstructiveReals.
From Stdlib Require Import ConstructiveRealsMorphisms.
From Stdlib Require Import ConstructiveAbs.
From Stdlib Require Import ConstructiveSum.
Require Import Stdlib.QArith.QArith.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.micromega.Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat seq eqtype div.
From Stdlib Require Import Ring.
Require Import ca_rip_cr.

Unset Implicit Arguments.

Local Open Scope ConstructiveReals.
(* 不打开 Q_scope——Q 值全部通过 Qmake 辅助构造（同 ca_rip_cr） *)

(* E138①：Notation 注册（8 项，恢复 Stdlib nat 记号——防 mathcomp 污染，
   合并版双环境兼容硬规则 9） *)
Notation "a + b" := (Nat.add a b) (at level 50, left associativity) : nat_scope.
Notation "a - b" := (Nat.sub a b) (at level 50, left associativity) : nat_scope.
Notation "a * b" := (Nat.mul a b) (at level 40, left associativity) : nat_scope.
Notation "a <= b" := (Nat.le a b) (at level 70, no associativity) : nat_scope.
Notation "a < b" := (Nat.lt a b) (at level 70, no associativity) : nat_scope.
Notation "a >= b" := (Nat.le b a) (at level 70, no associativity) : nat_scope.
Notation "a > b" := (Nat.lt b a) (at level 70, no associativity) : nat_scope.

(* ============ Q 层：逐对有理上界表（与经典 D 层同数值） ============ *)

(* pfb4 i j：|⟨u_i,u_j⟩| 的有理上界（六对，对称填充；对角支置 0）。
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

(* 列和 C_j = Σ_i pfb4 i j（对角为 0，表对称故=行和）与最大行 ρ₄ = C_2 *)
Definition col4 (j : nat) : Q := pfb4 0 j + pfb4 1 j + pfb4 2 j + pfb4 3 j.
Definition rho4 : Q := col4 2.
(* 谱下界 λ* = 1 − ρ₄ = 651/3200（★ 可提取常数） *)
Definition lam4 : Q := Qminus (Qmake 1 1) rho4.

(* 表对称（值域内成立——外层 `_` default 支给出第 3 行内容，
   与行内 `_` 的 Qmake 0 1 在越界下标上不对称，故必须带 le 前提；
   0..3 的 16 例为具体构造子，reflexivity 直算） *)
Lemma pfb4_sym : forall i j, le i 3 -> le j 3 -> pfb4 i j = pfb4 j i.
Proof.
  intros i j Hi Hj.
  destruct i as [|[|[|[|i4]]]]; destruct j as [|[|[|[|j4]]]];
    try reflexivity; exfalso; lia.
Qed.

(* ρ₄ < 1：0.797... < 1（Q 层精确判定）
   unfold 顺序：定义先行，谓词在后（后展开的节点才能被覆盖） *)
Lemma rho4_lt_one : Qlt rho4 (Qmake 1 1).
Proof.
  unfold rho4, col4, pfb4, Qlt, Qplus. cbn [Qnum Qden]. lia.
Qed.

(* 各行 ≤ ρ₄（ρ₄ 即最大行） *)
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

(* λ* > 0 与 λ* = 651/3200（谱下界常数的精确值） *)
Lemma lam4_pos : Qlt (Qmake 0 1) lam4.
Proof.
  unfold lam4, rho4, col4, pfb4, Qlt, Qminus, Qplus, Qopp.
  cbn [Qnum Qden]. lia.
Qed.

Lemma lam4_val : Qeq lam4 (Qmake 651 3200).
Proof.
  unfold lam4, rho4, col4, pfb4, Qeq, Qminus, Qplus, Qopp, Qmult.
  cbn [Qnum Qden]. lia.
Qed.

(* 表非负（AM-GM 乘子合法性）——同对称性：值域内才可归约判定。
   注意：cbn 必须带 pfb4（否则 Qnum (pfb4 i j) 的 delta 不展开，
   iota 无法点火，Qmake 挡在常量应用之下——E-本卡） *)
Lemma pfb4_nonneg : forall i j, le i 3 -> le j 3 -> Qle (Qmake 0 1) (pfb4 i j).
Proof.
  intros i j Hi Hj.
  destruct i as [|[|[|[|i4]]]]; destruct j as [|[|[|[|j4]]]];
    unfold Qle, Qplus; cbn [pfb4 Qnum Qden]; lia.
Qed.

(* PFLAT 系数三和 ≤ ρ₄（c_k² 系数组：{01,02,03},{01,12,13},{02,12,23},{03,13,23}） *)
Lemma qsum0_le_rho4 : Qle (pfb4 0 1 + (pfb4 0 2 + pfb4 0 3)) rho4.
Proof. unfold rho4, col4, pfb4, Qle, Qplus. cbn [Qnum Qden]. lia. Qed.
Lemma qsum1_le_rho4 : Qle (pfb4 0 1 + (pfb4 1 2 + pfb4 1 3)) rho4.
Proof. unfold rho4, col4, pfb4, Qle, Qplus. cbn [Qnum Qden]. lia. Qed.
Lemma qsum2_le_rho4 : Qle (pfb4 0 2 + (pfb4 1 2 + pfb4 2 3)) rho4.
Proof. unfold rho4, col4, pfb4, Qle, Qplus. cbn [Qnum Qden]. lia. Qed.
Lemma qsum3_le_rho4 : Qle (pfb4 0 3 + (pfb4 1 3 + pfb4 2 3)) rho4.
Proof. unfold rho4, col4, pfb4, Qle, Qplus. cbn [Qnum Qden]. lia. Qed.

(* ============ CR 层：四原子 Gram 特征值口径注入性 ============ *)

Section C4GramUniqueCR.

Context {R : ConstructiveReals}.
Add Ring CR_ring : (CRisRing R).

Variable u : nat -> @CRComplex R.

(* 单位范数：⟨u_j,u_j⟩ = 1 *)
Hypothesis Hu_unit : forall j, le j 3 ->
  CReq R (CRnorm_sq (u j)) (CR_of_Q R (Qmake 1 1)).

(* 逐对相干上界：|⟨u_i,u_j⟩| ≤ pfb4 i j（i ≠ j） *)
Hypothesis Hu_pf : forall i j, le i 3 -> le j 3 -> i <> j ->
  CRle R (CRabs R (CRip (u i) (u j))) (CR_of_Q R (pfb4 i j)).

(* ---------- CR 层 Q-常数桥 ---------- *)

Definition pfb4c (i j : nat) : CRcarrier R := CR_of_Q R (pfb4 i j).
Definition rho4c : CRcarrier R := CR_of_Q R rho4.
Definition lam4c : CRcarrier R := CR_of_Q R lam4.

Lemma pfb4c_pos : forall i j, le i 3 -> le j 3 ->
  CRle R (CR_of_Q R (Qmake 0 1)) (pfb4c i j).
Proof. intros i j Hi Hj. apply CR_of_Q_le. apply pfb4_nonneg; assumption. Qed.

Lemma pfb4c_sym : forall i j, le i 3 -> le j 3 ->
  CReq R (pfb4c i j) (pfb4c j i).
Proof.
  intros i j Hi Hj. apply (CR_of_Q_morph R (pfb4 i j) (pfb4 j i)).
  rewrite (pfb4_sym i j Hi Hj). apply Qeq_refl.
Qed.

Lemma rho4c_lt_one : CRlt R rho4c (CR_of_Q R (Qmake 1 1)).
Proof. exact (CR_of_Q_lt R rho4 (Qmake 1 1) rho4_lt_one). Qed.

Lemma lam4c_pos : CRlt R (CR_of_Q R (Qmake 0 1)) lam4c.
Proof. exact (CR_of_Q_lt R (Qmake 0 1) lam4 lam4_pos). Qed.

(* ---------- 通用工具 ---------- *)

(* CRopp 保序（本地自备——本探针不依赖 zeta 库）。
   注意 CRplus_le_reg_r 是右加法消去：r1 + r ≤ r2 + r -> r1 ≤ r2 *)
Lemma c4g_opp_le_compat (a b : CRcarrier R) :
  CRle R a b -> CRle R (CRopp R b) (CRopp R a).
Proof.
  intros Hab.
  apply (CRplus_le_reg_r (R:=R) b).
  assert (H0 : CRle R (CRopp R b + b) (CRopp R a + b)).
  { assert (Hz2 : CReq R (CRopp R b + b) (CR_of_Q R (Qmake 0 1))) by ring.
    apply (CRle_trans (R:=R) (CRopp R b + b)
             (CR_of_Q R (Qmake 0 1)) (CRopp R a + b)).
    - exact (proj2 Hz2).
    - apply (CRle_trans (R:=R) (CR_of_Q R (Qmake 0 1))
               (a + CRopp R a) (CRopp R a + b)).
      + assert (Hz : CReq R (a + CRopp R a) (CR_of_Q R (Qmake 0 1))) by ring.
        exact (proj1 Hz).
      + apply (CRle_trans (R:=R) (a + CRopp R a) (b + CRopp R a)
                 (CRopp R a + b)).
        * apply CRplus_le_compat; [exact Hab | apply CRle_refl].
        * assert (Hc : CReq R (b + CRopp R a) (CRopp R a + b)) by ring.
          exact (proj2 Hc). }
  exact H0.
Qed.

(* 三项三角不等式（CS-21 同款） *)
Lemma c4g_abs_tri3 (b1 b2 b3 : CRcarrier R) :
  CRle R (CRabs R (b1 + (b2 + b3)))
         (CRabs R b1 + (CRabs R b2 + CRabs R b3)).
Proof.
  apply (CRle_trans (R:=R) (CRabs R (b1 + (b2 + b3)))
           (CRabs R b1 + CRabs R (b2 + b3))
           (CRabs R b1 + (CRabs R b2 + CRabs R b3))).
  - apply CRabs_triang.
  - apply CRplus_le_compat; [apply CRle_refl | apply CRabs_triang].
Qed.

(* 五项三角不等式（右嵌套）：assoc 桥 → tri3 → 逐项三角 → ring 收口 *)
Lemma c4g_abs5 (f1 f2 f3 f4 f5 : CRcarrier R) :
  CRle R (CRabs R (f1 + (f2 + (f3 + (f4 + f5)))))
         (CRabs R f1 + (CRabs R f2 + (CRabs R f3 + (CRabs R f4 + CRabs R f5)))).
Proof.
  apply (CRle_trans (R:=R) (CRabs R (f1 + (f2 + (f3 + (f4 + f5)))))
           (CRabs R ((f1 + f2) + (f3 + (f4 + f5))))
           (CRabs R f1 + (CRabs R f2 + (CRabs R f3 + (CRabs R f4 + CRabs R f5))))).
  - apply (proj2 (CRabs_morph_prop R (f1 + (f2 + (f3 + (f4 + f5))))
                   ((f1 + f2) + (f3 + (f4 + f5))) ltac:(ring))).
  - apply (CRle_trans (R:=R) (CRabs R ((f1 + f2) + (f3 + (f4 + f5))))
             (CRabs R (f1 + f2) + (CRabs R f3 + CRabs R (f4 + f5)))
             (CRabs R f1 + (CRabs R f2 + (CRabs R f3 + (CRabs R f4 + CRabs R f5))))).
    + exact (c4g_abs_tri3 (f1 + f2) f3 (f4 + f5)).
    + apply (CRle_trans (R:=R)
               (CRabs R (f1 + f2) + (CRabs R f3 + CRabs R (f4 + f5)))
               ((CRabs R f1 + CRabs R f2) + (CRabs R f3 + (CRabs R f4 + CRabs R f5)))
               (CRabs R f1 + (CRabs R f2 + (CRabs R f3 + (CRabs R f4 + CRabs R f5))))).
      * apply CRplus_le_compat.
        -- exact (CRabs_triang (R:=R) f1 f2).
        -- apply CRplus_le_compat; [apply CRle_refl | exact (CRabs_triang (R:=R) f4 f5)].
      * assert (Hr : CReq R ((CRabs R f1 + CRabs R f2)
                             + (CRabs R f3 + (CRabs R f4 + CRabs R f5)))
                       (CRabs R f1 + (CRabs R f2 + (CRabs R f3
                        + (CRabs R f4 + CRabs R f5)))))
          by ring.
        exact (proj2 Hr).
Qed.

(* ---------- Gram 结构（组合内积双线性展开的 Q-表桥） ---------- *)

Definition g4 (i j : nat) : CRcarrier R := CRip (u i) (u j).

(* Gram 第 j 列 ×c：Σ_i c_i·G_ij（含对角） *)
Definition colg (c : nat -> CRcarrier R) (j : nat) : CRcarrier R :=
  c 0%nat * g4 0%nat j + (c 1%nat * g4 1%nat j
   + (c 2%nat * g4 2%nat j + c 3%nat * g4 3%nat j)).

(* 非对角列（j 列去掉自项） *)
Definition colb0 (c : nat -> CRcarrier R) : CRcarrier R :=
  c 1%nat * g4 1%nat 0%nat + (c 2%nat * g4 2%nat 0%nat + c 3%nat * g4 3%nat 0%nat).
Definition colb1 (c : nat -> CRcarrier R) : CRcarrier R :=
  c 0%nat * g4 0%nat 1%nat + (c 2%nat * g4 2%nat 1%nat + c 3%nat * g4 3%nat 1%nat).
Definition colb2 (c : nat -> CRcarrier R) : CRcarrier R :=
  c 0%nat * g4 0%nat 2%nat + (c 1%nat * g4 1%nat 2%nat + c 3%nat * g4 3%nat 2%nat).
Definition colb3 (c : nat -> CRcarrier R) : CRcarrier R :=
  c 0%nat * g4 0%nat 3%nat + (c 1%nat * g4 1%nat 3%nat + c 2%nat * g4 2%nat 3%nat).

(* 非对角对 (i<j) 的 CR 值：c_i·c_j·G_ij + c_j·c_i·G_ji *)
Definition pairv (c : nat -> CRcarrier R) (i j : nat) : CRcarrier R :=
  c i * c j * g4 i j + c j * c i * g4 j i.

(* 非对角部分 E = Σ_{i<j} pairv（对邻六对，对邻嵌套） *)
Definition Egrp (c : nat -> CRcarrier R) : CRcarrier R :=
  (pairv c 0%nat 1%nat + (pairv c 0%nat 2%nat + (pairv c 0%nat 3%nat
   + (pairv c 1%nat 2%nat + pairv c 1%nat 3%nat))))
  + pairv c 2%nat 3%nat.

(* ---------- 能量恒等式：⟨combo,combo⟩ ≡ Σ_j c_j·colg c j ---------- *)

(* ⟨combo 3, v⟩ ≡ Σ_j c_j·⟨u_j,v⟩（CRcombo_ip_rec 三步 + ring） *)
Lemma combo3_ip_expand (c : nat -> CRcarrier R) (v : @CRComplex R) :
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

(* CRip 定义对称（实双线性形式）：⟨x,y⟩ ≡ ⟨y,x⟩ *)
Lemma c4g_ip_sym (x y : @CRComplex R) : CReq R (CRip x y) (CRip y x).
Proof. unfold CRip. ring. Qed.

(* ⟨u_j, combo⟩ ≡ colg c j：对称翻转 + 组合展开 *)
Lemma col_ip (c : nat -> CRcarrier R) (j : nat) :
  CReq R (CRip (u j) (CRcombo 3 c u)) (colg c j).
Proof.
  apply (CReq_trans (CRip (u j) (CRcombo 3 c u))
           (CRip (CRcombo 3 c u) (u j)) (colg c j)).
  - exact (c4g_ip_sym (u j) (CRcombo 3 c u)).
  - exact (combo3_ip_expand c (u j)).
Qed.

(* ★ 核心恒等式一（Gram 二次型展开 = 能量恒等式）：
   ‖combo‖² ≡ c₀·colg 0 + (c₁·colg 1 + (c₂·colg 2 + c₃·colg 3)) *)
Theorem c4g_gram_energy (c : nat -> CRcarrier R) :
  CReq R (CRnorm_sq (CRcombo 3 c u))
    (c 0%nat * colg c 0%nat
     + (c 1%nat * colg c 1%nat
     + (c 2%nat * colg c 2%nat
     +  c 3%nat * colg c 3%nat))).
Proof.
  apply (CReq_trans (CRnorm_sq (CRcombo 3 c u))
           (CRip (CRcombo 3 c u) (CRcombo 3 c u))
           (c 0%nat * colg c 0%nat
            + (c 1%nat * colg c 1%nat
            + (c 2%nat * colg c 2%nat
            +  c 3%nat * colg c 3%nat)))).
  - unfold CRnorm_sq. split; apply CRle_refl.
  - setoid_rewrite (combo3_ip_expand c (CRcombo 3 c u)).
    setoid_rewrite (col_ip c 0%nat).
    setoid_rewrite (col_ip c 1%nat).
    setoid_rewrite (col_ip c 2%nat).
    setoid_rewrite (col_ip c 3%nat).
    split; apply CRle_refl.
Qed.

(* 对角项：c_j·colg j ≡ c_j²·G_jj + c_j·colbj（逐 j 具体——match 实例化
   后的 iota 归约在 setoid_rewrite 实例里不可靠，E-本卡） *)
Lemma diag_j0 (c : nat -> CRcarrier R) :
  CReq R (c 0%nat * colg c 0%nat)
    (c 0%nat * c 0%nat * g4 0%nat 0%nat + c 0%nat * colb0 c).
Proof. unfold colg, colb0. ring. Qed.
Lemma diag_j1 (c : nat -> CRcarrier R) :
  CReq R (c 1%nat * colg c 1%nat)
    (c 1%nat * c 1%nat * g4 1%nat 1%nat + c 1%nat * colb1 c).
Proof. unfold colg, colb1. ring. Qed.
Lemma diag_j2 (c : nat -> CRcarrier R) :
  CReq R (c 2%nat * colg c 2%nat)
    (c 2%nat * c 2%nat * g4 2%nat 2%nat + c 2%nat * colb2 c).
Proof. unfold colg, colb2. ring. Qed.
Lemma diag_j3 (c : nat -> CRcarrier R) :
  CReq R (c 3%nat * colg c 3%nat)
    (c 3%nat * c 3%nat * g4 3%nat 3%nat + c 3%nat * colb3 c).
Proof. unfold colg, colb3. ring. Qed.

(* 对角元 = 1：G_jj ≡ 1（Hu_unit 经 CRnorm_sq 定义展开转换） *)
Lemma unit_g (j : nat) (Hj : le j 3) : CReq R (g4 j j) (CR_of_Q R (Qmake 1 1)).
Proof. unfold g4. exact (Hu_unit j Hj). Qed.

Lemma diag_unit (c : nat -> CRcarrier R) (j : nat) (Hj : le j 3) :
  CReq R (c j * c j * g4 j j) (c j * c j).
Proof.
  setoid_rewrite (unit_g j Hj). ring.
Qed.

(* ---------- ★ 列-对重排：Σ_j c_j·colg j ≡ S + Egrp（32 单项式 ring） ---------- *)

Theorem c4g_colb_split (c : nat -> CRcarrier R) :
  CReq R (c 0%nat * colg c 0%nat
          + (c 1%nat * colg c 1%nat
          + (c 2%nat * colg c 2%nat
          +  c 3%nat * colg c 3%nat)))
         (CRsum (fun j => c j * c j) 3 + Egrp c).
Proof.
  unfold Egrp, pairv.
  change (CRsum (fun j => c j * c j) 3) with
    (((c 0%nat * c 0%nat) + (c 1%nat * c 1%nat))
     + (c 2%nat * c 2%nat) + c 3%nat * c 3%nat).
  setoid_rewrite (diag_j0 c).
  setoid_rewrite (diag_j1 c).
  setoid_rewrite (diag_j2 c).
  setoid_rewrite (diag_j3 c).
  setoid_rewrite (diag_unit c 0%nat ltac:(lia)).
  setoid_rewrite (diag_unit c 1%nat ltac:(lia)).
  setoid_rewrite (diag_unit c 2%nat ltac:(lia)).
  setoid_rewrite (diag_unit c 3%nat ltac:(lia)).
  unfold colb0, colb1, colb2, colb3.
  ring.
Qed.

(* ---------- 逐对绝对值 / AM-GM 工具 ---------- *)

(* |c_i·c_j·G_ij| ≤ |c_i|·|c_j|·pfb4 i j *)
Lemma term2_abs (c : nat -> CRcarrier R) (i j : nat)
  (Hi : le i 3) (Hj : le j 3) (Hij : i <> j) :
  CRle R (CRabs R (c i * c j * g4 i j))
         (CRabs R (c i) * CRabs R (c j) * pfb4c i j).
Proof.
  setoid_rewrite (CRabs_mult (R:=R) (c i * c j) (g4 i j)).
  setoid_rewrite (CRabs_mult (R:=R) (c i) (c j)).
  apply (CRmult_le_compat_l (R:=R) (CRabs R (c i) * CRabs R (c j))).
  - apply CRmult_le_0_compat; apply CRabs_pos.
  - exact (Hu_pf i j Hi Hj Hij).
Qed.

(* 对邻对绝对值：|pairv i j| ≤ |c_i||c_j|p_ij + |c_j||c_i|p_ji *)
Lemma pair_abs (c : nat -> CRcarrier R) (i j : nat)
  (Hi : le i 3) (Hj : le j 3) (Hij : i <> j) :
  CRle R (CRabs R (pairv c i j))
    (CRabs R (c i) * CRabs R (c j) * pfb4c i j
     + CRabs R (c j) * CRabs R (c i) * pfb4c j i).
Proof.
  unfold pairv.
  apply (CRle_trans (R:=R) (CRabs R (c i * c j * g4 i j + c j * c i * g4 j i))
           (CRabs R (c i * c j * g4 i j) + CRabs R (c j * c i * g4 j i))
           (CRabs R (c i) * CRabs R (c j) * pfb4c i j
            + CRabs R (c j) * CRabs R (c i) * pfb4c j i)).
  - apply CRabs_triang.
  - apply CRplus_le_compat.
    + exact (term2_abs c i j Hi Hj Hij).
    + exact (term2_abs c j i Hj Hi ltac:(congruence)).
Qed.

(* ★ 对邻对 AM-GM（Gershgorin 逐对收口）：
   |c_i||c_j|p_ij + |c_j||c_i|p_ji ≤ p_ij·(c_i²+c_j²)（表对称 + 2|ab|≤a²+b²） *)
Lemma pair_le (c : nat -> CRcarrier R) (i j : nat) (Hi : le i 3) (Hj : le j 3) :
  CRle R (CRabs R (c i) * CRabs R (c j) * pfb4c i j
          + CRabs R (c j) * CRabs R (c i) * pfb4c j i)
         (pfb4c i j * (c i * c i + c j * c j)).
Proof.
  setoid_rewrite (pfb4c_sym j i Hj Hi).
  apply (CRle_trans (R:=R)
           (CRabs R (c i) * CRabs R (c j) * pfb4c i j
            + CRabs R (c j) * CRabs R (c i) * pfb4c i j)
           (pfb4c i j * (CRabs R (c i) * CRabs R (c j)
                         + CRabs R (c j) * CRabs R (c i)))
           (pfb4c i j * (c i * c i + c j * c j))).
  - assert (Hr : CReq R (CRabs R (c i) * CRabs R (c j) * pfb4c i j
                         + CRabs R (c j) * CRabs R (c i) * pfb4c i j)
                  (pfb4c i j * (CRabs R (c i) * CRabs R (c j)
                                + CRabs R (c j) * CRabs R (c i))))
      by ring.
    exact (proj2 Hr).
  - apply CRmult_le_compat_l.
    + apply (pfb4c_pos i j Hi Hj).
    + assert (Hr2 : CReq R (CRabs R (c i) * CRabs R (c j)
                            + CRabs R (c j) * CRabs R (c i))
                     ((1 + 1) * (CRabs R (c i) * CRabs R (c j))))
        by ring.
      apply (CRle_trans (R:=R)
               (CRabs R (c i) * CRabs R (c j) + CRabs R (c j) * CRabs R (c i))
               ((1 + 1) * (CRabs R (c i) * CRabs R (c j)))
               (c i * c i + c j * c j)).
      * exact (proj2 Hr2).
      * exact (CRabs_amgm (c i) (c j)).
Qed.

(* ---------- Q-系数三和桥（PFLAT → CR_of_Q） ---------- *)

Lemma qsum0_cr :
  CReq R (pfb4c 0%nat 1%nat + (pfb4c 0%nat 2%nat + pfb4c 0%nat 3%nat))
         (CR_of_Q R (pfb4 0 1 + (pfb4 0 2 + pfb4 0 3))).
Proof.
  apply CReq_sym. unfold pfb4c.
  repeat setoid_rewrite (CR_of_Q_plus R). ring.
Qed.

Lemma qsum1_cr :
  CReq R (pfb4c 0%nat 1%nat + (pfb4c 1%nat 2%nat + pfb4c 1%nat 3%nat))
         (CR_of_Q R (pfb4 0 1 + (pfb4 1 2 + pfb4 1 3))).
Proof.
  apply CReq_sym. unfold pfb4c.
  repeat setoid_rewrite (CR_of_Q_plus R). ring.
Qed.

Lemma qsum2_cr :
  CReq R (pfb4c 0%nat 2%nat + (pfb4c 1%nat 2%nat + pfb4c 2%nat 3%nat))
         (CR_of_Q R (pfb4 0 2 + (pfb4 1 2 + pfb4 2 3))).
Proof.
  apply CReq_sym. unfold pfb4c.
  repeat setoid_rewrite (CR_of_Q_plus R). ring.
Qed.

Lemma qsum3_cr :
  CReq R (pfb4c 0%nat 3%nat + (pfb4c 1%nat 3%nat + pfb4c 2%nat 3%nat))
         (CR_of_Q R (pfb4 0 3 + (pfb4 1 3 + pfb4 2 3))).
Proof.
  apply CReq_sym. unfold pfb4c.
  repeat setoid_rewrite (CR_of_Q_plus R). ring.
Qed.

(* ---------- ★ 核心定理二：非对角部分的 Gershgorin 谱上界 ----------

   |Egrp| = |Σ_{i<j} pairv| ≤ Σ 对邻对绝对值 ≤ Σ p_ij·(c_i²+c_j²)
          ≡ Σ_k (三和_k)·c_k² ≤ ρ₄·Σc²（三和 ≤ ρ₄，Q 层判定） ---------- *)

(* 六对 PFLAT 重排（24 单项式 ring，同原子恒等式） *)
Lemma pp6_pflat (c : nat -> CRcarrier R) :
  CReq R (pfb4c 0 1 * (c 0%nat * c 0%nat + c 1%nat * c 1%nat)
          + (pfb4c 0 2 * (c 0%nat * c 0%nat + c 2%nat * c 2%nat)
          + (pfb4c 0 3 * (c 0%nat * c 0%nat + c 3%nat * c 3%nat)
          + (pfb4c 1 2 * (c 1%nat * c 1%nat + c 2%nat * c 2%nat)
          + (pfb4c 1 3 * (c 1%nat * c 1%nat + c 3%nat * c 3%nat)
          +  pfb4c 2 3 * (c 2%nat * c 2%nat + c 3%nat * c 3%nat))))))
         ((pfb4c 0 1 + (pfb4c 0 2 + pfb4c 0 3)) * (c 0%nat * c 0%nat)
          + ((pfb4c 0 1 + (pfb4c 1 2 + pfb4c 1 3)) * (c 1%nat * c 1%nat)
          + ((pfb4c 0 2 + (pfb4c 1 2 + pfb4c 2 3)) * (c 2%nat * c 2%nat)
          +  (pfb4c 0 3 + (pfb4c 1 3 + pfb4c 2 3)) * (c 3%nat * c 3%nat)))).
Proof. ring. Qed.

(* PFLAT ≤ ρ₄·Σc²：三和桥 + Q 判定 + 乘法保序 *)
Lemma pflat_le_rhoS (c : nat -> CRcarrier R) :
  CRle R ((pfb4c 0 1 + (pfb4c 0 2 + pfb4c 0 3)) * (c 0%nat * c 0%nat)
          + ((pfb4c 0 1 + (pfb4c 1 2 + pfb4c 1 3)) * (c 1%nat * c 1%nat)
          + ((pfb4c 0 2 + (pfb4c 1 2 + pfb4c 2 3)) * (c 2%nat * c 2%nat)
          +  (pfb4c 0 3 + (pfb4c 1 3 + pfb4c 2 3)) * (c 3%nat * c 3%nat))))
         (rho4c * CRsum (fun j => c j * c j) 3).
Proof.
  change (CRsum (fun j => c j * c j) 3) with
    (((c 0%nat * c 0%nat) + (c 1%nat * c 1%nat))
     + (c 2%nat * c 2%nat) + c 3%nat * c 3%nat).
  setoid_rewrite qsum0_cr.
  setoid_rewrite qsum1_cr.
  setoid_rewrite qsum2_cr.
  setoid_rewrite qsum3_cr.
  apply (CRle_trans (R:=R)
           (CR_of_Q R (pfb4 0 1 + (pfb4 0 2 + pfb4 0 3)) * (c 0%nat * c 0%nat)
            + (CR_of_Q R (pfb4 0 1 + (pfb4 1 2 + pfb4 1 3)) * (c 1%nat * c 1%nat)
            + (CR_of_Q R (pfb4 0 2 + (pfb4 1 2 + pfb4 2 3)) * (c 2%nat * c 2%nat)
            +  CR_of_Q R (pfb4 0 3 + (pfb4 1 3 + pfb4 2 3)) * (c 3%nat * c 3%nat))))
           (rho4c * (c 0%nat * c 0%nat)
            + (rho4c * (c 1%nat * c 1%nat)
            + (rho4c * (c 2%nat * c 2%nat) + rho4c * (c 3%nat * c 3%nat))))
           (rho4c * (((c 0%nat * c 0%nat) + (c 1%nat * c 1%nat))
                     + (c 2%nat * c 2%nat) + c 3%nat * c 3%nat))).
  - apply (CRplus_le_compat (R:=R)
        (CR_of_Q R (pfb4 0 1 + (pfb4 0 2 + pfb4 0 3)) * (c 0%nat * c 0%nat))
        (rho4c * (c 0%nat * c 0%nat))
        (CR_of_Q R (pfb4 0 1 + (pfb4 1 2 + pfb4 1 3)) * (c 1%nat * c 1%nat)
         + (CR_of_Q R (pfb4 0 2 + (pfb4 1 2 + pfb4 2 3)) * (c 2%nat * c 2%nat)
         +  CR_of_Q R (pfb4 0 3 + (pfb4 1 3 + pfb4 2 3)) * (c 3%nat * c 3%nat)))
        (rho4c * (c 1%nat * c 1%nat)
         + (rho4c * (c 2%nat * c 2%nat) + rho4c * (c 3%nat * c 3%nat)))).
    + apply (CRmult_le_compat_r (R:=R) (c 0%nat * c 0%nat)).
      * exact (CRsqr_nonneg (c 0%nat)).
      * apply CR_of_Q_le. exact qsum0_le_rho4.
    + apply (CRplus_le_compat (R:=R)
        (CR_of_Q R (pfb4 0 1 + (pfb4 1 2 + pfb4 1 3)) * (c 1%nat * c 1%nat))
        (rho4c * (c 1%nat * c 1%nat))
        (CR_of_Q R (pfb4 0 2 + (pfb4 1 2 + pfb4 2 3)) * (c 2%nat * c 2%nat)
         + CR_of_Q R (pfb4 0 3 + (pfb4 1 3 + pfb4 2 3)) * (c 3%nat * c 3%nat))
        (rho4c * (c 2%nat * c 2%nat) + rho4c * (c 3%nat * c 3%nat))).
      * apply (CRmult_le_compat_r (R:=R) (c 1%nat * c 1%nat)).
        -- exact (CRsqr_nonneg (c 1%nat)).
        -- apply CR_of_Q_le. exact qsum1_le_rho4.
      * apply (CRplus_le_compat (R:=R)
          (CR_of_Q R (pfb4 0 2 + (pfb4 1 2 + pfb4 2 3)) * (c 2%nat * c 2%nat))
          (rho4c * (c 2%nat * c 2%nat))
          (CR_of_Q R (pfb4 0 3 + (pfb4 1 3 + pfb4 2 3)) * (c 3%nat * c 3%nat))
          (rho4c * (c 3%nat * c 3%nat))).
        -- apply (CRmult_le_compat_r (R:=R) (c 2%nat * c 2%nat)).
           ++ exact (CRsqr_nonneg (c 2%nat)).
           ++ apply CR_of_Q_le. exact qsum2_le_rho4.
        -- apply (CRmult_le_compat_r (R:=R) (c 3%nat * c 3%nat)).
           ++ exact (CRsqr_nonneg (c 3%nat)).
           ++ apply CR_of_Q_le. exact qsum3_le_rho4.
  - assert (Hr : CReq R (rho4c * (c 0%nat * c 0%nat)
                         + (rho4c * (c 1%nat * c 1%nat)
                         + (rho4c * (c 2%nat * c 2%nat) + rho4c * (c 3%nat * c 3%nat))))
                  (rho4c * (((c 0%nat * c 0%nat) + (c 1%nat * c 1%nat))
                            + (c 2%nat * c 2%nat) + c 3%nat * c 3%nat)))
      by ring.
    exact (proj2 Hr).
Qed.

(* ---------- 中间形态缩写（T：逐对绝对值六叶；PP6：六对 p-和；
   PFLAT：系数分组形） ---------- *)

Definition T (c : nat -> CRcarrier R) : CRcarrier R :=
  (CRabs R (pairv c 0%nat 1%nat)
   + (CRabs R (pairv c 0%nat 2%nat)
   + (CRabs R (pairv c 0%nat 3%nat)
   + (CRabs R (pairv c 1%nat 2%nat) + CRabs R (pairv c 1%nat 3%nat)))))
  + CRabs R (pairv c 2%nat 3%nat).
Definition TR (c : nat -> CRcarrier R) : CRcarrier R :=
  CRabs R (pairv c 0%nat 1%nat)
   + (CRabs R (pairv c 0%nat 2%nat)
   + (CRabs R (pairv c 0%nat 3%nat)
   + (CRabs R (pairv c 1%nat 2%nat)
   + (CRabs R (pairv c 1%nat 3%nat) + CRabs R (pairv c 2%nat 3%nat))))).
Lemma t_tr (c : nat -> CRcarrier R) : CReq R (T c) (TR c).
Proof. unfold T, TR. ring. Qed.
Definition PP6 (c : nat -> CRcarrier R) : CRcarrier R :=
  pfb4c 0%nat 1%nat * (c 0%nat * c 0%nat + c 1%nat * c 1%nat)
   + (pfb4c 0%nat 2%nat * (c 0%nat * c 0%nat + c 2%nat * c 2%nat)
   + (pfb4c 0%nat 3%nat * (c 0%nat * c 0%nat + c 3%nat * c 3%nat)
   + (pfb4c 1%nat 2%nat * (c 1%nat * c 1%nat + c 2%nat * c 2%nat)
   + (pfb4c 1%nat 3%nat * (c 1%nat * c 1%nat + c 3%nat * c 3%nat)
   +  pfb4c 2%nat 3%nat * (c 2%nat * c 2%nat + c 3%nat * c 3%nat))))).
Definition PFLAT (c : nat -> CRcarrier R) : CRcarrier R :=
  (pfb4c 0%nat 1%nat + (pfb4c 0%nat 2%nat + pfb4c 0%nat 3%nat)) * (c 0%nat * c 0%nat)
   + ((pfb4c 0%nat 1%nat + (pfb4c 1%nat 2%nat + pfb4c 1%nat 3%nat)) * (c 1%nat * c 1%nat)
   + ((pfb4c 0%nat 2%nat + (pfb4c 1%nat 2%nat + pfb4c 2%nat 3%nat)) * (c 2%nat * c 2%nat)
   +  (pfb4c 0%nat 3%nat + (pfb4c 1%nat 3%nat + pfb4c 2%nat 3%nat)) * (c 3%nat * c 3%nat))).

(* ★ 主界：|Egrp| ≤ ρ₄·Σc²（对邻绝对值 → 逐对 AM-GM → 三和收缩） *)
Theorem c4g_E_abs_bound (c : nat -> CRcarrier R) :
  CRle R (CRabs R (Egrp c))
         (rho4c * CRsum (fun j => c j * c j) 3).
Proof.
  (* 外层：|Egrp| ≤ T ≤ TR ≤ PP6 ≤ ρS（每跳 trans 的 C=当前目标 RHS，
     深层递归嵌入第二前提；E-本卡） *)
  apply (CRle_trans (R:=R) (CRabs R (Egrp c)) (T c)
           (rho4c * CRsum (fun j => c j * c j) 3)).
  - (* 第一跳：|Egrp| ≤ T（三角 + abs5 + 显式 compat） *)
    apply (CRle_trans (R:=R) (CRabs R (Egrp c))
             ((CRabs R (pairv c 0%nat 1%nat + (pairv c 0%nat 2%nat + (pairv c 0%nat 3%nat
                        + (pairv c 1%nat 2%nat + pairv c 1%nat 3%nat)))))
              + CRabs R (pairv c 2%nat 3%nat))
             (T c)).
    + unfold Egrp. apply CRabs_triang.
    + apply (CRplus_le_compat (R:=R)
        (CRabs R (pairv c 0%nat 1%nat + (pairv c 0%nat 2%nat + (pairv c 0%nat 3%nat
                   + (pairv c 1%nat 2%nat + pairv c 1%nat 3%nat)))))
        (CRabs R (pairv c 0%nat 1%nat) + (CRabs R (pairv c 0%nat 2%nat)
         + (CRabs R (pairv c 0%nat 3%nat) + (CRabs R (pairv c 1%nat 2%nat)
          + CRabs R (pairv c 1%nat 3%nat)))))
        (CRabs R (pairv c 2%nat 3%nat))
        (CRabs R (pairv c 2%nat 3%nat))).
      * exact (c4g_abs5 (pairv c 0%nat 1%nat) (pairv c 0%nat 2%nat)
                 (pairv c 0%nat 3%nat) (pairv c 1%nat 2%nat) (pairv c 1%nat 3%nat)).
      * apply CRle_refl.
  - (* 第二跳：T ≡ TR ≤ PP6 ≤ ρS *)
    apply (CRle_trans (R:=R) (T c) (TR c)
             (rho4c * CRsum (fun j => c j * c j) 3)).
    + exact (proj2 (t_tr c)).
    + apply (CRle_trans (R:=R) (TR c) (PP6 c)
               (rho4c * CRsum (fun j => c j * c j) 3)).
      * (* TR ≤ PP6：头对齐 plain compat 递归 + 逐对两步 *)
        apply CRplus_le_compat.
        -- apply (CRle_trans (R:=R) (CRabs R (pairv c 0%nat 1%nat))
                    (CRabs R (c 0%nat) * CRabs R (c 1%nat) * pfb4c 0 1
                     + CRabs R (c 1%nat) * CRabs R (c 0%nat) * pfb4c 1 0)
                    (pfb4c 0 1 * (c 0%nat * c 0%nat + c 1%nat * c 1%nat))).
           ++ apply (pair_abs c 0 1 ltac:(lia) ltac:(lia) ltac:(lia)).
           ++ apply (pair_le c 0 1 ltac:(lia) ltac:(lia)).
        -- apply CRplus_le_compat.
           ++ apply (CRle_trans (R:=R) (CRabs R (pairv c 0%nat 2%nat))
                       (CRabs R (c 0%nat) * CRabs R (c 2%nat) * pfb4c 0 2
                        + CRabs R (c 2%nat) * CRabs R (c 0%nat) * pfb4c 2 0)
                       (pfb4c 0 2 * (c 0%nat * c 0%nat + c 2%nat * c 2%nat))).
              ** apply (pair_abs c 0 2 ltac:(lia) ltac:(lia) ltac:(lia)).
              ** apply (pair_le c 0 2 ltac:(lia) ltac:(lia)).
           ++ apply CRplus_le_compat.
              ** apply (CRle_trans (R:=R) (CRabs R (pairv c 0%nat 3%nat))
                          (CRabs R (c 0%nat) * CRabs R (c 3%nat) * pfb4c 0 3
                           + CRabs R (c 3%nat) * CRabs R (c 0%nat) * pfb4c 3 0)
                          (pfb4c 0 3 * (c 0%nat * c 0%nat + c 3%nat * c 3%nat))).
                 *** apply (pair_abs c 0 3 ltac:(lia) ltac:(lia) ltac:(lia)).
                 *** apply (pair_le c 0 3 ltac:(lia) ltac:(lia)).
              ** apply CRplus_le_compat.
                 --- apply (CRle_trans (R:=R) (CRabs R (pairv c 1%nat 2%nat))
                             (CRabs R (c 1%nat) * CRabs R (c 2%nat) * pfb4c 1 2
                              + CRabs R (c 2%nat) * CRabs R (c 1%nat) * pfb4c 2 1)
                             (pfb4c 1 2 * (c 1%nat * c 1%nat + c 2%nat * c 2%nat))).
                    **** apply (pair_abs c 1 2 ltac:(lia) ltac:(lia) ltac:(lia)).
                    **** apply (pair_le c 1 2 ltac:(lia) ltac:(lia)).
                 --- apply CRplus_le_compat.
                    ++++ apply (CRle_trans (R:=R) (CRabs R (pairv c 1%nat 3%nat))
                                (CRabs R (c 1%nat) * CRabs R (c 3%nat) * pfb4c 1 3
                                 + CRabs R (c 3%nat) * CRabs R (c 1%nat) * pfb4c 3 1)
                                (pfb4c 1 3 * (c 1%nat * c 1%nat + c 3%nat * c 3%nat))).
                       ----- apply (pair_abs c 1 3 ltac:(lia) ltac:(lia) ltac:(lia)).
                       ----- apply (pair_le c 1 3 ltac:(lia) ltac:(lia)).
                    ++++ apply (CRle_trans (R:=R) (CRabs R (pairv c 2%nat 3%nat))
                                (CRabs R (c 2%nat) * CRabs R (c 3%nat) * pfb4c 2 3
                                 + CRabs R (c 3%nat) * CRabs R (c 2%nat) * pfb4c 3 2)
                                (pfb4c 2 3 * (c 2%nat * c 2%nat + c 3%nat * c 3%nat))).
                       ----- apply (pair_abs c 2 3 ltac:(lia) ltac:(lia) ltac:(lia)).
                       ----- apply (pair_le c 2 3 ltac:(lia) ltac:(lia)).
      * (* PP6 ≤ ρS：PFLAT 重排桥 + 三和收缩 *)
        apply (CRle_trans (R:=R) (PP6 c) (PFLAT c)
                 (rho4c * CRsum (fun j => c j * c j) 3)).
        -- exact (proj2 (pp6_pflat c)).
        -- exact (pflat_le_rhoS c).
Qed.
Theorem c4g_combo_ge (c : nat -> CRcarrier R) :
  CRle R (CRsum (fun j => c j * c j) 3
          + CRopp R (rho4c * CRsum (fun j => c j * c j) 3))
         (CRnorm_sq (CRcombo 3 c u)).
Proof.
  assert (Heng : CReq R (CRnorm_sq (CRcombo 3 c u))
                  (CRsum (fun j => c j * c j) 3 + Egrp c)).
  { apply (CReq_trans _ _ _ (c4g_gram_energy c) (c4g_colb_split c)). }
  assert (Hneg : CRle R (CRopp R (rho4c * CRsum (fun j => c j * c j) 3))
                         (Egrp c)).
  { apply (CRle_trans (R:=R)
             (CRopp R (rho4c * CRsum (fun j => c j * c j) 3))
             (CRopp R (CRabs R (Egrp c)))
             (Egrp c)).
    - apply c4g_opp_le_compat. exact (c4g_E_abs_bound c).
    - exact (CRopp_abs_le_self (R:=R) (Egrp c)). }
  apply (CRle_trans (R:=R)
             (CRsum (fun j => c j * c j) 3
              + CRopp R (rho4c * CRsum (fun j => c j * c j) 3))
             (CRsum (fun j => c j * c j) 3 + Egrp c)
             (CRnorm_sq (CRcombo 3 c u))).
  - apply CRplus_le_compat; [apply CRle_refl | exact Hneg].
  - exact (proj1 Heng).
Qed.

(* ---------- ★ 核心定理三：Gram 下界（RIP-型与 λ*-型） ---------- *)

(* RIP 型：Σc² ≤ ‖combo‖² + ρ₄·Σc²（收缩引理接口形态） *)
Theorem c4g_gram_lower (c : nat -> CRcarrier R) :
  CRle R (CRsum (fun j => c j * c j) 3)
         (CRnorm_sq (CRcombo 3 c u)
          + rho4c * CRsum (fun j => c j * c j) 3).
Proof.
  assert (Hring : CReq R (CRsum (fun j => c j * c j) 3)
                  (CRsum (fun j => c j * c j) 3
                   + (rho4c * CRsum (fun j => c j * c j) 3
                      + CRopp R (rho4c * CRsum (fun j => c j * c j) 3)))).
  { setoid_rewrite (CRplus_opp_r (R:=R) (rho4c * CRsum (fun j => c j * c j) 3)).
    setoid_rewrite (CRplus_0_r (R:=R) (CRsum (fun j => c j * c j) 3)).
    split; apply CRle_refl. }
  apply (CRle_trans (R:=R) (CRsum (fun j => c j * c j) 3)
           (CRsum (fun j => c j * c j) 3
            + (rho4c * CRsum (fun j => c j * c j) 3
               + CRopp R (rho4c * CRsum (fun j => c j * c j) 3)))
           (CRnorm_sq (CRcombo 3 c u)
            + rho4c * CRsum (fun j => c j * c j) 3)).
  - exact (proj2 Hring).
  - assert (Hassoc : CReq R (CRsum (fun j => c j * c j) 3
                              + (rho4c * CRsum (fun j => c j * c j) 3
                                 + CRopp R (rho4c * CRsum (fun j => c j * c j) 3)))
                     ((CRsum (fun j => c j * c j) 3
                       + CRopp R (rho4c * CRsum (fun j => c j * c j) 3))
                      + rho4c * CRsum (fun j => c j * c j) 3))
      by ring.
    apply (CRle_trans (R:=R)
             (CRsum (fun j => c j * c j) 3
              + (rho4c * CRsum (fun j => c j * c j) 3
                 + CRopp R (rho4c * CRsum (fun j => c j * c j) 3)))
             ((CRsum (fun j => c j * c j) 3
               + CRopp R (rho4c * CRsum (fun j => c j * c j) 3))
              + rho4c * CRsum (fun j => c j * c j) 3)
             (CRnorm_sq (CRcombo 3 c u)
              + rho4c * CRsum (fun j => c j * c j) 3)).
    + exact (proj2 Hassoc).
    + apply CRplus_le_compat.
      * exact (c4g_combo_ge c).
      * apply CRle_refl.
Qed.

(* λ*-型（特征值下界主形态）：λ*·Σc² ≤ ‖combo‖²，λ* = 1 − ρ₄ = 651/3200 *)
Lemma lam4c_expand : CReq R lam4c (CR_of_Q R (Qmake 1 1) + CRopp R rho4c).
Proof.
  unfold lam4c, rho4c, lam4, Qminus.
  setoid_rewrite <- (CR_of_Q_opp rho4).
  apply CR_of_Q_plus.
Qed.

Theorem c4g_lam_lower (c : nat -> CRcarrier R) :
  CRle R (lam4c * CRsum (fun j => c j * c j) 3)
         (CRnorm_sq (CRcombo 3 c u)).
Proof.
  assert (Hb : CReq R (lam4c * CRsum (fun j => c j * c j) 3)
                (CRsum (fun j => c j * c j) 3
                 + CRopp R (rho4c * CRsum (fun j => c j * c j) 3))).
  { setoid_rewrite (CRopp_mult_distr_l (R:=R) rho4c
                      (CRsum (fun j => c j * c j) 3)).
    setoid_rewrite lam4c_expand.
    change (CRsum (fun j => c j * c j) 3) with
      (((c 0%nat * c 0%nat) + (c 1%nat * c 1%nat))
       + (c 2%nat * c 2%nat) + c 3%nat * c 3%nat).
    ring. }
  apply (CRle_trans (R:=R) (lam4c * CRsum (fun j => c j * c j) 3)
           (CRsum (fun j => c j * c j) 3
            + CRopp R (rho4c * CRsum (fun j => c j * c j) 3))
           (CRnorm_sq (CRcombo 3 c u))).
  - exact (proj2 Hb).
  - exact (c4g_combo_ge c).
Qed.

(* ---------- sigT 特征值下界证书（Set 层数据见证） ---------- *)

Definition c4g_lam_sigT :
  { lam : CRcarrier R &
    prod (CRlt R (CR_of_Q R (Qmake 0 1)) lam)
         (forall c : nat -> CRcarrier R,
           CRle R (lam * CRsum (fun j => c j * c j) 3)
                  (CRnorm_sq (CRcombo 3 c u))) } :=
  existT _ lam4c (pair lam4c_pos c4g_lam_lower).

(* ---------- ★★ 最终定理：四原子合成单射（Gram 谱口径） ---------- *)

Theorem c4g_synthesis_injective (c : nat -> CRcarrier R)
  (Hcombo : CRcombo 3 c u = CRzero) :
  forall j, le j 3 -> CReq R (c j) (CR_of_Q R (Qmake 0 1)).
Proof.
  intros j Hj.
  (* ‖combo‖² ≡ 0 *)
  assert (Hz : CReq R (CRnorm_sq (CRcombo 3 c u)) (CR_of_Q R (Qmake 0 1))).
  { rewrite Hcombo. unfold CRnorm_sq, CRip, CRzero. cbn [cre cim]. ring. }
  (* gram_lower + combo≡0 ⟹ S ≤ 0 + ρS ≡ ρS ⟹（ρ<1）S ≤ 0 *)
  assert (Hs : CRle R (CRsum (fun j => c j * c j) 3)
                       (rho4c * CRsum (fun j => c j * c j) 3)).
  { assert (Hstep : CRle R (CRsum (fun j => c j * c j) 3)
                      (CR_of_Q R (Qmake 0 1)
                       + rho4c * CRsum (fun j => c j * c j) 3)).
    { apply (CRle_trans (R:=R) (CRsum (fun j => c j * c j) 3)
               (CRnorm_sq (CRcombo 3 c u)
                + rho4c * CRsum (fun j => c j * c j) 3)
               (CR_of_Q R (Qmake 0 1)
                + rho4c * CRsum (fun j => c j * c j) 3)).
      - exact (c4g_gram_lower c).
      - apply CRplus_le_compat; [exact (proj2 Hz) | apply CRle_refl]. }
    assert (Hb : CReq R (CR_of_Q R (Qmake 0 1)
                         + rho4c * CRsum (fun j => c j * c j) 3)
                  (rho4c * CRsum (fun j => c j * c j) 3)).
    { setoid_rewrite (CRplus_0_l (R:=R) (rho4c * CRsum (fun j => c j * c j) 3)).
      split; apply CRle_refl. }
    exact (CRle_trans (R:=R) (CRsum (fun j => c j * c j) 3)
             (CR_of_Q R (Qmake 0 1) + rho4c * CRsum (fun j => c j * c j) 3)
             (rho4c * CRsum (fun j => c j * c j) 3) Hstep (proj2 Hb)). }
  (* S ≤ ρ₄·S ∧ ρ₄ < 1 ⟹ S ≤ 0（收缩） *)
  assert (Hs0 : CRle R (CRsum (fun j => c j * c j) 3) (CR_of_Q R (Qmake 0 1))).
  { exact (CRle_scaled_le_zero (R:=R) (CRsum (fun j => c j * c j) 3) rho4c
             Hs rho4c_lt_one). }
  (* S ≡ 0（S ≥ 0 + S ≤ 0）⟹ 逐项为零 *)
  assert (HS0 : CReq R (CRsum (fun j => c j * c j) 3) (CR_of_Q R (Qmake 0 1))).
  { split.
    - apply (cond_pos_sum (fun j => c j * c j) 3).
      intro k. apply CRsqr_nonneg.
    - exact Hs0. }
  exact (CRsum_sq_zero_terms (R:=R) 3 c HS0 j Hj).
Qed.

(* 推论：2-sparse 唯一恢复（差向量 ≤4-sparse ⟹ 全族覆盖） *)
Corollary c4g_2sparse_unique (ca cb : CRcarrier R)
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
  - apply (c4g_synthesis_injective _ Hcombo 0%nat). lia.
  - apply (c4g_synthesis_injective _ Hcombo 1%nat). lia.
Qed.

End C4GramUniqueCR.

(* ============ 审计 ============ *)
Print Assumptions c4g_gram_energy.
Print Assumptions c4g_colb_split.
Print Assumptions c4g_E_abs_bound.
Print Assumptions c4g_gram_lower.
Print Assumptions c4g_lam_lower.
Print Assumptions c4g_lam_sigT.
Print Assumptions c4g_synthesis_injective.
Print Assumptions c4g_2sparse_unique.

(* ============ 提取（窗口常数 + pfb 表 + bool 证书链） ============ *)
From Stdlib Require Import Extraction.
From Stdlib Require Import ConstructiveRcomplete.

(* ρ₄ / λ* 窗口：Qnum/Qden 具象化（Z * positive） *)
Definition c4g_rho4_window : Z * positive :=
  (Qnum rho4, Qden rho4).
Definition c4g_lam4_window : Z * positive :=
  (Qnum lam4, Qden lam4).

(* 逐对上界表（nat -> nat -> Q 可执行） *)
Definition c4g_pfb4_table : nat -> nat -> Q := pfb4.

(* 列和窗口 *)
Definition c4g_col_window : nat -> Z * positive :=
  fun j => (Qnum (col4 j), Qden (col4 j)).

(* 可执行 bool 证书链：行 ≤ ρ₄、ρ₄ < 1、λ* > 0、总证书 *)
Definition c4g_col_ok : nat -> bool := fun j => Qle_bool (col4 j) rho4.
Definition c4g_rho_ok : bool := negb (Qle_bool (Qmake 1 1) rho4).
(* Qlt_bool 不在默认 QArith（E179⑦）——用 negb ∘ Qle_bool 反向表达 *)
Definition c4g_lam_ok : bool := negb (Qle_bool lam4 (Qmake 0 1)).
Definition c4g_window_ok : bool :=
  andb c4g_rho_ok (andb c4g_lam_ok
    (andb (c4g_col_ok 0%nat)
      (andb (c4g_col_ok 1%nat)
        (andb (c4g_col_ok 2%nat) (c4g_col_ok 3%nat))))).

(* CR 组合实例具象化（柯西实数实例上的 λ* 与组合） *)
Definition c4g_ladder_zero :
  nat -> @CRComplex CRealConstructive := fun _ => CRzero.
Definition c4g_lam_cauchy : @CRcarrier CRealConstructive :=
  @CR_of_Q CRealConstructive lam4.
Definition c4g_combo_cauchy :
  (nat -> @CRcarrier CRealConstructive) -> @CRComplex CRealConstructive :=
  fun c => @CRcombo CRealConstructive 3 c c4g_ladder_zero.
Definition c4g_norm_sq_cauchy :
  (nat -> @CRcarrier CRealConstructive) -> @CRcarrier CRealConstructive :=
  fun c => @CRnorm_sq CRealConstructive (c4g_combo_cauchy c).

Extraction "c4_gram_unique_cr.ml"
  c4g_lam_cauchy c4g_rho4_window c4g_lam4_window c4g_pfb4_table
  c4g_col_window c4g_window_ok c4g_rho_ok c4g_lam_ok c4g_col_ok
  c4g_combo_cauchy c4g_norm_sq_cauchy.
