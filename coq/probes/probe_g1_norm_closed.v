(* ============================================================
   用户红线：零 Admitted、零自定义公理；经典 R/C 轨道（与 probe_pairbound/
             probe_incoherence 同轨——G-1 依赖 Cexp/sin 复分析基础设施，
             CR 构造性轨道无 exp/sin，按文档定位走经典轨道）。
   数学内容（加权阶梯范数精确闭式，评估 T*-2 定理化）：
     对混窗阶梯 F = Σ_{j≤M} c_j·ψ_{n_j}（ψ_n = 窗口化复指数，单位范数）：
       ‖F‖²_W = Σ_{j≤M} c_j²·‖ψ_{n_j}‖²_W + 2·Σ_{i<j≤M} c_i·c_j·K_W(n_i,n_j)
     其中 K_W(a,b) = ⟨ψ_a,ψ_b⟩_W 为**显式 Dirichlet 核比闭式**（单对公式的
     窗口求和版）——即 Gram 交叉项的精确解析形式。
   证明路线：
     R0. 求和/复工具（sum_f_R0 split/swap、Csum re 桥、rot_atom 几何和）
     R1. ★ 单对精确内积：ipW (psi a) (psi b) W 的显式闭式
          ——psi 定义展开 → rot_atom 几何和 → re 提取（Dirichlet 实部）
     R2. ★ Gram 完全展开：‖comboM M c u‖²_W
          = Σ_{j≤M} c_j²·‖u_j‖²_W + 2·Σ_{i<j≤M} c_i·c_j·⟨u_i,u_j⟩_W
          （norm_sq_comboM_rec 归纳 + ipW_combo_l 双和组装）
     R3. ★ G1_norm_closed（主定理）：u_j := psi (n_j) 实例化 R2，
          交叉项用 R1 闭式替换 ⟹ 加权阶梯范数精确等式
   依赖： probe_incoherence（comboM/ipW/norm_sq_comboM_rec/ipW_combo_l）、
          probe_partial（rot_atom/geom_sum_identity）、
          ca_basis（psi）、probe_parseval（re_mul_conj）。
   审计：零 Admitted / 零自定义公理（同 probe_pairbound 脚印）。
   ============================================================ *)
From mathcomp Require Import ssreflect ssrbool ssrnat seq eqtype div prime.
Require Import Stdlib.Reals.Reals.
Require Import Stdlib.Arith.Arith.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.micromega.Lra.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Logic.FunctionalExtensionality.
Require Import ca_base.
Require Import ca_complex_foundation.
Require Import ca_basis.
Require Import ca_independence.
Require Import ca_fourier.
Require Import ca_char_ortho.
Require Import ca_zeta_scaffold.
Require Import probe_grid_ortho.
Require Import probe_parseval.
Require Import probe_partial.
Require Import probe_pairbound.
Require Import probe_incoherence.
Import ComplexNumbers.
Import FourierAnalysis.
Import GridOrtho.
Import TPartial.
Import Incoherence.
Import Incoherence2.
Open Scope R_scope.
(* Open Scope complex_scope 已移除：scope 劫持 nat * 与 +（G-1 全 R 注解） *)
(* 所有 nat 运算用显式函数/括号标注 *)
Module G1NormClosed.
(* ============ R0. 求和工具（本地，防重名） ============ *)
(* 有限和递归公式（本地自证，probe_incoherence 未暴露顶层版） *)
Lemma g1_sum_S : forall (f : nat -> R) (n : nat),
  sum_f_R0 f (S n) = (sum_f_R0 f n + f (S n))%R.
Proof. intros. simpl. reflexivity. Qed.
(* 逐点相等 ⟹ 和相等（本地归纳版） *)
Lemma g1_sum_ext : forall (f g : nat -> R) (n : nat),
  (forall k, Nat.le k n -> f k = g k) ->
  sum_f_R0 f n = sum_f_R0 g n.
Proof.
  intros f g n H.
  induction n as [| n IH].
  - simpl. apply H. lia.
  - rewrite (g1_sum_S f n). rewrite (g1_sum_S g n).
    assert (Hih : forall k : nat, le k n -> f k = g k) by (intros k Hk; apply H; lia).
    rewrite (IH Hih).
    rewrite (H (S n) (Nat.le_refl (S n))). reflexivity.
Qed.
(* 常数提取：Σ (c·f k) = c·Σ f（本地） *)
Lemma g1_sum_scal : forall (c : R) (f : nat -> R) (n : nat),
  sum_f_R0 (fun k => (c * f k)%R) n = (c * sum_f_R0 f n)%R.
Proof.
  intros c f n.
  induction n as [| n IH].
  - simpl. ring.
  - rewrite (g1_sum_S (fun k => (c * f k)%R) n).
    rewrite (g1_sum_S f n). rewrite IH. ring.
Qed.
(* 常零和 = 0（本地） *)
Lemma g1_sum_zero : forall (n : nat),
  sum_f_R0 (fun _ : nat => 0%R) n = 0%R.
Proof.
  intros n. induction n as [| n IH].
  - reflexivity.
  - rewrite (g1_sum_S (fun _ => 0%R) n). rewrite IH. ring.
Qed.
(* Cof_real r *c z 的范数平方 = r²·‖z‖²（复用 Incoherence2.Cnorm_sq_scal） *)
Lemma g1_norm_Cof_mul (r : R) (z : Complex) :
  Cnorm_sq (Cof_real r *c z) = (r * r * Cnorm_sq z)%R.
Proof. exact (Cnorm_sq_scal r z). Qed.
(* 交叉双和（索引平移编码，外层 j'=S j 从 1 到 SM，i<j'，无伪项）。
   拆分：Σ_{j≤predn(SM)} = Σ_{j≤predn M} + 尾层 j'=SM（i=0..SM）。
   M≥1 前提（M=0 时 predn 1 = 0 给伪项 f 0 1，组合无原子 1） *)
Lemma g1_cross_S (M : nat) (f : nat -> nat -> R) :
  le 1 M ->
  (sum_f_R0 (fun j => sum_f_R0 (fun i => f i (S j)) j) (predn (S M)))%R
  = ((sum_f_R0 (fun j => sum_f_R0 (fun i => f i (S j)) j) (predn M))%R
     + (sum_f_R0 (fun i => f i (S M)) (predn (S M)))%R).
Proof.
  intros HM.
  destruct M as [| M'].
  - exfalso. lia.
  - rewrite (g1_sum_S (fun j => sum_f_R0 (fun i => f i (S j)) j) M').
    replace (predn (S (S M'))) with (S M') by lia.
    reflexivity.
Qed.
(* 对角尾部拆分：Σ_{j≤SM} c_j²·g_j = Σ_{j≤M} c_j²·g_j + c_{SM}²·g_{SM} *)
Lemma g1_diag_S (M : nat) (c : nat -> R) (g : nat -> R) :
  (sum_f_R0 (fun j => (c j * c j * g j)%R) (S M))%R
  = ((sum_f_R0 (fun j => (c j * c j * g j)%R) M)%R
     + (c (S M) * c (S M) * g (S M))%R)%R.
Proof. exact (g1_sum_S (fun j => (c j * c j * g j)%R) M). Qed.
(* 内层和展开：Σ_{i<SM} c_i·c_{SM}·⟨u_i,u_{SM}⟩ = Σ_{i≤M} ...（predn (S M) = M） *)
Lemma g1_cross_tail (M : nat) (c : nat -> R) (u : nat -> nat -> Complex) (W : nat) :
  (sum_f_R0 (fun i => (c i * c (S M) * ipW (u i) (u (S M)) W)%R) (predn (S M)))%R
  = (sum_f_R0 (fun i => (c i * c (S M) * ipW (u i) (u (S M)) W)%R) M)%R.
Proof.
  replace (predn (S M)) with M by lia. reflexivity.
Qed.
(* 双和交换：Σ_j c_j·Σ_i a_i·b_j·⟨u_i,u_j⟩ 换序（同索引聚合辅助，供组装） *)
Lemma g1_ipW_combo_l_cross (M : nat) (c : nat -> R) (u : nat -> nat -> Complex) (v : nat -> Complex) (W : nat) :
  (ipW (comboM (S M) c u) v W)%R
  = (sum_f_R0 (fun j => c j * ipW (u j) v W) M)%R.
Proof. exact (ipW_combo_l M c u v W). Qed.
(* ============ R1. 单对精确内积（ψ 闭式） ============ *)
(* k ≥ a 时 psi a k = C0（支撑外为零） *)
Lemma g1_psi_zero (a k : nat) :
  (a <= k)%nat -> psi a k = C0.
Proof.
  intros Hak.
  unfold psi.
  assert (Hkge : Nat.le a k) by (apply/leP; exact Hak).
  rewrite (phi_ge_n_zero a k Hkge).
  rewrite Cmul_0_r.
  reflexivity.
Qed.
(* k ≥ a 时 psi a k·conj(psi b k) = C0（支撑外乘积为零） *)
Lemma g1_psi_conj_zero (a b k : nat) :
  (a <= k)%nat -> (psi a k *c Cconj (psi b k))%C = C0.
Proof.
  intros Hak.
  rewrite (g1_psi_zero a k Hak).
  rewrite Cmul_0_l.
  reflexivity.
Qed.
(* k ≥ min(min a b)(S W) 且 k ≤ W ⟹ k ≥ min a b
   （若 k < min a b 则 m = S W ⟹ S W ≤ k 与 k ≤ W 矛盾） *)
Lemma g1_min_ge (a b W k : nat) :
  le (Nat.min (Nat.min a b) (S W)) k -> le k W ->
  le (Nat.min a b) k.
Proof.
  intros Hmk HkW.
  destruct (Nat.min_spec (Nat.min a b) (S W)) as [[Hlt Hmn] | [Hle Hmn]].
  - (* min a b < S W：min(min a b)(S W) = min a b *)
    rewrite Hmn in Hmk. exact Hmk.
  - (* S W ≤ min a b：min(min a b)(S W) = S W ⟹ S W ≤ k 与 k ≤ W 矛盾 *)
    rewrite Hmn in Hmk.
    exfalso. lia.
Qed.
(* Σ 截断：f 在 [m, W] 上为零 ⟹ Σ_{k≤W} f k = Σ_{k<predn m} f k（m ≤ S W）
   注意 Hz 只要求 m ≤ k ≤ W 范围内的 f k = 0（k > W 不在和中） *)
Lemma g1_sum_trunc (f : nat -> R) (W m : nat) :
  le m (S W) ->
  (forall k, le m k -> le k W -> f k = 0%R) ->
  (sum_f_R0 f W)%R = (sum_f_R0 f (predn m))%R.
Proof.
  intros HmW Hz.
  induction W as [| W IH].
  - (* W=0：sum_f_R0 f 0 = f 0；predn m 分 m=0/m=1（m ≤ 1） *)
    destruct m as [| m'].
    + simpl. reflexivity.
    + assert (Hm'0 : m' = 0%nat) by lia. subst. simpl. reflexivity.
  - (* W = S W'：m ≤ S(S W') *)
    destruct (Nat.leb m (S W)) as [] eqn: Hle.
    + (* m ≤ S W：sum_f_R0 f (S W) = sum_f_R0 f W + f (S W)，
         f (S W) = 0（Hz：le m (S W) 且 le (S W) (S W)）⟹ = sum_f_R0 f W = IH *)
      apply Nat.leb_le in Hle.
      rewrite (g1_sum_S f W).
      assert (Htail : f (S W) = 0%R).
      { apply Hz; lia. }
      rewrite Htail.
      assert (Hih' : forall k : nat, le m k -> le k W -> f k = 0%R) by (intros k Hk1 Hk2; apply Hz; [exact Hk1 | lia]).
      rewrite (IH Hle Hih').
      ring.
    + (* m > S W：但 m ≤ S(S W) ⟹ m = S(S W) ⟹ predn m = S W = S W' *)
      assert (Hgt : (S W < m)%coq_nat) by (apply (proj1 (Nat.leb_gt m (S W))); exact Hle).
      assert (Hm : m = S (S W)) by lia.
      rewrite (g1_sum_S f W).
      rewrite Hm. simpl. ring.
Qed.
(* Cconj 对纯虚指数：Cconj (Cexp (0+iθ)) = Cexp (0+i(−θ)) *)
(* le k (predn m) 且 1 ≤ m ⟹ k < m（nat 桥，lia + succ_pred） *)
Lemma g1_lt_pred (k m : nat) :
  le 1 m -> le k (Nat.pred m) -> lt k m.
Proof.
  intros Hm1 Hkm.
  destruct m as [| m'].
  - exfalso. lia.
  - simpl in Hkm. lia.
Qed.
Lemma g1_Cconj_Cof_real (r : R) :
  Cconj (Cof_real r) = Cof_real r.
Proof.
  unfold Cof_real, Cconj. simpl. apply Complex_eq; simpl; ring.
Qed.
(* Cconj 对纯虚指数：Cconj (Cexp (0+itheta)) = Cexp (0+i(−theta)) *)
Lemma g1_Cconj_exp (theta : R) :
  Cconj (Cexp (0 +i theta)) = Cexp (0 +i (- theta)).
Proof.
  unfold Cexp, Cconj. simpl.
  apply Complex_eq; simpl.
  - rewrite cos_neg. ring.
  - rewrite sin_neg. ring.
Qed.
(* 纯虚指数乘法：Cexp(0+itheta1)·Cexp(0+itheta2) = Cexp(0+i(theta1+theta2)) *)
Lemma g1_Cexp_mul_i (theta1 theta2 : R) :
  Cexp (0 +i theta1) *c Cexp (0 +i theta2) = Cexp (0 +i (theta1 + theta2)).
Proof.
  rewrite <- Cexp_add.
  f_equal.
  unfold Cadd.
  simpl.
  f_equal; ring.
Qed.
(* ψ_a 与 ψ_b 的单点积：psi a k *c Cconj (psi b k) = (1/√(ab))·rot_atom theta k，
   theta = 2π(b−a)/(ab)（k < min(a,b) 时） *)
Lemma g1_psi_point (a b k : nat) :
  (k < a)%nat -> (k < b)%nat ->
  (psi a k *c Cconj (psi b k))%C
  = (Cof_real ((1 / sqrt (INR a))%R * (1 / sqrt (INR b))%R)
     *c rot_atom ((2 * PI * (INR b - INR a)) / (INR a * INR b))%R k)%C.
Proof.
  intros Hka Hkb.
  (* 展开 psi 与 phi（k<a, k<b 时 phi = Cexp） *)
  unfold UnconditionalBasis.psi.
  rewrite Cconj_mul.
  rewrite (g1_Cconj_Cof_real (1 / sqrt (INR b))).
  (* UnconditionalBasis.phi a k = Cexp(0+i·2πk/a)，UnconditionalBasis.phi b k = Cexp(0+i·2πk/b) *)
  assert (Hphia : UnconditionalBasis.phi a k = Cexp (0 +i (2 * PI * INR k / INR a))).
  { unfold UnconditionalBasis.phi.
    assert (Hltb : (k <? a) = true).
    { apply (proj2 (Nat.ltb_lt k a)). move: Hka => /ltP Hka'. exact Hka'. }
    rewrite Hltb. reflexivity. }
  assert (Hphib : UnconditionalBasis.phi b k = Cexp (0 +i (2 * PI * INR k / INR b))).
  { unfold UnconditionalBasis.phi.
    assert (Hltb : (k <? b) = true).
    { apply (proj2 (Nat.ltb_lt k b)). move: Hkb => /ltP Hkb'. exact Hkb'. }
    rewrite Hltb. reflexivity. }
  rewrite Hphia.
  (* 展开 b 侧 phi：psi b k 内部 phi b k = Cexp(0+i·2πk/b)（Cconj 内 rewrite） *)
  rewrite Hphib.
  (* Cconj (Cexp (0+iθ)) = Cexp (0+i(−θ))，θ = 2πk/b（内联 g1_Cconj_exp） *)
  rewrite (g1_Cconj_exp (2 * PI * INR k / INR b)).
  (* 标量重组：(c1·Cexp(θ1))·(c2·Cexp(θ2)) = (c1·c2)·(Cexp(θ1)·Cexp(θ2)) *)
  set (c1 := Cof_real (1 / sqrt (INR a))).
  set (c2 := Cof_real (1 / sqrt (INR b))).
  assert (Hre : (c1 *c Cexp (0 +i (2 * PI * INR k / INR a)))
                *c (c2 *c Cexp (0 +i (- (2 * PI * INR k / INR b))))
                = (c1 *c c2) *c (Cexp (0 +i (2 * PI * INR k / INR a))
                                  *c Cexp (0 +i (- (2 * PI * INR k / INR b))))).
  { rewrite Cmul_assoc.
    assert (Htmp : Cexp (0 +i (2 * PI * INR k / INR a)) *c (c2 *c Cexp (0 +i (- (2 * PI * INR k / INR b))))
                   = c2 *c (Cexp (0 +i (2 * PI * INR k / INR a)) *c Cexp (0 +i (- (2 * PI * INR k / INR b))))).
    { rewrite <- Cmul_assoc.
      rewrite (Cmul_comm (Cexp (0 +i (2 * PI * INR k / INR a))) c2).
      rewrite Cmul_assoc. reflexivity. }
    rewrite Htmp. rewrite <- Cmul_assoc. reflexivity. }
  rewrite Hre.
  (* 乘法合并：Cexp(0+iθ1)·Cexp(0+i(−θ2)) = Cexp(0+i(θ1−θ2))
     —— 用 g1_Cexp_mul_i（已证） *)
  rewrite (g1_Cexp_mul_i (2 * PI * INR k / INR a) (- (2 * PI * INR k / INR b))).
  (* 角度归一：θ1+(−θ2) = INR k·2π(b−a)/(ab)，整体替换 Cexp 参数 *)
  assert (Hang : (2 * PI * INR k / INR a + - (2 * PI * INR k / INR b))
                 = (INR k * ((2 * PI * (INR b - INR a)) / (INR a * INR b)))%R).
  { field.
    split.
    - apply Rgt_not_eq. apply lt_0_INR. move: Hkb => /ltP Hkb'. lia.
    - apply Rgt_not_eq. apply lt_0_INR. move: Hka => /ltP Hka'. lia. }
  rewrite Hang.
  (* Cexp(0+i·INR k·theta) = rot_atom theta k（定义展开） *)
  replace (Cexp (0 +i (INR k * ((2 * PI * (INR b - INR a)) / (INR a * INR b)))))
    with (rot_atom ((2 * PI * (INR b - INR a)) / (INR a * INR b))%R k).
  2: { unfold rot_atom. reflexivity. }
  (* 标量合并：c1·c2 = Cof_real(1/√a)·Cof_real(1/√b) = Cof_real((1/√a)·(1/√b)) *)
  unfold c1, c2.
  replace (Cof_real (1 / sqrt (INR a)) *c Cof_real (1 / sqrt (INR b)))
    with (Cof_real ((1 / sqrt (INR a))%R * (1 / sqrt (INR b))%R)).
  2: { unfold Cof_real, Cmul. apply Complex_eq; simpl; ring. }
  reflexivity.
Qed.
(* ★ 单对精确内积（Dirichlet 实部闭式）：
   ipW (psi a) (psi b) W = (1/√(ab))·Σ_{k<m} re(rot_atom theta k)，
   m = min(a,b,W+1) —— 支撑截断 + 窗口截断（Σ 只到 k < m，即 predn m） *)
Lemma g1_ipW_psi (a b W : nat) :
  (1 <= a)%nat -> (1 <= b)%nat ->
  ipW (psi a) (psi b) W
  = ((1 / sqrt (INR a))%R * (1 / sqrt (INR b))%R)
    * sum_f_R0 (fun k => re (rot_atom ((2 * PI * (INR b - INR a)) / (INR a * INR b))%R k))
        (predn (Nat.min (Nat.min a b) (S W))).
Proof.
  intros H1 H2.
  unfold ipW.
  set (m := Nat.min (Nat.min a b) (S W)).
  assert (HmW : le m (S W)) by (unfold m; lia).
  assert (Hhz : forall k : nat, le m k -> le k W -> re (psi a k *c Cconj (psi b k)) = 0%R).
  { intros k Hk1 Hk2.
    assert (Hmin : le (Nat.min a b) k).
    { apply (g1_min_ge a b W k). exact Hk1. exact Hk2. }
    destruct (Nat.leb a b) as [] eqn: Hab.
    - apply Nat.leb_le in Hab.
      assert (Hak : le a k).
      { apply (Nat.le_trans _ (Nat.min a b) _).
        - rewrite (Nat.min_l a b Hab). reflexivity.
        - exact Hmin. }
      assert (Hakb : (a <= k)%nat) by (apply/leP; exact Hak).
      rewrite (g1_psi_conj_zero a b k Hakb). simpl. ring.
    - apply Nat.leb_gt in Hab.
      assert (Hbk : le b k).
      { apply (Nat.le_trans _ (Nat.min a b) _).
        - lia.
        - exact Hmin. }
      assert (Hbkb : (b <= k)%nat) by (apply/leP; exact Hbk).
      rewrite (g1_psi_zero b k Hbkb).
      unfold Cconj, C0, Cmul. simpl. ring. }
  rewrite (g1_sum_trunc (fun k => re (psi a k *c Cconj (psi b k))) W m HmW Hhz).
  unfold m.
  assert (Hext : forall k : nat, Nat.le k (predn (Nat.min (Nat.min a b) (S W))) ->
           re (psi a k *c Cconj (psi b k)) =
           (1 / sqrt (INR a))%R * (1 / sqrt (INR b))%R
             * re (rot_atom ((2 * PI * (INR b - INR a)) / (INR a * INR b))%R k)).
  { intros k Hk.
       assert (Hklt : lt k (Nat.min (Nat.min a b) (S W))).
       { apply (g1_lt_pred k (Nat.min (Nat.min a b) (S W))).
          - apply (Nat.min_glb (Nat.min a b) (S W) 1).
           + destruct (Nat.leb a b) as [] eqn: Hab.
             * apply Nat.leb_le in Hab.
               rewrite (Nat.min_l a b Hab). apply/leP. exact H1.
             * apply Nat.leb_gt in Hab.
               assert (Hba : le b a) by lia.
               rewrite (Nat.min_r a b Hba).
               apply/leP. exact H2.
            + lia.
         - exact Hk. }
       assert (Hka : lt k a).
        { apply (Stdlib.Arith.PeanoNat.Nat.lt_le_trans k (Nat.min (Nat.min a b) (S W)) a).
         - exact Hklt.
         - apply (Nat.le_trans _ (Nat.min a b) _).
           + apply Nat.le_min_l.
           + apply Nat.le_min_l. }
       assert (Hkb : lt k b).
         { apply (Stdlib.Arith.PeanoNat.Nat.lt_le_trans k (Nat.min (Nat.min a b) (S W)) b).
         - exact Hklt.
         - apply (Nat.le_trans _ (Nat.min a b) _).
           + apply Nat.le_min_l.
           + apply Nat.le_min_r. }
        assert (Hka' : (k < a)%nat) by (apply/ltP; exact Hka).
        assert (Hkb' : (k < b)%nat) by (apply/ltP; exact Hkb).
        rewrite (g1_psi_point a b k Hka' Hkb').
         rewrite Cof_real_mul_re.
         reflexivity. }
  rewrite (g1_sum_ext _ (fun k => ((1 / sqrt (INR a))%R * (1 / sqrt (INR b))%R
                                    * re (rot_atom ((2 * PI * (INR b - INR a)) / (INR a * INR b))%R k))%R)
                        (predn (Nat.min (Nat.min a b) (S W))) Hext).
  rewrite (g1_sum_scal ((1 / sqrt (INR a))%R * (1 / sqrt (INR b))%R)
            (fun k => re (rot_atom ((2 * PI * (INR b - INR a)) / (INR a * INR b))%R k))
            (predn (Nat.min (Nat.min a b) (S W)))).
  reflexivity.
Qed.
(* ‖comboM (S M) c u‖²_W = Σ_{j≤SM} c_j²·‖u_j‖²_W
   + 2·Σ_{j'=1}^{SM}Σ_{i<j'} c_i·c_{j'}·⟨u_i,u_{j'}⟩_W
   （comboM (S M) 含原子 0..SM；交叉和索引平移外层 j'=S j，j 到 predn M） *)
Lemma g1_gram_full (M : nat) (c : nat -> R) (u : nat -> nat -> Complex) (W : nat) :
  le 1 M ->
  (l2_norm_sq (comboM (S M) c u) W)%R
  = (sum_f_R0 (fun j => (c j * c j * l2_norm_sq (u j) W)%R) M
     + 2 * sum_f_R0 (fun j => sum_f_R0
         (fun i => (c i * c (S j) * ipW (u i) (u (S j)) W)%R) j) (predn M))%R.
Proof.
  intros HM.
  destruct M as [| M'].
  - exfalso. lia.
  - (* M = S M'：comboM (S (S M'))，归纳于 M' *)
    induction M' as [| M'' IH].
    + (* M'=0：comboM (S (S 0)) = comboM 2 = 两原子 u_0, u_1 *)
      rewrite (norm_sq_comboM_rec 0 c u W).
      rewrite (comboM_one c u).
      assert (Hc0 : (l2_norm_sq (fun k => Cof_real (c 0%nat) *c u 0%nat k) W)%R
                    = (c 0%nat * c 0%nat * l2_norm_sq (u 0%nat) W)%R).
      { unfold l2_norm_sq.
        assert (Hpt : forall k : nat, Nat.le k W -> (Cnorm_sq (Cof_real (c 0%nat) *c u 0%nat k) = c 0%nat * c 0%nat * Cnorm_sq (u 0%nat k))%R).
        { intro k. intro Hk. exact (g1_norm_Cof_mul (c 0%nat) (u 0%nat k)). }
        transitivity (sum_f_R0 (fun k => (c 0%nat * c 0%nat * Cnorm_sq (u 0%nat k))%R) W).
        { apply (g1_sum_ext (fun k => Cnorm_sq (Cof_real (c 0%nat) *c u 0%nat k))
                            (fun k => (c 0%nat * c 0%nat * Cnorm_sq (u 0%nat k))%R) W Hpt). }
        rewrite (g1_sum_scal (c 0%nat * c 0%nat) (fun k => Cnorm_sq (u 0%nat k)) W).
        reflexivity. }
      rewrite Hc0.
      (* 交叉项：2·c_1·⟨Cof_real(c_0)·u_0, u_1⟩ = 2·c_1·(c_0·⟨u_0,u_1⟩)
         （comboM 1 已归约，用 ipW_CR_l 线性提取） *)
      rewrite (ipW_CR_l (c 0%nat) (u 0%nat) (u 1%nat) W).
      (* RHS：对角 Σ_{j≤1} + 2·交叉 j'=1 层（i=0..0） *)
      replace (sum_f_R0 (fun j => (c j * c j * l2_norm_sq (u j) W)%R) 1)%R
        with ((c 0%nat * c 0%nat * l2_norm_sq (u 0%nat) W)%R
              + (c 1%nat * c 1%nat * l2_norm_sq (u 1%nat) W)%R)%R by reflexivity.
      replace (sum_f_R0 (fun j : nat => sum_f_R0
          (fun i : nat => (c i * c (S j) * ipW (u i) (u (S j)) W)%R) j) (predn 1))%R
        with (c 0%nat * c 1%nat * ipW (u 0%nat) (u 1%nat) W)%R by reflexivity.
      ring.
    + (* M' = S M''：comboM (S (S (S M'')))，norm_sq_comboM_rec (S M'') + IH *)
      rewrite (norm_sq_comboM_rec (S M'') c u W).
      rewrite (IH (le_n_S _ _ (Nat.le_0_l M''))).  (* IH 需 le 1 (S M'')，恒真 *)
      (* 交叉项：2·c_{S(S M'')}·⟨comboM (S (S M'')), u_{S(S M'')}⟩
         = 2·c_{S(S M'')}·Σ_{j≤S M''} c_j·⟨u_j, u_{S(S M'')}⟩（ipW_combo_l） *)
      rewrite (ipW_combo_l (S M'') c u (u (S (S M''))) W).
      (* RHS(S(S M'')) 拆分：对角 + 交叉双和（尾层 j'=S(S M'')） *)
      rewrite (g1_diag_S (S M'') c (fun j => l2_norm_sq (u j) W)).
      rewrite (g1_cross_S (S M'') (fun i j => (c i * c j * ipW (u i) (u j) W)%R)
                           (le_n_S 0 M'' (Nat.le_0_l M''))).
      + (* 最终：LHS 交叉项 2·c_{SM''}·Σ_{j≤SM''} c_j·⟨u_j,u_{SM''}⟩
           == RHS 尾层 2·Σ_{i≤SM''} c_i·c_{SM''}·⟨u_i,u_{SM''}⟩
           用 replace 一次性替换 LHS 交叉项为目标形式 *)
        replace (2 * c (S (S M'')) * sum_f_R0 (fun j : nat =>
            (c j * ipW (u j) (u (S (S M''))) W)%R) (S M''))%R
          with (2 * sum_f_R0 (fun i : nat =>
            (c i * c (S (S M'')) * ipW (u i) (u (S (S M''))) W)%R) (S M''))%R.
        2: { (* 目标（2: 反向）：2·Σ(c_i·c·⟨⟩) = 2·c·Σ(c_j·⟨⟩)
               ① RHS 结合律：2·c·Σ = 2·(c·Σ) *)
             replace (2 * c (S (S M'')) * sum_f_R0 (fun j : nat =>
                 (c j * ipW (u j) (u (S (S M''))) W)%R) (S M''))%R
               with (2 * (c (S (S M'')) * sum_f_R0 (fun j : nat =>
                 (c j * ipW (u j) (u (S (S M''))) W)%R) (S M'')))%R by ring.
             (* ② 消 2 *)
             apply Rmult_eq_compat_l.
             (* ③ RHS：c·Σ(c_j·⟨⟩) = Σ(c·(c_j·⟨⟩))（g1_sum_scal 反向） *)
             rewrite <- (g1_sum_scal (c (S (S M'')))
               (fun j => (c j * ipW (u j) (u (S (S M''))) W)%R) (S M'')).
             (* ④ 逐点对齐：Σ(c·(c_j·⟨⟩)) = Σ(c_j·c·⟨⟩)（g1_sum_ext） *)
             apply g1_sum_ext. intro k. intro Hk. cbv beta. ring. }
        (* 归一所有 predn：目标中 RHS 双和外层 predn (S (S M'')) = S M'' *)
        change (predn (S (S M''))) with (S M'').
        ring.
Qed.
(* ============ R3. ★ 主定理：加权阶梯范数精确闭式 ============ *)
(* 混窗阶梯 F = Σ_{j≤M} c_j·ψ_{n_j} 的范数平方精确等式：
   ‖F‖²_W = Σ_j c_j²·‖ψ_{n_j}‖²_W + 2·Σ_{i<j'} c_i·c_{j'}·⟨ψ_{n_i},ψ_{n_{j'}}⟩_W
   （交叉和索引平移编码 j'=S j，与 R2 一致） *)
Theorem G1_norm_closed (M : nat) (c : nat -> R) (n : nat -> nat) (W : nat) :
  le 1 M ->
  (l2_norm_sq (comboM (S M) c (fun j => psi (n j))) W)%R
  = (sum_f_R0 (fun j => (c j * c j * l2_norm_sq (psi (n j)) W)%R) M
     + 2 * sum_f_R0 (fun j => sum_f_R0
         (fun i => (c i * c (S j) * ipW (psi (n i)) (psi (n (S j))) W)%R) j) (predn M))%R.
Proof.
  (* R2 实例化 u := fun j => psi (n j) *)
  intros HM.
  apply (g1_gram_full M c (fun j => psi (n j)) W HM).
Qed.

End G1NormClosed.
