(* ============================================================
   网格阶梯正交探针（probe_grid_ortho）
   G1  grid_pair_ortho：网格原子对窗口 N 精确正交
       —— prime_character_orthogonality 的直接实例（该证明对任意 p≥2 成立，
          不用素数性；μ=0 证书的数学内核已在库中）
   G2  off_grid_ortho：公共偏移 α 在成对内积中精确相消
       —— 偏移网格同享 μ=0 证书（α 无理 ⟹ 证书保持 + 非周期，见碰撞探针 C5）
   G3  grid_ortho_mult：窗口 a·N 上正交保持（训练窗 + 全部 2^a 外推长度）

   依赖：ca_char_ortho（Cexp 机器 + prime_character_orthogonality）
         ca_independence（Csum / Csum_ext / Csum_split_rev）
   实验对应：length_extrap.py --grid N 的 theta = 2π·m/N；
             建议新增 --ogrid：theta = 2π·(β + m/N)，β 黄金比。
   ============================================================ *)
From mathcomp Require Import ssreflect ssrbool ssrnat seq eqtype div prime.
Require Import Stdlib.Reals.Reals.
Require Import Stdlib.Arith.Arith.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.micromega.Lra.
Require Import Stdlib.ZArith.ZArith.
Require Import ca_base.
Require Import ca_complex_foundation.
Require Import ca_independence.
Require Import ca_fourier.
Require Import ca_char_ortho.
Require Import ca_zeta_scaffold.
Import ComplexNumbers.
Import FourierAnalysis.

Open Scope R_scope.
Open Scope complex_scope.
Open Scope nat_scope.   (* nat 后开：mathcomp 记法优先，裸 nat 算术（0*N+i 等）不被 R 劫持；
                            R 表达式全部显式 %R 标注（见下） *)

Module GridOrtho.

(* 合并友好：本地 Csum_ext 别名（全局命名空间冲突防御）——
   ca_independence 的 Csum_ext（f g n）与 ca_basis_lemmas 的 Csum_ext（n f g）
   签名参数序不同，合并版内联后后者遮蔽前者（后定义者胜），探针独立编译（.vo
   模块边界）解析前者 → 两环境不一致。本模块内定义本地版（直接归纳，不依赖
   外部 Csum_ext 名字），两环境均解析到此处。 *)
Lemma Csum_ext : forall (f g : nat -> Complex) (n : nat),
  (forall i, (i < n)%nat -> f i = g i) -> PrimeEmbedding.Csum f n = PrimeEmbedding.Csum g n.
Proof.
  induction n as [|n IH]; intros H.
  - reflexivity.
  - simpl.
    (* 显式 assert 前提后 rewrite (IH Hn)：不依赖 rewrite 自动统一前提子目标
       （CI mathcomp 2.6 下 rewrite IH 的前提实例化环境敏感，与 CRsum_eq 同型） *)
    assert (Hn : forall i, (i < n)%nat -> f i = g i).
    { intros i Hi. apply H. exact (ltn_trans Hi (ltnSn n)). }
    rewrite (IH Hn).
    f_equal. apply H. exact (ltnSn n).
Qed.

(* ---------- 基础：纯虚指数的加法拆分 ---------- *)

Lemma i_split (x y : R) : (0 +i (x + y)) = (0 +i x) +c (0 +i y).
Proof.
  unfold Cadd. apply Complex_eq; simpl; ring.
Qed.

Lemma Cmul_middle_comm (a b c : Complex) : a *c (b *c c) = b *c (a *c c).
Proof.
  rewrite <- Cmul_assoc. rewrite (Cmul_comm a b). rewrite Cmul_assoc. reflexivity.
Qed.

Lemma Cmul_rearr (X B Y D : Complex) :
  (X *c B) *c (Y *c D) = (X *c Y) *c (B *c D).
Proof.
  rewrite (Cmul_assoc X B (Y *c D)).
  rewrite (Cmul_middle_comm B Y D).
  rewrite <- (Cmul_assoc X Y (B *c D)).
  reflexivity.
Qed.

(* ---------- 旋转原子与网格原子 ---------- *)

(* rot_atom θ k = e^{i·k·θ}：RoPE 式旋转角 θ 在位置 k 的相位 *)
Definition rot_atom (theta : R) (k : nat) : Complex :=
  Cexp (0 +i (INR k * theta)%R).

(* grid_atom N m k = e^{2πi·m·k/N}：N-网格原子（prime_character_orthogonality 口径） *)
Definition grid_atom (N m k : nat) : Complex :=
  Cexp (0 +i (2 * PI * INR (m * k) / INR N)%R).

Definition grid_pair (N m u k : nat) : Complex :=
  grid_atom N m k *c Cconj (grid_atom N u k).

(* 角度归一：INR k · (2π·m/N) = 2π·(m·k)/N *)
Lemma angle_norm (k m N : nat) :
  (2 <= N)%nat ->
  (INR k * (2 * PI * INR m / INR N))%R = (2 * PI * INR (m * k) / INR N)%R.
Proof.
  intros HN.
  assert (Hp : (0 < INR N)%R).
  { apply lt_0_INR.
    move: (ltnW HN) => /ltP HN0.
    exact HN0. }
  rewrite mult_INR.
  field.
  apply Rgt_not_eq. exact Hp.
Qed.

Lemma rot_atom_add (theta phi : R) (k : nat) :
  rot_atom ((theta + phi)%R) k = rot_atom theta k *c rot_atom phi k.
Proof.
  unfold rot_atom.
  rewrite <- Cexp_add.
  replace ((INR k * (theta + phi))%R) with (INR k * theta + INR k * phi)%R by ring.
  rewrite i_split.
  reflexivity.
Qed.

Lemma rot_atom_lag_add (theta : R) (a b : nat) :
  rot_atom theta (a + b) = rot_atom theta a *c rot_atom theta b.
Proof.
  unfold rot_atom.
  rewrite plus_INR.
  replace ((INR a + INR b) * theta)%R with ((INR a * theta + INR b * theta)%R) by ring.
  rewrite <- Cexp_add.
  rewrite <- i_split.
  reflexivity.
Qed.

Lemma rot_conj_eq_1 (theta : R) (k : nat) :
  rot_atom theta k *c Cconj (rot_atom theta k) = C1.
Proof.
  unfold rot_atom. rewrite Cconj_Cexp.
  rewrite <- Cexp_add. rewrite <- i_split.
  replace ((INR k * theta + - (INR k * theta))%R) with 0%R by ring.
  replace (0 +i 0) with C0 by reflexivity.
  rewrite Cexp_0. reflexivity.
Qed.

(* rot 形式与 p.c.o. 口径的网格原子一致 *)
Lemma rot_grid (N m k : nat) :
  (2 <= N)%nat ->
  rot_atom (2 * PI * INR m / INR N)%R k = grid_atom N m k.
Proof.
  intros HN. unfold rot_atom, grid_atom.
  rewrite (angle_norm k m N HN).
  reflexivity.
Qed.

(* ---------- G1：网格原子对窗口 N 精确正交 ----------
   口径：PrimeEmbedding.Csum（p.c.o. 原方言）。注意 ca_independence 的
   Csum_ext(:263) 亦陈述于 PE.Csum（早于其内部 Csum(:1109) 定义）。 *)
Theorem grid_pair_ortho (N m u : nat) :
  (2 <= N)%nat -> m mod N <> u mod N ->
  PrimeEmbedding.Csum (grid_pair N m u) N = C0.
Proof.
  intros HN Hneq.
  unfold grid_pair, grid_atom.
  move: HN => /leP HNle.
  apply (prime_character_orthogonality N m u); [exact HNle | exact Hneq].
Qed.

(* ---------- 偏移相消 ---------- *)

(* 步骤 1：公共偏移 α 在成对内积中精确消失（N 无关！） *)
Lemma offset_cancel (alpha theta1 theta2 : R) (k : nat) :
  rot_atom ((alpha + theta1)%R) k *c Cconj (rot_atom ((alpha + theta2)%R) k)
  = rot_atom theta1 k *c Cconj (rot_atom theta2 k).
Proof.
  rewrite (rot_atom_add alpha theta1 k) (rot_atom_add alpha theta2 k).
  rewrite Cconj_mul Cmul_rearr.
  rewrite (rot_conj_eq_1 alpha k) Cmul_1_l.
  reflexivity.
Qed.

(* 步骤 2：网格角度的 rot 形式 = p.c.o. 口径网格原子 *)
Lemma rot_pair_grid (N m u k : nat) :
  (2 <= N)%nat ->
  rot_atom (2 * PI * INR m / INR N)%R k *c Cconj (rot_atom (2 * PI * INR u / INR N)%R k)
  = grid_pair N m u k.
Proof.
  intros HN. unfold grid_pair.
  rewrite (rot_grid N m k HN) (rot_grid N u k HN).
  reflexivity.
Qed.

(* ---------- G2：偏移网格正交（α 精确相消 ⟹ μ=0 证书保持） ---------- *)

Theorem off_grid_ortho (alpha : R) (N m u : nat) :
  (2 <= N)%nat -> m mod N <> u mod N ->
  PrimeEmbedding.Csum (fun k => rot_atom (alpha + 2 * PI * INR m / INR N)%R k *c
                 Cconj (rot_atom (alpha + 2 * PI * INR u / INR N)%R k)) N = C0.
Proof.
  intros HN Hneq.
  (* 倒退解法（E114）：Csum_ext 前提显式 assert，勿让 rewrite 自动生成前提子目标
     （CI mathcomp 2.6 下 (i<n)%nat 被解析为 bool，rewrite 自动统一失败） *)
  assert (Hp : forall k : nat, (k < N)%nat ->
    (fun k => rot_atom (alpha + 2 * PI * INR m / INR N)%R k *c
              Cconj (rot_atom (alpha + 2 * PI * INR u / INR N)%R k)) k
    = grid_pair N m u k).
  { intros k Hk.
    rewrite (offset_cancel alpha (2 * PI * INR m / INR N)%R
                             (2 * PI * INR u / INR N)%R k).
    apply rot_pair_grid. exact HN. }
  rewrite (Csum_ext _ (fun k => grid_pair N m u k) N Hp).
  apply grid_pair_ortho; [exact HN | exact Hneq].
Qed.

(* ---------- G3：多窗口正交保持 ---------- *)

(* 满周期旋转 = 1 *)
Lemma rot_full_turn (N m : nat) :
  (2 <= N)%nat ->
  rot_atom (2 * PI * INR m / INR N)%R N = C1.
Proof.
  intros HN.
  assert (Hp : (0 < INR N)%R).
  { apply lt_0_INR.
    move: (ltnW HN) => /ltP HN0.
    exact HN0. }
  unfold rot_atom.
  replace ((INR N * (2 * PI * INR m / INR N))%R) with ((2 * PI * INR m)%R)
    by (field; apply Rgt_not_eq; exact Hp).
  rewrite (INR_IZR_INZ m).
  apply Cexp_2PI_int.
Qed.

(* 相对核周期性：网格对的 lag-N 平移不变 *)
Lemma grid_pair_periodic (N m u k : nat) :
  (2 <= N)%nat ->
  grid_pair N m u (N + k) = grid_pair N m u k.
Proof.
  intros HN.
  rewrite <- (rot_pair_grid N m u (N + k) HN).
  rewrite <- (rot_pair_grid N m u k HN).
  rewrite (rot_atom_lag_add (2 * PI * INR m / INR N)%R N k).
  rewrite (rot_atom_lag_add (2 * PI * INR u / INR N)%R N k).
  rewrite Cconj_mul Cmul_rearr.
  rewrite (rot_full_turn N m HN) (rot_full_turn N u HN).
  replace (Cconj C1) with C1
    by (unfold C1, Cconj; simpl; apply Complex_eq; simpl; ring).
  rewrite !Cmul_1_l.
  reflexivity.
Qed.

(* 任意整块平移 *)
Lemma grid_pair_shift_mul (N m u c i : nat) :
  (2 <= N)%nat ->
  grid_pair N m u (c * N + i) = grid_pair N m u i.
Proof.
  intros HN. induction c as [|c IH].
  - replace (0 * N + i) with i by (rewrite mul0n add0n; reflexivity). reflexivity.
  - replace (S c * N + i) with (N + (c * N + i))
      by (rewrite mulSn addnA; reflexivity).
    rewrite (grid_pair_periodic N m u (c * N + i) HN).
    exact IH.
Qed.

(* PE.Csum 的分块拆分（头部优先递归：尾块在前） *)
Lemma PE_Csum_split (f : nat -> Complex) (n m : nat) :
  PrimeEmbedding.Csum f (n + m)
  = PrimeEmbedding.Csum (fun i => f (n + i)) m +c PrimeEmbedding.Csum f n.
Proof.
  induction m as [|m IH].
  - replace (n + 0) with n by (rewrite addn0; reflexivity).
    simpl.
    symmetry. apply Cadd_0_l.
  - replace (n + S m) with (S (n + m)) by (rewrite (addnS n m) || rewrite (Nat.add_succ_r n m); reflexivity).
    simpl.
    rewrite IH.
    symmetry. apply Cadd_assoc.
Qed.

(* G3 主定理：窗口 a·N 上正交保持（a=1 训练窗；a=2,4,8 外推长度） *)
Theorem grid_ortho_mult (N a m u : nat) :
  (2 <= N)%nat -> m mod N <> u mod N ->
  PrimeEmbedding.Csum (grid_pair N m u) (a * N) = C0.
Proof.
  intros HN Hneq. induction a as [|a IH].
  - simpl. reflexivity.
  - rewrite mulSn.
    rewrite PE_Csum_split.
    (* 目标: Csum (fun i => f (N+i)) (a*N) +c Csum f N = C0
       先 Csum_ext 换函数：∀i<a*N, f(N+i)=f i（grid_pair_periodic）——前提显式 assert（E114） *)
    assert (Hper : forall i : nat, (i < a * N)%nat ->
      grid_pair N m u (N + i) = grid_pair N m u i).
    { intros i Hi. apply grid_pair_periodic. exact HN. }
    rewrite (Csum_ext (fun i => grid_pair N m u (N + i))
                      (grid_pair N m u) (a * N) Hper).
    rewrite IH.                  (* Csum f (a*N) → C0 *)
    rewrite Cadd_0_l.            (* 0 +c Csum f N = Csum f N *)
    apply grid_pair_ortho; [exact HN | exact Hneq].
Qed.

End GridOrtho.
