(* ============================================================
   T4（G-12）：μ=0 正交家族完备性（⟹ 方向）——probe_g12_orthofam.v
   终态（2026-09-02）：零 Admitted——g12_ortho_witness（S1–S3 核心引擎）
   与 g12_ortho_family（S4 完备性合成）双 Qed，编译 EXIT=0。
   公理脚印 = Dedekind 三件套（ClassicalDedekindReals.sig_not_dec /
   sig_forall_dec + FunctionalExtensionality_dep），与姊妹探针
   probe_grid_ortho（⟸ 方向 off_grid_ortho/grid_pair_ortho）及
   probe_collision kernel_collides_iff 引擎完全一致——该三件套是本库
   R 基建（ClassicalDedekindReals 系）的固有脚印，凡涉 R 定理必有
   （实测连 Rmult_1_l 亦携带）；无 classic、无 IndefiniteDescription。
   可归档/入合并版（合并 = 剔除 Require 后同一份文件——「探针即终态」）。

   论文 A §14 limitation：「μ=0 家族目前只证 ⟸ 方向（grid_ortho/off_grid_ortho：
   公共偏移 + N-网格互异 ⟹ 两两正交）」。本模块补 ⟹ 方向：
     窗 N 内两两正交 ⟹ ∃θ₀ + 互异整数网格
       （θ_t = θ₀ + 2π·j_t/N，j_t mod N 互异）
   ——「不存在第三种正交家族」（设计空间被 (N, {j_t}, θ₀) 完全参数化）。

   数学链（四步，详见考古四轮报告 §4b）：
     S1 正交 ⟹ 几何和零：win_ip = Σ_{k<N} conj(e^{ik·θ1})·e^{ik·θ2}
        = Σ_{k<N} e^{ik·(θ2−θ1)}（g12_step 逐项改写 + g12_csum_ext）
     S2 几何和望远镜（g12_telescope，ca_basis Csum_geometric_aux 同型）：
        (1−ω)·Σ_{k<N}ω^k = 1−ω^N ⟹ 和零直接给 ω^N = C1
        （无需先验 ω ≠ 1——望远镜恒等式对 ω=1 也成立）
     S3 幂一 ⟹ 代数见证：Cexp_eq_1_iff（ca_char_ortho，kernel_collides_iff
        同型引擎）proj2 ⟹ ∃k:Z, INR N·(θ2−θ1) = 2π·IZR k（绕 cos 注入性）
     S4 取 θ₀ := nth 0 ths 0，逐对 S3 ⟹ ∀t: INR N·(θ_t−θ₀) = 2π·j_t；
        mod-N 互异反证：j_s ≡ j_t (mod N) ⟹ θ_s−θ_t = 2π·m
        ⟹ 逐项原子全为 1 ⟹ 内积和 = INR N ≠ 0，与正交性矛盾
        （g12_zmod_diff + g12_rot_2pi + g12_csum_C1）

   Pass 1 陈述验型修正（2026-09-02，不改定理语义）：
     ① grid_witness 删除体内未使用的 d 参数（原 L62 定义与 L71 调用
        类型不匹配：d : R 收到 nat——框架先行工作流预期修正）；
     ② mod-N 互异条件由病态的 (… mod IZR N …)%R 改为整数口径
        (nth s js 0%Z mod Z.of_nat N ≠ …)%Z——Stdlib Reals 无 R-modulo
        记号（mod 仅 nat/Z 解释，原写法必然验型失败），Z 口径即头注
        「j_t mod N 互异」的原意。

   轨道：经典 R（grid_ortho/tchar 同生态；构造性孪生需 CR 三角注入基建，
   后置——两轨政策同 g3/g5 先例）。
   依赖：Reals + ca_complex_foundation（Cexp/Cadd/Cmul/*c）+
   ca_char_ortho 引擎（Cexp_eq_1_iff / Cexp_2PI_int / Cconj_Cexp）+
   ca_zeta_scaffold（PrimeEmbedding.Csum）。
   合并友好：本文件全部自建引理加 g12_ 前缀防合并版同名遮蔽（E138
   同款防御）；Csum 和式操作一律本地重建于 PrimeEmbedding.Csum 上，
   不依赖 ca_basis/ca_independence 的 Csum 短名（两环境解析一致）。
   ============================================================ *)

Require Import Stdlib.Reals.Reals.
Require Import Stdlib.Lists.List.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.micromega.Lra.
Import ListNotations.
Local Open Scope R_scope.

(* 复数库引入（与 grid_ortho 对齐——项目自身 ca_complex_foundation 体系） *)
Require Import ca_base.
Require Import ca_complex_foundation.
Require Import ca_independence.
Require Import ca_fourier.
Require Import ca_char_ortho.
Require Import ca_zeta_scaffold.
Import ComplexNumbers.
Import FourierAnalysis.

(* 窗口旋转原子（grid_ortho 同款） *)
Definition g12_rot_atom (theta : R) (k : nat) : Complex :=
  Cexp (0 +i (INR k * theta)%R).

(* 窗口内积：Σ_{k<N} conj(u_i k) · u_j k（PrimeEmbedding.Csum 口径） *)
Definition win_ip (N : nat) (ui uj : nat -> Complex) : Complex :=
  PrimeEmbedding.Csum (fun k => Cconj (ui k) *c uj k) N.

(* T1b 正交条件：窗 N 内逐对正交（i ≠ j ⟹ 内积 = 0） *)
Definition t1b_ortho (N : nat) (ths : list R) : Prop :=
  forall i j, (i < length ths)%nat -> (j < length ths)%nat -> i <> j ->
    win_ip N (g12_rot_atom (nth i ths 0)) (g12_rot_atom (nth j ths 0)) = C0.

(* S3 代数见证（kernel_collides_iff 同型引擎）
   （Pass 1 验型修正 ①：删除体内未使用的 d 参数——2026-09-02） *)
Definition grid_witness (N : nat) (th1 th2 : R) : Prop :=
  exists k : Z, (INR N * (th2 - th1))%R = (2 * PI * IZR k)%R.

(* ============ g12 自建零件（局部引理，唯一命名空间） ============ *)

(* 纯虚指数的加法拆分（probe_grid_ortho i_split 同款） *)
Lemma g12_i_split (x y : R) : (0 +i (x + y)) = (0 +i x) +c (0 +i y).
Proof.
  unfold Cadd. apply Complex_eq; simpl; ring.
Qed.

(* 旋转原子的 lag 可加性：e^{i(a+b)θ} = e^{ia·θ}·e^{ib·θ} *)
Lemma g12_rot_lag (d : R) (a b : nat) :
  g12_rot_atom d (a + b) = g12_rot_atom d a *c g12_rot_atom d b.
Proof.
  unfold g12_rot_atom.
  rewrite plus_INR.
  replace ((INR a + INR b) * d)%R with (INR a * d + INR b * d)%R by ring.
  rewrite <- Cexp_add.
  rewrite <- g12_i_split.
  reflexivity.
Qed.

(* 零频原子 = 1 *)
Lemma g12_rot_0 (d : R) : g12_rot_atom d 0 = C1.
Proof.
  unfold g12_rot_atom.
  replace (INR 0 * d)%R with 0%R by (rewrite INR_0; ring).
  replace (0 +i 0) with C0 by reflexivity.
  apply Cexp_0.
Qed.

(* 单步原子 = 1·ω^k = ω^{k+1}（几何和望远镜的推进齿轮） *)
Lemma g12_rot_S (d : R) (n : nat) : g12_rot_atom d 1 *c g12_rot_atom d n = g12_rot_atom d (S n).
Proof.
  replace (S n) with (n + 1)%nat by lia.
  rewrite g12_rot_lag. apply Cmul_comm.
Qed.

(* S1 步：正交对逐项化成频差原子
   conj(e^{ik·θ1})·e^{ik·θ2} = e^{ik·(θ2−θ1)}（offset_cancel 零件同型，α=0 特例） *)
Lemma g12_step (th1 th2 : R) (k : nat) :
  Cconj (g12_rot_atom th1 k) *c g12_rot_atom th2 k = g12_rot_atom (th2 - th1) k.
Proof.
  unfold g12_rot_atom.
  rewrite Cconj_Cexp.
  rewrite <- Cexp_add.
  rewrite <- g12_i_split.
  replace (-(INR k * th1) + INR k * th2)%R with (INR k * (th2 - th1))%R by ring.
  reflexivity.
Qed.

(* 复数右分配：减法·乘（本地版，规避库内 Cmul_sub_distr_r 参数序歧义） *)
Lemma g12_msdr (a b c : Complex) : (a -c b) *c c = a *c c -c b *c c.
Proof.
  destruct a as [a1 a2]; destruct b as [b1 b2]; destruct c as [c1 c2].
  apply Complex_eq; simpl; ring.
Qed.

(* 复数缩并恒等式：(a−b) + (c−a) = c − b（望远镜收尾步） *)
Lemma g12_cs3 (a b c : Complex) : (a -c b) +c (c -c a) = c -c b.
Proof.
  destruct a as [a1 a2]; destruct b as [b1 b2]; destruct c as [c1 c2].
  apply Complex_eq; simpl; ring.
Qed.

(* 减法零消去：a − b = 0 ⟹ b = a *)
Lemma g12_sub_eq0 (a b : Complex) : a -c b = C0 -> b = a.
Proof.
  intros H.
  destruct a as [a1 a2]; destruct b as [b1 b2].
  unfold Csub, C0 in H. simpl in H.
  injection H as H1 H2.
  apply Complex_eq; simpl; lra.
Qed.

(* PE.Csum 有限和逐项相等（probe_grid_ortho 本地 Csum_ext 同款——
   不依赖 ca_independence/ca_basis 的 Csum_ext 短名，合并版两环境一致） *)
Lemma g12_csum_ext : forall (f g : nat -> Complex) (n : nat),
  (forall i, (i < n)%nat -> f i = g i) ->
  PrimeEmbedding.Csum f n = PrimeEmbedding.Csum g n.
Proof.
  intros f g n. induction n as [|n IH]; intros H.
  - reflexivity.
  - replace (PrimeEmbedding.Csum f (S n))
      with (Cadd (f n) (PrimeEmbedding.Csum f n)) by reflexivity.
    replace (PrimeEmbedding.Csum g (S n))
      with (Cadd (g n) (PrimeEmbedding.Csum g n)) by reflexivity.
    assert (Hn : forall i, (i < n)%nat -> f i = g i) by (intros i Hi; apply H; lia).
    assert (Hnn : f n = g n) by (apply H; lia).
    rewrite Hnn, (IH Hn). reflexivity.
Qed.

(* 全 1 求和 = 标量（恒等原子列的内积和） *)
Lemma g12_csum_C1 : forall N : nat,
  PrimeEmbedding.Csum (fun _ : nat => C1) N = (INR N +i 0)%R.
Proof.
  induction N as [|N IH].
  - reflexivity.
  - replace (PrimeEmbedding.Csum (fun _ : nat => C1) (S N))
      with (Cadd C1 (PrimeEmbedding.Csum (fun _ : nat => C1) N)) by reflexivity.
    rewrite IH.
    replace (INR (S N))%R with (INR N + 1)%R by (rewrite S_INR; ring).
    apply Complex_eq; simpl; ring.
Qed.

(* S2 核心几何和望远镜（ca_basis Csum_geometric_aux 同型，PE.Csum 口径，
   且无 z ≠ 1 前提——(1−ω)·Σω^k = 1−ω^N 对 ω = 1 也成立） *)
Lemma g12_telescope : forall (d : R) (N : nat),
  (C1 -c g12_rot_atom d 1) *c PrimeEmbedding.Csum (fun k => g12_rot_atom d k) N
  = C1 -c g12_rot_atom d N.
Proof.
  intros d N. induction N as [|N IH].
  - replace (PrimeEmbedding.Csum (fun k => g12_rot_atom d k) 0) with C0 by reflexivity.
    replace (g12_rot_atom d 0) with C1 by (symmetry; apply g12_rot_0).
    rewrite Cmul_0_r. symmetry. apply Csub_self.
  - replace (PrimeEmbedding.Csum (fun k => g12_rot_atom d k) (S N))
      with (Cadd (g12_rot_atom d N) (PrimeEmbedding.Csum (fun k => g12_rot_atom d k) N))
      by reflexivity.
    rewrite Cmul_add_distr_l, IH, g12_msdr, Cmul_1_l, g12_rot_S.
    apply g12_cs3.
Qed.

(* INR k·IZR m = IZR(k·m)（Rocq 9 名：mult_IZR） *)
Lemma g12_INR_IZR (k : nat) (m : Z) : (INR k * IZR m)%R = IZR (Z.of_nat k * m).
Proof.
  rewrite INR_IZR_INZ. symmetry. apply mult_IZR.
Qed.

(* IZR 对取反的分配（probe_tchar IZR_opp 同款） *)
Lemma g12_IZR_opp (z : Z) : (IZR (Z.opp z))%R = (- (IZR z))%R.
Proof.
  destruct z as [| p | p].
  - replace (IZR (Z.opp 0))%R with 0%R by reflexivity.
    replace (IZR 0)%R with 0%R by reflexivity.
    rewrite Ropp_0. reflexivity.
  - reflexivity.
  - change (IZR (Z.neg p)) with (- (IZR (Z.pos p)))%R.
    rewrite Ropp_involutive. reflexivity.
Qed.

Lemma g12_IZR_0 : (IZR 0)%R = 0%R.
Proof. reflexivity. Qed.

(* 2π·整数倍频差原子恒为 1（grid_full_turn 零件的一般整数版） *)
Lemma g12_rot_2pi (m : Z) (k : nat) : g12_rot_atom (2 * PI * IZR m)%R k = C1.
Proof.
  unfold g12_rot_atom.
  replace (INR k * (2 * PI * IZR m))%R with ((2 * PI) * (INR k * IZR m))%R by ring.
  rewrite g12_INR_IZR.
  apply Cexp_2PI_int.
Qed.

(* Z 口径 mod 同余提取：a mod n = b mod n ⟹ ∃m, a = b + n·m *)
Lemma g12_zmod_diff (a b n : Z) : n <> 0%Z ->
  (a mod n = b mod n)%Z -> exists m : Z, (a = b + n * m)%Z.
Proof.
  intros Hn Hmod.
  pose proof (Z.div_mod a n Hn) as Ha.
  pose proof (Z.div_mod b n Hn) as Hb.
  rewrite Hmod in Ha.
  exists (a / n - b / n)%Z.
  replace (n * (a / n - b / n))%Z with (n * (a / n) - n * (b / n))%Z by ring.
  lia.
Qed.

(* S4 见证列表构造：逐位置整数见证 ⟹ 同长列表 js（逐点 nth 读出） *)
Lemma g12_build_js : forall (N : nat) (theta0 : R) (ths : list R),
  (forall t, (t < length ths)%nat ->
     exists k : Z, (INR N * (nth t ths 0 - theta0))%R = (2 * PI * IZR k)%R) ->
  exists js : list Z,
    length js = length ths /\
    (forall t, (t < length ths)%nat ->
      (INR N * (nth t ths 0 - theta0))%R = (2 * PI * IZR (nth t js 0%Z))%R).
Proof.
  intros N theta0 ths.
  induction ths as [| th tl IH]; intros Hw.
  - exists []. split; [reflexivity | ].
    intros t Ht. simpl in Ht. exfalso. lia.
  - assert (Hk0 : exists k : Z,
      (INR N * (nth 0 (th :: tl) 0 - theta0))%R = (2 * PI * IZR k)%R)
      by (apply Hw; simpl; lia).
    destruct Hk0 as [k0 Hk0].
    assert (Hwtl : forall t, (t < length tl)%nat ->
      exists k : Z, (INR N * (nth t tl 0 - theta0))%R = (2 * PI * IZR k)%R).
    { intros t Ht. apply (Hw (S t)). simpl. lia. }
    destruct (IH Hwtl) as [js' [Hl' Hp']].
    exists (k0 :: js'). split.
    + simpl. rewrite Hl'. reflexivity.
    + intros t Ht. destruct t as [| t'].
      * exact Hk0.
      * apply (Hp' t'). simpl in Ht. lia.
Qed.

(* ============ S1+S2+S3：核心引理（2026-09-02 闭合） ============ *)

(* 几何和零的代数见证：
   窗 N 内旋转原子正交 ⟹ 频差 δ = θ_j−θ_i 的 N 倍是 2π 的整数倍
   （HN 在证明中未用到：望远镜恒等式覆盖 ω=1 情形，非退化性仅
   S4 消矛盾时需要——陈述保留 HN 以维持 Pass 1 签名） *)
Lemma g12_ortho_witness : forall (N : nat) (th1 th2 : R), (2 <= N)%nat ->
  win_ip N (g12_rot_atom th1) (g12_rot_atom th2) = C0 ->
  grid_witness N th1 th2.
Proof.
  intros N th1 th2 HN Hortho.
  (* S1：win_ip 逐项改写为频差原子列之和 *)
  unfold win_ip in Hortho.
  rewrite (g12_csum_ext (fun k => Cconj (g12_rot_atom th1 k) *c g12_rot_atom th2 k)
                        (fun k => g12_rot_atom (th2 - th1) k) N
           (fun k (_ : (k < N)%nat) => g12_step th1 th2 k)) in Hortho.
  (* S2：望远镜 (1−ω)·Σ = 1−ω^N，和零 ⟹ ω^N = C1 *)
  pose proof (g12_telescope (th2 - th1) N) as Htel.
  rewrite Hortho in Htel.
  rewrite Cmul_0_r in Htel.
  symmetry in Htel.
  apply g12_sub_eq0 in Htel.
  (* S3：Cexp_eq_1_iff proj2 ⟹ ∃k:Z 代数见证（绕 cos 注入性） *)
  unfold g12_rot_atom in Htel.
  destruct (proj2 (Cexp_eq_1_iff (INR N * (th2 - th1))%R) Htel) as [k Hk].
  unfold grid_witness. exists k. exact Hk.
Qed.

(* ============ S4：完备性合成（2026-09-02 闭合） ============ *)

(* 主定理：窗 N 内两两正交 ⟹ ∃θ₀ + 互异整数偏移
   （θ_t = θ₀ + 2π·j_t/N，j_t mod N 互异）
   Pass 1 验型修正 ②：mod-N 互异取整数口径（见文件头注记）。 *)
Theorem g12_ortho_family : forall (N : nat) (ths : list R), (2 <= N)%nat ->
  (2 <= length ths)%nat ->
  t1b_ortho N ths ->
  exists (theta0 : R) (js : list Z),
    length js = length ths /\
    (forall t, (t < length ths)%nat ->
      (INR N * (nth t ths 0 - theta0))%R = (2 * PI * IZR (nth t js 0%Z))%R) /\
    (forall s t, (s < length ths)%nat -> (t < length ths)%nat -> s <> t ->
      (nth s js 0%Z mod Z.of_nat N <> nth t js 0%Z mod Z.of_nat N)%Z).
Proof.
  intros N ths HN Hlen Hortho.
  unfold t1b_ortho in Hortho.
  assert (H0lt : (0 < length ths)%nat) by lia.
  (* 逐位置整数见证（t = 0 平凡取 k=0；t ≠ 0 用 S3 引擎） *)
  assert (Hw : forall t, (t < length ths)%nat ->
     exists k : Z, (INR N * (nth t ths 0 - nth 0 ths 0))%R = (2 * PI * IZR k)%R).
  { intros t Ht. destruct t as [| t'].
    - exists 0%Z.
      replace (nth 0 ths 0 - nth 0 ths 0)%R with 0%R by ring.
      replace (2 * PI * IZR 0)%R with (2 * PI * 0)%R by reflexivity.
      ring.
    - assert (Hne : (0 <> S t')%nat) by discriminate.
      exact (g12_ortho_witness N (nth 0 ths 0) (nth (S t') ths 0) HN
               (Hortho 0%nat (S t') H0lt Ht Hne)). }
  destruct (g12_build_js N (nth 0 ths 0) ths Hw) as [js [Hlenjs Hjs]].
  exists (nth 0 ths 0), js.
  split; [exact Hlenjs | split; [exact Hjs | ]].
  (* mod-N 互异反证：j_s ≡ j_t (mod N) ⟹ θ_s = θ_t ⟹ 和 = INR N ≠ 0 *)
  intros s t Hs Ht Hne Hmod.
  assert (HnZ : Z.of_nat N <> 0%Z).
  { destruct N as [| N']; [simpl in HN; lia | intro c; discriminate c]. }
  destruct (g12_zmod_diff (nth s js 0%Z) (nth t js 0%Z) (Z.of_nat N) HnZ Hmod) as [m Hm].
  assert (HIN : (INR N = IZR (Z.of_nat N))%R) by apply INR_IZR_INZ.
  assert (Hp : (0 < INR N)%R) by (apply lt_0_INR; lia).
  assert (HZsub : (IZR (nth s js 0%Z) - IZR (nth t js 0%Z))%R
                = (IZR (Z.of_nat N) * IZR m)%R).
  { rewrite Hm. rewrite <- minus_IZR.
    replace ((nth t js 0%Z + Z.of_nat N * m) - nth t js 0%Z)%Z
      with (Z.of_nat N * m)%Z by lia.
    apply mult_IZR. }
  assert (Hcomb2 : (INR N * (nth s ths 0 - nth t ths 0))%R
                 = (2 * PI * (IZR (nth s js 0%Z) - IZR (nth t js 0%Z)))%R).
  { replace (INR N * (nth s ths 0 - nth t ths 0))%R
      with (INR N * (nth s ths 0 - nth 0 ths 0)
            - INR N * (nth t ths 0 - nth 0 ths 0))%R by ring.
    rewrite (Hjs s Hs), (Hjs t Ht). ring. }
  rewrite HZsub, HIN in Hcomb2.
  replace (2 * PI * (IZR (Z.of_nat N) * IZR m))%R
    with (IZR (Z.of_nat N) * (2 * PI * IZR m))%R in Hcomb2 by ring.
  assert (Hnz : (IZR (Z.of_nat N) <> 0)%R)
    by (rewrite <- HIN; apply Rgt_not_eq; exact Hp).
  assert (Hd : (nth s ths 0 - nth t ths 0)%R = (2 * PI * IZR m)%R).
  { exact (Rmult_eq_reg_l (IZR (Z.of_nat N)) (nth s ths 0 - nth t ths 0)
             (2 * PI * IZR m)%R Hcomb2 Hnz). }
  assert (Hopp : (nth t ths 0 - nth s ths 0)%R = (2 * PI * IZR (Z.opp m))%R).
  { replace (2 * PI * IZR (Z.opp m))%R with (- (2 * PI * IZR m))%R
      by (rewrite g12_IZR_opp; ring).
    rewrite <- Hd. ring. }
  assert (Hall : forall k : nat, g12_rot_atom (nth t ths 0 - nth s ths 0) k = C1).
  { intros k. rewrite Hopp. apply g12_rot_2pi. }
  specialize (Hortho s t Hs Ht Hne).
  unfold win_ip in Hortho.
  rewrite (g12_csum_ext (fun k => Cconj (g12_rot_atom (nth s ths 0) k) *c g12_rot_atom (nth t ths 0) k)
                        (fun k => g12_rot_atom (nth t ths 0 - nth s ths 0) k) N
           (fun k (_ : (k < N)%nat) => g12_step (nth s ths 0) (nth t ths 0) k)) in Hortho.
  rewrite (g12_csum_ext (fun k => g12_rot_atom (nth t ths 0 - nth s ths 0) k)
                        (fun _ : nat => C1) N
           (fun k (_ : (k < N)%nat) => Hall k)) in Hortho.
  rewrite g12_csum_C1 in Hortho.
  unfold C0 in Hortho. injection Hortho as Hre.
  lra.
Qed.

(* ============ 审计 ============ *)
Print Assumptions g12_ortho_witness.
Print Assumptions g12_ortho_family.
