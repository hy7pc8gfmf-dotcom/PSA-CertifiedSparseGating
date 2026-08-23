(* ============================================================
   任意角度对 Dirichlet 界 → 混合网格跨网格相干界
   （z 工作区，E039 纪律；2026-08-22 第二批 ①）
   前置：probe_grid_ortho（rot 机器）、probe_partial（Dirichlet 主定理）。

   主定理 pair_dirichlet：任意两角度 t1 t2，若差频 t1−t2 落在
   N-网格（= 2π·j/N，j mod N ≠ 0），则任意窗口 W 上
     ‖Σ_{k<W} e^{ik·t1}·conj(e^{ik·t2})‖ ≤ INR N / (2·INR s)
     s = min(j mod N, N − j mod N)
   ——窗口无关，全部机器复用 dirichlet_partial_bound。

   推论 mixed_grid_coherence：嵌套网格 N 与 a·N 上的两原子
   （grid_atom N m1 与 grid_atom (a*N) m2），差频 = j/(a·N) 时
   跨网格相干 ≤ INR (a·N) / (2·INR s)。grid 崩塌后"多尺度网格
   设计空间"的核心定量工具。
   ============================================================ *)
From mathcomp Require Import ssreflect ssrbool ssrnat seq eqtype div prime.
Require Import Stdlib.Reals.Reals.
Require Import Stdlib.Arith.Arith.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.micromega.Lra.
Require Import Stdlib.ZArith.ZArith.
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
Import ComplexNumbers.
Import FourierAnalysis.
Import GridOrtho.
Import TPartial.

Open Scope R_scope.
Open Scope complex_scope.
Open Scope nat_scope.

Module PairDirichlet.

(* conj 的旋转原子形式 *)
Lemma rot_conj_rot (theta : R) (k : nat) : Cconj (rot_atom theta k) = rot_atom (- theta) k.
Proof.
  unfold rot_atom. rewrite Cconj_Cexp.
  replace ((INR k * - theta))%R with (- (INR k * theta))%R by ring.
  reflexivity.
Qed.

(* 旋转原子乘法 → 和角原子 *)
Lemma rot_mul_rot (a b : R) (k : nat) :
  rot_atom a k *c rot_atom b k = rot_atom (a + b) k.
Proof.
  unfold rot_atom. rewrite <- Cexp_add, <- i_split.
  replace ((INR k * (a + b)))%R with ((INR k * a) + (INR k * b))%R by ring.
  reflexivity.
Qed.

(* 乘积对 = 差频原子（核心步） *)
Lemma pair_eq_rotdiff (t1 t2 : R) (k : nat) :
  rot_atom t1 k *c Cconj (rot_atom t2 k) = rot_atom (t1 - t2) k.
Proof. rewrite rot_conj_rot rot_mul_rot. reflexivity. Qed.

(* ---------- 主定理 ---------- *)

Theorem pair_dirichlet (N j W : nat) (t1 t2 : R) :
  (2 <= N)%nat -> (j mod N <> 0)%nat ->
  ((t1 - t2) = (2 * PI * INR j / INR N))%R ->
  ((Cnorm (PrimeEmbedding.Csum
      (fun k => rot_atom t1 k *c Cconj (rot_atom t2 k)) W)
    <= INR N / (2 * INR (Nat.min (j mod N) (N - j mod N))))%R).
Proof.
  intros HN Hneq Hdiff.
  assert (Hconv : PrimeEmbedding.Csum
             (fun k => rot_atom t1 k *c Cconj (rot_atom t2 k)) W
             = PrimeEmbedding.Csum (fun k => grid_atom N j k) W).
  { apply Csum_ext. intros k Hk.
    rewrite pair_eq_rotdiff Hdiff.
    rewrite (rot_grid N j k HN). reflexivity. }
  rewrite Hconv.
  apply dirichlet_partial_bound; [exact HN | exact Hneq].
Qed.

(* ---------- 混合网格推论 ---------- *)

Theorem mixed_grid_coherence (N a m1 m2 W j : nat) :
  (2 <= N)%nat -> (0 < a)%nat -> (j mod (a * N) <> 0)%nat ->
  ((INR m1 / INR N - INR m2 / INR (a * N)) = (INR j / INR (a * N)))%R ->
  ((Cnorm (PrimeEmbedding.Csum
      (fun k => grid_atom N m1 k *c Cconj (grid_atom (a * N) m2 k)) W)
    <= INR (a * N)
       / (2 * INR (Nat.min (j mod (a * N)) (a * N - j mod (a * N))))))%R.
Proof.
  intros HN Ha Hneq Hdiff.
  assert (Hconv : PrimeEmbedding.Csum
             (fun k => grid_atom N m1 k *c Cconj (grid_atom (a * N) m2 k)) W
             = PrimeEmbedding.Csum
                 (fun k => rot_atom (2 * PI * INR m1 / INR N) k
                           *c Cconj (rot_atom (2 * PI * INR m2 / INR (a * N)) k)) W).
  { apply Csum_ext. intros k Hk.
    rewrite (rot_grid N m1 k HN).
    rewrite (rot_grid (a * N) m2 k); [reflexivity | exact (leq_mul Ha HN)]. }
  rewrite Hconv.
  assert (HNz : (0 < INR N)%R) by (apply lt_0_INR; move: HN => /ltP HNp; lia).
  assert (HANz : (0 < INR (a * N))%R)
    by (apply lt_0_INR; apply/ltP;
        apply (leq_trans (n := 2));
        [ exact (ltnW (ltnSn 1)) | exact (leq_mul Ha HN) ]).
  assert (Heq : ((2 * PI * INR m1 / INR N - 2 * PI * INR m2 / INR (a * N))
                 = (2 * PI * INR j / INR (a * N)))%R).
  { replace ((2 * PI * INR j / INR (a * N)))%R
      with ((2 * PI) * (INR j / INR (a * N)))%R by (field; lra).
    replace ((2 * PI * INR m1 / INR N))%R
      with ((2 * PI) * (INR m1 / INR N))%R by (field; lra).
    replace ((2 * PI * INR m2 / INR (a * N)))%R
      with ((2 * PI) * (INR m2 / INR (a * N)))%R by (field; lra).
    rewrite <- Hdiff. ring. }
  apply (pair_dirichlet (a * N) j W
           (2 * PI * INR m1 / INR N) (2 * PI * INR m2 / INR (a * N)));
    [ exact (leq_mul Ha HN) | exact Hneq | exact Heq ].
Qed.

End PairDirichlet.

(* ---------- 构造性审计 ---------- *)

Print Assumptions PairDirichlet.pair_dirichlet.
Print Assumptions PairDirichlet.mixed_grid_coherence.
