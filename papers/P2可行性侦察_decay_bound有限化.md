# P2 可行性侦察：外部守卫路线（decay_bound 有限化）

> 侦察对象：ca_decay.v 的 `decay_bound`（:1572）/ `decay_bound_i_lt_j`（:1284）/
> `decay_bound_i_lt_j_one_factor`（:1442）及其支撑引理。
> 问题：decay_bound 的 growth 前提是**全函数** `forall i, INR (seq (S i)) > INR C * INR (seq i)`，
> 而运行时守卫只验证有限索引列表 I 内相邻对。外部守卫路线能否成立？
> 日期：2026-08-18 会话 3。结论：**可行，但必须 PSA 层重述（finite restatement），不能直接实例化**。
>
> **实现状态：✅ 已完成（同会话）**——`psa_guard_decay` 及其全部辅助引理已在
> `PSA_framework.v` 中 Qed（RC=0），公理 = sig_not_dec+sig_forall_dec+fext（继承库内衰减定理，
> **零 classic**）。实测公理明细见文末「实现结果」。

---

## 一、结论

**可行**。decay_bound 的全局前提在证明中**只被用于 I 元素链上的相邻对**，从未用于非 I 位置的
seq 值。将全局前提换成两个有限前提后，证明可镜像重述：

1. `forall k, (S k < length I)%nat -> INR (seq (nth (S k) I)) > INR C * INR (seq (nth k I))`
   （I 内**相邻元素**的 R 级增长——正是守卫 `check_sparse_growth (map seq I) C` 验证的对象）
2. `forall i, (i < length I)%nat -> (seq (nth i I) >= 2)%nat`
   （I 元素的 seq 值 ≥2——正是守卫 `all_ge_2 (map seq I)` 验证的对象）

外加已有的 `Sorted Nat.lt I`、`NoDup I`、`C >= 2`。

---

## 二、依赖图（decay_bound 的全局前提在每个使用点的角色）

`decay_bound`（:1572）→ `decay_bound_i_lt_j_one_factor`（:1442，i<j 情形；j<i 用
`Cnorm_Csum_conj_sym` 对称化，无需额外处理）。

`one_factor` 中全局前提的**全部**使用点：

| # | 使用点 | 位置 | 库内实现 | 对全局前提的依赖 | 替代方案 |
|---|--------|------|---------|----------------|---------|
| 1a | `Hn1_lt_n2 : seq (nth i I) < seq (nth j I)` | :1458 | `seq_strict_growth_lt`（:959，经 `seq_exp_growth` **值距离链**） | 值距离链经过非 I 位置 | **I 元素链**：相邻 I 元素严格增（C≥2 ⟹ x < C·x < next）⟹ 任意 I 元素对严格增 |
| 1b | `seq a < seq (max I)`（截断用） | :1462-1471 | `Csum_psi_conj_truncate_by_upper_bound` 的 Hstrict | 同上 | 同 1a：a 与 max I 均在 I（max I ∈ I），链覆盖 |
| 2 | `INR n2 >= INR C^(j-i) · INR n1` | :1495 | `sparse_index_growth`（:1233，经 `seq_exp_growth` 值距离链 + `nth_diff_ge_index_diff`） | 值距离链 | **I 元素链复合**：`x_{k+1} > C·x_k` 逐乘 ⟹ `x_j > C^(j-i)·x_i`，指数 = 索引距离 j-i（恰为守卫覆盖的步数） |
| 3 | `n1 >= 2`, `n2 >= 2` | :1459-1460 | `Hseq_ge2` | 只在 I 元素位置使用 | all_ge_2 (map seq I) |
| 4 | `sqrt_div_bound`（:830）| :1500 | 前提 `C>=2, d>=1, INR n2 >= INR C^d·INR n1` | **不依赖全局**（不接触 seq） | 直接复用 |
| 5 | `sparse_sqrt_inv_bound`（:1154）| :1503 | 前提 `C>=2, n1>=2, d>=1, 同 4` | **不依赖全局** | 直接复用 |
| 6 | `inner_product_norm_bound_general_n`（:1068）| :1487 | 前提 `n1>=2, n2>=2, n1<n2` | **不依赖全局** | 直接复用 |
| 7 | `nth_sorted_strict_lt`（:1111）| :1455 | `nth i I < nth j I`（Sorted） | 无 | 库内已有，复用 |

**关键事实**：`sparse_index_growth` 的结论（指数 = 索引距离）本可用**索引链**证明，库内选择用
值距离链（seq_exp_growth）只是实现选择，非本质。守卫验证的恰是索引链的每一步。

---

## 三、PSA 层辅助引理（全部零公理，需新证）

```coq
(* 1. I 链严格增：相邻 I 元素 R 级增长 + C>=2 ⟹ 任意 I 元素对严格增 *)
Lemma I_chain_strict (seq : nat -> nat) (I : list nat) (C : nat) :
  (C >= 2)%nat -> Sorted Nat.lt I ->
  (forall k, (S k < length I)%nat ->
     (INR (seq (nth (S k) I 0%nat)) > INR C * INR (seq (nth k I 0%nat)))%R) ->
  forall i j, (i < j)%nat -> (j < length I)%nat ->
    (seq (nth i I 0%nat) < seq (nth j I 0%nat))%nat.
(* 证：对 j-i 归纳；每步 nth i < nth (S i)（R 级 > ⟹ lt_INR ⟹ 用 x <= C*x < next，C>=2）*)

(* 2. I 链复合增长：相邻 ⟹ 任意对的指数界（指数 = 索引距离） *)
Lemma I_chain_compound (seq : nat -> nat) (I : list nat) (C : nat) :
  (C >= 2)%nat ->
  (forall k, (S k < length I)%nat ->
     (INR (seq (nth (S k) I 0%nat)) > INR C * INR (seq (nth k I 0%nat)))%R) ->
  forall i j, (i < j)%nat -> (j < length I)%nat ->
    (INR (seq (nth j I 0%nat)) >= (INR C) ^ (j - i) * INR (seq (nth i I 0%nat)))%R.
(* 证：对链归纳，逐乘（x_{k+1} > C·x_k ⟹ x_j > C^d·x_i），指数累加为 j-i *)

(* 3. max 是元素：max I ∈ I（截断链终点用） *)
Lemma fold_right_max_In (I : list nat) :
  exists m, (m < length I)%nat /\ nth m I 0%nat = fold_right Nat.max 0%nat I.
(* 证：对 I 归纳；stdlib 或有现成引理可查 *)

(* 4. 截断实例：seq a < seq (max I) ⟹ Csum 可截到 seq a（用 psi_ge_n_zero + Csum_trunc_tail） *)
(*    —— one_factor 里 Csum_psi_conj_truncate_by_upper_bound 的实例化，用 1+2 重述 *)
```

## 四、桥梁引理（守卫 → 有限前提，零公理）

```coq
(* 守卫的相邻布尔 ⟹ I 相邻 R 级增长（无需 Sorted！forallb_adjacent_nth 无 Sorted 前提） *)
Lemma guard_adjacent_growth (seq : nat -> nat) (I : list nat) (C : nat) :
  check_sparse_growth (map seq I) C = true ->
  forall k, (S k < length I)%nat ->
    (INR (seq (nth (S k) I 0%nat)) > INR C * INR (seq (nth k I 0%nat)))%R.
(* 证：forallb_adjacent_nth（已证，零公理）⟹ 相邻布尔 ⟹ Nat.ltb_lt + lt_INR + mult_INR
       + H_nth_map（nth (S k) (map seq I) 0 = seq (nth (S k) I 0)）+ length_map *)

(* 守卫的 all_ge_2 ⟹ I 元素值 >= 2 *)
Lemma guard_ge2_map (seq : nat -> nat) (I : list nat) :
  all_ge_2 (map seq I) = true ->
  forall i, (i < length I)%nat -> (seq (nth i I 0%nat) >= 2)%nat.
(* 证：all_ge_2P + nth_In + H_nth_map *)
```

## 五、目标定理（P2 核心，替换 doc 第三步的 Admitted）

```coq
Theorem psa_guard_decay (seq : nat -> nat) (I : list nat) (C : nat) :
  (C >= 2)%nat -> NoDup I -> Sorted Nat.lt I ->
  all_ge_2 (map seq I) = true ->
  check_sparse_growth (map seq I) C = true ->
  forall i j, i <> j -> (i < length I)%nat -> (j < length I)%nat ->
    Cnorm (Csum (fun k => psi (nth i (map seq I) 0%nat) k *c
                            Cconj (psi (nth j (map seq I) 0%nat) k))
                (seq (fold_right Nat.max 0%nat I) - 1))
    <= 2 / ((sqrt (INR C)) ^ (Z.abs_nat (Z.of_nat i - Z.of_nat j))).
(* 证：镜像 decay_bound_i_lt_j_one_factor（约 70 行），三处全局前提用 §三/§四 替换；
      对称方向用 Cnorm_Csum_conj_sym（ca_decay.v:1544）。 *)
```

**公理预期**：与反射引理同级（sig_forall_dec + fext，INR 继承），零 classic。

## 六、工作量与风险

- 辅助引理：~90 行（§三 4 个 + §四 2 个）
- 目标定理：~80 行（one_factor 镜像 + 对称包装）
- 合计 ~170 行，单会话可完成。
- 风险点（低）：
  - `fold_right_max_In` 若 stdlib 无现成（`fold_right_max_ge` 在 ca_decay 有，元素性需自证 ~15 行）；
  - 截断实例需重述（不直接用 Csum_psi_conj_truncate_by_upper_bound 的全局 Hstrict）；
  - `I_chain_compound` 的 R 级逐乘需小心 INR 幂运算（Rpow），但纯算术。

## 七、与内部序列路线的分工

| 路线 | seq 来源 | 守卫角色 | 状态 |
|------|---------|---------|------|
| 内部序列 | `base_seq C start`（生成器迭代，全局增长可证） | 校验提取的生成器运行时输出（防实现错误） | 现有 psa_pipeline_decay 已可直接实例化；只需 `base_seq_global_growth` + `generate_eq_map` |

---

## 八、实现结果（2026-08-18 会话 3，全部 Qed，RC=0）

`PSA_framework.v` 新增（均零 Admitted）：

**SeqProps（内部序列路线，零公理）**：
- `base_seq`（迭代 next_idx 的全局序列 Fixpoint）
- `base_seq_global_growth`：任意 i 有 base_seq ≥2 且 INR 级严格增长（零公理）
- `base_seq_shift` / `seq_shift_gen` / `generate_eq_map`：生成器 = 全局序列前缀（零公理）

**PSA_Pipeline（外部守卫路线）**：
- `guard_adjacent_growth`：守卫布尔 ⟹ I 相邻 R 级增长（sig_forall_dec+fext）
- `guard_ge2_map`：all_ge_2 (map seq I) ⟹ I 元素值 ≥2（**零公理**）
- `nth_lt_backward` / `fold_right_max_In`（**零公理**）
- `I_chain_strict` / `I_chain_compound`：I 链严格增 / 索引距离复合增长（sig_forall_dec+fext）
- `Csum_psi_conj_truncate_fin`：有限截断（sig_forall_dec+fext）
- `decay_bound_finite_one_factor`：one_factor 有限化重述（sig_not_dec+sig_forall_dec+fext）
- **`psa_guard_decay`**：守卫全部通过 ⟹ 任意 I 内对的衰减界（sig_not_dec+sig_forall_dec+fext，**零 classic**）

实测踩坑（已修）：`simpl` 过度展开 Fixpoint（用 change 只展一层）；`Rle_ge`/`Rge_le` 方向；
`Nat.max_l`/`max_r` 参数方向；`rewrite Rmult_assoc` 方向；裸 `0` 需 `%nat`。

| **外部守卫（本文）** | 任意外部全函数 seq | 校验用户提供的索引列表 I ⟹ 数学保证成立 | **本文路线，论文核心声明** |

建议两条都做：内部序列（小，~60 行）证明生成器闭环；外部守卫（本文，~170 行）证明
"运行时守护断言 ⟹ decay 界"的完整叙事。
