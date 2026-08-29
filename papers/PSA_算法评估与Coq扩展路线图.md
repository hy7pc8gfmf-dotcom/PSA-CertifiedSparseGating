# PSA 算法评估与 Coq 扩展路线图（2026-08-18 会话 3 末）

> 基于：会话 2-3 完成的 PSA 补证（17 引理全 Qed）+ 提取/FFI 闭环 +
> 本日通读《Prime-Structured Attention v2.1.txt》原文与库内关键定理精读。

---

## 一、算法评估（补证完成后）

### 1.1 已形式化闭环（真实增量，可写入论文）

| 环节 | 对应文档节 | 形式化状态 |
|------|-----------|-----------|
| 确定性基序列生成器 | §1.1 / Step2 | ✅ `generate_correct`（零公理）：长度 S len、全 ≥2、严格 C-增长、NoDup、Sorted |
| 守护断言反射正确性 | Step1 | ✅ `check_sparse_growthP` / `check_c_sparse_on_valsP` / `all_ge_2P`（反射，bool ⟷ R 级条件） |
| 管线实例化 | §0 依赖链 | ✅ `psa_pipeline_decay`（exact decay_bound）/ `psa_pipeline_linindep`（exact psi_linear_independent） |
| 提取 → 运行时检查器 | §10 Phase0 | ✅ 全链：Coq → `psa_guard.ml`（Peano nat 无溢出）→ OCaml 字节码 → Python FFI，11/11 参考值通过 |

### 1.2 结构性缺口（算法文档声称但未/不能形式化）

1. **概率门控前提不可满足**（§3）：`sparse_subset_exists` 与 `sparse_subset_exists_constructive`
   （ca_probabilistic.v:1449/2646）前提均为 `(INR N·INR N·p·p < 1)`，p=0.5、N≥2 恒不成立。
   → 伯努利采样路线的"失败概率上界"无法借用；**确定性贪心门控是唯一可行路线，且其正确性尚未形式化**。
2. **行截断误差引理缺失**（§4.2 / 第五步 1）：`truncation_error_lemma` 未证；且文档草稿
   `sort (>=) scores` 在构造性 Coq 中**不可行**（R 上序不可判定）——需改为"保留集/补集"的
   无排序陈述（`complement_sum_bound`）。
3. **decay_bound 全局前提 vs 守卫有限列表**（**本日新发现**）：decay_bound（ca_decay.v:1572）
   的 growth 前提是**全函数** `forall i, INR (seq (S i)) > INR C * INR (seq i)`，而守卫只验证
   有限索引列表 I 内相邻对。外部列表路线（任意 vals ⟹ decay_bound）**不能直接实例化**；
   需①生成器全局序列（内部保证），或②在 PSA 层重述"有限链足够支撑 I 内对的界"（可考察
   库内中间引理 `decay_bound_i_lt_j` / `decay_bound_i_lt_j_one_factor`，ca_decay.v:1284/1442）。
4. **softmax 非线性 vs 线性范数界**（结构性）：库内界是 psi 框架的线性代数界（内积衰减、
   Riesz 常数 1±4K），注意力是行归一化 softmax（非线性）。"注意力分数由学到的 W_Q/W_K
   投影产生"不在任何定理覆盖内。§6 范数比监控区间 [0.5,3.0]、梯度 Lipschitz 推导均为启发式。
5. **无限维/质数声明**：无定理支撑（l2_sequence 仅定义层；质数幂仅线性无关）。

### 1.3 总评

- **数学部件**（稀疏基生成、守护反射、衰减/线性无关实例化、低相干结构）：形式化完整、零 classic，
  是真实增量——支撑"受定理约束的稀疏注意力：Coq 到运行时守护"（CPP/ITP 定位）。
- **算法工程部件**（softmax 注意力本身）：与形式化脱节是**根本限制**（会话 2 结论不变）。
- 建议叙事：形式化方法论文 + 诚实路线 A（运行时守护方法论），而非"加持 AI"。

---

## 二、Coq 扩展路线图（按优先级，全部落点 PSA_framework.v 或新文件）

### P0 — 确定性门控形式化（补 §3 缺口，中工作量，本周可做）

```coq
(* 贪心过滤：首个总是保留，之后 val >= C·last_kept 才保留（与 Python fallback_mask 一致） *)
Fixpoint greedy_selected (C : nat) (vals : list nat) : list nat := ...

Theorem greedy_selected_correct (vals : list nat) (C : nat) :
  (C >= 2)%nat -> Sorted Nat.lt vals -> all_ge_2 vals = true ->
  let sel := greedy_selected C vals in
  Sorted Nat.lt sel /\ NoDup sel /\ all_ge_2 sel = true /\
  check_c_sparse_on_vals sel C = true.          (* <=? 语义，匹配 c_sparse_subset 的 >= *)

(* 推论：反射 ⟹ 选出的子集满足库内 c_sparse_subset（ca_basis_lemmas.v:6658） *)
```
机械：已有 all_ge_2P / check_c_sparse_on_valsP / sorted_of_strict_adjacent /
forallb_adjacent_from_nth；需 filter/递归的 NoDup、In、Sorted 保持引理（Stdlib）。
意义：确定性门控（会话 2 已裁定唯一可行路线）的正确性首次形式化，补齐 doc §3.2。

### P1 — 生成器 → BaseSequence 收尾 + 行截断误差（小-中工作量）

```coq
(* P1a：generate_correct 的列表性质封装为记录（doc Step2 的 construct_base_sequence，已 Qed 化） *)
Definition construct_base_sequence (len C start : nat)
  (HC : (C >= 2)%nat) (Hstart : (start >= 2)%nat) : BaseSequence C := ...
(* 需 map_nth_seq 引理：map (fun i => nth i lst 0) (seq 0 (length lst)) = lst *)

(* P1b：行截断误差（无排序的构造性版本，避免 R 上 sort 不可判定） *)
Lemma complement_sum_bound (n : nat) (score : nat -> R) (A B : list nat) (budget : R) :
  (* A ∪ B = seq 0 n，A ∩ B = ∅ *)
  sum_A >= sum_total - budget -> sum_B <= budget.
(* 与 row_sum_bound_K（ca_decay.v:3506，需 C > 2）连接：行非对角能量 ≤ 2/(√C−1)
   ⟹ 丢弃能量 ≤ min(S·ε_rel, R_max·ε_abs) ≤ ε_abs·R_max（掩码构造直接保证）。 *)
```
注意：这是**抽象行能量层**的引理；到实际注意力分数（含 W_Q/W_K）的桥不存在（见缺口 4），
文档应如实表述。

### P2 — psa_pipeline_soundness 真证（doc 第三步的 Admitted 变 Qed，中-大工作量，论文核心声明）

```coq
(* 全局生成器序列：next = max(last·C+1, last+2) 的迭代函数（generate_correct 的无限版） *)
Definition base_seq (C start : nat) : nat -> nat := iter next_idx start.
Theorem base_seq_global_growth (C start : nat) :
  (C >= 2)%nat -> (start >= 2)%nat ->
  (forall i, (base_seq C start i >= 2)%nat
              /\ (INR (base_seq C start (S i)) > INR C * INR (base_seq C start i))%R).
Theorem generate_eq_map : forall len C start,
  generate_base_indices len C start = map (base_seq C start) (seq 0 (S len)).

(* 守卫 → 库内定理合一（真 Qed，替换 doc 的 Admitted 骨架） *)
Theorem psa_pipeline_soundness (seq : nat -> nat) (I : list nat) (C : nat) :
  (C >= 2)%nat -> (forall i, (seq i >= 2)%nat) ->
  NoDup I -> Sorted Nat.lt I ->
  (forall i, (INR (seq (S i)) > INR C * INR (seq i))%R) ->   (* 或：check_sparse_growth (map seq I) C = true + 有限链引理 *)
  (forall i j, i <> j -> (i < length I)%nat -> (j < length I)%nat ->
     Cnorm (Csum (fun k => psi (nth i (map seq I) 0%nat) k *c Cconj (psi (nth j (map seq I) 0%nat) k))
                 (seq (fold_right Nat.max 0%nat I) - 1)) <= 2 / ((sqrt (INR C)) ^ (Z.abs_nat (Z.of_nat i - Z.of_nat j))))%R
  /\ psi_linear_independent (map seq I) ... .
```
关键难点（本日新发现，需先攻克）：decay_bound 的 growth 前提是**全函数**，守卫只给有限 I。
两条路线：
  (a) 内部序列路线：seq := base_seq C start，用 base_seq_global_growth 填全函数前提（生成器保证）。
  (b) 外部序列路线：考察库内 `decay_bound_i_lt_j`（ca_decay.v:1284）/`_one_factor`（1442）
      是否只需有限相邻链；若可，在 PSA 层重述"守卫 ⟹ 有限前缀 decay"。

### P3 — 低相干 / Riesz 常数组合定理（数学深度，中-大工作量）

```coq
(* P3a：低相干——相邻基内积范数界（decay_bound dist=1 的命名特例，PSA 声称的"低相干结构"） *)
Theorem psa_low_coherence (seq : nat -> nat) (C : nat) ... :
  ... Cnorm (Csum (fun k => psi (seq i) k *c Cconj (psi (seq (S i)) k)) ...) <= 2 / sqrt (INR C).

(* P3b：框架界实例化（Riesz 常数 1±4K，需 C > 2 与 Hinc；生成器序列天然满足） *)
Theorem psa_frame_bounds (C start : nat) (I : list nat) (coeffs : list Complex) ... :
  ... ((1 - 4*K(INR C))*S <= l2_norm_sq F (M-1) <= (1 + 4*K(INR C))*S)%R.  (* psi_unconditional_basis 实例 *)
```
意义：把 PSA 的"确定性 + 闭式常数 + 低相干"声明变成可引用的命名定理。

### P4 — 远期
- 22 库剩余 7 条 classic 消除（MVT×2 / gamma EM×7 / RInt_gen 源定位）——"减依赖"方向。
- S3 CReal 平行证明（可提取实数闭环）。

---

## 三、建议下一步

1. P0（贪心门控正确性）——最易见效，补齐 doc §3 唯一可行路线的形式化。
2. P2 路线 (b) 的可行性侦察——读 `decay_bound_i_lt_j` / `_one_factor`（ca_decay.v:1284/1442），
   判断"有限相邻链 ⟹ I 内对的界"是否可重述；这决定 psa_pipeline_soundness 的外部序列版能否成立。
3. 论文叙事 = P0 + P2 + P3a 的合集："可验证的稀疏注意力运行时：生成、守卫、框架界全链形式化"。
