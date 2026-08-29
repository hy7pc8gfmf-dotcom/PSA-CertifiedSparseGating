# 交接文档：三维无条件基组装定理（纯构造性）

> **更新时间**：2026-08-19 21:10 (GMT+8) —— Step-4 完成版
> **用途**：更换账号 / 新对话框后，从本文档恢复全部上下文，继续推进任务。
> **铁律（源自 `coq-live-repair` 技能 §0–§6）**：Rocq/Coq 9.0，仅依赖 mathcomp + Coquelicot；**零 `Admitted`、零活动 `Axiom`（AZ 红线）**；纯构造性证明（显式界，不用 `Req_EM_T`）。

---

## 0. 当前状态总览（2026-08-19 Step-4 完成）

**全部完成，主定理完全自包含：**

- `ca_basis_3d.v`（945+ 行 → 现 ~1000 行）编译 EXIT=0
- `tensor_product_unconditional_basis_3d`：**已删除 Hdecay_engine 假设**，衰减由
  `phi_flat_decay_general_3d`（本文件第 4 步，位于主定理之前）直接供给
- `phi_flat_decay_general_3d`：完整 Qed（8 分支常数分类 + 截断 C-S 三重界）
- 辅助引理族：`min6_is_one`、`complex_eq_re_im`、`Cmul_shuffle`、
  `phi3D_inner_scalar_decomposition`、`Rsqr_nonneg`、`triple_inner_single_bound`、
  `Rmult_le_compat_right_mine`、`Rmult_le_compat4_mine`、`K0_mult_fin`、`one_le_half_K0_dprod`
- 验证：零 Admitted/Abort（grep 仅注释命中）、`Print Assumptions` 仅 Reals 标准库
  经典公理（sig_not_dec / sig_forall_dec / 函数外延性，与 22 库基线一致）、
  `coqchk -silent` RC=0

**⚠ 常数修正（重要设计变更）**：原 Hdecay_engine 草案的 `K0 = Rmax 8 C³/4`
**数学上不可满足**——在「仅 c 轴索引不同（dk=6）且 a=b≤c₁」配置下三重内积可逼近 1，
而目标界只有 (C³/4)·2/C³ = 1/2。已改为**可证最小常数 `K0 = Rmax 8 C³/2`**，
主定理 K0 与 M_bound 同步（M_bound = K0·((1+4K)³−1)，数值约为旧版 2 倍）。

## 1. 任务主线

**目标**：为「解析数论 3D 无条件基」写出第 5 步组装定理——**三维张量积无条件基定理**，纯构造性风格。

- **定理名**：`tensor_product_unconditional_basis_3d`（位于 `ca_basis_3d.v` 末部）
- **数学内容**：对三维索引族 `seq1/seq2/seq3`（稀疏增长），构造归一化张量积函数系 `phi_flat`，证明 Riesz 双边界：
  `(1 - M_bound) * S <= l2_norm_sq F (Nat.pred M) <= (1 + M_bound) * S`
- **实现策略**：组装式复用 ca_decay.v 中维度无关骨架 `abstract_unconditional_basis`，6 个证明义务中衰减义务由 `phi_flat_decay_general_3d` 供给。

## 2. 环境与工具

### 2.1 编译（无需 subst，实路径直用）

- coqc：`C:\Rocq-Platform~9.0~2025.08\bin\coqc.exe`（路径含 `~`，**cwd 必须是其 bin 目录**）
- 一律用 Python 脚本编译（PowerShell 空输出 / Git Bash 吞字符）：
  `C:\Users\Live\.workbuddy\binaries\python\versions\3.13.12\python.exe D:\ComplexAnalysis\Live_WorkBuddy\Tools\build\_coq3d_build.py`
- 日志：`Tools/compile_3d.log`；产物：`Tools/src/ca_basis_3d.vo`
- 单文件探针编译：`Tools/build/_probe_build.py <name>`（编译 `Tools/src/<name>.v`）
- coqchk：`coqchk -Q <src> "" -Q <mc> mathcomp -Q <cq> Coquelicot -silent ca_basis_3d`

## 3. 关键目录与文件（Tools/ 工作区）

| 路径 | 说明 |
|---|---|
| `Tools/src/ca_basis_3d.v` | **主交付物**（Step-4 引擎 + 组装定理，~1000 行） |
| `Tools/src/ca_decay.v` 等 22 库 | 依赖库（已预编译 .vo；`Module ExtendedTheorems` 需显式 Import） |
| `Tools/src/ca_basis_3d.backup-20260819-step4.v` | Step-4 动工前备份 |
| `Tools/build/_coq3d_build.py` | 编译脚本 |
| `Tools/docs/HANDOVER.md` | 本文档副本 |
| `Tools/docs/经验/` | 经验卡（E063 新增：lia/lra 与 Cpow 作用域两大坑） |
| `Tools/skill/coq-live-repair/` | 技能源（已安装到 `~/.zcode/cli/skills/`） |

## 4. Step-4 引擎结构（phi_flat_decay_general_3d）

签名：C>2、seq1..3、Hsparse1..3、Hge2_1..3、I1..3、n1..3 与 Hn1..3、idx1≠idx2、
Hlt1/Hlt2、点态 Hidx6（|Δi|+|Δj|+|Δk| ≤ 6）→
`Cnorm (Csum (fun k => phi3D_norm a1 b1 c1 k *c Cconj (phi3D_norm a2 b2 c2 k)) (Nat.pred (S Mfull))) ≤ (Rmax 8 C³/2)·d_i·d_j·d_k`

证明三支路（不走 2D 引擎嵌套，因 K0' 常数下界 ≥1 即可闭合）：
1. `phi3D_inner_scalar_decomposition`：内积提出纯量 `(1/G1·1/G2) *c` 三重 ψ 内积（纯代数，Cmul_shuffle + Cconj_mul）；
2. `triple_inner_single_bound`：截断 C-S（U=A*B, V=C）→ `Cnorm ≤ G1·G2`（无稀疏/域条件）⇒ 归一化内积 ≤ 1；
3. `one_le_half_K0_dprod`：8 分支（i/j/k 各自是否相等）常数引理 → `1 ≤ (Rmax 8 C³/2)·dprod`（等轴 d_factor=1，异轴=2/r^d，dtot≤6 ⇒ r^dtot≤C³）。
稀疏性仅用于截断（值 ≤ seq maxIdx ≤ pred Mfull，经 Hseq*_inc + fold_right_max_ge）。

## 5. 已踩坑清单（新增 4 条，接旧版 11 条）

12. **R 目标禁用 `lia`（本机环境）**：ca_* 导入链破坏 zify，`lia`/`lra` 中 **`lia` 对 R 目标恒败（"Cannot find witness"）**，`lra` 正常。nat 目标两者皆可。原文件惯例 nat→lia、R→lra。
13. **C_scope 下 `^` 是 Cpow**（ca_base complex_scope 定义 `z^n := Cpow`）：实数幂必须 `(...)%R` 标注，否则 "r : R expected Complex"。`/`、`-`、`<=` 虽未重定义但组合表达式也建议标注。
14. **大上下文 + min 析取 + lia = 挂死**：`(unfold N0; lia)` 证 6 层 min 的 6 路析取，在引擎 60+ 假设上下文里指数爆炸（>20 分钟）。改用 `min6_is_one`（3 层 `Nat.min_spec` destruct，确定性）。
15. **stdlib 名被遮蔽/形态不符**：`Rplus_le_compat_r` 要求相同加数、`Rmult_le_compat_l` 报 ring 错、`Cnorm_ge_0` 不在顶层。自建 `Rmult_le_compat_right_mine`/`Rmult_le_compat4_mine`/`complex_eq_re_im`；`0 ≤ Cnorm z` 用 `unfold Cnorm; apply sqrt_pos`。
16. **field 侧条件顺序不定**：用 `repeat split; try (...)` 顺序无关化；等式方向注意 `symmetry`（`Rinv_l` 结论是 `/r*r = 1`）。
17. **`rewrite <-` 会重写子项内部的同名变量**（如 K→K/2*2 循环展开）：用 `Rle_trans with (中转项)` + 正向 rewrite 替代。

## 6. 关键引理与骨架（ca_decay.v 内，需 Import ExtendedTheorems）

- `abstract_unconditional_basis n phi M M_bound delta`：6 义务 → Riesz 双边界
- `Csum_trunc_tail f M N`：`M<=N` 且 `[M,N)` 上 f=0 → `Csum f N = Csum f M`（注意区间是 `M <= k < N`）
- `CauchySchwarz_truncated A B N0`：`(N0>0)`（注意是 0<N0 不是 ≠）+ `A N0 *c B N0 = C0` → 平方和界
- `sum_sq_psi_product n1 n2 M`、`Cnorm_sq_psi_exact`、`psi_ge_n_zero`、`d_factor`、`d_factor_diag`
- `H_nth_map`、`fold_right_max_ge`（ca_independence）、`nth_In`、`seq_strict_growth_lt`

## 7. 完成标准（Definition of Done）

- [x] `ca_basis_3d.v` 通过 coqc 编译，EXIT=0（仅 deprecation Warning）
- [x] 零 `Admitted`、零活动项目 Axiom（Print Assumptions 仅 Reals 经典公理，与基线一致）
- [x] `tensor_product_unconditional_basis_3d` 完整 Qed，**无 Hdecay_engine 假设**
- [x] `phi_flat_decay_general_3d` 完整 Qed（K0' = Rmax 8 C³/2）
- [x] `coqchk` 独立复验 RC=0
- [x] 主定理 K0/M_bound 常数同步为 /2（原 /4 数学不可满足，见 §0）

## 8. 下一步建议（可选跟进）

1. 若需还原旧常数 C³/4：须加强 H_dom 域条件（例如要求 c 轴值与 a=b 的序关系），并给出单轴相消引理——当前无此必要。
2. 可选：把 `min6_is_one`/`Rmult_le_compat*_mine` 等泛用引理上提到 ca_basis_lemmas.v 供复用（涉及下游 .vo 全量重建，非必需）。
3. 经验卡 E063 已登记（lia-R 失效 + Cpow 作用域 + min-lia 挂死三坑）。
