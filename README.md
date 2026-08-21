# 可认证稀疏门控注意力（Prime-Structured Attention，PSA）

**Certified Sparse Gating and Attention Approximation: An Executable Coq Development**

一个"算法—形式化—实证"三位一体的研究仓库：面向几何结构化频率基（psi 基 / 频率阶梯）的**可审计稀疏门控注意力**，配套两篇论文、一套 Coq/Rocq 9.0 形式化开发（165 项审计全零经典排中）、以及可执行的 OCaml/Python 反射检查器与实证脚本。

---

## 仓库结构

```
PSA-CertifiedSparseGating/
├── README.md                 # 本文件
├── LICENSE                   # Apache License 2.0
├── .gitignore
├── CLA/                      # 贡献者许可协议 + 商业授权模板（双许可模式）
│   ├── ICLA.md               # 个人贡献者 CLA
│   ├── CCLA.md               # 实体组织（公司）CLA
│   ├── RLA.md                # 运行时许可协议（特定公司授权）
│   ├── commercial_license_template.md  # 商业许可模板
│   └── README.md             # 签署流程说明
├── papers/                   # 两篇论文（草稿 + 中文规范版 md/docx）+ 评审 + 实验设计
│   ├── 论文A草稿-CertifiedSparseGating-CPP-20260819.md      # 形式化论文（CPP/ITP 方向）
│   ├── 论文B草稿-PhaseCompleteLadders-TACL-20260819.md      # 实证论文（TACL 方向）
│   ├── 论文A中文规范版-CertifiedSparseGating.md/.docx       # 中文规范版（含 Word）
│   ├── 论文B中文规范版-PhaseCompleteLadders.md/.docx
│   ├── 论文评审.txt                                        # （已按作者决定置空）
│   └── 预登记实验设计-20260819.md                       # 预登记假说 + 执行结果
├── coq/                      # Coq 形式化（Rocq 9.0.1）
│   ├── PSA_framework.v       # 主框架：19 模块 / 250 Qed / 零 Admitted / 6405 行
│   ├── PSA_audit.v           # 165 项 Print Assumptions 审计（RC=0，全零 classic）
│   ├── PSA_extract.v         # 提取链（→ OCaml psa_guard.exe）
│   ├── PSA_refcheck.v        # 参考值检查（FFI 24/24 的一部分）
│   ├── psa_guard.ml / psa_guard_main.ml / psa_guard_ffi.py  # OCaml 检查器 + Python FFI
│   ├── lib/                  # 30 个 .v：21 个在 PSA 核心传递闭包内；3D/4D/2D-wide 等 9 个为独立证书模块（各自审计）
│   └── deps/mathcomp/        # vendored mathcomp 源码（CeCILL-C，217 .v，审计/离线参考）
├── scripts/
│   ├── ci_build.sh           # CI 构建脚本（lib 链 + PSA 核心 + 零 Admitted 检查）
│   └── order.txt             # lib/ 编译顺序（DAG）
├── .github/workflows/coq.yml # GitHub Actions CI（Rocq 9.0）
├── empirical/                # 实证脚本（训练/评估/消融/相干分析/2D/KV 逐出/检查器扫描）
│   ├── length_extrap.py      # 主训练+外推评估（psi/psi-rope/rope/dense 全模式，温控内置）
│   ├── frame_check_scan.py   # 反射检查器 114 阶梯系统扫描（假阴性率 49.1%）
│   ├── coherence_analysis.py # ΔCoh 相干衰减分析（13 点指标族）
│   ├── kv_eviction.py        # KV 逐出模拟（OOD 远距 KV 净负债）
│   ├── ps2d_eval.py / ps2d_exp.py  # 2D 截断验证（评审 11 判定删除，记录在案）
│   ├── ntk_stats.py          # rope-NTK 3-seed 统计（Welch t / Cohen's d）
│   └── md2docx_zh.py         # 中文规范版 → Word 转换脚本
└── docs/
    └── audit_run.txt         # 审计证据（165 项全零 classic 的原始输出）
```

## 两篇论文

| 论文 | 方向 | 核心主张 |
|------|------|---------|
| 论文 A（Certified Sparse Gating） | CPP/ITP（形式化） | 解析核层机器检查保证：门控→框架界→截断能量→softmax 稳定→注意力近似；反射检查器 `frame_check_instance_sound`（Qed）；165 项审计全零 `Classical_Prop.classic` |
| 论文 B（Phase-Complete Ladders） | TACL（实证） | 频率阶梯统一分析：相位截断 + 旋转注入 + 覆盖梯度；实证性能最优方案 psi-rope-rand @4096=6.45±0.03（3-seed）；预登记证伪链 |

**主张边界（两文联合）**：论文 A 的证书覆盖**结构化几何阶梯**（C=4、七带复合证书）；实证性能最优方案 psi-rope-rand（随机阶梯）**不在**证书范围——两条贡献正交。"端到端"= 两条正交轨（表示稳定性 + 注意力扰动），无单一依赖链。从"能量控制"到"外推 PPL 增益"的桥梁是经验观察，**未经形式化**（论文 A §10 What is not certified）。

## 复现指引

**CI 验证链（GitHub Actions，全绿）**：Rocq 9.0 编译（lib 链 30 文件 + PSA 核心 3 文件 + 零 Admitted 检查）+ **coqchk 内核独立复验（RC=0，不信任编译器证明证书）**——代码库的证明在 Coq 内核层面独立确认。

### Coq 形式化（Rocq 9.0.1）

```powershell
# coqc 路径含 ~，cwd 必须是 bin 目录
Push-Location "C:\Rocq-Platform~9.0~2025.08\bin"
& .\coqc.exe -R "D:\ComplexAnalysis\Live_harness\AI注意力算法" PSA -Q "$uc\mathcomp" mathcomp -Q "$uc\Coquelicot" Coquelicot "coq\PSA_framework.v"
```

- 外部依赖仅 mathcomp + Coquelicot；**禁止 `-Q WBJ`**。
- 审计：`coq\PSA_audit.v`（165 项，`Classical_Prop.classic` = 0）。
- 提取链：`PSA_extract.v` → `psa_guard.ml` → `psa_guard.exe`（DkMLNative ocamlc + `OCAMLLIB` 环境变量）；FFI 自测 `python psa_guard_ffi.py`（24/24）。

### 实证（RTX 3070 8GB，torch 2.6.0+cu124）

```powershell
# 主训练 + 外推（psi-rope 七带；--psi-variant rand/lin 为嵌入变体；3 种子 {1337,42,7}）
python length_extrap.py --block 512 --batch 32 --gen-c 4 --bands 0 --seed 1337 --modes psi-rope --gpu-max 79 --gpu-resume 69 --cpu-util-max 90 --check-interval 0.5 --cooldown 60
# 反射检查器系统扫描（114 阶梯）
python frame_check_scan.py
# KV 逐出 / ΔCoh 相干分析
python kv_eviction.py && python coherence_analysis.py
```

**数据**：Gutenberg 5.1M 字符（词表 125）、模型权重（.pt）、训练日志与原始输出位于原工作区
`D:\ComplexAnalysis\Live_harness\AI注意力算法\psa_empirical\测试数据\`（本仓库已归档副本，见下）。

### 数据清单（已归档于 `data/`）

| 目录 | 内容 | 规模 |
|------|------|------|
| `data/test/` | 训练日志（ms_*/ms2_*/ntk_*/kv_*/ps2d_*）、eval 输出、相干分析 csv、multi_seed 主表 | 66 MB / 107 文件 |
| `data/models/` | 训练模型权重（.pt，全部配置 18 个，seed {1337,42,7}） | 32 MB |
| `data/corpus/` | Gutenberg / arxiv / paper / tinyshakespeare 语料 | ~6 MB |

- 数据与论文 B 各表一一对应（3-seed 均值±std 由 `data/test/` 原始日志核算，脚本见 `empirical/ntk_stats.py` 等）。
- 复现：`python empirical/length_extrap.py ...`（参数见上文），模型权重可直接加载推理/评估。
- 未入库：RH 框架的 `certificates_gamma.jsonl`（429MB，非本仓库内容）。

### 温控协议（必读）

RTX 3070 训练治理：80°C 触发 / 70°C 恢复 / 0.5s 轮询 / 60s 冷却；一次只跑一件 GPU 任务；历史 4 次宕机教训——空闲基线 56–58°C、死机临界 ~85°C、训练每步 `guard.check()`。

## 关键数字（2026-08-21 实证终态，3-seed 均值±std @8×）

| 方案 | ppl(4096) | 证书 |
|------|-----------|------|
| **psi-rope-rand（实证性能最优方案，随机阶梯）** | **6.45±0.03** | 不在证书范围（正交） |
| rope-NTK（3-seed） | 11.54±1.18（p=0.018） | 无证书 |
| E5'' 七带 [3,7,15,31,63,127,255] | 12.40±0.74 | 复合证书（Qed） |
| C=4 [3,13,53,213] | 12.75±0.34 | 紧证书（μ=4/5 有理界） |
| rope（朴素 RoPE，3-seed） | 25.30±4.63 | 无 |
| C=3 | 22.86±5.30 | 间距缺陷+方差放大 |

## 许可与授权

- **Apache License 2.0（公开版）**：源码与文档以 Apache-2.0 公开，研究 / 学习 / 参考自由使用。详见 `LICENSE`。
- **贡献者许可协议（CLA）**：贡献者须签署 `CLA/ICLA.md`（个人）或 `CLA/CCLA.md`（公司），确保贡献既可 Apache-2.0 公开、也可纳入商业许可版本（作者保留商业化权利）。详见 `CLA/README.md`。
- **商业授权 / 运行时许可（RLA）**：商业使用（嵌入产品、SaaS、生产环境）或需要 `psa_guard.exe` 等运行时组件的**特定公司**，请联系 `168888@live.cn` 获取商业许可（模板见 `CLA/commercial_license_template.md`，组件条款见 `CLA/RLA.md`）。开源版不含运行时组件的商业授权。
- **第三方依赖**：`coq/deps/mathcomp/`（CeCILL-C，vendored，见其 README）；Coquelicot（LGPL 2.1+，CI 经 opam 安装）。各自许可独立适用。


