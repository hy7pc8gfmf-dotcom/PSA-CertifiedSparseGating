# 可认证稀疏门控注意力（Prime-Structured Attention，PSA）

**Certified Sparse Gating and Attention Approximation: An Executable Coq Development**

一个"算法—形式化—实证"三位一体的研究仓库：面向几何结构化频率基（psi 基 / 频率梯子）的**可审计稀疏门控注意力**，配套两篇论文、一套 Coq/Rocq 9.0 形式化开发（165 项审计全零经典排中）、以及可执行的 OCaml/Python 反射检查器与实证脚本。

---

## 仓库结构

```
PSA-CertifiedSparseGating/
├── README.md                 # 本文件
├── LICENSE                   # MIT
├── .gitignore
├── papers/                   # 两篇论文（草稿 + 中文规范版 md/docx）+ 评审 + 实验设计
│   ├── 论文A草稿-CertifiedSparseGating-CPP-20260819.md      # 形式化论文（CPP/ITP 方向）
│   ├── 论文B草稿-PhaseCompleteLadders-TACL-20260819.md      # 实证论文（TACL 方向）
│   ├── 论文A中文规范版-CertifiedSparseGating.md/.docx       # 中文规范版（含 Word）
│   ├── 论文B中文规范版-PhaseCompleteLadders.md/.docx
│   ├── 论文评审.txt                                        # 形式化审查报告（Accept Strong）
│   └── 诚实性支柱实验设计-20260819.md                       # 预登记假说 + 执行结果
├── coq/                      # Coq 形式化（Rocq 9.0.1，仅 mathcomp + Coquelicot 依赖）
│   ├── PSA_framework.v       # 主框架：19 模块 / 250 Qed / 零 Admitted / 6405 行
│   ├── PSA_audit.v           # 165 项 Print Assumptions 审计（RC=0，全零 classic）
│   ├── PSA_extract.v         # 提取链（→ OCaml psa_guard.exe）
│   ├── PSA_refcheck.v        # 参考值检查（FFI 24/24 的一部分）
│   ├── psa_guard.ml / psa_guard_main.ml / psa_guard_ffi.py  # OCaml 检查器 + Python FFI
│   ├── ca_basis_3d.v / ca_basis_4d.v                        # 3D/4D 张量积无条件基（组合性演示）
│   ├── ca_2d_wide_const.v / _engine.v / _asm.v             # 2D-wide（免 H_dom，M_bound=768）
│   └── ca_2d_wide_audit.v / ca_4d_audit.v                   # 高维审计
├── empirical/                # 实证脚本（训练/评估/消融/相干分析/2D/KV 逐出/检查器扫描）
│   ├── length_extrap.py      # 主训练+外推评估（psi/psi-rope/rope/dense 全模式，温控内置）
│   ├── frame_check_scan.py   # 反射检查器 114 梯子系统扫描（假阴性率 49.1%）
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
| 论文 B（Phase-Complete Ladders） | TACL（实证） | 频率梯子统一分析：相位截断 + 旋转注入 + 覆盖梯度；实证冠军 psi-rope-rand @4096=6.45±0.03（3-seed）；诚实证伪链 |

**主张边界（两文联合）**：论文 A 的证书覆盖**结构化几何梯子**（C=4、七带复合证书）；实证冠军 psi-rope-rand（随机梯子）**不在**证书范围——两条贡献正交。"端到端"= 两条正交轨（表示稳定性 + 注意力扰动），无单一依赖链。从"能量控制"到"外推 PPL 增益"的桥梁是经验观察，**未经形式化**（论文 A §10 What is not certified）。

## 复现指引

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
# 反射检查器系统扫描（114 梯子）
python frame_check_scan.py
# KV 逐出 / ΔCoh 相干分析
python kv_eviction.py && python coherence_analysis.py
```

**数据**：Gutenberg 5.1M 字符（词表 125）、模型权重（.pt）、训练日志与原始输出位于原工作区
`D:\ComplexAnalysis\Live_harness\AI注意力算法\psa_empirical\测试数据\`（本仓库不含大型二进制，.gitignore 已排除）。

### 温控协议（必读）

RTX 3070 训练治理：80°C 触发 / 70°C 恢复 / 0.5s 轮询 / 60s 冷却；一次只跑一件 GPU 任务；历史 4 次宕机教训——空闲基线 56–58°C、死机临界 ~85°C、训练每步 `guard.check()`。

## 关键数字（2026-08-21 实证终态，3-seed 均值±std @8×）

| 方案 | ppl(4096) | 证书 |
|------|-----------|------|
| **psi-rope-rand（实证冠军，随机梯子）** | **6.45±0.03** | 不在证书范围（正交） |
| rope-NTK（3-seed） | 11.54±1.18（p=0.018） | 无证书 |
| E5'' 七带 [3,7,15,31,63,127,255] | 12.40±0.74 | 复合证书（Qed） |
| C=4 [3,13,53,213] | 12.75±0.34 | 紧证书（μ=4/5 有理界） |
| rope 裸绳（3-seed） | 25.30±4.63 | 无 |
| C=3 | 22.86±5.30 | 间距缺陷+方差放大 |

## 许可与致谢

MIT License。研究用代码，无隐式担保。详见 `LICENSE`。
