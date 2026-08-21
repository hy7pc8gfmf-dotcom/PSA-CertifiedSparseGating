# psa_empirical 测试数据归档（2026-08-19）

> **用途**：注意力算法实验的**必须保存的测试数据**（模型权重 / 日志 / 评估结果 / 语料），
> 与脚本分离归档于此子目录；脚本留在 `psa_empirical\` 根。

## 分类清单（71 个文件）

| 类别 | 数量 | 说明 |
|------|------|------|
| 模型权重 `model_*.pt` | 26 | dense / psi / psi-trunc / psi-rope / rope / nope × b256/b512 × seed 变体——训练产物，不可再生（重训需 GPU 时间），**核心证据** |
| 训练日志 `train_log*.txt` | 25 | 各 run 完整日志（含 multi-seed 8 run：ms_c2/c3/c4/e5pp × s42/s7、nope、extrap 系列等） |
| 评估结果 `eval_*.txt` | 3 | eval_rope_ntk / eval_rope_pi / eval_psitrunc_c2——诚实性对照 |
| 主表 | 1 | `multi_seed_main_table.md`（论文 B 核心数据表） |
| 温控日志 | 1 | `thermal_probe_log.txt`（温控治理环境证据） |
| 语料/输入数据 `*.txt` | 9 | gutenberg_corpus（5.1M 字符训练语料，**复现必需**）、arxiv_corpus、paper_corpus、tinyshakespeare、1342/1661/2600/2701-0.txt |
| arXiv 论文语料 | 7 | `arxiv_papers/`（5 PDF + 2 bin，实验输入） |

## 脚本路径兼容（2026-08-19 已改 length_extrap.py）

`length_extrap.py` 新增 `resolve_data()` / `resolve_model()` 路径回退：
- **语料**：`HERE` 根缺失时自动找 `测试数据/`（load_data 三个候选语料同样生效）；
- **模型加载**：eval-only 时先找 `HERE` 根、再找 `测试数据/`（旧路径仍可用）；
- **模型保存**：新训练仍存 `HERE` 根（保持原逻辑），完成后可手动移入 `测试数据/`。

## 根目录剩余（非数据，开发用）

`arxiv_corpus.py` / `length_extrap.py` / `mini_gpt_compare.py` / `thermal_probe.py` / `thermal.py`
（`__pycache__` 已删除）。
