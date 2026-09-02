# 提取产物清单（Extraction Inventory）

生成：`审计证据/gen_extraction_inventory.py`（2026-09-02）。
再生：`make extract`（脚本 scripts/extract_artifacts.sh，coqc 9.1 + ocamlc）；
源↔生成物漂移自检：`python scripts/check_extraction_determinism.py [--full]`。
纪律：生成物由源码内 Extraction 命令产生——**do not edit**，改源再生。

| 产物 | 源（声明位） | 轨道 | 论文引用 | 运行时证据 |
|---|---|---|---|---|
| `c4_four_atom_cr.ml+.mli ✅` | coq/probes/probe_c4_four_atom_cr.v:L162 | constructive-Q | §5.6.6 CS-15 | ocamlc 绿（论文记载） |
| `c4_gram_unique_cr.ml+.mli ✅` | coq/probes/probe_c4_gram_unique_cr.v:L934 | constructive-Q | §5.6.6 CS-23 | 提取 bench 全过（论文记载） |
| `c4_unique2sparse_cr.ml+.mli ✅` | coq/probes/probe_c4_unique2sparse_cr.v:L772 | constructive-Q | §5.6.6 CS-21 | — |
| `frame_check_graduated.ml+.mli ✅` | coq/probes/probe_frame_check_graduated.v:L451 | classic-R | §5.6.6 CS-17 分级检查器 | 四级判定 <1ms（extraction_benchmark_20260830） |
| `g11_checkiff_cr.ml+.mli ✅` | coq/probes/probe_g11_checkiff_cr.v:L221 | constructive-Q | §5.6.6 G-11 真 iff | — |
| `g13_certtight_cr.ml+.mli ✅` | coq/probes/probe_g13_certtight_cr.v:L253 | constructive-Q | §5.6.6 G-13 收紧器 | 提取 bench（论文记载） |
| `g7_welch_cr.ml+.mli ✅` | coq/probes/probe_g7_welch_cr.v:L828 | classic-R | §5.6.6 G-7 Welch 下界 | — |
| `g9_pairfrac_cr.ml+.mli ✅` | coq/probes/probe_g9_pairfrac_cr.v:L234 | constructive-Q | §5.6.6 G-9 闭合式 | ocamlc 绿（论文记载） |
| `gershgorin_qtw.ml+.mli ✅` | coq/probes/probe_gershgorin_qtw.v:L594 | constructive-Q | §5.2 C1 孪生 | WSL 冒烟 true/true（2026-09-02） |
| `itv_noisyor_cr.ml+.mli ✅` | coq/probes/probe_itv_noisyor_cr.v:L214 | constructive-Q | §5.6.6 G-10 noisy-OR | — |
| `pareto_qtw.ml+.mli ✅` | coq/probes/probe_pareto_qtw.v:L456 | constructive-Q | §5.2 C2 孪生 | WSL 冒烟 305/6400 + 鸽笼 0/9^10（2026-09-02） |
| `qset_twin_base.ml+.mli ✅` | coq/probes/qset_twin_base.v:L845 | constructive-Q | C 系列基座（A v2.27） | ocamlc 绿；44×Closed |
| `rc_envelope_t2.ml+.mli ✅` | coq/probes/probe_rc_envelope.v:L756 | constructive-Q | §6 T2 包络 | bench_rc_env.log：env_lt_check 分离翻转 n=25 true 5.98ms |
| `safe_domain.ml+.mli ✅` | coq/probes/probe_safe_domain.v:L148 | constructive-Q | §5.6.6 CS-16 | safe_domain_bool 运行时判定（<1ms） |
| `taugrid_cr.ml+.mli ✅` | coq/probes/probe_taugrid_cr.v:L352 | constructive-Q | §5.6.6 CS-12 | ocamlc 绿（DkMLNative 4.14.2） |
| `z2b_bench.ml（无 mli）` | ⚠️ 未解析到 Extraction 声明 | bench-driver | Z2b 基准驱动 | ocamlc 绿 |
| `z2b_int63mirror.ml+.mli ✅` | coq/probes/probe_z2b_int63mirror.v:L373 | constructive-Q | §5.6.6 Z2b | z2b_bench：C=4 双 true + 溢出发散确认 |
| `z3b_bench.ml+.mli ✅` | ⚠️ 未解析到 Extraction 声明 | classic-Q-bench | §5.2 z3b 充分性基准 | [2,16,128]=true / [2,3]=false 机器实证（WSL ocamlopt） |
| `z_frame_check.ml+.mli ✅` | coq/probes/probe_z_frame_check.v:L322 | constructive-Q | §5.6.6 CS-22（Zarith 路线） | — |

---
统计：跟踪 19 件（18 有 .mli），Extraction 声明全部解析；⚠️ 未解析：z2b_bench, z3b_bench。

**确定性说明**：Extraction 为确定性输出——同版本提取器对同源产生逐字节相同产物；
自检脚本对代表集重新提取并 diff，DRIFT 即「源已改而生成物未再生」或「提取器版本错位」，
处置 = `make extract` 再生后随源同批入库（生成物头部含来源，**禁手改**）。
