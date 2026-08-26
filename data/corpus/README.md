# 训练语料：tinystories_corpus_200mb.txt（200MB）

本文件为论文 B（Phase-Truncated Frequency Ladders）正式配置训练语料：

- **文件名**：`tinystories_corpus_200mb.txt`
- **大小**：200 MB（精确 200,000,000 字节）
- **用途**：论文 B 正式配置（27000 iters，云端 T4）训练语料；日志见 `../logs/formal27000_20260826/`
- **为何不在仓库内**：GitHub 单文件推送硬限 100 MB，本文件超出——故移出 git 跟踪（`.gitignore` 忽略），文件保留在本地工作区 `D:\ComplexAnalysis\Live_harness\AI注意力算法\psa_empirical\测试数据\corpus\tinystories_corpus_200mb.txt` 与本地仓库副本。

## 获取方式

1. **本地路径**：`D:\ComplexAnalysis\Live_harness\AI注意力算法\psa_empirical\测试数据\corpus\tinystories_corpus_200mb.txt`（权威副本）
2. **构造方式**：由 TinyStories 语料清洗拼接至 200MB（脚本 `../scripts/` 或 `psa_empirical/` 下语料准备脚本）
3. **哈希**：SHA-256 = `C05A5A07BE665056ABF1222F48B38FB9549715C19FC94C069DFA18EA0F5FB877`（如需复现训练，向作者索取或本地重建）

## 替代（若需完全可复现）

- 训练脚本 `length_extrap.py --data tinystories_corpus_200mb.txt` 接受任意同格式语料文件；
- 论文 B 全部数值结论已固化于 `../logs/formal27000_20260826/` 日志，不依赖语料文件本身可核验。

