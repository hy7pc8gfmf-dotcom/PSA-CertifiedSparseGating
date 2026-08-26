# 训练语料：tinystories_corpus_200mb.txt（200MB）

本文件为论文 B（Phase-Truncated Frequency Ladders）正式配置训练语料：

- **文件名**：`tinystories_corpus_200mb.txt`
- **大小**：200 MB（精确 200,000,000 字节）
- **用途**：论文 B 正式配置（27000 iters，云端 T4）训练语料；日志见 `../logs/formal27000_20260826/`
- **为何不在仓库内**：GitHub 单文件推送硬限 100 MB，本文件超出——故移出 git 跟踪（`.gitignore` 忽略），文件保留在本地工作区 `D:\ComplexAnalysis\Live_harness\AI注意力算法\psa_empirical\测试数据\corpus\tinystories_corpus_200mb.txt` 与本地仓库副本。

## 下载链接（原始语料）

本语料来自 **TinyStories** 数据集（roneneldan/TinyStories，Hugging Face）：

- **官方源（Hugging Face）**：<https://huggingface.co/datasets/roneneldan/TinyStories>
  - 训练集直链：<https://huggingface.co/datasets/roneneldan/TinyStories/resolve/main/TinyStories-train.txt>
- **国内镜像（hf-mirror）**：<https://hf-mirror.com/datasets/roneneldan/TinyStories/resolve/main/TinyStories-train.txt>

### 复现命令（下载并截取 200MB）

仓库内 `psa_empirical/download_corpus.py` 提供流式下载（无需额外依赖）：

```bash
# 下载完整 TinyStories 训练集
python download_corpus.py "https://hf-mirror.com/datasets/roneneldan/TinyStories/resolve/main/TinyStories-train.txt" "data/corpus/tinystories_full.txt" 0

# 截取前 200,000,000 字节（与论文 B 正式配置语料一致）
python download_corpus.py "https://hf-mirror.com/datasets/roneneldan/TinyStories/resolve/main/TinyStories-train.txt" "data/corpus/tinystories_corpus_200mb.txt" 200000000
```

> 注：`download_corpus.py` 位于工作区 `psa_empirical/`；hf-mirror 直连慢或不可达时改用 Hugging Face 官方直链。

## 哈希校验

- **SHA-256**：`C05A5A07BE665056ABF1222F48B38FB9549715C19FC94C069DFA18EA0F5FB877`
- 下载后校验：`Get-FileHash data/corpus/tinystories_corpus_200mb.txt -Algorithm SHA256`（PowerShell）

## 替代（若需完全可复现）

- 训练脚本 `length_extrap.py --data tinystories_corpus_200mb.txt` 接受任意同格式语料文件；
- 论文 B 全部数值结论已固化于 `../logs/formal27000_20260826/` 日志，不依赖语料文件本身可核验。
