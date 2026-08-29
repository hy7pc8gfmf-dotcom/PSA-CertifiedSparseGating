# owt 切分 v2：连续切片（简单可靠）
# 头部 10MB 损坏段跳过 → 连续取 500MB 训练 + 20MB 验证 → 清洗写入
import io, re, time

SRC = r"D:\ComplexAnalysis\Live_harness\AI注意力算法\psa_empirical\新数据\owt_corpus.txt"
OUT_DIR = r"D:\ComplexAnalysis\Live_harness\AI注意力算法\psa_empirical\测试数据"
SKIP_HEAD = 10 * 1024 * 1024
TRAIN_TARGET = 500 * 1024 * 1024
VALID_TARGET = 20 * 1024 * 1024

def clean(text):
    text = re.sub(r'<[^>]+>|https?://\S+', ' ', text)
    return re.sub(r'\s+', ' ', text).strip()

t0 = time.time()
with io.open(SRC, encoding="utf-8", errors="replace") as f:
    f.seek(SKIP_HEAD)
    raw_train = f.read(TRAIN_TARGET)
    raw_valid = f.read(VALID_TARGET)
print(f"读取完成 {time.time()-t0:.0f}s，清洗中...")
t1 = time.time()
c_train = clean(raw_train)
c_valid = clean(raw_valid)
print(f"清洗完成 {time.time()-t1:.0f}s，写入...")
with io.open(OUT_DIR + r"\owt_train_500mb.txt", "w", encoding="utf-8") as f:
    f.write(c_train)
with io.open(OUT_DIR + r"\owt_valid_20mb.txt", "w", encoding="utf-8") as f:
    f.write(c_valid)
print(f"完成: train {len(c_train)/1e6:.0f}MB, valid {len(c_valid)/1e6:.1f}MB, 总耗时 {time.time()-t0:.0f}s")
