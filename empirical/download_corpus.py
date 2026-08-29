# -*- coding: utf-8 -*-
"""
社区语料流式下载（带字节上限，避免 hf 直连慢/大文件阻塞）。
用法:
  python download_corpus.py <url> <out_path> [cap_bytes]
  cap_bytes=0 表示不截断（下载完整文件）。
特性:
  - 用 urllib（无需额外依赖），自动跟随 302 重定向（hf-mirror 返回 302+Accept-Ranges）。
  - 1MB 分块流式写入，支持随时 SIGPIPE/提前停止。
  - 打印吞吐，便于评估是否放大 cap。
示例（hf-mirror，国内可达）:
  python download_corpus.py "https://hf-mirror.com/datasets/roneneldan/TinyStories/resolve/main/TinyStories-train.txt" "测试数据/tinystories_corpus.txt" 50000000
完整文件:
  python download_corpus.py "https://hf-mirror.com/datasets/roneneldan/TinyStories/resolve/main/TinyStories-train.txt" "测试数据/tinystories_full.txt" 0
BPE 复刻（OpenWebText 样本）:
  python download_corpus.py "https://hf-mirror.com/datasets/stanford-cs336/owt-sample/resolve/main/owt_train.txt.gz" "测试数据/owt_train.txt.gz" 0
"""
import sys, time, urllib.request, os

def main():
    if len(sys.argv) < 3:
        print(__doc__)
        sys.exit(2)
    url, out = sys.argv[1], sys.argv[2]
    cap = int(sys.argv[3]) if len(sys.argv) > 3 else 0
    os.makedirs(os.path.dirname(os.path.abspath(out)), exist_ok=True)
    req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0 (corpus-fetch)"})
    t0 = time.time()
    n = 0
    chunk = 1 << 20  # 1MB
    with urllib.request.urlopen(req, timeout=120) as r, open(out, "wb") as f:
        while True:
            if cap and n >= cap:
                break
            buf = r.read(chunk)
            if not buf:
                break
            if cap:
                buf = buf[: cap - n]
            f.write(buf)
            n += len(buf)
    dt = max(time.time() - t0, 1e-9)
    print(f"[done] bytes={n:,} sec={dt:.1f} MB/s={n/1e6/dt:.2f} -> {out}")

if __name__ == "__main__":
    main()
