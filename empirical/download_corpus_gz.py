#!/usr/bin/env python3
# 流式下载 .gz 语料并即时 gunzip 解压为纯文本（跨平台、无需 head -c）
# 用法: python download_corpus_gz.py <gz_url> <out_txt> [max_decompressed_bytes]
import sys, os, gzip, urllib.request

def main():
    url, out = sys.argv[1], sys.argv[2]
    cap = int(sys.argv[3]) if len(sys.argv) > 3 else 0  # 0 = 不限制解压后字节
    tmp = out + ".part.gz"
    req = urllib.request.Request(url, headers={"User-Agent": "corpus-fetch/1.0"})
    decompressed = 0
    MB = 1024 * 1024
    with urllib.request.urlopen(req, timeout=120) as r, open(tmp, "wb") as gf:
        while True:
            chunk = r.read(1024 * 1024)
            if not chunk:
                break
            gf.write(chunk)
    with gzip.open(tmp, "rb") as gz, open(out, "wb") as wf:
        while True:
            chunk = gz.read(1024 * 1024)
            if not chunk:
                break
            if cap and decompressed + len(chunk) > cap:
                wf.write(chunk[: cap - decompressed])
                decompressed = cap
                break
            wf.write(chunk)
            decompressed += len(chunk)
    os.remove(tmp)
    print(f"OK {out}: {decompressed:,} decompressed bytes")

if __name__ == "__main__":
    main()
