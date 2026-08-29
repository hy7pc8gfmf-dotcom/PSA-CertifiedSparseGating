# -*- coding: utf-8 -*-
"""
从 arxiv 下载论文 PDF 构建英文语料（实证轨道，v2：PDF 路线）
======================================================
export.arxiv.org/pdf/{id}（可达）-> pypdf 提取文本。
用法：python arxiv_corpus.py --n 20 [--query ...] [--start 0]
"""
import os, time, urllib.parse, urllib.request
import xml.etree.ElementTree as ET
from pypdf import PdfReader
import io

BASE_API = "https://export.arxiv.org/api/query"
HERE = os.path.dirname(os.path.abspath(__file__))
OUT_DIR = os.path.join(HERE, "arxiv_papers")
CORPUS = os.path.join(HERE, "arxiv_corpus.txt")
NS = {"a": "http://www.w3.org/2005/Atom"}

def fetch_ids(query, n, start):
    url = BASE_API + "?" + urllib.parse.urlencode(
        {"search_query": query, "start": start, "max_results": n, "sortBy": "submittedDate"})
    req = urllib.request.Request(url, headers={"User-Agent": "psa-empirical/0.2"})
    with urllib.request.urlopen(req, timeout=25) as r:
        root = ET.fromstring(r.read().decode("utf-8"))
    return [e.find("a:id", NS).text.split("/abs/")[-1].split("v")[0] for e in root.findall("a:entry", NS)]

def download_pdf(arxiv_id):
    url = f"https://export.arxiv.org/pdf/{arxiv_id}"
    req = urllib.request.Request(url, headers={"User-Agent": "psa-empirical/0.2"})
    with urllib.request.urlopen(req, timeout=60) as r:
        return r.read()

def pdf_to_text(data):
    try:
        reader = PdfReader(io.BytesIO(data))
        parts = []
        for page in reader.pages:
            t = page.extract_text() or ""
            parts.append(t)
        return "\n".join(parts)
    except Exception as e:
        return ""

def main():
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=20)
    ap.add_argument("--query", default='cat:cs.CL AND abs:transformer')
    ap.add_argument("--out", default=CORPUS)
    args = ap.parse_args()

    os.makedirs(OUT_DIR, exist_ok=True)
    ids = fetch_ids(args.query, args.n, 0)
    print(f"got {len(ids)} ids: {ids[:5]}...", flush=True)

    all_text = []
    for i, pid in enumerate(ids):
        safe = pid.replace("/", "_")
        path = os.path.join(OUT_DIR, f"{safe}.pdf")
        if os.path.exists(path):
            data = open(path, "rb").read()
        else:
            try:
                data = download_pdf(pid)
                if len(data) < 5000:
                    print(f"  [{i}] {pid}: too small ({len(data)}B), skip", flush=True)
                    continue
                open(path, "wb").write(data)
            except Exception as e:
                print(f"  [{i}] {pid}: download fail {str(e)[:50]}", flush=True)
                continue
            time.sleep(2)
        txt = pdf_to_text(data)
        if len(txt) < 3000:
            print(f"  [{i}] {pid}: text too short ({len(txt)}), skip", flush=True)
            continue
        all_text.append(f"\n\n===== PAPER {pid} =====\n" + txt)
        print(f"  [{i}] {pid}: {len(txt)} chars", flush=True)

    corpus = "".join(all_text)
    with open(args.out, "w", encoding="utf-8") as f:
        f.write(corpus)
    print(f"\ncorpus: {len(corpus)} chars -> {args.out}", flush=True)

if __name__ == "__main__":
    main()
