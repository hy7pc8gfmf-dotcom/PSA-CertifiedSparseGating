# -*- coding: utf-8 -*-
"""提取确定性自检：对代表集重新 Extraction，与 repo 跟踪的生成物逐字节 diff。
不一致 = 源与生成物漂移（退出码 1）。
用法: python scripts/check_extraction_determinism.py [--full]
  quick（默认）: C 系列四件（coqc 9.1 + Q 层自足，秒级）
  --full       : 全部 constructive-Q 件（需逐件编译，分钟级）
铁律 E250: 落盘脚本；临时产物进系统 temp，不污染 repo。
"""
import os, re, subprocess, sys, tempfile, hashlib

REPO = r"D:\ComplexAnalysis\PSA-CertifiedSparseGating"
PROBES = os.path.join(REPO, "coq", "probes")
# 提取器可经环境变量覆盖——入库生成物与检查必须同一提取器版本，
# 否则头部/编码差异会诱发环境性假警报（源未变）。
COQC = os.environ.get("COQC", r"C:\Rocq-Platform~9.1~2026.01\bin\coqc.exe")

QUICK = ["qset_twin_base", "probe_rc_envelope", "probe_gershgorin_qtw", "probe_pareto_qtw"]
FULL_EXTRA = ["probe_taugrid_cr", "probe_c4_four_atom_cr", "probe_safe_domain",
              "probe_c4_unique2sparse_cr", "probe_c4_gram_unique_cr", "probe_g11_checkiff_cr",
              "probe_g13_certtight_cr", "probe_g9_pairfrac_cr", "probe_itv_noisyor_cr",
              "probe_z_frame_check", "probe_z2b_int63mirror"]
# 源 .v -> 产物名映射（Extraction "X.ml"）
def extraction_target(src_path):
    with open(src_path, encoding="utf-8", errors="replace") as f:
        m = re.search(r'^Extraction\s+"([^"]+\.ml)"', f.read(), re.M)
    return m.group(1)[:-3] if m else None

def sha(p):
    return hashlib.sha256(open(p, "rb").read()).hexdigest()

def check_one(src_base):
    src = os.path.join(PROBES, src_base + ".v")
    assert os.path.isfile(src), "缺源 " + src
    out_name = extraction_target(src)
    assert out_name, src_base + " 无 Extraction 命令"
    with tempfile.TemporaryDirectory() as tmp:
        r = subprocess.run([COQC, "-q", "-Q", PROBES, "", "-output-directory", tmp, src],
                           capture_output=True, text=True, timeout=300)
        ok_files, drift = [], []
        for ext in (".ml", ".mli"):
            gen = os.path.join(tmp, out_name + ext)
            tracked = os.path.join(PROBES, out_name + ext)
            if not os.path.isfile(tracked):
                drift.append((out_name + ext, "repo 未跟踪"))
                continue
            if not os.path.isfile(gen):
                drift.append((out_name + ext, "本次未生成（提取命令未覆盖该扩展名）"))
                continue
            if sha(gen) == sha(tracked):
                ok_files.append(out_name + ext)
            else:
                drift.append((out_name + ext, "SHA 漂移"))
        return src_base, out_name, ok_files, drift

def main():
    full = "--full" in sys.argv
    targets = QUICK + (FULL_EXTRA if full else [])
    total_ok, total_drift = 0, []
    for b in targets:
        src_base, out, ok, drift = check_one(b)
        total_ok += len(ok)
        total_drift.extend((src_base,) + d for d in drift)
        status = "PASS" if not drift else "DRIFT"
        print("%-28s %-22s %s  ok=%s" % (src_base, out, status, ",".join(ok) or "-"))
    print("---")
    if total_drift:
        print("DRIFT 明细:")
        for s, f, why in total_drift:
            print("  %s: %s (%s)" % (s, f, why))
        print("结论: 源与生成物漂移 %d 处——先再生（make extract）再入库" % len(total_drift))
        sys.exit(1)
    print("结论: 确定性自检通过（%d 件生成物与源逐字节一致）" % total_ok)

if __name__ == "__main__":
    main()
