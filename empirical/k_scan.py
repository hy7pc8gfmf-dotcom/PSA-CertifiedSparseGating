# -*- coding: utf-8 -*-
"""
k 扫描（B 层：掩码评估）——裁剪点 N* 是否随外推倍数 k 移动
========================================================
T4 推论判别实验：常数论预测 N* 稳定，深度论（变分平衡）预测 N* 随 k 移动。
方法：加载已训练 psi-rope-rand 全频率模型（Gutenberg 3000 iters），评估时把 theta
换成裁剪版（只保留 n <= N 的旋转频率）——纯几何效应近似（不含训练适应）。
判定：每个评估长度 T（= k*512）的最优 N*(T) 是否随 T 移动。
注意：掩码评估是近似；若显示移动，再用真训练（--rand-max 训练时裁剪）验证。
"""
import os, sys, math
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import torch
import length_extrap as le

DEVICE = le.DEVICE

# ---- 语料与 vocab（与模型训练一致：tinystories 3000 iters，vocab=123）----
text = le.load_data("tinystories")
chars = sorted(list(set(text)))
stoi = {c: i for i, c in enumerate(chars)}
data = [stoi[c] for c in text]
split = int(0.9 * len(data))
data_train, data_val = data[:split], data[split:]

config = dict(vocab=len(chars), n_layer=2, n_head=4, n_embd=128,
              lr=3e-4, batch=32, psi_indices=le.gen_indices(128, 4))

MODEL_PATH = le.resolve_model("psi-rope", 512, "_rr")   # s1337 全频率 rand
print("model:", MODEL_PATH, "vocab:", len(chars), flush=True)

# 裁剪点（0 = 不裁剪全保留）与评估长度（k = T/512）
Ns = [0, 224, 256, 288, 320, 352, 384, 416, 448, 480, 511]
Ts = [512, 1024, 2048, 4096]

# 训练时 theta：128 波长 log-uniform [3,511]，循环填充 d/2=64 维
rl_full = [n for n in le.log_uniform_ladder(3, 511, 128, 1337, sort=False) if n <= 512]
ns_full = torch.tensor(rl_full, dtype=torch.float32, device=DEVICE)
half = config["n_embd"] // config["n_head"] // 2
idx = torch.arange(half, device=DEVICE) % len(ns_full)
theta_full = 2.0 * math.pi / ns_full[idx]          # 训练时 theta（每维波长）
assigned = ns_full[idx]                            # 每维分配到的波长（float）

def mask_theta(N):
    """保持每维波长分配不变，仅把分配波长 > N 的维度旋转角归零（静音高频）。"""
    if N == 0:
        return theta_full.clone()
    m = assigned <= N
    return torch.where(m, theta_full, torch.zeros_like(theta_full))

rows = {}
for N in Ns:
    theta = mask_theta(N)
    model = le.build_model("psi-rope", config, 512, theta)
    model.load_state_dict(torch.load(MODEL_PATH, map_location=DEVICE, weights_only=True))
    model.to(DEVICE).eval()
    n_keep = int((assigned <= N).sum()) if N > 0 else len(rl_full)
    label = "full" if N == 0 else f"{N}"
    print(f"--- N={label} (静音 {len(rl_full) - n_keep}/{len(rl_full)} 高频) ---", flush=True)
    for T in Ts:
        nb = 6 if T <= 1024 else 3
        bs = 8 if T <= 1024 else 4
        mean, losses = le.eval_at_length(model, data_val, T, bs, nb, DEVICE, seed=1337 + T)
        ppl = math.exp(mean)
        print(f"  T={T:5d}: loss {mean:.4f}  ppl {ppl:.2f}", flush=True)
        rows[(N, T)] = ppl

print("\n===== 汇总（ppl，掩码评估）=====")
print("N\\T   " + "".join(f"{T:>8d}" for T in Ts))
for N in Ns:
    lab = "full" if N == 0 else f"{N}"
    line = f"{lab:>6s}" + "".join(f"{rows[(N, T)]:>8.2f}" for T in Ts)
    print(line)
for T in Ts:
    best = min(Ns, key=lambda N: rows[(N, T)])
    print(f"T={T} (k={T//512}): 最优 N* = {'full' if best == 0 else best}  (ppl {rows[(best, T)]:.2f})")

# 保存结果
out = os.path.join(os.path.dirname(os.path.abspath(__file__)), "新数据", "k_scan_mask_table.md")
os.makedirs(os.path.dirname(out), exist_ok=True)
with open(out, "w", encoding="utf-8") as f:
    f.write("# k 扫描（掩码评估）：裁剪点 N* 是否随 k 移动（Gutenberg 3000 iters）\n\n")
    f.write("> 方法：加载 psi-rope-rand 全频率模型，评估时换裁剪 theta（纯几何近似）。\n\n")
    f.write("| N \\ T | " + " | ".join(str(t) for t in Ts) + " |\n")
    f.write("|---|" + "---|" * len(Ts) + "\n")
    for N in Ns:
        lab = "full" if N == 0 else f"{N}"
        f.write(f"| {lab} | " + " | ".join(f"{rows[(N, T)]:.2f}" for T in Ts) + " |\n")
    f.write("\n**每 T 最优 N***：\n")
    for T in Ts:
        best = min(Ns, key=lambda N: rows[(N, T)])
        lab = "full" if best == 0 else best
        f.write(f"- T={T} (k={T//512}): N* = {lab} (ppl {rows[(best, T)]:.2f})\n")
print("saved:", out, flush=True)
