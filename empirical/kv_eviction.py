# -*- coding: utf-8 -*-
"""
证书引导的 KV 逐出模拟（评审 5 方向 4，P1）
============================================
用论文 A 的 row_dropped_energy_bound 直觉：丢弃谱能量 ≤ ε 的 KV ⟹ 输出偏差
≤ (e^{2√ε}−1)·V_max。远距 KV 因 psi 基的衰减界（decay_bound）能量低——本脚本
模拟"按距离丢弃远距 KV"（保留最近 W 个），报告 8×（T=4096）外推 PPL vs W 曲线，
验证：证书保证的输出不变性是否在 ppl 上体现（甚至因去噪微降）。

用法：python kv_eviction.py [--mode psi-rope] [--block 512] [--T 4096]
      [--seeds 1337,42,7] [--windows 512,256,128,64]
依赖：已训练的 psi-rope 模型（model_psi-rope_b512*.pt，测试数据/）。
温控：同 length_extrap（ThermalGuard 0.5s 探测，gpu-max 58 / resume 52）。
"""
import argparse, math, os, sys, time
os.environ.setdefault("OMP_NUM_THREADS", "2")
os.environ.setdefault("MKL_NUM_THREADS", "2")
import torch
torch.set_num_threads(2)
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from thermal import ThermalGuard
import length_extrap as le

def eval_kv_window(model, data_val, T, W, batch_size, n_batches, device, loss_window=None):
    """评估：attention 只保留最近 W 个 key/value（丢弃更远 KV），query 全保留；
    loss 只算尾部 loss_window 个位置（默认 = W——这些位置有完整 W 上下文）。
    评审 11 修正：比较不同 W 时必须固定 loss 位置集合——调用传 loss_window=64，
    W 独立变化（{512,256,128,64}），所有 loss 位置在任何 W≥64 下都有完整上下文。"""
    model.eval()
    for m in model.modules():
        if isinstance(m, le.CausalSelfAttention):
            m.kv_window = W
    losses = []
    n = len(data_val) - T - 1
    for _ in range(n_batches):
        ix = torch.randint(0, max(n, 1), (batch_size,))
        x = torch.stack([torch.tensor(data_val[i:i+T], dtype=torch.long) for i in ix]).to(device)
        y = torch.stack([torch.tensor(data_val[i+1:i+1+T], dtype=torch.long) for i in ix]).to(device)
        logits, _ = model(x, None)
        lw = loss_window if loss_window is not None else (W if W is not None and T > W else T)
        if lw < T:
            loss = torch.nn.functional.cross_entropy(
                logits[:, -lw:].reshape(-1, logits.size(-1)), y[:, -lw:].reshape(-1))
        else:
            loss = torch.nn.functional.cross_entropy(
                logits.reshape(-1, logits.size(-1)), y.reshape(-1))
        losses.append(loss.item())
    for m in model.modules():
        if isinstance(m, le.CausalSelfAttention):
            m.kv_window = None
    model.train()
    return sum(losses) / len(losses)

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--mode", type=str, default="psi-rope")
    ap.add_argument("--block", type=int, default=512)
    ap.add_argument("--T", type=int, default=4096)
    ap.add_argument("--windows", type=str, default="512,256,128,64")
    ap.add_argument("--seeds", type=str, default="1337,42,7")
    ap.add_argument("--gpu-max", type=float, default=58.0)
    ap.add_argument("--gpu-resume", type=float, default=52.0)
    args = ap.parse_args()

    guard = ThermalGuard(gpu_max=args.gpu_max, gpu_resume=args.gpu_resume, verbose=True)
    text = le.load_data()
    chars = sorted(list(set(text)))
    stoi = {c: i for i, c in enumerate(chars)}
    data = [stoi[c] for c in text]
    split = int(0.9 * len(data))
    data_train, data_val = data[:split], data[split:]
    psi_ladder = le.gen_indices(128, 4)
    config = dict(vocab=len(chars), n_layer=2, n_head=4, n_embd=128,
                  lr=3e-4, batch=32, psi_indices=psi_ladder)
    theta = le.psi_rope_theta(32, le.DEVICE, [n for n in psi_ladder if n <= args.block])
    windows = [int(w) for w in args.windows.split(",")]
    seeds = [int(s) for s in args.seeds.split(",")]
    LOSS_WIN = 64   # 评审 11 修正：固定 loss 评估窗口（尾部 64 位置），W 独立变化

    print(f"===== KV 逐出模拟 mode={args.mode} T={args.T} windows={windows} seeds={seeds} =====", flush=True)
    print(f"T={args.T:5d} " + "  ".join(f"W={w:5d}" for w in windows) + "   (full=512)", flush=True)
    print(f"[评审 11 修正] loss 固定尾部 {LOSS_WIN} 位置（各 W 下相同评估点），W 独立变化——纯逐出净效应", flush=True)
    for seed in seeds:
        tag = f"_s{seed}" if seed != 1337 else ""
        path = le.resolve_model(args.mode, args.block, tag)
        if not os.path.exists(path):
            print(f"  [seed {seed}] 模型不存在: {path}", flush=True)
            continue
        model = le.build_model(args.mode, config, args.block, theta)
        model.load_state_dict(torch.load(path, map_location=le.DEVICE, weights_only=True))
        model.to(le.DEVICE).eval()
        row = []
        for W in windows:
            loss = eval_kv_window(model, data_val, args.T, W, 4, 2, le.DEVICE, loss_window=LOSS_WIN)
            row.append((W, loss, math.exp(loss)))
            print(f"  [s{seed}] W={W:5d}: loss {loss:.4f}  ppl {math.exp(loss):.2f}", flush=True)
            guard.check(f"kv-eval s{seed} W={W}")
        # full（不截断）基线：同一固定 loss 窗口
        loss_full = eval_kv_window(model, data_val, args.T, 10**6, 4, 2, le.DEVICE, loss_window=LOSS_WIN)
        print(f"  [s{seed}] W=full: loss {loss_full:.4f}  ppl {math.exp(loss_full):.2f}", flush=True)
    guard.stop()

if __name__ == "__main__":
    main()
