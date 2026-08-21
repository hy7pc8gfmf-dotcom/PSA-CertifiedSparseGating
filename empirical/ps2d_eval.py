# -*- coding: utf-8 -*-
"""
2D patch 外推评估（评审 5 方向 6 / 论文 B §6 假说，2026-08-21 会话 18）
================================================================
假说：「截断应逐轴独立」——2D 张量积位置编码 φ2D(i,j)(k) = ψ_i(k)·ψ_j(k) 在 OOD
窗口 T 处，任一轴携带过长频带（n > T，相位不完备）都会破坏轴间可比性（H_dom）
⟹ 外推崩坏。评估两种截断策略：
  (A) 仅截断长轴：只丢弃 j 轴（或指定轴）n > T 的带，i 轴保留全部训练带（含 n > T）；
  (B) 双轴独立截断：两轴各自丢弃 n > T 的带（论文假说的处方）。
实现：截断 = 特征掩码（被丢带的特征通道置零，投影层形状不变——避免重训投影）。
用法：python ps2d_eval.py [--model 测试数据/model_2d_trunc.pth] [--trunc 16,16]
      [--gpu-max 79 --gpu-resume 69]  （温控必须覆盖默认 58/52！）
输出：T × (A/B) ppl 对比表。
"""
import argparse, math, os, sys, time

os.environ.setdefault("OMP_NUM_THREADS", "2")
os.environ.setdefault("MKL_NUM_THREADS", "2")
import torch
torch.set_num_threads(2)
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from thermal import ThermalGuard
import length_extrap as le
import ps2d_exp as p2

def mask_features(T, idx_i, idx_j, axis_drop):
    """返回 2·(mi·mj) 维布尔掩码：True = 保留。axis_drop='j' 仅丢 j 轴 n>T（A 策略），
    'both' 两轴都丢 n>T（B 策略）。"""
    mask = []
    for i in idx_i:
        for j in idx_j:
            keep = True
            if axis_drop in ("j", "both") and j > T:
                keep = False
            if axis_drop == "both" and i > T:
                keep = False
            mask += [keep, keep]  # 实/虚部
    return torch.tensor(mask, dtype=torch.bool)

@torch.no_grad()
def eval_at(model, data_val, T, idx_i, idx_j, mask, batch_size, n_batches, device):
    model.eval()
    losses = []
    n = len(data_val) - T - 1
    er, ei = p2.psi2d_embedding(T, idx_i, idx_j, device)
    feat = torch.cat([er, ei], dim=1)
    feat = feat * mask.to(device).float()          # 掩码截断
    feat = feat.unsqueeze(0)
    for _ in range(n_batches):
        ix = torch.randint(0, max(n, 1), (batch_size,))
        x = torch.stack([torch.tensor(data_val[i:i+T], dtype=torch.long) for i in ix]).to(device)
        y = torch.stack([torch.tensor(data_val[i+1:i+1+T], dtype=torch.long) for i in ix]).to(device)
        h = model.token_emb(x) + model.pos_proj(feat)
        for blk in model.blocks:
            h = blk(h)
        for ln1, attn, ln2 in model.attn_blocks:
            h = h + attn(ln1(h))
            h = ln2(h)
        logits = model.lm_head(model.ln_f(h))
        loss = torch.nn.functional.cross_entropy(logits.view(-1, logits.size(-1)), y.view(-1))
        losses.append(loss.item())
    model.train()
    return sum(losses) / len(losses)

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--model", default=os.path.join(le.HERE, "model_2d_trunc.pth"))
    ap.add_argument("--block", type=int, default=256)
    ap.add_argument("--trunc", type=str, default="16,16")
    ap.add_argument("--n-patches", type=int, default=4096)
    ap.add_argument("--patch", type=int, default=8)
    ap.add_argument("--vocab", type=int, default=16)
    ap.add_argument("--noise", type=float, default=0.0)
    ap.add_argument("--attn", action="store_true")
    ap.add_argument("--gpu-max", type=float, default=79.0)      # 覆盖默认 58！
    ap.add_argument("--gpu-resume", type=float, default=69.0)
    args = ap.parse_args()
    guard = ThermalGuard(gpu_max=args.gpu_max, gpu_resume=args.gpu_resume, verbose=True)

    if not os.path.exists(args.model):
        print(f"模型不存在：{args.model}。先跑 ps2d_exp.py 训练。", flush=True)
        sys.exit(2)
    data, grid = p2.build_data(args.n_patches, args.patch, vocab=args.vocab, noise=args.noise)
    split = int(0.9 * len(data))
    data_val = data[split:]
    vocab = args.vocab
    ti, tj = [int(v) for v in args.trunc.split(",")]
    ladder = le.gen_indices(32, 4)
    idx_i, idx_j = ladder[:ti], ladder[:tj]

    model = p2.MiniGPT2D(vocab, 2, 64, args.block, idx_i, idx_j, attn=args.attn).to(le.DEVICE)
    model.load_state_dict(torch.load(args.model, map_location=le.DEVICE, weights_only=True))
    model.eval()

    print(f"===== 2D 截断策略对比（模型 {os.path.basename(args.model)}，训练块 {args.block}，"
          f"i 轴 {ti} 带 / j 轴 {tj} 带）=====", flush=True)
    print(f"{'T':>6} | {'A 仅截断长轴':>12} | {'B 双轴独立截断':>12} | 差值(A−B)", flush=True)
    for T in (256, 512, 1024, 2048, 4096):
        mask_a = mask_features(T, idx_i, idx_j, "j")     # A：仅丢 j 轴 n>T
        mask_b = mask_features(T, idx_i, idx_j, "both")  # B：两轴都丢 n>T
        nb = 4 if T <= 1024 else 2
        bs = 8 if T <= 1024 else 4
        la = eval_at(model, data_val, T, idx_i, idx_j, mask_a, bs, nb, le.DEVICE)
        guard.check(f"2d eval A T={T}")
        lb = eval_at(model, data_val, T, idx_i, idx_j, mask_b, bs, nb, le.DEVICE)
        guard.check(f"2d eval B T={T}")
        print(f"{T:>6} | {math.exp(la):>12.2f} | {math.exp(lb):>12.2f} | {math.exp(la)-math.exp(lb):+10.2f}", flush=True)
    guard.stop()
    print("\n解读：B 显著优于 A（A−B > 0 且随 T 增大）⟹ 逐轴独立截断成立；"
          "A 保留单轴 n>T 不完备带 ⟹ H_dom 破坏 ⟹ 外推崩坏（论文 B §6 假说实证）。")

if __name__ == "__main__":
    main()
