# -*- coding: utf-8 -*-
"""
2D 图像 patch 验证（评审 5 方向 6，P2）："截断应逐轴独立"假说
================================================================
论文 B §6 假说：轴间可比性（H_dom）破坏 ⟹ 外推崩坏；截断必须逐轴独立执行。
本脚本用 2D 合成 patch 数据验证：二维频率阶梯 (i,j) 满足 max(i,j) ≤ T_train 训练，
外推时（A）仅截断长轴 vs（B）两轴同时截断 的困惑度对比。

2D 位置编码 = 论文 A §5.4 的二维张量积：φ2D(i,j)(k) = γ⁻¹·ψ_i(k)·ψ_j(k)
（ψ_n(k) = (1/√n)·e^{2πik/n}，n 为阶梯频带；γ = √(min(i,j)/(ij))）。

用法：python ps2d_exp.py [--patch 8] [--iters 3000] [--trunc-axis 16,16]
温控：同 length_extrap（ThermalGuard 0.5s 探测）。
"""
import argparse, math, os, sys, time
os.environ.setdefault("OMP_NUM_THREADS", "2")
os.environ.setdefault("MKL_NUM_THREADS", "2")
import torch
torch.set_num_threads(2)
import torch.nn as nn
import torch.nn.functional as F
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from thermal import ThermalGuard
import length_extrap as le

# ---------- 2D 合成 patch 数据 ----------
def gen_patch_sequence(n_patches, patch, seed=1337):
    """确定性 2D patch 序列：值 = 双频正弦纹理 + 相位扰动（量化到 vocab）。
    patch 序列按行主序展平；每个 patch 是一个 token（值量化）。"""
    rng = torch.Generator().manual_seed(seed)
    rows = cols = int(math.sqrt(n_patches * patch * patch / (patch * patch)))  # 网格边长（patch 数）
    grid = int(math.sqrt(n_patches))
    seq = []
    for t in range(n_patches):
        i, j = t % grid, t // grid
        # 双频正弦纹理（patch 内 8 个像素值 → 量化 8 级）
        vals = []
        for a in range(patch):
            for b in range(patch):
                v = (math.sin(2 * math.pi * (i * patch + a) / (grid * patch))
                     + math.sin(2 * math.pi * (j * patch + b) / (grid * patch))) / 2
                vals.append(int(round((v + 1) / 2 * 7)))
        seq.append(tuple(vals))
    return seq  # list of (patch*patch,) tuples —— 每个 patch 展平成 64 个像素 token

# 简化：把每个 patch 当作一个超 token（patch² 像素展平为 vocab 序列，类似字符流）
def build_data(n_patches=4096, patch=8, seed=1337, vocab=16, noise=0.0):
    """2D 合成 patch 数据（难任务版，会话 18）：vocab 量化级 + 高斯噪声参数化。
    vocab 越大、patch 越小、噪声越大 → 任务越难（产生外推压力，避免天花板）。"""
    rng = torch.Generator().manual_seed(seed)
    grid = int(math.sqrt(n_patches))
    flat = []
    for t in range(n_patches):
        i, j = t % grid, t // grid
        for a in range(patch):
            for b in range(patch):
                v = (math.sin(2 * math.pi * (i * patch + a) / (grid * patch))
                     + math.sin(2 * math.pi * (j * patch + b) / (grid * patch))) / 2
                if noise > 0:
                    v += torch.randn(1, generator=rng).item() * noise
                q = int(round((v + 1) / 2 * (vocab - 1)))
                flat.append(max(0, min(vocab - 1, q)))
    return flat, grid

# ---------- 2D psi 位置编码 ----------
def psi2d_embedding(L, idx_i, idx_j, device):
    """二维张量积位置编码：φ2D(i,j)(k) = γ⁻¹ ψ_i(k) ψ_j(k)（i 轴/ j 轴各取阶梯频带）。
    返回实虚部对（每个位置 k 一个 2·m_i·m_j 维嵌入）。"""
    ni = torch.tensor(idx_i, dtype=torch.float32, device=device)
    nj = torch.tensor(idx_j, dtype=torch.float32, device=device)
    k = torch.arange(L, dtype=torch.float32, device=device)[:, None]   # (L,1)
    # ψ_n(k) = cos(2πk/n)/√n + i·sin(2πk/n)/√n；张量积 → 每个 (p,q) 一列
    ci = torch.cos(2 * math.pi * k / ni[None, :]) / torch.sqrt(ni[None, :])   # (L, mi)
    si = torch.sin(2 * math.pi * k / ni[None, :]) / torch.sqrt(ni[None, :])
    cj = torch.cos(2 * math.pi * k / nj[None, :]) / torch.sqrt(nj[None, :])   # (L, mj)
    sj = torch.sin(2 * math.pi * k / nj[None, :]) / torch.sqrt(nj[None, :])
    # 实部 = ci*cj - si*sj；虚部 = ci*sj + si*cj（张量积 φ2D 的实虚部，γ 归一省略）
    er = (ci[:, :, None] * cj[:, None, :] - si[:, :, None] * sj[:, None, :]).reshape(L, -1)
    ei = (ci[:, :, None] * sj[:, None, :] + si[:, :, None] * cj[:, None, :]).reshape(L, -1)
    return er, ei

class MiniGPT2D(nn.Module):
    def __init__(self, vocab, n_layer, n_embd, block, idx_i, idx_j, n_head=4, attn=False):
        super().__init__()
        self.idx_i, self.idx_j = idx_i, idx_j
        self.attn = attn
        self.token_emb = nn.Embedding(vocab, n_embd)
        m = len(idx_i) * len(idx_j)
        self.pos_proj = nn.Linear(2 * m, n_embd, bias=False)
        self.blocks = nn.ModuleList([
            nn.Sequential(nn.LayerNorm(n_embd),
                          nn.Linear(n_embd, 4 * n_embd), nn.GELU(),
                          nn.Linear(4 * n_embd, n_embd),
                          nn.LayerNorm(n_embd))
            for _ in range(n_layer)])   # 纯位置编码 + MLP（验证位置结构，非注意力）
        self.attn_blocks = nn.ModuleList([
            nn.ModuleList([nn.LayerNorm(n_embd),
                           le.CausalSelfAttention(n_embd, n_head, "nope", None),   # 无位置旋转（2D 位置在嵌入）
                           nn.LayerNorm(n_embd)])
            for _ in range(n_layer)]) if attn else nn.ModuleList()
        self.ln_f = nn.LayerNorm(n_embd)
        self.lm_head = nn.Linear(n_embd, vocab, bias=False)
    def forward(self, idx, targets=None):
        B, T = idx.shape
        x = self.token_emb(idx)
        er, ei = psi2d_embedding(T, self.idx_i, self.idx_j, idx.device)
        x = x + self.pos_proj(torch.cat([er, ei], dim=1)).unsqueeze(0)
        for blk in self.blocks:
            x = blk(x)
        for ln1, attn, ln2 in self.attn_blocks:
            x = x + attn(ln1(x))
            x = ln2(x)
        logits = self.lm_head(self.ln_f(x))
        if targets is None:
            return logits, None
        return logits, F.cross_entropy(logits.view(-1, logits.size(-1)), targets.view(-1))

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--iters", type=int, default=3000)
    ap.add_argument("--block", type=int, default=256)
    ap.add_argument("--n-embd", type=int, default=64)
    ap.add_argument("--n-layer", type=int, default=2)
    ap.add_argument("--n-patches", type=int, default=4096)
    ap.add_argument("--patch", type=int, default=8)
    ap.add_argument("--trunc", type=str, default="16,16")   # 训练时二维阶梯截断（i,j 各取前 n 带）
    ap.add_argument("--vocab", type=int, default=16)        # 难任务：量化级数（64 = 更细）
    ap.add_argument("--noise", type=float, default=0.0)     # 难任务：高斯噪声
    ap.add_argument("--attn", action="store_true")          # 难任务：加自注意力层
    ap.add_argument("--gpu-max", type=float, default=79.0)
    ap.add_argument("--gpu-resume", type=float, default=69.0)
    ap.add_argument("--eval-only", type=str, default="")
    args = ap.parse_args()
    guard = ThermalGuard(gpu_max=args.gpu_max, gpu_resume=args.gpu_resume, verbose=True)

    data, grid = build_data(args.n_patches, args.patch, vocab=args.vocab, noise=args.noise)
    split = int(0.9 * len(data))
    data_train, data_val = data[:split], data[split:]
    vocab = args.vocab
    ti, tj = [int(v) for v in args.trunc.split(",")]
    # 二维阶梯：C=4 生成器取前 ti/tj 带（与论文 A 2D 张量积一致）
    ladder = le.gen_indices(32, 4)
    idx_i, idx_j = ladder[:ti], ladder[:tj]
    config = dict(vocab=vocab, n_layer=args.n_layer, n_embd=args.n_embd)
    print(f"2D patch 实验：grid={grid} patch={args.patch} vocab={vocab} noise={args.noise} attn={args.attn} "
          f"阶梯截断 i≤{ti}(带{idx_i[:4]}...) j≤{tj}(带{idx_j[:4]}...) "
          f"gpu_max={args.gpu_max}", flush=True)

    model = MiniGPT2D(vocab, args.n_layer, args.n_embd, args.block, idx_i, idx_j,
                      attn=args.attn).to(le.DEVICE)
    opt = torch.optim.AdamW(model.parameters(), lr=3e-4)
    n = len(data_train) - args.block - 1
    t0 = time.time()
    for step in range(args.iters):
        ix = torch.randint(0, n, (32,))
        x = torch.stack([torch.tensor(data_train[i:i+args.block], dtype=torch.long) for i in ix]).to(le.DEVICE)
        y = torch.stack([torch.tensor(data_train[i+1:i+1+args.block], dtype=torch.long) for i in ix]).to(le.DEVICE)
        _, loss = model(x, y)
        opt.zero_grad(); loss.backward(); opt.step()
        if step % 500 == 0 or step == args.iters - 1:
            print(f"  step {step:5d} train {loss.item():.4f} ({time.time()-t0:.0f}s)", flush=True)
        guard.check(f"2d step {step}")
    guard.stop()
    torch.save(model.state_dict(), os.path.join(le.HERE, "model_2d_trunc.pth"))
    print("DONE 训练完成。外推评估（A 仅截断长轴 vs B 双轴截断）见下一步脚本。", flush=True)

if __name__ == "__main__":
    main()
