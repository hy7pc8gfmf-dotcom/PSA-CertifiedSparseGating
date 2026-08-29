# -*- coding: utf-8 -*-
"""
nanoGPT 实证轨道（PSA v2.1 三路对比）
=====================================
在 char-level mini-GPT 上对比三种注意力：
  1. dense      : 标准因果注意力（torch SDPA, FlashAttention 后端）
  2. gated      : dense 架构 + 贪心能量门控（保留累计能量 >= (1-budget) 的最大项集）
  3. psi-gated  : psi 基位置编码（E_real/E_imag 实虚分离，1/√n 归一）+ 贪心能量门控
指标：验证集困惑度（exp(val_loss)）+ 门控稀疏度（保留 token 比例）。

psi 基（Coq ca_basis.v psi n k = (1/√n)·e^{2πi·k/n}）：
  E_real[k,j] = cos(2π·k/n_j)/√n_j, E_imag[k,j] = sin(2π·k/n_j)/√n_j
基索引 n_j 由生成器 next = max(last*C+1, last+2) 产生（C=4, start=3）。

用法：python mini_gpt_compare.py [--mode all|dense|gated|psi] [--iters 3000]
"""
import argparse, math, os, time, urllib.request

import torch
import torch.nn as nn
import torch.nn.functional as F

torch.manual_seed(1337)
DEVICE = "cuda" if torch.cuda.is_available() else "cpu"

# ---------------- 数据：tiny shakespeare (char-level) ----------------
DATA_URL = "https://raw.githubusercontent.com/karpathy/char-rnn/master/data/tinyshakespeare/input.txt"
DATA_PATH = os.path.join(os.path.dirname(os.path.abspath(__file__)), "tinyshakespeare_input.txt")
PAPER_CORPUS = os.path.join(os.path.dirname(os.path.abspath(__file__)), "paper_corpus.txt")
ARXIV_CORPUS = os.path.join(os.path.dirname(os.path.abspath(__file__)), "arxiv_corpus.txt")
FALLBACK = (
    "The quick brown fox jumps over the lazy dog. Pack my box with five dozen liquor jugs. "
    "How vexingly quick daft zebras jump! The five boxing wizards jump quickly. "
) * 300

def load_data():
    """语料优先级：arxiv 论文语料（大、真实学术英语）> tiny shakespeare > 论文 docx > 内置回退。"""
    for p in (ARXIV_CORPUS, DATA_PATH, PAPER_CORPUS):
        if os.path.exists(p) and os.path.getsize(p) > 100000:
            return open(p, encoding="utf-8").read()
    if not os.path.exists(DATA_PATH):
        ok = False
        try:
            urllib.request.urlretrieve(DATA_URL, DATA_PATH, timeout=30)
            if os.path.getsize(DATA_PATH) > 1000:
                ok = True
        except Exception:
            pass
        if not ok:
            with open(DATA_PATH, "w", encoding="utf-8") as f:
                f.write(FALLBACK)
    return open(DATA_PATH, encoding="utf-8").read()

# ---------------- psi 基嵌入（对应 Coq psi n k） ----------------
def gen_indices(m, C=4, start=3):
    """生成器：next = max(last*C+1, last+2)；与 SeqProps.generate_base_indices 一致。"""
    out = []
    last = start
    for _ in range(m):
        out.append(last)
        last = max(last * C + 1, last + 2)
    return out

def psi_embedding(L, indices, device):
    """E_real/E_imag: (L, m)；psi n k = (1/√n)·e^{2πi k/n}（k<n 恒真，n>=2 且 L 有限）。"""
    n = torch.tensor(indices, dtype=torch.float32, device=device)          # (m,)
    inv_sqrt = 1.0 / torch.sqrt(n)
    k = torch.arange(L, dtype=torch.float32, device=device)[:, None]        # (L,1)
    theta = 2.0 * math.pi * k / n[None, :]                                  # (L,m)
    return torch.cos(theta) * inv_sqrt[None, :], torch.sin(theta) * inv_sqrt[None, :]

# ---------------- 贪心能量门控 ----------------
def greedy_energy_gate(att, budget_frac, causal=True):
    """att: (B,H,T,T) 分数；保留每行累计能量 >= (1-budget) 的最小最大项集（论文 §4 掩码）。
       返回重归一化概率与布尔门。至少保留 1 项；causal 约束下保留位置 <= 对角线。"""
    B, H, T, _ = att.shape
    p = torch.softmax(att, dim=-1)
    if causal:
        tril = torch.tril(torch.ones(T, T, dtype=torch.bool, device=att.device))
        p = p.masked_fill(~tril[None, None], 0.0)
    sorted_p, idx = torch.sort(p, dim=-1, descending=True)
    cum = torch.cumsum(sorted_p, dim=-1)
    keep = cum <= (1.0 - budget_frac)
    keep[..., 0] = True
    gate = torch.zeros_like(p)
    gate.scatter_(-1, idx, keep.to(gate.dtype))
    if causal:
        gate = gate * tril[None, None].to(gate.dtype)
    p_g = gate * p
    p_g = p_g / p_g.sum(-1, keepdim=True).clamp(min=1e-9)
    return p_g, gate

# ---------------- 模型 ----------------
class CausalSelfAttention(nn.Module):
    def __init__(self, n_embd, n_head, block_size, dropout, mode, budget_frac):
        super().__init__()
        self.n_head, self.n_embd, self.block_size = n_head, n_embd, block_size
        self.mode, self.budget_frac = mode, budget_frac
        self.c_attn = nn.Linear(n_embd, 3 * n_embd)
        self.c_proj = nn.Linear(n_embd, n_embd)
        self.dropout = dropout

    def forward(self, x, psi_pos=None):
        B, T, C = x.shape
        qkv = self.c_attn(x)
        q, k, v = qkv.split(C, dim=2)
        q = q.view(B, T, self.n_head, C // self.n_head).transpose(1, 2)
        k = k.view(B, T, self.n_head, C // self.n_head).transpose(1, 2)
        v = v.view(B, T, self.n_head, C // self.n_head).transpose(1, 2)
        if self.mode in ("dense", "psi-dense"):
            y = F.scaled_dot_product_attention(q, k, v, is_causal=True, dropout_p=self.dropout if self.training else 0.0)
        else:
            att = (q @ k.transpose(-2, -1)) * (1.0 / math.sqrt(k.size(-1)))
            p_g, gate = greedy_energy_gate(att, self.budget_frac, causal=True)
            # 稀疏度统计：有效位置（因果三角区内）保留比例
            tril = torch.tril(torch.ones(T, T, dtype=torch.bool, device=att.device))
            valid = tril.sum().item()
            self.last_sparsity = gate[:, :, tril].sum().item() / (B * self.n_head * valid)
            y = p_g @ v
        y = y.transpose(1, 2).contiguous().view(B, T, C)
        return self.c_proj(y)

class Block(nn.Module):
    def __init__(self, n_embd, n_head, block_size, dropout, mode, budget_frac):
        super().__init__()
        self.ln1 = nn.LayerNorm(n_embd)
        self.attn = CausalSelfAttention(n_embd, n_head, block_size, dropout, mode, budget_frac)
        self.ln2 = nn.LayerNorm(n_embd)
        self.mlp = nn.Sequential(
            nn.Linear(n_embd, 4 * n_embd), nn.GELU(), nn.Linear(4 * n_embd, n_embd), nn.Dropout(dropout))

    def forward(self, x, psi_pos=None):
        x = x + self.attn(self.ln1(x), psi_pos)
        x = x + self.mlp(self.ln2(x))
        return x

class MiniGPT(nn.Module):
    def __init__(self, vocab_size, n_layer, n_head, n_embd, block_size, dropout,
                 mode="dense", budget_frac=0.2, psi_indices=None, psi_proj_dim=256):
        super().__init__()
        self.mode, self.block_size = mode, block_size
        self.token_emb = nn.Embedding(vocab_size, n_embd)
        if mode in ("psi", "psi-dense"):
            # psi 位置编码：E_real/E_imag (block_size, m) 拼接 → 学习投影 → n_embd
            m = len(psi_indices) if psi_indices else block_size
            self.psi_m = m
            self.psi_proj = nn.Linear(2 * m, n_embd, bias=False)
            with torch.no_grad():
                er, ei = psi_embedding(block_size, psi_indices or gen_indices(block_size), "cpu")
                self.register_buffer("E_real", er)
                self.register_buffer("E_imag", ei)
            self.pos_emb = None
        else:
            self.pos_emb = nn.Parameter(torch.zeros(1, block_size, n_embd))
        self.blocks = nn.ModuleList([Block(n_embd, n_head, block_size, dropout, mode, budget_frac)
                                     for _ in range(n_layer)])
        self.ln_f = nn.LayerNorm(n_embd)
        self.lm_head = nn.Linear(n_embd, vocab_size, bias=False)
        self.apply(self._init_weights)

    def _init_weights(self, m):
        if isinstance(m, nn.Linear):
            nn.init.normal_(m.weight, std=0.02)
            if m.bias is not None:
                nn.init.zeros_(m.bias)
        elif isinstance(m, nn.Embedding):
            nn.init.normal_(m.weight, std=0.02)

    def forward(self, idx, targets=None):
        B, T = idx.shape
        x = self.token_emb(idx)
        if self.mode in ("psi", "psi-dense"):
            er = self.E_real[:T].to(x.device); ei = self.E_imag[:T].to(x.device)
            psi_pos = self.psi_proj(torch.cat([er, ei], dim=1))       # (T, n_embd)
            x = x + psi_pos.unsqueeze(0)
        else:
            x = x + self.pos_emb[:, :T, :]
        for blk in self.blocks:
            x = blk(x)
        x = self.ln_f(x)
        logits = self.lm_head(x)
        if targets is None:
            return logits, None
        loss = F.cross_entropy(logits.view(-1, logits.size(-1)), targets.view(-1))
        return logits, loss

# ---------------- 训练 ----------------
def get_batch(data, ix, block_size, batch_size, device):
    x = torch.stack([torch.tensor(data[i:i+block_size], dtype=torch.long) for i in ix])
    y = torch.stack([torch.tensor(data[i+1:i+1+block_size], dtype=torch.long) for i in ix])
    return x.to(device), y.to(device)

@torch.no_grad()
def estimate_loss(model, data_train, data_val, block_size, batch_size, eval_iters, device):
    model.eval()
    out = {}
    for split, data in (("train", data_train), ("val", data_val)):
        losses = []
        n = len(data) - block_size - 1
        for _ in range(eval_iters):
            ix = torch.randint(0, n, (batch_size,))
            x, y = get_batch(data, ix.tolist(), block_size, batch_size, device)
            _, loss = model(x, y)
            losses.append(loss.item())
        out[split] = sum(losses) / len(losses)
    model.train()
    return out

def run_mode(mode, iters, config, data_train, data_val, block_size, device):
    torch.manual_seed(1337)
    model = MiniGPT(vocab_size=config["vocab_size"], n_layer=config["n_layer"],
                    n_head=config["n_head"], n_embd=config["n_embd"], block_size=block_size,
                    dropout=config["dropout"], mode=mode, budget_frac=config["budget_frac"],
                    psi_indices=config["psi_indices"], psi_proj_dim=config["psi_proj_dim"]).to(device)
    n_param = sum(p.numel() for p in model.parameters())
    optimizer = torch.optim.AdamW(model.parameters(), lr=config["lr"])
    n = len(data_train) - block_size - 1
    t0 = time.time()
    best_val = float("inf")
    for step in range(iters):
        ix = torch.randint(0, n, (config["batch_size"],))
        x, y = get_batch(data_train, ix.tolist(), block_size, config["batch_size"], device)
        _, loss = model(x, y)
        optimizer.zero_grad()
        loss.backward()
        optimizer.step()
        if step % config["eval_interval"] == 0 or step == iters - 1:
            m = estimate_loss(model, data_train, data_val, block_size, config["batch_size"],
                              config["eval_iters"], device)
            best_val = min(best_val, m["val"])
            el = time.time() - t0
            spar = getattr(model.blocks[0].attn, "last_sparsity", None)
            spar_s = f" sparsity={spar:.3f}" if spar is not None else ""
            print(f"  [{mode}] step {step:5d} train {m['train']:.4f} val {m['val']:.4f} "
                  f"ppl {math.exp(m['val']):.2f} ({el:.0f}s){spar_s}", flush=True)
    return {"mode": mode, "val_loss": best_val, "ppl": math.exp(best_val), "params": n_param,
            "seconds": time.time() - t0}

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--mode", default="all", choices=["all", "dense", "gated", "psi", "psi-dense"])
    ap.add_argument("--iters", type=int, default=3000)
    ap.add_argument("--budget", type=float, default=0.2)
    ap.add_argument("--n-embd", type=int, default=128)
    ap.add_argument("--n-layer", type=int, default=2)
    ap.add_argument("--block", type=int, default=256)
    args = ap.parse_args()

    text = load_data()
    chars = sorted(list(set(text)))
    stoi = {c: i for i, c in enumerate(chars)}
    data = [stoi[c] for c in text]
    split = int(0.9 * len(data))
    data_train, data_val = data[:split], data[split:]
    block_size = args.block

    psi_idx = gen_indices(128, C=4, start=3)   # 与 generate_base_indices 一致（C=4, start=3）
    config = dict(vocab_size=len(chars), n_layer=args.n_layer, n_head=4, n_embd=args.n_embd,
                  dropout=0.1, budget_frac=args.budget, lr=3e-4, batch_size=64,
                  eval_interval=500, eval_iters=100, psi_indices=psi_idx, psi_proj_dim=256)

    print(f"device={DEVICE} vocab={len(chars)} data={len(data)} chars iters={args.iters}")
    print(f"psi indices (C=4, start=3): {psi_idx[:8]}...")

    modes = ["dense", "psi-dense", "gated", "psi"] if args.mode == "all" else [args.mode]
    results = []
    for mode in modes:
        print(f"===== mode={mode} =====")
        results.append(run_mode(mode, args.iters, config, data_train, data_val, block_size, DEVICE))

    print("\n===== 对比汇总 =====")
    print(f"{'mode':<10}{'params':>10}{'val_loss':>12}{'ppl':>10}{'seconds':>10}")
    for r in results:
        print(f"{r['mode']:<10}{r['params']:>10}{r['val_loss']:>12.4f}{r['ppl']:>10.2f}{r['seconds']:>10.0f}")
    print(f"门控稀疏度（budget={args.budget}）：每行保留 >= {int((1-args.budget)*100)}% 累计能量")

if __name__ == "__main__":
    main()
