# -*- coding: utf-8 -*-
"""
长度外推实验（引爆点 1）：psi 基位置编码 vs 可学习位置编码
=========================================================
训练 T=512，评估 T=512/1024/2048/4096。
- dense     : 可学习位置编码（表，超出训练长度用 0 填充——标准 OOD 崩溃对照）
- psi-dense : psi 基位置编码（函数，e^{2πik/n} 对任意 k 定义，动态计算任意长度）
语料：gutenberg_corpus.txt（572 万字符公版小说）。
用法：python length_extrap.py [--iters 3000] [--block 512]
"""
import argparse, math, os, sys, time
# 训练约束 v2：在 torch 导入前限制 CPU 线程（防多核满载过热，见交接文档第二节）
os.environ.setdefault("OMP_NUM_THREADS", "2")
os.environ.setdefault("MKL_NUM_THREADS", "2")
import torch
torch.set_num_threads(2)
import torch.nn as nn
import torch.nn.functional as F

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from thermal import ThermalGuard

DATA_DIR = os.path.join(HERE, "测试数据")   # 测试数据已归档到子目录（2026-08-19）

def resolve_data(name):
    """数据路径回退：先 HERE 根，再 HERE/测试数据（兼容归档前后）。"""
    p = os.path.join(HERE, name)
    if os.path.exists(p):
        return p
    q = os.path.join(DATA_DIR, name)
    if os.path.exists(q):
        return q
    return p   # 返回主路径，让调用方报缺失

def resolve_model(mode, block, tag):
    """模型路径回退：先 HERE 根，再 HERE/测试数据。"""
    base = f"model_{mode}_b{block}{tag}.pt"
    p = os.path.join(HERE, base)
    if os.path.exists(p):
        return p
    q = os.path.join(DATA_DIR, base)
    if os.path.exists(q):
        return q
    return p

torch.manual_seed(1337)
DEVICE = "cuda" if torch.cuda.is_available() else "cpu"
GUTENBERG = resolve_data("gutenberg_corpus.txt")
ARXIV = resolve_data("arxiv_corpus.txt")
TINY = resolve_data("tinyshakespeare.txt")

def load_data():
    for p in (GUTENBERG, TINY, ARXIV):
        if os.path.exists(p) and os.path.getsize(p) > 200000:
            return open(p, encoding="utf-8").read()
    raise FileNotFoundError("no corpus")

def gen_indices(m, C=4, start=3):
    out, last = [], start
    for _ in range(m):
        out.append(last)
        last = max(last * C + 1, last + 2)
    return out

def log_uniform_ladder(lo, hi, m, seed, sort=True):
    """E1 psi-rand：m 个波长 log-uniform 采样于 [lo, hi]（seed 控制）。
    sort=True（psi 嵌入用，设计文档 L76「排序」）；sort=False（psi-rope-rand 用，
    「循环填充」= 随机顺序，避免前 half 个全为极小频率）。"""
    import random
    rng = random.Random(seed)
    log_vals = [rng.uniform(math.log(lo), math.log(hi)) for _ in range(m)]
    vals = [int(round(math.exp(v))) for v in log_vals]
    return sorted(vals) if sort else vals

def lin_ladder(lo, hi, m):
    """E1 psi-lin：m 个波长线性铺 [lo, hi]（排序）。"""
    return [int(round(lo + (hi - lo) * i / (m - 1))) for i in range(m)]

def psi_embedding(L, indices, device):
    n = torch.tensor(indices, dtype=torch.float32, device=device)
    inv = 1.0 / torch.sqrt(n)
    k = torch.arange(L, dtype=torch.float32, device=device)[:, None]
    th = 2.0 * math.pi * k / n[None, :]
    return torch.cos(th) * inv[None, :], torch.sin(th) * inv[None, :]

def get_batch(data, ix, block_size, batch_size, device):
    x = torch.stack([torch.tensor(data[i:i+block_size], dtype=torch.long) for i in ix])
    y = torch.stack([torch.tensor(data[i+1:i+1+block_size], dtype=torch.long) for i in ix])
    return x.to(device), y.to(device)

@torch.no_grad()
def eval_at_length(model, data_val, T, batch_size, n_batches, device):
    """在长度 T 上评估平均 loss（支持 T > 训练长度）。"""
    model.eval()
    losses = []
    n = len(data_val) - T - 1
    for _ in range(n_batches):
        ix = torch.randint(0, max(n, 1), (batch_size,))
        x = torch.stack([torch.tensor(data_val[i:i+T], dtype=torch.long) for i in ix]).to(device)
        y = torch.stack([torch.tensor(data_val[i+1:i+1+T], dtype=torch.long) for i in ix]).to(device)
        _, loss = model(x, y)
        losses.append(loss.item())
    model.train()
    return sum(losses) / len(losses)

def apply_rope_theta(q, k, T, device, theta):
    """通用旋转位置编码：theta (d/2,) 为逐维旋转角。RoPE 用 10000^{-2i/d}，psi-rope 用 2π/n_j。"""
    pos = torch.arange(T, dtype=torch.float32, device=device)
    angles = pos[:, None] * theta[None, :]                     # (T, d/2)
    cos = torch.cos(angles); sin = torch.sin(angles)           # (T, d/2)
    def rot(x):
        x1 = x[..., 0::2]; x2 = x[..., 1::2]                   # (B,H,T,d/2)
        c1 = cos.unsqueeze(0).unsqueeze(0); s1 = sin.unsqueeze(0).unsqueeze(0)
        return torch.cat([x1 * c1 - x2 * s1, x1 * s1 + x2 * c1], dim=-1)
    return rot(q), rot(k)

def rope_theta(d, device, base=10000.0):
    return base ** (-torch.arange(0, d, 2, dtype=torch.float32, device=device) / d)

def psi_rope_theta(d, device, ladder, grid_N=None, grid_offset=0.0):
    """psi-rope：旋转角 = 2π/n_j（n_j 取截断阶梯频带，循环填充 d/2 维）。
    grid_N 设置时用网格角 θ = 2π·m/grid_N（m 为互异整数，DFT 精确正交，μ=0 全长度成立）。
    grid_offset ≠ 0 时为 offset-grid：θ = 2π·(α + m/grid_N)，α 取黄金比 0.6180339887
    （无理偏移 ⟹ 每个原子严格非周期，任何 lag 无精确碰撞——C5 已证；证书经 T1d 保持）。"""
    ns = torch.tensor([n for n in ladder], dtype=torch.float32, device=device)
    half = d // 2
    idx = torch.arange(half, device=device) % len(ns)
    if grid_N:
        return 2.0 * math.pi * (grid_offset + ns[idx] / grid_N)
    return 2.0 * math.pi / ns[idx]

def _t5_relative_bucket(rel, num_buckets=32, max_distance=128):
    """T5 式相对位置分桶（单向：只处理因果过去的距离）。
    rel: (T,T) int，rel[i,j] = i − j（≥0 为过去）。返回同形桶索引张量。"""
    num_buckets //= 2
    n = rel.clamp(min=0)
    is_small = n < num_buckets
    log_denom = math.log(max_distance / num_buckets)
    log_part = ((n.float().log() - math.log(num_buckets)) / log_denom * (num_buckets - 1)).floor().long()
    large = num_buckets + log_part.clamp(min=0, max=num_buckets - 1)
    return torch.where(is_small, n, large).clamp(max=2 * num_buckets - 1)


class CausalSelfAttention(nn.Module):
    def __init__(self, n_embd, n_head, mode, theta=None, alibi=False, rel_bias=None):
        super().__init__()
        self.n_head, self.n_embd, self.mode, self.theta = n_head, n_embd, mode, theta
        self.alibi, self.rel_bias = alibi, rel_bias
        self.c_attn = nn.Linear(n_embd, 3 * n_embd)
        self.c_proj = nn.Linear(n_embd, n_embd)
        if alibi:
            # ALiBi 斜率（Press et al. 2021）：m_h = 2^(−8(h+1)/n_head)
            slopes = torch.tensor([2.0 ** (-8.0 * (h + 1) / n_head) for h in range(n_head)],
                                  dtype=torch.float32)
            self.register_buffer("alibi_slopes", slopes)
    def forward(self, x):
        B, T, C = x.shape
        qkv = self.c_attn(x)
        q, k, v = qkv.split(C, dim=2)
        q = q.view(B, T, self.n_head, C // self.n_head).transpose(1, 2)
        k = k.view(B, T, self.n_head, C // self.n_head).transpose(1, 2)
        v = v.view(B, T, self.n_head, C // self.n_head).transpose(1, 2)
        if self.mode in ("rope", "psi-rope"):
            q, k = apply_rope_theta(q, k, T, x.device, self.theta)
        w = getattr(self, "kv_window", None)
        if self.alibi or self.rel_bias is not None:
            # 手工注意力：ALiBi 线性偏置 / T5 相对位置偏置（均需在 softmax 前注入）
            scale = (C // self.n_head) ** -0.5
            scores = torch.matmul(q, k.transpose(-2, -1)) * scale          # (B,H,T,T)
            pos = torch.arange(T, device=x.device)
            if self.alibi:
                rel = pos[None, :] - pos[:, None]                          # rel[i,j] = j − i ≤ 0（过去为负）
                bias = self.alibi_slopes.view(-1, 1, 1) * rel               # (H,T,T)
                scores = scores + bias.unsqueeze(0)
            else:
                rel = pos[:, None] - pos[None, :]                          # rel[i,j] = i − j ≥ 0（过去）
                buckets = _t5_relative_bucket(rel, self.rel_bias.shape[1])
                scores = scores + self.rel_bias[:, buckets].unsqueeze(0)   # (H,T,T)
            causal = torch.tril(torch.ones(T, T, dtype=torch.bool, device=x.device))
            if w is not None and T > w:
                causal = causal & (pos[:, None] - pos[None, :] < w)        # 只保留最近 w（KV 逐出口径）
            scores = scores.masked_fill(~causal.unsqueeze(0), float("-inf"))
            attn = torch.softmax(scores, dim=-1)
            y = attn @ v                                                   # (B,H,T,d)
        else:
            if w is not None and T > w:
                # KV 逐出模拟（kv_eviction.py）：只保留最近 w 个 key/value（丢弃更远 KV），
                # query 全保留（位置语义不变）；显式 (T,w) 因果窗口 mask（True=可 attend）。
                k, v = k[..., -w:, :], v[..., -w:, :]
                i_glob = torch.arange(T, device=x.device)
                j_glob = torch.arange(T - w, T, device=x.device)
                attn_mask = j_glob[None, :] <= i_glob[:, None]
                y = F.scaled_dot_product_attention(q, k, v, attn_mask=attn_mask, is_causal=False)
            else:
                y = F.scaled_dot_product_attention(q, k, v, is_causal=True)
        return self.c_proj(y.transpose(1, 2).contiguous().view(B, y.shape[-2], C))

class Block(nn.Module):
    def __init__(self, n_embd, n_head, mode, theta=None, alibi=False, rel_bias=None):
        super().__init__()
        self.ln1 = nn.LayerNorm(n_embd)
        self.attn = CausalSelfAttention(n_embd, n_head, mode, theta, alibi=alibi, rel_bias=rel_bias)
        self.ln2 = nn.LayerNorm(n_embd)
        self.mlp = nn.Sequential(nn.Linear(n_embd, 4*n_embd), nn.GELU(), nn.Linear(4*n_embd, n_embd))
    def forward(self, x):
        x = x + self.attn(self.ln1(x))
        x = x + self.mlp(self.ln2(x))
        return x

class MiniGPT(nn.Module):
    def __init__(self, vocab_size, n_layer, n_head, n_embd, block_size, mode, psi_indices, theta=None):
        super().__init__()
        self.mode, self.block_size, self.psi_indices = mode, block_size, psi_indices
        self.theta = theta
        self.token_emb = nn.Embedding(vocab_size, n_embd)
        if mode in ("psi", "psi-trunc"):
            m = len(psi_indices)
            self.psi_proj = nn.Linear(2 * m, n_embd, bias=False)
        elif mode == "dense-frozen":
            # E1 dense-frozen：固定随机高斯特征（2m 维/位置，对标 psi 的 2m 特征维）+ 学习投影。
            # 去掉全部频率结构，只留"固定通道 + 瓶颈"；外推用 0 延拓（同 dense）。
            m = len(psi_indices)
            self.pos_feat = nn.Parameter(torch.randn(1, block_size, 2 * m) * 0.02)
            self.pos_feat.requires_grad_(False)          # 固定，不训练
            self.pos_proj = nn.Linear(2 * m, n_embd, bias=False)  # 学习投影（同 psi_proj）
        elif mode in ("rope", "psi-rope", "nope", "alibi", "t5rel"):
            self.pos_emb = None
        else:
            self.pos_emb = nn.Parameter(torch.zeros(1, block_size, n_embd))
        self.rel_bias = None
        if mode == "t5rel":
            self.rel_bias = nn.Parameter(torch.zeros(n_head, 32))   # 32 桶（16 线性 + 16 对数）
        self.blocks = nn.ModuleList([Block(n_embd, n_head, mode, theta,
                                           alibi=(mode == "alibi"), rel_bias=self.rel_bias)
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
        if self.mode in ("psi", "psi-trunc"):
            er, ei = psi_embedding(T, self.psi_indices, x.device)      # 任意 T（外推）
            x = x + self.psi_proj(torch.cat([er, ei], dim=1)).unsqueeze(0)
        elif self.mode == "dense-frozen":
            if T <= self.block_size:
                feat = self.pos_feat[:, :T, :]
            else:
                feat = F.pad(self.pos_feat, (0, 0, 0, T - self.block_size))  # 0 延拓（同 dense）
            x = x + self.pos_proj(feat)
        elif self.mode in ("rope", "psi-rope", "nope", "alibi", "t5rel"):
            pass  # rope/psi-rope 位置在注意力内旋转；nope/alibi/t5rel 无位置项（ALiBi/T5 偏置在注意力内）
        else:
            if T <= self.block_size:
                x = x + self.pos_emb[:, :T, :]
            else:
                x = x + F.pad(self.pos_emb, (0, 0, 0, T - self.block_size))
        for blk in self.blocks:
            x = blk(x)
        logits = self.lm_head(self.ln_f(x))
        if targets is None:
            return logits, None
        return logits, F.cross_entropy(logits.view(-1, logits.size(-1)), targets.view(-1))

def build_model(mode, config, block_size, theta=None):
    """构造模型（训练与 eval-only 共用）。"""
    return MiniGPT(vocab_size=config["vocab"], n_layer=config["n_layer"], n_head=config["n_head"],
                   n_embd=config["n_embd"], block_size=block_size, mode=mode,
                   psi_indices=config["psi_indices"], theta=theta)

def train_and_save(mode, iters, config, data_train, block_size, device, path, theta=None, guard=None, seed=1337):
    torch.manual_seed(seed)
    model = build_model(mode, config, block_size, theta).to(device)
    opt = torch.optim.AdamW(model.parameters(), lr=config["lr"])
    n = len(data_train) - block_size - 1
    t0 = time.time()
    for step in range(iters):
        ix = torch.randint(0, n, (config["batch"],))
        x, y = get_batch(data_train, ix.tolist(), block_size, config["batch"], device)
        _, loss = model(x, y)
        opt.zero_grad(); loss.backward(); opt.step()
        if step % 1000 == 0 or step == iters - 1:
            print(f"  [{mode}] step {step:5d} train {loss.item():.4f} ({time.time()-t0:.0f}s)", flush=True)
        if guard is not None:
            guard.check(f"{mode} step {step}")   # v3: 每步检查（后台线程 0.5s 测温，过热即阻塞）
    if guard is not None:
        guard.check(f"{mode} done")
    torch.save(model.state_dict(), path)
    return model

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--iters", type=int, default=3000)
    ap.add_argument("--block", type=int, default=512)
    ap.add_argument("--n-embd", type=int, default=128)
    ap.add_argument("--n-layer", type=int, default=2)
    ap.add_argument("--batch", type=int, default=64)          # v2: 传 32（v1 是 64）
    ap.add_argument("--gpu-max", type=float, default=58.0)    # v2: 58（v1 是 70）
    ap.add_argument("--gpu-resume", type=float, default=52.0) # v2: 52（v1 是 65）
    ap.add_argument("--cpu-util-max", type=float, default=70.0)  # v2: 70（v1 是 90）
    ap.add_argument("--check-interval", type=float, default=0.5)  # v3: 0.5s 高频探测（v2 是 15s，E5 第三次宕机教训）
    ap.add_argument("--cooldown", type=float, default=60.0)   # v2: 60（v1 是 30）
    ap.add_argument("--gen-c", type=int, default=4)           # E5: 2（C=2 八频带全相位阶梯）
    ap.add_argument("--bands", type=int, default=0)           # E5'/E5'': 截断阶梯到前 N 带（0 = 全部）
    ap.add_argument("--seed", type=int, default=1337)         # 多 seed 实验用（>=3 确认稳定性）
    ap.add_argument("--psi-variant", type=str, default="none",
                    help="E1 消融：none|rand（log-uniform 随机阶梯 [3,54613]）|lin（线性阶梯 [3,54613]）")
    ap.add_argument("--rope-rand", action="store_true",
                    help="E1 psi-rope-rand：旋转角来自随机全相位阶梯（log-uniform [3,511]）")
    ap.add_argument("--grid", type=int, default=0,
                    help="O1 网格阶梯：θ=2π·m/grid（m 从 [3,255] log-uniform 取互异整数，DFT 精确正交 μ=0）")
    ap.add_argument("--grid-offset", type=float, default=0.0,
                    help="offset-grid（Z 提案，2026-08-22 获批）：θ=2π·(α+m/grid)，α=黄金比 0.6180339887"
                         "（无理偏移消碰撞，证书保持；tag _ogrid；须与 --grid 同用）")
    ap.add_argument("--rand-max", type=int, default=0,
                    help="rand-trunc：psi-rope-rand 阶梯截断到 n≤rand-max（0=不截断；τ vs 密度判决实验：τ 预测剪 n>256 改善）")
    ap.add_argument("--modes", type=str, default="dense,psi,psi-trunc,rope,psi-rope")
    ap.add_argument("--eval-only", type=str, default="")      # 只评估已存模型（纯前向），如 "psi-trunc"
    ap.add_argument("--rope-variant", type=str, default="none",
                    help="测试时 rope 缩放（eval-only 用）：none|pi|ntk。"
                         "pi=位置插值 θ/r；ntk=base 缩放 base·r^(d/(d-2))。")
    args = ap.parse_args()

    guard = ThermalGuard(gpu_max=args.gpu_max, gpu_resume=args.gpu_resume,
                         cpu_util_max=args.cpu_util_max, check_interval=args.check_interval,
                         verbose=True)

    text = load_data()
    chars = sorted(list(set(text)))
    stoi = {c: i for i, c in enumerate(chars)}
    data = [stoi[c] for c in text]
    split = int(0.9 * len(data))
    data_train, data_val = data[:split], data[split:]
    if args.psi_variant == "rand":
        psi_ladder = log_uniform_ladder(3, 54613, 128, args.seed)
    elif args.psi_variant == "lin":
        psi_ladder = lin_ladder(3, 54613, 128)
    else:
        psi_ladder = gen_indices(128, args.gen_c)
    if args.bands > 0:
        psi_ladder = psi_ladder[:args.bands]
    if args.psi_variant != "none":
        print(f"  psi-variant={args.psi_variant}: ladder {psi_ladder[:6]}...", flush=True)
    config = dict(vocab=len(chars), n_layer=args.n_layer, n_head=4, n_embd=args.n_embd,
                  lr=3e-4, batch=args.batch, psi_indices=psi_ladder)
    print(f"device={DEVICE} vocab={len(chars)} train={len(data_train)} chars block={args.block} "
          f"batch={args.batch} gen_c={args.gen_c} bands={args.bands if args.bands else 'all'} seed={args.seed} "
          f"gpu_max={args.gpu_max} gpu_resume={args.gpu_resume} "
          f"cpu_util_max={args.cpu_util_max} check_interval={args.check_interval}", flush=True)

    if args.eval_only:
        # 纯前向评估已存模型（补齐中断的评估；不影响训练）
        mode = args.eval_only
        idxs = config["psi_indices"]
        theta = None
        if mode == "psi-trunc":
            idxs = [n for n in idxs if n <= args.block]
        if mode == "rope":
            theta = rope_theta(config["n_embd"] // config["n_head"], DEVICE)
        if mode == "psi-rope":
            if args.rope_rand:
                # rr：旋转角来自随机全相位阶梯（与训练路径逐字对齐）
                rl = [n for n in log_uniform_ladder(3, 511, 128, args.seed, sort=False)
                      if n <= args.block and (args.rand_max == 0 or n <= args.rand_max)]
                if args.grid:
                    # O1 网格阶梯：m_t 取互异整数（DFT 精确正交 μ=0 的前提）；grid_offset≠0 时 offset-grid
                    rl = sorted(set(n for n in log_uniform_ladder(3, 255, 128, args.seed, sort=False)))
                    theta = psi_rope_theta(config["n_embd"] // config["n_head"], DEVICE, rl,
                                           grid_N=args.grid, grid_offset=args.grid_offset)
                else:
                    theta = psi_rope_theta(config["n_embd"] // config["n_head"], DEVICE, rl)
            else:
                theta = psi_rope_theta(config["n_embd"] // config["n_head"], DEVICE,
                                       [n for n in config["psi_indices"] if n <= args.block])
        # E1 变体 tag：与训练路径同构（_rand / _rr / _s<seed> / _grid）
        tag = (f"_c{args.gen_c}" if args.gen_c != 4 else "") + (f"_s{args.seed}" if args.seed != 1337 else "") \
              + (f"_{args.psi_variant}" if args.psi_variant != "none" else "") \
              + ("_rr" if args.rope_rand else "") + (("_ogrid" if args.grid_offset else "_grid") if args.grid else "") \
              + (f"_rt{args.rand_max}" if args.rand_max > 0 else "")
        path = resolve_model(mode, args.block, tag)   # 先 HERE 根，再 测试数据/（归档后兼容）
        if not os.path.exists(path):
            print(f"[eval-only] 模型不存在: {path}", flush=True)
            sys.exit(2)
        model = build_model(mode, {**config, "psi_indices": idxs}, args.block, theta)
        model.load_state_dict(torch.load(path, map_location=DEVICE, weights_only=True))
        model.to(DEVICE)
        model.eval()
        variant = args.rope_variant if mode == "rope" else "none"
        print(f"===== [eval-only] {mode} (rope-variant={variant})  "
              f"({os.path.basename(path)}): length extrapolation =====", flush=True)
        row = {}
        for T in (512, 1024, 2048, 4096):
            if mode == "rope" and T != args.block and variant != "none":
                # 测试时 rope 缩放：按 r = T/T_train 重算 θᵢ
                d = config["n_embd"] // config["n_head"]
                r = T / args.block
                base = 10000.0
                if variant == "pi":
                    theta_v = base ** (-torch.arange(0, d, 2, dtype=torch.float32, device=DEVICE) / d) / r
                else:  # ntk：base' = base * r^(d/(d-2))
                    base_n = base * (r ** (d / (d - 2)))
                    theta_v = base_n ** (-torch.arange(0, d, 2, dtype=torch.float32, device=DEVICE) / d)
                # 重建模型并替换 theta
                model = build_model(mode, {**config, "psi_indices": idxs}, args.block, theta_v)
                model.load_state_dict(torch.load(path, map_location=DEVICE, weights_only=True))
                model.to(DEVICE).eval()
            nb = 4 if T <= 1024 else 2
            bs = 8 if T <= 1024 else 4
            loss = eval_at_length(model, data_val, T, bs, nb, DEVICE)
            row[T] = (loss, math.exp(loss))
            print(f"  T={T:5d}: loss {loss:.4f}  ppl {math.exp(loss):.2f}", flush=True)
            guard.check(f"{mode} eval T={T}")
        guard.stop()
        sys.exit(0)

    results = {}
    cooled_before = 0
    modes = [m.strip() for m in args.modes.split(",") if m.strip()]
    for mode in modes:
        idxs = config["psi_indices"]
        theta = None
        if mode == "psi-trunc":
            idxs = [n for n in idxs if n <= args.block]      # 只保留训练长度内见过全相位的频带
            print(f"  psi-trunc: 保留频带 {idxs}", flush=True)
        if mode == "rope":
            theta = rope_theta(config["n_embd"] // config["n_head"], DEVICE)
        if mode == "psi-rope":
            # 旋转角 = 2π/n_j，n_j 取截断阶梯（训练内见过全相位）——检验"psi 频率做相对旋转"
            if args.rope_rand:
                rl = [n for n in log_uniform_ladder(3, 511, 128, args.seed, sort=False)
                      if n <= args.block and (args.rand_max == 0 or n <= args.rand_max)]
                if args.grid:
                    # O1 网格阶梯：m_t 互异整数（[3,255] log-uniform），DFT 精确正交 μ=0
                    # grid_offset≠0 时为 offset-grid：θ=2π·(α+m/grid)，α 无理消碰撞（C5 已证）
                    rl = sorted(set(n for n in log_uniform_ladder(3, 255, 128, args.seed, sort=False)))
                    theta = psi_rope_theta(config["n_embd"] // config["n_head"], DEVICE, rl,
                                           grid_N=args.grid, grid_offset=args.grid_offset)
                    print(f"  psi-rope-{'ogrid' if args.grid_offset else 'grid'}: "
                          f"θ=2π·({args.grid_offset}+m)/{args.grid}，m 互异 {len(rl)} 个，首 16: {rl[:16]}", flush=True)
                else:
                    theta = psi_rope_theta(config["n_embd"] // config["n_head"], DEVICE, rl)
                    print(f"  psi-rope-rand: 旋转角来自随机全相位阶梯（log-uniform [3,511]，未排序）首 16: {[round(math.log(n)/math.log(3),1) for n in rl[:6]]}", flush=True)
            else:
                theta = psi_rope_theta(config["n_embd"] // config["n_head"], DEVICE,
                                       [n for n in config["psi_indices"] if n <= args.block])
                print(f"  psi-rope: 旋转角来自频带 {[n for n in config['psi_indices'] if n <= args.block]}", flush=True)
        tag = (f"_c{args.gen_c}" if args.gen_c != 4 else "") + (f"_s{args.seed}" if args.seed != 1337 else "") \
              + (f"_{args.psi_variant}" if args.psi_variant != "none" else "") \
              + ("_rr" if args.rope_rand else "") + (("_ogrid" if args.grid_offset else "_grid") if args.grid else "") \
              + (f"_rt{args.rand_max}" if args.rand_max > 0 else "")
        path = os.path.join(HERE, f"model_{mode}_b{args.block}{tag}.pt")
        model = train_and_save(mode, args.iters, {**config, "psi_indices": idxs},
                               data_train, args.block, DEVICE, path, theta, guard, args.seed)
        print(f"===== {mode}: length extrapolation =====", flush=True)
        guard.cooldown(args.cooldown)      # 模式间固定冷却
        row = {}
        for T in (512, 1024, 2048, 4096):
            nb = 4 if T <= 1024 else 2
            bs = 8 if T <= 1024 else 4
            loss = eval_at_length(model, data_val, T, bs, nb, DEVICE)
            row[T] = (loss, math.exp(loss))
            print(f"  T={T:5d}: loss {loss:.4f}  ppl {math.exp(loss):.2f}", flush=True)
            guard.check(f"{mode} eval T={T}")   # 评估也检查温度
        results[mode] = row
        mode_cooled = guard.cooled - cooled_before
        cooled_before = guard.cooled
        print(f"  [thermal] {mode} 冷却次数: {mode_cooled}（若 > 3 次须降载重跑）", flush=True)

    print("\n===== 外推对比汇总（训练 T=%d）=====" % args.block)
    header = f"{'T':>6} | " + " | ".join(f"{m:>10}" for m in modes)
    print(header)
    for T in (512, 1024, 2048, 4096):
        row = f"{T:>6} | " + " | ".join(f"{results[m][T][1]:>10.2f}" for m in modes)
        print(row)
    guard.stop()

if __name__ == "__main__":
    main()
