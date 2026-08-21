# -*- coding: utf-8 -*-
"""
PSA 运行时守护检查器 Python FFI（subprocess 封装）
=================================================
调用由 Coq 提取的 OCaml 检查器 psa_guard.exe（若已编译）。

验证链：
  PSA_framework.v（全部 Qed，零 Admitted）
    -> PSA_extract.v 提取为 psa_guard.ml（Coq 定义原样，Peano nat 无溢出）
    -> ocamlopt 编译为 psa_guard.exe
    -> 本模块 subprocess 调用

用法：
  from psa_guard_ffi import check_sparse_growth, check_c_sparse_on_vals, generate_base_indices
  check_sparse_growth([2,5,11], 2)          # True
  check_c_sparse_on_vals([3,3,4], 1)        # True（c*c*a = b 相等情形，<=? 语义）
  generate_base_indices(3, 2, 5)            # [5, 11, 23, 47]

本工作区当前无 ocamlopt，需在有 OCaml 工具链的机器上编译：
  ocamlopt psa_guard.ml psa_guard_main.ml -o psa_guard.exe
（Windows 下请从装有 OCaml 的环境执行；Rocq Platform 自带 ocamlfind，
  但其 cygwin opam 树在本机不可达。）

self_test()：嵌入的期望值来自 PSA_refcheck.v 的 Coq 真实计算（权威参考）。
"""

import os
import subprocess
import sys

_HERE = os.path.dirname(os.path.abspath(__file__))
GUARD_EXE = os.path.join(_HERE, "psa_guard.exe")

# 字节码 exe 运行需 camlrun 在 PATH（DkMLNative 安装目录）
_OCAML_BIN = os.path.join(
    os.environ.get("LOCALAPPDATA", ""), "Programs", "DkMLNative", "desktop", "bc", "bin"
)


def _run(args):
    if not os.path.exists(GUARD_EXE):
        raise FileNotFoundError(
            f"{GUARD_EXE} 不存在。请先编译：ocamlc psa_guard.ml psa_guard_main.ml -o psa_guard.exe"
        )
    env = os.environ.copy()
    if os.path.isdir(_OCAML_BIN):
        env["PATH"] = _OCAML_BIN + os.pathsep + env.get("PATH", "")
    out = subprocess.run([GUARD_EXE] + args, capture_output=True, text=True, timeout=60, env=env)
    if out.returncode != 0:
        raise RuntimeError(f"psa_guard 失败 rc={out.returncode}: {out.stderr.strip()}")
    return out.stdout.strip()


def check_sparse_growth(indices, C):
    """线性稀疏增长守卫：相邻对满足 C*a < b（对应 decay_bound 前提）。"""
    return _run(["sparse", str(C)] + [str(i) for i in indices]) == "true"


def check_c_sparse_on_vals(vals, c):
    """平方稀疏 + 全元素 >=2 守卫：相邻对满足 c*c*a <= b 且每元素 >=2。"""
    return _run(["square", str(c)] + [str(v) for v in vals]) == "true"


def generate_base_indices(length, C, start):
    """确定性生成器：长度 S len，首元素 start，next = max(last*C+1, last+2)。"""
    out = _run(["gen", str(length), str(C), str(start)])
    return [int(x) for x in out.split()] if out else []


def greedy_selected(M, vals):
    """贪心门控（值层面）：首个保留，之后 val >= M*last_kept 才保留（P0 定理的对象）。"""
    out = _run(["gateval", str(M)] + [str(v) for v in vals])
    return [int(x) for x in out.split()] if out else []


def greedy_indices(M, C, start, indices):
    """索引层面门控：greedy_indices (base_seq C start) M indices（生成器上的门控）。"""
    out = _run(["gateidx", str(M), str(C), str(start)] + [str(i) for i in indices])
    return [int(x) for x in out.split()] if out else []


def fallback_mask(M, vals):
    """布尔掩码形式（原文 §3.2）：与 vals 等长的 true/false 列表。"""
    out = _run(["mask", str(M)] + [str(v) for v in vals])
    return [s == "true" for s in out.split()] if out else []


def frame_check_instance(ladder):
    """反射框架检查器：任意梯子 → 判定 Gershgorin μ ≤ 4/5（可认证性）。
    ladder: 升序正整数列表（如 [3,13,53,213]）。
    返回 True 表示对任意系数向量，框架界 [1/5,9/5] 成立（窗口=末元素）。
    注意：实现为原生 int（psa_guard_main.ml 的 frame_check_instance_int），
    镜像 PSA_framework.v 的 FrameCheckInstance 定义；与 Coq 定理
    certified_c4_frame_bounds / certified_t8_core_frame_bounds 同构。"""
    out = _run(["frame"] + [str(v) for v in ladder])
    return out == "true"


# ---------------------------------------------------------------------------
# 自测：期望值来自 PSA_refcheck.v 的 Coq 真实计算（2026-08-18 会话 3 实测）
# ---------------------------------------------------------------------------

REF_SPARSE = [
    (([2, 5, 11], 2), True),   # 2*2<5 且 2*5<11
    (([2, 5, 10], 2), False),  # 2*5<10 不成立
    (([], 2), True),           # 空列表平凡
    (([7], 3), True),          # 单元素平凡
]

REF_SQUARE = [
    (([3, 13, 53], 2), True),  # 4*3<=13 且 4*13<=53，全 >=2
    (([3, 3, 4], 1), True),    # 关键：c*c*a = b 相等情形（旧 <? 误拒，<=? 通过）
    (([1, 13, 53], 2), False), # 元素 1 < 2，all_ge_2 失败
    (([], 2), True),           # 空列表平凡
]

REF_GEN = [
    ((3, 2, 5), [5, 11, 23, 47]),       # max(5*2+1,5+2)=11 -> 23 -> 47，长度 4 = S 3
    ((5, 3, 2), [2, 7, 22, 67, 202, 607]),
    ((0, 2, 2), [2]),
]

# 2026-08-18 会话 5 续：门控参考值（PSA_refcheck.v 的 Coq 真实计算）
REF_GATEVAL = [
    ((2, [3, 5, 9, 20]), [3, 9, 20]),   # 5<2*3=6 丢弃；9>=6 保留；20>=18 保留
    ((4, [3, 5, 9, 20]), [3, 20]),      # 20>=4*3=12 保留
    ((2, [2, 5, 11, 23]), [2, 5, 11, 23]),
    ((1, [3, 3, 4]), [3, 3, 4]),        # M=1：3>=3 全保留（含相等）
]

REF_GATEIDX = [
    # seq = base_seq 2 5 = [5,11,23,47]；M=4（平方门 C*C）
    ((4, 2, 5, [0, 1, 2, 3]), [0, 2]),  # 4*5=20<=11? no；20<=23? yes；4*23=92<=47? no
    # seq = base_seq 3 2 = [2,7,22,67,202,607]；M=9
    ((9, 3, 2, [0, 1, 2, 3, 4, 5]), [0, 2, 4]),
]

REF_MASK = [
    ((2, [3, 5, 9, 20]), [True, False, True, True]),
    ((4, [3, 5, 9, 20]), [True, False, False, True]),
]

# 2026-08-19 会话 9：反射框架检查器参考值
# 期望值来自 Coq 中 frame_check_instance 的语义 + 整数行和验算（见 six pairs 文档）
REF_FRAME = [
    ([3, 13, 53, 213], True),          # C=4 可认证（μ=4/5 证书）
    ([3, 15, 63, 255], True),          # T8 核可认证
    ([3, 7, 15, 31, 63, 127, 255], False),   # E5'' 整梯不可认证（行和>1）
    ([3, 7, 15, 31, 63, 127, 255, 511], False),  # C2b 八带不可认证
    ([3, 13], True),                   # 2 带小梯（行和小）
]


def self_test(verbose=True):
    """对照 Coq 权威参考值校验 OCaml 检查器；exe 缺失时打印参考值并跳过。"""
    if not os.path.exists(GUARD_EXE):
        print("[self_test] psa_guard.exe 未编译，跳过执行校验。")
        print("[self_test] Coq 权威参考值（PSA_refcheck.v 计算）：")
        for (args, expected) in REF_SPARSE:
            print(f"  check_sparse_growth{args} = {expected}")
        for (args, expected) in REF_SQUARE:
            print(f"  check_c_sparse_on_vals{args} = {expected}")
        for (args, expected) in REF_GEN:
            print(f"  generate_base_indices{args} = {expected}")
        return False

    ok = True
    for (args, expected) in REF_SPARSE:
        got = check_sparse_growth(*args)
        if got != expected:
            ok = False
            print(f"  FAIL check_sparse_growth{args}: got {got}, expected {expected}")
        elif verbose:
            print(f"  ok   check_sparse_growth{args} = {got}")
    for (args, expected) in REF_SQUARE:
        got = check_c_sparse_on_vals(*args)
        if got != expected:
            ok = False
            print(f"  FAIL check_c_sparse_on_vals{args}: got {got}, expected {expected}")
        elif verbose:
            print(f"  ok   check_c_sparse_on_vals{args} = {got}")
    for (args, expected) in REF_GEN:
        got = generate_base_indices(*args)
        if got != expected:
            ok = False
            print(f"  FAIL generate_base_indices{args}: got {got}, expected {expected}")
        elif verbose:
            print(f"  ok   generate_base_indices{args} = {got}")
    for (args, expected) in REF_GATEVAL:
        got = greedy_selected(*args)
        if got != expected:
            ok = False
            print(f"  FAIL greedy_selected{args}: got {got}, expected {expected}")
        elif verbose:
            print(f"  ok   greedy_selected{args} = {got}")
    for (args, expected) in REF_GATEIDX:
        got = greedy_indices(*args)
        if got != expected:
            ok = False
            print(f"  FAIL greedy_indices{args}: got {got}, expected {expected}")
        elif verbose:
            print(f"  ok   greedy_indices{args} = {got}")
    for (args, expected) in REF_MASK:
        got = fallback_mask(*args)
        if got != expected:
            ok = False
            print(f"  FAIL fallback_mask{args}: got {got}, expected {expected}")
        elif verbose:
            print(f"  ok   fallback_mask{args} = {got}")
    for (args, expected) in REF_FRAME:
        got = frame_check_instance(args)
        if got != expected:
            ok = False
            print(f"  FAIL frame_check_instance{args}: got {got}, expected {expected}")
        elif verbose:
            print(f"  ok   frame_check_instance{args} = {got}")
    print(f"[self_test] {'全部通过' if ok else '存在失败'}")
    return ok


if __name__ == "__main__":
    sys.exit(0 if self_test() else 1)
