#!/usr/bin/env bash
# CI 构建脚本：在 Rocq/Coq 容器内编译完整开发并运行审计
# 阶段 1: lib/ 22 库依赖链（DAG 顺序见 scripts/order.txt）
# 阶段 2: PSA 核心（PSA_framework / PSA_audit / PSA_refcheck）
set -euo pipefail

echo "=== 0. 环境 ==="
rocq_version=$(coqc --version 2>/dev/null | head -1 || true)
echo "coqc: $rocq_version"

echo "=== 1. 依赖（mathcomp + Coquelicot）==="
eval "$(opam env 2>/dev/null || true)"
# 依赖由 workflow 预装：mathcomp 经 opam，Coquelicot 经 gitlab master 编译安装（见下方 1b 定位）

echo "=== 1b. 定位 mathcomp / Coquelicot 安装路径 ==="
# 优先 coqc -where 的 user-contrib；其次 ocamlfind；再次 opam lib 目录搜索；最后兜底
# 注意：Linux runner 文件系统大小写敏感，目录名须为小写 coquelicot
COQLIB=$(coqc -where 2>/dev/null || true)
MC=""
CQ=""
if [ -n "$COQLIB" ] && [ -d "$COQLIB/user-contrib/mathcomp" ]; then
  MC="$COQLIB/user-contrib/mathcomp"
fi
if [ -n "$COQLIB" ] && [ -d "$COQLIB/user-contrib/coquelicot" ]; then
  CQ="$COQLIB/user-contrib/coquelicot"
fi
if [ -z "$MC" ]; then MC=$(ocamlfind query mathcomp 2>/dev/null || true); fi
if [ -z "$CQ" ]; then CQ=$(ocamlfind query coquelicot 2>/dev/null || true); fi
OPAM_LIB=$(opam var lib 2>/dev/null || true)
if [ -z "$MC" ] && [ -n "$OPAM_LIB" ]; then MC=$(find "$OPAM_LIB" -maxdepth 4 -type d -name mathcomp 2>/dev/null | head -1); fi
if [ -z "$CQ" ] && [ -n "$OPAM_LIB" ]; then CQ=$(find "$OPAM_LIB" -maxdepth 4 -type d -name coquelicot 2>/dev/null | head -1); fi
if [ -z "$MC" ]; then MC="/usr/lib/ocaml/mathcomp"; fi
if [ -z "$CQ" ]; then CQ="/usr/lib/ocaml/coquelicot"; fi
echo "  mathcomp: $MC"
echo "  Coquelicot: $CQ"
test -d "$MC" && test -d "$CQ"

echo "=== 2. lib/ 依赖链编译 ==="
cd /repo 2>/dev/null || cd "$(dirname "$0")/.."
while read -r f; do
  # 跳过注释行（# 开头）与空行
  [ -z "$f" ] && continue
  case "$f" in \#*) continue ;; esac
  echo "  coqc lib/$f.v"
  coqc -Q "coq/lib" "" -Q "$MC" mathcomp -Q "$CQ" Coquelicot "coq/lib/$f.v"
done < scripts/order.txt
echo "  lib chain compiled"

echo "=== 3. PSA 核心编译 ==="
for f in PSA_framework PSA_audit PSA_refcheck; do
  echo "  coqc $f.v"
  coqc -R "coq" PSA -Q "$MC" mathcomp -Q "$CQ" Coquelicot "coq/$f.v"
done
echo "  ✅ PSA 核心编译通过"

echo "=== 4. 零 Admitted 检查 ==="
if grep -rn "Admitted" coq/PSA_framework.v | grep -v "(\*" ; then
  echo "  ❌ 发现 Admitted！"
  exit 1
else
  echo "  ✅ 零 Admitted（PSA_framework.v）"
fi

echo "=== CI 全部通过 ==="
