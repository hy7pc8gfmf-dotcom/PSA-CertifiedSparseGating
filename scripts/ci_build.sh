#!/usr/bin/env bash
# CI 构建脚本：在 Rocq/Coq 容器内编译完整开发并运行审计
# 阶段 1: lib/ 22 库依赖链（DAG 顺序见 scripts/order.txt）
# 阶段 2: PSA 核心（PSA_framework / PSA_audit / PSA_refcheck）
set -euo pipefail

echo "=== 0. 环境 ==="
rocq_version=$(coqc --version 2>/dev/null | head -1 || true)
echo "coqc: $rocq_version"

echo "=== 1. 依赖（mathcomp opam + Coquelicot vendored）==="
eval "$(opam env 2>/dev/null || true)"
SCRIPTS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_DIR="$(dirname "$SCRIPTS_DIR")"
COQLIB=$(coqc -where 2>/dev/null || true)
# mathcomp 2.5.0 经 opam 安装（配 HB/elpi）；Coquelicot 用仓库 vendored master 编译
MC="$COQLIB/user-contrib/mathcomp"
CQ="$REPO_DIR/coq/deps/coquelicot/theories"
HB="$COQLIB/user-contrib/HB"
ELPI="$COQLIB/user-contrib/elpi"
echo "  mathcomp (opam): $MC"
echo "  Coquelicot (vendored): $CQ"
echo "  HB (opam): $HB"
echo "  elpi (opam): $ELPI"
test -d "$CQ" || { echo "  ✗ vendored Coquelicot 缺失"; exit 1; }
test -d "$MC" && test -d "$HB" && test -d "$ELPI" || { echo "  ✗ opam 依赖缺失（需 coq-mathcomp-ssreflect.2.5.0 + coq-elpi）"; exit 1; }
test -f "$CQ/Coquelicot.vo" && echo "  ✅ Coquelicot .vo 就绪" || { echo "  ✗ Coquelicot 未编译——需 workflow 'Build vendored Coquelicot' 步骤"; exit 1; }

echo "=== 2. lib/ 依赖链编译 ==="
cd /repo 2>/dev/null || cd "$(dirname "$0")/.."
while read -r f; do
  # 跳过注释行（# 开头）与空行
  [ -z "$f" ] && continue
  case "$f" in \#*) continue ;; esac
  echo "  coqc lib/$f.v"
  # mathcomp>=2.6 把 ssrbool/ssrnat/seq/prime/div 移到 boot/，代码用 boot.X 前缀（单映射）
  coqc -Q "coq/lib" "" -Q "$MC" mathcomp -Q "$CQ" Coquelicot -Q "$HB" HB -Q "$ELPI" elpi "coq/lib/$f.v"
done < scripts/order.txt
echo "  lib chain compiled"

echo "=== 2.5 合并版编译（E130：PSA_audit 直接 Require 合并版 .vo）==="
echo "  coqc merged/ca_merged_full_25.v"
coqc -Q "coq/merged" "" -Q "$MC" mathcomp -Q "$CQ" Coquelicot -Q "$HB" HB -Q "$ELPI" elpi "coq/merged/ca_merged_full_25.v"
echo "  ✅ 合并版编译通过"

echo "=== 3. PSA 核心编译 ==="
for f in PSA_framework PSA_audit PSA_refcheck; do
  echo "  coqc core/$f.v"
  # -Q coq/core PSA（PSA 前缀）+ -Q coq/lib ""（lib 顶层）+ -Q coq/merged ""（合并版，PSA_audit 依赖）
  coqc -Q "coq/core" PSA -Q "coq/lib" "" -Q "coq/merged" "" -Q "$MC" mathcomp -Q "$CQ" Coquelicot -Q "$HB" HB -Q "$ELPI" elpi "coq/core/$f.v"
done
echo "  ✅ PSA 核心编译通过"

echo "=== 4. 零 Admitted 检查 ==="
if grep -rn "Admitted" coq/core/PSA_framework.v | grep -v "(\*" ; then
  echo "  ❌ 发现 Admitted！"
  exit 1
else
  echo "  ✅ 零 Admitted（PSA_framework.v）"
fi

echo "=== 5. coqchk 内核独立复验 ==="
# coqchk 不信任 coqc 的证明证书，用 Rocq 内核重新验证全部证明（含依赖闭包）
if command -v rocqchk >/dev/null 2>&1; then COQCHK=rocqchk; else COQCHK=coqchk; fi
echo "  使用 $COQCHK 复验 PSA.PSA_framework / PSA.PSA_audit / PSA.PSA_refcheck ..."
"$COQCHK" -Q "$COQLIB/user-contrib/mathcomp" mathcomp -Q "$CQ" Coquelicot -Q "$HB" HB -Q "$ELPI" elpi \
  -Q "coq/lib" "" -Q "coq/core" PSA -Q "coq/merged" "" PSA.PSA_framework PSA.PSA_audit PSA.PSA_refcheck 2>&1 | tail -8
rc=${PIPESTATUS[0]}
if [ "$rc" = "0" ]; then
  echo "  ✅ coqchk 内核复验通过（RC=0）"
else
  echo "  ❌ coqchk 复验失败（RC=$rc）"
  exit 1
fi

echo "=== CI 全部通过 ==="
