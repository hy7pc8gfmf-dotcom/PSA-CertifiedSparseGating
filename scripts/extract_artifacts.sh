#!/usr/bin/env bash
# 提取产物再生 + ocamlc 良构性验证（make extract 的实体）
# 用法: bash scripts/extract_artifacts.sh [COQC 路径可经环境变量 COQC 传入]
# 纪律: 日志文件重定向（E081 禁管道）；产物 *.vo 已被 .gitignore 覆盖；
#       再生后 `git status --short coq/probes` 非空 = 生成物与源漂移（确定性自检信号）。
set -uo pipefail
SCRIPTS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_DIR="$(dirname "$SCRIPTS_DIR")"
PROBES="$REPO_DIR/coq/probes"
CORE="$REPO_DIR/coq/core"
LOG="$REPO_DIR/docs/audit_local/extract_build.log"
COQC="${COQC:-coqc}"
OCAMLC="${OCAMLC:-ocamlc}"

# 构造性 Q 层（零外部依赖，-Q probes "" 自足）；格式 out:src（基座源文件名无 probe_ 前缀）
Q_LIST="qset_twin_base:qset_twin_base rc_envelope_t2:probe_rc_envelope gershgorin_qtw:probe_gershgorin_qtw pareto_qtw:probe_pareto_qtw taugrid_cr:probe_taugrid_cr c4_four_atom_cr:probe_c4_four_atom_cr safe_domain:probe_safe_domain c4_unique2sparse_cr:probe_c4_unique2sparse_cr c4_gram_unique_cr:probe_c4_gram_unique_cr g11_checkiff_cr:probe_g11_checkiff_cr g13_certtight_cr:probe_g13_certtight_cr g9_pairfrac_cr:probe_g9_pairfrac_cr itv_noisyor_cr:probe_itv_noisyor_cr z_frame_check:probe_z_frame_check z2b_int63mirror:probe_z2b_int63mirror"
# classic-R 两件（frame_check_graduated/g7_welch_cr）不在本脚本——需 9.0.1 平台
# + mathcomp/Coquelicot 真环境（9.1 读不了 9.0 编的 .vo），提取验证由 z 侧记录承担
ZARITH_DEP="z_frame_check"

mkdir -p "$(dirname "$LOG")"
: > "$LOG"
pass=0; fail=0
q_flags=(-Q "$PROBES" "")

# classic 轨依赖路径（与 Makefile LIBQ/DEPSQ 同源；缺失则跳过 R 轨）
MC="${MC:-$COQLIB/user-contrib/mathcomp}"; CQ="${CQ:-$REPO_DIR/coq/deps/coquelicot/theories}"
r_flags=()
if [ -d "$MC" ] && [ -d "$CQ" ]; then r_flags=(-Q "$PROBES" "" -Q "$MC" mathcomp -Q "$CQ" Coquelicot); fi

extract_one() { # $1=src file 基名(不含.v)  $2=产物名  $3...=flags
  local src="$1"; shift; local out="$1"; shift
  echo "--- extract $src -> $out.ml" >> "$LOG"
  "$COQC" -q "$@" -output-directory "$PROBES" "$PROBES/$src.v" >> "$LOG" 2>&1
  local rc=$?
  if [ $rc -ne 0 ] || [ ! -f "$PROBES/$out.ml" ]; then
    echo "FAIL(extract) $out (rc=$rc)"; fail=$((fail+1)); return 1
  fi
  pass=$((pass+1))
  # ocamlc 良构性验证（Zarith 依赖件缺失包时降级）
  if command -v "$OCAMLC" >/dev/null 2>&1; then
    case " $ZARITH_DEP " in *" $out "*)
      if ! "$OCAMLC" -list 2>/dev/null | grep -qi zarith && ! ocamlfind query zarith >/dev/null 2>&1; then
        echo "SKIP(ocamlc zarith) $out"; return 0
      fi ;;
    esac
    ( cd "$PROBES" && "$OCAMLC" -c "$out.mli" >> "$LOG" 2>&1 && "$OCAMLC" -c "$out.ml" >> "$LOG" 2>&1 )
    if [ $? -eq 0 ]; then echo "OK(ocamlc) $out"; else echo "FAIL(ocamlc) $out"; fail=$((fail+1)); fi
  fi
}

echo "=== extract_artifacts $(date +%F) coqc=$($COQC --version 2>/dev/null | head -1) ==="
for pair in $Q_LIST; do
  out="${pair%%:*}"; src="${pair##*:}"
  extract_one "$src" "$out" "${q_flags[@]}" || true
done
# core 提取驱动（psa_guard）：依赖 lib 链 .vo 与 mathcomp/Coquelicot——
# 不满足则 SKIP（提示 make lib），不硬失败
if [ -f "$CORE/PSA_extract.v" ]; then
  if ls "$CORE"/*.vo >/dev/null 2>&1 || ls "${CORE%/core}/lib"/*.vo >/dev/null 2>&1; then
    echo "--- PSA_extract (psa_guard)" >> "$LOG"
    ( cd "$CORE" && "$COQC" -q PSA_extract.v >> "$LOG" 2>&1 ) && { echo "OK(psa_guard)"; pass=$((pass+1)); } || { echo "FAIL(psa_guard)"; fail=$((fail+1)); }
  else
    echo "SKIP(psa_guard): lib 链 .vo 未编译（先 make lib）"
  fi
fi
echo "=== extract summary: pass=$pass fail=$fail log=$LOG ==="
[ "$fail" -eq 0 ]
