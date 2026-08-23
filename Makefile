# PSA-CertifiedSparseGating — 一键构建 Makefile（Rocq/Coq 9.0 + mathcomp + Coquelicot）
#
# 用法：
#   make            # lib 链 + 独立模块 + core + 审计 + 零 Admitted + coqchk 复验
#   make lib        # 按 scripts/order.txt 编译 lib 依赖链（30 个正式模块）
#   make lib-extra  # 独立模块（ca_zeta_euler 构造性欧拉主线 + ParetoLaw/P1Coherence/ParetoRandom/CRTResolve）
#   make core       # PSA 核心（PSA_framework / PSA_audit / PSA_refcheck / PSA_extract）
#   make probes     # z 区探针（24 个，独立验证；7 个亦并入合并版）
#   make audit      # PSA_audit（165 项 Print Assumptions）
#   make check      # 零 Admitted + coqchk 内核独立复验
#   make clean
#
# 变量覆盖（Windows 本地示例）：
#   make COQC="C:/Rocq-Platform~9.0~2025.08/bin/coqc.exe" MC="D:/ComplexAnalysis/Live_harness/lib/mathcomp" CQ="D:/ComplexAnalysis/Live_harness/lib/Coquelicot"

COQC  ?= coqc
COQCHK ?= $(if $(shell command -v rocqchk 2>/dev/null),rocqchk,$(if $(shell command -v coqchk 2>/dev/null),coqchk,coqc -check))

LIB_DIR     := coq/lib
CORE_DIR    := coq/core
PROBES_DIR  := coq/probes
ORDER       := scripts/order.txt

# 外部依赖路径：vendored 优先（coq/deps），否则 opam（Linux/CI）
COQLIB ?= $(shell $(COQC) -where 2>/dev/null)
MC  ?= $(if $(wildcard coq/deps/mathcomp),$(CURDIR)/coq/deps/mathcomp,$(COQLIB)/user-contrib/mathcomp)
CQ  ?= $(if $(wildcard coq/deps/coquelicot/theories),$(CURDIR)/coq/deps/coquelicot/theories,$(COQLIB)/user-contrib/Coquelicot)
HB  ?= $(COQLIB)/user-contrib/HB
ELPI?= $(COQLIB)/user-contrib/elpi

HAS_HB := $(if $(wildcard $(HB)),-Q $(HB) HB -Q $(ELPI) elpi,)

# -Q 映射：lib 顶层 ""、core 前缀 PSA、probes 顶层 ""
LIBQ    := -Q $(LIB_DIR) ""
COREQ   := -Q $(CORE_DIR) PSA
PROBEQ  := -Q $(PROBES_DIR) ""
DEPSQ   := -Q $(MC) mathcomp -Q $(CQ) Coquelicot

LIB_FILES   := $(shell grep -v '^\s*#' $(ORDER) | grep -v '^\s*$$' | sed 's|^|$(LIB_DIR)/|; s|$$|.v|')
LIB_VO      := $(LIB_FILES:.v=.vo)
EXTRA_FILES := $(LIB_DIR)/ca_zeta_euler.v $(LIB_DIR)/ParetoLaw.v $(LIB_DIR)/P1Coherence.v $(LIB_DIR)/ParetoRandom.v $(LIB_DIR)/CRTResolve.v
EXTRA_VO    := $(EXTRA_FILES:.v=.vo)
CORE_FILES  := $(CORE_DIR)/PSA_framework.v $(CORE_DIR)/PSA_audit.v $(CORE_DIR)/PSA_refcheck.v $(CORE_DIR)/PSA_extract.v
CORE_VO     := $(CORE_FILES:.v=.vo)
PROBE_FILES := $(wildcard $(PROBES_DIR)/*.v)
PROBE_VO    := $(PROBE_FILES:.v=.vo)

.PHONY: all lib lib-extra core probes audit check extract clean

all: lib lib-extra core audit check

lib: $(LIB_VO)
$(LIB_DIR)/%.vo: $(LIB_DIR)/%.v
	$(COQC) $(LIBQ) $(DEPSQ) $(HAS_HB) $<

lib-extra: $(EXTRA_VO)
$(LIB_DIR)/ca_zeta_euler.vo: $(LIB_DIR)/ca_zeta_euler.v
	$(COQC) $(LIBQ) $(DEPSQ) $(HAS_HB) $<
$(LIB_DIR)/ParetoLaw.vo $(LIB_DIR)/P1Coherence.vo $(LIB_DIR)/ParetoRandom.vo $(LIB_DIR)/CRTResolve.vo: $(LIB_DIR)/%.v
	$(COQC) $(LIBQ) $(DEPSQ) $(HAS_HB) $<

core: $(CORE_VO)
$(CORE_DIR)/%.vo: $(CORE_DIR)/%.v
	$(COQC) $(COREQ) $(LIBQ) $(DEPSQ) $(HAS_HB) $<

probes: $(PROBE_VO)
$(PROBES_DIR)/%.vo: $(PROBES_DIR)/%.v
	$(COQC) $(PROBEQ) $(LIBQ) $(DEPSQ) $(HAS_HB) $<

audit: $(CORE_DIR)/PSA_audit.vo
	@echo "Audit output: coq/core/PSA_audit.vo (165 entries)"

check:
	@echo "=== 零 Admitted 检查 ==="
	@if grep -rn "Admitted" $(CORE_DIR)/PSA_framework.v | grep -v "(\*" ; then \
	  echo "FAIL: Admitted found in PSA_framework.v"; exit 1; \
	else echo "OK: zero Admitted (PSA_framework.v)"; fi
	@echo "=== coqchk 内核独立复验 ==="
	$(COQCHK) $(COREQ) $(LIBQ) $(DEPSQ) PSA.PSA_framework PSA.PSA_audit

extract: $(CORE_DIR)/PSA_extract.vo
	@echo "Extraction: run 'coqc ... PSA_extract.v' then ocamlc (see README §复现指引)"

clean:
	rm -f $(LIB_DIR)/*.vo $(LIB_DIR)/*.glob $(LIB_DIR)/*.vos $(LIB_DIR)/*.vok
	rm -f $(CORE_DIR)/*.vo $(CORE_DIR)/*.glob $(CORE_DIR)/*.vos $(CORE_DIR)/*.vok
	rm -f $(PROBES_DIR)/*.vo $(PROBES_DIR)/*.glob $(PROBES_DIR)/*.vos $(PROBES_DIR)/*.vok
