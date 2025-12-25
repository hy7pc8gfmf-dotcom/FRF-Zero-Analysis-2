# FRF2.0形式化分析验证系统 - 最终Makefile
# 版本: 2.0.0 | Coq 8.18.0+ | 支持并行编译+动态资源管理

# ======================== 基础配置 ========================
COQC ?= coqc
COQDEP ?= coqdep
COQTOP ?= coqtop
COQDOC ?= coqdoc

# 版本检测
COQ_VERSION := $(shell $(COQC) --version | grep -o 'version [0-9.]\+' | cut -d' ' -f2)
COQ_MAJOR := $(shell echo $(COQ_VERSION) | cut -d. -f1)
COQ_MINOR := $(shell echo $(COQ_VERSION) | cut -d. -f2)

# 并行配置
PARALLEL_JOBS ?= $(shell nproc || echo 4)
MAKEFLAGS += -j$(PARALLEL_JOBS) -l$(PARALLEL_JOBS)

# ======================== 路径配置 ========================
PROJECT_ROOT := $(CURDIR)
SELF_CONTAINED := $(PROJECT_ROOT)/SelfContainedLib
THEORIES := $(PROJECT_ROOT)/theories
QUANTUM := $(PROJECT_ROOT)/Quantum
CS_NULL := $(PROJECT_ROOT)/CS_Null
TEST := $(PROJECT_ROOT)/Test

# 外部库路径检测
MATHLIB_PATH ?= $(shell opam var coq-mathlib:lib 2>/dev/null || echo "")
STDLIB_PATH ?= $(shell $(COQC) -where 2>/dev/null)/../user-contrib

# ======================== 文件集合 ========================
# 层级1: 自包含基础库
CORE_BASE := \
	$(SELF_CONTAINED)/Algebra.v \
	$(SELF_CONTAINED)/Geometry.v \
	$(SELF_CONTAINED)/Category.v

# 层级2: FRF元理论
CORE_FRF := \
	$(THEORIES)/FRF_MetaTheory.v \
	$(THEORIES)/ChurchZero.v \
	$(THEORIES)/ChurchNumerals.v

# 层级3: 数学场景
CORE_SCENES := \
	$(THEORIES)/CaseA_SetTheory.v \
	$(THEORIES)/CaseB_Algebra.v \
	$(THEORIES)/CaseC_TypeTheory.v \
	$(THEORIES)/CaseD_CategoryTheory.v \
	$(THEORIES)/CaseE_QuantumVacuum.v

# 层级4: 扩展模块
EXTENSION_MODULES := \
	$(QUANTUM)/QFT_FRF.v \
	$(QUANTUM)/CurvedSpacetimeQFT.v \
	$(CS_NULL)/FRF_CS_Null_Common.v \
	$(CS_NULL)/FRF_CS_Null.v \
	$(CS_NULL)/CxxNull.v \
	$(CS_NULL)/PythonNull.v \
	$(CS_NULL)/JavaNull.v \
	$(CS_NULL)/MathNull.v \
	$(CS_NULL)/RustNull.v

# 层级5: 集成模块
INTEGRATION_MODULES := \
	$(THEORIES)/FRF_Comparative.v

# 层级6: 测试套件
TEST_MODULES := \
	$(TEST)/Test_Basic.v \
	$(TEST)/Test_FRF_MetaTheory.v \
	$(TEST)/Test_QuantumVacuum.v \
	$(TEST)/Test_BlockchainSystem.v \
	$(TEST)/SelfContainedVerification.v

# 所有源文件
ALL_SRC_FILES := $(CORE_BASE) $(CORE_FRF) $(CORE_SCENES) \
                 $(EXTENSION_MODULES) $(INTEGRATION_MODULES) $(TEST_MODULES)

# ======================== 大文件识别 ========================
# 基于行数的大文件识别函数
define IS_HUGE_FILE
$(shell wc -l < "$1" 2>/dev/null | awk '$$1 > 3000 {print "YES"}')
endef

# 大文件列表（用于特殊处理）
HUGE_FILES := \
	$(SELF_CONTAINED)/Geometry.v \
	$(THEORIES)/FRF_MetaTheory.v \
	$(THEORIES)/ChurchNumerals.v \
	$(THEORIES)/CaseE_QuantumVacuum.v \
	$(CS_NULL)/FRF_CS_Null_Common.v \
	$(THEORIES)/FRF_Comparative.v

# ======================== 编译标志 ========================
# 基础标志
BASE_COQFLAGS := -R $(SELF_CONTAINED) SelfContainedLib \
                 -R $(THEORIES) theories \
                 -R $(QUANTUM) Quantum \
                 -R $(CS_NULL) CS_Null \
                 -R $(TEST) Test

# 版本特定标志
ifeq ($(COQ_MAJOR).$(COQ_MINOR),8.18)
	VERSION_FLAGS := -w -deprecated
else ifeq ($(COQ_MAJOR).$(COQ_MINOR),8.17)
	VERSION_FLAGS := -w -deprecated-since,8.18
else
	VERSION_FLAGS := -w -deprecated
endif

# 外部库包含
ifneq ($(MATHLIB_PATH),)
	BASE_COQFLAGS += -R $(MATHLIB_PATH) Mathlib
endif

ifneq ($(STDLIB_PATH),)
	BASE_COQFLAGS += -R $(STDLIB_PATH) Stdlib
endif

# 动态内存管理
AVAIL_MEM := $(shell free -m 2>/dev/null | awk '/^Mem:/{print $$7}' || echo 4096)
ifeq ($(shell echo "$(AVAIL_MEM) > 16000" | bc 2>/dev/null),1)
	MEMORY_FLAGS := -m 16384
else ifeq ($(shell echo "$(AVAIL_MEM) > 8000" | bc 2>/dev/null),1)
	MEMORY_FLAGS := -m 8192
else ifeq ($(shell echo "$(AVAIL_MEM) > 4000" | bc 2>/dev/null),1)
	MEMORY_FLAGS := -m 4096
else
	MEMORY_FLAGS := -m 2048
endif

# 大文件特殊标志
BIGFILE_FLAGS := $(MEMORY_FLAGS) -async-proofs on -async-proofs-tac-j $(PARALLEL_JOBS)

# 最终标志
COQFLAGS := $(BASE_COQFLAGS) $(VERSION_FLAGS) $(MEMORY_FLAGS)

# ======================== 编译规则 ========================
# 智能编译规则
define COMPILE_RULE
$(info 编译: $(notdir $<) [$(shell wc -l < "$<" 2>/dev/null || echo 0)行])
@if echo "$(HUGE_FILES)" | grep -q "$<"; then \
	echo "  大文件: 使用增强编译参数"; \
	$(COQC) $(BASE_COQFLAGS) $(VERSION_FLAGS) $(BIGFILE_FLAGS) "$<"; \
else \
	$(COQC) $(COQFLAGS) "$<"; \
fi
endef

# 默认编译规则
%.vo: %.v
	$(COMPILE_RULE)

# 依赖生成
%.d: %.v
	@$(COQDEP) $(BASE_COQFLAGS) "$<" > "$@" 2>/dev/null || true

# ======================== 主目标 ========================
# 完整构建（默认）
all: check-env core-base core-frf core-scenes extensions integrations tests
	@echo "✅ FRF2.0 完整构建完成"

# 检查构建环境
check-env:
	@echo "检查构建环境..."
	@echo "Coq版本: $(COQ_VERSION)"
	@echo "并行任务: $(PARALLEL_JOBS)"
	@echo "可用内存: $(AVAIL_MEM) MB"
	@echo "大文件数量: $(words $(HUGE_FILES))"
	@if [ -z "$(MATHLIB_PATH)" ]; then \
		echo "⚠️  警告: Mathlib路径未找到，某些模块可能编译失败"; \
	fi

# 层级1: 自包含基础库（完全并行）
core-base: $(CORE_BASE:.v=.vo)
	@echo "✅ 基础库编译完成"

# 层级2: FRF元理论（完全并行）
core-frf: core-base $(CORE_FRF:.v=.vo)
	@echo "✅ FRF元理论编译完成"

# 层级3: 数学场景（部分并行）
core-scenes: core-frf $(CORE_SCENES:.v=.vo)
	@echo "✅ 数学场景编译完成"

# 层级4: 扩展模块（依赖复杂，需要串行）
extensions: core-scenes
	@echo "编译扩展模块..."
	@$(MAKE) -j1 $(EXTENSION_MODULES:.v=.vo)
	@echo "✅ 扩展模块编译完成"

# 层级5: 集成模块
integrations: extensions $(INTEGRATION_MODULES:.v=.vo)
	@echo "✅ 集成模块编译完成"

# 层级6: 测试套件（并行）
tests: integrations $(TEST_MODULES:.v=.vo)
	@echo "✅ 测试套件编译完成"

# ======================== 实用目标 ========================
# 清理
clean:
	@echo "清理编译文件..."
	@find . -name "*.vo" -delete
	@find . -name "*.glob" -delete
	@find . -name "*.v.d" -delete
	@find . -name "*.aux" -delete
	@echo "✅ 清理完成"

clean-all: clean
	@find . -name "*.pdf" -delete
	@find . -name "*.html" -delete
	@find . -name "*.dot" -delete
	@find . -name "*.png" -delete

# 依赖图生成
depgraph:
	@echo "生成依赖图..."
	@$(COQDEP) $(BASE_COQFLAGS) $(ALL_SRC_FILES) > dependencies.dot 2>/dev/null
	@if command -v dot >/dev/null; then \
		dot -Tpng dependencies.dot -o dependencies.png; \
		echo "✅ 依赖图已生成: dependencies.png"; \
	else \
		echo "⚠️  Graphviz未安装，无法生成图片"; \
	fi

# 报告生成
report: integrations
	@echo "生成FRF跨系统对比报告..."
	@if [ -f "$(THEORIES)/FRF_Comparative.vo" ]; then \
		$(COQTOP) $(BASE_COQFLAGS) -batch \
			-eval 'Declare ML Module "frf_verify_report".' \
			-eval 'LoadPath := "$(PROJECT_ROOT)" :: LoadPath.' \
			-eval 'From FRF_Comparative Require Import default_comparative_report.' \
			-eval 'write_file "frf_report.json" (default_comparative_report [] AllTheoremsInModule [] (fun _ _ => None)).' && \
		echo "✅ 报告数据已生成: frf_report.json"; \
	else \
		echo "❌ FRF_Comparative未编译，无法生成报告"; \
	fi

# 快速验证（仅编译核心）
quick: core-base core-frf
	@echo "✅ 快速验证完成"

# 仅测试
test-only: $(TEST_MODULES:.v=.vo)
	@echo "✅ 测试编译完成"

# ======================== 监控目标 ========================
# 编译统计
stats:
	@echo "📊 FRF2.0项目统计"
	@echo "总文件数: $(words $(ALL_SRC_FILES))"
	@echo "总代码行数: $$(wc -l $(ALL_SRC_FILES) 2>/dev/null | tail -1 | awk '{print $$1}' || echo 0)"
	@echo "大文件(>3000行): $(words $(HUGE_FILES))"
	@echo "实数依赖文件: $$(grep -l "Require.*Reals" $(ALL_SRC_FILES) 2>/dev/null | wc -l || echo 0)"
	@echo "外部依赖: $$(if [ -n "$(MATHLIB_PATH)" ]; then echo "Mathlib 3.74.0"; else echo "无"; fi)"

# 内存监控
monitor:
	@echo "📈 内存使用监控"
	@echo "当前内存: $$(free -m | awk '/^Mem:/{printf "%.1f/%.1f MB", $$3, $$2}')"
	@echo "可用内存: $(AVAIL_MEM) MB"
	@echo "交换空间: $$(free -m | awk '/^Swap:/{printf "%.1f MB", $$3}')"

# ======================== 环境设置 ========================
# OPAM环境设置（可选）
setup-env:
	@echo "设置OPAM环境..."
	@opam switch create frf2.0 ocaml-base-compiler.4.14.1 2>/dev/null || true
	@opam switch set frf2.0
	@opam repo add coq-released https://coq.inria.fr/opam/released
	@opam update
	@opam install coq.8.18.0 coq-mathlib.3.74.0 coq-stdlib
	@echo "✅ 环境设置完成"

# ======================== Docker支持 ========================
# Docker构建
docker-build:
	@if command -v docker >/dev/null; then \
		echo "构建Docker镜像..."; \
		docker build -t frf2.0 .; \
	else \
		echo "❌ Docker未安装"; \
	fi

docker-run: docker-build
	@docker run -it --rm -v $(PWD):/frf2.0 frf2.0 make all

# ======================== CI/CD支持 ========================
# GitHub Actions兼容
ci-test:
	@echo "运行CI测试..."
	@$(MAKE) clean
	@$(MAKE) -j2 all
	@echo "✅ CI测试通过"

# ======================== 包含依赖文件 ========================
# 自动包含生成的依赖文件
-include $(ALL_SRC_FILES:.v=.d)

# ======================== Phony目标声明 ========================
.PHONY: all check-env core-base core-frf core-scenes extensions integrations tests \
        clean clean-all depgraph report quick test-only stats monitor \
        setup-env docker-build docker-run ci-test

# ======================== 帮助信息 ========================
help:
	@echo "FRF2.0形式化分析验证系统 - Makefile帮助"
	@echo ""
	@echo "主要目标:"
	@echo "  all          完整构建整个项目（默认）"
	@echo "  quick        快速验证（仅编译核心）"
	@echo "  clean        清理编译文件"
	@echo "  clean-all    清理所有生成文件"
	@echo ""
	@echo "模块化构建:"
	@echo "  core-base    编译自包含基础库（层级1）"
	@echo "  core-frf     编译FRF元理论（层级2）"
	@echo "  core-scenes  编译数学场景（层级3）"
	@echo "  extensions   编译扩展模块（层级4）"
	@echo "  integrations 编译集成模块（层级5）"
	@echo "  tests        编译测试套件（层级6）"
	@echo ""
	@echo "实用工具:"
	@echo "  depgraph     生成项目依赖图"
	@echo "  report       生成FRF跨系统对比报告"
	@echo "  stats        显示项目统计信息"
	@echo "  monitor      显示内存使用情况"
	@echo ""
	@echo "环境管理:"
	@echo "  setup-env    设置OPAM开发环境"
	@echo "  docker-build 构建Docker镜像"
	@echo "  docker-run   在Docker中运行构建"
	@echo "  ci-test      运行CI测试（简化版）"
	@echo ""
	@echo "配置:"
	@echo "  PARALLEL_JOBS=8   设置并行任务数"
	@echo "  COQC=custom-coqc  使用自定义Coq编译器"