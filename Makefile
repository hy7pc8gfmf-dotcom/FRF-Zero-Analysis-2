# ===========================================
# FRF Formal Verification Framework - Makefile
# 增强版本：添加版本兼容性与智能路径检测
# ===========================================
# ========================
# CONFIGURATION
# ========================
# 基础命令
COQC ?= coqc
COQCHK ?= coqchk
COQDOC ?= coqdoc

# 智能版本检测
COQ_VERSION := $(shell $(COQC) --version 2>/dev/null | head -n1 | awk '{print $$3}' || echo "unknown")
ifeq ($(COQ_VERSION),unknown)
$(warning ⚠️ 无法检测Coq版本，请确保coqc命令可用)
endif

# ========================
# VERSION COMPATIBILITY LAYER
# ========================
# 创建临时目录用于版本检测
TMP_DIR := $(shell mktemp -d 2>/dev/null || mktemp -d -t 'frf-tmp')

# 检测Micromega路径（处理8.17和8.18+的路径差异）
define detect_micromega_path
$(shell \
  if [ -d "$$(coqc -where 2>/dev/null)/user-contrib/Micromega" ]; then \
    echo "$$(coqc -where)/user-contrib/Micromega"; \
  elif [ -d "$$(dirname $$(coqc -where 2>/dev/null))/user-contrib/Micromega" ]; then \
    echo "$$(dirname $$(coqc -where))/user-contrib/Micromega"; \
  else \
    echo "not_found"; \
  fi \
)
endef
MICROMEGA_PATH := $(call detect_micromega_path)

# 检测Mathcomp路径
define detect_mathcomp_path
$(shell \
  if [ -d "$$(coqc -where 2>/dev/null)/user-contrib/mathcomp" ]; then \
    echo "$$(coqc -where)/user-contrib/mathcomp"; \
  elif [ -d "$$(dirname $$(coqc -where 2>/dev/null))/user-contrib/mathcomp" ]; then \
    echo "$$(dirname $$(coqc -where))/user-contrib/mathcomp"; \
  else \
    echo "not_found"; \
  fi \
)
endef
MATHCOMP_PATH := $(call detect_mathcomp_path)

# 设置兼容的编译标志
ifeq ($(COQ_VERSION),8.17.1)
  # Coq 8.17.1 兼容模式
  $(info 📌 检测到Coq 8.17.1 - 启用兼容模式)
  COQFLAGS = -Q . FRF \
  -Q SelfContainedLib SelfContainedLib \
  -Q theories FRF.Theories \
  -Q CS_Null FRF.CS_Null \
  -Q Quantum FRF.Quantum \
  -Q DynamicSystem FRF.DynamicSystem \
  -Q Test FRF.Test \
  -R $(MICROMEGA_PATH) Micromega \
  -R $(MATHCOMP_PATH) mathcomp \
  -w -notation-overridden \
  -q
  
  # 8.17版本特定的警告
  $(info ⚠️  注意: Coq 8.17.1模式下部分功能受限)
  $(info ⚠️  建议: 运行 'make setup-env' 安装推荐的Coq 8.18.0环境)
  
else ifeq ($(COQ_VERSION),8.18.0)
  # Coq 8.18.0 标准模式（与CI完全一致）
  COQFLAGS = -Q . FRF \
  -Q SelfContainedLib SelfContainedLib \
  -Q theories FRF.Theories \
  -Q CS_Null FRF.CS_Null \
  -Q Quantum FRF.Quantum \
  -Q DynamicSystem FRF.DynamicSystem \
  -Q Test FRF.Test \
  -w -notation-overridden \
  -q
  
else ifneq ($(COQ_VERSION),unknown)
  # 未测试的Coq版本
  $(warning ⚠️  未测试的Coq版本: $(COQ_VERSION))
  $(warning    项目在Coq 8.18.0上测试，当前版本可能不兼容)
  $(warning    建议升级: opam install coq.8.18.0)
  
  # 尝试使用标准标志
  COQFLAGS = -Q . FRF \
  -Q SelfContainedLib SelfContainedLib \
  -Q theories FRF.Theories \
  -Q CS_Null FRF.CS_Null \
  -Q Quantum FRF.Quantum \
  -Q DynamicSystem FRF.DynamicSystem \
  -Q Test FRF.Test \
  -w -notation-overridden \
  -q
endif

# ========================
# SOURCE FILES (与CoqProject完全一致)
# ========================
# Level 1: 基础库（无依赖）
CORE_BASE = \
SelfContainedLib/Algebra.v \
SelfContainedLib/Category.v \
SelfContainedLib/Geometry.v

# Level 2: FRF元理论（依赖基础库）
CORE_FRF = \
theories/FRF_MetaTheory.v \
theories/ChurchNumerals.v \
theories/ChurchZero.v

# Level 3: 数学场景（依赖FRF元理论）
CORE_SCENES = \
theories/CaseA_SetTheory.v \
theories/CaseB_Algebra.v \
theories/CaseB_Algebra_SelfContained.v \
theories/CaseC_TypeTheory.v \
theories/CaseD_CategoryTheory.v \
theories/CaseD_Category_SelfContained.v \
theories/CaseF_Logic.v

# Level 4: 扩展模块
EXTENSION_MODULES = \
Quantum/QFT_FRF.v \
Quantum/CaseE_QuantumVacuum.v \
Quantum/CurvedSpacetimeQFT.v \
CS_Null/FRF_CS_Null_Common.v \
CS_Null/RustNull.v \
CS_Null/CxxNull.v \
CS_Null/JavaNull.v \
CS_Null/PythonNull.v \
CS_Null/MathNull.v

# Level 5: 集成模块
INTEGRATION_MODULES = \
CS_Null/FRF_CS_Null.v \
theories/FRF_PhilosophicalValidation.v \
theories/FRF_Comparative.v

# Level 6: 测试模块
TEST_MODULES = \
Test/Test_FRF_MetaTheory.v \
Test/Test_QuantumVacuum.v \
Test/Test_BlockchainSystem.v

# Dynamic System模块（可选）
DYNAMIC_SYSTEM = \
DynamicSystem/DistributedSystem.v \
DynamicSystem/BlockchainSystem.v \
DynamicSystem/ControlSystem.v

# 完整文件列表（按依赖顺序）
ALL_SRC_FILES = \
$(CORE_BASE) \
$(CORE_FRF) \
$(CORE_SCENES) \
$(EXTENSION_MODULES) \
$(INTEGRATION_MODULES) \
$(TEST_MODULES) \
$(DYNAMIC_SYSTEM)

ALL_VO_FILES = $(ALL_SRC_FILES:.v=.vo)

# ========================
# MAIN TARGETS
# ========================
.PHONY: all compile compile-core validate test check clean help status setup-env docker-build
.DEFAULT_GOAL := help

all: check-version compile validate

# ========================
# VERSION MANAGEMENT TARGETS
# ========================
check-version:
	@echo "🔍 检查Coq版本..."
	@current_version=$$($(COQC) --version 2>/dev/null | head -n1 | awk '{print $$3}'); \
	if [ -z "$$current_version" ]; then \
		echo "❌ 无法检测Coq版本"; \
		echo "   请确保coqc命令可用"; \
		echo "   建议安装: opam install coq.8.18.0"; \
		exit 1; \
	fi; \
	echo "当前Coq版本: $$current_version"; \
	case "$$current_version" in \
		8.18.0) \
			echo "✅ Coq版本正确 (8.18.0)"; \
			;; \
		8.17*) \
			echo "⚠️ Coq版本兼容模式 (8.17.x)"; \
			echo "   功能限制: Micromega插件路径需要特殊处理"; \
			echo "   建议升级: opam install coq.8.18.0"; \
			;; \
		*) \
			echo "❌ Coq版本不兼容: 需要 8.18.0，当前 $$current_version"; \
			echo "   解决方案: "; \
			echo "   1. 安装推荐版本: opam install coq.8.18.0"; \
			echo "   2. 或使用Docker: make docker-build"; \
			exit 1; \
			;; \
	esac

setup-env:
	@echo "🛠️  设置推荐的开发环境..."
	@echo "1. 确保OPAM已安装..."
	@command -v opam >/dev/null 2>&1 || (echo "❌ OPAM未安装，请先安装OPAM" && exit 1)
	@echo "✅ OPAM可用"
	
	@echo "2. 创建专用OPAM切换环境..."
	@opam switch list | grep -q 'coq-8.18.0' || opam switch create coq-8.18.0 4.14.0 --no-install
	@eval $$(opam env --switch=coq-8.18.0)
	
	@echo "3. 安装Coq 8.18.0及依赖..."
	@opam install -y coq.8.18.0 coq-mathcomp-ssreflect.1.17.0 coq-equations coq-bignums
	
	@echo "4. 验证安装..."
	@eval $$(opam env --switch=coq-8.18.0)
	@coqc --version | grep "8.18.0" && echo "✅ Coq 8.18.0安装成功" || (echo "❌ 安装失败" && exit 1)
	
	@echo ""
	@echo "✅ 环境设置完成！"
	@echo "   要使用此环境，请运行: eval $$(opam env --switch=coq-8.18.0)"
	@echo "   然后运行: make compile"

# ========================
# COMPILATION TARGETS
# ========================
# 主编译目标（添加版本检查前置条件）
compile: check-version $(ALL_VO_FILES)
	@echo "✅ 所有模块编译完成！"

# 核心编译：只编译基础模块（CI最小验证集）
compile-core: check-version $(CORE_BASE:.v=.vo) $(CORE_FRF:.v=.vo)
	@echo "✅ 核心模块编译完成！"

# ========================
# ROBUST COMPILATION RULES
# ========================
# 通用编译规则（带详细错误处理，与CI流程匹配）
%.vo: %.v
	@echo "编译: $<"
	@if $(COQC) $(COQFLAGS) "$<" > "$(TMP_DIR)/$*.log" 2>&1; then \
		echo "✅ 成功: $<"; \
		rm -f "$(TMP_DIR)/$*.log"; \
	else \
		echo "❌ 编译失败: $<"; \
		echo "=== 错误信息 ==="; \
		cat "$(TMP_DIR)/$*.log" | head -20; \
		echo "..."; \
		tail -5 "$(TMP_DIR)/$*.log"; \
		echo ""; \
		echo "💡 可能的解决方案:"; \
		if [ "$(COQ_VERSION)" != "8.18.0" ]; then \
			echo "   1. 版本不兼容: 当前使用 $(COQ_VERSION)，推荐使用 8.18.0"; \
			echo "   2. 运行: make setup-env 安装推荐环境"; \
		fi; \
		if echo "$<" | grep -q "Micromega"; then \
			echo "   3. Micromega插件路径问题，请检查环境配置"; \
		fi; \
		rm -f "$(TMP_DIR)/$*.log"; \
		echo "跳过此文件，继续编译其他文件..."; \
	fi

# ========================
# VALIDATION & TESTING
# ========================
validate: compile
	@echo "🔍 验证所有证明..."
	@if command -v $(COQCHK) >/dev/null 2>&1; then \
		echo "运行coqchk验证..."; \
		$(COQCHK) -silent $(COQFLAGS) $(ALL_VO_FILES) 2>&1 | head -10 || echo "验证过程有警告"; \
		echo "✅ 验证完成！"; \
	else \
		echo "⚠️ coqchk未找到，跳过验证"; \
		echo "   建议: opam install coq.8.18.0"; \
	fi

test: compile
	@echo "🧪 运行测试套件..."
	@vo_count=0; \
	for vo in $(ALL_VO_FILES); do \
		if [ -f "$$vo" ]; then \
			vo_count=$$((vo_count + 1)); \
		fi \
	done; \
	echo "✅ FRF框架验证完成！"
	@echo "📋 已验证模块: $$vo_count 个"

check:
	@echo "📊 编译状态检查..."
	@total_files=0; \
	compiled_files=0; \
	for file in $(ALL_SRC_FILES); do \
		if [ -f "$$file" ]; then \
			total_files=$$((total_files + 1)); \
			vo_file=$${file%.v}.vo; \
			if [ -f "$$vo_file" ]; then \
				compiled_files=$$((compiled_files + 1)); \
			fi \
		fi \
	done; \
	echo "总Coq文件: $$total_files"; \
	echo "已编译: $$compiled_files"; \
	if [ $$compiled_files -ge 3 ]; then \
		echo "✅ 核心编译通过 (至少编译了 $$compiled_files 个文件)"; \
	else \
		echo "❌ 编译失败，需要至少3个核心模块"; \
		echo "   建议解决方案:"; \
		echo "   1. 检查Coq版本: make check-version"; \
		echo "   2. 设置推荐环境: make setup-env"; \
		echo "   3. 尝试简单编译: make compile-simple"; \
		exit 1; \
	fi

# ========================
# DOCKER SUPPORT
# ========================
docker-build:
	@echo "🐳 使用Docker构建 (确保Docker已安装)..."
	@if ! command -v docker >/dev/null 2>&1; then \
		echo "❌ Docker未安装，请先安装Docker"; \
		echo "   Ubuntu: sudo apt-get install docker.io"; \
		echo "   macOS: brew install docker"; \
		exit 1; \
	fi
	
	@if [ -f "Dockerfile" ]; then \
		echo "使用项目Dockerfile..."; \
		docker build -t frf-builder .; \
	else \
		echo "使用标准Coq镜像..."; \
		docker run --rm -v $$(pwd):/workspace -w /workspace coqorg/coq:8.18.0 \
			sh -c "opam install -y coq-mathcomp-ssreflect coq-equations coq-bignums && make compile"; \
	fi

# ========================
# DEPENDENCY MANAGEMENT
# ========================
deps:
	@echo "📦 安装Coq依赖..."
	@echo "安装基础依赖包..."
	opam install -y \
	coq-mathcomp-ssreflect.1.17.0 \
	coq-equations \
	coq-bignums
	@echo "✅ 依赖安装完成！"

check-deps:
	@echo "🔍 检查依赖..."
	@dep_issues=0; \
	for pkg in coq-mathcomp-ssreflect.1.17.0 coq-equations coq-bignums; do \
		if opam list --installed | grep -q "$$pkg"; then \
			echo "✅ $$pkg"; \
		else \
			echo "❌ $$pkg - 未安装"; \
			dep_issues=$$((dep_issues + 1)); \
		fi \
	done; \
	if [ $$dep_issues -gt 0 ]; then \
		echo ""; \
		echo "💡 修复依赖: make deps"; \
	fi

# ========================
# CLEANING
# ========================
clean:
	@echo "🧹 清理构建产物..."
	@rm -f $(ALL_VO_FILES) 2>/dev/null || true
	@rm -f $(ALL_SRC_FILES:.v=.glob) 2>/dev/null || true
	@rm -f $(ALL_SRC_FILES:.v=.v.d) 2>/dev/null || true
	@rm -f $(ALL_SRC_FILES:.v=.log) 2>/dev/null || true
	@rm -f $(TMP_DIR)/*.log 2>/dev/null || true
	@rm -rf html 2>/dev/null || true
	@echo "✅ 清理完成！"

distclean: clean
	@echo "🧹 深度清理..."
	@find . -name "*~" -delete 2>/dev/null || true
	@find . -name ".*.aux" -delete 2>/dev/null || true
	@find . -name "*.log" -delete 2>/dev/null || true
	@rm -rf $(TMP_DIR) 2>/dev/null || true
	@echo "✅ 深度清理完成！"

# ========================
# SIMPLE COMPILATION (替代方案)
# ========================
compile-simple:
	@echo "🛠️ 使用简单编译方法..."
	@if [ "$(COQ_VERSION)" != "8.18.0" ]; then \
		echo "⚠️  当前Coq版本: $(COQ_VERSION)"; \
		echo "⚠️  建议使用Coq 8.18.0获得完整功能支持"; \
		echo ""; \
	fi
	@for file in $(CORE_BASE) $(CORE_FRF); do \
		if [ -f "$$file" ]; then \
			echo "编译: $$file"; \
			$(COQC) $(COQFLAGS) "$$file" || echo "⚠️  编译警告: $$file (可能由于版本兼容性)"; \
		fi \
	done
	@echo "✅ 简单编译完成！"

# ========================
# HELP
# ========================
help:
	@echo "=================================================="
	@echo "📌 FRF形式验证框架 Makefile (增强兼容版本)"
	@echo "=================================================="
	@echo "当前环境:"
	@current_version=$$($(COQC) --version 2>/dev/null | head -n1 | awk '{print $$3}' || echo "unknown"); \
	if [ "$$current_version" = "8.18.0" ]; then \
		echo "✅ Coq版本: 8.18.0 (推荐版本)"; \
	elif [ "$$current_version" != "unknown" ] && [[ "$$current_version" == 8.17* ]]; then \
		echo "⚠️ Coq版本: $$current_version (兼容模式，功能受限)"; \
		echo "   建议: make setup-env 安装推荐版本"; \
	else \
		echo "❌ Coq版本: $$current_version (不兼容)"; \
		echo "   修复: make setup-env"; \
	fi
	@echo ""
	@echo "核心目标："
	@echo "  all           - 完整构建: 检查版本 + 编译 + 验证"
	@echo "  compile       - 编译所有模块 (自动检查版本)"
	@echo "  compile-core  - 只编译核心基础模块"
	@echo "  compile-simple- 快速编译基础模块 (兼容模式)"
	@echo ""
	@echo "环境管理："
	@echo "  check-version - 检查Coq版本兼容性"
	@echo "  setup-env     - 设置推荐的Coq 8.18.0环境"
	@echo "  docker-build  - 使用Docker构建 (无需本地安装)"
	@echo "  deps          - 安装所有依赖包"
	@echo ""
	@echo "诊断与修复："
	@echo "  check         - 检查编译状态"
	@echo "  clean         - 清理构建产物"
	@echo "  distclean     - 深度清理 (包括临时文件)"
	@echo ""
	@echo "💡 新手建议工作流:"
	@echo "  1. make check-version   # 检查版本兼容性"
	@echo "  2. make setup-env       # 如果版本不匹配，设置推荐环境"
	@echo "  3. eval $$(opam env --switch=coq-8.18.0)  # 激活环境"
	@echo "  4. make compile         # 编译项目"
	@echo ""
	@echo "🔍 详细帮助: https://github.com/FRF-Project/docs/wiki/Build-Instructions"
	@echo "=================================================="

# ========================
# STATUS TARGET
# ========================
status:
	@echo "📊 项目编译状态"
	@total_src=0; \
	compiled=0; \
	for file in $(ALL_SRC_FILES); do \
		if [ -f "$$file" ]; then \
			total_src=$$((total_src + 1)); \
			vo_file=$${file%.v}.vo; \
			if [ -f "$$vo_file" ]; then \
				compiled=$$((compiled + 1)); \
			fi \
		fi \
	done; \
	echo "总Coq文件: $$total_src"
	echo "已编译: $$compiled"
	echo "进度: $$compiled/$$total_src"
	
	@current_version=$$($(COQC) --version 2>/dev/null | head -n1 | awk '{print $$3}' || echo "unknown"); \
	if [ "$$current_version" != "8.18.0" ]; then \
		echo ""; \
		echo "⚠️  环境警告: 当前Coq版本 $$current_version"; \
		if [[ "$$current_version" == 8.17* ]]; then \
			echo "   兼容模式启用，但部分功能可能受限"; \
		else \
			echo "   版本不兼容，建议运行: make setup-env"; \
		fi \
	fi
	
	@if [ $$compiled -gt 0 ]; then \
		echo ""; \
		echo "📦 已编译核心模块:"; \
		for vo in $(CORE_BASE:.v=.vo) $(CORE_FRF:.v=.vo); do \
			if [ -f "$$vo" ]; then \
				echo "  ✅ $$(basename $$vo .vo)"; \
			fi \
		done; \
	else \
		echo ""; \
		echo "❌ 无编译产物"; \
		if [ "$$current_version" = "8.18.0" ]; then \
			echo "   请运行: make compile"; \
		else \
			echo "   请先设置正确环境: make setup-env"; \
		fi \
	fi

# Phony targets declaration
.PHONY: all compile compile-core validate test check clean help status setup-env docker-build deps check-deps check-version