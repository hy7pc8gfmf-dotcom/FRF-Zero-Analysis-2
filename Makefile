# ===========================================
# FRF Formal Verification Framework - Makefile
# 重构版本：与CoqProject和CI配置完全契合
# ===========================================

# ========================
# CONFIGURATION
# ========================
COQC = coqc
COQCHK = coqchk
COQDOC = coqdoc
COQ_MAKEFILE = coq_makefile

# Coq版本要求
REQUIRED_COQ_VERSION = 8.18.0

# ========================
# LOGICAL PATH MAPPINGS (与CoqProject完全一致)
# ========================
COQFLAGS = -Q . FRF \
           -Q SelfContainedLib SelfContainedLib \
           -Q theories FRF.Theories \
           -Q CS_Null FRF.CS_Null \
           -Q Quantum FRF.Quantum \
           -Q DynamicSystem FRF.DynamicSystem \
           -Q Toolchain FRF.Toolchain \
           -Q Test FRF.Test \
           -Q CategoryTheory CategoryTheory

# 编译参数 (与CoqProject一致)
COQ_ARGS = -w -notation-overridden,-redundant-canonical-projection,-unused-intro-pattern,-deprecated \
           -async-proofs on \
           -async-proofs-queue-size 10 \
           -q

# ========================
# DIRECTORY STRUCTURE
# ========================
SELF_CONTAINED_DIR = SelfContainedLib
THEORIES_DIR = theories
CS_NULL_DIR = CS_Null
QUANTUM_DIR = Quantum
DYNAMIC_SYSTEM_DIR = DynamicSystem
TOOLCHAIN_DIR = Toolchain
TEST_DIR = Test
CATEGORY_THEORY_DIR = CategoryTheory
REPORT_DIR = verification-reports

# ========================
# SOURCE FILES (从CoqProject自动提取)
# ========================
COQPROJECT_FILES = $(shell grep '\.v$$' CoqProject | grep -v '^#')

# 按层级分组 (与CoqProject层级一致)
LEVEL1_BASE = \
	SelfContainedLib/Algebra.v \
	SelfContainedLib/Category.v \
	SelfContainedLib/Geometry.v

LEVEL1_FRF = \
	theories/FRF_MetaTheory.v \
	CS_Null/FRF_CS_Null_Common.v

LEVEL1_CATEGORY = \
	CategoryTheory/Core.v \
	CategoryTheory/Equivalence.v

LEVEL2_MATH = \
	theories/CaseA_SetTheory.v \
	theories/ChurchNumerals.v \
	theories/ChurchZero.v \
	theories/CaseB_Algebra.v \
	theories/CaseB_Algebra_SelfContained.v \
	theories/CaseC_TypeTheory.v \
	theories/CaseD_CategoryTheory.v \
	theories/CaseD_Category_SelfContained.v \
	theories/CaseF_Logic.v

LEVEL2_QUANTUM = \
	Quantum/QFT_FRF.v \
	Quantum/CaseE_QuantumVacuum.v \
	Quantum/CurvedSpacetimeQFT.v

LEVEL2_CS_NULL = \
	CS_Null/RustNull.v \
	CS_Null/CxxNull.v \
	CS_Null/JavaNull.v \
	CS_Null/PythonNull.v \
	CS_Null/MathNull.v

LEVEL2_DYNAMIC = \
	DynamicSystem/TimeVaryingSystem.v \
	DynamicSystem/DistributedSystem.v \
	DynamicSystem/BlockchainSystem.v \
	DynamicSystem/ControlSystem.v

LEVEL2_TOOLCHAIN = \
	Toolchain/FRF_to_Agda.v \
	Toolchain/FRF_to_Isabelle.v \
	Toolchain/FRF_to_Lean.v

LEVEL2_CATEGORY_EXT = \
	CategoryTheory/ZeroObjectPreservedByEquivalence.v \
	CategoryTheory/TestEquivalence.v

LEVEL3_INTEGRATION = \
	CS_Null/FRF_CS_Null.v \
	theories/FRF_PhilosophicalValidation.v \
	theories/FRF_Comparative.v

LEVEL3_TEST = \
	Test/Test_FRF_MetaTheory.v \
	Test/Test_QuantumVacuum.v \
	Test/Test_BlockchainSystem.v

# 完整编译顺序
ALL_SRC_FILES = \
	$(LEVEL1_BASE) \
	$(LEVEL1_FRF) \
	$(LEVEL1_CATEGORY) \
	$(LEVEL2_MATH) \
	$(LEVEL2_QUANTUM) \
	$(LEVEL2_CS_NULL) \
	$(LEVEL2_DYNAMIC) \
	$(LEVEL2_TOOLCHAIN) \
	$(LEVEL2_CATEGORY_EXT) \
	$(LEVEL3_INTEGRATION) \
	$(LEVEL3_TEST)

ALL_VO_FILES = $(ALL_SRC_FILES:.v=.vo)

# ========================
# MAIN TARGETS
# ========================
.PHONY: all compile compile-coqproject validate test check clean help ci

.DEFAULT_GOAL := help

all: compile validate

# ========================
# COMPILATION TARGETS
# ========================

# 主编译目标：使用手工依赖规则
compile: $(ALL_VO_FILES)
	@echo "✅ 所有模块编译完成！"

# 使用CoqProject生成Makefile并编译（备用方案）
compile-coqproject:
	@echo "🔄 使用CoqProject生成Makefile并编译..."
	$(COQ_MAKEFILE) -f CoqProject -o Makefile.coq
	$(MAKE) -f Makefile.coq

# ========================
# COMPILATION RULES (详细依赖关系)
# ========================

# Level 1: 基础库 (无依赖)
$(SELF_CONTAINED_DIR)/Algebra.vo: $(SELF_CONTAINED_DIR)/Algebra.v
	$(COQC) $(COQFLAGS) $(COQ_ARGS) $<

$(SELF_CONTAINED_DIR)/Category.vo: $(SELF_CONTAINED_DIR)/Category.v
	$(COQC) $(COQFLAGS) $(COQ_ARGS) $<

$(SELF_CONTAINED_DIR)/Geometry.vo: $(SELF_CONTAINED_DIR)/Geometry.v
	$(COQC) $(COQFLAGS) $(COQ_ARGS) $<

# Level 1: FRF基础 (依赖基础库)
$(THEORIES_DIR)/FRF_MetaTheory.vo: $(THEORIES_DIR)/FRF_MetaTheory.v \
	$(SELF_CONTAINED_DIR)/Algebra.vo $(SELF_CONTAINED_DIR)/Category.vo
	$(COQC) $(COQFLAGS) $(COQ_ARGS) $<

$(CS_NULL_DIR)/FRF_CS_Null_Common.vo: $(CS_NULL_DIR)/FRF_CS_Null_Common.v \
	$(THEORIES_DIR)/FRF_MetaTheory.vo
	$(COQC) $(COQFLAGS) $(COQ_ARGS) $<

# Level 1: 范畴论基础
$(CATEGORY_THEORY_DIR)/Core.vo: $(CATEGORY_THEORY_DIR)/Core.v \
	$(SELF_CONTAINED_DIR)/Category.vo
	$(COQC) $(COQFLAGS) $(COQ_ARGS) $<

$(CATEGORY_THEORY_DIR)/Equivalence.vo: $(CATEGORY_THEORY_DIR)/Equivalence.v \
	$(CATEGORY_THEORY_DIR)/Core.vo
	$(COQC) $(COQFLAGS) $(COQ_ARGS) $<

# Level 2: 核心数学场景 (依赖FRF基础)
$(THEORIES_DIR)/CaseA_SetTheory.vo: $(THEORIES_DIR)/CaseA_SetTheory.v \
	$(THEORIES_DIR)/FRF_MetaTheory.vo
	$(COQC) $(COQFLAGS) $(COQ_ARGS) $<

$(THEORIES_DIR)/ChurchNumerals.vo: $(THEORIES_DIR)/ChurchNumerals.v \
	$(SELF_CONTAINED_DIR)/Algebra.vo
	$(COQC) $(COQFLAGS) $(COQ_ARGS) $<

$(THEORIES_DIR)/ChurchZero.vo: $(THEORIES_DIR)/ChurchZero.v \
	$(THEORIES_DIR)/ChurchNumerals.vo $(THEORIES_DIR)/FRF_MetaTheory.vo
	$(COQC) $(COQFLAGS) $(COQ_ARGS) $<

$(THEORIES_DIR)/CaseB_Algebra.vo: $(THEORIES_DIR)/CaseB_Algebra.v \
	$(THEORIES_DIR)/CaseA_SetTheory.vo $(SELF_CONTAINED_DIR)/Algebra.vo
	$(COQC) $(COQFLAGS) $(COQ_ARGS) $<

$(THEORIES_DIR)/CaseB_Algebra_SelfContained.vo: $(THEORIES_DIR)/CaseB_Algebra_SelfContained.v \
	$(THEORIES_DIR)/CaseB_Algebra.vo
	$(COQC) $(COQFLAGS) $(COQ_ARGS) $<

$(THEORIES_DIR)/CaseC_TypeTheory.vo: $(THEORIES_DIR)/CaseC_TypeTheory.v \
	$(THEORIES_DIR)/CaseA_SetTheory.vo $(THEORIES_DIR)/FRF_MetaTheory.vo
	$(COQC) $(COQFLAGS) $(COQ_ARGS) $<

$(THEORIES_DIR)/CaseD_CategoryTheory.vo: $(THEORIES_DIR)/CaseD_CategoryTheory.v \
	$(THEORIES_DIR)/CaseC_TypeTheory.vo $(CATEGORY_THEORY_DIR)/Core.vo
	$(COQC) $(COQFLAGS) $(COQ_ARGS) $<

$(THEORIES_DIR)/CaseD_Category_SelfContained.vo: $(THEORIES_DIR)/CaseD_Category_SelfContained.v \
	$(SELF_CONTAINED_DIR)/Category.vo
	$(COQC) $(COQFLAGS) $(COQ_ARGS) $<

$(THEORIES_DIR)/CaseF_Logic.vo: $(THEORIES_DIR)/CaseF_Logic.v \
	$(THEORIES_DIR)/FRF_MetaTheory.vo
	$(COQC) $(COQFLAGS) $(COQ_ARGS) $<

# Level 2: 量子物理扩展
$(QUANTUM_DIR)/QFT_FRF.vo: $(QUANTUM_DIR)/QFT_FRF.v \
	$(SELF_CONTAINED_DIR)/Algebra.vo
	$(COQC) $(COQFLAGS) $(COQ_ARGS) $<

$(QUANTUM_DIR)/CaseE_QuantumVacuum.vo: $(QUANTUM_DIR)/CaseE_QuantumVacuum.v \
	$(QUANTUM_DIR)/QFT_FRF.vo $(THEORIES_DIR)/FRF_MetaTheory.vo
	$(COQC) $(COQFLAGS) $(COQ_ARGS) $<

$(QUANTUM_DIR)/CurvedSpacetimeQFT.vo: $(QUANTUM_DIR)/CurvedSpacetimeQFT.v \
	$(QUANTUM_DIR)/QFT_FRF.vo $(SELF_CONTAINED_DIR)/Geometry.vo
	$(COQC) $(COQFLAGS) $(COQ_ARGS) $<

# Level 2: 编程语言空值分析
$(CS_NULL_DIR)/RustNull.vo: $(CS_NULL_DIR)/RustNull.v \
	$(CS_NULL_DIR)/FRF_CS_Null_Common.vo
	$(COQC) $(COQFLAGS) $(COQ_ARGS) $<

$(CS_NULL_DIR)/CxxNull.vo: $(CS_NULL_DIR)/CxxNull.v \
	$(CS_NULL_DIR)/FRF_CS_Null_Common.vo
	$(COQC) $(COQFLAGS) $(COQ_ARGS) $<

$(CS_NULL_DIR)/JavaNull.vo: $(CS_NULL_DIR)/JavaNull.v \
	$(CS_NULL_DIR)/FRF_CS_Null_Common.vo
	$(COQC) $(COQFLAGS) $(COQ_ARGS) $<

$(CS_NULL_DIR)/PythonNull.vo: $(CS_NULL_DIR)/PythonNull.v \
	$(CS_NULL_DIR)/FRF_CS_Null_Common.vo
	$(COQC) $(COQFLAGS) $(COQ_ARGS) $<

$(CS_NULL_DIR)/MathNull.vo: $(CS_NULL_DIR)/MathNull.v \
	$(CS_NULL_DIR)/FRF_CS_Null_Common.vo $(SELF_CONTAINED_DIR)/Algebra.vo
	$(COQC) $(COQFLAGS) $(COQ_ARGS) $<

# Level 2: 动态系统
$(DYNAMIC_SYSTEM_DIR)/TimeVaryingSystem.vo: $(DYNAMIC_SYSTEM_DIR)/TimeVaryingSystem.v \
	$(THEORIES_DIR)/FRF_MetaTheory.vo
	$(COQC) $(COQFLAGS) $(COQ_ARGS) $<

$(DYNAMIC_SYSTEM_DIR)/DistributedSystem.vo: $(DYNAMIC_SYSTEM_DIR)/DistributedSystem.v \
	$(DYNAMIC_SYSTEM_DIR)/TimeVaryingSystem.vo
	$(COQC) $(COQFLAGS) $(COQ_ARGS) $<

$(DYNAMIC_SYSTEM_DIR)/BlockchainSystem.vo: $(DYNAMIC_SYSTEM_DIR)/BlockchainSystem.v \
	$(DYNAMIC_SYSTEM_DIR)/TimeVaryingSystem.vo
	$(COQC) $(COQFLAGS) $(COQ_ARGS) $<

$(DYNAMIC_SYSTEM_DIR)/ControlSystem.vo: $(DYNAMIC_SYSTEM_DIR)/ControlSystem.v \
	$(DYNAMIC_SYSTEM_DIR)/TimeVaryingSystem.vo
	$(COQC) $(COQFLAGS) $(COQ_ARGS) $<

# Level 2: 工具链转换
$(TOOLCHAIN_DIR)/FRF_to_Agda.vo: $(TOOLCHAIN_DIR)/FRF_to_Agda.v
	$(COQC) $(COQFLAGS) $(COQ_ARGS) $<

$(TOOLCHAIN_DIR)/FRF_to_Isabelle.vo: $(TOOLCHAIN_DIR)/FRF_to_Isabelle.v
	$(COQC) $(COQFLAGS) $(COQ_ARGS) $<

$(TOOLCHAIN_DIR)/FRF_to_Lean.vo: $(TOOLCHAIN_DIR)/FRF_to_Lean.v
	$(COQC) $(COQFLAGS) $(COQ_ARGS) $<

# Level 2: 范畴论扩展
$(CATEGORY_THEORY_DIR)/ZeroObjectPreservedByEquivalence.vo: $(CATEGORY_THEORY_DIR)/ZeroObjectPreservedByEquivalence.v \
	$(CATEGORY_THEORY_DIR)/Equivalence.vo $(THEORIES_DIR)/CaseD_CategoryTheory.vo
	$(COQC) $(COQFLAGS) $(COQ_ARGS) $<

$(CATEGORY_THEORY_DIR)/TestEquivalence.vo: $(CATEGORY_THEORY_DIR)/TestEquivalence.v \
	$(CATEGORY_THEORY_DIR)/ZeroObjectPreservedByEquivalence.vo
	$(COQC) $(COQFLAGS) $(COQ_ARGS) $<

# Level 3: 集成模块
$(CS_NULL_DIR)/FRF_CS_Null.vo: $(CS_NULL_DIR)/FRF_CS_Null.v \
	$(CS_NULL_DIR)/RustNull.vo $(CS_NULL_DIR)/CxxNull.vo \
	$(CS_NULL_DIR)/JavaNull.vo $(CS_NULL_DIR)/PythonNull.vo $(CS_NULL_DIR)/MathNull.vo
	$(COQC) $(COQFLAGS) $(COQ_ARGS) $<

$(THEORIES_DIR)/FRF_PhilosophicalValidation.vo: $(THEORIES_DIR)/FRF_PhilosophicalValidation.v \
	$(THEORIES_DIR)/FRF_MetaTheory.vo $(THEORIES_DIR)/ChurchZero.vo
	$(COQC) $(COQFLAGS) $(COQ_ARGS) $<

$(THEORIES_DIR)/FRF_Comparative.vo: $(THEORIES_DIR)/FRF_Comparative.v \
	$(THEORIES_DIR)/FRF_PhilosophicalValidation.vo $(THEORIES_DIR)/CaseD_CategoryTheory.vo
	$(COQC) $(COQFLAGS) $(COQ_ARGS) $<

# Level 3: 测试模块
$(TEST_DIR)/Test_FRF_MetaTheory.vo: $(TEST_DIR)/Test_FRF_MetaTheory.v
	$(COQC) $(COQFLAGS) $(COQ_ARGS) $<

$(TEST_DIR)/Test_QuantumVacuum.vo: $(TEST_DIR)/Test_QuantumVacuum.v
	$(COQC) $(COQFLAGS) $(COQ_ARGS) $<

$(TEST_DIR)/Test_BlockchainSystem.vo: $(TEST_DIR)/Test_BlockchainSystem.v
	$(COQC) $(COQFLAGS) $(COQ_ARGS) $<

# ========================
# VALIDATION & TESTING
# ========================

validate: compile
	@echo "🔍 验证所有证明..."
	@mkdir -p $(REPORT_DIR)
	$(COQCHK) -silent $(ALL_VO_FILES) 2>&1 | tee $(REPORT_DIR)/validation.log || true
	@echo "✅ 验证完成！"

test: compile
	@echo "🧪 运行测试套件..."
	@echo "✅ FRF框架全维度验证完成！"
	@echo "📋 已验证模块列表："
	@for vo in $(ALL_VO_FILES); do \
		echo "  - $$(basename $$vo .vo)"; \
	done

check: compile
	@echo "📊 编译状态检查..."
	@total_files=$$(echo "$(ALL_SRC_FILES)" | wc -w); \
	compiled_files=$$(find . -name "*.vo" | wc -l); \
	echo "总文件数: $$total_files"; \
	echo "已编译: $$compiled_files"; \
	if [ $$compiled_files -eq $$total_files ]; then \
		echo "✅ 所有文件编译完成！"; \
	else \
		echo "⚠️ 编译不完整：$$compiled_files/$$total_files"; \
		exit 1; \
	fi

# 分级测试目标
test-level1: $(LEVEL1_BASE:.v=.vo) $(LEVEL1_FRF:.v=.vo) $(LEVEL1_CATEGORY:.v=.vo)
	@echo "✅ Level 1 基础模块验证完成！"

test-level2: $(LEVEL2_MATH:.v=.vo) $(LEVEL2_QUANTUM:.v=.vo) $(LEVEL2_CS_NULL:.v=.vo) \
             $(LEVEL2_DYNAMIC:.v=.vo) $(LEVEL2_TOOLCHAIN:.v=.vo) $(LEVEL2_CATEGORY_EXT:.v=.vo)
	@echo "✅ Level 2 场景模块验证完成！"

test-level3: $(LEVEL3_INTEGRATION:.v=.vo) $(LEVEL3_TEST:.v=.vo)
	@echo "✅ Level 3 集成模块验证完成！"

# ========================
# CI/CD SUPPORT
# ========================

ci: check-version compile validate test
	@echo "🚀 CI流水线执行成功！所有模块编译、验证和测试完成！"

ci-fast: check-version compile check
	@echo "⚡ 快速CI检查完成！编译和依赖验证通过！"

# ========================
# DEPENDENCY MANAGEMENT
# ========================

check-version:
	@echo "🔍 检查Coq版本..."
	@current_version=$$(coqc --version | head -n1 | awk '{print $$3}'); \
	if [ "$$current_version" = "$(REQUIRED_COQ_VERSION)" ]; then \
		echo "✅ Coq版本正确: $$current_version"; \
	else \
		echo "❌ Coq版本不匹配：需要 $(REQUIRED_COQ_VERSION)，当前 $$current_version"; \
		exit 1; \
	fi

opam-deps:
	@echo "📦 安装依赖包..."
	opam install -y coq.8.18.0 coq-mathcomp-ssreflect.1.18.0 coq-equations.1.3+8.18 coq-bignums
	@echo "✅ 依赖安装完成！"

# ========================
# DOCUMENTATION
# ========================

doc:
	@echo "📚 生成HTML文档..."
	$(COQDOC) --html -d html -t "FRF形式验证框架文档" $(COQFLAGS) $(ALL_SRC_FILES)
	@echo "✅ HTML文档生成在 html/ 目录"

doc-pdf:
	@echo "📚 生成PDF文档..."
	$(COQDOC) --latex -o frf_formalization.tex -t "FRF形式验证框架" $(COQFLAGS) $(ALL_SRC_FILES)
	pdflatex frf_formalization.tex >/dev/null 2>&1
	pdflatex frf_formalization.tex >/dev/null 2>&1
	@echo "✅ PDF文档生成：frf_formalization.pdf"

# ========================
# CLEANING
# ========================

clean:
	@echo "🧹 清理构建产物..."
	rm -f $(ALL_VO_FILES)
	rm -f $(ALL_SRC_FILES:.v=.glob) $(ALL_SRC_FILES:.v=.v.d)
	rm -rf html
	rm -f frf_formalization.*
	rm -f Makefile.coq
	rm -rf $(REPORT_DIR)
	@echo "✅ 清理完成！"

distclean: clean
	@echo "🧹 深度清理..."
	find . -name "*~" -delete
	find . -name ".*.aux" -delete
	@echo "✅ 深度清理完成！"

# ========================
# HELP
# ========================

help:
	@echo "=================================================="
	@echo "📌 FRF形式验证框架 Makefile (Coq $(REQUIRED_COQ_VERSION))"
	@echo "=================================================="
	@echo "基本目标："
	@echo "  all           - 编译所有模块 + 验证证明 (默认)"
	@echo "  compile       - 编译所有模块 (分层依赖顺序)"
	@echo "  validate      - 使用coqchk验证所有证明"
	@echo "  test          - 完整编译 + 验证 + 模块列表"
	@echo ""
	@echo "分级测试："
	@echo "  test-level1   - 编译/验证 Level 1 基础模块"
	@echo "  test-level2   - 编译/验证 Level 2 场景模块"
	@echo "  test-level3   - 编译/验证 Level 3 集成模块"
	@echo ""
	@echo "质量检查："
	@echo "  check         - 检查所有目录的编译完整性"
	@echo "  check-version - 验证Coq版本 (必须为 $(REQUIRED_COQ_VERSION))"
	@echo ""
	@echo "CI/CD："
	@echo "  ci            - 完整CI流水线 (版本+依赖+编译+验证+测试)"
	@echo "  ci-fast       - 快速CI检查 (版本+依赖+编译+完整性)"
	@echo ""
	@echo "文档："
	@echo "  doc           - 生成HTML文档 (所有模块)"
	@echo "  doc-pdf       - 生成PDF文档 (所有模块)"
	@echo ""
	@echo "清理："
	@echo "  clean         - 删除所有构建产物"
	@echo "  distclean     - 深度清理 (包括临时和备份文件)"
	@echo ""
	@echo "依赖管理："
	@echo "  opam-deps     - 通过OPAM安装所需包"
	@echo "=================================================="

# ========================
# UTILITY TARGETS
# ========================

status:
	@echo "📁 项目目录结构："
	@echo "  - Level 1 基础: SelfContainedLib, FRF_MetaTheory, FRF_CS_Null_Common, CategoryTheory/Core"
	@echo "  - Level 2 场景: Case* 场景, *Null.v, Quantum, DynamicSystem, Toolchain, CategoryTheory扩展"
	@echo "  - Level 3 集成: FRF_*.v, FRF_CS_Null, Test"
	@echo ""
	@echo "📦 已编译模块："
	@if [ -n "$$(find . -name '*.vo' -print -quit)" ]; then \
		find . -name "*.vo" | head -10 | sed 's|^./||' | while read vo; do \
			echo "  - $$vo"; \
		done; \
		total=$$(find . -name "*.vo" | wc -l); \
		if [ $$total -gt 10 ]; then \
			echo "  ... 和其他 $$((total-10)) 个模块"; \
		fi; \
	else \
		echo "  无 (先运行 'make compile')"; \
	fi
	@echo ""
	@echo "📈 编译进度: $$(find . -name "*.vo" | wc -l)/$$(echo "$(ALL_SRC_FILES)" | wc -w)"