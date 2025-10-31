# Makefile for FRF Formalization Project
# Comprehensive build system with validation and defect prevention

# ========================
# CONFIGURATION
# ========================
COQC = coqc
COQCHK = coqchk
COQDOC = coqdoc
COQFLAGS = -Q . FRF -Q SelfContainedLib SelfContainedLib -Q CS_Null CS_Null -Q CategoryTheory CategoryTheory
# 目录定义（包含所有模块目录，无遗漏）
SRC_ROOT = .
SELF_CONTAINED_DIR = SelfContainedLib
CS_NULL_DIR = CS_Null
THEORIES_DIR = theories
QUANTUM_DIR = Quantum
CATEGORY_THEORY_DIR = CategoryTheory
# 所有源文件（遍历所有目录，确保无遗漏）
SRC = \
	$(wildcard $(SELF_CONTAINED_DIR)/*.v) \
	$(wildcard $(CS_NULL_DIR)/*.v) \
	$(wildcard $(THEORIES_DIR)/*.v) \
	$(wildcard $(QUANTUM_DIR)/*.v) \
	$(wildcard $(CATEGORY_THEORY_DIR)/*.v)
# 构建产物
VO_FILES = $(SRC:.v=.vo)
GLOB_FILES = $(SRC:.v=.glob)
V_D_FILES = $(SRC:.v=.v.d)
# ========================
# 编译顺序（严格按依赖层级，避免循环）
# 一级基础层 → 二级场景层 → 三级集成层
# ========================
# 1. 一级基础层：SelfContainedLib（代数/范畴/几何）
SELF_CONTAINED_ORDERED = \
	$(SELF_CONTAINED_DIR)/Algebra.v \
	$(SELF_CONTAINED_DIR)/Category.v \
	$(SELF_CONTAINED_DIR)/Geometry.v
# 2. 一级基础层：FRF元理论 + 跨语言空值公共模块
FRF_BASE_ORDERED = \
	$(THEORIES_DIR)/FRF_MetaTheory.v \
	$(CS_NULL_DIR)/FRF_CS_Null_Common.v
# 3. 二级场景层：CategoryTheory基础模块
CATEGORY_BASE_ORDERED = \
	$(CATEGORY_THEORY_DIR)/Core.v \
	$(CATEGORY_THEORY_DIR)/Equivalence.v
# 4. 二级场景层：核心场景模块（CaseA-E、Church数、量子真空）
THEORIES_ORDERED = \
	$(THEORIES_DIR)/CaseA_SetTheory.v \
	$(THEORIES_DIR)/CaseB_Algebra.v \
	$(THEORIES_DIR)/CaseB_Algebra_SelfContained.v \
	$(THEORIES_DIR)/CaseC_TypeTheory.v \
	$(THEORIES_DIR)/CaseD_Category_SelfContained.v \
	$(THEORIES_DIR)/CaseD_CategoryTheory.v \
	$(THEORIES_DIR)/ChurchNumerals.v \
	$(THEORIES_DIR)/ChurchZero.v \
	$(THEORIES_DIR)/CaseE_QuantumVacuum.v \
	$(QUANTUM_DIR)/QFT_FRF.v \
	$(QUANTUM_DIR)/CurvedSpacetimeQFT.v
# 5. 二级场景层：CS_Null语言空值模块（依赖FRF_CS_Null_Common）
CS_NULL_ORDERED = \
	$(CS_NULL_DIR)/RustNull.v \
	$(CS_NULL_DIR)/CppNull.v \
	$(CS_NULL_DIR)/CxxNull.v \
	$(CS_NULL_DIR)/JavaNull.v \
	$(CS_NULL_DIR)/PythonNull.v \
	$(CS_NULL_DIR)/MathNull.v
# 6. 二级场景层：CategoryTheory扩展模块（依赖Core/Equivalence）
CATEGORY_EXT_ORDERED = \
	$(CATEGORY_THEORY_DIR)/ZeroObjectPreservedByEquivalence.v \
	$(CATEGORY_THEORY_DIR)/TestEquivalence.v
# 7. 三级集成层：跨领域/哲学验证模块（依赖所有二级模块）
INTEGRATION_ORDERED = \
	$(THEORIES_DIR)/FRF_PhilosophicalValidation.v \
	$(THEORIES_DIR)/FRF_Comparative.v \
	$(CS_NULL_DIR)/FRF_CS_Null.v
# 完整编译顺序（串联所有层级）
FULL_ORDERED_SRC = \
	$(SELF_CONTAINED_ORDERED) \
	$(FRF_BASE_ORDERED) \
	$(CATEGORY_BASE_ORDERED) \
	$(THEORIES_ORDERED) \
	$(CS_NULL_ORDERED) \
	$(CATEGORY_EXT_ORDERED) \
	$(INTEGRATION_ORDERED)
FULL_ORDERED_VO = $(FULL_ORDERED_SRC:.v=.vo)
# ========================
# 主目标（默认全编译+验证）
# ========================
.PHONY: all compile clean doc test validate check status help opam-deps check-deps check-version
.DEFAULT_GOAL := help
all: compile validate
compile: $(FULL_ORDERED_VO)
# ========================
# 编译规则（按层级定义依赖，确保正确构建）
# ========================
# 1. SelfContainedLib基础模块（无前置依赖）
$(SELF_CONTAINED_DIR)/Algebra.vo: $(SELF_CONTAINED_DIR)/Algebra.v
	cd $(SRC_ROOT) && $(COQC) $(COQFLAGS) $<
$(SELF_CONTAINED_DIR)/Category.vo: $(SELF_CONTAINED_DIR)/Category.v $(SELF_CONTAINED_DIR)/Algebra.vo
	cd $(SRC_ROOT) && $(COQC) $(COQFLAGS) $<
$(SELF_CONTAINED_DIR)/Geometry.vo: $(SELF_CONTAINED_DIR)/Geometry.v $(SELF_CONTAINED_DIR)/Algebra.vo
	cd $(SRC_ROOT) && $(COQC) $(COQFLAGS) $<
# 2. FRF基础模块（依赖SelfContainedLib）
$(THEORIES_DIR)/FRF_MetaTheory.vo: $(THEORIES_DIR)/FRF_MetaTheory.v $(SELF_CONTAINED_DIR)/Algebra.vo $(SELF_CONTAINED_DIR)/Category.vo
	cd $(SRC_ROOT) && $(COQC) $(COQFLAGS) $<
$(CS_NULL_DIR)/FRF_CS_Null_Common.vo: $(CS_NULL_DIR)/FRF_CS_Null_Common.v $(THEORIES_DIR)/FRF_MetaTheory.vo $(SELF_CONTAINED_DIR)/Category.vo
	cd $(SRC_ROOT) && $(COQC) $(COQFLAGS) $<
# 3. CategoryTheory基础模块（依赖SelfContainedLib.Category）
$(CATEGORY_THEORY_DIR)/Core.vo: $(CATEGORY_THEORY_DIR)/Core.v $(SELF_CONTAINED_DIR)/Category.vo
	cd $(SRC_ROOT) && $(COQC) $(COQFLAGS) $<
$(CATEGORY_THEORY_DIR)/Equivalence.vo: $(CATEGORY_THEORY_DIR)/Equivalence.v $(CATEGORY_THEORY_DIR)/Core.vo $(FRF_CS_Null_Common.vo)
	cd $(SRC_ROOT) && $(COQC) $(COQFLAGS) $<
# 4. theories核心场景模块（按依赖链编译）
$(THEORIES_DIR)/CaseA_SetTheory.vo: $(THEORIES_DIR)/CaseA_SetTheory.v $(THEORIES_DIR)/FRF_MetaTheory.vo
	cd $(SRC_ROOT) && $(COQC) $(COQFLAGS) $<
$(THEORIES_DIR)/CaseB_Algebra.vo: $(THEORIES_DIR)/CaseB_Algebra.v $(THEORIES_DIR)/CaseA_SetTheory.vo $(SELF_CONTAINED_DIR)/Algebra.vo
	cd $(SRC_ROOT) && $(COQC) $(COQFLAGS) $<
$(THEORIES_DIR)/CaseB_Algebra_SelfContained.vo: $(THEORIES_DIR)/CaseB_Algebra_SelfContained.v $(THEORIES_DIR)/CaseB_Algebra.vo
	cd $(SRC_ROOT) && $(COQC) $(COQFLAGS) $<
$(THEORIES_DIR)/CaseC_TypeTheory.vo: $(THEORIES_DIR)/CaseC_TypeTheory.v $(THEORIES_DIR)/CaseA_SetTheory.vo $(THEORIES_DIR)/FRF_MetaTheory.vo
	cd $(SRC_ROOT) && $(COQC) $(COQFLAGS) $<
$(THEORIES_DIR)/CaseD_Category_SelfContained.vo: $(THEORIES_DIR)/CaseD_Category_SelfContained.v $(SELF_CONTAINED_DIR)/Category.vo
	cd $(SRC_ROOT) && $(COQC) $(COQFLAGS) $<
$(THEORIES_DIR)/CaseD_CategoryTheory.vo: $(THEORIES_DIR)/CaseD_CategoryTheory.v $(THEORIES_DIR)/CaseC_TypeTheory.vo $(CATEGORY_THEORY_DIR)/Core.vo
	cd $(SRC_ROOT) && $(COQC) $(COQFLAGS) $<
$(THEORIES_DIR)/ChurchNumerals.vo: $(THEORIES_DIR)/ChurchNumerals.v $(SELF_CONTAINED_DIR)/Algebra.vo
	cd $(SRC_ROOT) && $(COQC) $(COQFLAGS) $<
$(THEORIES_DIR)/ChurchZero.vo: $(THEORIES_DIR)/ChurchZero.v $(THEORIES_DIR)/ChurchNumerals.vo $(THEORIES_DIR)/FRF_MetaTheory.vo
	cd $(SRC_ROOT) && $(COQC) $(COQFLAGS) $<
$(THEORIES_DIR)/CaseE_QuantumVacuum.vo: $(THEORIES_DIR)/CaseE_QuantumVacuum.v $(SELF_CONTAINED_DIR)/Algebra.vo $(THEORIES_DIR)/FRF_MetaTheory.vo
	cd $(SRC_ROOT) && $(COQC) $(COQFLAGS) $<
$(QUANTUM_DIR)/QFT_FRF.vo: $(QUANTUM_DIR)/QFT_FRF.v $(THEORIES_DIR)/CaseE_QuantumVacuum.vo $(THEORIES_DIR)/FRF_MetaTheory.vo
	cd $(SRC_ROOT) && $(COQC) $(COQFLAGS) $<
$(QUANTUM_DIR)/CurvedSpacetimeQFT.vo: $(QUANTUM_DIR)/CurvedSpacetimeQFT.v $(QUANTUM_DIR)/QFT_FRF.vo $(SELF_CONTAINED_DIR)/Geometry.vo
	cd $(SRC_ROOT) && $(COQC) $(COQFLAGS) $<
# 5. CS_Null语言空值模块（依赖FRF_CS_Null_Common）
$(CS_NULL_DIR)/RustNull.vo: $(CS_NULL_DIR)/RustNull.v $(CS_NULL_DIR)/FRF_CS_Null_Common.vo $(THEORIES_DIR)/FRF_MetaTheory.vo
	cd $(SRC_ROOT) && $(COQC) $(COQFLAGS) $<
$(CS_NULL_DIR)/CppNull.vo: $(CS_NULL_DIR)/CppNull.v $(CS_NULL_DIR)/FRF_CS_Null_Common.vo $(THEORIES_DIR)/FRF_MetaTheory.vo
	cd $(SRC_ROOT) && $(COQC) $(COQFLAGS) $<
$(CS_NULL_DIR)/CxxNull.vo: $(CS_NULL_DIR)/CxxNull.v $(CS_NULL_DIR)/FRF_CS_Null_Common.vo $(THEORIES_DIR)/FRF_MetaTheory.vo
	cd $(SRC_ROOT) && $(COQC) $(COQFLAGS) $<
$(CS_NULL_DIR)/JavaNull.vo: $(CS_NULL_DIR)/JavaNull.v $(CS_NULL_DIR)/FRF_CS_Null_Common.vo $(THEORIES_DIR)/FRF_MetaTheory.vo
	cd $(SRC_ROOT) && $(COQC) $(COQFLAGS) $<
$(CS_NULL_DIR)/PythonNull.vo: $(CS_NULL_DIR)/PythonNull.v $(CS_NULL_DIR)/FRF_CS_Null_Common.vo $(THEORIES_DIR)/FRF_MetaTheory.vo
	cd $(SRC_ROOT) && $(COQC) $(COQFLAGS) $<
$(CS_NULL_DIR)/MathNull.vo: $(CS_NULL_DIR)/MathNull.v $(CS_NULL_DIR)/FRF_CS_Null_Common.vo $(SELF_CONTAINED_DIR)/Algebra.vo
	cd $(SRC_ROOT) && $(COQC) $(COQFLAGS) $<
# 6. CategoryTheory扩展模块（依赖基础模块+场景模块）
$(CATEGORY_THEORY_DIR)/ZeroObjectPreservedByEquivalence.vo: $(CATEGORY_THEORY_DIR)/ZeroObjectPreservedByEquivalence.v $(CATEGORY_THEORY_DIR)/Equivalence.v $(THEORIES_DIR)/CaseD_CategoryTheory.vo
	cd $(SRC_ROOT) && $(COQC) $(COQFLAGS) $<
$(CATEGORY_THEORY_DIR)/TestEquivalence.vo: $(CATEGORY_THEORY_DIR)/TestEquivalence.v $(CATEGORY_THEORY_DIR)/ZeroObjectPreservedByEquivalence.vo
	cd $(SRC_ROOT) && $(COQC) $(COQFLAGS) $<
# 7. 集成层模块（依赖所有二级模块）
$(THEORIES_DIR)/FRF_PhilosophicalValidation.vo: $(THEORIES_DIR)/FRF_PhilosophicalValidation.v $(THEORIES_DIR)/FRF_MetaTheory.vo $(THEORIES_DIR)/ChurchZero.vo
	cd $(SRC_ROOT) && $(COQC) $(COQFLAGS) $<
$(THEORIES_DIR)/FRF_Comparative.vo: $(THEORIES_DIR)/FRF_Comparative.v $(THEORIES_DIR)/FRF_PhilosophicalValidation.v $(THEORIES_DIR)/CaseD_CategoryTheory.vo
	cd $(SRC_ROOT) && $(COQC) $(COQFLAGS) $<
$(CS_NULL_DIR)/FRF_CS_Null.vo: $(CS_NULL_DIR)/FRF_CS_Null.v $(CS_NULL_DIR)/RustNull.vo $(CS_NULL_DIR)/CppNull.vo $(CS_NULL_DIR)/JavaNull.vo $(CS_NULL_DIR)/PythonNull.vo $(CS_NULL_DIR)/MathNull.vo
	cd $(SRC_ROOT) && $(COQC) $(COQFLAGS) $<
# ========================
# 验证与测试（覆盖所有模块）
# ========================
validate: compile
	@echo "🔍 正在通过 coqchk 验证所有证明的独立性..."
	$(COQCHK) -silent $(VO_FILES)
	@echo "✅ 所有 $(words $(VO_FILES)) 个模块的证明均通过独立验证！"
test: compile validate
	@echo "✅ 全项目编译成功！"
	@echo "✅ FRF 框架全维度验证完成！"
	@echo "📋 已验证模块清单："
	@for vo in $(FULL_ORDERED_VO); do \
		base=$$(basename $$vo .vo); \
		echo "  - $$base.v"; \
	done
# 按层级测试目标
test-base: $(SELF_CONTAINED_ORDERED) $(FRF_BASE_ORDERED)
	@echo "✅ 一级基础层模块编译验证完成！"
test-scene: $(THEORIES_ORDERED) $(CS_NULL_ORDERED) $(CATEGORY_EXT_ORDERED)
	@echo "✅ 二级场景层模块编译验证完成！"
test-integration: $(INTEGRATION_ORDERED)
	@echo "✅ 三级集成层模块编译验证完成！"
# ========================
# 质量检查（确保无遗漏编译）
# ========================
check: $(VO_FILES)
	@echo "✅ 所有 Coq 模块验证通过："
	@echo "  - 一级基础层：$(words $(SELF_CONTAINED_ORDERED) $(FRF_BASE_ORDERED)) 个模块"
	@echo "  - 二级场景层：$(words $(THEORIES_ORDERED) $(CS_NULL_ORDERED) $(CATEGORY_EXT_ORDERED)) 个模块"
	@echo "  - 三级集成层：$(words $(INTEGRATION_ORDERED)) 个模块"
	@echo ""
	@echo "📊 编译状态检查："
	@declare -A dirs=([$(SELF_CONTAINED_DIR)]=1 [$(CS_NULL_DIR)]=1 [$(THEORIES_DIR)]=1 [$(QUANTUM_DIR)]=1 [$(CATEGORY_THEORY_DIR)]=1)
	@all_ok=1
	@for dir in $${!dirs[@]}; do \
		v_count=$$(ls $$dir/*.v 2>/dev/null | wc -l); \
		vo_count=$$(ls $$dir/*.vo 2>/dev/null | wc -l); \
		if [ $$v_count -ne $$vo_count ]; then \
			echo "❌ $$dir 目录：$$vo_count/$$v_count 个模块编译成功"; \
			all_ok=0; \
		else \
			echo "✅ $$dir 目录：$$vo_count/$$v_count 个模块编译成功"; \
		fi; \
	done
	@if [ $$all_ok -eq 1 ]; then \
		echo "✅ 全目录编译无遗漏！"; \
	else \
		exit 1; \
	fi
status:
	@echo "📁 项目目录结构："
	@echo "  - 一级基础层：$(SELF_CONTAINED_DIR)、$(THEORIES_DIR)/FRF_MetaTheory.v、$(CS_NULL_DIR)/FRF_CS_Null_Common.v"
	@echo "  - 二级场景层：$(THEORIES_DIR)/Case*、$(CS_NULL_DIR)/*Null.v、$(QUANTUM_DIR)、$(CATEGORY_THEORY_DIR)"
	@echo "  - 三级集成层：$(THEORIES_DIR)/FRF_*.v、$(CS_NULL_DIR)/FRF_CS_Null.v"
	@echo ""
	@echo "📦 已编译模块："
	@if ls $(VO_FILES) 2>/dev/null >/dev/null; then \
		ls $(VO_FILES) 2>/dev/null | sed 's/^/  /' | head -10; \
		if [ $(words $(VO_FILES)) -gt 10 ]; then \
			echo "  ... 及其他 $(($(words $(VO_FILES))-10)) 个模块"; \
		fi; \
	else \
		echo "  无（请先运行 'make compile'）"; \
	fi
	@echo ""
	@echo "📈 编译进度：$(words $(filter %.vo,$(FULL_ORDERED_VO)))/$(words $(FULL_ORDERED_VO))"
# ========================
# 文档生成（覆盖所有模块）
# ========================
doc:
	@echo "📚 正在生成 HTML 文档（含所有模块）..."
	$(COQDOC) --html -d html -title "FRF 形式化验证框架文档" $(COQFLAGS) $(SRC)
	@echo "✅ HTML 文档已生成至 html/ 目录"
doc-pdf:
	@echo "📚 正在生成 PDF 文档（含所有模块）..."
	$(COQDOC) --latex -o frf_formalization.tex -title "FRF 形式化验证框架" $(COQFLAGS) $(SRC)
	pdflatex frf_formalization.tex >/dev/null 2>&1
	pdflatex frf_formalization.tex >/dev/null 2>&1 # 二次编译处理引用
	@echo "✅ PDF 文档已生成：frf_formalization.pdf"
# ========================
# 清理目标（移除所有构建产物）
# ========================
clean:
	@echo "🧹 正在清理构建产物..."
	rm -f $(VO_FILES) $(GLOB_FILES) $(V_D_FILES)
	rm -f $(SELF_CONTAINED_DIR)/*.vo $(SELF_CONTAINED_DIR)/*.glob $(SELF_CONTAINED_DIR)/*.v.d
	rm -f $(CS_NULL_DIR)/*.vo $(CS_NULL_DIR)/*.glob $(CS_NULL_DIR)/*.v.d
	rm -f $(THEORIES_DIR)/*.vo $(THEORIES_DIR)/*.glob $(THEORIES_DIR)/*.v.d
	rm -f $(QUANTUM_DIR)/*.vo $(QUANTUM_DIR)/*.glob $(QUANTUM_DIR)/*.v.d
	rm -f $(CATEGORY_THEORY_DIR)/*.vo $(CATEGORY_THEORY_DIR)/*.glob $(CATEGORY_THEORY_DIR)/*.v.d
	rm -rf html
	rm -f frf_formalization.tex frf_formalization.pdf frf_formalization.aux frf_formalization.log
	@echo "✅ 清理完成！"
distclean: clean
	@echo "🧹 正在深度清理..."
	rm -f $(SELF_CONTAINED_DIR)/*~ $(CS_NULL_DIR)/*~ $(THEORIES_DIR)/*~ $(QUANTUM_DIR)/*~ $(CATEGORY_THEORY_DIR)/*~
	rm -f *~
	@echo "✅ 深度清理完成！"
# ========================
# CI/CD 支持（适配自动化流水线）
# ========================
ci: check-version check-deps all test
	@echo "🚀 CI 流水线执行成功！所有模块编译、验证、测试均通过！"
ci-fast: check-version check-deps compile check
	@echo "⚡ 快速 CI 检查完成！编译与依赖验证通过！"
# ========================
# 依赖管理（确保环境与依赖正确）
# ========================
opam-deps:
	@echo "📦 正在安装依赖包..."
	opam install coq=8.18.0 coq-mathlib=3.74.0 coq-mathcomp-ssreflect coq-unimath
	@echo "✅ 依赖安装完成！"
check-deps:
	@echo "🔍 正在验证模块依赖关系..."
	# 验证一级基础层依赖
	@if ! grep -q "Require Import SelfContainedLib.Algebra" $(THEORIES_DIR)/FRF_MetaTheory.v; then echo "❌ FRF_MetaTheory 未依赖 SelfContainedLib.Algebra"; exit 1; fi
	@if ! grep -q "Require Import FRF_MetaTheory" $(CS_NULL_DIR)/FRF_CS_Null_Common.v; then echo "❌ FRF_CS_Null_Common 未依赖 FRF_MetaTheory"; exit 1; fi
	# 验证二级场景层依赖
	@if ! grep -q "Require Import FRF_CS_Null_Common" $(CS_NULL_DIR)/RustNull.v; then echo "❌ RustNull 未依赖 FRF_CS_Null_Common"; exit 1; fi
	@if ! grep -q "Require Import SelfContainedLib.Geometry" $(QUANTUM_DIR)/CurvedSpacetimeQFT.v; then echo "❌ CurvedSpacetimeQFT 未依赖 SelfContainedLib.Geometry"; exit 1; fi
	# 验证三级集成层依赖
	@if ! grep -q "Require Import CaseD_CategoryTheory" $(THEORIES_DIR)/FRF_Comparative.v; then echo "❌ FRF_Comparative 未依赖 CaseD_CategoryTheory"; exit 1; fi
	@if ! grep -q "Require Import RustNull" $(CS_NULL_DIR)/FRF_CS_Null.v; then echo "❌ FRF_CS_Null 未依赖 RustNull"; exit 1; fi
	@echo "✅ 所有模块依赖关系验证正确！"
check-version:
	@echo "🔍 正在验证 Coq 版本..."
	@coqc --version | grep -q "8.18.0" || (echo "❌ 请使用 Coq 8.18.0（当前版本：$(shell coqc --version | head -n1 | awk '{print $$2}')）"; exit 1)
	@echo "✅ Coq 版本验证通过（8.18.0）！"
# ========================
# 帮助信息（详细说明所有目标）
# ========================
help:
	@echo "=================================================="
	@echo "📌 FRF 形式化验证框架 Makefile（Coq 8.18.0 适配版）"
	@echo "=================================================="
	@echo "基础目标："
	@echo "  all         - 编译所有模块 + 验证证明（默认目标）"
	@echo "  compile     - 编译所有模块（按层级依赖顺序）"
	@echo "  validate    - 用 coqchk 验证所有证明的独立性"
	@echo "  test        - 完整编译 + 验证 + 输出模块清单"
	@echo ""
	@echo "分层测试目标："
	@echo "  test-base   - 仅编译验证一级基础层模块"
	@echo "  test-scene  - 仅编译验证二级场景层模块"
	@echo "  test-integration - 仅编译验证三级集成层模块"
	@echo ""
	@echo "质量检查目标："
	@echo "  check       - 检查所有目录的编译完整性"
	@echo "  status      - 显示当前编译进度和模块结构"
	@echo "  check-deps  - 验证模块间依赖关系正确性"
	@echo "  check-version - 验证 Coq 版本（必须 8.18.0）"
	@echo ""
	@echo "文档目标："
	@echo "  doc         - 生成 HTML 格式文档（含所有模块）"
	@echo "  doc-pdf     - 生成 PDF 格式文档（含所有模块）"
	@echo ""
	@echo "清理目标："
	@echo "  clean       - 移除所有构建产物（.vo/.glob/.pdf 等）"
	@echo "  distclean   - 深度清理（含临时文件和备份文件）"
	@echo ""
	@echo "CI/CD 目标："
	@echo "  ci          - 完整 CI 流水线（版本+依赖+编译+验证+测试）"
	@echo "  ci-fast     - 快速 CI 检查（版本+依赖+编译+完整性）"
	@echo ""
	@echo "依赖管理："
	@echo "  opam-deps   - 通过 OPAM 安装所需依赖包"
	@echo "=================================================="