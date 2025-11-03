# Makefile for FRF Formalization Project
# Comprehensive build system with validation and defect prevention
# FIXED: Complete logical path mapping aligned with CoqProject

# ========================
# CONFIGURATION
# ========================
COQC = coqc
COQCHK = coqchk
COQDOC = coqdoc

# FIXED: Complete logical path mapping aligned with CoqProject
COQFLAGS = -Q . FRF \
           -Q SelfContainedLib SelfContainedLib \
           -Q theories FRF.Theories \
           -Q CS_Null FRF.CS_Null \
           -Q Quantum FRF.Quantum \
           -Q DynamicSystem FRF.DynamicSystem \
           -Q Toolchain FRF.Toolchain \
           -Q Test FRF.Test \
           -Q CategoryTheory CategoryTheory

# FIXED: Complete directory definitions
SRC_ROOT = .
SELF_CONTAINED_DIR = SelfContainedLib
THEORIES_DIR = theories
CS_NULL_DIR = CS_Null
QUANTUM_DIR = Quantum
DYNAMIC_SYSTEM_DIR = DynamicSystem
TOOLCHAIN_DIR = Toolchain
TEST_DIR = Test
CATEGORY_THEORY_DIR = CategoryTheory

# FIXED: Complete source file scanning
SRC = \
	$(wildcard $(SELF_CONTAINED_DIR)/*.v) \
	$(wildcard $(THEORIES_DIR)/*.v) \
	$(wildcard $(CS_NULL_DIR)/*.v) \
	$(wildcard $(QUANTUM_DIR)/*.v) \
	$(wildcard $(DYNAMIC_SYSTEM_DIR)/*.v) \
	$(wildcard $(DYNAMIC_SYSTEM_DIR)/Utils/*.v) \
	$(wildcard $(TOOLCHAIN_DIR)/*.v) \
	$(wildcard $(TEST_DIR)/*.v) \
	$(wildcard $(CATEGORY_THEORY_DIR)/*.v)

# Build artifacts
VO_FILES = $(SRC:.v=.vo)
GLOB_FILES = $(SRC:.v=.glob)
V_D_FILES = $(SRC:.v=.v.d)

# ========================
# COMPILATION ORDER (strict dependency hierarchy)
# ========================
# 1. Level 1: SelfContainedLib (Algebra/Category/Geometry)
SELF_CONTAINED_ORDERED = \
	$(SELF_CONTAINED_DIR)/Algebra.v \
	$(SELF_CONTAINED_DIR)/Category.v \
	$(SELF_CONTAINED_DIR)/Geometry.v

# 2. Level 1: FRF MetaTheory + Cross-language null common modules
FRF_BASE_ORDERED = \
	$(THEORIES_DIR)/FRF_MetaTheory.v \
	$(CS_NULL_DIR)/FRF_CS_Null_Common.v

# 3. Level 1: CategoryTheory base modules
CATEGORY_BASE_ORDERED = \
	$(CATEGORY_THEORY_DIR)/Core.v \
	$(CATEGORY_THEORY_DIR)/Equivalence.v

# 4. Level 2: Core scenario modules (CaseA-E, Church numerals, quantum vacuum)
THEORIES_ORDERED = \
	$(THEORIES_DIR)/CaseA_SetTheory.v \
	$(THEORIES_DIR)/ChurchNumerals.v \
	$(THEORIES_DIR)/ChurchZero.v \
	$(THEORIES_DIR)/CaseB_Algebra.v \
	$(THEORIES_DIR)/CaseB_Algebra_SelfContained.v \
	$(THEORIES_DIR)/CaseC_TypeTheory.v \
	$(THEORIES_DIR)/CaseD_CategoryTheory.v \
	$(THEORIES_DIR)/CaseD_Category_SelfContained.v \
	$(THEORIES_DIR)/CaseF_Logic.v

# 5. Level 2: Quantum modules
QUANTUM_ORDERED = \
	$(QUANTUM_DIR)/QFT_FRF.v \
	$(QUANTUM_DIR)/CaseE_QuantumVacuum.v \
	$(QUANTUM_DIR)/CurvedSpacetimeQFT.v

# 6. Level 2: CS_Null language null modules (depends on FRF_CS_Null_Common)
CS_NULL_ORDERED = \
	$(CS_NULL_DIR)/RustNull.v \
	$(CS_NULL_DIR)/CxxNull.v \
	$(CS_NULL_DIR)/JavaNull.v \
	$(CS_NULL_DIR)/PythonNull.v \
	$(CS_NULL_DIR)/MathNull.v

# 7. Level 2: DynamicSystem modules
DYNAMIC_SYSTEM_ORDERED = \
	$(DYNAMIC_SYSTEM_DIR)/Utils/Serialization.v \
	$(DYNAMIC_SYSTEM_DIR)/TimeVaryingSystem.v \
	$(DYNAMIC_SYSTEM_DIR)/DistributedSystem.v \
	$(DYNAMIC_SYSTEM_DIR)/BlockchainSystem.v \
	$(DYNAMIC_SYSTEM_DIR)/ControlSystem.v

# 8. Level 2: Toolchain modules
TOOLCHAIN_ORDERED = \
	$(TOOLCHAIN_DIR)/FRF_to_Agda.v \
	$(TOOLCHAIN_DIR)/FRF_to_Isabelle.v \
	$(TOOLCHAIN_DIR)/FRF_to_Lean.v

# 9. Level 2: CategoryTheory extension modules
CATEGORY_EXT_ORDERED = \
	$(CATEGORY_THEORY_DIR)/ZeroObjectPreservedByEquivalence.v \
	$(CATEGORY_THEORY_DIR)/TestEquivalence.v

# 10. Level 3: Integration modules (depends on all Level 2 modules)
INTEGRATION_ORDERED = \
	$(CS_NULL_DIR)/FRF_CS_Null.v \
	$(THEORIES_DIR)/FRF_PhilosophicalValidation.v \
	$(THEORIES_DIR)/FRF_Comparative.v

# 11. Level 3: Test modules (depends on all business modules)
TEST_ORDERED = \
	$(TEST_DIR)/Test_FRF_MetaTheory.v \
	$(TEST_DIR)/Test_QuantumVacuum.v \
	$(TEST_DIR)/Test_BlockchainSystem.v

# Complete compilation order
FULL_ORDERED_SRC = \
	$(SELF_CONTAINED_ORDERED) \
	$(FRF_BASE_ORDERED) \
	$(CATEGORY_BASE_ORDERED) \
	$(THEORIES_ORDERED) \
	$(QUANTUM_ORDERED) \
	$(CS_NULL_ORDERED) \
	$(DYNAMIC_SYSTEM_ORDERED) \
	$(TOOLCHAIN_ORDERED) \
	$(CATEGORY_EXT_ORDERED) \
	$(INTEGRATION_ORDERED) \
	$(TEST_ORDERED)

FULL_ORDERED_VO = $(FULL_ORDERED_SRC:.v=.vo)

# ========================
# MAIN TARGETS
# ========================
.PHONY: all compile clean doc test validate check status help opam-deps check-deps check-version
.DEFAULT_GOAL := help

all: compile validate

compile: $(FULL_ORDERED_VO)

# ========================
# COMPILATION RULES (dependency hierarchy)
# ========================
# Level 1: SelfContainedLib (no dependencies)
$(SELF_CONTAINED_DIR)/Algebra.vo: $(SELF_CONTAINED_DIR)/Algebra.v
	cd $(SRC_ROOT) && $(COQC) $(COQFLAGS) $<

$(SELF_CONTAINED_DIR)/Category.vo: $(SELF_CONTAINED_DIR)/Category.v
	cd $(SRC_ROOT) && $(COQC) $(COQFLAGS) $<

$(SELF_CONTAINED_DIR)/Geometry.vo: $(SELF_CONTAINED_DIR)/Geometry.v
	cd $(SRC_ROOT) && $(COQC) $(COQFLAGS) $<

# Level 1: FRF base modules (depends on SelfContainedLib)
$(THEORIES_DIR)/FRF_MetaTheory.vo: $(THEORIES_DIR)/FRF_MetaTheory.v $(SELF_CONTAINED_DIR)/Algebra.vo $(SELF_CONTAINED_DIR)/Category.vo
	cd $(SRC_ROOT) && $(COQC) $(COQFLAGS) $<

$(CS_NULL_DIR)/FRF_CS_Null_Common.vo: $(CS_NULL_DIR)/FRF_CS_Null_Common.v $(THEORIES_DIR)/FRF_MetaTheory.vo
	cd $(SRC_ROOT) && $(COQC) $(COQFLAGS) $<

# Level 1: CategoryTheory base (depends on SelfContainedLib.Category)
$(CATEGORY_THEORY_DIR)/Core.vo: $(CATEGORY_THEORY_DIR)/Core.v $(SELF_CONTAINED_DIR)/Category.vo
	cd $(SRC_ROOT) && $(COQC) $(COQFLAGS) $<

$(CATEGORY_THEORY_DIR)/Equivalence.vo: $(CATEGORY_THEORY_DIR)/Equivalence.v $(CATEGORY_THEORY_DIR)/Core.vo
	cd $(SRC_ROOT) && $(COQC) $(COQFLAGS) $<

# Level 2: Core theories (depends on FRF base)
$(THEORIES_DIR)/CaseA_SetTheory.vo: $(THEORIES_DIR)/CaseA_SetTheory.v $(THEORIES_DIR)/FRF_MetaTheory.vo
	cd $(SRC_ROOT) && $(COQC) $(COQFLAGS) $<

$(THEORIES_DIR)/ChurchNumerals.vo: $(THEORIES_DIR)/ChurchNumerals.v $(SELF_CONTAINED_DIR)/Algebra.vo
	cd $(SRC_ROOT) && $(COQC) $(COQFLAGS) $<

$(THEORIES_DIR)/ChurchZero.vo: $(THEORIES_DIR)/ChurchZero.v $(THEORIES_DIR)/ChurchNumerals.vo $(THEORIES_DIR)/FRF_MetaTheory.vo
	cd $(SRC_ROOT) && $(COQC) $(COQFLAGS) $<

$(THEORIES_DIR)/CaseB_Algebra.vo: $(THEORIES_DIR)/CaseB_Algebra.v $(THEORIES_DIR)/CaseA_SetTheory.vo $(SELF_CONTAINED_DIR)/Algebra.vo
	cd $(SRC_ROOT) && $(COQC) $(COQFLAGS) $<

$(THEORIES_DIR)/CaseB_Algebra_SelfContained.vo: $(THEORIES_DIR)/CaseB_Algebra_SelfContained.v $(THEORIES_DIR)/CaseB_Algebra.vo
	cd $(SRC_ROOT) && $(COQC) $(COQFLAGS) $<

$(THEORIES_DIR)/CaseC_TypeTheory.vo: $(THEORIES_DIR)/CaseC_TypeTheory.v $(THEORIES_DIR)/CaseA_SetTheory.vo $(THEORIES_DIR)/FRF_MetaTheory.vo
	cd $(SRC_ROOT) && $(COQC) $(COQFLAGS) $<

$(THEORIES_DIR)/CaseD_CategoryTheory.vo: $(THEORIES_DIR)/CaseD_CategoryTheory.v $(THEORIES_DIR)/CaseC_TypeTheory.vo $(CATEGORY_THEORY_DIR)/Core.vo
	cd $(SRC_ROOT) && $(COQC) $(COQFLAGS) $<

$(THEORIES_DIR)/CaseD_Category_SelfContained.vo: $(THEORIES_DIR)/CaseD_Category_SelfContained.v $(SELF_CONTAINED_DIR)/Category.vo
	cd $(SRC_ROOT) && $(COQC) $(COQFLAGS) $<

$(THEORIES_DIR)/CaseF_Logic.vo: $(THEORIES_DIR)/CaseF_Logic.v $(THEORIES_DIR)/FRF_MetaTheory.vo
	cd $(SRC_ROOT) && $(COQC) $(COQFLAGS) $<

# Level 2: Quantum modules
$(QUANTUM_DIR)/QFT_FRF.vo: $(QUANTUM_DIR)/QFT_FRF.v $(SELF_CONTAINED_DIR)/Algebra.vo
	cd $(SRC_ROOT) && $(COQC) $(COQFLAGS) $<

$(QUANTUM_DIR)/CaseE_QuantumVacuum.vo: $(QUANTUM_DIR)/CaseE_QuantumVacuum.v $(QUANTUM_DIR)/QFT_FRF.vo $(THEORIES_DIR)/FRF_MetaTheory.vo
	cd $(SRC_ROOT) && $(COQC) $(COQFLAGS) $<

$(QUANTUM_DIR)/CurvedSpacetimeQFT.vo: $(QUANTUM_DIR)/CurvedSpacetimeQFT.v $(QUANTUM_DIR)/QFT_FRF.vo $(SELF_CONTAINED_DIR)/Geometry.vo
	cd $(SRC_ROOT) && $(COQC) $(COQFLAGS) $<

# Level 2: CS_Null modules (depends on FRF_CS_Null_Common)
$(CS_NULL_DIR)/RustNull.vo: $(CS_NULL_DIR)/RustNull.v $(CS_NULL_DIR)/FRF_CS_Null_Common.vo
	cd $(SRC_ROOT) && $(COQC) $(COQFLAGS) $<

$(CS_NULL_DIR)/CxxNull.vo: $(CS_NULL_DIR)/CxxNull.v $(CS_NULL_DIR)/FRF_CS_Null_Common.vo
	cd $(SRC_ROOT) && $(COQC) $(COQFLAGS) $<

$(CS_NULL_DIR)/JavaNull.vo: $(CS_NULL_DIR)/JavaNull.v $(CS_NULL_DIR)/FRF_CS_Null_Common.vo
	cd $(SRC_ROOT) && $(COQC) $(COQFLAGS) $<

$(CS_NULL_DIR)/PythonNull.vo: $(CS_NULL_DIR)/PythonNull.v $(CS_NULL_DIR)/FRF_CS_Null_Common.vo
	cd $(SRC_ROOT) && $(COQC) $(COQFLAGS) $<

$(CS_NULL_DIR)/MathNull.vo: $(CS_NULL_DIR)/MathNull.v $(CS_NULL_DIR)/FRF_CS_Null_Common.vo $(SELF_CONTAINED_DIR)/Algebra.vo
	cd $(SRC_ROOT) && $(COQC) $(COQFLAGS) $<

# Level 2: DynamicSystem modules
$(DYNAMIC_SYSTEM_DIR)/Utils/Serialization.vo: $(DYNAMIC_SYSTEM_DIR)/Utils/Serialization.v
	cd $(SRC_ROOT) && $(COQC) $(COQFLAGS) $<

$(DYNAMIC_SYSTEM_DIR)/TimeVaryingSystem.vo: $(DYNAMIC_SYSTEM_DIR)/TimeVaryingSystem.v $(THEORIES_DIR)/FRF_MetaTheory.vo
	cd $(SRC_ROOT) && $(COQC) $(COQFLAGS) $<

$(DYNAMIC_SYSTEM_DIR)/DistributedSystem.vo: $(DYNAMIC_SYSTEM_DIR)/DistributedSystem.v $(DYNAMIC_SYSTEM_DIR)/TimeVaryingSystem.vo
	cd $(SRC_ROOT) && $(COQC) $(COQFLAGS) $<

$(DYNAMIC_SYSTEM_DIR)/BlockchainSystem.vo: $(DYNAMIC_SYSTEM_DIR)/BlockchainSystem.v $(DYNAMIC_SYSTEM_DIR)/Utils/Serialization.vo $(DYNAMIC_SYSTEM_DIR)/TimeVaryingSystem.vo
	cd $(SRC_ROOT) && $(COQC) $(COQFLAGS) $<

$(DYNAMIC_SYSTEM_DIR)/ControlSystem.vo: $(DYNAMIC_SYSTEM_DIR)/ControlSystem.v $(DYNAMIC_SYSTEM_DIR)/TimeVaryingSystem.vo
	cd $(SRC_ROOT) && $(COQC) $(COQFLAGS) $<

# Level 2: Toolchain modules
$(TOOLCHAIN_DIR)/FRF_to_Agda.vo: $(TOOLCHAIN_DIR)/FRF_to_Agda.v
	cd $(SRC_ROOT) && $(COQC) $(COQFLAGS) $<

$(TOOLCHAIN_DIR)/FRF_to_Isabelle.vo: $(TOOLCHAIN_DIR)/FRF_to_Isabelle.v
	cd $(SRC_ROOT) && $(COQC) $(COQFLAGS) $<

$(TOOLCHAIN_DIR)/FRF_to_Lean.vo: $(TOOLCHAIN_DIR)/FRF_to_Lean.v
	cd $(SRC_ROOT) && $(COQC) $(COQFLAGS) $<

# Level 2: CategoryTheory extensions
$(CATEGORY_THEORY_DIR)/ZeroObjectPreservedByEquivalence.vo: $(CATEGORY_THEORY_DIR)/ZeroObjectPreservedByEquivalence.v $(CATEGORY_THEORY_DIR)/Equivalence.vo $(THEORIES_DIR)/CaseD_CategoryTheory.vo
	cd $(SRC_ROOT) && $(COQC) $(COQFLAGS) $<

$(CATEGORY_THEORY_DIR)/TestEquivalence.vo: $(CATEGORY_THEORY_DIR)/TestEquivalence.v $(CATEGORY_THEORY_DIR)/ZeroObjectPreservedByEquivalence.vo
	cd $(SRC_ROOT) && $(COQC) $(COQFLAGS) $<

# Level 3: Integration modules
$(CS_NULL_DIR)/FRF_CS_Null.vo: $(CS_NULL_DIR)/FRF_CS_Null.v $(CS_NULL_DIR)/RustNull.vo $(CS_NULL_DIR)/CxxNull.vo $(CS_NULL_DIR)/JavaNull.vo $(CS_NULL_DIR)/PythonNull.vo $(CS_NULL_DIR)/MathNull.vo
	cd $(SRC_ROOT) && $(COQC) $(COQFLAGS) $<

$(THEORIES_DIR)/FRF_PhilosophicalValidation.vo: $(THEORIES_DIR)/FRF_PhilosophicalValidation.v $(THEORIES_DIR)/FRF_MetaTheory.vo $(THEORIES_DIR)/ChurchZero.vo
	cd $(SRC_ROOT) && $(COQC) $(COQFLAGS) $<

$(THEORIES_DIR)/FRF_Comparative.vo: $(THEORIES_DIR)/FRF_Comparative.v $(THEORIES_DIR)/FRF_PhilosophicalValidation.vo $(THEORIES_DIR)/CaseD_CategoryTheory.vo
	cd $(SRC_ROOT) && $(COQC) $(COQFLAGS) $<

# Level 3: Test modules
$(TEST_DIR)/Test_FRF_MetaTheory.vo: $(TEST_DIR)/Test_FRF_MetaTheory.v
	cd $(SRC_ROOT) && $(COQC) $(COQFLAGS) $<

$(TEST_DIR)/Test_QuantumVacuum.vo: $(TEST_DIR)/Test_QuantumVacuum.v
	cd $(SRC_ROOT) && $(COQC) $(COQFLAGS) $<

$(TEST_DIR)/Test_BlockchainSystem.vo: $(TEST_DIR)/Test_BlockchainSystem.v
	cd $(SRC_ROOT) && $(COQC) $(COQFLAGS) $<

# ========================
# VALIDATION & TESTING
# ========================
validate: compile
	@echo "🔍 Validating all proofs with coqchk..."
	$(COQCHK) -silent $(VO_FILES)
	@echo "✅ All $(words $(VO_FILES)) modules passed independent validation!"

test: compile validate
	@echo "✅ Full project compilation successful!"
	@echo "✅ FRF framework full-dimensional validation completed!"
	@echo "📋 Verified module list:"
	@for vo in $(FULL_ORDERED_VO); do \
		base=$$(basename $$vo .vo); \
		echo "  - $$base.v"; \
	done

# Level-based testing targets
test-base: $(SELF_CONTAINED_ORDERED) $(FRF_BASE_ORDERED)
	@echo "✅ Level 1 base modules compilation verified!"

test-scene: $(THEORIES_ORDERED) $(QUANTUM_ORDERED) $(CS_NULL_ORDERED) $(DYNAMIC_SYSTEM_ORDERED) $(TOOLCHAIN_ORDERED) $(CATEGORY_EXT_ORDERED)
	@echo "✅ Level 2 scene modules compilation verified!"

test-integration: $(INTEGRATION_ORDERED) $(TEST_ORDERED)
	@echo "✅ Level 3 integration modules compilation verified!"

# ========================
# QUALITY CHECKS
# ========================
check: $(VO_FILES)
	@echo "✅ All Coq modules verified:"
	@echo "  - Level 1 Base: $(words $(SELF_CONTAINED_ORDERED) $(FRF_BASE_ORDERED) $(CATEGORY_BASE_ORDERED)) modules"
	@echo "  - Level 2 Scene: $(words $(THEORIES_ORDERED) $(QUANTUM_ORDERED) $(CS_NULL_ORDERED) $(DYNAMIC_SYSTEM_ORDERED) $(TOOLCHAIN_ORDERED) $(CATEGORY_EXT_ORDERED)) modules"
	@echo "  - Level 3 Integration: $(words $(INTEGRATION_ORDERED) $(TEST_ORDERED)) modules"
	@echo ""
	@echo "📊 Compilation status check:"
	@declare -A dirs=([$(SELF_CONTAINED_DIR)]=1 [$(THEORIES_DIR)]=1 [$(CS_NULL_DIR)]=1 [$(QUANTUM_DIR)]=1 [$(DYNAMIC_SYSTEM_DIR)]=1 [$(TOOLCHAIN_DIR)]=1 [$(TEST_DIR)]=1 [$(CATEGORY_THEORY_DIR)]=1)
	@all_ok=1
	@for dir in $${!dirs[@]}; do \
		v_count=$$(find $$dir -name "*.v" 2>/dev/null | wc -l); \
		vo_count=$$(find $$dir -name "*.vo" 2>/dev/null | wc -l); \
		if [ $$v_count -ne $$vo_count ]; then \
			echo "❌ $$dir directory: $$vo_count/$$v_count modules compiled"; \
			all_ok=0; \
		else \
			echo "✅ $$dir directory: $$vo_count/$$v_count modules compiled"; \
		fi; \
	done
	@if [ $$all_ok -eq 1 ]; then \
		echo "✅ All directories compiled without omissions!"; \
	else \
		exit 1; \
	fi

status:
	@echo "📁 Project directory structure:"
	@echo "  - Level 1 Base: $(SELF_CONTAINED_DIR), $(THEORIES_DIR)/FRF_MetaTheory.v, $(CS_NULL_DIR)/FRF_CS_Null_Common.v, $(CATEGORY_THEORY_DIR)/Core"
	@echo "  - Level 2 Scene: $(THEORIES_DIR)/Case*, $(CS_NULL_DIR)/*Null.v, $(QUANTUM_DIR), $(DYNAMIC_SYSTEM_DIR), $(TOOLCHAIN_DIR), $(CATEGORY_THEORY_DIR)/Extensions"
	@echo "  - Level 3 Integration: $(THEORIES_DIR)/FRF_*.v, $(CS_NULL_DIR)/FRF_CS_Null.v, $(TEST_DIR)"
	@echo ""
	@echo "📦 Compiled modules:"
	@if ls $(VO_FILES) 2>/dev/null >/dev/null; then \
		ls $(VO_FILES) 2>/dev/null | sed 's/^/  /' | head -10; \
		if [ $(words $(VO_FILES)) -gt 10 ]; then \
			echo "  ... and other $(($(words $(VO_FILES))-10)) modules"; \
		fi; \
	else \
		echo "  None (run 'make compile' first)"; \
	fi
	@echo ""
	@echo "📈 Compilation progress: $(words $(filter %.vo,$(FULL_ORDERED_VO)))/$(words $(FULL_ORDERED_VO))"

# ========================
# DOCUMENTATION
# ========================
doc:
	@echo "📚 Generating HTML documentation (all modules)..."
	$(COQDOC) --html -d html -title "FRF Formal Verification Framework Documentation" $(COQFLAGS) $(SRC)
	@echo "✅ HTML documentation generated in html/ directory"

doc-pdf:
	@echo "📚 Generating PDF documentation (all modules)..."
	$(COQDOC) --latex -o frf_formalization.tex -title "FRF Formal Verification Framework" $(COQFLAGS) $(SRC)
	pdflatex frf_formalization.tex >/dev/null 2>&1
	pdflatex frf_formalization.tex >/dev/null 2>&1 # Second pass for references
	@echo "✅ PDF documentation generated: frf_formalization.pdf"

# ========================
# CLEANING
# ========================
clean:
	@echo "🧹 Cleaning build artifacts..."
	rm -f $(VO_FILES) $(GLOB_FILES) $(V_D_FILES)
	rm -f $(SELF_CONTAINED_DIR)/*.vo $(SELF_CONTAINED_DIR)/*.glob $(SELF_CONTAINED_DIR)/*.v.d
	rm -f $(THEORIES_DIR)/*.vo $(THEORIES_DIR)/*.glob $(THEORIES_DIR)/*.v.d
	rm -f $(CS_NULL_DIR)/*.vo $(CS_NULL_DIR)/*.glob $(CS_NULL_DIR)/*.v.d
	rm -f $(QUANTUM_DIR)/*.vo $(QUANTUM_DIR)/*.glob $(QUANTUM_DIR)/*.v.d
	rm -f $(DYNAMIC_SYSTEM_DIR)/*.vo $(DYNAMIC_SYSTEM_DIR)/*.glob $(DYNAMIC_SYSTEM_DIR)/*.v.d
	rm -f $(DYNAMIC_SYSTEM_DIR)/Utils/*.vo $(DYNAMIC_SYSTEM_DIR)/Utils/*.glob $(DYNAMIC_SYSTEM_DIR)/Utils/*.v.d
	rm -f $(TOOLCHAIN_DIR)/*.vo $(TOOLCHAIN_DIR)/*.glob $(TOOLCHAIN_DIR)/*.v.d
	rm -f $(TEST_DIR)/*.vo $(TEST_DIR)/*.glob $(TEST_DIR)/*.v.d
	rm -f $(CATEGORY_THEORY_DIR)/*.vo $(CATEGORY_THEORY_DIR)/*.glob $(CATEGORY_THEORY_DIR)/*.v.d
	rm -rf html
	rm -f frf_formalization.tex frf_formalization.pdf frf_formalization.aux frf_formalization.log
	@echo "✅ Cleanup completed!"

distclean: clean
	@echo "🧹 Deep cleaning..."
	rm -f $(SELF_CONTAINED_DIR)/*~ $(THEORIES_DIR)/*~ $(CS_NULL_DIR)/*~ $(QUANTUM_DIR)/*~ $(DYNAMIC_SYSTEM_DIR)/*~ $(TOOLCHAIN_DIR)/*~ $(TEST_DIR)/*~ $(CATEGORY_THEORY_DIR)/*~
	rm -f *~
	@echo "✅ Deep cleanup completed!"

# ========================
# CI/CD SUPPORT
# ========================
ci: check-version check-deps all test
	@echo "🚀 CI pipeline executed successfully! All modules compiled, validated, and tested!"

ci-fast: check-version check-deps compile check
	@echo "⚡ Fast CI check completed! Compilation and dependency validation passed!"

# ========================
# DEPENDENCY MANAGEMENT
# ========================
opam-deps:
	@echo "📦 Installing dependency packages..."
	opam install coq=8.18.0 coq-mathlib=3.74.0 coq-mathcomp-ssreflect coq-unimath
	@echo "✅ Dependencies installed!"

check-deps:
	@echo "🔍 Verifying module dependencies..."
	# Verify Level 1 dependencies
	@if ! grep -q "Require Import SelfContainedLib.Algebra" $(THEORIES_DIR)/FRF_MetaTheory.v; then echo "❌ FRF_MetaTheory not depending on SelfContainedLib.Algebra"; exit 1; fi
	@if ! grep -q "Require Import FRF_MetaTheory" $(CS_NULL_DIR)/FRF_CS_Null_Common.v; then echo "❌ FRF_CS_Null_Common not depending on FRF_MetaTheory"; exit 1; fi
	# Verify Level 2 dependencies
	@if ! grep -q "Require Import FRF_CS_Null_Common" $(CS_NULL_DIR)/RustNull.v; then echo "❌ RustNull not depending on FRF_CS_Null_Common"; exit 1; fi
	@if ! grep -q "Require Import SelfContainedLib.Geometry" $(QUANTUM_DIR)/CurvedSpacetimeQFT.v; then echo "❌ CurvedSpacetimeQFT not depending on SelfContainedLib.Geometry"; exit 1; fi
	# Verify Level 3 dependencies
	@if ! grep -q "Require Import CaseD_CategoryTheory" $(THEORIES_DIR)/FRF_Comparative.v; then echo "❌ FRF_Comparative not depending on CaseD_CategoryTheory"; exit 1; fi
	@if ! grep -q "Require Import RustNull" $(CS_NULL_DIR)/FRF_CS_Null.v; then echo "❌ FRF_CS_Null not depending on RustNull"; exit 1; fi
	@echo "✅ All module dependency relationships verified correctly!"

check-version:
	@echo "🔍 Verifying Coq version..."
	@coqc --version | grep -q "8.18.0" || (echo "❌ Please use Coq 8.18.0 (current version: $(shell coqc --version | head -n1 | awk '{print $$2}'))"; exit 1)
	@echo "✅ Coq version verified (8.18.0)!"

# ========================
# HELP
# ========================
help:
	@echo "=================================================="
	@echo "📌 FRF Formal Verification Framework Makefile (Coq 8.18.0)"
	@echo "=================================================="
	@echo "Basic targets:"
	@echo "  all         - Compile all modules + validate proofs (default)"
	@echo "  compile     - Compile all modules (hierarchical dependency order)"
	@echo "  validate    - Validate all proofs with coqchk"
	@echo "  test        - Complete compilation + validation + module list"
	@echo ""
	@echo "Level-based testing:"
	@echo "  test-base   - Compile/verify Level 1 base modules only"
	@echo "  test-scene  - Compile/verify Level 2 scene modules only"
	@echo "  test-integration - Compile/verify Level 3 integration modules only"
	@echo ""
	@echo "Quality checks:"
	@echo "  check       - Check compilation completeness for all directories"
	@echo "  status      - Show current compilation progress and module structure"
	@echo "  check-deps  - Verify inter-module dependency relationships"
	@echo "  check-version - Verify Coq version (must be 8.18.0)"
	@echo ""
	@echo "Documentation:"
	@echo "  doc         - Generate HTML documentation (all modules)"
	@echo "  doc-pdf     - Generate PDF documentation (all modules)"
	@echo ""
	@echo "Cleaning:"
	@echo "  clean       - Remove all build artifacts (.vo/.glob/.pdf etc)"
	@echo "  distclean   - Deep clean (including temp and backup files)"
	@echo ""
	@echo "CI/CD:"
	@echo "  ci          - Full CI pipeline (version+deps+compile+validate+test)"
	@echo "  ci-fast     - Fast CI check (version+deps+compile+completeness)"
	@echo ""
	@echo "Dependency management:"
	@echo "  opam-deps   - Install required packages via OPAM"
	@echo "=================================================="