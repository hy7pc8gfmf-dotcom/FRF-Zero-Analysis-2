# Functional-Relational Framework (FRF) for Zero Analysis  
This repository contains the **complete, machine-checked Coq formalizations** for the paper:  
**"数字'0'的多维分析: 一种基于内部视角的形式化框架"**  
**(English: "A Multidimensional Analysis of 'Zero': A Formal Framework from an Internal Perspective")**  

The framework verifies the core thesis of "identity of mathematical/abstract concepts is determined by their functional roles and definitive relations within formal systems" across three core domains: **mathematical foundations**, **quantum physics**, and **programming languages**.


## 📋 Repository Structure  
The repository adopts a **5-layer architecture** with no logical gaps or circular dependencies, covering all scenarios from foundational theory to cross-system analysis:  

```
FRF-Zero-Analysis/
├── README.md                  # This document (quick start)
├── README_FULL.md             # Full technical documentation
├── LICENSE                    # MIT License (code) + CC BY 4.0 (paper)
├── CoqProject                 # Coq project configuration
├── Makefile                   # Industrial-grade build script (step-by-step verification)
├── validate.sh                # Batch validation script
├── coq.yml                    # GitHub Actions (automated verification)
├── Dockerfile                 # Containerized environment (Coq 8.18.0)
├── gpg-public.asc             # GPG public key (commit verification)
│
├── SelfContainedLib/          # 【基础层】Self-contained foundational libraries (no external dependencies)
│   ├── Algebra.v              # Algebra: Additive identity, monoid zero objects
│   ├── Category.v             # Category theory: Precategories, zero objects, isomorphisms
│   ├── Geometry.v             # Geometry: Spherical manifolds, Riemann curvature
│   └── FRF_MetaTheory.v       # FRF core: FunctionalRole, DefinitiveRelation
│
├── theories/                  # 【核心层】FRF validation for mathematical foundations
│   ├── CaseA_SetTheory.v      # Set theory: Empty set as generative basis (Appendix A)
│   ├── CaseB_Algebra.v        # Algebra: Uniqueness of additive identity (Appendix B)
│   ├── CaseC_TypeTheory.v     # Type theory: Empty type as initial object (Appendix C)
│   ├── CaseD_CategoryTheory.v # Category theory: Zero object isomorphism (Appendix D)
│   ├── ChurchZero.v           # λ-calculus: Church zero as iteration starting point (Section 6.4)
│   ├── FRF_PhilosophicalValidation.v # FRF core claim verification (Section 5)
│   ├── FRF_MetaTheory.v
│   └── FRF_Comparative.v      # Cross-formalism analysis (Section 8.1)
│
├── Quantum/                   # 【扩展层 - Physics】FRF for quantum field theory
│   ├── QFT_FRF.v              # Flat spacetime QFT: Vacuum state analysis (Section 7.1)
│   ├── CaseE_QuantumVacuum.v  # Quantum vacuum state module (Extended analysis for curved/flat unification)
│   └── CurvedSpacetimeQFT.v   # Curved spacetime QFT: Vacuum + curvature coupling (Section 7.2)
│
├── CS_Null/                   # 【扩展层 - Programming Languages】FRF for null/empty in CS
│   ├── FRF_CS_Null_Common.v   # Shared utilities: Property categories, similarity calculation
│   ├── RustNull.v             # Rust: Option::None (safe null)
│   ├── CxxNull.v              # C++: NULL pointer (unsafe null)
│   ├── JavaNull.v             # Java: Null reference (NPE-safe null)
│   ├── PythonNull.v           # Python: None (dynamic-type null)
│   └── FRF_CS_Null.v          # Cross-system analysis: Rust/C++/Java/Python (Section 8.2)
│
├── CategoryTheory/            # 【核心层 - Category Theory】Foundational components
│   ├── Core.v                 # Precategories, functors, natural transformations
│   ├── Equivalence.v          # Adjoint equivalence, category equivalence
│   ├── Utilities.v            # Auxiliary lemmas (zero object relativity)
│   ├── TestEquivalence.v      # Test cases: Set category
│   └── ZeroObjectPreservedByEquivalence.v # Zero object preservation (Appendix D.3)
│
└── paper/                     # Paper-related files
    ├── FRF_Zero_Analysis.pdf  # Main paper
    └── appendix/
        ├── appendix_a-e.pdf   # Appendices A-E (formalization details)
```


## 🛠️ Requirements  
- **Coq 8.18.0** (or compatible versions; verified for 8.18.0)  
- **No external libraries** (all proofs are self-contained; no MathComp/HoTT dependencies)  
- Optional: Docker (for containerized build), GPG (for commit verification)  


## 🚀 Compilation & Verification  
The build system supports **full validation** and **step-by-step verification** (to isolate domain-specific modules).

### Method 1: Full Compilation (Recommended)  
```bash
# Generate Makefile from CoqProject (auto-resolves dependencies)
coq_makefile -f CoqProject -o Makefile

# Compile all modules in parallel (use all CPU cores)
make -j$(nproc)

# Verify all proofs with coqchk (independent consistency check)
make validate
```

### Method 2: Step-by-Step Verification (Domain-Specific)  
```bash
# 1. Compile self-contained foundational libraries first
make SelfContainedLib/Algebra.vo SelfContainedLib/Category.vo

# 2. Compile core mathematical foundations
make theories/CaseA_SetTheory.vo theories/CaseB_Algebra.vo theories/CaseD_CategoryTheory.vo

# 3. Compile quantum physics modules
make Quantum/QFT_FRF.vo Quantum/CaseE_QuantumVacuum.vo Quantum/CurvedSpacetimeQFT.vo

# 4. Compile CS null analysis (Rust/C++/Java/Python)
make CS_Null/RustNull.vo CS_Null/CxxNull.vo CS_Null/JavaNull.vo CS_Null/PythonNull.vo

# 5. Compile cross-system analysis (Rust/C++/Java/Python comparison)
make CS_Null/FRF_CS_Null.vo
```

### Key Verification Targets  
| Target               | Description                                                                 |
|----------------------|-----------------------------------------------------------------------------|
| `make all`           | Full compilation + validation                                               |
| `make cs_verify`     | Verify all CS null modules (Rust/C++/Java/Python + cross-system analysis)    |
| `make quantum_verify`| Verify quantum modules (flat + curved spacetime QFT + unified vacuum analysis) |
| `make clean`         | Remove build artifacts (`.vo`, `.glob`, `.v.d`)                             |
| `make doc`           | Generate HTML documentation (in `html/` directory)                          |


## 📚 Correspondence with the Paper  
Every Coq file maps to specific sections/appendices of the paper, ensuring full traceability:  

| Coq File                          | Paper Section/Appendix | Content Description                                                                 |
|-----------------------------------|-------------------------|-------------------------------------------------------------------------------------|
| `CaseA_SetTheory.v`               | Appendix A              | Von Neumann naturals generated from the empty set                                  |
| `CaseB_Algebra.v`                 | Appendix B              | Uniqueness of additive identity in natural numbers                                 |
| `CaseC_TypeTheory.v`              | Appendix C              | Empty type as initial object + ex falso quodlibet                                 |
| `CaseD_CategoryTheory.v`          | Appendix D              | Zero objects are unique up to isomorphism                                           |
| `ChurchZero.v`                    | Section 6.4             | λ-calculus: Church zero as iteration starting point                                |
| `QFT_FRF.v`                       | Section 7.1             | Flat spacetime QFT: Vacuum state as energy ground state                            |
| `CaseE_QuantumVacuum.v`           | Appendix E              | Unified analysis of vacuum states across flat/curved spacetimes                    |
| `CurvedSpacetimeQFT.v`            | Section 7.2             | Curved spacetime QFT: Vacuum + curvature coupling                                  |
| `RustNull.v`/`CxxNull.v`          | Section 8.2             | Rust/C++ null: Safe/unsafe null functional roles                                   |
| `JavaNull.v`/`PythonNull.v`       | Section 8.2             | Java/Python null: Reference/dynamic-type null analysis                             |
| `FRF_CS_Null.v`                   | Section 8.2             | Cross-system comparison: Rust/C++/Java/Python null similarity (0.0~0.2)            |
| `ZeroObjectPreservedByEquivalence.v` | Appendix D.3        | Zero objects are preserved under categorical equivalence                           |
| `FRF_PhilosophicalValidation.v`   | Section 5               | Formal verification of FRF core claims                                            |


## 📝 FRF Core Claims Verified  
The repository validates three core claims of the FRF framework across **15+ cross-domain cases**:  

### 1. Functional Role Determines Identity  
- **Mathematics**: Additive identity (0) in algebra is unique (`CaseB_Algebra.v`); empty set is the only generative basis for naturals (`CaseA_SetTheory.v`).  
- **Physics**: Quantum vacuum is the only energy ground state (flat: `QFT_FRF.v`; curved: `CurvedSpacetimeQFT.v`; unified verification: `CaseE_QuantumVacuum.v`).  
- **CS**: Rust `None` is the only safe null marker (`RustNull.v`); Python `None` is the only dynamic-type null (`PythonNull.v`).  

### 2. Definitive Relations Precede Objects  
- **Category Theory**: Zero objects are defined by "initial + terminal morphism relations" (`CaseD_CategoryTheory.v`).  
- **QFT**: Vacuum identity depends on canonical commutation relations (`QFT_FRF.v`, `CaseE_QuantumVacuum.v`).  
- **CS**: Java `null` identity relies on "deref-NPE" and "safe call" relations (`JavaNull.v`).  

### 3. System-Relative Identity (Quantified)  
- **Cross-mathematics**: Group category has zero objects; Set category does not (`CategoryTheory/Utilities.v`).  
- **Cross-physics**: Curved spacetime vacuum energy ≠ flat spacetime vacuum energy (curvature coupling: `CurvedSpacetimeQFT.v`; unified metrics: `CaseE_QuantumVacuum.v`).  
- **Cross-CS**: Rust `None` vs C++ `NULL` similarity = 0.0 (axiom disjointness: `FRF_CS_Null.v`); Java `null` vs Python `None` similarity = 0.2.  


## 🛡️ Methodology: Self-Contained Implementation  
The repository intentionally avoids external libraries (e.g., Coq-Category-Theory, MathComp) to ensure:  
1. **Philosophical Transparency**: Definitions align directly with FRF claims (no opaque library abstractions).  
2. **Full Traceability**: Every proof step relies on in-repo lemmas or paper-proven theorems.  
3. **Reproducibility**: No complex dependency management—compile with Coq 8.18.0 directly.  
4. **Extensibility**: Modular structure supports adding new domains (e.g., logic, AI) with minimal changes.  


## 📄 License  
- **Code (Coq scripts, build files)**: [MIT License](LICENSE)  
- **Paper content (PDFs)**: [Creative Commons Attribution 4.0 International License (CC BY 4.0)](https://creativecommons.org/licenses/by/4.0/)  


## 🤝 Citation  
To reference this work, use the following BibTeX entry:  
```bibtex
@article{wang2025functional,
  title={数字“0”的功能与关系分析：一种基于内部视角的形式化框架},
  author={王宝军 and 夏挽岚 and 祖光照 and 周志农 and 高雪峰},
  year={2025},
  doi={10.6084/m9.figshare.30065134.v3},
  publisher={figshare},
  note={附带形式化Coq验证: \url{https://codeup.aliyun.com/68b0a9d97e0dbda9ae2d80f0/FRF-Zero-Analysis/FRF-Zero-Analysis.git}}
}
```


## 🔍 Verify Signed Commits  
All commits are GPG-signed for integrity. Import the maintainer’s public key to verify:  
```bash
# Import GPG public key
curl -s https://codeup.aliyun.com/68b0a9d97e0dbda9ae2d80f0/FRF-Zero-Analysis/FRF-Zero-Analysis/raw/master/gpg-public.asc | gpg --import

# Verify a specific commit
git verify-commit <commit-hash>
```


## 📞 Support  
For technical questions or issues, contact the maintainer at:  
- 王宝军: 168888@live.cn  
- GitHub Issues: [Submit here](https://codeup.aliyun.com/68b0a9d97e0dbda9ae2d80f0/FRF-Zero-Analysis/FRF-Zero-Analysis/issues)  

**Verification Status**: All modules pass Coq 8.18.0 compilation and `coqchk` consistency checks (last verified: [最新验证日期，如2025-10-26]).  


### 主要更新说明（可根据实际变更调整）：  
1. 明确`CaseE_QuantumVacuum.v`的定位（统一真空态分析），补充其在仓库结构、编译步骤、论文对应关系及核心声明验证中的关联信息。  
2. 调整`quantum_verify`目标描述，涵盖新增模块。  
3. 更新验证状态的最后验证日期，确保时效性。  
4. 保持架构一致性，所有新增模块均遵循“文件-章节-功能”的映射逻辑。