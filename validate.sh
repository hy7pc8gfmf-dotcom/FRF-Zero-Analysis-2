#!/bin/bash
# validate.sh - Validate all Coq proofs in the repository with dependency-aware compilation

set -eo pipefail  # Exit on error, unset variable, or pipeline failure

# --------------------------
# 前置检查：环境与目录验证
# --------------------------
echo "🔍 Validating FRF Coq formalizations..."
echo "========================================"

# 检查Coq编译器是否安装
if ! command -v coqc &> /dev/null; then
    echo "❌ Error: coqc (Coq compiler) not found in PATH."
    echo "Please install Coq first (https://coq.inria.fr/download)."
    exit 1
fi

# 验证理论文件目录存在
THEORIES_DIR="theories"
if [ ! -d "$THEORIES_DIR" ]; then
    echo "❌ Error: Theory directory '$THEORIES_DIR' not found."
    echo "Please ensure the project structure includes a '$THEORIES_DIR' folder with .v files."
    exit 1
fi

# 检查是否有Coq源文件
shopt -s nullglob  # 避免无匹配时产生"*.v"字面量
V_FILES=("$THEORIES_DIR"/*.v)
if [ ${#V_FILES[@]} -eq 0 ]; then
    echo "⚠️ Warning: No .v files found in '$THEORIES_DIR' directory."
    echo "✅ Validation complete (no proofs to check)."
    exit 0
fi
shopt -u nullglob  # 恢复默认行为

# --------------------------
# 编译配置与依赖处理
# --------------------------
echo "📦 Coq version:"
coqc --version || { echo "❌ Failed to get Coq version"; exit 1; }

echo ""
echo "📁 Compiling Coq files (dependency order required)..."
echo "---------------------------------------------------"

# 按依赖顺序编译（需手动维护顺序以避免编译失败）
# 注意：若存在依赖关系，需按"基础文件→依赖文件"排序
COMPILE_ORDER=(
    "preliminaries.v"
    "nat_system.v"
    "relations.v"
    "functional_roles.v"
    # 补充项目实际.v文件及正确顺序
)

# 验证编译顺序中的文件是否存在
for file in "${COMPILE_ORDER[@]}"; do
    full_path="$THEORIES_DIR/$file"
    if [ ! -f "$full_path" ]; then
        echo "❌ Error: Required file '$full_path' not found in compile order."
        exit 1
    fi
done

# 执行编译
for file in "${COMPILE_ORDER[@]}"; do
    full_path="$THEORIES_DIR/$file"
    filename=$(basename "$file")
    echo "Compiling $filename..."
    (cd "$THEORIES_DIR" && coqc -q "$filename")  # -q 抑制冗余输出
    echo "  ✅ $filename compiled successfully"
done

# --------------------------
# 验证结果检查
# --------------------------
echo ""
echo "✅ Compilation phase complete!"
echo "-----------------------------"
echo "Verified proofs:"

# 检查生成的目标文件
VO_FILES=("$THEORIES_DIR"/*.vo)
for vo in "${VO_FILES[@]}"; do
    echo "  - $(basename "$vo" .vo)"
done

# --------------------------
# 统计与最终确认
# --------------------------
echo ""
echo "📊 Validation Summary:"
echo "======================"
total_v=$(find "$THEORIES_DIR" -maxdepth 1 -type f -name "*.v" | wc -l)
total_vo=$(find "$THEORIES_DIR" -maxdepth 1 -type f -name "*.vo" | wc -l)

echo "Total Coq source files: $total_v"
echo "Successfully verified: $total_vo"

if [ "$total_v" -eq "$total_vo" ]; then
    echo "🎉 All proofs verified successfully!"
    exit 0
else
    echo "❌ Validation failed: Mismatch between source files and verified outputs."
    exit 1
fi