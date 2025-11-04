# ChurchZero.v 编译验证脚本（兼容项目层级依赖）
#!/bin/bash
set -eo pipefail  # 错误立即退出，捕获管道失败，确保脚本严谨性

# ======================== 1. 脚本配置与前置检查 ========================
# 项目目录结构（与项目标准结构对齐）
BASE_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/.."  # 脚本所在目录的上级目录（项目根目录）
SELF_CONTAINED_DIR="${BASE_DIR}/SelfContainedLib"
THEORIES_DIR="${BASE_DIR}/theories"
# 编译参数（严格匹配项目层级依赖的模块路径映射）
BASE_FLAGS="-Q ${SELF_CONTAINED_DIR} SelfContainedLib -Q ${THEORIES_DIR} FRF.Theories"
# 待验证模块列表（按依赖顺序排列，确保无循环依赖）
DEP_MODULES=(
  # 一级基础层（ChurchZero.v间接依赖）
  "${SELF_CONTAINED_DIR}/Algebra.v"
  "${SELF_CONTAINED_DIR}/Category.v"
  "${SELF_CONTAINED_DIR}/Geometry.v"
  # 二级元理论层（ChurchZero.v直接依赖）
  "${THEORIES_DIR}/FRF_MetaTheory.v"
  "${THEORIES_DIR}/ChurchNumerals.v"
  # 目标验证模块
  "${THEORIES_DIR}/ChurchZero.v"
)
# 编译成功标志文件（Coq编译产物）
SUCCESS_VO_FILES=("${THEORIES_DIR}/ChurchZero.vo")

# 前置检查：确保Coq环境可用
check_coq_env() {
  echo "🔍 检查Coq环境..."
  if ! command -v coqc &> /dev/null; then
    echo "❌ 错误：未找到coqc命令，请先通过opam安装Coq 8.18.0"
    echo "   安装命令参考：opam install coq.8.18.0"
    exit 1
  fi
  COQ_VERSION=$(coqc --version | head -n1 | awk '{print $3}')
  if [ "${COQ_VERSION}" != "8.18.0" ]; then
    echo "⚠️ 警告：Coq版本为${COQ_VERSION}，推荐使用8.18.0（项目验证过的版本）"
  else
    echo "✅ Coq环境正常（版本：${COQ_VERSION}）"
  fi
}

# 前置检查：确保项目目录结构完整
check_project_structure() {
  echo -e "\n🔍 检查项目目录结构..."
  local required_dirs=("${SELF_CONTAINED_DIR}" "${THEORIES_DIR}")
  for dir in "${required_dirs[@]}"; do
    if [ ! -d "${dir}" ]; then
      echo "❌ 错误：目录${dir}不存在，请确保项目结构完整"
      exit 1
    fi
  done
  # 检查依赖模块文件是否存在
  for mod in "${DEP_MODULES[@]}"; do
    if [ ! -f "${mod}" ]; then
      echo "❌ 错误：依赖模块${mod}不存在，请检查文件路径"
      exit 1
    fi
  done
  echo "✅ 项目目录结构与依赖文件完整"
}

# ======================== 2. 环境初始化 ========================
init_env() {
  echo -e "\n🚀 初始化编译环境..."
  # 加载opam环境（Coq通常通过opam管理，确保coqc在PATH中）
  if command -v opam &> /dev/null; then
    eval "$(opam env)"
    echo "✅ Opam环境加载成功"
  else
    echo "⚠️ 警告：未找到opam，将使用系统PATH中的Coq（若存在）"
  fi
  # 创建编译日志目录（用于保存编译输出，便于错误排查）
  mkdir -p "${BASE_DIR}/compile_logs"
  echo "✅ 编译日志目录创建完成（${BASE_DIR}/compile_logs）"
}

# ======================== 3. 层级编译依赖模块 ========================
compile_module() {
  local mod_path="$1"
  local mod_name=$(basename "${mod_path}")
  local log_file="${BASE_DIR}/compile_logs/${mod_name%.v}.log"
  
  echo -e "\n📦 正在编译模块：${mod_name}"
  # 执行编译，捕获输出到日志
  if coqc ${BASE_FLAGS} "${mod_path}" 2>"${log_file}"; then
    # 编译成功：检查.vo文件是否生成（Coq编译成功的核心标志）
    local vo_file="${mod_path%.v}.vo"
    if [ -f "${vo_file}" ]; then
      echo "✅ ${mod_name} 编译成功（产物：${vo_file}）"
      return 0
    else
      echo "❌ ${mod_name} 编译无错误，但未生成.vo文件（异常情况）"
      cat "${log_file}" | head -20  # 输出日志前20行辅助排查
      exit 1
    fi
  else
    # 编译失败：输出详细错误信息
    echo "❌ ${mod_name} 编译失败，错误信息如下（前20行）："
    cat "${log_file}" | head -20
    echo "📄 完整错误日志已保存至：${log_file}"
    exit 1
  fi
}

compile_dependencies() {
  echo -e "\n📊 开始按层级编译依赖模块（共$((${#DEP_MODULES[@]}))个模块）"
  for mod in "${DEP_MODULES[@]}"; do
    compile_module "${mod}"
  done
}

# ======================== 4. 编译结果校验 ========================
validate_compile_result() {
  echo -e "\n🔍 验证编译结果..."
  local all_success=true
  for vo_file in "${SUCCESS_VO_FILES[@]}"; do
    if [ -f "${vo_file}" ]; then
      echo "✅ 目标产物 ${vo_file} 存在（编译成功）"
    else
      echo "❌ 目标产物 ${vo_file} 缺失（编译失败）"
      all_success=false
    fi
  done

  # 输出最终总结
  echo -e "\n======================= 编译验证总结 ========================"
  if ${all_success}; then
    echo "🎉 所有模块（含ChurchZero.v）编译验证通过！"
    echo "✅ 已验证模块列表："
    for mod in "${DEP_MODULES[@]}"; do
      echo "  - $(basename "${mod}")"
    done
    echo "📌 核心验证结论：ChurchZero.v 修复后可正常编译，依赖链路完整"
    exit 0
  else
    echo "❌ ChurchZero.v 编译验证失败，请查看错误日志排查问题"
    exit 1
  fi
}

# ======================== 5. 脚本主流程 ========================
main() {
  echo "=================================================="
  echo "📋 ChurchZero.v 编译验证脚本（项目层级依赖版）"
  echo "=================================================="
  
  # 执行前置检查
  check_coq_env
  check_project_structure
  
  # 初始化环境
  init_env
  
  # 层级编译依赖与目标模块
  compile_dependencies
  
  # 验证编译结果
  validate_compile_result
}

# 启动脚本主流程
main