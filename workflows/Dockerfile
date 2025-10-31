# ======================== 基础镜像选择（锁定Coq版本，避免环境差异） ========================
# 基于官方Coq 8.18.0镜像，预配置OPAM包管理和基础编译环境
FROM coqorg/coq:8.18.0 AS frf-base

# 维护者信息（便于问题反馈）
LABEL maintainer="FRF 2.0 Team <frf-zero-analysis@example.com>"
LABEL description="Docker image for FRF 2.0 Formalization (Coq 8.18.0 + Mathlib 3.74.0)"
LABEL version="1.0"

# ======================== 环境变量配置（统一路径与依赖版本） ========================
# 1. 模块搜索路径：与本地/CI部署对齐，避免“未定义标识符”错误
ENV COQPATH="/app/SelfContainedLib:/app/theories:/app/CS_Null:/app/Quantum:/app/CategoryTheory"
# 2. 依赖版本锁定：Mathlib版本与FRF 2.0严格兼容
ENV MATHLIB_VERSION="3.74.0"
# 3. 工作目录：统一代码存放路径
WORKDIR /app
# 4. 编码与语言：避免日志乱码
ENV LANG=C.UTF-8
ENV LC_ALL=C.UTF-8

# ======================== 权限配置（安全最佳实践：非root用户运行） ========================
# 基础镜像已创建coq用户，切换至该用户避免权限风险
USER coq
# 确保工作目录权限归属coq用户
RUN chown -R coq:coq /app

# ======================== 依赖安装（分层缓存：依赖不变则不重复构建） ========================
# 步骤1：更新OPAM仓库索引（加速后续依赖下载）
RUN opam update -y && \
    # 步骤2：安装指定版本的Mathlib（FRF 2.0核心依赖）
    opam install -y coq-mathlib=${MATHLIB_VERSION} && \
    # 步骤3：安装工程工具依赖（Python库用于报告生成、日志分析）
    pip3 install --no-cache-dir pyyaml==6.0.1 markdown==3.5 gitpython==3.1.40 && \
    # 步骤4：清理OPAM缓存，减少镜像体积
    opam clean -y && \
    # 步骤5：验证依赖版本（确保无版本冲突）
    coqc --version | grep -q "8.18.0" && \
    opam list | grep -q "coq-mathlib.*${MATHLIB_VERSION}" && \
    pip3 list | grep -q "pyyaml.*6.0.1"

# ======================== 代码复制与预处理（保留权限，避免编译错误） ========================
# 复制代码仓库（含所有FRF 2.0模块），保留文件权限
COPY --chown=coq:coq . /app

# 步骤1：验证核心配置文件是否存在（CoqProject是模块依赖的关键）
RUN if [ ! -f "CoqProject" ]; then \
        echo "❌ 错误：未找到CoqProject文件（模块依赖配置缺失）" && exit 1; \
    fi && \
    # 步骤2：生成依赖感知的Makefile（按层级解析模块依赖）
    coq_makefile -f CoqProject -o Makefile && \
    # 步骤3：验证Makefile是否包含核心模块（确保编译目标无遗漏）
    grep -q "SelfContainedLib/Algebra.vo" Makefile && \
    grep -q "CS_Null/FRF_CS_Null.vo" Makefile && \
    grep -q "Quantum/QFT_FRF.vo" Makefile && \
    echo "✅ Makefile生成成功，核心模块目标存在"

# ======================== 全量编译（预编译核心模块，加速后续使用） ========================
RUN echo "=== 开始全量编译FRF 2.0核心模块 ===" && \
    # 多核编译（利用容器CPU资源，约30-45分钟，视配置而定）
    make -j$(nproc) 2>&1 | tee /app/compile-full.log && \
    # 验证编译结果（核心模块.vo文件是否生成）
    core_vo_files=(
        "SelfContainedLib/Algebra.vo"
        "theories/FRF_MetaTheory.vo"
        "CS_Null/RustNull.vo"
        "Quantum/QFT_FRF.vo"
        "theories/FRF_Comparative.vo"
    ) && \
    for vo in "${core_vo_files[@]}"; do \
        if [ ! -f "$vo" ]; then \
            echo "❌ 错误：核心模块$vo未编译成功" && exit 1; \
        fi; \
    done && \
    # 清理中间产物（减少镜像体积，保留.vo/.glob等关键文件）
    make clean && \
    rm -rf /app/_build/*.log && \
    echo "✅ FRF 2.0全量编译完成，镜像构建成功"

# ======================== 容器启动配置（默认交互模式，方便使用） ========================
# 启动时默认进入bash交互环境，支持手动执行验证、调试等操作
CMD ["bash"]