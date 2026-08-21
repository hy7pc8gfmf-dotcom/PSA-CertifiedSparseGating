# PSA-CertifiedSparseGating — 项目长期记忆

## CI 流水线
- 定义：`.github/workflows/coq.yml`（`coq-community/docker-coq-action@v1.5.2`，Rocq 9.0，跑 `scripts/ci_build.sh`）。
- 触发器：仅 `push` 到 `main` 或 `pull_request`，**没有 `workflow_dispatch`**。要手动重跑只能再 push 一个 commit（建议加 `workflow_dispatch`）。
- 构建脚本 `scripts/ci_build.sh` 历史有两个 bug（已修于 1419c63）：`order.txt` 注释行未跳过；mathcomp/Coquelicot 路径解析错误（须用 `coqc -where user-contrib`/小写 `coquelicot`）。

## 本机 Git/网络环境（重要）
- `gh` CLI 未安装。
- `git-credential-manager`(GCM) 在本机 **segfault**，不能用。
- 认证用 `git -c credential.helper=wincred push origin main`（Windows 凭据管理器，GitHub Desktop 已存 token，`cmdkey` 中可见 `git:https://github.com`）。
- 网络极不稳定：GitHub 连接常被防火墙 reset（`Recv failure: Connection was reset`），需命中稳定窗口才能 push；重试循环 + 单次 push 用小 commit 易成功。
