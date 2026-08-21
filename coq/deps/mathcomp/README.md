# mathcomp (Mathematical Components) — vendored dependency

本目录为 **Mathematical Components (mathcomp)** 的完整源码副本（217 个 .v 文件，9.48 MB），
从本地 Rocq 9.0 平台安装（`user-contrib/mathcomp`）复制，用于仓库自包含构建。

## 许可

- **版权所有者**：mathcomp 项目团队（Assia Mahboubi, Georges Gonthier, 及贡献者等）。
- **许可证**：**CeCILL-C**（version 1.0，自由软件许可，与 BSD 2-clause 兼容）。
  - CeCILL-C 完整文本：https://cecill.info/licences/Licence_CeCILL-C_V1-en.txt
  - 允许：使用、修改、再分发（保留版权与许可声明）；禁止主张担保。
- 本 vendored 副本不修改 mathcomp 的任何源码；仅作为依赖随仓库分发。
- 使用本目录内的代码，须遵守 CeCILL-C 条款；PSA 项目自身的代码不受此影响
  （PSA 代码以 Apache-2.0 + CLA 双许可，见仓库根 `LICENSE` 与 `CLA/`）。

## 上游

- 官网：https://math-comp.github.io/
- 源码：https://github.com/math-comp/math-comp
- 版本：本副本对应本机 Rocq 9.0 平台随附的 mathcomp 版本（ssreflect 2.x 系）。

## 说明

- 编译时以 `-Q coq/deps/mathcomp mathcomp` 挂载（CI 与本地一致）。
- Coquelicot（另一外部依赖）因无官方 GitHub 镜像且本地仅有编译产物（.vo），
  未 vendor；CI 中经 opam 安装（`coq-coquelicot`），本地使用平台 .vo。
