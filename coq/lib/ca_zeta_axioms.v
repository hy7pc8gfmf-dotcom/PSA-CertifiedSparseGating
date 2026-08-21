(* ============================================================
   库: ca_zeta_axioms —— 已清空（占位说明）
   ============================================================

   本库原为原文件中的 Module ZetaAxioms（原文行 17473-17731），内容为：

     - Axiom zeta_series_conv_re / zeta_series_conv_im（两条"待证明"的级数收敛公理）
     - Definition zeta（完全由上述公理 proj1_sig 定义）
     - Axiom zeta_series（ζ = 狄利克雷级数，0 处使用）
     - Axiom Riemann_hypothesis（伪黎曼假设：前提 re s > 1 下退化、语句错误、全库 0 处使用）
     - Parameter Cgamma / Axiom Cgamma_neq_0（0 处使用）
     - Notation "'ζ' s"（重复声明三次）

   清理决定（2026-08-15，配合 my_complex_pow 数学修复）：
     1. 作者已声明不主张黎曼猜想 → 删除 Riemann_hypothesis 公理；
     2. 收敛公理所声称的结论已在 ca_gamma 中**被证明**（zeta_series_converges /
        zeta_series_converges_0_1，且经 my_complex_pow 修复后对应真正的 Σ n^{-s}），
        因此公理化 zeta 不再需要，连同 zeta_series / Cgamma 一并删除；
     3. 全库没有任何其它模块引用本库（叶子库），清空后依赖链不受影响。

   若未来需要"以证明过的收敛性构造 Re(s) > 1 的 ζ"，应直接基于 ca_gamma 的
   zeta_series_converges 构造，而不要恢复本库的公理。
   ============================================================ *)
