(* ============================================================
   PSA 运行时守护检查器提取（Coq 定义 -> OCaml）
   ------------------------------------------------------------
   从 PSA_framework.v 的 Qed 定义中提取可执行检查器：
     - check_sparse_growth   线性稀疏增长守卫（C*a < b 相邻对）
     - check_c_sparse_on_vals 平方稀疏 + 全元素 >= 2 守卫（c*c*a <= b）
     - all_ge_2              全元素 >= 2
     - forallb_adjacent      相邻对通用判定
     - generate_base_indices 确定性生成器（长度 S len，首元素 start）
     - greedy_selected       确定性贪心门控（值层面，门限 M*last <= v）
     - greedy_indices        索引层面门控（seq 提供值；配合 base_seq 即生成器门控）
     - fallback_mask         布尔掩码形式（原文 §3.2；selected_by_mask 提取）
   用法：coqc 编译本文件 -> psa_guard.ml；再以 ocamlopt 编译为 exe
          （psa_guard_main.ml 提供 CLI，psa_guard_ffi.py 提供 Python 封装）。
   注意：nat 按 Coq 默认映射为 OCaml int（机器字，防溢出依赖 63-bit）；
         勿手工加 nat->int 转换层。
   2026-08-18 会话 5 续：加入 GreedyGate 门控函数（greedy_selected / greedy_indices /
         fallback_mask 等）与 SeqProps.base_seq（供索引门控的生成器实例）。
   ============================================================ *)
Require Import Stdlib.Lists.List.
Require Import Extraction.
Require Import PSA.PSA_framework.

Import RuntimeGuards.
Import SeqProps.
Import GreedyGate.
Import FrameCheckInstance.

Extraction Language OCaml.

Extraction "psa_guard"
  RuntimeGuards.check_sparse_growth
  RuntimeGuards.check_c_sparse_on_vals
  RuntimeGuards.all_ge_2
  RuntimeGuards.forallb_adjacent
  SeqProps.generate_base_indices
  SeqProps.gen_aux
  SeqProps.next_idx
  SeqProps.base_seq
  GreedyGate.greedy_selected
  GreedyGate.greedy_aux
  GreedyGate.greedy_indices
  GreedyGate.greedy_idx_aux
  GreedyGate.fallback_mask
  GreedyGate.mask_aux
  GreedyGate.selected_by_mask
  FrameCheckInstance.pair_num
  FrameCheckInstance.pair_den
  FrameCheckInstance.pair_ok
  FrameCheckInstance.frac_add
  FrameCheckInstance.row_sum_frac_aux
  FrameCheckInstance.row_sum_frac
  FrameCheckInstance.row_le_4_5
  FrameCheckInstance.sorted_aux
  FrameCheckInstance.sorted_strict_aux
  FrameCheckInstance.all_ge_2
  FrameCheckInstance.all_pairs_ok
  FrameCheckInstance.all_rows_le
  FrameCheckInstance.frame_check_instance.
