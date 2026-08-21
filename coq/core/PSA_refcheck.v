(* PSA 运行时守护检查器参考值计算（供 Python FFI 自测对照） *)
Require Import Stdlib.Lists.List.
Require Import PSA.PSA_framework.
Import RuntimeGuards.
Import SeqProps.
Import GreedyGate.

(* 线性稀疏增长守卫 *)
Eval compute in (check_sparse_growth (2 :: 5 :: 11 :: nil) 2).
Eval compute in (check_sparse_growth (2 :: 5 :: 10 :: nil) 2).
Eval compute in (check_sparse_growth nil 2).
Eval compute in (check_sparse_growth (7 :: nil) 3).

(* 平方稀疏 + >=2 守卫（含 c*c*a = b 相等情形，验证 <=? 语义修正） *)
Eval compute in (check_c_sparse_on_vals (3 :: 13 :: 53 :: nil) 2).
Eval compute in (check_c_sparse_on_vals (3 :: 3 :: 4 :: nil) 1).
Eval compute in (check_c_sparse_on_vals (1 :: 13 :: 53 :: nil) 2).
Eval compute in (check_c_sparse_on_vals nil 2).

(* 确定性生成器 *)
Eval compute in (generate_base_indices 3 2 5).
Eval compute in (generate_base_indices 5 3 2).
Eval compute in (generate_base_indices 0 2 2).

(* 2026-08-18 会话 5 续：贪心门控参考值（值层 / 索引层 / 掩码） *)
Eval compute in (greedy_selected 2 (3 :: 5 :: 9 :: 20 :: nil)).
Eval compute in (greedy_selected 4 (3 :: 5 :: 9 :: 20 :: nil)).
Eval compute in (greedy_selected 2 (2 :: 5 :: 11 :: 23 :: nil)).
Eval compute in (greedy_selected 1 (3 :: 3 :: 4 :: nil)).
Eval compute in (greedy_indices (base_seq 2 5) 4 (0 :: 1 :: 2 :: 3 :: nil)).
Eval compute in (greedy_indices (base_seq 3 2) 9 (0 :: 1 :: 2 :: 3 :: 4 :: 5 :: nil)).
Eval compute in (fallback_mask 2 (3 :: 5 :: 9 :: 20 :: nil)).
Eval compute in (fallback_mask 4 (3 :: 5 :: 9 :: 20 :: nil)).
Eval compute in (selected_by_mask (3 :: 5 :: 9 :: 20 :: nil) (fallback_mask 2 (3 :: 5 :: 9 :: 20 :: nil))).
