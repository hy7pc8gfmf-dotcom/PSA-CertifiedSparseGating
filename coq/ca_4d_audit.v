(* ============================================================
   ca_4d_audit.v —— ca_basis_4d.v 公理审计探针（会话 13，E039 隔离纪律）
   目的：对 4D 张量积模块（N=4 预测→已证 + 主引擎 + 组装定理）做
         Print Assumptions 审计，记录经典逻辑/公理脚印（预期零 classic，
         仅继承 ca_* P4 库反射层基础设施；nat_quad_decode_inj / min8_is_one
         纯 nat 应为 Closed under the global context）。
   用法：coqc -Q src ""（同 ca_basis_4d.v 的 load path），Print Assumptions
         输出重定向审计文件。
   状态：2026-08-19 会话 13 建立，ca_basis_4d.v RC=0 后编译。
         （会话 14 追加主引擎/组装定理审计条目。）
   ============================================================ *)
Require Import Stdlib.Lists.List.
Require Import Stdlib.Reals.Reals.
Require Import ca_basis_4d.

(* ---- 归一化常数层 ---- *)
Print Assumptions gamma4_pos.
Print Assumptions gamma4_sq.

(* ---- 混合进制双射（纯 nat 算术） ---- *)
Print Assumptions nat_quad_decode_inj.
Print Assumptions min8_is_one.

(* ---- 16 分支常数引理（K0 = Rmax 8C³/2） ---- *)
Print Assumptions one_le_half_K0_4dprod.

(* ---- 数值紧度（N=4: M_bound_4d 4 = 19968） ---- *)
Print Assumptions M_bound_4d_C4_value.

(* ---- 主引擎与组装定理（会话 14 追加） ---- *)
Print Assumptions phi4D_inner_scalar_decomposition.
Print Assumptions quad_inner_single_bound.
Print Assumptions phi_flat_decay_general_4d.
Print Assumptions tensor_product_unconditional_basis_4d.

(* ---- 数值核验（Compute 输出应 = 19968） ---- *)
Compute M_bound_4d 4.
