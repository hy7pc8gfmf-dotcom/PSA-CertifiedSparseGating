(* ============================================================
   PSA 运行时守护检查器 CLI 包装
   ------------------------------------------------------------
   编译（需要 OCaml 工具链；本工作区当前无 ocamlopt，见
   PSA_extract.v 头部说明）：
     ocamlopt psa_guard.ml psa_guard_main.ml -o psa_guard.exe
   用法：
     psa_guard.exe sparse <C> <n1> <n2> ...   -> check_sparse_growth
     psa_guard.exe square <c> <n1> <n2> ...   -> check_c_sparse_on_vals
     psa_guard.exe gen <len> <C> <start>      -> generate_base_indices
     psa_guard.exe gateval <M> <n1> <n2> ...  -> greedy_selected (值层面贪心门控)
     psa_guard.exe gateidx <M> <C> <start> <i1> <i2> ... -> greedy_indices
                                                  (索引层面门控, seq = base_seq C start)
     psa_guard.exe mask <M> <n1> <n2> ...    -> fallback_mask (布尔掩码, true/false 列表)
     psa_guard.exe frame <n1> <n2> ...       -> frame_check_instance (反射框架检查器
                                                  μ≤4/5 判定, true/false)
   输出: sparse/square/frame 打印 true|false; gen/gateval/gateidx 打印空格分隔的索引列表;
         mask 打印空格分隔的 true|false。
   nat 为 Peano 表示（O/S），无溢出；CLI 输入/输出为十进制 int。
   注：本工作区 DkMLNative 的 ocamlopt 需 MSVC 汇编器（缺失），
       用字节码编译等价：ocamlc psa_guard.ml psa_guard_main.ml -o psa_guard.exe
   ============================================================ *)

open Psa_guard

let rec int_of_nat = function
  | O -> 0
  | S n -> 1 + int_of_nat n

let rec nat_of_int n =
  if n <= 0 then O else S (nat_of_int (n - 1))

let rec nat_list_of_int_list = function
  | [] -> Nil
  | x :: xs -> Cons (nat_of_int x, nat_list_of_int_list xs)

let rec int_list_of_nat_list = function
  | Nil -> []
  | Cons (x, xs) -> int_of_nat x :: int_list_of_nat_list xs

let string_of_bool = function
  | True -> "true"
  | False -> "false"

let rec bool_list_of_coq_list = function
  | Nil -> []
  | Cons (x, xs) -> string_of_bool x :: bool_list_of_coq_list xs

(* ============================================================
   frame 反射检查器（原生 int 实现，镜像 PSA_framework.v 的
   FrameCheckInstance.frame_check_instance 定义，逐行同构）
   用 OCaml int 替代 Peano nat——提取的 Peano 版在 DkMLNative 字节码下
   对大分母乘法（b*d ≈ 2e9）会栈溢出；这里用机器字整数无此问题。
   soundness 与 Coq 定义的等价性由逐行镜像 + 提取版小梯子核对保证。
   ============================================================ *)

(* floor-sqrt 有理化对界：bound(n1,n2)=n1*n2/(2*(n2-n1)*f), f=isqrt(n1*n2) *)
let int_sqrt n = int_of_float (Float.sqrt (Float.of_int n))

let pair_num n1 n2 = n1 * n2
let pair_den (n1:int) (n2:int) = 2 * (n2 - n1) * int_sqrt (n1 * n2)

(* f 有效性：f*f <= n1*n2 且 0 < f *)
let pair_ok n1 n2 =
  let f = int_sqrt (n1 * n2) in
  (f * f <= n1 * n2) && (0 < f)

(* 行和：对每 j≠i 累加对界（naive，int），判定 5*num <= 4*den *)
let row_sum_le_4_5 ladder i =
  let n = List.length ladder in
  let arr = Array.of_list ladder in
  let ni = arr.(i) in
  let acc = ref (0, 1) in   (* (num, den), den>0 *)
  for j = 0 to n - 1 do
    if j <> i then begin
      let nj = arr.(j) in
      let (n1, n2) = if nj < ni then (nj, ni) else (ni, nj) in
      let num, den = !acc in
      let pn = pair_num n1 n2 in
      let pd = pair_den n1 n2 in
      acc := (num * pd + pn * den, den * pd)
    end
  done;
  let num, den = !acc in
  5 * num <= 4 * den

(* 严格升序 *)
let sorted_strict ladder =
  let rec aux = function
    | a :: (b :: _ as rest) -> a < b && aux rest
    | _ -> true
  in aux ladder

(* 全部 >= 2 *)
let all_ge_2_int ladder = List.for_all (fun v -> v >= 2) ladder

(* 主检查器：frame_check_instance *)
let frame_check_instance_int ladder =
  sorted_strict ladder &&
  all_ge_2_int ladder &&
  (* 所有对界有效 *)
  (let rec pairs_ok = function
     | [] -> true
     | h :: tl -> List.for_all (pair_ok h) tl && pairs_ok tl
   in pairs_ok ladder) &&
  (* 所有行和 <= 4/5 *)
  (let rec rows_le i = function
     | [] -> true
     | _ :: tl -> row_sum_le_4_5 ladder i && rows_le (i + 1) tl
   in rows_le 0 ladder)

let () =
  let args = Array.to_list Sys.argv in
  match args with
  | _ :: "sparse" :: c :: rest ->
      let c = int_of_string c in
      let indices = nat_list_of_int_list (List.map int_of_string rest) in
      print_string (string_of_bool (RuntimeGuards.check_sparse_growth indices (nat_of_int c)))
  | _ :: "square" :: c :: rest ->
      let c = int_of_string c in
      let vals = nat_list_of_int_list (List.map int_of_string rest) in
      print_string (string_of_bool (RuntimeGuards.check_c_sparse_on_vals vals (nat_of_int c)))
  | _ :: "gen" :: len :: c :: start :: _ ->
      let len = int_of_string len and c = int_of_string c and start = int_of_string start in
      let lst = SeqProps.generate_base_indices (nat_of_int len) (nat_of_int c) (nat_of_int start) in
      print_string (String.concat " " (List.map string_of_int (int_list_of_nat_list lst)))
  | _ :: "gateval" :: m :: rest ->
      let m = int_of_string m in
      let vals = nat_list_of_int_list (List.map int_of_string rest) in
      let sel = GreedyGate.greedy_selected (nat_of_int m) vals in
      print_string (String.concat " " (List.map string_of_int (int_list_of_nat_list sel)))
  | _ :: "gateidx" :: m :: c :: start :: rest ->
      let m = int_of_string m and c = int_of_string c and start = int_of_string start in
      let idx = nat_list_of_int_list (List.map int_of_string rest) in
      let sel = GreedyGate.greedy_indices (SeqProps.base_seq (nat_of_int c) (nat_of_int start)) (nat_of_int m) idx in
      print_string (String.concat " " (List.map string_of_int (int_list_of_nat_list sel)))
  | _ :: "mask" :: m :: rest ->
      let m = int_of_string m in
      let vals = nat_list_of_int_list (List.map int_of_string rest) in
      let g = GreedyGate.fallback_mask (nat_of_int m) vals in
      print_string (String.concat " " (bool_list_of_coq_list g))
  | _ :: "frame" :: rest ->
      let vals = List.map int_of_string rest in
      print_string (string_of_bool (if frame_check_instance_int vals then True else False))
  | _ ->
      Printf.eprintf
        "usage: psa_guard.exe sparse <C> <n1> <n2> ... | square <c> <n1> ... | gen <len> <C> <start> | gateval <M> <n1> ... | gateidx <M> <C> <start> <i1> ... | mask <M> <n1> ... | frame <n1> <n2> ...\n";
      exit 2
