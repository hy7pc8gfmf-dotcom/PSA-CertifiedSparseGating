(* Z2b bench：镜像/精确一致性 + 溢出发散演示（运行时断言验证） *)
let () =
  match z2b_c4_runtime with
  | Pair (m, x) ->
    let mb = match m with True -> true | False -> false in
    let xb = match x with True -> true | False -> false in
    assert (mb && xb && mb = xb);
    (match z2b_overflow_demo with
     | Pair (mo, xo) ->
       let mob = match mo with True -> true | False -> false in
       let xob = match xo with True -> true | False -> false in
       assert (mob && not xob && mob <> xob);
       print_endline "Z2B_BENCH_ALL_OK")
