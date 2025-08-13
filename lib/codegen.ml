open Ast

(* 寄存器别名 *)
let sp = "sp"
let fp = "s0"
let ra = "ra"
let a0 = "a0"
let t0 = "t0"
let t1 = "t1"
let t2 = "t2"
let t3 = "t3"

(* 唯一标签生成器 *)
let label_counter = ref 0
let new_label prefix =
  incr label_counter;
  prefix ^ string_of_int !label_counter

(* --- 优化 1: 常量折叠 --- *)
let rec eval_const_expr expr =
  match expr with
  | EInt n -> Some n
  | EUnOp (op, e) ->
      (match eval_const_expr e with
      | Some v ->
          (match op with
          | Neg -> Some (-v)
          | Not -> Some (if v = 0 then 1 else 0))
      | None -> None)
  | EBinOp (op, e1, e2) ->
      (match (eval_const_expr e1, eval_const_expr e2) with
      | (Some v1, Some v2) ->
          (try
            Some (match op with
            | Add -> v1 + v2 | Sub -> v1 - v2 | Mul -> v1 * v2
            | Div -> if v2 = 0 then raise Exit else v1 / v2
            | Mod -> if v2 = 0 then raise Exit else v1 mod v2
            | Eq  -> if v1 = v2 then 1 else 0 | Neq -> if v1 <> v2 then 1 else 0
            | Lt  -> if v1 < v2 then 1 else 0 | Le  -> if v1 <= v2 then 1 else 0
            | Gt  -> if v1 > v2 then 1 else 0 | Ge  -> if v1 >= v2 then 1 else 0
            | And -> if v1 <> 0 && v2 <> 0 then 1 else 0
            | Or  -> if v1 <> 0 || v2 <> 0 then 1 else 0)
          with Exit -> None)
      | _ -> None)
  | _ -> None

let is_power_of_two n = n > 0 && (n land (n - 1) = 0)
let log2 n =
  let rec find_log i = if 1 lsl i = n then i else find_log (i + 1) in
  find_log 0

(* --- 优化 2: 表达式分析 --- *)
type expr_complexity = Simple | Medium | Complex

let rec analyze_expr_complexity expr =
  match expr with
  | EInt _ | EId _ -> Simple
  | EUnOp (_, e) -> 
      (match analyze_expr_complexity e with
      | Simple -> Simple
      | _ -> Medium)
  | EBinOp (op, e1, e2) ->
      let c1 = analyze_expr_complexity e1 in
      let c2 = analyze_expr_complexity e2 in
      (match (op, c1, c2) with
      | (Add | Sub | Mul), Simple, Simple -> Simple
      | (Div | Mod), _, _ -> Medium
      | (And | Or), _, _ -> Medium
      | _ when c1 = Complex || c2 = Complex -> Complex
      | _ -> Medium)
  | ECall (_, args) ->
      if List.length args <= 2 then Medium else Complex

(* 代码生成环境 *)
type env = {
  var_map: (id * int) list;
  current_offset: int;
  exit_label: string;
  break_label: string option;
  continue_label: string option;
  (* 新增：循环优化信息 *)
  in_loop: bool;
  loop_depth: int;
}

let find_var_offset id env = 
  try List.assoc id env.var_map 
  with Not_found -> failwith ("Undeclared variable " ^ id)

let rec count_local_vars_stmt stmt =
  match stmt with
  | SDecl _ -> 1 
  | SBlock stmts -> List.fold_left (fun acc s -> acc + count_local_vars_stmt s) 0 stmts
  | SIf (_, s1, s2_opt) -> count_local_vars_stmt s1 + 
      (match s2_opt with Some s -> count_local_vars_stmt s | None -> 0)
  | SWhile (_, body) -> count_local_vars_stmt body 
  | _ -> 0

(* --- 优化 3: 智能寄存器使用 --- *)
let select_work_reg complexity in_loop =
  match (complexity, in_loop) with
  | (Simple, false) -> t0
  | (Simple, true) -> t0  (* 循环中保持简单 *)
  | (Medium, _) -> t0
  | (Complex, _) -> t0

(* --- 优化 4: 改进的表达式生成 --- *)
let rec gen_expr env expr : string list =
  let complexity = analyze_expr_complexity expr in
  let work_reg = select_work_reg complexity env.in_loop in
  
  match eval_const_expr expr with
  | Some n -> [Printf.sprintf "  li %s, %d" work_reg n]
  | None ->
      match expr with
      | EInt n -> [Printf.sprintf "  li %s, %d" work_reg n]
      | EId id -> 
          let offset = find_var_offset id env in 
          [Printf.sprintf "  lw %s, %d(%s)" work_reg offset fp]
      | EUnOp (op, e) ->
          let e_code = gen_expr env e in
          e_code @ (match op with
          | Neg -> [Printf.sprintf "  neg %s, %s" work_reg work_reg]
          | Not -> [Printf.sprintf "  seqz %s, %s" work_reg work_reg])
      | EBinOp (op, e1, e2) ->
          gen_binary_op env op e1 e2 complexity
      | ECall (id, args) ->
          gen_function_call env id args

(* --- 优化 5: 优化的二元运算生成 --- *)
and gen_binary_op env op e1 e2 complexity =
  match op with
  | And -> gen_short_circuit_and env e1 e2
  | Or -> gen_short_circuit_or env e1 e2
  | _ ->
      (* 代数化简 *)
      let e1_const = eval_const_expr e1 in
      let e2_const = eval_const_expr e2 in
      (match (op, e1, e2, e1_const, e2_const) with
      | Add, _, _, Some 0, _ -> gen_expr env e2
      | Add, _, _, _, Some 0 -> gen_expr env e1
      | Sub, _, _, _, Some 0 -> gen_expr env e1
      | Sub, e1, e2, _, _ when e1 = e2 -> [Printf.sprintf "  li %s, 0" t0]
      | Mul, _, _, Some 1, _ -> gen_expr env e2
      | Mul, _, _, _, Some 1 -> gen_expr env e1
      | Mul, _, _, Some 0, _ | Mul, _, _, _, Some 0 -> [Printf.sprintf "  li %s, 0" t0]
      | Div, _, _, _, Some 1 -> gen_expr env e1
      | Mul, _, _, _, Some n when is_power_of_two n -> 
          (gen_expr env e1) @ [Printf.sprintf "  slli %s, %s, %d" t0 t0 (log2 n)]
      | Div, _, _, _, Some n when is_power_of_two n -> 
          (gen_expr env e1) @ [Printf.sprintf "  srai %s, %s, %d" t0 t0 (log2 n)]
      | _ ->
          (* 优化简单表达式的寄存器使用 *)
          if complexity = Simple && not env.in_loop then
            gen_simple_binary_op env op e1 e2
          else
            gen_complex_binary_op env op e1 e2
      )

(* 简单二元操作：直接使用寄存器 *)
and gen_simple_binary_op env op e1 e2 =
  let e1_code = gen_expr env e1 in
  let e2_code = gen_expr env e2 in
  (* 对于简单表达式，第二个操作数可以直接使用t1 *)
  let e2_in_t1 = 
    if e2_code = [Printf.sprintf "  li %s, %d" t0 0] then
      [Printf.sprintf "  li %s, 0" t1]
    else if List.length e2_code = 1 then
      let modified_code = List.map (fun inst ->
        if String.contains inst 't' && String.contains inst '0' then
          Str.global_replace (Str.regexp "t0") "t1" inst
        else inst
      ) e2_code in
      modified_code
    else 
      e2_code @ [Printf.sprintf "  mv %s, %s" t1 t0]
  in
  e1_code @ e2_in_t1 @ (gen_binary_instruction op t0 t0 t1)

(* 复杂二元操作：使用栈 *)
and gen_complex_binary_op env op e1 e2 =
  let e1_code = gen_expr env e1 in
  let e2_code = gen_expr env e2 in
  e1_code
  @ [Printf.sprintf "  addi %s, %s, -4" sp sp; 
     Printf.sprintf "  sw %s, 0(%s)" t0 sp]
  @ e2_code
  @ [Printf.sprintf "  lw %s, 0(%s)" t1 sp; 
     Printf.sprintf "  addi %s, %s, 4" sp sp]
  @ (gen_binary_instruction op t0 t1 t0)

and gen_binary_instruction op dest src1 src2 =
  match op with
  | Add -> [Printf.sprintf "  add %s, %s, %s" dest src1 src2]
  | Sub -> [Printf.sprintf "  sub %s, %s, %s" dest src1 src2]
  | Mul -> [Printf.sprintf "  mul %s, %s, %s" dest src1 src2]
  | Div -> [Printf.sprintf "  div %s, %s, %s" dest src1 src2]
  | Mod -> [Printf.sprintf "  rem %s, %s, %s" dest src1 src2]
  | Eq  -> [Printf.sprintf "  sub %s, %s, %s" dest src1 src2; 
           Printf.sprintf "  seqz %s, %s" dest dest]
  | Neq -> [Printf.sprintf "  sub %s, %s, %s" dest src1 src2; 
           Printf.sprintf "  snez %s, %s" dest dest]
  | Lt  -> [Printf.sprintf "  slt %s, %s, %s" dest src1 src2]
  | Le  -> [Printf.sprintf "  sgt %s, %s, %s" dest src1 src2; 
           Printf.sprintf "  xori %s, %s, 1" dest dest]
  | Gt  -> [Printf.sprintf "  sgt %s, %s, %s" dest src1 src2]
  | Ge  -> [Printf.sprintf "  slt %s, %s, %s" dest src1 src2; 
           Printf.sprintf "  xori %s, %s, 1" dest dest]
  | _ -> []

and gen_short_circuit_and env e1 e2 =
  let false_label = new_label "L_and_false" in
  let end_label = new_label "L_and_end" in
  (gen_expr env e1)
  @ [Printf.sprintf "  beqz %s, %s" t0 false_label]
  @ (gen_expr env e2)
  @ [Printf.sprintf "  snez %s, %s" t0 t0;
     Printf.sprintf "  j %s" end_label;
     Printf.sprintf "%s:" false_label;
     Printf.sprintf "  li %s, 0" t0;
     Printf.sprintf "%s:" end_label]

and gen_short_circuit_or env e1 e2 =
  let true_label = new_label "L_or_true" in
  let end_label = new_label "L_or_end" in
  (gen_expr env e1)
  @ [Printf.sprintf "  bnez %s, %s" t0 true_label]
  @ (gen_expr env e2)
  @ [Printf.sprintf "  snez %s, %s" t0 t0;
     Printf.sprintf "  j %s" end_label;
     Printf.sprintf "%s:" true_label;
     Printf.sprintf "  li %s, 1" t0;
     Printf.sprintf "%s:" end_label]

(* --- 优化 6: 优化的函数调用 --- *)
and gen_function_call env id args =
  (* 根据参数数量选择不同的优化策略 *)
  if List.length args <= 4 then
    gen_optimized_call env id args
  else
    gen_standard_call env id args

and gen_optimized_call env id args =
  (* 对于少量参数的函数调用，减少寄存器保存开销 *)
  let caller_saved = if env.in_loop then ["t0"; "t1"] else ["t0"] in
  let save_space = List.length caller_saved * 4 in
  
  let save_code = 
    if save_space > 0 then
      [Printf.sprintf "  addi %s, %s, -%d" sp sp save_space] @
      List.mapi (fun i reg -> 
        Printf.sprintf "  sw %s, %d(%s)" reg (i * 4) sp
      ) caller_saved
    else [] in
  
  let arg_code = gen_args_optimized env args in
  let call_code = [Printf.sprintf "  call %s" id] in
  let cleanup_code = 
    let arg_space = 4 * List.length args in
    if arg_space > 0 then [Printf.sprintf "  addi %s, %s, %d" sp sp arg_space] else [] in
  
  let restore_code =
    if save_space > 0 then
      List.mapi (fun i reg -> 
        Printf.sprintf "  lw %s, %d(%s)" reg (i * 4) sp
      ) caller_saved @
      [Printf.sprintf "  addi %s, %s, %d" sp sp save_space]
    else [] in
  
  save_code @ arg_code @ call_code @ cleanup_code @ restore_code @ 
  [Printf.sprintf "  mv %s, %s" t0 a0]

and gen_standard_call env id args =
  (* 标准函数调用处理 *)
  let caller_saved = ["t0"; "t1"; "t2"; "t3"] in
  let save_space = List.length caller_saved * 4 in
  
  let save_code = 
    [Printf.sprintf "  addi %s, %s, -%d" sp sp save_space] @
    List.mapi (fun i reg -> 
      Printf.sprintf "  sw %s, %d(%s)" reg (i * 4) sp
    ) caller_saved in
  
  let arg_code = gen_args_standard env args in
  let call_code = [Printf.sprintf "  call %s" id] in
  let cleanup_code = 
    let arg_space = 4 * List.length args in
    [Printf.sprintf "  addi %s, %s, %d" sp sp arg_space] in
  
  let restore_code =
    List.mapi (fun i reg -> 
      Printf.sprintf "  lw %s, %d(%s)" reg (i * 4) sp
    ) caller_saved @
    [Printf.sprintf "  addi %s, %s, %d" sp sp save_space] in
  
  save_code @ arg_code @ call_code @ cleanup_code @ restore_code @ 
  [Printf.sprintf "  mv %s, %s" t0 a0]

and gen_args_optimized env args =
  (* 优化的参数生成：对简单参数直接生成 *)
  let reversed_args = List.rev args in
  List.fold_left (fun acc_code arg ->
    let arg_complexity = analyze_expr_complexity arg in
    let arg_code = 
      if arg_complexity = Simple then
        gen_expr env arg
      else
        gen_expr env arg
    in
    let push_code = [
        Printf.sprintf "  addi %s, %s, -4" sp sp;
        Printf.sprintf "  sw %s, 0(%s)" t0 sp
      ] in
    acc_code @ arg_code @ push_code
  ) [] reversed_args

and gen_args_standard env args =
  let reversed_args = List.rev args in
  List.fold_left (fun acc_code arg ->
    let arg_code = gen_expr env arg in
    let push_code = [
        Printf.sprintf "  addi %s, %s, -4" sp sp;
        Printf.sprintf "  sw %s, 0(%s)" t0 sp
      ] in
    acc_code @ arg_code @ push_code
  ) [] reversed_args

(* --- 优化 7: 循环优化的语句生成 --- *)
let rec gen_stmt env stmt : string list =
  match stmt with
  | SExpr e -> gen_expr env e
  | SReturn (Some e) -> 
      (gen_expr env e) @ 
      [Printf.sprintf "  mv %s, %s" a0 t0; Printf.sprintf "  j %s" env.exit_label]
  | SReturn None -> [Printf.sprintf "  j %s" env.exit_label]
  | SDecl (id, e) -> 
      let offset = find_var_offset id env in 
      (gen_expr env e) @ [Printf.sprintf "  sw %s, %d(%s)" t0 offset fp]
  | SAssign (id, e) -> 
      let offset = find_var_offset id env in 
      (gen_expr env e) @ [Printf.sprintf "  sw %s, %d(%s)" t0 offset fp]
  | SIf (cond, then_stmt, else_opt) ->
      gen_if_stmt env cond then_stmt else_opt
  | SWhile (cond, body) ->
      gen_while_loop env cond body
  | SBreak -> 
      (match env.break_label with 
       | Some l -> [Printf.sprintf "  j %s" l] 
       | None -> failwith "break outside loop")
  | SContinue -> 
      (match env.continue_label with 
       | Some l -> [Printf.sprintf "  j %s" l] 
       | None -> failwith "continue outside loop")
  | SBlock stmts ->
      gen_block env stmts

and gen_if_stmt env cond then_stmt else_opt =
  let else_label = new_label "L_else" in
  let end_label = new_label "L_if_end" in
  let cond_code = gen_expr env cond in
  (match else_opt with
  | Some else_stmt ->
      cond_code
      @ [Printf.sprintf "  beqz %s, %s" t0 else_label]
      @ (gen_stmt env then_stmt)
      @ [Printf.sprintf "  j %s" end_label]
      @ [Printf.sprintf "%s:" else_label]
      @ (gen_stmt env else_stmt)
      @ [Printf.sprintf "%s:" end_label]
  | None ->
      cond_code
      @ [Printf.sprintf "  beqz %s, %s" t0 end_label]
      @ (gen_stmt env then_stmt)
      @ [Printf.sprintf "%s:" end_label]
  )

(* --- 优化 8: 循环特别优化 --- *)
and gen_while_loop env cond body =
  let start_label = new_label "L_while_start" in
  let end_label = new_label "L_while_end" in
  let continue_label = new_label "L_while_continue" in
  
  (* 创建循环环境 *)
  let loop_env = { 
    env with 
    break_label = Some end_label; 
    continue_label = Some continue_label;
    in_loop = true;
    loop_depth = env.loop_depth + 1;
  } in
  
  (* 生成优化的循环代码 *)
  [Printf.sprintf "%s:" start_label]
  @ (gen_expr env cond)  (* 条件求值在循环外环境 *)
  @ [Printf.sprintf "  beqz %s, %s" t0 end_label]
  @ (gen_stmt loop_env body)
  @ [Printf.sprintf "%s:" continue_label]
  @ [Printf.sprintf "  j %s" start_label]
  @ [Printf.sprintf "%s:" end_label]

and gen_block env stmts =
  let locals_in_block = count_local_vars_stmt (SBlock stmts) in
  let block_space = locals_in_block * 4 in
  let block_env = 
    let new_offset = env.current_offset - block_space in
    let (updated_var_map, _) = List.fold_left (fun (map, off) s ->
      match s with
      | SDecl(id, _) -> let new_off = off - 4 in ((id, new_off) :: map, new_off)
      | _ -> (map, off)
    ) (env.var_map, env.current_offset) stmts in
    { env with var_map = updated_var_map; current_offset = new_offset } in
  let body_code = List.concat_map (gen_stmt block_env) stmts in
  (if block_space > 0 then [Printf.sprintf "  addi %s, %s, -%d" sp sp block_space] else [])
  @ body_code
  @ (if block_space > 0 then [Printf.sprintf "  addi %s, %s, %d" sp sp block_space] else [])

(* --- 辅助函数：分析语句是否包含函数调用 --- *)
and has_function_calls stmt =
  let rec has_calls_expr = function
    | ECall _ -> true
    | EBinOp (_, e1, e2) -> has_calls_expr e1 || has_calls_expr e2
    | EUnOp (_, e) -> has_calls_expr e
    | _ -> false
  in
  let rec has_calls_stmt = function
    | SExpr e -> has_calls_expr e
    | SReturn (Some e) -> has_calls_expr e
    | SDecl (_, e) -> has_calls_expr e
    | SAssign (_, e) -> has_calls_expr e
    | SIf (cond, s1, s2_opt) -> 
        has_calls_expr cond || has_calls_stmt s1 || 
        (match s2_opt with Some s2 -> has_calls_stmt s2 | None -> false)
    | SWhile (cond, body) -> has_calls_expr cond || has_calls_stmt body
    | SBlock stmts -> List.exists has_calls_stmt stmts
    | _ -> false
  in
  has_calls_stmt stmt

let gen_func_def f : string list =
  let exit_label = new_label ("L_exit_" ^ f.name) in
  let num_locals = count_local_vars_stmt f.body in
  let locals_space = num_locals * 4 in
  
  (* 构建初始环境 *)
  let base_env = {
    var_map = []; 
    current_offset = 0; 
    exit_label; 
    break_label = None; 
    continue_label = None;
    in_loop = false;
    loop_depth = 0;
  } in
  
  (* 构建参数环境 *)
  let env_with_params, _ = List.fold_left (fun (env, i) (PInt id) ->
    let param_offset = 8 + i * 4 in
    ({env with var_map = (id, param_offset) :: env.var_map}, i + 1)
  ) (base_env, 0) f.params in
  
  (* 递归构建局部变量环境 *)
  let rec build_env_for_locals current_offset stmts =
    List.fold_left (fun (env, offset) stmt ->
      match stmt with
      | SDecl (id, _) -> 
          let new_offset = offset - 4 in 
          ({ env with var_map = (id, new_offset) :: env.var_map }, new_offset)
      | SBlock block_stmts -> build_env_for_locals offset block_stmts
      | SIf (_, s1, s2o) ->
          let env', off' = build_env_for_locals offset [s1] in
          (match s2o with Some s2 -> build_env_for_locals off' [s2] | None -> (env', off'))
      | SWhile (_, s) -> build_env_for_locals offset [s] 
      | _ -> (env, offset)
    ) (env_with_params, current_offset) stmts in
    
  let final_env, _ = build_env_for_locals 0 (match f.body with SBlock stmts -> stmts | s -> [s]) in
  let body_code = gen_stmt final_env f.body in
  
  (* 生成函数代码 *)
  [Printf.sprintf "%s:" f.name]
  @ [Printf.sprintf "  addi %s, %s, -8" sp sp; 
     Printf.sprintf "  sw %s, 4(%s)" ra sp; 
     Printf.sprintf "  sw %s, 0(%s)" fp sp; 
     Printf.sprintf "  mv %s, %s" fp sp]
  @ (if locals_space > 0 then [Printf.sprintf "  addi %s, %s, -%d" sp sp locals_space] else [])
  @ body_code
  @ [Printf.sprintf "%s:" exit_label]
  @ [Printf.sprintf "  mv %s, %s" sp fp; 
     Printf.sprintf "  lw %s, 4(%s)" ra sp; 
     Printf.sprintf "  lw %s, 0(%s)" fp sp; 
     Printf.sprintf "  addi %s, %s, 8" sp sp; 
     Printf.sprintf "  ret\n"]

(* --- 优化 9: 高级窥孔优化 --- *)
let peephole_optimize (code: string list) : string list =
  let rec optimize_pass instrs =
    match instrs with
    (* 消除冗余的sw/lw对 *)
    | ins1 :: ins2 :: rest when (
        match (Scanf.sscanf_opt ins1 "  sw %s, %d(%s@)" (fun r1 n1 b1 -> (r1, n1, b1)),
               Scanf.sscanf_opt ins2 "  lw %s, %d(%s@)" (fun r2 n2 b2 -> (r2, n2, b2))) with
        | (Some (r1, n1, b1), Some (r2, n2, b2)) -> r1 = r2 && n1 = n2 && b1 = b2
        | _ -> false
      ) -> ins1 :: (optimize_pass rest)
    
    (* 优化连续的常数加载 *)
    | ins1 :: ins2 :: rest when (
        match (Scanf.sscanf_opt ins1 "  li %s, %d@" (fun r1 _n1 -> r1),
               Scanf.sscanf_opt ins2 "  li %s, %d@" (fun r2 _n2 -> r2)) with
        | (Some r1, Some r2) when r1 = r2 -> true
        | _ -> false
      ) -> ins2 :: (optimize_pass rest)
    
    (* 消除无用的mv指令 *)
    | ins :: rest when (
        match Scanf.sscanf_opt ins "  mv %s, %s@" (fun r1 r2 -> r1 = r2) with
        | Some true -> true
        | _ -> false
      ) -> optimize_pass rest
    
    (* 优化跳转到下一条指令 *)
    | ins1 :: ins2 :: rest when (
        match (Scanf.sscanf_opt ins1 "  j %s@" (fun label -> label),
               String.sub ins2 0 (min (String.length ins2) (String.length ins2 - 1))) with
        | (Some label, label2) when label = label2 -> true
        | _ -> false
      ) -> ins2 :: (optimize_pass rest)
    
    (* 移除跳转后的死代码 *)
    | ins1 :: rest when (String.starts_with ~prefix:"  j " ins1 || 
                         String.starts_with ~prefix:"  ret" ins1) ->
        let rec drop_unreachable remaining =
          match remaining with
          | [] -> []
          | l :: ls when String.ends_with ~suffix:":" l -> l :: ls
          | _ :: ls -> drop_unreachable ls
        in
        ins1 :: (optimize_pass (drop_unreachable rest))
    
    | ins :: rest -> ins :: (optimize_pass rest)
    | [] -> []
  in
  
  let rec optimize_until_converge prev_code =
    let next_code = optimize_pass prev_code in
    if next_code = prev_code then next_code
    else optimize_until_converge next_code
  in
  optimize_until_converge code

(* 主生成函数 *)
let gen_comp_unit oc (CUnit funcs) =
  let unoptimized_code = [".text\n.global main"] @ List.concat_map gen_func_def funcs in
  let optimized_code = peephole_optimize unoptimized_code in
  List.iter (fun line -> Printf.fprintf oc "%s\n" line) optimized_code
