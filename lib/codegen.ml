open Ast

(* Register aliases *)
let sp = "sp"
let fp = "s0"
let ra = "ra"
let a0 = "a0"
let t0 = "t0"
let t1 = "t1"

(* Unique label generator *)
let label_counter = ref 0
let new_label prefix =
  incr label_counter;
  prefix ^ string_of_int !label_counter

(* === FAST CONSTANT FOLDING === *)
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

(* === FAST PATTERN DETECTION === *)
(* Matrix pattern: a[i*N + j] or a[i][j] *)
let is_matrix_access = function
  | EBinOp (Add, EBinOp (Mul, EId _, _), EId _) -> true
  | ECall (_, [EId _; EId _]) -> true  (* 2D array access *)
  | _ -> false

(* Graph pattern: function names containing graph keywords *)
let is_graph_function fname =
  let lower = String.lowercase_ascii fname in
  String.contains lower 'd' && String.contains lower 'f' ||  (* dfs *)
  String.contains lower 'b' && String.contains lower 'f' ||  (* bfs *)
  String.contains lower 'v' && String.contains lower 'i' ||  (* visit *)
  String.contains lower 'g' && String.contains lower 'r'     (* graph *)

(* Loop induction variable: i = i + 1, i = i - 1 *)
let is_induction_var = function
  | SAssign (id, EBinOp (Add, EId var, EInt 1)) when var = id -> Some id
  | SAssign (id, EBinOp (Sub, EId var, EInt 1)) when var = id -> Some id
  | _ -> None

(* === OPTIMIZATION CONTEXT === *)
type opt_level = Basic | Matrix | Graph | NestedLoop

type env = {
  var_map: (id * int) list;
  current_offset: int;
  exit_label: string;
  break_label: string option;
  continue_label: string option;
  opt_level: opt_level;
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

(* === SMART EXPRESSION GENERATION === *)
let rec gen_expr env expr : string list =
  match eval_const_expr expr with
  | Some n -> [Printf.sprintf "  li %s, %d" t0 n]
  | None ->
      match expr with
      | EInt n -> [Printf.sprintf "  li %s, %d" t0 n]
      | EId id -> 
          let offset = find_var_offset id env in
          [Printf.sprintf "  lw %s, %d(%s)" t0 offset fp]
      | EUnOp (op, e) ->
          let e_code = gen_expr env e in
          e_code @ (match op with
          | Neg -> [Printf.sprintf "  neg %s, %s" t0 t0]
          | Not -> [Printf.sprintf "  seqz %s, %s" t0 t0])
      | EBinOp (op, e1, e2) ->
          gen_optimized_binop env op e1 e2
      | ECall (id, args) ->
          if is_graph_function id then
            gen_graph_call env id args
          else
            gen_standard_call env id args

(* === MATRIX & LOOP OPTIMIZED BINARY OPS === *)
and gen_optimized_binop env op e1 e2 =
  match op with
  | And -> gen_short_circuit_and env e1 e2
  | Or -> gen_short_circuit_or env e1 e2
  | _ ->
      (* Fast algebraic simplifications *)
      let e1_const = eval_const_expr e1 in
      let e2_const = eval_const_expr e2 in
      (match (op, e1_const, e2_const) with
      | Add, Some 0, _ -> gen_expr env e2
      | Add, _, Some 0 -> gen_expr env e1
      | Sub, _, Some 0 -> gen_expr env e1
      | Mul, Some 1, _ -> gen_expr env e2
      | Mul, _, Some 1 -> gen_expr env e1
      | Mul, Some 0, _ | Mul, _, Some 0 -> [Printf.sprintf "  li %s, 0" t0]
      | Div, _, Some 1 -> gen_expr env e1
      | Mul, _, Some n when is_power_of_two n -> 
          (gen_expr env e1) @ [Printf.sprintf "  slli %s, %s, %d" t0 t0 (log2 n)]
      | Div, _, Some n when is_power_of_two n -> 
          (gen_expr env e1) @ [Printf.sprintf "  srai %s, %s, %d" t0 t0 (log2 n)]
      | _ ->
          (* Matrix access optimization *)
          if env.opt_level = Matrix && is_matrix_access (EBinOp (op, e1, e2)) then
            gen_matrix_binop env op e1 e2
          else
            gen_standard_binop env op e1 e2
      )

(* Matrix-optimized binary operations *)
and gen_matrix_binop env op e1 e2 =
  let e1_code = gen_expr env e1 in
  let e2_code = gen_expr env e2 in
  (* For matrix index calculations, use direct register operations when possible *)
  match (e1, e2) with
  | (EBinOp (Mul, EId _, EInt n), EId _) when is_power_of_two n ->
      (* i*N + j where N is power of 2 -> use shift *)
      e1_code @ e2_code @ [
        Printf.sprintf "  mv %s, %s" t1 t0;
        Printf.sprintf "  slli %s, %s, %d" t0 t0 (log2 n);
        Printf.sprintf "  add %s, %s, %s" t0 t0 t1
      ]
  | _ ->
      e1_code
      @ [Printf.sprintf "  addi %s, %s, -4" sp sp; 
         Printf.sprintf "  sw %s, 0(%s)" t0 sp]
      @ e2_code
      @ [Printf.sprintf "  lw %s, 0(%s)" t1 sp; 
         Printf.sprintf "  addi %s, %s, 4" sp sp]
      @ (match op with
        | Add -> [Printf.sprintf "  add %s, %s, %s" t0 t1 t0]
        | Mul -> [Printf.sprintf "  mul %s, %s, %s" t0 t1 t0]
        | _ -> gen_binop_instruction op)

and gen_standard_binop env op e1 e2 =
  let e1_code = gen_expr env e1 in
  let e2_code = gen_expr env e2 in
  e1_code
  @ [Printf.sprintf "  addi %s, %s, -4" sp sp; 
     Printf.sprintf "  sw %s, 0(%s)" t0 sp]
  @ e2_code
  @ [Printf.sprintf "  lw %s, 0(%s)" t1 sp; 
     Printf.sprintf "  addi %s, %s, 4" sp sp]
  @ gen_binop_instruction op

and gen_binop_instruction op =
  match op with
  | Add -> [Printf.sprintf "  add %s, %s, %s" t0 t1 t0]
  | Sub -> [Printf.sprintf "  sub %s, %s, %s" t0 t1 t0]
  | Mul -> [Printf.sprintf "  mul %s, %s, %s" t0 t1 t0]
  | Div -> [Printf.sprintf "  div %s, %s, %s" t0 t1 t0]
  | Mod -> [Printf.sprintf "  rem %s, %s, %s" t0 t1 t0]
  | Eq  -> [Printf.sprintf "  sub %s, %s, %s" t0 t1 t0; 
           Printf.sprintf "  seqz %s, %s" t0 t0]
  | Neq -> [Printf.sprintf "  sub %s, %s, %s" t0 t1 t0; 
           Printf.sprintf "  snez %s, %s" t0 t0]
  | Lt  -> [Printf.sprintf "  slt %s, %s, %s" t0 t1 t0]
  | Le  -> [Printf.sprintf "  sgt %s, %s, %s" t0 t1 t0; 
           Printf.sprintf "  xori %s, %s, 1" t0 t0]
  | Gt  -> [Printf.sprintf "  sgt %s, %s, %s" t0 t1 t0]
  | Ge  -> [Printf.sprintf "  slt %s, %s, %s" t0 t1 t0; 
           Printf.sprintf "  xori %s, %s, 1" t0 t0]
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

(* === GRAPH OPTIMIZED FUNCTION CALLS === *)
and gen_graph_call env id args =
  (* Minimal register saves for graph traversal functions *)
  let save_regs = if env.loop_depth > 0 then ["t0"] else ["t0"; "t1"] in
  let save_space = List.length save_regs * 4 in
  
  let save_code = 
    if save_space > 0 then
      [Printf.sprintf "  addi %s, %s, -%d" sp sp save_space] @
      List.mapi (fun i reg -> 
        Printf.sprintf "  sw %s, %d(%s)" reg (i * 4) sp
      ) save_regs
    else [] in
  
  let arg_code = gen_args env args in
  let call_code = [Printf.sprintf "  call %s" id] in
  let cleanup_code = 
    let arg_space = 4 * List.length args in
    if arg_space > 0 then [Printf.sprintf "  addi %s, %s, %d" sp sp arg_space] else [] in
  
  let restore_code =
    if save_space > 0 then
      List.mapi (fun i reg -> 
        Printf.sprintf "  lw %s, %d(%s)" reg (i * 4) sp
      ) save_regs @
      [Printf.sprintf "  addi %s, %s, %d" sp sp save_space]
    else [] in
  
  save_code @ arg_code @ call_code @ cleanup_code @ restore_code @ 
  [Printf.sprintf "  mv %s, %s" t0 a0]

and gen_standard_call env id args =
  (* Reduced register saves compared to original *)
  let need_save_regs = ["t0"; "t1"] in
  let save_space = List.length need_save_regs * 4 in
  
  let save_regs_code = 
    [Printf.sprintf "  addi %s, %s, -%d" sp sp save_space] @
    List.mapi (fun i reg -> 
      Printf.sprintf "  sw %s, %d(%s)" reg (i * 4) sp
    ) need_save_regs in
  
  let arg_eval_code = gen_args env args in
  let arg_space = 4 * List.length args in
  let call_code = [Printf.sprintf "  call %s" id] in
  let cleanup_args_code = 
      if arg_space > 0 then [Printf.sprintf "  addi %s, %s, %d" sp sp arg_space] else [] in
  
  let restore_regs_code = 
    List.mapi (fun i reg -> 
      Printf.sprintf "  lw %s, %d(%s)" reg (i * 4) sp
    ) need_save_regs @
    [Printf.sprintf "  addi %s, %s, %d" sp sp save_space] in
  
  save_regs_code @ arg_eval_code @ call_code @ cleanup_args_code @ restore_regs_code @ 
  [Printf.sprintf "  mv %s, %s" t0 a0]

and gen_args env args =
  let reversed_args = List.rev args in
  List.fold_left (fun acc_code arg ->
      let current_arg_code = gen_expr env arg in
      let push_code = [
          Printf.sprintf "  addi %s, %s, -4" sp sp;
          Printf.sprintf "  sw %s, 0(%s)" t0 sp
        ] in
      acc_code @ current_arg_code @ push_code
    ) [] reversed_args

(* === OPTIMIZED STATEMENT GENERATION === *)
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
  | SWhile (cond, body) ->
      gen_optimized_while_loop env cond body
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

(* === LOOP OPTIMIZATION - FOCUS ON PERFORMANCE === *)
and gen_optimized_while_loop env cond body =
  let start_label = new_label "L_while_start" in
  let end_label = new_label "L_while_end" in
  
  (* Detect optimization patterns quickly *)
  let has_matrix = is_matrix_access cond in
  let has_induction = match body with
    | SBlock stmts -> List.exists (fun s -> is_induction_var s <> None) stmts
    | s -> is_induction_var s <> None in
  
  (* Choose optimization level *)
  let opt_level = 
    if env.loop_depth > 1 then NestedLoop
    else if has_matrix then Matrix
    else if has_induction then Basic
    else Basic in
  
  let loop_env = { 
    env with 
    break_label = Some end_label; 
    continue_label = Some start_label;
    opt_level = opt_level;
    loop_depth = env.loop_depth + 1;
  } in
  
  (* Generate efficient loop code *)
  [Printf.sprintf "%s:" start_label]
  @ (gen_expr env cond)
  @ [Printf.sprintf "  beqz %s, %s" t0 end_label]
  @ (gen_stmt loop_env body)
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

(* === FAST FUNCTION GENERATION === *)
let gen_func_def f : string list =
  let exit_label = new_label ("L_exit_" ^ f.name) in
  let num_locals = count_local_vars_stmt f.body in
  let locals_space = num_locals * 4 in
  
  (* Fast function analysis *)
  let is_graph_func = is_graph_function f.name in
  
  let base_env = {
    var_map = []; 
    current_offset = 0; 
    exit_label; 
    break_label = None; 
    continue_label = None;
    opt_level = if is_graph_func then Graph else Basic;
    loop_depth = 0;
  } in
  
  let env_with_params, _ = List.fold_left (fun (env, i) (PInt id) ->
    let param_offset = 8 + i * 4 in
    ({env with var_map = (id, param_offset) :: env.var_map}, i + 1)
  ) (base_env, 0) f.params in
  
  (* Build local variable environment *)
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

(* === FAST PEEPHOLE OPTIMIZATION === *)
let peephole_optimize (code: string list) : string list =
  let rec optimize_pass instrs =
    match instrs with
    (* Remove redundant sw/lw pairs *)
    | ins1 :: ins2 :: rest when (
        match (Scanf.sscanf_opt ins1 "  sw %s, %d(%s@)" (fun r1 n1 b1 -> (r1, n1, b1)),
               Scanf.sscanf_opt ins2 "  lw %s, %d(%s@)" (fun r2 n2 b2 -> (r2, n2, b2))) with
        | (Some (r1, n1, b1), Some (r2, n2, b2)) -> r1 = r2 && n1 = n2 && b1 = b2
        | _ -> false
      ) -> ins1 :: (optimize_pass rest)
    
    (* Remove useless mv instructions *)
    | ins :: rest when (
        match Scanf.sscanf_opt ins "  mv %s, %s@" (fun r1 r2 -> r1 = r2) with
        | Some true -> true
        | _ -> false
      ) -> optimize_pass rest
    
    (* Remove dead code after jumps *)
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
  optimize_pass code  (* Single pass for speed *)

(* Main generation function *)
let gen_comp_unit oc (CUnit funcs) =
  let unoptimized_code = [".text\n.global main"] @ List.concat_map gen_func_def funcs in
  let optimized_code = peephole_optimize unoptimized_code in
  List.iter (fun line -> Printf.fprintf oc "%s\n" line) optimized_code
