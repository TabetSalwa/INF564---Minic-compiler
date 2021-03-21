open Ttree

module Smap = Map.Make(String) (* Optimal pour la recherche, qui se fait par dichotomie *)

(* utiliser cette exception pour signaler une erreur de typage *)
exception Error of string * Ptree.loc

let ctx_struct = (Hashtbl.create 17 : (string, structure) Hashtbl.t)
let ctx_fun = (Hashtbl.create 17 : (string, typ * (typ * ident) list) Hashtbl.t)
let () = Hashtbl.add ctx_fun "putchar" (Tint, [(Tint, "c")])
let () = Hashtbl.add ctx_fun "sbrk" (Tvoidstar, [(Tint, "n")])
            
(* Printer for the errors *)
let string_of_type = function
  | Tint       -> "int"
  | Tstructp x -> "struct " ^ x.str_name ^ " *"
  | Tvoidstar  -> "void*"
  | Ttypenull  -> "typenull"





(* Converting the primitive types in Ptree into types of Ttree*)                
let convert_type = function
  | Ptree.Tint -> Tint
  | Ptree.Tstructp x -> try Tstructp (Hashtbl.find ctx_struct x.Ptree.id) with
                          Not_found -> raise (Error ("Structure "^x.Ptree.id^" not found. ",x.Ptree.id_loc))

let check_type t1 t2 =
  match t1,t2 with
  |Tint,Tint -> true
  |Tstructp x,Tstructp y -> x.str_name=y.str_name
  |Tvoidstar,Tvoidstar -> true
  |Tvoidstar,Tstructp _ -> true
  |Ttypenull,_ -> true
  |_ -> false



      
(* Main two functions that type expressions and statements, along with a function that checks if a function is well-typed (return type matches the type that it actually yields) *)                                     
let rec typing_expr ctx e =
  begin match e.Ptree.expr_node with
  | Ptree.Econst n -> {expr_node = Econst n;
                       expr_typ = if Int32.equal n Int32.zero then Ttypenull else Tint}
  | Ptree.Eright lv -> begin match lv with  
                       | Ptree.Lident id -> begin try let t = Smap.find (id.Ptree.id) ctx in
                                                      {expr_node = Eaccess_local id.Ptree.id;
                                                      expr_typ = t}
                                                  with Not_found -> raise (Error ("Variable "^id.Ptree.id^" not found. ", id.Ptree.id_loc))
                                            end
                       | Ptree.Larrow (expr,id) -> let expr_type = typing_expr ctx expr in
                                                   begin match expr_type.expr_typ with
                                                   | Tstructp s -> begin try let f = Hashtbl.find s.str_fields (id.Ptree.id) in
                                                                             {expr_node = Eaccess_field (expr_type , f );
                                                                              expr_typ = f.field_typ}
                                                                         with Not_found -> raise (Error ("This expression has type "^(string_of_type (Tstructp s))^". Structure "^s.str_name^
                                                                                                           " has no field named "^id.Ptree.id^". ", e.Ptree.expr_loc))
                                                                   end
                                                   | _ -> raise (Error ("This expression has type "^(string_of_type (expr_type.expr_typ))^". This type cannot have a field." , e.Ptree.expr_loc) ) 
                                                   end
                       end
  | Ptree.Eassign (lv,expr) -> let new_e = typing_expr ctx expr in
                               begin match lv with  
                               | Ptree.Lident id -> begin try let t = Smap.find (id.Ptree.id) ctx in
                                                              if check_type new_e.expr_typ t
                                                              then {expr_node = Eassign_local (id.Ptree.id, new_e);
                                                                    expr_typ = t}
                                                              else raise (Error ("Cannot assign value of type "^(string_of_type (new_e.expr_typ))^"to variable "^id.Ptree.id^" of type "^(string_of_type (t))^". ", e.Ptree.expr_loc ))
                                                          with Not_found -> raise (Error ("Variable "^id.Ptree.id^" not found. ", id.Ptree.id_loc))
                                                    end
                               | Ptree.Larrow (e1,id) -> let e1_expr = typing_expr ctx e1 in
                                                           begin match e1_expr.expr_typ with
                                                           | Tstructp s -> begin try let f = Hashtbl.find s.str_fields (id.Ptree.id) in
                                                                                     if check_type new_e.expr_typ f.field_typ
                                                                                     then {expr_node = Eassign_field (e1_expr, f, new_e);
                                                                                          expr_typ = f.field_typ}
                                                                                     else raise (Error ("Cannot assign value of type "^(string_of_type (new_e.expr_typ))^"to field "^s.str_name^"."^f.field_name^
                                                                                                          " of type "^(string_of_type (f.field_typ))^". ", e.Ptree.expr_loc))  
                                                                                 with Not_found -> raise (Error ("This expression has type "^(string_of_type (Tstructp s))^". Structure "^s.str_name^" has no field named "^
                                                                                                                   id.Ptree.id^". ", e.Ptree.expr_loc))
                                                                           end
                                                           | _ -> raise (Error ("This expression has type "^(string_of_type (e1_expr.expr_typ))^". This type cannot have a field." , e.Ptree.expr_loc) ) 
                                                           end
                               end
  | Ptree.Eunop (unop, expr) -> let e1 = typing_expr ctx expr in
                                begin match unop with
                                | Ptree.Uminus -> if check_type e1.expr_typ Tint
                                                  then {expr_node = Eunop (Ptree.Uminus , e1);
                                                        expr_typ = Tint}
                                                  else raise (Error ("Cannot compute the negative value of an expression of type "^(string_of_type (e1.expr_typ))^". ", e.Ptree.expr_loc))
                                | Ptree.Unot -> {expr_node = Eunop (Ptree.Unot, e1);
                                                 expr_typ = Tint}
                                end
  | Ptree.Ebinop (binop, expr1, expr2) -> let e1 = typing_expr ctx expr1 in
                                          let e2 = typing_expr ctx expr2 in
                                          begin match binop with
                                          | Ptree.Beq
                                          | Ptree.Bneq
                                          | Ptree.Bgt
                                          | Ptree.Bge
                                          | Ptree.Blt
                                          | Ptree.Ble-> if (check_type e1.expr_typ e2.expr_typ) || (check_type e2.expr_typ e1.expr_typ)
                                                        then {expr_node = Ebinop (binop, e1, e2);
                                                              expr_typ = Tint}
                                                        else raise (Error ("Cannot compare an expression of type "^(string_of_type (e1.expr_typ))^" with and expression of type "^(string_of_type (e2.expr_typ)), e.Ptree.expr_loc))
                                          | Ptree.Band
                                          | Ptree.Bor -> {expr_node = Ebinop (binop, e1, e2);
                                                          expr_typ = Tint}
                                          | Ptree.Badd
                                          | Ptree.Bsub
                                          | Ptree.Bmul
                                          | Ptree.Bdiv -> begin match e1.expr_typ, e2.expr_typ with
                                                          | Tint, Tint
                                                          | Tint, Ttypenull
                                                          | Ttypenull, Tint
                                                          | Ttypenull, Ttypenull -> {expr_node = Ebinop (binop, e1, e2);
                                                                                     expr_typ = Tint}
                                                          | _,_ -> raise (Error ( "Cannot perform arithmetic operations between an expression of type "^(string_of_type (e1.expr_typ))^" and an expression of type "^(string_of_type (e2.expr_typ) )^". " , e.Ptree.expr_loc))
                                                          end
                                          end
  | Ptree.Ecall (id, expr_list) ->  let (fun_return_type, fun_arg_list)  = try Hashtbl.find (ctx_fun) (id.Ptree.id)
                                                                           with Not_found -> raise (Error ("Function "^id.Ptree.id^" not found. " , e.Ptree.expr_loc)) in
                                    let expr_list_typed = List.map (fun exp -> typing_expr ctx exp) expr_list in
                                    begin try let is_ok = List.for_all2 (fun (e1_typ,_) e2 -> check_type e2.expr_typ e1_typ) fun_arg_list expr_list_typed in
                                              if is_ok
                                              then {expr_node = Ecall (id.Ptree.id, expr_list_typed);
                                                    expr_typ = fun_return_type}
                                              else raise (Error ("The arguments of the function "^id.Ptree.id^" are not well-typed. ", e.Ptree.expr_loc))
                                          with Invalid_argument _ -> raise (Error ("Not enough or too many arguments given to function "^id.Ptree.id^". " , e.Ptree.expr_loc))
                                    end
  | Ptree.Esizeof id -> begin try let s = Hashtbl.find ctx_struct id.Ptree.id in
                                  {expr_node = Esizeof s;
                                   expr_typ = Tint}
                              with Not_found -> raise ( Error ("Structure "^id.Ptree.id^" not found. " , e.Ptree.expr_loc))
                        end
  end

  

let rec typing_stmt tr ctx stmt =
  match stmt.Ptree.stmt_node with
  | Ptree.Sreturn e -> let expr = typing_expr ctx e in
                       if check_type expr.expr_typ tr then Sreturn expr
                       else raise (Error ("This expression has type "^(string_of_type expr.expr_typ)^". An expression of type "^(string_of_type tr)^" should be returned. ",e.Ptree.expr_loc))
  | Ptree.Sskip -> Sskip
  | Ptree.Sexpr e ->  let expr = typing_expr ctx e in
                      Sexpr expr
  | Ptree.Sif (e,stmt1,stmt2) -> let e = typing_expr ctx e in
                                 let stmt1 = typing_stmt tr ctx stmt1 in
                                 let stmt2 = typing_stmt tr ctx stmt2 in
                                 Sif (e,stmt1,stmt2)
  | Ptree.Swhile (e, stmt) -> let e = typing_expr ctx e in
                              let stmt = typing_stmt tr ctx stmt in
                              Swhile (e, stmt)
  | Ptree.Sblock b -> Sblock (typing_block tr ctx b)

and typing_block tr ctx (pvars,stmt) =
  let tvars = List.fold_left (fun l (t,id) -> if List.exists (fun (_,s) -> s = id.Ptree.id) l
                                              then raise ( Error ("The variable name "^id.Ptree.id^" is already assigned.", id.Ptree.id_loc))
                                              else (convert_type t,id.Ptree.id)::l) [] pvars in
  let ctx = List.fold_left (fun  ctx (t,id) -> Smap.add id t ctx) ctx tvars in
  (tvars,List.map (typing_stmt tr ctx) stmt)





(*  *)
let type_fun (f_name,f_return_typ,f_formals,f_body) =
  let ctx = List.fold_left (fun ctx (t,id) -> Smap.add id t ctx) Smap.empty f_formals in
  let body = typing_block f_return_typ ctx f_body in
  {fun_typ = f_return_typ; fun_name = f_name; fun_formals = f_formals; fun_body = body}

let program p =
  let decl_fun,decl_struct = List.fold_left
                             (fun (l1,l2) decl -> match decl with
                                                  | Ptree.Dfun d -> (d::l1,l2)
                                                  | Ptree.Dstruct d -> (l1,d::l2))
                             ([],[]) p
  in
  List.iter (fun (id,varlist) -> if Hashtbl.mem ctx_struct id.Ptree.id
                                 then raise (Error ("The structure "^id.Ptree.id^" is already defined",id.Ptree.id_loc))
                                 else Hashtbl.add ctx_struct id.Ptree.id 
                                        {str_name = id.Ptree.id;
                                         str_fields = (Hashtbl.create 17 : (ident,field) Hashtbl.t);
                                         str_totalSize = 8*(List.length varlist);}) decl_struct;
  let add_struct_ctx (id,vars) =
    let s = Hashtbl.find ctx_struct id.Ptree.id in
    List.iteri (fun i (t,x) -> if Hashtbl.mem s.str_fields x.Ptree.id
                                    then raise (Error ("The field "^x.Ptree.id^" is already in the structure "^s.str_name^".", x.Ptree.id_loc))
                               else Hashtbl.add s.str_fields x.Ptree.id {field_name = x.Ptree.id;
                                                                         field_typ = convert_type t;
                                                                         field_pos = i };) vars
  in List.iter add_struct_ctx decl_struct;
  let add_fun_ctx decl =
    let f_name = decl.Ptree.fun_name.Ptree.id in
    let f_return_typ = convert_type decl.Ptree.fun_typ in
    let f_formals = List.fold_left (fun l (t,id) -> if List.exists (fun (_,s) -> s = id.Ptree.id) l
                                                    then raise ( Error ("The parameter "^id.Ptree.id^" is already in function "^f_name^".",id.Ptree.id_loc))
                                                    else (convert_type t, id.Ptree.id)::l) [] decl.Ptree.fun_formals in
    let f_formals = List.rev f_formals in
    if Hashtbl.mem ctx_fun f_name
    then raise (Error ("The function "^f_name^" is already defined", decl.Ptree.fun_name.Ptree.id_loc))
    else Hashtbl.add ctx_fun f_name (f_return_typ, f_formals);
    (f_name,f_return_typ,f_formals,decl.Ptree.fun_body)
  in
  let decl_fun = List.map add_fun_ctx decl_fun in
  if List.exists (fun (f_name,_,_,_) -> f_name = "main") decl_fun
  then
    {
      funs = List.map type_fun decl_fun;
    }
  else raise (Error ("No main function.",(Lexing.dummy_pos,Lexing.dummy_pos)))
    
