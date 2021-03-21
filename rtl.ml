open Rtltree
exception Error of string
   

let graph = ref Label.M.empty
let fun_table = Hashtbl.create 17

             

(* générateur de labels fraiches *)
let generate i =
    let l = Label.fresh () in
    graph := Label.M.add l i !graph;
    l                        
             

(* Fonction qui convertit les opérateur binaires de Ttree en Ops*)
let translate_binop = function
  | Ptree.Beq -> Ops.Msete
  | Ptree.Bneq -> Ops.Msetne
  | Ptree.Blt -> Ops.Msetl
  | Ptree.Ble -> Ops.Msetle
  | Ptree.Bgt -> Ops.Msetg
  | Ptree.Bge -> Ops.Msetge
  | Ptree.Badd -> Ops.Madd
  | Ptree.Bsub -> Ops.Msub
  | Ptree.Bmul -> Ops.Mmul
  | Ptree.Bdiv -> Ops.Mdiv
  | _ -> raise (Error "Non-simple binary operation given to translate")

let translate_int32 = function
  | Ptree.Badd -> Int32.add
  | Ptree.Bdiv -> Int32.div
  | Ptree.Bsub -> Int32.sub
  | Ptree.Bmul -> Int32.mul
  | _ -> raise (Error "This operation cannot be translated into an integer operation")



       

(* fonction qui traduit l'expression e, en lui donnant destr le registre de destination
 de la valeur de cette expression, et destl l'étiquette où il faut transférer ensuite
le controle 
il faut renvoyer un label, que l'on aura ajouté au graphe*)
let rec expr e locals destl destr =
  begin match e.Ttree.expr_node with
  | Ttree.Econst n -> generate (Econst (n, destr, destl))
  | Ttree.Eunop (op, e1) -> convert_unop op e1 locals destl destr
  | Ttree.Ebinop (op, e1, e2) -> convert_binop op e1 e2 locals destl destr
  | Ttree.Eaccess_local var_name -> begin try let var_r = Hashtbl.find locals var_name in
                                              generate (Embinop (Ops.Mmov, var_r, destr, destl))
                                          with Not_found -> raise (Error ("Variable "^var_name^" not found."))
                                    end
  | Ttree.Eassign_local (var_name, newe) -> begin try let var_r = Hashtbl.find locals var_name in
                                                     let calc_r = Register.fresh() in
                                                     let side_assignl = generate (Embinop (Ops.Mmov, calc_r, destr, destl)) in
                                                     let assignl = generate (Embinop (Ops.Mmov, calc_r, var_r, side_assignl)) in
                                                     expr newe locals assignl calc_r
                                                 with Not_found -> raise (Error ("Variable "^var_name^" not found."))
                                           end
  | Ttree.Ecall (fun_name, fun_args) -> convert_funcall fun_name fun_args locals destl destr
  | Ttree.Esizeof (s) -> generate (Econst ((Int32.of_int s.Ttree.str_totalSize), destr, destl))
  | Ttree.Eaccess_field (s_expr, field) -> let pos = field.Ttree.field_pos in
                                               let calcr = Register.fresh () in
                                               let accessl = generate (Eload (calcr, 8*pos, destr, destl)) in
                                               let calcl = expr s_expr locals accessl calcr in
                                               calcl
  | Ttree.Eassign_field (s_expr, field, assign_expr) -> let sr = Register.fresh() in
                                                        let assignr = Register.fresh() in
                                                        let pos = field.Ttree.field_pos in
                                                        let retl = generate (Embinop (Ops.Mmov, assignr, destr, destl)) in
                                                        let accessl = generate (Estore (assignr, sr, 8*pos, retl)) in
                                                        let calc_sl = expr s_expr locals accessl sr in
                                                        let calc_assignl = expr assign_expr locals calc_sl assignr in
                                                        calc_assignl
  end


(* Fonction qui convertit les expressions *)
and convert_if e true_block false_block locals locals_acc destl destr exitl =
  let newr = Register.fresh() in
  let truel = stmt true_block locals locals_acc destl destr exitl in
  let falsel = stmt false_block locals locals_acc destl destr exitl in
  let newl = generate (Emubranch (Ops.Mjnz, newr, truel, falsel)) in
  expr e locals newl newr

(* Fonction qui convertit les boucles while *)
and convert_while e true_block locals locals_acc destl destr exitl =
  let newr = Register.fresh() in
  let newl = Label.fresh() in
  let el = expr e locals newl newr in
  let blockl = stmt true_block locals locals_acc el destr exitl in
  let e_block = Emubranch (Ops.Mjnz, newr, blockl, destl) in
  graph := Label.M.add newl e_block !graph;
  el

(* Fonction qui convertit les opérateurs unaires *)
and convert_unop unop e locals destl destr =
  begin match unop with
  | Ptree.Uminus -> let er = Register.fresh() in
                    let substl = generate (Embinop (Ops.Msub, er, destr, destl)) in
                    let zerol = generate (Econst (Int32.zero, destr, substl)) in
                    expr e locals zerol er
  | Ptree.Unot -> let notl = generate (Emunop ((Ops.Msetei Int32.zero), destr, destl)) in
                  expr e locals notl destr
  end

(* Fonction qui convertit les opérateurs binaires *)
and convert_binop binop e1 e2 locals destl destr =
  let e1r = Register.fresh() in
  let e2r = Register.fresh() in
  begin match binop with
  | Ptree.Bmul -> let expr1 = e1.Ttree.expr_node in
                  let expr2 = e2.Ttree.expr_node in
                  begin match expr1, expr2 with
                  |Ttree.Econst 0l, _
                  |_, Ttree.Econst 0l -> generate (Econst (Int32.zero, destr, destl)) 
                  |Ttree.Econst 1l, _ -> expr e2 locals destl destr 
                  |_, Ttree.Econst 1l -> expr e1 locals destl destr
                  |_,_ -> let newl = generate (Embinop (Ops.Mmov, e1r, destr, destl)) in
                          let new_instr = generate (Embinop (Ops.Mmul, e2r, e1r, newl)) in
                          let e2l = expr e2 locals new_instr e2r in
                          expr e1 locals e2l e1r
                  end
  | (Ptree.Badd|Ptree.Bdiv|Ptree.Bsub|Ptree.Beq|Ptree.Bneq|Ptree.Bge|Ptree.Bgt|Ptree.Ble|Ptree.Blt) ->
     let rtl_binop = translate_binop binop in
     let newl = generate (Embinop (Ops.Mmov, e1r, destr, destl)) in
     let new_instr = generate (Embinop (rtl_binop, e2r, e1r, newl)) in
     let e2l = expr e2 locals new_instr e2r in
     expr e1 locals e2l e1r
  | Ptree.Band -> let new_e2l = generate (Embinop (Ops.Mmov, e2r, destr, destl)) in
                  let test_e2l = generate (Emunop (Ops.Msetnei (Int32.zero), e2r, new_e2l)) in
                  let calc_e2l = expr e2 locals test_e2l e2r in
                  let falsel = generate (Econst (Int32.zero, destr, destl)) in
                  let test_e1l = generate (Emubranch (Ops.Mjnz, e1r, calc_e2l, falsel)) in
                  let calc_e1l = expr e1 locals test_e1l e1r in
                  calc_e1l
  | Ptree.Bor -> let new_e2l = generate (Embinop (Ops.Mmov, e2r, destr, destl)) in
                 let test_e2l = generate (Emunop (Ops.Msetnei (Int32.zero), e2r, new_e2l)) in
                 let calc_e2l = expr e2 locals test_e2l e2r in
                 let truel = generate (Econst (Int32.one, destr, destl)) in
                 let test_e1l = generate (Emubranch (Ops.Mjz, e1r, calc_e2l, truel)) in
                 let calc_e1l = expr e1 locals test_e1l e1r in
                 calc_e1l
  end
  

(* Fonction qui s'occupe des appels de fonction*)  
and convert_funcall fun_name fun_args locals destl destr =
  let rec create_rlist n = 
    if n==0
    then []
    else Register.fresh() :: create_rlist (n-1)
  in
  let rec parse_formals expr_list formal_rlist exitl =
    match expr_list, formal_rlist with
    | e::etail, f::ftail -> 
      let newl = parse_formals etail ftail exitl in
      expr e locals newl f
    | [],[] -> exitl
    | _,_ -> raise (Error "Not enough or too many arguments given to the function")
  in
  let get_fun_info fun_ident =
    try let fun_descr,_,_ = Hashtbl.find fun_table fun_ident in (fun_ident,List.length fun_descr.fun_formals)
    with Not_found -> raise (Error ("Undefined function "^fun_ident))
  in
  let (fun_n, fun_formals_length) = get_fun_info fun_name in
  let fun_arg_rlist = create_rlist fun_formals_length in
  let funl = generate (Ecall (destr, fun_n, fun_arg_rlist, destl)) in
  let startl = parse_formals fun_args fun_arg_rlist funl in
  startl
  























(* fonction qui traduit le statement s, lui donnant destl l'étiquette où il faut transférer 
ensuite le contrôle 
*)
and stmt s locals locals_acc destl retr exitl =
  begin match s with
  | Ttree.Sreturn e -> expr e locals exitl retr
  | Ttree.Sskip -> (*destl*)
     generate (Egoto destl)
  | Ttree.Sexpr e -> expr e locals destl retr
  | Ttree.Sif (e, s1, s2) -> convert_if e s1 s2 locals locals_acc destl retr exitl
  | Ttree.Swhile (e, s1)  -> convert_while e s1 locals locals_acc destl retr exitl
  | Ttree.Sblock b -> convert_body b locals locals_acc destl retr exitl
  end


and convert_stmtlist s_list locals locals_acc destl retr exitl =
  begin match s_list with
  | s::[] -> let sl = stmt s locals locals_acc destl retr exitl in
             sl
  | s::s_tail -> let sl = stmt s locals locals_acc destl retr exitl in
                 convert_stmtlist s_tail locals locals_acc sl retr exitl
  | [] -> raise (Error "Empty body of statements")
  end

and convert_body b locals locals_acc destl retr exitl =
  let rec fill_locals = function
  | var::var_tail ->
     let newr = Register.fresh () in
     Hashtbl.add locals (snd var) (newr);
     Hashtbl.add locals_acc (snd var) (newr);
     fill_locals var_tail
  | [] -> () in
          
  let rec unfill_locals = function
  | var::var_tail -> Hashtbl.remove locals (snd var);
                     unfill_locals var_tail
  | [] -> () in
  
  let (var_list, s_list) = b in
  fill_locals var_list;
  let rev_s_list = List.rev s_list in
  let bl = convert_stmtlist rev_s_list locals locals_acc destl retr exitl in
  unfill_locals var_list;
  bl







       




         
                                                                       


(* Écrire enfin une fonction qui traduit un programme mini-C vers le type Rtltree.file,
 en traduisant chacune des fonctions. *)
  
let program p =
  let decl_fun_list = p.Ttree.funs in
  let add_formal locals locals2 formal =
    let (var_typ, var_ident) = formal in
    let newr = Register.fresh() in
    Hashtbl.add locals var_ident newr;
    Hashtbl.add locals2 var_ident newr;
    newr in
  let add_fun_table f =
    let locals = Hashtbl.create 17 in
    let locals_acc = Hashtbl.create 17 in
    let f_descr = {fun_name = f.Ttree.fun_name;
             fun_formals = List.map (add_formal locals locals_acc) f.Ttree.fun_formals;
             fun_result = Register.fresh();
             fun_locals = Register.set_of_list ([]);
             fun_entry = Label.fresh();
             fun_exit = Label.fresh();
             fun_body = !graph ;} in
    Hashtbl.add fun_table f.Ttree.fun_name (f_descr,locals,locals_acc)
  in List.iter add_fun_table decl_fun_list;   
     let locals = Hashtbl.create 17 in
     let locals_acc = Hashtbl.create 17 in
     let putchar_descr = {fun_name = "putchar";
                          fun_formals = List.map (add_formal locals locals_acc)  [(Ttree.Tint, "c")];
                          fun_result = Register.fresh();
                          fun_locals = Register.set_of_list ([]);
                          fun_entry = Label.fresh();
                          fun_exit = Label.fresh();
                          fun_body = !graph ;} in
     Hashtbl.add fun_table "putchar" (putchar_descr,locals,locals_acc);
     let locals = Hashtbl.create 17 in
     let locals_acc = Hashtbl.create 17 in
     let sbrk_descr = {fun_name = "sbrk";
                       fun_formals = List.map (add_formal locals locals_acc)  [(Ttree.Tint, "n")];
                       fun_result = Register.fresh();
                       fun_locals = Register.set_of_list ([]);
                       fun_entry = Label.fresh();
                       fun_exit = Label.fresh();
                       fun_body = !graph ;} in
     Hashtbl.add fun_table "sbrk" (sbrk_descr,locals,locals_acc);
  let extract_values table =
    Hashtbl.fold (fun key value val_list -> val_list@[value]) table [] in
  let update_descr f =
    let fdescr,locals,locals_acc = Hashtbl.find fun_table f.Ttree.fun_name in
    let f_exit = fdescr.fun_exit in
    let f_result = fdescr.fun_result in
    let f_entry = convert_body (f.Ttree.fun_body) locals locals_acc f_exit f_result f_exit in
    let f_rtl = {fun_name =  fdescr.fun_name;
                 fun_formals = fdescr.fun_formals;
                 fun_result = f_result;
                 fun_locals = Register.set_of_list (extract_values locals_acc);
                 fun_entry = f_entry;
                 fun_exit = f_exit;
                 fun_body = !graph ;} in
    Hashtbl.replace fun_table f.Ttree.fun_name (f_rtl,locals,locals_acc);
    f_rtl
  in
  {
    funs = List.map update_descr p.Ttree.funs;
  }
