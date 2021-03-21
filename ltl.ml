open Ltltree
open Ops
open Register
open Format
open Coloring
open Interference
exception Error of string



type color = Ltltree.operand
type coloring = color Register.map

(* Fonctions utiles pour les graphes *)
let graph = ref Label.M.empty

let generate i =
  let l = Label.fresh () in
  graph := Label.M.add l i !graph;
  l

let print_graph igraph =
  Register.M.iter (fun r arcs ->
      Format.printf "%s: prefs=@[%a@] intfs=@[%a@]@." (r :> string)
        Register.print_set arcs.prefs Register.print_set arcs.intfs) igraph


(* Fonctions utiles pour les couleurs *)
let lookup color_map r =
  if Register.is_hw r
  then Reg r
  else M.find r color_map

let color_matches_hw colors operand =
  match operand with
  | Reg (reg) -> true
  | Spilled (i) -> false

let print_color fmt = function
  | Reg hr    -> fprintf fmt "%a" Register.print hr
  | Spilled n -> fprintf fmt "stack %d" n

let print_color_graph cm =
  Register.M.iter
    (fun r cr -> printf "%a -> %a@\n" Register.print r print_color cr) cm

                 


  

(* On convertit, comme on l'a fait auparavant, les items Ertl en items Ltl *)
let convert_binop colors binop r1 r2 l= 
  let op1 = lookup colors r1 in
  let op2 = lookup colors r2 in
  match binop with
  | Mmov when op1 = op2 -> Egoto l
  | Mmov when not (color_matches_hw colors op1)
           && not (color_matches_hw colors op2) -> let newr = Register.tmp1 in
                                                   let mov2_l= generate(Embinop (Mmov, Reg(newr), op2, l)) in
                                                   Embinop (Mmov, op1 , Reg(newr), mov2_l)
  | Mmov -> Embinop (Mmov, op1, op2, l)
  | Mmul when not (color_matches_hw colors op2) -> let newr = Register.tmp1 in
                                                   let last_move_l= generate (Embinop (Mmov, Reg(newr), op2, l)) in
                                                   let mult_l= generate (Embinop (Mmul, op1, Reg(newr), last_move_l)) in
                                                   Embinop (Mmov, op2,  Reg(newr) , mult_l)
  | _ when not (color_matches_hw colors op1)
        && not (color_matches_hw colors op2) -> let newr = Register.tmp1 in
                                                let last_move_l= generate (Embinop (Mmov, Reg(newr) , op2 , l)) in
                                                let binop_l= generate (Embinop (binop, op1, Reg(newr), last_move_l)) in
                                                Embinop (Mmov, op2 ,Reg(newr) , binop_l)
  | _ -> Embinop (binop, op1, op2, l)





       
let convert_load colors srcr src_pos destr l = 
  let dest_op = lookup colors destr in
  let src_op = lookup colors srcr in
  let post_l, dest_reg = match dest_op with
    | Reg r -> l, r
    | Spilled i -> let dest_ops = Reg (Register.tmp1) in
                   let postcopy_l= generate (Embinop (Ops.Mmov, dest_ops, dest_op, l)) in
                   (postcopy_l, Register.tmp1)
  in
  let pre_instr = match src_op with 
    | Reg r -> let load_instr = Eload (r, src_pos, dest_reg, post_l) in
               load_instr
    | Spilled i -> let newr = Register.tmp2 in
                   let src_op = Reg (newr) in
                   let load_l= generate(Eload(newr, src_pos, dest_reg, post_l)) in
                   let precopy_instr = Embinop (Ops.Mmov, src_op, src_op, load_l) in
                   precopy_instr
  in 
  pre_instr


  
let convert_store colors srcr destr dest_pos l = 
  let dest_op = lookup colors destr in
  let src_op = lookup colors srcr in
  let post_l, dest_reg = match dest_op with
    | Reg (r) -> l, r
    | Spilled (i) -> let dest_ops = Reg (Register.tmp1) in
                     let postcopy_l= generate (Embinop (Ops.Mmov, dest_ops, dest_op, l)) in
                     (postcopy_l, Register.tmp1)
  in
  let pre_instr = match src_op with 
    | Reg (r) -> let load_instr = Estore (r, dest_reg, dest_pos, post_l) in
                 load_instr
    | Spilled (i) -> let newr = Register.tmp2 in
                     let src_op = Reg (newr) in
                     let load_l= generate(Estore(newr, dest_reg, dest_pos, post_l)) in
                     let precopy_instr = Embinop (Ops.Mmov, src_op, src_op, load_l) in
                     precopy_instr
  in 
  pre_instr





  

(* Fonction qui traduit une instruction de l'arbre de Ertl en Arbre de Ltl *)
let instr colors nb_spilled i = match i with 
  | Ertltree.Econst(n, r, l) -> Econst (n, lookup colors r, l)
  | Ertltree.Ereturn -> Ereturn
  | Ertltree.Egoto (l)-> Egoto l
  | Ertltree.Ecall (ident, nR, l) -> Ecall (ident, l)
  | Ertltree.Emunop (unop, r, l) -> Emunop (unop, (lookup colors r), l) 
  | Ertltree.Emubranch (branch, r, l1, l2) -> Emubranch (branch, (lookup colors r), l1, l2)
  | Ertltree.Embbranch (branch, r1, r2, l1, l2) -> let op1 = lookup colors r1 in
                                                   let op2 = lookup colors r2 in
                                                   Embbranch (branch, op1, op2, l1, l2)
  | Ertltree.Embinop (binop, r1, r2, l) -> convert_binop colors binop r1 r2 l
  | Ertltree.Eload (srcr, src_pos, destr, l) -> convert_load colors srcr src_pos  destr l
  | Ertltree.Estore (srcr, destr, dest_pos, l) -> convert_store colors srcr destr dest_pos l
  | Ertltree.Epush_param (r, l) -> Epush ((lookup colors r), l)
  | Ertltree.Ealloc_frame (l)-> let last_l = if nb_spilled <> 0
                                             then generate (Emunop(Maddi (Int32.of_int(- 8 * nb_spilled)), Reg(Register.rsp), l))
                                             else l in
                                let second_l = generate (Embinop(Mmov, Reg(Register.rsp), Reg(Register.rbp), last_l)) in
                                Epush (Reg (Register.rbp), second_l)
  | Ertltree.Edelete_frame (l) -> let label = generate (Epop (Register.rbp, l)) in
                                  Embinop(Mmov, Reg(Register.rbp), Reg(Register.rsp), label)
  | Ertltree.Eget_param (n, r, l) -> let op = lookup colors r in
                                     if not (color_matches_hw colors op)
                                     then let newr = Register.tmp1 in
                                          let last_move_l = generate (Embinop (Mmov, Reg(newr), op, l)) in
                                          Embinop (Mmov, Spilled(n) , Reg(newr), last_move_l)
                                     else Embinop(Mmov, Spilled(n), op , l)



let handle_instr_l colors nb_spilled l i = 
  let i = instr colors nb_spilled i in
  graph := Label.M.add l i !graph

let ltl_body colors nb_spilled b = 
  Label.M.iter (handle_instr_l colors nb_spilled) b

let ltl_fun colors nb_spilled f = 
  let () = ltl_body colors nb_spilled f.Ertltree.fun_body in
  {
    fun_name = f.Ertltree.fun_name;
    fun_entry = f.Ertltree.fun_entry;
    fun_body = !graph;
  }


let program p = 
  let final_interference_graph = construct_interference_graph p.Ertltree.liveness in
  let (colors, nb_spilled) = color final_interference_graph in
  let funlist = List.map (ltl_fun colors nb_spilled) p.Ertltree.funs in
  {
    funs = funlist;
  }
