open Ertltree
open Ops
open Register
open Liveness
exception Error of string

(* Comme dans le RTL, on crée un graphe *)
let graph = ref Label.M.empty

let generate i =
  let l = Label.fresh () in
  graph := Label.M.add l i !graph;
  l




  
(* On a un fichier du type Rtltree.file, qui est rempli de fonctions.
On s'occupe des istructions qui ne changent pas d'abord *)

let handle_div r1 r2 l =
  let l1 = generate (Embinop (Mmov, Register.rax, r2 , l)) in
  let l2 = generate (Embinop (Mdiv, r1, Register.rax, l1)) in
  Embinop (Mmov, r2, Register.rax, l2)

let handle_ecall destr fun_name rlist l =
  (* passer les arguments (liste rl) dans les registres donnée par la liste Register.parameters (avec Mmov)
et sur la pile s'il y en a trop (avec epush_param) *)
  let rec fill_reg rl i label =
    if i < 6 then 
      begin match rl with 
      | r::r_tail -> let newl = generate (Embinop (Mmov, r, (List.nth Register.parameters i), label)) in fill_reg r_tail (i+1) newl
      | [] -> label
      end
    else 
      begin match rl with 
    | r::r_tail -> let newl = generate (Epush_param (r, label)) in fill_reg r_tail (i+1) newl
    | [] -> label
      end in

  (* dépiler les arguments mis sur la pile, le cas échéant, avec une manipulation arithmétique de %rsp*)
  let lastl = if List.length rlist > 6
              then generate (Emunop (Maddi (Int32.of_int (((List.length rlist) - 6) * 8)), Register.rsp, l))
              else l in
  (* copier Register.result dans r*)
  let copyl = generate (Embinop(Mmov, Register.result, destr, lastl)) in
  (* n est le nombre d'arguments passés dans des registres*)
  let n = if List.length rlist <= 6
          then List.length rlist
          else 6 in
  (* effectuer l'appel avec l'instruction ERTL Ecall (f, n, ...) où n est le nombre d'arguments passés dans des registres*)
  let calll = generate (Ecall (fun_name, n, copyl)) in
  let secl = fill_reg rlist 0 calll in
  let goto = Egoto secl in
  goto


  
let instr = function
  | Rtltree.Econst (n, r, l) -> Econst (n, r, l)
  | Rtltree.Eload (r1, n, r2, l) -> Eload (r1, n, r2, l)
  | Rtltree.Estore (r1, r2, n, l) -> Estore (r1, r2, n, l)
  | Rtltree.Emunop  (m, r, l) -> Emunop (m, r, l)
  | Rtltree.Embinop (Mdiv, r1, r2, l) -> handle_div r1 r2 l
  | Rtltree.Embinop (m, r1, r2, l) -> Embinop (m, r1, r2, l)
  | Rtltree.Emubranch (m, r, l1, l2) -> Emubranch (m, r, l1, l2)
  | Rtltree.Embbranch (m, r1, r2, l1, l2) -> Embbranch (m, r1, r2, l1, l2)
  | Rtltree.Ecall (r, f, rl, l) -> handle_ecall r f rl l
  | Rtltree.Egoto (l) -> Egoto (l)

let handle_instr l i =
  let i = instr i in
  graph := Label.M.add l i !graph

let handle_body fun_body =
  Label.M.iter handle_instr fun_body


                       
let rec convert_fun f =
  handle_body f.Rtltree.fun_body;

  (* en entrée *)
(* récupérer les arguments dans les registres de la liste Register.parameters (avec Mmov) et sur la pile s'il y en a trop (avec Eget_param). *)
  let first_argl = get_args f.Rtltree.fun_formals  0 f.Rtltree.fun_entry in
  let saved_reg_table = Hashtbl.create 17 in
  (*sauvegarder les registres callee-saved (liste Register.callee_saved) dans des pseudo-registres frais ; *)
  let first_callee_savedl = save_reg (Register.callee_saved) first_argl saved_reg_table in
  (*allouer le tableau d'activation (instruction Ealloc_frame)*)
  let allocl = generate (Ealloc_frame first_callee_savedl) in

  
  (* en sortie *)
  let retl = generate (Ereturn) in
  let delete_framel = generate (Edelete_frame retl) in
  let first_restored_reg_l = restore_reg (Register.callee_saved) delete_framel saved_reg_table in
  let res = Embinop (Mmov, f.Rtltree.fun_result, Register.result, first_restored_reg_l) in
  graph := Label.M.add f.Rtltree.fun_exit res !graph;


  {fun_name = f.Rtltree.fun_name;
   fun_formals = List.length f.Rtltree.fun_formals;
   fun_locals = f.Rtltree.fun_locals;
   fun_entry = allocl;
   fun_body = !graph;
  }

and get_args fun_args c l =
  if c < 6
  then begin match fun_args with
       | r::r_tail -> let newl = generate (Embinop (Mmov, (List.nth Register.parameters c), r, l)) in
                      get_args r_tail (c+1) newl
       | [] -> l
       end
  else
      begin match fun_args with
      | r::r_tail -> let newl = generate (Eget_param ((c-6)*8 + 16, r, l)) in
                     get_args r_tail (c+1) newl
      | [] -> l
      end
  
and save_reg rl l saved_reg_table = 
  match rl with
  | r::tail -> let savedr = Register.fresh() in
               Hashtbl.add saved_reg_table r savedr;
               let newl = generate (Embinop (Mmov, r, savedr, l)) in
               save_reg tail newl saved_reg_table
  | [] -> l

and restore_reg rl l saved_reg_table = 
  match rl with
  | r::tail -> let savedr = Hashtbl.find saved_reg_table r in
               let newl = generate (Embinop (Mmov, savedr, r, l)) in
               restore_reg tail newl saved_reg_table
  | [] -> l
    




(* finally, the function program that handles the list of functions *)
let rec program p =
  let f_list = List.map convert_fun p.Rtltree.funs in
  let lm = liveness !graph in
  {
    funs = f_list;
    liveness = lm;
  }
                 
