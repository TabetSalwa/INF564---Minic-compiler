open Ertltree
open Format

type remaining_label_m = {mutable set : Label.set;}


let live_info_map = ref Label.M.empty
let live_table = Hashtbl.create 32



(*Comme d'habitude, on crée une instance presque vide que l'on mettra à jour*)
let create_live_info l i = 
  let successeurs = Ertltree.succ i in
  let defs, uses = Ertltree.def_use i in
  let my_live_info = {
    instr = i;
    succ = successeurs;    
    pred = Label.S.empty;
    defs = Register.set_of_list defs;    
    uses = Register.set_of_list uses;    
    ins = Register.S.empty; 
    outs = Register.S.empty; 
  } in
  Hashtbl.add live_table l my_live_info



let update_pred l my_live_info =
  let add_succ succl = 
    if Hashtbl.mem live_table succl then let one_succ = Hashtbl.find live_table succl in
    one_succ.pred <- Label.S.add l one_succ.pred
    else  fprintf std_formatter "%a isn't in livenessHatbl @\n"  Label.print succl;

  in
  if my_live_info.succ <> [] then List.iter add_succ my_live_info.succ












(* Fonctions nécessaires pour Kildall *)
let step_outs live_info = 
  let add_ins_of_succ label =
    let this_succ = Hashtbl.find live_table label in
    live_info.outs <- Register.S.union live_info.outs this_succ.ins 
  in
  List.iter add_ins_of_succ live_info.succ




let step_ins live_info = 
  let diff = Register.S.diff live_info.outs live_info.defs in 
  live_info.ins <- Register.S.union live_info.uses diff



 




 
let kildall () = 
  let remaining_labels = {set = Label.S.empty} in
  let fillSet label info = remaining_labels.set <- Label.S.add label remaining_labels.set
  in  
  Hashtbl.iter fillSet live_table;
  while (not (Label.S.is_empty remaining_labels.set))
  do 
    let l = Label.S.min_elt remaining_labels.set in
    remaining_labels.set <- Label.S.remove l remaining_labels.set;
    let my_live_info = Hashtbl.find live_table l in
    let old_ins = my_live_info.ins in
    step_outs (my_live_info);
    step_ins (my_live_info);
    if not (Register.S.equal old_ins my_live_info.ins) 
    then remaining_labels.set <- Label.S.union my_live_info.pred remaining_labels.set;
  done



let fill_the_map label my_live_info = 
  live_info_map := Label.M.add label my_live_info !live_info_map 



let liveness instrMap = 
  Label.M.iter create_live_info instrMap;
  Hashtbl.iter update_pred live_table;
  kildall ();
  Hashtbl.iter fill_the_map live_table;
  !live_info_map
