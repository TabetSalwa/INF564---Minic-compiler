open Ltltree
open Ops

   
let add_friends reg1 reg2 interf_map =
  if Register.M.mem reg1 interf_map.map 
  then let arcR1 = Register.M.find reg1 interf_map.map in
    arcR1.prefs <- Register.S.add reg2 arcR1.prefs;
  else let prefs = Register.S.singleton reg2 in
    let newarcR1 = {prefs = prefs; intfs = Register.S.empty} in
    interf_map.map <- Register.M.add reg1 newarcR1 interf_map.map;

    if Register.M.mem reg2 interf_map.map 
    then let arcR2 = Register.M.find reg2 interf_map.map in
      arcR2.prefs <- Register.S.add reg1 arcR2.prefs;
    else let prefs = Register.S.singleton reg1 in
      let newarcR2 = {prefs = prefs; intfs = Register.S.empty} in
      interf_map.map <- Register.M.add reg2 newarcR2 interf_map.map


let iter_pref label live_info interf_map = 
  match live_info.Ertltree.instr with
  | Ertltree.Embinop (Mmov, reg1, reg2, l ) -> if reg1 <> reg2 then add_friends reg1 reg2 interf_map 
  | _ -> ()

let add_interfs reg1 reg2 interf_map =
  if Register.M.mem reg1 interf_map.map 
  then begin let arcR1 = Register.M.find reg1 interf_map.map in
    arcR1.intfs <- Register.S.add reg2 arcR1.intfs;
    if Register.S.mem reg2 arcR1.prefs then arcR1.prefs <- Register.S.remove reg2 arcR1.prefs
  end
  else begin let intfs = Register.S.singleton reg2 in
    let newarcR1 = {prefs = Register.S.empty; intfs = intfs} in
    interf_map.map <- Register.M.add reg1 newarcR1 interf_map.map
  end ;

  if Register.M.mem reg2 interf_map.map 
  then begin let arcR2 = Register.M.find reg2 interf_map.map in
    arcR2.intfs <- Register.S.add reg1 arcR2.intfs;
    if Register.S.mem reg1 arcR2.prefs then arcR2.prefs <- Register.S.remove reg1 arcR2.prefs
  end
  else begin let intfs = Register.S.singleton reg1 in
    let newarcR2 = {prefs = Register.S.empty; intfs = intfs} in
    interf_map.map <- Register.M.add reg2 newarcR2 interf_map.map
       end

  
let handle_interf live_info interf_map =
  if not (Register.S.is_empty live_info.Ertltree.defs) then
    Register.S.iter (fun reg_def -> Register.S.iter (fun reg_out -> if reg_out <> reg_def then add_interfs reg_out reg_def interf_map) live_info.Ertltree.outs) live_info.Ertltree.defs



let handle_interf_mov reg_friend live_info interf_map = 
  if not (Register.S.is_empty live_info.Ertltree.defs) then
    Register.S.iter (fun reg_out -> let reg_def = Register.S.choose live_info.Ertltree.defs in if reg_out <> reg_friend && reg_out <> reg_def then add_interfs reg_out reg_def interf_map) live_info.Ertltree.outs


let iter_interfs label live_info interf_map = 
  match live_info.Ertltree.instr with
  | Ertltree.Embinop (Mmov, reg1, reg2, l ) -> if reg1 <> reg2 then handle_interf_mov reg1 live_info interf_map 
  | _ -> handle_interf live_info interf_map



(**
*)
let construct_interference_graph live_info_map =
  let interference_map = {map = Register.M.empty} in
  Label.M.iter (fun label live_info -> iter_pref label live_info interference_map) live_info_map;
  Label.M.iter (fun label live_info -> iter_interfs label live_info interference_map) live_info_map;
  interference_map.map 
