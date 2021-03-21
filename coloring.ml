open Ltltree

type todo_set_m = {mutable set : Register.set}

let best_color_4 todo potential_colors_map interference =
  let prefers_4 register potential_colors = 
    if Register.S.is_empty potential_colors 
    then false 
    else true 

  in
  let filtered_potential_colors_map = Register.M.filter prefers_4 potential_colors_map in

  if not (Register.M.is_empty filtered_potential_colors_map) 
  then let (register_to_color, potential_colors)= Register.M.choose filtered_potential_colors_map in
      (true, register_to_color, Register.S.choose potential_colors)
  else (false, Register.fresh(), Register.fresh())


let best_color_3 todo potential_colors_map interference = 
  let prefers_3 register potential_colors = 
    if Register.S.is_empty potential_colors 
    then false 
    else begin
        let arcs_of_reg = Register.M.find register interference in
        let preference_inter_potential = Register.S.inter arcs_of_reg.prefs potential_colors in
        if Register.S.is_empty preference_inter_potential then begin false end 
        else true
      end 

  in

  let filtered_potential_colors_map = Register.M.filter prefers_3 potential_colors_map in

  if not (Register.M.is_empty filtered_potential_colors_map) 
  then 
    begin
      let (register_to_color, potential_colors)= Register.M.choose filtered_potential_colors_map in
      let arcs_of_reg = Register.M.find register_to_color interference in
      let preference_inter_potential = Register.S.inter arcs_of_reg.prefs potential_colors in
      (true, register_to_color, Register.S.choose preference_inter_potential)
    end
  else
    begin
      best_color_4 todo potential_colors_map interference
    end


let best_color_2 todo potential_colors_map interference = 
  let prefers_2 register potential_colors = 
    if Register.S.is_empty potential_colors || (Register.S.cardinal potential_colors) > 1 then  false 
    else true
  in

  let filtered_potential_colors_map = Register.M.filter prefers_2 potential_colors_map in

  if not (Register.M.is_empty filtered_potential_colors_map) 
  then 
    begin
      let (register_to_color, potential_colors)= Register.M.choose filtered_potential_colors_map in
      (true, register_to_color, Register.S.choose potential_colors)
    end
  else
    begin
      best_color_3 todo potential_colors_map interference
    end


let best_color_1 todo potential_colors_map interference =
  let filter_to_do register potential_colors = 
    if Register.S.mem register todo then true else false
  in
  let potential_colors_map_todo = Register.M.filter filter_to_do potential_colors_map in

  let prefers_1 register potential_colors = 
    if Register.S.is_empty potential_colors || (Register.S.cardinal potential_colors) > 1 then begin false end
    else 
      begin
        let only_potential_color = Register.S.choose potential_colors in
        let arcs_of_reg = Register.M.find register interference in
        if Register.S.mem only_potential_color arcs_of_reg.prefs then begin true end
        else begin false end
      end 
  in

  let filtered_potential_colors_map = Register.M.filter prefers_1 potential_colors_map_todo in

  if not (Register.M.is_empty filtered_potential_colors_map) 
  then 
    begin
      let (register_to_color, potential_colors)= Register.M.choose filtered_potential_colors_map in
      (true, register_to_color, Register.S.choose potential_colors)
    end
  else
    begin
      best_color_2 todo potential_colors_map_todo interference
    end


let remove_color potential_colors_map colored_register chosen_color interference = 

  let arcs_from_register = Register.M.find colored_register interference in
  let rec remove_color_rec interfered_registers potential_colors_map =
    if not (Register.S.is_empty interfered_registers) 
    then
      begin
        let reg = Register.S.choose interfered_registers in
        if not (Register.S.mem reg Register.allocatable) 
        then 
          begin
            let new_interfered_registers = Register.S.remove reg interfered_registers in
            let old_potential_colors = Register.M.find reg potential_colors_map in
            let new_potential_colors = Register.S.remove chosen_color old_potential_colors in 
            let new_potential_colors_map = Register.M.add  reg new_potential_colors potential_colors_map in
            remove_color_rec new_interfered_registers new_potential_colors_map
          end
        else
          begin
            let new_interfered_registers = Register.S.remove reg interfered_registers in
            remove_color_rec new_interfered_registers potential_colors_map
          end
      end
    else
      begin
        potential_colors_map
      end
  in
  remove_color_rec arcs_from_register.intfs potential_colors_map

let change_pref interference register_to_color new_color = 
  let iter register arcs =
    if Register.S.mem register_to_color arcs.prefs then 
      arcs.prefs <- Register.S.add new_color (Register.S.remove register_to_color arcs.prefs) 
  in
  Register.M.iter iter interference; interference

let rec color_1 interference todo potential_colors_map color_map nb_spill =
  if not (Register.S.is_empty todo) then 
    begin
      let (coloring_is_possible, register_to_color , new_color) = best_color_1 todo potential_colors_map interference in
      if coloring_is_possible then
        begin
          let new_color_map = Register.M.add register_to_color (Ltltree.Reg new_color) color_map in
          let new_interference_graph = change_pref interference register_to_color new_color in
          let new_todo = Register.S.remove register_to_color todo in
          let new_potential_colors_map = remove_color potential_colors_map register_to_color new_color new_interference_graph in
          color_1 new_interference_graph new_todo new_potential_colors_map new_color_map nb_spill
        end
      else 
        begin
          let register_to_spill = Register.S.choose todo in
          let new_color_map = Register.M.add register_to_spill (Ltltree.Spilled (- 8 - nb_spill * 8)) color_map in
          let new_todo = Register.S.remove register_to_spill todo in
          color_1 interference new_todo potential_colors_map new_color_map (nb_spill + 1)
        end
    end
  else
    begin
      (color_map, nb_spill)
    end



let color interference = 
  let todo = {set = Register.S.empty} in
  let fill_todo register arcs =
    if not (Register.S.mem register Register.allocatable) then
      todo.set <- Register.S.add register todo.set
  in
  Register.M.iter fill_todo interference;
  let potential_colors_map = {reg_map= Register.M.empty} 
  in
  let fill_potential_colors_map register arcs = 
    let potential_colors = Register.S.diff Register.allocatable arcs.intfs
    in potential_colors_map.reg_map <- Register.M.add register potential_colors potential_colors_map.reg_map 
  in
  Register.M.iter fill_potential_colors_map interference;
  let empty_color_map = Register.M.empty in
  let zero = 0 in
  color_1 interference todo.set potential_colors_map.reg_map empty_color_map zero
