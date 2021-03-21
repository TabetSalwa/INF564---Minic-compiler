open X86_64
(* open Register *)
open Ops
open Format
exception Error of string

let visited = Hashtbl.create 17
type instr = Code of X86_64.text | Label of Label.t
let code = ref []
let emit l i = code := Code i :: Label l :: !code
let emit_wl i = code := Code i :: !code
let emit_only_l l = code := Label l :: !code
let labels = Hashtbl.create 17
let need_label l = if not (Hashtbl.mem labels l) then Hashtbl.add labels l ()

let registerq (r : Register.t) = match (r :> string) with
  | "%rax" -> X86_64.rax
  | "%rbx" -> X86_64.rbx
  | "%rcx" -> X86_64.rcx
  | "%rdx" -> X86_64.rdx
  | "%rdi" -> X86_64.rdi
  | "%rsi" -> X86_64.rsi
  | "%rbp" -> X86_64.rbp
  | "%rsp" -> X86_64.rsp
  | "%r8" -> X86_64.r8
  | "%r9" -> X86_64.r9
  | "%r10" -> X86_64.r10
  | "%r11" -> X86_64.r11
  | "%r12" -> X86_64.r12
  | "%r13" -> X86_64.r13
  | "%r14" -> X86_64.r14
  | "%r15" -> X86_64.r15
  | _ -> raise (Error ("cannot translate register"))

let registerb (r : Register.t) = match (r :> string) with
  | "%rax" -> X86_64.al
  | "%rbx" -> X86_64.bl
  | "%rcx" -> X86_64.cl
  | "%rdx" -> X86_64.dl
  | "%rdi" -> X86_64.dil
  | "%rsi" -> X86_64.sil
  | "%rbp" -> X86_64.bpl
  | "%rsp" -> X86_64.spl
  | "%r8" -> X86_64.r8b
  | "%r9" -> X86_64.r9b
  | "%r10" -> X86_64.r10b
  | "%r11" -> X86_64.r11b
  | "%r12" -> X86_64.r12b
  | "%r13" -> X86_64.r13b
  | "%r14" -> X86_64.r14b
  | "%r15" -> X86_64.r15b
  | _ -> raise (Error ("cannot translate register"))

let operandq = function
  | Ltltree.Reg (r) -> reg (registerq r)
  | Ltltree.Spilled (i) -> ind ~ofs:i X86_64.rbp

let operandb = function
  | Ltltree.Reg (r) -> reg (registerb r)
  | Ltltree.Spilled (i) -> ind ~ofs:i X86_64.rbp


let treat_unop unop op l= 
  match unop with 
  | Maddi (i32) ->  if Int32.to_int i32 == 1 
                    then begin
                      emit l (incq (operandq op))
                    end
                    else begin
                      if Int32.to_int i32 == -1 then begin
                        emit l (decq (operandq op))  
                      end
                      else begin
                      emit l (addq (imm32 i32) (operandq op))
                      end
                    end
  | Msetei (i32) -> emit l (cmpq (imm32 i32) (operandq op)) ; emit_wl (sete (operandb op))
  | Msetnei (i32) -> emit l (cmpq (imm32 i32) (operandq op)) ; emit_wl (setne (operandb op))


let convert_binop_2 = function
| Mmov -> movq
| Madd -> addq
| Msub -> subq
| Mmul -> imulq 
| _ -> raise (Error "convert binop 2 pas content")

let convert_binop_1 = function
| Msete -> sete
| Msetne -> setne
| Msetl -> setl
| Msetle -> setle
| Msetg -> setg
| Msetge -> setge
| _ -> raise (Error "convert binop 1 pas content")


let treat_binop binop op1 op2 l =
  match binop with  
  | Mmov 
  | Madd 
  | Msub 
  | Mmul -> emit l (convert_binop_2 binop (operandq op1) (operandq op2))
  | Mdiv -> emit l cqto; emit_wl (idivq (operandq op1)); 
  | _ -> begin match op2 with | Ltltree.Reg(reg2) -> emit l (cmpq (operandq op1) (operandq op2)); 
                                                     emit_wl (convert_binop_1 binop (reg r11b)); 
                                                     emit_wl (movzbq (reg r11b) (registerq reg2))
                              | Ltltree.Spilled (i) -> let pile = ind ~ofs:i X86_64.rbp in 
                                                       emit l (cmpq (operandq op1) (operandq op2)); 
                                                       emit_wl (convert_binop_1 binop (reg r11b));
                                                       emit_wl (movzbq (reg r11b) (registerq (Register.r11)));
                                                      emit_wl (movq (operandq (Ltltree.Reg(Register.r11))) pile)
    end

let bin_jmp_match = function
  | Mjl -> jl
  | Mjle -> jle


let bin_opposite_jmp_match = function
  | Mjl -> jle
  | Mjle -> jl 

let un_opposite_jmp_match = function
  | Mjz -> jnz
  | Mjnz -> jz
  (** inf or eq to const *)
  | Mjlei (i32) -> jg
  | Mjgi  (i32) -> jle 

let un_jmp_match = function
  | Mjz -> jz
  | Mjnz -> jnz
  (** inf or eq to const *)
  | Mjlei (i32) -> jle
  | Mjgi  (i32) -> jg 

let rec treat_mubranch mubranch (op : Ltltree.operand) (lb1 : Label.t) (lb2 : Label.t) g l =
  (match mubranch with 
  | Mjz 
  | Mjnz -> emit l (testq (operandq op) (operandq op))
  (** inf or eq to const *)
  | Mjlei (i32) 
  | Mjgi  (i32) -> emit l (cmpq (imm32 i32) (operandq op)));
  
  if not (Hashtbl.mem visited lb2) then begin
    need_label lb1;

    emit_wl ((un_jmp_match mubranch) (lb1 :> string));
    lin g lb2;
    lin g lb1
  end
  else begin
    need_label lb2;
    if not (Hashtbl.mem visited lb1) then begin
      emit_wl ((un_opposite_jmp_match mubranch) (lb2 :> string));
      lin g lb1;
    end
    else begin
      need_label lb1;

      emit_wl ((un_jmp_match mubranch) (lb1 :> string));
      emit_wl (jmp (lb2 :> string))
    end
  end





and treat_mbbranch mbbranch (op1 : Ltltree.operand) (op2 : Ltltree.operand) (lb1 : Label.t)  (lb2 : Label.t) g l = 
  emit l (cmpq (operandq op1) (operandq op2));
  
  if not (Hashtbl.mem visited lb2) then begin
    need_label lb1;

    emit_wl ((bin_jmp_match mbbranch) (lb1 :> string));
    lin g lb2;
    lin g lb1
  end
  else begin
    need_label lb2;
    if not (Hashtbl.mem visited lb1) then begin
      need_label lb1;
      emit_wl ((bin_opposite_jmp_match mbbranch) (lb2 :> string));
      lin g lb1;
    end
    else begin
      emit_wl ((bin_jmp_match mbbranch) (lb1 :> string));
      emit_wl (jmp (lb2 :> string))
    end
  end


and lin g l =
  if not (Hashtbl.mem visited l) then begin
    Hashtbl.add visited l ();
    instru g l (Label.M.find l g)
  end else begin
    need_label l;
    emit_wl (jmp (l :> string))
  end

and instru g l = function
  | Ltltree.Econst (n, op, lb) ->
      emit l (movq (imm32 n) (operandq op)); lin g lb
  | Ltltree.Egoto (lb) -> emit_only_l l ;lin g lb
  | Ltltree.Eload (op1 ,n , op2, lb) -> 
      emit l (movq (X86_64.ind ~ofs:n (registerq op1)) (reg (registerq op2))); lin g lb
  | Ltltree.Estore (op1, op2, n, lb) ->
      emit l (movq (reg (registerq op1)) (X86_64.ind ~ofs:n (registerq op2))); lin g lb
  | Ltltree.Ereturn -> emit l ret
  | Ltltree.Emunop (unop, op, lb) -> treat_unop unop op l; lin g lb
  | Ltltree.Embinop (binop, op1, op2, lb) -> treat_binop binop op1 op2 l; lin g lb 
  | Ltltree.Epush (op, lb) -> emit l (pushq (operandq(op))); lin g lb
  | Ltltree.Epop (op, lb) -> emit l (popq (registerq(op))); lin g lb
  | Ltltree.Emubranch (mubranch, op, lb1, lb2) -> treat_mubranch mubranch op lb1 lb2 g l 
  | Ltltree.Ecall (ident , lb) -> emit l (call ident); lin g lb
  | Ltltree.Embbranch (mbbranch, op1, op2, lb1, lb2) -> treat_mbbranch mbbranch op1 op2 lb1 lb2 g l 

let rec linearize = function
  | f::funlist -> emit_wl (label f.Ltltree.fun_name); lin f.Ltltree.fun_body f.Ltltree.fun_entry; linearize funlist
  | [] -> ()

let program p = 
  linearize p.Ltltree.funs; 
  let filter_instr asm1 instr =
    match instr with 
    | Code (cd) -> (++)  cd asm1
    | Label (lb) -> let (str_lb : string) = (lb :> string) in if Hashtbl.mem labels lb then (++) (label str_lb) asm1 else asm1
  in
  let text1 = List.fold_left filter_instr nop !code in
  {text = (++) (globl "main") text1; data = nop}
