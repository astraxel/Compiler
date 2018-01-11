open Tast
open Format
open X86_64

(* Première partie : travail préliminaire sur les structures *)

type adress = int*size register option*int*size register

let att_pos = Hashtbl.create 16

let struct_size = Hashtbl.create 16


let get_size = function
  |Tbool |Tint |Tref _ -> 8
  |Tvec _ -> 16
  |Tstruct s ->
    begin
      try (Hashtbl.find struct_size s)
      with Not_found -> failwith "Mauvais typage : structure inconnue"
    end
  |Tunit -> 0
          
let compute_att_position data next att =
  Hashtbl.add data (fst att) next;
  next - (get_size (snd att))
  
           

let compute_attributes_positions (s:tdecl_struct) =
  let data_struct = Hashtbl.create 2 in
  let rec aux next = function
    |[] -> next
    |a::q -> aux (compute_att_position data_struct next a) q
  in
  Hashtbl.add struct_size s.name (aux 0 s.attributes);
  Hashtbl.add att_pos s.name data_struct
        

let rec compute_all_attributes_positions = function
  |[] -> ()
  |(TDdecl_fun f)::q -> compute_all_attributes_positions q
  |(TDdecl_struct s)::q ->compute_attributes_positions s;    
                          compute_all_attributes_positions q
                              
                           
(* Deuxième partie  a : Calcul des positions des arguments/résultats *)

                          
let arg_corres = Hashtbl.create 16 (*Contient une liste des ident des arguments, dans l'ordre*)

let res_pos = Hashtbl.create 16
(*Also gives the size of the data that must be allocated before calling*)
            
let local_pos = Hashtbl.create 16

let compute_arg_position data next arg=
  let (_,id,t)=arg in
  let new_next = next + (get_size t) in
  Hashtbl.add data id new_next;
  new_next
  

let compute_res_pos next t =
  next + get_size(t)

let rec get_corres = function
  |[] -> []
  |(_,id,_)::q -> id::(get_corres q)

let compute_arguments_positions (f:tdecl_fun) =
  let data_fun = Hashtbl.create 2 in
  let rec aux next = function
    |[] -> next
    |arg::q -> aux (compute_arg_position data_fun next arg) q
  in
  Hashtbl.add res_pos f.name (compute_res_pos (aux 8 f.arguments) f.typ);
  Hashtbl.add local_pos f.name data_fun;
  Hashtbl.add arg_corres f.name (get_corres f.arguments)


let rec compute_all_arguments_positions = function
  |[] -> ()
  |(TDdecl_struct s)::q -> compute_all_arguments_positions q
  |(TDdecl_fun f)::q -> compute_arguments_positions f; compute_all_arguments_positions q



(*Deuxième partie b : Calcul des positions des variables locales*)

                        

let rec compute_locals_expr locals next expr =
  let e,t = expr in
  match e with
  |TEint n  ->
    next
  |TEbool b ->
    next
  |TEident i ->
    assert (Hashtbl.mem locals i); next
  |TEbinop (e1,b,e2) ->
    let dec_e1 = if b=Affect then (-8) else 0 in
    (*Quand on affect, on sauvegarde le registre r8 (adresse de l'id) avant de calculer e1*)
    let _ = compute_locals_expr locals (next+dec_e1) e1
    and _ = compute_locals_expr locals (next-8) e2
    in next 
  |TEunop (u,e) ->
    let _ = compute_locals_expr locals next e in next
  |TEattribute (e,id) ->
    let _ = compute_locals_expr locals next e in next
  |TElen e ->
    let _ = compute_locals_expr locals next e in next
  |TEselect (e1,e2) ->
    let _ = compute_locals_expr locals next e1
    and _ = compute_locals_expr locals next e2
    in next
  |TEcall (f,args) ->
    let args_size = Hashtbl.find res_pos f in
    (*On va calculer chaque arguments à la position où il sera dans la champs.
     Attention, il faudra calculer en premier ceux à la fin de la liste (qui sont le plus profond dans la pile)*)
    let l_arg_corres = (Hashtbl.find arg_corres f) in
    let locals_f = Hashtbl.find local_pos f in
    List.iter2 (fun e id ->
        let arg_ofs = Hashtbl.find locals_f id in
        let _ =compute_locals_expr locals (next-args_size+arg_ofs) e in ())
               args l_arg_corres;
    next
  |TEvect l ->
    List.iter (fun e -> let _ =compute_locals_expr locals next e in ()) l;
    next
  |TEprint s ->
    next
  |TEbloc b ->
    let _ = compute_locals_bloc locals next b in next
(* On doit stocker l'adresse du résultat dans un registre
 -> si c'est une struct, que l'accès aux champs est autorisé,
 sinon taille constante -> stockable dans un registre*)
  
and compute_locals_if locals next = function
  |TAif (e,b) ->
    let _ = compute_locals_expr locals next e
    and _ = compute_locals_bloc locals next b in next
  |TBif (e,b1,b2) ->
    let _ = compute_locals_expr locals next e
    and _ = compute_locals_bloc locals next b1
    and _ = compute_locals_bloc locals next b2 in next
  |TIif (e,b,i) ->
    let _ = compute_locals_expr locals next e
    and _ = compute_locals_bloc locals next b
    and _ = compute_locals_if locals next i in next
                                  
and compute_locals_stmt locals next stmt= match stmt with
  |TSUnit -> next
  |TSexpr e ->
    let _ = compute_locals_expr locals next e in next
  |TSwhile (e,b) ->
    let new_next = compute_locals_expr locals next e in
    let _ = compute_locals_bloc locals new_next b in
    next
  |TSreturn r ->
    begin
      match r with
      |None -> next
      |Some e -> let _ = compute_locals_expr locals next e in next
    end
  |TSif i ->
    let _ = compute_locals_if locals next i in next
  |TSaff (_,id,e) ->
    if Hashtbl.mem locals id then
      let _ = compute_locals_expr locals next e in next
    else
      begin
        Hashtbl.add locals id next;
        let s = get_size (snd e) in
        let _ = compute_locals_expr locals next e in
        next - s
      end
  |TSobj (_,id,structure,attributes) ->
    let structure_size = Hashtbl.find struct_size structure in
    List.iter (fun (i,e) -> let _ =compute_locals_expr locals (next-structure_size) e in ()) attributes;
    next+structure_size
(*Affectation d'une structure -> calculs effectués APRES la place réservée à la structure
 => stocker une addresse de début de structure à la création*)  
                 
and compute_locals_stmt_list locals next = function
  |[] -> next
  |stmt::q ->
    let new_next = compute_locals_stmt locals next stmt in
    compute_locals_stmt_list locals new_next q

and compute_locals_bloc locals next b=
  let _ =
    begin
      match b with
      |TUbloc l_stmt -> compute_locals_stmt_list locals next l_stmt
      |TVbloc (l_stmt,e) -> let new_next =  compute_locals_stmt_list locals next l_stmt in
                            compute_locals_expr locals new_next e
    end
  in next
                             
let compute_locals_positions f=
  let locals = Hashtbl.find local_pos f.name in
  let _ = compute_locals_bloc locals (-8) f.body in ()
  
              
let rec compute_all_locals_positions = function
  |[] -> ()
  |(TDdecl_struct s)::q -> compute_all_locals_positions q
  |(TDdecl_fun f)::q -> compute_locals_positions f; compute_all_locals_positions q



(*Partie 2 c : Production de code x86-64*)

let data_code = ref nop

let popn n = addq (imm n) (reg rsp)
let pushn n = subq (imm n) (reg rsp)

let rec write_bloc_code f = function
  |TUbloc b ->
    let code, size = write_stmt_list_code f b in
    comment "bloc" ++ code ++ popn size
  |TVbloc (b,e) -> let code, size = write_stmt_list_code f b in
                   let size_e = get_size (snd e) in
                   let add_or = size_e-8, None, 0, rsp
                   and add_target = (size +size_e -8), None, 0, rsp in
                   comment "bloc" ++ code ++ write_expr_code false f e ++ (copy_value size_e add_or add_target) ++ popn size

and write_stmt_list_code f = function
  |[] -> nop, 0
  |s::q -> let code, alloc_size = write_stmt_code f s in
           let codeq, alloc_sizeq =  write_stmt_list_code f q in
           code ++ codeq , alloc_size + alloc_sizeq   

and write_stmt_code f = function
  |TSUnit -> comment "unit", 0
  |TSexpr e ->
    let s = get_size (snd e) in
    comment "Sexpr" ++ write_expr_code false f e ++ popn s, 0
  |TSaff (_,_,expr) ->
    let size = get_size (snd expr) in
    comment "Saff" ++ write_expr_code false f expr, size (*En théorie, on se situe à la position du début de l'affectation*)
  |TSobj (_,_,structure,attributes) ->
    let size = Hashtbl.find struct_size structure in
    let positions = Hashtbl.find att_pos structure in
    let compute_att a=
      let id,e = a in
      let ofs = Hashtbl.find positions id in
      let s_a = get_size (snd e) in
      let add_or = s_a-8, None, 0, rsp
      and add_target = s_a + size + ofs-8, None, 0, rsp in
      write_expr_code false f e ++ (copy_value s_a add_or add_target) ++ popn s_a
    in
    let rec aux = function
      |[] -> nop
      |a::q -> (compute_att a) ++ (aux q)
    in comment "Sobj" ++ pushn size ++ aux attributes ++ popn size , size       
  |TSwhile (e,b) ->
    let lab_while = new_lab f in
    let lab_follow = new_lab f in
    let test_code =  write_test_code f e lab_while lab_follow in
    comment "Swhile" ++ test_code ++ (label lab_while) ++ (write_bloc_code f b) ++ test_code ++ (label lab_follow), 0
  |TSreturn eop ->
    let store_res = 
      begin
        match eop with
        |None -> nop
        |Some e ->
          let ofs = Hashtbl.find res_pos f in
          let size_value = (get_size (snd e)) in
          let add_target = ofs, None, 0, rbp
          and add_or = size_value-8, None, 0, rsp in
          (write_expr_code false f e) ++ (copy_value size_value add_or add_target) ++ (popn size_value)
      end
    in comment "Sreturn" ++ store_res ++ (movq (reg rbp) (reg rsp)) ++ (popq rbp) ++ ret, 0
  |TSif i ->
    comment "Sif" ++
    write_if_code f i, 0

and write_if_code f i_instr =
  let lab_if = new_lab f in
  let lab_follow = new_lab f in 
  match i_instr with
  |TAif (e,b) ->
    let test_code = write_test_code f e lab_if lab_follow in
    test_code ++ (label lab_if) ++ (write_bloc_code f b) ++ (jmp lab_follow) ++ (label lab_follow)
  |TBif (e,b1,b2) ->
    let lab_else = new_lab f in
    let test_code = write_test_code f e lab_if lab_else in
    test_code ++ (label lab_if) ++ (write_bloc_code f b1) ++ (jmp lab_follow) ++
      (label lab_else) ++ (write_bloc_code f b2) ++ (jmp lab_follow) ++ (label lab_follow)
  |TIif (e,b,i) ->
    let lab_else = new_lab f in
    let test_code = write_test_code f e lab_if lab_else in
    test_code ++ (label lab_if) ++ (write_bloc_code f b) ++ (jmp lab_follow) ++
      (label lab_else) ++ (write_if_code f i) ++ (jmp lab_follow) ++ (label lab_follow)

and write_test_code f e lab_true lab_follow =
  (write_expr_code false f e) ++ (popq rax) ++ (cmpq  (imm 0) (reg rax))  ++ (jne lab_true) ++ (jmp lab_follow)
      

and write_expr_code point f expr = match (fst expr) with
  (*Résultat sur la pile, l'opération fait attention à la taille, point indique si on veut un pointeur ou non*)
  |TEint n ->
    comment "Eint" ++ pushq (imm n)
  |TEbool b ->
    comment "Ebool" ++ movq (imm (match b with |false -> 0 |true -> 1)) (reg rax) ++
    pushq (reg rax)
  |TEident i ->
    comment ("Eident "^(fst i)) ++
    if point then
      let ofs = (Hashtbl.find (Hashtbl.find local_pos f) i) in
      movq (reg rbp) (reg rax) ++
      addq (imm ofs) (reg rax) ++
      pushq (reg rax)
    else
      let t = snd expr in      
      let s = get_size t in
      let add_or = (Hashtbl.find (Hashtbl.find local_pos f) i), None, 0, rbp
      and add_cop = -8, None, 0, rsp in
      (copy_value s  add_or add_cop) ++ pushn s
  |TEbinop (e1,b,e2) ->
    comment "Ebinop" ++
    let code_fetch =
    if b <> Affect then
      write_expr_code false f e1 ++ write_expr_code false f e2 ++ popq rbx ++ popq rax 
    else
      (pushq (reg r12) ++ write_expr_code true f e1 ++ popq r12 ++
         write_expr_code false f e2)
        (*On va vider la pile apres la copie. r8 contient toujours l'adresse d'un element a affecter*)
    in code_fetch ++
         begin
           match b with
           |Equal | Not_equal | Less | Greater | Less_or_equal | Greater_or_equal | And | Or
            -> write_bool_code b ++ pushq (reg rax)
           |Plus | Minus | Times
            -> write_arith_code b ++ pushq (reg rax)
           |Divide 
            -> write_div_code ++ pushq (reg rax)
           |Modulo
            -> write_div_code ++ pushq (reg rdx)
           |Affect
            -> let size = get_size (snd e2) in
               let add_or = size -8 , None, 0, rsp
               and add_target = 0, None, 0, r12 in
               copy_value size add_or add_target ++ popn (size) ++ popq r12
         end
  |TEunop (u,e) ->
    comment "Eunop" ++
    begin
      match u with
      |Not ->
        write_expr_code false f e ++ popq rax ++ notq (reg rax) ++ andq (imm 1) (reg rax) ++ pushq (reg rax)
      |UMinus ->
        write_expr_code false f e ++ popq rax ++ negq (reg rax) ++ pushq (reg rax)
      |SharedBorrow |MutBorrow ->
        write_expr_code true f e
      |Deref ->
        let (_,t) = e in
        let size_res =
          begin
            match t with
            |Tref (_,t1) -> get_size t1
            |_ -> failwith "Drunk programmer called the wrong function again"
          end
        in
        let add_or = 0, None, 0, rax
        and add_target = 0, None, 0, rsp in
        (write_expr_code false f e) ++ popq rax ++ (copy_value size_res add_or add_target)
    end
  |TEattribute (e,id) ->
    let s = get_size (snd expr) in
    let ofs = (Hashtbl.find (Hashtbl.find att_pos f) id) - s in
    let compute_value =
      if point then
        (popq rax) ++ (addq (reg rax) (imm (ofs))) ++ pushq (reg rax)
      else
        let add_or = ofs, None, 0, rax
        and add_target = -8,None,0,rsp in
        (copy_value s add_or add_target) ++ pushn s
    in
    comment "Eattribute" ++ write_expr_code true f e ++ compute_value 
  |TElen e ->
    write_expr_code false f  e  ++ popn 8 ++ popq rax
  (*Ca met le vecteur sur la pile, le premier champ c'est la longueur*)
  |TEselect (e1,e2) ->
    let s = get_size (snd e2) in
    let compute_value =
      if point then
        movq  (ind ~index:rbx ~scale:s rax) (reg rax) ++ pushq (reg rax)
      else
        let add_or = 0, Some rbx, s, rax
        and add_target = -8, None, 0, rsp in
        let s_expr = get_size (snd e1) in
        (copy_value s_expr add_or add_target) ++ (pushn s_expr)
    in
      write_expr_code false f e1 ++
        write_expr_code false f e2 ++ popq rbx ++ popq rax ++ popn 8 ++ compute_value
  |TEcall (func,args) ->
    let size_res = (get_size (snd expr)) in
    let total_ofs = -8+(Hashtbl.find res_pos func)-size_res (*cf emplacement des variables*) in
    let arg_ofs = Hashtbl.find local_pos func in      
    pushn size_res ++ (write_set_arguments_code f arg_ofs (Hashtbl.find arg_corres func) args) ++ (call func) ++ popn total_ofs(*TODO : remettre rsp au bon endroit*)
  |TEvect l ->
    let size = match l with
      |[] -> 8
      |e::q -> get_size (snd e)
    in
    let code, n_el = allocate_vector f size 0 l in
    movq (imm (size*n_el)) (reg rdi) ++ (call "malloc") ++ code
  |TEprint s ->
    let l = new_lab f in
    data_code := (!data_code) ++ label l ++ string s;
    comment "Eprint" ++ movq (imm 0) (reg rax) ++ movq (ilab l) (reg rdi) ++ call "printf" 
  |TEbloc b ->
    write_bloc_code f b

and allocate_vector f size n_el= function
  |[] -> nop, n_el
  |e::q -> let code, tot_el = allocate_vector f size  (n_el + 1) q in
           let add_or = size-8, None, 0, rsp
           and add_target = n_el*size, None, 0, rax in
           let fcode = write_expr_code false f e ++ (copy_value size add_or add_target) ++ popn size in
           fcode,tot_el

and write_bool_code = function
  |And ->
    andq (reg rbx) (reg rax)
  |Or ->
    orq (reg rbx) (reg rax)
  |binop ->
    cmpq (reg rbx) (reg rax) ++
      begin
        match binop with
        |Equal ->
          sete (reg al)
        |Not_equal ->
          setne (reg al)
        |Less ->
          setl (reg al)
        |Less_or_equal ->
          setle (reg al)
        |Greater ->
          setg (reg al)
        |Greater_or_equal ->
          setge (reg al)
        |_ -> failwith "Drunk programmer called the wrong function again"
      end
    ++ andq (imm 1) (reg rax) 
   
and write_arith_code  = function
  |Plus -> addq (reg rbx) (reg rax)
  |Minus -> subq (reg rbx) (reg rax)
  |Times -> imulq (reg rbx) (reg rax) (*comment fonctionne imulq en vrai ? il faudrait imulq %rax*)
  |_ -> failwith "Drunk programmer called the wrong function again"
    
and write_div_code =
  cqto ++ (idivq (reg rbx))

and copy_value size a_or a_target =
  let rec aux = function
    |n when n=size  -> nop
    |n -> movq (write_adress a_or n) (reg rcx)++
            (movq (reg rcx) (write_adress a_target n)) ++
            (aux (n+8))
  in aux 0

and write_adress a ofs=
  let ofs_a,index_a,scale_a,add_a = a in
  match index_a with
  |None -> ind ~ofs:(ofs_a+ofs) add_a
  |Some r -> ind ~ofs:(ofs_a+ofs) ~index:r ~scale:scale_a add_a

and new_lab =  let r = ref 0 in (fun f -> incr r; "."^f^(string_of_int !r))
                            
and write_set_arguments_code f var_ofs args_list args= match (args_list, args) with
  |([],[]) -> nop
  |(i::l,a::q) ->
    (write_set_arguments_code f var_ofs l q) ++ (write_expr_code false f a) 
  (*On écrit d'abord ceux qui sont à la fin de la liste => sont plus haut dans la pile*)      
  |_ -> failwith "Nombre incorrect d'arguments"

  
and write_function_code func =
  let f = func.name and body = func.body in
  (label f) ++ (pushq (reg rbp)) ++ (movq  (reg rsp) (reg rbp)) ++
    (write_bloc_code f body) ++ (movq  (reg rbp) (reg rsp)) ++ popq rbp ++ (
    if func.name="main" then movq (imm 0) (reg rax) else nop) ++ ret
(*A verifier*)
                                     
let rec write_all_codes = function
  |[] -> nop
  |(TDdecl_struct s)::q -> write_all_codes q
  |(TDdecl_fun f)::q -> write_function_code f ++ write_all_codes q

let compile s prog =
  compute_all_attributes_positions prog;
  print_string "1\n";
  compute_all_arguments_positions prog;
  print_string "2\n";
  compute_all_locals_positions prog;
  print_string "3\n";
  let t = globl "main" ++ write_all_codes prog in
  let p = {text = t;  data = !data_code} in
  let f = open_out (String.sub s 0 ((String.length s) -2)^"s") in
  let fmt = formatter_of_out_channel f in
  X86_64.print_program fmt p;
  fprintf fmt "@?";
  close_out f



