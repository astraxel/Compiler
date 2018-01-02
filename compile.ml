open Tast

(* Première partie : travail préliminaire sur les structures *)

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
  |Tunit -> failwith "Mauvais typage : attribut de type unit"
          
let compute_att_position data next att =
  Hashtbl.add data (fst att) next;
  next + (get_size (snd att))
  
           

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

let res_pos = Hashtbl.create 16
let arg_pos = Hashtbl.create 16

let compute_arg_position data next arg=
  let (_,id,t)=arg in
  let new_next = next - (get_size t) in
  Hashtbl.add data id new_next;
  new_next
  

let compute_res_pos next t =
  next - get_size(t)

let compute_arguments_positions (f:tdecl_fun) =
  let data_fun = Hashtbl.create 2 in
  let rec aux next = function
    |[] -> next
    |arg::q -> aux (compute_arg_position data_fun next arg) q
  in
  Hashtbl.add res_pos f.name (compute_res_pos (aux (-8) f.arguments) f.typ);
  Hashtbl.add arg_pos f.name data_fun

let rec compute_all_arguments_positions = function
  |[] -> ()
  |(TDdecl_struct s)::q -> compute_all_arguments_positions q
  |(TDdecl_fun f)::q -> compute_arguments_positions f; compute_all_arguments_positions q
