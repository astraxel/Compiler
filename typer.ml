open Ast

module Smap = Map.Make (String)
module Sset = Set.Make (String) 
type Env_variables = (bool, typ) Smap.t
type Env_fonction = (typ list , typ) Smap.t
type Env_structures = ((ident, typ) list )Smap.t 
type Env = (Env_variables, Env_fonction, Env_structures)

let get_variables (ev, _, _)= ev
let get_fonction (_,ef,_) =ef
let get_structures (_,_,es)=es

exception Erreur_typage of typ * typ * loc
exception Erreur_types_egaux of typ *loc *typ * loc
exception Erreur_types_non_egaux of typ *loc * typ  
exception Erreur_mut of expr * loc
exception Erreur_vide of loc
exception Erreur_lvalue of expr loc
exception Erreur_len of int * int *loc 
exception Erreur_no_expr of expr * loc
exception Erreur_types_non_coherents of typ * loc * typ * loc
exception Erreur_non_declare of typ * loc
exception Erreur_borrow of loc
exception Erreur_struct_call of typ * ident * loc
exception Erreur_not_mutable of loc

(* TODO veriffier le chek des stmt avec None et le transformer en Tunit mais donc le chek aev st *)
(*TODO les hashtbl, le e.x avec l histoire de regarder si ce st dans l ident *)
(* penser à la loc dans AST *)
(* def la fonction check_bf *)
(* list lenght *)


let rec deref_type t = if t =Tref (m, t1) then deref_type t1 else t
   
let rec type_adapte (t1, t2) =
   match deref_type t1 with
      |deref_type t2 -> true
      |_ -> false
 
let rec check_uni (list_ident) =
   match list_ident with
      |[] -> true
      |x::r -> 
   
 
let rec type_no_struct env (e, i) =
   match e with 
      |[] -> true
      |x::[] ->
         let (_, xt) as xtype = type_expr env x in
         begin match xt with
            |Tstruct (i) -> (*TODO faire cttte partie avec le sous vec et verifie la gestion d'erreur *)
            |_ -> raise (Error_struct_call (xt, i, snd xt))
      |x::y::r -> 
         let (_,xt) as xtype = type_expr env x in
         let (_,yt) as ytype = type_expr env y in
         begin match xt with 
            |Tstruct (i) -> (*TODO faire cttte partie avec le sous vec et verifie la gestion d'erreur *)
            |_ -> raise (Error_struct_call (xt, i, snd xt))
            
let rec type_no_borrow env (e ) =
   match e with
      |[] -> true
      |x::[] -> 
         let (_, xt) as xtype = type_expr env x in
         begin match check_no_borrow xt with (*TODO definir la fonction check_no_borrow *)
            |true -> true
            |false -> raise (Error_borrow (snd x))
         end
      |x::y::r -> 
         let (_,xt) as xtype = type_expr env x in
         let (_,yt) as ytype = type_expr env y in
         begin match check_no_borrow xt with (*TODO definir la fonction check_no_borrow *)
            |true -> type_no_borrow env (y::r)
            |false -> raise (Error_borrow (snd x))

let rec structure_list_with_constraint li_expr type_cible = match li_expr with
   | [] -> []
   | x::q -> let (type_pur_x, structure_x) = type_expr env x in
       if type_cible = type_pur_x then
           structure_x :: (type_list_with_constraint q)
       else
           raise (Error_typage (type_pur_x, type_cible, snd x))

let type_list li_expr = match li_expr with
   | [] -> ([], Vec (TUnit))
   | x::q -> let (type_pur, structure_x) = type_expr x in
       (structure_x :: (structure_list_with_constraint q type_pur), Vec (type_pur))
   
      
let rec type_bf env (e)=
   match e with 
      |[] -> true
      |x::[] ->
         let (_, xt) as xtype =type_expr env x in 
         begin match check_bf xt with  (* TODO definir la fonction check_bf *)
            |true -> true
            |false -> raise (Error_non_declare (xt, snd x))
         end
      |x::y::r ->
         let (_, xt) as xtype = type_expr env x in 
         let (_, yt) as ytype = type_expr env y in 
         begin match check_bf xt with (* TODO definir la fonction check_bf *)
            |true -> type_bf env (y::r) 
            |false -> raise (Error_non_declare (xt, snd x))
         end

let rec type_arg_comparaison_list env (list_typ, list_expr) =
   match list_typ with 
      |[] -> true  
      | x::[]-> begin match list_expr with 
         |y::[] -> 
            let r =type_adapte (y, snd x) in
            begin match r with
               | true -> true (* Une valeur random pour verifier *)
               | false -> raise (Erreur_types_non_egaux (snd x * snd (fst x) * y )) 
            end
         end
      end 
      | x::y::r -> begin match list_expr with 
         |w::z::o -> 
            let r = type_adapte (w, snd x) in
            begin match r with
               | true -> 
                  let r1 = type_adapte (z, snd y) in
                  begin match r1 with
                     |true  -> type_arg_list (y::r , z::o)
                     |false-> raise (Erreur_types_non_egaux (snd y * snd (fst y) * z ))
                  end
            |false-> raise (Erreur_types_non_egaux (snd x * snd (fst x) * w )) 
            end
         end
   
let rec type_arg_list env (list_typ, list_expr ) =
   match list_typ with 
      |-> true  
      | x::[]-> begin match list_expr with 
         |y::[] -> begin match snd x with
            | y -> true (* Une valeur random pour verifier *)
            | _ -> raise (Erreur_types_non_egaux (snd x * snd (fst x) * y )) 
         end
      end 
      | x::y::r -> begin match list_expr with 
         |w::z::o -> begin match snd x with
            | w -> begin match snd y with
               | z -> type_arg_list (y::r , z::o)
               |_ -> raise (Erreur_types_non_egaux (snd y * snd (fst y) * z ))
            end
            |_ -> raise (Erreur_types_non_egaux (snd x * snd (fst x) * w )) 
         end
      end

let type_mut_expr env (e, loc) = match e with 
   |Eident name -> let (m, t) = Smap.find name env in
      begin match m with 
         |true -> (TEident (name), t, true)
         |false -> raise ( Error_not_mutable (snd name))

   |Eselect (e1, e2) ->
      let (_, e1t, b) as e1type =type_mut_expr env e1 in
      let (_, e2t) as e2type =type_expr env e2 in
      let t1 = deref_type e1t in
      begin match t1 with 
         |Tvec -> begin match e2t with 
            |Tint -> (TEselect (e1type, e2type ), e1t, b)
            |_ -> raise (Erreur_typage (e2t, Tint, snd e2))
            end
         |_ -> raise (Erreur_typage (e1t, Tvec, snd e1))
      end
   
   |Eattribute (e, i) ->
      let (_,et, b) as etype = type_mut_expr env e in
      let t1 = deref_type et in
      begin match t1 with 
         |Tstruct  -> 
            let t = check_in (et, i) in
            (* TODO regarder si i est dans la struct associée à e avec une fonction qui renvoie le type associé a i et raise error sinon *)
            (TEattribute (etype, ident), t, b)
         |_ -> raise (Erreur_typage (et, Tstruct, snd e))
      end
   |Eunop (unop, e) ->
      begin match unop with
         |Deref ->
            let (_, et, b) as etype = type_mut_expr env e in
            begin match et with 
               |Tref (_, t) ->
                  let t1 = deref_type t in
                  (TEunop (unop, etype), t , b)
               |_ -> raise (Erreur_typage (et, Tref, snd e))
            end
   |_ -> raise (Erreur_mut (e, snd e))

 
      
let type_lvalue_expr env (e, loc ) = match e with 
   |Eident name -> 
      let (m, t) = Smap.find name env in
      (TEident (name), t)
   |Eunop (unop , e) ->
      begin match unop with 
         |Deref ->
            let (_, et) as etype = type_expr env e in
            begin match et with
               |Tref (_, t) -> 
                  let t1 = deref_type t in
                  (TEunop (unop, etype) , t1)
               |_-> raise ( Erreur_typage (et , Tref, snd e))
            end
      end
   |Eselect (e1 , e2) ->
      let (_, e1t) as e1type =type_lvalue_expr env e1 in
      let (_, e2t) as e2type =type_expr env e2 in
      let t1 = deref_type e1t in
      begin match t1 with 
         |Tvec -> begin match e2t with
            |Tint -> ( TEselect ( e1type , e2type ), e1t ) 
            | _-> raise ( Erreur_typage (e2t, Tint, snd e2))
            end
         | _-> raise ( Erreur_typage (e1t, Tvec, snd e1))
      end 
  |Eattribute (e, i) ->
      let (_, et) as etype = type_lvalue_expr env e in
      let t1 = deref_type et in
      begin match t1 with 
         |Tstruct  -> 
            let t = check_in (et, i) in
            (* TODO regarder si i est dans la struct associée à e avec une fonction qui renvoie le type associé a i et raise error sinon *)
            (TEattribute (etype, ident), t)
         |_ -> raise (Erreur_typage (et, Tstruct, snd e))
      end
   |Sobj (m, i, i1, s) ->
      let a = find.hastbl (i) in(* TODO codercette hastbl *)
      begin match a.len with 
         |s.len ->
            let r =type_arg_list env (snd s (*ici c est e *), find.hastbl (i)) in
            begin match r with 
               |true -> (* regarder si c est bien une permutation ! *) 
                  
            end
         |_ -> raise ( Erreur_len (s.len , a.len, snd s ))
      end
   |_ -> (Erreur_lvalue (e, snd e))
   
let type_expr env (e , loc) = match e with 
   |Eint n -> (TEint n, Tint)
   |Ebool b -> (TEbool b, Tbool)
   |Eunop ( unop , e) -> 
      | begin match unop with 
         |Deref -> (*verifie si ce n'est pas une lvalue car lvalue implique value *)
            let (_, et) as etype = type_expr env e in
            begin match et with
               |Tref (_, t) -> 
                  let t1 = deref_type t in
                  ( (TEunop (unop, etype) , t1)
               |_-> raise ( Erreur_typage (et , Tref, snd e)) 
            end
         |UMinus ->
            let (_, et) as etype=type_expr env e in
            begin match et with
               |Tint -> (TEunop ( unop , etype), Tint)
               | _-> raise ( Erreur_typage ( et,   Tint , snd e ))
            end
         |Not ->
            let (_, et) as etype =type_expr env e in
            begin match et with 
               | Tbool -> (TEunop (unop, etype ),Tbool)
               | false -> raise ( Erreur_typage ( et, Tbool , snd e))
            end
         
         |SharedBorrow ->
            let (_, et) as etype =type_lvalue_expr env e in
            (TEunop (unop, etype), Toref )
         
         |MutBorrow -> 
            let (_, et, b) as etype = type_mut_expr env e in
            begin match b with
               |false -> raise ( Erreur_mut (e , loc))
               |true -> (TEunop (unop, etype), Tref (b, et)) 
            end
      end
   |Ebinop (e1, op , e2) ->
      let (_, e1t) as e1type =type_expr env e1 in
      let (_, e2t) as e2type =type_expr env e2 in
      begin match op with 
         | Equal | Not_equal | Less | Greater | Less_or_equal
         | Greater_or_equal  ->
            begin match e1t with
               |Tint -> begin match e2t with 
                  |Tint -> (TEbinop (e1type, op , e2type), Tbool)
                  |_ -> raise ( Erreur_typage (e2t, Tint, snd e2))
                  end
               |_ -> raise ( Erreur_typage (e1t, Tint , snd e1))
            end
         | Plus | Minus | Times | Divide | Modulo -> 
            begin match e1t with
               |Tint -> begin match e2t with 
                  |Tint -> (TEbinop ( e1type, op , e2type ), Tint)
                  | _-> raise ( Erreur_typage (e2t, Tint, snd e2)
                  end
              |_ -> raise ( Erreur_typage (e1t, Tint, snd e1))
            end
         | And | Or ->
            begin match e1t with
               |Tbool -> begin match e2t with 
                  |Tbool -> (TEbinop (e1type , op, e2type ), Tbool)
                  | -> raise ( Erreur_typage ( e2t, Tbool , snd e2))
                  end
               |_ -> raise ( Erreur_typage ( e1t, Tbool, snd e1 ))
         
         | Affect -> 
            let (_, e1t, b) as e1type =type_mut_value_expr env e1 in 
            let (_, e2t) as e2type =type_expr env e2 in
            let r = type_adapte (e1t, e2t) in
            begin match r with
               |true -> 
                  begin match b with 
                     |false -> raise ( Erreur_mut (e1 , loc))
                     |true -> (TEbinop (e1type, e2type), Tunit ) 
                  end
               |false -> raise (Erreur_types_non_coherents (e1, snd e1, e2, snd e2))
      end
      
   |Elen e ->
      let (_, et) as etype =type_expr env e in
      let t1 = type_deref et in
      begin match t1 with 
         |Tvec -> (TEvect etype , Tint )
         |_ -> raise ( Erreur_typage ( et, Tvec , snd e))
      end      
  
  | Evect e ->
     let (struct, t)= type_list env e in
     (TEvect (struct), t)

  |Eprint s -> (TEprint s , Tunit)
  
  |Ecall (i, e) -> 
     let a = find.hastbl (i) in (* TODO coder cette hastbl *)
     begin match a.len with
        |e.len ->
           let r = type_arg_comparaison_list env (a, e) in
           begin match r with 
              | true -> (TEcall (i, e), type de retour) (* TODO trouver ce type de retour *)
           end
        |_ -> raise (Erreur_len (e.len , a.len, snd e))
     end
  (* tout ce qui suit permet de vérifier si l'expression n'est pas une l value car implique que c'est une value normale *)   
   |Eunop (unop , e) ->
      begin match unop with 
         
      end
   |Eselect (e1 , e2) ->
      let (_, e1t) as e1type =type_lvalue_expr env e1 in
      let (_, e2t) as e2type =type_expr env e2 in
      let t1 = deref_type e1t in
      begin match t1 with 
         |Tvec -> begin match e2t with
            |Tint -> ( TEselect ( e1type , e2type ), e1t ) 
            | _-> raise ( Erreur_typage (e2t, Tint, snd e2))
            end
         | _-> raise ( Erreur_typage (e1t, Tvec, snd e1))
      end 
  |Eattribute (e, i) ->
      let (_, et) as etype = type_lvalue_expr env e in
      let t1 = deref_type et in
      begin match t1 with 
         |Tstruct  -> 
            let t = check_in (et, i) in
            (* TODO regarder si i est dans la struct associée à e avec une fonction qui renvoie le type associé a i et raise error sinon *)
            (TEattribute (etype, ident), t)
         |_ -> raise (Erreur_typage (et, Tstruct, snd e))
      end
   |Sobj (m, i, i1, s) ->
      let a = find.hastbl (i) in(* TODO codercette hastbl *)
      begin match a.len with 
         |s.len ->
            let r =type_arg_list env (snd s (*ici c est e *), find.hastbl (i)) in
            begin match r with 
               |true -> (* regarder si c est bien une permutation ! *) 
                  
            end
         |_ -> raise ( Erreur_len (s.len , a.len, snd s ))
      end
  |_ -> raise (Erreur_no_expr (e, snd e)) 
  

let type_decl_struct (i, i1) = 
   

let type decl_fun (i, arg, b, t)=

and type_stmt env (s, loc ) = match s with 
   |Sreturn e -> begin match e with 
      |None -> (TSreturn e , Tunit )
      |Some e1 -> (TSreturn e1 , Tunit)
      end 
   |Swhile ( e, e1 ) ->
      let (_, et) as etype =type_expr env e in
      let (_, e1t) as e1type = type_bloc env e1 in 
      begin match et with 
         |Tbool -> begin match e1t with
            |Tunit -> (TSwhile (etype, e1type) , Tunit)
            |_ -> raise ( Erreur_typage (e2type, Tunit , snd e1 ))
            end
         |_ -> raise ( Erreur_typage (etype, Tunit , snd e))
      end
   |Sif s ->
      let (_,st) as stype = type_if env s in
      (TSif (stype), st) 
      
   |Sobj (m, i, i1, s) ->
      let a = find.hastbl (i) in (* TODO codercette hastbl *)
      begin match a.len with 
         |s.len ->
            let r =type_arg_list env (snd s (*ici c est e *), find.hastbl (i)) in
            begin match r with 
               |true -> (* regarder si c est bien une permutation ! *) 
                  
            end
         |_ -> raise ( Erreur_len (s.len , a.len, snd s ))
      end
              

and rec type_bloc env (liste_instr, e_finale, loc) = match liste_instr with
   |[] ->
         ([], type_expr env (e_finale)) 
   |instr::q -> 
      begin match instr with 
         |Sexpr (e) ->
            let (structure, _) = type_expr env e in
            let (r, rtype)  = type_bloc env (q, e_finale) in
            (structure ::r, rtype)
         | Swhile (e , b1) ->
            let (structure, et) as etype = type_expr env e in
            begin match et with 
               |Tbool -> 
                  let r_list = list.rev b1 in
                  let e_head = list.hd r_list in
                  let b2_stmt = list.tl r_list in
                  let b1_stmt = list. rev b2_stmt in
                  let (rb, rbtype) = type_bloc env (b1_stmt, e_head) in 
                  begin match rbtype with
                     |Tunit ->
                        let (r, rtype)  = type_bloc env (q, e_finale) in
                        (structure ::r, rtype)
                     |_ -> raise (Error_typage (et, Tunit, (* TODO loc *))
                  end
               |_ -> raise (Error_typage ( et, Tbool, snd e))
            end
         | Sreturn (e) -> (* A verif *)
            let (structure, _) = type_expr env e in
            let (r, rtype)  = type_bloc env (q, e_finale) in
            (structure ::r, rtype)
            
         |Sif (e)-> 
            let (structure, st) = type_if env (p, loc)
            let (r, rtype) = type_bloc env (q, e_finale) in
            (structure ::r, rtype)
            
         |Sobj (m, x, e) -> (* TODO sobj et Saff *)
            let (structure, et) as etype = type_expr env e in
            let nouvelles_variables = (Smap.add x (m, et ) (get_variables env)) in
            let nouvel_environnement = (nouvelles_variables, get_fonction env , get_structures env) in
            
            let (structure_bloc,bt) as btype = type_bloc nouvel_environnement (Vbloc (q, e_finale)) in 
            (TVbloc (structure :: structure_bloc, ), bt )
        |Saff (m, x, _, _)->
      end
      

and type_if env ( p, loc ) = match p with 
   |Aif ( e, b) -> 
      let (_, et ) as etype =type_expr env e in 
      let (_, bt) as btype = type_bloc env b in 
      begin match et with 
         |Tbool -> (TAif (etype, btype ), bt )
         |_-> raise ( Erreur_typage (etype, Tbool, snd e))
      end
   |Bif ( e, b1 , b2) ->
      let (_, et ) as etype =type_expr env e in 
      let (_, b1t) as b1type = type_bloc env b1 in 
      let (_, b2t) as b2type = type_bloc env b2 in 
      begin match et with 
         |Tbool -> begin match b1t with 
            |b2t -> (TBif (etype, b1type, b2type) , b1t )
            |_ -> raise (Erreur_types_non_egaux ( b1type, snd b1, b2type, snd b2))
         end
         |_-> raise ( Erreur_typage (etype, Tbool, snd e)
      end
   |Cif (e, b, c) ->
      let (_, et ) as etype =type_expr env e in 
      let (_, bt) as btype = type_bloc env b in 
      let (_, ct) as ctype = type_if env c in 
      begin match et with 
         |Tbool -> begin match bt with 
            |ct -> (TCif (etype, btype, ctype), bt)
            |_ -> raise ( Erreur_types_non_egaux (btype, snd b , ctype, snd c))
         end
         |_ -> raise (Erreur_typage (etype, Tbool, snd e)
      end
      

