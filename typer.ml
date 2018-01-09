open Ast

module Smap = Map.Make (String)
module Sset = Set.Make (String) 
type env = typ Smap.t
          

exception Erreur_typage of typ * typ * loc
exception Erreur_types_egaux of typ *loc *typ * loc
exception Erreur_types_non_egaux of typ *loc * typ  
exception Erreur_mut of expr * loc
exception Erreur_vide of loc
exception Erreur_lvalue of expr * loc
exception Erreur_len of int * int *loc 
exception Erreur_no_expr of expr * loc

(* TODO veriffier le chek des stmt avec None et le transformer en Tunit mais donc le chek aev st *)
(*TODO les hashtbl, les tref plusieurs fois, le e.x avec l histoire de regarder si ce st dans l ident , les histoires de t1<T2 *)

let rec type_list  env e = 
   match e with 
      |Unit -> raise (Erreur_vide (loc))
      |x -> 
         let (_,xt) as xtype = type_expr env x
         xt
      
      |x::y::r -> 
         let (_, xt) as xtype =type_expr env x
         let (_, yt) as ytype = type_expr env y
         begin match xt with
            |yt -> type_list env y::r
            |_-> raise (Erreur_types_non_egaux (xt, snd x , yt, snd y))
         end
   
let rec type_arg_list env (list_typ, list_expr ) =
   match list_typ with 
      |Unit -> true  
      | x-> begin match list_expr with 
         |y -> begin match snd x with
            | y -> true (* Une valeur random pour verifier *)
            | _ -> raise (Erreur_types_non_egaux (snd x * snd (fst x) * y )) (* verifier que snd fst x renvoie la loc de x *)
         end
      end 
      | x::y::r -> begin match list_expr with 
         |w::z::o -> begin match snd x with
            | w -> begin match snd y with
               | z -> type_arg_list (y::r , z::o)
               |_ -> raise (Erreur_types_non_egaux (snd y * snd (fst y) * z ))
            end
            |_ -> raise (Erreur_types_non_egaux (snd x * snd (fst x) * w )) (* De meme *)
         end
      end

let type_mut_expr env (e, loc) = match e with (* TODO premiere regele de mut *)

   |Eselect (e1, e2) ->
      let (_, e1t, b) as e1type =type_mut_expr env e1 in
      let (_, e2t) as e2type =type_expr env e2 in
      begin match e1t with 
         |Tvec -> begin match e2t with 
            |Tint -> (TEselect (e1type, e2type ), e1t, b)
            |_ -> raise (Erreur_typage (e2t, Tint, snd e2))
            end
         |Tref ->
            let (_, e3t, _) as e3type = type_mut_expr env *e1 in
            begin match e3t with
               |Tvec -> begin match e2t with 
                  |Tint -> (TEselect (e1type, e2type), e1t, b)
                  |_ -> raise ( Erreur_typage (e2t, Tint, snd e2))
                  end
               |_ -> raise (Erreur_typage (se3t , Tvec, snd e1))
            end
         |_ -> raise (Erreur_typage (e1t, Tvec, snd e1))
      end
   
   |Eattribute (e, i) ->
      let (_,et, b) as etype = type_mut_expr env e in
      begin match et with 
         |Tstruct  -> 
            let t = check_in (et, i) 
            (* TODO regarder si i est dans la struct associée à e avec une fonction qui renvoie le type associé a i et raise error sinon *)
            (TEattribute (etype, ident), t, b)
         
         | Tref -> 
            let (_, e2t, _) as e2type = type_mut_expr env *e in
            begin match e2t with
               |Tstruct ->
                  let t = check_in (et, i) 
                  (* TODO regarder si i est dans la struct associée à e avec une fonction qui renvoie le type associé a i et raise error sinon *)
                  (TEattribute (etype, ident), t, b)
               | _ -> raise ( Erreur_typage (e2t , Tstruct, snd e))
         
         |_ -> raise (Erreur_typage (et, Tstruct, snd e))
      end
   |Eunop (unop, e) ->
      begin match unop with
         |Deref ->
            let (_, et, b) as etype = type_mut_expr env e in
            begin match et with 
               |Tref -> (TEunop (unop, etype), Tint, b)
               |_ -> raise (Erreur_typage (et, Tref, snd e))
            end
   |Eattribute (e, i) ->
      let (a,et, b) as etype = type_mut_expr env e in
      begin match et with 
         |Tstruct  -> 
            let t = check_in (et, i) 
            (* TODO regarder si i est dans la struct associée à e avec une fonction qui renvoie le type associé a i et raise error sinon *)
            (TEattribute (etype, ident), t, b)
         
         | Tref ->
            let (_, e3t, _) as e3type = type_mut_expr env *e1 in
            begin match e3t with
               |Tstruct -> 
                   let t = check_in (e3t, i) 
                   (* TODO regarder si i est dans la struct associée à e avec une fonction qui renvoie le type associé a i et raise error sinon *)
                   (TEattribute (etype, ident), t, b)
               | _ -> raise ( Erreur_typage (e3t , Tstruct, snd e))
            end
         |_ -> raise (Erreur_typage (et, Tstruct, snd e))
      end
   |_ -> raise (Erreur_mut (e, snd e))

 
      
let type_lvalue_expr env (e, loc ) = match e with 
   (* deref done, deuxieme, crochet done, struct, struct bis done *)
   |Eunop (unop , e) ->
      begin match unop with 
         |Deref ->
            let (_, et) as etype = type_expr env e in
            begin match et with
               |Tref -> (TEunop (unop, etype) , Tint)
               |_-> raise ( Erreur_typage (et , Tref, snd e))
            end
      end
   |Eselect (e1 , e2) ->
      let (_, e1t) as e1type =type_lvalue_expr env e1 in
      let (_, e2t) as e2type =type_expr env e2 in
      begin match e1t with 
         |Tvec -> begin match e2t with
            |Tint -> ( TEselect ( e1type , e2type ), e1t ) 
            | _-> raise ( Erreur_typage (e2t, Tint, snd e2))
            end
         |Tref ->
            let (_, e3t, _) as e3type = type_mut_expr env *e1 in
            begin match e3t with
               |Tvec-> begin match e2t with
                  |Tint -> ( TEselect ( e1type , e2type ), e1t ) 
                  | _-> raise ( Erreur_typage (e2t, Tint, snd e2))
               end
               |_ -> raise (Erreur_typage (e3t, Tvec , snd e1))
            end
         | _-> raise ( Erreur_typage (e1t, Tvec, snd e1))
      end 
  |Eattribute (e, i) ->
      let (_, et) as etype = type_lvalue_expr env e in
      begin match et with 
         |Tstruct  -> 
            let t = check_in (et, i) 
            (* TODO regarder si i est dans la struct associée à e avec une fonction qui renvoie le type associé a i et raise error sinon *)
            (TEattribute (etype, ident), t)
         
         | Tref -> 
            let (_, e3t, _) as e3type = type_mut_expr env *e1 in
            begin match e3t with
               |Tstruct -> 
                   let t = check_in (et, i) 
                   (* TODO regarder si i est dans la struct associée à e avec une fonction qui renvoie le type associé a i et raise error sinon *)
                   (TEattribute (etype, ident), t)
               | _ -> raise ( Erreur_typage (e3t , Tstruct, snd e))
            end
         |_ -> raise (Erreur_typage (et, Tstruct, snd e))
      end
   |Sobj (m, i, i1, s) ->
      let a = find.hastbl (i) (* TODO codercette hastbl *)
      begin match a.len with 
         |s.len ->
            let r =type_arg_list env (snd s (*ici c est e *), find.hastbl (i))
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
               |true -> (TEunop (unop, etype), Tref ) 
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
            
            begin match b with
               |false -> raise ( Erreur_mut (e1 , loc))
               |true -> (Eassignement (e1type, e2type), Tunit ) 
            end
      end
      
   |Elen e ->
      let (_, et) as etype =type_expr env e in
      begin match et with 
         |Tvec -> (TEvect e , Tint )
         |Tref -> begin match snd a with
            |Tvec -> (TEvect e, Tint )
            |_ -> raise (Erreur_typage ( snd a, Tvec, snd e)) (*Considere que Tref peut etre applique qu'une fois *)
         |_ -> raise ( Erreur_typage ( et, Tvec , snd e))
      end      
  
  | Evect e ->
     let r=type_list env e
     (TEvect (type_expr env e),r)

  |Eprint s -> (TEprint s , Tunit)
  
  |Ecall (i, e) -> 
     let a = find.hastbl (i) (* TODO coder cette hastbl *)
     begin match a.len with
        |e.len ->
           let r = type_arg_list env (a, e) 
           begin match r with 
              | true -> (TEcall (i, e), type de retour) (* TODO trouver ce type de retour *)
           end
        |_ -> raise (Erreur_len (e.len , a.len, snd e))
     end
  (* tout ce qui suit permet de vérifier si l'expression n'est pas une l value car implique que c'est une value normale *)   
  |Eunop (unop , e) ->
      begin match unop with 
         |Deref ->
            let (_, et) as etype = type_expr env e in
            begin match et with
               |Tref -> (TEunop (unop, etype) , Tint)
               |_-> raise ( Erreur_typage (et , Tref, snd e))
            end
      end
   |Eselect (e1 , e2) ->
      let (_, e1t) as e1type =type_lvalue_expr env e1 in
      let (_, e2t) as e2type =type_expr env e2 in
      begin match e1t with 
         |Tvec -> begin match e2t with
            |Tint -> ( TEselect ( e1type , e2type ), e1t ) 
            | _-> raise ( Erreur_typage (e2t, Tint, snd e2))
            end
         |Tref -> 
            let (_, e3t, _) as e3type = type_mut_expr env *e1 in
            begin match e3t with
               |Tvec-> 
                  begin match e2t with
                     |Tint -> ( TEselect ( e1type , e2type ), e1t ) 
                     | _-> raise ( Erreur_typage (e2t, Tint, snd e2))
                  end
               |_ -> raise (Erreur_typage (e3t, Tvec , snd e1)) 
            end
         | _-> raise ( Erreur_typage (e1t, Tvec, snd e1))
      end 
  |Eattribute (e, i) ->
      let (_,et) as etype = type_lvalue_expr env e in
      begin match et with 
         |Tstruct  -> 
            let t = check_in (et, i) 
            (* TODO regarder si i est dans la struct associée à e avec une fonction qui renvoie le type associé a i et raise error sinon *)
            (TEattribute (etype, ident), t)
         
         | Tref -> 
            let (_, e3t, _) as e3type = type_mut_expr env *e1 in
            begin match e3t with
               |Tstruct ->
                   let t = check_in (et, i) 
                   (* TODO regarder si i est dans la struct associée à e avec une fonction qui renvoie le type associé a i et raise error sinon *)
                   (TEattribute (etype, ident), t)
               | _ -> raise ( Erreur_typage (e3t , Tstruct, snd e))
            end
         |_ -> raise (Erreur_typage (et, Tstruct, snd e))
      end
  |Sobj (m, i, i1, s) ->
      let a = find.hastbl (i) (* TODO codercette hastbl *)
      begin match a.len with 
         |s.len ->
            let r =type_arg_list env (snd s (*ici c est e *), find.hastbl (i))
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
      let a = find.hastbl (i) (* TODO codercette hastbl *)
      begin match a.len with 
         |s.len ->
            let r =type_arg_list env (snd s (*ici c est e *), find.hastbl (i))
            begin match r with 
               |true -> (* regarder si c est bien une permutation ! *) 
                  
            end
         |_ -> raise ( Erreur_len (s.len , a.len, snd s ))
      end
              

and type_bloc env (b, loc) = match b with
   |Ubloc (s) -> 
      begin match s with
         |Unit -> 
            let (_, st) as stype = type_stmt env s in
            (TUbloc (stype), Tunit)
         |_ -> 
            let (_,st) as stype = type_stmt env s in
            (TUbloc (stype), st) (* { e } est du type de e *)
      end   
   
   |Vbloc (s, b) -> 
      let (_, st) as stype = type_stmt env s in 
      begin match s with 
         |Unit ->
            let (_,bt) as btype= type_bloc env b in
            (TVbloc (stype, btype), bt) (* { ; b} est du type de b *)
         |Sexpr (_) | Swhile (_ , _) | Sreturn (_) |Sif (_)-> 
            let (_,bt) as btype =type_bloc env b in
            (TVbloc (stype, btype), bt) (* {e ; b} est du type de b *)
         |Sobj (m, x, _) | Saff (m, x, _, _)->
            let (_,bt) as btype =type_bloc (Smap.add (m*x)  (type_stmt env s ) env) in (* TODO check si m*x est legit *)
            (TVbloc (stype, btype), bt )
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
      
      
         
   
   
  (*  type env = {
   dec_vars : typ Smap.t ; (* associe à chaque variable son type *)
   dec_typs : typ SImap.t ; (* associe à chaque variable dont le type est déclarée le type qu'elle dénote *)
   def_funs : ((mode * typ) list * typ) Smap.t ;(*associe à chaque fonction son type de retour, la liste du type 
   * et du mode de sesargs *)
   dec_structs ((typ * int) Smap.t * (int *int)) Smap.t ;
   structs_counter : int ;
   borrowed_by : (ident list) BSmap.t; 
   const_vars : Sset.t ;
   idents : (dtyp * int ) Smap.t ; ;
   level : int ;
   
  let empty_env name= 
     let env = { dec_vars = Smap.empty ;
                 dec_typs = SImap.empty ;
                 def_funs = SImap.empty ;
                 dec_structs = Smap.empty  ;
                 structs_counter = 0 ;
                 borrowed_by  = BSmap.empty ;
                 const_vars : Sset.empty ;
                 idents = Smap.empty ;
                 level = 0 ;
                 
}

let rec type_fun_call env is_exp i el loc =
  let etl = List.map (fun x -> type_expr env x, snd x) el in
  let ((pl, rt), level) = fun_of_ident i env in
  if is_exp then match rt with
     |Tunit -> raise (Erreur_types_egaux (rt, Tunit, loc))
  else if rt <> Tunit then raise (Erreur_typage (rt, Tunit , loc))
  
  let lc = try List.combine etl pl with Invalid_argument _ ->
    raise (Wrong_argument_number (List.length el, List.length pl, loc)) in
  List.iter (fun (((exp, typ1), eloc), (mode, typ2)) ->
    if mode = Minout then check_is_lvalue exp eloc env;
    check_types_equal typ1 typ2 eloc) lc
  (List.map (fun ((x, _), (m, _)) -> (x, m = Minout)) lc, rt, level)

let fun_of_ident (i, loc) env =
  try
    let (dtyp, level) = Smap.find i env.idents in
    if dtyp <> Dtyp_fun_def then raise Not_found;
    Smap.find i env.def_funs, level
  with Not_found -> raise (Undeclared (i, loc))
  
 |Ecall (i, e1) ->
    let (el, rt, level) = type_fun_call env true i el loc in
    (TEcall ((fst i, level), el), rt)
    
    |

 |Eassignement (e1 , e2) -> 
      let (_, e1t) as e1type =type_expr env e1 in
      let (_, e2t) as e2type =type_expr env e2 in
      | false -> let muterr' = match e1.e_tre
         | Efield (_, idn) -> 
            (idn.id_loc, Assign_immutable_field idn.id)
         | Eid idn -> 
            (e1.e_loc, Re_assignment idn.id) 
         | _ -> 
            (e1.e_loc, Invalid_left_hand)  
         in 
         begin try typ_lt ty2 ty1 with 
            | Type -> raise_error e2.e_loc (Type_error (ty1, ty2));
            | Life -> () 
         end;
         Tunit None, env2, Some muterr', tree1 
         | true -> 
            begin try typ_lt ty2 ty1 with 
               | Type -> raise_error e2.e_loc (Type_error (ty1, ty2));
               | Life ->  
                  let id1 = exp_to_id e1 and id2 = get_br_id e2 in
                  raise_error e2.e_loc (Live_not_long_enough (id2, id1)) end;
            if is_id e1 then begin 
               let Eid idn = e1.e_tree in
               if alr_borrow env idn.id then 
                  raise_error e.e_loc (Assign_already_borrowed idn.id) end;
             let env3 = match e2.e_tree with
                | Eid idn -> drop_var env idn
                | _ -> env2 
             in 
             Tunit None, env3, None, to_addr tree1  

*)
