
	open Ast
        open Tast
	

	exception Lexing_error of string
        exception Erreur_typage of (Tast.ttyp * Tast.ttyp * Ast.loc)
        exception Erreur_types_egaux of (Tast.ttyp *Ast.loc *Tast.ttyp *Ast.loc)
        exception Erreur_types_non_egaux of (Tast.ttyp *Ast.loc * Tast.ttyp)  
        exception Erreur_mut of  Ast.loc
        exception Erreur_vide of Ast.loc
        exception Erreur_lvalue of Ast.loc
        exception Erreur_len of (int * int *Ast.loc) 
        exception Erreur_no_expr of  Ast.loc
        exception Erreur_types_non_coherents of (Tast.ttyp * Ast.loc * Tast.ttyp * Ast.loc)
        exception Erreur_non_declare of (Tast.ttyp * Ast.loc)
        exception Erreur_borrow of Ast.loc
        exception Erreur_struct_call of (Tast.ttyp * ident * Ast.loc)
        exception Erreur_not_mutable of Ast.loc 
	exception Erreur_non_definie of ident

	



module Smap = Map.Make (String)
module Sset = Set.Make (String) 

type env = (string,int*bool*ttyp*int) Smap.t (*numero, mut, type, profondeur *)

let num_table= Hastbl.create 16

let new_num_ident id =
   let num = try Hastbl.finc num_table id
   with Not_found -> 0
   in 
   Hastbl.replace num_table id (num +1) ;
   num 

(*TODO les hashtbl, le e.x avec l histoire de regarder si ce st dans l ident *)
(* penser à la loc dans AST *)
(* def la fonction check_bf *)
(* def la fonction check_unit, Type_no_struct, type_no_borrow, check_in, regarder si c'est une permu, Saff *)

let rec deref_type t = match t with
   |Tref (m, t1) -> deref_type t1
   |_ -> t

   
and type_adapte (t1, t2) =
   let a = deref_type t1 in
   let b= deref_type t2 in
   match a with
      |b -> true
      |_ -> false

and rec get_typ_arguments = function
  |[] -> []
  |a::q -> let _,_,t = a in (find_typ t)::(get_typ_arguments q)

and compute_types_fun = function
  |[] ->()
  |a::q ->
    begin
      match a with
      |Ddecl_struct s -> compute_types_fun q
      |Ddecl_fun f ->
        Hashtbl.add t_functions f.name (find_typ_fun f.typ);
        Hashtbl.add t_args_functions f.name (get_typ_arguments f.arguments);
        compute_types_fun q
    end

and type_prog p =
  compute_types_fun p;
  type_prog_after_init p
   
and type_prog_after_init = function
  |[] -> []
  |a::q ->
    begin
      match a with
      |Ddecl_struct s -> type_prog q
      |Ddecl_fun f -> (TDdecl_fun (type_fun f))::(type_prog q)
    end
and type_fun f =
  let env = Hashtbl.create 16 in
  let l_args = add_args f.arguments env in
  let t = find_typ_fun f.typ in
  let b = type_fun_bloc env t f.body in
  {name = f.name;
   arguments = l_args;
   body = b;
   typ = t;}
  
and find_typ_fun t = match t with
  |None -> Tunit
  |Some t1 -> find_typ t1
  
and find_typ t = match t with
  |Tid id ->
    begin
      match id with
      |"i32" -> Tint
      |"bool" -> Tbool
      |_ -> Tstruct id
    end
  |Tcons (id, t1) ->
    if id <> "Vec" then
      failwith "Mauvais type"
    else
      Tvec (find_typ t1)
  |Tesp (m,t1) ->
    Tref (m, find_typ t1)
    
and find_expr env depth id =
  let (n,m,t,d) = Hashtbl.find env id in
  if d > depth then
    (Hashtbl.remove env id; find_expr env depth id)
  else
    (n,m,t)

and add_args l env = match l with
  |[] -> []
  |a::q -> let m,id,t = a in
           let n = new_num_ident id in
           let t1 = find_typ t in
           Hashtbl.add env id (n,m,t1,0);
           (m,(id,n),t1)::(add_args q env)
           

(*let rec type_bf env (e)=
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
         end *)

 and type_arg_comparaison_list  (list_typ, list_expr) =
   match list_typ with 
      |[] ->  begin match list_expr with
         |[] -> true
	 (*| false -> (raise (Erreur_len (e.length , a.length, snd e)) *)
	 end
      | x::[]-> begin match list_expr with 
         |y::[] -> 
            let r =type_adapte (y, snd x) in
            begin match r with
               | true -> true (* Une valeur random pour verifier *)
               | false -> raise (Erreur_types_non_egaux ((snd x), snd (fst x) , y )) 
            end
	 (*| false -> (raise (Erreur_len (e.length , a.length, snd e)) *)
         end
      | x::y::q -> begin match list_expr with 
         |w::z::o -> 
            let r = type_adapte (w, snd x) in
            begin match r with
               |true-> 
                  let r1 = type_adapte (z, snd y) in
                  begin match r1 with
                     |true  -> type_arg_list (y::q , z::o)
                     (*|false-> raise (Erreur_types_non_egaux (snd y,snd (fst y) , z ))*)
                  end
            (*| false-> raise (Erreur_types_non_egaux (snd x , snd (fst x) ,w )) *)
	    end
	 (*| false e-> (Erreur_len (e.length , a.length, snd e)) *)
         end
   
and type_arg_list (list_typ, list_expr ) =
   match list_typ with 
      |[]->  true
      | x::[]-> begin match list_expr with 
         |y::[] -> begin match snd x with
            | y -> true (* Une valeur random pour verifier *)
            (*| _ -> raise (Erreur_types_non_egaux (snd x, snd (fst x) , y )) *) 
         end
      end 
      | x::y::r -> begin match list_expr with 
         |w::z::o -> begin match snd x with
            | w -> begin match snd y with
               | z -> type_arg_list (y::r , z::o)
               (*|_ -> raise (Erreur_types_non_egaux (snd y , snd (fst y) , z )) *)
            end
            (*|_ -> raise (Erreur_types_non_egaux (snd x , snd (fst x) , w )) *)
         end
      end 

and type_mut_expr env depth (e) = match e with 
   |Eident name -> 
      let (n,m,t) =
         begin 
	    try find_expr env depth i
	    with Not_found -> raise (Erreur_non_definie i )
	 end
         begin match m with 
            |true -> (TEident (name, n), t, true) 
            (*|false -> raise ( Erreur_not_mutable ( name)) (* should renvoie la loc de name *) *)
         end
      in
   |Eselect (e1, e2) ->
      let (s, e1t, b) as e1type = type_mut_expr env depth (e1)  in 
      let (s2, e2t) as e2type = type_expr env depth (e2 ) in
      let t1 = deref_type e1t in 
      begin match t1 with 
         |Tvec(a) -> begin match e2t with 
            |Tint -> (TEselect ((s, e1t), (s,e2t)), t1, b) (*Il ya un probleme ce ne doit pas etre s la deuxieme mais s2 et dans l'erreur pas e2 *)
            (* |_ -> raise (Erreur_typage (e2t, Tint, )) *)
            end
        (* |_ -> raise (Erreur_typage (t1, Tvec() , snd e1)) (* should be Tvec de n'importe quoi *) *)
      end 
   
   (*|Eattribute (e, i) ->
      let (_,et, b) as etype = type_mut_expr env e in
      let t1 = deref_type et in
      begin match t1 with 
         |Tstruct  -> 
            let t = check_in (et, i) in
            (* TODO regarder si i est dans la struct associée à e avec une fonction qui renvoie le type associé a i et raise error sinon *)
            (TEattribute (etype, ident), t, b)
         |_ -> raise (Erreur_typage (et, Tstruct, snd e))
      end *)
   |Eunop (unop, e) ->
      begin match unop with
         |Deref ->
            let (a, et, b) as etype = type_mut_expr env depth (e) in
            begin match et with 
               |Tref (_, t) ->
                  let t1 = deref_type t in
                  (TEunop (unop, (a, et)), t , b)
               (* |_ -> raise (Erreur_typage (et, Tref, snd e)) *) (* trouver les arg de Tref *)
            end
      end
   (*|_ -> raise (Erreur_mut (e, snd e)) *)

 
      
and type_lvalue_expr env depth (e) = match e with 
   |Eident name -> 
       let (n,m,t) =
         begin 
	    try find_expr env depth i
	    with Not_found -> raise (Erreur_non_definie i ) 
         end
       (TEident (name, n), t)
   |Eunop (unop, e) ->
      begin match unop with 
         |Deref -> 
            let (_, et) as etype = type_expr env depth e in
            begin match et with
               |Tref (_, t) -> 
                  let t1 = deref_type t in
                  (TEunop (unop, etype) , t1)
             (*|_-> raise ( Erreur_typage (et , Tref, snd e)) *)
            end
      end 
     |Eselect (e1 , e2) ->
      let (s, e1t) as e1type =type_lvalue_expr env depth (e1) in
      let (s2, e2t) as e2type =type_expr env depth (e2) in
      let t1 = deref_type e1t in
      begin match t1 with 
         |Tvec (a) -> begin match e2t with
            |Tint -> ( TEselect (( s, e1t ), (s ,e2t)), t1 ) (*Il ya un probleme ce ne doit pas etre s la deuxieme mais s2 et dans l'erreur pas e2 *)
            (*| _-> raise ( Erreur_typage (e2t, Tint, snd e2))*)
            end
         (*| _-> raise ( Erreur_typage (e1t, Tvec, snd e1))*)
      end 
  (*|Eattribute (e, i) ->
      let (_, et) as etype = type_lvalue_expr env e in
      let t1 = deref_type et in
      begin match t1 with 
         |Tstruct  -> 
            let t = check_in (et, i) in
            (* TODO regarder si i est dans la struct associée à e avec une fonction qui renvoie le type associé a i et raise error sinon *)
            (TEattribute (etype, ident), t)
         |_ -> raise (Erreur_typage (et, Tstruct, snd e))
      end
   |Saff (m, i, i1, s) ->
      (*let a = find.hastbl (i) in(* TODO codercette hastbl *)
      begin match a.length with 
         |1 ->
            let r =type_arg_list env (snd s (*ici c est e *), find.hastbl (i)) in
            begin match r with 
               |true -> (* regarder si c est bien une permutation  *) 
                  
            end
         |_ -> raise ( Erreur_len (s.length , a.length, snd s ))
      end
   |_ -> (Erreur_lvalue (e, snd e)) *)  *)
   
and type_expr env depth (e) = match e with 
   |Eint n -> (TEint n, Tint)
   |Ebool b -> (TEbool b, Tbool)
   |Eunop ( unop , e) -> 
      begin match unop with 
         |Deref -> (*verifie si ce n'est pas une lvalue car lvalue implique value *)
            let (_, et) as etype = type_expr env depth e in
            begin match et with
               |Tref (_, t) -> 
                  let t1 = deref_type t in
                  (TEunop (unop, etype) , t1)
               (*|_-> raise ( Erreur_typage (et , Tref, snd e)) *)
            end
         |UMinus ->
            let (_, et) as etype=type_expr env depth e in
            begin match et with
               |Tint -> (TEunop ( unop , etype), Tint)
               (*| _-> raise ( Erreur_typage ( et,   Tint , snd e )) *)
            end
         |Not ->
            let (_, et) as etype =type_expr env depth e in
            begin match et with 
               | Tbool -> (TEunop (unop, etype ),Tbool)
               (*| false -> raise ( Erreur_typage ( et, Tbool , snd e))*)
            end
         
         |SharedBorrow ->
            let (_, et) as etype =type_lvalue_expr env depth e in
            (TEunop (unop, etype), Tref (false, et) )
         
         |MutBorrow -> 
            let (a, et, b) as etype = type_mut_expr env depth e in
            begin match b with
               (*|false -> raise ( Erreur_mut (e , loc)) *)
               |true -> (TEunop (unop, (a, et)), Tref (b, et)) 
            end
      end 
   |Ebinop (e1, op , e2) ->
      begin match op with 
         | Equal | Not_equal | Less | Greater | Less_or_equal
         | Greater_or_equal  ->
            let (_, e1t) as e1type =type_expr env depth e1 in
            let (_, e2t) as e2type =type_expr env depth e2 in
            begin match e1t with
               |Tint -> begin match e2t with 
                  |Tint -> (TEbinop (e1type, op , e2type), Tbool)
                  (*|_ -> raise ( Erreur_typage (e2t, Tint, snd e2))*)
                  end
               (*|_ -> raise ( Erreur_typage (e1t, Tint , snd e1))*)
            end
         | Plus | Minus | Times | Divide | Modulo ->
            let (_, e1t) as e1type =type_expr env depth e1 in
            let (_, e2t) as e2type =type_expr env depth e2 in
            begin match e1t with
               |Tint -> begin match e2t with 
                  |Tint -> (TEbinop ( e1type, op , e2type ), Tint)
                  (*| _-> raise ( Erreur_typage (e2t, Tint, snd e2))*)
                  end
              (*|_ -> raise ( Erreur_typage (e1t, Tint, snd e1))*)
            end
         | And | Or ->
            let (_, e1t) as e1type =type_expr env depth e1 in
            let (_, e2t) as e2type =type_expr env depth e2 in
            begin match e1t with
               |Tbool -> begin match e2t with 
                  |Tbool -> (TEbinop (e1type , op, e2type ), Tbool)
                  (*| _-> raise ( Erreur_typage ( e2t, Tbool , snd e2))*)
                  end
               (*|_ -> raise ( Erreur_typage ( e1t, Tbool, snd e1 ))*)
            end
         
         | Affect -> 
            let (structure, e1t, b) as e1type =type_mut_expr depth env e1 in 
            let (_, e2t) as e2type =type_expr env e2 in
            let r = type_adapte (e1t, e2t) in
            begin match r with
               |true -> 
                  begin match b with 
                     (*|false -> raise ( Erreur_mut (e1 , loc))*)
                     |true -> (TEbinop ((structure, e1t), op, e2type), Tunit ) 
                  end
               (*|false -> raise (Erreur_types_non_coherents (e1, snd e1, e2, snd e2))*)
            end
      end 
      
   |Elen e ->
      let (_, et) as etype =type_expr env depth e in
      let t1 = deref_type et in
      begin match t1 with 
         |Tvec (a) -> (TElen etype  , Tint )
         (*|_ -> raise ( Erreur_typage ( et, Tvec , snd e)) *)
      end      
  
   |Evect e ->
     let (structure, t)= type_list env depth e in
     (TEvect (structure), t)

   |Eprint s -> (TEprint s , Tunit)
  
   |Ecall (f, l) -> 
      let l_ref = Hashtbl.find t_args_functions f in
      let l = Hastbl.find t_functions f in
      let l_targs = type_args env deptg l in
      let r = type_arg_comparaison_list (l_targs l_tref) in
      match r with 
         |true -> (TEcall (f, l), t)

  (* tout ce qui suit permet de vérifier si l'expression n'est pas une l value car implique que c'est une value normale *)*)
   |Eident name -> 
       let (n,m,t) =
         begin 
	    try find_expr env depth i
	    with Not_found -> raise (Erreur_non_definie i ) 
         end
       (TEident (name, n), t)
 
   |Eselect (e1 , e2) ->
      let (_, e1t) as e1type =type_lvalue_expr env depth e1 in
      let (_, e2t) as e2type =type_expr env depth e2 in
      let t1 = deref_type e1t in
      begin match t1 with 
         |Tvec a -> begin match e2t with
            |Tint -> ( TEselect ( e1type , e2type ), e1t ) 
            (*| _-> raise ( Erreur_typage (e2t, Tint, snd e2))*)
            end
         (*| _-> raise ( Erreur_typage (e1t, Tvec, snd e1))*)
      end 
   (*|Eattribute (e, i) ->
      let (_, et) as etype = type_lvalue_expr env e in
      let t1 = deref_type et in
      begin match t1 with 
         |Tstruct a -> 
            let t = check_in (et, i) in
            (* TODO regarder si i est dans la struct associée à e avec une fonction qui renvoie le type associé a i et raise error sinon *)
            (TEattribute (etype, ident), t)
         (*|_ -> raise (Erreur_typage (et, Tstruct, snd e)) *)
      end*)
   (*|Sobj (m, i, i1, s) ->
      let a = find.hastbl (i) in(* TODO codercette hastbl *)
      begin match a.length with 
         |s.length ->
            let r =type_arg_list env (snd s (*ici c est e *), find.hastbl (i)) in
            begin match r with 
               |true -> (* regarder si c est bien une permutation ! *) 
                  
            end
         |_ -> raise ( Erreur_len (s.length , a.length, snd s ))
      end *)
   (*|_ -> raise (Erreur_no_expr (e, snd e)) *)
  
and type_if env depth ( p ) = match p with 
   |Aif ( e, b) -> 
      let (s, et ) as etype =type_expr env depth e in 
      let (structure, bt) as btype = type_bloc env (depth+1) b in
      free_env env depth ;
      begin match et with 
         |Tbool -> (TAif (etype, structure)), env
         (* |_-> raise ( Erreur_typage (et, Tbool, e)) *)
      end
   |Bif ( e, b1 , b2) ->
      let (_, et ) as etype = type_expr env depth e in 
      let (structure, b1t) as b1type = type_bloc env (depth+1) b1 in
      free_env env depth ;
      let (structure2, b2t) as b2type = type_bloc env (depth+1) b2 in 
      free_env env depth;
      begin match et with 
         |Tbool -> begin match b1t with 
            |b2t -> (TBif (etype, structure , structure2)), env
            (*|_ -> raise (Erreur_types_non_egaux ( b1type, snd b1, b2type, snd b2)) *)
         end
         (*|_-> raise ( Erreur_typage (etype, Tbool, snd e)) *)
      end
   |Iif (e, b, c) ->
      let (structure_c, ct) as ctype = type_if env depth ( c) in
      let (_, et ) as etype = type_expr env depth e in 
      let (structure_b, bt) as btype = type_bloc env (depth+1) b in 
      free_env env depth ;
      begin match et with 
         |Tbool -> begin match bt with 
            |ct -> (TIif (etype, structure_b, structure_c)), env 
            (*|_ -> raise ( Erreur_types_non_egaux (btype, snd b , ctype, snd c)) *)
         end
         (*|_ -> raise (Erreur_typage (etype, Tbool, snd e))*)
      end 

and type_stmt env depth (s ) = match s with
   |Unit -> TSUnit
   |Sexpr e ->
      let (_, et) as etype= type_expr env depth e in
      (TSexpr (etype)),env
      
        
   |Sreturn e -> 
      begin match e with 
         |None -> (TSreturn None ), env
         |Some e1 -> 
            let (_,e1t) as e1type=type_expr env depth e1 in
            (TSreturn (Some  (e1type))), env 
      end 
   |Swhile ( e, e1 ) ->
      let (_, et) as etype =type_expr env depth e in
      let (structure_statements, type_expr_finale) as e1type = type_bloc env (depth +1) e1 in 
      begin match et with 
         |Tbool -> begin match type_expr_finale with
            |Tunit -> (TSwhile (etype, structure_statements)), env 
            (*|_ -> raise ( Erreur_typage (e2type, Tunit , snd e1 ))*)
            end
         (*|_ -> raise ( Erreur_typage (etype, Tunit , snd e))*)
      free_env env depth
      end 
   |Sif s -> 
      let (structure ,st) as stype = type_if env depth s in
      (TSif (structure)), env
      
   |Saff (m, id, expr) ->
      let n = new_num_ident id in
      let te = type_expr env depth expr in
      Hastbl.add env id (n, m, (snd te) , depth ) ;
      TSaff (m, (id, n) ,te)
     

and type_bloc env depth (p) = match p with 
   |Ubloc (liste_stmt) -> 
      let (a) = type_u_bloc env (depth+1) (liste_stmt) in
      (TUbloc (a), Tunit) 
   |Vbloc (liste_stmt, e_f) ->
      let (_, et) as etype = type_expr env (depth+1) e_f in
      let (a,b) =type_v_bloc env (depth+1) (liste_stmt, e_f) in
      (TVbloc (a,b), et)          

and type_u_bloc env depth (liste_instru) = match liste_instru with
   |[] -> ([])
   |instr::q -> 
      let (h, ht) = type_stmt env depth (instr) in
      let r =type_u_bloc env depth (q) in
      (h::r ) 

and type_v_bloc env depth (liste_instr, e_finale) = match liste_instr with
   |[] ->
      let (_, et) as etype =type_expr env depth (e_finale) in
      ([], etype) 
   |instr::q -> 
      let (h, ht)=type_stmt env depth (instr) in
      let (r, rtype) = type_v_bloc env depth (q, e_finale ) in
      (h ::r, rtype)
   |Saff (m, id, expr) ->
      let n = new_num_ident id in
      let te = type_expr env depth expr in
      Hastbl.add env id (n, m, (snd te) , depth ) ;
      TSaff (m, (id, n) ,te)
            
         (*|Saff (m, x, i, i1)-> (* TODO Saff *)
            let (structure, et) as stype =type_stmt env i1 in (* a verifier + finir *)
            let (structure_bloc, bt) as btype=type_bloc nouvel_environnement (q, e_finale) in
            
            (structure :: structure_bloc, bt) *)

and structure_list_with_constraint env depth li_expr type_cible = match li_expr with
   | [] -> []
   | x::q -> 
       let (structure_x, type_pur_x) as etype = type_expr env depth (x) in
       begin match type_cible with
          |structure_x -> etype :: (structure_list_with_constraint env depth q type_cible)
          (*| _ -> raise (Erreur_typage (type_pur_x, type_cible, snd x)) *)
       end  


and type_list env depth li_expr = match li_expr with
   | [] -> ([], Tvec (Tunit))
   | x::q -> let (structure_x, type_pur) as etype = type_expr depth env (x) in
       (etype :: (structure_list_with_constraint env depth q type_pur), Tvec (type_pur)) 

