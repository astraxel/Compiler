open Ast
open Tast

(*module Idmap = Map.Make (struct type t=tident
                               let compare=
                                 fun x y ->
                                 let (a,b)=x and (c,d)=y in
                                 if a<c then -1
                                 else if a>c then 1
                                 else if b=d then 0
                                 else if b<d then -1
                                 else 1
                         end)*)

module Smap = Map.Make(String)             

type environnement = (string,int*bool*ttyp*int)  Hashtbl.t (*numero, mut, type, profondeur *)

let num_table = Hashtbl.create 16
              
let new_num_ident id =
  let num = try Hashtbl.find num_table id
            with Not_found -> 0
  in Hashtbl.replace num_table id (num+1);
     num
     
let free_env env depth=
  let aux id value =
    let _,_,_,d = value in
    if d>depth then None else Some value
  in
  Hashtbl.filter_map_inplace aux env
         
let rec type_prog = function
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

and add_args l env = match l with
  |[] -> []
  |a::q -> let m,id,t = a in
           let n = new_num_ident id in
           let t1 = find_typ t in
           Hashtbl.add env id (n,m,t1,0);
           (m,(id,n),t1)::(add_args q env)
           
           

and type_fun_bloc env tfun b = match b with
  |Ubloc l -> TUbloc (type_lstmt env true 0 tfun l)
  |Vbloc (l,e) ->
    TUbloc ((type_lstmt env false 0 tfun l)@[(type_stmt env 0 tfun (Sreturn (Some e)))])


(*booleen b indique si on a un traitement particulier du if/de l'expression à la fin*)
and type_lstmt env b depth tfun l = match l with
  |[] -> []
  |[s] -> if b then
            [type_end_stmt env depth tfun s]
          else
            [type_stmt env depth tfun s]
  |s::q -> let s = (type_stmt env depth tfun s)
           in s::(type_lstmt env b depth tfun q)

and type_end_stmt env depth tfun s = match s with
  |Sif i -> let ti = type_end_if env depth tfun i in
            free_env env depth;
            TSif ti
  |_ -> type_stmt env depth tfun s
  
and type_stmt env depth tfun s = match s with
  |Unit -> TSUnit
  |Sexpr e -> TSexpr (type_expr env depth tfun e)
  |Saff (m,id,expr) ->
    let n = new_num_ident id in
    let te = type_expr env depth tfun expr in
    Hashtbl.add env id (n, m, (snd te), depth);
    TSaff (m, (id,n), te)
  |Swhile (e,b) ->
    let te = type_expr env depth tfun e in
    if (snd te) <> Tbool then failwith "mauvais type";
    let tb = type_bloc env (depth+1) tfun b in
    free_env env depth;
    TSwhile (te,tb)
  |Sreturn expr ->
    begin
      match expr with
      |None ->
        if tfun = Tunit then
          TSreturn None
        else
          failwith "Mauvais return"
      |Some e ->
        let te =  type_expr env depth tfun e in
        if tfun = (snd te) then
          TSreturn (Some te)
        else
          failwith "Mauvais return"
    end
  |Sif i -> TSif (type_if env depth tfun i)
  |_ -> assert false

and type_expr env depth tfun e = match e.expr with
  |Eint n -> (TEint n, Tint)
  |Ebool b -> (TEbool b, Tbool)
  |Eident i ->
    let (n,_,t) = 
      begin
        try find_expr env depth i
        with Not_found -> failwith (i^" undefined in this scope")
      end
    in
    TEident (i,n) ,t
  |Ebinop (e1,b,e2) ->
    let te1 = type_expr env depth tfun e1
    and te2 = type_expr env depth tfun e2 in
    type_binop te1 te2 b
  |Eunop (u,e) ->
    let te = type_expr env depth tfun e in
    type_unop te u
  |Ecall (i,l) ->
    assert false
  |Eprint s -> TEprint s, Tunit
  |Ebloc b ->
    let tb = type_bloc env (depth+1) tfun b in
    free_env env depth;
    let t = 
    match tb with
    |TUbloc _ -> Tunit
    |TVbloc (l,e) -> snd e
    in
    TEbloc tb, t
  |_ -> assert false

and type_binop te1 te2 b = match b with
  |Equal | Not_equal | Less | Greater | Less_or_equal| Greater_or_equal ->
    assert ( (snd te1)=Tint && (snd te2)=Tint);
    TEbinop (te1,b,te2), Tbool
  | Plus |Minus | Times | Divide | Modulo ->
     assert ( (snd te1)=Tint && (snd te2)=Tint);
    TEbinop (te1,b,te2), Tint
  | And | Or ->
     assert ( (snd te1)=Tbool && (snd te2)=Tbool);
     TEbinop (te1,b,te2), Tbool
  |Affect ->
    TEbinop (te1,b,te2), Tbool
           
and type_unop te u = match u with
  |Not ->
    assert ((snd te) = Tbool);
    TEunop (u,te), Tbool
  |UMinus ->
    assert ((snd te) = Tint);
    TEunop (u, te), Tint
  |SharedBorrow ->
    TEunop (u,te),Tref (false, (snd te))
  | MutBorrow ->
     TEunop (u,te), Tref (true, (snd te))
  |Deref ->
    begin
      match (snd te) with
      |Tref (m,t) -> TEunop (u,te), t
      |_ -> failwith "déréférencement interdit"
    end
                   
and find_expr env depth id =
  let (n,m,t,d) = Hashtbl.find env id in
  if d > depth then
    (Hashtbl.remove env id; find_expr env depth id)
  else
    (n,m,t)
      
and type_end_if env depth tfun i = assert false

and type_bloc env depth tfun b = match b with
  |Ubloc l -> TUbloc (type_lstmt env false depth tfun l)
  |Vbloc (l,e) -> let tls = type_lstmt env false depth tfun l in
                  TVbloc (tls, type_expr env depth tfun e)

and type_if env depth tfun i = assert false
        
