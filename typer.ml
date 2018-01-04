open Ast

module Smap = Map.Make (String)
module Sset = Set.Make (String) 

(*
exception Erreur_typage of typ * typ * startpos * endpos
*)

type env = {
   dec_vars : typ Smap.t ; (* associe à chaque variable son type *)
   dec_typs : typ SImap.t ; (* associe à chaque variable dont le type est déclarée le type qu'elle dénote *)
   def_recs : (typ Smap.t) SImap.t;
   def_funs : ((mode * typ) list * typ) Smap.t (*associe à chaque fonction son type de retour, la liste du type 
                                                * et du mode de sesargs *)
   const_vars : Sset.t ;
   for_vars : Sset.t ;
   idents : (dtyp * int ) Smap.t ;
   return_value : typ ;
   level : int ;
   nb_incomplete : int ;
}

let type_expr env (e , startpos, endpos ) = match e with 
   |Eint n -> (TEint n, Tint)
   |Ebool b -> (TEbool b, Tbool)
   |Eunop ( unop , e) -> 
      | begin match unop with 
         |UMinus ->
            let (_, et) as etype =type_expr env e in 
            begin match et with 
               |Tint -> (TEunop ( unop , etype), Tint) 
               | -> raise ( Erreur_typage ( et,   Tint , snd e ))
         |Not ->
            let (_, et) as etype =type_expr env e in
            begin match et with 
               | Tbool -> (TEunop (unop, etype ),Tbool)
               | -> raise ( Erreur_typage ( et, Tbool , snd e))
   |Ebinop (e1, op , e2) ->
      let (_, e1t) as e1type =type_expr env e1 in
      let (_, e2t) as e2type =type_expr env e2 in
      begin match op with 
         | Equal | Not_equal | Less | Greater | Less_or_equal
         | Greater_or_equal  ->
            begin match e1t with
               |Tint -> begin match e2t with 
                  |Tint -> (TEbinop (e1type, op , e2type), Tbool)
                  | -> raise ( Erreur_typage (e2t, Tint, snd e2))
               | -> raise ( Erreur_typage (e1t, Tint , snd e1))
         
         | Plus | Minus | Times | Divide | Modulo -> 
            begin match e1t with
               |Tint -> begin match e2t with 
                  |Tint -> (TEbinop ( e1type, op , e2type ), Tint)
                  | -> raise ( Erreur_typage (e2t, Tint, snd e2)
               | -> raise ( Erreur_typage (e1t, Tint, snd e1))
         | And | Or ->
            begin match e1t with
               |Tbool -> begin match e2t with 
                  |Tbool -> (TEbinop (e1type , op, e2type ), Tint)
                  | -> raise ( Erreur_typage ( e2t, Tbool , snd e2))
               | -> raise ( Erreur_typage ( e1t, Tbool, snd e1 ))
           
   |Elen e ->
      let (_, et) as etype =type_expr env e in
      begin match et with 
         |Tvec -> (TEvect e , Tint )
         | -> raise ( Erreur_typage ( et, Tvec , snd e))
            
   |Eselect (e1 , e2) ->
      let (_, e1t) as e1type =type_expr env e1 in
      let (_, e2t) as e2type =type_expr env e2 in
      begin match e1t with 
         |Tvec -> begin match e2t with
            |Tint -> ( TEselect ( e1type , e2type ), e1type ) (* renvoie un type de genre type*list au lieu de type *)
            | -> raise ( Erreur_typage (e2t, Tint, snd e2))
         | -> raise ( Erreur_typage (e1t, Tvec, snd e1))
   (* valeur gauche *)
   
   |Evect (
         
         
       
