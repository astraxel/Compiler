open Ast

module Smap = Map.Make (String)
module Sset = Set.Make (String) 

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

let type_expr env (e , loc ) = match e with 
   |Eint n -> (TEint n, Tint)
   |Ebool b -> (TEbool b, Tbool)
   |Eunop ( unop , e) -> 
      | begin match unop with 
         |UMinus ->
            begin match e with 
               |Tint -> 
               | -> failwith "erreur : e doit être un entier pour lui appliquer UMinus "
         |Not ->
            begin match e with 
               | Tbool -> Tbool
               | -> failwith "erreur : e doit être un booléen pour lui appliquer Not "
   |Ebinop (e1, op , e2) ->
     begin match op with 
        | Equal | Not_equal | Less | Greater | Less_or_equal
        | Greater_or_equal  ->
           begin match e1 with
              |Tint -> begin match e2 with 
                 |Tint -> Tbool
                 | -> failwith "erreur : e2 doit être un entier pour le comparer avec e1"
              | -> failwith "erreur : e1 doit être un entier pour le comparer avec e2 "
         
         | Plus | Minus | Times | Divide | Modulo -> 
            begin match e1 with
               |Tint -> begin match e2 with 
                  |Tint -> (TEbinop ((_, type_exp env e1), op , (_, type_expr env e2)), Tint)
                  | -> failwith "erreur : e2 doit être un entier pour utiliser des opérations arithmétiques dessus"
               | -> failwith "erreur : e1 doit être un entier pour utiliser des opérations arithmétiques dessus "
         | And | Or ->
            begin match e1 with
               |Tbool -> begin match e2 with 
                  |Tbool -> Tbool
                  | -> failwith "erreur : e2 doit être un booléen pour utiliser And ou Or dessus"
               | -> failwith "erreur : e1 doit être un booléen pour utiliser And ou Or"
           
   |Elen e ->
      begin match e with 
         |Tvec -> Tint
         | -> failwith "erreur : e doit être une liste pour utiliser len dessus "
   
   |Eselect (e1 , e2) ->
      begin match e1 with 
         |Tvec -> begin match e2 with
            |Tint -> Tint
            | -> failwith "erreur : e2 doit être un entier "
         | -> failwith "erreur : e1 doit être un vecteur pour faire e1 [e2] "
   (* valeur gauche *)
   
   |Evect (
         
         
       
