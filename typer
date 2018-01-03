open Ast

module Smap = Map.Make (String)
module Sset = Set.Make (String) 



let type_expr env = function 
   |Eint n -> Tint
   |Ebool b -> Tbool 
   |Eunop ( unop , e) -> 
      | begin match unop with 
         |UMinus ->
            begin match e with 
               |Tint -> Tint
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
                  |Tint -> Tint
                  | -> failwith "erreur : e2 doit être un entier pour utiliser des opérations arithmétiques dessus"
               | -> failwith "erreur : e1 doit être un entier pour utiliser des opérations arithmétiques dessus "
         | And | Or ->
            begin match e1 with
               |Tbool -> begin match e2 with 
                  |Tbool -> Tbool
                  | -> failwith "erreur : e2 doit être un booléen pour utiliser And ou Or dessus"
               | -> failwith "erreur : e1 doit être un booléen pour utiliser And ou Or"
           
            
         
         
       
