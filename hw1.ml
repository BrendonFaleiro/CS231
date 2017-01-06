exception ImplementMe
(*Big Step Semantics*)
type t = True | False | If of t * t * t | Int of int | Plus of t * t | Greater of t * t

let isval t =
  match t with
      True|False -> true
    | Int _ -> true
    | _ -> false

(* Problem 1a.*)

exception NormalForm 

let rec step t =
  match t with
    | If(True,t2,t3) -> t2 
    | If(False,t2,t3) -> t3 
    | If(t1,t2,t3) -> If(step t1, t2, t3) 
    | Plus(Int n1, Int n2) -> Int (n1 + n2)
    | Plus(t1, t2) when isval t1 -> Plus(t1, step t2)
    | Plus(t1, t2) -> Plus(step t1, t2)
    | Greater(Int n1, Int n2) -> if n1 > n2 then True else False
    | Greater(t1, t2) when isval t1 -> Greater(t1, step t2)
    | Greater(t1, t2) -> Greater(step t1, t2)
    | _ -> raise NormalForm
        

(* Problem 1b. *)

let rec eval t =
  try
    let t' = step t in
      eval t'
  with
      NormalForm -> t



