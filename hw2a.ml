exception ImplementMe

(* Problem 5 *)  
  
(* Type t represents abstract syntax trees for the lambda calculus.  A
variable name is represented as an OCaml string. We include the value
True so that you have a simple value to use for testing purposes.

Example: the term ((function x -> x x) (function x -> x)) would be represented as follows:

   FunCall(Function("x", FunCall(Var "x", Var "x")), Function("x", Var "x"))

*)

type t = True | Var of string | Function of string * t | FunCall of t * t

let isval t =
  match t with
      True -> true
    | Function (str, t) -> true
    | _ -> false

(* 5a: Implement the subst function below, which substitutes a given
   value v for all free occurrences of the variable named x in term t,
   returning the resulting term. You may assume that v has no free
   variables. *)

let rec subst (x:string) (v:t) (t:t) = 
	match t with
	| True -> True
	| Var r -> if (r=x) then v else t
	| Function (str, t1) -> if (str=x) 
		then  Function (str, t1)
		else Function(str, subst x v t1) 
	| FunCall (t1,t2) -> FunCall (subst x v t1,subst x v t2);;


  
(* 5b: Implement the step function, which takes a term of type t above
and produces a new term that results from taking one step of
computation on t.  If t is a normal form, the step function should
raise the NormalForm exception declared below. *)

exception NormalForm  

let rec step t = match t with
	| FunCall (t1 , t2) -> (match t1 with
		|Function (str , t3) -> (match isval t2 with
				| true -> subst (str) (t2) (t3)
				| false -> FunCall ( t1, step t2))
		| _ -> FunCall (step (t1) , t2))
	| _ -> raise NormalForm;; 