(* T ::= Bool | T -> T *)
type typ = Bool | Arrow of typ * typ

(* t ::= true | false | if t then t else t | x | lambda x:T.t | t1 t2 *)
type t = True | False | If of t * t * t
	   | Var of string | Function of string * typ * t | FunCall of t * t


(* env is a **type alias** for a list of (string,typ) pairs 
   env is not a new type, like t above, 
   but rather just a name for an existing type. 

   a list of pairs is sometimes called an *association* list.
   OCaml already has some useful operations for manipulating such lists.
   In particular, the function List.assoc (in the List standard library)
   looks up the value associated with a given key in a given association
   list.  e.g., List.assoc "y" [("x", Bool); ("y", Arrow(Bool,Bool))]
   returns Arrow(Bool,Bool).  List.assoc raises a Not_found exception
   if the given key is not in the list.

*)
type env = (string * typ) list

exception TypeError

(* typecheck takes a term (of type t) and a type environment (of type env) 
   and it returns the type of the term, or raises TypeError if the term
   cannot be given a type.  this function should have the same behavior
   as the typechecking rules on the cheat sheet. *)
let rec typecheck (t:t) (env:env) : typ = match t with
	| True -> Bool
	| False -> Bool
	| If (t1, t2, t3) -> ( match ((typecheck t1 env) = Bool) with
		| true -> (match ((typecheck t2 env) = (typecheck t3 env)) with
			| true -> typecheck t2 env
			| false -> raise TypeError)
		| false -> raise TypeError )
	| Var str -> ( match env with
		| [ ] -> raise TypeError
		| hd::tl -> (match hd with
			| (name , envtp) -> if (str = name) then envtp else (typecheck t tl) ) )
	| Function (str, ftp, ft) -> (Arrow (ftp , typecheck ft ((str,ftp)::env)))
	| FunCall (t1 , t2) -> ( match (typecheck t1 env) with
		| Arrow (at1 , at2) -> if ((typecheck t2 env) = at1) then (at2) else raise TypeError
		| _ -> raise TypeError )
