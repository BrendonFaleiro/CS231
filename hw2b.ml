exception ImplementMe

(* Problem 6 *)  

(* As you saw in Problem 5, implementing the lambda calculus, and any
other language that has variables, is annoying, because you have to
manually implement the proper scoping rules, in our case via a
substitution function.

An alternative style, known as higher-order abstract syntax (HOAS), is
a clever way to use variables from the host language (in our case,
OCaml) to represent variables in the language being implemented (in
our case, the lambda calculus).  That way, we get substitution for
free!  You will explore this style below...

*)
   
  
(* Type t represents abstract syntax trees for the lambda calculus.
We are only representing the subset of *closed* terms in the lambda
calculus -- HOAS cannot handle terms with free variables in them.
Note that we no longer have a term for variables below.  Instead,
variables are represented implicitly via the fact that a lambda
calculus function is represented as an OCaml function from terms to
terms (hence the notion of higher-order syntax -- the syntax tree
contains functions).
   
Example: the term ((function x -> x x) (function x -> x)) would be represented as follows:

   FunCall(Function(function x -> FunCall(x, x)), Function(function x -> x))

*)

type t = True | Function of (t -> t) | FunCall of t * t

let isval term = match term with
	| True -> true
	| Function t1  -> true
	| _ -> false

(* Implement the step function, which takes a term of type t above and
   produces a new term that results from taking one step of
   computation on t.  If t is a normal form, the step function should
   raise the NormalForm exception. *)

exception NormalForm  

let rec step t = match t with
	| FunCall (t1 , t2) -> (match t1 with
		| Function t3 -> (match isval t2 with
				| true -> t3 t2
				| false -> FunCall ( t1, step t2))
		| _ -> FunCall (step (t1) , t2))
	| _ -> raise NormalForm;; 
