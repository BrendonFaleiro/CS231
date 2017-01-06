Require Import SfLib.
(* PROBLEM 3: Functions and Proofs *)

(* We saw these types and functions in class. *)

Inductive bool : Type :=
  true : bool
| false : bool.

Inductive nat : Type :=
  zero : nat
| succ : nat -> nat.


Fixpoint plus (n1 n2 : nat) :=
  match n1 with
      zero => n2
    | (succ n1') => succ(plus n1' n2)
  end.

(* Problem 3a: Prove the following theorem about addition. *)

Theorem plus_n_Sm : forall n m : nat, 
  succ (plus n m) = (plus n (succ m)).

Proof.
intros n. intros m. induction n as [|n'].
Case "n=zero". simpl. reflexivity.
Case "n=succ n'". simpl. rewrite IHn'. reflexivity.
Qed.

(* Problem 3b: Define a function leq that performs "less than or equal" on natural numbers *)

Fixpoint leq (n1 n2 : nat) : bool :=
  match n1 with
    zero => true
  | (succ n1') =>
    match n2 with
      zero => false
    | (succ n2') => leq n1' n2'
    end
  end.

(* Problem 3c: Prove this theorem that relates leq and plus. *)

Lemma plusLeqLeft : forall n m, leq n (plus n m) = true.

Proof.
intros n. intros m. induction n as [|n'].
Case "n=zero". simpl. reflexivity. 
Case "n=succ n'". simpl. rewrite IHn'. reflexivity.
Qed. 

(* PROBLEM 4: CS231 All Over Again *)

(* Problem 4a: Add the syntax for integer constants (making use of the nat type defined earlier) and integer addition
    to our grammar, i.e.: 
      t ::= ... | n | t1 + t2
*)

Inductive term : Type :=
| t_unit  : term
| t_true  : term
| t_false : term
| t_if    : term -> term -> term -> term
| t_num   : nat -> term
| t_plus  : term -> term -> term.

(* Problem 4b: Add the type Int for integers to our definition of types below. *)

Inductive ty : Type :=
| Unit : ty
| Bool : ty
| Int  : ty.



(* Problem 4c: Add typing rules for your new terms. *)

Inductive typeof : term -> ty -> Prop :=
| tcUnit  : typeof t_unit Unit
| tcTrue  : typeof t_true Bool
| tcFalse : typeof t_false Bool
| tcIf    : forall t1 t2 t3 T, typeof t1 Bool -> typeof t2 T -> typeof t3 T -> typeof (t_if t1 t2 t3) T
| tcNum   : forall n, typeof (t_num n) Int
| tcPlus  : forall t1 t2, typeof t1 Int -> typeof t2 Int -> typeof (t_plus t1 t2) Int.

Notation "t : T" := (typeof t T) (at level 40). 

(* Problem 4d: Add integer constants as a kind of value. *)

Inductive isValue : term -> Prop :=
| unitVal  : isValue t_unit
| trueVal  : isValue t_true
| falseVal : isValue t_false
| numVal   : forall n, isValue (t_num n).

(* Problem 4e: Add the operational semantics for your new terms. *)

Inductive step : term -> term -> Prop :=
  | stepIfTrue    : forall t2 t3, step (t_if t_true t2 t3) t2
  | stepIfFalse   : forall t2 t3, step (t_if t_false t2 t3) t3
  | stepIf :
    forall t1 t1' t2 t3,
      step t1 t1' -> step (t_if t1 t2 t3) (t_if t1' t2 t3)
  | stepPlusVals  : forall n1 n2, step (t_plus (t_num n1) (t_num n2)) (t_num (plus n1 n2))
  | stepPlusRight : forall n1 t2 t2', step t2 t2' -> step (t_plus (t_num n1) t2) (t_plus (t_num n1) t2')
  | stepPlusBoth  : forall t1 t1' t2, step t1 t1' -> step (t_plus t1 t2) (t_plus t1' t2).

Notation "t1 '-->' t2" := (step t1 t2) (at level 40).


Lemma cfBool : forall v, isValue v -> v : Bool -> v = t_true \/ v = t_false.
Proof.
  intros. inversion H.
  rewrite <- H1 in H0. inversion H0.
  left. reflexivity.
  right. reflexivity.
  rewrite <- H1 in H0. inversion H0.
Qed.

Lemma cfInt : forall v, isValue v -> v : Int -> exists n, v = t_num n.
Proof.
  intros. inversion H.
  rewrite <- H1 in H0. inversion H0.
  rewrite <- H1 in H0. inversion H0.
  rewrite <- H1 in H0. inversion H0.
  exists n. reflexivity.
Qed.

(* Problem 4f: Complete the Progress proof for your language. *)

Theorem progress : forall t T, t : T -> isValue t \/ exists t', t --> t'.
Proof.
  intros. induction H. (* note induction on derivations! *)
    Case "t=unit". left. apply unitVal.
    Case "t = true". left. apply trueVal.
    Case "t = false". left. apply falseVal.
    Case "t = if t1 t2 t3". inversion IHtypeof1. right. apply cfBool in H. inversion H.
      SCase "t1 = true". rewrite -> H3. exists t2. apply stepIfTrue.
      SCase "t1 = false". rewrite -> H3. exists t3. apply stepIfFalse.
      apply H2.
      SCase "t1 steps". inversion H2 as [t1']. right. exists (t_if t1' t2 t3). apply stepIf. apply H3.
    Case "t = n". left. apply numVal.
    Case "t = t1 + t2". right. 
      inversion IHtypeof1. 
      apply cfInt in H1. inversion H1. inversion IHtypeof2.
        SCase "t1 and t2 are values". apply cfInt in H3. inversion H3.
          exists (t_num (plus x x0)). rewrite H2. rewrite H4. apply stepPlusVals. apply H0.
        SCase "t1 is value, t2 steps". inversion H3. exists (t_plus t1 x0). rewrite H2. apply stepPlusRight.
          apply H4. apply H.
        SCase "t1 steps". inversion H1. exists (t_plus x t2). apply stepPlusBoth. apply H2.  
Qed.
      

(* Problem 4g: Complete the Preservation proof for your language. *)

Theorem preservation : forall t t' T, t : T -> t --> t' -> t' : T.
Proof.
  intros. generalize dependent t'. induction H.
  Case "t = unit". intros. inversion H0.
  Case "t = true".
    intros. inversion H0.
  Case "t = false".
    intros. inversion H0.
  Case "t = if t1 t2 t3".
    intros. inversion H2.
    SCase "stepIfTrue". rewrite <- H3. apply H0.
    SCase "stepIfFalse". rewrite <- H3. apply H1.
    SCase "stepIf". apply tcIf. apply IHtypeof1. assumption. assumption. assumption.
  Case "t = t_num". 
    intros. inversion H0.
  Case "t = t1 + t2".
    intros. inversion H1.
    SCase "stepPlusVals". apply tcNum.
    SCase "stepPlusRight". apply tcPlus. apply tcNum. apply IHtypeof2. apply H5.
    SCase "stepPlusBoth". apply tcPlus. apply IHtypeof1. apply H5. apply H0. 
Qed.