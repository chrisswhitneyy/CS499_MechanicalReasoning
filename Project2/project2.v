(* Project 2: *)

Require Import Arith ZArith List String WhileStateFun.
Import ListNotations. 


Module Stack.

  Inductive A : Type :=
  | num | inst | empty.

  Inductive t (X:A) : Type := 
  | nil  : t X
  | cons : t X -> t X -> t X.

  Definition pop stack : A := 
    match stack with 
    | a1 :: _ => a1
    | [ ] => empty
    end.
  (* Start of the push function *)
  (* 
  Definition push stack (v:A) : Type :=
   v::stack. *)

End Stack.

(** ** Syntax *)
(* Translated from page 68 in text, where c is represented using lists*)
Inductive inst: Type := 
| PUSH   : Z -> inst
| ADD    | MULT | SUB 
| TRUE   | FALSE 
| EQ     | LE  
| AND    | NEG
| FETCH  : Z -> inst
| STORE  : Z -> inst 
| NOOP   : inst
| BRANCH : list inst -> list inst -> inst
| LOOP   : list inst -> list inst -> inst.

(* Configuration has the form <c,e,s> where c is a sequence of inst, 
    e is the stack, and s is the storage*)
Inductive configuration : Type :=
| Rem : inst -> State.t -> configuration
| Fin : State.t -> configuration.

(** ** Structural Operational Semantics *)
Inductive am : inst -> State.t -> configuration -> Prop := 
| am_noop:    (* < Skip, s > -> s *)
    forall s, am NOOP s (Fin s)
| am_fetch: 
    forall n s, am (State.find n) (Fin s).
(*| am_push: 
    forall n, am *)

 Module Examples.

    Example ex4_1 : t Z :=
      [ (Id.Id x, 3%Z) ; (PUSH 1) ; FETCH x; ADD ; STORE x ].



  End Examples.