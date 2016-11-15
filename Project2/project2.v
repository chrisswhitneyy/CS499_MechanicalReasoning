(* Project 2: *)

Require Import Arith ZArith List String WhileStateFun.
Import ListNotations. 


Module Stack.
  
  Definition t := list Type.

  Definition pop  (stack:Stack.t) : list := 
    match stack with 
    | a1 :: _ => a1
    | nil => stack
    end.

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
Inductive am : inst -> State.t -> State.t -> Prop := 
| am_noop:    (* < Skip, s > -> s *)
    forall s, am NOOP s (Fin s) 
| am_seq:
    forall S1 S2 s S1' s',
      am S1 s (Rem S1' s') ->
      am (Seq S1 S2) s (Rem (Seq S1' S2) s')
| am_seq2:
    forall S1 S2 s s',
      am S1 s (Fin s') ->
      am (Seq S1 S2) s (Rem S2 s')
| am_push: 
    forall (x:Id.t) (a:Aexp.t) (s:Id.t -> Z),
      am (am_push x a)
      s
      (Fin (State.update s x (Aexp.A a s))) (* Change these to Concat instead of replace *)
| am_true: 
    forall (x:Id.t) (a:Aexp.t) (s:Id.t -> Z),
      am (am_true x a)
      s
      (Fin (State.update s x (Aexp.A a s)))

| am_false: 
    forall (x:Id.t) (a:Aexp.t) (s:Id.t -> Z),
      am (am_false x a)
      s
      (Fin (State.update s x (Aexp.A a::x s)))
.

 Module Examples.

    Example ex4_1 : t Z :=
      [ (Id.Id x, 3%Z) ; (PUSH 1) ; FETCH x; ADD ; STORE x ].



  End Examples.