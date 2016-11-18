(* Project 2: *)
(* Authors: Chris and Charles Chatwin*)

Require Import Arith ZArith List String State Bool.
Import ListNotations.

(** ** Syntax *)
(* Translated from page 68 in text, where c is represented using lists*)
Inductive inst: Type := 
| PUSH   : Z -> inst
| ADD    | MULT | SUB 
| TRUE   | FALSE 
| EQ     | LE  
| AND    | NEG
| FETCH  : Id.t -> inst
| STORE  : Id.t -> inst 
| NOOP   : inst
| BRANCH : list inst -> list inst -> inst
| LOOP   : list inst -> list inst -> inst.

Definition code: Type := list inst.

(* Configuration has the form <c,e,s> where c is a sequence of inst,
    e is the stack, and s is the storage*)
Definition config : Type := ( code * Stack.t * State.t) .

(** ** Structural Operational Semantics *)
Inductive am : config -> config -> Prop :=
(*NOOP (skip)*)
| am_noop:
    forall (c:code) (e:Stack.t)(s:State.t),
      am  (c, e, s)  (c , e, s)
(*PUSH*)
| am_push:
  forall  (n:Z) (c:code) (e:Stack.t)(s:State.t),
      am ((PUSH n)::c, e, s) (c, (Stack.z n)::e, s)

(* Z operations *)
| am_add:
  forall (z1 z2: Z) (c:code) (s:State.t)  (e:Stack.t),
     am (ADD::c, e, s) (c, (Stack.z (Z.add z1 z2))::e, s)

| am_sub:
  forall (z1 z2: Z) (c:code) (s:State.t)  (e:Stack.t),
     am (SUB::c, e, s) (c, (Stack.z (Z.sub z1 z2))::e, s)

| am_mult:
  forall (z1 z2: Z) (c:code) (s:State.t)  (e:Stack.t),
     am (MULT::c, e, s) (c, (Stack.z (Z.mul z1 z2))::e, s)

(* TRUE and FALSE *)
| am_true:
    forall (c:code) (s:State.t) (e:Stack.t) (tt:bool),
       am (TRUE::c, e, s) (c, (Stack.T tt)::e, s)

| am_false:
    forall (c:code) (s:State.t) (e:Stack.t) (ff:bool),
       am (FALSE::c, e, s) (c, (Stack.T ff)::e, s)

(* EQ and LE *)
| am_eq_tt :
  forall (c:code) (s:State.t) (e:Stack.t) (z1 z2: Z),
    am (EQ::c,e,s) (c, (Stack.T (Z.eqb z1 z2))::e, s)

| am_le :
  forall (c:code) (s:State.t) (e:Stack.t) (z1 z2: Z),
    am (LE::c,e,s) (c, (Stack.T (Z.leb z1 z2))::e, s)

(* AND *) 
| am_and_tt:
  forall (c:code) (s:State.t) (e:Stack.t) (t1 t2:bool),
    am (AND::c, e, s) (c,(Stack.T (andb t1 t2))::e,s)

(*NEG *)
|am_neg:
  forall  (c:code) (s:State.t) (e:Stack.t) (t:bool),
    am (NEG::c,(Stack.T t)::e,s) (c,(Stack.T (negb t))::e,s)

(*FETCH*)
| am_fetch:
    forall (c:code) (s:State.t) (e:Stack.t) (x:Id.t),
      am ((FETCH x)::c,e,s) (c, (Stack.z (s x))::e,s)

(*STORE*)
|am_store:
    forall (c:code) (s:State.t) (e:Stack.t) (x:Id.t) (z:Z),
      am ((STORE x)::c,(Stack.z z)::e,s) (c,e, (State.update s x z))

(*BRANCH*)
|am_branch_tt:
    forall (c c1 c2:code) (s:State.t) (e:Stack.t),
      am ((BRANCH c1 c2)::c, (Stack.T true)::e, s) (c1++c, e, s)

|am_branch_ff:
    forall (c c1 c2:code) (s:State.t) (e:Stack.t),
      am ((BRANCH c1 c2)::c, (Stack.T false)::e, s) (c2++c, e, s)

(* LOOP *)
|am_loop:
    forall (c c1 c2:code) (s:State.t) (e:Stack.t),
      am ((LOOP c1 c2)::c, e, s) ( c1++(BRANCH(c2++[(LOOP c1 c2)]) [NOOP])::c,e,s).


Module Examples.

  Definition x : Id.t := Id.Id 0.

  Definition s (y: Id.t) : Z := 
    if Id.beq y x 
      then 3%Z
    else 0%Z.

  Definition s' (y: Id.t) : Z := 
    if Id.beq y x 
      then 4%Z
    else 0%Z.

   Example ex_4_1: 
      am ([ (PUSH 1%Z) ; (FETCH x) ; (ADD) ; (STORE x) ],[ ], s )  ([],[],s') . 
   Proof. 
       admit.
   Admitted.

   Example ex_4_2: 
      am ( [ LOOP [TRUE] [NOOP] ], [ ], s) ([ ], [ ], s). 
  Proof. 
    admit. 
  Admitted.

End Examples. 