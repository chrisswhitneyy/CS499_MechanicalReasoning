(* Project 2: *)

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

Compute (Z.eqb 2%Z 1%Z).

(** ** Structural Operational Semantics *)
Inductive am : config -> config -> Prop := 
| am_noop:
    forall (c:code) (e:Stack.t)(s:State.t) ,
      am  (c, e, s)  (c , e, s)
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
    (Z.eqb z1 z2) = true -> 
    am (EQ::c,e,s) (c, (Stack.T (Z.eqb z1 z2))::e, s)
| am_eq_ff : 
  forall (c:code) (s:State.t) (e:Stack.t) (z1 z2: Z), 
    (Z.eqb z1 z2) = false -> 
    am (EQ::c,e,s) (c, (Stack.T (Z.eqb z1 z2))::e, s)

| am_le_tt : 
  forall (c:code) (s:State.t) (e:Stack.t) (z1 z2: Z), 
    (Z.leb z1 z2) = true -> 
    am (EQ::c,e,s) (c, (Stack.T (Z.leb z1 z2))::e, s)
| am_le_ff : 
  forall (c:code) (s:State.t) (e:Stack.t) (z1 z2: Z), 
    (Z.leb z1 z2) = false -> 
    am (EQ::c,e,s) (c, (Stack.T (Z.leb z1 z2))::e, s).

(* AND *) 




| am_fetch: 
    forall (n:Id.t)  (s:State.t Type) (e:Stack.t), (State.find s n) ::e. 




|am_neg_tt: 
  forall  (c:inst) (s:State.t) (e:Stack.t), 
  Stack.pop e = tt ->  ff::e 

|am_neg_ff: 
  forall  (c:inst) (s:State.t) (e:Stack.t), 
  Stack.pop e = ff -> tt::e 

| am_store: 
    forall (n:Id.t)  (s:State.t) (e:Stack.t), (State.update (State.find s n) s) .

|am_branch_tt: 
  forall (c1 c2 c: inst) (e: Stack.t) (s:State.t) , 
    Stack.pop e = tt ->  c1::c 

|am_branch_ff: 
  forall (c1 c2 c: inst) (e: Stack.t) (s:State.t) , 
    Stack.pop e = ff ->  c2::c 
|am_loop: 
 Module Examples.

    Example ex4_1 : t Z :=
      [ (Id.Id x, 3%Z) ; (PUSH 1) ; FETCH x; ADD ; STORE x ].



  End Examples. *)