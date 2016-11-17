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
    am (LE::c,e,s) (c, (Stack.T (Z.leb z1 z2))::e, s)
| am_le_ff : 
  forall (c:code) (s:State.t) (e:Stack.t) (z1 z2: Z), 
    (Z.leb z1 z2) = false -> 
    am (LE::c,e,s) (c, (Stack.T (Z.leb z1 z2))::e, s)

(* AND *) 
| am_and_tt: 
  forall (c:code) (s:State.t) (e:Stack.t) (t1 t2 tt:bool), 
    t1 = true -> t2 = true -> 
    am (AND::c, e, s) (c,(Stack.T tt)::e,s)

| am_and_ff: 
  forall (c:code) (s:State.t) (e:Stack.t) (t1 t2 ff:bool), 
    t1 = false \/ t2 = false -> 
    am (AND::c, e, s) (c,(Stack.T ff)::e,s)
 
(*NEG *)
|am_neg_tt: 
  forall  (c:code) (s:State.t) (e:Stack.t) (t tt:bool), 
    t = true -> 
    am (NEG::c,e,s) (c,(Stack.T tt)::e,s)

|am_neg_ff: 
  forall  (c:code) (s:State.t) (e:Stack.t) (t ff:bool), 
    t = false -> 
    am (NEG::c,e,s) (c,(Stack.T ff)::e,s)

| am_fetch: 
    forall (c:code) (s:State.t) (e:Stack.t) (x:Id.t), 
      am ((FETCH x)::c,e,s) (c, (Stack.z (s x))::e,s)

|am_store:
    forall (c:code) (s:State.t) (e:Stack.t) (x:Id.t) (z:Z),
      am ((STORE x)::c,(Stack.z z)::e,s) (c,e, (State.update s x z))

|am_branch_tt: 
    forall (c c1 c2:code) (s:State.t) (e:Stack.t) (t:bool), 
      t = true ->
      am ((BRANCH c1 c2)::c, (Stack.T t)::e, s) (c1++c, e, s)

|am_branch_ff: 
    forall (c c1 c2:code) (s:State.t) (e:Stack.t) (t:bool), 
      t = false ->
      am ((BRANCH c1 c2)::c, (Stack.T t)::e, s) (c2++c, e, s).

(* LOOP *) 
(* |am_loop: 
    forall (c c1 c2:code) (s:State.t) (e:Stack.t), 
      am ((LOOP (c1++c2)++c), e, s) ( c1::BRANCH(c2::LOOP(c1,c2),NOOP)::c,e,s). *) 

(*
 Module Examples.

    Example ex_4_1: config :=
      [ (PUSH 1%Z) (Id.Id 0, 3%Z)  [ ] [ ]      ].



  End Examples. *)