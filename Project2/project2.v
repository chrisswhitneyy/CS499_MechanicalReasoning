(* Project 2: *)

Require Import Arith ZArith List String State.
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
      am  (c, e, s)  (c , e, s).
(*
| am_push: 
  forall  (n:Z) (s:State.t Type) (e:Stack.t), 
      am (PUSH n)  s  (Fin (Stack.push n e)).

| am_add: 
  forall (z1 z2: Z) (s:State.t)  (e:Stack.t), 
     (Stack.push (ZArith.add Stack.pop Stack.pop))

| am_sub: 
  forall (z1 z2: Z) (s:State.t)  (e:Stack.t), 
     (Stack.push (ZArith.sub Stack.pop Stack.pop))

| am_mult: 
  forall (z1 z2: Z) (s:State.t)  (e:Stack.t), 
     (Stack.push (ZArith.mult Stack.pop Stack.pop))

| am_fetch: 
    forall (n:Id.t)  (s:State.t Type) (e:Stack.t), (State.find s n) ::e. 

| am_true: 
    forall (tt:bool) (s:State.t)  (e:Stack.t), 
    Stack.push tt e. 

|am_false: 
   forall (ff:bool) (s:State.t)  (e:Stack.t), 
    Stack.push ff e.

| am_eq: 
  forall (z1 z2: Z) (s:State.t)  (e:Stack.t), 
     (Stack.push (ZArith.eq Stack.pop Stack.pop))

| am_le: 
  forall (z1 z2: Z) (s:State.t)  (e:Stack.t), 
     (Stack.push (ZArith.le Stack.pop Stack.pop))

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