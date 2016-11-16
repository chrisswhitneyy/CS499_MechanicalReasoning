(* Project 2: *)

Require Import Arith ZArith List String State.
Import ListNotations. 


Module Stack.

  Inductive A : Type :=
  | z : Z -> A 
  | t: bool -> A.

Inductive t : Type :=
  | nil : t
  | cons : A -> t -> t.

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Definition push (n:A)(s1:t): t :=
  cons n s1.

Definition pop (stack:t): t :=
  match stack with
  | [ ]  =>  [ ]
  | _::stack' => stack'
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
| Rem : inst -> State.t Type-> configuration
| Fin : State.t Type-> configuration.

(** ** Structural Operational Semantics *)
Inductive am : inst -> State.t Type-> configuration -> Prop := 
| am_noop:    (* < Skip, s > -> s *)
    forall s, am NOOP s (Fin s)

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



  End Examples.