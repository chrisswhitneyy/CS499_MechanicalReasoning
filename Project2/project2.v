(* Project 2:  The Abstract Machince   
            
    The purpose of this project is to formally define an abstract machince that translates a lanuage called 
    While into a structured form of assembler code.  This is done in order to prove that the implementation 
    of the programing lanuage is correct. This can not be acccomplished without first formally defining the meaing of 
    each insturction, this mapping from symbols to meaing is done within the function AM using operational semantics. 
    The rules are defined in Table 4.1 of the course text. The machince has a configuration of the following from <c,e,s> 
    where c is a list of instructions defined below as code, e is a stack defined in the State.v file, and s is a state implemented 
    as a function in State.v as well. 

    Authors: Charles Chatwin and Chris Whitney*)

Require Import Arith ZArith List String State Bool Relation_Operators.
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

(*  Definition of c based of page 68, c is a list of inst which is called code here *)
Definition code: Type := list inst.

(* Configuration has the form <c,e,s> where c is a sequence of inst,
    e is the stack, and s is the storage*)
Definition config : Type := ( code * Stack.t * State.t) .

(** ** Structural Operational Semantics *)
Inductive am : config -> config -> Prop :=
(*NOOP (skip)*)
| am_noop:
    forall (c:code) (e:Stack.t)(s:State.t),
      am  (NOOP::c, e, s)  (c , e, s)
(*PUSH*)
| am_push:
  forall  (n:Z) (c:code) (e:Stack.t)(s:State.t),
      am ((PUSH n)::c, e, s) (c, (Stack.z n)::e, s)

(* Z operations *)
| am_add:
  forall  (z1 z2:Z) (c:code) (s:State.t)  (e:Stack.t),
     am (ADD::c, (Stack.z z1)::(Stack.z z2)::e, s) (c, (Stack.z (Z.add z1 z2))::e, s)

| am_sub:
  forall (z1 z2: Z) (c:code) (s:State.t)  (e:Stack.t),
     am (SUB::c, (Stack.z z1)::(Stack.z z2)::e, s) (c, (Stack.z (Z.sub z1 z2))::e, s)

| am_mult:
  forall (z1 z2: Z) (c:code) (s:State.t)  (e:Stack.t),
     am (MULT::c, (Stack.z z1)::(Stack.z z2)::e, s) (c, (Stack.z (Z.mul z1 z2))::e, s)

(* TRUE and FALSE *)
| am_true:
    forall (c:code) (s:State.t) (e:Stack.t) (tt:bool),
       am (TRUE::c, e, s) (c, (Stack.T tt)::e, s)

| am_false:
    forall (c:code) (s:State.t) (e:Stack.t) (ff:bool),
       am (FALSE::c, e, s) (c, (Stack.T ff)::e, s)

(* EQ and LE *)
| am_eq :
  forall (c:code) (s:State.t) (e:Stack.t) (z1 z2: Z),
    am (EQ::c,e,s) (c, (Stack.T (Z.eqb z1 z2))::e, s)

| am_le :
  forall (c:code) (s:State.t) (e:Stack.t) (z1 z2: Z),
    am (LE::c,e,s) (c, (Stack.T (Z.leb z1 z2))::e, s)

(* AND *) 
| am_and:
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

   Example ex_4_1 : 
      exists s', 
      (clos_refl_trans_1n _ am) ( (PUSH 1%Z)::(FETCH x)::(ADD)::(STORE x)::[],[ ], s ) 
                                             ([],[],s') /\ s' x = 4%Z.
   Proof. 
       repeat eexists.
       do 10  econstructor.
       simpl. reflexivity.
  Qed.

   Example ex_4_2: 
      forall (s:State.t),
      exists s', 
          (clos_refl_trans_1n  _ am) ( [ LOOP [TRUE] [NOOP] ], [ ], s) ([ ], [ ], s'). 
      Proof. 
          repeat eexists.
          do 4 econstructor.
       Admitted.

End Examples. 