(* Project 2:  The Abstract Machince   
            
    The purpose of this project is to formally define an abstract machince that translates a lanuage called 
    While into a structured form of assembler code.  This is done in order to prove that the implementation 
    of the programing lanuage is correct. This can not be acccomplished without first formally defining the meaing of 
    each insturction, this mapping from symbols to meaing is done within the function AM using operational semantics. 
    The rules are defined in Table 4.1 of the course text. The machince has a configuration of the following from <c,e,s> 
    where c is a list of instructions defined below as code, e is a stack defined in the State.v file, and s is a state implemented 
    as a function in State.v as well. 

    Authors: Charles Chatwin and Chris Whitney*)

Require Import Arith ZArith List String Bool Relation_Operators.
Import ListNotations.

(** Id **)
Module Id.

  Inductive t := Id : nat -> t.

  Definition beq (id1 id2:t) : bool :=
    match (id1, id2) with
    | (Id n1, Id n2) => beq_nat n1 n2
    end.

  (** Properties of Id.beq: reflexivity, symmetry. *)

  Fact beq_refl: forall id, beq id id = true.
  Proof.
    intros id.
    destruct id as [ n ].
    unfold beq.
    symmetry.
    apply beq_nat_refl.
  Qed.

  Fact beq_sym: forall id1 id2, beq id1 id2 = beq id2 id1.
  Proof.
    intros id1 id2.
    destruct id1 as [ n1 ].
    destruct id2 as [ n2 ].
    unfold beq.
    now rewrite Nat.eqb_sym.
  Qed.

  Fact beq_eq: forall id1 id2,
      beq id1 id2 = true -> id1 = id2.
  Proof.
    intros [ id1 ] [ id2 ] H; unfold beq in *; simpl in *.
    apply beq_nat_true in H; now rewrite H.
  Qed.
  
End Id.

(* State *)
Module State.

  Definition t := Id.t -> Z.
  
  Definition update (s:t)(x:Id.t)(v:Z) : t :=
    fun y => if Id.beq y x
          then v
          else s y.

End State.

(* Evaluation Stack *)
Module Stack.

  Inductive A : Type :=
  | z : Z -> A 
  | T: bool -> A.

  Definition t : Type := list A.

End Stack.


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
          (clos_trans  _ am) ( [ LOOP [TRUE] [NOOP] ], [ ], s) ([ LOOP [TRUE] [NOOP] ], [ ], s). 
      Proof.
          do 5 (econstructor; simpl).
      Qed.
    Lemma ex_4_6: 
      forall (c:code) (s:State.t) (e:Stack.t), 
      exists c' s' e', 
        (clos_refl_trans_1n _ am) (c,e,s) (c',e',s').
    Proof. 
        repeat eexists.
        admit.
    Admitted.

(*Theorem 2.9 (page 41?)*) (*should do induction on derivation tree*)
(*show table 4.1 is determinisistc; use to prove there is only one 
   computation sequence. (pg 73?)
Instead of taking am: prove for am; prove for reflex_trans am.*)


End Examples.

Module Aexp.

  (** * The type of arithmetic expressions *) 

  Inductive binary_op : Type :=
    Add | Mul | Sub.

  Inductive t : Type :=
  | Int: Z -> t
  | Var: Id.t -> t
  | Binop : binary_op -> t -> t -> t.

  Definition get_op (op: binary_op): Z->Z->Z :=
    match op with
    | Add => Z.add
    | Mul => Z.mul
    | Sub => Z.sub
    end.
  
  (** ** Evaluation of expressions *)
  Fixpoint A (a:Aexp.t) (s:Id.t -> Z) : Z :=
    match a with
    | Aexp.Int z => z
    | Aexp.Var id => s id
    | Aexp.Binop op a1 a2 => (Aexp.get_op op) (A a1 s) (A a2 s)  
    end.

Module Notations.
  
    (* Coercions *)
    Coercion Int : Z >-> t.
    Coercion Var : Id.t >-> t.
    
    (* Notations *)
    Notation "a0 + a1" := (Binop Add a0 a1).
    Notation "a0 - a1" := (Binop Sub a0 a1).
    Notation "a0 * a1" := (Binop Mul a0 a1).

End Notations.

  (** ** Free variables *) 

  (* Instead of using a set of variables, we will use lists, and allow
     a variable to be present several times in the list. *)
  Fixpoint FV (a:t) : list Id.t :=
    match a with
    | Int z   => []     
    | Var id  => [id]      
    | Binop op a1 a2 => List.app (FV a1) (FV a2)
    end.

  Lemma lemma_1_12:
    forall (s s':State.t) (a:t),
      (forall x, In x (FV a) -> s x = s' x) ->
      A a s = A a s'.
  Proof.
    intros s s' a H.
    induction a as [ z | x | op a1 IH1 a2 IH2].
    - simpl. trivial.
    - simpl. apply H.
      simpl. left. reflexivity.
    - assert(A a1 s = A a1 s') as H1.
      {
        apply IH1.
        intros x Hx.
        apply H. simpl.
        apply in_or_app.
        left. assumption.
      }
      assert(A a2 s = A a2 s') as H2.
      {
        apply IH2.
        intros x Hx.
        apply H. simpl.
        apply in_or_app.
        right. assumption.
      }
      simpl.
      rewrite H1, H2.
      trivial.
  Qed.

  (** ** Substitution *)
  Fixpoint subst (a:t) (y:Id.t) (a0:t) : t :=
    match a with
    | Int z  =>  Int z
    | Var id =>  if Id.beq id y
                then a0
                else Var id
    | Binop op a1 a2 =>
      Binop op (subst a1 y a0) (subst a2 y a0)
    end.

  (** Lemma (Exercice) 1.14 (page 18) of Semantics with Applications
      is written as follows: A[a[y →a0]]s = A[a](s[y →A[a0]s]) for all
      states s.

      A direct ``translation'' one could think of in would be: forall
      s a a0 y, A (subst a y a0) s = A a (State.update s y (A a0 s)).

      However (A a0 s) has type option Z, whereas function
      State.update expect its third argument to be of type Z.

      Therefore the correct statement in Coq is as follows: *)
  Lemma lemma_1_14:
    forall (s:State.t)(a a0:t)(y:Id.t),
      A (subst a y a0) s = A a (State.update s y (A a0 s)). 
  Proof.
    intros s a a0 y.
    induction a as [ z | x | op a1 IH1 a2 IH2 ].
    - trivial.
    - unfold State.update. simpl.
      destruct (Id.beq x y).
      + trivial.
      + trivial.
    - simpl.
      now rewrite IH1, IH2.
  Qed.
  
End Aexp.

(** * Boolean expressions *)

Module Bexp.

  (** ** Definition of boolean expressions *)
  Inductive cmp_op : Type :=
    Equal | LowerEq.

  Definition get_cmp (cmp: cmp_op) : Z -> Z -> bool :=
    match cmp with
    | Equal => Z.eqb
    | LowerEq => Z.leb
    end.
  
  Inductive t : Type :=
  | Bool: bool -> t      (* Constant: true or false *)
  | Neg: t -> t       (* negation of an expression *)
  | And: t -> t -> t   (* conjunction of two boolean expressions *)
  | Cmp: cmp_op -> Aexp.t -> Aexp.t -> t
                     (* comparison of two arithmetic expressions *)
  .

  (** ** Notations *)
  Module Notations.
  
    Coercion Bool : bool >-> t.
    Notation "! b":=(Neg b)(at level 70).
    Infix "&&" := And.
    Notation "a1 == a2" := (Cmp Equal a1 a2)(at level 70).
    Notation "a1 <= a2" := (Cmp LowerEq a1 a2)(at level 70).

  End Notations.

  Fixpoint B (b:Bexp.t) (s:Id.t -> Z) : bool :=
  match b with
  | Bexp.Bool b => b
  | Bexp.Neg b  => negb(B b s)
  | Bexp.And b1 b2 => andb (B b1 s) (B b2 s)
  | Bexp.Cmp cmp a1 a2 => (Bexp.get_cmp  cmp) (Aexp.A a1 s) (Aexp.A a2 s)
  end.

End Bexp.

Inductive stm : Type :=
| Skip : stm
| Assign : Id.t -> Aexp.t -> stm
| Seq : stm -> stm -> stm
| If : Bexp.t -> stm -> stm -> stm
| While: Bexp.t -> stm -> stm.
