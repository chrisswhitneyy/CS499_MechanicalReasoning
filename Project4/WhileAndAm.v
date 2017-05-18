(* CS 499 - Mechanized Reasoning about Programs *)
(* Copyright Northern Arizona University        *)
(* All rights reserved                          *)

Require Import Arith ZArith List String Relation_Operators.
Import ListNotations.

(** * Identifiers and Polymorphic States *)

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

(** Natural numbers can be understood as identifiers *)
Coercion Id.Id: nat >-> Id.t.


(** In the module [State], [t A] is the type of a state, i.e.  a
    partial mapping from identifiers to values of type [A]. *)

Module State.

  Definition t := Id.t -> Z.
  
  Definition update (s:t)(x:Id.t)(v:Z) : t :=
    fun y => if Id.beq y x
          then v
          else s y.
  
End State.


(** * Arithmetic Expressions *)

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
    
  (* Examples of expressions *)
  Module Ex_t.
    Import Notations.
    
    Definition x : Id.t := Id.Id 0. 
    Definition y : Id.t := Id.Id 1.
    Definition z : Id.t := Id.Id 2.

    (* Warning: scope Z is not opened! *)
    Definition a0 : t := Binop Add x 1%Z.
    Definition a1 : t := Binop Add x 1.
    Print a0. (* 1%Z is considered as a numerical constant *)
    Print a1. (* 1 is considered as an identifier! *)

    Definition a2 : t := z - (x * (y + 1)).
  End Ex_t.
    
  (* Examples of evaluation *)
  Module Ex_A.
    Import Ex_t.
    
    Definition s :=
      fun z =>
        if Id.beq z x then 42%Z else
          if Id.beq z y then 0%Z else 0%Z.
    
    Example ex0 : A a0 s = 43%Z.
    Proof. simpl. trivial. Qed.

    Example ex1 : A a1 s = 42%Z.
    Proof. simpl. trivial. Qed.

    Example ex2 : A a2 s = 0%Z.
    Proof. simpl. trivial. Qed.

  End Ex_A.

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

  (** ** Examples *)
  Module Ex_t.
    Import Aexp.Notations Notations Aexp.Ex_t.
    
    Definition b1 : t := true.
    Definition b2 : t := !(a1 == 0%Z).
    Definition b3 : t := (0%Z <= x) && (x <= y).

  End Ex_t.

  Fixpoint B (b:Bexp.t) (s:Id.t -> Z) : bool :=
  match b with
  | Bexp.Bool b => b
  | Bexp.Neg b  => negb(B b s)
  | Bexp.And b1 b2 => andb (B b1 s) (B b2 s)
  | Bexp.Cmp cmp a1 a2 => (Bexp.get_cmp  cmp) (Aexp.A a1 s) (Aexp.A a2 s)
  end.

  
  Module Ex_B.
    Import Ex_t Aexp.Ex_A.

    Fact f1 : B b1 s = true.
    Proof.  simpl. trivial. Qed.

    Fact f2 : B b2 s = true.
    Proof.  simpl. trivial. Qed.

    Fact f3 : B b3 s = false.
    Proof.  simpl. trivial. Qed.
  End Ex_B.

  (** ** Free variables *)
  Fixpoint FV (b:t) : list Id.t :=
    match b with
    | Bool b   => []     
    | Neg b  => FV b      
    | And b1 b2 =>
      List.app (FV b1) (FV b2)
    | Cmp _ a1 a2 =>
      List.app (Aexp.FV a1) (Aexp.FV a2)
    end.

  Module Ex_FV.
    Import Ex_t Aexp.Ex_t.
    
    Fact f1 : FV b1 = [].
    Proof. simpl. trivial. Qed.

    Fact f2 : FV b2 = [x;y].
    Proof. simpl. trivial. Qed.

    Fact f3 : FV b3 = [x;x;y].
    Proof. simpl. trivial. Qed.
  End Ex_FV.    
  
  Lemma lemma_1_13:
    forall (s s':State.t) (b:t),
      (forall x, In x (FV b) -> s x = s' x) ->
      B b s = B b s'.
  Proof.
    intros s s' b Hstates.
    induction b as [ b | b IH | b1 IH1 b2 IH2 | cmp a1 a2 ]; simpl in *.
    - trivial.
    - rewrite IH; auto.
    - rewrite IH1, IH2; auto; intros; intuition.
    - assert(Aexp.A a1 s = Aexp.A a1 s') as H1
          by (apply Aexp.lemma_1_12;intros; intuition).
      assert(Aexp.A a2 s = Aexp.A a2 s') as H2
          by (apply Aexp.lemma_1_12;intros; intuition).
      now rewrite H1, H2.
  Qed.

  (** ** Substitution *)
  Fixpoint subst (b:t) (y:Id.t) (a:Aexp.t) : t :=
    match b with
    | Bool b => Bool b
    | Neg b => Neg(subst b y a)
    | And b1 b2 =>
      And (subst b1 y a) (subst b2 y a)
    | Cmp cmp a1 a2 =>
      Cmp cmp (Aexp.subst a1 y a) (Aexp.subst a2 y a)
    end.
    
  Lemma lemma_1_15:
    forall (s:State.t)(b:t)(a:Aexp.t)(y:Id.t),
      B (subst b y a) s = B b (State.update s y (Aexp.A a s)). 
  Proof.
    intros s; induction b; intros a y; simpl in *.
    - trivial.
    - now rewrite IHb.
    - now rewrite IHb1, IHb2.
    - now repeat rewrite Aexp.lemma_1_14.
  Qed.

End  Bexp.

(** * Semantics as Relations *)

(** ** Syntax *)

Inductive stm : Type :=
| Skip : stm
| Assign : Id.t -> Aexp.t -> stm
| Seq : stm -> stm -> stm
| If : Bexp.t -> stm -> stm -> stm
| While: Bexp.t -> stm -> stm.

(** ** Natural Semantics *)

(** < S, s > -> s' *)
Inductive ns : stm -> State.t -> State.t -> Prop :=
| ns_skip:    (* < Skip, s > -> s *)
    forall s, ns Skip s s 
| ns_assign:  (* < x := a, s > -> s[x|->A[x]s] *)
    forall (x:Id.t) (a:Aexp.t) (s:Id.t->Z),
      ns (Assign x a)
           s
           (State.update s x (Aexp.A a s))
| ns_comp:    (* < S1, s > -> s'   < S2, s'-> s" 
                 -------------------------------
                       < S1;S2, s > -> s"        *)
    forall S1 S2 s s' s'',
      ns S1 s s' ->
      ns S2 s' s'' -> 
      ns (Seq S1 S2) s s'' 
| ns_if_tt:  (* < S1 , s > -> s'      B[b]s = tt
                --------------------------------
                < if b then S1 else S2, s > -> s' *)
    forall b S1 S2 s s',
      Bexp.B b s = true ->
      ns S1 s s' ->
      ns (If b S1 S2) s s' 
| ns_if_ff:  (* < S2 , s > -> s'      B[b]s = ff
                --------------------------------
                < if b then S1 else S2, s > -> s' *)
    forall b S1 S2 s s',
      Bexp.B b s = false ->
      ns S2 s s' ->
      ns (If b S1 S2) s s'
| ns_while_tt:
  (* B[b]s = tt  < S, s > -> s'  <while b do S, s'>->s"
     --------------------------------------------------
     <while b do S, s> -> s"                         *)
    forall b S s s' s'',
      Bexp.B b s = true ->
      ns S s s' ->
      ns (While b S) s' s'' ->
      ns (While b S) s s''
| ns_while_ff:
  (* B[b]s = ff 
     ----------------------- 
     <while b do S, s> -> s                          *)
    forall b S s,
      Bexp.B b s = false ->
      ns (While b S) s s
.

(** ** Structural Operational Semantics *)

Inductive configuration : Type :=
| Rem : stm -> State.t -> configuration
| Fin : State.t -> configuration.

Inductive sos : stm -> State.t -> configuration -> Prop :=
| sos_skip:    (* < Skip, s > -> s *)
    forall s, sos Skip s (Fin s) 
| sos_assign:  (* < x := a, s > -> s[x|->A[x]s] *)
    forall (x:Id.t) (a:Aexp.t) (s:Id.t->Z),
      sos (Assign x a)
          s
          (Fin (State.update s x (Aexp.A a s)))
| sos_comp1:
    forall S1 S2 s S1' s',
      sos S1 s (Rem S1' s') ->
      sos (Seq S1 S2) s (Rem (Seq S1' S2) s')
| sos_comp2:
    forall S1 S2 s s',
      sos S1 s (Fin s') ->
      sos (Seq S1 S2) s (Rem S2 s')
| sos_if_tt:
    forall S1 S2 b s,
      Bexp.B b s = true -> 
      sos (If b S1 S2) s (Rem S1 s)
| sos_if_ff:
    forall S1 S2 b s,
      Bexp.B b s = false -> 
      sos (If b S1 S2) s (Rem S2 s)
| sos_while:
    forall b S s,
      sos (While b S) s
          (Rem (If b (Seq S (While b S)) Skip) s)
.

(*********************** AM Language ***********************)

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

    (** ** Exercise 4.4 *)

    (** First, we need to define what corresponds to ->k: *)
    Inductive am_k : nat -> (code*Stack.t*State.t) -> (code*Stack.t*State.t) -> Prop :=
    | am_O: forall config, am_k 0 config config
    | am_Sn: forall config config' config'' k,
        am config config' -> am_k k config' config'' -> am_k (S k) config config''.

    Lemma ex_4_4:
      forall k c1 e1 s c' e' s' c2 e2,
        am_k k (c1, e1, s) (c', e', s') ->
        am_k k (c1++c2, e1++e2, s) (c'++c2, e'++e2, s').
    Proof.
      induction e2.
    
    Notation am_star := (clos_refl_trans_1n  _ am).

  Lemma ex_4_4':
    forall c1 e1 s c' e' s' c2 e2,
      am_star (c1, e1, s) (c', e', s') ->
      am_star (c1++c2, e1++e2, s) (c'++c2, e'++e2, s').
  Proof.
  Admitted.
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
  
