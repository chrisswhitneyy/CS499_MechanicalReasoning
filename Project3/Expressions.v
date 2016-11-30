(* CS 499 - Mechanized Reasoning about Programs *)
(* Copyright Northern Arizona University        *)
(* All rights reserved                          *)

Require Import Arith ZArith List String Project2.
Import ListNotations.
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