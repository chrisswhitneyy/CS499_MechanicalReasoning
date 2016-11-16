(* CS 499 - Mechanized Reasoning about Programs *)
(* Copyright Northern Arizona University        *)
(* All rights reserved                          *)

Require Import Arith ZArith List String.
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

  Definition t (A:Type) : Type := list (Id.t * A).

  Definition update{A:Type}(state:t A)(key:Id.t)(value:A): t A :=
    (key,value)::state.

  Fixpoint find {A:Type}(state:t A)(key:Id.t) : option A :=
    match state with
      | [ ] => None
      | cons (k,v) state' => 
          if Id.beq key k
          then Some v
          else find state' key 
    end.

  Fact find_update :
    forall (A:Type)(k:Id.t) (v:A) (s: t A),
      find (update s k v) k = Some v.
  Proof.
    intros A k v s.
    simpl.
    rewrite Id.beq_refl.
    reflexivity.
  Qed.

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

  
