(* Project 2: *)

Require Import Arith ZArith List String. 
Import ListNotations. 

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

(** * Semantics as Relations *)

(** ** Syntax *)


Inductive inst: Type := 
| SEQ : inst -> inst -> inst
| PUSH-n : inst -> inst
| ADD : Z -> Z -> inst -> inst
| MULT : Z -> Z -> inst -> inst
| SUB : Z -> Z -> inst -> inst
| TRUE : inst -> inst
| FALSE : inst -> inst
| EQ : Z -> Z -> inst -> inst
| LE  : Z -> Z -> inst -> inst
| AND : bool -> bool -> inst -> inst
| NEG : bool -> inst -> inst
| FETCH-x : inst -> inst
| STORE-x : Z -> inst -> inst
| NOOP : inst
| BRANCH : bool -> inst -> inst
| LOOP : inst -> inst.

(** ** Structural Operational Semantics *)

Inductive configuration : Type :=
| Rem : inst -> State.t -> configuration
| Fin : State.t -> configuration.

Inductive am : inst -> State.t -> State.t -> Prop := 
| am_noop:    (* < Skip, s > -> s *)
    forall s, am NOOP s (Fin s) 
| am_seq:
    forall S1 S2 s S1' s',
      am S1 s (Rem S1' s') ->
      am (Seq S1 S2) s (Rem (Seq S1' S2) s')
| am_seq2:
    forall S1 S2 s s',
      am S1 s (Fin s') ->
      am (Seq S1 S2) s (Rem S2 s')
| am_push: 
    forall (x:Id.t) (a:Aexp.t) (s:Id.t -> Z),
      am (am_push x a)
      s
      (Fin (State.update s x (Aexp.A a s))) (* Change these to Concat instead of replace *)
| am_true: 
    forall (x:Id.t) (a:Aexp.t) (s:Id.t -> Z),
      am (am_true x a)
      s
      (Fin (State.update s x (Aexp.A a s)))

| am_false: 
    forall (x:Id.t) (a:Aexp.t) (s:Id.t -> Z),
      am (am_false x a)
      s
      (Fin (State.update s x (Aexp.A a::x s)))
.

