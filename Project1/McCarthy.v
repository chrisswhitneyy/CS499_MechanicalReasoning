(**Notes: We where able to assert everything, but the valid_ac_some eqt on Page 9.  
  Devoloped by: Chris Whitney, Charles Chatwin, John Devlin, Cameron Gaskin. 
  The ordering of the names is by time spend on the project. 
**)

Require Import List. Import ListNotations.
Require Import Arith ZArith.

(** * Formalisation in Coq of "CORRECTNESS OF A COMPILER FOR
      ARITHMETIC EXPRESSIONS" by McCarthy and Painter, 1967 *)
(** ** The source language *)

Module Source.

  Definition variable : Set := nat.

  Inductive t : Set :=
  | const : Z -> t
  | var   : variable -> t
  | add   : t -> t -> t.

  Inductive In : variable -> t -> Prop := 
  | in_var : forall v, In v (var v)
  | in_add : forall v e1 e2, In v e1 \/ In v e2 -> In v (add e1 e2).

  Definition state := variable -> Z.

  Definition c (x:nat) (s:state) := s x.

  (** Definition (2.1) page 3 in the paper. *)
  Fixpoint value (e:t) (env:state) : Z := 
    match e with
      | var x => c x env 
      | const v => v
      | add e1 e2 => ( (value e1 env) + (value e2 env) )%Z
    end.

End Source.

(** ** The object language *)

Module Object.

  (** Here an address is an option type so that the accumulator is the
      [None] value. *)

  Definition address : Set := option nat.

  Definition ac : address := None. (* The accumulator. *)

  Lemma eq_dec (l l' : address) : { l = l' } + { ~ l = l' }.
  Proof. repeat (decide equality). Qed.
  
  (** The paper assumes an order on addresses.  As in the
      formalization an address is not a number, we need to define the
      ``lower than'' relation on addresses: *)
  Inductive lt : address -> address -> Prop := 
  | lt_ac : forall l, lt ac (Some l)
  | lt_some : forall n1 n2, Peano.lt n1 n2 -> lt (Some n1) (Some n2).

  (** For some proofs, it is necessary to use the following property
      of [lt]: *)
  Lemma lt_trans : 
    forall a1 a2 a3, 
      lt a1 a2 -> lt a2 a3 -> lt a1 a3.
  Proof.
    intros a1 a2 a3 lt1 lt2.
    inversion lt1.
    destruct a3 as [b1|b2].
    - constructor.
    - inversion lt2 in lt1; simpl.
    - subst.
      inversion lt2.
      apply lt_some.
      subst.
      rewrite <-H1.
      assumption.
  Qed.
  
  Inductive instruction : Set := 
  | li : Z -> instruction
  | load : address -> instruction 
  | store : address -> instruction
  | add : address -> instruction.

  Definition t := list instruction.

  Definition state := address -> Z.

  (** Functions defined on page 5 *)
  Definition c (x:address) (η:state) := η x.

  Definition a (l:address)(v:Z)(η:state) : state := 
    fun l' => if eq_dec l' l 
             then v
             else η l'.

  (** Property (3.10) page 5 *)
  Lemma a_refl : 
    forall x η y,  c y (a x (c x η) η) = c y η.
  Proof.
    intros x n y.
    compute.
    destruct eq_dec.
    - subst. reflexivity.
    - reflexivity.
  Qed.

  (** Property (3.9) page 5 *)
  Lemma a_a : 
    forall z η x y vx vy ,  
      c z (a x vx (a y vy η)) = 
      if eq_dec x y then c z (a x vx η) else c z (a y vy (a x vx η)).
  Proof.
    intros z n x y vx vy. 
    destruct eq_dec.
    - subst. 
      compute.
      destruct eq_dec;
      reflexivity.
    - compute.
      destruct eq_dec.
      + case_eq (eq_dec z y). subst.
        * contradiction.
        * repeat reflexivity.
      + reflexivity.
  Qed.

  (** Property (3.8) page 5 *)
  Lemma c_a : 
    forall x η y v,  c x (a y v η) = 
                     if eq_dec x y then v else c x η.
  Proof.
    intros x n y v.
    compute. 
    reflexivity.
  Qed.

  (** Definition (3.11) page 5 *)
  Fixpoint step (i:instruction)(η:state) : state := 
    match i with 
      | li v      => a ac v η 
      | load adr  => a ac  (c adr η) η
      | store adr => a adr (c ac η)  η
      | add adr   => a ac  ((c adr η) + (c ac η))%Z η
    end.


  (** Definition (3.12) page 5 *)
  Fixpoint outcome (p : t) (η:state) : state := 
    match p with 
      | [] => η 
      | first::rest => outcome rest (step first η)
    end.

  (** Lemma (3.13) page 5 *)
  Lemma outcome_app: 
    forall p1 p2 η,
    outcome (p1 ++ p2) η = outcome p2 (outcome p1 η).
  Proof.
    intros p1.
    induction p1.
    - simpl. trivial.
    - intros p2. simpl. auto.
  Qed.

  (** Generic partial equality of state vectors *)
  Definition eqt (P:address->Prop)(η1 η2 : state) : Prop := 
    forall l, P l -> c l η1 = c l η2.

End Object.

(** ** Compilation *)

Section compilation.

  (** In the paper, the authors assume there is a map (not formally
      defined) that relates each variable in the expression to a
      location in main memory, and that this location is written
      loc(var, map) for a variable var. More simply we assume a total
      function loc for variables to memory addresses: *)

  Variable loc : Source.variable -> Object.address.

  (** It is not explicit in the paper, but this property should 
      hold: the accumulator cannot contain the value of one of 
      the variables of the source expression. *)
  Hypothesis loc_prop : forall x, loc x <> Object.ac.

  (** Definition (4.2) page 6 *)
  Fixpoint compile (e : Source.t) (t : nat) : Object.t := 
    match e with 
      | Source.const v => [ Object.li v ] 
      | Source.var x   => [ Object.load (loc x) ]
      | Source.add e1 e2 => 
        (compile e1 t) ++ [Object.store (Some t)] ++ 
        (compile e2 (t+1)) ++ [Object.add (Some t)]
    end.   

  (** The partial equality of state vectors is [Object.eqt] where a
      subset of a set is formalized as a predicat (property) on a
      type. *)

  (** To define what corresponds to =_t in the paper (page 7), we need
      to define a predicate on addresses given an address t.

      Note that on page 6, E1 =_A E2 was symbolically: forall x
      \not\in A, c(x,E1) = c(x,E2).

      As in =_t in the paper is defined as A: { x | x>= t},
      we want our predicate to mean \not\in A, therefore 
      forall x, x < t: *)
 
  Definition valid (t:Object.address) := fun l => Object.lt l t.

  (** Rather than stating lemmas about =_A in general 
      (properties (4.3) to (4.7)), it is enough to 
      have some properties about valid: *)
  Lemma valid_add_l:
    forall e1 e2 t x,
      (forall x, Source.In x (Source.add e1 e2) -> Object.lt (loc x) t) ->
      Source.In x e1 -> valid t (loc x).
  Proof.
    intros. apply H. right. intuition. 
  Qed.

  Lemma valid_add_r:
    forall e1 e2 t x,
      (forall x, Source.In x (Source.add e1 e2) -> Object.lt (loc x) t) ->
      Source.In x e2 -> valid t (loc x).
  Proof.
    intros. apply H. right. intuition. 
  Qed.
  
  Lemma valid_ac_some:
     forall t, valid (Some t) Object.ac.
  Proof.
    intros. compute. constructor.
  Qed.

  Theorem compiler_correctness: 
    forall (e:Source.t)(env:Source.state)(η:Object.state)(t:nat),
      (forall x, Source.In x e -> Object.lt (loc x) (Some t)) ->
      (forall x, Source.In x e -> Source.c x env = Object.c (loc x) η) -> 
      Object.eqt (valid (Some t))
                 (Object.outcome (compile e t) η)
                 (Object.a Object.ac (Source.value e env) η).
  Proof.
    (* TO COMPLETE *)
    (* The proof can be roughly similarly to the paper *)
    (* Do not hesitate to use: 
       - set(...:=...)
       - assert *)
    induction e.
    intros e env n t H H0. 
    - simpl. trivial.
    - simpl. compute. intuition. destruct Object.eq_dec.
      + rewrite <- H0.
        * trivial.
        * constructor.
      + reflexivity.
    - intros.
      set(v  := (Source.value (Source.add e1 e2) env)) .
      set(v1 := (Source.value e1 env)) .
      set(v2 := (Source.value e2 env)) .

      set(η1 := Object.outcome (compile e1 t) η) .
      set(η2 := Object.outcome [Object.store (Some t)] η1) .
      set(η3 := Object.outcome (compile e2 (t + 1)) η2) .
      set(η4 := Object.outcome [Object.add (Some t)] η3) .

      simpl.
      assert (Object.eqt (valid (Some t)) η1 (Object.a Object.ac v1 η)) as H1. {
        simpl. apply IHe1.
        - intros. apply H.
          constructor. left. assumption.
        - intros. apply H0.
          constructor. left. assumption.
      }
      assert  ((Object.c Object.ac η1) = v1 ) as H2. {
        rewrite H1.
        - rewrite Object.c_a. 
          destruct (Object.eq_dec Object.ac Object.ac) eqn:Heq.
          + reflexivity.
          + assert ( Object.ac = Object.ac ) by reflexivity. contradiction.
        - unfold valid. constructor.
      }
      (*proven by η2*)
      assert (η2 = Object.a (Some t) (Object.c Object.ac η1) η1 ) as A1. {
       unfold η2. rewrite H2.
       unfold Object.outcome, Object.step.
       replace (Object.c Object.ac η1) with v1.
       reflexivity.
      }
      assert (η2 = (Object.a (Some t) v1 η1 )) as A2. {
       subst. rewrite A1. 
       replace (Object.c Object.ac η1) with (Source.value e1 env).
       reflexivity.
      }
      assert (Object.eqt (valid (Some (t + 1))) η2 (Object.a (Some t) v1 (Object.a Object.ac v1 η))) as A3. {
        rewrite A1. rewrite H1. 
        - simpl. admit. (*by 4.5*)
        - constructor.
      }
      Check Object.ac.
      (* Was unable to unify the valid_ac_some with the type: Object.address -> Prop. However, we know that the term valid_ac_some  
        has type (valid (Some t) Object.ac) which is a prop and we know that Object.ac has type Object.address, but we can't unify them.
      assert (Object.eqt ( valid_ac_some (t + 1)) η2 (Object.a (Some t) v1 η)) as A4. {
       admit.
      } *)
      assert  ((Object.c (Some t) η2) = v1 ) as A5. {
        unfold Object.c, η2. simpl. 
        admit. (*by 3.8*)
      }

      (*proven by η3*)
      assert (Object.eqt (valid (Some (t  + 1))) η3 (Object.a Object.ac v2 η2) ) as B1. {
        apply IHe2.
        - 
        (* apply H.
          constructor. left. assumption.
        - intros. apply H0.
          constructor. left. assumption.*)
        admit. - admit.
      }

      assert(forall x, Source.In x e2 -> (Object.c (loc x) η2) = (Object.c (loc x)) ((Object.a (Some t) v1 η))) as B2. { 
        admit. 
      }
      assert(forall x, Source.In x e2 -> (Object.c (loc x) η2) = (Object.c (loc x) η)) as B3. { 
       admit. 
      }
      assert (forall x, Source.In x e2 -> Object.c (loc x) η2  = (Source.c x env) ) as B4. {
       intros.
       admit.
      }

      assert (Object.eqt (valid (Some (t + 1))) η3 (Object.a Object.ac v2 (Object.a (Some t) v1 η))) as B5. {
        (*by 3.9?*)
        admit. 
      }
      (*proven by η4*)
      assert (η4 = (Object.a Object.ac ((Object.c (Some t) η3) + (Object.c Object.ac η3)) η3)) as C1. {
        constructor. 
      }
      assert (η4 = (Object.a Object.ac v η3 )) as C2. {
      rewrite C1. unfold v. simpl.
      (*Definition of v; substition*)
        admit. 
      }
      assert (Object.eqt (valid (Some (t + 1))) η4 (Object.a Object.ac v (Object.a Object.ac v2 (Object.a (Some t) v1 η)))) as C3. {
      (*by 4.5?*)
        admit.
      }
      assert (Object.eqt (valid (Some (t + 1))) η4  (Object.a Object.ac v (Object.a (Some t) v1 η ))) as C4. {
      (*by 3.9?*)
        admit.
      }
      assert (Object.eqt (valid (Some t)) η4 (Object.a Object.ac v η)) as C5. {
      (*by 3.9 and 4.6?*)
        admit.
      }
(*congruence. *)
  Admitted.


End compilation.