(* Project 4: 

  Author: Charles Chawtin and Christopher D. Whitney 
  Last Modified: Dec. 9th, 2016
*) 

Require Import Arith ZArith List String WhileAndAm Bool Relation_Operators.
Import ListNotations.

Fixpoint CA (e:Aexp.t): code := 
  match e with 
  | Aexp.Int n => [(PUSH n)]
  | Aexp.Var x => [(FETCH x)]
  | Aexp.Binop Aexp.Add a1 a2 => (CA a2) ++ (CA a1) ++ [ADD]
  | Aexp.Binop Aexp.Mul a1 a2 => (CA a2) ++ (CA a1) ++ [MULT]
  | Aexp.Binop Aexp.Sub a1 a2 => (CA a2) ++ (CA a1) ++ [SUB]
  end.

Fixpoint CB (e:Bexp.t): code := 
  match e with 
  | Bexp.Bool true => [TRUE]
  | Bexp.Bool false => [FALSE]
  | Bexp.Neg t => CB t ++ [NEG]
  | Bexp.And t1 t2 => (CB t2) ++ (CB t1) ++ [AND]
  | Bexp.Cmp Bexp.Equal t1 t2 => (CA t2) ++ (CA t1) ++ [EQ]
  | Bexp.Cmp Bexp.LowerEq t1 t2 =>(CA t2) ++ (CA t1) ++ [LE]
  end.

Fixpoint CS (s:stm) : code := 
  match s with 
  | Assign x a => CA (a) ++ [STORE x]
  | Skip => [NOOP]
  | Seq s1 s2 => CS s1 ++ CS s2
  | If b s1 s2 => CB b  ++ [BRANCH (CS s1) (CS s2)]
  | While b s => [LOOP (CB b) (CS s)]
  end.


Module Examples. 
  
    Definition x : Id.t := Id.Id 0. 
    Definition y : Id.t := Id.Id 1.
    Definition z : Id.t := Id.Id 2.
    
    Example ex_4_10 : 
      CA (Aexp.Int 1%Z) ++ CA (Aexp.Var x) ++ [ADD] = [PUSH 1%Z] ++ [FETCH x] ++ [ADD]. 
      Proof. 
        compute. trivial.
      Qed.

    Example ex_4_12 :
      CS (Seq 
           (Assign y (Aexp.Int 1%Z))  
           (While (Bexp.Neg (Bexp.Cmp Bexp.Equal (Aexp.Var x) (Aexp.Int 1%Z))) 
                     (Seq (Assign y (Aexp.Binop Aexp.Mul (Aexp.Var x)  (Aexp.Var y))) 
                             (Assign x (Aexp.Binop Aexp.Sub (Aexp.Var x) (Aexp.Int 1%Z)))))) = 
           PUSH 1%Z :: STORE y :: [LOOP (PUSH 1%Z :: FETCH x :: EQ :: [NEG]) 
                                                         (FETCH y :: FETCH x :: MULT :: STORE y :: PUSH 1%Z :: FETCH x :: SUB :: [STORE x]) ].
    Proof.
        compute. trivial.
    Qed.
  
  Lemma lemma_4_18: 
    forall a s, 
      (clos_refl_trans_1n _ am) (CA a, [ ], s) ([ ], [Stack.z (Aexp.A a s)], s). 
  Proof.
    intros. induction a. 
    - simpl. econstructor. apply am_push. constructor.
    - simpl. econstructor. apply am_fetch. constructor.
    - simpl. destruct b.
       + repeat econstructor. simpl. (*rewrite am_add.*) admit.
       +  econstructor. (*apply am_mult.*)  admit.
  Admitted.

  Lemma lemma_4_19: 
     forall (b:Bexp.t) s, 
      (clos_refl_trans_1n _ am) (CB b, [ ], s) ([ ], [Stack.T (Bexp.B b s)], s). 
  Proof. 
  intros. induction b.
  - simpl.
     + destruct b;  repeat econstructor.
  - admit.
  Admitted.


  Lemma _4_21:
    forall (S:stm) (s:State.t) (s':State.t), 
      (ns S s s') -> (clos_refl_trans_1n _ am) (CS S, [ ], s) ([ ],[ ], s').
  Proof.
    intros S s s' NS.
    induction NS.
    - repeat econstructor.
    -  simpl.
         assert ((clos_refl_trans_1n _ am) (CA a,[ ], s) ([ ], [Stack.z (Aexp.A a s)], s)). { 
            apply lemma_4_18. }
         assert((clos_refl_trans_1n _ am) 
                    (CA a ++ [STORE x0], [ ], s) 
                    ([STORE x0], [Stack.z (Aexp.A a s)],s)). {

          (*SearchAbout clos_refl_trans_1n.*)
    apply Examples.ex_4_4' with (c2 := [STORE x0]) (e2 := []) in H. simpl in H. apply H.
        }
  
    apply Operators_Properties.clos_rt1n_rt in H0.
     (*??*)
    assert (Examples.am_star ([STORE x0], [Stack.z (Aexp.A a s)], s) ([], [], State.update s x0 (Aexp.A a s))).
    repeat econstructor. (*??*)

    apply Operators_Properties.clos_rt1n_rt in H1.
    apply Operators_Properties.clos_rt_rt1n.
    eapply rt_trans. eassumption. assumption.

    - simpl.
    apply Examples.ex_4_4' with (c2 := (CS S2)) (e2:= []) in IHNS1. simpl in IHNS1.
    apply Operators_Properties.clos_rt1n_rt in IHNS1.
    apply Operators_Properties.clos_rt1n_rt in IHNS2.
    apply Operators_Properties.clos_rt_rt1n.
    eapply rt_trans. eassumption. assumption.
    - simpl.
    set (HS := lemma_4_19 b s).
    apply Examples.ex_4_4' with (c2 := [BRANCH (CS S1) (CS S2)]) (e2:=[]) in HS.

    assert (Examples.am_star ([BRANCH (CS S1) (CS S2)], [Stack.T (Bexp.B b s)], s) (CS S1++[], [], s)).
    rewrite H.
    repeat econstructor. 
    simpl in *.
    rewrite app_nil_r in H0.
    
    apply Operators_Properties.clos_rt1n_rt in HS.
    apply Operators_Properties.clos_rt1n_rt in H0.
    apply Operators_Properties.clos_rt1n_rt in IHNS.
    apply Operators_Properties.clos_rt_rt1n.
    eapply rt_trans. eassumption.
    eapply rt_trans. eassumption. assumption.
    - simpl.
    set (HS := lemma_4_19 b s).
    apply Examples.ex_4_4' with (c2 := [BRANCH (CS S1) (CS S2)]) (e2:=[]) in HS.

    assert (Examples.am_star ([BRANCH (CS S1) (CS S2)], [Stack.T (Bexp.B b s)], s) (CS S2++[], [], s)).
    rewrite H.
    repeat econstructor. 
    simpl in *.
    rewrite app_nil_r in H0.
    
    apply Operators_Properties.clos_rt1n_rt in HS.
    apply Operators_Properties.clos_rt1n_rt in H0.
    apply Operators_Properties.clos_rt1n_rt in IHNS.
    apply Operators_Properties.clos_rt_rt1n.
    eapply rt_trans. eassumption.
    eapply rt_trans. eassumption. assumption.
    
    - simpl in *.
    assert (Examples.am_star ([LOOP (CB b) (CS S)], [], s) ([LOOP (CB b) (CS S)], [], s')).
    {
    econstructor. econstructor.
    set (HS := lemma_4_19 b s).
    apply Examples.ex_4_4' with (c2 := [BRANCH (CS S ++ [LOOP (CB b) (CS S)]) [NOOP]]) (e2:=[]) in HS.
    assert (Examples.am_star ([BRANCH (CS S ++ [LOOP (CB b) (CS S)]) [NOOP]], [Stack.T (Bexp.B b s)], s) (CS S++[LOOP (CB b) (CS S)], [], s)).
    rewrite H.
    simpl in *.
    econstructor. constructor.
    rewrite app_nil_r.
    constructor.
    simpl in *.
    
    apply Operators_Properties.clos_rt1n_rt in HS.
    apply Operators_Properties.clos_rt1n_rt in H0.
    apply Operators_Properties.clos_rt1n_rt in IHNS2.
    apply Examples.ex_4_4' with (c2:=[LOOP (CB b) (CS S)]) (e2:=[]) in IHNS1.
    simpl in IHNS1.
    apply Operators_Properties.clos_rt1n_rt in IHNS1.

    apply Operators_Properties.clos_rt_rt1n.
    eapply rt_trans. eassumption.
    eapply rt_trans. eassumption. assumption.
    }

    apply Operators_Properties.clos_rt1n_rt in H0.
    apply Operators_Properties.clos_rt1n_rt in IHNS2.
    
    apply Operators_Properties.clos_rt_rt1n.
    eapply rt_trans. eassumption. assumption.
   
   - simpl.
  
    apply Operators_Properties.clos_rt_rt1n.
    eapply rt_trans.
    repeat econstructor.
    eapply rt_trans.
    set (HS := lemma_4_19 b s).
    apply Examples.ex_4_4' with (c2:=[BRANCH (CS S ++ [LOOP (CB b) (CS S)]) [NOOP]]) (e2:=[]) in HS.
    simpl in *.
    apply Operators_Properties.clos_rt1n_rt in HS.
    eassumption.

    rewrite H.
    eapply rt_trans.
    set (HH := am_branch_ff ([]) (CS S ++ [LOOP (CB b) (CS S)]) ([NOOP]) s []).
    simpl in HH. 
    repeat econstructor.
    repeat econstructor.
  Qed.

   Lemma ca:
    forall a, exists i c, CA a = i::c.
    
   Admitted.

  Lemma cS:
    forall S, exists i c, CS S = i::c.
    
   Admitted.

    Lemma amS:
    forall S e s s',
      am (CS S, e, s) ([],[],s') ->
        S = Skip /\ e = [] /\ s = s'.
    Admitted.



  Lemma _4_22:
    forall k S s s' (e:Stack.t) , 
      (Examples.am_k k) (CS S, e, s) ([ ], [ ], s') -> 
          (ns S s s') /\ e = [ ].
   Proof. 
     intros k S s s' e.
     induction k.
     -  apply Empty_set_ind. admit.
     - destruct S. 
        + admit.
        + admit.
        + admit.
        + admit.
   Admitted.

End Examples.








