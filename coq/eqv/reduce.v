Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.
Require Import CAS.coq.common.data.
Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.or.properties.
Require Import CAS.coq.uop.properties. 
Require Import CAS.coq.eqv.theory.

Section Computation.

  Definition brel_reduce : ∀ {S : Type}, brel S → unary_op S → brel S
    := λ {S} eq r x y,  eq (r x) (r y).

End Computation.   

Section Theory.

  Variable S: Type.
  Variable eq : brel S.
  Variable r  : unary_op S.  
  Variable refS : brel_reflexive S eq.
  Variable symS : brel_symmetric S eq.
  Variable trnS : brel_transitive S eq.
  Variable eqS_cong : brel_congruence S eq eq.

  (* classic equality for reductions *)

  Definition is_a_fixed_point (x : S) := eq (r x) x = true.  
  Definition reduced_type := { x : S & is_a_fixed_point x}.

  (* equality on reduced_type is just equality on S, but need to project out first components! *) 
  Definition reduced_equality : brel reduced_type := λ p1 p2, eq ((projT1 p1)) ((projT1 p2)).

  Lemma reduced_equality_congruence : brel_congruence reduced_type reduced_equality reduced_equality. 
  Proof. intros [s1 p1] [s2 p2] [s3 p3] [s4 p4].   compute. apply eqS_cong. Qed. 

  Lemma reduced_equality_reflexive : brel_reflexive reduced_type reduced_equality. 
  Proof. intros [s p]. compute. apply refS. Qed.
       
  Lemma reduced_equality_symmetric : brel_symmetric reduced_type reduced_equality. 
  Proof. intros [s1 p1] [s2 p2].   compute. apply symS. Qed.

  Lemma reduced_equality_transitive : brel_transitive reduced_type reduced_equality. 
  Proof. intros [s1 p1] [s2 p2] [s3 p3]. compute. apply trnS. Qed.
  

  (* "OCaml friendly" representation of equality *)
  
  Lemma brel_reduce_congruence : brel_congruence S eq eq -> brel_congruence S (brel_reduce eq r) (brel_reduce eq r). 
  Proof. intro congS. compute. intros s t w v H1 H2. apply congS; auto. Qed. 

  Lemma brel_reduce_reflexive : brel_reflexive S (brel_reduce eq r). 
  Proof. intro s. unfold brel_reduce. apply refS. Defined. 

  Lemma brel_reduce_symmetric : brel_symmetric S (brel_reduce eq r). 
  Proof. intros s t. unfold brel_reduce. apply symS. Defined. 

  Lemma brel_reduce_transitive : brel_transitive S (brel_reduce eq r). 
  Proof. intros s t u. unfold brel_reduce.  apply trnS. Defined.          


(*
 These equalities are the same when r is idempotent. 
*)

Definition inject_into_reduced_type (r_idem  : uop_idempotent S eq r) (s : S) : reduced_type :=
    existT is_a_fixed_point (r s) (r_idem s).
  
Lemma reduced_equality_congruence_iff (r_idem  : uop_idempotent S eq r) :
  brel_congruence reduced_type reduced_equality reduced_equality
  <->
  brel_congruence S (brel_reduce eq r) (brel_reduce eq r).
Proof. split. intros H x y m n. compute. intros H1 H2.
       assert (K := H (inject_into_reduced_type r_idem x)
                      (inject_into_reduced_type r_idem y)
                      (inject_into_reduced_type r_idem m)
                      (inject_into_reduced_type r_idem n)). compute in K. 
       apply K; auto.
       intros H [s1 p1] [s2 p2] [s3 p3] [s4 p4].
       compute. apply eqS_cong.
Qed. 

Lemma reduced_equality_reflexive_iff (r_idem  : uop_idempotent S eq r) :
  brel_reflexive reduced_type reduced_equality
  <->
  brel_reflexive S (brel_reduce eq r).
  Proof. split. intros H s. compute.
         assert (K := H (inject_into_reduced_type r_idem s)).
         unfold reduced_equality in K. simpl in K.
         exact K. 
         intros H [s p]. unfold is_a_fixed_point in p.
         compute. apply refS. 
Qed.          

Lemma reduced_equality_symmetric_iff (r_idem  : uop_idempotent S eq r) :
  brel_symmetric reduced_type reduced_equality
  <->
  brel_symmetric S (brel_reduce eq r).
  Proof. split. intros H s1 s2. compute.
         assert (K := H (inject_into_reduced_type r_idem  s1)
                        (inject_into_reduced_type r_idem  s2)).
         unfold reduced_equality in K. simpl in K.
         exact K. 
         intros H [s1 p1] [s2 p2]. unfold is_a_fixed_point in p1. unfold is_a_fixed_point in p2.
         compute. intro H2. 
         assert (K := symS _ _ H2).
         exact K.
Qed.          

Lemma reduced_equality_transitive_iff (r_idem  : uop_idempotent S eq r) :
  brel_transitive reduced_type reduced_equality
  <->
  brel_transitive S (brel_reduce eq r).
  Proof. split. intros H s1 s2 s3. compute. intros H1 H2. 
         assert (K := H (inject_into_reduced_type r_idem  s1)
                        (inject_into_reduced_type r_idem  s2)
                        (inject_into_reduced_type r_idem  s3)). compute in K. 
         apply K; auto. 
         intros H [s1 p1] [s2 p2] [s3 p3]. 
         compute. apply trnS. 
Qed.          

  
(*
Lemma brel_reduce_antisymmetric : 
    brel_antisymmetric S eq eq  →
    brel_antisymmetric S (brel_reduce eq r) (brel_reduce eq r). 
Proof. unfold brel_antisymmetric. unfold brel_reduce. 
       intros asymS s t H1 H2.
       apply asymS; auto. 
Defined.

Lemma brel_reduce_not_antisymmetric : 
    uop_congruence S eq r →        
    uop_injective S eq r →    
    brel_not_antisymmetric S eq eq  →
    brel_not_antisymmetric S (brel_reduce eq r) (brel_reduce eq r). 
Proof. unfold brel_not_antisymmetric. unfold brel_reduce. 
       intros cong injS [[s t] [[H1 H2] H3]].
       exists (s, t).
       split. split. apply cong; auto. apply cong; auto.
       case_eq(eq (r s) (r t)); intro J.
          apply injS in J. rewrite J in H3. discriminate H3.
          reflexivity.
Defined. 

Lemma brel_reduce_not_trivial (f : S -> S) :
  (∀ x : S, eq (r x) (r (f x)) = false) ->  
  brel_not_trivial S (brel_reduce eq r) f. 
Proof. intros H x. compute. 
       split.
       apply H.
       apply (brel_symmetric_implies_dual _ _ symS _ _ (H x)). 
Qed.
*) 

End Theory.

Section ACAS.


Definition eqv_proofs_reduce : ∀ (S : Type) (eq : brel S) (r : unary_op S),
    eqv_proofs S eq → eqv_proofs S (brel_reduce eq r) 
:= λ S eq r eqv, 
   {| 
     A_eqv_congruence  := brel_reduce_congruence S eq r (A_eqv_congruence S eq eqv) 
   ; A_eqv_reflexive   := brel_reduce_reflexive S eq r (A_eqv_reflexive S eq eqv)
   ; A_eqv_transitive  := brel_reduce_transitive S eq r (A_eqv_transitive S eq eqv) 
   ; A_eqv_symmetric   := brel_reduce_symmetric S eq r (A_eqv_symmetric S eq eqv)
   |}. 

Definition A_eqv_reduce
           (S : Type)
           (eqvS : A_eqv S)
           (r : unary_op S)
           (f : S -> S)
           (nt: brel_not_trivial S (brel_reduce (A_eqv_eq S eqvS) r) f)
           (ex2 : brel_exactly_two_decidable S (brel_reduce (A_eqv_eq S eqvS) r))
           (fin : carrier_is_finite_decidable S (brel_reduce (A_eqv_eq S eqvS) r))
           (ast : cas_eqv_ast)
           : A_eqv S
                                                                                         
:= 
  let eq := A_eqv_eq S eqvS in
  let s  := A_eqv_witness S eqvS in
  let eqP := A_eqv_proofs S eqvS in
   {| 
      A_eqv_eq            := brel_reduce eq r 
    ; A_eqv_proofs        := eqv_proofs_reduce S eq r eqP 
    ; A_eqv_witness       := r s 
    ; A_eqv_new           := f 
    ; A_eqv_not_trivial   := nt 
    ; A_eqv_exactly_two_d := ex2 
    ; A_eqv_data          := λ d, A_eqv_data S eqvS (r d)  
    ; A_eqv_rep           := r
    ; A_eqv_finite_d      := fin
    ; A_eqv_ast           := ast 
   |}. 


End ACAS.

Section CAS.


Definition eqv_reduce {S : Type}
      (r : S -> S) (f : S -> S) (ex2 : @check_exactly_two S) (fin : @check_is_finite S)  (eqvS : @eqv S) (ast : cas_eqv_ast) : @eqv S
:= 
  let eq := eqv_eq eqvS in
  let s := eqv_witness eqvS in
 {| 
      eqv_eq       := brel_reduce eq r
    ; eqv_certs    :=
     {|
       eqv_congruence     := @Assert_Brel_Congruence S 
     ; eqv_reflexive      := @Assert_Reflexive S
     ; eqv_transitive     := @Assert_Transitive S
     ; eqv_symmetric      := @Assert_Symmetric S
     |}  
    ; eqv_witness := r s 
    ; eqv_new     := f 
    ; eqv_exactly_two_d := ex2 
    ; eqv_data    := λ d, eqv_data eqvS (r d)  
    ; eqv_rep     := r
    ; eqv_finite_d  := fin                     
    ; eqv_ast     := ast 
   |}. 

End CAS.

Section Verify.


Theorem correct_eqv_reduce : ∀ (S : Type) (E : A_eqv S) (r : unary_op S) (f : S -> S) 
      (nt: brel_not_trivial S (brel_reduce (A_eqv_eq S E) r) f)
      (ex2 : brel_exactly_two_decidable S (brel_reduce (A_eqv_eq S E) r))
      (fin : carrier_is_finite_decidable S (brel_reduce (A_eqv_eq S E) r))
      (ast : cas_eqv_ast),  
    
    eqv_reduce r f (p2c_exactly_two_check _ _ ex2) (p2c_is_finite_check _ _ fin) (A2C_eqv S E) ast
    =
    A2C_eqv S (A_eqv_reduce S E r f nt ex2 fin ast).
Proof. intros S E r f nt ex2 ast. destruct E; destruct ex2; compute; auto. Qed.        
 
End Verify.   
  
