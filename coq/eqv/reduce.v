Require Import CAS.coq.common.base.
Require Import CAS.coq.theory.facts. 

Section Theory.

  Variable S: Type.
  Variable eq : brel S.
  Variable r  : unary_op S.  
  Variable refS : brel_reflexive S eq.
  Variable symS : brel_symmetric S eq.
  Variable tranS : brel_transitive S eq.

Lemma brel_reduce_congruence : brel_congruence S eq eq -> brel_congruence S (brel_reduce eq r) (brel_reduce eq r). 
Proof. intro congS. compute. intros s t w v H1 H2. apply congS; auto. Qed. 
  

Lemma brel_reduce_reflexive : brel_reflexive S (brel_reduce eq r). 
Proof. intro s. unfold brel_reduce. apply refS. Defined. 

Lemma brel_reduce_symmetric : brel_symmetric S (brel_reduce eq r). 
Proof. intros s t. unfold brel_reduce. apply symS. Defined. 

Lemma brel_reduce_transitive : brel_transitive S (brel_reduce eq r). 
Proof. intros s t u. unfold brel_reduce.  apply tranS. Defined.          

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
  

Lemma brel_set_not_trivial (f : S -> S) :
  (∀ x : S, eq (r x) (r (f x)) = false) ->  
  brel_not_trivial S (brel_reduce eq r) f. 
Proof. intros H x. compute. 
       split.
       apply H.
       apply (brel_symmetric_implies_dual _ _ symS _ _ (H x)). 
Qed.

(*
Lemma brel_set_at_least_three :
  brel_at_least_three S eq -> 
  brel_at_least_three S (brel_reduce eq r).
Proof. intros [[a [b c]] [[H1 H2] H3]]. 
       exists (r , (s :: nil, (f s) :: nil)).
       destruct (nt s) as [L R].
       compute. rewrite L; auto. 
Defined. 


Lemma brel_set_not_exactly_two (s : S) (f : S -> S):
  brel_not_trivial S eq f -> 
  brel_not_exactly_two (finite_set S) (brel_set eq).
Proof. intro nt. apply brel_at_least_thee_implies_not_exactly_two.
       apply brel_set_symmetric; auto. 
       apply brel_set_transitive; auto.
       apply (brel_set_at_least_three s f); auto. 
Defined.
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
           (ex2 : brel_exactly_two_decidable S (brel_reduce (A_eqv_eq S eqvS) r)): A_eqv S
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
    ; A_eqv_ast           := Ast_eqv_reduce (A_eqv_ast S eqvS)
   |}. 


End ACAS.

Section CAS.


Definition eqv_reduce {S : Type} (r : S -> S) (f : S -> S) (ex2 : @check_exactly_two S) (eqvS : @eqv S) : @eqv S
:= 
  let eq := eqv_eq eqvS in
  let s := eqv_witness eqvS in
 {| 
     eqv_eq       := brel_reduce eq r
    ; eqv_witness := r s 
    ; eqv_new     := f 
    ; eqv_exactly_two_d := ex2 
    ; eqv_data    := λ d, eqv_data eqvS (r d)  
    ; eqv_rep     := r 
    ; eqv_ast     := Ast_eqv_reduce (eqv_ast eqvS)
   |}. 



End CAS.

Section Verify.


Theorem correct_eqv_set : ∀ (S : Type) (E : A_eqv S) (r : unary_op S) (f : S -> S) 
      (nt: brel_not_trivial S (brel_reduce (A_eqv_eq S E) r) f)
      (ex2 : brel_exactly_two_decidable S (brel_reduce (A_eqv_eq S E) r)),  
    
    eqv_reduce r f (p2c_exactly_two_check _ _ ex2) (A2C_eqv S E) = A2C_eqv S(A_eqv_reduce S E r f nt ex2).
Proof. intros S E r f nt ex2. destruct E; destruct ex2; compute; auto. Qed.        
 
End Verify.   
  