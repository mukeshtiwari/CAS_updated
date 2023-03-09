
Require Import Coq.Bool.Bool. 

Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.

Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.eqv.bool.

Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures.
Require Import CAS.coq.sg.classify.


Section Computation.

Definition bop_or     : binary_op bool := orb. 

End Computation.   


Section IntroElim.

Lemma bop_or_intro : ∀ b1 b2 : bool, (b1 = true) + (b2 = true) → bop_or b1 b2 = true. 
Proof. destruct b1; destruct b2; compute; intros [A | A]; auto. Qed. 

Lemma bop_or_elim : ∀ b1 b2 : bool, bop_or b1 b2 = true → (b1 = true) + (b2 = true). 
Proof. destruct b1; destruct b2; auto. Qed. 

Lemma bop_or_false_intro : ∀ b1 b2 : bool,  b1 = false → b2 = false → bop_or b1 b2 = false. 
Proof. destruct b1; destruct b2; auto. Qed. 

Lemma bop_or_false_elim : ∀ b1 b2 : bool, bop_or b1 b2 = false → (b1 = false) * (b2 = false). 
Proof.  destruct b1; destruct b2; auto. Qed. 

End IntroElim.   

Section Theory.

Lemma bop_or_congruence : bop_congruence bool brel_eq_bool bop_or.
Proof. intros s1 s2 t1 t2. destruct s1; destruct s2; destruct t1; destruct t2; compute; auto. Qed. 

Lemma bop_or_idempotent : bop_idempotent bool brel_eq_bool bop_or.
Proof. compute. induction s; simpl; reflexivity. Defined. 

Lemma bop_or_commutative : bop_commutative bool brel_eq_bool bop_or.
Proof. compute. induction s; induction t; simpl; reflexivity. Defined. 

Lemma bop_or_selective : bop_selective bool brel_eq_bool bop_or.
Proof. compute; induction s; induction t; auto. Qed.  

Lemma bop_or_associative : bop_associative bool brel_eq_bool bop_or.
Proof. compute. induction s; auto. induction t; auto. induction u; auto. Qed. 

Lemma bop_or_false_is_id : bop_is_id bool brel_eq_bool bop_or false. 
Proof. compute. induction s; auto. Qed.

Lemma bop_or_exists_id : bop_exists_id bool brel_eq_bool bop_or.
Proof. exists false. apply bop_or_false_is_id. Defined. 

Lemma bop_or_true_is_ann : bop_is_ann bool brel_eq_bool bop_or true. 
Proof. compute. induction s; auto. Qed.

Lemma bop_or_exists_ann : bop_exists_ann bool brel_eq_bool bop_or.
Proof. exists true. apply bop_or_true_is_ann. Defined. 

(*
Lemma bop_or_not_is_left : bop_not_is_left bool brel_eq_bool bop_or.
Proof. unfold bop_not_is_left. exists (false, true); simpl. reflexivity. Defined. 

Lemma bop_or_not_is_right : bop_not_is_right bool brel_eq_bool bop_or.
Proof. unfold bop_not_is_right. exists (true, false); simpl. reflexivity. Defined. 

Lemma bop_or_not_left_cancellative : bop_not_left_cancellative bool brel_eq_bool bop_or.
Proof. exists (true, (false, true)); simpl. auto. Defined. 

Lemma bop_or_not_right_cancellative : bop_not_right_cancellative bool brel_eq_bool bop_or.
Proof. exists (true, (false, true)); simpl. auto. Defined. 
  
Lemma bop_or_not_left_constant : bop_not_left_constant bool brel_eq_bool bop_or.
Proof. exists (false, (false, true)); simpl. auto. Defined. 

Lemma bop_or_not_right_constant : bop_not_right_constant bool brel_eq_bool bop_or.
Proof. exists (false, (false, true)); simpl. auto. Defined. 

Lemma bop_or_not_anti_left : bop_not_anti_left bool brel_eq_bool bop_or.
Proof. exists (true, false); simpl. auto. Defined. 

Lemma bop_or_not_anti_right : bop_not_anti_right bool brel_eq_bool bop_or.
Proof. exists (true, false); simpl. auto. Defined.


Lemma bop_or_somthing_is_finite : something_is_finite bool brel_eq_bool bop_or.
Proof. exact (exists_ann_implies_something_is_finite _ _ _ 
              bop_or_congruence
              brel_eq_bool_reflexive
              brel_eq_bool_symmetric
              brel_eq_bool_transitive
              bop_or_commutative
              bop_or_idempotent
              negb
              brel_eq_bool_not_trivial
              bop_or_exists_ann). 
Defined.
*) 

End Theory.

Section ACAS.

Definition sg_CS_proofs_or : sg_CS_proofs bool brel_eq_bool bop_or := 
{| 
  A_sg_CS_associative  := bop_or_associative
; A_sg_CS_congruence   := bop_or_congruence
; A_sg_CS_commutative  := bop_or_commutative
; A_sg_CS_selective    := bop_or_selective
|}. 


Definition A_sg_or : A_sg_CS bool
:= {| 
     A_sg_CS_eqv          := A_eqv_bool
   ; A_sg_CS_bop          := bop_or
   ; A_sg_CS_proofs       := sg_CS_proofs_or
   ; A_sg_CS_exists_id_d  := inl bop_or_exists_id 
   ; A_sg_CS_exists_ann_d := inl bop_or_exists_ann
   ; A_sg_CS_ast          := Ast_sg_or 
   |}. 



End ACAS.

Section AMCAS.

  Definition A_sg_or_below_sg_CS : @A_below_sg_CS bool :=
    A_classify_sg_CS A_sg_or. 

  Definition A_mcas_or : @A_sg_mcas bool := 
    A_MCAS_sg
      (A_Below_sg_sg_C
         (A_Below_sg_C_sg_CS A_sg_or_below_sg_CS)).


End AMCAS.  



Section CAS.



Definition sg_CS_certs_or : sg_CS_certificates (S := bool)
:= {| 
     sg_CS_associative        := Assert_Associative  
   ; sg_CS_congruence         := Assert_Bop_Congruence  
   ; sg_CS_commutative        := Assert_Commutative  
   ; sg_CS_selective          := Assert_Selective
   |}. 



Definition sg_or : @sg_CS bool
:= {| 
     sg_CS_eqv          := eqv_bool
   ; sg_CS_bop          := bop_or
   ; sg_CS_exists_id_d  := Certify_Exists_Id  false 
   ; sg_CS_exists_ann_d := Certify_Exists_Ann  true
   ; sg_CS_certs        := sg_CS_certs_or
   ; sg_CS_ast          := Ast_sg_or 
   |}. 
  

End CAS.

Section MCAS.

  Definition sg_or_below_sg_CS : @below_sg_CS bool :=
    classify_sg_CS sg_or. 

  Definition mcas_or : @sg_mcas bool := 
    MCAS_sg
      (Below_sg_sg_C
         (Below_sg_C_sg_CS sg_or_below_sg_CS)).

End MCAS.  


Section Verify.

Theorem correct_sg_CS_or : sg_or = A2C_sg_CS (A_sg_or). 
Proof. compute. reflexivity. Qed.

Theorem correct_mcas_sg_CS_or :
  mcas_or = A2C_sg_mcas A_mcas_or.
Proof. compute. reflexivity. Qed. 

End Verify.   
  
