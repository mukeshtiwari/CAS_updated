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

Definition bop_and : binary_op bool := andb.   

End Computation.   

Section IntroElim.

Lemma bop_and_intro : ∀ b1 b2 : bool, (b1 = true) →  (b2 = true) → bop_and b1 b2 = true. 
Proof. unfold bop_and. intros b1 b2 A B. rewrite A, B. compute. reflexivity. Qed. 

Lemma bop_and_elim : ∀ b1 b2 : bool, bop_and b1 b2 = true → (b1 = true) * (b2 = true). 
Proof. intros b1 b2;destruct b1; destruct b2; compute; intro H; auto. Qed. 

Lemma bop_and_false_intro : ∀ b1 b2 : bool, (b1 = false) + (b2 = false) → bop_and b1 b2 = false. 
Proof. intros b1 b2 [A | A]; rewrite A; compute. reflexivity. destruct b1; reflexivity. Qed. 

Lemma bop_and_false_elim : ∀ b1 b2 : bool, bop_and b1 b2 = false → (b1 = false) + (b2 = false). 
Proof. unfold bop_and. intros b1 b2. destruct b1; destruct b2; compute; auto. Qed. 

End IntroElim.   

Section Theory.
  
Lemma bop_and_congruence : bop_congruence bool brel_eq_bool bop_and.
Proof. intros s1 s2 t1 t2. destruct s1; destruct s2; destruct t1; destruct t2; compute; auto. Qed. 

Lemma bop_and_associative : bop_associative bool brel_eq_bool bop_and.
Proof. compute. destruct s; auto. destruct t; auto.  destruct u; auto. Qed. 

Lemma bop_and_idempotent : bop_idempotent bool brel_eq_bool bop_and.
Proof. compute. induction s; simpl; reflexivity. Qed. 

Lemma bop_and_commutative : bop_commutative bool brel_eq_bool bop_and.
Proof. compute; induction s; induction t; simpl; reflexivity. Qed. 

Lemma bop_and_selective : bop_selective bool brel_eq_bool bop_and.
Proof. compute; induction s; induction t; auto. Qed.


Lemma bop_and_true_is_id : bop_is_id bool brel_eq_bool bop_and true. 
Proof. compute. induction s; auto. Qed.

Lemma bop_and_exists_id : bop_exists_id bool brel_eq_bool bop_and.
Proof. exists true. apply bop_and_true_is_id. Defined. 

Lemma bop_and_false_is_ann : bop_is_ann bool brel_eq_bool bop_and false. 
Proof. compute. induction s; auto. Qed.

Lemma bop_and_exists_ann : bop_exists_ann bool brel_eq_bool bop_and.
Proof. exists false. apply bop_and_false_is_ann. Defined. 

(*
Lemma bop_and_not_is_left : bop_not_is_left bool brel_eq_bool bop_and.
Proof. compute. exists (true, false); simpl. reflexivity. Defined. 
 
Lemma bop_and_not_is_right : bop_not_is_right bool brel_eq_bool bop_and.
Proof. compute. exists (false, true); simpl. reflexivity. Defined.

Lemma bop_and_not_left_cancellative : bop_not_left_cancellative bool brel_eq_bool bop_and.
Proof. exists (false, (false, true)); simpl. auto. Defined. 

Lemma bop_and_not_right_cancellative : bop_not_right_cancellative bool brel_eq_bool bop_and.
Proof. exists (false, (false, true)); simpl. auto. Defined. 
  
Lemma bop_and_not_left_constant : bop_not_left_constant bool brel_eq_bool bop_and.
Proof. exists (true, (false, true)); simpl. auto. Defined. 

Lemma bop_and_not_right_constant : bop_not_right_constant bool brel_eq_bool bop_and.
Proof. exists (true, (false, true)); simpl. auto. Defined. 

Lemma bop_and_not_anti_left : bop_not_anti_left bool brel_eq_bool bop_and.
Proof. exists (false, true); simpl. auto. Defined. 

Lemma bop_and_not_anti_right : bop_not_anti_right bool brel_eq_bool bop_and.
Proof. exists (false, true); simpl. auto. Defined.

Lemma bop_and_somthing_is_finite : something_is_finite bool brel_eq_bool bop_and.
Proof. exact (exists_ann_implies_something_is_finite _ _ _ 
              bop_and_congruence
              brel_eq_bool_reflexive
              brel_eq_bool_symmetric
              brel_eq_bool_transitive
              bop_and_commutative
              bop_and_idempotent
              negb
              brel_eq_bool_not_trivial
              bop_and_exists_ann). 
Defined.
*) 


End Theory.

Section ACAS.

Definition sg_CS_proofs_and : sg_CS_proofs bool brel_eq_bool bop_and := 
{| 
  A_sg_CS_associative  := bop_and_associative
; A_sg_CS_congruence   := bop_and_congruence
; A_sg_CS_commutative  := bop_and_commutative
; A_sg_CS_selective    := bop_and_selective
|}. 

Definition A_sg_and : A_sg_CS bool
:= {| 
     A_sg_CS_eqv          := A_eqv_bool
   ; A_sg_CS_bop          := bop_and
   ; A_sg_CS_exists_id_d  := inl bop_and_exists_id 
   ; A_sg_CS_exists_ann_d := inl bop_and_exists_ann 
   ; A_sg_CS_proofs       := sg_CS_proofs_and
   ; A_sg_CS_ast          := Ast_sg_and 
   |}. 

End ACAS.

Section AMCAS.

  Definition A_sg_and_below_sg_CS : @A_below_sg_CS bool :=
    A_classify_sg_CS A_sg_and. 

  Definition A_mcas_and : @A_sg_mcas bool := 
    A_MCAS_sg
      (A_Below_sg_sg_C
         (A_Below_sg_C_sg_CS A_sg_and_below_sg_CS)).

End AMCAS.  

Section CAS.


Definition sg_CS_certs_and : @sg_CS_certificates bool
:= {| 
     sg_CS_associative        := Assert_Associative  
   ; sg_CS_congruence         := Assert_Bop_Congruence  
   ; sg_CS_commutative        := Assert_Commutative  
   ; sg_CS_selective          := Assert_Selective
   |}. 


Definition sg_and : @sg_CS bool
:= {| 
     sg_CS_eqv          := eqv_bool
   ; sg_CS_bop          := bop_and
   ; sg_CS_exists_id_d  := Certify_Exists_Id  true 
   ; sg_CS_exists_ann_d := Certify_Exists_Ann  false 
   ; sg_CS_certs        := sg_CS_certs_and
   ; sg_CS_ast          := Ast_sg_and 
   |}. 
  
End CAS.

Section MCAS.

  Definition sg_and_below_sg_CS : @below_sg_CS bool :=
    classify_sg_CS sg_and. 

  Definition mcas_and : @sg_mcas bool := 
    MCAS_sg
      (Below_sg_sg_C
         (Below_sg_C_sg_CS sg_and_below_sg_CS)).


End MCAS.  


Section Verify.


Theorem correct_sg_CS_and : sg_and = A2C_sg_CS A_sg_and. 
Proof. compute. reflexivity. Qed. 


Theorem correct_mcas_sg_CS_and :
  mcas_and = A2C_sg_mcas A_mcas_and. 
Proof. compute. reflexivity. Qed. 
 
End Verify.   

