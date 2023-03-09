Require Import Coq.Arith.Arith.     (* beq_nat *) 
Require Import Coq.Arith.Min.

Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.

Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.eqv.nat.

Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.theory.
Require Import CAS.coq.sg.structures.
Require Import CAS.coq.sg.classify. 

Section Theory.
  Open Scope nat.
  
Lemma beq_nat_min_congruence : 
   ∀ s1 s2 t1 t2 : nat,
   beq_nat s1 t1 = true
   → beq_nat s2 t2 = true → beq_nat (min s1 s2) (min t1 t2) = true.
Proof. 
   intros s1 s2 t1 t2 H1 H2. 
   assert (C1 := beq_nat_to_prop s1 t1 H1). 
   assert (C2 := beq_nat_to_prop s2 t2 H2). 
   rewrite C1. rewrite C2.  apply brel_eq_nat_reflexive. 
Defined. 

Lemma bop_min_congruence : bop_congruence nat brel_eq_nat bop_min.
Proof. unfold bop_congruence. unfold brel_eq_nat, bop_min.
       exact beq_nat_min_congruence. 
Defined. 

Lemma bop_min_associative : bop_associative nat brel_eq_nat bop_min.
Proof. unfold bop_associative. intros. unfold brel_eq_nat, bop_min. 
       rewrite (Min.min_assoc s t u). apply brel_eq_nat_reflexive.        
Defined. 


Lemma bop_min_idempotent : bop_idempotent nat brel_eq_nat bop_min.
Proof. unfold bop_idempotent, bop_min. induction s; simpl. 
       reflexivity. 
       assumption. 
Defined. 

Lemma bop_min_commutative : bop_commutative nat brel_eq_nat bop_min.
Proof. unfold bop_commutative, bop_min. intros s t. 
       rewrite Min.min_comm at 1. apply brel_eq_nat_reflexive. 
Defined. 

Lemma bop_min_selective : bop_selective nat brel_eq_nat bop_min.
Proof. unfold bop_selective. induction s; induction t; simpl. 
      right. reflexivity. left. reflexivity. right. reflexivity. apply IHs. 
Defined. 

Lemma bop_min_not_is_left : bop_not_is_left nat brel_eq_nat bop_min.
Proof. unfold bop_not_is_left. exists (1, 0); simpl. reflexivity. Defined. 

Lemma bop_min_not_is_right : bop_not_is_right nat brel_eq_nat bop_min.
Proof. unfold bop_not_is_left. exists (0, 1); simpl. reflexivity. Defined. 


Lemma bop_min_S : ∀ s t : nat, bop_min (S s) (S t) = S (bop_min s t). 
Proof. unfold bop_min. induction s; induction t; compute; reflexivity. Defined. 

Lemma bop_min_not_exists_id : bop_not_exists_id nat brel_eq_nat bop_min.
Proof. unfold bop_not_exists_id. induction i. 
       exists 1. left. compute. reflexivity. 
       destruct IHi as [s [H | H]]. 
          exists (S s). left.  rewrite bop_min_S. rewrite brel_nat_eq_S. assumption. 
          exists (S s). right.  rewrite bop_min_S. rewrite brel_nat_eq_S. assumption. 
Defined. 

Lemma bop_min_zero_is_ann : bop_is_ann nat brel_eq_nat bop_min 0.
Proof. intro s. unfold bop_min. split. 
       unfold min. apply brel_eq_nat_reflexive. 
       rewrite min_comm. unfold min. apply brel_eq_nat_reflexive.
Qed.        
  
Lemma bop_min_exists_ann : bop_exists_ann nat brel_eq_nat bop_min.
Proof. exists 0. apply bop_min_zero_is_ann. Defined. 

Lemma bop_min_not_left_cancellative : bop_not_left_cancellative nat brel_eq_nat bop_min.
Proof. exists (0, (0, 1)); simpl. auto. Defined. 

Lemma bop_min_not_right_cancellative : bop_not_right_cancellative nat brel_eq_nat bop_min.
Proof. exists (0, (0, 1)); simpl. auto. Defined. 
  
Lemma bop_min_not_left_constant : bop_not_left_constant nat brel_eq_nat bop_min.
Proof. exists (1, (0, 1)); simpl. auto. Defined. 

Lemma bop_min_not_right_constant : bop_not_right_constant nat brel_eq_nat bop_min.
Proof. exists (1, (0, 1)); simpl. auto. Defined. 

Lemma bop_min_not_anti_right : bop_not_anti_right nat brel_eq_nat bop_min.
Proof. exists (0, 1); simpl. auto. Defined. 

Lemma bop_min_not_anti_left : bop_not_anti_left nat brel_eq_nat bop_min.
Proof. exists (0, 1); simpl. auto. Defined. 

(*
Lemma bop_min_somthing_is_finite : something_is_finite nat brel_eq_nat bop_min.
Proof. exact (exists_ann_implies_something_is_finite _ _ _ 
              bop_min_congruence
              brel_eq_nat_reflexive
              brel_eq_nat_symmetric
              brel_eq_nat_transitive
              bop_min_commutative
              bop_min_idempotent
              S
              brel_eq_nat_not_trivial
              bop_min_exists_ann). 
Defined.
*) 

End Theory.

Section ACAS.
  
Definition sg_CS_proofs_min : sg_CS_proofs nat brel_eq_nat bop_min := 
{| 
  A_sg_CS_associative  := bop_min_associative
; A_sg_CS_congruence   := bop_min_congruence
; A_sg_CS_commutative  := bop_min_commutative
; A_sg_CS_selective    := bop_min_selective
|}. 



Definition A_sg_min : A_sg_CS nat 
:= {| 
     A_sg_CS_eqv          := A_eqv_nat 
   ; A_sg_CS_bop          := bop_min
   ; A_sg_CS_exists_id_d  := inr bop_min_not_exists_id
   ; A_sg_CS_exists_ann_d := inl bop_min_exists_ann
   ; A_sg_CS_proofs       := sg_CS_proofs_min
   ; A_sg_CS_ast          := Ast_sg_min 
   |}. 


End ACAS.


Section AMCAS.

 Definition A_sg_min_below_sg_CS := A_classify_sg_CS A_sg_min.     

 Definition A_mcas_sg_min : @A_sg_mcas nat :=
   A_MCAS_sg (A_Below_sg_sg_C (A_Below_sg_C_sg_CS (A_sg_min_below_sg_CS))). 


End AMCAS.  

Section CAS.
Open Scope nat.   

Definition sg_CS_certs_min : @sg_CS_certificates nat 
:= {|
     sg_CS_associative        := Assert_Associative 
   ; sg_CS_congruence         := Assert_Bop_Congruence 
   ; sg_CS_commutative        := Assert_Commutative 
   ; sg_CS_selective          := Assert_Selective
   |}. 



Definition sg_min : @sg_CS nat 
:= {| 
     sg_CS_eqv          := eqv_eq_nat 
   ; sg_CS_bop          := bop_min 
   ; sg_CS_exists_id_d  := Certify_Not_Exists_Id 
   ; sg_CS_exists_ann_d := Certify_Exists_Ann 0
   ; sg_CS_certs        := sg_CS_certs_min
   ; sg_CS_ast          := Ast_sg_min 
   |}. 
  

End CAS.

Section MCAS.

 Definition sg_min_below_sg_CS := classify_sg_CS sg_min.     

 Definition mcas_sg_min : @sg_mcas nat :=
   MCAS_sg (Below_sg_sg_C (Below_sg_C_sg_CS (sg_min_below_sg_CS))). 


End MCAS.  


Section Verify.

Theorem correct_sg_min : sg_min = A2C_sg_CS (A_sg_min). 
Proof. compute. reflexivity. Qed. 

Theorem correct_mcas_sg_min : mcas_sg_min = A2C_sg_mcas (A_mcas_sg_min). 
Proof. compute. reflexivity. Qed. 

End Verify.   
  
