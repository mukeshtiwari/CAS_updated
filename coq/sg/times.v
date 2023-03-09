Require Import Coq.Arith.Arith.     (* beq_nat *)

Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.

Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.eqv.nat. 

Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures.
Require Import CAS.coq.sg.classify. 


Section Theory.

Open Scope nat.   

Lemma beq_nat_times_congruence : 
   ∀ s1 s2 t1 t2 : nat,    beq_nat s1 t1 = true
   → beq_nat s2 t2 = true → beq_nat (mult s1 s2) (mult t1 t2) = true.
Proof. 
   intros s1 s2 t1 t2 H1 H2. 
   assert (C1 := beq_nat_to_prop s1 t1 H1). 
   assert (C2 := beq_nat_to_prop s2 t2 H2). 
   rewrite C1. rewrite C2.  apply brel_eq_nat_reflexive. 
Defined. 

Lemma bop_times_congruence : bop_congruence nat brel_eq_nat bop_times.
Proof. unfold bop_congruence. unfold brel_eq_nat, bop_times.
       exact beq_nat_times_congruence. 
Defined. 

Lemma bop_times_associative : bop_associative nat brel_eq_nat bop_times.
Proof. unfold bop_associative. intros. unfold brel_eq_nat, bop_times. 
       rewrite (Mult.mult_assoc s t u). apply brel_eq_nat_reflexive.        
Defined. 

Lemma bop_times_not_idempotent : bop_not_idempotent nat brel_eq_nat bop_times.
Proof. unfold bop_not_idempotent. exists 2. simpl. reflexivity. Defined. 

Lemma bop_times_commutative : bop_commutative nat brel_eq_nat bop_times.
Proof. unfold bop_commutative, bop_times. intros s t. 
       rewrite Mult.mult_comm at 1. apply brel_eq_nat_reflexive. 
Defined. 

Lemma bop_times_not_selective : bop_not_selective nat brel_eq_nat bop_times.
Proof. unfold bop_not_selective. exists (2, 2); simpl. split; reflexivity. 
Defined. 

Lemma bop_times_not_is_left : bop_not_is_left nat brel_eq_nat bop_times.
Proof. unfold bop_is_left. exists (1, 0); simpl. reflexivity. Defined. 

Lemma bop_times_not_is_right : bop_not_is_right nat brel_eq_nat bop_times.
Proof. unfold bop_not_is_left. exists (0, 1); simpl. reflexivity. Defined. 

Lemma bop_times_one_is_id : bop_is_id nat brel_eq_nat bop_times 1.
Proof. intro s. unfold bop_times. split. 
       unfold mult. rewrite plus_comm. simpl. apply brel_eq_nat_reflexive. 
       rewrite mult_comm. simpl. rewrite plus_comm. simpl. apply brel_eq_nat_reflexive. 
Qed. 

Lemma bop_times_exists_id : bop_exists_id nat brel_eq_nat bop_times.
Proof. exists 1. apply bop_times_one_is_id. Defined. 


Lemma bop_times_zero_is_ann : bop_is_ann nat brel_eq_nat bop_times 0.
Proof. intro s. unfold bop_times. split. 
       unfold mult. apply brel_eq_nat_reflexive. 
       rewrite mult_comm. simpl. reflexivity. 
Qed. 

Lemma bop_times_exists_ann : bop_exists_ann nat brel_eq_nat bop_times.
Proof. exists 0. apply bop_times_zero_is_ann. Defined. 


Lemma  bop_times_not_left_cancellative : bop_not_left_cancellative nat brel_eq_nat bop_times.
Proof. exists (0, (0, 1)); simpl. auto. Defined. 

Lemma  bop_times_not_right_cancellative : bop_not_right_cancellative nat brel_eq_nat bop_times.
Proof. exists (0, (0, 1)); simpl. auto. Defined. 

Lemma bop_times_not_left_constant : bop_not_left_constant nat brel_eq_nat bop_times.
Proof. exists (1, (0, 1)); simpl. auto. Defined. 

Lemma bop_times_not_right_constant : bop_not_right_constant nat brel_eq_nat bop_times.
Proof. exists (1, (0, 1)); simpl. auto. Defined. 

Lemma bop_times_not_anti_left : bop_not_anti_left nat brel_eq_nat bop_times.
Proof. exists (0, 0); simpl. auto. Defined. 

Lemma bop_times_not_anti_right : bop_not_anti_right nat brel_eq_nat bop_times.
Proof. exists (0, 0); simpl. auto. Defined. 

End Theory.

Section ACAS.

Definition sg_proofs_times : sg_proofs nat brel_eq_nat bop_times := 
{| 
  A_sg_associative      := bop_times_associative
; A_sg_congruence       := bop_times_congruence
; A_sg_commutative_d    := inl bop_times_commutative
; A_sg_selective_d      := inr bop_times_not_selective
; A_sg_idempotent_d     := inr bop_times_not_idempotent
; A_sg_is_left_d        := inr bop_times_not_is_left
; A_sg_is_right_d       := inr bop_times_not_is_right
; A_sg_left_cancel_d    := inr bop_times_not_left_cancellative
; A_sg_right_cancel_d   := inr bop_times_not_right_cancellative                               
; A_sg_left_constant_d  := inr bop_times_not_left_constant
; A_sg_right_constant_d := inr bop_times_not_right_constant                               
; A_sg_anti_left_d      := inr bop_times_not_anti_left
; A_sg_anti_right_d     := inr bop_times_not_anti_right
|}. 
  

Definition sg_C_proofs_times : sg_C_proofs nat brel_eq_nat bop_times := 
{| 
  A_sg_C_associative      := bop_times_associative
; A_sg_C_congruence       := bop_times_congruence
; A_sg_C_commutative      := bop_times_commutative
; A_sg_C_selective_d      := inr _ bop_times_not_selective
; A_sg_C_idempotent_d     := inr _ bop_times_not_idempotent 
; A_sg_C_cancel_d         := inr _ bop_times_not_left_cancellative
; A_sg_C_constant_d       := inr _ bop_times_not_left_constant
; A_sg_C_anti_left_d      := inr _ bop_times_not_anti_left
; A_sg_C_anti_right_d     := inr _ bop_times_not_anti_right
|}. 


Definition A_sg_times : A_sg_C nat 
:= {| 
     A_sg_C_eqv          := A_eqv_nat 
   ; A_sg_C_bop          := bop_times
   ; A_sg_C_exists_id_d  := inl bop_times_exists_id
   ; A_sg_C_exists_ann_d := inl bop_times_exists_ann
   ; A_sg_C_proofs       := sg_C_proofs_times
   ; A_sg_C_ast          := Ast_sg_times
   |}. 

End ACAS.

Section AMCAS.

Definition A_sg_times_below_sg_C := A_classify_sg_C A_sg_times.     

Definition A_mcas_sg_times : @A_sg_mcas nat :=
  A_MCAS_sg (A_Below_sg_sg_C (A_sg_times_below_sg_C)). 


End AMCAS.  


Section CAS.

Open Scope nat.


Definition sg_certs_times : @sg_certificates nat := 
{| 
  sg_associative      := Assert_Associative 
; sg_congruence       := Assert_Bop_Congruence 
; sg_commutative_d    := Certify_Commutative 
; sg_selective_d      := Certify_Not_Selective (2, 2)
; sg_idempotent_d     := Certify_Not_Idempotent 2
; sg_is_left_d        := Certify_Not_Is_Left (1, 0)
; sg_is_right_d       := Certify_Not_Is_Right (0, 1) 
; sg_left_cancel_d    := Certify_Not_Left_Cancellative (0, (0, 1))
; sg_right_cancel_d   := Certify_Not_Right_Cancellative (0, (0, 1))
; sg_left_constant_d  := Certify_Not_Left_Constant  (1, (0, 1))
; sg_right_constant_d := Certify_Not_Right_Constant (1, (0, 1))
; sg_anti_left_d      := Certify_Not_Anti_Left (0, 0)
; sg_anti_right_d     := Certify_Not_Anti_Right (0, 0)
|}. 
  

Definition sg_C_certs_times := 
{|
     sg_C_associative    := Assert_Associative 
   ; sg_C_congruence     := Assert_Bop_Congruence 
   ; sg_C_commutative    := Assert_Commutative 
   ; sg_C_selective_d    := Certify_Not_Selective (2, 2)
   ; sg_C_idempotent_d   := Certify_Not_Idempotent 2
   ; sg_C_cancel_d       := Certify_Not_Left_Cancellative (0, (0, 1))
   ; sg_C_constant_d     := Certify_Not_Left_Constant  (1, (0, 1))
   ; sg_C_anti_left_d    := Certify_Not_Anti_Left (0, 0)
   ; sg_C_anti_right_d   := Certify_Not_Anti_Right (0, 0)
  |}.

Definition sg_times : @sg_C nat 
:= {| 
     sg_C_eqv          := eqv_eq_nat 
   ; sg_C_bop          := bop_times
   ; sg_C_exists_id_d  := Certify_Exists_Id 1 
   ; sg_C_exists_ann_d := Certify_Exists_Ann 0
   ; sg_C_certs        := sg_C_certs_times
   ; sg_C_ast          := Ast_sg_times
   |}. 


End CAS.

Section MCAS.

  Definition sg_times_below_sg_C := classify_sg_C sg_times.     

  Definition mcas_sg_times : @sg_mcas nat :=
    MCAS_sg (Below_sg_sg_C (sg_times_below_sg_C)). 


End MCAS.  


Section Verify.

Lemma correct_sg_certs_times :
  sg_certs_times = P2C_sg _ _ sg_proofs_times. 
Proof. compute. reflexivity. Qed.         

Lemma correct_sg_C_certs_times :
  sg_C_certs_times = P2C_sg_C _ _ sg_C_proofs_times. 
Proof. compute. reflexivity. Qed.         
  
Theorem correct_sg_C_times :
  sg_times = A2C_sg_C (A_sg_times). 
Proof. compute. reflexivity. Qed.


Theorem correct_mcas_times :
  mcas_sg_times
  =
  A2C_sg_mcas A_mcas_sg_times. 
Proof. compute. reflexivity. Qed.

End Verify.   
  
