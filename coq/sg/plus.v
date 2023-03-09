Require Import Coq.Arith.Arith.     (* beq_nat *)

Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.
Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures.
Require Import CAS.coq.sg.classify. 

Require Import CAS.coq.eqv.nat. 

Section Theory.

Open Scope nat.   

Lemma beq_nat_plus_congruence : 
   ∀ s1 s2 t1 t2 : nat,
   beq_nat s1 t1 = true
   → beq_nat s2 t2 = true → beq_nat (plus s1 s2) (plus t1 t2) = true.
Proof. 
   intros s1 s2 t1 t2 H1 H2. 
   assert (C1 := beq_nat_to_prop s1 t1 H1). 
   assert (C2 := beq_nat_to_prop s2 t2 H2). 
   rewrite C1. rewrite C2.  apply brel_eq_nat_reflexive. 
Defined. 

Lemma bop_plus_congruence : bop_congruence nat brel_eq_nat bop_plus.
Proof. unfold bop_congruence. unfold brel_eq_nat, bop_plus.
       exact beq_nat_plus_congruence. 
Defined. 

Lemma bop_plus_associative : bop_associative nat brel_eq_nat bop_plus.
Proof. unfold bop_associative. intros. unfold brel_eq_nat, bop_plus. 
       rewrite (Plus.plus_assoc s t u). apply brel_eq_nat_reflexive.        
Defined. 

Lemma bop_plus_not_idempotent : bop_not_idempotent nat brel_eq_nat bop_plus.
Proof. unfold bop_not_idempotent. exists 1. simpl. reflexivity. Defined. 

Lemma bop_plus_commutative : bop_commutative nat brel_eq_nat bop_plus.
Proof. unfold bop_commutative, bop_plus. intros s t. 
       rewrite Plus.plus_comm at 1. apply brel_eq_nat_reflexive. 
Defined. 

Lemma bop_plus_not_selective : bop_not_selective nat brel_eq_nat bop_plus.
Proof. unfold bop_not_selective. exists (1, 1); simpl. split; reflexivity. 
Defined. 


Lemma bop_plus_not_is_left : bop_not_is_left nat brel_eq_nat bop_plus.
Proof. unfold bop_not_is_left. exists (0, 1); simpl. reflexivity. Defined. 

Lemma bop_plus_not_is_right : bop_not_is_right nat brel_eq_nat bop_plus.
Proof. unfold bop_not_is_left. exists (1, 0); simpl. reflexivity. Defined. 


Lemma bop_plus_zero_is_id : bop_is_id nat brel_eq_nat bop_plus 0.
Proof. intro s. unfold bop_plus. split. 
       unfold plus. apply brel_eq_nat_reflexive. 
       rewrite plus_comm. unfold plus. apply brel_eq_nat_reflexive. 
Qed. 

Lemma bop_plus_exists_id : bop_exists_id nat brel_eq_nat bop_plus.
Proof. exists 0. apply bop_plus_zero_is_id. Defined. 

Lemma bop_plus_S_left : ∀ s t : nat, bop_plus (S s) t = S (bop_plus s t). 
Proof. unfold bop_plus. induction s; induction t; compute; reflexivity. Defined. 

Lemma bop_plus_S_right : ∀ s t : nat, bop_plus s (S t) = S (bop_plus s t). 
Proof. intros s t. 
       assert(plus_comm_l := bop_plus_commutative s (S t)). apply beq_nat_to_prop in plus_comm_l. 
       assert(plus_comm_r := bop_plus_commutative s t). apply beq_nat_to_prop in plus_comm_r. 
       rewrite plus_comm_l, plus_comm_r.  
       apply bop_plus_S_left. 
Defined.


Lemma bop_plus_not_exists_ann : bop_not_exists_ann nat brel_eq_nat bop_plus.
Proof. unfold bop_not_exists_ann. induction a. 
       exists 1. left. compute. reflexivity. 
       destruct IHa as [s [H | H]]. 
          exists s. left.  rewrite bop_plus_S_left. rewrite brel_nat_eq_S. assumption. 
          exists s. right. rewrite bop_plus_S_right. rewrite brel_nat_eq_S. assumption. 
Defined. 


(* 
plus_Snm_nSm: ∀ n m : nat, S n + m = n + S m
plus_Sn_m: ∀ n m : nat, S n + m = S (n + m)
*) 
Lemma  bop_plus_left_cancellative : bop_left_cancellative nat brel_eq_nat bop_plus.
Proof. unfold bop_plus. unfold bop_left_cancellative. 
       induction s; intros t u.
       simpl. auto. 
       intro H. rewrite plus_Sn_m in H. rewrite plus_Sn_m in H. 
       rewrite brel_nat_eq_S in H. apply IHs; auto.  
Defined. 



Lemma  bop_plus_right_cancellative : bop_right_cancellative nat brel_eq_nat bop_plus.
Proof. unfold bop_plus, bop_right_cancellative. intros s t u H.
       rewrite plus_comm in H. (* does not work: rewrite plus_comm at 2. *) 
       apply brel_eq_nat_symmetric in H. 
       rewrite plus_comm in H. 
       apply brel_eq_nat_symmetric. 
       apply (bop_plus_left_cancellative _ _ _ H). 
Qed.        

Lemma bop_plus_not_left_constant : bop_not_left_constant nat brel_eq_nat bop_plus.
Proof. exists (0, (0, 1)); simpl. auto. Defined. 

Lemma bop_plus_not_right_constant : bop_not_right_constant nat brel_eq_nat bop_plus.
Proof. exists (0, (0, 1)); simpl. auto. Defined. 

Lemma bop_plus_not_anti_left : bop_not_anti_left nat brel_eq_nat bop_plus.
Proof. exists (0, 0); simpl. auto. Defined. 


Lemma bop_plus_not_anti_right : bop_not_anti_right nat brel_eq_nat bop_plus.
Proof. exists (0, 0); simpl. auto. Defined. 

End Theory.

Section ACAS.

Definition A_sg_proofs_plus : sg_proofs nat brel_eq_nat bop_plus := 
{| 
  A_sg_associative        := bop_plus_associative
; A_sg_congruence         := bop_plus_congruence
; A_sg_commutative_d      := inl bop_plus_commutative
; A_sg_selective_d        := inr bop_plus_not_selective
; A_sg_idempotent_d       := inr bop_plus_not_idempotent
; A_sg_is_left_d          := inr bop_plus_not_is_left
; A_sg_is_right_d         := inr bop_plus_not_is_right
; A_sg_left_cancel_d      := inl bop_plus_left_cancellative
; A_sg_right_cancel_d     := inl bop_plus_right_cancellative

; A_sg_left_constant_d    := inr bop_plus_not_left_constant
; A_sg_right_constant_d   := inr bop_plus_not_right_constant

; A_sg_anti_left_d        := inr bop_plus_not_anti_left
; A_sg_anti_right_d       := inr bop_plus_not_anti_right
|}. 


Definition A_sg_C_proofs_plus : sg_C_proofs nat brel_eq_nat bop_plus := 
{| 
  A_sg_C_associative      := bop_plus_associative
; A_sg_C_congruence       := bop_plus_congruence
; A_sg_C_commutative      := bop_plus_commutative
; A_sg_C_selective_d        := inr bop_plus_not_selective
; A_sg_C_idempotent_d       := inr bop_plus_not_idempotent
; A_sg_C_cancel_d           := inl bop_plus_left_cancellative
; A_sg_C_constant_d         := inr bop_plus_not_left_constant
; A_sg_C_anti_left_d        := inr bop_plus_not_anti_left
; A_sg_C_anti_right_d       := inr bop_plus_not_anti_right
|}. 


Definition A_sg_plus : A_sg_C nat 
:= {| 
       A_sg_C_eqv          := A_eqv_nat 
     ; A_sg_C_bop          := bop_plus
     ; A_sg_C_exists_id_d  := inl bop_plus_exists_id
     ; A_sg_C_exists_ann_d := inr bop_plus_not_exists_ann
     ; A_sg_C_proofs       := A_sg_C_proofs_plus
     ; A_sg_C_ast          := Ast_sg_plus 
   |}. 


End ACAS.

Section AMCAS.

Definition A_sg_plus_below_sg_C := A_classify_sg_C A_sg_plus.   

Definition A_mcas_sg_plus : @A_sg_mcas nat :=
  A_MCAS_sg (A_Below_sg_sg_C (A_sg_plus_below_sg_C)). 

End AMCAS.  

Section CAS.

Open Scope nat.

Definition sg_certs_plus : @sg_certificates nat := 
{| 
  sg_associative        := Assert_Associative 
; sg_congruence         := Assert_Bop_Congruence 
; sg_commutative_d      := Certify_Commutative
; sg_selective_d        := Certify_Not_Selective (1, 1)
; sg_idempotent_d       := Certify_Not_Idempotent 1
; sg_is_left_d          := Certify_Not_Is_Left (0, 1)
; sg_is_right_d         := Certify_Not_Is_Right (1, 0)
; sg_left_cancel_d      := Certify_Left_Cancellative
; sg_right_cancel_d     := Certify_Right_Cancellative
; sg_left_constant_d    := Certify_Not_Left_Constant (0, (0, 1))
; sg_right_constant_d   := Certify_Not_Right_Constant (0, (0, 1))
; sg_anti_left_d        := Certify_Not_Anti_Left (0, 0) 
; sg_anti_right_d       := Certify_Not_Anti_Right (0, 0) 
|}. 

Definition sg_C_certs_plus : @sg_C_certificates nat := 
{| 
  sg_C_associative      := Assert_Associative 
; sg_C_congruence       := Assert_Bop_Congruence 
; sg_C_commutative      := Assert_Commutative
; sg_C_selective_d      := Certify_Not_Selective (1, 1)
; sg_C_idempotent_d     := Certify_Not_Idempotent 1
; sg_C_cancel_d         := Certify_Left_Cancellative
; sg_C_constant_d       := Certify_Not_Left_Constant (0, (0, 1))
; sg_C_anti_left_d      := Certify_Not_Anti_Left (0, 0) 
; sg_C_anti_right_d     := Certify_Not_Anti_Right (0, 0) 
|}. 


Definition sg_plus : @sg_C nat
:= {| 
     sg_C_eqv          := eqv_eq_nat 
   ; sg_C_bop          := bop_plus
   ; sg_C_exists_id_d  := Certify_Exists_Id 0 
   ; sg_C_exists_ann_d := Certify_Not_Exists_Ann
   ; sg_C_certs        := sg_C_certs_plus   
   ; sg_C_ast          := Ast_sg_plus 
   |}. 

End CAS.

Section MCAS.

Definition sg_plus_below_sg_C := classify_sg_C sg_plus.   

Definition mcas_sg_plus : @sg_mcas nat :=
  MCAS_sg (Below_sg_sg_C (sg_plus_below_sg_C)). 


End MCAS.  

Section Verify.

  Theorem correct_sg_certs_plus :
    sg_certs_plus
    =
    P2C_sg brel_eq_nat bop_plus (A_sg_proofs_plus). 
  Proof. compute. reflexivity. Qed. 

  Theorem correct_sg_C_certs_plus :
    sg_C_certs_plus
    =
    P2C_sg_C brel_eq_nat bop_plus (A_sg_C_proofs_plus). 
  Proof. compute. reflexivity. Qed. 

  
  Theorem correct_mcas_plus :
    mcas_sg_plus
    =
    A2C_sg_mcas  A_mcas_sg_plus. 
  Proof. compute. reflexivity. Qed.


End Verify.   


