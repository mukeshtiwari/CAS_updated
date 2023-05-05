Require Import Coq.Arith.Arith.

Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.
Require Import CAS.coq.common.data.
Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.eqv.theory.

Section Theory.

Lemma brel_nat_eq_S : ∀ s t : nat, brel_eq_nat (S s) (S t) = brel_eq_nat s t. 
Proof. unfold brel_eq_nat. induction s; induction t; compute; reflexivity. Qed. 

Lemma brel_nat_neq_S : ∀ s : nat, brel_eq_nat s (S s) = false. 
Proof. unfold brel_eq_nat. induction s. 
          compute; reflexivity. 
          rewrite brel_nat_eq_S. assumption. 
Qed. 

Lemma brel_eq_nat_reflexive : brel_reflexive nat brel_eq_nat. 
Proof. unfold brel_reflexive, brel_eq_nat. induction s; auto. Qed. 

Lemma brel_eq_nat_symmetric : brel_symmetric nat brel_eq_nat. 
Proof. unfold brel_symmetric, brel_eq_nat. 
       induction s; induction t; simpl; intros; auto. Qed. 

Lemma brel_eq_nat_transitive : brel_transitive nat brel_eq_nat. 
Proof. unfold brel_transitive, brel_eq_nat. 
       induction s; induction t; induction u; simpl; intros; auto.        
          discriminate. apply (IHs t u H H0).
Qed. 

Lemma brel_eq_nat_congruence : brel_congruence nat brel_eq_nat brel_eq_nat. 
Proof. unfold brel_congruence. 
       induction s; induction t; induction u; induction v; simpl; intros H Q; auto; discriminate.  
Qed. 


Lemma brel_eq_nat_not_trivial : brel_not_trivial nat brel_eq_nat S.
Proof. intro s. split. 
          apply brel_nat_neq_S. 
          apply brel_symmetric_implies_dual. 
          apply brel_eq_nat_symmetric. 
          apply brel_nat_neq_S. 
Defined.

Lemma brel_eq_nat_not_finite : carrier_is_not_finite nat brel_eq_nat.
Proof. unfold carrier_is_not_finite. intro f.
       admit.        
Admitted. 



Open Scope nat. 
Lemma brel_eq_nat_at_least_three : brel_at_least_three nat brel_eq_nat.
Proof. exists (0, (1, 2)).  compute; split; auto. Defined. 

Lemma brel_nat_not_exactly_two :   brel_not_exactly_two nat brel_eq_nat.
Proof. apply brel_at_least_thee_implies_not_exactly_two.
       apply brel_eq_nat_symmetric; auto. 
       apply brel_eq_nat_transitive; auto.
       apply brel_eq_nat_at_least_three; auto. 
Defined.


(* general lemmas *) 

Lemma beq_nat_to_prop  : ∀ s t: nat, beq_nat s t = true -> s = t. 
Proof.  induction s;  induction t; simpl; intro H; auto; discriminate. Qed. 

Lemma injection_S_brel_eq_nat : ∀ s t : nat, brel_eq_nat s t = true -> brel_eq_nat (S s) (S t) = true. 
Proof. intros s t H. apply beq_nat_to_prop in H.  rewrite H. 
       apply brel_eq_nat_reflexive. 
Qed. 

End Theory.

Section ACAS.

Open Scope nat. 


Definition eqv_proofs_eq_nat : eqv_proofs nat brel_eq_nat (* (uop_id nat) *) 
:= {| 
     A_eqv_congruence  := brel_eq_nat_congruence 
   ; A_eqv_reflexive   := brel_eq_nat_reflexive 
   ; A_eqv_transitive  := brel_eq_nat_transitive 
   ; A_eqv_symmetric   := brel_eq_nat_symmetric

   |}. 


Definition brel_eq_nat_witness := 0.
Definition brel_eq_nat_new := S. 
Definition A_eqv_nat : A_eqv nat
:= {| 
      A_eqv_eq     := brel_eq_nat 
    ; A_eqv_proofs := eqv_proofs_eq_nat
    ; A_eqv_witness     := brel_eq_nat_witness
    ; A_eqv_new         := brel_eq_nat_new 
    ; A_eqv_not_trivial := brel_eq_nat_not_trivial
    ; A_eqv_exactly_two_d   := inr (brel_nat_not_exactly_two)                              
    ; A_eqv_data   := λ n, DATA_nat n 
    ; A_eqv_rep    := λ b, b
    ; A_eqv_finite_d := inr brel_eq_nat_not_finite 
    ; A_eqv_ast    := Ast_eqv_nat
   |}. 


End ACAS.

Section CAS.
Open Scope nat. 

Definition eqv_eq_nat : eqv (S := nat)
:= {| 
      eqv_eq    := brel_eq_nat
    ; eqv_certs := 
     {|
       eqv_congruence     := @Assert_Brel_Congruence nat
     ; eqv_reflexive      := @Assert_Reflexive nat 
     ; eqv_transitive     := @Assert_Transitive nat 
     ; eqv_symmetric      := @Assert_Symmetric nat

     |}  
    ; eqv_witness := 0
    ; eqv_new := S
    ; eqv_exactly_two_d := Certify_Not_Exactly_Two (not_ex2 brel_eq_nat 0 1 2)
    ; eqv_data  := λ n, DATA_nat n 
    ; eqv_rep   := λ b, b
    ; eqv_finite_d := Certify_Is_Not_Finite 
    ; eqv_ast   := Ast_eqv_nat
   |}. 


End CAS.

Section MCAS.

Definition mcas_eqv_eq_nat := EQV_eqv eqv_eq_nat.   

End MCAS.   


Section Verify.

Theorem correct_eqv_nat : eqv_eq_nat = A2C_eqv nat (A_eqv_nat). 
Proof. unfold eqv_eq_nat, A_eqv_nat, A2C_eqv; simpl.
       unfold brel_nat_not_exactly_two. unfold brel_at_least_thee_implies_not_exactly_two. 
       reflexivity.
Qed. 
  
End Verify.   
  
