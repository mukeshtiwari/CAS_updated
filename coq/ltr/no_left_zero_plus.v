Require Import Coq.Arith.Arith.     (* beq_nat *)

Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.
Require Import CAS.coq.theory.arithmetic. 

Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.eqv.nat. 

Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures.
Require Import CAS.coq.sg.plus. 

Require Import CAS.coq.ltr.properties.
Require Import CAS.coq.ltr.structures.
Require Import CAS.coq.ltr.classify. 
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Open Scope string_scope.
Open Scope nat_scope.

Section Compute.  

Definition ltr_no_left_zero_plus_op : ltr_type nat nat
    := λ m,  bop_plus (if brel_eq_nat 0 m then 1 else m). 

End Compute.  

Section Theory.  

Open Scope nat.   

Lemma ltr_no_left_zero_plus_congruence:
  A_ltr_congruence brel_eq_nat brel_eq_nat ltr_no_left_zero_plus_op. 
Proof. intros l1 l2 s1 s2 H1 H2. unfold ltr_no_left_zero_plus_op.
       apply bop_plus_congruence; auto. 
       + case_eq(brel_eq_nat 0 l1); intro A;
           case_eq(brel_eq_nat 0 l2); intro B; auto.
         * rewrite (brel_eq_nat_transitive _ _ _ A H1) in B. 
           discriminate B. 
         * apply brel_eq_nat_symmetric in H1.
           rewrite (brel_eq_nat_transitive _ _ _ B H1) in A. 
           discriminate A. 
Qed.

Lemma ltr_no_left_zero_plus_cancellative:
  A_ltr_cancellative brel_eq_nat ltr_no_left_zero_plus_op. 
Proof. intros l s1 s2 H. unfold ltr_no_left_zero_plus_op. 
       assert (A := bop_plus_left_cancellative _ _ _ H).
       exact A.
Qed.

Lemma ltr_no_left_zero_plus_not_is_right :
  A_ltr_not_is_right brel_eq_nat ltr_no_left_zero_plus_op. 
Proof. exists (0, 0). compute. reflexivity. Defined.

Lemma ltr_no_left_zero_plus_not_exists_id :
  A_ltr_not_exists_id brel_eq_nat ltr_no_left_zero_plus_op. 
Proof. intro l. exists 0. unfold ltr_no_left_zero_plus_op.
       case_eq(brel_eq_nat 0 l); intro A; simpl; auto. 
       assert (B := bop_plus_commutative l 0).
       assert (C : brel_eq_nat (bop_plus 0 l) l = true).
       {
         simpl. apply brel_eq_nat_reflexive. 
       } 
       assert (D := brel_eq_nat_transitive _ _ _ B C).
       case_eq(brel_eq_nat (bop_plus l 0) 0); intro E; auto.
       apply brel_eq_nat_symmetric in E. 
       rewrite (brel_eq_nat_transitive _ _ _ E D) in A.
       discriminate A.
Defined. 

Lemma ltr_no_left_zero_plus_not_exists_ann :
  A_ltr_not_exists_ann brel_eq_nat ltr_no_left_zero_plus_op. 
Proof. intro s.  exists 0. unfold ltr_no_left_zero_plus_op.
       rewrite brel_eq_nat_reflexive. 
       unfold bop_plus. unfold Init.Nat.add. 
       rewrite brel_eq_nat_Su_u.
       reflexivity. 
Defined. 

(*
Lemma ltr_no_left_zero_plus_not_left_constant : 
A_ltr_not_left_constant brel_eq_nat ltr_no_left_zero_plus_op. 
Proof. exists (0, (0, S 0)). compute. 
       reflexivity. 
Defined. 
*) 

End Theory.

Section ACAS.

Definition A_ltr_no_left_zero_plus_properties :
    A_ltr_properties brel_eq_nat brel_eq_nat ltr_no_left_zero_plus_op := 
{|
  A_ltr_props_congruence     := ltr_no_left_zero_plus_congruence 
; A_ltr_props_is_right_d     := inr ltr_no_left_zero_plus_not_is_right
; A_ltr_props_cancellative_d := inl ltr_no_left_zero_plus_cancellative
|}.


Definition A_ltr_no_left_zero_plus  : @A_ltr nat nat :=
{|
  A_ltr_carrier := A_eqv_nat 
; A_ltr_label   := A_eqv_nat 
; A_ltr_ltr     := ltr_no_left_zero_plus_op 
; A_ltr_exists_id_d    := inr ltr_no_left_zero_plus_not_exists_id
; A_ltr_exists_ann_d   := inr ltr_no_left_zero_plus_not_exists_ann 
; A_ltr_props   := A_ltr_no_left_zero_plus_properties
; A_ltr_ast     := Cas_ast ("ltr_no_left_zero_plus", []) 
|}.

  
End ACAS. 

Section AMCAS.

  Definition A_mcas_ltr_no_left_zero_plus :=
     A_MCAS_ltr (A_classify_ltr (A_ltr_no_left_zero_plus)).     

End AMCAS.   

Section CAS.

Definition ltr_no_left_zero_plus_properties :
    @ltr_properties nat nat := 
{|
  ltr_props_is_right_d     := inr (LTR_not_is_right (0, 0)) 
; ltr_props_cancellative_d := inl (LTR_cancellative (0, 0))
|}.


Definition ltr_no_left_zero_plus  : @ltr nat nat :=
{|
  ltr_carrier := eqv_eq_nat 
; ltr_label   := eqv_eq_nat 
; ltr_ltr     := ltr_no_left_zero_plus_op
; ltr_exists_id_d    := inr (LTR_not_exists_id 0) 
; ltr_exists_ann_d   := inr (LTR_not_exists_ann 0) 
; ltr_props   := ltr_no_left_zero_plus_properties
; ltr_ast     := Cas_ast ("ltr_no_left_zero_plus", []) 
|}.
  
  
End CAS.

Section MCAS.

  Definition mcas_ltr_no_left_zero_plus :=
     MCAS_ltr (classify_ltr (ltr_no_left_zero_plus)).     


End MCAS.   


Section Verify.


Theorem correct_ltr_no_left_zero_plus_properties :
  ltr_no_left_zero_plus_properties
  =
  P2C_ltr_properties _ _ _ A_ltr_no_left_zero_plus_properties 0 0. 
Proof. reflexivity. Qed. 

Theorem correct_ltr_no_left_zero_plus :
  ltr_no_left_zero_plus
  =
  A2C_ltr A_ltr_no_left_zero_plus.
Proof. unfold ltr_no_left_zero_plus, A_ltr_no_left_zero_plus, A2C_ltr; simpl. 
       rewrite <- correct_ltr_no_left_zero_plus_properties.
       unfold p2c_ltr_not_exists_id, p2c_ltr_not_exists_ann.
       reflexivity. Qed. 


Theorem correct_mcas_ltr_no_left_zero_plus : 
  mcas_ltr_no_left_zero_plus
  =
  A2C_mcas_ltr A_mcas_ltr_no_left_zero_plus.
Proof. reflexivity. Qed.


End Verify.   


Close Scope string_scope.
Close Scope nat_scope.
