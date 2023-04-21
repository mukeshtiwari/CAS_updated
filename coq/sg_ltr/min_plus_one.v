Require Import Coq.Strings.String.
Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.

Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.eqv.nat.

Require Import CAS.coq.bs.min_plus.

Require Import CAS.coq.ltr.properties.
Require Import CAS.coq.ltr.structures.
Require Import CAS.coq.ltr.
Require Import CAS.coq.sg_ltr.properties.
Require Import CAS.coq.sg_ltr.structures.
Require Import CAS.coq.sg.cast_up
  CAS.coq.sg.min.
From Coq Require Import Lia String.
Section Theory.

Open Scope nat.


(* (a + 1) + (b min c) = ((a + 1)  + b) min ((a + 1) + c) *) 
Lemma slt_min_plus_one_distributive :
  slt_distributive brel_eq_nat bop_min ltr_plus_one. 
Proof. unfold slt_distributive. intros s t u.
       apply bop_min_plus_left_distributive. 
Qed.        

(* absorption *) 

Lemma min_plus_one_slt_absorptive : 
       slt_absorptive brel_eq_nat bop_min ltr_plus_one. 
Proof. unfold slt_absorptive. intros s t. unfold ltr_plus_one. 
       apply bops_min_plus_left_right_absorptive.
Qed. 

Lemma ltr_plus_one_increasing (s t : nat) : bop_min t (ltr_plus_one s t) = t.
Proof.  unfold bop_min. unfold ltr_plus_one. unfold bop_plus. 
       rewrite Min.min_comm.
       eapply min_add.
Qed. 

Lemma ltr_plus_one_strictly_increasing (s t : nat) : brel_eq_nat (ltr_plus_one s t) t = false. 
Proof.
  unfold brel_eq_nat, ltr_plus_one,
    bop_plus.
  eapply PeanoNat.Nat.eqb_neq.
  lia.
Qed.


Lemma min_plus_one_slt_strictly_absorptive : 
       slt_strictly_absorptive brel_eq_nat bop_min ltr_plus_one. 
Proof. unfold slt_strictly_absorptive. intros s t. split. 
       + apply min_plus_one_slt_absorptive. 
       + rewrite ltr_plus_one_increasing.
         rewrite ltr_plus_one_strictly_increasing; auto. 
Qed. 
End Theory.

Section ACAS.
  
Open Scope string_scope. 
  Definition A_slt_min_plus_one : @A_selective_left_pre_dioid nat nat :=
    {|
      A_selective_left_pre_dioid_carrier := A_eqv_nat;
      A_selective_left_pre_dioid_label := A_eqv_nat;
      A_selective_left_pre_dioid_plus := bop_min;
      A_selective_left_pre_dioid_trans := ltr_plus_one;
      A_selective_left_pre_dioid_plus_proofs := sg_CS_proofs_min;
      A_selective_left_pre_dioid_trans_proofs := ltr_plus_one_proofs;
      A_selective_left_pre_dioid_exists_plus_ann :=
      existT
          (λ a : nat,
            properties.bop_is_ann nat (A_eqv_eq nat A_eqv_nat) bop_min a) 0%nat
          bop_min_zero_is_ann;
      A_selective_left_pre_dioid_id_ann_proofs_d :=
        SLT_Id_Ann_Proof_None (A_eqv_eq nat A_eqv_nat) bop_min ltr_plus_one
          (bop_min_not_exists_id, ltr_plus_one_not_exists_ann);
      A_selective_left_pre_dioid_proofs :=
        {|
          A_left_dioid_distributive := slt_min_plus_one_distributive;
          A_left_dioid_absorptive := min_plus_one_slt_absorptive;
          A_left_dioid_strictly_absorptive_d :=
            inl min_plus_one_slt_strictly_absorptive
        |};
      A_selective_left_pre_dioid_ast := Cas_ast ("slt_min_plus_one", nil)
    |}.


         
End ACAS.

Section AMCAS.
  
  Definition A_mcas_slt_min_plus_one := @A_SLT_Selective_Left_Pre_Dioid _ _ A_slt_min_plus_one.


End AMCAS.

Section CAS. 

Open Scope string_scope.   
  Definition slt_min_plus_one : @selective_left_pre_dioid nat nat :=
    {|
      selective_left_pre_dioid_carrier := eqv_eq_nat;
      selective_left_pre_dioid_label := eqv_eq_nat;
      selective_left_pre_dioid_plus := bop_min;
      selective_left_pre_dioid_trans := ltr_plus_one;
      selective_left_pre_dioid_plus_certs := sg_CS_certs_min;
      selective_left_pre_dioid_trans_certs := ltr_plus_one_certs;
      selective_left_pre_dioid_exists_plus_ann :=
      properties.Assert_Exists_Ann 0%nat;
      selective_left_pre_dioid_id_ann_certs_d := Certify_SLT_Id_Ann_Proof_None;
      selective_left_pre_dioid_certs :=
        {|
          left_dioid_distributive := Assert_Slt_Distributive;
          left_dioid_absorptive := Assert_Slt_Absorptive;
          left_dioid_strictly_absorptive_d := Certify_Slt_Strictly_Absorptive
        |};
      selective_left_pre_dioid_ast := Cas_ast ("slt_min_plus_one", nil)
    |}.
    
    

End CAS.

Section MCAS.

  Definition mcas_slt_min_plus_one := SLT_Selective_Left_Pre_Dioid slt_min_plus_one.

End MCAS.

Section Verify.

  Theorem correct_slt_min_plus_one : 
    slt_min_plus_one = A2C_selective_left_pre_dioid A_slt_min_plus_one.
  Proof.
    reflexivity.
  Qed.

  Theorem correct_mcas_slt_min_plus_one : 
    mcas_slt_min_plus_one = A2C_mcas_slt A_mcas_slt_min_plus_one.
  Proof.
    reflexivity.
  Qed.

End Verify.



