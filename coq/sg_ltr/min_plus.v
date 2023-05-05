From Coq Require Import Lia String PeanoNat Nat. 
From CAS Require Import 
coq.common.compute
coq.common.ast
coq.eqv.structures
coq.eqv.nat
coq.sg.min
coq.sg.cast_up
coq.bs.min_plus
coq.ltr.properties
coq.ltr.structures
coq.ltr.no_left_zero_plus
coq.sg_ltr.properties
coq.sg_ltr.structures
coq.sg_ltr.classify
.

Open Scope string_scope.
Open Scope nat_scope. 


Section Theory.

Lemma sg_ltr_min_plus_distributive :
  A_sg_ltr_distributive brel_eq_nat bop_min ltr_no_left_zero_plus_op. 
Proof. intros s t u. unfold ltr_no_left_zero_plus_op.
       case_eq(brel_eq_nat 0 s); intro A.
       - apply A_bs_min_plus_left_distributive. 
       - apply A_bs_min_plus_left_distributive. 
Qed.        

(* absorption *) 

Lemma sg_ltr_min_plus_absorptive : 
       A_sg_ltr_absorptive brel_eq_nat bop_min ltr_no_left_zero_plus_op. 
Proof. intros s t. unfold ltr_no_left_zero_plus_op.
       case_eq(brel_eq_nat 0 s); intro A.       
       - apply A_bs_min_plus_right_absorptive.
       - apply A_bs_min_plus_right_absorptive.         
Qed. 

Lemma  sg_ltr_min_plus_strictly_absorptive_auxiliary (s t : nat) :
  brel_eq_nat 0 s = false -> 
  brel_eq_nat (bop_plus s t) (bop_min t (bop_plus s t)) = false. 
Proof. intro A.
       unfold brel_eq_nat, bop_plus, bop_min. 
       apply PeanoNat.Nat.eqb_neq.
       rewrite Min.min_comm.
       rewrite min_add. unfold brel_eq_nat in A.
       apply PeanoNat.Nat.eqb_neq in A. 
       lia.
Qed. 

Lemma sg_ltr_min_plus_strictly_absorptive : 
       A_sg_ltr_strictly_absorptive brel_eq_nat bop_min ltr_no_left_zero_plus_op. 
Proof. intros s t. split.
       - apply sg_ltr_min_plus_absorptive.
       - unfold ltr_no_left_zero_plus_op.
         case_eq(brel_eq_nat 0 s); intro A;
           apply sg_ltr_min_plus_strictly_absorptive_auxiliary; auto. 
Qed.




End Theory.

Section ACAS.
  
  Definition A_sg_ltr_min_plus_properties :
    A_sg_ltr_properties brel_eq_nat bop_min ltr_no_left_zero_plus_op
    := 
    {|
      A_sg_ltr_distributive_d        := inl sg_ltr_min_plus_distributive
    ; A_sg_ltr_absorptive_d          := inl sg_ltr_min_plus_absorptive 
    ; A_sg_ltr_strictly_absorptive_d := inl sg_ltr_min_plus_strictly_absorptive 
    |}.

  Definition A_sg_ltr_min_plus : @A_sg_ltr nat nat :=
    let w := brel_eq_nat_witness in
    let f := brel_eq_nat_new in
    let nt := brel_eq_nat_not_trivial in
    let eqvPS := eqv_proofs_eq_nat in 
    {|
      A_sg_ltr_carrier        := A_eqv_nat
    ; A_sg_ltr_label          := A_eqv_nat
    ; A_sg_ltr_plus           := bop_min 
    ; A_sg_ltr_ltr            := ltr_no_left_zero_plus_op
    ; A_sg_ltr_plus_props     := A_sg_C_proofs_from_sg_CS_proofs _ _ _ w f nt eqvPS sg_CS_proofs_min 
    ; A_sg_ltr_ltr_props      := A_ltr_no_left_zero_plus_properties
    ; A_sg_ltr_id_ann_props_d :=
        A_SG_LTR_Id_Ann_None _ _ _ 
          (bop_min_not_exists_id, ltr_no_left_zero_plus_not_exists_ann)
    ; A_sg_ltr_props          := A_sg_ltr_min_plus_properties
    ; A_sg_ltr_ast            := Cas_ast ("sg_ltr_min_plus_one", nil) (* FIX ME *) 
    |}.


         
End ACAS.

Section AMCAS.
  
  Definition A_mcas_sg_ltr_min_plus :=
     A_MCAS_sg_ltr (A_classify_sg_ltr (A_sg_ltr_min_plus)).     

End AMCAS.

Section CAS. 
  Definition sg_ltr_min_plus_properties :
    @sg_ltr_properties nat nat 
    :=
    let w := brel_eq_nat_witness in    
    {|
      sg_ltr_distributive_d        := inl (SG_LTR_Distributive (w, w))
    ; sg_ltr_absorptive_d          := inl (SG_LTR_Absorptive (w, w))
    ; sg_ltr_strictly_absorptive_d := inl (SG_LTR_Strictly_Absorptive (w, w))
    |}.

  Definition sg_ltr_min_plus : @sg_ltr nat nat :=
    let w := brel_eq_nat_witness in
    let f := brel_eq_nat_new in    
    {|
      sg_ltr_carrier        := eqv_eq_nat
    ; sg_ltr_label          := eqv_eq_nat
    ; sg_ltr_plus           := bop_min 
    ; sg_ltr_ltr            := ltr_no_left_zero_plus_op
    ; sg_ltr_plus_props     := sg_C_certs_from_sg_CS_certs _ brel_eq_nat bop_min w f sg_CS_certs_min 
    ; sg_ltr_ltr_props      := ltr_no_left_zero_plus_properties
    ; sg_ltr_id_ann_props_d := SG_LTR_Id_Ann_None 
    ; sg_ltr_props          := sg_ltr_min_plus_properties
    ; sg_ltr_ast            := Cas_ast ("sg_ltr_min_plus_one", nil) (* FIX ME *) 
    |}.


End CAS.

Section MCAS.

  Definition mcas_sg_ltr_min_plus :=
     MCAS_sg_ltr (classify_sg_ltr (sg_ltr_min_plus)).     


End MCAS.

Section Verify.

  Theorem correct_sg_ltr_min_plus_properties :
    P2C_sg_ltr_properties brel_eq_nat bop_min ltr_no_left_zero_plus_op
      A_sg_ltr_min_plus_properties brel_eq_nat_witness brel_eq_nat_witness 
    = 
    sg_ltr_min_plus_properties. 
  Proof. reflexivity. Qed.

  Theorem correct_sg_ltr_min_plus :
    A2C_sg_ltr A_sg_ltr_min_plus 
    = 
    sg_ltr_min_plus. 
  Proof. reflexivity. Qed.
  
  Theorem correct_mcas_slt_min_plus_one :
    A2C_mcas_sg_ltr A_mcas_sg_ltr_min_plus
    = 
    mcas_sg_ltr_min_plus.  
  Proof. reflexivity. Qed.

End Verify.

Close Scope string_scope.
Close Scope nat_scope. 



