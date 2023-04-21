Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool. 

Require Import CAS.coq.common.compute.
Require Import CAS.coq.eqv.properties. 
Require Import CAS.coq.eqv.set. 
Require Import CAS.coq.eqv.add_constant.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.common.ast.

Require Import CAS.coq.tr.left.from_sg.
Require Import CAS.coq.bs.properties. 
Require Import CAS.coq.st.properties. 
Require Import CAS.coq.st.structures.
Require Import CAS.coq.sg.add_id.
Require Import CAS.coq.sg.add_ann. 
Require Import CAS.coq.sg.cast_up. 
Require Import CAS.coq.tr.left.add_ann.
Require Import CAS.coq.st.cast_up.

Require Import List. 
Import ListNotations.

Section Theory.

End Theory.



Section ACAS.

Section Decide.

      


End Decide.

Section Proofs. 

  Context 
    {L S : Type}
    (c : cas_constant)
    (wL : L)
    (r : brel S)
    (ltr : ltr_type L S)
    (bop : binary_op S)
    (eqv_s : @eqv_proofs S r).



  Lemma slt_add_ann_distributive_decidable :
    slt_distributive_decidable r bop ltr ->
    slt_distributive_decidable 
      (sum.brel_sum brel_constant r) 
      (bop_add_id bop c) 
      (ltr_add_ann_op ltr c).
  Proof.
    intros [Ha | Hb].
    + left.
      unfold slt_distributive in * |- *.
      intros ? [t | t] [u | u];
      simpl.
      ++ reflexivity.
      ++ destruct eqv_s; simpl in *.
         apply A_eqv_reflexive.
      ++ destruct eqv_s; simpl in *.
         apply A_eqv_reflexive.
      ++ apply Ha;
         try assumption.
    + right.
      unfold slt_not_distributive in * |- *.
      destruct Hb as ((au, (bu, cu)) & H).
      exists (au, (inr bu, inr cu)).
      exact H.
  Defined.
 


  Lemma slt_add_ann_absorptive_decidable :
    slt_absorptive_decidable r bop ltr ->
    slt_absorptive_decidable 
      (sum.brel_sum brel_constant r) 
      (bop_add_id bop c) 
      (ltr_add_ann_op ltr c).
  Proof.
    intros [Ha | Ha].
    + left.
      unfold slt_absorptive in * |- *.
      intros ? [sa | sa].
      ++ reflexivity.
      ++ apply Ha; try assumption.
    + right.
      unfold slt_not_absorptive in * |- *.
      destruct Ha as ((au, bu) & H).
      exists (au, inr bu).
      exact H.
  Defined.
    
  Lemma slt_add_ann_strictly_absorptive_decidable :
    slt_strictly_absorptive_decidable r bop ltr ->
    slt_strictly_absorptive_decidable 
      (sum.brel_sum brel_constant r)
      (bop_add_id bop c) 
      (ltr_add_ann_op ltr c).
  Proof.
    intros [Ha | Ha].
    + right.
      unfold slt_strictly_absorptive in * |-.
      unfold slt_not_strictly_absorptive.
      exists (wL, inl c);
      simpl.
      right.
      reflexivity.
    + right.
      unfold slt_not_strictly_absorptive in * |- *.
      destruct Ha as ((au, bu) & [Hu | Hu]).
      exists (au, inr bu); simpl.
      left. exact Hu.
      exists (au, inr bu); simpl.
      right. exact Hu.
  Defined.
      



  Lemma slt_add_ann_proof  :
    slt_proofs r bop ltr ->
    slt_proofs (sum.brel_sum brel_constant r) 
    (bop_add_id bop c) 
    (ltr_add_ann_op ltr c).
  Proof.
    intros [Ha Hb Hc].
    econstructor.
    + apply slt_add_ann_distributive_decidable;
      try assumption.
    + apply slt_add_ann_absorptive_decidable;
      try assumption.
    + apply slt_add_ann_strictly_absorptive_decidable; 
      try assumption.
  Defined.

  Lemma left_dioid_add_ann_proof : 
    left_dioid_proofs r bop ltr ->
    left_dioid_proofs (sum.brel_sum brel_constant r)
      (bop_add_id bop c) (ltr_add_ann_op ltr c).
  Proof.
    intros [Ha Hb Hc].
    econstructor.
    + unfold slt_distributive in * |- *.
      intros ? [t | t] [u | u];
      simpl.
      ++ reflexivity.
      ++ destruct eqv_s; simpl in *.
        apply A_eqv_reflexive.
      ++ destruct eqv_s; simpl in *.
        apply A_eqv_reflexive.
      ++ apply Ha;
        try assumption.
    + unfold slt_absorptive in * |- *.
      intros ? [sa | sa].
      ++ reflexivity.
      ++ apply Hb; try assumption.
    + apply slt_add_ann_strictly_absorptive_decidable; 
      try assumption.
  Defined.
  

  Lemma left_semiring_add_ann_proofs :
    left_semiring_proofs r bop ltr ->
    left_semiring_proofs (sum.brel_sum brel_constant r)
      (bop_add_id bop c) (ltr_add_ann_op ltr c).
  Proof.
    intros [Ha Hb].
    econstructor.
    + unfold slt_distributive in * |- *.
      intros ? [t | t] [u | u];
      simpl.
      ++ reflexivity.
      ++ destruct eqv_s; simpl in *.
         apply A_eqv_reflexive.
      ++ destruct eqv_s; simpl in *.
         apply A_eqv_reflexive.
      ++ apply Ha;
         try assumption.
    + unfold slt_not_absorptive in * |- *.
      destruct Hb as ((au, bu) & H).
      exists (au, inr bu);
      simpl.
      exact H.
  Defined.


End Proofs.

Section Combinators.

  Definition A_slt_add_zero {L S : Type} 
    (A : @A_slt L S) (c : cas_constant) :
    @A_slt L (with_constant S).
  Proof.
    refine 
    {|
        A_slt_carrier := A_eqv_add_constant S (A_slt_carrier A) c
      ; A_slt_label  := A_slt_label A
      ; A_slt_plus  := bop_add_id (A_slt_plus A) c                                        
      ; A_slt_trans  := ltr_add_ann_op (A_slt_trans A) c
      ; A_slt_plus_proofs := sg_proofs_add_id S _ c _ 
        (structures.A_eqv_witness _ (A_slt_carrier A))
        (structures.A_eqv_new _ (A_slt_carrier A))
        (structures.A_eqv_not_trivial _ (A_slt_carrier A)) 
        (structures.A_eqv_proofs _ (A_slt_carrier A)) 
        (A_slt_plus_proofs A)           
      ; A_slt_trans_proofs := A_ltr_add_ann_proofs c
          (structures.A_eqv_witness _ (A_slt_carrier A))
          (structures.A_eqv_witness _ (A_slt_label A))
          _ _ _ (A_slt_trans_proofs A) 
      ; A_slt_exists_plus_ann_d :=  bop_add_id_exists_ann_decide S _ c _ 
         (structures.A_eqv_witness _ (A_slt_carrier A))
         (structures.A_eqv_reflexive _ _ 
            (structures.A_eqv_proofs _ (A_slt_carrier A))) 
         (A_slt_exists_plus_ann_d A)                                  
      ; A_slt_id_ann_proofs_d  := _                                               
      ; A_slt_proofs := slt_add_ann_proof c (A_eqv_witness L (A_slt_label A))
         (A_eqv_eq S (A_slt_carrier A)) (A_slt_trans A) 
         (A_slt_plus A) (A_eqv_proofs S (A_slt_carrier A)) 
         (A_slt_proofs A)                                 
      ; A_slt_ast :=  Cas_ast ("slt_add_zero", [A_slt_ast A; Cas_ast_constant c])
    |}.
    apply SLT_Id_Ann_Proof_Equal.
    exists (inl c); simpl.
    split.
    apply bop_add_id_is_id.
    exact (structures.A_eqv_reflexive _ _ 
      (structures.A_eqv_proofs _ (A_slt_carrier A))).
    intros ?; reflexivity.
  Defined.    



  Definition A_slt_C_add_zero {L S : Type} 
    (A : @A_slt_C L S) (c : cas_constant) :
    @A_slt_C L (with_constant S).
  Proof.
    refine
    {|
        A_slt_C_carrier := A_eqv_add_constant S (A_slt_C_carrier A) c
      ; A_slt_C_label  := A_slt_C_label A
      ; A_slt_C_plus  := bop_add_id (A_slt_C_plus A) c                                             
      ; A_slt_C_trans  := ltr_add_ann_op (A_slt_C_trans A) c
      ; A_slt_C_plus_proofs  := sg_C_proofs_add_id S _ c _ 
        (structures.A_eqv_witness _ (A_slt_C_carrier A))
        (structures.A_eqv_new _ (A_slt_C_carrier A))
        (structures.A_eqv_not_trivial _ (A_slt_C_carrier A)) 
        (structures.A_eqv_proofs _ (A_slt_C_carrier A)) 
        (A_slt_C_plus_proofs A)           
      ; A_slt_C_trans_proofs :=  A_ltr_add_ann_proofs c
          (structures.A_eqv_witness _ (A_slt_C_carrier A))
          (structures.A_eqv_witness _ (A_slt_C_label A))
          _ _ _ (A_slt_C_trans_proofs A) 
      ; A_slt_C_exists_plus_ann_d := bop_add_id_exists_ann_decide S _ c _ 
         (structures.A_eqv_witness _ (A_slt_C_carrier A))
         (structures.A_eqv_reflexive _ _ 
            (structures.A_eqv_proofs _ (A_slt_C_carrier A))) 
         (A_slt_C_exists_plus_ann_d A)                                         
      ; A_slt_C_id_ann_proofs_d := _                                            
      ; A_slt_C_proofs := slt_add_ann_proof c (A_eqv_witness L (A_slt_C_label A))
         (A_eqv_eq S (A_slt_C_carrier A)) (A_slt_C_trans A) 
         (A_slt_C_plus A) (A_eqv_proofs S (A_slt_C_carrier A)) 
         (A_slt_C_proofs A)                               
      ; A_slt_C_ast := Cas_ast ("A_slt_C_add_zero", [A_slt_C_ast A])
    
    |}.
    apply SLT_Id_Ann_Proof_Equal.
    exists (inl c); simpl.
    split.
    apply bop_add_id_is_id.
    exact (structures.A_eqv_reflexive _ _ 
      (structures.A_eqv_proofs _ (A_slt_C_carrier A))).
    intros ?; reflexivity.
  Defined.

  Definition A_slt_CS_add_zero {L S : Type} 
    (A : @A_slt_CS L S) (c : cas_constant) :
    @A_slt_CS L (with_constant S).
  Proof.
    refine
    {|
        A_slt_CS_carrier  := A_eqv_add_constant S (A_slt_CS_carrier A) c
      ; A_slt_CS_label := A_slt_CS_label A
      ; A_slt_CS_plus  := bop_add_id (A_slt_CS_plus A) c                                          
      ; A_slt_CS_trans := ltr_add_ann_op (A_slt_CS_trans A) c 
      ; A_slt_CS_plus_proofs  := sg_CS_proofs_add_id S _ c _ 
        (structures.A_eqv_witness _ (A_slt_CS_carrier A))
        (structures.A_eqv_proofs _ (A_slt_CS_carrier A)) 
        (A_slt_CS_plus_proofs A)        
      ; A_slt_CS_trans_proofs  := A_ltr_add_ann_proofs c
          (structures.A_eqv_witness _ (A_slt_CS_carrier A))
          (structures.A_eqv_witness _ (A_slt_CS_label A))
          _ _ _ (A_slt_CS_trans_proofs A) 
      ; A_slt_CS_exists_plus_ann_d := bop_add_id_exists_ann_decide S _ c _ 
         (structures.A_eqv_witness _ (A_slt_CS_carrier A))
         (structures.A_eqv_reflexive _ _ 
            (structures.A_eqv_proofs _ (A_slt_CS_carrier A))) 
         (A_slt_CS_exists_plus_ann_d A)                                   
      ; A_slt_CS_id_ann_proofs_d  := _                                    
      ; A_slt_CS_proofs := slt_add_ann_proof c (A_eqv_witness L (A_slt_CS_label A))
         (A_eqv_eq S (A_slt_CS_carrier A)) (A_slt_CS_trans A) 
         (A_slt_CS_plus A) (A_eqv_proofs S (A_slt_CS_carrier A)) 
         (A_slt_CS_proofs A)                               
      ; A_slt_CS_ast := Cas_ast ("A_slt_CS_add_zero", [A_slt_CS_ast A])
    |}.
    apply SLT_Id_Ann_Proof_Equal.
    exists (inl c); simpl.
    split.
    apply bop_add_id_is_id.
    exact (structures.A_eqv_reflexive _ _ 
      (structures.A_eqv_proofs _ (A_slt_CS_carrier A))).
    intros ?; reflexivity.
  Defined.
    

  Definition A_slt_CI_add_zero {L S : Type} 
    (A : @A_slt_CI L S) (c : cas_constant) :
    @A_slt_CI L (with_constant S).
  Proof.
    refine
    {|
        A_slt_CI_carrier  := A_eqv_add_constant S (A_slt_CI_carrier A) c
      ; A_slt_CI_label := A_slt_CI_label A
      ; A_slt_CI_plus  := bop_add_id (A_slt_CI_plus A) c                                          
      ; A_slt_CI_trans := ltr_add_ann_op (A_slt_CI_trans A) c 
      ; A_slt_CI_plus_proofs  := sg_CI_proofs_add_id S _ c _ 
        (structures.A_eqv_witness _ (A_slt_CI_carrier A))
        (structures.A_eqv_proofs _ (A_slt_CI_carrier A)) 
        (A_slt_CI_plus_proofs A)        
      ; A_slt_CI_trans_proofs  := A_ltr_add_ann_proofs c
          (structures.A_eqv_witness _ (A_slt_CI_carrier A))
          (structures.A_eqv_witness _ (A_slt_CI_label A))
          _ _ _ (A_slt_CI_trans_proofs A) 
      ; A_slt_CI_exists_plus_ann_d := bop_add_id_exists_ann_decide S _ c _ 
         (structures.A_eqv_witness _ (A_slt_CI_carrier A))
         (structures.A_eqv_reflexive _ _ 
            (structures.A_eqv_proofs _ (A_slt_CI_carrier A))) 
         (A_slt_CI_exists_plus_ann_d A)                                   
      ; A_slt_CI_id_ann_proofs_d  := _                                    
      ; A_slt_CI_proofs := slt_add_ann_proof c (A_eqv_witness L (A_slt_CI_label A))
         (A_eqv_eq S (A_slt_CI_carrier A)) (A_slt_CI_trans A) 
         (A_slt_CI_plus A) (A_eqv_proofs S (A_slt_CI_carrier A)) 
         (A_slt_CI_proofs A)                               
      ; A_slt_CI_ast := Cas_ast ("A_slt_CI_add_zero", [A_slt_CI_ast A])
    |}.
    apply SLT_Id_Ann_Proof_Equal.
    exists (inl c); simpl.
    split.
    apply bop_add_id_is_id.
    exact (structures.A_eqv_reflexive _ _ 
      (structures.A_eqv_proofs _ (A_slt_CI_carrier A))).
    intros ?; reflexivity.
  Defined.


  Definition A_slt_C_zero_is_ltr_ann_add_zero {L S : Type} 
    (A : @A_slt_C_zero_is_ltr_ann L S) (c : cas_constant) :
    @A_slt_C_zero_is_ltr_ann L (with_constant S).
  Proof.
    refine
    {|
        A_slt_C_zero_is_ltr_ann_carrier  := 
          A_eqv_add_constant S (A_slt_C_zero_is_ltr_ann_carrier A) c
      ; A_slt_C_zero_is_ltr_ann_label  := 
          A_slt_C_zero_is_ltr_ann_label A
      ; A_slt_C_zero_is_ltr_ann_plus  :=  
          bop_add_id (A_slt_C_zero_is_ltr_ann_plus A) c                               
      ; A_slt_C_zero_is_ltr_ann_trans   := 
          ltr_add_ann_op (A_slt_C_zero_is_ltr_ann_trans A) c 
      ; A_slt_C_zero_is_ltr_ann_plus_proofs  := 
          sg_C_proofs_add_id S _ c _ 
            (structures.A_eqv_witness _ (A_slt_C_zero_is_ltr_ann_carrier A))
            (structures.A_eqv_new _ (A_slt_C_zero_is_ltr_ann_carrier A))
            (structures.A_eqv_not_trivial _ (A_slt_C_zero_is_ltr_ann_carrier A)) 
            (structures.A_eqv_proofs _ (A_slt_C_zero_is_ltr_ann_carrier A)) 
            (A_slt_C_zero_is_ltr_ann_plus_proofs A)        
      ; A_slt_C_zero_is_ltr_ann_trans_proofs := 
          A_ltr_add_ann_proofs c
          (structures.A_eqv_witness _ (A_slt_C_zero_is_ltr_ann_carrier A))
          (structures.A_eqv_witness _ (A_slt_C_zero_is_ltr_ann_label A))
          _ _ _ (A_slt_C_zero_is_ltr_ann_trans_proofs A) 
      ; A_slt_C_zero_is_ltr_ann_exists_plus_ann_d :=  
          bop_add_id_exists_ann_decide S _ c _ 
         (structures.A_eqv_witness _ (A_slt_C_zero_is_ltr_ann_carrier A))
         (structures.A_eqv_reflexive _ _ 
            (structures.A_eqv_proofs _ (A_slt_C_zero_is_ltr_ann_carrier A))) 
         (A_slt_C_zero_is_ltr_ann_exists_plus_ann_d A)                                    
      ; A_slt_C_zero_is_ltr_ann_id_ann_proofs  :=   _                                          
      ; A_slt_C_zero_is_ltr_ann_proofs :=  
          slt_add_ann_proof c (A_eqv_witness L (A_slt_C_zero_is_ltr_ann_label A))
         (A_eqv_eq S (A_slt_C_zero_is_ltr_ann_carrier A)) 
         (A_slt_C_zero_is_ltr_ann_trans A) 
         (A_slt_C_zero_is_ltr_ann_plus A) 
         (A_eqv_proofs S (A_slt_C_zero_is_ltr_ann_carrier A)) 
         (A_slt_C_zero_is_ltr_ann_proofs A)                                 
      ; A_slt_C_zero_is_ltr_ann_ast := 
          Cas_ast ("A_slt_C_zero_is_ltr_ann_add_zero", 
            [A_slt_C_zero_is_ltr_ann_ast A])
    |}.
    
    exists (inl c); simpl.
    split.
    apply bop_add_id_is_id.
    exact (structures.A_eqv_reflexive _ _ 
      (structures.A_eqv_proofs _ (A_slt_C_zero_is_ltr_ann_carrier A))).
    intros ?; reflexivity.
  Defined.


  Definition A_selective_left_pre_dioid_add_zero {L S : Type} 
    (A : @A_selective_left_pre_dioid L S) (c : cas_constant) :
    @A_selective_left_pre_dioid L (with_constant S).
  Proof.
    refine
    {|
        A_selective_left_pre_dioid_carrier  := 
          A_eqv_add_constant S (A_selective_left_pre_dioid_carrier A) c
      ; A_selective_left_pre_dioid_label := 
         A_selective_left_pre_dioid_label A
      ; A_selective_left_pre_dioid_plus :=  
          bop_add_id (A_selective_left_pre_dioid_plus A) c                                           
      ; A_selective_left_pre_dioid_trans  := 
          ltr_add_ann_op (A_selective_left_pre_dioid_trans A) c 
      ; A_selective_left_pre_dioid_plus_proofs  := 
          sg_CS_proofs_add_id S _ c _ 
          (structures.A_eqv_witness _ (A_selective_left_pre_dioid_carrier A))
          (structures.A_eqv_proofs _ (A_selective_left_pre_dioid_carrier A)) 
          (A_selective_left_pre_dioid_plus_proofs A)      
      ; A_selective_left_pre_dioid_trans_proofs := 
          A_ltr_add_ann_proofs c
          (structures.A_eqv_witness _ (A_selective_left_pre_dioid_carrier A))
          (structures.A_eqv_witness _ (A_selective_left_pre_dioid_label A))
          _ _ _ (A_selective_left_pre_dioid_trans_proofs A) 
      ; A_selective_left_pre_dioid_exists_plus_ann := 
          bop_add_id_exists_ann S
         (A_eqv_eq S (A_selective_left_pre_dioid_carrier A)) c
         (A_selective_left_pre_dioid_plus A)
         (A_eqv_reflexive S
            (A_eqv_eq S (A_selective_left_pre_dioid_carrier A))
            (A_eqv_proofs S (A_selective_left_pre_dioid_carrier A)))
         (A_selective_left_pre_dioid_exists_plus_ann A)
      ; A_selective_left_pre_dioid_id_ann_proofs_d := _                        
      ; A_selective_left_pre_dioid_proofs :=  
          left_dioid_add_ann_proof c
         (A_eqv_witness L (A_selective_left_pre_dioid_label A))
         (A_eqv_eq S (A_selective_left_pre_dioid_carrier A))
         (A_selective_left_pre_dioid_trans A)
         (A_selective_left_pre_dioid_plus A)
         (A_eqv_proofs S (A_selective_left_pre_dioid_carrier A))
         (A_selective_left_pre_dioid_proofs A)                                
      ; A_selective_left_pre_dioid_ast := 
          Cas_ast ("A_selective_left_pre_dioid_add_zero", 
            [A_selective_left_pre_dioid_ast A])
    |}.
    apply SLT_Id_Ann_Proof_Equal.
    exists (inl c); simpl.
    split.
    apply bop_add_id_is_id.
    exact (structures.A_eqv_reflexive _ _ 
      (structures.A_eqv_proofs _ (A_selective_left_pre_dioid_carrier A))).
    intros ?; reflexivity.
  Defined.


   Definition A_selective_left_dioid_add_zero {L S : Type} 
    (A : @A_selective_left_dioid L S) (c : cas_constant) :
    @A_selective_left_dioid L (with_constant S).
  Proof.
    refine
    {|
        A_selective_left_dioid_carrier  := 
          A_eqv_add_constant S (A_selective_left_dioid_carrier A) c
      ; A_selective_left_dioid_label := 
         A_selective_left_dioid_label A
      ; A_selective_left_dioid_plus :=  
          bop_add_id (A_selective_left_dioid_plus A) c                                           
      ; A_selective_left_dioid_trans  := 
          ltr_add_ann_op (A_selective_left_dioid_trans A) c 
      ; A_selective_left_dioid_plus_proofs  := 
          sg_CS_proofs_add_id S _ c _ 
          (structures.A_eqv_witness _ (A_selective_left_dioid_carrier A))
          (structures.A_eqv_proofs _ (A_selective_left_dioid_carrier A)) 
          (A_selective_left_dioid_plus_proofs A)      
      ; A_selective_left_dioid_trans_proofs := 
          A_ltr_add_ann_proofs c
          (structures.A_eqv_witness _ (A_selective_left_dioid_carrier A))
          (structures.A_eqv_witness _ (A_selective_left_dioid_label A))
          _ _ _ (A_selective_left_dioid_trans_proofs A) 
      ; A_selective_left_dioid_exists_plus_ann := 
          bop_add_id_exists_ann S
         (A_eqv_eq S (A_selective_left_dioid_carrier A)) c
         (A_selective_left_dioid_plus A)
         (A_eqv_reflexive S
            (A_eqv_eq S (A_selective_left_dioid_carrier A))
            (A_eqv_proofs S (A_selective_left_dioid_carrier A)))
         (A_selective_left_dioid_exists_plus_ann A)
      ; A_selective_left_dioid_id_ann_proofs := _                        
      ; A_selective_left_dioid_proofs :=  
          left_dioid_add_ann_proof c
         (A_eqv_witness L (A_selective_left_dioid_label A))
         (A_eqv_eq S (A_selective_left_dioid_carrier A))
         (A_selective_left_dioid_trans A)
         (A_selective_left_dioid_plus A)
         (A_eqv_proofs S (A_selective_left_dioid_carrier A))
         (A_selective_left_dioid_proofs A)                                
      ; A_selective_left_dioid_ast := 
          Cas_ast ("A_selective_left_dioid_add_zero", 
            [A_selective_left_dioid_ast A])
    |}.

    exists (inl c); simpl.
    split.
    apply bop_add_id_is_id.
    exact (structures.A_eqv_reflexive _ _ 
      (structures.A_eqv_proofs _ (A_selective_left_dioid_carrier A))).
    intros ?; reflexivity.
  Defined.

  Definition A_left_dioid_add_zero {L S : Type} 
    (A : @A_left_dioid L S) (c : cas_constant) :
    @A_left_dioid L (with_constant S).
  Proof.
    refine
    {|
        A_left_dioid_carrier  := 
          A_eqv_add_constant S (A_left_dioid_carrier A) c
      ; A_left_dioid_label := 
         A_left_dioid_label A
      ; A_left_dioid_plus :=  
          bop_add_id (A_left_dioid_plus A) c                                           
      ; A_left_dioid_trans  := 
          ltr_add_ann_op (A_left_dioid_trans A) c 
      ; A_left_dioid_plus_proofs  := 
          sg_CI_proofs_add_id S _ c _ 
          (structures.A_eqv_witness _ (A_left_dioid_carrier A))
          (structures.A_eqv_proofs _ (A_left_dioid_carrier A)) 
          (A_left_dioid_plus_proofs A)      
      ; A_left_dioid_trans_proofs := 
          A_ltr_add_ann_proofs c
          (structures.A_eqv_witness _ (A_left_dioid_carrier A))
          (structures.A_eqv_witness _ (A_left_dioid_label A))
          _ _ _ (A_left_dioid_trans_proofs A) 
      ; A_left_dioid_exists_plus_ann := 
          bop_add_id_exists_ann S
         (A_eqv_eq S (A_left_dioid_carrier A)) c
         (A_left_dioid_plus A)
         (A_eqv_reflexive S
            (A_eqv_eq S (A_left_dioid_carrier A))
            (A_eqv_proofs S (A_left_dioid_carrier A)))
         (A_left_dioid_exists_plus_ann A)
      ; A_left_dioid_id_ann_proofs := _                        
      ; A_left_dioid_proofs :=  
          left_dioid_add_ann_proof c
         (A_eqv_witness L (A_left_dioid_label A))
         (A_eqv_eq S (A_left_dioid_carrier A))
         (A_left_dioid_trans A)
         (A_left_dioid_plus A)
         (A_eqv_proofs S (A_left_dioid_carrier A))
         (A_left_dioid_proofs A)                                
      ; A_left_dioid_ast := 
          Cas_ast ("A_left_dioid_add_zero", 
            [A_left_dioid_ast A])
    |}.
    exists (inl c); simpl.
    split.
    apply bop_add_id_is_id.
    exact (structures.A_eqv_reflexive _ _ 
      (structures.A_eqv_proofs _ (A_left_dioid_carrier A))).
    intros ?; reflexivity.
  Defined.



  Definition A_left_pre_semiring_add_zero {L S : Type} 
    (A : @A_left_pre_semiring L S) (c : cas_constant) :
    @A_left_pre_semiring L (with_constant S).
  Proof.
    refine
    {|
        A_left_pre_semiring_carrier   := 
          A_eqv_add_constant S (A_left_pre_semiring_carrier A) c
      ; A_left_pre_semiring_label   :=  
          A_left_pre_semiring_label A
      ; A_left_pre_semiring_plus   := 
          bop_add_id (A_left_pre_semiring_plus A) c                                                
      ; A_left_pre_semiring_trans  := 
          ltr_add_ann_op (A_left_pre_semiring_trans A) c 
      ; A_left_pre_semiring_plus_proofs := 
          sg_C_proofs_add_id S _ c _ 
          (structures.A_eqv_witness _ (A_left_pre_semiring_carrier A))
          (structures.A_eqv_new _ (A_left_pre_semiring_carrier A))
          (structures.A_eqv_not_trivial _ (A_left_pre_semiring_carrier A)) 
          (structures.A_eqv_proofs _ (A_left_pre_semiring_carrier A)) 
          (A_left_pre_semiring_plus_proofs A)                                 
      ; A_left_pre_semiring_trans_proofs := 
          A_ltr_add_ann_proofs c
          (structures.A_eqv_witness _ (A_left_pre_semiring_carrier A))
          (structures.A_eqv_witness _ (A_left_pre_semiring_label A))
          _ _ _ (A_left_pre_semiring_trans_proofs A)
      ; A_left_pre_semiring_exists_plus_ann_d :=
          bop_add_id_exists_ann_decide S _ c _ 
         (structures.A_eqv_witness _ (A_left_pre_semiring_carrier A))
         (structures.A_eqv_reflexive _ _ 
            (structures.A_eqv_proofs _ (A_left_pre_semiring_carrier A))) 
         (A_left_pre_semiring_exists_plus_ann_d A)                          
      ; A_left_pre_semiring_id_ann_proofs_d := _ 
      ; A_left_pre_semiring_proofs :=
          left_semiring_add_ann_proofs c
         (A_eqv_eq S (A_left_pre_semiring_carrier A))
         (A_left_pre_semiring_trans A) (A_left_pre_semiring_plus A)
         (A_eqv_proofs S (A_left_pre_semiring_carrier A))
         (A_left_pre_semiring_proofs A)
      ; A_left_pre_semiring_ast := 
          Cas_ast ("A_left_pre_semiring_add_zero", 
            [A_left_pre_semiring_ast A])
    |}.
    apply SLT_Id_Ann_Proof_Equal.
    exists (inl c); simpl.
    split.
    apply bop_add_id_is_id.
    exact (structures.A_eqv_reflexive _ _ 
      (structures.A_eqv_proofs _ (A_left_pre_semiring_carrier A))).
    intros ?; reflexivity.
  Defined.


  Definition A_left_semiring_add_zero {L S : Type} 
    (A : @A_left_semiring L S) (c : cas_constant) :
    @A_left_semiring L (with_constant S).
  Proof.
    refine
    {|
        A_left_semiring_carrier   := 
          A_eqv_add_constant S (A_left_semiring_carrier A) c
      ; A_left_semiring_label   :=  
          A_left_semiring_label A
      ; A_left_semiring_plus   := 
          bop_add_id (A_left_semiring_plus A) c                                                
      ; A_left_semiring_trans  := 
          ltr_add_ann_op (A_left_semiring_trans A) c 
      ; A_left_semiring_plus_proofs := 
          sg_C_proofs_add_id S _ c _ 
          (structures.A_eqv_witness _ (A_left_semiring_carrier A))
          (structures.A_eqv_new _ (A_left_semiring_carrier A))
          (structures.A_eqv_not_trivial _ (A_left_semiring_carrier A)) 
          (structures.A_eqv_proofs _ (A_left_semiring_carrier A)) 
          (A_left_semiring_plus_proofs A)                                 
      ; A_left_semiring_trans_proofs := 
          A_ltr_add_ann_proofs c
          (structures.A_eqv_witness _ (A_left_semiring_carrier A))
          (structures.A_eqv_witness _ (A_left_semiring_label A))
          _ _ _ (A_left_semiring_trans_proofs A)
      ; A_left_semiring_exists_plus_ann_d :=
          bop_add_id_exists_ann_decide S _ c _ 
         (structures.A_eqv_witness _ (A_left_semiring_carrier A))
         (structures.A_eqv_reflexive _ _ 
            (structures.A_eqv_proofs _ (A_left_semiring_carrier A))) 
         (A_left_semiring_exists_plus_ann_d A)                          
      ; A_left_semiring_id_ann_proofs:= _ 
      ; A_left_semiring_proofs :=
          left_semiring_add_ann_proofs c
         (A_eqv_eq S (A_left_semiring_carrier A))
         (A_left_semiring_trans A) (A_left_semiring_plus A)
         (A_eqv_proofs S (A_left_semiring_carrier A))
         (A_left_semiring_proofs A)
      ; A_left_semiring_ast := 
          Cas_ast ("A_left_semiring_add_zero", 
            [A_left_semiring_ast A])
    |}.
    exists (inl c); simpl.
    split.
    apply bop_add_id_is_id.
    exact (structures.A_eqv_reflexive _ _ 
      (structures.A_eqv_proofs _ (A_left_semiring_carrier A))).
    intros ?; reflexivity.
  Defined.




  Definition A_left_idempotent_semiring_add_zero {L S : Type} 
    (A : @A_left_idempotent_semiring L S) (c : cas_constant) :
    @A_left_idempotent_semiring L (with_constant S).
  Proof.
    refine
    {|
        A_left_idempotent_semiring_carrier   := 
          A_eqv_add_constant S (A_left_idempotent_semiring_carrier A) c
      ; A_left_idempotent_semiring_label   :=  
          A_left_idempotent_semiring_label A
      ; A_left_idempotent_semiring_plus   := 
          bop_add_id (A_left_idempotent_semiring_plus A) c                                                
      ; A_left_idempotent_semiring_trans  := 
          ltr_add_ann_op (A_left_idempotent_semiring_trans A) c 
      ; A_left_idempotent_semiring_plus_proofs := 
          sg_CI_proofs_add_id S _ c _ 
          (structures.A_eqv_witness _ (A_left_idempotent_semiring_carrier A))
          (structures.A_eqv_proofs _ (A_left_idempotent_semiring_carrier A)) 
          (A_left_idempotent_semiring_plus_proofs A)        
      ; A_left_idempotent_semiring_trans_proofs := 
          A_ltr_add_ann_proofs c
          (structures.A_eqv_witness _ (A_left_idempotent_semiring_carrier A))
          (structures.A_eqv_witness _ (A_left_idempotent_semiring_label A))
          _ _ _ (A_left_idempotent_semiring_trans_proofs A)
      ; A_left_idempotent_semiring_exists_plus_ann_d :=
          bop_add_id_exists_ann_decide S _ c _ 
         (structures.A_eqv_witness _ (A_left_idempotent_semiring_carrier A))
         (structures.A_eqv_reflexive _ _ 
            (structures.A_eqv_proofs _ (A_left_idempotent_semiring_carrier A))) 
         (A_left_idempotent_semiring_exists_plus_ann_d A)                          
      ; A_left_idempotent_semiring_id_ann_proofs:= _ 
      ; A_left_idempotent_semiring_proofs :=
          left_semiring_add_ann_proofs c
         (A_eqv_eq S (A_left_idempotent_semiring_carrier A))
         (A_left_idempotent_semiring_trans A) (A_left_idempotent_semiring_plus A)
         (A_eqv_proofs S (A_left_idempotent_semiring_carrier A))
         (A_left_idempotent_semiring_proofs A)
      ; A_left_idempotent_semiring_ast := 
          Cas_ast ("A_left_idempotent_semiring_add_zero", 
            [A_left_idempotent_semiring_ast A])
    |}.
    exists (inl c); simpl.
    split.
    apply bop_add_id_is_id.
    exact (structures.A_eqv_reflexive _ _ 
      (structures.A_eqv_proofs _ (A_left_idempotent_semiring_carrier A))).
    intros ?; reflexivity.
  Defined.

  
  

  Definition A_left_selective_semiring_add_zero {L S : Type} 
    (A : @A_left_selective_semiring L S) (c : cas_constant) :
    @A_left_selective_semiring L (with_constant S).
  Proof.
    refine
    {|
        A_left_selective_semiring_carrier   := 
          A_eqv_add_constant S (A_left_selective_semiring_carrier A) c
      ; A_left_selective_semiring_label   :=  
          A_left_selective_semiring_label A
      ; A_left_selective_semiring_plus   := 
          bop_add_id (A_left_selective_semiring_plus A) c                                                
      ; A_left_selective_semiring_trans  := 
          ltr_add_ann_op (A_left_selective_semiring_trans A) c 
      ; A_left_selective_semiring_plus_proofs := 
          sg_CS_proofs_add_id S _ c _ 
          (structures.A_eqv_witness _ (A_left_selective_semiring_carrier A))
          (structures.A_eqv_proofs _ (A_left_selective_semiring_carrier A)) 
          (A_left_selective_semiring_plus_proofs A)                                  
      ; A_left_selective_semiring_trans_proofs := 
          A_ltr_add_ann_proofs c
          (structures.A_eqv_witness _ (A_left_selective_semiring_carrier A))
          (structures.A_eqv_witness _ (A_left_selective_semiring_label A))
          _ _ _ (A_left_selective_semiring_trans_proofs A)
      ; A_left_selective_semiring_exists_plus_ann_d :=
          bop_add_id_exists_ann_decide S _ c _ 
         (structures.A_eqv_witness _ (A_left_selective_semiring_carrier A))
         (structures.A_eqv_reflexive _ _ 
            (structures.A_eqv_proofs _ (A_left_selective_semiring_carrier A))) 
         (A_left_selective_semiring_exists_plus_ann_d A)                          
      ; A_left_selective_semiring_id_ann_proofs:= _ 
      ; A_left_selective_semiring_proofs :=
          left_semiring_add_ann_proofs c
         (A_eqv_eq S (A_left_selective_semiring_carrier A))
         (A_left_selective_semiring_trans A) (A_left_selective_semiring_plus A)
         (A_eqv_proofs S (A_left_selective_semiring_carrier A))
         (A_left_selective_semiring_proofs A)
      ; A_left_selective_semiring_ast := 
          Cas_ast ("A_left_selective_semiring_add_zero", 
            [A_left_selective_semiring_ast A])
    |}.
    exists (inl c); simpl.
    split.
    apply bop_add_id_is_id.
    exact (structures.A_eqv_reflexive _ _ 
      (structures.A_eqv_proofs _ (A_left_selective_semiring_carrier A))).
    intros ?; reflexivity.
  Defined.

End Combinators.   
End ACAS.

Section AMCAS.

Open Scope string_scope.   

Definition A_mcas_slt_add_zero_aux {L S : Type}
  (A : @A_slt_mcas L S) (c : cas_constant) : @A_slt_mcas L (with_constant S).
Proof.
  refine 
    match A with 
    | A_SLT_Error ls => A_SLT_Error ls
    | A_SLT slt => A_SLT (A_slt_add_zero slt c)
    | A_SLT_C slt => A_SLT_C (A_slt_C_add_zero slt c) 
    | A_SLT_CS slt => A_SLT_CS (A_slt_CS_add_zero slt c)
    | A_SLT_CI slt =>A_SLT_CI (A_slt_CI_add_zero  slt c)
    | A_SLT_C_Zero_Is_Ltr_ann slt => 
        A_SLT_C_Zero_Is_Ltr_ann (A_slt_C_zero_is_ltr_ann_add_zero slt c)
    | A_SLT_Left_Pre_Semiring slt => 
        A_SLT_Left_Pre_Semiring (A_left_pre_semiring_add_zero slt c)
    | A_SLT_Dioid slt => 
        A_SLT_Dioid (A_left_dioid_add_zero slt c)
    | A_SLT_Selective_Left_Pre_Dioid slt => 
        A_SLT_Selective_Left_Pre_Dioid (A_selective_left_pre_dioid_add_zero  slt c)
    | A_SLT_Semiring slt => 
        A_SLT_Semiring (A_left_semiring_add_zero slt c) 
    | A_SLT_Selective_Dioid slt =>
        A_SLT_Selective_Dioid (A_selective_left_dioid_add_zero slt c) 
    | A_SLT_Selective_Semiring slt => 
        A_SLT_Selective_Semiring (A_left_selective_semiring_add_zero  slt c)
    | A_SLT_Idempotent_Semiring slt => 
        A_SLT_Idempotent_Semiring (A_left_idempotent_semiring_add_zero slt c) 
    end.
Defined.

Definition A_mcas_slt_add_zero {L S : Type}
  (A : @A_slt_mcas L S) (c : cas_constant) := 
  match cast_A_slt_mcas_to_A_slt A with 
  | A_SLT B =>  A_slt_classify_slt (A_slt_add_zero B c)
  | A_SLT_Error l => A_SLT_Error l 
  | _ => A_SLT_Error ["Internal Error : mcas_slt_add_zero"]
  end.  


End AMCAS. 


Section CAS.

Section Certify.
    
  Context 
    {L S : Type}
    (c : cas_constant)
    (wL : L).

 
  Lemma slt_add_ann_distributive_check :
    @check_slt_distributive L S ->
    @check_slt_distributive L (with_constant S).
  Proof.
    intros Ha.
    destruct Ha eqn:H.
    + apply Certify_Slt_Distributive.
    + apply Certify_Slt_Not_Distributive.
      destruct p as (au, (bu, cu)).  
      exact (au, (inr bu, inr cu)).
  Defined.
  
 


  Lemma slt_add_ann_absorptive_check :
    @check_slt_absorptive L S ->
    @check_slt_absorptive L (with_constant S). 
  Proof.
    intros Ha.
    case Ha eqn:H.
    + apply Certify_Slt_Absorptive.
    + apply Certify_Slt_Not_Absorptive.
      destruct p as (au, bu).
      exact (au, inr bu).
  Defined.  

    
  Lemma slt_add_ann_strictly_absorptive_check :
    @check_slt_strictly_absorptive L S -> (* we don't need this *)
    @check_slt_strictly_absorptive L (with_constant S).
  Proof.
    intros Ha.
    case Ha eqn:H.
    + apply Certify_Slt_Not_Strictly_Absorptive.
      exact (wL, inl c).
    + apply Certify_Slt_Not_Strictly_Absorptive.
      destruct p as (au, bu).
      exact (au, inr bu).
  Defined.
  


 
  Lemma slt_add_ann_certificate  :
    @slt_certificates L S ->
    @slt_certificates L (with_constant S).
  Proof.
    intros [Ha Hb Hc].
    econstructor.
    + exact (slt_add_ann_distributive_check Ha).
    + exact (slt_add_ann_absorptive_check Hb).
    + exact (slt_add_ann_strictly_absorptive_check Hc).
  Defined.   

  

  Lemma left_dioid_add_ann_certificate : 
    @left_dioid_certificates L S -> 
    @left_dioid_certificates L (with_constant S).
  Proof.
    intros [Ha Hb Hc].
    econstructor.
    + exact Assert_Slt_Distributive.
    + exact Assert_Slt_Absorptive.
    + exact (slt_add_ann_strictly_absorptive_check Hc).
  Defined.   
   

  Lemma left_semiring_add_ann_certificate :
    @left_semiring_certificates L S ->
    @left_semiring_certificates L (with_constant S). 
  Proof.
    intros [Ha Hb].
    econstructor.
    + exact Assert_Slt_Distributive.
    + case Hb eqn:H.
      destruct p as (au, av).
      exact (Assert_Slt_Not_Absorptive (au, inr av)).
  Defined.
  
End Certify.

Section Certificates.



End Certificates.   

Section Combinators.

  Definition slt_add_zero {L S : Type} 
    (A : @slt L S) (c : cas_constant) :
    @slt L (with_constant S).
  Proof.
    refine 
    {|
        slt_carrier := eqv_add_constant (slt_carrier A) c
      ; slt_label  := slt_label A
      ; slt_plus  := bop_add_id (slt_plus A) c                                        
      ; slt_trans  := ltr_add_ann_op (slt_trans A) c
      ; slt_plus_certs := sg_certs_add_id c
          (structures.eqv_witness (slt_carrier A))
          (structures.eqv_new (slt_carrier A))
          (slt_plus_certs A)    
      ; slt_trans_certs := ltr_add_ann_certs c 
          (structures.eqv_witness (slt_carrier A))
          (structures.eqv_witness (slt_label A))
          (slt_trans_certs A)
      ; slt_exists_plus_ann_d := @bop_add_id_exists_ann_check S 
          (slt_exists_plus_ann_d A)                          
      ; slt_id_ann_certs_d  := Certify_SLT_Id_Ann_Proof_Equal (inl c)                                              
      ; slt_certs := slt_add_ann_certificate c 
        (structures.eqv_witness (slt_label A)) (slt_certs A)                          
      ; slt_ast :=  Cas_ast ("slt_add_zero", [slt_ast A; Cas_ast_constant c])
    |}.
  Defined.

  Definition slt_C_add_zero {L S : Type} 
    (A : @slt_C L S) (c : cas_constant) :
    @slt_C L (with_constant S).
  Proof.
    refine
    {|
        slt_C_carrier := eqv_add_constant (slt_C_carrier A) c
      ; slt_C_label  := slt_C_label A
      ; slt_C_plus  := bop_add_id (slt_C_plus A) c                                             
      ; slt_C_trans  := ltr_add_ann_op (slt_C_trans A) c
      ; slt_C_plus_certs  := sg_C_certs_add_id c
          (structures.eqv_witness (slt_C_carrier A))
          (structures.eqv_new (slt_C_carrier A))
          (slt_C_plus_certs A)
      ; slt_C_trans_certs :=  ltr_add_ann_certs c
          (structures.eqv_witness (slt_C_carrier A))
          (structures.eqv_witness (slt_C_label A))
          (slt_C_trans_certs A) 
      ; slt_C_exists_plus_ann_d :=  @bop_add_id_exists_ann_check S 
         (slt_C_exists_plus_ann_d A)                                         
      ; slt_C_id_ann_certs_d :=  Certify_SLT_Id_Ann_Proof_Equal (inl c)                                             
      ; slt_C_certs := slt_add_ann_certificate 
          c (structures.eqv_witness (slt_C_label A)) (slt_C_certs A)                             
      ; slt_C_ast := Cas_ast ("A_slt_C_add_zero", [slt_C_ast A])
    
    |}.
  Defined.

  Definition slt_CS_add_zero {L S : Type} 
    (A : @slt_CS L S) (c : cas_constant) :
    @slt_CS L (with_constant S).
  Proof.
    refine
    {|
        slt_CS_carrier  := eqv_add_constant (slt_CS_carrier A) c
      ; slt_CS_label := slt_CS_label A
      ; slt_CS_plus  := bop_add_id (slt_CS_plus A) c                                          
      ; slt_CS_trans := ltr_add_ann_op (slt_CS_trans A) c 
      ; slt_CS_plus_certs  := sg_CS_certs_add_id c 
        (slt_CS_plus_certs A)        
      ; slt_CS_trans_certs  := ltr_add_ann_certs c
          (structures.eqv_witness (slt_CS_carrier A))
          (structures.eqv_witness (slt_CS_label A))
          (slt_CS_trans_certs A) 
      ; slt_CS_exists_plus_ann_d :=  @bop_add_id_exists_ann_check S 
         (slt_CS_exists_plus_ann_d A)                                   
      ; slt_CS_id_ann_certs_d  :=  Certify_SLT_Id_Ann_Proof_Equal (inl c)                                     
      ; slt_CS_certs := slt_add_ann_certificate 
          c (structures.eqv_witness (slt_CS_label A)) (slt_CS_certs A)                             
      ; slt_CS_ast := Cas_ast ("A_slt_CS_add_zero", [slt_CS_ast A])
    |}.
  Defined.




  Definition slt_CI_add_zero {L S : Type} 
    (A : @slt_CI L S) (c : cas_constant) :
    @slt_CI L (with_constant S).
  Proof.
    refine
    {|
        slt_CI_carrier  := eqv_add_constant (slt_CI_carrier A) c
      ; slt_CI_label := slt_CI_label A
      ; slt_CI_plus  := bop_add_id (slt_CI_plus A) c                                          
      ; slt_CI_trans := ltr_add_ann_op (slt_CI_trans A) c 
      ; slt_CI_plus_certs  := sg_CI_certs_add_id c 
        (slt_CI_plus_certs A)        
      ; slt_CI_trans_certs  := ltr_add_ann_certs c
          (structures.eqv_witness (slt_CI_carrier A))
          (structures.eqv_witness (slt_CI_label A))
          (slt_CI_trans_certs A) 
      ; slt_CI_exists_plus_ann_d :=  @bop_add_id_exists_ann_check S 
         (slt_CI_exists_plus_ann_d A)                                   
      ; slt_CI_id_ann_certs_d  :=  Certify_SLT_Id_Ann_Proof_Equal (inl c)                                     
      ; slt_CI_certs := slt_add_ann_certificate 
          c (structures.eqv_witness (slt_CI_label A)) (slt_CI_certs A)                             
      ; slt_CI_ast := Cas_ast ("A_slt_CI_add_zero", [slt_CI_ast A])
    |}.
  Defined.

  


  Definition slt_C_zero_is_ltr_ann_add_zero {L S : Type} 
    (A : @slt_C_zero_is_ltr_ann L S) (c : cas_constant) :
    @slt_C_zero_is_ltr_ann L (with_constant S).
  Proof.
    refine
    {|
        slt_C_zero_is_ltr_ann_carrier  := 
          eqv_add_constant (slt_C_zero_is_ltr_ann_carrier A) c
      ; slt_C_zero_is_ltr_ann_label  := 
          slt_C_zero_is_ltr_ann_label A
      ; slt_C_zero_is_ltr_ann_plus  :=  
          bop_add_id (slt_C_zero_is_ltr_ann_plus A) c                               
      ; slt_C_zero_is_ltr_ann_trans   := 
          ltr_add_ann_op (slt_C_zero_is_ltr_ann_trans A) c 
      ; slt_C_zero_is_ltr_ann_plus_certs  := 
          sg_C_certs_add_id c 
            (structures.eqv_witness (slt_C_zero_is_ltr_ann_carrier A))
            (structures.eqv_new (slt_C_zero_is_ltr_ann_carrier A))
            (slt_C_zero_is_ltr_ann_plus_certs A)        
      ; slt_C_zero_is_ltr_ann_trans_certs := 
          ltr_add_ann_certs c
          (structures.eqv_witness (slt_C_zero_is_ltr_ann_carrier A))
          (structures.eqv_witness (slt_C_zero_is_ltr_ann_label A))
          (slt_C_zero_is_ltr_ann_trans_certs A) 
      ; slt_C_zero_is_ltr_ann_exists_plus_ann_d :=  
          @bop_add_id_exists_ann_check S
         (slt_C_zero_is_ltr_ann_exists_plus_ann_d A)                                    
      ; slt_C_zero_is_ltr_ann_id_ann_certs  := Assert_Slt_Exists_Id_Ann_Equal (inl c)                                           
      ; slt_C_zero_is_ltr_ann_certs :=  
          slt_add_ann_certificate c 
          (structures.eqv_witness (slt_C_zero_is_ltr_ann_label A))
         (slt_C_zero_is_ltr_ann_certs A)                                 
      ; slt_C_zero_is_ltr_ann_ast := 
          Cas_ast ("A_slt_C_zero_is_ltr_ann_add_zero", 
            [slt_C_zero_is_ltr_ann_ast A])
    |}.
  Defined.


  Definition selective_left_pre_dioid_add_zero {L S : Type} 
    (A : @selective_left_pre_dioid L S) (c : cas_constant) :
    @selective_left_pre_dioid L (with_constant S).
  Proof.
    refine
    {|
        selective_left_pre_dioid_carrier  := 
          eqv_add_constant (selective_left_pre_dioid_carrier A) c
      ; selective_left_pre_dioid_label := 
         selective_left_pre_dioid_label A
      ; selective_left_pre_dioid_plus :=  
          bop_add_id (selective_left_pre_dioid_plus A) c                                           
      ; selective_left_pre_dioid_trans  := 
          ltr_add_ann_op (selective_left_pre_dioid_trans A) c 
      ; selective_left_pre_dioid_plus_certs  := 
          sg_CS_certs_add_id c   
          (selective_left_pre_dioid_plus_certs A)      
      ; selective_left_pre_dioid_trans_certs := 
          ltr_add_ann_certs c
          (structures.eqv_witness (selective_left_pre_dioid_carrier A))
          (structures.eqv_witness (selective_left_pre_dioid_label A))
          (selective_left_pre_dioid_trans_certs A) 
      ; selective_left_pre_dioid_exists_plus_ann := 
          _
      ; selective_left_pre_dioid_id_ann_certs_d :=  
          Certify_SLT_Id_Ann_Proof_Equal (inl c)                         
      ; selective_left_pre_dioid_certs :=  
          left_dioid_add_ann_certificate c 
          (structures.eqv_witness (selective_left_pre_dioid_label A))
         (selective_left_pre_dioid_certs A)                                
      ; selective_left_pre_dioid_ast := 
          Cas_ast ("A_selective_left_pre_dioid_add_zero", 
            [selective_left_pre_dioid_ast A])
    |}.
    destruct A; simpl.
    destruct selective_left_pre_dioid_exists_plus_ann.
    econstructor.
    exact (inr s).
  Defined.

   


  Definition selective_left_dioid_add_zero {L S : Type} 
    (A : @selective_left_dioid L S) (c : cas_constant) :
    @selective_left_dioid L (with_constant S).
  Proof.
    refine
    {|
        selective_left_dioid_carrier  := 
          eqv_add_constant (selective_left_dioid_carrier A) c
      ; selective_left_dioid_label := 
         selective_left_dioid_label A
      ; selective_left_dioid_plus :=  
          bop_add_id (selective_left_dioid_plus A) c                                           
      ; selective_left_dioid_trans  := 
          ltr_add_ann_op (selective_left_dioid_trans A) c 
      ; selective_left_dioid_plus_certs  := 
          sg_CS_certs_add_id c 
          (selective_left_dioid_plus_certs A)      
      ; selective_left_dioid_trans_certs := 
          ltr_add_ann_certs c
          (structures.eqv_witness (selective_left_dioid_carrier A))
          (structures.eqv_witness (selective_left_dioid_label A))
          (selective_left_dioid_trans_certs A) 
      ; selective_left_dioid_exists_plus_ann := 
          _
      ; selective_left_dioid_id_ann_certs :=
          Assert_Slt_Exists_Id_Ann_Equal (inl c)                        
      ; selective_left_dioid_certs :=  
          left_dioid_add_ann_certificate c 
          (structures.eqv_witness (selective_left_dioid_label A))
         (selective_left_dioid_certs A)                                
      ; selective_left_dioid_ast := 
          Cas_ast ("A_selective_left_dioid_add_zero", 
            [selective_left_dioid_ast A])
    |}.
    destruct A; simpl.
    destruct selective_left_dioid_exists_plus_ann.
    econstructor.
    exact (inr s).
  Defined.

  
  Definition left_dioid_add_zero {L S : Type} 
    (A : @left_dioid L S) (c : cas_constant) :
    @left_dioid L (with_constant S).
  Proof.
    refine
    {|
        left_dioid_carrier  := 
          eqv_add_constant (left_dioid_carrier A) c
      ; left_dioid_label := 
         left_dioid_label A
      ; left_dioid_plus :=  
          bop_add_id (left_dioid_plus A) c                                           
      ; left_dioid_trans  := 
          ltr_add_ann_op (left_dioid_trans A) c 
      ; left_dioid_plus_certs  := 
          sg_CI_certs_add_id c
          (left_dioid_plus_certs A)      
      ; left_dioid_trans_certs := 
          ltr_add_ann_certs c
          (structures.eqv_witness (left_dioid_carrier A))
          (structures.eqv_witness (left_dioid_label A))
          (left_dioid_trans_certs A) 
      ; left_dioid_exists_plus_ann := 
         _
      ; left_dioid_id_ann_certs := 
          Assert_Slt_Exists_Id_Ann_Equal (inl c)                         
      ; left_dioid_certs :=  
          left_dioid_add_ann_certificate c 
          (structures.eqv_witness (left_dioid_label A))
         (left_dioid_certs A)                                
      ; left_dioid_ast := 
          Cas_ast ("A_left_dioid_add_zero", 
            [left_dioid_ast A])
    |}.
    destruct A, left_dioid_exists_plus_ann; simpl.
    econstructor.
    exact (inr s).
  Defined.


  Definition left_pre_semiring_add_zero {L S : Type} 
  (A : @left_pre_semiring L S) (c : cas_constant) :
  @left_pre_semiring L (with_constant S).
Proof.
  refine
  {|
      left_pre_semiring_carrier   := 
        eqv_add_constant (left_pre_semiring_carrier A) c
    ; left_pre_semiring_label   :=  
        left_pre_semiring_label A
    ; left_pre_semiring_plus   := 
        bop_add_id (left_pre_semiring_plus A) c                                                
    ; left_pre_semiring_trans  := 
        ltr_add_ann_op (left_pre_semiring_trans A) c 
    ; left_pre_semiring_plus_certs := 
        sg_C_certs_add_id  c 
        (structures.eqv_witness (left_pre_semiring_carrier A))
        (structures.eqv_new (left_pre_semiring_carrier A))
        (left_pre_semiring_plus_certs A)                                 
    ; left_pre_semiring_trans_certs := 
        ltr_add_ann_certs c
        (structures.eqv_witness (left_pre_semiring_carrier A))
        (structures.eqv_witness (left_pre_semiring_label A))
        (left_pre_semiring_trans_certs A)
    ; left_pre_semiring_exists_plus_ann_d :=
        @bop_add_id_exists_ann_check S
        (left_pre_semiring_exists_plus_ann_d A)                          
    ; left_pre_semiring_id_ann_certs_d := 
         Certify_SLT_Id_Ann_Proof_Equal (inl c) 
    ; left_pre_semiring_certs :=
        left_semiring_add_ann_certificate
       (left_pre_semiring_certs A)
    ; left_pre_semiring_ast := 
        Cas_ast ("A_left_pre_semiring_add_zero", 
          [left_pre_semiring_ast A])
  |}.
  Defined.

  Definition left_semiring_add_zero {L S : Type} 
  (A : @left_semiring L S) (c : cas_constant) :
  @left_semiring L (with_constant S).
Proof.
  refine
  {|
      left_semiring_carrier   := 
        eqv_add_constant (left_semiring_carrier A) c
    ; left_semiring_label   :=  
        left_semiring_label A
    ; left_semiring_plus   := 
        bop_add_id (left_semiring_plus A) c                                                
    ; left_semiring_trans  := 
        ltr_add_ann_op (left_semiring_trans A) c 
    ; left_semiring_plus_certs := 
        sg_C_certs_add_id c 
        (structures.eqv_witness (left_semiring_carrier A))
        (structures.eqv_new (left_semiring_carrier A))
        (left_semiring_plus_certs A)                                 
    ; left_semiring_trans_certs := 
        ltr_add_ann_certs c
        (structures.eqv_witness (left_semiring_carrier A))
        (structures.eqv_witness (left_semiring_label A))
        (left_semiring_trans_certs A)
    ; left_semiring_exists_plus_ann_d :=
        @bop_add_id_exists_ann_check S 
       (left_semiring_exists_plus_ann_d A)                          
    ; left_semiring_id_ann_certs:= 
        Assert_Slt_Exists_Id_Ann_Equal (inl c)
    ; left_semiring_certs :=
        left_semiring_add_ann_certificate
       (left_semiring_certs A)
    ; left_semiring_ast := 
        Cas_ast ("A_left_semiring_add_zero", 
          [left_semiring_ast A])
  |}.
  Defined.
  


  Definition left_idempotent_semiring_add_zero {L S : Type} 
    (A : @left_idempotent_semiring L S) (c : cas_constant) :
    @left_idempotent_semiring L (with_constant S).
  Proof.
    refine
    {|
        left_idempotent_semiring_carrier   := 
          eqv_add_constant (left_idempotent_semiring_carrier A) c
      ; left_idempotent_semiring_label   :=  
          left_idempotent_semiring_label A
      ; left_idempotent_semiring_plus   := 
          bop_add_id (left_idempotent_semiring_plus A) c                                                
      ; left_idempotent_semiring_trans  := 
          ltr_add_ann_op (left_idempotent_semiring_trans A) c 
      ; left_idempotent_semiring_plus_certs := 
          sg_CI_certs_add_id c
          (left_idempotent_semiring_plus_certs A)        
      ; left_idempotent_semiring_trans_certs := 
          ltr_add_ann_certs c
          (structures.eqv_witness (left_idempotent_semiring_carrier A))
          (structures.eqv_witness (left_idempotent_semiring_label A))
          (left_idempotent_semiring_trans_certs A)
      ; left_idempotent_semiring_exists_plus_ann_d :=
          @bop_add_id_exists_ann_check S
          (left_idempotent_semiring_exists_plus_ann_d A)                          
      ; left_idempotent_semiring_id_ann_certs :=
          Assert_Slt_Exists_Id_Ann_Equal (inl c)
      ; left_idempotent_semiring_certs :=
          left_semiring_add_ann_certificate
        (left_idempotent_semiring_certs A)
      ; left_idempotent_semiring_ast := 
          Cas_ast ("A_left_idempotent_semiring_add_zero", 
            [left_idempotent_semiring_ast A])
    |}.
  Defined.



  Definition left_selective_semiring_add_zero {L S : Type} 
    (A : @left_selective_semiring L S) (c : cas_constant) :
    @left_selective_semiring L (with_constant S).
  Proof.
  refine
  {|
      left_selective_semiring_carrier   := 
        eqv_add_constant (left_selective_semiring_carrier A) c
    ; left_selective_semiring_label   :=  
        left_selective_semiring_label A
    ; left_selective_semiring_plus   := 
        bop_add_id (left_selective_semiring_plus A) c                                                
    ; left_selective_semiring_trans  := 
        ltr_add_ann_op (left_selective_semiring_trans A) c 
    ; left_selective_semiring_plus_certs := 
        sg_CS_certs_add_id c
        (left_selective_semiring_plus_certs A)                                  
    ; left_selective_semiring_trans_certs := 
        ltr_add_ann_certs c
        (structures.eqv_witness (left_selective_semiring_carrier A))
        (structures.eqv_witness (left_selective_semiring_label A))
        (left_selective_semiring_trans_certs A)
    ; left_selective_semiring_exists_plus_ann_d :=
        @bop_add_id_exists_ann_check S
        (left_selective_semiring_exists_plus_ann_d A)                          
    ; left_selective_semiring_id_ann_certs := 
        Assert_Slt_Exists_Id_Ann_Equal (inl c)
    ; left_selective_semiring_certs :=
        left_semiring_add_ann_certificate
       (left_selective_semiring_certs A)
    ; left_selective_semiring_ast := 
        Cas_ast ("A_left_selective_semiring_add_zero", 
          [left_selective_semiring_ast A])
  |}.
  Defined.









  

    

End Combinators.   
End CAS.


Section MCAS. 

Open Scope string_scope.


Definition mcas_slt_add_zero_aux {L S : Type}
  (A : @slt_mcas L S) (c : cas_constant) : @slt_mcas L (with_constant S).
Proof.
refine 
  match A with 
  | SLT_Error ls => SLT_Error ls
  | SLT slt => SLT (slt_add_zero slt c)
  | SLT_C slt => SLT_C (slt_C_add_zero slt c) 
  | SLT_CS slt => SLT_CS (slt_CS_add_zero slt c)
  | SLT_CI slt => SLT_CI (slt_CI_add_zero  slt c)
  | SLT_C_Zero_Is_Ltr_ann slt => 
      SLT_C_Zero_Is_Ltr_ann (slt_C_zero_is_ltr_ann_add_zero slt c)
  | SLT_Left_Pre_Semiring slt => 
      SLT_Left_Pre_Semiring (left_pre_semiring_add_zero slt c)
  | SLT_Dioid slt => 
      SLT_Dioid (left_dioid_add_zero slt c)
  | SLT_Selective_Left_Pre_Dioid slt => 
      SLT_Selective_Left_Pre_Dioid (selective_left_pre_dioid_add_zero slt c)
  | SLT_Semiring slt => 
      SLT_Semiring  (left_semiring_add_zero slt c) 
  | SLT_Selective_Dioid slt => 
      SLT_Selective_Dioid (selective_left_dioid_add_zero slt c) 
  | SLT_Selective_Semiring slt => 
      SLT_Selective_Semiring (left_selective_semiring_add_zero  slt c)
  | SLT_Idempotent_Semiring slt => 
      SLT_Idempotent_Semiring (left_idempotent_semiring_add_zero slt c) 
  end.
Defined.

Definition mcas_slt_add_zero {L S : Type}
  (A : @slt_mcas L S) (c : cas_constant) := 
  match cast_slt_mcas_to_slt A with 
  | SLT B =>  slt_classify_slt (slt_add_zero B c)
  | SLT_Error l => SLT_Error l 
  | _ => SLT_Error ["Internal Error : mcas_slt_add_zero"]
  end.  



End MCAS. 




Section Verify.



Section Certify.
  Context 
    {L S : Type}
    (c : cas_constant)
    (wL : L)
    (r : brel S)
    (ltr : ltr_type L S)
    (bop : binary_op S)
    (eqv_s : @eqv_proofs S r).

  Lemma slt_add_ann_distributive_correct 
    (pf : slt_distributive_decidable r bop ltr) :
    p2c_slt_distributive_check (sum.brel_sum brel_constant r)
    (bop_add_id bop c) (ltr_add_ann_op ltr c)
    (slt_add_ann_distributive_decidable c r ltr bop eqv_s pf) =
   slt_add_ann_distributive_check
    (p2c_slt_distributive_check r bop ltr pf).
  Proof.
    destruct pf; simpl.
    + reflexivity.
    + destruct s, x, p; cbn.
      reflexivity.
  Defined.

  Lemma slt_add_ann_absorptive_correct 
    (pf : slt_absorptive_decidable r bop ltr) : 
    p2c_slt_absorptive_check (sum.brel_sum brel_constant r) 
    (bop_add_id bop c) (ltr_add_ann_op ltr c)
    (slt_add_ann_absorptive_decidable c r ltr bop pf) =
    slt_add_ann_absorptive_check
    (p2c_slt_absorptive_check r bop ltr pf).
  Proof.
    destruct pf; simpl.
    + reflexivity.
    + destruct s, x, y;
      cbn; reflexivity.
  Defined.  

  
  Lemma slt_add_ann_strictly_absorptive_correct 
    (pf : slt_strictly_absorptive_decidable r bop ltr) :
    p2c_slt_strictly_absorptive_check (sum.brel_sum brel_constant r)
    (bop_add_id bop c) (ltr_add_ann_op ltr c)
    (slt_add_ann_strictly_absorptive_decidable c wL r ltr bop pf) =
    slt_add_ann_strictly_absorptive_check c wL
    (p2c_slt_strictly_absorptive_check r bop ltr pf).
  Proof.
    destruct pf; simpl.
    + reflexivity.
    + destruct s, x, y;
      cbn; reflexivity.
  Defined.  

 
  Lemma slt_add_ann_proof_correct  
    (pf : slt_proofs r bop ltr) :
    P2C_slt _ _ _  (slt_add_ann_proof c wL r ltr bop eqv_s pf) = 
    @slt_add_ann_certificate _ _ c wL (P2C_slt _ _ _ pf).
  Proof.
    unfold P2C_slt;
    destruct pf; simpl;
    f_equal.
    + eapply slt_add_ann_distributive_correct.
    + eapply slt_add_ann_absorptive_correct.
    + eapply slt_add_ann_strictly_absorptive_correct.
  Defined.   
    
 
  Lemma left_dioid_add_ann_proof_correct  
    (pf : left_dioid_proofs r bop ltr) :
    P2C_left_dioid _ _ _  (left_dioid_add_ann_proof c wL r ltr bop eqv_s pf) = 
    @left_dioid_add_ann_certificate _ _ c wL (P2C_left_dioid _ _ _ pf).
  Proof.
    unfold P2C_left_dioid;
    destruct pf; simpl;
    f_equal.
    eapply slt_add_ann_strictly_absorptive_correct.
  Defined.
  

  Lemma left_semiring_add_ann_proof_correct 
    (pf : left_semiring_proofs r bop ltr) :
    P2C_left_semiring _ _ _  (left_semiring_add_ann_proofs c r ltr bop eqv_s pf) = 
    @left_semiring_add_ann_certificate _ _ (P2C_left_semiring _ _ _ pf).
  Proof.
    unfold P2C_left_semiring;
    destruct pf, A_left_semiring_not_absorptive, x; simpl;
    f_equal.
  Defined.


End Certify.

Section Combinators. 
  
  Context 
    {L S : Type}
    (c : cas_constant).

  Lemma correct_slt_add_zero 
    (A : @A_slt L S) :
    A2C_slt (A_slt_add_zero A c) = 
    slt_add_zero (A2C_slt A) c.
  Proof.
    unfold A2C_slt, 
    slt_add_zero; cbn;
    destruct A; simpl;
    f_equal.
    + symmetry.
      apply correct_eqv_add_constant.
    + rewrite <-correct_sg_certs_add_id.
      f_equal.
    + rewrite correct_ltr_certs_add_ann.
      f_equal.
    + rewrite bop_add_id_exists_ann_check_correct.
      f_equal.
    + apply slt_add_ann_proof_correct.
  Defined.


  Lemma correct_slt_C_add_zero 
     (A : @A_slt_C L S) : 
     A2C_slt_c (A_slt_C_add_zero A c) =
     slt_C_add_zero (A2C_slt_c A) c.
  Proof.
    unfold A2C_slt_c, 
    slt_C_add_zero; cbn;
    destruct A; simpl;
    f_equal.
    + symmetry.
      apply correct_eqv_add_constant.
    + rewrite <-correct_sg_C_certs_add_id.
      f_equal.
    + rewrite correct_ltr_certs_add_ann.
      f_equal.
    + rewrite bop_add_id_exists_ann_check_correct.
      f_equal.
    + apply slt_add_ann_proof_correct.
  Defined.


  Lemma correct_slt_CS_add_zero 
     (A : @A_slt_CS L S) : 
     A2C_slt_cs (A_slt_CS_add_zero A c) =
     slt_CS_add_zero (A2C_slt_cs A) c.
  Proof.
    unfold A2C_slt_cs, 
    slt_CS_add_zero; cbn;
    destruct A; simpl;
    f_equal.
    + symmetry.
      apply correct_eqv_add_constant.
    + rewrite correct_ltr_certs_add_ann.
      f_equal.
    + rewrite bop_add_id_exists_ann_check_correct.
      f_equal.
    + apply slt_add_ann_proof_correct.
  Defined.


  Lemma correct_slt_CI_add_zero 
     (A : @A_slt_CI L S) : 
     A2C_slt_ci (A_slt_CI_add_zero A c) =
     slt_CI_add_zero (A2C_slt_ci A) c.
  Proof.
    unfold A2C_slt_ci, 
    slt_CI_add_zero; cbn;
    destruct A; simpl;
    f_equal.
    + symmetry.
      apply correct_eqv_add_constant.
    + rewrite <-correct_sg_CI_certs_add_id.
      f_equal.
    + rewrite correct_ltr_certs_add_ann.
      f_equal.
    + rewrite bop_add_id_exists_ann_check_correct.
      f_equal.
    + apply slt_add_ann_proof_correct.
  Defined.


  Lemma correct_slt_C_zero_is_ltr_ann_add_zero 
     (A : @A_slt_C_zero_is_ltr_ann L S) : 
     A2C_slt_C_zero_is_ltr_ann (A_slt_C_zero_is_ltr_ann_add_zero A c) =
     slt_C_zero_is_ltr_ann_add_zero (A2C_slt_C_zero_is_ltr_ann A) c.
  Proof.
    unfold A2C_slt_C_zero_is_ltr_ann, 
    slt_C_zero_is_ltr_ann_add_zero; cbn;
    destruct A; simpl;
    f_equal.
    + symmetry.
      apply correct_eqv_add_constant.
    + rewrite <-correct_sg_C_certs_add_id.
      f_equal.
    + rewrite correct_ltr_certs_add_ann.
      f_equal.
    + rewrite bop_add_id_exists_ann_check_correct.
      f_equal.
    + apply slt_add_ann_proof_correct.
  Defined.


  Lemma correct_selective_left_pre_dioid_add_zero 
     (A : @A_selective_left_pre_dioid L S) : 
     A2C_selective_left_pre_dioid (A_selective_left_pre_dioid_add_zero A c) =
     selective_left_pre_dioid_add_zero (A2C_selective_left_pre_dioid A) c.
  Proof.
    unfold A2C_selective_left_pre_dioid, 
    selective_left_pre_dioid_add_zero; cbn;
    destruct A; simpl;
    f_equal.
    + symmetry.
      apply correct_eqv_add_constant.
    + rewrite correct_ltr_certs_add_ann.
      f_equal.
    + unfold properties.p2c_exists_ann_assert. 
      destruct A_selective_left_pre_dioid_exists_plus_ann; simpl.
      reflexivity.  
    + apply left_dioid_add_ann_proof_correct.
  Defined.


  Lemma correct_selective_left_dioid_add_zero 
     (A : @A_selective_left_dioid L S) : 
     A2C_selective_left_dioid (A_selective_left_dioid_add_zero A c) =
     selective_left_dioid_add_zero (A2C_selective_left_dioid A) c.
  Proof.
    unfold A2C_selective_left_dioid, 
    selective_left_dioid_add_zero; cbn;
    destruct A; simpl;
    f_equal.
    + symmetry.
      apply correct_eqv_add_constant.
    + rewrite correct_ltr_certs_add_ann.
      f_equal.
    + unfold properties.p2c_exists_ann_assert. 
      destruct A_selective_left_dioid_exists_plus_ann; simpl.
      reflexivity.  
    + apply left_dioid_add_ann_proof_correct.
  Defined.


  Lemma correct_left_dioid_add_zero 
     (A : @A_left_dioid L S) : 
     A2C_left_dioid (A_left_dioid_add_zero A c) =
     left_dioid_add_zero (A2C_left_dioid A) c.
  Proof.
    unfold A2C_left_dioid, 
    left_dioid_add_zero; cbn;
    destruct A; simpl;
    f_equal.
    + symmetry.
      apply correct_eqv_add_constant.
    + rewrite <-correct_sg_CI_certs_add_id.
      f_equal.  
    + rewrite correct_ltr_certs_add_ann.
      f_equal.
    + unfold properties.p2c_exists_ann_assert. 
      destruct A_left_dioid_exists_plus_ann; simpl.
      reflexivity.  
    + apply left_dioid_add_ann_proof_correct.
  Defined.

  Lemma correct_left_pre_semiring_add_zero 
     (A : @A_left_pre_semiring L S) : 
     A2C_left_pre_semiring (A_left_pre_semiring_add_zero A c) =
     left_pre_semiring_add_zero (A2C_left_pre_semiring A) c.
  Proof.
    unfold A2C_left_pre_semiring,
    left_pre_semiring_add_zero; cbn;
    destruct A; cbn;
    f_equal.
    + symmetry.
      apply correct_eqv_add_constant.
    + rewrite <-correct_sg_C_certs_add_id.
      f_equal.  
    + rewrite correct_ltr_certs_add_ann.
      f_equal.
    + rewrite bop_add_id_exists_ann_check_correct.
      f_equal.  
    + apply left_semiring_add_ann_proof_correct.
  Defined.


   Lemma correct_left_semiring_add_zero 
     (A : @A_left_semiring L S) : 
     A2C_left_semiring (A_left_semiring_add_zero A c) =
     left_semiring_add_zero (A2C_left_semiring A) c.
  Proof.
    unfold A2C_left_semiring,
    left_semiring_add_zero; cbn;
    destruct A; cbn;
    f_equal.
    + symmetry.
      apply correct_eqv_add_constant.
    + rewrite <-correct_sg_C_certs_add_id.
      f_equal.  
    + rewrite correct_ltr_certs_add_ann.
      f_equal.
    + rewrite bop_add_id_exists_ann_check_correct.
      f_equal.  
    + apply left_semiring_add_ann_proof_correct.
  Defined.

  Lemma correct_left_idempotent_semiring_add_zero 
     (A : @A_left_idempotent_semiring L S) : 
     A2C_left_idempotent_semiring (A_left_idempotent_semiring_add_zero A c) =
     left_idempotent_semiring_add_zero (A2C_left_idempotent_semiring A) c.
  Proof.
    unfold A2C_left_idempotent_semiring,
    left_idempotent_semiring_add_zero; cbn;
    destruct A; cbn;
    f_equal.
    + symmetry.
      apply correct_eqv_add_constant.
    + rewrite <-correct_sg_CI_certs_add_id.
      f_equal.  
    + rewrite correct_ltr_certs_add_ann.
      f_equal.
    + rewrite bop_add_id_exists_ann_check_correct.
      f_equal.  
    + apply left_semiring_add_ann_proof_correct.
  Defined.


  Lemma correct_left_selective_semiring_add_zero 
     (A : @A_left_selective_semiring L S) : 
     A2C_left_selective_semiring (A_left_selective_semiring_add_zero A c) =
     left_selective_semiring_add_zero (A2C_left_selective_semiring A) c.
  Proof.
    unfold A2C_left_selective_semiring,
    left_selective_semiring_add_zero; cbn;
    destruct A; cbn;
    f_equal.
    + symmetry.
      apply correct_eqv_add_constant. 
    + rewrite correct_ltr_certs_add_ann.
      f_equal.
    + rewrite bop_add_id_exists_ann_check_correct.
      f_equal.  
    + apply left_semiring_add_ann_proof_correct.
  Defined.


End Combinators. 

  Lemma correct_mcas_slt_add_zero_aux 
    {L S : Type}
    (A : @A_slt_mcas L S) (c : cas_constant) :
    A2C_mcas_slt (A_mcas_slt_add_zero_aux A c) = 
    mcas_slt_add_zero_aux (A2C_mcas_slt A) c.
  Proof.
    destruct A; simpl.
    + reflexivity.
    + rewrite <-correct_slt_add_zero.
      reflexivity.
    + rewrite <-correct_slt_C_add_zero.
      reflexivity.
    + rewrite <-correct_slt_CS_add_zero.
      reflexivity.
    + rewrite <-correct_slt_CI_add_zero.
      reflexivity.
    + rewrite <-correct_slt_C_zero_is_ltr_ann_add_zero.
      reflexivity.
    + rewrite <-correct_left_dioid_add_zero.
      reflexivity.
    + rewrite <-correct_selective_left_pre_dioid_add_zero.
      reflexivity.
    + rewrite <-correct_selective_left_dioid_add_zero.
      reflexivity.
    + rewrite <-correct_left_pre_semiring_add_zero.
      reflexivity.
    + rewrite <-correct_left_semiring_add_zero.
      reflexivity.
    + rewrite <-correct_left_selective_semiring_add_zero.
      reflexivity.
    + rewrite <-correct_left_idempotent_semiring_add_zero.
      reflexivity.
  Qed.

  Lemma correct_mcas_slt_add_zero
    {L S : Type}
    (A : @A_slt_mcas L S) (c : cas_constant) :
    A2C_mcas_slt (A_mcas_slt_add_zero A c) = 
    mcas_slt_add_zero (A2C_mcas_slt A) c.
  Proof.
    unfold A_mcas_slt_add_zero,
    mcas_slt_add_zero.
    rewrite correctness_cast_slt_mcas_to_slt.
    destruct (cast_A_slt_mcas_to_A_slt A); 
    simpl; try reflexivity.
    rewrite <-correctness_slt_classify_slt.
    f_equal.
    rewrite correct_slt_add_zero.
    reflexivity.
  Qed.


End Verify.   


