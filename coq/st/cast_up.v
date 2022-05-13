Require Import Coq.Strings.String.
Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast. 
Require Import CAS.coq.eqv.structures. 
Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures. 
Require Import CAS.coq.tr.structures.
Require Import CAS.coq.st.structures.
Require Import CAS.coq.st.properties.
Require Import CAS.coq.sg.cast_up.




(*

1.                A_slt_proof
                     |
             ------------------------     
            |                       |
    A_slt_dioid_proof      A_slt_semiring_proof

 2.   
                  left_dioid
                     |
                  left_dioid
 3.                
              selective_left_dioid
                      |
              selective_left_dioid   
4.
              selective_left_pre_dioid
                      |
              selective_left_dioid
5.
              left_selective_semiring
                      |
              left_selective_semiring
6.
              left_idempotent_semiring
                      |
              left_idempotent_semiring
7.
              left_semiring
                  |
              left_semiring
8.
              left_pre_semiring
                  |
              left_semiring
9.                           
                       A_slt_CS 
                          | 
    ---------------------------------------------------------- 
                 |                              |            
    A_selective_left_pre_dioid        A_left_selective_semiring
10.
                        A_slt_CI
                          |
       -------------------------------------                
      |                             |                   
  left_dioid              left_idempotent_semiring    

11.

                A_slt_zero_is_ltr_ann
    --------------------------------------------------------------------
           |                      |              |                   |
    selective_left_dioid      left_dioid     left_semiring   left_idempotent_semiring

12.    

                        A_slt
                          | 
          ------------------------------------------
          |                |                 |    
      A_slt_CS    A_slt_zero_is_ltr_ann     A_slt_CI

*)  
Section Proofs.

  Context 
    {L S : Type}
    (r : brel S)
    (add : binary_op S)
    (ltr : ltr_type L S).

  Lemma semiring_not_strictly_absorptive :  
    left_semiring_proofs r add ltr -> 
    slt_strictly_absorptive_decidable r add ltr.
  Proof.
    intros [Al [(x, y) Hx]].
    right; econstructor.
    instantiate (1 := (x, y)).
    left; exact Hx.
  Defined. (* becuase we the structure of simplify *)


  Lemma A_selective_left_dioid_to_sg_proofs 
    (A : A_selective_left_dioid) :
    sg_proofs S
    (A_eqv_eq S (A_selective_left_dioid_carrier A))
    (@A_selective_left_dioid_plus L S A).
  Proof.
    destruct A, 
    A_selective_left_dioid_plus_proofs; simpl.
    econstructor; try assumption.
    left; exact A_sg_CS_commutative.
    left; exact A_sg_CS_selective.
  Admitted.
    




End Proofs.    


Section ACAS.
  
   
   
  
  Definition cast_slt_proof_to_slt_proof  {L S : Type} 
    (r : brel S) (add : binary_op S)
    (ltr : ltr_type L S) (A : slt_proofs r add ltr) :
    slt_proofs r add ltr := A. 


  Definition cast_left_dioid_proof_to_slt_proof {L S : Type} 
    (r : brel S) (add : binary_op S)
    (ltr : ltr_type L S)
    (A : left_dioid_proofs r add ltr) : slt_proofs r add ltr :=
    {|
        A_slt_distributive_d := inl (A_left_dioid_distributive r add ltr A)
      ; A_slt_absorptive_d := inl (A_left_dioid_absorptive r add ltr A)
      ; A_slt_strictly_absorptive_d := A_left_dioid_strictly_absorptive_d r add ltr A   
    |}.

  

  Definition cast_left_semiring_proof_to_slt_proof 
    {L S : Type} 
    (r : brel S) (add : binary_op S)
    (ltr : ltr_type L S)
    (A : left_semiring_proofs r add ltr) : slt_proofs r add ltr :=
    {|
        A_slt_distributive_d := inl (A_left_semiring_distributive r add ltr A)
      ; A_slt_absorptive_d := inr (A_left_semiring_not_absorptive r add ltr A) 
      ; A_slt_strictly_absorptive_d := 
          semiring_not_strictly_absorptive r add ltr A
    |}.

  
  Definition cast_A_left_dioid_to_A_left_dioid  {L S : Type} 
    (A : @A_left_dioid L S) : A_left_dioid := A.

  Definition cast_selective_left_dioid_to_selective_left_dioid 
    {L S : Type} (A : @A_selective_left_dioid L S) : 
    @A_selective_left_dioid L S := A.


    
  Definition cast_A_selective_left_dioid_to_A_selective_left_pre_dioid 
    {L S : Type} (A : @A_selective_left_dioid L S) : @A_selective_left_pre_dioid L S :=
    {|
      A_selective_left_pre_dioid_carrier := A_selective_left_dioid_carrier A 
    ; A_selective_left_pre_dioid_label := A_selective_left_dioid_label A 
    ; A_selective_left_pre_dioid_plus := A_selective_left_dioid_plus A                                            
    ; A_selective_left_pre_dioid_trans := A_selective_left_dioid_trans A 
    ; A_selective_left_pre_dioid_plus_proofs := A_selective_left_dioid_plus_proofs A
    ; A_selective_left_pre_dioid_trans_proofs := A_selective_left_dioid_trans_proofs A
    ; A_selective_left_pre_dioid_exists_plus_ann := A_selective_left_dioid_exists_plus_ann A                                
    ; A_selective_left_pre_dioid_id_ann_proofs_d := 
      SLT_Id_Ann_Proof_Equal _ _ _ (A_selective_left_dioid_id_ann_proofs A)                
    ; A_selective_left_pre_dioid_proofs := A_selective_left_dioid_proofs A                                
    ; A_selective_left_pre_dioid_ast := A_selective_left_dioid_ast A 
  |}.
  

  Definition cast_A_left_selective_semiring_to_A_left_selective_semiring
    {L S : Type}  (A : @A_left_selective_semiring L S : Type) : 
    @A_left_selective_semiring L S := A.

  
  Definition cast_A_left_idempotent_semiring_to_A_left_idempotent_semiring 
    {L S : Type}  (A : @A_left_idempotent_semiring L S) : 
    @A_left_idempotent_semiring L S := A.


  Definition cast_A_left_semiring_to_A_left_semiring 
    {L S : Type} (A : @A_left_semiring L S) : @A_left_semiring L S := A.


  Definition cast_A_left_semiring_to_A_left_pre_semiring
    {L S : Type} (A : @A_left_semiring L S) : @A_left_pre_semiring L S :=
    {|
      A_left_pre_semiring_carrier := A_left_semiring_carrier A 
    ; A_left_pre_semiring_label := A_left_semiring_label A
    ; A_left_pre_semiring_plus := A_left_semiring_plus A                                               
    ; A_left_pre_semiring_trans := A_left_semiring_trans A 
    ; A_left_pre_semiring_plus_proofs := A_left_semiring_plus_proofs A                                
    ; A_left_pre_semiring_trans_proofs := A_left_semiring_trans_proofs A 
    ; A_left_pre_semiring_exists_plus_ann_d := A_left_semiring_exists_plus_ann_d A                            
    ; A_left_pre_semiring_id_ann_proofs_d  :=
        SLT_Id_Ann_Proof_Equal _ _ _ (A_left_semiring_id_ann_proofs A)
    ; A_left_pre_semiring_proofs := A_left_semiring_proofs A 
    ; A_left_pre_semiring_ast  := A_left_semiring_ast A 
  |}.
  
  


  Definition cast_A_selective_left_pre_dioid_to_A_slt_CS 
    {L S : Type} (A : @A_selective_left_pre_dioid L S) : @A_slt_CS L S :=
    {|
        A_slt_CS_carrier  := A_selective_left_pre_dioid_carrier A 
      ; A_slt_CS_label := A_selective_left_pre_dioid_label A
      ; A_slt_CS_plus := A_selective_left_pre_dioid_plus A                                               
      ; A_slt_CS_trans := A_selective_left_pre_dioid_trans A 
      ; A_slt_CS_plus_proofs := A_selective_left_pre_dioid_plus_proofs A                        
      ; A_slt_CS_trans_proofs := A_selective_left_pre_dioid_trans_proofs A
      ; A_slt_CS_exists_plus_ann_d := inl (A_selective_left_pre_dioid_exists_plus_ann A)                                
      ; A_slt_CS_id_ann_proofs_d  := A_selective_left_pre_dioid_id_ann_proofs_d A                                         
      ; A_slt_CS_proofs := cast_left_dioid_proof_to_slt_proof 
          (A_eqv_eq S (A_selective_left_pre_dioid_carrier A))
          (A_selective_left_pre_dioid_plus A)
          (A_selective_left_pre_dioid_trans A) 
          (A_selective_left_pre_dioid_proofs A)                           
      ; A_slt_CS_ast := A_selective_left_pre_dioid_ast A
    |}.
 
  
  
    Definition cast_A_left_selective_semiring_to_A_slt_CS 
      {L S : Type} (A : @A_left_selective_semiring L S) : @A_slt_CS L S :=
      {|
          A_slt_CS_carrier  := A_left_selective_semiring_carrier A
        ; A_slt_CS_label := A_left_selective_semiring_label A 
        ; A_slt_CS_plus := A_left_selective_semiring_plus A                                              
        ; A_slt_CS_trans := A_left_selective_semiring_trans A 
        ; A_slt_CS_plus_proofs := A_left_selective_semiring_plus_proofs A                        
        ; A_slt_CS_trans_proofs := A_left_selective_semiring_trans_proofs A
        ; A_slt_CS_exists_plus_ann_d := A_left_selective_semiring_exists_plus_ann_d A                               
        ; A_slt_CS_id_ann_proofs_d  := 
            SLT_Id_Ann_Proof_Equal _ _ _ (A_left_selective_semiring_id_ann_proofs A)                                         
        ; A_slt_CS_proofs := cast_left_semiring_proof_to_slt_proof 
            (A_eqv_eq S (A_left_selective_semiring_carrier A))
            (A_left_selective_semiring_plus A)
            (A_left_selective_semiring_trans A) 
            (A_left_selective_semiring_proofs A)                           
        ; A_slt_CS_ast := A_left_selective_semiring_ast A
      |}.




    Definition cast_A_left_dioid_to_A_slt_CI 
      {L S : Type} (A : @A_left_dioid L S) : @A_slt_CI L S :=
      {|
          A_slt_CI_carrier  := A_left_dioid_carrier A
        ; A_slt_CI_label := A_left_dioid_label A 
        ; A_slt_CI_plus := A_left_dioid_plus A                                              
        ; A_slt_CI_trans := A_left_dioid_trans A
        ; A_slt_CI_plus_proofs  := A_left_dioid_plus_proofs A                       
        ; A_slt_CI_trans_proofs := A_left_dioid_trans_proofs A
        ; A_slt_CI_exists_plus_ann_d := inl (A_left_dioid_exists_plus_ann A)                               
        ; A_slt_CI_id_ann_proofs_d :=
            SLT_Id_Ann_Proof_Equal _ _ _ (A_left_dioid_id_ann_proofs A)                                         
        ; A_slt_CI_proofs := cast_left_dioid_proof_to_slt_proof 
            (A_eqv_eq S (A_left_dioid_carrier A))
            (A_left_dioid_plus A)
            (A_left_dioid_trans A) 
            (A_left_dioid_proofs A)                                   
        ; A_slt_CI_ast := A_left_dioid_ast A 
      |}. 
  

    Definition cast_A_left_idempotent_semiring_to_A_slt_CI 
      {L S : Type} (A : @A_left_idempotent_semiring L S) : @A_slt_CI L S :=
      {|
          A_slt_CI_carrier  := A_left_idempotent_semiring_carrier A
        ; A_slt_CI_label := A_left_idempotent_semiring_label A 
        ; A_slt_CI_plus := A_left_idempotent_semiring_plus A                                              
        ; A_slt_CI_trans := A_left_idempotent_semiring_trans A
        ; A_slt_CI_plus_proofs  := A_left_idempotent_semiring_plus_proofs A                       
        ; A_slt_CI_trans_proofs := A_left_idempotent_semiring_trans_proofs A
        ; A_slt_CI_exists_plus_ann_d := A_left_idempotent_semiring_exists_plus_ann_d A                              
        ; A_slt_CI_id_ann_proofs_d :=
            SLT_Id_Ann_Proof_Equal _ _ _ (A_left_idempotent_semiring_id_ann_proofs A)                                         
        ; A_slt_CI_proofs := cast_left_semiring_proof_to_slt_proof 
            (A_eqv_eq S (A_left_idempotent_semiring_carrier A))
            (A_left_idempotent_semiring_plus A)
            (A_left_idempotent_semiring_trans A) 
            (A_left_idempotent_semiring_proofs A)                                   
        ; A_slt_CI_ast := A_left_idempotent_semiring_ast A 
      |}. 
    


    Definition cast_A_selective_left_dioid_to_A_slt_zero_is_ltr_ann 
      {L S : Type} (s : S) (f : S -> S) (A : @A_selective_left_dioid L S)
      (H : properties.brel_not_trivial S (A_eqv_eq S (A_selective_left_dioid_carrier A)) f) : 
      @A_slt_zero_is_ltr_ann L S.
      refine  
      {|
          A_slt_zero_is_ltr_ann_carrier := A_selective_left_dioid_carrier A 
        ; A_slt_zero_is_ltr_ann_label := A_selective_left_dioid_label A
        ; A_slt_zero_is_ltr_ann_plus  := A_selective_left_dioid_plus A 
        ; A_slt_zero_is_ltr_ann_trans := A_selective_left_dioid_trans A 
        ; A_slt_zero_is_ltr_ann_plus_proofs  := _                            
        ; A_slt_zero_is_ltr_ann_trans_proofs := A_selective_left_dioid_trans_proofs A 
        ; A_slt_zero_is_ltr_ann_exists_plus_ann_d := inl (A_selective_left_dioid_exists_plus_ann A)                                
        ; A_slt_zero_is_ltr_ann_id_ann_proofs  := A_selective_left_dioid_id_ann_proofs A  
        ; A_slt_zero_is_ltr_ann_proofs :=  cast_left_dioid_proof_to_slt_proof 
          (A_eqv_eq S (A_selective_left_dioid_carrier A))
          (A_selective_left_dioid_plus A)
          (A_selective_left_dioid_trans A) 
          (A_selective_left_dioid_proofs A)                                  
        ; A_slt_zero_is_ltr_ann_ast := A_selective_left_dioid_ast A 
      |}.
      pose proof (A_sg_C_proofs_from_sg_CS_proofs 
        S (A_eqv_eq S (A_selective_left_dioid_carrier A))
        (A_selective_left_dioid_plus A)
        s f H (A_eqv_proofs S (A_selective_left_dioid_carrier A))
        (A_selective_left_dioid_plus_proofs A)) as sg_C_proof;
      exact (A_sg_proofs_from_sg_C_proofs 
        S (A_eqv_eq S (A_selective_left_dioid_carrier A))
        (A_selective_left_dioid_plus A)
        s f H (A_eqv_proofs S (A_selective_left_dioid_carrier A))
        sg_C_proof).
    Defined.

    
    
End ACAS.

