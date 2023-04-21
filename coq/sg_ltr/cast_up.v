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
From Coq Require Import List String.
Local Open Scope string_scope.
Import ListNotations.




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
    ------------------------------------------
        |                             |
  left_idempotent_semiring      left_selective_semiring


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

                A_slt_C_zero_is_ltr_ann
    ------------------------------------------------------
           |                      |              |        
    selective_left_dioid      left_dioid     left_semiring  

12.    

                        A_slt_C
                          | 
          --------------------------------------------------------------
          |                |                 |                  |
      A_slt_CS    A_slt_C_zero_is_ltr_ann     A_slt_CI     A_left_pre_semiring

13.
                        A_slt
                          |
                        A_slt_C


*)  
Section Proofs.

  Context 
    {L S : Type}
    (r : brel S)
    (b : binary_op S)
    (s : S)
    (f : S -> S)
    (Pf : properties.brel_not_trivial S r f)
    (eqvS : eqv_proofs S r)
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

 
  Lemma A_sg_CS_proofs_to_sg_proofs (A : sg_CS_proofs S r b) : sg_proofs S r b.
  Proof.
    pose proof (A_sg_C_proofs_from_sg_CS_proofs S r b s f Pf eqvS A) 
    as sg_C_proof.
    exact (A_sg_proofs_from_sg_C_proofs S r b s f Pf eqvS sg_C_proof).
  Defined.
    

  Lemma A_sg_CI_proofs_to_sg_proofs (A : sg_CI_proofs S r b) : sg_proofs S r b.
  Proof.
    pose proof (A_sg_C_proofs_from_sg_CI_proofs S r b s f Pf eqvS A) 
    as sg_C_proof.
    exact (A_sg_proofs_from_sg_C_proofs S r b s f Pf eqvS sg_C_proof).
  Defined.

  Lemma A_sg_C_proofs_to_sg_proofs (A : sg_C_proofs S r b) : sg_proofs S r b.
  Proof.
    exact (A_sg_proofs_from_sg_C_proofs S r b s f Pf eqvS A).
  Defined.

 
End Proofs.    


Section ACAS.
  

  Definition cast_slt_proofs_to_slt_proofs  {L S : Type} 
    (r : brel S) (add : binary_op S)
    (ltr : ltr_type L S) (A : slt_proofs r add ltr) :
    slt_proofs r add ltr := A. 


  Definition cast_left_dioid_proofs_to_slt_proofs {L S : Type} 
    (r : brel S) (add : binary_op S)
    (ltr : ltr_type L S)
    (A : left_dioid_proofs r add ltr) : slt_proofs r add ltr :=
    {|
        A_slt_distributive_d := inl (A_left_dioid_distributive r add ltr A)
      ; A_slt_absorptive_d := inl (A_left_dioid_absorptive r add ltr A)
      ; A_slt_strictly_absorptive_d := A_left_dioid_strictly_absorptive_d r add ltr A   
    |}.

  

  Definition cast_left_semiring_proofs_to_slt_proofs 
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

  Definition cast_A_selective_left_dioid_to_A_selective_left_dioid 
    {L S : Type} (A : @A_selective_left_dioid L S) : 
    @A_selective_left_dioid L S := A.


  Definition cast_A_selective_left_pre_dioid_to_A_selective_left_pre_dioid
    {L S : Type} (A : @A_selective_left_pre_dioid L S) :
    @A_selective_left_pre_dioid L S := A.
    

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

  
  Definition cast_A_left_idempotent_semiring_to_A_left_semiring 
    {L S : Type} (A : @A_left_idempotent_semiring L S) : 
    @A_left_semiring L S  :=
    {|
          A_left_semiring_carrier := A_left_idempotent_semiring_carrier A
        ; A_left_semiring_label := A_left_idempotent_semiring_label A
        ; A_left_semiring_plus  := A_left_idempotent_semiring_plus A                                            
        ; A_left_semiring_trans  :=  A_left_idempotent_semiring_trans A
        ; A_left_semiring_plus_proofs  :=  A_sg_C_proofs_from_sg_CI_proofs _  
            (A_eqv_eq S (A_left_idempotent_semiring_carrier A))
            (A_left_idempotent_semiring_plus A)
            (A_eqv_witness _ (A_left_idempotent_semiring_carrier A)) 
            (A_eqv_new _ (A_left_idempotent_semiring_carrier A)) 
            (A_eqv_not_trivial _ (A_left_idempotent_semiring_carrier A))
            (A_eqv_proofs _ (A_left_idempotent_semiring_carrier A))
            (A_left_idempotent_semiring_plus_proofs A)                            
        ; A_left_semiring_trans_proofs := A_left_idempotent_semiring_trans_proofs A
        ; A_left_semiring_exists_plus_ann_d := A_left_idempotent_semiring_exists_plus_ann_d A                              
        ; A_left_semiring_id_ann_proofs  := A_left_idempotent_semiring_id_ann_proofs A
        ; A_left_semiring_proofs  := A_left_idempotent_semiring_proofs A 
        ; A_left_semiring_ast  := A_left_idempotent_semiring_ast A
    |}.

   
  Definition cast_A_left_selective_semiring_to_A_left_semiring 
    {L S : Type} (A : @A_left_selective_semiring L S) : 
    @A_left_semiring L S :=
    {|
          A_left_semiring_carrier := A_left_selective_semiring_carrier A
        ; A_left_semiring_label := A_left_selective_semiring_label A
        ; A_left_semiring_plus  := A_left_selective_semiring_plus A                                            
        ; A_left_semiring_trans  :=  A_left_selective_semiring_trans A
        ; A_left_semiring_plus_proofs  :=  A_sg_C_proofs_from_sg_CS_proofs _  
            (A_eqv_eq S (A_left_selective_semiring_carrier A))
            (A_left_selective_semiring_plus A)
            (A_eqv_witness _ (A_left_selective_semiring_carrier A)) 
            (A_eqv_new _ (A_left_selective_semiring_carrier A)) 
            (A_eqv_not_trivial _ (A_left_selective_semiring_carrier A))
            (A_eqv_proofs _ (A_left_selective_semiring_carrier A))
            (A_left_selective_semiring_plus_proofs A)                            
        ; A_left_semiring_trans_proofs := A_left_selective_semiring_trans_proofs A
        ; A_left_semiring_exists_plus_ann_d := A_left_selective_semiring_exists_plus_ann_d A                              
        ; A_left_semiring_id_ann_proofs  := A_left_selective_semiring_id_ann_proofs A
        ; A_left_semiring_proofs  := A_left_selective_semiring_proofs A 
        ; A_left_semiring_ast  := A_left_selective_semiring_ast A
    |}.  
    


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

  

  Definition cast_A_left_pre_semiring_to_A_left_pre_semiring
    {L S : Type} (A : @A_left_pre_semiring L S) : 
    @A_left_pre_semiring L S := A.


    
  Definition cast_A_slt_CS_to_A_slt_CS {L S : Type} 
    (A : @A_slt_CS L S) : @A_slt_CS L S := A.


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
      ; A_slt_CS_proofs := cast_left_dioid_proofs_to_slt_proofs 
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
      ; A_slt_CS_proofs := cast_left_semiring_proofs_to_slt_proofs 
          (A_eqv_eq S (A_left_selective_semiring_carrier A))
          (A_left_selective_semiring_plus A)
          (A_left_selective_semiring_trans A) 
          (A_left_selective_semiring_proofs A)                           
      ; A_slt_CS_ast := A_left_selective_semiring_ast A
    |}.


  Definition cast_A_slt_CI_to_A_slt_CI {L S : Type} 
    (A : @A_slt_CI L S) : @A_slt_CI L S := A.

  Definition cast_A_left_dioid_to_A_slt_CI 
    {L S : Type} (A : @A_left_dioid L S) : @A_slt_CI L S :=
    {|
        A_slt_CI_carrier := A_left_dioid_carrier A
      ; A_slt_CI_label := A_left_dioid_label A 
      ; A_slt_CI_plus := A_left_dioid_plus A                                              
      ; A_slt_CI_trans := A_left_dioid_trans A
      ; A_slt_CI_plus_proofs  := A_left_dioid_plus_proofs A                       
      ; A_slt_CI_trans_proofs := A_left_dioid_trans_proofs A
      ; A_slt_CI_exists_plus_ann_d := inl (A_left_dioid_exists_plus_ann A)                               
      ; A_slt_CI_id_ann_proofs_d :=
          SLT_Id_Ann_Proof_Equal _ _ _ (A_left_dioid_id_ann_proofs A)                                         
      ; A_slt_CI_proofs := cast_left_dioid_proofs_to_slt_proofs 
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
      ; A_slt_CI_proofs := cast_left_semiring_proofs_to_slt_proofs 
          (A_eqv_eq S (A_left_idempotent_semiring_carrier A))
          (A_left_idempotent_semiring_plus A)
          (A_left_idempotent_semiring_trans A) 
          (A_left_idempotent_semiring_proofs A)                                   
      ; A_slt_CI_ast := A_left_idempotent_semiring_ast A 
    |}.
    
 

  Definition cast_A_selective_left_dioid_to_A_slt_C_zero_is_ltr_ann 
    {L S : Type} (A : @A_selective_left_dioid L S) :
    @A_slt_C_zero_is_ltr_ann L S :=
    {|
        A_slt_C_zero_is_ltr_ann_carrier := A_selective_left_dioid_carrier A 
      ; A_slt_C_zero_is_ltr_ann_label := A_selective_left_dioid_label A
      ; A_slt_C_zero_is_ltr_ann_plus  := A_selective_left_dioid_plus A 
      ; A_slt_C_zero_is_ltr_ann_trans := A_selective_left_dioid_trans A 
      ; A_slt_C_zero_is_ltr_ann_plus_proofs  :=  A_sg_C_proofs_from_sg_CS_proofs _ 
          (A_eqv_eq S (A_selective_left_dioid_carrier A))
          (A_selective_left_dioid_plus A)  
          (A_eqv_witness _ (A_selective_left_dioid_carrier A)) 
          (A_eqv_new _ (A_selective_left_dioid_carrier A)) 
          (A_eqv_not_trivial _ (A_selective_left_dioid_carrier A)) 
          (A_eqv_proofs _ (A_selective_left_dioid_carrier A))
          (A_selective_left_dioid_plus_proofs A)                 
      ; A_slt_C_zero_is_ltr_ann_trans_proofs := A_selective_left_dioid_trans_proofs A 
      ; A_slt_C_zero_is_ltr_ann_exists_plus_ann_d := inl (A_selective_left_dioid_exists_plus_ann A)                                
      ; A_slt_C_zero_is_ltr_ann_id_ann_proofs  := A_selective_left_dioid_id_ann_proofs A  
      ; A_slt_C_zero_is_ltr_ann_proofs :=  cast_left_dioid_proofs_to_slt_proofs 
        (A_eqv_eq S (A_selective_left_dioid_carrier A))
        (A_selective_left_dioid_plus A)
        (A_selective_left_dioid_trans A) 
        (A_selective_left_dioid_proofs A)                                  
      ; A_slt_C_zero_is_ltr_ann_ast := A_selective_left_dioid_ast A
    
    |}.



  Definition cast_A_left_dioid_to_A_slt_C_zero_is_ltr_ann   
    {L S : Type} (A : @A_left_dioid L S) : 
    @A_slt_C_zero_is_ltr_ann L S :=
    {|
        A_slt_C_zero_is_ltr_ann_carrier := A_left_dioid_carrier A 
      ; A_slt_C_zero_is_ltr_ann_label := A_left_dioid_label A
      ; A_slt_C_zero_is_ltr_ann_plus  := A_left_dioid_plus A 
      ; A_slt_C_zero_is_ltr_ann_trans := A_left_dioid_trans A 
      ; A_slt_C_zero_is_ltr_ann_plus_proofs  := A_sg_C_proofs_from_sg_CI_proofs _ 
        (A_eqv_eq S (A_left_dioid_carrier A))
        (A_left_dioid_plus A) 
        (A_eqv_witness _ (A_left_dioid_carrier A)) 
        (A_eqv_new _ (A_left_dioid_carrier A)) 
        (A_eqv_not_trivial _ (A_left_dioid_carrier A)) 
        (A_eqv_proofs _ (A_left_dioid_carrier A))
        (A_left_dioid_plus_proofs A)                              
      ; A_slt_C_zero_is_ltr_ann_trans_proofs := A_left_dioid_trans_proofs A 
      ; A_slt_C_zero_is_ltr_ann_exists_plus_ann_d := inl (A_left_dioid_exists_plus_ann A)                                
      ; A_slt_C_zero_is_ltr_ann_id_ann_proofs  := A_left_dioid_id_ann_proofs A  
      ; A_slt_C_zero_is_ltr_ann_proofs :=  cast_left_dioid_proofs_to_slt_proofs 
        (A_eqv_eq S (A_left_dioid_carrier A))
        (A_left_dioid_plus A)
        (A_left_dioid_trans A) 
        (A_left_dioid_proofs A)                                  
      ; A_slt_C_zero_is_ltr_ann_ast := A_left_dioid_ast A 
    |}.



  Definition cast_A_left_semiring_to_A_slt_C_zero_is_ltr_ann   
    {L S : Type} (A : @A_left_semiring L S) : 
    @A_slt_C_zero_is_ltr_ann L S :=
    {|
        A_slt_C_zero_is_ltr_ann_carrier := A_left_semiring_carrier A 
      ; A_slt_C_zero_is_ltr_ann_label := A_left_semiring_label A
      ; A_slt_C_zero_is_ltr_ann_plus  := A_left_semiring_plus A 
      ; A_slt_C_zero_is_ltr_ann_trans := A_left_semiring_trans A 
      ; A_slt_C_zero_is_ltr_ann_plus_proofs  := A_left_semiring_plus_proofs A        
      ; A_slt_C_zero_is_ltr_ann_trans_proofs := A_left_semiring_trans_proofs A 
      ; A_slt_C_zero_is_ltr_ann_exists_plus_ann_d := A_left_semiring_exists_plus_ann_d A                                 
      ; A_slt_C_zero_is_ltr_ann_id_ann_proofs  := A_left_semiring_id_ann_proofs A  
      ; A_slt_C_zero_is_ltr_ann_proofs :=  cast_left_semiring_proofs_to_slt_proofs 
        (A_eqv_eq S (A_left_semiring_carrier A))
        (A_left_semiring_plus A)
        (A_left_semiring_trans A) 
        (A_left_semiring_proofs A)                                  
      ; A_slt_C_zero_is_ltr_ann_ast := A_left_semiring_ast A 
    
    |}.
   
  
   


  Definition cast_A_slt_CS_to_A_slt_C {L S : Type} 
    (A : @A_slt_CS L S) : @A_slt_C L S :=
    {|
        A_slt_C_carrier := A_slt_CS_carrier A
      ; A_slt_C_label := A_slt_CS_label A
      ; A_slt_C_plus := A_slt_CS_plus A                                               
      ; A_slt_C_trans := A_slt_CS_trans A 
      ; A_slt_C_plus_proofs := A_sg_C_proofs_from_sg_CS_proofs _ 
          (A_eqv_eq S (A_slt_CS_carrier A))
          (A_slt_CS_plus A)
          (A_eqv_witness _ (A_slt_CS_carrier A)) 
          (A_eqv_new _ (A_slt_CS_carrier A)) 
          (A_eqv_not_trivial _ (A_slt_CS_carrier A))
          (A_eqv_proofs _ (A_slt_CS_carrier A))
          (A_slt_CS_plus_proofs A)                        
      ; A_slt_C_trans_proofs := A_slt_CS_trans_proofs A 
      ; A_slt_C_exists_plus_ann_d :=  A_slt_CS_exists_plus_ann_d A                                
      ; A_slt_C_id_ann_proofs_d  := A_slt_CS_id_ann_proofs_d A                                              
      ; A_slt_C_proofs := A_slt_CS_proofs A                                 
      ; A_slt_C_ast := A_slt_CS_ast A 
    
    |}.


   
  Definition cast_A_slt_C_zero_is_ltr_ann_to_A_slt_C 
    {L S : Type} 
    (A : @A_slt_C_zero_is_ltr_ann L S)  : @A_slt_C L S :=
    {|
        A_slt_C_carrier := A_slt_C_zero_is_ltr_ann_carrier A
      ; A_slt_C_label := A_slt_C_zero_is_ltr_ann_label A
      ; A_slt_C_plus := A_slt_C_zero_is_ltr_ann_plus A                                               
      ; A_slt_C_trans := A_slt_C_zero_is_ltr_ann_trans A 
      ; A_slt_C_plus_proofs := A_slt_C_zero_is_ltr_ann_plus_proofs A                       
      ; A_slt_C_trans_proofs := A_slt_C_zero_is_ltr_ann_trans_proofs A 
      ; A_slt_C_exists_plus_ann_d :=  A_slt_C_zero_is_ltr_ann_exists_plus_ann_d A                                
      ; A_slt_C_id_ann_proofs_d  := 
          SLT_Id_Ann_Proof_Equal _ _ _ (A_slt_C_zero_is_ltr_ann_id_ann_proofs A)
      ; A_slt_C_proofs := A_slt_C_zero_is_ltr_ann_proofs A                                 
      ; A_slt_C_ast := A_slt_C_zero_is_ltr_ann_ast A
    |}.


  Definition cast_A_slt_CI_to_A_slt_C {L S : Type} 
    (A : @A_slt_CI L S) : @A_slt_C L S :=
    {|
        A_slt_C_carrier := A_slt_CI_carrier A
      ; A_slt_C_label := A_slt_CI_label A
      ; A_slt_C_plus := A_slt_CI_plus A                                               
      ; A_slt_C_trans := A_slt_CI_trans A 
      ; A_slt_C_plus_proofs := A_sg_C_proofs_from_sg_CI_proofs _ 
          (A_eqv_eq S (A_slt_CI_carrier A))
          (A_slt_CI_plus A)
          (A_eqv_witness _ (A_slt_CI_carrier A)) 
          (A_eqv_new _ (A_slt_CI_carrier A)) 
          (A_eqv_not_trivial _ (A_slt_CI_carrier A))
          (A_eqv_proofs _ (A_slt_CI_carrier A))
          (A_slt_CI_plus_proofs A)                        
      ; A_slt_C_trans_proofs := A_slt_CI_trans_proofs A 
      ; A_slt_C_exists_plus_ann_d :=  A_slt_CI_exists_plus_ann_d A                                
      ; A_slt_C_id_ann_proofs_d  := A_slt_CI_id_ann_proofs_d A                                              
      ; A_slt_C_proofs := A_slt_CI_proofs A                                 
      ; A_slt_C_ast := A_slt_CI_ast A 
    
    |}.




  Definition cast_A_left_pre_semiring_to_A_slt_C 
    {L S : Type} (A : @A_left_pre_semiring L S) : 
    @A_slt_C L S :=
    {|
        A_slt_C_carrier := A_left_pre_semiring_carrier A
      ; A_slt_C_label := A_left_pre_semiring_label A
      ; A_slt_C_plus := A_left_pre_semiring_plus A                                               
      ; A_slt_C_trans := A_left_pre_semiring_trans A 
      ; A_slt_C_plus_proofs := A_left_pre_semiring_plus_proofs A                
      ; A_slt_C_trans_proofs := A_left_pre_semiring_trans_proofs A 
      ; A_slt_C_exists_plus_ann_d :=  A_left_pre_semiring_exists_plus_ann_d A                                
      ; A_slt_C_id_ann_proofs_d  := A_left_pre_semiring_id_ann_proofs_d A                                              
      ; A_slt_C_proofs := cast_left_semiring_proofs_to_slt_proofs 
        (A_eqv_eq S (A_left_pre_semiring_carrier A))
        (A_left_pre_semiring_plus A)
        (A_left_pre_semiring_trans A) 
        (A_left_pre_semiring_proofs A)                               
      ; A_slt_C_ast := A_left_pre_semiring_ast A 
    |}.



  Definition cast_A_slt_C_to_A_slt 
    {L S : Type} (A : @A_slt_C L S) : 
    @A_slt L S :=
    {|
          A_slt_carrier := A_slt_C_carrier A
        ; A_slt_label := A_slt_C_label A
        ; A_slt_plus := A_slt_C_plus A                                               
        ; A_slt_trans := A_slt_C_trans A 
        ; A_slt_plus_proofs := A_sg_C_proofs_to_sg_proofs 
            (A_eqv_eq S (A_slt_C_carrier A))
            (A_slt_C_plus A)
            (A_eqv_witness _ (A_slt_C_carrier A)) 
            (A_eqv_new _ (A_slt_C_carrier A)) 
            (A_eqv_not_trivial _ (A_slt_C_carrier A))
            (A_eqv_proofs _ (A_slt_C_carrier A))
            (A_slt_C_plus_proofs A)                        
        ; A_slt_trans_proofs := A_slt_C_trans_proofs A 
        ; A_slt_exists_plus_ann_d :=  A_slt_C_exists_plus_ann_d A                                
        ; A_slt_id_ann_proofs_d  := A_slt_C_id_ann_proofs_d A                                              
        ; A_slt_proofs := A_slt_C_proofs A                                 
        ; A_slt_ast := A_slt_C_ast A 
    |}.

  (* One layer finished. *)  


  


  (* start of multilayer fusion *)

  
  (* casting selective_left_dioid to all the way to the top*)

  Definition cast_A_selective_left_dioid_to_A_slt_CS 
    {L S : Type} (A : @A_selective_left_dioid L S) : @A_slt_CS L S :=
    let As :=  cast_A_selective_left_dioid_to_A_selective_left_pre_dioid A in 
    cast_A_selective_left_pre_dioid_to_A_slt_CS As. 


  Definition cast_A_selective_left_dioid_to_A_slt_C
    {L S : Type} 
    (A : @A_selective_left_dioid L S)  : @A_slt_C L S :=
    let As := @cast_A_selective_left_dioid_to_A_slt_CS L S A in 
    @cast_A_slt_CS_to_A_slt_C _ _ As.


  Definition cast_A_selective_left_dioid_to_A_slt
    {L S : Type} 
    (A : @A_selective_left_dioid L S)  : @A_slt L S :=
    let As := @cast_A_selective_left_dioid_to_A_slt_C L S A in 
    @cast_A_slt_C_to_A_slt _ _ As.

  (* end of casting selective_left_dioids *)
  
  (* start of selective_left_pre_dioid casting *)

  Definition cast_A_selective_left_pre_dioid_to_A_slt_C 
    {L S : Type} (A : @A_selective_left_pre_dioid L S) :
    @A_slt_C L S :=
    let As := cast_A_selective_left_pre_dioid_to_A_slt_CS A in 
    cast_A_slt_CS_to_A_slt_C As.

  Definition cast_A_selective_left_pre_dioid_to_A_slt  
    {L S : Type} (A : @A_selective_left_pre_dioid L S) :
    @A_slt L S :=
    let As := cast_A_selective_left_pre_dioid_to_A_slt_C A 
    in cast_A_slt_C_to_A_slt As.

  (* end of casting of A_selective_left_pre_dioid all the way to top*)

  (* start of casting of A_slt_cs to A_slt *)
  Definition cast_A_slt_CS_to_A_slt 
    {L S : Type} (A : @A_slt_CS L S) : A_slt :=
    let As := cast_A_slt_CS_to_A_slt_C A in 
    cast_A_slt_C_to_A_slt As.
  (* end of casting *)

  (* start of left_selective_semiring casting *)

  Definition cast_A_left_selective_semiring_to_A_slt_C 
    {L S : Type} (A : @A_left_selective_semiring L S) :
    @A_slt_C L S :=
    let As := cast_A_left_selective_semiring_to_A_slt_CS A in 
    cast_A_slt_CS_to_A_slt_C As.


  Definition cast_A_left_selective_semiring_to_A_slt 
    {L S : Type} (A : @A_left_selective_semiring L S) :
    @A_slt L S :=
    let As := cast_A_left_selective_semiring_to_A_slt_C A in 
    cast_A_slt_C_to_A_slt As.

  (* end of left selective semiring *)

  
  (* casting of left idempotent semiring *)

  Definition cast_A_left_idempotent_semiring_to_A_left_pre_semiring 
    {L S : Type} (A : @A_left_idempotent_semiring L S) :
    @A_left_pre_semiring L S :=
    let As := cast_A_left_idempotent_semiring_to_A_left_semiring A in 
    cast_A_left_semiring_to_A_left_pre_semiring As.

  Definition cast_A_left_idempotent_semiring_to_A_slt_C
    {L S : Type} (A : @A_left_idempotent_semiring L S) :
    @A_slt_C L S :=
    let As := cast_A_left_idempotent_semiring_to_A_left_pre_semiring A in 
    cast_A_left_pre_semiring_to_A_slt_C As.
    
  Definition cast_A_left_idempotent_semiring_to_A_slt
    {L S : Type} (A : @A_left_idempotent_semiring L S) :
    @A_slt L S :=
    let As := cast_A_left_idempotent_semiring_to_A_slt_C A in 
    cast_A_slt_C_to_A_slt As.

  (* end of casting left_idempotent semiring *)

  (* cast up left selective semiring  *)
  
  
  Definition cast_A_left_selective_semiring_to_A_left_pre_semiring 
    {L S : Type} (A : @A_left_selective_semiring L S) :
    @A_left_pre_semiring L S :=
    let As := cast_A_left_selective_semiring_to_A_left_semiring A in 
    cast_A_left_semiring_to_A_left_pre_semiring As.

  (* en dof casting left selective semiring *)

  (* cast up A_left_semiring *)

  Definition cast_A_left_semiring_to_A_slt_C 
    {L S : Type} (A : @A_left_semiring L S) :
    @A_slt_C L S :=
    let As := cast_A_left_semiring_to_A_left_pre_semiring A in 
    cast_A_left_pre_semiring_to_A_slt_C As.

  Definition cast_A_left_semiring_to_A_slt 
    {L S : Type} (A : @A_left_semiring L S) :
    @A_slt L S :=
    let As :=  cast_A_left_semiring_to_A_slt_C A in 
    cast_A_slt_C_to_A_slt As.

  (* end of casting left semiring *)

  (* start of casting up left pre semiring *)

  Definition cast_A_left_pre_semiring_to_A_slt 
    {L S : Type} (A : @A_left_pre_semiring L S) :
    @A_slt L S :=
    let As := cast_A_left_pre_semiring_to_A_slt_C A in 
    cast_A_slt_C_to_A_slt As.
  
  (* end of left pre semiring casting *)

  (* start of left dioid casting up *)

  Definition cast_A_left_dioid_to_A_slt_C
    {L S : Type} (A : @A_left_dioid L S) : @A_slt_C L S :=
    let As := cast_A_left_dioid_to_A_slt_CI A in
    cast_A_slt_CI_to_A_slt_C As.

  Definition cast_A_left_dioid_to_A_slt 
    {L S : Type} (A : @A_left_dioid L S) : 
    @A_slt L S :=
    let As := cast_A_left_dioid_to_A_slt_C A in 
    cast_A_slt_C_to_A_slt As.

  (* end of left of dioid *)

  Definition cast_A_left_idempotent_semiring_to_A_slt_C_zero_is_ltr_ann 
    {L S : Type} (A : @A_left_idempotent_semiring L S) :
    @A_slt_C_zero_is_ltr_ann L S :=
    let As := cast_A_left_idempotent_semiring_to_A_left_semiring A in 
    cast_A_left_semiring_to_A_slt_C_zero_is_ltr_ann As.

  Definition cast_A_left_selective_semiring_to_A_slt_C_zero_is_ltr_ann
    {L S : Type} (A : @A_left_selective_semiring L S) :
    @A_slt_C_zero_is_ltr_ann L S :=
    let As := cast_A_left_selective_semiring_to_A_left_semiring A in 
    cast_A_left_semiring_to_A_slt_C_zero_is_ltr_ann As.
 
  Definition cast_A_slt_CI_to_A_slt 
    {L S : Type} (A : @A_slt_CI L S) : A_slt :=
    let As := cast_A_slt_CI_to_A_slt_C A in 
    cast_A_slt_C_to_A_slt As.

  Definition cast_A_slt_C_zero_is_ltr_ann_to_A_slt 
    {L S : Type} (A : @A_slt_C_zero_is_ltr_ann L S) : A_slt :=
    let As := cast_A_slt_C_zero_is_ltr_ann_to_A_slt_C A in 
    cast_A_slt_C_to_A_slt As.

  




    
End ACAS.


Section AMCAS.

  

  (* A_selective_left_dioid is at bottom 
    structure and there is nothing below it. *)
  Definition  cast_A_slt_mcas_to_A_selective_left_dioid 
    {L S : Type} (A : @A_slt_mcas L S) : @A_slt_mcas L S  :=
    match A with
    | A_SLT_Error ls => A_SLT_Error ls 
    | A_SLT slt => 
        A_SLT_Error ["Can not cast up A_slt to A_selective_left_dioid"]
    | A_SLT_C slt =>
        A_SLT_Error ["Can not cast up A_slt_C to A_selective_left_dioid"]    
    | A_SLT_CS slt => 
        A_SLT_Error ["Can not cast up A_slt_CS to A_selective_left_dioid"]
    | A_SLT_CI slt => 
        A_SLT_Error ["Can not cast up A_slt_CI to A_selective_left_dioid"]
    | A_SLT_C_Zero_Is_Ltr_ann slt => 
        A_SLT_Error ["Can not cast up A_slt_C_zero_is_ltr_ann to A_selective_left_dioid"]
    | A_SLT_Left_Pre_Semiring slt => 
        A_SLT_Error ["Can not cast up A_left_pre_semiring to A_selective_left_dioid"]
    | A_SLT_Dioid slt =>
        A_SLT_Error ["Can not cast up A_left_dioid to A_selective_left_dioid"]
    | A_SLT_Selective_Left_Pre_Dioid slt => 
        A_SLT_Error ["Can not cast up A_selective_left_pre_dioid to A_selective_left_dioid"]
    | A_SLT_Semiring slt => 
        A_SLT_Error ["Can not cast up A_left_semiring to A_selective_left_dioid"]
    | A_SLT_Selective_Dioid slt => 
        A_SLT_Selective_Dioid (cast_A_selective_left_dioid_to_A_selective_left_dioid slt) (* identity function *)
    | A_SLT_Selective_Semiring slt => 
        A_SLT_Error ["Can not cast up A_left_selective_semiring to A_selective_left_dioid"]
    | A_SLT_Idempotent_Semiring slt => 
        A_SLT_Error ["Can not cast up A_left_idempotent_semiring to A_selective_left_dioid"]
    end.

  (* 
    selective_left_pre_dioid
          |
    selective_left_dioid
    The only structure below selective_left_pre_dioid is selective_left_dioid and 
    therefore we return values in these two cases and rest are errors.
  *)
  Definition cast_A_slt_mcas_to_A_selective_left_pre_dioid
    {L S : Type} (A : @A_slt_mcas L S) : @A_slt_mcas L S :=
    match A with 
    | A_SLT_Error ls => A_SLT_Error ls 
    | A_SLT slt => 
        A_SLT_Error ["Can not cast up A_slt to A_selective_left_pre_dioid"]
    | A_SLT_C slt => 
        A_SLT_Error ["Can not cast up A_slt_C to A_selective_left_pre_dioid"]
    | A_SLT_CS slt => 
        A_SLT_Error ["Can not cast up A_slt_CS to A_selective_left_pre_dioid"]
    | A_SLT_CI slt => 
        A_SLT_Error ["Can not cast up A_slt_CI to A_selective_left_pre_dioid"]
    | A_SLT_C_Zero_Is_Ltr_ann slt => 
        A_SLT_Error ["Can not cast up A_slt_zero_is_ltr_ann to A_selective_left_pre_dioid"]
    | A_SLT_Left_Pre_Semiring slt => 
        A_SLT_Error ["Can not cast up A_left_pre_semiring to A_selective_left_pre_dioid"]
    | A_SLT_Dioid slt =>
        A_SLT_Error ["Can not cast up A_left_dioid to A_selective_left_pre_dioid"]
    | A_SLT_Selective_Left_Pre_Dioid slt => 
        A_SLT_Selective_Left_Pre_Dioid 
          (cast_A_selective_left_pre_dioid_to_A_selective_left_pre_dioid slt)
    | A_SLT_Semiring slt => 
        A_SLT_Error ["Can not cast up A_left_semiring to A_selective_left_pre_dioid"]
    | A_SLT_Selective_Dioid slt => 
        A_SLT_Selective_Left_Pre_Dioid (cast_A_selective_left_dioid_to_A_selective_left_pre_dioid slt)
    | A_SLT_Selective_Semiring slt => 
        A_SLT_Error ["Can not cast up A_left_selective_semiring to A_selective_left_pre_dioid"]
    | A_SLT_Idempotent_Semiring slt => 
        A_SLT_Error ["Can not cast up A_left_idempotent_semiring to A_selective_left_pre_dioid"]
    end.
   
   
  (*
    There is nothing below left_selective_semiring, so
    all the returns values are errors, except the 
    left_selective_semiring
  
  *)
  Definition cast_A_slt_mcas_to_A_left_selective_semiring 
    {L S : Type} (A : @A_slt_mcas L S) : @A_slt_mcas L S :=
    match A with 
    | A_SLT_Error ls => A_SLT_Error ls 
    | A_SLT slt => 
        A_SLT_Error ["Can not cast up A_slt to A_left_selective_semiring"]
    | A_SLT_C slt =>
        A_SLT_Error ["Can not cast up A_SLT_C to A_left_selective_semiring"]
    | A_SLT_CS slt => 
        A_SLT_Error ["Can not cast up A_slt_CS to A_left_selective_semiring"]
    | A_SLT_CI slt => 
        A_SLT_Error ["Can not cast up A_slt_CI to A_left_selective_semiring"]
    | A_SLT_C_Zero_Is_Ltr_ann slt => 
        A_SLT_Error ["Can not cast up A_slt_C_zero_is_ltr_ann to A_left_selective_semiring"]
    | A_SLT_Left_Pre_Semiring slt => 
        A_SLT_Error ["Can not cast up A_left_pre_semiring to A_left_selective_semiring"]
    | A_SLT_Dioid slt =>
        A_SLT_Error ["Can not cast up A_left_dioid to A_left_selective_semiring"]
    | A_SLT_Selective_Left_Pre_Dioid slt => 
        A_SLT_Error ["Can not cast up a A_selective_left_pre_dioid to A_left_selective_semiring"]
    | A_SLT_Semiring slt => 
        A_SLT_Error ["Can not cast up A_left_semiring to A_left_selective_semiring"]
    | A_SLT_Selective_Dioid slt => 
        A_SLT_Error ["Can not cast up A_selective_left_dioid to A_left_selective_semiring"]
    | A_SLT_Selective_Semiring slt => 
        A_SLT_Selective_Semiring (cast_A_left_selective_semiring_to_A_left_selective_semiring slt)
    | A_SLT_Idempotent_Semiring slt => 
        A_SLT_Error ["Can not cast up A_left_idempotent_semiring A_left_selective_semiring"]
    end.


  (* all the previously defined structures can be cast up to A_SLT_CS *)

  Definition cast_A_slt_mcas_to_A_slt_CS 
    {L S : Type} (A : @A_slt_mcas L S) : @A_slt_mcas L S :=
    match A with
    | A_SLT_Error ls => A_SLT_Error ls 
    | A_SLT slt => 
        A_SLT_Error ["Can not cast up A_slt to A_slt_CS"]
    | A_SLT_C slt =>
        A_SLT_Error ["Can not cast up A_SLT_C to A_slt_CS"]
    | A_SLT_CS slt => A
    | A_SLT_CI slt => 
        A_SLT_Error ["Can not cast up A_slt_CI to A_slt_CS"]
    | A_SLT_C_Zero_Is_Ltr_ann slt => 
        A_SLT_Error ["Can not cast up A_slt_C_zero_is_ltr_ann to A_slt_CS"]
    | A_SLT_Left_Pre_Semiring slt => 
        A_SLT_Error ["Can not cast up A_left_pre_semiring to A_slt_CS"]
    | A_SLT_Dioid slt =>
        A_SLT_Error ["Can not cast up A_left_dioid to A_slt_CS"]
    | A_SLT_Selective_Left_Pre_Dioid slt => 
        A_SLT_CS (cast_A_selective_left_pre_dioid_to_A_slt_CS slt)  
    | A_SLT_Semiring slt => 
        A_SLT_Error ["Can not cast up A_left_semiring to A_slt_CS"]
    | A_SLT_Selective_Dioid slt => 
        A_SLT_CS (cast_A_selective_left_dioid_to_A_slt_CS slt)
    | A_SLT_Selective_Semiring slt => 
        A_SLT_CS (cast_A_left_selective_semiring_to_A_slt_CS slt)
    | A_SLT_Idempotent_Semiring slt => 
        A_SLT_Error ["Can not cast up A_left_idempotent_semiring A_left_selective_semiring"]
    end.
  (* end of cast up to A_SLT_CS *)  


  (*
     A_left_idempotent_semiring is a structure at the bottom,
     so all cases are error, except the  A_left_idempotent_semiring case itself
  *)
  Definition cast_A_slt_mcas_to_A_left_idempotent_semiring 
    {L S : Type} (A : @A_slt_mcas L S) : @A_slt_mcas L S :=
    match A with
    | A_SLT_Error ls => A_SLT_Error ls 
    | A_SLT slt => 
        A_SLT_Error ["Can not cast up A_slt to A_left_idempotent_semiring"]
    | A_SLT_C slt =>
        A_SLT_Error ["Can not cast up A_slt_C to A_left_idempotent_semiring"]    
    | A_SLT_CS slt => 
        A_SLT_Error ["Can not cast up A_slt_CS to A_left_idempotent_semiring"]
    | A_SLT_CI slt => 
        A_SLT_Error ["Can not cast up A_slt_CI to A_left_idempotent_semiring"]
    | A_SLT_C_Zero_Is_Ltr_ann slt => 
        A_SLT_Error ["Can not cast up A_slt_C_zero_is_ltr_ann to A_left_idempotent_semiring"]
    | A_SLT_Left_Pre_Semiring slt => 
        A_SLT_Error ["Can not cast up A_left_pre_semiring to A_left_idempotent_semiring"]
    | A_SLT_Dioid slt =>
        A_SLT_Error ["Can not cast up A_left_dioid to A_left_idempotent_semiring"]
    | A_SLT_Selective_Left_Pre_Dioid slt => 
        A_SLT_Error ["Can not cast up A_selective_left_pre_dioid to A_left_idempotent_semiring"]
    | A_SLT_Semiring slt => 
        A_SLT_Error ["Can not cast up A_left_semiring to A_left_idempotent_semiring"]
    | A_SLT_Selective_Dioid slt => 
        A_SLT_Error ["Can not cast up A_selective_left_dioid to A_left_idempotent_semiring"]
    | A_SLT_Selective_Semiring slt => 
        A_SLT_Error ["Can not cast up A_selective_semiring to A_left_idempotent_semiring"]
    | A_SLT_Idempotent_Semiring slt => 
        A_SLT_Idempotent_Semiring 
          (cast_A_left_idempotent_semiring_to_A_left_idempotent_semiring slt)
    end.

    

  (* 
            left semiring
              |
        --------------------
        |                   |
    left idempotent     left selective
       semiring             semiring
  
  *)
  Definition cast_A_slt_mcas_to_A_left_semiring 
    {L S : Type} (A : @A_slt_mcas L S) : @A_slt_mcas L S :=
    match A with
    | A_SLT_Error ls => A_SLT_Error ls 
    | A_SLT slt => 
        A_SLT_Error ["Can not cast up A_slt to A_left_semiring"]
    | A_SLT_C slt =>
        A_SLT_Error ["Can not cast up A_slt_C to A_left_semiring"]    
    | A_SLT_CS slt => 
        A_SLT_Error ["Can not cast up A_slt_CS to A_left_semiring"]
    | A_SLT_CI slt => 
        A_SLT_Error ["Can not cast up A_slt_CI to A_left_semiring"]
    | A_SLT_C_Zero_Is_Ltr_ann slt => 
        A_SLT_Error ["Can not cast up A_slt_C_zero_is_ltr_ann to A_left_semiring"]
    | A_SLT_Left_Pre_Semiring slt => 
        A_SLT_Error ["Can not cast up A_left_pre_semiring to A_left_semiring"]
    | A_SLT_Dioid slt =>
        A_SLT_Error ["Can not cast up A_left_dioid to A_left_semiring"]
    | A_SLT_Selective_Left_Pre_Dioid slt => 
        A_SLT_Error ["Can not cast up A_selective_left_pre_dioid to A_left_semiring"]
    | A_SLT_Semiring slt => 
        A_SLT_Semiring (cast_A_left_semiring_to_A_left_semiring slt)
    | A_SLT_Selective_Dioid slt => 
        A_SLT_Error ["Can not cast up A_selective_left_dioid to A_left_semiring"]
    | A_SLT_Selective_Semiring slt => 
        A_SLT_Semiring (cast_A_left_selective_semiring_to_A_left_semiring slt)
    | A_SLT_Idempotent_Semiring slt => 
        A_SLT_Semiring (cast_A_left_idempotent_semiring_to_A_left_semiring slt)
    end.


  

  Definition cast_A_slt_mcas_to_A_left_pre_semiring 
    {L S : Type} (A : @A_slt_mcas L S) : @A_slt_mcas L S :=
    match A with
    | A_SLT_Error ls => A_SLT_Error ls 
    | A_SLT slt => 
        A_SLT_Error ["Can not cast up A_slt to A_left_pre_semiring"]
    | A_SLT_C slt =>
        A_SLT_Error ["Can not cast up A_slt_C to A_left_pre_semiring"]    
    | A_SLT_CS slt => 
        A_SLT_Error ["Can not cast up A_slt_CS to A_left_pre_semiring"]
    | A_SLT_CI slt => 
        A_SLT_Error ["Can not cast up A_slt_CI to A_left_pre_semiring"]
    | A_SLT_C_Zero_Is_Ltr_ann slt => 
        A_SLT_Error ["Can not cast up A_slt_C_zero_is_ltr_ann to A_left_pre_semiring"]
    | A_SLT_Left_Pre_Semiring slt => A 
    | A_SLT_Dioid slt =>
        A_SLT_Error ["Can not cast up A_left_dioid to A_left_pre_semiring"]
    | A_SLT_Selective_Left_Pre_Dioid slt => 
        A_SLT_Error ["Can not cast up A_selective_left_pre_dioid to A_left_pre_semiring"]
    | A_SLT_Semiring slt => 
        A_SLT_Left_Pre_Semiring (cast_A_left_semiring_to_A_left_pre_semiring slt)
    | A_SLT_Selective_Dioid slt => 
        A_SLT_Error ["Can not cast up A_selective_left_dioid to A_left_pre_semiring"]
    | A_SLT_Selective_Semiring slt => 
        A_SLT_Left_Pre_Semiring (cast_A_left_selective_semiring_to_A_left_pre_semiring slt)
    | A_SLT_Idempotent_Semiring slt => 
        A_SLT_Left_Pre_Semiring (cast_A_left_idempotent_semiring_to_A_left_pre_semiring slt)
    end.  


  (* end of casting selective left pre semiring *)

  (* starting to A_slt_CI casting group *)

  Definition cast_A_slt_mcas_to_A_left_dioid 
    {L S : Type} (A : @A_slt_mcas L S) : @A_slt_mcas L S :=
    match A with
    | A_SLT_Error ls => A_SLT_Error ls 
    | A_SLT slt => 
        A_SLT_Error ["Can not cast up A_slt to A_left_dioid"]
    | A_SLT_C slt => A_SLT_Error ["Can not cast up A_slt to A_left_dioid"]    
    | A_SLT_CS slt => 
        A_SLT_Error ["Can not cast up A_slt_CS to A_left_dioid"]
    | A_SLT_CI slt => 
        A_SLT_Error ["Can not cast up A_slt_CI to A_left_dioid"]
    | A_SLT_C_Zero_Is_Ltr_ann slt => 
        A_SLT_Error ["Can not cast up A_slt_zero_is_ltr_ann to A_left_dioid"]
    | A_SLT_Left_Pre_Semiring slt => 
        A_SLT_Error ["Can not cast up A_left_pre_semiring to A_left_dioid"]
    | A_SLT_Dioid slt => 
        A_SLT_Dioid (cast_A_left_dioid_to_A_left_dioid slt) (* identity function *)
    | A_SLT_Selective_Left_Pre_Dioid slt => 
        A_SLT_Error ["Can not cast up A_selective_left_pre_dioid to A_left_dioid"]
    | A_SLT_Semiring slt => 
        A_SLT_Error ["Can not cast up A_left_semiring to A_left_dioid"]
    | A_SLT_Selective_Dioid slt => 
        A_SLT_Error ["Can not cast up A_selective_left_dioid to A_left_dioid"]
    | A_SLT_Selective_Semiring slt => 
        A_SLT_Error ["Can not cast up A_left_selective_semiring to A_left_dioid"]
    | A_SLT_Idempotent_Semiring slt => 
        A_SLT_Error ["Can not cast up A_left_idempotent_semiring to A_left_dioid"]
    end.


  Definition cast_A_slt_mcas_to_A_slt_CI {L S : Type}
    (A : @A_slt_mcas L S) : @A_slt_mcas L S  :=
    match A with
    | A_SLT_Error ls => A_SLT_Error ls 
    | A_SLT slt => 
        A_SLT_Error ["Can not cast up A_slt to A_SLT_CI"]
    | A_SLT_C slt => 
        A_SLT_Error ["Can not cast up A_slt_C to A_slt_CI"]       
    | A_SLT_CS slt => 
        A_SLT_Error ["Can not cast up A_slt_CS to A_SLT_CI"]
    | A_SLT_CI slt => 
        A_SLT_CI (cast_A_slt_CI_to_A_slt_CI slt)
    | A_SLT_C_Zero_Is_Ltr_ann slt => 
        A_SLT_Error ["Can not cast up A_slt_C_zero_is_ltr_ann to A_SLT_CI"]
    | A_SLT_Left_Pre_Semiring slt => 
        A_SLT_Error ["Can not cast up A_left_pre_semiring to A_SLT_CI"]
    | A_SLT_Dioid slt =>
        A_SLT_CI (cast_A_left_dioid_to_A_slt_CI  slt)
    | A_SLT_Selective_Left_Pre_Dioid slt => 
        A_SLT_Error ["Can not cast up A_selective_left_pre_dioid to A_SLT_CI"]
    | A_SLT_Semiring slt => 
        A_SLT_Error ["Can not cast up A_left_semiring to A_SLT_CI"]
    | A_SLT_Selective_Dioid slt => A_SLT_Error [""]
    | A_SLT_Selective_Semiring slt => 
        A_SLT_Error ["Can not cast up A_left_selective_semiring to A_SLT_CI"]
    | A_SLT_Idempotent_Semiring slt => 
        A_SLT_CI (cast_A_left_idempotent_semiring_to_A_slt_CI  slt)
    end.

  (* end of A_slt_CI casting *)  

  (* start of casting A_slt_C_zero *)


  Definition cast_A_slt_mcas_to_A_slt_C_zero_is_ltr_ann {L S : Type}
    (A : @A_slt_mcas L S) : @A_slt_mcas L S  :=
    match A with
    | A_SLT_Error ls => A_SLT_Error ls 
    | A_SLT slt => 
        A_SLT_Error ["Can not cast up A_slt to A_slt_C_zero_is_ltr_ann"]
    | A_SLT_C slt => 
        A_SLT_Error ["Can not cast up A_slt_C to A_slt_C_zero_is_ltr_ann"]       
    | A_SLT_CS slt => 
        A_SLT_Error ["Can not cast up A_slt_CS to A_slt_C_zero_is_ltr_ann"]
    | A_SLT_CI slt => 
        A_SLT_Error ["Can not cast up A_SLT_CI to A_slt_C_zero_is_ltr_ann"]
    | A_SLT_C_Zero_Is_Ltr_ann slt => A
    | A_SLT_Left_Pre_Semiring slt => 
        A_SLT_Error ["Can not cast up A_left_pre_semiring toA_slt_C_zero_is_ltr_ann"]
    | A_SLT_Dioid slt =>
        A_SLT_C_Zero_Is_Ltr_ann (cast_A_left_dioid_to_A_slt_C_zero_is_ltr_ann slt)
    | A_SLT_Selective_Left_Pre_Dioid slt => 
        A_SLT_Error ["Can not cast up A_selective_left_pre_dioid to A_SLT_CI"]
    | A_SLT_Semiring slt => 
        A_SLT_C_Zero_Is_Ltr_ann (cast_A_left_semiring_to_A_slt_C_zero_is_ltr_ann slt)
    | A_SLT_Selective_Dioid slt => 
        A_SLT_C_Zero_Is_Ltr_ann (cast_A_selective_left_dioid_to_A_slt_C_zero_is_ltr_ann slt)
    | A_SLT_Selective_Semiring slt => 
        A_SLT_C_Zero_Is_Ltr_ann  (cast_A_left_selective_semiring_to_A_slt_C_zero_is_ltr_ann slt)
    | A_SLT_Idempotent_Semiring slt => 
        A_SLT_C_Zero_Is_Ltr_ann  (cast_A_left_idempotent_semiring_to_A_slt_C_zero_is_ltr_ann slt)
    end.


  Definition cast_A_slt_mcas_to_A_slt_C 
    {L S : Type} (A : @A_slt_mcas L S) : @A_slt_mcas L S  :=
    match A with
    | A_SLT_Error ls => A_SLT_Error ls 
    | A_SLT slt => 
        A_SLT_Error ["Can not cast up A_slt to A_slt_C"]
    | A_SLT_C slt => A       
    | A_SLT_CS slt => 
        A_SLT_C (cast_A_slt_CS_to_A_slt_C slt)
    | A_SLT_CI slt => 
        A_SLT_C (cast_A_slt_CI_to_A_slt_C slt)
    | A_SLT_C_Zero_Is_Ltr_ann slt => 
        A_SLT_C (cast_A_slt_C_zero_is_ltr_ann_to_A_slt_C slt) 
    | A_SLT_Left_Pre_Semiring slt => 
        A_SLT_C (cast_A_left_pre_semiring_to_A_slt_C slt)
    | A_SLT_Dioid slt =>
        A_SLT_C (cast_A_left_dioid_to_A_slt_C slt)
    | A_SLT_Selective_Left_Pre_Dioid slt => 
        A_SLT_C (cast_A_selective_left_pre_dioid_to_A_slt_C slt)
    | A_SLT_Semiring slt => 
        A_SLT_C (cast_A_left_semiring_to_A_slt_C slt)
    | A_SLT_Selective_Dioid slt => 
        A_SLT_C (cast_A_selective_left_dioid_to_A_slt_C slt)
    | A_SLT_Selective_Semiring slt => 
        A_SLT_C (cast_A_left_selective_semiring_to_A_slt_C slt)
    | A_SLT_Idempotent_Semiring slt => 
        A_SLT_C (cast_A_left_idempotent_semiring_to_A_slt_C slt)
    end.
  

  Definition cast_A_slt_mcas_to_A_slt 
    {L S : Type} (A : @A_slt_mcas L S) : @A_slt_mcas L S  :=
    match A with
    | A_SLT_Error ls => A_SLT_Error ls 
    | A_SLT slt =>  A
    | A_SLT_C slt => 
        A_SLT (cast_A_slt_C_to_A_slt slt)       
    | A_SLT_CS slt => 
        A_SLT (cast_A_slt_CS_to_A_slt slt)
    | A_SLT_CI slt => 
        A_SLT (cast_A_slt_CI_to_A_slt slt)
    | A_SLT_C_Zero_Is_Ltr_ann slt => 
        A_SLT (cast_A_slt_C_zero_is_ltr_ann_to_A_slt slt) 
    | A_SLT_Left_Pre_Semiring slt => 
        A_SLT (cast_A_left_pre_semiring_to_A_slt slt)
    | A_SLT_Dioid slt =>
        A_SLT (cast_A_left_dioid_to_A_slt slt)
    | A_SLT_Selective_Left_Pre_Dioid slt => 
        A_SLT (cast_A_selective_left_pre_dioid_to_A_slt slt)
    | A_SLT_Semiring slt => 
        A_SLT (cast_A_left_semiring_to_A_slt slt)
    | A_SLT_Selective_Dioid slt => 
        A_SLT (cast_A_selective_left_dioid_to_A_slt slt)
    | A_SLT_Selective_Semiring slt => 
        A_SLT (cast_A_left_selective_semiring_to_A_slt slt)
    | A_SLT_Idempotent_Semiring slt => 
        A_SLT (cast_A_left_idempotent_semiring_to_A_slt slt)
    end.
   
  
End AMCAS.


Section Certs.

  Context 
    {L S : Type}
    (r : brel S)
    (b : binary_op S)
    (s : S)
    (f : S -> S).
  
  Lemma semiring_not_strictly_absorptive_cert :  
    @left_semiring_certificates L S -> 
    @check_slt_strictly_absorptive L S.
  Proof.
    intros [Al [p]].
    right. exact p.
  Defined. 

 
  Lemma sg_CS_certs_to_sg_certs (A : @sg_CS_certificates S) : @sg_certificates S.
  Proof.
    pose proof (sg_C_certs_from_sg_CS_certs S r b s f A) 
    as sg_C_cert;
    exact (sg_certs_from_sg_C_certs S r b s f sg_C_cert).
  Defined.
    

  Lemma sg_CI_certs_to_sg_certs (A : @sg_CI_certificates S) : @sg_certificates S.
  Proof.
    pose proof (sg_C_certs_from_sg_CI_certs S r b s f A) 
    as sg_C_cert;
    exact (sg_certs_from_sg_C_certs S r b s f sg_C_cert).
  Defined.

  Lemma sg_C_certs_to_sg_certs (A : @sg_C_certificates S) : @sg_certificates S.
  Proof.
    exact (sg_certs_from_sg_C_certs S r b s f A).
  Defined.
 
End Certs.    


Section CAS. 

  Definition cast_slt_certificates_to_slt_certificates  {L S : Type}
    (A : @slt_certificates L S) :
    slt_certificates := A. 


  Definition cast_left_dioid_certificates_to_slt_certificates {L S : Type} 
    (A : @left_dioid_certificates L S) : @slt_certificates L S :=
    {|
        slt_distributive_d := Certify_Slt_Distributive
      ; slt_absorptive_d := Certify_Slt_Absorptive
      ; slt_strictly_absorptive_d := left_dioid_strictly_absorptive_d A   
    |}.


  Definition cast_left_semiring_certificates_to_slt_certificates 
    {L S : Type}
    (A : @left_semiring_certificates L S) : @slt_certificates L S :=
    {|
        slt_distributive_d := Certify_Slt_Distributive
      ; slt_absorptive_d := Certify_Slt_Not_Absorptive 
          (match left_semiring_not_absorptive A with 
          | Assert_Slt_Not_Absorptive p => p
          end)
      ; slt_strictly_absorptive_d := 
          semiring_not_strictly_absorptive_cert A
    |}.

    
  Definition cast_left_dioid_to_left_dioid  {L S : Type} 
    (A : @left_dioid L S) : left_dioid := A.

  Definition cast_selective_left_dioid_to_selective_left_dioid 
    {L S : Type} (A : @selective_left_dioid L S) : 
    @selective_left_dioid L S := A.


  Definition cast_selective_left_pre_dioid_to_selective_left_pre_dioid
    {L S : Type} (A : @selective_left_pre_dioid L S) :
    @selective_left_pre_dioid L S := A.

  Definition cast_selective_left_dioid_to_selective_left_pre_dioid 
    {L S : Type} (A : @selective_left_dioid L S) : @selective_left_pre_dioid L S :=
    {|
      selective_left_pre_dioid_carrier := selective_left_dioid_carrier A 
    ; selective_left_pre_dioid_label := selective_left_dioid_label A 
    ; selective_left_pre_dioid_plus := selective_left_dioid_plus A
    ; selective_left_pre_dioid_trans := selective_left_dioid_trans A 
    ; selective_left_pre_dioid_plus_certs := selective_left_dioid_plus_certs A
    ; selective_left_pre_dioid_trans_certs := selective_left_dioid_trans_certs A
    ; selective_left_pre_dioid_exists_plus_ann := selective_left_dioid_exists_plus_ann A
    ; selective_left_pre_dioid_id_ann_certs_d := 
      Certify_SLT_Id_Ann_Proof_Equal 
        (match selective_left_dioid_id_ann_certs A with
        | Assert_Slt_Exists_Id_Ann_Equal s => s 
        end)             
    ; selective_left_pre_dioid_certs := selective_left_dioid_certs A
    ; selective_left_pre_dioid_ast := selective_left_dioid_ast A 
  |}.



  Definition cast_left_selective_semiring_to_left_selective_semiring
    {L S : Type}  (A : @left_selective_semiring L S) : 
    @left_selective_semiring L S := A.

  
  Definition cast_left_idempotent_semiring_to_left_idempotent_semiring 
    {L S : Type}  (A : @left_idempotent_semiring L S) : 
    @left_idempotent_semiring L S := A.


  Definition cast_left_semiring_to_left_semiring 
    {L S : Type} (A : @left_semiring L S) : 
    @left_semiring L S := A.

 

 
  Definition cast_left_idempotent_semiring_to_left_semiring 
    {L S : Type} (A : @left_idempotent_semiring L S) : 
    @left_semiring L S := 
    {|
          left_semiring_carrier := left_idempotent_semiring_carrier A
        ; left_semiring_label := left_idempotent_semiring_label A
        ; left_semiring_plus  := left_idempotent_semiring_plus A                                            
        ; left_semiring_trans  :=  left_idempotent_semiring_trans A
        ; left_semiring_plus_certs  := sg_C_certs_from_sg_CI_certs _  
            (eqv_eq (left_idempotent_semiring_carrier A))
            (left_idempotent_semiring_plus A)
            (eqv_witness (left_idempotent_semiring_carrier A)) 
            (eqv_new (left_idempotent_semiring_carrier A)) 
            (left_idempotent_semiring_plus_certs A)                            
        ; left_semiring_trans_certs := left_idempotent_semiring_trans_certs A
        ; left_semiring_exists_plus_ann_d := left_idempotent_semiring_exists_plus_ann_d A                              
        ; left_semiring_id_ann_certs  := left_idempotent_semiring_id_ann_certs A
        ; left_semiring_certs  := left_idempotent_semiring_certs A 
        ; left_semiring_ast  := left_idempotent_semiring_ast A
    |}.


    Definition cast_left_selective_semiring_to_left_semiring 
      {L S : Type} (A : @left_selective_semiring L S) : 
      @left_semiring L S :=
      {|
            left_semiring_carrier := left_selective_semiring_carrier A
          ; left_semiring_label := left_selective_semiring_label A
          ; left_semiring_plus  := left_selective_semiring_plus A                                            
          ; left_semiring_trans  :=  left_selective_semiring_trans A
          ; left_semiring_plus_certs  :=  sg_C_certs_from_sg_CS_certs _  
              (eqv_eq (left_selective_semiring_carrier A))
              (left_selective_semiring_plus A)
              (eqv_witness (left_selective_semiring_carrier A)) 
              (eqv_new (left_selective_semiring_carrier A))
              (left_selective_semiring_plus_certs A)                            
          ; left_semiring_trans_certs := left_selective_semiring_trans_certs A
          ; left_semiring_exists_plus_ann_d := left_selective_semiring_exists_plus_ann_d A                              
          ; left_semiring_id_ann_certs  := left_selective_semiring_id_ann_certs A
          ; left_semiring_certs  := left_selective_semiring_certs A 
          ; left_semiring_ast  := left_selective_semiring_ast A
      |}.  



  Definition cast_left_semiring_to_left_pre_semiring
    {L S : Type} (A : @left_semiring L S) : 
    @left_pre_semiring L S :=
    {|
        left_pre_semiring_carrier := left_semiring_carrier A 
      ; left_pre_semiring_label := left_semiring_label A
      ; left_pre_semiring_plus := left_semiring_plus A                                               
      ; left_pre_semiring_trans := left_semiring_trans A 
      ; left_pre_semiring_plus_certs := left_semiring_plus_certs A                                
      ; left_pre_semiring_trans_certs := left_semiring_trans_certs A 
      ; left_pre_semiring_exists_plus_ann_d := left_semiring_exists_plus_ann_d A                            
      ; left_pre_semiring_id_ann_certs_d  :=
          Certify_SLT_Id_Ann_Proof_Equal 
            (match left_semiring_id_ann_certs A with
            | Assert_Slt_Exists_Id_Ann_Equal s => s 
            end)
      ; left_pre_semiring_certs := left_semiring_certs A 
      ; left_pre_semiring_ast  := left_semiring_ast A 
    |}.
    
    
  Definition cast_left_pre_semiring_to_left_pre_semiring
    {L S : Type} (A : @left_pre_semiring L S) : 
    @left_pre_semiring L S := A.


  Definition cast_slt_CS_to_slt_CS {L S : Type} 
    (A : @slt_CS L S) : @slt_CS L S := A.


  Definition cast_selective_left_pre_dioid_to_slt_CS 
    {L S : Type} (A : @selective_left_pre_dioid L S) : @slt_CS L S :=
    {|
        slt_CS_carrier  := selective_left_pre_dioid_carrier A 
      ; slt_CS_label := selective_left_pre_dioid_label A
      ; slt_CS_plus := selective_left_pre_dioid_plus A                                               
      ; slt_CS_trans := selective_left_pre_dioid_trans A 
      ; slt_CS_plus_certs := selective_left_pre_dioid_plus_certs A                        
      ; slt_CS_trans_certs := selective_left_pre_dioid_trans_certs A
      ; slt_CS_exists_plus_ann_d := Certify_Exists_Ann 
          (match  selective_left_pre_dioid_exists_plus_ann A with 
            | Assert_Exists_Ann s => s
            end)                             
      ; slt_CS_id_ann_certs_d  := selective_left_pre_dioid_id_ann_certs_d A                                         
      ; slt_CS_certs := cast_left_dioid_certificates_to_slt_certificates 
          (selective_left_pre_dioid_certs A)                           
      ; slt_CS_ast := selective_left_pre_dioid_ast A
    |}.
  

  Definition cast_left_selective_semiring_to_slt_CS 
    {L S : Type} (A : @left_selective_semiring L S) : @slt_CS L S :=
    {|
        slt_CS_carrier  := left_selective_semiring_carrier A
      ; slt_CS_label := left_selective_semiring_label A 
      ; slt_CS_plus := left_selective_semiring_plus A                                              
      ; slt_CS_trans := left_selective_semiring_trans A 
      ; slt_CS_plus_certs := left_selective_semiring_plus_certs A                        
      ; slt_CS_trans_certs := left_selective_semiring_trans_certs A
      ; slt_CS_exists_plus_ann_d := left_selective_semiring_exists_plus_ann_d A                               
      ; slt_CS_id_ann_certs_d  :=  Certify_SLT_Id_Ann_Proof_Equal 
          (match left_selective_semiring_id_ann_certs A with
          | Assert_Slt_Exists_Id_Ann_Equal s => s 
          end)                                
      ; slt_CS_certs := cast_left_semiring_certificates_to_slt_certificates
          (left_selective_semiring_certs A)                           
      ; slt_CS_ast := left_selective_semiring_ast A
    |}.  


  Definition cast_slt_CI_to_slt_CI {L S : Type} 
    (A : @slt_CI L S) : @slt_CI L S := A.


  Definition cast_left_dioid_to_slt_CI 
    {L S : Type} (A : @left_dioid L S) : @slt_CI L S :=
    {|
        slt_CI_carrier := left_dioid_carrier A
      ; slt_CI_label := left_dioid_label A 
      ; slt_CI_plus := left_dioid_plus A                                              
      ; slt_CI_trans := left_dioid_trans A
      ; slt_CI_plus_certs  := left_dioid_plus_certs A                       
      ; slt_CI_trans_certs := left_dioid_trans_certs A
      ; slt_CI_exists_plus_ann_d := Certify_Exists_Ann 
          (match left_dioid_exists_plus_ann A with 
            | Assert_Exists_Ann s => s
            end)                                                     
      ; slt_CI_id_ann_certs_d :=
        Certify_SLT_Id_Ann_Proof_Equal 
          (match left_dioid_id_ann_certs A with
          | Assert_Slt_Exists_Id_Ann_Equal s => s 
          end)                                         
      ; slt_CI_certs:= cast_left_dioid_certificates_to_slt_certificates  
          (left_dioid_certs A)                                   
      ; slt_CI_ast := left_dioid_ast A 
    |}.


  Definition cast_left_idempotent_semiring_to_slt_CI 
    {L S : Type} (A : @left_idempotent_semiring L S) : @slt_CI L S :=
    {|
        slt_CI_carrier  := left_idempotent_semiring_carrier A
      ; slt_CI_label := left_idempotent_semiring_label A 
      ; slt_CI_plus := left_idempotent_semiring_plus A                                              
      ; slt_CI_trans := left_idempotent_semiring_trans A
      ; slt_CI_plus_certs  := left_idempotent_semiring_plus_certs A                       
      ; slt_CI_trans_certs := left_idempotent_semiring_trans_certs A
      ; slt_CI_exists_plus_ann_d := left_idempotent_semiring_exists_plus_ann_d A                              
      ; slt_CI_id_ann_certs_d :=
          Certify_SLT_Id_Ann_Proof_Equal 
            (match left_idempotent_semiring_id_ann_certs A with
            | Assert_Slt_Exists_Id_Ann_Equal s => s 
            end)                    
      ; slt_CI_certs := cast_left_semiring_certificates_to_slt_certificates 
          (left_idempotent_semiring_certs A)                                   
      ; slt_CI_ast := left_idempotent_semiring_ast A 
    |}.
    
    

  Definition cast_selective_left_dioid_to_slt_C_zero_is_ltr_ann 
    {L S : Type} (A : @selective_left_dioid L S) :
    @slt_C_zero_is_ltr_ann L S :=
    {|
        slt_C_zero_is_ltr_ann_carrier := selective_left_dioid_carrier A 
      ; slt_C_zero_is_ltr_ann_label := selective_left_dioid_label A
      ; slt_C_zero_is_ltr_ann_plus  := selective_left_dioid_plus A 
      ; slt_C_zero_is_ltr_ann_trans := selective_left_dioid_trans A 
      ; slt_C_zero_is_ltr_ann_plus_certs  :=  sg_C_certs_from_sg_CS_certs _ 
          (eqv_eq (selective_left_dioid_carrier A))
          (selective_left_dioid_plus A)  
          (eqv_witness (selective_left_dioid_carrier A)) 
          (eqv_new (selective_left_dioid_carrier A)) 
          (selective_left_dioid_plus_certs A)                 
      ; slt_C_zero_is_ltr_ann_trans_certs := selective_left_dioid_trans_certs A 
      ; slt_C_zero_is_ltr_ann_exists_plus_ann_d := Certify_Exists_Ann 
          (match selective_left_dioid_exists_plus_ann A with 
          | Assert_Exists_Ann s => s
          end)                             
      ; slt_C_zero_is_ltr_ann_id_ann_certs  := selective_left_dioid_id_ann_certs A  
      ; slt_C_zero_is_ltr_ann_certs :=  cast_left_dioid_certificates_to_slt_certificates
        (selective_left_dioid_certs A)                                  
      ; slt_C_zero_is_ltr_ann_ast := selective_left_dioid_ast A
    |}.   

  
  Definition cast_left_dioid_to_slt_C_zero_is_ltr_ann   
    {L S : Type} (A : @left_dioid L S) : 
    @slt_C_zero_is_ltr_ann L S :=
    {|
        slt_C_zero_is_ltr_ann_carrier := left_dioid_carrier A 
      ; slt_C_zero_is_ltr_ann_label := left_dioid_label A
      ; slt_C_zero_is_ltr_ann_plus  := left_dioid_plus A 
      ; slt_C_zero_is_ltr_ann_trans := left_dioid_trans A 
      ; slt_C_zero_is_ltr_ann_plus_certs  := sg_C_certs_from_sg_CI_certs _ 
        (eqv_eq (left_dioid_carrier A))
        (left_dioid_plus A) 
        (eqv_witness (left_dioid_carrier A)) 
        (eqv_new (left_dioid_carrier A))
        (left_dioid_plus_certs A)                              
      ; slt_C_zero_is_ltr_ann_trans_certs := left_dioid_trans_certs A 
      ; slt_C_zero_is_ltr_ann_exists_plus_ann_d := Certify_Exists_Ann 
          (match left_dioid_exists_plus_ann A with 
          | Assert_Exists_Ann s => s
          end)                                                      
      ; slt_C_zero_is_ltr_ann_id_ann_certs  := left_dioid_id_ann_certs A  
      ; slt_C_zero_is_ltr_ann_certs :=  cast_left_dioid_certificates_to_slt_certificates
        (left_dioid_certs A)                                  
      ; slt_C_zero_is_ltr_ann_ast := left_dioid_ast A 
    |}.
    
  Definition cast_left_semiring_to_slt_C_zero_is_ltr_ann   
    {L S : Type} (A : @left_semiring L S) : 
    @slt_C_zero_is_ltr_ann L S :=
    {|
        slt_C_zero_is_ltr_ann_carrier := left_semiring_carrier A 
      ; slt_C_zero_is_ltr_ann_label := left_semiring_label A
      ; slt_C_zero_is_ltr_ann_plus  := left_semiring_plus A 
      ; slt_C_zero_is_ltr_ann_trans := left_semiring_trans A 
      ; slt_C_zero_is_ltr_ann_plus_certs  := left_semiring_plus_certs A        
      ; slt_C_zero_is_ltr_ann_trans_certs := left_semiring_trans_certs A 
      ; slt_C_zero_is_ltr_ann_exists_plus_ann_d := left_semiring_exists_plus_ann_d A                                 
      ; slt_C_zero_is_ltr_ann_id_ann_certs  := left_semiring_id_ann_certs A  
      ; slt_C_zero_is_ltr_ann_certs :=  cast_left_semiring_certificates_to_slt_certificates
        (left_semiring_certs A)                                  
      ; slt_C_zero_is_ltr_ann_ast := left_semiring_ast A
    |}.

  Definition cast_slt_CS_to_slt_C {L S : Type} 
    (A : @slt_CS L S) : @slt_C L S :=
    {|
        slt_C_carrier := slt_CS_carrier A
      ; slt_C_label := slt_CS_label A
      ; slt_C_plus := slt_CS_plus A                                               
      ; slt_C_trans := slt_CS_trans A 
      ; slt_C_plus_certs := sg_C_certs_from_sg_CS_certs _ 
          (eqv_eq (slt_CS_carrier A))
          (slt_CS_plus A)
          (eqv_witness (slt_CS_carrier A)) 
          (eqv_new (slt_CS_carrier A))
          (slt_CS_plus_certs A)                        
      ; slt_C_trans_certs := slt_CS_trans_certs A 
      ; slt_C_exists_plus_ann_d :=  slt_CS_exists_plus_ann_d A                                
      ; slt_C_id_ann_certs_d  := slt_CS_id_ann_certs_d A                                              
      ; slt_C_certs := slt_CS_certs A                                 
      ; slt_C_ast := slt_CS_ast A 
    
    |}.


  Definition cast_slt_C_zero_is_ltr_ann_to_slt_C 
    {L S : Type} 
    (A : @slt_C_zero_is_ltr_ann L S)  : @slt_C L S :=
    {|
        slt_C_carrier := slt_C_zero_is_ltr_ann_carrier A
      ; slt_C_label := slt_C_zero_is_ltr_ann_label A
      ; slt_C_plus := slt_C_zero_is_ltr_ann_plus A                                               
      ; slt_C_trans := slt_C_zero_is_ltr_ann_trans A 
      ; slt_C_plus_certs := slt_C_zero_is_ltr_ann_plus_certs A                       
      ; slt_C_trans_certs := slt_C_zero_is_ltr_ann_trans_certs A 
      ; slt_C_exists_plus_ann_d :=  slt_C_zero_is_ltr_ann_exists_plus_ann_d A                                
      ; slt_C_id_ann_certs_d  := Certify_SLT_Id_Ann_Proof_Equal 
      (match slt_C_zero_is_ltr_ann_id_ann_certs A with
      | Assert_Slt_Exists_Id_Ann_Equal s => s 
      end)                     
      ; slt_C_certs := slt_C_zero_is_ltr_ann_certs A                                 
      ; slt_C_ast := slt_C_zero_is_ltr_ann_ast A
    |}.
   

  Definition cast_slt_CI_to_slt_C {L S : Type} 
    (A : @slt_CI L S) : @slt_C L S :=
    {|
        slt_C_carrier := slt_CI_carrier A
      ; slt_C_label := slt_CI_label A
      ; slt_C_plus := slt_CI_plus A                                               
      ; slt_C_trans := slt_CI_trans A 
      ; slt_C_plus_certs := sg_C_certs_from_sg_CI_certs _ 
          (eqv_eq (slt_CI_carrier A))
          (slt_CI_plus A)
          (eqv_witness (slt_CI_carrier A)) 
          (eqv_new (slt_CI_carrier A))
          (slt_CI_plus_certs A)                        
      ; slt_C_trans_certs := slt_CI_trans_certs A 
      ; slt_C_exists_plus_ann_d :=  slt_CI_exists_plus_ann_d A                                
      ; slt_C_id_ann_certs_d  := slt_CI_id_ann_certs_d A                                              
      ; slt_C_certs := slt_CI_certs A                                 
      ; slt_C_ast := slt_CI_ast A 
    
    |}.
    
    

  Definition cast_left_pre_semiring_to_slt_C 
    {L S : Type} (A : @left_pre_semiring L S) : 
    @slt_C L S :=
    {|
        slt_C_carrier := left_pre_semiring_carrier A
      ; slt_C_label := left_pre_semiring_label A
      ; slt_C_plus := left_pre_semiring_plus A                                               
      ; slt_C_trans := left_pre_semiring_trans A 
      ; slt_C_plus_certs := left_pre_semiring_plus_certs A                
      ; slt_C_trans_certs := left_pre_semiring_trans_certs A 
      ; slt_C_exists_plus_ann_d :=  left_pre_semiring_exists_plus_ann_d A                                
      ; slt_C_id_ann_certs_d  := left_pre_semiring_id_ann_certs_d A                                              
      ; slt_C_certs := cast_left_semiring_certificates_to_slt_certificates
        (left_pre_semiring_certs A)                               
      ; slt_C_ast := left_pre_semiring_ast A 
    |}.

  Definition cast_slt_C_to_slt 
    {L S : Type} (A : @slt_C L S) : 
    @slt L S :=
    {|
          slt_carrier := slt_C_carrier A
        ; slt_label := slt_C_label A
        ; slt_plus := slt_C_plus A                                               
        ; slt_trans := slt_C_trans A 
        ; slt_plus_certs := sg_C_certs_to_sg_certs 
            (eqv_eq (slt_C_carrier A))
            (slt_C_plus A)
            (eqv_witness (slt_C_carrier A)) 
            (eqv_new (slt_C_carrier A)) 
            (slt_C_plus_certs A)                        
        ; slt_trans_certs := slt_C_trans_certs A 
        ; slt_exists_plus_ann_d :=  slt_C_exists_plus_ann_d A                                
        ; slt_id_ann_certs_d  := slt_C_id_ann_certs_d A                                              
        ; slt_certs := slt_C_certs A                                 
        ; slt_ast := slt_C_ast A 
    |}.

  (* One layer finished. *)     


  (* start of multilayer fusion *)

  
  (* casting selective_left_dioid to all the way to the top*)

  Definition cast_selective_left_dioid_to_slt_CS 
    {L S : Type} (A : @selective_left_dioid L S) : @slt_CS L S :=
    let As :=  cast_selective_left_dioid_to_selective_left_pre_dioid A in 
    cast_selective_left_pre_dioid_to_slt_CS As. 


  Definition cast_selective_left_dioid_to_slt_C
    {L S : Type} 
    (A : @selective_left_dioid L S)  : @slt_C L S :=
    let As := @cast_selective_left_dioid_to_slt_CS L S A in 
    cast_slt_CS_to_slt_C As.


  Definition cast_selective_left_dioid_to_slt
    {L S : Type} 
    (A : @selective_left_dioid L S)  : @slt L S :=
    let As := @cast_selective_left_dioid_to_slt_C L S A in 
    @cast_slt_C_to_slt _ _ As.

  (* end of casting selective_left_dioids *)



  (* start of selective_left_pre_dioid casting *)

  Definition cast_selective_left_pre_dioid_to_slt_C 
    {L S : Type} (A : @selective_left_pre_dioid L S) :
    @slt_C L S :=
    let As := cast_selective_left_pre_dioid_to_slt_CS A in 
    cast_slt_CS_to_slt_C As.

  Definition cast_selective_left_pre_dioid_to_slt  
    {L S : Type} (A : @selective_left_pre_dioid L S) :
    @slt L S :=
    let As := cast_selective_left_pre_dioid_to_slt_C A 
    in cast_slt_C_to_slt As.

  (* end of casting of selective_left_pre_dioid all the way to top*)

  (* start of casting of slt_cs to slt *)
  Definition cast_slt_CS_to_slt 
    {L S : Type} (A : @slt_CS L S) : slt :=
    let As := cast_slt_CS_to_slt_C A in 
    cast_slt_C_to_slt As.
  (* end of casting *)

  (* start of left_selective_semiring casting *)

  Definition cast_left_selective_semiring_to_slt_C 
    {L S : Type} (A : @left_selective_semiring L S) :
    @slt_C L S :=
    let As := cast_left_selective_semiring_to_slt_CS A in 
    cast_slt_CS_to_slt_C As.


  Definition cast_left_selective_semiring_to_slt 
    {L S : Type} (A : @left_selective_semiring L S) :
    @slt L S :=
    let As := cast_left_selective_semiring_to_slt_C A in 
    cast_slt_C_to_slt As.

  (* end of left selective semiring *)


  (* casting of left idempotent semiring *)

  Definition cast_left_idempotent_semiring_to_left_pre_semiring 
    {L S : Type} (A : @left_idempotent_semiring L S) :
    @left_pre_semiring L S :=
    let As := cast_left_idempotent_semiring_to_left_semiring A in 
    cast_left_semiring_to_left_pre_semiring As.

  Definition cast_left_idempotent_semiring_to_slt_C
    {L S : Type} (A : @left_idempotent_semiring L S) :
    @slt_C L S :=
    let As := cast_left_idempotent_semiring_to_left_pre_semiring A in 
    cast_left_pre_semiring_to_slt_C As.

  Definition cast_left_idempotent_semiring_to_slt
    {L S : Type} (A : @left_idempotent_semiring L S) :
    @slt L S :=
    let As := cast_left_idempotent_semiring_to_slt_C A in 
    cast_slt_C_to_slt As.

  (* end of casting left_idempotent semiring *)

  (* cast up left selective semiring  *)


  Definition cast_left_selective_semiring_to_left_pre_semiring 
    {L S : Type} (A : @left_selective_semiring L S) :
    @left_pre_semiring L S :=
    let As := cast_left_selective_semiring_to_left_semiring A in 
    cast_left_semiring_to_left_pre_semiring As.

  (* en dof casting left selective semiring *)

  (* cast up left_semiring *)

  Definition cast_left_semiring_to_slt_C 
    {L S : Type} (A : @left_semiring L S) :
    @slt_C L S :=
    let As := cast_left_semiring_to_left_pre_semiring A in 
    cast_left_pre_semiring_to_slt_C As.

  Definition cast_left_semiring_to_slt 
    {L S : Type} (A : @left_semiring L S) :
    @slt L S :=
    let As :=  cast_left_semiring_to_slt_C A in 
    cast_slt_C_to_slt As.

  (* end of casting left semiring *)

  (* start of casting up left pre semiring *)

  Definition cast_left_pre_semiring_to_slt 
    {L S : Type} (A : @left_pre_semiring L S) :
    @slt L S :=
    let As := cast_left_pre_semiring_to_slt_C A in 
    cast_slt_C_to_slt As.

  (* end of left pre semiring casting *)

  (* start of left dioid casting up *)

  Definition cast_left_dioid_to_slt_C
    {L S : Type} (A : @left_dioid L S) : @slt_C L S :=
    let As := cast_left_dioid_to_slt_CI A in
    cast_slt_CI_to_slt_C As.

  Definition cast_left_dioid_to_slt 
    {L S : Type} (A : @left_dioid L S) : 
    @slt L S :=
    let As := cast_left_dioid_to_slt_C A in 
    cast_slt_C_to_slt As.

  (* end of left of dioid *)

  Definition cast_left_idempotent_semiring_to_slt_C_zero_is_ltr_ann 
    {L S : Type} (A : @left_idempotent_semiring L S) :
    @slt_C_zero_is_ltr_ann L S :=
    let As := cast_left_idempotent_semiring_to_left_semiring A in 
    cast_left_semiring_to_slt_C_zero_is_ltr_ann As.

  Definition cast_left_selective_semiring_to_slt_C_zero_is_ltr_ann
    {L S : Type} (A : @left_selective_semiring L S) :
    @slt_C_zero_is_ltr_ann L S :=
    let As := cast_left_selective_semiring_to_left_semiring A in 
    cast_left_semiring_to_slt_C_zero_is_ltr_ann As.

  Definition cast_slt_CI_to_slt 
    {L S : Type} (A : @slt_CI L S) : slt :=
    let As := cast_slt_CI_to_slt_C A in 
    cast_slt_C_to_slt As.

  Definition cast_slt_C_zero_is_ltr_ann_to_slt 
    {L S : Type} (A : @slt_C_zero_is_ltr_ann L S) : slt :=
    let As := cast_slt_C_zero_is_ltr_ann_to_slt_C A in 
    cast_slt_C_to_slt As.

     

End CAS.


Section MCAS.

  





  (* A_selective_left_dioid is at bottom 
    structure and there is nothing below it. *)
  Definition  cast_slt_mcas_to_selective_left_dioid 
    {L S : Type} (A : @slt_mcas L S) : @slt_mcas L S  :=
    match A with
    | SLT_Error ls => SLT_Error ls 
    | SLT slt => 
        SLT_Error ["Can not cast up A_slt to A_selective_left_dioid"]
    | SLT_C slt =>
        SLT_Error ["Can not cast up A_slt_C to A_selective_left_dioid"]    
    | SLT_CS slt => 
        SLT_Error ["Can not cast up A_slt_CS to A_selective_left_dioid"]
    | SLT_CI slt => 
        SLT_Error ["Can not cast up A_slt_CI to A_selective_left_dioid"]
    | SLT_C_Zero_Is_Ltr_ann slt => 
        SLT_Error ["Can not cast up A_slt_C_zero_is_ltr_ann to A_selective_left_dioid"]
    | SLT_Left_Pre_Semiring slt => 
        SLT_Error ["Can not cast up A_left_pre_semiring to A_selective_left_dioid"]
    | SLT_Dioid slt =>
        SLT_Error ["Can not cast up A_left_dioid to A_selective_left_dioid"]
    | SLT_Selective_Left_Pre_Dioid slt => 
        SLT_Error ["Can not cast up A_selective_left_pre_dioid to A_selective_left_dioid"]
    | SLT_Semiring slt => 
        SLT_Error ["Can not cast up A_left_semiring to A_selective_left_dioid"]
    | SLT_Selective_Dioid slt => 
        SLT_Selective_Dioid (cast_selective_left_dioid_to_selective_left_dioid slt) (* identity function *)
    | SLT_Selective_Semiring slt => 
        SLT_Error ["Can not cast up A_left_selective_semiring to A_selective_left_dioid"]
    | SLT_Idempotent_Semiring slt => 
        SLT_Error ["Can not cast up A_left_idempotent_semiring to A_selective_left_dioid"]
    end.



  (* 
    selective_left_pre_dioid
          |
    selective_left_dioid
    The only structure below selective_left_pre_dioid is selective_left_dioid and 
    therefore we return values in these two cases and rest are errors.
  *)
  Definition cast_slt_mcas_to_selective_left_pre_dioid
    {L S : Type} (A : @slt_mcas L S) : @slt_mcas L S :=
    match A with 
    | SLT_Error ls => SLT_Error ls 
    | SLT slt => 
        SLT_Error ["Can not cast up A_slt to A_selective_left_pre_dioid"]
    | SLT_C slt => 
        SLT_Error ["Can not cast up A_slt_C to A_selective_left_pre_dioid"]
    | SLT_CS slt => 
        SLT_Error ["Can not cast up A_slt_CS to A_selective_left_pre_dioid"]
    | SLT_CI slt => 
        SLT_Error ["Can not cast up A_slt_CI to A_selective_left_pre_dioid"]
    | SLT_C_Zero_Is_Ltr_ann slt => 
        SLT_Error ["Can not cast up A_slt_zero_is_ltr_ann to A_selective_left_pre_dioid"]
    | SLT_Left_Pre_Semiring slt => 
        SLT_Error ["Can not cast up A_left_pre_semiring to A_selective_left_pre_dioid"]
    | SLT_Dioid slt =>
        SLT_Error ["Can not cast up A_left_dioid to A_selective_left_pre_dioid"]
    | SLT_Selective_Left_Pre_Dioid slt => 
        SLT_Selective_Left_Pre_Dioid 
          (cast_selective_left_pre_dioid_to_selective_left_pre_dioid slt)
    | SLT_Semiring slt => 
        SLT_Error ["Can not cast up A_left_semiring to A_selective_left_pre_dioid"]
    | SLT_Selective_Dioid slt => 
        SLT_Selective_Left_Pre_Dioid (cast_selective_left_dioid_to_selective_left_pre_dioid slt)
    | SLT_Selective_Semiring slt => 
        SLT_Error ["Can not cast up A_left_selective_semiring to A_selective_left_pre_dioid"]
    | SLT_Idempotent_Semiring slt => 
        SLT_Error ["Can not cast up A_left_idempotent_semiring to A_selective_left_pre_dioid"]
    end.



  (*
    There is nothing below left_selective_semiring, so
    all the returns values are errors, except the 
    left_selective_semiring
  
  *)
  Definition cast_slt_mcas_to_left_selective_semiring 
    {L S : Type} (A : @slt_mcas L S) : @slt_mcas L S :=
    match A with 
    | SLT_Error ls => SLT_Error ls 
    | SLT slt => 
        SLT_Error ["Can not cast up A_slt to A_left_selective_semiring"]
    | SLT_C slt =>
        SLT_Error ["Can not cast up A_SLT_C to A_left_selective_semiring"]
    | SLT_CS slt => 
        SLT_Error ["Can not cast up A_slt_CS to A_left_selective_semiring"]
    | SLT_CI slt => 
        SLT_Error ["Can not cast up A_slt_CI to A_left_selective_semiring"]
    | SLT_C_Zero_Is_Ltr_ann slt => 
        SLT_Error ["Can not cast up A_slt_C_zero_is_ltr_ann to A_left_selective_semiring"]
    | SLT_Left_Pre_Semiring slt => 
        SLT_Error ["Can not cast up A_left_pre_semiring to A_left_selective_semiring"]
    | SLT_Dioid slt =>
        SLT_Error ["Can not cast up A_left_dioid to A_left_selective_semiring"]
    | SLT_Selective_Left_Pre_Dioid slt => 
        SLT_Error ["Can not cast up a A_selective_left_pre_dioid to A_left_selective_semiring"]
    | SLT_Semiring slt => 
        SLT_Error ["Can not cast up A_left_semiring to A_left_selective_semiring"]
    | SLT_Selective_Dioid slt => 
        SLT_Error ["Can not cast up A_selective_left_dioid to A_left_selective_semiring"]
    | SLT_Selective_Semiring slt => 
        SLT_Selective_Semiring (cast_left_selective_semiring_to_left_selective_semiring slt)
    | SLT_Idempotent_Semiring slt => 
        SLT_Error ["Can not cast up A_left_idempotent_semiring A_left_selective_semiring"]
    end.



     (* all the previously defined structures can be cast up to A_SLT_CS *)

  Definition cast_slt_mcas_to_slt_CS 
    {L S : Type} (A : @slt_mcas L S) : @slt_mcas L S :=
    match A with
    | SLT_Error ls => SLT_Error ls 
    | SLT slt => 
        SLT_Error ["Can not cast up A_slt to A_slt_CS"]
    | SLT_C slt =>
        SLT_Error ["Can not cast up A_SLT_C to A_slt_CS"]
    | SLT_CS slt => A
    | SLT_CI slt => 
        SLT_Error ["Can not cast up A_slt_CI to A_slt_CS"]
    | SLT_C_Zero_Is_Ltr_ann slt => 
        SLT_Error ["Can not cast up A_slt_C_zero_is_ltr_ann to A_slt_CS"]
    | SLT_Left_Pre_Semiring slt => 
        SLT_Error ["Can not cast up A_left_pre_semiring to A_slt_CS"]
    | SLT_Dioid slt =>
        SLT_Error ["Can not cast up A_left_dioid to A_slt_CS"]
    | SLT_Selective_Left_Pre_Dioid slt => 
        SLT_CS (cast_selective_left_pre_dioid_to_slt_CS slt)  
    | SLT_Semiring slt => 
        SLT_Error ["Can not cast up A_left_semiring to A_slt_CS"]
    | SLT_Selective_Dioid slt => 
        SLT_CS (cast_selective_left_dioid_to_slt_CS slt)
    | SLT_Selective_Semiring slt => 
        SLT_CS (cast_left_selective_semiring_to_slt_CS slt)
    | SLT_Idempotent_Semiring slt => 
        SLT_Error ["Can not cast up A_left_idempotent_semiring A_left_selective_semiring"]
    end.
  (* end of cast up to A_SLT_CS *)  


  (*
     A_left_idempotent_semiring is a structure at the bottom,
     so all cases are error, except the  A_left_idempotent_semiring case itself
  *)
  Definition cast_slt_mcas_to_left_idempotent_semiring 
    {L S : Type} (A : @slt_mcas L S) : @slt_mcas L S :=
    match A with
    | SLT_Error ls => SLT_Error ls 
    | SLT slt => 
        SLT_Error ["Can not cast up A_slt to A_left_idempotent_semiring"]
    | SLT_C slt =>
        SLT_Error ["Can not cast up A_slt_C to A_left_idempotent_semiring"]    
    | SLT_CS slt => 
        SLT_Error ["Can not cast up A_slt_CS to A_left_idempotent_semiring"]
    | SLT_CI slt => 
        SLT_Error ["Can not cast up A_slt_CI to A_left_idempotent_semiring"]
    | SLT_C_Zero_Is_Ltr_ann slt => 
        SLT_Error ["Can not cast up A_slt_C_zero_is_ltr_ann to A_left_idempotent_semiring"]
    | SLT_Left_Pre_Semiring slt => 
        SLT_Error ["Can not cast up A_left_pre_semiring to A_left_idempotent_semiring"]
    | SLT_Dioid slt =>
        SLT_Error ["Can not cast up A_left_dioid to A_left_idempotent_semiring"]
    | SLT_Selective_Left_Pre_Dioid slt => 
        SLT_Error ["Can not cast up A_selective_left_pre_dioid to A_left_idempotent_semiring"]
    | SLT_Semiring slt => 
        SLT_Error ["Can not cast up A_left_semiring to A_left_idempotent_semiring"]
    | SLT_Selective_Dioid slt => 
        SLT_Error ["Can not cast up A_selective_left_dioid to A_left_idempotent_semiring"]
    | SLT_Selective_Semiring slt => 
        SLT_Error ["Can not cast up A_selective_semiring to A_left_idempotent_semiring"]
    | SLT_Idempotent_Semiring slt => 
        SLT_Idempotent_Semiring 
          (cast_left_idempotent_semiring_to_left_idempotent_semiring slt)
    end.


  
    
  (* 
            left semiring
              |
        --------------------
        |                   |
    left idempotent     left selective
       semiring             semiring
  
  *)
  Definition cast_slt_mcas_to_left_semiring 
    {L S : Type} (A : @slt_mcas L S) : @slt_mcas L S :=
    match A with
    | SLT_Error ls => SLT_Error ls 
    | SLT slt => 
        SLT_Error ["Can not cast up A_slt to A_left_semiring"]
    | SLT_C slt =>
        SLT_Error ["Can not cast up A_slt_C to A_left_semiring"]    
    | SLT_CS slt => 
        SLT_Error ["Can not cast up A_slt_CS to A_left_semiring"]
    | SLT_CI slt => 
        SLT_Error ["Can not cast up A_slt_CI to A_left_semiring"]
    | SLT_C_Zero_Is_Ltr_ann slt => 
        SLT_Error ["Can not cast up A_slt_C_zero_is_ltr_ann to A_left_semiring"]
    | SLT_Left_Pre_Semiring slt => 
        SLT_Error ["Can not cast up A_left_pre_semiring to A_left_semiring"]
    | SLT_Dioid slt =>
        SLT_Error ["Can not cast up A_left_dioid to A_left_semiring"]
    | SLT_Selective_Left_Pre_Dioid slt => 
        SLT_Error ["Can not cast up A_selective_left_pre_dioid to A_left_semiring"]
    | SLT_Semiring slt => 
        SLT_Semiring (cast_left_semiring_to_left_semiring slt)
    | SLT_Selective_Dioid slt => 
        SLT_Error ["Can not cast up A_selective_left_dioid to A_left_semiring"]
    | SLT_Selective_Semiring slt => 
        SLT_Semiring (cast_left_selective_semiring_to_left_semiring slt)
    | SLT_Idempotent_Semiring slt => 
        SLT_Semiring (cast_left_idempotent_semiring_to_left_semiring slt)
    end.


  Definition cast_slt_mcas_to_left_pre_semiring 
    {L S : Type} (A : @slt_mcas L S) : @slt_mcas L S :=
    match A with
    | SLT_Error ls => SLT_Error ls 
    | SLT slt => 
        SLT_Error ["Can not cast up A_slt to A_left_pre_semiring"]
    | SLT_C slt =>
        SLT_Error ["Can not cast up A_slt_C to A_left_pre_semiring"]    
    | SLT_CS slt => 
        SLT_Error ["Can not cast up A_slt_CS to A_left_pre_semiring"]
    | SLT_CI slt => 
        SLT_Error ["Can not cast up A_slt_CI to A_left_pre_semiring"]
    | SLT_C_Zero_Is_Ltr_ann slt => 
        SLT_Error ["Can not cast up A_slt_C_zero_is_ltr_ann to A_left_pre_semiring"]
    | SLT_Left_Pre_Semiring slt => A 
    | SLT_Dioid slt =>
        SLT_Error ["Can not cast up A_left_dioid to A_left_pre_semiring"]
    | SLT_Selective_Left_Pre_Dioid slt => 
        SLT_Error ["Can not cast up A_selective_left_pre_dioid to A_left_pre_semiring"]
    | SLT_Semiring slt => 
        SLT_Left_Pre_Semiring (cast_left_semiring_to_left_pre_semiring slt)
    | SLT_Selective_Dioid slt => 
        SLT_Error ["Can not cast up A_selective_left_dioid to A_left_pre_semiring"]
    | SLT_Selective_Semiring slt => 
        SLT_Left_Pre_Semiring (cast_left_selective_semiring_to_left_pre_semiring slt)
    | SLT_Idempotent_Semiring slt => 
        SLT_Left_Pre_Semiring (cast_left_idempotent_semiring_to_left_pre_semiring slt)
    end.


  (* end of casting selective left pre semiring *)


  (* starting to A_slt_CI casting group *)

  Definition cast_slt_mcas_to_left_dioid 
    {L S : Type} (A : @slt_mcas L S) : @slt_mcas L S :=
    match A with
    | SLT_Error ls => SLT_Error ls 
    | SLT slt => 
        SLT_Error ["Can not cast up A_slt to A_left_dioid"]
    | SLT_C slt => SLT_Error ["Can not cast up A_slt to A_left_dioid"]    
    | SLT_CS slt => 
        SLT_Error ["Can not cast up A_slt_CS to A_left_dioid"]
    | SLT_CI slt => 
        SLT_Error ["Can not cast up A_slt_CI to A_left_dioid"]
    | SLT_C_Zero_Is_Ltr_ann slt => 
        SLT_Error ["Can not cast up A_slt_zero_is_ltr_ann to A_left_dioid"]
    | SLT_Left_Pre_Semiring slt => 
        SLT_Error ["Can not cast up A_left_pre_semiring to A_left_dioid"]
    | SLT_Dioid slt => 
        SLT_Dioid (cast_left_dioid_to_left_dioid slt) (* identity function *)
    | SLT_Selective_Left_Pre_Dioid slt => 
        SLT_Error ["Can not cast up A_selective_left_pre_dioid to A_left_dioid"]
    | SLT_Semiring slt => 
        SLT_Error ["Can not cast up A_left_semiring to A_left_dioid"]
    | SLT_Selective_Dioid slt => 
        SLT_Error ["Can not cast up A_selective_left_dioid to A_left_dioid"]
    | SLT_Selective_Semiring slt => 
        SLT_Error ["Can not cast up A_left_selective_semiring to A_left_dioid"]
    | SLT_Idempotent_Semiring slt => 
        SLT_Error ["Can not cast up A_left_idempotent_semiring to A_left_dioid"]
    end.


  Definition cast_slt_mcas_to_slt_CI {L S : Type}
    (A : @slt_mcas L S) : @slt_mcas L S  :=
    match A with
    | SLT_Error ls => SLT_Error ls 
    | SLT slt => 
        SLT_Error ["Can not cast up A_slt to A_SLT_CI"]
    | SLT_C slt => 
        SLT_Error ["Can not cast up A_slt_C to A_slt_CI"]       
    | SLT_CS slt => 
        SLT_Error ["Can not cast up A_slt_CS to A_SLT_CI"]
    | SLT_CI slt => 
        SLT_CI (cast_slt_CI_to_slt_CI slt)
    | SLT_C_Zero_Is_Ltr_ann slt => 
        SLT_Error ["Can not cast up A_slt_C_zero_is_ltr_ann to A_SLT_CI"]
    | SLT_Left_Pre_Semiring slt => 
        SLT_Error ["Can not cast up A_left_pre_semiring to A_SLT_CI"]
    | SLT_Dioid slt =>
        SLT_CI (cast_left_dioid_to_slt_CI  slt)
    | SLT_Selective_Left_Pre_Dioid slt => 
        SLT_Error ["Can not cast up A_selective_left_pre_dioid to A_SLT_CI"]
    | SLT_Semiring slt => 
        SLT_Error ["Can not cast up A_left_semiring to A_SLT_CI"]
    | SLT_Selective_Dioid slt => SLT_Error [""]
    | SLT_Selective_Semiring slt => 
        SLT_Error ["Can not cast up A_left_selective_semiring to A_SLT_CI"]
    | SLT_Idempotent_Semiring slt => 
        SLT_CI (cast_left_idempotent_semiring_to_slt_CI  slt)
    end.

  (* end of A_slt_CI casting *)  

  (* start of casting A_slt_C_zero *)


  Definition cast_slt_mcas_to_slt_C_zero_is_ltr_ann {L S : Type}
    (A : @slt_mcas L S) : @slt_mcas L S  :=
    match A with
    | SLT_Error ls => SLT_Error ls 
    | SLT slt => 
        SLT_Error ["Can not cast up A_slt to A_slt_C_zero_is_ltr_ann"]
    | SLT_C slt => 
        SLT_Error ["Can not cast up A_slt_C to A_slt_C_zero_is_ltr_ann"]       
    | SLT_CS slt => 
        SLT_Error ["Can not cast up A_slt_CS to A_slt_C_zero_is_ltr_ann"]
    | SLT_CI slt => 
        SLT_Error ["Can not cast up A_SLT_CI to A_slt_C_zero_is_ltr_ann"]
    | SLT_C_Zero_Is_Ltr_ann slt => A
    | SLT_Left_Pre_Semiring slt => 
        SLT_Error ["Can not cast up A_left_pre_semiring toA_slt_C_zero_is_ltr_ann"]
    | SLT_Dioid slt =>
        SLT_C_Zero_Is_Ltr_ann (cast_left_dioid_to_slt_C_zero_is_ltr_ann slt)
    | SLT_Selective_Left_Pre_Dioid slt => 
        SLT_Error ["Can not cast up A_selective_left_pre_dioid to A_SLT_CI"]
    | SLT_Semiring slt => 
        SLT_C_Zero_Is_Ltr_ann (cast_left_semiring_to_slt_C_zero_is_ltr_ann slt)
    | SLT_Selective_Dioid slt => 
        SLT_C_Zero_Is_Ltr_ann (cast_selective_left_dioid_to_slt_C_zero_is_ltr_ann slt)
    | SLT_Selective_Semiring slt => 
        SLT_C_Zero_Is_Ltr_ann  (cast_left_selective_semiring_to_slt_C_zero_is_ltr_ann slt)
    | SLT_Idempotent_Semiring slt => 
        SLT_C_Zero_Is_Ltr_ann  (cast_left_idempotent_semiring_to_slt_C_zero_is_ltr_ann slt)
    end.


  Definition cast_slt_mcas_to_slt_C 
    {L S : Type} (A : @slt_mcas L S) : @slt_mcas L S  :=
    match A with
    | SLT_Error ls => SLT_Error ls 
    | SLT slt => 
        SLT_Error ["Can not cast up A_slt to A_slt_C"]
    | SLT_C slt => A       
    | SLT_CS slt => 
        SLT_C (cast_slt_CS_to_slt_C slt)
    | SLT_CI slt => 
        SLT_C (cast_slt_CI_to_slt_C slt)
    | SLT_C_Zero_Is_Ltr_ann slt => 
        SLT_C (cast_slt_C_zero_is_ltr_ann_to_slt_C slt) 
    | SLT_Left_Pre_Semiring slt => 
        SLT_C (cast_left_pre_semiring_to_slt_C slt)
    | SLT_Dioid slt =>
        SLT_C (cast_left_dioid_to_slt_C slt)
    | SLT_Selective_Left_Pre_Dioid slt => 
        SLT_C (cast_selective_left_pre_dioid_to_slt_C slt)
    | SLT_Semiring slt => 
        SLT_C (cast_left_semiring_to_slt_C slt)
    | SLT_Selective_Dioid slt => 
        SLT_C (cast_selective_left_dioid_to_slt_C slt)
    | SLT_Selective_Semiring slt => 
        SLT_C (cast_left_selective_semiring_to_slt_C slt)
    | SLT_Idempotent_Semiring slt => 
        SLT_C (cast_left_idempotent_semiring_to_slt_C slt)
    end.
    
    
  Definition cast_slt_mcas_to_slt 
    {L S : Type} (A : @slt_mcas L S) : @slt_mcas L S  :=
    match A with
    | SLT_Error ls => SLT_Error ls 
    | SLT slt =>  A
    | SLT_C slt => 
        SLT (cast_slt_C_to_slt slt)       
    | SLT_CS slt => 
        SLT (cast_slt_CS_to_slt slt)
    | SLT_CI slt => 
        SLT (cast_slt_CI_to_slt slt)
    | SLT_C_Zero_Is_Ltr_ann slt => 
        SLT (cast_slt_C_zero_is_ltr_ann_to_slt slt) 
    | SLT_Left_Pre_Semiring slt => 
        SLT (cast_left_pre_semiring_to_slt slt)
    | SLT_Dioid slt =>
        SLT (cast_left_dioid_to_slt slt)
    | SLT_Selective_Left_Pre_Dioid slt => 
        SLT (cast_selective_left_pre_dioid_to_slt slt)
    | SLT_Semiring slt => 
        SLT (cast_left_semiring_to_slt slt)
    | SLT_Selective_Dioid slt => 
        SLT (cast_selective_left_dioid_to_slt slt)
    | SLT_Selective_Semiring slt => 
        SLT (cast_left_selective_semiring_to_slt slt)
    | SLT_Idempotent_Semiring slt => 
        SLT (cast_left_idempotent_semiring_to_slt slt)
    end.
  
  


End MCAS.

Section ProofCertCorrect.


  Lemma correctness_sg_CI_certs_to_sg_certs 
    {L S : Type}
    (r : brel S)
    (b : binary_op S)
    (s : S)
    (f : S -> S)
    (Pf : properties.brel_not_trivial S r f)
    (eqvS : eqv_proofs S r) : 
    forall pf,  
    sg_CI_certs_to_sg_certs r b s f 
      (P2C_sg_CI S r b pf)  = 
    P2C_sg S r b 
      (A_sg_CI_proofs_to_sg_proofs r b s f Pf eqvS pf).
  Proof.
    intros pf.
    unfold A_sg_CI_proofs_to_sg_proofs.
    rewrite <-correct_sg_certs_from_sg_C_certs.
    rewrite <-correct_sg_C_certs_from_sg_CI_certs.
    unfold sg_CI_certs_to_sg_certs.
    reflexivity.
  Qed.


  Lemma correctness_sg_CS_certs_to_sg_certs
    {L S : Type}
    (r : brel S)
    (b : binary_op S)
    (s : S)
    (f : S -> S)
    (Pf : properties.brel_not_trivial S r f)
    (eqvS : eqv_proofs S r) : 
    forall pf,  
    sg_CS_certs_to_sg_certs r b s f 
      (P2C_sg_CS S r b pf)  = 
    P2C_sg S r b 
      (A_sg_CS_proofs_to_sg_proofs r b s f Pf eqvS pf).
  Proof.
    intros pf.
    unfold A_sg_CS_proofs_to_sg_proofs.
    rewrite <-correct_sg_certs_from_sg_C_certs.
    rewrite <-correct_sg_C_certs_from_sg_CS_certs.
    unfold sg_CS_certs_to_sg_certs.
    reflexivity.
  Qed.


  Lemma correctness_sg_C_certs_to_sg_certs 
    {L S : Type}
    (r : brel S)
    (b : binary_op S)
    (s : S)
    (f : S -> S)
    (Pf : properties.brel_not_trivial S r f)
    (eqvS : eqv_proofs S r) : 
    forall pf,  
    sg_C_certs_to_sg_certs r b s f 
      (P2C_sg_C S r b pf)  = 
    P2C_sg S r b 
      (A_sg_C_proofs_to_sg_proofs r b s f Pf eqvS pf).
  Proof.
    intros pf.
    unfold A_sg_C_proofs_to_sg_proofs,
    sg_C_certs_to_sg_certs.
    rewrite <-correct_sg_certs_from_sg_C_certs.
    reflexivity.
  Qed.
  

  
  Lemma correctness_cast_left_semiring_certificates_to_slt_certificates 
    {L S : Type}
    (r : brel S)
    (add : binary_op S)
    (ltr : ltr_type L S) : 
    forall pf, 
    cast_left_semiring_certificates_to_slt_certificates   
      (P2C_left_semiring r add ltr pf) = 
    P2C_slt r add ltr 
      (cast_left_semiring_proofs_to_slt_proofs r add ltr pf).
  Proof.
    intros pf.
    unfold cast_left_semiring_certificates_to_slt_certificates,
    cast_left_semiring_proofs_to_slt_proofs, P2C_slt; simpl.
    f_equal.
    unfold A_left_semiring_not_absorptive, 
    p2c_slt_strictly_absorptive_check; simpl.
    destruct pf; simpl.
    destruct A_left_semiring_not_absorptive; simpl.
    destruct x as (l, s); simpl.
    reflexivity.
  Qed.


End ProofCertCorrect.

Section Correctness.

  
  Context 
    {L S : Type}.
  
  Ltac destruct_and_solve pf := 
    destruct pf;
    simpl; try reflexivity.


  Lemma correctness_cast_slt_mcas_to_selective_left_dioid : 
    forall pf,  
    cast_slt_mcas_to_selective_left_dioid (A2C_mcas_slt pf) = 
    @A2C_mcas_slt L S (cast_A_slt_mcas_to_A_selective_left_dioid pf).
  Proof.
    destruct_and_solve pf.
  Qed.


  Lemma correctness_cast_slt_mcas_to_selective_left_pre_dioid : 
    forall pf, 
    cast_slt_mcas_to_selective_left_pre_dioid (A2C_mcas_slt pf) =
    @A2C_mcas_slt L S (cast_A_slt_mcas_to_A_selective_left_pre_dioid pf).
  Proof.
    destruct_and_solve pf.
  Qed.


  Lemma correctness_cast_slt_mcas_to_left_selective_semiring : 
    forall pf, 
    cast_slt_mcas_to_left_selective_semiring (A2C_mcas_slt pf) = 
    @A2C_mcas_slt L S (cast_A_slt_mcas_to_A_left_selective_semiring pf).
  Proof.
    destruct_and_solve pf.
  Qed.

  Lemma correctness_cast_left_selective_semiring_to_slt_CS :
    forall a,  
    cast_left_selective_semiring_to_slt_CS (A2C_left_selective_semiring a) =
    @A2C_slt_cs L S (cast_A_left_selective_semiring_to_A_slt_CS a).
  Proof.
    unfold cast_left_selective_semiring_to_slt_CS,
    cast_A_left_selective_semiring_to_A_slt_CS;
    destruct a; simpl;
    unfold A2C_slt_cs; simpl;
    f_equal.
    rewrite correctness_cast_left_semiring_certificates_to_slt_certificates.
    reflexivity.
  Qed.
    



  Lemma correctness_cast_slt_mcas_to_slt_CS :
    forall pf, 
    cast_slt_mcas_to_slt_CS (A2C_mcas_slt pf) = 
    @A2C_mcas_slt L S (cast_A_slt_mcas_to_A_slt_CS pf).
  Proof.
    unfold cast_slt_mcas_to_slt_CS,
    cast_A_slt_mcas_to_A_slt_CS;
    destruct pf; simpl;
    try reflexivity.
    rewrite  correctness_cast_left_selective_semiring_to_slt_CS;
    reflexivity.
  Qed.



  Lemma correctness_cast_slt_mcas_to_left_idempotent_semiring : 
    forall pf,  
    cast_slt_mcas_to_left_idempotent_semiring (A2C_mcas_slt pf) =
    @A2C_mcas_slt L S (cast_A_slt_mcas_to_A_left_idempotent_semiring pf).
  Proof.
    destruct_and_solve pf.
  Qed.

  Lemma correctness_cast_left_idempotent_semiring_to_left_semiring : 
    forall a,  
    cast_left_idempotent_semiring_to_left_semiring
      (A2C_left_idempotent_semiring a) =
    @A2C_left_semiring L S
      (cast_A_left_idempotent_semiring_to_A_left_semiring a).
  Proof.
    unfold cast_left_idempotent_semiring_to_left_semiring,
    cast_A_left_idempotent_semiring_to_A_left_semiring;
    destruct a; simpl;
    unfold A2C_left_semiring;
    simpl; f_equal.
    rewrite <-correct_sg_C_certs_from_sg_CI_certs; 
    reflexivity.
  Qed.
  

  Lemma correctness_cast_slt_mcas_to_left_semiring :
    forall pf, 
    cast_slt_mcas_to_left_semiring (A2C_mcas_slt pf) = 
    @A2C_mcas_slt L S (cast_A_slt_mcas_to_A_left_semiring  pf).
  Proof.
    unfold cast_slt_mcas_to_left_semiring,
    cast_A_slt_mcas_to_A_left_semiring;
    destruct_and_solve pf;
    f_equal.
    rewrite correctness_cast_left_idempotent_semiring_to_left_semiring;
    reflexivity.
  Qed.


  Lemma correctness_cast_left_idempotent_semiring_to_left_pre_semiring : 
    forall a, 
    cast_left_idempotent_semiring_to_left_pre_semiring
      (A2C_left_idempotent_semiring a) =
    @A2C_left_pre_semiring L S
      (cast_A_left_idempotent_semiring_to_A_left_pre_semiring a).
  Proof.
    unfold cast_left_idempotent_semiring_to_left_pre_semiring,
    cast_A_left_idempotent_semiring_to_A_left_pre_semiring,
    cast_left_semiring_to_left_pre_semiring,
    cast_left_idempotent_semiring_to_left_semiring,
    cast_A_left_semiring_to_A_left_pre_semiring,
    cast_A_left_idempotent_semiring_to_A_left_semiring;
    destruct a; simpl;
    unfold A2C_left_pre_semiring; 
    simpl; f_equal.
    rewrite <-correct_sg_C_certs_from_sg_CI_certs; 
    reflexivity.
  Qed.




  Lemma correctness_cast_slt_mcas_to_left_pre_semiring : 
    forall pf, 
    cast_slt_mcas_to_left_pre_semiring (A2C_mcas_slt pf) =
    @A2C_mcas_slt L S (cast_A_slt_mcas_to_A_left_pre_semiring pf).
  Proof.
    destruct_and_solve pf;
    f_equal.
    rewrite correctness_cast_left_idempotent_semiring_to_left_pre_semiring;
    reflexivity.
  Qed.


  Lemma correctness_cast_slt_mcas_to_left_dioid : 
    forall pf, 
    cast_slt_mcas_to_left_dioid (A2C_mcas_slt pf) = 
    @A2C_mcas_slt L S (cast_A_slt_mcas_to_A_left_dioid pf).
  Proof.
    unfold cast_slt_mcas_to_left_dioid,
    cast_A_slt_mcas_to_A_left_dioid; 
    destruct pf; simpl;
    try reflexivity.
  Qed.

  Lemma correctness_cast_left_idempotent_semiring_to_slt_CI :   
    forall a, 
    cast_left_idempotent_semiring_to_slt_CI 
      (A2C_left_idempotent_semiring a) =
    @A2C_slt_ci L S 
      (cast_A_left_idempotent_semiring_to_A_slt_CI a).
  Proof.
    unfold cast_left_idempotent_semiring_to_slt_CI,
    cast_A_left_idempotent_semiring_to_A_slt_CI;
    destruct_and_solve a;
    unfold A2C_slt_ci;
    simpl;
    f_equal.
    rewrite correctness_cast_left_semiring_certificates_to_slt_certificates.
    reflexivity.
  Qed.


  Lemma correctness_cast_slt_mcas_to_slt_CI : 
    forall pf, 
    cast_slt_mcas_to_slt_CI (A2C_mcas_slt pf) = 
    @A2C_mcas_slt L S (cast_A_slt_mcas_to_A_slt_CI pf).
  Proof.
    unfold cast_slt_mcas_to_slt_CI,
    cast_A_slt_mcas_to_A_slt_CI;
    destruct pf; simpl;
    try reflexivity;
    f_equal.
    rewrite correctness_cast_left_idempotent_semiring_to_slt_CI;
    reflexivity.
  Qed.

  Lemma correctness_cast_left_dioid_to_slt_C_zero_is_ltr_ann : 
    forall a,  
    cast_left_dioid_to_slt_C_zero_is_ltr_ann (A2C_left_dioid a) =
    @A2C_slt_C_zero_is_ltr_ann L S (cast_A_left_dioid_to_A_slt_C_zero_is_ltr_ann a).
  Proof.
    unfold cast_left_dioid_to_slt_C_zero_is_ltr_ann,
    cast_A_left_dioid_to_A_slt_C_zero_is_ltr_ann; 
    destruct a; simpl;
    unfold A2C_slt_C_zero_is_ltr_ann; 
    simpl; f_equal.
    rewrite <-correct_sg_C_certs_from_sg_CI_certs; 
    reflexivity.
  Qed.



  Lemma correctness_cast_left_semiring_to_slt_C_zero_is_ltr_ann : 
    forall a,  
    cast_left_semiring_to_slt_C_zero_is_ltr_ann (A2C_left_semiring a) =
    @A2C_slt_C_zero_is_ltr_ann L S 
      (cast_A_left_semiring_to_A_slt_C_zero_is_ltr_ann a).
  Proof.
    unfold cast_left_semiring_to_slt_C_zero_is_ltr_ann,
    cast_A_left_semiring_to_A_slt_C_zero_is_ltr_ann;
    destruct a; simpl;
    unfold  A2C_slt_C_zero_is_ltr_ann; 
    simpl; f_equal.
    rewrite correctness_cast_left_semiring_certificates_to_slt_certificates;
    reflexivity.
  Qed.
     

  Lemma correctness_cast_left_selective_semiring_to_slt_C_zero_is_ltr_ann : 
    forall a, 
    cast_left_selective_semiring_to_slt_C_zero_is_ltr_ann
      (A2C_left_selective_semiring a) =
    @A2C_slt_C_zero_is_ltr_ann L S 
      (cast_A_left_selective_semiring_to_A_slt_C_zero_is_ltr_ann a).
  Proof.
    intros a.
    unfold cast_left_selective_semiring_to_slt_C_zero_is_ltr_ann,
    cast_A_left_selective_semiring_to_A_slt_C_zero_is_ltr_ann.
    rewrite <-correctness_cast_left_semiring_to_slt_C_zero_is_ltr_ann.
    f_equal.
  Qed.



  Lemma correctness_cast_left_idempotent_semiring_to_slt_C_zero_is_ltr_ann : 
    forall a, 
    cast_left_idempotent_semiring_to_slt_C_zero_is_ltr_ann
      (A2C_left_idempotent_semiring a) =
    @A2C_slt_C_zero_is_ltr_ann L S 
      (cast_A_left_idempotent_semiring_to_A_slt_C_zero_is_ltr_ann a).
  Proof.
    intros *.
    unfold cast_left_idempotent_semiring_to_slt_C_zero_is_ltr_ann,
    cast_A_left_idempotent_semiring_to_A_slt_C_zero_is_ltr_ann.
    rewrite <-correctness_cast_left_semiring_to_slt_C_zero_is_ltr_ann;
    f_equal.
    apply correctness_cast_left_idempotent_semiring_to_left_semiring.
  Qed.


  Lemma correctness_cast_slt_mcas_to_slt_C_zero_is_ltr_ann : 
    forall pf, 
    cast_slt_mcas_to_slt_C_zero_is_ltr_ann (A2C_mcas_slt pf) = 
    @A2C_mcas_slt L S (cast_A_slt_mcas_to_A_slt_C_zero_is_ltr_ann pf).
  Proof.
    unfold cast_slt_mcas_to_slt_C_zero_is_ltr_ann,
    cast_A_slt_mcas_to_A_slt_C_zero_is_ltr_ann;
    destruct pf; simpl; 
    try reflexivity;
    f_equal.
    + apply correctness_cast_left_dioid_to_slt_C_zero_is_ltr_ann.
    + apply correctness_cast_left_semiring_to_slt_C_zero_is_ltr_ann.
    + apply correctness_cast_left_selective_semiring_to_slt_C_zero_is_ltr_ann.
    + apply correctness_cast_left_idempotent_semiring_to_slt_C_zero_is_ltr_ann.
  Qed.
  
  Lemma correctness_cast_slt_CI_to_slt_C :   
    forall a, 
    cast_slt_CI_to_slt_C (A2C_slt_ci a) =
    @A2C_slt_c L S (cast_A_slt_CI_to_A_slt_C a).
  Proof.
    unfold cast_slt_CI_to_slt_C, 
    cast_A_slt_CI_to_A_slt_C,
    A2C_slt_c; destruct a;
    simpl;
    f_equal.
    rewrite <-correct_sg_C_certs_from_sg_CI_certs; 
    reflexivity.
  Qed.


  Lemma correctness_cast_left_dioid_to_slt_C : 
    forall a, 
    cast_left_dioid_to_slt_C (A2C_left_dioid a) =
    @A2C_slt_c L S (cast_A_left_dioid_to_A_slt_C a).
  Proof.
    intros a.
    unfold cast_left_dioid_to_slt_C,
    cast_A_left_dioid_to_A_slt_C.
    rewrite <-correctness_cast_slt_CI_to_slt_C;
    reflexivity.
  Qed.
 

  Lemma correctness_cast_left_pre_semiring_to_slt_C:
    forall a,
    cast_left_pre_semiring_to_slt_C (A2C_left_pre_semiring a) =
    @A2C_slt_c L S (cast_A_left_pre_semiring_to_A_slt_C a).
  Proof.
    unfold cast_left_pre_semiring_to_slt_C,
    cast_A_left_pre_semiring_to_A_slt_C.
    destruct a; simpl;
    unfold A2C_slt_c; 
    simpl; f_equal.
    rewrite correctness_cast_left_semiring_certificates_to_slt_certificates;
    reflexivity.
  Qed.



  Lemma correctness_cast_left_semiring_to_slt_C :  
    forall a, 
    cast_left_semiring_to_slt_C (A2C_left_semiring a) =
    @A2C_slt_c L S (cast_A_left_semiring_to_A_slt_C a).
  Proof.
    unfold cast_left_semiring_to_slt_C,
    cast_A_left_semiring_to_A_slt_C.
    intro a.
    rewrite <-correctness_cast_left_pre_semiring_to_slt_C;
    reflexivity.
  Qed.

  Lemma correctness_cast_left_selective_semiring_to_slt_C :  
    forall a, 
    cast_left_selective_semiring_to_slt_C (A2C_left_selective_semiring a) =
    @A2C_slt_c L S (cast_A_left_selective_semiring_to_A_slt_C a).
  Proof.
    unfold cast_left_selective_semiring_to_slt_C,
    cast_A_left_selective_semiring_to_A_slt_C.
    intro a.
    rewrite correctness_cast_left_selective_semiring_to_slt_CS.
    unfold cast_slt_CS_to_slt_C,
      A2C_slt_cs,
      cast_A_left_selective_semiring_to_A_slt_CS,
      A2C_slt_c,
      cast_A_slt_CS_to_A_slt_C;
    destruct a; simpl;
    f_equal.
  Qed.
    

  Lemma correctness_cast_left_idempotent_semiring_to_slt_C : 
    forall a, 
    cast_left_idempotent_semiring_to_slt_C (A2C_left_idempotent_semiring a) =
    @A2C_slt_c L S (cast_A_left_idempotent_semiring_to_A_slt_C a).
  Proof.
    unfold cast_left_idempotent_semiring_to_slt_C,
    cast_A_left_idempotent_semiring_to_A_slt_C.
    intro a.
    rewrite <-correctness_cast_left_pre_semiring_to_slt_C;
    f_equal.
    rewrite correctness_cast_left_idempotent_semiring_to_left_pre_semiring;
    reflexivity.
  Qed.
  

    



  Lemma correctness_cast_slt_mcas_to_slt_C : 
    forall pf, 
    cast_slt_mcas_to_slt_C  (A2C_mcas_slt pf) = 
    @A2C_mcas_slt L S (cast_A_slt_mcas_to_A_slt_C pf).
  Proof.
    unfold cast_slt_mcas_to_slt_C,
    cast_A_slt_mcas_to_A_slt_C; 
    destruct pf; simpl;
    try reflexivity;
    f_equal.
    + apply correctness_cast_slt_CI_to_slt_C.
    + apply correctness_cast_left_dioid_to_slt_C.
    + apply correctness_cast_left_pre_semiring_to_slt_C.
    + apply correctness_cast_left_semiring_to_slt_C.
    + apply correctness_cast_left_selective_semiring_to_slt_C.
    + apply correctness_cast_left_idempotent_semiring_to_slt_C.
  Qed.


  Lemma correctness_cast_slt_C_to_slt :  
    forall a, 
    cast_slt_C_to_slt (A2C_slt_c a) = 
    @A2C_slt L S (cast_A_slt_C_to_A_slt a).
  Proof.
    unfold cast_slt_C_to_slt,
    cast_A_slt_C_to_A_slt,
    A2C_slt; destruct a; 
    simpl;
    f_equal.
    erewrite correctness_sg_C_certs_to_sg_certs;
    reflexivity.
    Unshelve. auto.
  Qed.



  Lemma correctness_cast_slt_CS_to_slt: 
    forall a, 
    cast_slt_CS_to_slt (A2C_slt_cs a) = 
    @A2C_slt L S (cast_A_slt_CS_to_A_slt a).
  Proof.
    unfold cast_slt_CS_to_slt,
    cast_A_slt_CS_to_A_slt.
    intros a.
    rewrite <-correctness_cast_slt_C_to_slt;
    reflexivity.
  Qed.


  Lemma correctness_cast_slt_CI_to_slt :  
    forall a, 
    cast_slt_CI_to_slt (A2C_slt_ci a) = 
    @A2C_slt L S (cast_A_slt_CI_to_A_slt a).
  Proof.
    unfold cast_slt_CI_to_slt,
    cast_A_slt_CI_to_A_slt.
    intros a.
    rewrite <-correctness_cast_slt_C_to_slt;
    f_equal.
    rewrite correctness_cast_slt_CI_to_slt_C;
    reflexivity.
  Qed.
  

  Lemma correctness_cast_slt_C_zero_is_ltr_ann_to_slt :  
    forall a, 
    cast_slt_C_zero_is_ltr_ann_to_slt (A2C_slt_C_zero_is_ltr_ann a) =
    @A2C_slt L S (cast_A_slt_C_zero_is_ltr_ann_to_A_slt a).
  Proof.
    unfold cast_slt_C_zero_is_ltr_ann_to_slt,
    cast_A_slt_C_zero_is_ltr_ann_to_A_slt.
    intros a.
    rewrite <-correctness_cast_slt_C_to_slt;
    f_equal.
  Qed.


  Lemma correctness_cast_left_dioid_to_slt :  
    forall a, 
    cast_left_dioid_to_slt (A2C_left_dioid a) =
    @A2C_slt L S (cast_A_left_dioid_to_A_slt a).
  Proof.
    unfold cast_left_dioid_to_slt,
    cast_A_left_dioid_to_A_slt.
    intros a.
    rewrite <-correctness_cast_slt_C_to_slt;
    f_equal.
    rewrite correctness_cast_left_dioid_to_slt_C;
    reflexivity.
  Qed.


  Lemma correctness_cast_selective_left_pre_dioid_to_slt :  
    forall a, 
    cast_selective_left_pre_dioid_to_slt (A2C_selective_left_pre_dioid a) =
    @A2C_slt L S (cast_A_selective_left_pre_dioid_to_A_slt a).
  Proof.
    unfold cast_selective_left_pre_dioid_to_slt,
    cast_A_selective_left_pre_dioid_to_A_slt.
    intro a.
    rewrite <-correctness_cast_slt_C_to_slt;
    f_equal.
  Qed.


  Lemma correctness_cast_selective_left_dioid_to_slt: 
    forall a, 
    cast_selective_left_dioid_to_slt (A2C_selective_left_dioid a) =
    @A2C_slt L S (cast_A_selective_left_dioid_to_A_slt a).
  Proof.
    unfold cast_selective_left_dioid_to_slt,
    cast_A_selective_left_dioid_to_A_slt.
    intros a.
    rewrite <-correctness_cast_slt_C_to_slt;
    f_equal.
  Qed.



  Lemma correctness_cast_left_pre_semiring_to_slt : 
    forall a, 
    cast_left_pre_semiring_to_slt (A2C_left_pre_semiring a) =
    @A2C_slt L S (cast_A_left_pre_semiring_to_A_slt a). 
  Proof.
    unfold cast_left_pre_semiring_to_slt,
    cast_A_left_pre_semiring_to_A_slt.
    intros a.
    rewrite <-correctness_cast_slt_C_to_slt;
    f_equal.
    rewrite correctness_cast_left_pre_semiring_to_slt_C;
    reflexivity.
  Qed.



  Lemma correctness_cast_left_semiring_to_slt :  
    forall a, 
    cast_left_semiring_to_slt (A2C_left_semiring a) =
    @A2C_slt L S (cast_A_left_semiring_to_A_slt a).
  Proof.
    unfold cast_left_semiring_to_slt,
    cast_A_left_semiring_to_A_slt.
    intros a.
    rewrite <-correctness_cast_slt_C_to_slt;
    f_equal.
    rewrite correctness_cast_left_semiring_to_slt_C;
    reflexivity.
  Qed.




  Lemma correctness_cast_left_selective_semiring_to_slt :  
    forall a, 
    cast_left_selective_semiring_to_slt (A2C_left_selective_semiring a) =
    @A2C_slt L S (cast_A_left_selective_semiring_to_A_slt a).
  Proof.
    unfold cast_left_selective_semiring_to_slt,
    cast_A_left_selective_semiring_to_A_slt.
    intros a.
    rewrite <-correctness_cast_slt_C_to_slt;
    f_equal.
    rewrite correctness_cast_left_selective_semiring_to_slt_C;
    reflexivity.
  Qed.

 


  Lemma correctness_cast_left_idempotent_semiring_to_slt:
    forall a, 
    cast_left_idempotent_semiring_to_slt (A2C_left_idempotent_semiring a) =
    @A2C_slt L S (cast_A_left_idempotent_semiring_to_A_slt a).
  Proof.
    unfold cast_left_idempotent_semiring_to_slt,
    cast_A_left_idempotent_semiring_to_A_slt.
    intros a.
    rewrite <-correctness_cast_slt_C_to_slt;
    f_equal.
    rewrite correctness_cast_left_idempotent_semiring_to_slt_C;
    reflexivity.
  Qed.


  Lemma correctness_cast_slt_mcas_to_slt : 
    forall pf, 
    cast_slt_mcas_to_slt (A2C_mcas_slt pf) = 
    @A2C_mcas_slt L S (cast_A_slt_mcas_to_A_slt pf).
  Proof.
    unfold cast_slt_mcas_to_slt,
    cast_A_slt_mcas_to_A_slt;
    destruct pf; simpl; 
    try reflexivity;
    f_equal. 
    + apply correctness_cast_slt_C_to_slt.
    + apply correctness_cast_slt_CS_to_slt.
    + apply correctness_cast_slt_CI_to_slt.
    + apply correctness_cast_slt_C_zero_is_ltr_ann_to_slt.
    + apply correctness_cast_left_dioid_to_slt.
    + apply correctness_cast_selective_left_pre_dioid_to_slt.
    + apply correctness_cast_selective_left_dioid_to_slt.
    + apply correctness_cast_left_pre_semiring_to_slt.
    + apply correctness_cast_left_semiring_to_slt.
    + apply correctness_cast_left_selective_semiring_to_slt.
    + apply correctness_cast_left_idempotent_semiring_to_slt.
  Qed.       


  Lemma cast_A_slt_mcas_to_A_slt_CS_is_A_slt_CS_or_error : 
    forall pf,
    {A : @A_slt_CS L S | cast_A_slt_mcas_to_A_slt_CS pf = A_SLT_CS A} + 
    {l | cast_A_slt_mcas_to_A_slt_CS pf = A_SLT_Error l}.
  Proof.
    destruct pf; simpl;
    try
      (right; eexists;
       reflexivity);
    try
      (left; eexists;
       f_equal).
  Qed.
   

  Lemma cast_A_slt_mcas_to_A_slt_C_is_A_slt_C_or_error : 
    forall pf,
    {A : @A_slt_C L S | cast_A_slt_mcas_to_A_slt_C pf = A_SLT_C A} + 
    {l | cast_A_slt_mcas_to_A_slt_C pf = A_SLT_Error l}.
  Proof.
    destruct pf; simpl;
    try
      (right; eexists;
       reflexivity);
    try
      (left; eexists;
       f_equal).
  Qed.

    
  Lemma cast_A_slt_mcas_to_A_slt_CI_is_A_slt_CI_or_error : 
    forall pf,
    {A : @A_slt_CI L S | cast_A_slt_mcas_to_A_slt_CI pf = A_SLT_CI A} + 
    {l | cast_A_slt_mcas_to_A_slt_CI pf = A_SLT_Error l}.
  Proof.
    destruct pf; simpl;
    try
      (right; eexists;
       reflexivity);
    try
      (left; eexists;
       f_equal).
  Qed. 

  Lemma cast_A_slt_mcas_to_A_slt_C_zero_is_ltr_ann_to_A_slt_C_zero_is_ltr_ann_or_error: 
    forall pf,
    {A : @A_slt_C_zero_is_ltr_ann L S 
      | cast_A_slt_mcas_to_A_slt_C_zero_is_ltr_ann pf = A_SLT_C_Zero_Is_Ltr_ann A} + 
    {l | cast_A_slt_mcas_to_A_slt_C_zero_is_ltr_ann pf = A_SLT_Error l}.
  Proof. 
    destruct pf; simpl;
    try
      (right; eexists;
       reflexivity);
    try
      (left; eexists;
       f_equal).
  Qed.
    
  
  



End Correctness.

