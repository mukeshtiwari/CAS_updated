
Require Import CAS.coq.common.compute.
Require Import CAS.coq.sg.properties. 
Require Import CAS.coq.sg.structures.
Require Import CAS.coq.sg_ltr.structures.

Section AMCAS. 

  Definition A_classify_sg_ltr_S {L S : Type} (A : @A_sg_ltr_S L S) : @A_below_sg_ltr_S L S :=
    A_Below_sg_ltr_S_top A. 

  Definition A_classify_sg_ltr {L S : Type} (A : @A_sg_ltr L S) : @A_below_sg_ltr L S :=
    let addP := A_sg_ltr_plus_props A in
    match A_sg_C_selective_d _ _ _ addP with
    | inl sel =>
        let B :=
          {|
            A_sg_ltr_S_carrier         := A_sg_ltr_carrier A
          ; A_sg_ltr_S_label           := A_sg_ltr_label A
          ; A_sg_ltr_S_plus            := A_sg_ltr_plus A
          ; A_sg_ltr_S_ltr             := A_sg_ltr_ltr A
          ; A_sg_ltr_S_plus_props      :=
              {|
                A_sg_CS_associative := A_sg_C_associative _ _ _ addP
              ; A_sg_CS_congruence  := A_sg_C_congruence _ _ _ addP
              ; A_sg_CS_commutative := A_sg_C_commutative _ _ _ addP
              ; A_sg_CS_selective   := sel                 
              |}
          ; A_sg_ltr_S_ltr_props       := A_sg_ltr_ltr_props A
          ; A_sg_ltr_S_id_ann_props_d  := A_sg_ltr_id_ann_props_d A
          ; A_sg_ltr_S_props           := A_sg_ltr_props A
          ; A_sg_ltr_S_ast             := A_sg_ltr_ast A
          |}
        in A_Below_sg_ltr_sg_ltr_S (A_classify_sg_ltr_S B) 
    | inr _   => A_Below_sg_ltr_top A
    end.
    
End AMCAS. 

Section MCAS. 

  Definition classify_sg_ltr_S {L S : Type} (A : @sg_ltr_S L S) : @below_sg_ltr_S L S :=
    Below_sg_ltr_S_top A. 


  Definition classify_sg_ltr {L S : Type} (A : @sg_ltr L S) : @below_sg_ltr L S :=
    let addP := sg_ltr_plus_props A in
    match sg_C_selective_d addP with
    | Certify_Selective =>
        let B :=
          {|
            sg_ltr_S_carrier         := sg_ltr_carrier A
          ; sg_ltr_S_label           := sg_ltr_label A
          ; sg_ltr_S_plus            := sg_ltr_plus A
          ; sg_ltr_S_ltr             := sg_ltr_ltr A
          ; sg_ltr_S_plus_props      :=
              {|
                sg_CS_associative := sg_C_associative addP
              ; sg_CS_congruence  := sg_C_congruence addP
              ; sg_CS_commutative := sg_C_commutative addP
              ; sg_CS_selective   := Assert_Selective                  
              |}
          ; sg_ltr_S_ltr_props       := sg_ltr_ltr_props A
          ; sg_ltr_S_id_ann_props_d  := sg_ltr_id_ann_props_d A
          ; sg_ltr_S_props           := sg_ltr_props A
          ; sg_ltr_S_ast             := sg_ltr_ast A
          |}
        in Below_sg_ltr_sg_ltr_S (classify_sg_ltr_S B) 
    | Certify_Not_Selective _  => Below_sg_ltr_top A
    end.


End MCAS. 

Section Verify.


  Lemma correct_classify_sg_ltr_S (L S : Type) (A : @A_sg_ltr_S L S) : 
  classify_sg_ltr_S (A2C_sg_ltr_S A)
  =
  A2C_below_sg_ltr_S (A_classify_sg_ltr_S A).
  Proof. destruct A; simpl; reflexivity. Qed. 


  Lemma correct_classify_sg_ltr (L S : Type) (A : @A_sg_ltr L S) : 
  classify_sg_ltr (A2C_sg_ltr A)
  =
    A2C_below_sg_ltr (A_classify_sg_ltr A).
  Proof. destruct A; simpl.
         destruct A_sg_ltr_plus_props.
         destruct A_sg_C_selective_d as [sel | nsel];
           simpl; try reflexivity. 
  Qed.   


End Verify.   
