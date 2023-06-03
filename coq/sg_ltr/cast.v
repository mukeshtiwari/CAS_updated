Require Import CAS.coq.common.compute.
Require Import CAS.coq.eqv.structures. 
Require Import CAS.coq.sg.properties. 
Require Import CAS.coq.sg.structures. 
Require Import CAS.coq.sg.classify.
Require Import CAS.coq.sg.cast_up.
Require Import CAS.coq.sg_ltr.structures.
Require Import CAS.coq.sg_ltr.classify. 

Section AMCAS. 

  
  Definition A_sg_ltr_from_sg_ltr_S {L S : Type} (A : @A_sg_ltr_S L S) : @A_sg_ltr L S :=
    let eqvS := A_sg_ltr_S_carrier A in
    let eqvP := A_eqv_proofs _ eqvS in    
    let wS   := A_eqv_witness _ eqvS in
    let f    := A_eqv_new _ eqvS in
    let nt   := A_eqv_not_trivial _ eqvS in  
    {|
      A_sg_ltr_carrier        := eqvS 
    ; A_sg_ltr_label          := A_sg_ltr_S_label A 
    ; A_sg_ltr_plus           := A_sg_ltr_S_plus A
    ; A_sg_ltr_ltr            := A_sg_ltr_S_ltr A
    ; A_sg_ltr_plus_props     :=
        A_sg_C_proofs_from_sg_CS_proofs _ _ _ wS f nt eqvP (A_sg_ltr_S_plus_props A)
    ; A_sg_ltr_ltr_props      := A_sg_ltr_S_ltr_props A
    ; A_sg_ltr_id_ann_props_d := A_sg_ltr_S_id_ann_props_d A
    ; A_sg_ltr_props          := A_sg_ltr_S_props A
    ; A_sg_ltr_ast            := A_sg_ltr_S_ast A
    |}.
  
    
  
  Definition A_cast_up_sg_ltr_S {L S : Type}
    (A : @A_below_sg_ltr_S L S) : @A_sg_ltr_S L S :=
    match A with 
    | A_Below_sg_ltr_S_top B => B
    end.
  
  Definition A_cast_up_sg_ltr {L S : Type} (A : @A_below_sg_ltr L S) : @A_sg_ltr L S :=
    match A with 
    | A_Below_sg_ltr_top B      => B
    | A_Below_sg_ltr_sg_ltr_S B =>
        A_sg_ltr_from_sg_ltr_S (A_cast_up_sg_ltr_S B) 
    end.


    Definition A_cast_below_sg_ltr_to_below_sg_ltr_S {L S : Type}
    (A : @A_below_sg_ltr L S) : option (@A_below_sg_ltr_S L S) :=
    match A with
    | A_Below_sg_ltr_top _   => None
    | A_Below_sg_ltr_sg_ltr_S B => Some B 
    end. 

    
  
End AMCAS. 

Section MCAS.

  Definition sg_ltr_from_sg_ltr_S {L S : Type} (A : @sg_ltr_S L S) : @sg_ltr L S :=
    let eqvS := sg_ltr_S_carrier A in
    let eqvP := eqv_certs eqvS in
    let eqS  := eqv_eq eqvS in        
    let wS   := eqv_witness eqvS in
    let f    := eqv_new eqvS in
    let add  := sg_ltr_S_plus A in 
    {|
      sg_ltr_carrier        := eqvS 
    ; sg_ltr_label          := sg_ltr_S_label A 
    ; sg_ltr_plus           := sg_ltr_S_plus A
    ; sg_ltr_ltr            := sg_ltr_S_ltr A
    ; sg_ltr_plus_props     :=
        sg_C_certs_from_sg_CS_certs _ eqS add wS f (sg_ltr_S_plus_props A)
    ; sg_ltr_ltr_props      := sg_ltr_S_ltr_props A
    ; sg_ltr_id_ann_props_d := sg_ltr_S_id_ann_props_d A
    ; sg_ltr_props          := sg_ltr_S_props A
    ; sg_ltr_ast            := sg_ltr_S_ast A
    |}.
  
    
  
  Definition cast_up_sg_ltr_S {L S : Type}
    (A : @below_sg_ltr_S L S) : @sg_ltr_S L S :=
    match A with 
    | Below_sg_ltr_S_top B => B
    end.
  
  Definition cast_up_sg_ltr {L S : Type} (A : @below_sg_ltr L S) : @sg_ltr L S :=
    match A with 
    | Below_sg_ltr_top B      => B
    | Below_sg_ltr_sg_ltr_S B =>
        sg_ltr_from_sg_ltr_S (cast_up_sg_ltr_S B) 
    end.
  
    Definition cast_below_sg_ltr_to_below_sg_ltr_S {L S : Type}
    (A : @below_sg_ltr L S) : option (@below_sg_ltr_S L S) :=
    match A with
    | Below_sg_ltr_top _   => None
    | Below_sg_ltr_sg_ltr_S B => Some B 
    end. 
  
End MCAS. 

Section Commute.

  Lemma correct_sg_ltr_from_sg_ltr_S (L S : Type) (A : @A_sg_ltr_S L S) :
    A2C_sg_ltr (A_sg_ltr_from_sg_ltr_S A)
    =                
    sg_ltr_from_sg_ltr_S (A2C_sg_ltr_S A). 
  Proof. destruct A; unfold A2C_sg_ltr_S, A2C_sg_ltr,
           A_sg_ltr_from_sg_ltr_S, sg_ltr_from_sg_ltr_S; simpl.
         rewrite <- correct_sg_C_certs_from_sg_CS_certs. 
         reflexivity.
  Qed.
  
 Lemma cast_up_sg_ltr_S_A2C_commute (L S : Type)
   (A : @A_below_sg_ltr_S L S) :         
  cast_up_sg_ltr_S (A2C_below_sg_ltr_S A)
  =
  A2C_sg_ltr_S (A_cast_up_sg_ltr_S A).
  Proof. destruct A; simpl; reflexivity. Qed. 

Lemma cast_up_sg_ltr_A2C_commute (L S : Type) (A : @A_below_sg_ltr L S) : 
  cast_up_sg_ltr (A2C_below_sg_ltr A)
  =
  A2C_sg_ltr (A_cast_up_sg_ltr A).
Proof. destruct A; unfold cast_up_sg_ltr, A_cast_up_sg_ltr; simpl.
       - reflexivity.
       - rewrite correct_sg_ltr_from_sg_ltr_S . 
         rewrite cast_up_sg_ltr_S_A2C_commute. 
         reflexivity.
Qed.
  

End Commute. 
