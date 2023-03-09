
Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.

Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.eqv.bool.

Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures.
Require Import CAS.coq.sg.cast_up. 
Require Import CAS.coq.sg.or.
Require Import CAS.coq.sg.and.

Require Import CAS.coq.bs.properties.
Require Import CAS.coq.bs.structures.
Require Import CAS.coq.bs.classify. 

Section Theory.

  Lemma A_bs_and_or_left_distributive  :
     A_bs_left_distributive brel_eq_bool bop_and bop_or. 
  Proof. intros x y z.
         destruct x; destruct y; destruct z; compute; reflexivity.
  Qed. 

Lemma A_bs_and_or_right_distributive  : 
     A_bs_right_distributive brel_eq_bool bop_and bop_or.
Proof. intros x y z.
       destruct x; destruct y; destruct z; compute; reflexivity.
Qed. 

Lemma A_bs_and_or_left_absorptive  : 
     A_bs_left_absorptive brel_eq_bool bop_and bop_or.
Proof. intros x y. destruct x; destruct y; compute; reflexivity. Qed. 

Lemma A_bs_and_or_right_absorptive  : 
     A_bs_right_absorptive brel_eq_bool bop_and bop_or.
Proof. intros x y. destruct x; destruct y; compute; reflexivity. Qed. 

(* strict absorption 
Lemma A_bs_and_or_not_left_strictly_absorptive  : 
     A_bs_not_left_strictly_absorptive bool brel_eq_bool A_bs_and A_bs_or.
Proof. exists (true, true). compute. right. auto. Defined. 

Lemma A_bs_and_or_not_right_strictly_absorptive  : 
     A_bs_not_right_strictly_absorptive bool brel_eq_bool A_bs_and A_bs_or.
Proof. exists (true, true). compute. right. auto. Defined.
 

Lemma A_bs_and_or_right_left_absorptive  : 
     A_bs_right_left_absorptive bool brel_eq_bool A_bs_and A_bs_or.
Proof. intros x y. destruct x; destruct y; compute; reflexivity. Qed. 

Lemma A_bs_and_or_right_right_absorptive  : 
     A_bs_right_right_absorptive bool brel_eq_bool A_bs_and A_bs_or.
Proof. intros x y. destruct x; destruct y; compute; reflexivity. Qed. 

*)
Lemma A_bs_and_or_exists_id_ann_equal : A_bs_exists_id_ann_equal brel_eq_bool bop_and bop_or. 
Proof. exists true. split. apply bop_and_true_is_id. apply bop_or_true_is_ann. Defined. 

Lemma A_bs_or_and_exists_id_ann_equal : A_bs_exists_id_ann_equal brel_eq_bool bop_or bop_and.
Proof. exists false. split. apply bop_or_false_is_id. apply bop_and_false_is_ann. Defined.

(* dual *) 
Lemma A_bs_or_and_left_absorptive  : 
     A_bs_left_absorptive brel_eq_bool bop_or bop_and.
Proof. intros x y. destruct x; destruct y; compute; reflexivity. Qed. 

End Theory.

Section ACAS.
  
Definition A_bs_and_or_properties : A_bs_properties brel_eq_bool bop_and bop_or := 
  {| 
     A_bs_left_distributive_d  := inl A_bs_and_or_left_distributive
   ; A_bs_right_distributive_d := inl A_bs_and_or_right_distributive
   ; A_bs_left_absorptive_d    := inl A_bs_and_or_left_absorptive
   ; A_bs_right_absorptive_d   := inl A_bs_and_or_right_absorptive
  |}.


Definition A_bs_and_or : @A_bs bool :=
let eqv := A_eqv_bool in
let eq  := A_eqv_eq _ eqv in
let w   := A_eqv_witness _ eqv in
let f   := A_eqv_new _ eqv in
let nt  := A_eqv_not_trivial _ eqv in
let eqvP := A_eqv_proofs _ eqv in 
{|
  A_bs_eqv          := eqv 
; A_bs_plus         := bop_and
; A_bs_times        := bop_or
; A_bs_plus_props   := A_sg_C_proofs_from_sg_CS_proofs _
                         eq bop_and w f nt eqvP 
                         sg_CS_proofs_and
; A_bs_times_props  := A_sg_proofs_from_sg_CS_proofs _
                         eq bop_or w f nt eqvP 
                         sg_CS_proofs_or 
; A_bs_id_ann_props :=
    {|
      A_id_ann_plus_times_d := A_Id_Ann_Equal _ _ _ A_bs_and_or_exists_id_ann_equal
    ; A_id_ann_times_plus_d := A_Id_Ann_Equal _ _ _ A_bs_or_and_exists_id_ann_equal
    |}
; A_bs_props        := A_bs_and_or_properties
; A_bs_ast          := Ast_and_or
|}.

End ACAS.

Section AMCAS.


Definition A_mcas_bs_and_or := A_MCAS_bs (A_classify_bs A_bs_and_or).   
  
End AMCAS.   

Section CAS.

Definition bs_and_or_properties : @bs_properties bool := 
  {| 
     bs_left_distributive_d  := inl (BS_Left_Distributive true)
   ; bs_right_distributive_d := inl (BS_Right_Distributive true)
   ; bs_left_absorptive_d    := inl (BS_Left_Absorptive true)
   ; bs_right_absorptive_d   := inl (BS_Right_Absorptive true)
  |}.
  

Definition bs_and_or : @bs bool :=
let eqv := eqv_bool in
let eq  := eqv_eq eqv in
let w   := eqv_witness eqv in
let f   := eqv_new eqv in
{|
  bs_eqv          := eqv 
; bs_plus         := bop_and
; bs_times        := bop_or
; bs_plus_props   := sg_C_certs_from_sg_CS_certs _
                         eq bop_and w f 
                         sg_CS_certs_and
; bs_times_props  := sg_certs_from_sg_CS_certs _
                         eq bop_or w f 
                         sg_CS_certs_or 
; bs_id_ann_props :=
    {|
      id_ann_plus_times_d := Id_Ann_Equal true 
    ; id_ann_times_plus_d := Id_Ann_Equal false 
    |}
; bs_props        := bs_and_or_properties
; bs_ast          := Ast_and_or
|}.


End CAS.

Section MCAS.

Definition mcas_bs_and_or := MCAS_bs (classify_bs bs_and_or).   
  
End MCAS.   


Section Verify.

Theorem correct_bs_and_or : bs_and_or = A2C_bs (A_bs_and_or). 
Proof. compute. reflexivity. Qed. 

Theorem correct_mcas_bs_and_or : mcas_bs_and_or = A2C_bs_mcas A_mcas_bs_and_or.
Proof. compute. reflexivity. Qed. 

 
End Verify.   
  
