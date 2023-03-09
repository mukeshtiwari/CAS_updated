Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.

Require Import CAS.coq.eqv.nat.
Require Import CAS.coq.eqv.structures. 

Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures. 
Require Import CAS.coq.sg.cast_up. 
Require Import CAS.coq.sg.max.
Require Import CAS.coq.sg.min.

Require Import CAS.coq.bs.properties.
Require Import CAS.coq.bs.structures.
Require Import CAS.coq.bs.classify. 
Require Import CAS.coq.bs.theory. 

Section Theory.

Lemma A_bs_max_min_left_absorptive  : 
     A_bs_left_absorptive brel_eq_nat bop_max bop_min. 
Proof. unfold A_bs_left_absorptive. 
       induction s; induction t; simpl; auto. 
       apply brel_eq_nat_reflexive. 
Qed.

Lemma A_bs_max_min_right_absorptive  : 
       A_bs_right_absorptive brel_eq_nat bop_max bop_min. 
Proof. unfold A_bs_right_absorptive. 
       induction s; induction t; simpl; auto. 
       apply brel_eq_nat_reflexive. 
Qed.

Lemma A_bs_max_min_left_distributive  : 
     A_bs_left_distributive brel_eq_nat bop_max bop_min. 
Proof. unfold A_bs_left_distributive. 
       induction s; induction t; induction u; simpl; auto. 
       apply brel_eq_nat_reflexive. 
       apply brel_eq_nat_symmetric. 
       apply brel_eq_nat_reflexive. 
Qed. 

Lemma A_bs_max_min_right_distributive  : 
     A_bs_right_distributive brel_eq_nat bop_max bop_min. 
Proof. apply bs_left_distributive_implies_right. 
       exact brel_eq_nat_transitive. 
       exact bop_max_congruence. 
       exact bop_max_commutative. 
       exact bop_min_commutative. 
       exact A_bs_max_min_left_distributive. 
Qed. 

(* strict absorption 
Lemma A_bs_max_min_not_left_strictly_absorptive  : 
  A_bs_not_left_strictly_absorptive nat brel_eq_nat bop_max bop_min.
Proof.
  exists (0, 0)%nat.
  compute.
  right; auto.
Qed. 

Lemma A_bs_max_min_not_right_strictly_absorptive  : 
  A_bs_not_right_strictly_absorptive nat brel_eq_nat bop_max bop_min.
Proof.
  exists (0, 0)%nat.
  compute.
  right; auto.
Qed.
 *)
Open Scope nat.


Lemma A_bs_max_min_id_ann_equal : A_bs_exists_id_ann_equal brel_eq_nat bop_max bop_min.
Proof. exists 0. split.
       + apply bop_max_zero_is_id.
       + apply bop_min_zero_is_ann.
Defined.

End Theory.

Section ACAS.

Open Scope nat.

  Definition A_bs_max_min_properties : A_bs_properties brel_eq_nat bop_max bop_min := 
  {| 
     A_bs_left_distributive_d  := inl A_bs_max_min_left_distributive
   ; A_bs_right_distributive_d := inl A_bs_max_min_right_distributive
   ; A_bs_left_absorptive_d    := inl A_bs_max_min_left_absorptive
   ; A_bs_right_absorptive_d   := inl A_bs_max_min_right_absorptive
  |}.


Definition A_bs_max_min : @A_bs nat :=
let eqv := A_eqv_nat in
let eq  := A_eqv_eq _ eqv in
let w   := A_eqv_witness _ eqv in
let f   := A_eqv_new _ eqv in
let nt  := A_eqv_not_trivial _ eqv in
let eqvP := A_eqv_proofs _ eqv in 
{|
  A_bs_eqv          := eqv 
; A_bs_plus         := bop_max
; A_bs_times        := bop_min
; A_bs_plus_props   := A_sg_C_proofs_from_sg_CS_proofs _
                         eq bop_max w f nt eqvP 
                         sg_CS_proofs_max
; A_bs_times_props  := A_sg_proofs_from_sg_CS_proofs _
                         eq bop_min w f nt eqvP 
                         sg_CS_proofs_min
; A_bs_id_ann_props :=
    {|
      A_id_ann_plus_times_d := A_Id_Ann_Equal _ _ _ A_bs_max_min_id_ann_equal
    ; A_id_ann_times_plus_d := A_Id_Ann_None _ _ _ (bop_min_not_exists_id, bop_max_not_exists_ann) 
    |}
; A_bs_props        := A_bs_max_min_properties
; A_bs_ast          := Ast_max_min
|}.

End ACAS.

Section MACAS.

  Definition A_mcas_bs_max_min := A_MCAS_bs (A_classify_bs A_bs_max_min). 

End MACAS.


Section CAS.
Open Scope nat.

Definition bs_max_min_properties : @bs_properties nat := 
  {| 
     bs_left_distributive_d  := inl (BS_Left_Distributive  0)
   ; bs_right_distributive_d := inl (BS_Right_Distributive 0)
   ; bs_left_absorptive_d    := inl (BS_Left_Absorptive  0)
   ; bs_right_absorptive_d   := inl (BS_Right_Absorptive  0)
  |}.

Definition bs_max_min : @bs nat :=
let eqv := eqv_eq_nat in
let eq  := eqv_eq eqv in
let w   := eqv_witness eqv in
let f   := eqv_new eqv in
{|
  bs_eqv          := eqv 
; bs_plus         := bop_max
; bs_times        := bop_min
; bs_plus_props   := sg_C_certs_from_sg_CS_certs _
                         eq bop_max w f 
                         sg_CS_certs_max
; bs_times_props  := sg_certs_from_sg_CS_certs _
                         eq bop_min w f 
                         sg_CS_certs_min
; bs_id_ann_props :=
    {|
      id_ann_plus_times_d := Id_Ann_Equal 0 
    ; id_ann_times_plus_d := Id_Ann_None 
    |}
; bs_props        := bs_max_min_properties
; bs_ast          := Ast_max_min
|}.


End CAS.

Section MACAS.

  Definition mcas_bs_max_min := MCAS_bs (classify_bs bs_max_min). 

End MACAS.



Section Verify.

Theorem correct_max_min : bs_max_min = A2C_bs A_bs_max_min. 
Proof. compute. reflexivity. Qed. 

Theorem correct_mcas_max_min : mcas_bs_max_min = A2C_bs_mcas A_mcas_bs_max_min.
Proof. compute. reflexivity. Qed. 


End Verify.   
  

