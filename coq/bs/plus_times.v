Require Import Coq.Arith.Arith.     
Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.

Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.eqv.nat.

Require Import CAS.coq.sg.plus.
Require Import CAS.coq.sg.times.
Require Import CAS.coq.sg.cast_up.

Require Import CAS.coq.bs.properties.
Require Import CAS.coq.bs.structures.
Require Import CAS.coq.bs.theory.
Require Import CAS.coq.bs.classify.

Section Theory.


(* 
   a * (b + c) = (a * b) + (a * c) 
*) 
Lemma A_bs_plus_times_left_distributive : 
        A_bs_left_distributive brel_eq_nat bop_plus bop_times.
Proof. 
    unfold bop_plus, bop_times.
    intros ? ? ?.
    rewrite Nat.mul_add_distr_l.
    unfold brel_eq_nat.
    apply Nat.eqb_refl.
Defined.

Lemma A_bs_plus_times_right_distributive : 
        A_bs_right_distributive brel_eq_nat bop_plus bop_times.
Proof. apply bops_left_distributive_and_times_commutative_imply_right_distributive. 
       apply brel_eq_nat_congruence. 
       apply bop_plus_congruence. 
       apply bop_times_commutative. 
       apply A_bs_plus_times_left_distributive. 
Defined.


(* dual of distributivity 

   a + (b * c) <> (a + b) * (a + c) 
*) 
Lemma A_bs_times_plus_not_left_distributive : 
        A_bs_not_left_distributive brel_eq_nat bop_times bop_plus.
Proof. exists (1, (1, 0)). compute. reflexivity. Defined. 


Lemma A_bs_times_plus_not_right_distributive : 
        A_bs_not_right_distributive brel_eq_nat bop_times bop_plus.
Proof. exists (1, (1, 0)). compute. reflexivity. Defined. 


(* absorption *) 

(* a <> a + (a * b) *) 
Lemma A_bs_plus_times_not_left_absorptive : 
        A_bs_not_left_absorptive brel_eq_nat bop_plus bop_times.   
Proof. exists (1, 1). compute. reflexivity. Defined.

Lemma A_bs_plus_times_not_right_absorptive : 
        A_bs_not_right_absorptive brel_eq_nat bop_plus bop_times.   
Proof. exists (1, 1). compute. reflexivity. Defined. 

(* dual 
a <> a * (a + b) *)
Lemma A_bops_times_plus_not_left_absorptive : 
        A_bs_not_left_absorptive brel_eq_nat bop_times bop_plus.   
Proof. exists (1, 1). compute. reflexivity. Defined.

(*
Lemma bops_plus_times_not_right_left_absorptive : 
        bops_not_right_left_absorptive nat brel_eq_nat bop_plus bop_times.   
Proof. exists (1, 1). compute. reflexivity. Defined. 

Lemma bops_plus_times_not_right_right_absorptive : 
        bops_not_right_right_absorptive nat brel_eq_nat bop_plus bop_times.   
Proof. exists (1, 1). compute. reflexivity. Defined. 
*) 
(* strict absorption 
Lemma bops_plus_times_not_left_strictly_absorptive : 
  bops_not_left_strictly_absorptive nat 
    brel_eq_nat bop_plus bop_times.   
Proof. exists (1, 1). compute.
  left. reflexivity.  Defined. 


Lemma bops_plus_times_not_right_strictly_absorptive : 
  bops_not_right_strictly_absorptive nat 
    brel_eq_nat bop_plus bop_times.   
Proof. exists (1, 1). compute.
  left. reflexivity.  Defined. 

*)


Lemma A_bs_plus_times_exists_id_ann_equal :
  A_bs_exists_id_ann_equal brel_eq_nat bop_plus bop_times.
Proof. exists 0. split.
       + apply bop_plus_zero_is_id.
       + apply bop_times_zero_is_ann.
Defined. 

End Theory.

Section ACAS.



Definition A_bs_plus_times_properties : A_bs_properties brel_eq_nat bop_plus bop_times :=
  {| 
    A_bs_left_distributive_d  := inl A_bs_plus_times_left_distributive
  ; A_bs_right_distributive_d := inl A_bs_plus_times_right_distributive
  ; A_bs_left_absorptive_d    := inr A_bs_plus_times_not_left_absorptive
  ; A_bs_right_absorptive_d   := inr A_bs_plus_times_not_right_absorptive
  |}.

Definition A_bs_plus_times : @A_bs nat :=
let eqv := A_eqv_nat in
let eq  := A_eqv_eq _ eqv in
let w   := A_eqv_witness _ eqv in
let f   := A_eqv_new _ eqv in
let nt  := A_eqv_not_trivial _ eqv in
let eqvP := A_eqv_proofs _ eqv in 
{|
  A_bs_eqv          := eqv 
; A_bs_plus         := bop_plus
; A_bs_times        := bop_times 
; A_bs_plus_props   := A_sg_C_proofs_plus
; A_bs_times_props  := A_sg_proofs_from_sg_C_proofs _
                         eq bop_times w f nt eqvP 
                         sg_C_proofs_times 
; A_bs_id_ann_props :=
    {|
      A_id_ann_plus_times_d := A_Id_Ann_Equal _ _ _ A_bs_plus_times_exists_id_ann_equal
    ; A_id_ann_times_plus_d := A_Id_Ann_Id_None _ _ _ (bop_times_exists_id, bop_plus_not_exists_ann)
    |}
; A_bs_props        := A_bs_plus_times_properties
; A_bs_ast          := Ast_plus_times 
|}.
End ACAS.

Section MACAS.

Definition A_mcas_plus_times := A_MCAS_bs (A_classify_bs A_bs_plus_times). 

End MACAS.
  
Section CAS.


Definition bs_plus_times_not_left_absorptive :=
    BS_Not_Left_Absorptive (1, 1).

Definition bs_plus_times_not_right_absorptive :=
    BS_Not_Right_Absorptive (1, 1).

Definition bs_plus_times_exists_id_ann_equal :=
  0. 
  
Definition bs_plus_times_properties : @bs_properties nat := 
  {| 
    bs_left_distributive_d  := inl (BS_Left_Distributive 0) 
  ; bs_right_distributive_d := inl (BS_Right_Distributive 0)
  ; bs_left_absorptive_d    := inr bs_plus_times_not_left_absorptive
  ; bs_right_absorptive_d   := inr bs_plus_times_not_right_absorptive
  |}.

Definition bs_plus_times : @bs nat :=
let eqv := eqv_eq_nat in
let eq  := eqv_eq eqv in
let w   := eqv_witness eqv in
let f   := eqv_new eqv in
{|
  bs_eqv          := eqv 
; bs_plus         := bop_plus
; bs_times        := bop_times 
; bs_plus_props   := sg_C_certs_plus
; bs_times_props  := sg_certs_from_sg_C_certs _
                         eq bop_times w f 
                         sg_C_certs_times 
; bs_id_ann_props :=
    {|
      id_ann_plus_times_d := Id_Ann_Equal bs_plus_times_exists_id_ann_equal
    ; id_ann_times_plus_d := Id_Ann_Id_None 1 (* ? *) 
    |}
; bs_props        := bs_plus_times_properties
; bs_ast          := Ast_plus_times 
|}.

End CAS.

Section MCAS.

Definition mcas_plus_times := MCAS_bs (classify_bs bs_plus_times). 

End MCAS.
  
Section Verify.

Theorem correct_plus_times : 
  bs_plus_times
  =
  A2C_bs A_bs_plus_times. 
Proof. compute. reflexivity. Qed.


Theorem correct_mcas_plus_times :
  mcas_plus_times
  =
  A2C_bs_mcas A_mcas_plus_times.
Proof. compute. reflexivity. Qed. 


End Verify.   
