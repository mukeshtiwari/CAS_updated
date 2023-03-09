Require Import Coq.Arith.Arith.     (* beq_nat *) 

Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.

Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.eqv.nat.

Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures.
Require Import CAS.coq.sg.theory.
Require Import CAS.coq.sg.max.
Require Import CAS.coq.sg.plus.
Require Import CAS.coq.sg.cast_up.

Require Import CAS.coq.bs.properties.
Require Import CAS.coq.bs.structures.
Require Import CAS.coq.bs.theory.
Require Import CAS.coq.bs.classify.

Section Theory.

Open Scope nat.   

Lemma max_add_l : ∀ u s : nat, u + s = max (u + s) s. 
Proof. induction u; induction s; simpl. 
       reflexivity. 
       simpl in IHs. rewrite <- IHs. reflexivity. 
       reflexivity. 
       apply injection_S. rewrite plus_Snm_nSm in IHs. assumption. 
Defined. 

Lemma max_add_r : ∀ u s : nat, u + s = max s (u + s). 
Proof. induction u; induction s; simpl. 
       reflexivity. 
       simpl in IHs. rewrite <- IHs. reflexivity. 
       reflexivity. 
       apply injection_S. rewrite plus_Snm_nSm in IHs. assumption. 
Defined. 

Lemma max_0_l : ∀ s : nat, s = max s 0. 
Proof. induction s; simpl; reflexivity. Qed. 

Lemma max_0_r : ∀ s : nat, s = max 0 s. 
Proof. intro s; compute. reflexivity. Qed. 

Lemma plus_0 : ∀ s : nat, s = s + 0. 
Proof. induction s; simpl. reflexivity. rewrite <- IHs. reflexivity. Qed. 


Lemma S_cong : ∀ s t : nat, brel_eq_nat s t = true -> brel_eq_nat (S s) (S t) = true. 
Proof. induction s; induction t; simpl; auto. Qed. 

Lemma S_cong_neg : ∀ s t : nat, brel_eq_nat s t = false -> brel_eq_nat (S s) (S t) = false. 
Proof. induction s; induction t; simpl; auto. Qed. 

(* distributivity *) 

(* a + (b max c) = (a + c) max (b + c) *) 
Lemma A_bs_max_plus_left_distributive : 
        A_bs_left_distributive brel_eq_nat bop_max bop_plus. 
Proof. unfold A_bs_left_distributive, bop_plus, bop_max. 
       induction s. 
          intros t u. simpl. apply brel_eq_nat_reflexive.
          induction t. 
             simpl. rewrite plus_comm. simpl. intro u.  
             rewrite Max.max_comm. rewrite plus_comm. rewrite <- max_add_l. 
             apply brel_eq_nat_reflexive.
             induction u; simpl. 
                rewrite <- plus_0. rewrite plus_comm. rewrite <- max_add_l. 
                apply brel_eq_nat_reflexive.
                rewrite <- plus_n_Sm. rewrite <- plus_n_Sm. rewrite <- plus_n_Sm. 
                rewrite bop_max_S. 
                apply S_cong. unfold bop_max. 
                apply IHs. 
Qed. 


Lemma A_bs_max_plus_right_distributive : 
        A_bs_right_distributive brel_eq_nat bop_max bop_plus. 
Proof. apply bops_left_distributive_and_times_commutative_imply_right_distributive. 
       apply brel_eq_nat_congruence. 
       apply bop_max_congruence. 
       apply bop_plus_commutative. 
       apply A_bs_max_plus_left_distributive. 
Defined.


(* dual 
a max (b + c) <> (a max b) + (a max c) *) 
Lemma A_bs_plus_max_not_left_distributive : 
        A_bs_not_left_distributive brel_eq_nat bop_plus bop_max. 
Proof. exists (1, (0, 0)). compute. reflexivity. Defined. 

Lemma A_bs_plus_max_not_right_distributive : 
        A_bs_not_right_distributive brel_eq_nat bop_plus bop_max. 
Proof. exists (1, (0, 0)). compute. reflexivity. Defined. 


(* absorption *) 

(* a <> max a (a + b) *) 
Lemma A_bs_max_plus_not_left_absorptive : 
        A_bs_not_left_absorptive brel_eq_nat bop_max bop_plus. 
Proof. exists (0,1); compute. reflexivity. Defined.

Lemma A_bs_max_plus_not_right_absorptive : 
        A_bs_not_right_absorptive brel_eq_nat bop_max bop_plus. 
Proof. exists (0, 1); compute. reflexivity. Defined. 

(* dual 
a <> a + (a max b) *) 
Lemma A_bs_plus_max_not_left_left_absorptive : 
        A_bs_not_left_absorptive brel_eq_nat bop_plus bop_max. 
Proof. exists (0,1); compute. reflexivity. Defined. 

Lemma A_bs_plus_max_not_left_right_absorptive : 
        A_bs_not_right_absorptive brel_eq_nat bop_plus bop_max. 
Proof. exists (0, 1); compute. reflexivity. Defined. 

(*
Lemma A_bs_max_plus_not_right_left_absorptive : 
        A_bs_not_right_left_absorptive nat brel_eq_nat bop_max bop_plus. 
Proof. exists (0, 1); compute. reflexivity. Defined.

Lemma A_bs_plus_max_not_right_left_absorptive : 
        A_bs_not_right_left_absorptive nat brel_eq_nat bop_plus bop_max. 
Proof. exists (0, 1); compute. reflexivity. Defined. 

Lemma A_bs_max_plus_not_right_right_absorptive : 
        A_bs_not_right_right_absorptive nat brel_eq_nat bop_max bop_plus. 
Proof. exists (0, 1); compute. reflexivity. Defined.

Lemma A_bs_plus_max_not_right_right_absorptive : 
        A_bs_not_right_right_absorptive nat brel_eq_nat bop_plus bop_max. 
Proof. exists (0, 1); compute. reflexivity. Defined. 
*) 
(* strict absorption 
Lemma A_bs_max_plus_not_left_strictly_absorptive : 
  A_bs_not_left_strictly_absorptive nat brel_eq_nat bop_max bop_plus. 
Proof. exists (0, 1); compute; right. reflexivity. Defined.

Lemma A_bs_max_plus_not_right_strictly_absorptive : 
  A_bs_not_right_strictly_absorptive nat brel_eq_nat bop_max bop_plus. 
Proof. exists (0, 1); compute; right. reflexivity. Defined.
*)




End Theory.

Section ACAS.

  Definition A_bs_max_plus_properties : A_bs_properties brel_eq_nat bop_max bop_plus := 
  {| 
     A_bs_left_distributive_d  := inl A_bs_max_plus_left_distributive
   ; A_bs_right_distributive_d := inl A_bs_max_plus_right_distributive
   ; A_bs_left_absorptive_d    := inr A_bs_max_plus_not_left_absorptive
   ; A_bs_right_absorptive_d   := inr A_bs_max_plus_not_right_absorptive
  |}.


Definition A_bs_max_plus : @A_bs nat :=
let eqv := A_eqv_nat in
let eq  := A_eqv_eq _ eqv in
let w   := A_eqv_witness _ eqv in
let f   := A_eqv_new _ eqv in
let nt  := A_eqv_not_trivial _ eqv in
let eqvP := A_eqv_proofs _ eqv in 
{|
  A_bs_eqv          := eqv 
; A_bs_plus         := bop_max
; A_bs_times        := bop_plus 
; A_bs_plus_props   := A_sg_C_proofs_from_sg_CS_proofs _
                         eq bop_max w f nt eqvP 
                         sg_CS_proofs_max
; A_bs_times_props  := A_sg_proofs_from_sg_C_proofs _
                         eq bop_plus w f nt eqvP 
                         A_sg_C_proofs_plus
; A_bs_id_ann_props :=
    {|
      A_id_ann_plus_times_d := A_Id_Ann_Id_None _ _ _ (bop_max_exists_id, bop_plus_not_exists_ann)
    ; A_id_ann_times_plus_d := A_Id_Ann_Id_None _ _ _ (bop_plus_exists_id, bop_max_not_exists_ann)
    |}
; A_bs_props        := A_bs_max_plus_properties
; A_bs_ast          := Ast_max_plus
|}.


End ACAS.

Section AMCAS.

  Definition A_mcas_bs_max_plus := A_MCAS_bs (A_classify_bs A_bs_max_plus).
  
End AMCAS.


Section CAS.

  Open Scope nat.

  Definition bs_min_plus_properties : @bs_properties nat := 
  {| 
     bs_left_distributive_d  := inl (BS_Left_Distributive 0)
   ; bs_right_distributive_d := inl (BS_Right_Distributive 0) 
   ; bs_left_absorptive_d    := inr (BS_Not_Left_Absorptive (0, 1))
   ; bs_right_absorptive_d   := inr (BS_Not_Right_Absorptive (0, 1))
  |}.

Definition bs_max_plus : @bs nat :=
let eqv := eqv_eq_nat in
let eq  := eqv_eq eqv in
let w   := eqv_witness eqv in
let f   := eqv_new eqv in
{|
  bs_eqv          := eqv 
; bs_plus         := bop_max
; bs_times        := bop_plus 
; bs_plus_props   := sg_C_certs_from_sg_CS_certs _
                         eq bop_max w f 
                         sg_CS_certs_max
; bs_times_props  := sg_certs_from_sg_C_certs _
                         eq bop_plus w f 
                         sg_C_certs_plus
; bs_id_ann_props :=
    {|
      id_ann_plus_times_d := Id_Ann_Id_None 0
    ; id_ann_times_plus_d := Id_Ann_Id_None 0
    |}
; bs_props        := bs_min_plus_properties
; bs_ast          := Ast_max_plus
|}.
  

End CAS.

Section MCAS.

  Definition mcas_bs_max_plus := MCAS_bs (classify_bs bs_max_plus).

End MCAS.



Section Verify.

Theorem correct_bs_max_plus : 
  bs_max_plus
  =
  A2C_bs (A_bs_max_plus). 
Proof. compute. reflexivity. Qed.

Theorem correct_mcas_bs_max_plus :
  mcas_bs_max_plus
  =
  A2C_bs_mcas A_mcas_bs_max_plus.
Proof. compute. reflexivity. Qed. 


End Verify.   
  
