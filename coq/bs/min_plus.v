Require Import Coq.Arith.Arith.     
Require Import Coq.Arith.Min.

Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.

Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.eqv.nat.

Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures.
Require Import CAS.coq.sg.theory.
Require Import CAS.coq.sg.min.
Require Import CAS.coq.sg.plus.
Require Import CAS.coq.sg.cast_up.

Require Import CAS.coq.bs.properties.
Require Import CAS.coq.bs.structures.
Require Import CAS.coq.bs.theory.
Require Import CAS.coq.bs.classify.

Section Theory.

Open Scope nat.   

Lemma min_add : ∀ u s : nat, min (u + s) s = s. 
Proof. induction u; induction s; simpl. 
       reflexivity. 
       simpl in IHs. rewrite IHs. reflexivity. 
       reflexivity. 
       apply injection_S. rewrite plus_Snm_nSm in IHs. assumption. 
Defined. 


(* a + (b min c) = (a + b) min (a + c) *) 
Lemma A_bs_min_plus_left_distributive : 
        A_bs_left_distributive brel_eq_nat bop_min bop_plus. 
Proof. unfold A_bs_left_distributive, bop_plus, bop_min. 
       induction s. 
       - intros t u. simpl. apply brel_eq_nat_reflexive.
       - induction t. 
         + simpl. rewrite plus_comm. simpl. intro u.  
           rewrite Min.min_comm. rewrite plus_comm. rewrite min_add. 
           apply brel_eq_nat_reflexive.
         + induction u. 
           * simpl. rewrite plus_comm. simpl. rewrite plus_comm. rewrite min_add. 
             apply brel_eq_nat_reflexive.
           * rewrite plus_SS.  rewrite plus_SS. rewrite bop_min_S.  rewrite bop_min_S. 
             rewrite plus_SS.  apply injection_S_brel_eq_nat. apply IHs. 
Qed.

Lemma A_bs_min_plus_right_distributive : 
        A_bs_right_distributive brel_eq_nat bop_min bop_plus. 
Proof. apply bops_left_distributive_and_times_commutative_imply_right_distributive. 
       apply brel_eq_nat_congruence. 
       apply bop_min_congruence. 
       apply bop_plus_commutative. 
       apply A_bs_min_plus_left_distributive. 
Defined.

(* dual 
a min (b + c) <> (a min b) + (a min c) *)
Lemma A_bs_plus_min_not_left_distributive : 
  A_bs_not_left_distributive brel_eq_nat bop_plus bop_min.
Proof. exists (1,(1, 1)). compute. reflexivity. Defined.  

Lemma A_bs_plus_min_not_right_distributive : 
  A_bs_not_right_distributive brel_eq_nat bop_plus bop_min.
Proof. exists (1,(1, 1)). compute. reflexivity. Defined.  


Lemma plus_lemma_1 : ∀ (a b : nat), plus a b = b -> a = 0. 
Proof. induction a. 
          auto. 
          induction b; intro H. 
             rewrite plus_comm in H. simpl in H. assumption. 
             elim IHb; auto.              
             assert (F: S a + S b = S (S a + b)). 
                rewrite plus_comm at 1. 
                rewrite plus_Sn_m at 1. 
                rewrite plus_comm at 1. reflexivity. 
             rewrite F in H.  apply injective_S in H. assumption.              
Defined.

(* absorption *) 

Lemma A_bs_min_plus_left_absorptive : 
        A_bs_left_absorptive brel_eq_nat bop_min bop_plus. 
Proof. unfold bop_plus, bop_min, brel_eq_nat, A_bs_left_absorptive.
       (* ugly --- cleanup ... *) 
       induction s. intro t. compute. reflexivity. 
       induction t. rewrite plus_comm. unfold plus. 
       assert (A := bop_min_idempotent). 
       unfold bop_idempotent in A. 
       assert (B := brel_eq_nat_symmetric). unfold brel_symmetric in B. 
       rewrite B. reflexivity. apply A. 
       rewrite plus_comm. rewrite min_comm. rewrite min_add. 
       apply brel_eq_nat_reflexive. 
Qed. 

Lemma A_bs_min_plus_right_absorptive  : 
       A_bs_right_absorptive brel_eq_nat bop_min bop_plus. 
Proof. apply bs_left_absorptive_implies_right.  
       apply brel_eq_nat_reflexive. 
       apply brel_eq_nat_transitive. 
       apply bop_min_congruence. 
       apply bop_plus_commutative. 
       apply A_bs_min_plus_left_absorptive. 
Qed. 


(* dual 
a <> a + (a min b) *)
Lemma A_bs_plus_min_not_left_absorptive : 
  A_bs_not_left_absorptive brel_eq_nat bop_plus bop_min.
Proof. exists (1, 1). compute. reflexivity. Defined. 

Lemma A_bs_plus_min_not_right_absorptive : 
  A_bs_not_right_absorptive brel_eq_nat bop_plus bop_min.
Proof. exists (1, 1). compute. reflexivity. Defined. 

(*

Lemma bops_min_plus_right_left_absorptive  : 
       bops_right_left_absorptive nat brel_eq_nat bop_min bop_plus. 
Proof. apply bops_left_right_absorptive_implies_right_left.  
       apply brel_eq_nat_reflexive. 
       apply brel_eq_nat_transitive. 
       apply bop_min_congruence. 
       apply bop_min_commutative. 
       apply bop_plus_commutative. 
       apply bops_min_plus_left_right_absorptive. 
Qed.

Lemma bops_plus_min_not_right_left_absorptive : 
  bops_not_right_left_absorptive nat brel_eq_nat bop_plus bop_min.
Proof. exists (1, 1). compute. reflexivity. Defined. 


Lemma bops_min_plus_right_right_absorptive  : 
       bops_right_right_absorptive nat brel_eq_nat bop_min bop_plus. 
Proof. apply bops_right_left_absorptive_implies_right_right.  
       apply brel_eq_nat_reflexive. 
       apply brel_eq_nat_transitive. 
       apply bop_min_congruence. 
       apply bop_plus_commutative. 
       apply bops_min_plus_right_left_absorptive. 
Qed.

Lemma bops_plus_min_not_right_right_absorptive : 
  bops_not_right_right_absorptive nat brel_eq_nat bop_plus bop_min.
Proof. exists (1, 1). compute. reflexivity. Defined. 
*) 

(* strict absorption 
Lemma bops_min_plus_not_left_strictly_absorptive : 
  bops_not_left_strictly_absorptive nat brel_eq_nat bop_min bop_plus.
Proof.
  exists (0, 0).
  compute; auto.
Qed.
  

Lemma bops_min_plus_not_right_strictly_absorptive : 
  bops_not_right_strictly_absorptive nat brel_eq_nat bop_min bop_plus.
Proof.
  exists (0, 0).
  compute; auto.
Qed.
  
*)


Lemma A_bs_min_plus_exists_id_ann_equal :
  A_bs_exists_id_ann_equal brel_eq_nat bop_plus bop_min.
Proof. exists 0. split.
       - apply bop_plus_zero_is_id.
       - apply bop_min_zero_is_ann.
Defined. 

End Theory.

Section ACAS.

  Open Scope nat.

Definition A_bs_min_plus_properties : A_bs_properties brel_eq_nat bop_min bop_plus := 
  {| 
     A_bs_left_distributive_d  := inl A_bs_min_plus_left_distributive
   ; A_bs_right_distributive_d := inl A_bs_min_plus_right_distributive
   ; A_bs_left_absorptive_d    := inl A_bs_min_plus_left_absorptive
   ; A_bs_right_absorptive_d   := inl A_bs_min_plus_right_absorptive
  |}.


Definition A_bs_min_plus : @A_bs nat :=
let eqv := A_eqv_nat in
let eq  := A_eqv_eq _ eqv in
let w   := A_eqv_witness _ eqv in
let f   := A_eqv_new _ eqv in
let nt  := A_eqv_not_trivial _ eqv in
let eqvP := A_eqv_proofs _ eqv in 
{|
  A_bs_eqv          := eqv 
; A_bs_plus         := bop_min
; A_bs_times        := bop_plus 
; A_bs_plus_props   := A_sg_C_proofs_from_sg_CS_proofs _
                         eq bop_min w f nt eqvP 
                         sg_CS_proofs_min
; A_bs_times_props  := A_sg_proofs_from_sg_C_proofs _
                         eq bop_plus w f nt eqvP 
                         A_sg_C_proofs_plus
; A_bs_id_ann_props :=
    {|
      A_id_ann_plus_times_d := A_Id_Ann_None _ _ _ (bop_min_not_exists_id, bop_plus_not_exists_ann)
    ; A_id_ann_times_plus_d := A_Id_Ann_Equal _ _ _ A_bs_min_plus_exists_id_ann_equal
    |}
; A_bs_props        := A_bs_min_plus_properties
; A_bs_ast          := Ast_min_plus
|}.

End ACAS.


Section MACAS.

Definition A_mcas_bs_min_plus := A_MCAS_bs (A_classify_bs A_bs_min_plus). 

End MACAS.
  
Section CAS.

  Open Scope nat.

  Definition bs_min_plus_properties : @bs_properties nat := 
  {| 
     bs_left_distributive_d  := inl (BS_Left_Distributive 0)
   ; bs_right_distributive_d := inl (BS_Right_Distributive 0)
   ; bs_left_absorptive_d    := inl (BS_Left_Absorptive 0)
   ; bs_right_absorptive_d   := inl (BS_Right_Absorptive 0)
  |}.

Definition bs_min_plus : @bs nat :=
let eqv := eqv_eq_nat in
let eq  := eqv_eq eqv in
let w   := eqv_witness eqv in
let f   := eqv_new eqv in
{|
  bs_eqv          := eqv 
; bs_plus         := bop_min
; bs_times        := bop_plus 
; bs_plus_props   := sg_C_certs_from_sg_CS_certs _
                         eq bop_min w f 
                         sg_CS_certs_min
; bs_times_props  := sg_certs_from_sg_C_certs _
                         eq bop_plus w f 
                         sg_C_certs_plus
; bs_id_ann_props :=
    {|
      id_ann_plus_times_d := Id_Ann_None 
    ; id_ann_times_plus_d := Id_Ann_Equal 0 
    |}
; bs_props        := bs_min_plus_properties
; bs_ast          := Ast_min_plus
|}.


End CAS.

Section MCAS.

  Definition mcas_bs_min_plus := MCAS_bs (classify_bs bs_min_plus). 

End MCAS.
  


Section Verify.

Theorem correct_min_plus : 
  bs_min_plus
  =
  A2C_bs (A_bs_min_plus). 
Proof. compute. reflexivity. Qed.


Theorem correct_mcas_min_plus :
  mcas_bs_min_plus
  =
  A2C_bs_mcas A_mcas_bs_min_plus.
Proof. compute. reflexivity. Qed. 


End Verify.   
