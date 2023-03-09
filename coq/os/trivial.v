
Require Import Coq.Strings.String.

Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.

Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.

Require Import CAS.coq.po.properties.
Require Import CAS.coq.po.structures.
Require Import CAS.coq.po.trivial.
Require Import CAS.coq.po.cast_up. 

Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures.
Require Import CAS.coq.sg.cast_up. 

Require Import CAS.coq.os.properties.
Require Import CAS.coq.os.structures.



Section Theory.

Variable S  : Type.
Variable eq : brel S.
Variable times     : binary_op S.

Lemma os_trivial_from_sg_left_monotone : os_left_monotone brel_trivial times.
Proof. intros a b c. compute; auto. Qed.        

Lemma os_trivial_from_sg_right_monotone : os_right_monotone brel_trivial times.
Proof. intros a b c. compute; auto. Qed.


Lemma os_trivial_from_sg_left_increasing : os_left_increasing brel_trivial times.
Proof. intros s t. compute. auto. Qed.

Lemma os_trivial_from_sg_right_increasing : os_right_increasing brel_trivial times.
Proof. intros s t. compute. auto. Qed.


Lemma os_trivial_from_sg_not_left_strictly_increasing (wS : S) :
      os_not_left_strictly_increasing brel_trivial times.
Proof. exists (wS, wS). compute. right; auto. Defined.   


Lemma os_trivial_from_sg_not_right_strictly_increasing (wS : S) :
      os_not_right_strictly_increasing brel_trivial times.
Proof. exists (wS, wS). compute. right; auto. Defined.


Definition os_trivial_from_sg_exists_qo_top_ann_equal_decide 
      (f : S -> S) (nt : brel_not_trivial S eq f)
      (ann_d : bop_exists_ann_decidable S eq times) : 
  os_exists_qo_top_ann_decidable S eq brel_trivial times :=
  match ann_d with
  | inl annP => Qo_Top_Ann_Proof_None_Ann _ _ _ _
                    (brel_trivial_not_exists_qo_top S eq f nt, annP)
  | inr nannP => Qo_Top_Ann_Proof_None _ _ _ _
                    (brel_trivial_not_exists_qo_top S eq f nt, nannP)
  end.                    


Definition os_trivial_from_sg_exists_qo_bottom_id_equal_decide 
      (f : S -> S) (nt : brel_not_trivial S eq f)
      (id_d : bop_exists_id_decidable S eq times) : 
  os_exists_qo_bottom_id_decidable S eq brel_trivial times :=
  match id_d with
  | inl idP => Qo_Bottom_Id_Proof_None_Id _ _ _ _
                    (brel_trivial_not_exists_qo_bottom S eq f nt, idP)
  | inr nidP => Qo_Bottom_Id_Proof_None _ _ _ _
                    (brel_trivial_not_exists_qo_bottom S eq f nt, nidP)
  end.                    

End Theory.

(*
Section ACAS.

Definition A_os_from_sg_trivial {S : Type} (A : A_sg S) :=
  let eqv   := A_sg_eqv _  A in 
  let eq    := A_eqv_eq _ eqv in
  let wS    := A_eqv_witness _ eqv in     
  let f     := A_eqv_new _ eqv in
  let nt    := A_eqv_not_trivial _ eqv in
  let times := A_sg_bop _ A in 
  {|
     A_orsg_eqv               := eqv 
   ; A_orsg_lte               := brel_trivial 
   ; A_orsg_times             := A_sg_bop _ A 
   ; A_orsg_lte_proofs        := or_proofs_from_wo_proofs _ _ _ (or_proofs_trivial S eq wS f nt)
   ; A_orsg_times_proofs      := A_sg_proofs _ A 
   ; A_orsg_bottom_top_proofs :=
       {| A_qo_bottom_top_bottom_id_d := os_trivial_from_sg_exists_qo_bottom_id_equal_decide S eq times f nt (A_sg_exists_id_d _ A)
        ; A_qo_bottom_top_top_ann_d   := os_trivial_from_sg_exists_qo_top_ann_equal_decide S eq times f nt (A_sg_exists_ann_d _ A)
       |}
   ; A_orsg_proofs            :=
      {|
         A_posg_left_monotonic_d   := inl (os_trivial_from_sg_left_monotone S times)
       ; A_posg_right_monotonic_d  := inl (os_trivial_from_sg_right_monotone S times)
       ; A_posg_left_increasing_d  := inl (os_trivial_from_sg_left_increasing S times)
       ; A_posg_right_increasing_d := inl (os_trivial_from_sg_right_increasing S times)
      |}
   ; A_orsg_ast                    := Ast_os_from_sg_trivial (A_sg_ast _ A) 
|}.
  
End ACAS.

Section AMCAS.

Open Scope string_scope.
  
Definition A_mcas_os_from_sg_trivial {S : Type} (A : A_sg_mcas S) := 
match A_sg_mcas_cast_up _ A with
| A_MCAS_sg _ A'         => A_OS_orsg _ (A_os_from_sg_trivial A')
| A_MCAS_sg_Error _ sl1  => A_OS_Error _ sl1
| _                      => A_OS_Error _ ("Internal Error : mcas_os_from_sg_trivial" :: nil)
end.
  
End AMCAS.   


Section CAS.

Definition os_trivial_from_sg_exists_qo_top_ann_equal_certify {S : Type} 
      (ann_d : @check_exists_ann S) : @os_exists_qo_top_ann_certificate S := 
  match ann_d with
  | Certify_Exists_Ann a => Qo_Top_Ann_Cert_None_Ann a
  | _                    => Qo_Top_Ann_Cert_None 
  end.                    

Definition os_trivial_from_sg_exists_qo_bottom_id_equal_certify {S : Type} 
      (ann_d : @check_exists_id S) : @os_exists_qo_bottom_id_certificate S := 
  match ann_d with
  | Certify_Exists_Id i => Qo_Bottom_Id_Cert_None_Id i
  | _                   => Qo_Bottom_Id_Cert_None 
  end.                    


Definition os_from_sg_trivial {S : Type} (A : @sg S) :=
  let eqv   := sg_eqv A in 
  let wS    := eqv_witness eqv in     
  let f     := eqv_new eqv in
  {|
     orsg_eqv               := eqv 
   ; orsg_lte               := brel_trivial 
   ; orsg_times             := sg_bop A 
   ; orsg_lte_certs         := or_certs_from_wo_certs (or_certs_trivial wS f)
   ; orsg_times_certs       := sg_certs A 
   ; orsg_bottom_top_certs  :=
       {| qo_bottom_top_bottom_id_d := os_trivial_from_sg_exists_qo_bottom_id_equal_certify (sg_exists_id_d A)
        ; qo_bottom_top_top_ann_d   := os_trivial_from_sg_exists_qo_top_ann_equal_certify (sg_exists_ann_d A)
       |}
   ; orsg_certs             :=
      {|
         posg_left_monotonic_d   := Certify_Left_Monotone 
       ; posg_right_monotonic_d  := Certify_Right_Monotone 
       ; posg_left_increasing_d  := Certify_Left_Increasing
       ; posg_right_increasing_d := Certify_Right_Increasing
      |}
   ; orsg_ast                    := Ast_os_from_sg_trivial (sg_ast A) 
|}.
  
End CAS.

Section MCAS.

Open Scope string_scope.
  
Definition mcas_os_from_sg_trivial {S : Type} (A : @sg_mcas S) := 
match sg_mcas_cast_up _ A with
| MCAS_sg A'         => OS_orsg (os_from_sg_trivial A')
| MCAS_sg_Error sl1  => OS_Error sl1
| _                  => OS_Error ("Internal Error : mcas_os_from_sg_trivial" :: nil)
end.
  
End MCAS.

Section Verify.


  Theorem correct_os_from_sg_trivial (S : Type) (A : A_sg S) :
    A2C_orsg (A_os_from_sg_trivial A)
    = 
    os_from_sg_trivial (A2C_sg _ A). 
  Proof. unfold A2C_orsg, A2C_sg, A_os_from_sg_trivial, os_from_sg_trivial.
         destruct A; simpl.
         unfold P2C_os_proofs; simpl.
         (* next line should be a lemma *) 
         unfold or_certs_from_wo_certs, or_certs_trivial,
                or_proofs_from_wo_proofs, or_proofs_trivial, P2C_or; simpl. 
         destruct A_sg_exists_id_d as [[i idP] | nidP]; 
         destruct A_sg_exists_ann_d as [[a annP] | nannP];
         unfold P2C_os_qo_bottom_top_proofs; simpl;
           try reflexivity.
  Qed.


Theorem correct_mcas_os_from_sg_trivial (S : Type) (sgS : A_sg_mcas S) :
    A2C_mcas_os (A_mcas_os_from_sg_trivial sgS)
    =
    mcas_os_from_sg_trivial (A2C_mcas_sg S sgS). 
Proof. unfold A_mcas_os_from_sg_trivial, mcas_os_from_sg_trivial. 
       rewrite correct_sg_mcas_cast_up.       
       destruct (A_sg_cas_up_is_error_or_sg S sgS) as [[l1 A] | [s1 A]]. 
       + rewrite A; simpl. reflexivity. 
       + rewrite A; simpl. rewrite correct_os_from_sg_trivial.
         reflexivity. 
Qed. 
    
    
End Verify.   

*) 
