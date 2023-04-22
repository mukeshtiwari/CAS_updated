Require Import Coq.Init.Datatypes. 
Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.

Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.eqv.list.

Require Import CAS.coq.po.properties.
Require Import CAS.coq.po.structures.
Require Import CAS.coq.po.length. 

Require Import CAS.coq.ltr.properties.
Require Import CAS.coq.ltr.structures.
Require Import CAS.coq.ltr.cons.

Require Import CAS.coq.oltr.properties.
Require Import CAS.coq.oltr.structures.

Section Theory.

Variable S : Type.


Lemma olt_length_cons_id_monotone : olt_monotone S (list S) brel_length ltr_cons_op. 
Proof. intros s l1 l2 A.
       unfold brel_length. unfold ltr_cons_op.
       unfold length. fold (length l1). fold (length l2).
Admitted. 

Lemma olt_length_cons_id_strictly_monotone : olt_strictly_monotone S (list S) brel_length ltr_cons. 
Proof. intros s l1 l2 A B.
       unfold brel_length. unfold ltr_cons.
       unfold length. fold (length l1). fold (length l2). 
Admitted. 

Lemma olt_length_cons_id_strictly_increasing   : 
      olt_strictly_increasing S (list S) brel_length ltr_cons. 
Proof. intros s l. induction l. 
          compute; auto. 
          unfold ltr_cons.  unfold brel_length.
          unfold length. fold (length l). fold (length (a::l)).
Admitted. 

End Theory. 

Section ACAS.


Definition length_cons_qoltr_msi_proofs (S : Type)  :=
{|
  A_qoltr_msi_monotone             := olt_length_cons_id_monotone S 
; A_qoltr_msi_strictly_increasing  := olt_length_cons_id_strictly_increasing S 
|}.

Definition length_cons_with_bottom_proofs (S: Type) (eq : brel S) (wS : S) := 
{|
  A_with_bottom_exists_top_d       := inr (brel_length_not_exists_qo_top S eq wS)
; A_with_bottom_exists             := brel_length_exists_qo_bottom S eq 
|}.


Definition A_length_cons_woltr_monotone_strictly_increasing (S : Type) (eqvS : A_eqv S) :=
{|
  A_woltr_msi_carrier      := A_eqv_list S eqvS 
; A_woltr_msi_label        := eqvS 
; A_woltr_msi_lte          := brel_length 
; A_woltr_msi_ltr          := ltr_cons 
; A_woltr_msi_lte_proofs   := wo_proofs_length S (A_eqv_eq S eqvS) (A_eqv_witness S eqvS) (A_eqv_new S eqvS) (A_eqv_not_trivial S eqvS)
; A_woltr_msi_ltr_proofs   := ltr_cons_proofs S (A_eqv_eq S eqvS) (A_eqv_witness S eqvS) (A_eqv_proofs S eqvS)
; A_woltr_msi_bottom_proofs := length_cons_with_bottom_proofs S (A_eqv_eq S eqvS) (A_eqv_witness S eqvS)                                              
; A_woltr_msi_proofs       := length_cons_qoltr_msi_proofs S 
; A_woltr_msi_ast          := Ast_lotr_length_cons (A_eqv_ast S eqvS)
|}.


End ACAS. 

(*
Section CAS.


Definition length_cons_with_bottom_certs {S: Type} := 
{|
  with_bottom_exists_top_d       := @Certify_Not_Exists_Qo_Top (list S) 
; with_bottom_exists             := @Assert_Exists_Qo_Bottom (list S) nil 
|}.


Definition length_cons_qoltr_msi_certs {S : Type} :=
{|
  qoltr_msi_monotone             := @Assert_Olt_Monotone S (list S)
; qoltr_msi_strictly_increasing  := @Assert_Olt_Strictly_Increasing S (list S) 
|}.


Definition length_cons_woltr_monotone_strictly_increasing {S : Type} (eqvS : @eqv S) :=
{|
  woltr_msi_carrier      := eqv_list eqvS 
; woltr_msi_label        := eqvS 
; woltr_msi_lte          := brel_length 
; woltr_msi_ltr          := ltr_cons 
; woltr_msi_lte_certs    := wo_certs_length (eqv_witness eqvS) (eqv_new eqvS)
; woltr_msi_ltr_certs    := ltr_cons_certs (eqv_witness eqvS)
; woltr_msi_bottom_certs := length_cons_with_bottom_certs       
; woltr_msi_certs        := length_cons_qoltr_msi_certs
; woltr_msi_ast          := Ast_lotr_length_cons (eqv_ast eqvS)
|}.
  

End CAS.

Section Verify.

Theorem correct_length_cons_woltr_monotone_strictly_increasing (L S : Type) (eqv : A_eqv S) : 
   length_cons_woltr_monotone_strictly_increasing (A2C_eqv S eqv) 
   =
   A2C_woltr_monotone_strictly_increasing S (list S) (A_length_cons_woltr_monotone_strictly_increasing S eqv). 
Proof. unfold length_cons_woltr_monotone_strictly_increasing, A_length_cons_woltr_monotone_strictly_increasing,
              A2C_woltr_monotone_strictly_increasing; simpl. 
       rewrite <- correct_eqv_list.
       unfold length_cons_qoltr_msi_certs. unfold P2C_qoltr_msi.        
       rewrite <- correct_wo_certs_length.
       rewrite <- correct_ltr_certs_cons.        
       reflexivity.
Qed. 
  


End Verify.   
*) 
