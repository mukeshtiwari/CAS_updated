
Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.
Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.po.properties.
Require Import CAS.coq.po.structures.
Require Import CAS.coq.os.properties.
Require Import CAS.coq.ot.properties.

Require Import CAS.coq.eqv.add_constant.
Require Import CAS.coq.eqv.sum.
Require Import CAS.coq.po.add_bottom. 
Require Import CAS.coq.sg.add_id.



Section Compute.

Open Scope list_scope.
  
Definition ltr_cons {S : Type} : left_transform S (list S) 
:= λ s l, (s :: l).  
  

Definition ltr_add_id {S : Type} (b : binary_op S) (c : cas_constant) : left_transform S (cas_constant + S) 
:= λ s d, 
   match d with
   | (inl _) => inr s
   | (inr t) => inr (b s t) 
   end.


Definition ltr_add_inject {L S : Type} (inj : L -> S) (ltr : left_transform L S) (c : cas_constant) : left_transform L (cas_constant + S) 
:= λ l d, 
   match d with
   | (inl _) => inr (inj l) 
   | (inr s) => inr (ltr l s) 
   end.

End Compute.   

Section Theory.

Variable bottom : cas_constant.
Variable L   : Type.
Variable S   : Type.
Variable eq  : brel S.
Variable lte : brel S.
Variable b   : binary_op S. 
Variable ltr : left_transform L S.

Variable inj : L -> S.
Variable inj_works : ∀ (l : L) (s : S), lte (inj l) (ltr l s) = true.  

Variable wS : S. 
Variable ref : brel_reflexive S eq. 
Variable lteRef : brel_reflexive S lte. 


Lemma olt_add_bottom_id_monotone  : 
     os_left_increasing S lte b -> os_left_monotone S lte b -> 
        olt_monotone S (with_constant S) (brel_add_bottom lte bottom) (ltr_add_id b bottom). 
Proof. intros LI LM s1 [c2 | s2] [c3 | s3]; simpl; intro A; auto. discriminate A. Qed.

Lemma olt_add_bottom_id_increasing   : 
     os_right_increasing S lte b -> 
        olt_increasing S (with_constant S) (brel_add_bottom lte bottom) (ltr_add_id b bottom). 
Proof. intros LI s1 [c2 | s2]; simpl; auto. Qed. 

Lemma olt_add_bottom_id_strictly_increasing   : 
     os_right_strictly_increasing S lte b -> 
        olt_strictly_increasing S (with_constant S) (brel_add_bottom lte bottom) (ltr_add_id b bottom). 
Proof. intros LI s1 [c2 | s2]; simpl; auto. Qed. 


Lemma olt_add_bottom_inject_monotone  : 
     olt_increasing L S lte ltr -> olt_monotone L S lte ltr -> 
        olt_monotone L (with_constant S) (brel_add_bottom lte bottom) (ltr_add_inject inj ltr bottom). 
Proof. intros LI LM l [c2 | s2] [c3 | s3]; simpl; intro A; auto. discriminate A. Qed. 

Lemma olt_add_bottom_inject_increasing  : 
     olt_increasing L S lte ltr -> 
        olt_increasing L (with_constant S) (brel_add_bottom lte bottom) (ltr_add_inject inj ltr bottom). 
Proof. intros LI l [c | s]; simpl; auto. Qed. 

Lemma olt_add_bottom_inject_strictly_increasing  : 
     olt_strictly_increasing L S lte ltr -> 
        olt_strictly_increasing L (with_constant S) (brel_add_bottom lte bottom) (ltr_add_inject inj ltr bottom). 
Proof. intros LI l [c | s]; simpl; auto. Qed. 


Lemma olt_add_bottom_inject_exists_qo_bottom : brel_exists_qo_bottom (with_constant S) (brel_sum brel_constant eq) (brel_add_bottom lte bottom). 
Proof. exists (inl bottom). split. 
       intros [c | s]; compute; auto. 
       intros [c | s]; compute; auto.        
Defined. 



End Theory. 

Section ACAS.

Print A_qo_with_bottom. 


(*
  qoltr_monotone_strictly_increasing -> qoltr_monotone_strictly_increasing_with_bottom



Record A_qo_with_bottom (S : Type) : Type := Build_A_qo_with_bottom
  { A_qowb_eqv : A_eqv S;
    A_qowb_lte : brel S;
    A_qowb_exists_top_d : brel_exists_qo_top_decidable S (A_eqv_eq S A_qowb_eqv) A_qowb_lte;
    A_qowb_exists_bottom : brel_exists_qo_bottom S (A_eqv_eq S A_qowb_eqv) A_qowb_lte;
    A_qowb_proofs : qo_proofs S (A_eqv_eq S A_qowb_eqv) A_qowb_lte;
    A_qowb_ast : cas_ast }


Record qoltr_msi_proofs (L S : Type) (lte : brel S) (ltr : L -> (S -> S)) :=
{
  A_qoltr_msi_monotone  : olt_monotone L S lte ltr 
; A_qoltr_msi_strictly_increasing  : olt_strictly_increasing L S lte ltr
}.


Record A_qoltr_monotone_strictly_increasing (L S : Type) :=
{
  A_qoltr_msi_carrier      : A_eqv S
; A_qoltr_msi_label        : A_eqv L
; A_qoltr_msi_lte          : brel S                                               
; A_qoltr_msi_ltr          : left_transform L S (* L -> (S -> S) *)
; A_qoltr_msi_lte_proofs   : qo_proofs S (A_eqv_eq S A_qoltr_msi_carrier) A_qoltr_msi_lte                                 
; A_qoltr_msi_ltr_proofs   : ltr_proofs L S (A_eqv_eq S A_qoltr_msi_carrier) (A_eqv_eq L A_qoltr_msi_label)  A_qoltr_msi_ltr
; A_qoltr_msi_proofs       : qoltr_msi_proofs L S A_qoltr_msi_lte A_qoltr_msi_ltr                                  
; A_qoltr_msi_ast          : cas_ast 
}.


*)
End ACAS.   