Require Import CAS.coq.common.compute.
Require Import CAS.coq.eqv.properties. 
Require Import CAS.coq.eqv.set. 

Require Import CAS.coq.tr.left.from_sg.
Require Import CAS.coq.bs.properties.
Require Import CAS.coq.bs.structures. 
Require Import CAS.coq.st.properties. 
Require Import CAS.coq.st.structures.



Section Theory.

Variables (S : Type)
          (wS : S)   
          (eq : brel S)
          (ref : brel_reflexive S eq)
          (sym : brel_symmetric S eq)
          (plus : binary_op S) 
          (times : binary_op S). 

Lemma slt_from_bs_distributive 
      (LD : bop_left_distributive S eq plus times) : 
      slt_distributive eq plus (ltr_from_sg times). 
Proof. intros s t u. unfold ltr_from_sg. apply LD. Qed.

Lemma slt_from_bs_not_distributive 
      (nLD : bop_not_left_distributive S eq plus times) : 
  slt_not_distributive eq plus (ltr_from_sg times).
Proof. destruct nLD as [[s [t u]] A]. 
       exists (s, (t, u)). compute.
       exact A. 
Defined.

Lemma slt_from_bs_left_absorptive 
       (lrabs : bops_left_right_absorptive S eq plus times) :
       slt_absorptive eq plus (ltr_from_sg times).
Proof. intros s t. unfold ltr_from_sg. exact (lrabs t s). Qed. 

Lemma slt_from_bs_not_absorptive 
       (nlrabs : bops_not_left_right_absorptive S eq plus times) :
       slt_not_absorptive eq plus (ltr_from_sg times).
Proof. destruct nlrabs as [[s t] P]. exists(t, s). compute. exact P. Defined. 


(* 
Lemma slt_from_bs_strictly_absorptive
       (lrabs : bops_left_right_absorptive S eq plus times)       
       (laabs : bops_right_anti_absorptive S eq plus times) :  
       slt_strictly_absorptive eq plus (ltr_from_sg times).
Proof.  intros s t. split; auto. Qed. 
*) 

(* 

Lemma slt_from_bs_not_strictly_absorptive_v2
       (laabs : bops_not_right_anti_absorptive S eq plus times) :  
       slt_not_strictly_absorptive eq plus (ltr_from_sg times).
Proof.  destruct laabs as [[s1 s2] A].
        exists (s2, s1); compute. right. exact A. 
Defined. 
*) 

End Theory.

(*
Section ACAS.

Section Proofs.

Variables (S : Type)
          (eq : brel S)
          (plus times : binary_op S)
          . 
  
Definition slt_from_bs_proofs (bsP : bs_proofs S eq plus times) : 
             slt_proofs S eq plus (ltr_from_sg times) := 
{|
  A_slt_distributive_d        := 
; A_slt_absorptive_d          := 
; A_slt_strictly_absorptive_d := 
|}.


End Proofs.

Section Combinators. 

Definition A_slt_from_bs {S : Type} (A : A_bs S) : A_slt S := 
let eqv   := A_bs_eqv _ A in 
let eq    := A_eqv_eq _ eqv in 
let times := A_bs_times _ A in 
{|
    A_slt_carrier           := eqv
    A_slt_label             := eqv 
    A_slt_plus              := A_bs_plus _ A 
    A_slt_trans             := ltr_from_sg times 
    A_slt_plus_proofs       := A_bs_plus_proofs _ A 
    A_slt_trans_proofs      := ltr_from_sg_proofs S eq times (A_bs_times_proofs _ A)
    A_slt_exists_plus_ann_d := 
    A_slt_id_ann_proofs_d   := 
    A_slt_proofs            := slt_from_bs_proofs 
    A_slt_ast               := Cas_ast("", (Cas_ast_bs (A_bs_ast _ A)) :: nil)
|}.
  
End Combinators.

End ACAS. 
*) 
