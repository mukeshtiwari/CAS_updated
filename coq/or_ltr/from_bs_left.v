
Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.
Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures.
Require Import CAS.coq.bs.properties.
Require Import CAS.coq.bs.structures.

Require Import CAS.coq.po.properties.
Require Import CAS.coq.po.structures.
Require Import CAS.coq.tr.properties.
Require Import CAS.coq.tr.structures.
Require Import CAS.coq.ot.properties.
Require Import CAS.coq.ot.structures.

Require Import CAS.coq.po.from_sg.
Require Import CAS.coq.tr.left.cayley.

Section Theory.

Variable S : Type.
Variable eq : brel S.
Variable ref : brel_reflexive S eq.
Variable sym : brel_symmetric S eq. 
Variable trn : brel_transitive S eq.

Variable plus times : binary_op S.
Variable tCong : bop_congruence S eq times.

Lemma olt_from_bs_left_monotone (LD : bop_left_distributive S eq plus times) :
  olt_monotone S S (brel_lte_left eq plus) (ltr_cayley times). 
Proof. intros s1 s2 s3. compute.  intro A.
       assert (B := LD s1 s2 s3).
       assert (C : eq (times s1 s2) (times s1 (plus s2 s3)) = true). 
          exact (tCong _ _ _ _ (ref s1) A).        
       exact (trn _ _ _ C B).
Qed.        

Lemma olt_from_bs_left_increasing (LRA : bops_left_right_absorptive S eq plus times) : 
      olt_increasing S S (brel_lte_left eq plus) (ltr_cayley times). 
Proof. intros s t. compute. exact (LRA t s). Defined. 

End Theory. 

Section ACAS.


Definition from_bs_left_poltr_mi_proofs
           (S : Type) (eqv : A_eqv S) (plus times : binary_op S)
           (TP : msg_proofs S _ times)
           (PAP : path_algebra_proofs S _ plus times) :=
let eq := A_eqv_eq S eqv in
let eqvP := A_eqv_proofs S eqv in 
let ref := A_eqv_reflexive S eq eqvP in 
let trn := A_eqv_transitive S eq eqvP in 
let tCong := A_msg_congruence S eq times TP in 
let LD := A_path_algebra_left_distributive S eq plus times PAP in
let LRA := A_path_algebra_left_right_absorptive S eq plus times PAP in 
{|
  A_poltr_mi_monotone    := olt_from_bs_left_monotone S eq ref trn plus times tCong LD 
; A_poltr_mi_increasing  := olt_from_bs_left_increasing S eq plus times LRA 
|}.

(*
Definition from_sg_left_with_bottom_proofs (S : Type) (eq : brel S) (eqvP : eqv_proofs S eq) (plus : binary_op S)
   (comm : bop_commutative S eq plus) (ann : bop_exists_ann S eq plus) (id_d : bop_exists_id_decidable S eq plus) := 
let sym := A_eqv_symmetric S eq eqvP in 
let trn := A_eqv_transitive S eq eqvP in 
{|
  A_with_bottom_exists_top_d       := po_from_sg_left_not_exists_top_decide S eq sym trn plus comm id_d 
; A_with_bottom_exists             := po_from_sg_left_exists_bottom S eq sym trn plus comm ann 
|}.


Definition A_pre_path_algebra_to_poltr_mi (S : Type) (PPA : A_pre_path_algebra_with_one S) :=
let eqv := A_pre_path_algebra_with_one_eqv S PPA  in
let eqvP := A_eqv_proofs S eqv in  
let eq := A_eqv_eq S eqv in
let plus := A_pre_path_algebra_with_one_plus S PPA in
let times := A_pre_path_algebra_with_one_times S PPA in
let PP := A_pre_path_algebra_with_one_plus_proofs S PPA in
let comm := A_sg_CINS_commutative _ _ _ PP in 
let TP := A_pre_path_algebra_with_one_times_proofs S PPA in
let PAP := A_pre_path_algebra_with_one_proofs S PPA in
let WOP := A_pre_path_algebra_with_one_id_ann_proofs S PPA in 
let id_d :=  A_with_one_exists_plus_id_d S eq plus times WOP in
let ann :=  A_with_one_exists_plus_ann S eq plus times WOP in
{|
  A_poltr_mi_carrier      := eqv 
; A_poltr_mi_label        := eqv 
; A_poltr_mi_lte          := brel_lte_left eq plus
; A_poltr_mi_ltr          := ltr_cayley times
; A_poltr_mi_lte_proofs   := po_from_sg_left_proofs S eq eqvP plus id_d ann PP 
; A_poltr_mi_ltr_proofs   := ltr_cayley_proofs S eq times TP
; A_poltr_mi_bottom_proofs := from_sg_left_with_bottom_proofs S eq eqvP plus comm ann id_d                                                
; A_poltr_mi_proofs       := from_bs_left_poltr_mi_proofs S eqv plus times TP PAP 
; A_poltr_mi_ast          := A_pre_path_algebra_with_one_ast S PPA (* FIX *) 
|}.

*) 
End ACAS. 


(********************************


Section CAS.

Definition from_bs_left_poltr_mi_certs {S : Type} := 
{|
  poltr_mi_monotone    := @Assert_Olt_Monotone S S 
; poltr_mi_increasing  := @Assert_Olt_Increasing S S 
|}.

Definition from_sg_left_with_bottom_certs {S : Type} (ann : @assert_exists_ann S) (id_d : @check_exists_id S) := 
{|
  with_bottom_exists_top_d       := match id_d with
                                    | Certify_Exists_Id i => Certify_Exists_Qo_Top i 
                                    | Certify_Not_Exists_Id => Certify_Not_Exists_Qo_Top
                                    end 
; with_bottom_exists             := match ann with
                                    | Assert_Exists_Ann a => Assert_Exists_Qo_Bottom a
                                    end                                                   
|}.



Definition pre_path_algebra_to_poltr_mi (S : Type) (PPA : @pre_path_algebra_with_one S) :=
let eqv := pre_path_algebra_with_one_eqv PPA  in
let eq := eqv_eq eqv in
let plus := pre_path_algebra_with_one_plus PPA in
let times := pre_path_algebra_with_one_times PPA in
let id_d := (with_one_exists_plus_id_d (pre_path_algebra_with_one_id_ann_certs PPA)) in
let ann := (with_one_exists_plus_ann (pre_path_algebra_with_one_id_ann_certs PPA)) in 
{|
  poltr_mi_carrier     := eqv 
; poltr_mi_label       := eqv 
; poltr_mi_lte         := brel_lte_left eq plus
; poltr_mi_ltr         := ltr_cayley times
; poltr_mi_lte_certs   := @po_from_sg_left_certs S id_d ann (pre_path_algebra_with_one_plus_certs PPA) 
; poltr_mi_ltr_certs   := @ltr_cayley_certs S (pre_path_algebra_with_one_times_certs PPA) 
; poltr_mi_bottom_certs := @from_sg_left_with_bottom_certs S ann id_d 
; poltr_mi_certs       := @from_bs_left_poltr_mi_certs S 
; poltr_mi_ast         := pre_path_algebra_with_one_ast PPA (* FIX *) 
|}.


End CAS.

Section Verify.


Theorem correct_from_bs_left_poltr_sg_left_certs (S : Type) (eq : brel S) (eqvP : eqv_proofs S eq) (plus times : binary_op S)
        (P : with_one_proofs S eq plus times) (Q : sg_CINS_proofs S eq plus) : 
po_from_sg_left_certs (p2c_exists_id_check S eq plus (A_with_one_exists_plus_id_d S eq plus times P)) 
                      (p2c_exists_ann_assert S eq plus (A_with_one_exists_plus_ann S eq plus times P))
                      (P2C_sg_CINS S eq plus Q) 
=
P2C_po S eq (brel_lte_left eq plus) (po_from_sg_left_proofs S eq eqvP plus 
                                       (A_with_one_exists_plus_id_d S eq plus times P)
                                       (A_with_one_exists_plus_ann S eq plus times P) 
                                       Q). 
Proof. destruct eqvP. destruct P. destruct Q.
       unfold po_from_sg_left_certs, po_from_sg_left_proofs, P2C_po, P2C_sg_CI; simpl.
       destruct A_with_one_exists_plus_ann as [ann Ann];
       destruct A_sg_CINS_not_selective as [[s1 s2] [A B]]; simpl; auto. 
Qed.

Lemma correct_from_bs_left_poltr_cayley_certs (S : Type) (eq : brel S) (times : binary_op S) (M : msg_proofs S eq times) :
ltr_cayley_certs S (P2C_msg S eq times M) 
= 
P2C_ltr S S eq eq (ltr_cayley times) (ltr_cayley_proofs S eq times M). 
Proof. destruct M. unfold ltr_cayley_certs, ltr_cayley_proofs, P2C_ltr, P2C_msg; simpl. 
       destruct A_msg_is_right_d as [IR | [[s1 s2] NIR]]; destruct A_msg_left_cancel_d as [LC | [[t1 [t2 t3]] NLC]]; simpl; auto. 
Qed. 

Lemma correct_from_bs_left_poltr_bottom_certs (S : Type) (eq : brel S) (eqvP : eqv_proofs S eq) (plus : binary_op S)
   (comm : bop_commutative S eq plus) (ann : bop_exists_ann S eq plus) (id_d : bop_exists_id_decidable S eq plus) : 
  from_sg_left_with_bottom_certs (p2c_exists_ann_assert S eq plus ann) (p2c_exists_id_check S eq plus id_d)
  = 
  P2C_with_bottom S eq (brel_lte_left eq plus) (from_sg_left_with_bottom_proofs S eq eqvP plus comm ann id_d). 
Proof. unfold from_sg_left_with_bottom_certs, from_sg_left_with_bottom_proofs, P2C_with_bottom,
       p2c_exists_ann_assert, p2c_exists_id_check; simpl. 
       destruct ann as [a A]; destruct id_d as [[i B] | Nid]; simpl; auto. 
Qed. 
                                                  

Lemma correct_from_bs_left_poltr_mi_certs (S : Type) (eqv : A_eqv S) (plus times : binary_op S)
      (M : msg_proofs S (A_eqv_eq S eqv) times) (P : path_algebra_proofs S (A_eqv_eq S eqv) plus times): 
from_bs_left_poltr_mi_certs
= 
P2C_poltr_mi S S (brel_lte_left (A_eqv_eq S eqv) plus) (ltr_cayley times) (from_bs_left_poltr_mi_proofs S eqv plus times M P).  
Proof. unfold from_bs_left_poltr_mi_certs, from_bs_left_poltr_mi_proofs, P2C_poltr_mi; simpl; auto. Qed. 

Theorem correct_pre_path_algebra_to_poltr_mi (S : Type) (PPA : A_pre_path_algebra_with_one S) :
  pre_path_algebra_to_poltr_mi S (A2C_pre_path_algebra_with_one S PPA)
  = 
  A2C_poltr_monotone_increasing S S (A_pre_path_algebra_to_poltr_mi S PPA).
Proof. destruct PPA. unfold A2C_pre_path_algebra_with_one, A2C_poltr_monotone_increasing,
       pre_path_algebra_to_poltr_mi, A_pre_path_algebra_to_poltr_mi; simpl.
       rewrite <- correct_from_bs_left_poltr_mi_certs.
       rewrite <- correct_from_bs_left_poltr_cayley_certs.
       rewrite <- correct_from_bs_left_poltr_sg_left_certs.
       rewrite <- correct_from_bs_left_poltr_bottom_certs.
       reflexivity. 
Qed. 





End Verify.



***********************)
