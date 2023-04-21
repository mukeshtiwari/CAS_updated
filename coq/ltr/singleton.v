Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.
Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures. 
Require Import CAS.coq.eqv.set.
Require Import CAS.coq.tr.properties.
Require Import CAS.coq.tr.structures.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.


Open Scope string_scope.
Import ListNotations.

Require Import CAS.coq.theory.set. 

Open Scope list.


Section Compute.

Definition ltr_singleton {S : Type} : ltr_type S (finite_set S) :=
    λ x y, (x :: nil). 

End Compute.   


Section Theory.

  Variable S : Type.
  Variable eq : brel S.
  Variable wS : S.
  Variable f : S -> S.
  Variable nt : brel_not_trivial S eq f. 
  Variable ref : brel_reflexive S eq. 
  Variable sym : brel_symmetric S eq.
  Variable trn : brel_transitive S eq. 

 Lemma ltr_singleton_congruence : ltr_congruence S (finite_set S) eq (brel_set eq) ltr_singleton. 
 Proof. intros s1 s2 l1 l2 H1 H2.
        unfold ltr_singleton. compute. rewrite H1. apply sym in H1. rewrite H1. 
        reflexivity. 
 Qed.


 Lemma ltr_singleton_not_left_cancellative : ltr_not_left_cancellative S (finite_set S) (brel_set eq) ltr_singleton. 
 Proof. unfold ltr_left_cancellative. exists (wS, (nil, wS::nil)). split.
        + unfold ltr_singleton.
          apply brel_set_reflexive; auto. 
        + compute. reflexivity. 
 Defined.

 Lemma ltr_singleton_left_constant : ltr_left_constant S (finite_set S) (brel_set eq) ltr_singleton. 
 Proof. intros s X Y.  compute. rewrite (ref s). reflexivity. Qed. 

 Lemma ltr_singleton_not_is_right : ltr_not_is_right S (finite_set S) (brel_set eq) ltr_singleton. 
 Proof. unfold ltr_not_is_right. exists (wS, (f wS) :: nil).
        destruct (nt wS) as [F1 F2]. 
        compute. rewrite F1. reflexivity. 
 Defined.
 
 Lemma ltr_singleton_not_exists_id : ltr_not_exists_id S (finite_set S) (brel_set eq) ltr_singleton. 
 Proof. unfold ltr_not_exists_id. intro s. unfold ltr_not_is_id. exists nil. compute; auto. Defined.

Lemma ltr_singleton_not_exists_ann : ltr_not_exists_ann S (finite_set S) (brel_set eq) ltr_singleton. 
  intros s. unfold ltr_not_is_ann. unfold ltr_singleton.
  destruct s.
  + exists wS. compute. reflexivity.
  + exists (f s).
    case_eq(brel_set eq (f s :: nil) (s :: s0)); intro A; auto.
    apply brel_set_elim_prop in A; auto. destruct A as [A B].
    assert (C : in_set eq (s :: s0) s = true). apply in_set_cons_intro; auto.
    assert (D := B _ C). compute in D.
    destruct (nt s) as [F1 F2].
    rewrite F1 in D. discriminate D. 
Defined. 


 
 
End Theory.

Section ACAS.

Section Proofs.
Variable S : Type.
Variable eq : brel S.
Variable wS : S.
Variable f : S -> S.
Variable nt : brel_not_trivial S eq f.
Variable eqvP : eqv_proofs S eq. 


Definition ltr_singleton_proofs : left_transform_proofs S (finite_set S) (brel_set eq) eq ltr_singleton :=
let ref := A_eqv_reflexive _ _ eqvP in
let sym := A_eqv_symmetric _ _ eqvP in
{|
  A_left_transform_congruence          := ltr_singleton_congruence S eq sym 
; A_left_transform_is_right_d          := inr(ltr_singleton_not_is_right S eq wS f nt)
; A_left_transform_left_constant_d     := inl(ltr_singleton_left_constant S eq ref)                                               
; A_left_transform_left_cancellative_d := inr(ltr_singleton_not_left_cancellative S eq wS ref sym)
|}.

End Proofs.

Definition A_left_transform_singleton (S : Type) (eqv : A_eqv S) :=
let eq := A_eqv_eq _ eqv in
let wS := A_eqv_witness S eqv in
let f  := A_eqv_new S eqv in
let nt  := A_eqv_not_trivial S eqv in
let eqvP := A_eqv_proofs _ eqv in
let ref := A_eqv_reflexive _ _ eqvP in
let sym := A_eqv_symmetric _ _ eqvP in
let trn := A_eqv_transitive _ _ eqvP in 
{|
  A_left_transform_carrier      := A_eqv_set S eqv 
; A_left_transform_label        := eqv                                                     
; A_left_transform_ltr          := ltr_singleton
; A_left_transform_exists_id_d  := inr(ltr_singleton_not_exists_id S eq) 
; A_left_transform_exists_ann_d := inr(ltr_singleton_not_exists_ann S eq wS f nt ref sym trn) 
; A_left_transform_proofs       := ltr_singleton_proofs S eq wS f nt eqvP 
; A_left_transform_ast          := Cas_ast ("A_left_transform_singleton", []) (*Ast_ltr_singleton (A_eqv_ast S eqv) *)
|}.

End ACAS.

Section CAS.

Definition ltr_singleton_certs {S : Type} (wS : S) (f : S -> S) : @left_transform_certificates S (list S) := 
{|
  left_transform_congruence            := Assert_Ltr_Congruence 
; left_transform_is_right_d            := Certify_Ltr_Not_Is_Right (wS, (f wS) :: nil)
; left_transform_left_constant_d       := Certify_Ltr_Left_Constant 
; left_transform_left_cancellative_d   := Certify_Ltr_Not_Left_Cancellative (wS, (nil, wS :: nil))
|}.


Definition left_transform_singleton {S : Type} (eqv : @eqv S) :=
{|
  left_transform_carrier      := eqv_set eqv 
; left_transform_label        := eqv                                                     
; left_transform_ltr          := ltr_singleton 
; left_transform_exists_id_d  := Certify_Ltr_Not_Exists_Id
; left_transform_exists_ann_d := Certify_Ltr_Not_Exists_Ann 
; left_transform_certs        := ltr_singleton_certs (eqv_witness eqv) (eqv_new eqv) 
; left_transform_ast          := Cas_ast ("A_left_transform_singleton", []) (*Ast_ltr_singleton (eqv_ast eqv)*)
|}.
  

End CAS. 
Section Verify.


Lemma correct_ltr_certs_singleton (S : Type) (eS : A_eqv S): 
  P2C_left_transform
          S (finite_set S)
          (brel_set (A_eqv_eq S eS))
          (A_eqv_eq S eS)
          ltr_singleton 
          (ltr_singleton_proofs S
                             (A_eqv_eq S eS)
                             (A_eqv_witness S eS)
                             (A_eqv_new S eS)
                             (A_eqv_not_trivial S eS)                                                          
                             (A_eqv_proofs S eS)
          ) 
    =                    
    ltr_singleton_certs (A_eqv_witness S eS) (A_eqv_new S eS).
Proof. compute. reflexivity. Qed. 


Theorem correct_left_transform_singleton (S : Type) (eS : A_eqv S)  : 
         left_transform_singleton (A2C_eqv S eS) 
         = 
         A2C_left_transform S (finite_set S) (A_left_transform_singleton S eS). 
Proof. unfold left_transform_singleton, A_left_transform_singleton, A2C_left_transform; simpl.
       rewrite correct_eqv_set.
       rewrite correct_ltr_certs_singleton.        
       reflexivity. 
Qed. 
  
  
 
End Verify.   
