
Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.
Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures.
Require Import CAS.coq.ltr.properties.
Require Import CAS.coq.ltr.structures.


Definition ltr_from_sg {S : Type} (b : binary_op S) : ltr_type S S := b.

Section Theory.

  Variable S : Type.
  Variable eqS : brel S.
  Variable bS : binary_op S.
  Variable bS_cong : bop_congruence S eqS bS.
  Variable refS : brel_reflexive S eqS. 

 Lemma A_ltr_from_sg_congruence : A_ltr_congruence eqS eqS (ltr_from_sg bS).
 Proof. unfold A_ltr_congruence, ltr_from_sg.
        intros. apply bS_cong; auto.
 Qed.

 
 Lemma A_ltr_from_sg_is_right (A : bop_is_right S eqS bS) : A_ltr_is_right eqS (ltr_from_sg bS).
 Proof. auto. Qed. 
 
 Lemma A_ltr_from_sg_not_is_right (A: bop_not_is_right S eqS bS) : A_ltr_not_is_right eqS (ltr_from_sg bS).
 Proof. auto. Defined.

 (*
 Lemma ltr_from_sg_left_constant (lc : bop_left_constant S eqS bS) : ltr_left_constant S S eqS (ltr_from_sg bS).
 Proof. intros l s1 s2. unfold ltr_from_sg. exact (lc l s1 s2).  Qed. 
        
 Lemma ltr_from_sg_not_left_constant (nlc : bop_not_left_constant S eqS bS) : ltr_not_left_constant S S eqS (ltr_from_sg bS).
 Proof. destruct nlc as [[l [s1 s2]] P]. exists (l, (s1, s2)). compute. exact P. Defined. 
*)   
 Lemma A_ltr_from_sg_cancellative (A : bop_left_cancellative S eqS bS) : A_ltr_cancellative eqS (ltr_from_sg bS).
 Proof. auto. Qed.

 Lemma A_ltr_from_sg_not_cancellative (A: bop_not_left_cancellative S eqS bS) : A_ltr_not_cancellative eqS (ltr_from_sg bS).
 Proof. auto. Defined. 
 
 Lemma A_ltr_from_sg_exists_id (A : bop_exists_left_id S eqS bS) : A_ltr_exists_id eqS (ltr_from_sg bS).
 Proof. auto. Qed. 

 Lemma A_ltr_from_sg_not_exists_id (A : bop_not_exists_left_id S eqS bS) : A_ltr_not_exists_id eqS (ltr_from_sg bS).
 Proof. auto. Defined.

(*
 Lemma A_ltr_from_sg_exists_ann (A : bop_exists_right_ann S eqS bS) : A_ltr_exists_ann eqS (ltr_from_sg bS).
 Proof. auto. Qed. 

 Lemma A_ltr_from_sg_not_exists_ann (A : bop_not_exists_right_ann S eqS bS) : A_ltr_not_exists_ann eqS (ltr_from_sg bS).
 Proof. auto. Defined. 
*) 
End Theory.

Section ACAS.


Definition A_ltr_from_sg_properties {S : Type}
    (eqS : brel S) (bS : binary_op S) (msgP : sg_proofs S eqS bS) :
    A_ltr_properties eqS eqS (ltr_from_sg bS) := 
{|
  A_ltr_props_congruence     :=
    A_ltr_from_sg_congruence S eqS bS (A_sg_congruence _ _ _ msgP)
; A_ltr_props_cancellative_d :=
    match A_sg_left_cancel_d _ _ _ msgP with
    | inl LC => inl (A_ltr_from_sg_cancellative _ _ _ LC)
    | inr NLC => inr (A_ltr_from_sg_not_cancellative _ _ _ NLC)
    end 
                                                       
; A_ltr_props_is_right_d :=
    match A_sg_is_right_d _ _ _ msgP with
    | inl IR => inl (A_ltr_from_sg_is_right _ _ _ IR)
    | inr NIR => inr (A_ltr_from_sg_not_is_right _ _ _ NIR)
    end
(*; A_left_transform_left_constant_d :=
                                   match A_sg_left_constant_d _ _ _ msgP with
                                   | inl LC => inl (ltr_from_sg_left_constant _ _ _ LC)
                                   | inr NLC => inr (ltr_from_sg_not_left_constant _ _ _ NLC)
                                   end 
*) 
|}.

Print cas_ast. 

Definition A_ltr_from_sg_ {S : Type} (A : A_sg S) :=
  let eqv := A_sg_eqv _ A in
  let eq  := A_eqv_eq _ eqv in
  let b   := A_sg_bop _ A in 
  {|
      A_ltr_carrier      := eqv 
    ; A_ltr_label        := eqv 
    ; A_ltr_ltr          := ltr_from_sg (A_sg_bop _ A) 
    ; A_ltr_exists_id_d  :=
        match A_sg_exists_id_d _ A with
        | inl ID  => A_ltr_from_sg_exists_id _ eq b ID
        | inr NID => A_ltr_from_sg_not_exists_id _ eq b NID
        end
    ; A_ltr_exists_ann_d :=
        match A_sg_exists_ann_d _ A with
        | inl ANN  => A_ltr_from_sg_exists_ann _ eq b ANN
        | inr NANN => A_ltr_from_sg_not_exists_ann _ eq b NANN
        end
    ; A_ltr_props        :=
        A_ltr_from_sg_properties eq b (A_sg_props _ A)  
    ; A_ltr_ast          := Cas_ast("FIX ME", nil)
  |}. 



End ACAS.

Section CAS.

End CAS.

Section Verify.
 
End Verify.   
  
