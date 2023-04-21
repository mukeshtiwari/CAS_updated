Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.

Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.eqv.theory.
Require Import CAS.coq.eqv.list.

Require Import CAS.coq.sg.and. 

Require Import CAS.coq.ltr.properties.
Require Import CAS.coq.ltr.structures.
Require Import CAS.coq.ltr.classify.
Require Import CAS.coq.ltr.cast. 
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Open Scope list.

Open Scope string_scope.
Import ListNotations.


Section Compute.

 Definition ltr_cons_op : ∀ {S : Type}, ltr_type S (list S) := λ {S} x y,  (x :: y) .   

End Compute.   


Section Theory.

  Variable S : Type.
  Variable eq : brel S.
  Variable wS : S.
  Variable ref : brel_reflexive S eq. 


 Lemma A_ltr_cons_congruence : A_ltr_congruence eq (brel_list eq) ltr_cons_op. 
 Proof. intros s1 s2 l1 l2 H1 H2. unfold ltr_cons_op.
        apply brel_list_cons_intro; auto. 
 Qed.

 Lemma A_ltr_cons_not_is_right : A_ltr_not_is_right (brel_list eq) ltr_cons_op. 
 Proof. exists (wS, nil). compute; auto. Defined.

 Lemma A_ltr_cons_cancellative : A_ltr_cancellative (brel_list eq) ltr_cons_op. 
 Proof. intros s l1 l2 H. unfold ltr_cons_op in H.
        apply brel_list_cons_elim in H. destruct H as [H G]; auto. 
 Qed.        

 Lemma A_ltr_cons_not_exists_id : A_ltr_not_exists_id (brel_list eq) ltr_cons_op. 
 Proof. intro s. exists nil. compute; auto. Defined.

Lemma list_cons_not_ann (l : list S) : ∀ (s : S), brel_list eq (ltr_cons_op s l) l = false.
Proof. induction l.
        + intro s. compute. reflexivity. 
        + intro s. unfold ltr_cons_op in *. 
          case_eq(brel_list eq (s :: a :: l) (a :: l)); intro A; auto.
          apply brel_list_cons_elim in A. destruct A as [A B].
          rewrite (IHl a) in B. discriminate B. 
Qed. 

Lemma A_ltr_cons_not_exists_ann : A_ltr_not_exists_ann (brel_list eq) ltr_cons_op. 
Proof. unfold A_ltr_not_exists_ann, ltr_cons_op. unfold A_ltr_not_is_ann. 
       intro l. exists wS. apply list_cons_not_ann. 
Defined.
 
 (*
 Lemma A_ltr_cons_not_constant : A_ltr_not_left_constant (brel_list eq) ltr_cons. 
 Proof. exists (wS, (nil, wS :: nil)). compute. rewrite (ref wS). reflexivity. Defined.
 *) 
 
End Theory.

Section ACAS.

  Definition A_ltr_cons_properties {S : Type} (eq : brel S) (wS : S) (eqvP : eqv_proofs S eq) :
    A_ltr_properties eq (brel_list eq) ltr_cons_op :=
    {|
       A_ltr_props_congruence     := A_ltr_cons_congruence S eq
     ; A_ltr_props_is_right_d     := inr (A_ltr_cons_not_is_right S eq wS)
     ; A_ltr_props_cancellative_d := inl (A_ltr_cons_cancellative S eq)
    |}. 

  Definition A_ltr_cons {S : Type} (A : A_eqv S) : @A_ltr S (list S) :=
    let eq := A_eqv_eq _ A in
    let wS := A_eqv_witness _ A in     
    {|
      A_ltr_carrier      := A_eqv_list _ A  
    ; A_ltr_label        := A
    ; A_ltr_ltr          := ltr_cons_op 
    ; A_ltr_exists_id_d  := inr (A_ltr_cons_not_exists_id _ eq)
    ; A_ltr_exists_ann_d := inr (A_ltr_cons_not_exists_ann _ eq wS) 
    ; A_ltr_props        := A_ltr_cons_properties eq wS (A_eqv_proofs _ A)
    ; A_ltr_ast          := Cas_ast ("ltr_cons", [Cas_eqv_ast(A_eqv_ast S A)]) 
    |}.


End ACAS.

Section AMCAS.

Definition A_mcas_ltr_cons {S : Type} (A : @A_mcas_eqv S) : @A_ltr_mcas S (list S) :=
match A with
| A_EQV_eqv B    => A_MCAS_ltr (A_Below_ltr_top (A_ltr_cons B))
| A_EQV_Error sl => A_MCAS_ltr_Error sl 
end.
  

End AMCAS.   

Section CAS.

  Definition ltr_cons_properties {S : Type} (wS : S) :
    @ltr_properties S (list S) :=
    {|
       ltr_props_is_right_d     := inr (LTR_not_is_right (wS, nil))
     ; ltr_props_cancellative_d := inl (LTR_cancellative (wS, nil))
    |}. 

  Definition ltr_cons {S : Type} (A : @eqv S) : @ltr S (list S) :=
    let wS := eqv_witness A in     
    {|
      ltr_carrier      := eqv_list A  
    ; ltr_label        := A
    ; ltr_ltr          := ltr_cons_op
    ; ltr_exists_id_d  := inr (LTR_not_exists_id wS)
    ; ltr_exists_ann_d := inr (LTR_not_exists_ann nil) 
    ; ltr_props        := ltr_cons_properties wS 
    ; ltr_ast          := Cas_ast ("ltr_cons", [Cas_eqv_ast(eqv_ast A)]) 
    |}.
  

End CAS.

Section MCAS.

Definition mcas_ltr_cons {S : Type} (A : @mcas_eqv S) : @ltr_mcas S (list S) :=
match A with
| EQV_eqv B    => MCAS_ltr (Below_ltr_top (ltr_cons B))
| EQV_Error sl => MCAS_ltr_Error sl 
end.
  

End MCAS.   



Section Verify.


Lemma correct_ltr_cons_properties (S : Type) (eS : A_eqv S): 
    ltr_cons_properties (A_eqv_witness S eS)
    =                    
    P2C_ltr_properties
        (A_eqv_eq S eS)
        (brel_list (A_eqv_eq S eS))
        ltr_cons_op 
        (A_ltr_cons_properties (A_eqv_eq S eS) (A_eqv_witness S eS) (A_eqv_proofs S eS))
        (A_eqv_witness S eS) nil. 
Proof. unfold A_ltr_cons_properties, ltr_cons_properties, P2C_ltr_properties.
       destruct eS. simpl. unfold p2c_ltr_not_is_right, p2c_ltr_cancellative.
       unfold A_ltr_cons_not_is_right. simpl. 
       reflexivity.
Qed. 


Theorem correct_mcas_ltr_cons (S : Type) (eS : A_eqv S)  : 
        ltr_cons (A2C_eqv S eS) 
         = 
         A2C_ltr (A_ltr_cons eS). 
Proof. unfold ltr_cons, A_ltr_cons, A2C_ltr; simpl. 
       rewrite correct_eqv_list. 
       rewrite <- correct_ltr_cons_properties.
       unfold A_ltr_cons_not_exists_id, A_ltr_cons_not_exists_ann,
         p2c_ltr_not_exists_id, p2c_ltr_not_exists_ann; simpl. 
       reflexivity. 
Qed. 
  
  
Theorem correct_ltr_cons (S : Type) (eS : @A_mcas_eqv S)  : 
        mcas_ltr_cons (A2C_mcas_eqv S eS) 
         = 
        A2C_mcas_ltr (A_mcas_ltr_cons eS).
Proof. destruct eS; 
       unfold mcas_ltr_cons, A_mcas_ltr_cons, A2C_mcas_eqv, A2C_mcas_ltr; auto. 
Qed.        
 
End Verify.   
  
