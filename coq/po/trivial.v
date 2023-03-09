Require Import Coq.Bool.Bool. 

Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.
Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.po.properties.
Require Import CAS.coq.po.structures.


Section Compute.

Definition brel_trivial {S : Type} :  brel S  := λ  x y, true. 

End Compute.   

Section Theory.

Variable S  : Type.
Variable eq : brel S.
Variable wS : S.
Variable f  : S -> S.
Variable nt : brel_not_trivial S eq f. 
  

Lemma brel_trivial_congruence : brel_congruence S eq brel_trivial. 
Proof. compute; intros; auto. Qed. 

Lemma brel_trivial_reflexive : brel_reflexive S brel_trivial. 
Proof. compute; intros; auto. Qed. 

Lemma brel_trivial_transitive : brel_transitive S brel_trivial. 
Proof. compute; intros; auto. Qed. 

Lemma brel_trivial_not_antisymmetric :
     brel_not_antisymmetric S eq brel_trivial. 
Proof. exists (wS, f wS). compute; intros; auto.
       destruct (nt wS) as [A B]. rewrite A. auto. 
Defined. 


Lemma brel_trivial_total : brel_total S brel_trivial. 
Proof. compute; intros; auto. Qed. 


Lemma brel_trivial_not_exists_qo_top : 
    brel_not_exists_qo_top S eq brel_trivial. 
Proof. intro s. unfold brel_not_is_qo_top. right.
       unfold lte_equiv_not_unique.
       destruct (nt s) as [A B].
       exists (f s); compute; auto. 
Defined.

Lemma brel_trivial_not_exists_qo_bottom : 
    brel_not_exists_qo_bottom S eq brel_trivial. 
Proof. intro s. unfold brel_not_is_qo_bottom. right.
       unfold lte_equiv_not_unique.
       destruct (nt s) as [A B].
       exists (f s); compute; auto. 
Defined.

Lemma brel_trivial_trivial : order_trivial S brel_trivial. 
Proof. intros s t. compute; reflexivity. Qed. 

End Theory.

Section ACAS.

Definition qo_proofs_trivial (S : Type) (eq : brel S) (wS : S) (f : S → S) (nt : brel_not_trivial S eq f) : 
    qo_proofs S eq brel_trivial := 
{|
  A_qo_congruence      := brel_trivial_congruence S eq
; A_qo_reflexive       := brel_trivial_reflexive S 
; A_qo_transitive      := brel_trivial_transitive S 
; A_qo_antisymmetric_d := inr (brel_trivial_not_antisymmetric S eq wS f nt)
; A_qo_total_d         := inl (brel_trivial_total S)
; A_qo_trivial_d       := inl (brel_trivial_trivial S)                                           
|}. 


Definition A_qo_trivial {S : Type} (eqv : A_eqv S) : @A_qo S := 
  let wS := A_eqv_witness S eqv in
  let f  := A_eqv_new S eqv in
  let nt := A_eqv_not_trivial S eqv in      
  let eq := A_eqv_eq S eqv in
  {| 
     A_qo_eqv                 := eqv 
   ; A_qo_lte                 := brel_trivial
   ; A_qo_exists_top_d    := inr (brel_trivial_not_exists_qo_top S eq f nt)
   ; A_qo_exists_bottom_d := inr (brel_trivial_not_exists_qo_bottom S eq f nt)
   ; A_qo_proofs              := qo_proofs_trivial S eq wS f nt
   ; A_qo_ast                 := Ast_or_trivial (A_eqv_ast S eqv)
   |}. 

End ACAS.

Section AMCAS.

  Definition A_mcas_qo_trivial {S : Type} (meqv : @A_mcas_eqv S) :=
    match meqv with
    | A_EQV_Error sl => A_MCAS_qo_Error sl
    | A_EQV_eqv eqv  => A_MCAS_qo (A_Below_qo_top (A_qo_trivial eqv))
    end.
  
End AMCAS.   
 

Section CAS.

Definition qo_certs_trivial {S : Type} (wS : S) (f : S -> S) : @qo_certificates S := 
{|
  qo_congruence      := Assert_Brel_Congruence
; qo_reflexive       := Assert_Reflexive 
; qo_transitive      := Assert_Transitive 
; qo_antisymmetric_d := Certify_Not_Antisymmetric (wS, f wS) 
; qo_total_d         := Certify_Total
; qo_trivial_d       := Certify_Order_Trivial 
|}. 

Definition qo_trivial {S : Type} :  @eqv S -> @qo S 
:= λ eqv,
  let wS := eqv_witness eqv in
  let f := eqv_new eqv in           
  {| 
     qo_eqv             := eqv
   ; qo_lte             := brel_trivial
   ; qo_exists_top_d    := Certify_Not_Exists_Qo_Top 
   ; qo_exists_bottom_d := Certify_Not_Exists_Qo_Bottom 
   ; qo_certs           := qo_certs_trivial wS f 
   ; qo_ast             := Ast_or_trivial (eqv_ast eqv)
   |}. 
 
End CAS.

Section MCAS.


    Definition mcas_qo_trivial {S : Type} (meqv : @mcas_eqv S) :=
    match meqv with
    | EQV_Error sl => MCAS_qo_Error sl
    | EQV_eqv eqv  => MCAS_qo (Below_qo_top (qo_trivial eqv))
    end.

End MCAS.   


Section Verify.
  
Lemma correct_qo_certs_trivial (S : Type) (eq : brel S) (wS : S) (f : S -> S) (nt : brel_not_trivial S eq f): 
       qo_certs_trivial wS f 
       = 
       P2C_qo eq brel_trivial (qo_proofs_trivial S eq wS f nt).
Proof. compute. reflexivity. Qed. 


Theorem correct_or_trivial (S : Type) (E : A_eqv S):  
         qo_trivial (A2C_eqv S E)  = A2C_qo (A_qo_trivial E). 
Proof. unfold qo_trivial, A_qo_trivial, A2C_qo; simpl. 
       rewrite <- correct_qo_certs_trivial. reflexivity.        
Qed.


Theorem correct_mcas_or_trivial (S : Type) (E : @A_mcas_eqv S):  
  mcas_qo_trivial (A2C_mcas_eqv S E)
  =
  A2C_qo_mcas (A_mcas_qo_trivial E). 
Proof. destruct E; simpl. 
       + reflexivity.
       + rewrite <- correct_or_trivial. reflexivity.        
Qed.



End Verify.   
  
