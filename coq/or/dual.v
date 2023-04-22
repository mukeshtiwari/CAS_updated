Require Import Coq.Bool.Bool. 

Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.
Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.

Require Import CAS.coq.or.properties.
Require Import CAS.coq.or.structures.
Require Import CAS.coq.or.classify.
Require Import CAS.coq.or.cast_up.


Section Compute.

Definition brel_dual {S : Type} (lte : brel S) : brel S := λ x y,  lte y x. 

End Compute.   

Section Theory.

Variable S    : Type.  
Variable eq   : brel S.
Variable refl : brel_reflexive S eq.

Variable lte : brel S.
Variable lteCong : brel_congruence S eq lte.

Lemma brel_dual_congruence : brel_congruence S eq (brel_dual lte). 
Proof. intros s1 s2 s3 s4; compute; intros A B; auto. Qed. 

Lemma brel_dual_trivial (A : order_trivial S lte) :
  order_trivial S (brel_dual lte). 
Proof. intros s t. compute. exact (A t s). Qed. 

Lemma brel_dual_not_trivial (A : order_not_trivial S lte) :
  order_not_trivial S (brel_dual lte). 
Proof. destruct A as [[s t] B]. exists (t, s); compute. exact B. Defined. 

Definition brel_dual_trivial_decide
  (dS : order_trivial_decidable S lte) : order_trivial_decidable S (brel_dual lte)
:= match dS with 
   | inl trv  => inl _ (brel_dual_trivial trv)
   | inr ntrv => inr _ (brel_dual_not_trivial ntrv)
   end.

Lemma brel_dual_reflexive
  (lteRefl : brel_reflexive S lte) :
  brel_reflexive S (brel_dual lte). 
Proof. intros s; compute; auto. Qed. 

Lemma brel_dual_not_reflexive
  (NlteRefl : brel_not_reflexive S lte) :
  brel_not_reflexive S (brel_dual lte). 
Proof. destruct NlteRefl as [s P]. exists s; compute; auto. Defined.

Definition brel_dual_reflexive_decide 
  (dS : brel_reflexive_decidable S lte) :
  brel_reflexive_decidable S (brel_dual lte) := 
   match dS with 
   | inl refl  => inl _ (brel_dual_reflexive refl)
   | inr nrefl => inr _ (brel_dual_not_reflexive nrefl)
   end.  

Lemma brel_dual_transitive
  (lteTran : brel_transitive S lte) :
     brel_transitive S (brel_dual lte).
Proof. intros s1 s2 s3; compute; intros A B; auto.
       exact (lteTran _ _ _ B A).
Qed.

Lemma brel_dual_antisymmetric
  (anti : brel_antisymmetric S eq lte):
  brel_antisymmetric S eq (brel_dual lte).
Proof. intros s1 s2; compute; intros A B; auto. Qed.

Lemma brel_dual_not_antisymmetric
  (nanti : brel_not_antisymmetric S eq lte):
     brel_not_antisymmetric S eq (brel_dual lte).
Proof. destruct nanti as [[s1 s2] [A B]]. exists (s1, s2); compute; split; auto.
       destruct A as [A C]. split; auto.
Defined.

Definition brel_dual_antisymmetric_decide 
  (dS : brel_antisymmetric_decidable S eq lte) :
     brel_antisymmetric_decidable S eq (brel_dual lte)
:= match dS with 
   | inl anti  => inl _ (brel_dual_antisymmetric anti)
   | inr nanti => inr _ (brel_dual_not_antisymmetric nanti)
   end.  

Lemma brel_dual_total
  (tot : brel_total S lte) : brel_total S (brel_dual lte).
Proof. intros s1 s2; compute; auto. Qed. 

Lemma brel_dual_not_total
  (ntot : brel_not_total S lte) : brel_not_total S (brel_dual lte).
Proof. destruct ntot as [[s1 s2] [A B]]. exists (s1, s2). compute; auto. Defined. 

Definition brel_dual_total_decide
  (dS : brel_total_decidable S lte) : brel_total_decidable S (brel_dual lte)
:= match dS with 
   | inl tot  => inl _ (brel_dual_total tot)
   | inr ntot => inr _ (brel_dual_not_total ntot)
   end.

(* po *) 
Lemma brel_dual_exists_bottom
  (topS : brel_exists_top S lte) :
  brel_exists_bottom S (brel_dual lte). 
Proof. destruct topS as [t P]. exists t. apply P. Defined.

Lemma brel_dual_not_exists_bottom
  (ntopS : brel_not_exists_top S lte) :
  brel_not_exists_bottom S (brel_dual lte). 
Proof. intros s. exact (ntopS s). Qed. 

Definition brel_dual_exists_bottom_decide
  (dS : brel_exists_top_decidable S lte) : brel_exists_bottom_decidable S (brel_dual lte)
:= match dS with 
   | inl p  => inl _ (brel_dual_exists_bottom p)
   | inr p => inr _ (brel_dual_not_exists_bottom p)
   end.

Lemma brel_dual_exists_top
  (botS : brel_exists_bottom S lte) :
  brel_exists_top S (brel_dual lte). 
Proof. destruct botS as [b P]. exists b. apply P. Defined.

Lemma brel_dual_not_exists_top
  (nbotS : brel_not_exists_bottom S lte) :
  brel_not_exists_top S (brel_dual lte). 
Proof. intros s. exact (nbotS s). Qed.

Definition brel_dual_exists_top_decide
  (dS : brel_exists_bottom_decidable S lte) : brel_exists_top_decidable S (brel_dual lte)
:= match dS with 
   | inl p  => inl _ (brel_dual_exists_top p)
   | inr p => inr _ (brel_dual_not_exists_top p)
   end.


(* qo *) 
Lemma brel_dual_exists_qo_bottom
  (topS : brel_exists_qo_top S eq lte) :
  brel_exists_qo_bottom S eq (brel_dual lte). 
Proof. destruct topS as [t [P Q]]. exists t.
       split.
       - apply P.
       - intros a A B. exact (Q _ B A). 
Defined.

Lemma brel_dual_not_exists_qo_bottom
  (ntopS : brel_not_exists_qo_top S eq lte) :
  brel_not_exists_qo_bottom S eq (brel_dual lte). 
Proof. intros s. destruct (ntopS s) as [[t A] | [t [[A B] C]]].
       - left. exists t. compute. exact A. 
       - right. exists t; compute; split; auto. 
Qed.

Definition brel_dual_exists_qo_bottom_decide
  (dS : brel_exists_qo_top_decidable S eq lte) :
     brel_exists_qo_bottom_decidable S eq (brel_dual lte)
:= match dS with 
   | inl p  => inl _ (brel_dual_exists_qo_bottom p)
   | inr p => inr _ (brel_dual_not_exists_qo_bottom p)
   end.


Lemma brel_dual_exists_qo_top
  (A : brel_exists_qo_bottom S eq lte) :
  brel_exists_qo_top S eq (brel_dual lte). 
Proof. destruct A as [t [P Q]]. exists t.
       split.
       - apply P.
       - intros a A B. exact (Q _ B A). 
Defined.

Lemma brel_dual_not_exists_qo_top
  (A : brel_not_exists_qo_bottom S eq lte) :
  brel_not_exists_qo_top S eq (brel_dual lte). 
Proof. intros s. destruct (A s) as [[t B] | [t [[B C] D]]].
       - left. exists t. compute. exact B. 
       - right. exists t; compute; split; auto. 
Qed.

Definition brel_dual_exists_qo_top_decide
  (dS : brel_exists_qo_bottom_decidable S eq lte) :
     brel_exists_qo_top_decidable S eq (brel_dual lte)
:= match dS with 
   | inl p  => inl _ (brel_dual_exists_qo_top p)
   | inr p => inr _ (brel_dual_not_exists_qo_top p)
   end.

End Theory.

Section ACAS.

Definition qo_dual_proofs {S : Type}
    (eq lte : brel S)
    (poP : qo_proofs S eq lte) : qo_proofs S eq (brel_dual lte) := 
{|
  A_qo_congruence      := brel_dual_congruence S eq lte (A_qo_congruence _ _ _ poP)  
; A_qo_reflexive       := brel_dual_reflexive S lte (A_qo_reflexive _ _ _ poP)
; A_qo_transitive      := brel_dual_transitive S lte (A_qo_transitive _ _ _ poP)
; A_qo_antisymmetric_d := brel_dual_antisymmetric_decide S eq lte (A_qo_antisymmetric_d _ _ _ poP)
; A_qo_total_d         := brel_dual_total_decide S lte (A_qo_total_d _ _ _ poP)
; A_qo_trivial_d       := brel_dual_trivial_decide S lte (A_qo_trivial_d _ _ _ poP)
|}. 

Definition fo_dual_proofs {S : Type}
    (eq lte : brel S)
    (poP : fo_proofs S eq lte) : fo_proofs S eq (brel_dual lte) := 
{|
  A_fo_congruence      := brel_dual_congruence S eq lte (A_fo_congruence _ _ _ poP)  
; A_fo_reflexive       := brel_dual_reflexive S lte (A_fo_reflexive _ _ _ poP)
; A_fo_transitive      := brel_dual_transitive S lte (A_fo_transitive _ _ _ poP)
; A_fo_antisymmetric_d := brel_dual_antisymmetric_decide S eq lte (A_fo_antisymmetric_d _ _ _ poP)
; A_fo_total           := brel_dual_total S lte (A_fo_total _ _ _ poP)
; A_fo_trivial_d       := brel_dual_trivial_decide S lte (A_fo_trivial_d _ _ _ poP)
|}. 

Definition po_dual_proofs {S : Type}
    (eq lte : brel S)
    (poP : po_proofs S eq lte) : po_proofs S eq (brel_dual lte) := 
{|
  A_po_congruence    := brel_dual_congruence S eq lte (A_po_congruence _ _ _ poP)  
; A_po_reflexive     := brel_dual_reflexive S lte (A_po_reflexive _ _ _ poP)
; A_po_transitive    := brel_dual_transitive S lte (A_po_transitive _ _ _ poP)                                                    
; A_po_antisymmetric := brel_dual_antisymmetric S eq lte (A_po_antisymmetric _ _ _ poP)   
; A_po_not_total      := brel_dual_not_total S lte (A_po_not_total _ _ _ poP)
|}. 

Definition A_qo_dual {S : Type} (R : A_qo S) : A_qo S :=
  let eqv := A_qo_eqv _ R   in 
  let eq  := A_eqv_eq _ eqv in
  let lte := A_qo_lte _ R   in 
  {|
    A_qo_eqv             := eqv 
  ; A_qo_lte             := brel_dual lte
  ; A_qo_exists_top_d    := brel_dual_exists_qo_top_decide _ eq lte (A_qo_exists_bottom_d _ R)
  ; A_qo_exists_bottom_d := brel_dual_exists_qo_bottom_decide _ eq lte (A_qo_exists_top_d _ R)
  ; A_qo_proofs          := qo_dual_proofs eq lte (A_qo_proofs _ R) 
  ; A_qo_ast             := Ast_or_dual (A_qo_ast _ R)
  |}. 

Definition A_po_dual {S : Type} (R : A_po S) : A_po S :=
  let eqv := A_po_eqv _ R   in 
  let eq  := A_eqv_eq _ eqv in
  let lte := A_po_lte _ R   in 
  {|
    A_po_eqv             := eqv 
  ; A_po_lte             := brel_dual lte
  ; A_po_exists_top_d    := brel_dual_exists_top_decide _ lte (A_po_exists_bottom_d _ R)
  ; A_po_exists_bottom_d := brel_dual_exists_bottom_decide _ lte (A_po_exists_top_d _ R)
  ; A_po_proofs          := po_dual_proofs eq lte (A_po_proofs _ R) 
  ; A_po_ast             := Ast_or_dual (A_po_ast _ R)
  |}. 

End ACAS.

Section AMCAS.

  Definition A_order_dual {S : Type} (R : @A_below_qo S) : @A_below_qo S :=
    A_classify_qo (A_qo_dual (A_cast_up_qo R)). 

  Definition A_mcas_order_dual {S : Type} (R : @A_qo_mcas S) : @A_qo_mcas S :=
    match R with
    | A_MCAS_qo A => A_MCAS_qo (A_order_dual A)
    | _ => R
    end.
                  
End AMCAS. 

Section CAS.

Definition brel_dual_trivial_check {S : Type}
   (dS : @order_trivial_certifiable S) :
         @order_trivial_certifiable S 
:= match dS with 
   | Certify_Order_Trivial => Certify_Order_Trivial
   | Certify_Order_Not_Trivial (s, t) => Certify_Order_Not_Trivial (t, s)
   end.

Definition brel_dual_antisymmetric_check {S : Type}
  (dS : @certify_antisymmetric S) : @certify_antisymmetric S
:= match dS with 
   | Certify_Antisymmetric => Certify_Antisymmetric
   | Certify_Not_Antisymmetric p => Certify_Not_Antisymmetric p 
   end.  

Definition brel_dual_total_check {S : Type}
  (dS : @certify_total S) : @certify_total S
  := match dS with
   | Certify_Total            => Certify_Total
   | Certify_Not_Total (s, t) => Certify_Not_Total (s, t)
   end.

Definition brel_dual_exists_bottom_check {S : Type}
  (dS : @certify_exists_top S) : @certify_exists_bottom S
  := match dS with
   | Certify_Exists_Top t   => Certify_Exists_Bottom t
   | Certify_Not_Exists_Top => Certify_Not_Exists_Bottom
   end.

Definition brel_dual_exists_top_check {S : Type}
  (dS : @certify_exists_bottom S) : @certify_exists_top S
  := match dS with
   | Certify_Exists_Bottom b   => Certify_Exists_Top b
   | Certify_Not_Exists_Bottom => Certify_Not_Exists_Top 
   end.

Definition brel_dual_exists_qo_bottom_check {S : Type}
  (dS : @certify_exists_qo_top S) : @certify_exists_qo_bottom S
  := match dS with
   | Certify_Exists_Qo_Top t   => Certify_Exists_Qo_Bottom t
   | Certify_Not_Exists_Qo_Top => Certify_Not_Exists_Qo_Bottom
   end.

Definition brel_dual_exists_qo_top_check {S : Type}
  (dS : @certify_exists_qo_bottom S) : @certify_exists_qo_top S
  := match dS with
   | Certify_Exists_Qo_Bottom b   => Certify_Exists_Qo_Top b
   | Certify_Not_Exists_Qo_Bottom => Certify_Not_Exists_Qo_Top 
     end.

Definition qo_dual_certs {S : Type}
    (poP : @qo_certificates S) : @qo_certificates S := 
{|
  qo_congruence      := qo_congruence poP  
; qo_reflexive       := qo_reflexive poP
; qo_transitive      := qo_transitive poP
; qo_antisymmetric_d := brel_dual_antisymmetric_check (qo_antisymmetric_d poP)
; qo_total_d         := brel_dual_total_check(qo_total_d poP)
; qo_trivial_d       := brel_dual_trivial_check (qo_trivial_d poP)
|}. 

Definition qo_dual {S : Type} (R : @qo S) : @qo S :=
  {|
    qo_eqv             := qo_eqv R
  ; qo_lte             := brel_dual (qo_lte R)
  ; qo_exists_top_d    := brel_dual_exists_qo_top_check (qo_exists_bottom_d R)
  ; qo_exists_bottom_d := brel_dual_exists_qo_bottom_check (qo_exists_top_d R)
  ; qo_certs           := qo_dual_certs (qo_certs R) 
  ; qo_ast             := Ast_or_dual (qo_ast R)
  |}. 

End CAS. 
 
Section AMCAS.

  Definition order_dual {S : Type} (R : @below_qo S) : @below_qo S :=
    classify_qo (qo_dual (cast_up_qo R)). 

  Definition mcas_order_dual {S : Type} (R : @qo_mcas S) : @qo_mcas S :=
    match R with
    | MCAS_qo A => MCAS_qo (order_dual A)
    | _ => R
    end.

End AMCAS. 

Section Verify.

Lemma correct_qo_dual_proofs {S : Type}
    (eq lte : brel S)
    (P : qo_proofs S eq lte) :
  qo_dual_certs (P2C_qo _ _ P)
  =
  P2C_qo _ _ (qo_dual_proofs _ _ P). 
Proof. destruct P; unfold qo_dual_certs, qo_dual_proofs, P2C_qo; simpl.
       destruct A_qo_antisymmetric_d as [ anti | [[s1 s2] [A B]]];
       destruct A_qo_total_d as [tot | [[s3 s4] [C D]]];
       destruct A_qo_trivial_d as [trv | [[s5 s6] E]];
       simpl; reflexivity.   
Qed.

Theorem correct_qo_dual {S : Type} (R : A_qo S) :
  qo_dual (A2C_qo R)
  =
  A2C_qo (A_qo_dual R). 
Proof. destruct R; unfold qo_dual, A_qo_dual, A2C_qo; simpl.
       rewrite correct_qo_dual_proofs. 
       destruct A_qo_exists_top_d as [ [t [A B]] | ntop]; 
       destruct A_qo_exists_bottom_d as [ [b [C D]] | nbot];
       simpl; try reflexivity. 
Qed. 

Theorem correct_order_dual {S : Type} (R : @A_below_qo S) :
  order_dual (A2C_below_qo R)
  =
  A2C_below_qo (A_order_dual R). 
Proof. unfold order_dual, A_order_dual.
       rewrite correct_cast_up_qo. 
       rewrite correct_qo_dual.
       apply correct_classify_qo.
Qed.

Theorem correct_mcas_order_dual {S : Type} (R : @A_qo_mcas S) :
  mcas_order_dual (A2C_qo_mcas R)
  =
  A2C_qo_mcas (A_mcas_order_dual R). 
Proof. destruct R; simpl. 
       - reflexivity. 
       - rewrite correct_order_dual.
         reflexivity.
Qed. 

End Verify. 
