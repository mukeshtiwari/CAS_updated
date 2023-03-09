Require Import Coq.Strings.String.

Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.

Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.

Require Import CAS.coq.po.properties.
Require Import CAS.coq.po.structures.
Require Import CAS.coq.po.theory.
Require Import CAS.coq.po.from_sg.

Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures.
Require Import CAS.coq.sg.cast_up.


Require Import CAS.coq.bs.properties.
Require Import CAS.coq.bs.structures.

Require Import CAS.coq.os.properties.
Require Import CAS.coq.os.structures.
Require Import CAS.coq.os.theory.


Section Theory.

Variable S  : Type.
Variable eq : brel S.
Variable wS : S.
Variable f  : S -> S.
Variable nt : brel_not_trivial S eq f. 
Variable ref : brel_reflexive S eq.
Variable sym : brel_symmetric S eq. 
Variable trn : brel_transitive S eq. 

Variable plus  : binary_op S.
Variable cong : bop_congruence S eq plus.
Variable asso : bop_associative S eq plus.
Variable idem : bop_idempotent S eq plus.
Variable comm : bop_commutative S eq plus.

Definition left_lte := brel_lte_left eq plus.
Definition right_lte := brel_lte_right eq plus.

Notation "a [=] b"   := (eq a b = true)          (at level 15).
Notation "a [+] b"   := (plus a b)          (at level 15).

(* 
         
A : b [=] (b [+] c)
============================
(a [+] b) [=] ((a [+] b) [+] (a [+] c))

a [+] b = a [+] (b [+] c) 
        = (a [+] a) [+] (b [+] c) 
        = a [+] (a [+] (b [+] c)) 
        = a [+] ((a [+] b) [+] c)
        = a [+] ((b [+] a) [+] c)
        = a [+] (b [+] (a [+] c)) 
        = (a [+] b) [+] (a [+] c)
*)  
Lemma os_from_sg_left_left_monotone : os_left_monotone left_lte plus. 
Proof. compute. intros a b c A.
       assert (B : (a [+] b) [=] (a [+] (b [+] c))).
          exact (cong _ _ _ _ (ref a) A). 
       assert (C : (a [+] (b [+] c)) [=] ((a [+] a) [+] (b [+] c))). 
          exact (cong _ _ _ _ (sym _ _ (idem a)) (ref (b [+] c))).
       assert (D : ((a [+] a) [+] (b [+] c)) [=] (a [+] (a [+] (b [+] c)))). 
          apply asso. 
       assert (E : (a [+] (a [+] (b [+] c))) [=] (a [+] ((a [+] b) [+] c))). 
          exact (cong _ _ _ _ (ref a) (sym _ _ (asso a b c))). 
       assert (F : (a [+] ((a [+] b) [+] c)) [=] (a [+] ((b [+] a) [+] c))).
          exact (cong _ _ _ _ (ref a) (cong _ _ _ _ (comm a b) (ref c))).
       assert (G : (a [+] ((b [+] a) [+] c)) [=] (a [+] (b [+] (a [+] c)))). 
          exact (cong _ _ _ _ (ref a) (asso b a c)).
       assert (H : (a [+] (b [+] (a [+] c))) [=] ((a [+] b) [+] (a [+] c))). 
          exact (sym _ _ (asso a b (a [+] c))). 
       exact (trn _ _ _ B (trn _ _ _ C (trn _ _ _ D (trn _ _ _ E (trn _ _ _ F (trn _ _ _ G H)))))). 
Qed.        

Lemma os_from_sg_right_left_monotone : os_left_monotone right_lte plus.
Proof. compute. intros a b c A.
       assert (B : (a [+] c) [=] (a [+] (b [+] c))).
          exact (cong _ _ _ _ (ref a) A). 
       assert (C : (a [+] (b [+] c)) [=] ((a [+] a) [+] (b [+] c))). 
          exact (cong _ _ _ _ (sym _ _ (idem a)) (ref (b [+] c))).
       assert (D : ((a [+] a) [+] (b [+] c)) [=] (a [+] (a [+] (b [+] c)))). 
          apply asso. 
       assert (E : (a [+] (a [+] (b [+] c))) [=] (a [+] ((a [+] b) [+] c))). 
          exact (cong _ _ _ _ (ref a) (sym _ _ (asso a b c))). 
       assert (F : (a [+] ((a [+] b) [+] c)) [=] (a [+] ((b [+] a) [+] c))).
          exact (cong _ _ _ _ (ref a) (cong _ _ _ _ (comm a b) (ref c))).
       assert (G : (a [+] ((b [+] a) [+] c)) [=] (a [+] (b [+] (a [+] c)))). 
          exact (cong _ _ _ _ (ref a) (asso b a c)).
       assert (H : (a [+] (b [+] (a [+] c))) [=] ((a [+] b) [+] (a [+] c))). 
          exact (sym _ _ (asso a b (a [+] c))). 
       exact (trn _ _ _ B (trn _ _ _ C (trn _ _ _ D (trn _ _ _ E (trn _ _ _ F (trn _ _ _ G H)))))). 
Qed.        



Lemma os_from_sg_left_right_monotone : os_right_monotone left_lte plus. 
Proof. compute. intros a b c A. 
       assert (B := os_from_sg_left_left_monotone a b c A). compute in B.
       assert (C := comm b a).
       assert (D := cong _ _ _ _ (comm a b) (comm a c)).
       exact (trn _ _ _ C (trn _ _ _ B D)).
Qed.        

Lemma os_from_sg_right_right_monotone : os_right_monotone right_lte plus. 
Proof. compute. intros a b c A. 
       assert (B := os_from_sg_right_left_monotone a b c A). compute in B.
       assert (C := comm c a).
       assert (D := cong _ _ _ _ (comm a b) (comm a c)).
       exact (trn _ _ _ C (trn _ _ _ B D)).
Qed.        

Lemma os_from_sg_left_not_left_increasing : os_not_left_increasing left_lte plus.
Proof. compute.
       destruct (nt wS) as [F1 F2]. 
       case_eq (left_lte wS (f wS)); intro A; compute in A.
       + case_eq (left_lte (f wS) wS); intro B; compute in B.
         ++ assert (C := brel_lte_left_antisymmetric S eq sym trn plus comm _ _ A B).
            rewrite F1 in C. discriminate C. 
         ++ exists (f wS, wS).
            admit. 
       + case_eq (left_lte (f wS) wS); intro B; compute in B.
         ++ exists (wS, f wS).
            admit. 
         ++ exists (f wS, wS).
            admit. 
Admitted. 

Lemma os_from_sg_right_left_increasing : os_left_increasing right_lte plus.
Proof. intros s t. compute.
       assert (A : (s [+] t) [=] ((s [+] s) [+] t)).
          exact (sym _ _ (cong _ _ _ _ (idem s) (ref t))). 
       assert (B := asso s s t). 
       exact (trn _ _ _ A B). 
Qed. 

Lemma os_from_sg_left_right_increasing : os_right_increasing left_lte plus.
Proof. compute.
Admitted.

Lemma os_from_sg_right_right_increasing : os_right_increasing right_lte plus.
Proof. intros s t. compute.
       assert (A : (t [+] s) [=] (t [+] (s [+] s))).
          exact (sym _ _ (cong _ _ _ _ (ref t) (idem s))). 
       assert (B := sym _ _ (asso t s s)).
       assert (C := comm (t [+] s) s). 
       exact (trn _ _ _ A (trn _ _ _ B C)).
Qed. 



Lemma os_from_sg_left_exists_top_ann_equal
      (P : bop_exists_ann S eq plus) :
           A_os_exists_top_ann_equal eq right_lte plus.
Proof. destruct P as [a A].
       exists a; split; auto. intro s.
       destruct (A s) as [B C]. compute. 
       exact (sym _ _ C). 
Defined.


Lemma os_from_bs_left_exists_bottom_id_equal
      (P : bop_exists_id S eq plus) :
           A_os_exists_bottom_id_equal eq right_lte plus.
Proof. destruct P as [a A].
       exists a; split; auto. intro s. 
       destruct (A s) as [B C]. compute. 
       exact (sym _ _ B). 
Defined.

Definition os_from_bs_left_exists_bottom_id_equal_decidable
       (P : bop_exists_id_decidable S eq plus) :
            os_exists_bottom_id_decidable S eq right_lte plus := 
  match P with
  | inl idP  => Bottom_Id_Proof_Equal _ _ _ _ (os_from_bs_left_exists_bottom_id_equal idP) 
  | inr nidP => Bottom_Id_Proof_None _ _ _ _ (brel_lte_right_not_exists_bottom S eq sym trn plus comm nidP, nidP)
end.

Definition os_from_sg_righ_exists_top_ann_equal_decidable
       (P : bop_exists_ann_decidable S eq plus) :
            os_exists_top_ann_decidable S eq right_lte plus := 
  match P with
  | inl annP  => Top_Ann_Proof_Equal _ _ _ _ (os_from_sg_left_exists_top_ann_equal annP) 
  | inr nannP => Top_Ann_Proof_None _ _ _ _ (brel_lte_right_not_exists_top S eq sym trn plus comm nannP, nannP) 
end.



End Theory.

(* 
Section ACAS.

Section Proofs. 

Variables (S : Type) (eq : brel S) (eqvP : eqv_proofs S eq) (plus : binary_op S).


Definition os_from_sg_right_bounded_proofs
           (idP : bop_exists_id S eq plus) 
           (annP : bop_exists_ann S eq plus) :  
                os_bounded_proofs S eq (brel_lte_right eq plus) plus := 
let sym := A_eqv_symmetric _ _ eqvP in
{|
  A_bounded_bottom_id := os_from_bs_left_exists_bottom_id_equal S eq sym plus idP
; A_bounded_top_ann   := os_from_sg_left_exists_top_ann_equal S eq sym plus annP
|}.


Definition os_from_sg_right_monotone_increasing_proofs
           (sgP : sg_CI_proofs S eq plus) : 
              os_monotone_increasing_proofs S (brel_lte_right eq plus) plus := 
let ref := A_eqv_reflexive _ _ eqvP in
let sym := A_eqv_symmetric _ _ eqvP in     
let trn := A_eqv_transitive _ _ eqvP in   
let cong := A_sg_CI_congruence _ _ _ sgP in
let comm := A_sg_CI_commutative _ _ _ sgP in
let idem := A_sg_CI_idempotent _ _ _ sgP in
let asso := A_sg_CI_associative _ _ _ sgP in 
{|
  A_mono_inc_left_monotonic   := os_from_sg_right_left_monotone S eq ref sym trn plus cong asso idem comm
; A_mono_inc_right_monotonic  := os_from_sg_right_right_monotone S eq ref sym trn plus cong asso idem comm

; A_mono_inc_left_increasing  := os_from_sg_right_left_increasing S eq ref sym trn plus cong asso idem 
; A_mono_inc_right_increasing := os_from_sg_right_right_increasing S eq ref sym trn plus cong asso idem comm 
|}. 
  
End Proofs.

Section Combinators.


Definition A_os_from_sg_BCI_right (S :Type) (D : A_sg_BCI S) : A_bounded_monotone_increasing_posg S :=
let eqv        := A_sg_BCI_eqv _ D in
let eq         := A_eqv_eq _ eqv in
let wS         := A_eqv_witness _ eqv in
let f          := A_eqv_new _ eqv in
let nt         := A_eqv_not_trivial _ eqv in
let eqvP       := A_eqv_proofs _ eqv in
let plus       := A_sg_BCI_bop _ D in
let plusP      := A_sg_BCI_proofs _ D in
let idP        := A_sg_BCI_exists_id _ D in
let annP       := A_sg_BCI_exists_ann _ D in
{|
  A_bmiposg_eqv          := eqv 
; A_bmiposg_lte          := brel_lte_right eq plus
; A_bmiposg_times        := plus 
; A_bmiposg_lte_proofs   := po_proofs_from_sg_CI_right_proofs S eq eqvP plus plusP 
; A_bmiposg_times_proofs := A_sg_proofs_from_sg_CI_proofs _ eq plus wS f nt eqvP plusP 
; A_bmiposg_top_bottom   := os_from_sg_right_bounded_proofs S eq eqvP plus idP annP 
; A_bmiposg_proofs       := os_from_sg_right_monotone_increasing_proofs S eq eqvP plus plusP 
; A_bmiposg_ast          := Ast_os_from_sg_right (A_sg_BCI_ast _ D)
|}.


End Combinators.   
  
End ACAS.

Section AMCAS.

Local Open Scope string_scope.
Local Open Scope list_scope.     

Definition A_mcas_os_from_sg_right  (S : Type) (A : A_sg_mcas S) :=
  match A_sg_classify _ A with
  | A_MCAS_sg_BCI _ B => A_OS_bounded_monotone_increasing_posg _ (A_os_from_sg_BCI_right _ B)
  | _ => A_OS_Error _ ("mcas_os_from_sg_right : this combinator (currently) requires a bounded idempotent and commutative semigrou (sg_BCI)" :: nil) 
  end. 

End AMCAS.   

Section CAS.


Section Certs. 

Definition os_from_sg_right_bounded_certs {S : Type} 
           (P : @assert_exists_id S) (Q : @assert_exists_ann S) : @os_bounded_certs S := 
{|
  bounded_bottom_id := match P with
                       | Assert_Exists_Id id => Assert_Os_Exists_Bottom_Id_Equal id 
                       end 
; bounded_top_ann   := match Q with
                       | Assert_Exists_Ann ann => Assert_Os_Exists_Top_Ann_Equal ann
                       end 
|}.

Definition os_from_sg_right_monotone_increasing_certs {S : Type} 
           (P : @sg_CI_certificates S) : @os_monotone_increasing_certificates S := 
{|
  mono_inc_left_monotonic   := Assert_Left_Monotone
; mono_inc_right_monotonic  := Assert_Right_Monotone
; mono_inc_left_increasing  := Assert_Left_Increasing
; mono_inc_right_increasing := Assert_Right_Increasing
|}. 
  
End Certs.

Section Combinators.

Definition os_from_sg_BCI_right {S :Type} (D : @sg_BCI S) : @bounded_monotone_increasing_posg S := 
let eqv        := sg_BCI_eqv D in
let eq         := eqv_eq eqv in
let wS         := eqv_witness eqv in
let f          := eqv_new eqv in
let plus       := sg_BCI_bop D in
let plusP      := sg_BCI_certs D in
let idP        := sg_BCI_exists_id D in
let annP       := sg_BCI_exists_ann D in
{|
  bmiposg_eqv          := eqv 
; bmiposg_lte          := brel_lte_right eq plus
; bmiposg_times        := plus 
; bmiposg_lte_certs    := po_certs_from_sg_CI_right_certs plusP 
; bmiposg_times_certs  := sg_certs_from_sg_CI_certs _ eq plus wS f plusP 
; bmiposg_top_bottom   := os_from_sg_right_bounded_certs idP annP 
; bmiposg_certs        := os_from_sg_right_monotone_increasing_certs plusP 
; bmiposg_ast          := Ast_os_from_sg_right (sg_BCI_ast D)
|}.

End Combinators.  
End CAS.


Section MCAS.

Local Open Scope string_scope.
Local Open Scope list_scope.

Definition mcas_os_from_sg_right {S : Type} (A : @sg_mcas S) :=
  match sg_classify _ A with
  | MCAS_sg_BCI B => OS_bounded_monotone_increasing_posg (os_from_sg_BCI_right B)
  | _ => OS_Error ("mcas_os_from_sg_right : this combinator (currently) requires a bounded idempotent and commutative semigrou (sg_BCI)" :: nil) 
  end. 



End MCAS.   



Section Verify.

Lemma correct_os_from_sg_right_bounded_certs
      (S : Type)
      (eq : brel S)
      (eqvP : eqv_proofs S eq)
      (plus : binary_op S)
      (idP : bop_exists_id S eq plus)
      (annP : bop_exists_ann S eq plus) : 
        P2C_os_bounded_proofs S eq (brel_lte_right eq plus) plus 
          (os_from_sg_right_bounded_proofs S eq eqvP plus idP annP)
        = 
        os_from_sg_right_bounded_certs
          (Assert_Exists_Id (projT1 idP))
          (Assert_Exists_Ann (projT1 annP)).
Proof. destruct idP as [id P]; destruct annP as [ann Q].
       compute. reflexivity. 
Qed.        

Lemma correct_os_from_sg_right_monotone_increasing_certs
      (S : Type) (eq : brel S) (eqvP : eqv_proofs S eq) (plus : binary_op S) (plusP : sg_CI_proofs S eq plus): 
   P2C_os_monotone_increasing_proofs S
          (brel_lte_right eq plus)
          plus
          (os_from_sg_right_monotone_increasing_proofs S eq eqvP plus plusP)
  =
  os_from_sg_right_monotone_increasing_certs (P2C_sg_CI S eq plus plusP). 
Proof. destruct plusP.
       unfold os_from_sg_right_monotone_increasing_proofs,
       os_from_sg_right_monotone_increasing_certs, P2C_sg_CI,
       P2C_os_monotone_increasing_proofs; simpl. 
       reflexivity.
Qed.        
  
Theorem correct_mcas_os_from_sg_right (S : Type) (A : A_sg_mcas S) :
 A2C_mcas_os (A_mcas_os_from_sg_right S A) 
 =       
 mcas_os_from_sg_right (A2C_mcas_sg S A). 
Proof. unfold A_mcas_os_from_sg_right, mcas_os_from_sg_right.
       rewrite correct_sg_classify. 
       destruct (A_sg_classify S A); simpl; try reflexivity.
       destruct a;
       unfold A_os_from_sg_BCI_right, os_from_sg_BCI_right,
              A2C_bounded_monotone_increasing_posg, A2C_sg_BCI; simpl. 
       rewrite correct_po_certs_from_sg_CI_right_certs.
       rewrite correct_os_from_sg_right_monotone_increasing_certs. 
       rewrite correct_os_from_sg_right_bounded_certs.
       unfold sg_certs_from_sg_CI_certs, A_sg_proofs_from_sg_CI_proofs.
       rewrite <- correct_sg_certs_from_sg_C_certs.        
       rewrite <- correct_sg_C_certs_from_sg_CI_certs.
       reflexivity.
Qed.       

End Verify.

*) 
