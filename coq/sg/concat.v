Require Import Coq.Bool.Bool.

Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.

Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.eqv.theory.
Require Import CAS.coq.eqv.list.

Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures.
Require Import CAS.coq.sg.and. 

Section Theory.

Open Scope list_scope.
  
Lemma bop_concat_not_idempotent : 
     ∀ (S : Type) (r : brel S) (s : S), 
           bop_not_idempotent (list S) (@brel_list S r) (@bop_concat S).
Proof. intros S r s. unfold bop_not_idempotent. exists (s :: nil). simpl. 
       rewrite andb_comm. simpl. reflexivity. 
Defined. 

Lemma bop_concat_not_commutative : 
   ∀ (S : Type) (r : brel S) (s : S) (f : S -> S), (brel_not_trivial S r f) -> bop_not_commutative (list S) (@brel_list S r) (@bop_concat S).
Proof. intros S r s f fP. 
       exists (s :: nil, (f s) :: nil). unfold bop_concat. 
       rewrite <- List.app_comm_cons. rewrite <- List.app_comm_cons. 
       rewrite List.app_nil_l. rewrite List.app_nil_l.
       unfold brel_list. destruct (fP s) as [L R]. rewrite L. simpl.  reflexivity. 
Defined. 

Lemma bop_concat_not_selective : 
   ∀ (S : Type) (r : brel S) (s : S) (f : S -> S), brel_not_trivial S r f -> bop_not_selective (list S) (@brel_list S r) (@bop_concat S).
Proof. intros S r s f fP. 
       exists (s :: nil, (f s) :: nil). 
       rewrite <- List.app_comm_cons. rewrite List.app_nil_l. 
       unfold brel_list.  destruct (fP s) as [L R]. 
       rewrite L, andb_comm.  simpl. auto. 
Defined. 


Lemma bop_concat_congruence : 
   ∀ (S : Type) (r : brel S),  (brel_reflexive S r) -> bop_congruence (list S) (@brel_list S r) (@bop_concat S).
Proof. unfold bop_congruence, bop_concat. intros S r refS. 
       induction s1; induction s2; induction t1; induction t2; unfold brel_list; intros H Q. 
       rewrite List.app_nil_l. reflexivity. 
       discriminate. discriminate. discriminate. discriminate. 
       fold @brel_list. rewrite List.app_nil_l. rewrite List.app_nil_l. 
          fold @brel_list in Q. unfold brel_list. fold @brel_list. assumption.
       discriminate. discriminate. discriminate. discriminate. 
       fold @brel_list. rewrite List.app_nil_r. rewrite List.app_nil_r. 
          fold @brel_list in H. unfold brel_list. fold @brel_list. assumption.
       discriminate. discriminate. discriminate. discriminate. 
       fold @brel_list. fold @brel_list in H, Q. 
       rewrite <- List.app_comm_cons. rewrite <- List.app_comm_cons.
       unfold brel_list. fold @brel_list. 
       destruct (bop_and_elim _ _ H) as [H1 H2]. 
       rewrite H1. simpl. 
       apply IHs1. assumption. 
       unfold brel_list. fold @brel_list. assumption. 
Qed. 


Lemma bop_concat_associative : 
   ∀ (S : Type) (r : brel S),  (brel_reflexive S r) -> bop_associative (list S) (@brel_list S r) (@bop_concat S).
Proof. intros S r refS. unfold bop_concat, bop_associative. 
       intros s t u. 
       rewrite List.app_assoc. 
       apply brel_list_reflexive. assumption. 
Qed. 

Lemma bop_concat_not_is_left : 
   ∀ (S : Type) (r : brel S) (s : S), bop_not_is_left (list S) (@brel_list S r) (@bop_concat S).
Proof. intros S r s. unfold bop_concat, bop_not_is_left. 
       exists (nil, s :: nil). rewrite List.app_nil_l. 
       unfold brel_list. reflexivity. 
Defined. 


Lemma bop_concat_not_is_right : 
   ∀ (S : Type) (r : brel S) (s : S), bop_not_is_right (list S) (@brel_list S r) (@bop_concat S).
Proof. intros S r s. unfold bop_concat, bop_not_is_right. 
       exists (s :: nil, nil). rewrite List.app_nil_r. 
       unfold brel_list. reflexivity. 
Defined. 

Lemma bop_concat_exists_id : ∀ (S : Type) (r : brel S), 
                  brel_reflexive S r -> bop_exists_id (list S) (@brel_list S r) (@bop_concat S).
Proof. intros S r refS. exists nil. intro s. split. 
          unfold bop_concat. rewrite List.app_nil_l. apply brel_list_reflexive; auto. 
          unfold bop_concat. rewrite List.app_nil_r. apply brel_list_reflexive; auto. 
Defined. 

Lemma bop_concat_not_exists_ann: ∀ (S : Type) (r : brel S) (witness : S), 
                  bop_not_exists_ann (list S) (@brel_list S r) (@bop_concat S).
Proof. intros S r witness. unfold bop_not_exists_ann. intro a. 
       case_eq(a). 
          intro Q. exists (witness :: nil). left. compute. reflexivity.
          intros s l H. unfold bop_concat. exists (witness :: nil). right. 
             rewrite <- List.app_comm_cons. rewrite List.app_nil_l.
             apply brel_list_not_cons_equal_left. 
Defined. 

Lemma brel_list_cons : ∀ (S : Type) (r : brel S) (a : S) (l1 l2 : list S), 
         brel_reflexive S r -> @brel_list S r (a :: l1) (a :: l2) = @brel_list S r l1 l2. 
Proof. intros S r a l1 l2 refS. unfold brel_list at 1. fold @brel_list. 
       rewrite (refS a). simpl. reflexivity. 
Qed. 

Lemma  bop_concat_left_cancellative : ∀ (S : Type) (r : brel S), 
       brel_reflexive S r -> 
         bop_left_cancellative (list S) (@brel_list S r) (@bop_concat S).
Proof. unfold bop_left_cancellative. intros S r refS. induction s; intros t u H.
       simpl in H. assumption. 
       unfold bop_concat in H. fold @bop_concat in H. 
       rewrite <- List.app_comm_cons in H. rewrite <- List.app_comm_cons in H.  
       rewrite brel_list_cons in H; auto.  
Qed.        

Lemma bop_concat_right_cancellative : ∀ (S : Type) (r : brel S), 
         bop_right_cancellative (list S) (@brel_list S r) (@bop_concat S).
Proof. unfold bop_right_cancellative, bop_concat. 
       intros S r. induction s; induction t; induction u; intro H.
          compute. reflexivity. 
          compute in H. discriminate. 
          compute in H. discriminate. 
          rewrite List.app_nil_r in H.  rewrite List.app_nil_r in H. assumption. 
          compute. reflexivity. 
          compute. simpl in H. apply bop_and_elim in H. destruct H as [L R].
             rewrite concat_cons_no_left_id in R; auto. 
          compute. simpl in H. apply bop_and_elim in H. destruct H as [L R].
             rewrite concat_cons_no_left_id_v2 in R; auto.              
          rewrite <- List.app_comm_cons in H. rewrite <- List.app_comm_cons in H.
          unfold brel_list in H. fold @brel_list in H.
          apply bop_and_elim in H. destruct H as [L R].
          apply IHt in R.
          unfold brel_list. fold @brel_list.
          apply bop_and_intro; auto. 
Qed. 

Lemma  bop_concat_not_left_constant : ∀ (S : Type) (r : brel S) (s : S), 
         bop_not_left_constant (list S) (@brel_list S r) (@bop_concat S).
Proof. intros S r s . exists (nil, (nil, s :: nil)); simpl. reflexivity. Defined. 

Lemma  bop_concat_not_right_constant : ∀ (S : Type) (r : brel S) (s : S), 
         bop_not_right_constant (list S) (@brel_list S r) (@bop_concat S).
Proof. intros S r s. exists (nil, (nil, s :: nil)); simpl. reflexivity. Defined. 


Lemma  bop_concat_not_anti_left : ∀ (S : Type) (r : brel S) (s : S), 
         brel_reflexive S r -> bop_not_anti_left (list S) (@brel_list S r) (@bop_concat S).
Proof. intros S r s refS. exists (s :: nil, nil); simpl. 
       rewrite (refS s). simpl. reflexivity. 
Defined. 


Lemma  bop_concat_not_anti_right : ∀ (S : Type) (r : brel S) (s : S), 
         brel_reflexive S r -> bop_not_anti_right (list S) (@brel_list S r) (@bop_concat S).
Proof. intros S r s refS. exists (s :: nil, nil); simpl. 
       rewrite (refS s). simpl. reflexivity. 
Defined. 


End Theory.

Section ACAS.


Definition sg_proofs_concat : ∀ (S : Type) (eqvS : A_eqv S), sg_proofs (list S) (brel_list (A_eqv_eq S eqvS)) (@bop_concat S)
:= λ S eqvS, 
let eqvP := A_eqv_proofs S eqvS in 
let rS   := A_eqv_eq S eqvS in
let s    := A_eqv_witness S eqvS in
let f    := A_eqv_new S eqvS in
let nt   := A_eqv_not_trivial S eqvS in 
let refS := A_eqv_reflexive _ _ eqvP in 
{|
  A_sg_associative   := bop_concat_associative S rS refS 
; A_sg_congruence    := bop_concat_congruence S rS refS

; A_sg_left_cancel_d    := inl _ (bop_concat_left_cancellative S rS refS)
; A_sg_right_cancel_d   := inl _ (bop_concat_right_cancellative S rS)
                                                
; A_sg_commutative_d    := inr _ (bop_concat_not_commutative S rS s f nt)
; A_sg_selective_d      := inr _ (bop_concat_not_selective S rS s f nt)
; A_sg_is_left_d        := inr _ (bop_concat_not_is_left S rS s)
; A_sg_is_right_d       := inr _ (bop_concat_not_is_right S rS s)
; A_sg_idempotent_d     := inr _ (bop_concat_not_idempotent S rS s)
; A_sg_left_constant_d  := inr _ (bop_concat_not_left_constant S rS s)
; A_sg_right_constant_d := inr _ (bop_concat_not_right_constant S rS s)
; A_sg_anti_left_d      := inr _ (bop_concat_not_anti_left S rS s refS)
; A_sg_anti_right_d     := inr _ (bop_concat_not_anti_right S rS s refS)
|}.


Definition A_sg_concat : ∀ (S : Type),  A_eqv S -> A_sg (list S) 
:= λ S eqvS,
let eqvP := A_eqv_proofs S eqvS in 
let rS   := A_eqv_eq S eqvS in
let s    := A_eqv_witness S eqvS in
let f    := A_eqv_new S eqvS in
let nt   := A_eqv_not_trivial S eqvS in 
let refS := A_eqv_reflexive _ _ eqvP in 
{| 
     A_sg_eqv         := A_eqv_list S eqvS
   ; A_sg_bop        := @bop_concat S
   ; A_sg_exists_id_d   := inl _ (bop_concat_exists_id S rS refS)
   ; A_sg_exists_ann_d  := inr _ (bop_concat_not_exists_ann S rS s)
   ; A_sg_proofs     := sg_proofs_concat S eqvS
   ; A_sg_ast        := Ast_sg_concat (A_eqv_ast S eqvS)
   |}. 


End ACAS.


Section AMCAS.

Definition A_mcas_sg_concat (S : Type) (A : @A_mcas_eqv S) : @A_sg_mcas (list S) :=
match A with
| A_EQV_eqv B    => A_MCAS_sg (A_Below_sg_top (A_sg_concat S B))
| A_EQV_Error sl => A_MCAS_sg_Error sl 
end.

End AMCAS.   


Section CAS.

Definition sg_certs_concat : ∀ {S : Type},  @eqv S -> @sg_certificates (list S)
:= λ {S} eqvS,
let s := eqv_witness eqvS in
let f := eqv_new eqvS in 
let t := f s in 
{|
  sg_associative      := Assert_Associative 
; sg_congruence       := Assert_Bop_Congruence 
; sg_commutative_d    := Certify_Not_Commutative  (s :: nil, t :: nil)
; sg_selective_d      := Certify_Not_Selective (s :: nil, t :: nil)
; sg_is_left_d        := Certify_Not_Is_Left (nil, s :: nil)
; sg_is_right_d       := Certify_Not_Is_Right  (s :: nil, nil)
; sg_idempotent_d     := Certify_Not_Idempotent  (s :: nil)
; sg_left_cancel_d    := Certify_Left_Cancellative  
; sg_right_cancel_d   := Certify_Right_Cancellative  
; sg_left_constant_d  := Certify_Not_Left_Constant   (nil, (nil, s :: nil))
; sg_right_constant_d := Certify_Not_Right_Constant  (nil, (nil, s :: nil))
; sg_anti_left_d      := Certify_Not_Anti_Left  (s :: nil, nil) 
; sg_anti_right_d     := Certify_Not_Anti_Right  (s :: nil, nil)
|}. 

Definition sg_concat: ∀ {S : Type},  eqv (S := S) -> sg (S := (list S)) 
:= λ {S} eqvS, 
   {| 
     sg_eqv      := eqv_list eqvS 
   ; sg_bop     := bop_concat
   ; sg_exists_id_d      := Certify_Exists_Id  nil 
   ; sg_exists_ann_d     := Certify_Not_Exists_Ann  
   ; sg_certs   := sg_certs_concat eqvS
   ; sg_ast     := Ast_sg_concat (eqv_ast eqvS)
   |}. 

End CAS.

Section MCAS.

Definition mcas_sg_concat {S : Type} (A : @mcas_eqv S) : @sg_mcas (list S) :=
match A with
| EQV_eqv B    => MCAS_sg (Below_sg_top (sg_concat B))
| EQV_Error sl => MCAS_sg_Error sl 
end.

End MCAS.   


Section Verify.


Lemma correct_sg_certs_concat : 
      ∀ (S : Type) (eS : A_eqv S), 
       sg_certs_concat (A2C_eqv S eS) 
       = 
       P2C_sg (brel_list (A_eqv_eq S eS)) (@bop_concat S) (sg_proofs_concat S eS). 
Proof. intros S eS. compute. reflexivity. Defined. 


Theorem correct_sg_concat : ∀ (S : Type) (eS : A_eqv S), 
         sg_concat (A2C_eqv S eS) 
         = 
         A2C_sg (A_sg_concat S eS). 
Proof. intros S eS. unfold sg_concat, A2C_sg. simpl. 
       rewrite correct_eqv_list. 
       rewrite <- correct_sg_certs_concat. 
       reflexivity. 
Qed. 
  
Theorem correct_mcas_sg_left (S : Type) (eS : @A_mcas_eqv S) : 
         mcas_sg_concat (A2C_mcas_eqv _ eS) 
         = 
         A2C_sg_mcas (A_mcas_sg_concat _ eS). 
Proof.  destruct eS; compute; reflexivity. Qed. 
 
End Verify.   
  
