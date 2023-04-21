(*

   x |> inr X    = inr ({x} union X) 
   x |> inl SELF = inr {x} 

Note : It might seem that SELF is not needed since 
     x |> inr{}    = inr {x} 
However, when this is used in a semigroup-left-transform with 
union as addition, we need SELF as the additive annihilator 
(the most preferred set of next hops). 
But {} is the additive identity!  (the worst set of next hops) 

*) 

Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.
Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.eqv.theory.
Require Import CAS.coq.eqv.add_constant. 
Require Import CAS.coq.eqv.set.
Require Import CAS.coq.eqv.sum.
Require Import CAS.coq.theory.set. 
Require Import CAS.coq.sg.properties. 
Require Import CAS.coq.sg.union.
Require Import CAS.coq.sg.or. 
Require Import CAS.coq.tr.properties.
Require Import CAS.coq.tr.structures.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.


Open Scope string_scope.
Import ListNotations.

Open Scope list.


Section Compute.

Definition ltr_insert {S : Type} (eq : brel S): ltr_type S (with_constant (finite_set S)) :=
  λ x y,
  match y with
  | inl _ => inr (x :: nil)
  | inr X => inr (bop_union eq (x :: nil) X)
  end.

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

  Lemma ltr_insert_congruence :
    ltr_congruence S
                   (with_constant (finite_set S))
                   eq
                   (brel_sum brel_constant (brel_set eq))
                   (ltr_insert eq). 
  Proof. intros s1 s2 [c1 | X1] [c2 | X2] H1 H2; simpl. 
         + compute. rewrite H1. apply sym in H1. rewrite H1. reflexivity. 
         + compute in H2. discriminate H2. 
         + compute in H2. discriminate H2. 
         + assert (H3 : brel_set eq (s1 :: nil) (s2 :: nil) = true). compute. rewrite H1.
           apply sym in H1. rewrite H1. reflexivity. 
           exact (bop_union_congruence S eq ref sym trn _ _ _ _ H3 H2). 
 Qed.

  Lemma ltr_insert_not_left_cancellative :
    ltr_not_left_cancellative S
                              (with_constant (finite_set S))                              
                              (brel_sum brel_constant (brel_set eq))
                              (ltr_insert eq). 
  Proof. unfold ltr_left_cancellative.
         exists (wS, (inr nil, inr (wS::nil))); simpl.  split.
         + apply brel_set_intro_prop; auto. split.
           ++ intros a A.
              apply in_set_bop_union_elim in A; auto.
              destruct A as [A | A].
              +++ apply in_set_singleton_elim in A; auto. 
                  apply in_set_bop_union_intro; auto.
                  left. compute. apply sym in A. rewrite A.
                  reflexivity. 
              +++ compute in A. discriminate A. 
           ++ intros a A.
              apply in_set_bop_union_elim in A; auto.
              destruct A as [A | A].
              +++ apply in_set_singleton_elim in A; auto. 
                  apply in_set_bop_union_intro; auto.
                  left. compute. apply sym in A. rewrite A.
                  reflexivity. 
              +++ apply in_set_singleton_elim in A; auto.
                  apply in_set_bop_union_intro; auto.
                  left. compute. apply sym in A. rewrite A.
                  reflexivity. 
         + compute. reflexivity. 
Defined. 

  Lemma ltr_insert_not_left_constant :
    ltr_not_left_constant S
                          (with_constant (finite_set S))                              
                          (brel_sum brel_constant (brel_set eq))
                          (ltr_insert eq). 
 Proof. exists (wS, (inr nil, inr ((f wS) :: nil))).
        destruct (nt wS) as [F1 F2]. simpl. 
        case_eq(brel_set eq (bop_union eq (wS :: nil) nil) (bop_union eq (wS :: nil) (f wS :: nil))); intro A; auto.
        + apply brel_set_elim_prop in A; auto.
          destruct A as [A B].
          assert (C : in_set eq (bop_union eq (wS :: nil) (f wS :: nil)) (f wS) = true).
             apply in_set_bop_union_intro; auto.
             right; compute. rewrite ref. reflexivity. 
          assert (D := B _ C).
          apply in_set_bop_union_elim in D; auto.
          destruct D as [D | D].
          ++ compute in D. rewrite F2 in D. discriminate D. 
          ++ compute in D. discriminate D. 
 Defined.

 Lemma ltr_insert_not_is_right :
   ltr_not_is_right S
                    (with_constant (finite_set S))                              
                    (brel_sum brel_constant (brel_set eq))
                    (ltr_insert eq). 
 Proof. exists (wS, inr nil). compute; auto. Defined.
 
 Lemma ltr_insert_not_exists_id :
   ltr_not_exists_id S
                    (with_constant (finite_set S))                              
                    (brel_sum brel_constant (brel_set eq))
                    (ltr_insert eq). 
 Proof. intro s. exists (inr nil). compute; auto. Defined.

Lemma ltr_insert_enum_is_ann (enum : carrier_is_finite S eq) : 
  ltr_is_ann S
             (with_constant (finite_set S))                              
             (brel_sum brel_constant (brel_set eq))
             (ltr_insert eq)
             (inr ((projT1 enum) tt)).
Proof. assert (A := bop_union_enum_is_ann S eq ref sym trn enum).
         intro s. unfold ltr_insert.
         destruct (A (s :: nil)) as [B C]. exact C. 
Qed. 

Lemma ltr_insert_exists_ann (enum : carrier_is_finite S eq) :
  ltr_exists_ann S
                 (with_constant (finite_set S))                              
                 (brel_sum brel_constant (brel_set eq))
                 (ltr_insert eq).
Proof. exists (inr (projT1 enum tt)). apply ltr_insert_enum_is_ann. Defined.

Lemma list_set_hack : ∀ l s,  in_set eq l s = true -> in_list eq l s = true. 
Proof. induction l; intros s A.
       + compute in A. discriminate A. 
       + simpl. simpl in A.
         apply bop_or_intro. apply bop_or_elim in A.
         destruct A as [A | A]. 
         ++ left. exact A. 
         ++ right. apply IHl; auto. 
Qed. 
       
Lemma ltr_insert_not_exists_ann (nfin : carrier_is_not_finite S eq) :
  ltr_not_exists_ann S
                     (with_constant (finite_set S))                              
                     (brel_sum brel_constant (brel_set eq))
                     (ltr_insert eq). 
  intros s. unfold carrier_is_not_finite in nfin. 
  unfold ltr_not_is_ann. unfold ltr_insert.
  destruct s as [c | s].
  + exists wS. compute. reflexivity. 
  + assert (A := nfin (fun tt => s)). simpl in A.
    destruct A as [t P].
    exists t. 
    case_eq(brel_set eq (bop_union eq (t :: nil) s) s); intro B; auto.
    ++ apply brel_set_elim_prop in B; auto.
       destruct B as [B C].
       assert (D : set.in_set eq (bop_union eq (t :: nil) s) t = true).
          apply in_set_bop_union_intro; auto. left. compute. rewrite (ref t). reflexivity. 
       assert (E := B t D).
       assert (F := list_set_hack s t E).
      rewrite F in P.
      discriminate P. 
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

Definition ltr_insert_proofs :
  left_transform_proofs S
                        (with_constant (finite_set S))                              
                        (brel_sum brel_constant (brel_set eq))
                        eq
                        (ltr_insert eq) :=
let ref := A_eqv_reflexive _ _ eqvP in
let sym := A_eqv_symmetric _ _ eqvP in
let trn := A_eqv_transitive _ _ eqvP in     
{|
  A_left_transform_congruence          := ltr_insert_congruence S eq ref sym trn
; A_left_transform_is_right_d          := inr(ltr_insert_not_is_right S eq wS)
; A_left_transform_left_constant_d     := inr(ltr_insert_not_left_constant S eq wS f nt ref sym trn)                                               
; A_left_transform_left_cancellative_d := inr(ltr_insert_not_left_cancellative S eq wS ref sym trn)
|}.

End Proofs.

Definition A_left_transform_insert (S : Type) (eqv : A_eqv S) (c : cas_constant) :=
let eq := A_eqv_eq _ eqv in
let wS := A_eqv_witness S eqv in
let f  := A_eqv_new S eqv in
let nt  := A_eqv_not_trivial S eqv in
let eqvP := A_eqv_proofs _ eqv in
let ref := A_eqv_reflexive _ _ eqvP in
let sym := A_eqv_symmetric _ _ eqvP in
let trn := A_eqv_transitive _ _ eqvP in 
{|
  A_left_transform_carrier      := A_eqv_add_constant _ (A_eqv_set S eqv) c 
; A_left_transform_label        := eqv                                                     
; A_left_transform_ltr          := ltr_insert eq 
; A_left_transform_exists_id_d  := inr(ltr_insert_not_exists_id S eq) 
; A_left_transform_exists_ann_d :=
                        match A_eqv_finite_d _ eqv with
                        | inl fin => inl (ltr_insert_exists_ann S eq ref sym trn fin) 
                        | inr nfin => inr (ltr_insert_not_exists_ann S eq wS ref sym trn nfin)
                        end 
; A_left_transform_proofs       := ltr_insert_proofs S eq wS f nt eqvP 
; A_left_transform_ast          := Cas_ast ("A_left_transform_insert", [])  (* Ast_ltr_insert (A_eqv_ast S eqv) *)
|}.

End ACAS.

Section CAS.

Definition ltr_insert_certs {S : Type} (wS : S) (f : S -> S) : @left_transform_certificates S (with_constant (list S)) := 
{|
  left_transform_congruence            := Assert_Ltr_Congruence 
; left_transform_is_right_d            := Certify_Ltr_Not_Is_Right (wS, inr nil)
; left_transform_left_constant_d       := Certify_Ltr_Not_Left_Constant (wS, (inr nil, inr ((f wS) :: nil)))
; left_transform_left_cancellative_d   := Certify_Ltr_Not_Left_Cancellative (wS, (inr nil, inr (wS :: nil)))
|}.


Definition left_transform_insert {S : Type} (eqv : @eqv S) (c : cas_constant) :=
{|
  left_transform_carrier      := eqv_add_constant (eqv_set eqv) c 
; left_transform_label        := eqv                                                     
; left_transform_ltr          := ltr_insert (eqv_eq eqv)
; left_transform_exists_id_d  := Certify_Ltr_Not_Exists_Id
; left_transform_exists_ann_d :=
                        match eqv_finite_d eqv with
                        | Certify_Is_Finite f => Certify_Ltr_Exists_Ann (inr (f tt)) 
                        | Certify_Is_Not_Finite => Certify_Ltr_Not_Exists_Ann 
                        end 
; left_transform_certs        := ltr_insert_certs (eqv_witness eqv) (eqv_new eqv) 
; left_transform_ast          := Cas_ast ("A_left_transform_insert", []) (*Ast_ltr_insert (eqv_ast eqv)*) 
|}.
  

End CAS. 
Section Verify.

Lemma correct_ltr_insert_certs (S : Type) (eS : A_eqv S): 
  P2C_left_transform
    S
    (with_constant (finite_set S))
    (brel_sum brel_constant (brel_set (A_eqv_eq S eS)))
    (A_eqv_eq S eS)
    (ltr_insert (A_eqv_eq S eS))
    (ltr_insert_proofs S
                       (A_eqv_eq S eS)
                       (A_eqv_witness S eS)
                       (A_eqv_new S eS)
                       (A_eqv_not_trivial S eS)                                                          
                       (A_eqv_proofs S eS)
    ) 
    =                    
    ltr_insert_certs (A_eqv_witness S eS) (A_eqv_new S eS).
Proof. destruct eS. destruct A_eqv_proofs.
       destruct A_eqv_finite_d; compute; reflexivity. Qed. 


Theorem correct_left_transform_insert (S : Type) (eS : A_eqv S) (c : cas_constant) : 
         left_transform_insert (A2C_eqv S eS) c
         = 
         A2C_left_transform S (with_constant (finite_set S)) (A_left_transform_insert S eS c). 
Proof. unfold left_transform_insert, A_left_transform_insert, A2C_left_transform; simpl.
       rewrite correct_ltr_insert_certs.
       rewrite correct_eqv_set.
       rewrite correct_eqv_add_constant. 
       destruct (A_eqv_finite_d S eS) as [[f P] | nfin]; simpl; 
       try reflexivity. 
Qed. 
  
  
 
End Verify.   
