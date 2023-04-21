Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.
Require Import CAS.coq.theory.set. (* for uop_duplicate_elim *)
Require Import CAS.coq.uop.properties.
Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.eqv.theory.
Require Import CAS.coq.eqv.set.
Require Import CAS.coq.eqv.list.
Require Import CAS.coq.sg.properties. 
Require Import CAS.coq.sg.lift.
Require Import CAS.coq.sg.union. 
Require Import CAS.coq.ltr.properties.
Require Import CAS.coq.ltr.structures.
Require Import CAS.coq.ltr.classify.
Require Import CAS.coq.ltr.cast.
Require Import CAS.coq.algorithms.list_congruences. 


Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Open Scope string_scope.
Import ListNotations.

Open Scope list.

Section Compute.

Definition ltr_lift_op {L S : Type} (eq : brel S) (ltr : ltr_type L S): ltr_type L (finite_set S) :=
    λ x Y,  uop_duplicate_elim eq (map (ltr x) Y). 

End Compute.   

Section Theory.

Variables (L : Type)
          (S : Type)
          (eqL : brel L)
          (eqS : brel S)
          (wL : L)          
          (wS : S)
          (refL : brel_reflexive L eqL)          
          (ref : brel_reflexive S eqS)
          (sym : brel_symmetric S eqS)
          (trn : brel_transitive S eqS)
          (ltr : ltr_type L S)
          (ltr_cong: A_ltr_congruence eqL eqS ltr). 

Lemma A_ltr_lift_congruence : A_ltr_congruence eqL (brel_set eqS) (ltr_lift_op eqS ltr). 
Proof. intros l1 l2 X Y H1 H2. 
       unfold A_ltr_congruence in ltr_cong.
       apply uop_duplicate_elim_congruence_v2; auto.       
       apply (map_set_congruence _ _ eqS eqS (ltr l1) (ltr l2)); auto. 
Qed.

Lemma in_set_ltr_lift_elim (l : L) ( X : finite_set S) (s : S)
  (A: in_set eqS (ltr_lift_op eqS ltr l X) s = true) :
    { x : S & (in_set eqS X x = true) * (eqS (ltr l x) s = true)}.
Proof. apply in_set_uop_duplicate_elim_elim in A.
       apply (in_set_map_elim _ _ eqS eqS) in A; auto. 
Qed. 


Lemma in_set_ltr_lift_intro (l : L) ( X : finite_set S) (s : S) 
  (A : { x : S & (in_set eqS X x = true) * (eqS (ltr l x) s = true)}) :
     in_set eqS (ltr_lift_op eqS ltr l X) s = true. 
Proof. apply in_set_uop_duplicate_elim_intro; auto. 
       apply (in_set_map_intro _ _ eqS eqS); auto. 
Qed.

Lemma A_ltr_lift_not_cancellative (nlc : A_ltr_not_cancellative eqS ltr) :
      A_ltr_not_cancellative (brel_set eqS) (ltr_lift_op eqS ltr) .
Proof. destruct nlc as [[l [a b]] [P Q]].
       exists (l, (a :: nil, b ::nil)).
       compute. rewrite P, Q. apply sym in P. rewrite P. auto. 
Defined.
 
Lemma A_ltr_lift_cancellative (lc : A_ltr_cancellative eqS ltr) :
      A_ltr_cancellative (brel_set eqS) (ltr_lift_op eqS ltr) .
Proof. intros l X Y A.
       apply brel_set_elim_prop in A; auto. destruct A as [A B]. 
       apply brel_set_intro_prop; auto. split; intros s C.
       + assert (D : in_set eqS (ltr_lift_op eqS ltr l X) (ltr l s) = true).
            apply in_set_ltr_lift_intro; auto. exists s. auto. 
         assert (E := A _ D).
         apply in_set_ltr_lift_elim in E; auto. destruct E as [x [E F]].
         apply lc in F.
         exact (in_set_right_congruence S eqS sym trn _ _ _ F E). 
       + assert (D : in_set eqS (ltr_lift_op eqS ltr l Y) (ltr l s) = true).
            apply in_set_ltr_lift_intro; auto. exists s. auto. 
         assert (E := B _ D).
         apply in_set_ltr_lift_elim in E; auto. destruct E as [x [E F]].
         apply lc in F.
         exact (in_set_right_congruence S eqS sym trn _ _ _ F E). 
Qed. 


Lemma A_ltr_lift_not_is_right (nr : A_ltr_not_is_right eqS ltr) :
  A_ltr_not_is_right (brel_set eqS) (ltr_lift_op eqS ltr). 
Proof. destruct nr as [[l s] P]. 
       exists (l, s :: nil). compute.
       rewrite P. reflexivity. 
Defined.

Lemma A_ltr_lift_is_right (ir : A_ltr_is_right eqS ltr) :
  A_ltr_is_right (brel_set eqS) (ltr_lift_op eqS ltr). 
Proof. intros l X.
       apply brel_set_intro_prop; auto. split; intros s A.
       + apply in_set_ltr_lift_elim in A; auto.
         destruct A as [x [A B]].
         assert (C := ir l x).
         apply sym in C.
         assert (D := trn _ _ _ C B).
         exact (in_set_right_congruence S eqS sym trn _ _ _ D A).          
       + apply in_set_ltr_lift_intro; auto.
         assert (B := ir l s).
         exists s. auto. 
Qed. 

Lemma A_ltr_lift_not_exists_id (nid : A_ltr_not_exists_id eqS ltr) :
  A_ltr_not_exists_id (brel_set eqS) (ltr_lift_op eqS ltr). 
Proof. intro l. destruct (nid l) as [s P]. 
       exists (s :: nil). compute. rewrite P.
       reflexivity. 
Defined.

Lemma A_ltr_lift_exists_id (id : A_ltr_exists_id eqS ltr) :
  A_ltr_exists_id (brel_set eqS) (ltr_lift_op eqS ltr). 
Proof. destruct id as [l P].
       exists l. intro X. 
        apply brel_set_intro_prop; auto. split.
        + intros s A.
          apply in_set_ltr_lift_elim in A; auto.
          destruct A as [x [A B]].
          assert (C := P x).
          apply sym in C.
          assert (D := trn _ _ _ C B). 
          exact (in_set_right_congruence S eqS sym trn _ _ _ D A). 
        + intros s A.
          apply in_set_ltr_lift_intro.
          assert (B := P s).
          exists s. split; auto. 
Defined. 
 
Lemma A_ltr_lift_is_ann : A_ltr_is_ann (brel_set eqS) (ltr_lift_op eqS ltr) nil.
Proof. intro l. compute. reflexivity. Qed.

Lemma A_ltr_lift_exists_ann : A_ltr_exists_ann (brel_set eqS) (ltr_lift_op eqS ltr). 
Proof. exists nil.  apply A_ltr_lift_is_ann. Defined.

(* note: with ltr's the annihilator need not be unique. *) 
Lemma A_ltr_lift_exists_ann_version_v2 (annP : A_ltr_exists_ann eqS ltr) :
  A_ltr_exists_ann (brel_set eqS) (ltr_lift_op eqS ltr).
Proof. destruct annP as [ann P]. 
       exists (ann :: nil). intro l. compute. 
       assert (A := P l). rewrite A. rewrite (sym _ _ A). reflexivity. 
Defined.

(*
Lemma ltr_lift_not_left_constant :
      ltr_not_left_constant L (finite_set S) (brel_set eqS) (ltr_lift eqS ltr) .
Proof. exists (wL, (nil, wS ::nil)). compute. reflexivity. Defined.
*) 
End Theory.

Section ACAS.

Definition A_ltr_lift_properties {L S : Type} 
  (eqL : brel L) (eqS : brel S)
  (ltr : ltr_type L S)
  (eqvL : eqv_proofs L eqL) (eqvS : eqv_proofs S eqS)
  (ltrP : A_ltr_properties eqL eqS ltr) :
  A_ltr_properties eqL (brel_set eqS) (ltr_lift_op eqS ltr) :=
let refL := A_eqv_reflexive _ _ eqvL in
let ref  := A_eqv_reflexive _ _ eqvS in
let sym  := A_eqv_symmetric _ _ eqvS in
let trn  := A_eqv_transitive _ _ eqvS in
let ltr_cong := A_ltr_props_congruence _ _ _ ltrP in
{|
  A_ltr_props_congruence          :=
    A_ltr_lift_congruence L S eqL eqS refL ref sym trn ltr ltr_cong
; A_ltr_props_cancellative_d :=
    match A_ltr_props_cancellative_d _ _ _ ltrP with
    | inl  lc => inl(A_ltr_lift_cancellative L S eqL eqS refL ref sym trn ltr ltr_cong lc)
    | inr nlc => inr(A_ltr_lift_not_cancellative L S eqS sym ltr nlc)
    end                                                               
; A_ltr_props_is_right_d          :=
    match A_ltr_props_is_right_d _ _ _ ltrP with
    | inl irP  => inl (A_ltr_lift_is_right L S eqL eqS refL ref sym trn ltr ltr_cong irP)
    | inr nirP => inr (A_ltr_lift_not_is_right L S eqS ltr nirP)
    end
|}.

Definition A_ltr_lift {L S : Type} (A : @A_ltr L S) :=
let eqvS := A_ltr_carrier A in
let eqvL := A_ltr_label A in     
let eqS := A_eqv_eq _ eqvS in
let eqL := A_eqv_eq _ eqvL in
let eqvSP := A_eqv_proofs _ eqvS in
let eqvLP := A_eqv_proofs _ eqvL in
let refL := A_eqv_reflexive _ _ eqvLP in
let ref := A_eqv_reflexive _ _ eqvSP in
let sym := A_eqv_symmetric _ _ eqvSP in
let trn := A_eqv_transitive _ _ eqvSP in
let ltr := A_ltr_ltr A in
let ltrP := A_ltr_props A in 
let ltr_cong := A_ltr_props_congruence _ _ _ ltrP in 
{|
  A_ltr_carrier      := A_eqv_set S eqvS 
; A_ltr_label        := eqvL 
; A_ltr_ltr          := ltr_lift_op eqS ltr 
; A_ltr_exists_id_d  :=
    match A_ltr_exists_id_d A with
    | inl idP  => inl (A_ltr_lift_exists_id L S eqL eqS refL ref sym trn ltr ltr_cong idP) 
    | inr nidP => inr (A_ltr_lift_not_exists_id L S eqS ltr nidP)
    end
; A_ltr_exists_ann_d := inl (A_ltr_lift_exists_ann L S eqS ltr)
; A_ltr_props        := A_ltr_lift_properties eqL eqS ltr eqvLP eqvSP ltrP 
; A_ltr_ast          := Cas_ast ("left_transform_lift", [])  (*Ast_ltr_lift (A_left_transform_ast _ _ A)*) 
|}.

End ACAS.

Section AMCAS.

Definition A_ltr_lift_below_ltr {L S : Type} (A : @A_below_ltr L S) : @A_below_ltr L (finite_set S) :=
  A_classify_ltr (A_ltr_lift (A_cast_up_ltr A)). 
  

Definition A_mcas_ltr_lift {L S : Type} (A : @A_ltr_mcas L S) : @A_ltr_mcas L (finite_set S) :=
match A with
| A_MCAS_ltr B          => A_MCAS_ltr (A_ltr_lift_below_ltr B)
| A_MCAS_ltr_Error sl1  => A_MCAS_ltr_Error sl1
end.
  

End AMCAS. 

Section CAS.

Definition ltr_lift_properties {L S : Type}
  (ltrP : @ltr_properties L S) :
  @ltr_properties L (finite_set S) := 
{|
  ltr_props_cancellative_d :=
    match ltr_props_cancellative_d ltrP with
    | inl (LTR_cancellative (l, s))  =>
        inl(LTR_cancellative (l, set_witness s))
    | inr (LTR_not_cancellative (l, (s, s'))) =>
        inr(LTR_not_cancellative (l, (s :: nil, s' :: nil)))
    end                                                               
; ltr_props_is_right_d          :=
    match ltr_props_is_right_d ltrP with
    | inl (LTR_is_right (l, s))  =>
        inl (LTR_is_right (l, set_witness s))
    | inr (LTR_not_is_right (l, s)) =>
        inr (LTR_not_is_right (l, s :: nil))
    end
|}.


Definition ltr_lift {L S : Type} (A : @ltr L S) :=
{|
  ltr_carrier      := eqv_set (ltr_carrier A)
; ltr_label        := ltr_label A
; ltr_ltr          := ltr_lift_op (eqv_eq (ltr_carrier A)) (ltr_ltr A)
; ltr_exists_id_d  :=
    match ltr_exists_id_d A with
    | inl idP  => inl idP 
    | inr (LTR_not_exists_id l) => inr (LTR_not_exists_id l)
    end
; ltr_exists_ann_d := inl (LTR_exists_ann nil)
; ltr_props        := ltr_lift_properties (ltr_props A) 
; ltr_ast          := Cas_ast ("left_transform_lift", [])  (*Ast_ltr_lift (left_transform_ast _ _ A)*) 
|}.
  

End CAS. 

Section MCAS.

Definition ltr_lift_below_ltr {L S : Type} (A : @below_ltr L S) : @below_ltr L (finite_set S) :=
  classify_ltr (ltr_lift (cast_up_ltr A)). 
  

Definition mcas_ltr_lift {L S : Type} (A : @ltr_mcas L S) : @ltr_mcas L (finite_set S) :=
match A with
| MCAS_ltr B          => MCAS_ltr (ltr_lift_below_ltr B)
| MCAS_ltr_Error sl1  => MCAS_ltr_Error sl1
end.
  

End MCAS. 



Section Verify.

Lemma correct_ltr_lift_properties
  (L S : Type) (wL : L) (wS : S)
  (eqL : brel L) (eqS : brel S)
  (ltr : ltr_type L S)
  (eqvL : eqv_proofs L eqL)(eqvS : eqv_proofs S eqS)           
  (ltrP : A_ltr_properties eqL eqS ltr) :
  P2C_ltr_properties
    eqL (brel_set eqS) 
    (ltr_lift_op eqS ltr) 
    (A_ltr_lift_properties eqL eqS ltr eqvL eqvS ltrP)
    wL (set_witness wS)
  = 
  ltr_lift_properties (P2C_ltr_properties eqL eqS ltr ltrP wL wS). 
Proof. destruct ltrP. unfold ltr_lift_properties,
         A_ltr_lift_properties, P2C_ltr_properties; simpl.
       destruct A_ltr_props_cancellative_d as [ lc | [[s [t u]] [P Q]]];
       destruct A_ltr_props_is_right_d as [ir | [[a b] nir]]; simpl;
       try reflexivity.     
Qed. 

Theorem correct_left_transform_insert (L S : Type) (A : @A_ltr L S)  : 
         ltr_lift (A2C_ltr A) 
         = 
         A2C_ltr (A_ltr_lift A). 
Proof. destruct A.
       unfold ltr_lift, A_ltr_lift, A2C_ltr; simpl.
       rewrite correct_eqv_set.       
       rewrite correct_ltr_lift_properties.        
       destruct (A_ltr_exists_id_d) as [[id P] | nid]; simpl; 
       try reflexivity. 
Qed.


Lemma correct_mcas_ltr_lift (L S : Type) (A : @A_ltr_mcas L S):
  mcas_ltr_lift (A2C_mcas_ltr A)
  = 
    A2C_mcas_ltr (A_mcas_ltr_lift A).
Proof. destruct A; simpl; try reflexivity.
       destruct a; simpl. unfold ltr_lift_below_ltr.
       unfold cast_up_ltr. unfold classify_ltr.
       rewrite correct_left_transform_insert.
       reflexivity. 
Qed. 
  
End Verify.   

