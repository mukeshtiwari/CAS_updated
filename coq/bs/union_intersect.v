Require Import Coq.Bool.Bool.

Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.

Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.eqv.theory. 
Require Import CAS.coq.eqv.set.
Require Import CAS.coq.eqv.sum. 
Require Import CAS.coq.eqv.add_constant. 

Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures.
Require Import CAS.coq.sg.union.
Require Import CAS.coq.sg.intersect.
Require Import CAS.coq.sg.add_id.
Require Import CAS.coq.sg.add_ann.
Require Import CAS.coq.sg.cast_up. 

Require Import CAS.coq.bs.properties.
Require Import CAS.coq.bs.structures.
Require Import CAS.coq.bs.theory. 
Require Import CAS.coq.bs.add_one.
Require Import CAS.coq.bs.add_zero.
Require Import CAS.coq.bs.cast.
Require Import CAS.coq.bs.classify.


Section Theory.

  Variable S: Type.
  Variable r : brel S.
  Variable wS  : S. 
  Variable f : S -> S.
  Variable ntS : brel_not_trivial S r f. 
  Variable refS : brel_reflexive S r.
  Variable symS : brel_symmetric S r.
  Variable tranS : brel_transitive S r.


Lemma A_bs_union_intersect_left_distributive : 
        A_bs_left_distributive (brel_set r) (bop_union r) (bop_intersect r). 
Proof. intros s t u. 
       apply brel_set_intro_prop; auto.
       split; intros a H.        
          apply in_set_bop_union_intro; auto. 
          apply in_set_bop_intersect_elim in H;
          auto. destruct H as [ L R ]. 
          apply in_set_bop_union_elim in R; auto.
          destruct R as [R | R].
             left. apply in_set_bop_intersect_intro; auto. 
             right. apply in_set_bop_intersect_intro; auto. 
       apply in_set_bop_intersect_intro; auto. 
       apply in_set_bop_union_elim in H; auto. 
       destruct H as [H | H]; split; apply in_set_bop_intersect_elim in H; auto. 
           destruct H as [ L _ ]; auto.            
           destruct H as [ L R ]. apply in_set_bop_union_intro; auto.
           destruct H as [ L _ ]; auto.                       
           destruct H as [ L R ]. apply in_set_bop_union_intro; auto.
Qed. 

Lemma A_bs_union_intersect_right_distributive : 
        A_bs_right_distributive (brel_set r) (bop_union r) (bop_intersect r). 
Proof. apply bs_left_distributive_implies_right; auto. 
       apply brel_set_transitive; auto. 
       apply bop_union_congruence; auto. 
       apply bop_union_commutative; auto. 
       apply bop_intersect_commutative; auto. 
       apply A_bs_union_intersect_left_distributive; auto. 
Defined. 


Lemma A_bs_union_intersect_left_absorptive : 
        A_bs_left_absorptive (brel_set r) (bop_union r) (bop_intersect r). 
Proof. intros s t. 
       apply brel_set_intro_prop; auto. split; intros a H. 
          apply in_set_bop_union_intro; auto. 
          apply in_set_bop_union_elim in H; auto. destruct H as [ H | H]; auto. 
             apply in_set_bop_intersect_elim in H; auto. destruct H as [L R]; auto.            
Qed. 

(*
Lemma A_bs_union_intersect_not_left_strictly_absorptive : 
  A_bs_not_left_strictly_absorptive 
    (finite_set S) (brel_set r) (bop_union r) (bop_intersect r). 
Proof.
  exists (nil, nil).
  compute.
  right.
  auto.
Qed.


Lemma A_bs_union_intersect_not_right_strictly_absorptive : 
  A_bs_not_right_strictly_absorptive 
    (finite_set S) (brel_set r) (bop_union r) (bop_intersect r). 
Proof.
  exists (nil, nil).
  compute.
  right.
  auto.
Qed.
*) 
Lemma A_bs_union_intersect_right_absorptive : 
        A_bs_right_absorptive (brel_set r) (bop_union r) (bop_intersect r) . 
Proof. apply bs_left_absorptive_implies_right; auto. 
       apply brel_set_reflexive; auto. 
       apply brel_set_transitive; auto. 
       apply bop_union_congruence; auto. 
       apply bop_intersect_commutative; auto. 
       apply A_bs_union_intersect_left_absorptive; auto. 
Qed. 
(***************)
(* 
Lemma A_bs_union_intersect_not_strictly_right_absorptive : 
  A_bs_not_strictly_right_absorptive (finite_set S) (brel_set r) (bop_union r) (bop_intersect r) .
Proof. exists (nil, nil). right.   compute. reflexivity. Defined. 

Lemma A_bs_intersect_union_not_strictly_right_absorptive : 
  A_bs_not_strictly_right_absorptive (finite_set S) (brel_set r) (bop_intersect r) (bop_union r).
Proof. exists (nil, nil). right.   compute. reflexivity. Defined. 
*)


(***************)

 (* intersect union theorems *)

Lemma A_bs_intersect_union_left_distributive : 
        A_bs_left_distributive (brel_set r) (bop_intersect r) (bop_union r). 
Proof. intros s t u. 
       apply brel_set_intro_prop; auto. split; intros a H.        
          apply in_set_bop_intersect_intro; auto. split; apply in_set_bop_union_intro; auto. 
             apply in_set_bop_union_elim in H; auto. destruct H as [H | H ]. 
                left. assumption. 
                apply in_set_bop_intersect_elim in H; auto. destruct H as [ L R ]. 
                right. assumption. 
             apply in_set_bop_union_elim in H; auto. destruct H as [H | H ]. 
                left. assumption. 
                apply in_set_bop_intersect_elim in H; auto. destruct H as [ L R ]. 
                right. assumption. 
          apply in_set_bop_union_intro; auto. 
          apply in_set_bop_intersect_elim in H; auto. destruct H as [ L R ]. 
          apply in_set_bop_union_elim in L; apply in_set_bop_union_elim in R; auto. 
          destruct L as [L |L]; destruct R as [R | R]. 
             left. assumption. 
             left. assumption. 
             left. assumption. 
             right. apply in_set_bop_intersect_intro; auto. 
Qed. 

Lemma A_bs_intersect_union_right_distributive : 
        A_bs_right_distributive (brel_set r) (bop_intersect r) (bop_union r). 
Proof. apply bs_left_distributive_implies_right; auto. 
       apply brel_set_transitive; auto. 
       apply bop_intersect_congruence; auto. 
       apply bop_intersect_commutative; auto. 
       apply bop_union_commutative; auto. 
       apply A_bs_intersect_union_left_distributive; auto. 
Qed. 

Lemma A_bs_intersect_union_left_absorptive : 
        A_bs_left_absorptive (brel_set r) (bop_intersect r) (bop_union r). 
Proof. intros s t. 
       apply brel_set_intro_prop; auto. split; intros a H. 
          apply in_set_bop_intersect_intro; auto. split; auto. 
             apply in_set_bop_union_intro; auto. 
          apply in_set_bop_intersect_elim in H; auto. destruct H as [ L R ]; auto. 
Qed. 


Lemma A_bs_intersect_union_right_absorptive : 
        A_bs_right_absorptive (brel_set r) (bop_intersect r) (bop_union r). 
Proof. apply bs_left_absorptive_implies_right. 
       apply brel_set_reflexive; auto. 
       apply brel_set_transitive; auto. 
       apply bop_intersect_congruence; auto. 
       apply bop_union_commutative; auto. 
       apply A_bs_intersect_union_left_absorptive; auto. 
Qed. 


Lemma A_bs_union_intersect_id_ann_equal :
  A_bs_exists_id_ann_equal  (brel_set r) (bop_union r) (bop_intersect r).
Proof. exists nil; split.
       apply bop_union_nil_is_id; auto.
       apply bop_intersect_nil_is_ann; auto.
Defined.

Lemma A_bs_intersect_union_id_ann_equal
  (finP : carrier_is_finite S r):
  A_bs_exists_id_ann_equal  (brel_set r) (bop_intersect r) (bop_union r).
Proof. exists ((projT1 finP) tt). split.
       apply bop_intersect_enum_is_id; auto. 
       apply bop_union_enum_is_ann; auto. 
Defined.

Lemma A_bs_intersect_union_exists_id_ann_decide
  (fin_d : carrier_is_finite_decidable S r) :
  A_bs_exists_id_ann_decidable (brel_set r) (bop_intersect r) (bop_union r). 
Proof. destruct fin_d as [finP | nfinP].
       + exact (A_Id_Ann_Equal _ _ _ (A_bs_intersect_union_id_ann_equal finP)). 
       + exact (A_Id_Ann_None _ _ _
                   (bop_intersect_not_exists_id S r refS symS tranS nfinP,
                    bop_union_not_exists_ann S r refS symS tranS nfinP)). 
Defined.  


End Theory.

Section ACAS.

Definition A_bs_union_intersect_id_ann_properties (S : Type) (eqv : A_eqv S) :
               A_bs_id_ann_properties
                  (brel_set (A_eqv_eq S eqv))
                  (bop_union (A_eqv_eq S eqv))
                  (bop_intersect (A_eqv_eq S eqv)) :=
let eqvP   := A_eqv_proofs S eqv in
let eq     := A_eqv_eq S eqv in  
let refS := A_eqv_reflexive _ _ eqvP in
let symS := A_eqv_symmetric _ _ eqvP in
let tranS := A_eqv_transitive _ _ eqvP in
let fin_d := A_eqv_finite_d S eqv in 
{|
  A_id_ann_plus_times_d := A_Id_Ann_Equal _ _ _ (A_bs_union_intersect_id_ann_equal S eq refS symS tranS) 
; A_id_ann_times_plus_d := A_bs_intersect_union_exists_id_ann_decide S eq refS symS tranS fin_d 
|}.


Definition A_bs_intersect_union_id_ann_properties (S : Type) (eqv : A_eqv S) :
               A_bs_id_ann_properties
                 (brel_set (A_eqv_eq S eqv))
                 (bop_intersect (A_eqv_eq S eqv))
                 (bop_union (A_eqv_eq S eqv)) :=
let eqvP   := A_eqv_proofs S eqv in
let eq     := A_eqv_eq S eqv in  
let refS := A_eqv_reflexive _ _ eqvP in
let symS := A_eqv_symmetric _ _ eqvP in
let tranS := A_eqv_transitive _ _ eqvP in
let fin_d := A_eqv_finite_d S eqv in 
{|
  A_id_ann_plus_times_d := A_bs_intersect_union_exists_id_ann_decide S eq refS symS tranS fin_d 
; A_id_ann_times_plus_d := A_Id_Ann_Equal _ _ _ (A_bs_union_intersect_id_ann_equal S eq refS symS tranS) 
|}.


Definition A_bs_union_intersect_properties {S : Type} (eqv : A_eqv S) :=
let eqvP   := A_eqv_proofs S eqv in
let eq     := A_eqv_eq S eqv in  
let refS   := A_eqv_reflexive S eq eqvP in
let symS   := A_eqv_symmetric S eq eqvP in
let trnS   := A_eqv_transitive S eq eqvP in
{|
  A_bs_left_distributive_d  := inl (A_bs_union_intersect_left_distributive S eq refS symS trnS) 
; A_bs_right_distributive_d := inl (A_bs_union_intersect_right_distributive S eq refS symS trnS) 
; A_bs_left_absorptive_d    := inl (A_bs_union_intersect_left_absorptive S eq refS symS trnS)
; A_bs_right_absorptive_d   := inl (A_bs_union_intersect_right_absorptive S eq refS symS trnS)
|}.


Definition A_bs_intersect_union_properties {S : Type} (eqv : A_eqv S) :=
let eqvP   := A_eqv_proofs S eqv in
let eq     := A_eqv_eq S eqv in  
let refS   := A_eqv_reflexive S eq eqvP in
let symS   := A_eqv_symmetric S eq eqvP in
let trnS   := A_eqv_transitive S eq eqvP in
{|
  A_bs_left_distributive_d  := inl (A_bs_intersect_union_left_distributive S eq refS symS trnS) 
; A_bs_right_distributive_d := inl (A_bs_intersect_union_right_distributive S eq refS symS trnS) 
; A_bs_left_absorptive_d    := inl (A_bs_intersect_union_left_absorptive S eq refS symS trnS)
; A_bs_right_absorptive_d   := inl (A_bs_intersect_union_right_absorptive S eq refS symS trnS)
|}.


Definition A_bs_union_intersect {S : Type} (eqv : A_eqv S) : @A_bs (finite_set S) :=
let rS := A_eqv_eq _ eqv in
let s  := A_eqv_witness _ eqv in 
{|
  A_bs_eqv          := A_eqv_set S eqv 
; A_bs_plus         := bop_union rS 
; A_bs_times        := bop_intersect rS  
; A_bs_plus_props   := sg_C_proofs_union eqv
; A_bs_times_props  := sg_proofs_intersect eqv
; A_bs_id_ann_props := A_bs_union_intersect_id_ann_properties S eqv
; A_bs_props        := A_bs_union_intersect_properties eqv
; A_bs_ast          := Ast_union_intersect (A_eqv_ast S eqv)
|}.

Definition A_bs_intersect_union {S : Type} (eqv : A_eqv S) : @A_bs (finite_set S) :=
let rS := A_eqv_eq _ eqv in
let s  := A_eqv_witness _ eqv in 
{|
  A_bs_eqv          := A_eqv_set S eqv 
; A_bs_plus         := bop_intersect rS  
; A_bs_times        := bop_union rS 
; A_bs_plus_props   := sg_C_proofs_intersect eqv
; A_bs_times_props  := sg_proofs_union eqv
; A_bs_id_ann_props := A_bs_intersect_union_id_ann_properties S eqv
; A_bs_props        := A_bs_intersect_union_properties eqv
; A_bs_ast          := Ast_intersect_union (A_eqv_ast S eqv)
|}.



Definition A_bs_union_intersect_with_one_id_ann_properties (S : Type) (c : cas_constant) (eqv : A_eqv S) := 
let eqvP   := A_eqv_proofs S eqv in
let eq     := A_eqv_eq S eqv in  
let refS := A_eqv_reflexive _ _ eqvP in
let symS := A_eqv_symmetric _ _ eqvP in
let tranS := A_eqv_transitive _ _ eqvP in
let ref := brel_set_reflexive _ _ refS symS in
let r := brel_set eq in
let b1 := bop_union eq in
let b2 := bop_intersect eq in 
{|
  A_id_ann_plus_times_d := A_Id_Ann_Equal _ _ _ (A_bs_add_one_exists_id_ann_equal_left _ r c b1 b2 ref
                                                   (A_bs_union_intersect_id_ann_equal _ eq refS symS tranS) )
; A_id_ann_times_plus_d := A_Id_Ann_Equal _ _ _ (A_bs_add_one_exists_id_ann_equal_right _ r c b1 b2 ref)
|}.

Definition A_bs_intersect_union_with_zero_id_ann_properties (S : Type) (c : cas_constant) (eqv : A_eqv S) := 
let eqvP   := A_eqv_proofs S eqv in
let eq     := A_eqv_eq S eqv in  
let refS := A_eqv_reflexive _ _ eqvP in
let symS := A_eqv_symmetric _ _ eqvP in
let tranS := A_eqv_transitive _ _ eqvP in
let ref := brel_set_reflexive _ _ refS symS in
let r := brel_set eq in
let b2 := bop_union eq in
let b1 := bop_intersect eq in 
{|
  A_id_ann_plus_times_d := A_Id_Ann_Equal _ _ _ (A_bs_add_zero_exists_id_ann_equal_left _ r c b1 b2 ref)
; A_id_ann_times_plus_d := A_Id_Ann_Equal _ _ _ (A_bs_add_zero_exists_id_ann_equal_right _ r c b1 b2 ref
                                                   (A_bs_union_intersect_id_ann_equal _ eq refS symS tranS))
                                                   
|}.

Definition A_bs_union_intersect_with_one_properties {S : Type} (c : cas_constant) (eqv : A_eqv S) :=
let eqvP   := A_eqv_proofs S eqv in    
let eq     := A_eqv_eq S eqv in  
A_bs_add_one_properties _
  (brel_set eq) c
  (bop_union eq)
  (bop_intersect eq)
  (eqv_proofs_set S eq eqvP)
  (sg_C_proofs_union eqv) 
  (A_bs_union_intersect_properties eqv).

Definition A_bs_intersect_union_with_zero_properties {S : Type} (c : cas_constant) (eqv : A_eqv S) :=
let eqvP   := A_eqv_proofs S eqv in    
let eq     := A_eqv_eq S eqv in  
A_bs_add_zero_properties _
  (brel_set eq) c
  (bop_intersect eq)
  (bop_union eq)
  (eqv_proofs_set S eq eqvP)
  (A_bs_intersect_union_properties eqv).



Definition A_bs_union_intersect_with_one {S : Type} (c : cas_constant) (eqv : A_eqv S) : @A_bs (with_constant (finite_set S)) :=
let rS := A_eqv_eq _ eqv in
let s  := A_eqv_witness _ eqv in 
{|
  A_bs_eqv          := A_eqv_add_constant _ (A_eqv_set S eqv) c
; A_bs_plus         := bop_add_ann (bop_union rS) c
; A_bs_times        := bop_add_id (bop_intersect rS) c
; A_bs_plus_props   := sg_C_proofs_union_with_ann c eqv
; A_bs_times_props  := sg_proofs_intersect_with_id c eqv
; A_bs_id_ann_props := A_bs_union_intersect_with_one_id_ann_properties S c eqv
; A_bs_props        := A_bs_union_intersect_with_one_properties c eqv
; A_bs_ast          := Ast_bs_add_one (c, Ast_union_intersect (A_eqv_ast S eqv))
|}.


Definition A_bs_intersect_union_with_zero {S : Type} (c : cas_constant) (eqv : A_eqv S) : @A_bs (with_constant (finite_set S)) :=
let rS := A_eqv_eq _ eqv in
let s  := A_eqv_witness _ eqv in 
{|
  A_bs_eqv          := A_eqv_add_constant _ (A_eqv_set S eqv) c
; A_bs_plus         := bop_add_id (bop_intersect rS) c
; A_bs_times        := bop_add_ann (bop_union rS) c
; A_bs_plus_props   := sg_C_proofs_intersect_with_id c eqv
; A_bs_times_props  := sg_proofs_union_with_ann c eqv
; A_bs_id_ann_props := A_bs_intersect_union_with_zero_id_ann_properties S c eqv
; A_bs_props        := A_bs_intersect_union_with_zero_properties c eqv
; A_bs_ast          := Ast_bs_add_zero (c, Ast_intersect_union (A_eqv_ast S eqv))
|}.



End ACAS.

Section AMCAS.

Definition A_bs_union_intersect_below_bs {S : Type} (E : A_eqv S) : @A_below_bs (finite_set S)  :=
    A_classify_bs (A_bs_union_intersect E) . 

Definition A_bs_intersect_union_below_bs {S : Type} (E : A_eqv S) : @A_below_bs (finite_set S)  :=
    A_classify_bs (A_bs_intersect_union E) . 

Definition A_bs_union_intersect_with_one_below_bs {S : Type} (c : cas_constant) (E : A_eqv S) :
  @A_below_bs (with_constant (finite_set S))  :=
    A_classify_bs (A_bs_union_intersect_with_one c E) . 

Definition A_bs_intersect_union_with_zero_below_bs {S : Type} (c : cas_constant) (E : A_eqv S) :
  @A_below_bs (with_constant (finite_set S))  :=
    A_classify_bs (A_bs_intersect_union_with_zero c E) . 

Definition A_mcas_bs_union_intersect {S : Type} (A : @A_mcas_eqv S) :=
match A with
| A_EQV_eqv B    => A_MCAS_bs (A_bs_union_intersect_below_bs B)
| A_EQV_Error sl => A_MCAS_bs_Error sl 
end.

Definition A_mcas_bs_intersect_union {S : Type} (A : @A_mcas_eqv S) :=
match A with
| A_EQV_eqv B    => A_MCAS_bs (A_bs_intersect_union_below_bs B)
| A_EQV_Error sl => A_MCAS_bs_Error sl 
end.

Definition A_mcas_bs_union_intersect_with_one {S : Type} (c : cas_constant) (A : @A_mcas_eqv S) :=
match A with
| A_EQV_eqv B    => A_MCAS_bs (A_bs_union_intersect_with_one_below_bs c B)
| A_EQV_Error sl => A_MCAS_bs_Error sl 
end.

Definition A_mcas_bs_intersect_union_with_zero {S : Type} (c : cas_constant) (A : @A_mcas_eqv S) :=
match A with
| A_EQV_eqv B    => A_MCAS_bs (A_bs_intersect_union_with_zero_below_bs c B)
| A_EQV_Error sl => A_MCAS_bs_Error sl 
end.

End AMCAS.

    
Section CAS.

Definition bs_intersect_union_exists_id_ann_decide {S : Type}
    (fin_d : @check_is_finite S ) : @bs_exists_id_ann_decidable (finite_set S) := 
match fin_d with
| Certify_Is_Finite h => Id_Ann_Equal (h tt)
| _                   => Id_Ann_None
end.                            

Definition bs_union_intersect_id_ann_properties {S : Type} (eqv : @eqv S) :
               @bs_id_ann_properties (finite_set S) := 
let fin_d := eqv_finite_d eqv in 
{|
  id_ann_plus_times_d := Id_Ann_Equal nil 
; id_ann_times_plus_d := bs_intersect_union_exists_id_ann_decide fin_d 
|}.

Definition bs_intersect_union_id_ann_properties {S : Type} (eqv : @eqv S) :
               @bs_id_ann_properties (finite_set S) := 
let fin_d := eqv_finite_d eqv in 
{|
  id_ann_plus_times_d := bs_intersect_union_exists_id_ann_decide fin_d 
; id_ann_times_plus_d := Id_Ann_Equal nil 
|}.


Definition bs_union_intersect_properties {S : Type} (wS : S) :=
{|
  bs_left_distributive_d  := inl (BS_Left_Distributive (wS :: nil))
; bs_right_distributive_d := inl (BS_Right_Distributive(wS :: nil))
; bs_left_absorptive_d    := inl (BS_Left_Absorptive(wS :: nil))
; bs_right_absorptive_d   := inl (BS_Right_Absorptive(wS :: nil))
|}.


Definition bs_intersect_union_properties {S : Type} (wS : S):=
{|
  bs_left_distributive_d  := inl (BS_Left_Distributive(wS :: nil))
; bs_right_distributive_d := inl (BS_Right_Distributive(wS :: nil))
; bs_left_absorptive_d    := inl (BS_Left_Absorptive(wS :: nil))
; bs_right_absorptive_d   := inl (BS_Right_Absorptive(wS :: nil))
|}.


Definition bs_union_intersect {S : Type} (eqv : @eqv S) : @bs (finite_set S) :=
let rS := eqv_eq eqv in
{|
  bs_eqv          := eqv_set eqv 
; bs_plus         := bop_union rS 
; bs_times        := bop_intersect rS  
; bs_plus_props   := sg_C_certs_union eqv
; bs_times_props  := sg_certs_intersect eqv
; bs_id_ann_props := bs_union_intersect_id_ann_properties eqv
; bs_props        := bs_union_intersect_properties (eqv_witness eqv)
; bs_ast          := Ast_union_intersect (eqv_ast eqv)
|}.


Definition bs_intersect_union {S : Type} (eqv : @eqv S) : @bs (finite_set S) :=
let rS := eqv_eq eqv in
{|
  bs_eqv          := eqv_set eqv 
; bs_plus         := bop_intersect rS  
; bs_times        := bop_union rS 
; bs_plus_props   := sg_C_certs_intersect eqv
; bs_times_props  := sg_certs_union eqv
; bs_id_ann_props := bs_intersect_union_id_ann_properties eqv
; bs_props        := bs_intersect_union_properties (eqv_witness eqv)
; bs_ast          := Ast_intersect_union (eqv_ast eqv)
|}.

Definition bs_union_intersect_with_one_id_ann_properties {S : Type} (c : cas_constant) (eqv : @eqv S) :
  @bs_id_ann_properties (with_constant (finite_set S)) := 
{|
  id_ann_plus_times_d := Id_Ann_Equal (inr nil) 
; id_ann_times_plus_d := Id_Ann_Equal (inl c) 
|}.

Definition bs_intersect_union_with_zero_id_ann_properties {S : Type} (c : cas_constant) (eqv : @eqv S) :
  @bs_id_ann_properties (with_constant (finite_set S)) := 
{|
  id_ann_plus_times_d := Id_Ann_Equal (inl c) 
; id_ann_times_plus_d := Id_Ann_Equal (inr nil) 
|}.

Definition bs_union_intersect_with_one_properties {S : Type} (c : cas_constant) (eqv : @eqv S) :=
bs_add_one_properties c
  (sg_C_certs_union eqv) 
  (bs_union_intersect_properties (eqv_witness eqv)).

Definition bs_intersect_union_with_zero_properties {S : Type} (c : cas_constant) (eqv : @eqv S) :=
bs_add_zero_properties c
  (bs_intersect_union_properties (eqv_witness eqv)).


Definition bs_union_intersect_with_one {S : Type} (c : cas_constant)
  (eqv : @eqv S) : @bs (with_constant (finite_set S)) :=
let rS := eqv_eq eqv in
{|
  bs_eqv          := eqv_add_constant (eqv_set eqv) c
; bs_plus         := bop_add_ann (bop_union rS) c
; bs_times        := bop_add_id (bop_intersect rS) c
; bs_plus_props   := sg_C_certs_union_with_ann c eqv
; bs_times_props  := sg_certs_intersect_with_id c eqv
; bs_id_ann_props := bs_union_intersect_with_one_id_ann_properties c eqv
; bs_props        := bs_union_intersect_with_one_properties c eqv
; bs_ast          := Ast_bs_add_one (c, Ast_union_intersect (eqv_ast eqv))
|}.

Definition bs_intersect_union_with_zero {S : Type} (c : cas_constant)
  (eqv : @eqv S) : @bs (with_constant (finite_set S)) :=
let rS := eqv_eq eqv in
{|
  bs_eqv          := eqv_add_constant (eqv_set eqv) c
; bs_plus         := bop_add_id (bop_intersect rS) c
; bs_times        := bop_add_ann (bop_union rS) c
; bs_plus_props   := sg_C_certs_intersect_with_id c eqv
; bs_times_props  := sg_certs_union_with_ann c eqv
; bs_id_ann_props := bs_intersect_union_with_zero_id_ann_properties c eqv
; bs_props        := bs_intersect_union_with_zero_properties c eqv
; bs_ast          := Ast_bs_add_zero (c, Ast_intersect_union (eqv_ast eqv))
|}.

End CAS.

Section MCAS.
Definition bs_union_intersect_below_bs {S : Type} (E : @eqv S) : @below_bs (finite_set S)  :=
    classify_bs (bs_union_intersect E) . 

Definition bs_intersect_union_below_bs {S : Type} (E : @eqv S) : @below_bs (finite_set S)  :=
    classify_bs (bs_intersect_union E) . 

Definition bs_union_intersect_with_one_below_bs {S : Type} (c : cas_constant) (E : @eqv S) :
  @below_bs (with_constant (finite_set S))  :=
    classify_bs (bs_union_intersect_with_one c E) . 

Definition bs_intersect_union_with_zero_below_bs {S : Type} (c : cas_constant) (E : @eqv S) :
  @below_bs (with_constant (finite_set S))  :=
    classify_bs (bs_intersect_union_with_zero c E) . 

Definition mcas_bs_union_intersect {S : Type} (A : @mcas_eqv S) :=
match A with
| EQV_eqv B    => MCAS_bs (bs_union_intersect_below_bs B)
| EQV_Error sl => MCAS_bs_Error sl 
end.

Definition mcas_bs_intersect_union {S : Type} (A : @mcas_eqv S) :=
match A with
| EQV_eqv B    => MCAS_bs (bs_intersect_union_below_bs B)
| EQV_Error sl => MCAS_bs_Error sl 
end.

Definition mcas_bs_union_intersect_with_one {S : Type} (c : cas_constant) (A : @mcas_eqv S) :=
match A with
| EQV_eqv B    => MCAS_bs (bs_union_intersect_with_one_below_bs c B)
| EQV_Error sl => MCAS_bs_Error sl 
end.

Definition mcas_bs_intersect_union_with_zero {S : Type} (c : cas_constant) (A : @mcas_eqv S) :=
match A with
| EQV_eqv B    => MCAS_bs (bs_intersect_union_with_zero_below_bs c B)
| EQV_Error sl => MCAS_bs_Error sl 
end.

End MCAS.


Section Verify.

  Lemma correct_bs_intersect_union_exists_id_ann_decide
    (S : Type) (eq : brel S)
    (refS : brel_reflexive S eq)
    (symS : brel_symmetric S eq)
    (trnS : brel_transitive S eq)
    (fin_d : carrier_is_finite_decidable S eq) : 
    p2c_exists_id_ann _ _ _ _ 
      (A_bs_intersect_union_exists_id_ann_decide S eq refS symS trnS fin_d)
    =
    bs_intersect_union_exists_id_ann_decide (p2c_is_finite_check S eq fin_d). 
  Proof. unfold p2c_exists_id_ann, p2c_is_finite_check,
           A_bs_intersect_union_exists_id_ann_decide,
           bs_intersect_union_exists_id_ann_decide; simpl.
         destruct fin_d as [[h A ]| A]; simpl; reflexivity. 
  Qed.
  
  Lemma correct_bs_union_intersect_id_ann_properties (S : Type) (eqv : A_eqv S) :
    P2C_id_ann _ _ _ _ (A_bs_union_intersect_id_ann_properties _ eqv)
    =
    bs_union_intersect_id_ann_properties (A2C_eqv _ eqv). 
  Proof. unfold A2C_eqv, P2C_id_ann, A_bs_union_intersect_id_ann_properties,
           bs_union_intersect_id_ann_properties; simpl.
         rewrite correct_bs_intersect_union_exists_id_ann_decide.
         reflexivity. 
Qed.

  Lemma correct_bs_intersect_union_id_ann_properties (S : Type) (eqv : A_eqv S) :
    P2C_id_ann _ _ _ _ (A_bs_intersect_union_id_ann_properties _ eqv)
    =
    bs_intersect_union_id_ann_properties (A2C_eqv _ eqv). 
  Proof. unfold A2C_eqv, P2C_id_ann, A_bs_intersect_union_id_ann_properties,
           bs_intersect_union_id_ann_properties; simpl.
         rewrite correct_bs_intersect_union_exists_id_ann_decide.
         reflexivity. 
Qed.

Lemma correct_bs_union_intersect_properties (S : Type) (eqv : A_eqv S) :
  P2C_bs _ ((A_eqv_witness _ eqv) :: nil) _ _ (A_bs_union_intersect_properties eqv)
  = bs_union_intersect_properties (A_eqv_witness _ eqv).
Proof. compute. reflexivity. Qed. 

Lemma correct_bs_intersect_union_properties (S : Type) (eqv : A_eqv S) :
  P2C_bs _ ((A_eqv_witness _ eqv) :: nil) _ _ (A_bs_intersect_union_properties eqv)
  = bs_intersect_union_properties (A_eqv_witness _ eqv).
Proof. compute. reflexivity. Qed. 

Theorem correct_bs_union_intersect (S : Type) (eqv: A_eqv S) : 
    bs_union_intersect (A2C_eqv S eqv)
    =
    A2C_bs (A_bs_union_intersect eqv).
Proof. unfold bs_union_intersect, A_bs_union_intersect, A2C_bs; simpl.
       rewrite correct_eqv_set.
       rewrite correct_sg_C_certs_union.
       rewrite correct_sg_certs_intersect.
       rewrite correct_bs_union_intersect_id_ann_properties. 
       reflexivity.
Qed. 

Theorem correct_bs_intersect_union (S : Type) (eqv: A_eqv S) : 
    bs_intersect_union (A2C_eqv S eqv)
    =
    A2C_bs (A_bs_intersect_union eqv).
Proof. unfold bs_intersect_union, A_bs_intersect_union, A2C_bs; simpl.
       rewrite correct_eqv_set.
       rewrite correct_sg_C_certs_intersect.
       rewrite correct_sg_certs_union. 
       rewrite correct_bs_intersect_union_id_ann_properties. 
       reflexivity.
Qed. 

Lemma correct_bs_union_intersect_with_one_id_ann_properties (S : Type) (c : cas_constant) (eqv : A_eqv S) :
  P2C_id_ann _ _ _ _ (A_bs_union_intersect_with_one_id_ann_properties S c eqv)
  = 
    bs_union_intersect_with_one_id_ann_properties c (A2C_eqv S eqv).
Proof. compute. reflexivity. Qed. 

Lemma correct_bs_intersect_union_with_zero_id_ann_properties (S : Type) (c : cas_constant) (eqv : A_eqv S) :
  P2C_id_ann _ _ _ _ (A_bs_intersect_union_with_zero_id_ann_properties S c eqv)
  = 
  bs_intersect_union_with_zero_id_ann_properties c (A2C_eqv S eqv).
Proof. compute. reflexivity. Qed. 

Lemma correct_bs_union_intersect_with_one_properties (S : Type) (c : cas_constant) (eqv : A_eqv S) :
  P2C_bs _ (inl c) _ _ (A_bs_union_intersect_with_one_properties c eqv)
  =
  bs_union_intersect_with_one_properties c (A2C_eqv _ eqv).
Proof. compute.        reflexivity. Qed. 


Lemma correct_bs_intersect_union_with_zero_properties (S : Type) (c : cas_constant) (eqv : A_eqv S) :
  P2C_bs _ (inl c) _ _ (A_bs_intersect_union_with_zero_properties c eqv)
  =
  bs_intersect_union_with_zero_properties c (A2C_eqv _ eqv).
Proof. compute. reflexivity. Qed. 

Theorem correct_bs_union_intersect_with_one (S : Type) (c : cas_constant) (eqv: A_eqv S) : 
    bs_union_intersect_with_one c (A2C_eqv S eqv)
    =
    A2C_bs (A_bs_union_intersect_with_one c eqv).
Proof. unfold bs_union_intersect_with_one, A_bs_union_intersect_with_one, A2C_bs; simpl.
       rewrite correct_eqv_set.
       rewrite correct_eqv_add_constant.
       rewrite correct_sg_C_certs_union_with_ann.
       rewrite correct_sg_certs_intersect_with_id.
       rewrite correct_bs_union_intersect_with_one_properties.        
       rewrite correct_bs_union_intersect_with_one_id_ann_properties. 
       reflexivity.
Qed. 


Theorem correct_bs_intersect_union_with_zero (S : Type) (c : cas_constant) (eqv: A_eqv S) : 
    bs_intersect_union_with_zero c (A2C_eqv S eqv)
    =
    A2C_bs (A_bs_intersect_union_with_zero c eqv).
Proof. unfold bs_intersect_union_with_zero, A_bs_intersect_union_with_zero, A2C_bs; simpl.
       rewrite correct_eqv_set.
       rewrite correct_eqv_add_constant.
       rewrite correct_sg_C_certs_intersect_with_id. 
       rewrite correct_sg_certs_union_with_ann.
       rewrite correct_bs_intersect_union_with_zero_properties.        
       rewrite correct_bs_intersect_union_with_zero_id_ann_properties. 
       reflexivity.
Qed. 

(***************) 

Theorem correct_bs_union_intersect_below_bs (S : Type )(A : A_eqv S) : 
    bs_union_intersect_below_bs (A2C_eqv S A)
    =
    A2C_below_bs (A_bs_union_intersect_below_bs A).
Proof. unfold bs_union_intersect_below_bs, A_bs_union_intersect_below_bs.
       rewrite correct_bs_union_intersect.
       rewrite correct_classify_bs. 
       reflexivity.
Qed.


Theorem correct_bs_intersect_union_below_bs (S : Type )(A : A_eqv S) : 
    bs_intersect_union_below_bs (A2C_eqv S A)
    =
    A2C_below_bs (A_bs_intersect_union_below_bs A).
Proof. unfold bs_intersect_union_below_bs, A_bs_intersect_union_below_bs.
       rewrite correct_bs_intersect_union.
       rewrite correct_classify_bs. 
       reflexivity.
Qed.

Theorem correct_mcas_bs_union_intersect (S : Type) (eqvS : @A_mcas_eqv S): 
         mcas_bs_union_intersect (A2C_mcas_eqv S eqvS)  
         = 
         A2C_bs_mcas (A_mcas_bs_union_intersect eqvS). 
Proof. unfold mcas_bs_union_intersect, A_mcas_bs_union_intersect.
       destruct eqvS; simpl.
       + reflexivity.
       + rewrite correct_bs_union_intersect_below_bs.
         reflexivity. 
Qed.  


Theorem correct_mcas_bs_intersect_union (S : Type) (eqvS : @A_mcas_eqv S): 
         mcas_bs_intersect_union (A2C_mcas_eqv S eqvS)  
         = 
         A2C_bs_mcas (A_mcas_bs_intersect_union eqvS). 
Proof. unfold mcas_bs_intersect_union, A_mcas_bs_intersect_union.
       destruct eqvS; simpl.
       + reflexivity.
       + rewrite correct_bs_intersect_union_below_bs.
         reflexivity. 
Qed.  



Theorem correct_bs_union_intersect_with_one_below_bs (S : Type ) (c : cas_constant) (A : A_eqv S) : 
    bs_union_intersect_with_one_below_bs c (A2C_eqv S A)
    =
    A2C_below_bs (A_bs_union_intersect_with_one_below_bs c A).
Proof. unfold bs_union_intersect_with_one_below_bs, A_bs_union_intersect_with_one_below_bs.
       rewrite correct_bs_union_intersect_with_one.
       rewrite correct_classify_bs. 
       reflexivity.
Qed.


Theorem correct_bs_intersect_union_with_zero_below_bs (S : Type ) (c : cas_constant) (A : A_eqv S) : 
    bs_intersect_union_with_zero_below_bs c (A2C_eqv S A)
    =
    A2C_below_bs (A_bs_intersect_union_with_zero_below_bs c A).
Proof. unfold bs_intersect_union_with_zero_below_bs,
         A_bs_intersect_union_with_zero_below_bs.
       rewrite correct_bs_intersect_union_with_zero.
       rewrite correct_classify_bs. 
       reflexivity.
Qed.


Theorem correct_mcas_bs_union_intersect_with_one (S : Type) (c : cas_constant) (eqvS : @A_mcas_eqv S): 
         mcas_bs_union_intersect_with_one c (A2C_mcas_eqv S eqvS)  
         = 
         A2C_bs_mcas (A_mcas_bs_union_intersect_with_one c eqvS). 
Proof. unfold mcas_bs_union_intersect_with_one, A_mcas_bs_union_intersect_with_one. 
       destruct eqvS; simpl.
       + reflexivity.
       + rewrite correct_bs_union_intersect_with_one_below_bs.
         reflexivity. 
Qed.  


Theorem correct_mcas_bs_intersect_union_with_zero (S : Type) (c : cas_constant) (eqvS : @A_mcas_eqv S): 
         mcas_bs_intersect_union_with_zero c (A2C_mcas_eqv S eqvS)  
         = 
         A2C_bs_mcas (A_mcas_bs_intersect_union_with_zero c eqvS). 
Proof. unfold mcas_bs_intersect_union_with_zero, A_mcas_bs_intersect_union_with_zero. 
       destruct eqvS; simpl.
       + reflexivity.
       + rewrite correct_bs_intersect_union_with_zero_below_bs.
         reflexivity. 
Qed.  
 
End Verify.   

