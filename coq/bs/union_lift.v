Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.

Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.

Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.eqv.theory. 
Require Import CAS.coq.eqv.set.

Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures.
Require Import CAS.coq.sg.theory. 
Require Import CAS.coq.sg.union.
Require Import CAS.coq.sg.lift.
Require Import CAS.coq.sg.cast_up.

Require Import CAS.coq.bs.properties.
Require Import CAS.coq.bs.structures.
Require Import CAS.coq.bs.theory.
Require Import CAS.coq.bs.cast. 
Require Import CAS.coq.bs.classify. 
Section Theory.

  Variable S: Type.
  Variable r : brel S.
  Variable wS  : S. 
  Variable f : S -> S.
  Variable ntS : brel_not_trivial S r f. 
  Variable bS : binary_op S.
  
  Variable refS : brel_reflexive S r.
  Variable symS : brel_symmetric S r.
  Variable tranS : brel_transitive S r.
  
  Variable bcong : bop_congruence S r bS. 
  Variable assS : bop_associative S r bS. 


Lemma A_bs_union_lift_left_distributive : 
        A_bs_left_distributive (brel_set r) (bop_union r) (bop_lift r bS). 
Proof. intros X Y Z. 
       apply brel_set_intro_prop; auto.
       split; intros a H.        
          apply in_set_bop_union_intro; auto. 
          apply in_set_bop_lift_elim in H;
          auto. destruct H as [ x [ y [[ P1 P2 ] P3 ] ] ]. 
          apply in_set_bop_union_elim in P2; auto.
          destruct P2 as [R | R].
             left. apply (in_set_bop_lift_intro_v2 S r bS refS tranS symS bcong X Y a x y); auto. 
             right. apply (in_set_bop_lift_intro_v2 S r bS refS tranS symS bcong X Z a x y); auto. 
       
       apply in_set_bop_union_elim in H; auto. destruct H as [H | H].
       apply in_set_bop_lift_elim in H; auto. destruct H as [ x [ y [[ P1 P2 ] P3 ] ] ]. 
       apply (in_set_bop_lift_intro_v2 S r bS refS tranS symS bcong X (bop_union r Y Z) a x y); auto.
       apply in_set_bop_union_intro; auto.
       apply in_set_bop_lift_elim in H; auto. destruct H as [ x [ y [[ P1 P2 ] P3 ] ] ]. 
       apply (in_set_bop_lift_intro_v2 S r bS refS tranS symS bcong X (bop_union r Y Z) a x y); auto.
       apply in_set_bop_union_intro; auto. 
Qed. 

(* just a test *) 
Lemma A_bs_union_lift_left_distributive_dual : 
        A_bs_left_distributive (brel_set r)  (bop_lift r bS) (bop_union r). 
Proof. intros X Y Z. 
       apply brel_set_intro_prop; auto.
       split; intros a H.
          apply in_set_bop_union_elim in H.
          destruct H as [H | H].
          + admit. (* need idempotence *) 
          + admit. (* need (X U Y) [^] (Z [^] W) = (X [^] Z) U (X [^] W) U (Y [^] Z) U (X [^] W) *) 
Admitted. 

(* just a test *) 
Lemma A_bs_union_lift_not_left_distributive_dual :
        bop_not_idempotent S r bS -> 
        A_bs_not_left_distributive (brel_set r)  (bop_lift r bS) (bop_union r). 
Proof. intros [i nidem]. exists (i :: nil, (nil, nil)).  compute.
       rewrite nidem. assert (H : r i (bS i i) = false). admit.  rewrite H. reflexivity. 
Admitted. 

        
Lemma A_bs_union_lift_right_distributive : 
        A_bs_right_distributive (brel_set r) (bop_union r) (bop_lift r bS). 
Proof. intros X Y Z. 
       apply brel_set_intro_prop; auto.
       split; intros a H.        
          apply in_set_bop_union_intro; auto. 
          apply in_set_bop_lift_elim in H;
          auto. destruct H as [ x [ y [[ P1 P2 ] P3 ] ] ]. 
          apply in_set_bop_union_elim in P1; auto.
          destruct P1 as [R | R].
             left. apply (in_set_bop_lift_intro_v2 S r bS refS tranS symS bcong Y X a x y); auto. 
             right. apply (in_set_bop_lift_intro_v2 S r bS refS tranS symS bcong Z X a x y); auto. 
       
       apply in_set_bop_union_elim in H; auto. destruct H as [H | H].
       apply in_set_bop_lift_elim in H; auto. destruct H as [ x [ y [[ P1 P2 ] P3 ] ] ]. 
       apply (in_set_bop_lift_intro_v2 S r bS refS tranS symS bcong (bop_union r Y Z) X a x y); auto.
       apply in_set_bop_union_intro; auto.
       apply in_set_bop_lift_elim in H; auto. destruct H as [ x [ y [[ P1 P2 ] P3 ] ] ]. 
       apply (in_set_bop_lift_intro_v2 S r bS refS tranS symS bcong (bop_union r Y Z) X a x y); auto.
       apply in_set_bop_union_intro; auto. 
Qed. 



Lemma A_bs_union_lift_left_absorptive : 
        bop_is_left S r bS -> A_bs_left_absorptive (brel_set r) (bop_union r) (bop_lift r bS). 
Proof. intros IL X Y. 
       apply brel_set_intro_prop; auto. split; intros a H. 
          apply in_set_bop_union_intro; auto. 
          apply in_set_bop_union_elim in H; auto. destruct H as [ H | H]; auto. 
             apply in_set_bop_lift_elim in H; auto. destruct H as [x [y [[H1 H2] H3]]].
             assert (H4 := IL x y).
             assert (H5 := tranS _ _ _ H3 H4).
             apply symS in H5. assert (H6 := in_set_right_congruence _ _ symS tranS _ _ _ H5 H1). exact H6. 
Qed. 

(* strict absorption 
Lemma bops_union_lift_not_left_strictly_absorptive : 
        bops_not_left_strictly_absorptive (finite_set S) 
        (brel_set r) (bop_union r) (bop_lift r bS). 
Proof. 
      exists (nil, nil).
      compute.
      right; auto.
Qed.


Lemma bops_union_lift_not_right_strictly_absorptive : 
        bops_not_right_strictly_absorptive (finite_set S) 
        (brel_set r) (bop_union r) (bop_lift r bS). 
Proof. 
      exists (nil, nil).
      compute.
      right; auto.
Qed.
*) 



(* just a test *) 
Lemma A_bs_union_lift_left_absorptive_dual : 
        bop_is_left S r bS -> A_bs_left_absorptive (brel_set r) (bop_lift r bS) (bop_union r). 
Proof. intros IL X Y. 
       (* hmm, should work as well *) 
Admitted.

Lemma A_bs_union_lift_not_left_absorptive : 
        bop_not_is_left S r bS -> A_bs_not_left_absorptive (brel_set r) (bop_union r) (bop_lift r bS). 
Proof. intros [[s t] P]. unfold A_bs_not_left_absorptive. 
       exists (s :: nil, t :: nil).
       case_eq(brel_set r (s :: nil) (bop_union r (s :: nil) (bop_lift r bS (s :: nil) (t :: nil)))); intro J1; auto.
          apply brel_set_elim in J1. destruct J1 as [L R].
          assert (K1 := brel_subset_elim _ _ symS tranS _ _ R (bS s t)).
          assert (K2 : in_set r (bop_union r (s :: nil) (bop_lift r bS (s :: nil) (t :: nil))) (bS s t) = true).
             apply in_set_bop_union_intro; auto.
             right. apply in_set_bop_lift_intro; auto.
             apply in_set_singleton_intro; auto.
             apply in_set_singleton_intro; auto.              
          assert (K3 := K1 K2).
          apply in_set_singleton_elim in K3; auto.
          apply symS in K3. rewrite K3 in P. discriminate P. 
Defined.

Definition A_bs_union_lift_left_absorptive_decide
  (ld : bop_is_left_decidable S r bS) : 
    A_bs_left_absorptive_decidable (brel_set r) (bop_union r) (bop_lift r bS)
  := match ld with
     | inl lla  => inl (A_bs_union_lift_left_absorptive lla)
     | inr nlla => inr (A_bs_union_lift_not_left_absorptive nlla)
     end.                                                          


Lemma A_bs_union_lift_right_absorptive : 
  bop_is_right S r bS ->
  A_bs_right_absorptive (brel_set r) (bop_union r) (bop_lift r bS). 
Proof. intros IR X Y. 
       apply brel_set_intro_prop; auto. split; intros a H. 
          apply in_set_bop_union_intro; auto. 
          apply in_set_bop_union_elim in H; auto. destruct H as [ H | H]; auto. 
             apply in_set_bop_lift_elim in H; auto. destruct H as [x [y [[H1 H2] H3]]].
             assert (H4 := IR x y).
             assert (H5 := tranS _ _ _ H3 H4).
             apply symS in H5. assert (H6 := in_set_right_congruence _ _ symS tranS _ _ _ H5 H2). exact H6. 
Qed. 

Lemma A_bs_union_lift_not_right_absorptive : 
  bop_not_is_right S r bS ->
  A_bs_not_right_absorptive (brel_set r) (bop_union r) (bop_lift r bS). 
Proof. intros [[s t] P]. 
       exists (t :: nil, s :: nil).
       case_eq(brel_set r (t :: nil) (bop_union r (t :: nil) (bop_lift r bS (s :: nil) (t :: nil)))); intro J1; auto.
          apply brel_set_elim in J1. destruct J1 as [L R].
          assert (K1 := brel_subset_elim _ _ symS tranS _ _ R (bS s t)).
          assert (K2 : in_set r (bop_union r (t :: nil) (bop_lift r bS (s :: nil) (t :: nil))) (bS s t) = true).
             apply in_set_bop_union_intro; auto.
             right. apply in_set_bop_lift_intro; auto.
             apply in_set_singleton_intro; auto.
             apply in_set_singleton_intro; auto.              
          assert (K3 := K1 K2).
          apply in_set_singleton_elim in K3; auto.
          apply symS in K3. rewrite K3 in P. discriminate P. 
Defined. 

Definition A_bs_union_lift_right_absorptive_decide
  (rd : bop_is_right_decidable S r bS) : 
    A_bs_right_absorptive_decidable (brel_set r) (bop_union r) (bop_lift r bS)
  := match rd with
     | inl lra  => inl (A_bs_union_lift_right_absorptive lra)
     | inr nlra => inr (A_bs_union_lift_not_right_absorptive nlra)
     end.                                                          

Lemma A_bs_union_lift_exists_id_ann_equal :
  A_bs_exists_id_ann_equal (brel_set r) (bop_union r) (bop_lift r bS).
Proof. exists nil; split. 
       apply bop_union_nil_is_id; auto. 
       apply bop_lift_nil_is_ann; auto.       
Defined.

Lemma A_bs_lift_union_id_equals_ann_decide 
      (id_d : bop_exists_id_decidable S r bS)
      (fin_d : carrier_is_finite_decidable S r):
  A_bs_exists_id_ann_decidable (brel_set r) (bop_lift r bS) (bop_union r).
Proof. destruct id_d as [idP | nidP]; destruct fin_d as [finP | nfinP].
       + assert (A : A_bs_exists_id_ann_not_equal (brel_set r) (bop_lift r bS) (bop_union r)).
            assert (ann  := bop_union_enum_is_ann S r refS symS tranS finP). 
            destruct idP as [id P]. destruct finP as [h Q]. simpl in ann. 
            exists (id :: nil, h tt). split. split. 
            apply bop_lift_is_id; auto. 
            exact ann. 
            case_eq(brel_set r (id :: nil) (h tt)); intro F; auto.
            apply brel_set_elim_prop in F; auto.  destruct F as [F1 F2]. 
            assert (G := F2 (f id) (Q (f id))).
            compute in G.
            destruct (ntS id) as [K J]. rewrite J in G. 
            discriminate G. 
         exact (A_Id_Ann_Not_Equal _ _ _ A). 
       + exact (A_Id_Ann_Id_None _ _ _ 
                  (bop_lift_exists_id S r bS refS tranS symS bcong idP, 
                   bop_union_not_exists_ann S r refS symS tranS nfinP)).               
       + exact (A_Id_Ann_None_Ann _ _ _ 
                  (bop_lift_not_exists_id S r bS refS tranS symS wS nidP, 
                   bop_union_exists_ann S r refS symS tranS finP)).               
       + exact (A_Id_Ann_None _ _ _ 
                  (bop_lift_not_exists_id S r bS refS tranS symS wS nidP, 
                   bop_union_not_exists_ann S r refS symS tranS nfinP)).               
Defined.  

End Theory. 

Section ACAS.

Section Proofs.   

Variables (S : Type)
          (eqvS : A_eqv S)
          (bS : binary_op S)
          (sgS : sg_proofs S (A_eqv_eq _ eqvS) bS).

Definition A_bs_union_lift_id_ann_properties 
      (id_d : bop_exists_id_decidable S (A_eqv_eq _ eqvS) bS)
      (fin_d : carrier_is_finite_decidable S (A_eqv_eq _ eqvS)) :
  A_bs_id_ann_properties
            (brel_set (A_eqv_eq _ eqvS))
            (bop_union (A_eqv_eq _ eqvS))
            (bop_lift (A_eqv_eq _ eqvS) bS) :=
let eq      := A_eqv_eq _ eqvS in
let f       := A_eqv_new _ eqvS in
let wS      := A_eqv_witness _ eqvS in
let ntS     := A_eqv_not_trivial _ eqvS in  
let eqvP    := A_eqv_proofs _ eqvS in  
let refS    := A_eqv_reflexive _ _ eqvP in
let symS    := A_eqv_symmetric _ _ eqvP in
let trnS    := A_eqv_transitive _ _ eqvP in
let bcong   := A_sg_congruence _ _ _ sgS in 
{|
  A_id_ann_plus_times_d := A_Id_Ann_Equal _ _ _ (A_bs_union_lift_exists_id_ann_equal S eq bS refS symS trnS)
; A_id_ann_times_plus_d := A_bs_lift_union_id_equals_ann_decide S eq wS f ntS bS refS symS trnS bcong id_d fin_d 
|}. 

Definition A_bs_union_lift_properties : 
  A_bs_properties
    (brel_set (A_eqv_eq _ eqvS))
    (bop_union (A_eqv_eq _ eqvS))
    (bop_lift (A_eqv_eq _ eqvS) bS) :=
let eqvP := A_eqv_proofs _ eqvS in
let rS   := A_eqv_eq _ eqvS in  
let refS := A_eqv_reflexive S rS eqvP  in
let symS := A_eqv_symmetric S rS eqvP  in
let trnS := A_eqv_transitive S rS eqvP in
let cnbS := A_sg_congruence S rS bS sgS in
let ilD  := A_sg_is_left_d S rS bS sgS in  
let irD  := A_sg_is_right_d S rS bS sgS in  
{|
  A_bs_left_distributive_d  := inl (A_bs_union_lift_left_distributive S rS bS refS symS trnS cnbS)
; A_bs_right_distributive_d := inl (A_bs_union_lift_right_distributive S rS bS refS symS trnS cnbS)
; A_bs_left_absorptive_d    := A_bs_union_lift_left_absorptive_decide S rS bS refS symS trnS cnbS ilD 
; A_bs_right_absorptive_d   := A_bs_union_lift_right_absorptive_decide S rS bS refS symS trnS cnbS irD 
|}.


End Proofs.   

Section Combinators.


Definition A_bs_union_lift {S : Type} (sgS : A_sg S) : @A_bs (finite_set S) := 
let eqvS  := A_sg_eqv S sgS in
let rS    := A_eqv_eq S eqvS in   
let bS    := A_sg_bop S sgS in
let eqvP := A_eqv_proofs S eqvS in
let s     := A_eqv_witness S eqvS in
let f     := A_eqv_new S eqvS in
let Pf    := A_eqv_not_trivial S eqvS in 
{| 
     A_bs_eqv           := A_eqv_set S eqvS
   ; A_bs_plus          := bop_union rS
   ; A_bs_times         := bop_lift rS bS
   ; A_bs_id_ann_props := A_bs_union_lift_id_ann_properties S eqvS bS (A_sg_proofs S sgS) (A_sg_exists_id_d S sgS) (A_eqv_finite_d S eqvS)
   ; A_bs_plus_props   := sg_C_proofs_union eqvS
   ; A_bs_times_props  := sg_lift_proofs S rS bS eqvP s f Pf (A_eqv_exactly_two_d _ eqvS) (A_sg_proofs S sgS)
   ; A_bs_props        := A_bs_union_lift_properties S eqvS bS (A_sg_proofs S sgS)
   ; A_bs_ast           := Ast_bs_union_lift (A_sg_ast S sgS)
|}.

End Combinators.   

End ACAS.

Section AMCAS.


  Definition A_bs_union_lift_below_bs {S : Type} (A : @A_below_sg S) : @A_below_bs (finite_set S) :=
            A_classify_bs (A_bs_union_lift (A_cast_up_sg A)). 

  Definition A_mcas_bs_union_lift {S : Type} (A : @A_sg_mcas S) : @A_bs_mcas (finite_set S) :=
    match A with
    | A_MCAS_sg B       => A_MCAS_bs (A_bs_union_lift_below_bs B)  
    | A_MCAS_sg_Error sl => A_MCAS_bs_Error sl
    end.

End AMCAS.




Section CAS.


Section Checks.   

Definition bs_union_lift_left_absorptive_decide {S : Type} (wS : S) 
    (ilD : @check_is_left S) : @bs_left_absorptive_decidable (finite_set S) :=
match ilD with
| Certify_Is_Left              => inl (BS_Left_Absorptive (wS::nil)) 
| Certify_Not_Is_Left (s1, s2) => inr (BS_Not_Left_Absorptive ((s1 :: nil), (s2 :: nil)))
end. 

Definition bs_union_lift_right_absorptive_decide {S : Type} (wS : S) 
  (ilD : @check_is_right S) : @bs_right_absorptive_decidable (finite_set S) :=
match ilD with
| Certify_Is_Right              => inl (BS_Right_Absorptive (wS::nil)) 
| Certify_Not_Is_Right (s1, s2) => inr (BS_Not_Right_Absorptive ((s2 :: nil), (s1 :: nil)))
end. 



End Checks. 


Section Proofs.

Definition bs_union_lift_properties {S : Type} (wS : S)
    (sgS : @sg_certificates S) : @bs_properties (finite_set S) := 
let ilD  := sg_is_left_d sgS in  
let irD  := sg_is_right_d sgS in  
{|
  bs_left_distributive_d  := inl (BS_Left_Distributive (wS :: nil)) 
; bs_right_distributive_d := inl (BS_Right_Distributive (wS :: nil)) 
; bs_left_absorptive_d    := bs_union_lift_left_absorptive_decide wS ilD 
; bs_right_absorptive_d   := bs_union_lift_right_absorptive_decide wS irD 
|}.

Definition bs_lift_union_exists_id_ann_decide {S : Type} 
      (id_d  : @check_exists_id S)
      (fin_d : @check_is_finite S): @bs_exists_id_ann_decidable (finite_set S) := 
match id_d with
| Certify_Exists_Id id =>
  match fin_d with
  | Certify_Is_Finite h  => Id_Ann_Not_Equal (id :: nil, h tt)
  | _                    => Id_Ann_Id_None (id :: nil) 
  end 
| _ =>
  match fin_d with
  | Certify_Is_Finite h  => Id_Ann_None_Ann (h tt)    
  | _                    => Id_Ann_None
  end 
end .


Definition bs_union_lift_id_ann_properties {S : Type} 
      (id_d : @check_exists_id S)
      (fin_d : @check_is_finite S) :
  @bs_id_ann_properties (finite_set S) := 
{|
  id_ann_plus_times_d := Id_Ann_Equal nil 
; id_ann_times_plus_d := bs_lift_union_exists_id_ann_decide id_d fin_d 
|}. 

End Proofs.   

Section Combinators.

Definition bs_union_lift {S : Type} (sgS : @sg S) : @bs (finite_set S) := 
let eqvS  := sg_eqv sgS in
let rS    := eqv_eq eqvS in   
let bS    := sg_bop sgS in
let s     := eqv_witness eqvS in
let f     := eqv_new eqvS in
{| 
     bs_eqv           := eqv_set eqvS
   ; bs_plus          := bop_union rS
   ; bs_times         := bop_lift rS bS
   ; bs_id_ann_props  := bs_union_lift_id_ann_properties (sg_exists_id_d sgS) (eqv_finite_d eqvS)
   ; bs_plus_props    := sg_C_certs_union eqvS
   ; bs_times_props  := sg_lift_certs S rS s f  (eqv_exactly_two_d eqvS) bS (sg_certs sgS)
   ; bs_props        := bs_union_lift_properties s (sg_certs sgS)
   ; bs_ast          := Ast_bs_union_lift (sg_ast sgS)
|}.

End Combinators.   

End CAS.

Section AMCAS.


  Definition bs_union_lift_below_bs {S : Type} (A : @below_sg S) : @below_bs (finite_set S) :=
            classify_bs (bs_union_lift (cast_up_sg A)). 

  Definition mcas_bs_union_lift {S : Type} (A : @sg_mcas S) : @bs_mcas (finite_set S) :=
    match A with
    | MCAS_sg B       => MCAS_bs (bs_union_lift_below_bs B)  
    | MCAS_sg_Error sl => MCAS_bs_Error sl
    end.

End AMCAS.


Section Verify.


Lemma correct_bs_union_lift_left_absorptive_decide
  (S : Type)
  (eq : brel S)
  (wS : S) 
  (refS : brel_reflexive S eq)
  (symS : brel_symmetric S eq)
  (trnS : brel_transitive S eq)     
  (bS : binary_op S)
  (cong : bop_congruence S eq bS)
  (il_d : bop_is_left_decidable S eq bS) : 
  p2c_bs_left_absorptive_decidable (brel_set eq) (wS :: nil) (bop_union eq) (bop_lift eq bS)
    (A_bs_union_lift_left_absorptive_decide S eq bS refS symS trnS cong il_d)
  =                                                                               
  bs_union_lift_left_absorptive_decide wS (p2c_is_left_check S eq bS il_d).
Proof. destruct il_d as [IL | [ [s1 s2] NIL ]]; simpl; reflexivity. Qed. 

Lemma correct_bs_union_lift_right_absorptive_decide
  (S : Type)
  (eq : brel S)
  (wS : S) 
  (refS : brel_reflexive S eq)
  (symS : brel_symmetric S eq)
  (trnS : brel_transitive S eq)     
  (bS : binary_op S)
  (cong : bop_congruence S eq bS)
  (ir_d : bop_is_right_decidable S eq bS):
  p2c_bs_right_absorptive_decidable (brel_set eq) (wS :: nil) (bop_union eq) (bop_lift eq bS)
    (A_bs_union_lift_right_absorptive_decide S eq bS refS symS trnS cong ir_d)
  =
  bs_union_lift_right_absorptive_decide wS (p2c_is_right_check S eq bS ir_d).
Proof. destruct ir_d as [IR | [ [s1 s2] NIR ]]; simpl; reflexivity. Qed. 


Lemma correct_bs_union_lift_properties
  (S : Type)
  (bS : binary_op S)
  (eqvS : A_eqv S)
  (sgP : sg_proofs S (A_eqv_eq S eqvS) bS) : 
  P2C_bs _ ((A_eqv_witness _ eqvS) :: nil) _ _ (A_bs_union_lift_properties S eqvS bS sgP)
  = 
  bs_union_lift_properties (A_eqv_witness _ eqvS) (P2C_sg (A_eqv_eq S eqvS) bS sgP).
Proof. destruct sgP. unfold bs_union_lift_properties, bs_union_lift_properties, P2C_sg, P2C_bs; simpl.
       destruct A_sg_is_left_d as [L | [[a b] NL]]; destruct A_sg_is_right_d as [R | [[c d] NR]]; simpl; reflexivity. 
Qed.

Lemma correct_bs_union_lift_id_ann_properties
      (S : Type)
      (eqvS : A_eqv S)
      (bS : binary_op S)
      (id_d : bop_exists_id_decidable S (A_eqv_eq S eqvS) bS)
      (sgP : sg_proofs S (A_eqv_eq S eqvS) bS) :
      bs_union_lift_id_ann_properties (p2c_exists_id_check _ _ _ id_d) (p2c_is_finite_check _ _ (A_eqv_finite_d _ eqvS)) 
      = 
      P2C_id_ann (finite_set S) (brel_set (A_eqv_eq _ eqvS)) (bop_union (A_eqv_eq _ eqvS)) (bop_lift (A_eqv_eq _ eqvS) bS)
                 (A_bs_union_lift_id_ann_properties S eqvS bS sgP id_d (A_eqv_finite_d _ eqvS)).
Proof.   unfold A_bs_union_lift_id_ann_properties, bs_union_lift_id_ann_properties,
           P2C_id_ann, p2c_is_finite_check, p2c_exists_id_check; simpl.
         destruct id_d as [[id idP] | nidP]; destruct (A_eqv_finite_d _ eqvS) as [[h finP] | nfinP]; simpl; 
         try reflexivity. 
Qed.

Theorem correct_bs_union_lift (S : Type) (sgS: A_sg S):  
   bs_union_lift (A2C_sg sgS)
   =
   A2C_bs (A_bs_union_lift sgS). 
Proof. unfold bs_union_lift, bs_union_lift, A2C_bs, A2C_sg. destruct sgS. simpl.
       rewrite correct_eqv_set.              
       rewrite correct_sg_lift_certs.
       rewrite <- correct_bs_union_lift_properties.              
       rewrite <- correct_bs_union_lift_id_ann_properties. 
       rewrite correct_sg_C_certs_union. 
       reflexivity.
Qed.


Theorem correct_bs_union_lift_below_bs  (S : Type) (A : @A_below_sg S) : 
 bs_union_lift_below_bs(A2C_below_sg A)
  =
 A2C_below_bs (A_bs_union_lift_below_bs A).
Proof. unfold A_bs_union_lift_below_bs, bs_union_lift_below_bs.
       rewrite cast_up_sg_A2C_commute. 
       rewrite correct_bs_union_lift. 
       rewrite correct_classify_bs. 
       reflexivity.
Qed.

Theorem correct_mcas_bs_union_lift (S : Type) (sgS : @A_sg_mcas S) : 
         mcas_bs_union_lift (A2C_sg_mcas sgS) 
         = 
         A2C_bs_mcas (A_mcas_bs_union_lift sgS).
Proof. unfold A_mcas_bs_union_lift, mcas_bs_union_lift. 
       destruct sgS; simpl; try reflexivity.
       rewrite correct_bs_union_lift_below_bs.
       reflexivity. 
Qed. 



End Verify. 










