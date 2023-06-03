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
Require Import CAS.coq.sg.cast_up.
Require Import CAS.coq.sg.theory. 
Require Import CAS.coq.sg.union.

Require Import CAS.coq.ltr.properties.
Require Import CAS.coq.ltr.structures.
Require Import CAS.coq.ltr.lift.
Require Import CAS.coq.ltr.cast.
Require Import CAS.coq.ltr.classify.

Require Import CAS.coq.sg_ltr.properties.
Require Import CAS.coq.sg_ltr.structures.
Require Import CAS.coq.sg_ltr.cast. 
Require Import CAS.coq.sg_ltr.classify. 
Section Theory.

  Variable L S: Type.

  Variable eqL : brel L.
  Variable refL : brel_reflexive L eqL.
  Variable wL  : L.
  
  Variable eqS : brel S.
  Variable refS : brel_reflexive S eqS.
  Variable symS : brel_symmetric S eqS.
  Variable trnS : brel_transitive S eqS.
  Variable wS  : S. 
  Variable f : S -> S.
  Variable ntS : brel_not_trivial S eqS f.

  Variable ltr : ltr_type L S. 
  Variable cong_ltr : A_ltr_congruence eqL eqS ltr. 

Lemma sg_ltr_union_lift_distributive : 
  A_sg_ltr_distributive (brel_set eqS) (bop_union eqS) (ltr_lift_op eqS ltr). 
Proof. intros l Y Z. 
       apply brel_set_intro_prop; auto.
       split; intros a H.        
       - apply in_set_bop_union_intro; auto.
         apply in_set_ltr_lift_elim in H; auto. 
         destruct H as [ x [ P1 P2 ]]. 
         apply in_set_bop_union_elim in P1; auto.
         destruct P1 as [R | R].
         + left. apply (in_set_ltr_lift_intro _ _ eqL); auto. 
           exists x; split; auto. 
         + right. apply (in_set_ltr_lift_intro _ _ eqL); auto. 
           exists x; split; auto. 
       - apply in_set_bop_union_elim in H; auto.
         destruct H as [H | H].
         + apply in_set_ltr_lift_elim in H; auto.
           destruct H as [ x [ P1 P2 ] ]. 
           apply (in_set_ltr_lift_intro _ _ eqL); auto.
           exists x; split; auto.
           apply in_set_bop_union_intro; auto. 
         + apply (in_set_ltr_lift_intro _ _ eqL); auto.
           apply in_set_ltr_lift_elim in H; auto.
           destruct H as [x [P1 P2]].
           exists x; split; auto.
           apply in_set_bop_union_intro; auto. 
Qed. 


Lemma sg_ltr_union_lift_absorptive (IR : A_ltr_is_right eqS ltr): 
        A_sg_ltr_absorptive (brel_set eqS) (bop_union eqS) (ltr_lift_op eqS ltr). 
Proof. intros l Y. 
       apply brel_set_intro_prop; auto.
       split; intros a H. 
       - apply in_set_bop_union_intro; auto. 
       - apply in_set_bop_union_elim in H; auto.
         destruct H as [ H | H]; auto. 
         + apply in_set_ltr_lift_elim in H; auto.
           destruct H as [x [H1 H2]].
           assert (H4 := IR l x). apply symS in H4. 
           assert (H5 := trnS _ _ _ H4 H2).
           assert (H6 := in_set_right_congruence _ _ symS trnS _ _ _ H5 H1).
           exact H6. 
Defined. 

Lemma sg_ltr_union_lift_not_absorptive (NIR : A_ltr_not_is_right eqS ltr): 
        A_sg_ltr_not_absorptive (brel_set eqS) (bop_union eqS) (ltr_lift_op eqS ltr). 
Proof. destruct NIR as [[l s] nir].
       exists (l, s :: nil). unfold ltr_lift_op. simpl.
       case_eq(brel_set eqS (s :: nil) (bop_union eqS (s :: nil) (ltr l s :: nil))); intro A; auto.
       apply brel_set_elim_prop in A; auto.
       destruct A as [A B].
       assert (C : in_set eqS (bop_union eqS (s :: nil) (ltr l s :: nil)) (ltr l s) = true).
       {
         apply in_set_bop_union_intro; auto.
         right. apply in_set_cons_intro; auto. 
       } 
       assert (D := B _ C).
       apply in_set_cons_elim in D; auto.
       destruct D as [D | D].
       - apply symS in D. rewrite D in nir.
         discriminate nir. 
       - compute in D. discriminate D.
Defined.


Definition A_sg_ltr_union_lift_absorptive_decidable 
  (ld : A_ltr_is_right_decidable eqS ltr) : 
    A_sg_ltr_absorptive_decidable (brel_set eqS) (bop_union eqS) (ltr_lift_op eqS ltr)
  := match ld with
     | inl ir  => inl (sg_ltr_union_lift_absorptive ir)
     | inr nir => inr (sg_ltr_union_lift_not_absorptive nir)
     end.                                                          

(* nice example of a single property depending on decidability of another *) 
Lemma sg_ltr_union_lift_not_strictly_absorptive (IR_d : A_ltr_is_right_decidable eqS ltr): 
        A_sg_ltr_not_strictly_absorptive (brel_set eqS) (bop_union eqS) (ltr_lift_op eqS ltr). 
Proof. destruct IR_d as [IR | NIR].
       - exists (wL, wS::nil). right.
         unfold ltr_lift_op; simpl.
         assert (A := IR wL wS).
         apply brel_set_intro_prop; auto; split; intros s B.
         + apply in_set_bop_union_intro; auto.
         + apply in_set_bop_union_elim in B; auto.
           destruct B as [B | B]; auto. 
           * apply in_set_singleton_elim in B; auto.
             apply in_set_singleton_intro; auto.
             exact (trnS _ _ _ A B). 
       - assert (A := sg_ltr_union_lift_not_absorptive NIR).
         destruct A as [[l X] B].
         exists (l, X); auto. 
Defined.


(*
*) 

Lemma sg_ltr_union_lift_exists_id_ann_equal :
  A_sg_ltr_exists_id_ann_equal (brel_set eqS) (bop_union eqS) (ltr_lift_op eqS ltr).
Proof. exists nil; split. 
       - apply bop_union_nil_is_id; auto. 
       - apply A_ltr_lift_is_ann; auto.       
Defined.

Definition A_sg_ltr_union_lift_exists_id_ann_equal_decidable :=
  A_SG_LTR_Id_Ann_Equal _ _ _ sg_ltr_union_lift_exists_id_ann_equal. 

End Theory. 

Section ACAS.

Section Proofs.

  Variables
    (L S : Type)
    (eqvL : A_eqv L)              
    (eqvS : A_eqv S)
    (ltr : ltr_type L S)
    (ltrP : A_ltr_properties (A_eqv_eq _ eqvL) (A_eqv_eq _ eqvS) ltr).


Definition A_sg_ltr_union_lift_properties :=
let eqvPS := A_eqv_proofs _ eqvS in
let eqS   := A_eqv_eq _ eqvS in
let wS    := A_eqv_witness _ eqvS in  
let refS := A_eqv_reflexive _ _ eqvPS  in
let symS := A_eqv_symmetric _ _ eqvPS  in
let trnS := A_eqv_transitive _  _ eqvPS in
let eqvPL := A_eqv_proofs _ eqvL in
let eqL   := A_eqv_eq _ eqvL in
let wL    := A_eqv_witness _ eqvL in  
let refL := A_eqv_reflexive _ _ eqvPL  in
let IR_d  := A_ltr_props_is_right_d _ _ _ ltrP in  
let cong_ltr := A_ltr_props_congruence _ _ _ ltrP in   
  {|
    A_sg_ltr_distributive_d        :=
      inl (sg_ltr_union_lift_distributive _ _ eqL refL eqS refS symS trnS ltr cong_ltr)
  ; A_sg_ltr_absorptive_d          :=
      A_sg_ltr_union_lift_absorptive_decidable _ _ eqS refS symS trnS ltr IR_d 
  ; A_sg_ltr_strictly_absorptive_d :=
      inr (sg_ltr_union_lift_not_strictly_absorptive _ _ wL eqS refS symS trnS wS ltr IR_d)
  |}. 
    
End Proofs.   

Section Combinators.


Definition A_sg_ltr_union_lift {L S : Type} (ltrLS : @A_ltr L S) : @A_sg_ltr L (finite_set S) := 
let eqvS  := A_ltr_carrier ltrLS in
let eqvPS := A_eqv_proofs S eqvS in   
let eqS   := A_eqv_eq S eqvS in
let refS  := A_eqv_reflexive _ _ eqvPS in
let symS  := A_eqv_symmetric _ _ eqvPS in
let trnS  := A_eqv_transitive _ _ eqvPS in 
let wS    := A_eqv_witness _ eqvS in
let eqvL  := A_ltr_label ltrLS in
let eqvPL := A_eqv_proofs L eqvL in
let refL  := A_eqv_reflexive _ _ eqvPL in
let eqL   := A_eqv_eq L eqvL in   
let wL    := A_eqv_witness _ eqvL in
let ltr := A_ltr_ltr ltrLS in
let ltrP := A_ltr_props ltrLS in 
{|
  A_sg_ltr_carrier        := A_eqv_set _ eqvS
; A_sg_ltr_label          := eqvL
; A_sg_ltr_plus           := bop_union eqS
; A_sg_ltr_ltr            := ltr_lift_op eqS ltr 
; A_sg_ltr_plus_props     := sg_C_proofs_union eqvS
; A_sg_ltr_ltr_props      := A_ltr_lift_properties eqL eqS ltr eqvPL eqvPS wL wS ltrP 
; A_sg_ltr_id_ann_props_d := A_sg_ltr_union_lift_exists_id_ann_equal_decidable _ _ eqS refS symS trnS ltr 
; A_sg_ltr_props          := A_sg_ltr_union_lift_properties _ _ eqvL eqvS ltr ltrP 
; A_sg_ltr_ast            := Cas_ast ("sg_ltr_union_lift", nil) (* FIX ME *) 
|}.

End Combinators.   

End ACAS.

Section AMCAS.


  Definition A_sg_ltr_union_lift_below_ltr {L S : Type} (A : @A_below_ltr L S) : @A_below_sg_ltr L (finite_set S) :=
            A_classify_sg_ltr (A_sg_ltr_union_lift (A_cast_up_ltr A)). 

  Definition A_mcas_sg_ltr_union_lift {L S : Type} (A : @A_ltr_mcas L S) : @A_sg_ltr_mcas L (finite_set S) :=
    match A with
    | A_MCAS_ltr B        => A_MCAS_sg_ltr (A_sg_ltr_union_lift_below_ltr B)  
    | A_MCAS_ltr_Error sl => A_MCAS_sg_ltr_Error sl
    end.

End AMCAS.


Section CAS.


Section Proofs.

Definition sg_ltr_union_lift_properties {L S : Type} 
    (eqvL : @eqv L)              
    (eqvS : @eqv S)
    (ltr : ltr_type L S)
    (ltrP : @ltr_properties L S) :=     
let wS    := eqv_witness eqvS in  
let wL    := eqv_witness eqvL in  
let IR_d  := ltr_props_is_right_d ltrP in  
  {|
    sg_ltr_distributive_d        :=
      inl (SG_LTR_Distributive(wL, wS :: nil))
  ; sg_ltr_absorptive_d          :=
      match IR_d with
      | inl _                         =>
          inl (SG_LTR_Absorptive (wL, wS :: nil))
      | inr (LTR_not_is_right (l, s)) =>
          inr (SG_LTR_Not_Absorptive (l, s :: nil))
      end
  ; sg_ltr_strictly_absorptive_d :=
      match IR_d with
      | inl _                         =>
          inr (SG_LTR_Not_Strictly_Absorptive (wL, wS :: nil))
      | inr (LTR_not_is_right (l, s)) =>
          inr (SG_LTR_Not_Strictly_Absorptive (l, s :: nil))
      end
  |}. 
    

End Proofs.   

Section Combinators.


Definition sg_ltr_union_lift {L S : Type} (ltrLS : @ltr L S) : @sg_ltr L (finite_set S) := 
let eqvS  := ltr_carrier ltrLS in
let eqvL  := ltr_label ltrLS in
let eqS   := eqv_eq eqvS in
let wS    := eqv_witness eqvS in
let wL    := eqv_witness eqvL in
let ltr   := ltr_ltr ltrLS in
let ltrP  := ltr_props ltrLS in 
{|
  sg_ltr_carrier        := eqv_set eqvS
; sg_ltr_label          := eqvL
; sg_ltr_plus           := bop_union eqS
; sg_ltr_ltr            := ltr_lift_op eqS ltr 
; sg_ltr_plus_props     := sg_C_certs_union eqvS
; sg_ltr_ltr_props      := ltr_lift_properties ltrP wL wS 
; sg_ltr_id_ann_props_d := SG_LTR_Id_Ann_Equal nil
; sg_ltr_props          := sg_ltr_union_lift_properties eqvL eqvS ltr ltrP 
; sg_ltr_ast            := Cas_ast ("sg_ltr_union_lift", nil) (* FIX ME *) 
|}.

End Combinators.   

End CAS.

Section AMCAS.

  Definition sg_ltr_union_lift_below_ltr {L S : Type} (A : @below_ltr L S) : @below_sg_ltr L (finite_set S) :=
            classify_sg_ltr (sg_ltr_union_lift (cast_up_ltr A)). 

  Definition mcas_sg_ltr_union_lift {L S : Type} (A : @ltr_mcas L S) : @sg_ltr_mcas L (finite_set S) :=
    match A with
    | MCAS_ltr B        => MCAS_sg_ltr (sg_ltr_union_lift_below_ltr B)  
    | MCAS_ltr_Error sl => MCAS_sg_ltr_Error sl
    end.

End AMCAS.


Section Verify.


Lemma correct_sg_ltr_union_lift_properties
  (L S : Type) 
  (eqvL : A_eqv L) 
  (eqvS : A_eqv S) 
  (ltr : ltr_type L S)
  (ltrP : A_ltr_properties (A_eqv_eq L eqvL) (A_eqv_eq S eqvS) ltr)  : 
  P2C_sg_ltr_properties
    (brel_set (A_eqv_eq _ eqvS))
    (bop_union (A_eqv_eq _ eqvS))
    (ltr_lift_op (A_eqv_eq S eqvS) ltr)
    (A_sg_ltr_union_lift_properties _ _ eqvL eqvS ltr ltrP)
    (A_eqv_witness _ eqvL)
    ((A_eqv_witness _ eqvS) :: nil) 
  = 
  sg_ltr_union_lift_properties
    (A2C_eqv _ eqvL) (A2C_eqv _ eqvS)
    ltr 
    (P2C_ltr_properties
       (A_eqv_eq L eqvL)
       (A_eqv_eq S eqvS) ltr ltrP
       (A_eqv_witness _ eqvL)
       (A_eqv_witness _ eqvS)).
Proof. destruct ltrP.
       unfold sg_ltr_union_lift_properties, A_sg_ltr_union_lift_properties,
         P2C_ltr_properties, P2C_sg_ltr_properties; simpl. 
       destruct A_ltr_props_is_right_d as [IR | [[l s] NR]]; simpl; 
       unfold p2c_sg_ltr_distributive; 
       unfold p2c_sg_ltr_absorptive; 
       unfold p2c_sg_ltr_not_strictly_absorptive; simpl; 
       reflexivity. 
Qed.


Theorem correct_sg_ltr_union_lift (L S : Type) (ltrLS: @A_ltr L S):  
   A2C_sg_ltr (A_sg_ltr_union_lift ltrLS)
   =
   sg_ltr_union_lift (A2C_ltr ltrLS).
Proof. unfold sg_ltr_union_lift, A_sg_ltr_union_lift, A2C_ltr, A2C_sg_ltr.
       destruct ltrLS. simpl.
       rewrite correct_eqv_set.
       rewrite correct_sg_C_certs_union. 
       rewrite correct_ltr_lift_properties.
       rewrite correct_sg_ltr_union_lift_properties.              
       reflexivity.
Qed.


Theorem correct_sg_ltr_union_lift_below_ltr  (L S : Type) (A : @A_below_ltr L S) : 
 A2C_below_sg_ltr (A_sg_ltr_union_lift_below_ltr A)
  =
 sg_ltr_union_lift_below_ltr (A2C_below_ltr A).
Proof. unfold A_sg_ltr_union_lift_below_ltr, sg_ltr_union_lift_below_ltr.
       rewrite cast_up_ltr_A2C_commute. 
       rewrite <- correct_sg_ltr_union_lift.
       rewrite correct_classify_sg_ltr. 
       reflexivity.
Qed.

Theorem correct_mcas_sg_ltr_union_lift (L S : Type) (ltrLS : @A_ltr_mcas L S) : 
         mcas_sg_ltr_union_lift (A2C_mcas_ltr ltrLS) 
         = 
         A2C_mcas_sg_ltr (A_mcas_sg_ltr_union_lift ltrLS).
Proof. unfold A_mcas_sg_ltr_union_lift, mcas_sg_ltr_union_lift. 
       destruct ltrLS; simpl; try reflexivity.
       rewrite <- correct_sg_ltr_union_lift_below_ltr.
       reflexivity. 
Qed. 

End Verify. 










