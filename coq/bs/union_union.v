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

(* 

Should this combinator be implemented with bs_twin(sg_union)? 

*) 

Section Theory.

  Variable S: Type.
  Variable eq : brel S.
  Variable wS  : S. 
  Variable f : S -> S.
  Variable nt : brel_not_trivial S eq f. 
  Variable ref : brel_reflexive S eq.
  Variable sym : brel_symmetric S eq.
  Variable trn : brel_transitive S eq.

Lemma bops_union_union_left_distributive : A_bs_left_distributive(brel_set eq) (bop_union eq) (bop_union eq). 
Proof. intros Z X Y.
       apply brel_set_intro_prop; auto. split.
       + intros s A.
         apply in_set_bop_union_elim in A; auto.
         apply in_set_bop_union_intro; auto.
         destruct A as [A | A].
         ++ left. apply in_set_bop_union_intro; auto.
         ++ apply in_set_bop_union_elim in A; auto.
            destruct A as [A | A].
            +++ left. apply in_set_bop_union_intro; auto.
            +++ right. apply in_set_bop_union_intro; auto.
       + intros s A.
         apply in_set_bop_union_elim in A; auto.
         apply in_set_bop_union_intro; auto.
         destruct A as [A | A].
         ++ apply in_set_bop_union_elim in A; auto.
            destruct A as [A | A].
            +++ left. exact A. 
            +++ right. apply in_set_bop_union_intro; auto.
         ++ apply in_set_bop_union_elim in A; auto.
            destruct A as [A | A].
            +++ left. exact A. 
            +++ right. apply in_set_bop_union_intro; auto.
Qed. 

Lemma bops_union_union_right_distributive : 
        A_bs_right_distributive (brel_set eq) (bop_union eq) (bop_union eq). 
Proof. apply bs_left_distributive_implies_right; auto. 
       apply brel_set_transitive; auto. 
       apply bop_union_congruence; auto. 
       apply bop_union_commutative; auto. 
       apply bop_union_commutative; auto. 
       apply bops_union_union_left_distributive; auto. 
Defined. 


Lemma bops_union_union_not_left_absorptive : 
  A_bs_not_left_absorptive (brel_set eq) (bop_union eq) (bop_union eq). 
Proof. exists (nil, wS :: nil). compute. reflexivity. Defined. 

(* strict absorption 
Lemma bops_union_union_not_left_strictly_absorptive : 
  bops_not_left_strictly_absorptive (finite_set S) 
    (brel_set eq) (bop_union eq) (bop_union eq). 
Proof. exists (nil, wS :: nil). compute. left. reflexivity. Defined.

Lemma bops_union_union_not_right_strictly_absorptive : 
  bops_not_right_strictly_absorptive (finite_set S) 
    (brel_set eq) (bop_union eq) (bop_union eq). 
Proof. exists (nil, wS :: nil). compute. left. reflexivity. Defined.
*)




Lemma bops_union_union_not_right_absorptive : 
  A_bs_not_right_absorptive (brel_set eq) (bop_union eq) (bop_union eq). 
Proof. exists (nil, wS :: nil). compute. reflexivity. Defined.


Lemma bops_union_union_id_equals_ann_decide (fin_d : carrier_is_finite_decidable S eq) :
  A_bs_exists_id_ann_decidable (brel_set eq) (bop_union eq) (bop_union eq). 
Proof. destruct fin_d as [finP | nfinP].
       + assert (A : A_bs_exists_id_ann_not_equal (brel_set eq) (bop_union eq) (bop_union eq)).
            exists (nil, (projT1 finP) tt). split. split. 
            apply bop_union_nil_is_id; auto. 
            apply bop_union_enum_is_ann; auto.
            case_eq(brel_set eq nil (projT1 finP tt)); intro B; auto.
            destruct finP as [enum P]. unfold projT1 in B.
            assert (C := P wS).
            apply brel_set_elim_prop in B;auto. destruct B as [B1 B2].
            assert (D := B2 _ C).
            compute in D. discriminate D.
         exact (A_Id_Ann_Not_Equal _ _ _ A). 
       + exact (A_Id_Ann_Id_None _ _ _
                   (bop_union_exists_id S eq ref sym trn,
                    bop_union_not_exists_ann S eq ref sym trn nfinP)). 
Defined.  

End Theory.


(*
Section ACAS.


Definition id_ann_proofs_union_union
           (S : Type) (eq : brel S) (wS : S) (fin_d : carrier_is_finite_decidable S eq) (eqvS : eqv_proofs S eq) : 
               id_ann_proofs 
                  (finite_set S)
                  (brel_set eq)
                  (bop_union eq)
                  (bop_union eq) :=
let ref := A_eqv_reflexive _ _ eqvS in
let sym := A_eqv_symmetric _ _ eqvS in
let trn := A_eqv_transitive _ _ eqvS in      
{|
  A_id_ann_plus_times_d := bops_union_union_id_equals_ann_decide S eq wS ref sym trn fin_d 
; A_id_ann_times_plus_d := bops_union_union_id_equals_ann_decide S eq wS ref sym trn fin_d 
|}.
             

Definition semiring_proofs_union_union 
  (S : Type) (eq : brel S) (wS : S) (eqvS : eqv_proofs S eq) : 
     semiring_proofs
       (finite_set S)
       (brel_set eq)
       (bop_union eq)
       (bop_union eq) := 
let refS := A_eqv_reflexive _ _ eqvS in
let symS := A_eqv_symmetric _ _ eqvS in
let tranS := A_eqv_transitive _ _ eqvS in      
{|
  A_semiring_left_distributive       := bops_union_union_left_distributive S eq refS symS tranS
; A_semiring_right_distributive      := bops_union_union_right_distributive S eq refS symS tranS              
; A_semiring_left_left_absorptive_d  := inr (bops_union_union_not_left_left_absorptive S eq wS)
; A_semiring_left_right_absorptive_d := inr (bops_union_union_not_left_right_absorptive S eq wS)                                           
|}.


Definition A_bs_union_union (S : Type) (eqv : A_eqv S) : A_presemiring (finite_set S) :=
let eq         := A_eqv_eq S eqv in
let s          := A_eqv_witness S eqv in
let f          := A_eqv_new S eqv in
let ntS        := A_eqv_not_trivial S eqv in
let fin_d      := A_eqv_finite_d S eqv in
let eqvP       := A_eqv_proofs S eqv in
let CIP        := sg_CI_proofs_union eqv in
let set_new    := λ (l : finite_set S), if brel_set eq nil l then (s :: nil) else nil in
let eqvSET     := eqv_proofs_set S eq eqvP  in 
let NT         := brel_set_not_trivial S eq s in 
let CP         := A_sg_C_proofs_from_sg_CI_proofs
                    (finite_set S)
                    (brel_set eq)
                    (bop_union eq)
                    nil
                    set_new 
                    NT
                    eqvSET
                    CIP in 
{|
  A_presemiring_eqv           := A_eqv_set S eqv 
; A_presemiring_plus          := bop_union eq 
; A_presemiring_times         := bop_union eq 
; A_presemiring_plus_proofs   := CP
; A_presemiring_times_proofs  := A_sg_proofs_from_sg_C_proofs
                                   (finite_set S)
                                   (brel_set eq)
                                   (bop_union eq)
                                   nil
                                   set_new
                                   NT
                                   eqvSET
                                   CP
; A_presemiring_id_ann_proofs := id_ann_proofs_union_union S eq s fin_d eqvP
; A_presemiring_proofs        := semiring_proofs_union_union S eq s eqvP  
; A_presemiring_ast           := Ast_union_union (A_eqv_ast S eqv)
|}.

End ACAS.

Section AMCAS.

Definition A_mcas_bs_union_union (S : Type) (eqv : @A_mcas_eqv S) :=
match eqv with
| A_EQV_eqv A    => A_BS_presemiring _ (A_bs_union_union _ A)
| A_EQV_Error sl => A_BS_Error _ sl     
end.

End AMCAS.

    
Section CAS.

Definition id_ann_certs_union_union {S : Type} (fin_d : @check_is_finite S) :
             @id_ann_certificates (finite_set S) :=
let C := match fin_d with
         | Certify_Is_Finite enum => Id_Ann_Cert_Not_Equal (nil, enum tt) 
         | Certify_Not_Is_Finite => Id_Ann_Cert_Id_None nil 
         end in 
{|
  id_ann_plus_times_d := C
; id_ann_times_plus_d := C
|}.
             

Definition semiring_certs_union_union {S : Type} (wS : S) : @semiring_certificates (finite_set S) := 
{|
  semiring_left_distributive       := Assert_Left_Distributive
; semiring_right_distributive      := Assert_Right_Distributive
; semiring_left_left_absorptive_d  := Certify_Not_Left_Left_Absorptive (nil, wS :: nil)
; semiring_left_right_absorptive_d := Certify_Not_Left_Right_Absorptive (nil, wS :: nil)
|}.

Definition bs_union_union {S : Type} (eqv : @eqv S) : @presemiring (finite_set S) :=
let eq         := eqv_eq eqv in
let s          := eqv_witness eqv in
let f          := eqv_new eqv in
let fin_d      := eqv_finite_d eqv in
let CIP        := sg_CI_certs_union eqv in
let set_new    := λ (l : finite_set S), if brel_set eq nil l then (s :: nil) else nil in
let CP         := sg_C_certs_from_sg_CI_certs
                    (finite_set S)
                    (brel_set eq)
                    (bop_union eq)
                    nil
                    set_new 
                    CIP in 
{|
  presemiring_eqv           := eqv_set eqv 
; presemiring_plus          := bop_union eq 
; presemiring_times         := bop_union eq 
; presemiring_plus_certs   := CP
; presemiring_times_certs  := sg_certs_from_sg_C_certs
                                   (finite_set S)
                                   (brel_set eq)
                                   (bop_union eq)
                                   nil
                                   set_new
                                   CP
; presemiring_id_ann_certs := id_ann_certs_union_union fin_d 
; presemiring_certs        := semiring_certs_union_union s
; presemiring_ast          := Ast_union_union (eqv_ast eqv)
|}.

End CAS.

Section MCAS.

Definition mcas_bs_union_union {S : Type} (eqv : @mcas_eqv S) :=
match eqv with
| EQV_eqv A    => BS_presemiring (bs_union_union A)
| EQV_Error sl => BS_Error sl     
end.

End MCAS.


Section Verify.

Lemma correct_certs_union_union (S : Type) (eq : brel S) (wS : S) (eqvP : eqv_proofs S eq) :
  semiring_certs_union_union wS 
  =                                            
  P2C_semiring (finite_set S)
               (brel_set eq)
               (bop_union eq)
               (bop_union eq)
               (semiring_proofs_union_union S eq wS eqvP). 
Proof. compute. reflexivity. Qed.


Lemma correct_id_ann_certs_union_union (S : Type) (eq : brel S) (wS : S) (fin_d : carrier_is_finite_decidable S eq )(eqvP : eqv_proofs S eq) :
  id_ann_certs_union_union (p2c_is_finite_check _ _ fin_d)
  = 
  P2C_id_ann (finite_set S) (brel_set eq) (bop_union eq) (bop_union eq) 
               (id_ann_proofs_union_union S eq wS fin_d eqvP). 
Proof. unfold id_ann_certs_union_union, id_ann_proofs_union_union, p2c_is_finite_check, P2C_id_ann.
       destruct fin_d as [[h finP] | nfinP]; reflexivity. 
Qed.


Theorem correct_union_union (S : Type) (eqv: A_eqv S) : 
    bs_union_union (A2C_eqv S eqv)
    =
    A2C_presemiring _ (A_bs_union_union S eqv).
Proof. unfold bs_union_union, A_bs_union_union, A2C_presemiring; simpl.
       rewrite correct_eqv_set.
       rewrite correct_bop_union_certs.
       rewrite <- correct_id_ann_certs_union_union.       
       rewrite <- correct_certs_union_union. simpl.
       rewrite <- correct_sg_C_certs_from_sg_CI_certs.
       rewrite <- correct_sg_certs_from_sg_C_certs. simpl.
       rewrite <- correct_sg_C_certs_from_sg_CI_certs.
       reflexivity. 
Qed. 

Theorem correct_bop_mcas_union_union (S : Type) (eqvS : @A_mcas_eqv S): 
         mcas_bs_union_union (A2C_mcas_eqv S eqvS)  
         = 
         A2C_mcas_bs _ (A_mcas_bs_union_union _ eqvS). 
Proof. destruct eqvS; simpl.
       + reflexivity. 
       + unfold mcas_bs_union_union, A_mcas_bs_union_union, A2C_mcas_bs. 
         rewrite correct_union_union. 
         reflexivity.        
Qed.  

 
End Verify.   

*) 
