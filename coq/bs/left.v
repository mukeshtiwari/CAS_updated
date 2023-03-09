Require Import Coq.Strings.String.
Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.
Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures.
Require Import CAS.coq.sg.theory. 
Require Import CAS.coq.bs.properties.
Require Import CAS.coq.bs.structures.
Require Import CAS.coq.bs.cast.
Require Import CAS.coq.bs.classify. 

Require Import CAS.coq.sg.left.
Require Import CAS.coq.sg.cast_up.

Section Theory.

Variable S : Type.
Variable rS : brel S.
Variable wS : S.
Variable f : S -> S. 
Variable nt : brel_not_trivial S rS f. 
Variable refS : brel_reflexive S rS.
Variable symS : brel_symmetric S rS.
Variable tranS : brel_transitive S rS. 
Variable addS  : binary_op S.
Variable congS: brel_congruence S rS rS.
Variable commS : bop_commutative S rS addS. 

Lemma A_bs_left_left_distributive
  (idemS : bop_idempotent S rS addS) :
  A_bs_left_distributive rS addS bop_left. 
Proof. intros s1 s2 s3 ; compute.
       exact (symS _ _ (idemS s1)).
Qed. 

Lemma A_bs_left_not_left_distributive
  (nidemS : bop_not_idempotent S rS addS) :
  A_bs_not_left_distributive rS addS bop_left. 
Proof. destruct nidemS as [a A]. exists (a, (a, a)). compute.
       case_eq(rS a (addS a a)); intro B; auto. apply symS in B. rewrite B in A.
       discriminate A.
Defined.        

Lemma A_bs_left_right_distributive :
  A_bs_right_distributive rS addS bop_left. 
Proof. intros s1 s2 s3 ; compute.  apply refS. Qed. 

Lemma A_bs_left_left_absorptive
  (idemS : bop_idempotent S rS addS) :
  A_bs_left_absorptive rS addS bop_left. 
Proof. intros s1 s2 ; compute. exact (symS _ _ (idemS s1)).  Qed.

Lemma A_bs_left_not_left_absorptive
  (nidemS : bop_not_idempotent S rS addS) :
  A_bs_not_left_absorptive rS addS bop_left. 
Proof. destruct nidemS as [a A]. exists (a, a). compute.
       case_eq(rS a (addS a a)); intro B; auto. apply symS in B. rewrite B in A.
       discriminate A.
Defined.        

Lemma A_bs_left_right_absorptive
  (L : bop_is_left S rS addS) :
  A_bs_right_absorptive rS addS bop_left. 
Proof. intros s1 s2 ; compute. apply symS. exact (L s1 s2). Qed. 


Lemma A_bs_left_not_right_absorptive
  (*NL : bop_not_is_left S rS addS*) :
  A_bs_not_right_absorptive rS addS bop_left. 
Proof. exists (cef_commutative_implies_not_is_left rS addS wS f). 
       unfold cef_commutative_implies_not_is_left.
       case_eq(rS (addS (f wS) wS) wS); compute; intro A. 
       + destruct (nt wS) as [B C].
         case_eq(rS (f wS) (addS (f wS) wS)); intro D; auto.
         rewrite (tranS _ _ _ D A) in C.
         discriminate C. 
       + case_eq(rS wS (addS wS (f wS))); intro B; auto.
         assert (C := commS wS (f wS)).
         assert (D := tranS _ _ _ B C). apply symS in D.
         rewrite D in A. discriminate A. 
(*         
       destruct NL as [[s1 s2] A]. exists (s1, s2). compute. 
       case_eq(rS s1 (addS s1 s2)); intro B; auto. apply symS in B. rewrite B in A.
       discriminate A.
*) 
Defined.

(* strict absorptivity. We insist on idempotence! 
Lemma bs_bops_not_left_strictly_absorptive : 
  bop_idempotent S rS addS  ->
  bops_not_left_strictly_absorptive S rS addS bop_left.
Proof.
  intros Ha.
  exists (wS, wS); compute.
  right.
  apply symS, Ha.
Qed.

Lemma bs_bops_not_right_strictly_absorptive : 
  bop_idempotent S rS addS  ->
  bops_not_right_strictly_absorptive S rS addS bop_left.
Proof.
  intros Ha.
  exists (wS, wS); compute.
  right.
  apply symS.
  apply Ha.
Qed.
*)

Definition A_bs_left_exists_id_ann_decide
  (id_d : bop_exists_id_decidable S rS addS) : 
  A_bs_exists_id_ann_decidable rS addS bop_left :=
  match id_d with
  | inl id => A_Id_Ann_Id_None _ _ _ (id, bop_left_not_exists_ann S rS f nt)
  | inr nid => A_Id_Ann_None _ _ _ (nid, bop_left_not_exists_ann S rS f nt)                                    
  end. 

Definition A_bs_left_exists_id_ann_decide_dual
  (ann_d : bop_exists_ann_decidable S rS addS) : 
  A_bs_exists_id_ann_decidable rS bop_left addS :=
  match ann_d with
  | inl ann  => A_Id_Ann_None_Ann _ _ _ (bop_left_not_exists_id S rS f nt, ann)
  | inr nann => A_Id_Ann_None _ _ _ (bop_left_not_exists_id S rS f nt, nann)                                    
  end. 

End Theory.

Section ACAS.

Definition A_bs_left_properties {S : Type} (sg : @A_sg_C S) :=
let eqv   := A_sg_C_eqv S sg in
let eqvP  := A_eqv_proofs S eqv in  
let rS    := A_eqv_eq _ eqv in
let wS    := A_eqv_witness _ eqv in
let f    := A_eqv_new _ eqv in
let ntS    := A_eqv_not_trivial _ eqv in
let addS  := A_sg_C_bop S sg in
let refS   := A_eqv_reflexive S rS eqvP in
let symS   := A_eqv_symmetric S rS eqvP in
let trnS   := A_eqv_transitive S rS eqvP in
let sgP    := A_sg_C_proofs _ sg in
let commS  := A_sg_C_commutative _ _ _ sgP in
(*let not_is_left := bop_commutative_implies_not_is_left _ rS addS wS f ntS symS trnS commS in *) 
{|
  A_bs_left_distributive_d := match A_sg_C_idempotent_d _ _ _ sgP with
                              | inl idemS  => inl (A_bs_left_left_distributive S rS symS addS idemS)
                              | inr nidemS => inr (A_bs_left_not_left_distributive S rS symS addS nidemS)
                              end 
; A_bs_right_distributive_d       := inl (A_bs_left_right_distributive S rS refS addS)
; A_bs_left_absorptive_d   := match A_sg_C_idempotent_d _ _ _ sgP with
                              | inl idemS  => inl (A_bs_left_left_absorptive S rS symS addS idemS)
                              | inr nidemS => inr (A_bs_left_not_left_absorptive S rS symS addS nidemS)
                              end 
; A_bs_right_absorptive_d  := inr (A_bs_left_not_right_absorptive S rS wS f ntS symS trnS addS commS)
|}.

Definition A_bs_left_id_ann_properties {S : Type} (sg : A_sg_C S) :=
let eqv   := A_sg_C_eqv S sg in
let eq    := A_eqv_eq _ eqv in
let f     := A_eqv_new _ eqv in
let nt    := A_eqv_not_trivial _ eqv in
let addS  := A_sg_C_bop S sg in
{|
  A_id_ann_plus_times_d := A_bs_left_exists_id_ann_decide S eq f nt addS (A_sg_C_exists_id_d _ sg)
; A_id_ann_times_plus_d := A_bs_left_exists_id_ann_decide_dual S eq f nt addS (A_sg_C_exists_ann_d _ sg)
|}.


Definition A_bs_left {S : Type} (sg : A_sg_C S) : @A_bs S :=
{|
  A_bs_eqv          := A_sg_C_eqv _ sg
; A_bs_plus         := A_sg_C_bop _ sg  
; A_bs_times        := bop_left 
; A_bs_plus_props   := A_sg_C_proofs _ sg 
; A_bs_times_props  := sg_proofs_left _ (A_sg_C_eqv _ sg)
; A_bs_id_ann_props := A_bs_left_id_ann_properties sg 
; A_bs_props        := A_bs_left_properties sg 
; A_bs_ast          := Ast_bs_left (A_sg_C_ast _ sg) 
|}.


End ACAS.

Section AMCAS.

  Open Scope string.
  
  Definition A_bs_left_below_bs {S : Type} (A : @A_below_sg_C S) : @A_below_bs S :=
            A_classify_bs (A_bs_left (A_cast_up_sg_C A)). 

  Definition A_mcas_bs_left {S : Type} (A : @A_sg_mcas S) : @A_bs_mcas S :=
    match A with
    | A_MCAS_sg_Error sl => A_MCAS_bs_Error sl      
    | A_MCAS_sg (A_Below_sg_sg_C B) => A_MCAS_bs (A_bs_left_below_bs B)  
    | A_MCAS_sg _ => A_MCAS_bs_Error ("bs_left : semigroup must be commutative" :: nil)
    end.

End AMCAS.


Section CAS.


Definition bs_left_properties (S : Type) (sg : @sg_C S) :=
let eqv   := sg_C_eqv sg in
let eq    := eqv_eq eqv in
let wS    := eqv_witness eqv in
let f     := eqv_new eqv in
let sgP   := sg_C_certs sg in
let add   := sg_C_bop sg in
{|
  bs_left_distributive_d      :=
    match sg_C_idempotent_d sgP with
    | Certify_Idempotent       => inl (BS_Left_Distributive wS)
    | Certify_Not_Idempotent a => inr (BS_Not_Left_Distributive (a, (a, a)) )
    end 
; bs_right_distributive_d     := inl (BS_Right_Distributive wS) 
; bs_left_absorptive_d        :=
    match sg_C_idempotent_d sgP with
    | Certify_Idempotent       => inl (BS_Left_Absorptive wS)
    | Certify_Not_Idempotent a => inr (BS_Not_Left_Absorptive (a, a))
    end 
; bs_right_absorptive_d       :=
    inr (BS_Not_Right_Absorptive (cef_commutative_implies_not_is_left eq add wS f))
|}.


Definition bs_left_exists_id_ann_decide {S : Type}
  (id_d : @check_exists_id S) : @bs_exists_id_ann_decidable S :=
  match id_d with
  | Certify_Exists_Id id => Id_Ann_Id_None id 
  | _                    => Id_Ann_None 
  end. 

Definition bs_left_exists_id_ann_decide_dual {S : Type}
  (ann_d : @check_exists_ann S) : @bs_exists_id_ann_decidable S :=
  match ann_d with
  | Certify_Exists_Ann ann  => Id_Ann_None_Ann ann
  | _                       => Id_Ann_None
  end. 

Definition bs_left_id_ann_properties {S : Type} (sg : @sg_C S) :=
{|
  id_ann_plus_times_d := bs_left_exists_id_ann_decide (sg_C_exists_id_d sg)
; id_ann_times_plus_d := bs_left_exists_id_ann_decide_dual (sg_C_exists_ann_d sg)
|}.


Definition bs_left {S : Type} (sg : @sg_C S) : @bs S :=
let eqv  := sg_C_eqv sg in
{|
  bs_eqv          := eqv 
; bs_plus         := sg_C_bop sg  
; bs_times        := bop_left 
; bs_plus_props   := sg_C_certs sg 
; bs_times_props  := sg_certs_left eqv
; bs_id_ann_props := bs_left_id_ann_properties sg 
; bs_props        := bs_left_properties _ sg 
; bs_ast          := Ast_bs_left (sg_C_ast sg) 
|}.

End CAS.


Section MCAS.

  Open Scope string.
  
  Definition bs_left_below_bs {S : Type} (A : @below_sg_C S) : @below_bs S :=
            classify_bs (bs_left (cast_up_sg_C A)). 

  Definition mcas_bs_left {S : Type} (A : @sg_mcas S) : @bs_mcas S :=
    match A with
    | MCAS_sg_Error sl => MCAS_bs_Error sl      
    | MCAS_sg (Below_sg_sg_C B) => MCAS_bs (bs_left_below_bs B)  
    | MCAS_sg _ => MCAS_bs_Error ("bs_left : semigroup must be commutative" :: nil)
    end.

End MCAS.

Section Verify.

  
Section Decide.

  Variables (S : Type)
    (eq : brel S)
    (f : S -> S)
    (nt : brel_not_trivial S eq f)
    (addS : binary_op S).     

  Lemma correct_bs_left_exists_id_ann_decide
    (id_d : bop_exists_id_decidable S eq addS) : 
   bs_left_exists_id_ann_decide
      (p2c_exists_id_check S eq addS id_d) 
   = p2c_exists_id_ann S eq addS bop_left
       (A_bs_left_exists_id_ann_decide S eq f nt addS id_d). 
  Proof. destruct id_d as [[id idP] | nid]; compute; reflexivity. Qed. 

  Lemma correct_bs_left_exists_id_ann_decide_dual
    (ann_d : bop_exists_ann_decidable S eq addS) : 
   bs_left_exists_id_ann_decide_dual
      (p2c_exists_ann_check S eq addS ann_d) 
   = p2c_exists_id_ann S eq bop_left addS 
       (A_bs_left_exists_id_ann_decide_dual S eq f nt addS ann_d). 
  Proof. destruct ann_d as [[ann annP] | nann]; compute; reflexivity. Qed. 

End Decide.   

Lemma correct_bs_left_id_ann_properties (S : Type) (sgS : A_sg_C S) :
   bs_left_id_ann_properties (A2C_sg_C sgS)
   =
   P2C_id_ann S (A_eqv_eq S (A_sg_C_eqv S sgS))
              (A_sg_C_bop S sgS)
              bop_left
              (A_bs_left_id_ann_properties sgS).
Proof. unfold A_bs_left_id_ann_properties,
         bs_left_id_ann_properties, P2C_id_ann, A2C_sg; simpl.
       destruct sgS. destruct A_sg_C_eqv. simpl.
       rewrite <- correct_bs_left_exists_id_ann_decide.
       rewrite <- correct_bs_left_exists_id_ann_decide_dual.
       reflexivity.
Qed.

Lemma correct_bs_left_properties (S : Type) (sgS : A_sg_C S) :
   bs_left_properties S (A2C_sg_C sgS)
   = 
   P2C_bs (A_eqv_eq S (A_sg_C_eqv _ sgS))
       (A_eqv_witness S (A_sg_C_eqv _ sgS))
       (A_sg_C_bop S sgS)
       bop_left (A_bs_left_properties sgS).   
Proof. unfold bs_left_properties, A_bs_left_properties,
         A2C_sg_C, P2C_bs; simpl.
       destruct sgS. destruct A_sg_C_proofs. simpl.
       destruct A_sg_C_idempotent_d as [idemS | [a nidemS]];
       destruct A_sg_C_exists_id_d as [[id idP] | nidP]; simpl;
         try reflexivity.
Qed.

Theorem correct_bs_left (S : Type) (sgS : A_sg_C S) : 
         bs_left (A2C_sg_C sgS) 
         = 
         A2C_bs (A_bs_left sgS). 
Proof. unfold bs_left, A_bs_left, A2C_bs; simpl. 
       rewrite <- correct_sg_certs_left.
       rewrite <- correct_bs_left_properties.
       rewrite <- correct_bs_left_id_ann_properties. 
       reflexivity. 
Qed.


Theorem correct_bs_left_below_bs (S : Type) (A : @A_below_sg_C S) : 
  bs_left_below_bs (A2C_below_sg_C A)
  =
  A2C_below_bs (A_bs_left_below_bs A). 
Proof. unfold A_bs_left_below_bs, bs_left_below_bs.
       rewrite cast_up_sg_C_A2C_commute.
       rewrite correct_bs_left. 
       rewrite correct_classify_bs.
       reflexivity.
Qed.

Theorem correct_mcas_bs_left (S : Type) (sgS : @A_sg_mcas S) : 
         mcas_bs_left (A2C_sg_mcas sgS) 
         = 
         A2C_bs_mcas (A_mcas_bs_left sgS). 
Proof.  unfold mcas_bs_left, A_mcas_bs_left.
        destruct sgS; simpl; try reflexivity.
        destruct a; simpl; try reflexivity. 
        rewrite correct_bs_left_below_bs.
        reflexivity. 
Qed.

End Verify.     


