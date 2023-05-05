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
Require Import CAS.coq.sg.intersect.
Require Import CAS.coq.sg.lift.
Require Import CAS.coq.sg.cast_up.

Require Import CAS.coq.bs.properties.
Require Import CAS.coq.bs.structures.
Require Import CAS.coq.bs.theory.
Require Import CAS.coq.bs.cast_up.


Definition bop_injective (S : Type) (eq : brel S) (bop : binary_op S) := 
  ∀ s t u v: S, eq (bop s t) (bop u v) = true -> (eq s u = true) * (eq t v = true).

Definition bop_not_injective (S : Type) (eq : brel S) (bop : binary_op S) :=
          { z : S * (S * (S * S)) &
                match z with
                | (s, (t, (u, v))) => (eq (bop s t) (bop u v) = true) *((eq s u = true) + (eq t v = true))
                end
          }.

Definition bop_injective_decidable (S : Type) (eq : brel S) (bop : binary_op S) := 
   (bop_injective S eq bop) + (bop_not_injective S eq bop). 


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


Lemma bop_intersect_lift_left_distributive
       (inj : bop_injective S r bS): 
        bop_left_distributive (finite_set S) (brel_set r) (bop_intersect r) (bop_lift r bS). 
Proof. intros X Y Z. 
       apply brel_set_intro_prop; auto.
       split; intros a H.        
          + apply in_set_bop_intersect_intro; auto. 
            apply in_set_bop_lift_elim in H;
            auto. destruct H as [ x [ y [[P1 P2] P3]]].
            apply in_set_bop_intersect_elim in P2; auto.
            destruct P2 as [P2 P4]. split. 
            ++ apply symS in P3. apply (in_set_right_congruence S r symS tranS (bS x y) a ((bop_lift r bS X Y)) P3).
               apply in_set_bop_lift_intro; auto. 
            ++ apply symS in P3. apply (in_set_right_congruence S r symS tranS (bS x y) a ((bop_lift r bS X Z)) P3).
               apply in_set_bop_lift_intro; auto. 
          + apply in_set_bop_intersect_elim in H; auto.
            destruct H as [H1 H2].
            apply in_set_bop_lift_elim in H1; auto. destruct H1 as [ x1 [ y1 [[P1 P2] P3]]].
            apply in_set_bop_lift_elim in H2; auto. destruct H2 as [ x2 [ z2 [[Q1 Q2] Q3]]].
            apply symS in P3. assert (P4 := tranS _ _ _ P3 Q3).
            destruct (inj _ _ _ _ P4) as [Q4 Q5].
            apply (in_set_right_congruence S r symS tranS (bS x1 y1) a (bop_lift r bS X (bop_intersect r Y Z)) P3).
            apply in_set_bop_lift_intro; auto.
            apply in_set_bop_intersect_intro; auto. split; auto. 
            apply symS in Q5. apply (in_set_right_congruence S r symS tranS z2 y1 Z Q5). exact Q2. 
Qed. 


Lemma bop_intersect_lift_right_distributive
       (inj : bop_injective S r bS): 
        bop_right_distributive (finite_set S) (brel_set r) (bop_intersect r) (bop_lift r bS). 
Proof. intros X Y Z. 
       apply brel_set_intro_prop; auto.
       split; intros a H.        
          + apply in_set_bop_intersect_intro; auto. 
            apply in_set_bop_lift_elim in H;
            auto. destruct H as [ x [ y [[P1 P2] P3]]].
            apply in_set_bop_intersect_elim in P1; auto.
            destruct P1 as [P1 P4]. split. 
            ++ apply symS in P3. apply (in_set_right_congruence S r symS tranS (bS x y) a ((bop_lift r bS Y X)) P3).
               apply in_set_bop_lift_intro; auto. 
            ++ apply symS in P3. apply (in_set_right_congruence S r symS tranS (bS x y) a ((bop_lift r bS Z X)) P3).
               apply in_set_bop_lift_intro; auto. 
          + apply in_set_bop_intersect_elim in H; auto.
            destruct H as [H1 H2].
            apply in_set_bop_lift_elim in H1; auto. destruct H1 as [ x1 [ y1 [[P1 P2] P3]]].
            apply in_set_bop_lift_elim in H2; auto. destruct H2 as [ x2 [ z2 [[Q1 Q2] Q3]]].
            apply symS in P3. assert (P4 := tranS _ _ _ P3 Q3).
            destruct (inj _ _ _ _ P4) as [Q4 Q5].
            apply (in_set_right_congruence S r symS tranS (bS x1 y1) a (bop_lift r bS (bop_intersect r Y Z) X) P3).
            apply in_set_bop_lift_intro; auto.
            apply in_set_bop_intersect_intro; auto. split; auto. 
            apply symS in Q4. apply (in_set_right_congruence S r symS tranS x2 x1 Z Q4). exact Q1. 
Qed. 


Lemma bops_intersect_lift_not_left_left_absorptive (X Y : finite_set S) : 
  bops_not_left_left_absorptive (finite_set S) (brel_set r) (bop_intersect r) (bop_lift r bS).
Proof. exists (wS::nil, nil). compute. reflexivity. Defined. 

Lemma bops_intersect_lift_not_left_right_absorptive (X Y : finite_set S) : 
  bops_not_left_right_absorptive (finite_set S) (brel_set r) (bop_intersect r) (bop_lift r bS).
Proof. exists (wS::nil, nil). compute. reflexivity. Defined. 

Lemma bops_intersect_lift_not_right_left_absorptive (X Y : finite_set S) : 
  bops_not_right_left_absorptive (finite_set S) (brel_set r) (bop_intersect r) (bop_lift r bS).
Proof. exists (wS::nil, nil). compute. reflexivity. Defined. 

Lemma bops_intersect_lift_not_right_right_absorptive (X Y : finite_set S) : 
  bops_not_right_right_absorptive (finite_set S) (brel_set r) (bop_intersect r) (bop_lift r bS).
Proof. exists (wS::nil, nil). compute. reflexivity. Defined. 




Lemma bops_lift_union_id_equals_ann_decide 
      (fin_d : carrier_is_finite_decidable S r):
  exists_id_ann_decidable (finite_set S) (brel_set r) (bop_intersect r) (bop_lift r bS).
Proof. destruct fin_d as [finP | nfinP].
       + assert (A : bops_exists_id_ann_not_equal (finite_set S) (brel_set r) (bop_intersect r) (bop_lift r bS)).
         assert (B := bop_intersect_enum_is_id S r refS symS tranS finP).
         unfold carrier_is_finite in finP. destruct finP as [fn P]. simpl in B. 
         exists (fn tt, nil). split. split.
         ++ exact B. 
         ++ apply bop_lift_nil_is_ann. 
         ++ assert (C := P wS).
            case_eq(brel_set r (fn tt) nil); intro D; auto.
            apply brel_set_elim_prop in D; auto. destruct D as [D E].
            assert (F : in_set r (fn tt) wS = true). admit.

            assert (G := D wS F). compute in G. discriminate G.
         ++ exact (Id_Ann_Proof_Not_Equal _ _ _ _ A).
       + exact (Id_Ann_Proof_None_Ann _ _ _ _ 
                   (bop_intersect_not_exists_id S r refS symS tranS nfinP,
                    bop_lift_exists_ann S r bS)                  
               ).
Admitted. 

Lemma bops_lift_intersect_id_equals_ann_decide 
      (id_d : bop_exists_id_decidable S r bS) :
  exists_id_ann_decidable (finite_set S) (brel_set r) (bop_lift r bS) (bop_intersect r).
Proof. destruct id_d as [idP | nidP]. 
       + assert (A : bops_exists_id_ann_not_equal (finite_set S) (brel_set r) (bop_lift r bS) (bop_intersect r)).
         destruct idP as [id P].
         exists (id :: nil, nil). split. split. 
         ++ apply bop_lift_is_id; auto. 
         ++ apply bop_intersect_nil_is_ann; auto. 
         ++ compute. reflexivity. 
         ++  exact (Id_Ann_Proof_Not_Equal _ _ _ _ A). 
       + exact (Id_Ann_Proof_None_Ann _ _ _ _ 
                  (bop_lift_not_exists_id S r bS refS tranS symS wS nidP, 
                   bop_intersect_exists_ann S r refS symS tranS)).               
Defined.  



End Theory. 
(*
Section ACAS.

Section Proofs.   

Variables (S : Type)
          (eqvS : A_eqv S)
          (bS : binary_op S)
          (sgS : sg_proofs S (A_eqv_eq _ eqvS) bS).

Definition id_ann_proofs_union_lift 
      (id_d : bop_exists_id_decidable S (A_eqv_eq _ eqvS) bS)
      (fin_d : carrier_is_finite_decidable S (A_eqv_eq _ eqvS)) :
  id_ann_proofs
            (finite_set S)
            (brel_set (A_eqv_eq _ eqvS))
            (bop_intersect (A_eqv_eq _ eqvS))
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
  A_id_ann_plus_times_d := Id_Ann_Proof_Equal _ _ _ _ (bops_union_lift_id_equals_ann S eq bS refS symS trnS)
; A_id_ann_times_plus_d := bops_lift_union_id_equals_ann_decide S eq wS f ntS bS refS symS trnS bcong id_d fin_d 
|}. 



Definition bs_proofs_union_lift : 
  bs_proofs (finite_set S) (brel_set (A_eqv_eq _ eqvS)) (bop_intersect (A_eqv_eq _ eqvS)) (bop_lift (A_eqv_eq _ eqvS) bS) :=
let eqvP := A_eqv_proofs _ eqvS in
let rS   := A_eqv_eq _ eqvS in  
let refS := A_eqv_reflexive S rS eqvP  in
let symS := A_eqv_symmetric S rS eqvP  in
let trnS := A_eqv_transitive S rS eqvP in
let cnbS := A_sg_congruence S rS bS sgS in
let ilD  := A_sg_is_left_d S rS bS sgS in  
let irD  := A_sg_is_right_d S rS bS sgS in  
{|
  A_bs_left_distributive_d      := inl (bop_intersect_lift_left_distributive S rS bS refS symS trnS cnbS)
; A_bs_right_distributive_d     := inl (bop_intersect_lift_right_distributive S rS bS refS symS trnS cnbS)
; A_bs_left_left_absorptive_d   := bops_union_lift_left_left_absorptive_decide S rS bS refS symS trnS cnbS ilD 
; A_bs_left_right_absorptive_d  := bops_union_lift_left_right_absorptive_decide S rS bS refS symS trnS cnbS irD 
; A_bs_right_left_absorptive_d  := bops_union_lift_right_left_absorptive_decide S rS bS refS symS trnS cnbS ilD 
; A_bs_right_right_absorptive_d := bops_union_lift_right_right_absorptive_decide S rS bS refS symS trnS cnbS irD
|}.



Definition bops_lift_union_id_equals_ann_certify 
      (id_d  : @check_exists_id S)
      (fin_d : @check_is_finite S): @exists_id_ann_certificate (finite_set S) := 
match id_d with
| Certify_Exists_Id id =>
  match fin_d with
  | Certify_Is_Finite h  => Id_Ann_Cert_Not_Equal (id :: nil, h tt)
  | _                    => Id_Ann_Cert_Id_None (id :: nil) 
  end 
| _ =>
  match fin_d with
  | Certify_Is_Finite h  => Id_Ann_Cert_None_Ann (h tt)    
  | _                    => Id_Ann_Cert_None
  end 
end .


End Proofs.   

Section Combinators.



Definition A_bs_union_lift (S : Type) (sgS : A_sg S) : A_bs (finite_set S) := 
let eqvS  := A_sg_eqv S sgS in
let rS    := A_eqv_eq S eqvS in   
let bS    := A_sg_bop S sgS in
let eqvP := A_eqv_proofs S eqvS in
let s     := A_eqv_witness S eqvS in
let f     := A_eqv_new S eqvS in
let Pf    := A_eqv_not_trivial S eqvS in 
{| 
     A_bs_eqv           := A_eqv_set S eqvS
   ; A_bs_plus          := bop_intersect rS
   ; A_bs_times         := bop_lift rS bS
   ; A_bs_id_ann_proofs := id_ann_proofs_union_lift S eqvS bS (A_sg_proofs S sgS) (A_sg_exists_id_d S sgS) (A_eqv_finite_d S eqvS)
   ; A_bs_plus_proofs   := A_sg_proofs_from_sg_CI_proofs
                                (finite_set S)
                                (brel_set rS)
                                (bop_intersect rS)
                                (s :: nil)
                                (λ (l : finite_set S), if brel_set rS nil l then (s :: nil) else nil) (* fix someday *) 
                                (brel_set_not_trivial S rS s)
                                (eqv_proofs_set S  rS eqvP) 
                                (sg_CI_proofs_union eqvS)
   ; A_bs_times_proofs  := sg_lift_proofs S rS bS eqvP s f Pf (A_eqv_exactly_two_d _ eqvS) (A_sg_proofs S sgS)
   ; A_bs_proofs        := bs_proofs_union_lift S eqvS bS (A_sg_proofs S sgS)
   ; A_bs_ast           := Ast_bs_union_lift (A_sg_ast S sgS)
|}.

End Combinators.   

End ACAS.

Section AMCAS.

Open Scope string_scope.

Definition A_mcas_bs_union_lift (S : Type) (A : A_sg_mcas S) : A_bs_mcas (finite_set S) :=
match A_sg_mcas_cast_up _ A with
| A_MCAS_sg _ B         => A_bs_classify _ (A_BS_bs _ (A_bs_union_lift _ B))
| A_MCAS_sg_Error _ sl  => A_BS_Error _ sl
| _                     => A_BS_Error _ ("Internal Error : mcas_bs_union_lift_with_one" :: nil)
end.

End AMCAS.




Section CAS.


Section Checks.   

Definition bops_union_lift_left_left_absorptive_check {S : Type} (ilD : @check_is_left S) : @check_left_left_absorptive (finite_set S) :=
match ilD with
| Certify_Is_Left              => Certify_Left_Left_Absorptive
| Certify_Not_Is_Left (s1, s2) => Certify_Not_Left_Left_Absorptive ((s1 :: nil), (s2 :: nil))
end. 

Definition bops_union_lift_left_right_absorptive_check {S : Type} (ilD : @check_is_right S) : @check_left_right_absorptive (finite_set S) :=
match ilD with
| Certify_Is_Right              => Certify_Left_Right_Absorptive
| Certify_Not_Is_Right (s1, s2) => Certify_Not_Left_Right_Absorptive ((s2 :: nil), (s1 :: nil))
end. 


Definition bops_union_lift_right_left_absorptive_check {S : Type} (ilD : @check_is_left S) :@check_right_left_absorptive (finite_set S) :=
match ilD with
| Certify_Is_Left              => Certify_Right_Left_Absorptive
| Certify_Not_Is_Left (s1, s2) => Certify_Not_Right_Left_Absorptive ((s1 :: nil), (s2 :: nil))
end. 

Definition bops_union_lift_right_right_absorptive_check {S : Type} (ilD : @check_is_right S) : @check_right_right_absorptive (finite_set S) :=
match ilD with
| Certify_Is_Right              => Certify_Right_Right_Absorptive
| Certify_Not_Is_Right (s1, s2) => Certify_Not_Right_Right_Absorptive ((s2 :: nil), (s1 :: nil))
end.

End Checks. 


Section Proofs. 

Definition bs_certs_union_lift {S : Type} (sgS : @sg_certificates S) : @bs_certificates (finite_set S) := 
let ilD  := sg_is_left_d sgS in  
let irD  := sg_is_right_d sgS in  
{|
  bs_left_distributive_d      := Certify_Left_Distributive 
; bs_right_distributive_d     := Certify_Right_Distributive 
; bs_left_left_absorptive_d   := bops_union_lift_left_left_absorptive_check ilD 
; bs_left_right_absorptive_d  := bops_union_lift_left_right_absorptive_check irD 
; bs_right_left_absorptive_d  := bops_union_lift_right_left_absorptive_check ilD 
; bs_right_right_absorptive_d := bops_union_lift_right_right_absorptive_check irD
|}.



Definition id_ann_certs_union_lift {S : Type} 
      (id_d : @check_exists_id S)
      (fin_d : @check_is_finite S) : @id_ann_certificates (finite_set S) := 
{|
  id_ann_plus_times_d := Id_Ann_Cert_Equal nil 
; id_ann_times_plus_d := bops_lift_union_id_equals_ann_certify S id_d fin_d 
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
   ; bs_plus          := bop_intersect rS
   ; bs_times         := bop_lift rS bS
   ; bs_id_ann_certs  := id_ann_certs_union_lift (sg_exists_id_d sgS) (eqv_finite_d eqvS)
   ; bs_plus_certs    := sg_certs_from_sg_CI_certs
                                (finite_set S)
                                (brel_set rS)
                                (bop_intersect rS)
                                (s :: nil)
                                (λ (l : finite_set S), if brel_set rS nil l then (s :: nil) else nil) (* fix someday *) 
                                (sg_CI_certs_union eqvS)
   ; bs_times_certs  := sg_lift_certs S rS s f  (eqv_exactly_two_d eqvS) bS (sg_certs sgS)
   ; bs_certs        := bs_certs_union_lift (sg_certs sgS)
   ; bs_ast          := Ast_bs_union_lift (sg_ast sgS)
|}.

End Combinators.   

End CAS.

Section AMCAS.

Open Scope string_scope.

Definition mcas_bs_union_lift  {S : Type} (A : @sg_mcas S) : @bs_mcas (finite_set S) :=
match sg_mcas_cast_up _ A with
| MCAS_sg B         => bs_classify (BS_bs (bs_union_lift B))
| MCAS_sg_Error sl  => BS_Error sl
| _                 => BS_Error ("Internal Error : mcas_bs_union_lift" :: nil)
end.

End AMCAS.


Section Verify.


Lemma correct_bops_union_lift_left_left_absorptive_check 
  (S : Type)
  (eq : brel S)
  (refS : brel_reflexive S eq)
  (symS : brel_symmetric S eq)
  (trnS : brel_transitive S eq)     
  (bS : binary_op S)
  (cong : bop_congruence S eq bS)
  (il_d : bop_is_left_decidable S eq bS) : 
  p2c_left_left_absorptive (finite_set S) (brel_set eq) (bop_intersect eq) (bop_lift eq bS)
                           (bops_union_lift_left_left_absorptive_decide S eq bS refS symS trnS cong il_d)
  =                                                                               
  bops_union_lift_left_left_absorptive_check (p2c_is_left_check S eq bS il_d).
Proof. destruct il_d as [IL | [ [s1 s2] NIL ]]; simpl; reflexivity. Qed. 

Lemma correct_bops_union_lift_left_right_absorptive_check 
  (S : Type)
  (eq : brel S)
  (refS : brel_reflexive S eq)
  (symS : brel_symmetric S eq)
  (trnS : brel_transitive S eq)     
  (bS : binary_op S)
  (cong : bop_congruence S eq bS)
  (ir_d : bop_is_right_decidable S eq bS):
  p2c_left_right_absorptive (finite_set S) (brel_set eq) (bop_intersect eq) (bop_lift eq bS)
                            (bops_union_lift_left_right_absorptive_decide S eq bS refS symS trnS cong ir_d)
  =
  bops_union_lift_left_right_absorptive_check (p2c_is_right_check S eq bS ir_d).
Proof. destruct ir_d as [IR | [ [s1 s2] NIR ]]; simpl; reflexivity. Qed. 

Lemma correct_bops_union_lift_right_left_absorptive_check 
  (S : Type)
  (eq : brel S)
  (refS : brel_reflexive S eq)
  (symS : brel_symmetric S eq)
  (trnS : brel_transitive S eq)     
  (bS : binary_op S)
  (cong : bop_congruence S eq bS)
  (il_d : bop_is_left_decidable S eq bS) : 
  p2c_right_left_absorptive (finite_set S) (brel_set eq) (bop_intersect eq) (bop_lift eq bS)
                            (bops_union_lift_right_left_absorptive_decide S eq bS refS symS trnS cong  il_d)
  =
  bops_union_lift_right_left_absorptive_check (p2c_is_left_check S eq bS il_d).
Proof. destruct il_d as [IL | [ [s1 s2] NIL ]]; simpl; reflexivity. Qed. 

Lemma correct_bops_union_lift_right_right_absorptive_check 
  (S : Type)
  (eq : brel S)
  (refS : brel_reflexive S eq)
  (symS : brel_symmetric S eq)
  (trnS : brel_transitive S eq)     
  (bS : binary_op S)
  (cong : bop_congruence S eq bS)
  (ir_d : bop_is_right_decidable S eq bS):
  p2c_right_right_absorptive (finite_set S) (brel_set eq) (bop_intersect eq) (bop_lift eq bS)
                             (bops_union_lift_right_right_absorptive_decide S eq bS refS symS trnS cong ir_d) 
  =                                      
  bops_union_lift_right_right_absorptive_check (p2c_is_right_check S eq bS ir_d). 
Proof. destruct ir_d as [IR | [ [s1 s2] NIR ]]; simpl; reflexivity. Qed. 


Lemma correct_bs_certs_union_lift
  (S : Type) (bS : binary_op S) (eqvS : A_eqv S) (sgP : sg_proofs S (A_eqv_eq S eqvS) bS) : 
  P2C_bs _ _ _ _ (bs_proofs_union_lift S eqvS bS sgP)
  = 
  bs_certs_union_lift (P2C_sg S (A_eqv_eq S eqvS) bS sgP).
Proof. destruct sgP. unfold bs_proofs_union_lift, bs_certs_union_lift, P2C_sg, P2C_bs; simpl.
       destruct A_sg_is_left_d as [L | [[a b] NL]]; destruct A_sg_is_right_d as [R | [[c d] NR]]; simpl; reflexivity. 
Qed.

Lemma correct_id_ann_certs_union_lift
      (S : Type)
      (eqvS : A_eqv S)
      (bS : binary_op S)
      (id_d : bop_exists_id_decidable S (A_eqv_eq S eqvS) bS)
      (sgP : sg_proofs S (A_eqv_eq S eqvS) bS) :
      id_ann_certs_union_lift (p2c_exists_id_check _ _ _ id_d) (p2c_is_finite_check _ _ (A_eqv_finite_d _ eqvS)) 
      = 
      P2C_id_ann (finite_set S) (brel_set (A_eqv_eq _ eqvS)) (bop_intersect (A_eqv_eq _ eqvS)) (bop_lift (A_eqv_eq _ eqvS) bS)
                 (id_ann_proofs_union_lift S eqvS bS sgP id_d (A_eqv_finite_d _ eqvS)).
Proof.   unfold id_ann_certs_union_lift, id_ann_proofs_union_lift, P2C_id_ann, p2c_is_finite_check, p2c_exists_id_check; simpl.
         destruct id_d as [[id idP] | nidP]; destruct (A_eqv_finite_d _ eqvS) as [[h finP] | nfinP]; simpl; 
         try reflexivity. 
Qed.


Theorem correct_bs_union_lift (S : Type) (sgS: A_sg S):  
   bs_union_lift (A2C_sg S sgS)
   =
   A2C_bs _ (A_bs_union_lift S sgS). 
Proof. unfold bs_union_lift, bs_union_lift, A2C_bs, A2C_sg. destruct sgS. simpl.
       rewrite correct_eqv_set.              
       rewrite correct_sg_lift_certs.
       rewrite <- correct_bs_certs_union_lift.              
       rewrite <- correct_id_ann_certs_union_lift.
       rewrite correct_bop_intersect_certs.
       unfold sg_certs_from_sg_CI_certs, A_sg_proofs_from_sg_CI_proofs.
       rewrite <- correct_sg_certs_from_sg_C_certs.               
       rewrite <- correct_sg_C_certs_from_sg_CI_certs.
       reflexivity.
Qed.


Theorem correct_mcas_bs_union_lift (S : Type) (sgS : A_sg_mcas S) : 
         mcas_bs_union_lift (A2C_mcas_sg S sgS)  
         = 
         A2C_mcas_bs _ (A_mcas_bs_union_lift _ sgS).
Proof. unfold mcas_bs_union_lift, A_mcas_bs_union_lift. 
       rewrite correct_sg_mcas_cast_up.       
       destruct (A_sg_cas_up_is_error_or_sg S sgS) as [[l1 A] | [s1 A]]. 
       + rewrite A; simpl. reflexivity. 
       + rewrite A; simpl. rewrite correct_bs_union_lift. 
         apply correct_bs_classify_bs. 
Qed. 


End Verify. 


*)
