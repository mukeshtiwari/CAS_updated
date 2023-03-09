Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool. 

Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.

Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.eqv.product.

Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures.
Require Import CAS.coq.sg.product.

Require Import CAS.coq.bs.properties.
Require Import CAS.coq.bs.structures.
Require Import CAS.coq.bs.cast.
Require Import CAS.coq.bs.classify. 



Section Theory. 

Variable S  : Type. 
Variable T  : Type. 
Variable rS : brel S. 
Variable rT : brel T.
Variable wS : S.
Variable wT : T.
Variable addS  mulS : binary_op S. 
Variable addT mulT : binary_op T. 

Notation "a =S b"  := (rS a b = true) (at level 15).
Notation "a =T b"  := (rT a b = true) (at level 15).
Notation "a +S b"  := (addS a b) (at level 15).
Notation "a +T b"  := (addT a b) (at level 15).
Notation "a *S b"  := (mulS a b) (at level 15).
Notation "a *T b"  := (mulT a b) (at level 15).

Notation "a <*> b" := (brel_product a b) (at level 15).
Notation "a [*] b" := (bop_product a b) (at level 15).



(* note : should be able to abstract away and universally quantfied predicate .... *) 

Lemma A_bs_product_left_distributive : 
      A_bs_left_distributive rS addS mulS → 
      A_bs_left_distributive rT addT mulT → 
         A_bs_left_distributive (rS <*> rT) (addS [*] addT) (mulS [*] mulT). 
Proof. intros ldS ldT [s1 t1] [s2 t2] [s3 t3]. simpl. rewrite ldS, ldT.  simpl. reflexivity. Defined. 

Lemma A_bs_product_not_left_distributive_left : 
      A_bs_not_left_distributive rS addS mulS → 
         A_bs_not_left_distributive (rS <*> rT) (addS [*] addT) (mulS [*] mulT). 
Proof. intros [ [s1 [s2 s3 ] ] nd ]. exists ((s1, wT), ((s2, wT), (s3, wT))). simpl.        
       rewrite nd.  simpl. reflexivity. 
Defined. 

Lemma A_bs_product_not_left_distributive_right : 
      A_bs_not_left_distributive rT addT mulT → 
         A_bs_not_left_distributive (rS <*> rT) (addS [*] addT) (mulS [*] mulT). 
Proof. intros [ [t1 [t2 t3 ] ] nd ]. exists ((wS, t1), ((wS, t2), (wS, t3))). simpl. 
       rewrite nd.  simpl. apply andb_comm. 
Defined.

Definition A_bs_product_left_distributive_decide 
  (dS : @A_bs_left_distributive_decidable S rS addS mulS)
  (dT : @A_bs_left_distributive_decidable T rT addT mulT) : 
        @A_bs_left_distributive_decidable (S * T) (rS <*> rT) (addS [*] addT) (mulS [*] mulT) := 
   match dS with 
   | inl ldS => 
     match dT with 
     | inl ldT  => inl _ (A_bs_product_left_distributive ldS ldT)
     | inr nldT => inr _ (A_bs_product_not_left_distributive_right nldT)
     end 
   | inr nldS   => inr _ (A_bs_product_not_left_distributive_left nldS)
   end. 

Lemma A_bs_product_right_distributive : 
      A_bs_right_distributive rS addS mulS → 
      A_bs_right_distributive rT addT mulT → 
         A_bs_right_distributive (rS <*> rT) (addS [*] addT) (mulS [*] mulT). 
Proof. intros lrS lrT [s1 t1] [s2 t2] [s3 t3]. simpl. rewrite lrS, lrT.  simpl. reflexivity. Defined. 


Lemma A_bs_product_not_right_distributive_left : 
      A_bs_not_right_distributive rS addS mulS → 
         A_bs_not_right_distributive (rS <*> rT) (addS [*] addT) (mulS [*] mulT). 
Proof. intros [ [s1 [s2 s3 ] ] nd ].
       exists ((s1, wT), ((s2, wT), (s3, wT))). simpl. 
       rewrite nd.  simpl. reflexivity. 
Defined. 

Lemma A_bs_product_not_right_distributive_right : 
      A_bs_not_right_distributive rT addT mulT → 
         A_bs_not_right_distributive (rS <*> rT) (addS [*] addT) (mulS [*] mulT). 
Proof. intros [ [t1 [t2 t3] ] nd ]. exists ((wS, t1), ((wS, t2), (wS, t3))). simpl. 
       rewrite nd.  simpl. apply andb_comm. 
Defined. 

Definition A_bs_product_right_distributive_decide : 
  A_bs_right_distributive_decidable rS addS mulS ->
  A_bs_right_distributive_decidable rT addT mulT -> 
       A_bs_right_distributive_decidable (rS <*> rT) (addS [*] addT) (mulS [*] mulT)
:= λ dS dT,  
   match dS with 
   | inl ldS => 
     match dT with 
     | inl ldT  => inl _ (A_bs_product_right_distributive ldS ldT)
     | inr nldT => inr _ (A_bs_product_not_right_distributive_right nldT)
     end 
   | inr nldS   => inr _ (A_bs_product_not_right_distributive_left nldS)
   end. 


(* absorption *) 
Lemma A_bs_product_left_absorptive : 
      A_bs_left_absorptive rS addS mulS → 
      A_bs_left_absorptive rT addT mulT → 
         A_bs_left_absorptive (rS <*> rT) (addS [*] addT) (mulS [*] mulT). 
Proof. intros ldS ldT [s1 t1] [s2 t2]. simpl. rewrite ldS, ldT.  simpl. reflexivity. Defined. 


Lemma A_bs_product_not_left_absorptive_left : 
      A_bs_not_left_absorptive rS addS mulS → 
         A_bs_not_left_absorptive (rS <*> rT) (addS [*] addT) (mulS [*] mulT). 
Proof. intros [ [s1 s2] P ]. exists ((s1, wT), (s2, wT)). simpl. rewrite P. simpl. reflexivity. Defined. 

Lemma A_bs_product_not_left_absorptive_right : 
      A_bs_not_left_absorptive rT addT mulT → 
         A_bs_not_left_absorptive (rS <*> rT) (addS [*] addT) (mulS [*] mulT). 
Proof. intros [ [t1 t2] P ]. exists ((wS, t1), (wS, t2)). simpl. rewrite P. simpl. apply andb_comm.  Defined. 


Definition A_bs_product_left_absorptive_decide 
  (laS_d : A_bs_left_absorptive_decidable rS addS mulS)
  (laT_d : A_bs_left_absorptive_decidable rT addT mulT) : 
         A_bs_left_absorptive_decidable (rS <*> rT) (addS [*] addT) (mulS [*] mulT) := 
match laS_d with 
|inl laS =>
   match laT_d with 
   |inl laT     => inl _ (A_bs_product_left_absorptive laS laT)
   |inr not_laT => inr _ (A_bs_product_not_left_absorptive_right not_laT) 
   end 
|inr not_laS => inr _ (A_bs_product_not_left_absorptive_left not_laS ) 
end. 


Lemma A_bs_product_right_absorptive : 
      A_bs_right_absorptive rS addS mulS → 
      A_bs_right_absorptive rT addT mulT → 
         A_bs_right_absorptive (rS <*> rT) (addS [*] addT) (mulS [*] mulT). 
Proof. intros ldS ldT [s1 t1] [s2 t2]. simpl. rewrite ldS, ldT.  simpl. reflexivity. Defined. 

Lemma A_bs_product_not_right_absorptive_left : 
      A_bs_not_right_absorptive rS addS mulS → 
         A_bs_not_right_absorptive (rS <*> rT) (addS [*] addT) (mulS [*] mulT). 
Proof. intros [ [s1 s2] P ]. exists ((s1, wT), (s2, wT)). simpl. rewrite P. simpl. reflexivity. Defined. 

Lemma A_bs_product_not_right_absorptive_right : 
      A_bs_not_right_absorptive rT addT mulT → 
         A_bs_not_right_absorptive (rS <*> rT) (addS [*] addT) (mulS [*] mulT). 
Proof. intros [ [t1 t2] P ]. exists ((wS, t1), (wS, t2)). simpl. rewrite P. simpl. apply andb_comm.  Defined. 


Definition A_bs_product_right_absorptive_decide 
  (laS_d : A_bs_right_absorptive_decidable rS addS mulS)
  (laT_d : A_bs_right_absorptive_decidable rT addT mulT): 
         A_bs_right_absorptive_decidable (rS <*> rT) (addS [*] addT) (mulS [*] mulT) := 
match laS_d with 
|inl laS =>
   match laT_d with 
   |inl laT     => inl _ (A_bs_product_right_absorptive laS laT)
   |inr not_laT => inr _ (A_bs_product_not_right_absorptive_right not_laT) 
   end 
|inr not_laS => inr _ (A_bs_product_not_right_absorptive_left not_laS ) 
end.


(* identities, annihilators *)

Lemma A_bs_product_exists_id_ann_equal : 
      A_bs_exists_id_ann_equal rS addS mulS → 
      A_bs_exists_id_ann_equal rT addT mulT → 
      A_bs_exists_id_ann_equal (rS <*> rT) (addS [*] addT) (mulS [*] mulT). 
Proof. intros [iS [piS paS]]  [iT [piT paT]].
       exists (iS, iT). split.
       apply bop_product_is_id; auto.
       apply bop_product_is_ann; auto. 
Defined.

Lemma A_bs_product_exists_id_ann_not_equal_v1 : 
      A_bs_exists_id_ann_not_equal rS addS mulS →  
      A_bs_exists_id_ann_equal rT addT mulT → 
      A_bs_exists_id_ann_not_equal (rS <*> rT) (addS [*] addT) (mulS [*] mulT). 
Proof. intros [[iS aS] [[piS paS] iS_not_aS]]  [iT [piT paT]].
       exists ((iS, iT), (aS, iT)). split. split. 
       apply bop_product_is_id; auto.
       apply bop_product_is_ann; auto. 
       compute. rewrite iS_not_aS. reflexivity. 
Defined. 

Lemma A_bs_product_exists_id_ann_not_equal_v2: 
      A_bs_exists_id_ann_equal rS addS mulS →   
      A_bs_exists_id_ann_not_equal rT addT mulT → 
      A_bs_exists_id_ann_not_equal (rS <*> rT) (addS [*] addT) (mulS [*] mulT). 
Proof. intros [iS [piS paS]]  [[iT aT] [[piT paT] iT_not_aT]].
       exists ((iS, iT), (iS, aT)). split. split. 
       apply bop_product_is_id; auto.
       apply bop_product_is_ann; auto. 
       compute. rewrite iT_not_aT.
       case_eq(rS iS iS); intro A; reflexivity. 
Defined.

Lemma A_bs_product_exists_id_ann_not_equal_v3 : 
      A_bs_exists_id_ann_not_equal rS addS mulS →   
      A_bs_exists_id_ann_not_equal rT addT mulT → 
      A_bs_exists_id_ann_not_equal (rS <*> rT) (addS [*] addT) (mulS [*] mulT). 
Proof. intros [[iS aS] [[piS paS] iS_not_aS]]  [[iT aT] [[piT paT] iT_not_aT]].
       exists ((iS, iT), (aS, aT)). split. split. 
       apply bop_product_is_id; auto.
       apply bop_product_is_ann; auto. 
       compute. rewrite iS_not_aS. reflexivity. 
Defined. 


End Theory.

Section ACAS.

Definition A_bs_product_exists_id_ann_decide
           (S T : Type) (eqS : brel S) (eqT : brel T)
           (bS1 bS2 : binary_op S)
           (bT1 bT2 : binary_op T)           
           (PS : A_bs_exists_id_ann_decidable eqS bS1 bS2)
           (PT : A_bs_exists_id_ann_decidable eqT bT1 bT2) :
           A_bs_exists_id_ann_decidable 
                                   (brel_product eqS eqT)
                                   (bop_product bS1 bT1)
                                   (bop_product bS2 bT2) :=
let F0 := bop_product_exists_id S T eqS eqT bS1 bT1      in
let F1 := bop_product_not_exists_id S T eqS eqT bS1 bT1  in  

let F3 := bop_product_exists_ann S T eqS eqT bS2 bT2     in 
let F2 := bop_product_not_exists_ann S T eqS eqT bS2 bT2 in

let F4 := A_bs_product_exists_id_ann_equal S T eqS eqT bS1 bS2 bT1 bT2 in 
let F5 := A_bs_product_exists_id_ann_not_equal_v2 S T eqS eqT bS1 bS2 bT1 bT2 in 
let F6 := A_bs_product_exists_id_ann_not_equal_v1 S T eqS eqT bS1 bS2 bT1 bT2 in
let F7 := A_bs_product_exists_id_ann_not_equal_v3 S T eqS eqT bS1 bS2 bT1 bT2 in 

let E5 := A_extract_exist_id_from_exists_id_ann_equal eqS bS1 bS2 in
let E1 := A_extract_exist_id_from_exists_id_ann_equal eqT bT1 bT2 in 

let E6 := A_extract_exist_ann_from_exists_id_ann_equal eqS bS1 bS2 in
let E3 := A_extract_exist_ann_from_exists_id_ann_equal eqT bT1 bT2 in

let E7 := A_extract_exist_id_from_exists_id_ann_not_equal eqS bS1 bS2 in
let E2 := A_extract_exist_id_from_exists_id_ann_not_equal eqT bT1 bT2 in 

let E8 := A_extract_exist_ann_from_exists_id_ann_not_equal eqS bS1 bS2 in 
let E4 := A_extract_exist_ann_from_exists_id_ann_not_equal eqT bT1 bT2 in

match PS with 
| A_Id_Ann_None _ _ _ (nidS, nannS)               =>
     A_Id_Ann_None _ _ _ (F1 (inl nidS), F2 (inl nannS))
| A_Id_Ann_Id_None _ _ _ (idS, nannS) =>
  match PT with 
  | A_Id_Ann_None _ _ _ (nidT, nannT)             =>
       A_Id_Ann_None _ _ _ (F1 (inr nidT), F2 (inl nannS))           
  | A_Id_Ann_Id_None _ _ _ (idT, nannT)           =>
       A_Id_Ann_Id_None _ _ _ (F0 idS idT, F2 (inl nannS))
  | A_Id_Ann_None_Ann _ _ _ (nidT, annT)          =>
       A_Id_Ann_None _ _ _ (F1 (inr nidT), F2 (inl nannS))                     
  | A_Id_Ann_Equal _ _ _ (idT_annT_equal)         =>
       A_Id_Ann_Id_None _ _ _ (F0 idS (E1 idT_annT_equal), F2 (inl nannS))              
  | A_Id_Ann_Not_Equal _ _ _ (idT_annT_not_equal) =>
       A_Id_Ann_Id_None _ _ _ (F0 idS (E2 idT_annT_not_equal), F2 (inl nannS))              
  end   
| A_Id_Ann_None_Ann _ _ _ (nidS, annS) =>
  match PT with 
  | A_Id_Ann_None _ _ _ (nidT, nannT)             =>
       A_Id_Ann_None _ _ _ (F1 (inl nidS),F2 (inr nannT))           
  | A_Id_Ann_Id_None _ _ _ (idT, nannT)           =>
       A_Id_Ann_None _ _ _ (F1 (inl nidS), F2 (inr nannT))                         
  | A_Id_Ann_None_Ann _ _ _ (nidT, annT)          =>
       A_Id_Ann_None_Ann _ _ _ (F1 (inl nidS), F3 annS annT)                      
  | A_Id_Ann_Equal _ _ _ (idT_annT_equal)         =>
       A_Id_Ann_None_Ann _ _ _ (F1 (inl nidS), F3 annS (E3 idT_annT_equal))  
  | A_Id_Ann_Not_Equal _ _ _ (idT_annT_not_equal) =>
       A_Id_Ann_None_Ann _ _ _ (F1 (inl nidS), F3 annS (E4 idT_annT_not_equal))   
  end   
| A_Id_Ann_Equal _ _ _ (idS_annS_equal)  =>
  match PT with 
  | A_Id_Ann_None _ _ _ (nidT, nannT)             =>
       A_Id_Ann_None _ _ _ (F1 (inr nidT), F2 (inr nannT))                      
  | A_Id_Ann_Id_None _ _ _ (idT, nannT)           =>
       A_Id_Ann_Id_None _ _ _ (F0 (E5 idS_annS_equal) idT, F2 (inr nannT))
  | A_Id_Ann_None_Ann _ _ _ (nidT, annT)          =>
       A_Id_Ann_None_Ann _ _ _ (F1 (inr nidT), F3 (E6 idS_annS_equal) annT)
  | A_Id_Ann_Equal _ _ _ (idT_annT_equal)         =>
       A_Id_Ann_Equal _ _ _ (F4 idS_annS_equal idT_annT_equal)
  | A_Id_Ann_Not_Equal _ _ _ (idT_annT_not_equal) =>
       A_Id_Ann_Not_Equal _ _ _ (F5 idS_annS_equal idT_annT_not_equal)
  end   
| A_Id_Ann_Not_Equal _ _ _ (idS_annS_not_equal)  =>
  match PT with 
  | A_Id_Ann_None _ _ _ (nidT, nannT)             =>
       A_Id_Ann_None _ _ _ (F1 (inr nidT), F2 (inr nannT))             
  | A_Id_Ann_Id_None _ _ _ (idT, nannT)           =>
    A_Id_Ann_Id_None _ _ _ (F0 (E7 idS_annS_not_equal) idT, F2 (inr nannT))                    
  | A_Id_Ann_None_Ann _ _ _ (nidT, annT)          =>
       A_Id_Ann_None_Ann _ _ _ (F1 (inr nidT), F3 (E8 idS_annS_not_equal) annT)
  | A_Id_Ann_Equal _ _ _ (idT_annT_equal)         =>
       A_Id_Ann_Not_Equal _ _ _ (F6 idS_annS_not_equal idT_annT_equal)
  | A_Id_Ann_Not_Equal _ _ _ (idT_annT_not_equal) =>
       A_Id_Ann_Not_Equal _ _ _ (F7 idS_annS_not_equal idT_annT_not_equal)
  end   
end. 
  
(* pay attention to order of arguement!  ;-) *) 
Definition A_bs_product_id_ann_properties 
 {S T: Type} 
 (rS : brel S) 
 (rT : brel T) 
 (plusS timesS : binary_op S) 
 (plusT timesT : binary_op T)
 (pS : A_bs_id_ann_properties rS plusS timesS)
 (pT : A_bs_id_ann_properties rT plusT timesT) : 
        A_bs_id_ann_properties
           (brel_product rS rT) 
           (bop_product plusS plusT)
           (bop_product timesS timesT) := 
let pS_id_ann_plus_times_d := A_id_ann_plus_times_d _ _ _ pS in 
let pS_id_ann_times_plus_d := A_id_ann_times_plus_d _ _ _ pS in 
let pT_id_ann_plus_times_d := A_id_ann_plus_times_d _ _ _ pT in 
let pT_id_ann_times_plus_d := A_id_ann_times_plus_d _ _ _ pT in 
{|
  A_id_ann_plus_times_d := A_bs_product_exists_id_ann_decide S T rS rT plusS timesS plusT timesT pS_id_ann_plus_times_d pT_id_ann_plus_times_d 
; A_id_ann_times_plus_d := A_bs_product_exists_id_ann_decide S T rS rT timesS plusS timesT plusT pS_id_ann_times_plus_d pT_id_ann_times_plus_d
|}.


Definition A_bs_product_properties 
    {S T: Type} 
    (rS : brel S) 
    (rT : brel T) 
    (plusS timesS : binary_op S) 
    (plusT timesT : binary_op T) (s : S) (t : T) 
    (pS : A_bs_properties rS plusS timesS) 
    (pT : A_bs_properties rT plusT timesT) : 
        A_bs_properties 
           (brel_product rS rT) 
           (bop_product plusS plusT)
           (bop_product timesS timesT) := 
{|
  A_bs_left_distributive_d := 
     A_bs_product_left_distributive_decide S T rS rT s t plusS timesS plusT timesT 
        (A_bs_left_distributive_d rS plusS timesS pS)
        (A_bs_left_distributive_d rT plusT timesT pT)
; A_bs_right_distributive_d := 
     A_bs_product_right_distributive_decide S T rS rT s t plusS timesS plusT timesT 
        (A_bs_right_distributive_d rS plusS timesS pS)
        (A_bs_right_distributive_d rT plusT timesT pT)

; A_bs_left_absorptive_d := 
     A_bs_product_left_absorptive_decide S T rS rT s t plusS timesS plusT timesT 
        (A_bs_left_absorptive_d rS plusS timesS pS)
        (A_bs_left_absorptive_d rT plusT timesT pT)
; A_bs_right_absorptive_d := 
     A_bs_product_right_absorptive_decide S T rS rT s t plusS timesS plusT timesT 
        (A_bs_right_absorptive_d rS plusS timesS pS)
        (A_bs_right_absorptive_d rT plusT timesT pT)
|}. 

Definition A_bs_product {S T : Type} (bsS : @A_bs S) (bsT : @A_bs T) : @A_bs (S * T)  := 
let eqvS   := A_bs_eqv bsS   in
let eqvT   := A_bs_eqv bsT   in
let peqvS  := A_eqv_proofs S eqvS in
let peqvT  := A_eqv_proofs T eqvT in 
let rS     := A_eqv_eq S eqvS  in 
let rT     := A_eqv_eq T eqvT  in
let s      := A_eqv_witness S eqvS in
let f      := A_eqv_new S eqvS in
let Pf     := A_eqv_not_trivial S eqvS in
let t      := A_eqv_witness T eqvT in
let g      := A_eqv_new T eqvT in
let Pg     := A_eqv_not_trivial T eqvT in
let plusS  := A_bs_plus bsS  in 
let plusT  := A_bs_plus bsT  in
let timesS := A_bs_times bsS in 
let timesT := A_bs_times bsT in 
{| 
     A_bs_eqv        := A_eqv_product S T eqvS eqvT 
   ; A_bs_plus       := bop_product plusS plusT 
   ; A_bs_times      := bop_product timesS timesT 
   ; A_bs_plus_props := sg_C_proofs_product S T rS rT plusS plusT s f t g Pf Pg peqvS peqvT 
                           (A_bs_plus_props bsS) 
                           (A_bs_plus_props bsT) 
   ; A_bs_times_props := sg_proofs_product S T rS rT timesS timesT s f t g Pf Pg peqvS peqvT 
                           (A_bs_times_props bsS) 
                           (A_bs_times_props bsT)
   ; A_bs_id_ann_props := A_bs_product_id_ann_properties rS rT plusS timesS plusT timesT
                           (A_bs_id_ann_props bsS) 
                           (A_bs_id_ann_props bsT)                           
   ; A_bs_props    := A_bs_product_properties rS rT plusS timesS plusT timesT s t 
                           (A_bs_props bsS) 
                           (A_bs_props bsT)
   ; A_bs_ast        := Ast_bs_product(A_bs_ast bsS, A_bs_ast bsT)
|}.



End ACAS.

Section AMCAS.

  Definition A_bs_product_below_bs {S T : Type} (A : @A_below_bs S)  (B : @A_below_bs T)  : @A_below_bs (S * T) :=
    A_classify_bs (A_bs_product (A_cast_up_bs A) (A_cast_up_bs B)).

  Definition A_mcas_bs_product {S T : Type} (A : @A_bs_mcas S)  (B : @A_bs_mcas T)  : @A_bs_mcas (S * T) :=
    match A, B with
    | A_MCAS_bs A', A_MCAS_bs B'               => A_MCAS_bs (A_bs_product_below_bs A' B')
    | A_MCAS_bs_Error sl1, A_MCAS_bs_Error sl2 => A_MCAS_bs_Error (sl1 ++ sl2)
    | A_MCAS_bs_Error sl1, _                   => A_MCAS_bs_Error sl1
    | _,  A_MCAS_bs_Error sl2                  => A_MCAS_bs_Error sl2
    end.
    
End AMCAS.   



Section CAS.


Definition bs_product_left_distributive_decide {S T : Type} (wS : S) (wT : T) 
  (dS : @bs_left_distributive_decidable S)
  (dT : @bs_left_distributive_decidable T) : 
        @bs_left_distributive_decidable (S * T)  := 
   match dS with 
   | inl ldS => 
     match dT with 
     | inl ldT  => inl (BS_Left_Distributive (wS, wT))
     | inr (BS_Not_Left_Distributive (t1, (t2, t3))) =>
           inr (BS_Not_Left_Distributive ((wS, t1), ((wS, t2), (wS, t3))))
     end 
   | inr (BS_Not_Left_Distributive (s1, (s2, s3))) =>
           inr (BS_Not_Left_Distributive ((s1, wT), ((s2, wT), (s3, wT))))
   end. 


Definition bs_product_right_distributive_decide {S T : Type} (wS : S) (wT : T) 
  (dS : @bs_right_distributive_decidable S)
  (dT : @bs_right_distributive_decidable T) : 
        @bs_right_distributive_decidable (S * T)  := 
   match dS with 
   | inl ldS => 
     match dT with 
     | inl ldT  => inl (BS_Right_Distributive (wS, wT) )
     | inr (BS_Not_Right_Distributive (t1, (t2, t3))) =>
           inr (BS_Not_Right_Distributive ((wS, t1), ((wS, t2), (wS, t3))))
     end 
   | inr (BS_Not_Right_Distributive (s1, (s2, s3))) =>
           inr (BS_Not_Right_Distributive ((s1, wT), ((s2, wT), (s3, wT))))
   end.


Definition bs_product_left_absorptive_decide {S T : Type} (wS : S) (wT : T) 
  (dS : @bs_left_absorptive_decidable S)
  (dT : @bs_left_absorptive_decidable T) : 
        @bs_left_absorptive_decidable (S * T)  := 
   match dS with 
   | inl ldS => 
     match dT with 
     | inl ldT  => inl (BS_Left_Absorptive (wS, wT) )
     | inr (BS_Not_Left_Absorptive (t1, t2)) =>
           inr (BS_Not_Left_Absorptive ((wS, t1), (wS, t2)))
     end 
   | inr (BS_Not_Left_Absorptive (s1, s2)) =>
           inr (BS_Not_Left_Absorptive ((s1, wT), (s2, wT)))
   end. 


Definition bs_product_right_absorptive_decide {S T : Type} (wS : S) (wT : T) 
  (dS : @bs_right_absorptive_decidable S)
  (dT : @bs_right_absorptive_decidable T) : 
        @bs_right_absorptive_decidable (S * T)  := 
   match dS with 
   | inl ldS => 
     match dT with 
     | inl ldT  => inl (BS_Right_Absorptive (wS, wT)) 
     | inr (BS_Not_Right_Absorptive (t1, t2)) =>
           inr (BS_Not_Right_Absorptive ((wS, t1), (wS, t2)))
     end 
   | inr (BS_Not_Right_Absorptive (s1, s2)) =>
           inr (BS_Not_Right_Absorptive ((s1, wT), (s2, wT)))
   end. 



Definition bs_product_exists_id_ann_decide
           {S T : Type} 
           (PS : @bs_exists_id_ann_decidable S)
           (PT : @bs_exists_id_ann_decidable T) :
             @bs_exists_id_ann_decidable (S * T) := 
match PS with 
| Id_Ann_None         => Id_Ann_None 
| Id_Ann_Id_None idS  =>
  match PT with 
  | Id_Ann_None               => Id_Ann_None 
  | Id_Ann_Id_None idT        => Id_Ann_Id_None (idS, idT) 
  | Id_Ann_None_Ann annT      => Id_Ann_None 
  | Id_Ann_Equal idT_annT     => Id_Ann_Id_None (idS, idT_annT) 
  | Id_Ann_Not_Equal (idT, _) => Id_Ann_Id_None (idS, idT) 
  end   
| Id_Ann_None_Ann annS =>
  match PT with 
  | Id_Ann_None                  => Id_Ann_None
  | Id_Ann_Id_None idT           => Id_Ann_None
  | Id_Ann_None_Ann annT         => Id_Ann_None_Ann (annS, annT) 
  | Id_Ann_Equal (idT_annT)     => Id_Ann_None_Ann (annS, idT_annT) 
  | Id_Ann_Not_Equal (_, annT)   => Id_Ann_None_Ann (annS, annT) 
  end   
| Id_Ann_Equal idS_annS  =>
  match PT with 
  | Id_Ann_None                  => Id_Ann_None
  | Id_Ann_Id_None idT           => Id_Ann_Id_None (idS_annS, idT)
  | Id_Ann_None_Ann annT         => Id_Ann_None_Ann (idS_annS, annT) 
  | Id_Ann_Equal idT_annT        => Id_Ann_Equal (idS_annS, idT_annT) 
  | Id_Ann_Not_Equal (idT, annT) => Id_Ann_Not_Equal ((idS_annS, idT), (idS_annS, annT))
  end   
| Id_Ann_Not_Equal (idS, annS)  =>
  match PT with 
  | Id_Ann_None                  => Id_Ann_None 
  | Id_Ann_Id_None idT           => Id_Ann_Id_None (idS, idT) 
  | Id_Ann_None_Ann annT         => Id_Ann_None_Ann (annS, annT)
  | Id_Ann_Equal idT_annT        => Id_Ann_Not_Equal ((idS, idT_annT), (annS, idT_annT))
  | Id_Ann_Not_Equal (idT,annT)  => Id_Ann_Not_Equal ((idS, idT), (annS, annT))
  end   
end. 


Definition bs_product_id_ann_properties 
  {S T: Type}
  (pS : @bs_id_ann_properties S) 
  (pT : @bs_id_ann_properties T) : 
        @bs_id_ann_properties (S * T) := 
let pS_id_ann_plus_times_d := id_ann_plus_times_d pS in 
let pS_id_ann_times_plus_d := id_ann_times_plus_d pS in 
let pT_id_ann_plus_times_d := id_ann_plus_times_d pT in 
let pT_id_ann_times_plus_d := id_ann_times_plus_d pT in 
{|
  id_ann_plus_times_d :=
    bs_product_exists_id_ann_decide pS_id_ann_plus_times_d pT_id_ann_plus_times_d 
; id_ann_times_plus_d :=
    bs_product_exists_id_ann_decide pS_id_ann_times_plus_d pT_id_ann_times_plus_d
|}.



Definition bs_product_properties 
  {S T : Type}
  (s : S) ( t : T)
  (bsS : @bs_properties S)
  (bsT : @bs_properties T) : @bs_properties (S * T) := 
{|
  bs_left_distributive_d      := bs_product_left_distributive_decide s t
                                     (bs_left_distributive_d bsS)
                                     (bs_left_distributive_d bsT)
; bs_right_distributive_d     := bs_product_right_distributive_decide s t
                                     (bs_right_distributive_d bsS)
                                     (bs_right_distributive_d bsT)
; bs_left_absorptive_d   := bs_product_left_absorptive_decide s t 
                                     (bs_left_absorptive_d bsS)
                                     (bs_left_absorptive_d bsT)
; bs_right_absorptive_d  := bs_product_right_absorptive_decide s t 
                                     (bs_right_absorptive_d bsS)
                                     (bs_right_absorptive_d bsT)
|}.

Definition bs_product {S T : Type} (bsS : @bs S) (bsT : @bs T) : @bs (S * T) := 
   {| 
     bs_eqv         := eqv_product (bs_eqv bsS) (bs_eqv bsT) 
   ; bs_plus        := bop_product (bs_plus bsS) (bs_plus bsT) 
   ; bs_times       := bop_product (bs_times bsS) (bs_times bsT) 
   ; bs_plus_props  := sg_C_certs_product
                         (eqv_eq (bs_eqv bsS))
                         (eqv_eq (bs_eqv bsT))
                         (bs_plus bsS) 
                         (bs_plus bsT)
                         (eqv_witness (bs_eqv bsS))
                         (eqv_new (bs_eqv bsS))
                         (eqv_witness (bs_eqv bsT))
                         (eqv_new (bs_eqv bsT))
                         (bs_plus_props bsS)
                         (bs_plus_props bsT) 
   ; bs_times_props := sg_certs_product 
                           (eqv_witness (bs_eqv bsS))
                           (eqv_witness (bs_eqv bsT))
                           (bs_times_props bsS) 
                           (bs_times_props bsT)
   ; bs_id_ann_props := bs_product_id_ann_properties
                          (bs_id_ann_props bsS)
                          (bs_id_ann_props bsT)
   ; bs_props       := bs_product_properties
                           (eqv_witness (bs_eqv bsS))
                           (eqv_witness (bs_eqv bsT))
                           (bs_props bsS) 
                           (bs_props bsT)
   ; bs_ast        := Ast_bs_product(bs_ast bsS, bs_ast bsT)
   |}. 
  
End CAS.

Section MCAS.
  
  Definition bs_product_below_bs {S T : Type} (A : @below_bs S)  (B : @below_bs T) : @below_bs (S * T) :=
    classify_bs (bs_product (cast_up_bs A) (cast_up_bs B)).

  Definition mcas_bs_product {S T : Type} (A : @bs_mcas S)  (B : @bs_mcas T)  : @bs_mcas (S * T) :=
    match A, B with
    | MCAS_bs A', MCAS_bs B'               => MCAS_bs (bs_product_below_bs A' B')
    | MCAS_bs_Error sl1, MCAS_bs_Error sl2 => MCAS_bs_Error (sl1 ++ sl2)
    | MCAS_bs_Error sl1, _                 => MCAS_bs_Error sl1
    | _,  MCAS_bs_Error sl2                => MCAS_bs_Error sl2
    end.

    
End MCAS.   

Section Verify.


Section ChecksCorrect.

  Variable S : Type.
  Variable T : Type.
  Variable rS : brel S.
  Variable rT : brel T.
  Variable plusS timesS : binary_op S.
  Variable plusT timesT : binary_op T.
  Variable wS : S.
  Variable f : S -> S.    
  Variable Pf : brel_not_trivial S rS f.
  Variable wT : T.
  Variable g : T -> T.      
  Variable Pg : brel_not_trivial T rT g.  
  Variable symS : brel_symmetric S rS.
  Variable symT : brel_symmetric T rT. 
  Variable transS : brel_transitive S rS.
  Variable transT : brel_transitive T rT. 
  Variable refS : brel_reflexive S rS. 
  Variable refT : brel_reflexive T rT.


Lemma correct_bs_product_left_distributive_decide
  (pS_d : A_bs_left_distributive_decidable rS plusS timesS) 
  (pT_d : A_bs_left_distributive_decidable rT plusT timesT):  
     bs_product_left_distributive_decide wS wT  
       (p2c_bs_left_distributive_decidable rS wS plusS timesS pS_d)
       (p2c_bs_left_distributive_decidable rT wT plusT timesT pT_d)
     = 
     p2c_bs_left_distributive_decidable
       (brel_product rS rT)
       (wS, wT)
        (bop_product plusS plusT)
        (bop_product timesS timesT)
        (A_bs_product_left_distributive_decide S T rS rT wS wT plusS timesS plusT timesT pS_d pT_d).
Proof. destruct pS_d as [ ldS | [ [s1 [s2 s3]] nldS]];
       destruct pT_d as [ ldT | [ [t1 [t2 t3]] nldT]];
       compute; reflexivity. 
Qed.


Lemma correct_bs_product_right_distributive_decide 
  (pS_d : A_bs_right_distributive_decidable rS plusS timesS) 
  (pT_d : A_bs_right_distributive_decidable rT plusT timesT):  
     bs_product_right_distributive_decide wS wT  
       (p2c_bs_right_distributive_decidable rS wS plusS timesS pS_d)
       (p2c_bs_right_distributive_decidable rT wT plusT timesT pT_d)
     = 
     p2c_bs_right_distributive_decidable
       (brel_product rS rT)
       (wS, wT)
        (bop_product plusS plusT)
        (bop_product timesS timesT)
        (A_bs_product_right_distributive_decide S T rS rT wS wT plusS timesS plusT timesT pS_d pT_d).
Proof. destruct pS_d as [ ldS | [ [s1 [s2 s3]] nldS]];
       destruct pT_d as [ ldT | [ [t1 [t2 t3]] nldT]];
       compute; reflexivity. 
Qed.


Lemma correct_bs_product_left_absorptive_decide
  (pS_d : A_bs_left_absorptive_decidable rS plusS timesS) 
  (pT_d : A_bs_left_absorptive_decidable rT plusT timesT):  
     bs_product_left_absorptive_decide wS wT  
       (p2c_bs_left_absorptive_decidable rS wS plusS timesS pS_d)
       (p2c_bs_left_absorptive_decidable rT wT plusT timesT pT_d)
     = 
     p2c_bs_left_absorptive_decidable
        (brel_product rS rT) (wS, wT)
        (bop_product plusS plusT)
        (bop_product timesS timesT)
        (A_bs_product_left_absorptive_decide S T rS rT wS wT plusS timesS plusT timesT pS_d pT_d).
Proof. destruct pS_d as [ ldS | [ [s1 s2] nldS]];
       destruct pT_d as [ ldT | [ [t1 t2] nldT]];
       compute; reflexivity. 
Qed.


Lemma correct_bs_product_right_absorptive_decide 
  (pS_d : A_bs_right_absorptive_decidable rS plusS timesS) 
  (pT_d : A_bs_right_absorptive_decidable rT plusT timesT):  
     bs_product_right_absorptive_decide wS wT  
       (p2c_bs_right_absorptive_decidable rS wS plusS timesS pS_d)
       (p2c_bs_right_absorptive_decidable rT wT plusT timesT pT_d)
     = 
     p2c_bs_right_absorptive_decidable
        (brel_product rS rT) (wS, wT) 
        (bop_product plusS plusT)
        (bop_product timesS timesT)
        (A_bs_product_right_absorptive_decide S T rS rT wS wT plusS timesS plusT timesT pS_d pT_d).
Proof. destruct pS_d as [ ldS | [ [s1 s2] nldS]];
       destruct pT_d as [ ldT | [ [t1 t2] nldT]];
       compute; reflexivity. 
Qed.


Lemma  correct_bs_product_properties 
  (bsS : A_bs_properties rS plusS timesS)
  (bsT : A_bs_properties rT plusT timesT) : 
    bs_product_properties wS wT (P2C_bs rS wS plusS timesS bsS) (P2C_bs rT wT plusT timesT bsT)
    =
    P2C_bs (brel_product rS rT) (wS, wT) (bop_product plusS plusT) (bop_product timesS timesT) 
       (A_bs_product_properties rS rT plusS timesS plusT timesT wS wT bsS bsT). 
Proof. unfold bs_product_properties, bs_product_properties, P2C_bs; simpl. 
       rewrite correct_bs_product_left_distributive_decide. 
       rewrite correct_bs_product_right_distributive_decide. 
       rewrite correct_bs_product_left_absorptive_decide.
       rewrite correct_bs_product_right_absorptive_decide. 
       reflexivity. 
Defined.


Lemma correct_bs_product_exists_id_ann_decidable
  (bS1 bS2 : binary_op S)
  (bT1 bT2 : binary_op T)
  (pS : A_bs_exists_id_ann_decidable rS bS1 bS2)
  (pT : A_bs_exists_id_ann_decidable rT bT1 bT2) :
  bs_product_exists_id_ann_decide
      (p2c_exists_id_ann _ rS bS1 bS2 pS)
      (p2c_exists_id_ann _ rT bT1 bT2 pT)                           
  =
  p2c_exists_id_ann _ 
    (brel_product rS rT)
    (bop_product bS1 bT1)
    (bop_product bS2 bT2)
    (A_bs_product_exists_id_ann_decide S T rS rT bS1 bS2 bT1 bT2 pS pT). 
Proof. unfold p2c_exists_id_ann, A_bs_product_exists_id_ann_decide, bs_product_exists_id_ann_decide; simpl. 
       destruct pS; simpl.
       + destruct pT; simpl. 
         ++ destruct p as [A B]; destruct p0 as [C D]. reflexivity. 
         ++ destruct p as [A B]; destruct p0 as [C D]. reflexivity. 
         ++ destruct p as [A B]; destruct p0 as [C D]. reflexivity. 
         ++ destruct p as [A B]. reflexivity. 
         ++ destruct p as [A B]. reflexivity. 
       + destruct pT; simpl.
         ++ destruct p as [A B]; destruct p0 as [C D]. reflexivity. 
         ++ destruct p as [[idS A] B]; destruct p0 as [[idT C] D]; simpl. reflexivity. 
         ++ destruct p as [A B]; destruct p0 as [C D]. reflexivity. 
         ++ destruct p as [[idS A] B]. destruct a as [idT_annT D]; simpl. reflexivity. 
         ++ destruct p as [[idS A] B]. destruct a as [[idT annT] D]; simpl. reflexivity. 
       + destruct pT; simpl.
         ++ destruct p as [A B]; destruct p0 as [C D]. reflexivity. 
         ++ destruct p as [A B]; destruct p0 as [C D]. reflexivity. 
         ++ destruct p as [A [annS B]]; destruct p0 as [C [annT D]]; simpl. reflexivity. 
         ++ destruct p as [A [annS B]]; destruct a as [idT_annT C]; simpl. reflexivity. 
         ++ destruct p as [A [annS B]]; destruct a as [[idT annT] C]; simpl. reflexivity. 
       + destruct pT; simpl.
         ++ destruct a as [idS_annS A]; destruct p as [C D]. reflexivity. 
         ++ destruct a as [idS_annS A]; destruct p as [[idT C] D]; simpl. reflexivity. 
         ++ destruct a as [idS_annS A]; destruct p as [C [annT D]]; simpl. reflexivity. 
         ++ destruct a as [idS_annS [A B]]; destruct a0 as [idT_annT [C D]]; simpl. reflexivity. 
         ++ destruct a as [idS_annS [A B]]; destruct a0 as [[idT annT] [[C D] E]]; simpl. reflexivity. 
       + destruct pT; simpl.
         ++ destruct a as [[idS annS] [[A B] C]]; destruct p as [D E]; simpl. reflexivity. 
         ++ destruct a as [[idS annS] [[A B] C]]; destruct p as [[idT D] E]; simpl. reflexivity. 
         ++ destruct a as [[idS annS] [[A B] C]]; destruct p as [D [annT E]]; simpl. reflexivity. 
         ++ destruct a as [[idS annS] [[A B] C]]; destruct a0 as [idT_annT [D E]]; simpl. reflexivity. 
         ++ destruct a as [[idS annS] [[A B] C]]; destruct a0 as [[idT annT] [[D E] F]]; simpl. reflexivity. 
Qed. 


Lemma  correct_bs_product_id_ann_properties
  (pS : A_bs_id_ann_properties rS plusS timesS)
  (pT : A_bs_id_ann_properties rT plusT timesT):  
  bs_product_id_ann_properties
    (P2C_id_ann _ rS plusS timesS pS)
    (P2C_id_ann _ rT plusT timesT pT) 
    = 
    P2C_id_ann _ (brel_product rS rT)
               (bop_product plusS plusT)
               (bop_product timesS timesT) 
               (A_bs_product_id_ann_properties rS rT plusS timesS plusT timesT pS pT). 
Proof. unfold A_bs_product_id_ann_properties, bs_product_id_ann_properties, P2C_id_ann; simpl.
       rewrite correct_bs_product_exists_id_ann_decidable. 
       rewrite correct_bs_product_exists_id_ann_decidable. 
       reflexivity. 
Qed.

End ChecksCorrect.

Theorem correct_bs_product (S T : Type) (bsS: @A_bs S) (bsT : @A_bs T) : 
   bs_product (A2C_bs bsS) (A2C_bs bsT)
   =
   A2C_bs (A_bs_product bsS bsT). 
Proof. unfold bs_product, A_bs_product, A2C_bs; simpl. 
       rewrite correct_eqv_product. 
       rewrite <- correct_sg_certs_product. 
       rewrite <- correct_sg_C_certs_product. 
       rewrite correct_bs_product_properties. 
       rewrite correct_bs_product_id_ann_properties. 
       reflexivity. 
Qed.

Theorem correct_bs_product_below_bs (S T : Type) (A : @A_below_bs S) (B : @A_below_bs T) : 
  bs_product_below_bs (A2C_below_bs A) (A2C_below_bs B)
  =
  A2C_below_bs (A_bs_product_below_bs A B).
Proof. unfold bs_product_below_bs, A_bs_product_below_bs.
       rewrite cast_up_bs_A2C_commute.
       rewrite cast_up_bs_A2C_commute.
       rewrite correct_bs_product.
       rewrite correct_classify_bs.
       reflexivity. 
Qed. 


Theorem correct_mcas_bs_product (S T : Type) (bsS : @A_bs_mcas S) (bsT : @A_bs_mcas T): 
         mcas_bs_product (A2C_bs_mcas bsS) (A2C_bs_mcas bsT) 
         = 
         A2C_bs_mcas (A_mcas_bs_product bsS bsT).
Proof. unfold mcas_bs_product, A_mcas_bs_product.
       destruct bsS, bsT; simpl; try reflexivity.
       rewrite correct_bs_product_below_bs. reflexivity. 
Qed. 

End Verify.   
