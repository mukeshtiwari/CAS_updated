Require Import Coq.Strings.String.
Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.

Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.eqv.theory.
Require Import CAS.coq.eqv.sum.

Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures.
Require Import CAS.coq.sg.left_sum.
Require Import CAS.coq.sg.right_sum.

Require Import CAS.coq.bs.properties.
Require Import CAS.coq.bs.structures.
Require Import CAS.coq.bs.cast.
Require Import CAS.coq.bs.classify. 
Require Import CAS.coq.bs.theory. 


Section Theory.

Section LeftRight. 
(*  
    (inl a) + (inl b) = inl (a +_S b) 
    (inr a) + (inr b) = inr (a +_T b) 
    (inl a) + (inr b) = inl a
    (inr a) + (inl b) = inl b 

    (inl a) * (inl b) = inl (a *_S b) 
    (inr a) * (inr b) = inr (a *_T b) 
    (inr a) * (inl b) = inr a 
    (inl a) * (inr b) = inr b 

compare to this left tranform 

     (a, b) |1> inl c = inl (a *_S c) 
     (a, b) |1> inr c = inr (b *_T c) 

that can easily be genrealized to this left transform 

     (a, b) |2> inl c = inl (a |>_S c) 
     (a, b) |2> inr c = inr (b |>_T c) 

or to
     (inl a) |> s = a |>_S s
     (inr b) |> s = b |>_T s 


Here is another interesting transform 
or two (with different +) 

     (inl a') |3> (a, b)  = (a' * _S a, b) 
     (inr b') |3> (a, b)  = (a, b' * _T b) 

which is a sub-algebra of product 
      
     (c, id) x (a, b)  = (c * _S a, b) 
     (id, c) x (a, b)  = (a, c * _T b) 

Q : could |3> be constructed like a product? 
Yes: 

(S, +_S, x_S) [x] (T, +_T, x_T)
  = (S x T, S + T, +_S [x or lex] +_T, |3>) 

Think of BGP-like scoped product: 

     (ebgp (a', b')) |> (a, b)  = (a' * _S a, b') 
           (ibgp b') |> (a, b)  = (a, b' * _T b) 

Could define 

     (inl (a', b')) |4> (a, b)  = (a' * _S a, b') 
           (inr b') |4> (a, b)  = (a, b' * _T b) 

Q : could |4> be constructed like a product? 
Yes: 

(S, +_S, x_S) [x] (T, +_T, x_T)
  = (S x T, S + T, +_S [x or lex] +_T, |4>) 
*) 


Variable S T : Type.
Variable rS : brel S.
Variable rT : brel T.

Variable wS : S.
Variable wT : T.

Variable addS  mulS : binary_op S.
Variable addT mulT : binary_op T. 
 
Variable congS: brel_congruence S rS rS. 
Variable refS : brel_reflexive S rS.
Variable symS : brel_symmetric S rS.
Variable tranS : brel_transitive S rS. 

Variable congT: brel_congruence T rT rT. 
Variable refT : brel_reflexive T rT.
Variable symT : brel_symmetric T rT. 
Variable tranT : brel_transitive T rT.

Variable commS : bop_commutative S rS addS.
Variable commT : bop_commutative T rT addT. 

Notation "x [+] y"  := (brel_sum x y) (at level 15).
Notation "x <+] y"  := (bop_left_sum x y) (at level 15).
Notation "x [+> y"  := (bop_right_sum x y) (at level 15).

Lemma A_bs_left_sum_right_sum_left_distributive : 
  bop_idempotent T rT addT →
  A_bs_left_distributive rS addS mulS → 
  A_bs_left_distributive rT addT mulT →
  A_bs_left_absorptive rT addT mulT →
  A_bs_left_distributive (rS [+] rT) (addS <+] addT) (mulS [+> mulT).
Proof. intros idemT ldS ldT laT [s1 | t1] [s2 | t2] [s3 | t3]; compute.
       + apply ldS.
       + apply refS.
       + apply refS.
       + apply refT. 
       + apply symT. apply idemT.
       + apply laT. 
       + assert (A := commT t1 (mulT t1 t2)).
         assert (B := laT t1 t2).
         exact (tranT _ _ _ B A). 
       + apply ldT.        
Qed.          
       

Lemma A_bs_left_sum_right_sum_not_left_distributive_v1 ( s : S) : 
  bop_not_idempotent T rT addT →
         A_bs_not_left_distributive (rS [+] rT) (addS <+] addT) (mulS [+> mulT).
Proof. intros [t Pt]. exists ((inr t), (inl s, inl s)). compute.
       rewrite (sym_as_rewrite symT). assumption.
Defined.        


Lemma A_bs_left_sum_right_sum_not_left_distributive_v2 : 
  A_bs_not_left_distributive rS addS mulS → 
     A_bs_not_left_distributive (rS [+] rT) (addS <+] addT) (mulS [+> mulT).
Proof. intros [[s1 [s2 s3]] Ps]. exists ((inl s1), (inl s2, inl s3)). compute. assumption. Defined.        

Lemma A_bs_left_sum_right_sum_not_left_distributive_v3 : 
  A_bs_not_left_distributive rT addT mulT → 
         A_bs_not_left_distributive (rS [+] rT) (addS <+] addT) (mulS [+> mulT).
Proof. intros [[t1 [t2 t3]] Pt]. exists ((inr t1), (inr t2, inr t3)). compute. assumption. Defined.        

Lemma A_bs_left_sum_right_sum_not_left_distributive_v4 : 
  A_bs_not_left_absorptive rT addT mulT →
         A_bs_not_left_distributive (rS [+] rT) (addS <+] addT) (mulS [+> mulT).
Proof. intros [ [t1 t2] Pt]. exists ((inr t1), (inl wS, inr t2)). compute. assumption. Defined.        


Definition A_bs_left_sum_right_sum_left_distributive_decide 
  (idm_d : bop_idempotent_decidable T rT addT)
  (ldS_d : A_bs_left_distributive_decidable  rS addS mulS)
  (ldT_d : A_bs_left_distributive_decidable  rT addT mulT)
  (lla_d : A_bs_left_absorptive_decidable  rT addT mulT) : 
         A_bs_left_distributive_decidable (rS [+] rT) (addS <+] addT) (mulS [+> mulT) := 
match idm_d with                                                                                  
| inl idm  =>
    match ldS_d with
    | inl ldS  =>
        match ldT_d with
        | inl ldT  =>
            match lla_d with
            | inl lla  => inl _ (A_bs_left_sum_right_sum_left_distributive idm ldS ldT lla)
            | inr nlla => inr _ (A_bs_left_sum_right_sum_not_left_distributive_v4 nlla)
            end 
        | inr nldT => inr _ (A_bs_left_sum_right_sum_not_left_distributive_v3 nldT)
        end 
    | inr nldS => inr _ (A_bs_left_sum_right_sum_not_left_distributive_v2 nldS)
    end 
| inr nidm => inr _ (A_bs_left_sum_right_sum_not_left_distributive_v1 wS nidm)
end. 


(* Let's see what happens when both plus and times are defined the same way. 
   (Do we want such a construction? Is it useful?) 

 This requires 
   rS (mulS s1 s2) (addS (mulS s1 s2) s1) = true
 and 
   rS (mulS s1 s2) (addS s1 (mulS s1 s2)) = true
 (or just one of these if addS is commutative) 
 
 This seems to be the opposite of absorption, for example 
   rS s1 (addS s1 (mulS s1 s2)) = true

 Note: the new properties cannot hold 
 if the additive id is the multiplicative ann. 

 But what about absorption? 

Lemma test_left_for_left_distrib :
  (∀ s1 s2 : S, rS (mulS s1 s2) (addS (mulS s1 s2) s1) = true) →
  (∀ s1 s2 : S, rS (mulS s1 s2) (addS s1 (mulS s1 s2)) = true) →  
  bop_idempotent S rS addS →  
  bop_left_distributive S rS addS mulS → 
  bop_left_distributive T rT addT mulT →
         bop_left_distributive (S + T) (rS [+] rT) (addS <+] addT) (mulS <+] mulT).
Proof. intros P1 P2 idemS ldS ldT [s1 | t1] [s2 | t2] [s3 | t3]; simpl. 
       apply ldS.
       apply P1. 
       apply P2. 
       apply symS. apply idemS.
       apply refS.
       apply refS. 
       apply refS. 
       apply ldT.
Qed.

Lemma test_left_for_left_absorp :
         A_bs_not_left_absorptive(S + T) (rS [+] rT) (addS <+] addT) (mulS <+] mulT).
Proof. exists (inr wT, inl wS). compute. reflexivity. Defined. 


Lemma test_right_right_for_left_distrib :
  (∀ t1 t2 : T, rT (mulT t1 t2) (addT (mulT t1 t2) t1) = true) →
  (∀ t1 t2 : T, rT (mulT t1 t2) (addT t1 (mulT t1 t2)) = true) →  
  bop_idempotent T rT addT →  
  bop_left_distributive S rS addS mulS → 
  bop_left_distributive T rT addT mulT →
         bop_left_distributive (S + T) (rS [+] rT) (addS [+> addT) (mulS [+> mulT).
Proof. intros  P1 P2 idemT ldS ldT [s1 | t1] [s2 | t2] [s3 | t3]; compute.
       apply ldS.
       apply refT.
       apply refT.
       apply refT.
       apply symT. apply idemT.       
       apply P2.
       apply P1. 
       apply ldT.
Qed. 
*)        



Lemma A_bs_left_sum_right_sum_right_distributive : 
  bop_idempotent T rT addT →
  A_bs_right_distributive rS addS mulS → 
  A_bs_right_distributive rT addT mulT →
  A_bs_right_absorptive rT addT mulT →
         A_bs_right_distributive (rS [+] rT) (addS <+] addT) (mulS [+> mulT).
Proof. intros idemT rdS rdT raT  [s1 | t1] [s2 | t2] [s3 | t3]; compute.
       + apply rdS.
       + apply refS.
       + apply refS.
       + apply refT. 
       + apply symT. apply idemT.
       + apply raT. 
       + assert (A := commT t1 (mulT t2 t1)).
         assert (B := raT t1 t2).
         exact (tranT _ _ _ B A). 
       + apply rdT.        
Qed.          


Lemma A_bs_left_sum_right_sum_not_right_distributive_v1 : 
  bop_not_idempotent T rT addT →
         A_bs_not_right_distributive (rS [+] rT) (addS <+] addT) (mulS [+> mulT).
Proof. intros [t Pt]. exists ((inr t), (inl wS, inl wS)). compute.
       rewrite (sym_as_rewrite symT). assumption.
Defined.        


Lemma A_bs_left_sum_right_sum_not_right_distributive_v2 : 
  A_bs_not_right_distributive rS addS mulS → 
         A_bs_not_right_distributive (rS [+] rT) (addS <+] addT) (mulS [+> mulT).
Proof. intros [[s1 [s2 s3]] Ps]. exists ((inl s1), (inl s2, inl s3)). compute. assumption. Defined.        

Lemma A_bs_left_sum_right_sum_not_right_distributive_v3 : 
  A_bs_not_right_distributive rT addT mulT → 
         A_bs_not_right_distributive (rS [+] rT) (addS <+] addT) (mulS [+> mulT).
Proof. intros [[t1 [t2 t3]] Pt]. exists ((inr t1), (inr t2, inr t3)). compute. assumption. Defined.        

Lemma A_bs_left_sum_right_sum_not_right_distributive_v4 : 
  A_bs_not_right_absorptive rT addT mulT →
         A_bs_not_right_distributive (rS [+] rT) (addS <+] addT) (mulS [+> mulT).
Proof. intros [ [t1 t2] Pt]. exists ((inr t1), (inl wS, inr t2)). compute. assumption. Defined.        


Definition A_bs_left_sum_right_sum_right_distributive_decide 
  (idm_d : bop_idempotent_decidable T rT addT)
  (ldS_d : A_bs_right_distributive_decidable rS addS mulS)
  (ldT_d : A_bs_right_distributive_decidable rT addT mulT)
  (lla_d : A_bs_right_absorptive_decidable rT addT mulT) :
         A_bs_right_distributive_decidable (rS [+] rT) (addS <+] addT) (mulS [+> mulT) := 
match idm_d with                                                                                  
| inl idm  =>
    match ldS_d with
    | inl ldS  =>
        match ldT_d with
        | inl ldT  =>
            match lla_d with
            | inl lla  => inl (A_bs_left_sum_right_sum_right_distributive idm ldS ldT lla)
            | inr nlla => inr (A_bs_left_sum_right_sum_not_right_distributive_v4 nlla)
            end 
        | inr nldT => inr (A_bs_left_sum_right_sum_not_right_distributive_v3 nldT)
        end 
    | inr nldS => inr (A_bs_left_sum_right_sum_not_right_distributive_v2 nldS)
    end 
| inr nidm => inr (A_bs_left_sum_right_sum_not_right_distributive_v1 nidm)
end. 

Lemma A_bs_left_sum_right_sum_left_absorptive :
  bop_idempotent T rT addT →   
  A_bs_left_absorptive rS addS mulS →   
  A_bs_left_absorptive rT addT mulT →    
         A_bs_left_absorptive (rS [+] rT) (addS <+] addT) (mulS [+> mulT). 
Proof. intros idemT llaS llaT. unfold A_bs_left_absorptive.
       intros [s1 | t1] [s2 | t2]; compute.
       + apply llaS. 
       + apply refS. 
       + apply symT. apply idemT. 
       + apply llaT.
Qed. 

Lemma A_bs_left_sum_right_sum_not_left_absorptive_v1 :
  bop_not_idempotent T rT addT →   
         A_bs_not_left_absorptive (rS [+] rT) (addS <+] addT) (mulS [+> mulT). 
Proof. intros [t Pt]. exists (inr t, inl wS). compute. rewrite (sym_as_rewrite symT). assumption. Defined. 

Lemma A_bs_left_sum_right_sum_not_left_absorptive_v2 :
  A_bs_not_left_absorptive rS addS mulS →   
         A_bs_not_left_absorptive (rS [+] rT) (addS <+] addT) (mulS [+> mulT). 
Proof. intros [[s1 s2] P]. exists (inl s1, inl s2). compute. assumption. Defined. 

Lemma A_bs_left_sum_right_sum_not_left_absorptive_v3 :
  A_bs_not_left_absorptive rT addT mulT →   
         A_bs_not_left_absorptive (rS [+] rT) (addS <+] addT) (mulS [+> mulT). 
Proof. intros [[t1 t2] P]. exists (inr t1, inr t2). compute. assumption. Defined. 


Definition A_bs_left_sum_right_sum_left_absorptive_decide :
  bop_idempotent_decidable T rT addT →
  A_bs_left_absorptive_decidable rS addS mulS →   
  A_bs_left_absorptive_decidable rT addT mulT →    
         A_bs_left_absorptive_decidable (rS [+] rT) (addS <+] addT) (mulS [+> mulT)
:= λ idm_d llaS_d llaT_d,
match idm_d with                                                                                  
| inl idm  => match llaS_d with
              | inl llaS  => match llaT_d with
                            | inl llaT  => inl _ (A_bs_left_sum_right_sum_left_absorptive idm llaS llaT)
                            | inr nllaT => inr _ (A_bs_left_sum_right_sum_not_left_absorptive_v3 nllaT)
                            end 
              | inr nllaS => inr _ (A_bs_left_sum_right_sum_not_left_absorptive_v2 nllaS)
              end 
| inr nidm => inr _ (A_bs_left_sum_right_sum_not_left_absorptive_v1 nidm)
end. 


Lemma A_bs_left_sum_right_sum_right_absorptive :
  bop_idempotent T rT addT →   
  A_bs_right_absorptive rS addS mulS →   
  A_bs_right_absorptive rT addT mulT →      
         A_bs_right_absorptive (rS [+] rT) (addS <+] addT) (mulS [+> mulT). 
Proof. intros idemT lraS lraT. unfold A_bs_right_absorptive.
       intros [s1 | t1] [s2 | t2]; compute.
       apply lraS. apply refS. apply symT. apply idemT. apply lraT.
Defined.        

Lemma A_bs_left_sum_right_sum_not_right_absorptive_v1 :
  bop_not_idempotent T rT addT →   
         A_bs_not_right_absorptive (rS [+] rT) (addS <+] addT) (mulS [+> mulT). 
Proof. intros [t Pt]. exists (inr t, inl wS). compute. rewrite (sym_as_rewrite symT). assumption. Defined. 

Lemma A_bs_left_sum_right_sum_not_right_absorptive_v2 :
  A_bs_not_right_absorptive rS addS mulS →   
         A_bs_not_right_absorptive  (rS [+] rT) (addS <+] addT) (mulS [+> mulT). 
Proof. intros [[s1 s2] P]. exists (inl s1, inl s2). compute. assumption. Defined. 

Lemma A_bs_left_sum_right_sum_not_right_absorptive_v3 :
  A_bs_not_right_absorptive rT addT mulT →   
         A_bs_not_right_absorptive (rS [+] rT) (addS <+] addT) (mulS [+> mulT). 
Proof. intros [[t1 t2] P]. exists (inr t1, inr t2). compute. assumption. Defined. 

Definition A_bs_left_sum_right_sum_right_absorptive_decide :
  bop_idempotent_decidable T rT addT →
  A_bs_right_absorptive_decidable rS addS mulS →   
  A_bs_right_absorptive_decidable rT addT mulT →    
         A_bs_right_absorptive_decidable (rS [+] rT) (addS <+] addT) (mulS [+> mulT)
:= λ idm_d lraS_d lraT_d,
match idm_d with                                                                                  
| inl idm  => match lraS_d with
              | inl lraS  => match lraT_d with
                            | inl lraT  => inl _ (A_bs_left_sum_right_sum_right_absorptive idm lraS lraT)
                            | inr nlraT => inr _ (A_bs_left_sum_right_sum_not_right_absorptive_v3 nlraT)
                            end 
              | inr nlraS => inr _ (A_bs_left_sum_right_sum_not_right_absorptive_v2 nlraS)
              end 
| inr nidm => inr _ (A_bs_left_sum_right_sum_not_right_absorptive_v1 nidm)
end. 



(*                                                                      
Lemma A_bs_left_sum_right_sum_not_left_strictly_absorptive :
    bop_idempotent T rT addT -> 
    A_bs_not_left_strictly_absorptive 
      (S + T) (rS [+] rT) (addS <+] addT) (mulS [+> mulT).
Proof.
  intros Ha.
  exists (inr wT, inl wS); compute.
  right.
  apply symT, Ha.
Qed.

Lemma A_bs_left_sum_right_sum_not_left_strictly_absorptive_v2:
  bop_not_idempotent T rT addT -> 
  A_bs_not_left_strictly_absorptive
    (S + T) (rS [+] rT) (addS <+] addT) (mulS [+> mulT).
 Proof. intros [t nidem]. exists (inr t, inl wS); simpl.
        left. case_eq(rT t (addT t t)); intro A; auto. 
        apply symT in A. rewrite A in nidem. exact nidem. 
Qed.

(* Experimental 
   Note: the above lemma shows the following is not needed. 
*)
Lemma A_bs_left_sum_right_sum_left_strictly_absorptive_absurd :
  A_bs_left_strictly_absorptive_absurd
    (S + T) (rS [+] rT) (addS <+] addT) (mulS [+> mulT).
Proof.
  intros Hd.
  pose proof (Hd (inr wT) (inl wS)) as [Hfl Hfr];
  compute in Hfl, Hfr.
Print A_bs_not_left_strictly_absorptive.   
  rewrite Hfl in Hfr.
  congruence.
Qed.



Lemma A_bs_left_sum_right_sum_not_right_strictly_absorptive :
    bop_idempotent T rT addT -> 
    A_bs_not_right_strictly_absorptive 
      (S + T) (rS [+] rT) (addS <+] addT) (mulS [+> mulT).
Proof.
  intros Ha.
  exists (inr wT, inl wS); compute.
  right.
  apply symT, Ha.
Qed.

Lemma A_bs_left_sum_right_sum_not_right_strictly_absorptive_v2 :
    bop_not_idempotent T rT addT -> 
    A_bs_not_right_strictly_absorptive 
      (S + T) (rS [+] rT) (addS <+] addT) (mulS [+> mulT).
Proof.
  intros [t nidem].
  exists (inr t, inl wS); compute.
  left. case_eq(rT t (addT t t)); intro A; auto. 
  apply symT in A.  rewrite A in nidem.  exact nidem. 
Qed.
 *)

                                                                      
Lemma A_bs_left_sum_right_sum_exists_id_ann_equal :
      A_bs_exists_id_ann_equal rT addT mulT →                                                                                       
      A_bs_exists_id_ann_equal (rS [+] rT) (addS <+] addT) (mulS [+> mulT). 
Proof. intros [iT [piT paT]].
       exists (inr iT). split. 
       apply bop_left_sum_is_id; auto.
       apply bop_right_sum_is_ann; auto. 
Defined. 


Lemma A_bs_left_sum_right_sum_exists_id_ann_not_equal :
      A_bs_exists_id_ann_not_equal rT addT mulT →                                                                                       
      A_bs_exists_id_ann_not_equal (rS [+] rT) (addS <+] addT) (mulS [+> mulT). 
Proof. intros [[idT annT] [[A B] C]].
       exists (inr idT, inr annT). split. split. 
       apply bop_left_sum_is_id; auto.
       apply bop_right_sum_is_ann; auto.
       compute. exact C. 
Defined. 

Lemma A_bs_right_sum_left_sum_exists_id_ann_equal :
      A_bs_exists_id_ann_equal rS mulS addS  →                                                                                       
      A_bs_exists_id_ann_equal (rS [+] rT) (mulS [+> mulT) (addS <+] addT). 
Proof. intros [iS [piS paS]].
       exists (inl iS). split. 
       apply bop_right_sum_is_id; auto.
       apply bop_left_sum_is_ann; auto. 
Defined. 

Lemma A_bs_right_sum_left_sum_exists_id_ann_not_equal :
      A_bs_exists_id_ann_not_equal rS mulS addS  →                                                                                       
      A_bs_exists_id_ann_not_equal (rS [+] rT) (mulS [+> mulT) (addS <+] addT). 
Proof. intros [[idS annS] [[A B] C]].
       exists (inl idS, inl annS). split. split. 
       apply bop_right_sum_is_id; auto.
       apply bop_left_sum_is_ann; auto.
       compute. exact C. 
Defined. 



Definition A_bs_left_sum_right_sum_exists_id_ann_decide
           (PT : A_bs_exists_id_ann_decidable rT addT mulT) :
           A_bs_exists_id_ann_decidable (rS [+] rT) (addS <+] addT) (mulS [+> mulT) := 
(*
bop_left_sum_exists_id
     : ∀ (S T : Type) (rS : brel S) (rT : brel T) 
         (bS : binary_op S) (bT : binary_op T),
         brel_reflexive S rS
         → bop_exists_id T rT bT
           → bop_exists_id (S + T) (rS [+] rT) (bS <+] bT)

bop_left_sum_not_exists_id
     : ∀ (S T : Type) (rS : brel S) (rT : brel T) 
         (bS : binary_op S) (bT : binary_op T),
         T
         → bop_not_exists_id T rT bT
           → bop_not_exists_id (S + T) (rS [+] rT) (bS <+] bT)

bop_right_sum_exists_ann
     : ∀ (S T : Type) (rS : brel S) (rT : brel T) 
         (bS : binary_op S) (bT : binary_op T),
         brel_reflexive T rT
         → bop_exists_ann T rT bT
           → bop_exists_ann (S + T) (rS [+] rT) (bS [+>bT)

bop_right_sum_not_exists_ann
     : ∀ (S T : Type) (rS : brel S) (rT : brel T) 
         (bS : binary_op S) (bT : binary_op T),
         T
         → bop_not_exists_ann T rT bT
           → bop_not_exists_ann (S + T) (rS [+] rT) (bS [+>bT)
 *)
let has_id_left := bop_left_sum_exists_id _ _ rS rT addS addT refS in                                                                           
let no_id_left := bop_left_sum_not_exists_id _ _ rS rT addS addT wT in
let has_ann_right := bop_right_sum_exists_ann _ _ rS rT mulS mulT refT in                                                                           
let no_ann_right := bop_right_sum_not_exists_ann _ _ rS rT mulS mulT wT in 
match PT with 
  | A_Id_Ann_None _ _ _ (nidT, nannT)             =>
    A_Id_Ann_None _ _ _ (no_id_left nidT, no_ann_right nannT)
  | A_Id_Ann_Id_None _ _ _ (idT, nannT)           =>
    A_Id_Ann_Id_None _ _ _ (has_id_left idT, no_ann_right nannT)
  | A_Id_Ann_None_Ann _ _ _ (nidT, annT)          =>
    A_Id_Ann_None_Ann _ _ _ (no_id_left nidT, has_ann_right annT)
  | A_Id_Ann_Equal _ _ _ (idT_annT_equal)         =>
    A_Id_Ann_Equal _ _ _ (A_bs_left_sum_right_sum_exists_id_ann_equal idT_annT_equal)
  | A_Id_Ann_Not_Equal _ _ _ (idT_annT_not_equal) =>
    A_Id_Ann_Not_Equal _ _ _ (A_bs_left_sum_right_sum_exists_id_ann_not_equal idT_annT_not_equal)
end. 


Definition A_bs_right_sum_left_sum_exists_id_ann_decide
           (PS : A_bs_exists_id_ann_decidable rS mulS addS) :
           A_bs_exists_id_ann_decidable (rS [+] rT) (mulS [+> mulT) (addS <+] addT) := 
(*
bop_left_sum_exists_ann
     : ∀ (S T : Type) (rS : brel S) (rT : brel T) 
         (bS : binary_op S) (bT : binary_op T),
         brel_reflexive S rS
         → bop_exists_ann S rS bS
           → bop_exists_ann (S + T) (rS [+] rT) (bS <+] bT)

bop_left_sum_not_exists_ann
     : ∀ (S T : Type) (rS : brel S) (rT : brel T) 
         (bS : binary_op S) (bT : binary_op T),
         S
         → bop_not_exists_ann S rS bS
           → bop_not_exists_ann (S + T) (rS [+] rT) (bS <+] bT)

bop_right_sum_exists_id
     : ∀ (S T : Type) (rS : brel S) (rT : brel T) 
         (bS : binary_op S) (bT : binary_op T),
         brel_reflexive T rT
         → bop_exists_id S rS bS
           → bop_exists_id (S + T) (rS [+] rT) (bS [+>bT)

bop_right_sum_not_exists_id
     : ∀ (S T : Type) (rS : brel S) (rT : brel T) 
         (bS : binary_op S) (bT : binary_op T),
         S
         → bop_not_exists_id S rS bS
           → bop_not_exists_id (S + T) (rS [+] rT) (bS [+>bT)
 *)
let has_ann_left := bop_left_sum_exists_ann _ _ rS rT addS addT refS in                                                                           
let no_ann_left  := bop_left_sum_not_exists_ann _ _ rS rT addS addT wS in
let has_id_right := bop_right_sum_exists_id _ _ rS rT mulS mulT refT in                                                                           
let no_id_right  := bop_right_sum_not_exists_id _ _ rS rT mulS mulT wS in 
match PS with 
  | A_Id_Ann_None _ _ _ (nidS, nannS)             =>
    A_Id_Ann_None _ _ _ (no_id_right nidS, no_ann_left nannS)
  | A_Id_Ann_Id_None _ _ _ (idS, nannS)           =>
    A_Id_Ann_Id_None _ _ _ (has_id_right idS, no_ann_left nannS)
  | A_Id_Ann_None_Ann _ _ _ (nidS, annS)          =>
    A_Id_Ann_None_Ann _ _ _ (no_id_right nidS, has_ann_left annS)
  | A_Id_Ann_Equal _ _ _ (idS_annS_equal)         =>
    A_Id_Ann_Equal _ _ _ (A_bs_right_sum_left_sum_exists_id_ann_equal idS_annS_equal)
  | A_Id_Ann_Not_Equal _ _ _ (idS_annS_not_equal) =>
    A_Id_Ann_Not_Equal _ _ _ (A_bs_right_sum_left_sum_exists_id_ann_not_equal idS_annS_not_equal)
end. 
  
Definition A_left_sum_right_sum_id_ann_properties 
 (pS : A_bs_id_ann_properties rS addS mulS)
 (pT : A_bs_id_ann_properties rT addT mulT) : 
        A_bs_id_ann_properties (rS [+] rT) (addS <+] addT) (mulS [+> mulT) := 
let pS_id_ann_times_plus_d := A_id_ann_times_plus_d _ _ _ pS in 
let pT_id_ann_plus_times_d := A_id_ann_plus_times_d _ _ _ pT in 
{|
  A_id_ann_plus_times_d := A_bs_left_sum_right_sum_exists_id_ann_decide pT_id_ann_plus_times_d 
; A_id_ann_times_plus_d := A_bs_right_sum_left_sum_exists_id_ann_decide pS_id_ann_times_plus_d 
|}.

                                                                                    
End LeftRight.

Section RightLeft.


(*  
    (inl a) + (inl b) = inl (a +_S b) 
    (inr a) + (inr b) = inr (a +_T b) 
    (inr a) + (inl b) = inr a 
    (inl a) + (inr b) = inr b 

    (inl a) * (inl b) = inl (a *_S b) 
    (inr a) * (inr b) = inr (a *_T b) 
    (inl a) * (inr b) = inl a
    (inr a) * (inl b) = inl b 

      
*) 


Variable S T : Type.
Variable rS : brel S.
Variable rT : brel T.

Variable wS : S.
Variable wT : T.

Variable addS  mulS : binary_op S.
Variable addT mulT : binary_op T. 
 
Variable congS: brel_congruence S rS rS. 
Variable refS : brel_reflexive S rS.
Variable symS : brel_symmetric S rS.
Variable tranS : brel_transitive S rS. 

Variable congT: brel_congruence T rT rT. 
Variable refT : brel_reflexive T rT.
Variable symT : brel_symmetric T rT. 
Variable tranT : brel_transitive T rT.

Variable commS : bop_commutative S rS addS.
Variable commT : bop_commutative T rT addT. 

Notation "x [+] y"  := (brel_sum x y) (at level 15).
Notation "x <+] y"  := (bop_left_sum x y) (at level 15).
Notation "x [+> y"  := (bop_right_sum x y) (at level 15).

Lemma A_bs_right_sum_left_sum_left_distributive : 
  bop_idempotent S rS addS →
  A_bs_left_distributive rS addS mulS → 
  A_bs_left_distributive rT addT mulT →
  A_bs_left_absorptive rS addS mulS →
         A_bs_left_distributive (rS [+] rT) (addS [+> addT) (mulS <+] mulT).
Proof. intros idemS ldS ldT llaS [s1 | t1] [s2 | t2] [s3 | t3]; compute.
       + apply ldS.
       + assert (A := commS s1 (mulS s1 s2)).
         assert (B := llaS s1 s2).
         exact (tranS _ _ _ B A). 
       + apply llaS.
       + apply symS. apply idemS.       
       + apply refS.
       + apply refT.       
       + apply refT.
       + apply ldT.
Qed. 

Lemma A_bs_right_sum_left_sum_not_left_distributive_v1 ( t : T) : 
  bop_not_idempotent S rS addS →
         A_bs_not_left_distributive (rS [+] rT) (addS [+> addT) (mulS <+] mulT).
Proof. intros [s Ps]. exists ((inl s), (inr t, inr t)). compute.
       rewrite (sym_as_rewrite symS). exact Ps. 
Defined. 


Lemma A_bs_right_sum_left_sum_not_left_distributive_v2 : 
  A_bs_not_left_distributive rS addS mulS → 
         A_bs_not_left_distributive (rS [+] rT) (addS [+> addT) (mulS <+] mulT).
Proof. intros [[s1 [s2 s3]] Ps]. exists ((inl s1), (inl s2, inl s3)). compute. assumption. Defined.        

Lemma A_bs_right_sum_left_sum_not_left_distributive_v3 : 
  A_bs_not_left_distributive rT addT mulT → 
         A_bs_not_left_distributive (rS [+] rT) (addS [+> addT) (mulS <+] mulT).
Proof. intros [[t1 [t2 t3]] Pt]. exists ((inr t1), (inr t2, inr t3)). compute. assumption. Defined.        

Lemma A_bs_right_sum_left_sum_not_left_distributive_v4 (t : T) : 
  A_bs_not_left_absorptive rS addS mulS →
         A_bs_not_left_distributive (rS [+] rT) (addS [+> addT) (mulS <+] mulT).
Proof. intros [ [s1 s2] Ps]. exists ((inl s1), (inr t, inl s2)). compute. assumption. Defined.        


Definition A_bs_right_sum_left_sum_left_distributive_decide 
  (idm_d : bop_idempotent_decidable S rS addS)
  (ldS_d : A_bs_left_distributive_decidable rS addS mulS)
  (ldT_d : A_bs_left_distributive_decidable rT addT mulT)
  (lla_d : A_bs_left_absorptive_decidable rS addS mulS) : 
         A_bs_left_distributive_decidable (rS [+] rT) (addS [+> addT) (mulS <+] mulT) :=
match idm_d with                                                                                  
| inl idm  =>
    match ldS_d with
    | inl ldS  =>
        match ldT_d with
        | inl ldT  =>
            match lla_d with
            | inl lla  => inl (A_bs_right_sum_left_sum_left_distributive idm ldS ldT lla )
            | inr nlla => inr (A_bs_right_sum_left_sum_not_left_distributive_v4 wT nlla)
            end 
        | inr nldT => inr (A_bs_right_sum_left_sum_not_left_distributive_v3 nldT)
        end 
    | inr nldS => inr (A_bs_right_sum_left_sum_not_left_distributive_v2 nldS)
    end 
| inr nidm => inr (A_bs_right_sum_left_sum_not_left_distributive_v1 wT nidm)
end. 

Lemma A_bs_right_sum_left_sum_right_distributive : 
  bop_idempotent S rS addS →
  A_bs_right_distributive rS addS mulS → 
  A_bs_right_distributive rT addT mulT →
  A_bs_right_absorptive rS addS mulS →
        A_bs_right_distributive (rS [+] rT) (addS [+> addT) (mulS <+] mulT).
Proof. intros idemS rdS rdT lraS [s1 | t1] [s2 | t2] [s3 | t3]; compute.
       + apply rdS.
       + assert (A := commS s1 (mulS s2 s1)).
         assert (B := lraS s1 s2).
         exact (tranS _ _ _ B A). 
       + apply lraS.
       + apply symS. apply idemS.       
       + apply refS.
       + apply refT.       
       + apply refT.
       + apply rdT.        
Qed. 


Lemma A_bs_right_sum_left_sum_not_right_distributive_v1 ( t : T ) : 
  bop_not_idempotent S rS addS →
         A_bs_not_right_distributive (rS [+] rT) (addS [+> addT) (mulS <+] mulT).
Proof. intros [s Ps]. exists ((inl s), (inr t, inr t)). compute.
       rewrite (sym_as_rewrite symS). assumption.
Defined. 


Lemma A_bs_right_sum_left_sum_not_right_distributive_v2 : 
  A_bs_not_right_distributive rS addS mulS → 
         A_bs_not_right_distributive (rS [+] rT) (addS [+> addT) (mulS <+] mulT).
Proof. intros [[s1 [s2 s3]] Ps]. exists ((inl s1), (inl s2, inl s3)). compute. assumption. Defined. 

Lemma A_bs_right_sum_left_sum_not_right_distributive_v3 : 
  A_bs_not_right_distributive rT addT mulT → 
         A_bs_not_right_distributive (rS [+] rT) (addS [+> addT) (mulS <+] mulT).
Proof. intros [[t1 [t2 t3]] Pt]. exists ((inr t1), (inr t2, inr t3)). compute. assumption. Defined. 

Lemma A_bs_right_sum_left_sum_not_right_distributive_v4 (t : T) : 
  A_bs_not_right_absorptive rS addS mulS →
         A_bs_not_right_distributive (rS [+] rT) (addS [+> addT) (mulS <+] mulT).
Proof. intros [ [s1 s2] Pt]. exists ((inl s1), (inr t, inl s2)). compute. assumption. Defined. 

Definition A_bs_right_sum_left_sum_right_distributive_decide 
  (idm_d : bop_idempotent_decidable S rS addS)
  (ldS_d : A_bs_right_distributive_decidable rS addS mulS)
  (ldT_d : A_bs_right_distributive_decidable rT addT mulT)
  (lla_d : A_bs_right_absorptive_decidable rS addS mulS) : 
         A_bs_right_distributive_decidable (rS [+] rT) (addS [+> addT) (mulS <+] mulT) := 
match idm_d with                                                                                  
| inl idm  =>
    match ldS_d with
    | inl ldS  =>
        match ldT_d with
        | inl ldT  =>
            match lla_d with
            | inl lla  => inl (A_bs_right_sum_left_sum_right_distributive idm ldS ldT lla)
            | inr nlla => inr (A_bs_right_sum_left_sum_not_right_distributive_v4 wT nlla)
            end 
        | inr nldT => inr (A_bs_right_sum_left_sum_not_right_distributive_v3 nldT)
        end 
    | inr nldS => inr (A_bs_right_sum_left_sum_not_right_distributive_v2 nldS)
    end 
| inr nidm => inr (A_bs_right_sum_left_sum_not_right_distributive_v1 wT nidm)
end. 


Lemma A_bs_right_sum_left_sum_left_absorptive :
  bop_idempotent S rS addS →   
  A_bs_left_absorptive rS addS mulS →   
  A_bs_left_absorptive rT addT mulT →    
         A_bs_left_absorptive (rS [+] rT) (addS [+> addT) (mulS <+] mulT). 
Proof. intros idemS llaS llaT. unfold A_bs_left_absorptive.
       intros [s1 | t1] [s2 | t2]; compute.
       apply llaS. apply symS. apply idemS. apply refT. apply llaT.
Defined. 


Lemma A_bs_right_sum_left_sum_not_left_absorptive_v1 (t : T) :
  bop_not_idempotent S rS addS →   
         A_bs_not_left_absorptive (rS [+] rT) (addS [+> addT) (mulS <+] mulT). 
Proof. intros [s Ps]. exists (inl s, inr t). compute. rewrite (sym_as_rewrite symS). assumption. Defined. 

Lemma A_bs_right_sum_left_sum_not_left_absorptive_v2 :
  A_bs_not_left_absorptive rS addS mulS →   
         A_bs_not_left_absorptive (rS [+] rT) (addS [+> addT) (mulS <+] mulT). 
Proof. intros [[s1 s2] P]. exists (inl s1, inl s2). compute. assumption. Defined. 

Lemma A_bs_right_sum_left_sum_not_left_absorptive_v3 :
  A_bs_not_left_absorptive rT addT mulT →   
         A_bs_not_left_absorptive (rS [+] rT) (addS [+> addT) (mulS <+] mulT). 
Proof. intros [[t1 t2] P]. exists (inr t1, inr t2). compute. assumption. Defined. 


Definition A_bs_right_sum_left_sum_left_absorptive_decide 
  (idm_d : bop_idempotent_decidable S rS addS)
  (llaS_d : A_bs_left_absorptive_decidable rS addS mulS) 
  (llaT_d : A_bs_left_absorptive_decidable rT addT mulT) : 
         A_bs_left_absorptive_decidable (rS [+] rT) (addS [+> addT) (mulS <+] mulT) := 
match idm_d with                                                                                  
| inl idm  => match llaS_d with
              | inl llaS  => match llaT_d with
                            | inl llaT  => inl _ (A_bs_right_sum_left_sum_left_absorptive idm llaS llaT)
                            | inr nllaT => inr _ (A_bs_right_sum_left_sum_not_left_absorptive_v3 nllaT)
                            end 
              | inr nllaS => inr _ (A_bs_right_sum_left_sum_not_left_absorptive_v2 nllaS)
              end 
| inr nidm => inr _ (A_bs_right_sum_left_sum_not_left_absorptive_v1 wT nidm)
end. 

Lemma A_bs_right_sum_left_sum_right_absorptive :
  bop_idempotent S rS addS →   
  A_bs_right_absorptive rS addS mulS →   
  A_bs_right_absorptive rT addT mulT →      
         A_bs_right_absorptive (rS [+] rT) (addS [+> addT) (mulS <+] mulT). 
Proof. intros idemS lraS lraT. unfold A_bs_right_absorptive.
       intros [s1 | t1] [s2 | t2]; compute.
       apply lraS. apply symS. apply idemS. apply refT. apply lraT.
Defined.        

Lemma A_bs_right_sum_left_sum_not_right_absorptive_v1 (t : T) :
  bop_not_idempotent S rS addS →   
         A_bs_not_right_absorptive (rS [+] rT) (addS [+> addT) (mulS <+] mulT). 
Proof. intros [s Ps]. exists (inl s, inr t). compute. rewrite (sym_as_rewrite symS). assumption. Defined. 

Lemma A_bs_right_sum_left_sum_not_right_absorptive_v2 :
  A_bs_not_right_absorptive rS addS mulS →   
         A_bs_not_right_absorptive (rS [+] rT) (addS [+> addT) (mulS <+] mulT). 
Proof. intros [[s1 s2] P]. exists (inl s1, inl s2). compute. assumption. Defined. 

Lemma A_bs_right_sum_left_sum_not_right_absorptive_v3 :
  A_bs_not_right_absorptive rT addT mulT →   
         A_bs_not_right_absorptive  (rS [+] rT) (addS [+> addT) (mulS <+] mulT). 
Proof. intros [[t1 t2] P]. exists (inr t1, inr t2). compute. assumption. Defined. 

Definition A_bs_right_sum_left_sum_right_absorptive_decide :
  bop_idempotent_decidable S rS addS →
  A_bs_right_absorptive_decidable rS addS mulS →   
  A_bs_right_absorptive_decidable rT addT mulT →    
         A_bs_right_absorptive_decidable (rS [+] rT) (addS [+> addT) (mulS <+] mulT)
:= λ idm_d llaS_d llaT_d,
match idm_d with                                                                                  
| inl idm  => match llaS_d with
              | inl llaS  => match llaT_d with
                            | inl llaT  => inl _ (A_bs_right_sum_left_sum_right_absorptive idm llaS llaT)
                            | inr nllaT => inr _ (A_bs_right_sum_left_sum_not_right_absorptive_v3 nllaT)
                            end 
              | inr nllaS => inr _ (A_bs_right_sum_left_sum_not_right_absorptive_v2 nllaS)
              end 
| inr nidm => inr _ (A_bs_right_sum_left_sum_not_right_absorptive_v1 wT nidm)
end. 

End RightLeft.                                                                            

End Theory.

Section ACAS.
                                                                             
Definition A_bs_left_sum_right_sum_properties 
  {S T: Type} 
  (rS : brel S) 
  (rT : brel T) 
  (plusS timesS : binary_op S) 
  (plusT timesT : binary_op T) (s : S) (t : T)
  (eqvS : eqv_proofs S rS)
  (eqvT : eqv_proofs T rT)
  (sgT : sg_C_proofs T rT plusT)
  (pS : A_bs_properties rS plusS timesS)
  (pT : A_bs_properties rT plusT timesT): 
        A_bs_properties
           (brel_sum rS rT) 
           (bop_left_sum plusS plusT)
           (bop_right_sum timesS timesT) := 
{|
  A_bs_left_distributive_d :=
    A_bs_left_sum_right_sum_left_distributive_decide S T rS rT s plusS timesS plusT timesT
        (A_eqv_reflexive S rS eqvS)                                                      
        (A_eqv_reflexive T rT eqvT)                                                      
        (A_eqv_symmetric T rT eqvT)
        (A_eqv_transitive T rT eqvT)
        (A_sg_C_commutative T rT plusT sgT)
        (A_sg_C_idempotent_d T rT plusT sgT)
        (A_bs_left_distributive_d rS plusS timesS pS)
        (A_bs_left_distributive_d rT plusT timesT pT)
        (A_bs_left_absorptive_d rT plusT timesT pT)

; A_bs_right_distributive_d := 
    A_bs_left_sum_right_sum_right_distributive_decide S T rS rT s plusS timesS plusT timesT
        (A_eqv_reflexive S rS eqvS)                                                      
        (A_eqv_reflexive T rT eqvT)                                                      
        (A_eqv_symmetric T rT eqvT)
        (A_eqv_transitive T rT eqvT)
        (A_sg_C_commutative T rT plusT sgT)
        (A_sg_C_idempotent_d T rT plusT sgT)
        (A_bs_right_distributive_d rS plusS timesS pS)
        (A_bs_right_distributive_d rT plusT timesT pT)
        (A_bs_right_absorptive_d rT plusT timesT pT)

; A_bs_left_absorptive_d := 
    A_bs_left_sum_right_sum_left_absorptive_decide S T rS rT s plusS timesS plusT timesT
        (A_eqv_reflexive S rS eqvS)                                                      
        (A_eqv_symmetric T rT eqvT)                                                      
        (A_sg_C_idempotent_d T rT plusT sgT)
        (A_bs_left_absorptive_d rS plusS timesS pS)
        (A_bs_left_absorptive_d rT plusT timesT pT)        

; A_bs_right_absorptive_d := 
    A_bs_left_sum_right_sum_right_absorptive_decide S T rS rT s plusS timesS plusT timesT
        (A_eqv_reflexive S rS eqvS)                                                      
        (A_eqv_symmetric T rT eqvT)                                                      
        (A_sg_C_idempotent_d T rT plusT sgT)
        (A_bs_right_absorptive_d rS plusS timesS pS)
        (A_bs_right_absorptive_d rT plusT timesT pT)        

|}.



Definition A_bs_left_sum_right_sum {S T : Type} (bsS : @A_bs S) (bsT : @A_bs T) : @A_bs (S + T) := 
let eqvS   := A_bs_eqv bsS   in
let eqvT   := A_bs_eqv bsT   in
let peqvS  := A_eqv_proofs S eqvS in
let refS   := A_eqv_reflexive _ _ peqvS in 
let peqvT  := A_eqv_proofs T eqvT in
let refT   := A_eqv_reflexive _ _ peqvT in 
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
     A_bs_eqv         := A_eqv_sum S T eqvS eqvT 
   ; A_bs_plus        := bop_left_sum plusS plusT 
   ; A_bs_times       := bop_right_sum timesS timesT 
   ; A_bs_plus_props := sg_C_proofs_left_sum S T rS rT plusS plusT s f t g Pf Pg peqvS peqvT 
                           (A_bs_plus_props bsS) 
                           (A_bs_plus_props bsT) 
   ; A_bs_times_props := sg_proofs_right_sum S T rS rT timesS timesT s f t g Pf Pg peqvS peqvT 
                           (A_bs_times_props bsS) 
                           (A_bs_times_props bsT)
   ; A_bs_id_ann_props := A_left_sum_right_sum_id_ann_properties  S T rS rT s t plusS timesS plusT timesT refS refT 
                           (A_bs_id_ann_props bsS) 
                           (A_bs_id_ann_props bsT)                                                  
   ; A_bs_props    := A_bs_left_sum_right_sum_properties rS rT plusS timesS plusT timesT s t peqvS peqvT 
                           (A_bs_plus_props bsT)                            
                           (A_bs_props bsS) 
                           (A_bs_props bsT)
   ; A_bs_ast        := Ast_bs_left_sum_right_sum(A_bs_ast bsS, A_bs_ast bsT)
|}. 




Definition A_bs_right_sum_left_sum_properties 
    {S T : Type} 
    (rS : brel S) 
    (rT : brel T) 
    (plusS timesS : binary_op S) 
    (plusT timesT : binary_op T) (s : S) (t : T)
    (eqvS : eqv_proofs S rS)
    (eqvT : eqv_proofs T rT)
    (sgS : sg_C_proofs S rS plusS) 
    (sgT : sg_C_proofs T rT plusT)
    (pS : A_bs_properties rS plusS timesS)
    (pT : A_bs_properties  rT plusT timesT):
       A_bs_properties 
                  (brel_sum rS rT)
                  (bop_right_sum plusS plusT)                  
                  (bop_left_sum timesS timesT) := 
{|
  A_bs_left_distributive_d :=
    A_bs_right_sum_left_sum_left_distributive_decide S T rS rT t plusS timesS plusT timesT
        (A_eqv_reflexive S rS eqvS)
        (A_eqv_symmetric S rS eqvS)
        (A_eqv_transitive S rS eqvS)
        (A_eqv_reflexive T rT eqvT)
        (A_sg_C_commutative S rS plusS sgS)
        (A_sg_C_idempotent_d S rS plusS sgS)
        (A_bs_left_distributive_d rS plusS timesS pS)
        (A_bs_left_distributive_d rT plusT timesT pT)
        (A_bs_left_absorptive_d rS plusS timesS pS)

; A_bs_right_distributive_d := 
    A_bs_right_sum_left_sum_right_distributive_decide S T rS rT t plusS timesS plusT timesT
        (A_eqv_reflexive S rS eqvS)
        (A_eqv_symmetric S rS eqvS)
        (A_eqv_transitive S rS eqvS)
        (A_eqv_reflexive T rT eqvT)
        (A_sg_C_commutative S rS plusS sgS)
        (A_sg_C_idempotent_d S rS plusS sgS)
        (A_bs_right_distributive_d rS plusS timesS pS)
        (A_bs_right_distributive_d rT plusT timesT pT)
        (A_bs_right_absorptive_d rS plusS timesS pS)

; A_bs_left_absorptive_d := 
    A_bs_right_sum_left_sum_left_absorptive_decide S T rS rT t plusS timesS plusT timesT
        (A_eqv_symmetric S rS eqvS)                                                      
        (A_eqv_reflexive T rT eqvT)                                                      
        (A_sg_C_idempotent_d S rS plusS sgS)
        (A_bs_left_absorptive_d rS plusS timesS pS)
        (A_bs_left_absorptive_d rT plusT timesT pT)        

; A_bs_right_absorptive_d := 
    A_bs_right_sum_left_sum_right_absorptive_decide S T rS rT t plusS timesS plusT timesT
        (A_eqv_symmetric S rS eqvS)                                                      
        (A_eqv_reflexive T rT eqvT)                                                      
        (A_sg_C_idempotent_d S rS plusS sgS)
        (A_bs_right_absorptive_d rS plusS timesS pS)
        (A_bs_right_absorptive_d rT plusT timesT pT)        
|}.




Definition A_right_sum_left_sum_id_ann_properties 
           (S T : Type) (rS : brel S) (rT : brel T) (wS : S) (wT : T) 
           (addS mulS : binary_op S) (addT mulT : binary_op T)
           (refS : brel_reflexive S rS) 
           (refT : brel_reflexive T rT) 
           (pS : A_bs_id_ann_properties rS addS mulS)
           (pT : A_bs_id_ann_properties rT addT mulT) : 
  A_bs_id_ann_properties (brel_sum rS rT) (bop_right_sum addS addT) (bop_left_sum mulS mulT) := 
let PS1 := A_id_ann_plus_times_d _ _ _ pS in
let PT1 := A_id_ann_times_plus_d _ _ _ pT in   
{|
  A_id_ann_plus_times_d := A_bs_right_sum_left_sum_exists_id_ann_decide _ _ _ _ wS _ _ _ _ refS refT PS1
; A_id_ann_times_plus_d := A_bs_left_sum_right_sum_exists_id_ann_decide _ _ _ _ wT _ _ _ _ refS refT PT1
|}.



Definition A_bs_right_sum_left_sum {S T : Type} (bsS : @A_bs S) (bsT : @A_bs T) : @A_bs (S + T) := 
let eqvS   := A_bs_eqv bsS   in
let eqvT   := A_bs_eqv bsT   in
let peqvS  := A_eqv_proofs S eqvS in
let refS   := A_eqv_reflexive _ _ peqvS in 
let peqvT  := A_eqv_proofs T eqvT in
let refT   := A_eqv_reflexive _ _ peqvT in 
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
     A_bs_eqv        := A_eqv_sum S T eqvS eqvT 
   ; A_bs_plus       := bop_right_sum plusS plusT 
   ; A_bs_times       := bop_left_sum timesS timesT 
   ; A_bs_plus_props := sg_C_proofs_right_sum S T rS rT plusS plusT s f t g Pf Pg peqvS peqvT 
                           (A_bs_plus_props bsS) 
                           (A_bs_plus_props bsT) 
   ; A_bs_times_props := sg_proofs_left_sum S T rS rT timesS timesT s f t g Pf Pg peqvS peqvT 
                           (A_bs_times_props bsS) 
                           (A_bs_times_props bsT)
   ; A_bs_id_ann_props := A_right_sum_left_sum_id_ann_properties S T rS rT s t plusS timesS plusT timesT refS refT 
                           (A_bs_id_ann_props bsS) 
                           (A_bs_id_ann_props bsT)                                                  
   ; A_bs_props    := A_bs_right_sum_left_sum_properties rS rT plusS timesS plusT timesT s t peqvS peqvT 
                           (A_bs_plus_props bsS)
                           (A_bs_plus_props bsT)                                                                                
                           (A_bs_props bsS) 
                           (A_bs_props bsT)
   ; A_bs_ast        := Ast_bs_right_sum_left_sum(A_bs_ast bsS, A_bs_ast bsT)
|}. 

End ACAS.

Section AMCAS.

Open Scope list_scope.


Definition A_bs_left_sum_right_sum_below_bs {S T : Type} (A : @A_below_bs S)  (B : @A_below_bs T)  : @A_below_bs (S + T) :=
    A_classify_bs (A_bs_left_sum_right_sum (A_cast_up_bs A) (A_cast_up_bs B)).

  
  Definition A_mcas_bs_left_sum_right_sum {S T : Type} (A : @A_bs_mcas S)  (B : @A_bs_mcas T)  : @A_bs_mcas (S + T) :=
    match A, B with
    | A_MCAS_bs A', A_MCAS_bs B'               => A_MCAS_bs (A_bs_left_sum_right_sum_below_bs A' B')
    | A_MCAS_bs_Error sl1, A_MCAS_bs_Error sl2 => A_MCAS_bs_Error (sl1 ++ sl2)
    | A_MCAS_bs_Error sl1, _                   => A_MCAS_bs_Error sl1
    | _,  A_MCAS_bs_Error sl2                  => A_MCAS_bs_Error sl2
    end.

  Definition A_bs_right_sum_left_sum_below_bs {S T : Type} (A : @A_below_bs S)  (B : @A_below_bs T)  : @A_below_bs (S + T) :=
    A_classify_bs (A_bs_right_sum_left_sum (A_cast_up_bs A) (A_cast_up_bs B)).
  
  Definition A_mcas_bs_right_sum_left_sum {S T : Type} (A : @A_bs_mcas S)  (B : @A_bs_mcas T)  : @A_bs_mcas (S + T) :=
    match A, B with
    | A_MCAS_bs A', A_MCAS_bs B'               => A_MCAS_bs (A_bs_right_sum_left_sum_below_bs A' B')
    | A_MCAS_bs_Error sl1, A_MCAS_bs_Error sl2 => A_MCAS_bs_Error (sl1 ++ sl2)
    | A_MCAS_bs_Error sl1, _                   => A_MCAS_bs_Error sl1
    | _,  A_MCAS_bs_Error sl2                  => A_MCAS_bs_Error sl2
    end.
  
End AMCAS.  


Section CAS.
(*

Definition bop_left_sum_right_sum_left_distributive_check (S T : Type) (wS : S) :
  @check_idempotent T →
  @check_left_distributive S →
  @check_left_distributive T →   
  @check_left_absorptive T →
  @check_right_left_absorptive T →  @check_left_distributive (S + T) 
:= λ idm_d ldS_d ldT_d lla_d rla_d,
match idm_d with                                                                                  
| Certify_Idempotent  =>
  match ldS_d with
  | Certify_Left_Distributive  =>
    match ldT_d with
    | Certify_Left_Distributive  =>
      match lla_d with
      | Certify_Left_Left_Absorptive  =>
        match rla_d with
        | Certify_Right_Left_Absorptive   => Certify_Left_Distributive
        | Certify_Not_Right_Left_Absorptive (t1, t2)  => Certify_Not_Left_Distributive (inr t1, (inr t2, inl wS))
        end 
      | Certify_Not_Left_Left_Absorptive (t1, t2) => Certify_Not_Left_Distributive (inr t1, (inl wS, inr t2))
      end 
    | Certify_Not_Left_Distributive (t1, (t2, t3)) => Certify_Not_Left_Distributive (inr t1, (inr t2, inr t3))
    end 
  | Certify_Not_Left_Distributive (s1, (s2, s3)) => Certify_Not_Left_Distributive (inl s1, (inl s2, inl s3))
  end
| Certify_Not_Idempotent t => Certify_Not_Left_Distributive (inr t, (inl wS, inl wS))
end. 



Definition bop_right_sum_left_sum_right_distributive_check (S T : Type) (wS : S) :
  @check_idempotent T →
  @check_right_distributive S →
  @check_right_distributive T →   
  @check_right_absorptive T →
  @check_right_right_absorptive T →  @check_right_distributive (S + T) 
:= λ idm_d ldS_d ldT_d lla_d rla_d,
match idm_d with                                                                                  
| Certify_Idempotent  =>
  match ldS_d with
  | Certify_Right_Distributive  =>
    match ldT_d with
    | Certify_Right_Distributive  =>
      match lla_d with
      | Certify_Left_Right_Absorptive  =>
        match rla_d with
        | Certify_Right_Right_Absorptive   => Certify_Right_Distributive
        | Certify_Not_Right_Right_Absorptive (t1, t2)  => Certify_Not_Right_Distributive (inr t1, (inr t2, inl wS))
        end 
      | Certify_Not_Left_Right_Absorptive (t1, t2) => Certify_Not_Right_Distributive (inr t1, (inl wS, inr t2))
      end 
    | Certify_Not_Right_Distributive (t1, (t2, t3)) => Certify_Not_Right_Distributive (inr t1, (inr t2, inr t3))
    end 
  | Certify_Not_Right_Distributive (s1, (s2, s3)) => Certify_Not_Right_Distributive (inl s1, (inl s2, inl s3))
  end
| Certify_Not_Idempotent t => Certify_Not_Right_Distributive (inr t, (inl wS, inl wS))
end.


Definition bop_right_sum_left_sum_left_absorptive_check (S T : Type) (wS : S) :
  @check_idempotent T →
  @check_left_absorptive S →
  @check_left_absorptive T →  @check_left_absorptive (S + T)
:= λ idm_d llaS_d llaT_d,
match idm_d with                                                                                  
| Certify_Idempotent =>
  match llaS_d with
  | Certify_Left_Left_Absorptive =>
    match llaT_d with
    | Certify_Left_Left_Absorptive  => Certify_Left_Left_Absorptive
    | Certify_Not_Left_Left_Absorptive  (t1, t2) => Certify_Not_Left_Left_Absorptive (inr t1, inr t2)
    end 
  | Certify_Not_Left_Left_Absorptive (s1, s2) => Certify_Not_Left_Left_Absorptive (inl s1, inl s2)
  end 
| Certify_Not_Idempotent t  => Certify_Not_Left_Left_Absorptive (inr t, inl wS) 
end. 



Definition bop_right_sum_left_sum_right_absorptive_check (S T : Type) (wS : S) :
  @check_idempotent T →
  @check_right_absorptive S →
  @check_right_absorptive T →  @check_right_absorptive (S + T)
:= λ idm_d llaS_d llaT_d,
match idm_d with                                                                                  
| Certify_Idempotent =>
  match llaS_d with
  | Certify_Left_Right_Absorptive =>
    match llaT_d with
    | Certify_Left_Right_Absorptive  => Certify_Left_Right_Absorptive
    | Certify_Not_Left_Right_Absorptive  (t1, t2) => Certify_Not_Left_Right_Absorptive (inr t1, inr t2)
    end 
  | Certify_Not_Left_Right_Absorptive (s1, s2) => Certify_Not_Left_Right_Absorptive (inl s1, inl s2)
  end 
| Certify_Not_Idempotent t  => Certify_Not_Left_Right_Absorptive (inr t, inl wS) 
end. 

Definition bop_right_sum_left_sum_right_left_absorptive_check (S T : Type) (wS : S) :
  @check_idempotent T →
  @check_right_left_absorptive S →
  @check_right_left_absorptive T →  @check_right_left_absorptive (S + T)
:= λ idm_d llaS_d llaT_d,
match idm_d with                                                                                  
| Certify_Idempotent =>
  match llaS_d with
  | Certify_Right_Left_Absorptive =>
    match llaT_d with
    | Certify_Right_Left_Absorptive  => Certify_Right_Left_Absorptive
    | Certify_Not_Right_Left_Absorptive  (t1, t2) => Certify_Not_Right_Left_Absorptive (inr t1, inr t2)
    end 
  | Certify_Not_Right_Left_Absorptive (s1, s2) => Certify_Not_Right_Left_Absorptive (inl s1, inl s2)
  end 
| Certify_Not_Idempotent t  => Certify_Not_Right_Left_Absorptive (inr t, inl wS) 
end. 

Definition bop_right_sum_left_sum_right_right_absorptive_check (S T : Type) (wS : S) :
  @check_idempotent T →
  @check_right_right_absorptive S →
  @check_right_right_absorptive T →  @check_right_right_absorptive (S + T)
:= λ idm_d llaS_d llaT_d,
match idm_d with                                                                                  
| Certify_Idempotent =>
  match llaS_d with
  | Certify_Right_Right_Absorptive =>
    match llaT_d with
    | Certify_Right_Right_Absorptive  => Certify_Right_Right_Absorptive
    | Certify_Not_Right_Right_Absorptive  (t1, t2) => Certify_Not_Right_Right_Absorptive (inr t1, inr t2)
    end 
  | Certify_Not_Right_Right_Absorptive (s1, s2) => Certify_Not_Right_Right_Absorptive (inl s1, inl s2)
  end 
| Certify_Not_Idempotent t  => Certify_Not_Right_Right_Absorptive (inr t, inl wS) 
end. 
*) 
End CAS.  

Section MCAS.
End MCAS.

Section Verify.

Section Decide.
End Decide.     

Section Combinators.
End Combinators.   
End Verify.  



