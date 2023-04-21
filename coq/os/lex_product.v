Require Import Coq.Bool.Bool.

Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.

Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.eqv.product.

Require Import CAS.coq.po.properties.
Require Import CAS.coq.po.structures.
Require Import CAS.coq.po.theory.
Require Import CAS.coq.po.lex. 

Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures.
Require Import CAS.coq.sg.theory. 
Require Import CAS.coq.sg.product.
Require Import CAS.coq.sg.and.
Require Import CAS.coq.sg.or. 

Require Import CAS.coq.os.properties.
Require Import CAS.coq.os.structures.

Definition bop_qo_left_cancellative (S : Type) (lte : brel S) (b : binary_op S)
    := ∀ s t u : S, equiv lte (b s t) (b s u) = true -> (equiv lte t u = true) + (incomp lte t u = true).

Definition bop_not_qo_left_cancellative (S : Type) (lte : brel S) (b : binary_op S)
  := { z : S * (S * S) &
           match z with (s, (t, u)) =>
                        (equiv lte (b s t) (b s u) = true) *
                        (((lte t u = true) * (lte u t = false))
                           +
                         ((lte t u = false) * (lte u t = true)))
           end }. 

Definition bop_qo_left_constant (S : Type) (lte : brel S) (b : binary_op S)
    := ∀ s t u : S, equiv lte (b s t) (b s u) = true. 

Definition bop_not_qo_left_constant (S : Type) (lte : brel S) (b : binary_op S)
   := { z : S * (S * S) & match z with (s, (t, u)) => equiv lte (b s t) (b s u) = false  end }. 

                                           
Section Theory.

Variable S  : Type. 
Variable T  : Type. 
Variable eqS : brel S. 
Variable eqT : brel T.

Variable conS : brel_congruence S eqS eqS. 
Variable refS : brel_reflexive S eqS.
Variable symS : brel_symmetric S eqS.  
Variable tranS : brel_transitive S eqS.
Variable conT : brel_congruence T eqT eqT. 
Variable refT : brel_reflexive T eqT.
Variable symT : brel_symmetric T eqT.  
Variable tranT : brel_transitive T eqT.

Variable wS : S. 
Variable wT : T.

Variable lteS : brel S.
Variable lteT : brel T.

Variable cong_lteS : brel_congruence S eqS lteS.
Variable ref_lteS  : brel_reflexive S lteS.
Variable cong_lteT : brel_congruence T eqT lteT.
Variable ref_lteT  : brel_reflexive T lteT.

Variable mulS : binary_op S. 
Variable mulT : binary_op T.

Variable m_conS : bop_congruence S eqS mulS.
Variable m_conT : bop_congruence T eqT mulT.

Notation "a =S b"  := (eqS a b = true) (at level 15).
Notation "a =T b"  := (eqT a b = true) (at level 15).
Notation "a *S b"  := (mulS a b) (at level 15).
Notation "a *T b"  := (mulT a b) (at level 15).

Notation "a <*> b" := (brel_product a b) (at level 15).
Notation "a [<=] b" := (brel_left_lex lteS lteT a b) (at level 15).
Notation "a [*] b" := (bop_product a b) (at level 15).


Lemma os_left_lex_product_left_monotone
 (LMS : os_left_monotone lteS mulS)
 (LMT : os_left_monotone lteT mulT)
 (D : (bop_qo_left_cancellative S lteS mulS) + (bop_qo_left_constant T lteT mulT)): 
  os_left_monotone (brel_left_lex lteS lteT) (mulS [*] mulT). 
Proof. intros [s1 t1] [s2 t2] [s3 t3] A. simpl.
       unfold brel_left_lex in A.
       apply bop_or_intro.
       apply bop_or_elim in A. destruct A as [A | A].
       + apply below_elim in A. destruct A as [L R].
         destruct D as [LC | LK].         
         ++ left. apply below_intro.
            +++ apply LMS; auto.
            +++ unfold bop_qo_left_cancellative in LC.
                case_eq(equiv lteS (s1 *S s3) (s1 *S s2)); intro A.
                ++++ destruct (LC _ _ _ A) as [B | B].
                     +++++ apply equiv_elim in B. destruct B as [B C].
                           rewrite C in R. discriminate R. 
                      +++++ apply incomp_elim in B.
                            destruct B as [B C].
                            rewrite B in L. discriminate L.                            
                ++++ apply equiv_false_elim in A.
                     destruct A as [A | A].
                     +++++ rewrite (LMS s1 s2 s3 L) in A. discriminate A. 
                     +++++ exact A. 
         ++ case_eq(below lteS (s1 *S s3) (s1 *S s2)); intro N. 
            +++ left; auto. 
            +++ apply below_false_elim in N. 
                right.
                apply bop_and_intro.
                ++++ apply equiv_intro.
                     +++++ destruct N as [N | N].
                           ++++++ rewrite (LMS s1 _ _ L) in N. discriminate N. 
                           ++++++ exact N.                       
                     +++++ apply LMS; auto. 
                ++++ assert (A := LK t1 t2 t3).
                     apply equiv_elim in A. destruct A as [A B].
                     exact B. 
       + apply bop_and_elim in A. destruct A as [A B].
         apply equiv_elim in A. destruct A as [L R].
         right. apply bop_and_intro.
         ++ apply equiv_intro.
            +++ apply LMS; auto. 
            +++ apply LMS; auto. 
         ++ apply LMT; auto. 
Qed. 

Lemma os_left_lex_product_not_left_monotone_v1
 (NLMS : os_not_left_monotone lteS mulS) : 
  os_not_left_monotone (brel_left_lex lteS lteT) (mulS [*] mulT). 
Proof. destruct NLMS as [[s1 [s2 s3]] [A B]].
       exists ((s1, wT), ((s2, wT), (s3, wT))).
       compute. rewrite A, B.
       case_eq(lteS s3 s2); intro C; auto. 
Defined.

Lemma os_left_lex_product_not_left_monotone_v2
 (NLMT : os_not_left_monotone lteT mulT) : 
  os_not_left_monotone (brel_left_lex lteS lteT) (mulS [*] mulT). 
Proof. destruct NLMT as [[t1 [t2 t3]] [A B]].
       exists ((wS, t1), ((wS, t2), (wS, t3))).
       compute. rewrite A, B, (ref_lteS wS), (ref_lteS (wS *S wS)). 
       auto. 
Defined.


Lemma os_left_lex_product_not_left_monotone_v3
 (LMS : os_left_monotone lteS mulS)
 (LMT : os_left_monotone lteT mulT)
 (NLC : bop_not_qo_left_cancellative S lteS mulS)
 (NLK : bop_not_qo_left_constant T lteT mulT) : 
  os_not_left_monotone (brel_left_lex lteS lteT) (mulS [*] mulT). 
Proof. destruct NLC as [[s1 [s2 s3]] [A B]].
       destruct NLK as [[t1 [t2 t3]] C].       
       apply equiv_elim in A. destruct A as [A1 A2].
       apply equiv_false_elim in C.
       destruct C as [C | C];
       destruct B as [[B1 B2] | [B1 B2]]. 
       + exists ((s1, t1), ((s2, t3), (s3, t2))).
         compute. rewrite B1, B2, A2, A1, C. auto. 
       + exists ((s1, t1), ((s3, t3), (s2, t2))).
         compute. rewrite A2, A1, B1, B2, C; auto. 
       + exists ((s1, t1), ((s2, t2), (s3, t3))).
         compute. rewrite A2, A1, B1, B2, C; auto.
       + exists ((s1, t1), ((s3, t2), (s2, t3))).
         compute. rewrite A2, A1, B1, B2, C; auto.
Qed.



Lemma os_left_lex_product_qo_left_cancellative 
      (LCS : bop_qo_left_cancellative S lteS mulS)
      (LCT : bop_qo_left_cancellative T lteT mulT):       
            bop_qo_left_cancellative _ (brel_left_lex lteS lteT) (mulS [*] mulT). 
Proof. intros [s1 t1] [s2 t2] [s3 t3] A.
       unfold bop_product in A.
       apply equiv_elim in A.
       destruct A as [A B].
       case_eq(equiv (brel_left_lex lteS lteT) (s2, t2) (s3, t3)); intro C. 
       + left. auto.
       + right. apply equiv_false_elim in C.
         destruct C as [C | C].
         ++ apply incomp_intro.
            +++ exact C. 
            +++ case_eq(equiv lteS (s1 *S s3) (s1 *S s2)); intro D.
                ++++ destruct (LCS _ _ _ D) as [E | E].
                     +++++ admit. 
                     +++++ admit. 
                ++++ apply equiv_false_elim in D.
                     admit. 
         ++ apply incomp_intro.
            +++ unfold brel_left_lex in A, B, C.
                unfold brel_left_lex.
                apply bop_or_false_elim in C.
                destruct C as [C D].
                apply below_false_elim in C.
                apply bop_and_false_elim in D. 
                apply bop_or_false_intro.
                ++++ apply below_false_intro.
                     admit. 
                ++++ apply bop_and_false_intro.
                     admit. 
            +++ exact C. 
Admitted.             
         
End Theory.
