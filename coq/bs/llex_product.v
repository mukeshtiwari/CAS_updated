Require Import Coq.Bool.Bool.

Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.

Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.eqv.product.

Require Import CAS.coq.po.properties.
Require Import CAS.coq.po.structures.
Require Import CAS.coq.po.theory.

Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures.
Require Import CAS.coq.sg.theory. 
Require Import CAS.coq.sg.product.
Require Import CAS.coq.sg.and. 
Require Import CAS.coq.sg.llex.

Require Import CAS.coq.bs.properties.
Require Import CAS.coq.bs.structures.



Section Theory.

Variable S  : Type. 
Variable T  : Type. 
Variable rS : brel S. 
Variable rT : brel T.

Variable wS : S. 
Variable wT : T.
Variable argT : T.

Variable addS  mulS : binary_op S. 
Variable addT mulT : binary_op T.


Variable conS : brel_congruence S rS rS. 
Variable refS : brel_reflexive S rS.
Variable symS : brel_symmetric S rS.  
Variable tranS : brel_transitive S rS.


Variable conT : brel_congruence T rT rT. 
Variable refT : brel_reflexive T rT.
Variable symT : brel_symmetric T rT.  
Variable tranT : brel_transitive T rT.

Variable a_conS : bop_congruence S rS addS.
Variable m_conS : bop_congruence S rS mulS.
Variable a_conT : bop_congruence T rT addT.
Variable m_conT : bop_congruence T rT mulT.

Variable a_commS : bop_commutative S rS addS.
Variable a_idemS : bop_idempotent S rS addS.

Notation "a =S b"  := (rS a b = true) (at level 15).
Notation "a =T b"  := (rT a b = true) (at level 15).
Notation "a +S b"  := (addS a b) (at level 15).
Notation "a +T b"  := (addT a b) (at level 15).
Notation "a *S b"  := (mulS a b) (at level 15).
Notation "a *T b"  := (mulT a b) (at level 15).

Notation "a <*> b" := (brel_product a b) (at level 15).
Notation "a [+] b" := (bop_llex argT rS a b) (at level 15).
Notation "a [*] b" := (bop_product a b) (at level 15).
Notation "[| p1 | a | c | b | d |]" := (llex_p2 argT rS addT p1 a c b d) (at level 15).

(*
Lemma bop_llex_product_left_monotone : 
  bop_left_monotone S rS addS mulS → bop_left_monotone T rT addT mulT →
  bop_left_cancellative S rS mulS →
             bop_left_monotone (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT). 
Proof. intros ldS ldT lcS [s1 t1] [s2 t2] [s3 t3]. 
       unfold bop_product, bop_llex, brel_product. intro A. apply andb_is_true_left in A. destruct A as [A B]. 
       apply andb_true_intro. split.  
       apply ldS.
       case_eq(rS s2 s3); intro H1;        
       case_eq(rS s2 (s2 +S s3)); intro H2; auto.
          rewrite H2 in A. discriminate A. 
          rewrite H2 in A. discriminate A. 

       case_eq(rS s2 s3); intro H1;        
       case_eq(rS (s1 *S s2) (s1 *S s3)); intro H2; auto.
          rewrite H1 in B. apply ldT; auto. 
          rewrite H1 in B. compute. rewrite H2.
             case_eq(rS (s1 *S s2) ((s1 *S s2) +S (s1 *S s3))); intro H3; auto.             
                assert (C := m_conS _ _ _ _ (refS s1) H1). rewrite C in H2. discriminate H2. 
          rewrite H1 in B. apply lcS in H2. rewrite H2 in H1. discriminate H1. 
          rewrite H1 in B. compute. rewrite H2. 
             case_eq(rS (s1 *S s2) ((s1 *S s2) +S (s1 *S s3))); intro H3; auto.
                rewrite (ldS s1 s2 s3 A) in H3. discriminate H3. 
Qed. 

Lemma bop_llex_product_not_left_monotone_v1 (selS : bop_selective S rS addS ) : 
  bop_not_left_monotone S rS addS mulS → 
         bop_not_left_monotone (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT). 
Proof. intros [ [s1 [s2 s3]] [A B] ].
       exists ((s1, wT), ((s2, wT), (s3, wT))); compute. rewrite A, B.
       split; auto. case_eq(rS s2 s3); intro C; auto.
          assert (D := bop_selective_implies_idempotent _ _ _ selS (s1 *S s2)). 
          apply symS in D. 
          assert (E : ((s1 *S s2) +S (s1 *S s2)) =S ((s1 *S s2) +S (s1 *S s3))).
             assert (F : (s1 *S s2) =S (s1 *S s3)). exact (m_conS _ _ _ _ (refS s1) C).
             exact (a_conS _ _ _ _ (refS (s1 *S s2)) F). 
          rewrite (tranS _ _ _ D E) in B. discriminate B. 
Defined.        


Lemma bop_llex_product_not_left_monotone_v2 (selS : bop_selective S rS addS ) : 
  bop_not_left_monotone T rT addT mulT → 
         bop_not_left_monotone (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT). 
Proof. intros [ [t1 [t2 t3]] [A B] ].
       exists ((wS, t1), ((wS, t2), (wS, t3))); compute. 
       split; auto. rewrite (refS wS).
       assert (C : wS =S (wS +S wS)).
          destruct (selS wS wS) as [D | D]; apply symS; auto. 
       rewrite C; auto. 
       rewrite (refS ((wS *S wS))).
       assert (C : (wS *S wS) =S ((wS *S wS) +S (wS *S wS))).
          destruct (selS (wS *S wS) (wS *S wS)) as [D | D]; apply symS; auto.        
       rewrite C; auto. 
Defined.


Lemma bop_llex_product_not_left_monotone_v3 (selS : bop_selective S rS addS ) :
  bop_not_left_cancellative S rS mulS →
  bop_not_left_monotone (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT).
Proof. intros [[s1 [s2 s3]] [A B]].
       exists ((s1, wT), ((s2, wT), (s3, wT))); compute. rewrite A, B. 
       case_eq(rS s2 (s2 +S s3)); intro C. 
          rewrite refT. split; auto.
          case_eq(rS (s1 *S s2) ((s1 *S s2) +S (s1 *S s3))); intro D; auto. 
             admit. 
          destruct (selS s2 s3) as [D | D].
             apply symS in D. rewrite D in C. discriminate C.
             admit. 
Admitted.

Lemma bop_llex_product_not_left_monotone_v4 (selS : bop_selective S rS addS ) :
  bop_not_left_constant T rT mulT →  
  bop_not_left_monotone (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT).
Proof. intros [[t1 [t2 t3]] A].
       exists ((wS, t1), ((wS, t2), (wS, t3))); compute. 
       assert (B : rS wS (wS +S wS) = true). admit. 
       rewrite B. rewrite refS. rewrite refS. 
       assert (C : rS (wS *S wS) ((wS *S wS) +S (wS *S wS)) = true). admit. 
       rewrite C. 
Admitted. 


Lemma bop_llex_product_not_left_monotone_v5 (selS : bop_selective S rS addS ) :
  bop_not_left_cancellative S rS mulS →
  bop_not_left_constant T rT mulT →    
  bop_not_left_monotone (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT).
Proof. intros [[s1 [s2 s3]] [A B]] [[t1 [t2 t3]] C].
(*

  A : (s1 *S s2) =S (s1 *S s3)
  B : rS s2 s3 = false
  t1, t2, t3 : T
  C : rT (t1 *T t2) (t1 *T t3) = false
  
need (a, b) (c, d) (e, f) 

(c, d) = (c, d) + (e, f) 
AND 
(a, b)(c, d) <> (a, b)(c, d) + (a, b)(e, f) 
That is 
(ac, bd) <> (ac, bd) + (ae, bf)

try a = s1, c = s2, e = s3

(s2, d) = (s2, d) + (s3, f) 
AND 
(s1 s2, bd) <> (s1 s2 , bd) + (s1 s3, bf)
            =  (s1 s2  + s1 s3 , ???) 
            =  (s1 s2 , bd + bf) 
*) 
Admitted.              

 *)


(*
   need what structures to get a (pre-) path_algebra? 

   both with dist and absorption 

   (sg_CS, sg_CK) lex (sg_CI, sg) 

   (sg_CI, sg_CK, pid_is_tann) lex (sg_CI, sg) 
           ^^^^                     
           want anti-left, -right
*) 

Lemma bop_llex_product_left_distributive 
      (selS_or_annT : bop_selective S rS addS + bop_is_ann T rT mulT argT)
      (ldS : bop_left_distributive S rS addS mulS)
      (ldT : bop_left_distributive T rT addT mulT)
      (D : (bop_left_cancellative S rS mulS) + (bop_left_constant T rT mulT)) : 
         bop_left_distributive (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT).
Proof. intros [s1 t1] [s2 t2] [s3 t3].
       unfold bop_product, bop_llex, brel_product.
       apply bop_and_intro. 
       apply ldS. 
       unfold llex_p2.
       case_eq(rS s2 (s2 +S s3)); intro H2; 
       case_eq(rS (s1 *S s2) ((s1 *S s2) +S (s1 *S s3))); intro H4; simpl. 
       - case_eq(rS (s2 +S s3) s3); intro H1; case_eq(rS ((s1 *S s2) +S (s1 *S s3)) (s1 *S s3)); intro H3. 
         + apply ldT. 
         + assert (F1 := tranS _ _ _ H2 H1).
           assert (F2 := a_idemS (s1 *S s3)). 
           assert (F3 := m_conS _ _ _ _ (refS s1) F1). 
           assert (F4 := a_conS _ _ _ _ F3 (refS ((s1 *S s3)))). 
           assert (F5 := tranS _ _ _ F4 F2).
           rewrite F5 in H3. discriminate H3. 
         + destruct D as [LC | LK].
           * assert (F1 := ldS s1 s2 s3).
             assert (F2 := tranS _ _ _ F1 H3). 
             apply LC in F2. 
             assert (F3 := tranS _ _ _ H2 F2).
             assert (F4 := conS _ _ _ _ (refS (s2 +S s3)) F3). 
             rewrite <- F4 in H1. apply symS in H2.
             rewrite H2 in H1. discriminate H1.
           * assert (F1 := ldT t1 t2 t3).
             assert (F2 := LK t1 t2 (t2 +T t3)). 
             exact (tranT _ _ _ F2 F1). 
         + apply refT. 
       - case_eq(rS (s2 +S s3) s3); intro H1; case_eq(rS ((s1 *S s2) +S (s1 *S s3)) (s1 *S s3)); intro H3.
         + assert (F1 := tranS _ _ _ H2 H1). 
           assert (F2 := a_idemS (s1 *S s2)). 
           assert (F3 := m_conS _ _ _ _ (refS s1) F1). 
           assert (F4 := a_conS _ _ _ _ (refS (s1 *S s2)) F3). apply symS in F2.
           assert (F5 := tranS _ _ _ F2 F4). 
           rewrite F5 in H4. discriminate H4.
         + assert (F1 := ldS s1 s2 s3).
           assert (F2 := m_conS _ _ _ _ (refS s1) H1). apply symS in F1. 
           rewrite (tranS _ _ _ F1 F2) in H3. discriminate H3.            
         + destruct D as [LC | LK].
           * assert (F1 := ldS s1 s2 s3).
             assert (F2 := tranS _ _ _ F1 H3). 
             apply LC in F2. 
             rewrite F2 in H1. discriminate H1.
           * exact(LK t1 t2 t3). 
         + assert (F1 := ldS s1 s2 s3).
           assert (F2 := m_conS _ _ _ _ (refS s1) H2).
           assert (F3 := tranS _ _ _ F2 F1).            
           rewrite F3 in H4. discriminate H4.
       - case_eq(rS (s2 +S s3) s3); intro H1; case_eq(rS ((s1 *S s2) +S (s1 *S s3)) (s1 *S s3)); intro H3.
         + destruct D as [LC | LK].
           * assert (F1 := ldS s1 s2 s3). apply symS in F1. 
             assert (F2 := tranS _ _ _ H4 F1). 
             apply LC in F2.
             rewrite F2 in H2. discriminate H2.
           * assert (F1 := ldT t1 t2 t3).
             assert (F2 := LK t1 t3 (t2 +T t3)). 
             exact (tranT _ _ _ F2 F1). 
         + assert (F1 := ldS s1 s2 s3).
           assert (F2 := m_conS _ _ _ _ (refS s1) H1). apply symS in F1. 
           assert (F3 := tranS _ _ _ F1 F2).            
           rewrite F3 in H3. discriminate H3.
         + destruct D as [LC | LK].
           * assert (F1 := ldS s1 s2 s3). apply symS in F1. 
             assert (F2 := tranS _ _ _ H4 F1). 
             apply LC in F2.
             rewrite F2 in H2. discriminate H2.
           * assert (F1 := ldT t1 t2 t3).
             assert (F2 := LK t1 argT (t2 +T t3)). 
             exact (tranT _ _ _ F2 F1).              (* NB : idT_is_annT -> not NK *)
         + destruct D as [LC | LK].
           * assert (F1 := ldS s1 s2 s3). apply symS in F1. 
             assert (F2 := tranS _ _ _ H4 F1). 
             apply LC in F2.
             rewrite F2 in H2. discriminate H2.
           * exact (LK t1 argT t2). 
       - case_eq(rS (s2 +S s3) s3); intro H1; case_eq(rS ((s1 *S s2) +S (s1 *S s3)) (s1 *S s3)); intro H3.
         + apply refT. 
         + assert (F1 := ldS s1 s2 s3).
           assert (F2 := m_conS _ _ _ _ (refS s1) H1). apply symS in F2. 
           assert (F3 := tranS _ _ _ F2 F1). apply symS in F3.
           rewrite F3 in H3. discriminate H3.
         + destruct D as [LC | LK].
           * assert (F1 := ldS s1 s2 s3).
             assert (F2 := tranS _ _ _ F1 H3). 
             apply LC in F2.
             rewrite F2 in H1. discriminate H1.
           * exact (LK t1 argT t3). 
         + destruct selS_or_annT as [selS | argT_is_annT].
           * destruct (selS s2 s3) as [F1 | F1].
             -- apply symS in F1. rewrite F1 in H2. discriminate H2.
             -- rewrite F1 in H1. discriminate H1. 
           * destruct (argT_is_annT t1) as [F1 F2].  exact F2. 
Qed. 




Lemma bop_llex_product_not_left_distributive_v1 : 
  bop_not_left_distributive S rS addS mulS → bop_not_left_distributive (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT).
Proof. intros [ [s1 [s2 s3 ] ] nld ].
       exists ((s1, wT), ((s2, wT), (s3, wT))).
       compute. rewrite nld. reflexivity.
Defined. 


Lemma bop_llex_product_not_left_distributive_v2 : 
  bop_not_left_distributive T rT addT mulT → bop_not_left_distributive (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT).
Proof. intros [ [t1 [t2 t3 ] ] nld ].
       exists ((wS, t1), ((wS, t2), (wS, t3))).
       unfold brel_product. unfold bop_product, bop_llex. 
       apply bop_and_false_intro. right. unfold llex_p2.
       assert (F1 := a_idemS wS). rewrite F1. apply symS in F1. rewrite F1. 
       assert (F2 := a_idemS (wS *S wS)). rewrite F2. apply symS in F2. rewrite F2. 
       exact nld. 
Defined. 


(* see cases 1-4 in the proof below *) 

Definition a_witness_llex_product_not_left_distributive
      (selS_or_id_annT : bop_selective S rS addS + (bop_is_id T rT addT argT * bop_is_ann T rT mulT argT))
      (s1 s2 s3 : S)
      (t1 t2 t3 : T)
:= if (rS (s2 +S s3) s2) 
   then if rS (s2 +S s3) s3
        then (* can't reach this branch *) 
             ((s1, t1), ((s2, t2), (s3, t3)))
        else  if rS (s1 *S s2) ((s1 *S s2) +S (s1 *S s3))
              then (* case 1 *) 
                   if rT (t1 *T t2) ((t1 *T t2) +T (t1 *T t3))
                   then ((s1, t1), ((s2, t3), (s3, t2)))
                   else ((s1, t1), ((s2, t2), (s3, t3)))
              else (* case 2 *) 
                   ((s1, t1), ((s2, t2), (s3, t3)))
   else if rS (s2 +S s3) s3
        then (* case 3 *) 
             if rT (t1 *T t3) ((t1 *T t2) +T (t1 *T t3))
             then ((s1, t1), ((s2, t3), (s3, t2)))
             else ((s1, t1), ((s2, t2), (s3, t3)))
        else (* case 4 *) 
             match selS_or_id_annT with 
             | inl _ => (* can't reach this branch *) 
                       ((s1, t1), ((s2, t2), (s3, t3)))
             | inr _ => if rT argT (t1 *T t2)
                        then ((s1, t1), ((s2, argT), (s3, t3)))
                        else ((s1, t1), ((s2, argT), (s3, t2)))
             end.   

Definition witness_llex_product_not_left_distributive_without_selectivity
      (s1 s2 s3 : S)
      (t1 t2 t3 : T)
:= if (rS (s2 +S s3) s2) 
   then if rS (s2 +S s3) s3
        then (* can't reach this branch *) 
             ((s1, t1), ((s2, t2), (s3, t3)))
        else  if rS (s1 *S s2) ((s1 *S s2) +S (s1 *S s3))
              then (* case 1 *) 
                   if rT (t1 *T t2) ((t1 *T t2) +T (t1 *T t3))
                   then ((s1, t1), ((s2, t3), (s3, t2)))
                   else ((s1, t1), ((s2, t2), (s3, t3)))
              else (* case 2 *) 
                   ((s1, t1), ((s2, t2), (s3, t3)))
   else if rS (s2 +S s3) s3
        then (* case 3 *) 
             if rT (t1 *T t3) ((t1 *T t2) +T (t1 *T t3))
             then ((s1, t1), ((s2, t3), (s3, t2)))
             else ((s1, t1), ((s2, t2), (s3, t3)))
        else (* case 4 *) 
             if rT argT (t1 *T t2)
             then ((s1, t1), ((s2, argT), (s3, t3)))
             else ((s1, t1), ((s2, argT), (s3, t2))). 


Definition witness_llex_product_not_left_distributive_with_selectivity
      (s1 s2 s3 : S)
      (t1 t2 t3 : T)
:= if (rS (s2 +S s3) s2) 
   then if rS (s2 +S s3) s3
        then (* can't reach this branch *) 
             ((s1, t1), ((s2, t2), (s3, t3)))
        else  if rS (s1 *S s2) ((s1 *S s2) +S (s1 *S s3))
              then (* case 1 *) 
                   if rT (t1 *T t2) ((t1 *T t2) +T (t1 *T t3))
                   then ((s1, t1), ((s2, t3), (s3, t2)))
                   else ((s1, t1), ((s2, t2), (s3, t3)))
              else (* case 2 *) 
                   ((s1, t1), ((s2, t2), (s3, t3)))
   else if rS (s2 +S s3) s3
        then (* case 3 *) 
             if rT (t1 *T t3) ((t1 *T t2) +T (t1 *T t3))
             then ((s1, t1), ((s2, t3), (s3, t2)))
             else ((s1, t1), ((s2, t2), (s3, t3)))
        else (* case 4 *)
             (* can't reach this branch *)           
             ((s1, t1), ((s2, t2), (s3, t3))). 


Lemma bop_llex_product_not_left_distributive_v3
      (a_commT : bop_commutative T rT addT) (*NB*)
      (selS_or_id_annT : bop_selective S rS addS + (bop_is_id T rT addT argT * bop_is_ann T rT mulT argT))
      (ldS : bop_left_distributive S rS addS mulS)
      (ldT : bop_left_distributive T rT addT mulT) : 
      bop_not_left_cancellative S rS mulS → bop_not_left_constant T rT mulT → 
      bop_not_left_distributive (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT).
Proof. intros [ [s1 [s2 s3 ] ] [E N] ] [ [t1 [ t2 t3 ]] F].
       (* to understand the cases below, assume we have done this: 
          
           exists ((s1, a), ((s2, b), (s3, c))).

          In each of the four cases pick a, b, and c to make that case work. 
        *)
       exists(a_witness_llex_product_not_left_distributive selS_or_id_annT s1 s2 s3 t1 t2 t3). 
       unfold a_witness_llex_product_not_left_distributive. 
       unfold bop_product, brel_product, bop_llex.        
       case_eq(rS s2 (s2 +S s3)); intro H2; 
       case_eq(rS (s1 *S s2) ((s1 *S s2) +S (s1 *S s3))); intro H4; simpl. 
       - case_eq(rS (s2 +S s3) s3); intro H1; case_eq(rS ((s1 *S s2) +S (s1 *S s3)) (s1 *S s3)); intro H3. 
         + rewrite (tranS _ _ _ H2 H1) in N. discriminate N. 
         + assert (F1 := tranS _ _ _ H2 H1).
           assert (F2 := a_idemS (s1 *S s3)). 
           assert (F3 := m_conS _ _ _ _ (refS s1) F1). 
           assert (F4 := a_conS _ _ _ _ F3 (refS ((s1 *S s3)))). 
           assert (F5 := tranS _ _ _ F4 F2).
           rewrite F5 in H3. discriminate H3. 
         + (* ============= case 1 ======================
              E : (s1 *S s2) =S (s1 *S s3)
              N : rS s2 s3 = false
              F : rT (t1 *T t2) (t1 *T t3) = false

             H2 : s2 =S (s2 +S s3)
             H4 : (s1 *S s2) =S ((s1 *S s2) +S (s1 *S s3))
             H1 : rS (s2 +S s3) s3 = false
             H3 : ((s1 *S s2) +S (s1 *S s3)) =S (s1 *S s3)
             ===========need=================
             rT (a *T b) ((a *T b) +T (a *T c)) = false

             if rT (t1 *T t2) ((t1 *T t2) +T (t1 *T t3))
             then (t1 *T t3) ((t1 *T t2) +T (t1 *T t3)) = false
                   a     b     a     c       a     b    (use a_commT) 

             else (t1 *T t2) ((t1 *T t2) +T (t1 *T t3)) = false
                   a      b     a     b      a     c 
           *) 
           unfold llex_p2. rewrite (symS _ _ H2).
           case_eq(rT (t1 *T t2) ((t1 *T t2) +T (t1 *T t3))); intro F1.
           * apply bop_and_false_intro. right.
             rewrite H2. rewrite H1. rewrite H4. rewrite H3.            
               case_eq(rT (t1 *T t3) ((t1 *T t3) +T (t1 *T t2))); intro F2; auto.              
             -- assert (F3 := a_commT (t1 *T t3) (t1 *T t2)). 
                assert (F4 := tranT _ _ _ F2 F3). apply symT in F4. 
                rewrite (tranT _ _ _ F1 F4) in F. discriminate F. 
           * apply bop_and_false_intro. right.
             rewrite H2. rewrite H1. rewrite H4. rewrite H3.            
             exact F1.            
         + apply symS in E.
           assert (F1 := tranS _ _ _ E H4). apply symS in F1. 
           rewrite F1 in H3. discriminate H3. 
       - case_eq(rS (s2 +S s3) s3); intro H1; case_eq(rS ((s1 *S s2) +S (s1 *S s3)) (s1 *S s3)); intro H3. 
         + assert (F1 := tranS _ _ _ H2 H1). 
           assert (F2 := a_idemS (s1 *S s2)). 
           assert (F3 := m_conS _ _ _ _ (refS s1) F1). 
           assert (F4 := a_conS _ _ _ _ (refS (s1 *S s2)) F3). apply symS in F2.
           assert (F5 := tranS _ _ _ F2 F4). 
           rewrite F5 in H4. discriminate H4.
         + assert (F1 := ldS s1 s2 s3).
           assert (F2 := m_conS _ _ _ _ (refS s1) H1). apply symS in F1. 
           rewrite (tranS _ _ _ F1 F2) in H3. discriminate H3.            
         + (* ===============case 2==============================
              E : (s1 *S s2) =S (s1 *S s3)
              N : rS s2 s3 = false
              F : rT (t1 *T t2) (t1 *T t3) = false

             H2 : s2 =S (s2 +S s3)
             H4 : rS (s1 *S s2) ((s1 *S s2) +S (s1 *S s3)) = false
             H1 : rS (s2 +S s3) s3 = false
             H3 : ((s1 *S s2) +S (s1 *S s3)) =S (s1 *S s3)
             ==========need==================
             rT (a *T b) (a *T c) = false
             so use F: 
             rT (t1 *T t2) (t1 *T t3) = false
                 a     b    c     d 
           *)
           unfold llex_p2. rewrite (symS _ _ H2). rewrite H2. 
           apply bop_and_false_intro. right. rewrite H1, H4, H3. 
           exact F. 
         + assert (F1 := ldS s1 s2 s3).
           assert (F2 := m_conS _ _ _ _ (refS s1) H2).
           assert (F3 := tranS _ _ _ F2 F1).            
           rewrite F3 in H4. discriminate H4.
       - case_eq(rS (s2 +S s3) s3); intro H1; case_eq(rS ((s1 *S s2) +S (s1 *S s3)) (s1 *S s3)); intro H3. 
         + (* ==================case 3=========================
              E : (s1 *S s2) =S (s1 *S s3)
              N : rS s2 s3 = false
              F : rT (t1 *T t2) (t1 *T t3) = false

              H2 : rS s2 (s2 +S s3) = false
              H4 : (s1 *S s2) =S ((s1 *S s2) +S (s1 *S s3))
              H1 : (s2 +S s3) =S s3
              H3 : ((s1 *S s2) +S (s1 *S s3)) =S (s1 *S s3)
              ===========need=================
              rT (a *T c) ((a *T b) +T (a *T c)) = false

             if rT (t1 *T t3) ((t1 *T t2) +T (t1 *T t3))
             then (t1 *T t2) ((t1 *T t2) +T (t1 *T t3)) = false
                   a     c     a     c       a     b    (use a_commT) 

             else (t1 *T t3) ((t1 *T t2) +T (t1 *T t3)) = false
                   a     c      a     b       a     c 

           *) 
           assert (G : rS (s2 +S s3) s2 = false).
              case_eq(rS (s2 +S s3) s2); intro H; auto.
                apply symS in H. rewrite H in H2. discriminate H2.            
           unfold llex_p2. rewrite G. 
           case_eq(rT (t1 *T t3) ((t1 *T t2) +T (t1 *T t3))); intro F1.
           * apply bop_and_false_intro. right.
             rewrite H2. rewrite H1. rewrite H4. rewrite H3.            
               case_eq(rT (t1 *T t2) ((t1 *T t3) +T (t1 *T t2))); intro F2; auto.              
             -- assert (F3 := a_commT (t1 *T t3) (t1 *T t2)). 
                assert (F4 := tranT _ _ _ F2 F3). apply symT in F1. 
                rewrite (tranT _ _ _ F4 F1) in F. discriminate F. 
           * apply bop_and_false_intro. right.
             rewrite H2. rewrite H1. rewrite H4. rewrite H3.            
             exact F1.            
         + assert (F1 := ldS s1 s2 s3).
           assert (F2 := m_conS _ _ _ _ (refS s1) H1). apply symS in F1. 
           assert (F3 := tranS _ _ _ F1 F2).            
           rewrite F3 in H3. discriminate H3.
         + (* =============case 4=================================
              E : (s1 *S s2) =S (s1 *S s3)
              N : rS s2 s3 = false
              F : rT (t1 *T t2) (t1 *T t3) = false

              H2 : rS s2 (s2 +S s3) = false
              H4 : (s1 *S s2) =S ((s1 *S s2) +S (s1 *S s3))
              H1 : rS (s2 +S s3) s3 = false
              H3 : ((s1 *S s2) +S (s1 *S s3)) =S (s1 *S s3)
             =============need===============
              rT (a *T argT) ((a *T b) +T (a *T c)) = false
  
             case split: 
             selective(+S) : contradiction with H1 H2. 
             
             argT is id for +T and is ann for *T: 
             =============need===============
             rT argT ((a *T b) +T (a *T c)) = false
             
             let b = argT. so  ((a *T b) +T (a *T c)) =T (a *T c). 

             =============need===============
             rT argT (a *T c) = false

             if argT = (t1 *T t2)
             then let (a *T c) = (t1 *T t3)
             else let (a *T c) = (t1 *T t2)
           *)
           destruct selS_or_id_annT as [selS | [idT annT]].
           * destruct (selS s2 s3) as [F1 | F1]. 
             -- apply symS in F1. rewrite F1 in H2. discriminate H2.
             -- rewrite F1 in H1. discriminate H1.
           * assert (G : rS (s2 +S s3) s2 = false).
             case_eq(rS (s2 +S s3) s2); intro H; auto.
             apply symS in H. rewrite H in H2. discriminate H2.
             unfold llex_p2. rewrite G.
             case_eq(rT argT (t1 *T t2)); intro F6.
             -- apply bop_and_false_intro. right.
                rewrite H1, H2, H3, H4.
                destruct (annT t1) as [F1 F2].
                destruct (idT (t1 *T t3)) as [F3 F4].                          
                assert (F5 : ((t1 *T argT) +T (t1 *T t3)) =T (t1 *T t3)).
                   assert (F5 := a_conT _ _ _ _ F2 (refT (t1 *T t3))). 
                   exact (tranT _ _ _ F5 F3). 
                case_eq(rT (t1 *T argT) ((t1 *T argT) +T (t1 *T t3))); intro F7; auto.
                ++ assert (F8 := tranT _ _ _ F7 F5).
                   assert (F9 := tranT _ _ _ F2 F6). apply symT in F9. 
                   rewrite (tranT _ _ _ F9 F8) in F. discriminate F. 
             -- apply bop_and_false_intro. right.
                rewrite H1, H2, H3, H4.
                destruct (annT t1) as [F1 F2].
                destruct (idT (t1 *T t2)) as [F3 F4].                                          
                assert (F5 : ((t1 *T argT) +T (t1 *T t2)) =T (t1 *T t2)).
                   assert (F5 := a_conT _ _ _ _ F2 (refT (t1 *T t2))). 
                   exact (tranT _ _ _ F5 F3). 
                case_eq(rT (t1 *T argT) ((t1 *T argT) +T (t1 *T t2))); intro F7; auto.
                ++ assert (F8 := tranT _ _ _ F7 F5). apply symT in F2. 
                   rewrite (tranT _ _ _ F2 F8) in F6. discriminate F6. 
         + apply symS in E. assert (F1 := tranS _ _ _ E H4). 
           apply symS in F1. rewrite F1 in H3. discriminate H3. 
       - case_eq(rS (s2 +S s3) s3); intro H1; case_eq(rS ((s1 *S s2) +S (s1 *S s3)) (s1 *S s3)); intro H3. 
         + apply symS in E. assert (F1 := tranS _ _ _ H3 E). 
           apply symS in F1. rewrite F1 in H4. discriminate H4. 
         + assert (F1 := ldS s1 s2 s3).
           assert (F2 := m_conS _ _ _ _ (refS s1) H1). apply symS in F2. 
           assert (F3 := tranS _ _ _ F2 F1). apply symS in F3.
           rewrite F3 in H3. discriminate H3.
         + apply symS in E. assert (F1 := tranS _ _ _ H3 E). 
           apply symS in F1. rewrite F1 in H4. discriminate H4. 
         + assert (F1 := a_idemS (s1 *S s3)). 
           assert (F2 := a_conS _ _ _ _ E (refS (s1 *S s3))). 
           assert (F3 := tranS _ _ _ F2 F1).
           rewrite F3 in H3. discriminate H3. 
Defined. 



Lemma bop_llex_product_right_distributive 
      (selS_or_annT : bop_selective S rS addS + bop_is_ann T rT mulT argT)
      (rdS : bop_right_distributive S rS addS mulS)
      (rdT : bop_right_distributive T rT addT mulT)
      (D : (bop_right_cancellative S rS mulS) + (bop_right_constant T rT mulT)) : 
         bop_right_distributive (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT).
Proof. intros [s1 t1] [s2 t2] [s3 t3].
       unfold bop_product, bop_llex, brel_product.
       apply bop_and_intro. 
       apply rdS. 
       unfold llex_p2.
       case_eq(rS s2 (s2 +S s3)); intro H2; 
       case_eq(rS (s2 *S s1) ((s2 *S s1) +S (s3 *S s1))); intro H4; simpl. 
       - case_eq(rS (s2 +S s3) s3); intro H1; case_eq(rS ((s2 *S s1) +S (s3 *S s1)) (s3 *S s1)); intro H3. 
         + apply rdT.
         + assert (F1 := tranS _ _ _ H2 H1).
           assert (F2 := a_idemS (s3 *S s1)). 
           assert (F3 := m_conS _ _ _ _ F1 (refS s1)). 
           assert (F4 := a_conS _ _ _ _ F3 (refS (s3 *S s1))). 
           assert (F5 := tranS _ _ _ F4 F2).
           rewrite F5 in H3. discriminate H3. 
         + destruct D as [RC | RK].
           * assert (F1 := rdS s1 s2 s3).
             assert (F2 := tranS _ _ _ F1 H3). 
             apply RC in F2. 
             assert (F3 := tranS _ _ _ H2 F2).
             assert (F4 := conS _ _ _ _ (refS (s2 +S s3)) F3). 
             rewrite <- F4 in H1. apply symS in H2.
             rewrite H2 in H1. discriminate H1.
           * assert (F1 := rdT t1 t2 t3).
             assert (F2 := RK t1 t2 (t2 +T t3)). 
             exact (tranT _ _ _ F2 F1). 
         + apply refT.
       - case_eq(rS (s2 +S s3) s3); intro H1; case_eq(rS ((s2 *S s1) +S (s3 *S s1)) (s3 *S s1)); intro H3. 
         + assert (F1 := tranS _ _ _ H2 H1). 
           assert (F2 := a_idemS (s2 *S s1)). 
           assert (F3 := m_conS _ _ _ _ F1 (refS s1)). 
           assert (F4 := a_conS _ _ _ _ (refS (s2 *S s1)) F3). apply symS in F2.
           assert (F5 := tranS _ _ _ F2 F4). 
           rewrite F5 in H4. discriminate H4.
         + assert (F1 := rdS s1 s2 s3).
           assert (F2 := m_conS _ _ _ _ H1 (refS s1)). apply symS in F1. 
           rewrite (tranS _ _ _ F1 F2) in H3. discriminate H3.            
         + destruct D as [RC | RK].
           * assert (F1 := rdS s1 s2 s3).
             assert (F2 := tranS _ _ _ F1 H3). 
             apply RC in F2. 
             rewrite F2 in H1. discriminate H1.
           * exact(RK t1 t2 t3). 
         + assert (F1 := rdS s1 s2 s3).
           assert (F2 := m_conS _ _ _ _ H2 (refS s1)).
           assert (F3 := tranS _ _ _ F2 F1).            
           rewrite F3 in H4. discriminate H4.
       - case_eq(rS (s2 +S s3) s3); intro H1; case_eq(rS ((s2 *S s1) +S (s3 *S s1)) (s3 *S s1)); intro H3. 
         + destruct D as [RC | RK].
           * assert (F1 := rdS s1 s2 s3). apply symS in F1. 
             assert (F2 := tranS _ _ _ H4 F1). 
             apply RC in F2.
             rewrite F2 in H2. discriminate H2.
           * assert (F1 := rdT t1 t2 t3).
             assert (F2 := RK t1 t3 (t2 +T t3)). 
             exact (tranT _ _ _ F2 F1). 
         + assert (F1 := rdS s1 s2 s3).
           assert (F2 := m_conS _ _ _ _ H1 (refS s1)). apply symS in F1. 
           assert (F3 := tranS _ _ _ F1 F2).            
           rewrite F3 in H3. discriminate H3.
         + destruct D as [RC | RK].
           * assert (F1 := rdS s1 s2 s3). apply symS in F1. 
             assert (F2 := tranS _ _ _ H4 F1). 
             apply RC in F2.
             rewrite F2 in H2. discriminate H2.
           * assert (F1 := rdT t1 t2 t3).
             assert (F2 := RK t1 argT (t2 +T t3)). 
             exact (tranT _ _ _ F2 F1).              (* NB : idT_is_annT -> not RK *)
         + destruct D as [RC | RK].
           * assert (F1 := rdS s1 s2 s3). apply symS in F1. 
             assert (F2 := tranS _ _ _ H4 F1). 
             apply RC in F2.
             rewrite F2 in H2. discriminate H2.
           * exact (RK t1 argT t2). 
       - case_eq(rS (s2 +S s3) s3); intro H1; case_eq(rS ((s2 *S s1) +S (s3 *S s1)) (s3 *S s1)); intro H3. 
         + apply refT. 
         + assert (F1 := rdS s1 s2 s3).
           assert (F2 := m_conS _ _ _ _ H1 (refS s1)). apply symS in F2. 
           assert (F3 := tranS _ _ _ F2 F1). apply symS in F3.
           rewrite F3 in H3. discriminate H3.
         + destruct D as [RC | RK].
           * assert (F1 := rdS s1 s2 s3).
             assert (F2 := tranS _ _ _ F1 H3). 
             apply RC in F2.
             rewrite F2 in H1. discriminate H1.
           * exact (RK t1 argT t3). 
         + destruct selS_or_annT as [selS | argT_is_annT].
           * destruct (selS s2 s3) as [F1 | F1].
             -- apply symS in F1. rewrite F1 in H2. discriminate H2.
             -- rewrite F1 in H1. discriminate H1. 
           * destruct (argT_is_annT t1) as [F1 F2].  exact F1. 
Qed. 

Lemma bop_llex_product_not_right_distributive_v1 : 
      bop_not_right_distributive S rS addS mulS → 
         bop_not_right_distributive (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT). 
Proof. intros [ [s1 [s2 s3 ] ] nld ]. exists ((s1, wT), ((s2, wT), (s3, wT))); simpl. rewrite nld. simpl. reflexivity. Defined. 


Lemma bop_llex_product_not_right_distributive_v2 : 
      bop_not_right_distributive T rT addT mulT → 
      bop_not_right_distributive (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT).
Proof. intros [ [t1 [t2 t3 ] ] nrd ].
       exists ((wS, t1), ((wS, t2), (wS, t3))).
      unfold brel_product. unfold bop_product, bop_llex. 
       apply bop_and_false_intro. right. unfold llex_p2.
       assert (F1 := a_idemS wS). rewrite F1. apply symS in F1. rewrite F1. 
       assert (F2 := a_idemS (wS *S wS)). rewrite F2. apply symS in F2. rewrite F2. 
       exact nrd. 
Defined. 


(* see cases 1-4 in the proof below *) 

Definition a_witness_llex_product_not_right_distributive
      (selS_or_id_annT : bop_selective S rS addS + (bop_is_id T rT addT argT * bop_is_ann T rT mulT argT))
      (s1 s2 s3 : S)
      (t1 t2 t3 : T)
:= if (rS (s2 +S s3) s2) 
   then if rS (s2 +S s3) s3
        then (* can't reach this branch *) 
             ((s1, t1), ((s2, t2), (s3, t3)))
        else  if rS (s2 *S s1) ((s2 *S s1) +S (s3 *S s1))
              then (* case 1 *) 
                   if rT (t2 *T t1) ((t2 *T t1) +T (t3 *T t1))
                   then ((s1, t1), ((s2, t3), (s3, t2)))
                   else ((s1, t1), ((s2, t2), (s3, t3)))
              else (* case 2 *) 
                   ((s1, t1), ((s2, t2), (s3, t3)))
   else if rS (s2 +S s3) s3
        then (* case 3 *) 
             if rT (t3 *T t1) ((t2 *T t1) +T (t3 *T t1))
             then ((s1, t1), ((s2, t3), (s3, t2)))
             else ((s1, t1), ((s2, t2), (s3, t3)))
        else (* case 4 *) 
             match selS_or_id_annT with 
             | inl _ => (* can't reach this branch *) 
                       ((s1, t1), ((s2, t2), (s3, t3)))
             | inr _ => if rT argT (t2 *T t1)
                        then ((s1, t1), ((s2, argT), (s3, t3)))
                        else ((s1, t1), ((s2, argT), (s3, t2)))
             end.   


Definition witness_llex_product_not_right_distributive_without_selectivity 
      (s1 s2 s3 : S)
      (t1 t2 t3 : T)
:= if (rS (s2 +S s3) s2) 
   then if rS (s2 +S s3) s3
        then (* can't reach this branch *) 
             ((s1, t1), ((s2, t2), (s3, t3)))
        else  if rS (s2 *S s1) ((s2 *S s1) +S (s3 *S s1))
              then (* case 1 *) 
                   if rT (t2 *T t1) ((t2 *T t1) +T (t3 *T t1))
                   then ((s1, t1), ((s2, t3), (s3, t2)))
                   else ((s1, t1), ((s2, t2), (s3, t3)))
              else (* case 2 *) 
                   ((s1, t1), ((s2, t2), (s3, t3)))
   else if rS (s2 +S s3) s3
        then (* case 3 *) 
             if rT (t3 *T t1) ((t2 *T t1) +T (t3 *T t1))
             then ((s1, t1), ((s2, t3), (s3, t2)))
             else ((s1, t1), ((s2, t2), (s3, t3)))
        else (* case 4 *) 
             if rT argT (t2 *T t1)
             then ((s1, t1), ((s2, argT), (s3, t3)))
             else ((s1, t1), ((s2, argT), (s3, t2))). 


Definition witness_llex_product_not_right_distributive_with_selectivity 
      (s1 s2 s3 : S)
      (t1 t2 t3 : T)
:= if (rS (s2 +S s3) s2) 
   then if rS (s2 +S s3) s3
        then (* can't reach this branch *) 
             ((s1, t1), ((s2, t2), (s3, t3)))
        else  if rS (s2 *S s1) ((s2 *S s1) +S (s3 *S s1))
              then (* case 1 *) 
                   if rT (t2 *T t1) ((t2 *T t1) +T (t3 *T t1))
                   then ((s1, t1), ((s2, t3), (s3, t2)))
                   else ((s1, t1), ((s2, t2), (s3, t3)))
              else (* case 2 *) 
                   ((s1, t1), ((s2, t2), (s3, t3)))
   else if rS (s2 +S s3) s3
        then (* case 3 *) 
             if rT (t3 *T t1) ((t2 *T t1) +T (t3 *T t1))
             then ((s1, t1), ((s2, t3), (s3, t2)))
             else ((s1, t1), ((s2, t2), (s3, t3)))
        else (* case 4 *)
             (* can't reach this branch *) 
             ((s1, t1), ((s2, t2), (s3, t3))). 


Lemma bop_llex_product_not_right_distributive_v3 
      (a_commT : bop_commutative T rT addT) (*NB*)
      (selS_or_id_annT : bop_selective S rS addS + (bop_is_id T rT addT argT * bop_is_ann T rT mulT argT))
      (rdS : bop_right_distributive S rS addS mulS)
      (rdT : bop_right_distributive T rT addT mulT) : 
      bop_not_right_cancellative S rS mulS → bop_not_right_constant T rT mulT → 
      bop_not_right_distributive (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT).
Proof. intros [ [s1 [s2 s3 ] ] [E N] ] [ [t1 [ t2 t3 ]] F].
       (* to understand the cases below, assume we have done this: 
          
           exists ((s1, a), ((s2, b), (s3, c))).

          In each of the four cases pick a, b, and c to make that case work. 
        *)
       exists(a_witness_llex_product_not_right_distributive selS_or_id_annT s1 s2 s3 t1 t2 t3). 
       unfold a_witness_llex_product_not_right_distributive. 
       unfold bop_product, brel_product, bop_llex.
       case_eq(rS s2 (s2 +S s3)); intro H2; 
       case_eq(rS (s2 *S s1) ((s2 *S s1) +S (s3 *S s1))); intro H4; simpl. 
       - case_eq(rS (s2 +S s3) s3); intro H1; case_eq(rS ((s2 *S s1) +S (s3 *S s1)) (s3 *S s1)); intro H3. 
         + rewrite (tranS _ _ _ H2 H1) in N. discriminate N. 
         + assert (F1 := tranS _ _ _ H2 H1).
           assert (F2 := a_idemS (s3 *S s1)). 
           assert (F3 := m_conS _ _ _ _ F1 (refS s1)). 
           assert (F4 := a_conS _ _ _ _ F3 (refS (s3 *S s1))). 
           assert (F5 := tranS _ _ _ F4 F2).
           rewrite F5 in H3. discriminate H3. 
         + (* ============= case 1 ======================
              E : (s2 *S s1) =S (s3 *S s1)
              N : rS s2 s3 = false
              F : rT (t2 *T t1) (t3 *T t1) = false
  
             H2 : s2 =S (s2 +S s3)
             H4 : (s2 *S s1) =S ((s2 *S s1) +S (s3 *S s1))
             H1 : rS (s2 +S s3) s3 = false
             H3 : ((s2 *S s1) +S (s3 *S s1)) =S (s3 *S s1)
             ===========need=================
             rT (b *T a) ((b *T a) +T (c *T a)) = false

             if rT (t2 *T t1) ((t2 *T t1) +T (t3 *T t1))
             then (t3 *T t1) ((t2 *T t1) +T (t3 *T t1)) = false
                   b     a     c     a        b    a    (use a_commT) 

             else rT (t2 *T t1) ((t2 *T t1) +T (t3 *T t1)) = false 
                      b      a    b     a       c     a 
            *)
           unfold llex_p2. rewrite (symS _ _ H2).
           case_eq(rT (t2 *T t1) ((t2 *T t1) +T (t3 *T t1))); intro F1.
           * rewrite H1, H2, H3, H4.
             apply bop_and_false_intro. right.
             case_eq(rT (t3 *T t1) ((t3 *T t1) +T (t2 *T t1))); intro F2; auto.              
             -- assert (F3 := a_commT (t3 *T t1) (t2 *T t1)). 
                assert (F4 := tranT _ _ _ F2 F3). apply symT in F4. 
                rewrite (tranT _ _ _ F1 F4) in F. discriminate F. 
           * apply bop_and_false_intro. right.
             rewrite H1, H2, H3, H4.
             exact F1.            
         + apply symS in E.
           assert (F1 := tranS _ _ _ E H4). apply symS in F1. 
           rewrite F1 in H3. discriminate H3. 
       - case_eq(rS (s2 +S s3) s3); intro H1; case_eq(rS ((s2 *S s1) +S (s3 *S s1)) (s3 *S s1)); intro H3. 
         + assert (F1 := tranS _ _ _ H2 H1). 
           assert (F2 := a_idemS (s2 *S s1)). 
           assert (F3 := m_conS _ _ _ _ F1 (refS s1)). 
           assert (F4 := a_conS _ _ _ _ (refS (s2 *S s1)) F3). apply symS in F2.
           assert (F5 := tranS _ _ _ F2 F4). 
           rewrite F5 in H4. discriminate H4.
         + assert (F1 := rdS s1 s2 s3).
           assert (F2 := m_conS _ _ _ _ H1 (refS s1)). apply symS in F1. 
           rewrite (tranS _ _ _ F1 F2) in H3. discriminate H3.            
         + (* ===============case 2==============================
              E : (s2 *S s1) =S (s3 *S s1)
              N : rS s2 s3 = false
              F : rT (t2 *T t1) (t3 *T t1) = false

             H2 : s2 =S (s2 +S s3)
             H4 : rS (s2 *S s1) ((s2 *S s1) +S (s3 *S s1)) = false
             H1 : rS (s2 +S s3) s3 = false
             H3 : ((s2 *S s1) +S (s3 *S s1)) =S (s3 *S s1)
             ==========need==================
               rT (b *T a) (c *T a) = false

             so use F: 
             rT (t2 *T t1) (t3 *T t1) = false
                 b     a    c     a 
           *)
           unfold llex_p2. rewrite (symS _ _ H2). 
           apply bop_and_false_intro. right. rewrite H1, H2, H4, H3. 
           exact F.
         + assert (F1 := rdS s1 s2 s3).
           assert (F2 := m_conS _ _ _ _ H2 (refS s1)).
           assert (F3 := tranS _ _ _ F2 F1).            
           rewrite F3 in H4. discriminate H4.
       - case_eq(rS (s2 +S s3) s3); intro H1; case_eq(rS ((s2 *S s1) +S (s3 *S s1)) (s3 *S s1)); intro H3. 
         + (* ==================case 3=========================
              E : (s2 *S s1) =S (s3 *S s1)
              N : rS s2 s3 = false
              F : rT (t2 *T t1) (t3 *T t1) = false

             H2 : rS s2 (s2 +S s3) = false
             H4 : (s2 *S s1) =S ((s2 *S s1) +S (s3 *S s1))
             H1 : (s2 +S s3) =S s3
             H3 : ((s2 *S s1) +S (s3 *S s1)) =S (s3 *S s1)
            =========need===================
             rT (c *T a) ((b *T a) +T (c *T a)) = false

             if rT (t3 *T t1) ((t2 *T t1) +T (t3 *T t1))
             then (t2 *T t1) ((t2 *T t1) +T (t3 *T t1)) = false
                   c     a     c     a       b     a    (use a_commT) 

             else (t3 *T t1) ((t2 *T t1) +T (t3 *T t1)) = false
                   c     a      b     a       c     a 
           *)   
           assert (G : rS (s2 +S s3) s2 = false).
              case_eq(rS (s2 +S s3) s2); intro H; auto.
                apply symS in H. rewrite H in H2. discriminate H2.            
           unfold llex_p2. rewrite G. 
           case_eq(rT (t3 *T t1) ((t2 *T t1) +T (t3 *T t1))); intro F1.
           * apply bop_and_false_intro. right.
             rewrite H1, H2, H3, H4. 
               case_eq(rT (t2 *T t1) ((t3 *T t1) +T (t2 *T t1))); intro F2; auto.              
             -- assert (F3 := a_commT (t3 *T t1) (t2 *T t1)). 
                assert (F4 := tranT _ _ _ F2 F3). apply symT in F1. 
                rewrite (tranT _ _ _ F4 F1) in F. discriminate F. 
           * apply bop_and_false_intro. right.
             rewrite H1, H2, H3, H4. 
             exact F1.
         + assert (F1 := rdS s1 s2 s3).
           assert (F2 := m_conS _ _ _ _ H1 (refS s1)). apply symS in F1. 
           assert (F3 := tranS _ _ _ F1 F2).            
           rewrite F3 in H3. discriminate H3.
         + (* =============case 4=================================
              E : (s2 *S s1) =S (s3 *S s1)
              N : rS s2 s3 = false
              F : rT (t2 *T t1) (t3 *T t1) = false

             H2 : rS s2 (s2 +S s3) = false
             H4 : (s2 *S s1) =S ((s2 *S s1) +S (s3 *S s1))
             H1 : rS (s2 +S s3) s3 = false
             H3 : ((s2 *S s1) +S (s3 *S s1)) =S (s3 *S s1)
             =============need===============
               rT (argT *T a) ((b *T a) +T (c *T a)) = false
  
             case split: 
             selective(+S) : contradiction with H1 H2. 
             
             argT is id for +T and is ann for *T: 
             =============need===============
             rT argT ((b *T a) +T (c *T a)) = false
             
             let b = argT. so  ((b *T a) +T (c *T a)) = (c *T a)

             =============need===============
             rT argT (c *T a) = false

             if argT = (t2 *T t1)
             then let (c *T a) = (t3 *T t1)
             else let (c *T a) = (t2 *T t1)
           *)
           destruct selS_or_id_annT as [selS | [idT annT]].
           * destruct (selS s2 s3) as [F1 | F1]. 
             -- apply symS in F1. rewrite F1 in H2. discriminate H2.
             -- rewrite F1 in H1. discriminate H1.
           * assert (G : rS (s2 +S s3) s2 = false).
             case_eq(rS (s2 +S s3) s2); intro H; auto.
             apply symS in H. rewrite H in H2. discriminate H2.
             unfold llex_p2. rewrite G.
             case_eq(rT argT (t2 *T t1)); intro F6.
             -- apply bop_and_false_intro. right.
                rewrite H1, H2, H3, H4.
                destruct (annT t1) as [F1 F2].
                destruct (idT (t3 *T t1)) as [F3 F4].                          
                assert (F5 : ((argT *T t1) +T (t3 *T t1)) =T (t3 *T t1)).
                   assert (F5 := a_conT _ _ _ _ F1 (refT (t3 *T t1))). 
                   exact (tranT _ _ _ F5 F3). 
                case_eq(rT (argT *T t1) ((argT *T t1) +T (t3 *T t1))); intro F7; auto.
                ++ assert (F8 := tranT _ _ _ F7 F5). apply symT in F6. apply symT in F1. 
                   assert (F9 := tranT _ _ _ F6 F1). 
                   rewrite (tranT _ _ _ F9 F8) in F. discriminate F. 
             -- apply bop_and_false_intro. right.
                rewrite H1, H2, H3, H4.
                destruct (annT t1) as [F1 F2].
                destruct (idT (t2 *T t1)) as [F3 F4].                                          
                assert (F5 : (argT *T t1) +T (t2 *T t1) =T (t2 *T t1)). 
                   assert (F5 := a_conT _ _ _ _ F1 (refT (t2 *T t1))). 
                   exact (tranT _ _ _ F5 F3). 
                case_eq(rT (argT *T t1) ((argT *T t1) +T (t2 *T t1))); intro F7; auto.
                ++ assert (F8 := tranT _ _ _ F7 F5). apply symT in F1. 
                   rewrite (tranT _ _ _ F1 F8) in F6. discriminate F6. 
         + apply symS in E. assert (F1 := tranS _ _ _ E H4). 
           apply symS in F1. rewrite F1 in H3. discriminate H3. 
       - case_eq(rS (s2 +S s3) s3); intro H1; case_eq(rS ((s2 *S s1) +S (s3 *S s1)) (s3 *S s1)); intro H3. 
         + apply symS in E. assert (F1 := tranS _ _ _ H3 E). 
           apply symS in F1. rewrite F1 in H4. discriminate H4. 
         + assert (F1 := rdS s1 s2 s3).
           assert (F2 := m_conS _ _ _ _ H1 (refS s1)). apply symS in F2. 
           assert (F3 := tranS _ _ _ F2 F1). apply symS in F3.
           rewrite F3 in H3. discriminate H3.
         + apply symS in E. assert (F1 := tranS _ _ _ H3 E). 
           apply symS in F1. rewrite F1 in H4. discriminate H4. 
         + assert (F1 := a_idemS (s3 *S s1)). 
           assert (F2 := a_conS _ _ _ _ E (refS (s3 *S s1))). 
           assert (F3 := tranS _ _ _ F2 F1).
           rewrite F3 in H3. discriminate H3. 
Defined.




(* absorption *) 

(* left left *) 

Lemma bops_llex_product_left_left_absorptive : 
      bops_left_left_absorptive S rS addS mulS → 
      ((bops_left_left_absorptive T rT addT mulT) + (bop_anti_left S rS mulS)) → 
         bops_left_left_absorptive (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT).
Proof. intros ldS [ldT| F] [s1 t1] [s2 t2]; compute. 
       - rewrite ldS. 
         case_eq(rS (s1 +S (s1 *S s2)) (s1 *S s2)); intro H. 
          + apply ldT.
          + apply refT. 
       - rewrite ldS.
         case_eq(rS (s1 +S (s1 *S s2)) (s1 *S s2)); intro H. 
         + assert (K := F s1 s2).
           assert (J := ldS s1 s2).
           rewrite (tranS _ _ _ J H) in K. discriminate K. 
          + apply refT.
Qed.

Lemma bops_llex_product_not_left_left_absorptive_left : 
      bops_not_left_left_absorptive S rS addS mulS → 
         bops_not_left_left_absorptive (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT). 
Proof. intros [ [s1 s2] P ]. exists ((s1, wT), (s2, wT)). simpl. rewrite P. simpl. reflexivity. Defined. 


Lemma bops_llex_product_not_left_left_absorptive_right : 
      bops_left_left_absorptive S rS addS mulS → bops_not_left_left_absorptive T rT addT mulT → bop_not_anti_left S rS mulS  →
      bops_not_left_left_absorptive (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT).
Proof. intros laS [ [t1 t2] P ] [ [s1 s2]  Q]; compute.
       exists ((s1, t1), (s2, t2)).
       rewrite laS.
       assert (F1 : (s1 +S (s1 *S s2)) =S (s1 *S s2)).
          assert (F2 := a_idemS (s1 *S s2)).
          assert (F3 := a_conS _ _ _ _ Q (refS (s1 *S s2))).        
          exact (tranS _ _ _ F3 F2). 
       rewrite F1. exact P.        
Defined.



(* left right *) 
Lemma bops_llex_product_left_right_absorptive :
      bops_left_right_absorptive S rS addS mulS → 
      ((bops_left_right_absorptive T rT addT mulT) + (bop_anti_right S rS mulS)) → 
      bops_left_right_absorptive (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT).
Proof. intros ldS [ldT| F] [s1 t1] [s2 t2]; compute. 
       - rewrite ldS. 
         case_eq(rS (s1 +S (s2 *S s1)) (s2 *S s1)); intro H. 
          + apply ldT.
          + apply refT. 
       - rewrite ldS.
         case_eq(rS (s1 +S (s2 *S s1)) (s2 *S s1)); intro H. 
         + assert (K := F s1 s2).
           assert (J := ldS s1 s2).
           rewrite (tranS _ _ _ J H) in K. discriminate K. 
          + apply refT.
Defined. 

Lemma bops_llex_product_not_left_right_absorptive_left : 
      bops_not_left_right_absorptive S rS addS mulS → 
         bops_not_left_right_absorptive (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT). 
Proof. intros [ [s1 s2] P ]. exists ((s1, wT), (s2, wT)). simpl. rewrite P. simpl. reflexivity. Defined. 

Lemma bops_llex_product_not_left_right_absorptive_right : 
      bops_left_right_absorptive S rS addS mulS → bops_not_left_right_absorptive T rT addT mulT → bop_not_anti_right S rS mulS  → 
      bops_not_left_right_absorptive (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT).
Proof. intros laS [ [t1 t2] P ] [ [s1 s2]  Q]. compute. 
       exists ((s1, t1), (s2, t2)).
       rewrite laS. 
       assert (F1 : (s1 +S (s2 *S s1)) =S (s2 *S s1)).
          assert (F2 := a_idemS (s2 *S s1)).
          assert (F3 := a_conS _ _ _ _ Q (refS (s2 *S s1))).        
          exact (tranS _ _ _ F3 F2). 
       rewrite F1. exact P.        
Defined.



(* right left *) 
Lemma bops_llex_product_right_left_absorptive : 
      bops_right_left_absorptive S rS addS mulS → 
      ((bops_right_left_absorptive T rT addT mulT) + (bop_anti_left S rS mulS)) → 
      bops_right_left_absorptive (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT).
Proof. intros ldS [ldT| F] [s1 t1] [s2 t2]; compute. 
       - assert (J := ldS s1 s2). rewrite J. apply symS in J. rewrite J. 
         case_eq(rS (s1 *S s2) ((s1 *S s2) +S s1)) ; intro K. 
         + apply ldT. 
         + apply refT. 
       - assert (J := ldS s1 s2). rewrite J. apply symS in J. rewrite J. 
         case_eq(rS (s1 *S s2) ((s1 *S s2) +S s1)) ; intro K.
         + apply symS in J. apply symS in K.
           assert (F1 := tranS _ _ _ J K). 
           assert (F2 := F s1 s2). 
           rewrite F1 in F2. discriminate F2. 
         + apply refT. 
Defined. 

Lemma bops_llex_product_not_right_left_absorptive_left : 
      bops_not_right_left_absorptive S rS addS mulS → 
         bops_not_right_left_absorptive (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT). 
Proof. intros [ [s1 s2] P ]. exists ((s1, wT), (s2, wT)). compute. rewrite P. reflexivity. Defined. 

Lemma bops_llex_product_not_right_left_absorptive_right : 
      bops_right_left_absorptive S rS addS mulS → bops_not_right_left_absorptive T rT addT mulT → bop_not_anti_left S rS mulS  → 
      bops_not_right_left_absorptive (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT).
Proof. intros laS [ [t1 t2] P ] [ [s1 s2]  Q]; compute. 
       exists ((s1, t1), (s2, t2)).
       assert (K := laS s1 s2). rewrite K. apply symS in K. rewrite K. 
       assert (J : (s1 *S s2) =S ((s1 *S s2) +S s1)).
          assert (L := a_idemS (s1 *S s2)). 
          assert (M := a_conS _ _ _ _ (refS (s1 *S s2)) Q). apply symS in L. apply symS in M. 
          exact (tranS _ _ _ L M). 
       rewrite J. exact P. 
Defined.



(* right_right *) 
Lemma bops_llex_product_right_right_absorptive : 
      bops_right_right_absorptive S rS addS mulS → 
      ((bops_right_right_absorptive T rT addT mulT) + (bop_anti_right S rS mulS)) → 
      bops_right_right_absorptive (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT).
Proof. intros laS [laT| F] [s1 t1] [s2 t2]; compute. 
       - assert (J := laS s1 s2). rewrite J. apply symS in J. rewrite J. 
         case_eq(rS (s2 *S s1) ((s2 *S s1) +S s1)) ; intro K. 
         + apply laT. 
         + apply refT. 
       - assert (J := laS s1 s2). rewrite J. apply symS in J. rewrite J. 
         case_eq(rS (s2 *S s1) ((s2 *S s1) +S s1)) ; intro K.
         + apply symS in J. apply symS in K.
           assert (F1 := tranS _ _ _ J K). 
           assert (F2 := F s1 s2). 
           rewrite F1 in F2. discriminate F2. 
         + apply refT. 
Defined.

Lemma bops_llex_product_not_right_right_absorptive_left : 
      bops_not_right_right_absorptive S rS addS mulS → 
         bops_not_right_right_absorptive (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT). 
Proof. intros [ [s1 s2] P ]. exists ((s1, wT), (s2, wT)). compute. rewrite P. reflexivity. Defined. 


Lemma bops_llex_product_not_right_right_absorptive_right : 
  bops_right_right_absorptive S rS addS mulS → bops_not_right_right_absorptive T rT addT mulT → bop_not_anti_right S rS mulS  →
  bops_not_right_right_absorptive (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT).
Proof. intros laS [ [t1 t2] P ] [ [s1 s2]  Q]; compute.
       exists ((s1, t1), (s2, t2)). 
       assert (K := laS s1 s2). rewrite K. apply symS in K. rewrite K. 
       assert (J : (s2 *S s1) =S ((s2 *S s1) +S s1)).
          assert (L := a_idemS (s2 *S s1)). 
          assert (M := a_conS _ _ _ _ (refS (s2 *S s1)) Q). apply symS in L. apply symS in M. 
          exact (tranS _ _ _ L M). 
       rewrite J. exact P. 
Defined. 



End Theory.

Section ACAS.

Section Decide.

Lemma bops_llex_product_exists_id_ann_equal_left 
(S T : Type) (eqS : brel S) (eqT : brel T) (argT : T)
(eqvS : eqv_proofs S eqS)
(eqvT : eqv_proofs T eqT)
           (bS1 bS2 : binary_op S)
           (bT1 bT2 : binary_op T): 
      bops_exists_id_ann_equal S eqS bS1 bS2 → 
      bops_exists_id_ann_equal T eqT bT1 bT2 → 
      bops_exists_id_ann_equal (S * T)
                               (brel_product eqS eqT)
                               (bop_llex argT eqS bS1 bT1)
                               (bop_product bS2 bT2).
Proof. intros [iS [piS paS]]  [iT [piT paT]].
       exists (iS, iT).
       destruct eqvS, eqvT. split.
       apply bop_llex_is_id; auto.
       apply bop_product_is_ann; auto. 
Defined. 

Lemma bops_llex_product_exists_id_ann_not_equal_left_v1
      (S T : Type) (eqS : brel S) (eqT : brel T) (argT : T)
      (eqvS : eqv_proofs S eqS)
      (eqvT : eqv_proofs T eqT)
           (bS1 bS2 : binary_op S)
           (bT1 bT2 : binary_op T):         
      bops_exists_id_ann_not_equal S eqS bS1 bS2 → 
      bops_exists_id_ann_equal T eqT bT1 bT2 → 
      bops_exists_id_ann_not_equal (S * T)
                               (brel_product eqS eqT)
                               (bop_llex argT eqS bS1 bT1)
                               (bop_product bS2 bT2).
Proof. intros [[iS aS] [[piS paS] iS_not_aS]]  [iT [piT paT]].
       exists ((iS, iT), (aS, iT)).
       destruct eqvS, eqvT. split. split. 
       apply bop_llex_is_id; auto.
       apply bop_product_is_ann; auto. 
       compute. rewrite iS_not_aS. reflexivity. 
Defined. 


Lemma bops_llex_product_exists_id_ann_not_equal_left_v2
      (S T : Type) (eqS : brel S) (eqT : brel T) (argT : T)
      (eqvS : eqv_proofs S eqS)
      (eqvT : eqv_proofs T eqT)
      (bS1 bS2 : binary_op S)
      (bT1 bT2 : binary_op T) : 
      bops_exists_id_ann_equal S eqS bS1 bS2 → 
      bops_exists_id_ann_not_equal T eqT bT1 bT2 → 
      bops_exists_id_ann_not_equal (S * T)
                               (brel_product eqS eqT)
                               (bop_llex argT eqS bS1 bT1)
                               (bop_product bS2 bT2).
Proof. intros [iS [piS paS]]  [[iT aT] [[piT paT] iT_not_aT]].
       exists ((iS, iT), (iS, aT)). 
       destruct eqvS, eqvT. split. split.        
       apply bop_llex_is_id; auto.
       apply bop_product_is_ann; auto. 
       compute. rewrite iT_not_aT.
       case_eq(eqS iS iS); intro A; reflexivity. 
Defined. 

Lemma bops_llex_product_exists_id_ann_not_equal_left_v3
      (S T : Type) (eqS : brel S) (eqT : brel T) (argT : T)
      (eqvS : eqv_proofs S eqS)
      (eqvT : eqv_proofs T eqT)
      (bS1 bS2 : binary_op S)
      (bT1 bT2 : binary_op T): 
      bops_exists_id_ann_not_equal S eqS bS1 bS2 → 
      bops_exists_id_ann_not_equal T eqT bT1 bT2 → 
      bops_exists_id_ann_not_equal (S * T)
                               (brel_product eqS eqT)
                               (bop_llex argT eqS bS1 bT1)
                               (bop_product bS2 bT2).
Proof. intros [[iS aS] [[piS paS] iS_not_aS]]  [[iT aT] [[piT paT] iT_not_aT]].
       exists ((iS, iT), (aS, aT)).
       destruct eqvS, eqvT. split. split.               
       apply bop_llex_is_id; auto.
       apply bop_product_is_ann; auto. 
       compute. rewrite iS_not_aS. reflexivity. 
Defined. 


Lemma bops_llex_product_exists_id_ann_equal_right
      (S T : Type) (eqS : brel S) (eqT : brel T) (argT : T)
      (eqvS : eqv_proofs S eqS)
      (eqvT : eqv_proofs T eqT)
      (bS1 bS2 : binary_op S)
      (bT1 bT2 : binary_op T): 
      bops_exists_id_ann_equal S eqS bS2 bS1 → 
      bops_exists_id_ann_equal T eqT bT2 bT1 → 
      bops_exists_id_ann_equal (S * T)
                               (brel_product eqS eqT)
                               (bop_product bS2 bT2)
                               (bop_llex argT eqS bS1 bT1). 
Proof. intros [iS [piS paS]]  [iT [piT paT]].
       exists (iS, iT).
       destruct eqvS, eqvT. split.
       apply bop_product_is_id; auto.        
       apply bop_llex_is_ann; auto.
Defined. 


Lemma bops_llex_product_exists_id_ann_not_equal_right_v1
      (S T : Type) (eqS : brel S) (eqT : brel T) (argT : T)
      (eqvS : eqv_proofs S eqS)
      (eqvT : eqv_proofs T eqT)
      (bS1 bS2 : binary_op S)
      (bT1 bT2 : binary_op T) : 
      bops_exists_id_ann_not_equal S eqS bS2 bS1 → 
      bops_exists_id_ann_equal T eqT bT2 bT1 → 
      bops_exists_id_ann_not_equal (S * T)
                                   (brel_product eqS eqT)
                                   (bop_product bS2 bT2)
                                   (bop_llex argT eqS bS1 bT1). 
Proof. intros [[iS aS] [[piS paS] iS_not_aS]]  [iT [piT paT]].
       exists ((iS, iT), (aS, iT)).
       destruct eqvS, eqvT. split. split.                      
       apply bop_product_is_id; auto. 
       apply bop_llex_is_ann; auto.
       compute. rewrite iS_not_aS. reflexivity. 
Defined. 


Lemma bops_llex_product_exists_id_ann_not_equal_right_v2
      (S T : Type) (eqS : brel S) (eqT : brel T) (argT : T)
      (eqvS : eqv_proofs S eqS)
      (eqvT : eqv_proofs T eqT)
      (bS1 bS2 : binary_op S)
      (bT1 bT2 : binary_op T) : 
      bops_exists_id_ann_equal S eqS bS2 bS1 → 
      bops_exists_id_ann_not_equal T eqT bT2 bT1 → 
      bops_exists_id_ann_not_equal (S * T)
                                   (brel_product eqS eqT)
                                   (bop_product bS2 bT2)                                   
                                   (bop_llex argT eqS bS1 bT1). 
Proof. intros [iS [piS paS]]  [[iT aT] [[piT paT] iT_not_aT]].
       exists ((iS, iT), (iS, aT)).
       destruct eqvS, eqvT. split. split. 
       apply bop_product_is_id; auto.        
       apply bop_llex_is_ann; auto.
       compute. rewrite iT_not_aT.
       case_eq(eqS iS iS); intro A; reflexivity. 
Defined. 

Lemma bops_llex_product_exists_id_ann_not_equal_right_v3
      (S T : Type) (eqS : brel S) (eqT : brel T) (argT : T)
      (eqvS : eqv_proofs S eqS)
      (eqvT : eqv_proofs T eqT)
      (bS1 bS2 : binary_op S)
      (bT1 bT2 : binary_op T) : 
      bops_exists_id_ann_not_equal S eqS bS2 bS1 → 
      bops_exists_id_ann_not_equal T eqT bT2 bT1 → 
      bops_exists_id_ann_not_equal (S * T)
                                   (brel_product eqS eqT)
                                   (bop_product bS2 bT2)
                                   (bop_llex argT eqS bS1 bT1).
Proof. intros [[iS aS] [[piS paS] iS_not_aS]]  [[iT aT] [[piT paT] iT_not_aT]].
       exists ((iS, iT), (aS, aT)).
       destruct eqvS, eqvT. split. split.        
       apply bop_product_is_id; auto.        
       apply bop_llex_is_ann; auto.
       compute. rewrite iS_not_aS. reflexivity. 
Defined. 


Definition bops_llex_product_exists_id_ann_decide_left 
           (S T : Type) (eqS : brel S) (eqT : brel T) (argT : T)
           (eqvS : eqv_proofs S eqS)
           (eqvT : eqv_proofs T eqT)
           (bS1 bS2 : binary_op S)
           (bT1 bT2 : binary_op T)           
           (PS : exists_id_ann_decidable S eqS bS1 bS2)
           (PT : exists_id_ann_decidable T eqT bT1 bT2) :
           exists_id_ann_decidable (S * T)
                                   (brel_product eqS eqT)
                                   (bop_llex argT eqS bS1 bT1)
                                   (bop_product bS2 bT2) :=
let symS := A_eqv_symmetric _ _ eqvS in
let refT := A_eqv_reflexive _ _ eqvT in     
let F0 := bop_llex_exists_id S T eqS eqT bS1 bT1 symS argT refT    in
let F1 := bop_llex_not_exists_id S T eqS eqT bS1 bT1 symS argT in  

let F3 := bop_product_exists_ann S T eqS eqT bS2 bT2     in 
let F2 := bop_product_not_exists_ann S T eqS eqT bS2 bT2 in

let F4 := bops_llex_product_exists_id_ann_equal_left S T eqS eqT argT eqvS eqvT bS1 bS2 bT1 bT2 in 
let F5 := bops_llex_product_exists_id_ann_not_equal_left_v2 S T eqS eqT argT eqvS eqvT bS1 bS2 bT1 bT2 in 
let F6 := bops_llex_product_exists_id_ann_not_equal_left_v1 S T eqS eqT argT eqvS eqvT bS1 bS2 bT1 bT2 in
let F7 := bops_llex_product_exists_id_ann_not_equal_left_v3 S T eqS eqT argT eqvS eqvT bS1 bS2 bT1 bT2  in 

let E5 := extract_exist_id_from_exists_id_ann_equal S eqS bS1 bS2 in
let E1 := extract_exist_id_from_exists_id_ann_equal T eqT bT1 bT2 in 

let E6 := extract_exist_ann_from_exists_id_ann_equal S eqS bS1 bS2 in
let E3 := extract_exist_ann_from_exists_id_ann_equal T eqT bT1 bT2 in

let E7 := extract_exist_id_from_exists_id_ann_not_equal S eqS bS1 bS2 in
let E2 := extract_exist_id_from_exists_id_ann_not_equal T eqT bT1 bT2 in 

let E8 := extract_exist_ann_from_exists_id_ann_not_equal S eqS bS1 bS2 in 
let E4 := extract_exist_ann_from_exists_id_ann_not_equal T eqT bT1 bT2 in

match PS with 
| Id_Ann_Proof_None _ _ _ _ (nidS, nannS)               =>
     Id_Ann_Proof_None _ _ _ _ (F1 (inl nidS), F2 (inl nannS))
| Id_Ann_Proof_Id_None _ _ _ _ (idS, nannS) =>
  match PT with 
  | Id_Ann_Proof_None _ _ _ _ (nidT, nannT)             =>
       Id_Ann_Proof_None _ _ _ _ (F1 (inr nidT), F2 (inl nannS))           
  | Id_Ann_Proof_Id_None _ _ _ _ (idT, nannT)           =>
       Id_Ann_Proof_Id_None _ _ _ _ (F0 idS idT, F2 (inl nannS))
  | Id_Ann_Proof_None_Ann _ _ _ _ (nidT, annT)          =>
       Id_Ann_Proof_None _ _ _ _ (F1 (inr nidT), F2 (inl nannS))                     
  | Id_Ann_Proof_Equal _ _ _ _ (idT_annT_equal)         =>
       Id_Ann_Proof_Id_None _ _ _ _ (F0 idS (E1 idT_annT_equal), F2 (inl nannS))              
  | Id_Ann_Proof_Not_Equal _ _ _ _ (idT_annT_not_equal) =>
       Id_Ann_Proof_Id_None _ _ _ _ (F0 idS (E2 idT_annT_not_equal), F2 (inl nannS))              
  end   
| Id_Ann_Proof_None_Ann _ _ _ _ (nidS, annS) =>
  match PT with 
  | Id_Ann_Proof_None _ _ _ _ (nidT, nannT)             =>
       Id_Ann_Proof_None _ _ _ _ (F1 (inl nidS),F2 (inr nannT))           
  | Id_Ann_Proof_Id_None _ _ _ _ (idT, nannT)           =>
       Id_Ann_Proof_None _ _ _ _ (F1 (inl nidS), F2 (inr nannT))                         
  | Id_Ann_Proof_None_Ann _ _ _ _ (nidT, annT)          =>
       Id_Ann_Proof_None_Ann _ _ _ _ (F1 (inl nidS), F3 annS annT)                      
  | Id_Ann_Proof_Equal _ _ _ _ (idT_annT_equal)         =>
       Id_Ann_Proof_None_Ann _ _ _ _ (F1 (inl nidS), F3 annS (E3 idT_annT_equal))  
  | Id_Ann_Proof_Not_Equal _ _ _ _ (idT_annT_not_equal) =>
       Id_Ann_Proof_None_Ann _ _ _ _ (F1 (inl nidS), F3 annS (E4 idT_annT_not_equal))   
  end   
| Id_Ann_Proof_Equal _ _ _ _ (idS_annS_equal)  =>
  match PT with 
  | Id_Ann_Proof_None _ _ _ _ (nidT, nannT)             =>
       Id_Ann_Proof_None _ _ _ _ (F1 (inr nidT), F2 (inr nannT))                      
  | Id_Ann_Proof_Id_None _ _ _ _ (idT, nannT)           =>
       Id_Ann_Proof_Id_None _ _ _ _ (F0 (E5 idS_annS_equal) idT, F2 (inr nannT))
  | Id_Ann_Proof_None_Ann _ _ _ _ (nidT, annT)          =>
       Id_Ann_Proof_None_Ann _ _ _ _ (F1 (inr nidT), F3 (E6 idS_annS_equal) annT)
  | Id_Ann_Proof_Equal _ _ _ _ (idT_annT_equal)         =>
       Id_Ann_Proof_Equal _ _ _ _ (F4 idS_annS_equal idT_annT_equal)
  | Id_Ann_Proof_Not_Equal _ _ _ _ (idT_annT_not_equal) =>
       Id_Ann_Proof_Not_Equal _ _ _ _ (F5 idS_annS_equal idT_annT_not_equal)
  end   
| Id_Ann_Proof_Not_Equal _ _ _ _ (idS_annS_not_equal)  =>
  match PT with 
  | Id_Ann_Proof_None _ _ _ _ (nidT, nannT)             =>
       Id_Ann_Proof_None _ _ _ _ (F1 (inr nidT), F2 (inr nannT))             
  | Id_Ann_Proof_Id_None _ _ _ _ (idT, nannT)           =>
    Id_Ann_Proof_Id_None _ _ _ _ (F0 (E7 idS_annS_not_equal) idT, F2 (inr nannT))                    
  | Id_Ann_Proof_None_Ann _ _ _ _ (nidT, annT)          =>
       Id_Ann_Proof_None_Ann _ _ _ _ (F1 (inr nidT), F3 (E8 idS_annS_not_equal) annT)
  | Id_Ann_Proof_Equal _ _ _ _ (idT_annT_equal)         =>
       Id_Ann_Proof_Not_Equal _ _ _ _ (F6 idS_annS_not_equal idT_annT_equal)
  | Id_Ann_Proof_Not_Equal _ _ _ _ (idT_annT_not_equal) =>
       Id_Ann_Proof_Not_Equal _ _ _ _ (F7 idS_annS_not_equal idT_annT_not_equal)
  end   
end. 


Definition bops_llex_product_exists_id_ann_decide_right
           (S T : Type) (eqS : brel S) (eqT : brel T) (argT : T)
           (eqvS : eqv_proofs S eqS)
           (eqvT : eqv_proofs T eqT)
           (bS1 bS2 : binary_op S)
           (bT1 bT2 : binary_op T)           
           (PS : exists_id_ann_decidable S eqS bS2 bS1)
           (PT : exists_id_ann_decidable T eqT bT2 bT1) :
           exists_id_ann_decidable (S * T)
                                   (brel_product eqS eqT)
                                   (bop_product bS2 bT2)
                                   (bop_llex argT eqS bS1 bT1) :=
let symS := A_eqv_symmetric _ _ eqvS in
let refT := A_eqv_reflexive _ _ eqvT in     
let F0 := bop_llex_exists_ann S T eqS eqT bS1 bT1 symS argT refT    in
let F1 := bop_llex_not_exists_ann S T eqS eqT bS1 bT1 symS argT in  

let F3 := bop_product_exists_id S T eqS eqT bS2 bT2     in 
let F2 := bop_product_not_exists_id S T eqS eqT bS2 bT2 in

let F4 := bops_llex_product_exists_id_ann_equal_right S T eqS eqT argT eqvS eqvT bS1 bS2 bT1 bT2  in 
let F5 := bops_llex_product_exists_id_ann_not_equal_right_v2 S T eqS eqT argT eqvS eqvT bS1 bS2 bT1 bT2  in 
let F6 := bops_llex_product_exists_id_ann_not_equal_right_v1 S T eqS eqT argT eqvS eqvT bS1 bS2 bT1 bT2  in
let F7 := bops_llex_product_exists_id_ann_not_equal_right_v3 S T eqS eqT argT eqvS eqvT bS1 bS2 bT1 bT2  in 

let E5 := extract_exist_id_from_exists_id_ann_equal S eqS bS2 bS1 in
let E1 := extract_exist_id_from_exists_id_ann_equal T eqT bT2 bT1 in 

let E6 := extract_exist_ann_from_exists_id_ann_equal S eqS bS2 bS1 in
let E3 := extract_exist_ann_from_exists_id_ann_equal T eqT bT2 bT1 in

let E7 := extract_exist_id_from_exists_id_ann_not_equal S eqS bS2 bS1 in
let E2 := extract_exist_id_from_exists_id_ann_not_equal T eqT bT2 bT1 in 

let E8 := extract_exist_ann_from_exists_id_ann_not_equal S eqS bS2 bS1 in 
let E4 := extract_exist_ann_from_exists_id_ann_not_equal T eqT bT2 bT1 in

match PS with 
| Id_Ann_Proof_None _ _ _ _ (nidS, nannS)               =>
     Id_Ann_Proof_None _ _ _ _ (F2 (inl nidS), F1 (inl nannS))
| Id_Ann_Proof_Id_None _ _ _ _ (idS, nannS) =>
  match PT with 
  | Id_Ann_Proof_None _ _ _ _ (nidT, nannT)             =>
       Id_Ann_Proof_None _ _ _ _ (F2 (inr nidT), F1 (inl nannS))           
  | Id_Ann_Proof_Id_None _ _ _ _ (idT, nannT)           =>
       Id_Ann_Proof_Id_None _ _ _ _ (F3 idS idT, F1 (inl nannS))
  | Id_Ann_Proof_None_Ann _ _ _ _ (nidT, annT)          =>
       Id_Ann_Proof_None _ _ _ _ (F2 (inr nidT), F1 (inl nannS))                     
  | Id_Ann_Proof_Equal _ _ _ _ (idT_annT_equal)         =>
       Id_Ann_Proof_Id_None _ _ _ _ (F3 idS (E1 idT_annT_equal), F1 (inl nannS))              
  | Id_Ann_Proof_Not_Equal _ _ _ _ (idT_annT_not_equal) =>
       Id_Ann_Proof_Id_None _ _ _ _ (F3 idS (E2 idT_annT_not_equal), F1 (inl nannS))              
  end   
| Id_Ann_Proof_None_Ann _ _ _ _ (nidS, annS) =>
  match PT with 
  | Id_Ann_Proof_None _ _ _ _ (nidT, nannT)             =>
       Id_Ann_Proof_None _ _ _ _ (F2 (inl nidS), F1 (inr nannT))           
  | Id_Ann_Proof_Id_None _ _ _ _ (idT, nannT)           =>
       Id_Ann_Proof_None _ _ _ _ (F2 (inl nidS), F1 (inr nannT))                         
  | Id_Ann_Proof_None_Ann _ _ _ _ (nidT, annT)          =>
       Id_Ann_Proof_None_Ann _ _ _ _ (F2 (inl nidS), F0 annS annT)                      
  | Id_Ann_Proof_Equal _ _ _ _ (idT_annT_equal)         =>
       Id_Ann_Proof_None_Ann _ _ _ _ (F2 (inl nidS), F0 annS (E3 idT_annT_equal))  
  | Id_Ann_Proof_Not_Equal _ _ _ _ (idT_annT_not_equal) =>
       Id_Ann_Proof_None_Ann _ _ _ _ (F2 (inl nidS), F0 annS (E4 idT_annT_not_equal))   
  end   
| Id_Ann_Proof_Equal _ _ _ _ (idS_annS_equal)  =>
  match PT with 
  | Id_Ann_Proof_None _ _ _ _ (nidT, nannT)             =>
       Id_Ann_Proof_None _ _ _ _ (F2 (inr nidT), F1 (inr nannT))                      
  | Id_Ann_Proof_Id_None _ _ _ _ (idT, nannT)           =>
       Id_Ann_Proof_Id_None _ _ _ _ (F3 (E5 idS_annS_equal) idT, F1 (inr nannT))
  | Id_Ann_Proof_None_Ann _ _ _ _ (nidT, annT)          =>
       Id_Ann_Proof_None_Ann _ _ _ _ (F2 (inr nidT), F0 (E6 idS_annS_equal) annT)
  | Id_Ann_Proof_Equal _ _ _ _ (idT_annT_equal)         =>
       Id_Ann_Proof_Equal _ _ _ _ (F4 idS_annS_equal idT_annT_equal)
  | Id_Ann_Proof_Not_Equal _ _ _ _ (idT_annT_not_equal) =>
       Id_Ann_Proof_Not_Equal _ _ _ _ (F5 idS_annS_equal idT_annT_not_equal)
  end   
| Id_Ann_Proof_Not_Equal _ _ _ _ (idS_annS_not_equal)  =>
  match PT with 
  | Id_Ann_Proof_None _ _ _ _ (nidT, nannT)             =>
       Id_Ann_Proof_None _ _ _ _ (F2 (inr nidT), F1 (inr nannT))             
  | Id_Ann_Proof_Id_None _ _ _ _ (idT, nannT)           =>
    Id_Ann_Proof_Id_None _ _ _ _ (F3 (E7 idS_annS_not_equal) idT, F1 (inr nannT))                    
  | Id_Ann_Proof_None_Ann _ _ _ _ (nidT, annT)          =>
       Id_Ann_Proof_None_Ann _ _ _ _ (F2 (inr nidT), F0 (E8 idS_annS_not_equal) annT)
  | Id_Ann_Proof_Equal _ _ _ _ (idT_annT_equal)         =>
       Id_Ann_Proof_Not_Equal _ _ _ _ (F6 idS_annS_not_equal idT_annT_equal)
  | Id_Ann_Proof_Not_Equal _ _ _ _ (idT_annT_not_equal) =>
       Id_Ann_Proof_Not_Equal _ _ _ _ (F7 idS_annS_not_equal idT_annT_not_equal)
  end   
end. 



    

Variable S T : Type.
Variable wS : S.
Variable wT : T.    
Variable argT : T.  
Variable rS : brel S.
Variable rT : brel T.   
Variable addS : binary_op S.
Variable mulS : binary_op S. 
Variable addT : binary_op T.
Variable mulT : binary_op T.
Variable eqvS : eqv_proofs S rS.
Variable eqvT : eqv_proofs T rT.   

Variable idem_addS : bop_idempotent S rS addS.  (* needed for associativity of llex *)
Variable comm_addS : bop_commutative S rS addS. (* needed for associativity of llex *)
Variable cng_addS  : bop_congruence S rS addS.
Variable cng_mulS  : bop_congruence S rS mulS. 
Variable cng_addT  : bop_congruence T rT addT.
Variable cng_mulT  : bop_congruence T rT mulT. 


Definition bops_llex_product_left_distributive_decide
           (comm_addT : bop_commutative T rT addT) 
           (selS_or_id_annT : bop_selective S rS addS + (bop_is_id T rT addT argT * bop_is_ann T rT mulT argT))           
           (ldS_d : bop_left_distributive_decidable S rS addS mulS)
           (ldT_d : bop_left_distributive_decidable T rT addT mulT)            
           (lcS_d : bop_left_cancellative_decidable S rS mulS)
           (lkT_d : bop_left_constant_decidable T rT mulT) : 
              bop_left_distributive_decidable (S * T) (brel_product rS rT) (bop_llex argT rS addS addT) (bop_product mulS mulT) :=
let selS_or_annT :=
    match selS_or_id_annT with
    | inl selS => inl selS
    | inr (_, annT) => inr annT 
    end
in
let cngS := A_eqv_congruence S rS eqvS in 
let refS := A_eqv_reflexive S rS eqvS in 
let symS := A_eqv_symmetric S rS eqvS in 
let trnS := A_eqv_transitive S rS eqvS in 
let refT := A_eqv_reflexive T rT eqvT in
let symT := A_eqv_symmetric T rT eqvT in 
let trnT := A_eqv_transitive T rT eqvT in 
let F0 := bop_llex_product_left_distributive S T rS rT argT addS mulS addT mulT cngS refS symS
                                             trnS refT trnT cng_addS cng_mulS idem_addS selS_or_annT in 
let F1 := bop_llex_product_not_left_distributive_v1 S T rS rT wT argT addS mulS addT mulT in 
let F2 := bop_llex_product_not_left_distributive_v2 S T rS rT wS argT addS mulS addT mulT symS idem_addS  in
let F3 := bop_llex_product_not_left_distributive_v3 S T rS rT argT addS mulS addT mulT refS symS
                                                    trnS refT symT trnT cng_addS cng_mulS cng_addT idem_addS comm_addT selS_or_id_annT in 
match ldS_d with 
| inl ldS =>
   match ldT_d with 
   | inl ldT =>
       match lcS_d with 
       | inl lcS => inl _ (F0 ldS ldT (inl _ lcS))
       | inr not_lcS => 
            match lkT_d with 
            | inl lkT => inl _ (F0 ldS ldT (inr _ lkT))
            | inr not_lkT => inr _ (F3 ldS ldT not_lcS not_lkT)
                                     
            end 
       end 
   |inr not_ldT => inr _ (F2 not_ldT)
   end 
|inr not_ldS => inr _ (F1 not_ldS ) 
end. 


  
Definition bops_llex_product_right_distributive_decide
           (comm_addT : bop_commutative T rT addT) (*NB*)
           (selS_or_id_annT : bop_selective S rS addS + (bop_is_id T rT addT argT * bop_is_ann T rT mulT argT))           
           (rdS_d : bop_right_distributive_decidable S rS addS mulS)
           (rdT_d : bop_right_distributive_decidable T rT addT mulT)            
           (rcS_d : bop_right_cancellative_decidable S rS mulS)
           (rkT_d : bop_right_constant_decidable T rT mulT) : 
              bop_right_distributive_decidable (S * T) (brel_product rS rT) (bop_llex argT rS addS addT) (bop_product mulS mulT) :=
let selS_or_annT :=
    match selS_or_id_annT with
    | inl selS => inl selS
    | inr (_, annT) => inr annT 
    end
in
let cngS := A_eqv_congruence S rS eqvS in 
let refS := A_eqv_reflexive S rS eqvS in 
let symS := A_eqv_symmetric S rS eqvS in 
let trnS := A_eqv_transitive S rS eqvS in 
let refT := A_eqv_reflexive T rT eqvT in
let symT := A_eqv_symmetric T rT eqvT in 
let trnT := A_eqv_transitive T rT eqvT in 
let F0 := bop_llex_product_right_distributive S T rS rT argT addS mulS addT mulT cngS refS symS
                                             trnS refT trnT cng_addS cng_mulS idem_addS selS_or_annT in 
let F1 := bop_llex_product_not_right_distributive_v1 S T rS rT wT argT addS mulS addT mulT in 
let F2 := bop_llex_product_not_right_distributive_v2 S T rS rT wS argT addS mulS addT mulT symS idem_addS  in
let F3 := bop_llex_product_not_right_distributive_v3 S T rS rT argT addS mulS addT mulT refS symS
                                                    trnS refT symT trnT cng_addS cng_mulS cng_addT idem_addS comm_addT selS_or_id_annT in
match rdS_d with 
| inl rdS =>
   match rdT_d with 
   | inl rdT =>
       match rcS_d with 
       | inl rcS => inl _ (F0 rdS rdT (inl _ rcS))
       | inr not_rcS => 
            match rkT_d with 
            | inl rkT => inl _ (F0 rdS rdT (inr _ rkT))
            | inr not_rkT => inr _ (F3 rdS rdT not_rcS not_rkT)
            end 
       end 
   |inr not_rdT => inr _ (F2 not_rdT)
   end 
|inr not_rdS => inr _ (F1 not_rdS ) 
end. 


Definition bops_llex_product_left_left_absorptive_decide 
      (laS_d : bops_left_left_absorptive_decidable S rS addS mulS)
      (laT_d : bops_left_left_absorptive_decidable T rT addT mulT) 
      (antilS_d : bop_anti_left_decidable S rS mulS) : 
         bops_left_left_absorptive_decidable (S * T) (brel_product rS rT) (bop_llex argT rS addS addT) (bop_product mulS mulT) :=
let refS := A_eqv_reflexive S rS eqvS in 
let trnS := A_eqv_transitive S rS eqvS in 
let refT := A_eqv_reflexive T rT eqvT in
let F0 := bops_llex_product_left_left_absorptive S T rS rT argT addS mulS addT mulT trnS refT in 
let F1 := bops_llex_product_not_left_left_absorptive_left S T rS rT wT argT addS mulS addT mulT in
let F2 := bops_llex_product_not_left_left_absorptive_right S T rS rT argT addS mulS addT mulT refS trnS cng_addS idem_addS in 
match laS_d with 
|inl laS =>
   match laT_d with 
   |inl laT =>  inl _ (F0 laS (inl _ laT))
   |inr not_laT  => 
       match antilS_d with 
       | inl antilS => inl _ (F0 laS (inr _ antilS))
       | inr not_antilS => inr _ (F2 laS not_laT not_antilS)
       end 
   end 
|inr not_laS => inr _ (F1 not_laS) 
end. 


Definition bops_llex_product_left_right_absorptive_decide 
      (laS_d : bops_left_right_absorptive_decidable S rS addS mulS)
      (laT_d : bops_left_right_absorptive_decidable T rT addT mulT) 
      (antilS_d : bop_anti_right_decidable S rS mulS) : 
         bops_left_right_absorptive_decidable (S * T) (brel_product rS rT) (bop_llex argT rS addS addT) (bop_product mulS mulT) :=
let refS := A_eqv_reflexive S rS eqvS in 
let trnS := A_eqv_transitive S rS eqvS in 
let refT := A_eqv_reflexive T rT eqvT in
let F0 := bops_llex_product_left_right_absorptive S T rS rT argT addS mulS addT mulT trnS refT in 
let F1 := bops_llex_product_not_left_right_absorptive_left S T rS rT wT argT addS mulS addT mulT in
let F2 := bops_llex_product_not_left_right_absorptive_right S T rS rT argT addS mulS addT mulT refS trnS cng_addS idem_addS in 
match laS_d with 
|inl laS =>
   match laT_d with 
   |inl laT =>  inl _ (F0 laS (inl _ laT))
   |inr not_laT  => 
       match antilS_d with 
       | inl antilS => inl _ (F0 laS (inr _ antilS))
       | inr not_antilS => inr _ (F2 laS not_laT not_antilS)
       end 
   end 
|inr not_laS => inr _ (F1 not_laS) 
end. 

Definition bops_llex_product_right_left_absorptive_decide 
      (laS_d : bops_right_left_absorptive_decidable S rS addS mulS)
      (laT_d : bops_right_left_absorptive_decidable T rT addT mulT) 
      (antilS_d : bop_anti_left_decidable S rS mulS) : 
         bops_right_left_absorptive_decidable (S * T) (brel_product rS rT) (bop_llex argT rS addS addT) (bop_product mulS mulT) :=
let refS := A_eqv_reflexive S rS eqvS in
let symS := A_eqv_symmetric S rS eqvS in   
let trnS := A_eqv_transitive S rS eqvS in 
let refT := A_eqv_reflexive T rT eqvT in
let F0 := bops_llex_product_right_left_absorptive S T rS rT argT addS mulS addT mulT symS trnS refT in 
let F1 := bops_llex_product_not_right_left_absorptive_left S T rS rT wT argT addS mulS addT mulT in
let F2 := bops_llex_product_not_right_left_absorptive_right S T rS rT argT addS mulS addT mulT refS symS trnS cng_addS idem_addS in 
match laS_d with 
|inl laS =>
   match laT_d with 
   |inl laT =>  inl _ (F0 laS (inl _ laT))
   |inr not_laT  => 
       match antilS_d with 
       | inl antilS => inl _ (F0 laS (inr _ antilS))
       | inr not_antilS => inr _ (F2 laS not_laT not_antilS)
       end 
   end 
|inr not_laS => inr _ (F1 not_laS) 
end. 

Definition bops_llex_product_right_right_absorptive_decide 
      (laS_d : bops_right_right_absorptive_decidable S rS addS mulS)
      (laT_d : bops_right_right_absorptive_decidable T rT addT mulT) 
      (antilS_d : bop_anti_right_decidable S rS mulS) : 
         bops_right_right_absorptive_decidable (S * T) (brel_product rS rT) (bop_llex argT rS addS addT) (bop_product mulS mulT) :=
let refS := A_eqv_reflexive S rS eqvS in
let symS := A_eqv_symmetric S rS eqvS in   
let trnS := A_eqv_transitive S rS eqvS in 
let refT := A_eqv_reflexive T rT eqvT in
let F0 := bops_llex_product_right_right_absorptive S T rS rT argT addS mulS addT mulT symS trnS refT in 
let F1 := bops_llex_product_not_right_right_absorptive_left S T rS rT wT argT addS mulS addT mulT in
let F2 := bops_llex_product_not_right_right_absorptive_right S T rS rT argT addS mulS addT mulT refS symS trnS cng_addS idem_addS in 
match laS_d with 
|inl laS =>
   match laT_d with 
   |inl laT =>  inl _ (F0 laS (inl _ laT))
   |inr not_laT  => 
       match antilS_d with 
       | inl antilS => inl _ (F0 laS (inr _ antilS))
       | inr not_antilS => inr _ (F2 laS not_laT not_antilS)
       end 
   end 
|inr not_laS => inr _ (F1 not_laS) 
end. 


End Decide. 

Section Proofs.     
(*
  id_ann_proofs

A_id_ann_plus_times_d
     : ∀ (S : Type) (eq : brel S) (plus times : binary_op S),
         id_ann_proofs S eq plus times
         → exists_id_ann_decidable S eq plus times

A_id_ann_times_plus_d
     : ∀ (S : Type) (eq : brel S) (plus times : binary_op S),
         id_ann_proofs S eq plus times
         → exists_id_ann_decidable S eq times plus


bops_llex_product_exists_id_ann_decide_left 
     : ∀ (S T : Type) (eqS : brel S) (eqT : brel T) (argT : T),
         brel_symmetric S eqS
         → brel_transitive S eqS
           → brel_reflexive T eqT
             → ∀ (bS1 bS2 : binary_op S) (bT1 bT2 : binary_op T),
                 bop_commutative S eqS bS1
                 → exists_id_ann_decidable S eqS bS1 bS2
                   → exists_id_ann_decidable T eqT bT1 bT2
                     → exists_id_ann_decidable (S * T) 
                         (brel_product eqS eqT) (bop_llex argT eqS bS1 bT1)
                         (bop_product bS2 bT2)

So, have 

A_id_ann_plus_times_d : exists_id_ann_decidable S eqS plusS timesS
A_id_ann_times_plus_d : exists_id_ann_decidable S eq timesS plusS
and 
A_id_ann_plus_times_d : exists_id_ann_decidable T eqT plusT timesT
A_id_ann_times_plus_d : exists_id_ann_decidable T eqT timesT plusT

want 

A_id_ann_plus_times_d : exists_id_ann_decidable (S * T) 
                         (brel_product eqS eqT) (bop_llex argT eqS plusS plusT)
                         (bop_product timesS timesT)

from bops_llex_product_exists_id_ann_decide_left. 

I need 

A_id_ann_times_plus_d : exists_id_ann_decidable (S * T) 
                         (brel_product eqS eqT) (bop_product timesS timesT)
                         (bop_llex argT eqS plusS plusT)


bops_llex_product_exists_id_ann_decide_right: 
     : ∀ (S T : Type) (eqS : brel S) (eqT : brel T) (argT : T),
         brel_symmetric S eqS
         → brel_transitive S eqS
           → brel_reflexive T eqT
             → ∀ (bS1 bS2 : binary_op S) (bT1 bT2 : binary_op T),
                 bop_commutative S eqS bS1
                 → exists_id_ann_decidable S eqS bS2 bS1
                   → exists_id_ann_decidable T eqT bT2 bT1
                     → exists_id_ann_decidable (S * T) 
                         (brel_product eqS eqT) 
                         (bop_product bS2 bT2)
                         (bop_llex argT eqS bS1 bT1)

 *)

Variable S T : Type.
Variable wS : S.
Variable wT : T.    
Variable argT : T.  
Variable rS : brel S.
Variable rT : brel T.   
Variable addS : binary_op S.
Variable mulS : binary_op S. 
Variable addT : binary_op T.
Variable mulT : binary_op T.
Variable eqvS : eqv_proofs S rS.
Variable eqvT : eqv_proofs T rT.   

(*
Variable idem_addS : bop_idempotent S rS addS.  (* needed for associativity of llex *)
Variable comm_addS : bop_commutative S rS addS. (* needed for associativity of llex *)
Variable cng_addS  : bop_congruence S rS addS.
Variable cng_mulS  : bop_congruence S rS mulS. 
Variable cng_addT  : bop_congruence T rT addT.
Variable cng_mulT  : bop_congruence T rT mulT. 
*) 

  
Definition id_ann_proofs_llex_product
 (pS : id_ann_proofs S rS addS mulS)
 (pT : id_ann_proofs T rT addT mulT) : 
        id_ann_proofs (S * T) 
           (brel_product rS rT) 
           (bop_llex argT rS addS addT)
           (bop_product mulS mulT) := 
let pS_id_ann_plus_times_d := A_id_ann_plus_times_d _ _ _ _ pS in 
let pS_id_ann_times_plus_d := A_id_ann_times_plus_d _ _ _ _ pS in 
let pT_id_ann_plus_times_d := A_id_ann_plus_times_d _ _ _ _ pT in 
let pT_id_ann_times_plus_d := A_id_ann_times_plus_d _ _ _ _ pT in 
{|
  A_id_ann_plus_times_d := bops_llex_product_exists_id_ann_decide_left S T rS rT argT eqvS eqvT
                              addS mulS addT mulT pS_id_ann_plus_times_d pT_id_ann_plus_times_d 
; A_id_ann_times_plus_d := bops_llex_product_exists_id_ann_decide_right S T rS rT argT eqvS eqvT
                              addS mulS addT mulT pS_id_ann_times_plus_d pT_id_ann_times_plus_d
|}.

(*   bs_proofs   *) 


Definition bs_proofs_llex_product_v1
           (id_is_annT : (bop_is_id T rT addT argT) * (bop_is_ann T rT mulT argT))
           (addPS : sg_CI_proofs S rS addS)
           (addPT : sg_CI_proofs T rT addT)
           (mulPS : msg_proofs S rS mulS)
           (mulPT : msg_proofs T rT mulT)
           (pS : bs_proofs  S rS addS mulS)
           (pT : bs_proofs  T rT addT mulT) : 
                bs_proofs (S * T) (brel_product rS rT) (bop_llex argT rS addS addT) (bop_product mulS mulT) := 
let idem_addS := A_sg_CI_idempotent _ _ _ addPS in 
let comm_addT := A_sg_CI_commutative _ _ _ addPT in
let cng_addS := A_sg_CI_congruence _ _ _ addPS in
let cng_mulS := A_msg_congruence _ _ _ mulPS in 
let cng_addT := A_sg_CI_congruence _ _ _ addPT in 
let LC := A_msg_left_cancel_d _ _ _ mulPS  in 
let RC := A_msg_right_cancel_d _ _ _ mulPS in
let LK := A_msg_left_constant_d _ _ _ mulPT in 
let RK := A_msg_right_constant_d _ _ _ mulPT in                
let ALS := A_msg_anti_left_d _ _ _ mulPS in 
let ARS := A_msg_anti_right_d _ _ _ mulPS in 
let LDS := A_bs_left_distributive_d _ _ _ _ pS in 
let LDT := A_bs_left_distributive_d _ _ _ _  pT in 
let RDS := A_bs_right_distributive_d _ _ _ _ pS in 
let RDT := A_bs_right_distributive_d _ _ _ _ pT in
let LLAS := A_bs_left_left_absorptive_d _ _ _ _ pS in
let LLAT := A_bs_left_left_absorptive_d _ _ _ _ pT in
let LRAS := A_bs_left_right_absorptive_d _ _ _ _ pS in
let LRAT := A_bs_left_right_absorptive_d _ _ _ _ pT in
let RLAS := A_bs_right_left_absorptive_d _ _ _ _ pS in
let RLAT := A_bs_right_left_absorptive_d _ _ _ _ pT in
let RRAS := A_bs_right_right_absorptive_d _ _ _ _ pS in
let RRAT := A_bs_right_right_absorptive_d _ _ _ _ pT in
{|
  A_bs_left_distributive_d    := 
    bops_llex_product_left_distributive_decide S T wS wT argT rS rT addS mulS addT mulT eqvS eqvT idem_addS
                                               cng_addS cng_mulS cng_addT comm_addT (inr id_is_annT) LDS LDT LC LK 
; A_bs_right_distributive_d   := 
    bops_llex_product_right_distributive_decide S T wS wT argT rS rT addS mulS addT mulT eqvS eqvT idem_addS
                                                cng_addS cng_mulS cng_addT comm_addT (inr id_is_annT) RDS RDT RC RK 
; A_bs_left_left_absorptive_d      := 
    bops_llex_product_left_left_absorptive_decide S T wT argT rS rT addS mulS addT mulT eqvS eqvT idem_addS
                                                cng_addS LLAS LLAT ALS 
; A_bs_left_right_absorptive_d      := 
    bops_llex_product_left_right_absorptive_decide S T wT argT rS rT addS mulS addT mulT eqvS eqvT idem_addS
                                                cng_addS LRAS LRAT ARS 
; A_bs_right_left_absorptive_d      := 
    bops_llex_product_right_left_absorptive_decide S T wT argT rS rT addS mulS addT mulT eqvS eqvT idem_addS
                                                cng_addS RLAS RLAT ALS 
; A_bs_right_right_absorptive_d      := 
    bops_llex_product_right_right_absorptive_decide S T wT argT rS rT addS mulS addT mulT eqvS eqvT idem_addS
                                                cng_addS RRAS RRAT ARS 
|}.

Definition bs_proofs_llex_product_v2 
           (addPS : sg_CS_proofs S rS addS)
           (addPT : sg_CI_proofs T rT addT)
           (mulPS : msg_proofs S rS mulS)
           (mulPT : msg_proofs T rT mulT)
           (pS : bs_proofs  S rS addS mulS)
           (pT : bs_proofs  T rT addT mulT) : 
                bs_proofs (S * T) (brel_product rS rT) (bop_llex argT rS addS addT) (bop_product mulS mulT) := 
let selS     := A_sg_CS_selective _ _ _ addPS in
let idem_addS := bop_selective_implies_idempotent S rS addS selS in 
let comm_addT := A_sg_CI_commutative _ _ _ addPT in
let cng_addS := A_sg_CS_congruence _ _ _ addPS in
let cng_mulS := A_msg_congruence _ _ _ mulPS in 
let cng_addT := A_sg_CI_congruence _ _ _ addPT in 
let LC := A_msg_left_cancel_d _ _ _ mulPS  in 
let RC := A_msg_right_cancel_d _ _ _ mulPS in
let LK := A_msg_left_constant_d _ _ _ mulPT in 
let RK := A_msg_right_constant_d _ _ _ mulPT in                
let ALS := A_msg_anti_left_d _ _ _ mulPS in 
let ARS := A_msg_anti_right_d _ _ _ mulPS in 
let LDS := A_bs_left_distributive_d _ _ _ _ pS in 
let LDT := A_bs_left_distributive_d _ _ _ _  pT in 
let RDS := A_bs_right_distributive_d _ _ _ _ pS in 
let RDT := A_bs_right_distributive_d _ _ _ _ pT in
let LLAS := A_bs_left_left_absorptive_d _ _ _ _ pS in
let LLAT := A_bs_left_left_absorptive_d _ _ _ _ pT in
let LRAS := A_bs_left_right_absorptive_d _ _ _ _ pS in
let LRAT := A_bs_left_right_absorptive_d _ _ _ _ pT in
let RLAS := A_bs_right_left_absorptive_d _ _ _ _ pS in
let RLAT := A_bs_right_left_absorptive_d _ _ _ _ pT in
let RRAS := A_bs_right_right_absorptive_d _ _ _ _ pS in
let RRAT := A_bs_right_right_absorptive_d _ _ _ _ pT in
{|
  A_bs_left_distributive_d    := 
    bops_llex_product_left_distributive_decide S T wS wT argT rS rT addS mulS addT mulT eqvS eqvT idem_addS
                                               cng_addS cng_mulS cng_addT comm_addT (inl selS) LDS LDT LC LK 
; A_bs_right_distributive_d   := 
    bops_llex_product_right_distributive_decide S T wS wT argT rS rT addS mulS addT mulT eqvS eqvT idem_addS
                                                cng_addS cng_mulS cng_addT comm_addT (inl selS) RDS RDT RC RK 
; A_bs_left_left_absorptive_d      := 
    bops_llex_product_left_left_absorptive_decide S T wT argT rS rT addS mulS addT mulT eqvS eqvT idem_addS
                                                cng_addS LLAS LLAT ALS 
; A_bs_left_right_absorptive_d      := 
    bops_llex_product_left_right_absorptive_decide S T wT argT rS rT addS mulS addT mulT eqvS eqvT idem_addS
                                                cng_addS LRAS LRAT ARS 
; A_bs_right_left_absorptive_d      := 
    bops_llex_product_right_left_absorptive_decide S T wT argT rS rT addS mulS addT mulT eqvS eqvT idem_addS
                                                cng_addS RLAS RLAT ALS 
; A_bs_right_right_absorptive_d      := 
    bops_llex_product_right_right_absorptive_decide S T wT argT rS rT addS mulS addT mulT eqvS eqvT idem_addS
                                                cng_addS RRAS RRAT ARS 
|}.




(* *) 

End Proofs.

Section Combinators.



Definition A_llex_product_from_CS_CI (S T : Type) (A : A_bs_CS S) (B : A_bs_CI T) : A_bs_CI (S * T) :=
let eqvS   := A_bs_CS_eqv _ A in
let eqvT   := A_bs_CI_eqv _ B in
let eqS    := A_eqv_eq _ eqvS in
let eqT    := A_eqv_eq _ eqvT in
let eqvPS  := A_eqv_proofs _ eqvS in
let eqvPT  := A_eqv_proofs _ eqvT in
let plusS  := A_bs_CS_plus _ A in
let plusT  := A_bs_CI_plus _ B in
let timesS  := A_bs_CS_times _ A in
let timesT  := A_bs_CI_times _ B in
let id_annS  := A_bs_CS_id_ann_proofs _ A in
let id_annT  := A_bs_CI_id_ann_proofs _ B in
let plusPS  := A_bs_CS_plus_proofs _ A in
let plusPT  := A_bs_CI_plus_proofs _ B in
let timesPS  := A_bs_CS_times_proofs _ A in
let timesPT  := A_bs_CI_times_proofs _ B in
let pS       := A_bs_CS_proofs _ A in
let pT       := A_bs_CI_proofs _ B in 
(* these should move to the A_eqv_proof structures *)
let wS     := A_eqv_witness _ eqvS in
let f      := A_eqv_new _ eqvS in
let ntS    := A_eqv_not_trivial _ eqvS in 
let wT     := A_eqv_witness _ eqvT in
let g      := A_eqv_new _ eqvT in
let ntT    := A_eqv_not_trivial _ eqvT in 
{|
  A_bs_CI_eqv           := A_eqv_product S T eqvS eqvT 
; A_bs_CI_plus          := bop_llex wT eqS plusS plusT 
; A_bs_CI_times         := bop_product timesS timesT
; A_bs_CI_plus_proofs   := sg_CI_llex_proofs_v2 S T wS wT eqS eqT plusS plusT eqvPS eqvPT plusPS plusPT 
; A_bs_CI_times_proofs  := msg_proofs_product S T eqS eqT timesS timesT wS f wT g ntS ntT eqvPS eqvPT timesPS timesPT 
; A_bs_CI_id_ann_proofs := id_ann_proofs_llex_product S T wT eqS eqT plusS timesS plusT timesT eqvPS eqvPT id_annS id_annT 
; A_bs_CI_proofs        := bs_proofs_llex_product_v2 S T wS wT wT eqS eqT plusS timesS plusT timesT eqvPS eqvPT plusPS plusPT timesPS timesPT pS pT 
; A_bs_CI_ast           := Ast_bs_llex (A_bs_CS_ast S A, A_bs_CI_ast T B)
|}.


End Combinators. 
End ACAS. 

Section CAS.


Section Certify.

Definition bops_llex_product_exists_id_ann_certify
           {S T : Type} 
           (PS : @exists_id_ann_certificate S)
           (PT : @exists_id_ann_certificate T) :
                 @exists_id_ann_certificate (S * T) := 
match PS with 
| Id_Ann_Cert_None           => Id_Ann_Cert_None  
| Id_Ann_Cert_Id_None idS    =>
  match PT with 
  | Id_Ann_Cert_None           => Id_Ann_Cert_None 
  | Id_Ann_Cert_Id_None idT    => Id_Ann_Cert_Id_None (idS, idT)
  | Id_Ann_Cert_None_Ann annT  => Id_Ann_Cert_None
  | Id_Ann_Cert_Equal idT_annT => Id_Ann_Cert_Id_None  (idS, idT_annT) 
  | Id_Ann_Cert_Not_Equal (idT, annT) => Id_Ann_Cert_Id_None  (idS, idT) 
  end   
| Id_Ann_Cert_None_Ann annS   =>
  match PT with 
  | Id_Ann_Cert_None              => Id_Ann_Cert_None  
  | Id_Ann_Cert_Id_None idT       => Id_Ann_Cert_None  
  | Id_Ann_Cert_None_Ann  annT    => Id_Ann_Cert_None_Ann (annS, annT)                      
  | Id_Ann_Cert_Equal  (idT_annT) => Id_Ann_Cert_None_Ann  (annS, idT_annT)  
  | Id_Ann_Cert_Not_Equal  (idT, annT) => Id_Ann_Cert_None_Ann  (annS, annT)  
  end   
| Id_Ann_Cert_Equal  (idS_annS)  =>
  match PT with 
  | Id_Ann_Cert_None             => Id_Ann_Cert_None 
  | Id_Ann_Cert_Id_None idT      => Id_Ann_Cert_Id_None (idS_annS, idT)
  | Id_Ann_Cert_None_Ann annT    => Id_Ann_Cert_None_Ann (idS_annS, annT)
  | Id_Ann_Cert_Equal (idT_annT) => Id_Ann_Cert_Equal (idS_annS, idT_annT)
  | Id_Ann_Cert_Not_Equal (idT, annT) => Id_Ann_Cert_Not_Equal ((idS_annS, idT), (idS_annS, annT))
  end   
| Id_Ann_Cert_Not_Equal  (idS, annS)  =>
  match PT with 
  | Id_Ann_Cert_None             => Id_Ann_Cert_None 
  | Id_Ann_Cert_Id_None idT      => Id_Ann_Cert_Id_None (idS, idT) 
  | Id_Ann_Cert_None_Ann annT    => Id_Ann_Cert_None_Ann (annS, annT)
  | Id_Ann_Cert_Equal (idT_annT) => Id_Ann_Cert_Not_Equal ((idS, idT_annT), (annS, idT_annT))
  | Id_Ann_Cert_Not_Equal (idT, annT) => Id_Ann_Cert_Not_Equal ((idS, idT), (annS, annT))
  end   
end.



Variable S T : Type.
Variable wS : S.
Variable wT : T.    
Variable argT : T.  
Variable rS : brel S.
Variable rT : brel T.   
Variable addS : binary_op S.
Variable mulS : binary_op S. 
Variable addT : binary_op T.
Variable mulT : binary_op T.

Definition bops_llex_product_left_distributive_certify_with_selectivity 
     (lcS_d : @check_left_cancellative S) 
     (lkT_d : @check_left_constant T) 
     (ldS_d : @check_left_distributive S) 
     (ldT_d : @check_left_distributive T) : 
     @check_left_distributive (S * T) := 
match ldS_d with 
| Certify_Left_Distributive => 
   match ldT_d with 
   | Certify_Left_Distributive => 
       match lcS_d with 
       | Certify_Left_Cancellative => Certify_Left_Distributive  
       | Certify_Not_Left_Cancellative (s1, (s2, s3)) => 
            match lkT_d with 
            | Certify_Left_Constant => Certify_Left_Distributive  
            | Certify_Not_Left_Constant (t1, (t2, t3)) => 
                  Certify_Not_Left_Distributive  
                    (witness_llex_product_not_left_distributive_with_selectivity S T rS rT addS mulS addT mulT s1 s2 s3 t1 t2 t3)
            end 
       end 
   | Certify_Not_Left_Distributive (t1, (t2, t3)) => 
          Certify_Not_Left_Distributive  ((wS, t1), ((wS, t2), (wS, t3))) 
   end 
| Certify_Not_Left_Distributive (s1, (s2, s3)) => 
        Certify_Not_Left_Distributive  ((s1, wT), ((s2, wT), (s3, wT))) 
end.


Definition bops_llex_product_left_distributive_certify_without_selectivity 
     (lcS_d : @check_left_cancellative S) 
     (lkT_d : @check_left_constant T) 
     (ldS_d : @check_left_distributive S) 
     (ldT_d : @check_left_distributive T) : 
     @check_left_distributive (S * T) := 
match ldS_d with 
| Certify_Left_Distributive => 
   match ldT_d with 
   | Certify_Left_Distributive => 
       match lcS_d with 
       | Certify_Left_Cancellative => Certify_Left_Distributive  
       | Certify_Not_Left_Cancellative (s1, (s2, s3)) => 
            match lkT_d with 
            | Certify_Left_Constant => Certify_Left_Distributive  
            | Certify_Not_Left_Constant (t1, (t2, t3)) => 
                  Certify_Not_Left_Distributive  
                    (witness_llex_product_not_left_distributive_without_selectivity S T rS rT argT addS mulS addT mulT s1 s2 s3 t1 t2 t3)
            end 
       end 
   | Certify_Not_Left_Distributive (t1, (t2, t3)) => 
          Certify_Not_Left_Distributive  ((wS, t1), ((wS, t2), (wS, t3))) 
   end 
| Certify_Not_Left_Distributive (s1, (s2, s3)) => 
        Certify_Not_Left_Distributive  ((s1, wT), ((s2, wT), (s3, wT))) 
end.

Definition bops_llex_product_right_distributive_check_with_selectivity 
     (lcS_d : check_right_cancellative (S := S)) 
     (lkT_d : check_right_constant (S := T)) 
     (ldS_d : check_right_distributive (S := S)) 
     (ldT_d : check_right_distributive (S := T)) : 
     check_right_distributive (S := (S * T)) 
:= 
match ldS_d with 
| Certify_Right_Distributive => 
   match ldT_d with 
   | Certify_Right_Distributive => 
       match lcS_d with 
       | Certify_Right_Cancellative => Certify_Right_Distributive  
       | Certify_Not_Right_Cancellative (s1, (s2, s3)) => 
            match lkT_d with 
            | Certify_Right_Constant => Certify_Right_Distributive  
            | Certify_Not_Right_Constant (t1, (t2, t3)) => 
                  Certify_Not_Right_Distributive  
                     (witness_llex_product_not_left_distributive_with_selectivity S T rS rT addS mulS addT mulT s1 s2 s3 t1 t2 t3) 

            end 
       end 
   | Certify_Not_Right_Distributive (t1, (t2, t3)) => 
          Certify_Not_Right_Distributive  ((wS, t1), ((wS, t2), (wS, t3))) 
   end 
| Certify_Not_Right_Distributive (s1, (s2, s3)) => 
        Certify_Not_Right_Distributive  ((s1, wT), ((s2, wT), (s3, wT))) 
end.

Definition bops_llex_product_right_distributive_check_without_selectivity 
     (lcS_d : check_right_cancellative (S := S)) 
     (lkT_d : check_right_constant (S := T)) 
     (ldS_d : check_right_distributive (S := S)) 
     (ldT_d : check_right_distributive (S := T)) : 
     check_right_distributive (S := (S * T)) 
:= 
match ldS_d with 
| Certify_Right_Distributive => 
   match ldT_d with 
   | Certify_Right_Distributive => 
       match lcS_d with 
       | Certify_Right_Cancellative => Certify_Right_Distributive  
       | Certify_Not_Right_Cancellative (s1, (s2, s3)) => 
            match lkT_d with 
            | Certify_Right_Constant => Certify_Right_Distributive  
            | Certify_Not_Right_Constant (t1, (t2, t3)) => 
                  Certify_Not_Right_Distributive  
                     (witness_llex_product_not_left_distributive_without_selectivity S T rS rT argT addS mulS addT mulT s1 s2 s3 t1 t2 t3) 

            end 
       end 
   | Certify_Not_Right_Distributive (t1, (t2, t3)) => 
          Certify_Not_Right_Distributive  ((wS, t1), ((wS, t2), (wS, t3))) 
   end 
| Certify_Not_Right_Distributive (s1, (s2, s3)) => 
        Certify_Not_Right_Distributive  ((s1, wT), ((s2, wT), (s3, wT))) 
end.

Definition bops_llex_product_left_left_absorptive_check 
     (dS : @check_left_left_absorptive S) 
     (dT : @check_left_left_absorptive T)
     (alS : @check_anti_left S) : 
        @check_left_left_absorptive (S * T) := 
match dS with 
| Certify_Left_Left_Absorptive => 
     match dT with 
     | Certify_Left_Left_Absorptive => Certify_Left_Left_Absorptive  
     | Certify_Not_Left_Left_Absorptive (t1, t2) => 
       match alS with 
       | Certify_Anti_Left => Certify_Left_Left_Absorptive  
       | Certify_Not_Anti_Left (s1, s2) => 
          Certify_Not_Left_Left_Absorptive  ((s1, t1), (s2, t2))
       end
     end 
| Certify_Not_Left_Left_Absorptive (s1, s2) => 
        Certify_Not_Left_Left_Absorptive  ((s1, wT), (s2, wT))
end. 


Definition bops_llex_product_left_right_absorptive_check 
     (dS : @check_left_right_absorptive S)
     (dT : @check_left_right_absorptive T) 
     (alS : @check_anti_right S) : 
       @check_left_right_absorptive (S * T) := 
match dS with 
| Certify_Left_Right_Absorptive => 
     match dT with 
     | Certify_Left_Right_Absorptive => Certify_Left_Right_Absorptive  
     | Certify_Not_Left_Right_Absorptive (t1, t2) => 
       match alS with 
       | Certify_Anti_Right => Certify_Left_Right_Absorptive  
       | Certify_Not_Anti_Right (s1, s2) => 
          Certify_Not_Left_Right_Absorptive  ((s1, t1), (s2, t2))
       end
     end 
| Certify_Not_Left_Right_Absorptive (s1, s2) => 
        Certify_Not_Left_Right_Absorptive  ((s1, wT), (s2, wT))
end. 



Definition bops_llex_product_right_left_absorptive_check 
     (dS : @check_right_left_absorptive S) 
     (dT : @check_right_left_absorptive T)
     (alS : @check_anti_left S) : 
       @check_right_left_absorptive (S * T) := 
match dS with 
| Certify_Right_Left_Absorptive => 
     match dT with 
     | Certify_Right_Left_Absorptive => Certify_Right_Left_Absorptive  
     | Certify_Not_Right_Left_Absorptive (t1, t2) => 
       match alS with 
       | Certify_Anti_Left => Certify_Right_Left_Absorptive  
       | Certify_Not_Anti_Left (s1, s2) => 
          Certify_Not_Right_Left_Absorptive  ((s1, t1), (s2, t2))
       end
     end 
| Certify_Not_Right_Left_Absorptive (s1, s2) => 
        Certify_Not_Right_Left_Absorptive  ((s1, wT), (s2, wT))
end. 


Definition bops_llex_product_right_right_absorptive_check 
     (dS : @check_right_right_absorptive S) 
     (dT : @check_right_right_absorptive T) 
     (alS : @check_anti_right S) : 
       @check_right_right_absorptive (S * T) := 
match dS with 
| Certify_Right_Right_Absorptive => 
     match dT with 
     | Certify_Right_Right_Absorptive => Certify_Right_Right_Absorptive  
     | Certify_Not_Right_Right_Absorptive (t1, t2) => 
       match alS with 
       | Certify_Anti_Right => Certify_Right_Right_Absorptive  
       | Certify_Not_Anti_Right (s1, s2) => 
          Certify_Not_Right_Right_Absorptive  ((s1, t1), (s2, t2))
       end
     end 
| Certify_Not_Right_Right_Absorptive (s1, s2) => 
        Certify_Not_Right_Right_Absorptive  ((s1, wT), (s2, wT))
end. 

End Certify. 

Section Certificates.

Variable S T : Type.
Variable wS : S.
Variable wT : T.    
Variable argT : T.  
Variable rS : brel S.
Variable rT : brel T.   
Variable addS : binary_op S.
Variable mulS : binary_op S. 
Variable addT : binary_op T.
Variable mulT : binary_op T.


Definition id_ann_certs_llex_product
 (pS : @id_ann_certificates S)
 (pT : @id_ann_certificates T) : @id_ann_certificates (S * T) := 
let pS_id_ann_plus_times_d := id_ann_plus_times_d pS in 
let pS_id_ann_times_plus_d := id_ann_times_plus_d pS in 
let pT_id_ann_plus_times_d := id_ann_plus_times_d pT in 
let pT_id_ann_times_plus_d := id_ann_times_plus_d pT in 
{|
  id_ann_plus_times_d := bops_llex_product_exists_id_ann_certify pS_id_ann_plus_times_d pT_id_ann_plus_times_d 
; id_ann_times_plus_d := bops_llex_product_exists_id_ann_certify pS_id_ann_times_plus_d pT_id_ann_times_plus_d
|}.
  
End Certificates.

End CAS.

Section Verify. 
End Verify.   



