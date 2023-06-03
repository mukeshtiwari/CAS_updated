Require Import Coq.Bool.Bool.
Require Import CAS.coq.common.compute.
From Coq Require Import String.

Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures. 
Require Import CAS.coq.eqv.product.

Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures.
Require Import CAS.coq.sg.llex.
Require Import CAS.coq.sg.and. 
Require Import CAS.coq.sg.product.
Require Import CAS.coq.sg.theory.
Require Import CAS.coq.sg.cast_up.

Require Import CAS.coq.ltr.properties.
Require Import CAS.coq.ltr.structures. 
Require Import CAS.coq.ltr.product. 

Require Import CAS.coq.sg_ltr.properties.
Require Import CAS.coq.sg_ltr.structures.
Require Import CAS.coq.sg_ltr.cast.
Require Import CAS.coq.sg_ltr.classify.

From Coq Require Import String List.
Import ListNotations.

Section Theory.

Variable LS : Type.     
Variable S  : Type.
Variable LT : Type. 
Variable T  : Type.

Variable eqLS : brel LS. 
Variable eqLT : brel LT.

Variable eqS : brel S. 
Variable eqT : brel T.

Variable argT : T.  (* for llex product *) 
Variable wS : S. 
Variable wT : T.

Variable wLS : LS. 
Variable wLT : LT.

Variable addS : binary_op S. 
Variable addT : binary_op T.

Variable ltrS : ltr_type LS S.
Variable ltrT : ltr_type LT T. 

Variable conS : brel_congruence S eqS eqS. 
Variable refS : brel_reflexive S eqS.
Variable symS : brel_symmetric S eqS.  
Variable trnS : brel_transitive S eqS.

Variable conT : brel_congruence T eqT eqT. 
Variable refT : brel_reflexive T eqT.
Variable symT : brel_symmetric T eqT.  
Variable trnT : brel_transitive T eqT.

Variable refLS : brel_reflexive LS eqLS.
Variable refLT : brel_reflexive LT eqLT.


Variable a_conS : bop_congruence S eqS addS.
Variable a_conT : bop_congruence T eqT addT.


Variable m_conS : A_ltr_congruence eqLS eqS ltrS.
Variable m_conT : A_ltr_congruence eqLT eqT ltrT.

Variable a_commS : bop_commutative S eqS addS.
Variable a_idemS : bop_idempotent S eqS addS.

Notation "a =S b"  := (eqS a b = true) (at level 15).
Notation "a =T b"  := (eqT a b = true) (at level 15).
Notation "a +S b"  := (addS a b) (at level 15).
Notation "a +T b"  := (addT a b) (at level 15).
Notation "a |S> b"  := (ltrS a b) (at level 15).
Notation "a |T> b"  := (ltrT a b) (at level 15).

Notation "a <*> b" := (brel_product a b) (at level 15).
Notation "a [+] b" := (bop_llex argT eqS a b) (at level 15).
Notation "a [*] b" := (ltr_product_op a b) (at level 15).

(* Note : this is a minor modification of the proof from bs/llex_product.v .... *) 
Lemma sg_ltr_llex_product_distributive
      (selS_or_annT : bop_selective S eqS addS + A_ltr_is_ann eqT ltrT argT)      
      (ldS : A_sg_ltr_distributive eqS addS ltrS)
      (ldT : A_sg_ltr_distributive eqT addT ltrT) 
      (D : ((A_ltr_cancellative eqS ltrS) + (A_ltr_constant eqT ltrT))): 
  A_sg_ltr_distributive (eqS <*> eqT) (addS [+] addT) (ltrS [*] ltrT). 
Proof. intros [s1 t1] [s2 t2] [s3 t3].
       unfold ltr_product, bop_llex, brel_product. 
       apply andb_true_intro. split.  
       apply ldS.
       unfold llex_p2.
       case_eq(eqS s2 (s2 +S s3)); intro H2; 
       case_eq(eqS (s1 |S> s2) ((s1 |S> s2) +S (s1 |S> s3))); intro H4; simpl. 
       - case_eq(eqS (s2 +S s3) s3); intro H1;
         case_eq(eqS ((s1 |S> s2) +S (s1 |S> s3)) (s1 |S> s3)); intro H3. 
         + apply ldT. 
         + assert (F1 := trnS _ _ _ H2 H1).
           assert (F2 := a_idemS (s1 |S> s3)). 
           assert (F3 := m_conS _ _ _ _ (refLS s1) F1). 
           assert (F4 := a_conS _ _ _ _ F3 (refS ((s1 |S> s3)))). 
           assert (F5 := trnS _ _ _ F4 F2).
           rewrite F5 in H3. discriminate H3. 
         + destruct D as [LC | LK].
           * assert (F1 := ldS s1 s2 s3).
             assert (F2 := trnS _ _ _ F1 H3). 
             apply LC in F2. 
             assert (F3 := trnS _ _ _ H2 F2).
             assert (F4 := conS _ _ _ _ (refS (s2 +S s3)) F3). 
             rewrite <- F4 in H1. apply symS in H2.
             rewrite H2 in H1. discriminate H1.
           * assert (F1 := ldT t1 t2 t3).
             assert (F2 := LK t1 t2 (t2 +T t3)). 
             exact (trnT _ _ _ F2 F1). 
         + apply refT. 
       - case_eq(eqS (s2 +S s3) s3); intro H1;
         case_eq(eqS ((s1 |S> s2) +S (s1 |S> s3)) (s1 |S> s3)); intro H3.
         + assert (F1 := trnS _ _ _ H2 H1). 
           assert (F2 := a_idemS (s1 |S> s2)). 
           assert (F3 := m_conS _ _ _ _ (refLS s1) F1). 
           assert (F4 := a_conS _ _ _ _ (refS (s1 |S> s2)) F3). apply symS in F2.
           assert (F5 :=trnS _ _ _ F2 F4). 
           rewrite F5 in H4. discriminate H4.
         + assert (F1 := ldS s1 s2 s3).
           assert (F2 := m_conS _ _ _ _ (refLS s1) H1). apply symS in F1. 
           rewrite (trnS _ _ _ F1 F2) in H3. discriminate H3.            
         + destruct D as [LC | LK].
           * assert (F1 := ldS s1 s2 s3).
             assert (F2 := trnS _ _ _ F1 H3). 
             apply LC in F2. 
             rewrite F2 in H1. discriminate H1.
           * exact(LK t1 t2 t3). 
         + assert (F1 := ldS s1 s2 s3).
           assert (F2 := m_conS _ _ _ _ (refLS s1) H2).
           assert (F3 := trnS _ _ _ F2 F1).            
           rewrite F3 in H4. discriminate H4.
       - case_eq(eqS (s2 +S s3) s3); intro H1;
         case_eq(eqS ((s1 |S> s2) +S (s1 |S> s3)) (s1 |S> s3)); intro H3.
         + destruct D as [LC | LK].
           * assert (F1 := ldS s1 s2 s3). apply symS in F1. 
             assert (F2 := trnS _ _ _ H4 F1). 
             apply LC in F2.
             rewrite F2 in H2. discriminate H2.
           * assert (F1 := ldT t1 t2 t3).
             assert (F2 := LK t1 t3 (t2 +T t3)). 
             exact (trnT _ _ _ F2 F1). 
         + assert (F1 := ldS s1 s2 s3).
           assert (F2 := m_conS _ _ _ _ (refLS s1) H1). apply symS in F1. 
           assert (F3 := trnS _ _ _ F1 F2).            
           rewrite F3 in H3. discriminate H3.
         + destruct D as [LC | LK].
           * assert (F1 := ldS s1 s2 s3). apply symS in F1. 
             assert (F2 := trnS _ _ _ H4 F1). 
             apply LC in F2.
             rewrite F2 in H2. discriminate H2.
           * assert (F1 := ldT t1 t2 t3).
             assert (F2 := LK t1 argT (t2 +T t3)). 
             exact (trnT _ _ _ F2 F1).              
         + destruct D as [LC | LK].
           * assert (F1 := ldS s1 s2 s3). apply symS in F1. 
             assert (F2 := trnS _ _ _ H4 F1). 
             apply LC in F2.
             rewrite F2 in H2. discriminate H2.
           * exact (LK t1 argT t2). 
       - case_eq(eqS (s2 +S s3) s3); intro H1;
         case_eq(eqS ((s1 |S> s2) +S (s1 |S> s3)) (s1 |S> s3)); intro H3.
         + apply refT. 
         + assert (F1 := ldS s1 s2 s3).
           assert (F2 := m_conS _ _ _ _ (refLS s1) H1). apply symS in F2. 
           assert (F3 := trnS _ _ _ F2 F1). apply symS in F3.
           rewrite F3 in H3. discriminate H3.
         + destruct D as [LC | LK].
           * assert (F1 := ldS s1 s2 s3).
             assert (F2 := trnS _ _ _ F1 H3). 
             apply LC in F2.
             rewrite F2 in H1. discriminate H1.
           * exact (LK t1 argT t3). 
         + destruct selS_or_annT as [selS | argT_is_annT].
           * destruct (selS s2 s3) as [F1 | F1].
             -- apply symS in F1. rewrite F1 in H2. discriminate H2.
             -- rewrite F1 in H1. discriminate H1. 
           * exact (argT_is_annT t1). 
Qed. 


Lemma sg_ltr_llex_product_not_distributive_v1 
  (ND : A_sg_ltr_not_distributive eqS addS ltrS) :
  A_sg_ltr_not_distributive (eqS <*> eqT) (addS [+] addT) (ltrS [*] ltrT). 
Proof. destruct ND as [ [s1 [s2 s3 ] ] nld ].
       exists ((s1, wLT), ((s2, wT), (s3, wT))); simpl.
       rewrite nld; simpl.
       reflexivity.
Defined. 

Lemma sg_ltr_llex_product_not_distributive_v2
  (dS : A_sg_ltr_distributive eqS addS ltrS)
  (ndT : A_sg_ltr_not_distributive eqT addT ltrT) :
  A_sg_ltr_not_distributive  (eqS <*> eqT) (addS [+] addT) (ltrS [*] ltrT).
Proof. destruct ndT as [ [t1 [t2 t3 ] ] nld ].
       exists ((wLS, t1), ((wS, t2), (wS, t3))); simpl.        
       unfold brel_product, llex_p2.
       apply bop_and_false_intro. right. 
       assert (F1 := a_idemS wS). rewrite F1. apply symS in F1. rewrite F1. 
       assert (A : eqS (wLS |S> wS) ((wLS |S> wS) +S (wLS |S> wS)) = true). 
          assert (B := dS wLS wS wS). 
          assert (C := m_conS _ _ _ _ (refLS wLS) F1).
          exact (trnS _ _ _ C B).
       rewrite A. apply symS in A. rewrite A. 
       exact nld. 
Defined.

(* see cases 1-4 in the proof below *) 

Definition A_witness_sg_ltr_llex_product_not_distributive
      (selS_or_id_annT : bop_selective S eqS addS + (bop_is_id T eqT addT argT * A_ltr_is_ann eqT ltrT argT))
      (s1 : LS) (s2 s3 : S)
      (t1 : LT) (t2 t3 : T)
:= if (eqS (s2 +S s3) s2) 
   then if eqS (s2 +S s3) s3
        then (* can't reach this branch *) 
             ((s1, t1), ((s2, t2), (s3, t3)))
        else  if eqS (s1 |S> s2) ((s1 |S> s2) +S (s1 |S> s3))
              then (* case 1 *) 
                   if eqT (t1 |T> t2) ((t1 |T> t2) +T (t1 |T> t3))
                   then ((s1, t1), ((s2, t3), (s3, t2)))
                   else ((s1, t1), ((s2, t2), (s3, t3)))
              else (* case 2 *) 
                   ((s1, t1), ((s2, t2), (s3, t3)))
   else if eqS (s2 +S s3) s3
        then (* case 3 *) 
             if eqT (t1 |T> t3) ((t1 |T> t2) +T (t1 |T> t3))
             then ((s1, t1), ((s2, t3), (s3, t2)))
             else ((s1, t1), ((s2, t2), (s3, t3)))
        else (* case 4 *) 
             match selS_or_id_annT with 
             | inl _ => (* can't reach this branch *) 
                       ((s1, t1), ((s2, t2), (s3, t3)))
             | inr _ => if eqT argT (t1 |T> t2)
                        then ((s1, t1), ((s2, argT), (s3, t3)))
                        else ((s1, t1), ((s2, argT), (s3, t2)))
             end.   


Lemma sg_ltr_llex_product_not_distributive_v3
      (a_commT : bop_commutative T eqT addT) (*NB*)
      (selS_or_id_annT : bop_selective S eqS addS + (bop_is_id T eqT addT argT * A_ltr_is_ann eqT ltrT argT))
      (ldS : A_sg_ltr_distributive eqS addS ltrS)
      (ldT : A_sg_ltr_distributive eqT addT ltrT) : 
      A_ltr_not_cancellative eqS ltrS →
      A_ltr_not_constant eqT ltrT → 
         A_sg_ltr_not_distributive (eqS <*> eqT) (addS [+] addT) (ltrS [*] ltrT).
Proof. intros [ [s1 [s2 s3 ] ] [E N] ] [ [t1 [ t2 t3 ]] F].
       (* to understand the cases below, assume we have done this: 
          
           exists ((s1, a), ((s2, b), (s3, c))).

          In each of the four cases pick a, b, and c to make that case work. 
        *)
       exists(A_witness_sg_ltr_llex_product_not_distributive selS_or_id_annT s1 s2 s3 t1 t2 t3). 
       unfold A_witness_sg_ltr_llex_product_not_distributive. 
       unfold ltr_product, brel_product, bop_llex.        
       case_eq(eqS s2 (s2 +S s3)); intro H2; 
       case_eq(eqS (s1 |S> s2) ((s1 |S> s2) +S (s1 |S> s3))); intro H4; simpl. 
       - case_eq(eqS (s2 +S s3) s3); intro H1; case_eq(eqS ((s1 |S> s2) +S (s1 |S> s3)) (s1 |S> s3)); intro H3. 
         + rewrite (trnS _ _ _ H2 H1) in N. discriminate N. 
         + assert (F1 := trnS _ _ _ H2 H1).
           assert (F2 := a_idemS (s1 |S> s3)). 
           assert (F3 := m_conS _ _ _ _ (refLS s1) F1). 
           assert (F4 := a_conS _ _ _ _ F3 (refS ((s1 |S> s3)))). 
           assert (F5 := trnS _ _ _ F4 F2).
           rewrite F5 in H3. discriminate H3. 
         + (* ============= case 1 ======================
              E : (s1 |S> s2) =S (s1 |S> s3)
              N : rS s2 s3 = false
              F : rT (t1 |T> t2) (t1 |T> t3) = false

             H2 : s2 =S (s2 +S s3)
             H4 : (s1 |S> s2) =S ((s1 |S> s2) +S (s1 |S> s3))
             H1 : rS (s2 +S s3) s3 = false
             H3 : ((s1 |S> s2) +S (s1 |S> s3)) =S (s1 |S> s3)
             ===========need=================
             rT (a *T b) ((a *T b) +T (a *T c)) = false

             if rT (t1 *T t2) ((t1 *T t2) +T (t1 *T t3))
             then (t1 *T t3) ((t1 *T t2) +T (t1 *T t3)) = false
                   a     b     a     c       a     b    (use a_commT  !!!) 

             else (t1 *T t2) ((t1 *T t2) +T (t1 *T t3)) = false
                   a      b     a     b      a     c 
           *) 
           unfold llex_p2. rewrite (symS _ _ H2).
           case_eq(eqT (t1 |T> t2) ((t1 |T> t2) +T (t1 |T> t3))); intro F1.
           * apply bop_and_false_intro. right.
             rewrite H2. rewrite H1. rewrite H4. rewrite H3.            
               case_eq(eqT (t1 |T> t3) ((t1 |T> t3) +T (t1 |T> t2))); intro F2; auto.              
             -- assert (F3 := a_commT (t1 |T> t3) (t1 |T> t2)). 
                assert (F4 := trnT _ _ _ F2 F3). apply symT in F4. 
                rewrite (trnT _ _ _ F1 F4) in F. discriminate F. 
           * apply bop_and_false_intro. right.
             rewrite H2. rewrite H1. rewrite H4. rewrite H3.            
             exact F1.            
         + apply symS in E.
           assert (F1 := trnS _ _ _ E H4). apply symS in F1. 
           rewrite F1 in H3. discriminate H3. 
       - case_eq(eqS (s2 +S s3) s3); intro H1; case_eq(eqS ((s1 |S> s2) +S (s1 |S> s3)) (s1 |S> s3)); intro H3. 
         + assert (F1 := trnS _ _ _ H2 H1). 
           assert (F2 := a_idemS (s1 |S> s2)). 
           assert (F3 := m_conS _ _ _ _ (refLS s1) F1). 
           assert (F4 := a_conS _ _ _ _ (refS (s1 |S> s2)) F3). apply symS in F2.
           assert (F5 := trnS _ _ _ F2 F4). 
           rewrite F5 in H4. discriminate H4.
         + assert (F1 := ldS s1 s2 s3).
           assert (F2 := m_conS _ _ _ _ (refLS s1) H1). apply symS in F1. 
           rewrite (trnS _ _ _ F1 F2) in H3. discriminate H3.            
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
           assert (F2 := m_conS _ _ _ _ (refLS s1) H2).
           assert (F3 := trnS _ _ _ F2 F1).            
           rewrite F3 in H4. discriminate H4.
       - case_eq(eqS (s2 +S s3) s3); intro H1; case_eq(eqS ((s1 |S> s2) +S (s1 |S> s3)) (s1 |S> s3)); intro H3. 
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
                   a     c     a     c       a     b    (use a_commT !!!) 

             else (t1 *T t3) ((t1 *T t2) +T (t1 *T t3)) = false
                   a     c      a     b       a     c 

           *) 
           assert (G : eqS (s2 +S s3) s2 = false).
              case_eq(eqS (s2 +S s3) s2); intro H; auto.
                apply symS in H. rewrite H in H2. discriminate H2.            
           unfold llex_p2. rewrite G. 
           case_eq(eqT (t1 |T> t3) ((t1 |T> t2) +T (t1 |T> t3))); intro F1.
           * apply bop_and_false_intro. right.
             rewrite H2. rewrite H1. rewrite H4. rewrite H3.            
               case_eq(eqT (t1 |T> t2) ((t1 |T> t3) +T (t1 |T> t2))); intro F2; auto.              
             -- assert (F3 := a_commT (t1 |T> t3) (t1 |T> t2)). 
                assert (F4 := trnT _ _ _ F2 F3). apply symT in F1. 
                rewrite (trnT _ _ _ F4 F1) in F. discriminate F. 
           * apply bop_and_false_intro. right.
             rewrite H2. rewrite H1. rewrite H4. rewrite H3.            
             exact F1.            
         + assert (F1 := ldS s1 s2 s3).
           assert (F2 := m_conS _ _ _ _ (refLS s1) H1). apply symS in F1. 
           assert (F3 := trnS _ _ _ F1 F2).            
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
           * assert (G : eqS (s2 +S s3) s2 = false).
             case_eq(eqS (s2 +S s3) s2); intro H; auto.
             apply symS in H. rewrite H in H2. discriminate H2.
             unfold llex_p2. rewrite G.
             case_eq(eqT argT (t1 |T> t2)); intro F6.
             -- apply bop_and_false_intro. right.
                rewrite H1, H2, H3, H4. 
                assert (F2 := annT t1).
                destruct (idT (t1 |T> t3)) as [F3 F4].                          
                assert (F5 : ((t1 |T> argT) +T (t1 |T> t3)) =T (t1 |T> t3)).
                   assert (F5 := a_conT _ _ _ _ F2 (refT (t1 |T> t3))). 
                   exact (trnT _ _ _ F5 F3). 
                case_eq(eqT (t1 |T> argT) ((t1 |T> argT) +T (t1 |T> t3))); intro F7; auto.
                ++ assert (F8 := trnT _ _ _ F7 F5).
                   assert (F9 := trnT _ _ _ F2 F6). apply symT in F9. 
                   rewrite (trnT _ _ _ F9 F8) in F. discriminate F. 
             -- apply bop_and_false_intro. right.
                rewrite H1, H2, H3, H4.
                assert (F2 := annT t1).
                destruct (idT (t1 |T> t2)) as [F3 F4].                                          
                assert (F5 : ((t1 |T> argT) +T (t1 |T> t2)) =T (t1 |T> t2)).
                   assert (F5 := a_conT _ _ _ _ F2 (refT (t1 |T> t2))). 
                   exact (trnT _ _ _ F5 F3). 
                case_eq(eqT (t1 |T> argT) ((t1 |T> argT) +T (t1 |T> t2))); intro F7; auto.
                ++ assert (F8 := trnT _ _ _ F7 F5). apply symT in F2. 
                   rewrite (trnT _ _ _ F2 F8) in F6. discriminate F6. 
         + apply symS in E. assert (F1 := trnS _ _ _ E H4). 
           apply symS in F1. rewrite F1 in H3. discriminate H3. 
       - case_eq(eqS (s2 +S s3) s3); intro H1; case_eq(eqS ((s1 |S> s2) +S (s1 |S> s3)) (s1 |S> s3)); intro H3. 
         + apply symS in E. assert (F1 := trnS _ _ _ H3 E). 
           apply symS in F1. rewrite F1 in H4. discriminate H4. 
         + assert (F1 := ldS s1 s2 s3).
           assert (F2 := m_conS _ _ _ _ (refLS s1) H1). apply symS in F2. 
           assert (F3 := trnS _ _ _ F2 F1). apply symS in F3.
           rewrite F3 in H3. discriminate H3.
         + apply symS in E. assert (F1 := trnS _ _ _ H3 E). 
           apply symS in F1. rewrite F1 in H4. discriminate H4. 
         + assert (F1 := a_idemS (s1 |S> s3)). 
           assert (F2 := a_conS _ _ _ _ E (refS (s1 |S> s3))). 
           assert (F3 := trnS _ _ _ F2 F1).
           rewrite F3 in H3. discriminate H3. 
Defined.



(* Absorption *)

(* compare to bs/llex_product.v 

   Here we have 
   absortive(S llex T) 
   <-> (strictly_absorptive S) + (absorptive(S) * absorptive(T))

   In bs we have 
   absortive(S llex T) 
   <-> (absorptive(S) * (absorptive(T) + anti_left(mulS)) 
   <-> (absorptive(S) * anti_left(mulS)) + (absorptive(S) * absorptive(T))
   where anti_left(mulS) = ∀ s t : S, eqS s (mulS s t) = false

 sg_ltr_strictly_absorptive: 
  ∀ (l : L) (s : S),
    (eqS s (add s (ltr l s)) = true) * (eqS (ltr l s) (add s (ltr l s)) = false)

  absorptive(S) * anti_left(mulS): 
  (∀ (l : L) (s : S), 
      eqS s (add s (ltr l s)) = true) * (∀ s t : S, eqS s (mulS s t) = false)
 *)

Lemma sg_ltr_llex_product_absorptive : 
      (A_sg_ltr_strictly_absorptive eqS addS ltrS) +  
      ((A_sg_ltr_absorptive eqS addS ltrS) * (A_sg_ltr_absorptive eqT addT ltrT)) → 
         A_sg_ltr_absorptive (eqS <*> eqT) (addS [+] addT) (ltrS [*] ltrT).
Proof. intros [sabsS | [absS absT]].
       + intros [lS lT] [s t].
         destruct (sabsS lS s) as [A B]. compute. 
         rewrite A.
         case_eq(eqS (s +S (lS |S> s)) (lS |S> s)); intro C.
         ++ apply symS in C. rewrite C in B. discriminate B. 
         ++ apply refT. 
       + intros [lS lT] [s t].
         assert (A := absS lS s).
         assert (B := absT lT t). compute.          
         rewrite A.
         case_eq(eqS (s +S (lS |S> s)) (lS |S> s)); intro D.
         ++ exact B. 
         ++ apply refT. 
Qed. 

Lemma sg_ltr_llex_product_not_absorptive_left : 
      A_sg_ltr_not_absorptive eqS addS ltrS → 
         A_sg_ltr_not_absorptive (eqS <*> eqT) (addS [+] addT) (ltrS [*] ltrT). 
Proof. intros [ [s1 s2] P ]. exists ((s1, wLT), (s2, wT)). simpl. rewrite P. simpl. reflexivity. Defined. 


Lemma sg_ltr_llex_product_not_absorptive_right : 
      (A_sg_ltr_not_strictly_absorptive eqS addS ltrS) *  
      ((A_sg_ltr_absorptive eqS addS ltrS) * (A_sg_ltr_not_absorptive eqT addT ltrT)) → 
         A_sg_ltr_not_absorptive (eqS <*> eqT) (addS [+] addT) (ltrS [*] ltrT).
Proof. intros [[[lS s] A] [absS [[lT t] B]]]; compute.
       assert (C := absS lS s).
       exists ((lS, lT), (s, t)). rewrite C.
       destruct A as [A | A]. 
       + rewrite A in C. discriminate C. 
       + assert (D : eqS (s +S (lS |S> s)) (lS |S> s) = true).
            apply symS in C.
            assert (H := trnS _ _ _ A C). 
            assert (E := a_idemS (lS |S> s)).
            apply symS in H. 
            exact (trnS _ _ _ C H). 
        rewrite D.
         exact B. 
Defined.



Lemma sg_ltr_llex_product_strictly_absorptive : 
      (A_sg_ltr_strictly_absorptive eqS addS ltrS) +  
      ((A_sg_ltr_absorptive eqS addS ltrS) * (A_sg_ltr_strictly_absorptive eqT addT ltrT)) → 
         A_sg_ltr_strictly_absorptive (eqS <*> eqT) (addS [+] addT) (ltrS [*] ltrT).
Proof. intros [sabsS | [absS sabsT]].
       + intros [lS lT] [s t].
         destruct (sabsS lS s) as [A B]. split; compute. 
         ++ rewrite A.
            case_eq(eqS (s +S (lS |S> s)) (lS |S> s)); intro C.
            +++ apply symS in C. rewrite C in B. discriminate B. 
            +++ apply refT. 
         ++ rewrite A. rewrite B. reflexivity.
       + intros [lS lT] [s t].
         assert (A := absS lS s).
         destruct (sabsT lT t) as [B C]. split; compute.          
         ++ rewrite A.
            case_eq(eqS (s +S (lS |S> s)) (lS |S> s)); intro D.
            +++ exact B. 
            +++ apply refT. 
         ++ rewrite A.
            case_eq(eqS (s +S (lS |S> s)) (lS |S> s)); intro D.
            +++ apply symS in D. rewrite D. exact C.
            +++ case_eq(eqS (lS |S> s) (s +S (lS |S> s))); intro E. 
                ++++ apply symS in E. rewrite E in D. discriminate D. 
                ++++ reflexivity. 
Qed.


Lemma sg_ltr_llex_product_not_strictly_absorptive_left : 
      A_sg_ltr_not_absorptive eqS addS ltrS → 
         A_sg_ltr_not_strictly_absorptive (eqS <*> eqT) (addS [+] addT) (ltrS [*] ltrT). 
Proof. intros [ [s1 s2] P ]. exists ((s1, wLT), (s2, wT)). simpl. rewrite P. simpl. left. reflexivity. Defined. 


Lemma sg_ltr_llex_product_not_strictly_absorptive_right : 
      (A_sg_ltr_not_strictly_absorptive eqS addS ltrS) *  
      ((A_sg_ltr_absorptive eqS addS ltrS) * (A_sg_ltr_not_strictly_absorptive eqT addT ltrT)) → 
         A_sg_ltr_not_strictly_absorptive (eqS <*> eqT) (addS [+] addT) (ltrS [*] ltrT).
Proof. intros [[[lS s] A] [absS [[lT t] B]]]; compute.
       assert (C := absS lS s).
       exists ((lS, lT), (s, t)). rewrite C.
       destruct A as [A | A]. 
       + rewrite A in C. discriminate C.          
       + rewrite A. 
        destruct B as [B | B].
         ++ left. apply symS in A. rewrite A. exact B. 
         ++ rewrite (symS _ _ A). right. exact B.
Defined.


Lemma A_sg_ltr_llex_product_exists_id_ann_equal : 
      A_sg_ltr_exists_id_ann_equal eqS addS ltrS → 
      A_sg_ltr_exists_id_ann_equal eqT addT ltrT → 
      A_sg_ltr_exists_id_ann_equal (eqS <*> eqT) (addS [+] addT) (ltrS [*] ltrT). 
Proof. intros [iS [piS paS]]  [iT [piT paT]].
       exists (iS, iT). split.
       - apply bop_llex_is_id; auto.
       - apply ltr_product_is_ann; auto. 
Defined.

Lemma A_sg_ltr_llex_product_exists_id_ann_not_equal_v1 : 
      A_sg_ltr_exists_id_ann_not_equal eqS addS ltrS →  
      A_sg_ltr_exists_id_ann_equal eqT addT ltrT → 
      A_sg_ltr_exists_id_ann_not_equal (eqS <*> eqT) (addS [+] addT) (ltrS [*] ltrT). 
Proof. intros [[iS aS] [[piS paS] iS_not_aS]]  [iT [piT paT]].
       exists ((iS, iT), (aS, iT)). split.
       - split.
         + apply bop_llex_is_id; auto.
         + apply ltr_product_is_ann; auto. 
       - compute. rewrite iS_not_aS. reflexivity. 
Defined. 

Lemma A_sg_ltr_llex_product_exists_id_ann_not_equal_v2: 
      A_sg_ltr_exists_id_ann_equal eqS addS ltrS →   
      A_sg_ltr_exists_id_ann_not_equal eqT addT ltrT → 
      A_sg_ltr_exists_id_ann_not_equal (eqS <*> eqT) (addS [+] addT) (ltrS [*] ltrT). 
Proof. intros [iS [piS paS]]  [[iT aT] [[piT paT] iT_not_aT]].
       exists ((iS, iT), (iS, aT)). split.
       - split.
         + apply bop_llex_is_id; auto.
         + apply ltr_product_is_ann; auto.
       - compute. rewrite iT_not_aT.
         rewrite (refS iS). reflexivity. 
Defined.

Lemma A_sg_ltr_llex_product_exists_id_ann_not_equal_v3 : 
      A_sg_ltr_exists_id_ann_not_equal eqS addS ltrS →   
      A_sg_ltr_exists_id_ann_not_equal eqT addT ltrT → 
      A_sg_ltr_exists_id_ann_not_equal (eqS <*> eqT) (addS [+] addT) (ltrS [*] ltrT). 
Proof. intros [[iS aS] [[piS paS] iS_not_aS]]  [[iT aT] [[piT paT] iT_not_aT]].
       exists ((iS, iT), (aS, aT)). split.
       - split.
         + apply bop_llex_is_id; auto.
         + apply ltr_product_is_ann; auto. 
       - compute. rewrite iS_not_aS. reflexivity. 
Defined. 

End Theory. 

Section ACAS.


Section Decide.

Variables (LS S LT T : Type)  
          (eqLS : brel LS)
          (eqLT : brel LT)
          (eqS : brel S)
          (eqT : brel T)
          (conS : brel_congruence _ eqS eqS)
          (refS : brel_reflexive _ eqS)
          (symS : brel_symmetric _ eqS)
          (trnS : brel_transitive _ eqS)
          (conT : brel_congruence _ eqT eqT)          
          (refT : brel_reflexive _ eqT)
          (symT : brel_symmetric _ eqT)
          (trnT : brel_transitive _ eqT)          
          (argT : T)
          (wLS : LS)
          (wLT : LT)                     
          (wS : S)
          (wT : T)           
          (eqvLS : eqv_proofs LS eqLS)
          (eqvLT : eqv_proofs LT eqLT)                     
          (eqvS : eqv_proofs S eqS)
          (eqvT : eqv_proofs T eqT)           
          (addS : binary_op S) 
          (addT : binary_op T)
          (idemS : bop_idempotent S eqS addS)
          (commS : bop_commutative S eqS addS)
          (commT : bop_commutative T eqT addT)                     
          (ltrS : ltr_type LS S)
          (ltrT : ltr_type LT T)
          (a_congS : bop_congruence S eqS addS)
          (a_congT : bop_congruence T eqT addT)
          (ltr_congS : A_ltr_congruence eqLS eqS ltrS).                     

Definition A_sg_ltr_llex_product_distributive_decide
           (a_commT : bop_commutative T eqT addT) 
           (selS_or_id_annT : 
              bop_selective S eqS addS + 
              (bop_is_id T eqT addT argT * A_ltr_is_ann eqT ltrT argT))
           (LDS_d : A_sg_ltr_distributive_decidable eqS addS ltrS)
           (LDT_d : A_sg_ltr_distributive_decidable eqT addT ltrT)
           (LCS_d : A_ltr_cancellative_decidable eqS ltrS)
           (LKT_d : A_ltr_constant_decidable eqT ltrT): 
  A_sg_ltr_distributive_decidable
             (brel_product eqS eqT)
             (bop_llex argT eqS addS addT)
             (ltr_product_op ltrS ltrT) :=
let congS := A_eqv_congruence _ _ eqvS in   
let refS := A_eqv_reflexive _ _ eqvS in 
let symS := A_eqv_symmetric _ _ eqvS in
let trnS := A_eqv_transitive _ _ eqvS in
let refT := A_eqv_reflexive _ _ eqvT in 
let symT := A_eqv_symmetric _ _ eqvT in
let trnT := A_eqv_transitive _ _ eqvT in
let refLS := A_eqv_reflexive _ _ eqvLS in
let selS_or_annT :=
    match selS_or_id_annT with
    | inl sel         => inl sel
    | inr (_, is_ann) => inr is_ann 
    end
in       
match LDS_d with
| inl LDS  =>
  match LDT_d with
  | inl LDT  =>
      match LCS_d with
      | inl LCS  =>
          inl (sg_ltr_llex_product_distributive LS S LT T eqLS eqS eqT argT addS addT ltrS ltrT congS refS symS trnS refT trnT refLS a_congS ltr_congS idemS selS_or_annT LDS LDT (inl LCS))
    | inr nLCS =>
      match LKT_d with
      | inl LKT  => inl (sg_ltr_llex_product_distributive LS S LT T eqLS eqS eqT argT addS addT ltrS ltrT congS refS symS trnS refT trnT refLS a_congS ltr_congS idemS selS_or_annT LDS LDT (inr LKT))
      | inr nLKT => inr (sg_ltr_llex_product_not_distributive_v3 LS S LT T eqLS eqS eqT argT addS addT ltrS ltrT refS symS trnS refT symT trnT refLS a_congS a_congT ltr_congS idemS commT selS_or_id_annT LDS LDT nLCS nLKT) 
      end 
    end 
  | inr nLDT => inr (@sg_ltr_llex_product_not_distributive_v2 LS S LT T eqLS eqS eqT argT wS wLS addS addT ltrS ltrT symS trnS refLS ltr_congS idemS LDS nLDT)    
  end 
| inr nLDS => inr (@sg_ltr_llex_product_not_distributive_v1 LS S LT T eqS eqT argT wT wLT addS addT ltrS ltrT nLDS) 
end.     


Definition A_sg_ltr_llex_product_absorptive_decide
           (sabsS_d : A_sg_ltr_strictly_absorptive_decidable eqS addS ltrS)
           (absS_d : A_sg_ltr_absorptive_decidable eqS addS ltrS)
           (absT_d : A_sg_ltr_absorptive_decidable eqT addT ltrT) :
  A_sg_ltr_absorptive_decidable
             (brel_product eqS eqT)
             (bop_llex argT eqS addS addT)
             (ltr_product_op ltrS ltrT) :=
let refS := A_eqv_reflexive _ _ eqvS in 
let symS := A_eqv_symmetric _ _ eqvS in
let trnS := A_eqv_transitive _ _ eqvS in
let refT := A_eqv_reflexive _ _ eqvT in 
match sabsS_d with
| inl sabsS  => inl(sg_ltr_llex_product_absorptive LS S LT T eqS eqT argT addS addT ltrS ltrT symS refT (inl sabsS))
| inr nsabsS =>
  match absS_d with
  | inl absS  =>
    match absT_d with
    | inl absT  => inl(sg_ltr_llex_product_absorptive LS S LT T eqS eqT argT addS addT ltrS ltrT symS refT (inr (absS, absT)))
    | inr nabsT => inr(sg_ltr_llex_product_not_absorptive_right LS S LT T eqS eqT argT addS addT ltrS ltrT symS trnS idemS (nsabsS, (absS, nabsT)))
    end 
  | inr nabsS => inr (sg_ltr_llex_product_not_absorptive_left LS S LT T eqS eqT argT wT wLT addS addT ltrS ltrT nabsS)
  end
end.     

Definition A_sg_ltr_llex_product_strictly_absorptive_decide
           (sabsS_d : A_sg_ltr_strictly_absorptive_decidable eqS addS ltrS)
           (absS_d : A_sg_ltr_absorptive_decidable eqS addS ltrS)
           (absT_d : A_sg_ltr_strictly_absorptive_decidable eqT addT ltrT) :
  A_sg_ltr_strictly_absorptive_decidable
             (brel_product eqS eqT)
             (bop_llex argT eqS addS addT)
             (ltr_product_op ltrS ltrT) :=    
let refS := A_eqv_reflexive _ _ eqvS in 
let symS := A_eqv_symmetric _ _ eqvS in
let trnS := A_eqv_transitive _ _ eqvS in
let refT := A_eqv_reflexive _ _ eqvT in  
match sabsS_d with
| inl sabsS  => inl(sg_ltr_llex_product_strictly_absorptive LS S LT T eqS eqT argT addS addT ltrS ltrT symS refT (inl sabsS))
| inr nsabsS =>
  match absS_d with
  | inl absS  =>
    match absT_d with
    | inl absT  => inl(sg_ltr_llex_product_strictly_absorptive LS S LT T eqS eqT argT addS addT ltrS ltrT symS refT (inr (absS, absT)))
    | inr nabsT => inr(sg_ltr_llex_product_not_strictly_absorptive_right LS S LT T eqS eqT argT addS addT ltrS ltrT symS (nsabsS, (absS, nabsT)))
    end 
  | inr nabsS => inr (sg_ltr_llex_product_not_strictly_absorptive_left LS S LT T eqS eqT argT wT wLT addS addT ltrS ltrT nabsS)
  end
end.



Definition A_sg_ltr_llex_product_proofs_exists_id_ann_decidable 
    (idaS_d : A_sg_ltr_exists_id_ann_decidable eqS addS ltrS)
    (idaT_d : A_sg_ltr_exists_id_ann_decidable eqT addT ltrT) : 
    A_sg_ltr_exists_id_ann_decidable
      (brel_product eqS eqT)
      (bop_llex argT eqS addS addT) 
      (ltr_product_op ltrS ltrT) :=
  let idST idS idT   := bop_llex_exists_id S T eqS eqT addS addT symS argT refT idS idT in 
  let nidST_l nidS   := bop_llex_not_exists_id_left S T eqS eqT addS addT argT nidS in
  let nidST_r nidT   := bop_llex_not_exists_id_right S T eqS eqT addS addT symS argT nidT in
  let annST annS annT := ltr_product_exists_ann LS S LT T eqS ltrS eqT ltrT annS annT in  
  let nannST_l nannS := ltr_product_not_exists_ann_left LS S LT T eqS ltrS eqT wLT ltrT nannS in
  let nannST_r nannT := ltr_product_not_exists_ann_right LS S LT T eqS wLS ltrS eqT ltrT nannT in
  let extract_idS1 id_ann_eqS := A_extract_exist_id_from_sg_ltr_exists_id_ann_equal eqS addS ltrS id_ann_eqS in
  let extract_idS2 id_ann_not_eqS := A_extract_exist_id_from_sg_ltr_exists_id_ann_not_equal eqS addS ltrS id_ann_not_eqS in                             
  let extract_idT1 id_ann_eqT := A_extract_exist_id_from_sg_ltr_exists_id_ann_equal eqT addT ltrT id_ann_eqT in
  let extract_idT2 id_ann_not_eqT := A_extract_exist_id_from_sg_ltr_exists_id_ann_not_equal eqT addT ltrT id_ann_not_eqT in
  let extract_annS1 id_ann_eqS := A_extract_exist_ann_from_sg_ltr_exists_id_ann_equal eqS addS ltrS id_ann_eqS in
  let extract_annS2 id_ann_not_eqS := A_extract_exist_ann_from_sg_ltr_exists_id_ann_not_equal eqS addS ltrS id_ann_not_eqS in                             
  let extract_annT1 id_ann_eqT := A_extract_exist_ann_from_sg_ltr_exists_id_ann_equal eqT addT ltrT id_ann_eqT in
  let extract_annT2 id_ann_not_eqT := A_extract_exist_ann_from_sg_ltr_exists_id_ann_not_equal eqT addT ltrT id_ann_not_eqT in                           
  match idaS_d with
  | A_SG_LTR_Id_Ann_None _ _ _ (nidS, nannS) =>
      A_SG_LTR_Id_Ann_None _ _ _ (nidST_l nidS, nannST_l nannS)      
  | A_SG_LTR_Id_Ann_Id_None _ _ _ (idS, nannS) =>
       match idaT_d with 
       | A_SG_LTR_Id_Ann_None _ _ _ (nidT, nannT) =>
           A_SG_LTR_Id_Ann_None _ _ _ (nidST_r nidT, nannST_l nannS)      
       | A_SG_LTR_Id_Ann_Id_None _ _ _ (idT, nannT) =>
           A_SG_LTR_Id_Ann_Id_None _ _ _ (idST idS idT, nannST_l nannS)      
       | A_SG_LTR_Id_Ann_None_Ann _ _ _ (nidT, annT) =>
           A_SG_LTR_Id_Ann_None _ _ _ (nidST_r nidT, nannST_l nannS)      
       | A_SG_LTR_Id_Ann_Equal _ _ _ id_ann_eqT =>
           A_SG_LTR_Id_Ann_Id_None _ _ _ (idST idS (extract_idT1 id_ann_eqT),  nannST_l nannS)
       | A_SG_LTR_Id_Ann_Not_Equal _ _ _ id_ann_not_eqT =>
           A_SG_LTR_Id_Ann_Id_None _ _ _ (idST idS (extract_idT2 id_ann_not_eqT),  nannST_l nannS)
       end       
  | A_SG_LTR_Id_Ann_None_Ann _ _ _ (nidS, annS) =>
       match idaT_d with 
       | A_SG_LTR_Id_Ann_None _ _ _ (nidT, nannT) =>
           A_SG_LTR_Id_Ann_None _ _ _ (nidST_l nidS, nannST_r nannT)
       | A_SG_LTR_Id_Ann_Id_None _ _ _ (idT, nannT) => 
           A_SG_LTR_Id_Ann_None _ _ _ (nidST_l nidS, nannST_r nannT)
       | A_SG_LTR_Id_Ann_None_Ann _ _ _ (nidT, annT) =>
           A_SG_LTR_Id_Ann_None_Ann _ _ _ (nidST_l nidS, annST annS annT) 
       | A_SG_LTR_Id_Ann_Equal _ _ _ id_ann_eqT =>
           A_SG_LTR_Id_Ann_None_Ann _ _ _ (nidST_l nidS, annST annS (extract_annT1 id_ann_eqT)) 
       | A_SG_LTR_Id_Ann_Not_Equal _ _ _ id_ann_not_eqT =>
           A_SG_LTR_Id_Ann_None_Ann _ _ _ (nidST_l nidS, annST annS (extract_annT2 id_ann_not_eqT)) 
       end      
  | A_SG_LTR_Id_Ann_Equal _ _ _ id_ann_eqS =>
       match idaT_d with 
       | A_SG_LTR_Id_Ann_None _ _ _ (nidT, nannT) =>
           A_SG_LTR_Id_Ann_None _ _ _ (nidST_r nidT, nannST_r nannT)           
       | A_SG_LTR_Id_Ann_Id_None _ _ _ (idT, nannT) =>
           A_SG_LTR_Id_Ann_Id_None _ _ _ (idST (extract_idS1 id_ann_eqS) idT, nannST_r nannT)                      
       | A_SG_LTR_Id_Ann_None_Ann _ _ _ (nidT, annT) =>
           A_SG_LTR_Id_Ann_None_Ann _ _ _ (nidST_r nidT, annST (extract_annS1 id_ann_eqS) annT)                      
       | A_SG_LTR_Id_Ann_Equal _ _ _ id_ann_eqT =>
           A_SG_LTR_Id_Ann_Equal _ _ _ (@A_sg_ltr_llex_product_exists_id_ann_equal LS S LT T eqS eqT argT addS addT ltrS ltrT symS refT id_ann_eqS id_ann_eqT)
       | A_SG_LTR_Id_Ann_Not_Equal _ _ _ id_ann_not_eqT =>
           A_SG_LTR_Id_Ann_Not_Equal _ _ _ (@A_sg_ltr_llex_product_exists_id_ann_not_equal_v2 LS S LT T eqS eqT argT addS addT ltrS ltrT refS symS refT id_ann_eqS id_ann_not_eqT)           
       end       
  | A_SG_LTR_Id_Ann_Not_Equal _ _ _ id_ann_not_eqS =>
       match idaT_d with 
       | A_SG_LTR_Id_Ann_None _ _ _ (nidT, nannT) =>
           A_SG_LTR_Id_Ann_None _ _ _ (nidST_r nidT, nannST_r nannT)                      
       | A_SG_LTR_Id_Ann_Id_None _ _ _ (idT, nannT) =>
           A_SG_LTR_Id_Ann_Id_None _ _ _ (idST (extract_idS2 id_ann_not_eqS) idT, nannST_r nannT)                                 
       | A_SG_LTR_Id_Ann_None_Ann _ _ _ (nidT, annT) =>
           A_SG_LTR_Id_Ann_None_Ann _ _ _ (nidST_r nidT, annST (extract_annS2 id_ann_not_eqS) annT)                                 
       | A_SG_LTR_Id_Ann_Equal _ _ _ id_ann_eqT =>
           A_SG_LTR_Id_Ann_Not_Equal _ _ _ (@A_sg_ltr_llex_product_exists_id_ann_not_equal_v1 LS S LT T eqS eqT argT addS addT ltrS ltrT symS refT id_ann_not_eqS id_ann_eqT)                      
       | A_SG_LTR_Id_Ann_Not_Equal _ _ _ id_ann_not_eqT =>
           A_SG_LTR_Id_Ann_Not_Equal _ _ _ (@A_sg_ltr_llex_product_exists_id_ann_not_equal_v3 LS S LT T eqS eqT argT addS addT ltrS ltrT symS refT id_ann_not_eqS id_ann_not_eqT)
    end 
  end. 

End Decide.


Section Proofs.


  Variables
    (LS S LT T : Type)
    (eqLS : brel LS)
    (wLS : LS)       
    (eqS  : brel S)
    (wS : S) 
    (eqLT : brel LT)
    (wLT : LT)
    (eqT : brel T)
    (wT : T)
    (eqvLSP : eqv_proofs LS eqLS) 
    (eqvSP  : eqv_proofs S eqS) 
    (eqvTP  : eqv_proofs T eqT)
    (addS : binary_op S)
    (addT : binary_op T)
    (addSP : sg_CS_proofs S eqS addS)
    (addTP : sg_C_proofs T eqT addT)     
    (ltrS : ltr_type LS S)
    (ltrT : ltr_type LT T)
    (QS : A_ltr_properties eqLS eqS ltrS)
    (QT : A_ltr_properties eqLT eqT ltrT)           
    (PS : A_sg_ltr_properties eqS addS ltrS)
    (PT : A_sg_ltr_properties eqT addT ltrT).

Definition A_sg_ltr_llex_product_properties_selective_version : 
  A_sg_ltr_properties
    (brel_product eqS eqT)
    (bop_llex wT eqS addS addT)
    (ltr_product_op ltrS ltrT) :=
let congS := A_sg_CS_congruence _ _ _ addSP in   
let selS := A_sg_CS_selective _ _ _ addSP in
let idemS := bop_selective_implies_idempotent _ eqS addS selS in
let congT := A_sg_C_congruence _ _ _ addTP in   
let commT := A_sg_C_commutative _ _ _ addTP in
let cong_ltrS := A_ltr_props_congruence _ _ _ QS in 
let DS_d := A_sg_ltr_distributive_d _ _ _ PS in
let DT_d := A_sg_ltr_distributive_d _ _ _ PT in
let CS_d := A_ltr_props_cancellative_d _ _ _ QS in
let KT_d := A_ltr_props_constant_d _ _ _ QT in
let asbS_d := A_sg_ltr_absorptive_d _ _ _ PS in
let asbT_d := A_sg_ltr_absorptive_d _ _ _ PT in
let sasbS_d := A_sg_ltr_strictly_absorptive_d _ _ _ PS in
let sasbT_d := A_sg_ltr_strictly_absorptive_d _ _ _ PT in
{|
  A_sg_ltr_distributive_d          :=
    A_sg_ltr_llex_product_distributive_decide
      LS S LT T eqLS eqS eqT wT wLS wLT wS wT eqvLSP eqvSP eqvTP addS addT idemS 
      commT ltrS ltrT congS congT cong_ltrS commT (inl selS) DS_d DT_d CS_d KT_d
; A_sg_ltr_absorptive_d            :=
    A_sg_ltr_llex_product_absorptive_decide LS S LT T eqS eqT wT wLT
      wT eqvSP eqvTP addS addT idemS ltrS ltrT sasbS_d asbS_d asbT_d
; A_sg_ltr_strictly_absorptive_d   :=
    A_sg_ltr_llex_product_strictly_absorptive_decide LS S LT T eqS eqT wT wLT
      wT eqvSP eqvTP addS addT ltrS ltrT sasbS_d asbS_d sasbT_d
|}.

    
End Proofs.   

Section Combinators.

Definition A_sg_ltr_llex_product {LS S LT T: Type} 
 (A : @A_sg_ltr_S LS S)
 (B : @A_sg_ltr LT T) : @A_sg_ltr (LS * LT) (S * T) :=
let eqvS  := A_sg_ltr_S_carrier A in
let eqvT  := A_sg_ltr_carrier B in
let eqvLS := A_sg_ltr_S_label A in
let eqvLT := A_sg_ltr_label B in
let wS    := A_eqv_witness _ eqvS in
let nS    := A_eqv_new _ eqvS in
let ntS   := A_eqv_not_trivial _ eqvS in 
let wT    := A_eqv_witness _ eqvT in
let nT    := A_eqv_new _ eqvT in 
let ntT   := A_eqv_not_trivial _ eqvT in 
let eqS   := A_eqv_eq _ eqvS in
let eqT   := A_eqv_eq _ eqvT in
let eqLS  := A_eqv_eq _ eqvLS in 
let wLS   := A_eqv_witness _ eqvLS in 
let eqLT  := A_eqv_eq _ eqvLT in 
let wLT   := A_eqv_witness _ eqvLT in 
let addS  := A_sg_ltr_S_plus A in
let addT  := A_sg_ltr_plus B in
let ltrS  := A_sg_ltr_S_ltr A in
let ltrT  := A_sg_ltr_ltr B in
let eqvSP := A_eqv_proofs _ eqvS in
let eqvTP := A_eqv_proofs _ eqvT in
let eqvLSP := A_eqv_proofs _ eqvLS in 
let addSP := A_sg_ltr_S_plus_props A in 
let addTP := A_sg_ltr_plus_props B in
let ltrSP := A_sg_ltr_S_ltr_props A in 
let ltrTP := A_sg_ltr_ltr_props B in 
let refS  := A_eqv_reflexive _ _ eqvSP in
let symS  := A_eqv_symmetric _ _ eqvSP in
let refT  := A_eqv_reflexive _ _ eqvTP in
let id_annSP := A_sg_ltr_S_id_ann_props_d A in
let id_annTP := A_sg_ltr_id_ann_props_d B in 
      {|
        A_sg_ltr_carrier :=
          A_eqv_product _ _ eqvS eqvT
      ; A_sg_ltr_label :=
          A_eqv_product _ _ eqvLS eqvLT 
      ; A_sg_ltr_plus :=
          bop_llex wT eqS addS addT 
      ; A_sg_ltr_ltr :=
          ltr_product_op ltrS ltrT 
      ; A_sg_ltr_plus_props :=
          @sg_CS_sg_C_llex_proofs S T wS wT 
            eqS eqT nS ntS nT ntT addS addT eqvSP eqvTP addSP addTP
      ; A_sg_ltr_ltr_props :=
          A_ltr_product_properties LS LT S T 
             eqS eqLS wS wLS ltrS refS eqT eqLT wT wLT ltrT refT ltrSP ltrTP
      ; A_sg_ltr_id_ann_props_d :=
          A_sg_ltr_llex_product_proofs_exists_id_ann_decidable LS S LT T
            eqS eqT refS symS refT wT wLS wLT addS addT ltrS ltrT
            id_annSP id_annTP 
      ; A_sg_ltr_props :=
          A_sg_ltr_llex_product_properties_selective_version LS S LT T eqLS wLS eqS wS
            eqLT wLT eqT wT eqvLSP eqvSP eqvTP addS addT addSP addTP ltrS ltrT
            ltrSP ltrTP (A_sg_ltr_S_props A) (A_sg_ltr_props B)
      ; A_sg_ltr_ast :=
          ast.Cas_ast ("sg_ltr_llex_product", 
              [A_sg_ltr_S_ast A; A_sg_ltr_ast B])
      |}.
    
End Combinators.   
  
End ACAS.

Section AMCAS.

  Open Scope string_scope.

  Definition A_sg_ltr_llex_product_below_sg_ltr_S {LS S LT T : Type}
    (A : @A_below_sg_ltr_S LS S)
    (B : @A_below_sg_ltr LT T) := 
    A_classify_sg_ltr (A_sg_ltr_llex_product (A_cast_up_sg_ltr_S A) (A_cast_up_sg_ltr B)).  

  Definition A_mcas_sg_ltr_llex_product {LS S LT T : Type}
    (A : @A_sg_ltr_mcas LS S)
    (B : @A_sg_ltr_mcas LT T)  : @A_sg_ltr_mcas (LS * LT) (S * T) :=
    match A, B with
    | A_MCAS_sg_ltr A', A_MCAS_sg_ltr B'               =>
        match A_cast_below_sg_ltr_to_below_sg_ltr_S A' with
        | Some bcs => A_MCAS_sg_ltr (A_sg_ltr_llex_product_below_sg_ltr_S bcs B')
        | None     => A_MCAS_sg_ltr_Error ("sg_ltr_llex_product : the additive component of the first argument must be selective." :: nil)
        end 
    | A_MCAS_sg_ltr_Error sl1, A_MCAS_sg_ltr_Error sl2 =>
        A_MCAS_sg_ltr_Error (sl1 ++ sl2)
    | A_MCAS_sg_ltr_Error sl1, _ =>
        A_MCAS_sg_ltr_Error sl1
    | _,  A_MCAS_sg_ltr_Error sl2  =>
        A_MCAS_sg_ltr_Error sl2
    end.


End AMCAS.

Section CAS.

Section Decide.


Variables (LS S LT T : Type)  
          (argT : T)
          (rS : brel S)
          (rT : brel T)
          (bopS : binary_op S)
          (bopT : binary_op T)
          (ltrS : ltr_type LS S)
          (ltrT : ltr_type LT T).


  
  Definition witness_sg_ltr_llex_product_not_left_distributive_new 
    (selS_or_id_annT : @assert_selective S + (@assert_exists_id T * @assert_exists_ann T))
    (s1 : LS) (s2 s3 : S)
    (t1 : LT) (t2 t3 : T)
  := if (rS (bopS s2 s3) s2) 
  then if rS (bopS s2 s3) s3
    then (* can't reach this branch *) 
        ((s1, t1), ((s2, t2), (s3, t3)))
    else  if rS (ltrS s1 s2) (bopS (ltrS s1 s2) (ltrS s1 s3))
          then (* case 1 *) 
              if rT (ltrT t1 t2) (bopT (ltrT t1 t2) (ltrT t1  t3))
              then ((s1, t1), ((s2, t3), (s3, t2)))
              else ((s1, t1), ((s2, t2), (s3, t3)))
          else (* case 2 *) 
              ((s1, t1), ((s2, t2), (s3, t3)))
  else if rS (bopS s2 s3) s3
    then (* case 3 *) 
        if rT (ltrT t1 t3) (bopT (ltrT t1 t2) (ltrT t1 t3))
        then ((s1, t1), ((s2, t3), (s3, t2)))
        else ((s1, t1), ((s2, t2), (s3, t3)))
    else (* case 4 *) 
        match selS_or_id_annT with 
        | inl _ => (* can't reach this branch *) 
                  ((s1, t1), ((s2, t2), (s3, t3)))
        | inr _ => if rT argT (ltrT t1 t2)
                    then ((s1, t1), ((s2, argT), (s3, t3)))
                    else ((s1, t1), ((s2, argT), (s3, t2)))
        end.  


Definition sg_ltr_llex_product_distributive_decide
           (wLT : LT) (wT : T) 
           (selS_or_id_annT : @assert_selective S + 
                 (@assert_exists_id T * @assert_exists_ann T))    
           (LDS_d : @sg_ltr_distributive_decidable LS S) 
           (LDT_d : @sg_ltr_distributive_decidable LT T) 
           (LCS_d : @ltr_cancellative_decidable LS S) 
           (LKT_d : @ltr_constant_decidable LT T) : 
  @sg_ltr_distributive_decidable (LS * LT) (S * T) :=
let selS_or_annT :=
        match selS_or_id_annT with 
        | inl sel => inl sel 
        | inr (_, is_ann) => inr is_ann 
        end 
in       
match LDS_d with
| inl (SG_LTR_Distributive (wLS, wS))  =>
  match LDT_d with
  | inl (SG_LTR_Distributive (wLT, wT))  =>
      match LCS_d with
      | inl (LTR_cancellative _ )  =>
          inl (SG_LTR_Distributive  ((wLS, wLT), (wS, wT)))
      | inr (LTR_not_cancellative (lS, (s1, s2))) =>
          match LKT_d with
          | inl (LTR_constant _)  =>
              inl (SG_LTR_Distributive  ((wLS, wLT), (wS, wT)))
          | inr (LTR_not_constant (lT, (t1, t2))) =>
              inr (SG_LTR_Not_Distributive
                     (witness_sg_ltr_llex_product_not_left_distributive_new 
                        selS_or_id_annT lS s1 s2 lT t1 t2))
          end 
      end 
  | inr (SG_LTR_Not_Distributive  (l, (t1, t2))) =>
    inr (SG_LTR_Not_Distributive ((wLS, l), ((wS, t1), (wS, t2))))
  end 
| inr (SG_LTR_Not_Distributive  (l, (s1, s2))) =>
    inr (SG_LTR_Not_Distributive ((l, wLT), ((s1, wT), (s2, wT))))
end.     


Definition sg_ltr_llex_product_absorptive_decide
  (wLT : LT) (wT : T) 
  (sabsS_d : @sg_ltr_strictly_absorptive_decidable LS S)
  (absS_d : @sg_ltr_absorptive_decidable LS S)
  (absT_d : @sg_ltr_absorptive_decidable LT T) :
     @sg_ltr_absorptive_decidable (LS * LT) (S * T) := 
match sabsS_d with
| inl (SG_LTR_Strictly_Absorptive (l, s) )  =>
    inl(SG_LTR_Absorptive ((l, wLT), (s, wT)))
| inr (SG_LTR_Not_Strictly_Absorptive (lS', s') ) =>
  match absS_d with
  | inl (SG_LTR_Absorptive (lS, s))   =>
    match absT_d with
    | inl (SG_LTR_Absorptive (lT, t))  =>
        inl(SG_LTR_Absorptive ((lS, lT), (s, t)))
    | inr (SG_LTR_Not_Absorptive (l, t))=>
        inr(SG_LTR_Not_Absorptive ((lS', l), (s', t)))
    end 
  | inr (SG_LTR_Not_Absorptive (lS, s)) =>
      inr (SG_LTR_Not_Absorptive ((lS, wLT), (s, wT)))
  end
end.     

Definition sg_ltr_llex_product_strictly_absorptive_decide
  (wLT : LT) (wT : T) 
  (sabsS_d : @sg_ltr_strictly_absorptive_decidable LS S)
  (absS_d : @sg_ltr_absorptive_decidable LS S)
  (absT_d : @sg_ltr_strictly_absorptive_decidable LT T) :
    @sg_ltr_strictly_absorptive_decidable (LS * LT) (S * T) := 
match sabsS_d with
| inl (SG_LTR_Strictly_Absorptive (l, s) )  =>
    inl(SG_LTR_Strictly_Absorptive ((l, wLT), (s, wT)))
| inr (SG_LTR_Not_Strictly_Absorptive (lS', s') ) =>
  match absS_d with
  | inl (SG_LTR_Absorptive (lS, s))   =>
    match absT_d with
    | inl (SG_LTR_Strictly_Absorptive (lT, t))  =>
        inl(SG_LTR_Strictly_Absorptive ((lS, lT), (s, t)))
    | inr (SG_LTR_Not_Strictly_Absorptive (l, t))=>
        inr(SG_LTR_Not_Strictly_Absorptive ((lS', l), (s', t)))
    end 
  | inr (SG_LTR_Not_Absorptive (lS, s)) =>
      inr (SG_LTR_Not_Strictly_Absorptive ((lS, wLT), (s, wT)))
  end
end.     



Definition sg_ltr_llex_product_proofs_exists_id_ann_decidable 
    (idaS_d : @sg_ltr_exists_id_ann_decidable LS S)
    (idaT_d : @sg_ltr_exists_id_ann_decidable LT T) : 
    @sg_ltr_exists_id_ann_decidable (LS * LT) (S * T) := 
  match idaS_d with
  | SG_LTR_Id_Ann_None => SG_LTR_Id_Ann_None 
  | SG_LTR_Id_Ann_Id_None idS =>
       match idaT_d with 
       | SG_LTR_Id_Ann_None =>
           SG_LTR_Id_Ann_None  
       | SG_LTR_Id_Ann_Id_None idT =>
           SG_LTR_Id_Ann_Id_None (idS, idT)
       | SG_LTR_Id_Ann_None_Ann _ =>
           SG_LTR_Id_Ann_None   
       | SG_LTR_Id_Ann_Equal id_annT =>
           SG_LTR_Id_Ann_Id_None (idS, id_annT)
       | SG_LTR_Id_Ann_Not_Equal (idT, annT) =>  
           SG_LTR_Id_Ann_Id_None (idS, idT)
       end       
  | SG_LTR_Id_Ann_None_Ann annS =>
       match idaT_d with 
       | SG_LTR_Id_Ann_None  =>
           SG_LTR_Id_Ann_None  
       | SG_LTR_Id_Ann_Id_None idT => 
           SG_LTR_Id_Ann_None 
       | SG_LTR_Id_Ann_None_Ann annT =>
           SG_LTR_Id_Ann_None_Ann (annS, annT)
       | SG_LTR_Id_Ann_Equal id_annT =>
           SG_LTR_Id_Ann_None_Ann (annS, id_annT)
       | SG_LTR_Id_Ann_Not_Equal (idT, annT) => 
           SG_LTR_Id_Ann_None_Ann (annS, annT)
       end      
  | SG_LTR_Id_Ann_Equal   id_annS =>
       match idaT_d with 
       | SG_LTR_Id_Ann_None =>
           SG_LTR_Id_Ann_None 
       | SG_LTR_Id_Ann_Id_None idT =>
           SG_LTR_Id_Ann_Id_None (id_annS, idT) 
       | SG_LTR_Id_Ann_None_Ann annT =>
           SG_LTR_Id_Ann_None_Ann (id_annS, annT)
       | SG_LTR_Id_Ann_Equal id_annT =>
           SG_LTR_Id_Ann_Equal  (id_annS, id_annT) 
       | SG_LTR_Id_Ann_Not_Equal (idT, annT) => 
           SG_LTR_Id_Ann_Not_Equal ((id_annS, idT), (id_annS, annT)) 
       end       
  | SG_LTR_Id_Ann_Not_Equal (idS, annS) =>
       match idaT_d with 
       | SG_LTR_Id_Ann_None  =>
           SG_LTR_Id_Ann_None 
       | SG_LTR_Id_Ann_Id_None idT =>
           SG_LTR_Id_Ann_Id_None (idS, idT) 
       | SG_LTR_Id_Ann_None_Ann annT =>
           SG_LTR_Id_Ann_None_Ann (annS, annT) 
       | SG_LTR_Id_Ann_Equal id_annT =>
           SG_LTR_Id_Ann_Not_Equal ((idS, id_annT), (annS, id_annT))
       | SG_LTR_Id_Ann_Not_Equal  (idT, annT) =>
           SG_LTR_Id_Ann_Not_Equal ((idS, idT), (annS, annT))
    end 
  end. 

End Decide.       

Section Proofs.


  Variables
    (LS S LT T : Type)
    (eqS  : brel S)
    (eqLT : brel LT)
    (wLT : LT)
    (eqT : brel T)
    (wT : T)
    (addS : binary_op S)
    (addT : binary_op T)
    (ltrS : ltr_type LS S)
    (ltrT : ltr_type LT T)
    (QS : @ltr_properties LS S)
    (QT : @ltr_properties LT T)           
    (PS : @sg_ltr_properties LS S)
    (PT : @sg_ltr_properties LT T).


Definition sg_ltr_llex_product_properties_selective_version : 
  @sg_ltr_properties (LS * LT) (S * T) := 
let DS_d := sg_ltr_distributive_d PS in
let DT_d := sg_ltr_distributive_d  PT in
let CS_d := ltr_props_cancellative_d QS in
let KT_d := ltr_props_constant_d QT in
let asbS_d := sg_ltr_absorptive_d PS in
let asbT_d := sg_ltr_absorptive_d PT in
let sasbS_d := sg_ltr_strictly_absorptive_d PS in
let sasbT_d := sg_ltr_strictly_absorptive_d PT in
{|
  sg_ltr_distributive_d          :=
    sg_ltr_llex_product_distributive_decide
      LS S LT T wT eqS eqT addS addT ltrS ltrT
      wLT wT (inl Assert_Selective) DS_d DT_d CS_d KT_d
; sg_ltr_absorptive_d            :=
    sg_ltr_llex_product_absorptive_decide LS S LT T wLT wT
      sasbS_d asbS_d asbT_d
; sg_ltr_strictly_absorptive_d   :=
    sg_ltr_llex_product_strictly_absorptive_decide LS S LT T wLT wT
      sasbS_d asbS_d sasbT_d
|}.

    
End Proofs.   


Section Combinators.

Definition sg_ltr_llex_product {LS S LT T: Type} 
 (A : @sg_ltr_S LS S)
 (B : @sg_ltr LT T) : @sg_ltr (LS * LT) (S * T) :=
let eqvS  := sg_ltr_S_carrier A in
let eqvT  := sg_ltr_carrier B in
let eqvLS := sg_ltr_S_label A in
let eqvLT := sg_ltr_label B in
let wS    := eqv_witness eqvS in
let nS    := eqv_new eqvS in
let wT    := eqv_witness eqvT in
let nT    := eqv_new eqvT in 
let eqS   := eqv_eq eqvS in
let eqT   := eqv_eq eqvT in
let eqLS  := eqv_eq eqvLS in 
let wLS   := eqv_witness eqvLS in 
let eqLT  := eqv_eq eqvLT in 
let wLT   := eqv_witness eqvLT in 
let addS  := sg_ltr_S_plus A in
let addT  := sg_ltr_plus B in
let ltrS  := sg_ltr_S_ltr A in
let ltrT  := sg_ltr_ltr B in
let addSP := sg_ltr_S_plus_props A in 
let addTP := sg_ltr_plus_props B in
let ltrSP := sg_ltr_S_ltr_props A in 
let ltrTP := sg_ltr_ltr_props B in 
let id_annSP := sg_ltr_S_id_ann_props_d A in
let id_annTP := sg_ltr_id_ann_props_d B in 
      {|
        sg_ltr_carrier :=
          eqv_product eqvS eqvT
      ; sg_ltr_label :=
          eqv_product eqvLS eqvLT 
      ; sg_ltr_plus :=
          bop_llex wT eqS addS addT 
      ; sg_ltr_ltr :=
          ltr_product_op ltrS ltrT 
      ; sg_ltr_plus_props :=
          sg_CS_sg_C_llex_certificates eqS wS nS wT nT addS addSP addTP
      ; sg_ltr_ltr_props :=
          ltr_product_properties ltrSP ltrTP wLS wS wLT wT 
      ; sg_ltr_id_ann_props_d :=
          sg_ltr_llex_product_proofs_exists_id_ann_decidable LS S LT T
            id_annSP id_annTP 
      ; sg_ltr_props :=
          sg_ltr_llex_product_properties_selective_version LS S LT T
            eqS wLT eqT wT addS addT
            ltrS ltrT ltrSP ltrTP (sg_ltr_S_props A) (sg_ltr_props B)
      ; sg_ltr_ast :=
          ast.Cas_ast ("sg_ltr_llex_product", 
              [sg_ltr_S_ast A; sg_ltr_ast B])
      |}.

End Combinators.   
  
End CAS.

Section MCAS.
  Definition sg_ltr_llex_product_below_sg_ltr_S {LS S LT T : Type}
    (A : @below_sg_ltr_S LS S)
    (B : @below_sg_ltr LT T) := 
    classify_sg_ltr (sg_ltr_llex_product (cast_up_sg_ltr_S A) (cast_up_sg_ltr B)).  

  Definition mcas_sg_ltr_llex_product {LS S LT T : Type}
    (A : @sg_ltr_mcas LS S)
    (B : @sg_ltr_mcas LT T)  : @sg_ltr_mcas (LS * LT) (S * T) :=
    match A, B with
    | MCAS_sg_ltr A', MCAS_sg_ltr B'               =>
        match cast_below_sg_ltr_to_below_sg_ltr_S A' with
        | Some bcs => MCAS_sg_ltr (sg_ltr_llex_product_below_sg_ltr_S bcs B')
        | None     => MCAS_sg_ltr_Error ("sg_ltr_llex_product : the additive component of the first argument must be selective." :: nil)
        end 
    | MCAS_sg_ltr_Error sl1, MCAS_sg_ltr_Error sl2 =>
        MCAS_sg_ltr_Error (sl1 ++ sl2)
    | MCAS_sg_ltr_Error sl1, _ =>
        MCAS_sg_ltr_Error sl1
    | _,  MCAS_sg_ltr_Error sl2  =>
        MCAS_sg_ltr_Error sl2
    end.

End MCAS.


Section Verify.


Section Decide.

Variables (LS S LT T : Type)  
          (eqLS : brel LS)
          (eqLT : brel LT)
          (eqS : brel S)
          (eqT : brel T)
          (conS : brel_congruence _ eqS eqS)
          (refS : brel_reflexive _ eqS)
          (symS : brel_symmetric _ eqS)
          (trnS : brel_transitive _ eqS)
          (conT : brel_congruence _ eqT eqT)          
          (refT : brel_reflexive _ eqT)
          (symT : brel_symmetric _ eqT)
          (trnT : brel_transitive _ eqT)          
          (argT : T)
          (wLS : LS)
          (wLT : LT)                     
          (wS : S)
          (wT : T)           
          (eqvLS : eqv_proofs LS eqLS)
          (eqvLT : eqv_proofs LT eqLT)                     
          (eqvS : eqv_proofs S eqS)
          (eqvT : eqv_proofs T eqT)           
          (addS : binary_op S) 
          (addT : binary_op T)
          (idemS : bop_idempotent S eqS addS)
          (commS : bop_commutative S eqS addS)
          (commT : bop_commutative T eqT addT)                     
          (ltrS : ltr_type LS S)
          (ltrT : ltr_type LT T)
          (a_congS : bop_congruence S eqS addS)
          (a_congT : bop_congruence T eqT addT)
          (ltr_congS : A_ltr_congruence eqLS eqS ltrS).                     


Theorem correct_sg_ltr_llex_product_proofs_exists_id_ann_decidable
    (idaS_d : A_sg_ltr_exists_id_ann_decidable eqS addS ltrS)
    (idaT_d : A_sg_ltr_exists_id_ann_decidable eqT addT ltrT) :           
  p2c_sg_ltr_exists_id_ann_decidable
    (brel_product eqS eqT)
    (bop_llex wT eqS addS addT)
    (ltr_product_op ltrS ltrT)
    (A_sg_ltr_llex_product_proofs_exists_id_ann_decidable
       LS S LT T eqS eqT
       refS symS refT wT wLS wLT addS addT ltrS ltrT idaS_d idaT_d)
  =
  sg_ltr_llex_product_proofs_exists_id_ann_decidable LS S LT T 
     (p2c_sg_ltr_exists_id_ann_decidable eqS addS ltrS idaS_d)
     (p2c_sg_ltr_exists_id_ann_decidable eqT addT ltrT idaT_d). 
Proof. unfold A_sg_ltr_llex_product_proofs_exists_id_ann_decidable,
         sg_ltr_llex_product_proofs_exists_id_ann_decidable,
         p2c_sg_ltr_exists_id_ann_decidable;
         destruct idaS_d as [[p1 p2] | [[idS p1] p2] | [p1 [idS p2]] | [id_annS [p1 p2]] | [[idS annS] [[p1 p2] p3]]]; 
         destruct idaT_d as [[q1 q2] | [[idT q1] q2] | [q1 [idT q2]] | [id_annT [q1 q2]] | [[idT annT] [[q1 q2] q3]]];
         reflexivity. 
Qed.

Lemma correct_sg_ltr_llex_product_distributive_decide
   (selS : bop_selective S eqS addS)
   (LCS_d : A_ltr_cancellative_decidable eqS ltrS)
   (LKT_d : A_ltr_constant_decidable eqT ltrT)
   (LDS_d : A_sg_ltr_distributive_decidable eqS addS ltrS)
   (LDT_d : A_sg_ltr_distributive_decidable eqT addT ltrT): 
    p2c_sg_ltr_distributive_decidable
      (brel_product eqS eqT)
      (bop_llex wT eqS addS addT)
      (ltr_product_op ltrS ltrT)
      (A_sg_ltr_llex_product_distributive_decide LS S LT T
         eqLS eqS eqT wT wLS wLT wS wT eqvLS eqvS eqvT
         addS addT idemS commT ltrS ltrT a_congS a_congT ltr_congS commT (inl selS)
           LDS_d LDT_d LCS_d LKT_d) (wLS, wLT) (wS, wT)
   = 
   sg_ltr_llex_product_distributive_decide LS S LT T wT eqS eqT
        addS addT ltrS ltrT wLT wT (inl Assert_Selective)
        (p2c_sg_ltr_distributive_decidable eqS addS ltrS LDS_d wLS wS)
        (p2c_sg_ltr_distributive_decidable eqT addT ltrT LDT_d wLT wT)
        (p2c_ltr_cancellative_decidable eqS ltrS LCS_d wLS wS)
        (p2c_ltr_constant_decidable eqT ltrT LKT_d wLT wT). 
Proof.  destruct
           LCS_d as [LCS | [[l1 [s1 s2]] [A B]] ],
           LKT_d as [LKT | [[l2 [t1 t2]] NKT] ],
           LDS_d as [LDS | [[l3 [s3 s4]] NDS] ],
           LDT_d as [LDT | [[l4 [t3 t4]] NDT] ]; 
         unfold A_sg_ltr_llex_product_distributive_decide,
         sg_ltr_llex_product_distributive_decide,
         p2c_sg_ltr_distributive_decidable, p2c_ltr_cancellative_decidable,
         p2c_ltr_constant_decidable; simpl; try reflexivity. 
Qed.

Print A_sg_ltr_not_absorptive. 
Lemma correct_sg_ltr_llex_product_absorptive_decide
  (LSAS_d : A_sg_ltr_strictly_absorptive_decidable eqS addS ltrS)
  (LAS_d : A_sg_ltr_absorptive_decidable eqS addS ltrS)
  (LAT_d : A_sg_ltr_absorptive_decidable eqT addT ltrT) : 
  p2c_sg_ltr_absorptive_decidable
    (brel_product eqS eqT)
    (bop_llex wT eqS addS addT)
    (ltr_product_op ltrS ltrT)
    (A_sg_ltr_llex_product_absorptive_decide LS S LT T eqS eqT
       wT wLT wT eqvS eqvT addS addT idemS
       ltrS ltrT LSAS_d LAS_d LAT_d)
    (wLS, wLT) (wS, wT)
    = 
    sg_ltr_llex_product_absorptive_decide LS S LT T wLT wT
        (p2c_sg_ltr_strictly_absorptive_decidable eqS addS ltrS LSAS_d wLS wS)
        (p2c_sg_ltr_absorptive_decidable eqS addS ltrS LAS_d wLS wS)
        (p2c_sg_ltr_absorptive_decidable eqT addT ltrT LAT_d wLT wT).
Proof.  destruct
           LSAS_d as [LSAS | [[l1 s1] [A | A]] ],
           LAS_d as [LAS | [[l3 s3] NAS] ],
           LAT_d as [LAT | [[l4 t3] NAT] ]; 
         unfold A_sg_ltr_llex_product_absorptive_decide,
         sg_ltr_llex_product_absorptive_decide,
         p2c_sg_ltr_strictly_absorptive_decidable, 
         p2c_sg_ltr_absorptive_decidable ; simpl; try reflexivity. 
Qed.

    
Lemma correct_sg_ltr_llex_product_strictly_absorptive_decide
  (LSAS_d : A_sg_ltr_strictly_absorptive_decidable eqS addS ltrS)
  (LAS_d : A_sg_ltr_absorptive_decidable eqS addS ltrS)
  (LSAT_d : A_sg_ltr_strictly_absorptive_decidable eqT addT ltrT) : 
  p2c_sg_ltr_strictly_absorptive_decidable
    (brel_product eqS eqT)
    (bop_llex wT eqS addS addT)
    (ltr_product_op ltrS ltrT)
    (A_sg_ltr_llex_product_strictly_absorptive_decide LS S LT T eqS eqT
       wT wLT wT eqvS eqvT addS addT ltrS ltrT LSAS_d LAS_d LSAT_d)
    (wLS, wLT) (wS, wT)
  = 
  sg_ltr_llex_product_strictly_absorptive_decide LS S LT T wLT wT
    (p2c_sg_ltr_strictly_absorptive_decidable eqS addS ltrS LSAS_d wLS wS)
    (p2c_sg_ltr_absorptive_decidable eqS addS ltrS LAS_d wLS wS)
    (p2c_sg_ltr_strictly_absorptive_decidable eqT addT ltrT LSAT_d wLT wT).
Proof.  destruct
           LSAS_d as [LSAS | [[l1 s1] [A | A]] ],
           LAS_d as [LAS | [[l3 s3] NAS] ],
           LSAT_d as [LAT | [[l4 t3] [B | B]] ]; 
         unfold A_sg_ltr_llex_product_absorptive_decide,
         sg_ltr_llex_product_absorptive_decide,
         p2c_sg_ltr_strictly_absorptive_decidable, 
         p2c_sg_ltr_absorptive_decidable ; simpl; try reflexivity. 
Qed.
  


End Decide. 


Section Properties.    

Variables (LS S LT T : Type)  
          (eqLS : brel LS)
          (eqLT : brel LT)
          (eqS : brel S)
          (eqT : brel T)
          (argT : T)
          (wLS : LS)
          (wLT : LT)                     
          (wS : S)
          (wT : T)           
          (eqvLSP : eqv_proofs LS eqLS)
          (eqvLTP : eqv_proofs LT eqLT)                     
          (eqvSP : eqv_proofs S eqS)
          (eqvTP : eqv_proofs T eqT)           
          (addS : binary_op S) 
          (addT : binary_op T)
          (ltrS : ltr_type LS S)
          (ltrT : ltr_type LT T). 



Theorem correct_sg_ltr_llex_product_properties_selective_version
  (addSP : sg_CS_proofs S eqS addS)
  (addTP : sg_C_proofs T eqT addT) 
  (ltrSP : A_ltr_properties eqLS eqS ltrS)
  (ltrTP : A_ltr_properties eqLT eqT ltrT)           
  (PS : A_sg_ltr_properties eqS addS ltrS)
  (PT : A_sg_ltr_properties eqT addT ltrT) : 
      P2C_sg_ltr_properties
        (brel_product eqS eqT)
        (bop_llex wT eqS addS addT)
        (ltr_product_op ltrS ltrT)
        (@A_sg_ltr_llex_product_properties_selective_version 
           LS S LT T eqLS wLS eqS wS eqLT wLT eqT wT
           eqvLSP eqvSP eqvTP addS addT addSP addTP 
           ltrS ltrT ltrSP ltrTP PS PT)
        (wLS, wLT) (wS, wT)
      =           
     @sg_ltr_llex_product_properties_selective_version
        LS S LT T      
        eqS wLT eqT wT addS addT ltrS ltrT
        (P2C_ltr_properties eqLS eqS ltrS ltrSP wLS wS)
        (P2C_ltr_properties eqLT eqT ltrT ltrTP wLT wT)
        (P2C_sg_ltr_properties eqS addS ltrS PS wLS wS)
        (P2C_sg_ltr_properties eqT addT ltrT PT wLT wT).
Proof. unfold A_sg_ltr_llex_product_properties_selective_version,
         sg_ltr_llex_product_properties_selective_version,
         P2C_sg_ltr_properties, P2C_ltr_properties;
         destruct addSP, addTP, ltrSP, ltrTP, PS, PT; simpl. 
       rewrite correct_sg_ltr_llex_product_distributive_decide.
       rewrite correct_sg_ltr_llex_product_absorptive_decide.        
       rewrite correct_sg_ltr_llex_product_strictly_absorptive_decide.
       reflexivity.
Qed.

  End Properties.     


Section Combinators.   

  Context {LS S LT T : Type}.

  Theorem correct_sg_ltr_llex_product 
  (A : @A_sg_ltr_S LS S) (B : @A_sg_ltr LT T) : 
    A2C_sg_ltr (A_sg_ltr_llex_product A B)
    =
   sg_ltr_llex_product (A2C_sg_ltr_S A) (A2C_sg_ltr B).
  Proof. destruct A, B; unfold A_sg_ltr_llex_product,
           sg_ltr_llex_product, A2C_sg_ltr_S,
           A2C_sg_ltr; simpl.
         rewrite correct_eqv_product.
         rewrite correct_eqv_product.
         rewrite <- correct_sg_CS_sg_C_llex_certificates. 
         rewrite correct_ltr_product_properties. 
         rewrite correct_sg_ltr_llex_product_proofs_exists_id_ann_decidable.
         rewrite correct_sg_ltr_llex_product_properties_selective_version.
         reflexivity. 
  Qed. 

  Theorem correct_sg_ltr_llex_product_below_sg_ltr_S
    (A : @A_below_sg_ltr_S LS S)
    (B : @A_below_sg_ltr LT T) :             
    A2C_below_sg_ltr (A_sg_ltr_llex_product_below_sg_ltr_S A B)
    =
    sg_ltr_llex_product_below_sg_ltr_S
      (A2C_below_sg_ltr_S A)
      (A2C_below_sg_ltr B). 
  Proof. destruct A, B;
         unfold A_sg_ltr_llex_product_below_sg_ltr_S,
           sg_ltr_llex_product_below_sg_ltr_S. 
         - simpl. rewrite <- correct_classify_sg_ltr.
           rewrite correct_sg_ltr_llex_product.
           reflexivity. 
         - rewrite cast_up_sg_ltr_A2C_commute.
           rewrite cast_up_sg_ltr_S_A2C_commute.
           rewrite <- correct_classify_sg_ltr.
           rewrite correct_sg_ltr_llex_product.
           reflexivity. 
  Qed.

  Theorem correct_cast_below_sg_ltr_to_below_sg_ltr_S
    (A : @A_below_sg_ltr LS S) :
 option_map A2C_below_sg_ltr_S (A_cast_below_sg_ltr_to_below_sg_ltr_S A)
  =
  cast_below_sg_ltr_to_below_sg_ltr_S (A2C_below_sg_ltr A). 
Proof. destruct A; unfold A_cast_below_sg_ltr_to_below_sg_ltr_S,
         cast_below_sg_ltr_to_below_sg_ltr_S; simpl; try reflexivity.
Qed.

  

Theorem correct_mcas_sg_ltr_llex_product
  (A : @A_sg_ltr_mcas LS S)
  (B : @A_sg_ltr_mcas LT T) :
  A2C_mcas_sg_ltr (A_mcas_sg_ltr_llex_product A B)
  = 
  mcas_sg_ltr_llex_product 
    (A2C_mcas_sg_ltr A)
    (A2C_mcas_sg_ltr B). 
Proof. destruct A, B; try reflexivity.
       - unfold A_mcas_sg_ltr_llex_product,
           mcas_sg_ltr_llex_product; simpl.
         rewrite <- correct_cast_below_sg_ltr_to_below_sg_ltr_S.          
         destruct (A_cast_below_sg_ltr_to_below_sg_ltr_S a);
           simpl; try reflexivity. 
         + rewrite correct_sg_ltr_llex_product_below_sg_ltr_S.
           reflexivity.
Qed. 
  
End Combinators.   

End Verify.   


