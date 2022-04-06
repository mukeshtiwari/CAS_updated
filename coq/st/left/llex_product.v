Require Import Coq.Bool.Bool.
Require Import CAS.coq.common.compute.

Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures. 
Require Import CAS.coq.eqv.product.

Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures.
Require Import CAS.coq.sg.llex.
Require Import CAS.coq.sg.and. 

Require Import CAS.coq.tr.properties.
Require Import CAS.coq.tr.structures. 
Require Import CAS.coq.tr.left.product. 

Require Import CAS.coq.st.properties.
Require Import CAS.coq.st.structures. 
(* why? *) 
Definition ltr_weak_congruence (L S : Type) (rS : brel S) (lt : ltr_type L S) := 
   ∀ (l : L) (s1 s2 : S), rS s1 s2 = true -> rS (lt l s1) (lt l s2) = true.


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

(*
Variable m_conS : ltr_weak_congruence LS S rS mulS.
Variable m_conT : ltr_weak_congruence LT T rT mulT. 
 *)

Variable m_conS : ltr_congruence LS S eqLS eqS ltrS.
Variable m_conT : ltr_congruence LT T eqLT eqT ltrT.

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
Notation "a [*] b" := (ltr_product a b) (at level 15).

(* Note : this is a minor modification of the proof from bs/llex_product.v .... *) 
Lemma slt_llex_product_distributive
      (selS_or_annT : bop_selective S eqS addS + ltr_is_ann LT T eqT ltrT argT)      
      (ldS : slt_distributive LS S eqS addS ltrS)
      (ldT : slt_distributive LT T eqT addT ltrT) 
      (D : ((ltr_left_cancellative LS S eqS ltrS) + (ltr_left_constant LT T eqT ltrT))): 
             slt_distributive (LS * LT) (S * T) (eqS <*> eqT) (addS [+] addT) (ltrS [*] ltrT). 
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
           assert (F5 := trnS _ _ _ F2 F4). 
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


Lemma slt_llex_product_not_distributive_v1 : 
      slt_not_distributive LS S eqS addS ltrS → slt_not_distributive (LS * LT) (S * T) (eqS <*> eqT) (addS [+] addT) (ltrS [*] ltrT). 
Proof. intros [ [s1 [s2 s3 ] ] nld ]. exists ((s1, wLT), ((s2, wT), (s3, wT))); simpl. rewrite nld. simpl. reflexivity. Defined. 

Lemma slt_llex_product_not_distributive_v2 (dS : slt_distributive LS S eqS addS ltrS): 
  slt_not_distributive LT T eqT addT ltrT → slt_not_distributive (LS * LT) (S * T) (eqS <*> eqT) (addS [+] addT) (ltrS [*] ltrT).
Proof. intros [ [t1 [t2 t3 ] ] nld ].
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

Definition A_witness_slt_llex_product_not_left_distributive
      (selS_or_id_annT : bop_selective S eqS addS + (bop_is_id T eqT addT argT * ltr_is_ann LT T eqT ltrT argT))
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

(* for use in CAS 
Definition witness_slt_llex_product_not_left_distributive_new
      (selS_or_id_annT : @assert_selective S + (@assert_exists_id T * @assert_exists_ann T))
      (s1 : LS) (s2 s3 : S)
      (t1 : LT) (t2 t3 : T)
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

*) 
Lemma slt_llex_product_not_distributive_v3
      (a_commT : bop_commutative T eqT addT) (*NB*)
      (selS_or_id_annT : bop_selective S eqS addS + (bop_is_id T eqT addT argT * ltr_is_ann LT T eqT ltrT argT))
      (ldS : slt_distributive LS S eqS addS ltrS)
      (ldT : slt_distributive LT T eqT addT ltrT) : 
      ltr_not_left_cancellative LS S eqS ltrS →
      ltr_not_left_constant LT T eqT ltrT → 
         slt_not_distributive (LS * LT) (S * T) (eqS <*> eqT) (addS [+] addT) (ltrS [*] ltrT).
Proof. intros [ [s1 [s2 s3 ] ] [E N] ] [ [t1 [ t2 t3 ]] F].
       (* to understand the cases below, assume we have done this: 
          
           exists ((s1, a), ((s2, b), (s3, c))).

          In each of the four cases pick a, b, and c to make that case work. 
        *)
       exists(A_witness_slt_llex_product_not_left_distributive selS_or_id_annT s1 s2 s3 t1 t2 t3). 
       unfold A_witness_slt_llex_product_not_left_distributive. 
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

 slt_strictly_absorptive: 
  ∀ (l : L) (s : S),
    (eqS s (add s (ltr l s)) = true) * (eqS (ltr l s) (add s (ltr l s)) = false)

  absorptive(S) * anti_left(mulS): 
  (∀ (l : L) (s : S), 
      eqS s (add s (ltr l s)) = true) * (∀ s t : S, eqS s (mulS s t) = false)
 *)

Lemma slt_llex_product_absorptive : 
      (slt_strictly_absorptive LS S eqS addS ltrS) +  
      ((slt_absorptive LS S eqS addS ltrS) * (slt_absorptive LT T eqT addT ltrT)) → 
         slt_absorptive (LS * LT) (S * T) (eqS <*> eqT) (addS [+] addT) (ltrS [*] ltrT).
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

Lemma slt_llex_product_not_absorptive_left : 
      slt_not_absorptive LS S eqS addS ltrS → 
         slt_not_absorptive (LS * LT) (S * T) (eqS <*> eqT) (addS [+] addT) (ltrS [*] ltrT). 
Proof. intros [ [s1 s2] P ]. exists ((s1, wLT), (s2, wT)). simpl. rewrite P. simpl. reflexivity. Defined. 


Lemma slt_llex_product_not_absorptive_right : 
      (slt_not_strictly_absorptive LS S eqS addS ltrS) *  
      ((slt_absorptive LS S eqS addS ltrS) * (slt_not_absorptive LT T eqT addT ltrT)) → 
         slt_not_absorptive (LS * LT) (S * T) (eqS <*> eqT) (addS [+] addT) (ltrS [*] ltrT).
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



Lemma slt_llex_product_strictly_absorptive : 
      (slt_strictly_absorptive LS S eqS addS ltrS) +  
      ((slt_absorptive LS S eqS addS ltrS) * (slt_strictly_absorptive LT T eqT addT ltrT)) → 
         slt_strictly_absorptive (LS * LT) (S * T) (eqS <*> eqT) (addS [+] addT) (ltrS [*] ltrT).
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


Lemma slt_llex_product_not_strictly_absorptive_left : 
      slt_not_absorptive LS S eqS addS ltrS → 
         slt_not_strictly_absorptive (LS * LT) (S * T) (eqS <*> eqT) (addS [+] addT) (ltrS [*] ltrT). 
Proof. intros [ [s1 s2] P ]. exists ((s1, wLT), (s2, wT)). simpl. rewrite P. simpl. left. reflexivity. Defined. 


Lemma slt_llex_product_not_strictly_absorptive_right : 
      (slt_not_strictly_absorptive LS S eqS addS ltrS) *  
      ((slt_absorptive LS S eqS addS ltrS) * (slt_not_strictly_absorptive LT T eqT addT ltrT)) → 
         slt_not_strictly_absorptive (LS * LT) (S * T) (eqS <*> eqT) (addS [+] addT) (ltrS [*] ltrT).
Proof. intros [[[lS s] A] [absS [[lT t] B]]]; compute.
       assert (C := absS lS s).
       exists ((lS, lT), (s, t)). rewrite C.
       destruct A as [A | A]. 
       + rewrite A in C. discriminate C.          
       + rewrite A. 
        destruct B as [B | B].
         ++ left. apply symS in A. rewrite A. exact B. 
         ++ rewrite (symS _ _ A). right. exact B.
Qed.             

End Theory. 

Section ACAS.


Section Decide.

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
          (ltr_congS : ltr_congruence LS S eqLS eqS ltrS).                     

Definition slt_llex_product_distributive_decide
           (a_commT : bop_commutative T eqT addT) 
           (selS_or_id_annT : bop_selective S eqS addS + (bop_is_id T eqT addT argT * ltr_is_ann LT T eqT ltrT argT))
           (LDS_d : slt_distributive_decidable LS S eqS addS ltrS)
           (LDT_d : slt_distributive_decidable LT T eqT addT ltrT)
           (LCS_d : ltr_left_cancellative_decidable LS S eqS ltrS)
           (LKT_d : ltr_left_constant_decidable LT T eqT ltrT): 
  slt_distributive_decidable
             (LS * LT)
             (S * T)
             (brel_product eqS eqT)
             (bop_llex argT eqS addS addT)
             (ltr_product ltrS ltrT) :=
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
    | inl LCS  => inl (slt_llex_product_distributive LS S LT T eqLS eqS eqT argT addS addT ltrS ltrT congS refS symS trnS refT trnT refLS a_congS ltr_congS idemS selS_or_annT LDS LDT (inl LCS))
    | inr nLCS =>
      match LKT_d with
      | inl LKT  => inl (slt_llex_product_distributive LS S LT T eqLS eqS eqT argT addS addT ltrS ltrT congS refS symS trnS refT trnT refLS a_congS ltr_congS idemS selS_or_annT LDS LDT (inr LKT))
      | inr nLKT => inr (slt_llex_product_not_distributive_v3 LS S LT T eqLS eqS eqT argT addS addT ltrS ltrT refS symS trnS refT symT trnT refLS a_congS a_congT ltr_congS idemS commT selS_or_id_annT LDS LDT nLCS nLKT) 
      end 
    end 
  | inr nLDT => inr (slt_llex_product_not_distributive_v2 LS S LT T eqLS eqS eqT argT wS wLS addS addT ltrS ltrT symS trnS refLS ltr_congS idemS LDS nLDT)    
  end 
| inr nLDS => inr (slt_llex_product_not_distributive_v1 LS S LT T eqS eqT argT wT wLT addS addT ltrS ltrT nLDS) 
end.     


Definition slt_llex_product_absorptive_decide
           (sabsS_d : slt_strictly_absorptive_decidable LS S eqS addS ltrS)
           (absS_d : slt_absorptive_decidable LS S eqS addS ltrS)
           (absT_d : slt_absorptive_decidable LT T eqT addT ltrT) :
  slt_absorptive_decidable
             (LS * LT)
             (S * T)
             (brel_product eqS eqT)
             (bop_llex argT eqS addS addT)
             (ltr_product ltrS ltrT) :=
let refS := A_eqv_reflexive _ _ eqvS in 
let symS := A_eqv_symmetric _ _ eqvS in
let trnS := A_eqv_transitive _ _ eqvS in
let refT := A_eqv_reflexive _ _ eqvT in 
match sabsS_d with
| inl sabsS  => inl(slt_llex_product_absorptive LS S LT T eqS eqT argT addS addT ltrS ltrT symS refT (inl sabsS))
| inr nsabsS =>
  match absS_d with
  | inl absS  =>
    match absT_d with
    | inl absT  => inl(slt_llex_product_absorptive LS S LT T eqS eqT argT addS addT ltrS ltrT symS refT (inr (absS, absT)))
    | inr nabsT => inr(slt_llex_product_not_absorptive_right LS S LT T eqS eqT argT addS addT ltrS ltrT symS trnS idemS (nsabsS, (absS, nabsT)))
    end 
  | inr nabsS => inr (slt_llex_product_not_absorptive_left LS S LT T eqS eqT argT wT wLT addS addT ltrS ltrT nabsS)
  end
end.     

Definition slt_llex_product_strictly_absorptive_decide
           (sabsS_d : slt_strictly_absorptive_decidable LS S eqS addS ltrS)
           (absS_d : slt_absorptive_decidable LS S eqS addS ltrS)
           (absT_d : slt_strictly_absorptive_decidable LT T eqT addT ltrT) :
  slt_strictly_absorptive_decidable
             (LS * LT)
             (S * T)
             (brel_product eqS eqT)
             (bop_llex argT eqS addS addT)
             (ltr_product ltrS ltrT) :=    
let refS := A_eqv_reflexive _ _ eqvS in 
let symS := A_eqv_symmetric _ _ eqvS in
let trnS := A_eqv_transitive _ _ eqvS in
let refT := A_eqv_reflexive _ _ eqvT in  
match sabsS_d with
| inl sabsS  => inl(slt_llex_product_strictly_absorptive LS S LT T eqS eqT argT addS addT ltrS ltrT symS refT (inl sabsS))
| inr nsabsS =>
  match absS_d with
  | inl absS  =>
    match absT_d with
    | inl absT  => inl(slt_llex_product_strictly_absorptive LS S LT T eqS eqT argT addS addT ltrS ltrT symS refT (inr (absS, absT)))
    | inr nabsT => inr(slt_llex_product_not_strictly_absorptive_right LS S LT T eqS eqT argT addS addT ltrS ltrT symS (nsabsS, (absS, nabsT)))
    end 
  | inr nabsS => inr (slt_llex_product_not_strictly_absorptive_left LS S LT T eqS eqT argT wT wLT addS addT ltrS ltrT nabsS)
  end
end.

Definition stl_llex_product_proofs
           (a_commT : bop_commutative T eqT addT) 
           (selS_or_id_annT : bop_selective S eqS addS + (bop_is_id T eqT addT argT * ltr_is_ann LT T eqT ltrT argT))
           (QS : left_transform_proofs LS S eqS eqLS ltrS)
           (QT : left_transform_proofs LT T eqT eqLT ltrT)           
           (PS : slt_proofs LS S eqS addS ltrS)
           (PT : slt_proofs LT T eqT addT ltrT) : 
  slt_proofs (LS * LT)
             (S * T)
             (brel_product eqS eqT)
             (bop_llex argT eqS addS addT)
             (ltr_product ltrS ltrT) :=
let DS_d := A_slt_distributive_d _ _ _ _ _ PS in
let DT_d := A_slt_distributive_d _ _ _ _ _ PT in
let CS_d := A_left_transform_left_cancellative_d _ _ _ _ _ QS in
let KT_d := A_left_transform_left_constant_d _ _ _ _ _ QT in
let asbS_d := A_slt_absorptive_d _ _ _ _ _ PS in
let asbT_d := A_slt_absorptive_d _ _ _ _ _ PT in
let sasbS_d := A_slt_strictly_absorptive_d _ _ _ _ _ PS in
let sasbT_d := A_slt_strictly_absorptive_d _ _ _ _ _ PT in
{|
  A_slt_distributive_d          := slt_llex_product_distributive_decide commT selS_or_id_annT DS_d DT_d CS_d KT_d 
; A_slt_absorptive_d            := slt_llex_product_absorptive_decide sasbS_d asbS_d asbT_d
; A_slt_strictly_absorptive_d   := slt_llex_product_strictly_absorptive_decide sasbS_d asbS_d sasbT_d
|}.

End Decide.     

Section Combinators.

  
    
End Combinators.   
  
End ACAS.

Section CAS.

Section Decide.

(*  
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
          (addS : binary_op S) 
          (addT : binary_op T)
          (idemS : bop_idempotent S eqS addS)
          (commS : bop_commutative S eqS addS)
          (commT : bop_commutative T eqT addT)                     
          (ltrS : ltr_type LS S)
          (ltrT : ltr_type LT T).

Definition slt_llex_product_distributive_certify
           (a_commT : bop_commutative T eqT addT) 
           (selS_or_id_annT : bop_selective S eqS addS + (bop_is_id T eqT addT argT * ltr_is_ann LT T eqT ltrT argT))
           (LDS_d : slt_distributive_decidable LS S eqS addS ltrS)
           (LDT_d : slt_distributive_decidable LT T eqT addT ltrT)
           (LCS_d : ltr_left_cancellative_decidable LS S eqS ltrS)
           (LKT_d : ltr_left_constant_decidable LT T eqT ltrT): 
  @slt_distributive_decidable (LS * LT) (S * T) := 
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
    | inl LCS  => inl (slt_llex_product_distributive LS S LT T eqLS eqS eqT argT addS addT ltrS ltrT congS refS symS trnS refT trnT refLS a_congS ltr_congS idemS selS_or_annT LDS LDT (inl LCS))
    | inr nLCS =>
      match LKT_d with
      | inl LKT  => inl (slt_llex_product_distributive LS S LT T eqLS eqS eqT argT addS addT ltrS ltrT congS refS symS trnS refT trnT refLS a_congS ltr_congS idemS selS_or_annT LDS LDT (inr LKT))
      | inr nLKT => inr (slt_llex_product_not_distributive_v3 LS S LT T eqLS eqS eqT argT addS addT ltrS ltrT refS symS trnS refT symT trnT refLS a_congS a_congT ltr_congS idemS commT selS_or_id_annT LDS LDT nLCS nLKT) 
      end 
    end 
  | inr nLDT => inr (slt_llex_product_not_distributive_v2 LS S LT T eqLS eqS eqT argT wS wLS addS addT ltrS ltrT symS trnS refLS ltr_congS idemS LDS nLDT)    
  end 
| inr nLDS => inr (slt_llex_product_not_distributive_v1 LS S LT T eqS eqT argT wT wLT addS addT ltrS ltrT nLDS) 
end.     


Definition slt_llex_product_absorptive_decide
           (sabsS_d : slt_strictly_absorptive_decidable LS S eqS addS ltrS)
           (absS_d : slt_absorptive_decidable LS S eqS addS ltrS)
           (absT_d : slt_absorptive_decidable LT T eqT addT ltrT) :
  slt_absorptive_decidable
             (LS * LT)
             (S * T)
             (brel_product eqS eqT)
             (bop_llex argT eqS addS addT)
             (ltr_product ltrS ltrT) :=
let refS := A_eqv_reflexive _ _ eqvS in 
let symS := A_eqv_symmetric _ _ eqvS in
let trnS := A_eqv_transitive _ _ eqvS in
let refT := A_eqv_reflexive _ _ eqvT in 
match sabsS_d with
| inl sabsS  => inl(slt_llex_product_absorptive LS S LT T eqS eqT argT addS addT ltrS ltrT symS refT (inl sabsS))
| inr nsabsS =>
  match absS_d with
  | inl absS  =>
    match absT_d with
    | inl absT  => inl(slt_llex_product_absorptive LS S LT T eqS eqT argT addS addT ltrS ltrT symS refT (inr (absS, absT)))
    | inr nabsT => inr(slt_llex_product_not_absorptive_right LS S LT T eqS eqT argT addS addT ltrS ltrT symS trnS idemS (nsabsS, (absS, nabsT)))
    end 
  | inr nabsS => inr (slt_llex_product_not_absorptive_left LS S LT T eqS eqT argT wT wLT addS addT ltrS ltrT nabsS)
  end
end.     

Definition slt_llex_product_strictly_absorptive_decide
           (sabsS_d : slt_strictly_absorptive_decidable LS S eqS addS ltrS)
           (absS_d : slt_absorptive_decidable LS S eqS addS ltrS)
           (absT_d : slt_strictly_absorptive_decidable LT T eqT addT ltrT) :
  slt_strictly_absorptive_decidable
             (LS * LT)
             (S * T)
             (brel_product eqS eqT)
             (bop_llex argT eqS addS addT)
             (ltr_product ltrS ltrT) :=    
let refS := A_eqv_reflexive _ _ eqvS in 
let symS := A_eqv_symmetric _ _ eqvS in
let trnS := A_eqv_transitive _ _ eqvS in
let refT := A_eqv_reflexive _ _ eqvT in  
match sabsS_d with
| inl sabsS  => inl(slt_llex_product_strictly_absorptive LS S LT T eqS eqT argT addS addT ltrS ltrT symS refT (inl sabsS))
| inr nsabsS =>
  match absS_d with
  | inl absS  =>
    match absT_d with
    | inl absT  => inl(slt_llex_product_strictly_absorptive LS S LT T eqS eqT argT addS addT ltrS ltrT symS refT (inr (absS, absT)))
    | inr nabsT => inr(slt_llex_product_not_strictly_absorptive_right LS S LT T eqS eqT argT addS addT ltrS ltrT symS (nsabsS, (absS, nabsT)))
    end 
  | inr nabsS => inr (slt_llex_product_not_strictly_absorptive_left LS S LT T eqS eqT argT wT wLT addS addT ltrS ltrT nabsS)
  end
end.

Definition stl_llex_product_proofs
           (a_commT : bop_commutative T eqT addT) 
           (selS_or_id_annT : bop_selective S eqS addS + (bop_is_id T eqT addT argT * ltr_is_ann LT T eqT ltrT argT))
           (QS : left_transform_proofs LS S eqS eqLS ltrS)
           (QT : left_transform_proofs LT T eqT eqLT ltrT)           
           (PS : slt_proofs LS S eqS addS ltrS)
           (PT : slt_proofs LT T eqT addT ltrT) : 
  slt_proofs (LS * LT)
             (S * T)
             (brel_product eqS eqT)
             (bop_llex argT eqS addS addT)
             (ltr_product ltrS ltrT) :=
let DS_d := A_slt_distributive_d _ _ _ _ _ PS in
let DT_d := A_slt_distributive_d _ _ _ _ _ PT in
let CS_d := A_left_transform_left_cancellative_d _ _ _ _ _ QS in
let KT_d := A_left_transform_left_constant_d _ _ _ _ _ QT in
let asbS_d := A_slt_absorptive_d _ _ _ _ _ PS in
let asbT_d := A_slt_absorptive_d _ _ _ _ _ PT in
let sasbS_d := A_slt_strictly_absorptive_d _ _ _ _ _ PS in
let sasbT_d := A_slt_strictly_absorptive_d _ _ _ _ _ PT in
{|
  A_slt_distributive_d          := slt_llex_product_distributive_decide commT selS_or_id_annT DS_d DT_d CS_d KT_d 
; A_slt_absorptive_d            := slt_llex_product_absorptive_decide sasbS_d asbS_d asbT_d
; A_slt_strictly_absorptive_d   := slt_llex_product_strictly_absorptive_decide sasbS_d asbS_d sasbT_d
|}.

End Decide.     
*) 
Section Combinators.

End Combinators.   
  
End CAS.

Section Verify.

End Verify.   
  
