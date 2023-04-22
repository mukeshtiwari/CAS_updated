Require Import Coq.Bool.Bool.
Require Import CAS.coq.common.base.
Require Import CAS.coq.eqv.product.
Require Import CAS.coq.sg.llex.
Require Import CAS.coq.sg.cast_up. 
Require Import CAS.coq.theory.facts.
Require Import CAS.coq.theory.llte. 


Definition cef_sltr_llex_product_not_distributive  
      {S LS T LT : Type}
      (rS : brel S)
      (rT : brel T)
      (s1 : LS)
      (t1 : LT) 
      (s2 s3 : S)
      (t2 t3 : T)
      (addS : binary_op S) 
      (addT : binary_op T)
      (mulT : left_transform LT T) 
:= if (rS (addS s2 s3) s2) 
   then if rT (mulT t1 t2) (addT (mulT t1 t2) (mulT t1 t3))
        then ((s1, t1), ((s2, t3), (s3, t2)))
        else ((s1, t1), ((s2, t2), (s3, t3)))
   else if rT (mulT t1 t2) (addT (mulT t1 t2) (mulT t1 t3))
        then ((s1, t1), ((s2, t2), (s3, t3)))
        else ((s1, t1), ((s2, t3), (s3, t2))). 


Definition ltran_product : ∀ {S LS T LT: Type}, left_transform LS S → left_transform LT T → left_transform (LS * LT) (S * T)
:= λ {S LS T LT} U V x y,  
   match x, y with
    | (x1, x2), (y1, y2) => (U x1 y1, V x2 y2) 
   end.

Definition ltr_weak_congruence (L S : Type) (rS : brel S) (lt : left_transform L S) := 
   ∀ (l : L) (s1 s2 : S), rS s1 s2 = true -> rS (lt l s1) (lt l s2) = true.


Section Theory.

Variable S  : Type.
Variable LS : Type.   
Variable T  : Type.
Variable LT : Type. 
Variable rS : brel S. 
Variable rT : brel T.

Variable wS : S. 
Variable wT : T.

Variable wLS : LS. 
Variable wLT : LT.

Variable addS : binary_op S. 
Variable addT : binary_op T.

Variable mulS : left_transform LS S.
Variable mulT : left_transform LT T. 

Variable conS : brel_congruence S rS rS. 
Variable refS : brel_reflexive S rS.
Variable symS : brel_symmetric S rS.  
Variable tranS : brel_transitive S rS.


Variable conT : brel_congruence T rT rT. 
Variable refT : brel_reflexive T rT.
Variable symT : brel_symmetric T rT.  
Variable tranT : brel_transitive T rT.

Variable a_conS : bop_congruence S rS addS.
Variable a_conT : bop_congruence T rT addT.

Variable m_conS : ltr_weak_congruence LS S rS mulS.
Variable m_conT : ltr_weak_congruence LT T rT mulT. 

Notation "a =S b"  := (rS a b = true) (at level 15).
Notation "a =T b"  := (rT a b = true) (at level 15).
Notation "a +S b"  := (addS a b) (at level 15).
Notation "a +T b"  := (addT a b) (at level 15).
Notation "a |S> b"  := (mulS a b) (at level 15).
Notation "a |T> b"  := (mulT a b) (at level 15).

Notation "a <*> b" := (brel_product a b) (at level 15).
Notation "a [+] b" := (bop_llex rS a b) (at level 15).
Notation "a [*] b" := (ltran_product a b) (at level 15).

Print ltr_left_cancellative.

Lemma sltr_llex_product_distributive : 
      sltr_distributive S LS rS addS mulS → sltr_distributive T LT rT addT mulT → 
         ((ltr_left_cancellative LS S rS mulS) + (ltr_left_constant LT T rT mulT)) → 
             sltr_distributive (S * T) (LS * LT) (rS <*> rT) (addS [+] addT) (mulS [*] mulT). 
Proof. intros ldS ldT D [s1 t1] [s2 t2] [s3 t3].
       unfold ltran_product, bop_llex, brel_product. 
       apply andb_true_intro. split.  
       apply ldS. 
       unfold brel_llt. 
       unfold brel_conjunction. 
       unfold brel_llte. 
       unfold brel_complement. 
       case_eq(rS s2 s3); intro H1; 
       case_eq(rS s2 (s2 +S s3)); intro H2; 
       case_eq(rS (s1 |S> s2) (s1 |S> s3)); intro H3; 
       case_eq(rS (s1 |S> s2) ((s1 |S> s2) +S (s1 |S> s3))); intro H4; simpl. 
          apply ldT. 
          apply ldT. 
          assert(fact := m_conS s1 s2 s3 H1). rewrite fact in H3. discriminate. 
          assert(fact := m_conS s1 s2 s3 H1). rewrite fact in H3. discriminate. 
          apply ldT. 
          apply ldT. 
          assert(fact := m_conS s1 s2 s3 H1). rewrite fact in H3. discriminate. 
          assert(fact := m_conS s1 s2 s3 H1). rewrite fact in H3. discriminate. 
          destruct D as [C | K]. 
             apply C in H3. rewrite H3 in H1. discriminate. 
             assert (fact1 := ldT t1 t2 t3). 
             assert (fact2 := K t1 t2 (t2 +T t3)). (* t1 * t2 = t1 * (t2 + t3) *) 
             assert (fact3 := tranT _ _ _ fact2 fact1). assumption. 
          destruct D as [C | K]. 
             apply C in H3. rewrite H3 in H1. discriminate. 
             assert (fact1 := ldT t1 t2 t3). 
             assert (fact2 := K t1 t2 (t2 +T t3)). (* t1 * t2 = t1 * (t2 + t3) *) 
             assert (fact3 := tranT _ _ _ fact2 fact1). assumption. 
          apply refT. 

          assert (fact1 := ldS s1 s2 s3). 
          assert (fact2 := m_conS s1 _ _ H2).
          assert (fact3 := tranS _ _ _ fact2 fact1). 
          rewrite fact3 in H4. discriminate. 

          destruct D as [C | K]. 
             apply C in H3. rewrite H3 in H1. discriminate. 
             assert (fact1 := ldT t1 t2 t3). 
             assert (fact2 := K t1 t3 (t2 +T t3)). (* t1 * t3 = t1 * (t2 + t3) *) 
             assert (fact3 := tranT _ _ _ fact2 fact1). assumption. 
          destruct D as [C | K]. 
             apply C in H3. rewrite H3 in H1. discriminate. 
             assert (fact1 := ldT t1 t2 t3). 
             assert (fact2 := K t1 t3 (t2 +T t3)). (* t1 * t3 = t1 * (t2 + t3) *) 
             assert (fact3 := tranT _ _ _ fact2 fact1). assumption. 
          destruct D as [C | K]. 
             assert (fact1 := ldS s1 s2 s3). apply symS in fact1. 
             assert (fact2 := tranS _ _ _ H4 fact1). 
             apply C in fact2. 
             rewrite fact2 in H2. discriminate. 
             apply K. (* "direct" use of K *) 
          apply refT. 
Defined. 


Lemma sltr_llex_product_not_distributive_v1 : 
      sltr_not_distributive S LS rS addS mulS → sltr_not_distributive (S * T) (LS * LT) (rS <*> rT) (addS [+] addT) (mulS [*] mulT). 
Proof. intros [ [s1 [s2 s3 ] ] nld ]. exists ((s1, wLT), ((s2, wT), (s3, wT))); simpl. rewrite nld. simpl. reflexivity. Defined. 


Lemma sltr_llex_product_not_distributive_v2 : 
      sltr_not_distributive T LT rT addT mulT → sltr_not_distributive (S * T) (LS * LT) (rS <*> rT) (addS [+] addT) (mulS [*] mulT). 
Proof. intros [ [t1 [t2 t3 ] ] nld ].
       exists ((wLS, t1), ((wS, t2), (wS, t3))); simpl. 
       apply andb_is_false_right. right. 
       rewrite (refS wS). rewrite (refS (mulS wLS wS)). 
       assumption. 
Defined. 






(*  

   Assume 

   bop_not_cancellative : s1 * s2 = s1 * s3, s2 <> s3 
   bop_not_constant     : t1 * t2 <> t1 * t3 

   find ((s1, a), (s2, b), (s3, c)) that violates LD 

   case 1 :  s2 < s3 

      LHS : (s1, a) * ( (s2, b) + (s3, c))      = (s1, a) * (s2, b) = (s1 * s2, a * b) 
      RHS : (s1 * s2, a * b) + (s1 * s3, a * c) = (s1 * s2, (a * b) + (a * c)) 

      Need a * b <> (a * b) + (a * c) 
      
      case 1.1 : t1 * t2  = (t1 * t2) + (t1 * t3) 
           so    t1 * t3 <> (t1 * t2) + (t1 * t3) ={commT}=  (t1 * t3) + (t1 * t2)
           use   a    b                                       a     b     a    c 

      case 1.2 : t1 * t2  <> (t1 * t2) + (t1 * t3) 
           use   a    b       a     b     a    c 


   case 1 :  s3 < s2 

      LHS : (s1, a) * ( (s2, b) + (s3, c))      = (s1, a) * (s3, c) = (s1 * s2, a * c) 
      RHS : (s1 * s2, a * b) + (s1 * s3, a * c) = (s1 * s2, (a * b) + (a * c)) 

      Need a * c <> (a * b) + (a * c) 
      
      case 1.1 : t1 * t2  = (t1 * t2) + (t1 * t3) 
           so    t1 * t3 <> (t1 * t2) + (t1 * t3) 
           use   a    c      a     b     a    c 

      case 1.2 : t1 * t2  <> (t1 * t2) + (t1 * t3) ={commT}=  (t1 * t3) + (t1 * t2)
           use    a    c                                       a     b     a    c 

 *)

Lemma sltr_llex_product_not_distributive_v3 : 
      bop_selective S rS addS → bop_commutative S rS addS → bop_commutative T rT addT → 
      ltr_not_left_cancellative LS S rS mulS → ltr_not_left_constant LT T rT mulT → 
            sltr_not_distributive (S * T) (LS * LT) (rS <*> rT) (addS [+] addT) (mulS [*] mulT). 
Proof. intros selS commS commT  [ [s1 [s2 s3 ] ] [E N] ] [ [t1 [ t2 t3 ]] F].
exists(cef_sltr_llex_product_not_distributive rS rT s1 t1 s2 s3 t2 t3 addS addT mulT). 
unfold cef_sltr_llex_product_not_distributive. 
destruct(selS s2 s3) as [H | H]. 
   case_eq(rT (t1 |T> t2) ((t1 |T> t2) +T (t1 |T> t3))); intro J; simpl. 

      rewrite H. simpl. 
      apply andb_is_false_right. right.    
      rewrite N. compute. 
      apply symS in H. rewrite N, E, H.  
      assert (fact1 := commT (t1 |T> t2) (t1 |T> t3)). 
      assert (fact2 := tranT _ _ _ J fact1). 
      assert (fact3 := brel_transititivity_implies_dual _ _ tranT _ _ _ fact2 F). 
      apply (brel_symmetric_implies_dual _ _ symT). 
      assumption. 

      rewrite H; compute.           
      apply andb_is_false_right. right.    
      apply symS in H. rewrite N, E, H. 
      assumption. 

   assert (A : rS (s2 +S s3) s2 = false).  
       apply (brel_symmetric_implies_dual _ _ symS) in N.
       apply symS in H. 
       apply (brel_transititivity_implies_dual _ _ tranS _ _ _ H N). 

   case_eq(rT (t1 |T> t2) ((t1 |T> t2) +T (t1 |T> t3))); intro J; rewrite A; compute. 
      apply andb_is_false_right. right.  rewrite N.
      apply (brel_symmetric_implies_dual _ _ symS) in A.  rewrite A. 
      rewrite E. 
      assert (fact5 := brel_transititivity_implies_dual _ _ tranT _ _ _ J F). 
      apply (brel_symmetric_implies_dual _ _ symT). 
      assumption. 


      rewrite N. rewrite E. 
      apply (brel_symmetric_implies_dual _ _ symS) in A. rewrite A. 
      case_eq(rS (s1 |S> (s2 +S s3)) ((s1 |S> s2) +S (s1 |S> s3))); intro K; auto.    
      assert (fact1 := commT (t1 |T> t2) (t1 |T> t3)). 
      apply (brel_symmetric_implies_dual _ _ symT) in J.
      assert (fact2 := brel_transititivity_implies_dual _ _ tranT _ _ _ fact1 J). 
      apply (brel_symmetric_implies_dual _ _ symT).             
      assumption. 
Defined.  

(* absorption *) 

(* left left *) 

Lemma sltr_llex_product_left_left_absorptive : 
      sltr_absorptive S LS rS addS mulS → ((sltr_absorptive T LT rT addT mulT) + (ltr_anti_right LS S rS mulS)) → 
         sltr_absorptive (S * T) (LS * LT) (rS <*> rT) (addS [+] addT) (mulS [*] mulT). 
Proof. intros ldS [ldT | ar] [ls lt] [s t].
       simpl. 
       rewrite ldS. simpl. 
       case_eq(rS s (ls |S> s)); intro H. 
          apply ldT.
          compute. rewrite ldS. rewrite H. 
          apply refT. 
       compute.
       rewrite ldS. rewrite ldS.
       assert (F : rS s (ls |S> s) = false). admit. 
       rewrite F. apply refT. 
Admitted.

Lemma sltr_llex_product_not_absorptive_left : 
      sltr_not_absorptive S LS rS addS mulS → 
         sltr_not_absorptive (S * T) (LS * LT) (rS <*> rT) (addS [+] addT) (mulS [*] mulT). 
Proof. intros [ [ls s] P ]. exists ((ls, wLT), (s, wT)). simpl. rewrite P. simpl. reflexivity. Defined. 

Lemma sltr_llex_product_not_absorptive_right : 
      sltr_absorptive S LS rS addS mulS → sltr_not_absorptive T LT rT addT mulT → ltr_not_anti_right LS S rS mulS →
         sltr_not_absorptive (S * T) (LS * LT) (rS <*> rT) (addS [+] addT) (mulS [*] mulT). 
Proof. unfold ltr_not_anti_right. 
       intros laS [ [lt t] P ] [[ls s] Q]. exists ((ls, lt), (s, t)). compute. rewrite laS. apply symS in Q. rewrite Q. 
       exact P.
Defined. 


(* IDs ANNs 

In semiring (S + x)   
  id(+) =?= ann(x) 
  id(x) =?= ann(+)

Suppose 
  
   (S-> S, [+], [x]) where 

    (f [+] h)(s) = f(s) + h(s) 
    (f [x] h)(s) = f(s) * h(s) 

    id([+]) = lambda s.id(+) 
    ann([+]) = lambda s.ann(+) 

    id([x]) = lambda s.id(x) 
    ann([x]) = lambda s.ann(x) 

does it then become 

  id(+) =?= ann(x) : 
  exists l such that forall x (l |> s) is id(+) 

  id(x) =?= ann(+): 
  exists l such that forall x (l |> s) is ann(+)

=====================================================
  recall why id(x) = ann(+) is usful. No loops! 

   a x b <= a x c x b 

   (a x b) + (a x c x b)
         =LD= a x (b + c x b) 
         =RD= a x (id(x) + c) x b 
            = a x id(x) x b 
            = a x b 

   Can we use absorption instead? 

    s <= t x s 

    b <= c x b -> a x b <= a x c x b 

    where does monotonicity come from? 

    s <= t -> u x s <= u x t 

    s = s + t -> u x s = u x (s + t) =LD= (u x s) + (u x t)  

    btw, id(x) = ann(+) and RD gives absorption : 

    a = id(x) x a = (id(x) + b) x a = a + b x a


How does this carry over to transforms ? 
    Just need LD and ABS. 

=====================================================
  why is id(+) = ann(x) usful? 

  1) in def of I:  (I x A)(i,j) = sum_q I(i, q) x A(q, j)
                                = I(i, i) x A(i, j) + sum_{q<>i} I(i, q) x A(q, j) 
                                = A(i, j) + sum_{q<>i} id(+) x A(q, j)       
                                = A(i, j) + id(+)       
                                = A(i, j) 

  Is there an l such that id(+) = l |> s, for any s? 

*)

Lemma bops_llex_product_id_equals_ann : 
      bop_commutative S rS addS → bops_id_equals_ann S rS addS mulS → bops_id_equals_ann T rT addT mulT → 
         bops_id_equals_ann (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT). 
Proof. intros commS [iS [piS paS]] [iT [piT paT]]. 
       exists (iS, iT). split.
       apply bop_llex_is_id; auto.
       apply ltran_product_is_ann; auto.        
Defined. 



Lemma bops_product_llex_id_equals_ann : 
      bop_commutative S rS addS → bops_id_equals_ann S rS mulS addS  → 
      bops_id_equals_ann T rT mulT addT  → 
      bops_id_equals_ann (S * T) (rS <*> rT) (mulS [*] mulT) (addS [+] addT).
Proof. intros commS [iS [piS paS]] [iT [piT paT]]. 
       exists (iS, iT). split.
       apply ltran_product_is_id; auto.               
       apply bop_llex_is_ann; auto.
Defined. 

Lemma bops_llex_product_not_id_equals_ann_left : 
      bops_not_id_equals_ann S rS addS mulS → 
         bops_not_id_equals_ann (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT). 
Proof. unfold bops_not_id_equals_ann. 
       intros H [s t]. destruct (H s) as [ [s' [L | R]] | [s' [L | R]] ].
       left. exists (s', t). compute. rewrite L. left. reflexivity.
       left. exists (s', t). compute. rewrite R. right. reflexivity.   
       right. exists (s', t). compute. rewrite L. left. reflexivity.
       right. exists (s', t). compute. rewrite R. right. reflexivity.   
Defined. 

Lemma bops_llex_product_not_id_equals_ann_right : 
      bops_not_id_equals_ann T rT addT mulT → 
         bops_not_id_equals_ann (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT). 
Proof. unfold bops_not_id_equals_ann. 
       intros H [s t]. destruct (H t) as [ [t' [L | R]] | [t' [L | R]] ].
       left. exists (s, t'). compute. case_eq(rS (s +S s) s); intro J. rewrite refS. rewrite L. left; auto. left; auto. 
       left. exists (s, t'). compute. case_eq(rS (s +S s) s); intro J. rewrite refS. rewrite R. right; auto. left; auto. 
       right. exists (s, t'). compute. case_eq(rS (s |S> s) s); intro J. rewrite L. left; auto. left; auto. 
       right. exists (s, t'). compute. case_eq(rS (s |S> s) s); intro J. rewrite R. right; auto. left; auto. 
Defined. 


Lemma bops_product_llex_not_id_equals_ann_left : 
      bops_not_id_equals_ann S rS mulS addS → 
         bops_not_id_equals_ann (S * T) (rS <*> rT) (mulS [*] mulT) (addS [+] addT). 
Proof. unfold bops_not_id_equals_ann. intros H [s t]. 
       destruct (H s) as [ [s' [L| R] ] | [s' [L | R]] ].
       left. exists (s', t). compute. rewrite L. left. reflexivity.
       left. exists (s', t). compute. rewrite R. right. reflexivity.
       right. exists (s', t). compute. rewrite L. left. reflexivity.
       right. exists (s', t). compute. rewrite R. right. reflexivity.              
Defined. 

Lemma bops_product_llex_not_id_equals_ann_right :
      bop_idempotent S rS addS → (* NB *) 
      bops_not_id_equals_ann T rT mulT addT → 
         bops_not_id_equals_ann (S * T) (rS <*> rT) (mulS [*] mulT) (addS [+] addT). 
Proof. unfold bops_not_id_equals_ann. intros idemS H [s t]. 
       destruct (H t) as [ [t' [L| R] ] | [t' [L | R]] ].
       left. exists (s, t'). compute. rewrite L. case(rS (s |S> s) s); left; reflexivity.
       left. exists (s, t'). compute. rewrite R. case(rS (s |S> s) s); right; reflexivity.
       right. exists (s, t'). compute. rewrite (idemS s). rewrite refS. rewrite L. left. reflexivity.
       right. exists (s, t'). compute. rewrite (idemS s). rewrite refS. rewrite R. right. reflexivity.
Defined. 








(* Decide *) 

Definition bops_llex_product_left_distributive_decide : 
      bop_selective S rS addS  →      (* NB *) 
      bop_commutative S rS addS  →    (* NB *) 
      bop_commutative T rT addT  →    (* NB *) 
      bop_left_cancellative_decidable S rS mulS  → 
      bop_left_constant_decidable T rT mulT → 
      bop_left_distributive_decidable S rS addS mulS → 
      bop_left_distributive_decidable T rT addT mulT → 
         bop_left_distributive_decidable (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT)
:= λ selS commS commT lcS_d lkT_d ldS_d ldT_d, 
match ldS_d with 
|inl ldS =>
   match ldT_d with 
   |inl ldT =>
       match lcS_d with 
       | inl lcS => inl _ (bop_llex_product_left_distributive ldS ldT (inl _ lcS))
       | inr not_lcS => 
            match lkT_d with 
            | inl lkT => inl _ (bop_llex_product_left_distributive ldS ldT (inr _ lkT))
            | inr not_lkT => inr _ (bop_llex_product_not_left_distributive_v3 selS commS commT not_lcS not_lkT)
                                     
            end 
       end 
   |inr not_ldT => inr _ (bop_llex_product_not_left_distributive_v2 not_ldT)
   end 
|inr not_ldS => inr _ (bop_llex_product_not_left_distributive_v1 not_ldS ) 
end. 


(*
 LA(S) -> 
          LA(T) -> (LA(T) | nQ) -> LA(lex, product) 
          nLA(T) -> 
             nQ  -> (LA(T) | nQ) -> LA(lex, product) 
              Q -> (nLA(T) & Q) -> nLA(lex, product) 
nLA(S) -> nLA(lex, product) 

*)
Definition bops_llex_product_left_left_absorptive_decide : 
      bops_left_left_absorptive_decidable S rS addS mulS → 
      bops_left_left_absorptive_decidable T rT addT mulT → 
      bop_anti_left_decidable S rS mulS → 
         bops_left_left_absorptive_decidable (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT) 
:= λ laS_d laT_d antilS_d, 
match laS_d with 
|inl laS =>
   match laT_d with 
   |inl laT =>  inl _ (bops_llex_product_left_left_absorptive laS (inl _ laT))
   |inr not_laT  => 
       match antilS_d with 
       | inl antilS => inl _ (bops_llex_product_left_left_absorptive laS (inr _ antilS))
       | inr not_antilS => inr _ (bops_llex_product_not_left_left_absorptive_right laS not_laT not_antilS)
       end 
   end 
|inr not_laS => inr _ (bops_llex_product_not_left_left_absorptive_left not_laS) 
end. 

Definition bops_llex_product_left_right_absorptive_decide : 
      bops_left_right_absorptive_decidable S rS addS mulS → 
      bops_left_right_absorptive_decidable T rT addT mulT → 
      bop_anti_right_decidable S rS mulS → 
         bops_left_right_absorptive_decidable (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT) 
:= λ laS_d laT_d antilS_d, 
match laS_d with 
|inl laS =>
   match laT_d with 
   |inl laT =>  inl _ (bops_llex_product_left_right_absorptive laS (inl _ laT))
   |inr not_laT  => 
       match antilS_d with 
       | inl antilS => inl _ (bops_llex_product_left_right_absorptive laS (inr _ antilS))
       | inr not_antilS => inr _ (bops_llex_product_not_left_right_absorptive_right laS not_laT not_antilS )
       end 
   end 
|inr not_laS => inr _ (bops_llex_product_not_left_right_absorptive_left not_laS ) 
end. 

Definition bops_llex_product_right_left_absorptive_decide : 
      bops_right_left_absorptive_decidable S rS addS mulS → 
      bops_right_left_absorptive_decidable T rT addT mulT → 
      bop_anti_left_decidable S rS mulS → 
         bops_right_left_absorptive_decidable (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT) 
:= λ laS_d laT_d antilS_d, 
match laS_d with 
|inl laS =>
   match laT_d with 
   |inl laT =>  inl _ (bops_llex_product_right_left_absorptive laS (inl _ laT))
   |inr not_laT  => 
       match antilS_d with 
       | inl antilS => inl _ (bops_llex_product_right_left_absorptive laS (inr _ antilS))
       | inr not_antilS => inr _ (bops_llex_product_not_right_left_absorptive_right laS not_laT not_antilS )
       end 
   end 
|inr not_laS => inr _ (bops_llex_product_not_right_left_absorptive_left not_laS ) 
end. 

Definition bops_llex_product_right_right_absorptive_decide : 
      bops_right_right_absorptive_decidable S rS addS mulS → 
      bops_right_right_absorptive_decidable T rT addT mulT → 
      bop_anti_right_decidable S rS mulS → 
         bops_right_right_absorptive_decidable (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT) 
:= λ laS_d laT_d antilS_d, 
match laS_d with 
|inl laS =>
   match laT_d with 
   |inl laT =>  inl _ (bops_llex_product_right_right_absorptive laS (inl _ laT))
   |inr not_laT  => 
       match antilS_d with 
       | inl antilS => inl _ (bops_llex_product_right_right_absorptive laS (inr _ antilS))
       | inr not_antilS => inr _ (bops_llex_product_not_right_right_absorptive_right laS not_laT not_antilS )
       end 
   end 
|inr not_laS => inr _ (bops_llex_product_not_right_right_absorptive_left not_laS ) 
end.


Definition bops_llex_product_id_equals_ann_decide : 
      bop_commutative S rS addS  →
      bops_id_equals_ann_decidable S rS addS mulS → 
      bops_id_equals_ann_decidable T rT addT mulT →  
        bops_id_equals_ann_decidable (S * T) (rS <*> rT) (addS [+] addT) (mulS [*] mulT)
 := λ commS dS dT,  
   match dS with 
   | inl ieaS => 
     match dT with 
     | inl ieaT  => inl _ (bops_llex_product_id_equals_ann commS ieaS ieaT)
     | inr nieaT => inr _ (bops_llex_product_not_id_equals_ann_right nieaT)
     end 
   | inr nieaS   => inr _ (bops_llex_product_not_id_equals_ann_left nieaS)
   end. 


Definition bops_product_llex_id_equals_ann_decide : 
  bop_commutative S rS addS  →
  bop_idempotent S rS addS  →
  bops_id_equals_ann_decidable S rS mulS addS  → 
  bops_id_equals_ann_decidable T rT mulT addT  →  
        bops_id_equals_ann_decidable (S * T) (rS <*> rT) (mulS [*] mulT) (addS [+] addT) 
:= λ commS idemS dS dT,  
   match dS with 
   | inl ieaS => 
     match dT with 
     | inl ieaT  => inl _ (bops_product_llex_id_equals_ann commS ieaS ieaT)
     | inr nieaT => inr _ (bops_product_llex_not_id_equals_ann_right idemS nieaT)
     end 
   | inr nieaS   => inr _ (bops_product_llex_not_id_equals_ann_left nieaS)
   end. 
End Theory.

Section ACAS.


Definition bs_proofs_llex : 
  ∀ (S T: Type) (rS : brel S) (rT : brel T) (plusS timesS : binary_op S) (plusT timesT : binary_op T) (s : S) (t : T), 
     eqv_proofs S rS -> 
     eqv_proofs T rT -> 

     sg_CS_proofs S rS plusS ->          (*NB*) 
     sg_proofs S rS timesS ->            
     sg_C_proofs T rT plusT ->           (*NB*) 
     sg_proofs T rT timesT ->            

     bs_proofs S rS plusS timesS -> 
     bs_proofs T rT plusT timesT -> 

        bs_proofs (S * T) 
           (brel_product rS rT) 
           (bop_llex rS plusS plusT)
           (ltran_product timesS timesT)

:= λ S T rS rT plusS timesS plusT timesT s t eqvS eqvT sg_CS_S sg_S sg_C_T sg_T pS pT,
let refS   := A_eqv_reflexive S rS eqvS in 
let symS   := A_eqv_symmetric S rS eqvS in 
let transS := A_eqv_transitive S rS eqvS in 
let refT   := A_eqv_reflexive T rT eqvT in 
let symT   := A_eqv_symmetric T rT eqvT in 
let transT := A_eqv_transitive T rT eqvT in 
let selS := A_sg_CS_selective S rS plusS sg_CS_S in 
let comS := A_sg_CS_commutative S rS plusS sg_CS_S in 
let comT := A_sg_C_commutative T rT plusT sg_C_T in   
let c_timesS := A_sg_congruence S rS timesS sg_S in 
{|
  A_bs_left_distributive_d    := 
   bops_llex_product_left_distributive_decide S T rS rT s t plusS timesS plusT timesT refS symS transS refT symT transT c_timesS selS comS comT
     (A_sg_left_cancel_d S rS timesS  sg_S) 
     (A_sg_left_constant_d T rT timesT sg_T)
     (A_bs_left_distributive_d S rS plusS timesS pS)
     (A_bs_left_distributive_d T rT plusT timesT pT)
; A_bs_right_distributive_d   := 
   bops_llex_product_right_distributive_decide S T rS rT s t plusS timesS plusT timesT refS symS transS refT symT transT c_timesS selS comS comT
     (A_sg_right_cancel_d S rS timesS  sg_S) 
     (A_sg_right_constant_d T rT timesT sg_T)
     (A_bs_right_distributive_d S rS plusS timesS pS)
     (A_bs_right_distributive_d T rT plusT timesT pT)
; A_bs_plus_id_is_times_ann_d :=  
    bops_llex_product_id_equals_ann_decide S T rS rT plusS timesS plusT timesT refS symS transS refT comS 
     (A_bs_plus_id_is_times_ann_d S rS plusS timesS pS)
     (A_bs_plus_id_is_times_ann_d T rT plusT timesT pT)
; A_bs_times_id_is_plus_ann_d :=  
   bops_product_llex_id_equals_ann_decide S T rS rT plusS timesS plusT timesT refS symS transS refT comS 
   (bop_selective_implies_idempotent S rS plusS (A_sg_CS_selective S rS plusS sg_CS_S))
   (A_bs_times_id_is_plus_ann_d S rS plusS timesS pS)
   (A_bs_times_id_is_plus_ann_d T rT plusT timesT pT)
; A_bs_left_left_absorptive_d      := 
    bops_llex_product_left_left_absorptive_decide S T rS rT t plusS timesS plusT timesT refT
    (A_bs_left_left_absorptive_d S rS plusS timesS pS)
    (A_bs_left_left_absorptive_d T rT plusT timesT pT)
    (A_sg_anti_left_d S rS timesS sg_S)
; A_bs_left_right_absorptive_d      := 
    bops_llex_product_left_right_absorptive_decide S T rS rT t plusS timesS plusT timesT refT 
    (A_bs_left_right_absorptive_d S rS plusS timesS pS)
    (A_bs_left_right_absorptive_d T rT plusT timesT pT)
    (A_sg_anti_right_d S rS timesS sg_S)
; A_bs_right_left_absorptive_d      := 
    bops_llex_product_right_left_absorptive_decide S T rS rT t plusS timesS plusT timesT symS transS refT 
       (A_bs_right_left_absorptive_d S rS plusS timesS pS)
       (A_bs_right_left_absorptive_d T rT plusT timesT pT)
       (A_sg_anti_left_d S rS timesS sg_S)
; A_bs_right_right_absorptive_d      := 
    bops_llex_product_right_right_absorptive_decide S T rS rT t plusS timesS plusT timesT symS transS refT
       (A_bs_right_right_absorptive_d S rS plusS timesS pS)
       (A_bs_right_right_absorptive_d T rT plusT timesT pT)
       (A_sg_anti_right_d S rS timesS sg_S)
|}. 


Definition A_bs_C_llex_product : ∀ (S T : Type),  A_bs_CS S -> A_bs_C T -> A_bs_C (S * T) 
:= λ S T bsS bsT,
let eqvS   := A_bs_CS_eqv S bsS   in
let eqvT   := A_bs_C_eqv T bsT   in
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
let plusS  := A_bs_CS_plus S bsS  in 
let plusT  := A_bs_C_plus T bsT  in
let timesS := A_bs_CS_times S bsS in 
let timesT := A_bs_C_times T bsT in 
{| 
     A_bs_C_eqv         := A_eqv_product S T eqvS eqvT 
   ; A_bs_C_plus        := bop_llex rS plusS plusT 
   ; A_bs_C_times       := ltran_product timesS timesT 
   ; A_bs_C_plus_proofs := sg_C_proofs_llex S T rS rT plusS plusT s f t g Pf Pg peqvS peqvT 
                           (A_bs_CS_plus_proofs S bsS) 
                           (A_bs_C_plus_proofs T bsT) 
   ; A_bs_C_times_proofs := sg_proofs_product S T rS rT timesS timesT s f t g Pf Pg peqvS peqvT 
                           (A_bs_CS_times_proofs S bsS)
                           (A_bs_C_times_proofs T bsT)
   ; A_bs_C_proofs    := bs_proofs_llex S T rS rT plusS timesS plusT timesT s t peqvS peqvT 
                           (A_bs_CS_plus_proofs S bsS) 
                           (A_bs_CS_times_proofs S bsS) 
                           (A_bs_C_plus_proofs T bsT) 
                           (A_bs_C_times_proofs T bsT) 
                           (A_bs_CS_proofs S bsS) 
                           (A_bs_C_proofs T bsT)
   ; A_bs_C_plus_ast   := Ast_bop_llex (A_bs_CS_plus_ast S bsS, A_bs_C_plus_ast T bsT)
   ; A_bs_C_times_ast  := Ast_ltran_product (A_bs_CS_times_ast S bsS, A_bs_C_times_ast T bsT)                                       
   ; A_bs_C_ast        := Ast_bs_C_llex (A_bs_CS_ast S bsS, A_bs_C_ast T bsT)
|}. 



Definition A_bs_CS_llex_product : ∀ (S T : Type),  A_bs_CS S -> A_bs_CS T -> A_bs_CS (S * T) 
:= λ S T bsS bsT,
let eqvS   := A_bs_CS_eqv S bsS   in
let eqvT   := A_bs_CS_eqv T bsT   in
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
let plusS  := A_bs_CS_plus S bsS  in 
let plusT  := A_bs_CS_plus T bsT  in
let timesS := A_bs_CS_times S bsS in 
let timesT := A_bs_CS_times T bsT in 
{| 
     A_bs_CS_eqv         := A_eqv_product S T eqvS eqvT 
   ; A_bs_CS_plus        := bop_llex rS plusS plusT 
   ; A_bs_CS_times       := ltran_product timesS timesT 
   ; A_bs_CS_plus_proofs := sg_CS_proofs_llex S T rS rT plusS plusT peqvS peqvT 
                           (A_bs_CS_plus_proofs S bsS) 
                           (A_bs_CS_plus_proofs T bsT) 
   ; A_bs_CS_times_proofs := sg_proofs_product S T rS rT timesS timesT s f t g Pf Pg peqvS peqvT 
                           (A_bs_CS_times_proofs S bsS)
                           (A_bs_CS_times_proofs T bsT)
   ; A_bs_CS_proofs    := bs_proofs_llex S T rS rT plusS timesS plusT timesT s t peqvS peqvT 
                           (A_bs_CS_plus_proofs S bsS) 
                           (A_bs_CS_times_proofs S bsS) 
                           (A_sg_C_proofs_from_sg_CS_proofs T _ _ t g Pg (A_eqv_proofs T (A_bs_CS_eqv T bsT)) (A_bs_CS_plus_proofs T bsT))
                           (A_bs_CS_times_proofs T bsT)
                           (A_bs_CS_proofs S bsS) 
                           (A_bs_CS_proofs T bsT)
   ; A_bs_CS_plus_ast   := Ast_bop_llex (A_bs_CS_plus_ast S bsS, A_bs_CS_plus_ast T bsT)
   ; A_bs_CS_times_ast  := Ast_ltran_product (A_bs_CS_times_ast S bsS, A_bs_CS_times_ast T bsT)            
   ; A_bs_CS_ast        := Ast_bs_CS_llex (A_bs_CS_ast S bsS, A_bs_CS_ast T bsT)
|}. 

End ACAS.

Section CAS.


(* 

C = Constructor 
P = Property 

  1) C_P_check 
  2) C_P_assert 
  3) C_not_P_assert 

*) 


Definition bops_llex_product_left_distributive_check 
     {S T : Type}
     (rS : brel S) 
     (rT : brel T) 
     (addS : binary_op S) 
     (addT mulT : binary_op T)
     (s : S) 
     (t : T) 
     (lcS_d : check_left_cancellative (S := S)) 
     (lkT_d : check_left_constant (S := T)) 
     (ldS_d : check_left_distributive (S := S)) 
     (ldT_d : check_left_distributive (S := T)) : 
     check_left_distributive (S := (S * T)) 
:= 
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
                     (cef_llex_product_not_left_distributive rS rT s1 s2 s3 t1 t2 t3
                         addS addT mulT) 
            end 
       end 
   | Certify_Not_Left_Distributive (t1, (t2, t3)) => 
          Certify_Not_Left_Distributive  ((s, t1), ((s, t2), (s, t3))) 
   end 
| Certify_Not_Left_Distributive (s1, (s2, s3)) => 
        Certify_Not_Left_Distributive  ((s1, t), ((s2, t), (s3, t))) 
end.

Definition bops_llex_product_right_distributive_check 
     {S T : Type}
     (rS : brel S) 
     (rT : brel T) 
     (addS : binary_op S) 
     (addT mulT : binary_op T)
     (s : S) 
     (t : T) 
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
                     (cef_llex_product_not_right_distributive rS rT s1 s2 s3 t1 t2 t3
                         addS addT mulT) 

            end 
       end 
   | Certify_Not_Right_Distributive (t1, (t2, t3)) => 
          Certify_Not_Right_Distributive  ((s, t1), ((s, t2), (s, t3))) 
   end 
| Certify_Not_Right_Distributive (s1, (s2, s3)) => 
        Certify_Not_Right_Distributive  ((s1, t), ((s2, t), (s3, t))) 
end.


(* these are the same as for product *) 
Definition bops_llex_product_plus_id_is_times_ann_check : 
   ∀ {S T : Type},  
     check_plus_id_equals_times_ann (S := S) -> 
     check_plus_id_equals_times_ann (S := T) -> 
     check_plus_id_equals_times_ann (S := (S * T)) 
:= λ {S T} dS dT,  
   match dS with 
   | Certify_Plus_Id_Equals_Times_Ann => 
     match dT with 
     | Certify_Plus_Id_Equals_Times_Ann => Certify_Plus_Id_Equals_Times_Ann  
     | Certify_Not_Plus_Id_Equals_Times_Ann => 
          Certify_Not_Plus_Id_Equals_Times_Ann  
     end 
   | Certify_Not_Plus_Id_Equals_Times_Ann => 
        Certify_Not_Plus_Id_Equals_Times_Ann 
   end. 

Definition bops_llex_product_times_id_equals_plus_ann_check : 
   ∀ {S T : Type},  
     check_times_id_equals_plus_ann (S := S) -> 
     check_times_id_equals_plus_ann (S := T) -> 
     check_times_id_equals_plus_ann (S := (S * T)) 
:= λ {S T} dS dT,  
   match dS with 
   | Certify_Times_Id_Equals_Plus_Ann => 
     match dT with 
     | Certify_Times_Id_Equals_Plus_Ann => Certify_Times_Id_Equals_Plus_Ann  
     | Certify_Not_Times_Id_Equals_Plus_Ann => 
          Certify_Not_Times_Id_Equals_Plus_Ann  
     end 
   | Certify_Not_Times_Id_Equals_Plus_Ann => 
        Certify_Not_Times_Id_Equals_Plus_Ann 
   end. 



Definition bops_llex_product_left_left_absorptive_check : 
   ∀ {S T : Type} (t : T),  
     check_left_left_absorptive (S := S) -> 
     check_left_left_absorptive (S := T) -> 
     check_anti_left (S := S) -> 
     check_left_left_absorptive (S := (S * T)) 
:= λ {S T} t dS dT alS,  
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
        Certify_Not_Left_Left_Absorptive  ((s1, t), (s2, t))
end. 


Definition bops_llex_product_left_right_absorptive_check : 
   ∀ {S T : Type} (t : T),  
     check_left_right_absorptive (S := S) -> 
     check_left_right_absorptive (S := T) -> 
     check_anti_right (S := S) -> 
     check_left_right_absorptive (S := (S * T)) 
:= λ {S T} t dS dT alS,  
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
        Certify_Not_Left_Right_Absorptive  ((s1, t), (s2, t))
end. 



Definition bops_llex_product_right_left_absorptive_check : 
   ∀ {S T : Type} (t : T),  
     check_right_left_absorptive (S := S) -> 
     check_right_left_absorptive (S := T) -> 
     check_anti_left (S := S) -> 
     check_right_left_absorptive (S := (S * T)) 
:= λ {S T} t dS dT alS,  
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
        Certify_Not_Right_Left_Absorptive  ((s1, t), (s2, t))
end. 


Definition bops_llex_product_right_right_absorptive_check : 
   ∀ {S T : Type} (t : T),  
     check_right_right_absorptive (S := S) -> 
     check_right_right_absorptive (S := T) -> 
     check_anti_right (S := S) -> 
     check_right_right_absorptive (S := (S * T)) 
:= λ {S T} t dS dT alS,  
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
        Certify_Not_Right_Right_Absorptive  ((s1, t), (s2, t))
end. 




Definition bs_certs_llex_product : 
  ∀ {S T: Type}
     (rS : brel S) 
     (rT : brel T) 
     (addS : binary_op S) 
     (addT mulT : binary_op T),
    S -> 
    T -> 
    sg_certificates (S := S)  → 
    sg_certificates (S := T) → 
    bs_certificates (S := S) -> 
    bs_certificates (S := T) -> bs_certificates (S := (S * T)) 
:= λ {S T} rS rT addS addT mulT s t sg_timesS sg_timesT bsS bsT, 
{|
  bs_left_distributive_d     := bops_llex_product_left_distributive_check 
                                     rS rT addS addT mulT s t
                                     (sg_left_cancel_d sg_timesS)
                                     (sg_left_constant_d sg_timesT) 
                                     (bs_left_distributive_d bsS)
                                     (bs_left_distributive_d bsT)
; bs_right_distributive_d    := bops_llex_product_right_distributive_check 
                                     rS rT addS addT mulT s t
                                     (sg_right_cancel_d sg_timesS)
                                     (sg_right_constant_d sg_timesT) 
                                     (bs_right_distributive_d bsS)
                                     (bs_right_distributive_d bsT)
; bs_plus_id_is_times_ann_d := bops_llex_product_plus_id_is_times_ann_check 
                                     (bs_plus_id_is_times_ann_d bsS)
                                     (bs_plus_id_is_times_ann_d bsT)
; bs_times_id_is_plus_ann_d := bops_llex_product_times_id_equals_plus_ann_check 
                                     (bs_times_id_is_plus_ann_d bsS)
                                     (bs_times_id_is_plus_ann_d bsT)
; bs_left_left_absorptive_d := bops_llex_product_left_left_absorptive_check t 
                                     (bs_left_left_absorptive_d bsS)
                                     (bs_left_left_absorptive_d bsT) 
                                     (sg_anti_left_d sg_timesS) 
; bs_left_right_absorptive_d := bops_llex_product_left_right_absorptive_check t 
                                     (bs_left_right_absorptive_d bsS)
                                     (bs_left_right_absorptive_d bsT) 
                                     (sg_anti_right_d sg_timesS)
; bs_right_left_absorptive_d := bops_llex_product_right_left_absorptive_check t 
                                     (bs_right_left_absorptive_d bsS)
                                     (bs_right_left_absorptive_d bsT) 
                                     (sg_anti_left_d sg_timesS)  
; bs_right_right_absorptive_d   := bops_llex_product_right_right_absorptive_check t
                                     (bs_right_right_absorptive_d bsS)
                                     (bs_right_right_absorptive_d bsT)
                                     (sg_anti_right_d sg_timesS) 

|}
.


Definition bs_C_llex_product : ∀ {S T : Type},  bs_CS (S := S) -> bs_C (S := T) -> bs_C (S := (S * T)) 
:= λ {S T} bsS bsT, 
{| 
     bs_C_eqv        := eqv_product  
                           (bs_CS_eqv bsS) 
                           (bs_C_eqv  bsT) 
   ; bs_C_plus       := bop_llex 
                           (eqv_eq (bs_CS_eqv bsS)) 
                           (bs_CS_plus bsS) 
                           (bs_C_plus bsT) 
   ; bs_C_times       := ltran_product 
                           (bs_CS_times bsS) 
                           (bs_C_times bsT) 
   ; bs_C_plus_certs := sg_C_certs_llex 
                           (eqv_eq (bs_CS_eqv bsS)) 
                           (bs_CS_plus bsS) 
                           (eqv_witness (bs_CS_eqv bsS)) (eqv_new (bs_CS_eqv bsS)) 
                           (eqv_witness (bs_C_eqv bsT)) (eqv_new (bs_C_eqv bsT)) 
                           (bs_CS_plus_certs bsS) 
                           (bs_C_plus_certs bsT) 
   ; bs_C_times_certs := sg_certs_product 
                           (eqv_witness (bs_CS_eqv bsS)) 
                           (eqv_witness (bs_C_eqv bsT)) 
                           (bs_CS_times_certs bsS)
                           (bs_C_times_certs bsT)
   ; bs_C_certs    := bs_certs_llex_product 
                           (eqv_eq (bs_CS_eqv bsS)) 
                           (eqv_eq (bs_C_eqv bsT)) 
                           (bs_CS_plus bsS)
                           (bs_C_plus bsT) 
                           (bs_C_times bsT)  
                           (eqv_witness (bs_CS_eqv bsS)) 
                           (eqv_witness (bs_C_eqv bsT)) 
                           (bs_CS_times_certs bsS) 
                           (bs_C_times_certs bsT) 
                           (bs_CS_certs bsS) 
                           (bs_C_certs bsT)
   ; bs_C_plus_ast   := Ast_bop_llex (bs_CS_plus_ast bsS, bs_C_plus_ast bsT)
   ; bs_C_times_ast  := Ast_ltran_product (bs_CS_times_ast bsS, bs_C_times_ast bsT)                                       
   ; bs_C_ast        := Ast_bs_C_llex (bs_CS_ast bsS, bs_C_ast bsT)
|}. 

Definition bs_CS_llex_product : ∀ {S T : Type},  bs_CS (S := S) -> bs_CS (S := T) -> bs_CS (S := (S * T)) 
:= λ {S T} bsS bsT, 
{| 
     bs_CS_eqv        := eqv_product  
                           (bs_CS_eqv bsS) 
                           (bs_CS_eqv bsT) 
   ; bs_CS_plus       := bop_llex 
                           (eqv_eq (bs_CS_eqv bsS)) 
                           (bs_CS_plus bsS) 
                           (bs_CS_plus bsT) 
   ; bs_CS_times       := ltran_product 
                           (bs_CS_times bsS) 
                           (bs_CS_times bsT) 
   ; bs_CS_plus_certs := sg_CS_certs_llex 
                           (eqv_eq (bs_CS_eqv bsS)) 
                           (bs_CS_plus bsS) 
                           (bs_CS_plus_certs bsS) 
                           (bs_CS_plus_certs bsT) 
   ; bs_CS_times_certs := sg_certs_product 
                           (eqv_witness (bs_CS_eqv bsS)) 
                           (eqv_witness (bs_CS_eqv bsT)) 
                           (bs_CS_times_certs bsS)
                           (bs_CS_times_certs bsT)
   ; bs_CS_certs    := bs_certs_llex_product 
                           (eqv_eq (bs_CS_eqv bsS)) 
                           (eqv_eq (bs_CS_eqv bsT)) 
                           (bs_CS_plus bsS)
                           (bs_CS_plus bsT) 
                           (bs_CS_times bsT)  
                           (eqv_witness (bs_CS_eqv bsS)) 
                           (eqv_witness (bs_CS_eqv bsT)) 
                           (bs_CS_times_certs bsS) 
                           (bs_CS_times_certs bsT) 
                           (bs_CS_certs bsS) 
                           (bs_CS_certs bsT)
   ; bs_CS_plus_ast   := Ast_bop_llex (bs_CS_plus_ast bsS, bs_CS_plus_ast bsT)
   ; bs_CS_times_ast  := Ast_ltran_product (bs_CS_times_ast bsS, bs_CS_times_ast bsT)                                                                  
   ; bs_CS_ast        := Ast_bs_CS_llex (bs_CS_ast bsS, bs_CS_ast bsT)
|}. 

  

End CAS.

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

Lemma bop_llex_product_left_distributive_check_correct : 
  ∀ (rfS : brel_reflexive S rS)
     (syS : brel_symmetric S rS)
     (tnS : brel_transitive S rS)
     (rfT : brel_reflexive T rT)     
     (syT : brel_symmetric T rT)
     (tnT : brel_transitive T rT)
     (cong_timesS : bop_congruence S rS timesS)
     (sel_plusS : bop_selective S rS plusS)
     (comm_plusS : bop_commutative S rS plusS)
     (comm_plusT : bop_commutative T rT plusT)
     (qS_d : bop_left_cancellative_decidable S rS timesS) 
     (qT_d : bop_left_constant_decidable T rT timesT)
     (pS_d : bop_left_distributive_decidable S rS plusS timesS) 
     (pT_d : bop_left_distributive_decidable T rT plusT timesT), 
    bops_llex_product_left_distributive_check rS rT plusS plusT timesT wS wT
       (p2c_left_cancel_check S rS timesS qS_d)
       (p2c_left_constant_check T rT timesT qT_d)                                                                                            
       (p2c_left_distributive S rS plusS timesS pS_d)
       (p2c_left_distributive T rT plusT timesT pT_d)
     = 
     @p2c_left_distributive (S * T) 
        (brel_product rS rT)
        (bop_llex rS plusS plusT)
        (ltran_product timesS timesT)
        (bops_llex_product_left_distributive_decide S T rS rT wS wT plusS timesS plusT timesT rfS syS tnS rfT syT tnT
                                                    cong_timesS sel_plusS comm_plusS comm_plusT qS_d qT_d pS_d pT_d).
Proof. intros rfS syS tnS rfT syT tnT ct sp cpS cpT 
              [lcS | [[u1 [u2 u3]] [L R]] ]
              [lkS | [[v1 [v2 v3]] P] ]
              [ ldS | [ [s1 [s2 s3]] nldS] ]
              [ ldT | [ [t1 [t2 t3]] nldT] ];
         compute; reflexivity. Qed. 

Lemma bop_llex_product_right_distributive_check_correct : 
  ∀ (rfS : brel_reflexive S rS)
     (syS : brel_symmetric S rS)
     (tnS : brel_transitive S rS)
     (rfT : brel_reflexive T rT)     
     (syT : brel_symmetric T rT)
     (tnT : brel_transitive T rT)
     (cong_timesS : bop_congruence S rS timesS)
     (sel_plusS : bop_selective S rS plusS)
     (comm_plusS : bop_commutative S rS plusS)
     (comm_plusT : bop_commutative T rT plusT)
     (qS_d : bop_right_cancellative_decidable S rS timesS) 
     (qT_d : bop_right_constant_decidable T rT timesT)
     (pS_d : bop_right_distributive_decidable S rS plusS timesS) 
     (pT_d : bop_right_distributive_decidable T rT plusT timesT), 
    bops_llex_product_right_distributive_check rS rT plusS plusT timesT wS wT
       (p2c_right_cancel_check S rS timesS qS_d)
       (p2c_right_constant_check T rT timesT qT_d)                                                                                            
       (p2c_right_distributive S rS plusS timesS pS_d)
       (p2c_right_distributive T rT plusT timesT pT_d)
     = 
     @p2c_right_distributive (S * T) 
        (brel_product rS rT)
        (bop_llex rS plusS plusT)
        (ltran_product timesS timesT)
        (bops_llex_product_right_distributive_decide S T rS rT wS wT plusS timesS plusT timesT rfS syS tnS rfT syT tnT
                                                     cong_timesS sel_plusS comm_plusS comm_plusT qS_d qT_d pS_d pT_d).
Proof. intros rfS syS tnS rfT syT tnT ct sp cpS cpT 
              [lcS | [[u1 [u2 u3]] [L R]] ]
              [lkS | [[v1 [v2 v3]] P] ]
              [ ldS | [ [s1 [s2 s3]] nldS] ]
              [ ldT | [ [t1 [t2 t3]] nldT] ];
         compute; reflexivity. Qed. 


Lemma bop_llex_product_plus_id_is_times_ann_check_correct : 
  ∀ (rfS : brel_reflexive S rS)
     (syS : brel_symmetric S rS)
     (tnS : brel_transitive S rS) 
     (rfT : brel_reflexive T rT)
     (cplusS : bop_commutative S rS plusS)
     (pS_d : bops_id_equals_ann_decidable S rS plusS timesS)
     (pT_d : bops_id_equals_ann_decidable T rT plusT timesT), 
   p2c_plus_id_equals_times_ann (S * T) 
      (brel_product rS rT)
      (bop_llex rS plusS plusT)
      (ltran_product timesS timesT)
      (bops_llex_product_id_equals_ann_decide S T rS rT plusS timesS plusT timesT rfS syS tnS rfT cplusS pS_d pT_d)
   = 
   bops_llex_product_plus_id_is_times_ann_check 
      (p2c_plus_id_equals_times_ann S rS plusS timesS pS_d)
      (p2c_plus_id_equals_times_ann T rT plusT timesT pT_d). 
Proof. intros rfs syS tnS rfT cplus [ eqS | neqS] [eqT | neqT] ; compute; reflexivity. Qed.



Lemma bop_llex_product_times_id_equals_plus_ann_check_correct : 
  ∀ (rfS : brel_reflexive S rS)
     (syS : brel_symmetric S rS)
     (tnS : brel_transitive S rS) 
     (rfT : brel_reflexive T rT)
     (cplusS : bop_commutative S rS plusS)
     (idem_plusS : bop_idempotent S rS plusS)
     (pS_d : bops_id_equals_ann_decidable S rS timesS plusS)
     (pT_d : bops_id_equals_ann_decidable T rT timesT plusT), 
   p2c_times_id_equals_plus_ann (S * T) 
      (brel_product rS rT)
      (bop_llex rS plusS plusT)
      (ltran_product timesS timesT)
      (bops_product_llex_id_equals_ann_decide S T rS rT plusS timesS plusT
                                              timesT rfS syS tnS rfT cplusS idem_plusS pS_d pT_d)
   = 
   bops_llex_product_times_id_equals_plus_ann_check 
      (p2c_times_id_equals_plus_ann S rS plusS timesS pS_d) 
      (p2c_times_id_equals_plus_ann T rT plusT timesT pT_d). 
Proof. intros rfS syS tnS rfT cplus idem_S [ eqS | neqS] [eqT | neqT] ; compute; reflexivity. Qed.


Lemma bop_llex_product_left_left_absorbtive_check_correct : 
  ∀ (rfT : brel_reflexive T rT)
     (alS : bop_anti_left_decidable S rS timesS)
     (pS_d : bops_left_left_absorptive_decidable S rS plusS timesS) 
     (pT_d : bops_left_left_absorptive_decidable T rT plusT timesT), 
   bops_llex_product_left_left_absorptive_check wT 
       (p2c_left_left_absorptive S rS plusS timesS pS_d)
       (p2c_left_left_absorptive T rT plusT timesT pT_d)
       (p2c_anti_left_check S rS timesS alS) 
     = 
   p2c_left_left_absorptive (S * T) 
        (brel_product rS rT)
        (bop_llex rS plusS plusT)
        (ltran_product timesS timesT)
        (bops_llex_product_left_left_absorptive_decide S T rS rT wT plusS timesS plusT timesT rfT pS_d pT_d alS).
Proof. intros rfT [al | [[u1 u2] nal]] [ ldS | [ [s1 s2] nldS]] [ ldT | [ [t1 t2] nldT]]; simpl; auto. Qed. 


Lemma bop_llex_product_right_left_absorbtive_check_correct : 
  ∀ (syS : brel_symmetric S rS)
     (tnS : brel_transitive S rS)
     (rfT : brel_reflexive T rT)    
     (alS : bop_anti_left_decidable S rS timesS)
     (pS_d : bops_right_left_absorptive_decidable S rS plusS timesS) 
     (pT_d : bops_right_left_absorptive_decidable T rT plusT timesT), 
   bops_llex_product_right_left_absorptive_check wT 
       (p2c_right_left_absorptive S rS plusS timesS pS_d)
       (p2c_right_left_absorptive T rT plusT timesT pT_d)
       (p2c_anti_left_check S rS timesS alS) 
     = 
   p2c_right_left_absorptive (S * T) 
        (brel_product rS rT)
        (bop_llex rS plusS plusT)
        (ltran_product timesS timesT)
        (bops_llex_product_right_left_absorptive_decide S T rS rT wT plusS timesS plusT timesT syS tnS rfT pS_d pT_d alS).
Proof. intros syS tnS rfT [al | [[u1 u2] nal]] [ ldS | [ [s1 s2] nldS]] [ ldT | [ [t1 t2] nldT]]; simpl; auto. Qed. 


Lemma bop_llex_product_left_right_absorbtive_check_correct : 
  ∀ (rfT : brel_reflexive T rT)
     (alS : bop_anti_right_decidable S rS timesS)
     (pS_d : bops_left_right_absorptive_decidable S rS plusS timesS) 
     (pT_d : bops_left_right_absorptive_decidable T rT plusT timesT), 
   bops_llex_product_left_right_absorptive_check wT 
       (p2c_left_right_absorptive S rS plusS timesS pS_d)
       (p2c_left_right_absorptive T rT plusT timesT pT_d)
       (p2c_anti_right_check S rS timesS alS)        
     = 
     p2c_left_right_absorptive (S * T) 
        (brel_product rS rT)
        (bop_llex rS plusS plusT)
        (ltran_product timesS timesT)
        (bops_llex_product_left_right_absorptive_decide S T rS rT wT plusS timesS plusT timesT rfT pS_d pT_d alS).
Proof. intros rfT [al | [[u1 u2] nal]] [ ldS | [ [s1 s2] nldS]] [ ldT | [ [t1 t2] nldT]]; compute; reflexivity. Qed.


Lemma bop_llex_product_right_right_absorbtive_check_correct : 
  ∀ (syS : brel_symmetric S rS)
     (tnS : brel_transitive S rS)
     (rfT : brel_reflexive T rT)
     (alS : bop_anti_right_decidable S rS timesS)
     (pS_d : bops_right_right_absorptive_decidable S rS plusS timesS) 
     (pT_d : bops_right_right_absorptive_decidable T rT plusT timesT), 
   bops_llex_product_right_right_absorptive_check wT 
       (p2c_right_right_absorptive S rS plusS timesS pS_d)
       (p2c_right_right_absorptive T rT plusT timesT pT_d)
       (p2c_anti_right_check S rS timesS alS)        
     = 
     p2c_right_right_absorptive (S * T) 
        (brel_product rS rT)
        (bop_llex rS plusS plusT)
        (ltran_product timesS timesT)
        (bops_llex_product_right_right_absorptive_decide S T rS rT wT plusS timesS plusT timesT syS tnS rfT pS_d pT_d alS).
Proof. intros syS trS rfT [al | [[u1 u2] nal]] [ ldS | [ [s1 s2] nldS]] [ ldT | [ [t1 t2] nldT]]; compute; reflexivity. Qed.


Lemma  correct_bs_C_certs_llex_product : 
  ∀ (eqvS : eqv_proofs S rS)
     (eqvT : eqv_proofs T rT)
     (plusPS : sg_CS_proofs S rS plusS)
     (timesPS : sg_proofs S rS timesS)     
     (plusPT : sg_C_proofs T rT plusT)
     (timesPT : sg_proofs T rT timesT)          
     (bsS : bs_proofs S rS plusS timesS)
     (bsT : bs_proofs T rT plusT timesT), 
  bs_certs_llex_product rS rT plusS plusT timesT wS wT
               (P2C_sg S rS timesS timesPS)  (P2C_sg T rT timesT timesPT)
               (P2C_bs S rS plusS timesS bsS) (P2C_bs T rT plusT timesT bsT)
  =
 P2C_bs (S * T) (brel_product rS rT)
                  (bop_llex rS plusS plusT)
                  (ltran_product timesS timesT)
                  (bs_proofs_llex S T rS rT plusS timesS plusT timesT wS wT eqvS eqvT plusPS timesPS plusPT timesPT bsS bsT). 
Proof. intros.
       unfold bs_certs_llex_product, bs_proofs_llex, P2C_bs; simpl.
       rewrite bop_llex_product_plus_id_is_times_ann_check_correct.        
       rewrite bop_llex_product_times_id_equals_plus_ann_check_correct.                     
       rewrite <- bop_llex_product_left_left_absorbtive_check_correct. 
       rewrite <- bop_llex_product_left_right_absorbtive_check_correct. 
       rewrite <- bop_llex_product_right_left_absorbtive_check_correct. 
       rewrite <- bop_llex_product_right_right_absorbtive_check_correct.
       rewrite <- bop_llex_product_left_distributive_check_correct. 
       rewrite <- bop_llex_product_right_distributive_check_correct. 
       reflexivity. 
Qed.   




Lemma  correct_bs_CS_certs_llex_product : 
  ∀ (eqvS : eqv_proofs S rS)
     (eqvT : eqv_proofs T rT)
     (plusPS : sg_CS_proofs S rS plusS)
     (timesPS : sg_proofs S rS timesS)     
     (plusPT : sg_CS_proofs T rT plusT)
     (plusPT_v2 : sg_C_proofs T rT plusT)
     (timesPT : sg_proofs T rT timesT)          
     (bsS : bs_proofs S rS plusS timesS)
     (bsT : bs_proofs T rT plusT timesT), 
  bs_certs_llex_product rS rT plusS plusT timesT wS wT
               (P2C_sg S rS timesS timesPS)  (P2C_sg T rT timesT timesPT)
               (P2C_bs S rS plusS timesS bsS) (P2C_bs T rT plusT timesT bsT)
  =
 P2C_bs (S * T) (brel_product rS rT)
                  (bop_llex rS plusS plusT)
                  (ltran_product timesS timesT)
                  (bs_proofs_llex S T rS rT plusS timesS plusT timesT wS wT eqvS eqvT plusPS timesPS plusPT_v2 timesPT bsS bsT). 
Proof. intros.
       unfold bs_certs_llex_product, bs_proofs_llex, P2C_bs; simpl.
       rewrite bop_llex_product_plus_id_is_times_ann_check_correct.        
       rewrite bop_llex_product_times_id_equals_plus_ann_check_correct.                     
       rewrite <- bop_llex_product_left_left_absorbtive_check_correct. 
       rewrite <- bop_llex_product_left_right_absorbtive_check_correct. 
       rewrite <- bop_llex_product_right_left_absorbtive_check_correct. 
       rewrite <- bop_llex_product_right_right_absorbtive_check_correct.
       rewrite <- bop_llex_product_left_distributive_check_correct. 
       rewrite <- bop_llex_product_right_distributive_check_correct. 
       reflexivity. 
Qed.   

End ChecksCorrect.   

  

Theorem correct_bs_C_llex_product : ∀ (S T : Type) (bsS: A_bs_CS S) (bsT : A_bs_C T), 
   bs_C_llex_product (A2C_bs_CS S bsS) (A2C_bs_C T bsT)
   =
   A2C_bs_C (S * T) (A_bs_C_llex_product S T bsS bsT). 
Proof. intros S T bsS bsT. 
       unfold bs_C_llex_product, A_bs_C_llex_product, A2C_bs_C, A2C_bs_CS; simpl. 
       rewrite correct_eqv_product. 
       rewrite <- correct_sg_certs_product. 
       rewrite <- correct_sg_C_certs_llex. 
       rewrite <- correct_bs_C_certs_llex_product. 
       reflexivity. 
Qed. 

Theorem correct_bs_CS_llex_product : ∀ (S T : Type) (bsS: A_bs_CS S) (bsT : A_bs_CS T), 
   bs_CS_llex_product (A2C_bs_CS S bsS) (A2C_bs_CS T bsT)
   =
   A2C_bs_CS (S * T) (A_bs_CS_llex_product S T bsS bsT). 
Proof. intros S T bsS bsT. 
       unfold bs_CS_llex_product, A_bs_CS_llex_product, A2C_bs_CS; simpl. 
       rewrite correct_eqv_product.
       rewrite <- correct_sg_CS_certs_llex.        
       rewrite <- correct_sg_certs_product. 
       rewrite <- correct_bs_CS_certs_llex_product.
       reflexivity.
       apply A_bs_CS_plus_proofs. (* broken abstraction ? *) 
Qed. 



End Verify.   
  