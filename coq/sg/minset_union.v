Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.

Require Import CAS.coq.theory.set.

Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.eqv.theory.
Require Import CAS.coq.eqv.set.
Require Import CAS.coq.theory.set.
Require Import CAS.coq.eqv.reduce. 
Require Import CAS.coq.eqv.minset.

Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures. 
Require Import CAS.coq.sg.theory. 
Require Import CAS.coq.sg.union.
Require Import CAS.coq.sg.reduce.
Require Import CAS.coq.sg.cast_up.
Require Import CAS.coq.sg.classify.

Require Import CAS.coq.or.properties.
Require Import CAS.coq.or.structures.
Require Import CAS.coq.or.cast_up. 
Require Import CAS.coq.or.theory.
Require Import CAS.coq.or.subset.
Require Import CAS.coq.or.minset_subset.
Require Import CAS.coq.or.dual.
Require Import CAS.coq.or.from_sg. 

Require Import CAS.coq.or_sg.properties.
Require Import CAS.coq.or_sg.theory. 

Section Computation.
  
  Definition bop_minset_union {S : Type} (eqS lteS : brel S) : binary_op (finite_set S)
  := bop_reduce (uop_minset lteS) (bop_union eqS). 

End Computation. 

Section Theory.

Variable S  : Type. 
Variable eqS : brel S.

Variable wS : S.
Variable f : S -> S.                
Variable Pf : brel_not_trivial S eqS f. 

Variable congS : brel_congruence S eqS eqS. 
Variable refS  : brel_reflexive S eqS.
Variable symS  : brel_symmetric S eqS.  
Variable tranS : brel_transitive S eqS.


(* NB: antisymmetry is not assumed! *) 
Variable lteS : brel S.
Variable lteCong : brel_congruence S eqS lteS.
Variable lteRefl : brel_reflexive S lteS.
Variable lteTrans : brel_transitive S lteS. 

Notation "a [=] b"  := (eqS a b = true)          (at level 15).
Notation "a [<>] b" := (eqS a b = false)         (at level 15).
Notation "a <<= b"  := (lteS a b = true)        (at level 15).
Notation "a !<<= b" := (lteS a b = false)       (at level 15).

Notation "a << b"   := (below lteS b a = true) (at level 15).
Notation "a !<< b"  := (below lteS b a = false) (at level 15).
Notation "a [~] b"   := (equiv lteS b a = true) (at level 15).
Notation "a [!~] b"   := (equiv lteS b a = false) (at level 15).
Notation "a [#] b"   := (incomp lteS b a = true) (at level 15).
Notation "a [!#] b"   := (incomp lteS b a = false) (at level 15).
Notation "a [~|#] b"   := (equiv_or_incomp lteS b a = true) (at level 15).
Notation "a [!~|#] b"   := (equiv_or_incomp lteS b a = false) (at level 15).


Notation "[SEQ]" := (brel_set eqS).
(*Notation "[MSEQ]" := (brel_reduce [SEQ] (uop_minset lteS)).*) 
Notation "[MSEQ]" := (brel_minset eqS lteS). 
Notation "[MSU]" := (bop_minset_union eqS lteS).

Notation "a [in] b"  := (in_set eqS b a = true)   (at level 15).
Notation "a [!in] b" := (in_set eqS b a = false)  (at level 15).

Notation "a [=S] b"   := ([SEQ] a b = true)         (at level 15).
Notation "a [<>S] b"  := ([SEQ] a b = false)        (at level 15).
Notation "a [=MS] b"  := ([MSEQ] a b = true)        (at level 15).
Notation "a [<>MS] b" := ([MSEQ] a b = false)       (at level 15).
Notation "[ms] x"     := (uop_minset lteS x) (at level 15).

Notation "a [U] b" := (bop_union eqS a b)         (at level 15).
Notation "a <U> b" := (bop_minset_union eqS lteS a b)         (at level 15).

Definition set_transitive := brel_set_transitive S eqS refS symS tranS.
Definition set_symmetric := brel_set_symmetric S eqS.
Definition set_reflexive := brel_set_reflexive S eqS refS symS.
Definition minset_idempotent := uop_minset_idempotent S eqS refS symS tranS lteS lteCong lteRefl. 
Definition minset_transitive := brel_minset_transitive S eqS refS symS tranS lteS.
Definition minset_symmetric := brel_minset_symmetric S eqS lteS.
Definition minset_reflexive := brel_minset_reflexive S eqS refS symS lteS.
Definition uop_minset_congruence_weak := uop_minset_congruence_weak _ _ refS symS tranS lteS lteCong lteRefl lteTrans. 
Definition uop_minset_congruence := uop_minset_congruence S eqS refS symS tranS lteS lteCong.
Definition brel_minset_congruence_weak := brel_minset_congruence_weak S eqS refS symS tranS lteS lteCong lteRefl lteTrans.
Definition brel_minset_congruence := brel_minset_congruence S eqS refS symS tranS lteS lteCong lteRefl lteTrans.
Definition uop_minset_idempotent := uop_minset_idempotent _ _ refS symS tranS lteS lteCong lteRefl. 
Definition bop_union_congruence := bop_union_congruence _ _ refS symS tranS.
Definition bop_union_idempotent := bop_union_idempotent _ _ refS symS tranS.
Definition bop_union_commutative := bop_union_commutative _ _ refS symS tranS.
Definition bop_union_associative := bop_union_associative _ _ refS symS tranS.
Definition set_equal_implies_minset_equal := set_equal_implies_minset_equal S eqS refS symS tranS lteS lteCong lteRefl lteTrans.
Definition brel_minset_transitive := brel_minset_transitive S eqS refS symS tranS lteS.
Definition uop_minset_is_antichain := uop_minset_is_antichain S eqS refS symS lteS lteCong lteRefl.
Definition fundamental_minset_theorem := fundamental_minset_theorem S eqS refS symS tranS lteS lteCong lteTrans.

Lemma fundamental_minset_union_theorem (X Y : finite_set S) :
       {Z : finite_set S &
            ((X [U] Y) [=S] ((X <U> Y) [U] Z)) *
            (∀ s : S, s [in] Z → {t : S & t [in] (X <U> Y) * t << s})
       }. 
Proof. assert (A := fundamental_minset_theorem (X [U] Y)).
       destruct A as [Z [B C]]. 
       exists Z. split.
       + exact B. 
       + intros s E. 
         destruct (C s E) as [t [F G]].
         exists t. split; auto. 
Defined.

Lemma bop_minset_union_congruence_weak : bop_congruence _ [SEQ] [MSU]. 
Proof. intros X1 X2 Y1 Y2 A B.
       unfold bop_minset_union.
       assert (C := bop_union_congruence _ _ _ _ A B).
       apply set_equal_implies_minset_equal; auto. 
Qed. 


Lemma minset_union_left_uop_invariant : bop_left_uop_invariant _ [SEQ] [MSU] (uop_minset lteS). 
Proof. unfold bop_left_uop_invariant. unfold bop_minset_union. unfold bop_reduce.
       intros X Y. (* [ms] (([ms] X) [U] Y) [=S] [ms] (X [U] Y) *) 
       apply brel_set_intro_prop; auto. split. 
       - intros s A. 
         apply in_minset_elim in A; auto. destruct A as [A B]. 
         apply in_set_bop_union_elim in A; auto.             
         destruct A as [A | A].
         + apply in_minset_elim in A; auto. destruct A as [A C]. 
           apply in_minset_intro; auto. split. 
           * apply in_set_bop_union_intro; auto. 
           * intros t D. 
             apply in_set_bop_union_elim in D; auto. 
             destruct D as [D | D].
             -- apply C; auto. 
             -- apply B; auto. 
                apply in_set_bop_union_intro; auto.                         
         + apply in_minset_intro; auto. split. 
           apply in_set_bop_union_intro; auto. 
           intros t C.
           apply in_set_bop_union_elim in C; auto. 
           destruct C as [C | C]. 
           case_eq(in_set eqS ([ms] X) t); intro D. 
           * apply B; auto.                      
             -- apply in_set_bop_union_intro; auto.                         
           * apply in_set_minset_false_elim in D; auto. 
             destruct D as [u [D E]]. 
             assert (F : u [in] (([ms] X) [U] Y)).
             {
               apply in_set_bop_union_intro; auto.
             }
             assert (G := B _ F).
             case_eq(below lteS s t);intro H; auto. 
             -- assert (I := below_transitive _ _ lteTrans _ _ _ E H). 
                rewrite I in G. discriminate G.                            
           * apply B; auto.                      
             apply in_set_bop_union_intro; auto. 
       - intros s A. 
         apply in_minset_elim in A; auto. destruct A as [A B].
         apply in_minset_intro; auto. split. 
         + apply in_set_bop_union_intro; auto. 
           apply in_set_bop_union_elim in A; auto.
           destruct A as [A| A].
           * left. apply in_minset_intro; auto. split; auto. 
             -- intros t C. apply B. 
                apply in_set_bop_union_intro; auto. 
           * right; auto. 
         + intros t C.
           apply in_set_bop_union_elim in C; auto. 
           destruct C as [C | C].                
           * apply B. apply in_minset_elim in C; auto.
             destruct C as [C _].
             apply in_set_bop_union_intro; auto.                   
           * apply B. apply in_set_bop_union_intro; auto.
Qed. 

Lemma minset_union_right_uop_invariant : bop_right_uop_invariant _ [SEQ] [MSU] (uop_minset lteS).
Proof. apply bop_commutative_implies_left_uop_invariant_implies_right_uop_invariant.
       - apply set_symmetric. 
       - apply set_transitive. 
       - apply uop_minset_congruence_weak.
       - apply bop_union_commutative. 
       - apply minset_union_left_uop_invariant.
Qed. 

Lemma minset_union_uop_invariant : bop_uop_invariant [SEQ] (bop_union eqS) (uop_minset lteS).
Proof. apply r_is_b_reduction. 
       - exact set_symmetric.
       - exact set_transitive. 
       - exact minset_union_left_uop_invariant.
       - exact minset_union_right_uop_invariant.          
Qed.

Lemma bop_minset_union_congruence : bop_congruence _ [MSEQ] [MSU].
Proof. apply bop_reduce_congruence.
       - exact set_symmetric.
       - exact set_transitive.
       - exact bop_union_congruence.
       - exact uop_minset_congruence_weak.
       - exact minset_union_uop_invariant.
Qed. 

Lemma bop_minset_union_associative : bop_associative _ [MSEQ] [MSU].
Proof. apply bop_reduce_associative. 
       - exact set_reflexive.
       - exact set_symmetric. 
       - exact set_transitive. 
       - exact bop_union_congruence.
       - exact bop_union_associative.
       - exact uop_minset_congruence_weak. 
       - exact  minset_idempotent. 
       - exact minset_union_left_uop_invariant.
       - exact minset_union_right_uop_invariant. 
Qed. 

Lemma bop_minset_union_idempotent : bop_idempotent _ [MSEQ] [MSU].
Proof. apply bop_reduce_idempotent. 
       - exact set_reflexive.
       - exact set_symmetric. 
       - exact set_transitive. 
       - exact bop_union_congruence.
       - exact uop_minset_congruence_weak. 
       - exact minset_idempotent. 
       - exact minset_union_left_uop_invariant.
       - exact minset_union_right_uop_invariant.
       - exact bop_union_idempotent. 
Qed.

Lemma bop_minset_union_commutative : bop_commutative _ [MSEQ] [MSU].
Proof. apply bop_reduce_commutative. 
       - exact set_reflexive.
       - exact set_symmetric. 
       - exact set_transitive. 
       - exact bop_union_congruence.
       - exact uop_minset_congruence_weak. 
       - exact minset_idempotent. 
       - exact minset_union_left_uop_invariant.
       - exact minset_union_right_uop_invariant.
       - exact bop_union_commutative. 
Qed.

Lemma bop_minset_union_nil_left (X : finite_set S) :  (nil <U> X) [=MS] X. 
Proof. unfold bop_minset_union, brel_reduce. unfold bop_reduce.
       assert (A : (nil [U] X) [=S] X).
       {
         apply bop_union_with_nil_left; auto. 
       } 
       apply uop_minset_congruence_weak in A.
       assert (B := uop_minset_idempotent ((nil [U] X))).               
       exact (set_transitive _ _ _ B A). 
Qed.


Lemma bop_minset_union_nil_right (X : finite_set S) : (X <U> nil) [=MS] X.
Proof. assert (A := bop_minset_union_nil_left X). 
       assert (B := bop_minset_union_commutative nil X). 
       apply minset_symmetric in B.
       exact (minset_transitive _ _ _ B A).  
Qed.

Lemma bop_minset_union_id_is_nil : bop_is_id _ [MSEQ] [MSU] nil. 
Proof. split. 
         apply bop_minset_union_nil_left. 
         apply bop_minset_union_nil_right.
Qed.

Lemma bop_minset_union_exists_id : bop_exists_id _ [MSEQ] [MSU]. 
Proof. exists nil. apply bop_minset_union_id_is_nil. Defined.


(********************** BOTTOM ***********************

Note : proofs that expose iterate_minset should be 
moved to eqv/minset.v ....

*******)


Lemma iterate_minset_bottom  (b : S) :
  brel_is_bottom S lteS b -> (∀ (a : S),  b <<= a -> a <<= b -> b [=] a) -> 
  ∀ (X W : finite_set S), snd(iterate_minset lteS W (b :: nil) X) [=MS] (b :: nil).
Proof. intros A A' X W. induction X. 
       + unfold iterate_minset. simpl. apply brel_minset_reflexive; auto. 
       + unfold iterate_minset.
         case_eq(find (below lteS a) X). 
         ++ intros s B.
            fold (iterate_minset lteS (a :: W) (b :: nil) X).
            rewrite (iterate_minset_invariant_0 _ lteS X (a :: W) W (b :: nil)).
            exact IHX.
         ++ intro B.
            case_eq(equiv lteS b a); intro R. 
            +++ destruct (equiv_elim _ _ _ _ R) as [R1 R2]. 
                assert (R' := A' a R2 R1). 
                assert (D : find (below lteS a) (b :: nil) = None).
                compute.
                assert (E: b <<= a). rewrite (lteCong _ _ _ _ R' (refS a)). apply lteRefl. 
                assert (F: a <<= b). rewrite (lteCong _ _ _ _ (refS a) R'). apply lteRefl. 
                rewrite E, F; auto. 
                rewrite D. 
                fold (iterate_minset lteS W (a :: b :: nil) X). 
                assert (E : (a :: b :: nil) [=S] (b::nil)).
                   compute. rewrite R'.  rewrite (symS _ _ R'). rewrite refS; auto.
                assert (F := iterate_minset_left_congruence_weak _ _ refS symS tranS _ lteCong X W _ _ E). 
                apply set_equal_implies_minset_equal in F. 
                exact (brel_minset_transitive _ _ _ F IHX). 

            +++ case_eq(find (below lteS a) (b :: nil)).
                ++++ intros s C. (* s must be bottom b *)
                     compute in C.
                     case_eq(lteS b a); intro D; case_eq(lteS a b); intro E. 
                     +++++ rewrite D in C. rewrite E in C. discriminate C. 
                     +++++ rewrite D in C. rewrite E in C. inversion C.
                           fold (iterate_minset lteS (a :: W) (s :: nil) X).
                           rewrite <- H0. 
                           assert (I := iterate_minset_invariant_0 _ lteS X (a :: W)  W (b :: nil)).
                           rewrite I.
                           exact IHX. 
                     +++++ rewrite D in C. discriminate C. 
                     +++++ rewrite D in C. discriminate C. 

                ++++ intro C.
                     assert (D := find_below_none _ _ refS symS lteS lteCong _ _ C).
                     assert (E := D _ (in_set_singleton_intro S eqS symS _ _ (refS b))).
                     assert (F := A a).
                     apply below_false_elim in E.  
                     destruct E as [E | E]. 
                     +++++ rewrite F in E. discriminate E. 
                     +++++ assert (G : a [~] b). apply equiv_intro; auto. 
                           rewrite G in R. discriminate R.
Qed. 

Lemma minset_bottom_aux (X : finite_set S) (b : S) :
     brel_is_bottom S lteS b -> (∀ t : S, b <<= t → t <<= b → b [=] t) ->  
         ([ms] (b :: X)) [=MS] (b :: nil). 
Proof. intros A A'. unfold uop_minset. 
       unfold iterate_minset.        
       assert (B : find (below lteS b) X = None).
          case_eq(find (below lteS b) X); auto. 
             intros s C.  
             destruct (find_below_some _ _ refS symS _ _ _ _ C) as [D E]. 
             assert (F := A s). apply below_elim in E.
             rewrite F in E. destruct E as [_ E]. discriminate E. 
       rewrite B.
       assert (C : find (below lteS b) nil = None). compute; auto.
       rewrite C.       
       fold (iterate_minset lteS nil (b :: nil) X). 
       apply iterate_minset_bottom; auto. 
Qed.

                                    
Lemma minset_bottom_with_anti_symmetry2 (anti : brel_antisymmetric S eqS lteS) (X : finite_set S) (b : S) :
    brel_is_bottom S lteS b -> ([ms] (b :: X)) [=MS] (b :: nil). 
Proof. intros A. assert (A' := anti b). apply minset_bottom_aux; auto. Qed. 

Lemma minset_bottom_without_anti_symmetry2 (X : finite_set S) (b : S) :
    brel_is_qo_bottom S eqS lteS b -> ([ms] (b :: X)) [=MS] (b :: nil). 
Proof. intros [A A']. apply minset_bottom_aux; auto. Qed. 


Lemma bop_minset_union_exists_ann_is_bottom (b : S) :
     brel_is_bottom S lteS b -> (∀ t : S, b <<= t → t <<= b → b [=] t) ->  
     bop_is_ann (finite_set S) [MSEQ] [MSU] (b :: nil). 
Proof. intros A A' X. unfold brel_is_bottom in A.
       split; unfold bop_minset_union, bop_reduce. 
       - assert (B := minset_bottom_aux X b A A').
         assert (C : ([ms] ((b :: nil) [U] X)) [=MS] ([ms] (b :: X))).
         {
           assert (D := bop_union_cons_shift_left S eqS refS symS tranS X b).
           apply uop_minset_congruence_weak in D.
           apply set_equal_implies_minset_equal; auto. 
         } 
         exact (minset_transitive _ _ _ C B). 
       - assert (B := minset_bottom_aux X b A A').
         assert (C : ([ms] (X [U] (b :: nil))) [=MS] ([ms] (b :: X))).
         {
           assert (D := bop_union_cons_shift_right S eqS refS symS tranS X b).
           apply uop_minset_congruence_weak in D.
           apply set_equal_implies_minset_equal; auto. 
         } 
         exact (minset_transitive _ _ _ C B). 
Qed.

Lemma bop_minset_union_exists_ann_without_antisymmetry :
  brel_exists_qo_bottom S eqS lteS ->  bop_exists_ann _ [MSEQ] [MSU].
Proof. intros [b [A A']]. exists (b :: nil).
       apply (bop_minset_union_exists_ann_is_bottom b); auto.
Defined. 


Lemma bop_minset_union_exists_ann_with_antisymmetry
  (anti : brel_antisymmetric S eqS lteS) : 
      brel_exists_bottom S lteS ->
           bop_exists_ann  _ [MSEQ] [MSU].
Proof. intros [b A].
       assert (B : brel_exists_qo_bottom S eqS lteS). 
          exists b. split; auto. exact (anti b). 
       exact (bop_minset_union_exists_ann_without_antisymmetry B).
Defined.        


Lemma brel_not_antisymmetric_implies_bop_minset_union_not_selective :
         (brel_not_antisymmetric S eqS lteS) → bop_not_selective _ [MSEQ] [MSU].
Proof. intros [ [s t] [[A B] C] ]. unfold brel_reduce, bop_minset_union, bop_reduce. 
       assert (D := bop_union_two_singletons S eqS refS symS tranS s t).
       apply uop_minset_congruence_weak in D.
       apply uop_minset_congruence_weak in D.
       exists (s :: nil, t :: nil). split.
       - case_eq([SEQ] ([ms] ([ms] ((s :: nil) [U] (t :: nil)))) ([ms] (s :: nil))); intro E; auto.
         apply set_symmetric in E.
         assert (F := set_transitive _ _ _ E D).
         apply brel_set_elim_prop in F; auto.
         destruct F as [F H].
         (* pull out as a lemma? *) 
         assert (I : t [in] ([ms] ([ms] (s :: t :: nil)))).
         {
           assert (J := uop_minset_idempotent (s :: t :: nil)). 
           rewrite (in_set_congruence _ eqS symS tranS _ _ _ _ J (refS t)). 
           apply in_minset_intro; auto. split.
           + apply in_set_cons_intro; auto.
             right. apply in_set_singleton_intro; auto.
           + intros u I.
             apply in_set_cons_elim in I; auto.
             apply below_false_intro.
             destruct I as [I | I].
             * rewrite (lteCong _ _ _ _ (refS t) I) in B. 
               right; auto. 
             * apply in_set_singleton_elim in I; auto.
               right. rewrite <- (lteCong _ _ _ _ (refS t) I).
               apply lteRefl. 
         } 
         assert (J := H _ I).
         apply in_minset_elim in J; auto. destruct J as [J _].
         apply in_set_singleton_elim in J; auto.
         rewrite J in C. discriminate C.
       - unfold brel_minset, brel_reduce.
         case_eq([SEQ] ([ms] ([ms] ((s :: nil) [U] (t :: nil)))) ([ms] (t :: nil))); intro E; auto.
         apply set_symmetric in E.
         assert (F := set_transitive _ _ _ E D).
         apply brel_set_elim_prop in F; auto.
         destruct F as [F H].
         (* pull out as a lemma? *) 
         assert (I : s [in] ([ms] ([ms] (s :: t :: nil)))).
         {
           assert (J := uop_minset_idempotent (s :: t :: nil)). 
           rewrite (in_set_congruence _ eqS symS tranS _ _ _ _ J (refS s)). 
           apply in_minset_intro; auto. split.
           + apply in_set_cons_intro; auto.
           + intros u I.
             apply in_set_cons_elim in I; auto.
             apply below_false_intro.
             destruct I as [I | I].
             * right. rewrite <- (lteCong _ _ _ _ (refS s) I).
               apply lteRefl.
             * apply in_set_singleton_elim in I; auto.
               rewrite (lteCong _ _ _ _ (refS s) I) in A.
               right; auto. 
         } 
         assert (J := H _ I).
         apply in_minset_elim in J; auto. destruct J as [J _].
         apply in_set_singleton_elim in J; auto. apply symS in J. 
         rewrite J in C. discriminate C.
Defined. 


Lemma bop_minset_union_incomp_pair (s t : S) (L : s !<<= t) (R : t !<<= s): ((s :: nil) <U> (t :: nil)) [<>MS] (s :: nil).
       unfold bop_minset_union, bop_reduce. 
       case_eq([MSEQ] ([ms] ((s :: nil) [U] (t :: nil))) (s :: nil)); intro A; auto.
       - apply brel_set_elim_prop in A; auto. destruct A as [A B].
         assert (C : t [in] ([ms] ([ms] ((s :: nil) [U] (t :: nil))))).
         {
           assert (J := uop_minset_idempotent ((s :: nil) [U] (t :: nil))). 
           rewrite (in_set_congruence _ eqS symS tranS _ _ _ _ J (refS t)).
           apply in_minset_intro; auto. split.
           + apply in_set_bop_union_intro; auto.
             right. apply in_set_singleton_intro; auto.
           + intros u I.
             apply in_set_bop_union_elim in I; auto.
             apply below_false_intro.
             destruct I as [I | I].
             * apply in_set_singleton_elim in I; auto.
               rewrite (lteCong _ _ _ _ I (refS t)) in L. 
               left; auto. 
             * apply in_set_singleton_elim in I; auto.
               rewrite <- (lteCong _ _ _ _ (refS t) I).
               right. apply lteRefl. 
         } 
         assert (D := A _ C).
         apply in_minset_elim in D; auto.
         destruct D as [D E].
         apply in_set_singleton_elim in D; auto.
         assert (F := lteCong _ _ _ _ D (refS s)).
         rewrite (lteRefl s) in F. rewrite R in F. 
         exact F. 
Qed. 


Lemma bop_minset_union_not_selective:
  (brel_not_total S lteS) → bop_not_selective _ [MSEQ] [MSU].
Proof. intros [ [s t] [L R] ]. 
       exists (s :: nil, t :: nil).
       assert (A := bop_minset_union_incomp_pair s t L R).
       assert (B := bop_minset_union_incomp_pair t s R L).
       assert (C := bop_minset_union_commutative (s :: nil) (t :: nil)).
       split. 
       - exact A. 
       - case_eq([MSEQ] ((s :: nil) <U> (t :: nil)) (t :: nil)); intro D; auto.
         + apply minset_symmetric in C.
           assert (E := minset_transitive _ _ _ C D). 
           rewrite E in B. discriminate B. 
Defined. 




Lemma total_implies_singlton_minsets
  (tot : brel_total S lteS)
  (X : finite_set S)
  (anti : brel_antisymmetric S eqS lteS):
            (nil [=S] X) + {s : S & (s :: nil) [=S] [ms] X}.
Proof. induction X.
       left. compute; auto. 
       right. destruct IHX as [IHX | [s A]]. 
          exists a.
          assert (A : [ms] (a :: X) [=S] (a :: nil)).
             assert (B : ([ms] (a :: X)) [=S] ([ms] (a :: nil))).
                assert (C : (a :: X) [=S] (a :: nil)).
                   apply brel_set_intro_prop; auto. split. 
                   intros s A. apply in_set_singleton_intro; auto. 
                   apply in_set_cons_elim in A; auto. destruct A as [A | A]; auto. 
                      rewrite <- (in_set_congruence _ _ symS tranS _ _ _ _ IHX (refS s)) in A. 
                      compute in A.  discriminate A. 
                   intros s A. apply in_set_singleton_elim in A; auto.                      
                   apply in_set_cons_intro; auto. 
               exact (uop_minset_congruence_weak _ _ C ). 
             rewrite minset_singleton in B. auto. 
          apply set_symmetric; auto.

          apply brel_set_elim_prop in A; auto. destruct A as [A B].
          assert (C : s [in] (s :: nil)). apply in_set_cons_intro; auto. 
          assert (D := A s C). 
          apply in_minset_elim in D; auto. destruct D as [D E]. 
          destruct (tot a s) as [F | F]. 
             exists a. 
             apply brel_set_intro_prop; auto. split. 
                intros t G. apply in_set_singleton_elim in G; auto. 
                rewrite (lteCong _ _ _ _ G (refS s)) in F.  
                apply in_minset_intro; auto. split. 
                   apply in_set_cons_intro; auto. 
                   intros u H. apply below_false_intro; auto. 
                   apply in_set_cons_elim in H; auto. 
                   destruct H as [H | H]. 
                      right. apply symS in G. apply symS in H. 
                      rewrite (lteCong _ _ _ _ G H). exact (lteRefl a). 
                      assert (I := E u H). apply below_false_elim in I. 
                      destruct I as [I | I]. 
                         left. case_eq(lteS u t); intro J; auto. 
                            rewrite (lteTrans _ _ _ J F) in I. discriminate I. 
                         right. exact (lteTrans _ _ _ F I). 
                intros t G. apply in_minset_elim in G; auto. destruct G as [G H]. 
                assert (I : s [in] (a :: X)). apply in_set_cons_intro; auto.              
                assert (J := H s I). apply below_false_elim in J; auto. 
                apply in_set_cons_elim in G; auto.
                (* this is a mess *) 
                destruct G as [G | G]; destruct J as [J | J]. 
                   apply in_set_singleton_intro; auto. 
                   apply in_set_singleton_intro; auto. 
                   assert (Z : a [in] (a :: X)). apply in_set_cons_intro; auto. 
                   assert (W := H a Z). apply below_false_elim in W; auto. 
                      destruct W as [W | W]. 
                         destruct (tot a t) as [Y | Y]; destruct (tot s t) as [U | U]. 
                           rewrite Y in W. discriminate W. 
                           rewrite Y in W. discriminate W. 
                           rewrite U in J. discriminate J. 
                           assert (V := E t G). apply below_false_elim in V; auto.
                               destruct V as [V | V]. 
                                  rewrite U in V. discriminate V. 
                                  rewrite V in J. discriminate J. 
                         assert (Y : t [in] [ms] X). 
                            apply in_minset_intro; auto. split; auto. 
                            intros u Y. apply H. apply in_set_cons_intro; auto. 
                         assert (U := B t Y). apply in_set_singleton_elim in U; auto. 
                         rewrite (lteCong _ _ _ _ U (refS t)) in J. rewrite (lteRefl t) in J. discriminate J. 
                   assert (K := E t G). apply below_false_elim in K; auto.
                   destruct K as [K | K]. 
                      rewrite J in K. discriminate K. 
                      assert (L := anti _ _ K J). 
                      rewrite (lteCong _ _ _ _ (refS a) L) in F. 
                      apply in_set_singleton_intro; auto. 
                      case_eq(eqS a t); intro M; auto.                       
                         case_eq(lteS t a); intro N. 
                            rewrite (anti _ _ F N) in M. discriminate M. 
                            assert (O : a [in] (a :: X)). apply in_set_cons_intro; auto. 
                            assert (P := H a O). apply below_false_elim in P; auto. 
                               destruct P as [P | P]. 
                                  rewrite F in P. discriminate P. 
                                  rewrite P in N. discriminate N. 
                              
             exists s.
             apply brel_set_intro_prop; auto; split. 
                intros t G. apply in_set_singleton_elim in G; auto. 
                rewrite (lteCong _ _ _ _ G (refS a)) in F. 
                apply in_minset_intro; auto. split.                 
                   apply in_set_cons_intro; auto. right.
                   apply (in_set_right_congruence _ _ symS tranS _ _ X G); auto. 
                   intros u H. apply in_set_cons_elim in H; auto. 
                   destruct H as [H | H]. 
                      apply below_false_intro; auto. 
                      right. rewrite (lteCong _ _ _ _ (refS t) (symS _ _ H)). exact F. 
                      assert (I := E u H). rewrite (below_congruence _ _ _ lteCong _ _ _ _ G (refS u)) in I. 
                      exact I. 
                intros t G. apply in_minset_elim in G; auto.
                destruct G as [G H].  apply in_set_cons_elim in G; auto. 
                destruct G as [G | G]. 
                   rewrite (lteCong _ _ _ _ (refS s) G) in F. 
                   assert (I : s [in] (a :: X)). apply in_set_cons_intro; auto. 
                   assert (J := H s I). apply below_false_elim in J; auto.
                   destruct J as [J | J]. 
                      rewrite F in J. discriminate J. 
                      apply in_set_singleton_intro; auto.                    
                   assert (I : t [in] ([ms] X)).
                      apply in_minset_intro; auto. split; auto. 
                         intros u I. apply H. apply in_set_cons_intro; auto. 
                   exact (B t I).                 
Qed.


Lemma bop_minset_union_nil_left_v2 (X Y : finite_set S) : nil [=S] X -> (X <U> Y) [=S] ([ms] Y).
Proof. intro A. 
       assert (B := bop_minset_union_congruence_weak _ _ _ _ A (set_reflexive Y)).
       apply set_symmetric in B.
       assert (C : (nil <U> Y) [=S] ([ms] Y)).
       {
          unfold bop_minset_union, brel_reduce, bop_reduce.  
          assert (C := bop_union_with_nil_left _ eqS refS symS tranS Y). 
          assert (D := uop_minset_congruence_weak _ _ C). 
          exact D.
       } 
       exact (set_transitive _ _ _ B C). 
Qed. 

Lemma minset_union_commutative_weak : bop_commutative _ [SEQ] [MSU].
Proof. intros X Y.
       apply uop_minset_congruence_weak. 
       apply bop_union_commutative.
Qed. 

Lemma bop_minset_union_nil_right_v2 (X Y : finite_set S) : nil [=S] Y -> (X <U> Y) [=S] ([ms] X). 
Proof. intro A.
       assert (B := bop_minset_union_nil_left_v2 Y X A). 
       assert (C : (X <U> Y) [=S] (Y <U> X)).
          unfold bop_minset_union.
          apply minset_union_commutative_weak. 
       exact (brel_set_transitive _ _ refS symS tranS _ _ _ C B).        
Qed. 
       
Lemma bop_minset_union_selective_weak (tot : brel_total S lteS) (anti : brel_antisymmetric S eqS lteS) (X Y : finite_set S):
  (X <U> Y) [=S] ([ms] X) + (X <U> Y) [=S] ([ms] Y). 
Proof. destruct(total_implies_singlton_minsets tot X) as [A | A];
       destruct(total_implies_singlton_minsets tot Y) as [B | B]; auto. 
       - left. apply bop_minset_union_nil_right_v2; auto. 
       - right. apply bop_minset_union_nil_left_v2; auto. 
       - left.  apply bop_minset_union_nil_right_v2;auto.
       - destruct A as [x A]. destruct B as [y B].
         unfold bop_minset_union, brel_reduce, bop_reduce. 
         assert (F := bop_union_congruence _ _ _ _ A B).
         assert (G := uop_minset_congruence_weak _ _ F). 
         assert (H : (x :: nil) [U] (y :: nil) [=S] (x :: y :: nil)).
         {
             apply brel_set_intro_prop; auto. split. 
                intros t C. apply in_set_bop_union_elim in C; auto.
                destruct C as [C | C]. 
                   apply in_set_singleton_elim in C; auto.
                   apply in_set_cons_intro; auto. 
                   apply in_set_cons_intro; auto. 
                intros t C. apply in_set_bop_union_intro; auto. 
                apply in_set_cons_elim in C; auto. 
                destruct C as [C | C]. 
                   left. apply in_set_singleton_intro; auto. 
                   right. auto.
         } 
         assert (I := uop_minset_congruence_weak _ _ H).           
         apply brel_set_symmetric in G. 
         assert (J' := brel_set_transitive _ _ refS symS tranS _ _ _ G I).
         assert (J'' := minset_union_uop_invariant X Y).
         assert (J := set_transitive _ _ _ J'' J'). 

          assert (A' := A). assert(B' := B). 
          apply brel_set_elim_prop in A; auto. destruct A as [A1 A2].
          apply brel_set_elim_prop in B; auto. destruct B as [B1 B2].
          
          case_eq(lteS x y); intro C;  case_eq(lteS y x); intro D.  
            (* x ~ y *)
            assert (E := anti _ _ C D). left.
            assert (K : [ms] (x :: y :: nil) [=S] ([ms] X)).
               apply brel_set_intro_prop; auto. split. 
                  intros t K. apply A1. apply in_set_singleton_intro; auto. 
                  apply in_minset_elim in K; auto. destruct K as [K1 K2]. 
                  apply in_set_cons_elim in K1; auto.
                  destruct K1 as [K1 | K1]. 
                     exact K1. 
                     apply in_set_cons_elim in K1; auto.
                     destruct K1 as [K1 | K1]. 
                        exact (tranS _ _ _ E K1). 
                        compute in K1. discriminate K1. 
                     
                  intros t K. assert (L := A2 t K). 
                  apply in_set_singleton_elim in L; auto. 
                  apply in_minset_intro; auto. split. 
                     apply in_set_cons_intro; auto. 
                     intros u M. apply in_set_cons_elim in M; auto. 
                     destruct M as [M | M]. 
                        rewrite (below_congruence _ _ _ lteCong _ _ _ _ (symS _ _ L) (symS _ _ M)). 
                        apply below_not_reflexive; auto. 
                        apply in_set_singleton_elim in M; auto. 
                        assert (N := tranS _ _ _ E M). 
                        rewrite (below_congruence _ _ _ lteCong _ _ _ _ (symS _ _ L) (symS _ _ N)). 
                        apply below_not_reflexive; auto.                         
            exact (brel_set_transitive _ _ refS symS tranS _ _ _ J K).

            (* x < y *)  
            left.
            assert (K : [ms] (x :: y :: nil) [=S] ([ms] X)).
               assert (K : [ms] (x :: y :: nil) [=S] (x :: nil)). 
                  apply brel_set_intro_prop; auto. split. 
                     intros t K. apply in_set_singleton_intro; auto. 
                     apply in_minset_elim in K; auto. destruct K as [K1 K2]. 
                     apply in_set_cons_elim in K1; auto.
                     destruct K1 as [K1 | K1]; auto. 
                        apply in_set_singleton_elim in K1; auto. 
                        assert (M : x [in] (x :: y :: nil)). apply in_set_cons_intro; auto. 
                        assert (N := K2 x M). 
                        rewrite (below_congruence _ _ _ lteCong _ _ _ _ (symS _ _ K1) (refS x)) in N. 
                        apply below_false_elim in N; auto. 
                        destruct N as [N | N]. 
                           rewrite C in N. discriminate N. 
                           rewrite N in D. discriminate D.
                     intros t K. apply in_set_singleton_elim in K; auto. 
                     apply in_minset_intro; auto. split. 
                        apply in_set_cons_intro; auto. 
                        intros u L. apply in_set_cons_elim in L; auto.                       
                        destruct L as [L | L]. 
                           rewrite (below_congruence _ _ _ lteCong _ _ _ _ (symS _ _ K) (symS _ _ L)). 
                           apply below_not_reflexive; auto. 
                           apply in_set_singleton_elim in L; auto.                   
                           rewrite (below_congruence _ _ _ lteCong _ _ _ _ (symS _ _ K) (symS _ _ L)). 
                           apply below_false_intro; auto. 
               exact (brel_set_transitive _ _ refS symS tranS _ _ _ K A'). 
            exact (brel_set_transitive _ _ refS symS tranS _ _ _ J K). 


            (* y < x *)
            right. assert (K : [ms] (x :: y :: nil) [=S] ([ms] Y)).
               assert (K : [ms] (x :: y :: nil) [=S] (y :: nil)). 
                  apply brel_set_intro_prop; auto. split. 
                     intros t K. apply in_set_singleton_intro; auto. 
                     apply in_minset_elim in K; auto. destruct K as [K1 K2]. 
                     apply in_set_cons_elim in K1; auto.
                     destruct K1 as [K1 | K1]; auto. 
                        assert (M : y [in] (x :: y :: nil)).
                           apply in_set_cons_intro; auto. right.
                           apply in_set_cons_intro; auto.                            
                        assert (N := K2 y M). 
                        rewrite (below_congruence _ _ _ lteCong _ _ _ _ (symS _ _ K1) (refS y)) in N. 
                        apply below_false_elim in N; auto. 
                        destruct N as [N | N]. 
                           rewrite D in N. discriminate N. 
                           rewrite N in C. discriminate C.
                        apply in_set_singleton_elim in K1; auto. 

                     intros t K. apply in_set_singleton_elim in K; auto. 
                     apply in_minset_intro; auto. split. 
                        apply in_set_cons_intro; auto. right. apply in_set_cons_intro; auto. 
                        intros u L. apply in_set_cons_elim in L; auto.                       
                        destruct L as [L | L]. 
                           rewrite (below_congruence _ _ _ lteCong _ _ _ _ (symS _ _ K) (symS _ _ L)).
                           apply below_false_intro; auto. 
                           apply in_set_singleton_elim in L; auto.                   
                           rewrite (below_congruence _ _ _ lteCong _ _ _ _ (symS _ _ K) (symS _ _ L)). 
                           apply below_not_reflexive; auto. 

               exact (brel_set_transitive _ _ refS symS tranS _ _ _ K B'). 
          exact (brel_set_transitive _ _ refS symS tranS _ _ _ J K). 

            (* x # y *)
            destruct (tot x y) as [E | E].
               rewrite E in C. discriminate C.
               rewrite E in D. discriminate D. 
Qed. 
          
Lemma bop_minset_union_selective
  (tot : brel_total S lteS)
  (anti : brel_antisymmetric S eqS lteS) : bop_selective  _ [MSEQ] [MSU].
Proof. intros X Y.
       unfold brel_minset, brel_reduce.
       unfold bop_minset_union, bop_reduce. 
       destruct (bop_minset_union_selective_weak tot anti X Y) as [B | B]. 
       left. unfold bop_minset_union, bop_reduce in B. 
       assert (C := uop_minset_idempotent (X [U] Y)). 
       exact (brel_set_transitive _ _ refS symS tranS _ _ _ C B). 
       right. unfold bop_minset_union, bop_reduce in B. 
       assert (C := uop_minset_idempotent (X [U] Y)). 
       exact (brel_set_transitive _ _ refS symS tranS _ _ _ C B). 
Qed.


Definition bop_minset_union_selective_decide_v1 (tot_d : brel_total_decidable S lteS) (anti : brel_antisymmetric S eqS lteS): 
      bop_selective_decidable _ [MSEQ] [MSU]
 := match tot_d with
     | inl tot  => inl (bop_minset_union_selective tot anti) 
     | inr ntot => inr (bop_minset_union_not_selective ntot)
    end.


Definition bop_minset_union_selective_decide_v2 
           (tot_d : brel_total_decidable S lteS)
           (anti_d : brel_antisymmetric_decidable S eqS lteS): 
  bop_selective_decidable   _ [MSEQ] [MSU] 
:= match anti_d with
   | inl anti => bop_minset_union_selective_decide_v1 tot_d anti 
   | inr nanti => inr (brel_not_antisymmetric_implies_bop_minset_union_not_selective nanti)
   end. 

Lemma bop_minset_union_not_anti_left : 
  bop_not_anti_left _ [MSEQ] [MSU].
Proof. exists (nil, nil). compute.
       reflexivity.
Defined. 

Lemma bop_minset_union_not_anti_right : 
  bop_not_anti_right _ [MSEQ] [MSU].
Proof. exists (nil, nil). compute.
       reflexivity.
Defined. 


Lemma bop_minset_union_not_left_constant : 
  bop_not_left_constant _ [MSEQ] [MSU].
Proof. exists (nil, ((wS :: nil), (f wS) ::nil)).
       compute. destruct (Pf wS) as [A B]. 
       rewrite A. reflexivity.
Defined. 


Lemma bop_minset_union_not_left_cancellative
  (tot_d : brel_total_decidable S lteS)
  (anti_d : brel_antisymmetric_decidable S eqS lteS): 
  bop_not_left_cancellative _ [MSEQ] [MSU].
Proof. apply (bop_idempotent_and_commutative_and_selective_decidable_imply_not_left_cancellative _ [MSEQ] [MSU] nil (brel_minset_new _ eqS wS)).
       - apply brel_minset_congruence. 
       - apply brel_minset_not_trivial; auto.
       - apply brel_minset_reflexive; auto.
       - apply brel_minset_symmetric; auto.
       - apply brel_minset_transitive; auto.
       - apply bop_minset_union_associative.
       - apply bop_minset_union_congruence.
       - apply bop_minset_union_idempotent.
       - apply bop_minset_union_commutative.
       - apply bop_minset_union_selective_decide_v2; auto.
Defined.


(* will I need to do this for CAS version??? 

Lemma bop_minset_union_not_left_cancellative
  (tot_d : brel_total_decidable S lteS)
  (anti_d : brel_antisymmetric_decidable S eqS lteS): 
  bop_not_left_cancellative _ [MSEQ] [MSU].
Proof.   destruct anti_d as [anti | [[s1 s2] A]]. 
       - destruct tot_d as [tot | [[s3 s4] [B C]]]. 
         + exists (wS :: nil, (wS :: nil, nil)). split.
           * admit. 
           * compute. reflexivity.
         + exists ((s3 :: nil) <U> (s4 :: nil), (s3 :: nil, s4 :: nil)). split. 
           * admit. 
           * admit. 
       - exists ((s1 :: nil) <U> (s2 :: nil), (s1 :: nil, s2 :: nil)). split. 
         * admit. 
         * admit. 
Admitted. 
*) 
(************************* ann *****************************************)

(*
move this ... 
*)
Lemma lte_trichotomy (s t : S ) : s << t + t << s + s [~|#] t.
Proof. case_eq(below lteS s t); intro A;  case_eq(below lteS t s); intro B; auto. 
       apply below_false_elim in A. apply below_false_elim in B.
       destruct A as [A | A]; destruct B as [B | B]. 
          right. apply equiv_or_incomp_intro. right. apply incomp_intro; auto.
          rewrite B in A. discriminate A. 
          rewrite B in A. discriminate A.
          right. apply equiv_or_incomp_intro. left. apply equiv_intro; auto.
Qed. 


(* this is really a general lemma about antichains *) 
Lemma bottoms_is_minimal (BOTTOMS : finite_set S) (AC : is_antichain S eqS lteS BOTTOMS) : 
  [ms] BOTTOMS [=S] BOTTOMS.
Proof. apply brel_set_intro_prop; auto. split. 

          intros a A. apply in_minset_elim in A; auto. 
          destruct A as [A _]. exact A. 

          intros a A. apply in_minset_intro; auto. split. 
             exact A. 
             intros t B.  assert (C := AC a A t B). apply equiv_or_incomp_elim in C.
             apply below_false_intro. 
             destruct C as [C | C]. 
                apply equiv_elim in C. destruct C as [C _]. right; exact C. 
                apply incomp_elim in C. destruct C as [_ C]. left; exact C. 
Qed.


Lemma bop_minset_union_enum_is_ann_left
      (BOTTOMS : finite_set S)
      (AC : is_antichain S eqS lteS BOTTOMS)
      (*EC : ∀ s x : S, x [in] BOTTOMS -> s [~] x -> s [in] BOTTOMS*) 
      (w : S → S)
      (H :  ∀ s : S, (s [in] BOTTOMS) + ((w s) [in] BOTTOMS * (w s) << s)) 
      (* H :  ∀ s : S, (w s) [in] BOTTOMS * (w s) <<= s *)
      :
  ∀ X : finite_set S, (BOTTOMS <U> X) [=MS] BOTTOMS. 
Proof. intro X.
       assert (A : (BOTTOMS <U> X) [=S] BOTTOMS).
          apply brel_set_intro_prop; auto. split. 
             intros s B. unfold bop_minset_union, bop_reduce in B. 
             apply in_minset_elim in B; auto. destruct B as [B C].
             apply in_set_bop_union_elim in B; auto. 
             destruct B as [B | B].
                (* B : s [in] BOTTOMS *) 
                exact B. 

                (* B : s [in] X *)                    
                destruct (H s) as [Q | [E F]].
                   exact Q. 
                   assert (G : (w s) [in] (BOTTOMS [U] X)).
                      apply in_set_bop_union_intro; auto. 
                   assert (I := C (w s) G). apply below_false_elim in I.
                   destruct I as [I | I].
                      apply below_elim in F. destruct F as [F _]. 
                      rewrite I in F. discriminate F.
                      assert (J : w s << w s). exact (below_pseudo_transitive_right _ lteS lteTrans _ _ _ F I).
                      rewrite (below_not_reflexive S lteS  (w s)) in J. discriminate J. 
                   
             intros s B. unfold bop_minset_union. apply in_minset_intro; auto. split. 
             apply in_set_bop_union_intro; auto. 
             intros t C. case_eq(below lteS s t); intro D; auto. 
             apply in_set_bop_union_elim in C; auto. 
             destruct C as [C | C].
             assert (E := AC s B t C). apply equiv_or_incomp_elim in E.
             apply below_elim in D. destruct D as [D1 D2].                       
             destruct E as [E | E].
             apply equiv_elim in E. destruct E as [E1 E2]. 
                         rewrite E1 in D2. discriminate D2.

                         apply incomp_elim in E. destruct E as [E1 E2]. 
                         rewrite E2 in D1. discriminate D1. 
                         
                      destruct (H t) as [Q | [F G]].
                         assert (F := AC s B t Q). apply equiv_or_incomp_elim in F.
                         apply below_elim in D. destruct D as [D1 D2].
                         destruct F as [F | F]. 
                            apply equiv_elim in F. destruct F as [F1 F2]. 
                            rewrite F1 in D2. discriminate D2. 

                            apply incomp_elim in F. destruct F as [F1 F2]. 
                            rewrite F2 in D1. discriminate D1. 
                         
                         assert (I : w t << s).  exact (below_transitive _ lteS lteTrans _ _ _ G D).
                         apply below_elim in I. destruct I as [I K]. 
                         assert (J := AC s B (w t) F). apply equiv_or_incomp_elim in J.
                         destruct J as [J | J]. 
                            apply equiv_elim in J. destruct J as [J1 J2]. 
                            rewrite J1 in K. discriminate K.
                            apply incomp_elim in J. destruct J as [J1 J2]. 
                            rewrite J2 in I. discriminate I.
                      
                         
       apply set_equal_implies_minset_equal; auto. 
Qed.

Lemma bop_minset_union_enum_is_ann_right
      (BOTTOMS : finite_set S)
      (AC : is_antichain S eqS lteS BOTTOMS)
      (w : S → S)
      (H :  ∀ s : S, (s [in] BOTTOMS) + ((w s) [in] BOTTOMS * (w s) << s)) :
  ∀ X : finite_set S, (X <U> BOTTOMS) [=MS] BOTTOMS. 
Proof. intro X.
       assert (A := bop_minset_union_commutative X BOTTOMS).
       assert (B := bop_minset_union_enum_is_ann_left BOTTOMS AC w H X). 
       assert (C := brel_minset_transitive _ _ _ A B). 
       exact C.
Qed.        
                 
Lemma bop_minset_union_enum_is_ann_aux
      (BOTTOMS : finite_set S)
      (AC : is_antichain S eqS lteS BOTTOMS)
      (w : S → S)
      (H :  ∀ s : S, (s [in] BOTTOMS) + ((w s) [in] BOTTOMS * (w s) << s)) :
        bop_is_ann  _ [MSEQ] [MSU]  BOTTOMS. 
Proof. intro X. split. 
          (* (BOTTOMS <U> X) [=MS] BOTTOMS *) 
          apply (bop_minset_union_enum_is_ann_left BOTTOMS AC w H X). 
          (* (X <U> BOTTOMS) [=MS] BOTTOMS *)
          apply (bop_minset_union_enum_is_ann_right BOTTOMS AC w H X). 
Qed.


Lemma bop_minset_union_enum_is_ann (bf : bottoms_set_is_finite S eqS lteS) : 
  bop_is_ann _ [MSEQ] [MSU] (fst (projT1 bf)).
Proof. destruct bf as [[BOTTOMS w] [AC H]].
       apply (bop_minset_union_enum_is_ann_aux BOTTOMS AC w H).
Defined. 

Lemma bop_minset_union_exists_ann (bf : bottoms_set_is_finite S eqS lteS) : 
   bop_exists_ann _ [MSEQ] [MSU] .
Proof. exists (fst (projT1 bf)).
       apply (bop_minset_union_enum_is_ann bf). 
Defined. 

(* number 2 *) 


Lemma bop_minset_union_enum_is_ann_left2
      (BOTTOMS : finite_set S)
      (AC : is_antichain S eqS lteS BOTTOMS)
      (w : S → S)
      (H :  ∀ s : S, (w s) [in] BOTTOMS * (w s) << s)
      :
  ∀ X : finite_set S, (BOTTOMS <U> X) [=MS] BOTTOMS. 
Proof. intro X.
       assert (A : (BOTTOMS <U> X) [=S] BOTTOMS).
          apply brel_set_intro_prop; auto. split. 
             intros s B. unfold bop_minset_union in B. 
             apply in_minset_elim in B; auto. destruct B as [B C].
             apply in_set_bop_union_elim in B; auto. 
             destruct B as [B | B].
                exact B. 
                destruct (H s) as [E F].
                   assert (G : (w s) [in] (BOTTOMS [U] X)).
                      apply in_set_bop_union_intro; auto. 
                   assert (I := C (w s) G). apply below_false_elim in I.
                   destruct I as [I | I].
                      apply below_elim in F. destruct F as [F _]. 
                      rewrite I in F. discriminate F.

                      assert (J : w s << w s). exact (below_pseudo_transitive_right _ lteS lteTrans _ _ _ F I).
                      rewrite (below_not_reflexive S lteS (w s)) in J. discriminate J. 
                   
             intros s B. unfold bop_minset_union, bop_reduce. apply in_minset_intro; auto. split. 
                apply in_set_bop_union_intro; auto. 
                intros t C. case_eq(below lteS s t); intro D; auto. 
                   apply in_set_bop_union_elim in C; auto. 
                   destruct C as [C | C].
                      assert (E := AC s B t C). apply equiv_or_incomp_elim in E.
                      apply below_elim in D. destruct D as [D1 D2].                       
                      destruct E as [E | E].
                         apply equiv_elim in E. destruct E as [E1 E2]. 
                         rewrite E1 in D2. discriminate D2.

                         apply incomp_elim in E. destruct E as [E1 E2]. 
                         rewrite E2 in D1. discriminate D1. 
                         
                      destruct (H t) as [F G].
                         
                         assert (I : w t << s).  exact (below_transitive _ lteS lteTrans _ _ _ G D).
                         apply below_elim in I. destruct I as [I K]. 
                         assert (J := AC s B (w t) F). apply equiv_or_incomp_elim in J.
                         destruct J as [J | J]. 
                            apply equiv_elim in J. destruct J as [J1 J2]. 
                            rewrite J1 in K. discriminate K.
                            apply incomp_elim in J. destruct J as [J1 J2]. 
                            rewrite J2 in I. discriminate I.
                      
                         
       apply set_equal_implies_minset_equal; auto. 
Qed.


Lemma bop_minset_union_enum_is_ann_right2
      (BOTTOMS : finite_set S)
      (AC : is_antichain S eqS lteS BOTTOMS)
      (w : S → S)
      (H :  ∀ s : S, ((w s) [in] BOTTOMS * (w s) << s)) :
  ∀ X : finite_set S, (X <U> BOTTOMS) [=MS] BOTTOMS. 
Proof. intro X.
       assert (A := bop_minset_union_commutative X BOTTOMS).
       assert (B := bop_minset_union_enum_is_ann_left2 BOTTOMS AC w H X). 
       assert (C := brel_minset_transitive _ _ _ A B). 
       exact C.
Qed.        

Lemma bop_minset_union_enum_is_ann_aux2
      (BOTTOMS : finite_set S)
      (AC : is_antichain S eqS lteS BOTTOMS)
      (w : S → S)
      (H :  ∀ s : S, ((w s) [in] BOTTOMS * (w s) << s)) :
        bop_is_ann _ [MSEQ] [MSU] BOTTOMS. 
Proof. intro X. split. 
          (* (BOTTOMS <U> X) [=MS] BOTTOMS *) 
          apply (bop_minset_union_enum_is_ann_left2 BOTTOMS AC w H X). 
          (* (X <U> BOTTOMS) [=MS] BOTTOMS *)
          apply (bop_minset_union_enum_is_ann_right2 BOTTOMS AC w H X). 
Qed.

Lemma bop_minset_union_enum_is_ann2 (bf : bottoms_set_is_finite2 S eqS lteS) : 
  bop_is_ann _ [MSEQ] [MSU] (fst (projT1 bf)).
Proof. destruct bf as [[BOTTOMS w] [AC H]].
       apply (bop_minset_union_enum_is_ann_aux2 BOTTOMS AC w H).
Defined. 

Lemma bop_minset_union_not_exists_ann_aux (bnf : bottoms_set_not_is_finite S eqS lteS) : 
  ∀ X : finite_set S, {Z : finite_set S & (Z <U> X) [<>MS] X}.
Proof. intro X. destruct bnf as [F P].
       exists ((F ([ms] X)) :: nil).
       assert (Q := P ([ms] X) (uop_minset_is_antichain X)). destruct Q as [Q1 Q2].
       unfold brel_minset, brel_reduce. 
       case_eq(brel_set eqS ([ms] ((F ([ms] X) :: nil) <U> X)) ([ms] X)); intro A; auto.
       - apply brel_set_elim_prop in A; auto. destruct A as [A A'].
         assert (B : F ([ms] X) [in] ([ms] ((F ([ms] X) :: nil) <U> X))).
         { 
           apply in_minset_intro; auto. split. 
           unfold bop_minset_union, bop_reduce. 
           apply in_minset_intro; auto. split. 
           + apply in_set_bop_union_intro; auto. 
             * left. apply in_set_singleton_intro; auto. 
           + intros t B. apply in_set_bop_union_elim in B; auto. 
             destruct B as [B | B].
             * apply in_set_singleton_elim in B; auto. 
               apply symS in B. rewrite (below_congruence S eqS lteS lteCong _ _ _ _ (refS (F ([ms] X))) B). 
               apply (below_not_reflexive S lteS).
             * case_eq(in_set eqS ([ms] X) t); intro C.
               -- exact (Q2 t C).
               -- destruct (in_set_minset_false_elim _ eqS refS symS lteS lteCong lteRefl lteTrans _ _ B C) as [t' [D E]].
                  assert (G := Q2 _ D).
                  case_eq(below lteS (F ([ms] X)) t); intro H; auto.
                  rewrite (below_transitive _ lteS lteTrans _ _ _ E H) in G.
                  exact G. 
           +  unfold bop_minset_union, bop_reduce. 
              intros t D. 
              apply in_minset_elim in D; auto. destruct D as [D1 D2].
              apply in_set_bop_union_elim in D1; auto.
              destruct D1 as [D1 | D1]. 
              * apply in_set_singleton_elim in D1; auto. 
                apply symS in D1. rewrite (below_congruence S eqS lteS lteCong _ _ _ _ (refS (F ([ms] X))) D1). 
                apply (below_not_reflexive S lteS).
              * case_eq(in_set eqS ([ms] X) t); intro C.
               -- exact (Q2 t C).
               -- destruct (in_set_minset_false_elim _ eqS refS symS lteS lteCong lteRefl lteTrans _ _ D1 C) as [t' [D E]].
                  assert (G := Q2 _ D).
                  case_eq(below lteS (F ([ms] X)) t); intro H; auto.
                  rewrite (below_transitive _ lteS lteTrans _ _ _ E H) in G.
                  exact G. 
         }    
         assert (D := A _ B). rewrite D in Q1. discriminate Q1. 
Defined. 


       
Lemma bop_minset_union_not_exists_ann (bnf : bottoms_set_not_is_finite S eqS lteS) : 
  bop_not_exists_ann _ [MSEQ] [MSU].
Proof. intros X. 
       destruct (bop_minset_union_not_exists_ann_aux bnf X) as [Z A]. 
       exists Z. right. exact A. 
Defined. 


Definition bottoms_set_is_finite_decidable  (T : Type) (eq lte : brel T) :=
  (bottoms_set_is_finite T eq lte) + (bottoms_set_not_is_finite T eq lte).


Definition bop_minset_union_exists_ann_decide (bf_d : bottoms_set_is_finite_decidable S eqS lteS) :
      bop_exists_ann_decidable _ [MSEQ] [MSU]
 := match bf_d with
     | inl p  => inl (bop_minset_union_exists_ann p) 
     | inr p => inr (bop_minset_union_not_exists_ann p)
    end.


Lemma bop_minset_union_is_glb_wrt_lte_left : bop_is_glb (brel_lte_left [MSEQ] [MSU]) [MSU].
Proof. apply bop_is_glb_wrt_lte_left.
       apply brel_minset_reflexive; auto. 
       apply brel_minset_symmetric; auto. 
       apply brel_minset_transitive; auto. 
       apply bop_minset_union_associative; auto.
       apply bop_minset_union_congruence; auto.
       apply bop_minset_union_idempotent; auto.        
       apply bop_minset_union_commutative; auto.        
Qed. 

Lemma bop_union_is_lub_wrt_lte_right : bop_is_lub (brel_lte_right [MSEQ] [MSU]) [MSU].
Proof. apply bop_is_lub_wrt_lte_right. 
       apply brel_minset_reflexive; auto. 
       apply brel_minset_symmetric; auto. 
       apply brel_minset_transitive; auto. 
       apply bop_minset_union_associative; auto.
       apply bop_minset_union_congruence; auto. 
       apply bop_minset_union_idempotent; auto.        
       apply bop_minset_union_commutative; auto.        
Qed. 

End Theory.

Section ACAS.

Definition sg_CI_proofs_minset_union_from_po 
  (S : Type)
  (eqS lteS : brel S)
  (eqvS : eqv_proofs S eqS)
  (poS : po_proofs S eqS lteS) : 
        sg_CI_proofs (finite_set S) (brel_minset eqS lteS) (bop_minset_union eqS lteS)
:= 
let congS := A_eqv_congruence S eqS eqvS in  
let refS := A_eqv_reflexive S eqS eqvS in
let symS := A_eqv_symmetric S eqS eqvS in
let tranS := A_eqv_transitive S eqS eqvS in

let lteCong    := A_po_congruence S eqS lteS poS in
let lteRefl    := A_po_reflexive S eqS lteS poS in
let lteTran    := A_po_transitive S eqS lteS poS in
let lteAntiSym := A_po_antisymmetric S eqS lteS poS in 
let ntot       := A_po_not_total S eqS lteS poS in 
{|
  A_sg_CI_associative        := bop_minset_union_associative S eqS refS symS tranS lteS lteCong lteRefl lteTran 
; A_sg_CI_congruence         := bop_minset_union_congruence S eqS refS symS tranS lteS lteCong lteRefl lteTran
; A_sg_CI_commutative        := bop_minset_union_commutative S eqS refS symS tranS lteS lteCong lteRefl lteTran
; A_sg_CI_idempotent         := bop_minset_union_idempotent S eqS refS symS tranS lteS lteCong lteRefl lteTran
; A_sg_CI_not_selective      := bop_minset_union_not_selective S eqS refS symS tranS lteS lteCong lteRefl lteTran ntot 
|}. 

Definition A_sg_minset_union_from_po_with_bottom (S : Type) (A : A_po_with_bottom S) : A_sg_CI (finite_set S) := 
  let eqvS := A_po_with_bottom_eqv S A in
  let botP := A_po_with_bottom_exists_bottom S A in 
  let eqP  := A_eqv_proofs _ eqvS in
  let congS := A_eqv_congruence _ _ eqP in    
  let refS := A_eqv_reflexive _ _ eqP in
  let symS := A_eqv_symmetric _ _ eqP in
  let tranS := A_eqv_transitive _ _ eqP in
  let eq   := A_eqv_eq _ eqvS in  
  let lteS := A_po_with_bottom_lte _ A in
  let poP  := A_po_with_bottom_proofs _ A in
  let lteCong    := A_po_congruence _ _ _ poP in
  let lteRefl    := A_po_reflexive _ _ _ poP in
  let lteTran    := A_po_transitive _ _ _ poP in
  let anti       := A_po_antisymmetric _ _ _ poP in
  {| 
     A_sg_CI_eqv          := A_eqv_minset_from_po S (A_po_from_po_with_bottom A)
   ; A_sg_CI_bop          := bop_minset_union eq lteS
   ; A_sg_CI_exists_id_d  := inl (bop_minset_union_exists_id S eq refS symS tranS lteS lteCong lteRefl lteTran)
   ; A_sg_CI_exists_ann_d := inl (bop_minset_union_exists_ann_with_antisymmetry S eq refS symS tranS lteS lteCong lteRefl lteTran anti botP)
   ; A_sg_CI_proofs       := sg_CI_proofs_minset_union_from_po S eq lteS eqP poP 
   ; A_sg_CI_ast          := Ast_sg_minset_union (A_po_with_bottom_ast S A)                                                                   
  |}.

Definition sg_C_proofs_minset_union_from_qo 
 (S : Type) (eqS lteS : brel S) (s : S) (f : S -> S) 
 (ntS : brel_not_trivial S eqS f)     
 (eqvS : eqv_proofs S eqS)
 (qoS : qo_proofs S eqS lteS) : 
        sg_C_proofs (finite_set S) (brel_minset eqS lteS) (bop_minset_union eqS lteS) := 
let congS := A_eqv_congruence S eqS eqvS in  
let refS := A_eqv_reflexive S eqS eqvS in
let symS := A_eqv_symmetric S eqS eqvS in
let tranS := A_eqv_transitive S eqS eqvS in
let lteCong    := A_qo_congruence S eqS lteS qoS in
let lteRefl    := A_qo_reflexive S eqS lteS qoS in
let lteTran    := A_qo_transitive S eqS lteS qoS in
let anti_d     := A_qo_antisymmetric_d S eqS lteS qoS in 
let tot_d      := A_qo_total_d S eqS lteS qoS in 
{|
  A_sg_C_associative   := bop_minset_union_associative S eqS refS symS tranS lteS lteCong lteRefl lteTran 
; A_sg_C_congruence    := bop_minset_union_congruence S eqS refS symS tranS lteS lteCong lteRefl lteTran
; A_sg_C_commutative   := bop_minset_union_commutative S eqS refS symS tranS lteS lteCong lteRefl lteTran
; A_sg_C_idempotent_d  := inl (bop_minset_union_idempotent S eqS refS symS tranS lteS lteCong lteRefl lteTran) 
; A_sg_C_selective_d   := bop_minset_union_selective_decide_v2 S eqS refS symS tranS lteS lteCong lteRefl lteTran tot_d anti_d
; A_sg_C_anti_left_d   := inr (bop_minset_union_not_anti_left S eqS lteS)
; A_sg_C_anti_right_d  := inr (bop_minset_union_not_anti_right S eqS lteS)
; A_sg_C_cancel_d      := inr (bop_minset_union_not_left_cancellative S eqS s refS symS tranS lteS lteCong lteRefl lteTran tot_d anti_d)
; A_sg_C_constant_d    := inr (bop_minset_union_not_left_constant S eqS s f ntS lteS )
|}.


Definition A_sg_minset_union_from_qo_with_bottom (S : Type) (A : @A_qo_with_bottom S) : A_sg_C (finite_set S) := 
  let eqvS := A_qo_with_bottom_eqv S A in
  let botP := A_qo_with_bottom_exists_bottom S A in 
  let eqP  := A_eqv_proofs _ eqvS in
  let congS := A_eqv_congruence _ _ eqP in    
  let refS := A_eqv_reflexive _ _ eqP in
  let symS := A_eqv_symmetric _ _ eqP in
  let tranS := A_eqv_transitive _ _ eqP in
  let eq   := A_eqv_eq _ eqvS in  
  let s    := A_eqv_witness _ eqvS in
  let f    := A_eqv_new _ eqvS in
  let ntS  := A_eqv_not_trivial _ eqvS in
  let lteS := A_qo_with_bottom_lte _ A in
  let poP  := A_qo_with_bottom_proofs _ A in
  let lteCong    := A_qo_congruence _ _ _ poP in
  let lteRefl    := A_qo_reflexive _ _ _ poP in
  let lteTran    := A_qo_transitive _ _ _ poP in
  {| 
     A_sg_C_eqv          := A_eqv_minset_from_qo S (A_qo_from_qo_with_bottom A)
   ; A_sg_C_bop          := bop_minset_union eq lteS
   ; A_sg_C_exists_id_d  := inl (bop_minset_union_exists_id S eq refS symS tranS lteS lteCong lteRefl lteTran)
   ; A_sg_C_exists_ann_d := inl (bop_minset_union_exists_ann_without_antisymmetry S eq refS symS tranS lteS lteCong lteRefl lteTran botP)
   ; A_sg_C_proofs       := sg_C_proofs_minset_union_from_qo S eq lteS s f ntS eqP poP 
   ; A_sg_C_ast          := Ast_sg_minset_union (A_qo_with_bottom_ast S A)                                                                   
  |}.

End ACAS.

Section AMCAS.

  Open Scope string_scope.

  Definition A_minset_union_from_below_po_with_bottom {S : Type} (A : @A_below_po_with_bottom S) := 
    A_classify_sg_CI (A_sg_minset_union_from_po_with_bottom _ (A_cast_up_po_with_bottom A)).  

  Definition A_minset_union_from_below_qo_with_bottom {S : Type} (A : @A_below_qo_with_bottom S) := 
    A_classify_sg_C (A_sg_minset_union_from_qo_with_bottom _ (A_cast_up_qo_with_bottom A)).  

  Definition A_mcas_sg_minset_union {S : Type} (A : @A_qo_mcas S)  : @A_sg_mcas (finite_set S) :=
    match A with
    | A_MCAS_qo A' =>
        match A_cast_qo_down_to_po_with_bottom A' with
        | Some powb => A_MCAS_sg (A_Below_sg_sg_C (A_Below_sg_C_sg_CI (A_minset_union_from_below_po_with_bottom powb)))
        | None      =>
            match A_cast_qo_down_to_qo_with_bottom A' with
            | Some qowb => A_MCAS_sg (A_Below_sg_sg_C (A_minset_union_from_below_qo_with_bottom qowb))
            | None      => A_MCAS_sg_Error ("minset_union : must have a bottom (a least element)." :: nil)
            end 
        end 
    | A_MCAS_qo_Error sl => A_MCAS_sg_Error sl
    end.
  
End AMCAS.   

Section CAS.

  
Definition assert_minset_union_not_selective {S : Type} (ntot : @assert_not_total S) : @assert_not_selective (finite_set S)
  := match ntot with
     | Assert_Not_Total (s, t) => Assert_Not_Selective (s :: nil, t :: nil)
     end.

Definition  assert_minset_union_not_selective_from_not_antisymmetric {S : Type} (nanti : @assert_not_antisymmetric S) : @assert_not_selective (finite_set S)
  := match nanti with
     | Assert_Not_Antisymmetric (s, t) => Assert_Not_Selective (s :: nil, t :: nil)
     end.

Definition bop_minset_union_selective_certify_v1 {S : Type} (tot_d : @certify_total S) : 
      @check_selective (finite_set S) 
 := match tot_d with
     | Certify_Total  => Certify_Selective 
     | Certify_Not_Total (s1, s2) => Certify_Not_Selective (s1 :: nil, s2 :: nil)
    end.

Definition bop_minset_union_selective_certify_v2 {S : Type}
           (tot_d : @certify_total S)
           (anti_d : @certify_antisymmetric S): 
  @check_selective (finite_set S) 
:= match anti_d with
   | Certify_Antisymmetric => bop_minset_union_selective_certify_v1 tot_d
   | Certify_Not_Antisymmetric (s1, s2) => Certify_Not_Selective (s1 :: nil, s2 :: nil)
   end. 


Definition sg_C_certs_minset_union_from_qo 
 {S : Type} (eqS lteS : brel S) (wS : S) (f : S -> S) 
 (qoS : @qo_certificates S) : 
        @sg_C_certificates (finite_set S) := 
let anti_d     := qo_antisymmetric_d qoS in 
let tot_d      := qo_total_d qoS in
let sel_d      := bop_minset_union_selective_certify_v2 tot_d anti_d in
let b := bop_minset_union eqS lteS in
let r := brel_minset eqS lteS in 
{|
  sg_C_associative   := Assert_Associative  
; sg_C_congruence    := Assert_Bop_Congruence  
; sg_C_commutative   := Assert_Commutative  
; sg_C_idempotent_d  := Certify_Idempotent
; sg_C_selective_d   := sel_d
; sg_C_anti_left_d   := Certify_Not_Anti_Left (nil, nil) 
; sg_C_anti_right_d  := Certify_Not_Anti_Right (nil, nil)
(*the next is lacking in abstraction.  FIX THIS *) 
; sg_C_cancel_d      := match sel_d with
                        | Certify_Selective =>
                            Certify_Not_Left_Cancellative (cef_selective_and_commutative_imply_not_left_cancellative r b nil (brel_minset_new _ eqS wS))
                        | Certify_Not_Selective (X, Y) =>
                            Certify_Not_Left_Cancellative (cef_idempotent_and_commutative_and_not_selective_imply_not_left_cancellative b X Y)
                        end 
; sg_C_constant_d    := Certify_Not_Left_Constant (nil, ((wS :: nil), (f wS) ::nil))
|}.

Definition sg_CI_certs_minset_union_from_po : ∀ {S : Type},  @po_certificates S -> @sg_CI_certificates (finite_set S)
:= λ {S} po,  
{|
  sg_CI_associative        := Assert_Associative  
; sg_CI_congruence         := Assert_Bop_Congruence  
; sg_CI_commutative        := Assert_Commutative  
; sg_CI_idempotent         := Assert_Idempotent  
; sg_CI_not_selective      := assert_minset_union_not_selective (po_not_total po)
|}.


Definition sg_minset_union_from_po_with_bottom {S : Type} (A : @po_with_bottom S) : @sg_CI (finite_set S) := 
  let eqvS := po_with_bottom_eqv A   in
  let lteS := po_with_bottom_lte A   in     
  let eq   := eqv_eq eqvS in  

   {| 
     sg_CI_eqv           := eqv_minset_from_po (po_from_po_with_bottom A)
   ; sg_CI_bop           := bop_minset_union eq lteS 
   ; sg_CI_exists_id_d     := Certify_Exists_Id nil 
   ; sg_CI_exists_ann_d    := match po_with_bottom_exists_bottom A with
                             | Assert_Exists_Bottom b => Certify_Exists_Ann (b :: nil)
                             end 
   ; sg_CI_certs         := sg_CI_certs_minset_union_from_po (po_with_bottom_certs A)
   ; sg_CI_ast           := Ast_sg_minset_union (po_with_bottom_ast A)                                                                   
   |}.

Definition sg_minset_union_from_qo_with_bottom {S : Type} (A : @qo_with_bottom S) : @sg_C (finite_set S) := 
  let eqvS := qo_with_bottom_eqv A   in
  let eq   := eqv_eq eqvS in
  let wS   := eqv_witness eqvS in
  let f   := eqv_new eqvS in  
  let lteS := qo_with_bottom_lte A   in   
   {| 
     sg_C_eqv           := eqv_minset_from_qo (qo_from_qo_with_bottom A)
   ; sg_C_bop           := bop_minset_union eq lteS 
   ; sg_C_exists_id_d   := Certify_Exists_Id nil 
   ; sg_C_exists_ann_d  := match qo_with_bottom_exists_bottom A with
                             | Assert_Exists_Qo_Bottom b => Certify_Exists_Ann (b :: nil)
                             end 
   ; sg_C_certs         := sg_C_certs_minset_union_from_qo eq lteS wS f (qo_with_bottom_certs A)
   ; sg_C_ast           := Ast_sg_minset_union (qo_with_bottom_ast A)                                                                   
   |}.


End CAS.

Section MCAS.


  Open Scope string_scope.

  Definition minset_union_from_below_po_with_bottom {S : Type} (A : @below_po_with_bottom S) := 
    classify_sg_CI (sg_minset_union_from_po_with_bottom (cast_up_po_with_bottom A)).

  Definition minset_union_from_below_qo_with_bottom {S : Type} (A : @below_qo_with_bottom S) := 
    classify_sg_C (sg_minset_union_from_qo_with_bottom (cast_up_qo_with_bottom A)).  


  Definition mcas_sg_minset_union {S : Type} (A : @qo_mcas S)  : @sg_mcas (finite_set S) :=
    match A with
    | MCAS_qo A' =>
        match cast_qo_down_to_po_with_bottom A' with
        | Some powb => MCAS_sg (Below_sg_sg_C (Below_sg_C_sg_CI (minset_union_from_below_po_with_bottom powb)))
        | None      =>
            match cast_qo_down_to_qo_with_bottom A' with
            | Some qowb => MCAS_sg (Below_sg_sg_C (minset_union_from_below_qo_with_bottom qowb))
            | None      => MCAS_sg_Error ("minset_union : must have a bottom (a least element)." :: nil)
            end 
            
        end 
    | MCAS_qo_Error sl => MCAS_sg_Error sl
    end.

End MCAS.   



Section Verify.

Lemma bop_minset_union_from_po_certs_correct 
      (S : Type) (eq lte : brel S) (eqv : eqv_proofs S eq) (po : po_proofs S eq lte) : 
      sg_CI_certs_minset_union_from_po (P2C_po eq lte po) 
      =                        
      P2C_sg_CI (brel_minset eq lte) (bop_minset_union eq lte)
                (sg_CI_proofs_minset_union_from_po S eq lte eqv po).
Proof. destruct eqv, po. 
       unfold sg_CI_certs_minset_union_from_po, sg_CI_proofs_minset_union_from_po, P2C_sg_CI, P2C_po; simpl.
       destruct A_po_not_total as [[a b] [L R]]; simpl; reflexivity. 
Qed. 

Lemma bop_minset_union_from_qo_certs_correct 
  (S : Type) (eq lte : brel S) (s : S) (f : S -> S)
  (nt : brel_not_trivial S eq f)
  (eqv : eqv_proofs S eq)
  (qo : qo_proofs S eq lte) : 
      sg_C_certs_minset_union_from_qo eq lte s f (P2C_qo eq lte qo) 
      =                        
      P2C_sg_C (brel_minset eq lte)
               (bop_minset_union eq lte)
               (sg_C_proofs_minset_union_from_qo S eq lte s f nt eqv qo).
Proof. destruct eqv, qo. 
       unfold sg_C_certs_minset_union_from_qo, sg_C_proofs_minset_union_from_qo, P2C_sg_C, P2C_qo; simpl.
       destruct A_qo_antisymmetric_d as [A | [[c d] [[A B] C]]];
       destruct A_qo_total_d as [tot | [[a b] [D E]]]; simpl; 
       try reflexivity. 
Qed. 


Theorem correct_sg_minset_union_from_po_with_bottom (S : Type) (A : A_po_with_bottom S) : 
  sg_minset_union_from_po_with_bottom (A2C_po_with_bottom A)
  =
  A2C_sg_CI (A_sg_minset_union_from_po_with_bottom S A). 
Proof. unfold sg_minset_union_from_po_with_bottom, A_sg_minset_union_from_po_with_bottom, A2C_sg_CI; simpl.
       rewrite <- bop_minset_union_from_po_certs_correct.       
       destruct A_po_with_bottom_exists_bottom as [b P]. simpl. 
       unfold bop_minset_union_exists_ann_with_antisymmetry. 
       rewrite <- correct_eqv_minset_from_po.
       destruct A. unfold A2C_po_with_bottom;
       reflexivity. 
Qed.

Theorem correct_sg_minset_union_from_qo_with_bottom (S : Type) (A : A_qo_with_bottom S) : 
  sg_minset_union_from_qo_with_bottom (A2C_qo_with_bottom A)
  =
  A2C_sg_C (A_sg_minset_union_from_qo_with_bottom S A). 
Proof. unfold sg_minset_union_from_qo_with_bottom, A_sg_minset_union_from_qo_with_bottom, A2C_sg_C; simpl.
       rewrite <- bop_minset_union_from_qo_certs_correct.       
       destruct A_qo_with_bottom_exists_bottom as [b [P Q]]. simpl.
       rewrite correct_qo_from_qo_with_bottom. 
       rewrite correct_eqv_minset_from_qo. 
       reflexivity. 
Qed.

Theorem correct_minset_union_from_below_po_with_bottom (S : Type) (A : @A_below_po_with_bottom S) : 
  minset_union_from_below_po_with_bottom (A2C_below_po_with_bottom A)
  =
  A2C_below_sg_CI (A_minset_union_from_below_po_with_bottom A). 
Proof. unfold A_minset_union_from_below_po_with_bottom,
         minset_union_from_below_po_with_bottom. 
       rewrite cast_up_po_with_bottom_A2C_commute.
       rewrite correct_sg_minset_union_from_po_with_bottom.
       rewrite correct_classify_sg_CI.
       reflexivity. 
 Qed.


Theorem correct_minset_union_from_below_qo_with_bottom (S : Type) (A : @A_below_qo_with_bottom S) : 
  minset_union_from_below_qo_with_bottom (A2C_below_qo_with_bottom A)
  =
  A2C_below_sg_C (A_minset_union_from_below_qo_with_bottom A). 
Proof. unfold A_minset_union_from_below_qo_with_bottom,
         minset_union_from_below_qo_with_bottom. 
       rewrite cast_up_qo_with_bottom_A2C_commute.
       rewrite correct_sg_minset_union_from_qo_with_bottom.
       rewrite correct_classify_sg_C. 
       reflexivity. 
 Qed.



Theorem correct_mcas_sg_minset_union (S : Type) (A : @A_qo_mcas S): 
         mcas_sg_minset_union (A2C_qo_mcas A)  
         = 
         A2C_sg_mcas (A_mcas_sg_minset_union A).
Proof. destruct A; simpl; unfold A_mcas_sg_minset_union, A_mcas_sg_minset_union; simpl; try reflexivity.
       rewrite correct_cast_qo_down_to_po_with_bottom.
       destruct (A_cast_qo_down_to_po_with_bottom a); simpl. 
       - rewrite correct_minset_union_from_below_po_with_bottom.
         reflexivity.
       - rewrite correct_cast_qo_down_to_qo_with_bottom.
         destruct (A_cast_qo_down_to_qo_with_bottom a); simpl;
           try reflexivity.
         rewrite correct_minset_union_from_below_qo_with_bottom. 
         reflexivity.                                                              
Qed.  


End Verify.   
