Require Import Coq.Strings.String.
Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.

Require Import CAS.coq.theory.set.

Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.eqv.theory.
Require Import CAS.coq.eqv.set.
Require Import CAS.coq.eqv.reduce.
Require Import CAS.coq.eqv.minset.

Require Import CAS.coq.po.properties.
Require Import CAS.coq.po.structures.
Require Import CAS.coq.po.theory.

Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures.
Require Import CAS.coq.sg.theory. 
Require Import CAS.coq.sg.lift.
Require Import CAS.coq.sg.reduce.
Require Import CAS.coq.sg.classify.
Require Import CAS.coq.sg.cast_up. 

Require Import CAS.coq.os.properties.
Require Import CAS.coq.os.structures.
Require Import CAS.coq.os.cast_up. 


Section Theory.

Variable S  : Type. 
Variable rS : brel S.

Variable wS : S.
Variable f : S -> S.                
Variable Pf : brel_not_trivial S rS f. 

Variable congS : brel_congruence S rS rS. 
Variable refS  : brel_reflexive S rS.
Variable symS  : brel_symmetric S rS.  
Variable tranS : brel_transitive S rS.

Variable lteS : brel S.
Variable lteCong : brel_congruence S rS lteS.
Variable lteRefl : brel_reflexive S lteS.
Variable lteTrans : brel_transitive S lteS.
(* NB : anti-symmetry is not assumed *) 

Variable bS : binary_op S. 
Variable bCong : bop_congruence S rS bS. 
Variable bAss : bop_associative S rS bS.

Definition bop_minset_lift : binary_op (finite_set S)
  := bop_reduce (uop_minset lteS) (bop_lift rS bS).


Notation "a [=] b"  := (rS a b = true)          (at level 15).
Notation "a [<>] b" := (rS a b = false)         (at level 15).
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


Notation "a [in] b"  := (in_set rS b a = true)   (at level 15).
Notation "a [!in] b" := (in_set rS b a = false)  (at level 15).

Notation "a [=S] b"   := (brel_set rS a b = true)         (at level 15).
Notation "a [<>S] b"  := (brel_set rS a b = false)        (at level 15).
Notation "a [=MS] b"  := (brel_minset rS lteS a b = true)        (at level 15).
Notation "a [<>MS] b" := (brel_minset rS lteS a b = false)       (at level 15).
Notation "[ms] x" := (uop_minset lteS x) (at level 15).

Notation "a [^] b" := (bop_lift rS bS a b)         (at level 15).
Notation "a <^> b" := (bop_minset_lift a b)         (at level 15).

Definition set_transitive := brel_set_transitive S rS refS symS tranS.
Definition set_symmetric := brel_set_symmetric S rS.
Definition set_reflexive := brel_set_reflexive S rS refS symS.
Definition minset_idempotent := uop_minset_idempotent S rS refS symS tranS lteS lteCong lteRefl. 
Definition minset_transitive := brel_minset_transitive S rS refS symS tranS lteS.
Definition minset_symmetric := brel_minset_symmetric S rS lteS.
Definition minset_reflexive := brel_minset_reflexive S rS refS symS lteS.
Definition uop_minset_congruence_weak := uop_minset_congruence_weak _ _ refS symS tranS lteS lteCong lteRefl lteTrans. 
Definition uop_minset_congruence := uop_minset_congruence S rS refS symS tranS lteS lteCong.
Definition brel_minset_congruence_weak := brel_minset_congruence_weak S rS refS symS tranS lteS lteCong lteRefl lteTrans.
Definition brel_minset_congruence := brel_minset_congruence S rS refS symS tranS lteS lteCong lteRefl lteTrans.
Definition uop_minset_idempotent := uop_minset_idempotent _ _ refS symS tranS lteS lteCong lteRefl. 
Definition bop_lift_congruence := bop_lift_congruence _ _ bS refS tranS symS bCong. 
Definition bop_lift_associative := bop_lift_associative _ _ bS refS tranS symS bCong bAss. 
Definition set_equal_implies_minset_equal := set_equal_implies_minset_equal S rS refS symS tranS lteS lteCong lteRefl lteTrans.
Definition below_pseudo_transitive_left := below_pseudo_transitive_left S lteS lteTrans. 
Definition below_pseudo_transitive_right := below_pseudo_transitive_right S lteS lteTrans.
Definition uop_minset_is_antichain := uop_minset_is_antichain S rS refS symS lteS lteCong lteRefl. 

Lemma uop_minset_equational_idempotence (X Y : finite_set S): 
  ([ms] ([ms] X)) [=S] ([ms] ([ms] Y)) -> ([ms] X) [=S] ([ms] Y). 
Proof. intro A.
       assert (B := minset_idempotent X). 
       assert (C := minset_idempotent Y).
       apply set_symmetric in B. 
       assert (D := set_transitive _ _ _ B A). 
       exact (set_transitive _ _ _ D C).        
Qed. 

Lemma simplify_minset_lift_minset_eq (X Y Z : finite_set S) :
    ((X <^> Y) [=MS] Z) -> ([ms] (X [^] Y)) [=S] ([ms] Z).
Proof. intro H.
       unfold brel_minset in H.
       unfold brel_reduce in H.
       apply brel_set_elim_prop in H; auto.
       destruct H as [L R].
       apply brel_set_intro_prop; auto. split.
       - intros s A.
         assert (B : s [in] ([ms] (X <^> Y))).
         {
           unfold bop_minset_lift.
           unfold bop_reduce.
           assert (C := uop_minset_idempotent (X [^] Y)).
           rewrite (in_set_left_congruence S rS symS tranS s _ _ C).
           exact A. 
         }
         exact (L _ B). 
       - intros s A.
         assert (B := R _ A).
         apply in_minset_elim in B; auto.
         destruct B as [B _].
         exact B. 
Qed. 





Lemma minset_lift_right_inclusion_1
      (RM : os_right_monotone lteS bS) 
      (DDD : (brel_antisymmetric S rS lteS) +
               ((os_left_strictly_monotone lteS bS) * (os_right_strictly_monotone lteS bS)))
      (X Y : finite_set S)
      (a : S)
      (H : a [in] ([ms] (X [^] Y))) :  a [in] ([ms] (([ms] X) [^] Y)).
Proof. apply in_minset_elim in H; auto. destruct H as [H1 H2].
        apply in_set_bop_lift_elim in H1; auto.
        destruct H1 as [x [y [[H3 H4] H5]]]. 
        apply in_minset_intro; auto. split.
        - apply symS in H5. 
          rewrite (in_set_right_congruence S rS symS tranS (bS x y) a (([ms] X) [^] Y) H5);auto.
          case_eq(in_set rS ([ms] X) x); intro H6.
          + apply in_set_bop_lift_intro; auto. 
          + assert (B := H6). 
            apply in_set_minset_false_elim in B; auto.
            destruct B as [s [H7 H8]]. apply below_elim in H8.  destruct H8 as [H8 H9].
            assert (R := RM y _ _ H8).
            case_eq (lteS (bS x y) (bS s y)) ; intro H10.
            * assert (H7' := H7). 
              apply in_minset_elim in H7; auto. 
              destruct H7 as [H7 H7'']. 
              assert (H : (bS s y) [in] (X [^] Y)). apply in_set_bop_lift_intro; auto. 
              assert (H11 := H2 _ H). 
              apply symS in H5.
              rewrite(below_congruence _ _ _ lteCong _ _ _ _ H5 (refS (bS s y))) in H11.
              apply below_false_elim in H11. 
              destruct H11 as [H11 | H11].
              -- rewrite H11 in R. discriminate R.
              -- destruct DDD as [AntiSym | [_ RSM]] .
                 (* AntiSym *) 
                 ++ assert (G := AntiSym _ _ R H10).
                    rewrite (in_set_right_congruence S rS symS tranS _  _ (([ms] X) [^] Y) G); auto. 
                    apply in_set_bop_lift_intro; auto.
                 (* RSM *) 
                 ++ destruct (RSM y  _  _ H8 H9) as [H12 H13].
                    rewrite H13 in H10. discriminate H10. 
            * assert (H11 : bS s y [in] (X [^] Y)).
              apply in_set_bop_lift_intro; auto.
              apply in_minset_elim in H7; auto.                     
              destruct H7 as [H7 _]; auto. 
              assert (Q := H2 (bS s y) H11). apply below_false_elim in Q.
              destruct Q as [H12 | H12]. 
              -- apply symS in H5. rewrite (lteCong _ _ _ _ (refS (bS s y)) H5) in H12.
                 rewrite H12 in R. discriminate R. 
              -- apply symS in H5. rewrite (lteCong _ _ _ _ H5 (refS (bS s y))) in H12.
                 rewrite H12 in H10. discriminate H10.                    
           - intros s H6.  apply H2. 
             apply in_set_bop_lift_elim in H6; auto.
             destruct H6 as [x' [y' [[H7 H8] H9]]].
             apply symS in H9. 
             rewrite (in_set_right_congruence S rS symS tranS (bS x' y') s (X [^] Y) H9);auto. 
             apply in_set_bop_lift_intro; auto.
             apply in_minset_elim in H7; auto. destruct H7 as [H7 _]; auto. 
Qed.            


(* nb : this did not use strictness or antisym *) 
Lemma minset_lift_right_inclusion_2
      (RM : os_right_monotone lteS bS) 
      (X Y : finite_set S)
      (a : S)
      (H : a [in] ([ms] (([ms] X) [^] Y))) : a [in] ([ms] (X [^] Y)).
Proof. apply in_minset_elim in H; auto. destruct H as [H1 H2].
        apply in_set_bop_lift_elim in H1; auto.
        destruct H1 as [x [y [[H3 H4] H5]]]. 
        apply in_minset_intro; auto. split.
           apply in_minset_elim in H3; auto.
           destruct H3 as [H3 _].
           apply symS in H5. rewrite (in_set_right_congruence S rS symS tranS (bS x y) a (X [^] Y) H5);auto. 
           apply in_set_bop_lift_intro; auto. 

           intros s H6.
           apply in_set_bop_lift_elim in H6; auto. 
           destruct H6 as [b [ c [[H7 H8] H9]]].
           case_eq(in_set rS ([ms] X) b); intro H10. 
              apply H2.               
              apply symS in H9. rewrite (in_set_right_congruence S rS symS tranS (bS b c) s (([ms] X) [^] Y) H9);auto.
              apply in_set_bop_lift_intro; auto.
              apply in_set_minset_false_elim in H10; auto.
              destruct H10 as [b' [H11 H12]]. apply below_elim in H12. destruct H12 as [H12 H13].
              assert (H14 := RM c _ _ H12).
              assert (A : (bS b' c) [in] (([ms] X) [^] Y)).
                 apply in_set_bop_lift_intro; auto. 
              assert (B := H2 (bS b' c) A).
              case_eq(below lteS a s); intro C; auto. 
              apply below_false_elim in B. 
              rewrite(below_congruence _ _ _ lteCong _ _ _ _ H5 H9) in C.
              rewrite (lteCong _ _ _ _ (refS (bS b' c)) H5) in B. 
              rewrite (lteCong _ _ _ _ H5 (refS (bS b' c))) in B.               
              destruct B as [B | B].              
                 assert (D := below_pseudo_transitive_left _ _ _ H14 C). 
                 apply below_elim in D. destruct D as [D E].
                 rewrite D in B. discriminate B. 
                 assert (D := below_pseudo_transitive_right _ _ _ C B). 
                 apply below_elim in D. destruct D as [D E].
                 rewrite E in H14. discriminate H14. 
Qed.

  Lemma lift_left_minset_invariant
    (RM : os_right_monotone lteS bS) 
    (DDD : (brel_antisymmetric S rS lteS) +
             ((os_left_strictly_monotone lteS bS)
              *
             (os_right_strictly_monotone lteS bS))) :
  bop_left_uop_invariant
    (finite_set S)
    (brel_set rS)
    (bop_reduce (uop_minset lteS) (bop_lift rS bS))
    (uop_minset lteS).
Proof. intros X Y.
       unfold bop_reduce.
       (* ([ms] (([ms] X) [^] Y)) [=S] ([ms] (X [^] Y)) *)
       apply brel_set_intro_prop; auto. split.
       apply minset_lift_right_inclusion_2; auto.        
       apply minset_lift_right_inclusion_1; auto.        
Qed. 

Lemma minset_lift_left_inclusion_1
      (LM : os_left_monotone lteS bS) 
      (DDD : (brel_antisymmetric S rS lteS) +
               ((os_left_strictly_monotone lteS bS) * (os_right_strictly_monotone lteS bS)))
      (X Y : finite_set S)
      (a : S)
      (H : a [in] ([ms] (X [^] Y))) : a [in] ([ms] (X [^] ([ms] Y))).
Proof. apply in_minset_elim in H; auto. destruct H as [H1 H2].
        apply in_set_bop_lift_elim in H1; auto.
        destruct H1 as [x [y [[H3 H4] H5]]]. 
        apply in_minset_intro; auto. split.
            apply symS in H5. 
           rewrite (in_set_right_congruence S rS symS tranS (bS x y) a (X [^] ([ms] Y)) H5);auto.
           case_eq(in_set rS ([ms] Y) y); intro H6.
              apply in_set_bop_lift_intro; auto. 
              assert (B := H6). 
              apply in_set_minset_false_elim in B; auto.
              destruct B as [s [H7 H8]]. apply below_elim in H8. destruct H8 as [H8 H9]. 
              assert (R := LM x _ _ H8).
              case_eq (lteS (bS x y) (bS x s)) ; intro H10.
                 destruct DDD as [AntiSym | [LSM _]].
                    (* AntiSym *) 
                    assert (G := AntiSym _ _ R H10).
                    rewrite (in_set_right_congruence S rS symS tranS _  _ (X [^] ([ms] Y)) G); auto. 
                    apply in_set_bop_lift_intro; auto. unfold os_left_strictly_monotone in LSM.
                    (* LSM *) 
                  destruct (LSM x  _  _ H8 H9) as [H11 H12].
                  rewrite H12 in H10. discriminate H10. 
                    
                 assert (H11 : bS x s [in] (X [^] Y)).
                    apply in_set_bop_lift_intro; auto.
                    apply in_minset_elim in H7; auto.                     
                    destruct H7 as [H7 _]; auto.
                 assert (Q := H2 (bS x s) H11). 
                 apply below_false_elim in Q. 
                 destruct Q as [H12 | H12]. 
                    apply symS in H5. rewrite (lteCong _ _ _ _ (refS (bS x s)) H5) in H12.
                    rewrite H12 in R. discriminate R.
                    rewrite (lteCong _ _ _ _ (symS _ _ H5) (refS (bS x s))) in H12.
                    rewrite H12 in H10. discriminate H10.
           intros s H6.  apply H2. 
           apply in_set_bop_lift_elim in H6; auto.
           destruct H6 as [x' [y' [[H7 H8] H9]]].
           apply symS in H9. 
           rewrite (in_set_right_congruence S rS symS tranS (bS x' y') s (X [^] Y) H9);auto. 
           apply in_set_bop_lift_intro; auto.
           apply in_minset_elim in H8; auto. destruct H8 as [H8 _]; auto. 
Qed.            

(* nb : this did not use strictness or antisym *) 
Lemma minset_lift_left_inclusion_2
      (LM : os_left_monotone lteS bS)
      (X Y : finite_set S) (a : S) (H : a [in] ([ms] (X [^] ([ms] Y)))) : 
  a [in] ([ms] (X [^] Y)).
Proof. apply in_minset_elim in H; auto. destruct H as [H1 H2].
        apply in_set_bop_lift_elim in H1; auto.
        destruct H1 as [x [y [[H3 H4] H5]]]. 
        apply in_minset_intro; auto. split.
           apply in_minset_elim in H4; auto.
           destruct H4 as [H4 _].
           apply symS in H5. rewrite (in_set_right_congruence S rS symS tranS (bS x y) a (X [^] Y) H5);auto. 
           apply in_set_bop_lift_intro; auto. 

           intros s H6.
           apply in_set_bop_lift_elim in H6; auto. 
           destruct H6 as [b [ c [[H7 H8] H9]]].
           case_eq(in_set rS ([ms] Y) c); intro H10. 
              apply H2.               
              apply symS in H9. rewrite (in_set_right_congruence S rS symS tranS (bS b c) s (X [^] ([ms] Y)) H9);auto.
              apply in_set_bop_lift_intro; auto.
              apply in_set_minset_false_elim in H10; auto.
              destruct H10 as [c' [H11 H12]]. apply below_elim in H12. destruct H12 as [H12 H13].
              assert (H14 := LM b _ _ H12).
              assert (A : (bS b c') [in] (X [^] ([ms] Y))).
                 apply in_set_bop_lift_intro; auto. 
              assert (B := H2 (bS b c') A).
              rewrite (below_congruence _ _ _ lteCong _ _ _ _ H5 (refS (bS b c'))) in B.                 
              apply below_false_elim in B.
              destruct B as [B | B].
                 rewrite (below_congruence _ _ _ lteCong _ _ _ _ H5 H9). 
                 case_eq(below lteS (bS x y) (bS b c) ); intro D; auto. 
                    assert (E := below_pseudo_transitive_left _ _ _ H14 D).
                    apply below_elim in E. destruct E as [E F].
                     rewrite E in B. discriminate B. 
                 
                 assert (C := lteTrans _ _ _ B H14). 
                 rewrite (below_congruence _ _ _ lteCong _ _ _ _ H5 H9). 
                 case_eq(below lteS (bS x y) (bS b c) ); intro D; auto. 
                    assert (E := below_pseudo_transitive_right _ _ _ D C). 
                    assert (G := below_not_reflexive _ lteS (bS b c)). 
                    rewrite G in E. discriminate E. 
Qed.

Lemma lift_right_minset_invariant
  (LM : os_left_monotone lteS bS) 
  (DDD : (brel_antisymmetric S rS lteS) +
           ((os_left_strictly_monotone lteS bS)
            *
            (os_right_strictly_monotone lteS bS))):
  bop_right_uop_invariant
    (finite_set S)
    (brel_set rS)
    (bop_reduce (uop_minset lteS) (bop_lift rS bS))
    (uop_minset lteS).
Proof. intros X Y.
       unfold bop_reduce.
       (* ([ms] (X [^] ([ms] Y))) [=S] ([ms] (X [^] Y)) *)
       apply brel_set_intro_prop; auto. split.
       apply minset_lift_left_inclusion_2; auto.        
       apply minset_lift_left_inclusion_1; auto.        
Qed. 


Lemma minset_lift_uop_invariant
  (LM : os_left_monotone lteS bS) 
  (RM : os_right_monotone lteS bS) 
  (DDD : (brel_antisymmetric S rS lteS) +
           ((os_left_strictly_monotone lteS bS)
            *
           (os_right_strictly_monotone lteS bS))) :
  bop_uop_invariant (brel_set rS) (bop_lift rS bS) (uop_minset lteS).
Proof. apply r_is_b_reduction.
       - apply set_symmetric. 
       - apply set_transitive. 
       - apply lift_left_minset_invariant; auto.  
       - apply lift_right_minset_invariant; auto. 
Qed.


(* Note: congruence could be proved directly as shown here.  However, 
   I find that tracing it all the way back to the "ground truth" of 
   the classical model is a reassuring sanity check, even though that
   proof requires extra assumptions. 

Lemma bop_minset_lift_congruence_weak : bop_congruence (finite_set S) (brel_set rS) bop_minset_lift.
Proof. intros X1 X2 Y1 Y2 A B.
       unfold bop_minset_lift.
       apply set_equal_implies_minset_equal in A.
       apply set_equal_implies_minset_equal in B.        
       unfold brel_minset in A, B. 
       assert (C := bop_lift_congruence _ _ _ _ A B).
       assert (D := uop_minset_congruence_weak _ _ C).
       exact D. 
Qed.

Lemma bop_minset_lift_congruence : bop_congruence (finite_set S) (brel_minset rS lteS) bop_minset_lift.
Proof. unfold bop_congruence. intros X1 X2 Y1 Y2 A B.
       unfold bop_minset_lift.
       unfold brel_minset in A, B. 
       assert (C := bop_lift_congruence _ _ _ _ A B).
       assert (D := uop_minset_congruence_weak _ _ C).
       unfold brel_minset. 
       apply uop_minset_congruence_weak; auto. 
Qed.
 *)

Lemma bop_minset_lift_congruence
  (LM : os_left_monotone lteS bS) 
  (RM : os_right_monotone lteS bS) 
  (DDD : (brel_antisymmetric S rS lteS) +
           ((os_left_strictly_monotone lteS bS)
            *
           (os_right_strictly_monotone lteS bS))) :
  bop_congruence (finite_set S) (brel_minset rS lteS) bop_minset_lift.
Proof. apply bop_reduce_congruence.
       - exact set_symmetric.
       - exact set_transitive.
       - exact bop_lift_congruence.
       - exact uop_minset_congruence_weak.
       - exact (minset_lift_uop_invariant LM RM DDD). 
Qed.

Lemma bop_minset_lift_associative
  (LM : os_left_monotone lteS bS) 
  (RM : os_right_monotone lteS bS) 
  (DDD : (brel_antisymmetric S rS lteS) +
           ((os_left_strictly_monotone lteS bS)
            *
            (os_right_strictly_monotone lteS bS))):
  bop_associative (finite_set S) (brel_minset rS lteS) bop_minset_lift.
Proof. apply bop_reduce_associative.
       - exact set_reflexive.
       - exact set_symmetric.
       - exact set_transitive.
       - exact bop_lift_congruence.
       - exact bop_lift_associative. 
       - exact uop_minset_congruence_weak.
       - exact minset_idempotent.
       - exact (lift_left_minset_invariant RM DDD).
       - exact (lift_right_minset_invariant LM DDD). 
Qed. 
  
(* Note: Here is my first "brute force" proof of associativity.  Ugh! 
         (this helped inspire the results of sg/reduce.v.....) 
  --- tgg22

Lemma bop_minset_lift_associative
      (LM : os_left_monotone lteS bS) 
      (RM : os_right_monotone lteS bS) 
      (DDD : (brel_antisymmetric S rS lteS) +
             ((os_left_strictly_monotone lteS bS) * (os_right_strictly_monotone lteS bS))):
  bop_associative (finite_set S) (brel_minset rS lteS) bop_minset_lift.
Proof. intros X Y Z.
       assert (A : ((X <^> Y) <^> Z) [=MS] [ms] (([ms] (X <^> Y)) [^] ([ms] Z))).
           apply brel_minset_reflexive; auto. 
       assert (B : [ms] (([ms] (X <^> Y)) [^] ([ms] Z)) [=MS]  [ms] ((X <^> Y) [^] ([ms] Z))). 
           apply minset_lift_left_invariant; auto. 
       assert (C : ((X <^> Y) <^> Z) [=MS] [ms] ((X <^> Y) [^] ([ms] Z))). 
          exact (minset_transitive _ _ _ A B).
       assert (D : [ms] ((X <^> Y) [^] ([ms] Z))  [=MS] [ms] ([ms] (([ms] X) [^] ([ms] Y)) [^] ([ms] Z))). 
           apply brel_minset_reflexive; auto. 
       assert (E : ((X <^> Y) <^> Z) [=MS] [ms] ([ms] (([ms] X) [^] ([ms] Y)) [^] ([ms] Z))). 
          exact (minset_transitive _ _ _ C D).
          assert (F : [ms] (([ms] (([ms] X) [^] ([ms] Y))) [^] ([ms] Z)) [=MS] [ms] ((([ms] X) [^] ([ms] Y)) [^] ([ms] Z))).
             apply minset_lift_left_invariant_v1; auto. 
       assert (G : ((X <^> Y) <^> Z) [=MS] [ms] ((([ms] X) [^] ([ms] Y)) [^] ([ms] Z))).
          exact(minset_transitive _ _ _ E F).
       assert (H : [ms] ((([ms] X) [^] ([ms] Y)) [^] ([ms] Z)) [=MS] [ms] (([ms] X) [^] (([ms] Y) [^] ([ms] Z)))). 
          assert (AS := bop_lift_associative ([ms] X) ([ms] Y) ([ms] Z)).
          apply set_equal_implies_minset_equal in AS. 
          apply uop_minset_congruence; auto. 
       assert (I : ((X <^> Y) <^> Z) [=MS] [ms] (([ms] X) [^] (([ms] Y) [^] ([ms] Z)))).
          exact(minset_transitive _ _ _  G H).          
       assert (J : [ms] (([ms] X) [^] (([ms] Y) [^] ([ms] Z))) [=MS] [ms] (([ms] X) [^] ([ms] (([ms] Y) [^] ([ms] Z))))).  
           apply brel_minset_symmetric. 
           apply minset_lift_right_invariant_v1; auto. 
       assert (K : ((X <^> Y) <^> Z) [=MS] [ms] (([ms] X) [^] ([ms] (([ms] Y) [^] ([ms] Z))))).
          exact(minset_transitive _ _ _  I J).
       assert (L : [ms] (([ms] X) [^] ([ms] (([ms] Y) [^] ([ms] Z)))) [=MS] [ms] (([ms] X) [^] (Y <^> Z))).
          apply brel_minset_reflexive; auto. 
       assert (M : ((X <^> Y) <^> Z) [=MS] [ms] (([ms] X) [^] (Y <^> Z))).
          exact(minset_transitive _ _ _  K L).
       assert (N : [ms] (([ms] X) [^] (Y <^> Z)) [=MS] [ms] (([ms] X) [^] ([ms] (Y <^> Z)))).
           apply brel_minset_symmetric. 
           apply minset_lift_right_invariant_v1; auto. 
       assert (O : ((X <^> Y) <^> Z) [=MS] [ms] (([ms] X) [^] ([ms] (Y <^> Z)))).
          exact(minset_transitive _ _ _  M N).
       assert (P : [ms] (([ms] X) [^] ([ms] (Y <^> Z))) [=MS] (X <^> (Y <^> Z))). 
          apply brel_minset_reflexive; auto. 
       exact(minset_transitive _ _ _  O P).
Qed. 

*) 

Lemma bop_minset_lift_commutative
  (comm : bop_commutative S rS bS)
  (LM : os_left_monotone lteS bS) 
  (RM : os_right_monotone lteS bS) 
  (DDD : (brel_antisymmetric S rS lteS) +
           ((os_left_strictly_monotone lteS bS)
            *
           (os_right_strictly_monotone lteS bS))):
  bop_commutative (finite_set S) (brel_minset rS lteS) bop_minset_lift.
Proof. apply bop_reduce_commutative.
       - exact set_reflexive.
       - exact set_symmetric.
       - exact set_transitive.
       - exact bop_lift_congruence.
       - exact uop_minset_congruence_weak.
       - exact minset_idempotent.
       - exact (lift_left_minset_invariant RM DDD).
       - exact (lift_right_minset_invariant LM DDD).
       - apply bop_lift_commutative; auto. 
Qed. 
  


Lemma bop_lift_singletons (s t : S) : ((s :: nil) [^] (t :: nil)) [=S] ((bS s t) :: nil).
Proof. compute.
       case_eq(rS (bS s t) (bS s t)); intro A; auto. 
       rewrite refS in A. discriminate A. 
Qed. 

Lemma bop_minset_lift_not_commutative (ncomm : bop_not_commutative S rS bS) :
     bop_not_commutative (finite_set S) (brel_minset rS lteS) bop_minset_lift.
Proof. destruct ncomm as [[s t] A].
       exists (s :: nil, t ::nil).
       case_eq(brel_minset rS lteS ((s :: nil) <^> (t :: nil)) ((t :: nil) <^> (s :: nil))); intro B; auto. 
       unfold brel_minset in B. unfold bop_minset_lift in B.
       unfold brel_reduce in B. unfold bop_reduce in B.
       assert (C := uop_minset_idempotent ((s :: nil) [^] (t :: nil))).  
       assert (D := uop_minset_idempotent ((t :: nil) [^] (s :: nil))).
       apply set_symmetric in C.
       assert (E := set_transitive _ _ _ C B). 
       assert (F := set_transitive _ _ _ E D). 
       assert (G := bop_lift_singletons s t). 
       assert (H := bop_lift_singletons t s). 
       assert (I : ([ms] ((s :: nil) [^] (t :: nil))) [=S] ((bS s t) :: nil)).
             exact (uop_minset_congruence_weak _ _ G).
       assert (J : ([ms] ((t :: nil) [^] (s :: nil))) [=S] ((bS t s) :: nil)). 
            assert (J := uop_minset_congruence_weak _ _ G).
            rewrite minset_singleton in J; auto. 
            apply set_symmetric in I.
       assert (K := set_transitive _ _ _ I F).
       assert (L := set_transitive _ _ _ K J). 
          compute in L.  rewrite A in L. discriminate L. 
Defined. 


Definition bop_minset_lift_commutative_decide
  (comm_d : bop_commutative_decidable S rS bS)
  (LM : os_left_monotone lteS bS) 
  (RM : os_right_monotone lteS bS) 
  (DDD : (brel_antisymmetric S rS lteS) +
           ((os_left_strictly_monotone lteS bS)
            *
           (os_right_strictly_monotone lteS bS))):
  bop_commutative_decidable (finite_set S) (brel_minset rS lteS) bop_minset_lift := 
match comm_d with
| inl comm  => inl(bop_minset_lift_commutative comm LM RM DDD)
| inr ncomm => inr(bop_minset_lift_not_commutative ncomm) 
end. 

Lemma bop_minset_lift_nil_left (X : finite_set S) :  (nil <^> X) [=MS] nil. 
Proof. compute. reflexivity. Qed. 

Lemma bop_lift_nil_right (X : finite_set S) : (X [^] nil) [=S] nil.
Proof. destruct X.
       compute; auto. 
       apply brel_set_intro_prop; auto. split. 
          intros t A. apply in_set_bop_lift_elim in A; auto. 
          destruct A as [x [y [[B C] D]]]. 
          compute in C. discriminate C.        
          intros t A. compute in A. discriminate A.        
Qed.

Lemma bop_minset_lift_nil_right (X : finite_set S) : (X <^> nil) [=MS] nil.
Proof. unfold bop_minset_lift, brel_minset, brel_reduce, bop_reduce. 
       assert (A := bop_lift_nil_right X). 
       assert (B := uop_minset_congruence_weak _ _ A).
       assert (C := uop_minset_idempotent ((X [^] nil))). 
       exact (set_transitive _ _ _ C B). 
Qed. 

Lemma bop_minset_lift_ann_is_nil : bop_is_ann (finite_set S) (brel_minset rS lteS) bop_minset_lift nil. 
Proof. split. 
         apply bop_minset_lift_nil_left. 
         apply bop_minset_lift_nil_right.
Qed.

Lemma bop_minset_lift_exists_ann : bop_exists_ann (finite_set S) (brel_minset rS lteS) bop_minset_lift. 
Proof. exists nil. apply bop_minset_lift_ann_is_nil. Defined.

Lemma bop_minset_lift_id_is_bottom
      (b : S) (P : bop_is_id S rS bS b) : 
      bop_is_id (finite_set S) (brel_minset rS lteS) bop_minset_lift (b :: nil). 
Proof. intro X.   
       destruct (bop_lift_is_id _ _ _ refS tranS symS bCong b P X) as [L R]. 
       unfold brel_minset. unfold bop_minset_lift, brel_reduce, bop_reduce.
       split. 
       - apply uop_minset_congruence_weak in L. 
         assert (A := uop_minset_idempotent ((b :: nil) [^] X)).
         assert (B := set_transitive _ _ _ A L). 
         exact B.
       - apply uop_minset_congruence_weak in R. 
         assert (A := uop_minset_idempotent (X [^] (b :: nil))).
         assert (B := set_transitive _ _ _ A R). 
         exact B. 
Qed. 

Lemma bop_minset_lift_exists_id
      (bId  : bop_exists_id S rS bS):
  bop_exists_id (finite_set S) (brel_minset rS lteS) bop_minset_lift. 
Proof. destruct bId as [b P]. exists (b :: nil).
       apply bop_minset_lift_id_is_bottom; auto.
Defined.

(* Open problem: when does bop_not_exists_id hold? 
   This seems tricky. 
   Imagine a case where "bop_not_exists_id S rS bS" holds. 
   There could be a left id l (l * s = s) and a 
   right id r (s * r = s), where 
   s * l = top and r * s = top. 
   So, I = {l, r} is an idenity for minset_lift. 
   One could have many variations of this. 
   s1 could act as left id on X subset S
   and a right id on S - X, while s2 is a 
   right id on X and a left id on S - X, 
   so I = {s1, s2} is an idenity for minset_lift. 
   And, we can rig up simular things for 
   some {s1, s2, s3}, {s1, s2, s3, s4}, ...,  where 
   some s_i are always return (left or right) top 
   on some subset of S and act as left or right 
   ids on others....
*) 

Lemma bop_minset_lift_not_is_left : bop_not_is_left (finite_set S) (brel_minset rS lteS) bop_minset_lift. 
Proof. exists (wS :: nil, nil). compute. reflexivity. Defined. 

Lemma bop_minset_lift_not_is_right : bop_not_is_right (finite_set S) (brel_minset rS lteS) bop_minset_lift. 
Proof. exists (nil, wS :: nil). compute. reflexivity. Defined. 

Lemma bop_minset_lift_not_anti_left : bop_not_anti_left (finite_set S) (brel_minset rS lteS) bop_minset_lift. 
Proof. exists (nil, nil). compute. reflexivity.  Defined. 

Lemma bop_minset_lift_not_anti_right : bop_not_anti_right (finite_set S) (brel_minset rS lteS) bop_minset_lift. 
Proof. exists (nil, nil). compute. reflexivity. Defined.

Lemma bop_minset_lift_not_left_constant : bop_not_left_constant (finite_set S) (brel_minset rS lteS) bop_minset_lift.
Proof. exists (wS :: nil, (wS :: nil, nil)). compute. reflexivity. Defined.        

Lemma bop_minset_lift_not_right_constant : bop_not_right_constant (finite_set S) (brel_minset rS lteS) bop_minset_lift. 
Proof. exists (wS :: nil, (wS :: nil, nil)). compute. reflexivity. Defined.        

Lemma bop_minset_lift_not_left_cancellative : bop_not_left_cancellative (finite_set S) (brel_minset rS lteS) bop_minset_lift.
Proof. exists (nil, (wS :: nil, (f wS) :: nil)). compute. 
       destruct (Pf wS) as [L R]. rewrite L. split; reflexivity. 
Defined. 

Lemma bop_minset_lift_not_right_cancellative : bop_not_right_cancellative (finite_set S) (brel_minset rS lteS) bop_minset_lift.
Proof. exists (nil, (wS :: nil, (f wS) :: nil)). compute. 
       destruct (Pf wS) as [L R]. rewrite L. split; reflexivity. 
Defined. 

(**************** selectivity, idempotence ***************) 

(*  Deciding selectivity from sg/lift.v: 

Definition bop_lift_selective_decide (S : Type) (eq: brel S) (b: binary_op S)
        (refS : brel_reflexive S eq) (symS : brel_symmetric S eq) (trnS : brel_transitive S eq)
        (cong_b : bop_congruence S eq b) (asso_b : bop_associative S eq b) 
        (ilD : bop_is_left_decidable S eq b)
        (irD : bop_is_right_decidable S eq b)
        (idD : bop_idempotent_decidable S eq b)
        (exD : brel_exactly_two_decidable S eq) :=
match ilD with
| inl isl  => inl (bop_lift_selective_v1 S eq b refS trnS symS cong_b isl) 
| inr nisl => match irD with
              | inl isr  => inl (bop_lift_selective_v2 S eq b refS trnS symS cong_b isr) 
              | inr nisr => match idD with
                            | inl idem  => match exD with
                                           | inl ex2 => inl (bop_lift_selective_v3 S eq b refS trnS symS cong_b idem ex2) 
                                           | inr nex2 => inr (bop_lift_not_selective S eq b refS trnS symS cong_b nisl nisr idem nex2)
                                           end 
                            | inr nidem => inr (bop_lift_not_selective_v1 S eq b nidem)
                            end 
              end 
end.


Note that all cases except one could be used for minset_lift. 

However, this case causes problems: 

   | inr nex2 => inr (bop_lift_not_selective S eq b refS trnS symS cong_b nisl nisr idem nex2)

since we could have "X [^] Y not in {X, Y}", but  "[ms] (X [^] Y) in {X, Y}".

Note that bop_lift_not_selective for lift has 15 cases. 

Somehow we have to bring the order in to the picture. 

For now, we have only: 
     not_selective(bS) -> not_selective(minset_lift(<=, bS). 

So, for now we will insist on not_selective(bS). 

=================================================================
1. bop_not_selective bS → bop_not_selective bop_minset_lift. 
2. bop_selective bS → bop_idempotent bop_minset_lift. 
3. (assume anti, LI, LM RM, DDD) bop_idempotent bS → bop_idempotent bop_minset_lift. 
4  bop_not_idempotent bS → bop_not_idempotent bop_minset_lift. 

Need id = bottom 
not_idem + (idem * not_sel) 
Need comm???? 
Monotone increasing. 
anti (for now) 

what does minset_union need?
bottom 
po + qo 

What does minset_union_lift need? 
comm????  
nidem + (idem * nsel) 
Monotone increasing. 

What does minset_lift_union need? 
(not implemented yet!) 
same as above? 

Need 

os_monotone_increasing_po_sg_CI_with_bottom
os_monotone_increasing_po_sg_CNI_with_bottom

*) 

Lemma bop_minset_lift_not_selective_v1 :
         (bop_not_selective S rS bS) → bop_not_selective (finite_set S) (brel_minset rS lteS) bop_minset_lift. 
Proof. intros [[s t] [A B]]. 
       exists (s :: nil, t :: nil). 
          unfold bop_minset_lift.        
          unfold brel_minset. 
          assert (C := bop_lift_singletons s t).
          apply uop_minset_congruence_weak in C. rewrite minset_singleton in C.
          apply uop_minset_congruence_weak in C. rewrite minset_singleton in C.           
          assert (D : (bS s t :: nil) [<>S] (s :: nil)).
             case_eq(brel_set rS (bS s t :: nil) (s :: nil)); intro H; auto.
                apply brel_set_elim_prop in H; auto. destruct H as [H _]. 
                assert (G : (bS s t) [in] (bS s t :: nil)). apply in_set_singleton_intro; auto. 
                assert (I := H _ G). apply in_set_singleton_elim in I; auto.  apply symS in I. 
                rewrite I in A. discriminate A.                 
          assert (E : (bS s t :: nil) [<>S] (t :: nil)).
             case_eq(brel_set rS (bS s t :: nil) (t :: nil)); intro H; auto.
                apply brel_set_elim_prop in H;auto. destruct H as [H _]. 
                assert (G : (bS s t) [in] (bS s t :: nil)). apply in_set_singleton_intro; auto. 
                assert (I := H _ G). apply in_set_singleton_elim in I; auto.  apply symS in I. 
                rewrite I in B. discriminate B.                 
          assert (F : ([ms] ([ms] ((s :: nil) [^] (t :: nil)))) [<>S] (s :: nil)).
             apply set_symmetric in C.       
             exact (brel_transititivity_implies_dual _ (brel_set rS) set_transitive _ _ _ C D). 
          assert (G : ([ms] ([ms] ((s :: nil) [^] (t :: nil)))) [<>S] (t :: nil)). 
             apply set_symmetric in C.       
             exact (brel_transititivity_implies_dual _ (brel_set rS) set_transitive _ _ _ C E). 
          split; auto. 
Defined. 


Lemma bop_minset_lift_not_selective : 
         (bop_not_selective S rS bS) → bop_not_selective (finite_set S) (brel_minset rS lteS) bop_minset_lift. 
Proof. intros [[s t] [A B]]. 
       exists (s :: nil, t :: nil). 
          unfold bop_minset_lift.        
          unfold brel_minset.
          assert (C := bop_lift_singletons s t).
          apply uop_minset_congruence_weak in C. 
          rewrite minset_singleton in C. 
          apply uop_minset_congruence_weak in C.
          rewrite minset_singleton in C. 
          apply set_symmetric in C. 
          split. 
             case_eq(brel_set rS ([ms] ([ms] ((s :: nil) [^] (t :: nil)))) (s :: nil)); intro H; auto.
                assert (E := set_transitive _ _ _ C H).
                apply brel_set_elim_prop in E; auto. destruct E as [E1 E2].             
                assert (J : s [in] (s :: nil)). apply in_set_singleton_intro; auto. 
                assert (K := E2 _ J).
                apply in_set_singleton_elim in K; auto.
                rewrite K in A. discriminate A. 
             case_eq(brel_set rS ([ms] ([ms] ((s :: nil) [^] (t :: nil)))) (t :: nil)); intro H; auto. 
                assert (E := set_transitive _ _ _ C H).
                apply brel_set_elim_prop in E; auto. destruct E as [E1 E2].             
                assert (J : t [in] (t :: nil)). apply in_set_singleton_intro; auto. 
                assert (K := E2 _ J).
                apply in_set_singleton_elim in K; auto.
                rewrite K in B. discriminate B. 
Defined.


Lemma bop_minset_lift_idempotent_v1 (selS : bop_selective S rS bS) : bop_idempotent (finite_set S) (brel_minset rS lteS) bop_minset_lift.
Proof. intros X.
       unfold bop_minset_lift. unfold brel_minset, brel_reduce, bop_reduce. 
       assert (A := uop_minset_idempotent (X [^] X)). 
       assert (B := bop_lift_idempotent S rS bS refS tranS symS bCong selS X). 
       apply uop_minset_congruence_weak in B. 
       exact (set_transitive _ _ _ A B).
Qed.

Lemma bop_minset_lift_idempotent_v2_aux
      (anti : brel_antisymmetric S rS lteS)
      (idem : bop_idempotent S rS bS)
      (LI : os_left_increasing lteS bS) 
      (X : finite_set S) :
                [ms] (([ms] X) [^] ([ms] X)) [=S] ([ms] X).
Proof. apply brel_set_intro_prop; auto. split. 
       - intros a A.
         apply in_minset_elim in A; auto. destruct A as [A1 A2].          
         apply in_set_bop_lift_elim in A1; auto. 
         destruct A1 as [x [y [[B C] D]]].     
         assert (F := LI x y). 
         case_eq(in_set rS X a); intro E. 
         + apply in_minset_intro; auto. split; auto. 
           intros t G. 
           case_eq(in_set rS ([ms] X) t); intro H. 
           * apply A2. 
             assert (I := idem t).
             apply (in_set_right_congruence S rS symS tranS _ _ _ I).
             apply in_set_bop_lift_intro; auto.
           * apply in_set_minset_false_elim in H; auto. 
             destruct H as [u [I J]]. 
             case_eq(below lteS a t); intro K; auto. 
                assert (L := below_transitive _ lteS lteTrans _ _ _ J K). 
                assert (M : u [in] (([ms] X) [^] ([ms] X))). 
                   assert (H := idem u).
                   apply (in_set_right_congruence S rS symS tranS _ _ _ H).
                   apply in_set_bop_lift_intro; auto.
                rewrite (A2 _ M) in L. discriminate L. 
         + assert (G : x [in] (([ms] X) [^] ([ms] X))).
              assert (H := idem x).
              apply (in_set_right_congruence S rS symS tranS _ _ _ H).
              apply in_set_bop_lift_intro; auto.
           assert (H := A2 _ G).
           rewrite (below_congruence S rS lteS lteCong _ _ _ _ D (refS x)) in H.           
           apply below_false_elim in H. destruct H as [H | H]. 
           * rewrite F in H. discriminate H. 
           * assert (I := anti _ _ H F).            (* only use of anti *)
             assert (J := tranS _ _ _ D I). apply symS in J. 
             apply (in_set_right_congruence S rS symS tranS _ _ _ J).
             exact B. (* could also get contradiction from a [!in] X *)
       - intros a A. 
         apply in_minset_intro; auto. split. 
         + assert (B := idem a).  
           apply (in_set_right_congruence S rS symS tranS _ _ _ B).
           apply in_set_bop_lift_intro; auto. 
         + intros t B.
           apply in_set_bop_lift_elim in B; auto. 
           destruct B as [x [y [[B C] D]]].
           rewrite (below_congruence S rS lteS lteCong _ _ _ _ (refS a) D). 
           case_eq(below lteS a (bS x y)); intro E; auto. 
              apply in_minset_elim in A; auto. destruct A as [A1 A2].
              assert (F := LI x y). 
              assert (G := below_pseudo_transitive_left _ _ _ F E).
              apply in_minset_elim in B; auto. destruct B as [B1 B2].
              rewrite (A2 x B1) in G. discriminate G. 
Qed. 

Lemma bop_minset_lift_idempotent_v2
      (anti : brel_antisymmetric S rS lteS) 
      (idem : bop_idempotent S rS bS)
      (LI : os_left_increasing lteS bS)
      (LM : os_left_monotone lteS bS) 
      (RM : os_right_monotone lteS bS) :
  (*
      (DDD : (brel_antisymmetric S rS lteS) +
               ((os_left_strictly_monotone lteS bS)
                *
               (os_right_strictly_monotone lteS bS))): *) 
         bop_idempotent (finite_set S) (brel_minset rS lteS) bop_minset_lift.
Proof. intros X. unfold bop_minset_lift. unfold brel_minset, brel_reduce, bop_reduce. 
       assert (A := uop_minset_idempotent (X [^] X)).
       assert (B : ([ms] (([ms] X) [^] ([ms] X))) [=S] ([ms] X)).
       {
         apply bop_minset_lift_idempotent_v2_aux; auto.
       }
       assert (C : ([ms] (X [^] X)) [=S] ([ms] (([ms] X) [^] ([ms] X)))).
       {
         apply minset_lift_uop_invariant; auto.
       } 
       assert (D := set_transitive _ _ _ A C).
       exact (set_transitive _ _ _ D B). 
Qed.

(* from Vilius *)
Definition os_selective_increasing {S : Type} (lte : brel S) (b : binary_op S)  
  := ∀ s t : S, (lte s (b s t) = true) + (lte t (b s t) = true) .

Definition os_not_selective_increasing {S : Type} (lte : brel S) (b : binary_op S)  
  := { '(s, t) & (lte s (b s t) = false) * (lte t (b s t) = false)} .

Lemma bop_minset_lift_idempotent_using_selective_increasing_pointwise_proof 
      (anti : brel_antisymmetric S rS lteS)
      (idem : bop_idempotent S rS bS)
      (SI : os_selective_increasing lteS bS)
      (X : finite_set S) :
                [ms] (([ms] X) [^] ([ms] X)) [=S] ([ms] X).
Proof. apply brel_set_intro_prop; auto. split. 
       - intros a A.
         apply in_minset_elim in A; auto. destruct A as [A1 A2].          
         apply in_set_bop_lift_elim in A1; auto. 
         destruct A1 as [x [y [[B C] D]]].     
         case_eq(in_set rS X a); intro E. 
         + apply in_minset_intro; auto. split; auto. 
           intros t G. 
           case_eq(in_set rS ([ms] X) t); intro H. 
           * apply A2. 
             assert (I := idem t).
             apply (in_set_right_congruence S rS symS tranS _ _ _ I).
             apply in_set_bop_lift_intro; auto.
           * apply in_set_minset_false_elim in H; auto. 
             destruct H as [u [I J]]. 
             case_eq(below lteS a t); intro K; auto. 
                assert (L := below_transitive _ lteS lteTrans _ _ _ J K). 
                assert (M : u [in] (([ms] X) [^] ([ms] X))). 
                   assert (H := idem u).
                   apply (in_set_right_congruence S rS symS tranS _ _ _ H).
                   apply in_set_bop_lift_intro; auto.
                rewrite (A2 _ M) in L. discriminate L. 
         + assert (G : x [in] (([ms] X) [^] ([ms] X))).
              assert (H := idem x).
              apply (in_set_right_congruence S rS symS tranS _ _ _ H).
              apply in_set_bop_lift_intro; auto.
           assert (H := A2 _ G).
           rewrite (below_congruence S rS lteS lteCong _ _ _ _ D (refS x)) in H.           
           apply below_false_elim in H.
           destruct H as [H | H]; destruct (SI x y) as [F | F]. 
           * rewrite F in H. discriminate H.
           * assert (I : y [in] (([ms] X) [^] ([ms] X))). admit.
             assert (J := A2 _ I).
             apply below_false_elim in J.
             destruct J as [J | J].
             -- admit. 
             -- admit. 
           * assert (I := anti _ _ H F).            
             assert (J := tranS _ _ _ D I). apply symS in J. 
             apply (in_set_right_congruence S rS symS tranS _ _ _ J).
             exact B.
           * assert (I : y [in] (([ms] X) [^] ([ms] X))). admit.
             assert (J := A2 _ I).
             apply below_false_elim in J.
             destruct J as [J | J].
             -- admit. 
             -- admit. 
       - intros a A. 
         apply in_minset_intro; auto. split. 
         + assert (B := idem a).  
           apply (in_set_right_congruence S rS symS tranS _ _ _ B).
           apply in_set_bop_lift_intro; auto. 
         + intros t B.
           apply in_set_bop_lift_elim in B; auto. 
           destruct B as [x [y [[B C] D]]].
           rewrite (below_congruence S rS lteS lteCong _ _ _ _ (refS a) D). 
           case_eq(below lteS a (bS x y)); intro E; auto. 
              apply in_minset_elim in A; auto. destruct A as [A1 A2].
              destruct (SI x y) as [F | F]. 
              * assert (G := below_pseudo_transitive_left _ _ _ F E).
                apply in_minset_elim in B; auto. destruct B as [B1 B2].
                rewrite (A2 x B1) in G. discriminate G.
              * assert (G := below_pseudo_transitive_left _ _ _ F E).
                apply in_minset_elim in C; auto. destruct C as [C1 C2].
                rewrite (A2 _ C1) in G. discriminate G.
Admitted.


Lemma bop_minset_lift_idempotent_using_selective_increasing_upperset_proof 
      (anti : brel_antisymmetric S rS lteS)
      (idem : bop_idempotent S rS bS)
      (SI : os_selective_increasing lteS bS)
      (X : finite_set S) :
                [ms] (([ms] X) [^] ([ms] X)) [=S] ([ms] X).
Proof. apply minset_equal_intro; auto. 
       intro a.
       case_eq(in_upperset S rS lteS X a); intro A.
       - apply in_upperset_elim in A; auto. 
         destruct A as [b [A B]].
         assert (D : b [in] (([ms] X) [^] ([ms] X))).
         {
           assert (C := idem b).
           apply (in_set_right_congruence S rS symS tranS _ _ _ C). 
           apply in_set_bop_lift_intro; auto. 
         } 
         assert (E : b [in] [ms] (([ms] X) [^] ([ms] X))).
         {
           apply in_minset_intro; auto. split; auto.
           intros t F. 
           apply in_set_bop_lift_elim in F; auto. 
           destruct F as [c [d [[G H] I]]].
           apply in_minset_elim in A; auto.
           destruct A as [A A']. 
           destruct (SI c d) as [J | J].
           + case_eq(below lteS b t); intro K; auto.
             rewrite (lteCong _ _ _ _ (refS c) (symS _ _ I)) in J.
             assert (L := below_pseudo_transitive_left _ _ _ J K).
             apply in_minset_elim in G; auto. destruct G as [G _].
             rewrite (A' _ G) in L.
             discriminate L. 
           + case_eq(below lteS b t); intro K; auto.
             rewrite (lteCong _ _ _ _ (refS d) (symS _ _ I)) in J.
             assert (L := below_pseudo_transitive_left _ _ _ J K).
             apply in_minset_elim in H; auto. destruct H as [H _].
             rewrite (A' _ H) in L.
             discriminate L. 
         } 
         exact(in_upperset_intro S rS refS symS tranS lteS lteCong lteRefl lteTrans anti _ _ _ E B).
       - assert (B := in_upperset_false_elim S rS refS symS tranS lteS lteCong lteRefl lteTrans anti _ _ A).
         case_eq(in_upperset S rS lteS (([ms] X) [^] ([ms] X)) a); intro C; auto.
         apply in_upperset_elim in C; auto.
         destruct C as [b [D E]].
         apply in_minset_elim in D; auto. destruct D as [D F].
         apply in_set_bop_lift_elim in D; auto.
         destruct D as [c [d [[G H] I]]].
         destruct (SI c d) as [J | J].
         + rewrite <- (lteCong _ _ _ _ (refS c) I) in J.
           assert (K := lteTrans _ _ _ J E).
           destruct (B c) as [L | L]. 
           * rewrite G in L. discriminate L. 
           * rewrite K in L. discriminate L. 
         + rewrite <- (lteCong _ _ _ _ (refS d) I) in J.
           assert (K := lteTrans _ _ _ J E).
           destruct (B d) as [L | L]. 
           * rewrite H in L. discriminate L. 
           * rewrite K in L. discriminate L. 
Qed.

Lemma bop_minset_lift_idempotent_vilus_version 
      (anti : brel_antisymmetric S rS lteS) 
      (idem : bop_idempotent S rS bS)
      (SI : os_selective_increasing lteS bS)
      (LM : os_left_monotone lteS bS) 
      (RM : os_right_monotone lteS bS) :
         bop_idempotent (finite_set S) (brel_minset rS lteS) bop_minset_lift.
Proof. intros X. unfold bop_minset_lift. unfold brel_minset, brel_reduce, bop_reduce. 
       assert (A := uop_minset_idempotent (X [^] X)).
       assert (B : ([ms] (([ms] X) [^] ([ms] X))) [=S] ([ms] X)).
       {
         apply bop_minset_lift_idempotent_using_selective_increasing_upperset_proof ; auto.
       }
       assert (C : ([ms] (X [^] X)) [=S] ([ms] (([ms] X) [^] ([ms] X)))).
       {
         apply minset_lift_uop_invariant; auto.
       } 
       assert (D := set_transitive _ _ _ A C).
       exact (set_transitive _ _ _ D B). 
Qed.

Lemma bop_minset_lift_not_idempotent_aux_from_not_selective_increasing_pointwise_version 
      (anti : brel_antisymmetric S rS lteS)
      (idem : bop_idempotent S rS bS)
      (NSI : os_not_selective_increasing lteS bS) :
  { X : finite_set S &  [ms] (([ms] X) [^] ([ms] X)) [<>S] ([ms] X) }.
Proof. destruct NSI as [[s t] [A B]].
       exists (s :: t :: nil).
       case_eq(brel_set rS
                 ([ms] (([ms] (s :: t :: nil)) [^] ([ms] (s :: t :: nil))))
                 ([ms] (s :: t :: nil))
              ); intro C; auto.
       apply brel_set_elim_prop in C; auto.
       destruct C as [C D].
       assert (E : s [in] ([ms] (s :: t :: nil))). admit.
       assert (F := D _ E).
       apply in_minset_elim in F; auto.
       destruct F as [F G]. 
(*
       assert (E : bS s t [in] ([ms] (([ms] (s :: t :: nil)) [^] ([ms] (s :: t :: nil))))).
       {
         
       } 
       assert (F : ∀ x, x [in] ([ms] (s :: t :: nil)) -> (s [=] x) + (t [=] x)).
       {
         intros x G.
         apply in_minset_elim in G; auto.
         destruct G as [G _].
         apply in_set_cons_elim in G; auto.
         destruct G as [G | G]; auto.
         apply in_set_cons_elim in G; auto.
         destruct G as [G | G]; auto.
         compute in G. discriminate G. 
       } 
       destruct (F _ (C _ E)) as [I | I].
       - assert (K : s <<= bS s t).
         {
           rewrite (lteCong _ _ _ _ (refS s) I). apply lteRefl.
         }
         rewrite K in A. discriminate A. 
       - assert (K : t <<= bS s t).
         {
           rewrite (lteCong _ _ _ _ (refS t) I). apply lteRefl.
         }
         rewrite K in B. discriminate B.
*) 
Admitted.

Lemma bop_minset_lift_not_idempotent_aux_from_not_selective_increasing_upperset_version 
      (anti : brel_antisymmetric S rS lteS)
      (idem : bop_idempotent S rS bS)
      (NSI : os_not_selective_increasing lteS bS) :
  { X : finite_set S &  [ms] (([ms] X) [^] ([ms] X)) [<>S] ([ms] X) }.
Proof. destruct NSI as [[s t] [A B]].
       exists (s :: t :: nil).
       case_eq(brel_set rS
                 ([ms] (([ms] (s :: t :: nil)) [^] ([ms] (s :: t :: nil))))
                 ([ms] (s :: t :: nil))
              ); intro C;auto. 
       assert (D := minset_equal_elim _ _ refS symS tranS lteS lteCong lteRefl lteTrans _ _ anti C (bS s t)).
       assert (E : in_upperset S rS lteS (s :: t :: nil) (bS s t) = false).
       {
         case_eq(in_upperset S rS lteS (s :: t :: nil) (bS s t)); intro E; auto.
         apply in_upperset_elim in E; auto.
         destruct E as [b [F G]].
         apply in_minset_elim in F; auto. destruct F as [F _].
         apply in_set_cons_elim in F; auto. destruct F as [F | F].
         - rewrite (lteCong _ _ _ _ F (refS (bS s t))) in A.
           rewrite A in G. discriminate G. 
         - apply in_set_singleton_elim in F; auto. 
           rewrite (lteCong _ _ _ _ F (refS (bS s t))) in B.
           rewrite B in G. discriminate G. 
       }
       rewrite E in D. 
       assert (F := in_upperset_false_elim _ _ refS symS tranS lteS lteCong lteRefl lteTrans anti _ _ D).
       case_eq(lteS s t); intro G; case_eq(lteS t s); intro H. 
       - assert (I := anti _ _ G H).
         assert (J := bCong _ _ _ _ (refS s) I).
         assert (K := idem s). apply symS in J.
         assert (L := tranS _ _ _ J K). 
         rewrite (lteCong _ _ _ _ (refS s) L) in A.
         rewrite lteRefl in A. discriminate A. 
       - admit. 
       - admit. 
       - assert (I : (bS s t) [in] ([ms] (([ms] (s :: t :: nil)) [^] ([ms] (s :: t :: nil))))).
         {
           apply in_minset_intro; auto. split.
           + admit.
           + admit. 
         } 
Admitted. 


       (*
Lemma bop_minset_lift_idempotent_v3_aux
      (nanti : brel_not_antisymmetric S rS lteS) 
      (idem : bop_idempotent S rS bS)
      (LI : os_left_increasing lteS bS)
      (LSM : os_left_strictly_monotone lteS bS)
      (RSM : os_right_strictly_monotone lteS bS)
      (X : finite_set S) :
                [ms] (([ms] X) [^] ([ms] X)) [=S] ([ms] X).
Proof. destruct nanti as [[z1 z2] [[H1 H2] H3]].
       compute in LI, LSM, RSM. 
       apply brel_set_intro_prop; auto. split. 
       - intros a A.
         apply in_minset_elim in A; auto. destruct A as [A1 A2].          
         apply in_set_bop_lift_elim in A1; auto. 
         destruct A1 as [x [y [[B C] D]]].     
         assert (F := LI x y). 
         case_eq(in_set rS X a); intro E. 
         + apply in_minset_intro; auto. split; auto. 
           intros t G. 
           case_eq(in_set rS ([ms] X) t); intro H. 
           * apply A2. 
             assert (I := idem t).
             apply (in_set_right_congruence S rS symS tranS _ _ _ I).
             apply in_set_bop_lift_intro; auto.
           * apply in_set_minset_false_elim in H; auto. 
             destruct H as [u [I J]]. 
             case_eq(below lteS a t); intro K; auto. 
                assert (L := below_transitive _ lteS lteTrans _ _ _ J K). 
                assert (M : u [in] (([ms] X) [^] ([ms] X))). 
                   assert (H := idem u).
                   apply (in_set_right_congruence S rS symS tranS _ _ _ H).
                   apply in_set_bop_lift_intro; auto.
                rewrite (A2 _ M) in L. discriminate L. 
         + assert (G : x [in] (([ms] X) [^] ([ms] X))).
              assert (H := idem x).
              apply (in_set_right_congruence S rS symS tranS _ _ _ H).
              apply in_set_bop_lift_intro; auto.
           assert (H := A2 _ G).
           rewrite (below_congruence S rS lteS lteCong _ _ _ _ D (refS x)) in H.           
           apply below_false_elim in H. destruct H as [H | H]. 
           * rewrite F in H. discriminate H. 
           * case_eq(in_set rS ([ms] X) a); intro I; auto.
             apply in_set_minset_false_elim in I; auto.
             destruct I as [z [J K]].
             (* OK *) admit.
             (* NO *) admit. 
       - intros a A. 
         apply in_minset_intro; auto. split. 
         + assert (B := idem a).  
           apply (in_set_right_congruence S rS symS tranS _ _ _ B).
           apply in_set_bop_lift_intro; auto. 
         + intros t B.
           apply in_set_bop_lift_elim in B; auto. 
           destruct B as [x [y [[B C] D]]].
           rewrite (below_congruence S rS lteS lteCong _ _ _ _ (refS a) D). 
           case_eq(below lteS a (bS x y)); intro E; auto. 
              apply in_minset_elim in A; auto. destruct A as [A1 A2].
              assert (F := LI x y). 
              assert (G := below_pseudo_transitive_left _ _ _ F E).
              apply in_minset_elim in B; auto. destruct B as [B1 B2].
              rewrite (A2 x B1) in G. discriminate G. 
Qed. 

Lemma bop_minset_lift_idempotent_v3
      (nanti : brel_not_antisymmetric S rS lteS) 
      (idem : bop_idempotent S rS bS)
      (LI : os_left_increasing lteS bS)
      (LM : os_left_monotone lteS bS) 
      (RM : os_right_monotone lteS bS) 
      (LSM : os_left_strictly_monotone lteS bS)
      (RSM : os_right_strictly_monotone lteS bS):
         bop_idempotent (finite_set S) (brel_minset rS lteS) bop_minset_lift.
Proof. intros X. unfold bop_minset_lift. unfold brel_minset, brel_reduce, bop_reduce. 
       assert (A := uop_minset_idempotent (X [^] X)).
       assert (B : ([ms] (([ms] X) [^] ([ms] X))) [=S] ([ms] X)).
       {
         admit. 
       }
       assert (C : ([ms] (X [^] X)) [=S] ([ms] (([ms] X) [^] ([ms] X)))).
       {
         apply minset_lift_uop_invariant; auto.
       } 
       assert (D := set_transitive _ _ _ A C).
       exact (set_transitive _ _ _ D B). 
Qed. 

*) 




Lemma bop_minset_lift_not_idempotent :
  (bop_not_idempotent S rS bS)
  →
  bop_not_idempotent (finite_set S) (brel_minset rS lteS) bop_minset_lift. 
Proof. intros [ s A]. 
       exists (s :: nil). 
       unfold bop_minset_lift, brel_minset, brel_reduce, bop_reduce. 
       case_eq(brel_set rS ([ms] ([ms] ((s :: nil) [^] (s :: nil)))) ([ms] (s :: nil))); intro C; auto. 
       assert (D := uop_minset_idempotent ((s :: nil) [^] (s :: nil))).
       apply set_symmetric in D.
       assert (E := set_transitive _ _ _ D C). 
       apply brel_set_elim_prop in E; auto. destruct E as [E F]. 
       assert (G : s [in] (s :: nil)). apply in_set_cons_intro; auto. 
       assert (H := F s G). 
       apply in_minset_elim in H; auto. destruct H as [H I]. 
       apply in_set_bop_lift_elim in H; auto. 
       destruct H as [x [y [[J K] L]]].
       apply in_set_singleton_elim in K; auto.
       apply in_set_singleton_elim in J; auto.              
       assert (M : rS (bS s s) (bS x y) = true). exact (bCong _ _ _ _ J K). 
       apply symS in L. rewrite (tranS _ _ _ M L) in A. 
       discriminate A. 
Defined.



End Theory.

Section ACAS.

Section Proofs.

Variables     
    (S : Type)
    (rS lteS : brel S)
    (s : S)
    (f : S -> S)
    (b   : binary_op S)
    (ntS : brel_not_trivial S rS f)     
    (eqvS : eqv_proofs S rS)
    (poS : po_proofs S rS lteS)
    (LM : os_left_monotone lteS b)
    (RM : os_right_monotone lteS b)
    (DDD : (brel_antisymmetric S rS lteS) +
             ((os_left_strictly_monotone lteS b)
              *
                (os_right_strictly_monotone lteS b))).

(*
Definition sg_proofs_minset_lift_from_po
  (sgS : sg_proofs S rS b) :
         sg_proofs (finite_set S) (brel_minset rS lteS) (bop_minset_lift S rS lteS b) := 
let congS := A_eqv_congruence S rS eqvS in  
let refS := A_eqv_reflexive S rS eqvS in
let symS := A_eqv_symmetric S rS eqvS in
let tranS := A_eqv_transitive S rS eqvS in

let lteCong    := A_po_congruence S rS lteS poS in
let lteRefl    := A_po_reflexive S rS lteS poS in
let lteTran    := A_po_transitive S rS lteS poS in
let anti       := A_po_antisymmetric S rS lteS poS in

let bCong  := A_sg_congruence _ _ _ sgS in
let bAssoc := A_sg_associative _ _ _ sgS in
let bComm_d := A_sg_commutative_d _ _ _ sgS in
{|
  A_sg_associative      := bop_minset_lift_associative S rS refS symS tranS lteS lteCong lteRefl lteTran  b bCong bAssoc LM RM (inl anti) 
; A_sg_congruence       := bop_minset_lift_congruence S rS refS symS tranS lteS lteCong lteRefl lteTran b bCong LM RM DDD
; A_sg_commutative_d    := bop_minset_lift_commutatice_decide S rS refS symS tranS lteS lteCong lteRefl lteTran b bCong bComm_d LM RM DDD
; A_sg_idempotent_d     := inr (bop_minset_lift_not_idempotent S rS refS symS tranS lteS lteCong lteRefl lteTran b bCong nIdem)
; A_sg_C_selective_d    := inr (bop_minset_lift_not_selective S rS refS symS tranS lteS lteCong lteRefl lteTran b nsel)


                                 
; A_sg_C_cancel_d         := inr (bop_minset_lift_not_left_cancellative S rS s f ntS lteS b)
; A_sg_C_constant_d       := inr (bop_minset_lift_not_left_constant S rS s lteS b)
; A_sg_C_anti_left_d      := inr (bop_minset_lift_not_anti_left S rS lteS b)
; A_sg_C_anti_right_d     := inr (bop_minset_lift_not_anti_right S rS lteS b)

|}. 
*) 

Definition sg_CI_proofs_minset_lift_from_po
    (bComm  : bop_commutative S rS b) 
    (bIdem  : bop_idempotent S rS b) 
    (NotSel : bop_not_selective S rS b) 
    (bAssoc : bop_associative S rS b)
    (bCong  : bop_congruence S rS b) 
    (LI : os_left_increasing lteS b) : 
        sg_CI_proofs (finite_set S) (brel_minset rS lteS) (bop_minset_lift S rS lteS b) := 
let congS := A_eqv_congruence S rS eqvS in  
let refS := A_eqv_reflexive S rS eqvS in
let symS := A_eqv_symmetric S rS eqvS in
let tranS := A_eqv_transitive S rS eqvS in
let lteCong    := A_po_congruence S rS lteS poS in
let lteRefl    := A_po_reflexive S rS lteS poS in
let lteTran    := A_po_transitive S rS lteS poS in
let anti       := A_po_antisymmetric S rS lteS poS in
{|
  A_sg_CI_associative        := bop_minset_lift_associative S rS refS symS tranS lteS lteCong lteRefl lteTran  b bCong bAssoc LM RM (inl anti) 
; A_sg_CI_congruence         := bop_minset_lift_congruence S rS refS symS tranS lteS lteCong lteRefl lteTran b bCong LM RM DDD
; A_sg_CI_commutative        := bop_minset_lift_commutative S rS refS symS tranS lteS lteCong lteRefl lteTran b bCong bComm LM RM DDD
; A_sg_CI_idempotent         := bop_minset_lift_idempotent_v2 S rS refS symS tranS lteS lteCong lteRefl lteTran b bCong anti bIdem LI LM RM
; A_sg_CI_not_selective      := bop_minset_lift_not_selective_v1 S rS refS symS tranS lteS lteCong lteRefl lteTran b NotSel

|}.


Definition sg_CNI_proofs_minset_lift_from_po
           (sgS : sg_CNI_proofs S rS b) : 
        sg_CNI_proofs (finite_set S) (brel_minset rS lteS) (bop_minset_lift S rS lteS b) := 
let congS := A_eqv_congruence S rS eqvS in  
let refS := A_eqv_reflexive S rS eqvS in
let symS := A_eqv_symmetric S rS eqvS in
let tranS := A_eqv_transitive S rS eqvS in

let lteCong    := A_po_congruence S rS lteS poS in
let lteRefl    := A_po_reflexive S rS lteS poS in
let lteTran    := A_po_transitive S rS lteS poS in
let anti       := A_po_antisymmetric S rS lteS poS in

let bComm   := A_sg_CNI_commutative _ _ _ sgS in
let nIdem   := A_sg_CNI_not_idempotent _ _ _ sgS in

let bCong  := A_sg_CNI_congruence _ _ _ sgS in
let bAssoc := A_sg_CNI_associative _ _ _ sgS in
{|
  A_sg_CNI_associative      := bop_minset_lift_associative S rS refS symS tranS lteS lteCong lteRefl lteTran  b bCong bAssoc LM RM (inl anti) 
; A_sg_CNI_congruence       := bop_minset_lift_congruence S rS refS symS tranS lteS lteCong lteRefl lteTran b bCong LM RM DDD
; A_sg_CNI_commutative      := bop_minset_lift_commutative S rS refS symS tranS lteS lteCong lteRefl lteTran b bCong bComm LM RM DDD
; A_sg_CNI_not_idempotent   := bop_minset_lift_not_idempotent S rS refS symS tranS lteS lteCong lteRefl lteTran b bCong nIdem

; A_sg_CNI_cancel_d         := inr (bop_minset_lift_not_left_cancellative S rS s f ntS lteS b)
; A_sg_CNI_constant_d       := inr (bop_minset_lift_not_left_constant S rS s lteS b)
; A_sg_CNI_anti_left_d      := inr (bop_minset_lift_not_anti_left S rS lteS b)
; A_sg_CNI_anti_right_d     := inr (bop_minset_lift_not_anti_right S rS lteS b)
|}. 

End Proofs.

Section Combinators. 

Definition A_sg_CI_minset_lift {S : Type} 
           (A : @A_monotone_increasing_po_with_bottom_sg_CI S) : A_sg_CI (finite_set S) :=             
let eqv := A_mi_powb_sg_CI_eqv A in
let eqvP := A_eqv_proofs _ eqv in
let refS := A_eqv_reflexive _ _ eqvP in
let symS := A_eqv_symmetric _ _ eqvP in
let trnS := A_eqv_transitive _ _ eqvP in 
let eq  := A_eqv_eq _ eqv in
let lte := A_mi_powb_sg_CI_lte A in 
let bop := A_mi_powb_sg_CI_times A in
let lteP := A_mi_powb_sg_CI_lte_properties A in
let lteCong := A_po_congruence _ _ _ lteP in 
let lteRef  := A_po_reflexive  _ _ _ lteP in 
let lteTrn  := A_po_transitive  _ _ _ lteP in             
let lteAnti := A_po_antisymmetric  _ _ _ lteP in 
let bopP := A_mi_powb_sg_CI_times_properties A in
let bopAssoc := A_sg_CI_associative _ _ _ bopP in
let bopCong := A_sg_CI_congruence _ _ _ bopP in
let bComm   := A_sg_CI_commutative _ _ _ bopP in
let bIdem   := A_sg_CI_idempotent _ _ _ bopP in
let bNotSel := A_sg_CI_not_selective _ _ _ bopP in
let bottom_id_equal := A_bottom_is_id  _ _ _ _ (A_mi_powb_sg_CI_bottom_top_properties A) in
let idP  := A_extract_exist_id_from_exists_bottom_id_equal _ _ _ _ bottom_id_equal in 
let AP   := A_mi_powb_sg_CI_properties A in
let LM   := A_mono_inc_left_monotonic _ _ _ AP in 
let RM   := A_mono_inc_right_monotonic _ _ _ AP in 
let LI   := A_mono_inc_left_increasing _ _ _ AP in 
{|
  A_sg_CI_eqv          := A_eqv_minset_from_po _ (A_po_from_monotone_increasing_po_with_bottom_sg_CI _ A)
; A_sg_CI_bop          := bop_minset_lift S eq lte bop
; A_sg_CI_exists_id_d  := inl (bop_minset_lift_exists_id S eq refS symS trnS lte lteCong lteRef lteTrn bop bopCong idP)
; A_sg_CI_exists_ann_d := inl (bop_minset_lift_exists_ann S eq refS symS trnS lte lteCong lteRef lteTrn bop)
; A_sg_CI_proofs       := sg_CI_proofs_minset_lift_from_po S eq lte bop eqvP lteP LM RM (inl lteAnti) bComm bIdem bNotSel bopAssoc bopCong  LI 
; A_sg_CI_ast          := Ast_sg_minset_lift (A_mi_powb_sg_CI_ast A)
|}.  


Definition A_sg_CNI_minset_lift {S : Type} 
           (A : @A_monotone_increasing_po_with_bottom_sg_CNI S) : A_sg_CNI (finite_set S) :=             
let eqv := A_mi_powb_sg_CNI_eqv A in
let eqvP := A_eqv_proofs _ eqv in
let refS := A_eqv_reflexive _ _ eqvP in
let symS := A_eqv_symmetric _ _ eqvP in
let trnS := A_eqv_transitive _ _ eqvP in 
let eq  := A_eqv_eq _ eqv in
let wS  := A_eqv_witness _ eqv in
let f   := A_eqv_new _ eqv in
let nt   := A_eqv_not_trivial _ eqv in
let lte := A_mi_powb_sg_CNI_lte A in 
let bop := A_mi_powb_sg_CNI_times A in
let lteP := A_mi_powb_sg_CNI_lte_properties A in
let lteCong := A_po_congruence _ _ _ lteP in 
let lteRef  := A_po_reflexive  _ _ _ lteP in 
let lteTrn  := A_po_transitive  _ _ _ lteP in             
let lteAnti := A_po_antisymmetric  _ _ _ lteP in 
let bopP := A_mi_powb_sg_CNI_times_properties A in
let bopAssoc := A_sg_CNI_associative _ _ _ bopP in
let bopCong := A_sg_CNI_congruence _ _ _ bopP in
let bottom_id_equal := A_bottom_is_id  _ _ _ _ (A_mi_powb_sg_CNI_bottom_top_properties A) in
let idP  := A_extract_exist_id_from_exists_bottom_id_equal _ _ _ _ bottom_id_equal in 
let AP   := A_mi_powb_sg_CNI_properties A in
let LM   := A_mono_inc_left_monotonic _ _ _ AP in 
let RM   := A_mono_inc_right_monotonic _ _ _ AP in 
let LI   := A_mono_inc_left_increasing _ _ _ AP in 
{|
  A_sg_CNI_eqv          := A_eqv_minset_from_po _ (A_po_from_monotone_increasing_po_with_bottom_sg_CNI _ A)
; A_sg_CNI_bop          := bop_minset_lift S eq lte bop
; A_sg_CNI_exists_id_d  := inl (bop_minset_lift_exists_id S eq refS symS trnS lte lteCong lteRef lteTrn bop bopCong idP)
; A_sg_CNI_exists_ann_d := inl (bop_minset_lift_exists_ann S eq refS symS trnS lte lteCong lteRef lteTrn bop)
; A_sg_CNI_proofs       := sg_CNI_proofs_minset_lift_from_po S eq lte wS f bop nt eqvP lteP LM RM (inl lteAnti) bopP 
; A_sg_CNI_ast          := Ast_sg_minset_lift (A_mi_powb_sg_CNI_ast A)
|}.  


End Combinators.   

End ACAS.

Section AMCAS.

Local Open Scope string_scope.

Definition A_minset_lift_from_monotone_increasing_po_with_bottom_sg_CI
             {S : Type} 
             (A : @A_monotone_increasing_po_with_bottom_sg_CI S) : @A_below_sg_CI (finite_set S) :=
  A_classify_sg_CI (A_sg_CI_minset_lift A).


Definition A_minset_lift_from_monotone_increasing_po_with_bottom_sg_CNI
             {S : Type} 
             (A : @A_monotone_increasing_po_with_bottom_sg_CNI S) : @A_below_sg_CNI (finite_set S) :=
  A_classify_sg_CNI (A_sg_CNI_minset_lift A).

(*


  Definition A_sg_llex_below_sg_CS {S T : Type} (A : @A_below_sg_CS S) (B : @A_below_sg T) := 
    A_classify_sg (A_sg_llex (A_cast_up_sg_CS A) (A_cast_up_sg B)).  

  Definition A_mcas_sg_llex {S T : Type} (A : @A_sg_mcas S)  (B : @A_sg_mcas T)  : @A_sg_mcas (S * T) :=
    match A, B with
    | A_MCAS_sg A', A_MCAS_sg B'               =>
        match A_cast_below_sg_to_below_sg_CS A' with
        | Some bcs => A_MCAS_sg (A_sg_llex_below_sg_CS bcs B')
        | None     => A_MCAS_sg_Error ("sg_llex : the first argument must be commutative and selective." :: nil)
        end 
    | A_MCAS_sg_Error sl1, A_MCAS_sg_Error sl2 => A_MCAS_sg_Error (sl1 ++ sl2)
    | A_MCAS_sg_Error sl1, _                   => A_MCAS_sg_Error sl1
    | _,  A_MCAS_sg_Error sl2                  => A_MCAS_sg_Error sl2
    end.




Definition A_mcas_minset_lift (S : Type) (M : A_os_mcas S) : A_sg_mcas (finite_set S ) :=
match M with
| A_OS_bounded_monotone_increasing_posg _ A => 
  let bopP   := A_bmiposg_times_proofs _ A in
  let comm_d := A_sg_commutative_d _ _ _ bopP in
  let idem_d := A_sg_idempotent_d _ _ _ bopP in
  let sel_d  := A_sg_selective_d _ _ _ bopP in
  match comm_d with
  | inl comm =>
    match idem_d with 
    | inl idem  =>
      match sel_d with
      | inl _    => A_MCAS_sg_Error _ ("mcas_minset_lift : (currently) multiplication cannot be selective" :: nil)
      | inr nsel => A_MCAS_sg_BCI _ (A_sg_BCI_minset_lift_GUARDED S A comm idem nsel) 
      end 
    | inr nidem => A_MCAS_sg_BCNI _ (A_sg_CNI_minset_lift_GUARDED S A comm nidem) 
    end        
  | inr _    => A_MCAS_sg_Error _ ("mcas_minset_lift : (currently) multiplication must be commutative" :: nil)
  end
| _ => A_MCAS_sg_Error _ ("mcas_minset_lift : (currently) can only be applied to a bounded, monotone, and increasing order-semigroup" :: nil)
end. 
*) 
End AMCAS.

(********************************************************************************************
Section CAS.
Section Proofs.

Variables     
    (S : Type)
    (wS : S)
    (f : S -> S).

Definition sg_CI_certs_minset_lift_from_po
    (bComm  : @assert_commutative S) 
    (bIdem  : @assert_idempotent S) 
    (NotSel : @assert_not_selective S) : @sg_CI_certificates (finite_set S) := 
match NotSel with
| Assert_Not_Selective (s1, s2) =>     
{|
  sg_CI_associative        := Assert_Associative 
; sg_CI_congruence         := Assert_Bop_Congruence 
; sg_CI_commutative        := Assert_Commutative 
; sg_CI_idempotent         := Assert_Idempotent 
; sg_CI_not_selective      := Assert_Not_Selective (s1 :: nil, s2 :: nil)
|}
end. 

Definition sg_CNI_certs_minset_lift_from_po
           (bComm  : @assert_commutative S) 
           (nIdem  : @assert_not_idempotent S) : @sg_CNI_certificates (finite_set S) := 
match nIdem with
| Assert_Not_Idempotent i =>     
{|
  sg_CNI_associative      := Assert_Associative 
; sg_CNI_congruence       := Assert_Bop_Congruence 
; sg_CNI_commutative      := Assert_Commutative 
; sg_CNI_not_idempotent   := Assert_Not_Idempotent (i :: nil) 

; sg_CNI_cancel_d         := Certify_Not_Left_Cancellative (nil, (wS :: nil, (f wS) :: nil))
; sg_CNI_constant_d       := Certify_Not_Left_Constant (wS :: nil, (wS :: nil, nil))
; sg_CNI_anti_left_d      := Certify_Not_Anti_Left (nil, nil) 
; sg_CNI_anti_right_d     := Certify_Not_Anti_Right (nil, nil) 
|}
end. 

End Proofs.


Section Combinators. 

Definition sg_CNI_minset_lift_GUARDED 
           (S : Type)
           (A : @bounded_monotone_increasing_posg S) 
           (bComm : @assert_commutative S) 
           (bNotIdem : @assert_not_idempotent S) : @sg_BCNI (finite_set S) :=             
let eqv := bmiposg_eqv A in
let eq  := eqv_eq eqv in
let wS  := eqv_witness eqv in
let f  := eqv_new eqv in
let lte := bmiposg_lte A in 
let bop := bmiposg_times A in
{|
  sg_BCNI_eqv        := eqv_minset_from_po_bounded (po_from_bounded_monotone_increasing_posg A)
; sg_BCNI_bop        := bop_minset_lift S eq lte bop
; sg_BCNI_exists_id  := match bounded_bottom_id (bmiposg_top_bottom A) with
                        | Assert_Os_Exists_Bottom_Id_Equal bottom =>
                          Assert_Exists_Id (bottom :: nil) 
                        end 
; sg_BCNI_exists_ann := Assert_Exists_Ann nil 
; sg_BCNI_certs      := sg_CNI_certs_minset_lift_from_po S wS f bComm bNotIdem 
; sg_BCNI_ast        := Ast_sg_minset_lift (bmiposg_ast A)
|}.  


Definition sg_BCI_minset_lift_GUARDED 
           (S : Type)
           (A : @bounded_monotone_increasing_posg S) 
           (bComm : @assert_commutative S) 
           (bIdem : @assert_idempotent S)
           (bNotSel : @assert_not_selective S) : @sg_BCI (finite_set S) :=             
let eqv := bmiposg_eqv A in
let eq  := eqv_eq eqv in
let wS  := eqv_witness eqv in
let f  := eqv_new eqv in
let lte := bmiposg_lte A in 
let bop := bmiposg_times A in
{|
  sg_BCI_eqv        := eqv_minset_from_po_bounded (po_from_bounded_monotone_increasing_posg A)
; sg_BCI_bop        := bop_minset_lift S eq lte bop
; sg_BCI_exists_id  := match bounded_bottom_id (bmiposg_top_bottom A) with
                        | Assert_Os_Exists_Bottom_Id_Equal bottom =>
                          Assert_Exists_Id (bottom :: nil) 
                        end 
; sg_BCI_exists_ann := Assert_Exists_Ann nil 
; sg_BCI_certs      := sg_CI_certs_minset_lift_from_po S bComm bIdem bNotSel
; sg_BCI_ast        := Ast_sg_minset_lift (bmiposg_ast A)
|}.  


End Combinators.   

End CAS.

Section AMCAS.

Local Open Scope string_scope.

Definition mcas_minset_lift {S : Type} (M : @os_mcas S) : @sg_mcas (finite_set S ) :=
match M with
| OS_bounded_monotone_increasing_posg A => 
  let bopP   := bmiposg_times_certs A in
  let comm_d := sg_commutative_d bopP in
  let idem_d := sg_idempotent_d bopP in
  let sel_d  := sg_selective_d bopP in
  match comm_d with
  | Certify_Commutative =>
    match idem_d with 
    | Certify_Idempotent  =>
      match sel_d with
      | Certify_Selective =>
           MCAS_sg_Error ("mcas_minset_lift : (currently) multiplication cannot be selective" :: nil)
      | Certify_Not_Selective p  =>
           MCAS_sg_BCI (sg_BCI_minset_lift_GUARDED _ A  Assert_Commutative Assert_Idempotent (Assert_Not_Selective p))
      end 
    | Certify_Not_Idempotent i => MCAS_sg_BCNI (sg_CNI_minset_lift_GUARDED _ A Assert_Commutative (Assert_Not_Idempotent i)) 
    end        
  | i_    => MCAS_sg_Error ("mcas_minset_lift : (currently) multiplication must be commutative" :: nil)
  end
| _ => MCAS_sg_Error ("mcas_minset_lift : (currently) can only be applied to a bounded, monotone, and increasing order-semigroup" :: nil)
end. 

End AMCAS.

Section Verify.

Section Proofs.

Variables (S : Type)
          (eq lte : brel S)
          (wS : S) (f : S -> S)
          (nt : brel_not_trivial S eq f)
          (eqvP : eqv_proofs S eq)
          (bop : binary_op S) 
          (bopP : sg_proofs S eq bop)
          (LM : os_left_monotone lte bop)
          (RM : os_right_monotone lte bop)
          (DDD : (brel_antisymmetric S eq lte) +
               ((os_left_strictly_monotone lte bop) * (os_right_strictly_monotone lte bop)))
          (LI : os_left_increasing lte bop) 
          (comm : bop_commutative S eq bop).

Lemma correct_sg_CNI_certs_minset_lift_from_po (nidem : bop_not_idempotent S eq bop) (po : po_proofs S eq lte) :
  P2C_sg_CNI (finite_set S)
             (brel_minset eq lte)
             (bop_minset_lift S eq lte bop)
             (sg_CNI_proofs_minset_lift_from_po S eq lte wS f bop nt eqvP po LM RM DDD bopP comm nidem)
      =
      sg_CNI_certs_minset_lift_from_po S wS f Assert_Commutative (Assert_Not_Idempotent (projT1 nidem)).
Proof. unfold sg_CNI_certs_minset_lift_from_po, sg_CNI_proofs_minset_lift_from_po,  P2C_sg_CNI; simpl.
       destruct nidem as [i A]; simpl. 
       reflexivity.
Qed.        


Lemma correct_sg_CI_certs_minset_lift_from_po (idem : bop_idempotent S eq bop) (nsel : bop_not_selective S eq bop) (po : po_proofs S eq lte) :
  P2C_sg_CI (finite_set S)
             (brel_minset eq lte)
             (bop_minset_lift S eq lte bop)
             (sg_CI_proofs_minset_lift_from_po S eq lte bop eqvP po LM RM DDD comm idem nsel bopP LI)
      =
      sg_CI_certs_minset_lift_from_po S Assert_Commutative Assert_Idempotent (Assert_Not_Selective (projT1 nsel)).
Proof. unfold sg_CI_certs_minset_lift_from_po, sg_CI_proofs_minset_lift_from_po,  P2C_sg_CI; simpl.
       destruct nsel as [[s1 s2] [A B]]; simpl. unfold p2c_not_selective_assert. simpl. 
       reflexivity.
Qed.        

End Proofs.

Section Combinators.

Theorem correct_sg_BCI_minset_lift_GUARDED  (S : Type)
        (A : A_bounded_monotone_increasing_posg S) 
        (comm : bop_commutative S (A_eqv_eq S (A_bmiposg_eqv S A)) (A_bmiposg_times S A))
        (idem : bop_idempotent S (A_eqv_eq S (A_bmiposg_eqv S A)) (A_bmiposg_times S A))
        (nSel : bop_not_selective S (A_eqv_eq S (A_bmiposg_eqv S A)) (A_bmiposg_times S A)) : 
  A2C_sg_BCI (finite_set S) (A_sg_BCI_minset_lift_GUARDED S A comm idem nSel)                          
  =
  sg_BCI_minset_lift_GUARDED S
       (A2C_bounded_monotone_increasing_posg A)
       (Assert_Commutative)
       (Assert_Idempotent)
       (Assert_Not_Selective (projT1 nSel)). 
Proof. unfold A_sg_BCI_minset_lift_GUARDED, sg_BCI_minset_lift_GUARDED.
       destruct A; unfold A2C_sg_BCI, A2C_bounded_monotone_increasing_posg. simpl. 
       rewrite <- correct_eqv_minset_from_po_bounded.
       rewrite correct_sg_CI_certs_minset_lift_from_po.
       reflexivity. 
Qed.

Theorem correct_sg_BCNI_minset_lift_GUARDED  (S : Type)
        (A : A_bounded_monotone_increasing_posg S) 
        (comm : bop_commutative S (A_eqv_eq S (A_bmiposg_eqv S A)) (A_bmiposg_times S A))
        (nidem : bop_not_idempotent S (A_eqv_eq S (A_bmiposg_eqv S A)) (A_bmiposg_times S A)) : 
  A2C_sg_BCNI (finite_set S) (A_sg_CNI_minset_lift_GUARDED S A comm nidem)                          
  =
  sg_CNI_minset_lift_GUARDED S
       (A2C_bounded_monotone_increasing_posg A)
       (Assert_Commutative)
       (Assert_Not_Idempotent (projT1 nidem)).      
Proof. unfold A_sg_CNI_minset_lift_GUARDED, sg_CNI_minset_lift_GUARDED.
       destruct A; unfold A2C_sg_BCNI, A2C_bounded_monotone_increasing_posg. simpl. 
       rewrite <- correct_eqv_minset_from_po_bounded.
       rewrite correct_sg_CNI_certs_minset_lift_from_po.
       reflexivity. 
Qed.

Theorem correct_mcas_minset_lift (S : Type) (M : A_os_mcas S) :
  mcas_minset_lift (A2C_mcas_os M) 
  = 
  A2C_mcas_sg _ (A_mcas_minset_lift S M).
Proof. unfold mcas_minset_lift, A_mcas_minset_lift.
       destruct M; simpl; try reflexivity. 
       destruct a; simpl. destruct A_bmiposg_times_proofs; simpl.
       destruct A_sg_commutative_d as [comm | ncomm]; simpl.
       + destruct A_sg_idempotent_d as [idem | [i nidem]]; simpl.
         ++ destruct A_sg_selective_d as [sel | nsel]; simpl. (* destruct A_sg_selective_d as [sel | [[s1 s2] [A B]]]; simpl.*)
            +++ reflexivity. 
            +++ rewrite correct_sg_BCI_minset_lift_GUARDED. reflexivity. 
         ++ rewrite correct_sg_BCNI_minset_lift_GUARDED. reflexivity. 
       + reflexivity. 
Qed. 

  
End Combinators.     
 
End Verify.   
  
********************************************************************************************)
