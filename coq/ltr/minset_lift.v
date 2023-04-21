
Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.

Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.eqv.theory. 
Require Import CAS.coq.eqv.set.
Require Import CAS.coq.eqv.minset.

Require Import CAS.coq.po.properties.
Require Import CAS.coq.po.structures.
Require Import CAS.coq.po.theory. 

Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures.
Require Import CAS.coq.sg.lift.

Require Import CAS.coq.os.properties.
Require Import CAS.coq.os.structures.

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

Variable L : Type
Variable ltrS : left_transform L S. 
Variable LM : olt_monotone S lteS bS. 

Variable DDD : (brel_antisymmetric S rS lteS) +
               ((olt_strictly_monotone S lteS bS) * (olt_strictly_monotone S lteS bS)). 


Definition bop_minset_lift : binary_op (finite_set S)
  := λ X Y, uop_minset lteS (bop_lift rS bS (uop_minset lteS X) (uop_minset lteS Y)). 



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

Lemma bop_minset_lift_congruence : bop_congruence (finite_set S) (brel_minset rS lteS) bop_minset_lift.
Proof. unfold bop_congruence. intros X1 X2 Y1 Y2 A B.
       unfold bop_minset_lift.
       unfold brel_minset in A, B. 
       assert (C := bop_lift_congruence _ _ _ _ A B).
       assert (D := uop_minset_congruence_weak _ _ C).
       unfold brel_minset. 
       apply uop_minset_congruence_weak; auto. 
Qed.

Lemma minset_lift_commutative_weak (comm : bop_commutative S rS bS) (X Y : finite_set S) : ([ms] (X [^] Y)) [=MS] ([ms] (Y [^] X)). 
Proof. assert (A : (X [^] Y) [=S] (Y [^] X)).
          apply bop_lift_commutative; auto. 
       assert (B := uop_minset_congruence_weak _ _ A).
       apply uop_minset_congruence_weak; auto.
Qed. 

Lemma bop_minset_lift_commutative (comm : bop_commutative S rS bS) :
     bop_commutative (finite_set S) (brel_minset rS lteS) bop_minset_lift.
Proof. intros X Y. unfold bop_minset_lift. apply minset_lift_commutative_weak; auto. Qed. 


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
          rewrite minset_singleton in B. rewrite minset_singleton in B. 
          assert (C := uop_minset_idempotent ((s :: nil) [^] (t :: nil))).  
          assert (D := uop_minset_idempotent ((t :: nil) [^] (s :: nil))).
          apply set_symmetric in C.
          assert (E := set_transitive _ _ _ C B). 
          assert (F := set_transitive _ _ _ E D). 
          assert (G := bop_lift_singletons s t). 
          assert (H := bop_lift_singletons t s). 
          assert (I : ([ms] ((s :: nil) [^] (t :: nil))) [=S] ((bS s t) :: nil)).
             assert (J := uop_minset_congruence_weak _ _ G).
             rewrite minset_singleton in J; auto. 
          assert (J : ([ms] ((t :: nil) [^] (s :: nil))) [=S] ((bS t s) :: nil)). 
             assert (J := uop_minset_congruence_weak _ _ G).
             rewrite minset_singleton in J; auto. 
          apply set_symmetric in I.
          assert (K := set_transitive _ _ _ I F).
          assert (L := set_transitive _ _ _ K J). 
          compute in L.  rewrite A in L. discriminate L. 
Defined. 

Lemma below_pseudo_transitive_left (s t u : S) : s <<= t -> t << u -> s << u.
Proof. intros A B. apply below_elim in B. destruct B as [B C]. 
       apply below_intro. 
         exact (lteTrans _ _ _ A B). 
         case_eq(lteS u s); intro D; auto. 
         rewrite (lteTrans _ _ _ D A) in C. discriminate C. 
Qed. 


Lemma below_pseudo_transitive_right (s t u : S) : s << t -> t <<= u -> s << u.
Proof. intros A B. apply below_elim in A. destruct A as [A C]. 
       apply below_intro. 
         exact (lteTrans _ _ _ A B). 
         case_eq(lteS u s); intro D; auto. 
         rewrite (lteTrans _ _ _ B D) in C. discriminate C. 
Qed. 



Lemma minset_lift_right_inclusion_1 (X Y : finite_set S) (a : S) (H : a [in] ([ms] (X [^] Y))) : 
     a [in] ([ms] (([ms] X) [^] Y)).
Proof. apply in_minset_elim in H; auto. destruct H as [H1 H2].
        apply in_set_bop_lift_elim in H1; auto.
        destruct H1 as [x [y [[H3 H4] H5]]]. 
        apply in_minset_intro; auto. split.
           apply symS in H5. 
           rewrite (in_set_right_congruence S rS symS tranS (bS x y) a (([ms] X) [^] Y) H5);auto.
           case_eq(in_set rS ([ms] X) x); intro H6.
              apply in_set_bop_lift_intro; auto. 
              assert (B := H6). 
              apply in_set_minset_false_elim in B; auto.
              destruct B as [s [H7 H8]]. apply below_elim in H8.  destruct H8 as [H8 H9].
              assert (R := RM y _ _ H8).
              case_eq (lteS (bS x y) (bS s y)) ; intro H10. assert (H7' := H7). 
                 apply in_minset_elim in H7; auto. 
                 destruct H7 as [H7 _]. 
                 assert ((bS s y) [in] (X [^] Y)). apply in_set_bop_lift_intro; auto. 
                 assert (H11 := H2 _ H). 
                 apply symS in H5.
                 rewrite(below_congruence _ _ _ lteCong _ _ _ _ H5 (refS (bS s y))) in H11.
                 apply below_false_elim in H11. 
                 destruct H11 as [H11 | H11].
                    rewrite H11 in R. discriminate R.
                    destruct DDD as [AntiSym | [_ RSM]] .
                       (* AntiSym *) 
                       assert (G := AntiSym _ _ R H10).
                       rewrite (in_set_right_congruence S rS symS tranS _  _ (([ms] X) [^] Y) G); auto. 
                       apply in_set_bop_lift_intro; auto.
                       (* RSM *) 
                     destruct (RSM y  _  _ H8 H9) as [H12 H13].
                     rewrite H13 in H10. discriminate H10. 

                 assert (H11 : bS s y [in] (X [^] Y)).
                    apply in_set_bop_lift_intro; auto.
                    apply in_minset_elim in H7; auto.                     
                    destruct H7 as [H7 _]; auto. 
                 assert (Q := H2 (bS s y) H11). apply below_false_elim in Q.   destruct Q as [H12 | H12]. 
                    apply symS in H5. rewrite (lteCong _ _ _ _ (refS (bS s y)) H5) in H12.
                    rewrite H12 in R. discriminate R. 
                    apply symS in H5. rewrite (lteCong _ _ _ _ H5 (refS (bS s y))) in H12.
                    rewrite H12 in H10. discriminate H10.                    

           intros s H6.  apply H2. 
           apply in_set_bop_lift_elim in H6; auto.
           destruct H6 as [x' [y' [[H7 H8] H9]]].
           apply symS in H9. 
           rewrite (in_set_right_congruence S rS symS tranS (bS x' y') s (X [^] Y) H9);auto. 
           apply in_set_bop_lift_intro; auto.
           apply in_minset_elim in H7; auto. destruct H7 as [H7 _]; auto. 
Qed.            



(* nb : this did not use strictness or antisym *) 
Lemma minset_lift_right_inclusion_2 (X Y : finite_set S) (a : S) (H : a [in] ([ms] (([ms] X) [^] Y))) : 
  a [in] ([ms] (X [^] Y)).
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

(* note : clean these up someday?  *) 

Lemma minset_lift_left_invariant_v0 (X Y : finite_set S) :  [ms] (([ms] X) [^] Y) [=S] [ms] (X [^] Y). 
Proof. apply brel_set_intro_prop; auto. split.
       apply minset_lift_right_inclusion_2; auto.        
       apply minset_lift_right_inclusion_1; auto.        
Qed. 

Lemma minset_lift_left_invariant_v1 (X Y : finite_set S) :  [ms] (([ms] X) [^] Y) [=MS] [ms] (X [^] Y). 
Proof. assert (A := minset_lift_left_invariant_v0 X Y).
       apply set_equal_implies_minset_equal; auto. 
Qed.


(* proves   (([ms] X) <^> Y) [=S] (X <^> Y)   *) 
Lemma minset_lift_left_invariant_v2 : 
     bop_left_uop_invariant (finite_set S) (brel_set rS) bop_minset_lift (uop_minset lteS).
Proof. unfold bop_left_uop_invariant. intros X Y. 
       apply brel_set_intro_prop; auto. split. 
          intros a H.
          apply minset_lift_right_inclusion_2; auto. 
          intros a H.
          apply minset_lift_right_inclusion_1; auto. 
Qed.

(* (([ms] X) <^> Y) [=MS] (X <^> Y)   *) 
Lemma minset_lift_left_invariant :
     bop_left_uop_invariant (finite_set S) (brel_minset rS lteS) bop_minset_lift (uop_minset lteS).
Proof. intros X Y. 
       assert (A := minset_lift_left_invariant_v2 X Y). 
       apply set_equal_implies_minset_equal; auto. 
Qed.




Lemma minset_lift_left_inclusion_1 (X Y : finite_set S) (a : S) (H : a [in] ([ms] (X [^] Y))) : 
  a [in] ([ms] (X [^] ([ms] Y))).
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
                    apply in_set_bop_lift_intro; auto.
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
Lemma minset_lift_left_inclusion_2 (X Y : finite_set S) (a : S) (H : a [in] ([ms] (X [^] ([ms] Y)))) : 
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
                    assert (G := below_not_reflexive _ _ lteRefl (bS b c)). 
                    rewrite G in E. discriminate E. 
                 
Qed.



Lemma minset_lift_right_invariant_v0 (X Y : finite_set S) :  [ms] (X [^] ([ms] Y)) [=S] [ms] (X [^] Y). 
Proof. apply brel_set_intro_prop; auto. split.
       apply minset_lift_left_inclusion_2; auto.        
       apply minset_lift_left_inclusion_1; auto.        
Qed. 

Lemma minset_lift_right_invariant_v1 (X Y : finite_set S) :  [ms] (X [^] ([ms] Y)) [=MS] [ms] (X [^] Y). 
Proof. assert (A := minset_lift_right_invariant_v0 X Y).
       apply set_equal_implies_minset_equal; auto. 
Qed.


Lemma minset_lift_right_invariant_v2 :
     bop_right_uop_invariant (finite_set S) (brel_set rS) bop_minset_lift (uop_minset lteS).
Proof. unfold bop_right_uop_invariant. intros X Y. 
       apply brel_set_intro_prop; auto. split. 
          intros a H. apply minset_lift_left_inclusion_2; auto. 
          intros a H. apply minset_lift_left_inclusion_1; auto. 
Qed.

Lemma minset_lift_right_invariant :
     bop_right_uop_invariant (finite_set S) (brel_minset rS lteS) bop_minset_lift (uop_minset lteS).
Proof. intros X Y. 
       assert (A := minset_lift_right_invariant_v2 X Y). 
       apply set_equal_implies_minset_equal; auto. 
Qed.





(*       
Lemma bop_uop_minset_invariant (X Y : finite_set S): [ms] (([ms] X) [^] ([ms] Y)) [=MS] [ms] (X [^] Y). 
Proof.  assert (A : [ms] (([ms] X) [^] ([ms] Y)) [=MS] [ms] (X [^] ([ms] Y))).
          apply minset_lift_right_invariant. 
        assert (B := bop_right_uop_minset_invariant_right X Y).
        apply brel_minset_symmetric in B.   
        exact (minset_transitive _ _ _ A B). 
Qed.
 *)



Lemma bop_minset_lift_associative : bop_associative (finite_set S) (brel_minset rS lteS) bop_minset_lift.
Proof. intros X Y Z.
       assert (A : ((X <^> Y) <^> Z) [=MS] [ms] (([ms] (X <^> Y)) [^] ([ms] Z))).
           apply brel_minset_reflexive; auto. 
       assert (B : [ms] (([ms] (X <^> Y)) [^] ([ms] Z)) [=MS]  [ms] ((X <^> Y) [^] ([ms] Z))). 
           apply minset_lift_left_invariant.
       assert (C : ((X <^> Y) <^> Z) [=MS] [ms] ((X <^> Y) [^] ([ms] Z))). 
          exact (minset_transitive _ _ _ A B).
       assert (D : [ms] ((X <^> Y) [^] ([ms] Z))  [=MS] [ms] ([ms] (([ms] X) [^] ([ms] Y)) [^] ([ms] Z))). 
           apply brel_minset_reflexive; auto. 
       assert (E : ((X <^> Y) <^> Z) [=MS] [ms] ([ms] (([ms] X) [^] ([ms] Y)) [^] ([ms] Z))). 
          exact (minset_transitive _ _ _ C D).
          assert (F : [ms] (([ms] (([ms] X) [^] ([ms] Y))) [^] ([ms] Z)) [=MS] [ms] ((([ms] X) [^] ([ms] Y)) [^] ([ms] Z))).
             apply minset_lift_left_invariant_v1. 
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
           apply minset_lift_right_invariant_v1. 
       assert (K : ((X <^> Y) <^> Z) [=MS] [ms] (([ms] X) [^] ([ms] (([ms] Y) [^] ([ms] Z))))).
          exact(minset_transitive _ _ _  I J).
       assert (L : [ms] (([ms] X) [^] ([ms] (([ms] Y) [^] ([ms] Z)))) [=MS] [ms] (([ms] X) [^] (Y <^> Z))).
          apply brel_minset_reflexive; auto. 
       assert (M : ((X <^> Y) <^> Z) [=MS] [ms] (([ms] X) [^] (Y <^> Z))).
          exact(minset_transitive _ _ _  K L).
       assert (N : [ms] (([ms] X) [^] (Y <^> Z)) [=MS] [ms] (([ms] X) [^] ([ms] (Y <^> Z)))).
           apply brel_minset_symmetric. 
           apply minset_lift_right_invariant_v1. 
       assert (O : ((X <^> Y) <^> Z) [=MS] [ms] (([ms] X) [^] ([ms] (Y <^> Z)))).
          exact(minset_transitive _ _ _  M N).
       assert (P : [ms] (([ms] X) [^] ([ms] (Y <^> Z))) [=MS] (X <^> (Y <^> Z))). 
          apply brel_minset_reflexive; auto. 
       exact(minset_transitive _ _ _  O P).
Qed. 


Lemma bop_minset_lift_nil_left (X : finite_set S) :  (nil <^> X) [=MS] nil. 
Proof. unfold bop_minset_lift. unfold brel_minset.        
       rewrite minset_empty. compute; auto. 
Qed. 

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
Proof. unfold bop_minset_lift. unfold brel_minset.        
       rewrite minset_empty.
       assert (A := bop_lift_nil_right ([ms] X)). 
       assert (B := uop_minset_congruence_weak _ _ A).
       rewrite minset_empty in B. 
       assert (C := uop_minset_idempotent (([ms] X) [^] nil)). 
       exact (set_transitive _ _ _ C B). 
Qed. 

Lemma bop_minset_lift_ann_is_nil : bop_is_ann (finite_set S) (brel_minset rS lteS) bop_minset_lift nil. 
Proof. split. 
         apply bop_minset_lift_nil_left. 
         apply bop_minset_lift_nil_right.
Qed.

Lemma bop_minset_lift_exists_ann : bop_exists_ann (finite_set S) (brel_minset rS lteS) bop_minset_lift. 
Proof. exists nil. apply bop_minset_lift_ann_is_nil. Defined.

Lemma bop_minset_lift_id_is_bottom (b : S) (P : bop_is_id S rS bS b) : 
      bop_is_id (finite_set S) (brel_minset rS lteS) bop_minset_lift (b :: nil). 
Proof. intro X.   
       destruct (bop_lift_is_id _ _ _ refS tranS symS bCong b P X) as [L R]. 
       unfold brel_minset. unfold bop_minset_lift.
       rewrite minset_singleton. split. 
          assert (A := uop_minset_idempotent ((b :: nil) [^] ([ms] X))). 
          assert (B := minset_lift_right_invariant_v0 (b :: nil) X). 
          assert (C := set_transitive _ _ _ A B). 
          assert (D := uop_minset_congruence_weak _ _ L). 
          exact (set_transitive _ _ _ C  D). 

          assert (A := uop_minset_idempotent (([ms] X) [^] (b :: nil))). 
          assert (B := minset_lift_left_invariant_v0 X (b :: nil) ). 
          assert (C := set_transitive _ _ _ A B). 
          assert (D := uop_minset_congruence_weak _ _ R).  
          exact (set_transitive _ _ _ C  D). 
Qed. 

Lemma bop_minset_lift_exists_id : bop_exists_id (finite_set S) (brel_minset rS lteS) bop_minset_lift. 
Proof. destruct bId as [b P]. exists (b :: nil). apply bop_minset_lift_id_is_bottom; auto. Defined. 

Lemma not_not_selective_implies_bop_minset_lift_not_selective :
         (bop_not_selective S rS bS) → bop_not_selective (finite_set S) (brel_minset rS lteS) bop_minset_lift. 
Proof. intros [ [s t] [A B]]. 
       exists (s :: nil, t :: nil). 
          unfold bop_minset_lift.        
          unfold brel_minset. rewrite minset_singleton.  rewrite minset_singleton. split.
          case_eq(brel_set rS ([ms] ([ms] ((s :: nil) [^] ([ms] (t :: nil))))) (s :: nil)); intro C; auto. 
             assert (D := uop_minset_idempotent ((s :: nil) [^] ([ms] (t :: nil)))).
             assert (E := minset_lift_left_invariant_v0 (s :: nil) (t :: nil)). 
             assert (F := bop_lift_singletons s t).
             assert (G := uop_minset_congruence_weak _ _ F). 
             rewrite minset_singleton in G. 
             assert (H := set_transitive _ _ _ E G).
             assert (I := set_transitive _ _ _ D H). apply set_symmetric in C. 
             assert (J := set_transitive _ _ _ C I).
             compute in J. rewrite A in J.
             case_eq(rS s (bS s t)); intro K. (* need better way of dealing with <> *) 
                apply symS in K. rewrite K in A. discriminate A. 
                rewrite K in J. discriminate J. 
          case_eq(brel_set rS ([ms] ([ms] ((s :: nil) [^] (t :: nil)))) (t :: nil)); intro C; auto. 
             assert (D := uop_minset_idempotent ((s :: nil) [^] ([ms] (t :: nil)))).
             assert (E := minset_lift_left_invariant_v0 (s :: nil) (t :: nil)). 
             assert (F := bop_lift_singletons s t).
             assert (G := uop_minset_congruence_weak _ _ F). 
             rewrite minset_singleton in G. 
             assert (H := set_transitive _ _ _ E G).
             assert (I := set_transitive _ _ _ D H). apply set_symmetric in C. 
             assert (J := set_transitive _ _ _ C I).
             compute in J. rewrite B in J.
             case_eq(rS t (bS s t)); intro K. (* need better way of dealing with <> *) 
                apply symS in K. rewrite K in B. discriminate B. 
                rewrite K in J. discriminate J. 
Defined. 


Lemma bop_minset_lift_not_is_left : bop_not_is_left (finite_set S) (brel_minset rS lteS) bop_minset_lift. 
Proof. exists (wS :: nil, nil).
       unfold brel_minset. unfold bop_minset_lift.
       rewrite minset_singleton.  rewrite minset_empty. compute; auto. 
Defined. 


Lemma bop_minset_lift_not_is_right : bop_not_is_right (finite_set S) (brel_minset rS lteS) bop_minset_lift. 
Proof. exists (nil, wS :: nil).
       unfold brel_minset. unfold bop_minset_lift.
       rewrite minset_singleton.  rewrite minset_empty. compute; auto. 
Defined. 


Lemma bop_minset_lift_not_anti_left : bop_not_anti_left (finite_set S) (brel_minset rS lteS) bop_minset_lift. 
Proof. exists (nil, nil). compute; auto.  Defined. 

Lemma bop_minset_lift_not_anti_right : bop_not_anti_right (finite_set S) (brel_minset rS lteS) bop_minset_lift. 
Proof. exists (nil, nil). compute; auto.  Defined.


Lemma uop_minset_equational_idempotence (X Y : finite_set S): 
  ([ms] ([ms] X)) [=S] ([ms] ([ms] Y)) -> ([ms] X) [=S] ([ms] Y). 
Proof. intro A.
       assert (B := minset_idempotent X). 
       assert (C := minset_idempotent Y).
       apply set_symmetric in B. 
       assert (D := set_transitive _ _ _ B A). 
       exact (set_transitive _ _ _ D C).        
Qed. 


Lemma bop_minset_lift_not_left_constant : bop_not_left_constant (finite_set S) (brel_minset rS lteS) bop_minset_lift.
Proof. unfold bop_not_left_constant.
       destruct bId as [b P].
       exists (b :: nil, (wS :: nil, (f wS) :: nil)).
       unfold brel_minset. unfold bop_minset_lift. 
       rewrite minset_singleton. rewrite minset_singleton. rewrite minset_singleton.
       case_eq(brel_set rS ([ms] ([ms] ((b :: nil) [^] (wS :: nil)))) ([ms] ([ms] ((b :: nil) [^] (f wS :: nil))))); intro A; auto. 
       apply uop_minset_equational_idempotence in A. 
       assert (B := bop_lift_singletons b wS).
       assert (C := bop_lift_singletons b (f wS)).       
       assert (D := uop_minset_congruence_weak _ _ B).
       assert (E := uop_minset_congruence_weak _ _ C).        
       assert (F := set_transitive _ _ _ A E).
       apply set_symmetric in D. 
       assert (G := set_transitive _ _ _ D F).
       rewrite minset_singleton in G. rewrite minset_singleton in G.
       compute in G.        
       assert (H : rS (bS b wS) (bS b (f wS)) = false). 
          destruct (Pf wS) as [I J].
          destruct (P wS) as [K L].     apply symS in K. 
          destruct (P (f wS)) as [M N]. apply symS in M. 
          rewrite (congS _ _ _ _ K M) in I; auto. 
       rewrite H in G.  discriminate G. 
Defined. 

       
Lemma bop_minset_lift_not_right_constant : bop_not_right_constant (finite_set S) (brel_minset rS lteS) bop_minset_lift. 
Proof. unfold bop_not_right_constant.
       destruct bId as [b P].
       exists (b :: nil, (wS :: nil, (f wS) :: nil)).
       unfold brel_minset. unfold bop_minset_lift. 
       rewrite minset_singleton. rewrite minset_singleton. rewrite minset_singleton.
       case_eq(brel_set rS ([ms] ([ms] ((wS :: nil) [^] (b :: nil)))) ([ms] ([ms] ((f wS :: nil) [^] (b :: nil))))); intro A; auto. 
       apply uop_minset_equational_idempotence in A. 
       assert (B := bop_lift_singletons wS b).
       assert (C := bop_lift_singletons (f wS) b).       
       assert (D := uop_minset_congruence_weak _ _ B).
       assert (E := uop_minset_congruence_weak _ _ C).        
       assert (F := set_transitive _ _ _ A E).
       apply set_symmetric in D. 
       assert (G := set_transitive _ _ _ D F).
       rewrite minset_singleton in G. rewrite minset_singleton in G.
       compute in G.        
       assert (H : rS (bS wS b) (bS (f wS) b) = false). 
          destruct (Pf wS) as [I J].
          destruct (P wS) as [K L].     apply symS in L. 
          destruct (P (f wS)) as [M N]. apply symS in N. 
          rewrite (congS _ _ _ _ L N) in I; auto. 
       rewrite H in G.  discriminate G. 
Defined. 



Lemma bop_minset_lift_not_left_cancellative : bop_not_left_cancellative (finite_set S) (brel_minset rS lteS) bop_minset_lift.
Proof. exists (nil, (wS :: nil, (f wS) :: nil)). 
       destruct (Pf wS) as [L R]. split. 
          compute; auto. 
          case_eq(brel_minset rS lteS (wS :: nil) (f wS :: nil)); intro F; auto.
          unfold brel_minset in F. 
          rewrite minset_singleton in F. rewrite minset_singleton in F. 
          compute in F. rewrite L in F. discriminate F. 
Defined. 


Lemma bop_minset_lift_not_right_cancellative : bop_not_right_cancellative (finite_set S) (brel_minset rS lteS) bop_minset_lift.
Proof. exists (nil, (wS :: nil, (f wS) :: nil)). 
       destruct (Pf wS) as [L R]. split. 
          compute; auto. 
          case_eq(brel_minset rS lteS (wS :: nil) (f wS :: nil)); intro F; auto.
          unfold brel_minset in F. 
          rewrite minset_singleton in F. rewrite minset_singleton in F. 
          compute in F. rewrite L in F. discriminate F. 
Defined. 



End Theory.

Section ACAS.

(*  
Definition sg_CI_proofs_minset_lift_from_po : 
  ∀ (S : Type) (rS lteS : brel S) (s : S) (f : S -> S) ,
     brel_not_trivial S rS f ->     
     eqv_proofs S rS -> po_proofs S rS lteS -> 
        sg_CI_proofs (finite_set S) (brel_minset rS lteS) (bop_minset_lift S rS lteS)
  := λ S rS lteS s f ntS eqvS poS,
let congS := A_eqv_congruence S rS eqvS in  
let refS := A_eqv_reflexive S rS eqvS in
let symS := A_eqv_symmetric S rS eqvS in
let tranS := A_eqv_transitive S rS eqvS in

let lteCong    := A_po_congruence S rS lteS poS in
let lteRefl    := A_po_reflexive S rS lteS poS in
let lteTran    := A_po_transitive S rS lteS poS in
let lteAntiSym := A_po_antisymmetric S rS lteS poS in 
let tot_d      := A_po_total_d S rS lteS poS in 
{|
  A_sg_CI_associative        := bop_minset_lift_associative S rS refS symS tranS lteS lteCong lteRefl lteTran 
; A_sg_CI_congruence         := bop_minset_lift_congruence S rS refS symS tranS lteS lteCong lteRefl lteTran
; A_sg_CI_commutative        := bop_minset_lift_commutative S rS refS symS tranS lteS lteCong lteRefl lteTran
; A_sg_CI_idempotent         := bop_minset_lift_idempotent S rS refS symS tranS lteS lteCong lteRefl lteTran
; A_sg_CI_selective_d        := bop_minset_lift_selective_decide S rS s f ntS congS refS symS tranS lteS lteCong lteRefl lteTran tot_d
|}. 


Record msg_proofs (S: Type) (eq : brel S) (bop : binary_op S) := 
{
  A_msg_associative      : bop_associative S eq bop                OK 
; A_msg_congruence       : bop_congruence S eq bop                 OK 
; A_msg_commutative_d    : bop_commutative_decidable S eq bop      OK 

(* needed?*)                                                    
; A_msg_is_left_d        : bop_is_left_decidable S eq bop          OK 
; A_msg_is_right_d       : bop_is_right_decidable S eq bop         OK 

(***)                                                   
; A_msg_left_cancel_d    : bop_left_cancellative_decidable S eq bop OK 
K; A_msg_right_cancel_d   : bop_right_cancellative_decidable S eq bop OK 
1
; A_msg_left_constant_d  : bop_left_constant_decidable S eq bop   OK 
; A_msg_right_constant_d : bop_right_constant_decidable S eq bop  OK 

; A_msg_anti_left_d      : bop_anti_left_decidable S eq bop       OK 
; A_msg_anti_right_d     : bop_anti_right_decidable S eq bop      OK 

                                                    
}. 







Definition sg_CI_proofs_minset_lift_from_qo : 
  ∀ (S : Type) (rS lteS : brel S) (s : S) (f : S -> S) ,
     brel_not_trivial S rS f ->     
     eqv_proofs S rS -> qo_proofs S rS lteS -> 
        sg_CI_proofs (finite_set S) (brel_minset rS lteS) (bop_minset_lift S rS lteS)
  := λ S rS lteS s f ntS eqvS qoS,
let congS := A_eqv_congruence S rS eqvS in  
let refS := A_eqv_reflexive S rS eqvS in
let symS := A_eqv_symmetric S rS eqvS in
let tranS := A_eqv_transitive S rS eqvS in

let lteCong    := A_qo_congruence S rS lteS qoS in
let lteRefl    := A_qo_reflexive S rS lteS qoS in
let lteTran    := A_qo_transitive S rS lteS qoS in
let lteNotAntiSym := A_qo_not_antisymmetric S rS lteS qoS in 
{|
  A_sg_CI_associative        := bop_minset_lift_associative S rS refS symS tranS lteS lteCong lteRefl lteTran 
; A_sg_CI_congruence         := bop_minset_lift_congruence S rS refS symS tranS lteS lteCong lteRefl lteTran
; A_sg_CI_commutative        := bop_minset_lift_commutative S rS refS symS tranS lteS lteCong lteRefl lteTran
; A_sg_CI_idempotent         := bop_minset_lift_idempotent S rS refS symS tranS lteS lteCong lteRefl lteTran
; A_sg_CI_selective_d        := inr (brel_not_antisymmetric_implies_bop_minset_lift_not_selective S rS refS symS tranS lteS lteCong lteRefl lteTran lteNotAntiSym)
|}. 
*) 


(*
Definition A_sg_CI_minset_lift : ∀ (S : Type),  A_qo_with_bottom S -> A_sg_CI (finite_set S)
  := λ S qo,
  let eqvS := A_qowb_eqv S qo in
  let botP := A_qowb_exists_bottom S qo in 
  let eqP  := A_eqv_proofs _ eqvS in
  let congS := A_eqv_congruence _ _ eqP in    
  let refS := A_eqv_reflexive _ _ eqP in
  let symS := A_eqv_symmetric _ _ eqP in
  let tranS := A_eqv_transitive _ _ eqP in
  let eq   := A_eqv_eq _ eqvS in  
  let s    := A_eqv_witness _ eqvS in
  let f    := A_eqv_new _ eqvS in
  let ntS  := A_eqv_not_trivial _ eqvS in
  let lteS := A_qowb_lte _ qo in
  let poP  := A_qowb_proofs _ qo in
  let lteCong    := A_qo_congruence _ _ _ poP in
  let lteRefl    := A_qo_reflexive _ _ _ poP in
  let lteTran    := A_qo_transitive _ _ _ poP in

  {| 
     A_sg_CI_eqv          := A_eqv_minset S qo   HERE need eqv_minset built from qo ! *****************************
   ; A_sg_CI_bop          := bop_minset_lift S eq lteS
   ; A_sg_CI_exists_id_d  := inl (bop_minset_lift_exists_id S eq congS refS symS tranS lteS lteCong lteRefl)
   ; A_sg_CI_exists_ann_d := inl (bop_minset_lift_exists_ann S eq f ntS congS refS symS tranS lteS lteCong lteRefl lteTran botP)
   ; A_sg_CI_proofs       := sg_CI_proofs_minset_lift_from_qo S eq lteS s f ntS eqP poP 
   ; A_sg_CI_ast          := Ast_sg_minset_lift (A_po_ast S qo)                                                                   
  |}.

*) 

(*

from po:   with bottom? 

Definition A_sg_CI_minset_lift : ∀ (S : Type),  A_po S -> A_sg_CI (finite_set S)
  := λ S po,
  let eqvS := A_po_eqv S po in
  let eqP  := A_eqv_proofs _ eqvS in
  let congS := A_eqv_congruence _ _ eqP in    
  let refS := A_eqv_reflexive _ _ eqP in
  let symS := A_eqv_symmetric _ _ eqP in
  let tranS := A_eqv_transitive _ _ eqP in
  let eq   := A_eqv_eq _ eqvS in  
  let s    := A_eqv_witness _ eqvS in
  let f    := A_eqv_new _ eqvS in
  let ntS  := A_eqv_not_trivial _ eqvS in
  let lteS := A_po_lte _ po in
  let poP  := A_po_proofs _ po in
  let lteCong    := A_po_congruence _ _ _ poP in
  let lteRefl    := A_po_reflexive _ _ _ poP in
  let lteTran    := A_po_transitive _ _ _ poP in
  let lteAntiSym := A_po_antisymmetric _ _ _ poP in 
  let bf_d := A_po_bottoms_finite_d _ _ _ poP in 
  {| 
     A_sg_CI_eqv          := A_eqv_minset S po
   ; A_sg_CI_bop          := bop_minset_lift S eq lteS
   ; A_sg_CI_exists_id_d  := inl (bop_minset_lift_exists_id S eq congS refS symS tranS lteS lteCong lteRefl)
   ; A_sg_CI_exists_ann_d := bop_minset_lift_exists_ann_decide S eq s f ntS congS refS symS tranS lteS lteCong lteRefl lteTran lteAntiSym bf_d
   ; A_sg_CI_proofs       := sg_CI_proofs_minset_lift S eq lteS s f ntS eqP poP 
   
   ; A_sg_CI_ast          := Ast_sg_minset_lift (A_po_ast S po)                                                                   
  |}.




Why needed? 

    3) sg_CI_with_ann 
*) 


End ACAS.


(*
Section CAS.

Definition  check_minset_lift_exists_ann {S : Type} (df_d : @check_bottoms_finite S) : @check_exists_ann (finite_set S)
  := match df_d with
     | Certify_Bottoms_Finite (f, _)  => Certify_Exists_Ann (f tt)
     | Certify_Is_Not_Bottoms_Finite => Certify_Not_Exists_Ann
     end.

Definition  check_minset_lift_selective {S : Type} (tot_d : @check_total S) : @check_selective (finite_set S)
  := match tot_d with
     | Certify_Total            => Certify_Selective 
     | Certify_Not_Total (s, t) => Certify_Not_Selective (s :: nil, t :: nil)
     end.



Definition sg_CI_certs_minset_lift : ∀ {S : Type},  @po_certificates S -> @sg_CI_certificates (finite_set S)
:= λ {S} po,  
{|
  sg_CI_associative        := Assert_Associative  
; sg_CI_congruence         := Assert_Bop_Congruence  
; sg_CI_commutative        := Assert_Commutative  
; sg_CI_idempotent         := Assert_Idempotent  
; sg_CI_selective_d        := check_minset_lift_selective (po_total_d po)
|}. 

Definition sg_CI_minset_lift : ∀ {S : Type}, @po S -> @sg_CI (finite_set S)
  := λ S po,
  let eqvS := po_eqv po   in
  let eq   := eqv_eq eqvS in  
  let lteS := po_lte po   in   
   {| 
     sg_CI_eqv       := eqv_minset po
   ; sg_CI_bop       := bop_minset_lift S eq lteS 
   ; sg_CI_exists_id_d       := Certify_Exists_Id nil 
   ; sg_CI_exists_ann_d       := check_minset_lift_exists_ann (po_bottoms_finite_d (po_certs po))
   ; sg_CI_certs     := sg_CI_certs_minset_lift (po_certs po)
   
   ; sg_CI_ast       := Ast_sg_minset_lift (po_ast po)                                                                   
   |}. 

End CAS.
 *)

(*
Section Verify.

Lemma bop_minset_lift_certs_correct 
      (S : Type) (eq lte : brel S) (s : S) (f : S -> S) (nt : brel_not_trivial S eq f) (eqv : eqv_proofs S eq) (po : po_proofs S eq lte) : 
      sg_CI_certs_minset_lift (P2C_po S eq lte po) 
      =                        
      P2C_sg_CI (finite_set S) (brel_minset eq lte) (bop_minset_lift S eq lte)
                (sg_CI_proofs_minset_lift S eq lte s f nt eqv po).
Proof. destruct eqv, po. 
       unfold sg_CI_certs_minset_lift, sg_CI_proofs_minset_lift, P2C_sg_CI, P2C_po; simpl.
       destruct A_po_total_d as [tot | [[a b] [L R]]]; simpl; reflexivity. 
Qed. 
  

Theorem bop_minset_lift_correct (S : Type) (po : A_po S) : 
         sg_CI_minset_lift (A2C_po S po)  =  A2C_sg_CI (finite_set S) (A_sg_CI_minset_lift S po). 
Proof. unfold sg_CI_minset_lift, A_sg_CI_minset_lift, A2C_sg_CI, A2C_po; simpl.
       rewrite <- bop_minset_lift_certs_correct.
       rewrite <- correct_eqv_minset.
       destruct A_po_bottoms_finite_d as [[[F w] bf] | nbf];         
       reflexivity. 
Qed.
 
End Verify.   
  

*) 