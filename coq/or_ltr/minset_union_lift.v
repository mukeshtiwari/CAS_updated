Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.
Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.po.properties.
Require Import CAS.coq.po.structures.
Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures.
Require Import CAS.coq.tr.properties.
Require Import CAS.coq.tr.structures.
Require Import CAS.coq.ot.properties.
Require Import CAS.coq.ot.structures.
Require Import CAS.coq.st.properties.
Require Import CAS.coq.st.structures.

Require Import CAS.coq.theory.facts.
Require Import CAS.coq.theory.subset. 
Require Import CAS.coq.theory.order. (* for below, equiv, ... *)

Require Import CAS.coq.eqv.set.
Require Import CAS.coq.eqv.minset.
Require Import CAS.coq.sg.union.
Require Import CAS.coq.sg.minset_union.

Require Import CAS.coq.sg.minset_lift. 


Lemma olt_strictly_monotone_implies_left_monotone (L S : Type) (lte : brel S) (eqL : brel L) (ltr : left_transform L S):
  brel_reflexive S lte ->
  brel_reflexive L eqL ->   
  olt_strictly_monotone L S lte ltr ->
  ltr_congruence L S eqL (equiv lte) ltr ->
     olt_monotone L S lte ltr. 
Proof. intros refS refL LSM Cong s t u A.
       assert (lteRefl := equiv_reflexive S lte refS). 
       case_eq(lte u t); intro B.
          assert (C : equiv lte t u = true). apply equiv_intro; auto.       
          assert (D := Cong _ _ _ _ (refL s) C).
          apply equiv_elim in D; auto.  destruct D as [D E]. exact E. 
          destruct (LSM s t u A B) as [C D]. exact C. 
Qed.


Section Compute.

Definition fun_congruence (D R : Type) (eqD : brel D) (eqR : brel R) (f : D -> R) := 
   ∀ (s1 s2 : D) , eqD s1 s2 = true -> eqR (f s1) (f s2) = true.

Definition brel_superset {S} (eq : brel S) : brel (finite_set S)   
  := λ X Y, brel_subset eq Y X. 
     
Definition ltr_lift {L S : Type} (eq : brel S) (ltr : left_transform L S) : left_transform L (finite_set S) 
  := λ l X, uop_duplicate_elim eq (List.map (ltr l) X). 
  
Definition ltr_minset_lift {L S : Type} (eq lte : brel S) (ltr : left_transform L S) : left_transform L (finite_set S)
  := λ l X, uop_minset lte (ltr_lift eq ltr l (uop_minset lte X)). 

Definition ltr_minset_lift_v2 {L S : Type} (eq lte : brel S) (ltr : left_transform L S) : left_transform L (finite_set S)
  := λ l X, uop_minset lte (ltr_lift eq ltr l X). 

  
End Compute.   


Section Theory.

Variable S  : Type. 
Variable rS : brel S.

Variable wS : S.
Variable fS : S -> S.                
Variable Pf : brel_not_trivial S rS fS. 

Variable congS : brel_congruence S rS rS. 
Variable refS  : brel_reflexive S rS.
Variable symS  : brel_symmetric S rS.  
Variable tranS : brel_transitive S rS.

Variable lteS : brel S. 
Variable lteCong : brel_congruence S rS lteS.
Variable lteRefl : brel_reflexive S lteS.
Variable lteTrans : brel_transitive S lteS.


Variable L       : Type.
Variable eqL     : brel L.
Variable refL  : brel_reflexive L eqL.
Variable ltr     : left_transform L S. 
(* Variable ltrCong : ltr_congruence L S eqL (equiv lteS) ltr. *) 
Variable ltrCong : ltr_congruence L S eqL rS ltr.

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

Notation "a [U] b" := (bop_union rS a b)         (at level 15).
Notation "a <U> b" := (bop_minset_union S rS lteS a b)         (at level 15).

Notation "a [*] b" := (ltr a b)         (at level 15).
Notation "a [^] b" := (ltr_lift rS ltr a b)         (at level 15).
Notation "a <^> b" := (ltr_minset_lift rS lteS ltr a b)         (at level 15).


Definition set_congruence := brel_set_congruence S rS refS symS tranS.
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
Definition set_equal_implies_minset_equal := set_equal_implies_minset_equal S rS refS symS tranS lteS lteCong lteRefl lteTrans.
Definition minset_union_left_uop_invariant_weak := minset_union_left_uop_invariant_weak S rS refS symS tranS lteS lteCong lteRefl lteTrans.
Definition minset_union_right_uop_invariant_weak := minset_union_right_uop_invariant_weak S rS refS symS tranS lteS lteCong lteRefl lteTrans.
Definition minset_union_uop_invariant_weak := minset_union_uop_invariant_weak S rS refS symS tranS lteS lteCong lteRefl lteTrans.
Definition below_pseudo_transitive_left := below_pseudo_transitive_left S lteS lteTrans. 
Definition below_pseudo_transitive_right := below_pseudo_transitive_right S lteS lteTrans. 

Lemma in_set_map_elim 
      (U : Type) (eqU : brel U) (refU : brel_reflexive U eqU) (symU : brel_symmetric U eqU)
      (a : S) (Y : finite_set U) (f : U -> S) :
  a [in] List.map f Y -> {y : U & (in_set eqU Y y = true) * a [=] (f y)}.
Proof. induction Y.
       intro A. compute in A. discriminate A.
       intro A. unfold List.map in A. fold (List.map f Y) in A. 
       apply in_set_cons_elim in A; auto. destruct A as [A | A]. 
          exists a0. split. compute. rewrite (refU a0); auto. 
          apply symS in A; auto.        
          destruct (IHY A) as [y [B C]]. 
          exists y. split. 
             apply in_set_cons_intro; auto. exact C. 
Qed. 


          
Lemma in_set_map_intro (U : Type) (eqU : brel U) (a : S) (Y : finite_set U) (f : U -> S)
  (symU : brel_symmetric U eqU) (congf : fun_congruence U S eqU rS f) :
  {y : U & (in_set eqU Y y = true) * a [=] (f y)} -> a [in] List.map f Y. 
Proof. induction Y. 
       intros [y [A B]]. compute in A. discriminate A. 
       intros [y [A B]]. unfold List.map. fold (List.map f Y). 
       apply in_set_cons_elim in A; auto.         
       destruct A as [A | A].
          apply in_set_cons_intro; auto. left. 
          assert (C := congf _ _ A). 
          rewrite (congS _ _ _ _ (refS (f a0)) B). exact C. 
          apply in_set_cons_intro; auto. 
          assert (C : {y : U & (in_set eqU Y y = true) * a [=] f y}). 
             exists y; split; auto. 
          right. exact (IHY C). 
Qed. 



Lemma  in_set_ltr_lift_elim :
 ∀ (l : L) (Y : finite_set S) (a : S), 
   a [in] (l [^] Y) -> {y : S & (y [in] Y) * (a [=] (l [*] y))}.
Proof. intros l Y a H. 
       unfold ltr_lift in H.
       apply in_set_uop_duplicate_elim_elim in H.
       apply in_set_map_elim; auto. 
Defined. 


Lemma  in_set_ltr_lift_intro :
   ∀ (Y : finite_set S) (l : L) (y : S) (cong : fun_congruence S S rS rS (ltr l)), 
        y [in] Y ->  (l [*] y) [in] (l [^] Y). 
Proof. intros Y l y cong A. 
       unfold ltr_lift.
       apply in_set_uop_duplicate_elim_intro; auto.
       apply (in_set_map_intro S rS); auto.
       exists y; auto. 
Qed.


Lemma equal_implies_equiv (a b : S) (A : a [=]b): a [~]b.
Proof.  apply equiv_intro.
           rewrite (lteCong _ _ _ _ A (refS b)). exact (lteRefl b). 
           rewrite (lteCong _ _ _ _ (refS b) A). exact (lteRefl b).
Qed. 
           
(* why not make this an independent combinator? 
 *)
Lemma ltr_union_lift_monotone_subset :
 olt_monotone L (finite_set S) (brel_subset rS) (ltr_lift rS ltr). 
Proof. intros l Y Z H. 
       apply brel_subset_intro; auto.  
          intros a A.
          apply in_set_ltr_lift_elim in A; auto. 
          destruct A as [y [B C]].
          apply (in_set_right_congruence _ _ symS tranS _ _ _ (symS _ _ C)).
          assert (D : fun_congruence S S rS rS (ltr l)).
             unfold fun_congruence. intros s1 s2 D.
             exact (ltrCong _ _ _ _ (refL l) D). 
          apply in_set_ltr_lift_intro; auto.
          exact(brel_subset_elim _ _ symS tranS _ _ H _ B). 
Qed. 


Lemma ltr_union_lift_monotone_superset :
 olt_monotone L (finite_set S) (brel_superset rS) (ltr_lift rS ltr). 
Proof. intros l Y. unfold brel_superset.  intros Z H.
       apply brel_subset_intro; auto.  
          intros a A.
          apply in_set_ltr_lift_elim in A; auto. 
          destruct A as [y [B C]].
          apply (in_set_right_congruence _ _ symS tranS _ _ _ (symS _ _ C)).
          assert (D : fun_congruence S S rS rS (ltr l)).
             unfold fun_congruence. intros s1 s2 D.
             exact (ltrCong _ _ _ _ (refL l) D). 
          apply in_set_ltr_lift_intro; auto.
          exact(brel_subset_elim _ _ symS tranS _ _ H _ B). 
Qed. 




Lemma ltr_union_lift_distributive :
 slt_distributive L (finite_set S) (brel_set rS) (bop_union rS) (ltr_lift rS ltr). 
Proof. intros l Y Z.
       assert (D : fun_congruence S S rS rS (ltr l)). admit. 
       apply brel_set_intro_prop; auto.  split. 
          intros a A.
          apply in_set_ltr_lift_elim in A; auto. 
          destruct A as [y [B C]].
          apply (in_set_right_congruence _ _ symS tranS _ _ _ (symS _ _ C)).
          apply in_set_bop_union_intro; auto.
          apply in_set_bop_union_elim in B; auto.
          destruct B as [B | B].
             left. apply in_set_ltr_lift_intro; auto. 
             right. apply in_set_ltr_lift_intro; auto.           
          intros a A.
          apply in_set_bop_union_elim in A; auto. 
          destruct A as [A | A]; apply in_set_ltr_lift_elim in A; auto.
            destruct A as [y [A B]]. 
            apply (in_set_right_congruence _ _ symS tranS _ _ _ (symS _ _ B)).
            apply in_set_ltr_lift_intro; auto.
            apply in_set_bop_union_intro; auto.
            destruct A as [y [A B]]. 
            apply (in_set_right_congruence _ _ symS tranS _ _ _ (symS _ _ B)).
            apply in_set_ltr_lift_intro; auto.
            apply in_set_bop_union_intro; auto.
Admitted. 


Lemma ltr_minset_lift_left_inclusion_1
   (LM : olt_monotone L S lteS ltr)
   (DDD : (brel_antisymmetric S rS lteS) +  (olt_strictly_monotone L S lteS ltr))
   (l : L) (X Y : finite_set S) (a : S) (H : a [in] ([ms] (l [^] Y))) :  a [in] ([ms] (l [^] ([ms] Y))).
Proof.  assert (D : fun_congruence S S rS rS (ltr l)). admit. 
        apply in_minset_elim in H; auto. destruct H as [H1 H2].
        apply in_set_ltr_lift_elim in H1; auto.
        destruct H1 as [y [H3 H4]]. 
        apply in_minset_intro; auto. split.
           apply symS in H4. 
           rewrite (in_set_right_congruence S rS symS tranS _ _ _ H4);auto.
           case_eq(in_set rS ([ms] Y) y); intro H6.
              apply in_set_ltr_lift_intro; auto. 
              assert (B := H6). 
              apply in_set_minset_false_elim in B; auto.
              destruct B as [s [H7 H8]]. apply below_elim in H8. destruct H8 as [H8 H9]. 
              assert (R := LM l _ _ H8).
              case_eq (lteS (ltr l y) (ltr l s)) ; intro H10.
                 destruct DDD as [AntiSym | LSM].
                    (* AntiSym *) 
                    assert (G := AntiSym _ _ R H10).
                    rewrite (in_set_right_congruence S rS symS tranS _  _ _ G); auto. 
                    apply in_set_ltr_lift_intro; auto.
                    (* LSM *) 
                  destruct (LSM l  _  _ H8 H9) as [H11 H12].
                  rewrite H12 in H10. discriminate H10. 

                 assert (H11 : ltr l s [in] (l [^] Y)).
                    apply in_set_ltr_lift_intro; auto.
                    apply in_minset_elim in H7; auto.                     
                    destruct H7 as [H7 _]; auto.
                 assert (Q := H2 (ltr l s) H11). 
                 apply below_false_elim in Q. 
                 destruct Q as [H12 | H12]. 
                    apply symS in H4. rewrite (lteCong _ _ _ _ (refS (ltr l s)) H4) in H12.
                    rewrite H12 in R. discriminate R.
                    rewrite (lteCong _ _ _ _ (symS _ _ H4) (refS (ltr l s))) in H12.
                    rewrite H12 in H10. discriminate H10.

           intros s H6.  apply H2. 
           apply in_set_ltr_lift_elim in H6; auto.
           destruct H6 as [y' [H7 H8]].
           apply symS in H8. 
           rewrite (in_set_right_congruence S rS symS tranS _ _ (l [^] Y) H8);auto. 
           apply in_set_ltr_lift_intro; auto.
           apply in_minset_elim in H7; auto. destruct H7 as [H7 _]; auto. 
Admitted. 


Lemma ltr_minset_lift_left_inclusion_1_VII
   (LM : olt_monotone L S lteS ltr)
   (DDD : (brel_antisymmetric S rS lteS) +  (olt_strictly_increasing L S lteS ltr))
   (l : L) (X Y : finite_set S) (a : S) (H : a [in] ([ms] (l [^] Y))) :  a [in] ([ms] (l [^] ([ms] Y))).
Proof.  assert (D : fun_congruence S S rS rS (ltr l)). admit. 
        apply in_minset_elim in H; auto. destruct H as [H1 H2].
        apply in_set_ltr_lift_elim in H1; auto.
        destruct H1 as [y [H3 H4]]. 
        apply in_minset_intro; auto. split.
           apply symS in H4. 
           rewrite (in_set_right_congruence S rS symS tranS _ _ _ H4);auto.
           case_eq(in_set rS ([ms] Y) y); intro H6.
              apply in_set_ltr_lift_intro; auto. 
              assert (B := H6). 
              apply in_set_minset_false_elim in B; auto.
              destruct B as [s [H7 H8]]. apply below_elim in H8. destruct H8 as [H8 H9]. 
              assert (R := LM l _ _ H8).
              case_eq (lteS (ltr l y) (ltr l s)) ; intro H10.
                 destruct DDD as [AntiSym | SI].
                    (* AntiSym *) 
                    assert (G := AntiSym _ _ R H10).
                    rewrite (in_set_right_congruence S rS symS tranS _  _ _ G); auto. 
                    apply in_set_ltr_lift_intro; auto.
                    (* SI if doesn't worl, try < or ~ ... *) 
                    assert (H11 := SI l y). destruct H11 as [H11 H12]. 
                    assert (H14 := SI l s). destruct H14 as [H14 H15]. 
                    
admit. 
                    
                 assert (H11 : ltr l s [in] (l [^] Y)).
                    apply in_set_ltr_lift_intro; auto.
                    apply in_minset_elim in H7; auto.                     
                    destruct H7 as [H7 _]; auto.
                 assert (Q := H2 (ltr l s) H11). 
                 apply below_false_elim in Q. 
                 destruct Q as [H12 | H12]. 
                    apply symS in H4. rewrite (lteCong _ _ _ _ (refS (ltr l s)) H4) in H12.
                    rewrite H12 in R. discriminate R.
                    rewrite (lteCong _ _ _ _ (symS _ _ H4) (refS (ltr l s))) in H12.
                    rewrite H12 in H10. discriminate H10.

           intros s H6.  apply H2. 
           apply in_set_ltr_lift_elim in H6; auto.
           destruct H6 as [y' [H7 H8]].
           apply symS in H8. 
           rewrite (in_set_right_congruence S rS symS tranS _ _ (l [^] Y) H8);auto. 
           apply in_set_ltr_lift_intro; auto.
           apply in_minset_elim in H7; auto. destruct H7 as [H7 _]; auto. 
Admitted. 



Lemma ltr_minset_lift_left_inclusion_1_VIII
   (LM : olt_monotone L S lteS ltr)
   (DDD : (brel_antisymmetric S rS lteS) +  (olt_strictly_increasing L S lteS ltr))
   (l : L) (X Y : finite_set S) (a : S) (H : a [in] ([ms] (l [^] Y))) :  a [in] ([ms] (l [^] ([ms] Y))).
Proof.  assert (D : fun_congruence S S rS rS (ltr l)). admit. 
        apply in_minset_elim in H; auto. destruct H as [H1 H2].
        apply in_set_ltr_lift_elim in H1; auto.
        destruct H1 as [y [H3 H4]]. 
        apply in_minset_intro; auto. split.
           apply symS in H4. 
           rewrite (in_set_right_congruence S rS symS tranS _ _ _ H4);auto.
           case_eq(in_set rS ([ms] Y) y); intro H6.
              apply in_set_ltr_lift_intro; auto. 
              assert (B := H6). 
              apply in_set_minset_false_elim in B; auto.
              destruct B as [s [H7 H8]]. apply below_elim in H8. destruct H8 as [H8 H9]. 
              assert (R := LM l _ _ H8).
              case_eq (lteS (ltr l y) (ltr l s)) ; intro H10.
                 destruct DDD as [AntiSym | SI].
                    (* AntiSym *) 
                    assert (G := AntiSym _ _ R H10).
                    rewrite (in_set_right_congruence S rS symS tranS _  _ _ G); auto. 
                    apply in_set_ltr_lift_intro; auto.
                    (* SI if doesn't worl, try < or ~ ... *) 
                    assert (H11 := SI l y). destruct H11 as [H11 H12]. 
                    assert (H14 := SI l s). destruct H14 as [H14 H15]. 
                    
admit. 
                    
                 assert (H11 : ltr l s [in] (l [^] Y)).
                    apply in_set_ltr_lift_intro; auto.
                    apply in_minset_elim in H7; auto.                     
                    destruct H7 as [H7 _]; auto.
                 assert (Q := H2 (ltr l s) H11). 
                 apply below_false_elim in Q. 
                 destruct Q as [H12 | H12]. 
                    apply symS in H4. rewrite (lteCong _ _ _ _ (refS (ltr l s)) H4) in H12.
                    rewrite H12 in R. discriminate R.
                    rewrite (lteCong _ _ _ _ (symS _ _ H4) (refS (ltr l s))) in H12.
                    rewrite H12 in H10. discriminate H10.

           intros s H6.  apply H2. 
           apply in_set_ltr_lift_elim in H6; auto.
           destruct H6 as [y' [H7 H8]].
           apply symS in H8. 
           rewrite (in_set_right_congruence S rS symS tranS _ _ (l [^] Y) H8);auto. 
           apply in_set_ltr_lift_intro; auto.
           apply in_minset_elim in H7; auto. destruct H7 as [H7 _]; auto. 
Admitted. 







(* nb : this did not use strictness or antisym *) 
Lemma ltr_minset_lift_left_inclusion_2    (LM : olt_monotone L S lteS ltr)
      (l : L) (Y : finite_set S) (a : S) (H : a [in] ([ms] (l [^] ([ms] Y)))) : 
          a [in] ([ms] (l [^] Y)).
Proof.  assert (D' : fun_congruence S S rS rS (ltr l)). admit.
        apply in_minset_elim in H; auto. destruct H as [H1 H2].
        apply in_set_ltr_lift_elim in H1; auto.
        destruct H1 as [y [H3 H4]]. 
        apply in_minset_intro; auto. split.
           apply in_minset_elim in H3; auto.
           destruct H3 as [H3 _].
           apply symS in H4. rewrite (in_set_right_congruence S rS symS tranS _ _ _ H4);auto. 
           apply in_set_ltr_lift_intro; auto. 

           intros s H6.
           apply in_set_ltr_lift_elim in H6; auto. 
           destruct H6 as [ c [H7 H8]].
           case_eq(in_set rS ([ms] Y) c); intro H10. 
              apply H2.               
              apply symS in H8. rewrite (in_set_right_congruence S rS symS tranS _ _ _ H8);auto.
              apply in_set_ltr_lift_intro; auto.
              apply in_set_minset_false_elim in H10; auto.
              destruct H10 as [c' [H11 H12]]. apply below_elim in H12. destruct H12 as [H12 H13].
              assert (H14 := LM l _ _ H12).
              assert (A : (ltr l c') [in] (l [^] ([ms] Y))).
                 apply in_set_ltr_lift_intro; auto. 
              assert (B := H2 (ltr l c') A).
              rewrite (below_congruence _ _ _ lteCong _ _ _ _ H4 (refS (ltr l c'))) in B.                 
              apply below_false_elim in B.
              destruct B as [B | B].
                 rewrite (below_congruence _ _ _ lteCong _ _ _ _ H4 H8). 
                 case_eq(below lteS (ltr l y) (ltr l c) ); intro D; auto. 
                    assert (E := below_pseudo_transitive_left _ _ _ H14 D).
                    apply below_elim in E. destruct E as [E F].
                     rewrite E in B. discriminate B. 
                 
                 assert (C := lteTrans _ _ _ B H14). 
                 rewrite (below_congruence _ _ _ lteCong _ _ _ _ H4 H8). 
                 case_eq(below lteS (ltr l y) (ltr l c) ); intro D; auto. 
                    assert (E := below_pseudo_transitive_right _ _ _ D C). 
                    assert (G := below_not_reflexive _ _ lteRefl (ltr l c)). 
                    rewrite G in E. discriminate E. 
Admitted. 


Lemma ltr_minset_lift_right_invariant_v0
   (LM : olt_monotone L S lteS ltr)
   (DDD : (brel_antisymmetric S rS lteS) +  (olt_strictly_monotone L S lteS ltr))
      (l : L) (X Y : finite_set S) :  [ms] (l [^] ([ms] Y)) [=S] [ms] (l [^] Y). 
Proof. apply brel_set_intro_prop; auto. split.
       apply ltr_minset_lift_left_inclusion_2; auto.        
       apply ltr_minset_lift_left_inclusion_1; auto.        
Qed. 



(*

*) 
Lemma ltr_minset_union_lift_monotone_weak
   (LM : olt_monotone L S lteS ltr)
   (DDD : (brel_antisymmetric S rS lteS) +  (olt_strictly_monotone L S lteS ltr)) :   
     slt_distributive L (finite_set S) (brel_set rS) (bop_minset_union S rS lteS) (ltr_minset_lift rS lteS ltr). 
Proof. unfold brel_antisymmetric, olt_strictly_monotone in DDD. 
       intros l Y Z.
       assert (A : (l <^> (Y <U> Z)) [=S] ([ms] (l [^] ([ms] ([ms] (([ms] Y) [U] ([ms] Z))))))).
          unfold ltr_minset_lift. unfold bop_minset_union. apply set_reflexive. 
       assert (B : ([ms] (l [^] ([ms] ([ms] (([ms] Y) [U] ([ms] Z)))))) [=S] ([ms] (l [^] ([ms] (([ms] Y) [U] ([ms] Z)))))).
          apply ltr_minset_lift_right_invariant_v0; auto.   (* uses DDD and LM ! *) 
       assert (C := set_transitive _ _ _ A B).          
       assert (D : ([ms] (l [^] ([ms] (([ms] Y) [U] ([ms] Z))))) [=S] ([ms] (l [^] (([ms] Y) [U] ([ms] Z))))). 
          apply ltr_minset_lift_right_invariant_v0; auto.
       assert (E := set_transitive _ _ _ C D).       
       assert (F := ltr_union_lift_distributive l ([ms] Y) ([ms] Z)).
       assert (G := uop_minset_congruence_weak _ _ F). 
       assert (H := set_transitive _ _ _ E G).       
       assert (I : ([ms] ((l [^] ([ms] Y)) [U] (l [^] ([ms] Z)))) [=S] ([ms] ((l [^] ([ms] Y)) [U] ([ms] (l [^] ([ms] Z)))))). 
          apply set_symmetric. apply minset_union_right_uop_invariant_weak. 
       assert (J := set_transitive _ _ _ H I).       
       assert (K : [ms] ((l [^] ([ms] Y)) [U] ([ms] (l [^] ([ms] Z))))
                     [=S] 
                   [ms] (([ms] (l [^] ([ms] Y)))    [U] ([ms] ([ms] (l [^] ([ms] Z)))))). 
          apply set_symmetric. apply minset_union_uop_invariant_weak. 
       assert (L' := set_transitive _ _ _ J K).
       assert (M :  [ms] (([ms] (l [^] ([ms] Y))) [U] ([ms] ([ms] (l [^] ([ms] Z)))))
                       [=S] 
                    [ms] (([ms] ([ms] (l [^] ([ms] Y)))) [U] ([ms] ([ms] (l [^] ([ms] Z)))))).
       apply set_symmetric. apply minset_union_left_uop_invariant_weak. 
       assert (N := set_transitive _ _ _ L' M).               
       assert (O : [ms] (([ms] ([ms] (l [^] ([ms] Y)))) [U] ([ms] ([ms] (l [^] ([ms] Z)))))
                      [=S]
                   ((l <^> Y) <U> (l <^> Z))).
          unfold ltr_minset_lift. unfold bop_minset_union. apply set_reflexive. 
       exact (set_transitive _ _ _ N O).
Qed. 

Lemma ltr_minset_union_lift_distributive
   (LM : olt_monotone L S lteS ltr)
   (DDD : (brel_antisymmetric S rS lteS) +  (olt_strictly_monotone L S lteS ltr)) :
        slt_distributive L (finite_set S) (brel_minset rS lteS) (bop_minset_union S rS lteS) (ltr_minset_lift rS lteS ltr).   
Proof. intros l Y Z. apply set_equal_implies_minset_equal. apply ltr_minset_union_lift_monotone_weak; auto. Qed. 


Lemma test (a b : S)
   (LM : olt_monotone L S lteS ltr)
   (NAS : brel_not_antisymmetric S rS lteS)
   (NSM : olt_not_strictly_monotone L S lteS ltr) :   
     slt_not_distributive L (finite_set S) (brel_set rS) (bop_minset_union S rS lteS) (ltr_minset_lift rS lteS ltr). 
Proof. unfold brel_not_antisymmetric in NAS.
       unfold olt_not_strictly_monotone in NSM.
       unfold slt_not_distributive. 
       destruct NAS as [[s1 s2] [[A B] C]].
       destruct NSM as [[l [s3 s4]] [[D E] F]].
       exists (l, (a :: nil, b :: nil)).
(*

  
  given monotone, s1 ~ s2, s3 < s4 and 
        (l|>s3 !<= l|>s4) or (l|>s4 <= l|>s3) 
        ----------------
        contradicts monotone 

  find a, b such that 

  LHS = (l <^> ({a} <U> {b})) 
  RHS = ((l <^> {a}) <U> (l <^> {b}))
  and LHS <> RHS 

  LHS = (l <^> ((a :: nil) <U> (b :: nil))) 
      = ms (l |> ms ({a, b}))

  RHS = ((l <^> {a}) <U> (l <^> {b}))
      = ms {l|>a, l|>b}

try a = s3, b = s4

  LHS = {l |> s3}

  RHS:   from s3 < s4 and mono know (l|>s3 <= l|>s4). 
         for "or" know (l|>s4 <= l|>s3) 
       if l|> s3 =l|>s4 
       then RHS = LHS 
       ow, l|> s3 ~ l|>s4 
       and RHS = {l |> s3, l|>s4} 

Q: what would this mean for minset_union_lift (bs x sp x path)?

LHS = local optima 
RHS = global optima 

LHS subset RHS. 

so, not getting all paths! again the bottleneck links! 


NOTE: we really want NSA and NSM to be combined! 


Note: we have in the possitive case 

DDD : (∀ s t : S, s <<= t → t <<= s → s [=] t) + 
      (∀ (l : L) (t u : S), t <<= u → u !<<= t → (l [*] t) <<= (l [*] u) * (l [*] u) !<<= (l [*] t))

And in the negative case: 
A : s1 <<= s2
  B : s2 <<= s1
  C : s1 [<>] s2
  l : L
  s3, s4 : S
  D : s3 <<= s4
  E : s4 !<<= s3
  F : (l [*] s3) !<<= (l [*] s4) + (l [*] s4) <<= (l [*] s3)
  

All that is needed in the negated case is 
     
   l |> s3 [<>]  l|>s4

*) 
Admitted.        
       
Lemma ltr_minset_union_lift_absorptive_with_antisymmetry_weak
      (anti: brel_antisymmetric S rS lteS)      
      (inc : olt_increasing L S lteS ltr)       
      (l : L ) (Y : finite_set S): ([ms] Y) [=S] ([ms] (Y [U] (l [^] Y))).
Proof.  apply brel_set_intro_prop; auto. split. 
           intros s A. 
           apply in_minset_elim in A; auto. destruct A as [A B].
           apply in_minset_intro; auto. split. 
              apply in_set_bop_union_intro; auto. 
              intros t C. apply in_set_bop_union_elim in C; auto. 
              destruct C as [C | C]. 
                apply B; auto. 
                apply in_set_ltr_lift_elim in C; auto. 
                destruct C as [y [D E]].
                assert (F := B y D). 
                case_eq(below lteS s t); intro G; auto. 
                  assert (H := inc l y). 
                  rewrite (lteCong _ _ _ _ (refS y) (symS _ _ E)) in H. 
                  apply below_false_elim in F. apply below_elim in G. destruct G as [G I].
                  assert (J := lteTrans _ _ _ H G).
                  destruct F as [F | F].
                     rewrite J in F. discriminate F. 
                     assert (K := lteTrans _ _ _ F H).
                     rewrite K in I. discriminate I. 
                  
           intros s A. 
           apply in_minset_elim in A; auto. destruct A as [A B]. 
           apply in_set_bop_union_elim in A; auto. 
           apply in_minset_intro; auto. split. 
              destruct A as [A | A]; auto. 
                apply in_set_ltr_lift_elim in A; auto.               
                destruct A as [y [C D]]. 
                assert (E := inc l y). 
                assert (F : y [in] (Y [U] (l [^] Y))).
                    apply in_set_bop_union_intro; auto. 
                assert (G := B y F). 
                apply below_false_elim in G.
                destruct G as [G | G].
                   rewrite (lteCong _ _ _ _ (refS y) D) in G. 
                   rewrite E in G. discriminate G.
                   (* use antisymmetry *)
                   rewrite (lteCong _ _ _ _ (refS y) (symS _ _ D)) in E.                    
                   assert (H := anti _ _ E G). 
                   apply (in_set_right_congruence _ _ symS tranS _ _ _ H); auto. 
                   
              intros t C. 
              apply B. apply in_set_bop_union_intro; auto. 
Qed.

Lemma ltr_minset_union_lift_absorptive_with_antisymmetry
      (anti: brel_antisymmetric S rS lteS)      
      (inc : olt_increasing L S lteS ltr):
         slt_absorptive L (finite_set S) (brel_minset rS lteS) (bop_minset_union S rS lteS) (ltr_minset_lift rS lteS ltr).         
Proof. intros l Y. unfold brel_minset. 
       assert (A : ([ms] Y)
                     [=S]
                   ([ms] (Y [U] (l [^] Y)))). 
          apply ltr_minset_union_lift_absorptive_with_antisymmetry_weak; auto.
       assert (B : ([ms] (Y [U] (l [^] Y)))
                     [=S] (
                   [ms] (([ms] Y) [U] ([ms] (l [^] Y))))). admit. 
       assert (C := set_transitive _ _ _ A B). 
       assert (D : ([ms] (([ms] Y) [U] ([ms] (l [^] Y))))
                     [=S]
                   [ms] ([ms] (([ms] Y) [U] ([ms] (l [^] Y))))). admit. 
       assert (E := set_transitive _ _ _ C D). 
       assert (F : ([ms] ([ms] (([ms] Y) [U] ([ms] (l [^] Y)))))
                     [=S]
                   ([ms] (Y <U> (l <^> Y)))).
       unfold bop_minset_union. unfold ltr_minset_lift. apply set_reflexive.



       ([ms] ([ms] (([ms] Y) [U] ([ms] ([ms] (l [^] ([ms] Y)))))))
       
Qed. 

Lemma ltr_minset_union_lift_absorptive_without_antisymmetry_weak
      (inc : olt_strictly_increasing L S lteS ltr)       
      (l : L ) (Y : finite_set S): ([ms] Y) [=S] ([ms] (Y [U] (l [^] Y))).
Proof.  apply brel_set_intro_prop; auto. split. 
           intros s A. 
           apply in_minset_elim in A; auto. destruct A as [A B].
           apply in_minset_intro; auto. split. 
              apply in_set_bop_union_intro; auto. 
              intros t C. apply in_set_bop_union_elim in C; auto. 
              destruct C as [C | C]. 
                apply B; auto. 
                apply in_set_ltr_lift_elim in C; auto. 
                destruct C as [y [D E]].
                assert (F := B y D). 
                case_eq(below lteS s t); intro G; auto. 
                  assert (H := inc l y). destruct H as [H H']. 
                  rewrite (lteCong _ _ _ _ (refS y) (symS _ _ E)) in H. 
                  apply below_false_elim in F. apply below_elim in G. destruct G as [G I].
                  assert (J := lteTrans _ _ _ H G).
                  destruct F as [F | F].
                     rewrite J in F. discriminate F. 
                     assert (K := lteTrans _ _ _ F H).
                     rewrite K in I. discriminate I. 
                  
           intros s A. 
           apply in_minset_elim in A; auto. destruct A as [A B]. 
           apply in_set_bop_union_elim in A; auto. 
           apply in_minset_intro; auto. split. 
              destruct A as [A | A]; auto. 
                apply in_set_ltr_lift_elim in A; auto.               
                destruct A as [y [C D]]. 
                assert (E := inc l y). destruct E as [E E']. 
                assert (F : y [in] (Y [U] (l [^] Y))).
                    apply in_set_bop_union_intro; auto. 
                assert (G := B y F). 
                apply below_false_elim in G.
                destruct G as [G | G].
                   rewrite (lteCong _ _ _ _ (refS y) D) in G. 
                   rewrite E in G. discriminate G.  
                   (* use strictly increasing *)
                   rewrite (lteCong _ _ _ _  (symS _ _ D) (refS y)) in E'.                    
                   rewrite G in E'. discriminate E'.                    

              intros t C. 
              apply B. apply in_set_bop_union_intro; auto. 
Qed. 
       
End Theory.

Section ACAS.


End ACAS.

Section CAS.

End CAS.

Section Verify.
 
End Verify.   


