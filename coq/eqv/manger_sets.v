Require Import Coq.Lists.List
  Psatz.
Require Import CAS.coq.common.compute.

Require Import CAS.coq.theory.set. (* for in_set lemmas *) 

Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.set.
Require Import CAS.coq.eqv.minset.
Require Import CAS.coq.eqv.product.

Require Import CAS.coq.or.properties.
Require Import CAS.coq.or.trivial. 

Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.or.
Require Import CAS.coq.sg.and. 
Require Import CAS.coq.sg.union.
Require Import CAS.coq.sg.lift.
Require Import CAS.coq.sg.product.

Require Import CAS.coq.uop.properties.

Import ListNotations.

Section Computation.

(*
• Phase 1. All pairs from X with equal active components are merged
into a single pair whose active component is the one found in the
original pairs and passive component is the join of passive components
from the original pairs. For instance, if X contains altogether three
pairs with a given x ∈ P , i.e., (x, x1 ), (x, x2 ) and (x, x3 ), then they are
replaced with a single pair (x, x1 ∨ x2 ∨ x3 ). Note that after phase 1
all pairs in X have distinct active components.

• Phase 2. All pairs from X that are dominated in X with respect
to their active components are deleted from X. For instance, if X
contains two pairs (x, x') and (y, y') such that x ≺ y, then the pair
(x, x') is deleted. In other words, phase 2 leaves in X only those pairs
that are efficient according to their active component.

TGG22: Note that Manger's order is the dual of our left order. 
*)   

(* 
  A = type of active component
  P = type of passive component
*)   
Fixpoint manger_merge_sets
           {A P : Type}
           (eqA : brel A)
           (addP : binary_op P)
           (Y : finite_set (A * P))
           (p1 : A * P) :=
  match Y with
  | nil => p1 :: nil
  | p2 :: Y' =>
    match p1, p2 with
    | (s1, t1), (s2, t2) =>
      if eqA s1 s2
      then manger_merge_sets eqA addP Y' (s1, addP t1 t2) 
      else p2 :: (manger_merge_sets eqA addP Y' p1) 
    end 
  end.



(* This makes the current proof that I am trying is bit easier.
The manger_merge_sets and manger_merge_sets_new can 
be proven equivalent, with some effort.
*)


Definition manger_merge_sets_new_aux
  {A P : Type}
  (eqA : brel A)
  (addP : binary_op P)
  (Y : finite_set (A * P))
  (p1 : A * P) : list (A * P) * list (A * P) :=
    ((filter (λ '(s2, t2), eqA (fst p1) s2) Y),
    (filter (λ '(s2, t2), negb (eqA (fst p1) s2)) Y)).


Definition manger_merge_sets_new
  {A P : Type}
  (eqA : brel A)
  (addP : binary_op P)
  (Y : finite_set (A * P))
  (p1 : A * P) : list (A * P) :=
    match manger_merge_sets_new_aux eqA addP Y p1 with 
    | (Y1, Y2) => 
        Y2 ++ 
        [(fold_left 
          (λ '(s1, t1) '(s2, t2), (s1, addP t1 t2)) 
          Y1 p1)] 
    end.


Definition manger_phase_1_auxiliary 
          {A P : Type}
          (eqA : brel A)
          (addP : binary_op P) 
          (Y : finite_set (A * P))
          (X : finite_set (A * P))  : finite_set (A * P) :=
  fold_left (manger_merge_sets eqA addP) X Y.

Definition uop_manger_phase_1 
          {A P : Type}
          (eqA : brel A)
          (addP : binary_op P) 
          (X : finite_set (A * P))  : finite_set (A * P) :=
  manger_phase_1_auxiliary  eqA addP nil X.   

Definition equal_manger_phase_1 
          {A P : Type}
          (eqA : brel A)
          (eqP : brel P)          
          (addP : binary_op P) : brel (finite_set (A * P)) :=
  λ X Z, brel_set (brel_product eqA eqP)
                  (uop_manger_phase_1 eqA addP X)
                  (uop_manger_phase_1 eqA addP Z). 

Definition manger_pre_order
           {A P : Type}
           (lteA : brel A) : brel (A * P)
  := brel_product lteA (@brel_trivial P). 

Definition uop_manger_phase_2
           {A P : Type} (lteA : brel A) : unary_op (finite_set (A * P))          
  := uop_minset (manger_pre_order lteA). 

Definition equal_manger_phase_2
          {A P : Type}
          (eqA lteA : brel A)
          (eqP : brel P) : brel (finite_set (A * P)) :=         
  λ X Z, brel_set (brel_product eqA eqP)
                  (uop_manger_phase_2 lteA X)
                  (uop_manger_phase_2 lteA Z). 

Definition equal_manger
          {A P : Type}
          (eqA lteA : brel A)
          (eqP : brel P)          
          (addP : binary_op P) : brel (finite_set (A * P)) :=
  λ X Z, equal_manger_phase_1 eqA eqP addP 
                  (@uop_manger_phase_2 A P lteA X)
                  (@uop_manger_phase_2 A P lteA Z).

Definition equal_manger_v2
          {A P : Type}
          (eqA lteA : brel A)
          (eqP : brel P)          
          (addP : binary_op P) : brel (finite_set (A * P)) :=
  λ X Z, @equal_manger_phase_2 A P eqA lteA eqP 
                  (uop_manger_phase_1 eqA addP X)
                  (uop_manger_phase_1 eqA addP Z).

(* conjecture these two equalities are the same *) 


End Computation. 

Section Theory.

Variables (A P : Type) 
          (eqA lteA : brel A)
          (eqP : brel P)          
          (addP : binary_op P)
          (refA : brel_reflexive A eqA)
          (symA : brel_symmetric A eqA)
          (trnA : brel_transitive A eqA)
          (refP : brel_reflexive P eqP)
          (symP : brel_symmetric P eqP)
          (trnP : brel_transitive P eqP)
          (cong_addP : bop_congruence P eqP addP) 
          (cong_lteA : brel_congruence A eqA lteA)
          (cong_eqP : brel_congruence P eqP eqP)
          (cong_eqA : brel_congruence A eqA eqA)
          (ref_lteA : brel_reflexive A lteA)
          (* is idemP really needed, or is it 
             a consequence of using lists to represent sets?
          *) 
          (idemP : bop_idempotent P eqP addP)
          (* Extra assumptions needed to prove the lemmas fold_left congruence *)
          (addP_assoc : bop_associative P eqP addP)
          (addP_com : bop_commutative P eqP addP)
          (addP_cong : ∀ x y : P, eqP x y = true → eqP (addP x y) y = true)
          (addP_assoc_cong : ∀ x y z : P, addP x (addP y z) = addP (addP x y) z)
          (addP_com_cong : ∀ x y : P, addP x y = addP y x).


Local Notation "a [in] X" := (in_set (brel_product eqA eqP) X a = true) (at level 70).
Local Notation "a == b"   := (brel_product eqA eqP a b = true) (at level 70).
Local Notation "a <A> b"  := (eqA a b = false) (at level 70). 

Local Notation "[MMS]"  := (manger_merge_sets eqA addP).
Local Notation "[P1AX]" := (manger_phase_1_auxiliary eqA addP).
Local Notation "[P1]"   := (uop_manger_phase_1 eqA addP).
Local Notation "[P2]"   := (uop_manger_phase_2 lteA).

Local Notation "[EQ]"    := (brel_set (brel_product eqA eqP)).
Local Notation "a =S= b" := (brel_set (brel_product eqA eqP) a b = true) (at level 70). 
Local Notation "[EQ1]"   := (equal_manger_phase_1 eqA eqP addP). 
Local Notation "[EQM]"   := (equal_manger eqA lteA eqP addP).


(* equality on A * P *) 
Lemma refAP : brel_reflexive (A * P) (brel_product eqA eqP).
Proof. apply brel_product_reflexive; auto. Qed. 

Lemma symAP : brel_symmetric (A * P) (brel_product eqA eqP).
Proof. apply brel_product_symmetric; auto. Qed. 

Lemma trnAP : brel_transitive (A * P) (brel_product eqA eqP).
Proof. apply brel_product_transitive; auto. Qed. 

(* equality on set over A * P *)

Lemma refSetAP : brel_reflexive _ [EQ]. 
Proof. apply brel_set_reflexive.
       - apply refAP.
       - apply symAP. 
Qed. 

Lemma symSetAP : brel_symmetric _ [EQ]. 
Proof. apply brel_set_symmetric. Qed. 

Lemma trnSetAP : brel_transitive _ [EQ]. 
Proof. apply brel_set_transitive.
       - apply refAP.
       - apply symAP.
       - apply trnAP. 
Qed. 

Lemma set_equal_with_cons_left :
  ∀ X p1 p2, p1 == p2 -> (p1 :: X) =S= (p2 :: X) . 
Proof. intros X p1 p2 H1.
       apply brel_set_intro_prop.
       - apply refAP.
       - split; intros a H2. 
         + apply in_set_cons_intro; auto.
           * apply symAP.
           * apply in_set_cons_elim in H2.
             -- destruct H2 as [H2 | H2].
                ++ left. apply symAP in H1.
                   exact (trnAP _ _ _ H1 H2). 
                ++ right. exact H2. 
             -- apply symAP. 
         + apply in_set_cons_intro; auto.
           * apply symAP.
           * apply in_set_cons_elim in H2.
             -- destruct H2 as [H2 | H2].
                ++ left. 
                   exact (trnAP _ _ _ H1 H2). 
                ++ right. exact H2. 
             -- apply symAP. 
Qed.

Lemma set_equal_with_cons_right :
  ∀ X Y p, X =S= Y -> (p :: X) =S= (p :: Y) . 
Proof. intros X Y p H1.
       apply brel_set_intro_prop.
       - apply refAP.
       - split; intros a H2. 
         + apply in_set_cons_intro; auto.
           * apply symAP.
           * apply in_set_cons_elim in H2.
             -- destruct H2 as [H2 | H2].
                ++ left. exact H2.
                ++ right.
                   rewrite (in_set_left_congruence _ _ symAP trnAP a _ _ H1) in H2.
                   exact H2. 
            -- apply symAP. 
         + apply in_set_cons_intro; auto.
           * apply symAP.
           * apply in_set_cons_elim in H2.
             -- destruct H2 as [H2 | H2].
                ++ left. exact H2.
                ++ right.
                   rewrite (in_set_left_congruence _ _ symAP trnAP a _ _ H1).
                   exact H2. 
             -- apply symAP. 
Qed.

Lemma remove_duplicate_from_set :
  ∀ Y p1 p2, p1 == p2 -> (p1 :: p2 :: Y) =S= (p1 :: Y).
Proof. intros Y p1 p2 H1.
       apply brel_set_intro_prop.
       - apply refAP. 
       - split; intros a H2. 
         + apply in_set_cons_intro.
           * apply symAP. 
           * apply in_set_cons_elim in H2.
             -- destruct H2 as [H2 | H2].
                ++ left; auto. 
                ++ apply in_set_cons_elim in H2.
                   ** destruct H2 as [H2 | H2].
                      --- left. exact (trnAP _ _ _ H1 H2). 
                      --- right; auto. 
                   ** apply symAP. 
             -- apply symAP. 
         + apply in_set_cons_intro.
           * apply symAP. 
           * apply in_set_cons_elim in H2.
             -- destruct H2 as [H2 | H2].
                ++ left; auto. 
                ++ right.
                   apply in_set_cons_intro; auto.
                   apply symAP. 
             -- apply symAP.
Qed. 
                
Lemma set_rearrange_v1 :
  ∀ Y p1 p2, (p1 :: p2 :: Y) =S= (p2:: p1 :: Y).
Proof. intros Y p1 p2.
       apply brel_set_intro_prop.
       - apply refAP. 
       - split; intros p3 H1.
         + (*
  H1 : p3 [in] p1 :: p2 :: Y
  ============================
  p3 [in] p2 :: p1 :: Y
            *)
           apply in_set_cons_intro.
           * apply symAP.
           * apply in_set_cons_elim in H1.
             -- destruct H1 as [H1 | H1].
                ++ right.
                   apply in_set_cons_intro.
                   ** apply symAP.
                   ** left. auto. 
                ++ apply in_set_cons_elim in H1.
                   --- destruct H1 as [H1 | H1].
                       +++ left. auto.
                       +++ right. 
                           apply in_set_cons_intro.
                           *** apply symAP.
                           *** right. auto.
                   --- apply symAP.
             -- apply symAP.
         + (* same code! 

  H1 : p3 [in] p2 :: p1 :: Y
  ============================
  p3 [in] p1 :: p2 :: Y
           *)
           apply in_set_cons_intro.
           * apply symAP.
           * apply in_set_cons_elim in H1.
             -- destruct H1 as [H1 | H1].
                ++ right.
                   apply in_set_cons_intro.
                   ** apply symAP.
                   ** left. auto. 
                ++ apply in_set_cons_elim in H1.
                   --- destruct H1 as [H1 | H1].
                       +++ left. auto.
                       +++ right. 
                           apply in_set_cons_intro.
                           *** apply symAP.
                           *** right. auto.
                   --- apply symAP.
             -- apply symAP.
Qed.

Lemma set_rearrange_v2 : 
   ∀ X Y p,  p :: X ++ Y =S= X ++ p :: Y.
Proof. induction X; intros Y p. 
       - rewrite app_nil_l. rewrite app_nil_l.
         apply refSetAP. 
       - rewrite <- app_comm_cons. rewrite <- app_comm_cons. 
         assert (H1 := set_rearrange_v1 (X ++ Y) p a).
         assert (H2 := IHX Y p). 
         assert (H3 := set_equal_with_cons_right (p :: X ++ Y) (X ++ p :: Y) a H2). 
         exact (trnSetAP _ _ _ H1 H3).
Qed. 
                   
(* properties of manger_pre_order *)  

Lemma manger_pre_order_congruence : brel_congruence (A * P) (brel_product eqA eqP) (manger_pre_order lteA). 
Proof. unfold manger_pre_order.
       apply brel_product_congruence; auto.
       apply brel_trivial_congruence. 
Qed.

Lemma manger_pre_order_reflexive : brel_reflexive (A * P) (manger_pre_order lteA).
Proof. unfold manger_pre_order.
       apply brel_product_reflexive; auto.
       apply brel_trivial_reflexive. 
Qed.

(* properties of equality [EQ1] *)

Lemma equal_manger_phase_1_congruence : brel_congruence _ [EQ1] [EQ1].
Proof. intros X Y Z W. unfold equal_manger_phase_1.
       apply brel_set_congruence.
       - apply refAP. 
       - apply symAP. 
       - apply trnAP. 
Qed.

Lemma equal_manger_phase_1_reflexive : brel_reflexive _ [EQ1].
Proof. intro X. unfold equal_manger_phase_1. 
       apply brel_set_reflexive; auto. 
       + apply refAP. 
       + apply symAP. 
Qed. 

Lemma equal_manger_phase_1_symmetric : brel_symmetric _ [EQ1].
Proof. unfold equal_manger_phase_1. intros X Y. 
       apply brel_set_symmetric; auto.
Qed. 

Lemma equal_manger_phase_1_transitive : brel_transitive _ [EQ1].
Proof. unfold equal_manger_phase_1. intros X Y Z. 
       apply brel_set_transitive; auto.
       - apply refAP. 
       - apply symAP. 
       - apply trnAP. 
Qed. 

(* properties of equality [EQM] *)

Lemma equal_manger_congruence : brel_congruence _ [EQM] [EQM].
Proof. intros X Y Z W. unfold equal_manger. 
       apply equal_manger_phase_1_congruence.
Qed.

Lemma equal_manger_reflexive : brel_reflexive _ [EQM].
Proof. unfold equal_manger; intro X; 
       apply equal_manger_phase_1_reflexive.
Qed.        

Lemma equal_manger_symmetric : brel_symmetric _ [EQM].
Proof. unfold equal_manger; intros X Y; 
       apply equal_manger_phase_1_symmetric.
Qed.        


Lemma equal_manger_transitive : brel_transitive _ [EQM].
Proof. unfold equal_manger; intros X Y Z; 
       apply equal_manger_phase_1_transitive.
Qed.        

(* Idempotence of reductions *)

Definition fst_unique_in_set X :=
  ∀ a a' p p',  (a, p) [in] X ->  (a', p') [in] X -> ((a, p) == (a', p')) + (a <A> a').

Lemma singleton_uniqueness : ∀ p, fst_unique_in_set (p :: nil). 
Proof. destruct p as [a p].
       intros a1 a2 p1 p2 H2 H3. left.
       apply in_set_singleton_elim in H2, H3; try (apply symAP).
       apply symAP in H3.
       exact(trnAP _ _ _ H3 H2). 
Qed.

Lemma fst_unique_in_set_congruence :
  ∀ X Y, X =S= Y -> fst_unique_in_set X -> fst_unique_in_set Y.
Proof. unfold fst_unique_in_set.
       intros X Y H1 H2 a a' p p' H3 H4.
       assert (H5 : (a, p) [in] X).
       {
         rewrite (in_set_left_congruence _ _ symAP trnAP (a,p) _ _ H1).
         exact H3. 
       } 
       assert (H6 : (a', p') [in] X).
       {
         rewrite (in_set_left_congruence _ _ symAP trnAP (a',p') _ _ H1).
         exact H4. 
       } 
       exact (H2 _ _ _ _ H5 H6). 
Qed. 


Lemma fst_unique_in_set_cons_intro : 
  ∀ X a p, (∀ a' p',  (a', p') [in] X -> ((a, p) == (a', p')) + (a <A> a')) 
           -> (fst_unique_in_set X)
           -> fst_unique_in_set ((a,p) :: X). 
Proof. intros X a p H1 H2. unfold fst_unique_in_set.
       intros a' a'' p' p'' H3 H4.
       apply in_set_cons_elim in H3.
       - apply in_set_cons_elim in H4.
         + destruct H3 as [H3 | H3];
           destruct H4 as [H4 | H4].
           * left. apply symAP in H3.
             exact (trnAP _ _ _ H3 H4).
           * destruct (H1 _ _ H4) as [H5 | H5].
             -- left. apply symAP in H3.
                exact (trnAP _ _ _ H3 H5).
             -- right.
                apply brel_product_elim in H3.
                destruct H3 as [H3 _].
                case_eq(eqA a' a''); intro H6; auto.
                rewrite (trnA _ _ _ H3 H6) in H5.
                discriminate H5. 
           * destruct (H1 _ _ H3) as [H5 | H5].
             -- left. apply symAP in H5.
                exact (trnAP _ _ _ H5 H4).
             -- right.
                apply brel_product_elim in H4.
                destruct H4 as [H4 _].
                case_eq(eqA a' a''); intro H6; auto.
                apply symA in H6. rewrite (trnA _ _ _ H4 H6) in H5.
                discriminate H5. 
           * destruct (H1 _ _ H3) as [H5 | H5];
             destruct (H1 _ _ H4) as [H6 | H6].
             -- left. apply symAP in H5.
                exact (trnAP _ _ _ H5 H6).
             -- right.
                apply brel_product_elim in H5.
                destruct H5 as [H5 _].
                case_eq(eqA a' a''); intro H7; auto.
                rewrite (trnA _ _ _ H5 H7) in H6.
                discriminate H6.
             -- right.
                apply brel_product_elim in H6.
                destruct H6 as [H6 _].
                case_eq(eqA a' a''); intro H7; auto.
                apply symA in H7. rewrite (trnA _ _ _ H6 H7) in H5.
                discriminate H5.
             -- case_eq(eqA a' a''); intro H7.
                ++ left.
                   destruct (H2 _ _ _ _ H3 H4) as [H8 | H8].
                   ** exact H8. 
                   ** rewrite H7 in H8. discriminate H8.
                ++ right. reflexivity. 
         + apply symAP. 
       - apply symAP. 
Qed.

Lemma fst_unique_in_set_cons_elim : 
  ∀ X a p, fst_unique_in_set ((a,p) :: X) ->
           (∀ a' p',  (a', p') [in] X -> ((a, p) == (a', p')) + (a <A> a')) 
           * 
           (fst_unique_in_set X).
Proof. intros X a p H1. split. 
       - intros a' p' H2.
         unfold fst_unique_in_set in H1.
         assert (H3 : (a, p) [in] (a, p) :: X).
         {
           apply in_set_cons_intro; auto.
           + apply symAP.
           + left. apply refAP. 
         } 
         assert (H4 : (a', p') [in] (a, p) :: X). 
         {
           apply in_set_cons_intro; auto.
           + apply symAP.
         } 
         exact (H1 _ _ _ _ H3 H4). 
       - unfold fst_unique_in_set in *.
         intros a' a'' p' p'' H2 H3.
         assert (H4 : (a', p') [in] (a, p) :: X).
         {
           apply in_set_cons_intro; auto.
           + apply symAP.
         } 
         assert (H5 : (a'', p'') [in] (a, p) :: X).
         {
           apply in_set_cons_intro; auto.
           + apply symAP.
         } 
         exact (H1 _ _ _ _ H4 H5).          
Qed.

Lemma fst_unique_in_set_concat_elim_right :
  ∀ X Y, fst_unique_in_set (X ++ Y) -> fst_unique_in_set Y.
Proof. induction X; intros Y H1.
       - rewrite app_nil_l in H1. exact H1.
       - rewrite <- app_comm_cons in H1.
         destruct a as [a p]. 
         apply fst_unique_in_set_cons_elim in H1.
         destruct H1 as [_ H1].
         apply IHX; auto. 
Qed.                           

Lemma manger_merge_sets_unchanged : 
  ∀ Y a b p p',
    Y <> nil -> 
    a <A> b ->  (b, p') [in] ([MMS] Y (a, p)) -> (b, p') [in] Y. 
Proof. induction Y; intros s t p p' H0 H1 H2.
       - congruence. 
       - simpl in H2.
         destruct a as [a1 p1].
         case_eq(eqA s a1); intro H3; rewrite H3 in H2.
         + apply in_set_cons_intro.
           * apply symAP.
           * right. destruct Y.
             -- simpl in H2.
                apply bop_or_elim in H2.
                destruct H2 as [H2 | H2].
                ++ apply bop_and_elim in H2.
                   destruct H2 as [H2 H4].
                   apply symA in H2. rewrite H2 in H1.
                   discriminate H1.
                ++ discriminate H2. 
             -- assert (H4 : p0 :: Y ≠ nil). congruence.
                exact(IHY _ _ _ _ H4 H1 H2). 
         + apply in_set_cons_intro. 
           * apply symAP. 
           * destruct Y.
             -- simpl in H2.
                apply bop_or_elim in H2.
                destruct H2 as [H2 | H2].
                ** left. apply bop_and_elim in H2.
                   destruct H2 as [H2 H4]. 
                   apply brel_product_intro; auto. 
                ** apply bop_or_elim in H2.
                   destruct H2 as [H2 | H2].
                   --- apply bop_and_elim in H2.
                       destruct H2 as [H2 H4].
                       apply symA in H2. rewrite H2 in H1.
                       discriminate H1.
                   --- discriminate H2. 
             -- apply in_set_cons_elim in H2.
                ++ destruct H2 as [H2 | H2].
                   ** left. exact H2.
                   ** right.
                      assert (H4 : p0 :: Y ≠ nil). congruence. 
                      exact (IHY _ _ _ _ H4 H1 H2).
                ++ apply symAP. 
Qed. 



Lemma manger_merge_sets_unchanged_v2 : 
  ∀ Y a b p p',
    Y <> nil -> 
    a <A> b -> (b, p') [in] Y -> (b, p') [in] ([MMS] Y (a, p)).
Proof. induction Y; intros a1 a2 p1 p2 H0 H1 H2.
       - congruence. 
       - destruct a as [a3 p3].
         simpl. 
         apply in_set_cons_elim in H2.
         + destruct H2 as [H2 | H2]; 
             case_eq(eqA a1 a3); intro H3.
           * apply brel_product_elim in H2.
             destruct H2 as [H2 H4].
             rewrite (trnA _ _ _ H3 H2) in H1.
             discriminate H1. 
           * apply in_set_cons_intro.
             -- apply symAP.
             -- left. exact H2. 
           * destruct Y. 
             -- compute in H2. discriminate H2.
             -- assert (H4 : p :: Y ≠ nil). congruence.  
                exact(IHY _ _ (addP p1 p3) _ H4 H1 H2).
           * destruct Y. 
             -- compute in H2. discriminate H2.
             -- assert (H4 : p :: Y ≠ nil). congruence.  
                assert (H5 := IHY _ _ p1 _ H4 H1 H2).
                apply in_set_cons_intro.
                ++ apply symAP.
                ++ right. auto. 
         + apply symAP. 
Qed. 

Lemma manger_merge_sets_preserves_uniqueness : 
∀ Y p, fst_unique_in_set Y -> fst_unique_in_set ([MMS] Y p). 
Proof. induction Y; intros p H1. 
       - simpl. apply singleton_uniqueness.
       - destruct a as [a1 p1]. destruct p as [a2 p2].
         apply fst_unique_in_set_cons_elim in H1.
         destruct H1 as [H1 H2]. simpl.
         case_eq(eqA a2 a1); intro H3.
         + apply IHY. exact H2. 
         + apply fst_unique_in_set_cons_intro.
           * intros a' p' H4.
             case_eq(eqA a1 a'); intro H5.
             -- left. apply brel_product_intro; auto.
                assert (H6' : (a', p') == (a1, p')).
                {
                  apply brel_product_intro; auto. 
                } 
                assert (H6 : (a1, p') [in] [MMS] Y (a2, p2)).
                {
                  exact (in_set_right_congruence _ _ symAP trnAP _ _ _ H6' H4).
                }
                destruct Y.
                ++ simpl in H6. apply bop_or_elim in H6.
                   destruct H6 as [H6 | H6]. 
                   ** apply bop_and_elim in H6.
                      destruct H6 as [H6 H7].
                      apply symA in H6. rewrite H6 in H3.
                      discriminate H3.
                   **  discriminate H6.
                ++ assert (H99 : p :: Y <> nil). congruence. 
                   assert (H6'' := manger_merge_sets_unchanged _ _ _ _ _ H99 H3 H6). 
                   destruct (H1 _ _ H6'') as [H7 | H7].
                   ** apply brel_product_elim in H7; auto.
                      destruct H7 as [_ H7]. exact H7. 
                   ** rewrite refA in H7. discriminate H7.
             -- right. reflexivity. 
           * apply IHY; auto.
Qed. 


Lemma uop_manger_phase_1_auxiliary_preserves_uniqueness : 
    ∀ X Y, fst_unique_in_set Y -> fst_unique_in_set ([P1AX] Y X). 
Proof. induction X; intros Y H1.
       - simpl. exact H1. 
       - simpl. apply IHX.
         apply manger_merge_sets_preserves_uniqueness; auto. 
Qed. 

Lemma manger_merge_set_congruence_right :
  ∀ Y p1 p2, p1 == p2 -> ([MMS] Y p1) =S= ([MMS] Y p2). 
Proof. induction Y; intros [a1 p1] [a2 p2] H1.
       - simpl.
         apply set_equal_with_cons_left; auto. 
       - apply brel_product_elim in H1. 
         destruct H1 as [H1 H2]. 
         destruct a as [a3 p3]. simpl.
         case_eq(eqA a1 a3); intro H3; case_eq(eqA a2 a3); intro H4.
         + assert (H5 : (a1, addP p1 p3) == (a2, addP p2 p3)).
           {
             apply brel_product_intro; auto.
           }
           exact (IHY _ _ H5). 
         + apply symA in H1.
           rewrite (trnA _ _ _ H1 H3) in H4.
           discriminate H4. 
         + rewrite (trnA _ _ _ H1 H4) in H3.
           discriminate H3. 
         + assert (H5 : (a1, p1) == (a2, p2)).
           {
             apply brel_product_intro; auto.
           }
           assert (H6 := IHY _ _ H5).
           exact (set_equal_with_cons_right _ _ (a3, p3) H6). 
Qed.




Lemma filter_negb : 
  forall (X : list (A * P))
  (f : A -> bool),
  List.filter (λ '(s2, _), negb (f s2)) X ++ 
  List.filter (λ '(s2, _), f s2) X =S= X.
Proof.
  induction X as [|(ax, bx) X Ihx];
  intros f; cbn.
  + reflexivity.
  + case_eq (f ax); intros Ha;
    simpl.
    ++
      remember (List.filter (λ '(s2, _), 
        negb (f s2)) X) as Xt.
      remember (List.filter (λ '(s2, _), 
        f s2) X) as Yt.
      apply symSetAP.
      eapply trnSetAP.
      instantiate (1 := (ax, bx) :: Xt ++ Yt).
      +++
        apply set_equal_with_cons_right,
        symSetAP; subst; apply Ihx.
      +++
        apply set_rearrange_v2.
    ++
      apply set_equal_with_cons_right,
      Ihx.
Qed.



Lemma filter_congruence_gen : 
  forall X Y f,
  (theory.bProp_congruence _ 
    (brel_product eqA eqP) f) ->
  X =S= Y ->
  filter f X =S=
  filter f Y.
Proof.
  intros ? ? ? Fcong Ha.
  apply brel_set_intro_prop.
  + apply refAP.
  + split.
    ++
      intros (a, p) Hb.
      eapply in_set_filter_elim in Hb.
      destruct Hb as [Hbl Hbr].
      eapply in_set_filter_intro;
      [apply symAP | apply Fcong | 
        split; [exact Hbl | ]].
      apply brel_set_elim_prop in Ha.
      destruct Ha as [Hal Har].
      apply Hal, Hbr.
      apply symAP.
      apply trnAP.
      apply Fcong.
    ++ 
      intros (a, p) Hb.
      eapply in_set_filter_elim in Hb.
      destruct Hb as [Hbl Hbr].
      eapply in_set_filter_intro;
      [apply symAP | apply Fcong | 
        split; [exact Hbl | ]].
      apply brel_set_elim_prop in Ha.
      destruct Ha as [Hal Har].
      apply Har, Hbr.
      apply symAP.
      apply trnAP.
      apply Fcong.
  Qed. 

Lemma negb_eqP_congruence : 
  forall a : P,
  theory.bProp_congruence P 
    eqP (λ x : P, negb (eqP a x)).
Proof.
  intros ? x y Hx.
  f_equal.
  case_eq (eqP a x);
  case_eq (eqP a y);
  intros Ha Hb;
  try reflexivity.
  rewrite (trnP _ _ _ Hb Hx) in Ha;
  congruence.
  apply symP in Hx.
  rewrite (trnP _ _ _ Ha Hx) in Hb;
  congruence.
Qed.


Lemma bop_neg_bProp_product_cong : 
  forall (ax : A) (bx : P),
  theory.bProp_congruence (A * P) (brel_product eqA eqP)
  (λ p : A * P, negb (brel_product eqA eqP p (ax, bx))).
Proof.
  intros ax bx (ap, aq) (bp, bq) Ha.
  apply f_equal.
  apply brel_product_elim in Ha.
  destruct Ha as [Hal Har].
  eapply brel_product_congruence with 
    (rS := eqA) (rT := eqP).
  eapply cong_eqA.
  eapply cong_eqP.
  apply brel_product_intro;
  [exact Hal | exact Har].
  apply brel_product_intro;
  [apply refA | apply refP].
Qed.


Lemma bop_theory_bProp_congruence_negb : 
  forall (pa : A), 
  theory.bProp_congruence _ 
    (brel_product eqA eqP)
    (λ '(s2, _), negb (eqA pa s2)).
Proof.
  intros ?.
  unfold theory.bProp_congruence.
  intros (aa, ap) (ba, bp) He.
  f_equal.
  apply brel_product_elim in He.
  destruct He as [Hel Her].
  case_eq (eqA pa aa); intro Hf.
  rewrite (trnA pa aa ba Hf Hel);
  reflexivity.
  case_eq (eqA pa ba); intro Hg.
  apply symA in Hel.
  rewrite (trnA pa ba aa Hg Hel) in Hf;
  congruence.
  reflexivity.
Qed.

Lemma bop_congruence_bProp_eqA : 
  forall (pa : A),
  theory.bProp_congruence _ 
        (brel_product eqA eqP)
        (λ '(s2, _), eqA pa s2).
Proof.
  intros pa.
  unfold theory.bProp_congruence.
  intros (aa, ap) (ba, bp) He.
  apply brel_product_elim in He.
  destruct He as [Hel Her].
  case_eq (eqA pa aa); intro Hf.
  rewrite (trnA pa aa ba Hf Hel);
  reflexivity.
  case_eq (eqA pa ba); intro Hg.
  apply symA in Hel.
  rewrite (trnA pa ba aa Hg Hel) in Hf;
  congruence.
  reflexivity.
Qed.

Lemma manger_merge_set_new_aux_congruence_left :
  ∀ X Y pa, 
  X =S= Y -> 
  (filter (λ '(s2, _), negb (eqA pa s2)) X =S= 
    filter (λ '(s2, _), negb (eqA pa s2)) Y) ∧
  (filter (λ '(s2, _), eqA pa s2) X =S= 
    filter (λ '(s2, _), eqA pa s2) Y).
Proof.
  intros ? ? ? Ha.
  pose proof (filter_negb X (fun x => negb (eqA pa x))) as Hb.
  pose proof (filter_negb Y (eqA pa)) as Hc.
  apply symSetAP in Hc.
  pose proof (trnSetAP _ _ _ Ha Hc) as Hd.
  split.
  + assert (He : theory.bProp_congruence _ 
      (brel_product eqA eqP)
      (λ '(s2, _), negb (eqA pa s2))).
    eapply bop_theory_bProp_congruence_negb.
    eapply filter_congruence_gen;
    [exact He | exact Ha].
  + assert (He : theory.bProp_congruence _ 
      (brel_product eqA eqP)
      (λ '(s2, _), eqA pa s2)).
    eapply bop_congruence_bProp_eqA.
    eapply filter_congruence_gen;
    [exact He | exact Ha].
Qed.
  

(* 
If a ∈ X then by idempotence 
  a + (fold_right f p X) = (fold_right f p X). 
*)
Lemma fold_right_idempotent_aux_one : 
  forall (X : list P) (a p : P)
  (f : P -> P -> P),
  (forall x y z : P, 
    eqP (f x (f y z)) (f (f x y) z) = true) ->
  (forall x y : P, eqP (f x y) (f y x) = true) ->
  (forall (x y w v : P),
    eqP x y = true ->
    eqP w v = true ->
    eqP (f x w) (f y v) = true) ->
  (forall x y : P, eqP x y = true ->
    eqP (f x y) y = true) ->
  in_set eqP X a = true ->
  eqP (f a (fold_right f p X)) (fold_right f p X) = true.
Proof.
  induction X as [|x X IHx].
  + 
    intros ? ? ? fassoc fcom fcong Ha Hb.
    simpl in Hb;
    congruence.
  +
    intros ? ? ? fassoc fcom fcong Ha Hb.
    simpl in * |- *.
    case_eq ((in_set eqP X a));
    case_eq (eqP a x); 
    intros Hc Hd.
    ++ (* a = x *)
      remember ((fold_right f p X)) as w.
      (* I need f to be associative *)
      eapply trnP.
      eapply fassoc.
      eapply fcong. 
      eapply Ha.
      exact Hc.
      apply refP.
    ++
      (* Induction case *)
      pose proof IHx a p f fassoc fcom fcong Ha Hd as He.
      remember ((fold_right f p X)) as w.
      eapply trnP with (f a (f w x)).
      eapply fcong.
      eapply refP.
      eapply fcom.
      eapply trnP with (f (f a w) x).
      eapply fassoc.
      eapply trnP with (f w x).
      eapply fcong.
      exact He.
      apply refP.
      eapply fcom.
    ++
      remember ((fold_right f p X)) as w.
      (* I need f to be associative *)
      eapply trnP.
      eapply fassoc.
      eapply fcong. 
      eapply Ha.
      exact Hc.
      eapply refP.
    ++
      rewrite Hc, Hd in Hb;
      simpl in Hb; congruence.
Qed.



Lemma in_set_false : 
  forall (Y : list P) (a : P),
  in_set eqP (filter (λ x : P, negb (eqP a x)) Y) a = false.
Proof.
  induction Y as [|b Y IHy];
  simpl.
  + intros ?; reflexivity.
  + intros ?.
    case_eq (eqP a b); simpl; intro Ha.
    ++
      now rewrite IHy.
    ++
      now rewrite Ha, IHy.
Qed.





Lemma in_set_true_false : 
  forall (Y : list P) (a b : P),
  eqP b a = false ->
  in_set eqP Y a = true ->
  in_set eqP (filter (λ x : P, negb (eqP a x)) Y) b = true ->
  in_set eqP Y b = true.
Proof.
  induction Y as [|u Y IHy]; simpl.
  + 
    intros ? ? Ha Hb Hc.
    simpl in Hb;
    congruence.
  +
    intros ? ? Ha Hb Hc.
    case_eq (eqP a u);
    case_eq (in_set eqP Y a);
    intros Hd He.
    rewrite He in Hc;
    simpl in Hc.
    eapply bop_or_intro.
    right.
    eapply in_set_filter_elim in Hc.
    firstorder.
    intros x y Hx.
    apply negb_eqP_congruence;
    exact Hx.
    eapply bop_or_intro.
    rewrite He in Hc;
    simpl in Hc.
    eapply in_set_filter_elim in Hc.
    right; firstorder.
    eapply negb_eqP_congruence.
    rewrite He in Hc;
    simpl in Hc.
    eapply bop_or_elim in Hc.
    eapply bop_or_intro.
    destruct Hc as [Hc | Hc].
    left; auto.
    right. 
    eapply in_set_filter_elim in Hc.
    destruct Hc as [Hcl Hcr];
    auto.
    eapply negb_eqP_congruence.
    rewrite Hd, He in Hb;
    simpl in Hb; 
    congruence.
Qed.


Lemma in_set_not_member :
  forall (X : list P) (a b : P),
  in_set eqP X a = false ->
  in_set eqP X b = true ->
  eqP a b = false.
Proof.
  induction X as [|u X IHx];
  simpl.
  + congruence.
  + intros ? ? Ha Hb.
    eapply bop_or_elim in Hb.
    eapply bop_or_false_elim in Ha.
    destruct Ha as [Hal Har].
    destruct Hb as [Hb | Hb].
    case_eq (eqP a b);
    intro Hc.
    rewrite (trnP _ _ _ Hc Hb) in Hal;
    congruence.
    reflexivity.
    eapply IHx;
    try assumption.
Qed.



Lemma brel_set_filter : 
  forall (X Y : list P) (a : P),
  in_set eqP X a = false ->
  brel_set eqP (a :: X) Y = true ->
  brel_set eqP X (filter (λ x : P, negb (eqP a x)) Y) = true.
Proof.
  intros ? ? ? Ha Hb.
  eapply brel_set_elim_prop in Hb;
  try assumption.
  destruct Hb as [Hbl Hbr].
  eapply brel_set_intro_prop;
  try assumption.
  split.
  +
    intros ? Hb.
    eapply in_set_filter_intro;
    try assumption.
    eapply negb_eqP_congruence.
    split.
    eapply Bool.negb_true_iff.
    eapply in_set_not_member;
    [exact Ha | exact Hb].
    eapply Hbl.
    eapply in_set_cons_intro;
    try assumption.
    right.
    exact Hb.
  +
    intros ? Hb.
    eapply in_set_filter_elim in Hb.
    destruct Hb as [Hba Hbb].
    pose proof Hbr a0 Hbb as Hc.
    eapply in_set_cons_elim in Hc;
    try assumption.
    eapply Bool.negb_true_iff in Hba.
    destruct Hc as [Hc | Hc].
    rewrite Hba in Hc.
    congruence.
    exact Hc.
    eapply negb_eqP_congruence.
Qed.


Lemma fold_right_in_set_false :
  forall (X : list P) (a p : P)
  (f : P -> P -> P),
  (forall (x y w v : P),
    eqP x y = true ->
    eqP w v = true ->
    eqP (f x w) (f y v) = true) ->
  in_set eqP X a = false ->
  eqP 
    (fold_right f p X)
    (fold_right f p 
      (filter (λ x : P, negb (eqP a x)) X)) = true.
Proof.
  induction X as [|ax X IHx];
  simpl.
  + 
    intros ? ? ? fcong Hb.
    apply refP.
  +
    intros ? ? ? fcong Hb.
    case_eq (in_set eqP X a);
    case_eq (eqP a ax);
    intros Hc Hd.
    ++
      rewrite Hc, Hd in Hb; 
      simpl in Hb;
      congruence.
    ++
      rewrite Hc, Hd in Hb; 
      simpl in Hb;
      congruence.
    ++
      rewrite Hc, Hd in Hb; 
      simpl in Hb;
      congruence.
    ++
      simpl.
      eapply fcong.
      eapply refP.
      eapply IHx;
      try assumption.
Qed.


Lemma fold_right_in_set :
  forall (X : list P) (a p : P)
  (f : P -> P -> P),
  (forall x y z : P, 
    eqP (f x (f y z)) (f (f x y) z) = true) ->
  (forall x y : P, eqP (f x y) (f y x) = true) ->
  (forall (x y w v : P),
    eqP x y = true ->
    eqP w v = true ->
    eqP (f x w) (f y v) = true) ->
  (forall x y : P, eqP x y = true ->
    eqP (f x y) y = true) ->
  in_set eqP X a = true ->
  eqP (fold_right f p X) 
    (f a (fold_right f p 
      (filter (fun x => negb (eqP a x)) X))) = true.
Proof.
  induction X as [|ax X IHx];
  simpl.
  + 
    intros ? ? ? fassoc fcom fcong Ha Hb.
    simpl in Hb;
    congruence.
  +
    intros ? ? ? fassoc fcom fcong Ha Hb.
    simpl in * |- *.
    case_eq ((in_set eqP X a));
    case_eq (eqP a ax); 
    intros Hc Hd;
    simpl.
    ++ (* a = x *)
      pose proof IHx a p f fassoc fcom
        fcong Ha Hd as He.
      remember (fold_right f p X) as w.
      remember (fold_right f p 
        (filter (λ x : P, negb (eqP a x)) X)) as v.
      eapply trnP with (f ax (f a v)).
      eapply fcong.
      eapply refP.
      exact He.
      assert (Ht : eqP (f ax (f a v)) 
        (f (f ax a) v) = true).
      eapply fassoc.
      rewrite <-Ht.
      eapply cong_eqP.
      eapply refP.
      eapply fcong.
      eapply symP.
      eapply Ha.
      eapply symP.
      exact Hc.
      eapply refP.
    ++ 
      (* Induction case *)
      pose proof IHx a p f fassoc fcom fcong
        Ha Hd as He.
      remember (fold_right f p X) as w.
      remember (fold_right f p 
        (filter (λ x : P, negb (eqP a x)) X)) as v.
      eapply trnP with (f ax (f a v)).
      eapply fcong.
      eapply refP.
      exact He.
      eapply trnP with (f (f ax a) v).
      eapply fassoc.
      eapply trnP with (f (f a ax) v).
      eapply fcong.
      eapply fcom.
      eapply refP.
      eapply symP.
      eapply fassoc.
    ++
      remember (fold_right f p X) as w.
      remember (fold_right f p 
        (filter (λ x : P, negb (eqP a x)) X)) as v.
      apply fcong.
      eapply symP;
      exact Hc.
      subst.
      eapply fold_right_in_set_false;
      try assumption.
    ++
      rewrite Hc, Hd in Hb;
      simpl in Hb; congruence.
Qed.



Lemma fold_right_congruence : 
  forall (X Y : list P) (p : P)
  (f : P -> P -> P),
  (forall x y z : P, 
    eqP (f x (f y z)) (f (f x y) z) = true) ->
  (forall x y : P, eqP (f x y) (f y x) = true) ->
  (forall (x y w v : P),
    eqP x y = true ->
    eqP w v = true ->
    eqP (f x w) (f y v) = true) ->
  (forall x y : P, eqP x y = true ->
    eqP (f x y) y = true) ->
  brel_set eqP X Y = true ->
  eqP (fold_right f p X) (fold_right f p Y) = true.
Proof.
  induction X as [|a X IHx].
  + 
    intros ? ? ? ? fassoc fcom fcong Ha.
    eapply brel_set_nil in Ha;
    rewrite Ha;
    simpl;
    apply refP.
  + (* Inducation Case *)
    simpl;
    intros ? ? ? fassoc fcom fcong Ha Hb.
    destruct (in_set eqP X a) eqn:Hc.
    ++
      assert (Hd : brel_set eqP X Y = true).
      apply brel_set_elim_prop in Hb;
      [|apply symP | apply trnP].
      destruct Hb as [Hbl Hbr].
      eapply brel_set_intro_prop.
      apply refP.
      split.
      +++
        intros ? Hd.
        eapply Hbl.
        eapply in_set_cons_intro.
        apply symP.
        right.
        exact Hd.
      +++
        intros ? Hd.
        pose proof (Hbr _ Hd) as He.
        apply in_set_cons_elim in He.
        destruct He as [He | He].
        eapply in_set_right_congruence.
        apply symP.
        apply trnP.
        exact He.
        exact Hc.
        exact He.
        apply symP.
      +++
        eapply trnP.
        eapply fold_right_idempotent_aux_one.
        exact fassoc.
        exact fcom.
        intros ? ? ? Hx Hy.
        eapply fcong.
        exact Hy.
        intros ? ? Hx.
        eapply Ha;
        exact Hx.
        exact Hc.
        eapply IHx.
        exact fassoc.
        exact fcom.
        exact fcong.
        exact Ha.
        exact Hd.
    ++
      remember (filter (fun x => negb (eqP a x)) Y) as 
        remove_a_Y.
      (* There is no a in remove_a_Y *)
      assert(Hd: in_set eqP remove_a_Y a = false).
      subst; eapply in_set_false.

      (* There is a, in fact one, 'a' in Y*)
      assert(He : in_set eqP Y a = true).  
        eapply brel_set_elim_prop in Hb;
        try assumption.
        destruct Hb as [Hbl Hbr].
        eapply Hbl.
        cbn; eapply bop_or_intro.
        left. apply refP.
      
      assert(Hg : brel_set eqP X remove_a_Y = true).
        rewrite Heqremove_a_Y.
        eapply brel_set_filter;
        try assumption.
      (* Specialise the induction hypothesis *)
      pose proof IHx remove_a_Y p f fassoc fcom fcong Ha Hg as Hh.
      (* 
        I need to play with transitivity. 
      *)
      eapply trnP.
      eapply fcong.
      eapply refP.
      exact Hh.
      eapply symP.
      eapply trnP.
      (* Now I am in a bit better situation. *)
      eapply fold_right_in_set.
      exact fassoc.
      exact fcom.
      exact fcong.
      exact Ha.
      exact He.
      rewrite <-Heqremove_a_Y.
      eapply fcong.
      all:eapply refP.
Qed.
      



Lemma fold_left_simp : 
  forall (X : list (A * P))
    (pa : A) (pb : P),
  fold_left 
    (λ '(s1, t1) '(_, t2), (s1, addP t1 t2)) 
    X (pa, pb) =  
    (pa, fold_left (λ t1 t2, addP t1 t2) 
    (List.map snd X ) pb).
Proof.
  induction X as [|(a,b) X IHx].
  + simpl; reflexivity.
  + simpl; intros ? ?.
    rewrite IHx.
    reflexivity.
Qed.

Lemma map_in_set :
  forall (X : list (A * P)) (au av : A)
  (bu bv : P), 
  eqA au av = true ->
  eqP bu bv = true ->
  (av, bv) [in] X ->
  in_set eqA (map fst X) au = true ∧
  in_set eqP (map snd X) bu = true.
Proof.
  induction X as [|(ux, vx) X IHx];
  simpl.
  +
    intros ? ? ? ? Ha Hb Hc.
    congruence.
  +
    intros ? ? ? ? Ha Hb Hc.
    eapply bop_or_elim in Hc.
    split.
    ++ 
      eapply bop_or_intro.
      destruct Hc as [Hc | Hc].
      eapply bop_and_elim in Hc.
      firstorder.
      right.
      exact (proj1 (IHx _ _ _ _ Ha Hb Hc)).
    ++
      eapply bop_or_intro.
      destruct Hc as [Hc | Hc].
      eapply bop_and_elim in Hc.
      left. firstorder.
      right.
      exact (proj2 (IHx _ _ _ _ Ha Hb Hc)).
Qed.






Lemma length_filter {T : Type} : 
  forall (X : list T) (f : T -> bool),
  (length (filter f X) < S (length X))%nat.
Proof.
  induction X as [| ax X IHx];
  simpl.
  +
    intros ?.
    nia.
  +
    intros ?.
    destruct (f ax);
    simpl.
    ++
      specialize (IHx f).
      nia.
    ++
      specialize (IHx f).
      nia.
Qed.



Lemma membship_filter : 
  forall (Y X : list (A * P)) (ax : A)
  (bx : P),
  (ax, bx) :: X =S= Y ->
  Y =S= (ax, bx) :: 
  filter (λ p : A * P, 
  negb (brel_product eqA eqP p (ax, bx))) Y.
Proof.
  intros ? ? ? ? Ha.
  eapply brel_set_intro_prop;
  try assumption.
  eapply refAP.
  eapply brel_set_elim_prop in Ha;
  [|apply symAP | apply trnAP].
  destruct Ha as [Hal Har].
  split.
  +
    intros (au, av) Hb.
    apply in_set_cons_intro;
    [apply symAP |].
    case_eq (eqP bx av);
    case_eq (eqA ax au);
    intros Hc Hd.
    ++
      left.
      eapply brel_product_intro;
      try assumption.
    ++
      right.
      eapply in_set_filter_intro;
      [eapply symAP | eapply bop_neg_bProp_product_cong |].
      split.
      eapply Bool.negb_true_iff.
      unfold brel_product.
      apply symP in Hd.
      rewrite Hd.
      assert (He : eqA au ax = false).
      case_eq (eqA au ax); intro Hf.
      apply symA in Hf.
      rewrite Hf in Hc;
      congruence.
      reflexivity.
      rewrite He.
      compute;
      reflexivity.
      exact Hb.
    ++
      right.
      eapply in_set_filter_intro;
      [eapply symAP | eapply bop_neg_bProp_product_cong |].
      split.
      eapply Bool.negb_true_iff.
      unfold brel_product.
      apply symA in Hc.
      rewrite Hc.
      assert (He : eqP av bx = false).
      case_eq (eqP av bx); intro Hf.
      apply symP in Hf.
      rewrite Hf in Hd;
      congruence.
      reflexivity.
      rewrite He.
      compute;
      reflexivity.
      exact Hb.
    ++
      right.
      eapply in_set_filter_intro;
      [eapply symAP | eapply bop_neg_bProp_product_cong |].
      split.
      eapply Bool.negb_true_iff.
      unfold brel_product.
      assert (He : eqA au ax = false).
      case_eq (eqA au ax); intro Hf.
      apply symA in Hf.
      rewrite Hf in Hc;
      congruence.
      reflexivity.
      rewrite He.
      compute;
      reflexivity.
      exact Hb.
  +
    intros (au, av) Hb.
    apply in_set_cons_elim in Hb;
    [|apply symAP].
    case_eq (eqP bx av);
    case_eq (eqA ax au);
    intros Hc Hd.
    ++
      eapply Hal.
      eapply in_set_cons_intro;
      [eapply symAP |].
      left.
      unfold brel_product.
      rewrite Hc, Hd;
      compute; reflexivity.
    ++
      destruct Hb as [Hb | Hb].
      eapply brel_product_elim in Hb.
      destruct Hb as [Hb _].
      rewrite Hb in Hc;
      congruence.
      eapply in_set_filter_elim in Hb.
      exact (snd Hb).
      eapply bop_neg_bProp_product_cong.
    ++
      destruct Hb as [Hb | Hb].
      eapply brel_product_elim in Hb.
      destruct Hb as [_ Hb].
      rewrite Hb in Hd;
      congruence.
      eapply in_set_filter_elim in Hb.
      exact (snd Hb).
      eapply bop_neg_bProp_product_cong.
    ++
      destruct Hb as [Hb | Hb].
      eapply brel_product_elim in Hb.
      destruct Hb as [_ Hb].
      rewrite Hb in Hd;
      congruence.
      eapply in_set_filter_elim in Hb.
      exact (snd Hb).
      eapply bop_neg_bProp_product_cong.
Qed.


Lemma map_snd_filter_membership_true : 
  forall (X : list (A * P)) (ax : A) (bx : P),
  in_set eqP 
    (map snd (filter (λ (p : A * P), 
      negb (brel_product eqA eqP p (ax, bx))) X)) bx = true ->
    in_set eqP (map snd X) bx = true.
Proof.
  induction X as [|(au, av) X IHx];
  simpl.
  +
    intros ? ? Ha;
    congruence.
  +
    intros ? ? Ha.
    case_eq ((eqP av bx));
    case_eq ((eqA au ax));
    intros Hb Hc;
    rewrite Hb, Hc in Ha;
    simpl in Ha.
    ++
      apply symP in Hc.
      rewrite Hc;
      compute;
      reflexivity.
    ++
      apply symP in Hc.
      rewrite Hc;
      compute;
      reflexivity.
    ++
      assert (Hd : eqP bx av = false).
      case_eq (eqP bx av); intros Hf.
      apply symP in Hf;
      rewrite Hf in Hc;
      congruence.
      reflexivity.
      rewrite Hd in Ha |- *.
      simpl in * |- *.
      eapply IHx; exact Ha.
    ++
      assert (Hd : eqP bx av = false).
      case_eq (eqP bx av); intros Hf.
      apply symP in Hf;
      rewrite Hf in Hc;
      congruence.
      reflexivity.
      rewrite Hd in Ha |- *.
      simpl in * |- *.
      eapply IHx; exact Ha.
Qed.



Lemma in_set_filter_map_true_snd_forward : 
  forall (X : list (A * P)) (ax : A) (a bx : P),
  eqP bx a = false ->
  in_set eqP (map snd X) a = true ->
  in_set eqP
  (map snd (filter (λ p : A * P, 
    negb (brel_product eqA eqP p (ax, bx))) X)) a = true.
Proof.
  induction X as [|(au, av) X IHx];
  simpl.
  +
    intros ? ? ? Ha Hb.
    congruence.
  +
    intros ? ? ? Ha Hb.
    case_eq (in_set eqP (map snd X) a);
    case_eq (eqP a av); 
    intros Hc Hd; 
    rewrite Hc, Hd in Hb.
    ++
      simpl.
      case_eq ((eqP av bx));
      case_eq (eqA au ax);
      intros He Hf;
      simpl.
      *
        rewrite (symP _ _ (trnP _ _ _ Hc Hf)) in Ha;
        congruence.
      *
        rewrite Hc;
        compute;
        reflexivity.
      *
        rewrite Hc;
        compute;
        reflexivity.
      *
        rewrite Hc; 
        compute;
        reflexivity.
    ++
      case_eq ((eqP av bx));
      case_eq (eqA au ax);
      intros He Hf;
      simpl.
      *
        (* Induction Hypothesis *)
        eapply IHx;
        try assumption.
      *
        rewrite Hc;
        simpl.
        eapply IHx;
        try assumption.
      *
        rewrite Hc;
        simpl.
        eapply IHx;
        try assumption.
      *
        rewrite Hc;
        simpl.
        eapply IHx;
        try assumption.
      ++
        case_eq ((eqP av bx));
        case_eq (eqA au ax);
        intros He Hf;
        simpl.
        *
          rewrite (symP _ _ (trnP _ _ _ Hc Hf)) in Ha;
          congruence.
        *
          rewrite Hc;
          compute; 
          reflexivity.
        *
          rewrite Hc;
          compute; 
          reflexivity.
        * 
          rewrite Hc;
          compute; 
          reflexivity.
      ++
        simpl in Hb; 
        congruence.
Qed.



Lemma in_set_filter_map_true_snd_backward : 
  forall (X : list (A * P)) (ax : A) (a bx : P),
  eqP bx a = false ->
  in_set eqP
  (map snd (filter (λ p : A * P, 
    negb (brel_product eqA eqP p (ax, bx))) X)) a = true ->
  in_set eqP (map snd X) a = true. 
Proof.
  induction X as [|(au, av) X IHx];
  simpl.
  +
    intros ? ? ? Ha Hb;
    congruence.
  +
    intros ? ? ? Ha Hb.
    case_eq (eqP av bx);
    case_eq (eqA au ax);
    intros Hc Hd;
    rewrite Hc, Hd in Hb;
    simpl in Hb.
    ++
      eapply bop_or_intro.
      right.
      eapply IHx; 
      try assumption.
      exact Ha.
      exact Hb.
    ++
      eapply bop_or_elim in Hb.
      eapply bop_or_intro.
      destruct Hb as [Hb | Hb].
      left. exact Hb.
      right.
      eapply IHx;
      try assumption.
      exact Ha.
      exact Hb.
    ++
      eapply bop_or_elim in Hb.
      eapply bop_or_intro.
      destruct Hb as [Hb | Hb].
      left. exact Hb.
      right.
      eapply IHx;
      try assumption.
      exact Ha.
      exact Hb.
    ++
      eapply bop_or_elim in Hb.
      eapply bop_or_intro.
      destruct Hb as [Hb | Hb].
      left. exact Hb.
      right.
      eapply IHx;
      try assumption.
      exact Ha.
      exact Hb.
Qed.



Lemma brel_set_filter_product : 
  forall (X : list (A * P)) (ax : A)
  (bx : P),
  brel_set eqP (bx :: map snd X)
  (bx :: map snd (filter
    (λ (p : A * P), 
      negb (brel_product eqA eqP p (ax, bx))) X)) = true.
Proof.
  intros ? ? ?.
  eapply brel_set_intro_prop;
  try assumption.
  split.
  +
    intros ? Ha.
    eapply in_set_cons_elim in Ha;
    try assumption.
    eapply in_set_cons_intro;
    try assumption.
    case_eq (eqP bx a);
    intros Hb.
    left; exact eq_refl.
    right.
    destruct Ha as [Ha | Ha].
    rewrite Ha in Hb;
    congruence.
    eapply in_set_filter_map_true_snd_forward;
    try assumption.
  +
    intros ? Ha.
    eapply in_set_cons_elim in Ha;
    try assumption.
    eapply in_set_cons_intro;
    try assumption.
    case_eq (eqP bx a);
    intros Hb.
    left; reflexivity.
    right.
    destruct Ha as [Ha | Ha].
    rewrite Ha in Hb.
    congruence.
    eapply in_set_filter_map_true_snd_backward;
    try assumption.
    exact Hb.
    exact Ha.
Qed.





Lemma duplicate_an_element : 
  forall (Y Xt : list (A * P)) (ax : A)
  (bx : P),
  (ax, bx) :: Xt =S= Y ->
  brel_set eqP (map snd Y) (bx :: map snd Y) = true.
Proof.
    intros ? ? ? ? Ha.
    eapply brel_set_intro_prop;
    try assumption.
    eapply brel_set_elim_prop in Ha;
    [|eapply symAP| eapply trnAP].
    split.
    +
      intros ? Hb.
      eapply in_set_cons_intro;
      try assumption.
      right; exact Hb.
    +
      intros ? Hb.
      eapply in_set_cons_elim in Hb;
      try assumption.
      destruct Hb as [Hb | Hb].
      ++
        eapply in_set_right_congruence with bx;
        try assumption.
        destruct Ha as [Hal Har].
        pose proof Hal (ax, bx) as Hw.
        assert (Hv : (ax, bx) [in] (ax, bx) :: Xt).
        apply in_set_cons_intro;
        [eapply symAP | left].
        compute.
        rewrite refA, refP;
        reflexivity.
        specialize (Hw Hv).
        eapply map_in_set in Hw.
        destruct Hw as [Hwl Hwr].
        exact Hwr.
        apply refA.
        apply refP.
      ++
        exact Hb.
Qed.



(*
This turned out to be more tricky than 
I anticipated because now I can't 
do case analysis

Key to prove this lemma is staging a tricky 
induction principal that decreases on both components X and Y, 
contrary to structural induction. In addition, 
it also requires some key insight about transitivity. This 
equality is very difficult, yet fun at the same time, to 
work with. 
*)
Lemma map_preservs_equivalence_on_second : 
  forall X Y : list (A * P), 
  X =S= Y -> 
  brel_set eqP (List.map snd X) (List.map snd Y) = true.
Proof.
  intro X.
  refine ((fix Fn xs 
    (Hacc : (Acc (fun x y => 
      (List.length x < List.length y)%nat) xs)) 
    {struct Hacc} := _) X _).
  intros ? Ha.
  refine (match xs as xsp return xs = xsp -> _ with 
  | [] => _ 
  | (ax, bx) :: Xt => _ 
  end eq_refl); simpl; intros Hb.
  +
    rewrite Hb in Ha.
    eapply brel_set_nil  in Ha.
    rewrite Ha;
    compute; 
    reflexivity.
  +
    (* Induction case that involves 
      some tricky transitivity *)
    rewrite Hb in Ha.
    (* get rid of (ax, bx) from Xt *)
    remember (filter (λ p : A * P, 
      negb (brel_product eqA eqP p (ax, bx))) xs) as Xrem.
    (* get rid of all (ax, bx) from Y *)
    remember (filter (λ p : A * P, 
      negb (brel_product eqA eqP p (ax, bx))) Y) as Yrem.
    assert (Hc : Y =S= (ax, bx) :: Yrem).
    rewrite HeqYrem.
    eapply membship_filter;
    exact Ha.
    assert (Hd : Xrem =S= Yrem).
    rewrite HeqXrem, HeqYrem.
    eapply filter_congruence_gen;
    try assumption.
    eapply bop_neg_bProp_product_cong;
    try assumption.
    rewrite <-Hb in Ha;
    exact Ha.
    assert (He : Acc (fun x y => 
      (List.length x < List.length y)%nat) Xrem).
    eapply Acc_inv with xs;
    try assumption.
   
    rewrite HeqXrem, Hb;
    simpl.
    rewrite refA, refP;
    simpl.
    eapply length_filter.
    specialize (Fn Xrem He Yrem Hd) as Hf.
    (* 
      Here comes tricky transitivity 
    *)
    eapply brel_set_transitive with (bx :: map snd Yrem);
    try assumption.
    eapply brel_set_transitive with (bx :: (map snd Xrem));
    try assumption.
    ++
      rewrite HeqXrem.
      rewrite Hb;
      simpl.
      rewrite refA, refP;
      simpl.
      eapply brel_set_filter_product.
    ++
      eapply brel_set_intro_prop;
      try assumption.
      eapply brel_set_elim_prop in Hf;
      try assumption.
      destruct Hf as [Hfl Hfr].
      split.
      +++
        intros a Hg.
        eapply in_set_cons_elim in Hg;
        try assumption.
        eapply in_set_cons_intro; 
        try assumption.
        destruct Hg as [Hg | Hg].
        left; exact Hg.
        right.
        eapply Hfl;
        exact Hg.
      +++
        intros a Hg.
        eapply in_set_cons_elim in Hg;
        try assumption.
        eapply in_set_cons_intro; 
        try assumption.
        destruct Hg as [Hg | Hg].
        left; exact Hg.
        right.
        eapply Hfr;
        exact Hg.
    ++
      eapply brel_set_symmetric.
      (* duplicate a 'bx' in Y *)
      assert (Hg : brel_set eqP (map snd Y) 
        (bx :: map snd Y) = true).
      eapply duplicate_an_element;
      exact Ha.
      eapply brel_set_transitive with (bx :: map snd Y);
      try assumption.
      rewrite HeqYrem.
      eapply brel_set_filter_product.
    +
      eapply (Wf_nat.well_founded_ltof _ 
        (fun x => List.length x)).
Qed.




Lemma fold_left_congruence : 
  forall (X Y : list (A * P)) 
  (pa : A) (pb : P),
  (forall u v, (u, v) [in] X -> eqA u pa = true) ->
  (forall u v, (u, v) [in] Y -> eqA u pa = true) ->
  X =S= Y ->
  [fold_left (λ '(s1, t1) '(_, t2), (s1, addP t1 t2)) 
    X (pa, pb)] =S= 
  [fold_left (λ '(s1, t1) '(_, t2), (s1, addP t1 t2)) 
    Y (pa, pb)].
Proof.
  intros ? ? ? ? Ha Hb Hc.
  eapply  brel_set_elim_prop in Hc;
  [| apply symAP| apply trnAP].
  destruct Hc as [Hcl Hcr].
  repeat rewrite fold_left_simp.
  eapply  brel_set_intro_prop;
  [apply refAP | split].
  + intros (au, pu) Hd.
    apply bop_or_elim in Hd.
    destruct Hd as [Hd | Hd].
    apply brel_product_elim in Hd.
    destruct Hd as [Hdl Hdr].
    apply bop_or_intro.
    left.
    apply brel_product_intro.
    exact Hdl.
    eapply trnP.
    exact Hdr.
    repeat rewrite fold_symmetric;
    try assumption.
    eapply fold_right_congruence.
    intros ? ? ?.
    eapply symP.
    eapply addP_assoc.
    eapply addP_com.
    intros ? ? ? ? Hxy Hwv;
    eapply cong_addP;
    try assumption.
    exact addP_cong.
    apply map_preservs_equivalence_on_second.
    eapply brel_set_intro_prop.
    eapply refAP.
    split; assumption.
    intros ?.
    eapply addP_com_cong.
    eapply addP_com_cong.
    inversion Hd.
  + 
    intros (au, pu) Hd.
    apply bop_or_elim in Hd.
    destruct Hd as [Hd | Hd].
    apply brel_product_elim in Hd.
    destruct Hd as [Hdl Hdr].
    apply bop_or_intro.
    left.
    apply brel_product_intro.
    exact Hdl.
    eapply trnP.
    exact Hdr.
    repeat rewrite fold_symmetric.
    eapply fold_right_congruence.
    intros ? ? ?;
    eapply symP;
    eapply addP_assoc.
    exact addP_com.
    intros ? ? ? ? Hxy Hwv;
    eapply cong_addP;
    try assumption.
    exact addP_cong.
    apply map_preservs_equivalence_on_second.
    eapply brel_set_intro_prop.
    eapply refAP.
    split; assumption.
    eapply addP_assoc_cong.
    eapply addP_com_cong.
    eapply addP_assoc_cong.
    eapply addP_com_cong.
    inversion Hd.
Qed.



(* generalise this one *)
Lemma manger_merge_set_new_aux_fold_filter :
  ∀ (X Y : list (A * P)) (pa : A) (pb : P), 
  X =S= Y -> 
  [fold_left (λ '(s1, t1) '(_, t2), 
    (s1, addP t1 t2)) 
    (filter (λ '(s2, _), eqA pa s2) X) 
    (pa, pb)] =S= 
  [fold_left (λ '(s1, t1) '(_, t2), 
    (s1, addP t1 t2))
    (filter (λ '(s2, _), eqA pa s2) Y) 
    (pa, pb)].
Proof.
  intros ? ? ? ? Ha.
  assert (Hb : theory.bProp_congruence _  
    (brel_product eqA eqP)
    (λ '(s2, _), eqA pa s2)).
  intros (aa, ap) (ba, bp) He.
  apply brel_product_elim in He.
  destruct He as [Hel Her].
  case_eq (eqA pa aa); intro Hf.
  rewrite (trnA pa aa ba Hf Hel);
  reflexivity.
  case_eq (eqA pa ba); intro Hg.
  apply symA in Hel.
  rewrite (trnA pa ba aa Hg Hel) in Hf;
  congruence.
  reflexivity.
  pose proof filter_congruence_gen 
    X Y (λ '(s2, _), eqA pa s2) Hb Ha as Hc.
  remember (filter (λ '(s2, _), eqA pa s2) X) 
  as Xf.
  remember (filter (λ '(s2, _), eqA pa s2) Y) 
  as Yf.
  eapply fold_left_congruence.
  + intros ? ? Hd.
    rewrite HeqXf in Hd.
    eapply in_set_filter_elim in Hd;
    firstorder.
  + intros ? ? Hd.
    rewrite HeqYf in Hd.
    eapply in_set_filter_elim in Hd;
    firstorder.
  + exact Hc.
Qed. 


  


Lemma append_congruence : 
  forall X₁ X₂ Y₁ Y₂ : list (A * P), 
  X₁ =S= Y₁ -> 
  X₂ =S= Y₂ ->
  X₁ ++ X₂ =S= Y₁ ++ Y₂.
Proof.
  intros ? ? ? ? Ha Hb.
  apply brel_set_elim_prop in Ha, Hb;
  try (repeat apply symAP; repeat apply trnAP).
  destruct Ha as [Hal Har].
  destruct Hb as [Hbl Hbr].
  apply brel_set_intro_prop.
  apply refAP.
  split.
  + intros (a, b) Hc.
    apply in_set_concat_elim in Hc.
    destruct Hc as [Hc | Hc].
    apply in_set_concat_intro.
    left.
    apply Hal; exact Hc.
    apply in_set_concat_intro.
    right.
    apply Hbl; exact Hc.
    apply symAP.
  + intros (a, b) Hc.
    apply in_set_concat_elim in Hc.
    destruct Hc as [Hc | Hc].
    apply in_set_concat_intro.
    left.
    apply Har; exact Hc.
    apply in_set_concat_intro.
    right.
    apply Hbr; exact Hc.
    apply symAP.
Qed.

Local Notation "[MMSN]"  := 
  (manger_merge_sets_new eqA addP).

Lemma manger_merge_set_new_congruence_left :
  ∀ X Y p, 
  X =S= Y -> [MMSN] X p =S= [MMSN] Y p.
Proof.
  unfold manger_merge_sets_new,
  manger_merge_sets_new_aux.
  intros ? ? (pa, pb) Ha; cbn.
  pose proof 
    (manger_merge_set_new_aux_congruence_left X Y pa Ha) as 
    [Hb Hc].
  eapply append_congruence;
  [exact Hb | 
    eapply manger_merge_set_new_aux_fold_filter;
    exact Ha].
Qed.

(* [MMS] and [MMSN] are same *)
Lemma manger_merge_set_manger_merge_set_new_same :
  forall X p, [MMS] X p = [MMSN] X p.
Proof.
  unfold manger_merge_sets_new,
  manger_merge_sets_new_aux.
  induction X as [|(a, b) X Ihx].
  + simpl;
    intros ?; reflexivity.
  + simpl.
    intros (pa, pb); simpl.
    case_eq (eqA pa a); intro Ha;
    simpl.
    ++
      rewrite Ihx;
      reflexivity.
    ++
      f_equal.
      rewrite Ihx;
      reflexivity.
Qed.


Lemma manger_merge_set_congruence_left :
  ∀ Y Y' p, Y =S= Y' -> ([MMS] Y p) =S= ([MMS] Y' p).
Proof.
  intros ? ? ? Ha.
  repeat rewrite manger_merge_set_manger_merge_set_new_same.
  apply manger_merge_set_new_congruence_left;
  exact Ha.
Qed.

Lemma uop_manger_phase1_auxiliary_congurence_left :
  ∀ X Y1 Y2,  Y1 =S= Y2 -> [P1AX] Y1 X =S= [P1AX] Y2 X. 
Proof. induction X; intros Y1 Y2 H1; simpl. 
       - exact H1. 
       - assert (H2 := manger_merge_set_congruence_left _ _ a H1). 
         apply IHX; auto.
Qed.

Lemma  fst_unique_in_set_implies_manger_merge_set_fixpoint : 
∀ Y a' p', fst_unique_in_set ((a', p') :: Y) -> ([MMS] Y (a',p')) =S= ((a', p') :: Y). 
Proof. induction Y; intros a' p' H1; simpl. 
       - apply refSetAP. 
       - destruct a as [a p].
         case_eq(eqA a' a); intro H2.
         + case_eq(eqP p' p); intro H7.
           * assert (H3 : ((a', p') :: (a, p) :: Y) =S= ((a', p') :: Y)).
             {
               assert (H4 : (a', p') == (a, p)).
               {
                 apply brel_product_intro; auto. 
               } 
               exact (remove_duplicate_from_set Y _ _ H4). 
             } 
             assert (H4 : fst_unique_in_set ((a', p') :: Y)).
             {
               exact (fst_unique_in_set_congruence _ _ H3 H1). 
             } 
             assert (H5 := IHY _ _ H4).
             apply symSetAP in H3.
             assert (H6 := trnSetAP _ _ _ H5 H3).
             assert (H8 := cong_addP _ _ _ _(refP p') H7).
             assert (H9 := idemP p'). apply symP in H9.
             assert (H10 := trnP _ _ _ H9 H8).
             assert (H11 : (a', addP p' p) == (a', p')).
             {
               apply brel_product_intro; auto. 
             }
             assert (H12 : [MMS] Y (a', addP p' p) =S= [MMS] Y (a', p')).
             {
               exact(manger_merge_set_congruence_right Y _ _ H11). 
             } 
             exact(trnSetAP _ _ _ H12 H6). 
           * apply fst_unique_in_set_cons_elim in H1.
             destruct H1 as [H1 H3]. 
             apply fst_unique_in_set_cons_elim in H3.
             destruct H3 as [H3 H4].
             assert (H5 : (a, p) [in] (a, p) :: Y).
             {
               apply in_set_cons_intro.
               -- apply symAP.
               -- left. apply brel_product_intro.
                  apply refA. apply refP. 
             } 
             assert (H6 := H1 _ _ H5).
             destruct H6 as [H6 | H6].
             -- apply brel_product_elim in H6.
                destruct H6 as [_ H6].
                rewrite H6 in H7. discriminate H7. 
             -- rewrite H6 in H2. discriminate H2. 
         + assert (H3 : (a, p) :: (a', p') :: Y =S= (a', p') :: (a, p) :: Y).
           {
             apply set_rearrange_v1. 
           } 
           assert (H4 : fst_unique_in_set ((a', p') :: Y)).
           {
             apply symSetAP in H3. 
             assert (H5 := fst_unique_in_set_congruence _ _ H3 H1).
             apply fst_unique_in_set_cons_elim in H5.
             destruct H5 as [_ H5].
             exact H5. 
           } 
           assert (H5 := IHY _ _ H4).
           assert (H6 : (a, p) :: ([MMS] Y (a', p')) =S= (a, p) :: (a', p') :: Y).
           {
             exact (set_equal_with_cons_right _ _ (a, p) H5). 
           } 
           exact (trnSetAP _ _ _ H6 H3). 
Qed. 
         
Lemma  fst_unique_in_set_implies_uop_manger_phase_1_auxiliary_fixpoint_general : 
∀ X Y, fst_unique_in_set (X ++ Y) -> ([P1AX] Y X) =S= (X ++ Y). 
Proof. induction X; intros Y H1.
       - simpl.
         apply brel_set_reflexive; auto.
         + apply refAP. 
         + apply symAP.          
       - destruct a as [a p].
         rewrite <- app_comm_cons in H1.
         rewrite <- app_comm_cons. simpl.
         assert (H4 : (a, p) :: X ++ Y =S= X ++ (a, p) :: Y). 
         {
           apply set_rearrange_v2. 
         } 
         assert (H2: fst_unique_in_set (X ++ ((a, p) :: Y))).
         {
           exact (fst_unique_in_set_congruence _ _ H4 H1). 
         } 
         assert (H3 := IHX _ H2).
         assert (H3' : fst_unique_in_set ((a, p) :: Y)).
         {
           exact (fst_unique_in_set_concat_elim_right _ _ H2). 
         } 
         assert (H4' : ([MMS] Y (a, p)) =S= ((a, p) :: Y)).
         {
           exact (fst_unique_in_set_implies_manger_merge_set_fixpoint _ _ _ H3'). 
         } 
         assert (H5 : [P1AX] ([MMS] Y (a, p)) X =S= [P1AX] ((a, p) :: Y) X).
         {
           exact (uop_manger_phase1_auxiliary_congurence_left _ _ _ H4'). 
         }
         apply symSetAP in H4. 
         exact (trnSetAP _ _ _ (trnSetAP _ _ _ H5 H3) H4). 
Qed. 

             
Lemma  fst_unique_in_set_implies_uop_manger_phase_1_auxiliary_fixpoint : 
∀ X, fst_unique_in_set X -> ([P1AX] nil X) =S= X. 
Proof. intro X.
       assert (H1 := fst_unique_in_set_implies_uop_manger_phase_1_auxiliary_fixpoint_general X nil).
       rewrite app_nil_r in H1.
       exact H1. 
Qed. 

Lemma uop_manger_phase_1_auxiliary_uop_idempotent :
  ∀ X Y,  fst_unique_in_set Y -> [P1AX] nil ([P1AX] Y X) =S= [P1AX] Y X. 
Proof. intros X Y H1.
       assert (H2 := uop_manger_phase_1_auxiliary_preserves_uniqueness X Y H1).
       apply fst_unique_in_set_implies_uop_manger_phase_1_auxiliary_fixpoint; auto. 
Qed. 

Lemma fst_unique_in_empty_set : fst_unique_in_set nil.
Proof. intros a a' p p' H. compute in H. discriminate H. Qed.

Lemma uop_manger_phase_1_uop_idempotent : uop_idempotent _ [EQ] [P1]. 
Proof. intro X. unfold uop_manger_phase_1.
       apply uop_manger_phase_1_auxiliary_uop_idempotent.
       apply fst_unique_in_empty_set. 
Qed. 

Lemma uop_manger_phase_2_uop_idempotent : uop_idempotent _ [EQ] [P2]. 
Proof. intro X. unfold uop_manger_phase_2.  
       apply uop_minset_idempotent.
       - apply refAP. 
       - apply symAP. 
       - apply trnAP. 
       - apply manger_pre_order_congruence. 
       - apply manger_pre_order_reflexive.
Qed.          

End Theory.   
