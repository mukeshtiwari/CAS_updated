From Coq Require Import
     List.
Import ListNotations.
From CAS Require Import
  coq.common.compute
  coq.theory.set
  coq.eqv.properties
  coq.eqv.nat
  coq.eqv.set
  coq.eqv.list
  coq.sg.properties
  coq.sg.or
  coq.sg.and. 


(* congruence wrt list equality *) 
Lemma map_congruence 
          (A B : Type)
          (eqA : brel A)
          (eqB : brel B)
          (f g : A → B)
          (cong : ∀ a a', eqA a a' = true -> eqB (f a) (g a') = true): 
      ∀ (l1 l2 : list A),  (brel_list eqA l1 l2 = true) -> brel_list eqB (map f l1) (map g l2) = true.
 Proof. induction l1. 
          + intros l2 I.  destruct l2. 
            ++ compute. reflexivity.
            ++ compute in I. congruence.
          + intros l2 I. destruct l2.
            ++ compute in I. congruence.
            ++ simpl.
               apply brel_list_cons_elim in I.
               destruct I as [I J]. 
               apply bop_and_intro; auto.
 Qed.

Lemma fold_right_congruence 
          (A B : Type)
          (eqA : brel A)
          (eqB : brel B)
          (f g : B → A → A)
          (cong : ∀ b b' a a', eqB b b' = true -> eqA a a' = true -> eqA (f b a) (g b' a') = true): 
  ∀ (a a' : A) (l l' : list B),
    (eqA a a'= true) ->
      (brel_list eqB l l' = true) ->
        eqA (fold_right f a l) (fold_right g a' l') = true.
 Proof. intros a a'. induction l. 
          + intros l' I J.  destruct l'.
            ++ compute. exact I. 
            ++ compute in J. congruence.
          + intros l' I J. destruct l'.
            ++ compute in J. congruence.
            ++ simpl.
               apply brel_list_cons_elim in J.
               destruct J as [J K]. 
               assert (C := IHl l' I K).
               exact (cong _ _ _ _ J C). 
 Qed.


 (* congruence wrt set equality *) 

   Lemma in_set_map_intro
   (A B : Type)
   (eqA : brel A)
   (eqB : brel B)
   (refA : brel_reflexive A eqA)
   (symA : brel_symmetric A eqA)
   (symB : brel_symmetric B eqB)
   (trnB : brel_transitive B eqB)
   (f : A → B)
   (cong : ∀ a a', eqA a a' = true -> eqB (f a) (f a') = true): 
    ∀ (X : finite_set A) (b : B) ,
      {a' : A & (in_set eqA X a' = true) * (eqB (f a') b = true)} → 
         in_set eqB (map f X) b = true. 
 Proof. induction X; intros b [a' [H1 H2]].
        - compute in H1. discriminate H1. 
        - simpl. apply bop_or_intro.
          apply in_set_cons_elim in H1; auto. 
          destruct H1 as [H1 | H1]. 
          + left. apply symB.
            apply cong in H1.
            exact (trnB _ _ _ H1 H2). 
          + assert (H3 : {a' : A & (in_set eqA X a' = true) * (eqB (f a') b = true)}).
            {
              exists a'; auto.
            }
            right. exact (IHX _ H3). 
 Qed.

 Lemma in_set_map_elim
   (A B : Type)
   (eqA : brel A)
   (eqB : brel B)
   (refA : brel_reflexive A eqA)
   (symA : brel_symmetric A eqA)
   (symB : brel_symmetric B eqB)
   (f : A → B) : 
   ∀ (X : finite_set A) (b : B) ,  
     in_set eqB (map f X) b = true → {a' : A & (in_set eqA X a' = true) * (eqB (f a') b = true)}.
 Proof. induction X; intros b H1.
        - compute in H1. discriminate H1. 
        - simpl in H1. apply bop_or_elim in H1.
          destruct H1 as [H1 | H1]. 
          + exists a. split.
            * apply in_set_cons_intro; auto.
            * apply symB. exact H1.
          + destruct (IHX _ H1) as [a' [H2 H3]].
            exists a'. split; auto. 
            apply in_set_cons_intro; auto.
 Qed.

 Lemma in_set_map_congruence 
          (A B : Type)
          (eqA : brel A)
          (eqB : brel B)
          (f g : A → B)
          (refA : brel_reflexive A eqA)
          (symA : brel_symmetric A eqA)
          (trnA : brel_transitive A eqA)
          (refB : brel_reflexive B eqB)
          (symB : brel_symmetric B eqB)
          (trnB : brel_transitive B eqB)          
          (eqfg: ∀ a a', eqA a a' = true -> eqB (f a) (g a') = true)
          (cong: ∀ a a', eqA a a' = true -> eqB (g a) (g a') = true): 
   ∀ (l1 l2 : finite_set A),  (brel_set eqA l1 l2 = true) ->
                               (∀ a : B, in_set eqB (map f l1) a = true → in_set eqB (map g l2) a = true). 
 Proof. intros l1 l2 H1 b H3. 
        apply brel_set_elim_prop in H1;auto.
        destruct H1 as [H1 H2]. 
        apply (in_set_map_elim _ _ eqA eqB) in H3; auto. 
        destruct H3 as [a [H4 H5]].
        apply (in_set_map_intro _ _ eqA eqB); auto.
        exists a; split.
        + apply H1; auto. 
        + assert (H6 := eqfg _ _ (refA a)). 
          apply symB in H6. exact (trnB _ _ _ H6 H5). 
Qed. 

 
 Lemma map_set_congruence 
          (A B : Type)
          (eqA : brel A)
          (eqB : brel B)
          (f g : A → B)
          (refA : brel_reflexive A eqA)
          (symA : brel_symmetric A eqA)
          (trnA : brel_transitive A eqA)
          (refB : brel_reflexive B eqB)
          (symB : brel_symmetric B eqB)
          (trnB : brel_transitive B eqB)          
          (eqfg: ∀ a a', eqA a a' = true -> eqB (f a) (g a') = true)
          (congg: ∀ a a', eqA a a' = true -> eqB (g a) (g a') = true)
          (congf: ∀ a a' : A, eqA a a' = true → eqB (f a) (f a') = true) : 
      ∀ (l1 l2 : finite_set A),  (brel_set eqA l1 l2 = true) -> brel_set eqB (map f l1) (map g l2) = true.
 Proof. intros l1 l2 H1.
        apply brel_set_intro_prop; auto.
        split. 
        - apply (in_set_map_congruence _ _ eqA eqB f g); auto. 
        - apply (in_set_map_congruence _ _ eqA eqB g f); auto.
          apply brel_set_symmetric; auto. 
Qed. 


Lemma fold_left_set_congruence_simple 
          (A : Type)
          (eqA : brel A)
          (f : A → A → A) : 
  ∀ (a a' : A) (X : finite_set A),
      (eqA a a' = true) ->
        eqA (fold_left f X a) (fold_left f X a') = true.
 Admitted. 

(*
Coq.Lists.List.fold_symmetric :
  ∀ (A : Type) (f : A → A → A),
    (∀ x y z : A, f x (f y z) = f (f x y) z) → 
      ∀ a0 : A, (∀ y : A, f a0 y = f y a0) → 
        ∀ l : list A, fold_left f l a0 = fold_right f a0 l

 *)
Lemma fold_symmetric_with_equality
  (A : Type)
  (eqA : brel A) 
  (b : binary_op A)
  (refA : brel_reflexive A eqA)
  (symA : brel_symmetric A eqA)
  (trnA : brel_transitive A eqA)
  (assoc : bop_associative A eqA b)
  (comm  : bop_commutative A eqA b) : ∀ X a, eqA (fold_left b X a) (fold_right b a X) = true. 
Proof. induction X as [ | a1 l IHX]; intro a. 
       - simpl; auto.
       - assert (H1 := IHX a).
         simpl.
         clear IHX. clear H1. revert a1.
         induction l as [|? ? IHl]; intro a1; simpl. 
         + apply comm.
         + assert (H1 := IHl (b a1 a0)).
           assert (H2 := assoc a a1 a0).
           assert (H3 := assoc a1 a0 (fold_right b a l)).
           assert (H4 : eqA (fold_left b l (b (b a a1) a0)) (fold_left b l (b a (b a1 a0))) = true).
           {
             apply fold_left_set_congruence_simple; auto.
           } 
           assert (H5 := trnA _ _ _ H4 H1). 
           exact (trnA _ _ _ H5 H3). 
  Qed.
Lemma tmp
  (A : Type)
  (eqA : brel A) :  
  ∀ (X Y : finite_set A) (a1 a2 : A),
  eqA a1 a2 = false -> 
  brel_set eqA (a1 :: X) (a2 :: Y) = true ->
  {'(X1, X2, Y1, Y2) & (brel_set eqA X (X1 ++ a2 :: X2) = true) *
                       (brel_set eqA Y (Y1 ++ a1 :: Y2) = true)}. 
  Admitted. 
  
Lemma fold_left_set_congruence 
          (A : Type)
          (eqA : brel A)
          (b : binary_op A)
          (refA : brel_reflexive A eqA): 
  ∀ (X Y : finite_set A) (a a' : A),
    (eqA a a' = true) ->
      (brel_set eqA X Y = true) ->
        eqA (fold_left b X a) (fold_left b Y a') = true.
Proof. 
  induction X as [ | a1 X IHX]; intros Y a a' H0 H1.
       - destruct Y.
         + compute. exact H0.
         + compute in H1. discriminate H1. 
       - destruct Y as [ | a2 Y].
         + compute in H1. discriminate H1. 
         + simpl.
           case_eq(eqA a1 a2); intro H2.
           * admit. (* OK *)
           * assert (H3 := tmp _ eqA _ _ _ _ H2 H1).
             destruct H3 as [[[[X1 X2] Y1] Y2] [H3 H4]].
             admit. 
Admitted. 
(*
fold_left_app: 
∀ (A B : Type) (f : A → B → A) (l l' : list B) (i : A),
    fold_left f (l ++ l') i = fold_left f l' (fold_left f l i)

Lemma fold_right_set_congruence 
  (A : Type)
  (eqA : brel A)
  (b : binary_op A)
  (refA : brel_reflexive A eqA)
  (symA : brel_symmetric A eqA)
  (trnA : brel_transitive A eqA)
  (assoc : bop_associative A eqA b)
  (comm  : bop_commutative A eqA b) : 
  ∀ (a : A) (X Y : finite_set A),
      (brel_set eqA X Y = true) ->
        eqA (fold_right b a X) (fold_right b a Y) = true.
Proof. intros a X Y H1.
       assert (H2 := fold_left_set_congruence A eqA b refA X Y a H1).
       assert (H3 := fold_symmetric_with_equality A eqA b refA symA trnA assoc comm X a). 
       assert (H4 := fold_symmetric_with_equality A eqA b refA symA trnA assoc comm Y a).
       apply symA in H3.
       exact (trnA _ _ _ H3 (trnA _ _ _ H2 H4)).
Qed. 

     Definition sum_fn
               {V : Type}               
               {R : Type}
               (zeroR : R)               
               (plusR : binary_op R)                
               (f : V -> R)
               (row : list V) : R := fold_right plusR zeroR (map f row). 
*)        
(*
  Lemma sum_fn_set_congruence
    (A : Type)
    (eqA : brel A)
    (plus : binary_op A)
    (f g : A -> A)
    (refA : brel_reflexive A eqA)
    (symA : brel_symmetric A eqA)
    (trnA : brel_transitive A eqA)
    (congg : ∀ a0 a' : A, eqA a0 a' = true → eqA (g a0) (g a') = true)
    (congf : ∀ a0 a' : A, eqA a0 a' = true → eqA (f a0) (f a') = true)
    (eqfg : ∀ i j, eqA i j = true -> eqA (f i) (g j) = true):
    ∀ a (l1 l2 : finite_set A),  brel_set eqA l1 l2 = true -> 
          eqA (sum_fn a plus f l1) (sum_fn a plus g l2) = true. 
  Proof. intros a l1 l2 I.
         unfold sum_fn.
         apply (fold_right_set_congruence _ eqA plus).
         apply (map_set_congruence _ _ eqA eqA f g); auto.
  Qed.          
 *) 
