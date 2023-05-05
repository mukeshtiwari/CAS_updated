Require Import Coq.Strings.String.
Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.

Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.eqv.theory.
Require Import CAS.coq.eqv.set.

Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures.
Require Import CAS.coq.sg.theory.
Require Import CAS.coq.sg.cast_up.
Require Import CAS.coq.sg.classify. 
Require Import CAS.coq.sg.and. 
Require Import CAS.coq.sg.union. (* just for in_set_uop_duplicate_elim_elim ? *)

Section Computation.

Definition bop_lift : ∀ {S : Type}, brel S → binary_op S → binary_op(finite_set S) := 
    λ {S} eq bS X Y, uop_duplicate_elim eq (bop_list_product_left bS X Y). 

End Computation.   

Section Theory. 

Variable S  : Type. 
Variable rS : brel S. 
Variable bS : binary_op S. 

Variable refS  : brel_reflexive S rS.    
Variable tranS : brel_transitive S rS. 
Variable symS  : brel_symmetric S rS. 

Variable bcong : bop_congruence S rS bS. 
Variable assS : bop_associative S rS bS. 

(* MOVE *) 
Lemma brel_set_intro_false : ∀ (X Y : finite_set S), 
     {s : S & (in_set rS X s = true) * (in_set rS Y s = false)} → brel_set rS X Y = false. 
Proof. intros X Y [ s [T F]]. 
       case_eq(brel_set rS X Y); intro H. 
          apply brel_set_elim in H. destruct H as [L R]. 
          assert (K := brel_subset_elim S rS symS tranS X Y L s T). 
          rewrite K in F. discriminate. 
          reflexivity. 
Defined.

(* end MOVE *) 

Lemma bop_list_product_nil_left : ∀ (X : finite_set S), bop_list_product_left bS nil X = nil.
Proof. intro X. compute; auto. Qed.

Lemma bop_list_product_nil_right : ∀ (X : finite_set S), bop_list_product_left bS X nil = nil.
Proof. induction X.
       compute; auto.
       unfold bop_list_product_left. fold (@bop_list_product_left S).
       rewrite IHX.
       rewrite List.app_nil_r.
       compute; auto.
Qed.        

Lemma bop_lift_nil_left : ∀ (X : finite_set S), bop_lift rS bS nil X = nil.
Proof. intro X. compute; auto. Qed.

Lemma bop_lift_nil_right : ∀ (X : finite_set S), bop_lift rS bS X nil = nil.
Proof. intro X. unfold bop_lift. rewrite bop_list_product_nil_right. 
       compute; auto.
Qed.        

Lemma bop_lift_nil_is_ann : bop_is_ann (finite_set S) (brel_set rS) (bop_lift rS bS) nil.
Proof. unfold bop_is_ann. intro X. split.
       rewrite bop_lift_nil_left. compute; auto. 
       rewrite bop_lift_nil_right. compute; auto.
Qed.        

Lemma  in_set_ltran_list_product_elim :
  ∀ (a b : S) (Y : finite_set S),
    in_set rS (ltran_list_product bS a Y) b = true ->   
       {y : S & (in_set rS Y y = true) * (rS b (bS a y) = true)}.
Proof. intros a b. induction Y.
       compute. intro F. discriminate F.
       intro H. 
       unfold ltran_list_product in H. fold (@ltran_list_product S) in H.
       apply in_set_cons_elim in H; auto. 
       destruct H as [H | H].
       exists a0. split; auto. 
       compute. rewrite (refS a0); auto. 

       destruct (IHY H) as [y [P1 P2]].
       exists y. split; auto.
       apply in_set_cons_intro; auto. 
Defined.


Lemma  in_set_ltran_list_product_intro :
   ∀ (x y : S) (Y : finite_set S),  
        in_set rS Y y = true -> 
           in_set rS (ltran_list_product bS x Y) (bS x y) = true. 
Proof. intros x y. induction Y.
       compute; auto. 
       intro H. apply in_set_cons_elim in H; auto. destruct H as [H | H].
       unfold ltran_list_product. fold (@ltran_list_product S).
       apply in_set_cons_intro; auto.
       assert (K := IHY H).
       unfold ltran_list_product. fold (@ltran_list_product S).       
       apply in_set_cons_intro; auto.
Qed. 

Lemma  in_set_list_product_elim :
 ∀ (a : S) (X Y : finite_set S),  in_set rS (bop_list_product_left bS X Y) a = true ->   
       {x : S & {y : S & (in_set rS X x = true) * (in_set rS Y y = true) * (rS a (bS x y) = true)}}.
Proof. intro a. induction X; induction Y. 
       compute. intro F. discriminate F.
       simpl. intro F. discriminate F.
       simpl. rewrite bop_list_product_nil_right. simpl. intro F. discriminate F.
       unfold bop_list_product_left. fold (@bop_list_product_left S).
       intro H.
       apply in_set_concat_elim in H; auto. destruct H as [H | H].
          destruct (in_set_ltran_list_product_elim a0 a _ H) as [y [Q1 Q2]].
          exists a0; exists y. split; auto. split; auto.
          apply in_set_cons_intro; auto.
          
          destruct (IHX _ H) as [x [y [[P1 P2] P3]]].
          exists x; exists y. split; auto. split; auto. 
          apply in_set_cons_intro; auto. 
Defined.        


Lemma  in_set_list_product_intro :
   ∀ (X Y : finite_set S),  ∀ (x y : S), 
        in_set rS X x = true -> 
        in_set rS Y y = true -> 
           in_set rS (bop_list_product_left bS X Y) (bS x y) = true. 
Proof. induction X. 
       intros Y x y H1 H2. compute in H1. discriminate.
       intros Y x y H1 H2.
       unfold bop_list_product_left. fold (@bop_list_product_left S).
       apply in_set_concat_intro.
       destruct (in_set_cons_elim _ _ symS _ _ _ H1) as [J | J].

       left. assert (N : rS (bS a y) (bS x y) = true). apply bcong. apply symS; auto. apply refS.
       assert (M := in_set_right_congruence _ _ symS tranS _ _ (ltran_list_product bS a Y) N).
       apply M. 
       apply in_set_ltran_list_product_intro; auto. 

       right. apply IHX; auto.
Defined.        

          
Lemma  in_set_bop_lift_elim :
 ∀ (X Y : finite_set S),  ∀ (a : S), 
  in_set rS (bop_lift rS bS X Y) a = true -> 
   {x : S & {y : S & (in_set rS X x = true) * (in_set rS Y y = true) * (rS a (bS x y) = true)}}.
Proof. intros X Y a H. 
       unfold bop_lift in H.
       apply in_set_uop_duplicate_elim_elim in H.
       apply in_set_list_product_elim; auto. 
Defined. 

Lemma  in_set_bop_lift_intro :
   ∀ (X Y : finite_set S),  ∀ (x y : S), 
        in_set rS X x = true -> 
        in_set rS Y y = true -> 
           in_set rS (bop_lift rS bS X Y) (bS x y) = true. 
Proof. intros X Y x y H1 H2. 
       unfold bop_lift.
       apply in_set_uop_duplicate_elim_intro; auto.
       apply in_set_list_product_intro; auto.        
Qed.

Lemma  in_set_bop_lift_intro_v2 :
   ∀ (X Y : finite_set S),  ∀ (a x y : S), 
        in_set rS X x = true -> 
        in_set rS Y y = true ->
        rS a (bS x y) = true -> 
           in_set rS (bop_lift rS bS X Y) a = true. 
Proof. intros X Y a x y H1 H2 H3. 
       unfold bop_lift.
       apply in_set_uop_duplicate_elim_intro; auto.
       apply symS in H3. assert (M := in_set_right_congruence _ _ symS tranS _ _ (bop_list_product_left bS X Y) H3).
       apply M. 
       apply in_set_list_product_intro; auto.        
Qed. 


Lemma  lift_lemma_1 : 
   ∀ (a : S) (s t u : finite_set S) ,
   in_set rS (bop_lift rS bS (bop_lift rS bS s t) u) a = true
   → in_set rS (bop_lift rS bS s (bop_lift rS bS t u)) a = true.
Proof. intro a. induction s.
       intros t u H. compute in H. discriminate H. 
       induction t. 
       intros u H. rewrite bop_lift_nil_right in H. compute in H. discriminate H.  
       induction u.
       rewrite bop_lift_nil_right. simpl. intro F. discriminate F.
       intro H.
       apply in_set_bop_lift_elim in H.
       destruct H as [x [y [[P1 P2] P3]]].
       apply in_set_bop_lift_elim in P1.
       destruct  P1 as [z [w [[Q1 Q2] Q3]]].
       apply in_set_cons_elim in Q1; auto.
       apply in_set_cons_elim in Q2; auto.
       apply in_set_cons_elim in P2; auto.
       assert (K : rS (bS z (bS w y)) a = true).
          assert (J1 : rS (bS (bS z w) y) (bS z (bS w y))  = true). apply assS.
          assert (J2 : rS (bS x y) (bS (bS z w) y)  = true). apply (bcong _ _ _ _ Q3 (refS y)).
          assert (J3 := tranS _ _ _ J2 J1).
          assert (J4 := tranS _ _ _ P3 J3).
          apply symS. exact J4. 
       apply (in_set_right_congruence _ _ symS tranS _ _ (bop_lift rS bS (a0 :: s) (bop_lift rS bS (a1 :: t) (a2 :: u))) K).
       destruct Q1 as [Q1 | Q1]; destruct Q2 as [Q2 | Q2]; destruct P2 as [P2 | P2].
       apply in_set_bop_lift_intro.
       apply in_set_cons_intro; auto.
       apply in_set_bop_lift_intro.
       apply in_set_cons_intro; auto.
       apply in_set_cons_intro; auto.

       apply in_set_bop_lift_intro.
       apply in_set_cons_intro; auto.
       apply in_set_bop_lift_intro.
       apply in_set_cons_intro; auto.
       apply in_set_cons_intro; auto.

       apply in_set_bop_lift_intro.
       apply in_set_cons_intro; auto.
       apply in_set_bop_lift_intro.
       apply in_set_cons_intro; auto.
       apply in_set_cons_intro; auto.

       apply in_set_bop_lift_intro.
       apply in_set_cons_intro; auto.
       apply in_set_bop_lift_intro.
       apply in_set_cons_intro; auto.
       apply in_set_cons_intro; auto.

       apply in_set_bop_lift_intro.
       apply in_set_cons_intro; auto.
       apply in_set_bop_lift_intro.
       apply in_set_cons_intro; auto.
       apply in_set_cons_intro; auto.

       apply in_set_bop_lift_intro.
       apply in_set_cons_intro; auto.
       apply in_set_bop_lift_intro.
       apply in_set_cons_intro; auto.
       apply in_set_cons_intro; auto.

       apply in_set_bop_lift_intro.
       apply in_set_cons_intro; auto.
       apply in_set_bop_lift_intro.
       apply in_set_cons_intro; auto.
       apply in_set_cons_intro; auto.

       apply in_set_bop_lift_intro.
       apply in_set_cons_intro; auto.
       apply in_set_bop_lift_intro.
       apply in_set_cons_intro; auto.
       apply in_set_cons_intro; auto.       
Qed.        


Lemma  lift_lemma_2 : 
   ∀ (a : S) (s t u : finite_set S) ,
   in_set  rS (bop_lift rS bS s (bop_lift rS bS t u)) a = true
    → in_set  rS (bop_lift rS bS (bop_lift rS bS s t) u) a = true. 
Proof. intro a. induction s.
       intros t u H. compute in H. discriminate H. 
       induction t. 
       intros u H. rewrite bop_lift_nil_left in H. rewrite bop_lift_nil_right in H. compute in H. discriminate H.  
       induction u.
       rewrite bop_lift_nil_right. rewrite bop_lift_nil_right. simpl. intro F. discriminate F.
       intro H.
       apply in_set_bop_lift_elim in H.
       destruct H as [x [y [[P1 P2] P3]]].
       apply in_set_bop_lift_elim in P2.
       destruct  P2 as [z [w [[Q1 Q2] Q3]]].
       apply in_set_cons_elim in Q1; auto.
       apply in_set_cons_elim in Q2; auto.
       apply in_set_cons_elim in P1; auto.
       assert (K : rS (bS (bS x z) w) a = true).
          assert (J1 : rS (bS (bS x z) w) (bS x (bS z w))  = true). apply assS.
          assert (J2 : rS (bS x y) (bS x (bS z w))  = true). apply (bcong _ _ _ _ (refS x) Q3).
          apply symS in J1. assert (J3 := tranS _ _ _ J2 J1).
          assert (J4 := tranS _ _ _ P3 J3).
          apply symS. exact J4. 
       apply (in_set_right_congruence _ _ symS tranS _ _ (bop_lift rS bS (bop_lift rS bS (a0 :: s) (a1 :: t)) (a2 :: u)) K).
       destruct Q1 as [Q1 | Q1]; destruct Q2 as [Q2 | Q2]; destruct P1 as [P1 | P1].
       apply in_set_bop_lift_intro.
       apply in_set_bop_lift_intro.       
       apply in_set_cons_intro; auto.
       apply in_set_cons_intro; auto.
       apply in_set_cons_intro; auto.

       apply in_set_bop_lift_intro.
       apply in_set_bop_lift_intro.       
       apply in_set_cons_intro; auto.
       apply in_set_cons_intro; auto.
       apply in_set_cons_intro; auto.

       apply in_set_bop_lift_intro.
       apply in_set_bop_lift_intro.       
       apply in_set_cons_intro; auto.
       apply in_set_cons_intro; auto.
       apply in_set_cons_intro; auto.

       apply in_set_bop_lift_intro.
       apply in_set_bop_lift_intro.       
       apply in_set_cons_intro; auto.
       apply in_set_cons_intro; auto.
       apply in_set_cons_intro; auto.

       apply in_set_bop_lift_intro.
       apply in_set_bop_lift_intro.       
       apply in_set_cons_intro; auto.
       apply in_set_cons_intro; auto.
       apply in_set_cons_intro; auto.

       apply in_set_bop_lift_intro.
       apply in_set_bop_lift_intro.       
       apply in_set_cons_intro; auto.
       apply in_set_cons_intro; auto.
       apply in_set_cons_intro; auto.

       apply in_set_bop_lift_intro.
       apply in_set_bop_lift_intro.       
       apply in_set_cons_intro; auto.
       apply in_set_cons_intro; auto.
       apply in_set_cons_intro; auto.

       apply in_set_bop_lift_intro.
       apply in_set_bop_lift_intro.       
       apply in_set_cons_intro; auto.
       apply in_set_cons_intro; auto.
       apply in_set_cons_intro; auto.       
Qed.        


Lemma bop_lift_associative : bop_associative (finite_set S) (brel_set rS) (bop_lift rS bS). 
Proof. intros s t u. 
       apply brel_set_intro. 
       split; apply brel_subset_intro; auto.
       intro a. apply lift_lemma_1.
       intro a. apply lift_lemma_2.       
Qed. 

Lemma bop_lift_subset :   ∀ (X1 X2 Y1 Y2 : finite_set S),  
  brel_subset rS X1 Y1 = true -> 
  brel_subset rS X2 Y2 = true -> 
      brel_subset rS (bop_lift rS bS X1 X2) (bop_lift rS bS Y1 Y2) = true. 
Proof. intros X1 X2 Y1 Y2 H1 H2.
       apply brel_subset_intro; auto.
       assert (K1 := brel_subset_elim _ _ symS tranS _ _ H1); auto.
       assert (K2 := brel_subset_elim _ _ symS tranS _ _ H2); auto.       
       intros a J.
       apply in_set_bop_lift_elim in J; auto. destruct J as [x [y [[P1 P2] P3]]].
       apply symS in P3. assert (M := in_set_right_congruence _ _ symS tranS _ _ (bop_lift rS bS Y1 Y2) P3).
       apply M. 
       apply in_set_bop_lift_intro; auto.        
Qed. 

Lemma bop_lift_congruence : bop_congruence (finite_set S) (brel_set rS) (bop_lift rS bS). 
Proof. unfold bop_congruence. intros X1 X2 Y1 Y2 H1 H2. 
       apply brel_set_elim in H1. apply brel_set_elim in H2. 
       destruct H1 as [L1 R1]. destruct H2 as [L2 R2]. 
       apply brel_set_intro. 
       split; apply bop_lift_subset; auto. 
Qed. 


Lemma bop_lift_subset_commutative : 
     bop_commutative S rS bS -> ∀ (X Y : finite_set S), brel_subset rS (bop_lift rS bS X Y) (bop_lift rS bS Y X) = true.
Proof. intros comm X Y. 
       apply brel_subset_intro; auto. 
       intros a H.
       apply in_set_bop_lift_elim in H.
       destruct H as [x [y [[P1 P2] P3]]].
       assert (C := comm x y).
       assert (D := tranS _ _ _ P3 C).
       apply symS in D.       
       assert (M := in_set_right_congruence _ _ symS tranS _ _ (bop_lift rS bS Y X) D).
       apply M. 
       apply in_set_bop_lift_intro; auto.
Qed.        
  
Lemma bop_lift_commutative : 
     bop_commutative S rS bS -> bop_commutative (finite_set S) (brel_set rS) (bop_lift rS bS). 
Proof. unfold bop_commutative. intros commS X Y. 
       apply brel_set_intro. 
       split; apply bop_lift_subset_commutative; auto. 
Qed. 

Lemma bop_lift_not_commutative : 
     bop_not_commutative S rS bS -> bop_not_commutative (finite_set S) (brel_set rS) (bop_lift rS bS). 
Proof. intros [[x y] P]. exists ((x :: nil), (y :: nil)). compute. rewrite P; auto. Defined. 


Lemma bop_lift_exists_ann : bop_exists_ann (finite_set S) (brel_set rS) (bop_lift rS bS). 
Proof. exists nil. apply bop_lift_nil_is_ann. Defined. 

Lemma bop_lift_is_id (i : S) : bop_is_id S rS bS i  -> bop_is_id (finite_set S) (brel_set rS) (bop_lift rS bS) (i :: nil).
Proof. intros P X.
       split. 

       apply brel_set_intro.
       split.

       apply brel_subset_intro; auto.
       intros a H. apply in_set_bop_lift_elim in H.
       destruct H as [x [y [[P1 P2] P3]]].
       assert (T : rS y a = true). 
           compute in P1. case_eq(rS x i); intro J.
           destruct (P y) as [L R].
           assert (K1 := bcong _ _ _ _ J (refS y)).
           assert (K2 := tranS _ _ _ P3 K1).
           assert (K3 := tranS _ _ _ K2 L).
           apply symS in K3. exact K3.
           rewrite J in P1. discriminate P1. 
       assert (M := in_set_right_congruence _ _ symS tranS _ _ X T).
       apply M; auto. 

       apply brel_subset_intro; auto.
       intros a H.
       destruct (P a) as [L R].
       assert (M := in_set_right_congruence _ _ symS tranS _ _ (bop_lift rS bS (i :: nil) X) L).
       apply M.
       apply in_set_bop_lift_intro; auto.
       compute. rewrite refS; auto.

       apply brel_set_intro.
       split.
       
       apply brel_subset_intro; auto.
       intros a H. apply in_set_bop_lift_elim in H.
       destruct H as [x [y [[P1 P2] P3]]].
       assert (T : rS x a = true). 
           compute in P2. case_eq(rS y i); intro J.
           destruct (P x) as [L R].
           assert (K1 := bcong _ _ _ _ (refS x) J).
           assert (K2 := tranS _ _ _ P3 K1).
           assert (K3 := tranS _ _ _ K2 R).
           apply symS in K3. exact K3.
           rewrite J in P2. discriminate P2. 
       assert (M := in_set_right_congruence _ _ symS tranS _ _ X T).
       apply M; auto.

       apply brel_subset_intro; auto.
       intros a H.
       destruct (P a) as [L R].
       assert (M := in_set_right_congruence _ _ symS tranS _ _ (bop_lift rS bS X (i :: nil)) R).
       apply M.
       apply in_set_bop_lift_intro; auto.
       compute. rewrite refS; auto.
Qed.        

Lemma bop_lift_exists_id : bop_exists_id S rS bS  -> bop_exists_id (finite_set S) (brel_set rS) (bop_lift rS bS). 
Proof. intros [i P]. exists (i :: nil). apply bop_lift_is_id; auto. Defined. 

Lemma bop_list_product_left_contains_product : ∀ (a b : S) (X Y : finite_set S), in_set rS (bop_list_product_left bS (a :: X) (b :: Y)) (bS a b) = true.
Proof. intros a b X Y.
       unfold bop_list_product_left. fold (@bop_list_product_left (finite_set S)).
       unfold ltran_list_product. fold (@ltran_list_product S).
       apply in_set_concat_intro. left.
       apply in_set_cons_intro; auto. 
Qed.


Lemma bop_lift_contains_product : ∀ (a b : S) (X Y : finite_set S), in_set rS (bop_lift rS bS (a :: X) (b :: Y)) (bS a b) = true.
Proof. intros a b X Y.
       unfold  bop_lift.
       apply in_set_uop_duplicate_elim_intro; auto.
       apply bop_list_product_left_contains_product; auto. 
Qed. 


Lemma bop_lift_not_exists_id (s : S) (H : bop_not_exists_id S rS bS) :
  bop_not_exists_id (finite_set S) (brel_set rS) (bop_lift rS bS). 
Proof. intro X.
       destruct X.
       - exists (s :: nil). compute; auto.
       - destruct (H s0) as [u [G | G]].
         + exists (u :: nil). left.  
           case_eq(brel_set rS (bop_lift rS bS (s0 :: X) (u :: nil)) (u :: nil) ); intro K; auto.
           apply brel_set_elim_prop in K; auto. destruct K as [J1 J2]. 
           assert (K3 : in_set rS (u :: nil) (bS s0 u) = true).
           {
             apply J1. 
             apply bop_lift_contains_product.
           }
           apply in_set_singleton_elim in K3; auto. 
           apply symS in K3. 
           rewrite K3 in G. discriminate G. 
         + exists (u :: nil). right.
           case_eq(brel_set rS (bop_lift rS bS (u :: nil) (s0 :: X)) (u :: nil)); intro K; auto.
           apply brel_set_elim_prop in K; auto. destruct K as [J1 J2]. 
           assert (K3 : in_set rS (u :: nil) (bS u s0) = true).
           {
             apply J1. 
             apply bop_lift_contains_product.
           } 
           apply in_set_singleton_elim in K3; auto. 
           apply symS in K3. 
           rewrite K3 in G. discriminate G. 
Defined.        

Lemma bop_lift_not_idempotent : 
    bop_not_selective S rS bS -> 
    bop_not_idempotent (finite_set S) (brel_set rS) (bop_lift rS bS). 
Proof. intros nsel. exists ((fst (projT1 nsel)) :: (snd (projT1 nsel)) :: nil).
       destruct nsel as [[a b] [L R]]. simpl. 
       apply brel_set_intro_false. 
       exists (bS a b). split.
       apply in_set_bop_lift_intro.
       apply in_set_cons_intro; auto. 
       apply in_set_cons_intro; auto. right. apply in_set_cons_intro; auto. 
       compute. rewrite L. rewrite R; auto. 
Defined. 

Lemma bop_lift_idempotent : 
    bop_selective S rS bS -> 
    bop_idempotent (finite_set S) (brel_set rS) (bop_lift rS bS). 
Proof. intros selS X.
       apply brel_set_intro; auto. split; apply brel_subset_intro; auto. 

       intros a H.
       apply in_set_bop_lift_elim in H.
       destruct H as [x [y [[P1 P2] P3]]].
       destruct (selS x y) as [L | R].
       assert (K := tranS _ _ _ P3 L). 
       apply symS in K. assert (M := in_set_right_congruence _ _ symS tranS _ _ X K).
       apply M. exact P1. 
       assert (K := tranS _ _ _ P3 R). 
       apply symS in K. assert (M := in_set_right_congruence _ _ symS tranS _ _ X K).
       apply M. exact P2. 
      

       intros a H.
       assert (K : rS (bS a a) a = true). 
          destruct (selS a a) as [L | R]; auto. 
       assert (M := in_set_right_congruence _ _ symS tranS _ _ (bop_lift rS bS X X) K).
       apply M.  apply in_set_bop_lift_intro; auto. 
 Defined.

Lemma bop_lift_not_is_left (s : S) : bop_not_is_left (finite_set S) (brel_set rS) (bop_lift rS bS).
Proof. exists (s :: nil, nil). compute; auto. Defined. 


Lemma bop_lift_not_is_right (s : S) : bop_not_is_right (finite_set S) (brel_set rS) (bop_lift rS bS).
Proof. exists (nil, s :: nil). compute; auto. Defined. 

Lemma bop_lift_not_anti_left : bop_not_anti_left (finite_set S) (brel_set rS) (bop_lift rS bS).
Proof. exists (nil, nil). compute; auto. Defined. 

Lemma bop_lift_not_anti_right : bop_not_anti_right (finite_set S) (brel_set rS) (bop_lift rS bS).
Proof. exists (nil, nil). compute; auto. Defined. 

Lemma bop_lift_not_left_constant (s : S) : bop_not_left_constant (finite_set S) (brel_set rS) (bop_lift rS bS).
Proof. exists (s :: nil, (s :: nil, nil)). compute; auto. Defined. 

Lemma bop_lift_not_right_constant (s : S) : bop_not_right_constant (finite_set S) (brel_set rS) (bop_lift rS bS).
Proof. exists (s :: nil, (s :: nil, nil)). compute; auto. Defined. 


Lemma bop_lift_not_left_cancellative (s : S) (f : S -> S) (ntS : brel_not_trivial S rS f) :
         bop_not_left_cancellative (finite_set S) (brel_set rS) (bop_lift rS bS).
Proof. exists (nil, (s :: nil, (f s) :: nil)).
       destruct (ntS s) as [L R].
       compute; auto.
       rewrite L; auto. 
Defined. 

Lemma bop_lift_not_right_cancellative (s : S) (f : S -> S) (ntS : brel_not_trivial S rS f) :
        bop_not_right_cancellative (finite_set S) (brel_set rS) (bop_lift rS bS).
Proof. exists (nil, (s :: nil, (f s) :: nil)).
       destruct (ntS s) as [L R].
       compute; auto.
       rewrite L; auto. 
Defined. 


(* selectivity *)

Lemma ltran_list_product_is_left_elim : bop_is_left S rS bS ->   ∀ (a b : S) (X : finite_set S),
  in_set rS (ltran_list_product bS a X) b = true -> rS a b = true. 
Proof. intros IL a b X H. induction X. compute in H. discriminate H. 
       unfold ltran_list_product in H. fold (@ltran_list_product S) in H.
       apply in_set_cons_elim in H; auto.
       destruct H as [H | H].
       assert (K := IL a a0). apply symS in K. apply (tranS _ _ _ K H). 
       apply IHX; auto.
Qed. 


Lemma bop_list_product_is_left_elim : bop_is_left S rS bS ->   ∀ (a : S) (X Y : finite_set S),
  in_set rS (bop_list_product_left bS X Y) a = true -> in_set rS X a = true. 
Proof. intros IL a X Y H. induction X. compute in H. discriminate H. 
       apply in_set_cons_intro; auto.   
       unfold bop_list_product_left in H. fold (@bop_list_product_left S) in H.
       apply in_set_concat_elim in H; auto. 
       destruct H as [H | H].
       assert (K := ltran_list_product_is_left_elim IL a0 a Y H). 
       left; auto.
       right. apply IHX; auto.
Qed.



Lemma ltran_list_product_is_left_intro : bop_is_left S rS bS ->  ∀ (a b : S) (X : finite_set S),
      rS a b = true ->
      brel_set rS nil X = false -> in_set rS (ltran_list_product bS a X) b = true.
Proof. intros IL a b X E F.
       destruct X. 
       compute in F. discriminate F.
       unfold ltran_list_product. fold (@ltran_list_product S).       
       apply in_set_cons_intro; auto.
       left. assert (K := IL a s). apply (tranS _ _ _ K E). 
Qed.

Lemma ltran_list_product_is_right_intro : bop_is_right S rS bS ->  ∀ (a b c : S) (X : finite_set S),
      rS b c = true -> in_set rS (ltran_list_product bS a (b :: X)) c = true.
Proof. intros IR a b c X E.
       unfold ltran_list_product. fold (@ltran_list_product S).       
       apply in_set_cons_intro; auto.
       left. assert (K := IR a b). apply (tranS _ _ _ K E). 
Qed.

Lemma bop_list_product_is_left_intro : bop_is_left S rS bS ->   ∀ (a : S) (X Y : finite_set S),
  in_set rS X a = true -> (brel_set rS nil Y = false) -> (in_set rS (bop_list_product_left bS X Y) a = true). 
Proof. intros IL a X Y H1 H2. induction X. compute in H1. discriminate H1.
       apply in_set_cons_elim in H1; auto. 
       destruct H1 as [H1 | H1].
       unfold bop_list_product_left. fold (@bop_list_product_left S).
       apply in_set_concat_intro; auto.
       left. apply (ltran_list_product_is_left_intro IL a0 a Y H1 H2). 
       assert (K := IHX H1).
       unfold bop_list_product_left. fold (@bop_list_product_left S).
       apply in_set_concat_intro; auto.
Qed. 

Lemma bop_list_product_is_right_intro : bop_is_right S rS bS ->   ∀ (a : S) (X Y : finite_set S),
  in_set rS Y a = true -> (brel_set rS nil X = false) -> (in_set rS (bop_list_product_left bS X Y) a = true). 
Proof. intros IR a X Y H1 H2. induction Y. compute in H1. discriminate H1.
       apply in_set_cons_elim in H1; auto. 
       destruct H1 as [H1 | H1].
       destruct X.
       compute in H2. discriminate H2. 
       unfold bop_list_product_left. fold (@bop_list_product_left S).
       apply in_set_concat_intro; auto.
       left. apply (ltran_list_product_is_right_intro IR s a0 a Y H1). 
       assert (K := IHY H1).
       apply in_set_list_product_elim in K.
       destruct K as [x [y [[P1 P2] P3]]].
       apply symS in P3. assert (M := in_set_right_congruence _ _ symS tranS _ _ (bop_list_product_left bS X (a0 :: Y)) P3).
       apply M. 
       apply in_set_list_product_intro; auto. 
       apply in_set_cons_intro; auto.
Qed. 


Lemma ltran_list_product_is_right_elim : bop_is_right S rS bS ->   ∀ (a b : S) (X : finite_set S),
      in_set rS (ltran_list_product bS a X) b = true -> {c : S & (in_set rS X c = true) * (rS c b = true)}.
Proof. intros IR a b X. 
       induction X. intro H. 
       compute in H. discriminate H. 
       intro H. unfold ltran_list_product in H. fold (@ltran_list_product S) in H.
       apply in_set_cons_elim in H; auto.
       destruct H as [H | H].
       exists a0. split. 
       compute. rewrite refS; auto.
       assert (K := IR a a0). apply symS in K. apply (tranS _ _ _ K H). 
       destruct (IHX H) as [c [P Q]].
       exists c. split; auto.
       apply in_set_cons_intro; auto. 
Qed. 

Lemma bop_list_product_is_right_elim : bop_is_right S rS bS ->   ∀ (a : S) (X Y : finite_set S),
  in_set rS (bop_list_product_left bS X Y) a = true -> in_set rS Y a = true. 
Proof. intros IL a X Y H. induction X. 
       compute in H. discriminate H.
       unfold bop_list_product_left in H. fold (@bop_list_product_left S) in H.
       apply in_set_concat_elim in H; auto. 
       destruct H as [H | H].
       apply ltran_list_product_is_right_elim in H; auto. destruct H as [c [P Q]].
       apply (in_set_right_congruence _ _ symS tranS _ _ _ Q P). 
       apply IHX; auto. 
Qed.        


Lemma bop_lift_selective_v1 : bop_is_left S rS bS -> bop_selective (finite_set S) (brel_set rS) (bop_lift rS bS).
Proof. unfold bop_is_left. unfold bop_selective.
       intros L X Y.
       assert (refSet := brel_set_reflexive _ _ refS symS).
       assert (tranSet := brel_set_transitive _ _ refS symS tranS).
       assert (congSet := brel_set_congruence _ _ refS symS tranS).               

       case_eq(brel_set rS nil X); intro J1; case_eq(brel_set rS nil Y); intro J2.
       left. assert (K1 : brel_set rS nil (bop_lift rS bS nil nil)= true). compute; auto. 
             assert (K2 := bop_lift_congruence _ _ _ _ J1 J2).  
             assert (K3 := tranSet _ _ _ K1 K2).
             assert (K4 := congSet _ _ _ _ K3 (refSet X)).
             rewrite <- K4. exact J1. 
       left. assert (K1 : brel_set rS nil (bop_lift rS bS nil Y)= true). compute; auto. 
             assert (K2 := bop_lift_congruence _ _ _ _ J1 (refSet Y)).  
             assert (K3 := tranSet _ _ _ K1 K2).
             assert (K4 := congSet _ _ _ _ K3 (refSet X)).
             rewrite <- K4. exact J1. 
       right. assert (K1 : brel_set rS nil (bop_lift rS bS X nil)= true). rewrite bop_lift_nil_right.  compute; auto. 
             assert (K2 := bop_lift_congruence _ _ _ _ (refSet X) J2).  
             assert (K3 := tranSet _ _ _ K1 K2).
             assert (K4 := congSet _ _ _ _ K3 (refSet Y)).
             rewrite <- K4. exact J2. 
       left.
       apply brel_set_intro. split; apply brel_subset_intro; auto.

       intros a H. apply in_set_bop_lift_elim in H.
       destruct H as [x [y [[P1 P2] P3]]].
       assert (K1 := L x y).
       assert (K2 := tranS _ _ _ P3 K1).
       apply symS in K2. assert (M := in_set_right_congruence _ _ symS tranS _ _ X K2).
       apply M; auto.


       intros a H.
       unfold bop_lift. 
       apply in_set_dup_elim_intro; auto.
       apply bop_list_product_is_left_intro; auto. 
Qed. 


Lemma bop_lift_selective_v2 : bop_is_right S rS bS -> bop_selective (finite_set S) (brel_set rS) (bop_lift rS bS).
Proof. unfold bop_is_right. unfold bop_selective.
       intros R X Y.
       assert (refSet := brel_set_reflexive _ _ refS symS).
       assert (tranSet := brel_set_transitive _ _ refS symS tranS).
       assert (congSet := brel_set_congruence _ _ refS symS tranS).               
       
       case_eq(brel_set rS nil X); intro J1; case_eq(brel_set rS nil Y); intro J2.
       left. assert (K1 : brel_set rS nil (bop_lift rS bS nil nil)= true). compute; auto. 
             assert (K2 := bop_lift_congruence _ _ _ _ J1 J2).  
             assert (K3 := tranSet _ _ _ K1 K2).
             assert (K4 := congSet _ _ _ _ K3 (refSet X)).
             rewrite <- K4. exact J1. 
       left. assert (K1 : brel_set rS nil (bop_lift rS bS nil Y)= true). compute; auto. 
             assert (K2 := bop_lift_congruence _ _ _ _ J1 (refSet Y)).  
             assert (K3 := tranSet _ _ _ K1 K2).
             assert (K4 := congSet _ _ _ _ K3 (refSet X)).
             rewrite <- K4. exact J1. 
       right. assert (K1 : brel_set rS nil (bop_lift rS bS X nil)= true). rewrite bop_lift_nil_right.  compute; auto. 
             assert (K2 := bop_lift_congruence _ _ _ _ (refSet X) J2).  
             assert (K3 := tranSet _ _ _ K1 K2).
             assert (K4 := congSet _ _ _ _ K3 (refSet Y)).
             rewrite <- K4. exact J2. 
       right. 
       apply brel_set_intro. split; apply brel_subset_intro; auto.

       intros a H. apply in_set_bop_lift_elim in H.
       destruct H as [x [y [[P1 P2] P3]]].
       assert (K1 := R x y).
       assert (K2 := tranS _ _ _ P3 K1).
       apply symS in K2. assert (M := in_set_right_congruence _ _ symS tranS _ _ Y K2).
       apply M; auto.


       intros a H.
       unfold bop_lift. 
       apply in_set_dup_elim_intro; auto.
       apply bop_list_product_is_right_intro; auto. 
Qed. 


Lemma brel_set_exactly_two_implies_four_subsets : ∀ (s t : S), exactly_two S rS s t -> ∀ (X : finite_set S),
      (brel_set rS X nil = true) +
      (brel_set rS X (s :: nil) = true) +
      (brel_set rS X (t :: nil) = true) +
      (brel_set rS X (s :: t :: nil) = true).
Proof. intros s t et X.
       destruct et as [L R]. 
       induction X.
       left. left. left. compute; auto. 
       destruct IHX as [[[H1 | H2] | H3] | H4]. 

       destruct (R a) as [J | J]. 
       left. left. right.
       apply brel_set_intro; split; apply brel_subset_intro; auto.
       intros x H. apply in_set_cons_intro; auto. apply in_set_cons_elim in H; auto. 
       destruct H as [H | H].
       left. apply (tranS _ _ _ J H).
       right.  apply (in_set_left_congruence_v3 _ _ symS tranS _ _ _ H1 H).
       intros x H. apply in_set_cons_intro; auto. apply in_set_cons_elim in H; auto.
       destruct H as [H | H].
       left. apply symS in J. apply (tranS _ _ _ J H).
       right. apply brel_set_symmetric in H1; auto.
       apply (in_set_left_congruence_v3 _ _ symS tranS _ _ _ H1 H).
       left. right. 
       apply brel_set_intro; split; apply brel_subset_intro; auto.
       intros x H. apply in_set_cons_intro; auto. apply in_set_cons_elim in H; auto. 
       destruct H as [H | H].
       left. apply (tranS _ _ _ J H).
       right. apply (in_set_left_congruence_v3 _ _ symS tranS  _ _ _ H1 H). 
       intros x H. apply in_set_cons_intro; auto. apply in_set_cons_elim in H; auto.
       destruct H as [H | H].
       left. apply symS in J. apply (tranS _ _ _ J H).
       right. apply brel_set_symmetric in H1; auto.
       apply (in_set_left_congruence_v3 _ _ symS tranS  _ _ _ H1 H). 
           
       
       destruct (R a) as [J | J].
       left. left. right.
       apply brel_set_intro; split; apply brel_subset_intro; auto.
       intros x H. apply in_set_cons_intro; auto. apply in_set_cons_elim in H; auto. 
       destruct H as [H | H].
       left. apply (tranS _ _ _ J H).
       left. assert (K := in_set_left_congruence_v3 _ _ symS tranS  _ _ _ H2 H). compute in K. case_eq(rS x s); intro F.
       apply symS. exact F. rewrite F in K. discriminate K. 
       intros x H. apply in_set_cons_intro; auto. apply in_set_cons_elim in H; auto.
       destruct H as [H | H].
       left. apply symS in J. apply (tranS _ _ _ J H).
       compute in H. discriminate H. 
       right.
       apply brel_set_intro; split; apply brel_subset_intro; auto.
       intros x H. apply in_set_cons_intro; auto. apply in_set_cons_elim in H; auto. 
       destruct H as [H | H].
       right. apply in_set_cons_intro; auto. left. apply (tranS _ _ _ J H).
       left. assert (K := in_set_left_congruence_v3 _ _ symS tranS  _ _ _ H2 H). compute in K. case_eq(rS x s); intro F.
       apply symS. exact F. rewrite F in K. discriminate K. 
       intros x H. apply in_set_cons_intro; auto. apply in_set_cons_elim in H; auto.
       destruct H as [H | H].
       right. apply symS in H. rewrite (in_set_congruence _ _ symS tranS _ _ _ _ H2 H). compute. rewrite refS; auto. 
       left. compute in H. case_eq(rS x t); intro F. apply symS. apply (tranS _ _ _ F J).  rewrite F in H. discriminate H.

       destruct (R a) as [J | J].
       right.
       apply brel_set_intro; split; apply brel_subset_intro; auto.
       intros x H. apply in_set_cons_intro; auto. apply in_set_cons_elim in H; auto. 
       destruct H as [H | H].
       left. apply (tranS _ _ _ J H).
       right.  assert (K := in_set_left_congruence_v3 _ _ symS tranS  _ _ _ H3 H). exact K. 
       intros x H. apply in_set_cons_intro; auto. apply in_set_cons_elim in H; auto.
       destruct H as [H | H].
       left. apply symS in J. apply (tranS _ _ _ J H).
       right. apply brel_set_symmetric in H3; auto. apply (in_set_left_congruence_v3 _ _ symS tranS  _ _ _ H3 H). 
       left. right. 
       apply brel_set_intro; split; apply brel_subset_intro; auto.
       intros x H. apply in_set_cons_intro; auto. apply in_set_cons_elim in H; auto. 
       destruct H as [H | H].
       left. apply (tranS _ _ _ J H). 
       left. assert (K := in_set_left_congruence_v3 _ _ symS tranS  _ _ _ H3 H). compute in K.  case_eq(rS x t); intro F; auto. 
       rewrite F in K. discriminate K.
       intros x H. apply in_set_cons_intro; auto. apply in_set_cons_elim in H; auto. 
       destruct H as [H | H].
       left.  apply symS in J. apply (tranS _ _ _ J H). 
       compute in H. discriminate H. 

       destruct (R a) as [J | J].
       right.
       apply brel_set_intro; split; apply brel_subset_intro; auto.
       intros x H. apply in_set_cons_intro; auto. apply in_set_cons_elim in H; auto. 
       destruct H as [H | H].
       left. apply (tranS _ _ _ J H).
       compute. destruct (R x) as [F | F]; auto. apply symS in F. rewrite F. right; auto. 
       intros x H. apply in_set_cons_intro; auto. apply in_set_cons_elim in H; auto.
       destruct H as [H | H].
       left. apply symS in J. apply (tranS _ _ _ J H).
       right. rewrite (in_set_congruence _ _ symS tranS  _ _ _ _ H4 (refS x)). 
       apply in_set_cons_intro; auto.        
       right.
       apply brel_set_intro; split; apply brel_subset_intro; auto.
       intros x H. apply in_set_cons_intro; auto. apply in_set_cons_elim in H; auto. 
       destruct H as [H | H].
       right. compute. assert (K := tranS _ _ _ J H). apply symS in K. rewrite K; auto. 
       compute. destruct (R x) as [F | F]; auto. apply symS in F. rewrite F. right; auto. 

       intros x H. apply in_set_cons_intro; auto. apply in_set_cons_elim in H; auto.
       destruct H as [H | H].
       right. apply symS in J. apply symS in H. rewrite (in_set_congruence _ _ symS tranS  _ _ _ _ H4 H). 
       apply in_set_cons_intro; auto.
       right. apply in_set_singleton_elim in H; auto. compute in H. 
       apply symS in H. rewrite (in_set_congruence _ _ symS tranS  _ _ _ _ H4 H). 
       apply in_set_cons_intro; auto.  right.  apply in_set_cons_intro; auto.  
Defined.

Lemma testX : ∀ (X Z Y W : finite_set S),
  brel_set rS X Z = true -> 
  brel_set rS Y W = true -> 
  brel_set rS (bop_lift rS bS X Y) X = brel_set rS (bop_lift rS bS Z W) Z.
Proof. intros X Z Y W H1 H2.
       assert (C := bop_lift_congruence _ _ _ _ H1 H2).
       assert (D := brel_set_congruence _ _ refS symS tranS).
       assert (E := D _ _ _ _ C H1). 
       exact E.
Qed.

Lemma testY : ∀ (X Z Y W : finite_set S),
  brel_set rS X Z = true -> 
  brel_set rS Y W = true -> 
     brel_set rS (bop_lift rS bS X Y) Y = brel_set rS (bop_lift rS bS Z W) W.
Proof. intros X Z Y W H1 H2.
       assert (C := bop_lift_congruence _ _ _ _ H1 H2).
       assert (D := brel_set_congruence _ _ refS symS tranS).
       assert (E := D _ _ _ _ C H2). 
       exact E.
Qed.


Lemma bop_lift_singletons: ∀ (a b : S),  
    brel_set rS (bop_lift rS bS (a :: nil) (b :: nil)) ((bS a b) :: nil) = true.
Proof. intros a b. 
       apply brel_set_intro. split.
          apply brel_subset_intro; auto.
          apply brel_subset_intro; auto.
Qed. 

Lemma bop_lift_compute_1_by_2 : ∀ (a b c : S),  
    brel_set rS (bop_lift rS bS (a :: nil) (b :: c :: nil)) ((bS a b):: (bS a c) :: nil) = true.
Proof. intros a b c.
       apply brel_set_intro. split.
          apply brel_subset_intro; auto. intros e H. 
          apply in_set_bop_lift_elim in H; auto.
          destruct H as [x [y [[H1 H2] H3]]].
          apply in_set_two_set_intro; auto. 
          apply in_set_singleton_elim in H1; auto. 
          apply in_set_two_set_elim in H2; auto. 
          destruct H2 as [H2 | H2];
          assert (H4 := tranS _ _ _ H3 (symS _ _ (bcong _ _ _ _ H1 H2))); auto.
          apply brel_subset_intro; auto. intros e H.
          apply in_set_two_set_elim in H; auto. 
          destruct H as [H | H]. 
             apply (in_set_bop_lift_intro_v2 _ _ e a b); auto.
                apply in_set_singleton_intro; auto. 
                apply in_set_two_set_intro; auto. 
             apply (in_set_bop_lift_intro_v2 _ _ e a c); auto.
                apply in_set_singleton_intro; auto. 
                apply in_set_two_set_intro; auto.  
Qed. 


Lemma bop_lift_compute_2_by_1 : ∀ (a b c : S),  
    brel_set rS (bop_lift rS bS (a :: b :: nil) (c :: nil)) ((bS a c):: (bS b c) :: nil) = true.
Proof. intros a b c.
       apply brel_set_intro. split.
          apply brel_subset_intro; auto. intros e H. 
          apply in_set_bop_lift_elim in H; auto.
          destruct H as [x [y [[H1 H2] H3]]].
          apply in_set_two_set_intro; auto.
          apply in_set_two_set_elim in H1; auto. 
          apply in_set_singleton_elim in H2; auto. 
          destruct H1 as [H1 | H1]; 
          assert (H4 := tranS _ _ _ H3 (symS _ _ (bcong _ _ _ _ H1 H2))); auto.
          apply brel_subset_intro; auto. intros e H.
          apply in_set_two_set_elim in H; auto. 
          destruct H as [H | H].
             apply (in_set_bop_lift_intro_v2 _ _ e a c); auto.
                apply in_set_two_set_intro; auto. 
                apply in_set_singleton_intro; auto. 
             apply (in_set_bop_lift_intro_v2 _ _ e b c); auto.
                apply in_set_two_set_intro; auto. 
                apply in_set_singleton_intro; auto. 
Qed. 


Lemma bop_lift_compute_2_by_2 : ∀ (a b c d : S),  
    brel_set rS (bop_lift rS bS (a :: b :: nil) (c :: d :: nil)) ((bS a c):: (bS a d) :: (bS b c) :: (bS b d) :: nil) = true.
Proof. intros a b c d.
       apply brel_set_intro. split.
          apply brel_subset_intro; auto. intros e H. 
          apply in_set_bop_lift_elim in H; auto.
          destruct H as [x [y [[H1 H2] H3]]].
          apply in_set_four_set_intro; auto.
          apply in_set_two_set_elim in H1; auto. 
          apply in_set_two_set_elim in H2; auto.
          destruct H1 as [H1 | H1];
          destruct H2 as [H2 | H2];
          assert (H4 := tranS _ _ _ H3 (symS _ _ (bcong _ _ _ _ H1 H2))); auto.
          apply brel_subset_intro; auto. intros e H.
          apply in_set_four_set_elim in H; auto. 
          destruct H as [[[H | H] | H] | H].
             apply (in_set_bop_lift_intro_v2 _ _ e a c); auto.
                apply in_set_two_set_intro; auto. 
                apply in_set_two_set_intro; auto. 
             apply (in_set_bop_lift_intro_v2 _ _ e a d); auto.
                apply in_set_two_set_intro; auto. 
                apply in_set_two_set_intro; auto. 
             apply (in_set_bop_lift_intro_v2 _ _ e b c); auto.
                apply in_set_two_set_intro; auto. 
                apply in_set_two_set_intro; auto. 
             apply (in_set_bop_lift_intro_v2 _ _ e b d); auto.
                apply in_set_two_set_intro; auto. 
                apply in_set_two_set_intro; auto. 
Qed. 

Lemma bop_lift_selective_v3 :  bop_idempotent S rS bS -> brel_exactly_two S rS -> bop_selective (finite_set S) (brel_set rS) (bop_lift rS bS).
Proof. intros idem [[s t] P] X Y.

       assert (cong_set := brel_set_congruence S rS refS symS tranS).
       assert (ref_set := brel_set_reflexive S rS refS symS).
       assert (sym_set := brel_set_symmetric S rS).
       assert (trn_set := brel_set_transitive S rS refS symS tranS).       
       
       assert (Ls := idem s). assert (Rs := symS _ _ Ls). 
       assert (Lt := idem t). assert (Rt := symS _ _ Lt).        
       assert (KX := brel_set_exactly_two_implies_four_subsets s t P X).
       assert (KY := brel_set_exactly_two_implies_four_subsets s t P Y).

       unfold exactly_two in P. destruct P as [F Q]. 
       assert (Kst := Q (bS s t)).       
       assert (Kts := Q (bS t s)). 
       
       destruct KX as [[[KX | KX] | KX] | KX]; destruct KY as [[[KY | KY] | KY] | KY];
       rewrite (testX _ _ _ _ KX KY); rewrite (testY _ _ _ _ KX KY).
           
       compute; auto.
       compute; auto.
       compute; auto.        
       compute; auto.
       compute; auto.
       compute; auto.        
       rewrite Ls, Rs; auto. 
       compute; auto.
       destruct Kst as [Kst | Kst].
          rewrite Kst. rewrite (symS _ _ Kst). left; auto.
          rewrite Kst. rewrite (symS _ _ Kst). right; auto.


       assert (J1 := bop_lift_compute_1_by_2 s s t).
       destruct Kts as [Kts | Kts]; destruct Kst as [Kst | Kst].
          left. assert (J2 := cong_set _ _ _ _ J1 (ref_set (s :: nil))).
                rewrite J2. compute. rewrite Kst. rewrite (symS _ _ Kst).  rewrite Ls, Rs. auto. 
          right. assert (J2 := cong_set _ _ _ _ J1 (ref_set (s :: t :: nil))).
                 rewrite J2. compute. rewrite Kst. rewrite (symS _ _ Kst).  rewrite Ls, Rs.
                 case_eq(rS (bS s t) s); intro J3; case_eq(rS t (bS s s)); intro J4; auto.
          left. assert (J2 := cong_set _ _ _ _ J1 (ref_set (s :: nil))).
                rewrite J2. compute. rewrite Kst. rewrite (symS _ _ Kst).  rewrite Ls, Rs. auto. 
          right. assert (J2 := cong_set _ _ _ _ J1 (ref_set (s :: t :: nil))).
                 rewrite J2. compute. rewrite Kst. rewrite (symS _ _ Kst).  rewrite Ls, Rs.
                 case_eq(rS (bS s t) s); intro J3; case_eq(rS t (bS s s)); intro J4; auto. 

       compute. right. auto. 

       compute. destruct Kts as [Kts | Kts].
          rewrite Kts. rewrite (symS _ _ Kts). right; auto.
          rewrite Kts. rewrite (symS _ _ Kts). left; auto.

       compute. rewrite Lt, Rt; auto. 

       assert (J1 := bop_lift_compute_1_by_2 t s t).
       destruct Kts as [Kts | Kts]; destruct Kst as [Kst | Kst].
          right. assert (J2 := cong_set _ _ _ _ J1 (ref_set (s :: t :: nil))).
                 rewrite J2. compute. rewrite Kts. rewrite (symS _ _ Kts).  rewrite Lt, Rt.
                 case_eq(rS (bS t t) s); intro J3; case_eq(rS t (bS t s)); intro J4; auto. 
          right. assert (J2 := cong_set _ _ _ _ J1 (ref_set (s :: t :: nil))).
                 rewrite J2. compute. rewrite Kts. rewrite (symS _ _ Kts).  rewrite Lt, Rt.
                 case_eq(rS (bS t t) s); intro J3; case_eq(rS t (bS t s)); intro J4; auto. 
          left. assert (J2 := cong_set _ _ _ _ J1 (ref_set (t :: nil))).
                rewrite J2. compute. rewrite Kts. rewrite (symS _ _ Kts).  rewrite Lt. auto. 
          left. assert (J2 := cong_set _ _ _ _ J1 (ref_set (t :: nil))).
                rewrite J2. compute. rewrite Kts. rewrite (symS _ _ Kts).  rewrite Lt. auto.                   

       compute; auto.  

       assert (J1 := bop_lift_compute_2_by_1 s t s).
       destruct Kts as [Kts | Kts]; destruct Kst as [Kst | Kst].          
          right. assert (J2 := cong_set _ _ _ _ J1 (ref_set (s :: nil))).
                 rewrite J2. compute. rewrite Kts. rewrite (symS _ _ Kts).  rewrite Ls, Rs. auto. 
          right. assert (J2 := cong_set _ _ _ _ J1 (ref_set (s :: nil))).
                 rewrite J2. compute. rewrite Kts. rewrite (symS _ _ Kts).  rewrite Ls, Rs. auto. 
          left. assert (J2 := cong_set _ _ _ _ J1 (ref_set (s :: t :: nil))).
                rewrite J2. compute. rewrite Kts. rewrite (symS _ _ Kts).  rewrite Ls, Rs.
                case_eq(rS (bS t s) s); intro J3; case_eq(rS t (bS s s)); intro J4; auto.                  
          left. assert (J2 := cong_set _ _ _ _ J1 (ref_set (s :: t :: nil))).
                rewrite J2. compute. rewrite Kts. rewrite (symS _ _ Kts).  rewrite Ls, Rs. 
                case_eq(rS (bS t s) s); intro J3; case_eq(rS t (bS s s)); intro J4; auto.                  

       assert (J1 := bop_lift_compute_2_by_1 s t t).
       destruct Kts as [Kts | Kts]; destruct Kst as [Kst | Kst].
          left. assert (J2 := cong_set _ _ _ _ J1 (ref_set (s :: t :: nil))).
                rewrite J2. compute. rewrite Kst. rewrite (symS _ _ Kst).  rewrite Lt, Rt.
                case_eq(rS (bS t t) s); intro J3; case_eq(rS t (bS s t)); intro J4; auto.
          right. assert (J2 := cong_set _ _ _ _ J1 (ref_set (t :: nil))).
                 rewrite J2. compute. rewrite Kst. rewrite (symS _ _ Kst).  rewrite Lt. auto. 
          left. assert (J2 := cong_set _ _ _ _ J1 (ref_set (s :: t :: nil))).
                rewrite J2. compute. rewrite Kst. rewrite (symS _ _ Kst).  rewrite Lt, Rt.
                case_eq(rS (bS t t) s); intro J3; case_eq(rS t (bS s t)); intro J4; auto.                  
          right. assert (J2 := cong_set _ _ _ _ J1 (ref_set (t :: nil))).
                 rewrite J2. compute. rewrite Kst. rewrite (symS _ _ Kst).  rewrite Lt. auto. 
       
       assert (J1 := bop_lift_compute_2_by_2 s t s t).
       left.
       assert (J2 := cong_set _ _ _ _ J1 (ref_set (s :: t :: nil))).
       rewrite J2. compute. rewrite Ls, Rs, Lt, Rt. 
       destruct Kts as [Kts | Kts]; destruct Kst as [Kst | Kst].
          rewrite (symS _ _ Kst), (symS _ _ Kts). 
          case_eq(rS (bS t t) s); intro J3; case_eq(rS t (bS s s)); intro J4;
          case_eq(rS t (bS s t)); intro J5; case_eq(rS t (bS t s)); intro J6; auto. 
          rewrite (symS _ _ Kst), (symS _ _ Kts). rewrite Kst.            
          case_eq(rS (bS s t) s); intro J3; case_eq(rS t (bS s s)); intro J4;
          case_eq(rS (bS t t) s); intro J5; auto. 
          rewrite (symS _ _ Kst), (symS _ _ Kts). rewrite Kts.                      
          case_eq(rS (bS t s) s); intro J3; case_eq(rS (bS t t) s); intro J4;
          case_eq(rS t (bS s s)); intro J5; case_eq(rS t (bS s t)); intro J6; auto. 
          rewrite (symS _ _ Kst), (symS _ _ Kts). rewrite Kts. rewrite Kst. 
          case_eq(rS (bS s t) s); intro J3; case_eq(rS (bS t s) s); intro J4;
          case_eq(rS (bS t t) s); intro J5; case_eq(rS t (bS s s)); intro J6; auto. 
Qed.               



Lemma bop_lift_selective :
  bop_is_left S rS bS +
  bop_is_right S rS bS +   
  (bop_idempotent S rS bS) * (brel_exactly_two S rS) -> bop_selective (finite_set S) (brel_set rS) (bop_lift rS bS).
Proof. intros [[IL | IR] | [idim et]].
       apply bop_lift_selective_v1; auto.
       apply bop_lift_selective_v2; auto.
       apply bop_lift_selective_v3; auto.
Qed.

Lemma bop_lift_not_selective_v1 :
  bop_not_idempotent S rS bS -> bop_not_selective (finite_set S) (brel_set rS) (bop_lift rS bS).
Proof. intros [a Nidem]. exists (a :: nil, a :: nil). compute. rewrite Nidem; auto. Defined. 


Lemma in_set_cons_false_elim  : ∀ (a b : S) (X : finite_set S),
   in_set rS (a :: X) b = false -> ((rS a b = false) * (in_set rS X b = false)).   
Proof. intros a b X H.
       case_eq(rS a b); intro K1; case_eq(in_set rS X b); intro K2; auto.
       rewrite (in_set_cons_intro _ _ symS a b X (inl K1)) in H. discriminate H.
       rewrite (in_set_cons_intro _ _ symS a b X (inl K1)) in H. discriminate H.
       rewrite (in_set_cons_intro _ _ symS a b X (inr K2)) in H. discriminate H.       
Qed.        

Lemma in_set_cons_false_intro : ∀ (a b : S) (X : finite_set S),
    ((rS a b = false) * (in_set rS X b = false)) -> in_set rS (a :: X) b = false. 
Proof. intros a b X [L R].
       case_eq(in_set rS (a :: X) b); intro J; auto.
       destruct (in_set_cons_elim _ _ symS _ _ _ J) as [F | F].
       rewrite F in L. discriminate L.
       rewrite F in R. discriminate R.        
Qed.

Lemma brel_subset_false_elim : 
  ∀ (x w : finite_set S),
    brel_subset rS x w = false -> {a : S & (in_set rS x a = true) * (in_set rS w a = false)}. 
Proof. induction x; intros w H. 
       compute in H. discriminate H.
       unfold brel_subset in H. fold (@brel_subset S) in H. 
       apply bop_and_false_elim in H.
       destruct H as [H | H].
       exists a. split. apply in_set_cons_intro; auto. exact H.
       destruct (IHx _ H) as [a0 [K1 K2]].
       exists a0. split. 
       apply in_set_cons_intro; auto.
       exact K2. 
Defined. 

Lemma brel_subset_false_intro : ∀ (x w : finite_set S), 
           {a : S & (in_set rS x a = true) * (in_set rS w a = false)} -> brel_subset rS x w = false. 
Proof. induction x.
       intros w [a [L R]].
       compute in L. discriminate L.
       intros w [b [L R]].  apply in_set_cons_elim in L; auto.
       unfold brel_subset. fold (@brel_subset S).
       destruct L as [L | L].
       apply bop_and_false_intro. left.
       case_eq(in_set rS w a); intro J; auto.
       assert (K := in_set_right_congruence _ _ symS tranS _ _ _ L J).  rewrite K in R. discriminate R.
       apply bop_and_false_intro. right.
       apply IHx.
       exists b. split; auto. 
Defined. 

Lemma brel_set_false_elim : ∀ (X Y : finite_set S), brel_set rS X Y = false -> (brel_subset rS X Y = false) + (brel_subset rS Y X = false).
Proof. intros X Y H.
       case_eq(brel_subset rS X Y); intro K1; case_eq(brel_subset rS Y X); intro K12; auto.
       rewrite (brel_set_intro  _ _ _ _ (K1, K12)) in H. discriminate H.        
Defined. 

Lemma brel_set_false_intro : ∀ (X Y : finite_set S), 
     (brel_subset rS X Y = false) + (brel_subset rS Y X = false) -> brel_set rS X Y = false.
Proof. intros X Y [H | H].
       case_eq(brel_set rS X Y); intro K; auto.
       apply brel_set_elim in K; auto. destruct K as [K1 K2]. rewrite K1 in H. discriminate H.
       case_eq(brel_set rS X Y); intro K; auto.
       apply brel_set_elim in K; auto. destruct K as [K1 K2]. rewrite K2 in H. discriminate H.
Defined. 


Lemma bop_lift_not_selective_initial_solution :
  bop_not_is_left S rS bS -> 
  bop_not_is_right S rS bS -> 
  (bop_idempotent S rS bS) -> 
  (brel_not_exactly_two S rS) -> bop_not_selective (finite_set S) (brel_set rS) (bop_lift rS bS).
Proof. intros [[a b] NL] [[c d] NR] idem [nex2 Net]. 

       assert (F1 : rS a b = false).
          case_eq(rS a b); intro F; auto.
          assert (K := idem a).
          assert (J := bcong _ _ _ _ (refS a) F).
          apply symS in K. assert (M := tranS _ _ _ K J).  apply symS in M. rewrite M in NL. discriminate NL. 

       assert (F2 : rS c d = false).
          case_eq(rS c d); intro F; auto.
          assert (K := idem d).
          assert (J := bcong _ _ _ _ F (refS d)).
          assert (M := tranS _ _ _ J K).  rewrite M in NR. discriminate NR.

       case_eq(rS (bS a b) b); intro J1.
          case_eq(rS (bS c d) c); intro J2. 
             destruct (Net a b) as [J3 | J3].
             rewrite J3 in F1. discriminate F1.
             destruct J3 as [J3 J4].  
             case_eq (rS (nex2 a b) (bS (nex2 a b) b)); intro J5; case_eq (rS b (bS (nex2 a b) b)); intro J6.
                (* J5 : rS (nex2 a b) (bS (nex2 a b) b) = true,  J6 : rS b (bS (nex2 a b) b) = true *) 
                apply symS in J5. rewrite (tranS _ _ _ J6 J5) in J4. discriminate J4.
                (* J5 : rS (nex2 a b) (bS (nex2 a b) b) = true,  J6 : rS b (bS (nex2 a b) b) = false *) 
                (* {(nex2 a b), a}.{b} = {(nex2 a b)b, ab} = {(nex2 a b), b} *)
                exists ((nex2 a b) :: a :: nil, b :: nil). split.
                   apply brel_set_false_intro; auto. 
                   right. apply brel_subset_false_intro; auto.
                   exists a. split.
                      compute. rewrite J3. rewrite refS. auto. 
                      case_eq(in_set rS (bop_lift rS bS ((nex2 a b) :: a :: nil) (b :: nil)) a); intro K; auto.
                      apply in_set_bop_lift_elim in K; auto.
                      destruct K as [x [y [[K1 K2] K3]]].
                      apply in_set_cons_elim in K1; auto. apply in_set_cons_elim in K2; auto. 
                      destruct K1 as [K1 | K1]; destruct K2 as [K2 | K2].
                      assert (K4 := bcong _ _ _ _ K1 K2).
                      apply symS in K4. assert (K5 := tranS _ _ _ K3 K4).
                      apply symS in J5. assert (K6 := tranS _ _ _ K5 J5). rewrite K6 in J3. discriminate J3.
                      compute in K2. discriminate K2. 
                      apply in_set_cons_elim in K1; auto. destruct K1 as [K1 | K1].
                         assert (K4 := bcong _ _ _ _ K1 K2). 
                         apply symS in K4. assert (K5 := tranS _ _ _ K3 K4).
                         assert (K6 := tranS _ _ _ K5 J1). rewrite K6 in F1. discriminate F1.
                         compute in K1. discriminate K1.
                         compute in K2. discriminate K2.
                      case_eq(brel_set rS (bop_lift rS bS ((nex2 a b) :: a :: nil) (b :: nil)) (b :: nil)); intro J7; auto. 
                         apply brel_set_elim in J7; auto. destruct J7 as [J7 J8].
                         assert (J9 := brel_subset_elim _ _ symS tranS _ _ J7 (bS (nex2 a b) b)). 
                         assert (J10 : in_set rS (bop_lift rS bS ((nex2 a b) :: a :: nil) (b :: nil)) (bS (nex2 a b) b) = true).
                            apply in_set_bop_lift_intro; auto.
                                apply in_set_cons_intro; auto. apply in_set_cons_intro; auto. 
                         assert (J11 := J9 J10).
                         apply in_set_cons_elim in J11; auto. destruct J11 as [J11 | J11].
                            rewrite J11 in J6. discriminate J6. 
                            compute in J11. discriminate J11. 
                (* J5 : rS (nex2 a b) (bS (nex2 a b) b) = false,  J6 : rS b (bS (nex2 a b) b) = true *) 
                destruct (Net c d) as [J7 | J7].
                rewrite J7 in F2. discriminate F2.
                destruct J7 as [J7 J8].
                case_eq (rS (nex2 c d) (bS c (nex2 c d))); intro J9; case_eq (rS c (bS c (nex2 c d))); intro J10.
                   (* J9 : rS (nex2 c d) (bS c (nex2 c d)) = true   J10 : rS c (bS c (nex2 c d)) = true*) 
                   apply symS in J9. rewrite (tranS _ _ _ J10 J9) in J7. discriminate J7.
                   (* J9 : rS (nex2 c d) (bS c (nex2 c d)) = true   J10 : rS c (bS c (nex2 c d)) = false *) 
                   (* {c}.{(nex2 c d) d} = {c(nex2 c d), cd} = {(nex2 c d), c} *)
                   exists (c :: nil, (nex2 c d) :: d :: nil). split.
                      (* brel_set rS (bop_lift rS bS (c :: nil) ((nex2 c d) :: d :: nil)) (c :: nil) = false *)
                      apply brel_set_false_intro; auto.
                      left. apply brel_subset_false_intro; auto.
                      exists (bS c (nex2 c d)). split.
                         apply in_set_bop_lift_intro; auto.
                         compute. rewrite refS; auto.
                         apply in_set_cons_intro; auto. 
                         compute. rewrite (brel_symmetric_implies_dual _ _ symS _ _ J10). auto. 
                      (* brel_set rS (bop_lift rS bS (c :: nil) ((nex2 c d) :: d :: nil)) ((nex2 c d) :: d :: nil) = false *)
                      apply brel_set_false_intro; auto.
                      left.
                      case_eq(brel_subset rS (bop_lift rS bS (c :: nil) ((nex2 c d) :: d :: nil)) ((nex2 c d) :: d :: nil) ); intro J11; auto.
                         assert (J12 := brel_subset_elim _ _ symS tranS _ _ J11 (bS c d)).
                         assert (J13 : in_set rS (bop_lift rS bS (c :: nil) ((nex2 c d) :: d :: nil)) (bS c d) = true).
                             apply in_set_bop_lift_intro; auto. 
                             compute. rewrite refS; auto.
                             apply in_set_cons_intro; auto. right. compute. rewrite refS; auto.
                         assert (J14 := J12 J13).
                         apply in_set_cons_elim in J14; auto. destruct J14 as [J14 | J14 ].
                            assert (J15 := tranS _ _ _ J14 J2).
                            apply symS in J15. rewrite J15 in J7. discriminate J7.
                            apply in_set_cons_elim in J14; auto. destruct J14 as [J14 | J14].
                               assert (J15 := tranS _ _ _ J14 J2). apply symS in J15. rewrite J15 in F2. discriminate F2. 
                               compute in J14. discriminate J14. 
                   (* J9 : rS (nex2 c d) (bS c (nex2 c d)) = false   J10 : rS d (bS c (nex2 c d)) = true *) 
                   case_eq (rS (nex2 a b) (bS (nex2 a b) (nex2 c d))); intro J11; case_eq (rS (nex2 c d) (bS (nex2 a b) (nex2 c d))); intro J12.
                      apply symS in J12. assert (J13 := tranS _ _ _ J11 J12).
                      (* DO THIS CASE EARLY ??? *) 
                      case_eq (rS (nex2 a b) (bS (nex2 a b) a)); intro J14; case_eq (rS a (bS (nex2 a b) a)); intro J15.
                         apply symS in J14. rewrite (tranS _ _ _ J15 J14) in J3. discriminate J3.
                         (* {e}{a, b} = {ea, eb} = {e, b} *)
                         exists((nex2 a b) :: nil, a :: b :: nil). split.
                            apply brel_set_false_intro; auto.
                            left. apply brel_subset_false_intro; auto.
                            exists b. split. 
                               apply (in_set_bop_lift_intro_v2 _ _ b (nex2 a b) b); auto.
                                  compute. rewrite refS; auto. 
                                  compute. rewrite refS. rewrite (brel_symmetric_implies_dual _ _ symS _ _ F1). auto. 
                               compute. rewrite J4; auto.                                 
                            apply brel_set_false_intro; auto. 
                            right. apply brel_subset_false_intro; auto.
                            exists a. split.
                               compute. rewrite refS; auto.                                 
                               case_eq(in_set rS (bop_lift rS bS ((nex2 a b) :: nil) (a :: b :: nil)) a); intro J16; auto. 
                                  apply in_set_bop_lift_elim in J16; auto.
                                  destruct J16 as [x [y [[J16 J17] J18]]].
                                  apply in_set_cons_elim in J16; auto. apply in_set_cons_elim in J17; auto. 
                                  destruct J16 as [J16 | J16]; destruct J17 as [J17 | J17].
                                     assert (J19 := bcong _ _ _ _ J16 J17).  apply symS in J19. rewrite (tranS _ _ _ J18 J19) in J15. discriminate J15.
                                     apply in_set_cons_elim in J17; auto. destruct J17 as [J17 | J17].
                                        assert (J19 := bcong _ _ _ _ J16 J17). 
                                        apply symS in J19. assert (J20 := tranS _ _ _ J18 J19). apply symS in J6.
                                        rewrite (tranS _ _ _ J20 J6) in F1. discriminate F1. 
                                        compute in J17. discriminate J17.
                                     compute in J16. discriminate J16.
                                     compute in J16. discriminate J16.
                         case_eq (rS (nex2 c d) (bS d (nex2 c d))); intro J16; case_eq (rS d (bS d (nex2 c d))); intro J17.
                            apply symS in J16. rewrite (tranS _ _ _ J17 J16) in J8. discriminate J8.
                            (* {c,d}{(nex2 c d)} = {c(nex2 c d), d(nex2 c d)} = {c, (nex2 c d)} *)
                            exists (c :: d :: nil, (nex2 c d) :: nil). split. 
                               apply brel_set_false_intro; auto.
                               right.  apply brel_subset_false_intro; auto.
                               exists d. split. 
                                  compute. rewrite refS. case_eq(rS d c); intro J18; auto.
                                  case_eq(in_set rS (bop_lift rS bS (c :: d :: nil) ((nex2 c d) :: nil)) d); intro J18; auto.
                                  apply in_set_bop_lift_elim in J18. destruct J18 as [x [y [[J18 J19] J20]]].
                                  apply in_set_cons_elim in J18; auto. apply in_set_cons_elim in J19; auto.
                                  destruct J18 as [J18 | J18]; destruct J19 as [J19 | J19].
                                     assert (J21 := bcong _ _ _ _ J18 J19).
                                     apply symS in J21. assert (J22 := tranS _ _ _ J20 J21).
                                     apply symS in J22. rewrite (tranS _ _ _ J10 J22) in F2. discriminate F2.
                                     compute in J19. discriminate J19.                                      
                                     apply in_set_cons_elim in J18; auto. destruct J18 as [J18 | J18].
                                        assert (J21 := bcong _ _ _ _ J18 J19). apply symS in J21.
                                        assert (J22 := tranS _ _ _ J20 J21). rewrite J22 in J17. discriminate J17.
                                        compute in J18. discriminate J18. 
                                     compute in J19. discriminate J19.                                      
                               apply brel_set_false_intro; auto.
                               left. apply brel_subset_false_intro; auto.
                               exists (bS c (nex2 c d)). split.
                                  apply in_set_bop_lift_intro; auto.
                                     compute. rewrite refS; auto.
                                     compute. rewrite refS; auto.
                                  compute. rewrite (brel_symmetric_implies_dual _ _ symS _ _ J9). auto.
                             case_eq(rS a c); intro J18.    
                               (*  {a}{b, e} = {ab, ae} = {b, a} *)
                               exists (a :: nil, (nex2 c d) :: b :: nil). split.
                                  apply brel_set_false_intro; auto.
                                  left. apply brel_subset_false_intro; auto.
                                  exists b. split.
                                     apply (in_set_bop_lift_intro_v2 _ _ b a b); auto.
                                        compute; rewrite refS; auto.
                                        compute. rewrite refS. case_eq(rS b (nex2 c d)); intro J19; auto.
                                        compute. rewrite (brel_symmetric_implies_dual _ _ symS _ _ F1). auto. 
                                  apply brel_set_false_intro; auto.
                                  right. apply brel_subset_false_intro; auto.
                                  exists (nex2 c d). split.
                                     compute. rewrite refS. auto. 
                                     case_eq(in_set rS (bop_lift rS bS (a :: nil) ((nex2 c d) :: b :: nil)) (nex2 c d)); intro J19; auto.
                                        apply in_set_bop_lift_elim in J19; auto.
                                        destruct J19 as [x [y [[J19 J20] J21]]].
                                        apply in_set_singleton_elim in J19; auto. 
                                        apply in_set_cons_elim in J20; auto. 
                                        destruct J20 as [J20 | J20].
                                           assert (J22 := bcong _ _ _ _ J19 J20).
                                           apply symS in J22. assert (J23 := tranS _ _ _ J21 J22).
                                           assert (J24 := bcong _ _ _ _ J18 (refS (nex2 c d))).
                                           rewrite (tranS _ _ _ J23 J24) in J9. discriminate J9.
                                        apply in_set_singleton_elim in J20; auto. 
                                        assert (J22 := bcong _ _ _ _ J19 J20).
                                        apply symS in J22. assert (J23 := tranS _ _ _ J21 J22).
                                        assert (J24 := tranS _ _ _ J23 J1).
                                        assert (J25 := tranS _ _ _ J13 J24).
                                        apply symS in J25. rewrite J25 in J4. discriminate J4. 
                               (* {e, c}{e, a} = {ee, ea, ce ca} = {e, a, c, ca} *)
                               exists ((nex2 a b) :: c :: nil, (nex2 c d) :: a :: nil). split.
                                  apply brel_set_false_intro; auto. 
                                  left. apply brel_subset_false_intro; auto.
                                  exists a. split.
                                     apply (in_set_bop_lift_intro_v2 _ _ a (nex2 a b) a); auto.
                                        compute. rewrite refS; auto.
                                        compute. rewrite refS. case_eq(rS a (nex2 c d)); intro J19; auto.
                                        compute. rewrite J18. rewrite J3. auto. 
                                  apply brel_set_false_intro; auto.
                                  left. apply brel_subset_false_intro; auto.
                                  exists (bS c (nex2 c d)). split.
                                     apply in_set_bop_lift_intro; auto.
                                        compute. rewrite refS. case_eq(rS c (nex2 a b)); intro J19; auto. 
                                        compute. rewrite refS. auto. 
                                     compute. case_eq(rS (bS c (nex2 c d)) (nex2 c d)); intro J19; case_eq(rS (bS c (nex2 c d)) a); intro J20; auto.
                                        apply symS in J20. apply symS in J10. rewrite (tranS _ _ _ J20 J10) in J18. discriminate J18.  
                                        rewrite (tranS _ _ _ J10 J19) in J7. discriminate J7.
                                        apply symS in J20. apply symS in J10. rewrite (tranS _ _ _ J20 J10) in J18. discriminate J18. 
                          (* {d}{(nex2 c d)} = {d(nex2 c d)}*)
                          exists (d:: nil, (nex2 c d) :: nil). compute. rewrite J16, J17.
                               rewrite (brel_symmetric_implies_dual _ _ symS _ _ J16). rewrite (brel_symmetric_implies_dual _ _ symS _ _ J17). auto. 
                         (* {e}{a} = {ea} *)                         
                         exists((nex2 a b) :: nil, a :: nil). split.
                            apply brel_set_false_intro; auto.
                            right. apply brel_subset_false_intro; auto.
                            exists (nex2 a b). split. 
                               compute. rewrite refS; auto.
                               case_eq(in_set rS (bop_lift rS bS ((nex2 a b) :: nil) (a :: nil)) (nex2 a b)); intro J16; auto. 
                                  apply in_set_bop_lift_elim in J16; auto. destruct J16 as [x [y [[J16 J17] J18]]].
                                  apply in_set_cons_elim in J16; auto. apply in_set_cons_elim in J17; auto.
                                  destruct J16 as[J16 | J16]; destruct J17 as[J17 | J17].
                                     assert (J19 := bcong _ _ _ _ J16 J17). apply symS in J19. rewrite (tranS _ _ _ J18 J19) in J14. discriminate J14.
                                  compute in J17. discriminate J17.
                                  compute in J16. discriminate J16.
                                  compute in J17. discriminate J17.
                            apply brel_set_false_intro; auto.
                            right. apply brel_subset_false_intro; auto.
                            exists a. split. 
                               compute. rewrite refS; auto.
                               case_eq(in_set rS (bop_lift rS bS ((nex2 a b) :: nil) (a :: nil)) a); intro J16; auto. 
                                  apply in_set_bop_lift_elim in J16; auto. destruct J16 as [x [y [[J16 J17] J18]]].
                                  apply in_set_cons_elim in J16; auto. apply in_set_cons_elim in J17; auto.
                                  destruct J16 as[J16 | J16]; destruct J17 as[J17 | J17].
                                     assert (J19 := bcong _ _ _ _ J16 J17). apply symS in J19. rewrite (tranS _ _ _ J18 J19) in J15. discriminate J15.
                                  compute in J17. discriminate J17.
                                  compute in J16. discriminate J16.
                                  compute in J17. discriminate J17.
                      (* {(nex2 a b)}{(nex2 c d), b} = {(nex2 a b)(nex2 c d), (nex2 a b)b} = {(nex2 a b), b} *)
                      exists ((nex2 a b) :: nil, (nex2 c d) :: b :: nil). split.
                         apply brel_set_false_intro; auto.
                         left. apply brel_subset_false_intro; auto.
                         exists (bS (nex2 a b) b). split. 
                             apply in_set_bop_lift_intro; auto.                          
                                compute. rewrite refS; auto. 
                                compute. rewrite refS.
                                case_eq(rS b (nex2 c d)); intro J13; auto.
                                compute. rewrite (brel_symmetric_implies_dual _ _ symS _ _ J5). auto. 
                         apply brel_set_false_intro; auto.
                         left. apply brel_subset_false_intro; auto.
                         exists (nex2 a b). split.
                            apply (in_set_bop_lift_intro_v2 _ _ (nex2 a b) (nex2 a b) (nex2 c d)); auto. 
                               compute. rewrite refS; auto. 
                               compute. rewrite refS. auto.
                               compute. rewrite (brel_symmetric_implies_dual _ _ symS _ _ J4).
                               assert (J13 : rS (nex2 a b) (nex2 c d) = false).
                                  case_eq(rS (nex2 a b) (nex2 c d)); intro J13; auto. apply symS in J13. rewrite (tranS _ _ _ J13 J11) in J12. discriminate J12.                                            rewrite J13; auto.                    
                      (* {(nex2 a b), c}{(nex2 c d)} = {(nex2 a b)(nex2 c d), c(nex2 c d)} = {(nex2 c d), c} *)
                      exists ((nex2 a b) :: c :: nil, (nex2 c d) :: nil). split.
                         apply brel_set_false_intro; auto.
                         right. apply brel_subset_false_intro; auto.
                         exists (nex2 a b). split. 
                            compute. rewrite refS; auto. 
                            case_eq(in_set rS (bop_lift rS bS ((nex2 a b) :: c :: nil) ((nex2 c d) :: nil)) (nex2 a b)); intro J13; auto.
                               apply in_set_bop_lift_elim in J13; auto.
                               destruct J13 as [x [y [[J13 J14] J15]]].
                               apply in_set_cons_elim in J13; auto. apply in_set_cons_elim in J14; auto.
                               destruct J13 as [J13 | J13]; destruct J14 as [J14 | J14].
                                  assert (J16 := bcong _ _ _ _ J13 J14). apply symS in J16.
                                  rewrite (tranS _ _ _ J15 J16) in J11. discriminate J11. 
                                  compute in J14. discriminate J14. 
                                  apply in_set_singleton_elim in J13; auto. (***********)
                                  assert (J16 := bcong _ _ _ _ J13 J14). apply symS in J16.
                                  assert (J17 := tranS _ _ _ J15 J16). apply symS in J17.
                                  case_eq(rS c (nex2 a b)); intro J18.
                                     assert (J19 := bcong _ _ _ _ J18 (refS (nex2 c d))).
                                     assert (J20 := tranS _ _ _ J10 J19).
                                     apply symS in J12. rewrite (tranS _ _ _ J20 J12) in J7. discriminate J7.
                                     rewrite (tranS _ _ _ J10 J17) in J18. discriminate J18. 
                                  compute in J14. discriminate J14. 
                         apply brel_set_false_intro; auto. 
                         left. apply brel_subset_false_intro; auto.
                         exists c. split.
                            apply (in_set_bop_lift_intro_v2 _ _ c c (nex2 c d)); auto. 
                               compute. rewrite refS. case_eq(rS c (nex2 a b)); intro J13; auto.
                               compute. rewrite refS; auto.
                            compute. rewrite J7; auto. 
                      exists ((nex2 a b) :: nil, (nex2 c d) :: nil). compute. rewrite J11, J12.
                         rewrite (brel_symmetric_implies_dual _ _ symS _ _ J11). rewrite (brel_symmetric_implies_dual _ _ symS _ _ J12). auto. 
                   (* J9 : rS (nex2 c d) (bS c (nex2 c d)) = false   J10 : rS c (bS c (nex2 c d)) =  false*)
                   exists (c :: nil, (nex2 c d) :: nil). compute. rewrite J9, J10.
                      rewrite (brel_symmetric_implies_dual _ _ symS _ _ J9). rewrite (brel_symmetric_implies_dual _ _ symS _ _ J10). auto.
                (* J5 : rS (nex2 a b) (bS (nex2 a b) b) = false,  J6 : rS b (bS (nex2 a b) b) = false *)                 
                exists ((nex2 a b) :: nil, b :: nil). compute. rewrite J5, J6.
                   rewrite (brel_symmetric_implies_dual _ _ symS _ _ J5). rewrite (brel_symmetric_implies_dual _ _ symS _ _ J6). auto. 
          (* J2 : rS (bS c d) c = false *)           
          exists (c :: nil, d :: nil). compute.  rewrite NR. rewrite J2. auto.
       (* J1 : rS (bS a b) b = false *)           
       exists (a :: nil, b :: nil). compute.  rewrite NL. rewrite J1. auto. 
Defined.


(* simplify this ? 

given 

not left  : a * b <> a 
not ritht : c * d <> d 
nex2 x y <> x 
nex2 x y <> y 

produce (X, Y) such that X *^ Y <> X and X *^ Y <> Y. 

Definition lift_not_selective (a b c d : S) (nex2 : S -> (S -> S)) : (finite_set S) * (finite_set S) :=
  let e = nex2 a b in
  let f = next c d in 
  if a * b = b      
  then if (c * d) = c 
       then if e = e * b
            then ({e, a}, {b})
            else if b = e * b  
                 then if f = c * f
                      then ({c}, {f, d})
                      else if c = c * f
                           then if e = e * f 
                                then if f = e * f
                                     then if e = e * a
                                          then ({e}, {a, b})
                                          else if a = e * a 
                                               then if f = d * f  
                                                    then ({c, d}, {f})
                                                    else if d = d * f
                                                         then if a = c 
                                                              then ({a}, {f, b})
                                                              else ({e, c}, {f, a})
                                                         else ({d}, {f})
                                               else ({e}, {a})
                                     else ({e}, {f, b})
                                else if f = e * f
                                     then ({e, c}, {f})
                                     else ({e}, {f})
                           else ({c}, {f})
                 else ({e}, {b})
       else ({c}, {d})
  else ({a}, {b}).

simplify to 

  let e = nex2 a b in
  let f = next c d in 
  if a * b <> b      
  then ({a}, {b}) 
  else (* H1 : a * b = b <> a *) 
       if (c * d) <> c 
       then ({c}, {d})
       else (* H2 : c * d = c <> d *) 
            if (a * c) <> a 
            then if (a * c) <> c 
                 then ({a}, {c})
                 else (* H3 : a * c = c *) 

            else (* H3 : a * c = a *) 

==============================
  let e = nex2 a b in
  let f = next c d in 
  if ab <> b      
  then ({a}, {b}) 
  else (* H1 : ab = b <> a *) 
       if cd <> c 
       then ({c}, {d})
       else (* H2 : cd = c <> d *) 
            if ad <> d 
            then {a}*{b, d} = {ab, ad} = {b, ad}
            else (* H3 : ad = d *) 
            if 
            then {c}*{b, d} = {cb, cd} = {cb, c}
            
*) 

Definition lift_not_selective (a b c d : S) (nex2 : S -> (S -> S)) : (finite_set S) * (finite_set S) :=
  if rS (bS a b) b      (* J1 *) 
  then if rS (bS c d) c (* J2 *) 
       then if rS (nex2 a b) (bS (nex2 a b) b) (* J5 *)
            then ((nex2 a b) :: a :: nil, b :: nil)
            else if rS b (bS (nex2 a b) b)     (* J6 *)
                 then if rS (nex2 c d) (bS c (nex2 c d))  (* J9 *) 
                      then (c :: nil, (nex2 c d) :: d :: nil)
                      else if rS c (bS c (nex2 c d))      (* J10 *) 
                           then if rS (nex2 a b) (bS (nex2 a b) (nex2 c d)) (* J11 *) 
                                then if rS (nex2 c d) (bS (nex2 a b) (nex2 c d)) (* J12 *)
                                     then if rS (nex2 a b) (bS (nex2 a b) a) (* J14 *)
                                          then ((nex2 a b) :: nil, a :: b :: nil)
                                          else if rS a (bS (nex2 a b) a) (* J15 *)
                                               then if rS (nex2 c d) (bS d (nex2 c d))  (* J16 *)
                                                    then (c :: d :: nil, (nex2 c d) :: nil)
                                                    else if rS d (bS d (nex2 c d)) (* J 17 *)
                                                         then if rS a c (* J18 *)
                                                              then (a :: nil, (nex2 c d) :: b :: nil)
                                                              else ((nex2 a b) :: c :: nil, (nex2 c d) :: a :: nil)
                                                         else (d:: nil, (nex2 c d) :: nil)
                                               else ((nex2 a b) :: nil, a :: nil)
                                     else ((nex2 a b) :: nil, (nex2 c d) :: b :: nil)
                                else if rS (nex2 c d) (bS (nex2 a b) (nex2 c d)) (* J12 *)
                                     then ((nex2 a b) :: c :: nil, (nex2 c d) :: nil)
                                     else ((nex2 a b) :: nil, (nex2 c d) :: nil)
                           else (c :: nil, (nex2 c d) :: nil)
                 else ((nex2 a b) :: nil, b :: nil)
       else (c :: nil, d :: nil)
  else (a :: nil, b :: nil).

(* 
Definition lift_not_selective_new (a b c d : S) (nex2 : S -> (S -> S)) : (finite_set S) * (finite_set S) :=
  let d := nex2 a b in
  let e := nex2 c d in 
  if rS (bS a b) b      (* J1 *) 
  then if rS (bS c d) c (* J2 *) 
       then if rS d (bS d b) (* J5 *)
            then (d :: a :: nil, b :: nil)
            else if rS b (bS d b)     (* J6 *)
                 then if rS e (bS c e)  (* J9 *) 
                      then (c :: nil, e :: d :: nil)
                      else if rS c (bS c e)      (* J10 *) 
                           then if rS d (bS d e) (* J11 *) 
                                then if rS e (bS d e) (* J12 *)
                                     then if rS d (bS d a) (* J14 *)
                                          then (d :: nil, a :: b :: nil)
                                          else if rS a (bS d a) (* J15 *)
                                               then if rS e (bS d e)  (* J16 *)
                                                    then (c :: d :: nil, e :: nil)
                                                    else if rS d (bS d e) (* J 17 *)
                                                         then if rS a c (* J18 *)
                                                              then (a :: nil, e :: b :: nil)
                                                              else (d :: c :: nil, e :: a :: nil)
                                                         else (d:: nil, e :: nil)
                                               else (d :: nil, a :: nil)
                                     else (d :: nil, e :: b :: nil)
                                else if rS e (bS d e) (* J12 *)
                                     then (d :: c :: nil, e :: nil)
                                     else (d :: nil, e :: nil)
                           else (c :: nil, e :: nil)
                 else (d :: nil, b :: nil)
       else (c :: nil, d :: nil)
  else (a :: nil, b :: nil).

Note that there are 14 distinct sulutions here: 
(d :: a :: nil, b :: nil)
(c :: nil, e :: d :: nil)
(d :: nil, a :: b :: nil)
(c :: d :: nil, e :: nil)
(a :: nil, e :: b :: nil)
(d :: c :: nil, e :: a :: nil)
(d :: nil, e :: nil)       <<< duplicated
(d :: nil, a :: nil)
(d :: nil, e :: b :: nil)
(d :: c :: nil, e :: nil)
(d :: nil, e :: nil)        <<< duplicated
(c :: nil, e :: nil)
(d :: nil, b :: nil)
(c :: nil, d :: nil)
(a :: nil, b :: nil).

Could this be simplified somehow? 

*) 

Lemma bop_lift_not_selective :
  bop_not_is_left S rS bS -> 
  bop_not_is_right S rS bS -> 
  (bop_idempotent S rS bS) -> 
  (brel_not_exactly_two S rS) -> bop_not_selective (finite_set S) (brel_set rS) (bop_lift rS bS).
Proof. intros bnil bnir idem bnext.
       exists(lift_not_selective (fst (projT1 bnil)) (snd (projT1 bnil)) (fst (projT1 bnir)) (snd (projT1 bnir))  (projT1 bnext)). 
       destruct bnil as [[a b] NL].
       destruct bnir as [[c d] NR].
       destruct bnext as [nex2 Net]. simpl. 

       assert (F1 : rS a b = false).
          case_eq(rS a b); intro F; auto.
          assert (K := idem a).
          assert (J := bcong _ _ _ _ (refS a) F).
          apply symS in K. assert (M := tranS _ _ _ K J).  apply symS in M. rewrite M in NL. discriminate NL. 

       assert (F2 : rS c d = false).
          case_eq(rS c d); intro F; auto.
          assert (K := idem d).
          assert (J := bcong _ _ _ _ F (refS d)).
          assert (M := tranS _ _ _ J K).  rewrite M in NR. discriminate NR.

       unfold lift_not_selective. 
       case_eq(rS (bS a b) b); intro J1.
          case_eq(rS (bS c d) c); intro J2. 
             destruct (Net a b) as [J3 | J3].
             rewrite J3 in F1. discriminate F1.
             destruct J3 as [J3 J4].  
             case_eq (rS (nex2 a b) (bS (nex2 a b) b)); intro J5; case_eq (rS b (bS (nex2 a b) b)); intro J6.
                (* J5 : rS (nex2 a b) (bS (nex2 a b) b) = true,  J6 : rS b (bS (nex2 a b) b) = true *) 
                apply symS in J5. rewrite (tranS _ _ _ J6 J5) in J4. discriminate J4.
                (* J5 : rS (nex2 a b) (bS (nex2 a b) b) = true,  J6 : rS b (bS (nex2 a b) b) = false *) 
                (* {(nex2 a b), a}.{b} = {(nex2 a b)b, ab} = {(nex2 a b), b} *)
                split.
                   apply brel_set_false_intro; auto. 
                   right. apply brel_subset_false_intro; auto.
                   exists a. split.
                      compute. rewrite J3. rewrite refS. auto. 
                      case_eq(in_set rS (bop_lift rS bS ((nex2 a b) :: a :: nil) (b :: nil)) a); intro K; auto.
                      apply in_set_bop_lift_elim in K; auto.
                      destruct K as [x [y [[K1 K2] K3]]].
                      apply in_set_cons_elim in K1; auto. apply in_set_cons_elim in K2; auto. 
                      destruct K1 as [K1 | K1]; destruct K2 as [K2 | K2].
                      assert (K4 := bcong _ _ _ _ K1 K2).
                      apply symS in K4. assert (K5 := tranS _ _ _ K3 K4).
                      apply symS in J5. assert (K6 := tranS _ _ _ K5 J5). rewrite K6 in J3. discriminate J3.
                      compute in K2. discriminate K2. 
                      apply in_set_cons_elim in K1; auto. destruct K1 as [K1 | K1].
                         assert (K4 := bcong _ _ _ _ K1 K2). 
                         apply symS in K4. assert (K5 := tranS _ _ _ K3 K4).
                         assert (K6 := tranS _ _ _ K5 J1). rewrite K6 in F1. discriminate F1.
                         compute in K1. discriminate K1.
                         compute in K2. discriminate K2.
                      case_eq(brel_set rS (bop_lift rS bS ((nex2 a b) :: a :: nil) (b :: nil)) (b :: nil)); intro J7; auto. 
                         apply brel_set_elim in J7; auto. destruct J7 as [J7 J8].
                         assert (J9 := brel_subset_elim _ _ symS tranS _ _ J7 (bS (nex2 a b) b)). 
                         assert (J10 : in_set rS (bop_lift rS bS ((nex2 a b) :: a :: nil) (b :: nil)) (bS (nex2 a b) b) = true).
                            apply in_set_bop_lift_intro; auto.
                                apply in_set_cons_intro; auto. apply in_set_cons_intro; auto. 
                         assert (J11 := J9 J10).
                         apply in_set_cons_elim in J11; auto. destruct J11 as [J11 | J11].
                            rewrite J11 in J6. discriminate J6. 
                            compute in J11. discriminate J11. 
                (* J5 : rS (nex2 a b) (bS (nex2 a b) b) = false,  J6 : rS b (bS (nex2 a b) b) = true *) 
                destruct (Net c d) as [J7 | J7].
                rewrite J7 in F2. discriminate F2.
                destruct J7 as [J7 J8].
                case_eq (rS (nex2 c d) (bS c (nex2 c d))); intro J9; case_eq (rS c (bS c (nex2 c d))); intro J10.
                   (* J9 : rS (nex2 c d) (bS c (nex2 c d)) = true   J10 : rS c (bS c (nex2 c d)) = true*) 
                   apply symS in J9. rewrite (tranS _ _ _ J10 J9) in J7. discriminate J7.
                   (* J9 : rS (nex2 c d) (bS c (nex2 c d)) = true   J10 : rS c (bS c (nex2 c d)) = false *) 
                   (* {c}.{(nex2 c d) d} = {c(nex2 c d), cd} = {(nex2 c d), c} *)
                   split.
                      (* brel_set rS (bop_lift rS bS (c :: nil) ((nex2 c d) :: d :: nil)) (c :: nil) = false *)
                      apply brel_set_false_intro; auto.
                      left. apply brel_subset_false_intro; auto.
                      exists (bS c (nex2 c d)). split.
                         apply in_set_bop_lift_intro; auto.
                         compute. rewrite refS; auto.
                         apply in_set_cons_intro; auto. 
                         compute. rewrite (brel_symmetric_implies_dual _ _ symS _ _ J10). auto. 
                      (* brel_set rS (bop_lift rS bS (c :: nil) ((nex2 c d) :: d :: nil)) ((nex2 c d) :: d :: nil) = false *)
                      apply brel_set_false_intro; auto.
                      left.
                      case_eq(brel_subset rS (bop_lift rS bS (c :: nil) ((nex2 c d) :: d :: nil)) ((nex2 c d) :: d :: nil) ); intro J11; auto.
                         assert (J12 := brel_subset_elim _ _ symS tranS _ _ J11 (bS c d)).
                         assert (J13 : in_set rS (bop_lift rS bS (c :: nil) ((nex2 c d) :: d :: nil)) (bS c d) = true).
                             apply in_set_bop_lift_intro; auto. 
                             compute. rewrite refS; auto.
                             apply in_set_cons_intro; auto. right. compute. rewrite refS; auto.
                         assert (J14 := J12 J13).
                         apply in_set_cons_elim in J14; auto. destruct J14 as [J14 | J14 ].
                            assert (J15 := tranS _ _ _ J14 J2).
                            apply symS in J15. rewrite J15 in J7. discriminate J7.
                            apply in_set_cons_elim in J14; auto. destruct J14 as [J14 | J14].
                               assert (J15 := tranS _ _ _ J14 J2). apply symS in J15. rewrite J15 in F2. discriminate F2. 
                               compute in J14. discriminate J14. 
                   (* J9 : rS (nex2 c d) (bS c (nex2 c d)) = false   J10 : rS d (bS c (nex2 c d)) = true *) 
                   case_eq (rS (nex2 a b) (bS (nex2 a b) (nex2 c d))); intro J11; case_eq (rS (nex2 c d) (bS (nex2 a b) (nex2 c d))); intro J12.
                      apply symS in J12. assert (J13 := tranS _ _ _ J11 J12).
                      (* DO THIS CASE EARLY ??? *) 
                      case_eq (rS (nex2 a b) (bS (nex2 a b) a)); intro J14; case_eq (rS a (bS (nex2 a b) a)); intro J15.
                         apply symS in J14. rewrite (tranS _ _ _ J15 J14) in J3. discriminate J3.
                         (* {e}{a, b} = {ea, eb} = {e, b} *)
                         split.
                            apply brel_set_false_intro; auto.
                            left. apply brel_subset_false_intro; auto.
                            exists b. split. 
                               apply (in_set_bop_lift_intro_v2 _ _ b (nex2 a b) b); auto.
                                  compute. rewrite refS; auto. 
                                  compute. rewrite refS. rewrite (brel_symmetric_implies_dual _ _ symS _ _ F1). auto. 
                               compute. rewrite J4; auto.                                 
                            apply brel_set_false_intro; auto. 
                            right. apply brel_subset_false_intro; auto.
                            exists a. split.
                               compute. rewrite refS; auto.                                 
                               case_eq(in_set rS (bop_lift rS bS ((nex2 a b) :: nil) (a :: b :: nil)) a); intro J16; auto. 
                                  apply in_set_bop_lift_elim in J16; auto.
                                  destruct J16 as [x [y [[J16 J17] J18]]].
                                  apply in_set_cons_elim in J16; auto. apply in_set_cons_elim in J17; auto. 
                                  destruct J16 as [J16 | J16]; destruct J17 as [J17 | J17].
                                     assert (J19 := bcong _ _ _ _ J16 J17).  apply symS in J19. rewrite (tranS _ _ _ J18 J19) in J15. discriminate J15.
                                     apply in_set_cons_elim in J17; auto. destruct J17 as [J17 | J17].
                                        assert (J19 := bcong _ _ _ _ J16 J17). 
                                        apply symS in J19. assert (J20 := tranS _ _ _ J18 J19). apply symS in J6.
                                        rewrite (tranS _ _ _ J20 J6) in F1. discriminate F1. 
                                        compute in J17. discriminate J17.
                                     compute in J16. discriminate J16.
                                     compute in J16. discriminate J16.
                         case_eq (rS (nex2 c d) (bS d (nex2 c d))); intro J16; case_eq (rS d (bS d (nex2 c d))); intro J17.
                            apply symS in J16. rewrite (tranS _ _ _ J17 J16) in J8. discriminate J8.
                            (* {c,d}{(nex2 c d)} = {c(nex2 c d), d(nex2 c d)} = {c, (nex2 c d)} *)
                            split. 
                               apply brel_set_false_intro; auto.
                               right.  apply brel_subset_false_intro; auto.
                               exists d. split. 
                                  compute. rewrite refS. case_eq(rS d c); intro J18; auto.
                                  case_eq(in_set rS (bop_lift rS bS (c :: d :: nil) ((nex2 c d) :: nil)) d); intro J18; auto.
                                  apply in_set_bop_lift_elim in J18. destruct J18 as [x [y [[J18 J19] J20]]].
                                  apply in_set_cons_elim in J18; auto. apply in_set_cons_elim in J19; auto.
                                  destruct J18 as [J18 | J18]; destruct J19 as [J19 | J19].
                                     assert (J21 := bcong _ _ _ _ J18 J19).
                                     apply symS in J21. assert (J22 := tranS _ _ _ J20 J21).
                                     apply symS in J22. rewrite (tranS _ _ _ J10 J22) in F2. discriminate F2.
                                     compute in J19. discriminate J19.                                      
                                     apply in_set_cons_elim in J18; auto. destruct J18 as [J18 | J18].
                                        assert (J21 := bcong _ _ _ _ J18 J19). apply symS in J21.
                                        assert (J22 := tranS _ _ _ J20 J21). rewrite J22 in J17. discriminate J17.
                                        compute in J18. discriminate J18. 
                                     compute in J19. discriminate J19.                                      
                               apply brel_set_false_intro; auto.
                               left. apply brel_subset_false_intro; auto.
                               exists (bS c (nex2 c d)). split.
                                  apply in_set_bop_lift_intro; auto.
                                     compute. rewrite refS; auto.
                                     compute. rewrite refS; auto.
                                  compute. rewrite (brel_symmetric_implies_dual _ _ symS _ _ J9). auto.
                             case_eq(rS a c); intro J18.    
                               (*  {a}{b, e} = {ab, ae} = {b, a} *)
                               split.
                                  apply brel_set_false_intro; auto.
                                  left. apply brel_subset_false_intro; auto.
                                  exists b. split.
                                     apply (in_set_bop_lift_intro_v2 _ _ b a b); auto.
                                        compute; rewrite refS; auto.
                                        compute. rewrite refS. case_eq(rS b (nex2 c d)); intro J19; auto.
                                        compute. rewrite (brel_symmetric_implies_dual _ _ symS _ _ F1). auto. 
                                  apply brel_set_false_intro; auto.
                                  right. apply brel_subset_false_intro; auto.
                                  exists (nex2 c d). split.
                                     compute. rewrite refS. auto. 
                                     case_eq(in_set rS (bop_lift rS bS (a :: nil) ((nex2 c d) :: b :: nil)) (nex2 c d)); intro J19; auto.
                                        apply in_set_bop_lift_elim in J19; auto.
                                        destruct J19 as [x [y [[J19 J20] J21]]].
                                        apply in_set_singleton_elim in J19; auto. 
                                        apply in_set_cons_elim in J20; auto. 
                                        destruct J20 as [J20 | J20].
                                           assert (J22 := bcong _ _ _ _ J19 J20).
                                           apply symS in J22. assert (J23 := tranS _ _ _ J21 J22).
                                           assert (J24 := bcong _ _ _ _ J18 (refS (nex2 c d))).
                                           rewrite (tranS _ _ _ J23 J24) in J9. discriminate J9.
                                        apply in_set_singleton_elim in J20; auto. 
                                        assert (J22 := bcong _ _ _ _ J19 J20).
                                        apply symS in J22. assert (J23 := tranS _ _ _ J21 J22).
                                        assert (J24 := tranS _ _ _ J23 J1).
                                        assert (J25 := tranS _ _ _ J13 J24).
                                        apply symS in J25. rewrite J25 in J4. discriminate J4. 
                               (* {e, c}{e, a} = {ee, ea, ce ca} = {e, a, c, ca} *)
                               split.
                                  apply brel_set_false_intro; auto. 
                                  left. apply brel_subset_false_intro; auto.
                                  exists a. split.
                                     apply (in_set_bop_lift_intro_v2 _ _ a (nex2 a b) a); auto.
                                        compute. rewrite refS; auto.
                                        compute. rewrite refS. case_eq(rS a (nex2 c d)); intro J19; auto.
                                        compute. rewrite J18. rewrite J3. auto. 
                                  apply brel_set_false_intro; auto.
                                  left. apply brel_subset_false_intro; auto.
                                  exists (bS c (nex2 c d)). split.
                                     apply in_set_bop_lift_intro; auto.
                                        compute. rewrite refS. case_eq(rS c (nex2 a b)); intro J19; auto. 
                                        compute. rewrite refS. auto. 
                                     compute. case_eq(rS (bS c (nex2 c d)) (nex2 c d)); intro J19; case_eq(rS (bS c (nex2 c d)) a); intro J20; auto.
                                        apply symS in J20. apply symS in J10. rewrite (tranS _ _ _ J20 J10) in J18. discriminate J18.  
                                        rewrite (tranS _ _ _ J10 J19) in J7. discriminate J7.
                                        apply symS in J20. apply symS in J10. rewrite (tranS _ _ _ J20 J10) in J18. discriminate J18. 
                          (* {d}{(nex2 c d)} = {d(nex2 c d)}*)
                          compute. rewrite J16, J17.
                               rewrite (brel_symmetric_implies_dual _ _ symS _ _ J16). rewrite (brel_symmetric_implies_dual _ _ symS _ _ J17). auto. 
                         (* {e}{a} = {ea} *)                         
                         split.
                            apply brel_set_false_intro; auto.
                            right. apply brel_subset_false_intro; auto.
                            exists (nex2 a b). split. 
                               compute. rewrite refS; auto.
                               case_eq(in_set rS (bop_lift rS bS ((nex2 a b) :: nil) (a :: nil)) (nex2 a b)); intro J16; auto. 
                                  apply in_set_bop_lift_elim in J16; auto. destruct J16 as [x [y [[J16 J17] J18]]].
                                  apply in_set_cons_elim in J16; auto. apply in_set_cons_elim in J17; auto.
                                  destruct J16 as[J16 | J16]; destruct J17 as[J17 | J17].
                                     assert (J19 := bcong _ _ _ _ J16 J17). apply symS in J19. rewrite (tranS _ _ _ J18 J19) in J14. discriminate J14.
                                  compute in J17. discriminate J17.
                                  compute in J16. discriminate J16.
                                  compute in J17. discriminate J17.
                            apply brel_set_false_intro; auto.
                            right. apply brel_subset_false_intro; auto.
                            exists a. split. 
                               compute. rewrite refS; auto.
                               case_eq(in_set rS (bop_lift rS bS ((nex2 a b) :: nil) (a :: nil)) a); intro J16; auto. 
                                  apply in_set_bop_lift_elim in J16; auto. destruct J16 as [x [y [[J16 J17] J18]]].
                                  apply in_set_cons_elim in J16; auto. apply in_set_cons_elim in J17; auto.
                                  destruct J16 as[J16 | J16]; destruct J17 as[J17 | J17].
                                     assert (J19 := bcong _ _ _ _ J16 J17). apply symS in J19. rewrite (tranS _ _ _ J18 J19) in J15. discriminate J15.
                                  compute in J17. discriminate J17.
                                  compute in J16. discriminate J16.
                                  compute in J17. discriminate J17.
                      (* {(nex2 a b)}{(nex2 c d), b} = {(nex2 a b)(nex2 c d), (nex2 a b)b} = {(nex2 a b), b} *)
                      split.
                         apply brel_set_false_intro; auto.
                         left. apply brel_subset_false_intro; auto.
                         exists (bS (nex2 a b) b). split. 
                             apply in_set_bop_lift_intro; auto.                          
                                compute. rewrite refS; auto. 
                                compute. rewrite refS.
                                case_eq(rS b (nex2 c d)); intro J13; auto.
                                compute. rewrite (brel_symmetric_implies_dual _ _ symS _ _ J5). auto. 
                         apply brel_set_false_intro; auto.
                         left. apply brel_subset_false_intro; auto.
                         exists (nex2 a b). split.
                            apply (in_set_bop_lift_intro_v2 _ _ (nex2 a b) (nex2 a b) (nex2 c d)); auto. 
                               compute. rewrite refS; auto. 
                               compute. rewrite refS. auto.
                               compute. rewrite (brel_symmetric_implies_dual _ _ symS _ _ J4).
                               assert (J13 : rS (nex2 a b) (nex2 c d) = false).
                                  case_eq(rS (nex2 a b) (nex2 c d)); intro J13; auto. apply symS in J13. rewrite (tranS _ _ _ J13 J11) in J12. discriminate J12.                                            rewrite J13; auto.                    
                      (* {(nex2 a b), c}{(nex2 c d)} = {(nex2 a b)(nex2 c d), c(nex2 c d)} = {(nex2 c d), c} *)
                      split.
                         apply brel_set_false_intro; auto.
                         right. apply brel_subset_false_intro; auto.
                         exists (nex2 a b). split. 
                            compute. rewrite refS; auto. 
                            case_eq(in_set rS (bop_lift rS bS ((nex2 a b) :: c :: nil) ((nex2 c d) :: nil)) (nex2 a b)); intro J13; auto.
                               apply in_set_bop_lift_elim in J13; auto.
                               destruct J13 as [x [y [[J13 J14] J15]]].
                               apply in_set_cons_elim in J13; auto. apply in_set_cons_elim in J14; auto.
                               destruct J13 as [J13 | J13]; destruct J14 as [J14 | J14].
                                  assert (J16 := bcong _ _ _ _ J13 J14). apply symS in J16.
                                  rewrite (tranS _ _ _ J15 J16) in J11. discriminate J11. 
                                  compute in J14. discriminate J14. 
                                  apply in_set_singleton_elim in J13; auto. (***********)
                                  assert (J16 := bcong _ _ _ _ J13 J14). apply symS in J16.
                                  assert (J17 := tranS _ _ _ J15 J16). apply symS in J17.
                                  case_eq(rS c (nex2 a b)); intro J18.
                                     assert (J19 := bcong _ _ _ _ J18 (refS (nex2 c d))).
                                     assert (J20 := tranS _ _ _ J10 J19).
                                     apply symS in J12. rewrite (tranS _ _ _ J20 J12) in J7. discriminate J7.
                                     rewrite (tranS _ _ _ J10 J17) in J18. discriminate J18. 
                                  compute in J14. discriminate J14. 
                         apply brel_set_false_intro; auto. 
                         left. apply brel_subset_false_intro; auto.
                         exists c. split.
                            apply (in_set_bop_lift_intro_v2 _ _ c c (nex2 c d)); auto. 
                               compute. rewrite refS. case_eq(rS c (nex2 a b)); intro J13; auto.
                               compute. rewrite refS; auto.
                      compute. rewrite J7; auto.
                      (* J11 : rS (nex2 a b) (bS (nex2 a b) (nex2 c d)) = false, J12 : rS (nex2 c d) (bS (nex2 a b) (nex2 c d)) = true*)
                      (* {(nex2 a b)} {(nex2 c d)} *)        
                      compute. rewrite J11, J12.
                         rewrite (brel_symmetric_implies_dual _ _ symS _ _ J11). rewrite (brel_symmetric_implies_dual _ _ symS _ _ J12). auto. 
                   (* J9 : rS (nex2 c d) (bS c (nex2 c d)) = false   J10 : rS c (bS c (nex2 c d)) =  false*)
                   compute. rewrite J9, J10.
                      rewrite (brel_symmetric_implies_dual _ _ symS _ _ J9). rewrite (brel_symmetric_implies_dual _ _ symS _ _ J10). auto.
                (* J5 : rS (nex2 a b) (bS (nex2 a b) b) = false,  J6 : rS b (bS (nex2 a b) b) = false *)                 
                compute. rewrite J5, J6.
                   rewrite (brel_symmetric_implies_dual _ _ symS _ _ J5). rewrite (brel_symmetric_implies_dual _ _ symS _ _ J6). auto. 
          (* J2 : rS (bS c d) c = false *)           
          compute.  rewrite NR. rewrite J2. auto.
       (* J1 : rS (bS a b) b = false *)           
       compute.  rewrite NL. rewrite J1. auto. 
Defined.


(* end selectivity *)



(* bottoms 

Lemma bop_intersect_somthing_is_finite (wS : S) (selS : bop_selective S rS bS) (commS : bop_commutative S rS bS) :
      something_is_finite (finite_set S) (brel_set rS) (bop_lift rS bS).
Proof. exact (exists_ann_implies_something_is_finite _ _ _ 
              bop_lift_congruence 
              (brel_set_reflexive _ _ refS symS)
              (brel_set_symmetric _ rS) 
              (brel_set_transitive  _ _ refS symS tranS)
              (bop_lift_commutative commS)
              (bop_lift_idempotent selS) 
              (λ l : finite_set S, if brel_set rS nil l then wS :: nil else nil)
              (brel_set_not_trivial S rS wS)
              bop_lift_exists_ann). 
Defined.

*)

End Theory.



Section ACAS.

Section ACAS_Proofs.

Definition bop_lift_commutative_decide (S : Type) (eq: brel S) (b: binary_op S)
        (refS : brel_reflexive S eq) (symS : brel_symmetric S eq) (trnS : brel_transitive S eq)
        (cong_b : bop_congruence S eq b) (cD : bop_commutative_decidable S eq b) := 
match cD with
| inl c  => inl (bop_lift_commutative S eq b refS trnS symS cong_b c)                               
| inr nc => inr (bop_lift_not_commutative S eq b nc)
end .

Definition bop_lift_idempotent_decide (S : Type) (eq: brel S) (b: binary_op S)
        (refS : brel_reflexive S eq) (symS : brel_symmetric S eq) (trnS : brel_transitive S eq)
        (cong_b : bop_congruence S eq b) (sD : bop_selective_decidable S eq b) :=
match sD with
| inl sel  => inl (bop_lift_idempotent S eq b refS trnS symS cong_b sel)                               
| inr nsel => inr (bop_lift_not_idempotent S eq b refS trnS symS cong_b nsel)                               
end.

Definition bop_lift_exists_id_decide (S : Type) (eq: brel S) (wS : S) (b: binary_op S)
        (refS : brel_reflexive S eq) (symS : brel_symmetric S eq) (trnS : brel_transitive S eq)
        (cong_b : bop_congruence S eq b) (iD : bop_exists_id_decidable S eq b) :=
match iD with
| inl id  => inl (bop_lift_exists_id S eq b refS trnS symS cong_b id)                               
| inr nid => inr (bop_lift_not_exists_id S eq b refS trnS symS wS nid)                               
end.

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


Definition sg_lift_proofs (S: Type)
           (eq : brel S)
           (b : binary_op S)
           (eqvP : eqv_proofs S eq)
           (wS : S)
           (f : S -> S)
           (nt : brel_not_trivial S eq f)
           (ex2_d : brel_exactly_two_decidable S eq)           
           (bP : sg_proofs S eq b) : sg_proofs (finite_set S) (brel_set eq) (bop_lift eq b)
:=
let refS := A_eqv_reflexive S eq eqvP    in
let symS := A_eqv_symmetric S eq eqvP    in
let trnS := A_eqv_transitive S eq eqvP   in
let cong_b := A_sg_congruence S eq b bP  in
let asso_b := A_sg_associative S eq b bP in
{|
  A_sg_associative      :=  bop_lift_associative S eq b refS trnS symS cong_b asso_b 
; A_sg_congruence       :=  bop_lift_congruence S eq b refS trnS symS cong_b  
; A_sg_commutative_d    :=  bop_lift_commutative_decide S eq b refS symS trnS cong_b (A_sg_commutative_d S eq b bP)
; A_sg_selective_d      :=  bop_lift_selective_decide S eq b refS symS trnS cong_b asso_b
                                                      (A_sg_is_left_d S eq b bP)
                                                      (A_sg_is_right_d S eq b bP)
                                                      (A_sg_idempotent_d S eq b bP)
                                                      ex2_d 
; A_sg_idempotent_d     :=  bop_lift_idempotent_decide S eq b refS symS trnS cong_b (A_sg_selective_d S eq b bP)
; A_sg_is_left_d        :=  inr (bop_lift_not_is_left S eq b wS)
; A_sg_is_right_d       :=  inr (bop_lift_not_is_right S eq b wS)
; A_sg_left_cancel_d    :=  inr (bop_lift_not_left_cancellative S eq b wS f nt) 
; A_sg_right_cancel_d   :=  inr (bop_lift_not_right_cancellative S eq b wS f nt) 
; A_sg_left_constant_d  :=  inr (bop_lift_not_left_constant S eq b wS)
; A_sg_right_constant_d :=  inr (bop_lift_not_right_constant S eq b wS)
; A_sg_anti_left_d      :=  inr (bop_lift_not_anti_left S eq b)
; A_sg_anti_right_d     :=  inr (bop_lift_not_anti_right S eq b)
|}. 

End ACAS_Proofs. 

Definition A_sg_lift : ∀ (S : Type),  A_sg S -> A_sg (finite_set S)
:= λ S sgS,
  let eqv  := A_sg_eqv S sgS in
  let eqvP := A_eqv_proofs S eqv in
  let refS := A_eqv_reflexive _ _ eqvP in
  let symS := A_eqv_symmetric _ _ eqvP in
  let trnS := A_eqv_transitive _ _ eqvP in
  let cngb := A_sg_congruence _ _ _  (A_sg_proofs S sgS) in       
  let eq   := A_eqv_eq S eqv in
  let bS   := A_sg_bop S sgS in
  let wS   := A_eqv_witness S eqv in
   {| 
     A_sg_eqv           := A_eqv_set S eqv
   ; A_sg_bop          := bop_lift eq bS 
   ; A_sg_exists_id_d  :=  bop_lift_exists_id_decide S eq wS bS refS symS trnS cngb (A_sg_exists_id_d S sgS)
   ; A_sg_exists_ann_d :=  inl (bop_lift_exists_ann S eq bS)
   ; A_sg_proofs       := sg_lift_proofs S eq bS eqvP wS 
                                      (A_eqv_new S eqv)
                                      (A_eqv_not_trivial S eqv)
                                      (A_eqv_exactly_two_d S eqv)
                                      (A_sg_proofs S sgS)    
   ; A_sg_ast       := Ast_sg_lift (A_sg_ast S sgS)
   |}.

  
End ACAS.

Section AMCAS. 

Definition A_sg_lift_below_sg {S : Type} (A : @A_below_sg S) : @A_below_sg (finite_set S) :=
  A_classify_sg (A_sg_lift _ (A_cast_up_sg A)). 
  
Definition A_mcas_sg_lift (S : Type) (A : @A_sg_mcas S) : @A_sg_mcas (finite_set S) :=
match A with
| A_MCAS_sg B          => A_MCAS_sg (A_sg_lift_below_sg B)
| A_MCAS_sg_Error sl1  => A_MCAS_sg_Error sl1
end.

End AMCAS.



Section CAS.


Definition bop_lift_commutative_check {S : Type} (cD: @check_commutative S) : @check_commutative (finite_set S) := 
match cD with
| Certify_Commutative              => Certify_Commutative
| Certify_Not_Commutative (s1, s2) => Certify_Not_Commutative (s1 :: nil, s2 :: nil)
end.

Definition bop_lift_idempotent_check {S : Type} (idD: @check_selective S) : @check_idempotent (finite_set S) := 
match idD with
| Certify_Selective  => Certify_Idempotent
| Certify_Not_Selective (s1, s2) => Certify_Not_Idempotent (s1 :: s2 :: nil) 
end.

Definition bop_lift_exists_id_check {S : Type} (idD: @check_exists_id S) : @check_exists_id (finite_set S) := 
match idD with
| Certify_Exists_Id id  => Certify_Exists_Id (id :: nil) 
| Certify_Not_Exists_Id => Certify_Not_Exists_Id
end.

Definition bop_lift_selective_check {S : Type}
           (eq : brel S) (bS : binary_op S)
           (ilD: @check_is_left S)
           (irD: @check_is_right S)
           (idD: @check_idempotent S)
           (exD: @check_exactly_two S)                      
  : @check_selective (finite_set S) := 
match ilD with
| Certify_Is_Left  => Certify_Selective 
| Certify_Not_Is_Left (a, b)  =>
  match irD with
  | Certify_Is_Right  => Certify_Selective 
  | Certify_Not_Is_Right (c, d) =>
    match idD  with
    | Certify_Idempotent  =>
      match exD with
      | Certify_Exactly_Two _  => Certify_Selective 
      | Certify_Not_Exactly_Two nex2 =>
        Certify_Not_Selective (lift_not_selective S eq bS a b c d nex2)
      end 
    | Certify_Not_Idempotent e => Certify_Not_Selective (e :: nil, e :: nil) 
    end 
  end 
end.


Definition sg_lift_certs (S: Type)
           (eq : brel S) 
           (wS : S)
           (f : S -> S)
           (ex2_d : @check_exactly_two S)
           (bS : binary_op S)
           (bP : @sg_certificates S) : @sg_certificates (finite_set S)
:= {|
  sg_associative      :=  Assert_Associative  
; sg_congruence       :=  Assert_Bop_Congruence  
; sg_commutative_d    :=  bop_lift_commutative_check (sg_commutative_d bP)
; sg_selective_d      :=  bop_lift_selective_check eq bS 
                                                   (sg_is_left_d bP)
                                                   (sg_is_right_d bP)
                                                   (sg_idempotent_d bP)
                                                   ex2_d 
; sg_idempotent_d     :=  bop_lift_idempotent_check (sg_selective_d bP)
; sg_is_left_d        :=  Certify_Not_Is_Left (wS :: nil, nil) 
; sg_is_right_d       :=  Certify_Not_Is_Right (nil, wS :: nil) 
; sg_left_cancel_d    :=  Certify_Not_Left_Cancellative (nil, (wS :: nil, (f wS) :: nil))
; sg_right_cancel_d   :=  Certify_Not_Right_Cancellative (nil, (wS :: nil, (f wS) :: nil))
; sg_left_constant_d  :=  Certify_Not_Left_Constant (wS :: nil, (wS ::nil, nil)) 
; sg_right_constant_d :=  Certify_Not_Right_Constant (wS :: nil, (wS ::nil, nil)) 
; sg_anti_left_d      :=  Certify_Not_Anti_Left (nil, nil) 
; sg_anti_right_d     :=  Certify_Not_Anti_Right (nil, nil)
|}. 


Definition sg_lift : ∀ {S : Type},  @sg S -> @sg (finite_set S)
:= λ {S} sgS,
  let eqv := sg_eqv sgS in
  let eq := eqv_eq eqv in
  let bS := sg_bop sgS in 
   {| 
     sg_eqv        := eqv_set eqv
   ; sg_bop       := bop_lift eq bS 
   ; sg_exists_id_d      :=  bop_lift_exists_id_check (sg_exists_id_d sgS)  
   ; sg_exists_ann_d     :=  Certify_Exists_Ann nil 
   ; sg_certs     := sg_lift_certs S eq (eqv_witness eqv) (eqv_new eqv) (eqv_exactly_two_d eqv) bS (sg_certs sgS) 

   ; sg_ast       := Ast_sg_lift (sg_ast sgS)
   |}. 

  
End CAS.

Section MCAS.

Definition sg_lift_below_sg {S : Type} (A : @below_sg S) : @below_sg (finite_set S) :=
  classify_sg (sg_lift (cast_up_sg A)). 
  
Definition mcas_sg_lift (S : Type) (A : @sg_mcas S) : @sg_mcas (finite_set S) :=
match A with
| MCAS_sg B          => MCAS_sg (sg_lift_below_sg B)
| MCAS_sg_Error sl1  => MCAS_sg_Error sl1
end.

End MCAS.


Section Verify.



Lemma correct_bop_lift_commutative_check : 
  ∀ (S : Type)
     (eq : brel S)
     (b : binary_op S)
     (eqP : eqv_proofs S eq)
     (cong_b : bop_congruence S eq b)
     (cD : bop_commutative_decidable S eq b),

     p2c_commutative_check (finite_set S) (brel_set eq) (bop_lift eq b)
                      (bop_lift_commutative_decide S eq b
                           (A_eqv_reflexive S eq eqP)
                           (A_eqv_symmetric S eq eqP)
                           (A_eqv_transitive S eq eqP) cong_b cD)
    =
    bop_lift_commutative_check (p2c_commutative_check S eq b cD).
Proof. intros. destruct cD as [C | [[s1 s2] NC] ]; compute; auto. Qed. 
  
Lemma correct_bop_lift_selective_check : 
  ∀ (S : Type)
     (eq : brel S)
     (b : binary_op S)
     (eqP : eqv_proofs S eq)
     (asso_b : bop_associative S eq b)
     (cong_b : bop_congruence S eq b)
     (ilD : bop_is_left_decidable S eq b)
     (irD : bop_is_right_decidable S eq b)      
     (iD : bop_idempotent_decidable S eq b)
     (exD : brel_exactly_two_decidable S eq), 

    p2c_selective_check (finite_set S) (brel_set eq) (bop_lift eq b)
                    (bop_lift_selective_decide S eq b
                              (A_eqv_reflexive S eq eqP)
                              (A_eqv_symmetric S eq eqP)
                              (A_eqv_transitive S eq eqP) cong_b asso_b ilD irD iD exD)
    =
    bop_lift_selective_check eq b
                             (p2c_is_left_check S eq b ilD)
                             (p2c_is_right_check S eq b irD)
                             (p2c_idempotent_check S eq b iD)
                             (p2c_exactly_two_check S eq exD).
Proof. intros.
       destruct ilD as [IL | [[s1 s2] NIL] ];
       destruct irD as [IR | [[s3 s4] NIR] ];
       destruct iD  as [IDEM | [s5 NIDEM] ];
       destruct exD as [ [[s6 s7] AT] | [nex2 NAT] ]; simpl; auto. 
Qed.

Lemma correct_bop_lift_idempotent_check : 
  ∀ (S : Type)
     (eq : brel S)
     (b : binary_op S)
     (eqP : eqv_proofs S eq)
     (cong_b : bop_congruence S eq b)
     (sD : bop_selective_decidable S eq b),

    p2c_idempotent_check (finite_set S) (brel_set eq) (bop_lift eq b)
                         (bop_lift_idempotent_decide S eq b
                                                     (A_eqv_reflexive S eq eqP)
                                                     (A_eqv_symmetric S eq eqP)
                                                     (A_eqv_transitive S eq eqP) cong_b sD)
    =
    bop_lift_idempotent_check (p2c_selective_check S eq b sD).
Proof. intros. destruct sD as [ SEL | [ [s1 s2] NSEL ] ]; compute; auto. Qed. 

Lemma correct_bop_lift_exists_id_check : 
  ∀ (S : Type)
     (eq : brel S)
     (b : binary_op S)
     (eqP : eqv_proofs S eq)
     (wS : S) 
     (cong_b : bop_congruence S eq b)
     (idD : bop_exists_id_decidable S eq b),

    p2c_exists_id_check (finite_set S) (brel_set eq) (bop_lift eq b)
                        (bop_lift_exists_id_decide S eq wS b
                                                   (A_eqv_reflexive S eq eqP)
                                                   (A_eqv_symmetric S eq eqP)
                                                   (A_eqv_transitive S eq eqP) cong_b idD)
    =
    bop_lift_exists_id_check (p2c_exists_id_check S eq b idD).
Proof. intros. destruct idD as [ [id  ID] | NID ]; compute; auto. Qed. 


Lemma correct_sg_lift_certs 
  (S : Type)
  (eq : brel S)
  (wS : S)
  (f : S -> S)
  (bS : binary_op S)
  (nt : brel_not_trivial S eq f)
  (ex2_d : brel_exactly_two_decidable S eq)
  (eqvP : eqv_proofs S eq)   
  (sgP : sg_proofs S eq bS) :
  P2C_sg (brel_set eq)
         (bop_lift eq bS)
         (sg_lift_proofs S eq bS eqvP wS f nt ex2_d  sgP) 
  =  
  sg_lift_certs S eq wS f (p2c_exactly_two_check S eq ex2_d) bS (P2C_sg eq bS sgP).
Proof. unfold sg_lift_proofs, sg_lift_certs, P2C_sg. simpl. 
       rewrite correct_bop_lift_idempotent_check; auto.
       rewrite correct_bop_lift_selective_check; auto. 
       rewrite correct_bop_lift_commutative_check; auto.
Qed.   
  
Theorem correct_sg_lift  (S : Type) (sgS : A_sg S) : 
         sg_lift (A2C_sg sgS) 
         = 
         A2C_sg (A_sg_lift S sgS). 
Proof. 
       unfold A2C_sg, sg_lift, A_sg_lift. simpl.
       rewrite correct_eqv_set.
       rewrite correct_sg_lift_certs.
       rewrite correct_bop_lift_exists_id_check; 
       reflexivity. 
Qed.

Theorem correct_sg_lift_below_sg (S: Type) (A : @A_below_sg S) : 
  sg_lift_below_sg (A2C_below_sg A)
  =
  A2C_below_sg (A_sg_lift_below_sg A).
Proof. destruct A; unfold sg_lift_below_sg, A_sg_lift_below_sg. 
       - simpl. rewrite correct_sg_lift. 
         rewrite correct_classify_sg.
         reflexivity.
       - rewrite <- correct_classify_sg.
         rewrite correct_cast_up_sg.
         rewrite correct_sg_lift.
         reflexivity.
Qed.

Theorem correct_mcas_sg_lift (S : Type) (A : @A_sg_mcas S) :
         mcas_sg_lift _ (A2C_sg_mcas A) 
         = 
         A2C_sg_mcas (A_mcas_sg_lift S A).
Proof. unfold mcas_sg_lift, A_mcas_sg_lift.
       destruct A; simpl.
       - reflexivity.
       - rewrite correct_sg_lift_below_sg.
         reflexivity.
Qed. 

End Verify.

