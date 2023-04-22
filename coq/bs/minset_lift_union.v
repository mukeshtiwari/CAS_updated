Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.

Require Import CAS.coq.theory.set. 

Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.eqv.theory. 
Require Import CAS.coq.eqv.set.
Require Import CAS.coq.eqv.minset.

Require Import CAS.coq.uop.properties.

Require Import CAS.coq.or.properties.
Require Import CAS.coq.or.structures.
Require Import CAS.coq.or.theory.
Require Import CAS.coq.or.set_lte. 

Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures.
Require Import CAS.coq.sg.cast_up. 
Require Import CAS.coq.sg.union.
Require Import CAS.coq.sg.minset_union.
Require Import CAS.coq.sg.lift.
Require Import CAS.coq.sg.minset_lift.

Require Import CAS.coq.bs.properties.
Require Import CAS.coq.bs.structures.
Require Import CAS.coq.bs.theory.
Require Import CAS.coq.bs.reduce. 
Require Import CAS.coq.bs.minset_union_lift.  (* for bounded proofs. *) 

Require Import CAS.coq.or_sg.properties.
Require Import CAS.coq.or_sg.structures.
Require Import CAS.coq.or_sg.theory. 


(* should move this to po as a combinator! *) 
Definition set_lte {S : Type} (eq lte : brel S) (X Y: finite_set S) := 
  ∀ y : S,  in_set eq Y y = true -> 
  {x : S & (in_set eq X x = true) * (lte x y = true) }. 

Section Computation.


End Computation.   

Section Theory.  

Section Lift_Union.

(*
   minset_lift_union (S, <=, (x)) = (P(S), (+), (x')) 
   where 
   (+)  = min(<=, lift(x)) 
   (x') = min(<=, union)
   That is, 
   X (+) Y = min(<=, {x (x) y | x in X, y in Y}
   X (x') Y = min(<=, X union Y)

   NOTE: The construction (currently) requires (x) to be commutative, idempotent, and not selective. 

A*[i,j] = (+)_{p in P(i,j)} w(p) 
        = (+)_{p in P(i,j)} min(<=, U_{e in p} w(e))
        = (+)_{p in {p_1, .... p_k}} min(<=, U_{e in p} w(e))
        = min(<=, U_{e in p_1} w(e)) (+) ... (+) min(<=, U_{e in p_k} w(e))
        = (U_{e in p_1} w(e)) (+) ... (+) (U_{e in p_k} w(e))
        = min(<=, {w(e_1) (x) w(e_2) ... (x) w(e_k) | e_1 in p_1, ... e_k in p_k})

or

A*[i,j] = (+)_{p in P(i,j)} w(p) 
        = (+)_{p in P(i,j)} min(<=, U_{e in p} w(e))
        = (+)_{p in P(i,j)} U_{e in p} w(e)   
        = (+)_{p in P(i,j)} {w'(e)| e in p}   (when w(e) = {w'(e)}, so each arc weight is a singleton) 
        = min(<=, (lift (x))_{p in P(i,j)} {w'(e)| e in p})  (* need good notation for this operation *)
        
*) 

    

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


Variable bS : binary_op S. 
Variable bCong : bop_congruence S rS bS. 
Variable bAss : bop_associative S rS bS.

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
Notation "a [<=] b"   := (set_lte rS lteS a b) (at level 15).
Notation "a [=MS] b"  := (brel_minset rS lteS a b = true)        (at level 15).
Notation "a [<>MS] b" := (brel_minset rS lteS a b = false)       (at level 15).
Notation "[ms] x" := (uop_minset lteS x) (at level 15).

Notation "a [U] b" := (bop_union rS a b)         (at level 15).
Notation "a <U> b" := (bop_minset_union rS lteS a b)         (at level 15).
Notation "a [^] b" := (bop_lift rS bS a b)         (at level 15).
Notation "a <^> b" := (bop_minset_lift S rS lteS bS a b)         (at level 15).


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
Definition minset_lift_uop_invariant := minset_lift_uop_invariant S rS refS symS tranS lteS lteCong lteRefl lteTrans bS bCong. 


Lemma subset_lemma_1 (Z X : finite_set S) (a : S):
  brel_subset rS (a :: Z) X = true -> brel_subset rS Z X = true.
Proof. intro H.   
       assert (F := brel_subset_elim _ _ symS tranS _ _ H). 
       apply brel_subset_intro; auto.
       intros w G. 
       assert (J : w [in] (a :: Z)). apply in_set_cons_intro; auto.
       exact (F _ J).
Qed. 

(* assume * is idempotent: 

(X [^] X) 
 = { w * y | w in X, y in X} 
 = { w * w | w in X} 
   [U] { w * y | w in X, y in X, w <> y, w*y not in { w * w | w in X}}  
 = X [U] { w * y | w in X, y in X, w <> y, w*y not in X} 

partition
     : ∀ A : Type, (A → bool) → list A → list A * list A
partition f (X [^] X) = (X, { w * y | w in X, y in X, w <> y, w*y not in X})


 *)


Lemma partition_lemma (f : S -> bool) (fcong : ∀ (s t : S),  s [=] t -> (f s) = (f t)) (X : finite_set S) :
∀ (Y Z : finite_set S),  
  partition f X = (Y, Z) ->
  (∀ x : S, x [in] X -> f x = true -> x [in] Y) *
  (∀ x : S, x [in] Y -> (f x = true) * (x [in] X)) *  
  (∀ x : S, x [in] X -> f x = false -> x [in] Z) *   
  (∀ x : S, x [in] Z -> (f x = false) * (x [in] X)).   
Proof. induction X.
       ++ intros Y Z A. compute in A. inversion A. split. split. split.
          intros x B. compute in B. discriminate B. 
          intros x B. compute in B. discriminate B.
          intros x B. compute in B. discriminate B.
          intros x B. compute in B. discriminate B.
       ++ case_eq(f a); intro K. 
          +++ intros Y Z A. 
              unfold partition in A. fold (partition f X) in A.
              rewrite K in A.
              case_eq(partition f X); intros W U J.
              rewrite J in A. inversion A.
              destruct (IHX _ _ J) as [[[B C] D] E].
              split.
              ++++ split.
                   +++++ split.
                         ++++++ intros x F G.
                                apply in_set_cons_intro; auto. 
                                apply in_set_cons_elim in F; auto.
                                destruct F as [F | F].
                                +++++++ left. exact F. 
                                +++++++ right. apply B; auto. 
                         ++++++ intros x F.
                                apply in_set_cons_elim in F; auto.
                                destruct F as [F | F].
                                +++++++ split. rewrite (fcong _ _ F) in K. exact K.
                                        apply in_set_cons_intro; auto. 
                                +++++++ destruct (C _ F) as [G H]. 
                                        split; auto. apply in_set_cons_intro; auto. 
                   +++++ intros x F G.
                         apply in_set_cons_elim in F; auto.
                         destruct F as [F | F].
                         ++++++ rewrite (fcong _ _ F) in K. rewrite G in K. discriminate K. 
                         ++++++ rewrite <- H1. exact (D _ F G).
              ++++ intros x F. rewrite <- H1 in F.
                   destruct (E _ F) as [G H].
                   split; auto. apply in_set_cons_intro; auto. 
          +++ intros Y Z A. 
              unfold partition in A. fold (partition f X) in A.
              rewrite K in A.
              case_eq(partition f X); intros W U J.
              rewrite J in A. inversion A.
              destruct (IHX _ _ J) as [[[B C] D] E].
              split.
              ++++ split.
                   +++++ split.
                         ++++++ intros x F G.
                                apply in_set_cons_elim in F; auto.
                                destruct F as [F | F].
                                +++++++ rewrite (fcong _ _ F) in K. rewrite G in K. discriminate K. 
                                +++++++ rewrite <- H0. exact (B _ F G).
                         ++++++ intros x F. rewrite <- H0 in F. 
                                destruct (C _ F) as [G H]. split; auto. 
                                apply in_set_cons_intro; auto. 
                   +++++ intros x F G.
                         apply in_set_cons_elim in F; auto.
                         destruct F as [F | F].
                         ++++++ apply in_set_cons_intro; auto. 
                         ++++++ assert (I := D _ F G).
                                apply in_set_cons_intro; auto. 
              ++++ intros x F.
                   apply in_set_cons_elim in F; auto.
                   destruct F as [F | F].
                   +++++ split. rewrite (fcong _ _ F) in K. exact K.
                         apply in_set_cons_intro; auto. 
                   +++++ destruct (E _ F) as [G H]. 
                         split; auto.
                         apply in_set_cons_intro; auto. 
Qed. 

Lemma in_set_cong (X : finite_set S) : ∀ (s t : S),  s [=] t -> (in_set rS X s) = (in_set rS X t).
Proof. intros s t A.
       case_eq(in_set rS X s); intro B; case_eq(in_set rS X t); intro C; auto. 
       + assert (D := in_set_right_congruence _ _ symS tranS _ _ X A).
         rewrite (D B) in C. discriminate C. 
       + assert (D := in_set_right_congruence _ _ symS tranS _ _ X (symS _ _ A)).
         rewrite (D C) in B. discriminate B. 
Qed. 
  

Lemma partition_union
      (f : S -> bool)
      (fcong : ∀ (s t : S),  s [=] t -> (f s) = (f t))
      (X Y Z : finite_set S) :
        partition f X = (Y, Z) -> X [=S] (Y [U] Z).
Proof. intro A.
       destruct (partition_lemma f fcong X Y Z A) as [[[B C] D] E].
       apply brel_set_intro_prop; auto; split; intros a F.
       + apply in_set_bop_union_intro; auto.
         case_eq(f a); intro G. 
         ++ left. exact (B _ F G).
         ++ right. exact (D _ F G).
       + apply in_set_bop_union_elim in F; auto. 
         destruct F as [F | F].
         ++ destruct (C _ F) as [_ G]. exact G. 
         ++ destruct (E _ F) as [_ G]. exact G. 
Qed.




Lemma partition_in_set_lemma (idem : bop_idempotent S rS bS)
                   (LI : os_left_increasing lteS bS)
                   (X Y Z : finite_set S) :
      partition (in_set rS X) (X [^] X) = (Y, Z) -> (X [=S] Y) * (X [<=] Z).
Proof. intro A.
       destruct (partition_lemma (in_set rS X) (in_set_cong X) (X [^] X) Y Z A) as [[[B C] _] E].
       split. 
       + apply brel_set_intro_prop; auto; split; intros a F. 
         ++ assert (G : a [in] (X [^] X)).
               assert (H := idem a).
               apply (in_set_right_congruence _ _ symS tranS _ _ (X [^] X) H).
               apply in_set_bop_lift_intro; auto. 
            exact (B _ G F). 
         ++ destruct (C _ F) as [G _]. exact G. 
       + intros s F.
         destruct (E _ F) as [G H].
         apply in_set_bop_lift_elim in H; auto. 
         destruct H as [x [y [[I J] K]]].
         exists x.
         rewrite (lteCong _ _ _ _ (refS x) K).
         split. exact I. exact (LI x y).
Qed. 

Notation "[rej] x" := (snd (partition (in_set rS x) (x [^] x))) (at level 15).

Lemma reject_lemma (idem : bop_idempotent S rS bS)
                   (LI : os_left_increasing lteS bS)
                   (X : finite_set S) : (X [^] X) [=S] (X [U] ([rej] X)). 
Proof. case_eq(partition (in_set rS X) (X [^] X)); intros V W A. 
       destruct (partition_in_set_lemma idem LI _ _ _ A) as [B C]. simpl. 
       assert (F := partition_union _ (in_set_cong _) _ _ _ A).
       assert (E := bop_union_congruence _ _ refS symS tranS _ _ _ _ B (set_reflexive W)).
       apply set_symmetric in E.
       exact (set_transitive _ _ _ F E). 
Qed.

Lemma reject_lemma_2
      (idem : bop_idempotent S rS bS)
      (LI : os_left_increasing lteS bS)
      (X : finite_set S) : X [<=] ([rej] X).
       assert (A := partition_in_set_lemma idem LI X). 
       case_eq (partition (in_set rS X) (X [^] X)); intros W V C. 
       destruct (A _ _ C) as [D E].
       simpl. exact E. 
Qed.


Lemma discard_lemma_left
      (idem : bop_idempotent S rS bS)
      (LI : os_left_increasing lteS bS)
      (X Y : finite_set S) : X [<=] (X [^] Y). 
Proof. intros s A. apply in_set_bop_lift_elim in A; auto. 
       destruct A as [x [y [[A B] C]]].
       exists x.
       rewrite (lteCong _ _ _ _ (refS x) C).       
       split. exact A. exact (LI x y).
Qed.

Lemma discard_lemma_right
      (idem : bop_idempotent S rS bS)
      (RI : os_right_increasing lteS bS)
      (X Y : finite_set S) : X [<=] (Y [^] X).
Proof. intros s A. apply in_set_bop_lift_elim in A; auto. 
       destruct A as [x [y [[A B] C]]].
       exists y.
       rewrite (lteCong _ _ _ _ (refS y) C).       
       split. exact B. exact (RI y x).
Qed.


Lemma lift_union_left_distributive (X Y Z : finite_set S) : 
  (X [^] (Y [U] Z)) [=S] ((X [^] Y) [U] (X [^] Z)). 
Proof. apply brel_set_intro_prop; auto. split; intros a A. 
       + apply in_set_bop_lift_elim in A; auto.
         destruct A as [x [y [[A B] C]]].
         apply in_set_bop_union_intro; auto.
         apply in_set_bop_union_elim in B; auto.
         destruct B as [B | B].
         ++ left. apply (in_set_right_congruence _ _ symS tranS _ _ _ (symS _ _ C)); auto. 
            apply in_set_bop_lift_intro; auto. 
         ++ right. apply (in_set_right_congruence _ _ symS tranS _ _ _ (symS _ _ C)); auto. 
            apply in_set_bop_lift_intro; auto. 
       + apply in_set_bop_union_elim in A; auto. 
         destruct A as [A | A].
         ++ apply in_set_bop_lift_elim in A; auto. 
            destruct A as [x [y [[A B] C]]].
            apply (in_set_right_congruence _ _ symS tranS _ _ _ (symS _ _ C)); auto. 
            apply in_set_bop_lift_intro; auto.
            apply in_set_bop_union_intro; auto. 
         ++ apply in_set_bop_lift_elim in A; auto. 
            destruct A as [x [y [[A B] C]]].
            apply (in_set_right_congruence _ _ symS tranS _ _ _ (symS _ _ C)); auto. 
            apply in_set_bop_lift_intro; auto.
            apply in_set_bop_union_intro; auto. 
Qed. 


Lemma lift_union_right_distributive (X Y Z : finite_set S) : 
  ((Y [U] Z) [^] X) [=S] ((Y [^] X) [U] (Z [^] X)). 
Proof. apply brel_set_intro_prop; auto. split; intros a A. 
       + apply in_set_bop_lift_elim in A; auto.
         destruct A as [x [y [[A B] C]]].
         apply in_set_bop_union_intro; auto.
         apply in_set_bop_union_elim in A; auto.
         destruct A as [A | A].
         ++ left. apply (in_set_right_congruence _ _ symS tranS _ _ _ (symS _ _ C)); auto. 
            apply in_set_bop_lift_intro; auto. 
         ++ right. apply (in_set_right_congruence _ _ symS tranS _ _ _ (symS _ _ C)); auto. 
            apply in_set_bop_lift_intro; auto. 
       + apply in_set_bop_union_elim in A; auto. 
         destruct A as [A | A].
         ++ apply in_set_bop_lift_elim in A; auto. 
            destruct A as [x [y [[A B] C]]].
            apply (in_set_right_congruence _ _ symS tranS _ _ _ (symS _ _ C)); auto. 
            apply in_set_bop_lift_intro; auto.
            apply in_set_bop_union_intro; auto. 
         ++ apply in_set_bop_lift_elim in A; auto. 
            destruct A as [x [y [[A B] C]]].
            apply (in_set_right_congruence _ _ symS tranS _ _ _ (symS _ _ C)); auto. 
            apply in_set_bop_lift_intro; auto.
            apply in_set_bop_union_intro; auto. 
Qed. 

         
Lemma distribution_lemma_1 (X Y Z : finite_set S) : 
  ((X [U] Y) [^] (X [U] Z))
       [=S]
       (((X [^] X) [U] (Y [^] X)) 
        [U]
       ((X [^] Z) [U] (Y [^] Z))). 
Proof. assert (A := lift_union_left_distributive (X [U] Y) X Z). 
       assert (B := lift_union_right_distributive X X Y).
       assert (C := lift_union_right_distributive Z X Y).
       assert (D := bop_union_congruence _ _ refS symS tranS _ _ _ _ B C).
       assert (E := set_transitive _ _ _ A D).
       exact E.        
Qed.

Lemma distribution_lemma_1_5
  (idem : bop_idempotent S rS bS)
  (LI : os_left_increasing lteS bS)
  (X Y Z : finite_set S) : 
  ((X [U] Y) [^] (X [U] Z))
       [=S]
       (((X [U] ([rej] X)) [U] (Y [^] X))
        [U]
       ((X [^] Z) [U] (Y [^] Z))). 
Proof. assert (A := distribution_lemma_1 X Y Z).
       assert (B := reject_lemma idem LI X).
       assert (C := bop_union_congruence _ _ refS symS tranS _ _ _ _ B (set_reflexive (Y [^] X))).       
       assert (D := bop_union_congruence _ _ refS symS tranS _ _ _ _ C (set_reflexive ((X [^] Z) [U] (Y [^] Z)))).               
       exact (set_transitive _ _ _ A D).
Qed.

(* 
      (((X [U] W) [U] P) [U] (Q [U] V))
      [=S]       
      ((X [U] (W [U] P)) [U] (Q [U] V))
      [=S]       
      (X [U] ((W [U] P) [U] (Q [U] V))) 
      [=S]       
      (X [U] (((W [U] P) [U] Q) [U] V))  
      [=S]       
      (X [U] (V [U] ((W [U] P) [U] Q))) 
      [=S]       
      ((X [U] V) [U] ((W [U] P) [U] Q)))   
      [=S]       
      ((X [U] V) [U] (W [U] (P [U] Q))) 
*) 
Lemma shuffle_lemma (X W P Q V : finite_set S) :
      (((X [U] W) [U] P) [U] (Q [U] V))
      [=S]       
      ((X [U] V) [U] (W [U] (P [U] Q))).
Proof. assert (Uassoc := bop_union_associative _ _ refS symS tranS).
       assert (Ucong := bop_union_congruence _ _ refS symS tranS).
       assert (Ucomm := bop_union_commutative _ _ refS symS tranS).       
       assert (A : (((X [U] W) [U] P) [U] (Q [U] V))
                   [=S]       
                   ((X [U] (W [U] P)) [U] (Q [U] V))).
          assert (B := Uassoc X W P).
          assert (C := Ucong _ _ _ _ B (set_reflexive (Q [U] V))). 
          exact C.           
       assert (B : ((X [U] (W [U] P)) [U] (Q [U] V))
                     [=S]       
                   (X [U] ((W [U] P) [U] (Q [U] V)))).
          exact (Uassoc X (W [U] P) (Q [U] V)). 
       assert (C := set_transitive _ _ _ A B).
       assert (D : (X [U] ((W [U] P) [U] (Q [U] V)))
                   [=S]       
                   (X [U] (((W [U] P) [U] Q) [U] V))). 
          assert (E := Uassoc ((W [U] P)) Q V). 
          assert (F := Ucong _ _ _ _ (set_reflexive X) E). 
          apply set_symmetric in F. exact F. 
       assert (E := set_transitive _ _ _ C D).
       assert (F :(X [U] (((W [U] P) [U] Q) [U] V))
                    [=S]
                  (X [U] (V [U] ((W [U] P) [U] Q)))). 
          assert (G := Ucomm ((W [U] P) [U] Q) V). 
          assert (F := Ucong _ _ _ _ (set_reflexive X) G). 
          exact F. 
       assert (G := set_transitive _ _ _ E F).       
       assert (H : (X [U] (V [U] ((W [U] P) [U] Q))) 
                     [=S]       
                   ((X [U] V) [U] ((W [U] P) [U] Q))). 
          assert (I := Uassoc X V ((W [U] P) [U] Q)).
          apply set_symmetric in I. exact I. 
       assert (I := set_transitive _ _ _ G H).
       assert (J : ((X [U] V) [U] ((W [U] P) [U] Q))
                    [=S]
                    ((X [U] V) [U] (W [U] (P [U] Q)))).
          assert (K := Uassoc W P Q). 
          assert (L := Ucong _ _ _ _ (set_reflexive (X [U] V)) K). 
          exact L. 
       assert (K := set_transitive _ _ _ I J).
       exact K.
Qed. 

       
 Lemma distribution_lemma_2
      (idem : bop_idempotent S rS bS)
      (LI : os_left_increasing lteS bS)
      (X Y Z : finite_set S) :
     ((X [U] Y) [^] (X [U] Z))
       [=S]
       ((X [U] (Y [^] Z))
          [U] (([rej] X)
                 [U] ((Y [^] X)
                        [U] (X [^] Z)))). 
Proof. assert (A := distribution_lemma_1_5 idem LI X Y Z).
       assert (B := shuffle_lemma X ([rej] X) (Y [^] X) (X [^] Z) (Y [^] Z)).
       exact (set_transitive _ _ _ A B). 
Qed. 
                                      
Lemma minset_lift_union_left_quasi_distributive
  (idem : bop_idempotent S rS bS)
  (LI : os_left_increasing lteS bS)
  (RI : os_right_increasing lteS bS)
  (X Y Z : finite_set S) :         
  {D : finite_set S &
       ((X [U] Y) [^] (X [U] Z) [=S] ((X [U] (Y [^] Z)) [U] D)) * ((X [U] (Y [^] Z)) [<=] D)}.
Proof. exists (([rej] X)
                 [U] ((Y [^] X)
                        [U] (X [^] Z))). 
       split. 
       + apply distribution_lemma_2; auto. 
       + apply set_lte_lemma2; auto. 
         ++ apply set_lte_lemma; auto. apply reject_lemma_2; auto. 
         ++ apply set_lte_lemma2; auto. 
            +++ apply set_lte_lemma; auto. apply discard_lemma_right; auto.
            +++ apply set_lte_lemma; auto. apply discard_lemma_left; auto. 
Qed. 


(* compare this to minset.fundamental_minset_theorem

Theorem fundamental_minset_theorem (X : finite_set S) : 
   {Z : finite_set S &
        (X [=S] (([ms] X) [U] Z) ) *
        (∀ (s : S), s [in] Z -> {t : S & (t [in] ([ms] X)) * t << s })
   }.


Should this be moved to eqv/minset.v?

Q : do we want <= or << ? 
A : perhaps we want two versions of each fundamental theorem: 
    one with antisymmetry (using [<=]) and one without (using [<<])  

*) 
Lemma second_fundamental_minset_theorem (anti : brel_antisymmetric S rS lteS)
           (Y Z : finite_set S) : (Y [<=] Z) -> ([ms] (Y [U] Z)) [=S] ([ms] Y). 
Proof. intros A.
       apply brel_set_intro_prop; auto.
       split; intros a B. 
       + apply in_minset_intro; auto.
         apply in_minset_elim in B; auto. 
         destruct B as [B C].
         apply in_set_bop_union_elim in B; auto. 
         destruct B as [B | B]. 
         ++ split; auto.
            intros t D.
            apply C; auto.             
            apply in_set_bop_union_intro; auto.
         ++ split.
            +++ assert (D := A a B).
                destruct D as [t [E F]].
                assert (G : t [in] (Y [U] Z)). apply in_set_bop_union_intro; auto. 
                assert (H := C t G).
                apply below_false_elim in H. destruct H as [H | H].
                ++++ rewrite H in F. discriminate F. 
                ++++ assert (I := anti _ _ F H).
                     apply (in_set_right_congruence _ _ symS tranS _ _ Y I); auto.                      
            +++ intros t D.
                apply C; auto.
                apply in_set_bop_union_intro; auto.                
       + apply in_minset_intro; auto.
         apply in_minset_elim in B; auto. 
         destruct B as [B C]. split.
         ++ apply in_set_bop_union_intro; auto.
         ++ intros t D.
            apply in_set_bop_union_elim in D; auto.
            destruct D as [D | D].
            +++ apply C; auto. 
            +++ assert (E := A t D).
                case_eq(below lteS a t); intro F; auto.
                destruct E as [u [G H]].
                assert (I := C u G).
                assert (J := below_pseudo_transitive_left _ _ lteTrans _ _ _ H F).
                rewrite J in I. discriminate I. 
Qed. 

Lemma minset_lift_union_left_distributive_weak
      (anti : brel_antisymmetric S rS lteS)
      (idem : bop_idempotent S rS bS)
      (LI : os_left_increasing lteS bS)
      (RI : os_right_increasing lteS bS)
      (X Y Z : finite_set S) :
      ([ms] (X [U] (Y [^] Z))) [=S] ([ms] ((X [U] Y) [^] (X [U] Z))). 
Proof. apply set_symmetric. 
       destruct (minset_lift_union_left_quasi_distributive idem LI RI X Y Z) as [D [C E]].
       assert (F := second_fundamental_minset_theorem anti _ _ E).
       assert (G := uop_minset_congruence_weak _ _ C). 
       assert (I := set_transitive _ _ _ G F).
       exact I. 
Qed.

Lemma minset_lift_union_right_distributive_weak
      (anti : brel_antisymmetric S rS lteS)
      (idem : bop_idempotent S rS bS)
      (LI : os_left_increasing lteS bS)
      (RI : os_right_increasing lteS bS)
      (X Y Z : finite_set S) :
      ([ms] ((Y [^] Z) [U] X)) [=S] ([ms] ((Y [U] X) [^] (Z [U] X))). 
Proof. assert (A := minset_lift_union_left_distributive_weak anti idem LI RI X Y Z).
       assert (B := bop_union_commutative _ _ refS symS tranS).
       assert (C := B (Y [^] Z) X).
       apply uop_minset_congruence_weak in C. 
       assert (D := set_transitive _ _ _ C A).
       assert (E := B X Y).
       assert (F := B X Z).
       assert (G := bop_lift_congruence _ _ refS symS tranS bS bCong _ _ _ _ E F).
       apply uop_minset_congruence_weak in G.        
       assert (H := set_transitive _ _ _ D G).
       exact H.
Qed.



Lemma abs_lemma_left (idem : bop_idempotent S rS bS)
                (LI : os_left_increasing lteS bS)
                (X Y : finite_set S) :
  (((X [^] (X [U] Y))) [=S] (X [U] (([rej] X) [U] (X [^] Y))) * (X [<=] (([rej] X) [U] (X [^] Y)))). 
Proof. split. 
       + assert (A := lift_union_left_distributive X X Y).
         assert (B := reject_lemma idem LI X).
         assert (C := bop_union_congruence _ _ refS symS tranS _ _ _ _ B (set_reflexive (X [^] Y))).
         assert (D := set_transitive _ _ _ A C). 
         assert (E := bop_union_associative _ _ refS symS tranS X ([rej] X) (X [^] Y)).
         assert (F := set_transitive _ _ _ D E).
         exact F. 
       + apply set_lte_lemma2; auto. 
         ++ exact (reject_lemma_2 idem LI X). 
         ++ exact (discard_lemma_left idem LI X Y). 
Qed.

Lemma abs_lemma_right (idem : bop_idempotent S rS bS)
                (LI : os_left_increasing lteS bS) 
                (X Y : finite_set S) :
  (((X [^] (Y [U] X))) [=S] (X [U] (([rej] X) [U] (X [^] Y))) * (X [<=] (([rej] X) [U] (X [^] Y)))).
Proof. split. 
       + destruct (abs_lemma_left idem LI X Y) as [A K]. 
         assert (B := bop_union_commutative _ _ refS symS tranS).
         assert (C := B Y X).
         assert (D := bop_lift_congruence _ _ refS symS tranS bS bCong _ _ _ _ (set_reflexive X) C).
         assert (E := set_transitive _ _ _ D A). 
         exact E.
       + apply set_lte_lemma2; auto. 
         ++ apply reject_lemma_2; auto. 
         ++ apply discard_lemma_left; auto. 
Qed.

Lemma minset_lift_union_left_left_absorption_weak
      (anti : brel_antisymmetric S rS lteS)      
      (idem : bop_idempotent S rS bS)
      (LI : os_left_increasing lteS bS)
      (X Y : finite_set S) :
      ([ms] X) [=S] ([ms] (X [^] (X [U] Y))). 
Proof. destruct (abs_lemma_left idem LI X Y) as [A B].
       assert (C := second_fundamental_minset_theorem anti _ _ B). 
       assert (D := uop_minset_congruence_weak _ _ A). 
       assert (E := set_transitive _ _ _ D C). 
       apply set_symmetric.
       exact E. 
Qed.

Lemma minset_lift_union_left_right_absorption_weak
      (anti : brel_antisymmetric S rS lteS)      
      (idem : bop_idempotent S rS bS)
      (LI : os_left_increasing lteS bS)
      (X Y : finite_set S) :
      ([ms] X) [=S] ([ms] (X [^] (Y [U] X))). 
Proof. destruct (abs_lemma_right idem LI X Y) as [A B].
       assert (C := second_fundamental_minset_theorem anti _ _ B). 
       assert (D := uop_minset_congruence_weak _ _ A). 
       assert (E := set_transitive _ _ _ D C). 
       apply set_symmetric.
       exact E. 
Qed.


(* BEWARE of badly named lift_union_left_distributive *) 
Lemma bops_lift_union_left_distributive : 
  A_bs_left_distributive (brel_set rS)
                         (bop_lift rS bS)
                         (bop_union rS). 
Proof. intros X Y Z. 
       apply brel_set_intro_prop; auto.
       split; intros a H.
          apply in_set_bop_union_elim in H.
          destruct H as [H | H].
          + admit. (* need idempotence *) 
          + admit. (* need (X U Y) [^] (Z [^] W) = (X [^] Z) U (X [^] W) U (Y [^] Z) U (X [^] W) *) 
Admitted. 


Lemma bops_lift_union_right_distributive : 
  A_bs_right_distributive (brel_set rS)
                         (bop_lift rS bS)
                         (bop_union rS). 
Proof. 
Admitted.

Lemma minset_lift_union_left_distributive
      (anti : brel_antisymmetric S rS lteS)      
      (idem : bop_idempotent S rS bS)
      (LM : os_left_monotone lteS bS) 
      (RM : os_right_monotone lteS bS) 
      (LI : os_left_increasing lteS bS)
      (RI : os_right_increasing lteS bS): 
  A_bs_left_distributive (brel_minset rS lteS)
                         (bop_minset_lift S rS lteS bS)
                         (bop_minset_union rS lteS). 
Proof. apply bop_reduce_left_distributive. 
       - exact set_reflexive.
       - exact set_symmetric.
       - exact set_transitive.
       - apply bop_lift_congruence; auto.
       - apply bop_union_congruence; auto.
       - exact uop_minset_congruence_weak. 
       - exact minset_idempotent.
       - apply lift_left_minset_invariant; auto. 
       - apply lift_right_minset_invariant; auto.         
       - apply minset_union_left_uop_invariant; auto. 
       - apply minset_union_right_uop_invariant; auto. 
       - exact bops_lift_union_left_distributive. 
Qed.


Lemma minset_lift_union_right_distributive
      (anti : brel_antisymmetric S rS lteS)      
      (idem : bop_idempotent S rS bS)
      (LM : os_left_monotone lteS bS) 
      (RM : os_right_monotone lteS bS) 
      (LI : os_left_increasing lteS bS)
      (RI : os_right_increasing lteS bS): 
  A_bs_right_distributive (brel_minset rS lteS)
                         (bop_minset_lift S rS lteS bS)
                         (bop_minset_union rS lteS). 
Proof. apply bop_reduce_right_distributive. 
       - exact set_reflexive.
       - exact set_symmetric.
       - exact set_transitive.
       - apply bop_lift_congruence; auto.
       - apply bop_union_congruence; auto.
       - exact uop_minset_congruence_weak. 
       - exact minset_idempotent.
       - apply lift_left_minset_invariant; auto. 
       - apply lift_right_minset_invariant; auto.         
       - apply minset_union_left_uop_invariant; auto. 
       - apply minset_union_right_uop_invariant; auto. 
       - exact bops_lift_union_right_distributive. 
Qed
.
(*
Lemma minset_lift_union_left_distributive
      (anti : brel_antisymmetric S rS lteS)      
      (idem : bop_idempotent S rS bS)
      (LM : os_left_monotone lteS bS) 
      (RM : os_right_monotone lteS bS) 
      (LI : os_left_increasing lteS bS)
      (RI : os_right_increasing lteS bS): 
  bop_left_distributive (finite_set S)
                         (brel_minset rS lteS)
                         (bop_minset_lift S rS lteS bS)
                         (bop_minset_union rS lteS). 
Proof. intros X Y Z.
       apply set_equal_implies_minset_equal.
       unfold bop_minset_union.
       unfold bop_minset_lift. 
       (*
          ([ms] (([ms] X) 
                 [U] ([ms] ([ms] (  ([ms] Y) [^] ([ms] Z)  )
                           )
                     )
                )
          )
         [=S] 
         ([ms] (
                 ([ms] ([ms] (   ([ms] X) [U] ([ms] Y)   )
                       )
                 )
                 [^] 
                 ([ms] ([ms] (  ([ms] X) [U] ([ms] Z)  ))
                 )
              )
         )

        *)
       assert (A := minset_lift_union_left_distributive_weak anti idem LI RI X Y Z).
       assert (B : ([ms] (([ms] X) [U] ([ms] ([ms] (([ms] Y) [^] ([ms] Z))))))
                     [=S]
                     ([ms] (X [U] (Y [^] Z)))).
       (*
        minset_union_uop_invariant_weak
        : ∀ X Y : finite_set S, ([ms] (([ms] X) [U] ([ms] Y))) [=S] ([ms] (X [U] Y))

       minset_lift_uop_invariant_weak
       : ∀ X Y : finite_set S, ([ms] (([ms] X) [^] ([ms] Y))) [=S] ([ms] (X [^] Y))
        *)
           assert (C := minset_lift_uop_invariant LM RM (inl anti) Y Z).
           assert (D := uop_minset_idempotent (([ms] Y) [^] ([ms] Z))). 
           assert (E := set_transitive _ _ _ D C).
           assert (F := bop_union_congruence _ _ refS symS tranS _ _ _ _ (set_reflexive ([ms] X)) E).
           assert (G := uop_minset_congruence_weak _ _ F).
           assert (H := minset_union_uop_invariant_weak X ((Y [^] Z))). 
           assert (I := set_transitive _ _ _ G H). 
           exact I. 
       assert (C : ([ms] ((X [U] Y) [^] (X [U] Z)))
                     [=S]
                     ([ms] (([ms] ([ms] (([ms] X) [U] ([ms] Y))))
                              [^]
                           ([ms] ([ms] (([ms] X) [U] ([ms] Z))))))).
          assert (D := minset_lift_uop_invariant_weak LM RM (inl anti) (X [U] Y) (X [U] Z)).
          apply set_symmetric in D. 
          assert (E := minset_union_uop_invariant_weak X Y). 
          assert (F := minset_union_uop_invariant_weak X Z). 
          assert (G := uop_minset_idempotent (([ms] X) [U] ([ms] Y))). 
          assert (I := set_transitive _ _ _ G E).
          assert (J := uop_minset_idempotent (([ms] X) [U] ([ms] Z))). 
          assert (K := set_transitive _ _ _ J F).
          assert (L := bop_lift_congruence _ _ refS symS tranS bS bCong _ _ _ _ I K).
          assert (M := uop_minset_congruence_weak _ _ L).
          apply set_symmetric in M.
          assert (N := set_transitive _ _ _ D M). 
          exact N.           
       assert (D := set_transitive _ _ _ B A).
       assert (E := set_transitive _ _ _ D C).
       exact E. 
Qed. 


Lemma minset_lift_union_right_distributive
  (anti : brel_antisymmetric S rS lteS)      
  (idem : bop_idempotent S rS bS)
  (LM : os_left_monotone lteS bS) 
  (RM : os_right_monotone lteS bS)       
  (LI : os_left_increasing lteS bS)
  (RI : os_right_increasing lteS bS) :
  bop_right_distributive (finite_set S)
                          (brel_minset rS lteS)
                          (bop_minset_lift S rS lteS bS)
                          (bop_minset_union S rS lteS). 
Proof. intros X Y Z.
       assert (A := minset_lift_union_left_distributive anti idem LM RM LI RI X Y Z).
       assert (B := bop_minset_union_commutative _ _ refS symS tranS lteS lteCong lteRefl lteTrans).
       assert (C := B (Y <^> Z) X).
       assert (D := minset_transitive _ _ _ C A). 
       assert (E := B X Y).
       assert (F := B X Z).
       assert (G := bop_minset_lift_congruence _ _ refS symS tranS lteS lteCong lteRefl lteTrans bS bCong).
       assert (H := G _ _ _ _ E F).
       assert (I := minset_transitive _ _ _ D H).
       exact I. 
Qed. 

*) 

Lemma left_left_abs_rhs
      (anti : brel_antisymmetric S rS lteS)      
      (LM : os_left_monotone lteS bS) 
      (RM : os_right_monotone lteS bS)
      (X Y Z : finite_set S) : 
  ([ms] (X <^> (Y <U> Z))) [=S] ([ms] (X [^] (Y [U] Z))).
Admitted.
(*
Proof. unfold bop_minset_union.
       unfold bop_minset_lift.
       assert (A := uop_minset_idempotent (([ms] X)
                                                [^]
                                                ([ms] ([ms] (([ms] Y) [U] ([ms] Z)))))).
       assert (B := minset_lift_uop_invariant LM RM (inl anti) X ([ms] (([ms] Y) [U] ([ms] Z)))). 
       assert (C := set_transitive _ _ _ A B). 
       assert (D := minset_union_uop_invariant_weak Y Z).
       assert (E := bop_lift_congruence _ _ refS symS tranS bS bCong).       
       assert (F := E _ _ _ _ (set_reflexive X) D).
       apply uop_minset_congruence_weak in F. 
       assert (G := set_transitive _ _ _ C F).
       assert (H := minset_lift_right_invariant_v0 _ _ refS symS tranS lteS lteCong lteRefl lteTrans bS bCong LM RM (inl anti)).
       assert (I := H X (Y [U] Z)).
       assert (J := set_transitive _ _ _ G I).       
       exact J. 
Qed. 
*)       
Lemma minset_lift_union_left_absorptive
      (anti : brel_antisymmetric S rS lteS)      
      (LM : os_left_monotone lteS bS) 
      (RM : os_right_monotone lteS bS)      
      (idem : bop_idempotent S rS bS)
      (LI : os_left_increasing lteS bS) : 
  A_bs_left_absorptive (brel_minset rS lteS)
                       (bop_minset_lift S rS lteS bS)
                       (bop_minset_union rS lteS). 
Proof. intros X Y.
       assert (A := minset_lift_union_left_left_absorption_weak anti idem LI X Y).
       unfold brel_minset.
       assert (B := left_left_abs_rhs anti LM RM X X Y). apply set_symmetric in B. 
       exact (set_transitive _ _ _ A B).
Qed. 

  
Lemma minset_lift_union_right_absorptive
      (anti : brel_antisymmetric S rS lteS)      
      (idem : bop_idempotent S rS bS)
      (LM : os_left_monotone lteS bS) 
      (RM : os_right_monotone lteS bS)
      (DDD : (brel_antisymmetric S rS lteS) +
               ((os_left_strictly_monotone lteS bS)
                *
               (os_right_strictly_monotone lteS bS)))
      (LI : os_left_increasing lteS bS) :                                            
  A_bs_right_absorptive (brel_minset rS lteS)
                        (bop_minset_lift S rS lteS bS)
                        (bop_minset_union rS lteS). 
Proof. intros X Y.
       assert (A := minset_lift_union_left_absorptive anti LM RM idem LI X Y).
       assert (B := bop_minset_union_commutative _ _ refS symS tranS lteS lteCong lteRefl lteTrans).       
       assert (C := bop_minset_lift_congruence _ _ refS symS tranS lteS lteCong lteRefl lteTrans bS bCong LM RM DDD).       
       assert (D := B X Y). 
       assert (E := C _ _ _ _ (minset_reflexive X) D). 
       assert (F := minset_transitive _ _ _ A E). 
       exact F. 
Qed. 


(* strict absorption 
Lemma minset_lift_union_bops_not_left_strictly_absorptive :
   bops_not_left_strictly_absorptive 
    (finite_set S)
    (brel_minset rS lteS)
    (bop_minset_lift S rS lteS bS)
    (bop_minset_union rS lteS). 
Proof.
   unfold bops_not_left_strictly_absorptive.
   exists (nil, nil); compute.
   right; reflexivity.
Qed.



Lemma minset_lift_union_bops_not_right_strictly_absorptive :
   bops_not_right_strictly_absorptive 
   (finite_set S)
   (brel_minset rS lteS)
   (bop_minset_lift S rS lteS bS)
   (bop_minset_union rS lteS). 
Proof.
   exists (nil, nil); compute.
   right; reflexivity.
Qed.
*)


(***************** ID, ANN ********************************) 

(* from minset_union_lift.v 

Lemma minset_union_lift_exists_id_ann_equal :
      bops_exists_id_ann_equal (finite_set S) (brel_minset rS lteS) (bop_minset_union S rS lteS) (bop_minset_lift S rS lteS bS).

Lemma minset_lift_union_exists_id_ann_equal_partial_order_version  
      (LM : os_left_monotone lteS bS) 
      (RM : os_right_monotone lteS bS) 
      (anti : brel_antisymmetric S rS lteS)
      (bot_id : A_os_exists_bottom_id_equal rS lteS bS) :
      bops_exists_id_ann_equal (finite_set S) (brel_minset rS lteS) (bop_minset_lift S rS lteS bS) (bop_minset_union S rS lteS).
*) 


    
End Lift_Union.   
End Theory. 



(**********************************************************************

Section ACAS.

Section Proofs.   
Variables (S : Type)
          (eq lte : brel S)
          (eqvP : eqv_proofs S eq)
          (times : binary_op S). 
  

Definition  minset_lift_union_bs_bounded_proofs_from_os_bounded_proofs
            (O : po_proofs S eq lte) 
            (times_cong : bop_congruence S eq times)
            (LM : os_left_monotone lte times)             
            (RM : os_right_monotone lte times) 
            (P : os_bounded_proofs S eq lte times)  :
                      dually_bounded_proofs (finite_set S)
                                      (brel_minset eq lte)
                                      (bop_minset_lift S eq lte times)
                                      (bop_minset_union S eq lte) := 
let ref := A_eqv_reflexive _ _ eqvP in   
let sym := A_eqv_symmetric _ _ eqvP in
let trn := A_eqv_transitive _ _ eqvP in
let lte_ref := A_po_reflexive _ _ _ O in 
let lte_trn := A_po_transitive _ _ _ O in
let lte_cong := A_po_congruence _ _ _ O in 
let anti := A_po_antisymmetric _ _ _ O in         
let bot_id_equal := A_bounded_bottom_id _ _ _ _ P in
{|
  A_bounded_plus_id_is_times_ann := minset_lift_union_exists_id_ann_equal_partial_order_version S eq ref sym trn lte lte_cong lte_ref lte_trn times times_cong LM RM anti bot_id_equal 
; A_bounded_times_id_is_plus_ann := minset_union_lift_exists_id_ann_equal S eq ref sym trn lte lte_cong lte_ref lte_trn times 
|}.


Definition  minset_lift_union_dioid_proofs_from_monotone_increasing_proofs 
            (times_cong : bop_congruence S eq times)
            (idem: bop_idempotent S eq times)             
            (P : po_proofs S eq lte)
            (LM : os_left_monotone lte times)
            (RM : os_right_monotone lte times)
            (LI : os_left_increasing lte times)
            (RI : os_right_increasing lte times) : 
                dioid_proofs (finite_set S)
                             (brel_minset eq lte)
                             (bop_minset_lift S eq lte times)                             
                             (bop_minset_union S eq lte)   := 
let lte_ref := A_po_reflexive _ _ _ P in 
let lte_trn := A_po_transitive _ _ _ P in
let lte_cong := A_po_congruence _ _ _ P in
let anti := A_po_antisymmetric _ _ _ P in

let ref := A_eqv_reflexive _ _ eqvP in
let sym := A_eqv_symmetric _ _ eqvP in
let trn := A_eqv_transitive _ _ eqvP in
{| 
  A_dioid_left_distributive     :=
    minset_lift_union_left_distributive S eq ref sym trn lte lte_cong lte_ref lte_trn times times_cong anti idem LM RM LI RI 
; A_dioid_right_distributive    :=
   minset_lift_union_right_distributive S eq ref sym trn lte lte_cong lte_ref lte_trn times times_cong anti idem LM RM LI RI 
; A_dioid_left_left_absorptive  :=
    minset_lift_union_left_left_absorptive S eq ref sym trn lte lte_cong lte_ref lte_trn times times_cong anti LM RM idem LI 
; A_dioid_left_right_absorptive :=
    minset_lift_union_left_right_absorptive S eq ref sym trn lte lte_cong lte_ref lte_trn times times_cong anti idem LM RM LI 
|}. 

End Proofs.   
  
Section Combinators.

Definition A_minset_lift_union_from_bounded_monotone_increasing_posg_GUARDED_CI_VERSION 
             (S : Type) 
             (P : A_bounded_monotone_increasing_posg S)
             (comm : bop_commutative S (A_eqv_eq _ (A_bmiposg_eqv _ P)) (A_bmiposg_times _ P)) 
             (idem : bop_idempotent S (A_eqv_eq _ (A_bmiposg_eqv _ P)) (A_bmiposg_times _ P)) 
             (nsel : bop_not_selective S (A_eqv_eq _ (A_bmiposg_eqv _ P)) (A_bmiposg_times _ P)) : A_dioid (finite_set S) := 
let eqv    := A_bmiposg_eqv _ P in
let eq     := A_eqv_eq _ eqv in
let wS     := A_eqv_witness _ eqv in
let f      := A_eqv_new _ eqv in
let nt     := A_eqv_not_trivial _ eqv in
let eqvP   := A_eqv_proofs _ eqv in   
let lte    := A_bmiposg_lte _ P in
let lteP   := A_bmiposg_lte_proofs _ P in
(* let anti   := A_po_antisymmetric _ _ _ lteP in   NB: unlikde minset_lift_union anti-symmetric is not needed! *) 
let times  := A_bmiposg_times _ P in
let timesP := A_bmiposg_times_proofs _ P in
let times_cong := A_sg_congruence _ _ _ timesP in 
let MOS    := A_bmiposg_proofs _ P in
let LM     := A_mono_inc_left_monotonic _ _ _ MOS in
let RM     := A_mono_inc_right_monotonic _ _ _ MOS in 
let LI     := A_mono_inc_left_increasing _ _ _ MOS in
let RI     := A_mono_inc_right_increasing _ _ _ MOS in
let PO     := A_po_from_bounded_monotone_increasing_posg _ P in
let Deqv   := A_eqv_minset_from_po_bounded _ PO in
{|
  A_dioid_eqv           := Deqv
; A_dioid_plus          := bop_minset_lift S eq lte times 
; A_dioid_times         := bop_minset_union S eq lte
; A_dioid_plus_proofs   := sg_CI_proofs_minset_lift_from_po S eq lte times eqvP lteP LM RM comm idem nsel timesP LI 
(* ouch.  loss of info. need A_commutative_dioid  ? *)                                                                    
; A_dioid_times_proofs  := A_sg_proofs_from_sg_CI_proofs _ _ _ 
                              (A_eqv_witness _ Deqv)
                              (A_eqv_new _ Deqv)
                              (A_eqv_not_trivial _ Deqv)
                              (A_eqv_proofs _ Deqv) 
                              (sg_CI_proofs_minset_union_from_po S eq lte wS f nt eqvP lteP)
; A_dioid_id_ann_proofs := minset_lift_union_bs_bounded_proofs_from_os_bounded_proofs S eq lte eqvP times lteP times_cong LM RM (A_bmiposg_top_bottom _ P)
; A_dioid_proofs        := minset_lift_union_dioid_proofs_from_monotone_increasing_proofs S eq lte eqvP times times_cong idem lteP LM RM LI RI 
; A_dioid_ast           := Ast_minset_lift_union (A_bmiposg_ast _ P)
|}.
  

End Combinators. 
End ACAS.


Section AMCAS.

Local Open Scope string_scope.

Definition A_mcas_minset_lift_union (S : Type) (M : A_os_mcas S) : A_bs_mcas (finite_set S ) :=
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
      | inl _    => A_BS_Error _ ("mcas_minset_lift_union : (currently) multiplication cannot be selective" :: nil)
      | inr nsel => A_BS_dioid _ (A_minset_lift_union_from_bounded_monotone_increasing_posg_GUARDED_CI_VERSION  S A comm idem nsel) 
      end 
    | inr nidem => A_BS_Error _ ("mcas_minset_lift_union : (currently) multiplication must be idempotent" :: nil)
    end        
  | inr _    => A_BS_Error _ ("mcas_minset_lift_union : (currently) multiplication must be commutative" :: nil)
  end
| _ => A_BS_Error _ ("mcas_minset_lift_union : (currently) can only be applied to a bounded, monotone, and increasing order-semigroup" :: nil)
end. 

End AMCAS.   


Section CAS.

Section Proofs.

Definition  minset_lift_union_dioid_certs_from_monotone_increasing_certs {S : Type}
            (P : @po_certificates S)
            (M : @os_monotone_increasing_certificates S) :
                 @dioid_certificates (finite_set S) := 
{| 
  dioid_left_distributive     := Assert_Left_Distributive
; dioid_right_distributive    := Assert_Right_Distributive
; dioid_left_left_absorptive  := Assert_Left_Left_Absorptive
; dioid_left_right_absorptive := Assert_Left_Right_Absorptive
|}. 


Definition  minset_lift_union_bs_bounded_certs_from_os_bounded_certs {S : Type}
            (O :  @po_certificates S) 
            (LM : @assert_left_monotone S)             
            (RM : @assert_right_monotone S) 
            (P :  @os_bounded_certs S)  : @dually_bounded_certificates (finite_set S) :=
match bounded_bottom_id P with
| Assert_Os_Exists_Bottom_Id_Equal bot_id => 
{|
  bounded_plus_id_is_times_ann := Assert_Exists_Id_Ann_Equal (bot_id :: nil) 
; bounded_times_id_is_plus_ann := Assert_Exists_Id_Ann_Equal nil 
|}
end.   
  
End Proofs.

Section Combinators.


Definition minset_lift_union_from_bounded_monotone_increasing_posg_GUARDED_CI_VERSION
             {S : Type} 
             (P : @bounded_monotone_increasing_posg S)
             (bComm  : @assert_commutative S) 
             (bIdem  : @assert_idempotent S) 
             (NotSel : @assert_not_selective S) : @dioid (finite_set S) := 
let eqv    := bmiposg_eqv P in
let eq     := eqv_eq eqv in
let wS     := eqv_witness eqv in
let f      := eqv_new eqv in
let lte    := bmiposg_lte P in
let lteP   := bmiposg_lte_certs P in
let times  := bmiposg_times P in
let timesP := bmiposg_times_certs P in
let MOS    := bmiposg_certs P in
let LM     := mono_inc_left_monotonic MOS in
let RM     := mono_inc_right_monotonic MOS in
let LI     := mono_inc_left_increasing MOS in
let PO     := po_from_bounded_monotone_increasing_posg P in
let Deqv   := eqv_minset_from_po_bounded PO in 
{|
  dioid_eqv           := Deqv 
; dioid_plus          := bop_minset_lift S eq lte times 
; dioid_times         := bop_minset_union S eq lte
; dioid_plus_certs    := sg_CI_certs_minset_lift_from_po S bComm bIdem NotSel
; dioid_times_certs   := sg_certs_from_sg_CI_certs _ 
                              (brel_minset eq lte)
                              (bop_minset_union S eq lte)                     
                              (eqv_witness Deqv)
                              (eqv_new Deqv)
                              (sg_CI_certs_minset_union_from_po lteP)
; dioid_id_ann_certs  := minset_lift_union_bs_bounded_certs_from_os_bounded_certs lteP LM RM (bmiposg_top_bottom P)
; dioid_certs         := minset_lift_union_dioid_certs_from_monotone_increasing_certs lteP MOS
; dioid_ast           := Ast_minset_lift_union (bmiposg_ast P)
|}
. 
End Combinators. 
End CAS. 

Section MCAS.

Local Open Scope string_scope.

Definition mcas_minset_lift_union {S : Type} (M : @os_mcas S) : @bs_mcas (finite_set S ) :=
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
      | Certify_Not_Selective p
                 => BS_dioid (minset_lift_union_from_bounded_monotone_increasing_posg_GUARDED_CI_VERSION  A
                       Assert_Commutative Assert_Idempotent (Assert_Not_Selective p))         
      | _        => BS_Error ("mcas_minset_lift_union : (currently) multiplication cannot be selective" :: nil)
      end 
    | _          => BS_Error ("mcas_minset_lift_union : (currently) multiplication must be idempotent" :: nil)
    end        
  | _            => BS_Error ("mcas_minset_lift_union : (currently) multiplication must be commutative" :: nil)
  end
| _              => BS_Error ("mcas_minset_lift_union : (currently) can only be applied to a bounded, monotone, and increasing order-semigroup" :: nil)
end. 

End MCAS.   

Section Verify.

Section Proofs.

Variables (S : Type)
          (eq lte : brel S)
          (eqvP : eqv_proofs S eq)
          (times : binary_op S). 

Lemma correct_minset_lift_union_bs_bounded_certs_from_os_bounded_certs 
            (O : po_proofs S eq lte) 
            (times_cong : bop_congruence S eq times)
            (LM : os_left_monotone lte times)             
            (RM : os_right_monotone lte times) 
            (P : os_bounded_proofs S eq lte times) : 
     P2C_dually_bounded
        (finite_set S)
        (brel_minset eq lte)
        (bop_minset_lift S eq lte times)         
        (bop_minset_union S eq lte)
        (minset_lift_union_bs_bounded_proofs_from_os_bounded_proofs S
           eq lte eqvP times O times_cong LM RM P)              
      =
      minset_lift_union_bs_bounded_certs_from_os_bounded_certs
        (P2C_po eq lte O) Assert_Left_Monotone Assert_Right_Monotone
        (P2C_os_bounded_proofs S eq lte times P). 
Proof. unfold minset_lift_union_bs_bounded_certs_from_os_bounded_certs,
       minset_lift_union_bs_bounded_proofs_from_os_bounded_proofs, P2C_dually_bounded; simpl.
       unfold p2c_exists_id_ann_equal.
       destruct A_bounded_bottom_id as [id [A B]]; simpl.
       reflexivity.
Qed.        

Lemma correct_minset_lift_union_dioid_certs_from_monotone_increasing_certs
      (*   (anti : brel_antisymmetric S eq lte) NOT NEEDED *)
            (idem: bop_idempotent S eq times)                   
            (times_cong : bop_congruence S eq times) 
            (P  : po_proofs S eq lte)
            (Q : os_monotone_increasing_proofs S lte times) 
            (LM : os_left_monotone lte times)
            (RM : os_right_monotone lte times)
            (LI : os_left_increasing lte times)
            (RI : os_right_increasing lte times) : 
    P2C_dioid (finite_set S) 
        (brel_minset eq lte)
        (bop_minset_lift S eq lte times)               
        (bop_minset_union S eq lte)
        (minset_lift_union_dioid_proofs_from_monotone_increasing_proofs S
          eq lte eqvP times times_cong idem P
          (A_mono_inc_left_monotonic _ _ _ Q)
          (A_mono_inc_right_monotonic _ _ _ Q)          
          (A_mono_inc_left_increasing _ _ _ Q)
          (A_mono_inc_right_increasing _ _ _ Q))
    =         
    minset_lift_union_dioid_certs_from_monotone_increasing_certs 
        (P2C_po eq lte P) 
        (P2C_os_monotone_increasing_proofs S lte times Q). 
Proof. unfold minset_lift_union_dioid_certs_from_monotone_increasing_certs,
       minset_lift_union_dioid_proofs_from_monotone_increasing_proofs, 
       P2C_dioid; simpl.
       reflexivity. 
Qed.

End Proofs.     

Section Combinators.

Theorem correct_minset_lift_union_from_bounded_monotone_increasing_posg_GUARDED_CI_VERSION (S : Type)
             (P : A_bounded_monotone_increasing_posg S)
             (comm : bop_commutative S (A_eqv_eq _ (A_bmiposg_eqv _ P)) (A_bmiposg_times _ P)) 
             (idem : bop_idempotent S (A_eqv_eq _ (A_bmiposg_eqv _ P)) (A_bmiposg_times _ P)) 
             (nsel : bop_not_selective S (A_eqv_eq _ (A_bmiposg_eqv _ P)) (A_bmiposg_times _ P)) :          
  A2C_dioid (finite_set S)
            (A_minset_lift_union_from_bounded_monotone_increasing_posg_GUARDED_CI_VERSION S P comm idem nsel)
  = 
  minset_lift_union_from_bounded_monotone_increasing_posg_GUARDED_CI_VERSION
    (A2C_bounded_monotone_increasing_posg P)
    Assert_Commutative Assert_Idempotent
    (Assert_Not_Selective (projT1 nsel)).
Proof. unfold A_minset_lift_union_from_bounded_monotone_increasing_posg_GUARDED_CI_VERSION,
       minset_lift_union_from_bounded_monotone_increasing_posg_GUARDED_CI_VERSION, A2C_dioid; simpl.
       unfold po_from_bounded_monotone_increasing_posg, A_po_from_bounded_monotone_increasing_posg.
       rewrite <- correct_eqv_minset_from_po_bounded.       
       rewrite correct_sg_CI_certs_minset_lift_from_po.       
       destruct nsel as [[s1 s2] [A B]]; simpl.
       (* need a lemma correct_sg_certs_from_sg_CI_certs *) 
       unfold sg_certs_from_sg_CI_certs, A_sg_proofs_from_sg_CI_proofs.
       rewrite <- correct_sg_certs_from_sg_C_certs.
       rewrite <- correct_sg_C_certs_from_sg_CI_certs.
       rewrite <- bop_minset_union_from_po_certs_correct.
       rewrite correct_minset_lift_union_bs_bounded_certs_from_os_bounded_certs.
       rewrite correct_minset_lift_union_dioid_certs_from_monotone_increasing_certs.
       reflexivity.
       destruct P; destruct A_bmiposg_proofs; auto. 
       destruct P; destruct A_bmiposg_proofs; auto.
       destruct P; destruct A_bmiposg_proofs; auto.
       destruct P; destruct A_bmiposg_proofs; auto.        
Qed. 

Theorem correct_mcas_minset_lift_union (S : Type) (M : A_os_mcas S) :
  mcas_minset_lift_union (A2C_mcas_os M) 
  = 
  A2C_mcas_bs _ (A_mcas_minset_lift_union S M).
Proof. unfold mcas_minset_lift_union, A_mcas_minset_lift_union.
       destruct M; simpl; try reflexivity. 
       destruct a; simpl. destruct A_bmiposg_times_proofs; simpl.
       destruct A_sg_commutative_d as [comm | ncomm]; simpl.
       + destruct A_sg_idempotent_d as [idem | [i nidem]]; simpl.
         ++ destruct A_sg_selective_d as [sel | nsel]; simpl. 
            +++ reflexivity. 
            +++ rewrite correct_minset_lift_union_from_bounded_monotone_increasing_posg_GUARDED_CI_VERSION.
                reflexivity. 
         ++ reflexivity. 
       + reflexivity. 
Qed. 
  
End Combinators.   

End Verify.   

(* create a dioid from a A_bounded_join_semilattice : 

Record A_bounded_join_semilattice {S : Type} := {
  A_bjsl_eqv           : A_eqv S 
; A_bjsl_lte           : brel S 
; A_bjsl_join          : binary_op S 
; A_bjsl_lte_proofs    : po_proofs S (A_eqv_eq _ A_bjsl_eqv) A_bjsl_lte 
; A_bjsl_join_proofs   : sg_CI_proofs S (A_eqv_eq _ A_bjsl_eqv) A_bjsl_join
; A_bjsl_top_bottom    : os_bounded_proofs S (A_eqv_eq S A_bjsl_eqv) A_bjsl_lte A_bjsl_join
; A_bjsl_proofs        : bop_is_lub A_bjsl_lte A_bjsl_join
; A_bjsl_ast           : cas_ast
}.

Definition A_minset_lift_union_from_bounded_join_semilattice
             (S : Type) 
             (P : A_bounded_join_semilattice S) : A_dioid (finite_set S) := 
let eqv    := A_bjsl_eqv _ P in
let eq     := A_eqv_eq _ eqv in
let s      := A_eqv_witness _ eqv in
let f      := A_eqv_new _ eqv in
let nt     := A_eqv_not_trivial _ eqv in
let eqvP   := A_eqv_proofs _ eqv in   
let ref := A_eqv_reflexive _ _ eqvP in
let sym := A_eqv_symmetric _ _ eqvP in
let trn := A_eqv_transitive _ _ eqvP in

let lte    := A_bjsl_lte _ P in
let lteP   := A_bjsl_lte_proofs _ P in
let lte_ref := A_po_reflexive _ _ _ lteP in 
let lte_trn := A_po_transitive _ _ _ lteP in
let lte_cong := A_po_congruence _ _ _ lteP in
let anti := A_po_antisymmetric _ _ _ lteP in

let times  := A_bjsl_join _ P in
let timesP := A_bjsl_join_proofs _ P in
let times_cong := A_sg_CI_congruence _ _ _ timesP in 
let idem   := A_sg_CI_idempotent _ _ _ timesP in
let comm   := A_sg_CI_commutative _ _ _ timesP in
let assoc  := A_sg_CI_associative _ _ _ timesP in                                  

let LUB    := A_bjsl_proofs _ P in
let LM     := lub_is_left_monotone _ _ _ ref sym trn lte_cong lte_ref anti times times_cong assoc idem comm LUB in 
let RM     := lub_is_right_monotone _ _ _ ref sym trn lte_cong lte_ref anti times times_cong assoc idem comm LUB in 
let LI     := lub_is_left_increasing _ _ _ ref sym trn lte_cong lte_ref anti times times_cong assoc idem comm LUB in
let RI     := lub_is_right_increasing _ _ _ ref sym trn lte_cong lte_ref anti times times_cong assoc idem comm LUB in 

let PO     := A_po_from_bounded_join_semilattice  _ P in
let Meqv   := A_eqv_minset_from_po _ PO  in 
{|
  A_dioid_eqv           := Meqv 
; A_dioid_plus          := bop_minset_lift S eq lte times 
; A_dioid_times         := bop_minset_union S eq lte
; A_dioid_plus_proofs   := sg_CI_proofs_minset_lift_from_po S eq lte s f times nt eqvP lteP timesP LM RM LI
(* Hmmm, note the loss of information here with this cast-up ... 
   Should define a A_commutative_idempotent_dioid .... 
*)                                                     
; A_dioid_times_proofs  := A_sg_proofs_from_sg_CI_proofs
                             (finite_set S)
                             (brel_minset eq lte)
                             (bop_minset_union S eq lte)
                             (A_eqv_witness _ Meqv)
                             (A_eqv_new _ Meqv)
                             (A_eqv_not_trivial _ Meqv)
                             (A_eqv_proofs _ Meqv)
                             (sg_CI_proofs_minset_union_from_po S eq lte s f nt eqvP lteP)
; A_dioid_id_ann_proofs := minset_lift_union_bs_bounded_proofs_from_os_bounded_proofs S eq lte eqvP times lteP times_cong LM RM (A_bjsl_top_bottom _ P)
; A_dioid_proofs        := minset_lift_union_dioid_proofs_from_monotone_increasing_proofs S eq lte eqvP times times_cong idem lteP LM RM LI RI 
; A_dioid_ast           := Ast_minset_lift_union (A_bjsl_ast _ P)
|}.

End Combinators. 
End ACAS.   
*) 
**********************************************************************)
