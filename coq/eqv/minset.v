Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.
Require Import CAS.coq.common.data.

Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.eqv.theory.
Require Import CAS.coq.eqv.set.
Require Import CAS.coq.eqv.list.
Require Import CAS.coq.eqv.reduce. 

Require Import CAS.coq.or.properties.
Require Import CAS.coq.or.structures.
Require Import CAS.coq.or.theory.
Require Import CAS.coq.or.cast_up. 

Require Import CAS.coq.sg.union.

Require Import CAS.coq.uop.properties.



Section Computation. 

(*  
   The standard way of defining minsets is as follows. 
   Given an order, (S, <=), define and a subset X of S, 
   define (the antichain) 

   min(<=, X) := {x in X | for all y in X, not (y < x)}. 

   Now, the set of minimal sets over S is defined as 

   MIN(<=, S) := {X subset S | X is finite and min(<=, X) = X}, 
   and we can define an equivalence relation 
   (MIN(<=, S), =') 
   where equality =' is just equality over sets restricted to MIN(<=, S). 

   Now, here is a problem.  We want MIN(<=, S) to be a type representable in OCaml. 
   So, instead of (MIN(<=, S), ='), we represent minsets as 

      (Finite_set S, ='') 

   where X ='' Y iff min(<=, X) =' min(<=, Y). 

   Note: This could be defined using the more abstract notion of a reduction.  
   This was attempted, but it turned out that proving things  
   so many layers of abstraction was pure torture, at least with the way reductions 
   are currently defined (see coq/theory/reductions). 

   Another note: antisymmetry will not be assumed for <=. This allows us to model 
   some exotic network routing constructions ... 
*)   

(* 

*)   
Fixpoint  iterate_minset {S : Type} (lte : brel S) (W Y X : finite_set S): (finite_set S) * (finite_set S) := 
      match X with
         | nil => (W, Y) 
         | a :: Z => match find (below lte a) Z with
                     | None   => match find (below lte a) Y with
                                 | None   => iterate_minset lte W (a :: Y) Z 
                                 | Some _ => iterate_minset lte (a :: W) Y Z 
                                 end 
                     | Some _ => iterate_minset lte (a :: W) Y Z 
                     end
      end.


Definition uop_minset {S : Type} (lte :brel S) (X : finite_set S) : (finite_set S) := 
    let (_, Y) := iterate_minset lte nil nil X in Y. 

(*Definition brel_minset {S : Type} (eq lte : brel S)  : brel (finite_set S)
  := λ X Y, brel_set eq (uop_minset lte X) (uop_minset lte Y).
 *)

Definition brel_minset {S : Type} (eq lte : brel S)  : brel (finite_set S)
  := brel_reduce (brel_set eq) (uop_minset lte). 

End Computation. 

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
(* NB: antisymmetry is not assumed! *) 
Variable lteRefl : brel_reflexive S lteS.
Variable lteTrans : brel_transitive S lteS. 

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

Notation "a [U] b"   := (bop_union rS a b)         (at level 15).

Notation "a [=S] b"   := (brel_set rS a b = true)         (at level 15).
Notation "a [<>S] b"  := (brel_set rS a b = false)        (at level 15).
Notation "a [=MS] b"  := (brel_minset rS lteS a b = true)        (at level 15).
Notation "a [<>MS] b" := (brel_minset rS lteS a b = false)       (at level 15).
Notation "[ms] x" := (uop_minset lteS x) (at level 15).

Definition set_congruence := brel_set_congruence S rS refS symS tranS.
Definition set_transitive := brel_set_transitive S rS refS symS tranS.
Definition set_symmetric := brel_set_symmetric S rS.
Definition set_reflexive := brel_set_reflexive S rS refS symS.

Definition equiv_reflexive := equiv_reflexive S lteS lteRefl.
Definition below_equiv_pseudo_congruence_v2 := below_equiv_pseudo_congruence_v2 S lteS lteRefl lteTrans.
Definition equiv_or_incomp_congruence :=  equiv_or_incomp_congruence S rS lteS lteCong. 
Definition below_congruence := below_congruence S rS lteS lteCong.
Definition below_transitive := below_transitive S lteS lteTrans.
Definition equiv_elim := equiv_elim S lteS. 

Definition is_antichain := is_antichain S rS lteS. 

Lemma find_brel_congruence (X: finite_set S) (r : brel S) :
    brel_congruence S rS r -> ∀ (s t : S), s [=] t -> find (r s) X = find (r t) X. 
Proof. induction X.
       intros A s t B. compute; auto.
       intros A s t B.
       unfold find; fold (find (r s)); fold (find (r t)).
       rewrite (A _ _ _ _ B (refS a)). 
       rewrite (IHX A s t B).
       reflexivity. 
Qed.

Definition brel_equiv_congruence  (r : brel S) := 
       ∀ s t u v : S, s [~] u  → t [~] v → r s t = r u v. 

Lemma find_equiv_congruence (X: finite_set S) (r : brel S) :
  brel_equiv_congruence r -> ∀ (s t : S), s [~] t -> find (r s) X = find (r t) X.
Proof. induction X.
       intros A s t B. compute; auto.
       intros A s t B.
       unfold find; fold (find (r s)); fold (find (r t)).
       rewrite (A _ _ _ _ B (equiv_reflexive a)).
       rewrite (IHX A s t B).
       reflexivity. 
Qed.


Lemma find_equiv_below_congruence (X: finite_set S):
 ∀ (s t : S), s [~] t -> find (below lteS s) X = find (below lteS t) X.
Proof. induction X.
       intros s t A. compute; auto.
       intros s t A.
       unfold find; fold (find (below lteS s)); fold (find (below lteS t)).
       rewrite (below_equiv_pseudo_congruence_v2 _ _ _  A). 
       rewrite (IHX s t A).
       reflexivity. 
Qed.


Lemma find_below_congruence (X: finite_set S) : 
  ∀ (s t : S), s [=] t -> find (below lteS s) X = find (below lteS t) X.
Proof. apply find_brel_congruence. apply below_congruence; auto. Qed.   


Lemma filter_brel_congruence (X: finite_set S) (r : brel S) :
    brel_congruence S rS r -> ∀ (s t : S), s [=] t -> filter (r s) X = filter (r t) X. 
Proof. induction X.
       intros A s t B. compute; auto.
       intros A s t B.
       unfold filter; fold (filter (r s)); fold (filter (r t)).
       rewrite (A _ _ _ _ B (refS a)). 
       rewrite (IHX A s t B).
       reflexivity. 
Qed.

Lemma filter_equiv_or_incomp_congruence (X: finite_set S) : 
  ∀ (s t : S), s [=] t -> filter (equiv_or_incomp lteS s) X = filter (equiv_or_incomp lteS t) X.
Proof. apply filter_brel_congruence. apply equiv_or_incomp_congruence; auto. Qed.   


Lemma find_below_none (X : finite_set S) : 
  ∀ (s : S), find (below lteS s) X = None -> ∀ (t : S), t [in] X ->  t !<< s. 
Proof. induction X.
       intros s A t B. compute in B. discriminate B. 
       intros s A t B. unfold find in A. fold (find (below lteS s)) in A.
       apply in_set_cons_elim in B; auto. destruct B as [B | B].
         compute. case_eq(lteS t s); intro C; case_eq(lteS s t); intro D; auto.
         rewrite (lteCong _ _ _ _ (refS s) (symS _ _ B)) in D.
         rewrite (lteCong _ _ _ _ (symS _ _ B) (refS s)) in C.         
         unfold below in A. rewrite D in A. rewrite C in A. simpl in A.
         discriminate A. 
         case_eq(below lteS s a); intro C; rewrite C in A. 
            discriminate A.
            apply IHX; auto. 
Qed.

Lemma find_below_some (X : finite_set S) :
      ∀ (s t : S), find (below lteS s) X = Some t -> t [in] X * (t << s).
Proof. induction X.
       intros s t A. compute in A. discriminate A.
       intros s t A. unfold find in A. fold (find (below lteS s)) in A.
       case_eq(below lteS s a); intro B; rewrite B in A. 
          assert (C : t = a ). inversion A. reflexivity. 
          rewrite C. split; auto. 
             apply in_set_cons_intro; auto. 
          destruct (IHX s t A) as [C D].
          split; auto.
          apply in_set_cons_intro; auto. 
Qed.

Lemma in_filter_brel_elim  (X : finite_set S) (r : brel S):
     brel_congruence S rS r -> 
     ∀ (s t : S), s [in] (filter (r t) X) -> (s [in] X) * (r t s = true).
Proof. induction X.
       intros C s t A. compute in A. discriminate A. 
       intros C s t A.
       unfold filter in A. fold (filter (r t)) in A. 
       case_eq (r t a); intro B.
          rewrite B in A. 
          apply in_set_cons_elim in A; auto. 
          destruct A as [A | A]. split. 
             apply in_set_cons_intro; auto.
             rewrite (C _ _ _ _ (refS t) A) in B; auto.
             destruct (IHX C s t A) as [D E].
             split; auto.
             apply in_set_cons_intro; auto.

          rewrite B in A.
          destruct (IHX C s t A) as [D E].             
             split; auto.
             apply in_set_cons_intro; auto.
Qed.              

Lemma in_filter_equiv_or_incomp_elim  (X : finite_set S) :
     ∀ (s t : S), s [in] (filter (equiv_or_incomp lteS t) X) -> (s [in] X) * (equiv_or_incomp lteS t s = true).
Proof. apply in_filter_brel_elim.  apply equiv_or_incomp_congruence; auto. Qed. 


(** *******************  uop_minset ********************* **)

(* note: definition of is_antichaing 
is more general than the standard defintion 
since antisymmetry is not assumed. 
It is defined in po/properties.v: 

Definition is_antichain (X : finite_set S) :=   ∀ (s : S), s [in] X  -> ∀ (t : S), t [in] X  -> (s [~|#] t).

*) 
Lemma minset_empty : [ms] nil = nil. 
Proof. compute; auto. Qed. 

Lemma minset_singleton : ∀ (s : S), [ms] (s :: nil) = s :: nil. 
Proof. intro s. compute; auto. Qed.

Lemma in_iterate_minset_implies_in_union (X : finite_set S) :
      ∀ (s : S) (W Y : finite_set S),  s [in] snd(iterate_minset lteS W Y X) -> (s [in] Y) + (s [in] X). 
Proof. induction X. 
       intros s W Y A. unfold iterate_minset in A; auto. 
       intros s W Y A. unfold iterate_minset in A. 
       case_eq(find (below lteS a) X).
          intros t B. rewrite B in A. 
          fold (iterate_minset lteS (a :: W) Y X) in A.
          destruct (IHX s (a :: W) Y A) as [C | C]; auto. 
             right. apply in_set_cons_intro; auto.           

          intros B. rewrite B in A.
          case_eq(find (below lteS a) Y).          
             intros t C. rewrite C in A. 
             fold (iterate_minset lteS (a :: W) Y X) in A.
             destruct (IHX s (a :: W) Y A) as [D | D]; auto. 
                right. apply in_set_cons_intro; auto.           
             intros C. rewrite C in A. 
             fold (iterate_minset lteS W (a ::Y) X) in A.
             destruct (IHX s W (a :: Y) A) as [D | D]; auto. 
                apply in_set_cons_elim in D; auto. 
                destruct D as [D | D]; auto. 
                   right. apply in_set_cons_intro; auto. 
                right. apply in_set_cons_intro; auto. 
Qed. 

Lemma in_minset_implies_in_set (X : finite_set S) :
      ∀ (s : S), s [in] ([ms] X) -> s [in] X. 
Proof. intros s A.
       unfold uop_minset in A.
       destruct (in_iterate_minset_implies_in_union _ _ _ _ A) as [B | B]; auto.
          compute in B. discriminate B.
Qed.           

Lemma empty_set_is_antichain : is_antichain nil.
Proof. intros s A t. compute in A. discriminate A. Qed. 

Lemma is_antichain_cons_intro (X : finite_set S) :
    is_antichain X -> ∀ (s : S), (∀ (t : S),  t [in] X -> s [~|#] t) -> is_antichain (s :: X). 
Proof. intros A s I t B u C.
       apply in_set_cons_elim in B; auto. apply in_set_cons_elim in C; auto. 
       destruct B as [B | B]; destruct C as [C | C].
          rewrite (equiv_or_incomp_congruence _ _ _ _ (symS _ _ C) (symS _ _ B)).
          apply equiv_or_incomp_reflexive; auto.                    

          assert (K := I _ C). 
          rewrite (equiv_or_incomp_congruence _ _ _ _ (refS u) (symS _ _ B)); auto. 

          assert (K := I _ B). 
          rewrite (equiv_or_incomp_congruence  _ _ _ _  (symS _ _ C) (refS t)); auto. 
          apply equiv_or_incomp_symmetric; auto. 
          
          exact (A t B u C).
Qed.


Lemma is_antichain_cons_elim (X : finite_set S) :
  ∀ (s : S), is_antichain (s :: X) -> 
            (is_antichain X)  * (∀ (t : S),  t [in] X -> s [~|#] t). 
Proof. unfold is_antichain. intros s A. split. 
          intros u B t C. apply A. 
             apply in_set_cons_intro; auto.
             apply in_set_cons_intro; auto.           
          intros t B. apply A. 
             apply in_set_cons_intro; auto.
             apply in_set_cons_intro; auto.          
Qed.


Lemma iterate_minset_is_antichain (X : finite_set S) :
  ∀ (W Y : finite_set S),
        is_antichain Y ->
        (∀ (s : S), s [in] X -> ∀ (t : S), t [in] Y → s !<< t) ->  
        is_antichain (snd (iterate_minset lteS W Y X)).
Proof. induction X.
       intros W Y A B. unfold iterate_minset. auto. 
       intros W Y A B. unfold iterate_minset.
       assert (B' : ∀ t : S, t [in] Y → a !<< t).
          intros t C.
          assert (D : a [in] (a :: X)). apply in_set_cons_intro; auto.
          exact (B a D t C). 
       case_eq(find (below lteS a) X). 
          intros u C. 
          fold (iterate_minset lteS (a :: W) Y X).
          assert (D : ∀ s : S, s [in] X → ∀ t : S, t [in] Y → s !<< t).
             intros s E t F. apply B; auto. apply in_set_cons_intro; auto. 
          apply IHX; auto. 
 
          intros C.
          case_eq(find (below lteS a) Y).
             intros u D. 
             fold (iterate_minset lteS (a :: W) Y X).
             assert (E : ∀ s : S, s [in] X → ∀ t : S, t [in] Y → s !<< t).
                intros s E t F. apply B; auto. apply in_set_cons_intro; auto.              
             apply IHX; auto.
             intros D. 
             fold (iterate_minset lteS W (a :: Y) X).
             assert (F := find_below_none Y a D).                   
             assert (F' := find_below_none X a C).             
             assert (G : ∀ s : S, s [in] X → ∀ t : S, t [in] (a :: Y) → s !<< t).
                intros s G t H.
                assert (I := F' s G).                 
                apply in_set_cons_elim in H; auto.
                destruct H as [H | H]; auto.
                   rewrite (below_congruence _ _ _ _ (symS _ _ H) (refS s) ); auto. 
                   apply B; auto. 
                   apply in_set_cons_intro; auto. 

                   
             assert (H : is_antichain (a :: Y)).
                unfold is_antichain. intros s H t I.
                apply in_set_cons_elim in H; auto. 
                apply in_set_cons_elim in I; auto.
                destruct H as [H | H]; destruct I as [I | I]. 
                   rewrite (equiv_or_incomp_congruence _ _ _ _ (symS _ _ I) (symS _ _ H)). 
                   apply equiv_or_incomp_reflexive; auto.

                   assert (J := F t I).
                   assert (K := B' t I). 
                   rewrite (equiv_or_incomp_congruence _ _ _ _ (refS t) (symS _ _ H)).
                   apply not_below_implies_equiv_or_incomp; auto. 
                   
                   rewrite (equiv_or_incomp_congruence _ _ _ _ (symS _ _ I) (refS s) ).
                   assert (J := B' s H).
                   apply equiv_or_incomp_intro.
                   compute. 
                   case_eq(lteS a s); intro K; case_eq(lteS s a); intro L; auto.  
                      compute in J. rewrite K in J. rewrite L in J. discriminate J. 
                      assert (M := F s H).
                      compute in M. rewrite L in M. rewrite K in M. discriminate M. 

                   exact (A _ H _ I). 
             exact (IHX W (a :: Y) H G).
Qed. 

             
Lemma uop_minset_is_antichain (X : finite_set S) : is_antichain ([ms] X). 
Proof. assert (A : ∀ (s  : S), s [in] X -> ∀ (t : S), t [in] nil → s !<< t).
          intros s B t C. compute in C. discriminate C. 
       exact (iterate_minset_is_antichain X nil nil empty_set_is_antichain A).
Qed.   


Lemma in_iterate_minset_elim (X : finite_set S) :
  ∀ (W Y : finite_set S), 
        is_antichain Y ->
        (∀ (s : S), s [in] X -> ∀ (t : S), t [in] Y → s !<< t) ->  
        ∀ (s : S), s [in] (snd (iterate_minset lteS W Y X)) -> (∀ (t : S), (t [in] Y) + (t [in] X) -> t !<< s).
Proof. induction X.
       intros W Y A B s C t [D | D].
          unfold is_antichain in A.
          unfold iterate_minset  in C.
          assert (E := A s C t D).
          apply equiv_or_incomp_elim in E.
          destruct E as [E | E]. 
             apply equiv_implies_not_below; auto. 
             apply incomp_implies_not_below; auto.              
          
          compute in D. discriminate D. 

       intros W Y A B s C.
       assert (B' : ∀ s : S, s [in] X → ∀ t : S, t [in] Y → s !<< t).
          intros u D t E.
          assert (F : u [in] (a :: X)). apply in_set_cons_intro; auto. 
          exact (B u F t E). 
       unfold iterate_minset in C.
       case_eq(find (below lteS a) X). 
          intros t D. rewrite D in C.
          fold (iterate_minset lteS (a :: W) Y X) in C. 
          destruct (find_below_some X a t D) as [E F].
          assert (H := IHX _ _ A B' s C). 
          intros u [I | I]. 
             exact (H u (inl I)).
             destruct (in_iterate_minset_implies_in_union _ _ _ _ C) as [J | J].
                exact(B _ I _ J).               
                apply in_set_cons_elim in I; auto. 
                destruct I as [I | I]. 
                   rewrite (below_congruence _ _ _ _ (refS s) (symS _ _ I)). 
                   case_eq(below lteS s a); intro K; auto.
                      assert (L := below_transitive _ _ _ F K). 
                      rewrite (H _ (inr E)) in L.  discriminate L. 
                   exact (H u (inr I)) . 
                
          intros D. rewrite D in C.
          assert (E := find_below_none _ _ D).                    
          case_eq(find (below lteS a) Y).
            intros t F. rewrite F in C.
            destruct (find_below_some _ _  _ F) as [G H]. 
            fold (iterate_minset lteS (a :: W) Y X) in C.
            assert (J := IHX _ _ A B' _ C). 
            intros u [K | K]. 
               exact (J u (inl K)). 
               apply in_set_cons_elim in K; auto.
               destruct K as [K | K]. 
                  rewrite (below_congruence _ _ _ _ (refS s) (symS _ _ K)).
                  case_eq(below lteS s a); intro L; auto. 
                     assert (M := below_transitive _ _ _ H L). 
                     rewrite (J t (inl G)) in M. discriminate M. 
                  exact (J u (inr K)). 
               
            intros F. rewrite F in C.
            fold (iterate_minset lteS (a :: Y) X) in C.                                             
            assert (G := find_below_none _ _ F).
            assert (G' : ∀ t : S, t [in] Y → a !<< t).
                intros t H. 
                assert (K : a [in] (a :: X)). apply in_set_cons_intro; auto. 
                exact (B a K t H).

            assert (A' : is_antichain (a :: Y)).
               intros u H v I.
               apply in_set_cons_elim in H; auto. apply in_set_cons_elim in I; auto. 
               destruct H as [H | H]; destruct I as [I | I].
                  rewrite (equiv_or_incomp_congruence _ _ _ _ (symS _ _ I) (symS _ _ H)).
                  apply equiv_or_incomp_reflexive; auto. 
                  
                  rewrite (equiv_or_incomp_congruence _ _ _ _ (refS v) (symS _ _ H)).                 
                  apply (not_below_implies_equiv_or_incomp).
                     exact (G' v I).
                     exact (G v I). 

                  rewrite (equiv_or_incomp_congruence _ _ _ _ (symS _ _ I) (refS u) ).
                  apply (not_below_implies_equiv_or_incomp).
                     exact (G u H).
                     exact (G' u H). 

                  apply (not_below_implies_equiv_or_incomp).
                  assert (J := A u H v I). 
                  apply equiv_or_incomp_implies_not_below in J. 
                  destruct J as [J _]; auto.                   
                  assert (J := A u H v I). 
                  apply equiv_or_incomp_implies_not_below in J. 
                  destruct J as [_ J]; auto.                   

            assert (B'' : ∀ s : S, s [in] X → ∀ t : S, t [in] (a :: Y) → s !<< t).
               intros u J v I.       
               apply in_set_cons_elim in I; auto.       
               destruct I as [I | I].
                  rewrite (below_congruence _ _ _ _ (symS _ _ I) (refS u)).
                  exact (E u J). 
                  exact (B' u J v I). 

           assert (I := IHX _ _ A' B'' _ C).             

           intros t [J | J].
               assert (K : t [in] (a :: Y)). apply in_set_cons_intro; auto. 
               exact (I t (inl K)). 

               apply in_set_cons_elim in J; auto. 
               destruct J as [J | J].
                  assert (K : a [in] (a :: Y)). apply in_set_cons_intro; auto.
                  rewrite (below_congruence _ _ _ _ (refS s) (symS _ _ J) ).
                  exact (I a (inl K)). 
               
                  exact (I t (inr J)).
Qed. 

          
Lemma in_minset_elim (X : finite_set S) :
  ∀ (s : S), s [in] ([ms] X) -> (s [in] X) * (∀ (t : S), t [in] X -> t !<< s).
Proof. intros s A. split. 
       exact (in_minset_implies_in_set X s A). 

       unfold uop_minset in A.
       assert (B : ∀ (s : S), s [in] X -> ∀ (t : S), t [in] nil → s !<< t).
          intros a D t E. compute in E. discriminate E. 
       assert (C := in_iterate_minset_elim X nil nil empty_set_is_antichain B s A).
       intros t D. exact (C t (inr D)). 
Qed.

Lemma in_iterate_minset_intro (X : finite_set S) :
  ∀ (W Y : finite_set S), 
        is_antichain Y ->
        (∀ (s : S), s [in] X -> ∀ (t : S), t [in] Y → s !<< t) ->  
        ∀ (s : S), (s [in] Y + s [in] X) * (∀ (t : S), (t [in] Y) + (t [in] X) -> t !<< s)
                   -> s [in] (snd (iterate_minset lteS W Y X)). 
Proof. induction X. 
       intros W Y A B s [[C | C] D].
          unfold iterate_minset; auto. 
          compute in C. discriminate C. 

       intros W Y A B s [[C | C] D].
          unfold iterate_minset. 
          case_eq(find (below lteS a) X).
             intros t E.
             fold (iterate_minset lteS (a :: W) Y X).
             assert (F : ∀ s : S, s [in] X → ∀ t : S, t [in] Y → s !<< t).
                intros u F v G.
                assert (H: u [in] (a :: X)). apply in_set_cons_intro; auto. 
                exact (B u H v G).
             assert (G : ∀ t : S, t [in] Y + t [in] X → t !<< s).
                intros u [G | G].    
                   assert (H := A s C u G).
                   apply equiv_or_incomp_implies_not_below in H. 
                   destruct H as [_ H]; auto. 
                   assert (H: u [in] (a :: X)). apply in_set_cons_intro; auto. 
                   exact (D u (inr H)). 
             exact (IHX _ _ A F s (inl C, G)).             
             
             intro E.
             case_eq(find (below lteS a) Y).
                intros t F. 
                fold (iterate_minset lteS (a :: W) Y X).
                   assert (G : ∀ s : S, s [in] X → ∀ t : S, t [in] Y → s !<< t).
                      intros u G v H. 
                      assert (I: u [in] (a :: X)). apply in_set_cons_intro; auto. 
                      exact (B u I v H). 
                   assert (H : ∀ t : S, t [in] Y + t [in] X → t !<< s). 
                      intros u [H | H].
                         exact (D u (inl H)). 
                         assert (I: u [in] (a :: X)). apply in_set_cons_intro; auto. 
                         exact (D u (inr I)).
                   exact (IHX _ _ A G s (inl C, H)).             

                intro F.
                fold (iterate_minset lteS (a :: Y) X).
                assert (G : s [in] (a :: Y)). apply in_set_cons_intro; auto. 
                assert (A' : is_antichain (a :: Y)). 
                   unfold is_antichain. 
                   intros t H u I. 
                   apply in_set_cons_elim in H; auto. apply in_set_cons_elim in I; auto.
                   destruct H as [H | H]; destruct I as [I | I].
                      rewrite (equiv_or_incomp_congruence _ _ _ _ (symS _ _ I) (symS _ _ H)). 
                      apply equiv_or_incomp_reflexive; auto. 
                      
                      rewrite (equiv_or_incomp_congruence _ _ _ _ (refS u) (symS _ _ H)). 
                      assert (J : a [in] (a :: X)). apply in_set_cons_intro; auto. 
                      assert (K := B a J u I). 
                      assert (L := find_below_none _ _ F u I). 
                      apply not_below_implies_equiv_or_incomp; auto. 
                      
                      rewrite (equiv_or_incomp_congruence _ _ _ _ (symS _ _ I) (refS t) ). 
                      assert (J : a [in] (a :: X)). apply in_set_cons_intro; auto. 
                      assert (K := B a J t H). 
                      assert (L := find_below_none _ _ F t H). 
                      apply not_below_implies_equiv_or_incomp; auto. 

                      exact (A t H u I). 
                assert (H : ∀ s : S, s [in] X → ∀ t : S, t [in] (a :: Y) → s !<< t). 
                    intros t H u I.
                    apply in_set_cons_elim in I; auto. destruct I as [I | I].
                       assert (J := find_below_none _ _ E t H). 
                       rewrite (below_congruence _ _ _ _ (symS _ _ I) (refS t) ); auto. 
                       assert (J : t [in] (a :: X)). apply in_set_cons_intro; auto. 
                       exact (B t J u I). 
                assert (J : ∀ t : S, t [in] (a :: Y) + t [in] X → t !<< s). 
                   intros t [I | I].
                      apply in_set_cons_elim in I; auto.  destruct I as [I | I].
                         rewrite (below_congruence _ _ _ _ (refS s) (symS _ _ I)).
                         assert (J : a [in] (a :: X)). apply in_set_cons_intro; auto. 
                         exact (B a J s C). 
                         assert (J := A s C t I). 
                         apply equiv_or_incomp_implies_not_below in J. 
                         destruct J as [_ J]; auto.
                         
                      assert (J : t [in] (a :: X)). apply in_set_cons_intro; auto. 
                      exact (B t J s C). 

                exact (IHX _ _ A' H s (inl G, J)).                  
                

          unfold iterate_minset. 
          case_eq(find (below lteS a) X).
             intros t E.
             fold (iterate_minset lteS (a :: W) Y X).
             assert (F : ∀ s : S, s [in] X → ∀ t : S, t [in] Y → s !<< t).
                intros u F v G. 
                assert (H: u [in] (a :: X)). apply in_set_cons_intro; auto. 
                exact (B u H v G).
             assert (G : ∀ t : S, t [in] Y + t [in] X → t !<< s).
                intros u [G | G].    
                   exact (D u (inl G)). 
                   assert (H: u [in] (a :: X)). apply in_set_cons_intro; auto. 
                   exact (D u (inr H)). 
             apply in_set_cons_elim in C; auto. destruct C as [C | C].
                destruct (find_below_some X a t E) as [H I].
                assert (J := G t (inr H)). 
                rewrite (below_congruence _ _ _ _ C (refS t)) in I. 
                rewrite I in J. discriminate J. 
                exact (IHX _ _ A F s (inr C, G)).             
             
             intro E.
             case_eq(find (below lteS a) Y).
                intros t F. 
                fold (iterate_minset lteS Y X).
                   assert (G : ∀ s : S, s [in] X → ∀ t : S, t [in] Y → s !<< t).
                      intros u G v H. 
                      assert (I: u [in] (a :: X)). apply in_set_cons_intro; auto. 
                      exact (B u I v H). 
                   assert (H : ∀ t : S, t [in] Y + t [in] X → t !<< s). 
                      intros u [H | H].
                         exact (D u (inl H)). 
                         assert (I: u [in] (a :: X)). apply in_set_cons_intro; auto. 
                         exact (D u (inr I)).

                   apply in_set_cons_elim in C; auto. destruct C as [C | C].
                      destruct (find_below_some Y a t F) as [I J].
                      assert (K := H t (inl I)). 
                      rewrite (below_congruence _ _ _ _ C (refS t)) in J. 
                      rewrite J in K. discriminate K. 
                      exact (IHX _ _ A G s (inr C, H)).             

                intro F.
                fold (iterate_minset lteS W (a :: Y) X).
                assert (A' : is_antichain (a :: Y)). 
                   unfold is_antichain. 
                   intros t H u I. 
                   apply in_set_cons_elim in H; auto. apply in_set_cons_elim in I; auto.
                   destruct H as [H | H]; destruct I as [I | I].
                      rewrite (equiv_or_incomp_congruence _ _ _ _ (symS _ _ I) (symS _ _ H)). 
                      apply equiv_or_incomp_reflexive; auto. 
                      
                      rewrite (equiv_or_incomp_congruence _ _ _ _ (refS u) (symS _ _ H)). 
                      assert (J : a [in] (a :: X)). apply in_set_cons_intro; auto. 
                      assert (K := B a J u I). 
                      assert (L := find_below_none _ _ F u I). 
                      apply not_below_implies_equiv_or_incomp; auto. 
                      
                      rewrite (equiv_or_incomp_congruence _ _ _ _ (symS _ _ I) (refS t) ). 
                      assert (J : a [in] (a :: X)). apply in_set_cons_intro; auto. 
                      assert (K := B a J t H). 
                      assert (L := find_below_none _ _ F t H). 
                      apply not_below_implies_equiv_or_incomp; auto. 

                      exact (A t H u I). 
                assert (H : ∀ s : S, s [in] X → ∀ t : S, t [in] (a :: Y) → s !<< t). 
                    intros t H u I.
                    apply in_set_cons_elim in I; auto. destruct I as [I | I].
                       assert (J := find_below_none _ _ E t H). 
                       rewrite (below_congruence _ _ _ _ (symS _ _ I) (refS t) ); auto. 
                       assert (J : t [in] (a :: X)). apply in_set_cons_intro; auto. 
                       exact (B t J u I). 
               assert (J : ∀ t : S, t [in] (a :: Y) + t [in] X → t !<< s).
                  intros t [I | I].
                     apply in_set_cons_elim in I; auto. destruct I as [I | I]. 
                        rewrite (below_congruence _ _ _ _ (refS s)  (symS _ _ I) ).
                        assert (J : a [in] (a :: X)). apply in_set_cons_intro; auto. 
                        exact (D a (inr J)).                   
                        exact (D t (inl I)).                   
                     assert (J : t [in] (a :: X)). apply in_set_cons_intro; auto. 
                     exact (D t (inr J)).
              apply in_set_cons_elim in C; auto. destruct C as [C | C].
                 assert (K : s [in] (a :: Y)). apply in_set_cons_intro; auto.
                 exact (IHX _ _ A' H s (inl K, J)).                                
                 exact (IHX _ _ A' H s (inr C, J)).                  
Qed. 
       
Lemma in_minset_intro (X : finite_set S) :
  ∀ (s : S), (s [in] X) * (∀ (t : S), t [in] X -> t !<< s) -> s [in] ([ms] X). 
Proof. intros s [A B]. 
       unfold uop_minset. 
       assert (C : ∀ (s : S), s [in] X -> ∀ (t : S), t [in] nil → s !<< t).
          intros u C t D. compute in D. discriminate D. 
       assert (D : ∀ (t : S), (t [in] nil) + (t [in] X) -> t !<< s).
         intros t [D | D]. 
            compute in D. discriminate D. 
            exact (B t D). 
       exact (in_iterate_minset_intro X nil nil empty_set_is_antichain C s (inr A, D)). 
Qed.  


Lemma iterate_minset_subset (X : finite_set S) :
  ∀ (W Y : finite_set S), ∀ (s : S), s [in] Y -> s [in] snd(iterate_minset lteS W Y X).
Proof. induction X.   
       intros W Y s A.
       unfold iterate_minset; auto. 

       intros W Y s A.
       unfold iterate_minset.
       case_eq(find (below lteS a) X).
          intros t B.
          fold (iterate_minset lteS (a :: W) Y X). 
          apply IHX; auto. 

          intros B.
          case_eq(find (below lteS a) Y).
             intros t C.
             fold (iterate_minset lteS (a :: W) Y X).
             apply IHX; auto.              

             intro C. fold (iterate_minset lteS W (a :: Y) X). 
             apply IHX; auto.                           
             apply in_set_cons_intro; auto. 
Qed.

Lemma iterate_minset_subset_v2 (X : finite_set S) :
  ∀ (W Y : finite_set S), brel_subset rS Y (snd (iterate_minset lteS W Y X)) = true. 
Proof. intros W Y. apply brel_subset_intro; auto.  apply iterate_minset_subset. Qed. 


Lemma iterate_minset_left_congruence_weak (X : finite_set S):
  ∀ (W Y1 Y2: finite_set S), Y1 [=S] Y2 ->  snd (iterate_minset lteS W Y1 X) [=S] snd(iterate_minset lteS W Y2 X).
Proof. induction X.
       intros W Y1 Y2 A. unfold iterate_minset; auto. 
       intros W Y1 Y2 A. unfold iterate_minset. 
       case_eq(find (below lteS a) X). 
          intros s B.
          fold (iterate_minset lteS (a :: W) Y1 X). 
          fold (iterate_minset lteS (a :: W) Y2 X).
          apply IHX; auto. 
          intros B.
          case_eq(find (below lteS a) Y1).
             intros s C.              
             fold (iterate_minset lteS (a :: W) Y1 X). 
             case_eq(find (below lteS a) Y2). 
             intros t D.              
             fold (iterate_minset lteS (a :: W) Y2 X). 
             apply IHX; auto. 
             intros D.              
             destruct (find_below_some Y1 _ _ C) as [E F]. 
             assert (G := find_below_none Y2 _ D). 
             rewrite (in_set_congruence _ _ symS tranS _ _ _ _ A (refS s)) in E. 
             rewrite (G s E) in F. discriminate F.
             intros C.
             fold (iterate_minset lteS W (a :: Y1) X).              
             case_eq(find (below lteS a) Y2). 
                intros s D.
                destruct (find_below_some Y2 _ _ D) as [E F]. 
                assert (G := find_below_none Y1 _ C).
                apply brel_set_symmetric in A. 
                rewrite (in_set_congruence _ _ symS tranS _ _ _ _ A (refS s)) in E. 
                rewrite (G s E) in F. discriminate F.
                intros D.
                fold (iterate_minset lteS W (a :: Y2) X).              
                assert (E : (a :: Y1) [=S] (a :: Y2)). (* extract as lemma? *) 
                apply brel_set_intro_prop; auto. split.
                    intros s E. 
                    apply in_set_cons_intro; auto.
                    apply in_set_cons_elim in E; auto.
                    destruct E as [E | E]; auto. 
                       right. rewrite (in_set_congruence _ _ symS tranS _ _ _ _ A (refS s)) in E; auto.                     
                    intros s E. 
                    apply in_set_cons_intro; auto.
                    apply in_set_cons_elim in E; auto.
                    destruct E as [E | E]; auto. 
                       right. rewrite (in_set_congruence _ _ symS tranS _ _ _ _ A (refS s)); auto.                     
                apply IHX; auto. 
Qed.


Lemma in_set_iterate_minset_false_elim (X : finite_set S) :
  ∀ (W Y : finite_set S),
    is_antichain Y ->
     (∀ s : S, s [in] X → ∀ t : S, t [in] Y → s !<< t) -> 
     (∀ (s : S), s [in] X -> s [!in] snd (iterate_minset lteS W Y X) -> {t : S & t [in] snd(iterate_minset lteS W Y X) * (t << s)}).
Proof. induction X.
       intros W U A A' s B. compute in B. discriminate B.
       intros W Y A A' s B C.
       assert (A'' : ∀ s : S, s [in] X → ∀ t : S, t [in] Y → s !<< t). 
          intros u D t E.
          assert (F : u [in] (a :: X)). apply in_set_cons_intro; auto. 
          exact (A' u F t E). 
       apply in_set_cons_elim in B; auto.
       unfold iterate_minset in C. 
       case_eq(find (below lteS a) X). 
          intros t D. rewrite D in C. 
          fold (iterate_minset lteS (a :: W) Y X) in C. 
          destruct B as [B | B].
             case_eq(in_set rS (snd (iterate_minset lteS W Y (a :: X))) t); intro E.
                exists t. split; auto.
                   rewrite (below_congruence _ _ _ _ (symS _ _ B) (refS t)).
                   destruct (find_below_some _ _ _ D) as [_ G]; auto. 
                unfold iterate_minset in E. rewrite D in E. 
                fold (iterate_minset lteS (a :: W) Y X) in E. 
                case_eq(in_set rS X t); intro F. 
                  destruct (IHX _ Y A A'' t F E) as [u [G H]]. 
                  exists u; split.
                     unfold iterate_minset.
                     rewrite D.                   
                     fold (iterate_minset lteS (a :: W) Y X); auto. 
                     destruct (find_below_some _ _ _ D) as [I J]. 
                     assert (K := below_transitive _ _ _ H J).
                     rewrite (below_congruence _ _ _ _ (symS _ _ B) (refS u)); auto. 
                     apply find_below_some in D. destruct D as [D _].
                     rewrite D in F. discriminate F. 
             destruct (IHX _ Y A A'' s B C) as [u [E F]].
             exists u. split; auto. 
                unfold iterate_minset. rewrite D. 
                fold (iterate_minset lteS (a :: W) Y X); auto. 
          intros D. rewrite D in C.
          case_eq(find (below lteS a) Y). 
             intros u E. rewrite E in C. 
             fold (iterate_minset lteS (a :: W) Y X) in C. 
             destruct B as [B | B].
                exists u. split. 
                   unfold iterate_minset. rewrite D. rewrite E. 
                   fold (iterate_minset lteS (a :: W) Y X).
                   destruct (find_below_some Y _ _ E) as [F G]. 
                   apply iterate_minset_subset; auto.
                      
                   destruct (find_below_some Y _ _ E) as [F G]. 
                   rewrite (below_congruence _ _ _ _ (symS _ _ B) (refS u)); auto.                   
                destruct (IHX _ Y A A'' s B C) as [v [F G]].
                exists v. split; auto. 
                unfold iterate_minset. rewrite D. rewrite E. 
                fold (iterate_minset lteS Y X); auto. 
                
             intro E. rewrite E in C. 
             fold (iterate_minset lteS W (a :: Y) X) in C. 
             unfold iterate_minset. rewrite D. rewrite E. 
             fold (iterate_minset lteS (a :: Y) X).
             assert (F := find_below_none _  _ D).
             assert (G := find_below_none _  _ E).             
             destruct B as [B | B]. 
                assert (I : s [in] snd (iterate_minset lteS W (a :: Y) X)).
                   assert (J : s [in] (a :: Y)). apply in_set_cons_intro; auto.
                   apply iterate_minset_subset; auto. 
                   rewrite I in C. discriminate C. 
                apply IHX; auto.
                   apply is_antichain_cons_intro; auto. 
                   intros t H. 
                   assert (I := G t H). 
                   assert (J : a !<< t). 
                      case_eq(below lteS t a); intro J; auto. 
                         assert (K : a [in] (a :: X)). apply in_set_cons_intro; auto. 
                         assert (L := A' a K t H). 
                         rewrite L in J. discriminate J. 
                   apply not_below_implies_equiv_or_incomp; auto.
                   intros u H t I. 
                   apply in_set_cons_elim in I; auto.  destruct I as [I | I].
                      rewrite (below_congruence _ _ _ _ (symS _ _ I) (refS u)). 
                      exact (F u H). 
                      exact (A'' u H t I). 
Defined.    

Lemma in_set_minset_false_elim (X : finite_set S) :
      (∀ (s : S), s [in] X -> s [!in] ([ms] X) -> {t : S & t [in] ([ms] X) *  t << s}).
Proof. unfold uop_minset. 
       intros s A B.
       assert (C : ∀ s : S, s [in] X → ∀ t : S, t [in] nil → s !<< t).
          intros u C t D. compute in D. discriminate D. 
       exact (in_set_iterate_minset_false_elim X nil nil empty_set_is_antichain C s A B). 
Defined. 

       


(********** lemmas for brel_minset ***********)

Lemma set_not_below_congruence (X1 X2 : finite_set S) (s : S): 
  X1 [=S] X2 -> (∀ t : S, t [in] X1 → t !<< s) -> ∀ t : S, t [in] X2 → t !<< s .
intros A B t C. apply set_symmetric in A. 
      rewrite (in_set_left_congruence S rS symS tranS t _ _ A) in C. exact (B t C).
Qed.

Lemma in_minset_left_congruence (X1 X2 : finite_set S) : 
  X1 [=S] X2 -> ∀ s : S, s [in] ([ms] X1) -> s [in] ([ms] X2). 
Proof. intros A s B.
       apply in_minset_elim in B.  destruct B as [B C].
       apply in_minset_intro. split. 
         rewrite (in_set_left_congruence S rS symS tranS s _ _ A) in B; auto. 
         exact (set_not_below_congruence _ _ s A C). 
Qed.

Lemma uop_minset_congruence_weak : uop_congruence (finite_set S) (brel_set rS) (uop_minset lteS).
Proof. unfold uop_congruence.
       intros X1 X2 A.
       apply brel_set_intro_prop; auto. split.
       apply in_minset_left_congruence; auto.           
       apply brel_set_symmetric in A.
       apply in_minset_left_congruence; auto.    
Qed. 

Lemma brel_minset_congruence_weak : brel_congruence (finite_set S) (brel_set rS) (brel_minset rS lteS).
Proof. unfold brel_congruence.
       intros X1 Y1 X2 Y2 A B. 
       unfold brel_minset.
       assert (C := uop_minset_congruence_weak X1 X2 A).
       assert (D := uop_minset_congruence_weak Y1 Y2 B).        
       exact (set_congruence _ _ _ _ C D). 
Qed.


Lemma set_equal_implies_minset_equal (X Y : finite_set S):  X [=S] Y -> X [=MS] Y.
Proof. intro A. unfold brel_minset.  apply uop_minset_congruence_weak; auto. Qed. 



(* move to sg/union.v *)

Lemma bop_union_subset_left  : ∀ (X Y: finite_set S), brel_subset rS X (bop_union rS X Y) = true.
Proof. intros X Y.
       apply brel_subset_intro; auto. 
       intros s A.        
       apply in_set_bop_union_intro; auto. 
Qed. 

Lemma bop_union_subset_right  : ∀ (X Y: finite_set S), brel_subset rS Y (bop_union rS X Y) = true.
Proof. intros X Y.
       apply brel_subset_intro; auto. 
       intros s A.        
       apply in_set_bop_union_intro; auto. 
Qed. 


Lemma bop_union_nil_v2 : ∀ (X : finite_set S), brel_set rS (bop_union rS X nil) X = true. 
Proof. intro X.
       assert (A := bop_union_commutative _ _ refS symS tranS X nil).
       assert (B := bop_union_with_nil_left _ _ refS symS tranS X).
       exact (set_transitive _ _ _ A B). 
Qed. 

Lemma bop_union_shift : ∀ (X Y : finite_set S) (a : S), bop_union rS X (a :: Y) [=S] bop_union rS (a :: X) Y. 
Proof. intros X Y a. 
       apply brel_set_intro; auto. split. 
       apply brel_subset_intro; auto. 
       intros s A.
       apply in_set_bop_union_intro; auto. 
       apply in_set_bop_union_elim in A; auto. 
       destruct A as [A | A].       
         left. apply in_set_cons_intro; auto. 
         apply in_set_cons_elim in A; auto. 
         destruct A as [A | A]. 
            left. apply in_set_cons_intro; auto.
            right; auto.
       apply brel_subset_intro; auto. 
       intros s A.
       apply in_set_bop_union_intro; auto. 
       apply in_set_bop_union_elim in A; auto. 
       destruct A as [A | A].       
          apply in_set_cons_elim in A; auto.
          destruct A as [A | A].
            right. apply in_set_cons_intro; auto.
            left; auto.           
         right. apply in_set_cons_intro; auto.
Qed.             
         
Lemma find_below_is_none_in_antichain (Y : finite_set S) : 
    is_antichain Y ->  ∀ (s : S),  s [in] Y -> ∀ (X : finite_set S), brel_subset rS X Y = true -> find (below lteS s) X = None.
Proof. intros A s B X C. 
       case_eq(find (below lteS s) X); auto. 
       intros t D.
       destruct (find_below_some X _ _ D) as [E F]. 
       assert (G := brel_subset_elim _ _ symS tranS _ _ C _ E).
       assert (H := A _ B _ G).
       apply equiv_or_incomp_implies_not_below in H. destruct H as [H1 H2].
       rewrite H2 in F. discriminate F. 
Qed.

Lemma is_antichain_congruence (X Y: finite_set S) : X [=S] Y -> is_antichain X -> is_antichain Y. 
Proof. intros A B. 
       apply  brel_set_elim_prop in A; auto.  destruct A as [L R].
       intros s C t D. 
       exact (B _ (R _ C) _ (R _ D)).
Qed.


Lemma iterate_minset_on_anichain (X: finite_set S):
  ∀ (W Y : finite_set S), is_antichain (bop_union rS X Y) -> snd(iterate_minset lteS W Y X) [=S] (bop_union rS X Y).
Proof. induction X.
       intros W Y A. unfold iterate_minset.
       assert (B := bop_union_with_nil_left _ _ refS symS tranS Y).
       apply set_symmetric; auto. 

       intros W Y A.
       assert (B : a [in] bop_union rS (a :: X) Y).
          apply in_set_bop_union_intro; auto.
          left. apply in_set_cons_intro; auto. 
       assert (C : find (below lteS a) X = None).
          assert (D : brel_subset rS X (bop_union rS (a :: X) Y) = true).
             assert (E : brel_subset rS X (a :: X) = true). 
                apply brel_subset_intro; auto. intros s C.
                apply in_set_cons_intro; auto.                                                        
             assert (F := bop_union_subset_left (a :: X) Y). 
             exact(brel_subset_transitive _ _ refS symS tranS _ _ _ E F). 
          exact (find_below_is_none_in_antichain _ A a B _ D).
       assert (D : find (below lteS a) Y = None).
          assert (D : brel_subset rS Y (bop_union rS (a :: X) Y) = true).
             apply bop_union_subset_right. 
          exact (find_below_is_none_in_antichain _ A a B _ D).
       unfold iterate_minset. rewrite C. rewrite D.
       fold (iterate_minset lteS (a :: Y) X). 
       assert (E : is_antichain (bop_union rS X ( a :: Y))).
          assert (E : (bop_union rS (a :: X) Y) [=S] (bop_union rS X ( a :: Y))).
             apply set_symmetric. 
             apply bop_union_shift. 
          exact (is_antichain_congruence _ _ E A). 
       assert (F := IHX W (a :: Y) E). 
       assert (G : bop_union rS X (a :: Y) [=S] bop_union rS (a :: X) Y).
          apply bop_union_shift. 
       exact (set_transitive _ _ _ F G). 
Qed. 

Lemma uop_minset_on_antichain (X : finite_set S):   is_antichain X -> ([ms] X) [=S] X.
Proof. intro A. unfold uop_minset. 
       assert (B : is_antichain (bop_union rS X nil)).
          assert (C : X [=S] (bop_union rS X nil)). 
             apply set_symmetric. apply bop_union_nil_v2.  
          exact (is_antichain_congruence _ _ C A). 
       assert (C := iterate_minset_on_anichain X nil nil B).
       assert (D : bop_union rS X nil [=S] X). apply bop_union_nil_v2.  
       exact (set_transitive _ _ _ C D). 
Qed. 

Lemma uop_minset_idempotent : uop_idempotent (finite_set S) (brel_set rS) (uop_minset lteS).   
Proof.  intro X. exact (uop_minset_on_antichain ([ms] X) (uop_minset_is_antichain X)). Qed.

Lemma in_minset_minset_intro (X : finite_set S) (a : S) (A : a [in] ([ms] X)) :  a [in] ([ms] ([ms] X)). 
Proof. assert (B := uop_minset_idempotent X). 
       rewrite <- ((in_set_congruence _ _ symS tranS _ _ _ _ B (refS a))) in A.
       exact A.
Qed. 

Lemma in_minset_minset_elim (X : finite_set S) (a : S) (A : a [in] ([ms] ([ms] X))) :  a [in] ([ms] X). 
Proof. assert (B := uop_minset_idempotent X). 
       rewrite ((in_set_congruence _ _ symS tranS _ _ _ _ B (refS a))) in A.
       exact A.
Qed. 


Lemma uop_minset_congruence : uop_congruence (finite_set S) (brel_minset rS lteS) (uop_minset lteS).
Proof. unfold uop_congruence.
       intros X1 X2 A. unfold brel_minset in A. 
       apply uop_minset_congruence_weak; auto.                           
Qed. 


(**** TRY TO PROVE THIS FROME EQV.REDUCE!!! *****************) 
Lemma brel_minset_congruence : brel_congruence (finite_set S) (brel_minset rS lteS) (brel_minset rS lteS).
Proof. unfold brel_congruence.
       intros X1 Y1 X2 Y2 A B. 
       unfold brel_minset in A, B.
       assert (C := brel_minset_congruence_weak _ _ _ _ A B). 
       unfold brel_minset, brel_reduce in C. 
       assert (D := set_congruence _ _ _ _ (uop_minset_idempotent X1) (uop_minset_idempotent Y1)).
       assert (E := set_congruence _ _ _ _ (uop_minset_idempotent X2) (uop_minset_idempotent Y2)).        
       rewrite D in C. rewrite E in C. unfold brel_minset, brel_reduce.
       exact C. 
Qed. 



Lemma brel_minset_reflexive : brel_reflexive (finite_set S) (brel_minset rS lteS).
Proof. intro X. unfold brel_minset. apply brel_set_reflexive; auto. Qed.
  
Lemma brel_minset_symmetric : brel_symmetric (finite_set S) (brel_minset rS lteS).
Proof. intros X Y. unfold brel_minset. apply brel_set_symmetric; auto. Qed.


Lemma brel_minset_transitive : brel_transitive (finite_set S) (brel_minset rS lteS).
Proof. intros X Y Z. unfold brel_minset. apply brel_set_transitive; auto.  Qed.


Definition brel_minset_new : unary_op (finite_set S)
  := λ X, if brel_set rS nil X then wS :: nil else nil.

Lemma brel_set_nil_singleton (s : S) (X : finite_set S) : nil [<>S] (s :: X). 
Proof. compute; auto. Qed. 

Lemma iterate_minset_singleton (W Y : finite_set S) (s : S) :
    (find (below lteS s) Y = None -> iterate_minset lteS W Y (s :: nil) = (W, s :: Y)) *
    (∀ t : S,  find (below lteS s) Y = Some t -> iterate_minset lteS W Y (s :: nil) = (s :: W, Y)). 
Proof. assert (B : find (below lteS s) nil = None). compute; auto.
       split.
       intro A. unfold iterate_minset.
       rewrite B. rewrite A. reflexivity. 
       intros t A. unfold iterate_minset.
       rewrite B. rewrite A. reflexivity. 
Qed.


Lemma iterate_minset_invariant_0 (X : finite_set S) : 
  ∀ (W1 W2 Y : finite_set S), (snd (iterate_minset lteS W1 Y X)) = (snd (iterate_minset lteS W2 Y X)). 
Proof. induction X. 
       + intros W1 W2 Y. simpl. reflexivity. 
       + intros W1 W2 Y.
         unfold iterate_minset. 
         case_eq(find (below lteS a) X).
         ++ intros s B.
            fold (iterate_minset lteS (a :: W1) Y X).
            fold (iterate_minset lteS (a :: W2) Y X).
            exact (IHX (a :: W1) (a :: W2) Y).
         ++ intro B.
            case_eq(find (below lteS a) Y).
            +++ intros t C. 
                fold (iterate_minset lteS (a :: W1) Y X).
                fold (iterate_minset lteS (a :: W2) Y X).
                exact (IHX (a :: W1) (a :: W2) Y).
            +++ intro C. 
                fold (iterate_minset lteS W1 (a :: Y) X).
                fold (iterate_minset lteS W2 (a :: Y) X).
                exact (IHX W1 W2 (a :: Y)).
Qed. 
            
Lemma iterate_minset_invariant_1 (X : finite_set S) : 
  ∀ (W Y : finite_set S), (W [U] (Y [U] X)) [=S] ((fst (iterate_minset lteS W Y X)) [U] (snd (iterate_minset lteS W Y X))). 
Proof. induction X. 
       + intros W Y. simpl. 
         assert (A := bop_union_with_nil_right _ _ refS symS tranS Y). 
         assert (B := bop_union_congruence _ _ refS symS tranS _ _ _ _ (set_reflexive W) A).
         exact B. 

       + intros W Y.
         unfold iterate_minset.
         assert (E1 : (W [U] (Y [U] (a :: X))) [=S] ((a :: W) [U] (Y [U] X))).
             apply set_symmetric. 
             assert (A := bop_union_shift_element S rS refS symS tranS X Y a).
             assert (B := bop_union_push_element S rS refS symS tranS X Y a).          
             assert (C := bop_union_shift_element S rS refS symS tranS (Y [U] X) W a).
             assert (D := bop_union_congruence _ _ refS symS tranS _ _ _ _ (set_reflexive W) B).
             assert (E := set_transitive _ _ _ C D).
             assert (F := bop_union_congruence _ _ refS symS tranS _ _ _ _ (set_reflexive W) A).             
             assert (G := set_transitive _ _ _ E F).
             exact G. 
         assert (E2 : (W [U] (Y [U] (a :: X))) [=S] (W [U] ((a :: Y) [U] X))).
             assert (A := bop_union_shift_element S rS refS symS tranS X Y a).
             assert (B := bop_union_congruence _ _ refS symS tranS _ _ _ _ (set_reflexive W) A).
             apply set_symmetric.              
             exact B.
         case_eq(find (below lteS a) X).
         ++ intros s A.        
            fold(iterate_minset lteS (a :: W) Y X).               
            assert (B := IHX (a :: W) Y).
            exact (set_transitive _ _ _ E1 B). 

         ++ intro A. 
            case_eq(find (below lteS a) Y).
            +++ intros t B. 
                fold(iterate_minset lteS (a :: W) Y X).
                assert (C := IHX (a :: W) Y).
                exact (set_transitive _ _ _ E1 C). 
            +++ intro B. 
                fold(iterate_minset lteS W (a :: Y) X).
                assert (C := IHX W (a :: Y)).
                exact (set_transitive _ _ _ E2 C). 
Qed. 

Lemma iterate_minset_invariant_increasing (X : finite_set S) :
  ∀ (W Y : finite_set S) (y : S), y [in] Y -> y [in] snd (iterate_minset lteS W Y X). 
Proof. induction X.
       + intros W Y y A. unfold iterate_minset. simpl. exact A. 
       + intros W Y y A.
         unfold iterate_minset. 
         case_eq(find (below lteS a) X). 
         ++ intros s B. 
            fold (iterate_minset lteS (a :: W) Y X). 
            exact (IHX (a :: W) Y y A). 
         ++ intro B. 
            case_eq(find (below lteS a) Y). 
            +++ intros s C.
                fold (iterate_minset lteS (a :: W) Y X). 
                exact (IHX (a :: W) Y y A).                 
            +++ intro C. 
                fold (iterate_minset lteS W (a :: Y) X).
                assert (D : y [in] (a :: Y)). apply in_set_cons_intro; auto. 
                exact (IHX W (a :: Y) y D).                 
Qed. 



Lemma iterate_minset_invariants (X : finite_set S) : 
  ∀ (W Y : finite_set S),
    (∀ w : S,  w [in] W -> {t : S & (t [in] (Y [U] X)) * t << w}) ->
    (∀ y x : S,  y [in] Y -> x [in] X -> x !<< y) ->     
    (∀ w : S,  w [in] fst (iterate_minset lteS W Y X) -> {t : S & t [in] (snd(iterate_minset lteS W Y X)) * (t << w)}). 
Proof. induction X. 
       + intros W Y A B w C.
         unfold iterate_minset in C. simpl in C.
         unfold iterate_minset. simpl.
         destruct (A _ C) as [t [D E]]. 
         exists t. split; auto.
         apply in_set_bop_union_elim in D; auto.
         destruct D as [D | D]; auto.
            compute in D. discriminate D. 
       + intros W Y A B w C.
         unfold iterate_minset in C. 
         unfold iterate_minset.          
         case_eq(find (below lteS a) X). 
         ++ intros t D.
            rewrite D in C.
            fold (iterate_minset lteS (a :: W) Y X).
            fold (iterate_minset lteS (a :: W) Y X) in C.
            apply IHX.
            +++ intros x E.
                apply in_set_cons_elim in E; auto.
                destruct E as [E | E].
                ++++ apply find_below_some in D. destruct D as [D1 D2].
                     rewrite (below_congruence _ _ _ _ E (refS t)) in D2.
                     exists t. split; auto. 
                     apply in_set_bop_union_intro; auto. 
                ++++ destruct (A _ E) as [z [F G]].
                     apply find_below_some in D. destruct D as [D1 D2].
                     apply in_set_bop_union_elim in F; auto.                     
                     destruct F as [F | F].
                     +++++ exists z. split; auto.
                           apply in_set_bop_union_intro; auto. 
                     +++++ apply in_set_cons_elim in F; auto.                                            
                           destruct F as [F | F].
                           ++++++ exists t. split.
                                  apply in_set_bop_union_intro; auto.
                                  rewrite (below_congruence _ _ _ _ (refS x) (symS _ _ F)) in G.
                                  exact (below_transitive _ _ _ D2 G). 
                           ++++++ exists z. split; auto.
                                 apply in_set_bop_union_intro; auto. 
            +++ intros y x E F.
                assert (G : x [in] (a :: X)). apply in_set_cons_intro; auto. 
                apply B; auto.
            +++ exact C. 
         ++ intro D.
            rewrite D in C.
            case_eq (find (below lteS a) Y).
            +++ intros t E.
                rewrite E in C.
                fold (iterate_minset lteS (a :: W) Y X).
                fold (iterate_minset lteS (a :: W) Y X) in C.
                apply IHX.
                ++++ intros z F.
                     apply in_set_cons_elim in F; auto.
                     destruct F as [F | F].
                     +++++ apply find_below_some in E. destruct E as [E1 E2].
                           rewrite (below_congruence _ _ _ _ F (refS t)) in E2.                           
                           exists t. split; auto. 
                           apply in_set_bop_union_intro; auto.
                     +++++ destruct (A _ F) as [v [G H]].
                           apply in_set_bop_union_elim in G; auto. 
                           destruct G as [G | G].
                           ++++++ exists v. split; auto.
                                  apply in_set_bop_union_intro; auto.
                           ++++++ apply in_set_cons_elim in G; auto.
                                  destruct G as [G | G].
                                     apply find_below_some in E.  destruct E as [E1 E2].
                                     rewrite (below_congruence _ _ _ _ G (refS t)) in E2.                           
                                     exists t. split; auto. 
                                     apply in_set_bop_union_intro; auto.
                                     exact (below_transitive _ _ _ E2 H).                                      
                                     exists v. split; auto.
                                     apply in_set_bop_union_intro; auto.
                ++++ intros y x F G.
                     assert (H : x [in] (a :: X)). apply in_set_cons_intro; auto.
                     exact (B _ _ F H). 
                ++++ exact C. 
            +++ intro E.
                rewrite E in C.
                fold (iterate_minset lteS W (a :: Y) X).
                fold (iterate_minset lteS W (a :: Y) X) in C.
                apply IHX.
                ++++ intros z F.
                     destruct (A _ F) as [v [G H]].
                     exists v. split; auto.
                     apply in_set_bop_union_intro; auto. 
                     apply in_set_bop_union_elim in G; auto.
                     destruct G as [G | G].
                     +++++ left. apply in_set_cons_intro; auto. 
                     +++++ apply in_set_cons_elim in G; auto.
                           destruct G as [G | G]. 
                           ++++++ left. apply in_set_cons_intro; auto. 
                           ++++++ right. exact G.                        
                ++++ intros y x F G.
                     apply in_set_cons_elim in F; auto.
                     destruct F as [F | F].
                     +++++ assert (H := find_below_none _ _ D).
                           assert (I := find_below_none _ _ E).
                           assert (J := H _ G).
                           rewrite (below_congruence _ _ _ _ (symS _ _ F) (refS x)).
                           exact J. 
                     +++++ assert (I : x [in] (a :: X)). apply in_set_cons_intro; auto.
                           exact (B _ _ F I). 
                ++++ exact C. 
Qed. 
         
(* This theorem was inspired Lemma 1 in  Martelli's 1974 paper 
  "An application of regular algebra to the enumeration of cut sets in a graph", 
   Information Processing 74. 
*) 
Theorem fundamental_minset_theorem (X : finite_set S) : 
   {Z : finite_set S &
        (X [=S] (([ms] X) [U] Z) ) *
        (∀ (s : S), s [in] Z -> {t : S & (t [in] ([ms] X)) * t << s })
   }.
Proof. unfold uop_minset.
       assert (A := iterate_minset_invariant_1 X nil nil). 
       exists (fst (iterate_minset lteS nil nil X)). split. 
       + assert (B : X [=S] (nil [U] (nil [U] X))).
            assert (C := bop_union_with_nil_left S rS refS symS tranS X). 
            assert (D := bop_union_with_nil_left S rS refS symS tranS ((nil [U] X))). 
            assert (E := set_transitive _ _ _ D C).
            apply set_symmetric. exact E.
         assert (C := set_transitive _ _ _ B A).
         assert (D := bop_union_commutative _ _ refS symS tranS (fst (iterate_minset lteS nil nil X)) (snd (iterate_minset lteS nil nil X))).
         assert (E := set_transitive _ _ _ C D). 
         exact E. 
       + intros s B.
         assert (C : ∀ w : S, w [in] nil → {t : S & t [in] (nil [U] X) * t << w}).
           intros w C. compute in C. discriminate C. 
         assert (D : ∀ y x : S, y [in] nil → x [in] X → x !<< y).
           intros y x D. compute in D. discriminate D.            
         assert (E := iterate_minset_invariants X nil nil C D s B). unfold snd in E.
         exact E. 
Qed. 
       

Lemma brel_minset_nil_singleton (X : finite_set S) : ∀ (s : S), nil [<>MS] (s :: X).
Proof. unfold brel_minset, brel_reduce.
       induction X; intro s. 
       - compute; auto. 
       - unfold uop_minset, iterate_minset.            
            case_eq(find (below lteS s) (a :: X)).
               intros t A. 
               case_eq(find (below lteS a) X).
                  intros u B. 
                  fold(iterate_minset lteS (a :: s :: nil) nil X). 
                  assert (C := IHX a).                
                  unfold uop_minset, iterate_minset in C. rewrite B in C. 
                  fold(iterate_minset lteS (a :: nil) nil X) in C; auto.
                  assert (D := iterate_minset_invariant_0 X (a :: nil) (a :: s :: nil) nil).
                  unfold snd in D. rewrite D in C. exact C. 
                  intros B.
                  assert (C : find (below lteS a) nil = None). compute; auto. rewrite C. 
                  fold(iterate_minset lteS (s :: nil) (a :: nil) X). 
                  case_eq(brel_set rS nil (snd (iterate_minset lteS (s :: nil) (a :: nil) X))); intro D; auto. 
                    assert (E : brel_subset rS (a :: nil) (snd (iterate_minset lteS  (s :: nil) (a :: nil) X)) = true).
                      apply iterate_minset_subset_v2.
                  apply brel_set_elim in D; auto. destruct D as [_ D].
                  assert (F := brel_subset_transitive _ rS refS symS tranS _ _ _ E D). 
                  compute in F. discriminate F. 


               intros A.
               assert (C : find (below lteS s) nil = None). compute; auto. rewrite C.                   
               case_eq(find (below lteS a) X).
                  intros u B. 
                  fold(iterate_minset lteS (a :: nil) (s :: nil) X). 
                  case_eq(brel_set rS nil (snd(iterate_minset lteS (a :: nil) (s :: nil) X))); intro D; auto. 
                    assert (E : brel_subset rS (s :: nil) (snd (iterate_minset lteS (a :: nil) (s :: nil) X)) = true).
                      apply iterate_minset_subset_v2.
                    apply brel_set_elim in D; auto. destruct D as [_ D].
                    assert (F := brel_subset_transitive _ rS refS symS tranS _ _ _ E D). 
                    compute in F. discriminate F. 


                  intro B. 
                  case_eq(find (below lteS a) (s :: nil)).
                  intros w D. 
                  fold(iterate_minset lteS (a :: nil) (s :: nil) X).                   
                  case_eq(brel_set rS nil (snd (iterate_minset lteS (a :: nil) (s :: nil) X))); intro E; auto. 
                    assert (F : brel_subset rS (s :: nil) (snd (iterate_minset lteS (a :: nil) (s :: nil) X)) = true).
                      apply iterate_minset_subset_v2.
                    apply brel_set_elim in E; auto. destruct E as [_ E].
                    assert (G := brel_subset_transitive _ rS refS symS tranS _ _ _ F E). 
                    compute in G. discriminate G. 


                  intros D. 
                  fold(iterate_minset lteS nil (a :: s :: nil) X).                   
                  case_eq(brel_set rS nil (snd (iterate_minset lteS nil (a :: s :: nil) X))); intro E; auto. 
                    assert (F : brel_subset rS (a :: s :: nil) (snd (iterate_minset lteS  nil (a :: s :: nil) X)) = true).
                      apply iterate_minset_subset_v2.
                    apply brel_set_elim in E; auto. destruct E as [_ E].
                    assert (G := brel_subset_transitive _ rS refS symS tranS _ _ _ F E). 
                    compute in G. discriminate G. 
Qed. 

Lemma brel_minset_singleton_nil (s : S) (X : finite_set S): (s :: X) [<>MS] nil.
 Proof. case_eq(brel_minset rS lteS (s :: X) nil); intro A; auto. 
       apply brel_minset_symmetric in A.
       rewrite brel_minset_nil_singleton in A.       discriminate A. 
Qed.

Lemma brel_minset_not_trivial : brel_not_trivial (finite_set S) (brel_minset rS lteS) brel_minset_new.
Proof. unfold brel_not_trivial. intro X. 
       destruct X. 
       unfold brel_minset_new. rewrite (set_reflexive nil). split; compute; auto. 
       unfold brel_minset_new. rewrite brel_set_nil_singleton.
       rewrite brel_minset_nil_singleton. rewrite brel_minset_singleton_nil; auto.  
Qed. 


Definition minset_negate ( X Y : finite_set S) :=
   match uop_minset lteS X, uop_minset lteS Y with 
   | nil, nil => wS :: nil
   | nil, t::_ => (fS t) :: nil 
   | t::_, nil => (fS t) :: nil      
   | t :: _, u :: _ => nil 
  end. 




Lemma brel_minset_negate_left (X Y : finite_set S) : brel_minset rS lteS X (minset_negate X Y) = false.
Proof. destruct X; destruct Y.
       compute; auto. 
       unfold minset_negate. rewrite minset_empty.
       case_eq([ms] (s :: Y)).
          intro A. apply brel_minset_nil_singleton.  
          intros t Z A. apply brel_minset_nil_singleton.  
       unfold minset_negate. rewrite minset_empty.       
       case_eq([ms] (s :: X)).
       intro A. unfold brel_minset.  unfold brel_reduce. rewrite minset_singleton.
       assert (B := brel_minset_nil_singleton X s). unfold brel_minset, brel_reduce in B.
       rewrite A in B. compute in B. discriminate B. 
       intros t Z A.  unfold brel_minset, brel_reduce.  rewrite minset_singleton. 
          case_eq(brel_set rS ([ms] (s :: X)) (fS t :: nil)); intro B; auto. 
             rewrite A in B. apply set_symmetric in B. 
             apply brel_set_elim in B; auto. destruct B as [_ B].
             assert (C := brel_subset_elim _ _ symS tranS _ _ B). 
             assert (D : t [in] (t :: Z)). apply in_set_cons_intro; auto. 
             assert (E := C _ D). compute in E.
             destruct (Pf t) as [F G].  
             rewrite F in E. discriminate E. 
       unfold minset_negate.
       case_eq([ms] (s :: X)).
          intro A.
          assert (B : nil [=MS] (s :: X)).
             unfold brel_minset, brel_reduce. rewrite A. compute; auto. 
          rewrite brel_minset_nil_singleton  in B. discriminate B. 
          intros t Z A. 
          case_eq([ms] (s0 :: Y)). 
             intro B. unfold brel_minset, brel_reduce.
             rewrite A.
             case_eq(brel_set rS (t :: Z) ([ms] (fS t :: nil))); intro C; auto. 
                apply brel_set_elim in C; auto. destruct C as [C _].
                assert (D := brel_subset_elim _ _ symS tranS _ _ C). 
                assert (E : t [in] (t :: Z)). apply in_set_cons_intro; auto. 
                assert (F := D _ E). compute in F.
                destruct (Pf t) as [G H].  
               rewrite G in F. discriminate F. 
             intros u W B.
             apply brel_minset_singleton_nil.
Qed. 

Lemma brel_minset_negate_comm (X Y : finite_set S) : minset_negate X Y = minset_negate Y X.
Proof. destruct X; destruct Y; unfold minset_negate; simpl; auto.
       destruct(uop_minset lteS (s :: X)); destruct (uop_minset lteS (s0 :: Y)); auto. 
Qed.

Lemma brel_minset_negate_right (X Y : finite_set S) : brel_minset rS lteS Y (minset_negate X Y) = false.
Proof. rewrite brel_minset_negate_comm. apply brel_minset_negate_left. Qed. 


Lemma brel_minset_not_exactly_two : brel_not_exactly_two (finite_set S) (brel_minset rS lteS). 
Proof. unfold brel_not_exactly_two. exists minset_negate. 
       intros X Y. right. split.
       apply brel_minset_negate_left.
       apply brel_minset_negate_right.
Defined. 


(* we really want fully lazy sets here.  fix this someday.... *) 
Definition minset_enum (enum : unit -> list S) (x : unit) :=  List.map (uop_minset lteS) (power_set S (enum x)).

Lemma empty_set_in_minset_enum (f : unit -> list S) : in_set (brel_minset rS lteS) (minset_enum f tt) nil = true.
Admitted. 
       
Lemma min_set_enum_cons (f : unit -> list S) (pf : ∀ s : S, in_set rS (f tt) s = true) (a : S) (X : finite_set S) : 
        in_set rS (f tt) a = true -> 
        in_set (brel_minset rS lteS) (minset_enum f tt) X = true -> 
        in_set (brel_minset rS lteS) (minset_enum f tt) (a :: X) = true. 
Admitted. 

Lemma minset_enum_lemma (f : unit → list S) (pf : ∀ s : S, in_set rS (f tt) s = true) (X : finite_set S) : 
  in_set (brel_minset rS lteS) (minset_enum f tt) X = true.
Proof.  induction X. 
        apply empty_set_in_minset_enum. 
        assert (aIn := pf a). 
        apply min_set_enum_cons; auto. 
Qed. 


Definition brel_minset_is_finite : carrier_is_finite S rS -> carrier_is_finite (finite_set S) (brel_minset rS lteS).
Proof. unfold carrier_is_finite.   intros [f pf].
       exists (minset_enum f). intro X. 
       apply minset_enum_lemma; auto.
Defined. 


Definition squash : list (finite_set S) -> list S
  := fix f l :=
       match l with
       | nil => nil
       | X :: rest => X ++ (f rest)
       end.

Lemma brel_minset_singleton_elim (X : finite_set S) (s : S) : X [=MS] (s :: nil) → s [in] X. 
Proof. intro A.
       unfold brel_minset, brel_reduce in A. 
       rewrite minset_singleton in A. 
       apply brel_set_elim in A; auto. destruct A as [_ A].
       assert (B := brel_subset_elim _ _ symS tranS _ _ A).
       assert (C : s [in] (s :: nil)). compute. rewrite refS; auto. 
       assert (D := B _ C).
       apply in_minset_elim in D. destruct D as [D _]; auto. 
Qed.


Lemma squash_lemma (s : S) (X : list (finite_set S)) (H : in_list (brel_minset rS lteS) X (s :: nil) = true) : in_list rS (squash X) s = true. 
Proof. induction X. compute in H. discriminate H.
       apply in_list_cons_elim in H.
       unfold squash; fold squash.
       apply in_list_concat_intro.
       destruct H as [H | H].       
          left. apply brel_minset_singleton_elim; auto. 
          right. apply IHX; auto. 
       apply brel_minset_symmetric; auto.
Qed.        


Definition brel_minset_is_not_finite : carrier_is_not_finite S rS -> carrier_is_not_finite (finite_set S) (brel_minset rS lteS).
Proof. unfold carrier_is_not_finite.   
       intros H f. 
       destruct (H (λ _, squash (f tt))) as [s Ps].
       exists (s :: nil). 
       case_eq(in_list (brel_minset rS lteS) (f tt) (s :: nil)); intro J; auto.
       apply squash_lemma in J. rewrite J in Ps. exact Ps. 
Defined.

Definition brel_minset_finite_decidable (d : carrier_is_finite_decidable S rS) : carrier_is_finite_decidable (finite_set S) (brel_minset rS lteS)
  := match d with
     | inl fS  => inl (brel_minset_is_finite fS)
     | inr nfS => inr (brel_minset_is_not_finite nfS)                       
     end.

(*
Lemma minset_total (t : S) (anti: brel_antisymmetric S rS lteS) (tot : brel_total S lteS) (X : finite_set S) :
       ([ms] X = nil) + {s : S & [ms] X = (s ::nil)}. 
Proof. induction X. 
       left. compute. reflexivity. 
       right. unfold uop_minset.
       exists t.
       unfold iterate_minset.
       case_eq(find (below lteS a) X); intro b. intro A. 
          fold (iterate_minset lteS nil X). admit. 
          case_eq(find (below lteS a) nil); intro c. intro B. 
             compute in B. discriminate B. 
             fold (iterate_minset lteS (a :: nil) X). admit. 
Admitted. 
 *)



(*****************************************************************************)
(***************************** UPPER SETS ************************************)
(*****************************************************************************)

Definition in_upperset (X :finite_set S) (s : S) := brel_set rS ([ms] (s :: X)) ([ms] X).

Notation "a [inup] b"  := (in_upperset b a = true)   (at level 15).
Notation "a [!inup] b"  := (in_upperset b a = false)   (at level 15).

Lemma minset_is_minimal (a : S) (X : finite_set S) (A : a [in] X) : {b : S & (b [in] [ms] X) * (b <<= a)}.
Proof. case_eq(in_set rS ([ms] X) a); intro C.
       - exists a. split; auto. 
       - apply in_set_minset_false_elim in C; auto. 
         * destruct C as [t [D E]].
           exists t. split; auto.
           apply below_elim in E. destruct E as [E _]; auto. 
Defined. 



Lemma in_upperset_intro
  (anti : brel_antisymmetric S rS lteS)
  (a b : S) (X : finite_set S) (A : b [in] [ms] X) (B : b <<= a) : a [inup] X.
Proof. (*apply in_minset_elim in A; auto. destruct A as [A C].*) 
       unfold in_upperset.
       apply brel_set_intro_prop; auto. split; intros c D. 
       - apply in_minset_elim in D; auto. destruct D as [D E].
         apply in_set_cons_elim in D; auto.
         destruct D as [D | D].
         + assert (F : b [in] (a :: X)).
           {
             apply in_minset_elim in A; auto. destruct A as [A _].
             apply in_set_cons_intro; auto. 
           } 
           assert (G := E _ F). apply symS in D. 
           rewrite (below_congruence _ _ _ _  D (refS b)) in G.
           apply below_false_elim in G.
           destruct G as [G | G].
           * rewrite G in B. discriminate B. 
           * assert (H := anti _ _ G B).
             assert (I := tranS _ _ _ D H). apply symS in I. 
             exact(in_set_right_congruence S rS symS tranS _ _ _ I A). 
         + apply in_minset_intro. split; auto.
           intros t F. apply E. 
           apply in_set_cons_intro; auto. 
       - apply in_minset_elim in D; auto.
         destruct D as [D E]. 
         apply in_minset_intro. split; auto.
         + apply in_set_cons_intro; auto. 
         + intros t F. 
           apply in_set_cons_elim in F; auto.
           destruct F as [F | F]; auto.
           * case_eq(below lteS c t); intro G; auto.
             rewrite <- (below_congruence _ _ _ _  (refS c) F) in G.
             assert (H := below_pseudo_transitive_left _ lteS lteTrans _ _ _ B G).
             apply in_minset_elim in A; auto. destruct A as [A C].
             rewrite (E _ A) in H.
             discriminate H. 
Qed. 


Lemma in_upperset_elim (a : S) (X : finite_set S) (A : a [inup] X) : {b : S & (b [in] [ms] X) * (b <<= a)}.
Proof. case_eq(in_set rS X a); intro B.
       - apply minset_is_minimal; auto.
       - unfold in_upperset in A.
         apply brel_set_elim_prop in A; auto.
         destruct A as [A C].
         case_eq(in_set rS ([ms] (a :: X)) a); intro D.
         + assert (E := A _ D).
           apply in_minset_elim in E; auto.
           destruct E as [E _].
           rewrite E in B. discriminate B. 
         + apply in_set_minset_false_elim in D.
           * destruct D as [t [E F]].
             exists t. split.
             -- apply in_minset_elim in E; auto.
                destruct E as [E G].
                apply in_set_cons_elim in E; auto. 
                destruct E as [E | E].
                ++ assert (H := below_congruence _ _ _ _ (refS a) E).
                   rewrite <- H in F.
                   rewrite below_not_reflexive in F; auto. 
                   discriminate F. 
                ++ apply in_minset_intro; auto; split; auto.
                   intros v H.
                   assert (I : v [in] (a :: X)). apply in_set_cons_intro; auto. 
                   exact (G _ I). 
             -- apply below_elim in F. destruct F as [F _]; auto. 
           * apply in_set_cons_intro; auto. 
Defined. 

Lemma in_upperset_false_elim
  (anti : brel_antisymmetric S rS lteS)      
  (a : S) (X : finite_set S) (A : a [!inup] X) : ∀ b: S, (b [!in] [ms] X) + (b !<<= a).
Proof. intro b. case_eq(lteS b a); intro B; auto. left.
       case_eq(in_set rS ([ms] X) b); intro C; auto.
       unfold in_upperset in A.
       apply brel_set_false_elim_prop in A; auto. 
       destruct A as [ [c [D E]] | [c [D E]] ].
       - apply in_minset_elim in D; auto. destruct D as [D F].
         apply in_set_minset_false_elim in E; auto.
         + destruct E as [t [E G]].
           apply in_minset_elim in E; auto. destruct E as [E H].
           assert (I : t [in] (a :: X)). apply in_set_cons_intro; auto. 
           rewrite (F _ I) in G. discriminate G.
         + apply in_set_cons_elim in D; auto. 
           destruct D as [D | D]; auto.
           assert (I : b [in] (a :: X)).
           {
             assert (G := in_minset_implies_in_set _ _ C).
             apply in_set_cons_intro; auto. 
           } 
           assert (J := F _ I).
           apply below_false_elim in J.
           destruct J as [J | J].
           * rewrite <- (lteCong _ _ _ _ (refS b) D) in J.
             rewrite J in B. discriminate B. 
           * rewrite <- (lteCong _ _ _ _ D (refS b)) in J.
             assert (K := anti _ _ J B).
             apply in_minset_elim in C. destruct C as [C _].
             apply symS in D.
             assert (L := tranS _ _ _ D K). apply symS in L. 
             exact(in_set_right_congruence S rS symS tranS _ _ _ L C). 
       - apply in_minset_elim in D; auto. destruct D as [D F].
         apply in_set_minset_false_elim in E; auto.
         + destruct E as [t [E G]].
           apply in_minset_elim in E; auto. destruct E as [E H].
           apply in_set_cons_elim in E; auto.
           destruct E as [E | E].
           * assert (I : b [in] (a :: X)).
             {
               assert (J := in_minset_implies_in_set _ _ C).
               apply in_set_cons_intro; auto. 
             } 
             assert (J := H _ I).
             rewrite (lteCong _ _ _ _ (refS b) E) in B.
             assert (L := below_pseudo_transitive_left _ lteS lteTrans _ _ _ B G).
             assert (M : b [in] X). exact(in_minset_implies_in_set _ _ C).
             rewrite (F _ M) in L. discriminate L. 
           * rewrite (F _ E) in G. discriminate G. 
         + apply in_set_cons_intro; auto. 
Qed.

(* needed? 
Lemma in_upperset_false_intro 
  (anti : brel_antisymmetric S rS lteS)      
  (a : S) (X : finite_set S) (A : ∀ b: S, (b [!in] [ms] X) + (b !<<= a)) : a [!inup] X.
Admitted.
(*
Proof. unfold in_upperset.
       apply brel_set_false_intro_prop; auto.
       destruct (A a) as [B | B].
       - case_eq(in_set rS ([ms] (a :: X)) a); intro C.
         + left. exists a; auto. 
         + case_eq(in_set rS X a); intro D.
           * assert (E := minset_is_minimal _ _ D).
             destruct E as [b [E F]].
             admit. 
           * apply in_set_minset_false_elim in C; auto.
             -- destruct C as [t [C E]].
                apply in_minset_elim in C; auto.
                destruct C as [C F]. 
             -- apply in_set_cons_intro; auto. 






           assert (D : a [in] ([ms] (a :: X))).
           {
             apply in_minset_intro; auto. split.
             * apply in_set_cons_intro; auto. 
             * intros t D.
               destruct (A t) as [E | E].
               -- apply below_false_intro.
                  apply in_set_cons_elim in D.
                  destruct D as [D | D].
                  ++ right. rewrite (lteCong _ _ _ _ D (refS t)); auto. 
                  ++ 
               -- apply below_false_intro. left. auto. 
           }
           rewrite D in C. discriminate C. 
       - rewrite lteRefl in B. discriminate B. 
Defined. 
*) 
*) 

Lemma in_minset_implies_in_upperset
  (anti : brel_antisymmetric S rS lteS)
  (a : S) (X : finite_set S) (A : a [in] [ms] X) : a [inup] X.
Proof. exact (in_upperset_intro anti a a X A (lteRefl a)). Qed.  


(* needed? 
Lemma ttt (a : S) (X : finite_set S) : (a [inup] X) = (a [inup] ([ms] X)).
Proof. unfold in_upperset.
       case_eq(brel_set rS ([ms] (a :: X)) ([ms] X)); intro A;
         case_eq(brel_set rS (([ms] (a :: [ms] X))) ([ms] ([ms] X))); intro B; auto.
       - admit. 
       - admit. 
Admitted.
*) 

Lemma mimimal_elements_are_equal
  (anti : brel_antisymmetric S rS lteS)
  (a b: S) (X : finite_set S) (A : a [in] X) (B : b [in] [ms] X) (C : a <<= b) : a [=] b. 
Proof. apply in_minset_elim in B; auto. destruct B as [_ E].
       assert (G := E _ A). apply below_false_elim in G.
       destruct G as [G | G].
       - rewrite C in G. discriminate G.
       - apply anti; auto. 
Qed.

Lemma minset_equal_intro_aux
  (anti : brel_antisymmetric S rS lteS) 
  (a : S) (X Y: finite_set S)
  (A : ∀ a : S, in_upperset X a = in_upperset Y a) 
  (B : a [in] ([ms] Y)) : a [in] ([ms] X). 
Proof. case_eq(in_set rS X a); intro Z.
         + case_eq(in_set rS ([ms] X) a); intro E; auto.
           apply in_set_minset_false_elim in E; auto. 
           destruct E as [t [F G]].
           assert (H := in_minset_implies_in_upperset anti _ _ F).
           assert (I := A t). rewrite H in I. symmetry in I. 
           apply in_upperset_elim in I.
           destruct I as [s [J K]].
           assert (L := below_pseudo_transitive_left _ lteS lteTrans _ _ _ K G).
           apply in_minset_elim in B.
           destruct B as [B M].
           apply in_minset_elim in J. destruct J as [J _].
           rewrite (M _ J) in L. discriminate L.
         + assert (C := in_minset_implies_in_upperset anti _ _ B).
           assert (D := A a). rewrite C in D.
           apply in_upperset_elim in D.
           destruct D as [b [E F]].
           assert (G := A b).
           assert (H := in_minset_implies_in_upperset anti _ _ E).
           rewrite H in G. symmetry in G.
           apply in_upperset_elim in G.
           destruct G as [c [I J]].
           assert (K := lteTrans _ _ _ J F).
           apply in_minset_elim in I; auto. destruct I as [I _]. 
           assert (L := mimimal_elements_are_equal anti _ _ _ I B K). 
           rewrite (lteCong _ _ _ _ L (refS b)) in J.
           assert (M := anti _ _ F J).
           apply in_minset_elim in E; auto. destruct E as [E _].
           rewrite (in_set_right_congruence S rS symS tranS _ _ _ M E) in Z. 
           discriminate Z.
Qed. 

Lemma minset_equal_intro (X Y: finite_set S)
  (anti : brel_antisymmetric S rS lteS) : 
  (∀ a : S, (in_upperset X a) = (in_upperset Y a)) -> ([ms] X) [=S] ([ms] Y).
Proof. intro A.
       apply brel_set_intro_prop; auto. split; intros a B.
       - assert (A' : ∀ a : S, in_upperset Y a = in_upperset X a).
         {
           intro b. rewrite (A b). reflexivity. 
         }
         exact (minset_equal_intro_aux anti a Y X A' B). 
       - exact (minset_equal_intro_aux anti a X Y A B). 
Qed. 

Lemma minset_equal_elim (X Y: finite_set S)
  (anti : brel_antisymmetric S rS lteS) : 
  ([ms] X) [=S] ([ms] Y) -> ∀ a : S, (in_upperset X a) = (in_upperset Y a).
Proof. intros A a.
       apply brel_set_elim_prop in A; auto.
       destruct A as [A B]. 
       case_eq(in_upperset X a); intro C;
         case_eq(in_upperset Y a); intro D; auto.
       - apply in_upperset_elim in C.
         destruct C as [b [E F]].
         assert (G := A _ E).
         destruct (in_upperset_false_elim anti _ _ D b) as [H | H].
         + rewrite H in G. discriminate G. 
         + rewrite H in F. discriminate F. 
       - apply in_upperset_elim in D.
         destruct D as [b [E F]].
         assert (G := B _ E).
         destruct (in_upperset_false_elim anti _ _ C b) as [H | H].
         + rewrite H in G. discriminate G. 
         + rewrite H in F. discriminate F. 
Qed. 

End Theory.



Section ACAS.

(* can we use eqv/reduce.v? 

A_eqv_reduce
     : ∀ (S : Type) 
         (eqvS : structures.A_eqv S) 
         (r : unary_op S) 
         (f : S → S),
         brel_not_trivial S (brel_reduce (structures.A_eqv_eq S eqvS) r) f
         → brel_exactly_two_decidable S (brel_reduce (structures.A_eqv_eq S eqvS) r)
           → carrier_is_finite_decidable S (brel_reduce (structures.A_eqv_eq S eqvS) r) → ast.cas_eqv_ast → structures.A_eqv S
*)   

Definition eqv_proofs_brel_minset_from_qo
  (S : Type)
  (r : brel S)
  (lteS : brel S)
  (eqv : eqv_proofs S r)
  (lteP : qo_proofs S r lteS) : eqv_proofs (finite_set S) (brel_minset r lteS) := 
  let refS := A_eqv_reflexive S r eqv in
  let symS := A_eqv_symmetric S r eqv in
  let trnS := A_eqv_transitive S r eqv in
  let lteCong := A_qo_congruence _ _ _ lteP in
  let lteRefl := A_qo_reflexive _ _ _ lteP in
  let lteTrns := A_qo_transitive _ _ _ lteP in     
   {| 
     A_eqv_congruence  := brel_minset_congruence S r refS symS trnS lteS lteCong lteRefl lteTrns
   ; A_eqv_reflexive   := brel_minset_reflexive S r  refS symS lteS
   ; A_eqv_transitive  := brel_minset_transitive S r refS symS trnS lteS
   ; A_eqv_symmetric   := brel_minset_symmetric S r lteS
   |}.



Definition eqv_proofs_brel_minset_from_po 
  (S : Type)
  (r : brel S)
  (lteS : brel S)
  (eqv : eqv_proofs S r)
  (lteP : po_proofs S r lteS) : eqv_proofs (finite_set S) (brel_minset r lteS) := 
  let refS := A_eqv_reflexive S r eqv in
  let symS := A_eqv_symmetric S r eqv in
  let trnS := A_eqv_transitive S r eqv in
  let lteCong := A_po_congruence _ _ _ lteP in
  let lteRefl := A_po_reflexive _ _ _ lteP in
  let lteTrns := A_po_transitive _ _ _ lteP in     
   {| 
     A_eqv_congruence  := brel_minset_congruence S r refS symS trnS lteS lteCong lteRefl lteTrns
   ; A_eqv_reflexive   := brel_minset_reflexive S r  refS symS lteS
   ; A_eqv_transitive  := brel_minset_transitive S r refS symS trnS lteS
   ; A_eqv_symmetric   := brel_minset_symmetric S r lteS
   |}.


Definition A_eqv_minset_from_po : ∀ (S : Type),  A_po S -> A_eqv (finite_set S) 
  := λ S poS,
  let eqvS  := A_po_eqv S poS in 
  let rS    := A_eqv_eq S eqvS in
  let wS    := A_eqv_witness S eqvS in
  let fS    := A_eqv_new S eqvS in
  let nt    := A_eqv_not_trivial S eqvS in
  let eqP   := A_eqv_proofs S eqvS in
  let congS := A_eqv_congruence S rS eqP in 
  let refS  := A_eqv_reflexive S rS eqP in  
  let symS  := A_eqv_symmetric S rS eqP in
  let trnS  := A_eqv_transitive S rS eqP in
  let lteS  := A_po_lte S poS in
  let lteP  := A_po_proofs S poS in 
  let lte_congS := A_po_congruence S rS lteS lteP in 
  let lte_refS  := A_po_reflexive S rS lteS lteP in  
  let lte_trnS  := A_po_transitive S rS lteS lteP in  
   {| 
      A_eqv_eq            := brel_minset rS lteS 
    ; A_eqv_proofs        := eqv_proofs_brel_minset_from_po S rS lteS eqP lteP 
    ; A_eqv_witness       := nil 
    ; A_eqv_new           := brel_minset_new S rS wS 
    ; A_eqv_not_trivial   := brel_minset_not_trivial S rS wS refS symS trnS lteS 
    ; A_eqv_exactly_two_d := inr (brel_minset_not_exactly_two S rS wS fS nt refS symS trnS lteS)                              
    ; A_eqv_data          := λ l, DATA_list (List.map (A_eqv_data S eqvS) (uop_minset rS l))   
    ; A_eqv_rep           := λ l, List.map (A_eqv_rep S eqvS) (uop_minset rS l)
    ; A_eqv_finite_d      := brel_minset_finite_decidable S rS wS fS nt congS refS symS trnS lteS lte_congS lte_refS lte_trnS (A_eqv_finite_d S eqvS)
    ; A_eqv_ast           := Ast_eqv_minset (A_po_ast S poS)
   |}. 


(*
Definition A_eqv_minset_from_po_bounded : ∀ (S : Type),  A_po_bounded S -> A_eqv (finite_set S) 
  := λ S poS,
  let eqvS  := A_po_bd_eqv S poS in 
  let rS    := A_eqv_eq S eqvS in
  let wS    := A_eqv_witness S eqvS in
  let fS    := A_eqv_new S eqvS in
  let nt    := A_eqv_not_trivial S eqvS in
  let eqP   := A_eqv_proofs S eqvS in
  let congS := A_eqv_congruence S rS eqP in 
  let refS  := A_eqv_reflexive S rS eqP in  
  let symS  := A_eqv_symmetric S rS eqP in
  let trnS  := A_eqv_transitive S rS eqP in
  let lteS  := A_po_bd_lte S poS in
  let lteP  := A_po_bd_proofs S poS in 
  let lte_congS := A_po_congruence S rS lteS lteP in 
  let lte_refS  := A_po_reflexive S rS lteS lteP in  
  let lte_trnS  := A_po_transitive S rS lteS lteP in  
   {| 
      A_eqv_eq            := brel_minset rS lteS 
    ; A_eqv_proofs        := eqv_proofs_brel_minset_from_po S rS lteS eqP lteP 
    ; A_eqv_witness       := nil 
    ; A_eqv_new           := brel_minset_new S rS wS 
    ; A_eqv_not_trivial   := brel_minset_not_trivial S rS wS refS symS trnS lteS 
    ; A_eqv_exactly_two_d := inr (brel_minset_not_exactly_two S rS wS fS nt refS symS trnS lteS)                              
    ; A_eqv_data          := λ l, DATA_list (List.map (A_eqv_data S eqvS) (uop_minset rS l))   
    ; A_eqv_rep           := λ l, List.map (A_eqv_rep S eqvS) (uop_minset rS l)
    ; A_eqv_finite_d      := brel_minset_finite_decidable S rS wS fS nt congS refS symS trnS lteS lte_congS lte_refS lte_trnS (A_eqv_finite_d S eqvS)
    ; A_eqv_ast           := Ast_eqv_minset (A_po_bd_ast S poS)
   |}. 

*) 

Definition A_eqv_minset_from_qo : ∀ (S : Type),  A_qo S -> A_eqv (finite_set S) 
  := λ S poS,
  let eqvS  := A_qo_eqv S poS in 
  let rS    := A_eqv_eq S eqvS in
  let wS    := A_eqv_witness S eqvS in
  let fS    := A_eqv_new S eqvS in
  let nt    := A_eqv_not_trivial S eqvS in
  let eqP   := A_eqv_proofs S eqvS in
  let congS := A_eqv_congruence S rS eqP in 
  let refS  := A_eqv_reflexive S rS eqP in  
  let symS  := A_eqv_symmetric S rS eqP in
  let trnS  := A_eqv_transitive S rS eqP in
  let lteS  := A_qo_lte S poS in
  let lteP  := A_qo_proofs S poS in 
  let lte_congS := A_qo_congruence S rS lteS lteP in 
  let lte_refS  := A_qo_reflexive S rS lteS lteP in  
  let lte_trnS  := A_qo_transitive S rS lteS lteP in  
   {| 
      A_eqv_eq            := brel_minset rS lteS 
    ; A_eqv_proofs        := eqv_proofs_brel_minset_from_qo S rS lteS eqP lteP 
    ; A_eqv_witness       := nil 
    ; A_eqv_new           := brel_minset_new S rS wS 
    ; A_eqv_not_trivial   := brel_minset_not_trivial S rS wS refS symS trnS lteS 
    ; A_eqv_exactly_two_d := inr (brel_minset_not_exactly_two S rS wS fS nt refS symS trnS lteS)                              
    ; A_eqv_data          := λ l, DATA_list (List.map (A_eqv_data S eqvS) (uop_minset rS l))   
    ; A_eqv_rep           := λ l, List.map (A_eqv_rep S eqvS) (uop_minset rS l)
    ; A_eqv_finite_d      := brel_minset_finite_decidable S rS wS fS nt congS refS symS trnS lteS lte_congS lte_refS lte_trnS (A_eqv_finite_d S eqvS)
    ; A_eqv_ast           := Ast_eqv_minset (A_qo_ast S poS)
   |}. 


End ACAS.


Section AMCAS.

Definition A_eqv_minset_below_qo {S : Type} (E : @A_below_qo S) : A_eqv (finite_set S)  :=
    A_eqv_minset_from_qo _ (A_cast_up_qo E). 
  

Definition A_mcas_eqv_minset {S : Type}  (A : @A_qo_mcas S) : @A_mcas_eqv (finite_set S) :=
match A with
| A_MCAS_qo_Error sl => A_EQV_Error sl
| A_MCAS_qo B        => A_EQV_eqv (A_eqv_minset_below_qo B) 
end.

End AMCAS.


Section CAS.

Definition check_brel_minset_finite {S : Type} (lteS : brel S) (d : @check_is_finite S) : @check_is_finite (finite_set S)
  := match d with
     | Certify_Is_Finite fS  => Certify_Is_Finite (minset_enum S lteS fS) 
     | Certify_Is_Not_Finite => Certify_Is_Not_Finite 
     end.


Definition eqv_minset_from_qo : ∀ {S : Type},  @qo S -> @eqv (finite_set S)
:= λ {S} poS,
  let eqvS := qo_eqv poS in  
  let rS   := eqv_eq eqvS in
  let wS   := eqv_witness eqvS in
  let fS   := eqv_new eqvS in  
  let lteS := qo_lte poS in 
   {| 
      eqv_eq            := brel_minset rS lteS 
    ; eqv_certs := 
     {|
       eqv_congruence     := @Assert_Brel_Congruence (finite_set S)
     ; eqv_reflexive      := @Assert_Reflexive (finite_set S)
     ; eqv_transitive     := @Assert_Transitive (finite_set S)
     ; eqv_symmetric      := @Assert_Symmetric (finite_set S)
     |}  
    ; eqv_witness       := nil 
    ; eqv_new           := brel_minset_new S rS wS 
    ; eqv_exactly_two_d := Certify_Not_Exactly_Two (minset_negate S wS fS lteS) 
    ; eqv_data          := λ l, DATA_list (List.map (eqv_data eqvS) (uop_minset rS l))   
    ; eqv_rep           := λ l, List.map (eqv_rep eqvS) (uop_minset rS  l)
    ; eqv_finite_d      := check_brel_minset_finite lteS (eqv_finite_d eqvS)  
    ; eqv_ast           := Ast_eqv_minset (qo_ast poS)
   |}.



Definition eqv_minset_from_po : ∀ {S : Type},  @po S -> @eqv (finite_set S)
:= λ {S} poS,
  let eqvS := po_eqv poS in  
  let rS   := eqv_eq eqvS in
  let wS   := eqv_witness eqvS in
  let fS   := eqv_new eqvS in  
  let lteS := po_lte poS in 
   {| 
      eqv_eq            := brel_minset rS lteS 
    ; eqv_certs := 
     {|
       eqv_congruence     := @Assert_Brel_Congruence (finite_set S)
     ; eqv_reflexive      := @Assert_Reflexive (finite_set S)
     ; eqv_transitive     := @Assert_Transitive (finite_set S)
     ; eqv_symmetric      := @Assert_Symmetric (finite_set S)
     |}  
    ; eqv_witness       := nil 
    ; eqv_new           := brel_minset_new S rS wS 
    ; eqv_exactly_two_d := Certify_Not_Exactly_Two (minset_negate S wS fS lteS) 
    ; eqv_data          := λ l, DATA_list (List.map (eqv_data eqvS) (uop_minset rS l))   
    ; eqv_rep           := λ l, List.map (eqv_rep eqvS) (uop_minset rS  l)
    ; eqv_finite_d      := check_brel_minset_finite lteS (eqv_finite_d eqvS)  
    ; eqv_ast           := Ast_eqv_minset (po_ast poS)
   |}.

(*
Definition eqv_minset_from_po_bounded : ∀ {S : Type},  @po_bounded S -> @eqv (finite_set S)
:= λ {S} poS,
  let eqvS := po_bd_eqv poS in  
  let rS   := eqv_eq eqvS in
  let wS   := eqv_witness eqvS in
  let fS   := eqv_new eqvS in  
  let lteS := po_bd_lte poS in 
   {| 
      eqv_eq            := brel_minset rS lteS 
    ; eqv_certs := 
     {|
       eqv_congruence     := @Assert_Brel_Congruence (finite_set S)
     ; eqv_reflexive      := @Assert_Reflexive (finite_set S)
     ; eqv_transitive     := @Assert_Transitive (finite_set S)
     ; eqv_symmetric      := @Assert_Symmetric (finite_set S)
     |}  
    ; eqv_witness       := nil 
    ; eqv_new           := brel_minset_new S rS wS 
    ; eqv_exactly_two_d := Certify_Not_Exactly_Two (minset_negate S wS fS lteS) 
    ; eqv_data          := λ l, DATA_list (List.map (eqv_data eqvS) (uop_minset rS l))   
    ; eqv_rep           := λ l, List.map (eqv_rep eqvS) (uop_minset rS  l)
    ; eqv_finite_d      := check_brel_minset_finite lteS (eqv_finite_d eqvS)  
    ; eqv_ast           := Ast_eqv_minset (po_bd_ast poS)
   |}.

*) 

  
End CAS.


Section MCAS.

Definition eqv_minset_below_qo {S : Type} (E : @below_qo S) : @eqv (finite_set S)  :=
    eqv_minset_from_qo (cast_up_qo E). 
  

Definition mcas_eqv_minset {S : Type}  (A : @qo_mcas S) : @mcas_eqv (finite_set S) :=
match A with
| MCAS_qo_Error sl => EQV_Error sl
| MCAS_qo B        => EQV_eqv (eqv_minset_below_qo B) 
end.

End MCAS.

Section Verify.

Theorem correct_eqv_minset_from_qo : ∀ (S : Type) (P : A_qo S),  
    eqv_minset_from_qo (A2C_qo P) = A2C_eqv (finite_set S) (A_eqv_minset_from_qo S P).
Proof. intros S P. 
       unfold eqv_minset_from_qo, A_eqv_minset_from_qo, A2C_eqv; simpl. 
       destruct P; simpl.
       destruct A_qo_proofs; destruct A_qo_eqv; simpl.
       destruct A_eqv_finite_d as [ [fS FS] | NFS ]; simpl; auto. 
Qed.        
  
Theorem correct_eqv_minset_from_po : ∀ (S : Type) (P : A_po S),  
    eqv_minset_from_po (A2C_po P) = A2C_eqv (finite_set S) (A_eqv_minset_from_po S P).
Proof. intros S P. 
       unfold eqv_minset_from_po, A_eqv_minset_from_po, A2C_eqv; simpl. 
       destruct P; simpl.
       destruct A_po_proofs; destruct A_po_eqv; simpl.
       destruct A_eqv_finite_d as [ [fS FS] | NFS ]; simpl; auto. 
Qed.        

(*
Theorem correct_eqv_minset_from_po_bounded : ∀ (S : Type) (P : A_po_bounded S),  
    eqv_minset_from_po_bounded (A2C_po_bounded P)
    =
    A2C_eqv (finite_set S) (A_eqv_minset_from_po_bounded S P).
Proof. intros S P. 
       unfold eqv_minset_from_po_bounded, A_eqv_minset_from_po_bounded, A2C_eqv; simpl. 
       destruct P; simpl.
       destruct A_po_bd_proofs; destruct A_po_bd_eqv; simpl.
       destruct A_eqv_finite_d as [ [fS FS] | NFS ]; simpl; auto. 
Qed.        
*) 

Theorem correct_eqv_minset_below_qo (S : Type) (A : @A_below_qo S) : 
  eqv_minset_below_qo (A2C_below_qo A)
  =
    A2C_eqv _ (A_eqv_minset_below_qo A).
Proof. destruct A; unfold eqv_minset_below_qo, A_eqv_minset_below_qo; simpl.
       - apply correct_eqv_minset_from_qo. 
       - (*
           eqv_minset_from_qo (qo_from_po (cast_up_po (A2C_below_po a))) 
           = {cast_up_po_A2C_commute}
           eqv_minset_from_qo (qo_from_po (A2C_po (A_cast_up_po a)))
           = {correct_qo_from_po}
           eqv_minset_from_qo (A2C_qo (A_qo_from_po (A_cast_up_po a)))
           = {correct_eqv_minset_from_qo }
           A2C_eqv _ (A_eqv_minset_from_qo S (A_qo_from_po (A_cast_up_po a)))
          *)
         rewrite cast_up_po_A2C_commute.
         rewrite correct_qo_from_po.
         apply correct_eqv_minset_from_qo. 
       - (* similar *)
         rewrite cast_up_fo_A2C_commute.
         rewrite correct_qo_from_fo.
         apply correct_eqv_minset_from_qo.
       - (* similar *)
         rewrite cast_up_qo_with_bottom_A2C_commute.
         rewrite correct_qo_from_qo_with_bottom.
         apply correct_eqv_minset_from_qo.
Qed.

Theorem correct_mcas_eqv_minset (S : Type)  (A : @A_qo_mcas S) :
  mcas_eqv_minset (A2C_qo_mcas A)
  =
  A2C_mcas_eqv _ (A_mcas_eqv_minset A). 
Proof. destruct A; unfold mcas_eqv_minset, A_mcas_eqv_minset; simpl.
       - reflexivity.
       - rewrite correct_eqv_minset_below_qo.
         reflexivity. 
Qed.

End Verify.   
 
