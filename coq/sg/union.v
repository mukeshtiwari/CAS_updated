Require Import Coq.Bool.Bool.

Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.

Require Import CAS.coq.theory.set. 

Require Import CAS.coq.uop.properties.

Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.eqv.set.

Require Import CAS.coq.eqv.sum. 
Require Import CAS.coq.eqv.add_constant.

Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures.  
Require Import CAS.coq.sg.and.
Require Import CAS.coq.sg.or.
Require Import CAS.coq.sg.add_ann. 
Require Import CAS.coq.sg.cast_up.
Require Import CAS.coq.sg.classify. 

Require Import CAS.coq.po.subset.
Require Import CAS.coq.po.theory. 
Require Import CAS.coq.po.dual.
Require Import CAS.coq.po.from_sg. 

Require Import CAS.coq.os.properties.
Require Import CAS.coq.os.structures.
Require Import CAS.coq.os.theory. 

Section Computation.

Definition bop_union {S : Type} (eq : brel S) : binary_op (finite_set S) 
  := λ X Y,  uop_duplicate_elim eq (bop_concat X Y).

Definition bop_union_with_ann {S : Type} (c : cas_constant) (eq : brel S) : binary_op (with_constant (finite_set S))
  := bop_add_ann (bop_union eq) c. 

End Computation.   


Section Theory.


Section Concat.
  Variable S: Type.
  Variable r : brel S.
  Variable refS : brel_reflexive S r.
  Variable symS : brel_symmetric S r.
  Variable tranS : brel_transitive S r.
Lemma bop_concat_subset_congruence : bop_congruence (finite_set S) (brel_subset r) (@bop_concat S).
Proof. unfold bop_congruence, bop_concat. 
       intros s1 s2 t1 t2 J K. 
       assert (Q := brel_subset_elim S r symS tranS _ _ J). 
       assert (H := brel_subset_elim S r symS tranS _ _ K).
       apply (brel_subset_intro S r refS). intros a L. 
       apply (in_set_concat_intro S r t1 t2). apply (in_set_concat_elim S r symS) in L. destruct L as [L | L].
          left. rewrite (Q a L). reflexivity. 
          right. rewrite (H a L). reflexivity. 
Defined. 


Lemma bop_concat_set_congruence : bop_congruence (finite_set S) (brel_set r) (@bop_concat S).
Proof. unfold bop_congruence, bop_concat. unfold brel_set. unfold brel_and_sym. 
       intros s1 s2 t1 t2 H J.  
       apply bop_and_elim in H. apply bop_and_elim in J. 
       destruct H as [H1 H2]. destruct J as [J1 J2]. apply bop_and_intro. 
          apply (bop_concat_subset_congruence s1 s2 t1 t2 H1 J1).
          apply (bop_concat_subset_congruence t1 t2 s1 s2 H2 J2).
Defined. 
  

(* what is this ? 

   (r s t) + (r s u) -> r s (b t u) 

*) 

Lemma brel_subset_concat_right_intro  : ∀ (s t u : finite_set S), 
     (brel_subset r s t = true) + (brel_subset r s u = true) -> 
     brel_subset r s (t ++ u) = true. 
Proof. intros s t u H.             
       apply (brel_subset_intro S r); auto.
       intros a J. destruct H as [H | H].
       apply in_set_concat_intro.
       assert (Q := brel_subset_elim S r symS tranS s t H).
       left. apply Q; auto.
       assert (Q := brel_subset_elim S r symS tranS s u H).        
       apply in_set_concat_intro.
       right. apply Q; auto.
Defined. 



(* simplify? see below *) 
Lemma subset_cat_left : 
    ∀ (s v u : finite_set S), 
        brel_subset r u s = true -> 
        brel_subset r v s = true -> 
        brel_subset r (u ++ v) s = true. 
Proof. induction s; induction v; induction u; simpl; intros H Q. 
       reflexivity. assumption. assumption. assumption. assumption. 
       apply bop_and_elim in H. destruct H as [H1 H2].
          apply bop_or_elim in H1. destruct H1 as [H1 | H1].
             rewrite H1. simpl. apply IHu. assumption. simpl. reflexivity. 
             rewrite List.app_nil_r. rewrite H1, H2. rewrite orb_comm. simpl. reflexivity. 
       apply bop_and_elim in Q. destruct Q as [Q1 Q2].      
          apply bop_or_elim in Q1. destruct Q1 as [Q1 | Q1]. 
             rewrite Q1. simpl. assumption. 
             rewrite Q1, Q2. rewrite orb_comm. simpl. reflexivity. 
       apply bop_and_elim in H. apply bop_and_elim in Q. 
          destruct H as [H1 H2]. destruct Q as [Q1 Q2].
          apply bop_or_elim in H1.  apply bop_or_elim in Q1. 
          destruct H1 as [H1 | H1]; destruct Q1 as [Q1 | Q1]. 
             rewrite H1. simpl. apply IHu. assumption. 
                unfold brel_subset. fold (@brel_subset S). unfold in_set. fold (@in_set S). 
                rewrite Q1, Q2. simpl. reflexivity. 
             rewrite H1. simpl. apply IHu. assumption. 
                unfold brel_subset. fold (@brel_subset S). unfold in_set. fold (@in_set S). 
                rewrite Q1, Q2. rewrite orb_comm. simpl. reflexivity. 
             rewrite H1. rewrite orb_comm. simpl.  apply IHu. assumption. 
                unfold brel_subset. fold (@brel_subset S). unfold in_set. fold (@in_set S). 
                rewrite Q1, Q2. simpl. reflexivity. 
             rewrite H1. rewrite orb_comm. simpl.  apply IHu. assumption. 
                unfold brel_subset. fold (@brel_subset S). unfold in_set. fold (@in_set S). 
                rewrite Q1, Q2. rewrite orb_comm. simpl. reflexivity. 
Defined. 



(* simplify? *) 
Lemma subset_cat_right : 
  ∀ (s v u : finite_set S),
        brel_subset r s u = true -> 
        brel_subset r s v = true -> 
        brel_subset r s (u ++ v) = true. 
Proof. induction s; induction v; induction u; simpl; intros H Q. 
       reflexivity. assumption. assumption. assumption. assumption. 
       apply bop_and_elim in H. destruct H as [H1 H2].
          apply bop_or_elim in H1. destruct H1 as [H1 | H1].
             rewrite H1. simpl. rewrite List.app_nil_r. assumption. 
             rewrite List.app_nil_r. rewrite H1, H2. rewrite orb_comm. simpl. reflexivity. 
       apply bop_and_elim in Q. destruct Q as [Q1 Q2].      
          apply bop_or_elim in Q1. destruct Q1 as [Q1 | Q1]. 
             rewrite Q1. simpl. assumption. 
             rewrite Q1, Q2. rewrite orb_comm. simpl. reflexivity. 
       apply bop_and_elim in H. apply bop_and_elim in Q. 
          destruct H as [H1 H2]. destruct Q as [Q1 Q2].
          apply bop_or_elim in H1.  apply bop_or_elim in Q1. 
          destruct H1 as [H1 | H1]; destruct Q1 as [Q1 | Q1]. 
             rewrite H1. simpl. apply (IHs (a0 :: v) (a1 :: u) H2 Q2). 
             rewrite H1. simpl. apply (IHs (a0 :: v) (a1 :: u) H2 Q2). 
             rewrite List.app_comm_cons. rewrite (IHs (a0 :: v) (a1 :: u) H2 Q2). 
                rewrite (in_set_concat_intro S r u (a0 :: v) a (inl _ H1)). 
                rewrite orb_comm. simpl. reflexivity. 
             rewrite (in_set_concat_intro S r u (a0 :: v) a (inl _ H1)). 
                rewrite orb_comm. simpl. apply (IHs (a0 :: v) (a1 :: u) H2 Q2). 
Defined. 


Lemma bop_concat_set_commutative : bop_commutative (finite_set S) (brel_set r) (@bop_concat S).
Proof.  unfold bop_commutative, bop_concat.
        intros s t. unfold brel_set. unfold brel_and_sym. 
        apply bop_and_intro.
        apply subset_cat_left.        
        apply brel_subset_concat_right_intro. 
             right. apply brel_subset_reflexive; auto. 
             apply brel_subset_concat_right_intro. 
             left. apply brel_subset_reflexive; auto. 
          apply subset_cat_left.  apply brel_subset_concat_right_intro.
             right. apply brel_subset_reflexive; auto. 
             apply brel_subset_concat_right_intro. 
             left. apply brel_subset_reflexive; auto. 
Defined.

Lemma bop_concat_set_idempotent : bop_idempotent (finite_set S) (brel_set r) (@bop_concat S).
Proof.  unfold bop_idempotent, bop_concat.
        intro s. unfold brel_set. unfold brel_and_sym. 
        apply bop_and_intro. 
          apply subset_cat_left.  
                apply brel_subset_reflexive; auto. 
                apply brel_subset_reflexive; auto. 
          apply subset_cat_right.  
                apply brel_subset_reflexive; auto. 
                apply brel_subset_reflexive; auto. 
Defined. 


End Concat. 

Section DuplicateElim.
  Variable S: Type.
  Variable r : brel S.
  Variable refS : brel_reflexive S r.
  Variable symS : brel_symmetric S r.
  Variable tranS : brel_transitive S r.

(* move duplicate elim lemmas ?*)

Lemma  uop_duplicate_elim_lemma_1 : 
   ∀ (a b: S),  r b a = true →     
       ∀ (X : finite_set S), in_set r (uop_duplicate_elim r (a :: X)) b = true.
Proof. intros a b E. induction X. 
          compute. rewrite E. reflexivity. 
          simpl. simpl in IHX. 
          case_eq(r a a0); case_eq(in_set r X a); case_eq(in_set r X a0); intros J K M; simpl.
          rewrite K in IHX. assumption. 
          rewrite (tranS _ _ _ E M). simpl. reflexivity. 
          apply symS in M.

          assert (A := in_set_right_congruence _ _ symS tranS _ _ _ M J). 
          rewrite A in K. discriminate. 
          rewrite (tranS _ _ _ E M). simpl. reflexivity.           
          rewrite K in IHX. assumption. 
          case_eq(r b a0); intro N. simpl. reflexivity. simpl. rewrite K in IHX. assumption. 
          rewrite E. simpl. reflexivity.           rewrite E. simpl. reflexivity. 
Defined.

Lemma uop_duplicate_elim_lemma_2 : 
   ∀ (a : S), 
     ∀ (X : finite_set S), 
       in_set r X a = false → 
           (uop_duplicate_elim r (a :: X)) = a :: (uop_duplicate_elim r X).
Proof. intros a X H. simpl. rewrite H. reflexivity. Defined. 


Lemma in_set_uop_duplicate_elim_intro : 
       ∀ (X : finite_set S) (a : S), 
         in_set r X a = true →
            in_set r (uop_duplicate_elim r X) a = true. 
Proof. induction X. 
          intros a I. compute in I. discriminate. 
          intros a0 I. 
          case_eq(in_set r X a); intro H. 
             unfold uop_duplicate_elim. rewrite H. apply IHX. 
             apply in_set_cons_elim in I. destruct I as [I | I].               
                apply (in_set_right_congruence _ _ symS tranS _ _ _ I H); auto. assumption. assumption. 

            apply in_set_cons_elim in I. destruct I as [I | I].
               apply uop_duplicate_elim_lemma_1; auto.  
               rewrite (uop_duplicate_elim_lemma_2 a X H). 
               unfold in_set. fold (@in_set S).
               case_eq(r a0 a); intro J. 
                  simpl. reflexivity.
                  simpl. apply IHX. assumption. assumption. 
Defined. 

Lemma in_set_uop_duplicate_elim_elim : 
       ∀ (X : finite_set S) (a : S), 
         in_set r (uop_duplicate_elim r X) a = true →
            in_set r X a = true.
Proof. induction X. 
          intros a I. compute in I. discriminate. 
          intros a0 I. unfold in_set. fold (@in_set S). 
          case_eq(r a0 a); intro H; simpl. 
             reflexivity.
             case_eq(in_set r X a); intro J. 
                 unfold uop_duplicate_elim in I. rewrite J in I. apply IHX. assumption. 
               rewrite (uop_duplicate_elim_lemma_2 a X J) in I. 
                 unfold in_set in I. fold (@in_set S) in I. rewrite H in I. simpl in I. 
                 assert (QED := IHX a0 I). assumption. 
Defined. 


Lemma in_set_dup_elim_intro : 
     ∀ (X : finite_set S) (t : S), in_set r X t = true → in_set r (uop_duplicate_elim r X) t = true. 
Proof. induction X; intros t H. 
       simpl in H. discriminate. 
       simpl. case_eq(in_set r X a); intro Q.
          unfold in_set in H.  fold (@in_set S) in H.  
          apply bop_or_elim in H. destruct H as [H | H].
          apply IHX. apply symS in H. apply (in_set_right_congruence S r symS tranS a t X H Q). 
          apply IHX. assumption. 
       unfold in_set. fold (@in_set S). 
          unfold in_set in H.  fold (@in_set S) in H.  
          apply bop_or_elim in H. destruct H as [H | H].
             rewrite H. simpl. reflexivity. 
             rewrite (IHX t H). rewrite orb_comm. simpl. reflexivity. 
Defined. 


Lemma uop_duplicate_elim_congruence_v1 : 
      uop_congruence_positive (finite_set S) (brel_subset r) (uop_duplicate_elim r).  
Proof. unfold uop_congruence_positive. 
       induction s; intros t H. 
          simpl. reflexivity. 
          unfold uop_duplicate_elim at 1. fold (@uop_duplicate_elim S r). 
          case_eq(in_set r s a); intro Q. 
             apply IHs. unfold brel_subset in H. fold (@brel_subset S) in H. 
                apply bop_and_elim in H.  destruct H as [H1 H2].  assumption. 
             unfold brel_subset in H. fold (@brel_subset S) in H. 
             unfold brel_subset. fold (@brel_subset S). 
             apply bop_and_elim in H.  destruct H as [H1 H2].
             apply bop_and_intro. 
                apply in_set_dup_elim_intro; auto. 
                apply IHs; auto. 
Defined. 

Lemma uop_duplicate_elim_congruence_v2 :
      uop_congruence_positive (finite_set S) (brel_set r) (uop_duplicate_elim r).  
Proof. unfold brel_set. unfold brel_and_sym. unfold uop_congruence_positive. intros s t H. 
       apply bop_and_elim in H. destruct H as [H1 H2]. 
       apply bop_and_intro. 
         apply uop_duplicate_elim_congruence_v1; auto. 
         apply uop_duplicate_elim_congruence_v1; auto. 
Defined.


Lemma uop_duplicate_elim_preserves_left_v1 : 
      uop_preserves_left_positive (finite_set S) (brel_subset r) (uop_duplicate_elim r).  
Proof. unfold uop_preserves_left_positive. 
       induction s; simpl; intros t H. 
          reflexivity. 
          apply bop_and_elim in H. destruct H as [H1 H2].
          case_eq(in_set r s a); intro Q. 
             apply IHs. assumption. 
             unfold brel_subset. fold (@brel_subset S). rewrite H1, (IHs t H2). simpl. reflexivity. 
Defined. 


Lemma uop_duplicate_elim_preserves_right_v1 : 
      uop_preserves_right_positive (finite_set S) (brel_subset r) (uop_duplicate_elim r).  
Proof. unfold uop_preserves_right_positive. 
       induction s; simpl; intros t H; auto. 
          apply bop_and_elim in H. destruct H as [H1 H2].
          rewrite (IHs t H2).  rewrite (in_set_dup_elim_intro t a H1); auto. 
Defined. 


Lemma uop_duplicate_elim_preserves_right_v2 : 
      uop_preserves_right_positive (finite_set S) (brel_set r) (uop_duplicate_elim r).  
Proof. intros w u. unfold brel_set. unfold brel_and_sym. intro H. 
       apply bop_and_elim in H. destruct H as [H1 H2]. 
       apply bop_and_intro. 
         apply uop_duplicate_elim_preserves_right_v1; auto. 
         apply uop_duplicate_elim_preserves_left_v1; auto. 
Defined. 

Lemma duplicate_elim_concat_associative : 
         uop_bop_associative (finite_set S) (brel_set r) (uop_duplicate_elim r) (@bop_concat S). 
Proof. unfold uop_bop_associative. intros s t v. 
       assert (H : brel_set r (bop_concat (bop_concat s t) v) 
                              (bop_concat (uop_duplicate_elim r (bop_concat s t)) v) = true).
          apply (bop_concat_set_congruence _ _ refS symS tranS
                 (bop_concat s t) v (uop_duplicate_elim r (bop_concat s t)) v). 
          apply uop_duplicate_elim_preserves_right_v2. 
          apply brel_set_reflexive; auto. 
          apply brel_set_reflexive; auto. 
       assert (K : brel_set r (bop_concat s (bop_concat t v)) 
                              (bop_concat s (uop_duplicate_elim r (bop_concat t v))) = true).
          apply (bop_concat_set_congruence _ _ refS symS tranS
                 s (bop_concat t v) s (uop_duplicate_elim r (bop_concat t v))). 
          apply brel_set_reflexive; auto. 
          apply uop_duplicate_elim_preserves_right_v2. 
          apply brel_set_reflexive; auto. 
          unfold bop_concat in *. rewrite List.app_assoc in K.           
          apply brel_set_symmetric in H. 
          apply (brel_set_transitive S r refS symS tranS _ _ _ H K). 
Defined. 


Lemma uop_duplicate_elim_preserves_left_v2 : 
      uop_preserves_left_positive (finite_set S) (@brel_set S r) (@uop_duplicate_elim S r).  
Proof. intros w u. unfold brel_set. unfold brel_and_sym. intro H. 
       apply bop_and_elim in H. destruct H as [H1 H2]. 
       apply bop_and_intro. 
         apply uop_duplicate_elim_preserves_left_v1; auto. 
         apply uop_duplicate_elim_preserves_right_v1; auto. 
Defined. 

End DuplicateElim. 



Section ThenUnary.
  Variable S: Type.
  Variable r : brel S.
  Variable refS : brel_reflexive S r.
  Variable symS : brel_symmetric S r.
  Variable tranS : brel_transitive S r.

(* move then_unary lemmas ? *)

Lemma bop_then_unary_congruence : 
   ∀ (u : unary_op S) (b : binary_op S), 
           uop_congruence_positive S r u -> 
           bop_congruence S r b -> 
           bop_congruence S r (bop_then_unary u b).
Proof. intros u b congU congB. unfold bop_congruence, bop_then_unary.
       intros s1 s2 t1 t2 H Q. apply congU. apply congB.  assumption. assumption. 
Defined. 

Lemma bop_then_unary_associative : 
   ∀ (u : unary_op S) (b : binary_op S), 
           uop_congruence_positive S r u -> 
           uop_bop_associative S r u b -> 
           bop_associative S r (@bop_then_unary S u b).
Proof. intros u b congS assocS. unfold bop_associative, bop_then_unary.
       intros s t v. apply congS.
       apply assocS. 
Defined. 

(*  How to capture reductions? 

(a)  u (u (s * t) * v) =  u (s * (u (t * v)))

dist? 

  a x (b + c) 
= r(a x r(b + c))
= r(a x (b + c))
= r((a x b) + (a x c))
= r(r(a x b) + r(a x c))
= (a x b) + (a x c) 


(A) u(s * t) = u((u(s) * t) 
(B) u(s * t) = u(s * u(t)) 

Prove (a) : 

  u (u (s * t) * v)
= u ((s * t) * v)
= u (s * (t * v)) 
= u (s * u(t * v)) 

*) 

Lemma bop_then_unary_idempotent : 
   ∀ (u : unary_op S) (b : binary_op S), 
         uop_preserves_left_positive S r u -> 
         bop_idempotent S r b -> 
           bop_idempotent S r (@bop_then_unary S u b).
Proof. 
       intros u b presS idemS. 
       unfold bop_then_unary. unfold bop_idempotent. 
       intro s. apply (presS (b s s) s). apply idemS. 
Defined. 


Lemma bop_then_unary_commutative : 
   ∀ (u : unary_op S) (b : binary_op S), 
         uop_congruence_positive S r u -> 
         bop_commutative S r b -> 
           bop_commutative S r (@bop_then_unary S u b).
Proof. intros u b congS commS. 
       intros s t. unfold bop_then_unary. apply congS. apply commS. 
Defined. 

End ThenUnary. 

Section Union. 
  Variable S: Type.
  Variable c : cas_constant.
  Variable r : brel S.
  Variable refS : brel_reflexive S r.
  Variable symS : brel_symmetric S r.
  Variable tranS : brel_transitive S r.

Notation "a [=] b"  := (r a b = true)          (at level 15).
Notation "a [<>] b" := (r a b = false)         (at level 15).

Notation "a [in] b"  := (in_set r b a = true)   (at level 15).
Notation "a [!in] b" := (in_set r b a = false)  (at level 15).

Notation "a [U] b"   := (bop_union r a b)         (at level 15).

Notation "a [=S] b"   := (brel_set r a b = true)         (at level 15).
Notation "a [<>S] b"  := (brel_set r a b = false)         (at level 15).
  

Lemma in_set_bop_union_intro (X Y : finite_set S) (a : S) : 
       (a [in] X) + (a [in] Y) → a [in] (X [U] Y). 
Proof. intro H. unfold bop_union. unfold bop_then_unary. unfold bop_concat. 
       apply in_set_uop_duplicate_elim_intro; auto.
       apply in_set_concat_intro; auto. 
Defined. 

Lemma in_set_bop_union_elim (X Y : finite_set S) (a : S): 
       a [in] (X [U] Y)  → (a [in] X) + (a [in] Y). 
Proof. intro H. unfold bop_union in H. unfold bop_then_unary in H. unfold bop_concat in H. 
       apply in_set_uop_duplicate_elim_elim in H. 
       apply in_set_concat_elim in H; auto.
Defined. 

  
Lemma bop_union_congruence : bop_congruence (finite_set S) (brel_set r) (bop_union r).
Proof. unfold bop_union.
       apply bop_then_unary_congruence. 
       apply uop_duplicate_elim_congruence_v2; auto. 
       apply bop_concat_set_congruence; auto. 
Defined. 


Lemma bop_union_associative : bop_associative (finite_set S) (brel_set r) (bop_union r).
Proof. unfold bop_union. 
       apply bop_then_unary_associative. 
       apply uop_duplicate_elim_congruence_v2; auto. 
       apply duplicate_elim_concat_associative; auto. 
Defined.

Lemma bop_union_idempotent : bop_idempotent (finite_set S) (brel_set r) (bop_union r).
Proof. unfold bop_union.
       apply bop_then_unary_idempotent.
       apply uop_duplicate_elim_preserves_left_v2; auto. 
       apply bop_concat_set_idempotent; auto. 
Defined.

Lemma bop_union_commutative : bop_commutative(finite_set S) (brel_set r) (bop_union r).
Proof. unfold bop_union.
       apply bop_then_unary_commutative. 
       apply uop_duplicate_elim_congruence_v2; auto.  
       apply bop_concat_set_commutative; auto. 
Defined.


Lemma bop_union_not_selective : 
   ∀ (s : S) (f : S -> S), brel_not_trivial S r f -> bop_not_selective (finite_set S) (brel_set r) (bop_union r).
Proof. intros s f Pf.
       unfold bop_union, bop_not_selective. 
       exists ((s ::nil), ((f s) ::nil)).  
       unfold bop_concat, bop_then_unary.
       rewrite <- List.app_comm_cons.
       rewrite List.app_nil_l. 
       unfold uop_duplicate_elim.
       unfold in_set. 
       destruct (Pf s) as [L R].
       rewrite L; simpl. 
       unfold brel_set.
       unfold brel_and_sym.
       unfold brel_subset. 
       unfold in_set.
       rewrite (symS s), L; simpl.
       rewrite orb_comm. simpl. 
       case_eq(r (f s) s); intro Q. 
          apply symS in Q.
          rewrite L in Q. discriminate.
          auto. 
          apply refS. 
Defined.

(**** some useful lemmas ************) 
Lemma bop_union_with_nil_left : ∀ (X : finite_set S), (nil [U] X) [=S] X. 
Proof. intro X. 
       apply brel_set_intro. split. 
       apply brel_subset_intro; auto. 
       intros a H. apply in_set_bop_union_elim in H; auto. 
       destruct H as [H | H]. 
          unfold in_set in H. discriminate. 
          assumption. 
       apply brel_subset_intro; auto. 
       intros a H. apply in_set_bop_union_intro; auto. 
Qed. 


Lemma bop_union_with_nil_right : ∀ (X : finite_set S), (X [U] nil) [=S] X. 
Proof. intro X. 
       assert (A := bop_union_with_nil_left X).
       assert (B := bop_union_commutative X nil).
       assert (C := brel_set_transitive S r refS symS tranS _ _ _ B A).
       exact C. 
Qed. 

Lemma bop_union_cons_shift_left (X : finite_set S) (s : S) : ((s :: nil) [U] X)  [=S] (s :: X).
Proof. apply brel_set_intro_prop; auto. split. 
          intros t A. apply in_set_bop_union_elim in A; auto.
          apply in_set_cons_intro; auto.
          destruct A as [A | A].
             apply in_set_singleton_elim in A; auto. 
             right; auto.           
          intros t A. apply in_set_bop_union_intro; auto.
          apply in_set_cons_elim in A; auto.
          destruct A as [A | A].
             left. apply in_set_singleton_intro; auto. 
             right; auto.           
Qed.           

Lemma bop_union_cons_shift_right (X : finite_set S) (s : S) : (X [U] (s :: nil) )  [=S] (s :: X).
Proof. apply brel_set_intro_prop; auto. split. 
          intros t A. apply in_set_bop_union_elim in A; auto.
          apply in_set_cons_intro; auto.
          destruct A as [A | A].
             right; auto.           
             apply in_set_singleton_elim in A; auto. 
          intros t A. apply in_set_bop_union_intro; auto.
          apply in_set_cons_elim in A; auto.
          destruct A as [A | A].
             right. apply in_set_singleton_intro; auto. 
             left; auto. 
Qed.           

Lemma bop_union_shift_element (X Y : finite_set S) (s : S) :
  ((s :: Y) [U] X) [=S] (Y [U] (s :: X)). 
Proof. apply brel_set_intro_prop; auto; split; intros a A. 
       + apply in_set_bop_union_elim in A.
         apply in_set_bop_union_intro.
         destruct A as [A | A].
         ++ apply in_set_cons_elim in A; auto. 
            destruct A as [A | A]; auto. 
            +++ right. apply in_set_cons_intro; auto. 
         ++ right. apply in_set_cons_intro; auto.
       + apply in_set_bop_union_elim in A.
         apply in_set_bop_union_intro.
         destruct A as [A | A].
         ++ left. apply in_set_cons_intro; auto.
         ++ apply in_set_cons_elim in A; auto. 
            destruct A as [A | A]; auto. 
            +++ left. apply in_set_cons_intro; auto. 
Qed. 

Lemma bop_union_push_element (X Y : finite_set S) (s : S) :
  (s :: (Y [U] X)) [=S] ((s :: Y) [U] X). 
Proof. apply brel_set_intro_prop; auto; split; intros a A. 
       + apply in_set_cons_elim in A; auto. 
         apply in_set_bop_union_intro.
         destruct A as [A | A].
         ++ left. apply in_set_cons_intro; auto.         
         ++ apply in_set_bop_union_elim in A; auto. 
            destruct A as [A | A]; auto. 
            +++ left. apply in_set_cons_intro; auto. 
       + apply in_set_bop_union_elim in A.
         apply in_set_cons_intro; auto. 
         destruct A as [A | A].
         ++ apply in_set_cons_elim in A; auto. 
            destruct A as [A | A]; auto. 
            +++ right. apply in_set_bop_union_intro; auto.
         ++ right. apply in_set_bop_union_intro; auto.
Qed. 


Lemma bop_union_two_singletons (s t : S) :
  (s :: nil) [U] (t :: nil) [=S] (s :: t :: nil). 
Proof. apply brel_set_intro; auto. split.
       - apply brel_subset_intro; auto. 
         intros u D. 
         apply in_set_bop_union_elim in D; auto. 
         apply in_set_cons_intro; auto.                 
         destruct D as [D | D]. 
         + left. apply in_set_cons_elim in D; auto.
           destruct D as [D | D]; auto. 
           * compute in D. discriminate D.
         + right; auto.                    
       - apply brel_subset_intro; auto. 
         intros u D. 
         apply in_set_cons_elim in D; auto. 
         apply in_set_bop_union_intro; auto.                 
         destruct D as [D | D]. 
         + left. apply in_set_cons_intro; auto.
         + right; auto. 
Qed.

(****************** id and ann ************************) 

Lemma bop_union_nil_is_id : bop_is_id (finite_set S) (brel_set r) (bop_union r) nil.
Proof. intro s. 
       assert (fact1 : brel_set r (bop_union r nil s) s = true). 
          apply bop_union_with_nil_left; auto. 
       assert (fact2 : brel_set r (bop_union r s nil) (bop_union r nil s) = true). 
          apply bop_union_commutative; auto. 
       assert (fact3 : brel_set r (bop_union r s nil) s = true). 
          apply (brel_set_transitive S r refS symS tranS _ _ _ fact2 fact1). 
       rewrite fact1, fact3; auto. 
Defined. 
  
Lemma bop_union_exists_id : bop_exists_id (finite_set S) (brel_set r) (bop_union r).
Proof. exists nil. apply bop_union_nil_is_id; auto. Defined. 


Lemma bop_union_with_ann_exists_id : bop_exists_id (with_constant (finite_set S))
                                                   (brel_sum brel_constant (brel_set r))
                                                   (bop_union_with_ann c r).
Proof. apply bop_add_ann_exists_id. apply bop_union_exists_id. Defined. 

Lemma bop_union_with_ann_exists_ann : bop_exists_ann (with_constant (finite_set S))
                                                     (brel_sum brel_constant (brel_set r))
                                                     (bop_union_with_ann c r).
Proof. apply bop_add_ann_exists_ann. Defined. 

Lemma bop_union_enum_is_ann (enum : carrier_is_finite S r) : 
  bop_is_ann (finite_set S) (brel_set r) (bop_union r) ((projT1 enum) tt).
Proof. destruct enum as [f Pf]. simpl.
       unfold bop_is_id. intro X. split.
       apply brel_set_intro_prop; auto.
       split.
       intros s H. apply in_set_bop_union_elim in H.
       destruct H as [H | H]; auto. 
       intros s H.  apply in_set_bop_union_intro.
       left; auto.

       apply brel_set_intro_prop; auto.
       split.
       intros s H. apply in_set_bop_union_elim in H.
       destruct H as [H | H]; auto. 
       intros s H.  apply in_set_bop_union_intro.
       right; auto.
Defined. 


Lemma bop_union_exists_ann (enum : carrier_is_finite S r) :
   bop_exists_ann (finite_set S) (brel_set r) (bop_union r).
Proof. exists ((projT1 enum) tt).
       apply (bop_union_enum_is_ann enum). 
Defined. 

Lemma bop_union_not_exists_ann (no_enum : carrier_is_not_finite S r) : 
   bop_not_exists_ann (finite_set S) (brel_set r) (bop_union r).
Proof.  unfold bop_not_exists_ann. intro X.
        unfold bop_not_is_ann. unfold carrier_is_not_finite in no_enum. 
        assert (K := no_enum (λ _, list_of_set S X)). simpl in K.
        destruct K as [s K].
        exists (s :: nil). 
        right. case_eq(brel_set r (bop_union r (s :: nil) X) X); intro J; auto.
        apply brel_set_elim_prop  in J; auto.        
        destruct J as [L R]. 
        assert (J := L s).
        assert (F : in_set r (bop_union r (s :: nil) X) s = true).
           apply in_set_bop_union_intro.              
           left. compute. rewrite refS; auto. 
        assert (M := J F).
        assert (N : in_list r (list_of_set S X) s = true). apply in_set_implies_in_list; auto.  
        rewrite N in K. discriminate K. 
Defined. 

Definition bop_union_exists_ann_decide (fin_d : carrier_is_finite_decidable S r) : bop_exists_ann_decidable (finite_set S) (brel_set r) (bop_union r)
 := match fin_d with
     | inl fS  => inl (bop_union_exists_ann fS) 
     | inr nfs => inr (bop_union_not_exists_ann nfs)
    end.


(******************************************)

Lemma brel_subset_union_left (X Y : finite_set S) : brel_subset r X (bop_union r X Y) = true.
Proof. apply brel_subset_intro; auto. 
       intros x A.  apply in_set_bop_union_intro. left. exact A. 
Qed.

Lemma brel_subset_union_right (X Y : finite_set S) : brel_subset r Y (bop_union r X Y) = true.
Proof. apply brel_subset_intro; auto. 
       intros x A.  apply in_set_bop_union_intro. right. exact A. 
Qed.        
       
Lemma bop_union_is_glb_wrt_lte_left : bop_is_glb (brel_lte_left (brel_set r) (bop_union r)) (bop_union r).
Proof. 
       apply bop_is_glb_wrt_lte_left.
       apply brel_set_reflexive; auto. 
       apply brel_set_symmetric; auto. 
       apply brel_set_transitive; auto.
       apply bop_union_associative; auto.               
       apply bop_union_congruence; auto. 
       apply bop_union_idempotent; auto.        
       apply bop_union_commutative; auto.        
Qed. 


Lemma bop_union_is_lub_wrt_lte_right : bop_is_lub (brel_lte_right (brel_set r) (bop_union r)) (bop_union r).
Proof. apply bop_is_lub_wrt_lte_right. 
       apply brel_set_reflexive; auto. 
       apply brel_set_symmetric; auto. 
       apply brel_set_transitive; auto. 
       apply bop_union_associative; auto.
       apply bop_union_congruence; auto.        
       apply bop_union_idempotent; auto.        
       apply bop_union_commutative; auto.        
Qed. 

Lemma subset_implies_lte_right (X Y : finite_set S) : brel_subset r X Y = true -> brel_lte_right (brel_set r) (bop_union r) X Y = true. 
Proof. intro A. unfold brel_lte_right. 
       apply brel_set_intro. split. 
       - apply brel_subset_union_right. 
       - apply brel_subset_intro; auto. 
         intros a B. apply in_set_bop_union_elim in B. 
         destruct B as [B | B]. 
         + assert (C := brel_subset_elim _ r symS tranS _ _ A). 
           exact (C a B). 
         + exact B. 
Qed. 


Lemma lte_right_implies_subset (X Y : finite_set S) : brel_lte_right (brel_set r) (bop_union r) X Y = true -> brel_subset r X Y = true. 
Proof. unfold brel_lte_right. intros A.
       apply brel_set_elim in A; auto. destruct A as [A B].
       assert (C : brel_subset r X (bop_union r X Y) = true).
          apply brel_subset_union_left.
       exact (brel_subset_transitive S r refS symS tranS _ _ _ C B).  
Qed. 

(* Think of (brel_subset r) as an "optimization" of brel_lte_right (brel_set r) (bop_union r) 

Note: we could do this with some kind of extensional equality 

   (brel_subset r)  = brel_lte_right (brel_set r) (bop_union r)

and congruence of properties like bop_union_lub wrt to this equality. 
But, I'm taking an easier approach...
*) 
Lemma bop_union_lub : bop_is_lub (brel_subset r) (bop_union r).
Proof. intros X Y.
       destruct (bop_union_is_lub_wrt_lte_right X Y) as [A B].
       unfold is_upper_bound in A. destruct A as [A C].
       unfold is_lub. split. 
       - unfold is_upper_bound. split. 
         + apply lte_right_implies_subset. exact A. 
         + apply lte_right_implies_subset. exact C. 
       - intros U D. unfold is_upper_bound in D. destruct D as [D E]. 
         assert (G : is_upper_bound (brel_lte_right (brel_set r) (bop_union r)) X Y U).
            unfold is_upper_bound. split.
              apply subset_implies_lte_right. exact D. 
              apply subset_implies_lte_right. exact E. 
         assert (F := B U G).
         apply lte_right_implies_subset. exact F. 
Qed.

Lemma bop_union_glb : bop_is_glb (brel_dual (brel_subset r)) (bop_union r).
Proof.  apply lub_implies_dual_glb. apply bop_union_lub. Qed. 


(*********** "multiplicative" properties are all false. 
              see sg/theory.v and sg/cast-up.v

****************)

End Union.

End Theory.

Section ACAS.

Definition sg_CI_proofs_union {S : Type} (eqv : A_eqv S) :
    sg_CI_proofs (finite_set S) (brel_set (A_eqv_eq S eqv)) (bop_union (A_eqv_eq S eqv))
:= 
let eqvP := A_eqv_proofs S eqv in
let symS := A_eqv_symmetric _ _ eqvP in
let refS := A_eqv_reflexive _ _ eqvP in
let trnS := A_eqv_transitive _ _ eqvP in     
let rS   := A_eqv_eq S eqv in
let s    := A_eqv_witness S eqv in
let f    := A_eqv_new S eqv in
let ntS  := A_eqv_not_trivial S eqv in       
let refS := A_eqv_reflexive S rS eqvP in
let symS := A_eqv_symmetric S rS eqvP in
let tranS := A_eqv_transitive S rS eqvP in                                                            
{|
  A_sg_CI_associative        := bop_union_associative S rS refS symS tranS 
; A_sg_CI_congruence         := bop_union_congruence S rS refS symS tranS 
; A_sg_CI_commutative        := bop_union_commutative S rS refS symS tranS 
; A_sg_CI_idempotent         := bop_union_idempotent S rS refS symS tranS 
; A_sg_CI_not_selective      := bop_union_not_selective S rS refS symS s f ntS
|}.

Definition sg_CI_proofs_union_with_ann {S : Type} (c : cas_constant) (eqv : A_eqv S) := 
  sg_CI_proofs_add_ann _ _ c
    (bop_union (A_eqv_eq S eqv))
    nil
    (A_eqv_proofs _ (A_eqv_set S eqv))
    (sg_CI_proofs_union eqv).

(*the following are used in bi-semigroup (bs) constructions *)
Definition sg_C_proofs_union {S : Type} 
  (eqv : A_eqv S) : sg_C_proofs (finite_set S) (brel_set (A_eqv_eq S eqv)) (bop_union (A_eqv_eq S eqv))
:= 
let rS   := A_eqv_eq S eqv in
let s    := A_eqv_witness S eqv in
     A_sg_C_proofs_from_sg_CI_proofs
       (finite_set S)
       (brel_set rS)
       (bop_union rS)
       (set_witness s)
       (set_new rS s) 
       (brel_set_not_trivial S rS s)
       (eqv_proofs_set S rS (A_eqv_proofs _ eqv)) 
       (sg_CI_proofs_union eqv).

Definition sg_C_proofs_union_with_ann {S : Type} (c : cas_constant) (eqv : A_eqv S)  := 
  sg_C_proofs_add_ann _ _ c
    (bop_union (A_eqv_eq S eqv))
    nil
    (set_new (A_eqv_eq S eqv) (A_eqv_witness S eqv))
    (brel_set_not_trivial S (A_eqv_eq S eqv) (A_eqv_witness S eqv))
    (A_eqv_proofs _ (A_eqv_set S eqv))
    (sg_C_proofs_union eqv). 

Definition sg_proofs_union {S : Type}
  (eqv : A_eqv S) : sg_proofs (finite_set S) (brel_set (A_eqv_eq S eqv)) (bop_union (A_eqv_eq S eqv))
:= 
let rS   := A_eqv_eq S eqv in
let s    := A_eqv_witness S eqv in
     A_sg_proofs_from_sg_C_proofs
       (finite_set S)
       (brel_set rS)
       (bop_union rS)
       (set_witness s)
       (set_new rS s) 
       (brel_set_not_trivial S rS s)
       (eqv_proofs_set S rS (A_eqv_proofs _ eqv)) 
       (sg_C_proofs_union eqv). 

Definition sg_proofs_union_with_ann {S : Type} (c : cas_constant) (eqv : A_eqv S)  := 
  sg_proofs_add_ann _ _ c
    (bop_union (A_eqv_eq S eqv))
    nil
    (set_new (A_eqv_eq S eqv) (A_eqv_witness S eqv))
    (brel_set_not_trivial S (A_eqv_eq S eqv) (A_eqv_witness S eqv))
    (A_eqv_proofs _ (A_eqv_set S eqv))
    (sg_proofs_union eqv). 
(******************************************************************)

Definition A_sg_union_with_ann {S : Type} (c : cas_constant) (eqv : A_eqv S) : @A_sg_CI (with_constant(finite_set S)) := 
  let eqvP := A_eqv_proofs S eqv in
  let symS := A_eqv_symmetric _ _ eqvP in
  let refS := A_eqv_reflexive _ _ eqvP in
  let trnS := A_eqv_transitive _ _ eqvP in     
  let eqS  := A_eqv_eq S eqv in
  let s    := A_eqv_witness S eqv in
  let f    := A_eqv_new S eqv in
  let ntS  := A_eqv_not_trivial S eqv in
  let eqv_union := A_eqv_set S eqv in
  let bop   := bop_union eqS in

   {| 
     A_sg_CI_eqv          := A_eqv_add_constant _ eqv_union c  
   ; A_sg_CI_bop          := bop_add_ann bop c 
   ; A_sg_CI_exists_id_d  := inl (bop_union_with_ann_exists_id S c eqS refS symS trnS)
   ; A_sg_CI_exists_ann_d := inl (bop_union_with_ann_exists_ann S c eqS) 
   ; A_sg_CI_proofs       := sg_CI_proofs_union_with_ann c eqv 
   ; A_sg_CI_ast          := Ast_sg_add_ann(c, Ast_sg_union (A_eqv_ast S eqv))
   |}.


Definition A_sg_union {S : Type} (eqv : A_eqv S) : A_sg_CI (finite_set S) := 
  let eqvP := A_eqv_proofs S eqv in
  let symS := A_eqv_symmetric _ _ eqvP in
  let refS := A_eqv_reflexive _ _ eqvP in
  let trnS := A_eqv_transitive _ _ eqvP in     
  let eqS  := A_eqv_eq S eqv in
  let s    := A_eqv_witness S eqv in
  let f    := A_eqv_new S eqv in
  let ntS  := A_eqv_not_trivial S eqv in
   {| 
     A_sg_CI_eqv          := A_eqv_set S eqv 
   ; A_sg_CI_bop          := bop_union eqS 
   ; A_sg_CI_exists_id_d  := inl (bop_union_exists_id S eqS refS symS trnS) 
   ; A_sg_CI_exists_ann_d := bop_union_exists_ann_decide S eqS refS symS trnS (A_eqv_finite_d _ eqv) 
   ; A_sg_CI_proofs       := sg_CI_proofs_union eqv
   ; A_sg_CI_ast          := Ast_sg_union (A_eqv_ast S eqv)
   |}.

Definition bop_union_glb_proofs {S : Type} (eqv : A_eqv S) :
      bop_is_glb (brel_dual (brel_subset (A_eqv_eq S eqv))) (bop_union (A_eqv_eq S eqv)) :=
let eq   := A_eqv_eq S eqv in
let eqvP := A_eqv_proofs S eqv in
let refS := A_eqv_reflexive S eq eqvP in
let symS := A_eqv_symmetric S eq eqvP in
let trnS := A_eqv_transitive S eq eqvP in bop_union_glb S eq refS symS trnS. 

(*
Definition msl_union_proofs {S : Type} (eqv : A_eqv S) :
      meet_semilattice_proofs (brel_set (A_eqv_eq S eqv)) (brel_dual (brel_subset (A_eqv_eq S eqv))) (bop_union (A_eqv_eq S eqv)) :=
{|
  A_msl_lte_proofs    := po_dual_proofs _ _ (po_subset_proofs eqv) 
; A_msl_meet_proofs   := sg_CI_proofs_union eqv
; A_msl_glb           := bop_union_glb_proofs eqv 
|}.


Definition A_msl_union {S : Type} (eqv : A_eqv S) : @A_meet_semilattice (finite_set S) :=
let eq   := A_eqv_eq S eqv in
{|
  A_msl_eqv           := A_eqv_set S eqv
; A_msl_lte           := brel_dual (brel_subset eq)
; A_msl_meet          := bop_union eq 
; A_msl_proofs        := msl_union_proofs eqv 
(* ; A_msl_top_bottom_proofs : posg_top_bottom_id_ann_proofs S (A_eqv_eq S A_posg_eqv) A_posg_lte A_posg_times *) 
; A_msl_ast           := Ast_sg_union (A_eqv_ast S eqv) (* fix *)
|}.
*) 

Definition bop_union_lub_proofs {S : Type} (eqv : A_eqv S) :
      bop_is_lub (brel_subset (A_eqv_eq S eqv)) (bop_union (A_eqv_eq S eqv)) :=
let eq   := A_eqv_eq S eqv in
let eqvP := A_eqv_proofs S eqv in
let refS := A_eqv_reflexive S eq eqvP in
let symS := A_eqv_symmetric S eq eqvP in
let trnS := A_eqv_transitive S eq eqvP in bop_union_lub S eq refS symS trnS. 

(*
Definition jsl_union_proofs {S : Type} (eqv : A_eqv S) :
      join_semilattice_proofs (brel_set (A_eqv_eq S eqv)) (brel_subset (A_eqv_eq S eqv)) (bop_union (A_eqv_eq S eqv)) :=
{|
  A_jsl_lte_proofs    := po_subset_proofs eqv
; A_jsl_join_proofs   := sg_CI_proofs_union eqv
; A_jsl_lub           := bop_union_lub_proofs eqv 
|}.


Definition A_jsl_union {S : Type} (eqv : A_eqv S) : @A_join_semilattice (finite_set S) :=
let eq   := A_eqv_eq S eqv in
{|
  A_jsl_eqv           := A_eqv_set S eqv
; A_jsl_lte           := brel_subset eq
; A_jsl_join          := bop_union eq
; A_jsl_proofs        := jsl_union_proofs eqv                                    
(* ; A_jsl_top_bottom_proofs : posg_top_bottom_id_ann_proofs S (A_eqv_eq S A_posg_eqv) A_posg_lte A_posg_times *) 
; A_jsl_ast           := Ast_sg_union (A_eqv_ast S eqv) (* fix *)
|}.

*) 
End ACAS.


Section AMCAS.

Definition A_sg_union_below_sg_CI {S : Type} (E : A_eqv S) : @A_below_sg_CI (finite_set S)  :=
    A_classify_sg_CI (A_sg_union E) . 

Definition A_sg_union_with_ann_below_sg_CI {S : Type}
  (c : cas_constant)
   (E : A_eqv S) : @A_below_sg_CI (with_constant (finite_set S))  :=
    A_classify_sg_CI (A_sg_union_with_ann c E) . 

Definition A_mcas_sg_union {S : Type} (A : @A_mcas_eqv S) :=
match A with
| A_EQV_eqv B    =>
    A_MCAS_sg
      (A_Below_sg_sg_C
         (A_Below_sg_C_sg_CI (A_sg_union_below_sg_CI B)))

| A_EQV_Error sl => A_MCAS_sg_Error sl 
end.

Definition A_mcas_sg_union_with_ann {S : Type} (c : cas_constant) (A : @A_mcas_eqv S) :=
match A with
| A_EQV_eqv B    =>
    A_MCAS_sg
      (A_Below_sg_sg_C
         (A_Below_sg_C_sg_CI (A_sg_union_with_ann_below_sg_CI c B)))

| A_EQV_Error sl => A_MCAS_sg_Error sl 
end.


End AMCAS.   


Section CAS.

Definition  check_union_exists_ann {S : Type} (d : @check_is_finite S) : @check_exists_ann (finite_set S)
  := match d with
     | Certify_Is_Finite fS  => Certify_Exists_Ann (fS tt)
     | Certify_Is_Not_Finite => Certify_Not_Exists_Ann
     end.

Definition bop_union_exists_ann_certify {S : Type} (fin_d : @check_is_finite S) : @check_exists_ann (finite_set S) 
 := match fin_d with
     | Certify_Is_Finite h  => Certify_Exists_Ann (h tt) 
     | Certify_Is_Not_Finite  => Certify_Not_Exists_Ann 
    end.

Definition sg_CI_certs_union : ∀ {S : Type}, @eqv S -> @sg_CI_certificates (finite_set S)
:= λ {S} eqvS,  
let s   := eqv_witness eqvS in
let f   := eqv_new eqvS in
{|
  sg_CI_associative        := Assert_Associative  
; sg_CI_congruence         := Assert_Bop_Congruence  
; sg_CI_commutative        := Assert_Commutative  
; sg_CI_idempotent         := Assert_Idempotent  
; sg_CI_not_selective      := Assert_Not_Selective ((s :: nil), ((f s) :: nil))
|}. 

Definition sg_CI_certs_union_with_ann {S : Type} (c : cas_constant) (eqv : @eqv S) := 
  sg_CI_certs_add_ann c (sg_CI_certs_union eqv).


Definition sg_C_certs_union {S : Type} (eqv : @eqv S) :=
let rS   := eqv_eq eqv in
let s    := eqv_witness eqv in
     sg_C_certs_from_sg_CI_certs
       (finite_set S)
       (brel_set rS)
       (bop_union rS)
       (set_witness s)
       (set_new rS s) 
       (sg_CI_certs_union eqv).


Definition sg_C_certs_union_with_ann {S : Type} (c : cas_constant) (eqv : @eqv S)  := 
  sg_C_certs_add_ann c
    nil 
    (set_new (eqv_eq eqv) (eqv_witness eqv))
    (sg_C_certs_union eqv).

Definition sg_certs_union {S : Type} (eqv : @eqv S) :=
let rS   := eqv_eq eqv in
let s    := eqv_witness eqv in
     sg_certs_from_sg_C_certs
       (finite_set S)
       (brel_set rS)
       (bop_union rS)
       (set_witness s)
       (set_new rS s) 
       (sg_C_certs_union eqv).

Definition sg_certs_union_with_ann {S : Type} (c : cas_constant) (eqv : @eqv S)  := 
  sg_certs_add_ann c
    nil 
    (set_new (eqv_eq eqv) (eqv_witness eqv))
    (sg_certs_union eqv).

Definition sg_union_with_ann {S : Type} (c : cas_constant) (eqvS : @eqv S) : 
        @sg_CI (with_constant (finite_set S)) := 
  let eqS := eqv_eq eqvS in
  let s   := eqv_witness eqvS in
  let f   := eqv_new eqvS in
  let union_eqv := eqv_set eqvS in
  let bop   := bop_union eqS in  
   {| 
     sg_CI_eqv          := eqv_add_constant union_eqv c  
   ; sg_CI_bop          := bop_add_ann bop c 
   ; sg_CI_exists_id_d  := Certify_Exists_Id (inr nil) 
   ; sg_CI_exists_ann_d := Certify_Exists_Ann (inl c) 
   ; sg_CI_certs        := sg_CI_certs_union_with_ann c eqvS
   ; sg_CI_ast          := Ast_sg_add_ann(c, Ast_sg_union (eqv_ast eqvS))
   |}. 
 
Definition sg_union {S : Type} (eqv : @eqv S) : @sg_CI (finite_set S) := 
  let eqS  := eqv_eq eqv in
  let s    := eqv_witness eqv in
  let f    := eqv_new eqv in
   {| 
     sg_CI_eqv          := eqv_set eqv 
   ; sg_CI_bop          := bop_union eqS 
   ; sg_CI_exists_id_d  := Certify_Exists_Id nil 
   ; sg_CI_exists_ann_d := bop_union_exists_ann_certify (eqv_finite_d eqv) 
   ; sg_CI_certs        := sg_CI_certs_union eqv
   ; sg_CI_ast          := Ast_sg_union (eqv_ast eqv)
   |}.

(*
Definition sg_union {S : Type} (eqv : @eqv S) : @sg (finite_set S) := 
  let eqS  := eqv_eq eqv in
  let s    := eqv_witness eqv in
  let f    := eqv_new eqv in
   {| 
     sg_eqv          := eqv_set eqv 
   ; sg_bop          := bop_union eqS 
   ; sg_exists_id_d  := Certify_Exists_Id nil 
   ; sg_exists_ann_d := bop_union_exists_ann_certify (eqv_finite_d eqv) 
   ; sg_certs        := sg_certs_from_sg_CI_certs 
                                (finite_set S)
                                (brel_set eqS)
                                (bop_union eqS)
                                (s :: nil)
                                (λ (l : finite_set S), if brel_set eqS nil l then (s :: nil) else nil) (* fix someday *) 
                                (sg_CI_certs_union eqv)
   ; sg_ast          := Ast_sg_union (eqv_ast eqv)
   |}.

*) 
End CAS.

Section MCAS.


Definition sg_union_below_sg_CI {S : Type} (E : @eqv S) : @below_sg_CI (finite_set S)  :=
    classify_sg_CI (sg_union E) . 

Definition sg_union_with_ann_below_sg_CI {S : Type}
  (c : cas_constant)
   (E : @eqv S) : @below_sg_CI (with_constant (finite_set S))  :=
    classify_sg_CI (sg_union_with_ann c E) . 

Definition mcas_sg_union {S : Type} (A : @mcas_eqv S) :=
match A with
| EQV_eqv B    =>
    MCAS_sg
      (Below_sg_sg_C
         (Below_sg_C_sg_CI (sg_union_below_sg_CI B)))

| EQV_Error sl => MCAS_sg_Error sl 
end.

Definition mcas_sg_union_with_ann {S : Type} (c : cas_constant) (A : @mcas_eqv S) :=
match A with
| EQV_eqv B    =>
    MCAS_sg
      (Below_sg_sg_C
         (Below_sg_C_sg_CI (sg_union_with_ann_below_sg_CI c B)))

| EQV_Error sl => MCAS_sg_Error sl 
end.
     

End MCAS.   

Section Verify.


Lemma correct_bop_union_exists_ann_certify (S : Type) (eqvS : A_eqv S): 
      bop_union_exists_ann_certify (p2c_is_finite_check S (A_eqv_eq S eqvS) (A_eqv_finite_d S eqvS))
      = 
      p2c_exists_ann_check (finite_set S) (brel_set (A_eqv_eq S eqvS)) (bop_union (A_eqv_eq S eqvS))
           (bop_union_exists_ann_decide S (A_eqv_eq S eqvS)
               (A_eqv_reflexive S (A_eqv_eq S eqvS) (A_eqv_proofs S eqvS))
               (A_eqv_symmetric S (A_eqv_eq S eqvS) (A_eqv_proofs S eqvS))
               (A_eqv_transitive S (A_eqv_eq S eqvS) (A_eqv_proofs S eqvS))
               (A_eqv_finite_d S eqvS)).
Proof. unfold bop_union_exists_ann_certify, bop_union_exists_ann_decide, p2c_exists_ann_check;
       destruct (A_eqv_finite_d S eqvS) as [[h finP] | nfinP]; simpl; reflexivity. 
Qed.


Lemma correct_sg_CI_certs_union (S : Type) (eqvS : A_eqv S): 
      sg_CI_certs_union (A2C_eqv S eqvS)
      =                        
      P2C_sg_CI (brel_set (A_eqv_eq S eqvS)) (bop_union (A_eqv_eq S eqvS))
                (sg_CI_proofs_union eqvS).
Proof. destruct eqvS.
       unfold sg_CI_certs_union, sg_CI_proofs_union. unfold P2C_sg_CI. simpl.
       reflexivity.        
Qed.

Lemma correct_sg_CI_certs_union_with_ann (S : Type) (c : cas_constant) (eqvS : A_eqv S): 
      sg_CI_certs_union_with_ann c (A2C_eqv S eqvS)
      =                        
      P2C_sg_CI (brel_sum brel_constant (A_eqv_eq (finite_set S) (A_eqv_set S eqvS)))
                (bop_add_ann (bop_union (A_eqv_eq S eqvS)) c)
                (sg_CI_proofs_union_with_ann c eqvS).
Proof. destruct eqvS.
       unfold sg_CI_certs_union, sg_CI_proofs_union. unfold P2C_sg_CI. simpl.
       reflexivity.        
Qed.


Lemma correct_sg_C_certs_union (S : Type) (eqvS : A_eqv S): 
      sg_C_certs_union (A2C_eqv S eqvS)
      =                        
      P2C_sg_C (brel_set (A_eqv_eq S eqvS)) (bop_union (A_eqv_eq S eqvS))
               (sg_C_proofs_union eqvS).
Proof. unfold sg_C_certs_union, sg_C_proofs_union.
       rewrite <- correct_sg_C_certs_from_sg_CI_certs. 
       rewrite correct_sg_CI_certs_union.  
       reflexivity.               
Qed.

Lemma correct_sg_C_certs_union_with_ann (S : Type) (c : cas_constant) (eqvS : A_eqv S): 
      sg_C_certs_union_with_ann c (A2C_eqv S eqvS)
      =                        
      P2C_sg_C (brel_sum brel_constant (A_eqv_eq (finite_set S) (A_eqv_set S eqvS)))
               (bop_add_ann (bop_union (A_eqv_eq S eqvS)) c)
               (sg_C_proofs_union_with_ann c eqvS).
Proof. unfold sg_C_certs_union_with_ann, sg_C_proofs_union_with_ann.
       rewrite <- correct_sg_C_certs_add_ann. 
       rewrite correct_sg_C_certs_union.  
       reflexivity.               
Qed.


Lemma correct_sg_certs_union (S : Type) (eqvS : A_eqv S): 
      sg_certs_union (A2C_eqv S eqvS)
      =                        
      P2C_sg (brel_set (A_eqv_eq S eqvS)) (bop_union (A_eqv_eq S eqvS))
             (sg_proofs_union eqvS).
Proof. unfold sg_certs_union, sg_proofs_union.
       rewrite <- correct_sg_certs_from_sg_C_certs. 
       rewrite correct_sg_C_certs_union.  
       reflexivity.               
Qed.

Lemma correct_sg_certs_union_with_ann (S : Type) (c : cas_constant) (eqvS : A_eqv S): 
      sg_certs_union_with_ann c (A2C_eqv S eqvS)
      =                        
      P2C_sg (brel_sum brel_constant (A_eqv_eq (finite_set S) (A_eqv_set S eqvS)))
             (bop_add_ann (bop_union (A_eqv_eq S eqvS)) c)
             (sg_proofs_union_with_ann c eqvS).
Proof. unfold sg_certs_union_with_ann, sg_proofs_union_with_ann.
       rewrite <- correct_sg_certs_add_ann. 
       rewrite correct_sg_certs_union.  
       reflexivity.               
Qed.
  
Theorem correct_sg_union (S : Type) (eqvS : A_eqv S) : 
  sg_union  (A2C_eqv S eqvS)
  =
  A2C_sg_CI (A_sg_union eqvS). 
Proof. unfold sg_union, A_sg_union, A2C_sg_CI; simpl. 
       rewrite correct_eqv_set.        
       rewrite correct_sg_CI_certs_union. 
       rewrite <- correct_bop_union_exists_ann_certify.
       reflexivity. 
Qed. 


Theorem correct_sg_union_with_ann (S : Type) (c : cas_constant) (eqvS : A_eqv S) : 
  sg_union_with_ann c (A2C_eqv S eqvS)
  =
  A2C_sg_CI (A_sg_union_with_ann c eqvS). 
Proof. unfold sg_union_with_ann, A_sg_union_with_ann, A2C_sg_CI; simpl. 
       rewrite correct_eqv_set.        
       rewrite correct_eqv_add_constant.
       rewrite correct_sg_CI_certs_union_with_ann. 
       reflexivity. 
Qed. 

Theorem correct_sg_union_below_sg_CI (S : Type )(A : A_eqv S) : 
    sg_union_below_sg_CI (A2C_eqv S A)
    =
    A2C_below_sg_CI (A_sg_union_below_sg_CI A).
Proof. unfold sg_union_below_sg_CI, A_sg_union_below_sg_CI.
       rewrite correct_sg_union.
       rewrite correct_classify_sg_CI. 
       reflexivity.
Qed.

Theorem correct_sg_union_with_ann_below_sg_CI (S : Type ) (c : cas_constant) (A : A_eqv S) : 
    sg_union_with_ann_below_sg_CI c (A2C_eqv S A)
    =
    A2C_below_sg_CI (A_sg_union_with_ann_below_sg_CI c A).
Proof. unfold sg_union_with_ann_below_sg_CI, A_sg_union_with_ann_below_sg_CI.
       rewrite correct_sg_union_with_ann.
       reflexivity.
Qed.
  
Theorem correct_bop_mcas_union (S : Type) (eqvS : @A_mcas_eqv S): 
         mcas_sg_union (A2C_mcas_eqv S eqvS)  
         = 
         A2C_sg_mcas (A_mcas_sg_union eqvS). 
Proof. unfold mcas_sg_union, A_mcas_sg_union.
       destruct eqvS; simpl. 
       + reflexivity.
       + rewrite correct_sg_union_below_sg_CI.
         unfold A_sg_union_below_sg_CI. 
         rewrite <- correct_classify_sg_CI.
         unfold classify_sg_CI. 
         reflexivity. 
Qed.  

Theorem correct_bop_mcas_union_with_ann
  (S : Type) (c : cas_constant)(eqvS : @A_mcas_eqv S): 
         mcas_sg_union_with_ann c (A2C_mcas_eqv S eqvS)  
         = 
         A2C_sg_mcas (A_mcas_sg_union_with_ann c eqvS). 
Proof. unfold mcas_sg_union_with_ann, A_mcas_sg_union_with_ann.
       destruct eqvS; simpl.
       + reflexivity. 
       + rewrite correct_sg_union_with_ann_below_sg_CI.
         unfold A_sg_union_with_ann_below_sg_CI. 
         rewrite <- correct_classify_sg_CI.
         unfold classify_sg_CI. 
         reflexivity. 
Qed.  


End Verify.   
  
