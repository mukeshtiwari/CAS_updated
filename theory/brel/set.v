Require Import Coq.Bool.Bool. 
Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.code.uop. 
Require Import CAS.theory.brel_properties. 
Require Import CAS.theory.facts. 
Require Import CAS.theory.brel.subset.

Section BrelSet.
  Variable S: Type.
  Variable eq : brel S.
  Variable refS : brel_reflexive S eq.
  Variable symS : brel_symmetric S eq.
  Variable tranS : brel_transitive S eq.


Lemma brel_set_nil : ∀ (X : finite_set S), brel_set eq nil X = true -> X = nil. 
Proof. induction X; intro H. reflexivity. compute in H. discriminate. Defined. 


Lemma brel_set_intro : ∀ (X Y : finite_set S), (brel_subset eq X Y = true) * (brel_subset eq Y X = true)  → brel_set eq X Y = true. 
Proof. intros X Y [H1 H2]. unfold brel_set. unfold brel_and_sym. apply andb_is_true_right; auto. Defined. 

Lemma brel_set_elim : ∀ (X Y : finite_set S), 
     brel_set eq X Y = true -> (brel_subset eq X Y = true) * (brel_subset eq Y X = true).
Proof. intros X Y H. unfold brel_set in H. unfold brel_and_sym in H. 
       apply andb_is_true_left in H. destruct H as [H1 H2]; auto. 
Defined. 

Lemma brel_set_intro_prop : ∀ (X Y : finite_set S), 
        (∀ a : S, in_set eq X a = true → in_set eq Y a = true) 
      * (∀ a : S, in_set eq Y a = true → in_set eq X a = true)  → 
             brel_set eq X Y = true. 
Proof. intros X Y [H1 H2]. apply brel_set_intro. split. 
          apply brel_subset_intro in H1; auto. 
          apply brel_subset_intro in H2; auto. 
Defined. 

Lemma brel_set_elim_prop : ∀ (X Y : finite_set S),
     brel_set eq X Y = true -> 
        (∀ a : S, in_set eq X a = true → in_set eq Y a = true) 
      * (∀ a : S, in_set eq Y a = true → in_set eq X a = true).
Proof. intros X Y H. unfold brel_set in H. unfold brel_and_sym in H. 
       apply andb_is_true_left in H. destruct H as [H1 H2]. 
       assert (A1 := brel_subset_elim S eq symS tranS _ _ H1). 
       assert (A2 := brel_subset_elim S eq symS tranS _ _ H2); auto. 
Defined. 


(* 
   ∀ (t : S) (s1 s2 : finite_set S),
   brel_set X s1 s2 = true → in_set X s1 t = in_set X s2 t
*) 
Lemma in_set_left_congruence : brel2_left_congruence (finite_set S) S (brel_set eq) (in_set eq). 
Proof. unfold brel2_left_congruence.
       intros t s1 s2 H. 
       apply brel_set_elim_prop in H; auto. destruct H as [L R]. 
       case_eq(in_set eq s1 t); intro J; 
       case_eq(in_set eq s2 t); intro K; auto.  
          rewrite (L t J) in K. assumption. 
          rewrite (R t K) in J. discriminate. 
Defined. 

(***     brel_set eqv properties   ****)

(* move and_sym lemmas? *)
Lemma brel_and_sym_relexive (T : Type) (r : brel T) (refr : brel_reflexive T r) : brel_reflexive T (brel_and_sym r). 
Proof. unfold brel_reflexive, brel_and_sym. intros s. 
       rewrite (refr s). simpl. reflexivity. 
Defined. 

Lemma brel_and_sym_transitive (T : Type) (r : brel T) (tranr : brel_transitive T r) : brel_transitive T (brel_and_sym r). 
Proof. unfold brel_transitive, brel_and_sym. intros s t u H1 H2. 
       apply andb_is_true_left in H1. destruct H1 as [H1_l H1_r].        
       apply andb_is_true_left in H2. destruct H2 as [H2_l H2_r].        
       rewrite (tranr _ _ _ H1_l H2_l).
       rewrite (tranr _ _ _ H2_r H1_r ). simpl. reflexivity. 
Defined. 

Lemma brel_and_sym_symmetric (T : Type) (r : brel T) : brel_symmetric T (brel_and_sym r). 
Proof. unfold brel_symmetric, brel_and_sym. intros s t H. 
       apply andb_is_true_left in H. destruct H as [H_l H_r].        
       rewrite H_l. rewrite H_r. simpl. reflexivity. 
Defined. 


(***)


Lemma brel_set_reflexive : brel_reflexive (finite_set S) (brel_set eq). 
Proof. unfold brel_set. 
       apply brel_and_sym_relexive. 
       apply brel_subset_reflexive; auto. 
Defined.

Lemma brel_set_transitive : brel_transitive (finite_set S) (brel_set eq). 
Proof. unfold brel_set.
       apply brel_and_sym_transitive. 
       apply brel_subset_transitive; auto. 
Defined.

Lemma brel_set_symmetric : brel_symmetric (list S) (brel_set eq). 
Proof. unfold brel_set. apply brel_and_sym_symmetric. Defined. 

Lemma brel_set_congruence : brel_congruence (finite_set S) (brel_set eq) (brel_set eq). 
Proof. apply brel_congruence_self. 
       apply brel_set_symmetric; auto.  
       apply brel_set_transitive; auto.  
Defined. 

Lemma brel_set_not_trivial (s : S) : 
   brel_not_trivial (finite_set S) (brel_set eq) (λ (l : finite_set S), if brel_set eq nil l then (s :: nil) else nil). 
Proof. intro X. destruct X; compute; auto. Qed. 

(* 
Lemma brel_set_rep_correct : ∀ (rep : unary_op S), 
          brel_rep_correct S eq rep →
              brel_rep_correct (finite_set S) (brel_set S eq) (uop_set_rep S eq rep). 
Proof. intros rep P l. 
       apply brel_set_intro. split. 
          apply brel_subset_intro;auto. intros s H. 
          apply brel_subset_intro;auto. admit.  
Defined. 

Lemma brel_set_rep_idempotent : ∀ (rep : unary_op S), 
          brel_rep_idempotent S eq rep →
              brel_rep_idempotent (finite_set S) (brel_set S eq) (uop_set_rep S eq rep). 
Proof. intros rep P l. induction l. 
       simpl. reflexivity. 
       simpl. apply andb_is_true_right. split. 
          apply P. 
          assumption. 
Defined. 
 *)
End BrelSet.