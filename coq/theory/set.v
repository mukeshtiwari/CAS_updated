
Require Import Coq.Arith.Arith.     (* beq_nat *) 
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List. 

Require Import CAS.coq.common.compute. 
Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.theory.

Require Import CAS.coq.sg.and.
Require Import CAS.coq.sg.or. 

Open Scope list_scope.
Close Scope nat_scope. (* why? *) 
Section Computation.

Definition in_set : ∀ {S : Type},  brel S -> brel2 (finite_set S) S
:= fix f {S} r l s := 
   match l with 
   | nil => false 
   | a :: rest => bop_or (r s a) (f r rest s)
   end. 
  

Definition uop_duplicate_elim : ∀ {S : Type}, brel S -> unary_op (finite_set S) 
:= λ {S} r,  fix f x := 
      match x with
         | nil => nil
         | a :: y => 
            if in_set r y a 
              then f y
              else a :: (f y)
      end.

(* yes, cheating for now ... *) 
Definition uop_set_map : ∀ {S : Type}, unary_op S → unary_op (finite_set S) 
:= λ {S} f X,  uop_list_map f X. 

Definition uop_set_rep : ∀ {S : Type}, brel S -> unary_op S → unary_op (finite_set S) 
:= λ {S} eq f X,  uop_duplicate_elim eq (uop_set_map f X). 


End Computation. 


Section InSet.
  Variable S: Type.
  Variable r : brel S.
  Variable refS : brel_reflexive S r.
  Variable symS : brel_symmetric S r.
  Variable tranS : brel_transitive S r.


Definition list_of_set (X : finite_set S) : list S := X.

Lemma in_set_implies_in_list (s : S) (X : finite_set S) : in_set r X s = true -> in_list r (list_of_set X) s = true. 
Proof. auto. Qed. 
  

Lemma in_set_cons_intro  : ∀ (a b : S) (X : finite_set S),
    ((r a b = true) + (in_set r X b = true)) ->   in_set r (a :: X) b = true.
Proof. intros a b X [H | H]; unfold in_set; fold (@in_set S); apply bop_or_intro; auto. Qed.        
       
Lemma in_set_cons_elim : ∀ (a b : S) (X : finite_set S),
    in_set r (a :: X) b = true -> ((r a b = true) + (in_set r X b = true)). 
Proof. intros a b X H.
       unfold in_set in H. fold (@in_set S) in H. 
       apply bop_or_elim in H.
       destruct H as [H | H]; auto.
Qed.


Lemma not_in_set_cons_intro  : ∀ (a b : S) (X : finite_set S),
    ((r a b = false) * (in_set r X b = false)) ->   in_set r (a :: X) b = false.
Proof. intros a b X [H1 H2]. unfold in_set. fold (@in_set S). 
       apply (brel_symmetric_implies_dual S r symS) in H1.
       rewrite H1, H2. compute; reflexivity. 
Qed.

Lemma not_in_set_cons_elim : ∀ (a b : S) (X : finite_set S),
    in_set r (a :: X) b = false -> ((r a b = false) * (in_set r X b = false)). 
Proof. intros a b X H.
       unfold in_set in H. fold (@in_set S) in H. 
       apply bop_or_false_elim in H.
       destruct H as [H1 H2]; split; auto. 
       apply (brel_symmetric_implies_dual S r symS) in H1. exact H1. 
Qed.



Lemma in_set_singleton_elim : ∀ (a b : S), in_set r (a :: nil) b = true -> r a b = true.
Proof. intros a b H.
       compute in H. case_eq(r b a); intro F. apply symS. rewrite F in H; auto.
       rewrite F in H; discriminate H.
Qed.        

Lemma in_set_singleton_intro : ∀ (a b : S), r a b = true -> in_set r (a :: nil) b = true. 
Proof. intros a b H.
       compute. apply symS in H. rewrite H; auto. 
Qed.


Lemma in_set_two_set_elim : ∀ (a b c: S), in_set r (a :: b :: nil) c = true -> (r a c = true) + (r b c = true).
Proof. intros a b c H.
       apply in_set_cons_elim in H; auto.
       destruct H as [H | H]; auto. 
       apply in_set_cons_elim in H; auto.
       destruct H as [H | H]; auto.
       compute in H. discriminate H. 
 Qed.        

Lemma in_set_two_set_intro : ∀ (a b c: S), (r a c = true) + (r b c = true) -> in_set r (a :: b :: nil) c = true.
Proof. intros a b c [H | H].
       apply in_set_cons_intro; auto. 
       apply in_set_cons_intro; auto. right.
       apply in_set_cons_intro; auto.        
 Qed.        


Lemma in_set_three_set_elim : ∀ (a b c d : S), in_set r (a :: b :: c :: nil) d = true -> (r a d = true) + (r b d = true) + (r c d = true).
Proof. intros a b c d H.
       apply in_set_cons_elim in H; auto.
       destruct H as [H | H]; auto. 
       apply in_set_cons_elim in H; auto.
       destruct H as [H | H]; auto.
       apply in_set_cons_elim in H; auto.
       destruct H as [H | H]; auto.
       compute in H. discriminate H. 
Qed.        

Lemma in_set_three_set_intro : ∀ (a b c d : S), (r a d = true) + (r b d = true) + (r c d = true) -> in_set r (a :: b :: c :: nil) d = true.
Proof. intros a b c d [[H | H] | H]. 
       apply in_set_cons_intro; auto. 
       apply in_set_cons_intro; auto. right.
       apply in_set_cons_intro; auto.
       apply in_set_cons_intro; auto. right.
       apply in_set_cons_intro; auto. right.
       apply in_set_cons_intro; auto.       
 Qed.        


Lemma in_set_four_set_elim : ∀ (a b c d e : S), in_set r (a :: b :: c :: d :: nil) e = true
                                                -> (r a e = true) + (r b e = true) + (r c e = true) + (r d e = true).
Proof. intros a b c d e H.
       apply in_set_cons_elim in H; auto.
       destruct H as [H | H]; auto. 
       apply in_set_cons_elim in H; auto.
       destruct H as [H | H]; auto.
       apply in_set_cons_elim in H; auto.
       destruct H as [H | H]; auto.
       apply in_set_cons_elim in H; auto.
       destruct H as [H | H]; auto.
       compute in H. discriminate H. 
Qed.        

Lemma in_set_four_set_intro : ∀ (a b c d e : S), (r a e = true) + (r b e = true) + (r c e = true) + (r d e = true)
                                                 -> in_set r (a :: b :: c :: d :: nil) e = true.
Proof. intros a b c d e [[[H | H] | H] | H].
       apply in_set_cons_intro; auto.  
       apply in_set_cons_intro; auto. right.
       apply in_set_cons_intro; auto.
       apply in_set_cons_intro; auto. right.
       apply in_set_cons_intro; auto. right.
       apply in_set_cons_intro; auto.
       apply in_set_cons_intro; auto. right.
       apply in_set_cons_intro; auto. right.
       apply in_set_cons_intro; auto. right.
       apply in_set_cons_intro; auto.       
 Qed.        



Lemma in_set_right_congruence : ∀ (a b : S) (X : finite_set S),
    r a b = true -> in_set r X a = true -> in_set r X b = true.
Proof. intros a b X H.
       induction X.
       compute. auto.
       unfold in_set. fold (@in_set S).
       intro K.
       apply bop_or_intro. apply bop_or_elim in K.
       destruct K as [K | K].
       left. apply symS in H. apply (tranS _ _ _ H K). 
       right. apply IHX; auto.
Qed.

Lemma in_set_bProp_congruence : ∀ (X : finite_set S), bProp_congruence S r (in_set r X).
Proof. intros X a b E.
       case_eq(in_set r X a); intro H1; case_eq(in_set r X b); intro H2; auto. 
       rewrite (in_set_right_congruence _ _ _ E H1) in H2. discriminate H2. 
       apply symS in E. rewrite (in_set_right_congruence _ _ _ E H2) in H1. discriminate H1. 
Qed.


Lemma in_set_map_intro :
  ∀ (f : S -> S)
    (cong : ∀ s t, r s t = true -> r (f s) (f t) = true)
    (X : finite_set S) (a : S),
    { b : S & (in_set r X b = true) * (r a (f b) = true) } ->
       in_set r (map f X) a = true.
Proof.  intros f cong. induction X as [ | x X]; intros a [b [A B]].
        - compute in A. discriminate A. 
        - simpl. apply bop_or_intro.
          apply in_set_cons_elim in A.
          destruct A as [A | A].
          + left. assert (C := cong _ _ A).
            apply symS in C.
            exact (tranS _ _ _ B C). 
          + assert (C : {b : S & (in_set r X b = true) * (r a (f b) = true)}).
            {
              exists b; auto.
            }
            right. exact (IHX _ C). 
Qed.

Lemma in_set_map_elim : ∀ (f : S -> S) (X : finite_set S) (a : S),
    in_set r (map f X) a = true ->
       { b : S & (in_set r X b = true) * (r a (f b) = true) }.
Proof.  intro f. induction X as [ | x X]; intros a A.
        - compute in A. discriminate A. 
        - simpl in A. apply bop_or_elim in A.
          destruct A as [A | A].
          + exists x. split; auto.
            apply in_set_cons_intro; auto. 
          + destruct (IHX _ A) as [b [B C]].
            exists b; split; auto.
            apply in_set_cons_intro; auto. 
Defined. 



Lemma in_set_filter_elim :    ∀ (g : bProp S) (X : finite_set S) (a : S),
    bProp_congruence S r g ->
    in_set r (filter g X) a = true -> (g a = true) * (in_set r X a = true).
Proof. intros g X a cong H.
       induction X.  compute in H.  discriminate H.
       unfold filter in H. fold (@filter S) in H. 
       unfold in_set.  fold (@in_set S).
       case_eq(g a); intro J; case_eq(r a a0); intro K; case_eq(g a0); intro L; auto. 
       split; auto. simpl. rewrite L in H. unfold in_set in H. fold (@in_set S) in H. 
       rewrite K in H. simpl in H.  apply IHX; auto. 
       split; auto; simpl. rewrite L in H. apply IHX; auto.
       rewrite (cong _ _ K) in J. rewrite L in J. discriminate J.
       rewrite L in H. destruct (IHX H) as [F _]. rewrite F in J. discriminate J. 
       rewrite L in H.
       unfold in_set in H. fold (@in_set S) in H. rewrite K in H. simpl in H. 
       destruct (IHX H) as [F _]. rewrite F in J. discriminate J.
       rewrite L in H. destruct (IHX H) as [F _]. rewrite F in J. discriminate J.
Qed.

Lemma in_set_uop_filter_elim : ∀ (f : bProp S) (X : finite_set S) (a : S), (bProp_congruence S r f) -> 
           in_set r (uop_filter f X) a = true -> (f a = true) * (in_set r X a = true).
Proof. unfold uop_filter. apply in_set_filter_elim. Defined. 


Lemma in_set_filter_intro :    ∀ (g : bProp S) (X : finite_set S) (a : S),
    bProp_congruence S r g ->
    (g a = true) * (in_set r X a = true) -> in_set r (filter g X) a = true.
Proof. intros g X a cong [gP inX].
       induction X.
       compute in inX.  discriminate inX. 
       unfold in_set in inX. fold (@in_set S) in inX.
       unfold filter. fold (@filter S).
       apply bop_or_elim in inX.
       destruct inX as [inX | inX].
       assert (H := cong _ _ inX).  rewrite gP in H. 
       rewrite <- H. unfold in_set. fold (@in_set S). rewrite inX. simpl. reflexivity.
       case_eq(g a0); intro H.
       apply in_set_cons_intro; auto. 
       apply IHX; auto.        
Qed.


Lemma in_set_uop_filter_intro :    ∀ (f : bProp S) (X : finite_set S) (a : S),(bProp_congruence S r f) -> 
          (f a = true) * (in_set r X a = true) -> in_set r (uop_filter f X) a = true. 
Proof. unfold uop_filter. apply in_set_filter_intro. Defined. 


Lemma in_set_concat_intro : ∀ (X Y : finite_set S) (a : S),
     (in_set r X a = true) + (in_set r Y a = true) → in_set r (X ++ Y) a = true. 
Proof. induction X. intros Y a [L | R]. 
             compute in L. discriminate L. 
             rewrite List.app_nil_l. exact R. 
          intros Y a0 [L | R]. 
             rewrite <- List.app_comm_cons. 
             unfold in_set. fold (@in_set S). unfold in_set in L. fold (@in_set S) in L. 
             apply bop_or_elim in L. destruct L as [L | L]. 
                rewrite L. simpl. reflexivity. 
                apply bop_or_intro. right. apply IHX. left. exact L. 

             rewrite <- List.app_comm_cons. 
             unfold in_set. fold (@in_set S). 
             apply bop_or_intro. right. apply IHX. right. exact R. 
Defined. 

Lemma in_set_concat_false_intro : ∀ (X Y : finite_set S) (a : S),
     in_set r (X ++ Y) a = false →  (in_set r X a = false) * (in_set r Y a = false). 
Proof. intros X Y a A. split.
       - case_eq(in_set r X a); intro B; auto.
         assert (C := in_set_concat_intro X Y a (inl B)).
         rewrite C in A. congruence.
       - case_eq(in_set r Y a); intro B; auto.
         assert (C := in_set_concat_intro X Y a (inr B)).
         rewrite C in A. congruence. 
Qed. 


Lemma in_set_concat_elim : ∀ (X Y : finite_set S) (a : S),
      in_set r (X ++ Y) a = true → (in_set r X a = true) + (in_set r Y a = true). 
Proof. induction X. 
          intros U a H. rewrite List.app_nil_l in H. right. exact H. 
          intros U b H. rewrite <- List.app_comm_cons in H. 
          unfold in_set in H. fold (@in_set S) in H. 
          apply bop_or_elim in H.  destruct H as [L | R]. 
             left. unfold in_set. fold (@in_set S). rewrite L. simpl. reflexivity. 
             assert (K := IHX U b R). destruct K as [KL | KR].
                left. apply in_set_cons_intro. right. exact KL. 
                right. exact KR. 
Defined. 

  
End InSet. 


