Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.     (* beq_nat *)
Require Import Coq.Lists.List. 

Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.
Require Import CAS.coq.common.data.

Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.eqv.theory.

Require Import CAS.coq.sg.and.
Require Import CAS.coq.sg.or. 

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

Definition uop_set_rep : ∀ {S : Type}, brel S -> unary_op S → unary_op (finite_set S) 
:= λ {S} eq f X,  uop_duplicate_elim eq (uop_list_map f X). 

Definition brel_subset : ∀ {S : Type},  brel S -> brel (finite_set S)
:= fix f {S} r set1 set2 := 
   match set1 with 
   | nil => true 
   | a :: rest => bop_and (in_set r set2 a) (f r rest set2)
   end.

Definition brel_set : ∀ {S : Type}, brel S → brel(finite_set S) 
:= λ {S} r,  brel_and_sym (brel_subset r). 
  

End Computation.


Close Scope nat_scope.

Section InSet.
  Variable S: Type.
  Variable r : brel S.
  Variable refS : brel_reflexive S r.
  Variable symS : brel_symmetric S r.
  Variable tranS : brel_transitive S r.


Definition list_of_set (X : finite_set S) : list S := X.

Lemma in_set_implies_in_list (s : S) (X : finite_set S) :
  in_set r X s = true -> in_list r (list_of_set X) s = true. 
Proof. auto. Qed. 
  
(****************** in_set intro and elim rules *******************)

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


(************************** in_set congruences *******************)

Lemma in_set_right_congruence : ∀ (a b : S) (X : finite_set S),
    r a b = true -> in_set r X a = true -> in_set r X b = true.
Proof. intros a b.  
       induction X; intros A B; simpl. 
       - compute in B. discriminate B.
       - apply in_set_cons_elim in B.
         apply bop_or_intro. 
         destruct B as [B | B].
         + left. apply symS. exact(tranS _ _ _ B A). 
         + right. apply IHX; auto.
Qed.

Lemma in_set_bProp_congruence : ∀ (X : finite_set S), bProp_congruence S r (in_set r X).
Proof. intros X a b E.
       case_eq(in_set r X a); intro H1; case_eq(in_set r X b); intro H2; auto. 
       rewrite (in_set_right_congruence _ _ _ E H1) in H2. discriminate H2. 
       apply symS in E. rewrite (in_set_right_congruence _ _ _ E H2) in H1. discriminate H1. 
Qed.

End InSet. 


Section Theory.

  Variable S: Type.
  Variable eq : brel S.
  Variable refS : brel_reflexive S eq.
  Variable symS : brel_symmetric S eq.
  Variable tranS : brel_transitive S eq.



Lemma brel_subset_intro : 
        ∀ (x w : finite_set S), 
          (∀ a:S, in_set eq x a = true -> in_set eq w a = true) 
               -> brel_subset eq x w = true. 
Proof. induction x; intros w H; unfold brel_subset.  
       reflexivity. 
       fold (@brel_subset S). rewrite (H a). simpl. 
       apply IHx.  intros t Q. apply H. unfold in_set. fold (@in_set S). 
          rewrite Q. apply orb_comm. unfold in_set. fold (@in_set S). 
          rewrite (refS a). simpl. reflexivity. 
Defined. 


Lemma brel_subset_elim : 
           ∀ (x w : finite_set S), 
               brel_subset eq x w = true -> 
                   ∀ a:S, in_set eq x a = true -> in_set eq w a = true. 
Proof. induction x. 
       intros w H a Q. unfold in_set in Q. discriminate. 
       intros w H a0 Q.              
       unfold brel_subset in H.  fold (@brel_subset S) in H. 
       apply bop_and_elim in H. destruct H as [H1 H2].
       unfold in_set in Q. fold (@in_set S) in Q.  
       apply bop_or_elim in Q. destruct Q as [Q|Q]. 
         apply symS in Q.  
         apply (in_set_right_congruence S eq symS tranS a a0 w Q H1).
         apply (IHx w H2 a0 Q). 
Qed. 


Lemma brel_subset_false_elim : 
           ∀ (x w : finite_set S), 
               brel_subset eq x w = false -> 
                  { a :S & (in_set eq x a = true) * (in_set eq w a = false) }. 
Proof. intros x w H.
       induction x. compute in H. discriminate H. 
       unfold brel_subset in H. fold @brel_subset in H. apply bop_and_false_elim in H.
       destruct H as [H | H]. 
          exists a. split; auto. apply in_set_cons_intro; auto. 
          destruct (IHx H) as [s [P Q]]. exists s; split; auto. apply in_set_cons_intro; auto. 
Defined.         


Lemma brel_subset_filter_intro : 
   ∀ (f g : bProp S),
       bProp_congruence S eq f →
       bProp_congruence S eq g →
      (∀ s : S, g s = true -> f s = true) -> (* <<< NB *) 
        ∀ (X Y : finite_set S), brel_subset eq X Y = true -> 
            brel_subset eq (filter g X) (filter f Y) = true. 
Proof. intros f g cong_f cong_g P X Y H.
       apply brel_subset_intro; auto. 
       assert(A := brel_subset_elim _ _ H). 
       intros a J.
       apply in_set_filter_elim in J; auto.
       destruct J as [L R].
       apply in_set_filter_intro; auto. 
Defined.


Lemma brel_subset_uop_filter_intro : 
   ∀ (f g : bProp S),
       bProp_congruence S eq f →
       bProp_congruence S eq g →
      (∀ s : S, g s = true -> f s = true) -> 
        ∀ (X Y : finite_set S), brel_subset eq X Y = true -> 
            brel_subset eq (uop_filter g X) (uop_filter f Y) = true. 
Proof. unfold uop_filter. apply brel_subset_filter_intro; auto. Defined. 
  

Lemma brel_set_nil : ∀ (X : finite_set S), brel_set eq nil X = true -> X = nil. 
Proof. induction X; intro H. reflexivity. compute in H. discriminate. Defined. 


Lemma brel_set_intro : ∀ (X Y : finite_set S), (brel_subset eq X Y = true) * (brel_subset eq Y X = true)  → brel_set eq X Y = true. 
Proof. intros X Y [H1 H2]. unfold brel_set. unfold brel_and_sym. apply bop_and_intro; auto. Defined. 

Lemma brel_set_elim : ∀ (X Y : finite_set S), 
     brel_set eq X Y = true -> (brel_subset eq X Y = true) * (brel_subset eq Y X = true).
Proof. intros X Y H. unfold brel_set in H. unfold brel_and_sym in H. 
       apply bop_and_elim in H. destruct H as [H1 H2]; auto. 
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
       apply bop_and_elim in H. destruct H as [H1 H2]. 
       assert (A1 := brel_subset_elim _ _ H1). 
       assert (A2 := brel_subset_elim _ _ H2); auto. 
Defined. 


Lemma brel_set_false_intro_prop : ∀ (X Y : finite_set S), 
        {a : S & (in_set eq X a = true) * (in_set eq Y a = false)} 
      + {a : S & (in_set eq Y a = true) * (in_set eq X a = false)}  
             -> brel_set eq X Y = false. 
Proof. intros X Y [ [a [A B]] | [a [A B]] ].
       - case_eq(brel_set eq X Y); intro C; auto.
         apply brel_set_elim_prop in C. destruct C as [C D].
         rewrite (C _ A) in B. discriminate B.
       - case_eq(brel_set eq X Y); intro C; auto.
         apply brel_set_elim_prop in C. destruct C as [C D].
         rewrite (D _ A) in B. discriminate B.          
Defined. 

Lemma brel_set_false_elim_prop : ∀ (X Y : finite_set S),
     brel_set eq X Y = false -> 
        { a : S & (in_set eq X a = true) * (in_set eq Y a = false) } 
      + { a : S & (in_set eq Y a = true) * (in_set eq X a = false) }.
Proof. intros X Y H. unfold brel_set in H. unfold brel_and_sym in H. 
       apply bop_and_false_elim in H. destruct H as [H | H].  
          apply brel_subset_false_elim in H; auto. 
          apply brel_subset_false_elim in H; auto. 
Defined. 



(************** more in_set congruences ************************) 
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

Lemma in_set_left_congruence_v3 : ∀ (a : S) (X Y : finite_set S),
    brel_set eq X Y = true -> in_set eq X a = true -> in_set eq Y a = true.
Proof. intros a X Y H1 H2. 
       apply brel_set_elim in H1.
       destruct H1 as [H1 _]. 
       assert (K := brel_subset_elim X Y H1). 
       apply K; auto. 
Qed.

Lemma in_set_left_congruence_v2 : ∀ (X Y : finite_set S),
    brel_set eq X Y = true -> ∀ (a : S), in_set eq X a = in_set eq Y a.
Proof. intros X Y H a. 
       apply brel_set_elim in H.
       destruct H as [H1 H2]. 
       assert (K1 := brel_subset_elim X Y H1).
       assert (K2 := brel_subset_elim Y X H2).        
       case_eq(in_set eq X a); intro J1; case_eq(in_set eq Y a); intro J2; auto.
       apply K1 in J1. rewrite J1 in J2. exact J2.
       apply K2 in J2. rewrite J1 in J2. exact J2.       
Qed.



Lemma in_set_congruence : ∀ (a b : S) (X Y : finite_set S),
    brel_set eq X Y = true -> eq a b = true -> in_set eq X a = in_set eq Y b.
Proof. intros a b X Y H1 H2.
       assert (J1 := in_set_right_congruence S eq symS tranS _ _ X H2).
       apply symS in H2. assert (J2 := in_set_right_congruence S eq symS tranS _ _ Y H2).        
       assert (Ma := in_set_left_congruence_v2 X Y H1 a).       
       assert (Mb := in_set_left_congruence_v2 X Y H1 b).
       case_eq(in_set eq X a); intro K1; case_eq(in_set eq Y b); intro K2; auto.
       rewrite (J1 K1) in Mb. rewrite <- Mb in K2. exact K2.
       rewrite (J2 K2) in Ma. rewrite K1 in Ma. exact Ma.
Qed. 




(***     brel_set eqv properties   ****)

(* move and_sym lemmas? *)
Lemma brel_and_sym_relexive (T : Type) (r : brel T) (refr : brel_reflexive T r) : brel_reflexive T (brel_and_sym r). 
Proof. unfold brel_reflexive, brel_and_sym. intros s. 
       rewrite (refr s). simpl. reflexivity. 
Defined. 

Lemma brel_and_sym_transitive (T : Type) (r : brel T) (tranr : brel_transitive T r) : brel_transitive T (brel_and_sym r). 
Proof. unfold brel_transitive, brel_and_sym. intros s t u H1 H2. 
       apply bop_and_elim in H1. destruct H1 as [H1_l H1_r].        
       apply bop_and_elim in H2. destruct H2 as [H2_l H2_r].        
       rewrite (tranr _ _ _ H1_l H2_l).
       rewrite (tranr _ _ _ H2_r H1_r ). simpl. reflexivity. 
Defined. 

Lemma brel_and_sym_symmetric (T : Type) (r : brel T) : brel_symmetric T (brel_and_sym r). 
Proof. unfold brel_symmetric, brel_and_sym. intros s t H. 
       apply bop_and_elim in H. destruct H as [H_l H_r].        
       rewrite H_l. rewrite H_r. simpl. reflexivity. 
Defined. 




(***)

Lemma brel_subset_reflexive : brel_reflexive (finite_set S) (brel_subset eq). 
Proof. unfold brel_reflexive. induction s. 
       simpl. reflexivity. 
       unfold brel_subset. fold (@brel_subset S). unfold in_set. rewrite (refS a). simpl.
       apply brel_subset_intro; auto.   
       intros b H. apply in_set_cons_intro; auto. 
Defined. 

Lemma brel_subset_transitive : brel_transitive (finite_set S) (brel_subset eq). 
Proof. intros x y z H1 H2. 
      assert (Q1 := brel_subset_elim x y H1). 
      assert (Q2 := brel_subset_elim y z H2). 
      apply brel_subset_intro. 
      intros a I. apply Q2. apply Q1. assumption. 
Defined. 


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

Lemma brel_set_at_least_three (s : S) (f : S -> S):
  brel_not_trivial S eq f -> 
  brel_at_least_three (finite_set S) (brel_set eq).
Proof. intro nt. 
       exists (nil, (s :: nil, (f s) :: nil)).
       destruct (nt s) as [L R].
       compute. rewrite L; auto. 
Defined. 


Lemma brel_set_not_exactly_two (s : S) (f : S -> S):
  brel_not_trivial S eq f -> 
  brel_not_exactly_two (finite_set S) (brel_set eq).
Proof. intro nt. apply brel_at_least_thee_implies_not_exactly_two.
       apply brel_set_symmetric; auto. 
       apply brel_set_transitive; auto.
       apply (brel_set_at_least_three s f); auto. 
Defined.

Definition power_set : finite_set S -> finite_set (finite_set S)
:= fix f X := 
      match X with
         | nil => nil :: nil 
         | t :: Y => (f Y) ++ (List.map (λ Z, t :: Z) (f Y))
      end.

Definition powerset_enum (fS : unit -> list S) (x : unit) :=  power_set (fS x).

Lemma empty_set_in_powerset (X : finite_set S) : in_set (brel_set eq) (power_set X) nil = true.
Admitted.

Lemma  in_powerset_intro (a : S) (X Y : finite_set S) (H : in_set (brel_set eq) (power_set Y) X = true) (K : in_set eq Y a = true) : 
                          in_set (brel_set eq) (power_set Y) (a :: X) = true.
Admitted.   


Lemma brel_set_finite : carrier_is_finite S eq -> carrier_is_finite (finite_set S) (brel_set eq).
Proof. intros [fS pS]. unfold carrier_is_finite. exists (powerset_enum fS).
       intro X. unfold powerset_enum.
       induction X.
          apply empty_set_in_powerset. 
          assert (K := pS a).  apply in_powerset_intro; auto. 
Defined. 

Lemma brel_set_not_finite : carrier_is_not_finite S eq -> carrier_is_not_finite (finite_set S) (brel_set eq).
Proof. unfold carrier_is_not_finite. intros H f.
Admitted.

Definition brel_set_finite_decidable (d : carrier_is_finite_decidable S eq) : carrier_is_finite_decidable (finite_set S) (brel_set eq)
  := match d with
     | inl fS  => inl (brel_set_finite fS)
     | inr nfS => inr (brel_set_not_finite nfS)                       
     end.

Lemma brel_subset_congruence : brel_congruence (finite_set S) (brel_set eq) (brel_subset eq).
Proof. unfold brel_congruence. intros X Y V W A B.
       apply brel_set_elim in A. destruct A as [A1 A2].
       apply brel_set_elim in B. destruct B as [B1 B2].        
       case_eq(brel_subset eq X Y); intro C; case_eq(brel_subset eq V W); intro D. 
       + reflexivity. 
       + assert (E : brel_subset eq V W = true).
            assert (F := brel_subset_transitive _ _ _ A2 C).
            exact (brel_subset_transitive _ _ _ F B1).              
         rewrite E in D. discriminate D. 
       + assert (E : brel_subset eq X Y = true).
            assert (F := brel_subset_transitive _ _ _ A1 D).
            exact (brel_subset_transitive _ _ _ F B2).              
         rewrite E in C. discriminate C. 
       + reflexivity. 
Qed. 

End Theory.




Section ACAS.


Definition eqv_proofs_set : ∀ (S : Type) (eq : brel S),
    eqv_proofs S eq → eqv_proofs (finite_set S) (brel_set eq) 
:= λ S eq eqv, 
   {| 
     A_eqv_congruence  := brel_set_congruence S eq (A_eqv_reflexive S eq eqv) (A_eqv_symmetric S eq eqv) (A_eqv_transitive S eq eqv) 
   ; A_eqv_reflexive   := brel_set_reflexive S eq (A_eqv_reflexive S eq eqv) (A_eqv_symmetric S eq eqv) 
   ; A_eqv_transitive  := brel_set_transitive S eq (A_eqv_reflexive S eq eqv) (A_eqv_symmetric S eq eqv) (A_eqv_transitive S eq eqv) 
   ; A_eqv_symmetric   := brel_set_symmetric S eq
   |}. 

Definition set_new {S : Type} (eq : brel S) (s : S) (l : finite_set S) :=
  if brel_set eq nil l then (s :: nil) else nil.

Definition set_witness {S : Type} (s : S) := s :: nil. 

Definition A_eqv_set : ∀ (S : Type),  A_eqv S -> A_eqv (finite_set S)
:= λ S eqvS,
  let eq := A_eqv_eq S eqvS in
  let s  := A_eqv_witness S eqvS in
  let f  := A_eqv_new S eqvS in
  let nt := A_eqv_not_trivial S eqvS in
  let eqP := A_eqv_proofs S eqvS in
  let refS := A_eqv_reflexive S eq eqP in
  let symS := A_eqv_symmetric S eq eqP in
  let trnS := A_eqv_transitive S eq eqP in   
   {| 
      A_eqv_eq     := brel_set eq 
    ; A_eqv_proofs := eqv_proofs_set S eq eqP 
    ; A_eqv_witness := set_witness s 
    ; A_eqv_new    := set_new eq s 
    ; A_eqv_not_trivial := brel_set_not_trivial S eq s 
    ; A_eqv_exactly_two_d := inr (brel_set_not_exactly_two S eq refS symS trnS s f nt)                              
    ; A_eqv_data   := λ d, DATA_set (List.map (A_eqv_data S eqvS) d)  
    ; A_eqv_rep    := λ d, d  (* fix this someday ... *)
    ; A_eqv_finite_d  := brel_set_finite_decidable S eq refS symS trnS (A_eqv_finite_d S eqvS)
    ; A_eqv_ast    := Ast_eqv_set (A_eqv_ast S eqvS)
   |}. 

End ACAS.

Section CAS.

Definition brel_set_finite_checkable {S : Type} (d : @check_is_finite S) : @check_is_finite (finite_set S)
  := match d with
     | Certify_Is_Finite fS  => Certify_Is_Finite (powerset_enum S fS)
     | Certify_Is_Not_Finite => Certify_Is_Not_Finite
     end.
  

Definition eqv_set : ∀ {S : Type},  @eqv S -> @eqv (finite_set S)
:= λ {S} eqvS,
  let eq := eqv_eq eqvS in
  let s := eqv_witness eqvS in
  let f := eqv_new eqvS in   
 {| 
      eqv_eq       := brel_set eq 
    ; eqv_certs := 
     {|
       eqv_congruence     := @Assert_Brel_Congruence (finite_set S)
     ; eqv_reflexive      := @Assert_Reflexive (finite_set S)
     ; eqv_transitive     := @Assert_Transitive (finite_set S)
     ; eqv_symmetric      := @Assert_Symmetric (finite_set S)
     |}  
    ; eqv_witness := set_witness s 
    ; eqv_new     := set_new eq s 
    ; eqv_exactly_two_d := Certify_Not_Exactly_Two (not_ex2 (brel_set eq) nil (s :: nil)  ((f s):: nil))
    ; eqv_data    := λ d, DATA_set (List.map (eqv_data eqvS) d)  
    ; eqv_rep     := λ d, d  (* fix this? *)
    ; eqv_finite_d  := brel_set_finite_checkable (eqv_finite_d eqvS)
    ; eqv_ast     := Ast_eqv_set (eqv_ast eqvS)
   |}. 

End CAS.


Section MCAS.

Definition mcas_eqv_set {S : Type} (A : @mcas_eqv S) : @mcas_eqv (finite_set S) :=
match A with
| EQV_eqv B    => EQV_eqv (eqv_set B)
| EQV_Error sl => EQV_Error sl
end.                  

End MCAS.


Section Verify.


Theorem correct_eqv_set : ∀ (S : Type) (E : A_eqv S),  
    eqv_set (A2C_eqv S E) = A2C_eqv (finite_set S) (A_eqv_set S E).
Proof. intros S E. 
       unfold eqv_set, A_eqv_set, A2C_eqv; simpl.
       destruct E; simpl.  unfold brel_set_finite_checkable, brel_set_finite_decidable. 
       destruct A_eqv_finite_d; auto.
       destruct c as [fS PS]. simpl. unfold brel_set_finite. 
       reflexivity.
Qed.        

  
 
End Verify.   
  
