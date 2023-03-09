Require Import Coq.Strings.String.

Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.

Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.eqv.theory.
Require Import CAS.coq.eqv.sum.

Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures.
Require Import CAS.coq.sg.theory.
Require Import CAS.coq.sg.cast_up.
Require Import CAS.coq.sg.classify. 

Section Computation.

Definition bop_left_sum : ∀ {S T : Type}, binary_op S → binary_op T → binary_op (S + T)
:= λ {S T }opS opT x y,  
      match x, y with
         | (inl a), (inl b) => inl _ (opS a b)
         | (inl _), (inr _) => x
         | (inr _), (inl _) => y
         | (inr a), (inr b) => inr _ (opT a b)
      end.

End Computation.   

Section Theory.


  Variable S T : Type.
  Variable rS : brel S.
  Variable rT : brel T.
  Variable bS : binary_op S.
  Variable bT: binary_op T.    

  Variable wS : S.
  Variable f : S -> S.                
  Variable Pf : brel_not_trivial S rS f. 

  Variable refS : brel_reflexive S rS.
  Variable symS : brel_symmetric S rS.  
  Variable tranS : brel_transitive S rS.

  Variable wT : T.
  Variable g : T -> T.                
  Variable Pg : brel_not_trivial T rT g. 
  
  Variable refT : brel_reflexive T rT.
  Variable symT : brel_symmetric T rT.  
  Variable tranT : brel_transitive T rT.
  
  Variable congS : bop_congruence S rS bS.
  Variable assS : bop_associative S rS bS.

  Variable congT : bop_congruence T rT bT.  
  Variable assT : bop_associative T rT bT. 

  Notation "a <+> b"  := (brel_sum a b)                (at level 15).
  Notation "a [+] b"  := (bop_left_sum a b)            (at level 15).  
  Notation "a == b"   := (brel_sum rS rT a b = true)  (at level 15).  
  
Lemma bop_left_sum_congruence : bop_congruence (S + T) (rS <+> rT) (bS [+] bT). 
Proof. 
   unfold bop_congruence. intros [s1 | t1] [s2 | t2] [s3 | t3] [s4 | t4]; simpl.
   apply congS. 
   intros. discriminate. 
   intros. discriminate. 
   intros. discriminate. 
   intros. discriminate. 
   intros. assumption. 
   intros. discriminate. 
   intros. discriminate. 
   intros. discriminate. 
   intros. discriminate. 
   intros. assumption. 
   intros. discriminate. 
   intros. discriminate. 
   intros. discriminate. 
   intros. discriminate. 
   apply congT. 
Qed. 


Lemma bop_left_sum_associative : bop_associative (S + T) (rS <+> rT) (bS [+] bT). 
Proof. intros [s1 | t1] [s2 | t2] [s3 | t3]; simpl.
      apply assS. apply refS. apply refS. apply refS. apply refS. apply refS. apply refS. apply assT. 
Qed. 

Lemma bop_left_sum_idempotent : bop_idempotent S rS bS → bop_idempotent T rT bT → bop_idempotent (S + T) (rS <+> rT) (bS [+] bT). 
Proof. intros L R d.  destruct d; simpl. apply L. apply R. Qed. 

Lemma bop_left_sum_not_idempotent_left : bop_not_idempotent S rS bS → bop_not_idempotent (S + T) (rS <+> rT) (bS [+] bT). 
Proof. intros [s P]. exists (inl _ s). simpl. assumption. Defined. 

Lemma bop_left_sum_not_idempotent_right : bop_not_idempotent T rT bT → bop_not_idempotent (S + T) (rS <+> rT) (bS [+] bT). 
Proof. intros [t P]. exists (inr _ t). simpl. assumption. Defined. 

Lemma bop_left_sum_idempotent_comp : 
      (bop_not_idempotent S rS bS) + (bop_not_idempotent T rT bT) → bop_not_idempotent (S + T) (rS <+> rT) (bS [+] bT). 
Proof. intros [L | R].  apply (bop_left_sum_not_idempotent_left L). apply (bop_left_sum_not_idempotent_right R). Defined. 

Lemma bop_left_sum_commutative : 
      bop_commutative S rS bS → bop_commutative T rT bT → bop_commutative (S + T) (rS <+> rT) (bS [+] bT). 
Proof. intros L R [s1 | t1] [s2 | t2]; simpl. apply L. apply refS. apply refS. apply R. Qed. 

Lemma bop_left_sum_not_commutative_left : bop_not_commutative S rS bS → bop_not_commutative (S + T) (rS <+> rT) (bS [+] bT). 
Proof. intros [ [s t] P]. exists (inl _ s, inl _ t). simpl. exact P. Defined. 

Lemma bop_left_sum_not_commutative_right : bop_not_commutative T rT bT → bop_not_commutative (S + T) (rS <+> rT) (bS [+] bT). 
Proof. intros [ [s t] P]. exists (inr _ s, inr _ t). simpl. exact P. Defined. 

Lemma bop_left_sum_not_commutative : (bop_not_commutative S rS bS) + (bop_not_commutative T rT bT) → 
          bop_not_commutative (S + T) (rS <+> rT) (bS [+] bT). 
Proof. intros [L | R]. apply (bop_left_sum_not_commutative_left L). apply (bop_left_sum_not_commutative_right R). Defined. 

Lemma bop_left_sum_selective : bop_selective S rS bS → bop_selective T rT bT → bop_selective (S + T) (rS <+> rT) (bS [+] bT). 
Proof. intros L R [s1 | t1] [s2 | t2]; simpl. apply L. left. apply refS. right. apply refS. apply R. Defined. 

Lemma bop_left_sum_not_selective_left : bop_not_selective S rS bS → bop_not_selective (S + T) (rS <+> rT) (bS [+] bT). 
Proof.  intros [ [s1 s2] P]. exists (inl _ s1, inl _ s2). simpl. exact P. Defined. 

Lemma bop_left_sum_not_selective_right : bop_not_selective T rT bT → bop_not_selective (S + T) (rS <+> rT) (bS [+] bT). 
Proof. intros [ [t1 t2] P]. exists (inr _ t1, inr _ t2). simpl. exact P. Defined. 

Lemma bop_left_sum_not_selective : 
      (bop_not_selective S rS bS) + (bop_not_selective T rT bT) → bop_not_selective (S + T) (rS <+> rT) (bS [+] bT). 
Proof. intros [L | R]. apply (bop_left_sum_not_selective_left L). apply (bop_left_sum_not_selective_right R). Defined. 

Lemma bop_left_sum_not_is_left (s : S) (t : T) : bop_not_is_left (S + T) (rS <+> rT) (bS [+] bT). 
Proof. exists (inr _ t, inl _ s). simpl. reflexivity. Defined. 

Lemma bop_left_sum_not_is_right (s : S) (t : T) : bop_not_is_right (S + T) (rS <+> rT) (bS [+] bT). 
Proof. exists (inl _ s, inr _ t). simpl. reflexivity. Defined. 


Lemma bop_left_sum_is_id : ∀ i: T, bop_is_id T rT bT i -> bop_is_id (S + T) (rS <+> rT) (bS [+] bT) (inr _ i).
Proof. intros i pT [s | t]; compute. rewrite (refS s). split; reflexivity. apply (pT t). Defined. 

Lemma bop_left_sum_exists_id : (bop_exists_id T rT bT) -> bop_exists_id (S + T) (rS <+> rT) (bS [+] bT).
Proof. intros [i pT]. exists (inr _ i). apply bop_left_sum_is_id; auto. Defined. 

Lemma bop_left_sum_id_is_inr : ∀ i : S + T, (bop_is_id _ (rS <+> rT) (bS [+] bT) i) ->
                                            ∀ idT : T, bop_is_id _ rT bT idT -> i == (inr idT).
Proof. intros [s | t] P idT Q.
       assert (F := P (inr idT)). compute in F. destruct F as [F _]. discriminate F.
       compute. assert (C : bop_is_id _ rT bT t). intro t2. assert (F := P (inr t2)). compute in F. exact F.
       apply (bop_is_id_equal _ rT symT tranT bT t idT C Q). 
Qed.

Lemma bop_left_sum_simplify_id : ∀ t : T, 
    bop_is_id (S + T) (rS <+> rT) (bS [+] bT) (inr t) -> bop_is_id T rT bT t.
Proof. intros t H. intro t'. apply (H (inr t')). Qed .   

Lemma bop_left_sum_extract_id (t' : T) : ∀ i : S + T, 
    bop_is_id (S + T) (rS <+> rT) (bS [+] bT) i ->
       {t : T & (bop_is_id T rT bT t) * (i == (inr t)) }.
Proof. intros [s1 | t1] H; simpl.
       assert (F := H (inr t')). compute in F. destruct F as [F _]. discriminate F. 
       exists t1. split. apply bop_left_sum_simplify_id. exact H. apply refT.
Qed.        

Lemma bop_left_sum_not_exists_id : (bop_not_exists_id T rT bT) -> bop_not_exists_id (S + T) (rS <+> rT) (bS [+] bT).
Proof. intros pT [s | t]. exists (inr _ wT). compute. auto. destruct (pT t) as [x D]. exists (inr _ x). compute. exact D. Defined. 


Lemma bop_left_sum_is_ann : ∀ a : S, bop_is_ann S rS bS a -> bop_is_ann (S + T) (rS <+> rT) (bS [+] bT) (inl _ a).
Proof. intros a pS [s | t]; compute. apply (pS s). rewrite (refS a). split; reflexivity. Defined. 

Lemma bop_left_sum_exists_ann : (bop_exists_ann S rS bS) -> bop_exists_ann (S + T) (rS <+> rT) (bS [+] bT).
Proof. intros [a pS]. exists (inl _ a). apply bop_left_sum_is_ann; auto. Defined. 

Lemma bop_left_sum_ann_is_inl : ∀ i : S + T, (bop_is_ann _ (rS <+> rT) (bS [+] bT) i) ->
                                        ∀ annS : S, bop_is_ann _ rS bS annS -> i == (inl annS).
Proof. intros [s | t] P annS Q; compute. 
       assert (C : bop_is_ann _ rS bS s). intro s2. assert (F := P (inl s2)). compute in F. exact F.
       apply (bop_is_ann_equal _ rS symS tranS bS s annS C Q).
       assert (F := P (inl annS)). compute in F. destruct F as [F _]. discriminate F.       
Qed.

Lemma bop_left_sum_simplify_ann : ∀ s : S, 
    bop_is_ann (S + T) (rS <+> rT) (bS [+] bT) (inl s) -> bop_is_ann S rS bS s.
Proof. intros s H. intro s'. apply (H (inl s')). Qed .

Lemma bop_left_sum_extract_ann (s' : S) : ∀ i : S + T, 
    bop_is_ann (S + T) (rS <+> rT) (bS [+] bT) i ->
       {s : S & (bop_is_ann S rS bS s) * (brel_sum rS rT i (inl s) = true) }.
Proof. intros [s1 | t1] H; simpl.
       exists s1. split. apply bop_left_sum_simplify_ann. exact H. apply refS.       
       assert (F := H (inl s')). compute in F. destruct F as [F _]. discriminate F. 
Qed.        

Lemma bop_left_sum_not_exists_ann : (bop_not_exists_ann S rS bS) -> bop_not_exists_ann (S + T) (rS <+> rT) (bS [+] bT).
Proof. intros pS [s | t]. 
       destruct (pS s) as [x D].  exists (inl _ x). compute. exact D. 
       exists (inl _ wS). compute; auto.  
Defined. 

Lemma bop_left_sum_not_left_cancellative : bop_not_left_cancellative (S + T) (rS <+> rT) (bS [+] bT). 
Proof.  exists ((inl _ wS), ((inr wT), (inr (g wT)))). simpl. split. apply (refS wS).
        destruct (Pg wT) as [L _]. exact L. 
Defined. 

Lemma bop_left_sum_not_right_cancellative : bop_not_right_cancellative (S + T) (rS <+> rT) (bS [+] bT). 
Proof. exists ((inl _ wS), ((inr wT), (inr (g wT)))). simpl.  split. apply (refS wS).
        destruct (Pg wT) as [L _]. exact L. 
Defined. 

Lemma bop_left_sum_not_left_constant : bop_not_left_constant (S + T) (rS <+> rT) (bS [+] bT). 
Proof.   exists (inr wT, (inl wS, inl (f wS))). simpl.  destruct (Pf wS) as [L _]. exact L. 
Defined. 

Lemma bop_left_sum_not_right_constant : bop_not_right_constant (S + T) (rS <+> rT) (bS [+] bT). 
Proof.   exists (inr wT, (inl wS, inl (f wS))). simpl. destruct (Pf wS) as [L _]. exact L. 
Defined. 

Lemma bop_left_sum_not_anti_left : bop_not_anti_left (S + T) (rS <+> rT) (bS [+] bT). 
Proof. exists (inl wS, inr wT); simpl. apply refS. Defined. 

Lemma bop_left_sum_not_anti_right : bop_not_anti_right (S + T) (rS <+> rT) (bS [+] bT).
Proof. exists (inl wS, inr wT); simpl. apply refS. Defined.


(* bottoms *) 

(*
Definition bop_left_sum_BOTTOMS (B : list S) : list (S + T) :=
  List.map (λ d, inl d) B.

Definition bop_left_sum_w (B : list S) (w : S -> S) (d : S + T) : S + T :=
  match d with
  | inl s => inl (w s) 
  | inr _ => if in_set rS B wS then inl wS else inl (w wS) 
  end.
    
Lemma bop_left_sum_BOTTOMS_cons (a : S) (B : list S) : bop_left_sum_BOTTOMS (a :: B) = (inl a) :: (bop_left_sum_BOTTOMS B).
Proof. compute. reflexivity. Qed. 
  
Lemma bop_left_sum_BOTTOMS_inr (t : T) (B : list S) : 
  in_set (rS <+> rT) (bop_left_sum_BOTTOMS B) (inr t) = false.
Proof. induction B. 
       compute. reflexivity.
       rewrite bop_left_sum_BOTTOMS_cons.
       case_eq(in_set (rS <+> rT) (inl a :: bop_left_sum_BOTTOMS B) (inr t)); intro C; auto. 
          apply in_set_cons_elim in C. 
          destruct C as [C | C].
             compute in C. discriminate C. 
             rewrite IHB in C. discriminate C.
          apply brel_sum_symmetric; auto. 
Qed.

Lemma bop_left_sum_BOTTONS_inl (B : list S) (s : S) (H : in_set rS B s = true) :
       in_set (rS <+> rT) (bop_left_sum_BOTTOMS B) (inl s) = true. 
Proof. induction B.
       compute in H. discriminate H.
       rewrite bop_left_sum_BOTTOMS_cons.
       apply in_set_cons_intro. 
       apply brel_sum_symmetric; auto.
       apply in_set_cons_elim in H; auto.
       destruct H as [H | H]. 
          left. compute. exact H. 
          right. apply IHB; auto. 
Qed.

Lemma in_set_left_sum_BOTTOMS (B : list S) (s : S):
  in_set (rS <+> rT) (bop_left_sum_BOTTOMS B) (inl s) = true -> in_set rS B s = true. 
Proof. intro A. induction B. 
       compute in A. discriminate A.
       apply in_set_cons_intro; auto.
       rewrite bop_left_sum_BOTTOMS_cons in A.
       apply in_set_cons_elim in A. 
       destruct A as [A | A]. 
          compute in A. left. exact A. 
          right. exact (IHB A). 
       apply brel_sum_symmetric; auto. 
Qed.

Lemma bop_left_sum_is_interesting (B : list S) : 
  is_interesting S rS bS B ->
       is_interesting (S + T) (rS <+> rT) (bS [+] bT) (bop_left_sum_BOTTOMS B).
Proof. unfold is_interesting. intros I s A t C.
       destruct s as [s | s]; destruct t as [t | t].
          assert (A' := in_set_left_sum_BOTTOMS _ _ A).
          assert (C' := in_set_left_sum_BOTTOMS _ _ C).           
          destruct (I s A' t C') as [[D E] | [D E]].
             left. split. 
                compute. exact D. 
                compute. exact E. 
                
             right. split. 
                compute. exact D. 
                compute. exact E. 
          assert (D := bop_left_sum_BOTTOMS_inr t B). rewrite D in C. discriminate C. 
          assert (D := bop_left_sum_BOTTOMS_inr s B). rewrite D in A. discriminate A. 
          assert (D := bop_left_sum_BOTTOMS_inr t B). rewrite D in C. discriminate C. 
Qed. 


(* note: commutativity and idempotence not needed *) 
Lemma bop_left_sum_something_is_finite
      (sif : something_is_finite S rS bS) : something_is_finite (S + T) (rS <+> rT) (bS [+] bT).
Proof. destruct sif as [[BOTTOMS w] [A B]].
       unfold something_is_finite.
       exists (bop_left_sum_BOTTOMS BOTTOMS, bop_left_sum_w BOTTOMS w). split. 
          apply bop_left_sum_is_interesting; auto. 
          intros [s | s]; unfold bop_left_sum_w.
          destruct (B s) as [C | [C [D E]]]. 
             left. apply bop_left_sum_BOTTONS_inl; auto. 
             right. split. 
                apply bop_left_sum_BOTTONS_inl; auto. 
                split. 
                   compute. exact D. 
                   compute. exact E. 
          right. split. 
             destruct (B wS) as [C | [C [D E]]].           
                rewrite C. apply bop_left_sum_BOTTONS_inl; auto. 
                 case_eq(in_set rS BOTTOMS wS); intro F. 
                    apply bop_left_sum_BOTTONS_inl; auto.                    
                    apply bop_left_sum_BOTTONS_inl; auto.                                        
              split. 
                 case_eq(in_set rS BOTTOMS wS); intro C. 
                    compute. apply refS. 
                    compute. apply refS. 
                 case_eq(in_set rS BOTTOMS wS); intro C. 
                    compute. reflexivity. 
                    compute. reflexivity. 
Defined. 



Fixpoint strip_all_inl (carry : list S) (B : finite_set (S + T)) : list S :=
  match B with
  | nil => carry
  | (inr _) :: rest => strip_all_inl carry rest
  | (inl a) :: rest => strip_all_inl (a :: carry) rest
  end.

Definition bop_left_sum_not_BOTTOMS (F : list S → S) (B : finite_set (S + T)) : S + T :=
     inl (F (strip_all_inl nil B)). 

(*
Lemma bop_left_sum_not_BOTTOMS_is_not_inl (F : list S → S) (B : list (with_constant S)) (s : cas_constant) : 
  (brel_sum rS rT (inl s) ((c [+] bS) (inl s) (bop_left_sum_not_BOTTOMS F B)) = false).
Proof. compute. reflexivity. Qed.
*) 

Lemma in_set_strip_all_inl_aux (B : finite_set (S + T)): 
∀ (l : list S) (s : S), 
  ((in_set rS (strip_all_inl l B) s = true) -> (in_set rS l s = true) + (in_set (rS <+> rT) B (inl s) = true))
  *
  ((in_set rS (strip_all_inl l B) s = false) -> (in_set rS l s = false) * (in_set (rS <+> rT) B (inl s) = false)).
Proof. induction B. 
       intros l s. unfold strip_all_inl. split; intro H. 
          left. exact H.        
          split. 
             exact H. 
             compute. reflexivity. 

        destruct a as [a | a]. 
           unfold strip_all_inl. fold strip_all_inl.         
           intros l s; split; intro H. 
              destruct (IHB (a :: l) s) as [C D]. 
              destruct (C H) as [E | E]. 
                 apply in_set_cons_elim in E; auto. 
                 destruct E as [E | E]. 
                    right. unfold in_set.
                    fold (in_set (rS <+> rT) B (inl s)).
                    compute. rewrite (symS _ _ E). reflexivity. 
                    left. exact E. 
                 right. apply in_set_cons_intro; auto. 
                 apply brel_sum_symmetric; auto.
                 destruct (IHB (a :: l) s) as [C D].
                 destruct (D H) as [E F]. split. 
                 apply not_in_set_cons_elim in E; auto.
                 destruct E as [_ E]. exact E. 
                 case_eq(in_set (rS <+> rT) (inl a :: B) (inl s)); intro G; auto. 
                    apply in_set_cons_elim in G; auto. 
                    destruct G as [G | G]. 
                       compute in G. 
                       apply not_in_set_cons_elim in E; auto.
                       destruct E as [E _]. rewrite G in E. discriminate E. 
                       rewrite G in F. discriminate F. 
                    apply brel_sum_symmetric; auto.

           unfold strip_all_inl. fold strip_all_inl. 
           intros l s. destruct (IHB l s) as [C D]. split; intros H. 
              destruct (C H) as [E | E].                        
                 left. exact E. 
                 right. apply in_set_cons_intro; auto. 
                 apply brel_sum_symmetric; auto.
              destruct (D H) as [E F]. split.                                      
                 exact E. 
                 case_eq(in_set (rS <+> rT) (inr a :: B) (inl s)); intro G; auto. 
                    apply in_set_cons_elim in G. 
                    destruct G as [G | G]. 
                       compute in G. discriminate G.
                       rewrite F in G. discriminate G.
                    apply brel_sum_symmetric; auto.
Qed. 


(* this could be a nice student exercise.  Just give def of strip_all_inl and have
   them prove the following.  This requires generalizing to something like 
   in_set_strip_all_inl_aux.  However, setting up in_set_strip_all_inl_aux properly 
   in order to make the proof go through is 
   a bit tricky.  Students may try double induction, which does not seem to work.
   And the quantifiers have to be in the right order, (forall B, forall l, ....  see above).  
*) 
Lemma in_set_strip_all_inl (B : finite_set (S + T)) (s : S) : 
      in_set rS (strip_all_inl nil B) s = true -> in_set (rS <+> rT) B (inl s) = true.
Proof. intro H. destruct (in_set_strip_all_inl_aux B nil s) as [A _].
       destruct (A H) as [C | C]. 
          compute in C. discriminate C. 
          exact C. 
Qed.

Lemma bop_left_sum_is_interesting_right (B : finite_set (S + T)) : 
  is_interesting (S + T) (rS <+> rT) (bS [+] bT) B -> is_interesting S rS bS (strip_all_inl nil B). 
Proof. unfold is_interesting. intros A s C t D.
       assert (E : in_set (rS <+> rT) B (inl s) = true). apply in_set_strip_all_inl; auto. 
       assert (G : in_set (rS <+> rT) B (inl t) = true). apply in_set_strip_all_inl; auto. 
       destruct(A _ E _ G) as [[H1 H2] | [H1 H2]]; compute in H1, H2.
          left; auto. right; auto. 
Qed. 

(* note: commutativity and idempotence not needed *) 
Lemma bop_left_sum_something_not_is_finite
      (sif : something_not_is_finite S rS bS) : something_not_is_finite (S + T) (rS <+> rT) (bS [+] bT).
Proof. unfold something_not_is_finite. unfold something_not_is_finite in sif. 
       destruct sif as [F A].
       exists (bop_left_sum_not_BOTTOMS F).
       intros B C. 
       assert (D := bop_left_sum_is_interesting_right B C).
       destruct (A _ D) as [E G]. 
       split.
          unfold bop_left_sum_not_BOTTOMS.           
          destruct (in_set_strip_all_inl_aux B nil (F (strip_all_inl nil B))) as [_ K].
          destruct (K E) as [_ J]. 
          exact J. 

          intros [s | s] H.
             assert (J: in_set rS (strip_all_inl nil B) s = true). 
                case_eq(in_set rS (strip_all_inl nil B) s); intro K; auto.
                   destruct (in_set_strip_all_inl_aux B nil s) as [_ R].
                   destruct (R K) as [_ M]. rewrite M in H. discriminate H. 
             destruct (G s J) as [K | K].
                left. unfold bop_left_sum_not_BOTTOMS, brel_sum, bop_left_sum. exact K. 
                   
               right.  unfold bop_left_sum_not_BOTTOMS, brel_sum, bop_left_sum. exact K. 

             left. compute. reflexivity. 
Defined. 
*) 

(* decide *) 

Definition bop_left_sum_idempotent_decide : 
     bop_idempotent_decidable S rS bS  → bop_idempotent_decidable T rT bT  → 
         bop_idempotent_decidable (S + T) (rS <+> rT) (bS [+] bT)
:= λ dS dT,  
   match dS with 
   | inl commS => 
     match dT with 
     | inl commT     => inl _ (bop_left_sum_idempotent commS commT)
     | inr not_commT => inr _ (bop_left_sum_not_idempotent_right not_commT)
     end 
   | inr not_commS   => inr _ (bop_left_sum_not_idempotent_left not_commS)
   end. 

Definition bop_left_sum_commutative_decide : 
     bop_commutative_decidable S rS bS  → bop_commutative_decidable T rT bT  → 
        bop_commutative_decidable (S + T) (rS <+> rT) (bS [+] bT)
:= λ dS dT,  
   match dS with 
   | inl commS => 
     match dT with 
     | inl commT     => inl _ (bop_left_sum_commutative commS commT)
     | inr not_commT => inr _ (bop_left_sum_not_commutative_right not_commT)
     end 
   | inr not_commS   => inr _ (bop_left_sum_not_commutative_left not_commS)
   end. 

Definition bop_left_sum_selective_decide : 
     bop_selective_decidable S rS bS  → bop_selective_decidable T rT bT  → 
        bop_selective_decidable (S + T) (rS <+> rT) (bS [+] bT)
:= λ dS dT,  
   match dS with 
   | inl selS => 
     match dT with 
     | inl selT     => inl _ (bop_left_sum_selective selS selT)
     | inr not_selT => inr _ (bop_left_sum_not_selective_right not_selT)
     end 
   | inr not_selS   => inr _ (bop_left_sum_not_selective_left not_selS)
   end. 

Definition bop_left_sum_exists_id_decide : bop_exists_id_decidable T rT bT  → bop_exists_id_decidable (S + T) (rS <+> rT) (bS [+] bT)
:= λ dT,  
   match dT with 
   | inl eid  => inl _ (bop_left_sum_exists_id eid)
   | inr neid => inr _ (bop_left_sum_not_exists_id neid)
   end. 


Definition bop_left_sum_exists_ann_decide : bop_exists_ann_decidable S rS bS  → bop_exists_ann_decidable (S + T) (rS <+> rT) (bS [+] bT)
:= λ dS,     
   match dS with 
   | inl eann  => inl _ (bop_left_sum_exists_ann eann)
   | inr neann => inr _ (bop_left_sum_not_exists_ann neann)
   end. 

End Theory.

Section ACAS.

  
Definition sg_proofs_left_sum : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T) (s : S) (f : S -> S) (t : T) (g : T -> T), 
     brel_not_trivial S rS f -> brel_not_trivial T rT g -> 
     eqv_proofs S rS -> eqv_proofs T rT -> sg_proofs S rS bS -> sg_proofs T rT bT -> 
        sg_proofs (S + T) (brel_sum rS rT) (bop_left_sum bS bT)
:= λ S T rS rT bS bT s f t g Pf Pg eqvS eqvT sgS sgT, 
let refS := A_eqv_reflexive _ _ eqvS in 
{|
  A_sg_associative   := bop_left_sum_associative S T rS rT bS bT refS (A_sg_associative _ _ _ sgS) (A_sg_associative _ _ _ sgT) 
; A_sg_congruence    := bop_left_sum_congruence S T rS rT bS bT (A_sg_congruence _ _ _ sgS) (A_sg_congruence _ _ _ sgT) 

; A_sg_commutative_d := bop_left_sum_commutative_decide S T rS rT bS bT refS (A_sg_commutative_d _ _ _ sgS) (A_sg_commutative_d _ _ _ sgT) 
; A_sg_selective_d   := bop_left_sum_selective_decide S T rS rT bS bT refS (A_sg_selective_d _ _ _ sgS) (A_sg_selective_d _ _ _ sgT) 
; A_sg_idempotent_d  := bop_left_sum_idempotent_decide S T rS rT bS bT (A_sg_idempotent_d _ _ _ sgS) (A_sg_idempotent_d _ _ _ sgT) 

; A_sg_is_left_d        := inr _ (bop_left_sum_not_is_left S T rS rT bS bT s t)
; A_sg_is_right_d       := inr _ (bop_left_sum_not_is_right S T rS rT bS bT s t)
; A_sg_left_cancel_d    := inr _ (bop_left_sum_not_left_cancellative S T rS rT bS bT s refS t g Pg)
; A_sg_right_cancel_d   := inr _ (bop_left_sum_not_right_cancellative S T rS rT bS bT s refS t g Pg)
; A_sg_left_constant_d  := inr _ (bop_left_sum_not_left_constant S T rS rT bS bT s f Pf t)
; A_sg_right_constant_d := inr _ (bop_left_sum_not_right_constant S T rS rT bS bT s f Pf t)
; A_sg_anti_left_d      := inr _ (bop_left_sum_not_anti_left S T rS rT bS bT s refS t)
; A_sg_anti_right_d     := inr _ (bop_left_sum_not_anti_right S T rS rT bS bT s refS t)
|}. 


Definition sg_C_proofs_left_sum : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T) (s : S) (f : S -> S) (t : T) (g : T -> T), 
     brel_not_trivial S rS f -> brel_not_trivial T rT g -> 
     eqv_proofs S rS -> eqv_proofs T rT -> sg_C_proofs S rS bS -> sg_C_proofs T rT bT -> 
        sg_C_proofs (S + T) (brel_sum rS rT) (bop_left_sum bS bT)
:= λ S T rS rT bS bT s f t g Pf Pg eqvS eqvT sgS sgT, 
let refS := A_eqv_reflexive _ _ eqvS in 
{|
  A_sg_C_associative   := bop_left_sum_associative S T rS rT bS bT refS (A_sg_C_associative _ _ _ sgS) (A_sg_C_associative _ _ _ sgT) 
; A_sg_C_congruence    := bop_left_sum_congruence S T rS rT bS bT (A_sg_C_congruence _ _ _ sgS) (A_sg_C_congruence _ _ _ sgT) 
; A_sg_C_commutative   := bop_left_sum_commutative S T rS rT bS bT refS (A_sg_C_commutative _ _ _ sgS) (A_sg_C_commutative _ _ _ sgT) 

; A_sg_C_selective_d   := bop_left_sum_selective_decide S T rS rT bS bT refS (A_sg_C_selective_d _ _ _ sgS) (A_sg_C_selective_d _ _ _ sgT)
; A_sg_C_idempotent_d  := bop_left_sum_idempotent_decide S T rS rT bS bT (A_sg_C_idempotent_d _ _ _ sgS) (A_sg_C_idempotent_d _ _ _ sgT) 
                         
; A_sg_C_cancel_d      := inr _ (bop_left_sum_not_left_cancellative S T rS rT bS bT s refS t g Pg)
; A_sg_C_constant_d    := inr _ (bop_left_sum_not_left_constant S T rS rT bS bT s f Pf t)
; A_sg_C_anti_left_d   := inr _ (bop_left_sum_not_anti_left S T rS rT bS bT s refS t)
; A_sg_C_anti_right_d  := inr _ (bop_left_sum_not_anti_right S T rS rT bS bT s refS t)
|}. 

Definition sg_CI_proofs_left_sum : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T) (s : S) (t : T), 
     eqv_proofs S rS -> eqv_proofs T rT -> sg_CI_proofs S rS bS -> sg_CI_proofs T rT bT -> 
        sg_CI_proofs (S + T) (brel_sum rS rT) (bop_left_sum bS bT)
:= λ S T rS rT bS bT s t eqvS eqvT sgS sgT, 
let refS := A_eqv_reflexive _ _ eqvS in 
{|
  A_sg_CI_associative := bop_left_sum_associative S T rS rT bS bT refS (A_sg_CI_associative _ _ _ sgS) (A_sg_CI_associative _ _ _ sgT) 
; A_sg_CI_congruence  := bop_left_sum_congruence S T rS rT bS bT (A_sg_CI_congruence _ _ _ sgS) (A_sg_CI_congruence _ _ _ sgT) 
; A_sg_CI_commutative := bop_left_sum_commutative S T rS rT bS bT refS (A_sg_CI_commutative _ _ _ sgS) (A_sg_CI_commutative _ _ _ sgT) 
                         
(*; A_sg_CI_selective_d  := bop_left_sum_selective_decide S T rS rT bS bT refS (A_sg_CI_selective_d _ _ _ sgS) (A_sg_CI_selective_d _ _ _ sgT)*)
; A_sg_CI_not_selective  := bop_left_sum_not_selective_left S T rS rT bS bT (A_sg_CI_not_selective _ _ _ sgS) 
; A_sg_CI_idempotent   := bop_left_sum_idempotent S T rS rT bS bT (A_sg_CI_idempotent _ _ _ sgS) (A_sg_CI_idempotent _ _ _ sgT) 
|}.

Definition sg_CS_proofs_left_sum : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T) (s : S) (t : T), 
     eqv_proofs S rS -> eqv_proofs T rT -> sg_CS_proofs S rS bS -> sg_CS_proofs T rT bT -> 
        sg_CS_proofs (S + T) (brel_sum rS rT) (bop_left_sum bS bT)
:= λ S T rS rT bS bT s t eqvS eqvT sgS sgT, 
let refS := A_eqv_reflexive _ _ eqvS in 
{|
  A_sg_CS_associative := bop_left_sum_associative S T rS rT bS bT refS (A_sg_CS_associative _ _ _ sgS) (A_sg_CS_associative _ _ _ sgT) 
; A_sg_CS_congruence  := bop_left_sum_congruence S T rS rT bS bT (A_sg_CS_congruence _ _ _ sgS) (A_sg_CS_congruence _ _ _ sgT) 
; A_sg_CS_commutative := bop_left_sum_commutative S T rS rT bS bT refS (A_sg_CS_commutative _ _ _ sgS) (A_sg_CS_commutative _ _ _ sgT) 
; A_sg_CS_selective   := bop_left_sum_selective S T rS rT bS bT refS (A_sg_CS_selective _ _ _ sgS) (A_sg_CS_selective _ _ _ sgT) 
|}. 


Definition A_sg_left_sum : ∀ (S T : Type),  A_sg S -> A_sg T -> A_sg (S + T) 
:= λ S T sgS sgT, 
let eqvS := A_sg_eqv S sgS in
let eqvT := A_sg_eqv T sgT in
let bS   := A_sg_bop S sgS in
let bT   := A_sg_bop T sgT in
let rS   := A_eqv_eq S eqvS in
let rT   := A_eqv_eq T eqvT in 
let s    := A_eqv_witness S eqvS in
let f    := A_eqv_new S eqvS in
let t    := A_eqv_witness T eqvT in
let g    := A_eqv_new T eqvT in
let refS := A_eqv_reflexive _ _ (A_eqv_proofs S eqvS) in 
{| 
     A_sg_eqv           := A_eqv_sum S T eqvS eqvT
   ; A_sg_bop          := bop_left_sum  bS bT
   ; A_sg_exists_id_d  := bop_left_sum_exists_id_decide S T rS rT  bS bT refS t (A_sg_exists_id_d _ sgT) 
   ; A_sg_exists_ann_d := bop_left_sum_exists_ann_decide S T rS rT bS bT s refS (A_sg_exists_ann_d _ sgS)
   ; A_sg_proofs       := sg_proofs_left_sum S T rS rT bS bT s f t g 
                           (A_eqv_not_trivial S eqvS)                                                                                  
                           (A_eqv_not_trivial T eqvT)                                                       
                           (A_eqv_proofs S eqvS) 
                           (A_eqv_proofs T eqvT) 
                           (A_sg_proofs S sgS) 
                           (A_sg_proofs T sgT)
   
   ; A_sg_ast         := Ast_sg_left_sum (A_sg_ast S sgS, A_sg_ast T sgT)
|}. 


(*
Definition A_sg_C_left_sum : ∀ (S T : Type),  A_sg_C S -> A_sg_C T -> A_sg_C (S + T) 
:= λ S T sgS sgT, 
let eqvS := A_sg_C_eqv S sgS in 
let eqvT := A_sg_C_eqv T sgT in
let bS   := A_sg_C_bop S sgS in
let bT   := A_sg_C_bop T sgT in
let rS   := A_eqv_eq S eqvS in
let rT   := A_eqv_eq T eqvT in 
let s    := A_eqv_witness S eqvS in
let f    := A_eqv_new S eqvS in
let t    := A_eqv_witness T eqvT in
let g    := A_eqv_new T eqvT in
let refS := A_eqv_reflexive _ _ (A_eqv_proofs S eqvS) in 
{| 
     A_sg_C_eqv       := A_eqv_sum S T eqvS eqvT
   ; A_sg_C_bop       := bop_left_sum bS bT
   ; A_sg_C_exists_id_d  := bop_left_sum_exists_id_decide S T rS rT  bS bT refS t (A_sg_C_exists_id_d _ sgT) 
   ; A_sg_C_exists_ann_d := bop_left_sum_exists_ann_decide S T rS rT bS bT s refS (A_sg_C_exists_ann_d _ sgS)
   ; A_sg_C_proofs    := sg_C_proofs_left_sum S T rS rT bS bT s f t g 
                           (A_eqv_not_trivial S eqvS)                                                                                  
                           (A_eqv_not_trivial T eqvT)                                                       
                           (A_eqv_proofs S (A_sg_C_eqv S sgS)) 
                           (A_eqv_proofs T (A_sg_C_eqv T sgT)) 
                           (A_sg_C_proofs S sgS) 
                           (A_sg_C_proofs T sgT)
  
   ; A_sg_C_ast       := Ast_sg_left_sum (A_sg_C_ast S sgS, A_sg_C_ast T sgT)
|}. 


Definition A_sg_CI_left_sum : ∀ (S T : Type),  A_sg_CI S -> A_sg_CI T -> A_sg_CI (S + T) 
:= λ S T sgS sgT,
let eqvS := A_sg_CI_eqv S sgS in 
let eqvT := A_sg_CI_eqv T sgT in
let bS   := A_sg_CI_bop S sgS in
let bT   := A_sg_CI_bop T sgT in
let rS   := A_eqv_eq S eqvS in
let rT   := A_eqv_eq T eqvT in 
let s    := A_eqv_witness S eqvS in
let t    := A_eqv_witness T eqvT in
let refS := A_eqv_reflexive _ _ (A_eqv_proofs S eqvS) in 
   {| 
     A_sg_CI_eqv       := A_eqv_sum S T eqvS eqvT
   ; A_sg_CI_bop       := bop_left_sum bS bT 
   ; A_sg_CI_exists_id_d  := bop_left_sum_exists_id_decide S T rS rT  bS bT refS t (A_sg_CI_exists_id_d _ sgT) 
   ; A_sg_CI_exists_ann_d := bop_left_sum_exists_ann_decide S T rS rT bS bT s refS (A_sg_CI_exists_ann_d _ sgS)
   ; A_sg_CI_proofs    := sg_CI_proofs_left_sum S T rS rT bS bT s t 
                           (A_eqv_proofs S (A_sg_CI_eqv S sgS)) 
                           (A_eqv_proofs T (A_sg_CI_eqv T sgT)) 
                           (A_sg_CI_proofs S sgS) 
                           (A_sg_CI_proofs T sgT)
   
   ; A_sg_CI_ast       := Ast_sg_left_sum (A_sg_CI_ast S sgS, A_sg_CI_ast T sgT)
|}. 

Definition A_sg_CS_left_sum : ∀ (S T : Type),  A_sg_CS S -> A_sg_CS T -> A_sg_CS (S + T) 
:= λ S T sgS sgT, 
let eqvS := A_sg_CS_eqv S sgS in 
let eqvT := A_sg_CS_eqv T sgT in
let bS   := A_sg_CS_bop S sgS in
let bT   := A_sg_CS_bop T sgT in 
let rS   := A_eqv_eq S eqvS in
let rT   := A_eqv_eq T eqvT in 
let s    := A_eqv_witness S eqvS in
let t    := A_eqv_witness T eqvT in
let refS := A_eqv_reflexive _ _ (A_eqv_proofs S eqvS) in 
{| 
     A_sg_CS_eqv       := A_eqv_sum S T eqvS eqvT
   ; A_sg_CS_bop       := bop_left_sum bS bT
   ; A_sg_CS_exists_id_d  := bop_left_sum_exists_id_decide S T rS rT  bS bT refS t (A_sg_CS_exists_id_d _ sgT) 
   ; A_sg_CS_exists_ann_d := bop_left_sum_exists_ann_decide S T rS rT bS bT s refS (A_sg_CS_exists_ann_d _ sgS)
   ; A_sg_CS_proofs    := sg_CS_proofs_left_sum S T rS rT bS bT s t 
                           (A_eqv_proofs S (A_sg_CS_eqv S sgS)) 
                           (A_eqv_proofs T (A_sg_CS_eqv T sgT)) 
                           (A_sg_CS_proofs S sgS) 
                           (A_sg_CS_proofs T sgT)
   
   ; A_sg_CS_ast       := Ast_sg_left_sum (A_sg_CS_ast S sgS, A_sg_CS_ast T sgT)
|}. 
*) 
End ACAS.

Section AMCAS.

  Definition A_sg_left_sum_below_sg {S T : Type} (A : @A_below_sg S)  (B : @A_below_sg T)  : @A_below_sg (S + T) :=
    A_classify_sg (A_sg_left_sum _ _ (A_cast_up_sg A) (A_cast_up_sg B)).

  
  Definition A_mcas_sg_left_sum {S T : Type} (A : @A_sg_mcas S)  (B : @A_sg_mcas T)  : @A_sg_mcas (S + T) :=
    match A, B with
    | A_MCAS_sg A', A_MCAS_sg B'               => A_MCAS_sg (A_sg_left_sum_below_sg A' B')
    | A_MCAS_sg_Error sl1, A_MCAS_sg_Error sl2 => A_MCAS_sg_Error (sl1 ++ sl2)
    | A_MCAS_sg_Error sl1, _                   => A_MCAS_sg_Error sl1
    | _,  A_MCAS_sg_Error sl2                  => A_MCAS_sg_Error sl2
    end.

End AMCAS.

Section CAS.

Definition check_exists_id_left_sum : ∀ {S T : Type}, @check_exists_id T -> @check_exists_id (S + T)
:= λ {S T} cT,  
      match cT with 
      | Certify_Exists_Id t    => Certify_Exists_Id (inr S t) 
      | Certify_Not_Exists_Id  => Certify_Not_Exists_Id
      end. 

Definition check_exists_ann_left_sum : ∀ {S T : Type}, 
             (check_exists_ann (S := S)) -> (check_exists_ann (S := (S + T)))
:= λ {S T} cS,  
      match cS with 
      | Certify_Exists_Ann s    => Certify_Exists_Ann (inl T s)
      | Certify_Not_Exists_Ann => Certify_Not_Exists_Ann 
      end.

Definition check_idempotent_left_sum : ∀ {S T : Type}, 
             (check_idempotent (S := S)) -> 
             (check_idempotent (S := T)) -> 
                (check_idempotent (S := (S + T)))
:= λ {S T} cS cT,  
      match cS, cT with 
      | Certify_Idempotent, Certify_Idempotent => Certify_Idempotent 
      | Certify_Not_Idempotent s1 , _       => Certify_Not_Idempotent (inl _ s1)
      | _, Certify_Not_Idempotent t1        => Certify_Not_Idempotent (inr _ t1)
      end. 


Definition check_selective_left_sum : ∀ {S T : Type}, 
             (check_selective (S := S)) -> 
             (check_selective (S := T)) -> 
                (check_selective (S := (S + T)))
:= λ {S T} cS cT,  
      match cS, cT with 
      | Certify_Selective, Certify_Selective => Certify_Selective 
      | Certify_Not_Selective (s1, s2), _    => Certify_Not_Selective ((inl _ s1), (inl _ s2))
      | _, Certify_Not_Selective (t1, t2)    => Certify_Not_Selective ((inr _ t1), (inr _ t2))
      end. 

Definition check_commutative_left_sum : ∀ {S T : Type}, 
             (check_commutative (S := S)) -> 
             (check_commutative (S := T)) -> 
                (check_commutative (S := (S + T)))
:= λ {S T} cS cT,  
      match cS, cT with 
      | Certify_Commutative, Certify_Commutative => Certify_Commutative 
      | Certify_Not_Commutative (s1, s2), _  => Certify_Not_Commutative ((inl _ s1), (inl _ s2))
      | _, Certify_Not_Commutative (t1, t2)  => Certify_Not_Commutative ((inr _ t1), (inr _ t2))
      end. 



Definition sg_certs_left_sum : ∀ {S T : Type},  S -> (S -> S) -> T -> (T -> T) -> @sg_certificates S -> @sg_certificates T -> @sg_certificates (S + T) 
:= λ {S T} s f t g cS cT,  
{|
  sg_associative      := Assert_Associative 
; sg_congruence       := Assert_Bop_Congruence 
; sg_commutative_d    := check_commutative_left_sum 
                            (sg_commutative_d cS) 
                            (sg_commutative_d cT)
; sg_idempotent_d     := check_idempotent_left_sum 
                            (sg_idempotent_d cS) 
                            (sg_idempotent_d cT)
; sg_selective_d      := check_selective_left_sum 
                            (sg_selective_d cS) 
                            (sg_selective_d cT)
; sg_is_left_d        := Certify_Not_Is_Left (inr t, inl s) 
; sg_is_right_d       := Certify_Not_Is_Right (inl s, inr t) 
; sg_left_cancel_d    := Certify_Not_Left_Cancellative (inl s, (inr t, inr (g t)))
; sg_right_cancel_d   := Certify_Not_Right_Cancellative (inl s, (inr t, inr (g t)))
; sg_left_constant_d  := Certify_Not_Left_Constant (inr t, (inl s, inl (f s)))
; sg_right_constant_d := Certify_Not_Right_Constant (inr t, (inl s, inl (f s)))
; sg_anti_left_d      := Certify_Not_Anti_Left (inl s, inr t) 
; sg_anti_right_d     := Certify_Not_Anti_Right (inl s, inr t)
|}.


Definition sg_C_certs_left_sum : ∀ {S T : Type}, S -> (S -> S) -> T -> (T -> T) -> @sg_C_certificates S -> @sg_C_certificates T -> @sg_C_certificates (S + T) 
:= λ {S T} s f t g cS cT,  
{|
  sg_C_associative      := Assert_Associative 
; sg_C_congruence       := Assert_Bop_Congruence  
; sg_C_commutative      := Assert_Commutative  
; sg_C_idempotent_d     := check_idempotent_left_sum 
                            (sg_C_idempotent_d cS) 
                            (sg_C_idempotent_d cT)
; sg_C_selective_d      := check_selective_left_sum 
                            (sg_C_selective_d cS) 
                            (sg_C_selective_d cT)
; sg_C_cancel_d         := Certify_Not_Left_Cancellative (inl s, (inr t, inr (g t)))
; sg_C_constant_d       := Certify_Not_Left_Constant (inr t, (inl s, inl (f s)))
; sg_C_anti_left_d      := Certify_Not_Anti_Left (inl s, inr t) 
; sg_C_anti_right_d     := Certify_Not_Anti_Right (inl s, inr t) 
|}.


Definition sg_CI_certs_left_sum : ∀ {S T : Type},  sg_CI_certificates (S := S) -> sg_CI_certificates (S := T) -> sg_CI_certificates (S := (S + T)) 
:= λ {S T} cS cT,  
{|
  sg_CI_associative  := Assert_Associative   
; sg_CI_congruence   := Assert_Bop_Congruence  
; sg_CI_commutative  := Assert_Commutative  
; sg_CI_idempotent   := Assert_Idempotent  
(*; sg_CI_selective_d  := check_selective_left_sum (sg_CI_selective_d cS) (sg_CI_selective_d cT) *) 
; sg_CI_not_selective  := 
      match sg_CI_not_selective cS with 
      | Assert_Not_Selective (s1, s2) => Assert_Not_Selective ((inl _ s1), (inl _ s2))
      end
|}.

Definition sg_CS_certs_left_sum : ∀ {S T : Type},  sg_CS_certificates (S := S) -> sg_CS_certificates (S := T) -> sg_CS_certificates (S := (S + T)) 
:= λ {S T} cS cT,  
{|
  sg_CS_associative  := Assert_Associative   
; sg_CS_congruence   := Assert_Bop_Congruence  
; sg_CS_commutative  := Assert_Commutative  
; sg_CS_selective    := Assert_Selective  
|}.

Definition sg_left_sum : ∀ {S T : Type},  sg (S := S) -> sg (S := T) -> sg (S := (S + T))
:= λ {S T} sgS sgT, 
   {| 
     sg_eqv     := eqv_sum (sg_eqv sgS) (sg_eqv sgT) 
   ; sg_bop    := bop_left_sum (sg_bop sgS) (sg_bop sgT) 
   ; sg_exists_id_d      := check_exists_id_left_sum (sg_exists_id_d  sgT)
   ; sg_exists_ann_d     := check_exists_ann_left_sum (sg_exists_ann_d sgS)
   ; sg_certs := sg_certs_left_sum 
                    (eqv_witness (sg_eqv sgS)) (eqv_new (sg_eqv sgS))
                    (eqv_witness (sg_eqv sgT)) (eqv_new (sg_eqv sgT)) 
                    (sg_certs sgS) 
                    (sg_certs sgT)
   
   ; sg_ast    := Ast_sg_left_sum (sg_ast sgS, sg_ast sgT)
   |}. 

(*
Definition sg_C_left_sum : ∀ {S T : Type},  sg_C (S := S) -> sg_C (S := T) -> sg_C (S := (S + T))
:= λ {S T} sgS sgT, 
   {| 
     sg_C_eqv          := eqv_sum (sg_C_eqv sgS) (sg_C_eqv sgT) 
   ; sg_C_bop          := bop_left_sum (sg_C_bop sgS) (sg_C_bop sgT) 
   ; sg_C_exists_id_d  := check_exists_id_left_sum (sg_C_exists_id_d  sgT)
   ; sg_C_exists_ann_d := check_exists_ann_left_sum (sg_C_exists_ann_d sgS)
   ; sg_C_certs        := sg_C_certs_left_sum 
                           (eqv_witness (sg_C_eqv sgS)) (eqv_new (sg_C_eqv sgS)) 
                           (eqv_witness (sg_C_eqv sgT)) (eqv_new (sg_C_eqv sgT)) 
                           (sg_C_certs sgS) 
                           (sg_C_certs sgT)
   
   ; sg_C_ast          := Ast_sg_left_sum (sg_C_ast sgS, sg_C_ast sgT)
   |}. 

Definition sg_CI_left_sum : ∀ {S T : Type},  sg_CI (S := S) -> sg_CI (S := T) -> sg_CI (S := (S + T))
:= λ {S T} sgS sgT, 
   {| 
     sg_CI_eqv       := eqv_sum (sg_CI_eqv sgS) (sg_CI_eqv sgT) 
   ; sg_CI_bop       := bop_left_sum (sg_CI_bop sgS) (sg_CI_bop sgT) 
   ; sg_CI_exists_id_d  := check_exists_id_left_sum (sg_CI_exists_id_d  sgT)
   ; sg_CI_exists_ann_d := check_exists_ann_left_sum (sg_CI_exists_ann_d sgS)
   ; sg_CI_certs    := sg_CI_certs_left_sum (sg_CI_certs sgS) (sg_CI_certs sgT)
   
   ; sg_CI_ast       := Ast_sg_left_sum (sg_CI_ast sgS, sg_CI_ast sgT)
   |}. 

Definition sg_CS_left_sum : ∀ {S T : Type},  sg_CS (S := S) -> sg_CS (S := T) -> sg_CS (S := (S + T))
:= λ {S T} sgS sgT, 
   {| 
     sg_CS_eqv       := eqv_sum (sg_CS_eqv sgS) (sg_CS_eqv sgT) 
   ; sg_CS_bop       := bop_left_sum (sg_CS_bop sgS) (sg_CS_bop sgT) 
   ; sg_CS_exists_id_d  := check_exists_id_left_sum (sg_CS_exists_id_d  sgT)
   ; sg_CS_exists_ann_d := check_exists_ann_left_sum (sg_CS_exists_ann_d sgS)
   ; sg_CS_certs     := sg_CS_certs_left_sum (sg_CS_certs sgS) (sg_CS_certs sgT)
   
   ; sg_CS_ast       := Ast_sg_left_sum (sg_CS_ast sgS, sg_CS_ast sgT)
   |}. 
  
*) 
End CAS.

Section MCAS.



  Definition sg_left_sum_below_sg {S T : Type} (A : @below_sg S)  (B : @below_sg T)  : @below_sg (S + T) :=
    classify_sg (sg_left_sum (cast_up_sg A) (cast_up_sg B)).

  
  Definition mcas_sg_left_sum {S T : Type} (A : @sg_mcas S)  (B : @sg_mcas T)  : @sg_mcas (S + T) :=
    match A, B with
    | MCAS_sg A', MCAS_sg B'               => MCAS_sg (sg_left_sum_below_sg A' B')
    | MCAS_sg_Error sl1, MCAS_sg_Error sl2 => MCAS_sg_Error (sl1 ++ sl2)
    | MCAS_sg_Error sl1, _                 => MCAS_sg_Error sl1
    | _,  MCAS_sg_Error sl2                => MCAS_sg_Error sl2
    end.


End MCAS.

Section Verify.

Section ChecksCorrect.

  Variable S : Type.
  Variable T : Type.
  Variable rS : brel S.
  Variable rT : brel T.
  Variable wS : S.
  Variable wT : T.
  Variable bS : binary_op S.
  Variable bT : binary_op T.
  Variable symS : brel_symmetric S rS.
  Variable symT : brel_symmetric T rT. 
  Variable transS : brel_transitive S rS.
  Variable transT : brel_transitive T rT. 
  Variable refS : brel_reflexive S rS. 
  Variable refT : brel_reflexive T rT.


Lemma correct_check_commutative_left_sum :  ∀ (dS : bop_commutative_decidable S rS bS) (dT : bop_commutative_decidable T rT bT),
         
         check_commutative_left_sum 
            (p2c_commutative_check S rS bS dS)
            (p2c_commutative_check T rT bT dT)
         = 
         p2c_commutative_check (S + T) 
            (brel_sum rS rT) 
            (bop_left_sum bS bT)
            (bop_left_sum_commutative_decide S T rS rT bS bT refS dS dT). 
Proof. intros [cS | [ [s3 s4] ncS]] [cT | [ [t3 t4] ncT]]; compute; reflexivity. Defined. 


Lemma correct_check_idempotent_left_sum : ∀ (dS : bop_idempotent_decidable S rS bS) (dT : bop_idempotent_decidable T rT bT),
         
         check_idempotent_left_sum 
            (p2c_idempotent_check S rS bS dS)
            (p2c_idempotent_check T rT bT dT)
         = 
         p2c_idempotent_check (S + T) 
            (brel_sum rS rT) 
            (bop_left_sum bS bT)
            (bop_left_sum_idempotent_decide S T rS rT bS bT dS dT). 
Proof. intros [cS | [s4 ncS]] [cT | [t4 ncT]]; compute; reflexivity. Defined. 

Lemma correct_check_selective_left_sum : ∀ (dS : bop_selective_decidable S rS bS) (dT : bop_selective_decidable T rT bT),
         
         check_selective_left_sum 
            (p2c_selective_check S rS bS dS)
            (p2c_selective_check T rT bT dT)
         = 
         p2c_selective_check (S + T) 
            (brel_sum rS rT) 
            (bop_left_sum bS bT)
            (bop_left_sum_selective_decide S T rS rT bS bT refS dS dT). 
Proof. intros [cS | [ [s3 s4] ncS]] [cT | [ [t3 t4] ncT]]; compute; reflexivity. Defined. 

Lemma correct_check_exists_id_left_sum : ∀ (dT : bop_exists_id_decidable T rT bT),
    
         check_exists_id_left_sum (p2c_exists_id_check T rT bT dT)
         =
         p2c_exists_id_check (S + T) 
            (brel_sum rS rT)
            (bop_left_sum bS bT)
            (bop_left_sum_exists_id_decide S T rS rT bS bT refS wT dT).
Proof. intros [[t tP] | nT ]; compute; reflexivity. Defined. 

Lemma correct_check_exists_ann_left_sum : ∀ (dS : bop_exists_ann_decidable S rS bS), 
         check_exists_ann_left_sum (p2c_exists_ann_check S rS bS dS)
         =
         p2c_exists_ann_check (S + T) 
            (brel_sum rS rT)
            (bop_left_sum bS bT)
            (bop_left_sum_exists_ann_decide S T rS rT bS bT wS refS dS).
Proof. intros [[s sP] | nS ]; compute; reflexivity. Defined. 


End ChecksCorrect. 

Section ProofsCorrect.

  Variable S : Type.
  Variable T : Type.
  Variable rS : brel S.
  Variable rT : brel T.
  Variable wS : S.
  Variable f : S -> S.    
  Variable Pf : brel_not_trivial S rS f.
  Variable wT : T.
  Variable g : T -> T.      
  Variable Pg : brel_not_trivial T rT g.  
  Variable bS : binary_op S.
  Variable bT : binary_op T.
  Variable eS : eqv_proofs S rS.
  Variable eT : eqv_proofs T rT. 




Lemma correct_sg_certs_left_sum : ∀ (pS : sg_proofs S rS bS) (pT : sg_proofs T rT bT),

      sg_certs_left_sum wS f wT g (P2C_sg rS bS pS) (P2C_sg rT bT pT) 
      = 
      P2C_sg (brel_sum rS rT) 
             (bop_left_sum bS bT) 
             (sg_proofs_left_sum S T rS rT bS bT wS f wT g Pf Pg eS eT pS pT). 
Proof. intros pS pT. 
       unfold sg_proofs_left_sum, sg_certs_left_sum, P2C_sg; simpl. 
       rewrite <- correct_check_commutative_left_sum. 
       rewrite <- correct_check_selective_left_sum. 
       rewrite correct_check_idempotent_left_sum. 
       reflexivity.        
Defined. 

Lemma correct_sg_C_certs_left_sum : ∀ (pS : sg_C_proofs S rS bS) (pT : sg_C_proofs T rT bT),
        
      sg_C_certs_left_sum wS f wT g (P2C_sg_C rS bS pS) (P2C_sg_C rT bT pT) 
      = 
      P2C_sg_C (brel_sum rS rT) 
               (bop_left_sum bS bT) 
               (sg_C_proofs_left_sum S T rS rT bS bT wS f wT g Pf Pg eS eT pS pT). 
Proof. intros pS pT. 
       unfold sg_C_proofs_left_sum, sg_C_certs_left_sum, P2C_sg_C; simpl. 
       rewrite <- correct_check_selective_left_sum. 
       rewrite correct_check_idempotent_left_sum. 
       reflexivity. 
Defined. 

Lemma correct_sg_CS_certs_left_sum : ∀ (pS : sg_CS_proofs S rS bS) (pT : sg_CS_proofs T rT bT),
        
      sg_CS_certs_left_sum (P2C_sg_CS rS bS pS) (P2C_sg_CS rT bT pT) 
      = 
      P2C_sg_CS (brel_sum rS rT) 
                (bop_left_sum bS bT) 
                (sg_CS_proofs_left_sum S T rS rT bS bT wS wT eS eT pS pT). 
Proof. intros pS pT. 
       unfold sg_CS_proofs_left_sum, sg_CS_certs_left_sum, P2C_sg_CS; simpl. 
       reflexivity. 
Defined. 

Lemma correct_sg_CI_certs_left_sum : ∀ (pS : sg_CI_proofs S rS bS) (pT : sg_CI_proofs T rT bT),
      sg_CI_certs_left_sum (P2C_sg_CI rS bS pS) (P2C_sg_CI rT bT pT) 
      = 
      P2C_sg_CI (brel_sum rS rT) 
                (bop_left_sum bS bT) 
                (sg_CI_proofs_left_sum S T rS rT bS bT wS wT eS eT pS pT). 
Proof. intros pS pT. 
       unfold sg_CI_proofs_left_sum, sg_CI_certs_left_sum, P2C_sg_CI; simpl. 
       (*       rewrite <- correct_check_selective_left_sum. *)
       destruct (A_sg_CI_not_selective S rS bS pS) as [[s t] [A B]]. compute. 
       reflexivity. 
Defined.

End ProofsCorrect. 


Theorem correct_sg_left_sum : ∀ (S T : Type) (sgS : A_sg S) (sgT : A_sg T), 
      
         sg_left_sum (A2C_sg sgS) (A2C_sg sgT) 
         = 
         A2C_sg (A_sg_left_sum S T sgS sgT). 
Proof. intros S T sgS sgT. 
       unfold sg_left_sum, A2C_sg. simpl. 
       rewrite correct_eqv_sum. 
       rewrite <- correct_sg_certs_left_sum.
       rewrite <- correct_check_exists_id_left_sum. 
       rewrite <- correct_check_exists_ann_left_sum. 
       reflexivity. 
Qed. 

Theorem correct_sg_left_sum_below_sg (S T : Type) (A : @A_below_sg S) (B : @A_below_sg T) : 
  sg_left_sum_below_sg (A2C_below_sg A) (A2C_below_sg B)
  =
  A2C_below_sg (A_sg_left_sum_below_sg A B). 
Proof. unfold sg_left_sum_below_sg, A_sg_left_sum_below_sg.
       rewrite cast_up_sg_A2C_commute.
       rewrite cast_up_sg_A2C_commute.
       rewrite correct_sg_left_sum. 
       rewrite correct_classify_sg.
       reflexivity. 
Qed. 

Theorem correct_mcas_sg_left_sum (S T : Type) (A : @A_sg_mcas S) (B : @A_sg_mcas T) : 
         mcas_sg_left_sum (A2C_sg_mcas A) (A2C_sg_mcas B) 
         = 
         A2C_sg_mcas (A_mcas_sg_left_sum A B). 
Proof. destruct A, B; unfold mcas_sg_left_sum, A_mcas_sg_left_sum,
         A2C_sg_mcas; try reflexivity. 
       rewrite correct_sg_left_sum_below_sg.
       reflexivity. 
Qed. 



(*
Theorem correct_sg_C_left_sum : ∀ (S T : Type) (sgS : A_sg_C S) (sgT : A_sg_C T), 
      
         sg_C_left_sum (A2C_sg_C S sgS) (A2C_sg_C T sgT) 
         = 
         A2C_sg_C (S + T) (A_sg_C_left_sum S T sgS sgT). 
Proof. intros S T sgS sgT. 
       unfold sg_C_left_sum, A2C_sg_C. simpl. 
       rewrite correct_eqv_sum. 
       rewrite <- correct_sg_C_certs_left_sum.
       rewrite <- correct_check_exists_id_left_sum. 
       rewrite <- correct_check_exists_ann_left_sum. 
       reflexivity. 
Qed. 

Theorem correct_sg_CS_left_sum : ∀ (S T : Type) (sgS : A_sg_CS S) (sgT : A_sg_CS T), 
      
         sg_CS_left_sum (A2C_sg_CS S sgS) (A2C_sg_CS T sgT) 
         = 
         A2C_sg_CS (S + T) (A_sg_CS_left_sum S T sgS sgT). 
Proof. intros S T sgS sgT. 
       unfold sg_CS_left_sum, A2C_sg_CS. simpl. 
       rewrite correct_eqv_sum. 
       rewrite <- correct_sg_CS_certs_left_sum.
       rewrite <- correct_check_exists_id_left_sum. 
       rewrite <- correct_check_exists_ann_left_sum.        
       reflexivity. 
Qed. 


Theorem correct_sg_CI_left_sum : ∀ (S T : Type) (sgS : A_sg_CI S) (sgT : A_sg_CI T), 
      
         sg_CI_left_sum (A2C_sg_CI S sgS) (A2C_sg_CI T sgT) 
         = 
         A2C_sg_CI (S + T) (A_sg_CI_left_sum S T sgS sgT). 
Proof. intros S T sgS sgT. 
       unfold sg_CI_left_sum, A2C_sg_CI. simpl. 
       rewrite correct_eqv_sum. 
       rewrite <- correct_sg_CI_certs_left_sum.
       rewrite <- correct_check_exists_id_left_sum. 
       rewrite <- correct_check_exists_ann_left_sum.               
       reflexivity. 
Qed. 
*)   
 
End Verify.   
  
