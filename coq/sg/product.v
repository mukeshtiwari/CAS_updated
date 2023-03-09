Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool.

Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.

Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.eqv.theory.

Require Import CAS.coq.eqv.product.

Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures.
Require Import CAS.coq.sg.cast_up.
Require Import CAS.coq.sg.classify. 
Require Import CAS.coq.sg.theory. 
Require Import CAS.coq.sg.and. 
Require Import CAS.coq.sg.or.

Lemma not_is_left_and_is_right
      (S: Type)
      (eq : brel S)
      (wS : S)
      (f : S -> S)
      (nt : brel_not_trivial S eq f)
      (b : binary_op S)
      (sym : brel_symmetric S eq)
      (trn : brel_transitive S eq) :
   (bop_is_left S eq b) -> (bop_is_right S eq b) -> False. 
Proof. intros il ir.    
       assert (A := il wS (f wS)). 
       assert (B := ir wS (f wS)).
       destruct (nt wS) as [C D].
       apply sym in A. 
       rewrite (trn _ _ _ A B) in C.
       discriminate C. 
Qed. 

Section Computation.

Definition bop_product : ∀ {S T : Type}, binary_op S → binary_op T → binary_op (S * T) 
:= λ {S T} U V x y,  
   match x, y with
    | (x1, x2), (y1, y2) => (U x1 y1, V x2 y2) 
   end.
  

End Computation.   

Section Theory.

Section Product. 

Variable S  : Type. 
Variable T  : Type. 
Variable rS : brel S. 
Variable rT : brel T. 
Variable bS : binary_op S. 
Variable bT : binary_op T.

Variable wS : S.
Variable f : S -> S.                
Variable Pf : brel_not_trivial S rS f. 

Variable refS : brel_reflexive S rS.
Variable symS : brel_symmetric S rS.
Variable transS : brel_transitive S rS. 

Variable wT : T.
Variable g : T -> T.                
Variable Pg : brel_not_trivial T rT g. 

Variable refT :  brel_reflexive T rT. 
Variable symT : brel_symmetric T rT.
Variable transT : brel_transitive T rT. 


Variable conS : bop_congruence S rS bS.
Variable assS : bop_associative S rS bS.

Variable conT : bop_congruence T rT bT. 
Variable assT : bop_associative T rT bT.

Notation "a =S b"  := (rS a b = true) (at level 15).
Notation "a =T b"  := (rT a b = true) (at level 15).
Notation "a <>S b"  := (rS a b = false) (at level 15).
Notation "a <>T b"  := (rT a b = false) (at level 15).

Notation "a *S b"  := (bS a b) (at level 15).
Notation "a *T b"  := (bT a b) (at level 15).

Notation "a <*> b" := (brel_product a b) (at level 15).
Notation "a [*] b" := (bop_product a b) (at level 15).


Lemma bop_product_congruence : bop_congruence (S * T) (rS <*> rT) (bS [*] bT). 
Proof. intros [s1 s2] [t1 t2] [u1 u2] [w1 w2]; simpl. intros H1 H2. 
       destruct (bop_and_elim _ _ H1) as [C1 C2].
       destruct (bop_and_elim _ _ H2) as [C3 C4].
       apply bop_and_intro. 
          apply conS; auto. 
          apply conT; auto. 
Defined.  

Lemma bop_product_associative : bop_associative (S * T) (rS <*> rT) (bS [*] bT). 
Proof. intros [s1 s2] [t1 t2] [u1 u2]; simpl. apply bop_and_intro. apply assS. apply assT. Defined.  

Lemma bop_product_idempotent :  bop_idempotent S rS bS → bop_idempotent T rT bT → bop_idempotent (S * T) (rS <*> rT) (bS [*] bT). 
Proof. intros L R (s, t). compute. rewrite L, R. reflexivity. Qed. 

Lemma bop_product_not_idempotent_left :  bop_not_idempotent S rS bS → bop_not_idempotent (S * T) (rS <*> rT) (bS [*] bT). 
Proof. intros [s P]. exists (s, wT). compute. rewrite P. reflexivity. Defined. 

Lemma bop_product_not_idempotent_right : bop_not_idempotent T rT bT → bop_not_idempotent (S * T) (rS <*> rT) (bS [*] bT). 
Proof. intros [t P]. exists (wS, t). compute. rewrite P. case_eq(rS (wS *S wS) wS); intro J; reflexivity. Defined. 

Lemma bop_product_not_idempotent :  (bop_not_idempotent S rS bS) + (bop_not_idempotent T rT bT) → 
            bop_not_idempotent (S * T) (rS <*> rT) (bS [*] bT). 
Proof. intros [L | R]. 
   apply bop_product_not_idempotent_left. exact L. 
   apply bop_product_not_idempotent_right. exact R. 
Defined. 

Lemma bop_product_commutative : bop_commutative S rS bS → bop_commutative T rT bT → bop_commutative (S * T) (rS <*> rT) (bS [*] bT). 
Proof. intros L R (s1, t1) (s2, t2). simpl. compute in *. rewrite L, R. simpl. reflexivity. Defined. 

Lemma bop_product_not_commutative_left : bop_not_commutative S rS bS → bop_not_commutative (S * T) (rS <*> rT) (bS [*] bT). 
Proof. intros [ [s t] P]. exists ((s, wT), (t, wT)). simpl. rewrite P. simpl. reflexivity. Defined. 

Lemma bop_product_not_commutative_right : bop_not_commutative T rT bT → bop_not_commutative (S * T) (rS <*> rT) (bS [*] bT).       
Proof. intros [ [s t] P]. exists ((wS, s), (wS, t)). simpl. rewrite andb_comm. rewrite P. simpl. reflexivity. Defined. 

Lemma bop_product_not_commutative : 
      (bop_not_commutative S rS bS) +  (bop_not_commutative T rT bT) → bop_not_commutative (S * T) (rS <*> rT) (bS [*] bT).       
Proof. intros [L | R]. 
   apply bop_product_not_commutative_left. exact L. 
   apply bop_product_not_commutative_right. exact R. 
Defined. 

Lemma bop_product_is_left : bop_is_left S rS bS → bop_is_left T rT bT → bop_is_left (S * T) (rS <*> rT) (bS [*] bT).       
Proof. intros L R (s1, t1) (s2, t2). simpl. rewrite L, R. simpl. reflexivity. Defined. 

Lemma bop_product_not_is_left_left : bop_not_is_left S rS bS → bop_not_is_left (S * T) (rS <*> rT) (bS [*] bT).       
Proof. intros [ [s t] P]. exists ((s, wT), (t, wT)). simpl. rewrite P. simpl. reflexivity. Defined. 

Lemma bop_product_not_is_left_right : bop_not_is_left T rT bT → bop_not_is_left (S * T) (rS <*> rT) (bS [*] bT).       
Proof. intros [ [s t] P].  exists ((wS, s), (wS, t)). simpl. rewrite andb_comm. rewrite P. simpl. reflexivity. Defined. 

Lemma bop_product_not_is_left (s : S) (t : T) : 
      (bop_not_is_left S rS bS) +  (bop_not_is_left T rT bT) → 
      bop_not_is_left (S * T) (rS <*> rT) (bS [*] bT). 
Proof. 
   intros [L | R]. 
   apply bop_product_not_is_left_left. exact L. 
   apply bop_product_not_is_left_right. exact R. 
Defined. 

Lemma bop_product_is_right : bop_is_right S rS bS → bop_is_right T rT bT → bop_is_right (S * T) (rS <*> rT) (bS [*] bT). 
Proof. unfold bop_is_right. intros L R (s1, t1) (s2, t2). simpl. rewrite L, R. simpl. reflexivity. Defined. 

Lemma bop_product_not_is_right_left : bop_not_is_right S rS bS → bop_not_is_right (S * T) (rS <*> rT) (bS [*] bT). 
Proof. unfold bop_not_is_right. intros  [ [s t] P]. exists ((s, wT), (t, wT)). simpl. rewrite P. simpl. reflexivity. Defined. 

Lemma bop_product_not_is_right_right : bop_not_is_right T rT bT → bop_not_is_right (S * T) (rS <*> rT) (bS [*] bT). 
Proof. unfold bop_not_is_right. intros [ [s t] P]. exists ((wS, s), (wS, t)). simpl. rewrite andb_comm. rewrite P. simpl. reflexivity. Defined. 


Lemma bop_product_not_is_right : 
      (bop_not_is_right S rS bS) +  (bop_not_is_right T rT bT) → bop_not_is_right (S * T) (rS <*> rT) (bS [*] bT). 
Proof. 
   intros  [L | R]. 
   apply bop_product_not_is_right_left. exact L. 
   apply bop_product_not_is_right_right. exact R. 
Defined. 

(*
*) 

Lemma bop_product_selective : 
      ((bop_is_left S rS bS) * (bop_is_left T rT bT)) 
     + ((bop_is_right S rS bS) * (bop_is_right T rT bT)) → 
      bop_selective (S * T) (rS <*> rT) (bS [*] bT). 
Proof. 
    unfold bop_is_left, bop_is_right, bop_selective.  
    intros [ [L R] | [L R] ] [s1 t1] [s2 t2]; simpl.
       left. rewrite (L s1 s2), (R t1 t2). simpl. reflexivity. 
       right. rewrite (L s1 s2), (R t1 t2). simpl. reflexivity. 
Defined.  


Lemma bop_product_not_selective_test : 
      ((bop_not_is_left S rS bS) + (bop_not_is_left T rT bT)) 
     * ((bop_not_is_right S rS bS) + (bop_not_is_right T rT bT)) → 
      bop_not_selective (S * T) (rS <*> rT) (bS [*] bT). 
Proof. 
    unfold bop_not_is_left, bop_not_is_right, bop_not_selective.  
    intros [ 
             [ [ [s1 s2] P1 ] | [ [t1 t2] Q1]  ] 
             [ [ [s3 s4] P2 ] | [ [t3 t4] Q2]  ] 
           ]. 
    + exists ((s1, wT), (s2, wT)). simpl. 
      admit. 
    + exists ((s1, t3), (s2, t4)); 
          simpl. rewrite P1, Q2. simpl. rewrite andb_comm. simpl. split; reflexivity.             
    + exists ((s3, t1), (s4, t2)); 
          simpl. rewrite P2, Q1. simpl. rewrite andb_comm. simpl. split; reflexivity.             
    + admit.
Admitted.       

(*
   (NL(S) + NR(S)) * (NL(T) + NR(T)) * (NL(S)  + NL(T)) * (NR(S)  + NR(T)) 

   (L(S) * R(S)) + (L(T) * R(T)) + (L(S) * L(T)) + (R(S) * R(T)) 

*) 
Lemma bop_product_not_selective : 
(* NB *) ((bop_not_is_left S rS bS) + (bop_not_is_right S rS bS)) → 
(* NB *) ((bop_not_is_left T rT bT) + (bop_not_is_right T rT bT)) → 
      ((bop_not_is_left S rS bS) + (bop_not_is_left T rT bT)) 
     * ((bop_not_is_right S rS bS) + (bop_not_is_right T rT bT)) → 
      bop_not_selective (S * T) (rS <*> rT) (bS [*] bT). 
Proof. 
    intros  nl_or_nr_S nl_or_nr_T. 
    unfold bop_not_is_left, bop_not_is_right, bop_not_selective.  
    intros [ 
             [ [ [s1 s2] P1 ] | [ [t1 t2] Q1]  ] 
             [ [ [s3 s4] P2 ] | [ [t3 t4] Q2]  ] 
           ]. 
       destruct nl_or_nr_T as [ [ [t5 t6] W1 ]  | [ [t5 t6] W1 ] ]. 
          exists ((s3, t5), (s4, t6)); 
             simpl. rewrite P2, W1. simpl. rewrite andb_comm. simpl. split; reflexivity. 
          exists ((s1, t5), (s2, t6)); 
             simpl. rewrite P1, W1. simpl. rewrite andb_comm. simpl. split; reflexivity.
       exists ((s1, t3), (s2, t4)); 
          simpl. rewrite P1, Q2. simpl. rewrite andb_comm. simpl. split; reflexivity.             
       exists ((s3, t1), (s4, t2)); 
          simpl. rewrite P2, Q1. simpl. rewrite andb_comm. simpl. split; reflexivity.             
       destruct nl_or_nr_S as [ [ [s1 s2] W1]  | [ [s1 s2] W1] ]. 
          exists ((s1, t3), (s2, t4)); 
             simpl. rewrite Q2, W1. simpl. rewrite andb_comm. simpl. split; reflexivity.   
          exists ((s1, t1), (s2, t2)); 
             simpl. rewrite Q1, W1. simpl. rewrite andb_comm. simpl. split; reflexivity. 
Defined.


Lemma bop_product_not_selective_v2 (s : S) (t : T):
       bop_is_left_decidable S rS bS  →
       bop_is_right_decidable S rS bS  →  
       bop_is_left_decidable T rT bT  →
       bop_is_right_decidable T rT bT  →     
       ((bop_not_is_left S rS bS) + (bop_not_is_left T rT bT)) 
     * ((bop_not_is_right S rS bS) + (bop_not_is_right T rT bT)) → 
          bop_not_selective (S * T) (rS <*> rT) (bS [*] bT). 
Proof. 
  intros DLS DRS DLT DRT 
       [ 
             [ [ [s1 s2] P1 ] | [ [t1 t2] Q1]  ] 
             [ [ [s3 s4] P2 ] | [ [t3 t4] Q2]  ] 
       ].
       destruct DLT as [LT | [[t1 t2] NLT] ].
          destruct DRT as [RT | [[t1 t2] NTT] ].
             admit. (* T is left and right *) 
             exists ((s1, t1), (s2, t2)); simpl. admit. 
          exists ((s3, t1), (s4, t2)); simpl. admit.
       exists ((s1, t3), (s2, t4)); simpl. admit.
       exists ((s3, t1), (s4, t2)); simpl. admit.
       destruct DLS as [LS | [[s1 s2] NLS] ].
          destruct DRS as [RS | [[s1 s2] NTS] ].
             admit. (* S is left and right *) 
             exists ((s1, t1), (s2, t2)); simpl. admit. 
          exists ((s1, t3), (s2, t4)); simpl. admit.
Admitted. 


Lemma bop_product_left_cancellative :
        bop_left_cancellative S rS bS → bop_left_cancellative T rT bT → bop_left_cancellative (S * T) (rS <*> rT) (bS [*] bT). 
Proof. intros  L R [s1 t1] [s2 t2] [s3 t3]; simpl. 
       intro H. apply bop_and_elim in H. destruct H as [HL HR]. 
       apply L in HL. apply R in HR. rewrite HL, HR. auto. 
Defined. 

Lemma bop_product_not_left_cancellative_left : 
        bop_not_left_cancellative S rS bS → bop_not_left_cancellative (S * T) (rS <*> rT) (bS [*] bT). 
Proof. intros [ [s1 [s2 s3]] [L R] ] . 
       exists ((s1, wT), ((s2, wT), (s3, wT))); simpl. split. 
       apply bop_and_intro. 
         exact L. 
         apply refT. 
      rewrite R. simpl. reflexivity. 
Defined. 

Lemma bop_product_not_left_cancellative_right : 
      bop_not_left_cancellative T rT bT → bop_not_left_cancellative (S * T) (rS <*> rT) (bS [*] bT). 
Proof. intros [ [t1 [t2 t3]] [L R] ]. 
       exists ((wS, t1), ((wS, t2), (wS, t3))); simpl. split. 
       apply bop_and_intro. 
         apply refS. 
         exact L. 
      rewrite R. rewrite (refS wS). simpl. reflexivity. 
Defined. 


Lemma bop_product_right_cancellative : 
      bop_right_cancellative S rS bS → bop_right_cancellative T rT bT → 
         bop_right_cancellative (S * T) (rS <*> rT) (bS [*] bT). 
Proof. 
   intros L R [s1 t1] [s2 t2] [s3 t3]; simpl. 
   intro H. apply bop_and_elim in H. destruct H as [HL HR]. 
   apply L in HL. apply R in HR. rewrite HL, HR. auto. 
Defined. 

Lemma bop_product_not_right_cancellative_left : 
      bop_not_right_cancellative S rS bS → bop_not_right_cancellative (S * T) (rS <*> rT) (bS [*] bT). 
Proof. intros [ [s1 [s2 s3]] [L R] ]. 
       exists ((s1, wT), ((s2, wT), (s3, wT))); simpl. split. 
       apply bop_and_intro. 
         exact L. 
         apply refT. 
      rewrite R. simpl. reflexivity. 
Defined. 

Lemma bop_product_not_right_cancellative_right : 
        bop_not_right_cancellative T rT bT → bop_not_right_cancellative (S * T) (rS <*> rT) (bS [*] bT). 
Proof. intros [ [t1 [t2 t3]] [L R] ]. 
       exists ((wS, t1), ((wS, t2), (wS, t3))); simpl. split. 
       apply bop_and_intro. 
         apply refS. 
         exact L.      
      rewrite R. rewrite (refS wS). simpl. reflexivity. 
Defined. 

Lemma bop_product_left_constant : 
      bop_left_constant S rS bS → bop_left_constant T rT bT → bop_left_constant (S * T) (rS <*> rT) (bS [*] bT). 
Proof. intros  L R [s1 t1] [s2 t2] [s3 t3]; simpl. apply bop_and_intro. apply L. apply R. Defined. 

Lemma bop_product_not_left_constant_left : 
          bop_not_left_constant S rS bS → bop_not_left_constant (S * T) (rS <*> rT) (bS [*] bT). 
Proof. intros  [ [s1 [s2 s3]] Q ]. exists ((s1, wT), ((s2, wT), (s3, wT))); simpl. apply bop_and_false_intro. left. exact Q. Defined. 

Lemma bop_product_not_left_constant_right : bop_not_left_constant T rT bT → bop_not_left_constant (S * T) (rS <*> rT) (bS [*] bT). 
Proof. intros  [ [t1 [t2 t3]]  Q ]. exists ((wS, t1), ((wS, t2), (wS, t3))); simpl. apply bop_and_false_intro. right. exact Q. Defined. 

Lemma bop_product_right_constant : bop_right_constant S rS bS → bop_right_constant T rT bT → bop_right_constant (S * T) (rS <*> rT) (bS [*] bT). 
Proof. intros  L R [s1 t1] [s2 t2] [s3 t3]; simpl. apply bop_and_intro. apply L. apply R. Defined. 

Lemma bop_product_not_right_constant_left : bop_not_right_constant S rS bS → bop_not_right_constant (S * T) (rS <*> rT) (bS [*] bT). 
Proof. intros  [ [s1 [s2 s3]] Q ]. exists ((s1, wT), ((s2, wT), (s3, wT))); simpl. apply bop_and_false_intro. left. exact Q. Defined. 

Lemma bop_product_not_right_constant_right : bop_not_right_constant T rT bT → bop_not_right_constant (S * T) (rS <*> rT) (bS [*] bT). 
Proof. intros  [ [t1 [t2 t3]] Q ]. exists ((wS, t1), ((wS, t2), (wS, t3))); simpl. apply bop_and_false_intro. right. exact Q. Defined. 

Lemma bop_product_anti_left : (bop_anti_left S rS bS) + (bop_anti_left T rT bT) → bop_anti_left (S * T) (rS <*> rT) (bS [*] bT). 
Proof. intros  [P | P] [s1 t1] [s2 t2]; simpl; apply bop_and_false_intro. left. apply P. right. apply P. Defined. 

Lemma bop_product_anti_right : (bop_anti_right S rS bS) + (bop_anti_right T rT bT) → bop_anti_right (S * T) (rS <*> rT) (bS [*] bT). 
Proof. intros  [P | P] [s1 t1] [s2 t2]; simpl; apply bop_and_false_intro. left. apply P. right. apply P. Defined. 

Lemma bop_product_not_anti_left : bop_not_anti_left S rS bS → bop_not_anti_left T rT bT → bop_not_anti_left (S * T) (rS <*> rT) (bS [*] bT). 
Proof. intros  [[ s1 s2 ] P ] [ [ t1 t2 ] Q ]. exists ((s1, t1), (s2, t2)); simpl. rewrite P, Q. simpl. reflexivity. Defined. 

Lemma bop_product_not_anti_right : bop_not_anti_right S rS bS → bop_not_anti_right T rT bT → bop_not_anti_right (S * T) (rS <*> rT) (bS [*] bT). 
Proof. intros  [ [s1 s2] P ] [ [t1 t2] Q ]. exists ((s1, t1), (s2, t2)); simpl. rewrite P, Q. simpl. reflexivity. Defined. 

(* Elimination *) 

Lemma bop_product_is_id_left : 
   ∀ (s : S ) (t : T ),  (bop_is_id (S * T) (rS <*> rT) (bS [*] bT) (s, t)) ->  bop_is_id S rS bS s.        
Proof. intros  s t H s1. 
       destruct (H (s1, t)) as [L R]. simpl in L, R. 
       apply bop_and_elim in L. apply bop_and_elim in R. 
       destruct L as [LL RL]. destruct R as [LR RR]. 
       rewrite LL, LR. auto. 
Defined.                         

Lemma bop_product_is_id_right : 
   ∀ (s : S ) (t : T ), (bop_is_id (S * T) (rS <*> rT) (bS [*] bT) (s, t)) ->  bop_is_id T rT bT t.  
Proof. intros  s t H t1. 
       destruct (H (s, t1)) as [L R]. simpl in L, R. 
       apply bop_and_elim in L. apply bop_and_elim in R. 
       destruct L as [LL RL]. destruct R as [LR RR]. 
       rewrite RL, RR. auto. 
Defined.                         


Lemma bop_product_is_ann_left : 
   ∀ (s : S ) (t : T ), (bop_is_ann (S * T) (rS <*> rT) (bS [*] bT) (s, t)) ->  bop_is_ann S rS bS s.         
Proof. intros  s t H s1. 
       destruct (H (s1, t)) as [L R]. simpl in L, R. 
       apply bop_and_elim in L. apply bop_and_elim in R. 
       destruct L as [LL RL]. destruct R as [LR RR]. 
       rewrite LL, LR. auto. 
Defined.                         

Lemma bop_product_is_ann_right : 
   ∀ (s : S ) (t : T ), (bop_is_ann (S * T) (rS <*> rT) (bS [*] bT) (s, t)) ->  bop_is_ann T rT bT t.  
Proof. intros  s t H t1. 
       destruct (H (s, t1)) as [L R]. simpl in L, R. 
       apply bop_and_elim in L. apply bop_and_elim in R. 
       destruct L as [LL RL]. destruct R as [LR RR]. 
       rewrite RL, RR. auto. 
Defined.       



Lemma bop_product_is_id : 
        ∀ (s : S) (t : T), bop_is_id S rS bS s -> bop_is_id T rT bT t -> bop_is_id (S * T) (rS <*> rT) (bS [*] bT) (s, t).
Proof. unfold bop_is_id. intros  iS iT pS pT. 
       intros (s, t). compute. unfold brel_product, bop_product. 
       destruct (pS s) as [Sl Sr]. destruct (pT t) as [Tl Tr]. 
       rewrite Sl, Sr, Tl, Tr. auto. 
Defined. 


Lemma bop_product_not_is_id_left : 
        ∀ (s : S) (t : T), bop_not_is_id S rS bS s -> bop_not_is_id (S * T) (rS <*> rT) (bS [*] bT) (s, t).
Proof. unfold bop_is_id. intros  s t [x Nid]. 
       exists (x, t). compute. destruct Nid as [H | H]. 
       rewrite H. left. reflexivity. 
       rewrite H. right. reflexivity. 
Defined. 

Lemma bop_product_not_is_id_right : 
        ∀ (s : S) (t : T), bop_not_is_id T rT bT t -> bop_not_is_id (S * T) (rS <*> rT) (bS [*] bT) (s, t).
Proof. unfold bop_is_id. intros  s t [x Nid]. 
       exists (s, x). compute. destruct Nid as [H | H]. 
       rewrite H. left. case_eq(rS (bS s s) s); intro G. reflexivity. reflexivity. 
       rewrite H. right. case_eq(rS (bS s s) s); intro G. reflexivity. reflexivity. 
Defined. 


Lemma bop_product_exists_id : 
        bop_exists_id S rS bS -> bop_exists_id T rT bT -> bop_exists_id (S * T) (rS <*> rT) (bS [*] bT).
Proof. unfold bop_exists_id. intros  [iS pS] [iT pT]. exists (iS, iT). apply bop_product_is_id; auto. Defined. 

Lemma bop_product_not_exists_id : 
        (bop_not_exists_id S rS bS) + (bop_not_exists_id T rT bT) -> 
           bop_not_exists_id (S * T) (rS <*> rT) (bS [*] bT).
Proof. unfold bop_not_exists_id, brel_product, bop_product. 
       intros  [pS | pT] (s, t). 
       destruct (pS s) as [x [F | F]]. 
          exists (x, t). left. rewrite F. simpl. reflexivity. 
          exists (x, t). right. rewrite F. simpl. reflexivity. 
       destruct (pT t) as [x [F | F]]. 
          exists (s, x). left. rewrite F. apply andb_comm. 
          exists (s, x). right. rewrite F. apply andb_comm. 
Defined. 

Lemma bop_product_is_ann: 
        ∀ (s : S) (t : T), bop_is_ann S rS bS s -> bop_is_ann T rT bT t -> bop_is_ann (S * T) (rS <*> rT) (bS [*] bT) (s, t).
Proof. unfold bop_is_ann. intros  iS iT pS pT. 
       intros (s, t). compute. unfold brel_product, bop_product. 
       destruct (pS s) as [Sl Sr]. destruct (pT t) as [Tl Tr]. 
       rewrite Sl, Sr, Tl, Tr. auto. 
Defined. 


Lemma bop_product_not_is_ann_left : 
        ∀ (s : S) (t : T), bop_not_is_ann S rS bS s -> bop_not_is_ann (S * T) (rS <*> rT) (bS [*] bT) (s, t).
Proof. unfold bop_is_id. intros  s t [x Nid]. 
       exists (x, t). compute. destruct Nid as [H | H]. 
       rewrite H. left. reflexivity. 
       rewrite H. right. reflexivity. 
Defined. 

Lemma bop_product_not_is_ann_right : 
        ∀ (s : S) (t : T), bop_not_is_ann T rT bT t -> bop_not_is_ann (S * T) (rS <*> rT) (bS [*] bT) (s, t).
Proof. unfold bop_is_id. intros  s t [x Nid]. 
       exists (s, x). compute. destruct Nid as [H | H]; rewrite H. 
          left. case_eq(rS (bS s s) s); intro G. reflexivity. reflexivity. 
          right. case_eq(rS (bS s s) s); intro G. reflexivity. reflexivity. 
Defined. 

Lemma bop_product_exists_ann : 
        bop_exists_ann S rS bS -> bop_exists_ann T rT bT -> bop_exists_ann (S * T) (rS <*> rT) (bS [*] bT).
Proof. unfold bop_exists_id. intros  [annS pS] [annT pT]. exists (annS, annT). apply bop_product_is_ann; auto. Defined. 

Lemma bop_product_not_exists_ann : 
        (bop_not_exists_ann S rS bS) + (bop_not_exists_ann T rT bT) -> 
           bop_not_exists_ann (S * T) (rS <*> rT) (bS [*] bT).
Proof. unfold bop_not_exists_ann, brel_product, bop_product. 
       intros [pS | pT] (s, t). 
       destruct (pS s) as [x [F | F]]. 
          exists (x, t). left. rewrite F. simpl. reflexivity. 
          exists (x, t). right. rewrite F. simpl. reflexivity. 
       destruct (pT t) as [x [F | F]]. 
          exists (s, x). left. rewrite F. apply andb_comm. 
          exists (s, x). right. rewrite F. apply andb_comm. 
Defined.


(*bottoms

Definition bop_product_w (BS : list S) (BT : list T) (fS : S ->S) (fT : T -> T) (p : S * T) :=
  match p with (s, t) =>
               if in_set rS BS s 
               then if in_set rT BT t 
                    then (s, t)
                    else (s, fT t)
               else if in_set rT BT t 
                    then (fS s, t)
                    else (fS s, fT t)
  end.  

Definition map_mk_pairs: S -> finite_set T -> finite_set (S * T) :=
   fix f a Y := 
      match Y with
         | nil => nil 
         | b :: rest => (a, b) :: (f a rest)
      end.

Definition set_product : finite_set S -> finite_set T -> finite_set (S * T) :=
   fix f x y := 
      match x with
         | nil => nil 
         | a :: rest => (map_mk_pairs a y) ++ (f rest y) 
      end.

Lemma in_set_map_mk_pairs_elim (a s : S) (t : T) (BT : list T): 
      in_set (rS <*> rT) (map_mk_pairs a BT) (s, t) = true -> (rS a s = true) * (in_set rT BT t = true). 
Proof. induction BT; intro H. 
          compute in H. discriminate H. 
          unfold map_mk_pairs in H. fold map_mk_pairs in H. 
          apply in_set_cons_elim in H; auto. 
          destruct H as [H | H]. 
             compute in H. 
             case_eq(rS a s); intro G. 
                 rewrite G in H. split; auto. 
                 apply in_set_cons_intro; auto. 
                 rewrite G in H. discriminate H. 

             destruct (IHBT H) as [J K]. 
             split; auto. 
                apply in_set_cons_intro; auto. 
          apply brel_product_symmetric; auto. 
Qed. 
             
Lemma in_set_map_mk_pairs_intro (a s : S) (t : T) (BT : list T): 
    (rS a s = true) -> (in_set rT BT t = true) -> in_set (rS <*> rT) (map_mk_pairs a BT) (s, t) = true.
Proof. induction BT; intros H1 H2.
       compute in H2. discriminate H2. 

       unfold map_mk_pairs. fold map_mk_pairs. 
       apply in_set_cons_intro; auto. 
       apply brel_product_symmetric; auto. 
       apply in_set_cons_elim in H2; auto. 
       destruct H2 as [H2 | H2]. 
          left. compute. rewrite H1, H2. reflexivity. 
          right. apply IHBT; auto. 
Qed. 
       
Lemma in_set_product_elim (s : S) (t : T) (BS : list S) (BT : list T) :
  in_set (rS <*> rT) (set_product BS BT) (s, t) = true -> (in_set rS BS s = true) * (in_set rT BT t = true).
Proof. induction BS; intro H. 
       compute in H. discriminate H.
       unfold set_product in H. fold set_product in H.
       apply in_set_concat_elim in H; auto. 
       destruct H as [H | H]. 
          apply in_set_map_mk_pairs_elim in H. destruct H as [H1 H2].
          split; auto. 
             apply in_set_cons_intro; auto. 
       
          destruct (IHBS H) as [J K].        
          split; auto. 
             apply in_set_cons_intro; auto. 
             apply brel_product_symmetric; auto. 
Qed.

Lemma in_set_product_intro (s : S) (t : T) (BS : list S) (BT : list T) :
 (in_set rS BS s = true) -> (in_set rT BT t = true) -> in_set (rS <*> rT) (set_product BS BT) (s, t) = true. 
Proof. intros A B. induction BS. 
          compute in A. discriminate A. 

          unfold set_product. fold set_product. 
          apply in_set_concat_intro; auto. 
          apply in_set_cons_elim in A; auto.           
          destruct A as [A | A]. 
             left. apply in_set_map_mk_pairs_intro; auto. 
             right. exact (IHBS A). 
Qed. 

          
Lemma set_product_is_interesting (BS : list S) (BT : list T) :
  is_interesting S rS bS BS -> is_interesting T rT bT BT -> 
  is_interesting (S * T) (rS <*> rT) (bS [*] bT) (set_product BS BT).
Proof. unfold is_interesting. intros IS IT.
       intros [s1 t1] H1 [s2 t2] H2.
       apply in_set_product_elim in H1. destruct H1 as [H1L H1R].
       apply in_set_product_elim in H2. destruct H2 as [H2L H2R].
       destruct (IS s1 H1L s2 H2L) as [[A B] | [A B]];
       destruct (IT t1 H1R t2 H2R) as [[C D] | [C D]]; compute. 
          rewrite A, B, C, D. left; auto. 
          rewrite A, B, C, D. right; auto. 
          rewrite A, B.  right; auto. 
          rewrite A, B.  right; auto. 
Qed. 


(* note: commutativity not used *) 
Lemma bop_product_something_is_finite
      (idemS : bop_idempotent S rS bS) (idemT : bop_idempotent T rT bT):
  something_is_finite S rS bS →
  something_is_finite T rT bT →
       something_is_finite (S * T) (rS <*> rT) (bS [*] bT). 
Proof. unfold something_is_finite. 
       intros [[BS fS] [IS PS]] [[BT fT] [IT PT]]. 
       exists (set_product BS BT, bop_product_w BS BT fS fT). split. 
          apply set_product_is_interesting; auto.   
          intros [s t]. unfold bop_product_w.
          assert (iS := idemS s). apply symS in iS.
          assert (iT := idemT t). apply symT in iT.            
          destruct (PS s) as [A | [A [B C]]];
          destruct (PT t) as [D | [D [E F]]]. 
             left. apply in_set_product_intro; auto.

             rewrite A. case_eq(in_set rT BT t); intro G. 
                left. apply in_set_product_intro; auto.
                right. split. 
                   apply in_set_product_intro; auto.
                   split. 
                      compute. rewrite iS. exact E. 
                      compute. rewrite iS. exact F. 

             rewrite D. case_eq(in_set rS BS s); intro G. 
                left. apply in_set_product_intro; auto.
                right. split. 
                   apply in_set_product_intro; auto.
                   split. 
                      compute. rewrite B. exact iT. 
                      compute. rewrite C. reflexivity. 

             case_eq(in_set rS BS s); intro G; case_eq(in_set rT BT t); intro H.
                left. apply in_set_product_intro; auto. 

                right. split. 
                   apply in_set_product_intro; auto. 
                   split. 
                      compute. rewrite iS. exact E. 
                      compute. rewrite iS. exact F. 

                right. split. 
                   apply in_set_product_intro; auto. 
                   split. 
                      compute. rewrite B. exact iT. 
                      compute. rewrite C. reflexivity. 

                right. split. 
                   apply in_set_product_intro; auto. 
                   split. 
                      compute. rewrite B. exact E. 
                      compute. rewrite C. reflexivity. 
Qed. 

Definition set_product_proj1 (B : finite_set (S * T)) : finite_set S :=
  List.map (λ p, match p with (s, _) => s end) B. 

Definition set_product_proj2 (B : finite_set (S * T)) : finite_set T :=
  List.map (λ p, match p with (_, t) => t end) B.
 
Definition product_not_finite_v1 (F : finite_set S -> S) (X : finite_set (S * T)) : S * T :=
     (F (set_product_proj1 X), wT). 

Definition product_not_finite_v2 (F : finite_set T -> T) (X : finite_set (S * T)) : S * T :=
     (wS, F (set_product_proj2 X)). 

Lemma in_set_product_proj1_intro (B : finite_set (S * T)) :
  ∀ (s : S) (t : T) ,  
     in_set (rS <*> rT) B (s, t) = true -> in_set rS (set_product_proj1 B) s = true. 
Proof. induction B; intros s t H. 
          compute in H. discriminate H. 
          unfold set_product_proj1. 
          destruct a as [s' t']. 
          unfold List.map. fold (List.map (λ p : S * T, let (s0, _) := p in s0) B). 
          apply in_set_cons_intro; auto. 
          apply in_set_cons_elim in H; auto. 
          destruct H as [H | H]. 
             compute in H. 
             case_eq(rS s' s); intro J. 
               left. reflexivity. 
               rewrite J in H. discriminate H.

            right. exact (IHB s t H). 
          apply brel_product_symmetric; auto. 
Qed.

Lemma in_set_product_proj1_elim (B : finite_set (S * T)) :
  ∀ (s : S),  
     in_set rS (set_product_proj1 B) s = true -> {t : T & in_set (rS <*> rT) B (s, t) = true}. 
Proof. induction B; intros s H. 
       compute in H. discriminate H. 
       unfold set_product_proj1 in H. 
       destruct a as [s' t']. 
       unfold List.map in H. fold (List.map (λ p : S * T, let (s0, _) := p in s0) B) in H. 
       apply in_set_cons_elim in H; auto. 
       destruct H as [H | H]. 
          exists t'.
          apply in_set_cons_intro; auto.
          apply brel_product_symmetric; auto.
          left. compute. rewrite H. apply refT. 
          destruct (IHB s H) as [t P]. 
          exists t. 
          apply in_set_cons_intro; auto.
          apply brel_product_symmetric; auto.
Qed.


Lemma in_set_product_proj2_intro (B : finite_set (S * T)) :
  ∀ (s : S) (t : T) ,  
     in_set (rS <*> rT) B (s, t) = true -> in_set rT (set_product_proj2 B) t = true. 
Proof. induction B; intros s t H. 
          compute in H. discriminate H. 
          unfold set_product_proj2. 
          destruct a as [s' t']. 
          unfold List.map. fold (List.map (λ p : S * T, let (_, t0) := p in t0) B). 
          apply in_set_cons_intro; auto. 
          apply in_set_cons_elim in H; auto. 
          destruct H as [H | H]. 
             compute in H. 
             case_eq(rT t' t); intro J. 
               left. reflexivity. 
               rewrite J in H. 
               case_eq(rS s' s); intro K; rewrite K in H; discriminate H. 

              right. exact (IHB s t H). 
          apply brel_product_symmetric; auto. 
Qed.

Lemma set_product_is_interesting_v1 (B : finite_set (S * T)) : 
   is_interesting (S * T) (rS <*> rT) (bS [*] bT) B -> is_interesting S rS bS (set_product_proj1 B).
Proof. unfold is_interesting. intros I s1 H1 s2 H2.
       apply in_set_product_proj1_elim in H1. 
       apply in_set_product_proj1_elim in H2. 
       destruct H1 as [t1 H1]. 
       destruct H2 as [t2 H2]. 
       destruct (I (s1, t1) H1 (s2, t2) H2) as [[H3 H4] | [H3 H4]]; compute in H3, H4.           
          case_eq(rS s2 (s2 *S s1)); intro H5; case_eq(rS s1 (s1 *S s2)); intro H6. 
              left; auto. 
              rewrite H6 in H4. discriminate H4. 
              rewrite H5 in H3. discriminate H3. 
              right; auto. 
          case_eq(rT t2 (t2 *T t1)); intro H5; case_eq(rT t1 (t1 *T t2)); intro H6;
              rewrite H5 in H3; rewrite H6 in H4.
              case_eq(rS s2 (s2 *S s1)); intro H7; case_eq(rS s1 (s1 *S s2)); intro H8.  
                 left; auto. 
                 rewrite H7 in H3. discriminate H3. 
                 rewrite H8 in H4. discriminate H4. 
                 right; auto. 

              case_eq(rS s2 (s2 *S s1)); intro H7; case_eq(rS s1 (s1 *S s2)); intro H8.  
                 left; auto. 
                 rewrite H7 in H3. discriminate H3. 
                 admit. 
                 right; auto. 

              case_eq(rS s2 (s2 *S s1)); intro H7; case_eq(rS s1 (s1 *S s2)); intro H8.  
                 left; auto. 
                 admit. 
                 rewrite H8 in H4. discriminate H4. 
                 right; auto. 

              case_eq(rS s2 (s2 *S s1)); intro H7; case_eq(rS s1 (s1 *S s2)); intro H8.  
                 left; auto. 
                 admit. 
                 admit. 
                 right; auto. 
Admitted. 

       
Lemma set_product_is_interesting_v2 (B : finite_set (S * T)) : 
   is_interesting (S * T) (rS <*> rT) (bS [*] bT) B -> is_interesting T rT bT (set_product_proj2 B).
Admitted.



(* note: idempotence not used *) 
Lemma bop_product_something_not_is_finite_v1 (commS : bop_commutative S rS bS): 
  something_not_is_finite S rS bS →
     something_not_is_finite (S * T) (rS <*> rT) (bS [*] bT).
Proof. unfold something_not_is_finite.
       intros [F A]. 
       exists (product_not_finite_v1 F).
       intros B I. 
       assert (C := set_product_is_interesting_v1 B I).
       destruct (A (set_product_proj1 B) C) as [D E]. 
       unfold product_not_finite_v1.
       split. 
          case_eq(in_set (rS <*> rT) B (F (set_product_proj1 B), wT)); intro G; auto.
             apply in_set_product_proj1_intro in G. 
             rewrite G in D. discriminate D. 
          
          intros [s t] G. 
          assert (G' := in_set_product_proj1_intro _ _ _ G).
          unfold bop_product. unfold brel_product. 
          destruct (E s G') as [H | H].
             left. rewrite H. compute. reflexivity.

             case_eq(rS s (s *S F (set_product_proj1 B)) ); intro K. 
                assert (J := commS s (F (set_product_proj1 B))). 
                assert (L := transS _ _ _ K J).              
                apply symS in H. 
                assert (M := transS _ _ _ L H). 
                assert (N := in_set_right_congruence _ rS symS transS _ _ _ M G'). 
                rewrite N in D. discriminate D. 
                
                left. compute. reflexivity. 
Defined. 

Lemma bop_product_something_not_is_finite_v2 (commT : bop_commutative T rT bT): 
  something_not_is_finite T rT bT →
     something_not_is_finite (S * T) (rS <*> rT) (bS [*] bT).
Proof. unfold something_not_is_finite.
       intros [F A]. 
       exists (product_not_finite_v2 F).
       intros B I. 
       assert (C := set_product_is_interesting_v2 B I).
       destruct (A (set_product_proj2 B) C) as [D E]. 
       unfold product_not_finite_v2.
       split. 
          case_eq(in_set (rS <*> rT) B (wS, F (set_product_proj2 B))); intro G; auto.
             apply in_set_product_proj2_intro in G. 
             rewrite G in D. discriminate D. 
          
          intros [s t] G. 
          assert (G' := in_set_product_proj2_intro _ _ _ G).
          unfold bop_product. unfold brel_product. 
          destruct (E t G') as [H | H].
             left. rewrite H. apply andb_is_false_right. right. reflexivity. 

             case_eq(rT t (t *T F (set_product_proj2 B))); intro K. 
                assert (J := commT t (F (set_product_proj2 B))). 
                assert (L := transT _ _ _ K J).              
                apply symT in H. 
                assert (M := transT _ _ _ L H). 
                assert (N := in_set_right_congruence _ rT symT transT _ _ _ M G'). 
                rewrite N in D. discriminate D. 
                
                left. apply andb_is_false_right. right. reflexivity. 
Defined. 
*)

(* Decide *) 

Definition bop_product_idempotent_decide : 
     bop_idempotent_decidable S rS bS -> bop_idempotent_decidable T rT bT -> bop_idempotent_decidable (S * T) (rS <*> rT) (bS [*] bT)
:= λ dS dT,
       match dS with 
       | inl commS => 
         match dT with 
         | inl commT     => inl _ (bop_product_idempotent commS commT)
         | inr not_commT => inr _ (bop_product_not_idempotent_right not_commT)
         end 
       | inr not_commS   => inr _ (bop_product_not_idempotent_left not_commS)
       end.

Definition bop_product_commutative_decide : 
     bop_commutative_decidable S rS bS -> bop_commutative_decidable T rT bT -> bop_commutative_decidable (S * T) (rS <*> rT) (bS [*] bT)
:= λ dS dT,  
       match dS with 
       | inl commS => 
         match dT with 
         | inl commT     => inl _ (bop_product_commutative commS commT)
         | inr not_commT => inr _ (bop_product_not_commutative_right not_commT)
         end 
       | inr not_commS   => inr _ (bop_product_not_commutative_left not_commS)
       end.


Definition bop_product_left_cancellative_decide : 
  bop_left_cancellative_decidable S rS bS -> bop_left_cancellative_decidable T rT bT ->
      bop_left_cancellative_decidable (S * T) (rS <*> rT) (bS [*] bT)
:= λ dS dT,  
       match dS with 
       | inl canS => 
         match dT with 
         | inl canT     => inl _ (bop_product_left_cancellative canS canT)
         | inr not_canT => inr _ (bop_product_not_left_cancellative_right not_canT)
         end 
       | inr not_canS   => inr _ (bop_product_not_left_cancellative_left not_canS)
       end.

Definition bop_product_right_cancellative_decide : 
  bop_right_cancellative_decidable S rS bS -> bop_right_cancellative_decidable T rT bT -> 
     bop_right_cancellative_decidable (S * T) (rS <*> rT) (bS [*] bT) 
:= λ dS dT,  
       match dS with 
       | inl canS => 
         match dT with 
         | inl canT     => inl _ (bop_product_right_cancellative canS canT)
         | inr not_canT => inr _ (bop_product_not_right_cancellative_right not_canT)
         end 
       | inr not_canS   => inr _ (bop_product_not_right_cancellative_left not_canS)
       end.

Definition bop_product_is_left_decide : 
     bop_is_left_decidable S rS bS  → bop_is_left_decidable T rT bT  → bop_is_left_decidable (S * T) (rS <*> rT) (bS [*] bT)
:= λ dS dT,  
       match dS with 
       | inl leftS => 
         match dT with 
         | inl leftT     => inl _ (bop_product_is_left leftS leftT)
         | inr not_leftT => inr _ (bop_product_not_is_left_right not_leftT)
         end 
       | inr not_leftS   => inr _ (bop_product_not_is_left_left not_leftS)
       end. 

Definition bop_product_is_right_decide : 
     bop_is_right_decidable S rS bS  → bop_is_right_decidable T rT bT  → bop_is_right_decidable (S * T) (rS <*> rT) (bS [*] bT)
:= λ dS dT,  
       match dS with 
       | inl rightS => 
         match dT with 
         | inl rightT     => inl _ (bop_product_is_right rightS rightT)
         | inr not_rightT => inr _ (bop_product_not_is_right_right not_rightT)
         end 
       | inr not_rightS   => inr _ (bop_product_not_is_right_left not_rightS)
       end . 

Definition bop_product_exists_id_decide : 
     bop_exists_id_decidable S rS bS -> bop_exists_id_decidable T rT bT -> bop_exists_id_decidable (S * T) (rS <*> rT) (bS [*] bT)
:= λ dS dT,  
       match dS with 
       | inl eS => 
         match dT with 
         | inl eT  => inl _ (bop_product_exists_id eS eT)
         | inr neT => inr _ (bop_product_not_exists_id (inr _ neT))
         end 
       | inr neS   => inr _ (bop_product_not_exists_id (inl _ neS))
       end. 

Definition bop_product_exists_ann_decide : 
     bop_exists_ann_decidable S rS bS -> bop_exists_ann_decidable T rT bT -> bop_exists_ann_decidable (S * T) (rS <*> rT) (bS [*] bT) 
:= λ dS dT,  
       match dS with 
       | inl eS => 
         match dT with 
         | inl eT  => inl _ (bop_product_exists_ann eS eT)
         | inr neT => inr _ (bop_product_not_exists_ann (inr _ neT))
         end 
       | inr neS   => inr _ (bop_product_not_exists_ann (inl _ neS))
      end. 

Definition bop_product_left_constant_decide : 
     bop_left_constant_decidable S rS bS -> bop_left_constant_decidable T rT bT -> bop_left_constant_decidable (S * T) (rS <*> rT) (bS [*] bT)
:= λ dS dT,  
       match dS with 
       | inl PS => 
         match dT with 
         | inl PT     => inl _ (bop_product_left_constant PS PT)
         | inr nPT => inr _ (bop_product_not_left_constant_right nPT)
         end 
       | inr nPS   => inr _ (bop_product_not_left_constant_left nPS)
       end.


Definition bop_product_right_constant_decide : 
     bop_right_constant_decidable S rS bS -> bop_right_constant_decidable T rT bT ->      
         bop_right_constant_decidable (S * T) (rS <*> rT) (bS [*] bT)
:= λ dS dT,  
       match dS with 
       | inl PS => 
         match dT with 
         | inl PT  => inl _ (bop_product_right_constant PS PT)
         | inr nPT => inr _ (bop_product_not_right_constant_right nPT)
         end 
       | inr nPS   => inr _ (bop_product_not_right_constant_left nPS)
       end.

Definition bop_product_anti_left_decide : 
     bop_anti_left_decidable S rS bS -> bop_anti_left_decidable T rT bT -> 
        bop_anti_left_decidable (S * T) (rS <*> rT) (bS [*] bT)
:= λ dS dT,  
   match dS with 
   | inl PS => inl _ (bop_product_anti_left (inl _ PS))
   | inr nPS   => 
     match dT with 
     | inl PT     => inl _ (bop_product_anti_left (inr _ PT))
     | inr nPT => inr _ (bop_product_not_anti_left nPS nPT)
     end 
   end. 

Definition bop_product_anti_right_decide : 
     bop_anti_right_decidable S rS bS -> bop_anti_right_decidable T rT bT -> 
        bop_anti_right_decidable (S * T) (rS <*> rT) (bS [*] bT)
:= λ dS dT,  
   match dS with 
   | inl PS => inl _ (bop_product_anti_right (inl _ PS))
   | inr nPS   => 
     match dT with 
     | inl PT     => inl _ (bop_product_anti_right (inr _ PT))
     | inr nPT => inr _ (bop_product_not_anti_right nPS nPT)
     end 
   end.


Lemma bop_not_left_or_not_right : ∀ (U : Type) (r : brel U) (b : binary_op U) (u : U) (h : U -> U),
    brel_not_trivial U r h -> brel_symmetric U r -> brel_transitive U r ->     
    bop_is_left U r b -> bop_is_right U r b -> False. 
Proof. intros U r b u h Ph symU transU ilS irS.
       destruct (Ph u) as [L _].
       assert (H1 := ilS u (h u)).
       assert (H2 := irS u (h u)).
       apply symU in H1.
       assert (H3 := transU _ _ _ H1 H2).
       rewrite L in H3. 
       discriminate H3. 
Qed.

Lemma bop_product_selective_direct_decide :
  bop_selective_decidable S rS bS  →
  bop_selective_decidable T rT bT  →   
  bop_is_left_decidable S rS bS  → 
  bop_is_left_decidable T rT bT  → 
  bop_is_right_decidable S rS bS  → 
  bop_is_right_decidable T rT bT  → 
  bop_selective_decidable (S * T) (rS <*> rT) (bS [*] bT).
Proof. intros selS_d selT_d ilS_d ilT_d irS_d irT_d.
       destruct selS_d as [selS | [[s1 s2] [A B]]];
         destruct selT_d as [selT | [[t1 t2] [C D]]].
       + destruct ilS_d as [ilS | [[s1 s2] A]];
         destruct ilT_d as [ilT | [[t1 t2] B]];
         destruct irS_d as [irS | [[s3 s4] C]];
         destruct irT_d as [irT | [[t3 t4] D]].
         ++ exact (abort _ (not_is_left_and_is_right _ rS wS f Pf bS symS transS ilS irS)).
         ++ exact (abort _ (not_is_left_and_is_right _ rS wS f Pf bS symS transS ilS irS)).
         ++ exact (abort _ (not_is_left_and_is_right _ rT wT g Pg bT symT transT ilT irT)).
         ++ left.  intros [a b] [c d]. compute. 
            left. rewrite ilS. apply ilT. 
         ++ exact (abort _ (not_is_left_and_is_right _ rS wS f Pf bS symS transS ilS irS)).
         ++ exact (abort _ (not_is_left_and_is_right _ rS wS f Pf bS symS transS ilS irS)).
         ++ right. exists ((s3, t1), (s4, t2)).
            compute. rewrite B, C.
            destruct (selS s3 s4) as [D | D].
            +++ rewrite D. auto.
            +++ rewrite D in C. discriminate C. 
         ++ right. exists ((s3, t1), (s4, t2)).
            compute. rewrite B, C.
            destruct (selS s3 s4) as [E | E].
            +++ rewrite E. auto.
            +++ rewrite E in C. discriminate C. 
         ++ exact (abort _ (not_is_left_and_is_right _ rT wT g Pg bT symT transT ilT irT)).
         ++ right. exists ((s1, t3), (s2, t4)).
            compute. rewrite A, D.
            destruct (selS s1 s2) as [E | E].
            +++ rewrite E in A. discriminate A. 
            +++ rewrite E. auto.
         ++ exact (abort _ (not_is_left_and_is_right _ rT wT g Pg bT symT transT ilT irT)).
         ++ right. exists ((s1, t3), (s2, t4)).
            compute. rewrite A, D.
            destruct (selS s1 s2) as [E | E].
            +++ rewrite E in A. discriminate A. 
            +++ rewrite E. auto.
         ++ left. intros [a b] [c d]. compute. 
            rewrite irS. right. apply irT. 
         ++ right. exists ((s1, t3), (s2, t4)).
            compute. rewrite A, D.
            destruct (selS s1 s2) as [E | E].
            +++ rewrite E in A. discriminate A. 
            +++ rewrite E. auto.
         ++ right. exists ((s3, t1), (s4, t2)).
            compute. rewrite B, C.
            destruct (selS s3 s4) as [E | E].
            +++ rewrite E. auto.
            +++ rewrite E in C. discriminate C. 
         ++ right. exists ((s3, t1), (s4, t2)).
            compute. rewrite B, C.
            destruct (selS s3 s4) as [E | E].
            +++ rewrite E. auto.
            +++ rewrite E in C. discriminate C. 
       + right. exists ((wS, t1), (wS, t2)).
         compute. rewrite C, D.
         case_eq(rS (wS *S wS) wS); intro E; auto. 
       + right. exists ((s1, wT), (s2, wT)).
         compute. rewrite A, B; auto. 
       + right. exists ((s1, wT), (s2, wT)).
         compute. rewrite A, B; auto. 
Defined. 

Definition bop_product_selective_decide : 
     bop_is_left_decidable S rS bS  → 
     bop_is_left_decidable T rT bT  → 
     bop_is_right_decidable S rS bS  → 
     bop_is_right_decidable T rT bT  → 
        bop_selective_decidable (S * T) (rS <*> rT) (bS [*] bT)
:= λ dlS dlT drS drT,  
       match dlS, dlT, drS, drT with 
       |                 _,                  _,    inl is_right_S,      inl is_right_T => 
          inl _ (bop_product_selective (inr _ (is_right_S, is_right_T)))

       |     inl is_left_S,      inl is_left_T,                 _,                   _ => 
          inl _ (bop_product_selective (inl _ (is_left_S, is_left_T)))

       | inr not_is_left_S,                  _,                 _,  inr not_is_right_T => 
          inr _ (bop_product_not_selective (inl _ not_is_left_S) 
                                           (inr _ not_is_right_T) 
                                           (inl _ not_is_left_S, inr _ not_is_right_T))

       |                 _,  inr not_is_left_T, inr not_is_right_S,                  _ => 
          inr _ (bop_product_not_selective (inr _ not_is_right_S) 
                                           (inl _ not_is_left_T) 
                                           (inr _ not_is_left_T, inl _ not_is_right_S))
       (* NB : use of abort *) 
       |     inl is_left_S,                  _,    inl is_right_S,                   _ => 
          abort _ (bop_not_left_or_not_right _ _ _ wS f Pf symS transS is_left_S is_right_S)

       |                 _,      inl is_left_T,                 _,      inl is_right_T => 
          abort _ (bop_not_left_or_not_right _ _ _ wT g Pg symT transT is_left_T is_right_T)
       end. 


Definition cef_commutative_product := 
   let (s1, s2) := cef_commutative_implies_not_is_left rS bS wS f in
   let (t1, t2) := cef_commutative_implies_not_is_right rT bT wT g in
   (s1, t1, (s2, t2)).
                     
Lemma bop_product_selective_decide_commutative_case : 
     bop_commutative S rS bS  → 
     bop_commutative T rT bT  → 
         bop_not_selective (S * T) (rS <*> rT) (bS [*] bT).
Proof.  intros commS commT.
        exists cef_commutative_product.
        unfold cef_commutative_product.
        unfold cef_commutative_implies_not_is_left, cef_commutative_implies_not_is_right.
        destruct (Pf wS) as [Lf Rf].
        destruct (Pg wT) as [Lg Rg].
        assert (CS := commS (f wS) wS).
        assert (CT := commT (g wT) wT).         
        case_eq (rS (f wS *S wS) wS); intro H1; case_eq (rT (g wT *T wT) wT); intro H2; 
        unfold brel_product; unfold bop_product; 
        split; apply bop_and_false_intro. 
           left. case_eq (rS (f wS *S wS) (f wS)); intro H3; auto.
                 apply symS in H1. 
                 assert (H6 := transS _ _ _ H1 H3). 
                 rewrite H6 in Lf. 
                 exact Lf. 
           right. case_eq (rT (wT *T g wT) (g wT)); intro H3; auto.
                  apply symT in H2. 
                  assert (H6 := transT _ _ _ (transT _ _ _ H2 CT) H3). 
                  rewrite H6 in Lg. 
                  exact Lg. 
           left. case_eq (rS (f wS *S wS) (f wS)); intro H3; auto.
                 apply symS in H1. 
                 assert (H6 := transS _ _ _ H1 H3). 
                 rewrite H6 in Lf. 
                 exact Lf. 
           right. exact H2. 
           left. case_eq (rS (wS *S f wS) wS); intro H3; auto.
                 assert (H4 := transS _ _ _ CS H3). 
                 rewrite H4 in H1. 
                 exact H1. 
           right. case_eq (rT (wT *T g wT) (g wT)); intro H3; auto.
                  apply symT in H2.                  
                  assert (H4 := transT _ _ _ H2 (transT _ _ _ CT H3)). 
                  rewrite H4 in Lg. 
                  exact Lg. 
           left. case_eq (rS (wS *S f wS) wS); intro H3; auto.
                 assert (H4 := transS _ _ _ CS H3). 
                 rewrite H4 in H1. 
                 exact H1. 
           right. exact H2.
Defined. 
           
End Product. 
End Theory.

Section ACAS.

Definition sg_proofs_product : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T) (s : S) (f : S -> S) (t : T) (g : T -> T), 
     brel_not_trivial S rS f -> brel_not_trivial T rT g -> 
     eqv_proofs S rS -> eqv_proofs T rT -> sg_proofs S rS bS -> sg_proofs T rT bT -> 
        sg_proofs (S * T) (brel_product rS rT) (bop_product bS bT)
:= λ S T rS rT bS bT s f t g Pf Pg eqvS eqvT sgS sgT,
let symS   := A_eqv_symmetric _ _ eqvS in
let refS   := A_eqv_reflexive _ _ eqvS in 
let transS := A_eqv_transitive _ _ eqvS in  
let symT   := A_eqv_symmetric _ _ eqvT in
let refT   := A_eqv_reflexive _ _ eqvT in 
let transT := A_eqv_transitive _ _ eqvT in   
{|
  A_sg_associative   := bop_product_associative S T rS rT bS bT (A_sg_associative _ _ _ sgS) (A_sg_associative _ _ _ sgT) 
; A_sg_congruence    := bop_product_congruence S T rS rT bS bT (A_sg_congruence _ _ _ sgS) (A_sg_congruence _ _ _ sgT) 
; A_sg_commutative_d := bop_product_commutative_decide S T rS rT bS bT s t (A_sg_commutative_d _ _ _ sgS) (A_sg_commutative_d _ _ _ sgT) 
; A_sg_selective_d   := bop_product_selective_decide S T rS rT bS bT s f Pf symS transS t g Pg symT transT
                         (A_sg_is_left_d _ _ _ sgS) 
                         (A_sg_is_left_d _ _ _ sgT) 
                         (A_sg_is_right_d _ _ _ sgS) 
                         (A_sg_is_right_d _ _ _ sgT) 
; A_sg_is_left_d     := bop_product_is_left_decide S T rS rT bS bT s t (A_sg_is_left_d _ _ _ sgS) (A_sg_is_left_d _ _ _ sgT) 
; A_sg_is_right_d    := bop_product_is_right_decide S T rS rT bS bT s t (A_sg_is_right_d _ _ _ sgS) (A_sg_is_right_d _ _ _ sgT) 
; A_sg_idempotent_d  := bop_product_idempotent_decide S T rS rT bS bT s t (A_sg_idempotent_d _ _ _ sgS) (A_sg_idempotent_d _ _ _ sgT) 
; A_sg_left_cancel_d    := bop_product_left_cancellative_decide S T rS rT bS bT s refS t refT
                            (A_sg_left_cancel_d _ _ _ sgS) 
                            (A_sg_left_cancel_d _ _ _ sgT) 
; A_sg_right_cancel_d   := bop_product_right_cancellative_decide S T rS rT bS bT s refS t refT
                            (A_sg_right_cancel_d _ _ _ sgS) 
                            (A_sg_right_cancel_d _ _ _ sgT) 
; A_sg_left_constant_d  := bop_product_left_constant_decide S T rS rT bS bT s t 
                            (A_sg_left_constant_d _ _ _ sgS) 
                            (A_sg_left_constant_d _ _ _ sgT) 
; A_sg_right_constant_d := bop_product_right_constant_decide S T rS rT bS bT s t 
                            (A_sg_right_constant_d _ _ _ sgS) 
                            (A_sg_right_constant_d _ _ _ sgT) 
; A_sg_anti_left_d      := bop_product_anti_left_decide S T rS rT bS bT (A_sg_anti_left_d _ _ _ sgS) (A_sg_anti_left_d _ _ _ sgT) 
; A_sg_anti_right_d     := bop_product_anti_right_decide S T rS rT bS bT (A_sg_anti_right_d _ _ _ sgS) (A_sg_anti_right_d _ _ _ sgT) 
|}.

(*  
Definition asg_proofs_product : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T) (s : S) (f : S -> S) (t : T) (g : T -> T), 
     brel_not_trivial S rS f -> brel_not_trivial T rT g -> 
     eqv_proofs S rS -> eqv_proofs T rT -> asg_proofs S rS bS -> asg_proofs T rT bT -> 
        asg_proofs (S * T) (brel_product rS rT) (bop_product bS bT)
:= λ S T rS rT bS bT s f t g Pf Pg eqvS eqvT sgS sgT,
let symS   := A_eqv_symmetric _ _ eqvS in
let refS   := A_eqv_reflexive _ _ eqvS in 
let transS := A_eqv_transitive _ _ eqvS in  
let symT   := A_eqv_symmetric _ _ eqvT in
let refT   := A_eqv_reflexive _ _ eqvT in 
let transT := A_eqv_transitive _ _ eqvT in
let commS  := A_asg_commutative _ _ _ sgS in
let commT  := A_asg_commutative _ _ _ sgT in 
{|
  A_asg_associative   := bop_product_associative S T rS rT bS bT (A_asg_associative _ _ _ sgS) (A_asg_associative _ _ _ sgT) 
; A_asg_congruence    := bop_product_congruence S T rS rT bS bT (A_asg_congruence _ _ _ sgS) (A_asg_congruence _ _ _ sgT) 
; A_asg_commutative   := bop_product_commutative S T rS rT bS bT commS commT 
; A_asg_selective_d   := inr (bop_product_selective_decide_commutative_case S T rS rT bS bT s f Pf symS transS t g Pg symT transT commS commT) 
; A_asg_idempotent_d  := bop_product_idempotent_decide S T rS rT bS bT s t (A_asg_idempotent_d _ _ _ sgS) (A_asg_idempotent_d _ _ _ sgT) 
|}.


Definition msg_proofs_product : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T) (s : S) (f : S -> S) (t : T) (g : T -> T), 
     brel_not_trivial S rS f -> brel_not_trivial T rT g -> 
     eqv_proofs S rS -> eqv_proofs T rT -> msg_proofs S rS bS -> msg_proofs T rT bT -> 
        msg_proofs (S * T) (brel_product rS rT) (bop_product bS bT)
:= λ S T rS rT bS bT s f t g Pf Pg eqvS eqvT sgS sgT,
let symS   := A_eqv_symmetric _ _ eqvS in
let refS   := A_eqv_reflexive _ _ eqvS in 
let transS := A_eqv_transitive _ _ eqvS in  
let symT   := A_eqv_symmetric _ _ eqvT in
let refT   := A_eqv_reflexive _ _ eqvT in 
let transT := A_eqv_transitive _ _ eqvT in   
{|
  A_msg_associative   := bop_product_associative S T rS rT bS bT (A_msg_associative _ _ _ sgS) (A_msg_associative _ _ _ sgT) 
; A_msg_congruence    := bop_product_congruence S T rS rT bS bT (A_msg_congruence _ _ _ sgS) (A_msg_congruence _ _ _ sgT) 
; A_msg_commutative_d := bop_product_commutative_decide S T rS rT bS bT s t (A_msg_commutative_d _ _ _ sgS) (A_msg_commutative_d _ _ _ sgT) 
; A_msg_is_left_d     := bop_product_is_left_decide S T rS rT bS bT s t (A_msg_is_left_d _ _ _ sgS) (A_msg_is_left_d _ _ _ sgT) 
; A_msg_is_right_d    := bop_product_is_right_decide S T rS rT bS bT s t (A_msg_is_right_d _ _ _ sgS) (A_msg_is_right_d _ _ _ sgT) 
; A_msg_left_cancel_d    := bop_product_left_cancellative_decide S T rS rT bS bT s refS t refT
                            (A_msg_left_cancel_d _ _ _ sgS) 
                            (A_msg_left_cancel_d _ _ _ sgT) 
; A_msg_right_cancel_d   := bop_product_right_cancellative_decide S T rS rT bS bT s refS t refT
                            (A_msg_right_cancel_d _ _ _ sgS) 
                            (A_msg_right_cancel_d _ _ _ sgT) 
; A_msg_left_constant_d  := bop_product_left_constant_decide S T rS rT bS bT s t 
                            (A_msg_left_constant_d _ _ _ sgS) 
                            (A_msg_left_constant_d _ _ _ sgT) 
; A_msg_right_constant_d := bop_product_right_constant_decide S T rS rT bS bT s t 
                            (A_msg_right_constant_d _ _ _ sgS) 
                            (A_msg_right_constant_d _ _ _ sgT) 
; A_msg_anti_left_d      := bop_product_anti_left_decide S T rS rT bS bT (A_msg_anti_left_d _ _ _ sgS) (A_msg_anti_left_d _ _ _ sgT) 
; A_msg_anti_right_d     := bop_product_anti_right_decide S T rS rT bS bT (A_msg_anti_right_d _ _ _ sgS) (A_msg_anti_right_d _ _ _ sgT) 
|}.

*) 
Definition sg_C_proofs_product : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T) (s : S) (f : S -> S) (t : T) (g : T -> T), 
     brel_not_trivial S rS f -> brel_not_trivial T rT g -> 
     eqv_proofs S rS -> eqv_proofs T rT -> sg_C_proofs S rS bS -> sg_C_proofs T rT bT -> 
        sg_C_proofs (S * T) (brel_product rS rT) (bop_product bS bT)
:= λ S T rS rT bS bT s f t g Pf Pg eqvS eqvT sgS sgT,
let symS   := A_eqv_symmetric _ _ eqvS in
let refS   := A_eqv_reflexive _ _ eqvS in 
let transS := A_eqv_transitive _ _ eqvS in   
let symT   := A_eqv_symmetric _ _ eqvT in
let refT   := A_eqv_reflexive _ _ eqvT in 
let transT := A_eqv_transitive _ _ eqvT in
let commS := A_sg_C_commutative _ _ _ sgS in
let commT := A_sg_C_commutative _ _ _ sgT in 
{|
  A_sg_C_associative   := bop_product_associative S T rS rT bS bT (A_sg_C_associative _ _ _ sgS) (A_sg_C_associative _ _ _ sgT) 
; A_sg_C_congruence    := bop_product_congruence S T rS rT bS bT (A_sg_C_congruence _ _ _ sgS) (A_sg_C_congruence _ _ _ sgT) 
; A_sg_C_commutative   := bop_product_commutative S T rS rT bS bT commS commT 
; A_sg_C_selective_d   := inr (bop_product_selective_decide_commutative_case S T rS rT bS bT s f Pf symS transS t g Pg symT transT commS commT) 
; A_sg_C_idempotent_d  := bop_product_idempotent_decide S T rS rT bS bT s t (A_sg_C_idempotent_d _ _ _ sgS) (A_sg_C_idempotent_d _ _ _ sgT) 
; A_sg_C_cancel_d      := bop_product_left_cancellative_decide S T rS rT bS bT s refS t refT
                            (A_sg_C_cancel_d _ _ _ sgS) 
                            (A_sg_C_cancel_d _ _ _ sgT) 
; A_sg_C_constant_d    := bop_product_left_constant_decide S T rS rT bS bT s t 
                            (A_sg_C_constant_d _ _ _ sgS) 
                            (A_sg_C_constant_d _ _ _ sgT) 
; A_sg_C_anti_left_d      := bop_product_anti_left_decide S T rS rT bS bT (A_sg_C_anti_left_d _ _ _ sgS) (A_sg_C_anti_left_d _ _ _ sgT) 
; A_sg_C_anti_right_d     := bop_product_anti_right_decide S T rS rT bS bT (A_sg_C_anti_right_d _ _ _ sgS) (A_sg_C_anti_right_d _ _ _ sgT) 
|}. 

Definition sg_CI_proofs_product : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T) (s : S) (f : S -> S) (t : T) (g : T -> T), 
     brel_not_trivial S rS f -> brel_not_trivial T rT g -> 
     eqv_proofs S rS -> eqv_proofs T rT -> sg_CI_proofs S rS bS -> sg_CI_proofs T rT bT -> 
        sg_CI_proofs (S * T) (brel_product rS rT) (bop_product bS bT)
:= λ S T rS rT bS bT s f t g Pf Pg eqvS eqvT sgS sgT,
let symS   := A_eqv_symmetric _ _ eqvS in
let refS   := A_eqv_reflexive _ _ eqvS in 
let transS := A_eqv_transitive _ _ eqvS in   
let symT   := A_eqv_symmetric _ _ eqvT in
let refT   := A_eqv_reflexive _ _ eqvT in 
let transT := A_eqv_transitive _ _ eqvT in
let commS := A_sg_CI_commutative _ _ _ sgS in
let commT := A_sg_CI_commutative _ _ _ sgT in 
{|
  A_sg_CI_associative   := bop_product_associative S T rS rT bS bT (A_sg_CI_associative _ _ _ sgS) (A_sg_CI_associative _ _ _ sgT) 
; A_sg_CI_congruence    := bop_product_congruence S T rS rT bS bT (A_sg_CI_congruence _ _ _ sgS) (A_sg_CI_congruence _ _ _ sgT) 
; A_sg_CI_commutative   := bop_product_commutative S T rS rT bS bT (A_sg_CI_commutative _ _ _ sgS) (A_sg_CI_commutative _ _ _ sgT) 
; A_sg_CI_idempotent    := bop_product_idempotent S T rS rT bS bT (A_sg_CI_idempotent _ _ _ sgS) (A_sg_CI_idempotent _ _ _ sgT) 
; A_sg_CI_not_selective := bop_product_selective_decide_commutative_case S T rS rT bS bT s f Pf symS transS t g Pg symT transT commS commT
|}. 



Definition sg_CI_proofs_product_from_sg_CS_proofs 
    (S T : Type)
    (rS : brel S)
    (rT : brel T)
    (bS : binary_op S)
    (bT: binary_op T)
    (s : S)
    (f : S -> S)
    (t : T)
    (g : T -> T)
    (Pf : brel_not_trivial S rS f)
    (Pg : brel_not_trivial T rT g) 
    (eqvS : eqv_proofs S rS)
    (eqvT : eqv_proofs T rT)
    (sgS : sg_CS_proofs S rS bS)
    (sgT : sg_CS_proofs T rT bT) : sg_CI_proofs (S * T) (brel_product rS rT) (bop_product bS bT) := 
let symS   := A_eqv_symmetric _ _ eqvS in
let refS   := A_eqv_reflexive _ _ eqvS in 
let transS := A_eqv_transitive _ _ eqvS in   
let symT   := A_eqv_symmetric _ _ eqvT in
let refT   := A_eqv_reflexive _ _ eqvT in 
let transT := A_eqv_transitive _ _ eqvT in
let commS := A_sg_CS_commutative _ _ _ sgS in
let commT := A_sg_CS_commutative _ _ _ sgT in
let idemS := bop_selective_implies_idempotent _ _ _ (A_sg_CS_selective _ _ _ sgS) in
let idemT := bop_selective_implies_idempotent _ _ _ (A_sg_CS_selective _ _ _ sgT) in 
{|
  A_sg_CI_associative   := bop_product_associative S T rS rT bS bT (A_sg_CS_associative _ _ _ sgS) (A_sg_CS_associative _ _ _ sgT) 
; A_sg_CI_congruence    := bop_product_congruence S T rS rT bS bT (A_sg_CS_congruence _ _ _ sgS) (A_sg_CS_congruence _ _ _ sgT) 
; A_sg_CI_commutative   := bop_product_commutative S T rS rT bS bT (A_sg_CS_commutative _ _ _ sgS) (A_sg_CS_commutative _ _ _ sgT) 
; A_sg_CI_idempotent    := bop_product_idempotent S T rS rT bS bT idemS idemT 
; A_sg_CI_not_selective := bop_product_selective_decide_commutative_case S T rS rT bS bT s f Pf symS transS t g Pg symT transT commS commT
|}. 

(*
Definition sg_CK_proofs_product : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T) (bS : binary_op S) (bT: binary_op T),
     eqv_proofs S rS -> eqv_proofs T rT -> sg_CK_proofs S rS bS -> sg_CK_proofs T rT bT -> 
        sg_CK_proofs (S * T) (brel_product rS rT) (bop_product bS bT)
:= λ S T rS rT bS bT eqvS eqvT sgS sgT, 
{|
  A_sg_CK_associative        := bop_product_associative S T rS rT bS bT (A_sg_CK_associative _ _ _ sgS) (A_sg_CK_associative _ _ _ sgT) 
; A_sg_CK_congruence         := bop_product_congruence S T rS rT bS bT (A_sg_CK_congruence _ _ _ sgS) (A_sg_CK_congruence _ _ _ sgT) 
; A_sg_CK_commutative        := bop_product_commutative S T rS rT bS bT (A_sg_CK_commutative _ _ _ sgS) (A_sg_CK_commutative _ _ _ sgT) 
; A_sg_CK_cancel             := bop_product_left_cancellative S T rS rT bS bT (A_sg_CK_cancel _ _ _ sgS) (A_sg_CK_cancel _ _ _ sgT) 

; A_sg_CK_anti_left_d        := bop_product_anti_left_decide S T rS rT bS bT (A_sg_CK_anti_left_d _ _ _ sgS) (A_sg_CK_anti_left_d _ _ _ sgT) 
; A_sg_CK_anti_right_d       := bop_product_anti_right_decide S T rS rT bS bT (A_sg_CK_anti_right_d _ _ _ sgS) (A_sg_CK_anti_right_d _ _ _ sgT) 
|}. 
*) 

(**************************************************************************************)

Definition A_sg_product : ∀ (S T : Type),  A_sg S -> A_sg T -> A_sg (S * T) 
:= λ S T sgS sgT,
let eqvS := A_sg_eqv S sgS   in
let eqvT := A_sg_eqv T sgT   in
let eqS  := A_eqv_eq S eqvS in
let eqT  := A_eqv_eq T eqvT in  
let bS   := A_sg_bop S sgS  in
let bT   := A_sg_bop T sgT  in 
{| 
       A_sg_eqv              := A_eqv_product S T eqvS eqvT
     ; A_sg_bop           := bop_product bS bT
     ; A_sg_exists_id_d   := bop_product_exists_id_decide S T eqS eqT bS bT (A_sg_exists_id_d _ sgS) (A_sg_exists_id_d _ sgT) 
     ; A_sg_exists_ann_d  :=  bop_product_exists_ann_decide S T eqS eqT bS bT (A_sg_exists_ann_d _ sgS) (A_sg_exists_ann_d _ sgT) 
     ; A_sg_proofs := sg_proofs_product S T eqS eqT bS bT
                           (A_eqv_witness S eqvS) 
                           (A_eqv_new S eqvS) 
                           (A_eqv_witness T eqvT)
                           (A_eqv_new T eqvT)
                           (A_eqv_not_trivial S eqvS)                                                                                  
                           (A_eqv_not_trivial T eqvT)                                                       
                           (A_eqv_proofs S eqvS) 
                           (A_eqv_proofs T eqvT) 
                           (A_sg_proofs S sgS) 
                           (A_sg_proofs T sgT)
   
   ; A_sg_ast       := Ast_sg_product (A_sg_ast S sgS, A_sg_ast T sgT)
   |}. 

(*
Definition A_sg_C_product : ∀ (S T : Type),  A_sg_C S -> A_sg_C T -> A_sg_C (S * T) 
:= λ S T sgS sgT,
let eqvS := A_sg_C_eqv S sgS in
let eqvT := A_sg_C_eqv T sgT in
let eqS  := A_eqv_eq S eqvS in
let eqT  := A_eqv_eq T eqvT in  
let bS   := A_sg_C_bop S sgS in
let bT   := A_sg_C_bop T sgT in 
{| 
     A_sg_C_eqv         := A_eqv_product S T eqvS eqvT  
   ; A_sg_C_bop         := bop_product bS bT
   ; A_sg_C_exists_id_d   := bop_product_exists_id_decide S T eqS eqT bS bT (A_sg_C_exists_id_d _ sgS) (A_sg_C_exists_id_d _ sgT) 
   ; A_sg_C_exists_ann_d  := bop_product_exists_ann_decide S T eqS eqT bS bT (A_sg_C_exists_ann_d _ sgS) (A_sg_C_exists_ann_d _ sgT) 
   ; A_sg_C_proofs := sg_C_proofs_product S T eqS eqT bS bT
                           (A_eqv_witness S eqvS) 
                           (A_eqv_new S eqvS) 
                           (A_eqv_witness T eqvT)
                           (A_eqv_new T eqvT)
                           (A_eqv_not_trivial S eqvS)                                                                                  
                           (A_eqv_not_trivial T eqvT)                                                       
                           (A_eqv_proofs S eqvS)
                           (A_eqv_proofs T eqvT)                            
                           (A_sg_C_proofs S sgS) 
                           (A_sg_C_proofs T sgT) 
   
   ; A_sg_C_ast       := Ast_sg_product (A_sg_C_ast S sgS, A_sg_C_ast T sgT)
   |}. 

Definition A_sg_CI_product : ∀ (S T : Type),  A_sg_CI S -> A_sg_CI T -> A_sg_CI (S * T) 
:= λ S T sgS sgT,
let eqvS := A_sg_CI_eqv S sgS in
let eqvT := A_sg_CI_eqv T sgT in
let eqS  := A_eqv_eq S eqvS in
let eqT  := A_eqv_eq T eqvT in  
let bS   := A_sg_CI_bop S sgS in
let bT   := A_sg_CI_bop T sgT in 
{| 
     A_sg_CI_eqv    := A_eqv_product S T eqvS eqvT 
   ; A_sg_CI_bop    := bop_product bS bT
   ; A_sg_CI_exists_id_d   := bop_product_exists_id_decide S T eqS eqT bS bT (A_sg_CI_exists_id_d _ sgS) (A_sg_CI_exists_id_d _ sgT) 
   ; A_sg_CI_exists_ann_d  := bop_product_exists_ann_decide S T eqS eqT bS bT (A_sg_CI_exists_ann_d _ sgS) (A_sg_CI_exists_ann_d _ sgT) 
   ; A_sg_CI_proofs := sg_CI_proofs_product S T eqS eqT bS bT
                           (A_eqv_witness S eqvS) 
                           (A_eqv_new S eqvS) 
                           (A_eqv_witness T eqvT)
                           (A_eqv_new T eqvT)
                           (A_eqv_not_trivial S eqvS)                                                                                  
                           (A_eqv_not_trivial T eqvT)                                                       
                           (A_eqv_proofs S eqvS)
                           (A_eqv_proofs T eqvT)
                           (A_sg_CI_proofs S sgS) 
                           (A_sg_CI_proofs T sgT)
   
   ; A_sg_CI_ast       := Ast_sg_product (A_sg_CI_ast S sgS, A_sg_CI_ast T sgT)
   |}. 


Definition A_sg_CK_product : ∀ (S T : Type),  A_sg_CK S -> A_sg_CK T -> A_sg_CK (S * T) 
:= λ S T sgS sgT,
let eqvS := A_sg_CK_eqv S sgS in
let eqvT := A_sg_CK_eqv T sgT in
let eqS  := A_eqv_eq S eqvS in
let eqT  := A_eqv_eq T eqvT in  
let bS   := A_sg_CK_bop S sgS in
let bT   := A_sg_CK_bop T sgT in 
{| 
     A_sg_CK_eqv    := A_eqv_product S T eqvS eqvT 
   ; A_sg_CK_bop    := bop_product bS bT
   ; A_sg_CK_exists_id_d   := bop_product_exists_id_decide S T eqS eqT bS bT (A_sg_CK_exists_id_d _ sgS) (A_sg_CK_exists_id_d _ sgT)   
   ; A_sg_CK_proofs := sg_CK_proofs_product S T (A_eqv_eq S eqvS) (A_eqv_eq T eqvT) bS bT
                           (A_eqv_proofs S eqvS)
                           (A_eqv_proofs T eqvT)
                           (A_sg_CK_proofs S sgS) 
                           (A_sg_CK_proofs T sgT)
   
   ; A_sg_CK_ast       := Ast_sg_product (A_sg_CK_ast S sgS, A_sg_CK_ast T sgT)
   |}. 

*)   
End ACAS.

Section AMCAS.

  (*
Open Scope list_scope.
Open Scope string_scope.

Definition mcas_sg_proofs_product 
           (S T : Type)
           (eqS : brel S) (eqT : brel T)
           (wS : S) (wT : T)
           (f : S -> S) (g : T -> T)
           (ntS : brel_not_trivial S eqS f)
           (ntT : brel_not_trivial T eqT g)           
           (eqvPS : eqv_proofs S eqS)
           (eqvPT : eqv_proofs T eqT)            
           (bS : binary_op S) (bT : binary_op T)
           (id_dS : bop_exists_id_decidable S eqS bS)
           (id_dT : bop_exists_id_decidable T eqT bT)           
           (PS : sg_proofs_mcas S eqS bS) 
           (PT : sg_proofs_mcas T eqT bT) : sg_proofs_mcas (S * T) (brel_product eqS eqT) (bop_product bS bT) := 
match A_sg_proofs_mcas_cast_up S eqS wS f ntS eqvPS bS id_dS PS,
      A_sg_proofs_mcas_cast_up T eqT wT g ntT eqvPT bT id_dT PT with 
| A_MCAS_Proof_sg _ _ _ A', A_MCAS_Proof_sg _ _ _ B' =>
     sg_proof_classify _ _ _ (A_MCAS_Proof_sg _ _ _ (sg_proofs_product S T eqS eqT bS bT wS f wT g ntS ntT eqvPS eqvPT A' B'))
| A_MCAS_Proof_sg_Error _ _ _ sl1, A_MCAS_Proof_sg_Error _ _ _ sl2 => A_MCAS_Proof_sg_Error _ _ _ (sl1 ++ sl2)
| A_MCAS_Proof_sg_Error _ _ _ sl1, _  => A_MCAS_Proof_sg_Error _ _ _ sl1
| _,  A_MCAS_Proof_sg_Error _ _ _ sl2 => A_MCAS_Proof_sg_Error _ _ _ sl2
| _, _                                => A_MCAS_Proof_sg_Error _ _ _ ("Internal Error : mcas_sg_proofs_product" :: nil)
end.
*) 

  Definition A_sg_product_below_sg {S T : Type} (A : @A_below_sg S)  (B : @A_below_sg T)  : @A_below_sg (S * T) :=
    A_classify_sg (A_sg_product _ _ (A_cast_up_sg A) (A_cast_up_sg B)).

  
  Definition A_mcas_sg_product {S T : Type} (A : @A_sg_mcas S)  (B : @A_sg_mcas T)  : @A_sg_mcas (S * T) :=
    match A, B with
    | A_MCAS_sg A', A_MCAS_sg B'               => A_MCAS_sg (A_sg_product_below_sg A' B')
    | A_MCAS_sg_Error sl1, A_MCAS_sg_Error sl2 => A_MCAS_sg_Error (sl1 ++ sl2)
    | A_MCAS_sg_Error sl1, _                   => A_MCAS_sg_Error sl1
    | _,  A_MCAS_sg_Error sl2                  => A_MCAS_sg_Error sl2
    end.

End AMCAS.

Section CAS.

Definition check_commutative_product : ∀ {S T : Type} 
             (s : S) 
             (t : T), 
             (check_commutative (S := S)) -> 
             (check_commutative (S := T)) -> 
                (check_commutative (S := (S * T)))
:= λ {S T} s t cS cT,  
      match cS, cT with 
      | Certify_Commutative, Certify_Commutative => Certify_Commutative 
      | Certify_Not_Commutative (s1, s2), _      => Certify_Not_Commutative ((s1, t), (s2, t))
      | _, Certify_Not_Commutative (t1, t2)      => Certify_Not_Commutative ((s, t1), (s, t2))
      end.


Definition check_left_cancellative_product : ∀ {S T : Type} 
             (s : S) 
             (t : T), 
             (check_left_cancellative (S := S)) -> 
             (check_left_cancellative (S := T)) -> 
                (check_left_cancellative (S := (S * T)))
:= λ {S T} s t cS cT,  
      match cS, cT with 
      | Certify_Left_Cancellative, Certify_Left_Cancellative => Certify_Left_Cancellative
      | Certify_Not_Left_Cancellative (s1, (s2, s3)), _ => 
           Certify_Not_Left_Cancellative ((s1, t), ((s2, t), (s3, t)))
      | _, Certify_Not_Left_Cancellative (t1, (t2, t3))  => 
           Certify_Not_Left_Cancellative ((s, t1), ((s, t2), (s, t3)))
      end. 


Definition check_right_cancellative_product : ∀ {S T : Type} 
             (s : S) 
             (t : T), 
             (check_right_cancellative (S := S)) -> 
             (check_right_cancellative (S := T)) -> 
                (check_right_cancellative (S := (S * T)))
:= λ {S T} s t cS cT,  
      match cS, cT with 
      | Certify_Right_Cancellative , Certify_Right_Cancellative => Certify_Right_Cancellative
      | Certify_Not_Right_Cancellative (s1, (s2, s3)), _ => 
           Certify_Not_Right_Cancellative ((s1, t), ((s2, t), (s3, t)))
      | _, Certify_Not_Right_Cancellative (t1, (t2, t3))  => 
           Certify_Not_Right_Cancellative ((s, t1), ((s, t2), (s, t3)))
      end .

Definition check_left_constant_product : ∀ {S T : Type} 
             (s : S) 
             (t : T), 
             (check_left_constant (S := S)) -> 
             (check_left_constant (S := T)) -> 
                (check_left_constant (S := (S * T)))
:= λ {S T} s t cS cT,  
      match cS, cT with 
      | Certify_Left_Constant, Certify_Left_Constant => Certify_Left_Constant
      | Certify_Not_Left_Constant (s1, (s2, s3)), _ => 
           Certify_Not_Left_Constant ((s1, t), ((s2, t), (s3, t)))
      | _, Certify_Not_Left_Constant (t1, (t2, t3))  => 
           Certify_Not_Left_Constant ((s, t1), ((s, t2), (s, t3)))
      end .



Definition check_right_constant_product : ∀ {S T : Type} 
             (s : S) 
             (t : T), 
             (check_right_constant (S := S)) -> 
             (check_right_constant (S := T)) -> 
                (check_right_constant (S := (S * T)))
:= λ {S T} s t cS cT,  
      match cS, cT with 
      | Certify_Right_Constant, Certify_Right_Constant => Certify_Right_Constant
      | Certify_Not_Right_Constant (s1, (s2, s3)), _ => 
           Certify_Not_Right_Constant ((s1, t), ((s2, t), (s3, t)))
      | _, Certify_Not_Right_Constant (t1, (t2, t3))  => 
           Certify_Not_Right_Constant ((s, t1), ((s, t2), (s, t3)))
      end .


Definition check_anti_left_product : 
   ∀ {S T : Type},  check_anti_left (S := S) -> check_anti_left (S := T) -> check_anti_left (S := (S * T)) 
:= λ {S T} dS dT,  
   match dS with 
   | Certify_Anti_Left => Certify_Anti_Left 
   | Certify_Not_Anti_Left (s1, s2)  => 
     match dT with 
     | Certify_Anti_Left => Certify_Anti_Left 
     | Certify_Not_Anti_Left (t1, t2)  => Certify_Not_Anti_Left ((s1, t1), (s2, t2))
     end 
   end. 

Definition check_anti_right_product : 
   ∀ {S T : Type},  check_anti_right (S := S) -> check_anti_right (S := T) -> check_anti_right (S := (S * T)) 
:= λ {S T} dS dT,  
   match dS with 
   | Certify_Anti_Right  => Certify_Anti_Right 
   | Certify_Not_Anti_Right (s1, s2)  => 
     match dT with 
     | Certify_Anti_Right => Certify_Anti_Right 
     | Certify_Not_Anti_Right (t1, t2)  => Certify_Not_Anti_Right ((s1, t1), (s2, t2))
     end 
   end. 

Definition check_idempotent_product : ∀ {S T : Type}
             (s : S) 
             (t : T), 
             (check_idempotent (S := S)) -> 
             (check_idempotent (S := T)) -> 
                (check_idempotent (S := (S * T)))
:= λ {S T} s t cS cT,  
      match cS, cT with 
      | Certify_Idempotent, Certify_Idempotent => Certify_Idempotent 
      | Certify_Not_Idempotent s1 , _       => Certify_Not_Idempotent (s1, t) 
      | _, Certify_Not_Idempotent t1        => Certify_Not_Idempotent (s, t1) 
      end.

Definition check_is_left_product : ∀ {S T : Type}
             (s : S) 
             (t : T), 
             (check_is_left (S := S)) -> 
             (check_is_left (S := T)) -> 
                (check_is_left (S := (S * T)))
:= λ {S T} s t cS cT,  
      match cS, cT with 
      | Certify_Is_Left, Certify_Is_Left => Certify_Is_Left 
      | Certify_Not_Is_Left (s1, s2), _  => Certify_Not_Is_Left ((s1, t), (s2, t))
      | _, Certify_Not_Is_Left (t1, t2)  => Certify_Not_Is_Left ((s, t1), (s, t2))
      end.  


Definition check_is_right_product : ∀ {S T : Type} 
             (s : S) 
             (t : T), 
             (check_is_right (S := S)) -> 
             (check_is_right (S := T)) -> 
                (check_is_right (S := (S * T)))
:= λ {S T} s t cS cT,  
      match cS, cT with 
      | Certify_Is_Right, Certify_Is_Right => Certify_Is_Right 
      | Certify_Not_Is_Right (s1, s2), _   => Certify_Not_Is_Right ((s1, t), (s2, t))
      | _, Certify_Not_Is_Right (t1, t2)   => Certify_Not_Is_Right ((s, t1), (s, t2))
      end.


Definition check_not_selective_product : ∀ {S T : Type},
             (assert_not_is_left (S := S)) -> 
             (assert_not_is_right (S := T)) -> (check_selective (S := (S * T)))
:= λ {S T} nlS nrT,  
     match nlS, nrT with 
     | Assert_Not_Is_Left (s1, s2), Assert_Not_Is_Right (t1, t2) => 
          Certify_Not_Selective ((s1, t1), (s2, t2))  
     end. 


Definition check_selective_product : ∀ {S T : Type}
             (s : S) 
             (t : T), 
             (check_is_left (S := S)) -> 
             (check_is_left (S := T)) -> 
             (check_is_right (S := S)) -> 
             (check_is_right (S := T)) -> 
                (check_selective (S := (S * T)))
:= λ {S T} s t clS clT crS crT,  
     match clS with 
     | Certify_Not_Is_Left (s1, s2) => 
       (* NOT LEFT S *) 
       match crS with 
       | Certify_Is_Right =>  
         (* RIGHT S *) 
           match crT with 
           | Certify_Is_Right => 
             (* RIGHT T *)   Certify_Selective 
           | Certify_Not_Is_Right (t1, t2) => 
             (* NOT RIGHT T *) Certify_Not_Selective ((s1, t1), (s2, t2)) 
           end 
       | Certify_Not_Is_Right (s3, s4) =>  
          (* NOT RIGHT S *)   (* extra case *) 
           match crT with 
           | Certify_Is_Right => 
             (* RIGHT T *) (* MUST BE NOT LEFT T *) 
              match clT with 
              | Certify_Is_Left => (* NOT POSSIBLE *) Certify_Selective 
              | Certify_Not_Is_Left (t1, t2) => Certify_Not_Selective ((s3, t1), (s4, t2))
              end 
           | Certify_Not_Is_Right (t1, t2) => 
             (* NOT RIGHT T *)  
             match clT with  (* why needed ??  to match proof!  clean up! *) 
             | Certify_Is_Left => Certify_Not_Selective ((s1, t1), (s2, t2))  
             | Certify_Not_Is_Left (t3, t4) => Certify_Not_Selective ((s1, t1), (s2, t2))
             end 
           end 
       end 
     | Certify_Is_Left => 
       (* LEFT S *) 
       match clT with 
       | Certify_Is_Left =>  
         (* LEFT T *) Certify_Selective
       | Certify_Not_Is_Left (t1, t2) =>  
         (* NOT LEFT T *) 
           match crT with 
           | Certify_Is_Right => 
             (* RIGHT T *) 
                match crS with 
                | Certify_Is_Right =>   (* CAN'T HAPPEN with not-trivial S *) 
                  (* RIGHT S *)  Certify_Selective 
                | Certify_Not_Is_Right (s1, s2) => 
                  (* NOT RIGHT S *) Certify_Not_Selective ((s1, t1), (s2, t2))  
                end 
           | Certify_Not_Is_Right (t3, t4) => 
             (* NOT RIGHT T *) (* extra case *) 
             match crS with 
             | Certify_Is_Right => 
               (* RIGHT S *) (* MUST BE NOT LEFT S *) 
                match clS with 
                | Certify_Is_Left  => (* NOT POSSIBLE *) Certify_Selective 
                | Certify_Not_Is_Left  (s1, s2) => Certify_Not_Selective ((s1, t3), (s2, t4))
                end 
             | Certify_Not_Is_Right (s1, s2) => 
               (* NOT RIGHT S *)  Certify_Not_Selective ((s1, t1), (s2, t2))  
             end 
          end 
       end 
     end.


Definition assert_exists_id_product : ∀ {S T : Type}, 
             (assert_exists_id (S := S)) -> (assert_exists_id (S := T)) -> assert_exists_id (S := (S * T))
:= λ {S T} cS cT,  
      match cS, cT with 
      | Assert_Exists_Id s, Assert_Exists_Id t  => Assert_Exists_Id (s, t) 
      end. 


Definition check_exists_id_product : ∀ {S T : Type}, 
             (check_exists_id (S := S)) -> (check_exists_id (S := T)) -> (check_exists_id (S := (S * T)))
:= λ {S T} cS cT,  
      match cS, cT with 
      | Certify_Exists_Id s, Certify_Exists_Id t  => Certify_Exists_Id (s, t) 
      | Certify_Not_Exists_Id , _                 => Certify_Not_Exists_Id
      | _, Certify_Not_Exists_Id                  => Certify_Not_Exists_Id
      end. 

Definition check_exists_ann_product : ∀ {S T : Type}, 
             (check_exists_ann (S := S)) -> (check_exists_ann (S := T)) -> (check_exists_ann (S := (S * T)))
:= λ {S T} cS cT,  
      match cS, cT with 
      | Certify_Exists_Ann s, Certify_Exists_Ann t => Certify_Exists_Ann (s, t) 
      | Certify_Not_Exists_Ann, _                  => Certify_Not_Exists_Ann 
      | _, Certify_Not_Exists_Ann                  => Certify_Not_Exists_Ann 
      end. 

Definition sg_certs_product : ∀ {S T : Type},  S -> T -> sg_certificates (S := S) -> sg_certificates (S := T) -> sg_certificates (S := (S * T)) 
:= λ {S T} wS wT cS cT,  
{|
  sg_associative   := Assert_Associative   
; sg_congruence    := Assert_Bop_Congruence   
; sg_commutative_d := check_commutative_product wS wT 
                         (sg_commutative_d cS) 
                         (sg_commutative_d cT)
; sg_selective_d   := check_selective_product wS wT 
                         (sg_is_left_d cS) 
                         (sg_is_left_d cT)
                         (sg_is_right_d cS) 
                         (sg_is_right_d cT)
; sg_is_left_d     := check_is_left_product wS wT 
                         (sg_is_left_d cS) 
                         (sg_is_left_d cT)
; sg_is_right_d    := check_is_right_product wS wT 
                         (sg_is_right_d cS) 
                         (sg_is_right_d cT)
; sg_idempotent_d  := check_idempotent_product wS wT 
                         (sg_idempotent_d cS) 
                         (sg_idempotent_d cT)
; sg_left_cancel_d    := check_left_cancellative_product wS wT 
                          (sg_left_cancel_d cS)
                          (sg_left_cancel_d cT)
; sg_right_cancel_d   := check_right_cancellative_product wS wT 
                          (sg_right_cancel_d cS)
                          (sg_right_cancel_d cT)
; sg_left_constant_d  := check_left_constant_product wS wT 
                          (sg_left_constant_d cS)
                          (sg_left_constant_d cT)
; sg_right_constant_d := check_right_constant_product wS wT 
                          (sg_right_constant_d cS)
                          (sg_right_constant_d cT)
; sg_anti_left_d      := check_anti_left_product 
                         (sg_anti_left_d cS) 
                         (sg_anti_left_d cT)
; sg_anti_right_d     := check_anti_right_product 
                         (sg_anti_right_d cS) 
                         (sg_anti_right_d cT)
|}.

(*
Definition asg_certs_product : ∀ {S T : Type},  (brel S) -> (brel T) -> (binary_op S) -> (binary_op T) ->
                                                  S -> (S -> S) -> T -> (T -> T) -> asg_certificates (S := S) -> asg_certificates (S := T) -> asg_certificates (S := (S * T)) 
:= λ {S T} rS rT bS bT wS f wT g cS cT,  
{|
  asg_associative   := Assert_Associative   
; asg_congruence    := Assert_Bop_Congruence   
; asg_commutative   := Assert_Commutative 
; asg_selective_d   := Certify_Not_Selective (cef_commutative_product S T rS rT bS bT wS f wT g)
; asg_idempotent_d  := check_idempotent_product wS wT 
                         (asg_idempotent_d cS) 
                         (asg_idempotent_d cT)
|}.



Definition msg_certs_product : ∀ {S T : Type},  S -> T -> msg_certificates (S := S) -> msg_certificates (S := T) -> msg_certificates (S := (S * T)) 
:= λ {S T} wS wT cS cT,  
{|
  msg_associative   := Assert_Associative   
; msg_congruence    := Assert_Bop_Congruence   
; msg_commutative_d := check_commutative_product wS wT 
                         (msg_commutative_d cS) 
                         (msg_commutative_d cT)
; msg_is_left_d     := check_is_left_product wS wT 
                         (msg_is_left_d cS) 
                         (msg_is_left_d cT)
; msg_is_right_d    := check_is_right_product wS wT 
                         (msg_is_right_d cS) 
                         (msg_is_right_d cT)
; msg_left_cancel_d    := check_left_cancellative_product wS wT 
                          (msg_left_cancel_d cS)
                          (msg_left_cancel_d cT)
; msg_right_cancel_d   := check_right_cancellative_product wS wT 
                          (msg_right_cancel_d cS)
                          (msg_right_cancel_d cT)
; msg_left_constant_d  := check_left_constant_product wS wT 
                          (msg_left_constant_d cS)
                          (msg_left_constant_d cT)
; msg_right_constant_d := check_right_constant_product wS wT 
                          (msg_right_constant_d cS)
                          (msg_right_constant_d cT)
; msg_anti_left_d      := check_anti_left_product 
                         (msg_anti_left_d cS) 
                         (msg_anti_left_d cT)
; msg_anti_right_d     := check_anti_right_product 
                         (msg_anti_right_d cS) 
                         (msg_anti_right_d cT)
|}.
 *)


(*
Definition sg_CK_certs_product : ∀ {S T : Type},  sg_CK_certificates (S := S) -> sg_CK_certificates (S := T) -> sg_CK_certificates (S := (S * T)) 
:= λ {S T} cS cT,  
{|
  sg_CK_associative   := Assert_Associative   
; sg_CK_congruence    := Assert_Bop_Congruence   
; sg_CK_commutative   := Assert_Commutative   
; sg_CK_left_cancel   := Assert_Left_Cancellative   
; sg_CK_anti_left_d   := check_anti_left_product 
                         (sg_CK_anti_left_d cS) 
                         (sg_CK_anti_left_d cT)
; sg_CK_anti_right_d  := check_anti_right_product 
                         (sg_CK_anti_right_d cS) 
                         (sg_CK_anti_right_d cT)
|}.


Definition sg_CI_certs_product : ∀ {S T : Type},  (brel S) -> (brel T) -> (binary_op S) -> (binary_op T) ->
                                                  S -> (S -> S) -> T -> (T -> T) -> 
                                                  sg_CI_certificates (S := S) -> sg_CI_certificates (S := T) -> sg_CI_certificates (S := (S * T)) 
:= λ {S T} rS rT bS bT s f t g cS cT,  
{|
  sg_CI_associative   := Assert_Associative   
; sg_CI_congruence    := Assert_Bop_Congruence   
; sg_CI_commutative   := Assert_Commutative   
; sg_CI_idempotent    := Assert_Idempotent   
(*; sg_CI_selective_d   := Certify_Not_Selective (cef_commutative_product S T rS rT bS bT s f t g)*)
; sg_CI_not_selective  := Assert_Not_Selective (cef_commutative_product S T rS rT bS bT s f t g)
|}.

 *)


Definition sg_C_certs_product : ∀ {S T : Type},  (brel S) -> (brel T) -> (binary_op S) -> (binary_op T) ->
                                                  S -> (S -> S) -> T ->(T -> T) -> 
                                                 sg_C_certificates (S := S) -> sg_C_certificates (S := T) -> sg_C_certificates (S := (S * T)) 
:= λ {S T} rS rT bS bT s f t g cS cT,  
{|
  sg_C_associative   := Assert_Associative   
; sg_C_congruence    := Assert_Bop_Congruence   
; sg_C_commutative   := Assert_Commutative   
; sg_C_selective_d   := Certify_Not_Selective (cef_commutative_product S T rS rT bS bT s f t g)
; sg_C_idempotent_d  := check_idempotent_product s t
                         (sg_C_idempotent_d cS) 
                         (sg_C_idempotent_d cT)
; sg_C_cancel_d      := check_left_cancellative_product s t
                          (sg_C_cancel_d cS)
                          (sg_C_cancel_d cT)
; sg_C_constant_d    := check_left_constant_product s t
                          (sg_C_constant_d cS)
                          (sg_C_constant_d cT)
; sg_C_anti_left_d      := check_anti_left_product 
                         (sg_C_anti_left_d cS) 
                         (sg_C_anti_left_d cT)
; sg_C_anti_right_d     := check_anti_right_product 
                         (sg_C_anti_right_d cS) 
                         (sg_C_anti_right_d cT)
|}.


Definition sg_product : ∀ {S T : Type},  @sg S -> @sg T -> @sg (S * T)
:= λ {S T} sgS sgT, 
   {| 
       sg_eqv    := eqv_product (sg_eqv sgS) (sg_eqv sgT) 
     ; sg_bop    := bop_product (sg_bop sgS) (sg_bop sgT)
     ; sg_exists_id_d := check_exists_id_product (sg_exists_id_d sgS) (sg_exists_id_d sgT)
     ; sg_exists_ann_d := check_exists_ann_product (sg_exists_ann_d sgS) (sg_exists_ann_d sgT)
     ; sg_certs := sg_certs_product 
                    (eqv_witness (sg_eqv sgS)) 
                    (eqv_witness (sg_eqv sgT)) 
                    (sg_certs sgS) 
                    (sg_certs sgT)
     
     ; sg_ast    := Ast_sg_product (sg_ast sgS, sg_ast sgT)
   |}. 

(*
Definition sg_CK_product : ∀ {S T : Type},  @sg_CK S -> @sg_CK T -> @sg_CK (S * T)
:= λ {S T} sgS sgT, 
   {| 
     sg_CK_eqv     := eqv_product (sg_CK_eqv sgS) (sg_CK_eqv sgT) 
   ; sg_CK_bop     := bop_product (sg_CK_bop sgS) (sg_CK_bop sgT)
   ; sg_CK_exists_id_d := check_exists_id_product (sg_CK_exists_id_d sgS) (sg_CK_exists_id_d sgT)
   ; sg_CK_certs   := sg_CK_certs_product (sg_CK_certs sgS) (sg_CK_certs sgT)
   
   ; sg_CK_ast     := Ast_sg_product (sg_CK_ast sgS, sg_CK_ast sgT)
   |}.

Definition sg_C_product : ∀ {S T : Type},  @sg_C S  -> @sg_C T -> @sg_C (S * T)
:= λ {S T} sgS sgT, 
   {| 
     sg_C_eqv        := eqv_product  (sg_C_eqv sgS) (sg_C_eqv sgT) 
   ; sg_C_bop        := bop_product (sg_C_bop sgS) (sg_C_bop sgT)                            
   ; sg_C_exists_id_d  := check_exists_id_product (sg_C_exists_id_d sgS) (sg_C_exists_id_d sgT)
   ; sg_C_exists_ann_d := check_exists_ann_product (sg_C_exists_ann_d sgS) (sg_C_exists_ann_d sgT)
   ; sg_C_certs      := sg_C_certs_product (eqv_eq (sg_C_eqv sgS)) (eqv_eq (sg_C_eqv sgT))
                                      (sg_C_bop sgS) (sg_C_bop sgT) 
                                      (eqv_witness (sg_C_eqv sgS)) (eqv_new (sg_C_eqv sgS))
                                      (eqv_witness (sg_C_eqv sgT)) (eqv_new (sg_C_eqv sgT)) 
                                      (sg_C_certs sgS) (sg_C_certs sgT)
   
   ; sg_C_ast       := Ast_sg_product (sg_C_ast sgS, sg_C_ast sgT)
   |}. 


Definition sg_CI_product : ∀ {S T : Type},  sg_CI (S := S) -> sg_CI (S := T) -> sg_CI (S := (S * T))
:= λ {S T} sgS sgT, 
   {| 
     sg_CI_eqv    := eqv_product (sg_CI_eqv sgS) (sg_CI_eqv sgT) 
   ; sg_CI_bop       := bop_product (sg_CI_bop sgS) (sg_CI_bop sgT)
   ; sg_CI_exists_id_d  := check_exists_id_product (sg_CI_exists_id_d sgS) (sg_CI_exists_id_d sgT)
   ; sg_CI_exists_ann_d := check_exists_ann_product (sg_CI_exists_ann_d sgS) (sg_CI_exists_ann_d sgT)                                      
   ; sg_CI_certs := sg_CI_certs_product (eqv_eq (sg_CI_eqv sgS)) (eqv_eq (sg_CI_eqv sgT))
                                        (sg_CI_bop sgS) (sg_CI_bop sgT)
                                        (eqv_witness (sg_CI_eqv sgS))
                                        (eqv_new (sg_CI_eqv sgS))                                         
                                        (eqv_witness (sg_CI_eqv sgT))
                                        (eqv_new (sg_CI_eqv sgT))                                         
                                        (sg_CI_certs sgS) 
                                        (sg_CI_certs sgT)
   
   ; sg_CI_ast       := Ast_sg_product (sg_CI_ast sgS, sg_CI_ast sgT)
   |}. 
*) 
End CAS.


Section MCAS.


Open Scope list_scope.
Open Scope string_scope.
(*
Definition mcas_sg_certs_product 
           {S T : Type} 
           (eqS : brel S) (eqT : brel T)
           (wS : S) (wT : T)
           (f : S -> S) (g : T -> T)
           (bS : binary_op S) (bT : binary_op T)
           (id_dS : @check_exists_id S)
           (id_dT : @check_exists_id T)
           (PS : @sg_certs_mcas S) 
           (PT : @sg_certs_mcas T) : @sg_certs_mcas (S * T) := 
match sg_certs_mcas_cast_up S eqS wS f bS id_dS PS,
      sg_certs_mcas_cast_up T eqT wT g bT id_dT PT with 
| MCAS_Cert_sg A', MCAS_Cert_sg B' =>
     sg_certificates_classify (MCAS_Cert_sg (sg_certs_product wS wT A' B'))
| MCAS_Cert_sg_Error sl1, MCAS_Cert_sg_Error sl2 => MCAS_Cert_sg_Error (sl1 ++ sl2)
| MCAS_Cert_sg_Error sl1, _  => MCAS_Cert_sg_Error sl1
| _,  MCAS_Cert_sg_Error sl2 => MCAS_Cert_sg_Error sl2
| _, _                       => MCAS_Cert_sg_Error ("Internal Error : mcas_sg_certs_product" :: nil)
end.
 *)

  Definition sg_product_below_sg {S T : Type} (A : @below_sg S)  (B : @below_sg T)  : @below_sg (S * T) :=
     classify_sg (sg_product (cast_up_sg A) (cast_up_sg B)).
  
  Definition mcas_sg_product {S T : Type} (A : @sg_mcas S)  (B : @sg_mcas T)  : @sg_mcas (S * T) :=
    match A, B with
    | MCAS_sg A', MCAS_sg B'               => MCAS_sg (sg_product_below_sg A' B')
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
  Variable bS : binary_op S.
  Variable bT : binary_op T.
  Variable wS : S.
  Variable f : S -> S.    
  Variable Pf : brel_not_trivial S rS f.
  Variable wT : T.
  Variable g : T -> T.      
  Variable Pg : brel_not_trivial T rT g.  
  Variable symS : brel_symmetric S rS.
  Variable symT : brel_symmetric T rT. 
  Variable transS : brel_transitive S rS.
  Variable transT : brel_transitive T rT. 
  Variable refS : brel_reflexive S rS. 
  Variable refT : brel_reflexive T rT.


Lemma correct_check_commutative_product : 
      ∀ (dS : bop_commutative_decidable S rS bS) (dT : bop_commutative_decidable T rT bT),
        
         check_commutative_product wS wT 
            (p2c_commutative_check S rS bS dS)
            (p2c_commutative_check T rT bT dT)
         = 
         p2c_commutative_check (S * T) 
            (brel_product rS rT) 
            (bop_product bS bT)
            (bop_product_commutative_decide S T rS rT bS bT wS wT dS dT). 
Proof. intros [cS | [ [s3 s4] ncS] ] [cT | [ [t3 t4] ncT] ]; compute; reflexivity. Defined. 

Lemma correct_check_is_left_product : 
      ∀ (dS : bop_is_left_decidable S rS bS) (dT : bop_is_left_decidable T rT bT),
         
         check_is_left_product wS wT 
            (p2c_is_left_check S rS bS dS)
            (p2c_is_left_check T rT bT dT)
         = 
         p2c_is_left_check (S * T) 
            (brel_product rS rT) 
            (bop_product bS bT)
            (bop_product_is_left_decide S T rS rT bS bT wS wT dS dT). 
Proof. intros [cS | [ [s3 s4] ncS ] ] [cT | [ [t3 t4] ncT ]]; compute; reflexivity. Defined. 

Lemma correct_check_is_right_product : 
      ∀ (dS : bop_is_right_decidable S rS bS) (dT : bop_is_right_decidable T rT bT),
         
         check_is_right_product wS wT
            (p2c_is_right_check S rS bS dS)
            (p2c_is_right_check T rT bT dT)
         = 
         p2c_is_right_check (S * T) 
            (brel_product rS rT) 
            (bop_product bS bT)
            (bop_product_is_right_decide S T rS rT bS bT wS wT dS dT). 
Proof. intros [cS | [ [s3 s4] ncS]] [cT | [ [t3 t4] ncT]]; compute; reflexivity. Defined. 


Lemma correct_check_idempotent_product : 
      ∀ (dS : bop_idempotent_decidable S rS bS)  (dT : bop_idempotent_decidable T rT bT),
        
         check_idempotent_product wS wT 
            (p2c_idempotent_check S rS bS dS)
            (p2c_idempotent_check T rT bT dT)
         = 
         p2c_idempotent_check (S * T) 
            (brel_product rS rT) 
            (bop_product bS bT)
            (bop_product_idempotent_decide S T rS rT bS bT wS wT dS dT). 
Proof. intros [cS | [s3 niS]] [cT | [t3 niT]]; compute; reflexivity. Defined. 


Lemma correct_assert_exists_id_product : 
      ∀ (dS : bop_exists_id S rS bS) (dT : bop_exists_id T rT bT),
         
         assert_exists_id_product 
           (p2c_exists_id_assert S rS bS dS)
           (p2c_exists_id_assert T rT bT dT)
         =
         p2c_exists_id_assert (S * T) 
            (brel_product rS rT)
            (bop_product bS bT)
            (bop_product_exists_id S T rS rT bS bT dS dT).
Proof. intros [s sP] [t tP]; compute; reflexivity. Defined. 


Lemma correct_check_exists_id_product : 
      ∀ (dS : bop_exists_id_decidable S rS bS) (dT : bop_exists_id_decidable T rT bT),
         
         check_exists_id_product 
           (p2c_exists_id_check S rS bS dS)
           (p2c_exists_id_check T rT bT dT)
         =
         p2c_exists_id_check (S * T) 
            (brel_product rS rT)
            (bop_product bS bT)
            (bop_product_exists_id_decide S T rS rT bS bT dS dT).
Proof. intros [[s sP] | nS ] [[t tP] | nT ]; compute; reflexivity. Defined. 


Lemma correct_check_exists_ann_product : 
      ∀ (dS : bop_exists_ann_decidable S rS bS) (dT : bop_exists_ann_decidable T rT bT),
         
         check_exists_ann_product 
           (p2c_exists_ann_check S rS bS dS)
           (p2c_exists_ann_check T rT bT dT)
         =
         p2c_exists_ann_check (S * T) 
            (brel_product rS rT)
            (bop_product bS bT)
            (bop_product_exists_ann_decide S T rS rT bS bT dS dT).
Proof. intros [[s sP] | nS ] [[t tP] | nT ]; compute; reflexivity. Defined. 


Lemma correct_check_selective_product : 
      ∀ (dlS : bop_is_left_decidable S rS bS)
         (dlT : bop_is_left_decidable T rT bT)
         (drS : bop_is_right_decidable S rS bS)
         (drT : bop_is_right_decidable T rT bT),
         p2c_selective_check (S * T) 
            (brel_product rS rT) 
            (bop_product bS bT)
            (bop_product_selective_decide S T rS rT bS bT wS f Pf symS transS wT g Pg symT transT dlS dlT drS drT)
         = 
         check_selective_product wS wT 
            (p2c_is_left_check S rS bS dlS)
            (p2c_is_left_check T rT bT dlT)
            (p2c_is_right_check S rS bS drS)
            (p2c_is_right_check T rT bT drT). 
Proof. 
       intros [ilS | [ [s3 s4] nilS]] [ilT | [ [t3 t4] nilT]]
              [irS | [ [s5 s6] nirS]] [irT | [ [t5 t6] nirT]]; 
          compute; auto. 
          assert (F := bop_not_left_or_not_right S rS bS wS f Pf symS transS ilS irS). 
             elim F. 
          assert (F := bop_not_left_or_not_right T rT bT wT g Pg symT transT ilT irT). 
             elim F. 
Defined. 

Lemma correct_check_left_cancel_product : 
      ∀ (dS : bop_left_cancellative_decidable S rS bS) (dT : bop_left_cancellative_decidable T rT bT),
         
         p2c_left_cancel_check (S * T) 
            (brel_product rS rT) 
            (bop_product bS bT)
            (bop_product_left_cancellative_decide S T rS rT bS bT wS refS wT refT dS dT)
         = 
         check_left_cancellative_product  wS wT 
            (p2c_left_cancel_check S rS bS dS)
            (p2c_left_cancel_check T rT bT dT). 
Proof. intros [cS | [ [s3 [s4 s5]] [ncSL ncSR]] ] [cT | [ [t3 [t4 t5]] [ncTL ncTR] ] ]; compute; reflexivity. Defined. 

Lemma correct_check_right_cancel_product : 
      ∀ (dS : bop_right_cancellative_decidable S rS bS) (dT : bop_right_cancellative_decidable T rT bT),
         
         p2c_right_cancel_check (S * T) 
            (brel_product rS rT) 
            (bop_product bS bT)
            (bop_product_right_cancellative_decide S T rS rT bS bT wS refS wT refT dS dT)
         = 
         check_right_cancellative_product wS wT 
            (p2c_right_cancel_check S rS bS dS)
            (p2c_right_cancel_check T rT bT dT). 
Proof. intros [cS | [ [s3 [s4 s5]] [ncSL ncSR]] ] [cT | [ [t3 [t4 t5]] [ncTL ncTR] ] ]; compute; reflexivity. Defined. 

Lemma correct_check_left_constant_product : 
      ∀ (dS : bop_left_constant_decidable S rS bS) (dT : bop_left_constant_decidable T rT bT),
         
         p2c_left_constant_check (S * T) 
            (brel_product rS rT) 
            (bop_product bS bT)
            (bop_product_left_constant_decide S T rS rT bS bT wS wT dS dT)
         = 
         check_left_constant_product wS wT 
            (p2c_left_constant_check S rS bS dS)
            (p2c_left_constant_check T rT bT dT).
Proof. intros [cS | [ [s3 [s4 s5]] ncS] ] [cT | [ [t3 [t4 t5]] ncT] ]; compute; reflexivity. Defined. 


Lemma correct_check_right_constant_product : 
      ∀ (dS : bop_right_constant_decidable S rS bS) (dT : bop_right_constant_decidable T rT bT),
         
         p2c_right_constant_check (S * T) 
            (brel_product rS rT) 
            (bop_product bS bT)
            (bop_product_right_constant_decide S T rS rT bS bT wS wT dS dT)
         = 
         check_right_constant_product wS wT 
            (p2c_right_constant_check S rS bS dS)
            (p2c_right_constant_check T rT bT dT).
Proof. intros [cS | [ [s3 [s4 s5]] ncS] ] [cT | [ [t3 [t4 t5]] ncT] ]; compute; reflexivity. Defined. 


Lemma correct_check_anti_left_product : 
      ∀ (dS : bop_anti_left_decidable S rS bS) (dT : bop_anti_left_decidable T rT bT),
         
         p2c_anti_left_check (S * T) 
            (brel_product rS rT) 
            (bop_product bS bT)
            (bop_product_anti_left_decide S T rS rT bS bT dS dT)
         = 
         check_anti_left_product 
            (p2c_anti_left_check S rS bS dS)
            (p2c_anti_left_check T rT bT dT).
Proof. intros [cS | [ [s3 s4] ncS] ] [cT | [ [t3 t4] ncT] ]; compute; reflexivity. Defined. 


Lemma correct_check_anti_right_product : 
      ∀ (dS : bop_anti_right_decidable S rS bS)
         (dT : bop_anti_right_decidable T rT bT),
         p2c_anti_right_check (S * T) 
            (brel_product rS rT) 
            (bop_product bS bT)
            (bop_product_anti_right_decide S T rS rT bS bT dS dT)
         = 
         check_anti_right_product 
            (p2c_anti_right_check S rS bS dS)
            (p2c_anti_right_check T rT bT dT).
Proof. intros [cS | [ [s3 s4] ncS] ] [cT | [ [t3 t4] ncT] ]; compute; reflexivity. Defined.


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

(*
*) 
(*
Lemma correct_msg_certs_product : 
      ∀ (pS : msg_proofs S rS bS) (pT : msg_proofs T rT bT),
        
      msg_certs_product wS wT (P2C_msg S rS bS pS) (P2C_msg T rT bT pT) 
      = 
      P2C_msg (S * T) (brel_product rS rT) 
                     (bop_product bS bT) 
                     (msg_proofs_product S T rS rT bS bT wS f wT g Pf Pg eS eT pS pT). 
Proof. intros pS pT. 
       unfold msg_proofs_product, msg_certs_product, P2C_msg; simpl. 
       rewrite correct_check_is_right_product. 
       rewrite correct_check_is_left_product. 
       rewrite correct_check_commutative_product.
       rewrite <- correct_check_anti_left_product. 
       rewrite <- correct_check_anti_right_product.
       rewrite <- correct_check_left_constant_product.       
       rewrite <- correct_check_right_constant_product.        
       rewrite correct_check_left_cancel_product. 
       rewrite correct_check_right_cancel_product. 
       reflexivity. 
Defined.
 *)

(*
Lemma correct_sg_CI_certs_product : 
      ∀ (pS : sg_CI_proofs S rS bS) (pT : sg_CI_proofs T rT bT),
        
      sg_CI_certs_product rS rT bS bT wS f wT g (P2C_sg_CI S rS bS pS) (P2C_sg_CI T rT bT pT) 
      = 
      P2C_sg_CI (S * T) (brel_product rS rT) 
                        (bop_product bS bT) 
                       (sg_CI_proofs_product S T rS rT bS bT wS f wT g Pf Pg eS eT pS pT). 
Proof. intros pS pT. 
       unfold sg_CI_proofs_product, sg_CI_certs_product, P2C_sg_CI; simpl; auto. 
Defined. 






Lemma  correct_sg_CK_certs_product : 
      ∀ (pS : sg_CK_proofs S rS bS) (pT : sg_CK_proofs T rT bT),
        
      sg_CK_certs_product (P2C_sg_CK S rS bS pS) (P2C_sg_CK T rT bT pT) 
      = 
      P2C_sg_CK (S * T) 
         (brel_product rS rT) 
         (bop_product bS bT) 
         (sg_CK_proofs_product S T rS rT bS bT eS eT pS pT). 
Proof. intros pS pT. 
       unfold sg_CK_proofs_product, sg_CK_certs_product, P2C_sg_CK; simpl. 
       rewrite correct_check_anti_left_product. 
       rewrite correct_check_anti_right_product. 
       reflexivity. 
Defined.
*) 
(*
Lemma correct_asg_certs_product : 
      ∀ (pS : asg_proofs S rS bS) (pT : asg_proofs T rT bT),
        
      asg_certs_product rS rT bS bT wS f wT g (P2C_asg S rS bS pS) (P2C_asg T rT bT pT) 
      = 
      P2C_asg (S * T) (brel_product rS rT) 
                      (bop_product bS bT) 
                      (asg_proofs_product S T rS rT bS bT wS f wT g Pf Pg eS eT pS pT). 
Proof. intros pS pT. 
       unfold asg_proofs_product, asg_certs_product, P2C_asg; simpl. 
       rewrite correct_check_idempotent_product.
       reflexivity. 
Defined.
*) 

Lemma correct_sg_C_certs_product : 
      ∀ (pS : sg_C_proofs S rS bS) (pT : sg_C_proofs T rT bT),
        
      sg_C_certs_product rS rT bS bT wS f wT g (P2C_sg_C rS bS pS) (P2C_sg_C rT bT pT) 
      = 
      P2C_sg_C(brel_product rS rT) 
        (bop_product bS bT) 
        (sg_C_proofs_product S T rS rT bS bT wS f wT g Pf Pg eS eT pS pT). 
Proof. intros pS pT. 
       unfold sg_C_proofs_product, sg_C_certs_product, P2C_sg_C; simpl. 
       rewrite correct_check_idempotent_product; auto.
       rewrite <- correct_check_anti_left_product; auto. 
       rewrite <- correct_check_anti_right_product; auto.
       rewrite <- correct_check_left_constant_product; auto.       
       rewrite correct_check_left_cancel_product; auto. 
Defined. 



Lemma correct_sg_certs_product : 
      ∀ (pS : sg_proofs S rS bS) (pT : sg_proofs T rT bT),
        
      sg_certs_product wS wT (P2C_sg rS bS pS) (P2C_sg rT bT pT) 
      = 
      P2C_sg (brel_product rS rT) 
             (bop_product bS bT) 
             (sg_proofs_product S T rS rT bS bT wS f wT g Pf Pg eS eT pS pT). 
Proof. intros pS pT. 
       unfold sg_proofs_product, sg_certs_product, P2C_sg; simpl. 
       rewrite correct_check_idempotent_product.
       rewrite correct_check_selective_product.              
       rewrite correct_check_is_right_product. 
       rewrite correct_check_is_left_product. 
       rewrite correct_check_commutative_product.
       rewrite <- correct_check_anti_left_product. 
       rewrite <- correct_check_anti_right_product.
       rewrite <- correct_check_left_constant_product.       
       rewrite <- correct_check_right_constant_product.        
       rewrite correct_check_left_cancel_product. 
       rewrite correct_check_right_cancel_product. 
       reflexivity. 
Defined.

End ProofsCorrect. 

Theorem correct_sg_product 
         (S T : Type) (sgS : A_sg S) (sgT : A_sg T) : 
         sg_product (A2C_sg sgS) (A2C_sg sgT) 
         = 
         A2C_sg (A_sg_product S T sgS sgT). 
Proof. unfold sg_product, A2C_sg; simpl. 
       rewrite correct_eqv_product. 
       rewrite <- correct_sg_certs_product.
       rewrite correct_check_exists_id_product.  
       rewrite correct_check_exists_ann_product.
       reflexivity. 
Qed.

Theorem correct_sg_product_below_sg (S T : Type) (A : @A_below_sg S) (B : @A_below_sg T) : 
  sg_product_below_sg (A2C_below_sg A) (A2C_below_sg B)
  =
  A2C_below_sg (A_sg_product_below_sg A B). 
Proof. unfold sg_product_below_sg, A_sg_product_below_sg.
       rewrite cast_up_sg_A2C_commute.
       rewrite cast_up_sg_A2C_commute.
       rewrite correct_sg_product.
       rewrite correct_classify_sg.
       reflexivity. 
Qed. 

Theorem correct_mcas_sg_product (S T : Type) (A : @A_sg_mcas S) (B : @A_sg_mcas T): 
         mcas_sg_product (A2C_sg_mcas A) (A2C_sg_mcas B) 
         = 
         A2C_sg_mcas (A_mcas_sg_product A B).
Proof. destruct A, B; unfold mcas_sg_product, A_mcas_sg_product,
         A2C_sg_mcas; try reflexivity. 
       rewrite correct_sg_product_below_sg.
       reflexivity. 
Qed. 

(*
Theorem correct_sg_CK_product :
      ∀ (S T : Type) (sgS : A_sg_CK S) (sgT : A_sg_CK T), 
         sg_CK_product (A2C_sg_CK S sgS) (A2C_sg_CK T sgT) 
         = 
         A2C_sg_CK (S * T) (A_sg_CK_product S T sgS sgT). 
Proof. intros S T sgS sgT. 
       unfold sg_CK_product, A2C_sg_CK; simpl. 
       rewrite correct_eqv_product. 
       rewrite <- correct_sg_CK_certs_product.
       rewrite correct_check_exists_id_product.  
       reflexivity. 
Qed. 


Theorem correct_sg_CI_product :
      ∀ (S T : Type) (sgS : A_sg_CI S) (sgT : A_sg_CI T), 
         sg_CI_product (A2C_sg_CI S sgS) (A2C_sg_CI T sgT) 
         = 
         A2C_sg_CI (S * T) (A_sg_CI_product S T sgS sgT). 
Proof. intros S T sgS sgT. 
       unfold sg_CI_product, A2C_sg_CI; simpl. 
       rewrite correct_eqv_product. 
       rewrite <- correct_sg_CI_certs_product.
       rewrite correct_check_exists_id_product.  
       rewrite correct_check_exists_ann_product.
       reflexivity. 
Qed. 

Theorem correct_sg_C_product :
      ∀ (S T : Type) (sgS : A_sg_C S) (sgT : A_sg_C T), 
         sg_C_product (A2C_sg_C S sgS) (A2C_sg_C T sgT) 
         = 
         A2C_sg_C (S * T) (A_sg_C_product S T sgS sgT). 
Proof. intros S T sgS sgT. 
       unfold sg_C_product, A2C_sg_C; simpl. 
       rewrite correct_eqv_product. 
       rewrite <- correct_sg_C_certs_product.
       rewrite correct_check_exists_id_product.  
       rewrite correct_check_exists_ann_product.       
       reflexivity. 
Qed. 

*)  
End Verify.   

