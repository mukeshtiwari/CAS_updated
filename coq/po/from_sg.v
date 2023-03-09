Require Import CAS.coq.common.compute.
Require Import Coq.Strings.String.
Require Import CAS.coq.common.ast. 

Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures. 
Require Import CAS.coq.eqv.theory.

Require Import CAS.coq.po.properties.
Require Import CAS.coq.po.structures. 
Require Import CAS.coq.po.theory.
Require Import CAS.coq.po.classify.
Require Import CAS.coq.po.dual.

Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures. 
Require Import CAS.coq.sg.theory.
Require Import CAS.coq.sg.classify.  
Require Import CAS.coq.sg.cast_up. 

Section Computation. 

Definition brel_lte_left:  ∀ {S : Type}, brel S → binary_op S → brel S
  := λ {S} eq b x y, eq x (b x y). 

Definition brel_lt_left:  ∀ {S : Type}, brel S → binary_op S → brel S
  := λ {S} eq b x y,  below (brel_lte_left eq b) y x.

Definition brel_lte_right:  ∀ {S : Type}, brel S → binary_op S → brel S
  := λ {S} eq b x y, eq y (b x y). 

Definition brel_lt_right:  ∀ {S : Type}, brel S → binary_op S → brel S
  := λ {S} eq b x y, below (brel_lte_right eq b) y x. 

End Computation.

Section IntroElim.

Variable S  : Type. 
Variable eq : brel S.
Variable b     : binary_op S.

Lemma brel_lt_left_intro (s1 s2 : S) : eq s1 (b s1 s2) = true -> eq s2 (b s2 s1) = false -> brel_lt_left eq b s1 s2 = true. 
Proof. intros A B. compute. rewrite A, B. reflexivity. Qed. 

Lemma brel_lt_left_elim (s1 s2 : S) : brel_lt_left eq b s1 s2 = true -> (eq s1 (b s1 s2) = true) * (eq s2 (b s2 s1) = false). 
Proof. compute. case_eq(eq s1 (b s1 s2)); intro A; case_eq(eq s2 (b s2 s1)); intro B; auto. Qed. 

Lemma brel_lt_left_false_intro (s1 s2 : S) : (eq s1 (b s1 s2) = false) + (eq s2 (b s2 s1) = true) -> brel_lt_left eq b s1 s2 = false. 
Proof. intros [A | A]; compute; rewrite A. reflexivity. case_eq(eq s1 (b s1 s2)); intro B; auto. Qed. 

Lemma brel_lt_left_false_elim (s1 s2 : S) : brel_lt_left eq b s1 s2 = false -> (eq s1 (b s1 s2) = false) + (eq s2 (b s2 s1) = true). 
Proof. compute. case_eq(eq s1 (b s1 s2)); intro A; case_eq(eq s2 (b s2 s1)); intro B; auto. Qed. 

End IntroElim.

Section Theory.

Variable S  : Type. 

Variable eq : brel S.
Variable eqCong : brel_congruence S eq eq.
Variable refS : brel_reflexive S eq.
Variable symS : brel_symmetric S eq.
Variable trnS : brel_transitive S eq.
Definition symS_dual := brel_symmetric_implies_dual S eq symS. 

Variable bS     : binary_op S.
Variable congS : bop_congruence S eq bS.

Variable wS : S.
Variable f : S -> S.
Variable Pf   : brel_not_trivial S eq f.

Notation "a == b"    := (eq a b = true) (at level 30).
Notation "a != b"    := (eq a b = false) (at level 30).
Notation "a (+) b"   := (bS a b) (at level 15).


(* used? *)
Lemma brel_lt_left_total_order_split
      (commS : bop_commutative S eq bS)
      (selS : bop_selective S eq bS) : 
      ∀  (x y : S), 
      ((eq x y = true)  *  (brel_lt_left eq bS x y = false)) 
    + ((eq x y = false) *  (brel_lt_left eq bS x y = true)) 
    + ((eq x y = false) *  (brel_lt_left eq bS x y = false)).  
Proof. intros x y. 
       case_eq(eq x  y); intro H. 
          left. left. split. 
             reflexivity. 
             unfold brel_lt_left.
             assert (idemS := bop_selective_implies_idempotent S eq bS selS). 
             assert (Ix := idemS x). assert (Iy := idemS y). 
             assert (K := congS x y x x (refS x) (symS x y H)). 
             assert (Q : eq y (bS x y) = true). apply symS in K. apply symS in H. apply symS in Ix. 
                   apply (trnS _ _ _ H  (trnS _ _ _ Ix K)). 
             unfold below, brel_lte_left. unfold uop_not. 
             apply symS in Ix. apply symS in K. rewrite (trnS _ _ _ Ix K). 
             rewrite (trnS _ _ _ Q (commS x y)). compute. reflexivity. 
             
          unfold brel_lt_left. unfold below, brel_lte_left. unfold uop_not. 
          destruct (selS x y) as [K | K]; apply symS in K. 
             left. right. split.
                reflexivity.                          
                assert (J := brel_transititivity_implies_dual _ _ trnS _ _ _ K H). 
                apply (brel_symmetric_implies_dual _ _ symS) in J. 
                rewrite K.  case_eq(eq y (bS y x)); intro L; auto.
                assert (M := commS y x). rewrite (trnS _ _ _ L M) in J. 
                discriminate J. 
                
             right. split.
                reflexivity.                          
                apply (brel_symmetric_implies_dual _ _ symS) in H. 
                assert (J := brel_transititivity_implies_dual _ _ trnS _ _ _ K H). 
                apply (brel_symmetric_implies_dual _ _ symS) in J.
                rewrite J. simpl. reflexivity.
Defined.  

(*********************** PO properties ************************************) 


Lemma brel_lte_left_congruence : brel_congruence S eq (brel_lte_left eq bS).
Proof. compute. intros s t u v H1 H2. apply eqCong; auto. Qed.

Lemma brel_lte_right_congruence : brel_congruence S eq (brel_lte_right eq bS).
Proof. compute. intros s t u v H1 H2. apply eqCong; auto. Qed.

Lemma brel_lt_left_congruence : brel_congruence S eq (brel_lt_left eq bS).
Proof. compute. intros s t u v H1 H2.
       assert (A := congS _ _ _ _ H1 H2).
       assert (B := congS _ _ _ _ H2 H1).        
       rewrite (eqCong _ _ _ _ H1 A).
       rewrite (eqCong _ _ _ _ H2 B).
       reflexivity. 
Qed.

Lemma brel_lte_left_reflexive (idemS : bop_idempotent S eq bS) : brel_reflexive S  (brel_lte_left eq bS).
Proof. compute. intro s. auto. Qed.

Lemma brel_lte_right_reflexive (idemS : bop_idempotent S eq bS) : brel_reflexive S  (brel_lte_right eq bS).
Proof. compute. intro s. auto. Qed.

Lemma brel_lte_left_not_reflexive (idemS : bop_not_idempotent S eq bS) : brel_not_reflexive S  (brel_lte_left eq bS).
Proof. destruct idemS as [a A]. exists a. compute.
       case_eq(eq a (a (+) a)); intro H; auto.
       apply symS in H. rewrite H in A. discriminate A. 
Defined. 

Lemma brel_lte_left_transitive (assoS : bop_associative S eq bS) : brel_transitive S  (brel_lte_left eq bS).
Proof. compute. intros s t u H1 H2.
       assert (A : (s (+) t) == (s (+) (t (+) u))).
          exact (congS _ _ _ _ (refS s) H2). 
       assert (B : (s (+) (t (+) u)) == ((s (+) t) (+) u)).
          exact (symS _ _ (assoS s t u)). 
       assert (C : ((s (+) t) (+) u) == (s (+) u)).
          exact (congS _ _ _ _ (symS _ _ H1) (refS u)).
       exact (trnS _ _ _ (trnS _ _ _ (trnS _ _ _ H1 A) B) C).
Qed.

Lemma brel_lte_right_transitive (assoS : bop_associative S eq bS) : brel_transitive S  (brel_lte_right eq bS).
Proof. compute. intros s t u H1 H2.
       assert (A : (t (+) u) == ((s (+) t) (+) u)). 
          exact (congS _ _ _ _ H1 (refS u)). 
       assert (B : ((s (+) t) (+) u) == (s (+) (t (+) u))).
          exact (assoS s t u). 
       assert (C : (s (+) (t (+) u)) == (s (+) u)).
          exact (congS _ _ _ _ (refS s) (symS _ _ H2)).  
       exact (trnS _ _ _ (trnS _ _ _ (trnS _ _ _ H2 A) B) C).
Qed.

Lemma brel_lte_left_antisymmetric (commS : bop_commutative S eq bS) : brel_antisymmetric S eq (brel_lte_left eq bS).
Proof. intros s t H1 H2.
       assert (A := commS s t). 
       apply symS in H2. 
       assert (B := trnS _ _ _ H1 A).
       assert (C := trnS _ _ _ B H2).
       exact C. 
Qed.

Lemma brel_lte_right_antisymmetric (commS : bop_commutative S eq bS) : brel_antisymmetric S eq (brel_lte_right eq bS).
Proof. intros s t H1 H2.
       assert (A := commS s t). compute in H1, H2. 
       assert (B := trnS _ _ _ H1 A). apply symS in B. 
       exact (trnS _ _ _ H2 B).
Qed.

(* note : need something stronger than not_commutative to get not_antisymmetric. 

Explore this further????

*) 
Lemma brel_lte_left_not_antisymmetric
         (ncommS : {s : S & {t : S & (s (+) t != t (+) s) * s == (s (+) t) * t == (t (+) s) }}) :
             brel_not_antisymmetric S eq (brel_lte_left eq bS).
Proof. destruct ncommS as [a [b [[A B] C]]]. exists (a, b). compute. 
       split; auto. 
       case_eq(eq a b); intro H; auto. apply symS in B. 
       assert (D := trnS _ _ _ B H).
       assert (E := trnS _ _ _ D C).
       rewrite E in A. discriminate A. 
Qed.

(* just checking that this is an iff .... 

Explore this further????
*) 
Lemma brel_lte_left_antisymmetric_v2
      (commS : ∀ s t : S, (s (+) t == t (+) s) + (s != (s (+) t)) + (t != (t (+) s))) :
         brel_antisymmetric S eq (brel_lte_left eq bS).
Proof. compute. intros s t H1 H2.
       destruct (commS s t) as [[A | A] | A].
       + apply symS in H2. 
         assert (B := trnS _ _ _ H1 A).
         assert (C := trnS _ _ _ B H2).
         exact C.
       + rewrite A in H1. discriminate H1.
       + rewrite A in H2. discriminate H2.
Qed.

Lemma brel_lte_left_total
      (commS : bop_commutative S eq bS)
      (selS : bop_selective S eq bS) : brel_total S (brel_lte_left eq bS).
Proof. compute. intros s t.
       destruct (selS s t) as [H | H]. 
       left. apply symS; auto.        
       right.
       assert (A := commS s t). apply symS in H.
       exact (trnS _ _ _ H A). 
Qed.

Lemma brel_lte_right_total
      (commS : bop_commutative S eq bS)
      (selS : bop_selective S eq bS) : brel_total S (brel_lte_right eq bS).
Proof. compute. intros s t.
       destruct (selS s t) as [H | H]. 
       right. assert (A := commS s t). apply symS in H.
       exact (trnS _ _ _ H A).        
       left. exact (symS _ _ H). 
Qed.

Lemma brel_lte_left_not_total
      (commS : bop_commutative S eq bS)      
      (nselS : bop_not_selective S eq bS) : brel_not_total S (brel_lte_left eq bS).
Proof. destruct nselS as [[s t] [A B]].
       exists (s, t). compute.
       apply symS_dual in A. rewrite A.
       assert (C := commS s t).
       assert (D := brel_transititivity_implies_dual S eq trnS _ _ _ C B). 
       apply symS_dual in D. rewrite D. 
       auto.        
Defined.

Lemma brel_lte_right_not_total
      (commS : bop_commutative S eq bS)      
      (nselS : bop_not_selective S eq bS) : brel_not_total S (brel_lte_right eq bS).
Proof. destruct nselS as [[s t] [A B]].
       exists (s, t). compute. split. 
       apply symS_dual in B. exact B. 
       assert (C := commS s t).
       assert (D := brel_transititivity_implies_dual S eq trnS _ _ _ C A). 
       apply symS_dual in D. exact D. 
Defined.


Lemma brel_lte_left_is_top (s : S) (idS : bop_is_id S eq bS s) : brel_is_top S (brel_lte_left eq bS) s. 
Proof. compute. intro t.
       destruct (idS t) as [_ B].
       apply symS. exact B. 
Defined.

Lemma brel_lte_right_is_bottom (s : S) (idS : bop_is_id S eq bS s) : brel_is_bottom S (brel_lte_right eq bS) s. 
Proof. compute. intro t.
       destruct (idS t) as [A B].
       exact (symS _ _ A). 
Defined.

Lemma brel_lte_left_exists_top (idS : bop_exists_id S eq bS) : brel_exists_top S (brel_lte_left eq bS).
Proof. destruct idS as [s A]. exists s.  apply brel_lte_left_is_top; auto. Defined.

Lemma brel_lte_right_exists_bottom (idS : bop_exists_id S eq bS) : brel_exists_bottom S (brel_lte_right eq bS).
Proof. destruct idS as [s A]. exists s.  apply brel_lte_right_is_bottom; auto. Defined.

Lemma brel_lte_left_not_exists_top
      (commS : bop_commutative S eq bS)
      (nidS : bop_not_exists_id S eq bS) : brel_not_exists_top S (brel_lte_left eq bS).
Proof. compute. intros a. destruct (nidS a) as [ c A].  exists c. 
       destruct A as [A | A].
          apply symS_dual. assert (B := commS a c). 
          assert (C := brel_transititivity_implies_dual S eq trnS _ _ _ B A).
          exact C. 
         apply symS_dual. exact A. 
Defined.

Lemma brel_lte_right_not_exists_bottom
      (commS : bop_commutative S eq bS)
      (nidS : bop_not_exists_id S eq bS) : brel_not_exists_bottom S (brel_lte_right eq bS).
Proof. compute. intros a. destruct (nidS a) as [ c A].  exists c. 
       destruct A as [A | A].
       + apply symS_dual. exact A.
       + assert (B := commS a c).
         case_eq(eq c (a (+) c)); intro C; auto.  
         rewrite (symS _ _ (trnS _ _ _ C B)) in A.
         discriminate A. 
Defined.

Lemma brel_lte_left_exists_qo_top
      (commS : bop_commutative S eq bS)      
      (idS : bop_exists_id S eq bS) : brel_exists_qo_top S eq (brel_lte_left eq bS).
Proof. destruct idS as [s A]. exists s. split. 
       apply brel_lte_left_is_top; auto.
       intros a. compute. intros B C.
       assert (D := commS s a). apply symS in C. 
       assert (E := trnS _ _ _ B D).
       exact (trnS _ _ _ E C). 
Defined.

Lemma brel_lte_left_not_exists_qo_top
      (commS : bop_commutative S eq bS)      
      (nidS : bop_not_exists_id S eq bS) : brel_not_exists_qo_top S eq (brel_lte_left eq bS).
Proof. compute. intros a. left. 
       destruct (nidS a) as [ c A].
       exists c. 
       destruct A as [A | A].
          apply symS_dual. assert (B := commS a c). 
          assert (C := brel_transititivity_implies_dual S eq trnS _ _ _ B A).
          exact C. 
         apply symS_dual. exact A. 
Defined.


Lemma brel_lte_left_is_bottom (s : S) (annS : bop_is_ann S eq bS s) : brel_is_bottom S (brel_lte_left eq bS) s.
Proof. intro t. destruct (annS t) as [B _]. compute. apply symS. exact B. Defined.

Lemma brel_lte_right_is_top (s : S) (annS : bop_is_ann S eq bS s) : brel_is_top S (brel_lte_right eq bS) s.
Proof. intro t. destruct (annS t) as [B C]. compute.
       exact (symS _ _ C). 
Defined.

Lemma brel_lte_left_exists_bottom (annS : bop_exists_ann S eq bS) : brel_exists_bottom S (brel_lte_left eq bS).
Proof. destruct annS as [s A]. exists s. apply brel_lte_left_is_bottom; auto. Defined. 

Lemma brel_lte_right_exists_top (annS : bop_exists_ann S eq bS) : brel_exists_top S (brel_lte_right eq bS).
Proof. destruct annS as [s A]. exists s. apply brel_lte_right_is_top; auto. Defined. 


Lemma brel_lte_left_not_exists_bottom
      (commS : bop_commutative S eq bS)      
      (annS : bop_not_exists_ann S eq bS) : brel_not_exists_bottom S (brel_lte_left eq bS).
Proof. intro s. compute. destruct (annS s) as [t [L | R]]; exists t.
       + case_eq(eq s (s (+) t)); intro C; auto. apply symS in C. 
         rewrite C in L. discriminate L. 
       + case_eq(eq s (s (+) t)); intro C; auto.
         assert (D := commS s t). 
         assert (E := trnS _ _ _ C D). apply symS in E.
         rewrite E in R. discriminate R. 
Defined.

Lemma brel_lte_right_not_exists_top
      (commS : bop_commutative S eq bS)      
      (annS : bop_not_exists_ann S eq bS) : brel_not_exists_top S (brel_lte_right eq bS).
Proof. intro s. compute. destruct (annS s) as [t [L | R]]; exists t.
       + case_eq(eq s (t (+) s)); intro C; auto.
         assert (D := commS t s). 
         assert (E := trnS _ _ _ C D). apply symS in E.
         rewrite E in L. discriminate L. 
       + case_eq(eq s (t (+) s)); intro C; auto. apply symS in C. 
         rewrite C in R. discriminate R. 
Defined.


Lemma brel_lte_left_is_qo_bottom
      (s : S)
      (commS : bop_commutative S eq bS)      
      (annS : bop_is_ann S eq bS s) : brel_is_qo_bottom S eq (brel_lte_left eq bS) s.
Proof. compute. split.
       intro t. destruct (annS t) as [B _]. apply symS. exact B. 
       intros a. intros B C.
       assert (D := commS s a). apply symS in C. 
       assert (E := trnS _ _ _ B D).
       exact (trnS _ _ _ E C). 
Defined. 

Lemma brel_lte_left_exists_qo_bottom
      (commS : bop_commutative S eq bS)
      (annS : bop_exists_ann S eq bS) : brel_exists_qo_bottom S eq (brel_lte_left eq bS).
Proof. destruct annS as [s A]. exists s. apply brel_lte_left_is_qo_bottom; auto. Defined.

Lemma brel_lte_left_not_exists_qo_bottom
      (commS : bop_commutative S eq bS)
      (annS : bop_not_exists_ann S eq bS) : brel_not_exists_qo_bottom S eq (brel_lte_left eq bS).
Proof. intro s. compute. destruct (annS s) as [t [L | R]]; left; exists t.
       + case_eq(eq s (s (+) t)); intro C; auto. apply symS in C. 
         rewrite C in L. discriminate L. 
       + case_eq(eq s (s (+) t)); intro C; auto.
         assert (D := commS s t). 
         assert (E := trnS _ _ _ C D). apply symS in E.
         rewrite E in R. discriminate R. 
Defined.

(*  WTF is this? 


Lemma brel_lte_left_bottoms_set_is_finite (sif : something_is_finite S eq b) :
       bottoms_set_is_finite S eq (brel_lte_left eq b). 
Proof. destruct sif as [[B w] [Q P]].
       exists (B, w). split. 

       (* is_antichain S eq (brel_lte_left eq b) B *)
       unfold is_antichain.
       intros s A t C. compute.
       assert (D := Q s A t C). 
       destruct D as [[E F] | [E F]]; rewrite E, F; reflexivity. 

       intro s. destruct (P s) as [A | A]. 
          left. exact A. 
          destruct A as [A1 [A2 A3]]. right. split. 
             (* in_set eq B (w s) = true *)
             exact A1. 
             (* below (brel_lte_left eq b) s (w s) = true *)
             compute. rewrite A2, A3. reflexivity. 
Defined.

Lemma brel_lte_left_bottoms_set_not_is_finite (sif : something_not_is_finite S eq b) :
       bottoms_set_not_is_finite S eq (brel_lte_left eq b). 
Proof. destruct sif as [F A].
       unfold bottoms_set_not_is_finite.
       exists F. 
       intros B C.

          assert (D : is_interesting S eq b B).
             unfold is_interesting. unfold is_antichain in C. 
             intros s D t E.
             assert (bC := commS s t). 
             assert (G := C s D t E). apply equiv_or_incomp_elim in G.
             unfold brel_lte_left in G.              
             destruct G as [G | G]. 
                apply equiv_elim in G. left. 
                destruct G as [G1 G2]. split.
                   exact G2. 
                   exact G1. 
                
                apply incomp_elim in G. right. 
                destruct G as [G1 G2]. split.                   
                   exact G2. 
                   exact G1. 
          destruct (A B D) as [E G].
          split. 
            exact E.           
            intros s H.
            assert (I := G s H).
            apply below_false_intro.
            unfold brel_lte_left. 
            exact I. 
Defined. 
*) 


       
(*
Definition from_sg_left_bottoms (a: S) (x: unit)  := a :: nil.
Definition from_sg_left_lower (a b : S) := a.               
Definition from_sg_left_bottoms_finite_witness (a : S) := (from_sg_left_bottoms a, from_sg_left_lower a).


Lemma brel_lte_left_bottoms_finite (annS : bop_exists_ann S eq b) : bottoms_finite S eq (brel_lte_left eq b).
Proof. unfold bottoms_finite. destruct annS as [ c A]. compute in A. 
       exists (from_sg_left_bottoms_finite_witness c). 
       simpl. intro s.
       destruct (A s) as [B C]. unfold from_sg_left_lower. unfold brel_lte_left.
       rewrite refS. simpl. split; auto. 
Defined.

Lemma brel_lte_left_not_bottoms_finite (nannS : bop_not_exists_ann S eq b) : bottoms_finite S eq (brel_lte_left eq b).
Proof. unfold bop_not_exists_ann in nannS. 
*) 

Lemma brel_lte_left_not_trivial_from_not_is_left
  (Q: bop_not_is_left S eq bS):
     order_not_trivial S  (brel_lte_left eq bS).
Proof. destruct Q as [[s t] A].
       exists (s, t). compute.
       apply (brel_symmetric_implies_dual S eq symS); auto. 
Defined.


Lemma brel_lte_left_not_trivial
  (commS : bop_commutative S eq bS): 
     order_not_trivial S  (brel_lte_left eq bS).
Proof. apply brel_lte_left_not_trivial_from_not_is_left.
       exact (bop_commutative_implies_not_is_left S eq bS wS f Pf symS trnS commS). 
Defined.

(* for some reason the above do no work properly with extraction *) 
Lemma brel_lte_left_not_trivial_v2
  (commS : bop_commutative S eq bS): 
     order_not_trivial S  (brel_lte_left eq bS).
Proof. exists (cef_commutative_implies_not_is_left eq bS wS f).
       compute. destruct (Pf wS) as [A B].
       assert (C := commS wS (f wS)). 
       case_eq(eq (f wS (+) wS) wS); intro J; 
       case_eq(eq (f wS) (f wS (+) wS)); intro K; auto. 
       - rewrite (trnS _ _ _ K J) in B. discriminate B. 
       - case_eq(eq wS (wS (+) (f wS))); intro L; auto.
         assert (D := trnS _ _ _ L C). apply symS in D.
         rewrite D in J. discriminate J. 
       - case_eq(eq wS (wS (+) (f wS))); intro L; auto.
         assert (D := trnS _ _ _ L C). apply symS in D.
         rewrite D in J. discriminate J. 
Defined.


Lemma brel_lte_right_not_trivial_from_not_is_right
  (Q: bop_not_is_right S eq bS):
     order_not_trivial S  (brel_lte_right eq bS).
Proof. destruct Q as [[s t] A].
       exists (s, t). compute.
       apply (brel_symmetric_implies_dual S eq symS); auto. 
Defined.


Lemma brel_lte_right_not_trivial
  (commS : bop_commutative S eq bS): 
     order_not_trivial S  (brel_lte_right eq bS).
Proof. apply brel_lte_right_not_trivial_from_not_is_right.
       exact (bop_commutative_implies_not_is_right S eq bS wS f Pf symS trnS commS). 
Defined.


End Theory.

Section ACAS.

Section Decide.

Variables (S : Type) (eq : brel S) (eqvP : eqv_proofs S eq) (plus : binary_op S).  

Definition brel_lte_left_total_decide
     (plus_comm : bop_commutative S eq plus) 
     (D : bop_selective_decidable S eq plus) : 
          brel_total_decidable S (brel_lte_left eq plus) := 
     let trn := A_eqv_transitive S eq eqvP in 
     let sym := A_eqv_symmetric S eq eqvP in 
     match D with
     | inl sel  => inl (brel_lte_left_total S eq sym trn plus plus_comm sel)
     | inr nsel => inr (brel_lte_left_not_total S eq sym trn plus plus_comm nsel)
     end.

Definition brel_lte_right_total_decide
     (plus_comm : bop_commutative S eq plus) 
     (D : bop_selective_decidable S eq plus) : 
          brel_total_decidable S (brel_lte_right eq plus) := 
     let trn := A_eqv_transitive S eq eqvP in 
     let sym := A_eqv_symmetric S eq eqvP in 
     match D with
     | inl sel  => inl (brel_lte_right_total S eq sym trn plus plus_comm sel)
     | inr nsel => inr (brel_lte_right_not_total S eq sym trn plus plus_comm nsel)
     end.


Definition brel_lte_left_exists_top_decide
           (plus_comm : bop_commutative S eq plus)            
           (D : bop_exists_id_decidable S eq plus) :
                 brel_exists_top_decidable S (brel_lte_left eq plus) :=
  let trn := A_eqv_transitive S eq eqvP in 
  let sym := A_eqv_symmetric S eq eqvP in 
  match D with
  | inl idS  => inl (brel_lte_left_exists_top S eq sym plus idS)
  | inr nidS => inr (brel_lte_left_not_exists_top S eq sym trn plus plus_comm nidS)
  end. 


Definition brel_lte_right_exists_bottom_decide
           (plus_comm : bop_commutative S eq plus)            
           (D : bop_exists_id_decidable S eq plus) :
                 brel_exists_bottom_decidable S (brel_lte_right eq plus) :=
  let trn := A_eqv_transitive S eq eqvP in 
  let sym := A_eqv_symmetric S eq eqvP in 
  match D with
  | inl idS  => inl (brel_lte_right_exists_bottom S eq sym plus idS)
  | inr nidS => inr (brel_lte_right_not_exists_bottom S eq sym trn plus plus_comm nidS)
  end. 


Definition brel_lte_left_exists_bottom_decide
           (plus_comm : bop_commutative S eq plus)            
           (D : bop_exists_ann_decidable S eq plus) :
                 brel_exists_bottom_decidable S (brel_lte_left eq plus) :=
  let trn := A_eqv_transitive S eq eqvP in 
  let sym := A_eqv_symmetric S eq eqvP in 
  match D with
  | inl annS  => inl (brel_lte_left_exists_bottom S eq sym plus annS)
  | inr nannS => inr (brel_lte_left_not_exists_bottom S eq sym trn plus plus_comm nannS)
  end.

Definition brel_lte_right_exists_top_decide
           (plus_comm : bop_commutative S eq plus)            
           (D : bop_exists_ann_decidable S eq plus) :
                 brel_exists_top_decidable S (brel_lte_right eq plus) :=
  let trn := A_eqv_transitive S eq eqvP in 
  let sym := A_eqv_symmetric S eq eqvP in 
  match D with
  | inl annS  => inl (brel_lte_right_exists_top S eq sym plus annS)
  | inr nannS => inr (brel_lte_right_not_exists_top S eq sym trn plus plus_comm nannS)
  end. 

End Decide.

Section Proofs.

  Variables
    (S : Type)
    (eq : brel S)
    (eqvP : eqv_proofs S eq)
    (plus : binary_op S)
    (wS : S) 
    (f : S -> S)
    (ntS : brel_not_trivial S eq f). 
  
Definition po_proofs_from_sg_CI_left_proofs
           (P : sg_CI_proofs S eq plus) : po_proofs S eq ((brel_lte_left eq plus)) :=
let eqcong  := A_eqv_congruence _ _ eqvP in
let sym   := A_eqv_symmetric _ _ eqvP in
let ref   := A_eqv_reflexive _ _ eqvP in
let trn   := A_eqv_transitive _ _ eqvP in      
let cong  := A_sg_CI_congruence _ _ _   P in
let assoc := A_sg_CI_associative _ _ _   P in
let idem  := A_sg_CI_idempotent _ _ _   P in
let comm  := A_sg_CI_commutative _ _ _   P in
let nsel  := A_sg_CI_not_selective _ _ _   P in   
{|  
  A_po_congruence    := brel_lte_left_congruence S eq eqcong sym plus cong 
; A_po_reflexive     := brel_lte_left_reflexive S eq sym plus idem 
; A_po_transitive    := brel_lte_left_transitive S eq ref sym trn plus cong assoc 
; A_po_antisymmetric := brel_lte_left_antisymmetric S eq sym trn plus comm 
; A_po_not_total     := brel_lte_left_not_total S eq sym trn plus comm nsel
|}.

Definition po_proofs_from_sg_CI_right_proofs
           (P : sg_CI_proofs S eq plus) : po_proofs S eq ((brel_lte_right eq plus)) :=
let eqcong  := A_eqv_congruence _ _ eqvP in
let sym   := A_eqv_symmetric _ _ eqvP in
let ref   := A_eqv_reflexive _ _ eqvP in
let trn   := A_eqv_transitive _ _ eqvP in      
let cong  := A_sg_CI_congruence _ _ _   P in
let assoc := A_sg_CI_associative _ _ _   P in
let idem  := A_sg_CI_idempotent _ _ _   P in
let comm  := A_sg_CI_commutative _ _ _   P in
let nsel  := A_sg_CI_not_selective _ _ _   P in   
{|  
  A_po_congruence    := brel_lte_right_congruence S eq eqcong sym plus cong 
; A_po_reflexive     := brel_lte_right_reflexive S eq sym plus idem 
; A_po_transitive    := brel_lte_right_transitive S eq ref sym trn plus cong assoc 
; A_po_antisymmetric := brel_lte_right_antisymmetric S eq sym trn plus comm 
; A_po_not_total     := brel_lte_right_not_total S eq sym trn plus comm nsel
|}.


Definition fo_proofs_from_sg_CS_left_proofs
           (P : sg_CS_proofs S eq plus) : fo_proofs S eq ((brel_lte_left eq plus)) :=
let eqcong  := A_eqv_congruence _ _ eqvP in
let sym   := A_eqv_symmetric _ _ eqvP in
let ref   := A_eqv_reflexive _ _ eqvP in
let trn   := A_eqv_transitive _ _ eqvP in      
let cong  := A_sg_CS_congruence _ _ _   P in
let assoc := A_sg_CS_associative _ _ _   P in
let comm  := A_sg_CS_commutative _ _ _   P in
let sel  := A_sg_CS_selective _ _ _   P in
let idem  := bop_selective_implies_idempotent _ _ _ sel in
{|  
  A_fo_congruence    := brel_lte_left_congruence S eq eqcong sym plus cong 
; A_fo_reflexive     := brel_lte_left_reflexive S eq sym plus idem 
; A_fo_transitive    := brel_lte_left_transitive S eq ref sym trn plus cong assoc 
; A_fo_antisymmetric_d := inl (brel_lte_left_antisymmetric S eq sym trn plus comm)
; A_fo_total         := brel_lte_left_total S eq sym trn plus comm sel
; A_fo_trivial_d     := inr (brel_lte_left_not_trivial_v2 S eq sym trn plus wS f ntS comm)       
|}.

Definition fo_proofs_from_sg_CS_right_proofs
           (P : sg_CS_proofs S eq plus) : fo_proofs S eq ((brel_lte_right eq plus)) :=
let eqcong  := A_eqv_congruence _ _ eqvP in
let sym   := A_eqv_symmetric _ _ eqvP in
let ref   := A_eqv_reflexive _ _ eqvP in
let trn   := A_eqv_transitive _ _ eqvP in      
let cong  := A_sg_CS_congruence _ _ _   P in
let assoc := A_sg_CS_associative _ _ _   P in
let comm  := A_sg_CS_commutative _ _ _   P in
let sel  := A_sg_CS_selective _ _ _   P in
let idem  := bop_selective_implies_idempotent _ _ _ sel in
{|  
  A_fo_congruence    := brel_lte_right_congruence S eq eqcong sym plus cong 
; A_fo_reflexive     := brel_lte_right_reflexive S eq sym plus idem 
; A_fo_transitive    := brel_lte_right_transitive S eq ref sym trn plus cong assoc 
; A_fo_antisymmetric_d := inl (brel_lte_right_antisymmetric S eq sym trn plus comm) 
; A_fo_total         := brel_lte_right_total S eq sym trn plus comm sel
; A_fo_trivial_d     := inr (brel_lte_right_not_trivial S eq sym trn plus wS f ntS comm)
|}.

End Proofs.

Section Combinators.

Definition A_po_from_sg_CI_left {S : Type} (A : A_sg_CI S) : @A_po S :=
let eqv    := A_sg_CI_eqv _ A in
let eq     := A_eqv_eq _ eqv in
let eqvP   := A_eqv_proofs _ eqv in
let symS   := A_eqv_symmetric _ _ eqvP in
let trnS   := A_eqv_transitive _ _ eqvP in 
let bop    := A_sg_CI_bop _ A in
let sgP    := A_sg_CI_proofs _ A in
let comm   := A_sg_CI_commutative  _ _ _ sgP in 
{|
  A_po_eqv               := eqv 
; A_po_lte               := brel_lte_left eq bop 
; A_po_exists_top_d      := brel_lte_left_exists_top_decide S eq eqvP bop comm (A_sg_CI_exists_id_d _ A)
; A_po_exists_bottom_d   := brel_lte_left_exists_bottom_decide S eq eqvP bop comm (A_sg_CI_exists_ann_d _ A)
; A_po_proofs            := po_proofs_from_sg_CI_left_proofs S eq eqvP bop sgP 
; A_po_ast               := Ast_or_llte (A_sg_CI_ast _ A) 
|}.


Definition A_po_from_sg_CI_right {S : Type} (A : A_sg_CI S) : @A_po S :=
let eqv    := A_sg_CI_eqv _ A in
let eq     := A_eqv_eq _ eqv in
let eqvP   := A_eqv_proofs _ eqv in
let symS   := A_eqv_symmetric _ _ eqvP in
let trnS   := A_eqv_transitive _ _ eqvP in 
let bop    := A_sg_CI_bop _ A in
let sgP    := A_sg_CI_proofs _ A in
let comm   := A_sg_CI_commutative  _ _ _ sgP in 
{|
  A_po_eqv               := eqv 
; A_po_lte               := brel_lte_right eq bop 
; A_po_exists_top_d      := brel_lte_right_exists_top_decide S eq eqvP bop comm (A_sg_CI_exists_ann_d _ A)
; A_po_exists_bottom_d   := brel_lte_right_exists_bottom_decide S eq eqvP bop comm (A_sg_CI_exists_id_d _ A)
; A_po_proofs            := po_proofs_from_sg_CI_right_proofs S eq eqvP bop sgP 
; A_po_ast               := Ast_or_llte (A_sg_CI_ast _ A) 
|}.

Definition A_fo_from_sg_CS_left {S : Type} (A : A_sg_CS S) : @A_fo S :=
let eqv    := A_sg_CS_eqv _ A in
let wS     := A_eqv_witness _ eqv in
let f      := A_eqv_new _ eqv in
let ntS      := A_eqv_not_trivial _ eqv in 
let eq     := A_eqv_eq _ eqv in
let eqvP   := A_eqv_proofs _ eqv in
let symS   := A_eqv_symmetric _ _ eqvP in
let trnS   := A_eqv_transitive _ _ eqvP in 
let bop    := A_sg_CS_bop _ A in
let sgP    := A_sg_CS_proofs _ A in
let comm   := A_sg_CS_commutative  _ _ _ sgP in
let lte    := brel_lte_left eq bop in
let anti   := brel_lte_left_antisymmetric S eq symS trnS bop comm in 
{|
  A_fo_eqv               := eqv 
; A_fo_lte               := lte 
; A_fo_exists_top_d      := brel_exists_qo_top_decidable_from_brel_exists_top_decidable S eq lte anti
                              (brel_lte_left_exists_top_decide S eq eqvP bop comm (A_sg_CS_exists_id_d _ A))
; A_fo_exists_bottom_d   := brel_exists_qo_bottom_decidable_from_brel_exists_bottom_decidable S eq lte anti
                              (brel_lte_left_exists_bottom_decide S eq eqvP bop comm (A_sg_CS_exists_ann_d _ A))
; A_fo_proofs            := fo_proofs_from_sg_CS_left_proofs S eq eqvP bop wS f ntS sgP 
; A_fo_ast               := Ast_or_llte (A_sg_CS_ast _ A) 
|}.


Definition A_fo_from_sg_CS_right {S : Type} (A : A_sg_CS S) : @A_fo S :=
let eqv    := A_sg_CS_eqv _ A in
let wS     := A_eqv_witness _ eqv in
let f      := A_eqv_new _ eqv in
let ntS      := A_eqv_not_trivial _ eqv in 
let eq     := A_eqv_eq _ eqv in
let eqvP   := A_eqv_proofs _ eqv in
let symS   := A_eqv_symmetric _ _ eqvP in
let trnS   := A_eqv_transitive _ _ eqvP in 
let bop    := A_sg_CS_bop _ A in
let sgP    := A_sg_CS_proofs _ A in
let comm   := A_sg_CS_commutative  _ _ _ sgP in
let lte    := brel_lte_right eq bop in
let anti   := brel_lte_right_antisymmetric S eq symS trnS bop comm in 
{|
  A_fo_eqv               := eqv 
; A_fo_lte               := lte 
; A_fo_exists_top_d      := brel_exists_qo_top_decidable_from_brel_exists_top_decidable S eq lte anti
                              (brel_lte_right_exists_top_decide S eq eqvP bop comm (A_sg_CS_exists_ann_d _ A))
; A_fo_exists_bottom_d   := brel_exists_qo_bottom_decidable_from_brel_exists_bottom_decidable S eq lte anti
                              (brel_lte_right_exists_bottom_decide S eq eqvP bop comm (A_sg_CS_exists_id_d _ A))
; A_fo_proofs            := fo_proofs_from_sg_CS_right_proofs S eq eqvP bop wS f ntS sgP 
; A_fo_ast               := Ast_or_rlte (A_sg_CS_ast _ A) 
|}.
  
End Combinators.

End ACAS. 

                        
Section AMCAS.

Local Open Scope string_scope.

Definition A_below_po_from_below_sg_CI_left {S : Type} (A : @A_below_sg_CI S) : @A_below_po S :=
          A_classify_po (A_po_from_sg_CI_left (A_cast_up_sg_CI A)).

Definition A_below_fo_from_below_sg_CS_left {S : Type} (A : @A_below_sg_CS S) : @A_below_fo S :=
          A_classify_fo (A_fo_from_sg_CS_left (A_cast_up_sg_CS A)).


Definition A_mcas_po_from_sg_left {S : Type} (A : @A_sg_mcas S) : @A_qo_mcas S :=
    match A with
    | A_MCAS_sg_Error sl => A_MCAS_qo_Error sl
    | A_MCAS_sg B        => 
        match B with
        | A_Below_sg_top _      => A_MCAS_qo_Error ("mcas_po_from_sg : semigroup must be commutative" :: nil)
        | A_Below_sg_sg_C B =>
            match A_cast_below_sg_C_to_below_sg_CS B with
            | Some bcs =>
                A_MCAS_qo (
                     A_Below_qo_fo 
                       (A_below_fo_from_below_sg_CS_left bcs))
            | _ => match A_cast_below_sg_C_to_below_sg_CI B with
                   | Some bci =>
                       A_MCAS_qo (
                           A_Below_qo_po 
                             (A_below_po_from_below_sg_CI_left bci))
                   | _ => A_MCAS_qo_Error ("mcas_po_from_sg : semigroup must be selective or idempotent" :: nil)
                   end
            end
        end
    end. 

End AMCAS.

  
  
Section CAS.

Section Certify.

Definition brel_lte_left_total_certify {S : Type} 
     (D : @check_selective S) : @certify_total S  := 
     match D with
     | Certify_Selective  => Certify_Total 
     | Certify_Not_Selective p  => Certify_Not_Total p 
     end.

Definition brel_lte_right_total_certify {S : Type} 
     (D : @check_selective S) : @certify_total S  := 
     match D with
     | Certify_Selective  => Certify_Total 
     | Certify_Not_Selective p  => Certify_Not_Total p 
     end.


Definition brel_lte_left_exists_top_certify {S : Type} 
           (D : @check_exists_id S) : @certify_exists_top S := 
  match D with
  | Certify_Exists_Id id  => Certify_Exists_Top id 
  | Certify_Not_Exists_Id => Certify_Not_Exists_Top
  end. 


Definition brel_lte_right_exists_bottom_certify {S : Type} 
           (D : @check_exists_id S) : @certify_exists_bottom S := 
  match D with
  | Certify_Exists_Id id  => Certify_Exists_Bottom id 
  | Certify_Not_Exists_Id => Certify_Not_Exists_Bottom
  end. 


Definition brel_lte_left_exists_bottom_certify {S : Type} 
           (D : @check_exists_ann S) : @certify_exists_bottom S := 
  match D with
  | Certify_Exists_Ann ann  => Certify_Exists_Bottom ann 
  | Certify_Not_Exists_Ann => Certify_Not_Exists_Bottom
  end. 


Definition brel_lte_right_exists_top_certify {S : Type} 
           (D : @check_exists_ann S) : @certify_exists_top S := 
  match D with
  | Certify_Exists_Ann ann  => Certify_Exists_Top ann 
  | Certify_Not_Exists_Ann => Certify_Not_Exists_Top
  end. 

End Certify.

Section Certificates.

Definition po_certs_from_sg_CI_certs_left {S : Type}
 (P : @sg_CI_certificates S) : @po_certificates S :=
{|  
  po_congruence    := Assert_Brel_Congruence 
; po_reflexive     := Assert_Reflexive 
; po_transitive    := Assert_Transitive
; po_antisymmetric := Assert_Antisymmetric 
; po_not_total     := match sg_CI_not_selective P with
                      | Assert_Not_Selective p => Assert_Not_Total p
                      end
|}.

Definition fo_certs_from_sg_CS_certs_left {S : Type}
  (eq : brel S)
  (bop : binary_op S)
  (wS : S)
  (f : S -> S)
  (P : @sg_CS_certificates S) : @fo_certificates S :=
{|  
  fo_congruence    := Assert_Brel_Congruence 
; fo_reflexive     := Assert_Reflexive 
; fo_transitive    := Assert_Transitive
; fo_antisymmetric_d := Certify_Antisymmetric 
; fo_total         := Assert_Total
; fo_trivial_d     := Certify_Order_Not_Trivial (cef_commutative_implies_not_is_left eq bop wS f)
|}.

Definition po_certs_from_sg_CI_right_certs {S : Type} (P : @sg_CI_certificates S) : @po_certificates S :=
{|  
  po_congruence    := Assert_Brel_Congruence 
; po_reflexive     := Assert_Reflexive 
; po_transitive    := Assert_Transitive
; po_antisymmetric := Assert_Antisymmetric 
; po_not_total     := match sg_CI_not_selective P with
                      | Assert_Not_Selective p => Assert_Not_Total p
                      end
|}.
  
End Certificates.

Section Combinators.


Definition po_from_sg_CI_left {S : Type} (A : @sg_CI S) : @po S :=
let eqv    := sg_CI_eqv A in
let eq     := eqv_eq eqv in
let bop    := sg_CI_bop A in
let sgP    := sg_CI_certs A in
{|
  po_eqv               := eqv 
; po_lte               := brel_lte_left eq bop 
; po_exists_top_d      := brel_lte_left_exists_top_certify (sg_CI_exists_id_d A)
; po_exists_bottom_d   := brel_lte_left_exists_bottom_certify (sg_CI_exists_ann_d A)
; po_certs             := po_certs_from_sg_CI_certs_left sgP 
; po_ast               := Ast_or_llte (sg_CI_ast A) 
|}.


Definition fo_from_sg_CS_left {S : Type} (A : @sg_CS S) : @fo S :=
let eqv    := sg_CS_eqv A in
let wS := eqv_witness eqv in
let f := eqv_new eqv in   
let eq     := eqv_eq eqv in
let bop    := sg_CS_bop A in
let sgP    := sg_CS_certs A in
{|
  fo_eqv               := eqv 
; fo_lte               := brel_lte_left eq bop 
; fo_exists_top_d      := match sg_CS_exists_id_d A with
                          | Certify_Exists_Id i   => Certify_Exists_Qo_Top i 
                          | Certify_Not_Exists_Id => Certify_Not_Exists_Qo_Top
                          end 
; fo_exists_bottom_d   := match sg_CS_exists_ann_d A with
                          | Certify_Exists_Ann a   => Certify_Exists_Qo_Bottom a 
                          | Certify_Not_Exists_Ann => Certify_Not_Exists_Qo_Bottom
                          end 
; fo_certs             := fo_certs_from_sg_CS_certs_left eq bop wS f sgP 
; fo_ast               := Ast_or_llte (sg_CS_ast A) 
|}.


End Combinators.

End CAS.


Section MCAS.

Local Open Scope string_scope.   

Definition below_po_from_below_sg_CI_left {S : Type} (A : @below_sg_CI S) : @below_po S :=
          classify_po (po_from_sg_CI_left (cast_up_sg_CI A)).

Definition below_fo_from_below_sg_CS_left {S : Type} (A : @below_sg_CS S) : @below_fo S :=
          classify_fo (fo_from_sg_CS_left (cast_up_sg_CS A)).

Definition mcas_po_from_sg_left {S : Type} (A : @sg_mcas S) : @qo_mcas S :=
    match A with
    | MCAS_sg_Error sl => MCAS_qo_Error sl
    | MCAS_sg B        => 
        match B with
        | Below_sg_top _      => MCAS_qo_Error ("mcas_po_from_sg : semigroup must be commutative" :: nil)
        | Below_sg_sg_C B =>
            match cast_below_sg_C_to_below_sg_CS B with
            | Some bcs =>
                MCAS_qo (
                     Below_qo_fo 
                       (below_fo_from_below_sg_CS_left bcs))
            | _ => match cast_below_sg_C_to_below_sg_CI B with
                   | Some bci =>
                       MCAS_qo (
                           Below_qo_po 
                             (below_po_from_below_sg_CI_left bci))
                   | _ => MCAS_qo_Error ("mcas_po_from_sg : semigroup must be selective or idempotent" :: nil)
                   end
            end
        end
    end. 

End MCAS.

Section Verify.

Section Proofs.

Variables   
      (S : Type)
      (eq : brel S)
      (eqvP : eqv_proofs S eq)
      (bop : binary_op S)
      (wS : S)
      (f : S -> S)
      (ntS : brel_not_trivial S eq f). 


Lemma correct_po_certs_from_sg_CI_certs_left
      (P : sg_CI_proofs S eq bop) : 
      P2C_po eq (brel_lte_left eq bop) (po_proofs_from_sg_CI_left_proofs S eq eqvP bop P)
      = 
      po_certs_from_sg_CI_certs_left (P2C_sg_CI eq bop P). 
Proof. destruct P; unfold po_proofs_from_sg_CI_left_proofs, po_certs_from_sg_CI_certs_left,
                   P2C_po, P2C_sg_CI; simpl.
       destruct A_sg_CI_not_selective as [[s1 s2] [A B]]; simpl.
       unfold p2c_not_total_assert. simpl. 
       reflexivity. 
Qed. 

Lemma correct_fo_certs_from_sg_CS_certs_left
      (P : sg_CS_proofs S eq bop) : 
      P2C_fo eq (brel_lte_left eq bop) (fo_proofs_from_sg_CS_left_proofs S eq eqvP bop wS f ntS P)
      = 
      fo_certs_from_sg_CS_certs_left eq bop wS f (P2C_sg_CS eq bop P). 
Proof. destruct P; unfold fo_proofs_from_sg_CS_left_proofs, fo_certs_from_sg_CS_certs_left,
         P2C_fo, P2C_sg_CI; simpl. reflexivity. 
Qed. 

Lemma correct_po_certs_from_sg_CI_right_certs
      (P : sg_CI_proofs S eq bop) : 
      P2C_po eq (brel_lte_right eq bop) (po_proofs_from_sg_CI_right_proofs S eq eqvP bop P)
      = 
      po_certs_from_sg_CI_right_certs (P2C_sg_CI eq bop P). 
Proof. destruct P; unfold po_proofs_from_sg_CI_right_proofs, po_certs_from_sg_CI_right_certs,
                   P2C_po, P2C_sg_CI; simpl.
       destruct A_sg_CI_not_selective as [[s1 s2] [A B]]; simpl.
       unfold p2c_not_total_assert. simpl. 
       reflexivity. 
Qed. 
  
End Proofs.

Section Combinators.

Theorem correct_po_from_sg_CI_left (S : Type) (a : A_sg_CI S) : 
  po_from_sg_CI_left (A2C_sg_CI a)
  =
  A2C_po (A_po_from_sg_CI_left a). 
Proof. destruct a; unfold po_from_sg_CI_left, A_po_from_sg_CI_left, A2C_po, A2C_sg_CI; simpl. 
       rewrite correct_po_certs_from_sg_CI_certs_left.
       destruct A_sg_CI_exists_id_d as [[id P] | Q];
       destruct A_sg_CI_exists_ann_d as [[ann I] | J]; simpl; 
       try reflexivity. 
Qed. 


Theorem correct_fo_from_sg_CS_left (S : Type) (a : A_sg_CS S) : 
  fo_from_sg_CS_left (A2C_sg_CS a)
  =
  A2C_fo (A_fo_from_sg_CS_left a). 
Proof. destruct a; unfold fo_from_sg_CS_left, A_fo_from_sg_CS_left, A2C_fo, A2C_sg_CI; simpl. 
       rewrite correct_fo_certs_from_sg_CS_certs_left.
       destruct A_sg_CS_exists_id_d as [[id P] | Q];
       destruct A_sg_CS_exists_ann_d as [[ann I] | J]; simpl; 
       try reflexivity. 
Qed. 

Theorem correct_below_po_from_below_sg_CS_left (S : Type) (a : @A_below_sg_CS S) : 
  below_fo_from_below_sg_CS_left (A2C_below_sg_CS a)
  =
    A2C_below_fo (A_below_fo_from_below_sg_CS_left a).
Proof. destruct a; unfold below_fo_from_below_sg_CS_left,
         A_below_fo_from_below_sg_CS_left; simpl.
       rewrite <- correct_classify_fo. 
       rewrite correct_fo_from_sg_CS_left. 
       reflexivity. 
Qed.

Theorem correct_below_po_from_below_sg_CI_left (S : Type) (a : @A_below_sg_CI S) : 
  below_po_from_below_sg_CI_left (A2C_below_sg_CI a)
  =
  A2C_below_po (A_below_po_from_below_sg_CI_left a).
Proof. destruct a; unfold below_po_from_below_sg_CI_left,
         A_below_po_from_below_sg_CI_left; simpl.
       rewrite <- correct_classify_po. 
       rewrite correct_po_from_sg_CI_left. 
       reflexivity. 
Qed.
  
Theorem correct_mcas_po_from_sg (S : Type) (sgS : @A_sg_mcas S) : 
         mcas_po_from_sg_left (A2C_sg_mcas sgS) 
         = 
         A2C_qo_mcas (A_mcas_po_from_sg_left sgS).
Proof. destruct sgS; simpl; try reflexivity.
       destruct a; unfold mcas_po_from_sg_left, A_mcas_po_from_sg_left,
       A2C_sg_mcas, A2C_qo_mcas; simpl; try reflexivity. 
       destruct a; unfold A2C_below_sg_C,
         cast_below_sg_C_to_below_sg_CS,
         A_cast_below_sg_C_to_below_sg_CS; simpl ; try reflexivity.
       - rewrite correct_below_po_from_below_sg_CS_left.
         reflexivity. 
       - rewrite correct_below_po_from_below_sg_CI_left.
         reflexivity. 
Qed. 

End Combinators.

End Verify. 
