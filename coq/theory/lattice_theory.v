Require Export CAS.coq.common.compute.
Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.or.properties. 
Require Import CAS.coq.sg.properties.
Require Import CAS.coq.bs.properties.

Section LatticeTheory.  (* (S, join, meet) *) 

Variable S : Type.
Variable eqv : brel S.


Variable ref : brel_reflexive S eqv. 
Variable sym : brel_symmetric S eqv.
Variable trn : brel_transitive S eqv.

Variable join : binary_op S.  
Variable meet : binary_op S.
 
Variable j_cng : bop_congruence S eqv join.
Variable j_ass : bop_associative S eqv join.
Variable j_com : bop_commutative S eqv join.
Variable j_idm : bop_idempotent S eqv join.

Variable m_cng : bop_congruence S eqv meet.
Variable m_ass : bop_associative S eqv meet.
Variable m_com : bop_commutative S eqv meet.
Variable m_idm : bop_idempotent S eqv meet.

Variable abs      : A_bs_left_absorptive eqv join meet.
Variable abs_dual : A_bs_left_absorptive eqv meet join. 

Notation "a == b"    := (eqv a b = true) (at level 30).
Notation "a != b"    := (eqv a b = false) (at level 15).
Notation "a (j) b"   := (join a b) (at level 15).
Notation "a (m) b"   := (meet a b) (at level 15).

(* H : a (m) b = a 
    so b (j) (a (m) b) = b (j) a (cng) 
                       = a (j) b (com)

   b = b (j) (b (m) a)  (abs) 
     = b (j) (a (m) b)  (com) 
     = a (j) b          (trn) 
*)
Lemma lattice_meet_to_join_left : ∀ (a b : S),  a == a (m) b → b == a (j) b.
Proof. intros a b H.
       assert (F1 := abs b a).
       assert (F2 := m_com a b). apply sym in F2.       
       assert (F4 := j_cng _ _ _ _ (ref b) F2).
       assert (F5 := trn _ _ _ F1 F4). apply sym in H. 
       assert (F6 := j_cng _ _ _ _ (ref b) H).
       assert (F7 := trn _ _ _ F5 F6).
       assert (F8 := j_com b a).
       assert (F9 := trn _ _ _ F7 F8).
       exact F9.
Defined. 

(* H : a = b (m) a 
   b = b (j) (b (m) a)  (abs) 
     = b (j) a          (H, cng) 
*)
Lemma lattice_meet_to_join_right : ∀ (a b : S),  a == b (m) a → b == b (j) a.
Proof. intros a b H.
       assert (F1 := abs b a).
       assert (F2 := j_cng _ _ _ _ (ref b) H). apply sym in F2. 
       assert (F3 := trn _ _ _ F1 F2). 
       exact F3.
Defined. 

(* H : a (j) b = a 
    so b (m) (a (j) b) = b (m) a (cng) 
                       = a (m) b (com)

   b = b (m) (b (j) a)  (abs) 
     = b (m) (a (j) b)  (com) 
     = a (m) b          (trn) 
*)
Lemma lattice_join_to_meet_left : ∀ (a b : S),  a == a (j) b → b == a (m) b.
Proof. intros a b H.
       assert (F1 := abs_dual b a).
       assert (F2 := j_com a b). apply sym in F2.       
       assert (F4 := m_cng _ _ _ _ (ref b) F2).
       assert (F5 := trn _ _ _ F1 F4). apply sym in H. 
       assert (F6 := m_cng _ _ _ _ (ref b) H).
       assert (F7 := trn _ _ _ F5 F6).
       assert (F8 := m_com b a).
       assert (F9 := trn _ _ _ F7 F8).
       exact F9.
Qed.

(* H : a = b (j) a 
   b = b (m) (b (j) a)  (abs_dual) 
     = b (j) a          (H, cng) 
*)
Lemma lattice_join_to_meet_right : ∀ (a b : S),  a == b (j) a → b == b (m) a.
Proof. intros a b H.
       assert (F1 := abs_dual b a).
       assert (F2 := m_cng _ _ _ _ (ref b) H). apply sym in F2. 
       assert (F3 := trn _ _ _ F1 F2). 
       exact F3.
Defined. 


Lemma lattice_one_is_join_annihilator: ∀ (i : S),  bop_is_id S eqv meet i → bop_is_ann S eqv join i. 
Proof. intros i H a. destruct (H a) as [L R]. apply sym in L. apply sym in R. 
       apply lattice_meet_to_join_left in R.
       split.
       assert (F1 := j_com a i).
       assert (F2 := trn _ _ _ R F1).
       apply sym. exact F2.       
       apply sym. exact R.
Defined. 

Lemma lattice_join_annihilator_is_one : ∀ (i : S),  bop_is_ann S eqv join i  → bop_is_id S eqv meet i. 
Proof. intros i H a. destruct (H a) as [L R]. apply sym in L. apply sym in R. 
       apply lattice_join_to_meet_left in L.
       split.
       apply sym. exact L.       
       assert (F1 := m_com i a).
       assert (F2 := trn _ _ _ L F1).
       apply sym. exact F2.       
Qed.        

Lemma lattice_not_one_is_not_join_annihilator: ∀ (i : S),  bop_not_is_id S eqv meet i → bop_not_is_ann S eqv join i. 
Proof. intros i H. destruct H as [w [H | H]]; exists w.
       left.
       case_eq(eqv (i (j) w) i); intro J.
          apply sym in J. apply lattice_join_to_meet_left in J. apply sym in J. rewrite H in J. discriminate. 
          reflexivity.
       right.
       case_eq(eqv (w (j) i) i); intro J.
          apply sym in J. apply lattice_join_to_meet_right in J. apply sym in J. rewrite H in J. discriminate. 
          reflexivity.
Qed.        

Lemma lattice_zero_is_meet_annihilator: ∀ (i : S),  bop_is_id S eqv join i → bop_is_ann S eqv meet i. 
Proof. intros i H a. destruct (H a) as [L R]. apply sym in L. apply sym in R. 
       apply lattice_join_to_meet_left in R.
       split.
       assert (F1 := m_com a i).
       assert (F2 := trn _ _ _ R F1).
       apply sym. exact F2.       
       apply sym. exact R.
Qed.


Lemma lattice_meet_annihilator_is_zero : ∀ (i : S),  bop_is_ann S eqv meet i  → bop_is_id S eqv join i. 
Proof. intros i H a. destruct (H a) as [L R]. apply sym in L. apply sym in R. 
       apply lattice_meet_to_join_left in L.
       split.
       apply sym. exact L.       
       assert (F1 := j_com i a).
       assert (F2 := trn _ _ _ L F1).
       apply sym. exact F2.       
Qed.

Lemma lattice_not_zero_is_not_meet_annihilator: ∀ (i : S),  bop_not_is_id S eqv join i → bop_not_is_ann S eqv meet i. 
Proof. intros i H. destruct H as [w [H | H]]; exists w.
       left.
       case_eq(eqv (i (m) w) i); intro J.
          apply sym in J. apply lattice_meet_to_join_left in J. apply sym in J. rewrite H in J. discriminate. 
          reflexivity.
       right.
       case_eq(eqv (w (m) i) i); intro J.
          apply sym in J. apply lattice_meet_to_join_right in J. apply sym in J. rewrite H in J. discriminate. 
          reflexivity.
Qed.        


(*
  exists meet id <-> exists join annihilator 
*) 
Lemma lattice_exists_meet_id_implies_exists_join_ann : bop_exists_id S eqv meet -> bop_exists_ann S eqv join.  
Proof. intros [i P]. exists i. apply lattice_one_is_join_annihilator; auto. Defined. 

Lemma lattice_exists_join_ann_implies_exists_meet_id :  bop_exists_ann S eqv join -> bop_exists_id S eqv meet.  
Proof. intros [a P]. exists a. apply lattice_join_annihilator_is_one; auto. Defined. 

(*
  exists join id <-> exists meet annihilator 
*) 
Lemma lattice_exists_join_id_implies_exists_meet_ann : bop_exists_id S eqv join -> bop_exists_ann S eqv meet.  
Proof. intros [i P]. exists i. apply lattice_zero_is_meet_annihilator; auto. Defined. 

Lemma lattice_exists_meet_ann_implies_exists_join_id :  bop_exists_ann S eqv meet -> bop_exists_id S eqv join.  
Proof. intros [a P]. exists a. apply lattice_meet_annihilator_is_zero; auto. Defined.

(*
  exists join id <-> join id = meet annihilator 
*) 
Lemma lattice_exists_join_id_implies_join_id_equals_meet_ann : bop_exists_id S eqv join -> A_bs_exists_id_ann_equal eqv join meet.
Proof. intros [i P]. exists i. split. exact P. apply lattice_zero_is_meet_annihilator. exact P. Qed. 

(*
Lemma lattice_not_exists_join_id_implies_not_join_id_equals_meet_ann : bop_not_exists_id S eqv join -> bops_not_id_equals_ann S eqv join meet.
Proof. unfold bops_not_id_equals_ann, bop_not_exists_id. intros H s. right.
       apply lattice_not_zero_is_not_meet_annihilator. apply H.
Qed.        
*) 
(*
  exists meet id <-> meet id = join annihilator 
*) 
Lemma lattice_exists_meet_id_implies_meet_id_equals_join_ann : bop_exists_id S eqv meet -> A_bs_exists_id_ann_equal eqv meet join.
Proof. intros [i P]. exists i. split. exact P. apply lattice_one_is_join_annihilator. exact P. Qed. 

(*
Lemma lattice_not_exists_meet_id_implies_not_meet_id_equals_join_ann : bop_not_exists_id S eqv meet -> bops_not_id_equals_ann S eqv meet join.
Proof. unfold bops_not_id_equals_ann, bop_not_exists_id. intros H s. right.
       apply lattice_not_one_is_not_join_annihilator. apply H.
Qed.
*) 
(* selectivity *) 
Lemma join_selective_implies_meet_selective : bop_selective S eqv join -> bop_selective S eqv meet.
Proof. intros selS a b. destruct (selS a b) as [J1 | J1].
          assert (J2 := lattice_join_to_meet_left a b). 
          right. exact (sym _ _ (J2 (sym _ _ J1))). 
          assert (J2 := lattice_join_to_meet_right b a). 
          left. exact (sym _ _ (J2 (sym _ _ J1))). 
Qed. 

Lemma meet_selective_implies_join_selective : bop_selective S eqv meet -> bop_selective S eqv join.
Proof. intros selS a b. destruct (selS a b) as [J1 | J1].
          assert (J2 := lattice_meet_to_join_left a b). 
          right. exact (sym _ _ (J2 (sym _ _ J1))). 
          assert (J2 := lattice_meet_to_join_right b a). 
          left. exact (sym _ _ (J2 (sym _ _ J1))). 
Qed. 

  
(* distributive  <-> distributive dual *)

Lemma lattice_distributive_implies_distributive_dual : A_bs_left_distributive eqv join meet -> A_bs_left_distributive eqv meet join. 
Proof. intros D a b c. apply sym.
       assert (F0 := D (a (j) b) a c).
       assert (F1 := abs_dual a b).
       assert (F2 := m_com a (a (j) b)). 
       assert (F3 := trn _ _ _ F1 F2).  apply sym in F3. 
       assert (F4 := m_com (a (j) b) c).
       assert (F5 := D c a b).       
       assert (F6 := trn _ _ _ F4 F5).
       assert (F7 := j_cng _ _ _ _ F3 F6).
       assert (F8 := trn _ _ _ F0 F7).
       assert (F9 := m_com c a).
       assert (F10 := m_com c b).
       assert (F11 := j_cng _ _ _ _ F9 F10).
       assert (F12 := j_cng _ _ _ _ (ref a) F11).
       assert (F13 := trn _ _ _ F8 F12).
       assert (F14 := j_ass a (a (m) c) (b (m) c)). apply sym in F14.
       assert (F15 := trn _ _ _ F13 F14).
       assert (F16 := abs a c). apply sym in F16.
       assert (F17 := j_cng _ _ _ _ F16 (ref (b (m) c))).
       assert (R := trn _ _ _ F15 F17).
       exact R. 
Qed.


Lemma lattice_distributive_dual_implies_distributive : A_bs_left_distributive eqv meet join -> A_bs_left_distributive eqv join meet. 
Proof. intros D a b c. apply sym.
       assert (F0 := D (a (m) b) a c).
       assert (F1 := abs a b).
       assert (F2 := j_com a (a (m) b)).
       assert (F3 := trn _ _ _ F1 F2).  apply sym in F3. 
       assert (F4 := j_com (a (m) b) c).
       assert (F5 := D c a b).       
       assert (F6 := trn _ _ _ F4 F5).
       assert (F7 := m_cng _ _ _ _ F3 F6).
       assert (F8 := trn _ _ _ F0 F7).
       assert (F9 := j_com c a).
       assert (F10 := j_com c b).
       assert (F11 := m_cng _ _ _ _ F9 F10).
       assert (F12 := m_cng _ _ _ _ (ref a) F11).
       assert (F13 := trn _ _ _ F8 F12).
       assert (F14 := m_ass a (a (j) c) (b (j) c)). apply sym in F14.
       assert (F15 := trn _ _ _ F13 F14).
       assert (F16 := abs_dual a c). apply sym in F16.
       assert (F17 := m_cng _ _ _ _ F16 (ref (b (j) c))).
       assert (R := trn _ _ _ F15 F17).
       exact R. 
Qed.

(* Could be useful.  Move to ? 

proofs do not use absorption 

a == a (m) 1 
  == a (m) (1 (j) b) 
  == (a (m) 1) (j)  (a (m) b)
  == a (j) (a (m) b)
 *)
Lemma lattice_fact : A_bs_exists_id_ann_equal eqv meet join -> A_bs_left_distributive eqv join meet -> A_bs_left_absorptive eqv join meet.
Proof. intros [i [P Q]] D a b.
       destruct (P a) as [_ R]. apply sym in R.
       destruct (Q b) as [U _]. apply sym in U.
       assert (F1 := m_cng _ _ _ _ (ref a) U).
       assert (F2 := D a i b).  apply sym in R.
       assert (F3 := j_cng _ _ _ _ R (ref (a (m) b))). apply sym in R.
       assert (C := trn _ _ _ (trn _ _ _ (trn _ _ _ R F1) F2) F3). 
       exact C.
Qed.        

Lemma lattice_fact_dual : A_bs_exists_id_ann_equal eqv join meet -> A_bs_left_distributive eqv meet join -> A_bs_left_absorptive eqv meet join.
Proof. intros [i [P Q]] D a b.
       destruct (P a) as [L R]. apply sym in R.
       destruct (Q b) as [U V]. apply sym in U.
       assert (F1 := j_cng _ _ _ _ (ref a) U).
       assert (F2 := D a i b).  apply sym in R.
       assert (F3 := m_cng _ _ _ _ R (ref (a (j) b))). apply sym in R.
       assert (C := trn _ _ _ (trn _ _ _ (trn _ _ _ R F1) F2) F3). 
       exact C.
Qed.        

End LatticeTheory.
