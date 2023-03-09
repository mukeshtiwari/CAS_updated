Require Import CAS.coq.common.compute.

Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.theory.

Require Import CAS.coq.po.properties.
Require Import CAS.coq.po.theory.
Require Import CAS.coq.po.dual.
Require Import CAS.coq.po.from_sg.

Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.theory. 

Require Import CAS.coq.os.properties.



Lemma os_left_strictly_monotone_implies_left_monotone (S : Type) (lte : brel S) (b : binary_op S):
  brel_reflexive S lte -> 
  os_left_strictly_monotone lte b ->
  bop_congruence S (equiv lte) b ->
     os_left_monotone lte b. 
Proof. intros refl LSM Cong s t u A.
       assert (lteRefl := equiv_reflexive S lte refl). 
       case_eq(lte u t); intro B.
          assert (C : equiv lte t u = true). apply equiv_intro; auto.       
          assert (D := Cong _ _ _ _ (lteRefl s) C).
          apply equiv_elim in D; auto.  destruct D as [D E]. exact E. 
          destruct (LSM s t u A B) as [C D]. exact C. 
Qed.


Lemma os_right_strictly_monotone_implies_right_monotone (S : Type) (lte : brel S) (b : binary_op S):
  brel_reflexive S lte -> 
  os_right_strictly_monotone lte b ->
  bop_congruence S (equiv lte) b ->
     os_right_monotone lte b. 
Proof. intros refl RSM Cong s t u A.
       assert (lteRefl := equiv_reflexive S lte refl). 
       case_eq(lte u t); intro B.
          assert (C : equiv lte t u = true). apply equiv_intro; auto.       
          assert (D := Cong _ _ _ _ C (lteRefl s)).
          apply equiv_elim in D; auto.  destruct D as [D E]. exact E. 
          destruct (RSM s t u A B) as [C D]. exact C. 
Qed.



(*********************** OS properties ************************************)

Section GLB_LUB_DUALITY. 
  
Variables (S : Type) (eq lte : brel S) (bS : binary_op S). 

Lemma lower_bound_implies_dual_upper_bound (s t u : S) : 
       is_lower_bound lte s t u -> is_upper_bound (brel_dual lte) s t u. 
Proof. compute. auto. Qed. 

Lemma dual_upper_bound_implies_lower_bound (s t u : S) : 
       is_upper_bound (brel_dual lte) s t u -> is_lower_bound lte s t u. 
Proof. compute. auto. Qed. 

Lemma upper_bound_implies_dual_lower_bound (s t u : S) : 
       is_upper_bound lte s t u -> is_lower_bound (brel_dual lte) s t u. 
Proof. compute. auto. Qed. 

Lemma dual_lower_bound_implies_upper_bound  (s t u : S) : 
       is_lower_bound (brel_dual lte) s t u -> is_upper_bound lte s t u. 
Proof. compute. auto. Qed. 

       
Lemma glb_implies_dual_lub (b : binary_op S) (P : bop_is_glb lte b) : bop_is_lub (brel_dual lte) b.
Proof. intros s t.
       assert (A := P s t). unfold is_glb in A. destruct A as [A B]. 
       unfold is_lub. split. 
       - apply lower_bound_implies_dual_upper_bound; auto. 
       - intros u C.
         unfold brel_dual. apply B.
         apply dual_upper_bound_implies_lower_bound; auto. 
Qed. 

Lemma lub_implies_dual_glb (b : binary_op S) (P : bop_is_lub lte b) : bop_is_glb (brel_dual lte) b.
Proof. intros s t.
       assert (A := P s t). unfold is_lub in A. destruct A as [A B]. 
       unfold is_glb. split. 
       - apply upper_bound_implies_dual_lower_bound; auto. 
       - intros u C.
         unfold brel_dual. apply B.
         apply dual_lower_bound_implies_upper_bound; auto. 
Qed. 

End GLB_LUB_DUALITY. 


Section LTE_LEFT_RIGHT_MONOTONE_INCREASING. 

Variables (S : Type)
          (eq lte : brel S)
          (s : S) (f : S -> S)
          (nt : brel_not_trivial S eq f)
          (bS : binary_op S)
          (refS : brel_reflexive S eq)
          (symS : brel_symmetric S eq)
          (trnS : brel_transitive S eq)          
          (assoS : bop_associative S eq bS)
          (congS : bop_congruence S eq bS)
          (idemS : bop_idempotent S eq bS)
          (commS : bop_commutative S eq bS).

Notation "a == b"    := (eq a b = true) (at level 30).
Notation "a != b"    := (eq a b = false) (at level 30).
Notation "a (+) b"   := (bS a b) (at level 15).

(* b == b (+) c → a (+) b == (a (+) b) (+) (a (+) c) *) 
Lemma lte_left_is_left_monotone : os_left_monotone (brel_lte_left eq bS) bS.
Proof. intros a b c. compute.   intro A.
       assert (B := idemS (a (+) b)). apply symS in B.
       assert (C := congS _ _ _ _ (refS a) A).
       assert (D := assoS a b c).  apply symS in D. 
       assert (E := trnS _ _ _ C D).
       assert (F := congS _ _ _ _ (commS a b) (refS c)). 
       assert (G := trnS _ _ _ E F).
       assert (H := assoS b a c).  
       assert (I := trnS _ _ _ G H).
       assert (J := congS _ _ _ _ (refS (a (+) b)) I). 
       assert (K := trnS _ _ _ B J).
       assert (L := assoS (a (+) b) b (a (+) c)). apply symS in L. 
       assert (M := trnS _ _ _ K L).
       assert (N := assoS a b b).
       assert (O := congS _ _ _ _ (refS a) (idemS b)).
       assert (P := trnS _ _ _ N O).
       assert (Q := congS _ _ _ _ P (refS (a (+) c))). 
       assert (R := trnS _ _ _ M Q).
       exact R. 
Qed. 

(* b == b (+) c → b (+) a == (b (+) a) (+) (c (+) a) *) 
Lemma lte_left_is_right_monotone : os_right_monotone (brel_lte_left eq bS) bS.
Proof. intros a b c. compute.   intro A.
       assert (B := lte_left_is_left_monotone a b c A). compute in B.
       assert (C := commS b a).
       assert (D := trnS _ _ _ C B).
       assert (E := congS _ _ _ _ C (commS c a)). apply symS in E. 
       assert (F := trnS _ _ _ D E).
       exact F.
Qed. 

(* c == b (+) c → a (+) c == (a (+) b) (+) (a (+) c) *) 
Lemma lte_right_is_left_monotone : os_left_monotone (brel_lte_right eq bS) bS.
Proof. intros a b c. unfold brel_lte_right. compute.   intro A.
       assert (B := commS b c).
       assert (C := trnS _ _ _ A B). 
       assert (D := lte_left_is_left_monotone a c b C). compute in D. 
       assert (E := commS (a (+) c) (a (+) b)). 
       assert (F := trnS _ _ _ D E). 
       exact F.        
Qed. 

Lemma lte_right_is_right_monotone : os_right_monotone (brel_lte_right eq bS) bS.
Proof. intros a b c. compute.   intro A.
       assert (B := lte_right_is_left_monotone a b c A). compute in B.
       assert (C := commS c a).
       assert (D := trnS _ _ _ C B).
       assert (E := congS _ _ _ _ (commS b a) C). apply symS in E. 
       assert (F := trnS _ _ _ D E).
       exact F.
Qed. 
            

Lemma lte_left_is_not_left_increasing : os_not_left_increasing (brel_lte_left eq bS) bS.
Proof. compute.
       destruct (bop_commutative_implies_not_is_left S eq bS s f nt symS trnS commS) as [[a b] A]. 
       exists (a, b).
       case_eq(eq a (a (+) (a (+) b))); intro B; auto.
       assert (C := assoS a a b). apply symS in C. 
       assert (D := trnS _ _ _ B C).
       assert (E := congS _ _ _ _ (idemS a) (refS b)).
       assert (F := trnS _ _ _ D E). apply symS in F. 
       rewrite F in A.  discriminate A. 
Qed. 

Lemma lte_left_is_not_right_increasing : os_not_right_increasing (brel_lte_left eq bS) bS.
Proof. compute. destruct lte_left_is_not_left_increasing as [[a b] A]. compute in A.
       exists (a, b).
       case_eq(eq a (a (+) (b (+) a))); intro B; auto.       
       assert (C := congS _ _ _ _ (refS a) (commS b a)).
       assert (D := trnS _ _ _ B C).
       rewrite D in A. discriminate A. 
Qed. 


Lemma lte_left_is_left_decreasing : os_left_decreasing (brel_lte_left eq bS) bS.
Proof. intros a b. compute.
       assert (A := congS _ _ _ _ (idemS a) (refS b)). apply symS in A. 
       assert (B := assoS a a b).
       assert (C := trnS _ _ _ A B).
       assert (D := commS a (a (+) b)). 
       assert (E := trnS _ _ _ C D). 
       exact E. 
Qed. 

Lemma  lte_left_is_right_decreasing : os_right_decreasing (brel_lte_left eq bS) bS.
Proof. intros a b. compute.
       assert (A := assoS b a a).
       assert (B := congS _ _ _ _  (refS b) (idemS a)). 
       assert (C := trnS _ _ _ A B). apply symS in C. 
       exact C. 
Qed. 


Lemma lte_right_is_left_increasing : os_left_increasing (brel_lte_right eq bS) bS.
Proof. intros a b. compute.
       assert (A := assoS a a b).
       assert (B := congS _ _ _ _ (idemS a) (refS b)). apply symS in B. 
       assert (C := trnS _ _ _ B A).
       exact C. 
Qed. 

Lemma  lte_right_is_right_increasing : os_right_increasing (brel_lte_right eq bS) bS.
Proof. intros a b. compute.
       assert (A := commS a (b (+) a)).
       assert (B := assoS b a a).
       assert (C := trnS _ _ _ A B).
       assert (D := congS _ _ _ _ (refS b) (idemS a)). apply symS in B. 
       assert (E := trnS _ _ _ C D). apply symS in E. 
       exact E. 
Qed. 


Lemma lte_right_is_not_right_decreasing : os_not_right_decreasing (brel_lte_right eq bS) bS.
Proof. compute.
       destruct (bop_commutative_implies_not_is_right S eq bS s f nt symS trnS commS) as [[a b] A]. 
       exists (b, a).
       case_eq(eq b ((a (+) b) (+) b)); intro B; auto.
       assert (C := assoS a b b). 
       assert (D := trnS _ _ _ B C).
       assert (E := congS _ _ _ _ (refS a) (idemS b)).
       assert (F := trnS _ _ _ D E). apply symS in F. 
       rewrite F in A.  discriminate A. 
Qed. 

Lemma lte_right_is_not_left_decreasing : os_not_left_decreasing (brel_lte_right eq bS) bS.
Proof. compute. destruct lte_left_is_not_left_increasing as [[a b] A]. compute in A.
       exists (a, b).
       case_eq(eq a ((a (+) b) (+) a)); intro B; auto.
       assert (C := commS (a (+) b) a).       
       assert (D := trnS _ _ _ B C).
       rewrite D in A. discriminate A. 
Qed. 

End LTE_LEFT_RIGHT_MONOTONE_INCREASING.

Section SG_CI_IS_SEMILATTICE.

Variables (S : Type) (eq lte : brel S) (bS : binary_op S) 
         (refS : brel_reflexive S eq)
         (symS : brel_symmetric S eq)
         (trnS : brel_transitive S eq)          
         (assoS : bop_associative S eq bS)
         (congS : bop_congruence S eq bS)
         (idemS : bop_idempotent S eq bS)
         (commS : bop_commutative S eq bS).

Notation "a == b"    := (eq a b = true) (at level 30).
Notation "a != b"    := (eq a b = false) (at level 30).
Notation "a (+) b"   := (bS a b) (at level 15).


Lemma bop_is_glb_wrt_lte_left : bop_is_glb (brel_lte_left eq bS) bS.
Proof. intros a b. split; compute. split.
       assert (F0 := idemS a). apply symS in F0.
       assert (F1 := commS a b). 
       assert (F2 := congS _ _ _ _ F0 (refS b)).
       assert (F3 := assoS a a b).        
       assert (F4 := congS _ _ _ _ (refS a) F1).
       assert (F5 := assoS a b a).  apply symS in F5.
       assert (R := trnS _ _ _ (trnS _ _ _ (trnS _ _ _ F2 F3) F4) F5).
       exact R.

       assert (F0 := idemS b). apply symS in F0. 
       assert (F1 := congS _ _ _ _ (refS a) F0).              
       assert (F2 := assoS a b b).  apply symS in F2.
       assert (R := trnS _ _ _ F1 F2).
       exact R.

       intros c [L R].
       assert (F0 := idemS c). apply symS in F0.
       assert (F1 := congS _ _ _ _ L R).
       assert (F2 := assoS c a (c (+) b)).
       assert (F3 := commS a (c (+) b)).
       assert (F4 := congS _ _ _ _ (refS c) F3).
       assert (F5 := assoS c (c (+) b) a).  apply symS in F5.
       assert (F6 := assoS c c b).  apply symS in F6.
       assert (F7 := congS _ _ _ _ F6 (refS a)).
       assert (F8 := assoS (c (+) c) b a).  
       assert (F9 := commS b a).       apply symS in F0.
       assert (F10 := congS _ _ _ _ F0 F9). apply symS in F0.
       assert (C := trnS _ _ _ (trnS _ _ _ (trnS _ _ _ (trnS _ _ _ (trnS _ _ _ (trnS _ _ _ (trnS _ _ _ F0 F1) F2) F4) F5) F7) F8) F10).       
       exact C.
Qed. 

Lemma bop_is_lub_wrt_lte_right : bop_is_lub (brel_lte_right eq bS) bS.
Proof. intros a b. split; compute. split.
       assert (F0 := idemS a). apply symS in F0. 
       assert (F1 := congS _ _ _ _ F0 (refS b)).              
       assert (F2 := assoS a a b).  
       assert (R := trnS _ _ _ F1 F2).
       exact R.
       
       assert (F0 := idemS b). apply symS in F0.
       assert (F1 := commS a b). 
       assert (F2 := congS _ _ _ _ (refS a) F0).
       assert (F3 := assoS a b b).  apply symS in F3.      
       assert (F4 := congS _ _ _ _ F1 (refS b)).
       assert (F5 := assoS b a b).  
       assert (R := trnS _ _ _ (trnS _ _ _ (trnS _ _ _ F2 F3) F4) F5).        
       exact R. 

       intros c [L R].
       assert (F0 := idemS c). apply symS in F0.
       assert (F1 := congS _ _ _ _ L R).
       assert (F2 := assoS a c (b (+) c)).
       assert (F3 := commS c (b (+) c)).
       assert (F4 := congS _ _ _ _ (refS a) F3).
       assert (F6 := assoS b c c).  
       assert (F7 := congS _ _ _ _ (refS a) F6).
       assert (F8 := assoS a b (c (+) c)).  apply symS in F8. apply symS in F0. 
       assert (F10 := congS _ _ _ _ (refS (a (+) b)) F0). apply symS in F0.
       assert (C := trnS _ _ _ (trnS _ _ _ (trnS _ _ _ (trnS _ _ _ (trnS _ _ _ (trnS _ _ _ F0 F1) F2) F4) F7) F8) F10).       
       exact C.
Qed.

         
End SG_CI_IS_SEMILATTICE.


Section GLB_LUB_Order.

Variables (S : Type)
          (eq lte : brel S)
          (refS : brel_reflexive S eq)
          (symS : brel_symmetric S eq)                              
          (trnS : brel_transitive S eq)                    
          (lteCong : brel_congruence S eq lte)          
          (lteRef : brel_reflexive S lte)
          (anti : brel_antisymmetric S eq lte)
          (bS : binary_op S)
          (bCong : bop_congruence S eq bS)
          (bAss : bop_associative S eq bS)                                        
          (bIdem : bop_idempotent S eq bS)                              
          (bComm : bop_commutative S eq bS).
          
Lemma glb_lte_true_implies_lte_left_true 
      (GLB : bop_is_glb lte bS) (a b : S) : lte a b = true -> brel_lte_left eq bS a b = true. 
Proof. compute in GLB. compute. intro A. 
       destruct (GLB a b) as [[B C] D].       
       assert (E := D _ (lteRef a, A)).
       exact (anti _ _ E B).
Qed.

Lemma glb_lte_left_true_implies_lte_true
      (GLB : bop_is_glb lte bS) (a b : S) : brel_lte_left eq bS a b = true -> lte a b = true. 
Proof. compute in GLB. compute. intro A. 
       destruct (GLB a b) as [[_ B] _].       
       assert (C := lteCong _ _ _ _ A (refS b)).
       rewrite B in C. exact C. 
Qed.

Lemma glb_lte_is_lte_left
      (GLB : bop_is_glb lte bS) (a b : S) : lte a b = brel_lte_left eq bS a b.
Proof. case_eq(lte a b); intro A; case_eq(brel_lte_left eq bS a b); intro B.
       + reflexivity. 
       + rewrite (glb_lte_true_implies_lte_left_true GLB _ _ A) in B. discriminate B.
       + rewrite (glb_lte_left_true_implies_lte_true GLB _ _ B) in A. discriminate A. 
       + reflexivity. 
Qed.

Lemma lub_lte_true_implies_lte_right_true 
      (LUB : bop_is_lub lte bS) (a b : S) : lte a b = true -> brel_lte_right eq bS a b = true. 
Proof. compute in LUB. compute. intro A. 
       destruct (LUB b a) as [[B C] D].       
       assert (E := D _ (lteRef b, A)).
       assert (F := anti _ _ B E). 
       assert (G := bComm b a).       
       assert (H := trnS _ _ _ F G).
       exact H. 
Qed.

Lemma lub_lte_right_true_implies_lte_true
      (LUB : bop_is_lub lte bS) (a b : S) : brel_lte_right eq bS a b = true -> lte a b = true. 
Proof. compute in LUB. compute. intro A. 
       destruct (LUB a b) as [[B _] _].       
       assert (C := lteCong _ _ _ _ (refS a) A).
       rewrite B in C. exact C. 
Qed.

Lemma lub_lte_is_lte_right
      (LUB : bop_is_lub lte bS) (a b : S) : lte a b = brel_lte_right eq bS a b.
Proof. case_eq(lte a b); intro A; case_eq(brel_lte_right eq bS a b); intro B.
       + reflexivity. 
       + rewrite (lub_lte_true_implies_lte_right_true LUB _ _ A) in B. discriminate B.
       + rewrite (lub_lte_right_true_implies_lte_true LUB _ _ B) in A. discriminate A. 
       + reflexivity. 
Qed.

Theorem glb_is_left_monotone 
  (GLB : bop_is_glb lte bS) : os_left_monotone lte bS. 
Proof. assert (A := glb_lte_is_lte_left GLB).
       intros a b c. 
       assert (C := lte_left_is_left_monotone _ _ _ refS symS trnS bAss bCong bIdem bComm a b c).
       rewrite (A b c). rewrite (A (bS a b) (bS a c)). 
       exact C. 
Qed. 

Theorem glb_is_right_monotone 
  (GLB : bop_is_glb lte bS) : os_right_monotone lte bS. 
Proof. assert (A := glb_lte_is_lte_left GLB).
       intros a b c. 
       assert (C := lte_left_is_right_monotone _ _ _ refS symS trnS bAss bCong bIdem bComm a b c).
       rewrite (A b c). rewrite (A (bS b a) (bS c a)). 
       exact C. 
Qed. 

Theorem lub_is_left_monotone 
  (LUB : bop_is_lub lte bS) : os_left_monotone lte bS. 
Proof. assert (A := lub_lte_is_lte_right LUB).
       intros a b c. 
       assert (C := lte_right_is_left_monotone _ _ _ refS symS trnS bAss bCong bIdem bComm a b c).
       rewrite (A b c). rewrite (A (bS a b) (bS a c)). 
       exact C. 
Qed. 

Theorem lub_is_right_monotone 
  (LUB : bop_is_lub lte bS) : os_right_monotone lte bS. 
Proof. assert (A := lub_lte_is_lte_right LUB).
       intros a b c. 
       assert (C := lte_right_is_right_monotone _ _ _ refS symS trnS bAss bCong bIdem bComm a b c).
       rewrite (A b c). rewrite (A (bS b a) (bS c a)). 
       exact C. 
Qed. 


Theorem lub_is_left_increasing 
  (LUB : bop_is_lub lte bS) : os_left_increasing lte bS. 
Proof. assert (A := lub_lte_is_lte_right LUB).
       intros a b. 
       assert (C := lte_right_is_left_increasing _ _ _ refS symS trnS bAss bCong bIdem a b).
       rewrite (A a (bS a b)). 
       exact C. 
Qed. 

Theorem lub_is_right_increasing 
  (LUB : bop_is_lub lte bS) : os_right_increasing lte bS. 
Proof. assert (A := lub_lte_is_lte_right LUB).
       intros a b. 
       assert (C := lte_right_is_right_increasing _ _ _ refS symS trnS bAss bCong bIdem bComm a b).
       rewrite (A a (bS b a)). 
       exact C. 
Qed.

Lemma lub_from_monotone_increasing 
      (LM : os_left_monotone lte bS) (* Note : LM and commutativity gives RM *)
      (RM : os_right_monotone lte bS) 
      (LI : os_left_increasing lte bS) 
      (RI : os_right_increasing lte bS) : bop_is_lub lte bS.
Proof. compute. compute in LM, LI, RI. 
       intros s t. split. split.
       apply LI. apply RI.
       intros u [A B].
       assert (C := LM t s u A).
       assert (E := LI u t).
       rewrite (lteCong _ _ _ _ (refS u) (bComm u t)) in E.
       assert (F : lte (bS t u) u = true).
          assert (G := RM u t u B). 
          rewrite (lteCong _ _ _ _ (refS (bS t u)) (bIdem u)) in G. 
           exact G. 
       assert (H := anti _ _ E F).
       rewrite (lteCong _ _ _ _ (bComm s t) H). 
       exact C. 
Qed. 

End GLB_LUB_Order. 



