From Coq Require Import
     List
     BinNatDef.
From CAS Require Import
     coq.common.compute     
     coq.eqv.properties
     coq.eqv.list
     coq.eqv.nat
     coq.eqv.nat     
     coq.uop.properties     
     coq.sg.properties
     coq.ltr.properties
     coq.rtr.properties
     coq.sg.and
     coq.sg_ltr.properties
     coq.sg_rtr.properties          
     coq.bs.properties
     coq.algorithms.list_congruences
     coq.algorithms.big_plus
     coq.algorithms.matrix_definition
     coq.algorithms.matrix_algorithms
     coq.algorithms.matrix_addition
     coq.algorithms.ltr_matrix_multiplication
     coq.algorithms.rtr_matrix_multiplication.
Import ListNotations.

Section Matrix_Multiplication.

  Variables
    (R : Type)
    (eqR  : brel R)
    (refR : brel_reflexive R eqR)
    (symR : brel_symmetric R eqR)
    (trnR : brel_transitive R eqR)
    (zeroR oneR : R) (* 0 and 1 *)
    (plusR mulR: binary_op R)
    (congrP : bop_congruence R eqR plusR)
    (congrM : bop_congruence R eqR mulR)
    (congrR : brel_congruence R eqR eqR).

  Local Notation "~R m" := (functional_matrix_congruence _ eqR m) (at level 70).
  Local Infix "+" := plusR.
  Local Infix "*" := mulR.
  Local Notation "0" := zeroR.
  Local Notation "1" := oneR.
  Local Notation "a =n= b" := (brel_eq_nat a b = true) (at level 70).
  Local Notation "a =r= b" := (eqR a b = true) (at level 70).
  Local Infix "=n?=" := brel_eq_nat (at level 70).  
  Local Notation "a +M b" := (matrix_add plusR a b) (at level 70).
  Local Notation "a *[ n ] b" := (matrix_mul 0 plusR mulR n a b) (at level 70).
  Local Notation "a =M= b" := (eq_functional_matrix_prop R eqR a b) (at level 70).

  Lemma bop_left_distribitive_implies_slt_distributive
      (LD: A_bs_left_distributive eqR plusR mulR) :
         A_sg_ltr_distributive eqR plusR mulR. 
  Proof. apply LD. Qed.

  Lemma bop_right_distribitive_implies_srt_distributive
      (LD: A_bs_right_distributive eqR plusR mulR) :
         A_sg_rtr_distributive eqR plusR mulR. 
  Proof. apply LD. Qed.

  Lemma bop_is_ann_implies_ltr_is_ann (s : R) 
    (ann : bop_is_ann R eqR mulR s) : A_ltr_is_ann eqR mulR s.
  Proof. intro l. apply (ann l). Qed. 

  Lemma bop_is_ann_implies_rtr_is_ann (s : R) 
    (ann : bop_is_ann R eqR mulR s) : A_rtr_is_ann eqR mulR s.
  Proof. intro l. apply (ann l). Qed. 

  Lemma bop_big_plus_left_distributive
        (LD: A_bs_left_distributive eqR plusR mulR) 
        (mulANN : bop_is_ann R eqR mulR 0)
          (v : R) (f : nat -> R) (l : list nat) : v * (big_plus zeroR plusR f l) =r= big_plus zeroR plusR (fun h => v* (f h)) l.
  Proof. assert (A := bop_left_distribitive_implies_slt_distributive LD).
         assert (B := bop_is_ann_implies_ltr_is_ann 0 mulANN). 
         apply big_plus_left_distributive; auto. 
  Qed.

  Lemma bop_big_plus_right_distributive
        (mulANN : bop_is_ann R eqR mulR 0)
        (RD : A_bs_right_distributive eqR plusR mulR)
        (v : R) (f : nat -> R) (l : list nat) : (big_plus zeroR plusR f l) * v =r= big_plus zeroR plusR (fun h => (f h) * v) l.
  Proof. assert (A := bop_right_distribitive_implies_srt_distributive RD).
         assert (B := bop_is_ann_implies_rtr_is_ann 0 mulANN). 
         apply big_plus_right_distributive; auto. 
  Qed.


  Local Lemma rewrite_lemma
        (plus_associative : bop_associative R eqR plusR)
        (plus_commutative  : bop_commutative R eqR plusR)
        (a b c d : R) : (a + b) + (c + d) =r= (a + c) + (b + d). 
  Proof. (*   (a + b) + (c + d)
              ={assoc} 
              a + (b + (c + d))
              = {assoc, cong} 
              a + ((b + c) + d)
              = {comm, cong} 
              a + ((c + b) + d)             
              = {assoc, cong} 
              a + (c + (b + d))             
              = {assoc} 
              (a + c) + (b + d)
      
          *)
    assert (A : (a + b) + (c + d) =r= a + (b + (c + d))).
        apply plus_associative. 
    assert (B : a + (b + (c + d)) =r= a + ((b + c) + d)).
        apply congrP. apply refR. apply symR. 
        apply plus_associative.         
    assert (C : a + ((b + c) + d) =r= a + ((c + b) + d)).
        apply congrP. apply refR. apply congrP.
        apply plus_commutative. apply refR. 
    assert (D : a + ((c + b) + d) =r= a + (c + (b + d))).
        apply congrP. apply refR. apply plus_associative.         
    assert (E : a + (c + (b + d)) =r= (a + c) + (b + d)).
        apply symR. apply plus_associative.         
    exact (trnR _ _ _ (trnR _ _ _ (trnR _ _ _ (trnR _ _ _ A B) C) D) E).
Qed. 

  Lemma switch
        (plus_associative : bop_associative R eqR plusR)
        (plus_commutative  : bop_commutative R eqR plusR)
        (plusID : bop_is_id R eqR plusR 0)
        (v : R) (f : nat -> nat -> R) :
    ∀ l, big_plus zeroR plusR (λ q1, big_plus zeroR plusR (λ q2, f q1 q2) l) l
          =r=
          big_plus zeroR plusR (λ q2, big_plus zeroR plusR (λ q1, f q1 q2) l) l.
  Proof. induction l.
         + compute. apply refR. 
         + unfold big_plus. simpl.
           fold (big_plus 0 plusR (λ q2 : nat, f a q2) l).
           fold (big_plus 0 plusR (λ q1 : nat, f q1 a) l).
           fold (big_plus 0 plusR (λ q1 : nat, f q1 a + fold_right plusR 0 (map (λ q2 : nat, f q1 q2) l)) l).
           fold (big_plus 0 plusR (λ q2 : nat, f a q2 + fold_right plusR 0 (map (λ q1 : nat, f q1 q2) l)) l). 
           (* show 
               f a a + 
               big_plus 0 plusR (λ q2 : nat, f a q2) l +
               big_plus 0 plusR (λ q1 : nat, f q1 a + fold_right plusR 0 (map (λ q2 : nat, f q1 q2) l)) l 
               =r=
               f a a + 
               big_plus 0 plusR (λ q1 : nat, f q1 a) l +
               big_plus 0 plusR (λ q2 : nat, f a q2 + fold_right plusR 0 (map (λ q1 : nat, f q1 q2) l)) l
            *)
           assert (A := big_plus_left_function_distribution _ _ refR symR trnR 0 plusR congrP plus_associative plus_commutative plusID
                           (λ q1, f q1 a) (λ q1, fold_right plusR 0 (map (λ q2 : nat, f q1 q2) l)) l).
           simpl in A. 
           assert (B := big_plus_left_function_distribution _ _ refR symR trnR 0 plusR congrP plus_associative plus_commutative plusID
                           (λ q2, f a q2) (λ q2, fold_right plusR 0 (map (λ q1 : nat, f q1 q2) l)) l).
           simpl in B. 
           assert (C : f a a +
                       big_plus 0 plusR (λ q2 : nat, f a q2) l +
                       big_plus 0 plusR (λ q1 : nat, f q1 a + fold_right plusR 0 (map (λ q2 : nat, f q1 q2) l)) l
                       =r=
                       f a a +
                       big_plus 0 plusR (λ q2 : nat, f a q2) l +
                       (big_plus 0 plusR (λ q1 : nat, f q1 a) l +
                        big_plus 0 plusR (λ q1 : nat, fold_right plusR 0 (map (λ q2 : nat, f q1 q2) l)) l)).
              apply congrP. apply refR. exact A. 
           assert (D : f a a +
                       big_plus 0 plusR (λ q2 : nat, f a q2) l +
                       (big_plus 0 plusR (λ q1 : nat, f q1 a) l +
                        big_plus 0 plusR (λ q1 : nat, fold_right plusR 0 (map (λ q2 : nat, f q1 q2) l)) l)
                       =r=
                       f a a +
                       big_plus 0 plusR (λ q1 : nat, f q1 a) l +
                       (big_plus 0 plusR (λ q2 : nat, f a q2) l +
                        big_plus 0 plusR (λ q : nat, fold_right plusR 0 (map (λ q2 : nat, f q q2) l)) l)).
              apply rewrite_lemma; auto. 
           assert (E : f a a +
                       big_plus 0 plusR (λ q1 : nat, f q1 a) l +
                       (big_plus 0 plusR (λ q2 : nat, f a q2) l +
                        big_plus 0 plusR (λ q : nat, fold_right plusR 0 (map (λ q2 : nat, f q q2) l)) l)
                       =r=
                       f a a +
                       big_plus 0 plusR (λ q1 : nat, f q1 a) l +
                       big_plus 0 plusR (λ q2 : nat, f a q2 + fold_right plusR 0 (map (λ q1 : nat, f q1 q2) l)) l).
              apply congrP; auto.
              apply symR.
              assert (F :   big_plus 0 plusR (λ q2 : nat, f a q2) l +
                            big_plus 0 plusR (λ q : nat, fold_right plusR 0 (map (λ q2 : nat, f q q2) l)) l
                            =r= 
                            big_plus 0 plusR (λ q2 : nat, f a q2) l +
                            big_plus 0 plusR (λ q2 : nat, fold_right plusR 0 (map (λ q1 : nat, f q1 q2) l)) l).
                 apply congrP; auto. 
              exact (trnR _ _ _ B (symR _ _ F)). 
           exact (trnR _ _ _ (trnR _ _ _ C D) E). 
Qed. 
  
  Lemma matrix_mul_associative
        (plus_associative : bop_associative R eqR plusR)
        (plus_commutative  : bop_commutative R eqR plusR)
        (plusID : bop_is_id R eqR plusR 0)
        (mul_associative : bop_associative R eqR mulR)
        (mulANN : bop_is_ann R eqR mulR 0)
        (left_distributive_mul_over_plus : A_bs_left_distributive eqR plusR mulR) 
        (right_distributive_mul_over_plus : A_bs_right_distributive eqR plusR mulR)
        (n : nat) : 
    ∀ m₁ m₂ m₃,  ~R m₁ -> ~R m₂ -> ~R m₃ -> 
                 (m₁ *[n] (m₂ *[n] m₃)) =M= ((m₁ *[n] m₂) *[n] m₃).
    Proof. intros m₁ m₂ m₃ cong1 cong2 cong3 i j.
           unfold matrix_mul, left_matrix_mul. unfold left_row_i_dot_col_j.
           assert (A : big_plus 0 plusR
                              (λ q : nat, m₁ i q * big_plus 0 plusR
                                                   (λ q0 : nat, m₂ q q0 * m₃ q0 j)
                                                   (list_enum n))
                              (list_enum n)
                       =r=
                       big_plus 0 plusR
                              (λ q : nat, big_plus 0 plusR
                                                 (λ q0 : nat, m₁ i q * (m₂ q q0 * m₃ q0 j))
                                                 (list_enum n))
                              (list_enum n)).
              apply big_plus_congruence_v2; auto. 
              intros i0 j0 A. 
              apply big_plus_congruence; auto. 
              intros i1 j1 B.
              apply congrM.
              exact (cong1 _ _ _ _ (brel_eq_nat_reflexive i) A). 
              apply congrM.
              exact (cong2 _ _ _ _ A B). 
              exact (cong3 _ _ _ _ B (brel_eq_nat_reflexive j)). 
              intros i0.
              apply big_plus_left_distributive; auto.
              apply bop_is_ann_implies_ltr_is_ann; auto. 

           assert (B : big_plus 0 plusR
                              (λ q : nat, big_plus 0 plusR
                                                 (λ q0 : nat, m₁ i q * (m₂ q q0 * m₃ q0 j))
                                                 (list_enum n))
                              (list_enum n)
                       =r=
                       big_plus 0 plusR
                              (λ q : nat, big_plus 0 plusR
                                                 (λ q0 : nat, (m₁ i q * m₂ q q0) * m₃ q0 j)
                                                 (list_enum n))
                              (list_enum n)).
              apply big_plus_congruence_v2; auto. 
              intros i1 j0 B. 
              apply big_plus_congruence; auto. 
              intros i2 j1 C.
              apply congrM.
              apply congrM.              
              exact (cong1 _ _ _ _ (brel_eq_nat_reflexive i) B).               
              exact (cong2 _ _ _ _ B C).               
              exact (cong3 _ _ _ _ C (brel_eq_nat_reflexive j)).               
              intros i1.
              apply big_plus_congruence_v2; auto.
              intros i2 j0 D.
              apply congrM. 
              apply congrM.
              exact (cong1 _ _ _ _ (brel_eq_nat_reflexive i) (brel_eq_nat_reflexive i1)).                             
              exact (cong2 _ _ _ _ (brel_eq_nat_reflexive i1) D).                             
              exact (cong3 _ _ _ _ D (brel_eq_nat_reflexive j)).                             

           assert (C : big_plus 0 plusR
                              (λ q : nat, big_plus 0 plusR
                                                 (λ q0 : nat, (m₁ i q * m₂ q q0) * m₃ q0 j)
                                                 (list_enum n))
                              (list_enum n)
                       =r=
                       big_plus 0 plusR
                              (λ q0 : nat, big_plus 0 plusR
                                                 (λ q : nat, (m₁ i q * m₂ q q0) * m₃ q0 j)
                                                 (list_enum n))
                              (list_enum n)).
              apply switch; auto. 

           assert (D : big_plus 0 plusR
                              (λ q0 : nat, big_plus 0 plusR
                                                 (λ q : nat, (m₁ i q * m₂ q q0) * m₃ q0 j)
                                                 (list_enum n))
                              (list_enum n)
                       =r=
                       big_plus 0 plusR
                              (λ q0 : nat, (big_plus 0 plusR
                                                 (λ q : nat, m₁ i q * m₂ q q0) 
                                                 (list_enum n)) * m₃ q0 j)
                              (list_enum n)).
              apply big_plus_congruence_v2; auto. 
              intros i0 j0 E. 
              apply congrM.
              apply big_plus_congruence; auto. 
              intros i1 j1 F.
              apply congrM.
              exact (cong1 _ _ _ _ (brel_eq_nat_reflexive i) F).
              exact (cong2 _ _ _ _ F E).
              exact (cong3 _ _ _ _ E (brel_eq_nat_reflexive j)).                                                                                             
              intros i0.
              apply symR. 
              apply big_plus_right_distributive; auto.
              apply bop_is_ann_implies_rtr_is_ann; auto.               
              exact (trnR _ _ _ (trnR _ _ _ (trnR _ _ _ A B) C) D). 
Qed. 


    Lemma bop_big_plus_distributes_over_left_row_i_dot_col_j
          (plus_associative : bop_associative R eqR plusR)
          (plus_commutative  : bop_commutative R eqR plusR)
          (plusID : bop_is_id R eqR plusR 0)
          (LD : A_bs_left_distributive eqR plusR mulR)
          (l : list nat) : 
      ∀ m₁ m₂ m₃ i j,
        big_plus zeroR plusR (left_row_i_dot_col_j mulR m₁ (λ c d : nat, m₂ c d + m₃ c d) i j) l 
        =r=
        big_plus zeroR plusR (left_row_i_dot_col_j mulR m₁ m₂ i j) l + big_plus zeroR plusR (left_row_i_dot_col_j mulR m₁ m₃ i j) l.
    Proof. assert (A := bop_left_distribitive_implies_slt_distributive LD).
           apply big_plus_distributes_over_left_row_i_dot_col_j; auto. 
    Qed. 
                 
    Lemma matrix_mul_left_distributive_over_matrix_add
          (plus_associative : bop_associative R eqR plusR)
          (plus_commutative  : bop_commutative R eqR plusR)
          (plusID : bop_is_id R eqR plusR 0)
          (left_distributive_mul_over_plus : A_bs_left_distributive eqR plusR mulR)
          (n : nat) : 
      ∀ m₁ m₂ m₃, (m₁ *[n] (m₂ +M m₃)) =M= ((m₁ *[n] m₂) +M (m₁ *[n] m₃)).
    Proof. intros m₁ m₂ m₃ i j.
           unfold matrix_add, matrix_mul.
           apply bop_big_plus_distributes_over_left_row_i_dot_col_j; auto. 
    Qed.


    Lemma bop_big_plus_right_distributes_over_left_row_i_dot_col_j
          (plus_associative : bop_associative R eqR plusR)
          (plus_commutative  : bop_commutative R eqR plusR)
          (plusID : bop_is_id R eqR plusR 0)
          (right_distributive_mul_over_plus : A_bs_right_distributive eqR plusR mulR)
          (l : list nat) : 
      ∀ m₁ m₂ m₃ i j, 
         big_plus zeroR plusR (left_row_i_dot_col_j mulR (λ c d : nat, m₂ c d + m₃ c d) m₁ i j) l 
         =r=
         big_plus zeroR plusR (left_row_i_dot_col_j mulR m₂ m₁ i j) l + big_plus zeroR plusR (left_row_i_dot_col_j mulR m₃ m₁ i j) l.
    Proof. intros m₁ m₂ m₃ i j. unfold big_plus, left_row_i_dot_col_j.
           assert (A : fold_right plusR 0 (map (λ q : nat, (m₂ i q + m₃ i q) * m₁ q j) l)
                       =r=
                       fold_right plusR 0 (map (λ q : nat, (m₂ i q * m₁ q j) + (m₃ i q * m₁ q j)) l)).
               apply (fold_right_congruence _ _ eqR eqR plusR plusR).
               intros b b' a a' B C. apply congrP; auto. apply refR. 
               induction l.                
               compute; auto. 
               simpl. apply bop_and_intro. 
               apply right_distributive_mul_over_plus. 
               exact IHl.
               assert (B : fold_right plusR 0 (map (λ q : nat, (m₂ i q * m₁ q j) + (m₃ i q * m₁ q j)) l)
                           =r=
                           fold_right plusR 0 (map (λ q : nat, m₂ i q * m₁ q j) l) +
                           fold_right plusR 0 (map (λ q : nat, m₃ i q * m₁ q j) l)).
                  apply (big_plus_left_function_distribution _ _ refR symR trnR 0 plusR congrP
                           plus_associative                  
                           plus_commutative
                           plusID
                           (λ q : nat, m₂ i q * m₁ q j)
                           (λ q : nat, m₃ i q * m₁ q j)). 
         exact (trnR _ _ _ A B). 
    Qed. 
      
    Lemma matrix_mul_right_distributes_over_matrix_add
          (plus_associative : bop_associative R eqR plusR)
          (plus_commutative  : bop_commutative R eqR plusR)
          (plusID : bop_is_id R eqR plusR 0)
          (right_distributive_mul_over_plus : A_bs_right_distributive eqR plusR mulR)
          (n : nat): 
      ∀ m₁ m₂ m₃, ((m₂ +M m₃) *[n] m₁) =M= ((m₂ *[n] m₁) +M (m₃ *[n] m₁)).
    Proof. intros m₁ m₂ m₃ i j.
           unfold matrix_add, matrix_mul.
           apply bop_big_plus_right_distributes_over_left_row_i_dot_col_j; auto. 
    Qed. 

    (****************** mulitplicative idenitity matrix ***************************)

  Definition I := matrix_mul_identity 0 1.

 Lemma matrix_mul_identity_congruence : ~R I. 
 Proof. intros i j i' j' A B.
        unfold I. unfold matrix_mul_identity.
        case_eq(i =n?= j); intro C; case_eq(i' =n?= j'); intro D; compute; try (apply refR). 
        + apply brel_eq_nat_symmetric in A.
          rewrite (brel_eq_nat_transitive _ _ _ (brel_eq_nat_transitive _ _ _ A C) B) in D.
          congruence. 
        + apply brel_eq_nat_symmetric in B.
          rewrite (brel_eq_nat_transitive _ _ _ (brel_eq_nat_transitive _ _ _ A D) B) in C.    
          congruence.
 Qed.
 
 Local Open Scope nat_scope.

 (* We need to package up a matrix better so that we could have something like this: 

 Lemma matrix_mul_I_is_left_identity (n : nat) : ∀ m, I *[n] m =M= m.

*) 
 Lemma matrix_mul_I_is_left_identity :
          ∀ (n : nat), 0%nat < n  ->  ∀ (i : nat), i < n -> 
              ∀ m j, (I *[ n] m) i j =r= m i j. 
 Proof.  unfold I. unfold matrix_mul_identity.
         unfold matrix_mul. unfold left_matrix_mul.
         unfold left_row_i_dot_col_j.
         unfold big_plus.
        induction n.
        + intro A. apply PeanoNat.Nat.lt_irrefl in A. inversion A. 
        + intros A i B m j. simpl. 
          case_eq(i =n?= n); intro C. 
          ++ admit. (* OK? *)
          ++ admit. (* OK? *)
 Admitted. 


  Lemma matrix_mul_I_is_right_identity :
          ∀ (n : nat), 0%nat < n  ->  ∀ (j : nat), j < n -> 
                                                   ∀ m i, (m *[ n] I) i j =r= m i j.
 Proof.  unfold I. unfold matrix_mul_identity.
         unfold matrix_mul. unfold left_matrix_mul.
         unfold left_row_i_dot_col_j.
         unfold big_plus.
 Admitted. 
(*
  Lemma matrix_mul_I_is_identity (n : nat) : ∀ m, (I *[n] m =M= m) /\ (m *[n] I =M= m).
  Proof. intros m. split. 
         + apply matrix_mul_I_is_left_identity; auto.
         + apply matrix_mul_I_is_right_identity; auto.           
  Qed.
*) 
 

    
End Matrix_Multiplication.   

