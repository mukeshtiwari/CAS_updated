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
     coq.tr.properties
     coq.sg.and 
     coq.bs.properties
     coq.st.properties     
     coq.algorithms.list_congruences
     coq.algorithms.matrix_definition
     coq.algorithms.matrix_algorithms
     coq.algorithms.matrix_addition. 
Import ListNotations.



Section Left_and_Right_Matrix_Multiplication.

  Variables
    (L R : Type)
    (eqL  : brel L)
    (eqR  : brel R)    
    (refR : brel_reflexive R eqR)
    (symR : brel_symmetric R eqR)
    (trnR : brel_transitive R eqR)
    (zeroR oneR : R) (* 0 and 1 *)
    (plusR : binary_op R)
    (ltr   : ltr_type L R)
    (rtr   : rtr_type L R)
    (congrP : bop_congruence R eqR plusR).    

  Local Infix "+" := plusR.
  Local Infix "|>" := ltr (at level 70).
  Local Infix "<|" := rtr (at level 70).  
  Local Notation "0" := zeroR.
  Local Notation "1" := oneR.
  Local Notation "a =n= b" := (brel_eq_nat a b = true) (at level 70).
  Local Notation "a =r= b" := (eqR a b = true) (at level 70).
  Local Infix "=n?=" := brel_eq_nat (at level 70).
  Local Infix "=r?=" := eqR (at level 70).   
  Local Notation "a =M= b" := (eq_functional_matrix_prop R eqR a b) (at level 70).  
  Local Notation "a +M b" := (matrix_add plusR a b) (at level 70).

  Local Notation "a *[ n *] b" := (left_matrix_mul 0 plusR ltr n a b) (at level 60).
  Local Notation "a [* n ]* b" := (right_matrix_mul 0 plusR rtr n a b) (at level 50).  


  Lemma sum_fn_left_distributive
        (LD : slt_distributive eqR plusR ltr) 
        (mulANN : ltr_is_ann L R eqR ltr 0)
          (v : L) (f : nat -> R) (l : list nat) : v |> (sum_fn zeroR plusR f l) =r= sum_fn zeroR plusR (fun h => v |> (f h)) l.
  Proof. induction l.
         + compute. exact (mulANN v). 
         + unfold sum_fn. simpl. 
           assert (A := congrP _ _ _ _ (refR (v |> f a)) IHl).
           assert (B := LD v (f a) (sum_fn zeroR plusR f l)).            
           exact (trnR _ _ _ B A). 
  Qed.

  Lemma sum_fn_right_distributive
        (RD : srt_distributive eqR plusR rtr)        
        (mulANN : rtr_is_ann L R eqR rtr 0)
        (v : L) (f : nat -> R) (l : list nat) : (sum_fn zeroR plusR f l) <| v =r= sum_fn zeroR plusR (fun h => (f h) <| v) l.
  Proof. induction l.
         + compute. exact ((mulANN v)). 
         + unfold sum_fn. simpl. 
           assert (A := congrP _ _ _ _ (refR ((f a) <| v)) IHl).
           assert (B := RD v (f a) (sum_fn zeroR plusR f l)).            
           exact (trnR _ _ _ B A). 
  Qed.


  Lemma sum_fn_left_function_distribution 
        (plus_associative : bop_associative R eqR plusR)
        (plus_commutative  : bop_commutative R eqR plusR)
        (plusID : bop_is_id R eqR plusR 0)
        (f g : nat -> R) :
    ∀ l, sum_fn zeroR plusR (λ q, (f q) + (g q)) l
          =r=
          (sum_fn zeroR plusR f l) + (sum_fn zeroR plusR g l).
  Proof. induction l. 
         + compute. destruct (plusID 0) as [A B]. apply symR. exact A. 
         + unfold sum_fn; simpl.
           fold (sum_fn 0 plusR f l).
           fold (sum_fn 0 plusR g l). 
           fold (sum_fn 0 plusR (λ q : nat, f q + g q) l).
           assert (A : (f a + g a) + sum_fn 0 plusR (λ q : nat, f q + g q) l
                       =r=
                       (f a + g a) + (sum_fn 0 plusR f l + sum_fn 0 plusR g l)).
              apply congrP.
              apply refR. 
              exact IHl. 
              assert (B : (f a + g a) + (sum_fn 0 plusR f l + sum_fn 0 plusR g l)
                          =r=
                          (f a + (g a + (sum_fn 0 plusR f l + sum_fn 0 plusR g l)))). 
                 apply plus_associative.
              assert (C : f a + (g a + (sum_fn 0 plusR f l + sum_fn 0 plusR g l))
                          =r=
                          f a + ((g a + sum_fn 0 plusR f l) + sum_fn 0 plusR g l)).
                 apply congrP; auto. 
              assert (D : f a + ((g a + sum_fn 0 plusR f l) + sum_fn 0 plusR g l)
                          =r=
                          f a + (((sum_fn 0 plusR f l) + g a) + sum_fn 0 plusR g l)).
                 apply congrP; auto.
              assert (E : f a + (((sum_fn 0 plusR f l) + g a) + sum_fn 0 plusR g l)
                          =r=
                          f a + (sum_fn 0 plusR f l + (g a + sum_fn 0 plusR g l))).
                 apply congrP; auto.
              assert (F : f a + (sum_fn 0 plusR f l + (g a + sum_fn 0 plusR g l))
                          =r=
                          (f a + sum_fn 0 plusR f l) + (g a + sum_fn 0 plusR g l)).
                 apply symR. apply plus_associative .                
             exact (trnR _ _ _ (trnR _ _ _ (trnR _ _ _ (trnR _ _ _ (trnR _ _ _ A B) C) D) E) F). 
Qed. 

  Lemma sum_fn_distributes_over_left_row_i_dot_col_j
          (plus_associative : bop_associative R eqR plusR)
          (plus_commutative  : bop_commutative R eqR plusR)
          (plusID : bop_is_id R eqR plusR 0)
          (LD : slt_distributive eqR plusR ltr)
          (l : list nat) : 
      ∀ m₁ m₂ m₃ i j,
        sum_fn zeroR plusR (left_row_i_dot_col_j ltr m₁ (λ c d : nat, m₂ c d + m₃ c d) i j) l 
        =r=
        sum_fn zeroR plusR (left_row_i_dot_col_j ltr m₁ m₂ i j) l + sum_fn zeroR plusR (left_row_i_dot_col_j ltr m₁ m₃ i j) l. 
    Proof. intros m₁ m₂ m₃ i j. unfold sum_fn, left_row_i_dot_col_j. 
           assert (A : fold_right plusR 0 (map (λ q : nat, (m₁ i q ) |> (m₂ q j + m₃ q j)) l)
                       =r=
                       fold_right plusR 0 (map (λ q : nat, (m₁ i q |> m₂ q j) + (m₁ i q |> m₃ q j)) l)).
               apply (fold_right_congruence _ _ eqR eqR plusR plusR).
               intros b b' a a' B C. apply congrP; auto. apply refR. 
               induction l.                
               compute; auto. 
               simpl. apply bop_and_intro. 
               apply LD. 
               exact IHl.
               assert (B : fold_right plusR 0 (map (λ q : nat, (m₁ i q |> m₂ q j) + (m₁ i q |> m₃ q j)) l)
                           =r=
                           fold_right plusR 0 (map (λ q : nat, m₁ i q |> m₂ q j) l) +
                           fold_right plusR 0 (map (λ q : nat, m₁ i q |> m₃ q j) l)).
                  apply (sum_fn_left_function_distribution
                           plus_associative                  
                           plus_commutative
                           plusID
                           (λ q : nat, m₁ i q |> m₂ q j)
                           (λ q : nat, m₁ i q |> m₃ q j)). 
         exact (trnR _ _ _ A B). 
    Qed. 
                 
    Lemma left_matrix_left_mul_left_distributive_over_matrix_add
          (plus_associative : bop_associative R eqR plusR)
          (plus_commutative  : bop_commutative R eqR plusR)
          (plusID : bop_is_id R eqR plusR 0)
          (LD : slt_distributive eqR plusR ltr)          
          (n : nat) : 
      ∀ m₁ m₂ m₃, (m₁ *[ n *] (m₂ +M m₃)) =M= ((m₁ *[ n *] m₂) +M (m₁ *[ n *] m₃)).
    Proof. intros m₁ m₂ m₃ i j.
           unfold matrix_add, matrix_mul.
           apply sum_fn_distributes_over_left_row_i_dot_col_j; auto.
    Qed.

    Lemma sum_fn_distributes_over_right_row_i_dot_col_j
          (plus_associative : bop_associative R eqR plusR)
          (plus_commutative  : bop_commutative R eqR plusR)
          (plusID : bop_is_id R eqR plusR 0)
          (RD : srt_distributive eqR plusR rtr)
          (l : list nat) : 
      ∀ m₁ m₂ m₃ i j,
        sum_fn 0 plusR (right_row_i_dot_col_j rtr (λ c d : nat, m₂ c d + m₃ c d) m₁ i j) l
        =r=
        sum_fn 0 plusR (right_row_i_dot_col_j rtr m₂ m₁ i j) l
        +
        sum_fn 0 plusR (right_row_i_dot_col_j rtr m₃ m₁ i j) l. 
    Proof. intros m₁ m₂ m₃ i j. unfold sum_fn, right_row_i_dot_col_j.
           assert (A : fold_right plusR 0 (map (λ q : nat, (m₂ i q + m₃ i q) <| m₁ q j) l)
                       =r=
                       fold_right plusR 0 (map (λ q : nat, (m₂ i q <| m₁ q j) + (m₃ i q <| m₁ q j)) l)).
               apply (fold_right_congruence _ _ eqR eqR plusR plusR).
               intros b b' a a' B C. apply congrP; auto. apply refR. 
               induction l.                
               compute; auto. 
               simpl. apply bop_and_intro. 
               apply RD. 
               exact IHl.
           assert (B : fold_right plusR 0 (map (λ q : nat, (m₂ i q <| m₁ q j) + (m₃ i q <| m₁ q j)) l)
                       =r=
                       fold_right plusR 0 (map (λ q : nat, m₂ i q <| m₁ q j) l) +
                       fold_right plusR 0 (map (λ q : nat, m₃ i q <| m₁ q j) l)).
                  apply (sum_fn_left_function_distribution
                           plus_associative                  
                           plus_commutative
                           plusID
                           (λ q : nat, m₂ i q <| m₁ q j)
                           (λ q : nat, m₃ i q <| m₁ q j)). 
           exact (trnR _ _ _ A B). 
    Qed. 

    Lemma right_matrix_mul_right_distributes_over_matrix_add
          (plus_associative : bop_associative R eqR plusR)
          (plus_commutative  : bop_commutative R eqR plusR)
          (plusID : bop_is_id R eqR plusR 0)
          (RD : srt_distributive eqR plusR rtr)
          (n : nat): 
      ∀ m₁ m₂ m₃, ((m₂ +M m₃) [* n ]* m₁) =M= ((m₂ [* n ]* m₁) +M (m₃ [* n ]* m₁)).
    Proof. intros m₁ m₂ m₃ i j.
           unfold matrix_add, right_matrix_mul.
           apply sum_fn_distributes_over_right_row_i_dot_col_j; auto.
    Qed.

    (* useful for matrix multiplication (below) 
    Lemma sum_fn_right_distributes_over_left_row_i_dot_col_j
          (plus_associative : bop_associative R eqR plusR)
          (plus_commutative  : bop_commutative R eqR plusR)
          (plusID : bop_is_id R eqR plusR 0)
          (RD : slt_distributive eqR plusR ltr)
          (l : list nat) : 
      ∀ m₁ m₂ m₃ i j, 
         sum_fn zeroR plusR (left_row_i_dot_col_j ltr (λ c d : nat, m₂ c d + m₃ c d) m₁ i j) l 
         =r=
         sum_fn zeroR plusR (left_row_i_dot_col_j ltr m₂ m₁ i j) l
         +
         sum_fn zeroR plusR (left_row_i_dot_col_j ltr m₃ m₁ i j) l.
    Proof. intros m₁ m₂ m₃ i j. unfold sum_fn, left_row_i_dot_col_j.
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
                  apply (sum_fn_left_function_distribution
                           plus_associative                  
                           plus_commutative
                           plusID
                           (λ q : nat, m₂ i q * m₁ q j)
                           (λ q : nat, m₃ i q * m₁ q j)). 
         exact (trnR _ _ _ A B). 
    Qed. 

*) 
End Left_and_Right_Matrix_Multiplication.   

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
         slt_distributive eqR plusR mulR. 
  Proof. apply LD. Qed.

  Lemma bop_right_distribitive_implies_srt_distributive
      (LD: A_bs_right_distributive eqR plusR mulR) :
         srt_distributive eqR plusR mulR. 
  Proof. apply LD. Qed.

  Lemma bop_is_ann_implies_ltr_is_ann (s : R) 
    (ann : bop_is_ann R eqR mulR s) : ltr_is_ann R R eqR mulR s.
  Proof. intro l. apply (ann l). Qed. 

  Lemma bop_is_ann_implies_rtr_is_ann (s : R) 
    (ann : bop_is_ann R eqR mulR s) : rtr_is_ann R R eqR mulR s.
  Proof. intro l. apply (ann l). Qed. 

  Lemma bop_sum_fn_left_distributive
        (LD: A_bs_left_distributive eqR plusR mulR) 
        (mulANN : bop_is_ann R eqR mulR 0)
          (v : R) (f : nat -> R) (l : list nat) : v * (sum_fn zeroR plusR f l) =r= sum_fn zeroR plusR (fun h => v* (f h)) l.
  Proof. assert (A := bop_left_distribitive_implies_slt_distributive LD).
         assert (B := bop_is_ann_implies_ltr_is_ann 0 mulANN). 
         apply sum_fn_left_distributive; auto. 
  Qed.

  Lemma bop_sum_fn_right_distributive
        (mulANN : bop_is_ann R eqR mulR 0)
        (RD : A_bs_right_distributive eqR plusR mulR)
        (v : R) (f : nat -> R) (l : list nat) : (sum_fn zeroR plusR f l) * v =r= sum_fn zeroR plusR (fun h => (f h) * v) l.
  Proof. assert (A := bop_right_distribitive_implies_srt_distributive RD).
         assert (B := bop_is_ann_implies_rtr_is_ann 0 mulANN). 
         apply sum_fn_right_distributive; auto. 
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
    ∀ l, sum_fn zeroR plusR (λ q1, sum_fn zeroR plusR (λ q2, f q1 q2) l) l
          =r=
          sum_fn zeroR plusR (λ q2, sum_fn zeroR plusR (λ q1, f q1 q2) l) l.
  Proof. induction l.
         + compute. apply refR. 
         + unfold sum_fn. simpl.
           fold (sum_fn 0 plusR (λ q2 : nat, f a q2) l).
           fold (sum_fn 0 plusR (λ q1 : nat, f q1 a) l).
           fold (sum_fn 0 plusR (λ q1 : nat, f q1 a + fold_right plusR 0 (map (λ q2 : nat, f q1 q2) l)) l).
           fold (sum_fn 0 plusR (λ q2 : nat, f a q2 + fold_right plusR 0 (map (λ q1 : nat, f q1 q2) l)) l). 
           (* show 
               f a a + 
               sum_fn 0 plusR (λ q2 : nat, f a q2) l +
               sum_fn 0 plusR (λ q1 : nat, f q1 a + fold_right plusR 0 (map (λ q2 : nat, f q1 q2) l)) l 
               =r=
               f a a + 
               sum_fn 0 plusR (λ q1 : nat, f q1 a) l +
               sum_fn 0 plusR (λ q2 : nat, f a q2 + fold_right plusR 0 (map (λ q1 : nat, f q1 q2) l)) l
            *)
           assert (A := sum_fn_left_function_distribution _ _ refR symR trnR 0 plusR congrP plus_associative plus_commutative plusID
                           (λ q1, f q1 a) (λ q1, fold_right plusR 0 (map (λ q2 : nat, f q1 q2) l)) l).
           simpl in A. 
           assert (B := sum_fn_left_function_distribution _ _ refR symR trnR 0 plusR congrP plus_associative plus_commutative plusID
                           (λ q2, f a q2) (λ q2, fold_right plusR 0 (map (λ q1 : nat, f q1 q2) l)) l).
           simpl in B. 
           assert (C : f a a +
                       sum_fn 0 plusR (λ q2 : nat, f a q2) l +
                       sum_fn 0 plusR (λ q1 : nat, f q1 a + fold_right plusR 0 (map (λ q2 : nat, f q1 q2) l)) l
                       =r=
                       f a a +
                       sum_fn 0 plusR (λ q2 : nat, f a q2) l +
                       (sum_fn 0 plusR (λ q1 : nat, f q1 a) l +
                        sum_fn 0 plusR (λ q1 : nat, fold_right plusR 0 (map (λ q2 : nat, f q1 q2) l)) l)).
              apply congrP. apply refR. exact A. 
           assert (D : f a a +
                       sum_fn 0 plusR (λ q2 : nat, f a q2) l +
                       (sum_fn 0 plusR (λ q1 : nat, f q1 a) l +
                        sum_fn 0 plusR (λ q1 : nat, fold_right plusR 0 (map (λ q2 : nat, f q1 q2) l)) l)
                       =r=
                       f a a +
                       sum_fn 0 plusR (λ q1 : nat, f q1 a) l +
                       (sum_fn 0 plusR (λ q2 : nat, f a q2) l +
                        sum_fn 0 plusR (λ q : nat, fold_right plusR 0 (map (λ q2 : nat, f q q2) l)) l)).
              apply rewrite_lemma; auto. 
           assert (E : f a a +
                       sum_fn 0 plusR (λ q1 : nat, f q1 a) l +
                       (sum_fn 0 plusR (λ q2 : nat, f a q2) l +
                        sum_fn 0 plusR (λ q : nat, fold_right plusR 0 (map (λ q2 : nat, f q q2) l)) l)
                       =r=
                       f a a +
                       sum_fn 0 plusR (λ q1 : nat, f q1 a) l +
                       sum_fn 0 plusR (λ q2 : nat, f a q2 + fold_right plusR 0 (map (λ q1 : nat, f q1 q2) l)) l).
              apply congrP; auto.
              apply symR.
              assert (F :   sum_fn 0 plusR (λ q2 : nat, f a q2) l +
                            sum_fn 0 plusR (λ q : nat, fold_right plusR 0 (map (λ q2 : nat, f q q2) l)) l
                            =r= 
                            sum_fn 0 plusR (λ q2 : nat, f a q2) l +
                            sum_fn 0 plusR (λ q2 : nat, fold_right plusR 0 (map (λ q1 : nat, f q1 q2) l)) l).
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
           assert (A : sum_fn 0 plusR
                              (λ q : nat, m₁ i q * sum_fn 0 plusR
                                                   (λ q0 : nat, m₂ q q0 * m₃ q0 j)
                                                   (list_enum n))
                              (list_enum n)
                       =r=
                       sum_fn 0 plusR
                              (λ q : nat, sum_fn 0 plusR
                                                 (λ q0 : nat, m₁ i q * (m₂ q q0 * m₃ q0 j))
                                                 (list_enum n))
                              (list_enum n)).
              apply sum_fn_congruence_v2; auto. 
              intros i0 j0 A. 
              apply sum_fn_congruence; auto. 
              intros i1 j1 B.
              apply congrM.
              exact (cong1 _ _ _ _ (brel_eq_nat_reflexive i) A). 
              apply congrM.
              exact (cong2 _ _ _ _ A B). 
              exact (cong3 _ _ _ _ B (brel_eq_nat_reflexive j)). 
              intros i0.
              apply sum_fn_left_distributive; auto.
              apply bop_is_ann_implies_ltr_is_ann; auto. 

           assert (B : sum_fn 0 plusR
                              (λ q : nat, sum_fn 0 plusR
                                                 (λ q0 : nat, m₁ i q * (m₂ q q0 * m₃ q0 j))
                                                 (list_enum n))
                              (list_enum n)
                       =r=
                       sum_fn 0 plusR
                              (λ q : nat, sum_fn 0 plusR
                                                 (λ q0 : nat, (m₁ i q * m₂ q q0) * m₃ q0 j)
                                                 (list_enum n))
                              (list_enum n)).
              apply sum_fn_congruence_v2; auto. 
              intros i1 j0 B. 
              apply sum_fn_congruence; auto. 
              intros i2 j1 C.
              apply congrM.
              apply congrM.              
              exact (cong1 _ _ _ _ (brel_eq_nat_reflexive i) B).               
              exact (cong2 _ _ _ _ B C).               
              exact (cong3 _ _ _ _ C (brel_eq_nat_reflexive j)).               
              intros i1.
              apply sum_fn_congruence_v2; auto.
              intros i2 j0 D.
              apply congrM. 
              apply congrM.
              exact (cong1 _ _ _ _ (brel_eq_nat_reflexive i) (brel_eq_nat_reflexive i1)).                             
              exact (cong2 _ _ _ _ (brel_eq_nat_reflexive i1) D).                             
              exact (cong3 _ _ _ _ D (brel_eq_nat_reflexive j)).                             

           assert (C : sum_fn 0 plusR
                              (λ q : nat, sum_fn 0 plusR
                                                 (λ q0 : nat, (m₁ i q * m₂ q q0) * m₃ q0 j)
                                                 (list_enum n))
                              (list_enum n)
                       =r=
                       sum_fn 0 plusR
                              (λ q0 : nat, sum_fn 0 plusR
                                                 (λ q : nat, (m₁ i q * m₂ q q0) * m₃ q0 j)
                                                 (list_enum n))
                              (list_enum n)).
              apply switch; auto. 

           assert (D : sum_fn 0 plusR
                              (λ q0 : nat, sum_fn 0 plusR
                                                 (λ q : nat, (m₁ i q * m₂ q q0) * m₃ q0 j)
                                                 (list_enum n))
                              (list_enum n)
                       =r=
                       sum_fn 0 plusR
                              (λ q0 : nat, (sum_fn 0 plusR
                                                 (λ q : nat, m₁ i q * m₂ q q0) 
                                                 (list_enum n)) * m₃ q0 j)
                              (list_enum n)).
              apply sum_fn_congruence_v2; auto. 
              intros i0 j0 E. 
              apply congrM.
              apply sum_fn_congruence; auto. 
              intros i1 j1 F.
              apply congrM.
              exact (cong1 _ _ _ _ (brel_eq_nat_reflexive i) F).
              exact (cong2 _ _ _ _ F E).
              exact (cong3 _ _ _ _ E (brel_eq_nat_reflexive j)).                                                                                             
              intros i0.
              apply symR. 
              apply sum_fn_right_distributive; auto.
              apply bop_is_ann_implies_rtr_is_ann; auto.               
              exact (trnR _ _ _ (trnR _ _ _ (trnR _ _ _ A B) C) D). 
Qed. 


    Lemma bop_sum_fn_distributes_over_left_row_i_dot_col_j
          (plus_associative : bop_associative R eqR plusR)
          (plus_commutative  : bop_commutative R eqR plusR)
          (plusID : bop_is_id R eqR plusR 0)
          (LD : A_bs_left_distributive eqR plusR mulR)
          (l : list nat) : 
      ∀ m₁ m₂ m₃ i j,
        sum_fn zeroR plusR (left_row_i_dot_col_j mulR m₁ (λ c d : nat, m₂ c d + m₃ c d) i j) l 
        =r=
        sum_fn zeroR plusR (left_row_i_dot_col_j mulR m₁ m₂ i j) l + sum_fn zeroR plusR (left_row_i_dot_col_j mulR m₁ m₃ i j) l.
    Proof. assert (A := bop_left_distribitive_implies_slt_distributive LD).
           apply sum_fn_distributes_over_left_row_i_dot_col_j; auto. 
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
           apply bop_sum_fn_distributes_over_left_row_i_dot_col_j; auto. 
    Qed.


    Lemma bop_sum_fn_right_distributes_over_left_row_i_dot_col_j
          (plus_associative : bop_associative R eqR plusR)
          (plus_commutative  : bop_commutative R eqR plusR)
          (plusID : bop_is_id R eqR plusR 0)
          (right_distributive_mul_over_plus : A_bs_right_distributive eqR plusR mulR)
          (l : list nat) : 
      ∀ m₁ m₂ m₃ i j, 
         sum_fn zeroR plusR (left_row_i_dot_col_j mulR (λ c d : nat, m₂ c d + m₃ c d) m₁ i j) l 
         =r=
         sum_fn zeroR plusR (left_row_i_dot_col_j mulR m₂ m₁ i j) l + sum_fn zeroR plusR (left_row_i_dot_col_j mulR m₃ m₁ i j) l.
    Proof. intros m₁ m₂ m₃ i j. unfold sum_fn, left_row_i_dot_col_j.
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
                  apply (sum_fn_left_function_distribution _ _ refR symR trnR 0 plusR congrP
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
           apply bop_sum_fn_right_distributes_over_left_row_i_dot_col_j; auto. 
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
         unfold sum_fn.
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
         unfold sum_fn.
 Admitted. 
(*
  Lemma matrix_mul_I_is_identity (n : nat) : ∀ m, (I *[n] m =M= m) /\ (m *[n] I =M= m).
  Proof. intros m. split. 
         + apply matrix_mul_I_is_left_identity; auto.
         + apply matrix_mul_I_is_right_identity; auto.           
  Qed.
*) 
 

    
End Matrix_Multiplication.   

