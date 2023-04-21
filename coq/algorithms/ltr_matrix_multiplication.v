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
     coq.sg.and 
     coq.bs.properties
     coq.sg_ltr.properties     
     coq.algorithms.list_congruences
     coq.algorithms.big_plus
     coq.algorithms.matrix_definition
     coq.algorithms.matrix_algorithms
     coq.algorithms.matrix_addition. 
Import ListNotations.



Section Theory. 

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
    (*rtr   : rtr_type L R*)
    (congrP : bop_congruence R eqR plusR).    

  Local Infix "+" := plusR.
  Local Infix "|>" := ltr (at level 70).
(*  Local Infix "<|" := rtr (at level 70).  *) 
  Local Notation "0" := zeroR.
  Local Notation "1" := oneR.
  Local Notation "a =n= b" := (brel_eq_nat a b = true) (at level 70).
  Local Notation "a =r= b" := (eqR a b = true) (at level 70).
  Local Infix "=n?=" := brel_eq_nat (at level 70).
  Local Infix "=r?=" := eqR (at level 70).   
  Local Notation "a =M= b" := (eq_functional_matrix_prop R eqR a b) (at level 70).  
  Local Notation "a +M b" := (matrix_add plusR a b) (at level 70).

  Local Notation "a *[ n *] b" := (left_matrix_mul 0 plusR ltr n a b) (at level 60).
(*  Local Notation "a [* n ]* b" := (right_matrix_mul 0 plusR rtr n a b) (at level 50).  *) 


  (* move to big_plus? *)
  Lemma big_plus_left_distributive
    (LD : A_sg_ltr_distributive eqR plusR ltr)
    (mulANN : A_ltr_is_ann eqR ltr 0)
    (v : L) (f : nat -> R) (l : list nat) :
    v |> (big_plus zeroR plusR f l)
    =r=
    big_plus zeroR plusR (fun h => v |> (f h)) l.
  Proof. induction l.
         + compute. exact (mulANN v). 
         + unfold big_plus. simpl. 
           assert (A := congrP _ _ _ _ (refR (v |> f a)) IHl).
           assert (B := LD v (f a) (big_plus zeroR plusR f l)).            
           exact (trnR _ _ _ B A). 
  Qed.


  (* move to big_plus? 
  Lemma big_plus_right_distributive
        (RD : A_sg_ltr_distributive eqR plusR rtr)        
        (mulANN : A_rtr_is_ann eqR rtr 0)
        (v : L) (f : nat -> R) (l : list nat) : (big_plus zeroR plusR f l) <| v =r= big_plus zeroR plusR (fun h => (f h) <| v) l.
  Proof. induction l.
         + compute. exact ((mulANN v)). 
         + unfold big_plus. simpl. 
           assert (A := congrP _ _ _ _ (refR ((f a) <| v)) IHl).
           assert (B := RD v (f a) (big_plus zeroR plusR f l)).            
           exact (trnR _ _ _ B A). 
  Qed
*)   

  (* move to big_plus? *) 
  Lemma big_plus_left_function_distribution 
        (plus_associative : bop_associative R eqR plusR)
        (plus_commutative  : bop_commutative R eqR plusR)
        (plusID : bop_is_id R eqR plusR 0)
        (f g : nat -> R) :
    ∀ l, big_plus zeroR plusR (λ q, (f q) + (g q)) l
          =r=
          (big_plus zeroR plusR f l) + (big_plus zeroR plusR g l).
  Proof. induction l. 
         + compute. destruct (plusID 0) as [A B]. apply symR. exact A. 
         + unfold big_plus; simpl.
           fold (big_plus 0 plusR f l).
           fold (big_plus 0 plusR g l). 
           fold (big_plus 0 plusR (λ q : nat, f q + g q) l).
           assert (A : (f a + g a) + big_plus 0 plusR (λ q : nat, f q + g q) l
                       =r=
                       (f a + g a) + (big_plus 0 plusR f l + big_plus 0 plusR g l)).
              apply congrP.
              apply refR. 
              exact IHl. 
              assert (B : (f a + g a) + (big_plus 0 plusR f l + big_plus 0 plusR g l)
                          =r=
                          (f a + (g a + (big_plus 0 plusR f l + big_plus 0 plusR g l)))). 
                 apply plus_associative.
              assert (C : f a + (g a + (big_plus 0 plusR f l + big_plus 0 plusR g l))
                          =r=
                          f a + ((g a + big_plus 0 plusR f l) + big_plus 0 plusR g l)).
                 apply congrP; auto. 
              assert (D : f a + ((g a + big_plus 0 plusR f l) + big_plus 0 plusR g l)
                          =r=
                          f a + (((big_plus 0 plusR f l) + g a) + big_plus 0 plusR g l)).
                 apply congrP; auto.
              assert (E : f a + (((big_plus 0 plusR f l) + g a) + big_plus 0 plusR g l)
                          =r=
                          f a + (big_plus 0 plusR f l + (g a + big_plus 0 plusR g l))).
                 apply congrP; auto.
              assert (F : f a + (big_plus 0 plusR f l + (g a + big_plus 0 plusR g l))
                          =r=
                          (f a + big_plus 0 plusR f l) + (g a + big_plus 0 plusR g l)).
                 apply symR. apply plus_associative .                
             exact (trnR _ _ _ (trnR _ _ _ (trnR _ _ _ (trnR _ _ _ (trnR _ _ _ A B) C) D) E) F). 
Qed. 

  Lemma big_plus_distributes_over_left_row_i_dot_col_j
          (plus_associative : bop_associative R eqR plusR)
          (plus_commutative  : bop_commutative R eqR plusR)
          (plusID : bop_is_id R eqR plusR 0)
          (LD : A_sg_ltr_distributive eqR plusR ltr)
          (l : list nat) : 
      ∀ m₁ m₂ m₃ i j,
        big_plus zeroR plusR (left_row_i_dot_col_j ltr m₁ (λ c d : nat, m₂ c d + m₃ c d) i j) l 
        =r=
        big_plus zeroR plusR (left_row_i_dot_col_j ltr m₁ m₂ i j) l + big_plus zeroR plusR (left_row_i_dot_col_j ltr m₁ m₃ i j) l. 
    Proof. intros m₁ m₂ m₃ i j. unfold big_plus, left_row_i_dot_col_j. 
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
                  apply (big_plus_left_function_distribution
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
          (LD : A_sg_ltr_distributive eqR plusR ltr)          
          (n : nat) : 
      ∀ m₁ m₂ m₃, (m₁ *[ n *] (m₂ +M m₃)) =M= ((m₁ *[ n *] m₂) +M (m₁ *[ n *] m₃)).
    Proof. intros m₁ m₂ m₃ i j.
           unfold matrix_add, matrix_mul.
           apply big_plus_distributes_over_left_row_i_dot_col_j; auto.
    Qed.


(*    
    Lemma big_plus_distributes_over_right_row_i_dot_col_j
          (plus_associative : bop_associative R eqR plusR)
          (plus_commutative  : bop_commutative R eqR plusR)
          (plusID : bop_is_id R eqR plusR 0)
          (RD : srt_distributive eqR plusR rtr)
          (l : list nat) : 
      ∀ m₁ m₂ m₃ i j,
        big_plus 0 plusR (right_row_i_dot_col_j rtr (λ c d : nat, m₂ c d + m₃ c d) m₁ i j) l
        =r=
        big_plus 0 plusR (right_row_i_dot_col_j rtr m₂ m₁ i j) l
        +
        big_plus 0 plusR (right_row_i_dot_col_j rtr m₃ m₁ i j) l. 
    Proof. intros m₁ m₂ m₃ i j. unfold big_plus, right_row_i_dot_col_j.
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
                  apply (big_plus_left_function_distribution
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
           apply big_plus_distributes_over_right_row_i_dot_col_j; auto.
    Qed.
 *)

    
    (* useful for matrix multiplication (below) 
    Lemma big_plus_right_distributes_over_left_row_i_dot_col_j
          (plus_associative : bop_associative R eqR plusR)
          (plus_commutative  : bop_commutative R eqR plusR)
          (plusID : bop_is_id R eqR plusR 0)
          (RD : slt_distributive eqR plusR ltr)
          (l : list nat) : 
      ∀ m₁ m₂ m₃ i j, 
         big_plus zeroR plusR (left_row_i_dot_col_j ltr (λ c d : nat, m₂ c d + m₃ c d) m₁ i j) l 
         =r=
         big_plus zeroR plusR (left_row_i_dot_col_j ltr m₂ m₁ i j) l
         +
         big_plus zeroR plusR (left_row_i_dot_col_j ltr m₃ m₁ i j) l.
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
                  apply (big_plus_left_function_distribution
                           plus_associative                  
                           plus_commutative
                           plusID
                           (λ q : nat, m₂ i q * m₁ q j)
                           (λ q : nat, m₃ i q * m₁ q j)). 
         exact (trnR _ _ _ A B). 
    Qed. 

*) 
End Theory. 

