From Coq Require Import
     List.
Import ListNotations.
From CAS Require Import
  coq.common.compute
  coq.theory.set
  coq.eqv.properties
  coq.eqv.list
  coq.eqv.set
  coq.eqv.nat
  coq.eqv.product   
  coq.sg.properties
  coq.tr.properties
  coq.st.properties    
  coq.sg.and
  coq.sg.union  
  coq.algorithms.list_congruences
  coq.algorithms.big_plus
  coq.algorithms.matrix_definition
  coq.algorithms.matrix_algorithms
  coq.algorithms.matrix_addition  
  coq.algorithms.matrix_multiplication. 


Section Computation.

  Fixpoint left_sum_of_matrix_powers_general
           {L S : Type} 
           (n : nat)
           (zeroS oneS : S)
           (plusS : binary_op S)
           (ltr : ltr_type L S) 
           (m : functional_matrix L)
           (k : nat) : functional_matrix S :=
    match k with
    | O => matrix_mul_identity zeroS oneS  
    | S k' => matrix_add plusS
                         (left_sum_of_matrix_powers_general n zeroS oneS plusS ltr m k')
                         (left_matrix_exponentiation zeroS oneS plusS ltr n m k)
    end.

  Definition left_sum_of_matrix_powers
             (S : Type)
             (n : nat)
             (zeroS oneS : S)
             (plusS mulS : binary_op S)
             (m : functional_matrix S)
             (k : nat) : functional_matrix S :=
    left_sum_of_matrix_powers_general n zeroS oneS plusS mulS m k.


End Computation.   


Section Weighted_Paths.

  Local Open Scope nat_scope. 
  
Variables 
    (L R : Type)
    (zero one : R) (* 0 and 1 *)
    (plus : binary_op R)
    (ltr : ltr_type L R)    
    (eqL  : brel L)
    (eqR  : brel R)    
    (conR : brel_congruence R eqR eqR)            
    (refR :  brel_reflexive R eqR)
    (symR : brel_symmetric R eqR)
    (trnR : brel_transitive R eqR)
    (conL : brel_congruence L eqL eqL)            
    (refL :  brel_reflexive L eqL)
    (symL : brel_symmetric L eqL)
    (trnL : brel_transitive L eqL)
    (congrP : bop_congruence R eqR plus)
    (ltr_cong : ltr_congruence L R eqL eqR ltr)     
    .
      
  Definition is_eqR a b       := eqR a b = true.
  Definition is_eqL a b       := eqL a b = true.    
  Definition is_eq_nat a b    := brel_eq_nat a b = true.
  Definition not_eq_nat a b   := brel_eq_nat a b = false.      
  Local Notation "0" := zero.
  Local Notation "1" := one.
  Local Infix "+" := plus.
  Local Infix "|>" := ltr (at level 70).
  Local Infix "=l=" := is_eqL (at level 70).
  Local Infix "=r?=" := eqR (at level 70).
  Local Infix "=r=" := is_eqR (at level 70).
  Local Infix "=n=" := is_eq_nat (at level 70).
  Local Infix "<n>" := not_eq_nat (at level 70).    
  Local Infix "=l?=" := eqL (at level 70).  
  Local Infix "=n?=" := brel_eq_nat (at level 70).

  Definition value_list : Type        := list R.

  Definition label_list : Type        := list L.  

  Definition weighted_arc : Type      := nat * nat * L. 

  Definition weighted_path : Type     := list weighted_arc.

  Definition weighted_path_set : Type := finite_set weighted_path.

  Local Definition CongR := functional_matrix_congruence R eqR.
  Local Definition CongL := functional_matrix_congruence L eqL.  

  Local Infix "=M=" := (eq_functional_matrix_prop R eqR) (at level 70).
  Local Infix "=L=" := (eq_functional_matrix_prop L eqL) (at level 70).  

  Local Infix "+M" := (matrix_add plus ) (at level 70).
  
  Local Notation "a *[ n ]>  b" := (left_matrix_mul zero plus ltr n a b) (at level 70).


  
  (********************** value_list equality ***********************)

  Definition eq_value_list : brel value_list := brel_list eqR. 

  Lemma eq_value_list_congurence : brel_congruence _ eq_value_list eq_value_list.
  Proof. apply brel_list_congruence; auto. Qed.

  Lemma eq_value_list_reflexive : brel_reflexive _ eq_value_list.
  Proof. apply brel_list_reflexive; auto. Qed.

  Lemma eq_value_list_symmetric : brel_symmetric _ eq_value_list.
  Proof. apply brel_list_symmetric; auto. Qed.
  
  Lemma eq_value_list_transitive : brel_transitive _ eq_value_list.
  Proof. apply brel_list_transitive; auto.  Qed.

  Definition eq_value_list_is_true l1 l2 := eq_value_list l1 l2 = true.  
  Local Infix "=vl=" :=  eq_value_list_is_true (at level 70).

  Definition eq_value_list_intro :
    ∀ (v v' : R) (l l' : value_list), v =r= v' -> l =vl= l' -> (v :: l) =vl= (v' :: l').
  Proof. intros v v' l l' A B. apply brel_list_cons_intro; auto. Qed. 
         
  
  Definition eq_value_list_elim :
    ∀ (v v' : R) (l l' : value_list), (v :: l) =vl= (v' :: l') -> (v =r= v') ∧ (l =vl= l').
  Proof. intros v v' l l' A. apply brel_list_cons_elim in A. destruct A as [A B]. auto. Qed. 
  
  (********************** label_list equality ***********************)

  Definition eq_label_list : brel label_list := brel_list eqL. 

  Lemma eq_label_list_congurence : brel_congruence _ eq_label_list eq_label_list.
  Proof. apply brel_list_congruence; auto. Qed.

  Lemma eq_label_list_reflexive : brel_reflexive _ eq_label_list.
  Proof. apply brel_list_reflexive; auto. Qed.

  Lemma eq_label_list_symmetric : brel_symmetric _ eq_label_list.
  Proof. apply brel_list_symmetric; auto. Qed.
  
  Lemma eq_label_list_transitive : brel_transitive _ eq_label_list.
  Proof. apply brel_list_transitive; auto.  Qed.

  Definition eq_label_list_is_true l1 l2 := eq_label_list l1 l2 = true.  
  Local Infix "=ll=" :=  eq_label_list_is_true (at level 70).

  Definition eq_label_list_intro :
    ∀ (l l' : L) (ls ls' : label_list), l =l= l' -> ls =ll= ls' -> (l :: ls) =ll= (l' :: ls').
  Proof. intros l l' ls ls' A B. apply brel_list_cons_intro; auto. Qed. 
         
  Definition eq_label_list_elim :
    ∀ (l l' : L) (ls ls' : label_list), (l :: ls) =ll= (l' :: ls') -> (l =l= l') ∧ (ls =ll= ls').
  Proof. intros l l' ls ls' A. apply brel_list_cons_elim in A. destruct A as [A B]. auto. Qed. 
  
  
  (********************** weighted arc equality ***********************)

  Definition eq_weighted_arc : brel weighted_arc :=
        brel_product (brel_product brel_eq_nat brel_eq_nat) eqL. 

  Lemma eq_weighted_arc_congruence : brel_congruence weighted_arc eq_weighted_arc eq_weighted_arc.
  Proof. apply brel_product_congruence; auto.
         apply brel_product_congruence; auto.
         apply brel_eq_nat_congruence.
         apply brel_eq_nat_congruence.          
  Qed.          
    
  Lemma eq_weighted_arc_reflexive : brel_reflexive weighted_arc eq_weighted_arc.
  Proof. apply brel_product_reflexive; auto. 
         apply brel_product_reflexive; auto.
         apply brel_eq_nat_reflexive.
         apply brel_eq_nat_reflexive.                  
  Qed.          

  Lemma eq_weighted_arc_symmetric : brel_symmetric weighted_arc eq_weighted_arc. 
  Proof. apply brel_product_symmetric; auto. 
         apply brel_product_symmetric; auto.
         apply brel_eq_nat_symmetric.
         apply brel_eq_nat_symmetric.                  
  Qed. 

  Lemma eq_weighted_arc_transitive : brel_transitive weighted_arc eq_weighted_arc.
  Proof. apply brel_product_transitive; auto.
         apply brel_product_transitive; auto.
         apply brel_eq_nat_transitive.
         apply brel_eq_nat_transitive.                  
  Qed. 

  Definition eq_weighted_arc_is_true a1 a2 := eq_weighted_arc a1 a2 = true.  
  Local Infix "=a=" :=  eq_weighted_arc_is_true (at level 70).

  Lemma eq_weighted_arc_intro :
    ∀ (a b c d : nat) (s t : L), a =n= b -> c=n=d -> s =l= t -> ((a, c), s) =a= ((b, d), t).
  Proof. intros a b c d s t A B C.
         apply brel_product_intro; auto. 
         apply brel_product_intro; auto. 
  Qed.
  
  Lemma eq_weighted_arc_elim :
    ∀ (a b c d : nat) (s t : L), ((a, c), s) =a= ((b, d), t) -> a =n= b ∧ c=n=d ∧ s =l= t.
  Proof. intros a b c d s t A.
         apply brel_product_elim in A. destruct A as [A B]. 
         apply brel_product_elim in A. destruct A as [A C].
         auto. 
  Qed.
  
(********************** weighted path equality ***********************)     
  
  Definition eq_weighted_path : brel weighted_path := brel_list eq_weighted_arc. 

   Lemma eq_weighted_path_congruence : brel_congruence _ eq_weighted_path eq_weighted_path.
   Proof. apply brel_list_congruence.
          exact eq_weighted_arc_symmetric.
          exact eq_weighted_arc_transitive.
          exact eq_weighted_arc_congruence.
   Qed.     

  Lemma eq_weighted_path_reflexive : brel_reflexive weighted_path eq_weighted_path. 
   Proof. apply brel_list_reflexive. exact eq_weighted_arc_reflexive. Qed.

  Lemma eq_weighted_path_symmetric : brel_symmetric weighted_path eq_weighted_path. 
   Proof. apply brel_list_symmetric. exact eq_weighted_arc_symmetric. Qed.
  
  Lemma eq_weighted_path_transitive : brel_transitive weighted_path eq_weighted_path. 
   Proof. apply brel_list_transitive. exact eq_weighted_arc_transitive. Qed.

  Definition eq_weighted_path_is_true p1 p2     := eq_weighted_path p1 p2 = true.  
  Local Infix "=p=" := eq_weighted_path_is_true (at level 70).

  Definition eq_weighted_path_intro :
    ∀ (a1 a2 : weighted_arc) (p q : weighted_path), a1 =a= a2 -> p =p= q -> (a1 :: p) =p= (a2 :: q).
  Proof. intros a1 a2 p q A B. apply brel_list_cons_intro. exact A. exact B. Qed. 

  Definition eq_weighted_path_elim :
    ∀ (a1 a2 : weighted_arc) (p q : weighted_path), (a1 :: p) =p= (a2 :: q) -> a1 =a= a2 ∧ p =p= q.
  Proof. intros a1 a2 p q A.
         apply brel_list_cons_elim in A.
         destruct A as [A B].
         split; auto. 
  Qed. 

(********************** weighted path set equality ***********************)     
  
  Definition eq_weighted_path_set : brel weighted_path_set := brel_set eq_weighted_path. 

   Lemma eq_weighted_path_set_congruence : brel_congruence _ eq_weighted_path_set eq_weighted_path_set.
   Proof. apply brel_set_congruence.
          exact eq_weighted_path_reflexive.
          exact eq_weighted_path_symmetric.
          exact eq_weighted_path_transitive.
   Qed.     

  Lemma eq_weighted_path_set_reflexive : brel_reflexive weighted_path_set eq_weighted_path_set. 
  Proof. apply brel_set_reflexive.
         exact eq_weighted_path_reflexive.
         exact eq_weighted_path_symmetric.
  Qed.

  Lemma eq_weighted_path_set_symmetric : brel_symmetric weighted_path_set eq_weighted_path_set. 
  Proof. apply brel_set_symmetric. Qed.
  
  Lemma eq_weighted_path_set_transitive : brel_transitive weighted_path_set eq_weighted_path_set. 
  Proof. apply brel_set_transitive.
         exact eq_weighted_path_reflexive.
         exact eq_weighted_path_symmetric.
         exact eq_weighted_path_transitive.
  Qed.

  Local Definition CongP := functional_matrix_congruence _ eq_weighted_path_set.

  Definition in_path_set p X       := in_set eq_weighted_path X p = true.
  Definition test_in_path_set p X  := in_set eq_weighted_path X p.
  
  Local Infix "[in set]"   := in_path_set (at level 70).
  Local Infix "[?in set?]" := test_in_path_set (at level 70).    
  
  (****************** Source and target of a weighted path ********************)

  Definition arc_source (a : weighted_arc) : nat := 
    match a with 
    | (s, _, _) => s 
    end.

  Definition arc_target (a : weighted_arc) : nat := 
    match a with 
    | (_, t, _) => t
    end.

  Lemma arc_target_congruence : 
      ∀ a a', a =a= a' -> arc_target a =n= arc_target a'.
  Proof. intros [[b c] v] [[b' c'] v']  A. 
         apply eq_weighted_arc_elim in A.
         compute. destruct A as [_ [A _]]. exact A. 
  Qed. 
  
  Definition test_path_source (c : nat) (l : weighted_path) : bool :=
    match l with 
    | [] => false
    | a :: _ => c =n?= (arc_source a)
    end.

  
  Definition refN := brel_eq_nat_reflexive.  
  Definition symN := brel_eq_nat_symmetric.  
  Definition trnN := brel_eq_nat_transitive.

  Lemma test_path_source_congruence : 
    ∀ n n' p p', n =n= n' -> p =p= p' -> test_path_source n p = test_path_source n' p'.
  Proof. intros n n' p p' A B. 
         destruct p; destruct p'. 
         + compute. reflexivity. 
         + compute in B. congruence.
         + compute in B. congruence.
         + apply eq_weighted_path_elim in B. destruct B as [B C].
           destruct w as [[a b] v]; destruct w0 as [[a' b'] v']. simpl. 
           apply eq_weighted_arc_elim in B. destruct B as [B [D E]].
           case_eq(n =n?= a); intro F; case_eq(n' =n?= a'); intro G; auto.
           ++ rewrite (trnN _ _ _ (symN _ _ A) (trnN _ _ _ F B)) in G. congruence. 
           ++ rewrite (trnN _ _ _ (trnN _ _ _ A G) (symN _ _ B)) in F. congruence. 
  Qed.            

           
  Fixpoint test_path_target (d : nat) (l : weighted_path) : bool :=
    match l with
    | [] => false
    | [a] => d =n?= (arc_target a)
    | _ :: rest => test_path_target d rest 
    end.

  Definition is_path_source c p      := test_path_source c p = true.
  Definition is_path_target c p      := test_path_target c p = true.
  Local Infix "is_source_of" := is_path_source (at level 70).
  Local Infix "is_target_of" := is_path_target (at level 70).


  Lemma is_source_of_intro :
    ∀ a b c v p q, (p =p= (b, c, v) :: q) -> a =n= b -> a is_source_of p. 
  Proof. intros a b c v p q A B.
         compute. destruct p.
         + compute in A. congruence.
         + destruct w as [[d e] v'].
           apply eq_weighted_path_elim in A.
           destruct A as [A C].
           apply eq_weighted_arc_elim in A.
           destruct A as [A [D E]].
           exact (trnN _ _ _ B (symN _ _ A)). 
  Qed.

  Lemma is_source_of_elim : ∀ a p, a is_source_of p ->
      {' ((b,c,v),q) : weighted_arc * weighted_path |  (p =p= (b, c, v) :: q) ∧ a =n= b}. 
  Proof. intros a p G. destruct p.
         + compute in G. congruence. 
         + destruct w. destruct p0. 
           exists ((n, n0, l), p). split. 
           ++ apply eq_weighted_path_reflexive. 
           ++ compute in G. exact G. 
  Qed.


 Lemma source_same_path : (* prove this using a congruence on is_source_of  or test_path_source ? *) 
    ∀ p₁ p₂,  p₁ =p= p₂ -> 
        ∀ x y,  x is_source_of p₁ -> y is_source_of p₂ -> x =n= y.
  Proof. intros p₁ p₂ A x y B C.
         apply is_source_of_elim in B. destruct B as [[[[b c] v1] q1] [P1 Q1]]. 
         apply is_source_of_elim in C. destruct C as [[[[d e] v2] q2] [P2 Q2]].
         apply eq_weighted_path_symmetric in P1.         
         assert (D := eq_weighted_path_transitive _ _ _ P1 A).
         assert (E := eq_weighted_path_transitive _ _ _ D P2).
         apply eq_weighted_path_elim in E. destruct E as [E F]. 
         apply eq_weighted_arc_elim in E. destruct E as [E [I J]].
         exact (trnN _ _ _ Q1 (trnN _ _ _ E (symN _ _ Q2))). 
Qed. 


  (****************** congruence of map ********************)

  Lemma map_path_congruence
        (f : weighted_arc -> R)
        (conf : ∀ a a', a =a= a' -> (f a) =r= (f a')) : 
       ∀ (p q : weighted_path),  p =p= q -> map f p =vl= map f q. 
  Proof. induction p;  destruct q. 
         + intros A. compute. reflexivity. 
         + intros A. compute in A. congruence.
         + intros A. compute in A. congruence.            
         + intros A. simpl. 
           apply eq_weighted_path_elim in A. destruct A as [A B].
           apply eq_value_list_intro. 
           ++ exact (conf _ _ A). 
           ++ exact (IHp _ B). 
  Qed. 

    Lemma map_label_list_congruence
        (f : weighted_arc -> L)
        (conf : ∀ a a', a =a= a' -> (f a) =l= (f a')) : 
       ∀ (p q : weighted_path),  p =p= q -> map f p =ll= map f q. 
  Proof. induction p;  destruct q. 
         + intros A. compute. reflexivity. 
         + intros A. compute in A. congruence.
         + intros A. compute in A. congruence.            
         + intros A. simpl. 
           apply eq_weighted_path_elim in A. destruct A as [A B].
           apply eq_label_list_intro. 
           ++ exact (conf _ _ A). 
           ++ exact (IHp _ B). 
  Qed. 

 (****************** congruences of fold` ********************)

  (* generalize these proofs? *) 
  
  Lemma fold_right_path_congruence
        (f : weighted_arc -> R -> R)
        (conf : ∀ a a' v v', a =a= a' -> v=r=v' -> (f a v) =r= (f a' v')) :  (* make this a def *) 
    ∀ (p₁ p₂ : weighted_path) (v : R),
          p₁ =p= p₂ -> fold_right f v p₁ =r= fold_right f v p₂. 
  Proof. induction p₁;  destruct p₂. 
         + intros v A. compute. apply refR. 
         + intros v A. compute in A. congruence.
         + intros v A. compute in A. congruence.            
         + intros v A. simpl. 
           apply eq_weighted_path_elim in A. destruct A as [A B].
           assert (C := IHp₁ _ v B).
           exact (conf _ _ _ _ A C). 
  Qed. 

  Lemma fold_right_value_list_congruence
        (f : R -> R -> R)
        (conf : bop_congruence R eqR f) : 
      ∀ (l₁ l₂ : value_list) (v : R), (l₁ =vl= l₂) -> fold_right f v l₁ =r= fold_right f v l₂.
    Proof. induction l₁;  destruct l₂. 
         + intros v A. compute. apply refR. 
         + intros v A. compute in A. congruence.
         + intros v A. compute in A. congruence.            
         + intros v A. simpl. 
           apply eq_value_list_elim in A. destruct A as [A B].
           assert (C := IHl₁ _ v B).
           exact (conf _ _ _ _ A C). 
    Qed.


  Lemma fold_right_label_list_congruence
        (f : L -> R -> R)
        (f_cong : ltr_congruence L R eqL eqR f) : 
      ∀ (l₁ l₂ : label_list) (v : R), (l₁ =ll= l₂) -> fold_right f v l₁ =r= fold_right f v l₂.
    Proof. induction l₁;  destruct l₂. 
         + intros v A. compute. apply refR. 
         + intros v A. compute in A. congruence.
         + intros v A. compute in A. congruence.            
         + intros v A. simpl. 
           apply eq_label_list_elim in A. destruct A as [A B].
           assert (C := IHl₁ _ v B).
           exact (f_cong _ _ _ _ A C). 
    Qed.
    

 (****************** the weight of a weighted path ********************)

  
 Definition label_of_arc (a : weighted_arc) : L :=
    match a with 
    | (_, _, l) => l
    end.

 Lemma label_of_arc_congruence : ∀ a a', a =a= a' -> label_of_arc a =l= label_of_arc a'.
 Proof. intros a a' A. unfold label_of_arc.
        destruct a as [[a b] v]; destruct a' as [[a' b'] v'].
        apply eq_weighted_arc_elim in A. destruct A as [_ [_ A]]. 
        exact A. 
 Qed.         

 Definition ltr_of_list : label_list -> R := fold_right ltr 1. 

 Lemma ltr_of_list_congruence : 
     ∀l1 l2 : label_list, l1 =ll= l2 -> ltr_of_list l1 =r= ltr_of_list l2.
 Proof. intros l1 l2 A.
        unfold ltr_of_list.
        apply fold_right_label_list_congruence; auto. 
 Qed. 
 
  Definition left_weight_of_path (p : weighted_path) : R := ltr_of_list (map label_of_arc p). 

  Definition lw := left_weight_of_path.
  
  Lemma map_label_of_arc_congruence : ∀ p q, p =p= q -> map label_of_arc p =ll= map label_of_arc q.
  Proof. intros p q A.
         apply map_label_list_congruence; auto.
         apply label_of_arc_congruence. 
  Qed. 
  
  Lemma left_weight_of_path_congruence : 
        ∀ p q, p =p= q -> lw p =r= lw q. 
  Proof. intros p q E. unfold lw, left_weight_of_path.
         unfold ltr_of_list.
         assert (A := map_label_of_arc_congruence p q E). 
         apply fold_right_label_list_congruence; auto.
  Qed. 

  
(****************** Define when a path is well-formed wrt a matrix  ********************)

   Definition arc_has_matrix_label (m : functional_matrix L) (a : weighted_arc) : bool :=
     match a with
       ((b, c), v) =>  (m b c) =l?= v
     end.


   Lemma arc_has_matrix_label_congruence (m : functional_matrix L) (cong : CongL m) : 
     ∀ a a', a =a= a' -> arc_has_matrix_label m a = arc_has_matrix_label m a'.
   Proof. intros a a' A.
          destruct a as [[a b] v]; destruct a' as [[a' b'] v']. 
          apply eq_weighted_arc_elim in A. destruct A as [A [B C]]. 
          compute.
          assert (D := cong _ _ _ _ A B).
          case_eq(m a b =l?= v); intro E; case_eq(m a' b' =l?= v'); intro F; auto.
          ++ rewrite (trnL _ _ _ (trnL _ _ _ (symL _ _ D) E) C) in F. congruence. 
          ++ rewrite (trnL _ _ _ D (trnL _ _ _ F (symL _ _ C))) in E. congruence. 
   Qed.             
    
   
   Definition path_has_matrix_labels (m : functional_matrix L) (p : weighted_path) : bool :=
     forallb (arc_has_matrix_label m) p.

   Lemma path_has_matrix_labels_congruence (m : functional_matrix L) (cong : CongL m):
     ∀ p q,  p =p= q -> path_has_matrix_labels m p = path_has_matrix_labels m q. 
   Proof. unfold path_has_matrix_labels.
          induction p; destruct q.
          + compute; auto. 
          + intro A; compute in A; congruence. 
          + intro A; compute in A; congruence.
          + intro A. simpl.
            apply eq_weighted_path_elim in A; destruct A as [A B].
            rewrite (IHp _ B).
            rewrite (arc_has_matrix_label_congruence m cong _ _ A). 
            reflexivity. 
   Qed.           

   Definition arc_is_consistent_with_path  (a : weighted_arc) (p : weighted_path) : bool :=
     match p with
     | [] => true
     | _ => test_path_source (arc_target a) p
     end. 


   Lemma arc_is_consistent_with_path_congruence :
        ∀ a1 a2 p q, a1 =a= a2 -> p =p= q -> arc_is_consistent_with_path a1 p = arc_is_consistent_with_path a2 q. 
   Proof. intros a1 a2 p q A B.
          unfold arc_is_consistent_with_path.
          destruct p; destruct q; auto.
          + compute in B. congruence. 
          + compute in B. congruence. 
          + apply test_path_source_congruence. 
            ++ apply arc_target_congruence; auto. 
            ++ exact B. 
   Qed. 

   Fixpoint path_is_arc_consistent (p : weighted_path) :=
     match p with
     | [] => true
     | a :: q => bop_and (arc_is_consistent_with_path a q) (path_is_arc_consistent q)
     end.

   Lemma path_is_arc_consistent_congruence : ∀ p q, p =p= q -> path_is_arc_consistent p = path_is_arc_consistent q.
   Proof. induction p; destruct q; intro A; simpl. 
          + reflexivity. 
          + compute in A. congruence.
          + compute in A. congruence.
          + apply eq_weighted_path_elim in A. 
            destruct A as [A B].
            rewrite (IHp _ B).
            rewrite (arc_is_consistent_with_path_congruence _ _ _ _ A B). 
            reflexivity. 
   Qed.

(****************** Matrix of weighted paths of length k  *************************)

   Definition zeroP : weighted_path_set := [].
   Definition oneP : weighted_path_set := [[]].

   Definition plusP : binary_op weighted_path_set := bop_union eq_weighted_path. 
     (*fun X => fun Y => X ++ Y.*) 

   Definition path_adjacency_arcs (m : functional_matrix L) : functional_matrix weighted_arc := 
    fun (i j : nat) =>  ((i, j), m i j). 

   Definition ltr_extend_path : ltr_type weighted_arc weighted_path :=
     fun a => fun p => a :: p. 

   Lemma ltr_extend_path_congruence :
     ltr_congruence weighted_arc
                    weighted_path
                    eq_weighted_arc
                    eq_weighted_path
                    ltr_extend_path.
   Proof. unfold ltr_congruence in ltr_cong.
          unfold ltr_congruence.
          intros l1 l2.
          induction s1 as [ | [[i j] l] s1];
          induction s2 as [ | [[i' j'] l'] s2];
            intros A B.
          - unfold ltr_extend_path.
            apply brel_list_cons_intro; auto. 
          - compute in B. discriminate B. 
          - compute in B. discriminate B. 
          - simpl.
            apply brel_list_cons_intro; auto. 
   Qed.
   
   Definition ltr_extend_paths : ltr_type weighted_arc weighted_path_set :=
     fun a (X : weighted_path_set) => List.map (ltr_extend_path a) X.

   Definition matrix_of_k_length_paths m n k :=
     left_matrix_exponentiation zeroP oneP plusP ltr_extend_paths n (path_adjacency_arcs m) k.

   Lemma ltr_extend_paths_congruence :
     ltr_congruence weighted_arc
                    weighted_path_set
                    eq_weighted_arc
                    eq_weighted_path_set
                    ltr_extend_paths.
   Proof. unfold ltr_congruence in ltr_cong.
          unfold ltr_congruence. 
          intros l1 l2 s1 s2 A B.
          unfold eq_weighted_path_set. 
          unfold ltr_extend_paths.
          apply brel_set_map_congruence.
          - exact (eq_weighted_path_reflexive). 
          - exact (eq_weighted_path_symmetric). 
          - exact (eq_weighted_path_transitive). 
          - intros s t C.
            apply ltr_extend_path_congruence; auto.
            apply eq_weighted_arc_reflexive. 
          - intros s t C.
            apply ltr_extend_path_congruence; auto.
            apply eq_weighted_arc_reflexive. 
          - intros s t C.
            apply ltr_extend_path_congruence; auto.
          - exact B.
   Qed. 

   (******* Local definitions ****************************************)

   Local Notation "Pk[ m , k , n ]"  := (matrix_of_k_length_paths m n k) (at level 70).

   Local Notation "LW[ X ]" := (big_plus_set zero plus eq_weighted_path lw X) (at level 70). 
   Local Notation "LWP[ X ]" := (fun i j => LW[ X i j]) (at level 100).

   Local Notation "[I]" := (matrix_mul_identity zero one) (at level 70).

   Local Notation "[IP]" := (matrix_mul_identity zeroP oneP) (at level 70).

   Local Notation "A[ m ]" := (path_adjacency_arcs m) (at level 70).

   Local Infix "*[| n |]>" := (left_matrix_mul zeroP plusP ltr_extend_paths n) (at level 70).
   
   Local Infix "+PM" := (matrix_add plusP ) (at level 70).
   
   Local Infix "+P" := (plusP) (at level 70).

   Local Infix "=PM=" := (eq_functional_matrix_prop weighted_path_set eq_weighted_path_set) (at level 70).

   Local Infix "=PS=" := (eq_weighted_path_set) (at level 70).

   (****************************** matrix R congruences ***********************************************)

  Lemma left_matrix_mul_preserves_congruence
        (m1 : functional_matrix L)
        (m2 : functional_matrix R)        
        (cL : CongL m1) 
        (cR : CongR m2)
        (n : nat) : CongR (m1 *[ n ]> m2).     
  Proof. intros i j i' j' A B.
         unfold left_matrix_mul.
         apply big_plus_congruence; auto.
         intros i0 j0 C.
         (* bad lemma name *)
         apply (left_row_i_dot_col_j_congruence' _ _ eqL eqR); auto. 
  Qed. 
   
   (*
    congrM
     : ∀ (n : nat) (m1 m2 : functional_matrix L) 
         (m3 m4 : functional_matrix R),
         CongL m1 → CongR m3
           → m1 =L= m2 → m3 =M= m4 → (m1 *[ n ]> m3) =M= (m2 *[ n ]> m4)
    *) 
  Definition congrM := left_matrix_mul_congruence L R eqL eqR plus zero ltr refR trnR trnL congrP ltr_cong.

  (*
    congrM_right
     : ∀ (n : nat) (m : functional_matrix L) (m3 m4 : functional_matrix R),
         CongL m → CongR m3 → m3 =M= m4 → (m *[ n ]> m3) =M= (m *[ n ]> m4)
  *)   
  Definition congrM_right
             (n : nat) (m : functional_matrix L)
             (m3 m4 : functional_matrix R)
             (cL : CongL m)
             (cR : CongR m3)
             :=
               congrM n m m m3 m4 cL cR (eq_functional_matrix_prop_reflexive L eqL refL m).


  (****************************** matrix P congruences ***********************************************)
  
   Lemma plusP_congruence : bop_congruence weighted_path_set eq_weighted_path_set plusP.
   Proof. apply bop_union_congruence. 
          - exact (eq_weighted_path_reflexive).
          - exact (eq_weighted_path_symmetric).             
          - exact (eq_weighted_path_transitive).
   Qed.             
    
  (*
    congrPM
     : ∀ (n : nat) (m1 m2 : functional_matrix weighted_arc) 
         (m3 m4 : functional_matrix weighted_path_set),
         matrix_algorithms.CongL weighted_arc eq_weighted_arc m1
         → matrix_algorithms.CongR weighted_path_set eq_weighted_path_set m3
           → eq_functional_matrix_prop weighted_arc eq_weighted_arc m1 m2
             → m3 =PM= m4 → (m1 *[| n |]> m3) =PM= (m2 *[| n |]> m4)
   *) 
  Definition congrPM := left_matrix_mul_congruence
                          weighted_arc
                          weighted_path_set
                          eq_weighted_arc
                          eq_weighted_path_set
                          plusP
                          zeroP
                          ltr_extend_paths
                          eq_weighted_path_set_reflexive
                          eq_weighted_path_set_transitive
                          eq_weighted_arc_transitive
                          plusP_congruence
                          ltr_extend_paths_congruence.

  (* congrPM_right
     : ∀ (n : nat) (m : functional_matrix weighted_arc) 
         (m3 m4 : functional_matrix weighted_path_set),
         functional_matrix_congruence weighted_arc eq_weighted_arc m
         → functional_matrix_congruence weighted_path_set
             eq_weighted_path_set m3
           → m3 =PM= m4 → (m *[| n |]> m3) =PM= (m *[| n |]> m4)
  *) 
  Definition congrPM_right
             (n : nat)
             (m : functional_matrix weighted_arc)
             (m3 m4 : functional_matrix weighted_path_set)
             (cL : functional_matrix_congruence weighted_arc eq_weighted_arc m)
             (cR : functional_matrix_congruence weighted_path_set eq_weighted_path_set m3)
             :=
               congrPM n m m m3 m4 cL cR
                       (eq_functional_matrix_prop_reflexive
                          weighted_arc
                          eq_weighted_arc 
                          eq_weighted_arc_reflexive
                          m).
  
  Lemma adjacency_congruence (m : functional_matrix L) (cL : CongL m) : 
    functional_matrix_congruence weighted_arc eq_weighted_arc (A[ m]). 
  Proof. intros i j i' j' A B.
         unfold path_adjacency_arcs.
         unfold eq_weighted_arc. 
         apply brel_product_intro.
         + apply brel_product_intro; auto. 
         + apply cL; auto.
  Qed. 

    Lemma path_left_matrix_mul_preserves_congruence
        (m1 : functional_matrix L)
        (m2 : functional_matrix weighted_path_set)          
        (cL : CongL m1)
        (cP : CongP m2)         
        (n k : nat) : CongP ((A[ m1 ]) *[| n |]> m2). 
    Proof. intros i j i' j' A B.
         unfold left_matrix_mul.
         apply big_plus_congruence; auto.
           + apply eq_weighted_path_set_reflexive.
           + apply plusP_congruence. 
           + intros i0 j0 C.
             (* bad lemma name *)
             apply (left_row_i_dot_col_j_congruence' _ _ eq_weighted_arc eq_weighted_path_set); auto.
             ++ apply ltr_extend_paths_congruence; auto.
             ++ apply adjacency_congruence; auto. 
  Qed. 

    

  (****************************** LWP congruences ***********************************************)

    Lemma LWP_preserves_congruence 
       (assoc : bop_associative R eqR plus)
       (comm : bop_commutative R eqR plus) : 
      ∀ X, CongP X -> CongR (LWP[ X ]).
  Proof. intros X cong. intros i j i' j' A B.
         apply big_plus_set_congruence; auto.
         - apply eq_weighted_path_congruence. 
         - apply eq_weighted_path_reflexive. 
         - apply eq_weighted_path_symmetric. 
         - apply eq_weighted_path_transitive. 
         - exact eq_weighted_path. 
         - apply left_weight_of_path_congruence.
  Qed. 

  Lemma IP_congruence : CongP ([IP]).
  Proof. exact (matrix_mul_identity_congruence _
                   eq_weighted_path_set
                   eq_weighted_path_set_reflexive zeroP oneP).
  Qed. 

  Lemma LWP_IP_congruence
    (assoc : bop_associative R eqR plus)
    (comm : bop_commutative R eqR plus) : CongR (LWP[ [IP] ]).
  Proof. apply LWP_preserves_congruence; auto. 
         apply IP_congruence. 
  Qed.          

  
   Lemma LW_congruence
    (assoc : bop_associative R eqR plus)
    (comm : bop_commutative R eqR plus) : 
    ∀ X Y, eq_weighted_path_set X Y = true -> LW[ X ] =r= LW[ Y ].
   Proof. intros X Y A.
          apply big_plus_set_congruence; auto.
         - apply eq_weighted_path_congruence. 
         - apply eq_weighted_path_reflexive. 
         - apply eq_weighted_path_symmetric. 
         - apply eq_weighted_path_transitive. 
         - exact eq_weighted_path. 
         - apply left_weight_of_path_congruence.
  Qed.           


  
  Lemma LWP_congruence
    (assoc : bop_associative R eqR plus)
    (comm : bop_commutative R eqR plus) : 
    ∀ m1 m2, m1 =PM= m2 -> LWP[ m1 ] =M= LWP[ m2 ].
  Proof. intros m1 m2 A i j.
         apply LW_congruence; auto. 
  Qed. 

  (****************************** matrix Pk congruences ***********************************************)

    Lemma unfold_Pk (m : functional_matrix L) (n : nat) : 
     ∀ k, Pk[ m, S k, n ] =PM= (A[ m ] *[| n |]> (Pk[ m , k, n ])). 
   Proof. intro k. unfold matrix_of_k_length_paths. 
          exact (unfold_left_matrix_exponentiation _ _
                    eq_weighted_path_set
                    plusP
                    zeroP
                    oneP
                    ltr_extend_paths
                    eq_weighted_path_set_reflexive
                    (A[ m ])
                    n
                    k).
   Qed.           

  Lemma Pk_preserves_congruence
        (m : functional_matrix L)
        (cL : CongL m)
        (n : nat) : ∀ k, CongP (Pk[ m, k, n ]).
  Proof. induction k; intros i j i' j' A B.
         + unfold matrix_of_k_length_paths.
           unfold left_matrix_exponentiation.
           exact (IP_congruence i j i' j' A B).
         + assert (C := unfold_Pk m n k i j).
           assert (D := unfold_Pk m n k i' j').
           assert (E := path_left_matrix_mul_preserves_congruence m (Pk[ m, k, n]) cL IHk n k).
           assert (F := E i j i' j' A B).
           assert (G := eq_weighted_path_set_transitive _ _ _ C F). 
           apply eq_weighted_path_set_symmetric in D.
           exact (eq_weighted_path_set_transitive _ _ _ G D). 
  Qed. 

  (********************** matrix equalities ae equiv relations  ***********************)

  Lemma matrixR_equality_reflexive : 
    ∀X, X =M= X.
  Proof. exact (eq_functional_matrix_prop_reflexive R eqR refR). Qed. 

  Lemma matrixR_equality_symmetric :
    ∀X Y, X =M= Y -> Y =M= X.
  Proof. exact (eq_functional_matrix_prop_symmetric R eqR symR). Qed. 

  Lemma matrixR_equality_transitive :
    ∀X Y Z, X =M= Y -> Y =M= Z -> X =M= Z.
  Proof. exact (eq_functional_matrix_prop_transitive R eqR trnR). Qed. 

  Lemma matrixL_equality_reflexive : 
    ∀X, X =L= X.
  Proof. exact (eq_functional_matrix_prop_reflexive L eqL refL). Qed. 

  Lemma matrixL_equality_symmetric :
    ∀X Y, X =L= Y -> Y =L= X.
  Proof. exact (eq_functional_matrix_prop_symmetric L eqL symL). Qed. 

  Lemma matrixL_equality_transitive :
    ∀X Y Z, X =L= Y -> Y =L= Z -> X =L= Z.
  Proof. exact (eq_functional_matrix_prop_transitive L eqL trnL). Qed. 

  Lemma matrixP_equality_reflexive : 
    ∀X, X =PM= X.
  Proof. exact (eq_functional_matrix_prop_reflexive _
                  eq_weighted_path_set
                  eq_weighted_path_set_reflexive).
  Qed.

  Lemma matrixP_equality_symmetric :
    ∀X Y, X =PM= Y -> Y =PM= X.
  Proof. exact (eq_functional_matrix_prop_symmetric _
                  eq_weighted_path_set                                                    
                  eq_weighted_path_set_symmetric).
  Qed.   

  Lemma matrixP_equality_transitive :
    ∀X Y Z, X =PM= Y -> Y =PM= Z -> X =PM= Z.
  Proof. exact (eq_functional_matrix_prop_transitive _
                  eq_weighted_path_set                                                    
                  eq_weighted_path_set_transitive).
  Qed.   
  
  (***************************** equations *********************) 

  Lemma identity_is_weight_of_matrix_of_paths_of_length_zero
        (plusID : bop_is_id R eqR plus 0)
        (m : functional_matrix L) (n : nat) : 
             [I] =M= LWP[ Pk[ m , 0, n ]  ].
  Proof. intros i j.  unfold matrix_of_k_length_paths.
         simpl. unfold matrix_mul_identity.         
         case_eq(i =n?= j); intro A; compute. 
         + destruct (plusID 1) as [C D].
           apply symR in D. exact D. 
         + apply refR. 
  Qed.

  Lemma LWP_of_path_identity_is_identity (plusID : bop_is_id R eqR plus 0) :
         LWP[ [IP] ] =M= [I]. 
 Proof. intros i j. unfold matrix_mul_identity.
        unfold zeroP, oneP.
        case_eq(i =n?= j); intro A; compute. 
        + destruct (plusID 1) as [B C]. exact C. 
        + apply refR. 
 Qed.

 
 Lemma LWP_of_path_identity_is_weight_of_matrix_of_paths_of_length_zero
       (plusID : bop_is_id R eqR plus 0)
       (m : functional_matrix L) (n : nat) :        
         LWP[ [IP] ] =M= LWP[ Pk[ m , 0, n ]  ].
 Proof. intros i j.
        assert (A := identity_is_weight_of_matrix_of_paths_of_length_zero plusID m n i j).
        assert (B := LWP_of_path_identity_is_identity plusID i j).
        simpl in A, B. 
        exact (trnR _ _ _ B A). 
 Qed.


 Lemma LW_distributes_over_path_plus
       (assoc : bop_associative R eqR plus)
       (comm : bop_commutative R eqR plus)
       (idP : bop_is_id R eqR plus 0) 
       (X Y : functional_matrix weighted_path_set): 
          ∀ i j, LW[ (X i j) +P (Y i j) ] =r= LW[ X i j ] + LW[ Y i j ]. 
 Proof. intros i j. apply symR. 
        apply big_plus_set_distributes_over_union; auto.
         - apply eq_weighted_path_congruence. 
         - apply eq_weighted_path_reflexive. 
         - apply eq_weighted_path_symmetric. 
         - apply eq_weighted_path_transitive. 
         - apply left_weight_of_path_congruence.
  Qed. 

 Lemma LWP_distributes_over_matrix_add
       (assoc : bop_associative R eqR plus)
       (comm : bop_commutative R eqR plus)
       (idP : bop_is_id R eqR plus 0) : 
            ∀ X Y, LWP[ X +PM Y ] =M= LWP[ X ] +M LWP[ Y ]. 
 Proof. intros X Y i j. unfold matrix_add.
        apply LW_distributes_over_path_plus; auto. 
 Qed.

 Lemma lw_distributes_over_ltr_extend_path
       (i j : nat) (l : L) : 
   ∀ p : weighted_path,
       lw (ltr_extend_path ((i, j), l) p) =r= (l |> lw p). 
 Proof. intros p. destruct p.        
        + compute. apply refR. 
        + simpl. unfold lw. unfold left_weight_of_path.
          unfold ltr_of_list. simpl. 
          apply refR. 
 Qed. 

 
 Lemma IP_not_nil : ∀ i j p, (p [in set] ([IP] i j)) -> (i =n= j) + ((p = nil) -> False). 
  Proof. unfold matrix_mul_identity. unfold oneP, zeroP. 
         intros i j p A. 
         case_eq(i =n?= j); intro B. 
         + left. exact B.
         + right. rewrite B in A.
           compute in A. 
           discriminate A. 
  Qed. 

  Lemma LW_over_cons (p : weighted_path) :
    ∀ X, in_set eq_weighted_path X p = false ->
         LW[ p :: X ] =r= (lw p) + LW[ X ].
  Proof. intros X A.
         exact (big_plus_set_cons _ _ eqR refR eq_weighted_path plus zero lw p X A).
  Qed. 

  Lemma LW_ignore_cons (p : weighted_path) :
    ∀ X, in_set eq_weighted_path X p = true ->
         LW[ p :: X ] =r= LW[ X ].
  Proof. intros X A.
         exact(big_plus_set_ignore_cons _ _ eqR refR eq_weighted_path plus zero lw p X A).
  Qed.

   Lemma LW_of_empty_set : LW[ [] ] =r= 0. 
   Proof. compute. apply refR. Qed. 
          

  Lemma ltr_extend_path_cancellative
    (m : functional_matrix L) 
    (i q : nat) : 
    ∀ p p', eq_weighted_path (ltr_extend_path ((A[ m]) i q) p') (ltr_extend_path ((A[ m]) i q) p) = true
            -> eq_weighted_path p p' = true.
  Proof. intros p p' A.
         unfold ltr_extend_path in A.
         unfold path_adjacency_arcs in A.
         unfold eq_weighted_path in A.
         apply brel_list_cons_elim in A.
         destruct A as [A B].
         apply eq_weighted_path_symmetric.
         exact B. 
  Qed.
  
  Lemma LW_singleton
    (id : bop_is_id R eqR plus 0) :
      ∀ p, LW[ [p]] =r= (lw p).
  Proof. intro p.
         unfold big_plus_set. simpl.          (* should be a big_plus_set lemma! *) 
         unfold big_plus. simpl.
         destruct (id (lw p)) as [A B]; auto.
  Qed.

  Lemma lw_distributes_over_path_adjacency_arcs
    (m : functional_matrix L) 
    (i q : nat) : 
    ∀ p, lw ((A[ m]) i q :: p) =r= (m i q |> (lw p)). 
  Proof. intro p.
         assert (A := lw_distributes_over_ltr_extend_path i q (m i q) p). 
         unfold ltr_extend_path in A.
         unfold path_adjacency_arcs.
         exact A.
  Qed.
  
  Lemma LW_over_extend_path
    (id : bop_is_id R eqR plus 0)
    (m : functional_matrix L) 
    (i q : nat) : 
    ∀ p, LW[ [ltr_extend_path ((A[ m ]) i q) p]] =r= (m i q |> LW[ [p] ]).
  Proof. intro p.
         unfold ltr_extend_path.
         assert (A : in_set eq_weighted_path [] ((A[ m]) i q :: p) = false).
         {
           compute. reflexivity. 
         }
         apply LW_over_cons in A.
         assert (B := LW_of_empty_set).
         assert (C := congrP _ _ _ _ (refR (lw ((A[ m]) i q :: p))) B).
         assert (D := trnR _ _ _ A C). 
         destruct (id (lw ((A[ m]) i q :: p))) as [E F].
         assert (G := trnR _ _ _ D F).
         assert (H : lw ((A[ m]) i q :: p) =r= (m i q |> (LW[ [p]]))).
         {
           assert (I := LW_singleton id p). apply symR in I.
           assert (J := lw_distributes_over_path_adjacency_arcs m i q p).
           assert (K := ltr_cong _ _ _ _ (refL (m i q)) I).
           exact (trnR _ _ _ J K). 
         } 
         exact (trnR _ _ _ G H).
  Qed. 
         
  Lemma LW_over_extend_paths
    (id : bop_is_id R eqR plus 0)
    (ann : ltr_is_ann L R eqR ltr 0)
    (LD : slt_distributive eqR plus ltr) 
    (m : functional_matrix L) 
    (i q : nat) : 
   ∀ (X : weighted_path_set),
     LW[ ltr_extend_paths ((A[ m ]) i q) X ] 
     =r= 
     (m i q |> (LW[ X ])).
 Proof. induction X. 
        - compute. apply symR. apply ann. 
        - unfold ltr_extend_paths. simpl.
          case_eq(in_set eq_weighted_path X a); intro A.
          + assert (B : in_set eq_weighted_path (map (ltr_extend_path ((A[ m]) i q)) X) (ltr_extend_path ((A[ m]) i q) a) = true).
            {
              assert (C : ∀ p p',
                       eq_weighted_path p p' = true
                       → eq_weighted_path ((ltr_extend_path ((A[ m]) i q)) p)
                                           ((ltr_extend_path ((A[ m]) i q)) p') = true).
              {
                intros p p' C. 
                apply ltr_extend_path_congruence; auto. 
                apply eq_weighted_arc_reflexive.
              }
              assert (D := in_set_map_intro
                             _ _ eq_weighted_path eq_weighted_path
                             eq_weighted_path_reflexive
                             eq_weighted_path_symmetric
                             eq_weighted_path_symmetric                             
                             eq_weighted_path_transitive
                             (ltr_extend_path ((A[ m]) i q))
                             C 
                             X
                             (ltr_extend_path ((A[ m]) i q) a)).
              apply D. exists a. split; auto.
              apply eq_weighted_path_reflexive. 
            } 
            apply LW_ignore_cons in A.
            apply LW_ignore_cons in B.
            assert (D := trnR _ _ _ B IHX). apply symR in A.
            assert (E := ltr_cong _ _ _ _ (refL (m i q)) A).
            exact (trnR _ _ _ D E). 
          + assert (B : in_set eq_weighted_path (map (ltr_extend_path ((A[ m]) i q)) X) (ltr_extend_path ((A[ m]) i q) a) = false).
            {
              case_eq(in_set eq_weighted_path (map (ltr_extend_path ((A[ m]) i q)) X) (ltr_extend_path ((A[ m]) i q) a)); intro B; auto.
              apply (in_set_map_elim
                       _ _ eq_weighted_path eq_weighted_path
                       eq_weighted_path_reflexive
                       eq_weighted_path_symmetric
                       eq_weighted_path_symmetric)
                in B.
              destruct B as [a' [C D]].
              apply ltr_extend_path_cancellative in D. apply eq_weighted_path_symmetric in D. 
              rewrite (in_set_right_congruence _ _
                       eq_weighted_path_symmetric
                       eq_weighted_path_transitive
                       a' a X 
                       D C) in A. 
              discriminate A. 
            } 
            apply LW_over_cons in A.
            apply LW_over_cons in B.
            (*
                LW[ ltr_extend_path ((A[ m]) i q) a :: map (ltr_extend_path ((A[ m]) i q)) X] 
                =r= {B} 
                lw (ltr_extend_path ((A[ m]) i q) a) + LW[ map (ltr_extend_path ((A[ m]) i q)) X]
                =r= {congrP, (IHX C)}
                lw (ltr_extend_path ((A[ m]) i q) a) + (m i q |> LW[ X ])
                =r= {lw_distributes_over_ltr_extend_path, congrP} 
                (m i q |> lw a) + (m i q |> LW[ X ])
                =r= {LD} 
                m i q |> ((lw a) + LW[ X ])
                =r= {A, ltr_cong}
                m i q |> LW[ a :: X]
               *)
            apply symR in A.
            assert (E := congrP _ _ _ _ (refR (lw (ltr_extend_path ((A[ m]) i q) a))) IHX).
            assert (F := trnR _ _ _ B E). 
            assert (I : lw (ltr_extend_path ((A[ m]) i q) a) =r= ((m i q) |> lw a)).
            {
              apply lw_distributes_over_ltr_extend_path.
            }
            assert (J := congrP _ _ _ _ I (refR (m i q |> (LW[ X])))).
            assert (K := trnR _ _ _ F J).
            assert (G := LD (m i q) (lw a) (LW[ X ])). apply symR in G.
            assert (H := ltr_cong _ _ _ _ (refL (m i q)) A). 
            assert (N := trnR _ _ _ K G). 
            exact (trnR _ _ _ N H). 
 Qed. 


 Lemma LW_distributes_over_path_set_union
   (id : bop_is_id R eqR plus 0)
   (assoc : bop_associative R eqR plus)
   (comm : bop_commutative R eqR plus) :
   ∀ X Y,
     (∀ x, in_set eq_weighted_path X x = true
             -> in_set eq_weighted_path Y x = false) -> 

     LW[ X +P Y ] =r= LW[ X ] + LW[ Y].
 Proof. induction X; intros Y A.
        - assert (B : LW[ [] ] =r= 0).
          {
            compute. apply refR.
          }
          assert (C : [] +P Y =PS= Y = true).
          {
            apply bop_union_with_nil_left.
            apply eq_weighted_path_reflexive.
            apply eq_weighted_path_symmetric.
            apply eq_weighted_path_transitive. 
          }
          apply LW_congruence in C; auto. 
          destruct (id (LW[ Y ])) as [D E]. apply symR in D, B. 
          assert (F := trnR _ _ _ C D).
          assert (G := congrP _ _ _ _ B (refR (LW[ Y ]))).
          exact (trnR _ _ _ F G).
        - assert (B : ∀ x : weighted_path,
                     in_set eq_weighted_path X x = true →
                     in_set eq_weighted_path Y x = false).
          {
            intros x B.
            assert (C : in_set eq_weighted_path (a :: X) x = true).
            {
              apply in_set_cons_intro; auto.
              apply eq_weighted_path_symmetric. 
            }
            apply (A x); auto. 
          }
          assert (C := IHX Y B).
          assert (Z : LW[ a :: X +P Y] =r= LW[ a :: (X +P Y)]).
          {
            assert (D := bop_union_push_element _ _
                           eq_weighted_path_reflexive
                           eq_weighted_path_symmetric
                           eq_weighted_path_transitive                           
                           Y X a). 
            apply LW_congruence in D; auto.
            exact (symR _ _ D). 
          } 
          case_eq(in_set eq_weighted_path X a); intro D.
          + assert (ZZ : in_set eq_weighted_path (X +P Y) a = true).
            {
              apply in_set_bop_union_intro; auto.
              apply eq_weighted_path_symmetric.
              apply eq_weighted_path_transitive. 
            }     
            apply LW_ignore_cons in D. apply symR in D.
            assert (E := congrP _ _ _ _ D (refR (LW[ Y ]))).
            assert (F := trnR _ _ _ C E).
            assert (G : LW[ a :: X +P Y] =r= LW[ X +P Y]).
            {
              apply LW_ignore_cons in ZZ.
              exact (trnR _ _ _ Z ZZ).
            }
            exact (trnR _ _ _ G F). 
          + assert (ZZ : in_set eq_weighted_path (X +P Y) a = false).
            {
              case_eq(in_set eq_weighted_path (X +P Y) a); intro H; auto.
              apply in_set_bop_union_elim in H.
              * destruct H as [H | H].
                -- rewrite H in D. discriminate D. 
                -- assert (I : in_set eq_weighted_path (a :: X) a = true).
                   {
                     apply in_set_cons_intro; auto.
                     apply eq_weighted_path_symmetric.
                     left. apply eq_weighted_path_reflexive. 
                   }
                   rewrite (A _ I) in H. discriminate H. 
              * apply eq_weighted_path_symmetric.             
            }
            assert (E : LW[ a :: X +P Y] =r= (lw a) + LW[ X +P Y]).
            {
              apply LW_over_cons in ZZ.
              exact (trnR _ _ _ Z ZZ). 
            }
            assert (F := congrP _ _ _ _ (refR (lw a)) C).
            assert (G := trnR _ _ _ E F). 
            apply LW_over_cons in D. apply symR in D.
            assert (H := congrP _ _ _ _ D (refR (LW[ Y ]))).
            assert (I := assoc (lw a) (LW[ X ]) (LW[ Y ])). apply symR in I.
            assert (J := trnR _ _ _ G I). 
            exact (trnR _ _ _ J H). 
Qed. 


    Local Notation "⨁_( l ) f"      := (big_plus zero plus f l) (at level 70).
    Local Notation "⨁_{ X } f"      := (big_plus zeroP plusP f X) (at level 70).

    (*Unset Printing Notations.*)


(*
    in_set eq_weighted_path
                        (⨁_{ list_enum n} (λ q : nat, ltr_extend_paths (i, q, m i q) (if q =n?= j then oneP else zeroP)))
                        [(i, n, m i n)] = false).
 *)
    
    Lemma disjoint_lemma
      (m : functional_matrix L) 
      (P : functional_matrix weighted_path_set)
      (i j n : nat): 
  ∀ x : weighted_path,
    in_set eq_weighted_path (ltr_extend_paths ((A[ m ]) i n) (P n j)) x =
    true
    → in_set eq_weighted_path
        (⨁_{ list_enum n} (λ q : nat,
                             ltr_extend_paths ((A[ m]) i q) (P q j))) x =
      false. 
Admitted.             
  
 Lemma LWP_distributes_over_left_matrix_mul
   (id : bop_is_id R eqR plus 0)
   (ann : ltr_is_ann L R eqR ltr 0)
   (assoc : bop_associative R eqR plus)
   (comm : bop_commutative R eqR plus) 
   (LD : slt_distributive eqR plus ltr) 
   (m : functional_matrix L) (n : nat)
   (P : functional_matrix weighted_path_set): 
    LWP[ A[ m ] *[| n |]> P ] =M= (m *[ n ]> LWP[ P ]).
 Proof.    intros i j. 
           unfold left_matrix_mul. 
           unfold left_row_i_dot_col_j.
           induction n.
           - compute. apply refR.
           - simpl. 
             assert (A := big_plus_cons _ _ eqR refR plus zero (λ q : nat, m i q |> (LW[ P q j])) n (list_enum n)).
             (* B: Why big_plus here and not big_plus_set? 
                Because P does not contain duplicates and order does not matter with union. 
                Note: this is not an issue, of course, with CAPP-defined set-based algebras 
                since the big_plus (in matrix multiplication) is always over a list of indices. 
              *)
             assert (B := big_plus_cons _ _ eq_weighted_path_set eq_weighted_path_set_reflexive
                            plusP zeroP (λ q : nat, ltr_extend_paths ((A[ m]) i q) (P q j)) n (list_enum n)). 
             (*  
                 IHn : LW[ ⨁_{ list_enum n} (λ q : nat, ltr_extend_paths ((A[ m]) i q) (P q j))]
                       =r= 
                       ⨁_( list_enum n) (λ q : nat, m i q |> (LW[ P q j]))

                A : ⨁_( n :: list_enum n) (λ q : nat, m i q |> (LW[ P q j]))
                    =r=
                    (λ q : nat, m i q |> (LW[ P q j])) n 
                    + 
                    ⨁_( list_enum n) (λ q : nat, m i q |> (LW[ P q j]))

                B : ⨁_{ n :: list_enum n} (λ q : nat, ltr_extend_paths ((A[ m]) i q) (P q j))
                    =PS= 
                    ((λ q : nat, ltr_extend_paths ((A[ m]) i q) (P q j)) n 
                     +P 
                    (⨁_{ list_enum n} (λ q : nat, ltr_extend_paths ((A[ m]) i q) (P q j))))

                 ============================
                 LW[ ⨁_{ n :: list_enum n} (λ q : nat, ltr_extend_paths ((A[ m]) i q) (P q j))]
                 =r= 
                 ⨁_( n :: list_enum n) (λ q : nat, m i q |> (LW[ P q j]))

                PROOF: 
                 LW[ ⨁_{ n :: list_enum n} (λ q : nat, ltr_extend_paths ((A[ m]) i q) (P q j)) ]
                 =r= {B, LW_congruence} 
                 LW[ (ltr_extend_paths ((A[ m]) i q) (P q j))
                     +P 
                     ⨁_{ list_enum n} (λ q : nat, ltr_extend_paths ((A[ m]) i q) (P q j)) ]
                 =r= {LW_distributes_over_path_set_union} 
                 LW[ ltr_extend_paths ((A[ m]) i n) (P n j) ] 
                  + 
                 LW[ ⨁_{ list_enum n} (λ q : nat, ltr_extend_paths ((A[ m]) i q) (P q j))]              
                 =r={LW_over_extend_paths, +-congruence} 
                 (λ q : nat, m i q |> (LW[ P q j])) n         
                    + 
                 LW[ ⨁_{ list_enum n} (λ q : nat, ltr_extend_paths ((A[ m]) i q) (P q j))]       
                 =r={ IHn, +-congruence} 
                 (λ q : nat, m i q |> (LW[ P q j])) n         
                    + 
                 ⨁_( list_enum n) (λ q : nat, m i q |> (LW[ P q j]))
                 =r={ A } 
                 ⨁_( n :: list_enum n) (λ q : nat, m i q |> (LW[ P q j]))
              *)
             assert (C : LW[ ⨁_{ n :: list_enum n} (λ q : nat, ltr_extend_paths ((A[ m]) i q) (P q j)) ]
                         =r= 
                         LW[ (ltr_extend_paths ((A[ m]) i n) (P n j)) 
                             +P 
                             ⨁_{ list_enum n} (λ q : nat, ltr_extend_paths ((A[ m]) i q) (P q j)) ] ).
             {
               apply LW_congruence; auto. 
             }
             assert (D : LW[ (ltr_extend_paths ((A[ m]) i n) (P n j))
                             +P 
                             (⨁_{ list_enum n} (λ q : nat, ltr_extend_paths ((A[ m]) i q) (P q j))) ]
                         =r= 
                         LW[ (ltr_extend_paths ((A[ m]) i n) (P n j)) ] 
                         + 
                         LW[ ⨁_{ list_enum n} (λ q : nat, ltr_extend_paths ((A[ m]) i q) (P q j))]).
             {
               apply LW_distributes_over_path_set_union; auto. 
               apply disjoint_lemma. 
             }
             assert (E := trnR _ _ _ C D).
             assert (F : (LW[ (ltr_extend_paths ((A[ m]) i n) (P n j)) ] 
                         + 
                         LW[ ⨁_{ list_enum n} (λ q : nat, ltr_extend_paths ((A[ m]) i q) (P q j))])
                         =r= 
                         (m i n |> (LW[ P n j]))
                         + 
                         LW[ ⨁_{ list_enum n} (λ q : nat, ltr_extend_paths ((A[ m]) i q) (P q j))]).
             {
               apply congrP.
               apply LW_over_extend_paths; auto.
               + apply refR. 
             }
             assert (G := trnR _ _ _ E F).
             assert (H : ((m i n |> (LW[ P n j]))
                          + 
                          LW[ ⨁_{ list_enum n} (λ q : nat, ltr_extend_paths ((A[ m]) i q) (P q j))])
                        =r=
                        (m i n |> (LW[ P n j]))
                        + 
                        ⨁_( list_enum n) (λ q : nat, m i q |> (LW[ P q j]))).
             {
               apply congrP; auto. 
             }
             assert (I := trnR _ _ _ G H).
             apply symR in A. 
             exact (trnR _ _ _ I A).  
Qed.              

  Local Definition trnM := eq_functional_matrix_prop_transitive _ eqR trnR.
  (*Unset Printing Notations.*)
  
  Lemma LWP_distributes_over_left_exponentiation_base_case
       (id : bop_is_id R eqR plus 0)       
       (ann : ltr_is_ann L R eqR ltr 0)
       (assoc : bop_associative R eqR plus)
       (comm : bop_commutative R eqR plus) 
       (LD : slt_distributive eqR plus ltr) 
       (m : functional_matrix L) (cL : CongL m) (n : nat) :  
    LWP[ A[ m ] *[| n |]> [IP] ] =M= (m *[ n ]> [I]).
  Proof.  
    induction n; intros i j.
    - compute. apply refR.
    - unfold left_matrix_mul.
      unfold left_row_i_dot_col_j.
      unfold matrix_mul_identity. simpl.
      assert (A := big_plus_cons _ _ eqR refR plus zero  (λ q : nat, m i q |> (if q =n?= j then 1 else 0)) n (list_enum n)).
      simpl in A.
      assert (B := big_plus_cons _ _ eq_weighted_path_set eq_weighted_path_set_reflexive plusP zeroP
                     (λ q : nat, ltr_extend_paths ((A[ m]) i q) (if q =n?= j then oneP else zeroP)) n (list_enum n)).
      simpl in B. 
      case_eq(n =n?= j); intro C; rewrite C in A, B. 
      + simpl in B. unfold ltr_extend_path in B. unfold path_adjacency_arcs in B.
        apply LW_congruence in B; auto. 
        assert (D : (LW[ [[(i, n, m i n)]]
                         +P 
                         (⨁_{ list_enum n} (λ q : nat, ltr_extend_paths (i, q, m i q) (if q =n?= j then oneP else zeroP))) ])
                      =r= 
                      (LW[ [(i, n, m i n)] :: 
                             (⨁_{ list_enum n} (λ q : nat, ltr_extend_paths (i, q, m i q) (if q =n?= j then oneP else zeroP))) ])).
        {
          apply LW_congruence; auto.
          apply bop_union_cons_shift_left; auto.
          apply eq_weighted_path_reflexive.
          apply eq_weighted_path_symmetric.
          apply eq_weighted_path_transitive. 
        }
        assert (E : (LW[ [(i, n, m i n)] :: 
                             (⨁_{ list_enum n} (λ q : nat, ltr_extend_paths (i, q, m i q) (if q =n?= j then oneP else zeroP))) ])
                      =r= 
                      ( (lw [(i, n, m i n)]) +  
                         LW[ ⨁_{ list_enum n} (λ q : nat, ltr_extend_paths (i, q, m i q) (if q =n?= j then oneP else zeroP)) ])).
        {
          apply big_plus_set_cons; auto.
          assert (F : in_set eq_weighted_path
                        (⨁_{ list_enum n} (λ q : nat, ltr_extend_paths (i, q, m i q) (if q =n?= j then oneP else zeroP)))
                        [(i, n, m i n)] = false).
          {
            admit. 
          }
          exact F. 
        }
        assert (F := trnR _ _ _ D E). 
        assert (G := trnR _ _ _ B F).
        assert (H : (LW[ ⨁_{ list_enum n} (λ q : nat, ltr_extend_paths (i, q, m i q) (if q =n?= j then oneP else zeroP))])
                    =r=
                      (⨁_( list_enum n) (λ q : nat, m i q |> (if q =n?= j then 1 else 0)))).
        {
          apply IHn. 
        }
        assert (I : (lw [(i, n, m i n)]) =r= (m i n |> 1)).
        {
          compute. apply refR. 
        } 
        assert (J := congrP _ _ _ _ I H).
        assert (K := trnR _ _ _ G J). apply symR in A.
        exact (trnR _ _ _ K A).
      + simpl in B. unfold ltr_extend_path in B. unfold path_adjacency_arcs in B.
        apply LW_congruence in B; auto.
        assert (D : ([] +P (⨁_{ list_enum n} (λ q : nat, ltr_extend_paths (i, q, m i q) (if q =n?= j then oneP else zeroP))))
                    =PS=
                    (⨁_{ list_enum n} (λ q : nat, ltr_extend_paths (i, q, m i q) (if q =n?= j then oneP else zeroP))) = true ). 
        {
          apply bop_union_with_nil_left.
          apply eq_weighted_path_reflexive.
          apply eq_weighted_path_symmetric.
          apply eq_weighted_path_transitive. 
        }
        apply LW_congruence in D; auto.
        assert (E := trnR _ _ _ B D).
        assert (F : (m i n |> 0) =r= 0). apply ann.
        assert (G := congrP _ _ _ _ F (refR (⨁_( list_enum n) (λ q : nat, m i q |> (if q =n?= j then 1 else 0))))).
        assert (H := trnR _ _ _ A G).
        assert (I : (0 + (⨁_( list_enum n) (λ q : nat, m i q |> (if q =n?= j then 1 else 0))))
                    =r=
                      (⨁_( list_enum n) (λ q : nat, m i q |> (if q =n?= j then 1 else 0)))).
        apply id.
        assert (J := trnR _ _ _ H I). apply symR in J.
        assert (K : (LW[ ⨁_{ list_enum n} (λ q : nat, ltr_extend_paths (i, q, m i q) (if q =n?= j then oneP else zeroP))])
                    =r=
                      (⨁_( list_enum n) (λ q : nat, m i q |> (if q =n?= j then 1 else 0)))).
        {
          apply IHn. 
        }
        assert (N := trnR _ _ _ E K).
        exact (trnR _ _ _ N J). 
    Admitted.   

    Lemma IP_diag : ∀ i j : nat, i =n= j → ([IP]) i j = [[]].
    Proof. intros i j A. unfold matrix_mul_identity.
           rewrite A. reflexivity. 
    Qed. 

    Lemma nil_in_IP : ∀ i j : nat, [] [in set] ([IP]) i j → i =n= j.
    Proof. intros i j. unfold matrix_mul_identity.
           case_eq(i =n?= j); intros A B; auto.
           compute in B. discriminate B. 
    Qed. 
    
  Lemma LWP_distributes_over_left_exponentiation
       (id : bop_is_id R eqR plus 0)       
       (ann : ltr_is_ann L R eqR ltr 0)
       (assoc : bop_associative R eqR plus)
       (comm : bop_commutative R eqR plus) 
       (LD : slt_distributive eqR plus ltr) 
        (m : functional_matrix L) (n : nat)
        (cL : CongL m) : 
       ∀ k, LWP[ A[ m ] *[| n |]> (Pk[ m , k, n ]) ] =M= (m *[ n ]> LWP[ Pk[ m , k, n ] ]).
  Proof. induction k. 
         + (* (LWP[ (A[ m]) *[| n |]> (Pk[ m, 0, n ])]) 
               =M=
              (m *[ n ]> (LWP[ Pk[ m, 0, n ]]))
            *)
           unfold matrix_of_k_length_paths. simpl.
           (* (LWP[ (A[ m]) *[| n |]> ([IP])]) 
              =M= 
              (m *[ n ]> (LWP[ [IP]]))
            *)
           assert (C: CongR (LWP[ [IP] ])).
           {
             apply LWP_IP_congruence; auto. 
           }
           assert (A := LWP_distributes_over_left_exponentiation_base_case id ann assoc comm LD m cL n).
           assert (B : (m *[ n ]> LWP[ [IP]]) =M= (m *[ n ]> [I])).
           {
             exact (congrM_right n m _ _ cL C (LWP_of_path_identity_is_identity id)).
           }
           apply matrixR_equality_symmetric in B. 
           exact (matrixR_equality_transitive _ _ _ A B). 
         + (*  IHk : (LWP[ (A[ m]) *[| n |]> (Pk[ m, k, n ])]) 
                     =M=
                     (m *[ n ]> (LWP[ Pk[ m, k, n ]]))
               ============================
               (LWP[ (A[ m]) *[| n |]> (Pk[ m, S k, n ] )]) 
               =M=
               (m *[ n ]> (LWP[ Pk[ m, S k, n ]]))
           
               Proof: 
               LWP[ (A[ m]) *[| n |]> (Pk[ m, S k, n ])]
               =M= {unfold_Pk, congr} 
               LWP[ (A[ m]) *[| n |]> (A[ m ] *[| n |]> (Pk[ m , k, n ]))]
               =M={LWP_distributes_over_left_matrix_mul} 
               (m *[ n ]> LWP[ (A[ m ] *[| n |]> (Pk[ m , k, n ])) ])
               =M= {IHk, congr} 
               (m *[ n ]> (m *[ n ]> (LWP[ Pk[ m, k, n ]]))
               =M= {LWP_distributes_over_left_matrix_mul, congr}
               (m *[ n ]> (LWP[ A[ m ] *[| n |]> (Pk[ m , k, n ]  ]))
               =M= {unfold_Pk, congr}
               (m *[ n ]> (LWP[ Pk[ m, S k, n ]]))
            *)
           assert (A : LWP[ A[ m ] *[| n |]> Pk[ m, S k, n ]]
                       =M=
                       LWP[ A[ m ] *[| n |]> A[ m ] *[| n |]> Pk[ m , k, n ]]).
           {
                apply LWP_congruence; auto. 
                apply congrPM_right; auto.
                + apply adjacency_congruence; auto. 
                + apply Pk_preserves_congruence; auto. 
                + apply unfold_Pk.
           }
           assert (B : LWP[ A[ m ] *[| n |]> A[ m ] *[| n |]> Pk[ m , k, n ]]
                          =M=
                          (m *[ n ]> LWP[ A[ m ] *[| n |]> Pk[ m , k, n ]])).
           {
             apply LWP_distributes_over_left_matrix_mul; auto.
           }
           assert (C : (m *[ n ]> LWP[ A[ m ] *[| n |]> Pk[ m , k, n ] ])
                          =M=
                          (m *[ n ]> (m *[ n ]> (LWP[ Pk[ m, k, n ]])))).
              {
                 apply congrM_right; auto.
                 apply LWP_preserves_congruence; auto. 
                 apply path_left_matrix_mul_preserves_congruence; auto.
                 apply Pk_preserves_congruence; auto.
              }
            assert (D : (m *[ n ]> (m *[ n ]> (LWP[ Pk[ m, k, n ]])))
                             =M=
                             (m *[ n ]> (LWP[ A[ m ] *[| n |]> (Pk[ m , k, n ]) ] ))).
              {
                apply congrM_right; auto.
                + apply left_matrix_mul_preserves_congruence; auto.
                  apply LWP_preserves_congruence; auto. 
                  apply Pk_preserves_congruence; auto.                 
                + apply matrixR_equality_symmetric.
                  apply LWP_distributes_over_left_matrix_mul; auto.
              }
            assert (E : (m *[ n ]> (LWP[ A[ m ] *[| n |]> (Pk[ m , k, n ]) ] ))
                             =M=
                             (m *[ n ]> (LWP[ Pk[ m, S k, n ]]))).
              {
                    apply congrM_right; auto.
                    + apply LWP_preserves_congruence; auto.
                      apply path_left_matrix_mul_preserves_congruence; auto.
                      apply Pk_preserves_congruence; auto.                     
                    + apply LWP_congruence; auto.
                      apply unfold_Pk.
              }
                 exact (matrixR_equality_transitive _ _ _
                          (matrixR_equality_transitive _ _ _
                             (matrixR_equality_transitive _ _ _
                               (matrixR_equality_transitive _ _ _ A B) C) D) E). 
  Qed. 

  Lemma  base_case_of_fundamental_theorem_on_paths_of_length_k
       (id : bop_is_id R eqR plus 0)       
       (ann : ltr_is_ann L R eqR ltr 0)
       (assoc : bop_associative R eqR plus)
       (LD : slt_distributive eqR plus ltr)        
         (comm : bop_commutative R eqR plus) :
        ∀ m n, LWP[ Pk[ m, 1, n ] ] =M= ((m *[ n ]> LWP[ Pk[ m, 0, n ] ])).
  Proof. intros m n. 
         unfold matrix_of_k_length_paths.         
         unfold left_matrix_exponentiation.
         apply LWP_distributes_over_left_matrix_mul; auto.
  Qed.

  Theorem fundamental_theorem_on_paths_of_length_k
         (assoc : bop_associative R eqR plus)
         (comm : bop_commutative R eqR plus)
         (ann : ltr_is_ann L R eqR ltr 0)         
         (plusID : bop_is_id R eqR plus 0)
         (LD : slt_distributive eqR plus ltr)                 
         (m : functional_matrix L) (cL : CongL m) (n : nat) : 
    ∀ k, LWP[ Pk[ m , k + 1, n ] ]
          =M=
          (m *[ n ]> (LWP[ Pk[ m , k, n] ])). 
  Proof. induction k.
         + apply base_case_of_fundamental_theorem_on_paths_of_length_k; auto. 
         + (* Show: 
             IHk : (LWP[ Pk[ m, k + 1, n ]])  =M= (m *[ n ]> (LWP[ Pk[ m, k, n ]]))
             ============================
             (LWP[ Pk[ m, (S k) + 1, n ]])  =M= (m *[ n ]> (LWP[ Pk[ m, S k, n ]]))

             Proof: 
             LWP[ Pk[ m, (k + 1) + 1, n ]]
             = {unfold_left_matrix_exponentiation} 
             LWP[ (A[ m ] *[| n |]> (Pk[ m , k + 1, n ]))]
             = {LWP_distributes_over_left_exponentiation, congruence}
             (m *[ n ]> (LWP[ Pk[ m, k + 1, n ]]))
            *)
           assert (B : LWP[ Pk[ m, (S k) + 1, n ]]
                       =M=
                       LWP[ (A[ m ] *[| n |]> (Pk[ m , S k, n ])) ]).
               assert (C := unfold_Pk m n (S k)).             
               apply LWP_congruence; auto. 
               assert (D : S (S k) = ((S k) + 1)%nat). 
                  assert (E := theory.plus_SS k 0).
                  rewrite <- plus_n_O in E.
                  rewrite E. reflexivity. 
               rewrite D in C. exact C. 
           assert (D : LWP[   (A[ m ] *[| n |]> (Pk[ m , S k, n ]))   ] 
                       =M=
                       (m *[ n ]> (LWP[ Pk[ m, S k, n ]]))).
              apply LWP_distributes_over_left_exponentiation; auto. 
           exact (eq_functional_matrix_prop_transitive _ eqR trnR _ _ _ B D).
  Qed.


  (*************************************************************************************************************)
  (*************************************************************************************************************)  
  (*************************************************************************************************************)

  Definition left_sum_of_path_powers
             (n : nat)
             (m : functional_matrix L)
             (k : nat) : functional_matrix (weighted_path_set) :=
       left_sum_of_matrix_powers_general n (zeroP) (oneP) (plusP) (ltr_extend_paths) (path_adjacency_arcs m) k. 


  Local Notation "Mk[ m , k , n ]"   := (left_matrix_exponentiation zero one plus ltr n m k) (at level 70).
  Local Notation "Mk{ m , k , n }"   := (left_sum_of_matrix_powers_general n zero one plus ltr m k) (at level 70).  
  Local Notation "Mk<{ m , k , n }>" := (left_matrix_iteration zero one plus ltr n m k) (at level 70).


  Local Notation "Pk{ m , k , n }"   := (left_sum_of_path_powers n m k) (at level 70).
  Local Notation "Pk<{ m , k , n }>" := (left_matrix_iteration (zeroP R) (oneP R) (plusP R) (ltr_extend_paths R) n m k) (at level 70).

  
  (*  Main theorems below 

  matrix_path_equation
  ∀n k,  Mk[m, k, n] =M= LWP[ Pk[ m , k, n ] ].

  left_sum_of_matrix_powers_is_equal_to_left_matrix_iteration
  ∀ k, Mk{ m, k , n } =M= Mk<{ m, k , n }>. 

  powers
  ∀ k, Mk[ m +M [I], k , n ] =M= Mk{ m, k, n}.

  left_sum_of_matrix_powers_to_k_is_equal_to_weight_of_paths_of_length_at_most_k
  ∀ k, Mk{ m, k , n } =M= LWP[ Pk{ m , k , n } ].
  *) 
    Lemma matrix_exp_preserves_congruence : ∀ m,  CongL m → ∀ n k, CongR (Mk[ m, k, n]).
    Proof. intros m cong n k. 
           induction k; simpl.
           + apply (matrix_mul_identity_congruence R eqR refR).
           + apply left_matrix_mul_preserves_congruence; auto.
    Qed.
    
    Lemma left_sum_of_matrix_powers_congruence : ∀ m,  CongL m → ∀ n k, CongR (Mk{ m, k, n}).
    Proof. intros m cong n k. 
           induction k; simpl.
           + unfold left_sum_of_matrix_powers.
             unfold left_sum_of_matrix_powers_general.
             apply (matrix_mul_identity_congruence R eqR refR).
           + apply matrix_add_preserves_congruence; auto.
             apply left_matrix_mul_preserves_congruence; auto.
             apply matrix_exp_preserves_congruence; auto. 
    Qed.


  (* move this ? 
  Lemma bop_congruence_implies_ltr_congruence : ltr_congruence R R eqR eqR mul. 
  Proof. intros a b c d. apply congrM. Qed. 
   *)
    
  Lemma matrix_path_equation
        (plus_commutative  : bop_commutative R eqR plus)
        (plus_associative : bop_associative R eqR plus)
        (plusID : bop_is_id R eqR plus 0)
        (ann : ltr_is_ann L R eqR ltr 0)
        (assoc : bop_associative R eqR plus)
        (LD : slt_distributive eqR plus ltr)        
        (m : functional_matrix L) (cong : CongL m) :
    ∀n k,  Mk[m, k, n] =M= LWP[ Pk[ m , k, n ] ].
  Proof. intros n k. induction k; simpl. 
         + apply identity_is_weight_of_matrix_of_paths_of_length_zero; auto.
         + assert (A := fundamental_theorem_on_paths_of_length_k plus_associative plus_commutative ann plusID LD m cong n k).
           assert (B : (m *[ n ]> (Mk[m, k, n])) =M= (m *[ n ]> (LWP[ Pk[ m, k, n ] ])) ).
              apply (left_matrix_mul_congruence _ _ eqL eqR); auto.
              apply matrix_exp_preserves_congruence; auto. 
              apply eq_functional_matrix_prop_reflexive; auto. 
           apply eq_functional_matrix_prop_symmetric in A; auto.
           assert (C := eq_functional_matrix_prop_transitive _ _ trnR _ _ _ B A). 
           assert (D : S k = (k + 1)%nat). (* Ugh!!! *) 
              assert (E := plus_n_Sm k 0).
              rewrite PeanoNat.Nat.add_0_r in E.
              exact E. 
           rewrite D. exact C. 
  Qed. 
  
  (* move this? *) 
  Lemma unfold_left_matrix_iteration(n : nat) (m : functional_matrix L) :
    ∀ k, Mk<{ m, S k, n }> =M= ((m *[ n ]> (Mk<{ m, k, n }>)) +M ([I])). 
  Proof. intro k. simpl. 
         apply eq_functional_matrix_prop_reflexive; auto.
  Qed.
  
  Lemma unfold_left_sum_of_matrix_powers (n : nat) (m : functional_matrix L) :
    ∀ k, Mk{ m, S k, n} =M= Mk{ m, k, n} +M Mk[m, S k, n].
  Proof. intro k. unfold left_sum_of_matrix_powers.
         unfold left_sum_of_matrix_powers_general. simpl.
         apply eq_functional_matrix_prop_reflexive; auto.
  Qed.

  Lemma unfold_left_sum_of_path_powers (n : nat) (m : functional_matrix L) :
    ∀ k, Pk{ m, S k, n} =PM= (Pk{ m, k, n} +PM Pk[m, S k, n]).
  Proof. intro k. unfold left_sum_of_path_powers.
         unfold left_sum_of_matrix_powers_general. simpl.
         apply eq_functional_matrix_prop_reflexive; auto.
         apply eq_weighted_path_set_reflexive; auto. 
  Qed.

  Lemma shift_left_sum_of_matrix_powers
        (assoc : bop_associative R eqR plus) 
        (comm: bop_commutative R eqR plus)
        (plusID : bop_is_id R eqR plus 0)
        (LD : slt_distributive eqR plus ltr) 
        (n : nat) (m : functional_matrix L) (cong : CongL m) :
           ∀ k, Mk{ m, S k, n} =M= ((m *[ n ]> Mk{ m, k, n}) +M [I]).
  Proof. induction k.     
         + unfold left_sum_of_matrix_powers. simpl.
           apply matrix_add_comm; auto. 
         + (* IHk : (Mk{ m, S k, n}) =M= ((m *[ n ]> (Mk{ m, k, n})) +M ([I]))
              ============================
              (Mk{ m, S (S k), n}) =M= ((m *[ n ]> (Mk{ m, S k, n})) +M ([I]))

             Proof: 
             Mk{ m, S (S k), n}) 
             =M= {unfold_left_sum_of_matrix_powers }
             Mk{ m, S k, n} +M Mk[m, S (S k), n]
             =M= {IHk, unfold_left_matrix_exponentiation, +M congruence} 
             (m *[ n ]>Mk{ m, k, n} +M [I]) +M (m *[ n ]> Mk[m, S k, n])
             =M={+M assoc, commutative}
             (m *[ n ]> Mk{ m, k, n} +M (m *[ n ]> Mk[m, S k, n])) +M [I]
             =M={*M assoc distributes over +M}
             (m *[ n ]> (Mk{ m, k, n} +M Mk[m, S k, n])) +M [I]
             =M= {unfold_left_sum_of_matrix_powers} 
             ((m *[ n ]> (Mk{ m, S k, n})) +M ([I]))             
            *)
           assert (A := unfold_left_sum_of_matrix_powers n m (S k)).
           assert (B : ((Mk{ m, S k, n}) +M (Mk[ m, S (S k), n]))
                       =M=
                       (((m *[ n ]> (Mk{ m, k, n})) +M ([I]))
                        +M
                       ((m *[ n ]> Mk[ m, S k, n])))).
              apply matrix_add_congruence; auto. 
              apply unfold_left_matrix_exponentiation; auto. 
           assert (C : (((m *[ n ]> (Mk{ m, k, n})) +M ([I]))
                        +M
                       ((m *[ n ]> Mk[ m, S k, n])))
                       =M=
                       (((m *[ n ]> (Mk{ m, k, n})) +M ((m *[ n ]> Mk[ m, S k, n])))
                        +M
                        ([I]))).
              assert (C1 : (((m *[ n ]> (Mk{ m, k, n})) +M ([I])) +M (m *[ n ]> (Mk[ m, S k, n])))
                         =M=
                        ((m *[ n ]> (Mk{ m, k, n})) +M (([I]) +M (m *[ n ]> (Mk[ m, S k, n]))))).
                   apply matrix_add_assoc;auto. 
              assert(C2 : ((m *[ n ]> (Mk{ m, k, n})) +M (([I]) +M (m *[ n ]> (Mk[ m, S k, n]))))
                           =M= 
                           ((m *[ n ]> (Mk{ m, k, n})) +M ((m *[ n ]> (Mk[ m, S k, n])) +M ([I])))). 
                 apply matrix_add_congruence; auto.
                 apply matrixR_equality_reflexive.
                 apply matrix_add_comm; auto.                   
              assert (C3 : ((m *[ n ]> (Mk{ m, k, n})) +M ((m *[ n ]> (Mk[ m, S k, n])) +M ([I])))
                           =M=
                           (((m *[ n ]> (Mk{ m, k, n})) +M (m *[ n ]> (Mk[ m, S k, n]))) +M ([I]))).
                 apply matrixR_equality_symmetric. 
                 apply matrix_add_assoc;auto. 
              exact (trnM _ _ _ (trnM _ _ _ C1 C2) C3).
           assert (D : (((m *[ n ]> (Mk{ m, k, n})) +M ((m *[ n ]> Mk[ m, S k, n])))
                        +M
                       ([I]))
                       =M=
                       ((m *[ n ]> (Mk{ m, k, n} +M Mk[ m, S k, n]))
                        +M
                       ([I]))).
              apply matrix_add_congruence; auto.
              apply eq_functional_matrix_prop_symmetric; auto.
              apply left_matrix_left_mul_left_distributive_over_matrix_add; auto. 
              apply eq_functional_matrix_prop_reflexive; auto.
           assert (E : ((m *[ n ]> (Mk{ m, k, n} +M Mk[ m, S k, n]))
                        +M
                       ([I]))
                       =M=
                       ((m *[ n ]> Mk{ m, S k, n})
                        +M
                       ([I]))).
              apply matrix_add_congruence; auto.
              apply (left_matrix_mul_congruence L R eqL eqR plus zero ltr); auto.           
              apply matrix_add_preserves_congruence; auto.
              apply left_sum_of_matrix_powers_congruence; auto. 
              apply matrix_exp_preserves_congruence; auto. 
              apply eq_functional_matrix_prop_reflexive; auto.
              apply eq_functional_matrix_prop_symmetric; auto.
              apply unfold_left_sum_of_matrix_powers.
              apply eq_functional_matrix_prop_reflexive; auto.              
          apply (trnM _ _ _ A (trnM _ _ _ B (trnM _ _ _ C (trnM _ _ _ D E)))). 
  Qed. 
  
  Lemma left_sum_of_matrix_powers_is_equal_to_left_matrix_iteration
        (comm: bop_commutative R eqR plus)
        (assoc : bop_associative R eqR plus)
        (plusID : bop_is_id R eqR plus 0)
        (LD : slt_distributive eqR plus ltr) 
        (n : nat) (m : functional_matrix L) (cong : CongL m) :
           ∀ k, Mk{ m, k , n } =M= Mk<{ m, k , n }>. 
  Proof. induction k.     
         + simpl. apply eq_functional_matrix_prop_reflexive; auto.
         + (* Show : 
              IHk : Mk{ m, k, n} =M= Mk<{ m, k, n }>
              ============================
              Mk{ m, S k, n} =M= Mk<{ m, S k, n }>

              Proof: 
              Mk{ m, S k, n} 
              =M={shift_left_sum_of_matrix_powers}              
              (m *[ n ]> Mk{ m, k, n}) +M [I] 
              =M={IHk, congruence}              
              (m *[ n ]> Mk<{ m, k, n }>) +M [I] 
              =M={unfold_left_matrix_iteration}
              Mk<{ m, S k, n }>
            *)
           assert (A := shift_left_sum_of_matrix_powers assoc comm plusID LD n m cong k).
           assert (B : ((m *[ n ]> (Mk{ m, k, n})) +M ([I]))
                       =M=
                       ((m *[ n ]> (Mk<{ m, k, n }>)) +M ([I]))).
              assert (C : (m *[ n ]> Mk{ m, k, n}) =M= (m *[ n ]> (Mk<{ m, k, n }>))).
                 apply (left_matrix_mul_congruence L R eqL eqR plus zero ltr); auto.
                 apply left_sum_of_matrix_powers_congruence; auto.
                 apply eq_functional_matrix_prop_reflexive; auto. 
              apply matrix_add_congruence; auto.
              apply eq_functional_matrix_prop_reflexive; auto. 
           assert (C : ((m *[ n ]> (Mk<{ m, k, n }>)) +M ([I]))
                       =M=
                       Mk<{ m, S k, n }>).
              apply eq_functional_matrix_prop_symmetric; auto. 
              apply unfold_left_matrix_iteration. 
              exact (trnM _ _ _ (trnM _ _ _ A B) C).
  Qed. 

  
  Lemma  base_case (plusID : bop_is_id R eqR plus 0) (n : nat) (m : functional_matrix L) :
    Mk{ m, 0, n} =M= LWP[ Pk{ m, 0, n}]. 
  Proof. unfold left_sum_of_path_powers, left_sum_of_matrix_powers.
         apply eq_functional_matrix_prop_symmetric; auto.
         apply LWP_of_path_identity_is_identity; auto. 
  Qed.          
  
  Lemma left_sum_of_matrix_powers_to_k_is_equal_to_weight_of_paths_of_length_at_most_k
        (plus_associative : bop_associative R eqR plus)
        (plus_commutative  : bop_commutative R eqR plus)
        (plusID : bop_is_id R eqR plus 0)
        (ann : ltr_is_ann L R eqR ltr 0)
        (LD : slt_distributive eqR plus ltr) 
        (n : nat) (m : functional_matrix L) (cong : CongL m):
           ∀ k, Mk{ m, k , n } =M= LWP[ Pk{ m , k , n } ].
  Proof. induction k; simpl.
         + (* Mk{ m, 0, n} =M= LWP[ Pk{ m, 0, n}] *) 
           apply base_case; auto. 
         + (*
            IHk : (Mk{ m, k, n}) =M= (LWP[ Pk{ m, k, n}])
            ============================
            (Mk{ m, S k, n}) =M= (LWP[ Pk{ m, S k, n}])

            Proof: 
            Mk{ m, S k, n}
            =M= {unfold_left_sum_of_matrix_powers} 
            Mk{ m, k, n} +M Mk[ m, S k, n]
            =M= {IHk, congruence} 
            LWP[ Pk{ m, k, n} ] +M Mk[ m, S k, n]
            =M={matrix_path_equation, congruence} 
            LWP[ Pk{ m, k, n} ] +M LWP[ Pk[ m, S k, n] ] 
            =M={LWP_distributes_over_matrix_add} 
            LWP[ Pk{ m, k, n} +PM Pk[ m, S k, n] ] 
            =M= {unfold_left_sum_of_path_powers, congruence}
            LWP[ Pk{ m, S k, n}]
           *)
           assert (A := unfold_left_sum_of_matrix_powers n m k).
           assert (B : (Mk{ m, k, n} +M Mk[ m, S k, n])
                       =M= 
                       (LWP[ Pk{ m, k, n}] +M Mk[ m, S k, n])). 
              apply matrix_add_congruence; auto. 
              apply eq_functional_matrix_prop_reflexive; auto. 
           assert (C : (LWP[ Pk{ m, k, n}] +M Mk[ m, S k, n])
                       =M=
                       (LWP[ Pk{ m, k, n} ] +M LWP[ Pk[ m, S k, n] ])).
              apply matrix_add_congruence; auto. 
              apply eq_functional_matrix_prop_reflexive; auto.
              apply matrix_path_equation; auto.
           assert (D : (LWP[ Pk{ m, k, n} ] +M LWP[ Pk[ m, S k, n] ])
                       =M=                 
                       (LWP[ Pk{ m, k, n} +PM Pk[ m, S k, n] ])).
             apply eq_functional_matrix_prop_symmetric; auto.
             apply LWP_distributes_over_matrix_add; auto.  
           assert (E := unfold_left_sum_of_path_powers n m k).
           assert (F : (LWP[ Pk{ m, k, n} +PM Pk[ m, S k, n] ])
                       =M=
                       LWP[ Pk{ m, S k, n} ]).
              apply LWP_congruence; auto.  
           exact (trnM _ _ _ (trnM _ _ _ (trnM _ _ _ (trnM _ _ _ A B) C) D) F).
  Qed.

     (******* matrix of elementary paths ****************************************)   
     (******* matrix of elementary paths ****************************************)   
     (******* matrix of elementary paths ****************************************)   
   Definition ltr_extend_elementary_path : ltr_type weighted_arc weighted_path :=
     fun a => fun p =>
                match p with
                | nil => if (arc_source a) =n?= (arc_target a) then nil else  a :: nil
                | _   => a :: p 
                end. 

   Fixpoint is_elementary_weighted_path (p : weighted_path) : bool :=
     match p with
     | [] => true
     | (a, b, w) :: rest => bop_and (negb (a =n?= b))
                                 (bop_and (negb (in_list brel_eq_nat (List.map arc_target rest) a))
                                          (is_elementary_weighted_path rest)) 
     end. 

   Definition ltr_extend_elementary_paths : ltr_type weighted_arc weighted_path_set :=
       fun a (X : weighted_path_set) =>
         List.filter is_elementary_weighted_path (List.map (ltr_extend_elementary_path a) X).
   
   Definition matrix_of_elementary_paths_length_k_or_less m n k :=
     left_matrix_exponentiation zeroP oneP plusP ltr_extend_elementary_paths n (path_adjacency_arcs m) k.

   Local Notation "PEk[ m , k , n ]"  := (matrix_of_elementary_paths_length_k_or_less m n k) (at level 70).

   Local Infix "*[E n E]>" := (left_matrix_mul zeroP plusP ltr_extend_elementary_paths n) (at level 70).

   Lemma unfold_PEk (m : functional_matrix L) (n : nat) : 
     ∀ k, PEk[ m, S k, n ] =PM= (A[ m ] *[E n E]> (PEk[ m , k, n ])). 
   Proof. intro k. unfold matrix_of_elementary_paths_length_k_or_less.
          exact (unfold_left_matrix_exponentiation _ _
                    eq_weighted_path_set
                    plusP
                    zeroP
                    oneP
                    ltr_extend_elementary_paths
                    eq_weighted_path_set_reflexive
                    (A[ m ])
                    n
                    k).
   Qed.

   Lemma extend_elementary_path (i j : nat) (v : L): 
     ∀ p, is_elementary_weighted_path (ltr_extend_elementary_path (i, j, v) p) = true -> 
          ltr_extend_path (i, j, v) p = ltr_extend_elementary_path (i, j, v) p.
   Admitted.
   (*
   Proof. induction p; intro H. 
          + unfold ltr_extend_path.
            unfold ltr_extend_elementary_path. 
            unfold arc_source, arc_target. reflexivity. 
          +  destruct a as [i' j' v'].
             simpl. 
             reflexivity. 
   Qed. 
     *)        
   Lemma key_lemma
         (i j : nat) (v : L): 
     ∀ X,
         (map lw (map (ltr_extend_path (i, j, v)) X))
         =vl=
         (map lw (List.filter is_elementary_weighted_path
             (map (ltr_extend_elementary_path (i, j, v)) X)))
         . 
     Proof. induction X. 
            + compute. reflexivity. 
            + simpl.
              case_eq(is_elementary_weighted_path (ltr_extend_elementary_path (i, j, v) a)); intro A.
              ++ rewrite (extend_elementary_path i j v a A).
                 apply brel_list_cons_intro.
                 +++ apply refR.
                 +++ exact IHX. 
              ++ admit.
Admitted.                  
              
Lemma lemma_fold_right_with_map_ELEMENTARY 
       (m : functional_matrix L) (n : nat)
       (id : bop_is_id R eqR plus 0)       
       (ann : ltr_is_ann L R eqR ltr 0)
       (assoc : bop_associative R eqR plus)       
       (LD : slt_distributive eqR plus ltr) 
       (X : nat -> weighted_path_set)
       (i : nat) : ∀ l,        
  fold_right plus 0
     (map lw
        (fold_right plusP zeroP
             (map (λ q : nat,
                List.filter is_elementary_weighted_path                                
                  (map (ltr_extend_elementary_path (i, q, m i q)) (X q))) l)))
   =r=
   fold_right plus 0
     (map (λ q : nat, m i q |> fold_right plus 0 (map lw (X q))) l).
Admitted.
(*
 Proof.  induction l.         
         + compute. apply refR. 
         + simpl.       
           rewrite map_app. 
           rewrite fold_right_app.
           assert (A := technical_lemma
                         (fold_right plus 0
                                     (map lw
                                          (fold_right plusP zeroP
                                                      (map
                                                         (λ q : nat,
                                                                List.filter is_elementary_weighted_path
                                                                            (map (ltr_extend_elementary_path (i, q, m i q)) (X q)))
                                                         l))))
                    i a m id ann assoc LD (X a)
                  ).
           assert (B := congrP _ _ _ _
                           (refR (m i a |> fold_right plus 0 (map lw (X a))))
                           (symR _ _ IHl)).
(*


  C : (fold_right plus
         (fold_right plus 0
            (map lw
               (fold_right plusP zeroP
                  (map
                     (λ q : nat,
                        List.filter is_elementary_weighted_path
                          (map (ltr_extend_elementary_path (i, q, m i q)) (X q))) 
                     l))))

---------------------------
         (map lw (map (ltr_extend_path (i, a, m i a)) (X a))) 
---------------------------
    =r?=

    (m i a |> fold_right plus 0 (map lw (X a))) +
    fold_right plus 0
     (map (λ q : nat, m i q |> fold_right plus 0 (map lw (X q))) l)) =
      true
  ============================
  fold_right plus
    (fold_right plus 0
       (map lw
          (fold_right plusP zeroP
             (map
                (λ q : nat,
                   List.filter is_elementary_weighted_path
                     (map (ltr_extend_elementary_path (i, q, m i q)) (X q)))
                l))))

---------------------------
    (map lw
       (List.filter is_elementary_weighted_path
          (map (ltr_extend_elementary_path (i, a, m i a)) (X a)))) 
---------------------------
  =r=

  (m i a |> fold_right plus 0 (map lw (X a))) +
  fold_right plus 0
    (map (λ q : nat, m i q |> fold_right plus 0 (map lw (X q))) l)

 *)
           (* assert (C := trnR _ _ _ A (symR _ _ B)). *) 
           (*exact (trnR _ _ _ A (symR _ _ B)).*) 
Admitted. 
*) 

    Lemma LWP_distributes_over_left_matrix_mul_ELEMENTARY 
       (id : bop_is_id R eqR plus 0)       
       (ann : ltr_is_ann L R eqR ltr 0)
       (assoc : bop_associative R eqR plus)       
       (LD : slt_distributive eqR plus ltr) 
       (m : functional_matrix L) (n : nat) (P : functional_matrix weighted_path_set) : 
          LWP[ A[ m ] *[E n E]> P ] =M= (m *[ n ]> LWP[ P ]).
      Proof. intros i j.
         unfold left_matrix_mul.
         unfold left_row_i_dot_col_j.
         unfold ltr_extend_elementary_paths.
         unfold big_plus. 
         unfold path_adjacency_arcs.
         (* exact (lemma_fold_right_with_map_ELEMENTARY  m n id ann assoc LD (fun (q : nat) => P q j) i (list_enum n)). *) 
Admitted. 

    Lemma tmp_base_case
     (m : functional_matrix L) (n : nat) :           
    ((LWP[ [IP]]) +M (LWP[ (A[ m]) *[| n |]> ([IP])]))
    =M=
    (m *[ n ]> (LWP[ [IP]])). 
    Proof. intros i j. unfold matrix_add. 
    Admitted.

    Lemma needed_lemma
       (m : functional_matrix L) (n : nat) : 
       ∀ k,           
            (m *[ n ]> (LWP[ PEk[ m, k, n] ]))
            =M= 
            LWP[ PEk[ m, S k, n] ]. 
    Proof. induction k.
           + unfold matrix_of_elementary_paths_length_k_or_less; simpl.
             admit. (* (m *[ n ]> (LWP[ [IP]])) =M= (LWP[ (A[ m]) *[E n E]> ([IP])])  *) 
           + (*

             IHk : (m *[ n ]> (LWP[ PEk[ m, k, n]]))
                   =M=
                   LWP[ PEk[ m, S k, n]]
                   ============================
                   (m *[ n ]> (LWP[ PEk[ m, S k, n]])) 
                   =M= 
                   (LWP[ PEk[ m, S (S k), n]])

             Proof: 
                   (m *[ n ]> (LWP[ PEk[ m, S k, n]])) 
                   =M={unfold_PEk} 
                   (m *[ n ]> (LWP[ A[ m ] *[E n E]> (PEk[ m , k, n ]) ])) 
                   =M={dist LWP} 
                   (m *[ n ]> (m *[ n ]> LWP[ PEk[ m , k, n ] ]))`
                   =M={IHk} 
                   (m *[ n ]> LWP[ PEk[ m, S k, n]])
                   =M= {unfold_PEk) 
                   (LWP[ PEk[ m, S (S k), n]])

             *) 
    Admitted.
    
    Lemma tmp
     (m : functional_matrix L) (n : nat) : 
     ∀ k,           
      ((LWP[ PEk[ m, k, n]]) +M (LWP[ Pk[ m, S k, n]]))
      =M= 
      (m *[ n ]> (LWP[ PEk[ m, k, n]])).
      Proof. induction k. 
             + unfold matrix_of_elementary_paths_length_k_or_less; simpl. 
               unfold matrix_of_k_length_paths; simpl. 
               apply tmp_base_case.
             + (*
                 IHk : ((LWP[ PEk[ m, k, n]]) +M (LWP[ Pk[ m, S k, n]])) 
                       =M=
                       (m *[ n ]> (LWP[ PEk[ m, k, n]]))
                      ============================
                      ((LWP[ PEk[ m, S k, n]]) +M (LWP[ Pk[ m, S (S k), n]])) 
                      =M=
                      (m *[ n ]> (LWP[ PEk[ m, S k, n]]))

                      Proof: 
                      ((LWP[ PEk[ m, S k, n]]) +M (LWP[ Pk[ m, S (S k), n]])) 
                      =M= {unfolding, congruence}
                      ((LWP[ A[ m ] *[E n E]> (PEk[ m , k, n ]) ]) 
                       +M 
                      (LWP[ A[ m ] *[| n |]> (Pk[ m , S k, n ]) ])) 
                      =M= {distribute LWP} 
                      (m *[ n ]> LWP[ PEk[ m , k, n ] ])
                       +M 
                      (m *[ n ]> LWP[ Pk[ m , S k, n ] ] 
                      =M= {left_distribute} 
                      (m *[ n ]> (LWP[ PEk[ m , k, n ] ] +M LWP[ Pk[ m , S k, n ] ])
                      =M= {IHk} 
                      (m *[ n ]> (m *[ n ]> (LWP[ PEk[ m, k, n]]))
                      =M= {NEED A LEMMA} 
}                      (m *[ n ]> (LWP[ PEk[ m, S k, n]]))
               *)
      Admitted.
      
    Lemma conjecture
       (id : bop_is_id R eqR plus 0)       
       (ann : ltr_is_ann L R eqR ltr 0)
       (assoc : bop_associative R eqR plus)       
       (LD : slt_distributive eqR plus ltr) 
       (comm : bop_commutative R eqR plus)
       (m : functional_matrix L) (n : nat) : 
      ∀ k, LWP[ Pk{ m , k , n } ] =M= LWP[PEk[ m , k , n ] ].
    Admitted.
(*    
   Proof. induction k.
          + admit. (* (LWP[ Pk{ m, 0, n}]) =M= (LWP[ PEk[ m, 0, n]]) *)
          + assert (A := unfold_left_sum_of_path_powers n m k).
            assert (B := unfold_PEk m n k).
            assert (C := LWP_congruence _ _ A). 
            assert (D := LWP_congruence _ _ B).
            assert (E := LWP_distributes_over_matrix_add assoc comm id (Pk{ m, k, n}) (Pk[ m, S k, n])).
            assert (F := LWP_distributes_over_left_matrix_mul_ELEMENTARY id ann assoc LD m n (PEk[ m, k, n])).
            assert (G := trnM _ _ _ C E).
            assert (I := trnM _ _ _ D F). 

 IHk : (LWP[ Pk{ m, k, n}]) =M= (LWP[ PEk[ m, k, n]])
  G : (LWP[ Pk{ m, S k, n}])  =M= ((LWP[ Pk{ m, k, n}]) +M (LWP[ Pk[ m, S k, n]]))
  I : (LWP[ PEk[ m, S k, n]]) =M= (m *[ n ]> (LWP[ PEk[ m, k, n]]))

  ((LWP[ Pk{ m, k, n}]) +M (LWP[ Pk[ m, S k, n]]))
  =M= {IHk, congruence}
  ((LWP[ PEk[ m, k, n]]) +M (LWP[ Pk[ m, S k, n]]))

NEED 

  ((LWP[ PEk[ m, k, n]]) +M (LWP[ Pk[ m, S k, n]]))
  =M= 
  (m *[ n ]> (LWP[ PEk[ m, k, n]]))

  ============================
  (LWP[ Pk{ m, S k, n}]) =M= (LWP[ PEk[ m, S k, n]])


*) 

            
End Weighted_Paths.   

  (*
  Lemma claim3 (plusIdempotent : bop_idempotent R eqR plus)
        (n : nat) (m : functional_matrix L) :
        ∀ k, Mk{ m, k, n} +M (m *[ n ]> Mk{ m, k, n})
              =M=
              Mk{ m, k, n} +M Mk[m, S k, n].
  Proof. induction k. 
         + unfold left_sum_of_matrix_powers, left_matrix_exponentiation; simpl. 
           admit. (* need I is +M ann *)
         + (* IHk : Mk{ m, k, n} +M m *[ n]> Mk{ m, k, n}
                    =M=
                    Mk{ m, k, n} +M Mk[ m, S k, n]
               ============================
               Mk{ m, S k, n} +M m *[ n]> Mk{ m, S k, n}
               =M=
               Mk{ m, S k, n}) +M Mk[ m, S (S k), n]

              Proof: 
              Mk{ m, S k, n} +M m *[ n]> Mk{ m, S k, n}
              =M={unfold} 
              Mk{ m, S k, n} +M m *[ n]> (Mk{ m, k, n} +M Mk[m, S k, n]) 
              =M={left_distrib}  
              Mk{ m, S k, n} +M m *[ n]> Mk{ m, k, n} +M m *[ n]> Mk[m, S k, n]  
              =M= {unfold} 
              Mk{ m, S k, n} +M m *[ n]> Mk{ m, k, n} +M Mk[m, S (S k), n]  
              =M={unfold} 
              Mk{m, k, n} +M Mk[m, S k, n] +M m *[ n]> Mk{ m, k, n} +M Mk[m, S (S k), n]  
              =M={assoc, comm} 
              Mk{m, k, n} +M m *[ n]> Mk{ m, k, n} +M Mk[m, S k, n] +M Mk[m, S (S k), n]  
              =M={IHk} 
              Mk{ m, k, n} +M Mk[ m, S k, n] +M Mk[m, S k, n] +M Mk[m, S (S k), n]  
              =M={matrix_add_idempotent} 
              Mk{ m, k, n} +M Mk[ m, S k, n] +M Mk[m, S (S k), n]  
              =M= 
              Mk{ m, S k, n}) +M Mk[ m, S (S k), n]
          *)
Admitted. 


  Lemma powers (n : nat) (m : functional_matrix L) :
    ∀ k, Mk[ m +M [I], k , n ] =M= Mk{ m, k, n}.
  Proof. induction k.
         + simpl. apply eq_functional_matrix_prop_reflexive; auto. 
         + (* IHk : Mk[ m +M [I], k, n] =M= Mk{ m, k, n}
              ============================
              Mk[ m +M [I], S k, n] =M= Mk{ m, S k, n}
    
              Proof: 
              Mk[ m +M ([I]), S k, n]
              =M={unfold} 
              (m +M [I]) *M Mk[ m +M ([I]), k, n]
              =M={IHk, congruence} 
              (m +M [I]) *M Mk{ m, k, n} 
              =M= {right_distrib} 
              (m *M Mk{ m, k, n}) +M ([I] *M Mk{ m, k, n}) 
              =M={identity} 
              (m *M Mk{ m, k, n}) +M Mk{ m, k, n}
              =M={commutative} 
              Mk{ m, k, n} +M (m *M Mk{ m, k, n})
              =M={claim3} 
              Mk{ m, k, n} +M Mk[m, S k, n].
              =M={unfold} 
              Mk{ m, S k, n}
            *)
           assert (A : Mk[ m +M [I], S k, n]
                       =M=
                       ((m +M [I]) *[n] Mk[ m +M [I], k, n])).
              admit.
           assert (B : ((m +M [I]) *[n] Mk[ m +M [I], k, n])
                       =M=
                       ((m +M [I]) *[n] Mk{ m, k, n})).
                  admit. 
                  (*apply matrix_mul_congruence. *)
           
  Admitted.
  *)

