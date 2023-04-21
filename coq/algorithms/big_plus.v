From Coq Require Import
  Sorting.Permutation
  List.
Import ListNotations.
From CAS Require Import
     coq.common.compute
     coq.theory.set 
     coq.eqv.properties
     coq.eqv.nat
     coq.eqv.list
     coq.eqv.set 
     coq.sg.properties
     coq.sg.union
     coq.ltr.properties
     coq.algorithms.list_congruences. 


Section Computation.
  
  Definition big_plus
               {V : Type}               
               {S : Type}
               (zero : S)               
               (plus : binary_op S)                
               (f : V -> S)
               (l : list V) : S :=
    fold_right plus zero (map f l). 

  Definition big_plus_set
               {V : Type}               
               {S : Type}
               (zero : S)               
               (plus : binary_op S)
               (eq : brel V)                
               (f : V -> S)
               (X : finite_set V) : S :=
    big_plus zero plus f (uop_duplicate_elim eq X). 

End Computation.

Section Theory.

  Variables
    (V R : Type)

    (eqR  : brel R)
    (refR : brel_reflexive R eqR)
    (symR : brel_symmetric R eqR)
    (trnR : brel_transitive R eqR)

    (eqV : brel V)
    (conV : brel_congruence V eqV eqV)
    (refV : brel_reflexive V eqV)    
    (symV : brel_symmetric V eqV)
    (trnV : brel_transitive V eqV)
    
    (plus : binary_op R)
    (congrP : bop_congruence R eqR plus)
    (assoc : bop_associative R eqR plus)
    (comm : bop_commutative R eqR plus)
    
    (zero : R)
    . 

    Local Notation "a =r= b" := (eqR a b = true) (at level 70).
    Local Notation "a =n= b" := (brel_eq_nat a b = true) (at level 70).
    Local Notation "a =l= b" := (brel_list eqV a b = true) (at level 70).
    Notation "A ⊕ B" := (plus A B) (at level 50, left associativity).     
    Local Notation "a ∈ l"   := (in_list eqV l a = true) (at level 70).
    Local Notation "⨁_( l ) f"      := (big_plus zero plus f l) (at level 70).
    Local Notation "⨁_{ X } f"      := (big_plus_set zero plus eqV f X) (at level 70).
    
 Lemma big_plus_congruence_general
   (T : Type)
   (eqT : brel T) 
   (h g : T -> R)
   (cong : ∀ i j, eqT i j = true -> (h i) =r= (g j)):
    ∀ (l1 l2 : list T),  brel_list eqT l1 l2 = true -> 
          ⨁_(l1) h =r= ⨁_(l2) g. 
  Proof. intros l1 l2 I.
         unfold big_plus.
         apply (fold_right_congruence _ _ eqR eqR plus plus).
         intros b b' a a' J K. exact (congrP _ _ _ _ J K). 
         apply refR.
         apply (map_congruence T R eqT eqR h g cong); auto. 
  Qed.

  
  Lemma big_plus_congruence
    (h g : nat -> R)
    (cong : ∀ i j, i =n= j -> (h i) =r= (g j)):
    ∀ l, ⨁_(l) h =r= ⨁_(l) g.
  Proof. intro l.
         apply (big_plus_congruence_general _ brel_eq_nat h g cong). 
         apply brel_list_reflexive. apply brel_eq_nat_reflexive. 
  Qed.

  Lemma big_plus_congruence_v2
    (h g : nat -> R)
    (gcong : ∀ i j, i =n= j -> (g i) =r= (g j))
    (cong : ∀ i , (h i) =r= (g i)):
    ∀ l, ⨁_(l) h =r= ⨁_(l) g.
  Proof. intro l.
         assert (cong2 : ∀ i j, i =n= j -> (h i) =r= (g j)).
            intros i j A.
            assert (B := gcong i j A).
            assert (C := cong i).
            exact (trnR _ _ _ C B). 
         apply (big_plus_congruence_general nat brel_eq_nat h g cong2). 
         apply brel_list_reflexive. apply brel_eq_nat_reflexive. 
  Qed.

  (* try to make this as general as possible *) 
  Lemma fold_right_lemma {A B : Type}
        (a : B) (b : R) (h : B → R)
        (l : list B) : 
    fold_right plus (plus (h a) b) (map h l) =r= plus (h a) (fold_right plus b (map h l)).
  Proof. induction l.
         + compute. apply refR. 
         + simpl.
           (* Show: 
             IHl :        fold_right plus (plus (f a) b) (map f l)  = plus (f a)              (fold_right plus b (map f l))
             ============================
             plus (f a0) (fold_right plus (plus (f a) b) (map f l)) = plus (f a) (plus (f a0) (fold_right plus b (map f l)))
            
             Proof: 
             plus (f a0) (fold_right plus (plus (f a) b) (map f l))
             = {IHl and congruence} 
             plus (f a0) (plus (f a) (fold_right plus b (map f l)))
             = {assoc} 
             plus(plus (f a0) (f a)) (fold_right plus b (map f l))
             = {comm and congruence} 
             plus(plus (f a) (f a0)) (fold_right plus b (map f l))
             = {assoc}            
             plus (f a) (plus (f a0) (fold_right plus b (map f l)))
        *) 
        assert (C : plus (h a0) (fold_right plus (plus (h a) b) (map h l))
                    =r=
                   plus (h a0) (plus (h a) (fold_right plus b (map h l)))). 
           apply congrP; auto. 
        assert (D : plus (h a0) (plus (h a) (fold_right plus b (map h l)))
                    =r=                    
                    plus(plus (h a0) (h a)) (fold_right plus b (map h l))).
           exact (symR _ _ (assoc (h a0) (h a) (fold_right plus b (map h l)))). 
        assert (E : plus(plus (h a0) (h a)) (fold_right plus b (map h l))
                    =r=
                    plus(plus (h a) (h a0)) (fold_right plus b (map h l))).
            assert (F := comm (h a) (h a0)).
            assert (G := assoc (h a0) (h a) (fold_right plus b (map h l))). 
            assert (I := congrP _ _ _ _ F (refR ((fold_right plus b (map h l))))).
            exact (symR _ _ I).             
        assert (F : plus(plus (h a) (h a0)) (fold_right plus b (map h l))
                    =r=
                    plus (h a) (plus (h a0) (fold_right plus b (map h l)))).                     
            apply assoc. 

        exact (trnR _ _ _ C (trnR _ _ _ D (trnR _ _ _ E F))).
  Qed.

  Lemma big_plus_cons (f : V -> R) : ∀ a l,
      ⨁_(a :: l) f 
      =r=
      (f a) ⊕ (⨁_(l) f).
  Proof. intros a l. apply refR. Qed.

  Lemma fold_right_extract_plus
    (plusID : bop_is_id R eqR plus zero) (v : R) (l : list R) : 
    fold_right plus v l
    =r=
    (fold_right plus zero l) ⊕ v.
  Proof. induction l; simpl.
         + destruct (plusID v) as [A B]. exact (symR _ _ A). 
         + assert (A := symR _ _ (assoc a ((fold_right plus zero l)) v)).
           assert (B := congrP _ _ _ _ (refR a) IHl). 
           exact (trnR _ _ _ B A). 
  Qed. 
           
  Lemma big_plus_distributes_over_concat
    (plusID : bop_is_id R eqR plus zero) (f : V -> R) (l₁ l₂ : list V) : 
    ⨁_(l₁ ++ l₂) f 
    =r=
    (⨁_(l₁) f) ⊕ (⨁_(l₂) f).
    Proof. unfold big_plus.
           rewrite map_app. 
           rewrite fold_right_app.
           apply fold_right_extract_plus; auto. 
    Qed.

  Lemma big_plus_shift_middle
      (plusID : bop_is_id R eqR plus zero) (f : V -> R) (v : V) (l₁ l₂ : list V) : 
    ⨁_(l₁ ++ [v] ++ l₂) f 
    =r=
    (f v) ⊕ (⨁_(l₁ ++ l₂) f ).
  Proof. assert (A := big_plus_distributes_over_concat plusID f l₁ ([v] ++ l₂)).
         rewrite <- theory.list_lemma1 in A.
         assert (B := big_plus_cons f v l₂).
         assert (C := big_plus_distributes_over_concat plusID f l₁ l₂). apply symR in C. 
         assert (D := congrP _ _ _ _ (refR (⨁_(l₁) f)) B).
         assert (E := trnR _ _ _ A D). 
         assert (F := assoc (⨁_(l₁) f) (f v) (⨁_(l₂)f)).
         apply symR in F. 
         assert (G := trnR _ _ _ E F). 
         assert (H := comm (⨁_(l₁) f) (f v)).
         assert (I := congrP _ _ _ _ H (refR (⨁_(l₂) f))). 
         assert (J := trnR _ _ _ G I).
         assert (K := assoc (f v) (⨁_(l₁) f) (⨁_(l₂) f)).
         assert (L := trnR _ _ _ J K).
         assert (M := congrP _ _ _ _ (refR (f v)) C).
         exact (trnR _ _ _ L M).
  Qed.
 
  Lemma big_plus_permutation (f : V -> R) :
    ∀ (l₁ l₂ : list V), Permutation l₁ l₂ -> (⨁_(l₁) f) =r= (⨁_(l₂) f).
  Proof. apply (Permutation_ind_bis (fun l1 => fun l2 => (⨁_(l1) f) =r= (⨁_(l2) f))). 
         - apply refR.
         - intros v l l' A B.
           assert (C := big_plus_cons f v l).
           assert (D := big_plus_cons f v l').
           assert (E := congrP _ _ _ _ (refR (f v)) B).
           assert (F := trnR _ _ _ C E). apply symR in D.
           exact (trnR _ _ _ F D). 
         - intros v v' l l' A B.
           assert (C := big_plus_cons f v' (v :: l)).
           assert (D := big_plus_cons f v (v' :: l')).
           assert (E := big_plus_cons f v l).
           assert (F := big_plus_cons f v' l').
           assert (G := congrP _ _ _ _ (refR (f v')) E).
           assert (H := trnR _ _ _ C G). 
           assert (I := congrP _ _ _ _ (refR (f v)) F).
           assert (J := trnR _ _ _ D I).
           assert (K : plus (f v') (plus (f v) (⨁_(l) f))
                       =r=
                       plus (f v) (plus (f v') (⨁_(l') f))).
           {
             assert (L := assoc (f v') (f v) (⨁_(l) f)). apply symR in L.
             assert (M := comm (f v') (f v)). 
             assert (N := congrP _ _ _ _ M B).
             assert (O := trnR _ _ _ L N).
             assert (P := assoc (f v) (f v') (⨁_(l') f)).
             exact (trnR _ _ _ O P). 
           } 
           assert (L := trnR _ _ _ H K). apply symR in J.
           exact (trnR _ _ _ L J). 
         - intros l l' l'' A B C D.
           exact (trnR _ _ _ B D). 
  Qed.


(************** BIG PLUS OVER SETS ***************************)

  Local Definition de := uop_duplicate_elim eqV.
  Local Notation "x =S= y" := (brel_set eqV x y = true) (at level 70).

  Fixpoint no_duplicates {T : Type} (r : brel T) (X : finite_set T) : bool := 
    match X with
    | [] => true 
    | a :: Y => if in_set r Y a then false else no_duplicates r Y 
    end.

  Lemma no_duplicates_cons_intro (v : V) (X : finite_set V) :
     in_set eqV X v = false -> no_duplicates eqV X = true -> 
        no_duplicates eqV (v :: X) = true. 
  Proof. intros A B; simpl. 
         rewrite A. exact B. 
  Qed.

  Lemma no_duplicates_cons_elim (v : V) (X : finite_set V) :
    no_duplicates eqV (v :: X) = true ->
    (in_set eqV X v = false) * (no_duplicates eqV X = true). 
  Proof. intros A. simpl in A.
         case_eq(in_set eqV X v); intro B; rewrite B  in A; auto. 
         - discriminate A. 
  Qed.            

  Lemma duplicate_elim_eliminates_duplicates : ∀ X, no_duplicates eqV (de X) = true. 
  Proof. unfold de. induction X; simpl; try auto. 
         case_eq(in_set eqV X a); intro A.
         + exact IHX. 
         + simpl.
           case_eq(in_set eqV (uop_duplicate_elim eqV X) a ); intro B.
           * apply in_set_uop_duplicate_elim_elim in B.
             rewrite A in B. discriminate B. 
           * exact IHX.
  Qed.
  
  Lemma  duplicate_elim_preserves_equality : ∀ X, X =S= (de X). 
  Proof. unfold de. intro X. 
         apply brel_set_intro_prop; auto; split; intros a A. 
         - apply in_set_uop_duplicate_elim_intro; auto. 
         - apply in_set_uop_duplicate_elim_elim in A; auto. 
  Qed.            

  Lemma duplicate_elim_congruence : ∀ X Y,  X =S= Y -> (de X) =S= (de Y).
  Proof. assert (A := uop_duplicate_elim_congruence_v1 _ eqV symV trnV).
         unfold properties.uop_congruence_positive in A.
         unfold de.
         intros X Y B.
         apply brel_set_elim in B; auto. destruct B as [B C].
         assert (D := A _ _ B).
         assert (E := A _ _ C).
         apply brel_set_intro; auto.
  Qed.

  
  Lemma equal_sets_with_no_duplicates_are_permuted_lists :
    ∀ (X Y : finite_set V),
      no_duplicates eqV X = true -> no_duplicates eqV Y = true ->
               X =S= Y -> Permutation X Y.
  Proof. induction X; induction Y; intros A B C. 
         - exact (@perm_nil V). 
         - compute in C. discriminate C.
         - compute in C. discriminate C.
         - apply no_duplicates_cons_elim in A, B.
           destruct A as [A A']; destruct B as [B B'].
           case_eq(eqV a a0); intro E.
           + assert (F : X =S= Y).
             {
               apply brel_set_elim_prop in C; auto.
               destruct C as [C D].
               apply brel_set_intro_prop; auto.
               split; intros v F.
               * assert (G : in_set eqV (a :: X) v = true).
                 {
                   apply in_set_cons_intro; auto. 
                 } 
                 assert (H := C _ G).
                 apply in_set_cons_elim in H; auto.
                 destruct H as [H | H]; auto. 
                 -- assert (I := trnV _ _ _ E H). apply symV in I. 
                    rewrite (in_set_right_congruence _ _ symV trnV _ _ X I F) in A.
                    discriminate A. 
               * assert (G : in_set eqV (a0 :: Y) v = true).
                 {
                   apply in_set_cons_intro; auto. 
                 } 
                 assert (H := D _ G).
                 apply in_set_cons_elim in H; auto.
                 destruct H as [H | H]; auto. 
                 -- apply symV in E.
                    assert (I := trnV _ _ _ E H). apply symV in I.
                    rewrite (in_set_right_congruence _ _ symV trnV _ _ Y I F) in B.
                    discriminate B. 
             }
             assert (I := IHX _ A' B' F).
             (* perm_skip : ∀ (x : A) (l l' : list A), Permutation l l' → Permutation (x :: l) (x :: l') 
                Note: this is using =, but we need to use eqV.  So, need to define 
                a version Permutation parameterized by an equality. 
             *)
             admit. 
           +
             
(*
            Need to define a new function for this case .... 


  Inductive Permutation (A : Type) : list A → list A → Prop :=
    perm_nil : Permutation [] []
  | perm_skip : ∀ (x : A) (l l' : list A), Permutation l l' → Permutation (x :: l) (x :: l')
  | perm_swap : ∀ (x y : A) (l : list A), Permutation (y :: x :: l) (x :: y :: l)
  | perm_trans : ∀ l l' l'' : list A, Permutation l l' → Permutation l' l'' → Permutation l l''.
*)              
  Admitted.


  Inductive PermutationEqv : list V → list V → Prop :=
    perm_eqv_nil : PermutationEqv [] []
  | perm_eqv_skip : ∀ (x x' : V) (l l' : list V), eqV x x' = true → PermutationEqv l l' → PermutationEqv (x :: l) (x' :: l')
  | perm_eqv_swap : ∀ (x x' y y' : V) (l : list V), eqV x x' = true → eqV y y' = true → PermutationEqv (y :: x :: l) (x' :: y' :: l)
  | perm_eqv_trans : ∀ l l' l'' : list V, PermutationEqv l l' → PermutationEqv l' l'' → PermutationEqv l l''
  .


  Fixpoint list_remove l a :=
    match l with
    | [] => []
    | b :: l' => if eqV a b then l' else b :: (list_remove l' a)
    end.

  Local Infix "/" := (list_remove). 


  Lemma remove_permutation (v : V) :
    ∀ X, in_set eqV X v = true -> 
         PermutationEqv X (v :: (X / v)).
  Proof. induction X; intro A.
         - compute in A. discriminate A.
         - apply in_set_cons_elim in A; auto.
           destruct A as [A | A].
           + admit. 
           + assert (B := IHX A).
             assert (C : PermutationEqv (a :: X) (a :: (v :: X / v))).
             {
               apply perm_eqv_skip; auto. 
             }
             assert (D : PermutationEqv (a :: v :: X / v) (v :: (a :: X) / v)).
             {
               assert (E := perm_eqv_swap _ _ _ _ (X / v) (refV a) (refV v)).
               admit. 
             } 
             admit.
  Admitted.
  
  Lemma equal_sets_with_no_duplicates_are_permuted_lists_VII :
    ∀ n (X Y : finite_set V),
      n = length X -> 
      no_duplicates eqV X = true -> no_duplicates eqV Y = true ->
               X =S= Y -> PermutationEqv X Y.
  Proof. induction n; intros X Y XL A B C.
         - destruct X; destruct Y.
           + exact perm_eqv_nil. 
           + compute in C. discriminate C.
           + compute in C. discriminate C.
           + simpl in XL. admit. 
         - destruct X; destruct Y.
           + compute in XL. admit. 
           + compute in C. discriminate C.
           + compute in C. discriminate C.
           + apply no_duplicates_cons_elim in A, B.
             destruct A as [A A']; destruct B as [B B'].
             assert (XL' : n = length X). admit. 
             case_eq(eqV v v0); intro E.
             * assert (F : X =S= Y).
               {
                 apply brel_set_elim_prop in C; auto.
                 destruct C as [C D].
                 apply brel_set_intro_prop; auto.
                 split; intros v' F.
                 -- assert (G : in_set eqV (v :: X) v' = true).
                    {
                      apply in_set_cons_intro; auto. 
                    } 
                    assert (H := C _ G).
                    apply in_set_cons_elim in H; auto.
                    destruct H as [H | H]; auto. 
                    ++ assert (I := trnV _ _ _ E H). apply symV in I. 
                       rewrite (in_set_right_congruence _ _ symV trnV _ _ X I F) in A.
                       discriminate A. 
                 -- assert (G : in_set eqV (v0 :: Y) v' = true).
                    {
                      apply in_set_cons_intro; auto. 
                    } 
                    assert (H := D _ G).
                    apply in_set_cons_elim in H; auto.
                    destruct H as [H | H]; auto. 
                    ** apply symV in E.
                       assert (I := trnV _ _ _ E H). apply symV in I.
                       rewrite (in_set_right_congruence _ _ symV trnV _ _ Y I F) in B.
                       discriminate B. 
               }
               assert (I := IHn _ _ XL' A' B' F).
               (* perm_skip : ∀ (x : A) (l l' : list A), Permutation l l' → Permutation (x :: l) (x :: l') 
                Note: this is using =, but we need to use eqV.  So, need to define 
                a version Permutation parameterized by an equality. 
                *)
               admit. 
             * assert (F : (v :: (X / v0)) =S= (v :: (Y / v))). admit.
               assert (G : n = length (v :: (X / v0))). admit.
               assert (I : no_duplicates eqV (v :: (X / v0)) = true). admit.
               assert (J : no_duplicates eqV (v :: (Y / v)) = true). admit.
               assert (K := IHn _ _ G I J F).
               assert (L : PermutationEqv (v0 :: v :: (X / v0)) (v0:: v :: (Y / v))).
               {
                 (* use perm_skip *) 
                 admit. 
               }
               assert (M : PermutationEqv (v :: X) (v0 :: v :: (X / v0))). admit.
               assert (N : PermutationEqv (v0 :: v :: (Y / v)) (v0 :: Y)). admit.
               assert (O := perm_eqv_trans _ _ _ M L).
               exact (perm_eqv_trans _ _ _ O N). 
  Admitted.
  
  
  
  Lemma equal_sets_are_permuted_lists : ∀ X Y,  X =S= Y -> Permutation (de X) (de Y).  
  Proof. intros X Y A.
         assert (B := duplicate_elim_congruence _ _ A).
         assert (C := duplicate_elim_eliminates_duplicates X). 
         assert (D := duplicate_elim_eliminates_duplicates Y).
         exact (equal_sets_with_no_duplicates_are_permuted_lists _ _ C D B).
  Qed. 
  
 Lemma big_plus_set_congruence
   (eqT : brel V) 
   (h g : V -> R)
   (eq_h_g : ∀ i j, eqV i j = true -> (h i) =r= (g j)):
    ∀ (X Y : finite_set V),  X =S= Y -> 
       ⨁_{X} h =r= ⨁_{Y} g. 
  Proof. intros X Y I.
         unfold big_plus_set.
         assert (A := equal_sets_are_permuted_lists _ _ I).
         assert (B := big_plus_permutation h _ _ A).
         assert (C := big_plus_permutation g _ _ A).
         assert (D : (de Y) =l= (de Y)). apply brel_list_reflexive; auto. 
         assert (E := big_plus_congruence_general V eqV h g eq_h_g _ _ D).
         assert (F := trnR _ _ _ B E).
         unfold de in F. exact F. 
  Qed.

  Local Notation "x ∪ y" := (bop_union eqV x y) (at level 70).
  Local Notation "a ∈ x" := (in_set eqV x a = true) (at level 70).
  Local Notation "a ∉ x" := (in_set eqV x a = false) (at level 70).

  Lemma big_plus_set_cons (f : V -> R) :
    ∀ a X,  a ∉ X -> 
      ⨁_{a :: X} f 
      =r=
      (f a) ⊕ (⨁_{X} f).
  Proof. intros a X A.
         unfold big_plus_set at 1. 
         apply uop_duplicate_elim_lemma_2 in A.
         rewrite A.
         unfold big_plus_set.
         apply big_plus_cons. 
  Qed. 


  Lemma big_plus_set_ignore_cons (f : V -> R) :
    ∀ a X,  a ∈ X -> 
      ⨁_{a :: X} f =r= ⨁_{X} f. 
  Proof. intros a X A.
           unfold big_plus_set.
           apply uop_duplicate_elim_lemma_3 in A.
           rewrite A. apply refR. 
  Qed. 

  Lemma big_plus_set_distributes_over_union
    (plusID : bop_is_id R eqR plus zero)
    (g : V -> R)
    (cong_g : ∀ i j, eqV i j = true -> (g i) =r= (g j)):
    ∀ X Y,  (⨁_{X} g) ⊕ (⨁_{Y} g) =r= ⨁_{X ∪ Y} g. 
  Proof. induction X; intro Y.
         - unfold big_plus_set at 1. simpl.
           unfold big_plus. simpl.
           destruct (plusID (⨁_{Y} g)) as [A _].
           assert (B : Y =S= ([] ∪ Y)).
           {
             apply brel_set_symmetric; auto. 
             apply bop_union_with_nil_left; auto. 
           } 
           assert (C := big_plus_set_congruence eqV g g cong_g _ _ B).
           exact (trnR _ _ _ A C). 
         - case_eq(in_set eqV (X ∪ Y) a); intro A.
           + (* 
              we know (⨁_{a :: X ∪ Y} g) =r= (⨁_{X ∪ Y} g)
              if a ∈ X, then ⨁_{ a :: X} g) =r= ⨁_{X} g) and then use IHX. 
              if a ∉ X? 
             *) 
             admit. 
           + assert (B : a ∉ X).
             {
               case_eq(in_set eqV X a); intro B; auto.
               assert (C : a ∈ (X ∪ Y)). apply in_set_bop_union_intro; auto.
               rewrite C in A. discriminate A. 
             } 
             assert (C : ((a :: X) ∪ Y) =S= (a :: (X ∪ Y))).
             {
               apply brel_set_symmetric; auto.
               apply bop_union_push_element; auto. 
             } 
             assert (D := big_plus_set_congruence eqV g g cong_g _ _ C).
             apply (big_plus_set_cons g) in A. 
             apply (big_plus_set_cons g) in B.
             assert (E := trnR _ _ _ D A). apply symR in E.
             assert (F := congrP _ _ _ _ B (refR (⨁_{Y} g))).
             assert (G := assoc (g a) (⨁_{X} g) (⨁_{Y} g)).
             assert (H := trnR _ _ _ F G).
             assert (I := congrP _ _ _ _ (refR (g a)) (IHX Y)).
             assert (J := trnR _ _ _ H I).
             exact (trnR _ _ _ J E). 
  Admitted.            


(************** BIG UNION ***************************)
  Definition zero_set : finite_set V := [].

  Definition big_union (F : V -> finite_set V) (l : list V) := 
    big_plus zero_set (bop_union eqV) F l.

  Lemma big_union_cons (F : V -> finite_set V):
    ∀ a l, big_union F (a :: l) =S= ((F a) ∪ (big_union F l)).
  Proof. intros a l. apply brel_set_reflexive; auto. Qed.


  Lemma big_plus_big_union
    (plusID : bop_is_id R eqR plus zero)
    (g : V -> R)
    (cong_g : ∀ i j, eqV i j = true -> (g i) =r= (g j))
    (F : V -> finite_set V): 
    ∀ l,   ⨁_(l) (λ q, ⨁_{F q} g) =r= ⨁_{big_union F l} g.
  Proof. induction l. 
         - compute. apply refR. 
         - (*
               ⨁_(a :: l) (λ q : V, ⨁_{F q} g)
               =r= {big_plus_cons} 
               (⨁_{F a} g) ⊕ (⨁_(l) (λ q : V, ⨁_{F q} g))
               =r= {IHl, congrP} 
               (⨁_{F a} g) ⊕ (⨁_{ big_union F l } g)
               =r= {big_plus_set_distributes_over_union} 
               ⨁_{ (F a) ∪ (big_union F l) } g 
               =r= {big_union_cons, big_plus_set_congruence} 
               ⨁_{ big_union F (a :: l) } g
            *)
           assert (A := big_plus_cons (λ q : V, ⨁_{F q} g) a l).
           simpl in A. 
           assert (B := congrP _ _ _ _ (refR (⨁_{ F a} g)) IHl).
           assert (C := trnR _ _ _ A B).
           assert (D := big_plus_set_distributes_over_union plusID g cong_g (F a) (big_union F l)).
           assert (E := trnR _ _ _ C D).
           assert (G := big_union_cons F a l).
           assert (H := big_plus_set_congruence eqV g g cong_g _ _ G).
           exact (trnR _ _ _ E H).
  Qed.
  
End Theory.


