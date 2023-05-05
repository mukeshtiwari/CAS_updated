From Coq Require Import
  Sorting.Permutation
  List.
Import ListNotations.
From CAS Require Import
     coq.common.compute
     coq.eqv.properties
     coq.eqv.nat
     coq.eqv.list
     coq.eqv.set 
     coq.sg.properties
     coq.sg.or
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
    (zeroID : bop_is_id _ eqR plus zero)
    . 

    Local Notation "a =r= b" := (eqR a b = true) (at level 70).
    Local Notation "a =v= b" := (eqV a b = true) (at level 70).    
    Local Notation "a =n= b" := (brel_eq_nat a b = true) (at level 70).
    Local Notation "a =l= b" := (brel_list eqV a b = true) (at level 70).

    
    Notation "A ⊕ B" := (plus A B) (at level 50, left associativity).
    Local Notation "a ∈' l"   := (in_list eqV l a = true) (at level 70).
    Local Notation "a ∈ x" := (in_set eqV x a = true) (at level 70).
    Local Notation "a ∉ x" := (in_set eqV x a = false) (at level 70).
    Local Notation "x ∪ y" := (bop_union eqV x y) (at level 70).    
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

  Lemma big_plus_cons (f : V -> R) : ∀ a l,
      ⨁_(a :: l) f 
      =r=
      (f a) ⊕ (⨁_(l) f).
  Proof. intros a l. apply refR. Qed.

  Lemma fold_right_extract_accumulator 
    (v : R) (l : list R) : 
    fold_right plus v l
    =r=
    v ⊕ (fold_right plus zero l).
  Proof. induction l; simpl.
         + destruct (zeroID v) as [A B]; auto. 
         + (* IHl : fold_right plus v l =r= v ⊕ fold_right plus zero l
              ============================
              a ⊕ fold_right plus v l =r= v ⊕ (a ⊕ fold_right plus zero l)

              a ⊕ fold_right plus v l 
              =r= {IHl} 
              a ⊕ (v ⊕ fold_right plus zero l)
              =r= {assoc}
              (a ⊕ v) ⊕ fold_right plus zero l
              =r= {comm}
              (v ⊕ a) ⊕ fold_right plus zero l
              =r= {assoc}
              v ⊕ (a ⊕ fold_right plus zero l)        

           assert (A := symR _ _ (assoc a ((fold_right plus zero l)) v)).
           assert (B := congrP _ _ _ _ (refR a) IHl). 
           exact (trnR _ _ _ B A). 
            *)
           assert (A := congrP _ _ _ _ (refR a) IHl).
           assert (B := assoc a v (fold_right plus zero l)).
           apply symR in B.
           assert (C := trnR _ _ _ A B).
           assert (D := comm a v).           
           assert (E := congrP _ _ _ _ D (refR (fold_right plus zero l))).
           assert (F := trnR _ _ _ C E). 
           assert (G := assoc v a (fold_right plus zero l)).
           exact (trnR _ _ _ F G).
Qed. 

  Lemma fold_right_to_big_plus 
    (f : V → R) : 
    ∀ (l : list V) (a : R), 
    fold_right plus a (map f l)
    =r=
    a ⊕ (⨁_(l) f).
  Proof. intros l a. apply fold_right_extract_accumulator. Qed. 

           
  Lemma big_plus_distributes_over_concat
    (f : V -> R) (l₁ l₂ : list V) : 
    ⨁_(l₁ ++ l₂) f 
    =r=
    (⨁_(l₁) f) ⊕ (⨁_(l₂) f).
    Proof. unfold big_plus.
           rewrite map_app. 
           rewrite fold_right_app.
           assert (A := fold_right_extract_accumulator (fold_right plus zero (map f l₂)) (map f l₁)).
           assert (B := comm (fold_right plus zero (map f l₂)) (fold_right plus zero (map f l₁))).
           exact (trnR _ _ _ A B). 
    Qed.

  Lemma big_plus_shift_middle
    (f : V -> R) (v : V) (l₁ l₂ : list V) : 
    ⨁_(l₁ ++ [v] ++ l₂) f 
    =r=
    (f v) ⊕ (⨁_(l₁ ++ l₂) f ).
  Proof. assert (A := big_plus_distributes_over_concat f l₁ ([v] ++ l₂)).
         rewrite <- theory.list_lemma1 in A.
         assert (B := big_plus_cons f v l₂).
         assert (C := big_plus_distributes_over_concat f l₁ l₂). apply symR in C. 
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



(**** Permutations 

   In Coq.Sorting.Permutation we have the definition 

  Inductive Permutation (A : Type) : list A → list A → Prop :=
    perm_nil : Permutation [] []
  | perm_skip : ∀ (x : A) (l l' : list A), Permutation l l' → Permutation (x :: l) (x :: l')
  | perm_swap : ∀ (x y : A) (l : list A), Permutation (y :: x :: l) (x :: y :: l)
  | perm_trans : ∀ l l' l'' : list A, Permutation l l' → Permutation l' l'' → Permutation l l''.

  Note that this does not work when we roll our own equality, so we need to redefine this
  as follows. 
*)              
    
  Inductive PermutationEqv : list V → list V → Prop :=
    perm_eqv_nil : PermutationEqv [] []
  | perm_eqv_skip : ∀ (x x' : V) (l l' : list V), eqV x x' = true → PermutationEqv l l' → PermutationEqv (x :: l) (x' :: l')
  | perm_eqv_swap : ∀ (x x' y y' : V) (l : list V), eqV x x' = true -> eqV y y' = true → PermutationEqv (y :: x :: l) (x' :: y' :: l)
  | perm_eqv_trans : ∀ l l' l'' : list V, PermutationEqv l l' → PermutationEqv l' l'' → PermutationEqv l l''
  .


Theorem PermutationEqv_reflexive : ∀ l, PermutationEqv l l.
Proof.
  induction l; constructor.
  - apply refV.
  - exact IHl.
Qed.

Theorem PermutationEqv_symmetric : ∀ l l', PermutationEqv l l' -> PermutationEqv l' l.
Proof. intros l l' H. induction H.
       - exact perm_eqv_nil.
       - apply symV in H.
         exact (perm_eqv_skip x' x l' l H IHPermutationEqv).
       - apply symV in H, H0.
         exact (perm_eqv_swap y' y x' x l H0 H).
       - exact (perm_eqv_trans _ _ _ IHPermutationEqv2 IHPermutationEqv1).
Qed. 


Theorem PermutationEqv_ind_bis :
  ∀ P : list V -> list V -> Prop,
   (∀ l, P l l) -> 
   P [] [] ->
   (forall x x' l l', PermutationEqv l l' -> eqV x x' = true → P l l' -> P (x :: l) (x' :: l')) ->
   (forall x x' y y' l l', PermutationEqv l l' -> eqV x x' = true -> eqV y y' = true → P l l' -> P (y :: x :: l) (x' :: y' :: l')) ->
   (forall l l' l'', PermutationEqv l l' -> P l l' -> PermutationEqv l' l'' -> P l' l'' -> P l l'') ->
   forall l l', PermutationEqv l l' -> P l l'.
Proof.
  intros P Hid Hnil Hskip Hswap Htrans.
  induction 1. 
  - exact Hnil. 
  - exact (Hskip x x' l l' H0 H IHPermutationEqv). 
  - exact (Hswap x x' y y' l l (PermutationEqv_reflexive l) H H0 (Hid l)).
  - exact (Htrans l l' l'' H IHPermutationEqv1 H0 IHPermutationEqv2).     
Qed.

Lemma PermutationEqv_nil : ∀ l, PermutationEqv [] l -> l = [].
Proof. intros l HF.
       remember (@nil V) as m in HF.
       induction HF; discriminate || auto.
Qed.

Theorem PermutationEqv_nil_cons : 
 ∀ l x, PermutationEqv nil (x::l) -> False. 
Proof. intros l x HF.
       apply PermutationEqv_nil in HF; discriminate.
Qed.

(*******************************************************************************) 

  Lemma big_plus_skip
        (f : V → R) 
        (congf : ∀ v v' : V, v =v= v' → f v =r= f v') 
        (x x' : V) (l l' : list V)
        (B : x =v= x')
        (K : (⨁_( l) f) =r= (⨁_( l') f)) : (⨁_( x :: l) f) =r= (⨁_( x' :: l') f). 
  Proof. assert (C := big_plus_cons f x l).
         assert (D := big_plus_cons f x' l').
         assert (E := congrP _ _ _ _ (congf _ _ B) K).
         assert (F := trnR _ _ _ C E). apply symR in D.
         exact (trnR _ _ _ F D).                                                                  
  Qed.

  Lemma big_plus_swap
        (f : V → R) 
        (congf : ∀ v v' : V, v =v= v' → f v =r= f v') 
        (x x' y y' : V) (l l' : list V)
        (B : x =v= x')
        (C : y =v= y')        
        (K : (⨁_( l) f) =r= (⨁_( l') f)) :
    (⨁_( y :: x :: l) f) =r= (⨁_( x' :: y' :: l') f).
Proof. (*  ⨁_( y :: x :: l) f) 
           =r= {big_plus_cons} 
           (f y) ⊕ ⨁_(x :: l) f)     
           =r= {big_plus_cons} 
           (f y) ⊕ ((f x) ⊕ ⨁_(l) f))     
           =r= {assoc, comm, congf}
           (f x') ⊕ ((f y') ⊕ (⨁_(y' :: l') f)).
           =r= {big_plus_cons} 
          (f x') ⊕ (⨁_(y' :: l') f).
          =r= {big_plus_cons} 
          (⨁_( x' :: y' :: l') f).
        *)
  assert (H : ⨁_(y :: x :: l) f =r= (f y) ⊕ ((f x) ⊕ ⨁_(l) f)).
  {
    assert (W := big_plus_cons f y (x :: l)).
    assert (Z := big_plus_cons f x l).
    assert (U := congrP _ _ _ _ (refR (f y)) Z).
    exact (trnR _ _ _ W U). 
  } 
  assert (I : (f y) ⊕ ((f x) ⊕ ⨁_(l) f) =r= (f x') ⊕ ((f y') ⊕ ⨁_(l') f)).
  {
    assert (L := assoc (f y) (f x) (⨁_(l) f)). apply symR in L.
    assert (M := comm (f y) (f x)).
    assert (N := congrP _ _ _ _ (congf _ _ B) (congf _ _ C)).
    assert (O := trnR _ _ _ M N). 
    assert (P := congrP _ _ _ _ O K).
    assert (Q := trnR _ _ _ L P). 
    assert (U := assoc (f x') (f y') (⨁_(l') f)). 
    exact (trnR _ _ _ Q U). 
  } 
  assert (J : (f x') ⊕ ((f y') ⊕ ⨁_(l') f) =r= ⨁_( x' :: y' :: l') f).
  {
    assert (W := big_plus_cons f x' (y' :: l')).
    assert (Z := big_plus_cons f y' l').
    assert (U := congrP _ _ _ _ (refR (f x')) Z).
    apply symR in U, W. 
    exact (trnR _ _ _ W U). 
  } 
  exact (trnR _ _ _ H (trnR _ _ _ I J)). 
Qed. 


  Lemma big_plus_permutation (f : V -> R)
    (congf : ∀ v v',  v =v= v' -> (f v) =r= (f v')) : 
    ∀ (l l' : list V), PermutationEqv l l' -> (⨁_(l) f) =r= (⨁_(l') f).
  Proof. apply (PermutationEqv_ind_bis (λ l l', (⨁_(l) f) =r= (⨁_(l') f))).
         - intro l. apply refR.
         - apply refR.
         - intros x x' l l' _ B C. apply big_plus_skip; auto.  
         - intros x x' y y' l l' _ B C K. apply big_plus_swap; auto.  
         - intros l l' l'' _ B _ D.
           exact (trnR _ _ _ B D). 
  Qed.


(************** BIG PLUS OVER SETS ***************************)

  Local Notation 𝛿 := (uop_duplicate_elim eqV).
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

  Lemma duplicate_elim_eliminates_duplicates : ∀ X, no_duplicates eqV (𝛿 X) = true. 
  Proof. induction X; simpl; try auto. 
         case_eq(in_set eqV X a); intro A.
         + exact IHX. 
         + simpl.
           case_eq(in_set eqV (uop_duplicate_elim eqV X) a ); intro B.
           * apply in_set_uop_duplicate_elim_elim in B.
             rewrite A in B. discriminate B. 
           * exact IHX.
  Qed.
  
  Lemma  duplicate_elim_preserves_equality : ∀ X, X =S= (𝛿 X). 
  Proof.  intro X. 
         apply brel_set_intro_prop; auto; split; intros a A. 
         - apply in_set_uop_duplicate_elim_intro; auto. 
         - apply in_set_uop_duplicate_elim_elim in A; auto. 
  Qed.            

  Lemma duplicate_elim_congruence : ∀ X Y,  X =S= Y -> (𝛿 X) =S= (𝛿 Y).
  Proof. assert (A := uop_duplicate_elim_congruence_v1 _ eqV symV trnV).
         unfold properties.uop_congruence_positive in A.         
         intros X Y B.
         apply brel_set_elim in B; auto. destruct B as [B C].
         assert (D := A _ _ B).
         assert (E := A _ _ C).
         apply brel_set_intro; auto.
  Qed.

  Lemma big_plus_set_is_big_plus_with_duplicate_elim (f : V -> R) :
    ∀ X, ⨁_{ X } f =r= ⨁_( 𝛿 X ) f. 
  Proof. intro X. apply refR. Qed. 

    
  Fixpoint remove_equal_elements_from_list l a :=
    match l with
    | [] => []
    | b :: l' =>
        if eqV a b
        then remove_equal_elements_from_list l' a
        else b :: (remove_equal_elements_from_list l' a)
    end.

 Local Infix "/" := (remove_equal_elements_from_list).

 Fixpoint remove_list_from_list l l' :=
    match l' with
    | [] => l 
    | a :: l'' => remove_list_from_list (l / a) l''
    end.

 Local Infix "//" := (remove_list_from_list) (at level 70).


     Lemma remove_no_op : ∀ X a,  
        a ∉ X -> (X / a) = X.
     Proof. induction X as [ | b X]; intros a A; simpl. 
            - reflexivity. 
            - apply not_in_set_cons_elim in A; auto.
              destruct A as [A B].
              case_eq(eqV a b); intro C.
              + apply symV in C. rewrite C in A.
                discriminate A. 
              + rewrite (IHX _ B).
                reflexivity. 
     Qed.               

    Lemma remove_not_in_set_preserved : ∀ X a b,  
        b ∉ X -> b ∉ (X / a). 
    Proof. induction X as [ | c X]; intros a b A; simpl.
           - reflexivity.
           - apply not_in_set_cons_elim in A; auto.
             destruct A as [A B].
             case_eq(eqV a c); intro C.
             + apply IHX; auto. 
             + apply not_in_set_cons_intro; auto. 
    Qed.   


  Lemma in_set_remove_equal_elements_from_list_intro : 
       ∀ X a b,    
          b ∈ X -> eqV b a = false -> 
          b ∈ (X / a). 
  Proof. induction X as [ | c X]; intros a b A B.
         - compute in A. discriminate A.
         - apply in_set_cons_elim in A; auto.
           destruct A as [A | A]; simpl. 
           + case_eq(eqV a c); intro C.
             * apply symV in A, C.
               rewrite (trnV _ _ _ A C) in B.
               discriminate B. 
             * apply in_set_cons_intro; auto. 
           + case_eq(eqV a c); intro C.
             * apply IHX; auto. 
             * apply in_set_cons_intro; auto. 
  Qed.
  
  Lemma in_set_remove_equal_elements_from_list_elim : 
       ∀ X a b, b ∈ (X / a) -> 
          (b ∈ X) * (eqV b a = false). 
  Proof. induction X as [ | c X]; intros a b A; split.
         - compute in A. discriminate A. 
         - compute in A. discriminate A. 
         - simpl in A.
           apply in_set_cons_intro; auto.
           case_eq(eqV a c); intro B; rewrite B in A.
           + destruct (IHX _ _ A) as [C _].
             right. exact C. 
           + apply in_set_cons_elim in A; auto.
             destruct A as [A | A]; auto.
             destruct (IHX _ _ A) as [C _].
             right. exact C. 
         - simpl in A.
           case_eq(eqV a c); intro B; rewrite B in A.
           + apply IHX; auto. 
           + apply in_set_cons_elim in A; auto.
             destruct A as [A | A].
             * case_eq(eqV b a); intro C; auto.
               apply symV in A, C.
               rewrite (trnV _ _ _ C A) in B.
               discriminate B.
             * apply IHX; auto. 
  Qed.            


  Lemma brel_set_squash_duplicates :
    ∀ X a b, a =v= b -> a :: b :: X =S= b :: X.
  Proof. intros X a b A.
         apply brel_set_intro_prop; auto.
         split; intros c B. 
         - apply in_set_cons_elim in B; auto.
           destruct B as [B | B]; auto. 
           + apply symV in B.
             assert (C := trnV _ _ _ B A).
             apply in_set_cons_intro; auto. 
         - apply in_set_cons_intro; auto.
  Qed.
  
  Lemma simplify_brel_cons_equal : 
    ∀ X Y a, a ∈ X -> (a :: X) =S= Y -> X =S= Y.
  Proof. intros X Y a A B.
         apply brel_set_elim_prop in B; auto. 
         destruct B as [B C].
         apply brel_set_intro_prop; auto.
         split; intros b D.
         - apply B. apply in_set_cons_intro; auto.
         - apply C in D.
           apply in_set_cons_elim in D; auto.
           destruct D as [D | D]; auto.
           + exact (in_set_right_congruence _ eqV symV trnV _ _ _ D A). 
  Qed. 


    Lemma simplify_brel_cons_equal_v2 : 
    ∀ X Y a, a ∉ X -> (a :: X) =S= Y -> (a ∈ Y) * (X =S= (Y / a)).
    Proof. intros X Y a A B.
           apply brel_set_elim_prop in B; auto.
           destruct B as [B C]. split.
           - apply B. apply in_set_cons_intro; auto. 
           - apply brel_set_intro_prop; auto; split; intros b D.
             + apply in_set_remove_equal_elements_from_list_intro.
               * apply B. apply in_set_cons_intro; auto. 
               * case_eq(eqV b a); intro E; auto.
                 rewrite (in_set_right_congruence _ eqV symV trnV _ _ X E D) in A. 
                 discriminate A. 
             + apply in_set_remove_equal_elements_from_list_elim in D.
               destruct D as [D E].
               assert (F := C _ D).
               apply in_set_cons_elim in F; auto.
               destruct F as [F | F]; auto. 
               * apply symV in F. rewrite F in E.
                 discriminate E. 
    Qed. 
    
    Lemma Permutation_remove : ∀ X a,  
       (a ∈ X) -> PermutationEqv (a :: 𝛿 (X / a)) (𝛿 X). 
    Proof. induction X as [ | b X]; intros a A. 
           - compute in A. discriminate A.
           - apply in_set_cons_elim in A; auto.
             destruct A as [A | A].
             + simpl. apply symV in A.
               rewrite A.
               case_eq(in_set eqV X a); intro B. 
               * assert (C := IHX _ B).
                 assert (D := in_set_right_congruence _ eqV symV trnV _ _ _ A B).
                 rewrite D. exact C. 
               * case_eq(in_set eqV X b); intro C.
                 -- apply symV in A.
                    rewrite  (in_set_right_congruence _ eqV symV trnV _ _ _ A C) in B.
                    discriminate B. 
                 -- assert (D : (X / a) = X).
                    {
                      apply remove_no_op; auto. 
                    } 
                    rewrite D.
                    apply perm_eqv_skip; auto.
                    apply PermutationEqv_reflexive. 
             + simpl.
               case_eq(in_set eqV X b); intro B;
               case_eq(eqV a b); intro C.                   
               * apply IHX; auto. 
               * simpl.
                 assert (D : in_set eqV (X / a) b = true).
                 {
                   apply in_set_remove_equal_elements_from_list_intro; auto.
                   case_eq(eqV b a); intro D; auto.
                   apply symV in D. rewrite D in C.
                   discriminate C. 
                 } 
                 rewrite D.
                 apply IHX; auto. 
               * rewrite (in_set_right_congruence _ eqV symV trnV _ _ _ C A) in B.
                 discriminate B. 
               * simpl.
                 assert (D : in_set eqV (X / a) b = false).
                 {
                   apply remove_not_in_set_preserved; auto. 
                 } 
                 rewrite D.
                 assert (E := IHX _ A).
                 assert (F := perm_eqv_skip _ _   _ _ (refV b) E).
                 assert (G : PermutationEqv (a :: b :: 𝛿 (X / a)) (b :: a :: 𝛿 (X / a))).
                 {
                   apply perm_eqv_swap; auto. 
                 }
                 exact (perm_eqv_trans _ _ _ G F).
    Qed. 

  Lemma equal_sets_are_permuted_lists : ∀ X Y,  X =S= Y -> PermutationEqv (𝛿 X) (𝛿 Y).  
  Proof. induction X; intros Y  A.
         - apply brel_set_nil in A. rewrite A. simpl.
           exact perm_eqv_nil. 
         - simpl.
           case_eq(in_set eqV X a); intro B.
           + assert (C := simplify_brel_cons_equal _ _ _ B A).
             exact (IHX _ C).
           + destruct (simplify_brel_cons_equal_v2 _ _ _ B A) as [C' C].
             assert (D := IHX _ C).
             assert (E := Permutation_remove _ _ C').
             assert (F : PermutationEqv (a :: 𝛿 X) (a :: 𝛿 (Y / a))).
             {
               apply perm_eqv_skip; auto. 
             }
             exact (perm_eqv_trans _ _ _ F E). 
  Qed. 


  
 Lemma big_plus_set_congruence
   (eqT : brel V) 
   (h g : V -> R)
   (congh : ∀ v v' : V, v =v= v' → h v =r= h v')
   (congg : ∀ v v' : V, v =v= v' → g v =r= g v')   
   (eq_h_g : ∀ i j, eqV i j = true -> (h i) =r= (g j)):
    ∀ (X Y : finite_set V),  X =S= Y -> 
       ⨁_{X} h =r= ⨁_{Y} g. 
 Proof. intros X Y I.
        assert (A := equal_sets_are_permuted_lists _ _ I).
        assert (B := big_plus_permutation h congh _ _ A).
        assert (C := big_plus_permutation g congg _ _ A).
        assert (D : (𝛿 Y) =l= (𝛿 Y)). apply brel_list_reflexive; auto. 
        assert (E := big_plus_congruence_general V eqV h g eq_h_g _ _ D).
        assert (F := trnR _ _ _ B E).
        exact F. 
  Qed.


  Lemma big_plus_set_cons (f : V -> R) :
    ∀ a X,  a ∉ X -> ⨁_{a :: X} f =r= (f a) ⊕ (⨁_{X} f).
  Proof. intros a X A.
         unfold big_plus_set at 1. 
         apply uop_duplicate_elim_lemma_2 in A.
         rewrite A. 
         unfold big_plus_set.
         apply big_plus_cons. 
  Qed. 

  Lemma big_plus_set_ignore_cons (f : V -> R) :
    ∀ a X,  a ∈ X -> ⨁_{a :: X} f =r= ⨁_{X} f. 
  Proof.  intros a X A.
          unfold big_plus_set.
          apply uop_duplicate_elim_lemma_3 in A.
          rewrite A. apply refR. 
  Qed.

  Lemma big_plus_ignore_cons (f : V -> R)
    (congf : ∀ v v' : V, v =v= v' → f v =r= f v')                             
    (idemP : bop_idempotent _ eqR plus) : 
    ∀ l a,  a ∈' l -> ⨁_(a :: l) f =r= ⨁_(l) f. 
  Proof. induction l as [ | b l]; intros a A.
         - compute in A; discriminate A.
         - assert (B := big_plus_cons f a (b :: l)).
           assert (C := big_plus_cons f b l).
           assert (D := congrP _ _ _ _ (refR (f a)) C). 
           assert (E := trnR _ _ _ B D).
           assert (F := assoc (f a) (f b) (⨁_(l) f)).
           apply symR in F.
           assert (G := trnR _ _ _ E F).
           apply in_list_cons_elim in A; auto.
           destruct A as [A | A].
           + assert (H := idemP (f a)).
             assert (I := congf _ _ A). apply symR in I.
             assert (J := congrP _ _ _ _ (refR (f a)) I).
             apply symR in J. 
             assert (K := trnR _ _ _ J (trnR _ _ _ H I)).
             assert (L := congrP _ _ _ _ K (refR (⨁_(l) f))).
             assert (M := trnR _ _ _ G L).
             assert (N := big_plus_cons f b l). apply symR in N.
             exact (trnR _ _ _ M N). 
           + assert (H := comm (f a) (f b)).
             assert (I := congrP _ _ _ _ H (refR (⨁_(l) f))).
             assert (J := trnR _ _ _ G I).
             assert (K := big_plus_cons f a l).
             apply symR in K.
             assert (L := IHl _ A).
             assert (M := trnR _ _ _ K L).
             assert (O := congrP _ _ _ _ (refR (f b)) M).
             assert (P := assoc (f b) (f a) (⨁_(l) f)).
             assert (Q := trnR _ _ _ J P).
             assert (T := trnR _ _ _ Q O). apply symR in C.
             exact (trnR _ _ _ T C). 
  Qed.

  Lemma equal_in_set_in_list : 
    ∀ X a, in_set eqV X a = in_list eqV X a. 
  Proof. induction X as [ | b X]; intro a.
         + compute. reflexivity.
         + simpl. unfold bop_or.
           rewrite (IHX a). 
           reflexivity.
  Qed. 

  Lemma idempotence_implies_big_sum_set_is_big_sum (f : V -> R)
    (congf : ∀ v v' : V, v =v= v' → f v =r= f v')                                                                                
    (idemP : bop_idempotent _ eqR plus) :
    ∀ X, ⨁_{X} f =r= ⨁_(X) f.
  Proof. induction X as [ | a X]. 
         - compute. apply refR.
         - case_eq(in_set eqV X a); intro A.
           + assert (B := big_plus_set_ignore_cons f _ _ A).
             assert (C := trnR _ _ _ B IHX). 
             rewrite equal_in_set_in_list in A. 
             assert (D := big_plus_ignore_cons f congf idemP _ _ A).
             apply symR in D. 
             exact (trnR _ _ _ C D). 
           + assert (B := big_plus_cons f a X).
             apply (big_plus_set_cons f) in A.
             assert (C := congrP _ _ _ _ (refR (f a)) IHX).
             assert (D := trnR _ _ _ A C). 
             apply symR in B.
             exact (trnR _ _ _ D B). 
  Qed. 
  
  Lemma big_plus_set_cons_with_idempotence (f : V -> R)
    (congf : ∀ v v' : V, v =v= v' → f v =r= f v')                                            
    (idemP : bop_idempotent _ eqR plus) :
    ∀ X a,  ⨁_{a :: X} f =r= (f a) ⊕ ⨁_{X} f.
  Proof. intros X a.
         assert (A := idempotence_implies_big_sum_set_is_big_sum f congf idemP X).
         assert (B := idempotence_implies_big_sum_set_is_big_sum f congf idemP (a :: X)).
         assert (C := big_plus_cons f a X). 
         assert (D := trnR _ _ _ B C).
         apply symR in A.
         assert (E := congrP _ _ _ _ (refR (f a)) A). 
         exact (trnR _ _ _ D E). 
  Qed. 

  Lemma big_plus_set_distributes_over_union
    (idemP : bop_idempotent _ eqR plus)
    (g : V -> R)
    (cong_g : ∀ i j, eqV i j = true -> (g i) =r= (g j)):
    ∀ X Y,  (⨁_{X} g) ⊕ (⨁_{Y} g) =r= ⨁_{X ∪ Y} g. 
  Proof. induction X; intro Y.
         - unfold big_plus_set at 1. simpl.
           unfold big_plus. simpl.
           destruct (zeroID (⨁_{Y} g)) as [A _].
           assert (B : Y =S= ([] ∪ Y)).
           {
             apply brel_set_symmetric; auto. 
             apply bop_union_with_nil_left; auto. 
           } 
           assert (C := big_plus_set_congruence eqV g g cong_g cong_g cong_g _ _ B).
           exact (trnR _ _ _ A C). 
         - case_eq(in_set eqV (X ∪ Y) a); intro A.
           + assert (B := big_plus_set_ignore_cons g _ _ A).
             case_eq(in_set eqV X a); intro C.
             * assert (D := big_plus_set_ignore_cons g _ _ C).
               assert (E := congrP _ _ _ _ D (refR (⨁_{ Y} g))).
               assert (F := IHX Y).
               assert (G := trnR _ _ _ E F). apply symR in B.
               assert (H : a :: (X ∪ Y) =S= ((a :: X) ∪ Y)).
               {
                 apply bop_union_push_element; auto. 
               } 
               assert (I : (⨁_{ a :: (X ∪ Y)} g) =r= (⨁_{ (a :: X) ∪ Y} g)).
               {
                 apply big_plus_set_congruence; auto. 
               } 
               exact (trnR _ _ _ G (trnR _ _ _ B I)). 
             * assert (D : a ∈ Y).
               {
                 apply in_set_bop_union_elim in A; auto.
                 destruct A as [A | A]; auto. 
                 -- rewrite A in C. discriminate C.
               }
               (*
                (⨁_{ a :: X} g) ⊕ (⨁_{ Y} g) 
                =r=        
               ((g a) ⊕ ⨁_{X} g) ⊕ (⨁_{ Y} g)    
                =r=         
               (⨁_{X} g ⊕ (g a)) ⊕ (⨁_{ Y} g)    
                =r=        
               ⨁_{X} g ⊕ ((g a)) ⊕ (⨁_{ Y} g)) 
                =r=  big_plus_with_idempotence
               ⨁_{X} g ⊕ (⨁_{ a :: Y} g)) 
                =r=  IHX        
               (⨁_{ X ∪ (a :: Y)} g)
                =r=  
               (⨁_{ (a :: X) ∪ Y} g)
                *)
               assert (E := big_plus_set_cons g _ _ C).
               assert (F := congrP _ _ _ _ E (refR (⨁_{ Y} g))).
               assert (G := comm (g a) (⨁_{ X} g)).
               assert (H := congrP _ _ _ _ G (refR (⨁_{ Y} g))).
               assert (I := trnR _ _ _ F H).
               assert (J := assoc (⨁_{ X } g) (g a) (⨁_{ Y } g)).
               assert (K := trnR _ _ _ I J).
               assert (L := big_plus_set_cons_with_idempotence g cong_g idemP Y a).
               apply symR in L. 
               assert (M := congrP _ _ _ _(refR (⨁_{X} g)) L).
               assert (N := trnR _ _ _ K M).
               assert (O := IHX (a :: Y)).
               assert (P : (X ∪ a :: Y) =S= (a :: X ∪ Y)).
               {
                 assert (Z := bop_union_shift_element _ _ refV symV trnV Y X a).
                 apply brel_set_symmetric; auto. 
               } 
               assert (Q := big_plus_set_congruence eqV g g cong_g cong_g cong_g _ _ P).
               assert (S := trnR _ _ _ N O).
               exact (trnR _ _ _ S Q). 
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
             assert (D := big_plus_set_congruence eqV g g cong_g cong_g cong_g _ _ C).
             apply (big_plus_set_cons g) in A. 
             apply (big_plus_set_cons g) in B.
             assert (E := trnR _ _ _ D A). apply symR in E.
             assert (F := congrP _ _ _ _ B (refR (⨁_{Y} g))).
             assert (G := assoc (g a) (⨁_{X} g) (⨁_{Y} g)).
             assert (H := trnR _ _ _ F G).
             assert (I := congrP _ _ _ _ (refR (g a)) (IHX Y)).
             assert (J := trnR _ _ _ H I).
             exact (trnR _ _ _ J E). 
  Qed. 


(************** BIG UNION ***************************)
  Definition zero_set : finite_set V := [].


  Definition big_union (f : V -> finite_set V) (l : list V) : finite_set V := 
    big_plus zero_set (bop_union eqV) f l.

  Definition big_union_set (f : V -> finite_set V) (X : finite_set V) : finite_set V := 
    big_union f ((uop_duplicate_elim eqV X)).

  Local Notation "∪_( l ) f"      := (big_union f l) (at level 70).
  
  Local Notation "∪_{ X } f"      := (big_union_set f X) (at level 70).


  Lemma big_union_cons (f : V -> finite_set V):
    ∀ a l, ∪_( a :: l ) f =S= ((f a) ∪ (∪_( l ) f)).
  Proof. intros a l. apply brel_set_reflexive; auto. Qed.

  Lemma big_plus_big_union
    (idemP : bop_idempotent _ eqR plus)
    (g : V -> R)
    (cong_g : ∀ i j, eqV i j = true -> (g i) =r= (g j))
    (f : V -> finite_set V): 
    ∀ l,   ⨁_(l) (λ q, ⨁_{f q} g) =r= ⨁_{ ∪_(l) f } g.
  Proof. induction l. 
         - compute. apply refR. 
         - (*
               ⨁_(a :: l) (λ q : V, ⨁_{f q} g)
               =r= {big_plus_cons} 
               (⨁_{f a} g) ⊕ (⨁_(l) (λ q : V, ⨁_{f q} g))
               =r= {IHl, congrP} 
               (⨁_{f a} g) ⊕ (⨁_{ ∪_(l) f } g)
               =r= {big_plus_set_distributes_over_union} 
               ⨁_{ (f a) ∪ ( ∪_(l) f ) } g 
               =r= {big_union_cons, big_plus_set_congruence} 
               ⨁_{ ∪_(a :: l) f } g
            *)
           assert (A := big_plus_cons (λ q : V, ⨁_{f q} g) a l).
           simpl in A. 
           assert (B := congrP _ _ _ _ (refR (⨁_{ f a} g)) IHl).
           assert (C := trnR _ _ _ A B).
           assert (D := big_plus_set_distributes_over_union idemP g cong_g (f a) (∪_(l) f)).
           assert (E := trnR _ _ _ C D).
           assert (G := big_union_cons f a l).
           assert (H := big_plus_set_congruence eqV g g cong_g cong_g cong_g _ _ G).
           exact (trnR _ _ _ E H).
  Qed.
  
End Theory.


