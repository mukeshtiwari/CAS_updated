Require Import Coq.Bool.Bool.    
Require Import Coq.Strings.String.

Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.

Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.eqv.theory.
Require Import CAS.coq.eqv.set.
Require Import CAS.coq.eqv.product. (* some properties proved here *) 
Require Import CAS.coq.eqv.minset.  (* for bottoms *) 

Require Import CAS.coq.sg.and. 

Require Import CAS.coq.or.properties.
Require Import CAS.coq.or.structures.
Require Import CAS.coq.or.theory.
Require Import CAS.coq.or.cast_up.
Require Import CAS.coq.or.classify. 

Section Theory.

Variable S  : Type. 
Variable T  : Type.
Variable wS : S. 
Variable wT : T.

Variable eqS : brel S. 
Variable eqT : brel T.

Variable refS : brel_reflexive S eqS.
Variable symS : brel_symmetric S eqS.
Variable trnS : brel_transitive S eqS.

Variable refT : brel_reflexive T eqT.
Variable symT : brel_symmetric T eqT.
Variable trnT : brel_transitive T eqT.

Variable lteS : brel S. 
Variable lteT : brel T.

Variable lteReflS : brel_reflexive S lteS.
Variable lteReflT : brel_reflexive T lteT.
(* NB : anti-symmetry is not assumed! *) 

Variable lteTrnS : brel_transitive S lteS. 
Variable lteTrnT : brel_transitive T lteT.

Notation "a <*> b"  := (brel_product a b) (at level 15).



Lemma ord_product_not_reflexive_left : ∀ (t : T),   (brel_not_reflexive S lteS) 
               → brel_not_reflexive (S * T) (lteS <*> lteT). 
Proof. unfold brel_not_reflexive. intros t [s P]. 
        exists (s, t). compute. rewrite P. reflexivity. 
Defined. 

Lemma ord_product_not_reflexive_right : ∀ (s : S),   (brel_not_reflexive T lteT) 
               → brel_not_reflexive (S * T) (lteS <*> lteT). 
Proof. unfold brel_not_reflexive. intros s [t P]. 
        exists (s, t). compute. rewrite P. rewrite lteReflS; auto. Defined. 

Definition ord_product_reflexive_decide: 
   ∀ (s : S) (t : T),    
     brel_reflexive_decidable S lteS → 
     brel_reflexive_decidable T lteT → 
        brel_reflexive_decidable (S * T) (lteS <*> lteT)
:= λ s t dS dT,  
       match dS with 
       | inl refS => 
         match dT with 
         | inl refT     => inl _ (brel_product_reflexive S T lteS lteT refS refT)
         | inr not_refT => inr _ (ord_product_not_reflexive_right s not_refT)
         end 
       | inr not_refS   => inr _ (ord_product_not_reflexive_left t not_refS)
       end. 

Lemma ord_product_irreflexive_left : brel_irreflexive S lteS -> brel_irreflexive (S * T) (lteS <*> lteT). 
Proof. unfold brel_irreflexive. intros irr [s t]. compute. rewrite (irr s). reflexivity. Defined. 

Lemma ord_product_irreflexive_right : brel_irreflexive T lteT -> brel_irreflexive (S * T) (lteS <*> lteT). 
Proof. unfold brel_irreflexive. intros irr [s t]. compute. rewrite (irr t). case_eq(lteS s s); intro H; auto. Defined. 

Lemma ord_product_not_irreflexive : brel_not_irreflexive S lteS -> brel_not_irreflexive T lteT -> 
           brel_not_irreflexive (S * T) (lteS <*> lteT). 
Proof. unfold brel_not_irreflexive. intros [s P] [t Q]. exists (s, t). compute. rewrite P, Q; auto. Defined. 

Definition ord_product_irreflexive_decide: 
     brel_irreflexive_decidable S lteS → 
     brel_irreflexive_decidable T lteT → 
        brel_irreflexive_decidable (S * T) (lteS <*> lteT)
:= λ dS dT,  
       match dS with 
       | inl irrS => inl _ (ord_product_irreflexive_left irrS)
       | inr not_irrS   => 
         match dT with 
         | inl irrT     => inl _ (ord_product_irreflexive_right irrT)
         | inr not_irrT => inr _ (ord_product_not_irreflexive not_irrS not_irrT)
         end 
       end. 



Lemma ord_product_antisymmetric :
  (brel_antisymmetric S eqS lteS) → (brel_antisymmetric T eqT lteT)
  → brel_antisymmetric (S * T) (eqS <*> eqT) (lteS <*> lteT). 
Proof. intros AS AT [s1 t1] [s2 t2]; simpl. 
       intros A B.
       apply bop_and_elim in A. destruct A as [A1 A2].
       apply bop_and_elim in B. destruct B as [B1 B2].
       apply bop_and_intro; auto. 
Qed. 

Lemma ord_product_not_antisymmetric_left : brel_not_antisymmetric S eqS lteS → 
         brel_not_antisymmetric (S * T) (eqS <*> eqT) (lteS <*> lteT). 
Proof. intros [ [s1 s2] [[A B] C]]. 
       exists ((s1, wT), (s2, wT)). compute. 
       rewrite A. rewrite B. rewrite C.  rewrite lteReflT. auto. 
Defined. 

Lemma ord_product_not_antisymmetric_right : brel_not_antisymmetric T eqT lteT → 
         brel_not_antisymmetric (S * T) (eqS <*> eqT) (lteS <*> lteT). 
Proof. intros [ [t1 t2] [[A B] C]]. 
       exists ((wS, t1), (wS, t2)). compute. 
       rewrite A. rewrite B. rewrite C.  rewrite (lteReflS wS).
       case_eq(eqS wS wS); intro D; auto. 
Defined. 



Definition ord_product_antisymmetric_decide
    (dS : brel_antisymmetric_decidable S eqS lteS)
    (dT : brel_antisymmetric_decidable T eqT lteT) : 
      brel_antisymmetric_decidable (S * T) (eqS <*> eqT) (lteS <*> lteT) := 
       match dS with 
       | inl asymS => 
         match dT with 
         | inl asymT     => inl _ (ord_product_antisymmetric asymS asymT)
         | inr not_asymT => inr _ (ord_product_not_antisymmetric_right not_asymT)
         end 
       | inr not_asymS   => inr _ (ord_product_not_antisymmetric_left not_asymS)
       end.


Lemma ord_product_exists_qo_bottom :
  (brel_exists_qo_bottom S eqS lteS) → (brel_exists_qo_bottom T eqT lteT)
  → brel_exists_qo_bottom (S * T) (eqS <*> eqT) (lteS <*> lteT). 
Proof. intros [s [A B]] [t [C D]]. exists (s, t). split. 
     intros [a b]. compute. rewrite (A a). rewrite (C b); auto. 
     intros [a b]. compute.
     case_eq(lteS s a); intro E; case_eq(lteS a s); intro F; intros I J; auto. 
     rewrite (B _ E F). rewrite (D _ I J); auto. 
     discriminate J. discriminate I. discriminate J. 
Defined. 


Lemma ord_product_not_exists_qo_bottom_left :
  (brel_not_exists_qo_bottom S eqS lteS) → brel_not_exists_qo_bottom (S * T) (eqS <*> eqT) (lteS <*> lteT). 
Proof. intros N (s, t). destruct (N s) as [[w L] | [w [[A B] C]]]. 
       left. exists (w, t). compute. rewrite L; auto. 
       right. exists (w, t). compute. rewrite A, B, C. 
       rewrite (lteReflT t). auto. 
Defined. 

Lemma ord_product_not_exists_qo_bottom_right :
  (brel_not_exists_qo_bottom T eqT lteT) → brel_not_exists_qo_bottom (S * T) (eqS <*> eqT) (lteS <*> lteT). 
Proof. intros N (s, t). destruct (N t) as [[w L] | [w [[A B] C]]]. 
       left. exists (s, w). compute. rewrite L. rewrite (lteReflS s); auto. 
       right. exists (s, w). compute. rewrite A, B, C. 
       rewrite (lteReflS s), (refS s); auto. 
Defined.


Definition ord_product_exists_qo_bottom_decide 
     (DS : brel_exists_qo_bottom_decidable S eqS lteS)
     (DT : brel_exists_qo_bottom_decidable T eqT lteT) : 
           brel_exists_qo_bottom_decidable (S * T) (eqS <*> eqT) (lteS <*> lteT) := 
match DS with 
| inl botS  => match DT with
               | inl botT => inl (ord_product_exists_qo_bottom botS botT)
               | inr nbot => inr (ord_product_not_exists_qo_bottom_right nbot)
               end 
| inr nbot => inr (ord_product_not_exists_qo_bottom_left nbot)
end.


Lemma ord_product_exists_qo_top :
  (brel_exists_qo_top S eqS lteS) → (brel_exists_qo_top T eqT lteT)
  → brel_exists_qo_top (S * T) (eqS <*> eqT) (lteS <*> lteT). 
Proof. intros [s [A B]] [t [C D]]. exists (s, t). split. 
     intros [a b]. compute. rewrite (A a). rewrite (C b); auto. 
     intros [a b]. compute.
     case_eq(lteS s a); intro E; case_eq(lteS a s); intro F; intros I J; auto. 
     rewrite (B _ E F). rewrite (D _ I J); auto. 
     discriminate J. discriminate I. discriminate J. 
Defined. 

Lemma ord_product_not_exists_qo_top_left :
  (brel_not_exists_qo_top S eqS lteS) 
  → brel_not_exists_qo_top (S * T) (eqS <*> eqT) (lteS <*> lteT). 
Proof. intros N (s, t). destruct (N s) as [[w L] | [w [[A B] C]]]. 
       left. exists (w, t). compute. rewrite L; auto. 
       right. exists (w, t). compute. rewrite A, B, C. 
       rewrite (lteReflT t). auto. 
Defined. 


Lemma ord_product_not_exists_qo_top_right :
  (brel_not_exists_qo_top T eqT lteT) 
  → brel_not_exists_qo_top (S * T) (eqS <*> eqT) (lteS <*> lteT). 
Proof. intros N (s, t). destruct (N t) as [[w L] | [w [[A B] C]]]. 
       left. exists (s, w). compute. rewrite L. rewrite (lteReflS s); auto. 
       right. exists (s, w). compute. rewrite A, B, C. 
       rewrite (lteReflS s), (refS s); auto. 
Defined. 


Definition ord_product_exists_qo_top_decide 
     (DS : brel_exists_qo_top_decidable S eqS lteS)
     (DT : brel_exists_qo_top_decidable T eqT lteT) : 
           brel_exists_qo_top_decidable (S * T) (eqS <*> eqT) (lteS <*> lteT) := 
match DS with 
| inl topS  => match DT with
               | inl topT => inl (ord_product_exists_qo_top topS topT)
               | inr ntop => inr (ord_product_not_exists_qo_top_right ntop)
               end 
| inr ntop => inr (ord_product_not_exists_qo_top_left ntop)
end.


(* normal top/bottom *) 


Lemma ord_product_exists_bottom :
  (brel_exists_bottom S lteS) → (brel_exists_bottom T lteT)
  → brel_exists_bottom (S * T) (lteS <*> lteT). 
Proof. intros [s A] [t C]. exists (s, t). intros [a b]. compute. rewrite A, C; auto. Defined. 

Lemma ord_product_not_exists_bottom_left :
  (brel_not_exists_bottom S lteS) → brel_not_exists_bottom (S * T) (lteS <*> lteT). 
Proof. intros N [s t]. destruct (N s) as [w L]. exists (w, t). compute. rewrite L; auto. Defined. 

Lemma ord_product_not_exists_bottom_right :
  (brel_not_exists_bottom T lteT) → brel_not_exists_bottom (S * T) (lteS <*> lteT). 
Proof. intros N [s t]. destruct (N t) as [w R]. exists (s, w). compute. rewrite lteReflS, R; auto. Defined. 

Definition ord_product_exists_bottom_decide 
     (DS : brel_exists_bottom_decidable S lteS)
     (DT : brel_exists_bottom_decidable T lteT) : 
           brel_exists_bottom_decidable (S * T) (lteS <*> lteT) := 
match DS with 
| inl botS  => match DT with
               | inl botT => inl (ord_product_exists_bottom botS botT)
               | inr nbot => inr (ord_product_not_exists_bottom_right nbot)
               end 
| inr nbot => inr (ord_product_not_exists_bottom_left nbot)
end.

Lemma ord_product_exists_top :
  (brel_exists_top S lteS) → (brel_exists_top T lteT)
  → brel_exists_top (S * T) (lteS <*> lteT). 
Proof. intros [s A] [t C]. exists (s, t). intros [a b]. compute. rewrite A, C; auto. Defined. 

Lemma ord_product_not_exists_top_left :
  (brel_not_exists_top S lteS) → brel_not_exists_top (S * T) (lteS <*> lteT). 
Proof. intros N (s, t). destruct (N s) as [w L]. exists (w, t). compute. rewrite L; auto. Defined. 

Lemma ord_product_not_exists_top_right :
  (brel_not_exists_top T lteT) → brel_not_exists_top (S * T) (lteS <*> lteT). 
Proof. intros N (s, t). destruct (N t) as [w R]. exists (s, w). compute. rewrite lteReflS, R; auto. Defined. 

Definition ord_product_exists_top_decide 
     (DS : brel_exists_top_decidable S lteS)
     (DT : brel_exists_top_decidable T lteT) : 
           brel_exists_top_decidable (S * T) (lteS <*> lteT) := 
match DS with 
| inl topS  => match DT with
               | inl topT => inl (ord_product_exists_top topS topT)
               | inr ntop => inr (ord_product_not_exists_top_right ntop)
               end 
| inr ntop => inr (ord_product_not_exists_top_left ntop)
end.


Close Scope nat_scope. 

Lemma or_product_trivial (TS : order_trivial S lteS) (TT : order_trivial T lteT) : 
  order_trivial (S * T) (lteS <*> lteT).
Proof. intros [s1 t1]  [s2 t2]. compute. 
       rewrite (TS s1 s2). rewrite (TT t1 t2). 
       reflexivity.
Qed.

Lemma or_product_not_trivial_left (TS : order_not_trivial S lteS) : 
          order_not_trivial (S * T) (lteS <*> lteT).
Proof. destruct TS as [[s1 s2] A]. 
       exists ((s1, wT), (s2, wT)). compute.
       rewrite A. reflexivity.
Defined. 

Lemma or_product_not_trivial_right (TT : order_not_trivial T lteT) : 
          order_not_trivial (S * T) (lteS <*> lteT).
Proof. destruct TT as [[t1 t2] A]. 
       exists ((wS, t1), (wS, t2)). compute.
       rewrite A. rewrite lteReflS. reflexivity.
Defined.

Definition ord_product_order_trivial_decide 
     (trvS_d : order_trivial_decidable S lteS)
     (trvT_d : order_trivial_decidable T lteT): 
        order_trivial_decidable (S * T) (lteS <*> lteT) := 
       match trvS_d with 
       | inl trvS => 
         match trvT_d with 
         | inl trvT  => inl (or_product_trivial trvS trvT)
         | inr ntrvT => inr (or_product_not_trivial_right ntrvT)
         end 
       | inr ntrvS   => inr (or_product_not_trivial_left ntrvS)
       end. 



Lemma ord_product_total (TS : order_trivial S lteS) (TT : order_trivial T lteT) : 
       brel_total (S * T) (lteS <*> lteT). 
Proof. exact (order_trivial_implies_total _ _ (or_product_trivial TS TT)). Qed.

Lemma ord_product_total_left (totS : brel_total S lteS) (TT : order_trivial T lteT) : 
       brel_total (S * T) (lteS <*> lteT). 
Proof. intros [s1 t1]  [s2 t2]. compute. 
       rewrite (TT t1 t2). rewrite (TT t2 t1).
       destruct (totS s1 s2) as [A | A]; rewrite A. 
       + left. reflexivity. 
       + right. reflexivity. 
Qed. 

Lemma ord_product_total_right (TS : order_trivial S lteS) (totT : brel_total T lteT) : 
       brel_total (S * T) (lteS <*> lteT). 
Proof. intros [s1 t1]  [s2 t2]. compute. 
       rewrite (TS s1 s2). rewrite (TS s2 s1).
       destruct (totT t1 t2) as [A | A]; rewrite A. 
       + left. reflexivity. 
       + right. reflexivity. 
Qed. 

Lemma ord_product_not_total :
      brel_total S lteS ->
      brel_total T lteT ->
      order_not_trivial S lteS ->
      order_not_trivial T lteT ->  brel_not_total (S * T) (lteS <*> lteT). 
Proof. intros TS TT [[s1 s2] P] [[t1 t2] Q].
       exists ((s2, t1), (s1, t2)). 
       destruct (TS s1 s2) as [A | A].
       + rewrite A in P. discriminate P. 
       + destruct (TT t1 t2) as [B | B]. 
         ++ rewrite B in Q. discriminate Q. 
         ++ compute. rewrite A, P, Q. auto.  
Defined.

Lemma ord_product_not_total_left :
   brel_not_total S lteS -> brel_not_total (S * T) (lteS <*> lteT). 
Proof. intros [[s1 s2] [A B]]. exists ((s1, wT), (s2, wT)). compute. 
       rewrite A, B; auto. 
Defined.


Lemma ord_product_not_total_right (lteRef : brel_reflexive S lteS):
   brel_not_total T lteT -> brel_not_total (S * T) (lteS <*> lteT). 
Proof. intros [[t1 t2] [A B]]. exists ((wS, t1), (wS, t2)). compute. 
       rewrite A, B; auto. rewrite (lteRef wS). auto. 
Defined.

Definition ord_product_total_decide
           (totS_d : brel_total_decidable S lteS) 
           (totT_d : brel_total_decidable T lteT) 
           (trvS_d : order_trivial_decidable S lteS) 
           (trvT_d : order_trivial_decidable T lteT) : 
                 brel_total_decidable (S * T) (lteS <*> lteT) := 
match totS_d with
| inl totS =>
  match totT_d with
  | inl totT =>
    match trvS_d with
    | inl trvS => inl (ord_product_total_right trvS totT) 
    | inr ntrvS =>
      match trvT_d with
      | inl trvT => inl (ord_product_total_left totS trvT) 
      | inr ntrvT => inr (ord_product_not_total totS totT ntrvS ntrvT)
      end
    end 
  | inr ntotT => inr (ord_product_not_total_right lteReflS ntotT)    
  end 
| inr ntotS => inr (ord_product_not_total_left ntotS)
end.     



(* bottoms *)
Section Bottoms.

Definition bop_product_w (BS : list S) (BT : list T) (fS : S ->S) (fT : T -> T) (p : S * T) :=
  match p with (s, t) =>
               if in_set eqS BS s 
               then if in_set eqT BT t 
                    then (s, t)
                    else (s, fT t)
               else if in_set eqT BT t 
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
      in_set (eqS <*> eqT) (map_mk_pairs a BT) (s, t) = true -> (eqS a s = true) * (in_set eqT BT t = true). 
Proof. induction BT; intro H. 
          compute in H. discriminate H. 
          unfold map_mk_pairs in H. fold map_mk_pairs in H. 
          apply in_set_cons_elim in H; auto. 
          destruct H as [H | H]. 
             compute in H. 
             case_eq(eqS a s); intro G. 
                 rewrite G in H. split; auto. 
                 apply in_set_cons_intro; auto. 
                 rewrite G in H. discriminate H. 

             destruct (IHBT H) as [J K]. 
             split; auto. 
                apply in_set_cons_intro; auto. 
          apply brel_product_symmetric; auto. 
Qed.

Lemma in_set_product_elim (s : S) (t : T) (BS : list S) (BT : list T) :
  in_set (eqS <*> eqT) (set_product BS BT) (s, t) = true -> (in_set eqS BS s = true) * (in_set eqT BT t = true).
Proof. induction BS; intro H. 
       compute in H. discriminate H.
       unfold set_product in H. fold set_product in H.
       apply in_set_concat_elim in H; auto. 
       destruct H as [H | H]. 
          apply in_set_map_mk_pairs_elim in H; auto. destruct H as [H1 H2].
          split; auto. 
             apply in_set_cons_intro; auto. 
       
          destruct (IHBS H) as [J K].        
          split; auto. 
             apply in_set_cons_intro; auto. 
             apply brel_product_symmetric; auto. 
Qed.


Lemma in_set_map_mk_pairs_intro (a s : S) (t : T) (BT : list T): 
    (eqS a s = true) -> (in_set eqT BT t = true) -> in_set (eqS <*> eqT) (map_mk_pairs a BT) (s, t) = true.
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

Lemma in_set_product_intro (s : S) (t : T) (BS : list S) (BT : list T) :
 (in_set eqS BS s = true) -> (in_set eqT BT t = true) -> in_set (eqS <*> eqT) (set_product BS BT) (s, t) = true. 
Proof. intros A B. induction BS. 
          compute in A. discriminate A. 

          unfold set_product. fold set_product. 
          apply in_set_concat_intro; auto. 
          apply in_set_cons_elim in A; auto.           
          destruct A as [A | A]. 
             left. apply in_set_map_mk_pairs_intro; auto. 
             right. exact (IHBS A). 
Qed. 

Lemma set_product_is_antichain (BS : list S) (BT : list T) :
  is_antichain S eqS lteS BS -> is_antichain T eqT lteT BT -> 
  is_antichain (S * T) (eqS <*> eqT) (lteS <*> lteT) (set_product BS BT).
Proof. unfold is_antichain. intros IS IT.
       intros [s1 t1] H1 [s2 t2] H2.
       apply in_set_product_elim in H1; auto. destruct H1 as [H1L H1R].
       apply in_set_product_elim in H2; auto.  destruct H2 as [H2L H2R].
       assert (H3 := IS s1 H1L s2 H2L). apply equiv_or_incomp_elim in H3.
       assert (H4 := IT t1 H1R t2 H2R). apply equiv_or_incomp_elim in H4.
       apply equiv_or_incomp_intro. 
       destruct H3 as [A |A]; destruct H4 as [C | C]. 
          left. apply equiv_intro.
             compute. apply equiv_elim in A. apply equiv_elim in C. 
             destruct A as [A B]; destruct C as [C D]. 
             rewrite A, C. reflexivity.
             
             compute. apply equiv_elim in A. apply equiv_elim in C. 
             destruct A as [A B]; destruct C as [C D]. 
             rewrite B, D. reflexivity. 

             
          right. apply incomp_intro. 
             compute. apply equiv_elim in A. apply incomp_elim in C. 
             destruct A as [A B]; destruct C as [C D]. 
             rewrite A, C. reflexivity.
             
             compute. apply equiv_elim in A. apply incomp_elim in C. 
             destruct A as [A B]; destruct C as [C D]. 
             rewrite B, D. reflexivity. 
          
          right. apply incomp_intro. 
             compute. apply incomp_elim in A. apply equiv_elim in C. 
             destruct A as [A B]; destruct C as [C D]. 
             rewrite A. reflexivity.
             
             compute. apply incomp_elim in A. apply equiv_elim in C. 
             destruct A as [A B]; destruct C as [C D]. 
             rewrite B. reflexivity. 

          right. apply incomp_intro. 
             compute. apply incomp_elim in A. apply incomp_elim in C. 
             destruct A as [A B]; destruct C as [C D]. 
             rewrite A. reflexivity.
             
             compute. apply incomp_elim in A. apply incomp_elim in C. 
             destruct A as [A B]; destruct C as [C D]. 
             rewrite B. reflexivity. 
Qed. 


Lemma ord_product_bottoms_set_is_finite :
  (bottoms_set_is_finite S eqS lteS) → (bottoms_set_is_finite T eqT lteT)
  → bottoms_set_is_finite (S * T) (eqS <*> eqT) (lteS <*> lteT). 
Proof. unfold bottoms_set_is_finite. 
       intros [[BS fS] [IS PS]] [[BT fT] [IT PT]]. 
       exists (set_product BS BT, bop_product_w BS BT fS fT). split. 
          apply set_product_is_antichain; auto.   
          intros [s t]. unfold bop_product_w.
          (* assert (iS := idemS s). apply symS in iS.
          assert (iT := idemT t). apply symT in iT.            *) 
          destruct (PS s) as [A | [A B]];
          destruct (PT t) as [D | [D E]]. 
             left. apply in_set_product_intro; auto.

             rewrite A. case_eq(in_set eqT BT t); intro G. 
                left. apply in_set_product_intro; auto.
                right. split. 
                   apply in_set_product_intro; auto.
                   apply below_intro. 
                      compute. rewrite lteReflS. apply below_elim in E. destruct E as [E _]. exact E. 
                      compute. rewrite lteReflS. apply below_elim in E. destruct E as [_ E]. exact E. 

             rewrite D. case_eq(in_set eqS BS s); intro G. 
                left. apply in_set_product_intro; auto.
                right. split. 
                   apply in_set_product_intro; auto.
                   apply below_intro. 
                      compute. apply below_elim in B. destruct B as [B _]. rewrite B. apply lteReflT. 
                      compute. apply below_elim in B. destruct B as [_ B]. rewrite B. reflexivity. 

             case_eq(in_set eqS BS s); intro G; case_eq(in_set eqT BT t); intro H.
                left. apply in_set_product_intro; auto. 

                right. split. 
                   apply in_set_product_intro; auto. 
                   apply below_intro. 
                      compute. rewrite lteReflS. apply below_elim in E. destruct E as [E _]. exact E. 
                      compute. rewrite lteReflS. apply below_elim in E. destruct E as [_ E]. exact E. 

                right. split. 
                   apply in_set_product_intro; auto. 
                   apply below_intro. 
                      compute.  apply below_elim in B. destruct B as [B _]. rewrite B. apply lteReflT. 
                      compute. apply below_elim in B. destruct B as [_ B]. rewrite B. reflexivity. 

                right. split. 
                   apply in_set_product_intro; auto. 
                   apply below_intro. 
                      compute. apply below_elim in B. destruct B as [B _]. rewrite B. 
                               apply below_elim in E. destruct E as [E _]. exact E. 
                      compute. apply below_elim in B. destruct B as [_ B]. rewrite B. 
                               apply below_elim in E. destruct E as [_ E]. reflexivity. 
Qed. 


Definition set_product_proj1 (B : finite_set (S * T)) : finite_set S :=
  List.map (λ p, match p with (s, _) => s end) B.

Definition set_product_proj2 (B : finite_set (S * T)) : finite_set T :=
  List.map (λ p, match p with (_, t) => t end) B.

(*
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

*)
Lemma in_set_product_proj1_elim (B : finite_set (S * T)) :
  ∀ (s : S),  
     in_set eqS (set_product_proj1 B) s = true -> {t : T & in_set (eqS <*> eqT) B (s, t) = true}. 
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


(* For the cases of bottoms_set_not_is_finite 
   we need to extract antichains over S or T from an antichain over S * T. 
   Just doing simple projections doesn't work.  For example, suppose 

    (s2, t2) # (s1, t1)

   There are two situations where the neither projection will be an antichain. 
    That is [(s1 < s2) and (t2 < t1)] 
    and [(s2 < s1) and (t1 < t2)].  

    The solution is to take minsets of projections! 

 *)


Definition negation_v1 (X : finite_set (S * T)) : finite_set S :=
      uop_minset lteS (set_product_proj1 X). 

Definition negation_v2 (X : finite_set (S * T)) : finite_set T :=
     uop_minset lteT (set_product_proj2 X). 


Definition product_not_finite_v1 (F : finite_set S -> S) (B : finite_set (S * T)) : S * T :=
     (F (negation_v1 B), wT). 

Definition product_not_finite_v2 (F : finite_set T -> T) (X : finite_set (S * T)) : S * T :=
     (wS, F (negation_v2 X)). 


Lemma negation_v1_is_antichain (B : finite_set (S * T)) : is_antichain S eqS lteS (negation_v1 B).
Admitted.

Lemma negation_v2_is_antichain (B : finite_set (S * T)) : is_antichain T eqT lteT (negation_v2 B).
Admitted.

Lemma lemma10 (F : finite_set S -> S) (B : finite_set (S * T)) : 
     in_set (eqS <*> eqT) B (F (negation_v1 B), wT) = true
     -> in_set eqS (negation_v1 B) (F (negation_v1 B)) = true. 
Admitted.


Lemma in_set_negation_v1_intro (B : finite_set (S * T)) :
  ∀ (s : S) (t : T) ,  
     in_set (eqS <*> eqT) B (s, t) = true -> in_set eqS (negation_v1 B) s = true. 
Admitted. 

(* need glb on T *) 
Lemma ord_product_something_not_is_finite_v1 : 
  bottoms_set_not_is_finite S eqS lteS →
     bottoms_set_not_is_finite (S * T) (eqS <*> eqT) (lteS <*> lteT).
Proof. unfold bottoms_set_not_is_finite.
       intros [F A].
       exists (product_not_finite_v1 F).
       intros B I. 
       assert (C := negation_v1_is_antichain B).
       destruct (A (negation_v1 B) C) as [D E]. 
       unfold product_not_finite_v1.
       split. 
          case_eq(in_set (eqS <*> eqT) B (F (negation_v1 B), wT)); intro G; auto.
             apply lemma10 in G. rewrite G in D. discriminate D. 
          
          intros [s t] G. 
          assert (G' := in_set_negation_v1_intro _ _ _ G).
          apply below_false_intro.
          assert (H := E s G').           apply below_false_elim in H. 
          destruct H as [H | H].
             left. unfold brel_product. rewrite H. compute. reflexivity.

             unfold brel_product. 
             case_eq(lteT t wT); intro K;  case_eq(lteT wT t); intro J.  
                rewrite H. right. compute. reflexivity. 

                left. case_eq(lteS s (F (negation_v1 B)) ); intro L; auto. 
                   admit. 
                
                rewrite H. right. compute. reflexivity. 

                left. apply bop_and_false_intro. right. reflexivity. 
Admitted.

(*
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
End Bottoms. 
End Theory.

Section ACAS.

Section Proofs.
    
Variables (S T : Type) 
          (eqS : brel S) (wS : S) (eqvPS : eqv_proofs S eqS) 
          (eqT : brel T) (wT : T) (eqvPT : eqv_proofs T eqT) 
          (lteS : brel S)
          (lteT : brel T).
          
Definition qo_product_proofs (P : qo_proofs S eqS lteS)  (Q : qo_proofs T eqT lteT) :
  qo_proofs (S * T) (brel_product eqS eqT) (brel_product lteS lteT) :=
let symS     := A_eqv_symmetric _ _ eqvPS in
let symT     := A_eqv_symmetric _ _ eqvPT in  
let lteReflS := A_qo_reflexive _ _ _ P in
let lteReflT := A_qo_reflexive _ _ _ Q in
let lteTrnS  := A_qo_transitive _ _ _ P in
let lteTrnT  := A_qo_transitive _ _ _ Q in    
{|
  A_qo_congruence        := brel_product_congruence S T eqS eqT lteS lteT
                                (A_qo_congruence S eqS lteS P) 
                                (A_qo_congruence T eqT lteT Q)                                                    
; A_qo_reflexive         := brel_product_reflexive S T lteS lteT lteReflS lteReflT 
; A_qo_transitive        := brel_product_transitive S T lteS lteT lteTrnS lteTrnT 
; A_qo_antisymmetric_d   := ord_product_antisymmetric_decide S T wS wT eqS eqT symS symT lteS lteT lteReflS lteReflT
                                (A_qo_antisymmetric_d S eqS lteS P)
                                (A_qo_antisymmetric_d T eqT lteT Q)
; A_qo_total_d           := ord_product_total_decide S T wS wT lteS lteT lteReflS 
                                (A_qo_total_d S eqS lteS P)
                                (A_qo_total_d T eqT lteT Q)
                                (A_qo_trivial_d S eqS lteS P)
                                (A_qo_trivial_d T eqT lteT Q)
; A_qo_trivial_d         := ord_product_order_trivial_decide S T wS wT lteS lteT lteReflS 
                                (A_qo_trivial_d S eqS lteS P)
                                (A_qo_trivial_d T eqT lteT Q)
|}.
  
End Proofs.
  
Section Combinators.


Definition A_qo_product (S T : Type) (PS : A_qo S) (PT : A_qo T) : A_qo(S * T) :=
let eqvS := A_qo_eqv _ PS in
let eqvT := A_qo_eqv _ PT in
let eqvPS := A_eqv_proofs _ eqvS in
let eqvPT := A_eqv_proofs _ eqvT in
let refS  := A_eqv_reflexive _ _ eqvPS in
let eqS  := A_eqv_eq _ eqvS in
let eqT  := A_eqv_eq _ eqvT in
let wS   := A_eqv_witness _ eqvS in
let wT   := A_eqv_witness _ eqvT in
let lteS := A_qo_lte _ PS in 
let lteT := A_qo_lte _ PT in
let botS := A_qo_exists_bottom_d _ PS in
let botT := A_qo_exists_bottom_d _ PT in
let topS := A_qo_exists_top_d _ PS in
let topT := A_qo_exists_top_d _ PT in 
let pS   := A_qo_proofs _ PS in 
let pT   := A_qo_proofs _ PT in
let lteReflS := A_qo_reflexive _ _ _ pS in
let lteReflT := A_qo_reflexive _ _ _ pT in 
{|
  A_qo_eqv             := A_eqv_product S T eqvS eqvT
; A_qo_lte             := brel_product lteS lteT 
; A_qo_exists_top_d    := ord_product_exists_qo_top_decide S T eqS eqT refS lteS lteT lteReflS lteReflT topS topT
; A_qo_exists_bottom_d := ord_product_exists_qo_bottom_decide S T eqS eqT refS lteS lteT lteReflS lteReflT botS botT 
; A_qo_proofs          := qo_product_proofs S T eqS wS eqvPS eqT wT eqvPT lteS lteT pS pT
; A_qo_ast             := Ast_or_product (A_qo_ast _ PS, A_qo_ast _ PS)
|}.

  
End Combinators. 
  
End ACAS.


Section AMCAS.

  Definition A_qo_product_below_qo {S T : Type}
    (A : @A_below_qo S)
    (B : @A_below_qo T)  : @A_below_qo (S * T) :=
    A_classify_qo (A_qo_product _ _ (A_cast_up_qo A) (A_cast_up_qo B)).

  
  Definition A_mcas_qo_product {S T : Type}
    (A : @A_qo_mcas S)
    (B : @A_qo_mcas T)  : @A_qo_mcas (S * T) :=
    match A, B with
    | A_MCAS_qo A', A_MCAS_qo B'               => A_MCAS_qo (A_qo_product_below_qo A' B')
    | A_MCAS_qo_Error sl1, A_MCAS_qo_Error sl2 => A_MCAS_qo_Error (sl1 ++ sl2)
    | A_MCAS_qo_Error sl1, _                   => A_MCAS_qo_Error sl1
    | _,  A_MCAS_qo_Error sl2                  => A_MCAS_qo_Error sl2
    end.

End AMCAS.



Section CAS.


Definition ord_product_exists_qo_top_check {S T : Type}
     (DS : @certify_exists_qo_top S )
     (DT : @certify_exists_qo_top T ) : 
           @certify_exists_qo_top (S * T) := 
match DS with 
| Certify_Exists_Qo_Top topS  => 
               match DT with
               | Certify_Exists_Qo_Top topT => Certify_Exists_Qo_Top (topS, topT)
               | Certify_Not_Exists_Qo_Top  => Certify_Not_Exists_Qo_Top  
               end 
| Certify_Not_Exists_Qo_Top => Certify_Not_Exists_Qo_Top  
end.

Definition ord_product_exists_qo_bottom_check {S T : Type}
     (DS : @certify_exists_qo_bottom S )
     (DT : @certify_exists_qo_bottom T ) : 
           @certify_exists_qo_bottom (S * T) := 
match DS with 
| Certify_Exists_Qo_Bottom botS  => 
               match DT with
               | Certify_Exists_Qo_Bottom botT => Certify_Exists_Qo_Bottom (botS, botT)
               | Certify_Not_Exists_Qo_Bottom  => Certify_Not_Exists_Qo_Bottom  
               end 
| Certify_Not_Exists_Qo_Bottom => Certify_Not_Exists_Qo_Bottom  
end.

Definition ord_product_exists_bottom_assert {S T : Type}
     (DS : @assert_exists_bottom S )
     (DT : @assert_exists_bottom T ) : 
           @assert_exists_bottom (S * T) := 
match DS with 
| Assert_Exists_Bottom botS  => 
               match DT with
               | Assert_Exists_Bottom botT => Assert_Exists_Bottom (botS, botT)
               end 
end.


Definition ord_product_antisymmetric_certify {S T : Type} (wS : S) (wT : T) 
    (dS : @certify_antisymmetric S)
    (dT : @certify_antisymmetric T) : @certify_antisymmetric (S * T) := 
       match dS with 
       | Certify_Antisymmetric => 
         match dT with 
         | Certify_Antisymmetric              => Certify_Antisymmetric
         | Certify_Not_Antisymmetric (t1, t2) => Certify_Not_Antisymmetric ((wS, t1), (wS, t2))
         end 
       | Certify_Not_Antisymmetric (s1, s2)   => Certify_Not_Antisymmetric ((s1, wT), (s2, wT))
       end.

Definition ord_product_order_trivial_certify {S T : Type} (wS : S) (wT : T) 
     (trvS_d : @order_trivial_certifiable S)
     (trvT_d : @order_trivial_certifiable T): @order_trivial_certifiable (S * T) := 
       match trvS_d with 
       | Certify_Order_Trivial => 
         match trvT_d with 
         | Certify_Order_Trivial  => Certify_Order_Trivial
         | Certify_Order_Not_Trivial (t1, t2) => Certify_Order_Not_Trivial ((wS, t1), (wS, t2))
         end 
       | Certify_Order_Not_Trivial (s1, s2) => Certify_Order_Not_Trivial ((s1, wT), (s2, wT))
       end. 

Definition ord_product_total_certify {S T : Type} (wS : S) (wT : T) 
           (totS_d : @certify_total S) 
           (totT_d : @certify_total  T) 
           (trvS_d : @order_trivial_certifiable S) 
           (trvT_d : @order_trivial_certifiable T) : @certify_total (S * T) := 
match totS_d with
| Certify_Total =>
  match totT_d with
  | Certify_Total =>
    match trvS_d with
    | Certify_Order_Trivial                => Certify_Total 
    | Certify_Order_Not_Trivial (s1, s2)   =>
      match trvT_d with
      | Certify_Order_Trivial              => Certify_Total
      | Certify_Order_Not_Trivial (t1, t2) => Certify_Not_Total ((s2, t1), (s1, t2))
      end
    end 
  | Certify_Not_Total (t1, t2) => Certify_Not_Total ((wS, t1), (wS, t2))
  end 
| Certify_Not_Total (s1, s2) => Certify_Not_Total ((s1, wT), (s2, wT))
end.     


Definition qo_product_certs {S T : Type} (wS : S) (wT : T)
           (P : @qo_certificates S)
           (Q : @qo_certificates T) : @qo_certificates (S * T) := 
{|
  qo_congruence        := Assert_Brel_Congruence 
; qo_reflexive         := Assert_Reflexive
; qo_transitive        := Assert_Transitive
; qo_antisymmetric_d   := ord_product_antisymmetric_certify wS wT
                               (qo_antisymmetric_d P) 
                               (qo_antisymmetric_d Q)
; qo_total_d           := ord_product_total_certify wS wT
                               (qo_total_d P) 
                               (qo_total_d Q)
                               (qo_trivial_d P) 
                               (qo_trivial_d Q)                               
; qo_trivial_d         := ord_product_order_trivial_certify wS wT
                               (qo_trivial_d P) 
                               (qo_trivial_d Q)   
|}.

Definition qo_product {S T : Type} (PS : @qo S) (PT : @qo T) : @qo(S * T) :=
let eqvS   := qo_eqv PS in
let eqvT   := qo_eqv PT in
let eqS    := eqv_eq eqvS in
let eqT    := eqv_eq eqvT in
let wS     := eqv_witness eqvS in
let wT     := eqv_witness eqvT in
let lteS   := qo_lte PS in 
let lteT   := qo_lte PT in
let botS_d := qo_exists_bottom_d PS in
let botT_d := qo_exists_bottom_d PT in
let topS_d := qo_exists_top_d PS in
let topT_d := qo_exists_top_d PT in 
let pS     := qo_certs PS in 
let pT     := qo_certs PT in
{|
  qo_eqv             := eqv_product eqvS eqvT
; qo_lte             := brel_product lteS lteT 
; qo_exists_top_d    := ord_product_exists_qo_top_check topS_d topT_d
; qo_exists_bottom_d := ord_product_exists_qo_bottom_check botS_d botT_d
; qo_certs           := qo_product_certs wS wT pS pT 
; qo_ast             := Ast_or_product (qo_ast PS, qo_ast PS)
|}.

End CAS.

Section MCAS.

  Definition qo_product_below_qo {S T : Type}
    (A : @below_qo S)
    (B : @below_qo T)  : @below_qo (S * T) :=
    classify_qo (qo_product (cast_up_qo A) (cast_up_qo B)).

  
  Definition mcas_qo_product {S T : Type}
    (A : @qo_mcas S)
    (B : @qo_mcas T)  : @qo_mcas (S * T) :=
    match A, B with
    | MCAS_qo A', MCAS_qo B'               => MCAS_qo (qo_product_below_qo A' B')
    | MCAS_qo_Error sl1, MCAS_qo_Error sl2 => MCAS_qo_Error (sl1 ++ sl2)
    | MCAS_qo_Error sl1, _                   => MCAS_qo_Error sl1
    | _,  MCAS_qo_Error sl2                  => MCAS_qo_Error sl2
    end.

  

End MCAS.


Section Verify.

Section Decide.

Variables (S T: Type)
          (eqS lteS : brel S) (wS : S)
          (eqT lteT : brel T) (wT : T)
          (refS    : brel_reflexive S eqS)
          (symS    : brel_symmetric S eqS)          
          (refT    : brel_reflexive T eqT)
          (symT    : brel_symmetric T eqT)                    
          (lteRefS : brel_reflexive S lteS)
          (lteRefT : brel_reflexive T lteT). 

Lemma correct_po_product_exists_qo_top_check
  (topS : brel_exists_qo_top_decidable S eqS lteS)
  (topT : brel_exists_qo_top_decidable T eqT lteT) : 
  ord_product_exists_qo_top_check
    (p2c_exists_qo_top_check S eqS lteS topS)
    (p2c_exists_qo_top_check T eqT lteT topT)
  = 
  p2c_exists_qo_top_check (S * T) (brel_product eqS eqT) (brel_product lteS lteT)
    (ord_product_exists_qo_top_decide S T eqS eqT refS lteS lteT lteRefS lteRefT topS topT). 
Proof. unfold p2c_exists_qo_top_check, ord_product_exists_qo_top_check, ord_product_exists_qo_top_decide.
       destruct topS; destruct topT; simpl; auto. 
       destruct b as [s [A B]]. destruct b0 as [t [C D]]. simpl. reflexivity. 
Defined.


Lemma correct_po_product_exists_qo_bottom_check
  (bottomS : brel_exists_qo_bottom_decidable S eqS lteS)
  (bottomT : brel_exists_qo_bottom_decidable T eqT lteT) : 
  ord_product_exists_qo_bottom_check
    (p2c_exists_qo_bottom_check S eqS lteS bottomS)
    (p2c_exists_qo_bottom_check T eqT lteT bottomT)
  = 
  p2c_exists_qo_bottom_check (S * T) (brel_product eqS eqT) (brel_product lteS lteT)
    (ord_product_exists_qo_bottom_decide S T eqS eqT refS lteS lteT lteRefS lteRefT bottomS bottomT). 
Proof. unfold p2c_exists_qo_bottom_check, ord_product_exists_qo_bottom_check, ord_product_exists_qo_bottom_decide.
       destruct bottomS; destruct bottomT; simpl; auto. 
       destruct b as [s [A B]]. destruct b0 as [t [C D]]. simpl. reflexivity. 
Defined.

Lemma correct_qod_product_antisymmetric_certify
    (dS : brel_antisymmetric_decidable S eqS lteS)
    (dT : brel_antisymmetric_decidable T eqT lteT) : 
      p2c_antisymmetric_check (S * T) (brel_product eqS eqT) (brel_product lteS lteT)
        (ord_product_antisymmetric_decide S T wS wT eqS eqT symS symT lteS lteT lteRefS lteRefT dS dT)
      = 
      ord_product_antisymmetric_certify wS wT
        (p2c_antisymmetric_check S eqS lteS dS) 
        (p2c_antisymmetric_check T eqT lteT dT). 
Proof. unfold ord_product_antisymmetric_decide, ord_product_antisymmetric_certify, p2c_antisymmetric_check; simpl. 
       destruct dS as [antiS | [[s1 s2] [ [A B] C]]];
       destruct dT as [antiT | [[t1 t2] [ [D E] F]]]; simpl; reflexivity. 
Qed.   

Lemma correct_product_qoder_trivial_decide
     (trvS_d : order_trivial_decidable S lteS)
     (trvT_d : order_trivial_decidable T lteT): 
      p2c_order_trivial_certificate (S * T) (brel_product lteS lteT)
        (ord_product_order_trivial_decide S T wS wT lteS lteT lteRefS trvS_d trvT_d)
        =
        ord_product_order_trivial_certify wS wT
        (p2c_order_trivial_certificate S lteS trvS_d)
        (p2c_order_trivial_certificate T lteT trvT_d). 
Proof. unfold ord_product_order_trivial_decide,
         ord_product_order_trivial_certify,
         p2c_order_trivial_certificate; simpl. 
       destruct trvS_d as [trvS | [[s1 s2] A]]; 
       destruct trvT_d as [trvT | [[t1 t2] B]]; simpl; reflexivity.          
Qed.   

  
Lemma correct_qod_product_total_certify
           (totS_d : brel_total_decidable S lteS) 
           (totT_d : brel_total_decidable T lteT) 
           (trvS_d : order_trivial_decidable S lteS) 
           (trvT_d : order_trivial_decidable T lteT) : 
      p2c_total_check (S * T) (brel_product lteS lteT)
        (ord_product_total_decide S T wS wT lteS lteT lteRefS totS_d totT_d trvS_d trvT_d)
        = 
        ord_product_total_certify wS wT
        (p2c_total_check S lteS totS_d)
        (p2c_total_check T lteT totT_d)
        (p2c_order_trivial_certificate S lteS trvS_d)
        (p2c_order_trivial_certificate T lteT trvT_d).
Proof. unfold ord_product_total_certify, ord_product_total_decide.
       unfold p2c_total_check, p2c_order_trivial_certificate; simpl.
       destruct totS_d as [totS | [[s1 s2] [A B]]];
       destruct totT_d as [totT | [[t1 t2] [C D]]];
       destruct trvS_d as [trvS | [[s3 s4] E]];
       destruct trvT_d as [trvT | [[t3 t4] F]];
         simpl; try reflexivity.
Qed. 


End Decide.

Section Proofs.


Variables (S T: Type)
          (eqS lteS : brel S) (wS : S)
          (eqT lteT : brel T) (wT : T)
          (eqvPS    : eqv_proofs S eqS)
          (eqvPT    : eqv_proofs T eqT).

Lemma correct_qo_product_certs (P : qo_proofs S eqS lteS) (Q : qo_proofs T eqT lteT) :
   qo_product_certs wS wT (P2C_qo eqS lteS P) (P2C_qo eqT lteT Q) 
   =   
   P2C_qo _ _ (qo_product_proofs S T eqS wS eqvPS eqT wT eqvPT lteS lteT P Q). 
Proof. unfold qo_product_certs, qo_product_proofs, P2C_qo; simpl. 
       rewrite correct_qod_product_total_certify. 
       rewrite correct_product_qoder_trivial_decide.
       rewrite correct_qod_product_antisymmetric_certify. 
       reflexivity. 
Qed.


End Proofs.   


Section Combinators.

Lemma correct_qo_product (S T: Type) (P : A_qo S )  (Q : A_qo T) :
   qo_product (A2C_qo P) (A2C_qo Q) 
   =   
   A2C_qo (A_qo_product S T P Q). 
Proof. destruct P. destruct Q.
       unfold A_qo_product, qo_product, A2C_qo. simpl.
       rewrite <- correct_eqv_product.       
       rewrite <- correct_po_product_exists_qo_top_check.
       rewrite <- correct_po_product_exists_qo_bottom_check.       
       rewrite <- correct_qo_product_certs.
       reflexivity. 
Qed.

Theorem correct_qo_product_below_qo (S T : Type) (A : @A_below_qo S) (B : @A_below_qo T): 
  qo_product_below_qo (A2C_below_qo A) (A2C_below_qo B)
  =
 A2C_below_qo (A_qo_product_below_qo A B).
Proof. unfold A_qo_product_below_qo, qo_product_below_qo.
       rewrite cast_up_qo_A2C_commute.
       rewrite cast_up_qo_A2C_commute. 
       rewrite correct_qo_product.
       rewrite correct_classify_qo.
       reflexivity.
Qed.

Theorem correct_mcas_qo_product (S T : Type) (A : @A_qo_mcas S) (B : @A_qo_mcas T): 
         mcas_qo_product (A2C_qo_mcas A) (A2C_qo_mcas B) 
         = 
         A2C_qo_mcas (A_mcas_qo_product A B).
Proof. unfold mcas_qo_product, A_mcas_qo_product.
       destruct A; destruct B; simpl; try reflexivity. 
       rewrite correct_qo_product_below_qo.
       reflexivity. 
Qed. 


End Combinators.     

End Verify.   
  
