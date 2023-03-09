
Require Import CAS.coq.common.compute. 
Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.sg.properties. 
Require Import CAS.coq.bs.properties. 

(* 
LD( +,* )  left distributive       a * (b + c) = (a * b) + (a * c) 
RD( +,* )  right distributive      (b + c) * a = (b * a) + (c * a)
LA( +,* )  left absorptive         a = a + (a * b) 
RA( +,* )  right absorptive        a = (a * b) + a
0A( +,* ) plus id is times ann     id+ * a = id+ = a * id+
OA( *,+ ) times id is plus ann     id* + a = id* = a + id*

LD( +,* )  a * (b + c) = (a * b) + (a * c) 
LD( *,+ )  a + (b * c) = (a + b) * (a + c) 
RD( +,* )  (b + c) * a = (b * a) + (c * a)
RD( *,+ )  (b * c) + a = (b + a) * (c + a)
LA( +,* )  a = a + (a * b) 
LA( *,+ )  a = a * (a + b) 
RA( +,* )  a = (a * b) + a
0A( +,* )  id+ * a = id+ = a * id+
OA( *,+ )  id* + a = id* = a + id*


---------------------------------------------------------
LD( +,* ) C( * ) -> RD( +,* ) 
LA( +,* ) C( * ) -> RA( +,* ) 

C( + ), C( * ), LA( *, + ), a = a + b -> b = a * b 
                LA( +, * ), b = a * b -> a = a + b

LA( +, * ),  LA( *, + )             -> I( + )
LA( +, * ),  LA( *, + )             -> I( * )

C( * ), LA( +, * ),  LA( *, + ), LD( +, * ) -> LD( *, + ) 
---------------------------------------------------------
---------------------------------------------------------
I( * ), LD( +,* ) -> LA( +,* )
I( + ), LD( *,+ ) -> LA( *,+ )

   a + (b * c) = (a + b) * (a + c) 
   a + (a * b) = (a + a) * (a + b) 
               = a * (a + b)         I( + )

---------------------------------------------------------
S( + ), LD( *,+ ) 

   a + (b * c) = (a + b) * (a + c) 

---------------------------------------------------------

 *)


Lemma one_is_plus_annihilator_implies_left_absorptive
  (S : Type) (eq : brel S) (plus times : binary_op S)
  (ref : brel_reflexive S eq)
  (sym : brel_symmetric S eq)
  (trn : brel_transitive S eq)
  (pcng : bop_congruence S eq plus)
  (tcng : bop_congruence S eq times) 
  (A : A_bs_exists_id_ann_equal eq times plus)
  (B : A_bs_left_distributive eq plus times) :  
  A_bs_left_absorptive eq plus times. 
Proof. intros a b. compute in A.
       destruct A as [one [C D]].
       assert (E := B a one b). 
       destruct (D b) as [F G]. 
       destruct (C a) as [H I].
       assert (J : eq a (times a (plus one b)) = true). 
       {
         assert (K := tcng _ _ _ _ (ref a) F).
         assert (L := trn _ _ _ K I).
         apply sym; auto. 
       }
       assert (K: eq (plus (times a one) (times a b)) (plus a (times a b)) = true).
       {
         exact (pcng _ _ _ _ I (ref ((times a b)))). 
       }
       assert (L := trn _ _ _ J E). 
       assert (M := trn _ _ _ L K).
       exact M. 
Qed.


Lemma one_is_plus_annihilator_implies_right_absorptive
  (S : Type) (eq : brel S) (plus times : binary_op S)
  (ref : brel_reflexive S eq)
  (sym : brel_symmetric S eq)
  (trn : brel_transitive S eq)
  (pcng : bop_congruence S eq plus)
  (tcng : bop_congruence S eq times) 
  (A : A_bs_exists_id_ann_equal eq times plus)
  (B : A_bs_right_distributive eq plus times) :  
  A_bs_right_absorptive eq plus times. 
Proof. intros a b. compute in A.
       destruct A as [one [C D]].
       assert (E := B a one b). 
       destruct (D b) as [F G]. 
       destruct (C a) as [H I].
       assert (J : eq a (times (plus one b) a) = true). 
       {
         assert (K := tcng _ _ _ _ F (ref a)).
         assert (L := trn _ _ _ K H).
         apply sym; auto. 
       }
       assert (K: eq (plus (times one a) (times b a)) (plus a (times b a)) = true).
       {
         exact (pcng _ _ _ _ H (ref ((times b a)))). 
       }
       assert (L := trn _ _ _ J E). 
       assert (M := trn _ _ _ L K).
       exact M. 
Qed.

Lemma bs_left_distributive_implies_right : ∀ (S : Type) (r : brel S) (b1 b2 : binary_op S),
        brel_transitive S r -> 
        bop_congruence S r b1 -> 
        bop_commutative S r b1 -> 
        bop_commutative S r b2 -> 
           A_bs_left_distributive r b1 b2 -> A_bs_right_distributive r b1 b2. 
Proof. intros S r b1 b2 transS cong1 c1 c2 ld s t u.
       assert (fact1 := ld s t u).        
       assert (fact2 := c2 s u). 
       assert (fact3 := c2 s t). 
       assert (fact4 := c2 (b1 t u) s). 
       assert (fact5 := transS _ _ _ fact4 fact1). 
       assert (fact6 : r (b1 (b2 s t) (b2 s u)) (b1 (b2 t s) (b2 u s)) = true). 
          apply (cong1 _ _ _ _ fact3 fact2). 
       assert (fact7 := transS _ _ _ fact5 fact6). 
       assumption. 
Defined. 


Lemma bs_not_left_distributive_implies_not_right : ∀ (S : Type) (r : brel S) (b1 b2 : binary_op S),
        brel_transitive S r -> 
        bop_congruence S r b1 -> 
        bop_commutative S r b1 -> 
        bop_commutative S r b2 -> 
           A_bs_not_left_distributive r b1 b2 -> A_bs_not_right_distributive r b1 b2. 
Proof. intros S r b1 b2 transS cong1 c1 c2 [[a [b c]] NLD].
       exists (a, (b, c)). 
       case_eq(r (b2 (b1 b c) a) (b1 (b2 b a) (b2 c a))); intro H; auto. 
       assert (fact1 := c2 a (b1 b c)).
       assert (fact2 := transS _ _ _ fact1 H).        
       assert (fact3 := c2 b a).
       assert (fact4 := c2 c a).
       assert (fact5 := cong1 _ _ _ _ fact3 fact4).
       assert (fact6 := transS _ _ _ fact2 fact5).               
       rewrite fact6 in NLD. 
       discriminate NLD. 
Defined. 


Lemma bs_left_distributive_decidable_implies_right_decidable : ∀ (S : Type) (r : brel S) (b1 b2 : binary_op S),
        brel_transitive S r -> 
        bop_congruence S r b1 -> 
        bop_commutative S r b1 -> 
        bop_commutative S r b2 -> 
        A_bs_left_distributive_decidable r b1 b2 -> A_bs_right_distributive_decidable r b1 b2.
Proof. intros S r b1 b2 transS cong1 c1 c2 [LD | NLD].
       left. apply bs_left_distributive_implies_right; auto. 
       right. apply bs_not_left_distributive_implies_not_right; auto. 
Defined.


(*
   LD( +,* ) C( * ) -> RD( +,* ) 
*) 
Lemma bops_left_distributive_and_times_commutative_imply_right_distributive : 
      ∀ (S : Type) (rS : brel S) (plusS timesS : binary_op S),       
        brel_congruence S rS rS ->         
        bop_congruence S rS plusS ->         
        bop_commutative S rS timesS ->         
        A_bs_left_distributive rS plusS timesS -> 
           A_bs_right_distributive rS plusS timesS. 
Proof. intros S rS plusS timesS congS cong_plusS commS ldS s1 s2 s3. 
       unfold bop_commutative in commS. 
       unfold bop_congruence in cong_plusS. 
       unfold brel_congruence in congS. 
       assert (A := commS s1 (plusS s2 s3)). 
       assert (B := commS s1 s2).
       assert (C := commS s1 s3).
       assert (D := cong_plusS _ _ _ _ B C). 
       assert (E := congS _ _ _ _ A D). 
       assert (F := ldS s1 s2 s3). 
       rewrite F in E. 
       rewrite <- E. 
       reflexivity. 
Qed. 

(* 
     LA( +,* ) C( * ) -> RA( +,* ) 

Lemma bops_left_absorption_and_times_commutative_imply_right_absorption : 
      ∀ (S : Type) (rS : brel S) (plusS timesS : binary_op S),       
        brel_reflexive S rS ->         
        brel_transitive S rS ->         
        bop_congruence S rS plusS ->         
        bop_commutative S rS timesS ->         
        bops_left_absorption S rS plusS timesS -> 
           bops_right_absorption S rS plusS timesS. 
Proof. intros S rS plusS timesS refS transS cong_plusS commS laS s1 s2. 
       unfold bop_commutative in commS. 
       unfold bops_left_absorption in laS. 
       unfold bop_congruence in cong_plusS. 
       assert (B := commS s1 s2).
       assert (C := refS s1).
       assert (D := laS s1 s2). 
       assert (E := cong_plusS _ _ _ _ C B). 
       assert (F := transS _ _ _ D E). 
       assumption. 
Qed. 
*) 

(* 


Lemma bops_explore : 
      ∀ (S : Type) 
        (rS : brel S) 
        (plusS timesS : binary_op S)
        (LA1 : bops_left_absorption S rS plusS timesS)    (* a = a + (a * b) *)
        (LA2 : bops_left_absorption S rS timesS plusS)    (* a = a * (a + b) *)
        (RA1 : bops_right_absorption S rS plusS timesS)   (* a = (a * b) + a *) 
        (RA2 : bops_right_absorption S rS timesS plusS),  (* a = (a + b) * a *) 
        bop_left_distributive S rS plusS timesS ->        (* a * (b + c) = (a * b) + (a * c) *) 
           bop_right_distributive S rS timesS plusS. 
Proof. unfold bops_left_absorption, 
              bops_right_absorption,
              bop_left_distributive, 
              bop_left_distributive. 
       intros S rS plusS timesS LA1 LA2 RA1 RA2 ldS s1 s2 s3. 
 Qed. 
*) 


(* 
   C( + ), C( * ), LA( *, +), a = a + b -> b = a * b 

Lemma bops_lattice_test_1 : 
      ∀ (S : Type) (rS : brel S) (plusS timesS : binary_op S),       
        brel_reflexive S rS -> 
        brel_symmetric S rS -> 
        brel_transitive S rS -> 
        bop_congruence S rS timesS -> 
        bop_commutative S rS plusS ->         
        bop_commutative S rS timesS ->         
        bops_left_absorption S rS timesS plusS -> 
           ∀ (a b : S), rS a (plusS a b) = true -> rS b (timesS a b) = true. 
Proof. intros S rS plusS timesS refS symS transS cong_times comm_plus comm_times laS a b H. 
       assert (A := laS b a). 
       assert (B := comm_plus a b). 
       assert (C := transS _ _ _ H B).
       assert (D := cong_times _ _ _ _ (refS b) C). 
       apply symS in A. 
       assert (E := transS _ _ _ D A). 
       assert (F := comm_times a b).        
       assert (G := transS _ _ _ F E). apply symS. 
       assumption. 
Qed. 

*) 

(* 
   LA( +, * ), b = a * b -> a = a + b

Lemma bops_lattice_test_2 : 
      ∀ (S : Type) (rS : brel S) (plusS timesS : binary_op S),       
        brel_reflexive S rS -> 
        brel_symmetric S rS -> 
        brel_transitive S rS -> 
        bop_congruence S rS plusS -> 
        bops_left_absorption S rS plusS timesS -> 
           ∀ (a b : S), rS b (timesS a b) = true -> rS a (plusS a b) = true.  
Proof. intros S rS plusS timesS refS symS transS cong_plus laS a b H. 
       assert (A := laS a b). 
       assert (C := cong_plus _ _ _ _ (refS a) H). 
       apply symS in C. 
       assert (D := transS _ _ _ A C). 
       assumption. 
Qed. 
*) 

(* 
   LA( +, * ),  LA( *, + ) -> I( + )

Lemma bops_lattice_test_3 : 
      ∀ (S : Type) (rS : brel S) (plusS timesS : binary_op S),       
        brel_reflexive S rS -> 
        brel_symmetric S rS -> 
        brel_transitive S rS -> 
        bop_congruence S rS plusS ->  
        bops_left_absorption S rS plusS timesS ->       
        bops_left_absorption S rS timesS plusS -> 
           bop_idempotent S rS plusS. 
Proof. intros S rS plusS timesS refS symS transS cong_plus la1 la2 a. 
       unfold bops_left_absorption in *. 
       assert (A := la1 a (plusS a a)).
       assert (B := la2 a a). 
       assert (C := cong_plus _ _ _ _ (refS a) B). 
       apply symS in A. 
       assert (D := transS _ _ _ C A). 
       assumption. 
Qed.

*) 

(* 
   LA( +, * ),  LA( *, + ) -> I( * )

Lemma bops_lattice_test_4 : 
      ∀ (S : Type) (rS : brel S) (plusS timesS : binary_op S),       
        brel_reflexive S rS -> 
        brel_symmetric S rS -> 
        brel_transitive S rS -> 
        bop_congruence S rS timesS ->
        bops_left_absorption S rS plusS timesS ->       
        bops_left_absorption S rS timesS plusS -> 
           bop_idempotent S rS timesS. 
Proof. intros S rS plusS timesS refS symS transS cong_times la1 la2 a. 
       unfold bops_left_absorption in *. 
       assert (A := la2 a (timesS a a)).
       assert (B := la1 a a). 
       assert (C := cong_times _ _ _ _ (refS a) B). 
       apply symS in A. 
       assert (D := transS _ _ _ C A). 
       assumption. 
Qed.
*) 

(* 
   C ( * ), LA( +, * ),  LA( *, + ), LD( +, * ) -> LD( *, + ) 

Lemma bops_lattice_test_5 : 
      ∀ (S : Type) (rS : brel S) (b1 b2 : binary_op S),       
        brel_congruence S rS rS ->         
        brel_reflexive S rS -> 
        brel_symmetric S rS -> 
        brel_transitive S rS -> 
        bop_congruence S rS b1 ->
        bop_associative S rS b1 ->
        bop_commutative S rS b2 ->
        bops_left_absorption S rS b1 b2 ->       
        bops_left_absorption S rS b2 b1 -> 
           bop_left_distributive S rS b1 b2 -> bop_left_distributive S rS b2 b1.
Proof. intros S rS b1 b2 congS refS symS transS cong_b1 assoc_b1 comm_b2 la1 la2 ldS s1 s2 s3. 
       (* outline : (page 86 of Davey and Priestley)
            (s1 + s2) * (s1 + s3) 
          = ldS 
            ((s1 + s2) * s1) + ((s1 + s2) * s3)  
          = comm_b2, la2 
            s1 + (s3 * (s1 + s2))
          = ldS 
            s1 + ((s3 * s1) + (s3 * s2))
          = assoc 
            (s1 + (s3 * s1)) + (s3 * s2))
          = comm_b2, la1 
            s1 + (s2 * s3))
       *) 
       assert (A := ldS (b1 s1 s2) s1 s3). 
       assert (B : rS (b1 (b2 (b1 s1 s2) s1) (b2 (b1 s1 s2) s3))
                      (b1 s1 (b2 (b1 s1 s2) s3)) = true). 
          assert (C := la2 s1 s2).           
          assert (D := comm_b2 s1 (b1 s1 s2)). 
          assert (E := transS _ _ _ C D). 
          apply cong_b1. apply symS. assumption. apply refS. 
       assert (C := transS _ _ _ A B). 
       assert (D : rS (b1 s1 (b2 (b1 s1 s2) s3))
                      (b1 s1 (b2 s2 s3)) = true).
          assert (rdS := bops_left_distributive_and_times_commutative_imply_right_distributive S
                           rS b1 b2 congS cong_b1 comm_b2 ldS). 
          assert (E := rdS s3 s1 s2). 
          assert (F := cong_b1 _ _ _ _ (refS s1) E).           
          assert (G := assoc_b1 s1 (b2 s1 s3) (b2 s2 s3)). 
          apply symS in G. 
          assert (H := transS _ _ _ F G). 
          assert (I := la1 s1 s3). 
          assert (J := cong_b1 _ _ _ _ I (refS (b2 s2 s3))). apply symS in J. 
          assert (K := transS _ _ _ H J). 
          assumption. 
       assert (E := transS _ _ _ C D). 
       apply symS. assumption. 
Qed.
*) 


(* 
(B ∧ A) ∨ (C ∧ A) = [(B ∧ A) ∨ C] ∧ A.

B ≤ A implies B ∨ (C ∧ A) = (B ∨ C) ∧ A.

*) 
Definition bop_right_modular_eq (S : Type) (r : brel S) (b1 b2 : binary_op S)
   := ∀ a b c : S, r (b1 (b2 b a) (b2 c a)) (b2 (b1 (b2 b a) c) a) = true. 



(****************************************************************************************** 

This is same as theory.bop_product.bop_not_left_or_not_right

This justifies the semigroup attribute 

*) 
Lemma brel_nontrivial_implies_not_bop_is_left_and_bop_is_right : 
      ∀ (S : Type) (rS : brel S) (s : S) (f : S -> S),  
        brel_symmetric S rS -> 
        brel_transitive S rS -> 
        brel_not_trivial S rS f -> 
        ∀ (bS : binary_op S), ((bop_is_left S rS bS) * (bop_is_right S rS bS)) -> False. 
Proof. unfold bop_is_left, bop_is_right. 
       intros S rS s f symS tranS Pf bS [ ilS irS ]. 
       assert (A := ilS s (f s)). 
       assert (B := irS s (f s)). 
       apply symS in A. 
       assert (C := tranS _ _ _ A B). 
       destruct (Pf s) as [F _]. 
       rewrite F in C. 
       discriminate. 
Qed. 

(*
Definition bop_is_left (S : Type) (r : brel S) (b : binary_op S) 
    := ∀ s t : S, r (b s t) s = true. 

Definition bop_is_right (S : Type) (r : brel S) (b : binary_op S) 
    := ∀ s t : S, r (b s t) t = true. 

Definition bop_anti_left (S : Type) (r : brel S) (b : binary_op S) := 
    ∀ (s t : S), r s (b s t) = false. 

Definition bop_anti_right (S : Type) (r : brel S) (b : binary_op S) := 
    ∀ (s t : S), r s (b t s) = false. 

Definition bop_left_constant (S : Type) (r : brel S) (b : binary_op S)
    := ∀ s t u : S, r (b s t) (b s u) = true. 

Definition bop_right_constant (S : Type) (r : brel S) (b : binary_op S)
    := ∀ s t u : S, r (b t s) (b u s) = true. 

*) 


(* absorption 

Definition bops_left_left_absorptive (S : Type) (r : brel S) (b1 b2 : binary_op S) := 
    ∀ (s t : S), r s (b1 s (b2 s t)) = true.

Definition bops_left_right_absorptive (S : Type) (r : brel S) (b1 b2 : binary_op S) := 
    ∀ (s t : S), r s (b1 s (b2 t s)) = true.

Definition bops_right_left_absorptive (S : Type) (r : brel S) (b1 b2 : binary_op S) := 
    ∀ (s t : S), r s (b1 (b2 s t) s) = true.

Definition bops_right_right_absorptive (S : Type) (r : brel S) (b1 b2 : binary_op S) := 
    ∀ (s t : S), r s (b1 (b2 t s) s) = true.
 *)


Lemma id_ann_implies_left_left_absorptive
      (S : Type)
      (eq : brel S)
      (ref : brel_reflexive S eq)
      (trn : brel_transitive S eq)
      (sym : brel_symmetric S eq)      
      (plus times : binary_op S)
      (c_plus : bop_congruence S eq plus)
      (c_times : bop_congruence S eq times)       
      (ld : A_bs_left_distributive eq plus times)       
      (id_ann : A_bs_exists_id_ann_equal eq times plus) :
      A_bs_left_absorptive eq plus times.   
Proof. destruct id_ann as [id [A B]]. 
       intros a b.
       assert (C : eq (plus a (times a b)) (plus (times a id) (times a b)) = true).
          destruct (A a) as [D E].
          apply sym. exact (c_plus _ _ _ _ E (ref (times a b))). 
       assert (D : eq (plus (times a id) (times a b)) (times a (plus id b)) = true).
          apply sym. exact (ld a id b). 
       assert (E : eq (times a (plus id b)) (times a id) = true). 
          destruct (B b) as [F G]. 
          exact (c_times _ _ _ _ (ref a) F).
       assert (F : eq (times a id) a = true).
          destruct (A a) as [G H]. exact H. 
       apply sym.
       exact (trn _ _ _ (trn _ _ _ (trn _ _ _ C D) E) F). 
Qed.


Lemma id_ann_implies_left_right_absorptive
      (S : Type)
      (eq : brel S)
      (ref : brel_reflexive S eq)
      (trn : brel_transitive S eq)
      (sym : brel_symmetric S eq)      
      (plus times : binary_op S)
      (c_plus : bop_congruence S eq plus)
      (comm : bop_commutative S eq plus)      
      (c_times : bop_congruence S eq times)       
      (rd : A_bs_right_distributive eq plus times)       
      (id_ann : A_bs_exists_id_ann_equal eq times plus) :
      A_bs_right_absorptive eq plus times.   
Proof. destruct id_ann as [id [A B]]. 
       intros a b.
       assert (C : eq (plus (times b a) a) (plus  (times b a) (times id a)) = true).
          destruct (A a) as [D E].
          apply sym. exact (c_plus _ _ _ _ (ref (times b a)) D). 
       assert (D : eq (plus (times b a) (times id a)) (times  (plus b id) a) = true).
          apply sym. exact (rd a b id). 
       assert (E : eq (times (plus b id) a) (times id a) = true). 
          destruct (B b) as [F G]. 
          exact (c_times _ _ _ _ G (ref a)).
       assert (F : eq (times id a) a = true).
          destruct (A a) as [G H]. exact G.
       assert (G := comm a (times b a)).
       apply sym.
       exact (trn _ _ _ (trn _ _ _ (trn _ _ _ (trn _ _ _ G C) D) E) F). 
Qed.


       
(*
Lemma bops_left_right_absorptive_implies_right_right : ∀ (S : Type) (r : brel S) (b1 b2 : binary_op S),
        brel_transitive S r -> 
        bop_commutative S r b1 -> 
        A_bs_right_absorptive S r b1 b2 -> A_bs_right_right_absorptive S r b1 b2. 
Proof. intros S r b1 b2 transS comm_b1 abs s t.
       assert (fact1 := abs s t).
       assert (fact2 := comm_b1 s (b2 t s)). 
       apply (transS _ _ _ fact1 fact2). 
Defined.

Lemma bops_not_left_right_absorptive_implies_not_right_right : ∀ (S : Type) (r : brel S) (b1 b2 : binary_op S),
        brel_transitive S r ->
        bop_commutative S r b1 -> 
        bops_not_left_right_absorptive S r b1 b2 -> bops_not_right_right_absorptive S r b1 b2. 
Proof. intros S r b1 b2 transS comm_b1 [[s s'] P]. exists (s, s'). 
       case_eq(r s (b1 (b2 s' s) s)); intro J.
          assert (fact1 := comm_b1 (b2 s' s) s). 
          assert (fact2 := transS _ _ _ J fact1).
          rewrite fact2 in P. discriminate. 
          reflexivity. 
Defined.

Definition bops_right_right_absorptive_decide_I : ∀ (S : Type) (r : brel S) (b1 b2 : binary_op S),
        brel_transitive S r -> 
        bop_commutative S r b1 -> 
        bops_left_right_absorptive_decidable S r b1 b2 -> bops_right_right_absorptive_decidable S r b1 b2
:= λ S r b1 b2 trans comm lrad, 
   match lrad with 
   | inl lr  => inl _ (bops_left_right_absorptive_implies_right_right S r b1 b2 trans comm lr)
   | inr nlr => inr _ (bops_not_left_right_absorptive_implies_not_right_right S r b1 b2 trans comm nlr)
   end. 



Lemma bops_left_left_absorptive_implies_right_left: ∀ (S : Type) (r : brel S) (b1 b2 : binary_op S),
        brel_transitive S r -> 
        bop_commutative S r b1 -> 
        bops_left_left_absorptive S r b1 b2 -> bops_right_left_absorptive S r b1 b2. 
Proof. intros S r b1 b2 transS comm_b1 abs s t.
       assert (fact1 := abs s t).
       assert (fact2 := comm_b1 s (b2 s t)). 
       apply (transS _ _ _ fact1 fact2). 
Defined.

Lemma bops_not_left_left_absorptive_implies_not_right_left : ∀ (S : Type) (r : brel S) (b1 b2 : binary_op S),
        brel_transitive S r ->
        bop_commutative S r b1 -> 
        bops_not_left_left_absorptive S r b1 b2 -> bops_not_right_left_absorptive S r b1 b2. 
Proof. intros S r b1 b2 transS comm_b1 [[s s'] P]. exists (s, s'). 
       case_eq(r s (b1 (b2 s s') s)); intro J.
          assert (fact1 := comm_b1 (b2 s s') s). 
          assert (fact2 := transS _ _ _ J fact1).
          rewrite fact2 in P. discriminate. 
          reflexivity. 
Defined.

Definition bops_right_left_absorptive_decide_I : ∀ (S : Type) (r : brel S) (b1 b2 : binary_op S),
        brel_transitive S r -> 
        bop_commutative S r b1 -> 
        bops_left_left_absorptive_decidable S r b1 b2 -> bops_right_left_absorptive_decidable S r b1 b2
:= λ S r b1 b2 trans comm lrad, 
   match lrad with 
   | inl lr  => inl _ (bops_left_left_absorptive_implies_right_left S r b1 b2 trans comm lr)
   | inr nlr => inr _ (bops_not_left_left_absorptive_implies_not_right_left S r b1 b2 trans comm nlr)
   end. 

*) 




(*--------------------------*)



Lemma bs_left_absorptive_implies_right : ∀ (S : Type) (r : brel S) (b1 b2 : binary_op S),
        brel_reflexive S r -> 
        brel_transitive S r -> 
        bop_congruence S r b1 -> 
        bop_commutative S r b2 -> 
        A_bs_left_absorptive r b1 b2 -> A_bs_right_absorptive r b1 b2. 
Proof. intros S r b1 b2 refS transS cong_b1 comm_b2 lla s t.
       assert (fact1 := lla s t).        
       assert (fact2 : r (b1 s (b2 s t)) (b1 s (b2 t s)) = true). apply cong_b1; auto. 
       apply (transS _ _ _ fact1 fact2). 
Defined. 

(*
 Lemma bops_left_right_absorptive_implies_right_left : ∀ (S : Type) (r : brel S) (b1 b2 : binary_op S),        brel_reflexive S r -> 
        brel_transitive S r -> 
        bop_congruence S r b1 -> 
        bop_commutative S r b1 -> 
        bop_commutative S r b2 -> 
        bops_left_right_absorptive S r b1 b2 -> 
        bops_right_left_absorptive S r b1 b2. 
Proof. intros S r b1 b2 refS transS cong_b1 comm_b1 comm_b2 lra s t.
       assert (fact1 := lra s t).      
       assert (fact2 : r (b1 s (b2 t s)) (b1 (b2 s t) s) = true). 
          assert(fact3 := comm_b2 t s). 
          assert(fact4 := comm_b1 s (b2 t s)). 
          assert(fact5 : r (b1 (b2 t s) s) (b1 (b2 s t) s) = true). apply cong_b1; auto. 
          apply (transS _ _ _ fact4 fact5). 
       apply (transS _ _ _ fact1 fact2). 
Defined. 

Lemma bops_right_left_absorptive_implies_right_right : ∀ (S : Type) (r : brel S) (b1 b2 : binary_op S),
        brel_reflexive S r -> 
        brel_transitive S r -> 
        bop_congruence S r b1 -> 
        bop_commutative S r b2 -> 
        bops_right_left_absorptive S r b1 b2 -> bops_right_right_absorptive S r b1 b2. 
Proof. intros S r b1 b2 refS transS cong_b1 comm_b2 lla s t.
       assert (fact1 := lla s t).        
       assert (fact2 : r (b1 (b2 s t) s) (b1 (b2 t s) s) = true). apply cong_b1; auto. 
       apply (transS _ _ _ fact1 fact2). 
Defined. 
*) 
