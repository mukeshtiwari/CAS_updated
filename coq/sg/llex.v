Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool. 

Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.

Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.eqv.theory.
Require Import CAS.coq.eqv.product.

Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures.
Require Import CAS.coq.sg.theory.
Require Import CAS.coq.sg.and.
Require Import CAS.coq.sg.cast_up.
Require Import CAS.coq.sg.classify. 

Require Import CAS.coq.or.from_sg. 




(*** OUTLINE 

Section Computation.
  Defines (left) lexicographic product 

Section Theory.
  Semigroup property preservation lemmas 

Section ACAS. (annotated combinators. annotated with proofs) 
   Section Decide.
      decision procedures for semigroup properties 
   Section Proofs.
      use decision procedures to build proof structures 
   Section Combinators.
      use proof structures to build combinators 

Section CAS.  (proofs replaced by certificates) 
   Section Certify.
      CAS annologue of decision procedures 
   Section Certificates.
      CAS annologue of proof structures 
   Section Combinators.
      CAS annologue of proof combinators 

Section Verify.  (correctness proofs) 
   Section Certify.
   Section Certificates.
   Section Combinators.

      The main idea is that for every combinator pair (A_combo, combo) 
      we should prove that this diagram commutes: 

                       A_combo 
    (A_sg S, A_sg T) -------------> A_sg 
      |      |                      |
      |      |                      |   A2C 
     \/     \/                     \/
    (sgS',   sgT') ---------------> sg' 
                       combo

      For each combo the types of semigroups and A2C translations 
      may vary (A_sg, A_sg_CI, A_sg_CS, etc).
*) 



Section Computation.

(* for the general case t will be the identity of T. 
   for the selective S case, t can be any element of T since that case can't be reached. 
 *)

Definition llex_p2 {S T : Type} (t : T) (eq : brel S) (b2 : binary_op T) (ac a c : S) (b d : T) : T 
  := match eq a ac, eq ac c with
     | true, true   => b2 b d 
     | true, false  => b 
     | false, true  => d               
     | false, false => t 
     end. 
  
Definition bop_llex : ∀ {S T : Type}, T → brel S → binary_op S → binary_op T → binary_op (S * T) 
:= λ {S T} t eq b1 b2 x y,  
   match x, y with
    | (a, b), (c, d) => let ac := b1 a c in (ac, llex_p2 t eq b2 ac a c b d) 
   end.

End Computation.


Declare Scope bop_llex_scope.

Notation " a 'llex' [ eqS , t ] b"  := (bop_llex t eqS a b) (at level 1) : bop_llex_scope.

Open Scope brel_product_scope.
Open Scope bop_llex_scope.


Section Theory.

Variable S  : Type. 
Variable T  : Type. 
Variable rS : brel S. 
Variable rT : brel T. 
Variable bS : binary_op S. 
Variable bT : binary_op T.

Variable wS : S.
Variable f : S -> S.                
Variable Pf : brel_not_trivial S rS f. 


Variable conS : brel_congruence S rS rS. 
Variable refS : brel_reflexive S rS.
Variable symS : brel_symmetric S rS.  
Variable tranS : brel_transitive S rS.

Variable wT : T.
Variable argT : T.
Variable g : T -> T.                
Variable Pg : brel_not_trivial T rT g. 

Variable conT : brel_congruence T rT rT. 
Variable refT : brel_reflexive T rT.
Variable symT : brel_symmetric T rT.  
Variable tranT : brel_transitive T rT.
  
Variable b_conS : bop_congruence S rS bS.
Variable assS   : bop_associative S rS bS.  (* needed for associativity of llex, of course *) 
Variable idemS  : bop_idempotent S rS bS.   (* needed for associativity of llex! *) 
Variable commS  : bop_commutative S rS bS.  (* needed for associativity of llex!    tgg: REALLY???? *) 

Variable b_conT : bop_congruence T rT bT.  
Variable assT   : bop_associative T rT bT.  (* needed for associativity of llex, of course *) 


Notation "a =S b"  := (rS a b = true) (at level 15).
Notation "a !=S b" := (rS a b = false) (at level 15).
Notation "a =T b"  := (rT a b = true) (at level 15).
Notation "a !=T b" := (rT a b = false) (at level 15).
Notation "a *S b"  := (bS a b) (at level 15).
Notation "a *T b"  := (bT a b) (at level 15).
Notation "a <<= b" := (brel_lte_left rS bS a b = true) (at level 15).
Notation "a !<<= b" := (brel_lte_left rS bS a b = false) (at level 15).
Notation "a << b"  := (brel_lt_left rS bS a b = true) (at level 15).
Notation "a !<< b" := (brel_lt_left rS bS a b = false) (at level 15).

Notation "[| p1 | a | c | b | d |]" := (llex_p2 argT rS bT p1 a c b d) (at level 15).


Lemma llex_p2_congruence (s1 s2 s3 s4 : S) (t1 t2 t3 t4 : T)
  (C1 : s1 =S s3) 
  (C2 : t1 =T t3)
  (C3 : s2 =S s4)
  (C4 : t2 =T t4) : 
  ([|s1 *S s2 | s1 | s2 | t1 | t2|]) =T ([|s3 *S s4 | s3 | s4 | t3 | t4|]). 
Proof. unfold llex_p2.
       assert (F1 := b_conS _ _ _ _ C1 C3). 
       assert (F2 := conS _ _ _ _ C1 F1). rewrite F2. 
       assert (F3 := conS _ _ _ _ F1 C3). rewrite F3.
       case_eq(rS s3 (s3 *S s4)); intro A; case_eq(rS (s3 *S s4) s4); intro B; auto. 
Qed.


Lemma bop_llex_congruence : bop_congruence (S * T) (rS <*> rT) (bS llex [rS, argT] bT). 
Proof. intros [s1 t1] [s2 t2] [s3 t3] [s4 t4]; intros H1 H2.
       unfold brel_product in H1, H2. 
       destruct (bop_and_elim _ _ H1) as [C1 C2].
       destruct (bop_and_elim _ _ H2) as [C3 C4].
       unfold bop_llex. unfold brel_product. apply bop_and_intro. 
          exact (b_conS _ _ _ _ C1 C3).
          apply llex_p2_congruence; auto. 
Qed.

Lemma bop_llex_idempotent :bop_idempotent T rT bT → bop_idempotent (S * T) (rS <*> rT) (bS llex [rS, argT] bT). 
Proof. intros idemT (s, t). compute. assert (I := idemS s). rewrite I. apply symS in I. rewrite I. 
       rewrite idemT. reflexivity.
Qed.        

Lemma bop_llex_not_idempotent : bop_not_idempotent T rT bT →  bop_not_idempotent (S * T) (rS <*> rT) (bS llex [rS, argT] bT). 
Proof. intros [t P]. exists (wS, t). compute.
       assert (I := idemS wS). rewrite I. apply symS in I. rewrite I. exact P.
Defined. 

Lemma bop_llex_not_commutative : bop_not_commutative T rT bT → bop_not_commutative (S * T) (rS <*> rT) (bS llex [rS, argT] bT). 
Proof. intros [ [t t'] P]. exists ((wS, t), (wS, t')). compute. rewrite refS.
       (* Note : seems idempotence really is needed here. *) 
       assert (I := idemS wS). rewrite I. apply symS in I. rewrite I. exact P. 
Defined. 


Lemma llex_p2_commutative (commT : bop_commutative T rT bT) (s1 s2 : S) (t1 t2 : T) :
    ([|s1 *S s2 | s1 | s2 | t1 | t2|]) =T ([|s2 *S s1 | s2 | s1 | t2 | t1|]).
Proof. assert (F1 := commS s1 s2).
       assert (F2 := commT t1 t2). compute. 
       case_eq(rS s1 (s1 *S s2)); intro A; case_eq(rS s2 (s2 *S s1)); intro B.
       - apply symS in B. rewrite (tranS _ _ _ F1 B). 
         apply symS in A. apply symS in F1. 
         rewrite (tranS _ _ _  F1 A). apply commT. 
       - assert (F3 := tranS _ _ _ A F1). apply symS in F3. rewrite F3. 
         assert (F4 : (s1 *S s2) !=S s2).
            case_eq(rS (s1 *S s2) s2); intro F5; auto. 
               apply symS in F5. rewrite (tranS _ _ _ F5 F1) in B. discriminate B.
         rewrite F4. apply refT. 
       - apply symS in F1. assert (F3 := tranS _ _ _ B F1). 
         apply symS in F3. rewrite F3.
         assert (F4 : (s2 *S s1) !=S s1).
            case_eq(rS (s2 *S s1) s1); intro F5; auto.          
               apply symS in F5. rewrite (tranS _ _ _ F5 F1) in A. 
               discriminate A. 
         rewrite F4. apply refT. 
       - assert (F3 : (s2 *S s1) !=S s1).
            case_eq(rS (s2 *S s1) s1); intro F5; auto.          
               apply symS in F5. apply symS in F1. rewrite (tranS _ _ _ F5 F1) in A. 
               discriminate A.          
         assert (F4 : (s1 *S s2) !=S s2).
            case_eq(rS (s1 *S s2) s2); intro F5; auto.          
               apply symS in F5. rewrite (tranS _ _ _ F5 F1) in B. 
               discriminate B.          
         rewrite F3, F4. apply refT. 
Qed. 

Lemma bop_llex_commutative : bop_commutative T rT bT → bop_commutative (S * T) (rS <*> rT) (bS llex [rS, argT] bT). 
Proof. intros commT (s1, t1) (s2, t2).  
       unfold brel_product. unfold bop_llex. 
       apply bop_and_intro. 
          apply commS.
          apply llex_p2_commutative; auto. 
Qed. 

Lemma bop_llex_selective : 
     bop_selective S rS bS → bop_selective T rT bT → bop_selective (S * T) (rS <*> rT) (bS llex [rS, argT] bT). 
Proof. intros selS selT [s1 t1] [s2 t2].
       unfold bop_llex.
       unfold brel_product. unfold llex_p2.
       destruct (selS s1 s2) as [A | A]; destruct (selT t1 t2) as [B | B]; rewrite A. 
       - apply symS in A. rewrite A.
         case_eq(rS (s1 *S s2) s2); intro C. 
         + left. rewrite B. compute. reflexivity. 
         + left. rewrite refT. compute. reflexivity. 
       - apply symS in A. rewrite A.
         case_eq(rS (s1 *S s2) s2); intro C. 
         + right. rewrite B. compute. reflexivity. 
         + left. rewrite refT. compute. reflexivity. 
       - case_eq(rS s1 (s1 *S s2)); intro C. 
         + apply symS in C. rewrite C. 
           left. rewrite B. compute. reflexivity. 
         + right. rewrite refT. compute. reflexivity. 
       - case_eq(rS s1 (s1 *S s2)); intro C. 
         + apply symS in C. rewrite C. 
           right. rewrite B. compute. reflexivity. 
         + right. rewrite refT. compute. reflexivity. 
Qed.

Lemma bop_llex_not_selective_left : 
     bop_not_selective S rS bS → bop_not_selective (S * T) (rS <*> rT) (bS llex [rS, argT] bT). 
Proof. intros [ [s1 s2] [A B]]. exists ((s1, wT), (s2, wT)). compute.        
       rewrite A, B.  split; reflexivity. 
Defined.   


Lemma bop_llex_not_selective_right : 
     bop_selective S rS bS → bop_not_selective T rT bT → bop_not_selective (S * T) (rS <*> rT) (bS llex [rS, argT] bT). 
Proof. intros selS [ [t1 t2] [A B]]. exists ((wS, t1), (wS, t2)). compute.
       assert (ID := bop_selective_implies_idempotent S rS bS selS). 
       assert (I := ID wS). rewrite I. apply symS in I. rewrite I. rewrite A, B. split; reflexivity. 
Defined.


Lemma bop_llex_is_id (iS : S ) (iT : T )
       (pS : bop_is_id S rS bS iS) (pT : bop_is_id T rT bT iT) : 
         bop_is_id (S * T) (rS <*> rT) (bS llex [rS, argT] bT) (iS, iT). 
Proof. intros [s t].  compute.
       destruct (pS s) as [A1 A2]. destruct (pT t) as [B1 B2]. 
       rewrite A1, A2. apply symS in A1. apply symS in A2. rewrite A2.
       (* could use commutativity here but I don't want that dependency....*) 
       case_eq(rS iS (iS *S s)); intro C; case_eq(rS (s *S iS) iS); intro D; split; auto.  
Defined.


Lemma bop_llex_exists_id : bop_exists_id S rS bS -> bop_exists_id T rT bT -> 
                              bop_exists_id (S * T) (rS <*> rT) (bS llex [rS, argT] bT).
Proof. intros [iS pS] [iT pT]. exists (iS, iT). apply bop_llex_is_id; auto. Defined. 

Lemma bop_llex_not_exists_id_left : bop_not_exists_id S rS bS -> bop_not_exists_id (S * T) (rS <*> rT) (bS llex [rS, argT] bT).
Proof. unfold bop_not_exists_ann. 
       intros pS (s, t). destruct (pS s) as [x [F | F]]. 
          exists (x, t). left. compute. rewrite F. reflexivity. 
          exists (x, t). right. compute. rewrite F. reflexivity. 
Defined. 

Lemma bop_llex_not_exists_id_right: bop_not_exists_id T rT bT -> bop_not_exists_id (S * T) (rS <*> rT) (bS llex [rS, argT] bT).
Proof. unfold bop_not_exists_ann. 
       intros pT (s, t). destruct (pT t) as [x [F | F]].
       (* proof is shorter if we use idempotence, but I don't want to introduce the dependency if not needed ... *)
       - exists (s, x). left. compute.
         case_eq(rS (s *S s) s); intro G; auto.
         -- apply symS in G. rewrite G. exact F.
       - exists (s, x). right. compute. 
         case_eq(rS (s *S s) s); intro G; auto.
         -- apply symS in G. rewrite G. exact F.
Defined.


Lemma bop_llex_not_exists_id (D : (bop_not_exists_id S rS bS) + (bop_not_exists_id T rT bT)) :
     bop_not_exists_id (S * T) (rS <*> rT) (bS llex [rS, argT] bT).
Proof. destruct D as [D | D].
       apply (bop_llex_not_exists_id_left D).
       apply (bop_llex_not_exists_id_right D).        
Defined. 



Lemma bop_llex_is_ann (aS : S ) (aT : T )
                         (pS : bop_is_ann S rS bS aS) (pT : bop_is_ann T rT bT aT) :
                             bop_is_ann (S * T) (rS <*> rT) (bS llex [rS, argT] bT) (aS, aT). 
Proof. intros [s t]. compute. 
       destruct (pS s) as [A1 A2]. destruct (pT t) as [B1 B2].
       rewrite A1, A2. apply symS in A1. rewrite A1.
       (* could use commutativity here but I don't want that dependency....*) 
       case_eq(rS s (s *S aS)); intro C; case_eq(rS (aS *S s) s); intro D; split; auto.  
Defined.


Lemma bop_llex_exists_ann : bop_exists_ann S rS bS -> bop_exists_ann T rT bT -> 
                              bop_exists_ann (S * T) (rS <*> rT) (bS llex [rS, argT] bT).
Proof. intros [iS pS] [iT pT]. exists (iS, iT). apply bop_llex_is_ann; auto. Defined. 

Lemma bop_llex_not_exists_ann_left : bop_not_exists_ann S rS bS -> bop_not_exists_ann (S * T) (rS <*> rT) (bS llex [rS, argT] bT).
Proof. intros pS (s, t). destruct (pS s) as [x [F | F]]. 
          exists (x, t). left. compute. rewrite F. reflexivity. 
          exists (x, t). right. compute. rewrite F. reflexivity. 
Defined. 

Lemma bop_llex_not_exists_ann_right : bop_not_exists_ann T rT bT -> bop_not_exists_ann (S * T) (rS <*> rT) (bS llex [rS, argT] bT).
Proof. intros pT (s, t). destruct (pT t) as [x [F | F]].
       (* proof is shorter if we use idempotence, but I don't want to introduce the dependency if not needed ... *)
       - exists (s, x). left. compute.
         case_eq(rS (s *S s) s); intro G; auto.
         -- apply symS in G. rewrite G. exact F.
       - exists (s, x). right. compute. 
         case_eq(rS (s *S s) s); intro G; auto.
         -- apply symS in G. rewrite G. exact F.
Defined. 

Lemma bop_llex_not_exists_ann (D : (bop_not_exists_ann S rS bS) + (bop_not_exists_ann T rT bT)) :
     bop_not_exists_ann (S * T) (rS <*> rT) (bS llex [rS, argT] bT).
Proof. destruct D as [D | D].
       apply (bop_llex_not_exists_ann_left D).
       apply (bop_llex_not_exists_ann_right D).        
Defined. 


(********************* "multiplicative" properties **************************************

The only reason we need these results is that the AMCAS/MCAS version of llex 
cast things up to the top of the hierarchy in order to avoid an HUGE number of 
llex products defined lower in the hierarchy ... 
 
*)

Lemma bop_llex_not_anti_left_initial_proof  (P : (bop_selective S rS bS) + (bop_is_id T rT bT argT)) : 
  bop_not_anti_left (S * T) (rS <*> rT) (bS llex [rS, argT] bT).
Proof. destruct (Pf wS) as [A B]. 
       case_eq (rS wS (wS *S (f wS))); intro C.
       + exists ((wS, wT), (f wS, wT)). compute. 
         rewrite C.
         assert (D : rS (wS *S f wS) (f wS) = false).
            case_eq(rS (wS *S f wS) (f wS)); intro E; auto.
            assert (F := commS wS (f wS)).
            assert (G := tranS _ _ _ C F). apply symS in F. 
            assert (H := tranS _ _ _ G F).
            assert (I := tranS _ _ _ H E).
            rewrite I in A. discriminate A. 
         rewrite D. apply refT. 
       + case_eq (rS (f wS) (wS *S (f wS))); intro D.
         ++ exists ((f wS, wT), (wS, wT)). compute.
            assert (E : rS (f wS) ((f wS) *S wS) = true).
               assert (F := commS wS (f wS)). exact (tranS _ _ _ D F). 
            rewrite E.
            assert (F : rS  ((f wS) *S wS) wS = false).
               case_eq(rS (f wS *S wS) wS); intro K; auto.
               assert (F := commS wS (f wS)).
               assert (G := tranS _ _ _ F K). apply symS in G. 
               rewrite G in C. discriminate C. 
            rewrite F. apply refT. 
         ++ destruct P as [sel | idP].
            +++ destruct (sel wS (f wS)) as [E | E]. 
                ++++ apply symS in E. rewrite E in C. discriminate C. 
                ++++ apply symS in E. rewrite E in D. discriminate D. 
            +++ exists ((wS, argT), (wS, argT)). compute.
                assert (E := idemS wS). rewrite E. apply symS in E. rewrite E.
                destruct (idP argT) as [F _]. apply symT. exact F. 
Defined.


Definition witness_llex_not_anti_left :=
  if rS wS (wS *S (f wS))
  then ((wS, wT), (f wS, wT))
  else if rS (f wS) (wS *S (f wS))
       then ((f wS, wT), (wS, wT))
       else ((wS, argT), (wS, argT)).

Lemma bop_llex_not_anti_left  (P : (bop_selective S rS bS) + (bop_is_id T rT bT argT)) : 
  bop_not_anti_left (S * T) (rS <*> rT) (bS llex [rS, argT] bT).
Proof. exists (witness_llex_not_anti_left). unfold witness_llex_not_anti_left. 
       destruct (Pf wS) as [A B]. 
       case_eq (rS wS (wS *S (f wS))); intro C.
       + compute. 
         rewrite C.
         assert (D : rS (wS *S f wS) (f wS) = false).
            case_eq(rS (wS *S f wS) (f wS)); intro E; auto.
            assert (F := commS wS (f wS)).
            assert (G := tranS _ _ _ C F). apply symS in F. 
            assert (H := tranS _ _ _ G F).
            assert (I := tranS _ _ _ H E).
            rewrite I in A. discriminate A. 
         rewrite D. apply refT. 
       + case_eq (rS (f wS) (wS *S (f wS))); intro D.
         ++ compute.
            assert (E : rS (f wS) ((f wS) *S wS) = true).
               assert (F := commS wS (f wS)). exact (tranS _ _ _ D F). 
            rewrite E.
            assert (F : rS  ((f wS) *S wS) wS = false).
               case_eq(rS (f wS *S wS) wS); intro K; auto.
               assert (F := commS wS (f wS)).
               assert (G := tranS _ _ _ F K). apply symS in G. 
               rewrite G in C. discriminate C. 
            rewrite F. apply refT. 
         ++ destruct P as [sel | idP].
            +++ destruct (sel wS (f wS)) as [E | E]. 
                ++++ apply symS in E. rewrite E in C. discriminate C. 
                ++++ apply symS in E. rewrite E in D. discriminate D. 
            +++ compute.
                assert (E := idemS wS). rewrite E. apply symS in E. rewrite E.
                destruct (idP argT) as [F _]. apply symT. exact F. 
Defined.




Lemma bop_llex_not_anti_right_initial_proof  (P : (bop_selective S rS bS) + (bop_is_id T rT bT argT)) : 
  bop_not_anti_right (S * T) (rS <*> rT) (bS llex [rS, argT] bT).
Proof. destruct (Pf wS) as [A B]. 
       case_eq (rS (f wS) (wS *S (f wS))); intro C.
       + exists ((f wS, wT), (wS, wT)). compute. 
         rewrite C.
         assert (D : rS wS (wS *S f wS) = false).
            case_eq(rS wS (wS *S f wS)); intro E; auto. apply symS in C. 
            assert (G := tranS _ _ _ E C). 
            rewrite G in A. discriminate A. 
         rewrite D. apply symS in C. rewrite C. apply refT. 
       + case_eq (rS wS (wS *S (f wS))); intro D.
         ++ exists ((wS, wT), (f wS, wT)). compute.
            assert (E : rS wS ((f wS) *S wS) = true).
               assert (F := commS wS (f wS)). exact (tranS _ _ _ D F). 
            rewrite E.  apply symS in E. rewrite E. 
            assert (F : rS  (f wS) ((f wS) *S wS) = false).
               case_eq(rS (f wS) (f wS *S wS)); intro K; auto.
               assert (F := commS (f wS) wS).
               assert (G := tranS _ _ _ K F). 
               rewrite G in C. discriminate C. 
            rewrite F. apply refT. 
         ++ destruct P as [sel | idP].
            +++ destruct (sel wS (f wS)) as [E | E]. 
                ++++ apply symS in E. rewrite E in D. discriminate D. 
                ++++ apply symS in E. rewrite E in C. discriminate C. 
            +++ exists ((wS, argT), (wS, argT)). compute.
                assert (E := idemS wS). rewrite E. apply symS in E. rewrite E.
                destruct (idP argT) as [F _]. apply symT. exact F. 
 Defined. 


Definition witness_llex_not_anti_right :=
  if rS (f wS) (wS *S (f wS))
  then ((f wS, wT), (wS, wT))
  else if rS wS (wS *S (f wS))
       then ((wS, wT), (f wS, wT))
       else ((wS, argT), (wS, argT)). 

Lemma bop_llex_not_anti_right  (P : (bop_selective S rS bS) + (bop_is_id T rT bT argT)) : 
  bop_not_anti_right (S * T) (rS <*> rT) (bS llex [rS, argT] bT).
Proof. exists (witness_llex_not_anti_right). unfold witness_llex_not_anti_right.
       destruct (Pf wS) as [A B]. 
       case_eq (rS (f wS) (wS *S (f wS))); intro C.
       + compute. 
         rewrite C.
         assert (D : rS wS (wS *S f wS) = false).
            case_eq(rS wS (wS *S f wS)); intro E; auto. apply symS in C. 
            assert (G := tranS _ _ _ E C). 
            rewrite G in A. discriminate A. 
         rewrite D. apply symS in C. rewrite C. apply refT. 
       + case_eq (rS wS (wS *S (f wS))); intro D.
         ++ compute.
            assert (E : rS wS ((f wS) *S wS) = true).
               assert (F := commS wS (f wS)). exact (tranS _ _ _ D F). 
            rewrite E.  apply symS in E. rewrite E. 
            assert (F : rS  (f wS) ((f wS) *S wS) = false).
               case_eq(rS (f wS) (f wS *S wS)); intro K; auto.
               assert (F := commS (f wS) wS).
               assert (G := tranS _ _ _ K F). 
               rewrite G in C. discriminate C. 
            rewrite F. apply refT. 
         ++ destruct P as [sel | idP].
            +++ destruct (sel wS (f wS)) as [E | E]. 
                ++++ apply symS in E. rewrite E in D. discriminate D. 
                ++++ apply symS in E. rewrite E in C. discriminate C. 
            +++ compute.
                assert (E := idemS wS). rewrite E. apply symS in E. rewrite E.
                destruct (idP argT) as [F _]. apply symT. exact F. 
 Defined. 


Lemma bop_llex_not_left_constant_initial_proof (P : (bop_selective S rS bS) + (bop_is_id T rT bT argT)) : 
        bop_not_left_constant (S * T) (rS <*> rT) (bS llex [rS, argT] bT). 
Proof. destruct (Pf wS) as [A B]. destruct (Pg wT) as [A' B']. 
       case_eq (rS wS (wS *S (f wS))); intro C; case_eq (rS (f wS) (wS *S (f wS))); intro D.  
       + apply symS in D. rewrite (tranS _ _ _ C D) in A. discriminate A. 
       + exists ((f wS, wT), ((wS, wT), (wS, g wT))). compute.
         rewrite (refS ((f wS *S wS))).
         assert (E := commS wS (f wS)).
         assert (F := tranS _ _ _ C E). apply symS in F. rewrite F. 
         assert (G : rS (f wS) (f wS *S wS) = false).
             case_eq(rS (f wS) (f wS *S wS)); intro G; auto. 
             apply symS in E. rewrite (tranS _ _ _ G E) in D. 
             discriminate D. 
         rewrite G. exact A'. 
       + exists ((wS, wT), ((f wS, wT), (f wS, g wT))). compute.
         rewrite (refS ((wS *S (f wS)))).
         apply symS in D. rewrite D.
         rewrite C. exact A'. 
       + destruct P as [sel | idP].
            +++ destruct (sel wS (f wS)) as [E | E]. 
                ++++ apply symS in E. rewrite E in C. discriminate C. 
                ++++ apply symS in E. rewrite E in D. discriminate D. 
            +++ exists ((wS, argT), ((wS, wT), (wS, g wT))). compute.
                rewrite (refS ((wS *S wS))).
                assert (E := idemS wS). rewrite E. apply symS in E. rewrite E.
                destruct (idP wT) as [F G]. destruct (idP (g wT)) as [H I]. 
                case_eq(rT (argT *T wT) (argT *T g wT)); intro J; auto. 
                assert (K := tranT _ _ _ J H). apply symT in K. 
                rewrite (tranT _ _ _ K F) in B'. discriminate B'. 
Defined.


Definition witness_llex_not_left_constant :=
  if rS wS (wS *S (f wS))
  then if rS (f wS) (wS *S (f wS))
       then ((wS, wT), ((wS, wT), (wS, wT))) (* case cannot be reached *) 
       else ((f wS, wT), ((wS, wT), (wS, g wT)))
  else if rS (f wS) (wS *S (f wS))
       then ((wS, wT), ((f wS, wT), (f wS, g wT)))
       else ((wS, argT), ((wS, wT), (wS, g wT))). 

Lemma bop_llex_not_left_constant (P : (bop_selective S rS bS) + (bop_is_id T rT bT argT)) : 
        bop_not_left_constant (S * T) (rS <*> rT) (bS llex [rS, argT] bT). 
Proof. exists witness_llex_not_left_constant; unfold witness_llex_not_left_constant. 
       destruct (Pf wS) as [A B]. destruct (Pg wT) as [A' B']. 
       case_eq (rS wS (wS *S (f wS))); intro C; case_eq (rS (f wS) (wS *S (f wS))); intro D.  
       + apply symS in D. rewrite (tranS _ _ _ C D) in A. discriminate A. 
       + compute.
         rewrite (refS ((f wS *S wS))).
         assert (E := commS wS (f wS)).
         assert (F := tranS _ _ _ C E). apply symS in F. rewrite F. 
         assert (G : rS (f wS) (f wS *S wS) = false).
             case_eq(rS (f wS) (f wS *S wS)); intro G; auto. 
             apply symS in E. rewrite (tranS _ _ _ G E) in D. 
             discriminate D. 
         rewrite G. exact A'. 
       + compute.
         rewrite (refS ((wS *S (f wS)))).
         apply symS in D. rewrite D.
         rewrite C. exact A'. 
       + destruct P as [sel | idP].
            +++ destruct (sel wS (f wS)) as [E | E]. 
                ++++ apply symS in E. rewrite E in C. discriminate C. 
                ++++ apply symS in E. rewrite E in D. discriminate D. 
            +++ compute.
                rewrite (refS ((wS *S wS))).
                assert (E := idemS wS). rewrite E. apply symS in E. rewrite E.
                destruct (idP wT) as [F G]. destruct (idP (g wT)) as [H I]. 
                case_eq(rT (argT *T wT) (argT *T g wT)); intro J; auto. 
                assert (K := tranT _ _ _ J H). apply symT in K. 
                rewrite (tranT _ _ _ K F) in B'. discriminate B'. 
Defined.

Lemma bop_llex_not_right_constant_initial_proof (P : (bop_selective S rS bS) + (bop_is_id T rT bT argT)) : 
        bop_not_right_constant (S * T) (rS <*> rT) (bS llex [rS, argT] bT). 
Proof. destruct (Pf wS) as [A B]. destruct (Pg wT) as [A' B']. 
       case_eq (rS wS (wS *S (f wS))); intro C; case_eq (rS (f wS) (wS *S (f wS))); intro D.  
       + apply symS in D. rewrite (tranS _ _ _ C D) in A. discriminate A. 
       + exists ((f wS, wT), ((wS, wT), (wS, g wT))). compute.
         rewrite (refS ((wS *S f wS))). rewrite C. 
         assert (G : rS (wS *S (f wS)) (f wS) = false).
             case_eq(rS (wS *S (f wS)) (f wS)); intro G; auto. 
             apply symS in G. rewrite G in D. 
             discriminate D. 
         rewrite G. exact A'. 
       + exists ((wS, wT), ((f wS, wT), (f wS, g wT))). compute.
         rewrite (refS (((f wS) *S wS))). 
         assert (E := commS wS (f wS)).
         rewrite (tranS _ _ _ D E).
         assert (F : rS (f wS *S wS) wS = false).
            case_eq(rS (f wS *S wS) wS); intro G; auto. 
            apply symS in G. apply symS in E. rewrite (tranS _ _ _ G E) in C. 
             discriminate C. 
         rewrite F. exact A'. 
       + destruct P as [sel | idP].
            +++ destruct (sel wS (f wS)) as [E | E]. 
                ++++ apply symS in E. rewrite E in C. discriminate C. 
                ++++ apply symS in E. rewrite E in D. discriminate D. 
            +++ exists ((wS, argT), ((wS, wT), (wS, g wT))). compute.
                rewrite (refS ((wS *S wS))).
                assert (E := idemS wS). rewrite E. apply symS in E. rewrite E.
                destruct (idP wT) as [F G]. destruct (idP (g wT)) as [H I]. 
                case_eq(rT (wT *T argT) (g wT *T argT)); intro J; auto. 
                assert (K := tranT _ _ _ J I). apply symT in K. 
                rewrite (tranT _ _ _ K G) in B'. discriminate B'. 
Defined.

Definition witness_llex_not_right_constant :=
  if rS wS (wS *S (f wS))
  then if rS (f wS) (wS *S (f wS))
       then ((wS, wT), ((wS, wT), (wS, wT))) (* case cannot be reached *) 
       else ((f wS, wT), ((wS, wT), (wS, g wT)))
  else if rS (f wS) (wS *S (f wS))
       then ((wS, wT), ((f wS, wT), (f wS, g wT)))
       else ((wS, argT), ((wS, wT), (wS, g wT))). 


Lemma bop_llex_not_right_constant (P : (bop_selective S rS bS) + (bop_is_id T rT bT argT)) : 
        bop_not_right_constant (S * T) (rS <*> rT) (bS llex [rS, argT] bT). 
Proof. exists witness_llex_not_right_constant; unfold witness_llex_not_right_constant. 
       destruct (Pf wS) as [A B]. destruct (Pg wT) as [A' B']. 
       case_eq (rS wS (wS *S (f wS))); intro C; case_eq (rS (f wS) (wS *S (f wS))); intro D.  
       + apply symS in D. rewrite (tranS _ _ _ C D) in A. discriminate A. 
       + compute.
         rewrite (refS ((wS *S f wS))). rewrite C. 
         assert (G : rS (wS *S (f wS)) (f wS) = false).
             case_eq(rS (wS *S (f wS)) (f wS)); intro G; auto. 
             apply symS in G. rewrite G in D. 
             discriminate D. 
         rewrite G. exact A'. 
       + compute.
         rewrite (refS (((f wS) *S wS))). 
         assert (E := commS wS (f wS)).
         rewrite (tranS _ _ _ D E).
         assert (F : rS (f wS *S wS) wS = false).
            case_eq(rS (f wS *S wS) wS); intro G; auto. 
            apply symS in G. apply symS in E. rewrite (tranS _ _ _ G E) in C. 
             discriminate C. 
         rewrite F. exact A'. 
       + destruct P as [sel | idP].
            +++ destruct (sel wS (f wS)) as [E | E]. 
                ++++ apply symS in E. rewrite E in C. discriminate C. 
                ++++ apply symS in E. rewrite E in D. discriminate D. 
            +++ compute.
                rewrite (refS ((wS *S wS))).
                assert (E := idemS wS). rewrite E. apply symS in E. rewrite E.
                destruct (idP wT) as [F G]. destruct (idP (g wT)) as [H I]. 
                case_eq(rT (wT *T argT) (g wT *T argT)); intro J; auto. 
                assert (K := tranT _ _ _ J I). apply symT in K. 
                rewrite (tranT _ _ _ K G) in B'. discriminate B'. 
Defined.


Lemma bop_llex_not_left_cancellative_initial_proof (P : (bop_selective S rS bS) + (bop_is_id T rT bT argT)) : 
        bop_not_left_cancellative (S * T) (rS <*> rT) (bS llex [rS, argT] bT). 
Proof. destruct (Pf wS) as [A B]. destruct (Pg wT) as [A' B']. 
       case_eq (rS wS (wS *S (f wS))); intro C; case_eq (rS (f wS) (wS *S (f wS))); intro D.  
       + apply symS in D. rewrite (tranS _ _ _ C D) in A. discriminate A. 
       + exists ((wS, wT), ((f wS, wT), (f wS, g wT))). compute.
         rewrite (refS ((wS *S f wS))). rewrite C. rewrite (refS (f wS)). 
         assert (G : rS (wS *S (f wS)) (f wS) = false).
             case_eq(rS (wS *S (f wS)) (f wS)); intro G; auto. 
             apply symS in G. rewrite G in D. 
             discriminate D. 
         rewrite G. split. apply refT. exact A'. 
       + exists ((f wS, wT), ((wS, wT), (wS, g wT))). compute.
         rewrite (refS (((f wS) *S wS))). rewrite (refS wS).
         assert (E := commS wS (f wS)).
         rewrite (tranS _ _ _ D E).
         assert (F : rS (f wS *S wS) wS = false).
            case_eq(rS (f wS *S wS) wS); intro G; auto. 
            apply symS in G. apply symS in E. rewrite (tranS _ _ _ G E) in C. 
             discriminate C. 
         rewrite F. split. apply refT. exact A'. 
       + destruct P as [sel | idP].
            +++ destruct (sel wS (f wS)) as [E | E]. 
                ++++ apply symS in E. rewrite E in C. discriminate C. 
                ++++ apply symS in E. rewrite E in D. discriminate D. 
            +++ exists ((wS, wT), ((f wS, wT), (f wS, g wT))). compute.
                rewrite (refS ((wS *S (f wS)))). rewrite C.  rewrite (refS (f wS)).
                assert (I : rS (wS *S f wS) (f wS) = false). 
                   case_eq(rS (wS *S f wS) (f wS)); intro E; auto. 
                   apply symS in E. rewrite E in D. discriminate D. 
                rewrite I. split. apply refT. exact A'. 
Defined.


Definition witness_llex_not_left_cancellative :=
  if rS wS (wS *S (f wS))
  then if rS (f wS) (wS *S (f wS))
       then ((wS, wT), ((wS, wT), (wS, wT)))  (* case not reached *) 
       else ((wS, wT), ((f wS, wT), (f wS, g wT)))
  else if rS (f wS) (wS *S (f wS))
       then ((f wS, wT), ((wS, wT), (wS, g wT)))
       else ((wS, wT), ((f wS, wT), (f wS, g wT))).

Lemma bop_llex_not_left_cancellative (P : (bop_selective S rS bS) + (bop_is_id T rT bT argT)) : 
        bop_not_left_cancellative (S * T) (rS <*> rT) (bS llex [rS, argT] bT). 
Proof. exists witness_llex_not_left_cancellative; unfold witness_llex_not_left_cancellative. 
       destruct (Pf wS) as [A B]. destruct (Pg wT) as [A' B']. 
       case_eq (rS wS (wS *S (f wS))); intro C; case_eq (rS (f wS) (wS *S (f wS))); intro D.  
       + apply symS in D. rewrite (tranS _ _ _ C D) in A. discriminate A. 
       + compute.
         rewrite (refS ((wS *S f wS))). rewrite C. rewrite (refS (f wS)). 
         assert (G : rS (wS *S (f wS)) (f wS) = false).
             case_eq(rS (wS *S (f wS)) (f wS)); intro G; auto. 
             apply symS in G. rewrite G in D. 
             discriminate D. 
         rewrite G. split. apply refT. exact A'. 
       + compute.
         rewrite (refS (((f wS) *S wS))). rewrite (refS wS).
         assert (E := commS wS (f wS)).
         rewrite (tranS _ _ _ D E).
         assert (F : rS (f wS *S wS) wS = false).
            case_eq(rS (f wS *S wS) wS); intro G; auto. 
            apply symS in G. apply symS in E. rewrite (tranS _ _ _ G E) in C. 
             discriminate C. 
         rewrite F. split. apply refT. exact A'. 
       + destruct P as [sel | idP].
            +++ destruct (sel wS (f wS)) as [E | E]. 
                ++++ apply symS in E. rewrite E in C. discriminate C. 
                ++++ apply symS in E. rewrite E in D. discriminate D. 
            +++ compute.
                rewrite (refS ((wS *S (f wS)))). rewrite C.  rewrite (refS (f wS)).
                assert (I : rS (wS *S f wS) (f wS) = false). 
                   case_eq(rS (wS *S f wS) (f wS)); intro E; auto. 
                   apply symS in E. rewrite E in D. discriminate D. 
                rewrite I. split. apply refT. exact A'. 
Defined.


Lemma bop_llex_not_right_cancellative_initial_proof (P : (bop_selective S rS bS) + (bop_is_id T rT bT argT)) : 
        bop_not_right_cancellative (S * T) (rS <*> rT) (bS llex [rS, argT] bT). 
Proof. destruct (Pf wS) as [A B]. destruct (Pg wT) as [A' B']. 
       case_eq (rS wS (wS *S (f wS))); intro C; case_eq (rS (f wS) (wS *S (f wS))); intro D.  
       + apply symS in D. rewrite (tranS _ _ _ C D) in A. discriminate A. 
       + exists ((wS, wT), ((f wS, wT), (f wS, g wT))). compute.
         rewrite (refS ((f wS *S wS))). rewrite (refS (f wS)).
         assert (E := commS (f wS) wS). apply symS in C.
         rewrite (tranS _ _ _ E C). 
         assert (G : rS (f wS) (f wS *S wS) = false).
             case_eq(rS (f wS) (f wS *S wS)); intro G; auto. 
             rewrite (tranS _ _ _ G E) in D. 
             discriminate D. 
         rewrite G. split. apply refT. exact A'. 
       + exists ((f wS, wT), ((wS, wT), (wS, g wT))). compute.
         rewrite (refS ((wS *S f wS))). rewrite (refS wS). apply symS in D. rewrite D. 
         assert (F : rS wS (wS *S f wS) = false).
            case_eq(rS wS (wS *S f wS)); intro G; auto.  rewrite G in C. 
             discriminate C. 
         rewrite F. split. apply refT. exact A'. 
       + destruct P as [sel | idP].
            +++ destruct (sel wS (f wS)) as [E | E]. 
                ++++ apply symS in E. rewrite E in C. discriminate C. 
                ++++ apply symS in E. rewrite E in D. discriminate D. 
            +++ exists ((wS, wT), ((f wS, wT), (f wS, g wT))). compute.
                rewrite (refS ((f wS *S wS))). rewrite (refS (f wS)).
                assert (E := commS (f wS) wS). 
                assert (F : rS (f wS) (f wS *S wS) = false). 
                   case_eq(rS (f wS) (f wS *S wS)); intro G; auto. 
                   rewrite (tranS _ _ _ G E) in D. discriminate D. 
                rewrite F.
                assert (G : rS (f wS *S wS) wS = false). 
                   case_eq(rS (f wS *S wS) wS); intro G; auto. 
                   apply symS in G. rewrite (tranS _ _ _ G E) in C. discriminate C.
                rewrite G. split. apply refT. exact A'. 
                
Defined.


Definition witness_llex_not_right_cancellative :=
  if rS wS (wS *S (f wS))
  then if rS (f wS) (wS *S (f wS))
       then ((wS, wT), ((wS, wT), (wS, wT)))  (* case not reached *) 
       else ((wS, wT), ((f wS, wT), (f wS, g wT)))
  else if rS (f wS) (wS *S (f wS))
       then ((f wS, wT), ((wS, wT), (wS, g wT)))
       else ((wS, wT), ((f wS, wT), (f wS, g wT))).

Lemma bop_llex_not_right_cancellative (P : (bop_selective S rS bS) + (bop_is_id T rT bT argT)) : 
        bop_not_right_cancellative (S * T) (rS <*> rT) (bS llex [rS, argT] bT). 
Proof. exists witness_llex_not_right_cancellative; unfold witness_llex_not_right_cancellative.
       destruct (Pf wS) as [A B]. destruct (Pg wT) as [A' B']. 
       case_eq (rS wS (wS *S (f wS))); intro C; case_eq (rS (f wS) (wS *S (f wS))); intro D.  
       + apply symS in D. rewrite (tranS _ _ _ C D) in A. discriminate A. 
       + compute.
         rewrite (refS ((f wS *S wS))). rewrite (refS (f wS)).
         assert (E := commS (f wS) wS). apply symS in C.
         rewrite (tranS _ _ _ E C). 
         assert (G : rS (f wS) (f wS *S wS) = false).
             case_eq(rS (f wS) (f wS *S wS)); intro G; auto. 
             rewrite (tranS _ _ _ G E) in D. 
             discriminate D. 
         rewrite G. split. apply refT. exact A'. 
       + compute.
         rewrite (refS ((wS *S f wS))). rewrite (refS wS). apply symS in D. rewrite D. 
         assert (F : rS wS (wS *S f wS) = false).
            case_eq(rS wS (wS *S f wS)); intro G; auto.  rewrite G in C. 
             discriminate C. 
         rewrite F. split. apply refT. exact A'. 
       + destruct P as [sel | idP].
            +++ destruct (sel wS (f wS)) as [E | E]. 
                ++++ apply symS in E. rewrite E in C. discriminate C. 
                ++++ apply symS in E. rewrite E in D. discriminate D. 
            +++ compute.
                rewrite (refS ((f wS *S wS))). rewrite (refS (f wS)).
                assert (E := commS (f wS) wS). 
                assert (F : rS (f wS) (f wS *S wS) = false). 
                   case_eq(rS (f wS) (f wS *S wS)); intro G; auto. 
                   rewrite (tranS _ _ _ G E) in D. discriminate D. 
                rewrite F.
                assert (G : rS (f wS *S wS) wS = false). 
                   case_eq(rS (f wS *S wS) wS); intro G; auto. 
                   apply symS in G. rewrite (tranS _ _ _ G E) in C. discriminate C.
                rewrite G. split. apply refT. exact A'. 
Defined.


Lemma bop_llex_not_is_left_original_proof : bop_not_is_left (S * T) (rS <*> rT) (bS llex [rS, argT] bT). 
Proof. destruct (bop_commutative_implies_not_is_left S rS bS wS f Pf symS tranS commS) as [[s1 s2] Q]. 
       exists ((s1, wT), (s2, wT)). compute. rewrite Q. reflexivity. 
Defined.

Definition witness_llex_not_is_left := 
  match cef_commutative_implies_not_is_left rS bS wS f with
  | (s1, s2) => ((s1, wT), (s2, wT))
  end.

(* hmmmm, seems like too much effort here ... 
   redoing the proof of bop_commutative_implies_not_is_left? 
*) 
Lemma bop_llex_not_is_left : bop_not_is_left (S * T) (rS <*> rT) (bS llex [rS, argT] bT). 
Proof. exists witness_llex_not_is_left. compute. 
       case_eq(rS (f wS *S wS) wS); intro A.
       + rewrite A.
         case_eq(rS (f wS *S wS) (f wS)); intro B.
         ++ destruct (Pf wS) as [C D].
            apply symS in A. rewrite (tranS _ _ _ A B) in C.
            discriminate C. 
         ++ reflexivity. 
       + case_eq(rS (wS *S f wS) wS); intro B.
         ++ assert (C := commS (f wS) wS).
            assert (D := tranS _ _ _ C B).
            rewrite D in A. discriminate A. 
         ++ reflexivity. 
Defined.


Lemma bop_llex_not_is_right_initial_proof : bop_not_is_right (S * T) (rS <*> rT) (bS llex [rS, argT] bT).
Proof. destruct (bop_commutative_implies_not_is_right S rS bS wS f Pf symS tranS commS) as [[s1 s2] Q]. 
       exists ((s1, wT), (s2, wT)). compute. rewrite Q. reflexivity. 
Defined.

Definition witness_llex_not_is_right := 
  match cef_commutative_implies_not_is_right rS bS wS f with
  | (s1, s2) => ((s1, wT), (s2, wT))
  end.

Lemma bop_llex_not_is_right : bop_not_is_right (S * T) (rS <*> rT) (bS llex [rS, argT] bT). 
Proof. exists witness_llex_not_is_right. compute. 
       case_eq(rS (f wS *S wS) wS); intro A.
       + case_eq(rS (f wS *S wS) (f wS)); intro B.
         ++ destruct (Pf wS) as [C D].
            apply symS in A. rewrite (tranS _ _ _ A B) in C.
            discriminate C. 
         ++ case_eq(rS (wS *S f wS) (f wS)); intro C.
            +++ assert (D := commS (f wS) wS).
                rewrite (tranS _ _ _ D C) in B.
                discriminate B. 
            +++ reflexivity.
       + case_eq(rS (f wS *S wS) wS); intro B.
         ++ rewrite B in A. discriminate A. 
         ++ reflexivity. 
Defined.



(*================== ASSOCIATIVITY ========================

A bit tedious .... ;-) 

*) 

Lemma llex_assoc_case1_aux 
  {s1 s2 s3 : S}
  {t1 t2 t3 : T}
  (A1 : (s1 *S s2) =S ((s1 *S s2) *S s3))
  (C1 : ((s1 *S s2) *S s3) =S s3)
  (A2 : s1 =S (s1 *S (s2 *S s3)))
  (C2 : (s1 *S (s2 *S s3)) =S (s2 *S s3)):
  (([|s1 *S s2 | s1 | s2 | t1 | t2|]) *T t3) =T (t1 *T ([|s2 *S s3 | s2 | s3 | t2 | t3|])). 
Proof. unfold llex_p2.
       assert (D := tranS _ _ _ A2 C2). apply symS in C1. apply symS in A1. 
       assert (E := tranS _ _ _ C1 A1).
       assert (F := assS s1 s2 s3). 
       assert (G := tranS _ _ _ C1 F). apply symS in G. 
       assert (H := tranS _ _ _ A2 G). 
       assert (I := tranS _ _ _ H E). rewrite I. apply symS in D. 
       assert (J := tranS _ _ _ D H). rewrite J.
       apply symS in E. apply symS in J.
       assert (K := tranS _ _ _ E J). 
       case_eq(rS (s1 *S s2) s2); intro L; case_eq(rS s2 (s2 *S s3)); intro M. 
       - apply assT. 
       - apply symS in L. rewrite (tranS _ _ _ L K) in M. discriminate M. 
       - apply symS in M. rewrite (tranS _ _ _ K M) in L. discriminate L. 
       - apply refT. 
Qed. 

Lemma llex_assoc_case1 
  (s1 s2 s3 : S)
  (t1 t2 t3 : T)
  (A1 : (s1 *S s2) =S ((s1 *S s2) *S s3))
  (C1 : ((s1 *S s2) *S s3) =S s3)
  (A2 : s1 =S (s1 *S (s2 *S s3)))
  (C2 : (s1 *S (s2 *S s3)) =S (s2 *S s3)):
  ([|(s1 *S s2) *S s3 | s1 *S s2 | s3 | [|s1 *S s2 | s1 | s2 | t1 | t2|] | t3|]) =T
  ([|s1 *S (s2 *S s3) | s1 | s2 *S s3 | t1 | [|s2 *S s3 | s2 | s3 | t2 | t3|]|]). 
Proof. unfold llex_p2 at 1 3. rewrite A1, A2, C1, C2. exact (llex_assoc_case1_aux A1 C1 A2 C2). Qed. 

Lemma llex_assoc_case2_aux
  {s1 s2 s3 : S}
  {t1 t2 t3 : T}
  (A1 : (s1 *S s2) =S ((s1 *S s2) *S s3))
  (C1 : ((s1 *S s2) *S s3) =S s3)
  (A2 : s1 =S (s1 *S (s2 *S s3)))
  (C2 : (s1 *S (s2 *S s3)) !=S (s2 *S s3)) :
  (([|s1 *S s2 | s1 | s2 | t1 | t2|]) *T t3) =T t1. 
Proof. unfold llex_p2.
       apply symS in C1. apply symS in A1. 
       assert (E := tranS _ _ _ C1 A1).
       assert (F := assS s1 s2 s3). 
       assert (G := tranS _ _ _ C1 F). apply symS in G. 
       assert (H := tranS _ _ _ A2 G). 
       assert (I := tranS _ _ _ H E). rewrite I.
       assert (J : (s1 *S (s2 *S s3)) =S (s2 *S s3)). 
       (*
         s1 * (s2 * s3)
         = s1 * ((s2 * s2) * s3)
         = s1 * (s2 * (s2 * s3))
         = (s1 * s2) * (s2 * s3)
         = s3 * (s2 * s3)
         = (s3 * s2) * s3
         = (s2 * s3) * s3
         = s2 * (s3 * s3)
         = s2 * s3 

        *)
          assert (J1 : (s1 *S (s2 *S s3)) =S (s1 *S ((s2 *S s2) *S s3))).
             assert (J2 := b_conS _ _ _ _ (idemS s2) (refS s3)). 
             assert (J3 := b_conS _ _ _ _ (refS s1) J2).  apply symS in J3.
             exact J3.
          assert (J2 : (s1 *S (s2 *S s3)) =S (s1 *S (s2 *S (s2 *S s3)))).
             assert (J3 := assS s2 s2 s3). 
             assert (J4 := b_conS _ _ _ _ (refS s1) J3).  apply symS in J3.
             exact (tranS _ _ _ J1 J4).
          assert (J3 : (s1 *S (s2 *S s3)) =S ((s1 *S s2) *S (s2 *S s3))).  
             assert (J4 := assS s1 s2 (s2 *S s3)). apply symS in J4. 
             exact (tranS _ _ _ J2 J4).
          assert (J4 : (s1 *S (s2 *S s3)) =S (s3 *S (s2 *S s3))).
             assert (J5 := b_conS _ _ _ _ E (refS (s2 *S s3))). apply symS in J5.
             exact (tranS _ _ _ J3 J5).             
          assert (J5 : (s1 *S (s2 *S s3)) =S ((s2 *S s3) *S s3)).
             assert (J6 := commS s3 (s2 *S s3)).
             exact (tranS _ _ _ J4 J6). 
          assert (J7 : (s1 *S (s2 *S s3)) =S (s2 *S (s3 *S s3))).  
             assert (J8 := assS s2 s3 s3).  
             exact (tranS _ _ _ J5 J8). 
          assert (J8 : (s1 *S (s2 *S s3)) =S (s2 *S s3)).
             assert (J9 := b_conS _ _ _ _ (refS s2) (idemS s3)). 
             exact (tranS _ _ _ J7 J9). 
         exact J8. 
      rewrite J in C2. discriminate C2. 
Qed. 

Lemma llex_assoc_case2
  (s1 s2 s3 : S)
  (t1 t2 t3 : T)
  (A1 : (s1 *S s2) =S ((s1 *S s2) *S s3))
  (C1 : ((s1 *S s2) *S s3) =S s3)
  (A2 : s1 =S (s1 *S (s2 *S s3)))
  (C2 : (s1 *S (s2 *S s3)) !=S (s2 *S s3)) :
  ([|(s1 *S s2) *S s3 | s1 *S s2 | s3 | [|s1 *S s2 | s1 | s2 | t1 | t2|] | t3|]) =T
  ([|s1 *S (s2 *S s3) | s1 | s2 *S s3 | t1 | [|s2 *S s3 | s2 | s3 | t2 | t3|]|]). 
Proof. unfold llex_p2 at 1 3. rewrite A1, A2, C1, C2. exact (llex_assoc_case2_aux A1 C1 A2 C2). Qed. 


Lemma llex_assoc_case3_aux_selS
  {s1 s2 s3 : S}
  {t1 t2 t3 : T}
  (selS : bop_selective S rS bS) 
  (A1 : (s1 *S s2) =S ((s1 *S s2) *S s3))
  (C1 : ((s1 *S s2) *S s3) =S s3)
  (A2 : s1 !=S (s1 *S (s2 *S s3)))
  (C2 : (s1 *S (s2 *S s3)) =S (s2 *S s3)) :
  (([|s1 *S s2 | s1 | s2 | t1 | t2|]) *T t3) =T ([|s2 *S s3 | s2 | s3 | t2 | t3|]).
Proof. unfold llex_p2.
       assert (F0 := assS s1 s2 s3).
       assert (F2 := tranS _ _ _ A1 F0). 
       assert (F3 := tranS _ _ _ F2 C2). 
       assert (F4 : s1 !=S (s1 *S s2)).
          case_eq(rS s1 (s1 *S s2)); intro F4; auto.
             rewrite (tranS _ _ _ F4 F2) in A2. discriminate A2. 
       rewrite F4.
       assert (F5 : (s2 *S s3) =S s3). apply symS in F3.
          assert (F6 := tranS _ _ _ F3 A1). 
          exact (tranS _ _ _ F6 C1). 
       rewrite F5. 
       destruct (selS s1 s2) as [A | A]; destruct (selS s2 s3) as [B | B]. 
       - apply symS in B. rewrite B.
         case_eq(rS (s1 *S s2) s2); intro F6.
         + apply refT. 
         + apply symS in B. rewrite (tranS _ _ _ F3 B) in F6.
           discriminate F6.
       - apply symS in A. rewrite A in F4. discriminate F4. 
       - rewrite A. apply symS in B. rewrite B. apply refT. 
       - rewrite A. apply symS in A. rewrite (tranS _ _ _ A F3). apply refT. 
Qed. 

Lemma llex_assoc_case3_aux_idT 
  {s1 s2 s3 : S}
  {t1 t2 t3 : T}
  (idT : bop_is_id T rT bT argT) 
  (A1 : (s1 *S s2) =S ((s1 *S s2) *S s3))
  (C1 : ((s1 *S s2) *S s3) =S s3)
  (A2 : s1 !=S (s1 *S (s2 *S s3)))
  (C2 : (s1 *S (s2 *S s3)) =S (s2 *S s3)) :
  (([|s1 *S s2 | s1 | s2 | t1 | t2|]) *T t3) =T ([|s2 *S s3 | s2 | s3 | t2 | t3|]).
Proof. unfold llex_p2.
       assert (F1 := assS s1 s2 s3).
       assert (F2 := tranS _ _ _ A1 C1).
       assert (F3 := tranS _ _ _ A1 F1). 
       assert (F4 := tranS _ _ _ F3 C2). apply symS in F4. 
       assert (F5 := tranS _ _ _ F4 F2).     
       case_eq(rS s1 (s1 *S s2)); intro A; case_eq(rS s2 (s2 *S s3)); intro B.
       - case_eq(rS (s1 *S s2) s2); intro C; case_eq(rS (s2 *S s3) s3); intro D.
         + apply symS in F4. assert (F6 := tranS _ _ _ A F4). 
           assert (F7 := tranS _ _ _ F6 D). apply symS in C1. 
           assert (F8 := tranS _ _ _ F7 C1).
           assert (F9 := tranS _ _ _ F8 F1).
           rewrite F9 in A2. discriminate A2. 
         + rewrite F5 in D. discriminate D. 
         + apply symS in F4. assert (F6 := tranS _ _ _ A F4). 
           assert (F7 := tranS _ _ _ F6 D). apply symS in C1. 
           assert (F8 := tranS _ _ _ F7 C1).
           assert (F9 := tranS _ _ _ F8 F1).
           rewrite F9 in A2. discriminate A2. 
         + rewrite F5 in D. discriminate D. 
       - case_eq(rS (s1 *S s2) s2); intro C; case_eq(rS (s2 *S s3) s3); intro D.
         + apply symS in F4. assert (F6 := tranS _ _ _ A F4). 
           assert (F7 := tranS _ _ _ F6 D). apply symS in C1. 
           assert (F8 := tranS _ _ _ F7 C1).
           assert (F9 := tranS _ _ _ F8 F1).
           rewrite F9 in A2. discriminate A2. 
         + rewrite F5 in D. discriminate D. 
         + apply symS in F4. assert (F6 := tranS _ _ _ A F4). 
           assert (F7 := tranS _ _ _ F6 D). apply symS in C1. 
           assert (F8 := tranS _ _ _ F7 C1).
           assert (F9 := tranS _ _ _ F8 F1).
           rewrite F9 in A2. discriminate A2. 
         + rewrite F5 in D. discriminate D. 
       - case_eq(rS (s1 *S s2) s2); intro C; case_eq(rS (s2 *S s3) s3); intro D.
         + apply refT. 
         + rewrite F5 in D. discriminate D. 
         + assert (F6 := tranS _ _ _ B F4). apply symS in F6.
           rewrite F6 in C. discriminate C. 
         + rewrite F5 in D. discriminate D. 
       - case_eq(rS (s1 *S s2) s2); intro C; case_eq(rS (s2 *S s3) s3); intro D.
         + assert (F6 := tranS _ _ _ F4 C). apply symS in F6.
           rewrite F6 in B. discriminate B. 
         + rewrite F5 in D. discriminate D. 
         + destruct (idT t3) as [F6 F7]. exact F6.
         + rewrite F5 in D. discriminate D. 
Qed. 
  
Lemma llex_assoc_case3 
  (s1 s2 s3 : S)
  (t1 t2 t3 : T)
  (selS_or_idT : (bop_selective S rS bS) + (bop_is_id T rT bT argT)) 
  (A1 : (s1 *S s2) =S ((s1 *S s2) *S s3))
  (C1 : ((s1 *S s2) *S s3) =S s3)
  (A2 : s1 !=S (s1 *S (s2 *S s3)))
  (C2 : (s1 *S (s2 *S s3)) =S (s2 *S s3)) :
  ([|(s1 *S s2) *S s3 | s1 *S s2 | s3 | [|s1 *S s2 | s1 | s2 | t1 | t2|] | t3|]) =T
  ([|s1 *S (s2 *S s3) | s1 | s2 *S s3 | t1 | [|s2 *S s3 | s2 | s3 | t2 | t3|]|]). 
Proof. unfold llex_p2 at 1 3. rewrite A1, A2, C1, C2.
       destruct selS_or_idT  as [selS | idT].
       - exact (llex_assoc_case3_aux_selS selS A1 C1 A2 C2).
       - exact (llex_assoc_case3_aux_idT idT A1 C1 A2 C2). 
Qed. 

Lemma llex_assoc_case4_aux 
  {s1 s2 s3 : S}
  {t1 t2 t3 : T}
  (A1 : (s1 *S s2) =S ((s1 *S s2) *S s3))
  (C1 : ((s1 *S s2) *S s3) =S s3)
  (A2 : s1 !=S (s1 *S (s2 *S s3)))
  (C2 : (s1 *S (s2 *S s3)) !=S (s2 *S s3)) :
  (([|s1 *S s2 | s1 | s2 | t1 | t2|]) *T t3) =T argT.
Proof. unfold llex_p2.
       assert (A := assS s1 s2 s3). 
       assert (B := assS s1 s2 s2). 
       assert (C := assS s2 s1 s2). apply symS in C1.        
       assert (F1 : (s2 *S s3) =S (s1 *S (s2 *S s3))).
           (* s2 *S s3
              = s2 *S ((s1 *S s2) *S s3)
              = (s2 *S (s1 *S s2)) *S s3
              = ((s1 *S s2) * s2) *S s3
              = ((s1 *S (s2 * s2)) *S s3
              = ((s1 *S s2) *S s3
              = (s1 *S (s2 *S s3))
            *)
          assert (F5 := b_conS _ _ _ _ (refS s2) C1). 
          assert (F6 := assS s2 (s1 *S s2) s3). apply symS in F6. 
          assert (F7 := tranS _ _ _ F5 F6).
          assert (F8 := commS s2 (s1 *S s2)). 
          assert (F9 := b_conS _ _ _ _ F8 (refS s3)). 
          assert (F10 := tranS _ _ _ F7 F9).
          assert (F11 := assS s1 s2 s2). 
          assert (F12 := b_conS _ _ _ _ F11 (refS s3)). 
          assert (F13 := tranS _ _ _ F10 F12).
          assert (F14 := b_conS _ _ _ _ (refS s1) (idemS s2)). 
          assert (F15 := b_conS _ _ _ _ F14 (refS s3)).
          assert (F16 := tranS _ _ _ F13 F15).          
          assert (F17 := assS s1 s2 s3). 
          exact (tranS _ _ _ F16 F17). 
       apply symS in F1. rewrite F1 in C2. discriminate C2. 
Qed. 

Lemma llex_assoc_case4 
  (s1 s2 s3 : S)
  (t1 t2 t3 : T)
  (A1 : (s1 *S s2) =S ((s1 *S s2) *S s3))
  (C1 : ((s1 *S s2) *S s3) =S s3)
  (A2 : s1 !=S (s1 *S (s2 *S s3)))
  (C2 : (s1 *S (s2 *S s3)) !=S (s2 *S s3)) :
  ([|(s1 *S s2) *S s3 | s1 *S s2 | s3 | [|s1 *S s2 | s1 | s2 | t1 | t2|] | t3|]) =T
  ([|s1 *S (s2 *S s3) | s1 | s2 *S s3 | t1 | [|s2 *S s3 | s2 | s3 | t2 | t3|]|]). 
Proof. unfold llex_p2 at 1 3. rewrite A1, A2, C1, C2. exact (llex_assoc_case4_aux A1 C1 A2 C2). Qed. 

Lemma llex_assoc_case5_aux
  {s1 s2 s3 : S}
  {t1 t2 t3 : T}
  (selS_or_idT : (bop_selective S rS bS) + (bop_is_id T rT bT argT))     
  (A1 : (s1 *S s2) =S ((s1 *S s2) *S s3))
  (C1 : ((s1 *S s2) *S s3) !=S s3)
  (A2 : s1 =S (s1 *S (s2 *S s3)))
  (C2 : (s1 *S (s2 *S s3)) =S (s2 *S s3)) :
  ([|s1 *S s2 | s1 | s2 | t1 | t2|]) =T (t1 *T ([|s2 *S s3 | s2 | s3 | t2 | t3|])).
Proof. unfold llex_p2.
       assert (F1 := assS s1 s2 s3). 
       assert (F2 := tranS _ _ _ A1 F1). apply symS in F2. 
       assert (F3 := tranS _ _ _ A2 F2). rewrite F3.
       assert (F4 : (s1 *S s2) =S (s2 *S s3)). apply symS in F3. 
          assert (F5 := tranS _ _ _ F3 A2). 
          exact (tranS _ _ _ F5 C2).           
       assert (F5 : rS (s2 *S s3) s3 = false).
          case_eq(rS (s2 *S s3) s3); intro F6; auto. 
             assert (F7 := tranS _ _ _ F4 F6). apply symS in F7. 
             assert (F8 := tranS _ _ _ F7 A1). apply symS in F8. 
             rewrite F8 in C1. discriminate C1. 
       rewrite F5.
       destruct selS_or_idT  as [selS | idT].
       - destruct(selS s1 s2) as [A | A].
         + case_eq(rS s2 (s2 *S s3)); intro B.
           *  assert (F6 : (s1 *S s2) =S s2). 
              apply symS in B. exact (tranS _ _ _ F4 B). 
           rewrite F6. apply refT.
           * destruct (selS s2 s3) as [F6 | F6].
               apply symS in F6. rewrite F6 in B. discriminate B. 
               rewrite F6 in F5. discriminate F5. 
         + rewrite A. apply symS in A. rewrite (tranS _ _ _ A F4). 
           apply refT. 
       - case_eq(rS (s1 *S s2) s2); intro A.
         + case_eq(rS s2 (s2 *S s3)); intro B.
           * apply refT. 
           * apply symS in A. rewrite (tranS _ _ _ A F4) in B.
             discriminate B. 
         + case_eq(rS s2 (s2 *S s3)); intro B.
           * apply symS in F4.
             assert (F6 := tranS _ _ _ B F4). apply symS in F6. 
             rewrite F6 in A. discriminate A.             
           *  destruct (idT t1) as [F6 F7]. apply symT. exact F7. 
Qed. 

       
Lemma llex_assoc_case5
  (s1 s2 s3 : S)
  (t1 t2 t3 : T)
  (selS_or_idT : (bop_selective S rS bS) + (bop_is_id T rT bT argT))   
  (A1 : (s1 *S s2) =S ((s1 *S s2) *S s3))
  (C1 : ((s1 *S s2) *S s3) !=S s3)
  (A2 : s1 =S (s1 *S (s2 *S s3)))
  (C2 : (s1 *S (s2 *S s3)) =S (s2 *S s3)) :
  ([|(s1 *S s2) *S s3 | s1 *S s2 | s3 | [|s1 *S s2 | s1 | s2 | t1 | t2|] | t3|]) =T
  ([|s1 *S (s2 *S s3) | s1 | s2 *S s3 | t1 | [|s2 *S s3 | s2 | s3 | t2 | t3|]|]).
Proof. unfold llex_p2 at 1 3. rewrite A1, A2, C1, C2. exact (llex_assoc_case5_aux selS_or_idT A1 C1 A2 C2). Qed.

Lemma llex_assoc_case6_aux
  {s1 s2 s3 : S}
  {t1 t2    : T}
  (A1 : (s1 *S s2) =S ((s1 *S s2) *S s3))
  (C1 : ((s1 *S s2) *S s3) !=S s3)
  (A2 : s1 =S (s1 *S (s2 *S s3)))
  (C2 : (s1 *S (s2 *S s3)) !=S (s2 *S s3)) : 
  ([|s1 *S s2 | s1 | s2 | t1 | t2|]) =T t1.
Proof. unfold llex_p2.
       assert (F1 := assS s1 s2 s3). 
       assert (F2 := tranS _ _ _ A1 F1). apply symS in F2. 
       rewrite (tranS _ _ _ A2 F2). 
       case_eq(rS (s1 *S s2) s2); intro A. 
       - assert (F3 : (s1 *S (s2 *S s3)) =S (s2 *S s3)).
            assert (F4 := b_conS _ _ _ _ A (refS s3)). apply symS in F1. 
            exact (tranS _ _ _ F1 F4).             
         rewrite F3 in C2. discriminate C2. 
       - apply refT. 
Qed. 

Lemma llex_assoc_case6
  (s1 s2 s3 : S)
  (t1 t2 t3 : T)
  (A1 : (s1 *S s2) =S ((s1 *S s2) *S s3))
  (C1 : ((s1 *S s2) *S s3) !=S s3)
  (A2 : s1 =S (s1 *S (s2 *S s3)))
  (C2 : (s1 *S (s2 *S s3)) !=S (s2 *S s3)) : 
  ([|(s1 *S s2) *S s3 | s1 *S s2 | s3 | [|s1 *S s2 | s1 | s2 | t1 | t2|] | t3|]) =T
  ([|s1 *S (s2 *S s3) | s1 | s2 *S s3 | t1 | [|s2 *S s3 | s2 | s3 | t2 | t3|]|]). 
Proof. unfold llex_p2 at 1 3. rewrite A1, A2, C1, C2. exact (llex_assoc_case6_aux A1 C1 A2 C2). Qed.   


Lemma llex_assoc_case7_aux
  {s1 s2 s3 : S}
  {t1 t2 t3 : T}
  (A1 : (s1 *S s2) =S ((s1 *S s2) *S s3))
  (C1 : ((s1 *S s2) *S s3) !=S s3)
  (A2 : s1 !=S (s1 *S (s2 *S s3)))
  (C2 : (s1 *S (s2 *S s3)) =S (s2 *S s3)) : 
  ([|s1 *S s2 | s1 | s2 | t1 | t2|]) =T ([|s2 *S s3 | s2 | s3 | t2 | t3|]).
Proof. unfold llex_p2.
       assert (F0 := assS s1 s2 s3). 
       case_eq(rS s1 (s1 *S s2)); intro A; case_eq(rS s2 (s2 *S s3)); intro B.
       - assert (F1 := tranS _ _ _ A A1).
         rewrite (tranS _ _ _ F1 F0) in A2. discriminate A2. 
       - assert (F1 := tranS _ _ _ A A1).
         rewrite (tranS _ _ _ F1 F0) in A2. discriminate A2. 
       - case_eq(rS (s1 *S s2) s2); intro C; case_eq(rS (s2 *S s3) s3); intro D. 
         + assert (F1 := tranS _ _ _ C2 D).
           rewrite (tranS _ _ _ F0 F1) in C1. discriminate C1.            
         + apply refT.
         + assert (F1 := tranS _ _ _ C2 D).
           rewrite (tranS _ _ _ F0 F1) in C1. discriminate C1.            
         + assert (F1 : s2 =S (s1 *S s2)). apply symS in C2. 
              assert (F2 := tranS _ _ _ B C2). apply symS in A1. apply symS in F0. 
              assert (F3 := tranS _ _ _ F0 A1). 
              exact (tranS _ _ _ F2 F3). 
           apply symS in F1. rewrite F1 in C. discriminate C.          
       - case_eq(rS (s1 *S s2) s2); intro C; case_eq(rS (s2 *S s3) s3); intro D. 
         + assert (F1 := tranS _ _ _ C2 D).
           rewrite (tranS _ _ _ F0 F1) in C1. discriminate C1.            
         + assert (F1 : (s2 *S s3) =S s2).
              assert (F2 := tranS _ _ _ A1 F0). 
              assert (F3 := tranS _ _ _ F2 C2). apply symS in F3. 
              exact (tranS _ _ _ F3 C). 
           apply symS in F1. rewrite F1 in B. discriminate B.            
         + assert (F1 := tranS _ _ _ C2 D).
           rewrite (tranS _ _ _ F0 F1) in C1. discriminate C1.            
         + apply refT.
Qed. 

  
Lemma llex_assoc_case7
  (s1 s2 s3 : S)
  (t1 t2 t3 : T)
  (A1 : (s1 *S s2) =S ((s1 *S s2) *S s3))
  (C1 : ((s1 *S s2) *S s3) !=S s3)
  (A2 : s1 !=S (s1 *S (s2 *S s3)))
  (C2 : (s1 *S (s2 *S s3)) =S (s2 *S s3)) : 
  ([|(s1 *S s2) *S s3 | s1 *S s2 | s3 | [|s1 *S s2 | s1 | s2 | t1 | t2|] | t3|]) =T
  ([|s1 *S (s2 *S s3) | s1 | s2 *S s3 | t1 | [|s2 *S s3 | s2 | s3 | t2 | t3|]|]). 
Proof. unfold llex_p2 at 1 3. rewrite A1, A2, C1, C2. exact (llex_assoc_case7_aux A1 C1 A2 C2). Qed.   


Lemma llex_assoc_case8_aux
  (s1 s2 s3 : S)
  (t1 t2 t3 : T)
  (A1 : (s1 *S s2) =S ((s1 *S s2) *S s3))
  (C1 : ((s1 *S s2) *S s3) !=S s3)
  (A2 : s1 !=S (s1 *S (s2 *S s3)))
  (C2 : (s1 *S (s2 *S s3)) !=S (s2 *S s3)) : 
 ([|s1 *S s2 | s1 | s2 | t1 | t2|]) =T argT.
Proof. compute.
       case_eq(rS s1 (s1 *S s2)); intro A; case_eq(rS (s1 *S s2) s2); intro B.
       - assert (F1 := tranS _ _ _ A A1).  
         assert (F2 := assS s1 s2 s3). 
         rewrite (tranS _ _ _ F1 F2) in A2.
         discriminate A2.
       - assert (F1 := tranS _ _ _ A A1).  
         assert (F2 := assS s1 s2 s3). 
         rewrite (tranS _ _ _ F1 F2) in A2.
         discriminate A2.
       - assert (F1 : (s1 *S (s2 *S s3)) =S (s2 *S s3)). 
           assert (F2 := b_conS _ _ _ _ B (refS s3)). 
           assert (F3 := assS s1 s2 s3). apply symS in F3. 
           exact (tranS _ _ _ F3 F2). 
         rewrite F1 in C2. discriminate C2. 
       - apply refT.
Qed. 

Lemma llex_assoc_case8
  (s1 s2 s3 : S)
  (t1 t2 t3 : T)
  (A1 : (s1 *S s2) =S ((s1 *S s2) *S s3))
  (C1 : ((s1 *S s2) *S s3) !=S s3)
  (A2 : s1 !=S (s1 *S (s2 *S s3)))
  (C2 : (s1 *S (s2 *S s3)) !=S (s2 *S s3)) : 
  ([|(s1 *S s2) *S s3 | s1 *S s2 | s3 | [|s1 *S s2 | s1 | s2 | t1 | t2|] | t3|]) =T
  ([|s1 *S (s2 *S s3) | s1 | s2 *S s3 | t1 | [|s2 *S s3 | s2 | s3 | t2 | t3|]|]). 
Proof. unfold llex_p2 at 1 3. rewrite A1, A2, C1, C2.
       exact (llex_assoc_case8_aux s1 s2 s3 t1 t2 t3 A1 C1 A2 C2).
Qed.   

Lemma llex_assoc_case9_aux
  (s1 s2 s3 : S)
  (t1 t2 t3 : T)
  (A1 : (s1 *S s2) !=S ((s1 *S s2) *S s3))
  (C1 : ((s1 *S s2) *S s3) =S s3)
  (A2 : s1 =S (s1 *S (s2 *S s3)))
  (C2 : (s1 *S (s2 *S s3)) =S (s2 *S s3)) : 
  t3 =T (t1 *T ([|s2 *S s3 | s2 | s3 | t2 | t3|])).
Proof. unfold llex_p2.
       assert (F : (s1 *S s2) =S ((s1 *S s2) *S s3)).
          (* F1 : s1 = (s2 *S s3). 
             so (s1 *S s2) 
                = ((s2 *S s3) *S s2) 
                = ((s3 *S s2) *S s2) 
                = s3 *S (s2 *S s2) 
                = s3 *S s2
                = s2 *S s3
                = ((s1 *S s2) *S s3)
          *) 
          assert (F1 := tranS _ _ _ A2 C2).
          assert (F2 := b_conS _ _ _ _ F1 (refS s2)). 
          assert (F3 := commS s2 s3). 
          assert (F4 := b_conS _ _ _ _ F3 (refS s2)). 
          assert (F5 := tranS _ _ _ F2 F4).
          assert (F6 := assS s3 s2 s2). 
          assert (F7 := tranS _ _ _ F5 F6).
          assert (F8 := b_conS _ _ _ _ (refS s3) (idemS s2)). 
          assert (F9 := tranS _ _ _ F7 F8). apply symS in F3. 
          assert (F10 := tranS _ _ _ F9 F3). apply symS in C2. 
          assert (F11 := tranS _ _ _ F10 C2).
          assert (F12 := assS s1 s2 s3). apply symS in F12. 
          exact (tranS _ _ _ F11 F12).
       rewrite F in A1. discriminate A1. 
Qed. 
       
Lemma llex_assoc_case9
  (s1 s2 s3 : S)
  (t1 t2 t3 : T)
  (A1 : (s1 *S s2) !=S ((s1 *S s2) *S s3))
  (C1 : ((s1 *S s2) *S s3) =S s3)
  (A2 : s1 =S (s1 *S (s2 *S s3)))
  (C2 : (s1 *S (s2 *S s3)) =S (s2 *S s3)) : 
  ([|(s1 *S s2) *S s3 | s1 *S s2 | s3 | [|s1 *S s2 | s1 | s2 | t1 | t2|] | t3|]) =T
  ([|s1 *S (s2 *S s3) | s1 | s2 *S s3 | t1 | [|s2 *S s3 | s2 | s3 | t2 | t3|]|]). 
Proof. unfold llex_p2 at 1 3. rewrite A1, A2, C1, C2.
       exact (llex_assoc_case9_aux s1 s2 s3 t1 t2 t3 A1 C1 A2 C2).       
Qed.   

Lemma llex_assoc_case10
  (s1 s2 s3 : S)
  (t1 t2 t3 : T)
  (A1 : (s1 *S s2) !=S ((s1 *S s2) *S s3))
  (C1 : ((s1 *S s2) *S s3) =S s3)
  (A2 : s1 =S (s1 *S (s2 *S s3)))
  (C2 : (s1 *S (s2 *S s3)) !=S (s2 *S s3))  : 
  ([|(s1 *S s2) *S s3 | s1 *S s2 | s3 | [|s1 *S s2 | s1 | s2 | t1 | t2|] | t3|]) =T
  ([|s1 *S (s2 *S s3) | s1 | s2 *S s3 | t1 | [|s2 *S s3 | s2 | s3 | t2 | t3|]|]). 
Proof. unfold llex_p2 at 1 3. rewrite A1, A2, C1, C2.
       assert (F1 := assS s1 s2 s3). apply symS in C1. 
       assert (F2 := tranS _ _ _ C1 F1). apply symS in F2. 
       assert (F3 := tranS _ _ _ A2 F2). 
       assert (F4 : (s1 *S (s2 *S s3)) =S (s2 *S s3)).
          (* 
             s1 *S (s2 *S s3)
             = s3 *S (s2 *S s3)
             = (s3 *S s2) *S s3
             = (s2 *S s3) *S s3
             = s2 *S (s3 *S s3)
             = s2 *S s3 
          *) 
          assert (F5 := b_conS _ _ _ _ F3 (refS (s2 *S s3))).
          assert (F6 := commS s3 (s2 *S s3)).
          assert (F7 := tranS _ _ _ F5 F6). 
          assert (F8 := assS s2 s3 s3). 
          assert (F9 := tranS _ _ _ F7 F8). 
          assert (F10 := b_conS _ _ _ _ (refS s2) (idemS s3)).           
          exact (tranS _ _ _ F9 F10).           
       rewrite F4 in C2. discriminate C2. 
Qed. 


Lemma llex_assoc_case11_aux
  (s1 s2 s3 : S)
  (t1 t2 t3 : T)
  (A1 : (s1 *S s2) !=S ((s1 *S s2) *S s3))
  (C1 : ((s1 *S s2) *S s3) =S s3)
  (A2 : s1 !=S (s1 *S (s2 *S s3)))
  (C2 : (s1 *S (s2 *S s3)) =S (s2 *S s3)) : 
  t3 =T ([|s2 *S s3 | s2 | s3 | t2 | t3|]). 
Proof. unfold llex_p2.
       assert (F1 := assS s1 s2 s3). 
       assert (F2 := tranS _ _ _ F1 C2). apply symS in C1. 
       assert (F3 := tranS _ _ _ C1 F2). apply symS in C1. 
       case_eq(rS s2 (s2 *S s3)); intro A; case_eq(rS (s2 *S s3) s3); intro B.
       - assert (F4 := tranS _ _ _ A B).
         assert (F5 : (s1 *S s2) =S ((s1 *S s2) *S s3)). 
            assert (F6 := b_conS _ _ _ _ (refS s1) A).  apply symS in F1. 
            exact (tranS _ _ _ F6 F1).             
         rewrite F5 in A1. discriminate A1. 
       - assert (F4 : (s1 *S s2) =S ((s1 *S s2) *S s3)).
            assert (F6 := b_conS _ _ _ _ (refS s1) A).  apply symS in F1. 
            exact (tranS _ _ _ F6 F1).             
         rewrite F4 in A1. discriminate A1.            
       - apply refT. 
       - apply symS in F3. rewrite F3 in B. discriminate B. 
Qed. 
         
Lemma llex_assoc_case11
  (s1 s2 s3 : S)
  (t1 t2 t3 : T)
  (A1 : (s1 *S s2) !=S ((s1 *S s2) *S s3))
  (C1 : ((s1 *S s2) *S s3) =S s3)
  (A2 : s1 !=S (s1 *S (s2 *S s3)))
  (C2 : (s1 *S (s2 *S s3)) =S (s2 *S s3)) : 
  ([|(s1 *S s2) *S s3 | s1 *S s2 | s3 | [|s1 *S s2 | s1 | s2 | t1 | t2|] | t3|]) =T
  ([|s1 *S (s2 *S s3) | s1 | s2 *S s3 | t1 | [|s2 *S s3 | s2 | s3 | t2 | t3|]|]). 
unfold llex_p2 at 1 3. rewrite A1, A2, C1, C2. 
   exact (llex_assoc_case11_aux s1 s2 s3 t1 t2 t3 A1 C1 A2 C2).
Qed. 

Lemma llex_assoc_case12
  (s1 s2 s3 : S)
  (t1 t2 t3 : T)
  (A1 : (s1 *S s2) !=S ((s1 *S s2) *S s3))
  (C1 : ((s1 *S s2) *S s3) =S s3)
  (A2 : s1 !=S (s1 *S (s2 *S s3)))
  (C2 : (s1 *S (s2 *S s3)) !=S (s2 *S s3)) : 
  ([|(s1 *S s2) *S s3 | s1 *S s2 | s3 | [|s1 *S s2 | s1 | s2 | t1 | t2|] | t3|]) =T
  ([|s1 *S (s2 *S s3) | s1 | s2 *S s3 | t1 | [|s2 *S s3 | s2 | s3 | t2 | t3|]|]). 
Proof. unfold llex_p2 at 1 3. rewrite A1, A2, C1, C2.
       assert (F1 : (s1 *S (s2 *S s3)) =S (s2 *S s3)). 
          apply symS in C1. 
          assert (F2 := b_conS _ _ _ _ (refS s2) C1). 
          assert (F3 := assS s2 (s1 *S s2) s3). apply symS in F3. 
          assert (F4 := tranS _ _ _ F2 F3).
          assert (F5 : (s2 *S (s1 *S s2)) =S (s1 *S s2)). 
             assert (F6 := commS s2 (s1 *S s2)). 
             assert (F7 := assS s1 s2 s2). 
             assert (F8 := tranS _ _ _ F6 F7).
             assert (F9 := b_conS _ _ _ _ (refS s1) (idemS s2)).              
            exact (tranS _ _ _ F8 F9).
          assert (F6 := b_conS _ _ _ _ F5 (refS s3)). 
          assert (F7 := tranS _ _ _ F4 F6).
          assert (F8 := assS s1 s2 s3). 
          assert (F9 := tranS _ _ _ F7 F8). apply symS. 
          exact F9.            
       rewrite F1 in C2. discriminate C2. 
Qed. 


Lemma llex_assoc_case13_aux
  (s1 s2 s3 : S)
  (t1 t2 t3 : T)
  (A1 : (s1 *S s2) !=S ((s1 *S s2) *S s3))
  (C1 : ((s1 *S s2) *S s3) !=S s3)
  (A2 : s1 =S (s1 *S (s2 *S s3)))
  (C2 : (s1 *S (s2 *S s3)) =S (s2 *S s3)) : 
  argT =T (t1 *T ([|s2 *S s3 | s2 | s3 | t2 | t3|])).
Proof. compute.
       assert (F1 : (s1 *S s2) =S ((s1 *S s2) *S s3)). 
          assert (F2 := b_conS _ _ _ _ A2 (refS s2)). 
          assert (F3 := assS s1 (s2 *S s3) s2). 
          assert (F4 := tranS _ _ _ F2 F3). 
          assert (F5 : ((s2 *S s3) *S s2) =S (s2 *S s3)). 
             assert (F6 := commS s2 s3). 
             assert (F7 := b_conS _ _ _ _ F6 (refS s2)). 
             assert (F8 := assS s3 s2 s2). 
             assert (F9 := tranS _ _ _ F7 F8). 
             assert (F10 := b_conS _ _ _ _ (refS s3) (idemS s2)). 
             assert (F11 := tranS _ _ _ F9 F10).
             assert (F12 := commS s3 s2). 
             exact (tranS _ _ _ F11 F12).              
          assert (F6 := b_conS _ _ _ _ (refS s1) F5). 
          assert (F7 := tranS _ _ _ F4 F6).
          assert (F8 := assS s1 s2 s3). apply symS in F8.
          exact (tranS _ _ _ F7 F8). 
       rewrite F1 in A1. discriminate A1. 
Qed. 

Lemma llex_assoc_case13
  (s1 s2 s3 : S)
  (t1 t2 t3 : T)
  (A1 : (s1 *S s2) !=S ((s1 *S s2) *S s3))
  (C1 : ((s1 *S s2) *S s3) !=S s3)
  (A2 : s1 =S (s1 *S (s2 *S s3)))
  (C2 : (s1 *S (s2 *S s3)) =S (s2 *S s3)) : 
  ([|(s1 *S s2) *S s3 | s1 *S s2 | s3 | [|s1 *S s2 | s1 | s2 | t1 | t2|] | t3|]) =T
  ([|s1 *S (s2 *S s3) | s1 | s2 *S s3 | t1 | [|s2 *S s3 | s2 | s3 | t2 | t3|]|]). 
Proof. unfold llex_p2 at 1 3. rewrite A1, A2, C1, C2.
       exact (llex_assoc_case13_aux s1 s2 s3 t1 t2 t3 A1 C1 A2 C2).              
Qed. 


Lemma llex_assoc_case14
  (s1 s2 s3 : S)
  (t1 t2 t3 : T)
  (A1 : (s1 *S s2) !=S ((s1 *S s2) *S s3))
  (C1 : ((s1 *S s2) *S s3) !=S s3)
  (A2 : s1 =S (s1 *S (s2 *S s3)))
  (C2 : (s1 *S (s2 *S s3)) !=S (s2 *S s3)): 
  ([|(s1 *S s2) *S s3 | s1 *S s2 | s3 | [|s1 *S s2 | s1 | s2 | t1 | t2|] | t3|]) =T
  ([|s1 *S (s2 *S s3) | s1 | s2 *S s3 | t1 | [|s2 *S s3 | s2 | s3 | t2 | t3|]|]). 
Proof. unfold llex_p2 at 1 3. rewrite A1, A2, C1, C2.
       assert (F1 : (s1 *S s2) =S ((s1 *S s2) *S s3)). 
          assert (F2 := b_conS _ _ _ _ A2 (refS s2)).
          assert (F3 := assS s1 (s2 *S s3) s2). 
          assert (F4 := tranS _ _ _ F2 F3). 
          assert (F5 : ((s2 *S s3) *S s2) =S (s2 *S s3)).
             assert (F6 := commS (s2 *S s3) s2). 
             assert (F7 := assS s2 s2 s3). apply symS in F7.
             assert (F8 := tranS _ _ _ F6 F7). 
             assert (F9 := b_conS _ _ _ _ (idemS s2) (refS s3)).
             exact (tranS _ _ _ F8 F9). 
          assert (F6 := b_conS _ _ _ _ (refS s1) F5).
          assert (F7 := tranS _ _ _ F4 F6).
          assert (F8 := assS s1 s2 s3).  apply symS in F8. 
          exact (tranS _ _ _ F7 F8). 
       rewrite F1 in A1. discriminate A1. 
Qed. 

Lemma llex_assoc_case15_aux 
  (s1 s2 s3 : S)
  (t1 t2 t3 : T)
  (A1 : (s1 *S s2) !=S ((s1 *S s2) *S s3))
  (C1 : ((s1 *S s2) *S s3) !=S s3)
  (A2 : s1 !=S (s1 *S (s2 *S s3)))
  (C2 : (s1 *S (s2 *S s3)) =S (s2 *S s3)) : 
  argT =T ([|s2 *S s3 | s2 | s3 | t2 | t3|]).
Proof. compute.
       assert (F1 := assS s1 s2 s3).
       assert (F2 : (s2 *S s3) !=S s3).
          case_eq(rS (s2 *S s3) s3); intro D; auto.
             assert (F3 := tranS _ _ _ C2 D). 
             rewrite (tranS _ _ _ F1 F3) in C1. 
             discriminate C1. 
       rewrite F2.
       assert (F3 : s2 !=S (s2 *S s3)). 
          case_eq(rS s2 (s2 *S s3)); intro D; auto.
             assert (F4 := b_conS _ _ _ _ (refS s1) D).
             apply symS in F1. 
             rewrite (tranS _ _ _ F4 F1) in A1. 
             discriminate A1. 
       rewrite F3.       
       apply refT. 
Qed. 
       
Lemma llex_assoc_case15
  (s1 s2 s3 : S)
  (t1 t2 t3 : T)
  (A1 : (s1 *S s2) !=S ((s1 *S s2) *S s3))
  (C1 : ((s1 *S s2) *S s3) !=S s3)
  (A2 : s1 !=S (s1 *S (s2 *S s3)))
  (C2 : (s1 *S (s2 *S s3)) =S (s2 *S s3)) : 
  ([|(s1 *S s2) *S s3 | s1 *S s2 | s3 | [|s1 *S s2 | s1 | s2 | t1 | t2|] | t3|]) =T
  ([|s1 *S (s2 *S s3) | s1 | s2 *S s3 | t1 | [|s2 *S s3 | s2 | s3 | t2 | t3|]|]). 
Proof. unfold llex_p2 at 1 3. rewrite A1, A2, C1, C2.
   exact (llex_assoc_case15_aux s1 s2 s3 t1 t2 t3 A1 C1 A2 C2).       
Qed. 

Lemma llex_assoc_case16
  (s1 s2 s3 : S)
  (t1 t2 t3 : T)
  (A1 : (s1 *S s2) !=S ((s1 *S s2) *S s3))
  (C1 : ((s1 *S s2) *S s3) !=S s3)
  (A2 : s1 !=S (s1 *S (s2 *S s3)))
  (C2 : (s1 *S (s2 *S s3)) !=S (s2 *S s3)) : 
  ([|(s1 *S s2) *S s3 | s1 *S s2 | s3 | [|s1 *S s2 | s1 | s2 | t1 | t2|] | t3|]) =T
  ([|s1 *S (s2 *S s3) | s1 | s2 *S s3 | t1 | [|s2 *S s3 | s2 | s3 | t2 | t3|]|]). 
Proof. unfold llex_p2 at 1 3. rewrite A1, A2, C1, C2. apply refT. Qed. 

Lemma bop_llex_associative : 
     (bop_selective S rS bS + bop_is_id T rT bT argT) → bop_associative (S * T) (rS <*> rT) (bS llex [rS, argT] bT). 
Proof. 
    intros selS_or_idT [s1 t1] [s2 t2] [s3 t3].
    unfold brel_product, bop_llex. 
    apply bop_and_intro.
       apply assS.
       case_eq(rS (s1 *S s2) ((s1 *S s2) *S s3)); intro A1; 
       case_eq(rS ((s1 *S s2) *S s3) s3); intro C1; 
       case_eq(rS s1 (s1 *S (s2 *S s3))); intro A2; 
       case_eq(rS (s1 *S (s2 *S s3)) (s2 *S s3)); intro C2. 
       - apply llex_assoc_case1; auto. 
       - apply llex_assoc_case2; auto. 
       - apply llex_assoc_case3; auto. (* uses selS_or_idT *)
       - apply llex_assoc_case4; auto. 
       - apply llex_assoc_case5; auto. (* uses selS_or_idT *)
       - apply llex_assoc_case6; auto. 
       - apply llex_assoc_case7; auto. 
       - apply llex_assoc_case8; auto. 
       - apply llex_assoc_case9; auto. 
       - apply llex_assoc_case10; auto. 
       - apply llex_assoc_case11; auto. 
       - apply llex_assoc_case12; auto. 
       - apply llex_assoc_case13; auto. 
       - apply llex_assoc_case14; auto. 
       - apply llex_assoc_case15; auto. 
       - apply llex_assoc_case16; auto. 
Qed. 

End Theory.


Section ACAS.



Section Decide.
 
Variable S T : Type.
Variable wS : S.
Variable wT : T.    
Variable argT : T.  
Variable eqS : brel S.
Variable eqT : brel T.   
Variable bS : binary_op S. 
Variable bT : binary_op T.
Variable eqvS : eqv_proofs S eqS.
Variable eqvT : eqv_proofs T eqT.   

Definition bop_llex_commutative_decide
            (idemS : bop_idempotent S eqS bS) 
            (commS : bop_commutative S eqS bS) (cT_d : bop_commutative_decidable T eqT bT) : 
               bop_commutative_decidable (S * T) (brel_product eqS eqT) (bop_llex argT eqS bS bT) 
:= let refS := A_eqv_reflexive S eqS eqvS in 
   let symS := A_eqv_symmetric S eqS eqvS in 
   let trnS := A_eqv_transitive S eqS eqvS in 
   let refT := A_eqv_reflexive T eqT eqvT in 
    match cT_d with 
   | inl commT     => inl _ (bop_llex_commutative S T eqS eqT bS bT symS trnS argT refT commS commT)
   | inr not_commT => inr _ (bop_llex_not_commutative S T eqS eqT bS bT wS refS symS argT idemS not_commT)
    end.

Definition bop_llex_commutative_holds
            (commS : bop_commutative S eqS bS) (commT : bop_commutative T eqT bT) :
               bop_commutative (S * T) (brel_product eqS eqT) (bop_llex argT eqS bS bT) 
:= let symS := A_eqv_symmetric S eqS eqvS in 
   let trnS := A_eqv_transitive S eqS eqvS in 
   let refT := A_eqv_reflexive T eqT eqvT in 
      bop_llex_commutative S T eqS eqT bS bT symS trnS argT refT commS commT. 


Definition bop_llex_idempotent_decide
            (idemS : bop_idempotent S eqS bS) (idemT_d : bop_idempotent_decidable T eqT bT) :            
  bop_idempotent_decidable (S * T) (brel_product eqS eqT) (bop_llex argT eqS bS bT) 
:= let symS := A_eqv_symmetric S eqS eqvS in
   match idemT_d with 
   | inl idemT     => inl _ (bop_llex_idempotent S T eqS eqT bS bT symS argT idemS idemT)
   | inr not_idemT => inr _ (bop_llex_not_idempotent S T eqS eqT bS bT wS symS argT idemS not_idemT)
   end. 



Definition bop_llex_idempotent_holds
            (idemS : bop_idempotent S eqS bS) (idemT : bop_idempotent T eqT bT) :            
                 bop_idempotent (S * T) (brel_product eqS eqT) (bop_llex argT eqS bS bT) 
:= let symS  := A_eqv_symmetric S eqS eqvS in
      bop_llex_idempotent S T eqS eqT bS bT symS argT idemS idemT. 



Definition bop_llex_selective_decide
           (selS_d : bop_selective_decidable S eqS bS)
           (selT_d : bop_selective_decidable T eqT bT) :           
             bop_selective_decidable (S * T) (brel_product eqS eqT) (bop_llex argT eqS bS bT) 
:= let symS := A_eqv_symmetric S eqS eqvS in 
   let refT := A_eqv_reflexive T eqT eqvT in 
       match selS_d with
       | inl selS => match selT_d with
                     | inl selT     => inl (bop_llex_selective S T eqS eqT bS bT symS argT refT selS selT)
                     | inr not_selT => inr (bop_llex_not_selective_right S T eqS eqT bS bT wS symS argT selS not_selT)
                     end 
       | inr not_selS => inr (bop_llex_not_selective_left S T eqS eqT bS bT wT argT not_selS)
       end. 

Definition bop_llex_exists_id_decide
           (dS : bop_exists_id_decidable S eqS bS)
           (dT : bop_exists_id_decidable T eqT bT) : 
                 bop_exists_id_decidable (S * T) (brel_product eqS eqT) (bop_llex argT eqS bS bT) 
:= let symS := A_eqv_symmetric S eqS eqvS in 
   let refT := A_eqv_reflexive T eqT eqvT in 
   match dS with 
   | inl eS => match dT with 
               | inl eT  => inl _ (bop_llex_exists_id S T eqS eqT bS bT symS argT refT eS eT)
               | inr neT => inr _ (bop_llex_not_exists_id_right S T eqS eqT bS bT symS argT neT)
               end 
   | inr neS   => inr _ (bop_llex_not_exists_id_left S T eqS eqT bS bT argT neS)
   end.


Definition bop_llex_exists_ann_decide 
  (dS : bop_exists_ann_decidable S eqS bS)
  (dT : bop_exists_ann_decidable T eqT bT) : 
    bop_exists_ann_decidable (S * T) (brel_product eqS eqT) (bop_llex argT eqS bS bT)
:= let symS := A_eqv_symmetric S eqS eqvS in 
   let refT := A_eqv_reflexive T eqT eqvT in 
   match dS with 
   | inl eS => match dT with 
               | inl eT  => inl _ (bop_llex_exists_ann S T eqS eqT bS bT symS argT refT eS eT)
               | inr neT => inr _ (bop_llex_not_exists_ann_right S T eqS eqT bS bT symS argT neT)
               end 
   | inr neS   => inr _ (bop_llex_not_exists_ann_left S T eqS eqT bS bT argT neS)
   end.


Definition bop_llex_associative_holds_v1
           (idemS : bop_idempotent S eqS bS)
           (commS : bop_commutative S eqS bS)
           (conS : bop_congruence S eqS bS) 
           (assS : bop_associative S eqS bS)
           (assT : bop_associative T eqT bT)            
           (idT : bop_is_id T eqT bT argT) :
                bop_associative (S * T) (eqS <*> eqT) bS llex [eqS, argT] bT
:= let refS := A_eqv_reflexive S eqS eqvS in 
   let symS := A_eqv_symmetric S eqS eqvS in 
   let trnS := A_eqv_transitive S eqS eqvS in 
   let refT := A_eqv_reflexive T eqT eqvT in
   let symT := A_eqv_symmetric T eqT eqvT in
          bop_llex_associative S T eqS eqT bS bT refS symS trnS
                                   argT refT symT 
                                   conS assS idemS commS
                                   assT (inr idT).  


Definition bop_llex_associative_holds_v2
           (selS  : bop_selective S eqS bS)
           (commS : bop_commutative S eqS bS)
           (conS : bop_congruence S eqS bS) 
           (assS : bop_associative S eqS bS)
           (assT : bop_associative T eqT bT) : 
                bop_associative (S * T) (eqS <*> eqT) bS llex [eqS, argT] bT           
:= let refS := A_eqv_reflexive S eqS eqvS in 
   let symS := A_eqv_symmetric S eqS eqvS in 
   let trnS := A_eqv_transitive S eqS eqvS in 
   let refT := A_eqv_reflexive T eqT eqvT in
   let symT := A_eqv_symmetric T eqT eqvT in
   let idemS := bop_selective_implies_idempotent S eqS bS selS in 
          bop_llex_associative S T eqS eqT bS bT refS symS trnS
                                   argT refT symT 
                                   conS assS idemS commS
                                   assT (inl selS). 


Definition bop_llex_congruence_holds 
           (cng_bS : bop_congruence S eqS bS) (cng_bT : bop_congruence T eqT bT) :
                 bop_congruence (S * T) (eqS <*> eqT) bS llex [eqS, argT] bT
:= let cngS := A_eqv_congruence S eqS eqvS in
   let refT := A_eqv_reflexive T eqT eqvT in     
   let symT := A_eqv_symmetric T eqT eqvT in
      bop_llex_congruence S T eqS eqT bS bT cngS argT refT symT cng_bS cng_bT.

End  Decide.


Section Proofs.

(* NOTE: things marked with ** should really be included in eqv_proofs structure *) 
Variable S T : Type.
Variable wS : S.                             (**)
Variable wT : T.                             (**)
Variable argT : T.  
Variable eqS : brel S.
Variable eqT : brel T.
Variable f : S → S.                         (**)
Variable ntS : brel_not_trivial S eqS f.     (**)
Variable g : T → T.                         (**)
Variable ntT : brel_not_trivial T eqT g.     (**)
Variable bS : binary_op S. 
Variable bT : binary_op T.
Variable eqvS : eqv_proofs S eqS.
Variable eqvT : eqv_proofs T eqT.


Definition sg_llex_proofs
        (pS : sg_proofs S eqS bS)
        (pT : sg_proofs T eqT bT)
        (idemS : bop_idempotent S eqS bS)
        (commS : bop_commutative S eqS bS)
        (P : (bop_selective S eqS bS) + (bop_is_id T eqT bT argT)): 
  sg_proofs (S * T) (brel_product eqS eqT) (bop_llex argT eqS bS bT) :=
let congS := A_sg_congruence _ _ _ pS in     
let congT := A_sg_congruence _ _ _ pT in
let assS := A_sg_associative _ _ _ pS in     
let assT := A_sg_associative _ _ _ pT in   
let refS := A_eqv_reflexive S eqS eqvS in 
let symS := A_eqv_symmetric S eqS eqvS in 
let trnS := A_eqv_transitive S eqS eqvS in 
let refT := A_eqv_reflexive T eqT eqvT in
let symT := A_eqv_symmetric T eqT eqvT in
let trnT := A_eqv_transitive T eqT eqvT in  
{|
  A_sg_associative      := match P with
                           | inl sel => bop_llex_associative_holds_v2 _ _ argT eqS eqT bS bT eqvS eqvT sel commS congS assS assT
                           | inr idP => bop_llex_associative_holds_v1 _ _ argT eqS eqT bS bT eqvS eqvT idemS commS congS assS assT idP 
                           end
; A_sg_congruence       := bop_llex_congruence_holds S T argT eqS eqT bS bT eqvS eqvT congS congT 
; A_sg_commutative_d    := bop_llex_commutative_decide S T wS argT eqS eqT bS bT eqvS eqvT idemS commS (A_sg_commutative_d _ _ _ pT) 
; A_sg_selective_d      := bop_llex_selective_decide S T wS wT argT eqS eqT bS bT eqvS eqvT (A_sg_selective_d _ _ _ pS)  (A_sg_selective_d _ _ _ pT) 
; A_sg_idempotent_d     := bop_llex_idempotent_decide S T wS argT eqS eqT bS bT eqvS idemS (A_sg_idempotent_d _ _ _ pT) 
; A_sg_is_left_d        := inr (bop_llex_not_is_left S T eqS eqT bS bT wS f ntS symS trnS wT argT commS) 
; A_sg_is_right_d       := inr (bop_llex_not_is_right S T eqS eqT bS bT wS f ntS symS trnS wT argT commS) 
; A_sg_left_cancel_d    := inr (bop_llex_not_left_cancellative S T eqS eqT bS bT wS f ntS refS symS trnS wT argT g ntT refT commS P)
; A_sg_right_cancel_d   := inr (bop_llex_not_right_cancellative S T eqS eqT bS bT wS f ntS refS symS trnS wT argT g ntT refT commS P)
; A_sg_left_constant_d  := inr (bop_llex_not_left_constant S T eqS eqT bS bT wS f ntS refS symS trnS wT argT g ntT symT trnT idemS commS P)
; A_sg_right_constant_d := inr (bop_llex_not_right_constant S T eqS eqT bS bT wS f ntS refS symS trnS wT argT g ntT symT trnT idemS commS P)
; A_sg_anti_left_d      := inr (bop_llex_not_anti_left S T eqS eqT bS bT wS f ntS symS trnS wT argT refT symT idemS commS P)
; A_sg_anti_right_d     := inr (bop_llex_not_anti_right S T eqS eqT bS bT wS f ntS symS trnS wT argT refT symT idemS commS P)
|}.


Definition sg_CS_sg_llex_proofs
        (pS : sg_CS_proofs S eqS bS)
        (pT : sg_proofs T eqT bT) :=
let congS := A_sg_CS_congruence _ _ _ pS in     
let congT := A_sg_congruence _ _ _ pT in
let assS := A_sg_CS_associative _ _ _ pS in     
let assT := A_sg_associative _ _ _ pT in   
let refS := A_eqv_reflexive S eqS eqvS in 
let symS := A_eqv_symmetric S eqS eqvS in 
let trnS := A_eqv_transitive S eqS eqvS in 
let refT := A_eqv_reflexive T eqT eqvT in
let symT := A_eqv_symmetric T eqT eqvT in
let trnT := A_eqv_transitive T eqT eqvT in
let selS   := A_sg_CS_selective _ _ _ pS in
let idemS  := bop_selective_implies_idempotent _ _ _ selS in
let commS  := A_sg_CS_commutative _ _ _ pS in
let P      := inl selS in 
{|
  A_sg_associative      := match P with
                           | inl sel => bop_llex_associative_holds_v2 _ _ argT eqS eqT bS bT eqvS eqvT sel commS congS assS assT
                           | inr idP => bop_llex_associative_holds_v1 _ _ argT eqS eqT bS bT eqvS eqvT idemS commS congS assS assT idP 
                           end
; A_sg_congruence       := bop_llex_congruence_holds S T argT eqS eqT bS bT eqvS eqvT congS congT 
; A_sg_commutative_d    := bop_llex_commutative_decide S T wS argT eqS eqT bS bT eqvS eqvT idemS commS (A_sg_commutative_d _ _ _ pT) 
; A_sg_selective_d      := bop_llex_selective_decide S T wS wT argT eqS eqT bS bT eqvS eqvT (inl selS)  (A_sg_selective_d _ _ _ pT) 
; A_sg_idempotent_d     := bop_llex_idempotent_decide S T wS argT eqS eqT bS bT eqvS idemS (A_sg_idempotent_d _ _ _ pT) 
; A_sg_is_left_d        := inr (bop_llex_not_is_left S T eqS eqT bS bT wS f ntS symS trnS wT argT commS) 
; A_sg_is_right_d       := inr (bop_llex_not_is_right S T eqS eqT bS bT wS f ntS symS trnS wT argT commS) 
; A_sg_left_cancel_d    := inr (bop_llex_not_left_cancellative S T eqS eqT bS bT wS f ntS refS symS trnS wT argT g ntT refT commS P)
; A_sg_right_cancel_d   := inr (bop_llex_not_right_cancellative S T eqS eqT bS bT wS f ntS refS symS trnS wT argT g ntT refT commS P)
; A_sg_left_constant_d  := inr (bop_llex_not_left_constant S T eqS eqT bS bT wS f ntS refS symS trnS wT argT g ntT symT trnT idemS commS P)
; A_sg_right_constant_d := inr (bop_llex_not_right_constant S T eqS eqT bS bT wS f ntS refS symS trnS wT argT g ntT symT trnT idemS commS P)
; A_sg_anti_left_d      := inr (bop_llex_not_anti_left S T eqS eqT bS bT wS f ntS symS trnS wT argT refT symT idemS commS P)
; A_sg_anti_right_d     := inr (bop_llex_not_anti_right S T eqS eqT bS bT wS f ntS symS trnS wT argT refT symT idemS commS P)
|}.


Definition sg_CS_sg_C_llex_proofs
        (pS : sg_CS_proofs S eqS bS)
        (pT : sg_C_proofs T eqT bT) :=
let congS := A_sg_CS_congruence _ _ _ pS in     
let congT := A_sg_C_congruence _ _ _ pT in
let assS := A_sg_CS_associative _ _ _ pS in     
let assT := A_sg_C_associative _ _ _ pT in   
let refS := A_eqv_reflexive S eqS eqvS in 
let symS := A_eqv_symmetric S eqS eqvS in 
let trnS := A_eqv_transitive S eqS eqvS in 
let refT := A_eqv_reflexive T eqT eqvT in
let symT := A_eqv_symmetric T eqT eqvT in
let trnT := A_eqv_transitive T eqT eqvT in
let selS   := A_sg_CS_selective _ _ _ pS in
let idemS  := bop_selective_implies_idempotent _ _ _ selS in
let commS  := A_sg_CS_commutative _ _ _ pS in
let P      := inl selS in 
{|
  A_sg_C_associative      := bop_llex_associative_holds_v2 _ _ wT eqS eqT bS bT eqvS eqvT selS commS congS assS assT
; A_sg_C_congruence       := bop_llex_congruence_holds S T wT eqS eqT bS bT eqvS eqvT congS congT 
; A_sg_C_commutative      := bop_llex_commutative S T eqS eqT bS bT symS trnS wT refT commS (A_sg_C_commutative _ _ _ pT)
; A_sg_C_selective_d      := bop_llex_selective_decide S T wS wT wT eqS eqT bS bT eqvS eqvT (inl selS)  (A_sg_C_selective_d _ _ _ pT) 
; A_sg_C_idempotent_d     := bop_llex_idempotent_decide S T wS wT eqS eqT bS bT eqvS idemS (A_sg_C_idempotent_d _ _ _ pT) 
; A_sg_C_cancel_d         := inr (bop_llex_not_left_cancellative S T eqS eqT bS bT wS f ntS refS symS trnS wT wT g ntT refT commS P)
; A_sg_C_constant_d       := inr (bop_llex_not_left_constant S T eqS eqT bS bT wS f ntS refS symS trnS wT wT g ntT symT trnT idemS commS P)
; A_sg_C_anti_left_d      := inr (bop_llex_not_anti_left S T eqS eqT bS bT wS f ntS symS trnS wT wT refT symT idemS commS P)
; A_sg_C_anti_right_d     := inr (bop_llex_not_anti_right S T eqS eqT bS bT wS f ntS symS trnS wT wT refT symT idemS commS P)
|}.




Definition sg_CI_llex_proofs_v1
        (pS : sg_CI_proofs S eqS bS)
        (pT : sg_CI_proofs T eqT bT)
        (idT : bop_is_id T eqT bT argT) : 
             sg_CI_proofs (S * T) (brel_product eqS eqT) (bop_llex argT eqS bS bT) :=
let cng_bS   := A_sg_CI_congruence _ _ _ pS in
let cng_bT   := A_sg_CI_congruence _ _ _ pT in
let not_selS := A_sg_CI_not_selective _ _ _ pS in
let idemS    := A_sg_CI_idempotent _ _ _ pS in
let idemT    := A_sg_CI_idempotent _ _ _ pT in
let commS    := A_sg_CI_commutative _ _ _ pS in
let commT    := A_sg_CI_commutative _ _ _ pT in
let assS     := A_sg_CI_associative _ _ _ pS in
let assT     := A_sg_CI_associative _ _ _ pT in
{|
     A_sg_CI_associative   := bop_llex_associative_holds_v1 S T argT eqS eqT bS bT eqvS eqvT idemS commS cng_bS assS assT idT 
   ; A_sg_CI_congruence    := bop_llex_congruence_holds S T argT eqS eqT bS bT eqvS eqvT cng_bS cng_bT 
   ; A_sg_CI_commutative   := bop_llex_commutative_holds S T argT eqS eqT bS bT eqvS eqvT commS commT 
   ; A_sg_CI_idempotent    := bop_llex_idempotent_holds S T argT eqS eqT bS bT eqvS idemS idemT 
   ; A_sg_CI_not_selective := bop_llex_not_selective_left S T eqS eqT bS bT wT argT not_selS 
|}.


Definition sg_CI_llex_proofs_v2
        (pS : sg_CS_proofs S eqS bS)
        (pT : sg_CI_proofs T eqT bT) : 
             sg_CI_proofs (S * T) (brel_product eqS eqT) (bop_llex argT eqS bS bT) :=
let symS := A_eqv_symmetric S eqS eqvS in 
let cng_bS   := A_sg_CS_congruence _ _ _ pS in
let cng_bT   := A_sg_CI_congruence _ _ _ pT in
let selS     := A_sg_CS_selective _ _ _ pS in
let not_selT := A_sg_CI_not_selective _ _ _ pT in
let idemS    := bop_selective_implies_idempotent S eqS bS selS in 
let idemT    := A_sg_CI_idempotent _ _ _ pT in
let commS    := A_sg_CS_commutative _ _ _ pS in
let commT    := A_sg_CI_commutative _ _ _ pT in
let assS     := A_sg_CS_associative _ _ _ pS in
let assT     := A_sg_CI_associative _ _ _ pT in
{|
     A_sg_CI_associative   := bop_llex_associative_holds_v2 S T argT eqS eqT bS bT eqvS eqvT selS commS cng_bS assS assT 
   ; A_sg_CI_congruence    := bop_llex_congruence_holds S T argT eqS eqT bS bT eqvS eqvT cng_bS cng_bT 
   ; A_sg_CI_commutative   := bop_llex_commutative_holds S T argT eqS eqT bS bT eqvS eqvT commS commT 
   ; A_sg_CI_idempotent    := bop_llex_idempotent_holds S T argT eqS eqT bS bT eqvS idemS idemT 
   ; A_sg_CI_not_selective := bop_llex_not_selective_right S T eqS eqT bS bT wS symS argT selS not_selT
|}.


Definition sg_CS_llex_proofs
        (pS : sg_CS_proofs S eqS bS)
        (pT : sg_CS_proofs T eqT bT) : 
             sg_CS_proofs (S * T) (brel_product eqS eqT) (bop_llex argT eqS bS bT) :=
let symS     := A_eqv_symmetric S eqS eqvS in
let refT     := A_eqv_reflexive T eqT eqvT in   
let cng_bS   := A_sg_CS_congruence _ _ _ pS in
let cng_bT   := A_sg_CS_congruence _ _ _ pT in
let selS     := A_sg_CS_selective _ _ _ pS in
let selT     := A_sg_CS_selective _ _ _ pT in
let commS    := A_sg_CS_commutative _ _ _ pS in
let commT    := A_sg_CS_commutative _ _ _ pT in
let assS     := A_sg_CS_associative _ _ _ pS in
let assT     := A_sg_CS_associative _ _ _ pT in
{|
     A_sg_CS_associative    := bop_llex_associative_holds_v2 S T argT eqS eqT bS bT eqvS eqvT selS commS cng_bS assS assT 
   ; A_sg_CS_congruence     := bop_llex_congruence_holds S T argT eqS eqT bS bT eqvS eqvT cng_bS cng_bT 
   ; A_sg_CS_commutative    := bop_llex_commutative_holds S T argT eqS eqT bS bT eqvS eqvT commS commT 
   ; A_sg_CS_selective      := bop_llex_selective S T eqS eqT bS bT symS argT refT selS selT
|}.



End Proofs.   

Section Combinators.
Definition A_sg_llex
           {S T : Type}
           (A : A_sg_CS S)
           (B : A_sg T) : A_sg (S * T)  :=
let eqvS   := A_sg_CS_eqv _ A in
let eqvT   := A_sg_eqv _ B in
let eqS    := A_eqv_eq _ eqvS in
let eqT    := A_eqv_eq _ eqvT in
let eqvPS  := A_eqv_proofs _ eqvS in
let eqvPT  := A_eqv_proofs _ eqvT in
let bS     := A_sg_CS_bop _ A in
let bT     := A_sg_bop _ B in
let PS     := A_sg_CS_proofs _ A in
let PT     := A_sg_proofs _ B in
let idS_d  := A_sg_CS_exists_id_d _ A in
let idT_d  := A_sg_exists_id_d _ B in
let annS_d := A_sg_CS_exists_ann_d _ A in
let annT_d := A_sg_exists_ann_d _ B in 
(* these bits should move to the A_eqv structures *)
let f      := A_eqv_new _ eqvS in
let g      := A_eqv_new _ eqvT in
let ntS    := A_eqv_not_trivial _ eqvS in
let ntT    := A_eqv_not_trivial _ eqvT in
let wS     := A_eqv_witness _ eqvS in
let wT     := A_eqv_witness _ eqvT in
{| (* note : argT = wT here *) 
  A_sg_eqv          := A_eqv_product S T eqvS eqvT 
; A_sg_bop          := bop_llex wT eqS bS bT 
; A_sg_exists_id_d  := bop_llex_exists_id_decide S T wT eqS eqT bS bT eqvPS eqvPT idS_d idT_d 
; A_sg_exists_ann_d := bop_llex_exists_ann_decide S T wT eqS eqT bS bT eqvPS eqvPT annS_d annT_d 
; A_sg_proofs       := sg_CS_sg_llex_proofs S T wS wT wT eqS eqT f ntS g ntT bS bT eqvPS eqvPT PS PT
; A_sg_ast          := Ast_sg_llex (A_sg_CS_ast S A, A_sg_ast T B)
|}.

End Combinators. 

End ACAS.


Section AMCAS.

Open Scope string_scope.

  Definition A_sg_llex_below_sg_CS {S T : Type} (A : @A_below_sg_CS S) (B : @A_below_sg T) := 
    A_classify_sg (A_sg_llex (A_cast_up_sg_CS A) (A_cast_up_sg B)).  

  Definition A_mcas_sg_llex {S T : Type} (A : @A_sg_mcas S)  (B : @A_sg_mcas T)  : @A_sg_mcas (S * T) :=
    match A, B with
    | A_MCAS_sg A', A_MCAS_sg B'               =>
        match A_cast_below_sg_to_below_sg_CS A' with
        | Some bcs => A_MCAS_sg (A_sg_llex_below_sg_CS bcs B')
        | None     => A_MCAS_sg_Error ("sg_llex : the first argument must be commutative and selective." :: nil)
        end 
    | A_MCAS_sg_Error sl1, A_MCAS_sg_Error sl2 => A_MCAS_sg_Error (sl1 ++ sl2)
    | A_MCAS_sg_Error sl1, _                   => A_MCAS_sg_Error sl1
    | _,  A_MCAS_sg_Error sl2                  => A_MCAS_sg_Error sl2
    end.

End AMCAS.


Section CAS.

Section Certify.

Definition bop_llex_commutative_certify_v1 {S T : Type} (wS : S) 
            (pS : @sg_CI_certificates S) (pT : @sg_certificates T) : @check_commutative (S * T) 
:= match sg_commutative_d pT with 
   | Certify_Commutative => Certify_Commutative
   | Certify_Not_Commutative (t1, t2) => Certify_Not_Commutative ((wS, t1), (wS, t2))
   end.

Definition bop_llex_commutative_certify_v2 {S T : Type} (wS : S) 
            (pS : @sg_CS_certificates S) (pT : @sg_certificates T) : @check_commutative (S * T) 
:= match sg_commutative_d pT with 
   | Certify_Commutative => Certify_Commutative
   | Certify_Not_Commutative (t1, t2) => Certify_Not_Commutative ((wS, t1), (wS, t2))
   end.

Definition bop_llex_commutative_assert_v1 {S T : Type} (wS : S) 
            (pS : @sg_CI_certificates S) (pT : @sg_C_certificates T) : @assert_commutative (S * T) 
:= Assert_Commutative.

Definition bop_llex_commutative_assert_v2 {S T : Type} (wS : S) 
            (pS : @sg_CS_certificates S) (pT : @sg_C_certificates T) : @assert_commutative (S * T) 
:= Assert_Commutative.

    
Definition bop_llex_idempotent_certify {S T : Type} (wS : S) 
            (pS : @sg_CI_certificates S) (pT : @sg_certificates T) : @check_idempotent (S * T) 
:= match sg_idempotent_d pT with 
   | Certify_Idempotent => Certify_Idempotent 
   | Certify_Not_Idempotent t => Certify_Not_Idempotent (wS, t)
   end.

Definition bop_llex_idempotent_assert_v1 {S T : Type} (wS : S) 
            (pS : @sg_CI_certificates S) (pT : @sg_CI_certificates T) : @assert_idempotent (S * T) 
:= Assert_Idempotent.

Definition bop_llex_idempotent_assert_v2 {S T : Type} (wS : S) 
            (pS : @sg_CS_certificates S) (pT : @sg_CI_certificates T) : @assert_idempotent (S * T) 
:= Assert_Idempotent.

Definition bop_llex_selective_certify_v1 {S T : Type} (wS : S) 
            (pS : @sg_CI_certificates S) (pT : @sg_certificates T) : @check_selective (S * T) 
:= match sg_selective_d pT with 
   | Certify_Selective => Certify_Selective
   | Certify_Not_Selective (t1, t2) => Certify_Not_Selective ((wS, t1), (wS, t2))
   end.

Definition bop_llex_selective_assert_v1 {S T : Type} (wS : S) 
            (pS : @sg_CS_certificates S) (pT : @sg_CI_certificates T) : @assert_selective (S * T) 
:= Assert_Selective. 



Definition check_exists_id_llex : ∀ {S T : Type}, 
             (check_exists_id (S := S)) -> (check_exists_id (S := T)) -> (check_exists_id (S := (S * T)))
:= λ {S T} cS cT,  
      match cS, cT with 
      | Certify_Exists_Id s, Certify_Exists_Id t => Certify_Exists_Id  (s, t) 
      | Certify_Not_Exists_Id, _                 => Certify_Not_Exists_Id 
      | _, Certify_Not_Exists_Id                 => Certify_Not_Exists_Id 
      end. 

Definition check_exists_ann_llex : ∀ {S T : Type}, 
             (check_exists_ann (S := S)) -> (check_exists_ann (S := T)) -> (check_exists_ann (S := (S * T)))
:= λ {S T} cS cT,  
      match cS, cT with 
      | Certify_Exists_Ann s, Certify_Exists_Ann t => Certify_Exists_Ann  (s, t) 
      | Certify_Not_Exists_Ann, _                  => Certify_Not_Exists_Ann 
      | _, Certify_Not_Exists_Ann                  => Certify_Not_Exists_Ann 
      end. 

End Certify.



Section Certificates.

Definition sg_llex_certificates {S T : Type}
           (eqS : brel S) 
           (wS : S)
           (f : S -> S)           
           (wT argT : T)
           (g : T -> T)
           (bS : binary_op S)            
           (pS : @sg_certificates S)
           (pT : @sg_certificates T)
           (idemS : @assert_idempotent S)
           (commS : @assert_commutative S)
           (* (P : (@assert_selective S) + (@assert_exists_id T))   <<< this causes "magic" to appear in extracted code (why?) *) 
           : @sg_certificates (S * T) :=
{|
  sg_associative      := Assert_Associative 
; sg_congruence       := Assert_Bop_Congruence 
; sg_commutative_d    := match sg_commutative_d pT with
                         | Certify_Commutative              => Certify_Commutative
                         | Certify_Not_Commutative (t1, t2) => Certify_Not_Commutative ((wS, t1), (wS, t2))
                         end
; sg_selective_d      := match sg_selective_d pS with
                         | Certify_Selective       =>
                           match sg_selective_d pT with
                           | Certify_Selective       =>  Certify_Selective
                           | Certify_Not_Selective (t1, t2) => Certify_Not_Selective ((wS, t1), (wS, t2))                                  
                           end 
                         | Certify_Not_Selective (s1, s2) => Certify_Not_Selective ((s1, wT), (s2, wT))
                         end
; sg_idempotent_d     := match sg_idempotent_d pT with
                         | Certify_Idempotent       => Certify_Idempotent
                         | Certify_Not_Idempotent t => Certify_Not_Idempotent (wS, t)
                         end
; sg_is_left_d        := Certify_Not_Is_Left (witness_llex_not_is_left S T eqS bS wS f wT) 
; sg_is_right_d       := Certify_Not_Is_Right (witness_llex_not_is_right S T eqS bS wS f wT) 
; sg_left_cancel_d    := Certify_Not_Left_Cancellative (witness_llex_not_left_cancellative S T eqS bS wS f wT g)
; sg_right_cancel_d   := Certify_Not_Right_Cancellative (witness_llex_not_right_cancellative S T eqS bS wS f wT g)
; sg_left_constant_d  := Certify_Not_Left_Constant (witness_llex_not_left_constant S T eqS bS wS f wT argT g)
; sg_right_constant_d := Certify_Not_Right_Constant (witness_llex_not_right_constant S T eqS bS wS f wT argT g)
; sg_anti_left_d      := Certify_Not_Anti_Left (witness_llex_not_anti_left S T eqS bS wS f wT argT)
; sg_anti_right_d     := Certify_Not_Anti_Right (witness_llex_not_anti_right S T eqS bS wS f wT argT)
|}.
 


Definition sg_CS_sg_llex_certificates {S T : Type}
           (eqS : brel S) 
           (wS : S)
           (f : S -> S)           
           (wT : T)
           (g : T -> T)
           (bS : binary_op S)            
           (pS : @sg_CS_certificates S)
           (pT : @sg_certificates T)
           : @sg_certificates (S * T) :=
{|
  sg_associative      := Assert_Associative 
; sg_congruence       := Assert_Bop_Congruence 
; sg_commutative_d    := match sg_commutative_d pT with
                         | Certify_Commutative              => Certify_Commutative
                         | Certify_Not_Commutative (t1, t2) => Certify_Not_Commutative ((wS, t1), (wS, t2))
                         end
; sg_selective_d      := match sg_selective_d pT with
                           | Certify_Selective       =>  Certify_Selective
                           | Certify_Not_Selective (t1, t2) => Certify_Not_Selective ((wS, t1), (wS, t2))                                  
                           end 
; sg_idempotent_d     := match sg_idempotent_d pT with
                         | Certify_Idempotent       => Certify_Idempotent
                         | Certify_Not_Idempotent t => Certify_Not_Idempotent (wS, t)
                         end
; sg_is_left_d        := Certify_Not_Is_Left (witness_llex_not_is_left S T eqS bS wS f wT) 
; sg_is_right_d       := Certify_Not_Is_Right (witness_llex_not_is_right S T eqS bS wS f wT) 
; sg_left_cancel_d    := Certify_Not_Left_Cancellative (witness_llex_not_left_cancellative S T eqS bS wS f wT g)
; sg_right_cancel_d   := Certify_Not_Right_Cancellative (witness_llex_not_right_cancellative S T eqS bS wS f wT g)
; sg_left_constant_d  := Certify_Not_Left_Constant (witness_llex_not_left_constant S T eqS bS wS f wT wT g)
; sg_right_constant_d := Certify_Not_Right_Constant (witness_llex_not_right_constant S T eqS bS wS f wT wT g)
; sg_anti_left_d      := Certify_Not_Anti_Left (witness_llex_not_anti_left S T eqS bS wS f wT wT)
; sg_anti_right_d     := Certify_Not_Anti_Right (witness_llex_not_anti_right S T eqS bS wS f wT wT)
|}.

Definition sg_CS_sg_C_llex_certificates {S T : Type}
           (eqS : brel S) 
           (wS : S)
           (f : S -> S)           
           (wT : T)
           (g : T -> T)
           (bS : binary_op S)         
           (pS : @sg_CS_certificates S)
           (pT : @sg_C_certificates T) : @sg_C_certificates (S * T) :=
{|
     sg_C_associative   := Assert_Associative 
   ; sg_C_congruence    := Assert_Bop_Congruence 
   ; sg_C_commutative   := Assert_Commutative
   ; sg_C_idempotent_d  := match sg_C_idempotent_d pT with
                         | Certify_Idempotent       => Certify_Idempotent
                         | Certify_Not_Idempotent t => Certify_Not_Idempotent (wS, t)
                         end
   ; sg_C_selective_d   := match sg_C_selective_d pT with
                           | Certify_Selective       =>  Certify_Selective
                           | Certify_Not_Selective (t1, t2) => Certify_Not_Selective ((wS, t1), (wS, t2))                                  
                           end 
   ; sg_C_cancel_d     := Certify_Not_Left_Cancellative (witness_llex_not_right_cancellative S T eqS bS wS f wT g)
   ; sg_C_constant_d   := Certify_Not_Left_Constant (witness_llex_not_left_constant S T eqS bS wS f wT wT g)
   ; sg_C_anti_left_d  := Certify_Not_Anti_Left (witness_llex_not_anti_left S T eqS bS wS f wT wT)
   ; sg_C_anti_right_d := Certify_Not_Anti_Right (witness_llex_not_anti_right S T eqS bS wS f wT wT)
   
|}.


Definition sg_CI_llex_certs_v1 {S T : Type} (wT : T) 
        (pS : @sg_CI_certificates S)
        (pT : @sg_CI_certificates T)
        (idT : @assert_exists_id T) : @sg_CI_certificates (S * T) :=
{|
     sg_CI_associative   := Assert_Associative 
   ; sg_CI_congruence    := Assert_Bop_Congruence 
   ; sg_CI_commutative   := Assert_Commutative
   ; sg_CI_idempotent    := Assert_Idempotent 
   ; sg_CI_not_selective := match sg_CI_not_selective pS with
                              | Assert_Not_Selective (s1, s2) => Assert_Not_Selective ((s1, wT), (s2, wT))
                            end                                                     
|}.

Definition sg_CI_llex_certs_v2 {S T : Type} (wS : S) 
        (pS : @sg_CS_certificates S)
        (pT : @sg_CI_certificates T) : @sg_CI_certificates (S * T) :=
{|
     sg_CI_associative   := Assert_Associative 
   ; sg_CI_congruence    := Assert_Bop_Congruence 
   ; sg_CI_commutative   := Assert_Commutative
   ; sg_CI_idempotent    := Assert_Idempotent 
   ; sg_CI_not_selective := match sg_CI_not_selective pT with
                              | Assert_Not_Selective (t1, t2) => Assert_Not_Selective ((wS, t1), (wS, t2))
                            end                                                     
|}.


Definition sg_CS_llex_certs {S T : Type} 
        (pS : @sg_CS_certificates S)
        (pT : @sg_CS_certificates T) : @sg_CS_certificates (S * T) :=
{|
     sg_CS_associative   := Assert_Associative 
   ; sg_CS_congruence    := Assert_Bop_Congruence 
   ; sg_CS_commutative   := Assert_Commutative
   ; sg_CS_selective     := Assert_Selective
|}.

End Certificates.

Section Combinators.


Definition sg_llex
           {S T : Type} 
           (A : @sg_CS S)
           (B : @sg T) : @sg (S * T)  :=
let eqvS   := sg_CS_eqv A in
let eqvT   := sg_eqv B in  
let eqS    := eqv_eq eqvS in
let bS     := sg_CS_bop A in
let bT     := sg_bop B in
let PS     := sg_CS_certs A in
let PT     := sg_certs B in
let f      := eqv_new eqvS in
let g      := eqv_new eqvT in
let wS     := eqv_witness eqvS in
let wT     := eqv_witness eqvT in
{| 
  sg_eqv          := eqv_product eqvS eqvT 
; sg_bop          := bop_llex wT eqS bS bT 
; sg_exists_id_d  := check_exists_id_llex (sg_CS_exists_id_d A) (sg_exists_id_d B)
; sg_exists_ann_d := check_exists_ann_llex (sg_CS_exists_ann_d A) (sg_exists_ann_d B)
; sg_certs        := sg_CS_sg_llex_certificates eqS wS f wT g bS PS PT 
; sg_ast          := Ast_sg_llex (sg_CS_ast A, sg_ast B)
|}.
  

End Combinators. 


End CAS.



Section AMCAS.

Open Scope string_scope.

  Definition sg_llex_below_sg_CS {S T : Type} (A : @below_sg_CS S) (B : @below_sg T) := 
    classify_sg (sg_llex (cast_up_sg_CS A) (cast_up_sg B)).  

  Definition mcas_sg_llex {S T : Type} (A : @sg_mcas S)  (B : @sg_mcas T)  : @sg_mcas (S * T) :=
    match A, B with
    | MCAS_sg A', MCAS_sg B'               =>
        match cast_below_sg_to_below_sg_CS A' with
        | Some bcs => MCAS_sg (sg_llex_below_sg_CS bcs B')
        | None     => MCAS_sg_Error ("sg_llex : the first argument must be commutative and selective." :: nil)
        end 
    | MCAS_sg_Error sl1, MCAS_sg_Error sl2 => MCAS_sg_Error (sl1 ++ sl2)
    | MCAS_sg_Error sl1, _                   => MCAS_sg_Error sl1
    | _,  MCAS_sg_Error sl2                  => MCAS_sg_Error sl2
    end.

End AMCAS.


Section Verify.


Section Certify.

Variable S T : Type.
Variable wS : S.    
Variable argT : T.  
Variable eqS : brel S.
Variable eqT : brel T.   
Variable bS : binary_op S. 
Variable bT : binary_op T.
Variable eqvS : eqv_proofs S eqS.
Variable eqvT : eqv_proofs T eqT.   


Lemma correct_check_exists_id_llex 
    (dS : bop_exists_id_decidable S eqS bS)
    (dT : bop_exists_id_decidable T eqT bT): 
         p2c_exists_id_check (S * T) 
            (brel_product eqS eqT)
            (bop_llex argT eqS bS bT)
            (bop_llex_exists_id_decide S T argT eqS eqT bS bT eqvS eqvT dS dT)
         =
         check_exists_id_llex 
           (p2c_exists_id_check S eqS bS dS)
           (p2c_exists_id_check T eqT bT dT). 
Proof. destruct dS as [[s sP] | nS ]; destruct dT as [[t tP] | nT ]; compute; reflexivity. Defined. 


Lemma correct_check_exists_ann_llex 
    (dS : bop_exists_ann_decidable S eqS bS)
    (dT : bop_exists_ann_decidable T eqT bT): 
         p2c_exists_ann_check (S * T) 
            (brel_product eqS eqT)
            (bop_llex argT eqS bS bT)
            (bop_llex_exists_ann_decide S T argT eqS eqT bS bT eqvS eqvT dS dT)
         =
         check_exists_ann_llex 
           (p2c_exists_ann_check S eqS bS dS)
           (p2c_exists_ann_check T eqT bT dT). 
Proof. destruct dS as [[s sP] | nS ]; destruct dT as [[t tP] | nT ]; compute; reflexivity. Defined. 

End Certify.

Section Certificates.

Variable S T : Type.
Variable wS : S.     
Variable wT : T.     
Variable argT : T.  
Variable eqS : brel S.
Variable eqT : brel T.
Variable f : S → S. 
Variable ntS : brel_not_trivial S eqS f.  
Variable g : T → T. 
Variable ntT : brel_not_trivial T eqT g.  
Variable bS : binary_op S. 
Variable bT : binary_op T.
Variable eqvS : eqv_proofs S eqS.
Variable eqvT : eqv_proofs T eqT.

Lemma correct_sg_CS_sg_llex_certificates
  (PS : sg_CS_proofs S eqS bS)
  (PT : sg_proofs T eqT bT) : 
 sg_CS_sg_llex_certificates eqS wS f wT g bS (P2C_sg_CS eqS bS PS) (P2C_sg eqT bT PT) 
 =
 P2C_sg (brel_product eqS eqT) 
        (bop_llex wT eqS bS bT) 
        (sg_CS_sg_llex_proofs S T wS wT wT eqS eqT f ntS g ntT bS bT eqvS eqvT PS PT). 
Proof. unfold P2C_sg, P2C_sg_CS, sg_CS_sg_llex_certificates, sg_CS_sg_llex_proofs; simpl. 
       destruct PS, PT; simpl.
       destruct A_sg_commutative_d as [commT | [[t1 t2] A]]; 
       destruct A_sg_selective_d as [selT | [[t3 t4] [L R]]];          
       destruct A_sg_idempotent_d as [idemT | [t5 D]]; simpl; try reflexivity. 
Qed. 



Lemma correct_sg_CS_sg_C_llex_certificates
  (PS : sg_CS_proofs S eqS bS)
  (PT : sg_C_proofs T eqT bT) : 
 sg_CS_sg_C_llex_certificates eqS wS f wT g bS (P2C_sg_CS eqS bS PS) (P2C_sg_C eqT bT PT) 
 =
 P2C_sg_C (brel_product eqS eqT) 
        (bop_llex wT eqS bS bT) 
        (sg_CS_sg_C_llex_proofs S T wS wT eqS eqT f ntS g ntT bS bT eqvS eqvT PS PT). 
Proof. unfold P2C_sg_C, P2C_sg_CS, sg_CS_sg_C_llex_certificates, sg_CS_sg_C_llex_proofs; simpl. 
       destruct PS, PT; simpl.
       destruct A_sg_C_selective_d as [selT | [[t3 t4] [L R]]];          
         destruct A_sg_C_idempotent_d as [idemT | [t5 D]]; simpl; try reflexivity.
Qed.

Lemma correct_sg_llex_certificates_CS_version 
  (PS : sg_proofs S eqS bS)
  (PT : sg_proofs T eqT bT)       
  (idemS : bop_idempotent S eqS bS) 
  (commS : bop_commutative S eqS bS) 
  (selS  : bop_selective S eqS bS) : 
 sg_llex_certificates eqS wS f wT wT g bS (P2C_sg eqS bS PS) (P2C_sg eqT bT PT) 
                Assert_Idempotent
                Assert_Commutative
                (* (inl Assert_Selective) *) 
 =
 P2C_sg (brel_product eqS eqT) 
        (bop_llex wT eqS bS bT) 
        (sg_llex_proofs S T wS wT wT eqS eqT f ntS g ntT bS bT eqvS eqvT PS PT idemS commS (inl selS)). 
Proof. unfold P2C_sg, sg_llex_certificates, sg_llex_proofs; simpl. 
       destruct PS, PT; simpl.
       destruct A_sg_commutative_d0 as [commT | [[t1 t2] A]]; 
       destruct A_sg_selective_d as [selS' | [[s1 s2] [B C]]];
       destruct A_sg_selective_d0 as [selT | [[t3 t4] [L R]]];          
       destruct A_sg_idempotent_d0 as [idemT | [t5 D]]; simpl; try reflexivity. 
Qed. 

Lemma correct_sg_llex_certificates_CI_version
  (id : T) 
  (PS : sg_proofs S eqS bS)
  (PT : sg_proofs T eqT bT)       
  (idemS : bop_idempotent S eqS bS) 
  (commS : bop_commutative S eqS bS) 
  (idP  :  bop_is_id T eqT bT id) : 
 sg_llex_certificates eqS wS f wT id g bS (P2C_sg eqS bS PS) (P2C_sg eqT bT PT) 
                Assert_Idempotent
                Assert_Commutative
                (* (inr (Assert_Exists_Id id)) *) 
 =
 P2C_sg (brel_product eqS eqT) 
        (bop_llex id eqS bS bT) 
        (sg_llex_proofs S T wS wT id eqS eqT f ntS g ntT bS bT eqvS eqvT PS PT idemS commS (inr idP)). 
Proof. unfold P2C_sg, sg_llex_certificates, sg_llex_proofs; simpl. 
       destruct PS, PT; simpl.
       destruct A_sg_commutative_d0 as [commT | [[t1 t2] A]]; 
       destruct A_sg_selective_d as [selS' | [[s1 s2] [B C]]];
       destruct A_sg_selective_d0 as [selT | [[t3 t4] [L R]]];          
       destruct A_sg_idempotent_d0 as [idemT | [t5 D]]; simpl; try reflexivity. 
Qed. 




Lemma correct_sg_CI_llex_certs_v1
      (pS : sg_CI_proofs S eqS bS)
      (pT : sg_CI_proofs T eqT bT)
      (idT : bop_exists_id T eqT bT) : 
     P2C_sg_CI (brel_product eqS eqT) 
               (bop_llex (projT1 idT) eqS bS bT) 
               (sg_CI_llex_proofs_v1 S T wT (projT1 idT) eqS eqT bS bT eqvS eqvT pS pT (projT2 idT))
     =
     sg_CI_llex_certs_v1 wT (P2C_sg_CI eqS bS pS) (P2C_sg_CI eqT bT pT) (Assert_Exists_Id (projT1 idT)).
Proof. unfold sg_CI_llex_proofs_v1, sg_CI_llex_certs_v1, P2C_sg_CI; simpl.
       destruct pS. simpl. destruct A_sg_CI_not_selective as [[s1 s2] [C D]]. simpl.
       unfold p2c_not_selective_assert. simpl. 
       reflexivity. 
Defined.


Lemma correct_sg_CI_llex_certs_v2 (pS : sg_CS_proofs S eqS bS) (pT : sg_CI_proofs T eqT bT) : 
     P2C_sg_CI (brel_product eqS eqT) 
                (bop_llex argT eqS bS bT) 
                (sg_CI_llex_proofs_v2 S T wS argT eqS eqT bS bT eqvS eqvT pS pT)
     =
     sg_CI_llex_certs_v2 wS (P2C_sg_CS eqS bS pS) (P2C_sg_CI eqT bT pT).

Proof. unfold sg_CI_llex_proofs_v2, sg_CI_llex_certs_v2, P2C_sg_CI, P2C_sg_CS; simpl.
       destruct pS. simpl. destruct A_sg_CI_not_selective as [[s1 s2] [C D]]. simpl.
       unfold p2c_not_selective_assert. simpl. 
       reflexivity. 
Defined.

Lemma correct_sg_CS_certs_llex (pS : sg_CS_proofs S eqS bS) (pT : sg_CS_proofs T eqT bT) : 
    P2C_sg_CS (brel_product eqS eqT) 
              (bop_llex argT eqS bS bT) 
              (sg_CS_llex_proofs S T argT eqS eqT bS bT eqvS eqvT pS pT)
    =
    sg_CS_llex_certs (P2C_sg_CS eqS bS pS) (P2C_sg_CS eqT bT pT). 
 Proof. unfold sg_CS_llex_proofs, sg_CS_llex_certs, P2C_sg_CS; simpl. 
       reflexivity. 
Defined. 

End Certificates.

Section Combinators.

Theorem correct_sg_llex
        (S T : Type) (sgS : A_sg_CS S) (sgT : A_sg T) : 
         sg_llex (A2C_sg_CS sgS) (A2C_sg sgT)
         = 
         A2C_sg (A_sg_llex sgS sgT). 
 Proof. unfold sg_llex, A_sg_llex, A2C_sg, A2C_sg_CS; simpl. 
        rewrite correct_eqv_product.
        rewrite correct_check_exists_id_llex. 
        rewrite correct_check_exists_ann_llex.        
        rewrite <- correct_sg_CS_sg_llex_certificates. 
        reflexivity.
Qed. 

 Theorem correct_sg_llex_below_sg_CS (S T : Type) (A : @A_below_sg_CS S) (B : @A_below_sg T): 
   sg_llex_below_sg_CS (A2C_below_sg_CS A) (A2C_below_sg B)
   =
   A2C_below_sg (A_sg_llex_below_sg_CS A B).
 Proof. unfold A_sg_llex_below_sg_CS, sg_llex_below_sg_CS. 
        rewrite cast_up_sg_CS_A2C_commute.
        rewrite cast_up_sg_A2C_commute.
        rewrite correct_sg_llex.
        rewrite correct_classify_sg.
        reflexivity. 
 Qed.
 
 Theorem correct_mcas_sg_llex (S T : Type) (A : @A_sg_mcas S) (B : @A_sg_mcas T): 
         mcas_sg_llex (A2C_sg_mcas A) (A2C_sg_mcas B) 
         = 
         A2C_sg_mcas  (A_mcas_sg_llex A B).
 Proof. destruct A, B; unfold mcas_sg_llex, A_mcas_sg_llex, A2C_sg_mcas;
          try reflexivity.
        rewrite correct_cast_below_sg_to_below_sg_CS. 
        destruct (A_cast_below_sg_to_below_sg_CS a); simpl. 
        - rewrite correct_sg_llex_below_sg_CS.
          reflexivity. 
        - reflexivity. 
 Qed. 


End Combinators.   
End Verify.
  
(***************************************)
Close Scope brel_product_scope.
Close Scope bop_llex_scope.

