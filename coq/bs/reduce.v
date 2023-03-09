Require Export CAS.coq.common.ast.
Require Export CAS.coq.common.compute.
Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.eqv.reduce.
Require Import CAS.coq.eqv.product. 
Require Import CAS.coq.uop.properties. 
Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures.
Require Import CAS.coq.sg.reduce. 
Require Import CAS.coq.bs.properties.
Require Import CAS.coq.bs.structures.

Section Classical.

  Variable S : Type. 
  Variable add mul : binary_op S.
  Variable r : unary_op S.
  Variable eqS    : brel S.    

  Variable refS   : brel_reflexive S eqS. 
  Variable symS   : brel_symmetric S eqS. 
  Variable trnS : brel_transitive S eqS.
  Variable eqS_cong : brel_congruence S eqS eqS.

  
  Variable add_cong : bop_congruence S eqS add. 
  Variable add_ass  : bop_associative S eqS add.

  Variable mul_cong : bop_congruence S eqS mul. 
  Variable mul_ass  : bop_associative S eqS mul.

  Variable r_cong  : uop_congruence S eqS r. 
  Variable r_idem  : uop_idempotent S eqS r.

  Variable add_left  : bop_left_uop_invariant S eqS (bop_reduce r add) r.  
  Variable add_right : bop_right_uop_invariant S eqS (bop_reduce r add) r.

  Variable mul_left  : bop_left_uop_invariant S eqS (bop_reduce r mul) r.  
  Variable mul_right : bop_right_uop_invariant S eqS (bop_reduce r mul) r. 

  Local Notation "[rtype]" := (reduced_type _ eqS r).
  Local Notation "[req]" := (reduced_equality _ eqS r).
  Local Notation "a =_r b" := ([req] a b = true) (at level 70). 
  Local Notation "[add]" := (reduced_bop _ add r eqS r_idem). 
  Local Notation "[mul]" := (reduced_bop _ mul r eqS r_idem).
  Local Notation "a [+] b" := ([add] a b) (at level 70). 
  Local Notation "a [*] b" := ([mul] a b) (at level 70).

  Lemma r_is_add_reduction : bop_uop_invariant eqS add r.
  Proof. apply r_is_b_reduction; auto. Qed. 

  Lemma r_is_mul_reduction : bop_uop_invariant eqS mul r.
  Proof. apply r_is_b_reduction; auto. Qed. 


  Lemma reduced_bop_left_distributive
    (ld : A_bs_left_distributive eqS add mul) :
      @A_bs_left_distributive [rtype] [req] [add] [mul]. 
  Proof. intros [s1 p1] [s2 p2] [s3 p3]. compute. 
         assert (H1 := mul_right s1 (add s2 s3)).
         unfold bop_reduce in H1.
         assert (H2 := ld s1 s2 s3).
         apply r_cong in H2. 
         assert (H3 := trnS _ _ _ H1 H2).
         assert (H4 := r_is_add_reduction (mul s1 s2) (mul s1 s3)). 
         assert (H5 := trnS _ _ _ H3 H4).
         exact H5. 
  Qed.

  Lemma reduced_bop_not_left_distributive
    (nld : A_bs_not_left_distributive eqS add mul)
    (Q1 : let (s, _) := projT1 nld in is_a_fixed_point S eqS r s) 
    (Q2 : let '(_, (s, _)) := projT1 nld in is_a_fixed_point S eqS r s)
    (Q3 : let '(_, (_, s)) := projT1 nld in is_a_fixed_point S eqS r s) 
    (P : let '(s1, (s2, s3)) := projT1 nld in
         eqS (r (mul s1 (add s2 s3))) (r (add (mul s1 s2) (mul s1 s3))) = false) : 
    @A_bs_not_left_distributive [rtype] [req] [add] [mul]. 
  Proof. destruct nld as [[s1 [s2 s3]] A].
         exists ((existT (fun x => is_a_fixed_point S eqS r x) s1 Q1),
                 ((existT (fun x => is_a_fixed_point S eqS r x) s2 Q2),
                  (existT (fun x => is_a_fixed_point S eqS r x) s3 Q3))).
         compute. compute in Q1, Q2, Q3, P.
         assert (H1 := mul_right s1 (add s2 s3)). compute in H1.
         assert (H2 := r_is_add_reduction (mul s1 s2) (mul s1 s3)).
         apply symS in H1. 
         rewrite <- (eqS_cong _ _ _ _ H1 H2).
         exact P. 
  Defined.


  Lemma reduced_bop_right_distributive
    (rd : A_bs_right_distributive eqS add mul) :
      @A_bs_right_distributive [rtype] [req] [add] [mul]. 
  Proof. intros [s1 p1] [s2 p2] [s3 p3]. compute. 
         assert (H1 := mul_left (add s2 s3) s1).
         unfold bop_reduce in H1.
         assert (H2 := rd s1 s2 s3).
         apply r_cong in H2. 
         assert (H3 := trnS _ _ _ H1 H2).
         assert (H4 := r_is_add_reduction (mul s2 s1) (mul s3 s1)). 
         assert (H5 := trnS _ _ _ H3 H4).
         exact H5. 
  Qed.

  Lemma reduced_bop_not_right_distributive
    (nrd : A_bs_not_right_distributive eqS add mul)
    (Q1 : let (s, _) := projT1 nrd in is_a_fixed_point S eqS r s) 
    (Q2 : let '(_, (s, _)) := projT1 nrd in is_a_fixed_point S eqS r s)
    (Q3 : let '(_, (_, s)) := projT1 nrd in is_a_fixed_point S eqS r s) 
    (P : let '(s1, (s2, s3)) := projT1 nrd in
         eqS (r (mul (add s2 s3) s1)) (r (add (mul s2 s1) (mul s3 s1))) = false) : 
    @A_bs_not_right_distributive [rtype] [req] [add] [mul]. 
  Proof. destruct nrd as [[s1 [s2 s3]] A].
         exists ((existT (fun x => is_a_fixed_point S eqS r x) s1 Q1),
                 ((existT (fun x => is_a_fixed_point S eqS r x) s2 Q2),
                  (existT (fun x => is_a_fixed_point S eqS r x) s3 Q3))).
         compute. compute in Q1, Q2, Q3, P.
         assert (H1 := mul_left (add s2 s3) s1). compute in H1.
         assert (H2 := r_is_add_reduction (mul s2 s1) (mul s3 s1)).
         apply symS in H1. 
         rewrite <- (eqS_cong _ _ _ _ H1 H2).
         exact P. 
  Defined.

  Lemma reduced_bop_left_absorptive 
    (lla : A_bs_left_absorptive eqS add mul) :
    @A_bs_left_absorptive [rtype] [req] [add] [mul]. 
  Proof. intros [s1 p1] [s2 p2]. compute. 
         assert (H1 := add_right s1 (mul s1 s2)).
         unfold bop_reduce in H1.
         assert (H2 := lla s1 s2).
         unfold is_a_fixed_point in p1. apply symS in p1.
         apply r_cong in H2. 
         assert (H3 := trnS _ _ _ p1 H2). apply symS in H1.
         assert (H4 := trnS _ _ _ H3 H1).
         exact H4. 
  Qed.

  Lemma reduced_bop_not_left_absorptive 
    (nlla : A_bs_not_left_absorptive eqS add mul)
    (Q1 : let (s, _) := projT1 nlla in is_a_fixed_point S eqS r s) 
    (Q2 : let (_, t) := projT1 nlla in is_a_fixed_point S eqS r t) 
    (P : let (s, t) := projT1 nlla in eqS s (r (add s (mul s t))) = false) : 
    @A_bs_not_left_absorptive [rtype] [req] [add] [mul]. 
  Proof. destruct nlla as [[s1 s2] A].
         exists ((existT (fun x => is_a_fixed_point S eqS r x) s1 Q1),
                 (existT (fun x => is_a_fixed_point S eqS r x) s2 Q2)).
         compute. compute in Q1, Q2, P.
         assert (H1 := add_right s1 (mul s1 s2)). compute in H1. 
         rewrite (eqS_cong _ _ _ _ (refS s1) H1).
         exact P. 
  Defined.

  Lemma reduced_bop_right_absorptive 
    (lra : A_bs_right_absorptive eqS add mul) :
    @A_bs_right_absorptive [rtype] [req] [add] [mul]. 
  Proof. intros [s1 p1] [s2 p2]. compute. 
         assert (H1 := add_right s1 (mul s2 s1)).
         unfold bop_reduce in H1.
         assert (H2 := lra s1 s2).
         unfold is_a_fixed_point in p1. apply symS in p1.
         apply r_cong in H2. 
         assert (H3 := trnS _ _ _ p1 H2). apply symS in H1.
         assert (H4 := trnS _ _ _ H3 H1).
         exact H4. 
  Qed.

  Lemma reduced_bop_not_right_absorptive 
    (nlra : A_bs_not_right_absorptive eqS add mul)
    (Q1 : let (s, _) := projT1 nlra in is_a_fixed_point S eqS r s) 
    (Q2 : let (_, t) := projT1 nlra in is_a_fixed_point S eqS r t) 
    (P : let (s, t) := projT1 nlra in eqS s (r (add s (mul t s))) = false) : 
    @A_bs_not_right_absorptive [rtype] [req] [add] [mul]. 
  Proof. destruct nlra as [[s1 s2] A].
         exists ((existT (fun x => is_a_fixed_point S eqS r x) s1 Q1),
                 (existT (fun x => is_a_fixed_point S eqS r x) s2 Q2)).
         compute. compute in Q1, Q2, P.
         assert (H1 := add_right s1 (mul s2 s1)). compute in H1. 
         rewrite (eqS_cong _ _ _ _ (refS s1) H1).
         exact P. 
  Defined.

  Lemma reduced_bop_exists_id_ann_equal
    (ia : S)
    (Q : is_a_fixed_point S eqS r ia)
    (P1 : ∀ s, (eqS (r (add ia s)) s = true)
               *
                 (eqS (r (add s ia)) s = true))
    (P2 : ∀ s, (eqS (r (mul ia s)) ia = true)
               *
               (eqS (r (mul s ia)) ia = true)): 
    @A_bs_exists_id_ann_equal [rtype] [req] [add] [mul].
  Proof. compute in Q. 
         exists (inject_into_reduced_type _ eqS r r_idem ia).
         compute. split.
         - intros [s P].
           destruct (P1 s) as [L R]. split.
           + assert (H1 := add_left ia s). compute in H1.
             rewrite (eqS_cong _ _ _ _ H1 (refS s)).
             exact L. 
           + assert (H1 := add_right s ia). compute in H1.
             rewrite (eqS_cong _ _ _ _ H1 (refS s)).
             exact R. 
         - intros [s P].
           destruct (P2 s) as [L R]. split.
           + assert (H1 := mul_left ia s). compute in H1.
             rewrite (eqS_cong _ _ _ _ H1 Q).
             exact L. 
           + assert (H1 := mul_right s ia). compute in H1.
             rewrite (eqS_cong _ _ _ _ H1 Q).
             exact R.
Defined.              

  (*
Definition bops_exists_id_ann_not_equal (S : Type) (r : brel S) (b1 : binary_op S) (b2 : binary_op S)
  := { z : S * S & match z with (i, a) => (bop_is_id S r b1 i) * (bop_is_ann S r b2 a) * (r i a = false) end}.
*) 


  
  
End Classical.

  
Section Classical_vs_Bop_Reduce. 

  Variables (S : Type) 
           (add mul : binary_op S)
           (r : unary_op S)
           (eqS    : brel S)    
           (refS   : brel_reflexive S eqS) 
           (symS   : brel_symmetric S eqS) 
           (trnS   : brel_transitive S eqS)
           (eqS_cong : brel_congruence S eqS eqS)
           (add_cong : bop_congruence S eqS add) 
           (add_ass  : bop_associative S eqS add)
           (mul_cong : bop_congruence S eqS mul) 
           (mul_ass  : bop_associative S eqS mul)
           (r_cong  : uop_congruence S eqS r) 
           (r_idem  : uop_idempotent S eqS r)
           (add_left  : bop_left_uop_invariant S eqS (bop_reduce r add) r)
           (add_right : bop_right_uop_invariant S eqS (bop_reduce r add) r)
           (mul_left  : bop_left_uop_invariant S eqS (bop_reduce r mul) r)
           (mul_right : bop_right_uop_invariant S eqS (bop_reduce r mul) r). 

  Local Notation "[inj]" := (inject_into_reduced_type _ eqS r r_idem).
  Local Notation "[RT]" := (reduced_type _ eqS r).
  Local Notation "[REQ]" := (reduced_equality _ eqS r).
  Local Notation "[add]" := (reduced_bop _ add r eqS r_idem).
  Local Notation "[mul]" := (reduced_bop _ mul r eqS r_idem).
  Local Notation "a == b" := (eqS a b = true) (at level 70). 
  Local Notation "a [+] b" := (add a b) (at level 70). 
  Local Notation "a [*] b" := (mul a b) (at level 70).


Lemma reduced_bop_left_distributive_implies_bop_reduce_left_distributive : 
  @A_bs_left_distributive [RT] [REQ] [add] [mul] 
  ->
  @A_bs_left_distributive S (brel_reduce eqS r) (bop_reduce r add) (bop_reduce r mul).
Proof. assert (add_is_red := r_is_b_reduction _ add r eqS symS trnS add_left add_right).
       assert (mul_is_red := r_is_b_reduction _ mul r eqS symS trnS mul_left mul_right). 
       intros H0 a b c.
       assert (H1 := H0 ([inj] a) ([inj] b) ([inj] c)). compute in H1.
       compute. 
         (* H1 : r (r a [*] r (r b [+] r c)) == r (r (r a [*] r b) [+] r (r a [*] r c))
            ============================
                r (r (a [*] r (b [+] c))) == r (r (r (a [*] b) [+] r (a [*] c)))

          *) 
         assert (H3 : r (r (a [*] r (b [+] c))) == r ((r a) [*] r ((r b) [+] (r c)))).
         {
           assert (H4 := r_idem (a [*] r (b [+] c))).
           assert (H5 := add_is_red b c).
           assert (H6 := mul_cong _ _ _ _ (refS a) H5). apply r_cong in H6.
           assert (H7 := trnS _ _ _ H4 H6).
           assert (H8 := mul_left a (r ((r b) [+] (r c)))). unfold bop_reduce in H8.
           apply symS in H8.
           exact (trnS _ _ _ H7 H8).
         }
         assert (H4 : r (r ((r a) [*] (r b)) [+] r ((r a) [*] (r c))) == r (r (r (a [*] b) [+] r (a [*] c)))). 
         {
           assert (H5 := mul_is_red a b). apply symS in H5. 
           assert (H6 := mul_is_red a c). apply symS in H6.
           assert (H7 := add_cong _ _ _ _ H5 H6).
           apply r_cong in H7.
           assert (H8 := r_idem ((r (a [*] b) [+] r (a [*] c)))). apply symS in H8.
           exact (trnS _ _ _ H7 H8). 
         }
         exact (trnS _ _ _ (trnS _ _ _ H3 H1) H4).
Qed. 


Lemma bop_reduce_distributive_implies_reduced_bop_left_distributive : 
  @A_bs_left_distributive S (brel_reduce eqS r) (bop_reduce r add) (bop_reduce r mul)
  ->
  @A_bs_left_distributive [RT] [REQ] [add] [mul]. 
Proof. assert (add_is_red := r_is_b_reduction _ add r eqS symS trnS add_left add_right).
       assert (mul_is_red := r_is_b_reduction _ mul r eqS symS trnS mul_left mul_right). 
       intros H0 [a P1] [b P2] [c P3].
         assert (H1 := H0 a b c). compute in H1.
         compute. 
         (* H1 : r (r (a [*] r (b [+] c))) == r (r (r (a [*] b) [+] r (a [*] c)))
            ============================
                 r (a [*] r (b [+] c)) == r (r (a [*] b) [+] r (a [*] c))
          *) 
         assert (H3 : r (a [*] r (b [+] c)) == r (r (a [*] r (b [+] c)))).
         {
           apply symS. apply r_idem. 
         }
         assert (H4 : r (r (r (a [*] b) [+] r (a [*] c))) == r (r (a [*] b) [+] r (a [*] c))). 
         {
           apply r_idem. 
         }
         exact (trnS _ _ _ (trnS _ _ _ H3 H1) H4).
Qed. 


Lemma reduced_bop_right_distributive_implies_bop_reduce_right_distributive : 
  @A_bs_right_distributive [RT] [REQ] [add] [mul] 
  ->
  @A_bs_right_distributive S (brel_reduce eqS r) (bop_reduce r add) (bop_reduce r mul).
Proof. assert (add_is_red := r_is_b_reduction _ add r eqS symS trnS add_left add_right).
       assert (mul_is_red := r_is_b_reduction _ mul r eqS symS trnS mul_left mul_right). 
       intros H0 a b c.
       assert (H1 := H0 ([inj] a) ([inj] b) ([inj] c)). compute in H1.
       compute. 
         (* H1 : r (r (r b [+] r c) [*] r a) == r (r (r b [*] r a) [+] r (r c [*] r a)) 
            ============================
                 r (r (r (b [+] c) [*] a)) == r (r (r (b [*] a) [+] r (c [*] a)))
          *) 
         assert (H3 : r (r (r (b [+] c) [*] a)) == r (r (r b [+] r c) [*] r a)). 
         {
           assert (H4 := r_idem (r (b [+] c) [*] a)).
           assert (H5 := add_is_red b c).
           assert (H6 := mul_cong _ _ _ _ H5 (refS a)). apply r_cong in H6.
           assert (H7 := trnS _ _ _ H4 H6).
           assert (H8 := mul_right (r ((r b) [+] (r c))) a). unfold bop_reduce in H8.
           apply symS in H8.
           exact (trnS _ _ _ H7 H8).
         }
         assert (H4 : r (r (r b [*] r a) [+] r (r c [*] r a))  == r (r (r (b [*] a) [+] r (c [*] a)))). 
         {
           assert (H5 := mul_is_red b a). apply symS in H5. 
           assert (H6 := mul_is_red c a). apply symS in H6.
           assert (H7 := add_cong _ _ _ _ H5 H6).
           apply r_cong in H7.
           assert (H8 := r_idem ((r (b [*] a) [+] r (c [*] a)))). apply symS in H8.
           exact (trnS _ _ _ H7 H8). 
         }
         exact (trnS _ _ _ (trnS _ _ _ H3 H1) H4).
Qed.


Lemma bop_reduce_right_distributive_implies_reduced_bop_right_distributive : 
  @A_bs_right_distributive S (brel_reduce eqS r) (bop_reduce r add) (bop_reduce r mul)
  ->
  @A_bs_right_distributive [RT] [REQ] [add] [mul] .
Proof. assert (add_is_red := r_is_b_reduction _ add r eqS symS trnS add_left add_right).
       assert (mul_is_red := r_is_b_reduction _ mul r eqS symS trnS mul_left mul_right). 
       intros H0 [a P1] [b P2] [c P3].
         assert (H1 := H0 a b c). compute in H1.
         compute. 
         (* H1 : r (r (r (b [+] c) [*] a)) == r (r (r (b [*] a) [+] r (c [*] a)))
            ============================
                 r (r (b [+] c) [*] a) == r (r (b [*] a) [+] r (c [*] a) )
          *) 
         assert (H3 : r (r (b [+] c) [*] a) == r (r (r (b [+] c) [*] a))). 
         {
           apply symS. apply r_idem. 
         }
         assert (H4 : r (r (r (b [*] a) [+] r (c [*] a))) == r (r (b [*] a) [+] r (c [*] a) )).
         {
           apply r_idem. 
         }
         exact (trnS _ _ _ (trnS _ _ _ H3 H1) H4).
Qed.


Lemma reduced_bop_left_absorptive_implie_bop_reduce_left_absorptive : 
  @A_bs_left_absorptive [RT] [REQ] [add] [mul] 
  ->
  @A_bs_left_absorptive S (brel_reduce eqS r) (bop_reduce r add) (bop_reduce r mul).
Proof. assert (add_is_red := r_is_b_reduction _ add r eqS symS trnS add_left add_right).
       assert (mul_is_red := r_is_b_reduction _ mul r eqS symS trnS mul_left mul_right).
       intros H0 a b.
       assert (H1 := H0 ([inj] a) ([inj] b)). compute in H1.
       compute.
         (* 
           H1 : r a == r (r a [+] r (r a [*] r b))
           ============================
                r a == r (r (a [+] r (a [*] b)))
          *)
         assert (H2 : r (r a [+] r (r a [*] r b)) == r (r (a [+] r (a [*] b)))). 
         {
           assert (H3 := mul_is_red a b).
           assert (H4 := add_cong _ _ _ _ (refS (r a)) H3).
           apply r_cong in H4. apply symS in H4.
           assert (H5 := add_left a (r (a [*] b))). unfold bop_reduce in H5.
           assert (H6 := trnS _ _ _ H4 H5).
           assert (H7 := r_idem ((a [+] r (a [*] b)))). apply symS in H7. 
           exact (trnS _ _ _ H6 H7). 
         }
         exact (trnS _ _ _ H1 H2).
Qed. 


Lemma bop_reduce_left_absorptive_implies_reduced_bop_left_absorptive : 
  @A_bs_left_absorptive S (brel_reduce eqS r) (bop_reduce r add) (bop_reduce r mul)
  ->
  @A_bs_left_absorptive [RT] [REQ] [add] [mul]. 
Proof. assert (add_is_red := r_is_b_reduction _ add r eqS symS trnS add_left add_right).
       assert (mul_is_red := r_is_b_reduction _ mul r eqS symS trnS mul_left mul_right).
       intros H0 [a P1] [b P2]. 
       assert (H1 := H0 a b). compute in H1.
       compute.
         (* 
           H1 : r a == r (r (a [+] r (a [*] b)))
           ============================
                  a == r (a [+] r (a [*] b))      
                
          *)
         assert (H2 := r_idem (a [+] r (a [*] b))).
         apply symS in P1.
         exact (trnS _ _ _ (trnS _ _ _ P1 H1) H2). 
Qed. 



Lemma reduced_bop_right_absorptive_implie_bop_reduce_right_absorptive : 
  @A_bs_right_absorptive [RT] [REQ] [add] [mul] 
  ->
  @A_bs_right_absorptive S (brel_reduce eqS r) (bop_reduce r add) (bop_reduce r mul).
Proof. assert (add_is_red := r_is_b_reduction _ add r eqS symS trnS add_left add_right).
       assert (mul_is_red := r_is_b_reduction _ mul r eqS symS trnS mul_left mul_right).
       intros H0 a b.
       assert (H1 := H0 ([inj] a) ([inj] b)). compute in H1.
       compute.
         (* 
           H1 : r a == r (r a [+] r (r b [*] r a))
           ============================
                r a == r (r (a [+] r (b [*] a)))
          *)
         assert (H2 : r (r a [+] r (r b [*] r a)) == r (r (a [+] r (b [*] a)))). 
         {
           assert (H3 := mul_is_red b a).
           assert (H4 := add_cong _ _ _ _ (refS (r a)) H3).
           apply r_cong in H4. apply symS in H4.
           assert (H5 := add_left a (r (b [*] a))). unfold bop_reduce in H5.
           assert (H6 := trnS _ _ _ H4 H5).
           assert (H7 := r_idem ((a [+] r (b [*] a)))). apply symS in H7. 
           exact (trnS _ _ _ H6 H7). 
         }
         exact (trnS _ _ _ H1 H2).
Qed. 


Lemma bop_reduce_right_absorptive_implies_reduced_bop_right_absorptive : 
  @A_bs_right_absorptive S (brel_reduce eqS r) (bop_reduce r add) (bop_reduce r mul)
  ->
  @A_bs_right_absorptive [RT] [REQ] [add] [mul]. 
Proof. assert (add_is_red := r_is_b_reduction _ add r eqS symS trnS add_left add_right).
       assert (mul_is_red := r_is_b_reduction _ mul r eqS symS trnS mul_left mul_right).
       intros H0 [a P1] [b P2]. 
       assert (H1 := H0 a b). compute in H1.
       compute.
         (* 
           H1 : r a == r (r (a [+] r (b [*] a)))
           ============================
                  a == r (a [+] r (b [*] a))      
                
          *)
         assert (H2 := r_idem (a [+] r (b [*] a))).
         apply symS in P1.
         exact (trnS _ _ _ (trnS _ _ _ P1 H1) H2). 
Qed.


(* ********************************************************** 
   Bop Reduce 
**********************************************************  *)
Lemma bop_reduce_left_distributive
  (LD : A_bs_left_distributive eqS add mul) : 
    A_bs_left_distributive 
      (brel_reduce eqS r)
      (bop_reduce r add)
      (bop_reduce r mul).
  Proof. apply reduced_bop_left_distributive_implies_bop_reduce_left_distributive.
         apply reduced_bop_left_distributive; auto. 
  Qed. 

  Lemma bop_reduce_right_distributive
  (RD : A_bs_right_distributive eqS add mul) : 
    A_bs_right_distributive 
      (brel_reduce eqS r)
      (bop_reduce r add)
      (bop_reduce r mul).
  Proof. apply reduced_bop_right_distributive_implies_bop_reduce_right_distributive.
         apply reduced_bop_right_distributive; auto. 
  Qed.


  Lemma bop_reduce_left_absorptive
    (LLA : A_bs_left_absorptive eqS add mul): 
    A_bs_left_absorptive 
      (brel_reduce eqS r)
      (bop_reduce r add)
      (bop_reduce r mul).
  Proof. apply reduced_bop_left_absorptive_implie_bop_reduce_left_absorptive. 
         apply reduced_bop_left_absorptive; auto. 
  Qed.


  Lemma bop_reduce_right_absorptive
    (LRA : A_bs_right_absorptive eqS add mul): 
    A_bs_right_absorptive 
      (brel_reduce eqS r)
      (bop_reduce r add)
      (bop_reduce r mul).
  Proof. apply reduced_bop_right_absorptive_implie_bop_reduce_right_absorptive. 
         apply reduced_bop_right_absorptive; auto. 
  Qed.

  
End Classical_vs_Bop_Reduce.

