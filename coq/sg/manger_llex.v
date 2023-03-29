Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import CAS.coq.common.compute.

Require Import CAS.coq.po.properties.
Require Import CAS.coq.po.trivial.

Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.product.

Require Import CAS.coq.eqv.set.
Require Import CAS.coq.eqv.reduce.
Require Import CAS.coq.eqv.minset. 
Require Import CAS.coq.eqv.manger_sets.

Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.reduce.
Require Import CAS.coq.sg.union.
Require Import CAS.coq.sg.minset_union.

Require Import CAS.coq.theory.set.
Require Import CAS.coq.uop.properties. 
Require Import CAS.coq.uop.commutative_composition. 

(* 
  A = type of active component
  P = type of passive component

  See cas/coq/uop/commutative_composition.v 
  for a description of the composition 
  of two reductions, r1 and 2, that 
  commute: 
     r1 (r1 s) = r1 (r2 s). 

  I believe this is the case for our manger reductions: 

   r1 = uop_manger_phase_1

   r2 = uop_manger_phase_2 

   both considered as reductions over 

   b = bop_union (brel_product eqA eqP). 

 *)

Section Theory.
  Variables
    (A P : Type)
    (zeroP : P) (* 0 *)
    (eqA lteA : brel A)
    (eqP : brel P)
    (addP : binary_op P)
    (wA : A)
    (wP : P) 
    (fA : A -> A) 
    (ntA : brel_not_trivial A eqA fA)
    (conA : brel_congruence A eqA eqA) 
    (refA : brel_reflexive A eqA)
    (symA : brel_symmetric A eqA)
    (trnA : brel_transitive A eqA)
    (conP : brel_congruence P eqP eqP)
    (cong_addP : bop_congruence P eqP addP) 
    (refP : brel_reflexive P eqP)
    (symP : brel_symmetric P eqP)
    (trnP : brel_transitive P eqP)
    (conLte : brel_congruence A eqA lteA) 
    (refLte : brel_reflexive A lteA)
    (trnLte : brel_transitive A lteA) 
    (ntot : brel_not_total A lteA)
    (addP_assoc : bop_associative P eqP addP)
    (addP_com : bop_commutative P eqP addP)
    (* idempotence is baked in this addP_cong *)
    (zeropLid : ∀ (p : P), eqP (addP zeroP p) p = true)
    (zeropRid : ∀ (p : P), eqP (addP p zeroP) p = true)
    (addP_gen_idempotent : ∀ x y : P, eqP x y = true → eqP (addP x y) y = true)
    (addP_assoc_cong : ∀ x y z : P, addP x (addP y z) = addP (addP x y) z)
    (addP_com_cong : ∀ x y : P, addP x y = addP y x).
    
  Local Definition eqAP : brel (A * P)
    := brel_product eqA eqP.
  
  Local Definition eqSAP : brel (finite_set (A * P))
    := brel_set eqAP.
  
  Local Definition bSAP : binary_op (finite_set (A * P))
    := bop_union eqAP.

  Lemma conAP : brel_congruence (A * P) eqAP eqAP.
  Proof. apply brel_product_congruence; auto. Qed. 

  Lemma refAP : brel_reflexive (A * P) eqAP.
  Proof. apply brel_product_reflexive; auto. Qed. 

  Lemma symAP : brel_symmetric (A * P) eqAP.
  Proof. apply brel_product_symmetric; auto. Qed. 

  Lemma trnAP : brel_transitive (A * P) eqAP.
  Proof. apply brel_product_transitive; auto. Qed. 

  Lemma conSAP : brel_congruence (finite_set (A * P)) eqSAP eqSAP.
  Proof. apply brel_set_congruence.
         - apply refAP. 
         - apply symAP.
         - apply trnAP.
  Qed. 


  Lemma refSAP : brel_reflexive (finite_set (A * P)) eqSAP.
  Proof. apply brel_set_reflexive. 
         - apply refAP. 
         - apply symAP. 
  Qed. 

  Lemma symSAP : brel_symmetric (finite_set (A * P)) eqSAP.
  Proof. apply brel_set_symmetric. Qed. 

  Lemma trnSAP : brel_transitive (finite_set (A * P)) eqSAP.
  Proof. apply brel_set_transitive. 
         - apply refAP. 
         - apply symAP. 
         - apply trnAP.
  Qed. 

  Lemma bSAP_cong : bop_congruence _ eqSAP bSAP.
  Proof. apply bop_union_congruence.
         - apply refAP. 
         - apply symAP. 
         - apply trnAP.
  Qed. 

  Lemma bSAP_associative : bop_associative _ eqSAP bSAP.
  Proof. apply bop_union_associative.
         - apply refAP. 
         - apply symAP. 
         - apply trnAP.
  Qed. 

  Lemma bSAP_commutative : bop_commutative _ eqSAP bSAP.
   Proof. apply bop_union_commutative.
         - apply refAP. 
         - apply symAP. 
         - apply trnAP.
  Qed. 

  Lemma bSAP_idempotent : bop_idempotent _ eqSAP bSAP.
  Proof. apply bop_union_idempotent.
         - apply refAP. 
         - apply symAP. 
         - apply trnAP.
  Qed.

  (*  Ha! this is interesting. 
      The witness from sg.union.bop_union_not_selective for our type eqAP is (X, Y), where 
      X =  (wA, wP) ::nil 
      Y =  (fA wA, wP) ::nil
      where 
      Variable fA : A -> A. 
      Variable ntA brel_not_trivial A eqA fA.

      Ouch!  This does not work for Lemma nsel_witness_is_a_reduction_witness below. 
    
      That lemma needs 

        uop_manger { (wA, wP), (fA wA, wP)} not in { { (wA, wP) }, { (fA wA, wP)}}

      BUT, wA <> fA wA, so the minset of P2 will choose one of them!!! Ouch! 

    Solution?  It seems we need to come up with a bespoke proof of bSAP_not_selective
    just for this file, so that the witness makes this Lemma true. 
    But the witness has to be simple enough so that 
    we can prove fst_nsel_witness_is_fixed_point and snd_nsel_witness_is_fixed_point. 
    So, we need X and Y such that 

    1) uop_manger X = X
    2) uop_manger Y = Y
    3) uop_manger (X union Y) not in {X, Y}. 

    This can be done.  Here's how. 
    The whole scheme of manger only makes sence when lteA is a partial order. 
    So, let (a1, a2) be the witness for (ntot : brel_not_total A lteA), 
    then 
    X = {
    Y = {(a2, wP)} 
    will work since 
    uop_manger {(a1, wP), (a2, wP)} = {(a1, wP), (a2, wP)}. 

    Here is the bespoke proof of lack of selectivity for union: 
   *)
  Lemma bSAP_not_selective : bop_not_selective _ eqSAP bSAP.
  Proof. destruct ntot as [[a1 a2] [L R]].
         exists ((a1, wP)::nil, (a2, wP)::nil). split.
         - case_eq(eqSAP (bSAP ((a1, wP) :: nil) ((a2, wP) :: nil)) ((a1, wP) :: nil)); intro H1; auto.
           apply brel_set_elim_prop in H1.
           destruct H1 as [H1 H2].
           assert (H3 : in_set eqAP (bSAP ((a1, wP) :: nil) ((a2, wP) :: nil)) (a2, wP) = true).
           {
             apply in_set_bop_union_intro.
             + apply symAP.
             + apply trnAP.
             + right. apply in_set_cons_intro.
               * apply symAP.
               * left. apply refAP. 
           }
           assert (H4 := H1 _ H3).
           apply in_set_cons_elim in H4.
           + destruct H4 as [H4 | H4].
             * apply brel_product_elim in H4. destruct H4 as [H4 H5].
               assert (H6 := refLte a1).
               assert (H7 := conLte _ _ _ _ (refA a1) H4).
               rewrite H7 in H6. rewrite H6 in L.
               exact L. 
             * compute in H4.
               discriminate H4.
           + apply symAP.
           + apply symAP.
           + apply trnAP.
         - case_eq(eqSAP (bSAP ((a1, wP) :: nil) ((a2, wP) :: nil)) ((a2, wP) :: nil)); intro H1; auto.
           apply brel_set_elim_prop in H1.
           destruct H1 as [H1 H2].
           assert (H3 : in_set eqAP (bSAP ((a1, wP) :: nil) ((a2, wP) :: nil)) (a1, wP) = true).
           {
             apply in_set_bop_union_intro.
             + apply symAP.
             + apply trnAP.
             + left. apply in_set_cons_intro.
               * apply symAP.
               * left. apply refAP. 
           }
           assert (H4 := H1 _ H3).
           apply in_set_cons_elim in H4.
           + destruct H4 as [H4 | H4].
             * apply brel_product_elim in H4. destruct H4 as [H4 H5].
               assert (H6 := refLte a1).
               assert (H7 := conLte _ _ _ _ (refA a1) H4).
               rewrite H6 in H7. rewrite H7 in L.
               exact L. 
             * compute in H4.
               discriminate H4.
           + apply symAP.
           + apply symAP.
           + apply trnAP.
  Defined. 

  Local Notation "x =S= y" := (eqSAP x y = true) (at level 70). 
  Local Notation "[P1]" := (uop_manger_phase_1 eqA addP)
    (only parsing).  (* Phase 1 reduction *) 
  Local Notation "[P2]" := (@uop_manger_phase_2 A P lteA)
    (only parsing). (* Phase 2 reduction *)

  (* show [P1] is a reduction *)  
  Lemma P1_cong : uop_congruence _ eqSAP [P1].
  Admitted. (* this should come from eqv/manger_sets.v *) 
  
  Lemma P1_idem : uop_idempotent _ eqSAP [P1].
  Admitted. (* this should come from eqv/manger_sets.v *) 
  
  Lemma P1_left : bop_left_uop_invariant _ eqSAP (bop_reduce [P1] bSAP) [P1].
  Admitted. 
  
  Lemma P1_right : bop_right_uop_invariant _ eqSAP (bop_reduce [P1] bSAP) [P1].
  Admitted.

  (* show [P2] is a reduction. 

     Mukesh: I've modified minset_union so that it is now
     compatible with our Manger definitions. 
     So, now we can get the following results about [P2] 
     from more general results about uop_minset and bop_minset_union. 
  *)  
  Lemma P2_cong : uop_congruence _ eqSAP [P2].
  Proof. unfold uop_manger_phase_2.
         apply uop_minset_congruence_weak.
         - exact refAP.
         - exact symAP.
         - exact trnAP.
         - apply brel_product_congruence; auto.
           + apply brel_trivial_congruence. 
         - apply brel_product_reflexive; auto.
           + apply brel_trivial_reflexive.
         - apply brel_product_transitive; auto.
           + apply brel_trivial_transitive.
  Qed.
  
  Lemma P2_idem : uop_idempotent _ eqSAP [P2].
  Proof. unfold uop_manger_phase_2.
         apply uop_minset_idempotent. 
         - exact refAP.
         - exact symAP.
         - exact trnAP.
         - apply brel_product_congruence; auto.
           + apply brel_trivial_congruence. 
         - apply brel_product_reflexive; auto.
           + apply brel_trivial_reflexive.
  Qed.

  Lemma P2_left : bop_left_uop_invariant _ eqSAP (bop_reduce [P2] bSAP) [P2].
  Proof. apply minset_union_left_uop_invariant.
         - exact refAP.
         - exact symAP.
         - exact trnAP.
         - apply brel_product_congruence; auto.
           + apply brel_trivial_congruence. 
         - apply brel_product_reflexive; auto.
           + apply brel_trivial_reflexive.
         - apply brel_product_transitive; auto.
           + apply brel_trivial_transitive.
  Qed.

  Lemma P2_right : bop_right_uop_invariant _ eqSAP (bop_reduce [P2] bSAP) [P2].
  Proof. apply minset_union_right_uop_invariant.
         - exact refAP.
         - exact symAP.
         - exact trnAP.
         - apply brel_product_congruence; auto.
           + apply brel_trivial_congruence. 
         - apply brel_product_reflexive; auto.
           + apply brel_trivial_reflexive.
         - apply brel_product_transitive; auto.
           + apply brel_trivial_transitive.
  Qed.


  Local Notation "a =S= b" := 
    (brel_set (brel_product eqA eqP) a b = true) (at level 70). 

  (* 
  Lemma list_rewrite_uop_minset : 
    forall (X Y : finite_set (A * P)) a p, 
    (in_set (brel_product eqA eqP) Y (a, p) = true → 
    in_set (brel_product eqA eqP) X (a, p) = true) ->
    (List.filter (λ '(x, _), eqA x a) X) =S= 
    (List.filter (λ '(x, _), eqA x a) Y).
  Proof.
    intros * Ha.
    eapply brel_set_intro_prop;
    try assumption.
    + exact refAP.
    +
      refine(pair _ _).
      ++
        intros a' Hb.
  *)



  (* 
    Now, show that the two reductions commute! 
    **** I hope this is true! *****
    Seems true but difficult.
    
  *)

  Lemma cong_manger_preorder : (brel_congruence (A * P) 
    (brel_product eqA eqP) (manger_pre_order lteA)).
  Proof.
    intros (a, b) (c, d) (u, v) (w, x) Ha Hb.
    cbn. unfold brel_trivial.
    f_equal.
    eapply brel_product_elim in Ha, Hb.
    eapply conLte.
    exact (fst Ha).
    exact (fst Hb).
  Qed.

  Lemma ref_manger_pre_order :
    (brel_reflexive (A * P) (manger_pre_order lteA)).
  Proof.
   intros (a, b).
   cbn.
   rewrite refLte;
   unfold brel_trivial;
   reflexivity.
  Qed.
  


  

  Lemma iterate_minset_inv_2 : 
    forall (X W Y : finite_set (A * P)) au bu,
    find (theory.below (manger_pre_order lteA) (au, bu)) X = None ->
    (∀ t : A * P,
      in_set (brel_product eqA eqP) X t = true -> 
      theory.below (manger_pre_order lteA) (au, bu) t = false) ->
    snd (iterate_minset (manger_pre_order lteA) W ((au, bu) :: Y) X) = 
      (au, bu) :: snd (iterate_minset (manger_pre_order lteA) W Y X).
  Proof.
  Admitted.


    

  


  (* My hunch: this proof will go through only 
  if X is anti-chain. 
  forall ax bx, In (ax, bx) X ->
  (find (theory.below (manger_pre_order lteA) (au, bu)) X)= None. 
  *)
  Lemma matrix_algorithm_addP : 
    forall (X : finite_set (A * P)) a,
    eqP 
    (matrix_algorithms.sum_fn zeroP addP 
      snd (List.filter (λ '(x, _), eqA x a) X))
    (matrix_algorithms.sum_fn zeroP addP snd
      (List.filter (λ '(x, _), eqA x a) 
        (uop_minset (manger_pre_order lteA) X))) = true.
  Proof.
    (* So we minimizing the set X using lteA.
      Sow what if during minimization if there is an element 
      strictly below 'lteA' ?? 'a' will be eliminated??

      What if 'a' ends up in W ?? 
    *)
    induction X as [|(au, bu) X IHx].
    +
      intros ?; cbn;
      rewrite refP;
      reflexivity.
    +
      intros ?; cbn.
      case_eq (eqA au a);
      intros Ha.
      ++
        unfold uop_minset; cbn.
        destruct (find (theory.below (manger_pre_order lteA) (au, bu)) X) 
        as [(ap, bp)|] eqn:Hb.
        +++
          (* Some case and it's unprovable *)
          destruct (iterate_minset (manger_pre_order lteA)
            ((au, bu) :: nil) nil X) as (W, Y) eqn:Hf.
          pose proof find_below_some (A * P) 
            (brel_product eqA eqP) refAP symAP
            (manger_pre_order lteA) X _ _ Hb as (Hd & He).
          (* 
            Notice how au got eliminated, 
            even though it is equal to a. 'a's second 
            component
            
            For this proof to go through, (au, bu) 
            should have gone Y, not in W.
          *)
          pose proof iterate_minset_invariant_0 (A * P)
            (manger_pre_order lteA) X ((au, bu) :: nil)
            nil nil as Hg;
          rewrite Hf in Hg; cbn in Hg;
          eapply eq_sym in Hg.
          (* This case should be impossible *)
          admit.
        +++
          destruct (iterate_minset (manger_pre_order lteA) nil 
          ((au, bu) :: nil) X) as (W, Y) eqn:Hf.
          pose proof find_below_none (A * P) 
          (brel_product eqA eqP) refAP symAP
          (manger_pre_order lteA)
          cong_manger_preorder X _ Hb as Hc.
          specialize (IHx a).
          unfold uop_minset in IHx.
          destruct (iterate_minset (manger_pre_order lteA) nil nil X)
          as (W1, Y1) eqn:Hd.
          (* using Hc and Hf, can I infer 

          snd 
            (iterate_minset (manger_pre_order lteA) 
            nil ((au, bu) :: nil) X)  =
          (au, bu) :: 
            snd (iterate_minset (manger_pre_order lteA) nil nil X) ?? 
          *)
          assert (He : snd (iterate_minset (manger_pre_order lteA) 
            nil ((au, bu) :: nil) X)  =
            (au, bu) :: 
            snd (iterate_minset (manger_pre_order lteA) nil nil X)).
          eapply iterate_minset_inv_2; 
          try assumption.
          rewrite Hd, Hf in He;
          cbn in He; rewrite He;
          cbn; rewrite Ha;
          cbn.
          eapply cong_addP;
          [eapply refP| exact IHx].
      ++
        (* Trivial case *)
        unfold uop_minset.
        destruct (iterate_minset (manger_pre_order lteA) nil nil ((au, bu) :: X))
        as (W, Y) eqn:Hb.
        cbn in Hb.
        destruct (find (theory.below (manger_pre_order lteA) (au, bu)) X)
        eqn:Hc.
        *
          pose proof iterate_minset_invariant_0 (A * P)
            (manger_pre_order lteA) X ((au, bu) :: nil)
            nil nil as Hg;
          rewrite Hb in Hg; cbn in Hg;
          eapply eq_sym in Hg.
          specialize (IHx a).
          unfold uop_minset in IHx.
          destruct (iterate_minset (manger_pre_order lteA) nil nil X)
          as (W1, Y1) eqn:Hd.
          cbn in Hg; rewrite Hg in IHx.
          exact IHx.
        *
          pose proof find_below_none (A * P) 
          (brel_product eqA eqP) refAP symAP
          (manger_pre_order lteA)
          cong_manger_preorder X _ Hc as Hd.
          specialize (IHx a).
          unfold uop_minset in IHx.
          destruct (iterate_minset (manger_pre_order lteA) nil nil X)
          as (W1, Y1) eqn:He.
          (* using Hc and Hf, can I infer 

          snd 
            (iterate_minset (manger_pre_order lteA) 
            nil ((au, bu) :: nil) X)  =
          (au, bu) :: 
            snd (iterate_minset (manger_pre_order lteA) nil nil X) ?? 
          *)
          assert (Hf : snd (iterate_minset (manger_pre_order lteA) 
            nil ((au, bu) :: nil) X)  =
            (au, bu) :: 
            snd (iterate_minset (manger_pre_order lteA) nil nil X)).
          eapply iterate_minset_inv_2; 
          try assumption.
          rewrite Hb, He in Hf;
          cbn in Hf; rewrite Hf;
          cbn; rewrite Ha;
          exact IHx.
  Admitted.



  Lemma P1_P2_commute : ∀ X, ([P2] ([P1] X)) =S= ([P1] ([P2] X)).
  Proof.
    intros ?.
    eapply brel_set_intro_prop.
    + exact refAP.
    +
      refine(pair _ _).
      ++
        intros (a, p) Ha.
        eapply in_set_uop_manger_phase_2_elim in Ha;
        try assumption.
        destruct Ha as (Hal & Har).
        (* from Hal we know that 
        *)
        eapply in_set_uop_manger_phase_1_elim 
        with (zeroP := zeroP) in Hal;
        try assumption.
        destruct Hal as ((qt & Hall) & Halr).
        (*  from Halr we know that sum of 
        all 'a's is equal to p *)
        (* now apply intro rule in the goal *)
        eapply in_set_uop_manger_phase_1_intro with 
        (zeroP := zeroP);
        try assumption.
        (* What should be q ?? 
        What is uop_manger_phase_2 is doing? *)
        eexists.
        eapply in_set_uop_manger_phase_2_intro;
        try assumption.
        exact Hall.
        intros * Hb.
        eapply Har.
        eapply in_set_uop_manger_phase_1_intro 
        with (zeroP := zeroP); try assumption.
        exists q; exact Hb.
        instantiate (1 :=
        (matrix_algorithms.sum_fn zeroP addP snd 
          (List.filter (λ '(x, _), eqA x b) X)));
        eapply refP.
        unfold uop_manger_phase_2;
        rewrite <-list_filter_lib_filter_same in 
        Halr.
        (* from Har, I can infer below *)
        assert (Hc : ∀ (b : A) (q : P),
          in_set (brel_product eqA eqP) X (b, q) = true → 
          theory.below lteA a b = false).
        intros * Ha. eapply Har.
        eapply in_set_uop_manger_phase_1_intro
        with (zeroP := zeroP); try assumption.
        exists q; exact Ha.
        instantiate (1 :=
        (matrix_algorithms.sum_fn zeroP addP snd 
          (List.filter (λ '(x, _), eqA x b) X)));
        eapply refP.
        (* think! *)
        (* 
          It is only provable when we have 
          (List.filter (λ '(x, _), eqA x a) X)) =S=
          (List.filter (λ '(x, _), eqA x a) 
            (uop_minset (manger_pre_order lteA) X)))

        *)
        (*
          I know from Hc can I infer that 
          'a' is a minimal element? 
          min(<=, X) := {x in X | for all y in X, not (y < x)}. 
        *)
        (* 
        We don't need this. 
        pose proof in_minset_intro (A * P)
          (brel_product eqA eqP) refAP
          symAP (manger_pre_order lteA)
          cong_manger_preorder
          ref_manger_pre_order X (a, p) as Hd.
        *)
        (* manger_pre_order lteA is just lteA because 
          second component is trivial (true) *)
        assert (He : ∀ t : A * P,
          in_set (brel_product eqA eqP) X t = true → 
          theory.below (manger_pre_order lteA) (a, p) t = false).
        intros (c, d) He.
        specialize (Hc c d He).
        eapply theory.below_false_elim in Hc.
        eapply theory.below_false_intro.
        destruct Hc as [Hc | Hc].
        left; cbn; rewrite Hc; reflexivity.
        right; cbn; rewrite Hc; reflexivity.
        eapply trnP.
        exact Halr.
        eapply matrix_algorithm_addP.
      ++
        intros (a, p) Ha.
        eapply in_set_uop_manger_phase_1_elim 
        with (zeroP := zeroP) in Ha;
        try assumption.
        destruct Ha as ((qt & Hal) & Har).
        eapply in_set_uop_manger_phase_2_elim in Hal;
        try assumption.
        destruct Hal as (Hall & Halr).
        eapply in_set_uop_manger_phase_2_intro;
        try assumption.
        eapply in_set_uop_manger_phase_1_intro
        with (zeroP := zeroP); try assumption.
        exists qt; exact Hall.

        unfold uop_manger_phase_2 in Har.
        pose proof in_minset_implies_in_set
         (A * P) (brel_product eqA eqP)
        symAP (manger_pre_order lteA) as Hb.
        rewrite <-list_filter_lib_filter_same  in Har.
        eapply trnP.
        exact Har.
        apply symP.
        eapply matrix_algorithm_addP.
        intros * Hb.
        eapply in_set_uop_manger_phase_1_elim 
        with (zeroP := zeroP) in Hb; try assumption.
        destruct Hb as ((qp & Hbl) & Hbr).
        eapply Halr; exact Hbl.
    Qed.

    

  (* Given the above lemmas, we can now use the results of 
     cas/coq/uop/commutative_composition.v to 
     prove everything we need to build a 
     commutative and idempotent semigroup. 
     (Note : ignoring existence of id and ann for now ...) 
   *)

  Definition uop_manger := uop_compose [P2] [P1].
  Definition eq_manger :=  brel_reduce eqSAP uop_manger. 
  Definition bop_manger := bop_reduce uop_manger bSAP.

  (* to show non-selectivity of the reduced semigroup we need to prove some things about the witness for 
     non-selectivity of bSAP. 
  *) 
  Lemma fst_nsel_witness_is_fixed_point : let (s, _) := projT1 bSAP_not_selective in uop_manger s =S= s.
  Proof. unfold bSAP_not_selective.
         destruct ntot as [[a1 a2] [L R]]. simpl.
         compute. 
         rewrite refA. rewrite refP. rewrite refA. rewrite refP. reflexivity.
  Qed. 

  Lemma snd_nsel_witness_is_fixed_point : let (_, s) := projT1 bSAP_not_selective in uop_manger s =S= s.
  Proof. unfold bSAP_not_selective.
         destruct ntot as [[a1 a2] [L R]]. simpl.
         compute. 
         rewrite refA. rewrite refP. rewrite refA. rewrite refP. reflexivity.
  Qed. 

  (* Mukesh : this should be true now, but I've run out of steam ... *) 
  Lemma nsel_witness_is_a_reduction_witness : 
      let (s, t) := projT1 bSAP_not_selective in
      (eqSAP (bop_manger s t) s = false)
      *
      (eqSAP (bop_manger s t) t = false).
  Proof. unfold bSAP_not_selective.
         destruct ntot as [[a1 a2] [L R]]. simpl.
         split.
         - admit.
         - admit. 
  Admitted.          


  Lemma uop_manger_is_reduction : bop_uop_invariant eqSAP bSAP uop_manger.
  Proof. apply uop_compose_is_reduction.
         - exact symSAP. 
         - exact trnSAP. 
         - exact P1_cong. 
         - exact P1_left. 
         - exact P1_right. 
         - exact P2_cong. 
         - exact P2_left. 
         - exact P2_right. 
         - exact P1_P2_commute. 
  Qed. 

  Lemma bop_manger_congruence :
    bop_congruence _ eq_manger bop_manger.
  Proof. apply uop_compose_bop_congruence. 
         - exact symSAP. 
         - exact trnSAP.
         - exact bSAP_cong. 
         - exact P1_cong.
         - exact P1_left. 
         - exact P1_right. 
         - exact P2_cong.
         - exact P2_left. 
         - exact P2_right. 
         - exact P1_P2_commute. 
  Qed. 

  Lemma bop_manger_associative :
    bop_associative _ eq_manger bop_manger.
  Proof. apply uop_compose_bop_associative.
         - exact refSAP.          
         - exact symSAP. 
         - exact trnSAP.
         - exact bSAP_cong. 
         - exact bSAP_associative.           
         - exact P1_cong.
         - exact P1_idem. 
         - exact P1_left. 
         - exact P1_right. 
         - exact P2_cong.
         - exact P2_idem. 
         - exact P2_left. 
         - exact P2_right. 
         - exact P1_P2_commute. 
  Qed. 

    Lemma bop_manger_commutative :
    bop_commutative _ eq_manger bop_manger.
  Proof. apply uop_compose_bop_commutative.
         - exact refSAP.          
         - exact symSAP. 
         - exact trnSAP.
         - exact bSAP_cong. 
         - exact P1_cong.
         - exact P1_idem. 
         - exact P1_left. 
         - exact P1_right. 
         - exact P2_cong.
         - exact P2_idem. 
         - exact P2_left. 
         - exact P2_right. 
         - exact P1_P2_commute.
         - exact bSAP_commutative. 
  Qed. 
 
  Lemma bop_manger_idempotent :
    bop_idempotent _ eq_manger bop_manger.
  Proof. apply uop_compose_bop_idempotent.
         - exact refSAP.          
         - exact symSAP. 
         - exact trnSAP.
         - exact bSAP_cong. 
         - exact P1_cong.
         - exact P1_idem. 
         - exact P1_left. 
         - exact P1_right. 
         - exact P2_cong.
         - exact P2_idem. 
         - exact P2_left. 
         - exact P2_right. 
         - exact P1_P2_commute.
         - exact bSAP_idempotent. 
  Qed. 

  Lemma bop_manger_not_selective :
    bop_not_selective _ eq_manger bop_manger.
  Proof. exact (uop_compose_bop_not_selective _
                  bSAP [P1] [P2] eqSAP symSAP trnSAP bSAP_cong
                  P1_cong P1_idem P2_cong P2_idem P1_P2_commute
                  bSAP_not_selective
                  fst_nsel_witness_is_fixed_point
                  snd_nsel_witness_is_fixed_point
                  nsel_witness_is_a_reduction_witness).
  Qed. 

End Theory.   

