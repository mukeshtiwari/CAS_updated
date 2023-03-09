Require Import Coq.Bool.Bool.

Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.

Require Import CAS.coq.theory.set. 

Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.eqv.theory.
Require Import CAS.coq.eqv.set.
Require Import CAS.coq.eqv.sum. 
Require Import CAS.coq.eqv.add_constant.

Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures.
Require Import CAS.coq.sg.theory.
Require Import CAS.coq.sg.and.
Require Import CAS.coq.sg.add_id.
Require Import CAS.coq.sg.cast_up.
Require Import CAS.coq.sg.classify. 

Section Computation.

Definition bop_intersect {S : Type} (eq : brel S) : binary_op (finite_set S) 
  := λ X,  uop_filter (in_set eq X).

Definition bop_intersect_with_id {S : Type} (c : cas_constant) (eq : brel S) : binary_op (with_constant (finite_set S))
  := bop_add_id (bop_intersect eq) c. 

  
End Computation.   

Section Theory.

  Variable S: Type.
  Variable c : cas_constant.  
  Variable eq : brel S.
  Variable wS  : S. 
  Variable f : S -> S.
  Variable ntS : brel_not_trivial S eq f. 
  Variable refS : brel_reflexive S eq.
  Variable symS : brel_symmetric S eq.
  Variable tranS : brel_transitive S eq.

Lemma in_set_bop_intersect_intro : ∀ (X Y : finite_set S) (a : S),
       (in_set eq X a = true) * (in_set eq Y a = true) → in_set eq (bop_intersect eq X Y) a = true. 
Proof. intros X Y a H. unfold bop_intersect. 
       apply in_set_filter_intro; auto.
       apply in_set_bProp_congruence; auto.
Qed. 


Lemma in_set_bop_intersect_elim : ∀ (X Y : finite_set S) (a : S),
       in_set eq (bop_intersect eq X Y) a = true  → (in_set eq X a = true) * (in_set eq Y a = true). 
Proof. intros X Y a H. 
       unfold bop_intersect in H. 
       apply in_set_filter_elim in H. assumption.
       apply in_set_bProp_congruence; auto. 
Qed. 




Lemma bop_intersect_congruence : bop_congruence (finite_set S) (brel_set eq) (bop_intersect eq).
Proof. unfold bop_intersect. unfold bop_congruence. 
       assert (fact := brel_set_congruence S eq refS symS tranS). 
       intros s1 s2 t1 t2 H1 H2. 
       unfold brel_congruence in fact. 
       apply brel_set_intro_prop; auto. 
       split. 
          intros a J. 
          apply in_set_filter_intro; auto.
          apply in_set_bProp_congruence; auto.
          apply in_set_filter_elim in J. destruct J as [JL JR].
          assert(fact1 := in_set_left_congruence S eq symS tranS a _ _ H1).
          assert(fact2 := in_set_left_congruence S eq symS tranS a _ _ H2).
          rewrite JL in fact1. rewrite JR in fact2. 
          rewrite <- fact1, fact2. auto. 
          apply in_set_bProp_congruence; auto. 
          intros a J. 
          apply in_set_filter_intro; auto.
          apply in_set_bProp_congruence; auto. 
          apply in_set_filter_elim in J. destruct J as [JL JR]. 
          assert(fact1 := in_set_left_congruence S eq symS tranS a _ _ H1).
          assert(fact2 := in_set_left_congruence S eq symS tranS a _ _ H2).
          rewrite JL in fact1. rewrite JR in fact2. 
          rewrite <- fact1, fact2. auto. 
       apply in_set_bProp_congruence; auto. 
Qed. 

(* simplify?  theorems about composition? *) 
Lemma bop_intersect_associative : bop_associative (finite_set S) (brel_set eq) (bop_intersect eq).
Proof. intros s t u. apply brel_set_intro_prop; auto. 
       split. 
          intros a H.
          assert (J : bProp_congruence S eq (in_set eq s)). apply in_set_bProp_congruence; auto.
          assert (K : bProp_congruence S eq (in_set eq t)). apply in_set_bProp_congruence; auto.          
         apply in_set_filter_intro; auto. 
         apply in_set_filter_elim in H; auto.  
         destruct H as [HL HR]. apply in_set_filter_elim in HL; auto. 
         destruct HL as [HLL HLR]. 
         split;auto.            
            apply in_set_filter_intro; auto. 
            apply in_set_bProp_congruence; auto.

         intros a H. 
         apply in_set_filter_intro; auto. 
         apply in_set_bProp_congruence; auto.
         assert (J : bProp_congruence S eq (in_set eq s)). apply in_set_bProp_congruence; auto.
         assert (K : bProp_congruence S eq (in_set eq t)). apply in_set_bProp_congruence; auto.          
         apply in_set_filter_elim in H; auto. 
         destruct H as [HL HR]. apply in_set_filter_elim in HR; auto. 
         destruct HR as [HRL HRR]. 
         split; auto. 
            apply in_set_filter_intro; auto. 
Qed. 

Lemma bop_intersect_idempotent : bop_idempotent (finite_set S) (brel_set eq) (bop_intersect eq).
Proof. intro s. destruct s. 
          compute. reflexivity.
          unfold brel_set. unfold brel_and_sym. apply bop_and_intro. 
             apply brel_subset_intro; auto. 
             intros x H. 
             apply in_set_filter_elim in H.
             destruct H as [HL HR]. assumption. 
             apply in_set_bProp_congruence; auto.
             apply brel_subset_intro; auto. 
             intros x H. 
             apply in_set_filter_intro; auto. 
             apply in_set_bProp_congruence; auto.
Qed. 

Lemma uop_filter_false_is_nil : ∀ (X : finite_set S), filter (λ _ : S, false) X = nil.
Proof. unfold uop_filter. induction X; compute; auto. Qed. 

Lemma bop_intersect_commutative : bop_commutative(finite_set S) (brel_set eq) (bop_intersect eq).
Proof. intros s t. destruct s; destruct t. 
          compute; auto.
          unfold bop_intersect.  unfold in_set at 1. 
          simpl. rewrite uop_filter_false_is_nil. compute. reflexivity.
          unfold bop_intersect.  unfold in_set at 2.           
          simpl. rewrite uop_filter_false_is_nil. compute. reflexivity.
          apply brel_set_intro_prop; auto. 
          split; intros x H. 
             apply in_set_filter_elim in H. destruct H as [HL HR]. 
             apply in_set_filter_intro; auto.
             apply in_set_bProp_congruence; auto.
             apply in_set_bProp_congruence; auto.             

             apply in_set_filter_elim in H. destruct H as [HL HR]. 
             apply in_set_filter_intro; auto.
             apply in_set_bProp_congruence; auto.
             apply in_set_bProp_congruence; auto.             
Qed. 

Lemma bop_intersect_not_selective : bop_not_selective (finite_set S) (brel_set eq) (bop_intersect eq).
Proof. exists ((wS ::nil), ((f wS) :: nil)).
       destruct (ntS wS) as [L R].
       split; unfold bop_intersect; unfold uop_filter; unfold filter; unfold in_set; rewrite R; compute; auto. 
Defined. 

Lemma bop_intersect_nil :  ∀ (X : finite_set S), brel_set eq (bop_intersect eq nil X) nil = true. 
Proof. intro X. 
       apply brel_set_intro. split. 
       apply brel_subset_intro; auto. 
       intros a H. apply in_set_bop_intersect_elim in H; auto. 
       destruct H as [HL  HR]. 
       assumption. 
       apply brel_subset_intro; auto. 
       intros a H. compute in H. discriminate. 
Defined. 


Lemma bop_intersect_nil_is_ann : bop_is_ann (finite_set S) (brel_set eq) (bop_intersect eq) nil. 
Proof. unfold bop_is_ann. 
       intro s. 
       assert (fact1 : brel_set eq (bop_intersect eq nil s) nil = true). 
          apply bop_intersect_nil; auto. 
       assert (fact2 : brel_set eq (bop_intersect eq s nil) (bop_intersect eq nil s) = true). 
          apply bop_intersect_commutative; auto. 
       assert (fact3 : brel_set eq (bop_intersect eq s nil) nil = true). 
          apply (brel_set_transitive S eq refS symS tranS _ _ _ fact2 fact1). 
       rewrite fact1, fact3. auto. 
Defined. 


Lemma bop_intersect_exists_ann : bop_exists_ann (finite_set S) (brel_set eq) (bop_intersect eq).
Proof. exists nil. apply bop_intersect_nil_is_ann. Defined.

Lemma bop_intersect_with_id_exists_ann : bop_exists_ann (with_constant (finite_set S))
                                                   (brel_sum brel_constant (brel_set eq))
                                                   (bop_intersect_with_id c eq).
Proof. apply bop_add_id_exists_ann; auto.
       apply brel_set_reflexive; auto. 
       apply bop_intersect_exists_ann.
Defined. 

Lemma bop_intersect_with_id_exists_id : bop_exists_id (with_constant (finite_set S))
                                                     (brel_sum brel_constant (brel_set eq))
                                                     (bop_intersect_with_id c eq).
Proof. apply bop_add_id_exists_id. apply brel_set_reflexive; auto. Defined. 




(*****)

Lemma bop_intersect_enum_is_id (enum : carrier_is_finite S eq) : 
  bop_is_id (finite_set S) (brel_set eq) (bop_intersect eq) ((projT1 enum) tt).
Proof. destruct enum as [fS Pf]. simpl.
       unfold bop_is_id. intro X. split.
       apply brel_set_intro_prop; auto.
       split.
       intros s H. apply in_set_bop_intersect_elim in H.
       destruct H as [L R]; auto. 
       intros s H.  apply in_set_bop_intersect_intro.
       split; auto.

       apply brel_set_intro_prop; auto.
       split.
       intros s H. apply in_set_bop_intersect_elim in H.
       destruct H as [L R]; auto. 
       intros s H.  apply in_set_bop_intersect_intro.
       split; auto.
Defined. 


Lemma bop_intersect_exists_id (enum : carrier_is_finite S eq) :
   bop_exists_id (finite_set S) (brel_set eq) (bop_intersect eq).
Proof. exists ((projT1 enum) tt).
       apply (bop_intersect_enum_is_id enum). 
Defined. 


Lemma  bop_intersect_singleton_nil (s : S) (X : finite_set S) : in_set eq X s = false -> bop_intersect eq (s :: nil) X = nil.
Proof. intro H. induction X.
       compute. reflexivity. 
       apply not_in_set_cons_elim in H; auto. 
       destruct H as [H1 H2].
       assert (H3 := IHX H2). 
       unfold bop_intersect. unfold bop_intersect in H3.
       unfold uop_filter. unfold uop_filter in H3. 
       unfold filter. (fold (filter (in_set eq (s :: nil)) X)).
       case_eq(in_set eq (s :: nil) a ); intro H4. 
          compute in H4. rewrite H1 in H4. discriminate H4. 
          exact H3. 
Qed.

Lemma bop_intersect_not_exists_id (no_enum : carrier_is_not_finite S eq) : 
   bop_not_exists_id (finite_set S) (brel_set eq) (bop_intersect eq).
Proof.  unfold bop_not_exists_id. intro X.
        unfold bop_not_is_id.
        assert (K := no_enum (λ _, X)). simpl in K.
        destruct K as [s K].
        exists (s :: nil). 
        right. case_eq(brel_set eq (bop_intersect eq (s :: nil) X) (s :: nil)); intro J; auto.
        apply brel_set_elim_prop in J; auto.
        destruct J as [L R]. 
        assert (F : in_set eq (s :: nil) s = true). compute. rewrite refS; auto.
        assert (N := R s F).
        rewrite bop_intersect_singleton_nil in N; auto. 
Defined.

Definition bop_intersect_exists_id_decide (fin_d : carrier_is_finite_decidable S eq) : bop_exists_id_decidable (finite_set S) (brel_set eq) (bop_intersect eq)
 := match fin_d with
     | inl fS  => inl (bop_intersect_exists_id fS) 
     | inr nfs => inr (bop_intersect_not_exists_id nfs)
    end.


End Theory.

Section ACAS.

Definition sg_CI_proofs_intersect 
 {S : Type} (eqvS : A_eqv S) : sg_CI_proofs (finite_set S) (brel_set (A_eqv_eq S eqvS)) (bop_intersect (A_eqv_eq S eqvS)) := 
let rS   := A_eqv_eq S eqvS in
let s    := A_eqv_witness S eqvS in
let f    := A_eqv_new S eqvS in
let ntS  := A_eqv_not_trivial S eqvS in       
let eqvP := A_eqv_proofs S eqvS in
let refS := A_eqv_reflexive S rS eqvP in
let symS := A_eqv_symmetric S rS eqvP in
let tranS := A_eqv_transitive S rS eqvP in                                                            
{|
  A_sg_CI_associative        := bop_intersect_associative S rS refS symS tranS 
; A_sg_CI_congruence         := bop_intersect_congruence S rS  refS symS tranS 
; A_sg_CI_commutative        := bop_intersect_commutative S rS refS symS tranS 
; A_sg_CI_idempotent         := bop_intersect_idempotent S rS refS symS tranS 
; A_sg_CI_not_selective      := bop_intersect_not_selective S rS s f ntS
|}. 

Definition sg_CI_proofs_intersect_with_id {S : Type} (c : cas_constant) (eqv : A_eqv S) := 
  sg_CI_proofs_add_id _ _ c
    (bop_intersect (A_eqv_eq S eqv))
    nil
    (A_eqv_proofs _ (A_eqv_set S eqv))
    (sg_CI_proofs_intersect eqv).

(*the following are used in bi-semigroup (bs) constructions *)
Definition sg_C_proofs_intersect {S : Type} 
  (eqv : A_eqv S) : sg_C_proofs (finite_set S) (brel_set (A_eqv_eq S eqv)) (bop_intersect (A_eqv_eq S eqv))
:= 
let rS   := A_eqv_eq S eqv in
let s    := A_eqv_witness S eqv in
     A_sg_C_proofs_from_sg_CI_proofs
       (finite_set S)
       (brel_set rS)
       (bop_intersect rS)
       (set_witness s)
       (set_new rS s) 
       (brel_set_not_trivial S rS s)
       (eqv_proofs_set S rS (A_eqv_proofs _ eqv)) 
       (sg_CI_proofs_intersect eqv).

Definition sg_C_proofs_intersect_with_id {S : Type} (c : cas_constant) (eqv : A_eqv S)  := 
  sg_C_proofs_add_id _ _ c
    (bop_intersect (A_eqv_eq S eqv))
    nil
    (set_new (A_eqv_eq S eqv) (A_eqv_witness S eqv))
    (brel_set_not_trivial S (A_eqv_eq S eqv) (A_eqv_witness S eqv))
    (A_eqv_proofs _ (A_eqv_set S eqv))
    (sg_C_proofs_intersect eqv). 

Definition sg_proofs_intersect {S : Type}
  (eqv : A_eqv S) : sg_proofs (finite_set S) (brel_set (A_eqv_eq S eqv)) (bop_intersect (A_eqv_eq S eqv))
:= 
let rS   := A_eqv_eq S eqv in
let s    := A_eqv_witness S eqv in
     A_sg_proofs_from_sg_C_proofs
       (finite_set S)
       (brel_set rS)
       (bop_intersect rS)
       (set_witness s)
       (set_new rS s) 
       (brel_set_not_trivial S rS s)
       (eqv_proofs_set S rS (A_eqv_proofs _ eqv)) 
       (sg_C_proofs_intersect eqv). 

Definition sg_proofs_intersect_with_id {S : Type} (c : cas_constant) (eqv : A_eqv S)  := 
  sg_proofs_add_id _ _ c
    (bop_intersect (A_eqv_eq S eqv))
    nil
    (set_new (A_eqv_eq S eqv) (A_eqv_witness S eqv))
    (brel_set_not_trivial S (A_eqv_eq S eqv) (A_eqv_witness S eqv))
    (A_eqv_proofs _ (A_eqv_set S eqv))
    (sg_proofs_intersect eqv). 
(******************************************************************)

Definition A_sg_intersect  {S : Type} (eqv : A_eqv S) : A_sg_CI (finite_set S) := 
  let eqvP := A_eqv_proofs S eqv in
  let symS := A_eqv_symmetric _ _ eqvP in
  let refS := A_eqv_reflexive _ _ eqvP in
  let trnS := A_eqv_transitive _ _ eqvP in     
  let eqS  := A_eqv_eq S eqv in
  let s    := A_eqv_witness S eqv in
  let f    := A_eqv_new S eqv in
  let ntS  := A_eqv_not_trivial S eqv in       
  {| 
     A_sg_CI_eqv          := A_eqv_set S eqv 
   ; A_sg_CI_bop          := bop_intersect eqS 
   ; A_sg_CI_exists_id_d  := bop_intersect_exists_id_decide S eqS refS symS trnS (A_eqv_finite_d _ eqv) 
   ; A_sg_CI_exists_ann_d := inl (bop_intersect_exists_ann S eqS refS symS trnS)
   ; A_sg_CI_proofs       := sg_CI_proofs_intersect eqv
   ; A_sg_CI_ast          := Ast_sg_intersect (A_eqv_ast S eqv)
   |}. 


Definition A_sg_intersect_with_id  {S : Type} (c : cas_constant) (eqv : A_eqv S) : A_sg_CI (with_constant (finite_set S)) := 
  let eqvP := A_eqv_proofs S eqv in
  let symS := A_eqv_symmetric _ _ eqvP in
  let refS := A_eqv_reflexive _ _ eqvP in
  let trnS := A_eqv_transitive _ _ eqvP in     
  let eqS  := A_eqv_eq S eqv in
  let s    := A_eqv_witness S eqv in
  let f    := A_eqv_new S eqv in
  let ntS  := A_eqv_not_trivial S eqv in       
  let new_eqv := A_eqv_set S eqv in 
  let bop := bop_intersect eqS in 
  {| 
     A_sg_CI_eqv          := A_eqv_add_constant _ new_eqv c
   ; A_sg_CI_bop          := bop_add_id bop c 
   ; A_sg_CI_exists_id_d  := inl (bop_intersect_with_id_exists_id S c eqS refS symS)
   ; A_sg_CI_exists_ann_d := inl (bop_intersect_with_id_exists_ann S c eqS refS symS trnS) 
   ; A_sg_CI_proofs       := sg_CI_proofs_intersect_with_id c eqv 
   ; A_sg_CI_ast          := Ast_sg_add_id(c, Ast_sg_intersect (A_eqv_ast S eqv))
   |}. 
  

End ACAS.

Section AMCAS.

Definition A_sg_intersect_below_sg_CI {S : Type} (E : A_eqv S) : @A_below_sg_CI (finite_set S)  :=
    A_classify_sg_CI (A_sg_intersect E) . 

Definition A_sg_intersect_with_id_below_sg_CI {S : Type}
  (c : cas_constant)
   (E : A_eqv S) : @A_below_sg_CI (with_constant (finite_set S))  :=
    A_classify_sg_CI (A_sg_intersect_with_id c E) . 

Definition A_mcas_sg_intersect {S : Type} (A : @A_mcas_eqv S) :=
match A with
| A_EQV_eqv B    =>
    A_MCAS_sg
      (A_Below_sg_sg_C
         (A_Below_sg_C_sg_CI (A_sg_intersect_below_sg_CI B)))

| A_EQV_Error sl => A_MCAS_sg_Error sl 
end.

Definition A_mcas_sg_intersect_with_id {S : Type} (c : cas_constant) (A : @A_mcas_eqv S) :=
match A with
| A_EQV_eqv B    =>
    A_MCAS_sg
      (A_Below_sg_sg_C
         (A_Below_sg_C_sg_CI (A_sg_intersect_with_id_below_sg_CI c B)))

| A_EQV_Error sl => A_MCAS_sg_Error sl 
end.


End AMCAS.   

Section CAS.


Definition sg_CI_certs_intersect : ∀ {S : Type},  @eqv S -> @sg_CI_certificates (finite_set S)
:= λ {S} eqvS,
let s   := eqv_witness eqvS in
let f   := eqv_new eqvS in  
{|
  sg_CI_associative        := Assert_Associative  
; sg_CI_congruence         := Assert_Bop_Congruence  
; sg_CI_commutative        := Assert_Commutative  
; sg_CI_idempotent         := Assert_Idempotent  
; sg_CI_not_selective      := Assert_Not_Selective ((s :: nil), ((f s) :: nil))
|}. 


Definition sg_CI_certs_intersect_with_id {S : Type} (c : cas_constant) (eqv : @eqv S) := 
  sg_CI_certs_add_id c (sg_CI_certs_intersect eqv).


Definition sg_C_certs_intersect {S : Type} (eqv : @eqv S) :=
let rS   := eqv_eq eqv in
let s    := eqv_witness eqv in
     sg_C_certs_from_sg_CI_certs
       (finite_set S)
       (brel_set rS)
       (bop_intersect rS)
       (set_witness s)
       (set_new rS s) 
       (sg_CI_certs_intersect eqv).


Definition sg_C_certs_intersect_with_id {S : Type} (c : cas_constant) (eqv : @eqv S)  := 
  sg_C_certs_add_id c
    nil 
    (set_new (eqv_eq eqv) (eqv_witness eqv))
    (sg_C_certs_intersect eqv).

Definition sg_certs_intersect {S : Type} (eqv : @eqv S) :=
let rS   := eqv_eq eqv in
let s    := eqv_witness eqv in
     sg_certs_from_sg_C_certs
       (finite_set S)
       (brel_set rS)
       (bop_intersect rS)
       (set_witness s)
       (set_new rS s) 
       (sg_C_certs_intersect eqv).

Definition sg_certs_intersect_with_id {S : Type} (c : cas_constant) (eqv : @eqv S)  := 
  sg_certs_add_id c
    nil 
    (set_new (eqv_eq eqv) (eqv_witness eqv))
    (sg_certs_intersect eqv).


Definition  check_intersect_exists_id {S : Type} (d : @check_is_finite S) : @check_exists_id (finite_set S)
  := match d with
     | Certify_Is_Finite fS  => Certify_Exists_Id (fS tt)
     | Certify_Is_Not_Finite => Certify_Not_Exists_Id
     end.

Definition bop_intersect_exists_id_certify {S : Type} (fin_d : @check_is_finite S) : @check_exists_id (finite_set S) 
 := match fin_d with
     | Certify_Is_Finite h  => Certify_Exists_Id (h tt) 
     | Certify_Is_Not_Finite  => Certify_Not_Exists_Id
    end.


Definition sg_intersect {S : Type} (eqv : @eqv S) : @sg_CI (finite_set S) := 
  let eqS  := eqv_eq eqv in
  let s    := eqv_witness eqv in
  let f    := eqv_new eqv in
   {| 
     sg_CI_eqv          := eqv_set eqv 
   ; sg_CI_bop          := bop_intersect eqS 
   ; sg_CI_exists_id_d  := bop_intersect_exists_id_certify (eqv_finite_d eqv) 
   ; sg_CI_exists_ann_d := Certify_Exists_Ann nil 
   ; sg_CI_certs        := sg_CI_certs_intersect eqv
   ; sg_CI_ast          := Ast_sg_intersect (eqv_ast eqv)
   |}.


Definition sg_intersect_with_id {S : Type} (c : cas_constant) (eqvS : @eqv S) : @sg_CI (with_constant (finite_set S)) := 
  let eqS := eqv_eq eqvS in
   {| 
     sg_CI_eqv          := eqv_add_constant (eqv_set eqvS) c 
   ; sg_CI_bop          := bop_add_id (bop_intersect eqS) c 
   ; sg_CI_exists_id_d  := Certify_Exists_Id (inl c) 
   ; sg_CI_exists_ann_d := Certify_Exists_Ann (inr nil) 
   ; sg_CI_certs        := sg_CI_certs_intersect_with_id c eqvS 
   ; sg_CI_ast          := Ast_sg_add_id(c, Ast_sg_intersect (eqv_ast eqvS))
   |}.


End CAS.

Section MCAS.


Definition sg_intersect_below_sg_CI {S : Type} (E : @eqv S) : @below_sg_CI (finite_set S)  :=
    classify_sg_CI (sg_intersect E) . 

Definition sg_intersect_with_id_below_sg_CI {S : Type}
  (c : cas_constant)
   (E : @eqv S) : @below_sg_CI (with_constant (finite_set S))  :=
    classify_sg_CI (sg_intersect_with_id c E) . 

Definition mcas_sg_intersect {S : Type} (A : @mcas_eqv S) :=
match A with
| EQV_eqv B    =>
    MCAS_sg
      (Below_sg_sg_C
         (Below_sg_C_sg_CI (sg_intersect_below_sg_CI B)))

| EQV_Error sl => MCAS_sg_Error sl 
end.

Definition mcas_sg_intersect_with_id {S : Type} (c : cas_constant) (A : @mcas_eqv S) :=
match A with
| EQV_eqv B    =>
    MCAS_sg
      (Below_sg_sg_C
         (Below_sg_C_sg_CI (sg_intersect_with_id_below_sg_CI c B)))

| EQV_Error sl => MCAS_sg_Error sl 
end.

End MCAS.   

Section Verify.

Lemma correct_bop_intersect_exists_id_certify (S : Type) (eqvS : A_eqv S): 
      bop_intersect_exists_id_certify (p2c_is_finite_check S (A_eqv_eq S eqvS) (A_eqv_finite_d S eqvS))
      = 
      p2c_exists_id_check (finite_set S) (brel_set (A_eqv_eq S eqvS)) (bop_intersect (A_eqv_eq S eqvS))
           (bop_intersect_exists_id_decide S (A_eqv_eq S eqvS)
               (A_eqv_reflexive S (A_eqv_eq S eqvS) (A_eqv_proofs S eqvS))
               (A_eqv_symmetric S (A_eqv_eq S eqvS) (A_eqv_proofs S eqvS))
               (A_eqv_transitive S (A_eqv_eq S eqvS) (A_eqv_proofs S eqvS))
               (A_eqv_finite_d S eqvS)).
Proof. unfold bop_intersect_exists_id_certify, bop_intersect_exists_id_decide, p2c_exists_ann_check;
       destruct (A_eqv_finite_d S eqvS) as [[h finP] | nfinP]; simpl; reflexivity. 
Qed. 

Lemma correct_sg_CI_certs_intersect (S : Type) (eqvS : A_eqv S): 
      sg_CI_certs_intersect (A2C_eqv S eqvS)
      =                        
      P2C_sg_CI (brel_set (A_eqv_eq S eqvS)) (bop_intersect (A_eqv_eq S eqvS))
                (sg_CI_proofs_intersect eqvS).
Proof. destruct eqvS.
       unfold sg_CI_certs_intersect, sg_CI_proofs_intersect. unfold P2C_sg_CI. simpl.
       reflexivity.        
Qed.

Lemma correct_sg_CI_certs_intersect_with_id (S : Type) (c : cas_constant) (eqvS : A_eqv S): 
      sg_CI_certs_intersect_with_id c (A2C_eqv S eqvS)
      =                        
      P2C_sg_CI (brel_sum brel_constant (A_eqv_eq (finite_set S) (A_eqv_set S eqvS)))
                (bop_add_id (bop_intersect (A_eqv_eq S eqvS)) c)
                (sg_CI_proofs_intersect_with_id c eqvS).
Proof. destruct eqvS.
       unfold sg_CI_certs_intersect, sg_CI_proofs_intersect. unfold P2C_sg_CI. simpl.
       reflexivity.        
Qed.


Lemma correct_sg_C_certs_intersect (S : Type) (eqvS : A_eqv S): 
      sg_C_certs_intersect (A2C_eqv S eqvS)
      =                        
      P2C_sg_C (brel_set (A_eqv_eq S eqvS)) (bop_intersect (A_eqv_eq S eqvS))
               (sg_C_proofs_intersect eqvS).
Proof. unfold sg_C_certs_intersect, sg_C_proofs_intersect.
       rewrite <- correct_sg_C_certs_from_sg_CI_certs. 
       rewrite correct_sg_CI_certs_intersect.  
       reflexivity.               
Qed.

Lemma correct_sg_C_certs_intersect_with_id (S : Type) (c : cas_constant) (eqvS : A_eqv S): 
      sg_C_certs_intersect_with_id c (A2C_eqv S eqvS)
      =                        
      P2C_sg_C (brel_sum brel_constant (A_eqv_eq (finite_set S) (A_eqv_set S eqvS)))
               (bop_add_id (bop_intersect (A_eqv_eq S eqvS)) c)
               (sg_C_proofs_intersect_with_id c eqvS).
Proof. unfold sg_C_certs_intersect_with_id, sg_C_proofs_intersect_with_id.
       rewrite <- correct_sg_C_certs_add_id. 
       rewrite correct_sg_C_certs_intersect.  
       reflexivity.               
Qed.


Lemma correct_sg_certs_intersect (S : Type) (eqvS : A_eqv S): 
      sg_certs_intersect (A2C_eqv S eqvS)
      =                        
      P2C_sg (brel_set (A_eqv_eq S eqvS)) (bop_intersect (A_eqv_eq S eqvS))
             (sg_proofs_intersect eqvS).
Proof. unfold sg_certs_intersect, sg_proofs_intersect.
       rewrite <- correct_sg_certs_from_sg_C_certs. 
       rewrite correct_sg_C_certs_intersect.  
       reflexivity.               
Qed.

Lemma correct_sg_certs_intersect_with_id (S : Type) (c : cas_constant) (eqvS : A_eqv S): 
      sg_certs_intersect_with_id c (A2C_eqv S eqvS)
      =                        
      P2C_sg (brel_sum brel_constant (A_eqv_eq (finite_set S) (A_eqv_set S eqvS)))
             (bop_add_id (bop_intersect (A_eqv_eq S eqvS)) c)
             (sg_proofs_intersect_with_id c eqvS).
Proof. unfold sg_certs_intersect_with_id, sg_proofs_intersect_with_id.
       rewrite <- correct_sg_certs_add_id. 
       rewrite correct_sg_certs_intersect.  
       reflexivity.               
Qed.


Theorem correct_sg_intersect (S : Type) (eqvS : A_eqv S) : 
  sg_intersect  (A2C_eqv S eqvS)
  =
  A2C_sg_CI (A_sg_intersect eqvS). 
Proof. unfold sg_intersect, A_sg_intersect, A2C_sg, A2C_sg_CI; simpl. 
       rewrite correct_eqv_set.        
       rewrite correct_sg_CI_certs_intersect. 
       rewrite <- correct_bop_intersect_exists_id_certify.
       reflexivity. 
Qed. 
    
Theorem correct_sg_intersect_with_id (S : Type) (c : cas_constant)(eqvS : A_eqv S): 
         sg_intersect_with_id c (A2C_eqv S eqvS)  
         = 
         A2C_sg_CI (A_sg_intersect_with_id c eqvS). 
Proof. unfold sg_intersect_with_id, A_sg_intersect_with_id. unfold A2C_sg_CI. simpl.
       rewrite correct_eqv_set.        
       rewrite correct_eqv_add_constant.
       rewrite correct_sg_CI_certs_intersect_with_id. 
       reflexivity. 
Qed. 


Theorem correct_sg_intersect_with_id_below_sg_CI (S : Type ) (c : cas_constant) (A : A_eqv S) : 
    sg_intersect_with_id_below_sg_CI c (A2C_eqv S A)
    =
    A2C_below_sg_CI (A_sg_intersect_with_id_below_sg_CI c A).
Proof. unfold sg_intersect_with_id_below_sg_CI, A_sg_intersect_with_id_below_sg_CI.
       rewrite correct_sg_intersect_with_id.
       rewrite correct_classify_sg_CI. 
       reflexivity.
Qed.

Theorem correct_bop_mcas_intersect_with_id
  (S : Type) (c : cas_constant)(eqvS : @A_mcas_eqv S): 
         mcas_sg_intersect_with_id c (A2C_mcas_eqv S eqvS)  
         = 
         A2C_sg_mcas (A_mcas_sg_intersect_with_id c eqvS). 
Proof. unfold mcas_sg_intersect_with_id, A_mcas_sg_intersect_with_id.
       destruct eqvS; simpl.
       + reflexivity. 
       + rewrite correct_sg_intersect_with_id_below_sg_CI.
         reflexivity. 
Qed.  

Theorem correct_sg_intersect_below_sg_CI (S : Type )(A : A_eqv S) : 
    sg_intersect_below_sg_CI (A2C_eqv S A)
    =
    A2C_below_sg_CI (A_sg_intersect_below_sg_CI A).
Proof. unfold sg_intersect_below_sg_CI, A_sg_intersect_below_sg_CI.
       rewrite correct_sg_intersect.
       unfold classify_sg_CI, A_classify_sg_CI.
       unfold A2C_below_sg_CI. 
       reflexivity.
Qed.
  
Theorem correct_bop_mcas_intersect (S : Type) (eqvS : @A_mcas_eqv S): 
         mcas_sg_intersect (A2C_mcas_eqv S eqvS)  
         = 
         A2C_sg_mcas (A_mcas_sg_intersect eqvS). 
Proof. unfold mcas_sg_intersect, A_mcas_sg_intersect.
       destruct eqvS; simpl.
       + reflexivity.
       + rewrite correct_sg_intersect_below_sg_CI.
         unfold A_sg_intersect_below_sg_CI. 
         rewrite <- correct_classify_sg_CI.
         unfold classify_sg_CI. 
         reflexivity. 
Qed.  



 
End Verify.   
  
