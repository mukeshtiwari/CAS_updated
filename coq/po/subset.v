
Require Import CAS.coq.common.compute. 
Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures. 
Require Import CAS.coq.eqv.theory.
Require Import CAS.coq.eqv.set. 

Require Import CAS.coq.po.properties.
Require Import CAS.coq.po.structures. 

Require Import CAS.coq.sg.and.
Require Import CAS.coq.sg.or. 

Open Scope list_scope.

(* brel_subset defined in coq/eqv/set.v 
   as well as
   brel_subset_congruence : brel_congruence (finite_set S) (brel_set eq) (brel_subset eq).
   brel_subset_reflexive : brel_reflexive (finite_set S) (brel_subset r). 
   brel_subset_transitive : brel_transitive (finite_set S) (brel_subset r). 
*) 

Close Scope nat.

Section Theory.

Variable S: Type.
Variable eq : brel S.
Variable refS : brel_reflexive S eq.
Variable symS : brel_symmetric S eq.
Variable tranS : brel_transitive S eq.
  
Lemma brel_subset_antisymmetric : brel_antisymmetric (finite_set S) (brel_set eq) (brel_subset eq). 
Proof. intros x y H1 H2.
       unfold brel_set. unfold brel_and_sym.
       rewrite H1, H2. auto.
Defined.

(*
Print brel_subset_antisymmetric. 

brel_subset_antisymmetric = 
λ (x y : finite_set S) 
  (H1 : brel_subset eq x y = true) 
  (H2 : brel_subset eq y x = true),
  eq_ind_r (λ b : bool, (b && brel_subset eq y x)%bool = true)
           (eq_ind_r (λ b : bool, (true && b)%bool = true) eq_refl H2) H1
 : brel_antisymmetric (finite_set S) (brel_set eq) (brel_subset eq)
 *)

Lemma brel_subset_not_total (wS : S) (f : S -> S) (nt : brel_not_trivial S eq f): brel_not_total (finite_set S) (brel_subset eq).
Proof. exists (wS :: nil, (f wS)::nil). compute. destruct (nt wS) as [A B]. 
      rewrite A, B. auto. 
Defined.

End Theory. 

Section ACAS.

Definition po_subset_proofs {S : Type} (eqvS : A_eqv S) :
  po_proofs (finite_set S) (brel_set (A_eqv_eq _ eqvS)) (brel_subset (A_eqv_eq _ eqvS)) :=
let eq   := A_eqv_eq _ eqvS in  
let wS   := A_eqv_witness _ eqvS in
let f    := A_eqv_new _ eqvS in
let nt   := A_eqv_not_trivial _ eqvS in 
let eqvP := A_eqv_proofs _ eqvS in
let refS := A_eqv_reflexive _ _ eqvP in
let symS := A_eqv_symmetric _ _ eqvP in
let trnS := A_eqv_transitive _ _ eqvP in
{|
   A_po_congruence    := brel_subset_congruence S eq refS symS trnS 
 ; A_po_reflexive     := brel_subset_reflexive S eq refS symS 
 ; A_po_transitive    := brel_subset_transitive S eq refS symS trnS 
 ; A_po_antisymmetric := brel_subset_antisymmetric S eq
 ; A_po_not_total     := brel_subset_not_total S eq wS f nt
|}.

End ACAS. 
