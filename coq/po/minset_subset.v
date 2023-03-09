
Require Import CAS.coq.common.compute. 
Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures. 
Require Import CAS.coq.eqv.theory.
Require Import CAS.coq.eqv.set.
Require Import CAS.coq.eqv.minset.
Require Import CAS.coq.eqv.reduce. 

Require Import CAS.coq.po.properties.
Require Import CAS.coq.po.structures.
Require Import CAS.coq.po.subset. 

Require Import CAS.coq.sg.and.
Require Import CAS.coq.sg.or. 

Close Scope nat.


Section Computation.

Definition brel_minset_subset {S : Type} (eq lte : brel S) : brel (finite_set S)
:= λ X Y, brel_subset eq (uop_minset lte X) (uop_minset lte Y). 

End Computation.

Section Theory.

Variable S: Type.
Variable eq : brel S.
Variable refS : brel_reflexive S eq.
Variable symS : brel_symmetric S eq.
Variable tranS : brel_transitive S eq.

Variable lte : brel S.

Lemma brel_minset_subset_congruence : brel_congruence (finite_set S) (brel_minset eq lte) (brel_minset_subset eq lte).
Proof. unfold brel_congruence. unfold brel_minset_subset.
       intros X Y W Z A B.
       unfold brel_minset in A, B. 
       apply brel_subset_congruence; auto. 
Qed.

Lemma brel_minset_subset_reflexive : brel_reflexive (finite_set S) (brel_minset_subset eq lte).
Proof. intro X. unfold brel_minset_subset. apply brel_subset_reflexive; auto.  Qed.        

Lemma brel_minset_subset_transitive : brel_transitive (finite_set S) (brel_minset_subset eq lte).
Proof. unfold brel_transitive. unfold brel_minset_subset.
       intros X Y W A B.
       exact (brel_subset_transitive _ _ refS symS tranS _ _ _ A B).
Qed.        
  
Lemma brel_minset_subset_antisymmetric : brel_antisymmetric (finite_set S) (brel_minset eq lte) (brel_minset_subset eq lte). 
Proof. intros x y H1 H2.
       unfold brel_minset_subset in H1, H2.
       unfold brel_minset, brel_reduce.
       unfold brel_set. unfold brel_and_sym.
       rewrite H1, H2. auto.
Defined.

Lemma brel_minset_subset_not_total (wS : S) (f : S -> S) (nt : brel_not_trivial S eq f): brel_not_total (finite_set S) (brel_minset_subset eq lte).
Proof. exists (wS :: nil, (f wS)::nil). compute. destruct (nt wS) as [A B]. 
      rewrite A, B. auto. 
Defined.

End Theory. 

Section ACAS.


Definition po_minset_subset_proofs {S : Type} (eqvS : A_eqv S) (lte : brel S) :
  po_proofs (finite_set S) (brel_minset (A_eqv_eq _ eqvS) lte) (brel_minset_subset (A_eqv_eq _ eqvS) lte) :=
let eq   := A_eqv_eq _ eqvS in  
let wS   := A_eqv_witness _ eqvS in
let f    := A_eqv_new _ eqvS in
let nt   := A_eqv_not_trivial _ eqvS in 
let eqvP := A_eqv_proofs _ eqvS in
let refS := A_eqv_reflexive _ _ eqvP in
let symS := A_eqv_symmetric _ _ eqvP in
let trnS := A_eqv_transitive _ _ eqvP in
{|
   A_po_congruence    := brel_minset_subset_congruence S eq refS symS trnS lte 
 ; A_po_reflexive     := brel_minset_subset_reflexive S eq refS symS lte 
 ; A_po_transitive    := brel_minset_subset_transitive S eq refS symS trnS lte
 ; A_po_antisymmetric := brel_minset_subset_antisymmetric S eq lte
 ; A_po_not_total     := brel_minset_subset_not_total S eq lte wS f nt
|}.

End ACAS. 
