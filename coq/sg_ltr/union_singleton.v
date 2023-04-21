
Require Import CAS.coq.common.compute.
Require Import CAS.coq.eqv.properties. 
Require Import CAS.coq.eqv.set. 
Require Import CAS.coq.sg.union. 
Require Import CAS.coq.tr.left.singleton.
Require Import CAS.coq.bs.properties. 
Require Import CAS.coq.st.properties. 
Require Import CAS.coq.st.structures.

Section Theory.

Variables (S : Type)
          (wS : S)   
          (eq : brel S)
          (ref : brel_reflexive S eq)
          (sym : brel_symmetric S eq)
          (trn : brel_transitive S eq). 


Lemma slt_union_singleton_distributive : slt_distributive S (finite_set S) (brel_set eq) (bop_union eq) ltr_singleton.
Proof. intros s X Y. unfold slt_distributive, ltr_singleton.
       assert (A := bop_union_idempotent S eq ref sym trn (s :: nil)).
       apply brel_set_symmetric. exact A. 
Qed. 

Lemma slt_union_singleton_not_absorptive : 
       slt_not_absorptive S (finite_set S) (brel_set eq) (bop_union eq) ltr_singleton.
Proof. exists (wS, nil). compute. reflexivity. Defined. 

Lemma slt_union_singleton_not_strictly_absorptive : 
       slt_not_strictly_absorptive S (finite_set S) (brel_set eq) (bop_union eq) ltr_singleton.
Proof. exists (wS, nil). left. compute. reflexivity. Defined. 


End Theory.   
