Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.

Require Import CAS.coq.theory.set. 

Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.eqv.set.

Require Import CAS.coq.sg.union. 

Require Import CAS.coq.or.properties.
Require Import CAS.coq.or.structures.

Section Computation.
  
Definition set_lte {S : Type} (eq lte : brel S) (X Y: finite_set S) := 
           ∀ y : S,  in_set eq Y y = true -> {x : S & (in_set eq X x = true) * (lte x y = true) }. 

End Computation.

Section Theory.

Variable S  : Type. 
Variable eq : brel S.

Variable wS : S.
Variable fS : S -> S.                
Variable Pf : brel_not_trivial S eq fS. 

Variable congS : brel_congruence S eq eq. 
Variable refS  : brel_reflexive S eq.
Variable symS  : brel_symmetric S eq.  
Variable tranS : brel_transitive S eq.

Variable lte : brel S. 
Variable lteCong : brel_congruence S eq lte.
Variable lteRefl : brel_reflexive S lte.
Variable lteTrans : brel_transitive S lte.

Notation "a [=] b"  := (eq a b = true)          (at level 15).
Notation "a [<>] b" := (eq a b = false)         (at level 15).
Notation "a <<= b"  := (lte a b = true)        (at level 15).
Notation "a !<<= b" := (lte a b = false)       (at level 15).

Notation "a [<=] b"   := (set_lte eq lte a b) (at level 15).  
Notation "a [in] b"  := (in_set eq b a = true)   (at level 15).
Notation "a [!in] b" := (in_set eq b a = false)  (at level 15).
Notation "a [U] b" := (bop_union eq a b)         (at level 15).

(* the next two are used in bs/minset_lift_union. 
   do they belong here? 
*) 
Lemma set_lte_lemma (X : finite_set S) :
  ∀ (Y Z : finite_set S), (X [<=] Y) ->  (X [U] Z) [<=] Y.
Proof. intros Y Z A s B.  
       destruct (A s B) as [x [C D]].
       exists x. split; auto. 
       apply in_set_bop_union_intro; auto. 
Defined.

Lemma set_lte_lemma2 (X : finite_set S) :
  ∀ (Y Z : finite_set S), (X [<=] Y) ->  (X [<=] Z) ->  X [<=] (Y [U] Z).
Proof. intros Y Z A B s C.
       apply in_set_bop_union_elim in C; auto.
       destruct C as [C | C]. 
       ++ exact (A _ C). 
       ++ exact (B _ C).        
Defined.



End Theory.   
