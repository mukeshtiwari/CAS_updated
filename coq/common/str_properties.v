Require Import CAS.coq.common.compute.

Close Scope nat. 

Definition sltr_distributive (S L : Type) (r : brel S) (add : binary_op S) (ltr : L -> (S -> S)) 
   := ∀ (l : L) (t u : S), r (ltr l (add t u)) (add (ltr l t) (ltr l u)) = true. 

Definition sltr_not_distributive (S L : Type) (r : brel S) (add : binary_op S) (ltr : L -> (S -> S)) 
   := { z : L * (S * S) & match z with (l, (t, u)) => r (ltr l (add t u)) (add (ltr l t) (ltr l u)) = false end }. 

Definition sltr_distributive_decidable (S L : Type) (r : brel S) (add : binary_op S) (ltr : L -> (S -> S)) 
   := (sltr_distributive S L r add ltr) + (sltr_not_distributive S L r add ltr). 
 
Definition sltr_absorptive (S L : Type) (r : brel S) (add : binary_op S) (ltr : L -> (S -> S)) 
  := ∀ (l : L) (s : S), r s (add s (ltr l s)) = true.

Definition sltr_not_absorptive (S L : Type) (r : brel S) (add : binary_op S) (ltr : L -> (S -> S)) 
   := { z : L * S  & match z with (l, s) =>  r s (add s (ltr l s)) = false end }. 

Definition sltr_absorptive_decidable (S L : Type) (r : brel S) (add : binary_op S) (ltr : L -> (S -> S)) 
   := (sltr_absorptive S L r add ltr) + (sltr_not_absorptive S L r add ltr). 

