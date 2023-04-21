Require Import CAS.coq.common.compute.
Require Import CAS.coq.sg.properties.
Require Import CAS.coq.ltr.properties. 

Close Scope nat.

Section ACAS.

Definition A_sg_ltr_distributive {L S : Type} (r : brel S) (add : binary_op S) (ltr : L -> (S -> S)) 
   := ∀ (l : L) (t u : S), r (ltr l (add t u)) (add (ltr l t) (ltr l u)) = true. 

Definition A_sg_ltr_not_distributive {L S : Type} (r : brel S) (add : binary_op S) (ltr : L -> (S -> S)) 
   := { z : L * (S * S) & match z with (l, (t, u)) => r (ltr l (add t u)) (add (ltr l t) (ltr l u)) = false end }. 

Definition A_sg_ltr_distributive_decidable {L S : Type} (r : brel S) (add : binary_op S) (ltr : L -> (S -> S)) 
   := (A_sg_ltr_distributive r add ltr) + (A_sg_ltr_not_distributive r add ltr). 
 
Definition A_sg_ltr_absorptive {L S : Type} (r : brel S) (add : binary_op S) (ltr : L -> (S -> S)) 
  := ∀ (l : L) (s : S), r s (add s (ltr l s)) = true.

Definition A_sg_ltr_not_absorptive {L S : Type} (r : brel S) (add : binary_op S) (ltr : L -> (S -> S)) 
   := { z : L * S  & match z with (l, s) =>  r s (add s (ltr l s)) = false end }. 

Definition A_sg_ltr_absorptive_decidable {L S : Type} (r : brel S) (add : binary_op S) (ltr : L -> (S -> S)) 
   := (A_sg_ltr_absorptive r add ltr) + (A_sg_ltr_not_absorptive r add ltr). 

Definition A_sg_ltr_strictly_absorptive {L S : Type} (r : brel S) (add : binary_op S) (ltr : L -> (S -> S)) 
  := ∀ (l : L) (s : S), ((r s (add s (ltr l s)) = true) * (r (ltr l s) (add s (ltr l s)) = false)).

Definition A_sg_ltr_not_strictly_absorptive {L S : Type} (r : brel S) (add : binary_op S) (ltr : L -> (S -> S)) 
   := { z : L * S  & match z with (l, s) =>  ((r s (add s (ltr l s)) = false)  +  (r (ltr l s) (add s (ltr l s)) = true)) end }. 

Definition A_sg_ltr_strictly_absorptive_decidable {L S : Type} (r : brel S) (add : binary_op S) (ltr : L -> (S -> S)) 
   := (A_sg_ltr_strictly_absorptive r add ltr) + (A_sg_ltr_not_strictly_absorptive r add ltr). 

Definition A_sg_ltr_exists_id_ann_equal {L S : Type} (r : brel S) (b : binary_op S) (ltr : L -> (S -> S)) 
  := { i : S & (bop_is_id S r b i) * (A_ltr_is_ann r ltr i)}.

Definition A_sg_ltr_exists_id_ann_not_equal {L S : Type} (r : brel S) (b : binary_op S) (ltr : L -> (S -> S)) 
  := { z : S * S & match z with (i, a) => (bop_is_id S r b i) * (A_ltr_is_ann r ltr a) * (r i a = false) end}.

Inductive A_sg_ltr_exists_id_ann_decidable {L S : Type} (eq : brel S) (b : binary_op S) (ltr : L -> (S -> S))  : Type :=
| A_SLT_Id_Ann_Proof_None      : (bop_not_exists_id S eq b) * (A_ltr_not_exists_ann eq ltr) -> A_sg_ltr_exists_id_ann_decidable eq b ltr 
| A_SLT_Id_Ann_Proof_Id_None   : (bop_exists_id S eq b) * (A_ltr_not_exists_ann eq ltr)     -> A_sg_ltr_exists_id_ann_decidable eq b ltr 
| A_SLT_Id_Ann_Proof_None_Ann  : (bop_not_exists_id S eq b) * (A_ltr_exists_ann eq ltr)     -> A_sg_ltr_exists_id_ann_decidable eq b ltr 
| A_SLT_Id_Ann_Proof_Equal     : A_sg_ltr_exists_id_ann_equal eq b ltr                      -> A_sg_ltr_exists_id_ann_decidable eq b ltr 
| A_SLT_Id_Ann_Proof_Not_Equal : A_sg_ltr_exists_id_ann_not_equal eq b ltr                  -> A_sg_ltr_exists_id_ann_decidable eq b ltr 
. 


End ACAS. 

    
  
  

  

   

