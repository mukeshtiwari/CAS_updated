Require Import CAS.coq.common.compute.
Require Import CAS.coq.sg.properties.
Require Import CAS.coq.rtr.properties. 

Close Scope nat.

Section ACAS.

Definition A_sg_rtr_distributive {L S : Type} (r : brel S) (add : binary_op S) (rtr : rtr_type L S) 
   := ∀ (l : L) (t u : S), r (rtr (add t u) l) (add (rtr t l) (rtr u l)) = true. 

Definition A_sg_rtr_not_distributive {L S : Type} (r : brel S) (add : binary_op S) (rtr : rtr_type L S) 
   := { z : L * (S * S) & match z with (l, (t, u)) => r (rtr (add t u) l) (add (rtr t l) (rtr u l)) = false end }. 

Definition A_sg_rtr_distributive_decidable {L S : Type} (r : brel S) (add : binary_op S) (rtr : rtr_type L S) 
   := (A_sg_rtr_distributive r add rtr) + (A_sg_rtr_not_distributive r add rtr). 
 
Definition A_sg_rtr_absorptive {L S : Type} (r : brel S) (add : binary_op S) (rtr : rtr_type L S) 
  := ∀ (l : L) (s : S), r s (add s (rtr s l)) = true.

Definition A_sg_rtr_not_absorptive {L S : Type} (r : brel S) (add : binary_op S) (rtr : rtr_type L S) 
   := { z : L * S  & match z with (l, s) =>  r s (add s (rtr s l)) = false end }. 

Definition A_sg_rtr_absorptive_decidable {L S : Type} (r : brel S) (add : binary_op S) (rtr : rtr_type L S) 
   := (A_sg_rtr_absorptive r add rtr) + (A_sg_rtr_not_absorptive r add rtr). 

Definition A_sg_rtr_strictly_absorptive {L S : Type} (r : brel S) (add : binary_op S) (rtr : rtr_type L S) 
  := ∀ (l : L) (s : S), ((r s (add s (rtr s l)) = true) * (r (rtr s l) (add s (rtr s l)) = false)).

Definition A_sg_rtr_not_strictly_absorptive {L S : Type} (r : brel S) (add : binary_op S) (rtr : rtr_type L S) 
   := { z : L * S  & match z with (l, s) =>  ((r s (add s (rtr s l)) = false)  +  (r (rtr s l) (add s (rtr s l)) = true)) end }. 

Definition A_sg_rtr_strictly_absorptive_decidable {L S : Type} (r : brel S) (add : binary_op S) (rtr : rtr_type L S) 
   := (A_sg_rtr_strictly_absorptive r add rtr) + (A_sg_rtr_not_strictly_absorptive r add rtr). 

Definition A_sg_rtr_exists_id_ann_equal {L S : Type} (r : brel S) (b : binary_op S) (rtr : rtr_type L S) 
  := { i : S & (bop_is_id S r b i) * (A_rtr_is_ann r rtr i)}.

Definition A_sg_rtr_exists_id_ann_not_equal {L S : Type} (r : brel S) (b : binary_op S) (rtr : rtr_type L S) 
  := { z : S * S & match z with (i, a) => (bop_is_id S r b i) * (A_rtr_is_ann r rtr a) * (r i a = false) end}.

Inductive A_sg_rtr_exists_id_ann_decidable {L S : Type} (eq : brel S) (b : binary_op S) (rtr : rtr_type L S)  : Type :=
| A_SG_RTR_Id_Ann_Proof_None      : (bop_not_exists_id S eq b) * (A_rtr_not_exists_ann eq rtr) -> A_sg_rtr_exists_id_ann_decidable eq b rtr 
| A_SG_RTR_Id_Ann_Proof_Id_None   : (bop_exists_id S eq b) * (A_rtr_not_exists_ann eq rtr)     -> A_sg_rtr_exists_id_ann_decidable eq b rtr 
| A_SG_RTR_Id_Ann_Proof_None_Ann  : (bop_not_exists_id S eq b) * (A_rtr_exists_ann eq rtr)     -> A_sg_rtr_exists_id_ann_decidable eq b rtr 
| A_SG_RTR_Id_Ann_Proof_Equal     : A_sg_rtr_exists_id_ann_equal eq b rtr                      -> A_sg_rtr_exists_id_ann_decidable eq b rtr 
| A_SG_RTR_Id_Ann_Proof_Not_Equal : A_sg_rtr_exists_id_ann_not_equal eq b rtr                  -> A_sg_rtr_exists_id_ann_decidable eq b rtr 
. 


End ACAS. 

    
  
  

  

   

