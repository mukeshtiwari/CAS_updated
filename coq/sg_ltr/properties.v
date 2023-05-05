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

(* Some terminology 
    
  a <= b == a = a + b 

  ∀ l s, s <=  (l |> s)   : non-decreasing 
  
  ∀ l s, (l |> s) <= s    : non-increasing 

  ∀ l s, ¬(s <= (l |> s)) : never non-decreasing 

  ∀ l s, ¬((l |> s) <= s) : never non-increasing  

  ∀ l s, s < (l |> s)     : increasing = non-decreasing and never non-increasing  

  ∀ l s, (l |> s) < s     : decreasing = non-increasing and never non-decreasing 


  ∃ l s, ¬(s <= (l |> s)) : not non-decreasing 

  ∃ l s, ¬((l |> s) <= s) : not non-increasing 

  ∃ l s, s <= (l |> s)    : not never non-decreasing = exists non-decreasing 

  ∃ l s, (l |> s) <= s    : not never non-increasing = exists non-increasing

  ∃ l s, ¬(s < (l |> s))  : not increasing = (not non-decreasing) or (exists non-increasing) 

  ∃ l s, ¬((l |> s) < s)  : not decreasing = (not non-increasing) or (exists non-decreasing)
*) 

Definition A_sg_ltr_absorptive {L S : Type} (r : brel S) (add : binary_op S) (ltr : L -> (S -> S)) 
  := ∀ (l : L) (s : S), r s (add s (ltr l s)) = true.

Definition A_sg_ltr_not_absorptive {L S : Type} (r : brel S) (add : binary_op S) (ltr : L -> (S -> S)) 
   := { z : L * S  & match z with (l, s) =>  r s (add s (ltr l s)) = false end }. 

Definition A_sg_ltr_absorptive_decidable {L S : Type} (r : brel S) (add : binary_op S) (ltr : L -> (S -> S)) 
   := (A_sg_ltr_absorptive r add ltr) + (A_sg_ltr_not_absorptive r add ltr). 

(*
Definition A_sg_ltr_ {L S : Type} (r : brel S) (add : binary_op S) (ltr : L -> (S -> S)) 
  := ∀ (l : L) (s : S), r (ltr l s) (add s (ltr l s)) = false).
*) 
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

| A_SG_LTR_Id_Ann_None      : (bop_not_exists_id S eq b) * (A_ltr_not_exists_ann eq ltr) -> A_sg_ltr_exists_id_ann_decidable eq b ltr 
| A_SG_LTR_Id_Ann_Id_None   : (bop_exists_id S eq b) * (A_ltr_not_exists_ann eq ltr)     -> A_sg_ltr_exists_id_ann_decidable eq b ltr 
| A_SG_LTR_Id_Ann_None_Ann  : (bop_not_exists_id S eq b) * (A_ltr_exists_ann eq ltr)     -> A_sg_ltr_exists_id_ann_decidable eq b ltr 
| A_SG_LTR_Id_Ann_Equal     : A_sg_ltr_exists_id_ann_equal eq b ltr                      -> A_sg_ltr_exists_id_ann_decidable eq b ltr 
| A_SG_LTR_Id_Ann_Not_Equal : A_sg_ltr_exists_id_ann_not_equal eq b ltr                  -> A_sg_ltr_exists_id_ann_decidable eq b ltr 
. 


End ACAS. 

Section CAS.

Inductive sg_ltr_distributive {L S : Type} := 
| SG_LTR_Distributive : L * S -> @sg_ltr_distributive L S. 

Inductive sg_ltr_not_distributive {L S : Type} := 
| SG_LTR_Not_Distributive : (L * (S * S)) -> @sg_ltr_not_distributive L S.

Definition sg_ltr_distributive_decidable {L S : Type} := 
   (@sg_ltr_distributive L S)
   +
   (@sg_ltr_not_distributive L S). 

Inductive sg_ltr_absorptive {L S : Type} := 
| SG_LTR_Absorptive : L * S-> @sg_ltr_absorptive L S.

Inductive sg_ltr_not_absorptive {L S : Type} := 
| SG_LTR_Not_Absorptive : (L * S) -> @sg_ltr_not_absorptive L S.

Definition sg_ltr_absorptive_decidable  {L S : Type} := 
  (@sg_ltr_absorptive L S)
  +
  (@sg_ltr_not_absorptive L S). 


Inductive sg_ltr_strictly_absorptive {L S : Type} := 
| SG_LTR_Strictly_Absorptive : L * S-> @sg_ltr_strictly_absorptive L S.

Inductive sg_ltr_not_strictly_absorptive {L S : Type} := 
| SG_LTR_Not_Strictly_Absorptive : (L * S) -> @sg_ltr_not_strictly_absorptive L S.

Definition sg_ltr_strictly_absorptive_decidable  {L S : Type} := 
  (@sg_ltr_strictly_absorptive L S)
  +
  (@sg_ltr_not_strictly_absorptive L S). 


Inductive sg_ltr_exists_id_ann_equal {L S : Type} := 
| SG_LTR_Exists_Id_Ann_Equal : L * S → @sg_ltr_exists_id_ann_equal L S. 

Inductive sg_ltr_exists_id_ann_not_equal {L S : Type} := 
| SG_LTR_Exists_Id_Ann_Not_Equal : L * (S * S) → @sg_ltr_exists_id_ann_not_equal L S.

Inductive sg_ltr_exists_id_ann_decidable {L S : Type} : Type :=
| SG_LTR_Id_Ann_None      : @sg_ltr_exists_id_ann_decidable L S
| SG_LTR_Id_Ann_Id_None   : S -> @sg_ltr_exists_id_ann_decidable L S
| SG_LTR_Id_Ann_None_Ann  : S -> @sg_ltr_exists_id_ann_decidable L S
| SG_LTR_Id_Ann_Equal     : S -> @sg_ltr_exists_id_ann_decidable L S
| SG_LTR_Id_Ann_Not_Equal : (S * S) -> @sg_ltr_exists_id_ann_decidable L S.


End CAS.

Section Translation.

    Definition p2c_sg_ltr_distributive
    {L S : Type} (r : brel S) (b : binary_op S) (ltr : ltr_type L S)
    (p : A_sg_ltr_distributive r b ltr) (wL : L) (wS : S) :
      @sg_ltr_distributive L S := 
    SG_LTR_Distributive (wL, wS). 

    Definition p2c_sg_ltr_not_distributive
    {L S : Type} (r : brel S) (b : binary_op S) (ltr : ltr_type L S)
    (p : A_sg_ltr_not_distributive r b ltr) :
      @sg_ltr_not_distributive L S :=       
      SG_LTR_Not_Distributive(projT1 p). 

    Definition p2c_sg_ltr_distributive_decidable
    {L S : Type} (r : brel S) (b : binary_op S) (ltr : ltr_type L S)
    (d : A_sg_ltr_distributive_decidable r b ltr)
    (wL : L) (wS : S) :
      @sg_ltr_distributive_decidable L S := 
      match d with 
      | inl p => inl (p2c_sg_ltr_distributive r b ltr p wL wS) 
      | inr p => inr (p2c_sg_ltr_not_distributive r b ltr p) 
      end. 

    Definition p2c_sg_ltr_absorptive
    {L S : Type} (r : brel S) (b : binary_op S) (ltr : ltr_type L S)
    (p : A_sg_ltr_absorptive r b ltr) (wL : L) (wS : S) :
      @sg_ltr_absorptive L S := 
      SG_LTR_Absorptive (wL, wS). 

    Definition p2c_sg_ltr_not_absorptive
    {L S : Type} (r : brel S) (b : binary_op S) (ltr : ltr_type L S)
    (p : A_sg_ltr_not_absorptive r b ltr) :
      @sg_ltr_not_absorptive L S := 
      SG_LTR_Not_Absorptive(projT1 p). 

    Definition p2c_sg_ltr_absorptive_decidable
    {L S : Type} (r : brel S) (b : binary_op S) (ltr : ltr_type L S)
    (d : A_sg_ltr_absorptive_decidable r b ltr) (wL : L) (wS : S) :
      @sg_ltr_absorptive_decidable L S := 
      match d with 
      | inl p => inl (p2c_sg_ltr_absorptive r b ltr p wL wS)
      | inr p => inr (p2c_sg_ltr_not_absorptive r b ltr p) 
      end. 


    Definition p2c_sg_ltr_strictly_absorptive
    {L S : Type} (r : brel S) (b : binary_op S) (ltr : ltr_type L S)
    (p : A_sg_ltr_strictly_absorptive r b ltr) (wL : L) (wS : S) :
      @sg_ltr_strictly_absorptive L S := 
      SG_LTR_Strictly_Absorptive (wL, wS). 

    Definition p2c_sg_ltr_not_strictly_absorptive
    {L S : Type} (r : brel S) (b : binary_op S) (ltr : ltr_type L S)
    (p : A_sg_ltr_not_strictly_absorptive r b ltr) :
      @sg_ltr_not_strictly_absorptive L S := 
      SG_LTR_Not_Strictly_Absorptive(projT1 p). 

    Definition p2c_sg_ltr_strictly_absorptive_decidable
    {L S : Type} (r : brel S) (b : binary_op S) (ltr : ltr_type L S)
    (d : A_sg_ltr_strictly_absorptive_decidable r b ltr) (wL : L) (wS : S) :
      @sg_ltr_strictly_absorptive_decidable L S := 
      match d with 
      | inl p => inl (p2c_sg_ltr_strictly_absorptive r b ltr p wL wS)
      | inr p => inr (p2c_sg_ltr_not_strictly_absorptive r b ltr p) 
      end. 




    
    Definition p2c_sg_ltr_exists_id_ann_equal
      {L S : Type} (r : brel S) (b : binary_op S) (ltr : ltr_type L S)
      (p : A_sg_ltr_exists_id_ann_equal r b ltr) (wL : L) : 
      @sg_ltr_exists_id_ann_equal L S 
      := SG_LTR_Exists_Id_Ann_Equal (wL, projT1 p).

    Definition p2c_sg_ltr_exists_id_ann_not_equal
      {L S : Type} (r : brel S) (b : binary_op S) (ltr : ltr_type L S) 
      (p : A_sg_ltr_exists_id_ann_not_equal r b ltr) (wL : L) : 
      @sg_ltr_exists_id_ann_not_equal L S 
      := SG_LTR_Exists_Id_Ann_Not_Equal (wL, projT1 p).


    Definition p2c_sg_ltr_exists_id_ann_decidable 
      {L S : Type} (eq : brel S) (b : binary_op S) (ltr : ltr_type L S) 
      (P : A_sg_ltr_exists_id_ann_decidable eq b ltr) :
      @sg_ltr_exists_id_ann_decidable L S
      := match P with 
         | A_SG_LTR_Id_Ann_None _ _ _ (_, _)     => SG_LTR_Id_Ann_None
         | A_SG_LTR_Id_Ann_Id_None _ _ _ (Q, _)  => SG_LTR_Id_Ann_Id_None (projT1 Q)
         | A_SG_LTR_Id_Ann_None_Ann _ _ _ (_, Q) => SG_LTR_Id_Ann_None_Ann (projT1 Q)
         | A_SG_LTR_Id_Ann_Equal _ _ _ Q         => SG_LTR_Id_Ann_Equal (projT1 Q)
         | A_SG_LTR_Id_Ann_Not_Equal _ _ _ Q     => SG_LTR_Id_Ann_Not_Equal (projT1 Q)
         end. 

End Translation.


    
  
  

  

   

