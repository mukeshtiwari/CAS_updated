Require Import CAS.coq.common.compute.


Section ACAS. 
Close Scope nat. 



(* a <= b -> l |> a <= l |> b *) 
Definition olt_monotone (L S : Type) (lte : brel S) (tr : ltr_type L S)  
   := ∀ (l : L)  (s t : S), lte s t = true -> lte (tr l s) (tr l t) = true. 

Definition olt_not_monotone (L S : Type) (lte : brel S) (tr : ltr_type L S)  
   := { z : L * (S * S) & match z with (l, (s, t)) => (lte s t = true) * (lte (tr l s) (tr l t) = false) end }. 

Definition olt_monotone_decidable (L S : Type) (lte : brel S) (tr : ltr_type L S)  
   := (olt_monotone L S lte tr) + (olt_not_monotone L S lte tr). 


(* a < b -> l |> a < l |> b *) 
Definition olt_strictly_monotone (L S : Type) (lte : brel S) (ltr : ltr_type L S)  
  := ∀ (l : L) (t u : S), lte t u = true -> lte u t = false ->
                  (lte (ltr l t) (ltr l u) = true) * (lte (ltr l u) (ltr l t) = false). 

Definition olt_not_strictly_monotone (L S : Type) (lte : brel S) (ltr : ltr_type L S)  
  := { z : L * (S * S) & match z with (l, (t, u)) =>
            (lte t u = true) * (lte u t = false) * ((lte (ltr l t) (ltr l u) = false) + (lte (ltr l u) (ltr l t) = true)) end }. 

Definition olt_strictly_monotone_decidable (L S : Type) (lte : brel S) (ltr : ltr_type L S)  
   := (olt_strictly_monotone L S lte ltr) + (olt_not_strictly_monotone L S lte ltr). 


(* a <= l |> a *) 
Definition olt_increasing (L S : Type) (lte : brel S) (tr : ltr_type L S)  
   := ∀ (l : L) (s : S), lte s (tr l s) = true.  

Definition olt_not_increasing (L S : Type) (lte : brel S) (tr : ltr_type L S)  
   := { z : L * S & match z with (l, s) => lte s (tr l s) = false end }. 

Definition olt_increasing_decidable (L S : Type) (lte : brel S) (tr : ltr_type L S)  
   := (olt_increasing L S lte tr) + (olt_not_increasing L S lte tr). 


(* a < l |> a *) 
Definition olt_strictly_increasing (L S : Type) (lte : brel S) (tr : ltr_type L S)  
   := ∀ (l : L) (s : S), (lte s (tr l s) = true) * (lte (tr l s) s = false). 

Definition olt_not_strictly_increasing (L S : Type) (lte : brel S) (tr : ltr_type L S)  
   := { z : L * S & match z with (l, s) => (lte s (tr l s) = false) + (lte (tr l s) s = true)  end }. 

Definition olt_strictly_increasing_decidable (L S : Type) (lte : brel S) (tr : ltr_type L S)  
   := (olt_strictly_increasing L S lte tr) + (olt_not_strictly_increasing L S lte tr). 



End ACAS. 

Section CAS.

Inductive assert_olt_monotone {L S : Type} := 
| Assert_Olt_Monotone : @assert_olt_monotone L S. 

Inductive certify_olt_monotone {L S : Type} := 
| Certify_Olt_Monotone : @certify_olt_monotone L S
| Certify_Olt_Not_Monotone : (L * (S * S)) → @certify_olt_monotone L S.  

Inductive assert_olt_strictly_monotone {L S : Type} := 
| Assert_Olt_Strictly_Monotone : @assert_olt_strictly_monotone L S. 

Inductive certify_olt_strictly_monotone {L S : Type} := 
| Certify_Olt_Strictly_Monotone : @certify_olt_strictly_monotone L S
| Certify_Olt_Not_Strictly_Monotone : (L * (S * S)) → @certify_olt_strictly_monotone L S.  

Inductive assert_olt_increasing {L S : Type} := 
| Assert_Olt_Increasing : @assert_olt_increasing L S. 

Inductive certify_olt_increasing {L S : Type} := 
| Certify_Olt_Increasing : @certify_olt_increasing L S
| Certify_Olt_Not_Increasing : (L * S) → @certify_olt_increasing L S.  

Inductive assert_olt_strictly_increasing {L S : Type} := 
| Assert_Olt_Strictly_Increasing : @assert_olt_strictly_increasing L S.

Inductive certify_olt_strictly_increasing {L S : Type} := 
| Certify_Olt_Strictly_Increasing : @certify_olt_strictly_increasing L S
| Certify_Olt_Not_Strictly_Increasing : (L * S) → @certify_olt_strictly_increasing L S.  


End CAS. 

Section Translation.

Definition p2c_olt_monotone_assert : ∀ (L S : Type) (lte : brel S) (ltr : ltr_type L S), 
       olt_monotone L S lte ltr -> @assert_olt_monotone L S 
:= λ L S lte ltr d, Assert_Olt_Monotone. 
  
Definition p2c_olt_monotone : ∀ (L S : Type) (lte : brel S) (ltr : ltr_type L S), 
       olt_monotone_decidable L S lte ltr -> @certify_olt_monotone L S 
:= λ L S lte ltr d, 
   match d with 
   | inl _ => Certify_Olt_Monotone
   | inr p => Certify_Olt_Not_Monotone (projT1 p) 
   end.


Definition p2c_olt_strictly_monotone_assert : ∀ (L S : Type) (lte : brel S) (ltr : ltr_type L S), 
       olt_strictly_monotone L S lte ltr -> @assert_olt_strictly_monotone L S 
:= λ L S lte ltr d, Assert_Olt_Strictly_Monotone. 
  
Definition p2c_olt_strictly_monotone : ∀ (L S : Type) (lte : brel S) (ltr : ltr_type L S), 
       olt_strictly_monotone_decidable L S lte ltr -> @certify_olt_strictly_monotone L S 
:= λ L S lte ltr d, 
   match d with 
   | inl _ => Certify_Olt_Strictly_Monotone
   | inr p => Certify_Olt_Not_Strictly_Monotone (projT1 p) 
   end. 

Definition p2c_olt_increasing_assert : ∀ (L S : Type) (lte : brel S) (ltr : ltr_type L S), 
       olt_increasing L S lte ltr -> @assert_olt_increasing L S 
:= λ L S lte ltr d, Assert_Olt_Increasing. 
  
Definition p2c_olt_increasing : ∀ (L S : Type) (lte : brel S) (ltr : ltr_type L S), 
       olt_increasing_decidable L S lte ltr -> @certify_olt_increasing L S 
:= λ L S lte ltr d, 
   match d with 
   | inl _ => Certify_Olt_Increasing
   | inr p => Certify_Olt_Not_Increasing (projT1 p) 
   end. 



Definition p2c_olt_strictly_increasing_assert : ∀ (L S : Type) (lte : brel S) (ltr : ltr_type L S), 
       olt_strictly_increasing L S lte ltr -> @assert_olt_strictly_increasing L S 
:= λ L S lte ltr d, Assert_Olt_Strictly_Increasing. 
  
Definition p2c_olt_strictly_increasing : ∀ (L S : Type) (lte : brel S) (ltr : ltr_type L S), 
       olt_strictly_increasing_decidable L S lte ltr -> @certify_olt_strictly_increasing L S 
:= λ L S lte ltr d, 
   match d with 
   | inl _ => Certify_Olt_Strictly_Increasing
   | inr p => Certify_Olt_Not_Strictly_Increasing (projT1 p) 
   end. 




End Translation.   
