Require Import CAS.coq.common.compute.

Close Scope nat_scope.       


Section ACAS. 
  
Definition A_rtr_congruence {L S : Type} (eqL : brel L) (eqS : brel S) (rtr : rtr_type L S) := 
  ∀ (l1 l2 : L) (s1 s2 : S) , eqL l1 l2 = true -> eqS s1 s2 = true -> eqS (rtr s1 l1) (rtr s2 l2) = true.

Definition A_rtr_cancellative {L S : Type} (rS : brel S) (rtr : rtr_type L S) 
    := ∀ (l : L) (s1 s2 : S), rS (rtr s1 l) (rtr s2 l) = true -> rS s1 s2 = true.

Definition A_rtr_not_cancellative {L S : Type} (rS : brel S) (rtr : rtr_type L S) 
   := { z : L * (S * S) & match z with (l, (s1, s2)) => (rS (rtr s1 l) (rtr s2 l) = true) * (rS s1 s2 = false) end }. 

Definition A_rtr_cancellative_decidable  {L S : Type} (rS : brel S) (rtr : rtr_type L S) 
  := (A_rtr_cancellative rS rtr) + (A_rtr_not_cancellative rS rtr).

Definition A_rtr_is_left {L S : Type} (rS : brel S) (rtr : rtr_type L S) 
    := ∀ (l : L) (s : S), rS (rtr s l) s = true. 

Definition A_rtr_not_is_left {L S : Type} (rS : brel S) (rtr : rtr_type L S) 
    := { z : L * S & match z with (l, s) =>  rS (rtr s l) s = false end }. 

Definition A_rtr_is_left_decidable  {L S : Type} (rS : brel S) (rtr : rtr_type L S) 
    := (A_rtr_is_left rS rtr) + (A_rtr_not_is_left rS rtr). 

Definition A_rtr_is_id {L S : Type} (rS : brel S) (rtr : rtr_type L S) (l : L) 
    := ∀ s : S, (rS (rtr s l) s = true).

Definition A_rtr_not_is_id {L S : Type} (rS : brel S) (rtr : rtr_type L S) (l : L) 
    := {s : S & (rS (rtr s l) s = false)}.

Definition A_rtr_exists_id {L S : Type} (rS : brel S) (rtr : rtr_type L S) 
    := {l : L & A_rtr_is_id rS rtr l}.

Definition A_rtr_not_exists_id {L S : Type} (rS : brel S) (rtr : rtr_type L S) 
    := ∀ l : L, A_rtr_not_is_id rS rtr l.

Definition A_rtr_exists_id_decidable {L S : Type} (rS : brel S) (rtr : rtr_type L S) 
    := (A_rtr_exists_id rS rtr) + (A_rtr_not_exists_id rS rtr). 

Definition A_rtr_is_ann {L S : Type} (rS : brel S) (rtr : rtr_type L S) (s : S) 
    := ∀ l : L, (rS (rtr s l) s = true).

Definition A_rtr_not_is_ann {L S : Type} (rS : brel S) (rtr : rtr_type L S) (s : S) 
    := {l : L & (rS (rtr s l) s = false)}.

Definition A_rtr_exists_ann {L S : Type} (rS : brel S) (rtr : rtr_type L S) 
    := {a : S & A_rtr_is_ann rS rtr a}.

Definition A_rtr_not_exists_ann {L S : Type} (rS : brel S) (rtr : rtr_type L S) 
    := ∀ a : S, A_rtr_not_is_ann rS rtr a.

Definition A_rtr_exists_ann_decidable {L S : Type} (rS : brel S) (rtr : rtr_type L S) 
    := (A_rtr_exists_ann rS rtr) + (A_rtr_not_exists_ann rS rtr). 



End ACAS. 

Section CAS.

Inductive rtr_cancellative {L S : Type} := 
| RTR_cancellative : (L * S) -> @rtr_cancellative L S. 

Inductive  rtr_not_cancellative {L S : Type} := 
| RTR_not_cancellative : (L * (S * S)) -> @rtr_not_cancellative L S. 

Definition rtr_cancellative_decidable {L S : Type} := 
   (@rtr_cancellative L S)
   +
   (@rtr_not_cancellative L S). 


Inductive rtr_is_left {L S : Type} := 
| RTR_is_left : (L * S) -> @rtr_is_left L S. 

Inductive  rtr_not_is_left {L S : Type} := 
| RTR_not_is_left : (L * S) -> @rtr_not_is_left L S. 

Definition rtr_is_left_decidable {L S : Type} := 
   (@rtr_is_left L S)
   +
   (@rtr_not_is_left L S). 


Inductive rtr_exists_id {L : Type} := 
| RTR_exists_id : L -> @rtr_exists_id L. 

Inductive  rtr_not_exists_id {L : Type} := 
| RTR_not_exists_id : L -> @rtr_not_exists_id L. 

Definition rtr_exists_id_decidable {L : Type} := 
   (@rtr_exists_id L)
   +
   (@rtr_not_exists_id L). 


Inductive rtr_exists_ann {S : Type} := 
| RTR_exists_ann : S -> @rtr_exists_ann S. 

Inductive  rtr_not_exists_ann {S : Type} := 
| RTR_not_exists_ann : S -> @rtr_not_exists_ann S. 

Definition rtr_exists_ann_decidable {S : Type} := 
   (@rtr_exists_ann S)
   +
   (@rtr_not_exists_ann S). 


End CAS.

Section Translate.

Definition p2c_rtr_cancellative
    {L S : Type} (eqS : brel S) (ltr : rtr_type L S) 
    (p : A_rtr_cancellative eqS ltr) (wL : L) (wS : S) :
      @rtr_cancellative L S := 
  RTR_cancellative (wL, wS). 


Definition p2c_rtr_not_cancellative
    {L S : Type} (eqS : brel S) (ltr : rtr_type L S) 
    (p : A_rtr_not_cancellative eqS ltr) :
      @rtr_not_cancellative L S := 
  RTR_not_cancellative (projT1 p). 

Definition p2c_rtr_cancellative_decidable
    {L S : Type} (eqS : brel S) (ltr : rtr_type L S) 
    (p : A_rtr_cancellative_decidable eqS ltr) (wL : L) (wS : S) :
         @rtr_cancellative_decidable L S := 
  match p with 
  | inl c  => inl (p2c_rtr_cancellative _ _ c wL wS)
  | inr nc => inr (p2c_rtr_not_cancellative _ _ nc)
  end.


Definition p2c_rtr_is_left
    {L S : Type} (eqS : brel S) (ltr : rtr_type L S) 
    (p : A_rtr_is_left eqS ltr) (wL : L) (wS : S) :
      @rtr_is_left L S := 
  RTR_is_left (wL, wS). 


Definition p2c_rtr_not_is_left
    {L S : Type} (eqS : brel S) (ltr : rtr_type L S) 
    (p : A_rtr_not_is_left eqS ltr) :
      @rtr_not_is_left L S := 
  RTR_not_is_left (projT1 p). 

Definition p2c_rtr_is_left_decidable
    {L S : Type} (eqS : brel S) (ltr : rtr_type L S) 
    (p : A_rtr_is_left_decidable eqS ltr) (wL : L) (wS : S) :
         @rtr_is_left_decidable L S := 
  match p with 
  | inl c  => inl (p2c_rtr_is_left _ _ c wL wS)
  | inr nc => inr (p2c_rtr_not_is_left _ _ nc)
  end.


Definition p2c_rtr_exists_id
    {L S : Type} (eqS : brel S) (ltr : rtr_type L S) 
    (p : A_rtr_exists_id eqS ltr) : @rtr_exists_id L := 
  RTR_exists_id (projT1 p). 

Definition p2c_rtr_not_exists_id
    {L S : Type} (eqS : brel S) (ltr : rtr_type L S) 
    (p : A_rtr_not_exists_id eqS ltr) (wL : L) : @rtr_not_exists_id L := 
  RTR_not_exists_id wL. 

Definition p2c_rtr_exists_id_decidable
    {L S : Type} (eqS : brel S) (ltr : rtr_type L S) 
    (p : A_rtr_exists_id_decidable eqS ltr) (wL : L) :
         @rtr_exists_id_decidable L := 
  match p with 
  | inl c  => inl (p2c_rtr_exists_id _ _ c)
  | inr nc => inr (p2c_rtr_not_exists_id _ _ nc wL)
  end.


Definition p2c_rtr_exists_ann
    {L S : Type} (eqS : brel S) (ltr : rtr_type L S) 
    (p : A_rtr_exists_ann eqS ltr) : @rtr_exists_ann S := 
  RTR_exists_ann (projT1 p). 

Definition p2c_rtr_not_exists_ann
    {L S : Type} (eqS : brel S) (ltr : rtr_type L S) 
    (p : A_rtr_not_exists_ann eqS ltr) (wS : S) : @rtr_not_exists_ann S := 
  RTR_not_exists_ann wS. 

Definition p2c_rtr_exists_ann_decidable
    {L S : Type} (eqS : brel S) (ltr : rtr_type L S) 
    (p : A_rtr_exists_ann_decidable eqS ltr) (wS : S) :
         @rtr_exists_ann_decidable S := 
  match p with 
  | inl c  => inl (p2c_rtr_exists_ann _ _ c)
  | inr nc => inr (p2c_rtr_not_exists_ann _ _ nc wS)
  end.


End Translate.  
