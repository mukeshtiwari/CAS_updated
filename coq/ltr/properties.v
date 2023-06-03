Require Import CAS.coq.common.compute.

Close Scope nat_scope.       


Section ACAS. 
  
Definition A_ltr_congruence {L S : Type} (eqL : brel L) (eqS : brel S) (ltr : ltr_type L S) := 
  ∀ (l1 l2 : L) (s1 s2 : S) , eqL l1 l2 = true -> eqS s1 s2 = true -> eqS (ltr l1 s1) (ltr l2 s2) = true.

Definition A_ltr_cancellative {L S : Type} (rS : brel S) (lt : ltr_type L S) 
    := ∀ (l : L) (s1 s2 : S), rS (lt l s1) (lt l s2) = true -> rS s1 s2 = true.

Definition A_ltr_not_cancellative {L S : Type} (rS : brel S) (lt : ltr_type L S) 
   := { z : L * (S * S) & match z with (l, (s1, s2)) => (rS (lt l s1) (lt l s2) = true) * (rS s1 s2 = false) end }. 

Definition A_ltr_cancellative_decidable  {L S : Type} (rS : brel S) (lt : ltr_type L S) 
   := (A_ltr_cancellative rS lt) + (A_ltr_not_cancellative rS lt). 

Definition A_ltr_constant {L S : Type} (rS : brel S) (lt : ltr_type L S) 
    := ∀ (l : L) (s1 s2 : S), rS (lt l s1) (lt l s2) = true. 

Definition A_ltr_not_constant {L S : Type} (rS : brel S) (lt : ltr_type L S) 
   := { z : L * (S * S) & match z with (l, (s1, s2)) => rS (lt l s1) (lt l s2) = false  end }. 

Definition A_ltr_constant_decidable  {L S : Type} (rS : brel S) (lt : ltr_type L S) 
   := (A_ltr_constant rS lt) + (A_ltr_not_constant rS lt). 

Definition A_ltr_is_right {L S : Type} (rS : brel S) (lt : ltr_type L S) 
  := ∀ (l : L) (s : S), rS (lt l s) s = true.

Definition A_ltr_not_is_right {L S : Type} (rS : brel S) (lt : ltr_type L S) 
    := { z : L * S & match z with (l, s) =>  rS (lt l s) s = false end }. 

Definition A_ltr_is_right_decidable  {L S : Type} (rS : brel S) (lt : ltr_type L S) 
    := (A_ltr_is_right rS lt) + (A_ltr_not_is_right rS lt). 

Definition A_ltr_is_id {L S : Type} (rS : brel S) (lt : ltr_type L S) (l : L) 
    := ∀ s : S, (rS (lt l s) s = true).

Definition A_ltr_not_is_id {L S : Type} (rS : brel S) (lt : ltr_type L S) (l : L) 
    := {s : S & (rS (lt l s) s = false)}.

Definition A_ltr_exists_id {L S : Type} (rS : brel S) (lt : ltr_type L S) 
    := {l : L & A_ltr_is_id rS lt l}.

Definition A_ltr_not_exists_id {L S : Type} (rS : brel S) (lt : ltr_type L S) 
    := ∀ l : L, A_ltr_not_is_id rS lt l.

Definition A_ltr_exists_id_decidable {L S : Type} (rS : brel S) (lt : ltr_type L S) 
    := (A_ltr_exists_id rS lt) + (A_ltr_not_exists_id rS lt). 

Definition A_ltr_is_ann {L S : Type} (rS : brel S) (lt : ltr_type L S) (s : S) 
    := ∀ l : L, (rS (lt l s) s = true).

Definition A_ltr_not_is_ann {L S : Type} (rS : brel S) (lt : ltr_type L S) (s : S) 
    := {l : L & (rS (lt l s) s = false)}.

Definition A_ltr_exists_ann {L S : Type} (rS : brel S) (lt : ltr_type L S) 
    := {a : S & A_ltr_is_ann rS lt a}.

Definition A_ltr_not_exists_ann {L S : Type} (rS : brel S) (lt : ltr_type L S) 
    := ∀ a : S, A_ltr_not_is_ann rS lt a.

Definition A_ltr_exists_ann_decidable {L S : Type} (rS : brel S) (lt : ltr_type L S) 
    := (A_ltr_exists_ann rS lt) + (A_ltr_not_exists_ann rS lt). 


(* properties below: needed ? 

Definition A_ltr_anti_right {L S : Type} (rS : brel S) (lt : ltr_type L S) := 
    ∀ (l : L) (s : S), rS (lt l s) s = false. 

Definition A_ltr_not_anti_right {L S : Type} (rS : brel S) (lt : ltr_type L S) 
   := { z : L * S & match z with (l, s) => rS (lt l s) s = true end }. 

Definition A_ltr_anti_right_decidable  {L S : Type} (rS : brel S) (lt : ltr_type L S) := 
    (ltr_anti_right L S rS lt) + (ltr_not_anti_right L S rS lt). 

Definition A_ltr_right_cancellative {L S : Type} (rL : brel L) (rS : brel S) (lt : ltr_type L S) 
    := ∀ (l1 l2 : L) (s : S), rS (lt l1 s) (lt l2 s) = true -> rL l1 l2 = true.

Definition A_ltr_not_right_cancellative {L S : Type} (rL : brel L) (rS : brel S) (lt : ltr_type L S) 
   := { z : L * (L * S) & match z with (l1, (l2, s)) => (rS (lt l1 s) (lt l2 s) = true) * (rL l1 l2 = false) end }. 

Definition A_ltr_right_cancellative_decidable  {L S : Type} (rL : brel L) (rS : brel S) (lt : ltr_type L S) 
   := (ltr_right_cancellative L S rL rS lt) + (ltr_not_right_cancellative L S rL rS lt). 


(* Condensed ("constant") *) 


Definition A_ltr_right_constant {L S : Type} (rS : brel S) (lt : ltr_type L S) 
    := ∀ (l1 l2 : L) (s : S), rS (lt l1 s) (lt l2 s) = true.            

Definition A_ltr_not_right_constant {L S : Type} (rS : brel S) (lt : ltr_type L S) 
   := { z : L * (L * S) & match z with (l1, (l2, s)) => rS (lt l1 s) (lt l2 s) = false  end }. 

Definition A_ltr_right_constant_decidable  {L S : Type} (rS : brel S) (lt : ltr_type L S) 
   := (ltr_right_constant L S rS lt) + (ltr_not_right_constant L S rS lt). 
*) 

End ACAS. 

Section CAS.


Inductive ltr_cancellative {L S : Type} := 
| LTR_cancellative : (L * S) -> @ltr_cancellative L S. 

Inductive  ltr_not_cancellative {L S : Type} := 
| LTR_not_cancellative : (L * (S * S)) -> @ltr_not_cancellative L S. 

Definition ltr_cancellative_decidable {L S : Type} := 
   (@ltr_cancellative L S)
   +
     (@ltr_not_cancellative L S).

Inductive ltr_constant {L S : Type} := 
| LTR_constant : (L * S) -> @ltr_constant L S. 

Inductive  ltr_not_constant {L S : Type} := 
| LTR_not_constant : (L * (S * S)) -> @ltr_not_constant L S. 

Definition ltr_constant_decidable {L S : Type} := 
   (@ltr_constant L S)
   +
   (@ltr_not_constant L S). 

Inductive ltr_is_right {L S : Type} := 
| LTR_is_right : (L * S) -> @ltr_is_right L S. 

Inductive  ltr_not_is_right {L S : Type} := 
| LTR_not_is_right : (L * S) -> @ltr_not_is_right L S. 

Definition ltr_is_right_decidable {L S : Type} := 
   (@ltr_is_right L S)
   +
   (@ltr_not_is_right L S). 


Inductive ltr_exists_id {L : Type} := 
| LTR_exists_id : L -> @ltr_exists_id L. 

Inductive  ltr_not_exists_id {L : Type} := 
| LTR_not_exists_id : L -> @ltr_not_exists_id L. 

Definition ltr_exists_id_decidable {L : Type} := 
   (@ltr_exists_id L)
   +
   (@ltr_not_exists_id L). 


Inductive ltr_exists_ann {S : Type} := 
| LTR_exists_ann : S -> @ltr_exists_ann S. 

Inductive  ltr_not_exists_ann {S : Type} := 
| LTR_not_exists_ann : S -> @ltr_not_exists_ann S. 

Definition ltr_exists_ann_decidable {S : Type} := 
   (@ltr_exists_ann S)
   +
   (@ltr_not_exists_ann S). 


End CAS.

Section Translate.

Definition p2c_ltr_cancellative
    {L S : Type} (eqS : brel S) (ltr : ltr_type L S) 
    (p : A_ltr_cancellative eqS ltr) (wL : L) (wS : S) :
      @ltr_cancellative L S := 
  LTR_cancellative (wL, wS). 


Definition p2c_ltr_not_cancellative
    {L S : Type} (eqS : brel S) (ltr : ltr_type L S) 
    (p : A_ltr_not_cancellative eqS ltr) :
      @ltr_not_cancellative L S := 
  LTR_not_cancellative (projT1 p). 

Definition p2c_ltr_cancellative_decidable
    {L S : Type} (eqS : brel S) (ltr : ltr_type L S) 
    (p : A_ltr_cancellative_decidable eqS ltr) (wL : L) (wS : S) :
         @ltr_cancellative_decidable L S := 
  match p with 
  | inl c  => inl (p2c_ltr_cancellative _ _ c wL wS)
  | inr nc => inr (p2c_ltr_not_cancellative _ _ nc)
  end.


Definition p2c_ltr_constant
    {L S : Type} (eqS : brel S) (ltr : ltr_type L S) 
    (p : A_ltr_constant eqS ltr) (wL : L) (wS : S) :
      @ltr_constant L S := 
  LTR_constant (wL, wS). 


Definition p2c_ltr_not_constant
    {L S : Type} (eqS : brel S) (ltr : ltr_type L S) 
    (p : A_ltr_not_constant eqS ltr) :
      @ltr_not_constant L S := 
  LTR_not_constant (projT1 p). 

Definition p2c_ltr_constant_decidable
    {L S : Type} (eqS : brel S) (ltr : ltr_type L S) 
    (p : A_ltr_constant_decidable eqS ltr) (wL : L) (wS : S) :
         @ltr_constant_decidable L S := 
  match p with 
  | inl c  => inl (p2c_ltr_constant _ _ c wL wS)
  | inr nc => inr (p2c_ltr_not_constant _ _ nc)
  end.


Definition p2c_ltr_is_right
    {L S : Type} (eqS : brel S) (ltr : ltr_type L S) 
    (p : A_ltr_is_right eqS ltr) (wL : L) (wS : S) :
      @ltr_is_right L S := 
  LTR_is_right (wL, wS). 


Definition p2c_ltr_not_is_right
    {L S : Type} (eqS : brel S) (ltr : ltr_type L S) 
    (p : A_ltr_not_is_right eqS ltr) :
      @ltr_not_is_right L S := 
  LTR_not_is_right (projT1 p). 

Definition p2c_ltr_is_right_decidable
    {L S : Type} (eqS : brel S) (ltr : ltr_type L S) 
    (p : A_ltr_is_right_decidable eqS ltr) (wL : L) (wS : S) :
         @ltr_is_right_decidable L S := 
  match p with 
  | inl c  => inl (p2c_ltr_is_right _ _ c wL wS)
  | inr nc => inr (p2c_ltr_not_is_right _ _ nc)
  end.


Definition p2c_ltr_exists_id
    {L S : Type} (eqS : brel S) (ltr : ltr_type L S) 
    (p : A_ltr_exists_id eqS ltr) : @ltr_exists_id L := 
  LTR_exists_id (projT1 p). 

Definition p2c_ltr_not_exists_id
    {L S : Type} (eqS : brel S) (ltr : ltr_type L S) 
    (p : A_ltr_not_exists_id eqS ltr) (wL : L) : @ltr_not_exists_id L := 
  LTR_not_exists_id wL. 

Definition p2c_ltr_exists_id_decidable
    {L S : Type} (eqS : brel S) (ltr : ltr_type L S) 
    (p : A_ltr_exists_id_decidable eqS ltr) (wL : L) :
         @ltr_exists_id_decidable L := 
  match p with 
  | inl c  => inl (p2c_ltr_exists_id _ _ c)
  | inr nc => inr (p2c_ltr_not_exists_id _ _ nc wL)
  end.


Definition p2c_ltr_exists_ann
    {L S : Type} (eqS : brel S) (ltr : ltr_type L S) 
    (p : A_ltr_exists_ann eqS ltr) : @ltr_exists_ann S := 
  LTR_exists_ann (projT1 p). 

Definition p2c_ltr_not_exists_ann
    {L S : Type} (eqS : brel S) (ltr : ltr_type L S) 
    (p : A_ltr_not_exists_ann eqS ltr) (wS : S) : @ltr_not_exists_ann S := 
  LTR_not_exists_ann wS. 

Definition p2c_ltr_exists_ann_decidable
    {L S : Type} (eqS : brel S) (ltr : ltr_type L S) 
    (p : A_ltr_exists_ann_decidable eqS ltr) (wS : S) :
         @ltr_exists_ann_decidable S := 
  match p with 
  | inl c  => inl (p2c_ltr_exists_ann _ _ c)
  | inr nc => inr (p2c_ltr_not_exists_ann _ _ nc wS)
  end.


End Translate.  
