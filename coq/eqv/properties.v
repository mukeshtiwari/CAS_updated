
Require Import CAS.coq.common.compute. 

(*  
Set Implicit Arguments.
Unset Strict Implicit.

this seems to go "too far" often. 
I want to see the dependencies ... 
*)


Local Open Scope list_scope.

Section Compuation.

Fixpoint in_list {S : Type} (r : brel S) (l : list S) (s : S) : bool 
  := match l with 
     | nil => false 
     | a :: rest => orb (r s a) (in_list r rest s)
     end. 
End Compuation.

Section ACAS. 
Close Scope nat. 

Definition brel_not_trivial (S : Type) (r : brel S) (f : S -> S) 
    := ∀ s : S, (r s (f s) = false) * (r (f s) s = false). 

Definition brel_congruence (S : Type) (eq : brel S) (r : brel S) := 
   ∀ s t u v : S, eq s u = true → eq t v = true → r s t = r u v. 

Definition brel_reflexive (S : Type) (r : brel S) := 
    ∀ s : S, r s s = true. 

Definition brel_not_reflexive (S : Type) (r : brel S) := 
    {s : S &  r s s = false}. 

Definition brel_reflexive_decidable (S : Type) (r : brel S) := 
    (brel_reflexive S r) + (brel_not_reflexive S r). 

Definition brel_transitive (S : Type) (r : brel S) := 
    ∀ s t u: S, (r s t = true) → (r t u = true) → (r s u = true). 

Definition brel_not_transitive (S : Type) (r : brel S) 
   := { z : S * (S * S) & match z with (s, (t, u)) => (r s t = true) * (r t u = true) * (r s u = false)  end}. 

Definition brel_transitive_decidable (S : Type) (r : brel S) := 
   (brel_transitive S r) + (brel_not_transitive S r). 

Definition brel_symmetric (S : Type) (r : brel S) := 
    ∀ s t : S, (r s t = true) → (r t s = true). 

Definition brel_not_symmetric (S : Type) (r : brel S) 
(*    {s : S & {t : S & (r s t = true) * (r t s = false)}}. *) 
   := { z : S * S & match z with (s, t) =>  (r s t = true) * (r t s = false) end}. 

Definition brel_symmetric_decidable (S : Type) (r : brel S) := 
   (brel_symmetric S r) + (brel_not_symmetric S r).


(*  use this someday? 

Definition brel_rep_correct (S : Type) (eq : brel S) (r : unary_op S) := 
   ∀ s : S, eq s (r s) = true. 

Definition brel_rep_idempotent (S : Type) (eq : brel S) (r : unary_op S) := 
   ∀ s : S, eq (r (r s)) (r s) = true. 

Lemma identity_rep_correct : ∀ (S : Type) (eq : brel S), 
             brel_reflexive S eq -> brel_rep_correct S eq (@uop_id S). 
Proof. intros S eq refS s. compute. apply refS. Qed. 

Lemma identity_rep_idempotent : ∀ (S : Type) (eq : brel S), 
             brel_reflexive S eq -> brel_rep_idempotent S eq (@uop_id S). 
Proof. intros S eq refS s. compute. apply refS. Qed. 



Definition brel_has_2_chain (S : Type) (r : brel S) 
  (*  {s : S & {t : S & {u : S & (r s t = true) * (r t u = true)}}}. *) 
   := { z : S * (S * S) & match z with (s, (t, u)) =>  (r s t = true) * (r t u = true) end}. 

Definition brel_not_has_2_chain (S : Type) (r : brel S) := 
   ∀ s t u : S, r s t = true → r t u = false. 

Definition brel_has_2_chain_decidable (S : Type) (r : brel S) := 
   (brel_has_2_chain S r) + (brel_not_has_2_chain S r). 


Definition brel_bop_compatible_right (S : Type) (r : brel S) (b : binary_op S) := 
   ∀ (s u v : S), r s u = true -> r s v = true -> r s (b u v) = true.

*) 


(* brel2 *) 

Definition brel2_left_congruence (S T : Type) (r1 : brel S) (r2 : brel2 S T) := 
    ∀ (t : T) (s1 s2 : S), r1 s1 s2 = true -> r2 s1 t = r2 s2 t. 

Definition brel2_right_congruence (S T : Type) (r1 : brel T) (r2 : brel2 S T) := 
    ∀ (s : S) (t1 t2 : T), r1 t1 t2 = true -> r2 s t1 = true ->  r2 s t2 = true. 

Definition brel2_congruence (S T : Type) (rS : brel S) (rT : brel T) (r : brel2 S T) := 
    ∀ (s1 s2 : S) (t1 t2 : T), rS s1 s2 = true -> rT t1 t2 = true -> r s1 t1 = r s2 t2. 


(* bProp, pred 

   Move these to another file ... 
*) 

Definition bProp_congruence (S : Type) (eq : brel S) (P : bProp S) := 
   ∀ s t : S, eq s t = true → P s = P t. 

Definition pred_true (S : Type) (P : pred S) (s : S) 
  := P s = true. 

Definition pred_congruence (S : Type) (eq : brel S) (P : pred S) 
  := ∀ (a b : S), eq a b = true -> P a = P b.


(* needed for selectivity of bop_lift *)

Definition exactly_two (S : Type) (r : brel S) (s t : S)  
  := (r s t = false) * (∀ (a : S), (r s a = true) + (r t a = true)).

Definition brel_exactly_two (S : Type) (r : brel S) 
  := { z : S * S & match z with (s, t) =>  exactly_two S r s t end}.

Definition brel_not_exactly_two (S : Type) (r : brel S) 
  := {f : S -> (S ->S) & ∀ (s t : S), (r s t = true) + ((r s (f s t) = false) * (r t (f s t) = false))}.

Definition brel_exactly_two_decidable  (S : Type) (r : brel S):= 
    (brel_exactly_two S r) + (brel_not_exactly_two S r). 


Definition brel_at_least_three (S : Type) (r : brel S) 
  := { z : S * (S * S) &
      match z with (s, (t, u)) =>
       (r s t = false) *
       (r s u = false) *
       (r t u = false) 
      end}.


(* Needed for ann of union and id of intersect.  
   Using lists rather than sets to avoid circular dependencies (what??). 
   In future : could make this even more lazy ....
*)
Definition carrier_is_finite (S : Type) (r : brel S) := {f : unit -> list S & ∀ (s : S),  in_list r (f tt) s = true}.

Definition carrier_is_not_finite (S : Type) (r : brel S) := ∀ f : unit -> list S, {s : S &  in_list r (f tt) s = false}.

Definition carrier_is_finite_decidable  (S : Type) (r : brel S) := (carrier_is_finite S r) + (carrier_is_not_finite S r).


End ACAS. 

Section CAS.


Inductive assert_brel_congruence {S : Type} := 
| Assert_Brel_Congruence : assert_brel_congruence (S := S). 

Inductive assert_reflexive {S : Type} := 
| Assert_Reflexive : assert_reflexive (S := S). 

Inductive check_reflexive {S : Type} := 
| Certify_Reflexive : check_reflexive (S := S)
| Certify_Not_Reflexive : S → check_reflexive (S := S). 

Inductive assert_irreflexive {S : Type} := 
| Assert_Irreflexive : assert_irreflexive (S := S). 

Inductive check_irreflexive {S : Type} := 
| Certify_Irreflexive : check_irreflexive (S := S)
| Certify_Not_Irreflexive : S → check_irreflexive (S := S).  

Inductive assert_transitive {S : Type} := 
| Assert_Transitive : assert_transitive (S := S). 

Inductive check_transitive {S : Type} := 
| Certify_Transitive : check_transitive (S := S)
| Certify_Not_Transitive : (S * (S * S)) → check_transitive (S := S). 

Inductive assert_symmetric {S : Type} := 
| Assert_Symmetric : assert_symmetric (S := S). 

Inductive check_symmetric {S : Type} := 
| Certify_Symmetric : check_symmetric (S := S)
| Certify_Not_Symmetric : (S * S) → check_symmetric (S := S). 



Inductive check_exactly_two {S : Type} := 
| Certify_Exactly_Two : (S * S) → check_exactly_two (S := S)
| Certify_Not_Exactly_Two : (S -> (S -> S)) → check_exactly_two (S := S). 


Inductive check_is_finite {S : Type} := 
| Certify_Is_Finite : (unit -> list S) → check_is_finite (S := S)
| Certify_Is_Not_Finite : check_is_finite (S := S). 

End CAS.

Section Translation.

Definition p2c_exactly_two_check : ∀ (S : Type) (eq : brel S), 
       brel_exactly_two_decidable S eq -> @check_exactly_two S 
:= λ S eq d, 
   match d with
   | inl (existT _ p _) => Certify_Exactly_Two p
   | inr (existT _ f _) => Certify_Not_Exactly_Two f
   end. 


Definition p2c_is_finite_check : ∀ (S : Type) (eq : brel S), 
       carrier_is_finite_decidable S eq -> @check_is_finite S 
:= λ S eq d, 
   match d with
   | inl (existT _ p _) => Certify_Is_Finite p
   | inr _ => Certify_Is_Not_Finite 
   end. 

End Translation. 
