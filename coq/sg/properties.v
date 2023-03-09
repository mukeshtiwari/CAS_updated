Require Import CAS.coq.common.compute. 

Close Scope nat. 

Section ACAS.

(* required *)   

Definition bop_congruence (S : Type) (r : brel S) (b : binary_op S) := 
   ∀ (s1 s2 t1 t2 : S), r s1 t1 = true -> r s2 t2 = true -> r (b s1 s2) (b t1 t2) = true.

Definition bop_uop_congruence (S : Type) (r : brel S) (u : unary_op S) (b : binary_op S) := 
   ∀ (s1 s2 t1 t2 : S), r (u s1) (u t1) = true -> r (u s2) (u t2) = true 
          -> r (u (b s1 s2)) (u (b t1 t2)) = true.

Definition bop_associative (S : Type) (r : brel S) (b : binary_op S) 
    := ∀ s t u : S, r (b (b s t) u) (b s (b t u)) = true. 

(* Commutativity *) 


Definition bop_commutative (S : Type) (eq : brel S) (b : binary_op S) 
    := ∀ s t : S, eq (b s t) (b t s) = true. 

Definition bop_not_commutative(S : Type) (eq : brel S) (b : binary_op S) 
    := {'(s, t) : S * S & eq (b s t) (b t s) = false}. 

Definition bop_commutative_decidable  (S : Type) (r : brel S) (b : binary_op S) := 
    (bop_commutative S r b) + (bop_not_commutative S r b). 


(* Selectivity *) 

(* bop_selective : ∀ S : Type, brel S → binary_op S → Type *) 
Definition bop_selective (S : Type) (r : brel S) (b : binary_op S) 
    := ∀ s t : S, (r (b s t) s = true) + (r (b s t) t = true).

Definition bop_not_selective (S : Type) (eq : brel S) (b : binary_op S) 
(*    := {s : S & {t : S & prod (r (b s t) s = false) (r (b s t) t = false)}}. 
    := { z : S * S & match z with (s, t) =>  (r (b s t) s = false)  * (r (b s t) t = false) end }. *) 
    := { '(s, t) : S * S &  (eq (b s t) s = false)  * (eq (b s t) t = false) }. 

Definition bop_selective_decidable  (S : Type) (r : brel S) (b : binary_op S) := 
    (bop_selective S r b) + (bop_not_selective S r b). 


(* ruptured dioids my result in idempotance *) 

Definition bop_idempotent (S : Type) (r : brel S) (b : binary_op S) 
    := ∀ s : S, r (b s s) s = true. 

Definition bop_not_idempotent (S : Type) (r : brel S) (b : binary_op S) 
    := {s : S & r (b s s) s = false}.

Definition bop_idempotent_decidable  (S : Type) (r : brel S) (b : binary_op S) := 
    (bop_idempotent S r b) + (bop_not_idempotent S r b). 


(*  

    For every universally quantified property P we might have 

          P                   not_P 
    ∀ x, P(x) = true     {x & P(x) = false } 

        anti_P                not_anti_P 
    ∀ x, P(x) = false    {x & P(x) = true } 

    For nontrivial carriers we have only three options 

    P  not_P   anti_P    not_anti_P 
   ------------------------------------------------------------
   T   F        F           T        always P 
   F   T        T           F        never P 
   F   T        F           T        sometimes P, somtimes not P 


  For every existentially quantified property P we might have 

          P                   not_P 
    {x & P(x) = true }      ∀ x, P(x) = false    

        anti_P                not_anti_P 
    {x & P(x) = false }     ∀ x, P(x) = true 

    For nontrivial carriers we have only three options 

    P  not_P   anti_P    not_anti_P 
   ------------------------------------------------------------
   T   F        F           T        always P 
   F   T        T           F        never P 
   T   F        T           F        sometimes P, somtimes not P 

   **** For now, only introduce anti_P and/or not_anti_P when needed ... 

*) 


Definition bop_is_left (S : Type) (r : brel S) (b : binary_op S) 
    := ∀ s t : S, r (b s t) s = true. 

Definition bop_not_is_left (S : Type) (r : brel S) (b : binary_op S) 
    := { z : S * S & match z with (s, t) =>  r (b s t) s = false end }. 


Definition bop_is_left_decidable  (S : Type) (r : brel S) (b : binary_op S) := 
    (bop_is_left S r b) + (bop_not_is_left S r b). 

Definition bop_is_right (S : Type) (r : brel S) (b : binary_op S) 
    := ∀ s t : S, r (b s t) t = true. 

Definition bop_not_is_right (S : Type) (r : brel S) (b : binary_op S) 
    := { z : S * S & match z with (s, t) =>  r (b s t) t = false end }. 

Definition bop_is_right_decidable  (S : Type) (r : brel S) (b : binary_op S) := 
    (bop_is_right S r b) + (bop_not_is_right S r b). 

Definition bop_anti_left (S : Type) (r : brel S) (b : binary_op S) := 
    ∀ (s t : S), r s (b s t) = false. 

Definition bop_not_anti_left (S : Type) (r : brel S) (b : binary_op S) 
   := { z : S * S & match z with (s, t) => r s (b s t) = true end }. 

Definition bop_anti_left_decidable  (S : Type) (r : brel S) (b : binary_op S) := 
    (bop_anti_left S r b) + (bop_not_anti_left S r b). 

Definition bop_anti_right (S : Type) (r : brel S) (b : binary_op S) := 
    ∀ (s t : S), r s (b t s) = false. 

Definition bop_not_anti_right (S : Type) (r : brel S) (b : binary_op S) 
   := { z : S * S & match z with (s, t) => r s (b t s) = true end }. 

Definition bop_anti_right_decidable  (S : Type) (r : brel S) (b : binary_op S) := 
    (bop_anti_right S r b) + (bop_not_anti_right S r b). 



(* IDs Annihilators 

  need LEFT and RIGHT versions? 
 *)

Definition bop_is_left_id (S : Type) (r : brel S) (b : binary_op S) (i : S) 
    := ∀ s : S, (r (b i s) s = true).

Definition bop_not_is_left_id (S : Type) (r : brel S) (b : binary_op S) (i : S)
    := {s : S & (r (b i s) s = false)}.

Definition bop_exists_left_id (S : Type) (r : brel S) (b : binary_op S) 
    := {i : S & bop_is_left_id S r b i}.

Definition bop_not_exists_left_id (S : Type) (r : brel S) (b : binary_op S) 
  := ∀ i : S, bop_not_is_left_id S r b i.



Definition bop_is_id (S : Type) (r : brel S) (b : binary_op S) (i : S) 
    := ∀ s : S, (r (b i s) s = true) * (r (b s i) s = true).

Definition bop_not_is_id (S : Type) (r : brel S) (b : binary_op S) (i : S)
    := {s : S & (r (b i s) s = false) + (r (b s i) s = false)}.

Definition bop_exists_id (S : Type) (r : brel S) (b : binary_op S) 
    := {i : S & bop_is_id S r b i}.

Definition bop_not_exists_id (S : Type) (r : brel S) (b : binary_op S) 
    := ∀ i : S, bop_not_is_id S r b i.

Definition bop_exists_id_decidable  (S : Type) (r : brel S) (b : binary_op S) := 
    (bop_exists_id S r b) + (bop_not_exists_id S r b). 

Definition bop_is_ann (S : Type) (r : brel S) (b : binary_op S) (a : S)
    :=  ∀ s : S, (r (b a s) a = true) * (r (b s a) a = true).

Definition bop_not_is_ann (S : Type) (r : brel S) (b : binary_op S) (a : S)
    := {s : S & (r (b a s) a = false) + (r (b s a) a = false)}.

Definition bop_exists_ann (S : Type) (r : brel S) (b : binary_op S) 
    := {a : S & bop_is_ann S r b a }.

Definition bop_not_exists_ann (S : Type) (r : brel S) (b : binary_op S) 
    := ∀ a : S, bop_not_is_ann S r b a. 

Definition bop_exists_ann_decidable  (S : Type) (r : brel S) (b : binary_op S) := 
    (bop_exists_ann S r b) + (bop_not_exists_ann S r b). 





(* Cancellativity *) 

Definition bop_left_cancellative (S : Type) (r : brel S) (b : binary_op S)
    := ∀ s t u : S, r (b s t) (b s u) = true -> r t u = true.

Definition bop_not_left_cancellative (S : Type) (r : brel S) (b : binary_op S)
(*    := { s : S & { t : S & { u : S & (r (b s t) (b s u) = true) * (r t u = false) }}}. *) 
   := { z : S * (S * S) & match z with (s, (t, u)) => (r (b s t) (b s u) = true) * (r t u = false) end }. 

Definition bop_left_cancellative_decidable  (S : Type) (r : brel S) (b : binary_op S) := 
    (bop_left_cancellative S r b) + (bop_not_left_cancellative S r b). 

Definition bop_right_cancellative (S : Type) (r : brel S) (b : binary_op S)
    := ∀ s t u : S, r (b t s) (b u s) = true -> r t u = true. 

Definition bop_not_right_cancellative (S : Type) (r : brel S) (b : binary_op S)
(*    := { s : S & { t : S & { u : S & (r (b t s) (b u s) = true) * (r t u = false) }}}. *) 
   := { z : S * (S * S) & match z with (s, (t, u)) =>  (r (b t s) (b u s) = true) * (r t u = false) end }. 

Definition bop_right_cancellative_decidable  (S : Type) (r : brel S) (b : binary_op S) := 
    (bop_right_cancellative S r b) + (bop_not_right_cancellative S r b). 


(* needed for Manger llex? *) 
Definition bop_left_weakly_cancellative (S : Type) (r : brel S) (b : binary_op S)
  := ∀ s t u : S, r (b s t) (b s u) = true
                  -> (r t u = true) + (bop_is_ann S r b s).

Definition bop_not_left_weakly_cancellative (S : Type) (r : brel S) (b : binary_op S)
  := { z : S * (S * S) &
           match z with (s, (t, u)) =>
                        (r (b s t) (b s u) = true)
                        *
                        (r t u = false)
                        *
                        (bop_not_is_ann S r b s)
           end }. 

Definition bop_left_weakly_cancellative_decidable
           (S : Type) (r : brel S) (b : binary_op S) := 
  (bop_left_weakly_cancellative S r b)
  +
  (bop_not_left_weakly_cancellative S r b). 


(* Condensed ("constant") *) 

Definition bop_left_constant (S : Type) (r : brel S) (b : binary_op S)
    := ∀ s t u : S, r (b s t) (b s u) = true. 

Definition bop_not_left_constant (S : Type) (r : brel S) (b : binary_op S)
(*    := { s : S & { t : S & { u : S &  r (b s t) (b s u) = false }}}. *) 
   := { z : S * (S * S) & match z with (s, (t, u)) => r (b s t) (b s u) = false  end }. 

Definition bop_left_constant_decidable  (S : Type) (r : brel S) (b : binary_op S) := 
    (bop_left_constant S r b) + (bop_not_left_constant S r b). 

Definition bop_right_constant (S : Type) (r : brel S) (b : binary_op S)
    := ∀ s t u : S, r (b t s) (b u s) = true. 

Definition bop_not_right_constant (S : Type) (r : brel S) (b : binary_op S)
(*    := { s : S & { t : S & { u : S &  r (b t s) (b u s) = false }}}. *) 
   := { z : S * (S * S) & match z with (s, (t, u)) => r (b t s) (b u s) = false end }. 

Definition bop_right_constant_decidable  (S : Type) (r : brel S) (b : binary_op S) := 
    (bop_right_constant S r b) + (bop_not_right_constant S r b). 


(* for reductions *)

Definition bop_left_uop_invariant (S : Type) (eq : brel S) (b : binary_op S) (r : unary_op S) :=
  ∀ s1 s2 : S, eq (b (r s1) s2) (b s1 s2)  = true.

Definition bop_right_uop_invariant (S : Type) (eq : brel S) (b : binary_op S) (r : unary_op S) :=
  ∀ s1 s2 : S, eq (b s1 (r s2)) (b s1 s2)  = true.

Definition bop_self_divisor (S : Type) (eqS : brel S) (bS : binary_op S) (aS : S) :=
  ∀ a b : S, eqS (bS a b) aS = true → (eqS a aS = true) + (eqS b aS = true).

Definition bop_self_square (S : Type) (eqS : brel S) (bS : binary_op S) (aS : S) :=
  ∀ a b : S, eqS (bS a b) aS = true → (eqS a aS = true) * (eqS b aS = true).

Definition pred_bop_decompose (S : Type) (P : pred S) (bS : binary_op S) 
  := ∀ (a b : S), P (bS a b) = true -> (P a = true) + (P b = true).

Definition pred_bop_weak_decompose (S : Type) (P : pred S) (bS : binary_op S) 
  := ∀ (a b : S), P (bS a b) = true -> P (bS b a) = true -> (P a = true) + (P b = true).

Definition pred_bop_compose (S : Type) (P : pred S) (bS : binary_op S) 
  := ∀ (a b : S), (P a = true) + (P b = true) -> P (bS a b) = true.

Definition pred_preserve_order (S : Type) (P : pred S) (eqS : brel S) (bS : binary_op S)
  := ∀ (a b : S), eqS (bS a b) a = true -> P a = true -> P b = true.

Definition bop_preserve_pred (S : Type) (P : pred S) (bS : binary_op S)
  := ∀ (a b : S), P a = true -> P b = true -> P (bS a b) = true.

(* for reductions *)

Definition uop_preserves_id (S : Type) (eq : brel S) (b : binary_op S) (r : unary_op S) :=
  ∀ (s : S), bop_is_id S eq b s -> eq (r s) s = true.

Definition uop_preserves_ann (S : Type) (eq : brel S) (b : binary_op S) (r : unary_op S) :=
  ∀ (s : S), bop_is_ann S eq b s -> eq (r s) s = true.


(* ********************* NEW ***********

Definition is_interesting (S : Type) (rS : brel S) (bS : binary_op S) (X : finite_set S) :=
  ∀ (s : S), in_set rS X s = true  ->
             ∀ (t : S), in_set rS X t = true ->
                   ((rS t (bS t s)= true) * (rS s (bS s t) = true))
                   +
                   ((rS t (bS t s)= false) * (rS s (bS s t) = false)). 

Definition something_is_finite (T : Type) (rS : brel T) (bS : binary_op T) 
  := {p : (list T) * (T -> T) &
          match p with (B, w) =>
                       (is_interesting T rS bS B) * 
                       (∀(s : T), (in_set rS B s = true) +
                                   ((in_set rS B (w s) = true) *
                                    ((rS (w s) (bS (w s) s) = true) *
                                     (rS s (bS s (w s)) = false))
                                   )
                       )
          end}.

Definition something_not_is_finite (T : Type) (rS : brel T) (bS : binary_op T) 
  := {F : (list T) -> T &
                       ∀ B : finite_set T, 
                         (is_interesting T rS bS B) ->
                           (in_set rS B (F B) = false) * 
                           (∀(s : T), (in_set rS B s = true) -> 
                                       ((rS s (bS s (F B)) = false) +
                                        (rS (F B) (bS (F B) s) = true))
                           )}. 

*************)
End ACAS.


Section CAS.

Inductive assert_bop_congruence {S : Type} := 
| Assert_Bop_Congruence : @assert_bop_congruence S. 

Inductive assert_associative {S : Type} := 
| Assert_Associative : assert_associative (S := S). 

Inductive assert_exists_id {S : Type} := 
| Assert_Exists_Id : S -> assert_exists_id (S := S).

Inductive assert_not_exists_id {S : Type} := 
| Assert_Not_Exists_Id : @assert_not_exists_id S.

Inductive check_exists_id {S : Type} := 
| Certify_Exists_Id : S -> check_exists_id (S := S)
| Certify_Not_Exists_Id : check_exists_id (S := S). 

Inductive assert_exists_ann {S : Type} := 
| Assert_Exists_Ann : S -> assert_exists_ann (S := S).

Inductive assert_not_exists_ann {S : Type} := 
| Assert_Not_Exists_Ann : @assert_not_exists_ann S.

Inductive check_exists_ann {S : Type} := 
| Certify_Exists_Ann : S -> check_exists_ann (S := S)
| Certify_Not_Exists_Ann : check_exists_ann (S := S). 


Inductive assert_commutative {S : Type} := 
| Assert_Commutative : assert_commutative (S := S). 

Inductive assert_not_commutative {S : Type} := 
| Assert_Not_Commutative : (S * S) → assert_not_commutative (S := S). 

Inductive check_commutative {S : Type} := 
| Certify_Commutative : check_commutative (S := S)
| Certify_Not_Commutative : (S * S) → check_commutative (S := S). 

Inductive assert_idempotent {S : Type} := 
| Assert_Idempotent : assert_idempotent (S := S). 

Inductive assert_not_idempotent {S : Type} := 
| Assert_Not_Idempotent : S → assert_not_idempotent (S := S). 

Inductive check_idempotent {S : Type} := 
| Certify_Idempotent : check_idempotent (S := S)
| Certify_Not_Idempotent : S → check_idempotent (S := S). 

Inductive assert_selective {S : Type} := 
| Assert_Selective : assert_selective (S := S). 

Inductive assert_not_selective {S : Type} := 
| Assert_Not_Selective : (S * S) → assert_not_selective (S := S). 

Inductive check_selective {S : Type} := 
| Certify_Selective : check_selective (S := S)
| Certify_Not_Selective : (S * S) → check_selective (S := S). 

Inductive assert_left_cancellative {S : Type} := 
| Assert_Left_Cancellative : assert_left_cancellative (S := S). 

Inductive assert_not_left_cancellative {S : Type} := 
| Assert_Not_Left_Cancellative : (S * (S * S)) → assert_not_left_cancellative (S := S). 

Inductive check_left_cancellative {S : Type} := 
| Certify_Left_Cancellative : check_left_cancellative (S := S)
| Certify_Not_Left_Cancellative : (S * (S * S)) → check_left_cancellative (S := S). 


Inductive assert_right_cancellative {S : Type} := 
| Assert_Right_Cancellative : assert_right_cancellative (S := S). 

Inductive assert_not_right_cancellative {S : Type} := 
| Assert_Not_Right_Cancellative : (S * (S * S)) → assert_not_right_cancellative (S := S). 

Inductive check_right_cancellative {S : Type} := 
| Certify_Right_Cancellative : check_right_cancellative (S := S)
| Certify_Not_Right_Cancellative : (S * (S * S)) → check_right_cancellative (S := S). 

Inductive assert_left_constant {S : Type} := 
| Assert_Left_Constant : assert_left_constant (S := S). 

Inductive assert_not_left_constant {S : Type} := 
| Assert_Not_Left_Constant : (S * (S * S)) → assert_not_left_constant (S := S). 

Inductive check_left_constant {S : Type} := 
| Certify_Left_Constant : check_left_constant (S := S)
| Certify_Not_Left_Constant : (S * (S * S)) → check_left_constant (S := S). 

Inductive assert_right_constant {S : Type} := 
| Assert_Right_Constant : assert_right_constant (S := S). 

Inductive assert_not_right_constant {S : Type} := 
| Assert_Not_Right_Constant : (S * (S * S)) → assert_not_right_constant (S := S). 

Inductive check_right_constant {S : Type} := 
| Certify_Right_Constant : check_right_constant (S := S)
| Certify_Not_Right_Constant : (S * (S * S)) → check_right_constant (S := S). 

Inductive assert_anti_left {S : Type} := 
| Assert_Anti_Left : assert_anti_left (S := S). 

Inductive assert_not_anti_left {S : Type} := 
| Assert_Not_Anti_Left : (S * S) → assert_not_anti_left (S := S). 

Inductive check_anti_left {S : Type} := 
| Certify_Anti_Left : check_anti_left (S := S)
| Certify_Not_Anti_Left : (S * S) → check_anti_left (S := S). 

Inductive assert_anti_right {S : Type} := 
| Assert_Anti_Right : assert_anti_right (S := S). 

Inductive assert_not_anti_right {S : Type} := 
| Assert_Not_Anti_Right : (S * S) → assert_not_anti_right (S := S). 

Inductive check_anti_right {S : Type} := 
| Certify_Anti_Right : check_anti_right (S := S)
| Certify_Not_Anti_Right : (S * S) → check_anti_right (S := S). 

Inductive check_has_2_chain {S : Type} := 
| Certify_Has_2_Chain : (S * S) → S → check_has_2_chain (S := S)
| Certify_Not_Has_2_Chain : check_has_2_chain (S := S). 

Inductive assert_not_is_left {S : Type} := 
| Assert_Not_Is_Left : (S * S) → assert_not_is_left (S := S). 

Inductive check_is_left {S : Type} := 
| Certify_Is_Left : check_is_left (S := S)
| Certify_Not_Is_Left : (S * S) → check_is_left (S := S). 

Inductive assert_not_is_right {S : Type} := 
| Assert_Not_Is_Right : (S * S) → assert_not_is_right (S := S). 

Inductive check_is_right {S : Type} := 
| Certify_Is_Right : check_is_right (S := S)
| Certify_Not_Is_Right : (S * S) → check_is_right (S := S). 

End CAS.

Section Translation.

Definition p2c_exists_id_assert : ∀ (S : Type) (r : brel S) (b : binary_op S), 
      bop_exists_id S r b -> @assert_exists_id S 
:= λ S eq b p, Assert_Exists_Id (projT1 p). 


Definition p2c_not_exists_id_assert (S : Type) (r : brel S) (b : binary_op S)  
      (P : bop_not_exists_id S r b) :  @assert_not_exists_id S 
:= Assert_Not_Exists_Id.

Definition p2c_exists_id_check : ∀ (S : Type) (r : brel S) (b : binary_op S), 
      bop_exists_id_decidable S r b -> @check_exists_id S 
:= λ S eq b d, 
   match d with 
   | inl p => Certify_Exists_Id (projT1 p)
   | inr _ => @Certify_Not_Exists_Id S 
   end. 


Definition p2c_exists_ann_assert : ∀ (S : Type) (r : brel S) (b : binary_op S), 
      bop_exists_ann S r b -> @assert_exists_ann S 
  := λ S eq b p, Assert_Exists_Ann (projT1 p).

Definition p2c_not_exists_ann_assert (S : Type) (r : brel S) (b : binary_op S)  
      (P : bop_not_exists_ann S r b) : @assert_not_exists_ann S 
:= Assert_Not_Exists_Ann. 


Definition p2c_exists_ann_check : ∀ (S : Type) (r : brel S) (b : binary_op S), 
      bop_exists_ann_decidable S r b -> @check_exists_ann S 
:= λ S eq b d, 
   match d with 
   | inl p => Certify_Exists_Ann (projT1 p)
   | inr _ => @Certify_Not_Exists_Ann S 
   end. 


Definition p2c_commutative_check : ∀ (S : Type) (r : brel S) (b : binary_op S), 
       bop_commutative_decidable S r b -> @check_commutative S 
:= λ S eq b d, 
   match d with 
   | inl _             => @Certify_Commutative S
   | inr p => Certify_Not_Commutative (projT1 p) 
   end. 


Definition p2c_idempotent_check : ∀ (S : Type) (r : brel S) (b : binary_op S), 
       bop_idempotent_decidable S r b -> @check_idempotent S 
:= λ S eq b d, 
   match d with 
   | inl _  => @Certify_Idempotent S
   | inr p  => Certify_Not_Idempotent (projT1 p) 
   end. 



Definition p2c_selective_check : ∀ (S : Type) (r : brel S) (b : binary_op S), 
       bop_selective_decidable S r b -> @check_selective S 
:= λ S eq b d, 
   match d with 
   | inl _ => @Certify_Selective S
   | inr p => Certify_Not_Selective (projT1 p)
   end.

Definition p2c_selective_assert : ∀ (S : Type) (r : brel S) (b : binary_op S), 
       bop_selective S r b -> @assert_selective S 
:= λ S eq b d, @Assert_Selective S. 

Definition p2c_not_selective_assert : ∀ (S : Type) (r : brel S) (b : binary_op S), 
       bop_not_selective S r b -> @assert_not_selective S 
:= λ S eq b d, Assert_Not_Selective (projT1 d) .


Definition p2c_is_left_check : ∀ (S : Type) (r : brel S) (b : binary_op S), 
       bop_is_left_decidable S r b -> @check_is_left S 
:= λ S eq b d, 
   match d with 
   | inl _ => @Certify_Is_Left S
   | inr p => Certify_Not_Is_Left (projT1 p) 
   end. 

Definition p2c_not_is_left : ∀ (S : Type) (r : brel S) (b : binary_op S), 
       bop_not_is_left S r b -> @assert_not_is_left S 
:= λ S eq b d, Assert_Not_Is_Left (projT1 d). 

Definition p2c_is_right_check : ∀ (S : Type) (r : brel S) (b : binary_op S), 
       bop_is_right_decidable S r b -> @check_is_right S 
:= λ S eq b d, 
   match d with 
   | inl _ => @Certify_Is_Right S
   | inr p => Certify_Not_Is_Right (projT1 p) 
   end. 

Definition p2c_not_is_right : ∀ (S : Type) (r : brel S) (b : binary_op S), 
       bop_not_is_right S r b -> @assert_not_is_right S 
:= λ S eq b d, Assert_Not_Is_Right (projT1 d). 



Definition p2c_anti_left_check : ∀ (S : Type) (r : brel S) (b : binary_op S), 
       bop_anti_left_decidable S r b -> @check_anti_left S 
:= λ S eq b d, 
   match d with 
   | inl _ => @Certify_Anti_Left S 
   | inr p => Certify_Not_Anti_Left (projT1 p)
   end. 


Definition p2c_anti_right_check : ∀ (S : Type) (r : brel S) (b : binary_op S), 
       bop_anti_right_decidable S r b -> @check_anti_right S 
:= λ S eq b d, 
   match d with 
   | inl _ => @Certify_Anti_Right S 
   | inr p => Certify_Not_Anti_Right (projT1 p) 
   end. 


Definition p2c_left_constant_check : ∀ (S : Type) (r : brel S) (b : binary_op S), 
       bop_left_constant_decidable S r b -> @check_left_constant S 
:= λ S eq b d, 
   match d with 
   | inl _ => @Certify_Left_Constant S 
   | inr p => Certify_Not_Left_Constant (projT1 p)
   end. 


Definition p2c_right_constant_check : ∀ (S : Type) (r : brel S) (b : binary_op S), 
       bop_right_constant_decidable S r b -> @check_right_constant S 
:= λ S eq b d, 
   match d with 
   | inl _ => @Certify_Right_Constant S 
   | inr p => Certify_Not_Right_Constant (projT1 p)
   end. 

Definition p2c_left_cancel_check : ∀ (S : Type) (r : brel S) (b : binary_op S), 
       bop_left_cancellative_decidable S r b -> @check_left_cancellative S 
:= λ S eq b d, 
   match d with 
   | inl _ => @Certify_Left_Cancellative S 
   | inr p => Certify_Not_Left_Cancellative (projT1 p)
   end. 

Definition p2c_right_cancel_check : ∀ (S : Type) (r : brel S) (b : binary_op S), 
       bop_right_cancellative_decidable S r b -> @check_right_cancellative S 
:= λ S eq b d, 
   match d with 
   | inl _ => @Certify_Right_Cancellative S 
   | inr p => Certify_Not_Right_Cancellative (projT1 p) 
   end. 
  
  
End Translation.   
