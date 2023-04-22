Require Import CAS.coq.common.compute.
Require Import CAS.coq.sg.properties.


Section ACAS. 



Close Scope nat. 
(* Interaction of two binary ops *)

Definition A_bs_left_distributive {S : Type} (r : brel S) (add : binary_op S) (mul : binary_op S) 
   := ∀ s t u : S, r (mul s (add t u)) (add (mul s t) (mul s u)) = true. 

Definition A_bs_not_left_distributive {S : Type} (r : brel S) (add : binary_op S) (mul : binary_op S) 
   := { '(s, (t, u)) & r (mul s (add t u)) (add (mul s t) (mul s u)) = false }. 

Definition A_bs_left_distributive_decidable {S : Type} (r : brel S) (add : binary_op S) (mul : binary_op S) 
  := (A_bs_left_distributive r add mul)
     +
     (A_bs_not_left_distributive r add mul). 

Definition A_bs_right_distributive {S : Type} (r : brel S) (add : binary_op S) (mul : binary_op S) 
    := ∀ s t u : S, r (mul (add t u) s) (add (mul t s) (mul u s)) = true. 

Definition A_bs_not_right_distributive {S : Type} (r : brel S) (add : binary_op S) (mul : binary_op S)    
   := { '(s, (t, u)) & r (mul (add t u) s) (add (mul t s) (mul u s)) = false}. 

Definition A_bs_right_distributive_decidable {S : Type} (r : brel S) (add : binary_op S) (mul : binary_op S) 
  := (A_bs_right_distributive r add mul)
     +
       (A_bs_not_right_distributive r add mul).


(* Absorptivity *) 

(* s = s + (s x t) *) 
Definition A_bs_left_absorptive {S : Type} (r : brel S) (b1 b2 : binary_op S) := 
    ∀ (s t : S), r s (b1 s (b2 s t)) = true.

Definition A_bs_not_left_absorptive {S : Type} (r : brel S) (b1 b2 : binary_op S) 
   := { z : S * S & match z with (s, t) => r s (b1 s (b2 s t)) = false end }. 

Definition A_bs_left_absorptive_decidable  {S : Type} (r : brel S) (b1 b2 : binary_op S) := 
  (A_bs_left_absorptive r b1 b2)
  +
  (A_bs_not_left_absorptive r b1 b2). 

(* s = s + (t x s) *) 
Definition A_bs_right_absorptive {S : Type} (r : brel S) (b1 b2 : binary_op S) := 
    ∀ (s t : S), r s (b1 s (b2 t s)) = true.

Definition A_bs_not_right_absorptive {S : Type} (r : brel S) (b1 b2 : binary_op S)
   := { z : S * S & match z with (s, t) => r s (b1 s (b2 t s)) = false end }. 

Definition A_bs_right_absorptive_decidable  {S : Type} (r : brel S) (b1 b2 : binary_op S) := 
  (A_bs_right_absorptive r b1 b2)
  +
  (A_bs_not_right_absorptive r b1 b2). 







(*  id-ann pairs 

   b1 id        b2 ann 
   ----------------------
1) not exists   not exists 
2)     exists   not exists 
3) not exists       exists         
4)     exists       exists   equal
5)     exists       exists   not equal

*)   



Definition A_bs_exists_id_ann_equal {S : Type} (r : brel S) (b1 : binary_op S) (b2 : binary_op S) 
  := { i : S & (bop_is_id S r b1 i) * (bop_is_ann S r b2 i)}.

Definition A_bs_exists_id_ann_not_equal {S : Type} (r : brel S) (b1 : binary_op S) (b2 : binary_op S)
  := { '(i, a) & (bop_is_id S r b1 i) * (bop_is_ann S r b2 a) * (r i a = false)}.


Definition A_extract_exist_id_from_exists_id_ann_equal {S : Type} (r : brel S) (b1 : binary_op S) (b2 : binary_op S)
           (P : A_bs_exists_id_ann_equal r b1 b2) : bop_exists_id S r b1 := 
  existT (λ x : S, bop_is_id S r b1 x) (projT1 P) (fst (projT2 P)).

Definition A_extract_exist_ann_from_exists_id_ann_equal {S : Type} (r : brel S) (b1 : binary_op S) (b2 : binary_op S)
           (P : A_bs_exists_id_ann_equal r b1 b2) : bop_exists_ann S r b2 := 
  existT (λ x : S, bop_is_ann S r b2 x) (projT1 P) (snd (projT2 P)).

Definition A_extract_exist_id_from_exists_id_ann_not_equal {S : Type} (r : brel S) (b1 : binary_op S) (b2 : binary_op S)
           (P : A_bs_exists_id_ann_not_equal r b1 b2) : bop_exists_id S r b1 :=
  match P with
  existT _ (i, a) p =>     
     existT (λ x : S, bop_is_id S r b1 x) i (fst (fst p))
  end. 

Definition A_extract_exist_ann_from_exists_id_ann_not_equal {S : Type} (r : brel S) (b1 : binary_op S) (b2 : binary_op S)
           (P : A_bs_exists_id_ann_not_equal r b1 b2) : bop_exists_ann S r b2 := 
  match P with
  existT _ (i, a) p =>     
     existT (λ x : S, bop_is_ann S r b2 x) a (snd (fst p))
  end. 


Inductive A_bs_exists_id_ann_decidable {S : Type} (eq : brel S) (b1 : binary_op S) (b2 : binary_op S)  : Type :=
| A_Id_Ann_None      : (bop_not_exists_id S eq b1) * (bop_not_exists_ann S eq b2) -> A_bs_exists_id_ann_decidable eq b1 b2
| A_Id_Ann_Id_None   : (bop_exists_id S eq b1) * (bop_not_exists_ann S eq b2)     -> A_bs_exists_id_ann_decidable eq b1 b2
| A_Id_Ann_None_Ann  : (bop_not_exists_id S eq b1) * (bop_exists_ann S eq b2)     -> A_bs_exists_id_ann_decidable eq b1 b2
| A_Id_Ann_Equal     : A_bs_exists_id_ann_equal eq b1 b2                        -> A_bs_exists_id_ann_decidable eq b1 b2
| A_Id_Ann_Not_Equal : A_bs_exists_id_ann_not_equal eq b1 b2                    -> A_bs_exists_id_ann_decidable eq b1 b2
. 

(*
Definition A_extract_exists_id_decidable_from_exists_id_ann_decidable
           {S : Type} (r : brel S) (b1 : binary_op S) (b2 : binary_op S)
           (P : A_bs_exists_id_ann_decidable r b1 b2) : bop_exists_id_decidable S r b1 :=
match P with
| A_Id_Ann_None _ _ _ (no_id, _)          => inr no_id 
| A_Id_Ann_Id_None  _ _ _ (exists_id, _ ) => inl exists_id 
| A_Id_Ann_None_Ann _ _ _ (no_id, _)      => inr no_id 
| A_Id_Ann_Equal _ _ _ id_ann_eq          => inl (A_extract_exist_id_from_exists_id_ann_equal r b1 b2 id_ann_eq) 
| A_Id_Ann_Not_Equal _ _ _ id_ann_not_eq  => inl (A_extract_exist_id_from_exists_id_ann_not_equal r b1 b2 id_ann_not_eq) 
end.

Definition A_extract_exists_ann_decidable_from_exists_id_ann_decidable
           (S : Type) (r : brel S) (b1 : binary_op S) (b2 : binary_op S)
           (P : A_bs_exists_id_ann_decidable r b1 b2) : bop_exists_ann_decidable S r b2 :=
match P with
| A_Id_Ann_None _ _ _ (_, no_ann)         => inr no_ann
| A_Id_Ann_Id_None  _ _ _ (_, no_ann)     => inr no_ann
| A_Id_Ann_None_Ann _ _ _ (_, exists_ann) => inl exists_ann
| A_Id_Ann_Equal _ _ _ id_ann_eq          => inl (A_extract_exist_ann_from_exists_id_ann_equal r b1 b2 id_ann_eq) 
| A_Id_Ann_Not_Equal _ _ _ id_ann_not_eq  => inl (A_extract_exist_ann_from_exists_id_ann_not_equal r b1 b2 id_ann_not_eq) 
end.
*) 

End ACAS. 

Section CAS.

Inductive bs_left_distributive {S : Type} := 
| BS_Left_Distributive : S -> @bs_left_distributive S. 

Inductive bs_not_left_distributive {S : Type} := 
| BS_Not_Left_Distributive : (S * (S * S)) -> @bs_not_left_distributive S.

Definition bs_left_distributive_decidable {S : Type} := 
   (@bs_left_distributive S)
   +
   (@bs_not_left_distributive S). 

Inductive bs_right_distributive {S : Type} := 
| BS_Right_Distributive : S -> @bs_right_distributive S. 

Inductive bs_not_right_distributive {S : Type} := 
| BS_Not_Right_Distributive : (S * (S * S)) -> @bs_not_right_distributive S.

Definition bs_right_distributive_decidable {S : Type} := 
   (@bs_right_distributive S)
   +
   (@bs_not_right_distributive S).


Inductive bs_left_absorptive {S : Type} := 
| BS_Left_Absorptive : S-> @bs_left_absorptive S.

Inductive bs_not_left_absorptive {S : Type} := 
| BS_Not_Left_Absorptive : (S * S) -> @bs_not_left_absorptive S.

Definition bs_left_absorptive_decidable  {S : Type} := 
  (@bs_left_absorptive S)
  +
  (@bs_not_left_absorptive S). 

Inductive bs_right_absorptive {S : Type} := 
| BS_Right_Absorptive : S -> @bs_right_absorptive S.

Inductive bs_not_right_absorptive {S : Type} := 
| BS_Not_Right_Absorptive : (S * S) -> @bs_not_right_absorptive S.

Definition bs_right_absorptive_decidable  {S : Type} := 
  (@bs_right_absorptive S)
  +
  (@bs_not_right_absorptive S). 



Inductive bs_exists_id_ann_equal {S : Type} := 
| BS_Exists_Id_Ann_Equal : S → @bs_exists_id_ann_equal S. 

Inductive bs_exists_id_ann_not_equal {S : Type} := 
| BS_Exists_Id_Ann_Not_Equal : (S * S) → @bs_exists_id_ann_not_equal S.

Inductive bs_exists_id_ann_decidable {S : Type} : Type :=
| Id_Ann_None      : @bs_exists_id_ann_decidable S
| Id_Ann_Id_None   : S -> @bs_exists_id_ann_decidable S
| Id_Ann_None_Ann  : S -> @bs_exists_id_ann_decidable S
| Id_Ann_Equal     : S -> @bs_exists_id_ann_decidable S
| Id_Ann_Not_Equal : (S * S) -> @bs_exists_id_ann_decidable S.

(*
Definition extract_exists_id_decidable_from_exists_id_ann_decidable
  {S : Type} (P : @bs_exists_id_ann_decidable S ) :
  @check_exists_id S  :=
match P with
| Id_Ann_None               => Certify_Not_Exists_Id 
| Id_Ann_Id_None id         => Certify_Exists_Id id
| Id_Ann_None_Ann ann       => Certify_Not_Exists_Id 
| Id_Ann_Equal id_ann       => Certify_Exists_Id id_ann
| Id_Ann_Not_Equal (id,ann) => Certify_Exists_Id id
end.

Definition extract_exists_ann_decidable_from_exists_id_ann_decidable
  {S : Type} (P : @bs_exists_id_ann_decidable S ) :
  @check_exists_ann S  :=
match P with
| Id_Ann_None               => Certify_Not_Exists_Ann 
| Id_Ann_Id_None id         => Certify_Not_Exists_Ann 
| Id_Ann_None_Ann ann       => Certify_Exists_Ann ann 
| Id_Ann_Equal id_ann       => Certify_Exists_Ann id_ann
| Id_Ann_Not_Equal (id,ann) => Certify_Exists_Ann ann 
end.
*) 


End CAS.

Section Translation.

    Definition p2c_bs_left_distributive
    {S : Type} (r : brel S) (w : S) (b1 b2 : binary_op S) 
    (p : A_bs_left_distributive r b1 b2) : @bs_left_distributive S := 
    BS_Left_Distributive w. 

    Definition p2c_bs_not_left_distributive
    {S : Type} (r : brel S) (b1 b2 : binary_op S) 
    (p : A_bs_not_left_distributive r b1 b2) : @bs_not_left_distributive S := 
      BS_Not_Left_Distributive(projT1 p). 

    Definition p2c_bs_left_distributive_decidable
    {S : Type} (r : brel S) (w : S) (b1 b2 : binary_op S) 
    (d : A_bs_left_distributive_decidable r b1 b2) :
      @bs_left_distributive_decidable S := 
      match d with 
      | inl p => inl (p2c_bs_left_distributive r w b1 b2 p)
      | inr p => inr (p2c_bs_not_left_distributive r b1 b2 p) 
      end. 

    Definition p2c_bs_right_distributive
    {S : Type} (r : brel S) (w : S) (b1 b2 : binary_op S) 
    (p : A_bs_right_distributive r b1 b2) : @bs_right_distributive S := 
    BS_Right_Distributive w. 

    Definition p2c_bs_not_right_distributive
    {S : Type} (r : brel S) (b1 b2 : binary_op S) 
    (p : A_bs_not_right_distributive r b1 b2) : @bs_not_right_distributive S := 
      BS_Not_Right_Distributive(projT1 p). 

    Definition p2c_bs_right_distributive_decidable
    {S : Type} (r : brel S) (w : S) (b1 b2 : binary_op S) 
    (d : A_bs_right_distributive_decidable r b1 b2) :
      @bs_right_distributive_decidable S := 
      match d with 
      | inl p => inl (p2c_bs_right_distributive r w b1 b2 p)
      | inr p => inr (p2c_bs_not_right_distributive r b1 b2 p) 
      end.

    
    Definition p2c_bs_left_absorptive
    {S : Type} (r : brel S) (w : S) (b1 b2 : binary_op S) 
    (p : A_bs_left_absorptive r b1 b2) : @bs_left_absorptive S := 
    BS_Left_Absorptive w. 

    Definition p2c_bs_not_left_absorptive
    {S : Type} (r : brel S) (b1 b2 : binary_op S) 
    (p : A_bs_not_left_absorptive r b1 b2) : @bs_not_left_absorptive S := 
      BS_Not_Left_Absorptive(projT1 p). 

    Definition p2c_bs_left_absorptive_decidable
    {S : Type} (r : brel S) (w : S) (b1 b2 : binary_op S) 
    (d : A_bs_left_absorptive_decidable r b1 b2) :
      @bs_left_absorptive_decidable S := 
      match d with 
      | inl p => inl (p2c_bs_left_absorptive r w b1 b2 p)
      | inr p => inr (p2c_bs_not_left_absorptive r b1 b2 p) 
      end. 

    Definition p2c_bs_right_absorptive
    {S : Type} (r : brel S) (w : S) (b1 b2 : binary_op S) 
    (p : A_bs_right_absorptive r b1 b2) : @bs_right_absorptive S := 
    BS_Right_Absorptive w. 

    Definition p2c_bs_not_right_absorptive
    {S : Type} (r : brel S) (b1 b2 : binary_op S) 
    (p : A_bs_not_right_absorptive r b1 b2) : @bs_not_right_absorptive S := 
      BS_Not_Right_Absorptive(projT1 p). 

    Definition p2c_bs_right_absorptive_decidable
    {S : Type} (r : brel S) (w : S) (b1 b2 : binary_op S) 
    (d : A_bs_right_absorptive_decidable r b1 b2) :
      @bs_right_absorptive_decidable S := 
      match d with 
      | inl p => inl (p2c_bs_right_absorptive r w b1 b2 p)
      | inr p => inr (p2c_bs_not_right_absorptive r b1 b2 p) 
      end. 

Definition p2c_bs_exists_id_ann_equal
  (S : Type) (r : brel S) (b1 b2 : binary_op S)
  (p : A_bs_exists_id_ann_equal r b1 b2) : 
     @bs_exists_id_ann_equal S 
:= BS_Exists_Id_Ann_Equal (projT1 p).

Definition p2c_bs_exists_id_ann_not_equal
  (S : Type) (r : brel S) (b1 b2 : binary_op S)
  (p : A_bs_exists_id_ann_not_equal r b1 b2) : 
     @bs_exists_id_ann_not_equal S 
:= BS_Exists_Id_Ann_Not_Equal (projT1 p).


Definition p2c_exists_id_ann
  (S : Type) (eq : brel S) (b1 : binary_op S) (b2 : binary_op S)
  (P : A_bs_exists_id_ann_decidable eq b1 b2) :
     @bs_exists_id_ann_decidable S
:= match P with 
| A_Id_Ann_None _ _ _ (_, _)     => Id_Ann_None
| A_Id_Ann_Id_None _ _ _ (Q, _)  => Id_Ann_Id_None (projT1 Q)
| A_Id_Ann_None_Ann _ _ _ (_, Q) => Id_Ann_None_Ann (projT1 Q)
| A_Id_Ann_Equal _ _ _ Q         => Id_Ann_Equal (projT1 Q)
| A_Id_Ann_Not_Equal _ _ _ Q     => Id_Ann_Not_Equal (projT1 Q)
end. 

End Translation.

