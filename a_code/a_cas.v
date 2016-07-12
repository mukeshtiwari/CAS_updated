Require Import CAS.code.basic_types. 
Require Import CAS.code.ast. 
Require Import CAS.code.brel. 
Require Import CAS.code.bop. 
Require Import CAS.theory.properties. 

Require Import CAS.theory.brel_eq_nat. 
Require Import CAS.theory.brel_eq_bool. 
Require Import CAS.theory.brel_eq_list. 
Require Import CAS.theory.brel_sum.
Require Import CAS.theory.brel_product. 
Require Import CAS.theory.bop_plus. 
Require Import CAS.theory.bop_times.
Require Import CAS.theory.bop_min.
Require Import CAS.theory.bop_max. 
Require Import CAS.theory.bop_or.
Require Import CAS.theory.bop_and.
Require Import CAS.theory.bop_concat. 
Require Import CAS.theory.bop_product.

Require Import CAS.a_code.proof_records. 
Require Import CAS.a_code.construct_proofs. 
Require Import CAS.a_code.a_cas_records.
Require Import CAS.a_code.a_cast.
Require Import CAS.code.data.

(* eqv *) 

Definition A_eqv_eq_bool : A_eqv bool 
:= {| 
      A_eqv_eq     := brel_eq_bool 
    ; A_eqv_proofs := eqv_proofs_eq_bool
    ; A_eqv_data     := λ b, DATA_bool b 
    ; A_eqv_rep      := λ b, b 
    ; A_eqv_ast    := Ast_eqv_bool 
   |}. 


Definition A_eqv_eq_nat : A_eqv nat
:= {| 
      A_eqv_eq     := brel_eq_nat 
    ; A_eqv_proofs := eqv_proofs_eq_nat
    ; A_eqv_data     := λ n, DATA_nat n 
    ; A_eqv_rep      := λ b, b 
    ; A_eqv_ast    := Ast_eqv_nat
   |}. 

Definition A_eqv_add_constant : ∀ (S : Type),  A_eqv S -> cas_constant -> A_eqv (with_constant S) 
:= λ S eqvS c, 
   {| 
      A_eqv_eq     := brel_add_constant S (A_eqv_eq S eqvS) c
    ; A_eqv_proofs := eqv_proofs_add_constant S (A_eqv_eq S eqvS) c (A_eqv_proofs S eqvS)
    ; A_eqv_data   := λ d, (match d with inl s => DATA_inl(DATA_string s) | inr a => DATA_inr (A_eqv_data S eqvS a) end)
    ; A_eqv_rep    := λ d, (match d with inl s => inl _ s  | inr s => inr _ (A_eqv_rep S eqvS s) end )
    ; A_eqv_ast    := Ast_eqv_add_constant (c, A_eqv_ast S eqvS)
   |}. 

Definition A_eqv_list : ∀ (S : Type),  A_eqv S -> A_eqv (list S) 
:= λ S eqvS, 
   {| 
      A_eqv_eq     := brel_list S (A_eqv_eq S eqvS) 
    ; A_eqv_proofs := eqv_proofs_brel_list S (A_eqv_eq S eqvS) (A_eqv_proofs S eqvS)
    ; A_eqv_data   := λ l, DATA_list (List.map (A_eqv_data S eqvS) l)
    ; A_eqv_rep    := λ l, List.map (A_eqv_rep S eqvS) l
    ; A_eqv_ast    := Ast_eqv_list (A_eqv_ast S eqvS)
   |}. 


Definition A_eqv_set : ∀ (S : Type),  A_eqv S -> A_eqv (finite_set S) 
:= λ S eqvS, 
   {| 
      A_eqv_eq     := brel_set S (A_eqv_eq S eqvS) 
    ; A_eqv_proofs := eqv_proofs_brel_set S (A_eqv_eq S eqvS) (A_eqv_proofs S eqvS)
    ; A_eqv_data   := λ l, DATA_list (List.map (A_eqv_data S eqvS) l)   (* ??? *) 
    ; A_eqv_rep    := λ l, List.map (A_eqv_rep S eqvS) l                (* ??? *) 
      ; A_eqv_ast  := Ast_eqv_set (A_eqv_ast _ eqvS)
   |}. 


Definition A_eqv_product : ∀ (S T : Type),  A_eqv S -> A_eqv T -> A_eqv (S * T) 
:= λ S T eqvS eqvT, 
   {| 
     A_eqv_eq     := brel_product S T 
                           (A_eqv_eq S eqvS) 
                           (A_eqv_eq T eqvT) 
   ; A_eqv_proofs := eqv_proofs_product S T 
                           (A_eqv_eq S eqvS) 
                           (A_eqv_eq T eqvT) 
                           (A_eqv_proofs S eqvS) 
                           (A_eqv_proofs T eqvT) 
    ; A_eqv_data  := λ p, DATA_pair (A_eqv_data S eqvS (fst p), A_eqv_data T eqvT (snd p))
    ; A_eqv_rep   := λ p, (A_eqv_rep S eqvS (fst p), A_eqv_rep T eqvT (snd p))
    ; A_eqv_ast   := Ast_eqv_product (A_eqv_ast _ eqvS, A_eqv_ast _ eqvT)
   |}. 

Definition A_eqv_sum : ∀ (S T : Type),  A_eqv S -> A_eqv T -> A_eqv (S + T) 
:= λ S T eqvS eqvT, 
   {| 
     A_eqv_eq     := brel_sum S T 
                           (A_eqv_eq S eqvS) 
                           (A_eqv_eq T eqvT) 
   ; A_eqv_proofs := eqv_proofs_sum S T 
                           (A_eqv_eq S eqvS) 
                           (A_eqv_eq T eqvT) 
                           (A_eqv_proofs S eqvS) 
                           (A_eqv_proofs T eqvT) 
    ; A_eqv_data  := λ d, (match d with inl s => DATA_inl (A_eqv_data S eqvS s) | inr t => DATA_inr (A_eqv_data T eqvT t) end)
    ; A_eqv_rep   := λ d, (match d with inl s => inl _ (A_eqv_rep S eqvS s) | inr t => inr _ (A_eqv_rep T eqvT t) end)
    ; A_eqv_ast   := Ast_eqv_sum (A_eqv_ast S eqvS, A_eqv_ast T eqvT)
   |}. 


(* semigroups *) 

(* basics *) 

Definition A_sg_CS_and : A_sg_CS bool
:= {| 
     A_sg_CS_eqv         := A_eqv_eq_bool
   ; A_sg_CS_bop         := bop_and
   ; A_sg_CS_proofs      := sg_CS_proofs_and
   ; A_sg_CS_ast         := Ast_sg_CS_and 
   |}. 


Definition A_sg_CS_or : A_sg_CS bool
:= {| 
     A_sg_CS_eqv         := A_eqv_eq_bool
   ; A_sg_CS_bop         := bop_or
   ; A_sg_CS_proofs      := sg_CS_proofs_or
   ; A_sg_CS_ast         := Ast_sg_CS_or 
   |}. 

Definition A_sg_CS_min : A_sg_CS nat 
:= {| 
     A_sg_CS_eqv         := A_eqv_eq_nat 
   ; A_sg_CS_bop         := bop_min 
   ; A_sg_CS_proofs      := sg_CS_proofs_min 
   ; A_sg_CS_ast         := Ast_sg_CS_min 
   |}. 

Definition A_sg_CS_max : A_sg_CS nat 
:= {| 
     A_sg_CS_eqv         := A_eqv_eq_nat 
   ; A_sg_CS_bop         := bop_max
   ; A_sg_CS_proofs      := sg_CS_proofs_max
   ; A_sg_CS_ast         := Ast_sg_CS_max
   |}. 



Definition A_sg_C_times : A_sg_C nat 
:= {| 
     A_sg_C_eqv        := A_eqv_eq_nat 
   ; A_sg_C_bop        := bop_times
   ; A_sg_C_proofs     := sg_C_proofs_times
   ; A_sg_C_ast        := Ast_sg_C_times
   |}. 


Definition A_sg_CK_plus : A_sg_CK nat 
:= {| 
     A_sg_CK_eqv         := A_eqv_eq_nat 
   ; A_sg_CK_bop         := bop_plus
   ; A_sg_CK_proofs      := sg_CK_proofs_plus
   ; A_sg_CK_ast         := Ast_sg_CK_plus 
   |}. 



Definition A_sg_concat : ∀ (S : Type),  A_eqv S -> A_sg (list S) 
:= λ S eqvS, 
   {| 
     A_sg_eq         := A_eqv_list S eqvS
   ; A_sg_bop        := bop_concat S 
   ; A_sg_proofs     := sg_proofs_concat S (A_eqv_eq S eqvS) (A_eqv_proofs S eqvS) 
   ; A_sg_ast        := Ast_sg_concat (A_eqv_ast S eqvS)
   |}. 

Definition A_sg_left: ∀ (S : Type),  A_eqv S -> A_sg S 
:= λ S eqvS, 
   {| 
     A_sg_eq        := eqvS
   ; A_sg_bop       := bop_left S 
   ; A_sg_proofs    := sg_proofs_left S (A_eqv_eq S eqvS) (A_eqv_proofs S eqvS) 
   ; A_sg_ast       := Ast_sg_left (A_eqv_ast _ eqvS)
   |}. 


Definition A_sg_right : ∀ (S : Type),  A_eqv S -> A_sg S 
:= λ S eqvS, 
   {| 
     A_sg_eq         := eqvS
   ; A_sg_bop        := bop_right S 
   ; A_sg_proofs     := sg_proofs_right S (A_eqv_eq S eqvS) (A_eqv_proofs S eqvS) 
   ; A_sg_ast        := Ast_sg_right (A_eqv_ast _ eqvS)
   |}. 


(* semigroup add_id *) 



Definition A_sg_add_id : ∀ (S : Type) (c : cas_constant),  A_sg S -> A_sg (with_constant S) 
:= λ S c sgS, 
   {| 
     A_sg_eq        := A_eqv_add_constant S (A_sg_eq S sgS) c  
   ; A_sg_bop       := bop_add_id S (A_sg_bop S sgS) c 
   ; A_sg_proofs    := sg_proofs_add_id S (A_eqv_eq S (A_sg_eq S sgS)) c 
                                           (A_sg_bop S sgS) 
                                           (A_eqv_proofs S (A_sg_eq S sgS))
                                           (A_sg_proofs S sgS) 
   ; A_sg_ast       := Ast_sg_add_id (c, A_sg_ast S sgS)
   |}. 


Definition A_sg_C_add_id : ∀ (S : Type) (c : cas_constant),  A_sg_C S -> A_sg_C (with_constant S) 
:= λ S c sgS, 
   {| 
     A_sg_C_eqv       := A_eqv_add_constant S (A_sg_C_eqv S sgS) c  
   ; A_sg_C_bop       := bop_add_id S (A_sg_C_bop S sgS) c 
   ; A_sg_C_proofs    := sg_C_proofs_add_id S (A_eqv_eq S (A_sg_C_eqv S sgS)) c 
                                           (A_sg_C_bop S sgS) 
                                           (A_eqv_proofs S (A_sg_C_eqv S sgS))
                                           (A_sg_C_proofs S sgS) 
   ; A_sg_C_ast       := Ast_sg_C_add_id (c, A_sg_C_ast S sgS)
   |}. 


Definition A_sg_CI_add_id : ∀ (S : Type) (c : cas_constant), A_sg_CI S -> A_sg_CI (with_constant S) 
:= λ S c sgS, 
   {| 
     A_sg_CI_eqv       := A_eqv_add_constant S (A_sg_CI_eqv S sgS) c  
   ; A_sg_CI_bop       := bop_add_id S (A_sg_CI_bop S sgS) c 
   ; A_sg_CI_proofs    := sg_CI_proofs_add_id S (A_eqv_eq S (A_sg_CI_eqv S sgS)) c 
                                           (A_sg_CI_bop S sgS) 
                                           (A_eqv_proofs S (A_sg_CI_eqv S sgS))
                                           (A_sg_CI_proofs S sgS) 
   ; A_sg_CI_ast       := Ast_sg_CI_add_id (c, A_sg_CI_ast S sgS)
   |}. 


Definition A_sg_CS_add_id : ∀ (S : Type) (c : cas_constant),  A_sg_CS S -> A_sg_CS (with_constant S) 
:= λ S c sgS, 
   {| 
     A_sg_CS_eqv       := A_eqv_add_constant S (A_sg_CS_eqv S sgS) c  
   ; A_sg_CS_bop       := bop_add_id S (A_sg_CS_bop S sgS) c 
   ; A_sg_CS_proofs    := sg_CS_proofs_add_id S (A_eqv_eq S (A_sg_CS_eqv S sgS)) c 
                                           (A_sg_CS_bop S sgS) 
                                           (A_eqv_proofs S (A_sg_CS_eqv S sgS))
                                           (A_sg_CS_proofs S sgS) 
   ; A_sg_CS_ast       := Ast_sg_CS_add_id (c, A_sg_CS_ast S sgS)
   |}. 


(* semigroup add_ann *) 

Definition A_sg_add_ann : ∀ (S : Type) (c : cas_constant),  A_sg S -> A_sg (with_constant S) 
:= λ S c sgS, 
   {| 
     A_sg_eq        := A_eqv_add_constant S (A_sg_eq S sgS) c  
   ; A_sg_bop       := bop_add_ann S (A_sg_bop S sgS) c 
   ; A_sg_proofs    := sg_proofs_add_ann S (A_eqv_eq S (A_sg_eq S sgS)) c 
                                            (A_sg_bop S sgS) 
                                            (A_eqv_proofs S (A_sg_eq S sgS))
                                            (A_sg_proofs S sgS) 
   ; A_sg_ast       := Ast_sg_add_ann (c, A_sg_ast S sgS)
   |}. 


Definition A_sg_C_add_ann : ∀ (S : Type) (c : cas_constant),  A_sg_C S -> A_sg_C (with_constant S) 
:= λ S c sgS, 
   {| 
     A_sg_C_eqv       := A_eqv_add_constant S (A_sg_C_eqv S sgS) c  
   ; A_sg_C_bop       := bop_add_ann S (A_sg_C_bop S sgS) c 
   ; A_sg_C_proofs    := sg_C_proofs_add_ann S (A_eqv_eq S (A_sg_C_eqv S sgS)) c 
                                            (A_sg_C_bop S sgS) 
                                            (A_eqv_proofs S (A_sg_C_eqv S sgS))
                                            (A_sg_C_proofs S sgS) 
   ; A_sg_C_ast       := Ast_sg_C_add_ann (c, A_sg_C_ast S sgS)
   |}. 


Definition A_sg_CI_add_ann : ∀ (S : Type) (c : cas_constant),  A_sg_CI S -> A_sg_CI (with_constant S) 
:= λ S c sgS, 
   {| 
     A_sg_CI_eqv       := A_eqv_add_constant S (A_sg_CI_eqv S sgS) c  
   ; A_sg_CI_bop       := bop_add_ann S (A_sg_CI_bop S sgS) c 
   ; A_sg_CI_proofs    := sg_CI_proofs_add_ann S (A_eqv_eq S (A_sg_CI_eqv S sgS)) c 
                                            (A_sg_CI_bop S sgS) 
                                            (A_eqv_proofs S (A_sg_CI_eqv S sgS))
                                            (A_sg_CI_proofs S sgS) 
   ; A_sg_CI_ast       := Ast_sg_CI_add_ann (c, A_sg_CI_ast S sgS)
   |}. 


Definition A_sg_CS_add_ann : ∀ (S : Type) (c : cas_constant),  A_sg_CS S -> A_sg_CS (with_constant S) 
:= λ S c sgS, 
   {| 
     A_sg_CS_eqv       := A_eqv_add_constant S (A_sg_CS_eqv S sgS) c  
   ; A_sg_CS_bop       := bop_add_ann S (A_sg_CS_bop S sgS) c 
   ; A_sg_CS_proofs    := sg_CS_proofs_add_ann S (A_eqv_eq S (A_sg_CS_eqv S sgS)) c 
                                            (A_sg_CS_bop S sgS) 
                                            (A_eqv_proofs S (A_sg_CS_eqv S sgS))
                                            (A_sg_CS_proofs S sgS) 
   ; A_sg_CS_ast       := Ast_sg_CS_add_ann (c, A_sg_CS_ast S sgS)
   |}. 


(* semigroup sums *) 

Definition A_sg_left_sum : ∀ (S T : Type),  A_sg S -> A_sg T -> A_sg (S + T) 
:= λ S T sgS sgT, 
   {| 
     A_sg_eq        := A_eqv_sum S T 
                           (A_sg_eq S sgS) 
                           (A_sg_eq T sgT) 
   ; A_sg_bop       := bop_left_sum S T 
                           (A_sg_bop S sgS) 
                           (A_sg_bop T sgT) 
   ; A_sg_proofs    := sg_proofs_left_sum S T 
                           (A_eqv_eq S (A_sg_eq S sgS)) 
                           (A_eqv_eq T (A_sg_eq T sgT))
                           (A_sg_bop S sgS) 
                           (A_sg_bop T sgT) 
                           (A_eqv_proofs S (A_sg_eq S sgS)) 
                           (A_eqv_proofs T (A_sg_eq T sgT)) 
                           (A_sg_proofs S sgS) 
                           (A_sg_proofs T sgT) 
   ; A_sg_ast       := Ast_sg_left_sum (A_sg_ast S sgS, A_sg_ast T sgT)
   |}. 

Definition A_sg_right_sum : ∀ (S T : Type),  A_sg S -> A_sg T -> A_sg (S + T) 
:= λ S T sgS sgT, 
   {| 
     A_sg_eq        := A_eqv_sum S T 
                           (A_sg_eq S sgS) 
                           (A_sg_eq T sgT) 
   ; A_sg_bop       := bop_right_sum S T 
                           (A_sg_bop S sgS) 
                           (A_sg_bop T sgT) 
   ; A_sg_proofs := sg_proofs_right_sum S T 
                           (A_eqv_eq S (A_sg_eq S sgS)) 
                           (A_eqv_eq T (A_sg_eq T sgT))
                           (A_sg_bop S sgS) 
                           (A_sg_bop T sgT) 
                           (A_eqv_proofs S (A_sg_eq S sgS)) 
                           (A_eqv_proofs T (A_sg_eq T sgT)) 
                           (A_sg_proofs S sgS) 
                           (A_sg_proofs T sgT) 
   ; A_sg_ast       := Ast_sg_right_sum (A_sg_ast S sgS, A_sg_ast T sgT)
   |}. 



Definition A_sg_C_left_sum : ∀ (S T : Type),  A_sg_C S -> A_sg_C T -> A_sg_C (S + T) 
:= λ S T sgS sgT, 
   {| 
     A_sg_C_eqv       := A_eqv_sum S T 
                           (A_sg_C_eqv S sgS) 
                           (A_sg_C_eqv T sgT) 
   ; A_sg_C_bop       := bop_left_sum S T 
                           (A_sg_C_bop S sgS) 
                           (A_sg_C_bop T sgT) 
   ; A_sg_C_proofs    := sg_C_proofs_left_sum S T 
                           (A_eqv_eq S (A_sg_C_eqv S sgS)) 
                           (A_eqv_eq T (A_sg_C_eqv T sgT))
                           (A_sg_C_bop S sgS) 
                           (A_sg_C_bop T sgT) 
                           (A_eqv_proofs S (A_sg_C_eqv S sgS)) 
                           (A_eqv_proofs T (A_sg_C_eqv T sgT)) 
                           (A_sg_C_proofs S sgS) 
                           (A_sg_C_proofs T sgT) 
   ; A_sg_C_ast       := Ast_sg_C_left_sum (A_sg_C_ast S sgS, A_sg_C_ast T sgT)
   |}. 

Definition A_sg_C_right_sum : ∀ (S T : Type),  A_sg_C S -> A_sg_C T -> A_sg_C (S + T) 
:= λ S T sgS sgT, 
   {| 
     A_sg_C_eqv       := A_eqv_sum S T 
                           (A_sg_C_eqv S sgS) 
                           (A_sg_C_eqv T sgT) 
   ; A_sg_C_bop       := bop_right_sum S T 
                           (A_sg_C_bop S sgS) 
                           (A_sg_C_bop T sgT) 
   ; A_sg_C_proofs := sg_C_proofs_right_sum S T 
                           (A_eqv_eq S (A_sg_C_eqv S sgS)) 
                           (A_eqv_eq T (A_sg_C_eqv T sgT))
                           (A_sg_C_bop S sgS) 
                           (A_sg_C_bop T sgT) 
                           (A_eqv_proofs S (A_sg_C_eqv S sgS)) 
                           (A_eqv_proofs T (A_sg_C_eqv T sgT)) 
                           (A_sg_C_proofs S sgS) 
                           (A_sg_C_proofs T sgT) 
   ; A_sg_C_ast       := Ast_sg_C_right_sum (A_sg_C_ast S sgS, A_sg_C_ast T sgT)
   |}. 


Definition A_sg_CI_left_sum : ∀ (S T : Type),  A_sg_CI S -> A_sg_CI T -> A_sg_CI (S + T) 
:= λ S T sgS sgT, 
   {| 
     A_sg_CI_eqv       := A_eqv_sum S T 
                           (A_sg_CI_eqv S sgS) 
                           (A_sg_CI_eqv T sgT) 
   ; A_sg_CI_bop       := bop_left_sum S T 
                           (A_sg_CI_bop S sgS) 
                           (A_sg_CI_bop T sgT) 
   ; A_sg_CI_proofs    := sg_CI_proofs_left_sum S T 
                           (A_eqv_eq S (A_sg_CI_eqv S sgS)) 
                           (A_eqv_eq T (A_sg_CI_eqv T sgT))
                           (A_sg_CI_bop S sgS) 
                           (A_sg_CI_bop T sgT) 
                           (A_eqv_proofs S (A_sg_CI_eqv S sgS)) 
                           (A_eqv_proofs T (A_sg_CI_eqv T sgT)) 
                           (A_sg_CI_proofs S sgS) 
                           (A_sg_CI_proofs T sgT) 
   ; A_sg_CI_ast       := Ast_sg_CI_left_sum (A_sg_CI_ast S sgS, A_sg_CI_ast T sgT)
   |}. 

Definition A_sg_CI_right_sum : ∀ (S T : Type),  A_sg_CI S -> A_sg_CI T -> A_sg_CI (S + T) 
:= λ S T sgS sgT, 
   {| 
     A_sg_CI_eqv       := A_eqv_sum S T 
                           (A_sg_CI_eqv S sgS) 
                           (A_sg_CI_eqv T sgT) 
   ; A_sg_CI_bop       := bop_right_sum S T 
                           (A_sg_CI_bop S sgS) 
                           (A_sg_CI_bop T sgT) 
   ; A_sg_CI_proofs := sg_CI_proofs_right_sum S T 
                           (A_eqv_eq S (A_sg_CI_eqv S sgS)) 
                           (A_eqv_eq T (A_sg_CI_eqv T sgT))
                           (A_sg_CI_bop S sgS) 
                           (A_sg_CI_bop T sgT) 
                           (A_eqv_proofs S (A_sg_CI_eqv S sgS)) 
                           (A_eqv_proofs T (A_sg_CI_eqv T sgT)) 
                           (A_sg_CI_proofs S sgS) 
                           (A_sg_CI_proofs T sgT) 
   ; A_sg_CI_ast       := Ast_sg_CI_right_sum (A_sg_CI_ast S sgS, A_sg_CI_ast T sgT)
   |}. 


Definition A_sg_CS_left_sum : ∀ (S T : Type),  A_sg_CS S -> A_sg_CS T -> A_sg_CS (S + T) 
:= λ S T sgS sgT, 
   {| 
     A_sg_CS_eqv       := A_eqv_sum S T 
                           (A_sg_CS_eqv S sgS) 
                           (A_sg_CS_eqv T sgT) 
   ; A_sg_CS_bop       := bop_left_sum S T 
                           (A_sg_CS_bop S sgS) 
                           (A_sg_CS_bop T sgT) 
   ; A_sg_CS_proofs    := sg_CS_proofs_left_sum S T 
                           (A_eqv_eq S (A_sg_CS_eqv S sgS)) 
                           (A_eqv_eq T (A_sg_CS_eqv T sgT))
                           (A_sg_CS_bop S sgS) 
                           (A_sg_CS_bop T sgT) 
                           (A_eqv_proofs S (A_sg_CS_eqv S sgS)) 
                           (A_eqv_proofs T (A_sg_CS_eqv T sgT)) 
                           (A_sg_CS_proofs S sgS) 
                           (A_sg_CS_proofs T sgT) 
   ; A_sg_CS_ast       := Ast_sg_CS_left_sum (A_sg_CS_ast S sgS, A_sg_CS_ast T sgT)
   |}. 

Definition A_sg_CS_right_sum : ∀ (S T : Type),  A_sg_CS S -> A_sg_CS T -> A_sg_CS (S + T) 
:= λ S T sgS sgT, 
   {| 
     A_sg_CS_eqv       := A_eqv_sum S T 
                           (A_sg_CS_eqv S sgS) 
                           (A_sg_CS_eqv T sgT) 
   ; A_sg_CS_bop       := bop_right_sum S T 
                           (A_sg_CS_bop S sgS) 
                           (A_sg_CS_bop T sgT) 
   ; A_sg_CS_proofs := sg_CS_proofs_right_sum S T 
                           (A_eqv_eq S (A_sg_CS_eqv S sgS)) 
                           (A_eqv_eq T (A_sg_CS_eqv T sgT))
                           (A_sg_CS_bop S sgS) 
                           (A_sg_CS_bop T sgT) 
                           (A_eqv_proofs S (A_sg_CS_eqv S sgS)) 
                           (A_eqv_proofs T (A_sg_CS_eqv T sgT)) 
                           (A_sg_CS_proofs S sgS) 
                           (A_sg_CS_proofs T sgT) 
   ; A_sg_CS_ast       := Ast_sg_CS_right_sum (A_sg_CS_ast S sgS, A_sg_CS_ast T sgT)
   |}. 


(* semigroup products *) 

Definition A_sg_product : ∀ (S T : Type),  A_sg S -> A_sg T -> A_sg (S * T) 
:= λ S T sgS sgT, 
   {| 
     A_sg_eq        := A_eqv_product S T 
                           (A_sg_eq S sgS) 
                           (A_sg_eq T sgT) 
   ; A_sg_bop       := bop_product S T 
                           (A_sg_bop S sgS) 
                           (A_sg_bop T sgT) 
   ; A_sg_proofs := sg_proofs_product S T 
                           (A_eqv_eq S (A_sg_eq S sgS)) 
                           (A_eqv_eq T (A_sg_eq T sgT))
                           (A_sg_bop S sgS) 
                           (A_sg_bop T sgT) 
                           (A_eqv_proofs S (A_sg_eq S sgS)) 
                           (A_eqv_proofs T (A_sg_eq T sgT)) 
                           (A_sg_proofs S sgS) 
                           (A_sg_proofs T sgT) 
   ; A_sg_ast       := Ast_sg_product (A_sg_ast S sgS, A_sg_ast T sgT)
   |}. 


Definition A_sg_product_new : ∀ (S T : Type),  A_sg_new S -> A_sg_new T -> A_sg_new (S * T) 
:= λ S T sgS sgT, 
   {| 
     A_sgn_eq        := A_eqv_product S T 
                           (A_sgn_eq S sgS) 
                           (A_sgn_eq T sgT) 
   ; A_sgn_bop       := bop_product S T 
                           (A_sgn_bop S sgS) 
                           (A_sgn_bop T sgT) 
   ; A_sgn_proofs := sg_proofs_product_new S T 
                           (A_eqv_eq S (A_sgn_eq S sgS)) 
                           (A_eqv_eq T (A_sgn_eq T sgT))
                           (A_sgn_bop S sgS) 
                           (A_sgn_bop T sgT) 
                           (A_eqv_proofs S (A_sgn_eq S sgS)) 
                           (A_eqv_proofs T (A_sgn_eq T sgT)) 
                           (A_sgn_proofs S sgS) 
                           (A_sgn_proofs T sgT) 
   ; A_sgn_ast       := Ast_sg_product (A_sgn_ast S sgS, A_sgn_ast T sgT)
   |}. 


Definition A_sg_C_product : ∀ (S T : Type),  A_sg_C S -> A_sg_C T -> A_sg_C (S * T) 
:= λ S T sgS sgT, 
   {| 
     A_sg_C_eqv    := A_eqv_product S T 
                           (A_sg_C_eqv S sgS) 
                           (A_sg_C_eqv T sgT) 
   ; A_sg_C_bop       := bop_product S T 
                           (A_sg_C_bop S sgS) 
                           (A_sg_C_bop T sgT) 
   ; A_sg_C_proofs := sg_C_proofs_product S T 
                           (A_eqv_eq S (A_sg_C_eqv S sgS)) 
                           (A_eqv_eq T (A_sg_C_eqv T sgT))
                           (A_sg_C_bop S sgS) 
                           (A_sg_C_bop T sgT) 
                           (A_eqv_proofs S (A_sg_C_eqv S sgS)) 
                           (A_eqv_proofs T (A_sg_C_eqv T sgT)) 
                           (A_sg_C_proofs S sgS) 
                           (A_sg_C_proofs T sgT) 
   ; A_sg_C_ast       := Ast_sg_C_product (A_sg_C_ast S sgS, A_sg_C_ast T sgT)
   |}. 


Definition A_sg_CI_product : ∀ (S T : Type),  A_sg_CI S -> A_sg_CI T -> A_sg_CI (S * T) 
:= λ S T sgS sgT, 
   {| 
     A_sg_CI_eqv    := A_eqv_product S T 
                           (A_sg_CI_eqv S sgS) 
                           (A_sg_CI_eqv T sgT) 
   ; A_sg_CI_bop       := bop_product S T 
                           (A_sg_CI_bop S sgS) 
                           (A_sg_CI_bop T sgT) 
   ; A_sg_CI_proofs := sg_CI_proofs_product S T 
                           (A_eqv_eq S (A_sg_CI_eqv S sgS)) 
                           (A_eqv_eq T (A_sg_CI_eqv T sgT))
                           (A_sg_CI_bop S sgS) 
                           (A_sg_CI_bop T sgT) 
                           (A_eqv_proofs S (A_sg_CI_eqv S sgS)) 
                           (A_eqv_proofs T (A_sg_CI_eqv T sgT)) 
                           (A_sg_CI_proofs S sgS) 
                           (A_sg_CI_proofs T sgT) 
   ; A_sg_CI_ast       := Ast_sg_CI_product (A_sg_CI_ast S sgS, A_sg_CI_ast T sgT)
   |}. 


Definition A_sg_CK_product : ∀ (S T : Type),  A_sg_CK S -> A_sg_CK T -> A_sg_CK (S * T) 
:= λ S T sgS sgT, 
   {| 
     A_sg_CK_eqv    := A_eqv_product S T 
                           (A_sg_CK_eqv S sgS) 
                           (A_sg_CK_eqv T sgT) 
   ; A_sg_CK_bop       := bop_product S T 
                           (A_sg_CK_bop S sgS) 
                           (A_sg_CK_bop T sgT) 
   ; A_sg_CK_proofs := sg_CK_proofs_product S T 
                           (A_eqv_eq S (A_sg_CK_eqv S sgS)) 
                           (A_eqv_eq T (A_sg_CK_eqv T sgT))
                           (A_sg_CK_bop S sgS) 
                           (A_sg_CK_bop T sgT) 
                           (A_eqv_proofs S (A_sg_CK_eqv S sgS)) 
                           (A_eqv_proofs T (A_sg_CK_eqv T sgT)) 
                           (A_sg_CK_proofs S sgS) 
                           (A_sg_CK_proofs T sgT) 
   ; A_sg_CK_ast       := Ast_sg_CK_product (A_sg_CK_ast S sgS, A_sg_CK_ast T sgT)
   |}. 



(* semigroup lexicographic *) 


Definition A_sg_llex : ∀ (S T : Type),  A_sg_CS S -> A_sg T -> A_sg (S * T)
:= λ S T sgS sgT, 
      {| 
        A_sg_eq     := A_eqv_product S T (A_sg_CS_eqv S sgS) (A_sg_eq T sgT) 
      ; A_sg_bop    := bop_llex S T 
                          (A_eqv_eq S (A_sg_CS_eqv S sgS)) 
                          (A_sg_CS_bop S sgS) 
                          (A_sg_bop T sgT) 
      ; A_sg_proofs := sg_proofs_llex S T 
                          (A_eqv_eq S (A_sg_CS_eqv S sgS))
                          (A_eqv_eq T (A_sg_eq T sgT)) 
                          (A_sg_CS_bop S sgS) 
                          (A_sg_bop T sgT) 
                          (A_eqv_proofs S (A_sg_CS_eqv S sgS)) 
                          (A_eqv_proofs T (A_sg_eq T sgT))
                          (A_sg_CS_proofs S sgS) 
                          (A_sg_proofs T sgT) 
      ; A_sg_ast    := Ast_sg_llex (A_sg_CS_ast S sgS, A_sg_ast T sgT)  
      |}. 





Definition A_sg_C_llex : ∀ (S T : Type),  A_sg_CS S -> A_sg_C T -> A_sg_C (S * T)
:= λ S T sgS sgT, 
      {| 
        A_sg_C_eqv     := A_eqv_product S T (A_sg_CS_eqv S sgS) (A_sg_C_eqv T sgT) 
      ; A_sg_C_bop    := bop_llex S T 
                          (A_eqv_eq S (A_sg_CS_eqv S sgS)) 
                          (A_sg_CS_bop S sgS) 
                          (A_sg_C_bop T sgT) 
      ; A_sg_C_proofs := sg_C_proofs_llex S T 
                          (A_eqv_eq S (A_sg_CS_eqv S sgS))
                          (A_eqv_eq T (A_sg_C_eqv T sgT)) 
                          (A_sg_CS_bop S sgS) 
                          (A_sg_C_bop T sgT) 
                          (A_eqv_proofs S (A_sg_CS_eqv S sgS)) 
                          (A_eqv_proofs T (A_sg_C_eqv T sgT))
                          (A_sg_CS_proofs S sgS) 
                          (A_sg_C_proofs T sgT) 
      ; A_sg_C_ast    := Ast_sg_C_llex (A_sg_CS_ast S sgS, A_sg_C_ast T sgT)  
      |}. 



Definition A_sg_CI_llex : ∀ (S T : Type),  A_sg_CS S -> A_sg_CI T -> A_sg_CI (S * T)
:= λ S T sgS sgT, 
      {| 
        A_sg_CI_eqv     := A_eqv_product S T (A_sg_CS_eqv S sgS) (A_sg_CI_eqv T sgT) 
      ; A_sg_CI_bop    := bop_llex S T 
                          (A_eqv_eq S (A_sg_CS_eqv S sgS)) 
                          (A_sg_CS_bop S sgS) 
                          (A_sg_CI_bop T sgT) 
      ; A_sg_CI_proofs := sg_CI_proofs_llex S T 
                          (A_eqv_eq S (A_sg_CS_eqv S sgS))
                          (A_eqv_eq T (A_sg_CI_eqv T sgT)) 
                          (A_sg_CS_bop S sgS) 
                          (A_sg_CI_bop T sgT) 
                          (A_eqv_proofs S (A_sg_CS_eqv S sgS)) 
                          (A_eqv_proofs T (A_sg_CI_eqv T sgT))
                          (A_sg_CS_proofs S sgS) 
                          (A_sg_CI_proofs T sgT) 
      ; A_sg_CI_ast    := Ast_sg_CI_llex (A_sg_CS_ast S sgS, A_sg_CI_ast T sgT)  
      |}. 




Definition A_sg_CS_llex : ∀ (S T : Type),  A_sg_CS S -> A_sg_CS T -> A_sg_CS (S * T)
:= λ S T sgS sgT, 
      {| 
        A_sg_CS_eqv     := A_eqv_product S T (A_sg_CS_eqv S sgS) (A_sg_CS_eqv T sgT) 
      ; A_sg_CS_bop    := bop_llex S T 
                          (A_eqv_eq S (A_sg_CS_eqv S sgS)) 
                          (A_sg_CS_bop S sgS) 
                          (A_sg_CS_bop T sgT) 
      ; A_sg_CS_proofs := sg_CS_proofs_llex S T 
                          (A_eqv_eq S (A_sg_CS_eqv S sgS))
                          (A_eqv_eq T (A_sg_CS_eqv T sgT)) 
                          (A_sg_CS_bop S sgS) 
                          (A_sg_CS_bop T sgT) 
                          (A_eqv_proofs S (A_sg_CS_eqv S sgS)) 
                          (A_eqv_proofs T (A_sg_CS_eqv T sgT))
                          (A_sg_CS_proofs S sgS) 
                          (A_sg_CS_proofs T sgT) 
      ; A_sg_CS_ast    := Ast_sg_CS_llex (A_sg_CS_ast S sgS, A_sg_CS_ast T sgT)  
      |}. 


(* SETS *) 


Definition A_sg_CI_union_with_ann : ∀ (S : Type) (c : cas_constant),  A_eqv S -> A_sg_CI (with_constant (finite_set S)) 
:= λ S c eqvS, 
   {| 
     A_sg_CI_eqv    := A_eqv_add_constant (finite_set S) (A_eqv_set S eqvS) c  
   ; A_sg_CI_bop    := bop_add_ann (finite_set S) (bop_union S (A_eqv_eq S eqvS)) c 
   ; A_sg_CI_proofs := sg_CI_proofs_union_with_ann S (A_eqv_eq S eqvS) c (A_eqv_proofs S eqvS)
   ; A_sg_CI_ast    := Ast_sg_CI_union_with_ann (c, A_eqv_ast S eqvS)
   |}. 

Definition A_sg_CI_intersect_with_id : ∀ (S : Type) (c : cas_constant),  A_eqv S -> A_sg_CI (with_constant (finite_set S)) 
:= λ S c eqvS, 
   {| 
     A_sg_CI_eqv    := A_eqv_add_constant (finite_set S) (A_eqv_set S eqvS) c  
   ; A_sg_CI_bop    := bop_add_id (finite_set S) (bop_intersect S (A_eqv_eq S eqvS)) c 
   ; A_sg_CI_proofs := sg_CI_proofs_intersect_with_id S (A_eqv_eq S eqvS) c (A_eqv_proofs S eqvS)
   ; A_sg_CI_ast    := Ast_sg_CI_intersect_with_id (c, A_eqv_ast S eqvS)
   |}. 


(* ***************************************************
          SG SG 
* ***************************************************) 

Definition A_sg_CS_sg_CS_AD_and_or : A_sg_CS_sg_CS_AD bool := 
{|
  A_sg_CS_sg_CS_AD_eqv          := A_eqv_eq_bool
; A_sg_CS_sg_CS_AD_plus         := bop_and
; A_sg_CS_sg_CS_AD_times        := bop_or
; A_sg_CS_sg_CS_AD_plus_proofs  := sg_CS_proofs_and
; A_sg_CS_sg_CS_AD_times_proofs := sg_CS_proofs_or
; A_sg_CS_sg_CS_AD_proofs       := sg_sg_LALD_and_or_proofs 
; A_sg_CS_sg_CS_AD_ast          := Ast_sg_CS_sg_CS_AD_and_or
|}.

Definition A_sg_CS_sg_CS_AD_or_and : A_sg_CS_sg_CS_AD bool := 
{|
  A_sg_CS_sg_CS_AD_eqv          := A_eqv_eq_bool
; A_sg_CS_sg_CS_AD_plus         := bop_or
; A_sg_CS_sg_CS_AD_times        := bop_and
; A_sg_CS_sg_CS_AD_plus_proofs  := sg_CS_proofs_or
; A_sg_CS_sg_CS_AD_times_proofs := sg_CS_proofs_and
; A_sg_CS_sg_CS_AD_proofs       := sg_sg_LALD_or_and_proofs 
; A_sg_CS_sg_CS_AD_ast          := Ast_sg_CS_sg_CS_AD_or_and
|}.

Definition A_sg_CS_sg_CS_AD_max_min : A_sg_CS_sg_CS_AD nat := 
{|
  A_sg_CS_sg_CS_AD_eqv          := A_eqv_eq_nat 
; A_sg_CS_sg_CS_AD_plus         := bop_max 
; A_sg_CS_sg_CS_AD_times        := bop_min 
; A_sg_CS_sg_CS_AD_plus_proofs  := sg_CS_proofs_max  
; A_sg_CS_sg_CS_AD_times_proofs := sg_CS_proofs_min  
; A_sg_CS_sg_CS_AD_proofs       := sg_sg_LALD_max_min_proofs 
; A_sg_CS_sg_CS_AD_ast          := Ast_sg_CS_sg_CS_AD_max_min
|}.


Definition A_sg_CS_sg_CS_AD_min_max : A_sg_CS_sg_CS_AD nat := 
{|
  A_sg_CS_sg_CS_AD_eqv          := A_eqv_eq_nat 
; A_sg_CS_sg_CS_AD_plus         := bop_min 
; A_sg_CS_sg_CS_AD_times        := bop_max 
; A_sg_CS_sg_CS_AD_plus_proofs  := sg_CS_proofs_min  
; A_sg_CS_sg_CS_AD_times_proofs := sg_CS_proofs_max  
; A_sg_CS_sg_CS_AD_proofs       := sg_sg_LALD_min_max_proofs 
; A_sg_CS_sg_CS_AD_ast          := Ast_sg_CS_sg_CS_AD_min_max
|}.

(* min plus *) 
Definition A_sg_CS_sg_CK_AD_min_plus : A_sg_CS_sg_CK_AD nat := 
{|
  A_sg_CS_sg_CK_AD_eqv          := A_eqv_eq_nat 
; A_sg_CS_sg_CK_AD_plus         := bop_min 
; A_sg_CS_sg_CK_AD_times        := bop_plus
; A_sg_CS_sg_CK_AD_plus_proofs  := sg_CS_proofs_min  
; A_sg_CS_sg_CK_AD_times_proofs := sg_CK_proofs_plus
; A_sg_CS_sg_CK_AD_proofs       := sg_sg_LALD_min_plus_proofs 
; A_sg_CS_sg_CK_AD_ast          := Ast_sg_CS_sg_CK_AD_min_plus
|}.


(* max plus *) 
Definition A_sg_CS_sg_CK_D_max_plus : A_sg_CS_sg_CK_D nat := 
{|
  A_sg_CS_sg_CK_D_eqv          := A_eqv_eq_nat 
; A_sg_CS_sg_CK_D_plus         := bop_max
; A_sg_CS_sg_CK_D_times        := bop_plus
; A_sg_CS_sg_CK_D_plus_proofs  := sg_CS_proofs_max
; A_sg_CS_sg_CK_D_times_proofs := sg_CK_proofs_plus
; A_sg_CS_sg_CK_D_proofs       := sg_sg_LD_max_plus_proofs 
; A_sg_CS_sg_CK_D_ast          := Ast_sg_CS_sg_CK_D_max_plus
|}.


Definition A_sg_sg_product : ∀ (S T : Type),  A_sg_sg S -> A_sg_sg T -> A_sg_sg (S * T) 
:= λ S T sg_sgS sg_sgT, 
{| 
     A_sg_sg_eqv        := A_eqv_product S T 
                           (A_sg_sg_eqv S sg_sgS) 
                           (A_sg_sg_eqv T sg_sgT) 
   ; A_sg_sg_plus       := bop_product S T 
                           (A_sg_sg_plus S sg_sgS) 
                           (A_sg_sg_plus T sg_sgT) 
   ; A_sg_sg_times       := bop_product S T 
                           (A_sg_sg_times S sg_sgS) 
                           (A_sg_sg_times T sg_sgT) 
   ; A_sg_sg_plus_proofs := sg_proofs_product S T 
                           (A_eqv_eq S (A_sg_sg_eqv S sg_sgS)) 
                           (A_eqv_eq T (A_sg_sg_eqv T sg_sgT))
                           (A_sg_sg_plus S sg_sgS) 
                           (A_sg_sg_plus T sg_sgT) 
                           (A_eqv_proofs S (A_sg_sg_eqv S sg_sgS)) 
                           (A_eqv_proofs T (A_sg_sg_eqv T sg_sgT)) 
                           (A_sg_sg_plus_proofs S sg_sgS) 
                           (A_sg_sg_plus_proofs T sg_sgT) 
   ; A_sg_sg_times_proofs := sg_proofs_product S T 
                           (A_eqv_eq S (A_sg_sg_eqv S sg_sgS)) 
                           (A_eqv_eq T (A_sg_sg_eqv T sg_sgT))
                           (A_sg_sg_times S sg_sgS) 
                           (A_sg_sg_times T sg_sgT) 
                           (A_eqv_proofs S (A_sg_sg_eqv S sg_sgS)) 
                           (A_eqv_proofs T (A_sg_sg_eqv T sg_sgT)) 
                           (A_sg_sg_times_proofs S sg_sgS) 
                           (A_sg_sg_times_proofs T sg_sgT) 
   ; A_sg_sg_proofs    := sg_sg_proofs_product S T 
                           (A_eqv_eq S (A_sg_sg_eqv S sg_sgS)) 
                           (A_eqv_eq T (A_sg_sg_eqv T sg_sgT))
                           (A_sg_sg_plus S sg_sgS) 
                           (A_sg_sg_times S sg_sgS) 
                           (A_sg_sg_plus T sg_sgT) 
                           (A_sg_sg_times T sg_sgT) 
                           (A_eqv_proofs S (A_sg_sg_eqv S sg_sgS)) 
                           (A_eqv_proofs T (A_sg_sg_eqv T sg_sgT)) 
                           (A_sg_sg_proofs S sg_sgS) 
                           (A_sg_sg_proofs T sg_sgT) 
   ; A_sg_sg_ast        := Ast_sg_sg_product(A_sg_sg_ast S sg_sgS, A_sg_sg_ast T sg_sgT)
|}. 



Definition A_sg_sg_add_zero : ∀ (S : Type),  A_sg_sg S -> cas_constant -> A_sg_sg (with_constant S) 
:= λ S sg_sgS c, 
{| 
     A_sg_sg_eqv          := A_eqv_add_constant S (A_sg_sg_eqv S sg_sgS) c 
   ; A_sg_sg_plus         := bop_add_id S (A_sg_sg_plus S sg_sgS) c
   ; A_sg_sg_times        := bop_add_ann S (A_sg_sg_times S sg_sgS) c
   ; A_sg_sg_plus_proofs  := sg_proofs_add_id S 
                                (A_eqv_eq S (A_sg_sg_eqv S sg_sgS)) c 
                                (A_sg_sg_plus S sg_sgS) 
                                (A_eqv_proofs S (A_sg_sg_eqv S sg_sgS)) 
                                (A_sg_sg_plus_proofs S sg_sgS) 
   ; A_sg_sg_times_proofs := sg_proofs_add_ann S 
                                (A_eqv_eq S (A_sg_sg_eqv S sg_sgS)) c 
                                (A_sg_sg_times S sg_sgS)  
                                (A_eqv_proofs S (A_sg_sg_eqv S sg_sgS)) 
                                (A_sg_sg_times_proofs S sg_sgS) 
   ; A_sg_sg_proofs       := sg_sg_proofs_add_zero S _ c 
                                (A_sg_sg_plus S sg_sgS) 
                                (A_sg_sg_times S sg_sgS)  
                                (A_eqv_proofs S (A_sg_sg_eqv S sg_sgS)) 
                                (A_sg_sg_proofs S sg_sgS)
   ; A_sg_sg_ast          := Ast_sg_sg_add_zero (c, A_sg_sg_ast S sg_sgS)
|}. 


Definition A_sg_CS_sg_add_zero : ∀ (S : Type),  A_sg_CS_sg S -> cas_constant -> A_sg_CS_sg (with_constant S) 
:= λ S sg_sgS c, 
{| 
     A_sg_CS_sg_eqv          := A_eqv_add_constant S (A_sg_CS_sg_eqv S sg_sgS) c 
   ; A_sg_CS_sg_plus         := bop_add_id S (A_sg_CS_sg_plus S sg_sgS) c
   ; A_sg_CS_sg_times        := bop_add_ann S (A_sg_CS_sg_times S sg_sgS) c
   ; A_sg_CS_sg_plus_proofs  := sg_CS_proofs_add_id S 
                                (A_eqv_eq S (A_sg_CS_sg_eqv S sg_sgS)) c 
                                (A_sg_CS_sg_plus S sg_sgS) 
                                (A_eqv_proofs S (A_sg_CS_sg_eqv S sg_sgS)) 
                                (A_sg_CS_sg_plus_proofs S sg_sgS) 
   ; A_sg_CS_sg_times_proofs := sg_proofs_add_ann S 
                                (A_eqv_eq S (A_sg_CS_sg_eqv S sg_sgS)) c 
                                (A_sg_CS_sg_times S sg_sgS)  
                                (A_eqv_proofs S (A_sg_CS_sg_eqv S sg_sgS)) 
                                (A_sg_CS_sg_times_proofs S sg_sgS) 
   ; A_sg_CS_sg_proofs       := sg_sg_proofs_add_zero S _ c 
                                (A_sg_CS_sg_plus S sg_sgS) 
                                (A_sg_CS_sg_times S sg_sgS)  
                                (A_eqv_proofs S (A_sg_CS_sg_eqv S sg_sgS)) 
                                (A_sg_CS_sg_proofs S sg_sgS)
   ; A_sg_CS_sg_ast          := Ast_sg_CS_sg_add_zero (c, A_sg_CS_sg_ast S sg_sgS)
|}. 


(*
Someday get rid of need for C ... 

Definition A_sg_sg_add_one : ∀ (S : Type),  A_sg_sg S -> cas_constant -> A_sg_sg (with_constant S) 
:= λ S sg_sgS c, 
{| 
     A_sg_sg_eqv          := A_eqv_add_constant S (A_sg_sg_eqv S sg_sgS) c 
   ; A_sg_sg_plus         := bop_add_ann S (A_sg_sg_plus S sg_sgS) c
   ; A_sg_sg_times        := bop_add_id S (A_sg_sg_times S sg_sgS) c
   ; A_sg_sg_plus_proofs  := sg_proofs_add_ann S 
                                (A_eqv_eq S (A_sg_sg_eqv S sg_sgS)) c 
                                (A_sg_sg_plus S sg_sgS) 
                                (A_eqv_proofs S (A_sg_sg_eqv S sg_sgS)) 
                                (A_sg_sg_plus_proofs S sg_sgS) 
   ; A_sg_sg_times_proofs := sg_proofs_add_id S 
                                (A_eqv_eq S (A_sg_sg_eqv S sg_sgS)) c 
                                (A_sg_sg_times S sg_sgS)  
                                (A_eqv_proofs S (A_sg_sg_eqv S sg_sgS)) 
                                (A_sg_sg_times_proofs S sg_sgS) 
   ; A_sg_sg_proofs       := sg_sg_proofs_add_one S _ c 
                                (A_sg_sg_plus S sg_sgS) 
                                (A_sg_sg_times S sg_sgS)  
                                (A_eqv_proofs S (A_sg_sg_eqv S sg_sgS)) 
                                (A_sg_sg_plus_proofs S sg_sgS) 
                                (A_sg_sg_proofs S sg_sgS)
   ; A_sg_sg_ast          := Ast_sg_sg_add_one (c, A_sg_sg_ast S sg_sgS)
|}. 

*) 

Definition A_sg_C_sg_add_one : ∀ (S : Type),  A_sg_C_sg S -> cas_constant -> A_sg_C_sg (with_constant S) 
:= λ S sg_sgS c, 
{| 
     A_sg_C_sg_eqv          := A_eqv_add_constant S (A_sg_C_sg_eqv S sg_sgS) c 
   ; A_sg_C_sg_plus         := bop_add_ann S (A_sg_C_sg_plus S sg_sgS) c
   ; A_sg_C_sg_times        := bop_add_id S (A_sg_C_sg_times S sg_sgS) c
   ; A_sg_C_sg_plus_proofs  := sg_C_proofs_add_ann S 
                                (A_eqv_eq S (A_sg_C_sg_eqv S sg_sgS)) c 
                                (A_sg_C_sg_plus S sg_sgS) 
                                (A_eqv_proofs S (A_sg_C_sg_eqv S sg_sgS)) 
                                (A_sg_C_sg_plus_proofs S sg_sgS) 
   ; A_sg_C_sg_times_proofs := sg_proofs_add_id S 
                                (A_eqv_eq S (A_sg_C_sg_eqv S sg_sgS)) c 
                                (A_sg_C_sg_times S sg_sgS)  
                                (A_eqv_proofs S (A_sg_C_sg_eqv S sg_sgS)) 
                                (A_sg_C_sg_times_proofs S sg_sgS) 
   ; A_sg_C_sg_proofs       := sg_sg_proofs_add_one S _ c 
                                (A_sg_C_sg_plus S sg_sgS) 
                                (A_sg_C_sg_times S sg_sgS)  
                                (A_eqv_proofs S (A_sg_C_sg_eqv S sg_sgS)) 
                                (A_sg_C_sg_plus_proofs S sg_sgS) 
                                (A_sg_C_sg_proofs S sg_sgS)
   ; A_sg_C_sg_ast          := Ast_sg_C_sg_add_one (c, A_sg_C_sg_ast S sg_sgS)
|}. 

Definition A_sg_CS_sg_add_one : ∀ (S : Type),  A_sg_CS_sg S -> cas_constant -> A_sg_CS_sg (with_constant S) 
:= λ S sg_sgS c, 
{| 
     A_sg_CS_sg_eqv          := A_eqv_add_constant S (A_sg_CS_sg_eqv S sg_sgS) c 
   ; A_sg_CS_sg_plus         := bop_add_ann S (A_sg_CS_sg_plus S sg_sgS) c
   ; A_sg_CS_sg_times        := bop_add_id S (A_sg_CS_sg_times S sg_sgS) c
   ; A_sg_CS_sg_plus_proofs  := sg_CS_proofs_add_ann S 
                                (A_eqv_eq S (A_sg_CS_sg_eqv S sg_sgS)) c 
                                (A_sg_CS_sg_plus S sg_sgS) 
                                (A_eqv_proofs S (A_sg_CS_sg_eqv S sg_sgS)) 
                                (A_sg_CS_sg_plus_proofs S sg_sgS) 
   ; A_sg_CS_sg_times_proofs := sg_proofs_add_id S 
                                (A_eqv_eq S (A_sg_CS_sg_eqv S sg_sgS)) c 
                                (A_sg_CS_sg_times S sg_sgS)  
                                (A_eqv_proofs S (A_sg_CS_sg_eqv S sg_sgS)) 
                                (A_sg_CS_sg_times_proofs S sg_sgS) 
   ; A_sg_CS_sg_proofs       := sg_CS_sg_proofs_add_one S _ c 
                                (A_sg_CS_sg_plus S sg_sgS) 
                                (A_sg_CS_sg_times S sg_sgS)  
                                (A_eqv_proofs S (A_sg_CS_sg_eqv S sg_sgS)) 
                                (A_sg_CS_sg_plus_proofs S sg_sgS) 
                                (A_sg_CS_sg_proofs S sg_sgS)
   ; A_sg_CS_sg_ast          := Ast_sg_CS_sg_add_one (c, A_sg_CS_sg_ast S sg_sgS)
|}. 







Definition A_sg_C_sg_llex : ∀ (S T : Type),  A_sg_CS_sg S -> A_sg_C_sg T -> A_sg_C_sg (S * T) 
:= λ S T sg_sgS sg_sgT, 
{| 
     A_sg_C_sg_eqv        := A_eqv_product S T 
                           (A_sg_CS_sg_eqv S sg_sgS) 
                           (A_sg_C_sg_eqv T sg_sgT) 
   ; A_sg_C_sg_plus       := bop_llex S T 
                           (A_eqv_eq S (A_sg_CS_sg_eqv S sg_sgS)) 
                           (A_sg_CS_sg_plus S sg_sgS) 
                           (A_sg_C_sg_plus T sg_sgT) 
   ; A_sg_C_sg_times       := bop_product S T 
                           (A_sg_CS_sg_times S sg_sgS) 
                           (A_sg_C_sg_times T sg_sgT) 
   ; A_sg_C_sg_plus_proofs := sg_C_proofs_llex S T 
                           (A_eqv_eq S (A_sg_CS_sg_eqv S sg_sgS)) 
                           (A_eqv_eq T (A_sg_C_sg_eqv T sg_sgT))
                           (A_sg_CS_sg_plus S sg_sgS) 
                           (A_sg_C_sg_plus T sg_sgT) 
                           (A_eqv_proofs S (A_sg_CS_sg_eqv S sg_sgS)) 
                           (A_eqv_proofs T (A_sg_C_sg_eqv T sg_sgT)) 
                           (A_sg_CS_sg_plus_proofs S sg_sgS) 
                           (A_sg_C_sg_plus_proofs T sg_sgT) 
   ; A_sg_C_sg_times_proofs := sg_proofs_product S T 
                           (A_eqv_eq S (A_sg_CS_sg_eqv S sg_sgS)) 
                           (A_eqv_eq T (A_sg_C_sg_eqv T sg_sgT))
                           (A_sg_CS_sg_times S sg_sgS) 
                           (A_sg_C_sg_times T sg_sgT) 
                           (A_eqv_proofs S (A_sg_CS_sg_eqv S sg_sgS)) 
                           (A_eqv_proofs T (A_sg_C_sg_eqv T sg_sgT)) 
                           (A_sg_CS_sg_times_proofs S sg_sgS)
                           (A_sg_C_sg_times_proofs T sg_sgT)
   ; A_sg_C_sg_proofs    := sg_sg_proofs_llex S T 
                           (A_eqv_eq S (A_sg_CS_sg_eqv S sg_sgS)) 
                           (A_eqv_eq T (A_sg_C_sg_eqv T sg_sgT))
                           (A_sg_CS_sg_plus S sg_sgS) 
                           (A_sg_CS_sg_times S sg_sgS) 
                           (A_sg_C_sg_plus T sg_sgT) 
                           (A_sg_C_sg_times T sg_sgT) 
                           (A_eqv_proofs S (A_sg_CS_sg_eqv S sg_sgS)) 
                           (A_eqv_proofs T (A_sg_C_sg_eqv T sg_sgT)) 
                           (A_sg_CS_sg_plus_proofs S sg_sgS) 
                           (A_sg_CS_sg_times_proofs S sg_sgS) 
                           (A_sg_C_sg_plus_proofs T sg_sgT) 
                           (A_sg_C_sg_times_proofs T sg_sgT) 
                           (A_sg_CS_sg_proofs S sg_sgS) 
                           (A_sg_C_sg_proofs T sg_sgT) 
   ; A_sg_C_sg_ast        := Ast_sg_C_sg_llex (A_sg_CS_sg_ast S sg_sgS, A_sg_C_sg_ast T sg_sgT)
|}. 
