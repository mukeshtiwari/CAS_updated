Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast. 

Require Import CAS.coq.common.eqv_certificates.
Require Import CAS.coq.common.eqv_cert_records.
Require Import CAS.coq.common.eqv_records.

Require Import CAS.coq.common.proof_records.
Require Import CAS.coq.common.a_cas_records.

Require Import CAS.coq.common.brel_properties. 


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

Definition A2C_eqv : ∀ (S : Type), A_eqv S -> @eqv S 
:= λ S E,
let eq := A_eqv_eq S E in   
{| 
  eqv_eq      := eq
; eqv_certs   :=
    {|
       eqv_congruence     := @Assert_Brel_Congruence S 
     ; eqv_reflexive      := @Assert_Reflexive S
     ; eqv_transitive     := @Assert_Transitive S
     ; eqv_symmetric      := @Assert_Symmetric S
     ; eqv_type_ast       := A_eqv_type_ast S eq (A_eqv_proofs S E)                                               
     ; eqv_brel_ast       := A_eqv_brel_ast S eq (A_eqv_proofs S E)
    |}  
; eqv_witness := A_eqv_witness S E
; eqv_new     := A_eqv_new S E
; eqv_exactly_two_d := p2c_exactly_two_check S eq (A_eqv_exactly_two_d S E)                           
; eqv_data    := A_eqv_data S E
; eqv_rep     := A_eqv_rep S E
; eqv_finite_d := p2c_is_finite_check S eq (A_eqv_finite_d S E)
; eqv_ast     := A_eqv_ast S E
|}. 



(* orders *) 


Definition p2c_total_check : ∀ (S : Type) (lte : brel S), 
       brel_total_decidable S lte -> @check_total S 
:= λ S lte d, 
  match d with
   | inl _             => @Certify_Total S
   | inr p => Certify_Not_Total (projT1 p)   
   end. 

Definition p2c_exists_bottom_check : ∀ (S : Type) (lte : brel S), 
       brel_exists_bottom_decidable S lte -> @check_exists_bottom S 
:= λ S lte d, 
  match d with
   | inl p  => Certify_Exists_Bottom (projT1 p)   
   | inr _  => Certify_Not_Exists_Bottom
   end. 

Definition p2c_exists_top_check : ∀ (S : Type) (lte : brel S), 
       brel_exists_top_decidable S lte -> @check_exists_top S 
:= λ S lte d, 
  match d with
   | inl p  => Certify_Exists_Top (projT1 p)   
   | inr _  => Certify_Not_Exists_Top
   end. 

Definition p2c_bottoms_finite_check : ∀ (S : Type) (eq lte : brel S), 
       bottoms_finite_decidable S eq lte -> @check_bottoms_finite S 
:= λ S eq lte d, 
  match d with
   | inl p  => Certify_Bottoms_Finite (projT1 p)   
   | inr p  => Certify_Not_Bottoms_Finite (projT1 p)   
   end. 

Definition P2C_po : ∀ (S : Type) (eq lte : brel S), po_proofs S eq lte -> @po_certificates S 
:= λ S eq lte P,
{|
  po_congruence       := @Assert_Brel_Congruence S 
; po_reflexive        := @Assert_Reflexive S 
; po_transitive       := @Assert_Transitive S
; po_antisymmetric    := @Assert_Antisymmetric S 
; po_total_d          := p2c_total_check S lte (A_po_total_d S eq lte P)
; po_exists_top_d     := p2c_exists_top_check S lte (A_po_exists_top_d S eq lte P)
; po_exists_bottom_d  := p2c_exists_bottom_check S lte (A_po_exists_bottom_d S eq lte P)           
; po_bottoms_finite_d := p2c_bottoms_finite_check S eq lte (A_po_bottoms_finite_d S eq lte P)
; po_brel_ast         := A_po_brel_ast S eq lte P                                                  
|}. 


Definition A2C_po : ∀ (S : Type), A_po S -> @po S 
:= λ S R,
{| 
  po_eqv     := A2C_eqv S (A_po_eqv S R) 
; po_lte    := A_po_lte S R 
; po_certs   := P2C_po S (A_eqv_eq S (A_po_eqv S R)) (A_po_lte S R) (A_po_proofs S R)  
; po_ast     := A_po_ast S R
|}. 


Definition P2C_to : ∀ (S : Type) (eq lte : brel S), to_proofs S eq lte -> @to_certificates S 
:= λ S eq lte P,
{|
  to_congruence    := @Assert_Brel_Congruence S 
; to_reflexive     := @Assert_Reflexive S 
; to_transitive    := @Assert_Transitive S
; to_antisymmetric := @Assert_Antisymmetric S 
; to_total         := @Assert_Total S 
; to_brel_ast      := A_to_brel_ast S eq lte P
|}. 

Definition A2C_to : ∀ (S : Type), A_to S -> @to S 
:= λ S R,
{| 
  to_eqv     := A2C_eqv S (A_to_eqv S R) 
; to_brel    := A_to_brel S R 
; to_certs   := P2C_to S (A_eqv_eq S (A_to_eqv S R)) (A_to_brel S R) (A_to_proofs S R)  
; to_ast     := A_to_ast S R
|}. 


