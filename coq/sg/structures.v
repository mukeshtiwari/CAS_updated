Require Import Coq.Strings.String.

Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.data.
Require Import CAS.coq.common.ast.
Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.sg.properties.

(* semigroups 

Current Implementation Hierarchy

sg     = semigroup 
sg_C   = commutative semigroup 
sg_CS  = commutative selective semigroup (is idempotent, of course) 
sg_CI  = commutative idempotent semigroup, not selective 
sg_CNI = commutative, not idempotent 

           sg 
           |  
          sg_C
         / |  \ 
        /  |   \ 
       /   |    \  
      /    |     \ 
  sg_CI sg_CNI  sg_CS 

*) 


Section ACAS. 

Record sg_proofs (S: Type) (eq : brel S) (bop : binary_op S) := 
{
(* "root set" required                          *) 
  A_sg_associative      : bop_associative S eq bop 
; A_sg_congruence       : bop_congruence S eq bop   

(* "root set" of optional semigroup properties *) 
; A_sg_commutative_d    : bop_commutative_decidable S eq bop  
; A_sg_selective_d      : bop_selective_decidable S eq bop  
; A_sg_idempotent_d     : bop_idempotent_decidable S eq bop  

(* needed to decide selectivity of sg product    *) 
; A_sg_is_left_d        : bop_is_left_decidable S eq bop  
; A_sg_is_right_d       : bop_is_right_decidable S eq bop  

(* needed to decide distributivity of (lex, product). For multiplicative operator *) 
; A_sg_left_cancel_d    : bop_left_cancellative_decidable S eq bop 
; A_sg_right_cancel_d   : bop_right_cancellative_decidable S eq bop 

(* needed to decide distributivity of (lex, product). For multiplicative operator *) 
; A_sg_left_constant_d  : bop_left_constant_decidable S eq bop 
; A_sg_right_constant_d : bop_right_constant_decidable S eq bop 

(* needed to decide absorptivity of (lex, product). For multiplicative operator *) 
; A_sg_anti_left_d      : bop_anti_left_decidable S eq bop 
; A_sg_anti_right_d     : bop_anti_right_decidable S eq bop

}.



Record sg_C_proofs (S: Type) (eq : brel S) (bop : binary_op S) := 
{
  A_sg_C_associative      : bop_associative S eq bop 
; A_sg_C_congruence       : bop_congruence S eq bop   
; A_sg_C_commutative      : bop_commutative S eq bop

; A_sg_C_anti_left_d      : bop_anti_left_decidable S eq bop 
; A_sg_C_anti_right_d     : bop_anti_right_decidable S eq bop 

(***)
; A_sg_C_selective_d      : bop_selective_decidable S eq bop  
; A_sg_C_idempotent_d     : bop_idempotent_decidable S eq bop  

; A_sg_C_cancel_d         : bop_left_cancellative_decidable S eq bop 
; A_sg_C_constant_d       : bop_left_constant_decidable S eq bop 

}.

Record sg_CNI_proofs (S: Type) (eq : brel S) (bop : binary_op S) := 
{
  A_sg_CNI_associative     : bop_associative S eq bop 
; A_sg_CNI_congruence     : bop_congruence S eq bop   
; A_sg_CNI_commutative     : bop_commutative S eq bop  
; A_sg_CNI_not_idempotent : bop_not_idempotent S eq bop

; A_sg_CNI_cancel_d         : bop_left_cancellative_decidable S eq bop 
; A_sg_CNI_constant_d       : bop_left_constant_decidable S eq bop
; A_sg_CNI_anti_left_d      : bop_anti_left_decidable S eq bop 
; A_sg_CNI_anti_right_d     : bop_anti_right_decidable S eq bop                                                         
}. 


Record sg_CS_proofs (S: Type) (eq : brel S) (bop : binary_op S) := 
{
  A_sg_CS_associative        : bop_associative S eq bop 
; A_sg_CS_congruence         : bop_congruence S eq bop   
; A_sg_CS_commutative        : bop_commutative S eq bop  
; A_sg_CS_selective          : bop_selective S eq bop
}. 

Record sg_CI_proofs (S: Type) (eq : brel S) (bop : binary_op S) := 
{
  A_sg_CI_associative        : bop_associative S eq bop 
; A_sg_CI_congruence         : bop_congruence S eq bop   
; A_sg_CI_commutative        : bop_commutative S eq bop  
; A_sg_CI_idempotent         : bop_idempotent S eq bop  
; A_sg_CI_not_selective      : bop_not_selective S eq bop
}. 


(*********************************** sg = semigroup ******************************)

Record A_sg (S : Type) := {
  A_sg_eqv          : A_eqv S
; A_sg_bop          : binary_op S
; A_sg_exists_id_d  : bop_exists_id_decidable S (A_eqv_eq S A_sg_eqv) A_sg_bop
; A_sg_exists_ann_d : bop_exists_ann_decidable S (A_eqv_eq S A_sg_eqv) A_sg_bop
; A_sg_proofs       : sg_proofs S (A_eqv_eq S A_sg_eqv) A_sg_bop
; A_sg_ast          : cas_sg_ast
}.

Record A_sg_C (S : Type) := {
  A_sg_C_eqv            : A_eqv S
; A_sg_C_bop            : binary_op S
; A_sg_C_exists_id_d    : bop_exists_id_decidable S (A_eqv_eq S A_sg_C_eqv) A_sg_C_bop
; A_sg_C_exists_ann_d   : bop_exists_ann_decidable S (A_eqv_eq S A_sg_C_eqv) A_sg_C_bop
; A_sg_C_proofs         : sg_C_proofs S (A_eqv_eq S A_sg_C_eqv) A_sg_C_bop
; A_sg_C_ast            : cas_sg_ast
  }.

Record A_sg_CNI (S : Type) := {
  A_sg_CNI_eqv            : A_eqv S
; A_sg_CNI_bop            : binary_op S
; A_sg_CNI_exists_id_d    : bop_exists_id_decidable S (A_eqv_eq S A_sg_CNI_eqv) A_sg_CNI_bop
; A_sg_CNI_exists_ann_d   : bop_exists_ann_decidable S (A_eqv_eq S A_sg_CNI_eqv) A_sg_CNI_bop
; A_sg_CNI_proofs         : sg_CNI_proofs S (A_eqv_eq S A_sg_CNI_eqv) A_sg_CNI_bop
; A_sg_CNI_ast            : cas_sg_ast
}.


Record A_sg_CI (S : Type) := {
  A_sg_CI_eqv            : A_eqv S
; A_sg_CI_bop            : binary_op S
; A_sg_CI_exists_id_d    : bop_exists_id_decidable S (A_eqv_eq S A_sg_CI_eqv) A_sg_CI_bop
; A_sg_CI_exists_ann_d   : bop_exists_ann_decidable S (A_eqv_eq S A_sg_CI_eqv) A_sg_CI_bop
; A_sg_CI_proofs         : sg_CI_proofs S (A_eqv_eq S A_sg_CI_eqv) A_sg_CI_bop
; A_sg_CI_ast            : cas_sg_ast
}.

Record A_sg_CS (S : Type) := {
  A_sg_CS_eqv            : A_eqv S
; A_sg_CS_bop            : binary_op S
; A_sg_CS_exists_id_d    : bop_exists_id_decidable S (A_eqv_eq S A_sg_CS_eqv) A_sg_CS_bop
; A_sg_CS_exists_ann_d   : bop_exists_ann_decidable S (A_eqv_eq S A_sg_CS_eqv) A_sg_CS_bop
; A_sg_CS_proofs         : sg_CS_proofs S (A_eqv_eq S A_sg_CS_eqv) A_sg_CS_bop
; A_sg_CS_ast            : cas_sg_ast
}.

End ACAS.

Section AMCAS.

Inductive below_sg_proofs (S: Type) (eq : brel S) (bop : binary_op S) := 
| SG_below_sg_proofs       : sg_proofs S eq bop     -> below_sg_proofs S eq bop
| SG_C_below_sg_proofs     : sg_C_proofs S eq bop   -> below_sg_proofs S eq bop
| SG_CS_below_sg_proofs    : sg_CS_proofs S eq bop  -> below_sg_proofs S eq bop    
| SG_CI_below_sg_proofs    : sg_CI_proofs S eq bop  -> below_sg_proofs S eq bop
| SG_CNI_below_sg_proofs   : sg_CNI_proofs S eq bop -> below_sg_proofs S eq bop                                                                       
.

Inductive A_below_sg_CS {S : Type} := 
| A_Below_sg_CS_top        : A_sg_CS S          -> @A_below_sg_CS S
.

Inductive A_below_sg_CI {S : Type} := 
| A_Below_sg_CI_top        : A_sg_CI S          -> @A_below_sg_CI S
. 

Inductive A_below_sg_CNI {S : Type} := 
| A_Below_sg_CNI_top        : A_sg_CNI S          -> @A_below_sg_CNI S
. 

Inductive A_below_sg_C {S : Type} := 
| A_Below_sg_C_top         : A_sg_C S          -> @A_below_sg_C S
| A_Below_sg_C_sg_CS       : @A_below_sg_CS S  -> @A_below_sg_C S
| A_Below_sg_C_sg_CI       : @A_below_sg_CI S  -> @A_below_sg_C S
| A_Below_sg_C_sg_CNI      : @A_below_sg_CNI S -> @A_below_sg_C S                                                                  
.

Inductive A_below_sg {S : Type} := 
| A_Below_sg_top          : A_sg S             -> @A_below_sg S
| A_Below_sg_sg_C         : @A_below_sg_C S     -> @A_below_sg S
.

Inductive A_sg_mcas {S : Type} := 
| A_MCAS_sg_Error        : list string     -> @A_sg_mcas S
| A_MCAS_sg              : @A_below_sg S    -> @A_sg_mcas S
. 

End AMCAS.                                                                                            

Section CAS. 

Record sg_certificates {S: Type}  := 
{
  sg_associative      : assert_associative (S := S) 
; sg_congruence       : assert_bop_congruence (S := S) 

; sg_commutative_d    : check_commutative (S := S) 
; sg_selective_d      : check_selective (S := S) 
; sg_idempotent_d     : check_idempotent (S := S) 

; sg_is_left_d        : check_is_left (S := S) 
; sg_is_right_d       : check_is_right (S := S) 

; sg_left_cancel_d    : check_left_cancellative (S := S) 
; sg_right_cancel_d   : check_right_cancellative (S := S) 
; sg_left_constant_d  : check_left_constant (S := S) 
; sg_right_constant_d : check_right_constant (S := S) 
; sg_anti_left_d      : check_anti_left (S := S) 
; sg_anti_right_d     : check_anti_right (S := S)

}. 

Record sg_C_certificates {S: Type}  := 
{
  sg_C_associative      : assert_associative (S := S) 
; sg_C_congruence       : assert_bop_congruence (S := S) 
; sg_C_commutative      : assert_commutative (S := S) 
; sg_C_selective_d      : check_selective (S := S) 
; sg_C_idempotent_d     : check_idempotent (S := S)
; sg_C_cancel_d         : check_left_cancellative (S := S) 
; sg_C_constant_d       : check_left_constant (S := S) 
; sg_C_anti_left_d      : check_anti_left (S := S) 
; sg_C_anti_right_d     : check_anti_right (S := S)
}.

Record sg_CS_certificates {S: Type}  := 
{
  sg_CS_associative        : assert_associative (S := S) 
; sg_CS_congruence         : assert_bop_congruence (S := S) 
; sg_CS_commutative        : assert_commutative (S := S)
; sg_CS_selective          : assert_selective (S := S)
}. 

Record sg_CI_certificates {S: Type}  := 
{
  sg_CI_associative        : assert_associative (S := S) 
; sg_CI_congruence         : assert_bop_congruence (S := S) 
; sg_CI_commutative        : assert_commutative (S := S) 
; sg_CI_idempotent         : assert_idempotent (S := S) 
; sg_CI_not_selective      : assert_not_selective (S := S)                                             
}.

Record sg_CNI_certificates {S: Type}  := 
{
  sg_CNI_associative     : assert_associative (S := S) 
; sg_CNI_congruence      : assert_bop_congruence (S := S) 
; sg_CNI_commutative     : assert_commutative (S := S) 
; sg_CNI_not_idempotent  : assert_not_idempotent (S := S) 

; sg_CNI_cancel_d         : check_left_cancellative (S := S) 
; sg_CNI_constant_d       : check_left_constant (S := S) 
; sg_CNI_anti_left_d      : check_anti_left (S := S) 
; sg_CNI_anti_right_d     : check_anti_right (S := S)
}. 


Record sg {S : Type} := {
  sg_eqv          : @eqv S 
; sg_bop          : binary_op S
; sg_exists_id_d  : @check_exists_id S
; sg_exists_ann_d : @check_exists_ann S
; sg_certs        : @sg_certificates S
; sg_ast          : cas_sg_ast
}.

Record sg_C {S : Type} := {
  sg_C_eqv            : @eqv S 
; sg_C_bop            : binary_op S
; sg_C_exists_id_d    : @check_exists_id S
; sg_C_exists_ann_d   : @check_exists_ann S
; sg_C_certs          : @sg_C_certificates S
; sg_C_ast            : cas_sg_ast
}.

Record sg_CI {S : Type} := {
  sg_CI_eqv              : @eqv S 
; sg_CI_bop              : binary_op S
; sg_CI_exists_id_d      : @check_exists_id S
; sg_CI_exists_ann_d     : @check_exists_ann S
; sg_CI_certs            : @sg_CI_certificates S
; sg_CI_ast              : cas_sg_ast
  }.

Record sg_CNI {S : Type} := {
  sg_CNI_eqv              : @eqv S 
; sg_CNI_bop              : binary_op S
; sg_CNI_exists_id_d      : @check_exists_id S
; sg_CNI_exists_ann_d     : @check_exists_ann S
; sg_CNI_certs            : @sg_CNI_certificates S
; sg_CNI_ast              : cas_sg_ast
}.


Record sg_CS {S : Type} := {
  sg_CS_eqv            : @eqv S 
; sg_CS_bop            : binary_op S
; sg_CS_exists_id_d    : @check_exists_id S
; sg_CS_exists_ann_d   : @check_exists_ann S
; sg_CS_certs          : @sg_CS_certificates S
; sg_CS_ast            : cas_sg_ast
}.

End CAS.

Section MCAS.

Inductive below_sg_certificates {S: Type} := 
| SG_below_sg_certs       : @sg_certificates S    -> @below_sg_certificates S
| SG_C_below_sg_certs     : @sg_C_certificates S  -> @below_sg_certificates S
| SG_CS_below_sg_certs    : @sg_CS_certificates S -> @below_sg_certificates S
| SG_CI_below_sg_certs    : @sg_CI_certificates S -> @below_sg_certificates S
| SG_CNI_below_sg_certs   : @sg_CNI_certificates S -> @below_sg_certificates S
.

Inductive below_sg_CS {S : Type} := 
| Below_sg_CS_top        : @sg_CS S          -> @below_sg_CS S
.

Inductive below_sg_CI {S : Type} := 
| Below_sg_CI_top        : @sg_CI S          -> @below_sg_CI S
.

Inductive below_sg_CNI {S : Type} := 
| Below_sg_CNI_top        : @sg_CNI S          -> @below_sg_CNI S
. 

Inductive below_sg_C {S : Type} := 
| Below_sg_C_top         : @sg_C S           -> @below_sg_C S
| Below_sg_C_sg_CS       : @below_sg_CS S    -> @below_sg_C S
| Below_sg_C_sg_CI       : @below_sg_CI S    -> @below_sg_C S
| Below_sg_C_sg_CNI      : @below_sg_CNI S   -> @below_sg_C S
.

Inductive below_sg {S : Type} := 
| Below_sg_top          : @sg S             -> @below_sg S
| Below_sg_sg_C         : @below_sg_C S     -> @below_sg S
.

Inductive sg_mcas {S : Type} := 
| MCAS_sg_Error        : list string    -> @sg_mcas S
| MCAS_sg              : @below_sg S    -> @sg_mcas S
. 

End MCAS.                                                                                            


Section Translation.

Definition P2C_sg : ∀ {S : Type} (r : brel S) (b : binary_op S),  
         sg_proofs S r b -> @sg_certificates S 
:= λ S r b P,
{|
  sg_associative      := @Assert_Associative S 
; sg_congruence       := @Assert_Bop_Congruence S 
; sg_commutative_d    := p2c_commutative_check S r b (A_sg_commutative_d S r b P)
; sg_selective_d      := p2c_selective_check S r b (A_sg_selective_d S r b P)
; sg_idempotent_d     := p2c_idempotent_check S r b (A_sg_idempotent_d S r b P)
; sg_is_left_d        := p2c_is_left_check S r b (A_sg_is_left_d S r b P)
; sg_is_right_d       := p2c_is_right_check S r b (A_sg_is_right_d S r b P)
; sg_left_cancel_d    := p2c_left_cancel_check S r b (A_sg_left_cancel_d S r b P)
; sg_right_cancel_d   := p2c_right_cancel_check S r b (A_sg_right_cancel_d S r b P)
; sg_left_constant_d  := p2c_left_constant_check S r b (A_sg_left_constant_d S r b P)
; sg_right_constant_d := p2c_right_constant_check S r b (A_sg_right_constant_d S r b P)
; sg_anti_left_d      := p2c_anti_left_check S r b (A_sg_anti_left_d S r b P)
; sg_anti_right_d     := p2c_anti_right_check S r b (A_sg_anti_right_d S r b P)
|}. 


Definition P2C_sg_C : ∀ {S : Type} (r : brel S) (b : binary_op S),  
         sg_C_proofs S r b -> @sg_C_certificates S 
:= λ S r b P,
{|
  sg_C_associative   := @Assert_Associative S 
; sg_C_congruence    := @Assert_Bop_Congruence S 
; sg_C_commutative   := @Assert_Commutative S 
; sg_C_selective_d   := p2c_selective_check S r b (A_sg_C_selective_d S r b P)
; sg_C_idempotent_d  := p2c_idempotent_check S r b (A_sg_C_idempotent_d S r b P)
; sg_C_cancel_d      := p2c_left_cancel_check S r b (A_sg_C_cancel_d S r b P)
; sg_C_constant_d    := p2c_left_constant_check S r b (A_sg_C_constant_d S r b P)
; sg_C_anti_left_d   := p2c_anti_left_check S r b (A_sg_C_anti_left_d S r b P)
; sg_C_anti_right_d  := p2c_anti_right_check S r b (A_sg_C_anti_right_d S r b P)
|}. 

Definition P2C_sg_CI : ∀ {S : Type} (r : brel S) (b : binary_op S),  
         sg_CI_proofs S r b -> @sg_CI_certificates S 
:= λ S r b P,
{|
  sg_CI_associative   := @Assert_Associative S 
; sg_CI_congruence    := @Assert_Bop_Congruence S 
; sg_CI_commutative   := @Assert_Commutative S 
; sg_CI_idempotent    := @Assert_Idempotent S 
; sg_CI_not_selective   := p2c_not_selective_assert S r b (A_sg_CI_not_selective S r b P)
|}. 

Definition P2C_sg_CNI : ∀ (S : Type) (r : brel S) (b : binary_op S),  
         sg_CNI_proofs S r b -> @sg_CNI_certificates S 
:= λ S r b P,
{|
  sg_CNI_associative     := @Assert_Associative S 
; sg_CNI_congruence      := @Assert_Bop_Congruence S 
; sg_CNI_commutative     := @Assert_Commutative S 
; sg_CNI_not_idempotent  := Assert_Not_Idempotent (projT1 (A_sg_CNI_not_idempotent _ _ _ P))

; sg_CNI_cancel_d         := p2c_left_cancel_check S r b (A_sg_CNI_cancel_d S r b P)
; sg_CNI_constant_d       := p2c_left_constant_check S r b (A_sg_CNI_constant_d S r b P)
; sg_CNI_anti_left_d      := p2c_anti_left_check S r b (A_sg_CNI_anti_left_d S r b P)
; sg_CNI_anti_right_d     := p2c_anti_right_check S r b (A_sg_CNI_anti_right_d S r b P)
|}. 

Definition P2C_sg_CS : ∀ {S : Type} (r : brel S) (b : binary_op S),  
         sg_CS_proofs S r b -> @sg_CS_certificates S 
:= λ S r b P,
{|
  sg_CS_associative   := @Assert_Associative S 
; sg_CS_congruence    := @Assert_Bop_Congruence S 
; sg_CS_commutative   := @Assert_Commutative S 
; sg_CS_selective     := @Assert_Selective S
|}. 

(*************************************************************************) 


Definition A2C_sg {S : Type} (R : A_sg S) : @sg S := 
{| 
  sg_eqv           := A2C_eqv _ (A_sg_eqv _ R) 
; sg_bop          := A_sg_bop _ R 
; sg_exists_id_d  := p2c_exists_id_check _ _ _ (A_sg_exists_id_d _ R)
; sg_exists_ann_d := p2c_exists_ann_check _ _ _ (A_sg_exists_ann_d _ R)
; sg_certs        := P2C_sg _ _ (A_sg_proofs _ R)
; sg_ast          := A_sg_ast _ R
|}. 

Definition A2C_sg_C {S : Type} (R : A_sg_C S) : @sg_C S :=
{| 
  sg_C_eqv            := A2C_eqv _ (A_sg_C_eqv _ R) 
; sg_C_bop            := A_sg_C_bop _ R 
; sg_C_exists_id_d    := p2c_exists_id_check _ _ _ (A_sg_C_exists_id_d _ R)
; sg_C_exists_ann_d   := p2c_exists_ann_check _ _ _ (A_sg_C_exists_ann_d _ R)
; sg_C_certs          := P2C_sg_C _ _ (A_sg_C_proofs _ R)
; sg_C_ast            := A_sg_C_ast _ R
|}.

Definition A2C_sg_CI {S : Type} (R : A_sg_CI S) : @sg_CI S := 
{| 
  sg_CI_eqv              := A2C_eqv _ (A_sg_CI_eqv _ R)
; sg_CI_bop              := A_sg_CI_bop S R 
; sg_CI_exists_id_d      := p2c_exists_id_check _ _ _ (A_sg_CI_exists_id_d _ R)
; sg_CI_exists_ann_d     := p2c_exists_ann_check _ _ _ (A_sg_CI_exists_ann_d _ R)
; sg_CI_certs            := P2C_sg_CI _ _ (A_sg_CI_proofs _ R)
; sg_CI_ast              := A_sg_CI_ast _ R
|}. 
 
Definition A2C_sg_CS {S : Type} (R : A_sg_CS S) : @sg_CS S := 
{| 
  sg_CS_eqv            := A2C_eqv _ (A_sg_CS_eqv _ R)
; sg_CS_bop            := A_sg_CS_bop _ R 
; sg_CS_exists_id_d    := p2c_exists_id_check _ _ _ (A_sg_CS_exists_id_d _ R)
; sg_CS_exists_ann_d   := p2c_exists_ann_check _ _ _ (A_sg_CS_exists_ann_d _ R)
; sg_CS_certs          := P2C_sg_CS _ _ (A_sg_CS_proofs _ R)
; sg_CS_ast            := A_sg_CS_ast _ R
|}.


Definition A2C_sg_CNI {S : Type} (R : A_sg_CNI S) : @sg_CNI S := 
{| 
  sg_CNI_eqv              := A2C_eqv _ (A_sg_CNI_eqv _ R)
; sg_CNI_bop              := A_sg_CNI_bop S R 
; sg_CNI_exists_id_d      := p2c_exists_id_check _ _ _ (A_sg_CNI_exists_id_d _ R)
; sg_CNI_exists_ann_d     := p2c_exists_ann_check _ _ _ (A_sg_CNI_exists_ann_d _ R)
; sg_CNI_certs            := P2C_sg_CNI _ _ _ (A_sg_CNI_proofs _ R)
; sg_CNI_ast              := A_sg_CNI_ast _ R
|}. 


Definition P2C_below_sg_proofs
           {S : Type}
           (eq : brel S)
           (bop : binary_op S)
           (A : below_sg_proofs S eq bop) : @below_sg_certificates S :=
match A with 
| SG_below_sg_proofs _ _ _ B    => SG_below_sg_certs (P2C_sg _ _ B)
| SG_C_below_sg_proofs _ _ _ B  => SG_C_below_sg_certs (P2C_sg_C _ _ B)
| SG_CS_below_sg_proofs _ _ _ B => SG_CS_below_sg_certs (P2C_sg_CS _ _ B)
| SG_CI_below_sg_proofs _ _ _ B => SG_CI_below_sg_certs (P2C_sg_CI _ _ B)
| SG_CNI_below_sg_proofs _ _ _ B => SG_CNI_below_sg_certs (P2C_sg_CNI _ _ _ B)                                                        
end.

Definition A2C_below_sg_CS
           {S : Type}
           (A : @A_below_sg_CS S) : @below_sg_CS S :=
match A with 
| A_Below_sg_CS_top B => Below_sg_CS_top (A2C_sg_CS B)
end.

Definition A2C_below_sg_CI
           {S : Type}
           (A : @A_below_sg_CI S) : @below_sg_CI S :=
match A with 
| A_Below_sg_CI_top B => Below_sg_CI_top (A2C_sg_CI B)
end.

Definition A2C_below_sg_CNI
           {S : Type}
           (A : @A_below_sg_CNI S) : @below_sg_CNI S :=
match A with 
| A_Below_sg_CNI_top B => Below_sg_CNI_top (A2C_sg_CNI B)
end.

Definition A2C_below_sg_C
           {S : Type}
           (A : @A_below_sg_C S) : @below_sg_C S :=
match A with 
| A_Below_sg_C_top B    => Below_sg_C_top (A2C_sg_C B)
| A_Below_sg_C_sg_CS B  => Below_sg_C_sg_CS (A2C_below_sg_CS B)
| A_Below_sg_C_sg_CI B  => Below_sg_C_sg_CI (A2C_below_sg_CI B) 
| A_Below_sg_C_sg_CNI B => Below_sg_C_sg_CNI (A2C_below_sg_CNI B)
end.

Definition A2C_below_sg
           {S : Type}
           (A : @A_below_sg S) : @below_sg S :=
match A with 
| A_Below_sg_top B  => Below_sg_top (A2C_sg B)
| A_Below_sg_sg_C B => Below_sg_sg_C (A2C_below_sg_C B)
end.

Definition A2C_sg_mcas
           {S : Type}
           (A : @A_sg_mcas S) : @sg_mcas S :=
match A with
| A_MCAS_sg B        => MCAS_sg (A2C_below_sg B)
| A_MCAS_sg_Error sl => MCAS_sg_Error sl
end.
  
End Translation.




