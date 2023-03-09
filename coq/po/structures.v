Require Import Coq.Strings.String.

Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.data.
Require Import CAS.coq.common.ast.
Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.po.properties.
Require Import CAS.coq.po.theory.

(* implementation hierarchy for orders 

           qo 
         / | \
        /  |  \ 
       /   |   \ 
      /    |    \ 
     /     |     \
    po   qo_wb   fo  
     |  /     \  |
     | /       \ |
    po_wb      fo_wb

wb = with_bottom 

qo = quasi order (ref, trans) 
po = partial order (ref, trans, antisymm, not total)   
fo = preference order quasi order (ref, trans, total) 
wb = "with_bottom" (currently needed for minset_union ) 

Note : minset_union (currently) needs distinction 
between total/not_total as well as the "_with_bottom". 


*) 
Section ACAS.

Record qo_proofs (S : Type) (eq lte : brel S) := {
  A_qo_congruence      : brel_congruence S eq lte
; A_qo_reflexive       : brel_reflexive S lte       
; A_qo_transitive      : brel_transitive S lte
; A_qo_antisymmetric_d : brel_antisymmetric_decidable S eq lte
; A_qo_total_d         : brel_total_decidable S lte
; A_qo_trivial_d       : order_trivial_decidable S lte                                                          
}.

Record po_proofs (S : Type) (eq lte : brel S) := {
  A_po_congruence    : brel_congruence S eq lte 
; A_po_reflexive     : brel_reflexive S lte            
; A_po_transitive    : brel_transitive S lte           
; A_po_antisymmetric : brel_antisymmetric S eq lte
; A_po_not_total     : brel_not_total S lte
  }.

Record fo_proofs (S : Type) (eq lte : brel S) := {
  A_fo_congruence      : brel_congruence S eq lte
; A_fo_reflexive       : brel_reflexive S lte       
; A_fo_transitive      : brel_transitive S lte
; A_fo_antisymmetric_d : brel_antisymmetric_decidable S eq lte
; A_fo_total           : brel_total S lte
; A_fo_trivial_d       : order_trivial_decidable S lte                                                          
}.


Record A_qo (S : Type) := {
  A_qo_eqv             : A_eqv S 
; A_qo_lte             : brel S
; A_qo_exists_top_d    : brel_exists_qo_top_decidable S (A_eqv_eq S A_qo_eqv) A_qo_lte           
; A_qo_exists_bottom_d : brel_exists_qo_bottom_decidable S (A_eqv_eq S A_qo_eqv) A_qo_lte
; A_qo_proofs          : qo_proofs S (A_eqv_eq S A_qo_eqv) A_qo_lte 
; A_qo_ast             : cas_or_ast
}.

Record A_po (S : Type) := {
  A_po_eqv               : A_eqv S 
; A_po_lte               : brel S
; A_po_exists_top_d      : brel_exists_top_decidable S A_po_lte           
; A_po_exists_bottom_d   : brel_exists_bottom_decidable S A_po_lte
; A_po_proofs            : po_proofs S (A_eqv_eq S A_po_eqv) A_po_lte 
; A_po_ast               : cas_or_ast
}.

Record A_fo (S : Type) := {
  A_fo_eqv               : A_eqv S 
; A_fo_lte               : brel S
; A_fo_exists_top_d      : brel_exists_qo_top_decidable S (A_eqv_eq S A_fo_eqv) A_fo_lte           
; A_fo_exists_bottom_d   : brel_exists_qo_bottom_decidable S (A_eqv_eq S A_fo_eqv) A_fo_lte
; A_fo_proofs            : fo_proofs S (A_eqv_eq S A_fo_eqv) A_fo_lte 
; A_fo_ast               : cas_or_ast
}.

Record A_po_with_bottom (S : Type) := {
  A_po_with_bottom_eqv               : A_eqv S 
; A_po_with_bottom_lte               : brel S
; A_po_with_bottom_exists_top_d      : brel_exists_top_decidable S A_po_with_bottom_lte           
; A_po_with_bottom_exists_bottom     : brel_exists_bottom S A_po_with_bottom_lte
; A_po_with_bottom_proofs            : po_proofs S (A_eqv_eq S A_po_with_bottom_eqv) A_po_with_bottom_lte 
; A_po_with_bottom_ast               : cas_or_ast
}.

Record A_qo_with_bottom (S : Type) := {
  A_qo_with_bottom_eqv               : A_eqv S 
; A_qo_with_bottom_lte               : brel S
; A_qo_with_bottom_exists_top_d      : brel_exists_qo_top_decidable S (A_eqv_eq S A_qo_with_bottom_eqv) A_qo_with_bottom_lte           
; A_qo_with_bottom_exists_bottom     : brel_exists_qo_bottom S (A_eqv_eq S A_qo_with_bottom_eqv) A_qo_with_bottom_lte
; A_qo_with_bottom_proofs            : qo_proofs S (A_eqv_eq S A_qo_with_bottom_eqv) A_qo_with_bottom_lte 
; A_qo_with_bottom_ast               : cas_or_ast
}.

Record A_fo_with_bottom (S : Type) := {
  A_fo_with_bottom_eqv             : A_eqv S 
; A_fo_with_bottom_lte             : brel S
; A_fo_with_bottom_exists_top_d    : brel_exists_qo_top_decidable S (A_eqv_eq S A_fo_with_bottom_eqv) A_fo_with_bottom_lte           
; A_fo_with_bottom_exists_bottom   : brel_exists_qo_bottom S (A_eqv_eq S A_fo_with_bottom_eqv) A_fo_with_bottom_lte
; A_fo_with_bottom_proofs          : fo_proofs S (A_eqv_eq S A_fo_with_bottom_eqv) A_fo_with_bottom_lte 
; A_fo_with_bottom_ast             : cas_or_ast
}.

End ACAS.


Section AMCAS.


Inductive A_below_po_with_bottom {S : Type} := 
| A_Below_po_with_bottom_top : A_po_with_bottom S -> @A_below_po_with_bottom S
.

Inductive A_below_fo_with_bottom {S : Type} := 
| A_Below_fo_with_bottom_top : A_fo_with_bottom S -> @A_below_fo_with_bottom S
.

Inductive A_below_qo_with_bottom {S : Type} := 
| A_Below_qo_with_bottom_top : A_qo_with_bottom S -> @A_below_qo_with_bottom S
| A_Below_qo_with_bottom_fo_with_bottom : @A_below_fo_with_bottom S -> @A_below_qo_with_bottom S
| A_Below_qo_with_bottom_po_with_bottom : @A_below_po_with_bottom S -> @A_below_qo_with_bottom S                                                                                               
.

Inductive A_below_po {S : Type} := 
| A_Below_po_top            : A_po S                    -> @A_below_po S
| A_Below_po_po_with_bottom : @A_below_po_with_bottom S -> @A_below_po S
.

Inductive A_below_fo {S : Type} := 
| A_Below_fo_top            : A_fo S                    -> @A_below_fo S
| A_Below_fo_fo_with_bottom : @A_below_fo_with_bottom S -> @A_below_fo S
.

Inductive A_below_qo {S : Type} := 
| A_Below_qo_top            : A_qo S                    -> @A_below_qo S
| A_Below_qo_po             : @A_below_po S             -> @A_below_qo S                                                                       
| A_Below_qo_fo             : @A_below_fo S             -> @A_below_qo S
| A_Below_qo_qo_with_bottom : @A_below_qo_with_bottom S  -> @A_below_qo S                                                                       
.

Inductive A_qo_mcas {S : Type} := 
| A_MCAS_qo_Error : list string  -> @A_qo_mcas S
| A_MCAS_qo       : @A_below_qo S -> @A_qo_mcas S
.

End AMCAS. 

Section CAS.


Record qo_certificates {S : Type} := {
  qo_congruence       : @assert_brel_congruence S 
; qo_reflexive        : @assert_reflexive S 
; qo_transitive       : @assert_transitive S
; qo_antisymmetric_d  : @certify_antisymmetric S 
; qo_total_d          : @certify_total S
; qo_trivial_d        : @order_trivial_certifiable S               
}.

Record po_certificates {S : Type} := {
  po_congruence       : @assert_brel_congruence S 
; po_reflexive        : @assert_reflexive S 
; po_transitive       : @assert_transitive S
; po_antisymmetric    : @assert_antisymmetric S
; po_not_total        : @assert_not_total S
}.

Record fo_certificates {S : Type} := {
  fo_congruence       : @assert_brel_congruence S 
; fo_reflexive        : @assert_reflexive S 
; fo_transitive       : @assert_transitive S
; fo_antisymmetric_d  : @certify_antisymmetric S 
; fo_total            : @assert_total S
; fo_trivial_d        : @order_trivial_certifiable S               
}.


Record qo {S : Type} := {
  qo_eqv             : @eqv S
; qo_lte             : @brel S
; qo_exists_top_d    : @certify_exists_qo_top S 
; qo_exists_bottom_d : @certify_exists_qo_bottom S 
; qo_certs           : @qo_certificates S
; qo_ast             : cas_or_ast
}.

Record po {S : Type} := {
  po_eqv                 : @eqv S
; po_lte                 : @brel S
; po_exists_top_d        : @certify_exists_top S 
; po_exists_bottom_d     : @certify_exists_bottom S 
; po_certs               : @po_certificates S
; po_ast                 : cas_or_ast
}.

Record fo {S : Type} := {
  fo_eqv             : @eqv S
; fo_lte             : @brel S
; fo_exists_top_d    : @certify_exists_qo_top S 
; fo_exists_bottom_d : @certify_exists_qo_bottom S 
; fo_certs           : @fo_certificates S
; fo_ast             : cas_or_ast
}.

Record po_with_bottom {S : Type} := {
  po_with_bottom_eqv                 : @eqv S
; po_with_bottom_lte                 : @brel S
; po_with_bottom_exists_top_d        : @certify_exists_top S 
; po_with_bottom_exists_bottom       : @assert_exists_bottom S 
; po_with_bottom_certs               : @po_certificates S
; po_with_bottom_ast                 : cas_or_ast
}.

Record qo_with_bottom {S : Type} := {
  qo_with_bottom_eqv                 : @eqv S
; qo_with_bottom_lte                 : @brel S
; qo_with_bottom_exists_top_d        : @certify_exists_qo_top S 
; qo_with_bottom_exists_bottom       : @assert_exists_qo_bottom S 
; qo_with_bottom_certs               : @qo_certificates S
; qo_with_bottom_ast                 : cas_or_ast
}.

Record fo_with_bottom {S : Type} := {
  fo_with_bottom_eqv                 : @eqv S
; fo_with_bottom_lte                 : @brel S
; fo_with_bottom_exists_top_d        : @certify_exists_qo_top S 
; fo_with_bottom_exists_bottom       : @assert_exists_qo_bottom S 
; fo_with_bottom_certs               : @fo_certificates S
; fo_with_bottom_ast                 : cas_or_ast
}.

End CAS.

Section MCAS.

Inductive below_po_with_bottom {S : Type} := 
| Below_po_with_bottom_top : @po_with_bottom S -> @below_po_with_bottom S
.

Inductive below_fo_with_bottom {S : Type} := 
| Below_fo_with_bottom_top : @fo_with_bottom S -> @below_fo_with_bottom S
.

Inductive below_qo_with_bottom {S : Type} := 
| Below_qo_with_bottom_top : @qo_with_bottom S -> @below_qo_with_bottom S
| Below_qo_with_bottom_fo_with_bottom : @below_fo_with_bottom S -> @below_qo_with_bottom S
| Below_qo_with_bottom_po_with_bottom : @below_po_with_bottom S -> @below_qo_with_bottom S 
.

Inductive below_po {S : Type} := 
| Below_po_top            : @po S                    -> @below_po S
| Below_po_po_with_bottom : @below_po_with_bottom S -> @below_po S
.

Inductive below_fo {S : Type} := 
| Below_fo_top            : @fo S                   -> @below_fo S
| Below_fo_fo_with_bottom : @below_fo_with_bottom S -> @below_fo S
.

Inductive below_qo {S : Type} := 
| Below_qo_top            :@qo S                    -> @below_qo S
| Below_qo_po             : @below_po S             -> @below_qo S
| Below_qo_fo             : @below_fo S             -> @below_qo S
| Below_qo_qo_with_bottom : @below_qo_with_bottom S -> @below_qo S                                                                  
.

Inductive qo_mcas {S : Type} := 
| MCAS_qo_Error : list string  -> @qo_mcas S
| MCAS_qo       : @below_qo S -> @qo_mcas S
.  

End MCAS. 


Section Translation.

Definition P2C_qo {S : Type} (eq lte : brel S) (P : qo_proofs S eq lte) : @qo_certificates S := 
{|
  qo_congruence       := @Assert_Brel_Congruence S 
; qo_reflexive        := @Assert_Reflexive S 
; qo_transitive       := @Assert_Transitive S
; qo_antisymmetric_d  := p2c_antisymmetric_check S eq lte (A_qo_antisymmetric_d S eq lte P)
; qo_total_d          := p2c_total_check S lte (A_qo_total_d S eq lte P)
; qo_trivial_d        := p2c_order_trivial_certificate S lte (A_qo_trivial_d S eq lte P)                                         
|}. 

Definition P2C_po {S : Type} (eq lte : brel S) (P : po_proofs S eq lte) : @po_certificates S := 
{|
  po_congruence       := @Assert_Brel_Congruence S 
; po_reflexive        := @Assert_Reflexive S 
; po_transitive       := @Assert_Transitive S
; po_antisymmetric    := @Assert_Antisymmetric S
; po_not_total        := p2c_not_total_assert S lte (A_po_not_total S eq lte P)
|}.

Definition P2C_fo {S : Type} (eq lte : brel S) (P : fo_proofs S eq lte) : @fo_certificates S := 
{|
  fo_congruence       := @Assert_Brel_Congruence S 
; fo_reflexive        := @Assert_Reflexive S 
; fo_transitive       := @Assert_Transitive S
; fo_antisymmetric_d  := p2c_antisymmetric_check S eq lte (A_fo_antisymmetric_d S eq lte P)
; fo_total            := @Assert_Total S
; fo_trivial_d        := p2c_order_trivial_certificate S lte (A_fo_trivial_d S eq lte P)                                         
|}. 


Definition A2C_qo {S : Type} (R : A_qo S) : @qo S := 
let eq  := A_eqv_eq S (A_qo_eqv S R) in
let lte := A_qo_lte S R in   
{| 
  qo_eqv              := A2C_eqv S (A_qo_eqv S R) 
; qo_lte              := A_qo_lte S R
; qo_exists_top_d     := p2c_exists_qo_top_check S eq lte (A_qo_exists_top_d S R)
; qo_exists_bottom_d  := p2c_exists_qo_bottom_check S eq lte (A_qo_exists_bottom_d S R)                          
; qo_certs            := P2C_qo eq lte (A_qo_proofs S R)
; qo_ast              := A_qo_ast S R                       
|}.

Definition A2C_po {S : Type} (R : A_po S) : @po S := 
let eq  := A_eqv_eq S (A_po_eqv S R) in 
let lte := A_po_lte S R in 
{| 
  po_eqv               := A2C_eqv S (A_po_eqv S R) 
; po_lte               := lte 
; po_exists_top_d      := p2c_exists_top_check S lte (A_po_exists_top_d S R)
; po_exists_bottom_d   := p2c_exists_bottom_check S lte  (A_po_exists_bottom_d S R)                          
; po_certs             := P2C_po eq lte (A_po_proofs S R)
; po_ast               := A_po_ast S R                       
|}. 

Definition A2C_fo {S : Type} (R : A_fo S) : @fo S := 
let eq  := A_eqv_eq S (A_fo_eqv S R) in
let lte := A_fo_lte S R in   
{| 
  fo_eqv              := A2C_eqv S (A_fo_eqv S R) 
; fo_lte              := lte
; fo_exists_top_d     := p2c_exists_qo_top_check S eq lte (A_fo_exists_top_d S R)
; fo_exists_bottom_d  := p2c_exists_qo_bottom_check S eq lte (A_fo_exists_bottom_d S R)                          
; fo_certs            := P2C_fo eq lte (A_fo_proofs S R)
; fo_ast              := A_fo_ast S R                       
|}.

Definition A2C_po_with_bottom {S : Type} (R : A_po_with_bottom S) : @po_with_bottom S := 
let eq  := A_eqv_eq S (A_po_with_bottom_eqv S R) in 
let lte := A_po_with_bottom_lte S R in 
{| 
  po_with_bottom_eqv               := A2C_eqv S (A_po_with_bottom_eqv S R) 
; po_with_bottom_lte               := lte 
; po_with_bottom_exists_top_d      := p2c_exists_top_check S lte (A_po_with_bottom_exists_top_d S R)
; po_with_bottom_exists_bottom     := p2c_exists_bottom_assert S lte  (A_po_with_bottom_exists_bottom S R)                          
; po_with_bottom_certs             := P2C_po eq lte (A_po_with_bottom_proofs S R)
; po_with_bottom_ast               := A_po_with_bottom_ast S R                       
|}.


Definition A2C_qo_with_bottom {S : Type} (R : A_qo_with_bottom S) : @qo_with_bottom S := 
let eq  := A_eqv_eq S (A_qo_with_bottom_eqv S R) in 
let lte := A_qo_with_bottom_lte S R in 
{| 
  qo_with_bottom_eqv               := A2C_eqv S (A_qo_with_bottom_eqv S R) 
; qo_with_bottom_lte               := lte 
; qo_with_bottom_exists_top_d      := p2c_exists_qo_top_check S eq lte (A_qo_with_bottom_exists_top_d S R)
; qo_with_bottom_exists_bottom     := p2c_exists_qo_bottom_assert S eq lte (A_qo_with_bottom_exists_bottom S R)                          
; qo_with_bottom_certs             := P2C_qo eq lte (A_qo_with_bottom_proofs S R)
; qo_with_bottom_ast               := A_qo_with_bottom_ast S R                       
|}.

Definition A2C_fo_with_bottom {S : Type} (R : A_fo_with_bottom S) : @fo_with_bottom S :=
let eq  := A_eqv_eq S (A_fo_with_bottom_eqv S R) in
let lte := A_fo_with_bottom_lte S R in   
{| 
  fo_with_bottom_eqv               := A2C_eqv S (A_fo_with_bottom_eqv S R) 
; fo_with_bottom_lte               := lte
; fo_with_bottom_exists_top_d      := p2c_exists_qo_top_check S eq  lte (A_fo_with_bottom_exists_top_d S R)
; fo_with_bottom_exists_bottom     := p2c_exists_qo_bottom_assert S eq lte  (A_fo_with_bottom_exists_bottom S R)
; fo_with_bottom_certs             := P2C_fo eq lte (A_fo_with_bottom_proofs S R)
; fo_with_bottom_ast               := A_fo_with_bottom_ast S R                       
|}. 


Definition A2C_below_po_with_bottom {S : Type} (R : @A_below_po_with_bottom S) :=
match R with             
| A_Below_po_with_bottom_top A =>
    Below_po_with_bottom_top (A2C_po_with_bottom A)
end.

Definition A2C_below_fo_with_bottom {S : Type} (R : @A_below_fo_with_bottom S) :=
match R with             
| A_Below_fo_with_bottom_top A =>
    Below_fo_with_bottom_top (A2C_fo_with_bottom A)
end.

Definition A2C_below_qo_with_bottom {S : Type} (R : @A_below_qo_with_bottom S) :=
match R with             
| A_Below_qo_with_bottom_top A =>
    Below_qo_with_bottom_top (A2C_qo_with_bottom A)
| A_Below_qo_with_bottom_fo_with_bottom A =>
    Below_qo_with_bottom_fo_with_bottom (A2C_below_fo_with_bottom A)
| A_Below_qo_with_bottom_po_with_bottom A =>
    Below_qo_with_bottom_po_with_bottom (A2C_below_po_with_bottom A)
end.

Definition A2C_below_po {S : Type} (R : @A_below_po S):=
match R with 
| A_Below_po_top A            =>   Below_po_top (A2C_po A)                                                
| A_Below_po_po_with_bottom A =>
    Below_po_po_with_bottom (A2C_below_po_with_bottom A)
end.

Definition A2C_below_fo {S : Type} (R : @A_below_fo S):=
match R with 
| A_Below_fo_top A            =>   Below_fo_top (A2C_fo A)                                                
| A_Below_fo_fo_with_bottom A =>
    Below_fo_fo_with_bottom (A2C_below_fo_with_bottom A)
end.

Definition A2C_below_qo {S : Type} (R : @A_below_qo S):=
match R with 
| A_Below_qo_top A => Below_qo_top (A2C_qo A)            
| A_Below_qo_po  A => Below_qo_po (A2C_below_po A)
| A_Below_qo_fo  A => Below_qo_fo (A2C_below_fo A)
| A_Below_qo_qo_with_bottom  A => Below_qo_qo_with_bottom (A2C_below_qo_with_bottom A)                                                                     
end.

Definition A2C_qo_mcas {S : Type} (R : @A_qo_mcas S) : @qo_mcas S :=
match R with 
| A_MCAS_qo_Error sl =>  MCAS_qo_Error sl
| A_MCAS_qo       A  =>  MCAS_qo (A2C_below_qo A)
end.


End Translation.

