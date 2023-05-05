Require Import Coq.Strings.String.
Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.data.
Require Import CAS.coq.common.ast.
Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.ltr.properties.

Section ACAS. 

Record A_ltr_properties {L S : Type} (eqL : brel L) (eqS : brel S) (ltr : ltr_type L S) := 
{
  A_ltr_props_congruence     : A_ltr_congruence eqL eqS ltr    
; A_ltr_props_is_right_d     : A_ltr_is_right_decidable eqS ltr
; A_ltr_props_constant_d     : A_ltr_constant_decidable eqS ltr 
; A_ltr_props_cancellative_d : A_ltr_cancellative_decidable eqS ltr
}.


Record A_ltr {L S : Type} :=
{
  A_ltr_carrier      : A_eqv S
; A_ltr_label        : A_eqv L                                                       
; A_ltr_ltr          : ltr_type L S (* L -> (S -> S) *)
; A_ltr_exists_id_d  : A_ltr_exists_id_decidable (A_eqv_eq S A_ltr_carrier) A_ltr_ltr 
; A_ltr_exists_ann_d : A_ltr_exists_ann_decidable (A_eqv_eq S A_ltr_carrier) A_ltr_ltr 
; A_ltr_props        : A_ltr_properties (A_eqv_eq L A_ltr_label) (A_eqv_eq S A_ltr_carrier) A_ltr_ltr
; A_ltr_ast          : cas_ast 
}.

End ACAS.

Section AMCAS.

Inductive A_below_ltr {L S : Type} := 
| A_Below_ltr_top          : @A_ltr L S -> @A_below_ltr L S
.

Inductive A_ltr_mcas {L S : Type} := 
| A_MCAS_ltr_Error        : list string      -> @A_ltr_mcas L S
| A_MCAS_ltr              : @A_below_ltr L S -> @A_ltr_mcas L S
.  

End AMCAS.   

Section CAS. 

Record ltr_properties {L S : Type} := 
{
  ltr_props_is_right_d     : @ltr_is_right_decidable L S
; ltr_props_constant_d     : @ltr_constant_decidable L S                                                      
; ltr_props_cancellative_d : @ltr_cancellative_decidable L S 
}.


Record ltr {L S : Type} :=
{
  ltr_carrier      : @eqv S
; ltr_label        : @eqv L                                                       
; ltr_ltr          : ltr_type L S 
; ltr_exists_id_d  : @ltr_exists_id_decidable L
; ltr_exists_ann_d : @ltr_exists_ann_decidable S
; ltr_props        : @ltr_properties L S 
; ltr_ast          : cas_ast 
}.

End CAS.

Section MCAS.

Inductive below_ltr {L S : Type} := 
| Below_ltr_top  : @ltr L S -> @below_ltr L S
.

Inductive ltr_mcas {L S : Type} := 
| MCAS_ltr_Error : list string    -> @ltr_mcas L S
| MCAS_ltr       : @below_ltr L S -> @ltr_mcas L S
.  
  

End MCAS.   


Section Translate.

Definition P2C_ltr_properties {L S : Type} (eqL : brel L) (eqS : brel S) (ltr : ltr_type L S)
    (P : A_ltr_properties eqL eqS ltr)  (wL : L) (wS : S) : @ltr_properties L S := 
{|
  ltr_props_is_right_d          :=
    p2c_ltr_is_right_decidable eqS ltr (A_ltr_props_is_right_d eqL eqS ltr P) wL wS
; ltr_props_constant_d :=
    p2c_ltr_constant_decidable eqS ltr (A_ltr_props_constant_d eqL eqS ltr P) wL wS                               
; ltr_props_cancellative_d :=
    p2c_ltr_cancellative_decidable eqS ltr (A_ltr_props_cancellative_d eqL eqS ltr P) wL wS
|}.


Definition A2C_ltr {L S : Type} (R : @A_ltr L S) : @ltr L S := 
let ltr := A_ltr_ltr R in 
let eqvS := A_ltr_carrier R in
let eqvL := A_ltr_label R in
let eqS := A_eqv_eq S eqvS in
let eqL := A_eqv_eq L eqvL in
let wL := A_eqv_witness _ eqvL in
let wS := A_eqv_witness _ eqvS in 
{|
  ltr_carrier      := A2C_eqv S eqvS
; ltr_label        := A2C_eqv L eqvL
; ltr_ltr          := ltr 
; ltr_exists_id_d  := p2c_ltr_exists_id_decidable eqS ltr (A_ltr_exists_id_d R) wL
; ltr_exists_ann_d := p2c_ltr_exists_ann_decidable eqS ltr (A_ltr_exists_ann_d R) wS 
; ltr_props        := P2C_ltr_properties eqL eqS ltr (A_ltr_props R) wL wS 
; ltr_ast          := A_ltr_ast R
|}.


Definition A2C_below_ltr {L S : Type} (A : @A_below_ltr L S) : @below_ltr L S :=
  match A with
  | A_Below_ltr_top B => Below_ltr_top (A2C_ltr B)
  end. 

Definition A2C_mcas_ltr {L S : Type} (A : @A_ltr_mcas L S) : @ltr_mcas L S :=
match A with
| A_MCAS_ltr_Error s  => MCAS_ltr_Error s
| A_MCAS_ltr B        => MCAS_ltr (A2C_below_ltr B)
end. 

End Translate.   

