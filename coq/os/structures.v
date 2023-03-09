Require Import Coq.Strings.String.

Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.data.
Require Import CAS.coq.common.ast.
Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.po.properties.
Require Import CAS.coq.po.structures.
Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures.
Require Import CAS.coq.os.properties.
Require Import CAS.coq.os.theory. 

Section ACAS.

Record os_qo_bottom_top_proofs (S: Type) (eq lte : brel S) (times : binary_op S) := 
{
  A_qo_bottom_top_bottom_id_d : os_exists_qo_bottom_id_decidable S eq lte times 
; A_qo_bottom_top_top_ann_d   : os_exists_qo_top_ann_decidable S eq lte times 
}.
  
Record os_bottom_top_proofs (S: Type) (eq lte : brel S) (times : binary_op S) := 
{
  A_bottom_top_bottom_id_d : os_exists_bottom_id_decidable S eq lte times 
; A_bottom_top_top_ann_d   : os_exists_top_ann_decidable S eq lte times 
}.

Record os_bottom_is_id_proofs (S: Type) (eq lte : brel S) (times : binary_op S) := 
{
  A_bottom_is_id           : A_os_exists_bottom_id_equal eq lte times 
; A_bottom_is_id_top_ann_d : os_exists_top_ann_decidable S eq lte times 
}.

Record os_top_is_ann_proofs (S: Type) (eq lte : brel S) (times : binary_op S) := 
{
  A_top_is_ann_bottom_id_d : os_exists_bottom_id_decidable S eq lte times 
; A_top_is_ann             : A_os_exists_top_ann_equal eq lte times 
}.


Record os_bounded_proofs (S: Type) (eq lte : brel S) (times : binary_op S) := 
{
  A_bounded_bottom_id : A_os_exists_bottom_id_equal eq lte times 
; A_bounded_top_ann   : A_os_exists_top_ann_equal eq lte times 
}.

Record os_proofs (S: Type) (lte : brel S) (times : binary_op S) := 
{
  A_posg_left_monotonic_d            : os_left_monotone_decidable lte times 
; A_posg_right_monotonic_d           : os_right_monotone_decidable lte times 

; A_posg_left_increasing_d           : os_left_increasing_decidable lte times 
; A_posg_right_increasing_d          : os_right_increasing_decidable lte times 

(*                                                                     
; A_posg_left_strictly_increasing_d  : os_left_strictly_increasing_decidable lte times 
; A_posg_right_strictly_increasing_d : os_right_strictly_increasing_decidable lte times 
*) 
}.

Record os_monotone_proofs (S: Type) (lte : brel S) (times : binary_op S) := 
{
  A_mono_left_monotonic              : os_left_monotone lte times 
; A_mono_right_monotonic             : os_right_monotone lte times 

; A_mono_left_increasing_d           : os_left_increasing_decidable lte times 
; A_mono_right_increasing_d          : os_right_increasing_decidable lte times 

}. 

Record os_monotone_increasing_proofs (S: Type) (lte : brel S) (times : binary_op S) := 
{
  A_mono_inc_left_monotonic              : os_left_monotone lte times 
; A_mono_inc_right_monotonic             : os_right_monotone lte times 
; A_mono_inc_left_increasing             : os_left_increasing lte times 
; A_mono_inc_right_increasing            : os_right_increasing lte times 
}. 

(* used for trivial *) 
Record A_qosg (S : Type) := {
  A_qosg_eqv               : A_eqv S 
; A_qosg_lte               : brel S 
; A_qosg_times             : binary_op S 
; A_qosg_lte_proofs        : qo_proofs S (A_eqv_eq S A_qosg_eqv) A_qosg_lte
; A_qosg_times_proofs      : sg_proofs S (A_eqv_eq S A_qosg_eqv) A_qosg_times
; A_qosg_bottom_top_proofs : os_qo_bottom_top_proofs S (A_eqv_eq S A_qosg_eqv) A_qosg_lte A_qosg_times
; A_qosg_proofs            : os_proofs S A_qosg_lte A_qosg_times 
; A_qosg_ast               : cas_os_ast
}.

(* os/from_bs_left?  sg/union? *) 
Record A_posg (S : Type) := {
  A_posg_eqv               : A_eqv S 
; A_posg_lte               : brel S 
; A_posg_times             : binary_op S 
; A_posg_lte_proofs        : po_proofs S (A_eqv_eq S A_posg_eqv) A_posg_lte
; A_posg_times_proofs      : sg_proofs S (A_eqv_eq S A_posg_eqv) A_posg_times
; A_posg_bottom_top_proofs : os_bottom_top_proofs S (A_eqv_eq S A_posg_eqv) A_posg_lte A_posg_times
; A_posg_proofs            : os_proofs S A_posg_lte A_posg_times 
; A_posg_ast               : cas_os_ast
}.

(* only used in product (?*) 
Record A_monotone_posg (S : Type) := {
  A_mposg_eqv          : A_eqv S 
; A_mposg_lte          : brel S 
; A_mposg_times        : binary_op S 
; A_mposg_lte_proofs   : po_proofs S (A_eqv_eq S A_mposg_eqv) A_mposg_lte
; A_mposg_times_proofs : sg_proofs S (A_eqv_eq S A_mposg_eqv) A_mposg_times
; A_mposg_top_bottom   : os_bottom_top_proofs S (A_eqv_eq S A_mposg_eqv) A_mposg_lte A_mposg_times                                    
; A_mposg_proofs       : os_monotone_proofs S A_mposg_lte A_mposg_times 
; A_mposg_ast          : cas_os_ast
}.

(*currently only used in os/from_bs_left (?) *) 
Record A_monotone_increasing_posg (S : Type) := {
  A_miposg_eqv          : A_eqv S 
; A_miposg_lte          : brel S 
; A_miposg_times        : binary_op S 
; A_miposg_lte_proofs   : po_proofs S (A_eqv_eq S A_miposg_eqv) A_miposg_lte
; A_miposg_times_proofs : sg_proofs S (A_eqv_eq S A_miposg_eqv) A_miposg_times
; A_miposg_top_bottom   : os_bottom_top_proofs S (A_eqv_eq S A_miposg_eqv) A_miposg_lte A_miposg_times                                    
; A_miposg_proofs       : os_monotone_increasing_proofs S A_miposg_lte A_miposg_times 
; A_miposg_ast          : cas_os_ast
}.


(* These are needed for two version of sg/minset_lift : 
  A_monotone_increasing_po_with_bottom_sg_CI
  A_monotone_increasing_po_with_bottom_sg_CNI

  from ot: 

  A_monotone_strictly_increasing_qo_with_bottom_sg_CI
  A_monotone_strictly_increasing_qo_with_bottom_sg_CNI

  
 *)
Record A_monotone_increasing_po_with_bottom_sg_CI {S : Type} := {
  A_mi_powb_sg_CI_eqv               : A_eqv S 
; A_mi_powb_sg_CI_lte               : brel S 
; A_mi_powb_sg_CI_times             : binary_op S 
; A_mi_powb_sg_CI_lte_properties
  : po_proofs S 
      (A_eqv_eq S A_mi_powb_sg_CI_eqv)
      A_mi_powb_sg_CI_lte
; A_mi_powb_sg_CI_times_properties      :
  sg_CI_proofs S
    (A_eqv_eq S A_mi_powb_sg_CI_eqv)
    A_mi_powb_sg_CI_times
; A_mi_powb_sg_CI_bottom_top_properties :
  os_bottom_is_id_proofs S 
    (A_eqv_eq S A_mi_powb_sg_CI_eqv)
    A_mi_powb_sg_CI_lte
    A_mi_powb_sg_CI_times
; A_mi_powb_sg_CI_properties            :
  os_monotone_increasing_proofs S
    A_mi_powb_sg_CI_lte
    A_mi_powb_sg_CI_times
; A_mi_powb_sg_CI_ast               : cas_os_ast
  }.


Definition A_po_from_monotone_increasing_po_with_bottom_sg_CI
           (S : Type)
           (P : @A_monotone_increasing_po_with_bottom_sg_CI S) : A_po S :=
let bot_top := A_mi_powb_sg_CI_bottom_top_properties P in  
let bottom_id_equal := A_bottom_is_id  _ _ _ _ bot_top in
let botP  := A_extract_exist_bottom_from_exists_bottom_id_equal _ _ _ _ bottom_id_equal in 
let top_ann_d := A_bottom_is_id_top_ann_d _ _ _ _ bot_top in 
{|
  A_po_eqv             := A_mi_powb_sg_CI_eqv P
; A_po_lte             := A_mi_powb_sg_CI_lte P
; A_po_exists_top_d    := A_extract_exists_top_decidable_from_exists_top_ann_decidable _ _ _ _ top_ann_d 
; A_po_exists_bottom_d := inl botP
; A_po_proofs          := A_mi_powb_sg_CI_lte_properties P 
; A_po_ast             := Ast_or_of_os (A_mi_powb_sg_CI_ast P)
|}.  
  


Record A_monotone_increasing_po_with_bottom_sg_CNI {S : Type} := {
  A_mi_powb_sg_CNI_eqv               : A_eqv S 
; A_mi_powb_sg_CNI_lte               : brel S 
; A_mi_powb_sg_CNI_times             : binary_op S 
; A_mi_powb_sg_CNI_lte_properties
  : po_proofs S 
      (A_eqv_eq S A_mi_powb_sg_CNI_eqv)
      A_mi_powb_sg_CNI_lte
; A_mi_powb_sg_CNI_times_properties      :
  sg_CNI_proofs S
    (A_eqv_eq S A_mi_powb_sg_CNI_eqv)
    A_mi_powb_sg_CNI_times
; A_mi_powb_sg_CNI_bottom_top_properties :
  os_bottom_is_id_proofs S 
    (A_eqv_eq S A_mi_powb_sg_CNI_eqv)
    A_mi_powb_sg_CNI_lte
    A_mi_powb_sg_CNI_times
; A_mi_powb_sg_CNI_properties            :
  os_monotone_increasing_proofs S
    A_mi_powb_sg_CNI_lte
    A_mi_powb_sg_CNI_times
; A_mi_powb_sg_CNI_ast               : cas_os_ast
}.


Definition A_po_from_monotone_increasing_po_with_bottom_sg_CNI
           (S : Type)
           (P : @A_monotone_increasing_po_with_bottom_sg_CNI S) : A_po S :=
let bot_top := A_mi_powb_sg_CNI_bottom_top_properties P in  
let bottom_id_equal := A_bottom_is_id  _ _ _ _ bot_top in
let botP  := A_extract_exist_bottom_from_exists_bottom_id_equal _ _ _ _ bottom_id_equal in 
let top_ann_d := A_bottom_is_id_top_ann_d _ _ _ _ bot_top in 
{|
  A_po_eqv             := A_mi_powb_sg_CNI_eqv P
; A_po_lte             := A_mi_powb_sg_CNI_lte P
; A_po_exists_top_d    := A_extract_exists_top_decidable_from_exists_top_ann_decidable _ _ _ _ top_ann_d 
; A_po_exists_bottom_d := inl botP
; A_po_proofs          := A_mi_powb_sg_CNI_lte_properties P 
; A_po_ast             := Ast_or_of_os (A_mi_powb_sg_CNI_ast P)
|}.  

(*
currently used by 
minset_union_lift
minset_lift_union
minset_union
minset_lift
os/from_sg (?) 

Need 
A_monotone_increasing_posg_CI_with_bottom 
A_bounded_monotone_increasing_posg_CI

A_monotone_increasing_posg_CNI_with_bottom 
A_bounded_monotone_increasing_posg_CNI

*) 
Record A_bounded_monotone_increasing_posg (S : Type) := {
  A_bmiposg_eqv          : A_eqv S 
; A_bmiposg_lte          : brel S 
; A_bmiposg_times        : binary_op S 
; A_bmiposg_lte_proofs   : po_proofs S (A_eqv_eq S A_bmiposg_eqv) A_bmiposg_lte
; A_bmiposg_times_proofs : sg_proofs S (A_eqv_eq S A_bmiposg_eqv) A_bmiposg_times
; A_bmiposg_top_bottom   : os_bounded_proofs S (A_eqv_eq S A_bmiposg_eqv) A_bmiposg_lte A_bmiposg_times                                    
; A_bmiposg_proofs       : os_monotone_increasing_proofs S A_bmiposg_lte A_bmiposg_times 
; A_bmiposg_ast          : cas_os_ast
}.

(* used in union (?) *) 
Record A_meet_semilattice (S : Type) := {
  A_msl_eqv           : A_eqv S 
; A_msl_lte           : brel S 
; A_msl_meet          : binary_op S
; A_msl_lte_proofs    : po_proofs S (A_eqv_eq _ A_msl_eqv) A_msl_lte 
; A_msl_meet_proofs   : sg_CI_proofs S (A_eqv_eq _ A_msl_eqv) A_msl_meet
; A_msl_top_bottom    : os_bottom_top_proofs S (A_eqv_eq S A_msl_eqv) A_msl_lte A_msl_meet
; A_msl_proofs        : bop_is_glb A_msl_lte A_msl_meet
; A_msl_ast           : cas_os_ast
}.

(* used in union (?) *) 
Record A_join_semilattice (S : Type) := {
  A_jsl_eqv           : A_eqv S 
; A_jsl_lte           : brel S 
; A_jsl_join          : binary_op S 
; A_jsl_lte_proofs    : po_proofs S (A_eqv_eq _ A_jsl_eqv) A_jsl_lte 
; A_jsl_join_proofs   : sg_CI_proofs S (A_eqv_eq _ A_jsl_eqv) A_jsl_join
; A_jsl_top_bottom    : os_bottom_top_proofs S (A_eqv_eq S A_jsl_eqv) A_jsl_lte A_jsl_join
; A_jsl_proofs        : bop_is_lub A_jsl_lte A_jsl_join
; A_jsl_ast           : cas_os_ast
}.
(* used minset_union_lift, minset_lift_union  *) 
Record A_bounded_join_semilattice (S : Type) := {
  A_bjsl_eqv           : A_eqv S 
; A_bjsl_lte           : brel S 
; A_bjsl_join          : binary_op S 
; A_bjsl_lte_proofs    : po_proofs S (A_eqv_eq _ A_bjsl_eqv) A_bjsl_lte 
; A_bjsl_join_proofs   : sg_CI_proofs S (A_eqv_eq _ A_bjsl_eqv) A_bjsl_join
; A_bjsl_top_bottom    : os_bounded_proofs S (A_eqv_eq S A_bjsl_eqv) A_bjsl_lte A_bjsl_join
; A_bjsl_proofs        : bop_is_lub A_bjsl_lte A_bjsl_join
; A_bjsl_ast           : cas_os_ast
}.



(*

At one point we had this class defined : 

Record A_bounded_monotone_increasing_posg_CI (S : Type) := {
  A_bmiposg_CI_eqv          : A_eqv S 
; A_bmiposg_CI_lte          : brel S 
; A_bmiposg_CI_times        : binary_op S 
; A_bmiposg_CI_lte_proofs   : po_proofs S (A_eqv_eq S A_bmiposg_CI_eqv) A_bmiposg_CI_lte
; A_bmiposg_CI_times_proofs : sg_CI_proofs S (A_eqv_eq S A_bmiposg_CI_eqv) A_bmiposg_CI_times
; A_bmiposg_CI_top_bottom   : os_bounded_proofs S (A_eqv_eq S A_bmiposg_CI_eqv) A_bmiposg_CI_lte A_bmiposg_CI_times                                    
; A_bmiposg_CI_proofs       : os_monotone_increasing_proofs S A_bmiposg_CI_lte A_bmiposg_CI_times 
; A_bmiposg_CI_ast          : cas_os_ast
}.

At first they seem slightly more general than a A_bounded_join_semilattice S, 
only lacking "bop_is_lub lte times". AH, but not really! 

os/theory.lub_from_monotone_increasing 
     : ∀ (S : Type) (eq lte : brel S),
         brel_reflexive S eq
         → brel_congruence S eq lte
           → brel_antisymmetric S eq lte
             → ∀ bS : binary_op S,
                 bop_idempotent S eq bS
                 → bop_commutative S eq bS
                   → os_left_monotone lte bS
                     → os_right_monotone lte bS
                       → os_left_increasing lte bS
                         → os_right_increasing lte bS → bop_is_lub lte bS


Record A_bounded_monotone_increasing_posg_CNI (S : Type) := {
  A_bmiposg_CNI_eqv          : A_eqv S 
; A_bmiposg_CNI_lte          : brel S 
; A_bmiposg_CNI_times        : binary_op S 
; A_bmiposg_CNI_lte_proofs   : po_proofs S (A_eqv_eq S A_bmiposg_CNI_eqv) A_bmiposg_CNI_lte
; A_bmiposg_CNI_times_proofs : sg_CNI_proofs S (A_eqv_eq S A_bmiposg_CNI_eqv) A_bmiposg_CNI_times
; A_bmiposg_CNI_top_bottom   : os_bounded_proofs S (A_eqv_eq S A_bmiposg_CNI_eqv) A_bmiposg_CNI_lte A_bmiposg_CNI_times                                    
; A_bmiposg_CNI_proofs       : os_monotone_increasing_proofs S A_bmiposg_CNI_lte A_bmiposg_CNI_times 
; A_bmiposg_CNI_ast          : cas_os_ast
}.
 *)


(*
Section Projections.
  
Definition A_po_from_bounded_monotone_increasing_posg
           (S : Type)
           (P : A_bounded_monotone_increasing_posg S) : A_po_bounded S :=
let B := A_bmiposg_top_bottom _ P in 
let bot_id := A_bounded_bottom_id _ _ _ _ B in
let top_ann := A_bounded_top_ann _ _ _ _ B in 
{|
  A_po_bd_eqv           := A_bmiposg_eqv _ P 
; A_po_bd_lte           := A_bmiposg_lte _ P 
; A_po_bd_exists_top    := A_extract_exist_top_from_exists_top_ann_equal _ _ _ _ top_ann
; A_po_bd_exists_bottom := A_extract_exist_bottom_from_exists_bottom_id_equal _ _ _ _ bot_id 
; A_po_bd_proofs        := A_bmiposg_lte_proofs _ P 
; A_po_bd_ast           := Ast_or_of_os (A_bmiposg_ast _ P)
|}.  
  


Definition A_po_from_bounded_monotone_increasing_posg_CNI
           (S : Type)
           (P : A_bounded_monotone_increasing_posg_CNI S) : A_po_bounded S :=
let B := A_bmiposg_CNI_top_bottom _ P in 
let bot_id := A_bounded_bottom_id _ _ _ _ B in
let top_ann := A_bounded_top_ann _ _ _ _ B in 
{|
  A_po_bd_eqv           := A_bmiposg_CNI_eqv _ P 
; A_po_bd_lte           := A_bmiposg_CNI_lte _ P 
; A_po_bd_exists_top    := A_extract_exist_top_from_exists_top_ann_equal _ _ _ _ top_ann
; A_po_bd_exists_bottom := A_extract_exist_bottom_from_exists_bottom_id_equal _ _ _ _ bot_id 
; A_po_bd_proofs        := A_bmiposg_CNI_lte_proofs _ P 
; A_po_bd_ast           := Ast_or_of_os (A_bmiposg_CNI_ast _ P)
|}.  


Definition A_po_from_bounded_join_semilattice
           (S : Type)
           (P : A_bounded_join_semilattice S) : A_po_bounded S :=
let B := A_bjsl_top_bottom _ P in 
let bot_id := A_bounded_bottom_id _ _ _ _ B in
let top_ann := A_bounded_top_ann _ _ _ _ B in 
{|
  A_po_bd_eqv           := A_bjsl_eqv _ P 
; A_po_bd_lte           := A_bjsl_lte _ P 
; A_po_bd_exists_top    := A_extract_exist_top_from_exists_top_ann_equal _ _ _ _ top_ann 
; A_po_bd_exists_bottom := A_extract_exist_bottom_from_exists_bottom_id_equal _ _ _ _ bot_id 
; A_po_bd_proofs        := A_bjsl_lte_proofs _ P 
; A_po_bd_ast           := Ast_or_of_os (A_bjsl_ast _ P)
|}.  
  

End Projections.   
 *)

End ACAS.

Section AMCAS.

Inductive A_os_mcas S : Type :=
| A_OS_Error                            : list string                           -> A_os_mcas S
| A_OS_qosg                             : A_qosg S                             -> A_os_mcas S
| A_OS_posg                             : A_posg S                             -> A_os_mcas S
| A_OS_monotone_posg                    : A_monotone_posg S                    -> A_os_mcas S
| A_OS_monotone_increasing_posg         : A_monotone_increasing_posg S         -> A_os_mcas S
| A_OS_bounded_monotone_increasing_posg : A_bounded_monotone_increasing_posg S -> A_os_mcas S
| A_OS_bounded_join_semilattice         : A_bounded_join_semilattice S          -> A_os_mcas S                                                                                  
.

Definition A_os_classify_bounded_monotone_increasing_posg (S : Type) (A : A_bounded_monotone_increasing_posg S) : A_os_mcas S :=
  A_OS_bounded_monotone_increasing_posg _ A.  


Definition A_os_classify_monotone_increasing_posg (S : Type) (A : A_monotone_increasing_posg S) : A_os_mcas S :=
  match A_bottom_top_bottom_id_d _ _ _ _ (A_miposg_top_bottom _ A),
        A_bottom_top_top_ann_d _ _ _ _ (A_miposg_top_bottom _ A) 
  with 
  | Bottom_Id_Proof_Equal _ _ _ _ P, Top_Ann_Proof_Equal _ _ _ _ Q =>
    A_os_classify_bounded_monotone_increasing_posg _
     {|
         A_bmiposg_eqv          := A_miposg_eqv _ A 
       ; A_bmiposg_lte          := A_miposg_lte _ A 
       ; A_bmiposg_times        := A_miposg_times _ A 
       ; A_bmiposg_lte_proofs   := A_miposg_lte_proofs _ A 
       ; A_bmiposg_times_proofs := A_miposg_times_proofs _ A 
       ; A_bmiposg_top_bottom   := {| A_bounded_bottom_id := P; A_bounded_top_ann := Q|}
       ; A_bmiposg_proofs       := A_miposg_proofs _ A 
       ; A_bmiposg_ast          := A_miposg_ast _ A 
     |}
  | _ , _ => A_OS_monotone_increasing_posg _ A
  end. 

Definition A_os_classify_monotone_posg (S : Type) (A : A_monotone_posg S) : A_os_mcas S :=
  let P := A_mposg_proofs _ A in 
  match A_mono_left_increasing_d _ _ _ P, A_mono_right_increasing_d _ _ _ P 
  with 
  | inl LI, inl RI =>
    A_os_classify_monotone_increasing_posg _ 
     {|
         A_miposg_eqv          := A_mposg_eqv _ A 
       ; A_miposg_lte          := A_mposg_lte _ A 
       ; A_miposg_times        := A_mposg_times _ A 
       ; A_miposg_lte_proofs   := A_mposg_lte_proofs _ A 
       ; A_miposg_times_proofs := A_mposg_times_proofs _ A 
       ; A_miposg_top_bottom   := A_mposg_top_bottom _ A 
       ; A_miposg_proofs       := {|
                                     A_mono_inc_left_monotonic   := A_mono_left_monotonic _ _ _ P 
                                   ; A_mono_inc_right_monotonic  := A_mono_right_monotonic _ _ _ P 
                                   ; A_mono_inc_left_increasing  := LI 
                                   ; A_mono_inc_right_increasing := RI 
                                   |} 
       ; A_miposg_ast          := A_mposg_ast _ A 
     |}
  | _ , _ => A_OS_monotone_posg _ A
  end. 


Definition A_os_classify_posg (S : Type) (A : A_posg S) : A_os_mcas S :=
  let P := A_posg_proofs _ A in 
  match A_posg_left_monotonic_d _ _ _ P, A_posg_right_monotonic_d _ _ _ P 
  with 
  | inl LM, inl RM =>
    A_os_classify_monotone_posg _     
     {|
         A_mposg_eqv          := A_posg_eqv _ A 
       ; A_mposg_lte          := A_posg_lte _ A 
       ; A_mposg_times        := A_posg_times _ A 
       ; A_mposg_lte_proofs   := A_posg_lte_proofs _ A 
       ; A_mposg_times_proofs := A_posg_times_proofs _ A 
       ; A_mposg_top_bottom   := A_posg_bottom_top_proofs _ A 
       ; A_mposg_proofs       := {|
                                     A_mono_left_monotonic   := LM 
                                   ; A_mono_right_monotonic  := RM 
                                   ; A_mono_left_increasing_d  := A_posg_left_increasing_d _ _ _ P 
                                   ; A_mono_right_increasing_d := A_posg_right_increasing_d _ _ _ P 
                                   |} 
       ; A_mposg_ast          := A_posg_ast _ A 
     |}
  | _ , _ => A_OS_posg _ A
  end.


Definition A_os_classify_qosg (S : Type) (A : A_qosg S) : A_os_mcas S :=
  let P := A_qosg_lte_proofs _ A in
  let eqv := A_qosg_eqv _ A in
  let sym := A_eqv_symmetric _ _ (A_eqv_proofs _ eqv) in 
  let bot_top :=  A_qosg_bottom_top_proofs _ A in 
  match A_qo_antisymmetric_d _ _ _ P, A_qo_total_d _ _ _ P  with 
  | inl anti, inr ntot =>
    A_os_classify_posg _     
     {|
         A_posg_eqv          := eqv 
       ; A_posg_lte          := A_qosg_lte _ A 
       ; A_posg_times        := A_qosg_times _ A 
       ; A_posg_lte_proofs   :=
           {|
               A_po_congruence    := A_qo_congruence _ _ _ P
             ; A_po_reflexive     := A_qo_reflexive _ _ _ P
             ; A_po_transitive    := A_qo_transitive _ _ _ P
             ; A_po_antisymmetric := anti
             ; A_po_not_total     := ntot 
           |}
       ; A_posg_times_proofs := A_qosg_times_proofs _ A 
       ; A_posg_bottom_top_proofs   :=
           {|
             A_bottom_top_bottom_id_d :=
               os_exists_bottom_id_decidable_from_os_exists_qo_bottom_id_decidable _ _ _ _
                 sym anti 
                 (A_qo_bottom_top_bottom_id_d _ _ _ _ bot_top)

           ; A_bottom_top_top_ann_d :=
               os_exists_top_ann_decidable_from_os_exists_qo_top_ann_decidable _ _ _ _ 
                 sym anti 
                 (A_qo_bottom_top_top_ann_d _ _ _ _ bot_top)                 
           |}
       ; A_posg_proofs       := A_qosg_proofs _ A 
       ; A_posg_ast          := A_qosg_ast _ A 
     |}
  | _ , _ => A_OS_qosg _ A
  end. 



Definition A_os_classify (S : Type) (A : A_os_mcas S) : A_os_mcas S :=
match A with
| A_OS_Error _ _                            => A
| A_OS_qosg _ B                             => A_os_classify_qosg _ B                                                  
| A_OS_posg _ B                             => A_os_classify_posg _ B 
| A_OS_monotone_posg _ B                    => A_os_classify_monotone_posg _ B 
| A_OS_monotone_increasing_posg _ B         => A_os_classify_monotone_increasing_posg _ B 
| A_OS_bounded_monotone_increasing_posg _ B => A_os_classify_bounded_monotone_increasing_posg _ B
| _ => A                                                                                               
end.     


End AMCAS.                                                   



Section CAS.

Record os_qo_bottom_top_certs {S: Type} :=
{
  qo_bottom_top_bottom_id_d : @os_exists_qo_bottom_id_certificate S
; qo_bottom_top_top_ann_d   : @os_exists_qo_top_ann_certificate S
}.
  


Record os_bottom_top_certs {S: Type} :=
{
  bottom_top_bottom_id_d : @os_exists_bottom_id_certificate S
; bottom_top_top_ann_d   : @os_exists_top_ann_certificate S
}.

Record os_bottom_is_id_certs {S: Type}  :=
{
  bottom_is_id           : @os_exists_bottom_id_equal S
; bottom_is_id_top_ann_d : @os_exists_top_ann_certificate S
}.

Record os_top_is_ann_certs {S: Type}  :=
{
  top_is_ann_bottom_id_d : @os_exists_bottom_id_certificate S
; top_is_ann             : @os_exists_top_ann_equal S
}.

Record os_bounded_certs {S: Type}  :=
{
  bounded_bottom_id : @os_exists_bottom_id_equal S
; bounded_top_ann   : @os_exists_top_ann_equal S
}.

Record os_certificates {S: Type} := 
{
  posg_left_monotonic_d            : @check_left_monotone S 
; posg_right_monotonic_d           : @check_right_monotone S

; posg_left_increasing_d           : @check_left_increasing S
; posg_right_increasing_d          : @check_right_increasing S

(*                                                             
; posg_left_strictly_increasing_d  : @check_left_strictly_increasing S
; posg_right_strictly_increasing_d : @check_right_strictly_increasing S
*) 
}.


Record os_monotone_certificates (S: Type) := 
{
  mono_left_monotonic              : @assert_left_monotone S
; mono_right_monotonic             : @assert_right_monotone S

; mono_left_increasing_d           : @check_left_increasing S
; mono_right_increasing_d          : @check_right_increasing S

}. 

Record os_monotone_increasing_certificates {S: Type} := 
{
  mono_inc_left_monotonic              : @assert_left_monotone S
; mono_inc_right_monotonic             : @assert_right_monotone S 
; mono_inc_left_increasing             : @assert_left_increasing S
; mono_inc_right_increasing            : @assert_right_increasing S
}.

Record qosg {S : Type} := {
  qosg_eqv              : @eqv S 
; qosg_lte              : @brel S 
; qosg_times            : @binary_op S 
; qosg_lte_certs        : @qo_certificates S 
; qosg_times_certs      : @sg_certificates S 
; qosg_bottom_top_certs : @os_qo_bottom_top_certs S 
; qosg_certs            : @os_certificates S 
; qosg_ast              : cas_os_ast
}.

Record posg {S : Type} := {
  posg_eqv              : @eqv S 
; posg_lte              : @brel S 
; posg_times            : @binary_op S 
; posg_lte_certs        : @po_certificates S 
; posg_times_certs      : @sg_certificates S 
; posg_bottom_top_certs : @os_bottom_top_certs S 
; posg_certs            : @os_certificates S 
; posg_ast              : cas_os_ast
}.

Record monotone_posg {S : Type} := {
  mposg_eqv          : @eqv S 
; mposg_lte          : @brel S 
; mposg_times        : @binary_op S 
; mposg_lte_certs    : @po_certificates S 
; mposg_times_certs  : @sg_certificates S 
; mposg_top_bottom   : @os_bottom_top_certs S 
; mposg_certs        : @os_monotone_certificates S 
; mposg_ast          : cas_os_ast
}.

Record monotone_increasing_posg (S : Type) := {
  miposg_eqv          : @eqv S 
; miposg_lte          : @brel S 
; miposg_times        : @binary_op S 
; miposg_lte_certs    : @po_certificates S 
; miposg_times_certs  : @sg_certificates S 
; miposg_top_bottom   : @os_bottom_top_certs S 
; miposg_certs        : @os_monotone_increasing_certificates S 
; miposg_ast          : cas_os_ast
}.

Record bounded_monotone_increasing_posg {S : Type} :=
{
  bmiposg_eqv         : @eqv S 
; bmiposg_lte         : @brel S 
; bmiposg_times       : @binary_op S 
; bmiposg_lte_certs   : @po_certificates S 
; bmiposg_times_certs : @sg_certificates S 
; bmiposg_top_bottom  : @os_bounded_certs S 
; bmiposg_certs       : @os_monotone_increasing_certificates S 
; bmiposg_ast         : cas_os_ast 
}.

(*
Section Projections.
Definition po_from_bounded_monotone_increasing_posg
           {S : Type}
           (P : @bounded_monotone_increasing_posg S) : @po_bounded S :=
let B := bmiposg_top_bottom P in 
{|
  po_bd_eqv           := bmiposg_eqv P 
; po_bd_lte           := bmiposg_lte P 
; po_bd_exists_top    := match bounded_bottom_id B with
                      | Assert_Os_Exists_Bottom_Id_Equal bot_id => Assert_Exists_Top bot_id
                      end
; po_bd_exists_bottom := match bounded_top_ann B with 
                      | Assert_Os_Exists_Top_Ann_Equal top_ann => Assert_Exists_Bottom top_ann
                      end
; po_bd_certs         := bmiposg_lte_certs P 
; po_bd_ast           := Ast_or_of_os (bmiposg_ast P)
|}.  

End Projections.   
*) 
End CAS.

Section MCAS.

Inductive os_mcas {S : Type} :=
| OS_Error                            : list string                         -> @os_mcas S
| OS_qosg                             : @qosg S                             -> @os_mcas S
| OS_posg                             : @posg S                             -> @os_mcas S                     
| OS_monotone_posg                    : @monotone_posg S                    -> @os_mcas S
| OS_monotone_increasing_posg         : @monotone_increasing_posg S         -> @os_mcas S
| OS_bounded_monotone_increasing_posg : @bounded_monotone_increasing_posg S -> @os_mcas S
.

(* HELP : how to classify OS_bounded_monotone_increasing_posg_CI ??? *)

Definition os_classify_bounded_monotone_increasing_posg {S : Type} (A : @bounded_monotone_increasing_posg S) : @os_mcas S :=
  OS_bounded_monotone_increasing_posg A.  


Definition os_classify_monotone_increasing_posg {S : Type} (A : @monotone_increasing_posg S) : @os_mcas S :=
  match bottom_top_bottom_id_d (miposg_top_bottom _ A),
        bottom_top_top_ann_d (miposg_top_bottom _ A) 
  with 
  | Bottom_Id_Cert_Equal P, Top_Ann_Cert_Equal Q =>
    os_classify_bounded_monotone_increasing_posg 
     {|
         bmiposg_eqv          := miposg_eqv _ A 
       ; bmiposg_lte          := miposg_lte _ A 
       ; bmiposg_times        := miposg_times _ A 
       ; bmiposg_lte_certs    := miposg_lte_certs _ A 
       ; bmiposg_times_certs  := miposg_times_certs _ A 
       ; bmiposg_top_bottom   := {| bounded_bottom_id := Assert_Os_Exists_Bottom_Id_Equal P;
                                    bounded_top_ann := Assert_Os_Exists_Top_Ann_Equal Q|}
       ; bmiposg_certs        := miposg_certs _ A 
       ; bmiposg_ast          := miposg_ast _ A 
     |}
  | _ , _ => OS_monotone_increasing_posg A
  end. 

Definition os_classify_monotone_posg {S : Type} (A : @monotone_posg S) : @os_mcas S :=
  let P := mposg_certs A in 
  match mono_left_increasing_d _ P, mono_right_increasing_d _ P 
  with 
  | Certify_Left_Increasing, Certify_Right_Increasing => 
    os_classify_monotone_increasing_posg 
     {|
         miposg_eqv          := mposg_eqv A 
       ; miposg_lte          := mposg_lte A 
       ; miposg_times        := mposg_times A 
       ; miposg_lte_certs   := mposg_lte_certs A 
       ; miposg_times_certs := mposg_times_certs A 
       ; miposg_top_bottom   := mposg_top_bottom A 
       ; miposg_certs       := {|
                                     mono_inc_left_monotonic   := mono_left_monotonic _ P 
                                   ; mono_inc_right_monotonic  := mono_right_monotonic _ P 
                                   ; mono_inc_left_increasing  := Assert_Left_Increasing
                                   ; mono_inc_right_increasing := Assert_Right_Increasing
                                   |} 
       ; miposg_ast          := mposg_ast A 
     |}
  | _ , _ => OS_monotone_posg A
  end. 


Definition os_classify_posg {S : Type} (A : @posg S) : @os_mcas S :=
  let P := posg_certs A in 
  match posg_left_monotonic_d P, posg_right_monotonic_d P 
  with 
  | Certify_Left_Monotone, Certify_Right_Monotone => 
    os_classify_monotone_posg 
     {|
         mposg_eqv          := posg_eqv A 
       ; mposg_lte          := posg_lte A 
       ; mposg_times        := posg_times A 
       ; mposg_lte_certs   := posg_lte_certs A 
       ; mposg_times_certs := posg_times_certs A 
       ; mposg_top_bottom   := posg_bottom_top_certs A 
       ; mposg_certs       := {|
                                     mono_left_monotonic   := Assert_Left_Monotone 
                                   ; mono_right_monotonic  := Assert_Right_Monotone 
                                   ; mono_left_increasing_d  := posg_left_increasing_d P 
                                   ; mono_right_increasing_d := posg_right_increasing_d P 
                                   |} 
       ; mposg_ast          := posg_ast A 
     |}
  | _ , _ => OS_posg A
  end.


Definition os_exists_bottom_id_certificate_from_os_exists_qo_bottom_id_certificate {S : Type} 
           (d : @os_exists_qo_bottom_id_certificate S) :
                @os_exists_bottom_id_certificate S :=   
match d with
| Qo_Bottom_Id_Cert_None             => Bottom_Id_Cert_None 
| Qo_Bottom_Id_Cert_Bottom_None b    => Bottom_Id_Cert_Bottom_None b 
| Qo_Bottom_Id_Cert_None_Id i        => Bottom_Id_Cert_None_Id i 
| Qo_Bottom_Id_Cert_Equal s          => Bottom_Id_Cert_Equal s 
| Qo_Bottom_Id_Cert_Not_Equal (b, i) => Bottom_Id_Cert_Not_Equal  (b, i)
    
end. 
Definition os_exists_top_ann_certificate_from_os_exists_qo_top_ann_certificate {S : Type} 
           (d : @os_exists_qo_top_ann_certificate S ) :
                @os_exists_top_ann_certificate S :=   
match d with
| Qo_Top_Ann_Cert_None            => Top_Ann_Cert_None 
| Qo_Top_Ann_Cert_Top_None t      => Top_Ann_Cert_Top_None t 
| Qo_Top_Ann_Cert_None_Ann a      => Top_Ann_Cert_None_Ann a
| Qo_Top_Ann_Cert_Equal s         => Top_Ann_Cert_Equal s 
| Qo_Top_Ann_Cert_Not_Equal (t,a) => Top_Ann_Cert_Not_Equal (t, a)
    
end. 


Definition os_classify_qosg {S : Type} (A : @qosg S) : @os_mcas S :=
  let P := qosg_lte_certs A in 
  match qo_antisymmetric_d P, qo_total_d P  with 
  | Certify_Antisymmetric, Certify_Not_Total p2 =>
    os_classify_posg 
     {|
         posg_eqv          := qosg_eqv A 
       ; posg_lte          := qosg_lte A 
       ; posg_times        := qosg_times A 
       ; posg_lte_certs   :=
           {|
               po_congruence    := Assert_Brel_Congruence
             ; po_reflexive     := Assert_Reflexive
             ; po_transitive    := Assert_Transitive
             ; po_antisymmetric := Assert_Antisymmetric 
             ; po_not_total     := Assert_Not_Total p2 
           |}
       ; posg_times_certs        := qosg_times_certs A
       ; posg_bottom_top_certs   :=
           {|
             bottom_top_bottom_id_d := os_exists_bottom_id_certificate_from_os_exists_qo_bottom_id_certificate
                                           (qo_bottom_top_bottom_id_d (qosg_bottom_top_certs A))
           ; bottom_top_top_ann_d   := os_exists_top_ann_certificate_from_os_exists_qo_top_ann_certificate
                                            (qo_bottom_top_top_ann_d (qosg_bottom_top_certs A))
           |}
       ; posg_certs              := qosg_certs A 
       ; posg_ast                := qosg_ast A 
     |}
  | _ , _ => OS_qosg A
  end. 



Definition os_classify {S : Type} (A : @os_mcas S) : @os_mcas S :=
match A with
| OS_Error _                            => A
| OS_qosg B                             => os_classify_qosg B                                              
| OS_posg B                             => os_classify_posg B 
| OS_monotone_posg B                    => os_classify_monotone_posg B 
| OS_monotone_increasing_posg B         => os_classify_monotone_increasing_posg B 
| OS_bounded_monotone_increasing_posg B => os_classify_bounded_monotone_increasing_posg B
end.     


End MCAS. 
  
Section Translation.

Section Proofs.

Variables (S : Type) (eq lte : brel S) (b : binary_op S).

            
Definition P2C_os_proofs (C : os_proofs S lte b) := 
{|
  posg_left_monotonic_d            := p2c_left_monotone S lte b (A_posg_left_monotonic_d S lte b C)
; posg_right_monotonic_d           := p2c_right_monotone S lte b (A_posg_right_monotonic_d S lte b C)
; posg_left_increasing_d           := p2c_left_increasing S lte b (A_posg_left_increasing_d S lte b C)
; posg_right_increasing_d          := p2c_right_increasing S lte b (A_posg_right_increasing_d S lte b C)
|}.

Definition P2C_os_monotone_proofs (C : os_monotone_proofs S lte b) := 
{|
  mono_left_monotonic              := Assert_Left_Monotone 
; mono_right_monotonic             := Assert_Right_Monotone 
; mono_left_increasing_d           := p2c_left_increasing S lte b (A_mono_left_increasing_d S lte b C)
; mono_right_increasing_d          := p2c_right_increasing S lte b (A_mono_right_increasing_d S lte b C)
|}.


Definition P2C_os_monotone_increasing_proofs (C : os_monotone_increasing_proofs S lte b) := 
{|
  mono_inc_left_monotonic            := @Assert_Left_Monotone S
; mono_inc_right_monotonic           := @Assert_Right_Monotone S
; mono_inc_left_increasing           := @Assert_Left_Increasing S
; mono_inc_right_increasing          := @Assert_Right_Increasing S 
|}.



Definition P2C_os_qo_bottom_top_proofs  (P : os_qo_bottom_top_proofs S eq lte b) :=
{|
  qo_bottom_top_bottom_id_d := p2c_os_exists_qo_bottom_id_decidable _ _ _ _ (A_qo_bottom_top_bottom_id_d S eq lte b P)
; qo_bottom_top_top_ann_d   := p2c_os_exists_qo_top_ann_decidable _ _ _ _ (A_qo_bottom_top_top_ann_d S eq lte b P)
|}.

Definition P2C_os_bottom_top_proofs  (P : os_bottom_top_proofs S eq lte b) :=
{|
  bottom_top_bottom_id_d := p2c_os_exists_bottom_id_decidable _ _ _ _ (A_bottom_top_bottom_id_d S eq lte b P)
; bottom_top_top_ann_d   := p2c_os_exists_top_ann_decidable _ _ _ _ (A_bottom_top_top_ann_d S eq lte b P)
|}.

Definition P2C_os_bottom_is_id_proofs (P : os_bottom_is_id_proofs S eq lte b) :=
{|
  bottom_is_id           := p2c_os_exists_bottom_id_equal _ _ _ _ (A_bottom_is_id S eq lte b P)
; bottom_is_id_top_ann_d := p2c_os_exists_top_ann_decidable _ _ _ _ (A_bottom_is_id_top_ann_d S eq lte b P)
|}.

Definition P2C_os_top_is_ann_proofs (P : os_top_is_ann_proofs S eq lte b) :=
{|
  top_is_ann_bottom_id_d := p2c_os_exists_bottom_id_decidable _ _ _ _ (A_top_is_ann_bottom_id_d S eq lte b P)
; top_is_ann             := p2c_os_exists_top_ann_equal _ _ _ _ (A_top_is_ann S eq lte b P)
|}.

Definition P2C_os_bounded_proofs (P : os_bounded_proofs S eq lte b) :=
{|
  bounded_bottom_id := p2c_os_exists_bottom_id_equal _ _ _ _ (A_bounded_bottom_id S eq lte b P)
; bounded_top_ann   := p2c_os_exists_top_ann_equal  _ _ _ _ (A_bounded_top_ann S eq lte b P)
|}.


End Proofs.

Definition A2C_qosg {S : Type} (A : A_qosg S) : @qosg S := 
{|
  qosg_eqv              := A2C_eqv _ (A_qosg_eqv _ A)
; qosg_lte              := A_qosg_lte _ A 
; qosg_times            := A_qosg_times _ A 
; qosg_lte_certs        := P2C_qo _ _ (A_qosg_lte_proofs _ A)
; qosg_times_certs      := P2C_sg _ _ (A_qosg_times_proofs _ A)
; qosg_bottom_top_certs := P2C_os_qo_bottom_top_proofs _ _ _ _ (A_qosg_bottom_top_proofs _ A) 
; qosg_certs            := P2C_os_proofs _ _ _ (A_qosg_proofs _ A)
; qosg_ast              := A_qosg_ast _ A 
|}.

Definition A2C_posg {S : Type} (A : A_posg S) : @posg S := 
{|
  posg_eqv              := A2C_eqv _ (A_posg_eqv _ A)
; posg_lte              := A_posg_lte _ A 
; posg_times            := A_posg_times _ A 
; posg_lte_certs        := P2C_po _ _ (A_posg_lte_proofs _ A)
; posg_times_certs      := P2C_sg _ _ (A_posg_times_proofs _ A)
; posg_bottom_top_certs := P2C_os_bottom_top_proofs _ _ _ _ (A_posg_bottom_top_proofs _ A) 
; posg_certs            := P2C_os_proofs _ _ _ (A_posg_proofs _ A)
; posg_ast              := A_posg_ast _ A 
|}.


Definition A2C_monotone_posg {S : Type} (A : A_monotone_posg S) : @monotone_posg S := 
{|
  mposg_eqv              := A2C_eqv _ (A_mposg_eqv _ A)
; mposg_lte              := A_mposg_lte _ A 
; mposg_times            := A_mposg_times _ A 
; mposg_lte_certs        := P2C_po _ _ (A_mposg_lte_proofs _ A)
; mposg_times_certs      := P2C_sg _ _ (A_mposg_times_proofs _ A)
; mposg_top_bottom       := P2C_os_bottom_top_proofs _ _ _ _ (A_mposg_top_bottom _ A) 
; mposg_certs            := P2C_os_monotone_proofs _ _ _ (A_mposg_proofs _ A)
; mposg_ast              := A_mposg_ast _ A 
|}.


Definition A2C_monotone_increasing_posg {S : Type} (A : A_monotone_increasing_posg S) : @monotone_increasing_posg S := 
{|
  miposg_eqv              := A2C_eqv _ (A_miposg_eqv _ A)
; miposg_lte              := A_miposg_lte _ A 
; miposg_times            := A_miposg_times _ A 
; miposg_lte_certs        := P2C_po _ _ (A_miposg_lte_proofs _ A)
; miposg_times_certs      := P2C_sg _ _ (A_miposg_times_proofs _ A)
; miposg_top_bottom       := P2C_os_bottom_top_proofs _ _ _ _ (A_miposg_top_bottom _ A) 
; miposg_certs            := P2C_os_monotone_increasing_proofs _ _ _ (A_miposg_proofs _ A)
; miposg_ast              := A_miposg_ast _ A 
|}.

Definition A2C_bounded_monotone_increasing_posg {S : Type}
    (A : A_bounded_monotone_increasing_posg S) : @bounded_monotone_increasing_posg S := 
{|
  bmiposg_eqv              := A2C_eqv _ (A_bmiposg_eqv _ A)
; bmiposg_lte              := A_bmiposg_lte _ A 
; bmiposg_times            := A_bmiposg_times _ A 
; bmiposg_lte_certs        := P2C_po _ _ (A_bmiposg_lte_proofs _ A)
; bmiposg_times_certs      := P2C_sg _ _ (A_bmiposg_times_proofs _ A)
; bmiposg_top_bottom       := P2C_os_bounded_proofs _ _ _ _ (A_bmiposg_top_bottom _ A) 
; bmiposg_certs            := P2C_os_monotone_increasing_proofs _ _ _ (A_bmiposg_proofs _ A)
; bmiposg_ast              := A_bmiposg_ast _ A 
|}.

Local Open Scope string_scope.
Local Open Scope list_scope. 

Definition A2C_mcas_os {S : Type} (A : @A_os_mcas S) := 
match A with 
| A_OS_Error _ sl                           => OS_Error sl
| A_OS_qosg  _ B                            => OS_qosg (A2C_qosg B) 
| A_OS_posg  _ B                            => OS_posg (A2C_posg B) 
| A_OS_monotone_posg _ B                    => OS_monotone_posg (A2C_monotone_posg B) 
| A_OS_monotone_increasing_posg _ B         => OS_monotone_increasing_posg (A2C_monotone_increasing_posg B) 
| A_OS_bounded_monotone_increasing_posg _ B => OS_bounded_monotone_increasing_posg (A2C_bounded_monotone_increasing_posg B)
| A_OS_bounded_join_semilattice _ _         => OS_Error ("A2C_mcas_os : case for bounded_join_semilattice not yet implemented" :: nil) 
end. 

End Translation.   

Section Verify.
End Verify.   
