Require Import Coq.Strings.String.
Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.sg.structures.
Require Import CAS.coq.bs.properties.

(* bi-semigroups *) 

Section ACAS.

Record A_bs_id_ann_properties {S: Type} (eq : brel S) (plus : binary_op S) (times : binary_op S) := 
{
  A_id_ann_plus_times_d       : A_bs_exists_id_ann_decidable eq plus times (* 5 possibilities *)
; A_id_ann_times_plus_d       : A_bs_exists_id_ann_decidable eq times plus (* 5 possibilities *)                                                        
}.

Record A_bs_id_ann_bounded_properties {S: Type} (eq : brel S) (plus : binary_op S) (times : binary_op S) := 
{
  A_bounded_plus_id_is_times_ann : A_bs_exists_id_ann_equal eq plus times 
; A_bounded_times_id_is_plus_ann : A_bs_exists_id_ann_equal eq times plus 
}.

Record A_bs_properties {S: Type} (eq : brel S) (plus : binary_op S) (times : binary_op S) := 
{
  A_bs_left_distributive_d  : A_bs_left_distributive_decidable eq plus times 
; A_bs_right_distributive_d : A_bs_right_distributive_decidable eq plus times 
; A_bs_left_absorptive_d    : A_bs_left_absorptive_decidable eq plus times 
; A_bs_right_absorptive_d   : A_bs_right_absorptive_decidable eq plus times 
}.

Record A_pa_properties {S: Type} (eq : brel S) (plus : binary_op S) (times : binary_op S) := 
{
  A_pa_left_distributive  : A_bs_left_distributive eq plus times 
; A_pa_right_distributive : A_bs_right_distributive eq plus times 
}.

Record A_bs {S : Type} := {
  A_bs_eqv          : A_eqv S 
; A_bs_plus         : binary_op S 
; A_bs_times        : binary_op S 
; A_bs_plus_props   : sg_C_proofs S (A_eqv_eq S A_bs_eqv) A_bs_plus 
; A_bs_times_props  : sg_proofs S (A_eqv_eq S A_bs_eqv) A_bs_times   
; A_bs_id_ann_props : A_bs_id_ann_properties (A_eqv_eq S A_bs_eqv) A_bs_plus A_bs_times                                 
; A_bs_props        : A_bs_properties (A_eqv_eq S A_bs_eqv) A_bs_plus A_bs_times
; A_bs_ast          : cas_bs_ast
}.

Record A_bs_CS {S : Type} := {
  A_bs_CS_eqv          : A_eqv S 
; A_bs_CS_plus         : binary_op S 
; A_bs_CS_times        : binary_op S 
; A_bs_CS_plus_props   : sg_CS_proofs S (A_eqv_eq S A_bs_CS_eqv) A_bs_CS_plus
; A_bs_CS_times_props  : sg_proofs S    (A_eqv_eq S A_bs_CS_eqv) A_bs_CS_times
; A_bs_CS_id_ann_props : A_bs_id_ann_properties (A_eqv_eq S A_bs_CS_eqv) A_bs_CS_plus A_bs_CS_times
; A_bs_CS_props        : A_bs_properties (A_eqv_eq S A_bs_CS_eqv) A_bs_CS_plus A_bs_CS_times
; A_bs_CS_ast          : cas_bs_ast
}.

Record A_bs_CI {S : Type} := {
  A_bs_CI_eqv           : A_eqv S 
; A_bs_CI_plus          : binary_op S 
; A_bs_CI_times         : binary_op S 
; A_bs_CI_plus_props    : sg_CI_proofs S (A_eqv_eq S A_bs_CI_eqv) A_bs_CI_plus
; A_bs_CI_times_props   : sg_proofs S    (A_eqv_eq S A_bs_CI_eqv) A_bs_CI_times
; A_bs_CI_id_ann_props  : A_bs_id_ann_properties (A_eqv_eq S A_bs_CI_eqv) A_bs_CI_plus A_bs_CI_times
; A_bs_CI_props         : A_bs_properties (A_eqv_eq S A_bs_CI_eqv) A_bs_CI_plus A_bs_CI_times
; A_bs_CI_ast           : cas_bs_ast
}.


Record A_path_algebra {S : Type} := {
  A_pa_eqv           : A_eqv S 
; A_pa_plus          : binary_op S 
; A_pa_times         : binary_op S 
; A_pa_plus_props    : sg_CI_proofs S (A_eqv_eq S A_pa_eqv) A_pa_plus
; A_pa_times_props   : sg_proofs S    (A_eqv_eq S A_pa_eqv) A_pa_times
; A_pa_id_ann_props  : A_bs_id_ann_bounded_properties (A_eqv_eq S A_pa_eqv) A_pa_plus A_pa_times
; A_pa_props         : A_pa_properties (A_eqv_eq S A_pa_eqv) A_pa_plus A_pa_times
; A_pa_ast           : cas_bs_ast
}.


Record A_selective_path_algebra {S : Type} := {
  A_spa_eqv           : A_eqv S 
; A_spa_plus          : binary_op S 
; A_spa_times         : binary_op S 
; A_spa_plus_props    : sg_CS_proofs S (A_eqv_eq S A_spa_eqv) A_spa_plus
; A_spa_times_props   : sg_proofs S    (A_eqv_eq S A_spa_eqv) A_spa_times
; A_spa_id_ann_props  : A_bs_id_ann_bounded_properties (A_eqv_eq S A_spa_eqv) A_spa_plus A_spa_times
; A_spa_props         : A_pa_properties (A_eqv_eq S A_spa_eqv) A_spa_plus A_spa_times
; A_spa_ast           : cas_bs_ast
}.

End ACAS.

Section AMCAS.

Inductive A_below_bs_CS {S : Type} := 
| A_Below_bs_CS_top        : @A_bs_CS S          -> @A_below_bs_CS S
| A_Below_bs_CS_spa        : @A_selective_path_algebra S -> @A_below_bs_CS S                                                                   
.

Inductive A_below_bs_CI {S : Type} := 
| A_Below_bs_CI_top        : @A_bs_CI S        -> @A_below_bs_CI S
| A_Below_bs_CI_pa         : @A_path_algebra S -> @A_below_bs_CI S 
.

Inductive A_below_bs {S : Type} := 
| A_Below_bs_top          : @A_bs S             -> @A_below_bs S
| A_Below_bs_bs_CS        : @A_below_bs_CS S    -> @A_below_bs S
| A_Below_bs_bs_CI        : @A_below_bs_CI S    -> @A_below_bs S                                                               
.

Inductive A_bs_mcas {S : Type} := 
| A_MCAS_bs_Error        : list string     -> @A_bs_mcas S
| A_MCAS_bs              : @A_below_bs S   -> @A_bs_mcas S
. 

End AMCAS.                                                                   


Section CAS.

Record bs_id_ann_properties {S: Type} := 
{
  id_ann_plus_times_d       : @bs_exists_id_ann_decidable S
; id_ann_times_plus_d       : @bs_exists_id_ann_decidable S
}.

Record bs_id_ann_bounded_properties {S: Type}  := 
{
  bounded_plus_id_is_times_ann : @bs_exists_id_ann_equal S
; bounded_times_id_is_plus_ann : @bs_exists_id_ann_equal S
}.


Record bs_properties {S: Type} := 
{
  bs_left_distributive_d   : @bs_left_distributive_decidable S
; bs_right_distributive_d  : @bs_right_distributive_decidable S
; bs_left_absorptive_d     : @bs_left_absorptive_decidable S
; bs_right_absorptive_d    : @bs_right_absorptive_decidable S
}.

Record pa_properties {S: Type} := 
{
  pa_left_distributive  : @bs_left_distributive S 
; pa_right_distributive : @bs_right_distributive S
}.

  
Record bs {S : Type} := {
  bs_eqv           : @eqv S
; bs_plus          : binary_op S 
; bs_times         : binary_op S 
; bs_plus_props    : @sg_C_certificates S
; bs_times_props   : @sg_certificates S 
; bs_id_ann_props  : @bs_id_ann_properties S
; bs_props         : @bs_properties S
; bs_ast           : cas_bs_ast
}.

Record bs_CS {S : Type} := {
  bs_CS_eqv          : @eqv S
; bs_CS_plus         : binary_op S 
; bs_CS_times        : binary_op S 
; bs_CS_plus_props   : @sg_CS_certificates S
; bs_CS_times_props  : @sg_certificates S
; bs_CS_id_ann_props : @bs_id_ann_properties S
; bs_CS_props        : @bs_properties S
; bs_CS_ast          : cas_bs_ast
}.

Record bs_CI {S : Type} := {
  bs_CI_eqv          : @eqv S
; bs_CI_plus         : binary_op S 
; bs_CI_times        : binary_op S 
; bs_CI_plus_props   : @sg_CI_certificates S
; bs_CI_times_props  : @sg_certificates S
; bs_CI_id_ann_props : @bs_id_ann_properties S
; bs_CI_props        : @bs_properties S
; bs_CI_ast          : cas_bs_ast
  }.


Record path_algebra {S : Type} := {
  pa_eqv           : @eqv S 
; pa_plus          : binary_op S 
; pa_times         : binary_op S 
; pa_plus_props    : @sg_CI_certificates S 
; pa_times_props   : @sg_certificates S    
; pa_id_ann_props  : @bs_id_ann_bounded_properties S
; pa_props         : @pa_properties S
; pa_ast           : cas_bs_ast
}.


Record selective_path_algebra {S : Type} := {
  spa_eqv           : @eqv S 
; spa_plus          : binary_op S 
; spa_times         : binary_op S 
; spa_plus_props    : @sg_CS_certificates S 
; spa_times_props   : @sg_certificates S    
; spa_id_ann_props  : @bs_id_ann_bounded_properties S
; spa_props         : @pa_properties S
; spa_ast           : cas_bs_ast
}.


End CAS. 

Section MCAS.

Inductive below_bs_CS {S : Type} := 
| Below_bs_CS_top : @bs_CS S                  -> @below_bs_CS S
| Below_bs_CS_spa : @selective_path_algebra S -> @below_bs_CS S                                                             
.

Inductive below_bs_CI {S : Type} := 
| Below_bs_CI_top        : @bs_CI S          -> @below_bs_CI S
| Below_bs_CI_pa         : @path_algebra S -> @below_bs_CI S
.

Inductive below_bs {S : Type} := 
| Below_bs_top          : @bs S             -> @below_bs S
| Below_bs_bs_CS        : @below_bs_CS S    -> @below_bs S
| Below_bs_bs_CI        : @below_bs_CI S    -> @below_bs S                                                               
.

Inductive bs_mcas {S : Type} := 
| MCAS_bs_Error        : list string     -> @bs_mcas S
| MCAS_bs              : @below_bs S   -> @bs_mcas S
. 

End MCAS.                                                                   

Section Translation. 

Definition P2C_id_ann
    (S : Type)
    (r : brel S)
    (b1 b2 : binary_op S)
    (P : A_bs_id_ann_properties r b1 b2) : 
              @bs_id_ann_properties S := 
{|
  id_ann_plus_times_d := p2c_exists_id_ann _ _ b1 b2 (A_id_ann_plus_times_d _ _ _ P)
; id_ann_times_plus_d := p2c_exists_id_ann _ _ b2 b1 (A_id_ann_times_plus_d _ _ _ P)
|}.

Definition P2C_bs_id_ann_bounded_properties
    (S : Type)
    (r : brel S)
    (b1 b2 : binary_op S)
    (P : A_bs_id_ann_bounded_properties r b1 b2) : 
  @bs_id_ann_bounded_properties S :=
{|
  bounded_plus_id_is_times_ann := p2c_bs_exists_id_ann_equal _ _ _ _ (A_bounded_plus_id_is_times_ann _ _ _ P)
; bounded_times_id_is_plus_ann := p2c_bs_exists_id_ann_equal _ _ _ _ (A_bounded_times_id_is_plus_ann _ _ _ P)
|}.
  

Definition P2C_bs {S : Type} (r : brel S) (w : S) (b1 b2 : binary_op S)
             (R : A_bs_properties r b1 b2) : @bs_properties S := 
{|
  bs_left_distributive_d      :=
    p2c_bs_left_distributive_decidable r w b1 b2 (A_bs_left_distributive_d r b1 b2 R)
; bs_right_distributive_d     :=
    p2c_bs_right_distributive_decidable r w b1 b2 (A_bs_right_distributive_d r b1 b2 R)
; bs_left_absorptive_d   :=
    p2c_bs_left_absorptive_decidable r w b1 b2 (A_bs_left_absorptive_d r b1 b2 R)
; bs_right_absorptive_d  :=
    p2c_bs_right_absorptive_decidable r w b1 b2 (A_bs_right_absorptive_d r b1 b2 R)
|}.


Definition P2C_pa_properties {S : Type} (r : brel S) (w : S) (b1 b2 : binary_op S)
             (R : A_pa_properties r b1 b2) : @pa_properties S := 
{|
  pa_left_distributive  := p2c_bs_left_distributive _ w _ _ (A_pa_left_distributive _ _ _ R)
; pa_right_distributive := p2c_bs_right_distributive _ w _ _ (A_pa_right_distributive _ _ _ R)
|}.

Definition A2C_bs {S : Type} (R : @A_bs S) : @bs S := 
{|
  bs_eqv         := A2C_eqv S (A_bs_eqv R)
; bs_plus        := A_bs_plus R 
; bs_times       := A_bs_times R 
; bs_plus_props  := P2C_sg_C (A_eqv_eq S (A_bs_eqv R)) 
                           (A_bs_plus R) 
                           (A_bs_plus_props R)
; bs_times_props := P2C_sg (A_eqv_eq S (A_bs_eqv R)) 
                           (A_bs_times R) 
                           (A_bs_times_props R)
; bs_id_ann_props := P2C_id_ann S (A_eqv_eq S (A_bs_eqv R)) 
                                   (A_bs_plus R) 
                                   (A_bs_times R) 
                                   (A_bs_id_ann_props R)
; bs_props       := P2C_bs (A_eqv_eq S (A_bs_eqv R))
                           (A_eqv_witness S (A_bs_eqv R)) 
                           (A_bs_plus R) 
                           (A_bs_times R) 
                           (A_bs_props R)
; bs_ast        := A_bs_ast R
|}.

Definition A2C_bs_CS {S : Type} (R : @A_bs_CS S) : @bs_CS S := 
{|
  bs_CS_eqv         := A2C_eqv S (A_bs_CS_eqv R)
; bs_CS_plus        := A_bs_CS_plus R 
; bs_CS_times       := A_bs_CS_times R 
; bs_CS_plus_props  := P2C_sg_CS (A_eqv_eq S (A_bs_CS_eqv R)) 
                                (A_bs_CS_plus R) 
                                (A_bs_CS_plus_props R)
; bs_CS_times_props := P2C_sg  (A_eqv_eq S (A_bs_CS_eqv R)) 
                                (A_bs_CS_times R) 
                                (A_bs_CS_times_props R)
; bs_CS_id_ann_props := P2C_id_ann S (A_eqv_eq S (A_bs_CS_eqv R)) 
                                   (A_bs_CS_plus R) 
                                   (A_bs_CS_times R) 
                                   (A_bs_CS_id_ann_props R)
; bs_CS_props       := P2C_bs (A_eqv_eq S (A_bs_CS_eqv R))
                              (A_eqv_witness S (A_bs_CS_eqv R)) 
                                   (A_bs_CS_plus R) 
                                   (A_bs_CS_times R) 
                                   (A_bs_CS_props R)
; bs_CS_ast        := A_bs_CS_ast R
|}.


Definition A2C_bs_CI {S : Type} (R : @A_bs_CI S) : @bs_CI S := 
{|
  bs_CI_eqv         := A2C_eqv S (A_bs_CI_eqv R)
; bs_CI_plus        := A_bs_CI_plus R 
; bs_CI_times       := A_bs_CI_times R 
; bs_CI_plus_props  := P2C_sg_CI (A_eqv_eq S (A_bs_CI_eqv R)) 
                                (A_bs_CI_plus R) 
                                (A_bs_CI_plus_props R)
; bs_CI_times_props := P2C_sg  (A_eqv_eq S (A_bs_CI_eqv R)) 
                                (A_bs_CI_times R) 
                                (A_bs_CI_times_props R)
; bs_CI_id_ann_props := P2C_id_ann S (A_eqv_eq S (A_bs_CI_eqv R)) 
                                   (A_bs_CI_plus R) 
                                   (A_bs_CI_times R) 
                                   (A_bs_CI_id_ann_props R)
; bs_CI_props       := P2C_bs (A_eqv_eq S (A_bs_CI_eqv R))
                              (A_eqv_witness S (A_bs_CI_eqv R)) 
                                   (A_bs_CI_plus R) 
                                   (A_bs_CI_times R) 
                                   (A_bs_CI_props R)
; bs_CI_ast        := A_bs_CI_ast R
|}.



Definition A2C_path_algebra {S : Type} (R : @A_path_algebra S) : @path_algebra S := 
{|
  pa_eqv         := A2C_eqv S (A_pa_eqv R)
; pa_plus        := A_pa_plus R 
; pa_times       := A_pa_times R 
; pa_plus_props  := P2C_sg_CI (A_eqv_eq S (A_pa_eqv R)) 
                           (A_pa_plus R) 
                           (A_pa_plus_props R)
; pa_times_props := P2C_sg (A_eqv_eq S (A_pa_eqv R)) 
                           (A_pa_times R) 
                           (A_pa_times_props R)
; pa_id_ann_props := P2C_bs_id_ann_bounded_properties S
                       (A_eqv_eq S (A_pa_eqv R)) 
                       (A_pa_plus R) 
                       (A_pa_times R) 
                       (A_pa_id_ann_props R)
; pa_props       := P2C_pa_properties
                      (A_eqv_eq S (A_pa_eqv R))
                      (A_eqv_witness S (A_pa_eqv R)) 
                      (A_pa_plus R) 
                      (A_pa_times R) 
                      (A_pa_props R)
; pa_ast        := A_pa_ast R
|}.


Definition A2C_selective_path_algebra {S : Type}
  (R : @A_selective_path_algebra S) : @selective_path_algebra S := 
{|
  spa_eqv         := A2C_eqv S (A_spa_eqv R)
; spa_plus        := A_spa_plus R 
; spa_times       := A_spa_times R 
; spa_plus_props  := P2C_sg_CS (A_eqv_eq S (A_spa_eqv R)) 
                           (A_spa_plus R) 
                           (A_spa_plus_props R)
; spa_times_props := P2C_sg (A_eqv_eq S (A_spa_eqv R)) 
                           (A_spa_times R) 
                           (A_spa_times_props R)
; spa_id_ann_props := P2C_bs_id_ann_bounded_properties S
                       (A_eqv_eq S (A_spa_eqv R)) 
                       (A_spa_plus R) 
                       (A_spa_times R) 
                       (A_spa_id_ann_props R)
; spa_props       := P2C_pa_properties
                       (A_eqv_eq S (A_spa_eqv R))
                       (A_eqv_witness S (A_spa_eqv R)) 
                      (A_spa_plus R) 
                      (A_spa_times R) 
                      (A_spa_props R)
; spa_ast        := A_spa_ast R
|}.


Definition A2C_below_bs_CS
           {S : Type}
           (A : @A_below_bs_CS S) : @below_bs_CS S :=
match A with 
| A_Below_bs_CS_top B => Below_bs_CS_top (A2C_bs_CS B)
| A_Below_bs_CS_spa B => Below_bs_CS_spa (A2C_selective_path_algebra B)                                         
end.

Definition A2C_below_bs_CI
           {S : Type}
           (A : @A_below_bs_CI S) : @below_bs_CI S :=
match A with 
| A_Below_bs_CI_top B => Below_bs_CI_top (A2C_bs_CI B)
| A_Below_bs_CI_pa B  => Below_bs_CI_pa (A2C_path_algebra B)                                          
end.

Definition A2C_below_bs
           {S : Type}
           (A : @A_below_bs S) : @below_bs S :=
match A with 
| A_Below_bs_top B  => Below_bs_top (A2C_bs B)
| A_Below_bs_bs_CS B => Below_bs_bs_CS (A2C_below_bs_CS B)
| A_Below_bs_bs_CI B => Below_bs_bs_CI (A2C_below_bs_CI B)                                     
end.

Definition A2C_bs_mcas
           {S : Type}
           (A : @A_bs_mcas S) : @bs_mcas S :=
match A with
| A_MCAS_bs B        => MCAS_bs (A2C_below_bs B)
| A_MCAS_bs_Error sl => MCAS_bs_Error sl
end.

  
End Translation. 

