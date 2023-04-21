Require Import Coq.Strings.String.
Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast. 
Require Import CAS.coq.eqv.structures. 
Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures. 
Require Import CAS.coq.tr.structures.

Require Import CAS.coq.st.properties.

(* SLT = Semigroup with a Left Transform 

Comparison to bi-semigroups (bs)

For bs, 0-stability means id(x) = ann(+), so there is no point in going around loops. 
Note this implies absorption: 
    a (+) (a (x) b) = a (x) (id (+) b) = a (x) id = a. 
However, this kind of argument does not work for slt. 
slt_absorptive means 
    for all l, s, s = s (+) (l |> s). 
This cannot be derived from properties of ann(+), etc. 
We do want to know if there exists ann(+). But note that it makes no
sence for this to be an id of the multiplicative component, 
   "l |> ann(+) = l" <<< this is a type error, l has type L, not S. 

We still want to know if the id(+) acts as an slt-annihilator. 
That is, if 
   for all l, l |> id(+) = id(+). 

What condition do we need to guarantee that an slt will terminate 
using the iterative algorithm? 

    A^<0> = I   (so need id(+) and ann(+) to build this matrix) 
    A^<k+1> = (A |> A^<k>) (+) I 

    where 

    (A |> B)[i,j] = (+)_q A[i, q] |> B[q, j]. 

Definition.  The left-weight lw(p) of a path p is defined as

lw([]) = ann(+) 
lw((i, j) p) = A[i,j] |> lw(p) 


Claim : A^<k>[i,j] = the best left-weight for all paths from i to j with at most k arcs. 
Proof : induction. 

Definition. p |> s. 

   [] |> s = s 
   ((i, j) p) |> s = A[i,j] |> (p |> s)

Note that lw(p1 p2) = p1 |> lw(p2). 

How can we eliminate loops?   Suppose p2 is a loop and 

    p = p1 p2 p3 

    lw(p) = lw(p1 p2 p3) = p1 |> p2 |> lw(p3) 
    
    now,  

    (p1 |> p2 |> lw(p3)) (+) (p1 |> lw(p3)) 
    = (dist) 
    p1 |> (p2 |> lw(p3) (+) lw(p3))  
    = {by absorption: for all l, s, s = s (+) (l |> s)} 
    p1 |> lw(p3)
    = lw(p1 p3)

So, we need absorption! 

 *)



(*

1.                A_slt_proof
                     |
             ------------------------     
            |                       |
    A_slt_dioid_proof      A_slt_semiring_proof

 2.   
                  left_dioid
                     |
                  left_dioid
 3.                
              selective_left_dioid
                      |
              selective_left_dioid   
4.
              selective_left_pre_dioid
                      |
              selective_left_dioid
5.
              left_selective_semiring
                      |
              left_selective_semiring
6.
              left_idempotent_semiring
                      |
              left_idempotent_semiring
7.
              left_semiring
                  |
    ------------------------------------------
        |                             |
  left_idempotent_semiring      left_selective_semiring


8.
              left_pre_semiring
                  |
              left_semiring
9.                           
                       A_slt_CS 
                          | 
    ---------------------------------------------------------- 
                 |                              |            
    A_selective_left_pre_dioid        A_left_selective_semiring


10.
                        A_slt_CI
                          |
       -------------------------------------                
      |                             |                   
  left_dioid              left_idempotent_semiring    

11.

                A_slt_C_zero_is_ltr_ann
    ------------------------------------------------------
           |                      |              |        
    selective_left_dioid      left_dioid     left_semiring  

12.    

                        A_slt_C
                          | 
      --------------------------------------------------------------
          |                |                 |                  |
      A_slt_CS    A_slt_C_zero_is_ltr_ann     A_slt_CI     A_left_pre_semiring

13.
                        A_slt
                          |
                        A_slt_C



*)  



Section ACAS.
  
Record slt_proofs {L S : Type} (r : brel S) 
  (add : binary_op S) (ltr : ltr_type L S) :=
{
  A_slt_distributive_d 
    : slt_distributive_decidable r add ltr
; A_slt_absorptive_d 
    : slt_absorptive_decidable r add ltr
; A_slt_strictly_absorptive_d 
  : slt_strictly_absorptive_decidable r add ltr  
}.



Record left_dioid_proofs {L S : Type} (r : brel S) 
  (add : binary_op S) (ltr : ltr_type L S) :=
{
  A_left_dioid_distributive : slt_distributive r add ltr
; A_left_dioid_absorptive : slt_absorptive r add ltr                                               
; A_left_dioid_strictly_absorptive_d : slt_strictly_absorptive_decidable r add ltr 
}.


Record left_semiring_proofs {L S : Type} (r : brel S) 
  (add : binary_op S) (ltr : ltr_type L S) :=
{
  A_left_semiring_distributive  : slt_distributive r add ltr
; A_left_semiring_not_absorptive : slt_not_absorptive r add ltr                                               
}.


Record A_slt {L S : Type} :=
{
  A_slt_carrier        : A_eqv S
; A_slt_label          : A_eqv L
; A_slt_plus           : binary_op S                                               
; A_slt_trans          : ltr_type L S (* L -> (S -> S) *)
; A_slt_plus_proofs    : sg_proofs S (A_eqv_eq S A_slt_carrier) A_slt_plus                           
; A_slt_trans_proofs   :  left_transform_proofs L S 
                            (A_eqv_eq S A_slt_carrier) 
                            (A_eqv_eq L A_slt_label)  
                            A_slt_trans
; A_slt_exists_plus_ann_d : bop_exists_ann_decidable S 
                            (A_eqv_eq S A_slt_carrier) 
                            A_slt_plus                                 
; A_slt_id_ann_proofs_d  : slt_exists_id_ann_decidable 
                            (A_eqv_eq S A_slt_carrier) 
                            A_slt_plus  
                            A_slt_trans                                               
; A_slt_proofs : slt_proofs 
                  (A_eqv_eq S A_slt_carrier) 
                  A_slt_plus 
                  A_slt_trans                                  
; A_slt_ast : cas_ast
}.


Record A_slt_C {L S : Type} :=
{
    A_slt_C_carrier        : A_eqv S
  ; A_slt_C_label          : A_eqv L
  ; A_slt_C_plus           : binary_op S                                               
  ; A_slt_C_trans          : ltr_type L S (* L -> (S -> S) *)
  ; A_slt_C_plus_proofs    : sg_C_proofs S (A_eqv_eq S A_slt_C_carrier) A_slt_C_plus                           
  ; A_slt_C_trans_proofs   : left_transform_proofs L S 
                              (A_eqv_eq S A_slt_C_carrier) 
                              (A_eqv_eq L A_slt_C_label)  
                              A_slt_C_trans
  ; A_slt_C_exists_plus_ann_d : bop_exists_ann_decidable S 
                              (A_eqv_eq S A_slt_C_carrier) 
                              A_slt_C_plus                                 
  ; A_slt_C_id_ann_proofs_d  : slt_exists_id_ann_decidable 
                              (A_eqv_eq S A_slt_C_carrier) 
                              A_slt_C_plus  
                              A_slt_C_trans                                               
  ; A_slt_C_proofs : slt_proofs 
                    (A_eqv_eq S A_slt_C_carrier) 
                    A_slt_C_plus 
                    A_slt_C_trans                                  
  ; A_slt_C_ast : cas_ast
}.


Record A_slt_CS {L S : Type} :=
{
    A_slt_CS_carrier        : A_eqv S
  ; A_slt_CS_label          : A_eqv L
  ; A_slt_CS_plus           : binary_op S                                               
  ; A_slt_CS_trans          : ltr_type L S (* L -> (S -> S) *)
  ; A_slt_CS_plus_proofs    : sg_CS_proofs S (A_eqv_eq S A_slt_CS_carrier) A_slt_CS_plus                         
  ; A_slt_CS_trans_proofs   : left_transform_proofs L S 
                              (A_eqv_eq S A_slt_CS_carrier) 
                              (A_eqv_eq L A_slt_CS_label)  
                              A_slt_CS_trans
  ; A_slt_CS_exists_plus_ann_d : bop_exists_ann_decidable S 
                              (A_eqv_eq S A_slt_CS_carrier) 
                              A_slt_CS_plus                                 
  ; A_slt_CS_id_ann_proofs_d  : slt_exists_id_ann_decidable 
                              (A_eqv_eq S A_slt_CS_carrier) 
                              A_slt_CS_plus  
                              A_slt_CS_trans                                          
  ; A_slt_CS_proofs : slt_proofs 
                      (A_eqv_eq S A_slt_CS_carrier) 
                      A_slt_CS_plus 
                      A_slt_CS_trans                                  
  ; A_slt_CS_ast : cas_ast
}.


Record A_slt_CI {L S : Type} :=
{
    A_slt_CI_carrier        : A_eqv S
  ; A_slt_CI_label          : A_eqv L
  ; A_slt_CI_plus           : binary_op S                                               
  ; A_slt_CI_trans          : ltr_type L S (* L -> (S -> S) *)
  ; A_slt_CI_plus_proofs    : sg_CI_proofs S (A_eqv_eq S A_slt_CI_carrier) A_slt_CI_plus                         
  ; A_slt_CI_trans_proofs   : left_transform_proofs L S 
                              (A_eqv_eq S A_slt_CI_carrier) 
                              (A_eqv_eq L A_slt_CI_label)  
                              A_slt_CI_trans
  ; A_slt_CI_exists_plus_ann_d : bop_exists_ann_decidable S 
                              (A_eqv_eq S A_slt_CI_carrier) 
                              A_slt_CI_plus                                 
  ; A_slt_CI_id_ann_proofs_d  : slt_exists_id_ann_decidable 
                              (A_eqv_eq S A_slt_CI_carrier) 
                              A_slt_CI_plus  
                              A_slt_CI_trans                                          
  ; A_slt_CI_proofs : slt_proofs 
                    (A_eqv_eq S A_slt_CI_carrier) 
                    A_slt_CI_plus 
                    A_slt_CI_trans                                  
  ; A_slt_CI_ast : cas_ast
}.




Record A_slt_C_zero_is_ltr_ann {L S : Type} :=
{
    A_slt_C_zero_is_ltr_ann_carrier        : A_eqv S
  ; A_slt_C_zero_is_ltr_ann_label          : A_eqv L
  ; A_slt_C_zero_is_ltr_ann_plus           : binary_op S                                               
  ; A_slt_C_zero_is_ltr_ann_trans          : ltr_type L S (* L -> (S -> S) *)
  ; A_slt_C_zero_is_ltr_ann_plus_proofs    : sg_C_proofs S 
                                            (A_eqv_eq S A_slt_C_zero_is_ltr_ann_carrier) 
                                            A_slt_C_zero_is_ltr_ann_plus                           
  ; A_slt_C_zero_is_ltr_ann_trans_proofs   :  left_transform_proofs L S 
                                            (A_eqv_eq S A_slt_C_zero_is_ltr_ann_carrier) 
                                            (A_eqv_eq L A_slt_C_zero_is_ltr_ann_label)  
                                            A_slt_C_zero_is_ltr_ann_trans
  ; A_slt_C_zero_is_ltr_ann_exists_plus_ann_d : bop_exists_ann_decidable S 
                                              (A_eqv_eq S A_slt_C_zero_is_ltr_ann_carrier) 
                                              A_slt_C_zero_is_ltr_ann_plus                                 
  ; A_slt_C_zero_is_ltr_ann_id_ann_proofs  : slt_exists_id_ann_equal
                                            (A_eqv_eq S A_slt_C_zero_is_ltr_ann_carrier) 
                                            A_slt_C_zero_is_ltr_ann_plus  
                                            A_slt_C_zero_is_ltr_ann_trans                                               
  ; A_slt_C_zero_is_ltr_ann_proofs : slt_proofs 
                                    (A_eqv_eq S A_slt_C_zero_is_ltr_ann_carrier) 
                                    A_slt_C_zero_is_ltr_ann_plus 
                                    A_slt_C_zero_is_ltr_ann_trans                                  
  ; A_slt_C_zero_is_ltr_ann_ast : cas_ast
}.


Record A_selective_left_pre_dioid {L S : Type} :=
{
    A_selective_left_pre_dioid_carrier      : A_eqv S
  ; A_selective_left_pre_dioid_label        : A_eqv L
  ; A_selective_left_pre_dioid_plus         : binary_op S                                               
  ; A_selective_left_pre_dioid_trans        : ltr_type L S (* L -> (S -> S) *)
  ; A_selective_left_pre_dioid_plus_proofs  : sg_CS_proofs S 
                                              (A_eqv_eq S A_selective_left_pre_dioid_carrier) 
                                              A_selective_left_pre_dioid_plus 
  ; A_selective_left_pre_dioid_trans_proofs : left_transform_proofs L S
                                              (A_eqv_eq S A_selective_left_pre_dioid_carrier)
                                              (A_eqv_eq L A_selective_left_pre_dioid_label)
                                              A_selective_left_pre_dioid_trans
  ; A_selective_left_pre_dioid_exists_plus_ann : bop_exists_ann S
                                                (A_eqv_eq S A_selective_left_pre_dioid_carrier)
                                                A_selective_left_pre_dioid_plus                                 
  ; A_selective_left_pre_dioid_id_ann_proofs_d : slt_exists_id_ann_decidable 
                                                (A_eqv_eq S A_selective_left_pre_dioid_carrier)
                                                A_selective_left_pre_dioid_plus
                                                A_selective_left_pre_dioid_trans                        
  ; A_selective_left_pre_dioid_proofs : left_dioid_proofs 
                                        (A_eqv_eq S A_selective_left_pre_dioid_carrier)
                                        A_selective_left_pre_dioid_plus
                                        A_selective_left_pre_dioid_trans                                  
  ; A_selective_left_pre_dioid_ast : cas_ast 
}.



Record A_selective_left_dioid {L S : Type} :=
{
    A_selective_left_dioid_carrier      : A_eqv S
  ; A_selective_left_dioid_label        : A_eqv L
  ; A_selective_left_dioid_plus         : binary_op S                                               
  ; A_selective_left_dioid_trans        : ltr_type L S (* L -> (S -> S) *)
  ; A_selective_left_dioid_plus_proofs  : sg_CS_proofs S 
                                          (A_eqv_eq S A_selective_left_dioid_carrier) 
                                          A_selective_left_dioid_plus 
  ; A_selective_left_dioid_trans_proofs : left_transform_proofs L S
                                          (A_eqv_eq S A_selective_left_dioid_carrier)
                                          (A_eqv_eq L A_selective_left_dioid_label)
                                          A_selective_left_dioid_trans
  ; A_selective_left_dioid_exists_plus_ann : bop_exists_ann S
                                            (A_eqv_eq S A_selective_left_dioid_carrier)
                                            A_selective_left_dioid_plus                                 
  ; A_selective_left_dioid_id_ann_proofs  : slt_exists_id_ann_equal 
                                            (A_eqv_eq S A_selective_left_dioid_carrier)
                                            A_selective_left_dioid_plus
                                            A_selective_left_dioid_trans                        
  ; A_selective_left_dioid_proofs : left_dioid_proofs 
                                      (A_eqv_eq S A_selective_left_dioid_carrier)
                                      A_selective_left_dioid_plus
                                      A_selective_left_dioid_trans                                  
  ; A_selective_left_dioid_ast : cas_ast 
}.









Record A_left_dioid {L S : Type} :=
  {
    A_left_dioid_carrier         : A_eqv S
  ; A_left_dioid_label           : A_eqv L
  ; A_left_dioid_plus            : binary_op S                                               
  ; A_left_dioid_trans           : ltr_type L S (* L -> (S -> S) *)
  ; A_left_dioid_plus_proofs     : sg_CI_proofs S (A_eqv_eq S A_left_dioid_carrier) A_left_dioid_plus                                 
  ; A_left_dioid_trans_proofs    : left_transform_proofs L S 
                                      (A_eqv_eq S A_left_dioid_carrier) 
                                      (A_eqv_eq L A_left_dioid_label) 
                                      A_left_dioid_trans
  ; A_left_dioid_exists_plus_ann : bop_exists_ann S 
                                    (A_eqv_eq S A_left_dioid_carrier) 
                                    A_left_dioid_plus                                 
  ; A_left_dioid_id_ann_proofs   : slt_exists_id_ann_equal 
                                    (A_eqv_eq S A_left_dioid_carrier) 
                                    A_left_dioid_plus  
                                    A_left_dioid_trans 
  ; A_left_dioid_proofs          : left_dioid_proofs 
                                    (A_eqv_eq S A_left_dioid_carrier) 
                                    A_left_dioid_plus 
                                    A_left_dioid_trans 
  ; A_left_dioid_ast             : cas_ast 
  }.


Record A_left_pre_semiring {L S : Type} :=
  {
    A_left_pre_semiring_carrier         : A_eqv S
  ; A_left_pre_semiring_label           : A_eqv L
  ; A_left_pre_semiring_plus            : binary_op S                                               
  ; A_left_pre_semiring_trans           : ltr_type L S (* L -> (S -> S) *)
  ; A_left_pre_semiring_plus_proofs     : sg_C_proofs S 
                                          (A_eqv_eq S A_left_pre_semiring_carrier) 
                                          A_left_pre_semiring_plus                                 
  ; A_left_pre_semiring_trans_proofs    : left_transform_proofs L S 
                                          (A_eqv_eq S A_left_pre_semiring_carrier) 
                                          (A_eqv_eq L A_left_pre_semiring_label)  
                                          A_left_pre_semiring_trans
  ; A_left_pre_semiring_exists_plus_ann_d : bop_exists_ann_decidable S 
                                            (A_eqv_eq S A_left_pre_semiring_carrier) 
                                            A_left_pre_semiring_plus                                 
  ; A_left_pre_semiring_id_ann_proofs_d   : slt_exists_id_ann_decidable 
                                          (A_eqv_eq S A_left_pre_semiring_carrier) 
                                          A_left_pre_semiring_plus  
                                          A_left_pre_semiring_trans 
  ; A_left_pre_semiring_proofs          : left_semiring_proofs 
                                          (A_eqv_eq S A_left_pre_semiring_carrier) 
                                          A_left_pre_semiring_plus 
                                          A_left_pre_semiring_trans 
  ; A_left_pre_semiring_ast             : cas_ast 
}.



Record A_left_semiring {L S : Type} :=
  {
      A_left_semiring_carrier         : A_eqv S
    ; A_left_semiring_label           : A_eqv L
    ; A_left_semiring_plus            : binary_op S                                               
    ; A_left_semiring_trans           : ltr_type L S (* L -> (S -> S) *)
    ; A_left_semiring_plus_proofs     : sg_C_proofs S 
                                        (A_eqv_eq S A_left_semiring_carrier) 
                                        A_left_semiring_plus                                 
    ; A_left_semiring_trans_proofs    : left_transform_proofs L S 
                                        (A_eqv_eq S A_left_semiring_carrier) 
                                        (A_eqv_eq L A_left_semiring_label)  
                                        A_left_semiring_trans
    ; A_left_semiring_exists_plus_ann_d : bop_exists_ann_decidable S 
                                          (A_eqv_eq S A_left_semiring_carrier) 
                                          A_left_semiring_plus                                 
    ; A_left_semiring_id_ann_proofs   : slt_exists_id_ann_equal 
                                        (A_eqv_eq S A_left_semiring_carrier) 
                                        A_left_semiring_plus  
                                        A_left_semiring_trans 
    ; A_left_semiring_proofs          : left_semiring_proofs 
                                        (A_eqv_eq S A_left_semiring_carrier) 
                                        A_left_semiring_plus 
                                        A_left_semiring_trans 
    ; A_left_semiring_ast             : cas_ast 
  }.

 Record A_left_idempotent_semiring {L S : Type} :=
  {
      A_left_idempotent_semiring_carrier         : A_eqv S
    ; A_left_idempotent_semiring_label           : A_eqv L
    ; A_left_idempotent_semiring_plus            : binary_op S                                               
    ; A_left_idempotent_semiring_trans           : ltr_type L S (* L -> (S -> S) *)
    ; A_left_idempotent_semiring_plus_proofs     : sg_CI_proofs S 
                                        (A_eqv_eq S A_left_idempotent_semiring_carrier) 
                                        A_left_idempotent_semiring_plus                                 
    ; A_left_idempotent_semiring_trans_proofs    : left_transform_proofs L S 
                                        (A_eqv_eq S A_left_idempotent_semiring_carrier) 
                                        (A_eqv_eq L A_left_idempotent_semiring_label)  
                                        A_left_idempotent_semiring_trans
    ; A_left_idempotent_semiring_exists_plus_ann_d : bop_exists_ann_decidable S 
                                          (A_eqv_eq S A_left_idempotent_semiring_carrier) 
                                          A_left_idempotent_semiring_plus                                 
    ; A_left_idempotent_semiring_id_ann_proofs : slt_exists_id_ann_equal 
                                        (A_eqv_eq S A_left_idempotent_semiring_carrier) 
                                        A_left_idempotent_semiring_plus  
                                        A_left_idempotent_semiring_trans 
    ; A_left_idempotent_semiring_proofs  : left_semiring_proofs 
                                        (A_eqv_eq S A_left_idempotent_semiring_carrier) 
                                        A_left_idempotent_semiring_plus 
                                        A_left_idempotent_semiring_trans 
    ; A_left_idempotent_semiring_ast             : cas_ast 
  }.


Record A_left_selective_semiring {L S : Type} :=
  {
      A_left_selective_semiring_carrier         : A_eqv S
    ; A_left_selective_semiring_label           : A_eqv L
    ; A_left_selective_semiring_plus            : binary_op S                                               
    ; A_left_selective_semiring_trans           : ltr_type L S (* L -> (S -> S) *)
    ; A_left_selective_semiring_plus_proofs     : sg_CS_proofs S 
                                        (A_eqv_eq S A_left_selective_semiring_carrier) 
                                        A_left_selective_semiring_plus                                 
    ; A_left_selective_semiring_trans_proofs    : left_transform_proofs L S 
                                        (A_eqv_eq S A_left_selective_semiring_carrier) 
                                        (A_eqv_eq L A_left_selective_semiring_label)  
                                        A_left_selective_semiring_trans
    ; A_left_selective_semiring_exists_plus_ann_d : bop_exists_ann_decidable S 
                                          (A_eqv_eq S A_left_selective_semiring_carrier) 
                                          A_left_selective_semiring_plus                                 
    ; A_left_selective_semiring_id_ann_proofs   : slt_exists_id_ann_equal 
                                        (A_eqv_eq S A_left_selective_semiring_carrier) 
                                        A_left_selective_semiring_plus  
                                        A_left_selective_semiring_trans 
    ; A_left_selective_semiring_proofs  : left_semiring_proofs 
                                        (A_eqv_eq S A_left_selective_semiring_carrier) 
                                        A_left_selective_semiring_plus 
                                        A_left_selective_semiring_trans 
    ; A_left_selective_semiring_ast             : cas_ast 
  }.


End ACAS.

Section AMCAS.                                                    

Inductive A_slt_mcas {L S : Type} :=
| A_SLT_Error : list string                          -> @A_slt_mcas L S
| A_SLT : @A_slt L S                                  -> @A_slt_mcas L S
| A_SLT_C : @A_slt_C L S                              -> @A_slt_mcas L S
| A_SLT_CS : @A_slt_CS L S                            -> @A_slt_mcas L S
| A_SLT_CI : @A_slt_CI L S                            -> @A_slt_mcas L S
| A_SLT_C_Zero_Is_Ltr_ann : @A_slt_C_zero_is_ltr_ann L S  -> @A_slt_mcas L S
| A_SLT_Dioid : @A_left_dioid L S                     -> @A_slt_mcas L S
| A_SLT_Selective_Left_Pre_Dioid : @A_selective_left_pre_dioid L S -> @A_slt_mcas L S
| A_SLT_Selective_Dioid : @A_selective_left_dioid L S -> @A_slt_mcas L S
| A_SLT_Left_Pre_Semiring : @A_left_pre_semiring L S -> @A_slt_mcas L S 
| A_SLT_Semiring : @A_left_semiring L S -> @A_slt_mcas L S
| A_SLT_Selective_Semiring : @A_left_selective_semiring L S -> @A_slt_mcas L S
| A_SLT_Idempotent_Semiring : @A_left_idempotent_semiring L S -> @A_slt_mcas L S.



Inductive A_slt_mcas_proofs {L S : Type} (r : brel S) (add : binary_op S) (ltr : ltr_type L S)  :=
| A_SLT_proofs  : @slt_proofs L S r add ltr ->  @A_slt_mcas_proofs L S r add ltr
| A_SLT_dioid_proofs : @left_dioid_proofs L S r add ltr -> @A_slt_mcas_proofs L S r add ltr
| A_SLT_semiring_proofs : @left_semiring_proofs L S r add ltr -> @A_slt_mcas_proofs L S r add ltr. 

Definition A_slt_classify_proofs {L S : Type}  (r : brel S) 
  (add : binary_op S) 
  (ltr : ltr_type L S)  
  (A : @slt_proofs L S r add ltr) : @A_slt_mcas_proofs L S r add ltr :=
  match A_slt_distributive_d _ _ _ A with
  | inl ld => match A_slt_absorptive_d _ _ _ A with
    | inl la => A_SLT_dioid_proofs _ _ _ 
      {|
          A_left_dioid_distributive            := ld
        ; A_left_dioid_absorptive              := la                                               
        ; A_left_dioid_strictly_absorptive_d := A_slt_strictly_absorptive_d _ _ _ A 
      |}
    | inr nla => A_SLT_semiring_proofs _ _ _ 
      {|
          A_left_semiring_distributive            := ld
        ; A_left_semiring_not_absorptive          := nla                                              
      |}
  end
  | inr _  =>  A_SLT_proofs _ _ _ A      
  end.

 

  Definition A_slt_classify_left_dioid_slt {L S : Type} 
    (A : @A_left_dioid L S) : @A_slt_mcas L S :=
    A_SLT_Dioid A.


  Definition A_slt_classify_selective_left_dioid_slt {L S : Type} 
    (A : @A_selective_left_dioid L S) : A_slt_mcas :=
    A_SLT_Selective_Dioid A.
  
  
  Definition A_slt_classify_selective_left_pre_dioid_slt
    {L S : Type} (A : @A_selective_left_pre_dioid L S) : @A_slt_mcas L S :=
    match A_selective_left_pre_dioid_id_ann_proofs_d A with
    | SLT_Id_Ann_Proof_Equal _ _ _ ppf =>
      A_slt_classify_selective_left_dioid_slt
        {|
            A_selective_left_dioid_carrier := A_selective_left_pre_dioid_carrier A 
          ; A_selective_left_dioid_label :=  A_selective_left_pre_dioid_label A
          ; A_selective_left_dioid_plus := A_selective_left_pre_dioid_plus A                                             
          ; A_selective_left_dioid_trans := A_selective_left_pre_dioid_trans A  (* L -> (S -> S) *)
          ; A_selective_left_dioid_plus_proofs :=  A_selective_left_pre_dioid_plus_proofs A
          ; A_selective_left_dioid_trans_proofs := A_selective_left_pre_dioid_trans_proofs A 
          ; A_selective_left_dioid_exists_plus_ann := A_selective_left_pre_dioid_exists_plus_ann A                               
          ; A_selective_left_dioid_id_ann_proofs  := ppf                  
          ; A_selective_left_dioid_proofs := A_selective_left_pre_dioid_proofs A                               
          ; A_selective_left_dioid_ast := A_selective_left_pre_dioid_ast A 
        |}
    | _ => A_SLT_Selective_Left_Pre_Dioid A
    end.


  Definition A_slt_classify_left_selective_semiring_slt {L S : Type}
    (A : @A_left_selective_semiring L S) : A_slt_mcas :=
    A_SLT_Selective_Semiring A.

  Definition A_slt_classify_left_idempotent_semiring_slt {L S : Type}
    (A : @A_left_idempotent_semiring L S) : A_slt_mcas :=
    A_SLT_Idempotent_Semiring A.

 

  
  Definition A_slt_classify_left_semiring_slt {L S : Type} 
    (A : @A_left_semiring L S) : A_slt_mcas :=
    let plus_proof := A_left_semiring_plus_proofs A in 
    match A_sg_proofs_classify_sg_C  _ _ _ plus_proof with 
    | A_MCAS_Proof_sg_CS _ _ _ pf =>  
        A_slt_classify_left_selective_semiring_slt 
        {|
            A_left_selective_semiring_carrier := A_left_semiring_carrier A
          ; A_left_selective_semiring_label  := A_left_semiring_label A
          ; A_left_selective_semiring_plus   := A_left_semiring_plus A                                          
          ; A_left_selective_semiring_trans   := A_left_semiring_trans A
          ; A_left_selective_semiring_plus_proofs  := pf                                
          ; A_left_selective_semiring_trans_proofs  := A_left_semiring_trans_proofs A
          ; A_left_selective_semiring_exists_plus_ann_d := A_left_semiring_exists_plus_ann_d A                              
          ; A_left_selective_semiring_id_ann_proofs  := A_left_semiring_id_ann_proofs A
          ; A_left_selective_semiring_proofs := A_left_semiring_proofs A
          ; A_left_selective_semiring_ast  := A_left_semiring_ast A
        |}
    | A_MCAS_Proof_sg_CI _ _ _ pf =>  
        A_slt_classify_left_idempotent_semiring_slt 
        {|
            A_left_idempotent_semiring_carrier := A_left_semiring_carrier A
          ; A_left_idempotent_semiring_label := A_left_semiring_label A
          ; A_left_idempotent_semiring_plus  := A_left_semiring_plus A                                              
          ; A_left_idempotent_semiring_trans  := A_left_semiring_trans A  
          ; A_left_idempotent_semiring_plus_proofs := pf                                 
          ; A_left_idempotent_semiring_trans_proofs  := A_left_semiring_trans_proofs A
          ; A_left_idempotent_semiring_exists_plus_ann_d  := A_left_semiring_exists_plus_ann_d A                               
          ; A_left_idempotent_semiring_id_ann_proofs  := A_left_semiring_id_ann_proofs A
          ; A_left_idempotent_semiring_proofs  := A_left_semiring_proofs A
          ; A_left_idempotent_semiring_ast := A_left_semiring_ast A  
        |}
    | _ =>  A_SLT_Semiring A
    end.


     

  Definition A_slt_classify_left_pre_semiring_slt {L S : Type}
    (A : @A_left_pre_semiring L S) : A_slt_mcas :=
    match A_left_pre_semiring_id_ann_proofs_d A with
    | SLT_Id_Ann_Proof_Equal _ _ _ ppf => 
        A_slt_classify_left_semiring_slt
        {|
              A_left_semiring_carrier         := A_left_pre_semiring_carrier A
            ; A_left_semiring_label           := A_left_pre_semiring_label A
            ; A_left_semiring_plus            := A_left_pre_semiring_plus A                                              
            ; A_left_semiring_trans           := A_left_pre_semiring_trans A  (* L -> (S -> S) *)
            ; A_left_semiring_plus_proofs     := A_left_pre_semiring_plus_proofs A                                 
            ; A_left_semiring_trans_proofs    := A_left_pre_semiring_trans_proofs A 
            ; A_left_semiring_exists_plus_ann_d := A_left_pre_semiring_exists_plus_ann_d A                           
            ; A_left_semiring_id_ann_proofs  := ppf
            ; A_left_semiring_proofs          := A_left_pre_semiring_proofs A
            ; A_left_semiring_ast             := A_left_pre_semiring_ast A
        |}
    | _ => A_SLT_Left_Pre_Semiring A
    end.
  


  Definition A_slt_CS_classify_slt {L S : Type} (A : @A_slt_CS L S) : A_slt_mcas :=
    let slt_proof := A_slt_CS_proofs A in
    match A_slt_classify_proofs _ _ _ slt_proof with 
    | A_SLT_proofs _ _ _ pf =>  A_SLT_CS A
    | A_SLT_dioid_proofs _ _ _ pf =>
        match A_slt_CS_exists_plus_ann_d A with
        | inl ann => 
            A_slt_classify_selective_left_pre_dioid_slt
            {|
                A_selective_left_pre_dioid_carrier := A_slt_CS_carrier A 
              ; A_selective_left_pre_dioid_label := A_slt_CS_label A 
              ; A_selective_left_pre_dioid_plus := A_slt_CS_plus A                                              
              ; A_selective_left_pre_dioid_trans := A_slt_CS_trans A 
              ; A_selective_left_pre_dioid_plus_proofs := A_slt_CS_plus_proofs A
              ; A_selective_left_pre_dioid_trans_proofs := A_slt_CS_trans_proofs A 
              ; A_selective_left_pre_dioid_exists_plus_ann := ann                               
              ; A_selective_left_pre_dioid_id_ann_proofs_d := A_slt_CS_id_ann_proofs_d A                      
              ; A_selective_left_pre_dioid_proofs := pf                                
              ; A_selective_left_pre_dioid_ast := A_slt_CS_ast A
            
            |}
        | _ => A_SLT_CS A 
        end
    | A_SLT_semiring_proofs _ _ _ pf => 
        match A_slt_CS_id_ann_proofs_d  A with 
        | SLT_Id_Ann_Proof_Equal _ _ _ ppf => 
            A_slt_classify_left_selective_semiring_slt
            {|
                  A_left_selective_semiring_carrier :=  A_slt_CS_carrier A
                ; A_left_selective_semiring_label  := A_slt_CS_label A 
                ; A_left_selective_semiring_plus := A_slt_CS_plus A                                             
                ; A_left_selective_semiring_trans  := A_slt_CS_trans A 
                ; A_left_selective_semiring_plus_proofs  :=  A_slt_CS_plus_proofs A                               
                ; A_left_selective_semiring_trans_proofs  := A_slt_CS_trans_proofs A 
                ; A_left_selective_semiring_exists_plus_ann_d := A_slt_CS_exists_plus_ann_d A                                
                ; A_left_selective_semiring_id_ann_proofs  := ppf 
                ; A_left_selective_semiring_proofs := pf
                ; A_left_selective_semiring_ast  := A_slt_CS_ast A
            |}
        | _ => A_SLT_CS A
        end
    end.

   

  Definition A_slt_CI_classify_slt {L S : Type} (A : @A_slt_CI L S) : A_slt_mcas :=
    let slt_proof := A_slt_CI_proofs A in 
    match A_slt_classify_proofs _ _ _ slt_proof with 
    | A_SLT_proofs _ _ _ pf =>  A_SLT_CI A 
    | A_SLT_dioid_proofs _ _ _ pf =>
        match A_slt_CI_exists_plus_ann_d A with
        | inl ann => 
            match A_slt_CI_id_ann_proofs_d A with 
            | SLT_Id_Ann_Proof_Equal _ _ _ ppf =>
                A_slt_classify_left_dioid_slt
                  {|
                      A_left_dioid_carrier := A_slt_CI_carrier A 
                    ; A_left_dioid_label := A_slt_CI_label A
                    ; A_left_dioid_plus  := A_slt_CI_plus A                                             
                    ; A_left_dioid_trans := A_slt_CI_trans A
                    ; A_left_dioid_plus_proofs  := A_slt_CI_plus_proofs A
                    ; A_left_dioid_trans_proofs := A_slt_CI_trans_proofs A
                    ; A_left_dioid_exists_plus_ann := ann                              
                    ; A_left_dioid_id_ann_proofs   := ppf
                    ; A_left_dioid_proofs := pf 
                    ; A_left_dioid_ast := A_slt_CI_ast A
                  |}
            | _ => A_SLT_CI A 
            end
        | _ => A_SLT_CI A    
        end
    | A_SLT_semiring_proofs _ _ _ pf => 
        match A_slt_CI_id_ann_proofs_d A with 
        | SLT_Id_Ann_Proof_Equal _ _ _ ppf =>
            A_slt_classify_left_idempotent_semiring_slt
            {|
                  A_left_idempotent_semiring_carrier :=  A_slt_CI_carrier A 
                ; A_left_idempotent_semiring_label  := A_slt_CI_label A
                ; A_left_idempotent_semiring_plus   := A_slt_CI_plus A                                            
                ; A_left_idempotent_semiring_trans   := A_slt_CI_trans A
                ; A_left_idempotent_semiring_plus_proofs := A_slt_CI_plus_proofs A                              
                ; A_left_idempotent_semiring_trans_proofs := A_slt_CI_trans_proofs A
                ; A_left_idempotent_semiring_exists_plus_ann_d := A_slt_CI_exists_plus_ann_d A                              
                ; A_left_idempotent_semiring_id_ann_proofs := ppf
                ; A_left_idempotent_semiring_proofs  := pf
                ; A_left_idempotent_semiring_ast := A_slt_CI_ast A
            |}
        | _ => A_SLT_CI A
        end
    end.

   

  

 
  Definition A_slt_C_zero_is_ltr_ann_classify_slt {L S : Type} 
    (A : @A_slt_C_zero_is_ltr_ann L S) : A_slt_mcas := 
   let slt_proof := A_slt_C_zero_is_ltr_ann_proofs A in 
   match  A_slt_classify_proofs _ _ _ slt_proof with 
   | A_SLT_proofs _ _ _ pf => A_SLT_C_Zero_Is_Ltr_ann A 
   | A_SLT_dioid_proofs _ _ _ pf =>
      match A_sg_proofs_classify_sg_C  _ _ _ 
        (A_slt_C_zero_is_ltr_ann_plus_proofs A) with 
      | A_MCAS_Proof_sg_CS _ _ _ ppf => 
          match A_slt_C_zero_is_ltr_ann_exists_plus_ann_d A with
          | inl ann => 
            A_slt_classify_selective_left_dioid_slt
            {|
                  A_selective_left_dioid_carrier := A_slt_C_zero_is_ltr_ann_carrier A
                ; A_selective_left_dioid_label  := A_slt_C_zero_is_ltr_ann_label A
                ; A_selective_left_dioid_plus  := A_slt_C_zero_is_ltr_ann_plus A                                             
                ; A_selective_left_dioid_trans := A_slt_C_zero_is_ltr_ann_trans A
                ; A_selective_left_dioid_plus_proofs  := ppf 
                ; A_selective_left_dioid_trans_proofs := A_slt_C_zero_is_ltr_ann_trans_proofs A
                ; A_selective_left_dioid_exists_plus_ann := ann                             
                ; A_selective_left_dioid_id_ann_proofs  := A_slt_C_zero_is_ltr_ann_id_ann_proofs A                  
                ; A_selective_left_dioid_proofs := pf                                
                ; A_selective_left_dioid_ast := A_slt_C_zero_is_ltr_ann_ast A 
            |}
          | _ => A_SLT_C_Zero_Is_Ltr_ann A
          end
      | A_MCAS_Proof_sg_CI _ _ _ ppf => 
          match A_slt_C_zero_is_ltr_ann_exists_plus_ann_d A with
          | inl ann => 
              A_slt_classify_left_dioid_slt 
              {|
                      A_left_dioid_carrier := A_slt_C_zero_is_ltr_ann_carrier A
                    ; A_left_dioid_label := A_slt_C_zero_is_ltr_ann_label A
                    ; A_left_dioid_plus  := A_slt_C_zero_is_ltr_ann_plus A                                      
                    ; A_left_dioid_trans := A_slt_C_zero_is_ltr_ann_trans A
                    ; A_left_dioid_plus_proofs  := ppf  
                    ; A_left_dioid_trans_proofs := A_slt_C_zero_is_ltr_ann_trans_proofs A
                    ; A_left_dioid_exists_plus_ann := ann                                
                    ; A_left_dioid_id_ann_proofs  := A_slt_C_zero_is_ltr_ann_id_ann_proofs A 
                    ; A_left_dioid_proofs := pf 
                    ; A_left_dioid_ast := A_slt_C_zero_is_ltr_ann_ast A 
              
              |}
          | _ => A_SLT_C_Zero_Is_Ltr_ann A 
          end    
      |  _ => A_SLT_C_Zero_Is_Ltr_ann A 
      end
   | A_SLT_semiring_proofs _ _ _ pf => 
      A_slt_classify_left_semiring_slt 
      {|
            A_left_semiring_carrier := A_slt_C_zero_is_ltr_ann_carrier A 
          ; A_left_semiring_label  := A_slt_C_zero_is_ltr_ann_label A
          ; A_left_semiring_plus  := A_slt_C_zero_is_ltr_ann_plus A                                        
          ; A_left_semiring_trans  := A_slt_C_zero_is_ltr_ann_trans A
          ; A_left_semiring_plus_proofs := A_slt_C_zero_is_ltr_ann_plus_proofs A                                 
          ; A_left_semiring_trans_proofs := A_slt_C_zero_is_ltr_ann_trans_proofs A 
          ; A_left_semiring_exists_plus_ann_d := A_slt_C_zero_is_ltr_ann_exists_plus_ann_d A                           
          ; A_left_semiring_id_ann_proofs  := A_slt_C_zero_is_ltr_ann_id_ann_proofs A
          ; A_left_semiring_proofs  := pf
          ; A_left_semiring_ast  := A_slt_C_zero_is_ltr_ann_ast A 
      |}
   end.

   
  Definition A_slt_C_classify_slt {L S : Type} (A : @A_slt_C L S) : @A_slt_mcas L S :=
    let slt_proof := A_slt_C_proofs A in
    match A_slt_classify_proofs _ _ _ slt_proof with
     | A_SLT_proofs _ _ _ pf => 
        match A_sg_proofs_classify_sg_C  _ _ _ 
          (A_slt_C_plus_proofs A) with
        | A_MCAS_Proof_sg_CS _ _ _ ppf => 
            A_slt_CS_classify_slt 
            {|
                  A_slt_CS_carrier  := A_slt_C_carrier A
                ; A_slt_CS_label  := A_slt_C_label A 
                ; A_slt_CS_plus  := A_slt_C_plus A                                            
                ; A_slt_CS_trans   := A_slt_C_trans A 
                ; A_slt_CS_plus_proofs := ppf                       
                ; A_slt_CS_trans_proofs := A_slt_C_trans_proofs A 
                ; A_slt_CS_exists_plus_ann_d := A_slt_C_exists_plus_ann_d A                                
                ; A_slt_CS_id_ann_proofs_d  := A_slt_C_id_ann_proofs_d A                                       
                ; A_slt_CS_proofs := pf                              
                ; A_slt_CS_ast := A_slt_C_ast A
            
            |}
        | A_MCAS_Proof_sg_CI _ _ _ ppf => 
            A_slt_CI_classify_slt
            {|
                  A_slt_CI_carrier  := A_slt_C_carrier A
                ; A_slt_CI_label  := A_slt_C_label A 
                ; A_slt_CI_plus  := A_slt_C_plus A                                            
                ; A_slt_CI_trans   := A_slt_C_trans A 
                ; A_slt_CI_plus_proofs := ppf                       
                ; A_slt_CI_trans_proofs := A_slt_C_trans_proofs A 
                ; A_slt_CI_exists_plus_ann_d := A_slt_C_exists_plus_ann_d A                                
                ; A_slt_CI_id_ann_proofs_d  := A_slt_C_id_ann_proofs_d A                                       
                ; A_slt_CI_proofs := pf                              
                ; A_slt_CI_ast := A_slt_C_ast A
            
            |}
        | _ => 
          match A_slt_C_id_ann_proofs_d A with 
          | SLT_Id_Ann_Proof_Equal _ _ _ ppf =>  
              A_slt_C_zero_is_ltr_ann_classify_slt 
              {|
                    A_slt_C_zero_is_ltr_ann_carrier := A_slt_C_carrier A 
                  ; A_slt_C_zero_is_ltr_ann_label := A_slt_C_label A
                  ; A_slt_C_zero_is_ltr_ann_plus  := A_slt_C_plus A                               
                  ; A_slt_C_zero_is_ltr_ann_trans   := A_slt_C_trans A 
                  ; A_slt_C_zero_is_ltr_ann_plus_proofs  := A_slt_C_plus_proofs A                           
                  ; A_slt_C_zero_is_ltr_ann_trans_proofs := A_slt_C_trans_proofs A 
                  ; A_slt_C_zero_is_ltr_ann_exists_plus_ann_d := A_slt_C_exists_plus_ann_d A                               
                  ; A_slt_C_zero_is_ltr_ann_id_ann_proofs := ppf                                             
                  ; A_slt_C_zero_is_ltr_ann_proofs := pf                              
                  ; A_slt_C_zero_is_ltr_ann_ast := A_slt_C_ast A 
              
              |}
          | _ => A_SLT_C A
          end
        end
     | A_SLT_dioid_proofs _ _ _ pf => A_SLT_C A
     | A_SLT_semiring_proofs _ _ _ pf => 
        A_slt_classify_left_pre_semiring_slt
        {|
              A_left_pre_semiring_carrier :=  A_slt_C_carrier A
            ; A_left_pre_semiring_label := A_slt_C_label A
            ; A_left_pre_semiring_plus  := A_slt_C_plus A                                            
            ; A_left_pre_semiring_trans := A_slt_C_trans A
            ; A_left_pre_semiring_plus_proofs  := A_slt_C_plus_proofs A                             
            ; A_left_pre_semiring_trans_proofs  := A_slt_C_trans_proofs A
            ; A_left_pre_semiring_exists_plus_ann_d := A_slt_C_exists_plus_ann_d A                              
            ; A_left_pre_semiring_id_ann_proofs_d := A_slt_C_id_ann_proofs_d A
            ; A_left_pre_semiring_proofs := pf
            ; A_left_pre_semiring_ast   := A_slt_C_ast A
        |}
    end.

   
  Definition A_slt_classify_slt {L S : Type} (A : @A_slt L S) : A_slt_mcas :=
    let plus_proofs := A_slt_plus_proofs A in
    match sg_proof_classify _ _ _ (A_MCAS_Proof_sg _ _ _ plus_proofs) with 
    | A_MCAS_Proof_sg_C _ _ _ pf => 
        A_slt_C_classify_slt
        {|
              A_slt_C_carrier  := A_slt_carrier A
            ; A_slt_C_label  := A_slt_label A 
            ; A_slt_C_plus  := A_slt_plus A                                            
            ; A_slt_C_trans   := A_slt_trans A 
            ; A_slt_C_plus_proofs := pf                       
            ; A_slt_C_trans_proofs := A_slt_trans_proofs A 
            ; A_slt_C_exists_plus_ann_d := A_slt_exists_plus_ann_d A                                
            ; A_slt_C_id_ann_proofs_d  := A_slt_id_ann_proofs_d A                                       
            ; A_slt_C_proofs := A_slt_proofs A                             
            ; A_slt_C_ast := A_slt_ast A
        |}
    | _ => A_SLT A  
    end. 

    



(* This is the main claissification function *)

Definition A_slt_classify {L S : Type} (A : @A_slt_mcas L S) : @A_slt_mcas L S :=
  match A with
  | A_SLT_Error ls => A
  | A_SLT slt => A_slt_classify_slt slt 
  | A_SLT_C slt => A_slt_C_classify_slt slt
  | A_SLT_CS slt => A_slt_CS_classify_slt slt
  | A_SLT_CI slt => A_slt_CI_classify_slt slt
  | A_SLT_C_Zero_Is_Ltr_ann slt => A_slt_C_zero_is_ltr_ann_classify_slt slt
  | A_SLT_Left_Pre_Semiring slt => A_slt_classify_left_pre_semiring_slt slt  
  | A_SLT_Dioid slt => A_slt_classify_left_dioid_slt slt 
  | A_SLT_Selective_Left_Pre_Dioid slt => A_slt_classify_selective_left_pre_dioid_slt slt
  | A_SLT_Semiring slt => A_slt_classify_left_semiring_slt slt 
  | A_SLT_Selective_Dioid slt => A_slt_classify_selective_left_dioid_slt slt 
  | A_SLT_Selective_Semiring slt => A_slt_classify_left_selective_semiring_slt slt
  | A_SLT_Idempotent_Semiring slt => A_slt_classify_left_idempotent_semiring_slt slt
  end.

End AMCAS.       



Section CAS. 

  Record slt_certificates {L S : Type} :=
    {
      slt_distributive_d          : @check_slt_distributive L S
    ; slt_absorptive_d            : @check_slt_absorptive L S 
    ; slt_strictly_absorptive_d   : @check_slt_strictly_absorptive L S
    }.

  Record left_dioid_certificates {L S : Type} :=
    {
      left_dioid_distributive            : @assert_slt_distributive L S
    ; left_dioid_absorptive              : @assert_slt_absorptive L S                                              
    ; left_dioid_strictly_absorptive_d : @check_slt_strictly_absorptive L S
    }.

    


  Record left_semiring_certificates {L S : Type} :=
    {
      left_semiring_distributive            : @assert_slt_distributive L S
    ; left_semiring_not_absorptive          : @assert_slt_not_absorptive L S                                           
    }.


   
  Record slt {L S : Type} :=
    {
      slt_carrier        : @eqv S
    ; slt_label          : @eqv L
    ; slt_plus           : binary_op S                                               
    ; slt_trans          : ltr_type L S (* L -> (S -> S) *)
    ; slt_plus_certs    : @sg_certificates S                                
    ; slt_trans_certs   : @left_transform_certificates L S
    ; slt_exists_plus_ann_d : @check_exists_ann S                              
    ; slt_id_ann_certs_d : @check_slt_exists_id_ann L S                 
    ; slt_certs         : @slt_certificates L S                                
    ; slt_ast            : cas_ast
    }.

  Record slt_C {L S : Type} :=
    {
        slt_C_carrier : @eqv S
      ; slt_C_label : @eqv L
      ; slt_C_plus  : binary_op S                                               
      ; slt_C_trans : ltr_type L S (* L -> (S -> S) *)
      ; slt_C_plus_certs    : @sg_C_certificates S                           
      ; slt_C_trans_certs   : @left_transform_certificates L S
      ; slt_C_exists_plus_ann_d :  @check_exists_ann S                               
      ; slt_C_id_ann_certs_d  : @check_slt_exists_id_ann L S                                              
      ; slt_C_certs : @slt_certificates L S                                 
      ; slt_C_ast : cas_ast
    }.  
  

  Record slt_CS {L S : Type} :=
    {
        slt_CS_carrier        : @eqv S
      ; slt_CS_label          : @eqv L
      ; slt_CS_plus           : binary_op S                                               
      ; slt_CS_trans          : ltr_type L S (* L -> (S -> S) *)
      ; slt_CS_plus_certs     : @sg_CS_certificates S                         
      ; slt_CS_trans_certs   : @left_transform_certificates L S
      ; slt_CS_exists_plus_ann_d : @check_exists_ann S                                 
      ; slt_CS_id_ann_certs_d  : @check_slt_exists_id_ann L S                                          
      ; slt_CS_certs : @slt_certificates L S                                  
      ; slt_CS_ast : cas_ast
    }.
  
      
  Record slt_CI {L S : Type} :=
    {
        slt_CI_carrier        : @eqv S
      ; slt_CI_label          : @eqv L
      ; slt_CI_plus           : binary_op S                                               
      ; slt_CI_trans          : ltr_type L S (* L -> (S -> S) *)
      ; slt_CI_plus_certs    : @sg_CI_certificates S                         
      ; slt_CI_trans_certs   : @left_transform_certificates L S
      ; slt_CI_exists_plus_ann_d : @check_exists_ann S                                  
      ; slt_CI_id_ann_certs_d  : @check_slt_exists_id_ann L S                                      
      ; slt_CI_certs : @slt_certificates L S                                 
      ; slt_CI_ast : cas_ast
    }.


    Record slt_C_zero_is_ltr_ann {L S : Type} :=
    {
        slt_C_zero_is_ltr_ann_carrier : @eqv S 
      ; slt_C_zero_is_ltr_ann_label : @eqv L
      ; slt_C_zero_is_ltr_ann_plus  : binary_op S                                               
      ; slt_C_zero_is_ltr_ann_trans  : ltr_type L S (* L -> (S -> S) *)
      ; slt_C_zero_is_ltr_ann_plus_certs : @sg_C_certificates S                          
      ; slt_C_zero_is_ltr_ann_trans_certs : @left_transform_certificates L S
      ; slt_C_zero_is_ltr_ann_exists_plus_ann_d :  @check_exists_ann S                                
      ; slt_C_zero_is_ltr_ann_id_ann_certs  : @assert_slt_exists_id_ann_equal L S                                             
      ; slt_C_zero_is_ltr_ann_certs :  @slt_certificates L S                                  
      ; slt_C_zero_is_ltr_ann_ast : cas_ast
    }.


  Record selective_left_dioid {L S : Type} :=
    {
        selective_left_dioid_carrier      : @eqv S
      ; selective_left_dioid_label        : @eqv L
      ; selective_left_dioid_plus         : binary_op S                                               
      ; selective_left_dioid_trans        : ltr_type L S (* L -> (S -> S) *)
      ; selective_left_dioid_plus_certs   : @sg_CS_certificates S
      ; selective_left_dioid_trans_certs : @left_transform_certificates L S
      ; selective_left_dioid_exists_plus_ann : @assert_exists_ann S                               
      ; selective_left_dioid_id_ann_certs  : @assert_slt_exists_id_ann_equal L S                        
      ; selective_left_dioid_certs : @left_dioid_certificates L S                                 
      ; selective_left_dioid_ast : cas_ast 
    }.   

  

  Record selective_left_pre_dioid {L S : Type} :=
    {
        selective_left_pre_dioid_carrier      : @eqv S
      ; selective_left_pre_dioid_label        : @eqv L
      ; selective_left_pre_dioid_plus         : binary_op S                                               
      ; selective_left_pre_dioid_trans        : ltr_type L S (* L -> (S -> S) *)
      ; selective_left_pre_dioid_plus_certs   : @sg_CS_certificates S
      ; selective_left_pre_dioid_trans_certs  : @left_transform_certificates L S
      ; selective_left_pre_dioid_exists_plus_ann : @assert_exists_ann S                               
      ; selective_left_pre_dioid_id_ann_certs_d :  @check_slt_exists_id_ann L S                      
      ; selective_left_pre_dioid_certs : @left_dioid_certificates L S                                
      ; selective_left_pre_dioid_ast : cas_ast 
    }.

  

  Record left_dioid {L S : Type} :=
    {
      left_dioid_carrier         : @eqv S
    ; left_dioid_label           : @eqv L
    ; left_dioid_plus            : binary_op S                                               
    ; left_dioid_trans           : ltr_type L S (* L -> (S -> S) *)
    ; left_dioid_plus_certs     : @sg_CI_certificates S                                 
    ; left_dioid_trans_certs    : @left_transform_certificates L S    
    ; left_dioid_exists_plus_ann : @assert_exists_ann S                               
    ; left_dioid_id_ann_certs   : @assert_slt_exists_id_ann_equal L S
    ; left_dioid_certs          : @left_dioid_certificates L S
    ; left_dioid_ast             : cas_ast 
    }.
    
  
  Record left_pre_semiring {L S : Type} :=
    {
        left_pre_semiring_carrier         : @eqv S
      ; left_pre_semiring_label           : @eqv L
      ; left_pre_semiring_plus            : binary_op S                                               
      ; left_pre_semiring_trans           : ltr_type L S (* L -> (S -> S) *)
      ; left_pre_semiring_plus_certs     : @sg_C_certificates S                                
      ; left_pre_semiring_trans_certs    : @left_transform_certificates L S
      ; left_pre_semiring_exists_plus_ann_d : @check_exists_ann S                                
      ; left_pre_semiring_id_ann_certs_d   : @check_slt_exists_id_ann L S 
      ; left_pre_semiring_certs          : @left_semiring_certificates L S
      ; left_pre_semiring_ast             : cas_ast 
    }.

  Record left_semiring {L S : Type} :=
    {
      left_semiring_carrier         : @eqv S
    ; left_semiring_label           : @eqv L
    ; left_semiring_plus            : binary_op S                                               
    ; left_semiring_trans           : ltr_type L S (* L -> (S -> S) *)
    ; left_semiring_plus_certs     : @sg_C_certificates S                                
    ; left_semiring_trans_certs    : @left_transform_certificates L S
    ; left_semiring_exists_plus_ann_d : @check_exists_ann S                                
    ; left_semiring_id_ann_certs   : @assert_slt_exists_id_ann_equal L S 
    ; left_semiring_certs          : @left_semiring_certificates L S
    ; left_semiring_ast             : cas_ast 
    }.  
    

  Record left_idempotent_semiring {L S : Type} :=
    {
        left_idempotent_semiring_carrier         : @eqv S
      ; left_idempotent_semiring_label           : @eqv L
      ; left_idempotent_semiring_plus            : binary_op S                                               
      ; left_idempotent_semiring_trans           : ltr_type L S (* L -> (S -> S) *)
      ; left_idempotent_semiring_plus_certs     : @sg_CI_certificates S                                 
      ; left_idempotent_semiring_trans_certs    : @left_transform_certificates L S
      ; left_idempotent_semiring_exists_plus_ann_d : @check_exists_ann S                         
      ; left_idempotent_semiring_id_ann_certs : @assert_slt_exists_id_ann_equal L S
      ; left_idempotent_semiring_certs  : @left_semiring_certificates L S
      ; left_idempotent_semiring_ast         : cas_ast 
    }.



  Record left_selective_semiring {L S : Type} :=
    {
        left_selective_semiring_carrier         : @eqv S
      ; left_selective_semiring_label           : @eqv L
      ; left_selective_semiring_plus            : binary_op S                                               
      ; left_selective_semiring_trans           : ltr_type L S (* L -> (S -> S) *)
      ; left_selective_semiring_plus_certs      : @sg_CS_certificates S                                  
      ; left_selective_semiring_trans_certs     : @left_transform_certificates L S
      ; left_selective_semiring_exists_plus_ann_d : @check_exists_ann S                                 
      ; left_selective_semiring_id_ann_certs   : @assert_slt_exists_id_ann_equal L S
      ; left_selective_semiring_certs  : @left_semiring_certificates L S
      ; left_selective_semiring_ast             : cas_ast 
    }.  
    
  
    
End CAS.


Section MCAS.

  Inductive slt_mcas {L S : Type} :=
  | SLT_Error : list string                         -> @slt_mcas L S
  | SLT : @slt L S                                  -> @slt_mcas L S
  | SLT_C : @slt_C L S                              -> @slt_mcas L S
  | SLT_CS : @slt_CS L S                            -> @slt_mcas L S
  | SLT_CI : @slt_CI L S                            -> @slt_mcas L S
  | SLT_C_Zero_Is_Ltr_ann : @slt_C_zero_is_ltr_ann L S  -> @slt_mcas L S
  | SLT_Dioid : @left_dioid L S                     -> @slt_mcas L S
  | SLT_Selective_Dioid : @selective_left_dioid L S -> @slt_mcas L S
  | SLT_Selective_Left_Pre_Dioid : @selective_left_pre_dioid L S -> @slt_mcas L S
  | SLT_Left_Pre_Semiring : @left_pre_semiring L S -> @slt_mcas L S
  | SLT_Semiring : @left_semiring L S -> @slt_mcas L S
  | SLT_Idempotent_Semiring : @left_idempotent_semiring L S -> @slt_mcas L S
  | SLT_Selective_Semiring : @left_selective_semiring L S -> @slt_mcas L S.


  Inductive slt_mcas_certificates {L S : Type} :=
  | SLT_certs  : @slt_certificates L S ->  @slt_mcas_certificates L S
  | SLT_dioid_certs : @left_dioid_certificates L S -> @slt_mcas_certificates L S
  | SLT_semiring_certs : @left_semiring_certificates L S -> @slt_mcas_certificates L S.
  
  
  
  Definition slt_classify_certificates {L S : Type} 
    (A : @slt_certificates L S) : @slt_mcas_certificates L S :=
    match slt_distributive_d A with
    | Certify_Slt_Distributive =>
        match slt_absorptive_d A with
        | Certify_Slt_Absorptive => 
            SLT_dioid_certs 
            {|
                left_dioid_distributive := Assert_Slt_Distributive 
              ; left_dioid_absorptive := Assert_Slt_Absorptive
              ; left_dioid_strictly_absorptive_d := slt_strictly_absorptive_d A  
            |}
        | Certify_Slt_Not_Absorptive pf => 
            SLT_semiring_certs 
            {|
                left_semiring_distributive := Assert_Slt_Distributive
              ; left_semiring_not_absorptive := Assert_Slt_Not_Absorptive pf

            |}
        end
    | Certify_Slt_Not_Distributive _ => SLT_certs A 
    end. 
  

  Definition slt_classify_left_dioid_slt {L S : Type} 
    (A : @left_dioid L S) : @slt_mcas L S :=
    SLT_Dioid A.  

  Definition slt_classify_selective_left_dioid_slt {L S : Type} 
    (A : @selective_left_dioid L S) : slt_mcas :=
    SLT_Selective_Dioid A.
  
  
  
  Definition slt_classify_selective_left_pre_dioid_slt
    {L S : Type} (A : @selective_left_pre_dioid L S) : @slt_mcas L S :=
    match selective_left_pre_dioid_id_ann_certs_d A with
    | Certify_SLT_Id_Ann_Proof_Equal ppf =>
      slt_classify_selective_left_dioid_slt
        {|
            selective_left_dioid_carrier := selective_left_pre_dioid_carrier A 
          ; selective_left_dioid_label :=  selective_left_pre_dioid_label A
          ; selective_left_dioid_plus := selective_left_pre_dioid_plus A                                             
          ; selective_left_dioid_trans := selective_left_pre_dioid_trans A  (* L -> (S -> S) *)
          ; selective_left_dioid_plus_certs :=  selective_left_pre_dioid_plus_certs A
          ; selective_left_dioid_trans_certs := selective_left_pre_dioid_trans_certs A 
          ; selective_left_dioid_exists_plus_ann := selective_left_pre_dioid_exists_plus_ann A                               
          ; selective_left_dioid_id_ann_certs  := Assert_Slt_Exists_Id_Ann_Equal ppf                  
          ; selective_left_dioid_certs := selective_left_pre_dioid_certs A                               
          ; selective_left_dioid_ast := selective_left_pre_dioid_ast A 
        |}
    | _ => SLT_Selective_Left_Pre_Dioid A
    end.
  
    
   
  Definition slt_classify_left_selective_semiring_slt {L S : Type}
    (A : @left_selective_semiring L S) : slt_mcas :=
    SLT_Selective_Semiring A.

  Definition slt_classify_left_idempotent_semiring_slt {L S : Type}
    (A : @left_idempotent_semiring L S) : slt_mcas :=
    SLT_Idempotent_Semiring A.
   

  
  Definition slt_classify_left_semiring_slt {L S : Type} 
    (A : @left_semiring L S) : slt_mcas :=
    let plus_certificate := left_semiring_plus_certs A in 
    match sg_certificates_classify_sg_C plus_certificate with 
    | MCAS_Cert_sg_CS pf =>  
        slt_classify_left_selective_semiring_slt 
        {|
            left_selective_semiring_carrier := left_semiring_carrier A
          ; left_selective_semiring_label  := left_semiring_label A
          ; left_selective_semiring_plus   := left_semiring_plus A                                          
          ; left_selective_semiring_trans   := left_semiring_trans A
          ; left_selective_semiring_plus_certs  := pf                                
          ; left_selective_semiring_trans_certs  := left_semiring_trans_certs A
          ; left_selective_semiring_exists_plus_ann_d := left_semiring_exists_plus_ann_d A                              
          ; left_selective_semiring_id_ann_certs  := left_semiring_id_ann_certs A
          ; left_selective_semiring_certs := left_semiring_certs A
          ; left_selective_semiring_ast  := left_semiring_ast A
        |}
    | MCAS_Cert_sg_CI pf =>  
        slt_classify_left_idempotent_semiring_slt 
        {|
            left_idempotent_semiring_carrier := left_semiring_carrier A
          ; left_idempotent_semiring_label := left_semiring_label A
          ; left_idempotent_semiring_plus  := left_semiring_plus A                                              
          ; left_idempotent_semiring_trans  := left_semiring_trans A  
          ; left_idempotent_semiring_plus_certs := pf                                 
          ; left_idempotent_semiring_trans_certs  := left_semiring_trans_certs A
          ; left_idempotent_semiring_exists_plus_ann_d  := left_semiring_exists_plus_ann_d A                               
          ; left_idempotent_semiring_id_ann_certs  := left_semiring_id_ann_certs A
          ; left_idempotent_semiring_certs  := left_semiring_certs A
          ; left_idempotent_semiring_ast := left_semiring_ast A  
        |}
    | _ =>  SLT_Semiring A
    end.  

 

  Definition slt_classify_left_pre_semiring_slt {L S : Type}
    (A : @left_pre_semiring L S) : slt_mcas :=
    match left_pre_semiring_id_ann_certs_d A with
    | Certify_SLT_Id_Ann_Proof_Equal ppf => 
        slt_classify_left_semiring_slt
        {|
              left_semiring_carrier         := left_pre_semiring_carrier A
            ; left_semiring_label           := left_pre_semiring_label A
            ; left_semiring_plus            := left_pre_semiring_plus A                                              
            ; left_semiring_trans           := left_pre_semiring_trans A  (* L -> (S -> S) *)
            ; left_semiring_plus_certs     := left_pre_semiring_plus_certs A                                 
            ; left_semiring_trans_certs    := left_pre_semiring_trans_certs A 
            ; left_semiring_exists_plus_ann_d := left_pre_semiring_exists_plus_ann_d A                            
            ; left_semiring_id_ann_certs  := Assert_Slt_Exists_Id_Ann_Equal ppf  
            ; left_semiring_certs          := left_pre_semiring_certs A
            ; left_semiring_ast             := left_pre_semiring_ast A
        |}
    | _ => SLT_Left_Pre_Semiring A
    end.
  
    


  Definition slt_CS_classify_slt {L S : Type} (A : @slt_CS L S) : slt_mcas :=
    let slt_certificates := slt_CS_certs A in
    match slt_classify_certificates slt_certificates with 
    | SLT_certs _ => SLT_CS A
    | SLT_dioid_certs pf =>
        match slt_CS_exists_plus_ann_d A with
        | Certify_Exists_Ann ann => 
            slt_classify_selective_left_pre_dioid_slt
            {|
                selective_left_pre_dioid_carrier := slt_CS_carrier A 
              ; selective_left_pre_dioid_label := slt_CS_label A 
              ; selective_left_pre_dioid_plus := slt_CS_plus A                                              
              ; selective_left_pre_dioid_trans := slt_CS_trans A 
              ; selective_left_pre_dioid_plus_certs := slt_CS_plus_certs A
              ; selective_left_pre_dioid_trans_certs := slt_CS_trans_certs A 
              ; selective_left_pre_dioid_exists_plus_ann := Assert_Exists_Ann ann                              
              ; selective_left_pre_dioid_id_ann_certs_d := slt_CS_id_ann_certs_d A                      
              ; selective_left_pre_dioid_certs := pf                                
              ; selective_left_pre_dioid_ast := slt_CS_ast A
            
            |}
        | _ => SLT_CS A 
        end
    | SLT_semiring_certs pf => 
        match slt_CS_id_ann_certs_d  A with 
        | Certify_SLT_Id_Ann_Proof_Equal ppf => 
            slt_classify_left_selective_semiring_slt
            {|
                  left_selective_semiring_carrier :=  slt_CS_carrier A
                ; left_selective_semiring_label  := slt_CS_label A 
                ; left_selective_semiring_plus := slt_CS_plus A                                             
                ; left_selective_semiring_trans  := slt_CS_trans A 
                ; left_selective_semiring_plus_certs  :=  slt_CS_plus_certs A                               
                ; left_selective_semiring_trans_certs  := slt_CS_trans_certs A 
                ; left_selective_semiring_exists_plus_ann_d := slt_CS_exists_plus_ann_d A                                
                ; left_selective_semiring_id_ann_certs  := Assert_Slt_Exists_Id_Ann_Equal ppf
                ; left_selective_semiring_certs := pf
                ; left_selective_semiring_ast  := slt_CS_ast A
            |}
        | _ => SLT_CS A
        end
    end.

  
  Definition slt_CI_classify_slt {L S : Type} (A : @slt_CI L S) : slt_mcas :=
    let slt_certificates := slt_CI_certs A in 
    match slt_classify_certificates slt_certificates with 
    | SLT_certs _  =>  SLT_CI A 
    | SLT_dioid_certs pf =>
        match slt_CI_exists_plus_ann_d A with
        | Certify_Exists_Ann ann => 
            match slt_CI_id_ann_certs_d A with 
            | Certify_SLT_Id_Ann_Proof_Equal ppf =>
                slt_classify_left_dioid_slt
                  {|
                      left_dioid_carrier := slt_CI_carrier A 
                    ; left_dioid_label := slt_CI_label A
                    ; left_dioid_plus  := slt_CI_plus A                                             
                    ; left_dioid_trans := slt_CI_trans A
                    ; left_dioid_plus_certs  := slt_CI_plus_certs A
                    ; left_dioid_trans_certs := slt_CI_trans_certs A
                    ; left_dioid_exists_plus_ann := Assert_Exists_Ann ann                               
                    ; left_dioid_id_ann_certs   := Assert_Slt_Exists_Id_Ann_Equal ppf
                    ; left_dioid_certs := pf 
                    ; left_dioid_ast := slt_CI_ast A
                  |}
            | _ => SLT_CI A 
            end
        | _ => SLT_CI A    
        end
    | SLT_semiring_certs pf => 
        match slt_CI_id_ann_certs_d A with 
        | Certify_SLT_Id_Ann_Proof_Equal ppf =>
            slt_classify_left_idempotent_semiring_slt
            {|
                  left_idempotent_semiring_carrier :=  slt_CI_carrier A 
                ; left_idempotent_semiring_label  := slt_CI_label A
                ; left_idempotent_semiring_plus   := slt_CI_plus A                                            
                ; left_idempotent_semiring_trans   := slt_CI_trans A
                ; left_idempotent_semiring_plus_certs := slt_CI_plus_certs A                              
                ; left_idempotent_semiring_trans_certs := slt_CI_trans_certs A
                ; left_idempotent_semiring_exists_plus_ann_d := slt_CI_exists_plus_ann_d A                              
                ; left_idempotent_semiring_id_ann_certs := Assert_Slt_Exists_Id_Ann_Equal ppf
                ; left_idempotent_semiring_certs  := pf
                ; left_idempotent_semiring_ast := slt_CI_ast A
            |}
        | _ => SLT_CI A
        end
    end.


  Definition slt_C_zero_is_ltr_ann_classify_slt {L S : Type} 
    (A : @slt_C_zero_is_ltr_ann L S) : slt_mcas := 
    let slt_certificates := slt_C_zero_is_ltr_ann_certs A in 
    match  slt_classify_certificates slt_certificates with 
    | SLT_certs _ => SLT_C_Zero_Is_Ltr_ann A 
    | SLT_dioid_certs pf =>
        match sg_certificates_classify_sg_C 
          (slt_C_zero_is_ltr_ann_plus_certs A) with 
        | MCAS_Cert_sg_CS ppf => 
            match slt_C_zero_is_ltr_ann_exists_plus_ann_d A with
            | Certify_Exists_Ann ann => 
              slt_classify_selective_left_dioid_slt
              {|
                    selective_left_dioid_carrier := slt_C_zero_is_ltr_ann_carrier A
                  ; selective_left_dioid_label  := slt_C_zero_is_ltr_ann_label A
                  ; selective_left_dioid_plus  := slt_C_zero_is_ltr_ann_plus A                                             
                  ; selective_left_dioid_trans := slt_C_zero_is_ltr_ann_trans A
                  ; selective_left_dioid_plus_certs  := ppf 
                  ; selective_left_dioid_trans_certs := slt_C_zero_is_ltr_ann_trans_certs A
                  ; selective_left_dioid_exists_plus_ann := Assert_Exists_Ann ann                           
                  ; selective_left_dioid_id_ann_certs  := slt_C_zero_is_ltr_ann_id_ann_certs A                  
                  ; selective_left_dioid_certs := pf                                
                  ; selective_left_dioid_ast := slt_C_zero_is_ltr_ann_ast A 
              |}
            | _ => SLT_C_Zero_Is_Ltr_ann A
            end
        | MCAS_Cert_sg_CI ppf => 
            match slt_C_zero_is_ltr_ann_exists_plus_ann_d A with
            | Certify_Exists_Ann ann => 
                slt_classify_left_dioid_slt 
                {|
                        left_dioid_carrier := slt_C_zero_is_ltr_ann_carrier A
                      ; left_dioid_label := slt_C_zero_is_ltr_ann_label A
                      ; left_dioid_plus  := slt_C_zero_is_ltr_ann_plus A                                      
                      ; left_dioid_trans := slt_C_zero_is_ltr_ann_trans A
                      ; left_dioid_plus_certs  := ppf  
                      ; left_dioid_trans_certs := slt_C_zero_is_ltr_ann_trans_certs A
                      ; left_dioid_exists_plus_ann := Assert_Exists_Ann ann                                
                      ; left_dioid_id_ann_certs  := slt_C_zero_is_ltr_ann_id_ann_certs A 
                      ; left_dioid_certs := pf 
                      ; left_dioid_ast := slt_C_zero_is_ltr_ann_ast A 
                
                |}
            | _ => SLT_C_Zero_Is_Ltr_ann A 
            end    
        |  _ => SLT_C_Zero_Is_Ltr_ann A 
        end
    | SLT_semiring_certs pf => 
        slt_classify_left_semiring_slt 
        {|
              left_semiring_carrier := slt_C_zero_is_ltr_ann_carrier A 
            ; left_semiring_label  := slt_C_zero_is_ltr_ann_label A
            ; left_semiring_plus  := slt_C_zero_is_ltr_ann_plus A                                        
            ; left_semiring_trans  := slt_C_zero_is_ltr_ann_trans A
            ; left_semiring_plus_certs := slt_C_zero_is_ltr_ann_plus_certs A                                 
            ; left_semiring_trans_certs := slt_C_zero_is_ltr_ann_trans_certs A 
            ; left_semiring_exists_plus_ann_d := slt_C_zero_is_ltr_ann_exists_plus_ann_d A                           
            ; left_semiring_id_ann_certs  := slt_C_zero_is_ltr_ann_id_ann_certs A
            ; left_semiring_certs  := pf
            ; left_semiring_ast  := slt_C_zero_is_ltr_ann_ast A 
        |}
    end.
    



  
  
  Definition slt_C_classify_slt {L S : Type} 
    (A : @slt_C L S) : @slt_mcas L S :=
    let slt_certificate := slt_C_certs A in
    match slt_classify_certificates slt_certificate with
     | SLT_certs pf => 
        match sg_certificates_classify_sg_C 
          (slt_C_plus_certs A) with
        | MCAS_Cert_sg_CS ppf => 
            slt_CS_classify_slt 
            {|
                  slt_CS_carrier  := slt_C_carrier A
                ; slt_CS_label  := slt_C_label A 
                ; slt_CS_plus  := slt_C_plus A                                            
                ; slt_CS_trans   := slt_C_trans A 
                ; slt_CS_plus_certs := ppf                       
                ; slt_CS_trans_certs := slt_C_trans_certs A 
                ; slt_CS_exists_plus_ann_d := slt_C_exists_plus_ann_d A                                
                ; slt_CS_id_ann_certs_d  := slt_C_id_ann_certs_d A                                       
                ; slt_CS_certs := pf                              
                ; slt_CS_ast := slt_C_ast A
            
            |}
        | MCAS_Cert_sg_CI ppf => 
            slt_CI_classify_slt
            {|
                  slt_CI_carrier  := slt_C_carrier A
                ; slt_CI_label  := slt_C_label A 
                ; slt_CI_plus  := slt_C_plus A                                            
                ; slt_CI_trans   := slt_C_trans A 
                ; slt_CI_plus_certs := ppf                       
                ; slt_CI_trans_certs := slt_C_trans_certs A 
                ; slt_CI_exists_plus_ann_d := slt_C_exists_plus_ann_d A                                
                ; slt_CI_id_ann_certs_d  := slt_C_id_ann_certs_d A                                       
                ; slt_CI_certs := pf                              
                ; slt_CI_ast := slt_C_ast A
            
            |}
        | _ => 
          match slt_C_id_ann_certs_d A with 
          |  Certify_SLT_Id_Ann_Proof_Equal ppf =>  
              slt_C_zero_is_ltr_ann_classify_slt 
              {|
                    slt_C_zero_is_ltr_ann_carrier := slt_C_carrier A 
                  ; slt_C_zero_is_ltr_ann_label := slt_C_label A
                  ; slt_C_zero_is_ltr_ann_plus  := slt_C_plus A                               
                  ; slt_C_zero_is_ltr_ann_trans   := slt_C_trans A 
                  ; slt_C_zero_is_ltr_ann_plus_certs  := slt_C_plus_certs A                           
                  ; slt_C_zero_is_ltr_ann_trans_certs := slt_C_trans_certs A 
                  ; slt_C_zero_is_ltr_ann_exists_plus_ann_d := slt_C_exists_plus_ann_d A                               
                  ; slt_C_zero_is_ltr_ann_id_ann_certs := Assert_Slt_Exists_Id_Ann_Equal ppf                                            
                  ; slt_C_zero_is_ltr_ann_certs := pf                              
                  ; slt_C_zero_is_ltr_ann_ast := slt_C_ast A 
              
              |}
          | _ => SLT_C A
          end
        end
     | SLT_dioid_certs _ => SLT_C A
     | SLT_semiring_certs pf => 
        slt_classify_left_pre_semiring_slt
        {|
              left_pre_semiring_carrier :=  slt_C_carrier A
            ; left_pre_semiring_label := slt_C_label A
            ; left_pre_semiring_plus  := slt_C_plus A                                            
            ; left_pre_semiring_trans := slt_C_trans A
            ; left_pre_semiring_plus_certs  := slt_C_plus_certs A                             
            ; left_pre_semiring_trans_certs  := slt_C_trans_certs A
            ; left_pre_semiring_exists_plus_ann_d := slt_C_exists_plus_ann_d A                              
            ; left_pre_semiring_id_ann_certs_d := slt_C_id_ann_certs_d A
            ; left_pre_semiring_certs := pf
            ; left_pre_semiring_ast   := slt_C_ast A
        |}
    end.


  


  Definition slt_classify_slt {L S : Type} (A : @slt L S) : slt_mcas :=
    let plus_certificate := slt_plus_certs A in
    match sg_certificates_classify (MCAS_Cert_sg plus_certificate) with 
    | MCAS_Cert_sg_C pf => 
        slt_C_classify_slt
        {|
              slt_C_carrier  := slt_carrier A
            ; slt_C_label  := slt_label A 
            ; slt_C_plus  := slt_plus A                                            
            ; slt_C_trans   := slt_trans A 
            ; slt_C_plus_certs := pf                       
            ; slt_C_trans_certs := slt_trans_certs A 
            ; slt_C_exists_plus_ann_d := slt_exists_plus_ann_d A                                
            ; slt_C_id_ann_certs_d  := slt_id_ann_certs_d A                                       
            ; slt_C_certs := slt_certs A                             
            ; slt_C_ast := slt_ast A
        |}
    | _ => SLT A  
    end.


  
  Definition slt_classify {L S : Type} (A : @slt_mcas L S) : @slt_mcas L S :=
    match A with
    | SLT_Error ls => A
    | SLT slt => slt_classify_slt slt
    | SLT_C slt => slt_C_classify_slt slt 
    | SLT_CS slt => slt_CS_classify_slt slt
    | SLT_CI slt => slt_CI_classify_slt slt 
    | SLT_C_Zero_Is_Ltr_ann slt => slt_C_zero_is_ltr_ann_classify_slt slt
    | SLT_Left_Pre_Semiring slt => slt_classify_left_pre_semiring_slt slt  
    | SLT_Dioid slt => slt_classify_left_dioid_slt slt 
    | SLT_Selective_Left_Pre_Dioid slt => slt_classify_selective_left_pre_dioid_slt slt
    | SLT_Semiring slt => slt_classify_left_semiring_slt slt 
    | SLT_Selective_Dioid slt => slt_classify_selective_left_dioid_slt slt 
    | SLT_Selective_Semiring slt => slt_classify_left_selective_semiring_slt slt
    | SLT_Idempotent_Semiring slt => slt_classify_left_idempotent_semiring_slt slt
    end. 

  (* all good upto here*)

End MCAS.


Section Translation.


  Definition P2C_slt {L S : Type}  (r : brel S) (add : binary_op S) (ltr : ltr_type L S) :
    @slt_proofs L S r add ltr -> @slt_certificates L S :=
    λ A,  
    {|
      slt_distributive_d          := p2c_slt_distributive_check r add ltr 
        (A_slt_distributive_d _ _ _ A)
    ; slt_absorptive_d            := p2c_slt_absorptive_check r add ltr
        (A_slt_absorptive_d _ _ _ A) 
    ; slt_strictly_absorptive_d   := p2c_slt_strictly_absorptive_check r add ltr
        (A_slt_strictly_absorptive_d _ _ _ A)
    |}.


  Definition P2C_left_dioid {L S : Type} (r : brel S) (add : binary_op S) (ltr : ltr_type L S) :
    @left_dioid_proofs L S r add ltr -> @left_dioid_certificates L S :=
    λ A, 
    {|
      left_dioid_distributive            := p2c_slt_distributive_assert r add ltr 
        ( A_left_dioid_distributive _ _ _ A)
    ; left_dioid_absorptive              := p2c_slt_absorptive_assert r add ltr
        (A_left_dioid_absorptive _ _ _ A)                                          
    ; left_dioid_strictly_absorptive_d := p2c_slt_strictly_absorptive_check r add ltr
        (A_left_dioid_strictly_absorptive_d _ _ _ A)
    |}.


  Definition P2C_left_semiring {L S : Type} (r : brel S) (add : binary_op S) (ltr : ltr_type L S) :
    @left_semiring_proofs L S r add ltr -> @left_semiring_certificates L S :=
    λ A,
    {|
      left_semiring_distributive            := p2c_slt_distributive_assert r add ltr
        (A_left_semiring_distributive  _ _ _ A) 
    ; left_semiring_not_absorptive          := p2c_slt_not_absorptive_assert r add ltr
        (A_left_semiring_not_absorptive _ _ _ A)                              
    |}.
      

  Definition A2C_slt {L S : Type} :
    @A_slt L S -> @slt L S :=
    λ A, 
    {|
        slt_carrier := A2C_eqv _ (A_slt_carrier A)
      ; slt_label := A2C_eqv _ (A_slt_label A)
      ; slt_plus := A_slt_plus A
      ; slt_trans := A_slt_trans A
      ; slt_plus_certs := P2C_sg _ _ _ (A_slt_plus_proofs A)
      ; slt_trans_certs := P2C_left_transform _ _ _ _ _ (A_slt_trans_proofs A) 
      ; slt_exists_plus_ann_d := p2c_exists_ann_check _ _ _ (A_slt_exists_plus_ann_d A)
      ; slt_id_ann_certs_d := @p2c_slt_exists_id_ann_check L S _ _ _ (A_slt_id_ann_proofs_d A) 
      ; slt_certs := @P2C_slt L S _ _ _ (A_slt_proofs A)
      ; slt_ast := A_slt_ast  A
    |}.

  Definition A2C_slt_c {L S : Type} :
    @A_slt_C L S -> @slt_C L S := 
    λ A,
    {|
        slt_C_carrier := A2C_eqv _ (A_slt_C_carrier A)
      ; slt_C_label := A2C_eqv _ (A_slt_C_label A)
      ; slt_C_plus  := A_slt_C_plus A                                             
      ; slt_C_trans := A_slt_C_trans A
      ; slt_C_plus_certs := P2C_sg_C _ _ _ (A_slt_C_plus_proofs A)                         
      ; slt_C_trans_certs  := P2C_left_transform _ _ _ _ _ (A_slt_C_trans_proofs A) 
      ; slt_C_exists_plus_ann_d := p2c_exists_ann_check _ _ _ (A_slt_C_exists_plus_ann_d A)                             
      ; slt_C_id_ann_certs_d  := @p2c_slt_exists_id_ann_check L S _ _ _ (A_slt_C_id_ann_proofs_d A)                                        
      ; slt_C_certs := @P2C_slt L S _ _ _ (A_slt_C_proofs A)                             
      ; slt_C_ast := A_slt_C_ast A
    |}.
    
    


  Definition A2C_slt_cs {L S : Type} :
    @A_slt_CS L S -> @slt_CS L S :=
    λ A, 
    {|
        slt_CS_carrier := A2C_eqv _ (A_slt_CS_carrier A)
      ; slt_CS_label := A2C_eqv _ (A_slt_CS_label A) 
      ; slt_CS_plus  := A_slt_CS_plus A                                               
      ; slt_CS_trans   := A_slt_CS_trans A 
      ; slt_CS_plus_certs  := P2C_sg_CS _ _ _ (A_slt_CS_plus_proofs A)   (* This is wrong *)                    
      ; slt_CS_trans_certs := P2C_left_transform _ _ _ _ _ (A_slt_CS_trans_proofs A) 
      ; slt_CS_exists_plus_ann_d := p2c_exists_ann_check _ _ _ (A_slt_CS_exists_plus_ann_d A)                                 
      ; slt_CS_id_ann_certs_d  := @p2c_slt_exists_id_ann_check L S _ _ _ (A_slt_CS_id_ann_proofs_d A)                                          
      ; slt_CS_certs := @P2C_slt L S _ _ _ (A_slt_CS_proofs A)                               
      ; slt_CS_ast := A_slt_CS_ast  A 
    |}.




  Definition A2C_slt_ci {L S : Type} :
    @A_slt_CI L S -> @slt_CI L S :=
    λ A,
    {|
        slt_CI_carrier := A2C_eqv _ (A_slt_CI_carrier A)
      ; slt_CI_label := A2C_eqv _ (A_slt_CI_label A) 
      ; slt_CI_plus  := A_slt_CI_plus A                                               
      ; slt_CI_trans   := A_slt_CI_trans A 
      ; slt_CI_plus_certs  := P2C_sg_CI _ _ _ (A_slt_CI_plus_proofs A)                    
      ; slt_CI_trans_certs := P2C_left_transform _ _ _ _ _ (A_slt_CI_trans_proofs A) 
      ; slt_CI_exists_plus_ann_d := p2c_exists_ann_check _ _ _ (A_slt_CI_exists_plus_ann_d A)                                 
      ; slt_CI_id_ann_certs_d  := @p2c_slt_exists_id_ann_check L S _ _ _ (A_slt_CI_id_ann_proofs_d A)                                          
      ; slt_CI_certs := @P2C_slt L S _ _ _ (A_slt_CI_proofs A)                               
      ; slt_CI_ast := A_slt_CI_ast  A 
    |}.

  Definition A2C_slt_C_zero_is_ltr_ann {L S : Type} :  
    @A_slt_C_zero_is_ltr_ann L S -> @slt_C_zero_is_ltr_ann L S := 
    λ A,
    {|
        slt_C_zero_is_ltr_ann_carrier  := A2C_eqv _ (A_slt_C_zero_is_ltr_ann_carrier A)
      ; slt_C_zero_is_ltr_ann_label := A2C_eqv _ (A_slt_C_zero_is_ltr_ann_label A)
      ; slt_C_zero_is_ltr_ann_plus  := A_slt_C_zero_is_ltr_ann_plus A                                                 
      ; slt_C_zero_is_ltr_ann_trans := A_slt_C_zero_is_ltr_ann_trans A
      ; slt_C_zero_is_ltr_ann_plus_certs  := P2C_sg_C _ _ _ (A_slt_C_zero_is_ltr_ann_plus_proofs A)                           
      ; slt_C_zero_is_ltr_ann_trans_certs := P2C_left_transform _ _ _ _ _ (A_slt_C_zero_is_ltr_ann_trans_proofs A) 
      ; slt_C_zero_is_ltr_ann_exists_plus_ann_d := p2c_exists_ann_check _ _ _ (A_slt_C_zero_is_ltr_ann_exists_plus_ann_d A)                                                          
      ; slt_C_zero_is_ltr_ann_id_ann_certs  := @p2c_slt_exists_id_ann_equal_assert L S _ _ _ (A_slt_C_zero_is_ltr_ann_id_ann_proofs A)                                                                                  
      ; slt_C_zero_is_ltr_ann_certs:= @P2C_slt L S _ _ _ (A_slt_C_zero_is_ltr_ann_proofs A)                                 
      ; slt_C_zero_is_ltr_ann_ast := A_slt_C_zero_is_ltr_ann_ast A 
    |}. 
  

  Definition A2C_selective_left_dioid {L S : Type} :
    @A_selective_left_dioid L S -> @selective_left_dioid L S :=
    λ A, 
    {|
        selective_left_dioid_carrier := A2C_eqv _ (A_selective_left_dioid_carrier A) 
      ; selective_left_dioid_label := A2C_eqv _ (A_selective_left_dioid_label A)
      ; selective_left_dioid_plus := A_selective_left_dioid_plus A
      ; selective_left_dioid_trans  := A_selective_left_dioid_trans A
      ; selective_left_dioid_plus_certs := P2C_sg_CS _ _ _ (A_selective_left_dioid_plus_proofs A)
      ; selective_left_dioid_trans_certs := P2C_left_transform _ _ _ _ _ (A_selective_left_dioid_trans_proofs A)
      ; selective_left_dioid_exists_plus_ann := p2c_exists_ann_assert _ _ _ (A_selective_left_dioid_exists_plus_ann A)
      ; selective_left_dioid_id_ann_certs := @p2c_slt_exists_id_ann_equal_assert L S _ _ _ (A_selective_left_dioid_id_ann_proofs A)
      ; selective_left_dioid_certs := @P2C_left_dioid L S _ _ _ (A_selective_left_dioid_proofs A)
      ; selective_left_dioid_ast := A_selective_left_dioid_ast A   
    |}.

  Definition A2C_selective_left_pre_dioid {L S : Type} :
    @A_selective_left_pre_dioid L S -> @selective_left_pre_dioid L S :=
    λ A,
    {|
        selective_left_pre_dioid_carrier      := A2C_eqv _ (A_selective_left_pre_dioid_carrier A) 
      ; selective_left_pre_dioid_label        := A2C_eqv _ (A_selective_left_pre_dioid_label A)
      ; selective_left_pre_dioid_plus         := A_selective_left_pre_dioid_plus A                                               
      ; selective_left_pre_dioid_trans        := A_selective_left_pre_dioid_trans A
      ; selective_left_pre_dioid_plus_certs   := P2C_sg_CS _ _ _ (A_selective_left_pre_dioid_plus_proofs A)
      ; selective_left_pre_dioid_trans_certs  := P2C_left_transform _ _ _ _ _ (A_selective_left_pre_dioid_trans_proofs A)
      ; selective_left_pre_dioid_exists_plus_ann := p2c_exists_ann_assert _ _ _ (A_selective_left_pre_dioid_exists_plus_ann A)                         
      ; selective_left_pre_dioid_id_ann_certs_d := p2c_slt_exists_id_ann_check _ _ _ (A_selective_left_pre_dioid_id_ann_proofs_d A)                 
      ; selective_left_pre_dioid_certs :=  @P2C_left_dioid L S _ _ _ (A_selective_left_pre_dioid_proofs A)                              
      ; selective_left_pre_dioid_ast := A_selective_left_pre_dioid_ast A   
    |}.
  

    
  Definition A2C_left_dioid  {L S : Type} :
    @A_left_dioid L S -> @left_dioid L S :=
    λ A, 
    {|
        left_dioid_carrier := A2C_eqv _ (A_left_dioid_carrier A)
      ; left_dioid_label := A2C_eqv _ (A_left_dioid_label A)
      ; left_dioid_plus := A_left_dioid_plus A
      ; left_dioid_trans  := A_left_dioid_trans A
      ; left_dioid_plus_certs := P2C_sg_CI _ _ _ (A_left_dioid_plus_proofs A)
      ; left_dioid_trans_certs := P2C_left_transform _ _ _ _ _ (A_left_dioid_trans_proofs A)
      ; left_dioid_exists_plus_ann := p2c_exists_ann_assert _ _ _ (A_left_dioid_exists_plus_ann A)
      ; left_dioid_id_ann_certs := @p2c_slt_exists_id_ann_equal_assert L S _ _ _ (A_left_dioid_id_ann_proofs A)
      ; left_dioid_certs := @P2C_left_dioid L S _ _ _ (A_left_dioid_proofs A)
      ; left_dioid_ast  := A_left_dioid_ast A  
    |}.

  
  Definition A2C_left_pre_semiring {L S : Type} :
    @A_left_pre_semiring L S -> @left_pre_semiring L S :=
    λ A, 
    {|
        left_pre_semiring_carrier := A2C_eqv _ (A_left_pre_semiring_carrier A)
      ; left_pre_semiring_label := A2C_eqv _ (A_left_pre_semiring_label A)
      ; left_pre_semiring_plus := A_left_pre_semiring_plus A
      ; left_pre_semiring_trans := A_left_pre_semiring_trans A
      ; left_pre_semiring_plus_certs := P2C_sg_C _ _ _ (A_left_pre_semiring_plus_proofs A)
      ; left_pre_semiring_trans_certs := P2C_left_transform _ _ _ _ _ (A_left_pre_semiring_trans_proofs A)
      ; left_pre_semiring_exists_plus_ann_d := p2c_exists_ann_check _ _ _ (A_left_pre_semiring_exists_plus_ann_d A)
      ; left_pre_semiring_id_ann_certs_d := p2c_slt_exists_id_ann_check _ _ _ (A_left_pre_semiring_id_ann_proofs_d A)
      ; left_pre_semiring_certs := P2C_left_semiring _ _ _ (A_left_pre_semiring_proofs A)
      ; left_pre_semiring_ast  := A_left_pre_semiring_ast A 
    |}.

    



  Definition A2C_left_semiring {L S : Type} :
    @A_left_semiring L S -> @left_semiring L S :=
    λ A, 
    {|
        left_semiring_carrier := A2C_eqv _ (A_left_semiring_carrier A)
      ; left_semiring_label := A2C_eqv _ (A_left_semiring_label A)
      ; left_semiring_plus := A_left_semiring_plus A
      ; left_semiring_trans := A_left_semiring_trans A
      ; left_semiring_plus_certs := P2C_sg_C _ _ _ (A_left_semiring_plus_proofs A)
      ; left_semiring_trans_certs := P2C_left_transform _ _ _ _ _ (A_left_semiring_trans_proofs A)
      ; left_semiring_exists_plus_ann_d := p2c_exists_ann_check _ _ _ (A_left_semiring_exists_plus_ann_d A)
      ; left_semiring_id_ann_certs :=  @p2c_slt_exists_id_ann_equal_assert L S _ _ _ (A_left_semiring_id_ann_proofs A)
      ; left_semiring_certs := P2C_left_semiring _ _ _ (A_left_semiring_proofs A)
      ; left_semiring_ast  := A_left_semiring_ast A 
    |}.


  Definition A2C_left_idempotent_semiring {L S : Type} : 
    @A_left_idempotent_semiring L S -> @left_idempotent_semiring L S :=
    λ A,
    {|
        left_idempotent_semiring_carrier := A2C_eqv _ (A_left_idempotent_semiring_carrier A)
      ; left_idempotent_semiring_label := A2C_eqv _ (A_left_idempotent_semiring_label A)
      ; left_idempotent_semiring_plus := A_left_idempotent_semiring_plus A
      ; left_idempotent_semiring_trans := A_left_idempotent_semiring_trans A
      ; left_idempotent_semiring_plus_certs := P2C_sg_CI _ _ _ (A_left_idempotent_semiring_plus_proofs A)
      ; left_idempotent_semiring_trans_certs := P2C_left_transform _ _ _ _ _ (A_left_idempotent_semiring_trans_proofs A)
      ; left_idempotent_semiring_exists_plus_ann_d := p2c_exists_ann_check _ _ _ (A_left_idempotent_semiring_exists_plus_ann_d A)
      ; left_idempotent_semiring_id_ann_certs :=  @p2c_slt_exists_id_ann_equal_assert L S _ _ _ (A_left_idempotent_semiring_id_ann_proofs A)
      ; left_idempotent_semiring_certs := P2C_left_semiring _ _ _ (A_left_idempotent_semiring_proofs A)
      ; left_idempotent_semiring_ast  := A_left_idempotent_semiring_ast A 
    |}.

  
  Definition A2C_left_selective_semiring {L S : Type} :
    @A_left_selective_semiring L S -> @left_selective_semiring L S :=
    λ A, 
    {|
        left_selective_semiring_carrier := A2C_eqv _ (A_left_selective_semiring_carrier A)
      ; left_selective_semiring_label := A2C_eqv _ (A_left_selective_semiring_label A)
      ; left_selective_semiring_plus := A_left_selective_semiring_plus A
      ; left_selective_semiring_trans := A_left_selective_semiring_trans A
      ; left_selective_semiring_plus_certs := P2C_sg_CS _ _ _ (A_left_selective_semiring_plus_proofs A)
      ; left_selective_semiring_trans_certs := P2C_left_transform _ _ _ _ _ (A_left_selective_semiring_trans_proofs A)
      ; left_selective_semiring_exists_plus_ann_d := p2c_exists_ann_check _ _ _ (A_left_selective_semiring_exists_plus_ann_d A)
      ; left_selective_semiring_id_ann_certs :=  @p2c_slt_exists_id_ann_equal_assert L S _ _ _ (A_left_selective_semiring_id_ann_proofs A)
      ; left_selective_semiring_certs := P2C_left_semiring _ _ _ (A_left_selective_semiring_proofs A)
      ; left_selective_semiring_ast  := A_left_selective_semiring_ast A 
    |}.


  

  Definition A2C_mcas_slt {L S : Type} :
    @A_slt_mcas L S -> @slt_mcas L S :=
    λ A, match A with
      | A_SLT_Error err => SLT_Error err    
      | A_SLT pf => SLT (A2C_slt pf)
      | A_SLT_C pf => SLT_C (A2C_slt_c pf)
      | A_SLT_CS pf => SLT_CS (A2C_slt_cs pf)
      | A_SLT_CI pf => SLT_CI (A2C_slt_ci pf)
      | A_SLT_C_Zero_Is_Ltr_ann pf => SLT_C_Zero_Is_Ltr_ann (A2C_slt_C_zero_is_ltr_ann pf)
      | A_SLT_Dioid pf => SLT_Dioid (A2C_left_dioid pf) 
      | A_SLT_Selective_Dioid pf => SLT_Selective_Dioid (A2C_selective_left_dioid pf)
      | A_SLT_Selective_Left_Pre_Dioid pf => SLT_Selective_Left_Pre_Dioid (A2C_selective_left_pre_dioid pf)
      | A_SLT_Left_Pre_Semiring pf => SLT_Left_Pre_Semiring (A2C_left_pre_semiring pf) 
      | A_SLT_Semiring pf => SLT_Semiring (A2C_left_semiring pf) 
      | A_SLT_Selective_Semiring  pf => SLT_Selective_Semiring (A2C_left_selective_semiring pf)
      | A_SLT_Idempotent_Semiring pf => SLT_Idempotent_Semiring (A2C_left_idempotent_semiring pf)
    end.



  Definition P2C_proofs_mcas_slt {L S : Type} 
    (r : brel S) (add : binary_op S) (ltr : ltr_type L S) :
    @A_slt_mcas_proofs L S r add ltr -> @slt_mcas_certificates L S :=
    λ A, match A with
    | A_SLT_proofs _ _ _ pf => SLT_certs (P2C_slt r add ltr pf)
    | A_SLT_dioid_proofs  _ _ _ pf => SLT_dioid_certs (P2C_left_dioid r add ltr pf)
    | A_SLT_semiring_proofs _ _ _ pf => SLT_semiring_certs (P2C_left_semiring r add ltr pf)
    end.



End Translation.

Section Verify.

  
  Context 
    {L S : Type}.

 
  
  Lemma correctness_slt_classify_certificates_proofs 
    (r : brel S) (add : binary_op S) (ltr : ltr_type L S)
    (s : slt_proofs r add ltr) :
    slt_classify_certificates (P2C_slt r add ltr s) = 
    P2C_proofs_mcas_slt r add ltr (A_slt_classify_proofs r add ltr s).
  Proof.
      unfold 
        slt_classify_certificates, 
        A_slt_classify_proofs; 
      destruct s, 
      A_slt_distributive_d0;
      simpl.
      + destruct A_slt_absorptive_d0.
        ++ reflexivity.
        ++ reflexivity.   
      + reflexivity.
  Qed.

  Lemma correctness_slt_classify_left_dioid_slt :
    forall a, 
    slt_classify_left_dioid_slt (A2C_left_dioid a) = 
    @SLT_Dioid L S (A2C_left_dioid a).
  Proof.
    intros ?.
    reflexivity.
  Qed.


  Lemma correctness_slt_classify_selective_left_dioid_slt :
    forall a, 
    slt_classify_selective_left_dioid_slt (A2C_selective_left_dioid a) =
    @SLT_Selective_Dioid L S (A2C_selective_left_dioid a).
  Proof.
    intros ?.
    reflexivity.
  Qed.

  

  Lemma correctness_slt_classify_selective_left_pre_dioid_slt :
    forall a, 
    slt_classify_selective_left_pre_dioid_slt (A2C_selective_left_pre_dioid a) =
    @A2C_mcas_slt L S (A_slt_classify_selective_left_pre_dioid_slt a).
  Proof.
    unfold 
      slt_classify_selective_left_pre_dioid_slt,
      A2C_selective_left_pre_dioid,
      A2C_mcas_slt,
      A_slt_classify_selective_left_pre_dioid_slt;
    destruct a, 
      A_selective_left_pre_dioid_id_ann_proofs_d0;
    simpl; try (destruct p; reflexivity).
    + rewrite <- correctness_slt_classify_selective_left_dioid_slt;
      reflexivity.
    + reflexivity.
  Qed.

  Lemma correctness_slt_classify_left_selective_semiring_slt :
    forall a,
    slt_classify_left_selective_semiring_slt (A2C_left_selective_semiring a) =
    @SLT_Selective_Semiring L S (A2C_left_selective_semiring a).
  Proof.
    intros ?.
    reflexivity.
  Qed.


  Lemma correctness_slt_classify_left_idempotent_semiring_slt :
    forall a, 
    slt_classify_left_idempotent_semiring_slt (A2C_left_idempotent_semiring a) =
    @SLT_Idempotent_Semiring L S (A2C_left_idempotent_semiring a).
  Proof.
    intros ?.
    reflexivity.
  Qed.



  Lemma correctness_slt_classify_left_semiring_slt :
    forall a, 
    slt_classify_left_semiring_slt (A2C_left_semiring a) =
    @A2C_mcas_slt L S (A_slt_classify_left_semiring_slt a).
  Proof.
    unfold slt_classify_left_semiring_slt,
    A_slt_classify_left_semiring_slt; destruct a; 
    simpl.
    rewrite correct_sg_certificates_classify_sg_C.
    destruct (A_sg_proofs_classify_sg_C S (A_eqv_eq S A_left_semiring_carrier0)
    A_left_semiring_plus0 A_left_semiring_plus_proofs0); 
    simpl; try reflexivity.
  Qed.
   
  



  Lemma correctness_slt_classify_left_pre_semiring_slt :
    forall a, 
    slt_classify_left_pre_semiring_slt (A2C_left_pre_semiring a) =
    @A2C_mcas_slt L S (A_slt_classify_left_pre_semiring_slt a).
  Proof.
    unfold 
      slt_classify_left_pre_semiring_slt,
      A_slt_classify_left_pre_semiring_slt.
    destruct a,
    A_left_pre_semiring_id_ann_proofs_d0;
    simpl; try (destruct p; reflexivity).
    + rewrite <-correctness_slt_classify_left_semiring_slt.
      reflexivity.
    + reflexivity.
  Qed.  







  Lemma correctness_slt_C_zero_is_ltr_ann_classify_slt :
    forall a, 
    slt_C_zero_is_ltr_ann_classify_slt (A2C_slt_C_zero_is_ltr_ann a) =
    @A2C_mcas_slt L S (A_slt_C_zero_is_ltr_ann_classify_slt a).
  Proof.
    unfold slt_C_zero_is_ltr_ann_classify_slt,
    A_slt_C_zero_is_ltr_ann_classify_slt;
    destruct a; simpl.
    rewrite correctness_slt_classify_certificates_proofs.
    destruct (A_slt_classify_proofs (A_eqv_eq S A_slt_C_zero_is_ltr_ann_carrier0)
    A_slt_C_zero_is_ltr_ann_plus0 A_slt_C_zero_is_ltr_ann_trans0
    A_slt_C_zero_is_ltr_ann_proofs0); simpl;
    try reflexivity.
    + 
      rewrite correct_sg_certificates_classify_sg_C.
      destruct (A_sg_proofs_classify_sg_C S
      (A_eqv_eq S A_slt_C_zero_is_ltr_ann_carrier0)
      A_slt_C_zero_is_ltr_ann_plus0 A_slt_C_zero_is_ltr_ann_plus_proofs0);
      simpl; try reflexivity.
      destruct A_slt_C_zero_is_ltr_ann_exists_plus_ann_d0; 
      simpl; try reflexivity.
      destruct A_slt_C_zero_is_ltr_ann_exists_plus_ann_d0;
      simpl; try reflexivity.
    + 
      rewrite <-correctness_slt_classify_left_semiring_slt.
      f_equal.
  Qed.
  






  Lemma correctness_slt_CS_classify_slt : 
    forall a, 
    slt_CS_classify_slt (A2C_slt_cs a) = 
    @A2C_mcas_slt L S (A_slt_CS_classify_slt a).
  Proof.
    unfold 
      slt_CS_classify_slt,
      A_slt_CS_classify_slt.
    destruct a; simpl.
    rewrite correctness_slt_classify_certificates_proofs.
    destruct (A_slt_classify_proofs (A_eqv_eq S A_slt_CS_carrier0) 
      A_slt_CS_plus0 A_slt_CS_trans0
      A_slt_CS_proofs0);
    simpl.
    + reflexivity.
    + destruct A_slt_CS_exists_plus_ann_d0;
      simpl.
      ++ rewrite <-correctness_slt_classify_selective_left_pre_dioid_slt;
          reflexivity.
      ++ reflexivity.
    + destruct A_slt_CS_id_ann_proofs_d0;
      simpl; try (destruct p; reflexivity).
      ++ rewrite <-correctness_slt_classify_left_selective_semiring_slt;
          reflexivity.
      ++ reflexivity.
  Qed.      







  Lemma correctness_slt_CI_classify_slt :
    forall a,
    slt_CI_classify_slt (A2C_slt_ci a) = 
    @A2C_mcas_slt L S (A_slt_CI_classify_slt a).
  Proof.
    unfold 
      slt_CI_classify_slt,
      A_slt_CI_classify_slt.
    destruct a; simpl.
    rewrite correctness_slt_classify_certificates_proofs.
    destruct (A_slt_classify_proofs (A_eqv_eq S A_slt_CI_carrier0) 
      A_slt_CI_plus0 A_slt_CI_trans0
      A_slt_CI_proofs0);
    simpl.
    + reflexivity.
    + destruct A_slt_CI_exists_plus_ann_d0; simpl.
      ++ destruct A_slt_CI_id_ann_proofs_d0;
         try (destruct p; reflexivity);
         reflexivity.   
      ++ reflexivity.
    + destruct A_slt_CI_id_ann_proofs_d0;
      try (destruct p; reflexivity);
      reflexivity.   
  Qed.
  





  Lemma correctness_slt_C_classify_slt : 
    forall a, 
    slt_C_classify_slt (A2C_slt_c a) = 
    @A2C_mcas_slt L S (A_slt_C_classify_slt a).
  Proof.
    unfold slt_C_classify_slt,
    A_slt_C_classify_slt;
    destruct a; simpl.
    rewrite correctness_slt_classify_certificates_proofs.
    destruct (A_slt_classify_proofs (A_eqv_eq S A_slt_C_carrier0) A_slt_C_plus0
    A_slt_C_trans0 A_slt_C_proofs0); simpl;
    try reflexivity.
    rewrite correct_sg_certificates_classify_sg_C.
    destruct (A_sg_proofs_classify_sg_C S (A_eqv_eq S A_slt_C_carrier0)
    A_slt_C_plus0 A_slt_C_plus_proofs0); simpl;
    try reflexivity.
    + destruct A_slt_C_id_ann_proofs_d0;
      simpl; try (destruct p; reflexivity).
      ++ 
      rewrite <-correctness_slt_C_zero_is_ltr_ann_classify_slt.
      reflexivity.
      ++ 
      reflexivity.
    + destruct A_slt_C_id_ann_proofs_d0;
      simpl; try (destruct p; reflexivity).
      ++ 
      rewrite <-correctness_slt_C_zero_is_ltr_ann_classify_slt.
      reflexivity.
      ++ 
      reflexivity.
    + destruct A_slt_C_id_ann_proofs_d0;
      simpl; try (destruct p; reflexivity).
      ++ 
      rewrite <-correctness_slt_C_zero_is_ltr_ann_classify_slt.
      reflexivity.
      ++ 
      reflexivity.
    + destruct A_slt_C_id_ann_proofs_d0;
      simpl; try (destruct p; reflexivity).
      ++ 
      rewrite <-correctness_slt_C_zero_is_ltr_ann_classify_slt.
      reflexivity.
      ++ 
      reflexivity.  
    + rewrite <-correctness_slt_CS_classify_slt.
      reflexivity.
    + rewrite <-correctness_slt_CI_classify_slt.
      reflexivity.
    + destruct A_slt_C_id_ann_proofs_d0;
      simpl; try (destruct p; reflexivity).
      ++ 
      rewrite <-correctness_slt_C_zero_is_ltr_ann_classify_slt.
      reflexivity.
      ++ 
      reflexivity.
    + destruct A_slt_C_id_ann_proofs_d0;
      simpl; try (destruct p; reflexivity).
      ++ 
      rewrite <-correctness_slt_C_zero_is_ltr_ann_classify_slt.
      reflexivity.
      ++ 
      reflexivity. 
    + rewrite <-correctness_slt_classify_left_pre_semiring_slt.
      reflexivity.
  Qed.
   



  Lemma correctness_slt_classify_slt : 
    forall pf,
    slt_classify_slt (A2C_slt pf) = 
    @A2C_mcas_slt L S (A_slt_classify_slt pf).
  Proof.
    unfold 
      slt_classify_slt,
      A_slt_classify_slt.
    destruct pf; simpl.
    rewrite correct_sg_certificates_classify_sg.
    destruct ((A_sg_proofs_classify_sg S (A_eqv_eq S A_slt_carrier0) 
      A_slt_plus0 A_slt_plus_proofs0));
      unfold P2C_proofs_mcas_sg; try reflexivity.
    + rewrite <-correctness_slt_C_classify_slt.
      reflexivity.
  Qed.


Lemma correctness_slt_classify : 
  forall pf,  
  slt_classify (A2C_mcas_slt pf) = 
  @A2C_mcas_slt L S (A_slt_classify pf).
Proof.
  destruct pf; simpl.
  + reflexivity.
  + apply correctness_slt_classify_slt.  
  + apply correctness_slt_C_classify_slt. 
  + apply correctness_slt_CS_classify_slt.
  + apply correctness_slt_CI_classify_slt.
  + apply correctness_slt_C_zero_is_ltr_ann_classify_slt.
  + apply correctness_slt_classify_left_dioid_slt.
  + apply correctness_slt_classify_selective_left_pre_dioid_slt.
  + apply correctness_slt_classify_selective_left_dioid_slt.
  + apply correctness_slt_classify_left_pre_semiring_slt.
  + apply correctness_slt_classify_left_semiring_slt.
  + apply correctness_slt_classify_left_selective_semiring_slt.
  + apply correctness_slt_classify_left_idempotent_semiring_slt.          
Qed.      


End Verify.