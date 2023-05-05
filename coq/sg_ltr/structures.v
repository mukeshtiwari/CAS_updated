Require Import Coq.Strings.String.
Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast. 
Require Import CAS.coq.eqv.structures. 
Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures. 
Require Import CAS.coq.ltr.structures.
Require Import CAS.coq.sg_ltr.properties.

(* SG_LTR = Semigroup with a Left Transform 

Comparison to bi-semigroups (bs)

For bs, 0-stability means id(x) = ann(+), so there is no point in going around loops. 
Note that with left distributivity this implies absorption: 
    a (+) (a (x) b) = a (x) (id (+) b) = a (x) id = a. 
However, this kind of argument does not work for sg_ltr. 
A_sg_ltr_absorptive means 
    for all l, s, s = s (+) (l |> s). 
This cannot be derived from properties of ann(+), etc. 
We do want to know if there exists ann(+). But note that it makes no
sense for this to be an id of the multiplicative component, 
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




Section ACAS.
  
Record A_sg_ltr_properties {L S : Type} (r : brel S) 
  (add : binary_op S) (ltr : ltr_type L S) :=
{
  A_sg_ltr_distributive_d 
    : A_sg_ltr_distributive_decidable r add ltr
; A_sg_ltr_absorptive_d 
    : A_sg_ltr_absorptive_decidable r add ltr
; A_sg_ltr_strictly_absorptive_d 
  : A_sg_ltr_strictly_absorptive_decidable r add ltr  
}.

Record A_sg_ltr {L S : Type} :=
{
  A_sg_ltr_carrier        : A_eqv S
; A_sg_ltr_label          : A_eqv L
; A_sg_ltr_plus           : binary_op S  
; A_sg_ltr_ltr            : ltr_type L S (* L -> (S -> S) *)
; A_sg_ltr_plus_props     : sg_C_proofs S
                              (A_eqv_eq S A_sg_ltr_carrier)
                              A_sg_ltr_plus                           
; A_sg_ltr_ltr_props      :  A_ltr_properties
                               (A_eqv_eq L A_sg_ltr_label)                                 
                               (A_eqv_eq S A_sg_ltr_carrier) 
                               A_sg_ltr_ltr
; A_sg_ltr_id_ann_props_d  : A_sg_ltr_exists_id_ann_decidable 
                                (A_eqv_eq S A_sg_ltr_carrier) 
                                A_sg_ltr_plus  
                                A_sg_ltr_ltr 
; A_sg_ltr_props           : A_sg_ltr_properties 
                               (A_eqv_eq S A_sg_ltr_carrier) 
                               A_sg_ltr_plus 
                               A_sg_ltr_ltr
; A_sg_ltr_ast             : cas_ast
}.


End ACAS.

Section AMCAS.                                                    

Inductive A_below_sg_ltr {L S : Type} := 
| A_Below_sg_ltr_top          : @A_sg_ltr L S -> @A_below_sg_ltr L S
.

Inductive A_sg_ltr_mcas {L S : Type} := 
| A_MCAS_sg_ltr_Error        : list string      -> @A_sg_ltr_mcas L S
| A_MCAS_sg_ltr              : @A_below_sg_ltr L S -> @A_sg_ltr_mcas L S
.  

End AMCAS.       



Section CAS.

Record sg_ltr_properties {L S : Type} := 
{
  sg_ltr_distributive_d 
    : @sg_ltr_distributive_decidable L S
; sg_ltr_absorptive_d 
    : @sg_ltr_absorptive_decidable L S 
; sg_ltr_strictly_absorptive_d 
    : @sg_ltr_strictly_absorptive_decidable L S
}.

Record sg_ltr {L S : Type} :=
{
  sg_ltr_carrier        : @eqv S
; sg_ltr_label          : @eqv L
; sg_ltr_plus           : @binary_op S  
; sg_ltr_ltr            : @ltr_type L S 
; sg_ltr_plus_props     : @sg_C_certificates S
; sg_ltr_ltr_props      : @ltr_properties L S
; sg_ltr_id_ann_props_d  : @sg_ltr_exists_id_ann_decidable L S
; sg_ltr_props           : @sg_ltr_properties L S
; sg_ltr_ast             : cas_ast
}.

  
    
End CAS.

Section MCAS.

Inductive below_sg_ltr {L S : Type} := 
| Below_sg_ltr_top          : @sg_ltr L S -> @below_sg_ltr L S
.

Inductive sg_ltr_mcas {L S : Type} := 
| MCAS_sg_ltr_Error        : list string      -> @sg_ltr_mcas L S
| MCAS_sg_ltr              : @below_sg_ltr L S -> @sg_ltr_mcas L S
.  

End MCAS.


Section Translation.


  Definition P2C_sg_ltr_properties {L S : Type}
    (r : brel S) (add : binary_op S) (ltr : ltr_type L S) 
    (A : A_sg_ltr_properties r add ltr) (wL : L) (wS : S) :
    @sg_ltr_properties L S :=
    {|
      sg_ltr_distributive_d          :=
        p2c_sg_ltr_distributive_decidable r add ltr 
          (A_sg_ltr_distributive_d _ _ _ A) wL wS 
    ; sg_ltr_absorptive_d            :=
        p2c_sg_ltr_absorptive_decidable r add ltr
          (A_sg_ltr_absorptive_d _ _ _ A) wL wS 
    ; sg_ltr_strictly_absorptive_d   :=
        p2c_sg_ltr_strictly_absorptive_decidable r add ltr
          (A_sg_ltr_strictly_absorptive_d _ _ _ A) wL wS 
    |}.


  Definition A2C_sg_ltr {L S : Type} 
    (A : @A_sg_ltr L S) : @sg_ltr L S :=
    let wL := A_eqv_witness _ (A_sg_ltr_label A) in
    let wS := A_eqv_witness _ (A_sg_ltr_carrier A) in     
    {|
        sg_ltr_carrier           := A2C_eqv _ (A_sg_ltr_carrier A)
      ; sg_ltr_label             := A2C_eqv _ (A_sg_ltr_label A)
      ; sg_ltr_plus              := A_sg_ltr_plus A
      ; sg_ltr_ltr               := A_sg_ltr_ltr A
      ; sg_ltr_plus_props        := P2C_sg_C _ _ (A_sg_ltr_plus_props A)
      ; sg_ltr_ltr_props         := P2C_ltr_properties _ _ _ (A_sg_ltr_ltr_props A) wL wS 
      ; sg_ltr_id_ann_props_d    := @p2c_sg_ltr_exists_id_ann_decidable L S _ _ _ (A_sg_ltr_id_ann_props_d A) 
      ; sg_ltr_props             := @P2C_sg_ltr_properties _ _ _ _ _ (A_sg_ltr_props A) wL wS 
      ; sg_ltr_ast               := A_sg_ltr_ast  A
    |}.


  Definition A2C_below_sg_ltr {L S : Type} (A : @A_below_sg_ltr L S) : @below_sg_ltr L S :=
  match A with
  | A_Below_sg_ltr_top B => Below_sg_ltr_top (A2C_sg_ltr B)
  end. 

  Definition A2C_mcas_sg_ltr {L S : Type} (A : @A_sg_ltr_mcas L S) : @sg_ltr_mcas L S :=
    match A with
    | A_MCAS_sg_ltr_Error s  => MCAS_sg_ltr_Error s
    | A_MCAS_sg_ltr B        => MCAS_sg_ltr (A2C_below_sg_ltr B)
    end. 

End Translation.
