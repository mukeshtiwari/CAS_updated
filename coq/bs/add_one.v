
Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.

Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.eqv.theory. 
Require Import CAS.coq.eqv.add_constant.
Require Import CAS.coq.eqv.sum. 

Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures.
Require Import CAS.coq.sg.add_id.
Require Import CAS.coq.sg.add_ann.

Require Import CAS.coq.bs.properties.
Require Import CAS.coq.bs.structures.
Require Import CAS.coq.bs.cast.
Require Import CAS.coq.bs.classify. 


Section Theory.

Variable S : Type.
Variable r : brel S.
Variable c : cas_constant.
Variable b1 b2 : binary_op S.

Variable wS : S. 
Variable refS : brel_reflexive S r. 
Variable symS : brel_symmetric S r.
Variable trnS : brel_transitive S r.


Variable commS : bop_commutative S r b1. 

Notation "a [+ann] b" := (bop_add_ann b a)       (at level 15).
Notation "a [+id] b"  := (bop_add_id b a)       (at level 15).
  

Lemma A_bs_add_one_exists_id_ann_equal_left :    
  A_bs_exists_id_ann_equal r b1 b2 ->
  A_bs_exists_id_ann_equal (brel_sum brel_constant r) (c [+ann] b1) (c [+id] b2). 
Proof. intros [i [Pi Pa]]. exists (inr _ i). 
       assert (fact1 : bop_is_id (with_constant S) (brel_sum brel_constant r) (c [+ann] b1) (inr _ i)). 
          unfold bop_is_id. intros [c1 | s1]; compute; auto. 
       assert (fact2 : bop_is_ann (with_constant S) (brel_sum brel_constant r) (c [+id] b2)(inr _ i)). 
          unfold bop_is_id. intros [c1 | s1]; compute; auto. 
       split; assumption. 
Defined.

Lemma A_bs_add_one_exists_id_ann_equal_right :    
  A_bs_exists_id_ann_equal (brel_sum brel_constant r) (c [+id] b2) (c [+ann] b1). 
Proof. exists (inl _ c). split. 
       apply bop_add_id_is_id; auto. 
       apply bop_add_ann_is_ann; auto. 
Defined. 


Lemma A_bs_add_one_exists_id_ann_not_equal_left :
  A_bs_exists_id_ann_not_equal r b1 b2 ->
  A_bs_exists_id_ann_not_equal (brel_sum brel_constant r) (c [+ann] b1) (c [+id] b2).
Proof. intros [[id ann] [[A B] C]]. 
       exists (inr id, inr ann). split. split.
       intros [c' | s]; compute; auto.
       intros [c' | s]; compute; auto.          
       compute; auto. 
Defined.    



Lemma A_bs_add_one_left_distributive  : 
  bop_idempotent S r b1 ->
  A_bs_left_distributive r b1 b2 -> 
  A_bs_left_absorptive r b1 b2 -> 
        A_bs_left_distributive (brel_sum brel_constant r) (c [+ann] b1) (c [+id] b2). 
Proof. intros idemS ld la. 
       intros [c1 | s1] [c2 | s2] [c3 | s3]; compute; auto.
       + assert (A := la s1 s2).
         assert (B := commS s1 (b2 s1 s2)).
         exact (trnS _ _ _ A B). 
Qed. 

Lemma A_bs_add_one_not_left_distributive_v1 : 
      A_bs_not_left_distributive r b1 b2 -> 
        A_bs_not_left_distributive (brel_sum brel_constant r) (c [+ann] b1) (c [+id] b2). 
Proof. intros [[s1 [s2 s3]] nld]. 
       exists (inr s1, (inr s2, inr s3)).  compute. assumption. 
Defined. 


Lemma A_bs_add_one_not_left_distributive_v2 : 
     bop_not_idempotent S r b1 -> 
        A_bs_not_left_distributive (brel_sum brel_constant r) (c [+ann] b1) (c [+id] b2). 
Proof. intros [s nidem]. 
       exists (inr s, (inl c, inl c)). compute. 
       apply (brel_symmetric_implies_dual _ _ symS). assumption. 
Defined. 

Lemma A_bs_add_one_not_left_distributive_v3 : 
     A_bs_not_left_absorptive r b1 b2 -> 
        A_bs_not_left_distributive (brel_sum brel_constant r) (c [+ann] b1) (c [+id] b2). 
Proof. intros [[s1 s3] nla]. 
       exists (inr s1, (inl c, inr s3)). compute. assumption. 
Defined. 


(*
Lemma bops_add_one_not_left_distributive  : 
     (bop_not_idempotent S r b1 + 
     bops_not_left_left_absorptive S r b1 b2 +
     bops_not_right_left_absorptive S r b1 b2 +
     bop_not_left_distributive S r b1 b2)-> 
        bop_not_left_distributive (with_constant S) (brel_sum brel_constant r) (c [+ann] b1) (c [+id] b2). 
Proof. intros [[[NID | NLLA] | NRLA] | NLD].
       apply bops_add_one_not_left_distributive_v2; auto.
       apply bops_add_one_not_left_distributive_v3; auto.               
       apply bops_add_one_not_left_distributive_v4; auto.        
       apply bops_add_one_not_left_distributive_v1; auto.        
Defined. 
*) 


Lemma A_bs_add_one_right_distributive  : 
     bop_idempotent S r b1 ->          
     A_bs_right_distributive r b1 b2 ->
     A_bs_right_absorptive r b1 b2 -> 
        A_bs_right_distributive (brel_sum brel_constant r) (c [+ann] b1) (c [+id] b2). 
Proof. intros idemS rd ra. 
       intros [c1 | s1] [c2 | s2] [c3 | s3]; compute; auto.
       + assert (A := ra s1 s2).
         assert (B := commS s1 (b2 s2 s1)).
         exact (trnS _ _ _ A B). 
Qed. 

Lemma A_bs_add_one_not_right_distributive_v1 : 
     A_bs_not_right_distributive r b1 b2 -> 
        A_bs_not_right_distributive (brel_sum brel_constant r) (c [+ann] b1) (c [+id] b2). 
Proof. intros [[s1 [s2 s3]] nld]. 
       exists (inr s1, (inr s2, inr s3)).  compute. assumption. 
Defined. 

Lemma A_bs_add_one_not_right_distributive_v2 : 
     bop_not_idempotent S r b1 -> 
        A_bs_not_right_distributive(brel_sum brel_constant r) (c [+ann] b1) (c [+id] b2). 
Proof. intros [s nidem]. 
       exists (inr s, (inl c, inl c)). compute. 
       apply (brel_symmetric_implies_dual _ _ symS). 
       assumption. 
Defined. 

Lemma A_bs_add_one_not_right_distributive_v3 : 
     A_bs_not_right_absorptive r b1 b2 -> 
        A_bs_not_right_distributive (brel_sum brel_constant r) (c [+ann] b1) (c [+id] b2). 
Proof. intros [[s1 s3] nla]. 
       exists (inr s1, (inl c, inr s3)). compute. assumption. 
Defined. 

(*
Lemma bops_add_one_not_right_distributive  : 
     (bop_not_idempotent S r b1 + 
     bops_not_left_right_absorptive S r b1 b2 +
     bops_not_right_right_absorptive S r b1 b2 +
     bop_not_right_distributive S r b1 b2)-> 
        bop_not_right_distributive (with_constant S) (brel_sum brel_constant r) (c [+ann] b1) (c [+id] b2). 
Proof. intros [[[NID | NLLA] | NRLA] | NLD].
       apply bops_add_one_not_right_distributive_v2; auto.
       apply bops_add_one_not_right_distributive_v3; auto.               
       apply bops_add_one_not_right_distributive_v4; auto.        
       apply bops_add_one_not_right_distributive_v1; auto.        
Defined. 
*) 

Lemma A_bs_add_one_left_absorptive  : 
     bop_idempotent S r b1 -> 
     A_bs_left_absorptive r b1 b2 -> 
        A_bs_left_absorptive (brel_sum brel_constant r) (c [+ann] b1) (c [+id] b2). 
Proof. intros idemS la [c1 | s1] [c2 | s2]; compute; auto. Qed. 

Lemma A_bs_add_one_not_left_absorptive_v1  : 
     bop_not_idempotent S r b1 -> 
        A_bs_not_left_absorptive (brel_sum brel_constant r) (c [+ann] b1) (c [+id] b2). 
Proof. intros [s nidemS]. 
       exists (inr s, inl c). compute. 
       apply (brel_symmetric_implies_dual _ _ symS). 
       assumption. 
Defined. 

Lemma A_bs_add_one_not_left_absorptive_v2  : 
     A_bs_not_left_absorptive r b1 b2 -> 
        A_bs_not_left_absorptive (brel_sum brel_constant r) (c [+ann] b1) (c [+id] b2). 
Proof. intros [ [s1 s2] nldS].
       exists (inr _ s1, inr _ s2).
       compute. assumption.
Defined.

(*
Lemma bops_add_one_not_left_left_absorptive  : 
     (bop_not_idempotent S r b1 + 
      bops_not_left_left_absorptive S r b1 b2) -> 
        bops_not_left_left_absorptive (with_constant S)  (brel_sum brel_constant r) (c [+ann] b1) (c [+id] b2). 
Proof. intros [NID | NLLA].
       apply bops_add_one_not_left_left_absorptive_v1; auto.
       apply bops_add_one_not_left_left_absorptive_v2; auto.   
Defined. 
*) 

Lemma A_bs_add_one_right_absorptive  : 
     bop_idempotent S r b1 -> 
     A_bs_right_absorptive r b1 b2 -> 
        A_bs_right_absorptive (brel_sum brel_constant r) (c [+ann] b1) (c [+id] b2). 
Proof. intros idemS la [c1 | s1] [c2 | s2]; compute; auto. Qed. 

Lemma A_bs_add_one_not_right_absorptive_v1  : 
     bop_not_idempotent S r b1 -> 
        A_bs_not_right_absorptive (brel_sum brel_constant r) (c [+ann] b1) (c [+id] b2). 
Proof. intros [s nidemS]. 
       exists (inr s, inl c). compute. 
       apply (brel_symmetric_implies_dual _ _ symS). 
       assumption. 
Defined. 

Lemma A_bs_add_one_not_right_absorptive_v2  : 
     A_bs_not_right_absorptive r b1 b2 -> 
        A_bs_not_right_absorptive (brel_sum brel_constant r) (c [+ann] b1) (c [+id] b2). 
Proof. intros [ [s1 s2] nldS]. exists (inr _ s1, inr _ s2). compute. assumption. Defined. 

(*
Lemma bops_add_one_not_right_absorptive  : 
     (bop_not_idempotent S r b1 + 
      bops_not_right_absorptive S r b1 b2) -> 
        bops_not_right_absorptive (with_constant S)  (brel_sum brel_constant r) (c [+ann] b1) (c [+id] b2). 
Proof. intros [NID | NLRA].
       apply bops_add_one_not_right_absorptive_v1; auto.
       apply bops_add_one_not_right_absorptive_v2; auto.   
Defined. 
*) 

(* strictly absorptive 
Lemma bops_add_one_not_left_strictly_absorptive :
  bops_not_left_strictly_absorptive (with_constant S)  
    (brel_sum brel_constant r) (c [+ann] b1) (c [+id] b2).
Proof.
  unfold bops_not_left_strictly_absorptive.
  exists (inl c, inl c); compute.
  right; reflexivity.
Defined.


Lemma bops_add_one_not_right_strictly_absorptive :
  bops_not_right_strictly_absorptive (with_constant S)  
    (brel_sum brel_constant r) (c [+ann] b1) (c [+id] b2).
Proof.
  unfold bops_not_right_strictly_absorptive.
  exists (inl c, inl c); compute.
  right; reflexivity.
Defined.
*)


(*
bops_left_left_absorptive  : s = s + st 
bops_right_left_absorptive : s = st + s 

note:  comm(+) * left_abs * idem(+) -> 
       (left_monotone <-> left_distributive)

Lemma bops_add_one_left_order_left_monotone  :
     bop_idempotent S r b1 ->
     bops_left_left_absorptive S r b1 b2 ->   
     bops_left_order_left_monotone S r b1 b2 -> 
        bops_left_order_left_monotone (with_constant S) (brel_sum brel_constant r) (c [+ann] b1) (c [+id] b2). 
Proof. intros idem lla lm [c1 | s1] [c2 | s2] [c3 | s3]; compute; intro A; auto.
       + discriminate A.
       + apply lm; auto. 
Qed. 

Lemma bops_add_one_not_left_order_left_monotone_v1  :
     bops_not_left_order_left_monotone S r b1 b2 -> 
      bops_not_left_order_left_monotone (with_constant S) (brel_sum brel_constant r) (c [+ann] b1) (c [+id] b2).
Proof. intros [[s1 [s2 s3]] nld]. 
       exists (inr s1, (inr s2, inr s3)).  compute. assumption. 
Defined.

Lemma bops_add_one_not_left_order_left_monotone_v2  :
     bop_not_idempotent S r b1 -> 
     bops_not_left_order_left_monotone (with_constant S) (brel_sum brel_constant r) (c [+ann] b1) (c [+id] b2).
Proof. intros [s nidem]. 
       exists (inr s, (inl c, inl c)). compute. split; auto. 
       apply (brel_symmetric_implies_dual _ _ symS). assumption. 
Defined. 

Lemma bops_add_one_not_left_order_left_monotone_v3  :
  bops_not_left_left_absorptive S r b1 b2 -> 
    bops_not_left_order_left_monotone (with_constant S) (brel_sum brel_constant r) (c [+ann] b1) (c [+id] b2).
Proof. intros [[s1 s3] nla]. 
       exists (inr s1, (inl c, inr s3)). compute. split; auto. 
Defined. 
*)

(* strictly left right 
Lemma bops_add_one_not_strictly_right_absorptive  : 
        bops_not_strictly_right_absorptive (with_constant S) (brel_sum brel_constant r) (c [+ann] b1) (c [+id] b2). 
Proof.  exists (inl c, inl c). compute. right; auto. Defined. 
*)

End Theory.

Section ACAS.

Section Decide.

Variable S : Type.
Variable r : brel S.
Variable c : cas_constant.
Variable b1 b2 : binary_op S.
Variable wS : S. 
Variable eqv : eqv_proofs S r. 
Variable commS : bop_commutative S r b1.

Definition A_bs_add_one_left_distributive_decide 
     (idem_d : bop_idempotent_decidable S r b1)
     (la_d   : A_bs_left_absorptive_decidable r b1 b2)
     (ld_d   : A_bs_left_distributive_decidable r b1 b2) : 
  A_bs_left_distributive_decidable
    (brel_sum brel_constant r)
    (bop_add_ann b1 c)
    (bop_add_id b2 c) := 
  let sym := A_eqv_symmetric S r eqv in
  let ref := A_eqv_reflexive S r eqv in
  let trn := A_eqv_transitive S r eqv in   
   match ld_d with 
   | inl ld  => 
       match la_d with 
       | inl la   => 
           match idem_d with 
           | inl idem   => inl (A_bs_add_one_left_distributive S r c b1 b2 ref sym trn commS idem ld la)
           | inr nidem  => inr (A_bs_add_one_not_left_distributive_v2 S r c b1 b2 sym nidem)
           end
       | inr nla => inr (A_bs_add_one_not_left_distributive_v3 S r c b1 b2 nla)
       end 
  | inr nld => inr (A_bs_add_one_not_left_distributive_v1 S r c b1 b2 nld)
end. 


Definition A_bs_add_one_right_distributive_decide 
     (idem_d : bop_idempotent_decidable S r b1)
     (la_d   : A_bs_right_absorptive_decidable r b1 b2)
     (ld_d   : A_bs_right_distributive_decidable r b1 b2) : 
  A_bs_right_distributive_decidable
    (brel_sum brel_constant r)
    (bop_add_ann b1 c)
    (bop_add_id b2 c) := 
  let sym := A_eqv_symmetric S r eqv in
  let ref := A_eqv_reflexive S r eqv in
  let trn := A_eqv_transitive S r eqv in   
   match ld_d with 
   | inl ld  => 
       match la_d with 
       | inl la   => 
           match idem_d with 
           | inl idem   => inl (A_bs_add_one_right_distributive S r c b1 b2 ref sym trn commS idem ld la)
           | inr nidem  => inr (A_bs_add_one_not_right_distributive_v2 S r c b1 b2 sym nidem)
           end
       | inr nla => inr (A_bs_add_one_not_right_distributive_v3 S r c b1 b2 nla)
       end 
  | inr nld => inr (A_bs_add_one_not_right_distributive_v1 S r c b1 b2 nld)
end. 

Definition A_bs_add_one_left_absorptive_decide  
     (idemS_d : bop_idempotent_decidable S r b1)
     (laS_d   : A_bs_left_absorptive_decidable r b1 b2) : 
  A_bs_left_absorptive_decidable 
    (brel_sum brel_constant r)
    (bop_add_ann b1 c)
    (bop_add_id b2 c) := 
  let sym := A_eqv_symmetric S r eqv in
  match laS_d with 
   | inl laS  => 
     match idemS_d with 
     | inl idemS => inl (A_bs_add_one_left_absorptive S r c b1 b2 sym idemS laS)
     | inr nidemS => inr (A_bs_add_one_not_left_absorptive_v1 S r c b1 b2 sym nidemS)
     end 
   | inr nlaS => inr (A_bs_add_one_not_left_absorptive_v2 S r c b1 b2 nlaS)
   end. 

Definition A_bs_add_one_right_absorptive_decide  
     (idemS_d : bop_idempotent_decidable S r b1)
     (laS_d   : A_bs_right_absorptive_decidable r b1 b2) : 
  A_bs_right_absorptive_decidable 
    (brel_sum brel_constant r)
    (bop_add_ann b1 c)
    (bop_add_id b2 c) := 
  let sym := A_eqv_symmetric S r eqv in
  match laS_d with 
   | inl laS  => 
     match idemS_d with 
     | inl idemS => inl (A_bs_add_one_right_absorptive S r c b1 b2 sym idemS laS)
     | inr nidemS => inr (A_bs_add_one_not_right_absorptive_v1 S r c b1 b2 sym nidemS)
     end 
   | inr nlaS => inr (A_bs_add_one_not_right_absorptive_v2 S r c b1 b2 nlaS)
   end. 


Definition A_bs_add_one_id_equals_ann_decide_left  
  (dS : A_bs_exists_id_ann_decidable r b1 b2) : 
  A_bs_exists_id_ann_decidable 
    (brel_sum brel_constant r)
    (bop_add_ann b1 c)
    (bop_add_id b2 c) := 
let ref := A_eqv_reflexive S r eqv in   
match dS with                                 
| A_Id_Ann_None _ _ _ (nid, nann)           =>
  A_Id_Ann_None _ _ _ (bop_add_ann_not_exists_id S r c b1 wS nid,
                             bop_add_id_not_exists_ann S r c b2 wS nann)
| A_Id_Ann_Id_None _ _ _ (id, nann)         =>
  A_Id_Ann_Id_None _ _ _ (bop_add_ann_exists_id S r c b1 id,
                                bop_add_id_not_exists_ann S r c b2 wS nann)
| A_Id_Ann_None_Ann _ _ _ (nid, ann)        =>
  A_Id_Ann_None_Ann _ _ _ (bop_add_ann_not_exists_id S r c b1 wS nid,
                                 bop_add_id_exists_ann S r c b2 ref ann)     
| A_Id_Ann_Equal _ _ _ id_ann_equal         =>
  A_Id_Ann_Equal _ _ _ (A_bs_add_one_exists_id_ann_equal_left S r c b1 b2 ref id_ann_equal)
| A_Id_Ann_Not_Equal _ _ _ id_ann_not_equal =>
  A_Id_Ann_Not_Equal _ _ _ (A_bs_add_one_exists_id_ann_not_equal_left S r c b1 b2 ref id_ann_not_equal)
end.

End Decide.       

Section Proofs.

Variables (S : Type)
          (rS : brel S)
          (c : cas_constant)
          (plusS timesS : binary_op S)
          (wS : S)
          (eqvS : eqv_proofs S rS). 

Definition A_bs_add_one_properties 
     (ppS : sg_C_proofs S rS plusS)
     (pS : A_bs_properties rS plusS timesS) : 
       A_bs_properties
         (brel_sum brel_constant rS)
         (bop_add_ann plusS c)
         (bop_add_id timesS c) :=
let idemS_d := A_sg_C_idempotent_d S rS plusS ppS in
let commS   := A_sg_C_commutative S rS plusS ppS in
let LD  := A_bs_left_distributive_d rS plusS timesS pS in 
let RD  := A_bs_right_distributive_d rS plusS timesS pS in 
let LLA := A_bs_left_absorptive_d rS plusS timesS pS in
let LRA := A_bs_right_absorptive_d rS plusS timesS pS in 
{|
  A_bs_left_distributive_d    := 
     A_bs_add_one_left_distributive_decide S rS c plusS timesS eqvS commS idemS_d LLA LD 
; A_bs_right_distributive_d   := 
     A_bs_add_one_right_distributive_decide S rS c plusS timesS eqvS commS idemS_d LRA RD 
; A_bs_left_absorptive_d      := 
     A_bs_add_one_left_absorptive_decide S rS c plusS timesS eqvS idemS_d LLA 
; A_bs_right_absorptive_d      := 
     A_bs_add_one_right_absorptive_decide S rS c plusS timesS eqvS idemS_d LRA 
|}.


Definition A_bs_add_one_id_ann_properties 
     (pS : A_bs_id_ann_properties rS plusS timesS) : 
        A_bs_id_ann_properties
          (brel_sum brel_constant rS)
          (bop_add_ann plusS c)
          (bop_add_id timesS c) := 
let ref := A_eqv_reflexive S rS eqvS in 
{|
  A_id_ann_plus_times_d := A_bs_add_one_id_equals_ann_decide_left  S rS c plusS timesS wS eqvS (A_id_ann_plus_times_d _ _ _ pS) 
; A_id_ann_times_plus_d := A_Id_Ann_Equal _ _ _ (A_bs_add_one_exists_id_ann_equal_right S rS c plusS timesS ref)
|}.


(* Note: This is another example (like llex) where we can combine semirings and obtain 
   something that is not a semiring, since distributivity depends on absorption. 

Definition dioid_proofs_add_one 
     (idem : bop_idempotent S rS plusS)
     (comm : bop_commutative S rS plusS)           
     (pS : dioid_proofs S rS plusS timesS) : 
        dioid_proofs
           (with_constant S) 
           (brel_sum brel_constant rS)
           (bop_add_ann plusS c)
           (bop_add_id timesS c) :=
let ref := A_eqv_reflexive S rS eqvS in
let sym := A_eqv_symmetric S rS eqvS in
let trn := A_eqv_transitive S rS eqvS in   
let LD  := A_dioid_left_distributive S rS plusS timesS pS in 
let RD  := A_dioid_right_distributive S rS plusS timesS pS in 
let LLA := A_dioid_left_absorptive S rS plusS timesS pS in
let LRA := A_dioid_right_absorptive S rS plusS timesS pS in
let RLA := bops_left_absorptive_implies_right_left S rS plusS timesS trn comm LLA in 
let RRA := bops_right_absorptive_implies_right_right S rS plusS timesS trn comm LRA in 
{|
  A_dioid_left_distributive      := bops_add_one_left_distributive S rS c plusS timesS ref sym idem LLA RLA LD 
; A_dioid_right_distributive     := bops_add_one_right_distributive S rS c plusS timesS ref sym idem LRA RRA RD 
; A_dioid_left_absorptive   := bops_add_one_left_absorptive S rS c plusS timesS sym idem LLA 
; A_dioid_right_absorptive  := bops_add_one_right_absorptive S rS c plusS timesS sym idem LRA 
|}.

*) 

End Proofs. 

Section Combinators. 

Definition A_bs_add_one {S : Type} (c : cas_constant) (bsS : @A_bs S) : @A_bs (with_constant S) := 
let eqvS  := A_bs_eqv bsS in
let peqvS := A_eqv_proofs S eqvS in
let s     := A_eqv_witness S eqvS in
let f     := A_eqv_new S eqvS in
let Pf    := A_eqv_not_trivial S eqvS in 
let rS    := A_eqv_eq S eqvS in   
let plus  := A_bs_plus bsS in
let times := A_bs_times bsS in
let pproofs := A_bs_plus_props bsS in
let tproofs := A_bs_times_props bsS in 
{| 
     A_bs_eqv          := A_eqv_add_constant S eqvS c 
   ; A_bs_plus         := bop_add_ann plus c
   ; A_bs_times        := bop_add_id times c
   ; A_bs_plus_props   := sg_C_proofs_add_ann S rS c plus s f Pf peqvS pproofs 
   ; A_bs_times_props  := sg_proofs_add_id S rS c times s f Pf peqvS tproofs
   ; A_bs_id_ann_props := A_bs_add_one_id_ann_properties  S rS c plus times s peqvS (A_bs_id_ann_props bsS)
   ; A_bs_props        := A_bs_add_one_properties S rS c plus times peqvS pproofs (A_bs_props bsS)
   ; A_bs_ast          := Ast_bs_add_one (c, A_bs_ast bsS)
|}.

(* the next two need CAS versions ... 
Definition A_bs_CI_add_one (S : Type) (bsS : A_bs_CI S) (c : cas_constant) : A_bs_CI (with_constant S) := 
let eqvS  := A_bs_CI_eqv S bsS in
let peqvS := A_eqv_proofs S eqvS in
let s     := A_eqv_witness S eqvS in
let f     := A_eqv_new S eqvS in
let Pf    := A_eqv_not_trivial S eqvS in 
let rS    := A_eqv_eq S eqvS in   
let plus  := A_bs_CI_plus S bsS in
let times := A_bs_CI_times S bsS in
let pproofs := A_bs_CI_plus_proofs S bsS in
let tproofs := A_bs_CI_times_proofs S bsS in 
{| 
     A_bs_CI_eqv           := A_eqv_add_constant S eqvS c 
   ; A_bs_CI_plus          := bop_add_ann plus c
   ; A_bs_CI_times         := bop_add_id times c
   ; A_bs_CI_plus_proofs   := sg_CI_proofs_add_ann S rS c plus s peqvS pproofs 
   ; A_bs_CI_times_proofs  := sg_proofs_add_id S rS c times s f Pf peqvS tproofs
   ; A_bs_CI_id_ann_proofs := id_ann_proofs_add_one  S rS c plus times s peqvS (A_bs_CI_id_ann_proofs S bsS)
   ; A_bs_CI_proofs        := bs_proofs_add_one S rS c plus times peqvS
                                                (A_sg_proofs_from_sg_CI_proofs S rS plus s f Pf peqvS pproofs)
                                                (A_bs_CI_proofs S bsS)
   ; A_bs_CI_ast           := Ast_bs_add_one (c, A_bs_CI_ast S bsS)
|}.

Definition A_bs_CS_add_one (S : Type) (bsS : A_bs_CS S) (c : cas_constant) : A_bs_CS (with_constant S) := 
let eqvS  := A_bs_CS_eqv S bsS in
let peqvS := A_eqv_proofs S eqvS in
let s     := A_eqv_witness S eqvS in
let f     := A_eqv_new S eqvS in
let Pf    := A_eqv_not_trivial S eqvS in 
let rS    := A_eqv_eq S eqvS in   
let plus  := A_bs_CS_plus S bsS in
let times := A_bs_CS_times S bsS in
let pproofs := A_bs_CS_plus_proofs S bsS in
let tproofs := A_bs_CS_times_proofs S bsS in 
{| 
     A_bs_CS_eqv           := A_eqv_add_constant S eqvS c 
   ; A_bs_CS_plus          := bop_add_ann plus c
   ; A_bs_CS_times         := bop_add_id times c
   ; A_bs_CS_plus_proofs   := sg_CS_proofs_add_ann S rS c plus s peqvS pproofs 
   ; A_bs_CS_times_proofs  := sg_proofs_add_id S rS c times s f Pf peqvS tproofs
   ; A_bs_CS_id_ann_proofs := id_ann_proofs_add_one  S rS c plus times s peqvS (A_bs_CS_id_ann_proofs S bsS)
   ; A_bs_CS_proofs        := bs_proofs_add_one S rS c plus times peqvS
                                                (A_sg_proofs_from_sg_CS_proofs S rS plus s f Pf peqvS pproofs)
                                                (A_bs_CS_proofs S bsS)
   ; A_bs_CS_ast           := Ast_bs_add_one (c, A_bs_CS_ast S bsS)
|}.


Definition A_add_one_to_pre_dioid : ∀ (S : Type),  A_pre_dioid S -> cas_constant -> A_pre_dioid_with_one (with_constant S) 
:= λ S bsS c,
let eqvS  := A_pre_dioid_eqv S bsS in
let peqvS := A_eqv_proofs S eqvS in
let s     := A_eqv_witness S eqvS in
let f     := A_eqv_new S eqvS in
let Pf    := A_eqv_not_trivial S eqvS in 
let rS    := A_eqv_eq S eqvS in   
let plus  := A_pre_dioid_plus S bsS in
let times := A_pre_dioid_times S bsS in
let pproofs := A_pre_dioid_plus_proofs S bsS in
let tproofs := A_pre_dioid_times_proofs S bsS in
let idem   := A_sg_CI_idempotent _ _ _ pproofs in
let comm   := A_sg_CI_commutative _ _ _ pproofs in 
{| 
     A_pre_dioid_with_one_eqv          := A_eqv_add_constant S eqvS c 
   ; A_pre_dioid_with_one_plus         := bop_add_ann plus c
   ; A_pre_dioid_with_one_times        := bop_add_id times c
   ; A_pre_dioid_with_one_plus_proofs  := sg_CI_proofs_add_ann S rS c plus s peqvS pproofs 
   ; A_pre_dioid_with_one_times_proofs := sg_proofs_add_id S rS c times s f Pf peqvS tproofs
   ; A_pre_dioid_with_one_id_ann_proofs := pann_is_tid_proofs_add_one S _ c plus times s peqvS (A_pre_dioid_id_ann_proofs S bsS)
   ; A_pre_dioid_with_one_proofs       := dioid_proofs_add_one S rS c plus times peqvS idem comm (A_pre_dioid_proofs S bsS)
   ; A_pre_dioid_with_one_ast          := Ast_bs_add_one (c, A_pre_dioid_ast S bsS) (*FIX*)
|}.

Definition A_add_one_to_pre_dioid_with_zero : ∀ (S : Type),  A_pre_dioid_with_zero S -> cas_constant -> A_dioid (with_constant S) 
:= λ S bsS c,
let eqvS  := A_pre_dioid_with_zero_eqv S bsS in
let peqvS := A_eqv_proofs S eqvS in
let s     := A_eqv_witness S eqvS in
let f     := A_eqv_new S eqvS in
let Pf    := A_eqv_not_trivial S eqvS in 
let rS    := A_eqv_eq S eqvS in   
let plus  := A_pre_dioid_with_zero_plus S bsS in
let times := A_pre_dioid_with_zero_times S bsS in
let pproofs := A_pre_dioid_with_zero_plus_proofs S bsS in
let tproofs := A_pre_dioid_with_zero_times_proofs S bsS in
let idem   := A_sg_CI_idempotent _ _ _ pproofs in
let comm   := A_sg_CI_commutative _ _ _ pproofs in 
{| 
     A_dioid_eqv          := A_eqv_add_constant S eqvS c 
   ; A_dioid_plus         := bop_add_ann plus c
   ; A_dioid_times        := bop_add_id times c
   ; A_dioid_plus_proofs  := sg_CI_proofs_add_ann S rS c plus s peqvS pproofs 
   ; A_dioid_times_proofs := sg_proofs_add_id S rS c times s f Pf peqvS tproofs
   ; A_dioid_id_ann_proofs := dually_bounded_proofs_add_one S _ c plus times  peqvS (A_pre_dioid_with_zero_id_ann_proofs S bsS)
   ; A_dioid_proofs       := dioid_proofs_add_one S rS c plus times peqvS idem comm (A_pre_dioid_with_zero_proofs S bsS)
   ; A_dioid_ast          := Ast_bs_add_one (c, A_pre_dioid_with_zero_ast S bsS) (*FIX*)
|}.

Definition A_add_one_to_selective_pre_dioid_with_zero : ∀ (S : Type),  A_selective_pre_dioid_with_zero S -> cas_constant -> A_selective_dioid (with_constant S) 
:= λ S bsS c,
let eqvS  := A_selective_pre_dioid_with_zero_eqv S bsS in
let peqvS := A_eqv_proofs S eqvS in
let s     := A_eqv_witness S eqvS in
let f     := A_eqv_new S eqvS in
let Pf    := A_eqv_not_trivial S eqvS in 
let rS    := A_eqv_eq S eqvS in   
let plus  := A_selective_pre_dioid_with_zero_plus S bsS in
let times := A_selective_pre_dioid_with_zero_times S bsS in
let pproofs := A_selective_pre_dioid_with_zero_plus_proofs S bsS in
let tproofs := A_selective_pre_dioid_with_zero_times_proofs S bsS in
let idem   := bop_selective_implies_idempotent _ _ _ (A_sg_CS_selective _ _ _ pproofs) in
let comm   := A_sg_CS_commutative _ _ _ pproofs in 
{| 
     A_selective_dioid_eqv          := A_eqv_add_constant S eqvS c 
   ; A_selective_dioid_plus         := bop_add_ann plus c
   ; A_selective_dioid_times        := bop_add_id times c
   ; A_selective_dioid_plus_proofs  := sg_CS_proofs_add_ann S rS c plus s peqvS pproofs 
   ; A_selective_dioid_times_proofs := sg_proofs_add_id S rS c times s f Pf peqvS tproofs
   ; A_selective_dioid_id_ann_proofs := dually_bounded_proofs_add_one S _ c plus times  peqvS (A_selective_pre_dioid_with_zero_id_ann_proofs S bsS)
   ; A_selective_dioid_proofs       := dioid_proofs_add_one S rS c plus times peqvS idem comm (A_selective_pre_dioid_with_zero_proofs S bsS)
   ; A_selective_dioid_ast          := Ast_bs_add_one (c, A_selective_pre_dioid_with_zero_ast S bsS) (*FIX*)
|}.

 *)

End Combinators. 
End ACAS.

Section AMCAS. 

  Definition A_bs_add_one_below_bs {S : Type} (c : cas_constant) (A : @A_below_bs S) : @A_below_bs (with_constant S) :=
            A_classify_bs (A_bs_add_one c (A_cast_up_bs A)). 

  Definition A_mcas_bs_add_one {S : Type} (c : cas_constant) (A : @A_bs_mcas S) : @A_bs_mcas (with_constant S) :=
    match A with
    | A_MCAS_bs B       => A_MCAS_bs (A_bs_add_one_below_bs c B)  
    | A_MCAS_bs_Error sl => A_MCAS_bs_Error sl
    end.

End AMCAS. 


Section CAS. 

  Section Certify.


Definition bs_add_one_left_distributive_decide
     {S : Type} 
     (c : cas_constant)                 
     (idem_d : @check_idempotent S)
     (la_d   : @bs_left_absorptive_decidable S)
     (ld_d   : @bs_left_distributive_decidable S) : 
          @bs_left_distributive_decidable (with_constant S) := 
   match ld_d with 
   | inl ld  => 
       match la_d with 
       | inl la   => 
           match idem_d with 
           | Certify_Idempotent => inl (BS_Left_Distributive (inl c))
           | Certify_Not_Idempotent s =>
               inr (BS_Not_Left_Distributive (inr s, (inl c, inl c)))
           end
       | inr (BS_Not_Left_Absorptive (s1, s2)) =>
           inr (BS_Not_Left_Distributive (inr s1, (inl c, inr s2)))
       end 
   | inr (BS_Not_Left_Distributive (s1, (s2, s3))) =>
       inr (BS_Not_Left_Distributive (inr s1, (inr s2, inr s3)))
end. 


Definition bs_add_one_right_distributive_decide
     {S : Type} 
     (c : cas_constant)                 
     (idem_d : @check_idempotent S)
     (la_d   : @bs_right_absorptive_decidable S)
     (ld_d   : @bs_right_distributive_decidable S) : 
          @bs_right_distributive_decidable (with_constant S) := 
   match ld_d with 
   | inl ld  => 
       match la_d with 
       | inl la   => 
           match idem_d with 
           | Certify_Idempotent => inl (BS_Right_Distributive (inl c))
           | Certify_Not_Idempotent s =>
               inr (BS_Not_Right_Distributive (inr s, (inl c, inl c)))
           end
       | inr (BS_Not_Right_Absorptive (s1, s2)) =>
           inr (BS_Not_Right_Distributive (inr s1, (inl c, inr s2)))
       end 
   | inr (BS_Not_Right_Distributive (s1, (s2, s3))) =>
       inr (BS_Not_Right_Distributive (inr s1, (inr s2, inr s3)))
end. 


Definition bs_add_one_left_absorptive_decide
     {S : Type} 
     (c : cas_constant)
     (idemS_d : @check_idempotent S)
     (laS_d   : @bs_left_absorptive_decidable S) : 
  @bs_left_absorptive_decidable (with_constant S) :=  
  match laS_d with 
   | inl laS  => 
     match idemS_d with 
     | Certify_Idempotent => inl (BS_Left_Absorptive (inl c))
     | Certify_Not_Idempotent s =>
         inr (BS_Not_Left_Absorptive (inr s, inl c))
     end
  | inr (BS_Not_Left_Absorptive (s1, s2)) =>
      inr (BS_Not_Left_Absorptive (inr s1, inr s2))
   end. 


Definition bs_add_one_right_absorptive_decide
     {S : Type} 
     (c : cas_constant)
     (idemS_d : @check_idempotent S)
     (laS_d   : @bs_right_absorptive_decidable S) : 
  @bs_right_absorptive_decidable (with_constant S) :=  
  match laS_d with 
   | inl laS  => 
     match idemS_d with 
     | Certify_Idempotent => inl (BS_Right_Absorptive (inl c))
     | Certify_Not_Idempotent s =>
         inr (BS_Not_Right_Absorptive (inr s, inl c))
     end
  | inr (BS_Not_Right_Absorptive (s1, s2)) =>
      inr (BS_Not_Right_Absorptive (inr s1, inr s2))
   end. 


Definition bs_add_one_id_equals_ann_decide_left  
  {S : Type} (c : cas_constant)
  (dS : @bs_exists_id_ann_decidable S) :
  @bs_exists_id_ann_decidable (with_constant S) :=
match dS with                                 
| Id_Ann_None                => Id_Ann_None
| Id_Ann_Id_None id          => Id_Ann_Id_None (inr id) 
| Id_Ann_None_Ann ann        => Id_Ann_None_Ann (inr ann) 
| Id_Ann_Equal id_ann        => Id_Ann_Equal (inr id_ann) 
| Id_Ann_Not_Equal (id, ann) => Id_Ann_Not_Equal (inr id, inr ann)
end.


End Certify.

Section Certificates.

Definition bs_add_one_properties
           {S : Type}
           (c : cas_constant)
           (ppS : @sg_C_certificates S)
           (pS : @bs_properties S) : @bs_properties (with_constant S) :=
let idm := sg_C_idempotent_d ppS in
let LD  := bs_left_distributive_d pS in
let RD  := bs_right_distributive_d pS in 
let LLA := bs_left_absorptive_d pS in 
let LRA := bs_right_absorptive_d pS in
{|
  bs_left_distributive_d      := bs_add_one_left_distributive_decide c idm LLA LD
; bs_right_distributive_d     := bs_add_one_right_distributive_decide c idm LRA RD 
; bs_left_absorptive_d        := bs_add_one_left_absorptive_decide c idm LLA 
; bs_right_absorptive_d       := bs_add_one_right_absorptive_decide c idm LRA 
|}.

Definition bs_add_one_id_ann_properties 
           {S : Type}
           (c : cas_constant)
           (pS : @bs_id_ann_properties S) :
  @bs_id_ann_properties (with_constant S) := 
{|
  id_ann_plus_times_d := bs_add_one_id_equals_ann_decide_left c (id_ann_plus_times_d pS) 
; id_ann_times_plus_d := Id_Ann_Equal (inl c) 
|}.

End Certificates.   

Section Combinators.


Definition bs_add_one {S : Type} (c : cas_constant) (bsS : @bs S) : @bs (with_constant S) :=
let eqvS   := bs_eqv bsS in
let wS     := eqv_witness eqvS in
let f      := eqv_new eqvS in
let plus   := bs_plus bsS in
let times  := bs_times bsS in
let plusP  := bs_plus_props bsS in
let timesP := bs_times_props bsS in 
{| 
     bs_eqv         := eqv_add_constant eqvS c 
   ; bs_plus        := bop_add_ann plus c
   ; bs_times       := bop_add_id times c
   ; bs_plus_props  := sg_C_certs_add_ann c wS f plusP
   ; bs_times_props := sg_certs_add_id c wS f timesP
   ; bs_id_ann_props := bs_add_one_id_ann_properties c (bs_id_ann_props bsS)
   ; bs_props       := bs_add_one_properties c plusP (bs_props bsS)
   ; bs_ast         := Ast_bs_add_one (c, bs_ast bsS)
|}.

End Combinators.

End CAS.

Section MCAS.

  Definition bs_add_one_below_bs {S : Type} (c : cas_constant) (A : @below_bs S) : @below_bs (with_constant S) :=
            classify_bs (bs_add_one c (cast_up_bs A)). 

  Definition mcas_bs_add_one {S : Type} (c : cas_constant) (A : @bs_mcas S) : @bs_mcas (with_constant S) :=
    match A with
    | MCAS_bs B       => MCAS_bs (bs_add_one_below_bs c B)  
    | MCAS_bs_Error sl => MCAS_bs_Error sl
    end.


End MCAS. 



Section Verify.

Section Certify.

Variables (S : Type)
          (c : cas_constant)
          (wS : S)
          (rS : brel S)
          (eqvS : eqv_proofs S rS)                 
          (plusS timesS : binary_op S)
          (commS : bop_commutative S rS plusS).
  
Lemma correct_bs_add_one_id_equals_ann_decide 
  (P : A_bs_exists_id_ann_decidable rS plusS timesS) : 
  p2c_exists_id_ann (with_constant S)
                    (brel_sum brel_constant rS) 
                    (bop_add_ann plusS c) (bop_add_id timesS c)
                    (A_bs_add_one_id_equals_ann_decide_left S rS c plusS timesS wS eqvS P) 
  = 
  bs_add_one_id_equals_ann_decide_left c (p2c_exists_id_ann S rS plusS timesS P). 
Proof. unfold p2c_exists_id_ann, A_bs_add_one_id_equals_ann_decide_left,
       bs_add_one_id_equals_ann_decide_left; 
       destruct P; simpl. 
         + destruct p as [A B]; reflexivity. 
         + destruct p as [[id A] B]; simpl; reflexivity. 
         + destruct p as [A [ann B]]; simpl; reflexivity. 
         + destruct a as [id_ann [A B]]; simpl; reflexivity. 
         + destruct a as [[id ann] [[A B] C]]; simpl; reflexivity. 
Qed.

Lemma correct_bs_add_one_left_distributive_decide
  (idmS_d : bop_idempotent_decidable S rS plusS) 
  (llaS_d : A_bs_left_absorptive_decidable rS plusS timesS) 
  (ldS_d : A_bs_left_distributive_decidable rS plusS timesS): 
  p2c_bs_left_distributive_decidable
     (brel_sum brel_constant rS) (inl c)
     (bop_add_ann plusS c)
     (bop_add_id timesS c)
     (A_bs_add_one_left_distributive_decide S rS c plusS timesS eqvS commS idmS_d llaS_d ldS_d)
  = 
  bs_add_one_left_distributive_decide c 
     (p2c_idempotent_check S rS plusS idmS_d) 
     (p2c_bs_left_absorptive_decidable rS wS plusS timesS llaS_d)
     (p2c_bs_left_distributive_decidable rS wS plusS timesS ldS_d). 
Proof. destruct idmS_d as [ idmS | [ s0 nidmS ] ]; 
       destruct llaS_d as [ llaS | [ [s1 s2] nllaS ] ]; 
       destruct ldS_d as [ ldS | [ [s3 [s4 s5]] nldS ] ]; 
       compute; reflexivity. 
Qed. 

Lemma correct_bs_add_one_right_distributive_decide
  (idmS_d : bop_idempotent_decidable S rS plusS) 
  (llaS_d : A_bs_right_absorptive_decidable rS plusS timesS) 
  (ldS_d : A_bs_right_distributive_decidable rS plusS timesS): 
  p2c_bs_right_distributive_decidable
     (brel_sum brel_constant rS)                                  
     (inl c) (bop_add_ann plusS c)
     (bop_add_id timesS c)
     (A_bs_add_one_right_distributive_decide S rS c plusS timesS eqvS commS idmS_d llaS_d ldS_d)
  = 
  bs_add_one_right_distributive_decide c 
     (p2c_idempotent_check S rS plusS idmS_d) 
     (p2c_bs_right_absorptive_decidable rS wS plusS timesS llaS_d)
     (p2c_bs_right_distributive_decidable rS wS plusS timesS ldS_d). 
Proof. destruct idmS_d as [ idmS | [ s0 nidmS ] ]; 
       destruct llaS_d as [ llaS | [ [s1 s2] nllaS ] ]; 
       destruct ldS_d as [ ldS | [ [s3 [s4 s5]] nldS ] ]; 
       compute; reflexivity. 
Qed. 

Lemma correct_bs_add_one_left_absorbtive_decide 
  (idmS_d : bop_idempotent_decidable S rS plusS) 
  (laS_d : A_bs_left_absorptive_decidable rS plusS timesS): 
  p2c_bs_left_absorptive_decidable
     (brel_sum brel_constant rS)                                  
     (inl c) (bop_add_ann plusS c)
     (bop_add_id timesS c)
     (A_bs_add_one_left_absorptive_decide S rS c plusS timesS eqvS idmS_d laS_d)
  = 
  bs_add_one_left_absorptive_decide c 
     (p2c_idempotent_check S rS plusS idmS_d) 
     (p2c_bs_left_absorptive_decidable rS wS plusS timesS laS_d).
Proof. destruct idmS_d as [ idmS | [ s0 nidmS ] ] ;
       destruct laS_d as [ laS | [ [s1 s2] nlaS ] ]; 
       compute; reflexivity. 
Qed. 


Lemma correct_bs_add_one_right_absorbtive_decide 
  (idmS_d : bop_idempotent_decidable S rS plusS) 
  (laS_d : A_bs_right_absorptive_decidable rS plusS timesS): 
  p2c_bs_right_absorptive_decidable
     (brel_sum brel_constant rS)                                  
     (inl c) (bop_add_ann plusS c)
     (bop_add_id timesS c)
     (A_bs_add_one_right_absorptive_decide S rS c plusS timesS eqvS idmS_d laS_d)
  = 
  bs_add_one_right_absorptive_decide c 
     (p2c_idempotent_check S rS plusS idmS_d) 
     (p2c_bs_right_absorptive_decidable rS wS plusS timesS laS_d).
Proof. destruct idmS_d as [ idmS | [ s0 nidmS ] ] ;
       destruct laS_d as [ laS | [ [s1 s2] nlaS ] ]; 
       compute; reflexivity. 
Qed. 

End Certify.

Section Certificates. 

Variables (S : Type)
          (c : cas_constant)
          (wS : S)
          (rS : brel S)
          (eqvS : eqv_proofs S rS)            
          (plusS timesS : binary_op S)
          (plusP : sg_C_proofs S rS plusS).

Lemma  correct_bs_add_one_properties (bsS : A_bs_properties rS plusS timesS): 
    P2C_bs
       (brel_sum brel_constant rS) 
       (inl c) (bop_add_ann plusS c)
       (bop_add_id timesS c) 
       (A_bs_add_one_properties _ rS c plusS timesS eqvS plusP bsS)
    =
    bs_add_one_properties c (P2C_sg_C rS plusS plusP) (P2C_bs rS wS plusS timesS bsS). 
Proof. unfold bs_add_one_properties, A_bs_add_one_properties, P2C_bs; simpl. 
       rewrite (correct_bs_add_one_left_distributive_decide _ c wS).
       rewrite (correct_bs_add_one_right_distributive_decide _ c wS).
       rewrite (correct_bs_add_one_left_absorbtive_decide _ c wS).
       rewrite (correct_bs_add_one_right_absorbtive_decide _ c wS).
       reflexivity. 
Defined.


Lemma correct_bs_add_one_id_ann_properties (P : A_bs_id_ann_properties rS plusS timesS) : 
  P2C_id_ann _
             (brel_sum brel_constant rS)
             (bop_add_ann plusS c)
             (bop_add_id timesS c)
             (A_bs_add_one_id_ann_properties S rS c plusS timesS wS eqvS P)
  = 
  bs_add_one_id_ann_properties c (P2C_id_ann _ rS plusS timesS P). 
Proof. unfold P2C_id_ann, A_bs_add_one_id_ann_properties, bs_add_one_id_ann_properties; simpl. 
       rewrite correct_bs_add_one_id_equals_ann_decide. 
       reflexivity.
Qed.        



End Certificates.

Section Combinators.

Theorem correct_bs_add_one (S : Type) (c : cas_constant) (bsS: @A_bs S) : 
   bs_add_one c (A2C_bs bsS) 
   =
   A2C_bs (A_bs_add_one c bsS). 
Proof. unfold bs_add_one, A_bs_add_one, A2C_bs; simpl. 
       rewrite correct_eqv_add_constant.
       rewrite <- correct_sg_certs_add_id. 
       rewrite <- correct_sg_C_certs_add_ann. 
       rewrite (correct_bs_add_one_properties _ c (A_eqv_witness S (A_bs_eqv bsS))). 
       rewrite correct_bs_add_one_id_ann_properties.
       reflexivity. 
Qed. 

Theorem correct_bs_add_one_below_bs  (S : Type) (c : cas_constant)  (A : @A_below_bs S) : 
  bs_add_one_below_bs c (A2C_below_bs A)
  =
 A2C_below_bs (A_bs_add_one_below_bs c A).
Proof. unfold bs_add_one_below_bs, A_bs_add_one_below_bs.
       rewrite cast_up_bs_A2C_commute. 
       rewrite correct_bs_add_one. 
       rewrite correct_classify_bs. 
       reflexivity.
Qed.


Theorem correct_mcas_bs_add_one (S : Type) (c : cas_constant) (A : @A_bs_mcas S) : 
         mcas_bs_add_one c (A2C_bs_mcas A) 
         = 
         A2C_bs_mcas (A_mcas_bs_add_one c A).
Proof. unfold mcas_bs_add_one, A_mcas_bs_add_one.
       destruct A; simpl; try reflexivity.
       rewrite correct_bs_add_one_below_bs.
       reflexivity. 
Qed. 


End Combinators.   
End Verify.   

