
Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.

Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.eqv.sum.
Require Import CAS.coq.eqv.add_constant.

Require Import CAS.coq.sg.add_id.
Require Import CAS.coq.sg.add_ann. 
Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures.

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

Notation "a [+ann] b" := (bop_add_ann b a)       (at level 15).
Notation "a [+id] b"  := (bop_add_id b a)       (at level 15).

Lemma A_bs_add_zero_exists_id_ann_equal_left :    
  A_bs_exists_id_ann_equal (brel_sum brel_constant r) (c [+id] b1) (c [+ann] b2). 
Proof. exists (inl _ c). split. 
       apply bop_add_id_is_id; auto. 
       apply bop_add_ann_is_ann; auto. 
Defined. 

Lemma A_bs_add_zero_exists_id_ann_equal_right :    
  A_bs_exists_id_ann_equal r b2 b1 ->
  A_bs_exists_id_ann_equal (brel_sum brel_constant r) (c [+ann] b2) (c [+id] b1). 
Proof. intros [i [Pi Pa]]. exists (inr _ i). 
       assert (fact1 : bop_is_id (with_constant S) (brel_sum brel_constant r) (c [+ann] b2) (inr i)) . 
          unfold bop_is_id. intros [c1 | s1]; compute; auto. 
       assert (fact2 : bop_is_ann (with_constant S) (brel_sum brel_constant r) (c [+id] b1) (inr i)). 
          unfold bop_is_id. intros [c1 | s1]; compute; auto. 
       split; assumption. 
Defined.


Lemma A_bs_add_zero_exists_id_ann_not_equal_right :
  A_bs_exists_id_ann_not_equal r b2 b1 ->
  A_bs_exists_id_ann_not_equal (brel_sum brel_constant r) (c [+ann] b2) (c [+id] b1).
Proof. intros [[id ann] [[A B] C]]. 
       exists (inr id, inr ann). split. split.
       intros [c' | s]; compute; auto.
       intros [c' | s]; compute; auto.          
       compute; auto. 
Defined.    


Lemma A_bs_add_zero_left_distributive  :
     A_bs_left_distributive r b1 b2 ->   
        A_bs_left_distributive (brel_sum brel_constant r) (c [+id] b1) (c [+ann] b2).
Proof. intros ld [c1 | s1] [c2 | s2] [c3 | s3]; compute; auto. Qed. 

Lemma A_bs_add_zero_not_left_distributive  : 
     A_bs_not_left_distributive r b1 b2 -> 
        A_bs_not_left_distributive (brel_sum brel_constant r) (c [+id] b1) (c [+ann] b2).
Proof. intros [ [s1 [s2 s3]] nldS]. 
       exists (inr _ s1, (inr _ s2, inr _ s3)). compute. assumption. Defined. 


Lemma A_bs_add_zero_right_distributive  : 
     A_bs_right_distributive r b1 b2 -> 
        A_bs_right_distributive (brel_sum brel_constant r) (c [+id] b1) (c [+ann] b2).
Proof. intros ld [c1 | s1] [c2 | s2] [c3 | s3]; compute; auto. Qed. 

Lemma A_bs_add_zero_not_right_distributive  : 
     A_bs_not_right_distributive r b1 b2 -> 
        A_bs_not_right_distributive (brel_sum brel_constant r) (c [+id] b1) (c [+ann] b2).
Proof. intros [ [s1 [s2 s3]] nldS]. exists (inr _ s1, (inr _ s2, inr _ s3)). compute. assumption. Defined. 
       
(*
Lemma A_bs_add_zero_left_distributive_dual (times plus : binary_op S) :
     bop_idempotent S r times ->
     A_bs_left_left_absorptive S r times plus ->     
     A_bs_right_left_absorptive S r times plus ->        
     bop_left_distributive S r times plus ->   
        bop_left_distributive (with_constant S) (brel_sum brel_constant r) (c [+ann] times) (c [+id] plus). 
Proof. intros idem lla rla ld [c1 | s1] [c2 | s2] [c3 | s3]; compute; auto. Qed. 


Lemma A_bs_add_zero_not_left_distributive_dual_v1 (times plus : binary_op S) : 
     bop_not_left_distributive S r times plus -> 
        bop_not_left_distributive (with_constant S) (brel_sum brel_constant r) (c [+ann] times) (c [+id] plus). 
Proof. intros [ [s1 [s2 s3]] nldS]. 
       exists (inr _ s1, (inr _ s2, inr _ s3)). compute. assumption. Defined. 

Lemma A_bs_add_zero_not_left_distributive_dual_v2 (times plus : binary_op S) : 
     bop_not_idempotent S r times -> 
        bop_not_left_distributive (with_constant S) (brel_sum brel_constant r) (c [+ann] times) (c [+id] plus). 
Proof. intros [ s nidem]. 
       exists (inr _ s, (inl _ c, inl _ c)). compute.
       case_eq(r s (times s s)); intro H; auto.
       apply symS in H. rewrite H in nidem. 
       discriminate nidem. 
Defined. 

Lemma A_bs_add_zero_not_left_distributive_dual_v3 (times plus : binary_op S) : 
        A_bs_not_left_left_absorptive S r times plus ->     
        bop_not_left_distributive (with_constant S) (brel_sum brel_constant r) (c [+ann] times) (c [+id] plus). 
Proof. intros [ [s1 s3] nlla]. 
       exists (inr _ s1, (inl _ c, inr _ s3)). compute. assumption. Defined. 


Lemma A_bs_add_zero_not_left_distributive_dual_v4 (times plus : binary_op S) : 
        A_bs_not_right_left_absorptive S r times plus ->     
        bop_not_left_distributive (with_constant S) (brel_sum brel_constant r) (c [+ann] times) (c [+id] plus). 
Proof. intros [ [s1 s2] nlla]. 
       exists (inr _ s1, (inr _ s2, inl _ c)). compute. assumption. Defined. 
*) 

Lemma A_bs_add_zero_left_absorptive  : 
     A_bs_left_absorptive r b1 b2 -> 
        A_bs_left_absorptive (brel_sum brel_constant r) (c [+id] b1) (c [+ann] b2). 
Proof. intros la [c1 | s1] [c2 | s2]; compute; auto. Qed. 

Lemma A_bs_add_zero_not_left_absorptive : 
     A_bs_not_left_absorptive r b1 b2 -> 
        A_bs_not_left_absorptive (brel_sum brel_constant r) (c [+id] b1) (c [+ann] b2).
Proof. intros [ [s1 s2] nldS]. exists (inr _ s1, inr _ s2). compute. assumption. Defined.

Lemma A_bs_add_zero_right_absorptive  : 
     A_bs_right_absorptive r b1 b2 -> 
        A_bs_right_absorptive (brel_sum brel_constant r) (c [+id] b1) (c [+ann] b2).
Proof. intros la [c1 | s1] [c2 | s2]; compute; auto. Qed. 

Lemma A_bs_add_zero_not_right_absorptive : 
     A_bs_not_right_absorptive r b1 b2 -> 
        A_bs_not_right_absorptive (brel_sum brel_constant r) (c [+id] b1) (c [+ann] b2).
Proof. intros [ [s1 s2] nldS]. exists (inr _ s1, inr _ s2). compute. assumption. Defined. 


(*
Lemma A_bs_add_zero_left_absorptive_dual  (times plus : binary_op S) :
  bop_idempotent S r times -> 
  A_bs_left_absorptive S r times plus -> 
    A_bs_left_absorptive (with_constant S) (brel_sum brel_constant r)
      (bop_add_ann times c) (bop_add_id plus c). 
Proof. intros idem la [c1 | s1] [c2 | s2]; compute; auto. Qed. 


Lemma A_bs_add_zero_not_left_strictly_absorptive :
  A_bs_not_left_strictly_absorptive 
    (with_constant S) 
    (brel_sum brel_constant r) 
    (c [+id] b1) 
    (c [+ann] b2).
Proof. exists (inl c, inl c); compute; right; auto. Defined. 

Lemma A_bs_add_zero_not_right_strictly_absorptive :
  A_bs_not_right_strictly_absorptive 
    (with_constant S) 
    (brel_sum brel_constant r) 
    (c [+id] b1) 
    (c [+ann] b2).
Proof. exists (inl c, inl c); compute; right; auto. Defined.


Lemma A_bs_add_zero_left_order_left_monotone
      (lolm : A_bs_left_order_left_monotone S r b1 b2): 
        A_bs_left_order_left_monotone (with_constant S) (brel_sum brel_constant r) (c [+id] b1) (c [+ann] b2). 
Proof. intros [c1 | s1] [c2 | s2] [c3 | s3]; compute; intro A; auto.
       apply lolm; auto. 
Qed.

Lemma A_bs_zero_one_not_left_order_left_monotone  :
     A_bs_not_left_order_left_monotone S r b1 b2 -> 
      A_bs_not_left_order_left_monotone (with_constant S) (brel_sum brel_constant r) (c [+id] b1) (c [+id] b2).
Proof. intros [[s1 [s2 s3]] nld]. 
       exists (inr s1, (inr s2, inr s3)).  compute. assumption. 
Defined.
*) 

End Theory.



Section ACAS.

Section Decide.

Variable S   : Type.
Variable r   : brel S.
Variable wS  : S.
Variable c   : cas_constant.
Variable b1 b2 : binary_op S.
Variable eqv : eqv_proofs S r. 

Definition A_bs_add_zero_left_distributive_decide 
  (dS : A_bs_left_distributive_decidable r b1 b2) :
  A_bs_left_distributive_decidable (brel_sum brel_constant r)
                                  (bop_add_id b1 c)
                                  (bop_add_ann b2 c) := 
let ref := A_eqv_reflexive _ _ eqv in 
   match dS with 
   | inl ldS  => inl (A_bs_add_zero_left_distributive S r c b1 b2 ref ldS)
   | inr nldS => inr (A_bs_add_zero_not_left_distributive S r c b1 b2 nldS)
   end.

Definition A_bs_add_zero_right_distributive_decide 
  (dS : A_bs_right_distributive_decidable r b1 b2) : 
  A_bs_right_distributive_decidable (brel_sum brel_constant r)
                                  (bop_add_id b1 c)
                                  (bop_add_ann b2 c) := 
let ref := A_eqv_reflexive _ _ eqv in 
   match dS with 
   | inl ldS  => inl _ (A_bs_add_zero_right_distributive S r c b1 b2 ref ldS)
   | inr nldS => inr _ (A_bs_add_zero_not_right_distributive S r c b1 b2 nldS)
   end. 

(*
Definition A_bs_add_zero_left_distributive_decide_dual
  (idem_d : bop_idempotent_decidable S r b1)
  (lla_d : A_bs_left_absorptive_decidable S r b1 b2)
  (rla_d : A_bs_right_left_absorptive_decidable S r b1 b2)
  (ld_d : bop_left_distributive_decidable S r b1 b2) :
  bop_left_distributive_decidable (with_constant S)
                                  (brel_sum brel_constant r)
                                  (bop_add_ann b1 c)
                                  (bop_add_id b2 c) :=
let ref := A_eqv_reflexive _ _ eqv in
let sym := A_eqv_symmetric _ _ eqv in                                      
   match ld_d with 
   | inl ld  =>
     match idem_d with
     | inl  idem => match lla_d with
                    | inl lla  => match rla_d with
                                  | inl rla  => inl (A_bs_add_zero_left_distributive_dual S r c ref sym b1 b2 idem lla rla ld)
                                  | inr nrla => inr (A_bs_add_zero_not_left_distributive_dual_v4 S r c b1 b2 nrla)
                                  end 
                    | inr nlla => inr (A_bs_add_zero_not_left_distributive_dual_v3 S r c b1 b2 nlla) 
                    end 
     | inr nidem => inr (A_bs_add_zero_not_left_distributive_dual_v2 S r c sym b1 b2 nidem) 
     end 
   | inr nld => inr (A_bs_add_zero_not_left_distributive_dual_v1 S r c b1 b2 nld)
   end.

*) 

Definition A_bs_add_zero_left_absorptive_decide 
     (dS : A_bs_left_absorptive_decidable r b1 b2) : 
        A_bs_left_absorptive_decidable 
          (brel_sum brel_constant r)
          (bop_add_id b1 c)
          (bop_add_ann b2 c) := 
let ref := A_eqv_reflexive _ _ eqv in 
   match dS with 
   | inl ldS  => inl _ (A_bs_add_zero_left_absorptive S r c b1 b2 ref ldS)
   | inr nldS => inr _ (A_bs_add_zero_not_left_absorptive S r c b1 b2 nldS)
   end. 

Definition A_bs_add_zero_right_absorptive_decide 
     (dS : A_bs_right_absorptive_decidable  r b1 b2): 
        A_bs_right_absorptive_decidable 
          (brel_sum brel_constant r)
          (bop_add_id b1 c)
          (bop_add_ann b2 c) := 
let ref := A_eqv_reflexive _ _ eqv in 
   match dS with 
   | inl ldS  => inl _ (A_bs_add_zero_right_absorptive S r c b1 b2 ref ldS)
   | inr nldS => inr _ (A_bs_add_zero_not_right_absorptive S r c b1 b2 nldS)
   end. 


Definition A_bs_add_zero_id_equals_ann_decide_right  
  (dS : A_bs_exists_id_ann_decidable r b2 b1) : 
  A_bs_exists_id_ann_decidable 
    (brel_sum brel_constant r)
    (bop_add_ann b2 c)
    (bop_add_id b1 c) := 
let ref := A_eqv_reflexive S r eqv in   
match dS with                                 
| A_Id_Ann_None _ _ _ (nid, nann)           =>
  A_Id_Ann_None _ _ _ (bop_add_ann_not_exists_id S r c b2 wS nid,
                             bop_add_id_not_exists_ann S r c b1 wS nann)
| A_Id_Ann_Id_None _ _ _ (id, nann)         =>
  A_Id_Ann_Id_None _ _ _ (bop_add_ann_exists_id S r c b2 id,
                                bop_add_id_not_exists_ann S r c b1 wS nann)
| A_Id_Ann_None_Ann _ _ _ (nid, ann)        =>
  A_Id_Ann_None_Ann _ _ _ (bop_add_ann_not_exists_id S r c b2 wS nid,
                                 bop_add_id_exists_ann S r c b1 ref ann)     
| A_Id_Ann_Equal _ _ _ id_ann_equal         =>
  A_Id_Ann_Equal _ _ _ (A_bs_add_zero_exists_id_ann_equal_right S r c b1 b2 ref id_ann_equal)
| A_Id_Ann_Not_Equal _ _ _ id_ann_not_equal =>
  A_Id_Ann_Not_Equal _ _ _ (A_bs_add_zero_exists_id_ann_not_equal_right S r c b1 b2 ref id_ann_not_equal)
end.

End Decide.

Section Proofs. 
  
Variables (S : Type)
          (rS : brel S)
          (c : cas_constant)
          (plusS timesS : binary_op S)
          (wS : S)
          (eqvS : eqv_proofs S rS). 

Definition A_bs_add_zero_id_ann_properties 
     (pS : A_bs_id_ann_properties rS plusS timesS) : 
        A_bs_id_ann_properties 
           (brel_sum brel_constant rS)
           (bop_add_id plusS c)           
           (bop_add_ann timesS c) := 
let ref := A_eqv_reflexive S rS eqvS in 
{|
  A_id_ann_plus_times_d := A_Id_Ann_Equal _ _ _ (A_bs_add_zero_exists_id_ann_equal_left S rS c plusS timesS ref)
; A_id_ann_times_plus_d := A_bs_add_zero_id_equals_ann_decide_right  S rS wS c plusS timesS eqvS (A_id_ann_times_plus_d _ _ _ pS) 
|}.

Definition A_bs_add_zero_properties
     (pS : A_bs_properties rS plusS timesS) : 
        A_bs_properties
           (brel_sum brel_constant rS)
           (bop_add_id plusS c)
           (bop_add_ann timesS c) := 
let LD  := A_bs_left_distributive_d rS plusS timesS pS in 
let RD  := A_bs_right_distributive_d rS plusS timesS pS in 
let LLA := A_bs_left_absorptive_d rS plusS timesS pS in
let LRA := A_bs_right_absorptive_d rS plusS timesS pS in
{|
  A_bs_left_distributive_d    := 
     A_bs_add_zero_left_distributive_decide S rS c plusS timesS eqvS LD
; A_bs_right_distributive_d   := 
     A_bs_add_zero_right_distributive_decide S rS c plusS timesS eqvS RD
; A_bs_left_absorptive_d      := 
     A_bs_add_zero_left_absorptive_decide S rS c plusS timesS eqvS LLA 
; A_bs_right_absorptive_d      := 
     A_bs_add_zero_right_absorptive_decide S rS c plusS timesS eqvS LRA 
|}.

(* unlike add_one, add_zero can preserve semiring proofs 
Definition semiring_proofs_add_zero
     (pS : semiring_proofs S rS plusS timesS) : 
        semiring_proofs
           (with_constant S) 
           (brel_sum brel_constant rS)
           (bop_add_id plusS c)
           (bop_add_ann timesS c) :=
let ref := A_eqv_reflexive S rS eqvS in
let LD  := A_semiring_left_distributive S rS plusS timesS pS in 
let RD  := A_semiring_right_distributive S rS plusS timesS pS in 
let LLA := A_semiring_left_absorptive_d S rS plusS timesS pS in
let LRA := A_semiring_right_absorptive_d S rS plusS timesS pS in
{|
  A_semiring_left_distributive       := A_bs_add_zero_left_distributive S rS c plusS timesS ref LD 
; A_semiring_right_distributive      := A_bs_add_zero_right_distributive S rS c plusS timesS ref RD 
; A_semiring_left_absorptive_d  := A_bs_add_zero_left_absorptive_decide S rS c plusS timesS eqvS LLA 
; A_semiring_right_absorptive_d := A_bs_add_zero_right_absorptive_decide S rS c plusS timesS eqvS LRA 
|}.


Definition dioid_proofs_add_zero
     (pS : dioid_proofs S rS plusS timesS) : 
        dioid_proofs
           (with_constant S) 
           (brel_sum brel_constant rS)
           (bop_add_id plusS c)
           (bop_add_ann timesS c) :=
let ref := A_eqv_reflexive S rS eqvS in
let LD  := A_dioid_left_distributive S rS plusS timesS pS in 
let RD  := A_dioid_right_distributive S rS plusS timesS pS in 
let LLA := A_dioid_left_absorptive S rS plusS timesS pS in
let LRA := A_dioid_right_absorptive S rS plusS timesS pS in
{|
  A_dioid_left_distributive      := A_bs_add_zero_left_distributive S rS c plusS timesS ref LD 
; A_dioid_right_distributive     := A_bs_add_zero_right_distributive S rS c plusS timesS ref RD 
; A_dioid_left_absorptive   := A_bs_add_zero_left_absorptive S rS c plusS timesS ref LLA 
; A_dioid_right_absorptive  := A_bs_add_zero_right_absorptive S rS c plusS timesS ref LRA 
|}.


Definition lattice_proofs_add_zero
       (idem : bop_idempotent S rS timesS)
       (comm : bop_commutative S rS timesS)            
       (lS : lattice_proofs S rS plusS timesS) :
       lattice_proofs
           (with_constant S) 
           (brel_sum brel_constant rS)
           (bop_add_id plusS c)
           (bop_add_ann timesS c) := 
let ref := A_eqv_reflexive S rS eqvS in
let sym := A_eqv_symmetric S rS eqvS in
let trn := A_eqv_transitive S rS eqvS in  
let LD  := A_lattice_distributive_d S rS plusS timesS lS in
let LD_dual  := A_lattice_distributive_dual_d S rS plusS timesS lS in 
let LLA := A_lattice_absorptive S rS plusS timesS lS in
let LLA_dual := A_lattice_absorptive_dual S rS plusS timesS lS in
let RLA_dual := A_bs_left_absorptive_implies_right_left S rS timesS plusS trn comm LLA_dual in 
{|
  A_lattice_absorptive           := A_bs_add_zero_left_absorptive S rS c plusS timesS ref LLA
; A_lattice_absorptive_dual      := A_bs_add_zero_left_absorptive_dual S rS c sym timesS plusS idem LLA_dual
; A_lattice_distributive_d       := A_bs_add_zero_left_distributive_decide S rS c plusS timesS eqvS LD
; A_lattice_distributive_dual_d  := A_bs_add_zero_left_distributive_decide_dual S rS c timesS plusS eqvS
                                    (inl idem) (inl LLA_dual) (inl RLA_dual) LD_dual 
|}.


Definition distributive_lattice_proofs_add_zero
       (idem : bop_idempotent S rS timesS)
       (lS : distributive_lattice_proofs S rS plusS timesS) :
       distributive_lattice_proofs
           (with_constant S) 
           (brel_sum brel_constant rS)
           (bop_add_id plusS c)
           (bop_add_ann timesS c) := 
let ref := A_eqv_reflexive S rS eqvS in
let sym := A_eqv_symmetric S rS eqvS in
let LD  := A_distributive_lattice_distributive S rS plusS timesS lS in
let LLA := A_distributive_lattice_absorptive S rS plusS timesS lS in
let LLA_dual := A_distributive_lattice_absorptive_dual S rS plusS timesS lS in
{|
  A_distributive_lattice_absorptive        := A_bs_add_zero_left_absorptive S rS c plusS timesS ref LLA
; A_distributive_lattice_absorptive_dual   := A_bs_add_zero_left_absorptive_dual S rS c sym timesS plusS idem LLA_dual
; A_distributive_lattice_distributive      := A_bs_add_zero_left_distributive S rS c plusS timesS ref LD
|}. 
*) 
End Proofs.

Section Combinators.

Definition A_bs_add_zero {S : Type} (c : cas_constant) (bsS : @A_bs S) : @A_bs (with_constant S) := 
let eqv    := A_bs_eqv bsS in
let eq     := A_eqv_eq S eqv in
let eqvP   := A_eqv_proofs S eqv in 
let wS     := A_eqv_witness S eqv in
let f      := A_eqv_new S eqv in
let nt     := A_eqv_not_trivial S eqv in 
let plus   := A_bs_plus bsS in 
let times  := A_bs_times bsS in
let plusP  := A_bs_plus_props bsS in
let timesP := A_bs_times_props bsS in 
{| 
     A_bs_eqv          := A_eqv_add_constant S eqv c 
   ; A_bs_plus         := bop_add_id plus c
   ; A_bs_times        := bop_add_ann times c
   ; A_bs_plus_props   := sg_C_proofs_add_id S eq c plus wS f nt eqvP plusP
   ; A_bs_times_props  := sg_proofs_add_ann S eq c times wS f nt eqvP timesP
   ; A_bs_id_ann_props := A_bs_add_zero_id_ann_properties S eq c plus times wS eqvP (A_bs_id_ann_props bsS)
   ; A_bs_props        := A_bs_add_zero_properties S eq c plus times eqvP (A_bs_props bsS)
   ; A_bs_ast          := Ast_bs_add_zero (c, A_bs_ast bsS)
|}. 


(* NEED CAS versions of then next two combinators .... 
Definition A_bs_CI_add_zero (S : Type) (bsS : A_bs_CI S) (c : cas_constant) : A_bs_CI (with_constant S) := 
let eqv    := A_bs_CI_eqv S bsS in
let eq     := A_eqv_eq S eqv in
let eqvP   := A_eqv_props S eqv in 
let wS     := A_eqv_witness S eqv in
let f      := A_eqv_new S eqv in
let nt     := A_eqv_not_trivial S eqv in 
let plus   := A_bs_CI_plus S bsS in 
let times  := A_bs_CI_times S bsS in
let plusP  := A_bs_CI_plus_props S bsS in
let timesP := A_bs_CI_times_props S bsS in 
{| 
     A_bs_CI_eqv          := A_eqv_add_constant S eqv c 
   ; A_bs_CI_plus         := bop_add_id plus c
   ; A_bs_CI_times        := bop_add_ann times c
   ; A_bs_CI_plus_props  := sg_CI_props_add_id S eq c plus wS eqvP plusP
   ; A_bs_CI_times_props := sg_props_add_ann S eq c times wS f nt eqvP timesP
   ; A_bs_CI_id_ann_props := id_ann_props_add_zero S eq c plus times wS eqvP (A_bs_CI_id_ann_props S bsS)
   ; A_bs_CI_props       := bs_props_add_zero S eq c plus times eqvP (A_bs_CI_props S bsS)
   ; A_bs_CI_ast          := Ast_bs_add_zero (c, A_bs_CI_ast S bsS)
|}. 


Definition A_bs_CS_add_zero (S : Type) (bsS : A_bs_CS S) (c : cas_constant) : A_bs_CS (with_constant S) := 
let eqv    := A_bs_CS_eqv S bsS in
let eq     := A_eqv_eq S eqv in
let eqvP   := A_eqv_props S eqv in 
let wS     := A_eqv_witness S eqv in
let f      := A_eqv_new S eqv in
let nt     := A_eqv_not_trivial S eqv in 
let plus   := A_bs_CS_plus S bsS in 
let times  := A_bs_CS_times S bsS in
let plusP  := A_bs_CS_plus_props S bsS in
let timesP := A_bs_CS_times_props S bsS in 
{| 
     A_bs_CS_eqv          := A_eqv_add_constant S eqv c 
   ; A_bs_CS_plus         := bop_add_id plus c
   ; A_bs_CS_times        := bop_add_ann times c
   ; A_bs_CS_plus_props  := sg_CS_props_add_id S eq c plus wS eqvP plusP
   ; A_bs_CS_times_props := sg_props_add_ann S eq c times wS f nt eqvP timesP
   ; A_bs_CS_id_ann_props := id_ann_props_add_zero S eq c plus times wS eqvP (A_bs_CS_id_ann_props S bsS)
   ; A_bs_CS_props       := bs_props_add_zero S eq c plus times eqvP (A_bs_CS_props S bsS)
   ; A_bs_CS_ast          := Ast_bs_add_zero (c, A_bs_CS_ast S bsS)
|}. 

Definition A_add_zero_to_pre_dioid : ∀ (S : Type),  A_pre_dioid S -> cas_constant -> A_pre_dioid_with_zero (with_constant S) 
:= λ S bsS c,
let eqvS  := A_pre_dioid_eqv S bsS in
let peqvS := A_eqv_props S eqvS in
let s     := A_eqv_witness S eqvS in
let f     := A_eqv_new S eqvS in
let Pf    := A_eqv_not_trivial S eqvS in 
let rS    := A_eqv_eq S eqvS in   
let plus  := A_pre_dioid_plus S bsS in
let times := A_pre_dioid_times S bsS in
let pprops := A_pre_dioid_plus_props S bsS in
let tprops := A_pre_dioid_times_props S bsS in
{| 
     A_pre_dioid_with_zero_eqv          := A_eqv_add_constant S eqvS c 
   ; A_pre_dioid_with_zero_plus         := bop_add_id plus c
   ; A_pre_dioid_with_zero_times        := bop_add_ann times c
   ; A_pre_dioid_with_zero_plus_props  := sg_CI_props_add_id S rS c plus s peqvS pprops 
   ; A_pre_dioid_with_zero_times_props  := sg_props_add_ann S rS c times s f Pf peqvS tprops
   ; A_pre_dioid_with_zero_id_ann_props := pann_is_tid_props_add_zero S _ c plus times s peqvS (A_pre_dioid_id_ann_props S bsS)
   ; A_pre_dioid_with_zero_props        := dioid_props_add_zero S rS c plus times peqvS (A_pre_dioid_props S bsS)
   ; A_pre_dioid_with_zero_ast           := Ast_bs_add_one (c, A_pre_dioid_ast S bsS) (*FIX*)
|}.

Definition A_add_zero_to_pre_dioid_with_one : ∀ (S : Type),  A_pre_dioid_with_one S -> cas_constant -> A_dioid (with_constant S) 
:= λ S bsS c,
let eqvS  := A_pre_dioid_with_one_eqv S bsS in
let peqvS := A_eqv_props S eqvS in
let s     := A_eqv_witness S eqvS in
let f     := A_eqv_new S eqvS in
let Pf    := A_eqv_not_trivial S eqvS in 
let rS    := A_eqv_eq S eqvS in   
let plus  := A_pre_dioid_with_one_plus S bsS in
let times := A_pre_dioid_with_one_times S bsS in
let pprops := A_pre_dioid_with_one_plus_props S bsS in
let tprops := A_pre_dioid_with_one_times_props S bsS in
{| 
     A_dioid_eqv          := A_eqv_add_constant S eqvS c 
   ; A_dioid_plus         := bop_add_id plus c
   ; A_dioid_times        := bop_add_ann times c
   ; A_dioid_plus_props  := sg_CI_props_add_id S rS c plus s peqvS pprops 
   ; A_dioid_times_props := sg_props_add_ann S rS c times s f Pf peqvS tprops
   ; A_dioid_id_ann_props := dually_bounded_props_add_zero S _ c plus times  peqvS (A_pre_dioid_with_one_id_ann_props S bsS)
   ; A_dioid_props       := dioid_props_add_zero S rS c plus times peqvS (A_pre_dioid_with_one_props S bsS)
   ; A_dioid_ast          := Ast_bs_add_one (c, A_pre_dioid_with_one_ast S bsS) (*FIX*)
|}.


Definition A_add_zero_to_selective_pre_dioid_with_one : ∀ (S : Type),  A_selective_pre_dioid_with_one S -> cas_constant -> A_selective_dioid (with_constant S) 
:= λ S bsS c,
let eqvS  := A_selective_pre_dioid_with_one_eqv S bsS in
let peqvS := A_eqv_props S eqvS in
let s     := A_eqv_witness S eqvS in
let f     := A_eqv_new S eqvS in
let Pf    := A_eqv_not_trivial S eqvS in 
let rS    := A_eqv_eq S eqvS in   
let plus  := A_selective_pre_dioid_with_one_plus S bsS in
let times := A_selective_pre_dioid_with_one_times S bsS in
let pprops := A_selective_pre_dioid_with_one_plus_props S bsS in
let tprops := A_selective_pre_dioid_with_one_times_props S bsS in
{| 
     A_selective_dioid_eqv          := A_eqv_add_constant S eqvS c 
   ; A_selective_dioid_plus         := bop_add_id plus c
   ; A_selective_dioid_times        := bop_add_ann times c
   ; A_selective_dioid_plus_props  := sg_CS_props_add_id S rS c plus s peqvS pprops 
   ; A_selective_dioid_times_props := sg_props_add_ann S rS c times s f Pf peqvS tprops
   ; A_selective_dioid_id_ann_props := dually_bounded_props_add_zero S _ c plus times  peqvS (A_selective_pre_dioid_with_one_id_ann_props S bsS)
   ; A_selective_dioid_props       := dioid_props_add_zero S rS c plus times peqvS (A_selective_pre_dioid_with_one_props S bsS)
   ; A_selective_dioid_ast          := Ast_bs_add_one (c, A_selective_pre_dioid_with_one_ast S bsS) (*FIX*)
|}.
*) 
End Combinators.   
End ACAS.

Section AMCAS.

  Definition A_bs_add_zero_below_bs {S : Type} (c : cas_constant) (A : @A_below_bs S) : @A_below_bs (with_constant S) :=
            A_classify_bs (A_bs_add_zero c (A_cast_up_bs A)). 

  Definition A_mcas_bs_add_zero {S : Type} (c : cas_constant) (A : @A_bs_mcas S) : @A_bs_mcas (with_constant S) :=
    match A with
    | A_MCAS_bs B       => A_MCAS_bs (A_bs_add_zero_below_bs c B)  
    | A_MCAS_bs_Error sl => A_MCAS_bs_Error sl
    end.

End AMCAS. 


Section CAS.

Section Certify.
    
Definition bs_add_zero_left_distributive_decide
     {S : Type} (c : cas_constant)
     (dS : @bs_left_distributive_decidable S) : 
     @bs_left_distributive_decidable (with_constant S) := 
match dS with 
   | inl _ => inl (BS_Left_Distributive (inl c))
   | inr (BS_Not_Left_Distributive (s1, (s2, s3)))
           => inr (BS_Not_Left_Distributive (inr s1, (inr s2, inr s3)))
end. 


Definition bs_add_zero_right_distributive_decide
     {S : Type} (c : cas_constant)
     (dS : @bs_right_distributive_decidable S) : 
     @bs_right_distributive_decidable (with_constant S) := 
match dS with 
   | inl _ => inl (BS_Right_Distributive (inl c))
   | inr (BS_Not_Right_Distributive (s1, (s2, s3)))
           => inr (BS_Not_Right_Distributive (inr s1, (inr s2, inr s3)))
end. 

Definition bs_add_zero_left_absorptive_decide
     {S : Type} (c : cas_constant)
     (dS : @bs_left_absorptive_decidable S) : 
     @bs_left_absorptive_decidable (with_constant S) := 
match dS with 
   | inl _ => inl (BS_Left_Absorptive (inl c))
   | inr (BS_Not_Left_Absorptive (s1, s2))
           => inr (BS_Not_Left_Absorptive (inr s1, inr s2))
end. 

Definition bs_add_zero_right_absorptive_decide
     {S : Type} (c : cas_constant)
     (dS : @bs_right_absorptive_decidable S) : 
     @bs_right_absorptive_decidable (with_constant S) := 
match dS with 
   | inl _ => inl (BS_Right_Absorptive (inl c))
   | inr (BS_Not_Right_Absorptive (s1, s2))
           => inr (BS_Not_Right_Absorptive (inr s1, inr s2))
end. 

Definition bs_add_zero_id_equals_ann_decide_right  
  {S : Type} (c : cas_constant) (dS : @bs_exists_id_ann_decidable S) :
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



Definition bs_add_zero_id_ann_properties 
           {S : Type}
           (c : cas_constant)
           (pS : @bs_id_ann_properties S) : @bs_id_ann_properties (with_constant S) := 
{|
  id_ann_plus_times_d := Id_Ann_Equal (inl c) 
; id_ann_times_plus_d := bs_add_zero_id_equals_ann_decide_right c (id_ann_times_plus_d pS) 
|}.


Definition bs_add_zero_properties
  {S : Type} (c : cas_constant) (pS : @bs_properties S) : @bs_properties (with_constant S) := 
{|
  bs_left_distributive_d    := 
     bs_add_zero_left_distributive_decide c (bs_left_distributive_d pS) 
; bs_right_distributive_d   := 
     bs_add_zero_right_distributive_decide c (bs_right_distributive_d pS) 
; bs_left_absorptive_d      := 
     bs_add_zero_left_absorptive_decide c (bs_left_absorptive_d pS)
; bs_right_absorptive_d      := 
     bs_add_zero_right_absorptive_decide c (bs_right_absorptive_d pS)
|}. 

(*
Definition semiring_certs_add_zero
      {S : Type}
      (c : cas_constant)
      (pS : @semiring_certificates S) : @semiring_certificates (with_constant S)  := 
{|
  semiring_left_distributive       := Assert_Left_Distributive
; semiring_right_distributive      := Assert_Right_Distributive
; semiring_left_absorptive_d  :=
     A_bs_add_zero_left_absorptive_check (semiring_left_absorptive_d pS)    
; semiring_right_absorptive_d :=
    A_bs_add_zero_right_absorptive_check (semiring_right_absorptive_d pS)
|}.


Definition dioid_certs_add_zero
      {S : Type}
      (c : cas_constant)
      (pS : @dioid_certificates S) : @dioid_certificates (with_constant S)  := 
{|
  dioid_left_distributive      := Assert_Left_Distributive
; dioid_right_distributive     := Assert_Right_Distributive
; dioid_left_absorptive   := Assert_Left_Left_Absorptive
; dioid_right_absorptive  := Assert_Left_Right_Absorptive
|}.

*) 
End Certificates.   

Section Combinators.


Definition bs_add_zero {S : Type} (c : cas_constant) (bsS : @bs S) : @bs (with_constant S) := 
let s :=   eqv_witness (bs_eqv bsS) in
let f :=   eqv_new (bs_eqv bsS) in   
{| 
     bs_eqv         := eqv_add_constant (bs_eqv bsS) c 
   ; bs_plus        := bop_add_id (bs_plus bsS) c
   ; bs_times       := bop_add_ann (bs_times bsS) c
   ; bs_plus_props  := sg_C_certs_add_id c s f (bs_plus_props bsS) 
   ; bs_times_props := sg_certs_add_ann c s f (bs_times_props bsS)
   ; bs_id_ann_props := bs_add_zero_id_ann_properties c (bs_id_ann_props bsS)
   ; bs_props       := bs_add_zero_properties c (bs_props bsS)
   ; bs_ast         := Ast_bs_add_zero (c, bs_ast bsS)
|}. 


(*
Definition semiring_props_add_zero : 
  ∀ {S : Type} (s : S), @semiring_propificates S  -> @semiring_propificates (with_constant S) 
:= λ S s pS, 
{|
  semiring_left_distributive        := Assert_Left_Distributive 
; semiring_right_distributive       := Assert_Right_Distributive 
; semiring_plus_id_is_times_ann_d   := Certify_Plus_Id_Equals_Times_Ann  
; semiring_times_id_is_plus_ann_d   :=
  match semiring_times_id_is_plus_ann_d pS with (*** NB : type coer ***) 
  | Certify_Times_Id_Equals_Plus_Ann => Certify_Times_Id_Equals_Plus_Ann  
  | Certify_Not_Times_Id_Equals_Plus_Ann => Certify_Not_Times_Id_Equals_Plus_Ann  
  end 
; semiring_left_absorptive_d   := A_bs_add_zero_left_absorptive_check s (semiring_left_absorptive_d pS)
; semiring_right_absorptive_d  := A_bs_add_zero_right_absorptive_check s (semiring_right_absorptive_d pS)
|}.

Definition dioid_add_zero : ∀ (S : Type),  @dioid S -> cas_constant -> @dioid (with_constant S) 
:= λ S bsS c,
let s :=   eqv_witness (dioid_eqv bsS) in
let f :=   eqv_new (dioid_eqv bsS) in   
{| 
     dioid_eqv         := eqv_add_constant (dioid_eqv bsS) c 
   ; dioid_plus        := bop_add_id (dioid_plus bsS) c
   ; dioid_times       := bop_add_ann (dioid_times bsS) c
   ; dioid_plus_props  := sg_CI_props_add_id c (dioid_plus_props bsS)
   ; dioid_times_props := mm_props_add_ann c s f (dioid_times_props bsS)
   ; dioid_props       := semiring_props_add_zero s (dioid_props bsS)
   ; dioid_plus_ast    := Ast_bop_add_id (c, dioid_plus_ast bsS)
   ; dioid_times_ast   := Ast_bop_add_ann (c, dioid_times_ast bsS)
   ; dioid_ast         := Ast_dioid_add_zero (c, dioid_ast bsS)
|}. 

Definition semiring_add_zero : ∀ (S : Type),  @semiring S -> cas_constant -> @semiring (with_constant S) 
:= λ S bsS c,
let s :=   eqv_witness (semiring_eqv bsS) in
let f :=   eqv_new (semiring_eqv bsS) in   
{| 
     semiring_eqv         := eqv_add_constant (semiring_eqv bsS) c 
   ; semiring_plus        := bop_add_id (semiring_plus bsS) c
   ; semiring_times       := bop_add_ann (semiring_times bsS) c
   ; semiring_plus_props  := sg_C_props_add_id c s f (semiring_plus_props bsS)
   ; semiring_times_props := mm_props_add_ann c s f (semiring_times_props bsS)
   ; semiring_props       := semiring_props_add_zero s (semiring_props bsS)
   ; semiring_plus_ast    := Ast_bop_add_id (c, semiring_plus_ast bsS)
   ; semiring_times_ast   := Ast_bop_add_ann (c, semiring_times_ast bsS)                                                      
   ; semiring_ast         := Ast_semiring_add_zero (c, semiring_ast bsS)
|}. 
 *)
End Combinators.   
End CAS.


Section MCAS. 

  Definition bs_add_zero_below_bs {S : Type} (c : cas_constant) (A : @below_bs S) : @below_bs (with_constant S) :=
            classify_bs (bs_add_zero c (cast_up_bs A)). 

  Definition mcas_bs_add_zero {S : Type} (c : cas_constant) (A : @bs_mcas S) : @bs_mcas (with_constant S) :=
    match A with
    | MCAS_bs B       => MCAS_bs (bs_add_zero_below_bs c B)  
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
          (plusS timesS : binary_op S).

Lemma correct_bs_add_zero_id_equals_ann_decide 
  (P : A_bs_exists_id_ann_decidable rS timesS plusS) : 
  p2c_exists_id_ann _ 
                    (brel_sum brel_constant rS)
                    (bop_add_ann timesS c)                                        
                    (bop_add_id plusS c)                    
                    (A_bs_add_zero_id_equals_ann_decide_right S rS wS c plusS timesS eqvS P) 
  = 
  bs_add_zero_id_equals_ann_decide_right c (p2c_exists_id_ann _ rS timesS plusS P). 
Proof. unfold p2c_exists_id_ann, A_bs_add_zero_id_equals_ann_decide_right,
       bs_add_zero_id_equals_ann_decide_right; 
       destruct P; simpl. 
         + destruct p as [A B]; reflexivity. 
         + destruct p as [[id A] B]; simpl; reflexivity. 
         + destruct p as [A [ann B]]; simpl; reflexivity. 
         + destruct a as [id_ann [A B]]; simpl; reflexivity. 
         + destruct a as [[id ann] [[A B] C]]; simpl; reflexivity. 
Qed.
  

Lemma correct_bs_add_zero_left_distributive_decide 
  (pS : A_bs_left_distributive_decidable rS plusS timesS): 
  p2c_bs_left_distributive_decidable 
     (brel_sum brel_constant rS) 
     (inl c)
     (bop_add_id plusS c)
     (bop_add_ann timesS c)
     (A_bs_add_zero_left_distributive_decide S rS c plusS timesS eqvS pS)
  = 
  bs_add_zero_left_distributive_decide c (p2c_bs_left_distributive_decidable rS wS plusS timesS pS). 
Proof. destruct pS as [ ldS | [ [s1 [s2 s3]] nldS ] ]; compute; reflexivity. Qed. 

Lemma  correct_bs_add_zero_right_distributive_decide
    (pS : A_bs_right_distributive_decidable rS plusS timesS) : 
  p2c_bs_right_distributive_decidable
    (brel_sum brel_constant rS)
    (inl c) 
     (bop_add_id plusS c)
     (bop_add_ann timesS c)
     (A_bs_add_zero_right_distributive_decide S rS c plusS timesS eqvS pS)
  = 
  bs_add_zero_right_distributive_decide c (p2c_bs_right_distributive_decidable rS wS plusS timesS pS). 
Proof. destruct pS as [ ldS | [ [s1 [s2 s3]] nldS ] ]; compute; reflexivity. Qed. 

Lemma correct_bs_add_zero_left_absorbtive_decide 
  (pS : A_bs_left_absorptive_decidable rS plusS timesS) : 
  p2c_bs_left_absorptive_decidable
     (brel_sum brel_constant rS)                                  
     (inl c) (bop_add_id plusS c)
     (bop_add_ann timesS c)
     (A_bs_add_zero_left_absorptive_decide S rS c plusS timesS eqvS pS)
  = 
  bs_add_zero_left_absorptive_decide c
     (p2c_bs_left_absorptive_decidable rS wS plusS timesS pS). 
Proof. destruct pS as [ ldS | [ [s1 s2] nldS ] ]; compute; reflexivity. Qed. 

Lemma correct_bs_add_zero_right_absorbtive_decide 
  (pS : A_bs_right_absorptive_decidable rS plusS timesS) : 
  p2c_bs_right_absorptive_decidable
    (brel_sum brel_constant rS)
    (inl c) 
     (bop_add_id plusS c)
     (bop_add_ann timesS c)
     (A_bs_add_zero_right_absorptive_decide S rS c plusS timesS eqvS pS)
  = 
  bs_add_zero_right_absorptive_decide c (p2c_bs_right_absorptive_decidable rS wS plusS timesS pS).
Proof. destruct pS as [ ldS | [ [s1 s2] nldS ] ]; compute; reflexivity. Qed. 


Lemma  correct_bs_add_zero_properties (bsS : A_bs_properties rS plusS timesS): 
    P2C_bs 
       (brel_sum brel_constant rS) 
       (inl c) (bop_add_id plusS c) 
       (bop_add_ann timesS c) 
       (A_bs_add_zero_properties _ rS c plusS timesS eqvS bsS)
    =
    bs_add_zero_properties c (P2C_bs rS wS plusS timesS bsS). 
Proof. unfold bs_add_zero_properties, A_bs_add_zero_properties, P2C_bs; simpl. 
       rewrite correct_bs_add_zero_left_distributive_decide.
       rewrite correct_bs_add_zero_right_distributive_decide.
       rewrite correct_bs_add_zero_left_absorbtive_decide.
       rewrite correct_bs_add_zero_right_absorbtive_decide.
       reflexivity. 
Defined.


Lemma correct_bs_add_zero_id_ann_properties (P : A_bs_id_ann_properties rS plusS timesS) : 
  P2C_id_ann _
             (brel_sum brel_constant rS)
             (bop_add_id plusS c)
             (bop_add_ann timesS c)
             (A_bs_add_zero_id_ann_properties S rS c plusS timesS wS eqvS P)
  = 
  bs_add_zero_id_ann_properties c (P2C_id_ann _ rS plusS timesS P). 
Proof. unfold P2C_id_ann, A_bs_add_zero_id_ann_properties, bs_add_zero_id_ann_properties; simpl. 
       rewrite correct_bs_add_zero_id_equals_ann_decide. 
       reflexivity.
Qed.        

End Certify.

Section Combinators. 

Theorem correct_bs_add_zero (S : Type) (c : cas_constant) (bsS: @A_bs S) : 
   bs_add_zero c (A2C_bs bsS) 
   =
   A2C_bs (A_bs_add_zero c bsS). 
Proof. unfold bs_add_zero, A_bs_add_zero, A2C_bs; simpl. 
       rewrite correct_eqv_add_constant. 
       rewrite <- correct_sg_certs_add_ann. 
       rewrite <- correct_sg_C_certs_add_id.
       rewrite correct_bs_add_zero_id_ann_properties.
       rewrite (correct_bs_add_zero_properties _ c (A_eqv_witness S (A_bs_eqv bsS))).
       reflexivity. 
Qed.


Theorem correct_bs_add_zero_below_bs  (S : Type) (c : cas_constant)  (A : @A_below_bs S) : 
  bs_add_zero_below_bs c (A2C_below_bs A)
  =
 A2C_below_bs (A_bs_add_zero_below_bs c A).
Proof. unfold bs_add_zero_below_bs, A_bs_add_zero_below_bs.
       rewrite cast_up_bs_A2C_commute. 
       rewrite correct_bs_add_zero. 
       rewrite correct_classify_bs. 
       reflexivity.
Qed.


Theorem correct_mcas_bs_add_zero (S : Type) (c : cas_constant) (A : @A_bs_mcas S) : 
         mcas_bs_add_zero c (A2C_bs_mcas A) 
         = 
         A2C_bs_mcas (A_mcas_bs_add_zero c A).
Proof. unfold mcas_bs_add_zero, A_mcas_bs_add_zero.
       destruct A; simpl; try reflexivity.
       rewrite correct_bs_add_zero_below_bs.
       reflexivity. 
Qed. 


End Combinators. 

End Verify.   




(*
Lemma  correct_id_ann_props_add_zero : 
  ∀ (S : Type) (c : cas_constant) (rS : brel S) (s : S) 
    (plusS timesS : binary_op S) 
    (eqvS : eqv_props S rS)
    (bsS : id_ann_props S rS plusS timesS), 
    P2C_id_ann (with_constant S) 
       (brel_sum brel_constant rS) 
       (bop_add_id plusS c) 
       (bop_add_ann timesS c) 
       (id_ann_props_add_zero S rS c plusS timesS s eqvS bsS)
    =
    id_ann_props_add_zero c (P2C_id_ann S rS plusS timesS bsS). 
Proof. intros S c rS s plusS timesS eqvS bsS.
       unfold id_ann_props_add_zero, id_ann_props_add_zero, P2C_id_ann; simpl.        
       rewrite A_bs_add_zero_times_id_equals_plus_ann_check_correct.
       rewrite bop_add_id_exists_ann_check_correct.
       rewrite bop_add_ann_exists_id_check_correct.        
       reflexivity.
Qed.        

*) 
(*
Lemma  correct_semiring_props_add_zero : 
  ∀ (S : Type) (c : cas_constant) (rS : brel S) (s : S) 
    (plusS timesS : binary_op S) 
    (eqvS : eqv_props S rS)
    (bsS : semiring_props S rS plusS timesS), 
    P2C_semiring (with_constant S) 
       (brel_sum brel_constant rS) 
       (bop_add_id plusS c) 
       (bop_add_ann timesS c) 
       (semiring_props_add_zero S rS c plusS timesS s eqvS bsS)
    =
    semiring_props_add_zero s (P2C_semiring S rS plusS timesS bsS). 
Proof. intros S c rS s plusS timesS eqvS bsS. 
       unfold semiring_props_add_zero, semiring_props_add_zero, P2C_semiring, P2C_sg; simpl. 
       rewrite A_bs_add_zero_times_id_equals_plus_ann_check_correct.
       rewrite (A_bs_add_zero_left_absorbtive_check_correct S c rS s plusS timesS eqvS). 
       rewrite (A_bs_add_zero_right_absorbtive_check_correct S c rS s plusS timesS eqvS). 
       reflexivity. 
Defined. 


Theorem correct_semiring_add_zero: ∀ (S : Type) (pS: A_semiring S) (c : cas_constant), 
   semiring_add_zero S (A2C_semiring S pS) c 
   =
   A2C_semiring (with_constant S) (A_semiring_add_zero S pS c). 
Proof. intros S pS c. 
       unfold semiring_add_zero, A_semiring_add_zero, A2C_semiring; simpl. 
       rewrite correct_eqv_add_constant. 
       rewrite <- correct_mm_props_add_ann. 
       rewrite <- correct_sg_C_props_add_id. 
       rewrite correct_semiring_props_add_zero. 
       reflexivity. 
Qed. 


Theorem correct_dioid_add_zero: ∀ (S : Type) (pS: A_dioid S) (c : cas_constant), 
   dioid_add_zero S (A2C_dioid S pS) c 
   =
   A2C_dioid (with_constant S) (A_dioid_add_zero S pS c). 
Proof. intros S pS c. 
       unfold dioid_add_zero, A_dioid_add_zero, A2C_dioid; simpl. 
       rewrite correct_eqv_add_constant. 
       rewrite <- correct_mm_props_add_ann. 
       rewrite <- correct_sg_CI_props_add_id. 
       rewrite correct_semiring_props_add_zero. 
       reflexivity. 
Qed. 

*)

(*
Lemma  correct_distributive_lattice_props_add_zero : 
  ∀ (S : Type) (rS : brel S) (join meet : binary_op S) (c:  cas_constant) 
    (eqvS : eqv_props S rS) 
    (pmeet : sg_CI_props S rS meet)
    (dlp : distributive_lattice_props S rS join meet), 
    P2C_distributive_lattice _ _ _ _ (distributive_lattice_props_add_zero S rS c join meet eqvS pmeet dlp)
    =
    distributive_lattice_props_add_zero c (P2C_distributive_lattice S rS join meet dlp).
Proof. intros S rS join meet c eqvS pmeet dlp. compute. reflexivity. Qed.

Theorem correct_distributive_lattice_add_zero : ∀ (S : Type) (distributive_latticeS: A_distributive_lattice S) (c : cas_constant), 
   distributive_lattice_add_zero S (A2C_distributive_lattice S distributive_latticeS) c 
   =
   A2C_distributive_lattice (with_constant S) (A_distributive_lattice_add_zero S distributive_latticeS c). 
Proof. intros S distributive_latticeS c. 
       unfold distributive_lattice_add_zero, A_distributive_lattice_add_zero, A2C_distributive_lattice; simpl. 
       rewrite correct_eqv_add_constant. 
       rewrite <- correct_sg_CI_props_add_ann. 
       rewrite <- correct_sg_CI_props_add_id. 
       rewrite correct_distributive_lattice_props_add_zero. 
       reflexivity. 
Qed. 


Lemma  correct_lattice_props_add_zero : 
  ∀ (S : Type) (c : cas_constant) (rS : brel S) (s : S) 
    (joinS meetS : binary_op S) 
    (eqvS : eqv_props S rS)
    (pjoin : sg_CI_props S rS joinS)
    (pmeet : sg_CI_props S rS meetS) 
    (bsS : lattice_props S rS joinS meetS), 
    P2C_lattice (with_constant S) 
       (brel_sum brel_constant rS) 
       (bop_add_id joinS c) 
       (bop_add_ann meetS c) 
       (lattice_props_add_zero S rS c joinS meetS eqvS pjoin pmeet bsS)
    =
    lattice_props_add_zero (P2C_lattice S rS joinS meetS bsS). 
Proof. intros S c rS s joinS meetS eqvS pjoin pmeet bsS. 
       unfold lattice_props_add_zero, lattice_props_add_zero, P2C_lattice, P2C_sg; simpl. 
       rewrite A_bs_add_zero_left_distributive_check_correct.
       (* below, ugly! what is broken? *) 
       unfold A_bs_add_one_left_distributive_decide; simpl.
       unfold A_bs_add_zero_distributive_dual_check.
       case_eq (A_lattice_distributive_dual_d S rS joinS meetS bsS); intros b P; simpl. 
       reflexivity.
       destruct b as [ [s1 [s2 s3]] Q]. simpl. 
       reflexivity.        
Defined. 
*)   

(*
Definition distributive_lattice_props_add_zero : 
  ∀ (S : Type) (rS : brel S) (c : cas_constant) (join meet : binary_op S), 
     eqv_props S rS -> 
     sg_CI_props S rS meet ->      
     distributive_lattice_props S rS join meet -> 
        distributive_lattice_props 
           (with_constant S) 
           (brel_sum brel_constant rS)
           (bop_add_id join c)
           (bop_add_ann meet c)
:= λ S rS c join meet eqvS p_meet p_dl, 
{|
  A_distributive_lattice_absorptive        := 
    A_bs_add_zero_left_absorptive S rS c join meet
       (A_eqv_reflexive S rS eqvS)
       (A_distributive_lattice_absorptive S rS join meet p_dl)
; A_distributive_lattice_absorptive_dual   := 
    A_bs_add_ann_add_id_left_absorptive S rS c meet join
      (A_eqv_symmetric S rS eqvS)
      (A_sg_CI_idempotent S rS meet p_meet)                                             
      (A_distributive_lattice_absorptive_dual S rS join meet p_dl)                                                                        
; A_distributive_lattice_distributive      := 
    A_bs_add_zero_left_distributive S rS c join meet
        (A_eqv_reflexive S rS eqvS)
        (A_distributive_lattice_distributive S rS join meet p_dl)
|}.


Definition A_distributive_lattice_add_zero : ∀ (S : Type),  A_distributive_lattice S -> cas_constant -> A_distributive_lattice (with_constant S) 
:= λ S bsS c, 
{| 
     A_distributive_lattice_eqv          := A_eqv_add_constant S (A_distributive_lattice_eqv S bsS) c 
   ; A_distributive_lattice_join         := bop_add_id (A_distributive_lattice_join S bsS) c
   ; A_distributive_lattice_meet        := bop_add_ann (A_distributive_lattice_meet S bsS) c
   ; A_distributive_lattice_join_props  := sg_CI_props_add_id S 
                                (A_eqv_eq S (A_distributive_lattice_eqv S bsS)) c 
                                (A_distributive_lattice_join S bsS)
                                (A_eqv_witness S (A_distributive_lattice_eqv S bsS))                                 
                                (A_eqv_props S (A_distributive_lattice_eqv S bsS)) 
                                (A_distributive_lattice_join_props S bsS) 
   ; A_distributive_lattice_meet_props := sg_CI_props_add_ann S 
                                (A_eqv_eq S (A_distributive_lattice_eqv S bsS)) c 
                                (A_distributive_lattice_meet S bsS)
                                (A_eqv_witness S (A_distributive_lattice_eqv S bsS))                                 
                                (A_eqv_props S (A_distributive_lattice_eqv S bsS)) 
                                (A_distributive_lattice_meet_props S bsS) 
   ; A_distributive_lattice_props       := distributive_lattice_props_add_zero S _ c 
                                (A_distributive_lattice_join S bsS) 
                                (A_distributive_lattice_meet S bsS)  
                                (A_eqv_props S (A_distributive_lattice_eqv S bsS)) 
                                (A_distributive_lattice_meet_props S bsS)                                 
                                (A_distributive_lattice_props S bsS)
   ; A_distributive_lattice_ast  := Ast_distributive_lattice_add_zero (c, A_distributive_lattice_ast S bsS)
|}. 


Definition lattice_props_add_zero : 
  ∀ (S : Type) (rS : brel S) (c : cas_constant) (join meet : binary_op S), 
     eqv_props S rS ->
     sg_CI_props S rS join ->          
     sg_CI_props S rS meet ->      
     lattice_props S rS join meet -> 
        lattice_props 
           (with_constant S) 
           (brel_sum brel_constant rS)
           (bop_add_id join c)
           (bop_add_ann meet c)
:= λ S rS c join meet eqvS p_join p_meet p_dl, 
{|
  A_lattice_absorptive        := 
    A_bs_add_zero_left_absorptive S rS c join meet
       (A_eqv_reflexive S rS eqvS)
       (A_lattice_absorptive S rS join meet p_dl)
; A_lattice_absorptive_dual   := 
    A_bs_add_ann_add_id_left_absorptive S rS c meet join
      (A_eqv_symmetric S rS eqvS)
      (A_sg_CI_idempotent S rS meet p_meet)                                             
      (A_lattice_absorptive_dual S rS join meet p_dl)                                                                        
; A_lattice_distributive_d      := 
     A_bs_add_zero_left_distributive_decide S rS c join meet 
        (A_eqv_reflexive S rS eqvS)
        (A_lattice_distributive_d S rS join meet p_dl)
; A_lattice_distributive_dual_d      := 
     A_bs_add_one_left_distributive_decide S rS c meet join
        (A_eqv_reflexive S rS eqvS)
        (A_eqv_symmetric S rS eqvS)
        (inl _ (A_sg_CI_idempotent S rS meet p_meet))
        (inl _ (A_lattice_absorptive_dual S rS join meet p_dl))
        (inl _ (A_bs_right_absorptive_implies_right_left S rS meet join
                  (A_eqv_reflexive S rS eqvS)                                                       
                  (A_eqv_transitive S rS eqvS)
                  (A_sg_CI_congruence S rS meet p_meet)
                  (A_sg_CI_commutative S rS meet p_meet)
                  (A_sg_CI_commutative S rS join p_join)
                  (A_bs_left_absorptive_implies_right S rS meet join
                        (A_eqv_reflexive S rS eqvS)                                                          
                        (A_eqv_transitive S rS eqvS)
                        (A_sg_CI_congruence S rS meet p_meet)
                        (A_sg_CI_commutative S rS join p_join)
                        (A_lattice_absorptive_dual S rS join meet p_dl)
                  ) 
               )
        ) 
        (A_lattice_distributive_dual_d S rS join meet p_dl)         
|}.


Definition A_lattice_add_zero : ∀ (S : Type),  A_lattice S -> cas_constant -> A_lattice (with_constant S) 
:= λ S bsS c, 
{| 
     A_lattice_eqv          := A_eqv_add_constant S (A_lattice_eqv S bsS) c 
   ; A_lattice_join         := bop_add_id (A_lattice_join S bsS) c
   ; A_lattice_meet        := bop_add_ann (A_lattice_meet S bsS) c
   ; A_lattice_join_props  := sg_CI_props_add_id S 
                                (A_eqv_eq S (A_lattice_eqv S bsS)) c 
                                (A_lattice_join S bsS)
                                (A_eqv_witness S (A_lattice_eqv S bsS))                                 
                                (A_eqv_props S (A_lattice_eqv S bsS)) 
                                (A_lattice_join_props S bsS) 
   ; A_lattice_meet_props := sg_CI_props_add_ann S 
                                (A_eqv_eq S (A_lattice_eqv S bsS)) c 
                                (A_lattice_meet S bsS)
                                (A_eqv_witness S (A_lattice_eqv S bsS))                                 
                                (A_eqv_props S (A_lattice_eqv S bsS)) 
                                (A_lattice_meet_props S bsS) 
   ; A_lattice_props       := lattice_props_add_zero S _ c 
                                (A_lattice_join S bsS) 
                                (A_lattice_meet S bsS)  
                                (A_eqv_props S (A_lattice_eqv S bsS))
                                (A_lattice_join_props S bsS)                                                                 
                                (A_lattice_meet_props S bsS)                                 
                                (A_lattice_props S bsS)
   ; A_lattice_ast  := Ast_lattice_add_zero (c, A_lattice_ast S bsS)
|}. 


Definition semiring_props_add_zero : 
  ∀ (S : Type) (rS : brel S) (c : cas_constant) (join meet : binary_op S) (s : S), 
     eqv_props S rS -> 
     semiring_props S rS join meet -> 
        semiring_props 
           (with_constant S) 
           (brel_sum brel_constant rS)
           (bop_add_id join c)
           (bop_add_ann meet c)
:= λ S rS c join meet s eqvS srp, 
{|
  A_semiring_left_distributive        :=
    A_bs_add_zero_left_distributive S rS c join meet
        (A_eqv_reflexive S rS eqvS)
        (A_semiring_left_distributive S rS join meet srp)
    
; A_semiring_right_distributive       :=
    A_bs_add_zero_right_distributive S rS c join meet
        (A_eqv_reflexive S rS eqvS)
        (A_semiring_right_distributive S rS join meet srp)

; A_semiring_plus_id_is_times_ann_d   :=
     inl _ (A_bs_add_zero_id_equals_ann S rS c join meet (A_eqv_reflexive S rS eqvS))    

; A_semiring_times_id_is_plus_ann_d   :=
    A_bs_add_zero_ann_equals_id_decide S rS c join meet s
      (A_eqv_reflexive S rS eqvS)
      (A_semiring_times_id_is_plus_ann_d S rS join meet srp)
                                                                     
; A_semiring_left_absorptive_d   :=
    A_bs_add_zero_left_absorptive_decide S rS c join meet
        (A_eqv_reflexive S rS eqvS)
        (A_semiring_left_absorptive_d S rS join meet srp)

; A_semiring_right_absorptive_d  :=
     A_bs_add_zero_right_absorptive_decide S rS c join meet
        (A_eqv_reflexive S rS eqvS)
        (A_semiring_right_absorptive_d S rS join meet srp)
|}.


Definition A_dioid_add_zero : ∀ (S : Type),  A_dioid S -> cas_constant -> A_dioid (with_constant S) 
:= λ S bsS c, 
{| 
     A_dioid_eqv          := A_eqv_add_constant S (A_dioid_eqv S bsS) c 
   ; A_dioid_plus         := bop_add_id (A_dioid_plus S bsS) c
   ; A_dioid_times         := bop_add_ann (A_dioid_times S bsS) c
   ; A_dioid_plus_props  := sg_CI_props_add_id S 
                                (A_eqv_eq S (A_dioid_eqv S bsS)) c 
                                (A_dioid_plus S bsS)
                                (A_eqv_witness S (A_dioid_eqv S bsS))                                 
                                (A_eqv_props S (A_dioid_eqv S bsS)) 
                                (A_dioid_plus_props S bsS) 
   ; A_dioid_times_props := mm_props_add_ann S 
                                (A_eqv_eq S (A_dioid_eqv S bsS)) c 
                                (A_dioid_times S bsS)
                                (A_eqv_witness S (A_dioid_eqv S bsS))
                                (A_eqv_new S (A_dioid_eqv S bsS))
                                (A_eqv_not_trivial S (A_dioid_eqv S bsS)) 
                                (A_eqv_props S (A_dioid_eqv S bsS)) 
                                (A_dioid_times_props S bsS) 
   ; A_dioid_props       := semiring_props_add_zero S _ c 
                                (A_dioid_plus S bsS) 
                                (A_dioid_times S bsS)
                                (A_eqv_witness S (A_dioid_eqv S bsS))                                
                                (A_eqv_props S (A_dioid_eqv S bsS))
                                (A_dioid_props S bsS)
   ; A_dioid_plus_ast     := Ast_bop_add_id (c, A_dioid_plus_ast S bsS)
   ; A_dioid_times_ast    := Ast_bop_add_ann (c, A_dioid_times_ast S bsS)   
   ; A_dioid_ast          := Ast_dioid_add_zero (c, A_dioid_ast S bsS)
|}. 


Definition A_semiring_add_zero : ∀ (S : Type),  A_semiring S -> cas_constant -> A_semiring (with_constant S) 
:= λ S bsS c, 
{| 
     A_semiring_eqv          := A_eqv_add_constant S (A_semiring_eqv S bsS) c 
   ; A_semiring_plus         := bop_add_id (A_semiring_plus S bsS) c
   ; A_semiring_times        := bop_add_ann (A_semiring_times S bsS) c
   ; A_semiring_plus_props  := sg_C_props_add_id S 
                                (A_eqv_eq S (A_semiring_eqv S bsS)) c 
                                (A_semiring_plus S bsS)
                                (A_eqv_witness S (A_semiring_eqv S bsS))
                                (A_eqv_new S (A_semiring_eqv S bsS))
                                (A_eqv_not_trivial S (A_semiring_eqv S bsS))                                 
                                (A_eqv_props S (A_semiring_eqv S bsS)) 
                                (A_semiring_plus_props S bsS) 
   ; A_semiring_times_props := mm_props_add_ann S 
                                (A_eqv_eq S (A_semiring_eqv S bsS)) c 
                                (A_semiring_times S bsS)
                                (A_eqv_witness S (A_semiring_eqv S bsS))
                                (A_eqv_new S (A_semiring_eqv S bsS))
                                (A_eqv_not_trivial S (A_semiring_eqv S bsS))                                 
                                (A_eqv_props S (A_semiring_eqv S bsS)) 
                                (A_semiring_times_props S bsS) 
   ; A_semiring_props       := semiring_props_add_zero S _ c 
                                (A_semiring_plus S bsS) 
                                (A_semiring_times S bsS)
                                (A_eqv_witness S (A_semiring_eqv S bsS))                                
                                (A_eqv_props S (A_semiring_eqv S bsS))
                                (A_semiring_props S bsS)
   ; A_semiring_plus_ast     := Ast_bop_add_id (c, A_semiring_plus_ast S bsS)
   ; A_semiring_times_ast    := Ast_bop_add_ann (c, A_semiring_times_ast S bsS)                                
   ; A_semiring_ast          := Ast_semiring_add_zero (c, A_semiring_ast S bsS)
|}. 


Definition distributive_lattice_props_add_zero : 
  ∀ {S : Type} (c : cas_constant), @distributive_lattice_propificates S -> @distributive_lattice_propificates (with_constant S) 
:= λ {S} c dlc ,
{|
  distributive_lattice_absorptive        := Assert_Left_Left_Absorptive
; distributive_lattice_absorptive_dual   := Assert_Left_Left_Absorptive_Dual
; distributive_lattice_distributive      := Assert_Left_Distributive 
|}.

Definition distributive_lattice_add_zero : ∀ (S : Type),  @distributive_lattice S -> cas_constant -> @distributive_lattice (with_constant S) 
:= λ S bsS c,
{| 
     distributive_lattice_eqv         := eqv_add_constant (distributive_lattice_eqv bsS) c 
   ; distributive_lattice_join        := bop_add_id (distributive_lattice_join bsS) c
   ; distributive_lattice_meet        := bop_add_ann (distributive_lattice_meet bsS) c
   ; distributive_lattice_join_props  := sg_CI_props_add_id c (distributive_lattice_join_props bsS)
   ; distributive_lattice_meet_props  := sg_CI_props_add_ann c (distributive_lattice_meet_props bsS)
   ; distributive_lattice_props       := distributive_lattice_props_add_zero c (distributive_lattice_props bsS )
   ; distributive_lattice_join_ast    := Ast_bop_add_id (c, distributive_lattice_join_ast bsS)
   ; distributive_lattice_meet_ast    := Ast_bop_add_ann (c, distributive_lattice_meet_ast bsS) 
   ; distributive_lattice_ast         := Ast_distributive_lattice_add_zero (c, distributive_lattice_ast bsS)
|}. 


Definition lattice_props_add_zero : 
  ∀ {S : Type}, @lattice_propificates S -> @lattice_propificates (with_constant S) 
:= λ {S} pS, 
{|
  lattice_absorptive          := Assert_Left_Left_Absorptive
; lattice_absorptive_dual     := Assert_Left_Left_Absorptive_Dual
; lattice_distributive_d      := A_bs_add_zero_left_distributive_check (lattice_distributive_d pS) 
; lattice_distributive_dual_d := A_bs_add_zero_distributive_dual_check (lattice_distributive_dual_d pS) 
|}.

Definition lattice_add_zero : ∀ (S : Type),  @lattice S -> cas_constant -> @lattice (with_constant S) 
:= λ S bsS c,
let s :=   eqv_witness (lattice_eqv bsS) in
let f :=   eqv_new (lattice_eqv bsS) in   
{| 
     lattice_eqv         := eqv_add_constant (lattice_eqv bsS) c 
   ; lattice_join        := bop_add_id (lattice_join bsS) c
   ; lattice_meet        := bop_add_ann (lattice_meet bsS) c
   ; lattice_join_props  := sg_CI_props_add_id c (lattice_join_props bsS)
   ; lattice_meet_props  := sg_CI_props_add_ann c (lattice_meet_props bsS)
   ; lattice_props       := lattice_props_add_zero (lattice_props bsS)
   ; lattice_join_ast    := Ast_bop_add_id (c, lattice_join_ast bsS)
   ; lattice_meet_ast    := Ast_bop_add_ann (c, lattice_meet_ast bsS)                             
   ; lattice_ast         := Ast_lattice_add_zero (c, lattice_ast bsS)
|}. 
*)

