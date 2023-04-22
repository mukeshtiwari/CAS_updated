
Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.
Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.po.properties.
Require Import CAS.coq.po.structures.
Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures.
Require Import CAS.coq.os.properties.
Require Import CAS.coq.os.structures.


Require Import CAS.coq.eqv.add_constant.
Require Import CAS.coq.po.add_bottom. 
Require Import CAS.coq.sg.add_id.


Section Theory.

Variable bottom : cas_constant.  
Variable S   : Type.
Variable eq  : brel S.
Variable lte : brel S.
Variable b   : binary_op S.

Variable wS : S. 
Variable ref : brel_reflexive S eq. 
Variable lteRef : brel_reflexive S lte. 


(*  
Notation "a [+ann] b" := (bop_add_ann b a)       (at level 15).
Notation "a [+id] b"  := (bop_add_id b a)       (at level 15).
*)   


Lemma os_add_bottom_id_left_monotone
      (LI : os_left_increasing lte b)
      (LM : os_left_monotone lte b) : 
        os_left_monotone (brel_add_bottom lte bottom) (bop_add_id b bottom). 
Proof. intros [c1 | s1] [c2 | s2] [c3 | s3]; simpl; intro A; auto. discriminate A. Qed. 

Lemma os_add_bottom_id_not_left_monotone_v1 : 
      os_not_left_increasing lte b -> 
        os_not_left_monotone (brel_add_bottom lte bottom) (bop_add_id b bottom). 
Proof. intros [[s1 s2] nli]. 
       exists (inr s1, (inl bottom, inr s2)).  compute.
       split; auto. 
Defined. 

Lemma os_add_bottom_id_not_left_monotone_v2 : 
      os_not_left_monotone lte b -> 
        os_not_left_monotone (brel_add_bottom lte bottom) (bop_add_id b bottom). 
Proof. intros [[s1 [s2 s3]] [A B]]. 
       exists (inr s1, (inr s2, inr s3)).  compute.
       split; auto. 
Defined. 


Lemma os_add_bottom_id_right_monotone   
      (RI : os_right_increasing lte b)
      (RM : os_right_monotone lte b) : 
        os_right_monotone (brel_add_bottom lte bottom) (bop_add_id b bottom). 
Proof. intros[c1 | s1] [c2 | s2] [c3 | s3]; simpl; intro A; auto. discriminate A. Qed.


Lemma os_add_bottom_id_strictly_left_monotone  : 
     os_left_strictly_increasing lte b -> os_left_strictly_monotone lte b -> 
        os_left_strictly_monotone (brel_add_bottom lte bottom) (bop_add_id b bottom). 
Proof. intros LI LM [c1 | s1] [c2 | s2] [c3 | s3]; simpl; intros A B; auto.
       discriminate B. discriminate A.
Qed. 

Lemma os_add_bottom_id_strictly_right_monotone  : 
     os_right_strictly_increasing lte b -> os_right_strictly_monotone lte b -> 
        os_right_strictly_monotone (brel_add_bottom lte bottom) (bop_add_id b bottom). 
Proof. intros RI RM [c1 | s1] [c2 | s2] [c3 | s3]; simpl; intros A B; auto.
       discriminate B. discriminate A.
Qed.

Lemma os_add_bottom_id_left_increasing  : 
     os_left_increasing lte b -> 
        os_left_increasing (brel_add_bottom lte bottom) (bop_add_id b bottom). 
Proof. intros LI [c1 | s1] [c2 | s2]; simpl; auto. Qed. 

Lemma os_add_bottom_id_right_increasing  : 
     os_right_increasing lte b -> 
        os_right_increasing (brel_add_bottom lte bottom) (bop_add_id b bottom). 
Proof. intros RI [c1 | s1] [c2 | s2]; simpl; auto. Qed. 


Lemma os_add_bottom_id_not_left_strictly_increasing  : 
        os_not_left_strictly_increasing (brel_add_bottom lte bottom) (bop_add_id b bottom). 
Proof. exists (inr wS, inl bottom). compute. 
       right. apply lteRef. 
Defined. 

End Theory.

Section ACAS.

  
Definition bs_proofs_add_one : 
  ∀ (S : Type) (rS : brel S) (c : cas_constant) (plusS timesS : binary_op S) (s : S), 
     eqv_proofs S rS -> 
     asg_proofs S rS plusS -> 
     bs_proofs S rS plusS timesS -> 
        bs_proofs 
           (with_constant S) 
           (brel_sum brel_constant rS)
           (bop_add_ann plusS c)
           (bop_add_id timesS c)
:= λ S rS c plusS timesS s eqvS ppS pS, 
{|
  A_bs_left_distributive_d    := 
     bops_add_one_left_distributive_decide S rS c plusS timesS 
        (A_eqv_reflexive S rS eqvS)
        (A_eqv_symmetric S rS eqvS)
        (A_asg_idempotent_d S rS plusS ppS)
        (A_bs_left_left_absorptive_d S rS plusS timesS pS)
        (A_bs_right_left_absorptive_d S rS plusS timesS pS)
        (A_bs_left_distributive_d S rS plusS timesS pS) 
; A_bs_right_distributive_d   := 
     bops_add_one_right_distributive_decide S rS c plusS timesS 
        (A_eqv_reflexive S rS eqvS)
        (A_eqv_symmetric S rS eqvS)
        (A_asg_idempotent_d S rS plusS ppS)
        (A_bs_left_right_absorptive_d S rS plusS timesS pS)
        (A_bs_right_right_absorptive_d S rS plusS timesS pS)
        (A_bs_right_distributive_d S rS plusS timesS pS) 
; A_bs_left_left_absorptive_d      := 
     bops_add_one_left_left_absorptive_decide S rS c plusS timesS 
        (A_eqv_symmetric S rS eqvS)
        (A_asg_idempotent_d S rS plusS ppS)
        (A_bs_left_left_absorptive_d S rS plusS timesS pS)
; A_bs_left_right_absorptive_d      := 
     bops_add_one_left_right_absorptive_decide S rS c plusS timesS 
        (A_eqv_symmetric S rS eqvS)
        (A_asg_idempotent_d S rS plusS ppS)
        (A_bs_left_right_absorptive_d S rS plusS timesS pS)
; A_bs_right_left_absorptive_d     := 
     bops_add_one_right_left_absorptive_decide S rS c plusS timesS 
        (A_eqv_symmetric S rS eqvS)
        (A_asg_idempotent_d S rS plusS ppS)
        (A_bs_right_left_absorptive_d S rS plusS timesS pS)
; A_bs_right_right_absorptive_d     := 
     bops_add_one_right_right_absorptive_decide S rS c plusS timesS 
        (A_eqv_symmetric S rS eqvS)
        (A_asg_idempotent_d S rS plusS ppS)
        (A_bs_right_right_absorptive_d S rS plusS timesS pS)
|}.

Definition id_ann_proofs_add_one : 
  ∀ (S : Type) (rS : brel S) (c : cas_constant) (plusS timesS : binary_op S) (s : S), 
     eqv_proofs S rS -> 
     id_ann_proofs S rS plusS timesS -> 
        id_ann_proofs 
           (with_constant S) 
           (brel_sum brel_constant rS)
           (bop_add_ann plusS c)
           (bop_add_id timesS c)           
:= λ S rS c plusS timesS s eqvS pS,
let refS := A_eqv_reflexive S rS eqvS in   
{|
    A_id_ann_exists_plus_id_d       := bop_add_ann_exists_id_decide S rS c plusS s (A_id_ann_exists_plus_id_d S rS plusS timesS pS)
  ; A_id_ann_exists_plus_ann_d      := inl (bop_add_ann_exists_ann S rS c plusS) 
  ; A_id_ann_exists_times_id_d      := inl (bop_add_id_exists_id S rS c timesS refS)
  ; A_id_ann_exists_times_ann_d     := bop_add_id_exists_ann_decide S rS c timesS s refS (A_id_ann_exists_times_ann_d S rS plusS timesS pS)
  ; A_id_ann_plus_id_is_times_ann_d := 
    bops_add_one_id_equals_ann_decide S rS c plusS timesS s (A_eqv_reflexive S rS eqvS) 
      (A_id_ann_plus_id_is_times_ann_d S rS plusS timesS pS)
; A_id_ann_times_id_is_plus_ann_d :=  
     inl _ (bops_add_id_add_ann_id_equals_ann S rS c timesS plusS (A_eqv_reflexive S rS eqvS))
|}.



Definition A_bs_add_one : ∀ (S : Type),  A_bs S -> cas_constant -> A_bs (with_constant S) 
:= λ S bsS c,
let eqvS  := A_bs_eqv S bsS in
let peqvS := A_eqv_proofs S eqvS in
let s     := A_eqv_witness S eqvS in
let f     := A_eqv_new S eqvS in
let Pf    := A_eqv_not_trivial S eqvS in 
let rS    := A_eqv_eq S eqvS in   
let plus  := A_bs_plus S bsS in
let times := A_bs_times S bsS in
let pproofs := A_bs_plus_proofs S bsS in
let tproofs := A_bs_times_proofs S bsS in 
{| 
     A_bs_eqv          := A_eqv_add_constant S eqvS c 
   ; A_bs_plus         := bop_add_ann plus c
   ; A_bs_times        := bop_add_id times c
   ; A_bs_plus_proofs  := asg_proofs_add_ann S rS c plus s peqvS pproofs 
   ; A_bs_times_proofs := msg_proofs_add_id S rS c times s f Pf peqvS tproofs
   ; A_bs_id_ann_proofs := id_ann_proofs_add_one S _ c plus times (A_eqv_witness S eqvS) (A_eqv_proofs S eqvS) (A_bs_id_ann_proofs S bsS)
   ; A_bs_proofs       := bs_proofs_add_one S rS c plus times s peqvS pproofs (A_bs_proofs S bsS)
   ; A_bs_ast          := Ast_bs_add_one (c, A_bs_ast S bsS)
|}.





Definition lattice_proofs_add_one : 
  ∀ (S : Type) (rS : brel S) (c : cas_constant) (join meet : binary_op S), 
     eqv_proofs S rS -> 
     sg_CI_proofs S rS join ->
     sg_CI_proofs S rS meet ->      
     lattice_proofs S rS join meet -> 
        lattice_proofs 
           (with_constant S) 
           (brel_sum brel_constant rS)
           (bop_add_ann join c)
           (bop_add_id meet c)
:= λ S rS c join meet eqvS p_join p_meet pl, 
{|
  A_lattice_absorptive        := 
    bops_add_bottom_id_left_left_absorptive S rS c join meet
       (A_eqv_symmetric S rS eqvS)
       (A_sg_CI_idempotent S rS join p_join)
       (A_lattice_absorptive S rS join meet pl)
; A_lattice_absorptive_dual   := 
    bops_add_id_add_ann_left_left_absorptive S rS c meet join 
      (A_eqv_reflexive S rS eqvS)
      (A_lattice_absorptive_dual S rS join meet pl)                                                                        
; A_lattice_distributive_d      :=
     bops_add_one_left_distributive_decide S rS c join meet
        (A_eqv_reflexive S rS eqvS)
        (A_eqv_symmetric S rS eqvS)
        (inl _ (A_sg_CI_idempotent S rS join p_join))        
        (inl _ (A_lattice_absorptive S rS join meet pl))
        (inl _ (bops_left_right_absorptive_implies_right_left S rS join meet
                 (A_eqv_reflexive S rS eqvS)                                                       
                 (A_eqv_transitive S rS eqvS)
                 (A_sg_CI_congruence S rS join p_join)
                 (A_sg_CI_commutative S rS join p_join)
                 (A_sg_CI_commutative S rS meet p_meet)
                 (bops_left_left_absorptive_implies_left_right S rS join meet
                    (A_eqv_reflexive S rS eqvS)                                                          
                    (A_eqv_transitive S rS eqvS)
                    (A_sg_CI_congruence S rS join p_join)
                    (A_sg_CI_commutative S rS meet p_meet)
                    (A_lattice_absorptive S rS join meet pl)
                 )                                          
               )
        )
        (A_lattice_distributive_d S rS join meet pl) 
; A_lattice_distributive_dual_d :=
   bops_add_zero_left_distributive_decide S rS c meet join
        (A_eqv_reflexive S rS eqvS)
        (A_lattice_distributive_dual_d S rS join meet pl) 
|}.

(*
Definition A_lattice_add_one : ∀ (S : Type),  A_lattice S -> cas_constant -> A_lattice (with_constant S) 
:= λ S bsS c, 
{| 
     A_lattice_eqv          := A_eqv_add_constant S (A_lattice_eqv S bsS) c 
   ; A_lattice_join         := bop_add_ann (A_lattice_join S bsS) c
   ; A_lattice_meet        := bop_add_id (A_lattice_meet S bsS) c
   ; A_lattice_join_proofs  := sg_CI_proofs_add_ann S 
                                (A_eqv_eq S (A_lattice_eqv S bsS)) c 
                                (A_lattice_join S bsS)
                                (A_eqv_witness S (A_lattice_eqv S bsS))
                                (A_eqv_proofs S (A_lattice_eqv S bsS)) 
                                (A_lattice_join_proofs S bsS) 
   ; A_lattice_meet_proofs := sg_CI_proofs_add_id S 
                                (A_eqv_eq S (A_lattice_eqv S bsS)) c 
                                (A_lattice_meet S bsS)
                                (A_eqv_witness S (A_lattice_eqv S bsS))                                
                                (A_eqv_proofs S (A_lattice_eqv S bsS)) 
                                (A_lattice_meet_proofs S bsS) 
   ; A_lattice_proofs       := lattice_proofs_add_one S _ c 
                                (A_lattice_join S bsS) 
                                (A_lattice_meet S bsS)  
                                (A_eqv_proofs S (A_lattice_eqv S bsS)) 
                                (A_lattice_join_proofs S bsS)
                                (A_lattice_meet_proofs S bsS)                                 
                                (A_lattice_proofs S bsS)
   ; A_lattice_ast         :=  Ast_lattice_add_one (c, A_lattice_ast S bsS)
|}. 



Definition distributive_lattice_proofs_add_one : 
  ∀ (S : Type) (rS : brel S) (c : cas_constant) (join meet : binary_op S), 
     eqv_proofs S rS -> 
     sg_CI_proofs S rS join ->
     sg_CI_proofs S rS meet ->      
     distributive_lattice_proofs S rS join meet -> 
        distributive_lattice_proofs 
           (with_constant S) 
           (brel_sum brel_constant rS)
           (bop_add_ann join c)
           (bop_add_id meet c)
:= λ S rS c join meet eqvS p_join p_meet p_dl, 
{|
  A_distributive_lattice_absorptive        := 
    bops_add_bottom_id_left_left_absorptive S rS c join meet
       (A_eqv_symmetric S rS eqvS)
       (A_sg_CI_idempotent S rS join p_join)
       (A_distributive_lattice_absorptive S rS join meet p_dl)
; A_distributive_lattice_absorptive_dual   := 
    bops_add_id_add_ann_left_left_absorptive S rS c meet join 
      (A_eqv_reflexive S rS eqvS)
      (A_distributive_lattice_absorptive_dual S rS join meet p_dl)                                                                        
; A_distributive_lattice_distributive      := 
    bops_add_bottom_id_left_distributive S rS c join meet
        (A_eqv_reflexive S rS eqvS)
        (A_eqv_symmetric S rS eqvS)
        (A_sg_CI_idempotent S rS join p_join)
        (A_distributive_lattice_absorptive S rS join meet p_dl)
        (bops_left_right_absorptive_implies_right_left S rS join meet
            (A_eqv_reflexive S rS eqvS)                                                       
            (A_eqv_transitive S rS eqvS)
            (A_sg_CI_congruence S rS join p_join)
            (A_sg_CI_commutative S rS join p_join)
            (A_sg_CI_commutative S rS meet p_meet)
            (bops_left_left_absorptive_implies_left_right S rS join meet
                (A_eqv_reflexive S rS eqvS)                                                          
                (A_eqv_transitive S rS eqvS)
                (A_sg_CI_congruence S rS join p_join)
                (A_sg_CI_commutative S rS meet p_meet)
                (A_distributive_lattice_absorptive S rS join meet p_dl)
            )                                          
        )
        (A_distributive_lattice_distributive S rS join meet p_dl)
(*        
; A_distributive_lattice_distributive_dual := 
    bops_add_id_add_ann_left_distributive S rS c meet join 
        (A_eqv_reflexive S rS eqvS)
        (A_distributive_lattice_distributive_dual S rS join meet p_dl)        
*) 
|}.

Definition A_distributive_lattice_add_one : ∀ (S : Type),  A_distributive_lattice S -> cas_constant -> A_distributive_lattice (with_constant S) 
:= λ S bsS c, 
{| 
     A_distributive_lattice_eqv          := A_eqv_add_constant S (A_distributive_lattice_eqv S bsS) c 
   ; A_distributive_lattice_join         := bop_add_ann (A_distributive_lattice_join S bsS) c
   ; A_distributive_lattice_meet        := bop_add_id (A_distributive_lattice_meet S bsS) c
   ; A_distributive_lattice_join_proofs  := sg_CI_proofs_add_ann S 
                                (A_eqv_eq S (A_distributive_lattice_eqv S bsS)) c 
                                (A_distributive_lattice_join S bsS)
                                (A_eqv_witness S (A_distributive_lattice_eqv S bsS))                                
                                (A_eqv_proofs S (A_distributive_lattice_eqv S bsS)) 
                                (A_distributive_lattice_join_proofs S bsS) 
   ; A_distributive_lattice_meet_proofs := sg_CI_proofs_add_id S 
                                (A_eqv_eq S (A_distributive_lattice_eqv S bsS)) c 
                                (A_distributive_lattice_meet S bsS)
                                (A_eqv_witness S (A_distributive_lattice_eqv S bsS))                                                                
                                (A_eqv_proofs S (A_distributive_lattice_eqv S bsS)) 
                                (A_distributive_lattice_meet_proofs S bsS) 
   ; A_distributive_lattice_proofs       := distributive_lattice_proofs_add_one S _ c 
                                (A_distributive_lattice_join S bsS) 
                                (A_distributive_lattice_meet S bsS)  
                                (A_eqv_proofs S (A_distributive_lattice_eqv S bsS)) 
                                (A_distributive_lattice_join_proofs S bsS)
                                (A_distributive_lattice_meet_proofs S bsS)                                 
                                (A_distributive_lattice_proofs S bsS)
   ; A_distributive_lattice_join_ast    := Ast_bop_add_ann (c, A_distributive_lattice_join_ast S bsS)
   ; A_distributive_lattice_meet_ast    := Ast_bop_add_id (c, A_distributive_lattice_meet_ast S bsS)                                 
   ; A_distributive_lattice_ast         := Ast_distributive_lattice_add_one (c, A_distributive_lattice_ast S bsS)
|}. 

*)

(* Note: This is another example (like llex) where we can combine semirings and obtain 
   something that is not a semiring 

bops_add_bottom_id_left_distributive
     : ∀ (S : Type) (r : brel S) (c : cas_constant) (b1 b2 : binary_op S),
       brel_properties.brel_reflexive S r
       → brel_properties.brel_symmetric S r
         → bop_properties.bop_idempotent S r b1
ll         → bs_properties.bops_left_left_absorptive S r b1 b2
rl           → bs_properties.bops_right_left_absorptive S r b1 b2
               → bs_properties.bop_left_distributive S r b1 b2
                 → bs_properties.bop_left_distributive (with_constant S) (brel_add_constant r c) (bop_add_ann b1 c) (bop_add_id b2 c)

bops_add_bottom_id_right_distributive
     : ∀ (S : Type) (r : brel S) (c : cas_constant) (b1 b2 : binary_op S),
       brel_properties.brel_reflexive S r
       → brel_properties.brel_symmetric S r
         → bop_properties.bop_idempotent S r b1
lr         → bs_properties.bops_left_right_absorptive S r b1 b2
rr           → bs_properties.bops_right_right_absorptive S r b1 b2
               → bs_properties.bop_right_distributive S r b1 b2
                 → bs_properties.bop_right_distributive (with_constant S) (brel_add_constant r c) (bop_add_ann b1 c) (bop_add_id b2 c)

so we cannot use add_one to map dioids to dioids or semirings to semirings. 

BUT, what if structures are commutative, and we can derive one of the absorptions? (from 0-stable?) 

Definition bops_left_left_absorptive (S : Type) (r : brel S) (b1 b2 : binary_op S) := 
    ∀ (s t : S), r s (b1 s (b2 s t)) = true.

Definition bops_left_right_absorptive (S : Type) (r : brel S) (b1 b2 : binary_op S) := 
    ∀ (s t : S), r s (b1 s (b2 t s)) = true.

Definition bops_right_left_absorptive (S : Type) (r : brel S) (b1 b2 : binary_op S) := 
    ∀ (s t : S), r s (b1 (b2 s t) s) = true.

Definition bops_right_right_absorptive (S : Type) (r : brel S) (b1 b2 : binary_op S) := 
    ∀ (s t : S), r s (b1 (b2 t s) s) = true.

comutative(b1) -> 
    lr <-> rr 
    ll <-> rl 
commutative(b2) -> 
    ll <-> lr 
    lr <-> rl 

so comutative(b1) -> commutative(b2) -> ll <-> lr <-> rl <-> rr 

So only need one to get them all 

 *)

End ACAS.

Section CAS.


Definition bops_add_one_left_distributive_check : 
   ∀ {S : Type} 
     (c : cas_constant),
     check_idempotent (S := S) -> 
     check_left_left_absorptive (S := S) -> 
     check_right_left_absorptive (S := S) -> 
     check_left_distributive (S := S) ->  check_left_distributive (S := (with_constant S))
:= λ {S} c idemS_d llaS_d rlaS_d ldS_d, 
   match ldS_d with 
   | Certify_Left_Distributive  => 
    match llaS_d with 
    | Certify_Left_Left_Absorptive => 
      match rlaS_d with 
      | Certify_Right_Left_Absorptive => 
         match idemS_d with 
         | Certify_Idempotent      => Certify_Left_Distributive 
         | Certify_Not_Idempotent s => Certify_Not_Left_Distributive (inr s, (inl c, inl c))
        end 
      | Certify_Not_Right_Left_Absorptive (s1, s2) => 
            Certify_Not_Left_Distributive (inr _ s1, (inr _ s2, inl _ c))
      end 
    | Certify_Not_Left_Left_Absorptive (s1, s2) => 
         Certify_Not_Left_Distributive (inr _ s1, (inl _ c, inr _ s2))
    end 
   | Certify_Not_Left_Distributive (s1, (s2, s3)) => 
        Certify_Not_Left_Distributive (inr _ s1, (inr _ s2, inr _ s3))
   end. 


Definition bops_add_one_right_distributive_check : 
   ∀ {S : Type} 
     (c : cas_constant),
     check_idempotent (S := S) -> 
     check_left_right_absorptive (S := S) -> 
     check_right_right_absorptive (S := S) -> 
     check_right_distributive (S := S) ->  check_right_distributive (S := (with_constant S))
:= λ {S} c idemS_d llaS_d rlaS_d ldS_d, 
   match ldS_d with 
   | Certify_Right_Distributive => 
    match llaS_d with 
    | Certify_Left_Right_Absorptive => 
      match rlaS_d with 
      | Certify_Right_Right_Absorptive => 
         match idemS_d with 
         | Certify_Idempotent      => Certify_Right_Distributive 
         | Certify_Not_Idempotent s => Certify_Not_Right_Distributive (inr s, (inl c, inl c))
        end 
      | Certify_Not_Right_Right_Absorptive (s1, s2) => 
            Certify_Not_Right_Distributive (inr _ s1, (inr _ s2, inl _ c))
      end 
    | Certify_Not_Left_Right_Absorptive (s1, s2) => 
         Certify_Not_Right_Distributive (inr _ s1, (inl _ c, inr _ s2))
    end 
   | Certify_Not_Right_Distributive (s1, (s2, s3)) => 
        Certify_Not_Right_Distributive (inr _ s1, (inr _ s2, inr _ s3))
   end. 


Definition bops_add_one_left_left_absorptive_check : 
   ∀ {S : Type} 
     (c : cas_constant),
     check_idempotent (S := S) -> 
     check_left_left_absorptive (S := S) -> check_left_left_absorptive (S := (with_constant S))
:= λ {S} c idemS_d laS_d, 
   match laS_d with 
   | Certify_Left_Left_Absorptive => 
     match idemS_d with 
     | Certify_Idempotent => Certify_Left_Left_Absorptive 
     | Certify_Not_Idempotent s =>  Certify_Not_Left_Left_Absorptive (inr s, inl c) 
     end 
   | Certify_Not_Left_Left_Absorptive (s1, s2) => Certify_Not_Left_Left_Absorptive (inr _ s1, inr _ s2)
   end. 


Definition bops_add_one_left_right_absorptive_check : 
   ∀ {S : Type} 
     (c : cas_constant),
     check_idempotent (S := S) -> 
     check_left_right_absorptive (S := S) -> check_left_right_absorptive (S := (with_constant S))
:= λ {S} c idemS_d laS_d, 
   match laS_d with 
   | Certify_Left_Right_Absorptive => 
     match idemS_d with 
     | Certify_Idempotent => Certify_Left_Right_Absorptive 
     | Certify_Not_Idempotent s =>  Certify_Not_Left_Right_Absorptive (inr s, inl c) 
     end 
   | Certify_Not_Left_Right_Absorptive (s1, s2) => Certify_Not_Left_Right_Absorptive (inr _ s1, inr _ s2)
   end. 


Definition bops_add_one_right_left_absorptive_check : 
   ∀ {S : Type} 
     (c : cas_constant),
     check_idempotent (S := S) -> 
     check_right_left_absorptive (S := S) -> check_right_left_absorptive (S := (with_constant S))
:= λ {S} c idemS_d laS_d, 
   match laS_d with 
   | Certify_Right_Left_Absorptive => 
     match idemS_d with 
     | Certify_Idempotent => Certify_Right_Left_Absorptive 
     | Certify_Not_Idempotent s =>  Certify_Not_Right_Left_Absorptive (inr s, inl c) 
     end 
   | Certify_Not_Right_Left_Absorptive (s1, s2) => Certify_Not_Right_Left_Absorptive (inr _ s1, inr _ s2)
   end. 


Definition bops_add_one_right_right_absorptive_check : 
   ∀ {S : Type} 
     (c : cas_constant),
     check_idempotent (S := S) -> 
     check_right_right_absorptive (S := S) -> check_right_right_absorptive (S := (with_constant S))
:= λ {S} c idemS_d laS_d, 
   match laS_d with 
   | Certify_Right_Right_Absorptive => 
     match idemS_d with 
     | Certify_Idempotent => Certify_Right_Right_Absorptive 
     | Certify_Not_Idempotent s =>  Certify_Not_Right_Right_Absorptive (inr s, inl c) 
     end 
   | Certify_Not_Right_Right_Absorptive (s1, s2) => Certify_Not_Right_Right_Absorptive (inr _ s1, inr _ s2)
   end.

Definition bops_plus_id_equals_times_ann_check : 
   ∀ {S : Type}  (c : cas_constant),
     @check_plus_id_equals_times_ann S -> @check_plus_id_equals_times_ann (with_constant S)
:= λ {S} c iea_d, 
  match iea_d with                    (*** NB : same terms, different types! ***) 
  | Certify_Plus_Id_Equals_Times_Ann s   => Certify_Plus_Id_Equals_Times_Ann  (inr _ s)
  | Certify_Not_Plus_Id_Equals_Times_Ann => Certify_Not_Plus_Id_Equals_Times_Ann  
  end. 

Definition bs_certs_add_one : 
  ∀ {S : Type} (c : cas_constant),
     asg_certificates (S := S) -> bs_certificates (S := S) -> bs_certificates (S := (with_constant S))
:= λ {S} c ppS pS, 
{|
  bs_left_distributive_d      :=  bops_add_one_left_distributive_check c 
                                      (asg_idempotent_d ppS) 
                                      (bs_left_left_absorptive_d pS) 
                                      (bs_right_left_absorptive_d pS) 
                                      (bs_left_distributive_d pS) 
; bs_right_distributive_d     := bops_add_one_right_distributive_check c 
                                      (asg_idempotent_d ppS) 
                                      (bs_left_right_absorptive_d pS) 
                                      (bs_right_right_absorptive_d pS) 
                                      (bs_right_distributive_d pS) 
; bs_left_left_absorptive_d   := bops_add_one_left_left_absorptive_check c 
                                      (asg_idempotent_d ppS) 
                                      (bs_left_left_absorptive_d pS) 
; bs_left_right_absorptive_d  := bops_add_one_left_right_absorptive_check c 
                                      (asg_idempotent_d ppS) 
                                      (bs_left_right_absorptive_d pS) 
; bs_right_left_absorptive_d  := bops_add_one_right_left_absorptive_check c 
                                      (asg_idempotent_d ppS) 
                                      (bs_right_left_absorptive_d pS) 
; bs_right_right_absorptive_d := bops_add_one_right_right_absorptive_check c 
                                      (asg_idempotent_d ppS) 
                                      (bs_right_right_absorptive_d pS) 
|}. 

Definition id_ann_certs_add_one {S : Type} (c : cas_constant) : 
     @id_ann_certificates S -> @id_ann_certificates (with_constant S) 
:= λ pS,
{|
    id_ann_exists_plus_id_d       := bop_add_ann_exists_id_check (id_ann_exists_plus_id_d pS)
  ; id_ann_exists_plus_ann_d      := Certify_Exists_Ann (inl c) 
  ; id_ann_exists_times_id_d      := Certify_Exists_Id (inl c) 
  ; id_ann_exists_times_ann_d     := bop_add_id_exists_ann_check (id_ann_exists_times_ann_d pS)
  ; id_ann_plus_id_is_times_ann_d := bops_plus_id_equals_times_ann_check c (id_ann_plus_id_is_times_ann_d pS)
  ; id_ann_times_id_is_plus_ann_d := Certify_Times_Id_Equals_Plus_Ann (inl c) 
|}.
                                                                 

Definition bs_add_one : ∀ {S : Type}, bs (S := S) -> cas_constant -> bs (S := (with_constant S)) 
:= λ {S} bsS c, 
{| 
     bs_eqv         := eqv_add_constant (bs_eqv bsS) c 
   ; bs_plus        := bop_add_ann (bs_plus bsS) c
   ; bs_times       := bop_add_id (bs_times bsS) c
   ; bs_plus_certs  := asg_certs_add_ann c (eqv_witness (bs_eqv bsS)) (bs_plus_certs bsS) 
   ; bs_times_certs := msg_certs_add_id c (eqv_witness (bs_eqv bsS)) (eqv_new (bs_eqv bsS)) (bs_times_certs bsS)
   ; bs_id_ann_certs := id_ann_certs_add_one c (bs_id_ann_certs bsS)
   ; bs_certs       := bs_certs_add_one c (bs_plus_certs bsS) (bs_certs bsS)
   ; bs_ast         := Ast_bs_add_one (c, bs_ast bsS)
|}.

(* "dual" to code bops_add_zero_left_distributive_check *)

(*
Definition bops_add_one_left_distributive_dual_check : 
   ∀ {S : Type},  @check_left_distributive_dual S -> @check_left_distributive_dual (with_constant S) 
:= λ {S} dS,  
   match dS with 
   | Certify_Left_Distributive_Dual                    => Certify_Left_Distributive_Dual 
   | Certify_Not_Left_Distributive_Dual (s1, (s2, s3)) =>  Certify_Not_Left_Distributive_Dual (inr s1, (inr s2, inr _ s3))
   end. 


Definition lattice_certs_add_one : 
  ∀ {S : Type} (c : cas_constant),
     @lattice_certificates S -> @lattice_certificates (with_constant S)
:= λ {S} c pS, 
{|
  lattice_absorptive      := Assert_Left_Left_Absorptive
; lattice_absorptive_dual := Assert_Left_Left_Absorptive_Dual                              

; lattice_distributive_d      := bops_add_one_left_distributive_check c 
                                 Certify_Idempotent
                                 Certify_Left_Left_Absorptive
                                 Certify_Right_Left_Absorptive
                                 (lattice_distributive_d pS) 
; lattice_distributive_dual_d :=  bops_add_one_left_distributive_dual_check (lattice_distributive_dual_d pS)

|}. 


Definition lattice_add_one : ∀ (S : Type),  @lattice S -> cas_constant -> @lattice (with_constant S) 
:= λ S bsS c, 
{| 
     lattice_eqv         := eqv_add_constant (lattice_eqv bsS) c 
   ; lattice_join        := bop_add_ann (lattice_join bsS) c
   ; lattice_meet        := bop_add_id (lattice_meet bsS) c
   ; lattice_join_certs  := sg_CI_certs_add_ann c (lattice_join_certs bsS) 
   ; lattice_meet_certs  := sg_CI_certs_add_id c (lattice_meet_certs bsS) 
   ; lattice_certs       := lattice_certs_add_one c (lattice_certs bsS)
   ; lattice_join_ast    := Ast_bop_add_ann (c, lattice_join_ast bsS)                                                     
   ; lattice_meet_ast    := Ast_bop_add_id (c, lattice_meet_ast bsS)
   ; lattice_ast         := Ast_lattice_add_one (c, lattice_ast bsS)
|}. 


Definition distributive_lattice_certs_add_one : 
  ∀ {S : Type} (c : cas_constant), @distributive_lattice_certificates S -> @distributive_lattice_certificates (with_constant S)
:= λ {S} c dlc, 
{|
  distributive_lattice_absorptive      := Assert_Left_Left_Absorptive
; distributive_lattice_absorptive_dual := Assert_Left_Left_Absorptive_Dual                              
; distributive_lattice_distributive    := Assert_Left_Distributive 
|}. 

Definition distributive_lattice_add_one : ∀ (S : Type),  @distributive_lattice S -> cas_constant -> @distributive_lattice (with_constant S) 
:= λ S bsS c, 
{| 
     distributive_lattice_eqv         := eqv_add_constant (distributive_lattice_eqv bsS) c 
   ; distributive_lattice_join        := bop_add_ann (distributive_lattice_join bsS) c
   ; distributive_lattice_meet        := bop_add_id (distributive_lattice_meet bsS) c
   ; distributive_lattice_join_certs  := sg_CI_certs_add_ann c (distributive_lattice_join_certs bsS) 
   ; distributive_lattice_meet_certs  := sg_CI_certs_add_id c (distributive_lattice_meet_certs bsS) 
   ; distributive_lattice_certs       := distributive_lattice_certs_add_one c (distributive_lattice_certs bsS)
   ; distributive_lattice_join_ast    := Ast_bop_add_ann (c, distributive_lattice_join_ast bsS)                                            
   ; distributive_lattice_meet_ast    := Ast_bop_add_id (c, distributive_lattice_meet_ast bsS)
   ; distributive_lattice_ast         := Ast_distributive_lattice_add_one (c, distributive_lattice_ast bsS)
|}. 
  
*)
End CAS.

Section Verify.

Lemma bops_add_one_plus_id_equals_times_ann_check_correct : 
∀ (S : Type) (c : cas_constant) (rS : brel S) (s : S) (plusS timesS : binary_op S)
  (eqvS : eqv_proofs S rS) 
  (pS : bops_id_equals_ann_decidable S rS plusS timesS), 
  p2c_plus_id_equals_times_ann (with_constant S)
     (brel_sum brel_constant rS)
     (bop_add_ann plusS c)
     (bop_add_id timesS c)
     (bops_add_one_id_equals_ann_decide S rS 
        c plusS timesS s (A_eqv_reflexive S rS eqvS) pS) 
  =  bops_plus_id_equals_times_ann_check c (p2c_plus_id_equals_times_ann S rS plusS timesS pS).
Proof. intros S c rS s plusS timesS eqvS [ [i [P Q]] | R]; compute; reflexivity. Qed. 
 

Lemma bops_add_one_left_distributive_check_correct : 
  ∀ (S : Type) (c : cas_constant) (rS : brel S) (plusS timesS : binary_op S)
  (eqvS : eqv_proofs S rS)     
  (idmS_d : bop_idempotent_decidable S rS plusS) 
  (llaS_d : bops_left_left_absorptive_decidable S rS plusS timesS) 
  (rlaS_d : bops_right_left_absorptive_decidable S rS plusS timesS) 
  (ldS_d : bop_left_distributive_decidable S rS plusS timesS), 
  p2c_left_distributive (with_constant S)
     (brel_sum brel_constant rS)                                  
     (bop_add_ann plusS c)
     (bop_add_id timesS c)
     (bops_add_one_left_distributive_decide S rS c plusS timesS 
         (A_eqv_reflexive S rS eqvS) (A_eqv_symmetric S rS eqvS) idmS_d llaS_d rlaS_d ldS_d)
  = 
  bops_add_one_left_distributive_check c 
     (p2c_idempotent_check S rS plusS idmS_d) 
     (p2c_left_left_absorptive S rS plusS timesS llaS_d)
     (p2c_right_left_absorptive S rS plusS timesS rlaS_d)
     (p2c_left_distributive S rS plusS timesS ldS_d). 
Proof. intros S c rS plusS timesS eqvS
       [ idmS | [ s0 nidmS ] ] 
       [ llaS | [ [s1 s2] nllaS ] ]
       [ rlaS | [ [s6 s7] nrlaS ] ]
       [ ldS | [ [s3 [s4 s5]] nldS ] ]; 
       compute; reflexivity. 
Qed. 


Lemma bops_add_one_right_distributive_check_correct : 
  ∀ (S : Type) (c : cas_constant) (rS : brel S) (plusS timesS : binary_op S)
  (eqvS : eqv_proofs S rS)         
  (idmS_d : bop_idempotent_decidable S rS plusS) 
  (llaS_d : bops_left_right_absorptive_decidable S rS plusS timesS) 
  (rlaS_d : bops_right_right_absorptive_decidable S rS plusS timesS) 
  (ldS_d : bop_right_distributive_decidable S rS plusS timesS), 
  p2c_right_distributive (with_constant S)
     (brel_sum brel_constant rS)                                  
     (bop_add_ann plusS c)
     (bop_add_id timesS c)
     (bops_add_one_right_distributive_decide S rS c plusS timesS 
       (A_eqv_reflexive S rS eqvS) (A_eqv_symmetric S rS eqvS) idmS_d llaS_d rlaS_d ldS_d)
  = 
  bops_add_one_right_distributive_check c 
     (p2c_idempotent_check S rS plusS idmS_d) 
     (p2c_left_right_absorptive S rS plusS timesS llaS_d)
     (p2c_right_right_absorptive S rS plusS timesS rlaS_d)
     (p2c_right_distributive S rS plusS timesS ldS_d). 
Proof. intros S c rS plusS timesS eqvS
       [ idmS | [ s0 nidmS ] ] 
       [ llaS | [ [s1 s2] nllaS ] ]
       [ rlaS | [ [s6 s7] nrlaS ] ]
       [ ldS | [ [s3 [s4 s5]] nldS ] ]; 
       compute; reflexivity. 
Qed. 


Lemma bops_add_one_left_left_absorbtive_check_correct : 
  ∀ (S : Type) (c : cas_constant) (rS : brel S) (plusS timesS : binary_op S)
  (eqvS : eqv_proofs S rS)             
  (idmS_d : bop_idempotent_decidable S rS plusS) 
  (laS_d : bops_left_left_absorptive_decidable S rS plusS timesS), 
  p2c_left_left_absorptive (with_constant S)
     (brel_sum brel_constant rS)                                  
     (bop_add_ann plusS c)
     (bop_add_id timesS c)
     (bops_add_one_left_left_absorptive_decide S rS c plusS timesS (A_eqv_symmetric S rS eqvS) idmS_d laS_d)
  = 
  bops_add_one_left_left_absorptive_check c 
     (p2c_idempotent_check S rS plusS idmS_d) 
     (p2c_left_left_absorptive S rS plusS timesS laS_d).
Proof. intros S c rS plusS timesS eqvS 
       [ idmS | [ s0 nidmS ] ] 
       [ laS | [ [s1 s2] nlaS ] ]; 
       compute; reflexivity. 
Qed. 


Lemma bops_add_one_left_right_absorbtive_check_correct : 
  ∀ (S : Type) (c : cas_constant) (rS : brel S) (plusS timesS : binary_op S)
  (eqvS : eqv_proofs S rS)                 
  (idmS_d : bop_idempotent_decidable S rS plusS) 
  (laS_d : bops_left_right_absorptive_decidable S rS plusS timesS), 
  p2c_left_right_absorptive (with_constant S)
     (brel_sum brel_constant rS)                                  
     (bop_add_ann plusS c)
     (bop_add_id timesS c)
     (bops_add_one_left_right_absorptive_decide S rS c plusS timesS (A_eqv_symmetric S rS eqvS) idmS_d laS_d)
  = 
  bops_add_one_left_right_absorptive_check c 
     (p2c_idempotent_check S rS plusS idmS_d) 
     (p2c_left_right_absorptive S rS plusS timesS laS_d).
Proof. intros S c rS plusS timesS eqvS 
       [ idmS | [ s0 nidmS ] ] 
       [ laS | [ [s1 s2] nlaS ] ]; 
       compute; reflexivity. 
Qed. 

Lemma bops_add_one_right_left_absorbtive_check_correct : 
  ∀ (S : Type) (c : cas_constant) (rS : brel S) (plusS timesS : binary_op S)
  (eqvS : eqv_proofs S rS)                     
  (idmS_d : bop_idempotent_decidable S rS plusS) 
  (laS_d : bops_right_left_absorptive_decidable S rS plusS timesS), 
  p2c_right_left_absorptive (with_constant S)
     (brel_sum brel_constant rS)                                  
     (bop_add_ann plusS c)
     (bop_add_id timesS c)
     (bops_add_one_right_left_absorptive_decide S rS c plusS timesS (A_eqv_symmetric S rS eqvS) idmS_d laS_d)
  = 
  bops_add_one_right_left_absorptive_check c 
     (p2c_idempotent_check S rS plusS idmS_d) 
     (p2c_right_left_absorptive S rS plusS timesS laS_d).
Proof. intros S c rS plusS timesS eqvS 
       [ idmS | [ s0 nidmS ] ] 
       [ laS | [ [s1 s2] nlaS ] ]; 
       compute; reflexivity. 
Qed. 

Lemma bops_add_one_right_right_absorbtive_check_correct : 
  ∀ (S : Type) (c : cas_constant) (rS : brel S) (plusS timesS : binary_op S)
  (eqvS : eqv_proofs S rS)                     
  (idmS_d : bop_idempotent_decidable S rS plusS) 
  (laS_d : bops_right_right_absorptive_decidable S rS plusS timesS), 
  p2c_right_right_absorptive (with_constant S)
     (brel_sum brel_constant rS)                                  
     (bop_add_ann plusS c)
     (bop_add_id timesS c)
     (bops_add_one_right_right_absorptive_decide S rS c plusS timesS (A_eqv_symmetric S rS eqvS) idmS_d laS_d)
  = 
  bops_add_one_right_right_absorptive_check c 
     (p2c_idempotent_check S rS plusS idmS_d) 
     (p2c_right_right_absorptive S rS plusS timesS laS_d).
Proof. intros S c rS plusS timesS eqvS 
       [ idmS | [ s0 nidmS ] ] 
       [ laS | [ [s1 s2] nlaS ] ]; 
       compute; reflexivity. 
Qed. 

Lemma  correct_bs_certs_add_one : 
  ∀ (S : Type) (c : cas_constant) (s : S) (rS : brel S) 
    (plusS timesS : binary_op S) 
    (eqvS : eqv_proofs S rS)
    (sgS : asg_proofs S rS plusS) 
    (bsS : bs_proofs S rS plusS timesS), 
    P2C_bs (with_constant S) 
       (brel_sum brel_constant rS) 
       (bop_add_ann plusS c) 
       (bop_add_id timesS c) 
       (bs_proofs_add_one S rS c plusS timesS s eqvS sgS bsS)
    =
    bs_certs_add_one c (P2C_asg S rS plusS sgS) (P2C_bs S rS plusS timesS bsS). 
Proof. intros S c s rS plusS timesS eqvS sgS bsS. 
       unfold bs_certs_add_one, bs_proofs_add_one, P2C_bs, P2C_asg; simpl. 
       rewrite bops_add_one_left_distributive_check_correct. 
       rewrite bops_add_one_right_distributive_check_correct. 
       rewrite bops_add_one_left_left_absorbtive_check_correct .
       rewrite bops_add_one_left_right_absorbtive_check_correct. 
       rewrite bops_add_one_right_left_absorbtive_check_correct. 
       rewrite bops_add_one_right_right_absorbtive_check_correct. 
       reflexivity. 
Defined. 


Lemma  correct_id_ann_certs_add_one : 
  ∀ (S : Type) (c : cas_constant) (rS : brel S) (s : S) 
    (plusS timesS : binary_op S) 
    (eqvS : eqv_proofs S rS)
    (bsS : id_ann_proofs S rS plusS timesS), 
    P2C_id_ann (with_constant S) 
       (brel_sum brel_constant rS) 
       (bop_add_ann plusS c) 
       (bop_add_id timesS c) 
       (id_ann_proofs_add_one S rS c plusS timesS s eqvS bsS)
    =
    id_ann_certs_add_one c (P2C_id_ann S rS plusS timesS bsS). 
Proof. intros S c rS s plusS timesS eqvS bsS.
       unfold id_ann_certs_add_one, id_ann_proofs_add_one, P2C_id_ann; simpl.        
       rewrite bops_add_one_plus_id_equals_times_ann_check_correct.
       rewrite bop_add_id_exists_ann_check_correct.
       rewrite bop_add_ann_exists_id_check_correct.        
       reflexivity.
Qed.        
       
Theorem correct_bs_add_one : ∀ (S : Type) (bsS: A_bs S) (c : cas_constant), 
   bs_add_one (A2C_bs S bsS) c 
   =
   A2C_bs (with_constant S) (A_bs_add_one S bsS c). 
Proof. intros S bsS c. 
       unfold bs_add_one, A_bs_add_one, A2C_bs; simpl. 
       rewrite correct_eqv_add_constant. 
       rewrite <- correct_asg_certs_add_ann. 
       rewrite <- correct_msg_certs_add_id. 
       rewrite correct_bs_certs_add_one.
       rewrite correct_id_ann_certs_add_one.        
       reflexivity. 
Qed. 

(*
Lemma bops_add_one_left_distributive_dual_check_correct : 
  ∀ (S : Type) (c : cas_constant) (rS : brel S) (plusS timesS : binary_op S)
    (eqvS : eqv_proofs S rS)
  (idmS_d : bop_idempotent_decidable S rS timesS) 
  (llaS_d : bops_left_left_absorptive_decidable S rS timesS plusS ) 
  (rlaS_d : bops_right_left_absorptive_decidable S rS timesS plusS ) 
  (ldS_d : bop_left_distributive_decidable S rS timesS plusS ),     
  p2c_left_distributive_dual (with_constant S)
     (brel_sum brel_constant rS)
     (bop_add_ann plusS c)
     (bop_add_id timesS c)                        
     (bops_add_zero_left_distributive_decide S rS c timesS plusS 
         (A_eqv_reflexive S rS eqvS) ldS_d)
  = 
  bops_add_one_left_distributive_dual_check 
     (p2c_left_distributive_dual S rS plusS timesS ldS_d). 
Proof. intros S c rS plusS timesS eqvS
       [ idmS | [ s0 nidmS ] ] 
       [ llaS | [ [s1 s2] nllaS ] ]
       [ rlaS | [ [s6 s7] nrlaS ] ]
       [ ldS | [ [s3 [s4 s5]] nldS ] ]; 
       compute; reflexivity. 
Qed. 

(* broken abstraction below! *) 
Lemma  correct_lattice_certs_add_one : 
  ∀ (S : Type) (c : cas_constant) (rS : brel S) 
    (join meet : binary_op S) 
    (eqvS : eqv_proofs S rS)
    (pjoin : sg_CI_proofs S rS join)
    (pmeet : sg_CI_proofs S rS meet)     
    (latticeS : lattice_proofs S rS join meet), 
    P2C_lattice (with_constant S) 
       (brel_sum brel_constant rS) 
       (bop_add_ann join c) 
       (bop_add_id meet c) 
       (lattice_proofs_add_one S rS c join meet eqvS pjoin pmeet latticeS)
    =
    lattice_certs_add_one c (P2C_lattice S rS join meet latticeS). 
Proof. intros S c rS join meet eqvS pjoin pmeet latticeS. 
       unfold lattice_certs_add_one, lattice_proofs_add_one, P2C_lattice, P2C_sg; simpl. 
       rewrite bops_add_one_left_distributive_dual_check_correct.
       rewrite bops_add_one_left_distributive_check_correct. simpl. 
       reflexivity.
       (* ugly!  Broken abstraction! where? *)
       destruct pmeet. left; auto.
       destruct latticeS. left; auto.        
       destruct latticeS. left; auto.
       destruct eqvS, pmeet, pjoin.  
       apply bops_left_right_absorptive_implies_right_left; auto.
       apply bops_left_left_absorptive_implies_left_right; auto.        
Qed. 

Theorem correct_lattice_add_one : ∀ (S : Type) (latticeS: A_lattice S) (c : cas_constant), 
   lattice_add_one S (A2C_lattice S latticeS) c 
   =
   A2C_lattice (with_constant S) (A_lattice_add_one S latticeS c). 
Proof. intros S latticeS c. 
       unfold lattice_add_one, A_lattice_add_one, A2C_lattice; simpl. 
       rewrite correct_eqv_add_constant. 
       rewrite <- correct_sg_CI_certs_add_ann. 
       rewrite <- correct_sg_CI_certs_add_id. 
       rewrite correct_lattice_certs_add_one. 
       reflexivity. 
Qed. 


Lemma  correct_distributive_lattice_certs_add_one : 
  ∀ (S : Type) (rS : brel S) (join meet : binary_op S) (c:  cas_constant) 
    (eqvS : eqv_proofs S rS) 
    (pjoin : sg_CI_proofs S rS join)
    (pmeet : sg_CI_proofs S rS meet)
    (dlp : distributive_lattice_proofs S rS join meet), 

    P2C_distributive_lattice _ _ _ _ (distributive_lattice_proofs_add_one S rS c join meet eqvS pjoin pmeet dlp) 
    =
    distributive_lattice_certs_add_one c (P2C_distributive_lattice S rS join meet dlp). 
Proof. intros S rS join meet c eqvS pjoin pmeet dlp. compute. reflexivity. Qed.

Theorem correct_distributive_lattice_add_one : ∀ (S : Type) (distributive_latticeS: A_distributive_lattice S) (c : cas_constant), 
   distributive_lattice_add_one S (A2C_distributive_lattice S distributive_latticeS) c 
   =
   A2C_distributive_lattice (with_constant S) (A_distributive_lattice_add_one S distributive_latticeS c). 
Proof. intros S distributive_latticeS c. 
       unfold distributive_lattice_add_one, A_distributive_lattice_add_one, A2C_distributive_lattice; simpl. 
       rewrite correct_eqv_add_constant. 
       rewrite <- correct_sg_CI_certs_add_ann. 
       rewrite <- correct_sg_CI_certs_add_id. 
       rewrite correct_distributive_lattice_certs_add_one. 
       reflexivity. 
Qed. 
  
*) 
End Verify.   
  
