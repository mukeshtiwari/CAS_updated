Require Import Coq.Strings.String.

Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.

Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.

Require Import CAS.coq.or.properties.
Require Import CAS.coq.or.structures.
Require Import CAS.coq.or.theory.
Require Import CAS.coq.or.from_sg.

Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures.


Require Import CAS.coq.bs.properties.
Require Import CAS.coq.bs.structures.

Require Import CAS.coq.or_sg.properties.
Require Import CAS.coq.or_sg.structures.
Require Import CAS.coq.or_sg.theory.


Section Theory.

Variable S  : Type.
Variable eq : brel S.
Variable refS : brel_reflexive S eq.
Variable symS : brel_symmetric S eq. 
Variable trnS : brel_transitive S eq. 


Variable plus     : binary_op S.
Variable times     : binary_op S.

Variable congP : bop_congruence S eq plus.
Variable assoP : bop_associative S eq plus.
Variable idemP : bop_idempotent S eq plus.
Variable commP : bop_commutative S eq plus.

Variable congT : bop_congruence S eq times.

Definition left_lte := brel_lte_left eq plus.
Definition right_lte := brel_lte_right eq plus.

Notation "a [=] b"   := (eq a b = true)          (at level 15).
Notation "a [+] b"   := (plus a b)          (at level 15).
Notation "a [*] b"   := (times a b)          (at level 15).       

(*

(* monotonicity *) 

Lemma os_lte_left_left_monotone : os_left_monotone (brel_lte_left eq bS) bS.
Proof. intros s t u. compute. intro H.
       assert (F0 := idemS s). apply symS in F0. 
       assert (F1 := congS _ _ _ _ F0 H).  
       assert (F2 : (s (+) s) (+) (t (+) u) == (s (+) t) (+) (s (+) u)).
          (* (s (+) s) (+) (t (+) u)
             assoc = s (+) (s (+) (t (+) u)) 
             assoc = s (+) ((s (+) t) (+) u) 
             comm  = s (+) ((t (+) s) (+) u) 
             assoc = s (+) (t (+) (s (+) u)) 
             assoc = (s (+) t) (+) (s (+) u)
          *) 
          assert (F4 := assoS s s (t (+) u)).           
          assert (F5 := assoS s t u). apply symS in F5.
          assert (F6 := congS _ _ _ _ (refS s) F5).          
          assert (F7 := trnS _ _ _ F4 F6). apply symS in F5.
          assert (F8 := commS s t). 
          assert (F9 := congS _ _ _ _ (refS s) (congS _ _ _ _ F8 (refS u))). 
          assert (F10 := trnS _ _ _ F7 F9).
          assert (F11 := assoS t s u).
          assert (F12 := congS _ _ _ _ (refS s) F11). 
          assert (F13 := trnS _ _ _ F10 F12).          
          assert (F14 := assoS s t (s (+) u)). apply symS in F14. 
          exact (trnS _ _ _ F13 F14).
       exact (trnS _ _ _ F1 F2). 
Qed. 

Lemma os_lte_right_left_monotone : os_left_monotone (brel_lte_right eq bS) bS.
Proof. intros s t u. compute. intro H.
       assert (F0 := os_lte_left_left_monotone s u t). compute in F0.
       assert (F1 := commS (s (+) u) (s (+) t)).
       assert (F2 := commS t u).
       assert (F3 := trnS _ _ _ H F2). 
       exact (trnS _ _ _ (F0 F3) F1). 
Qed.

Lemma os_lte_left_right_monotone : os_right_monotone (brel_lte_left eq bS) bS.
Proof. intros s t u. compute. intro H. 
       assert (F0 := os_lte_left_left_monotone s t u). compute in F0.
       assert (F1 := F0 H). 
       assert (F2 := commS t s).
       assert (F3 := commS u s).        
       assert (F4 := trnS _ _ _ F2 F1).
       assert (F5 := congS _ _ _ _ F2 F3). apply symS in F5.
       exact (trnS _ _ _ F4 F5). 
Qed. 

Lemma os_lte_right_right_monotone : os_right_monotone (brel_lte_right eq bS) bS.
Proof. intros s t u. compute. intro H.
       assert (F0 := os_lte_left_right_monotone s u t). compute in F0.
       assert (F1 := commS (u (+) s) (t (+) s)).
       assert (F2 := commS t u).
       assert (F3 := trnS _ _ _ H F2). 
       exact (trnS _ _ _ (F0 F3) F1). 
Qed.

(* bottoms *)

(* Note: New properties needed! *)

Definition os_bottom_equals_ann {S : Type} (r lte : brel S) (b : binary_op S)
:= { i : S & (brel_is_bottom S lte i) * (bop_is_ann S r b i)}.

Definition os_top_equals_id {S : Type} (r lte : brel S) (b : binary_op S)
  := { i : S & (brel_is_top S lte i) * (bop_is_id S r b i)}. 


Lemma os_lte_left_bottom_equals_ann (annS : bop_exists_ann S eq bS) : os_bottom_equals_ann eq (brel_lte_left eq bS) bS.
Proof. destruct annS as [ann P]. exists ann. compute. compute in P. split; auto. 
       intro s. destruct (P s) as [A B]. apply symS. exact A. 
Defined. 

Lemma os_lte_left_top_equals_id (idS : bop_exists_id S eq bS) : os_top_equals_id eq (brel_lte_left eq bS) bS.
Proof. destruct idS as [id P]. exists id. compute. compute in P. split; auto. 
       intro s. destruct (P s) as [A B]. apply symS. exact B. 
Defined. 

Lemma os_lte_right_bottom_equals_id (idS : bop_exists_id S eq bS) : os_exists_bottom_id_equal eq (brel_lte_right eq bS) bS.
Proof. destruct idS as [id P]. exists id. compute. compute in P. split; auto. 
       intro s. destruct (P s) as [A B]. apply symS. exact A. 
Defined. 

Lemma os_lte_right_top_equals_ann (annS : bop_exists_ann S eq bS) : os_exists_top_ann_equal eq (brel_lte_right eq bS) bS.
Proof. destruct annS as [ann P]. exists ann. compute. compute in P. split; auto. 
       intro s. destruct (P s) as [A B]. apply symS. exact B. 
Defined. 


*) 




Lemma os_from_bs_left_left_monotone
      (LD : A_bs_left_distributive eq plus times) : os_left_monotone left_lte times.
Proof. intros a b c. compute.
       (* b [=] (b [+] c) → (a [*] b) [=] ((a [*] b) [+] (a [*] c)) *) 
       intro A. 
       assert (B := LD a b c).
       assert (C : (a [*] b) [=] (a [*] (b [+] c))).
          apply (congT _ _ _ _ (refS a) A). 
       assert (D := trnS _ _ _ C B).
       exact D. 
Qed.        

Lemma os_from_bs_left_not_left_monotone
      (LD : A_bs_not_left_distributive eq plus times) : os_not_left_monotone left_lte times.
Proof. destruct LD as [[a [b c]] A]. 
       exists (a, (b, c)). compute.
(*  b [=] (b [+] c) * (eq (a [*] b) ((a [*] b) [+] (a [*] c)) = false) *)       
Admitted.

Lemma os_from_bs_right_left_monotone
      (LD : A_bs_left_distributive eq plus times) : os_left_monotone right_lte times.
Proof. intros a b c. compute.
       (* c [=] (b [+] c) → (a [*] c) [=] ((a [*] b) [+] (a [*] c)) *)
       intro A. 
       assert (B := LD a b c).
       assert (C : (a [*] c) [=] (a [*] (b [+] c))).
          apply (congT _ _ _ _ (refS a) A). 
       assert (D := trnS _ _ _ C B).
       exact D. 
Qed.        

Lemma os_from_bs_left_right_monotone
      (RD : A_bs_right_distributive eq plus times) : os_right_monotone left_lte times.
Proof. intros a b c. compute.
       (* b [=] (b [+] c) → (b [*] a) [=] ((b [*] a) [+] (c [*] a)) *) 
       intro A.
       assert (B := RD a b c).
       assert (C : (b [*] a) [=] ((b [+] c) [*] a)).
          apply (congT _ _ _ _ A (refS a)). 
       assert (D := trnS _ _ _ C B).
       exact D. 
Qed.        

Lemma os_from_bs_left_not_right_monotone
      (RD : A_bs_not_right_distributive eq plus times) : os_not_right_monotone left_lte times.
Proof. destruct RD as [[a [b c]] A]. 
       exists (a, (b, c)). compute.
(*
    b [=] (b [+] c) * (eq (b [*] a) ((b [*] a) [+] (c [*] a)) = false)
*)       
Admitted.


Lemma os_from_bs_right_right_monotone
      (RD : A_bs_right_distributive eq plus times) : os_right_monotone right_lte times.
Proof. intros a b c. compute.
       (* c [=] (b [+] c) → (c [*] a) [=] ((b [*] a) [+] (c [*] a)) *) 
       intro A.
       assert (B := RD a b c).
       assert (C : (c [*] a) [=] ((b [+] c) [*] a)).
          apply (congT _ _ _ _ A (refS a)). 
       assert (D := trnS _ _ _ C B).
       exact D. 
Qed.        


Lemma os_from_bs_left_increasing : 
   A_bs_left_absorptive eq plus times -> os_left_increasing left_lte times.
Proof. intros A s t. compute. auto. Qed.

Lemma os_from_bs_not_left_increasing : 
   A_bs_not_left_absorptive eq plus times -> os_not_left_increasing left_lte times.
Proof. intros [[s t] A]. exists (s, t). compute. auto. Qed. 

Lemma os_from_bs_right_increasing : 
   A_bs_right_absorptive eq plus times -> os_right_increasing left_lte times.
Proof. intros A s t. compute. auto. Qed.

Lemma os_from_bs_not_right_increasing : 
   A_bs_not_right_absorptive eq plus times -> os_not_right_increasing left_lte times.
Proof. intros [[s t] A]. exists (s, t). compute. auto. Qed.


(*  need anti-absorptive, left_decreasing, ... ? 


Lemma os_from_bs_right_left_increasing : 
   bops_right_right_absorptive S eq plus times -> os_left_increasing right_lte times.
Proof. intros A s t. compute.
(*         (s [*] t) [=] (s [+] (s [*] t))  *) 
Admitted. 

Lemma os_from_bs_right_right_increasing : 
   bops_left_right_absorptive S eq plus times -> os_right_increasing right_lte times.
Proof. intros A s t. compute.
(*   (t [*] s) [=] (s [+] (t [*] s))  *)
Admitted. 
*) 



Lemma os_from_bs_left_structly_increasing : 
   A_bs_left_absorptive eq plus times -> os_left_strictly_increasing left_lte times.
Proof. intros A s t. compute. split.
       (* need s [=] (s [+] (s [*] t))  *) 
       auto. 
       (* need eq (s [*] t) ((s [*] t) [+] s) = false 
        perhaps s [=] (s [+] (s [*] t))  * (s <> (s [*] t)) would be enough. 
       *)        
       admit. 
Admitted. 


Lemma os_from_bs_left_exists_top_ann_equal
      (P : A_bs_exists_id_ann_equal  eq plus times) :
           A_os_exists_top_ann_equal eq left_lte times.
Proof. destruct P as [a [A B]].
       exists a; split; auto.
       apply brel_lte_left_is_top; auto.
Defined.

Lemma os_from_bs_left_exists_top_ann_not_equal
      (P : A_bs_exists_id_ann_not_equal eq plus times) :
           A_os_exists_top_ann_not_equal eq left_lte times.
Proof. destruct P as [[a b] [[A B] C]].
       exists (a, b). split; auto. split; auto. 
       apply brel_lte_left_is_top; auto.
Defined. 

Lemma os_from_bs_left_exists_bottom_id_equal
      (P : A_bs_exists_id_ann_equal eq times plus) :
           A_os_exists_bottom_id_equal eq left_lte times.
Proof. destruct P as [a [A B]].
       exists a; split; auto.
       apply brel_lte_left_is_bottom; auto.
Defined. 

Lemma os_from_bs_left_exists_bottom_id_not_equal
      (P : A_bs_exists_id_ann_not_equal eq times plus) :
           A_os_exists_bottom_id_not_equal eq left_lte times.
Proof. destruct P as [[a b] [[A B] C]].
       exists (b, a); split; auto. split; auto. 
       apply brel_lte_left_is_bottom; auto.
       case_eq(eq b a); intro H; auto. apply symS in H.
       rewrite H in C. discriminate C. 
Defined. 


End Theory.


(*

Section ACAS.


Section Decide.

Variables (S : Type) (eq : brel S) (eqvP : eqv_proofs S eq) (plus times : binary_op S). 
 
Definition os_from_bs_left_left_increasing_decide 
  (d : bops_left_left_absorptive_decidable S eq plus times) :
       os_left_increasing_decidable (brel_lte_left eq plus) times := 
   match d with 
   | inl li  => inl (os_from_bs_left_left_increasing S eq plus times li)
   | inr nli => inr (os_from_bs_left_not_left_increasing S eq plus times nli)
   end. 

Definition os_from_bs_left_right_increasing_decide 
  (d : bops_left_right_absorptive_decidable S eq plus times) :
       os_right_increasing_decidable (brel_lte_left eq plus) times := 
   match d with 
   | inl ri  => inl (os_from_bs_left_right_increasing S eq plus times ri)
   | inr nri => inr (os_from_bs_left_not_right_increasing S eq plus times nri)
   end.

Definition os_from_bs_left_exists_top_ann_equal_decidable
       (plus_comm : bop_commutative S eq plus)
       (P : exists_id_ann_decidable S eq plus times) :
            os_exists_top_ann_decidable S eq (brel_lte_left eq plus) times :=
  let sym := A_eqv_symmetric _ _ eqvP in
  let trn := A_eqv_transitive _ _ eqvP in   
  match P with 
  | Id_Ann_Proof_None _ _ _ _ (no_id, no_ann)         =>
       Top_Ann_Proof_None _ _ _ _ (brel_lte_left_not_exists_top S eq sym trn plus plus_comm no_id, no_ann) 
  | Id_Ann_Proof_Id_None  _ _ _ _ (exists_id, no_ann) =>
       Top_Ann_Proof_Top_None _ _ _ _ (brel_lte_left_exists_top S eq sym plus exists_id, no_ann)
  | Id_Ann_Proof_None_Ann _ _ _ _ (no_id, exists_ann) =>
       Top_Ann_Proof_None_Ann _ _ _ _ (brel_lte_left_not_exists_top S eq sym trn plus plus_comm no_id, exists_ann) 
  | Id_Ann_Proof_Equal _ _ _ _ id_ann_eq              =>
       Top_Ann_Proof_Equal _ _ _ _ (os_from_bs_left_exists_top_ann_equal S eq sym plus times id_ann_eq) 
  | Id_Ann_Proof_Not_Equal _ _ _ _ id_ann_not_eq      =>
       Top_Ann_Proof_Not_Equal _ _ _ _ (os_from_bs_left_exists_top_ann_not_equal S eq sym plus times id_ann_not_eq) 
end.


Definition os_from_bs_left_exists_bottom_id_equal_decidable
       (plus_comm : bop_commutative S eq plus)
       (P : exists_id_ann_decidable S eq times plus) :
            os_exists_bottom_id_decidable S eq (brel_lte_left eq plus) times :=
  let sym := A_eqv_symmetric _ _ eqvP in
  let trn := A_eqv_transitive _ _ eqvP in   
  match P with 
  | Id_Ann_Proof_None _ _ _ _ (no_id, no_ann)         =>
       Bottom_Id_Proof_None _ _ _ _ (brel_lte_left_not_exists_bottom S eq sym trn plus plus_comm no_ann, no_id) 
  | Id_Ann_Proof_Id_None  _ _ _ _ (exists_id, no_ann) =>
       Bottom_Id_Proof_None_Id _ _ _ _ (brel_lte_left_not_exists_bottom S eq sym trn plus plus_comm no_ann, exists_id)
  | Id_Ann_Proof_None_Ann _ _ _ _ (no_id, exists_ann) =>
       Bottom_Id_Proof_Bottom_None _ _ _ _ (brel_lte_left_exists_bottom S eq sym plus exists_ann, no_id)    
  | Id_Ann_Proof_Equal _ _ _ _ id_ann_eq              =>
       Bottom_Id_Proof_Equal _ _ _ _ (os_from_bs_left_exists_bottom_id_equal S eq sym plus times id_ann_eq) 
  | Id_Ann_Proof_Not_Equal _ _ _ _ id_ann_not_eq      =>
       Bottom_Id_Proof_Not_Equal _ _ _ _ (os_from_bs_left_exists_bottom_id_not_equal S eq sym plus times id_ann_not_eq) 
end.
  
End Decide.

Section Proofs. 

Variables (S : Type) (eq : brel S) (eqvP : eqv_proofs S eq) (plus times : binary_op S).

Definition os_bs_left_bottom_top_proofs_from_id_ann_proofs
           (plus_comm : bop_commutative S eq plus)
           (P : id_ann_proofs S eq plus times) :
                os_bottom_top_proofs S eq (brel_lte_left eq plus) times := 
{|
  A_bottom_top_bottom_id_d :=
    os_from_bs_left_exists_bottom_id_equal_decidable S eq eqvP plus times plus_comm (A_id_ann_times_plus_d _ _ _ _ P)
; A_bottom_top_top_ann_d   :=
    os_from_bs_left_exists_top_ann_equal_decidable S eq eqvP plus times plus_comm (A_id_ann_plus_times_d _ _ _ _ P)
|}.


Definition os_bs_left_bounded_proofs_from_bs_bounded_proofs
           (P : dually_bounded_proofs S eq plus times) :
                os_bounded_proofs S eq (brel_lte_left eq plus) times := 
let sym := A_eqv_symmetric _ _ eqvP in
{|
  A_bounded_bottom_id :=
      os_from_bs_left_exists_bottom_id_equal S eq sym plus times (A_bounded_times_id_is_plus_ann _ _ _ _ P) 
; A_bounded_top_ann   :=
      os_from_bs_left_exists_top_ann_equal S eq sym plus times (A_bounded_plus_id_is_times_ann _ _ _ _ P)     
|}.

Definition os_bs_left_bottom_is_id_proofs_from_pann_is_tid_proofs
           (plus_comm : bop_commutative S eq plus)           
           (P : pann_is_tid_proofs S eq plus times) :
             os_bottom_is_id_proofs S eq (brel_lte_left eq plus) times := 
let sym := A_eqv_symmetric _ _ eqvP in
{|
  A_bottom_is_id           :=
      os_from_bs_left_exists_bottom_id_equal S eq sym plus times (A_pann_is_tid_times_plus _ _ _ _ P)     
; A_bottom_is_id_top_ann_d :=
    os_from_bs_left_exists_top_ann_equal_decidable S eq eqvP plus times plus_comm (A_pann_is_tid_plus_times_d _ _ _ _ P)      
|}.

Definition os_bs_left_top_is_ann_proofs_from_pid_is_tann_proofs
           (plus_comm : bop_commutative S eq plus)           
           (P : pid_is_tann_proofs S eq plus times) :
             os_top_is_ann_proofs S eq (brel_lte_left eq plus) times := 
let sym := A_eqv_symmetric _ _ eqvP in           
{|
  A_top_is_ann_bottom_id_d :=
    os_from_bs_left_exists_bottom_id_equal_decidable S eq eqvP plus times plus_comm (A_pid_is_tann_times_plus_d _ _ _ _ P)    
; A_top_is_ann             :=
      os_from_bs_left_exists_top_ann_equal S eq sym plus times (A_pid_is_tann_plus_times _ _ _ _ P)           
|}.

Definition os_bs_left_monotone_increasing_proofs_from_dioid_proofs
           (times_cong : bop_congruence S eq times)
           (P : dioid_proofs S eq plus times) :
              os_monotone_increasing_proofs S (brel_lte_left eq plus) times := 
let ref := A_eqv_reflexive _ _ eqvP in   
let trn := A_eqv_transitive _ _ eqvP in   
let LD  := A_dioid_left_distributive _ _ _ _ P in
let RD  := A_dioid_right_distributive _ _ _ _ P in
let LLA := A_dioid_left_left_absorptive _ _ _ _ P in
let LRA := A_dioid_left_right_absorptive _ _ _ _ P in
{|
  A_mono_inc_left_monotonic   := os_from_bs_left_left_monotone S eq ref trn plus times times_cong LD 
; A_mono_inc_right_monotonic  := os_from_bs_left_right_monotone S eq ref trn plus times times_cong RD

; A_mono_inc_left_increasing  := os_from_bs_left_left_increasing S eq plus times LLA 
; A_mono_inc_right_increasing := os_from_bs_left_right_increasing S eq plus times LRA 
|}. 
  
End Proofs.

Section Combinators.

Definition A_posg_from_pre_dioid (S :Type) (D : A_pre_dioid S) : A_monotone_increasing_posg S :=
let eqv        := A_pre_dioid_eqv _ D in
let eq         := A_eqv_eq _ eqv in
let eqvP       := A_eqv_proofs _ eqv in
let plus       := A_pre_dioid_plus _ D in
let plusP      := A_pre_dioid_plus_proofs _ D in
let plus_comm  := A_sg_CI_commutative _ _ _ plusP in 
let times      := A_pre_dioid_times _ D in
let timesP     := A_pre_dioid_times_proofs _ D in
let times_cong := A_sg_congruence _ _ _ timesP in 
{|
  A_miposg_eqv          := eqv 
; A_miposg_lte          := brel_lte_left eq plus
; A_miposg_times        := times 
; A_miposg_lte_proofs   := po_proofs_from_sg_CI_left_proofs S eq eqvP plus plusP 
; A_miposg_times_proofs := timesP 
; A_miposg_top_bottom   := os_bs_left_bottom_top_proofs_from_id_ann_proofs S eq eqvP plus times plus_comm (A_pre_dioid_id_ann_proofs _ D)
; A_miposg_proofs       := os_bs_left_monotone_increasing_proofs_from_dioid_proofs S eq eqvP plus times times_cong (A_pre_dioid_proofs _ D)
; A_miposg_ast          := Ast_os_from_bs_left (A_pre_dioid_ast _ D) 
|}.


Definition A_posg_from_dioid (S :Type) (D : A_dioid S) : A_bounded_monotone_increasing_posg S :=
let eqv        := A_dioid_eqv _ D in
let eq         := A_eqv_eq _ eqv in
let eqvP       := A_eqv_proofs _ eqv in
let plus       := A_dioid_plus _ D in
let times      := A_dioid_times _ D in
let timesP     := A_dioid_times_proofs _ D in
let times_cong := A_sg_congruence _ _ _ timesP in 
{|
  A_bmiposg_eqv          := eqv 
; A_bmiposg_lte          := brel_lte_left eq plus
; A_bmiposg_times        := times 
; A_bmiposg_lte_proofs   := po_proofs_from_sg_CI_left_proofs S eq eqvP plus (A_dioid_plus_proofs _ D)
; A_bmiposg_times_proofs := timesP 
; A_bmiposg_top_bottom   := os_bs_left_bounded_proofs_from_bs_bounded_proofs S eq eqvP plus times (A_dioid_id_ann_proofs _ D)
; A_bmiposg_proofs       := os_bs_left_monotone_increasing_proofs_from_dioid_proofs S eq eqvP plus times times_cong (A_dioid_proofs _ D)
; A_bmiposg_ast          := Ast_os_from_bs_left (A_dioid_ast _ D)
|}.


End Combinators.   
  
End ACAS.

Section AMCAS.

Local Open Scope string_scope.
Local Open Scope list_scope.     

Definition A_mcas_os_from_bs_left  (S : Type) (A : A_bs_mcas S) :=
  match A_bs_classify _ A with
  | A_BS_dioid _ C => A_OS_bounded_monotone_increasing_posg _ (A_posg_from_dioid _ C)
  | _ => A_OS_Error _ ("mcas_posg_from_bs_left : this combinator (currently) requires a dioid" :: nil) 
  end. 

End AMCAS.   

Section CAS.


Section Decide.

 
Definition os_from_bs_left_left_increasing_certify {S : Type}
  (d : @check_left_left_absorptive S) : @check_left_increasing S := 
   match d with 
   | Certify_Left_Left_Absorptive          => Certify_Left_Increasing 
   | Certify_Not_Left_Left_Absorptive trip => Certify_Not_Left_Increasing trip
   end. 


Definition os_from_bs_left_right_increasing_certify {S : Type}
  (d : @check_left_right_absorptive S) : @check_right_increasing S := 
   match d with 
   | Certify_Left_Right_Absorptive          => Certify_Right_Increasing 
   | Certify_Not_Left_Right_Absorptive trip => Certify_Not_Right_Increasing trip
   end. 


Definition os_from_bs_left_exists_top_ann_equal_certify {S : Type} 
       (P : @exists_id_ann_certificate S) : @os_exists_top_ann_certificate S :=
match P with 
  | Id_Ann_Cert_None                => Top_Ann_Cert_None 
  | Id_Ann_Cert_Id_None  top        => Top_Ann_Cert_Top_None top 
  | Id_Ann_Cert_None_Ann ann        => Top_Ann_Cert_None_Ann ann 
  | Id_Ann_Cert_Equal top_ann       => Top_Ann_Cert_Equal top_ann 
  | Id_Ann_Cert_Not_Equal (top,ann) => Top_Ann_Cert_Not_Equal (top, ann) 
end.


Definition os_from_bs_left_exists_bottom_id_equal_certify {S : Type} 
       (P : @exists_id_ann_certificate S) : @os_exists_bottom_id_certificate S := 
match P with 
  | Id_Ann_Cert_None                => Bottom_Id_Cert_None 
  | Id_Ann_Cert_Id_None id          => Bottom_Id_Cert_None_Id id 
  | Id_Ann_Cert_None_Ann ann        => Bottom_Id_Cert_Bottom_None ann 
  | Id_Ann_Cert_Equal id_ann        => Bottom_Id_Cert_Equal id_ann 
  | Id_Ann_Cert_Not_Equal (id, ann) => Bottom_Id_Cert_Not_Equal (id, ann) 
end.
  
End Decide.

Section Certs. 

Definition os_bs_left_bottom_top_certs_from_id_ann_certs {S : Type} 
           (P : @id_ann_certificates S ) : @os_bottom_top_certs S := 
{|
  bottom_top_bottom_id_d := os_from_bs_left_exists_bottom_id_equal_certify (id_ann_times_plus_d P)
; bottom_top_top_ann_d   := os_from_bs_left_exists_top_ann_equal_certify (id_ann_plus_times_d P)
|}.


Definition os_bs_left_bounded_certs_from_bs_bounded_certs {S : Type} 
           (P : @dually_bounded_certificates S) : @os_bounded_certs S := 
{|
  bounded_bottom_id := match bounded_times_id_is_plus_ann P with
                       | Assert_Exists_Id_Ann_Equal id_ann => Assert_Os_Exists_Bottom_Id_Equal id_ann
                       end 
; bounded_top_ann   := match bounded_plus_id_is_times_ann P with
                       | Assert_Exists_Id_Ann_Equal id_ann => Assert_Os_Exists_Top_Ann_Equal id_ann
                       end 
|}.

Definition os_bs_left_bottom_is_id_certs_from_pann_is_tid_certs {S : Type} 
           (P : @pann_is_tid_certificates S) : @os_bottom_is_id_certs S := 
{|
  bottom_is_id           := match pann_is_tid_times_plus P with
                            | Assert_Exists_Id_Ann_Equal id_ann => Assert_Os_Exists_Bottom_Id_Equal id_ann
                            end 
; bottom_is_id_top_ann_d := os_from_bs_left_exists_top_ann_equal_certify (pann_is_tid_plus_times_d P) 
|}.

Definition os_bs_left_top_is_ann_certs_from_pid_is_tann_certs {S : Type} 
           (P : @pid_is_tann_certificates S) : @os_top_is_ann_certs S := 
{|
  top_is_ann_bottom_id_d := os_from_bs_left_exists_bottom_id_equal_certify (pid_is_tann_times_plus_d P)
; top_is_ann             := match (pid_is_tann_plus_times P) with
                            | Assert_Exists_Id_Ann_Equal id_ann => Assert_Os_Exists_Top_Ann_Equal id_ann
                            end 
|}.

Definition os_bs_left_monotone_increasing_certs_from_dioid_certs {S : Type} 
           (P : @dioid_certificates S) : @os_monotone_increasing_certificates S := 
{|
  mono_inc_left_monotonic   := Assert_Left_Monotone
; mono_inc_right_monotonic  := Assert_Right_Monotone

; mono_inc_left_increasing  := Assert_Left_Increasing
; mono_inc_right_increasing := Assert_Right_Increasing
|}. 
  
End Certs.

Section Combinators.

Definition posg_from_pre_dioid {S :Type} (D : @pre_dioid S) : @monotone_increasing_posg S :=
let eqv        := pre_dioid_eqv D in
let eq         := eqv_eq eqv in
let plus       := pre_dioid_plus D in
let plusP      := pre_dioid_plus_certs D in
{|
  miposg_eqv          := eqv 
; miposg_lte          := brel_lte_left eq plus
; miposg_times        := pre_dioid_times D
; miposg_lte_certs    := po_certs_from_sg_CI_left_certs plusP 
; miposg_times_certs  := pre_dioid_times_certs D
; miposg_top_bottom   := os_bs_left_bottom_top_certs_from_id_ann_certs (pre_dioid_id_ann_certs D)
; miposg_certs        := os_bs_left_monotone_increasing_certs_from_dioid_certs (pre_dioid_certs D)
; miposg_ast          := Ast_os_from_bs_left (pre_dioid_ast D)
|}.


Definition posg_from_dioid (S :Type) (D : @dioid S) : @bounded_monotone_increasing_posg S :=
{|
  bmiposg_eqv          := dioid_eqv _ D
; bmiposg_lte          := brel_lte_left (eqv_eq (dioid_eqv _ D)) (dioid_plus _ D)
; bmiposg_times        := dioid_times _ D 
; bmiposg_lte_certs    := po_certs_from_sg_CI_left_certs (dioid_plus_certs _ D )
; bmiposg_times_certs  := dioid_times_certs _ D 
; bmiposg_top_bottom   := os_bs_left_bounded_certs_from_bs_bounded_certs (dioid_id_ann_certs _ D)
; bmiposg_certs        := os_bs_left_monotone_increasing_certs_from_dioid_certs (dioid_certs _ D)
; bmiposg_ast          := Ast_os_from_bs_left (dioid_ast _ D)
|}.


End Combinators.  
End CAS.


Section MCAS.

Local Open Scope string_scope.
Local Open Scope list_scope.     

Definition mcas_os_from_bs_left  (S : Type) (A : @bs_mcas S) :=
  match bs_classify A with
  | BS_dioid C => OS_bounded_monotone_increasing_posg (posg_from_dioid _ C)
  | _ => OS_Error ("mcas_posg_from_bs_left : this combinator (currently) requires a dioid" :: nil) 
  end. 

End MCAS.   



Section Verify.
 
End Verify.   
  
*) 
