Require Import Coq.Strings.String.
Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.

Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.

Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures.
Require Import CAS.coq.sg.theory.


(* semigroups 

Current Implementation Hierarchy

sg     = semigroup 
sg_C   = commutative semigroup 
sg_CS  = commutative selective semigroup (is idempotent, of course) 
sg_CI  = commutative idempotent semigroup, not selective 
sg_CNI  = commutative, not idempotent 

           sg 
           |  
          sg_C
         / |  \ 
        /  |   \ 
       /   |    \  
      /    |     \ 
  sg_CI sg_CNI  sg_CS 

*) 
Section ACAS.

Section Proofs.

  Variables (S : Type)
            (r : brel S)
            (b : binary_op S)
            (s : S)
            (f : S -> S)
            (Pf : brel_not_trivial S r f)
            (eqvS : eqv_proofs S r)
            (id_d : bop_exists_id_decidable S r b).


Definition A_sg_proofs_from_sg_C_proofs (sgS : sg_C_proofs S r b) : sg_proofs S r b := 
let commS := A_sg_C_commutative S r b sgS in   
let symS :=  A_eqv_symmetric S r eqvS in 
let tranS := A_eqv_transitive S r eqvS in 
{|
  A_sg_associative      := A_sg_C_associative S r b sgS 
; A_sg_congruence       := A_sg_C_congruence S r b sgS 
; A_sg_commutative_d    := inl _ (A_sg_C_commutative S r b sgS) 
; A_sg_selective_d      := A_sg_C_selective_d S r b sgS    
; A_sg_is_left_d        := inr _ (bop_commutative_implies_not_is_left S r b s f Pf symS tranS commS)
; A_sg_is_right_d       := inr _ (bop_commutative_implies_not_is_right S r b s f Pf symS tranS commS)
; A_sg_idempotent_d     := A_sg_C_idempotent_d S r b sgS    
; A_sg_left_cancel_d    := A_sg_C_cancel_d S r b sgS    
; A_sg_right_cancel_d   := match A_sg_C_cancel_d S r b sgS with 
                           | inl lcanS => inl (bop_commutative_and_left_cancellative_imply_right_cancellative S r b tranS commS lcanS)
                           | inr nlcanS => inr (bop_commutative_and_not_left_cancellative_imply_not_right_cancellative S r b symS tranS commS nlcanS)
                           end 
; A_sg_left_constant_d  := A_sg_C_constant_d S r b sgS
; A_sg_right_constant_d := match A_sg_C_constant_d S r b sgS with
                           | inl conS => inl (bop_commutative_and_left_constant_imply_right_constant S r b tranS commS conS)                             
                           | inr nconS => inr (bop_commutative_and_not_left_constant_imply_not_right_constant S r b symS tranS commS nconS)
                           end                                                         
; A_sg_anti_left_d      := A_sg_C_anti_left_d S r b sgS
; A_sg_anti_right_d     := A_sg_C_anti_right_d S r b sgS
|}.

Definition A_sg_C_proofs_from_sg_CNI_proofs (sgS : sg_CNI_proofs S r b) : sg_C_proofs S r b := 
let nidem   := A_sg_CNI_not_idempotent S r b sgS  in
let not_sel := bop_not_idempotent_implies_not_selective _ _ _ nidem in 
{|
  A_sg_C_associative      := A_sg_CNI_associative S r b sgS 
; A_sg_C_congruence       := A_sg_CNI_congruence S r b sgS  
; A_sg_C_commutative      := A_sg_CNI_commutative S r b sgS 
; A_sg_C_selective_d      := inr not_sel
; A_sg_C_idempotent_d     := inr nidem 
; A_sg_C_cancel_d         := A_sg_CNI_cancel_d _ _ _  sgS
; A_sg_C_constant_d       := A_sg_CNI_constant_d _ _ _  sgS
; A_sg_C_anti_left_d      := A_sg_CNI_anti_left_d _ _ _  sgS
; A_sg_C_anti_right_d     := A_sg_CNI_anti_right_d _ _ _  sgS
|}. 


Definition A_sg_C_proofs_from_sg_CI_proofs (sgS : sg_CI_proofs S r b) : sg_C_proofs S r b := 
let assoc := A_sg_CI_associative S r b sgS in
let econg := A_eqv_congruence  S r eqvS  in 
let bcong := A_sg_CI_congruence S r b sgS  in 
let comm  := A_sg_CI_commutative S r b sgS in
let not_sel := A_sg_CI_not_selective S r b sgS   in
let idem  := A_sg_CI_idempotent S r b sgS  in 
let ref   := A_eqv_reflexive S r eqvS in
let sym   := A_eqv_symmetric S r eqvS in
let trn   := A_eqv_transitive S r eqvS in 
{|
  A_sg_C_associative      := assoc 
; A_sg_C_congruence       := bcong 
; A_sg_C_commutative      := comm 
; A_sg_C_selective_d      := inr not_sel
; A_sg_C_idempotent_d     := inl _ idem 
; A_sg_C_cancel_d    := inr _ (bop_idempotent_and_commutative_and_selective_decidable_imply_not_left_cancellative S r b s f 
                                       econg Pf ref sym trn assoc bcong idem comm (inr not_sel))
; A_sg_C_constant_d  := inr _ (bop_idempotent_and_commutative_imply_not_left_constant S r b s f Pf 
                                       econg ref trn idem comm) 
; A_sg_C_anti_left_d      := inr _ (bop_idempotent_implies_not_anti_left S r b s sym idem)
; A_sg_C_anti_right_d     := inr _ (bop_idempotent_implies_not_anti_right S r b s sym idem) 
|}. 

Definition A_sg_C_proofs_from_sg_CS_proofs (sgS : sg_CS_proofs S r b) : sg_C_proofs S r b := 
let assoc := A_sg_CS_associative S r b sgS in
let econg := A_eqv_congruence  S r eqvS  in 
let bcong := A_sg_CS_congruence S r b sgS  in 
let comm  := A_sg_CS_commutative S r b sgS in
let sel   := A_sg_CS_selective S r b sgS   in
let idem  := bop_selective_implies_idempotent S r b  sel in
let ref   := A_eqv_reflexive S r eqvS in
let sym   := A_eqv_symmetric S r eqvS in
let trn   := A_eqv_transitive S r eqvS in 
{|
  A_sg_C_associative      := assoc 
; A_sg_C_congruence       := bcong 
; A_sg_C_commutative      := comm 
; A_sg_C_selective_d      := inl sel 
; A_sg_C_idempotent_d     := inl idem 
; A_sg_C_cancel_d    := inr _ (bop_idempotent_and_commutative_and_selective_decidable_imply_not_left_cancellative S r b s f 
                                       econg Pf ref sym trn assoc bcong idem comm (inl sel))
; A_sg_C_constant_d  := inr _ (bop_idempotent_and_commutative_imply_not_left_constant S r b s f Pf 
                                       econg ref trn idem comm)
; A_sg_C_anti_left_d      := inr _ (bop_idempotent_implies_not_anti_left S r b s sym idem) 
; A_sg_C_anti_right_d     := inr _ (bop_idempotent_implies_not_anti_right S r b s sym idem) 
|}. 


(* DERIVED UPCASTS *)

(* two hops *) 
Definition A_sg_proofs_from_sg_CI_proofs (sgS : sg_CI_proofs S r b) : sg_proofs S r b := 
   A_sg_proofs_from_sg_C_proofs (A_sg_C_proofs_from_sg_CI_proofs sgS).

Definition A_sg_proofs_from_sg_CS_proofs (sgS : sg_CS_proofs S r b) : sg_proofs S r b := 
   A_sg_proofs_from_sg_C_proofs (A_sg_C_proofs_from_sg_CS_proofs sgS).

End Proofs.
  
Section Combinators. 


Definition A_sg_from_sg_C (S : Type) (sgS : A_sg_C S) : A_sg S := 
   {| 
     A_sg_eqv          := A_sg_C_eqv _ sgS
   ; A_sg_bop          := A_sg_C_bop _ sgS
   ; A_sg_exists_id_d  := A_sg_C_exists_id_d _ sgS
   ; A_sg_exists_ann_d := A_sg_C_exists_ann_d _ sgS
   ; A_sg_proofs       := A_sg_proofs_from_sg_C_proofs _ _ _ 
                            (A_eqv_witness _ (A_sg_C_eqv _ sgS))
                            (A_eqv_new _ (A_sg_C_eqv _ sgS))
                            (A_eqv_not_trivial _ (A_sg_C_eqv _ sgS))
                            (A_eqv_proofs _ (A_sg_C_eqv _ sgS)) 
                            (A_sg_C_proofs _ sgS)
   ; A_sg_ast        := A_sg_C_ast _ sgS
   |}. 


Definition A_sg_C_from_sg_CI (S : Type) (sgS : A_sg_CI S) : A_sg_C S := 
   {| 
     A_sg_C_eqv          := A_sg_CI_eqv S sgS
   ; A_sg_C_bop          := A_sg_CI_bop S sgS
   ; A_sg_C_exists_id_d  := A_sg_CI_exists_id_d S sgS    
   ; A_sg_C_exists_ann_d := A_sg_CI_exists_ann_d S sgS    
   ; A_sg_C_proofs       := A_sg_C_proofs_from_sg_CI_proofs S 
                            (A_eqv_eq S (A_sg_CI_eqv S sgS)) 
                            (A_sg_CI_bop S sgS)
                            (A_eqv_witness S (A_sg_CI_eqv S sgS))
                            (A_eqv_new S (A_sg_CI_eqv S sgS))
                            (A_eqv_not_trivial S (A_sg_CI_eqv S sgS))                                                                                     
                            (A_eqv_proofs S (A_sg_CI_eqv S sgS)) 
                            (A_sg_CI_proofs S sgS)
   ; A_sg_C_ast        := A_sg_CI_ast S sgS
   |}. 


Definition A_sg_C_from_sg_CS (S : Type) (sgS : A_sg_CS S) : A_sg_C S := 
   {| 
     A_sg_C_eqv          := A_sg_CS_eqv S sgS
   ; A_sg_C_bop          := A_sg_CS_bop S sgS
   ; A_sg_C_exists_id_d  := A_sg_CS_exists_id_d S sgS    
   ; A_sg_C_exists_ann_d := A_sg_CS_exists_ann_d S sgS    
   ; A_sg_C_proofs       := A_sg_C_proofs_from_sg_CS_proofs S 
                            (A_eqv_eq S (A_sg_CS_eqv S sgS)) 
                            (A_sg_CS_bop S sgS)
                            (A_eqv_witness S (A_sg_CS_eqv S sgS))
                            (A_eqv_new S (A_sg_CS_eqv S sgS))
                            (A_eqv_not_trivial S (A_sg_CS_eqv S sgS))                                                                                     
                            (A_eqv_proofs S (A_sg_CS_eqv S sgS)) 
                            (A_sg_CS_proofs S sgS)
   ; A_sg_C_ast        := A_sg_CS_ast S sgS
   |}.

Definition A_sg_C_from_sg_CNI (S : Type) (sgS : A_sg_CNI S) : A_sg_C S := 
   {| 
     A_sg_C_eqv          := A_sg_CNI_eqv S sgS
   ; A_sg_C_bop          := A_sg_CNI_bop S sgS
   ; A_sg_C_exists_id_d  := A_sg_CNI_exists_id_d S sgS    
   ; A_sg_C_exists_ann_d := A_sg_CNI_exists_ann_d S sgS    
   ; A_sg_C_proofs       := A_sg_C_proofs_from_sg_CNI_proofs _ _ _ (A_sg_CNI_proofs S sgS)
   ; A_sg_C_ast        := A_sg_CNI_ast S sgS
   |}. 




(* DERIVED UPCASTS *)

(* two hops*)

Definition A_sg_from_sg_CI : ∀ (S : Type),  A_sg_CI S -> A_sg S 
:= λ S sgS, A_sg_from_sg_C S (A_sg_C_from_sg_CI S sgS).  

Definition A_sg_from_sg_CS : ∀ (S : Type),  A_sg_CS S -> A_sg S 
  := λ S sgS, A_sg_from_sg_C S (A_sg_C_from_sg_CS S sgS).

End Combinators. 

End ACAS.


Section AMCAS.
  
    Definition A_cast_up_sg_CS {S : Type} (A : @A_below_sg_CS S) : A_sg_CS S :=
    match A with
    | A_Below_sg_CS_top  B    => B 
    end. 

    Definition A_cast_up_sg_CI {S : Type} (A : @A_below_sg_CI S) : A_sg_CI S :=
    match A with
    | A_Below_sg_CI_top  B    => B 
    end. 
    Definition A_cast_up_sg_CNI {S : Type} (A : @A_below_sg_CNI S) : A_sg_CNI S :=
    match A with
    | A_Below_sg_CNI_top  B    => B 
    end. 

    
  Definition A_cast_up_sg_C {S : Type} (A : @A_below_sg_C S) : A_sg_C S :=
    match A with
    | A_Below_sg_C_top  B   => B 
    | A_Below_sg_C_sg_CS B  => A_sg_C_from_sg_CS _ (A_cast_up_sg_CS B)
    | A_Below_sg_C_sg_CI B  => A_sg_C_from_sg_CI _ (A_cast_up_sg_CI B)
    | A_Below_sg_C_sg_CNI B => A_sg_C_from_sg_CNI _ (A_cast_up_sg_CNI B)                                                  
    end. 
    
  Definition A_cast_up_sg {S : Type} (A : @A_below_sg S) : A_sg S :=
    match A with 
    | A_Below_sg_top B   => B 
    | A_Below_sg_sg_C bc => A_sg_from_sg_C _ (A_cast_up_sg_C bc)       
    end.


    (* NB: each of the following cast (down) functions assumes 
       that its argument has been classified already.
       These functions can "fail" by returning None. 
    *)  
    Definition A_cast_below_sg_C_to_below_sg_CI {S : Type}
    (A : @A_below_sg_C S) : option (@A_below_sg_CI S) :=
    match A with
    | A_Below_sg_C_top _  => None
    | A_Below_sg_C_sg_CI B => Some B
    | A_Below_sg_C_sg_CS _ => None
    | A_Below_sg_C_sg_CNI _ => None                                 
    end. 

    Definition A_cast_below_sg_C_to_below_sg_CS {S : Type}
    (A : @A_below_sg_C S) : option (@A_below_sg_CS S) :=
    match A with
    | A_Below_sg_C_top _  => None
    | A_Below_sg_C_sg_CS B => Some B
    | A_Below_sg_C_sg_CI _ => None
    | A_Below_sg_C_sg_CNI _ => None
    end. 

    Definition A_cast_below_sg_C_to_below_sg_CNI {S : Type}
    (A : @A_below_sg_C S) : option (@A_below_sg_CNI S) :=
    match A with
    | A_Below_sg_C_top _  => None
    | A_Below_sg_C_sg_CS _ => None
    | A_Below_sg_C_sg_CI _ => None
    | A_Below_sg_C_sg_CNI B => Some B
    end. 
    
  Definition A_cast_below_sg_to_below_sg_CI {S : Type}
    (A : @A_below_sg S) : option (@A_below_sg_CI S) :=
    match A with
    | A_Below_sg_top _  => None
    | A_Below_sg_sg_C B => A_cast_below_sg_C_to_below_sg_CI B
    end. 


  Definition A_cast_below_sg_to_below_sg_CS {S : Type}
    (A : @A_below_sg S) : option (@A_below_sg_CS S) :=
    match A with
    | A_Below_sg_top _  => None
    | A_Below_sg_sg_C B => A_cast_below_sg_C_to_below_sg_CS B
    end. 


  Definition A_cast_below_sg_to_below_sg_C {S : Type}
    (A : @A_below_sg S) : option (@A_below_sg_C S) :=
    match A with
    | A_Below_sg_top _  => None
    | A_Below_sg_sg_C B => Some B
    end. 

End AMCAS.

Section CAS.

Section Certificates.
    
Variables  (S : Type)
           (r : brel S)
           (b : binary_op S)
           (s : S)
           (f : S -> S)
           (id_d : @check_exists_id S).  

Definition sg_certs_from_sg_C_certs (sgS : @sg_C_certificates S) : @sg_certificates S := 
{|
  sg_associative      := Assert_Associative 
; sg_congruence       := Assert_Bop_Congruence 
; sg_commutative_d    := Certify_Commutative 
; sg_selective_d      := sg_C_selective_d sgS    
; sg_is_left_d        := Certify_Not_Is_Left (cef_commutative_implies_not_is_left r b s f)
; sg_is_right_d       := Certify_Not_Is_Right (cef_commutative_implies_not_is_right r b s f)
; sg_idempotent_d     := sg_C_idempotent_d sgS    
; sg_left_cancel_d    := sg_C_cancel_d sgS    
; sg_right_cancel_d   := match sg_C_cancel_d sgS with
                         | Certify_Left_Cancellative => Certify_Right_Cancellative
                         | Certify_Not_Left_Cancellative (x, (y, z)) => Certify_Not_Right_Cancellative (x, (y, z))
                         end 
; sg_left_constant_d  := sg_C_constant_d sgS
; sg_right_constant_d := match sg_C_constant_d sgS with
                         | Certify_Left_Constant => Certify_Right_Constant
                         | Certify_Not_Left_Constant (x, (y, z)) => Certify_Not_Right_Constant (x, (y, z))
                         end 
; sg_anti_left_d      := sg_C_anti_left_d sgS
; sg_anti_right_d     := sg_C_anti_right_d sgS
|}.

Definition sg_C_certs_from_sg_CI_certs (sgS : @sg_CI_certificates S): @sg_C_certificates S := 
{|
  sg_C_associative      := Assert_Associative 
; sg_C_congruence       := Assert_Bop_Congruence 
; sg_C_commutative      := Assert_Commutative 

; sg_C_idempotent_d     := Certify_Idempotent
; sg_C_selective_d      := match sg_CI_not_selective sgS with
                           | Assert_Not_Selective (s1, s2) => Certify_Not_Selective (s1, s2)
                           end
; sg_C_constant_d       := Certify_Not_Left_Constant (cef_idempotent_and_commutative_imply_not_left_constant r b s f) 
; sg_C_cancel_d         := match sg_CI_not_selective sgS with
                           | Assert_Not_Selective (s1, s2) =>
                               Certify_Not_Left_Cancellative (cef_idempotent_and_commutative_and_not_selective_imply_not_left_cancellative  b s1 s2) 
                           end
; sg_C_anti_left_d      := Certify_Not_Anti_Left (cef_idempotent_implies_not_anti_left s) 
; sg_C_anti_right_d     := Certify_Not_Anti_Right (cef_idempotent_implies_not_anti_right s) 
|}.

Definition sg_C_certs_from_sg_CNI_certs (sgS : @sg_CNI_certificates S) : @sg_C_certificates S := 
{|
  sg_C_associative      := sg_CNI_associative sgS 
; sg_C_congruence       := sg_CNI_congruence sgS  
; sg_C_commutative      := sg_CNI_commutative sgS 
; sg_C_selective_d      := match sg_CNI_not_idempotent sgS with
                           | Assert_Not_Idempotent i => Certify_Not_Selective (i, i) 
                           end 
; sg_C_idempotent_d     := match sg_CNI_not_idempotent sgS with
                           | Assert_Not_Idempotent i => Certify_Not_Idempotent i
                           end 
; sg_C_cancel_d         := sg_CNI_cancel_d  sgS
; sg_C_constant_d       := sg_CNI_constant_d  sgS
; sg_C_anti_left_d      := sg_CNI_anti_left_d  sgS
; sg_C_anti_right_d     := sg_CNI_anti_right_d  sgS
|}. 


Definition sg_C_certs_from_sg_CS_certs (sgS : @sg_CS_certificates S): @sg_C_certificates S := 
{|
  sg_C_associative      := Assert_Associative 
; sg_C_congruence       := Assert_Bop_Congruence 
; sg_C_commutative      := Assert_Commutative 
; sg_C_idempotent_d     := Certify_Idempotent
; sg_C_selective_d      := Certify_Selective 
; sg_C_constant_d       := Certify_Not_Left_Constant (cef_idempotent_and_commutative_imply_not_left_constant r b s f) 
; sg_C_cancel_d         := Certify_Not_Left_Cancellative (cef_selective_and_commutative_imply_not_left_cancellative  r b s f)
; sg_C_anti_left_d      := Certify_Not_Anti_Left (cef_idempotent_implies_not_anti_left s) 
; sg_C_anti_right_d     := Certify_Not_Anti_Right (cef_idempotent_implies_not_anti_right s) 
|}. 


(* DERIVED UPCASTS *)

(* two hops *) 
Definition sg_certs_from_sg_CI_certs (sgS : @sg_CI_certificates S) :  @sg_certificates S :=
  sg_certs_from_sg_C_certs (sg_C_certs_from_sg_CI_certs sgS).

Definition sg_certs_from_sg_CS_certs (sgS : @sg_CS_certificates S) : @sg_certificates S := 
  sg_certs_from_sg_C_certs (sg_C_certs_from_sg_CS_certs sgS).

End Certificates. 

Section Combinators.

Definition sg_from_sg_C {S : Type} (sg_C : @sg_C S) : @sg S := 
   {| 
       sg_eqv    := sg_C_eqv sg_C
     ; sg_bop   := sg_C_bop sg_C
     ; sg_exists_id_d  := sg_C_exists_id_d sg_C
     ; sg_exists_ann_d := sg_C_exists_ann_d sg_C
     ; sg_certs := sg_certs_from_sg_C_certs S
                    (eqv_eq (sg_C_eqv sg_C)) 
                    (sg_C_bop sg_C) 
                    (eqv_witness (sg_C_eqv sg_C))
                    (eqv_new (sg_C_eqv sg_C))                    
                    (sg_C_certs sg_C)
     ; sg_ast   := sg_C_ast sg_C
   |}.

Definition sg_C_from_sg_CI {S : Type} (sg: @sg_CI S) : @sg_C S := 
   {| 
     sg_C_eqv   := sg_CI_eqv sg
   ; sg_C_bop   := sg_CI_bop sg
   ; sg_C_exists_id_d  := sg_CI_exists_id_d sg
   ; sg_C_exists_ann_d := sg_CI_exists_ann_d sg
   ; sg_C_certs := sg_C_certs_from_sg_CI_certs S
                     (eqv_eq (sg_CI_eqv sg))
                     (sg_CI_bop sg)                                               
                     (eqv_witness (sg_CI_eqv sg))
                     (eqv_new (sg_CI_eqv sg))
                     (sg_CI_certs sg)
   ; sg_C_ast   := sg_CI_ast sg
   |}. 

Definition sg_C_from_sg_CNI {S : Type} (sgS : @sg_CNI S) : @sg_C S := 
   {| 
     sg_C_eqv          := sg_CNI_eqv sgS
   ; sg_C_bop          := sg_CNI_bop sgS
   ; sg_C_exists_id_d  := sg_CNI_exists_id_d sgS    
   ; sg_C_exists_ann_d := sg_CNI_exists_ann_d sgS    
   ; sg_C_certs        := sg_C_certs_from_sg_CNI_certs _ (sg_CNI_certs sgS)
   ; sg_C_ast          := sg_CNI_ast sgS
   |}. 

Definition sg_C_from_sg_CS {S : Type} (sg : @sg_CS S) : @sg_C S := 
   {| 
     sg_C_eqv   := sg_CS_eqv sg
   ; sg_C_bop   := sg_CS_bop sg
   ; sg_C_exists_id_d  := sg_CS_exists_id_d sg
   ; sg_C_exists_ann_d := sg_CS_exists_ann_d sg
   ; sg_C_certs := sg_C_certs_from_sg_CS_certs S
                     (eqv_eq (sg_CS_eqv sg))
                     (sg_CS_bop sg)                                               
                     (eqv_witness (sg_CS_eqv sg))
                     (eqv_new (sg_CS_eqv sg))
                     (sg_CS_certs sg)
   ; sg_C_ast   := sg_CS_ast sg
   |}. 


(* DERIVED UPCASTS *)

Definition sg_from_sg_CI {S : Type} (sgS : @sg_CI S) : @sg S := 
  sg_from_sg_C (sg_C_from_sg_CI sgS). 

Definition sg_from_sg_CS {S : Type} (sgS : @sg_CS S) : @sg S := 
  sg_from_sg_C (sg_C_from_sg_CS sgS).

End Combinators. 
End CAS.

Section MCAS.

    Definition cast_up_sg_CS {S : Type} (A : @below_sg_CS S) : @sg_CS S :=
    match A with
    | Below_sg_CS_top  B    => B 
    end. 

    Definition cast_up_sg_CI {S : Type} (A : @below_sg_CI S) : @sg_CI S :=
    match A with
    | Below_sg_CI_top  B    => B 
    end. 

    Definition cast_up_sg_CNI {S : Type} (A : @below_sg_CNI S) : @sg_CNI S :=
    match A with
    | Below_sg_CNI_top  B    => B 
    end. 
    
  Definition cast_up_sg_C {S : Type} (A : @below_sg_C S) : @sg_C S :=
    match A with
    | Below_sg_C_top  B    => B 
    | Below_sg_C_sg_CS B => sg_C_from_sg_CS (cast_up_sg_CS B)
    | Below_sg_C_sg_CI B => sg_C_from_sg_CI (cast_up_sg_CI B)
    | Below_sg_C_sg_CNI B => sg_C_from_sg_CNI (cast_up_sg_CNI B)
    end. 
    
  Definition cast_up_sg {S : Type} (A : @below_sg S) : @sg S :=
    match A with 
    | Below_sg_top B   => B 
    | Below_sg_sg_C bc => sg_from_sg_C (cast_up_sg_C bc)       
    end.


   (* NB: each of the following cast (down) functions assumes 
       that its argument has been classified already.
       These functions can "fail" by returning None. 
    *)  
    Definition cast_below_sg_C_to_below_sg_CI {S : Type}
    (A : @below_sg_C S) : option (@below_sg_CI S) :=
    match A with
    | Below_sg_C_top _  => None
    | Below_sg_C_sg_CI B => Some B
    | Below_sg_C_sg_CS _ => None
    | Below_sg_C_sg_CNI _ => None                             
    end. 

    Definition cast_below_sg_C_to_below_sg_CS {S : Type}
    (A : @below_sg_C S) : option (@below_sg_CS S) :=
    match A with
    | Below_sg_C_top _  => None 
    | Below_sg_C_sg_CI _ => None                            
    | Below_sg_C_sg_CS B => Some B
    | Below_sg_C_sg_CNI _ => None                                                           
    end. 

    Definition cast_below_sg_C_to_below_sg_CNI {S : Type}
    (A : @below_sg_C S) : option (@below_sg_CNI S) :=
    match A with
    | Below_sg_C_top _  => None 
    | Below_sg_C_sg_CI _ => None                            
    | Below_sg_C_sg_CS _ => None                                                           
    | Below_sg_C_sg_CNI B => Some B
    end. 

    
  Definition cast_below_sg_to_below_sg_CI {S : Type}
    (A : @below_sg S) : option (@below_sg_CI S) :=
    match A with
    | Below_sg_top _  => None
    | Below_sg_sg_C B => cast_below_sg_C_to_below_sg_CI B
    end. 


  Definition cast_below_sg_to_below_sg_CS {S : Type}
    (A : @below_sg S) : option (@below_sg_CS S) :=
    match A with
    | Below_sg_top _  => None
    | Below_sg_sg_C B => cast_below_sg_C_to_below_sg_CS B
    end. 


  Definition cast_below_sg_to_below_sg_C {S : Type}
    (A : @below_sg S) : option (@below_sg_C S) :=
    match A with
    | Below_sg_top _  => None
    | Below_sg_sg_C B => Some B
    end. 


End MCAS.


Section Verify.

Section Certificates.

  Variables (S : Type)
            (r : brel S)
            (b : binary_op S)
            (s : S)
            (f : S -> S)
            (nt : brel_not_trivial S r f)
            (eqvS : eqv_proofs S r)
            (id_d : bop_exists_id_decidable S r b). 

Lemma correct_sg_certs_from_sg_C_certs (sgS : sg_C_proofs S r b) : 
       sg_certs_from_sg_C_certs S r b s f (P2C_sg_C r b sgS)
       = 
       P2C_sg r b (A_sg_proofs_from_sg_C_proofs S r b s f nt eqvS sgS). 
Proof. destruct sgS. destruct eqvS. 
       unfold sg_certs_from_sg_C_certs, A_sg_proofs_from_sg_C_proofs, P2C_sg, P2C_sg_C; simpl.
       destruct A_sg_C_cancel_d as [ lcanS | [[x [y z]] nlcanS]];
       destruct A_sg_C_constant_d as [ lconS | [[u [v w]] nlconS] ]; simpl; 
       reflexivity.
Defined. 

Lemma correct_sg_C_certs_from_sg_CI_certs (sgS : sg_CI_proofs S r b) : 
       sg_C_certs_from_sg_CI_certs S r b s f (P2C_sg_CI r b sgS)
       = 
       P2C_sg_C r b (A_sg_C_proofs_from_sg_CI_proofs S r b s f nt eqvS sgS). 
Proof. destruct sgS. destruct eqvS. 
       unfold sg_C_certs_from_sg_CI_certs, A_sg_C_proofs_from_sg_CI_proofs, P2C_sg_C, P2C_sg_CI. simpl. 
       destruct A_sg_CI_not_selective as [[s1 s2] [A B]]. 
       simpl. reflexivity.        
Defined.


Lemma correct_sg_C_certs_from_sg_CNI_certs (sgS : sg_CNI_proofs S r b) : 
       sg_C_certs_from_sg_CNI_certs S (P2C_sg_CNI _ r b sgS)
       = 
       P2C_sg_C r b (A_sg_C_proofs_from_sg_CNI_proofs S r b sgS). 
Proof. destruct sgS. 
       unfold sg_C_certs_from_sg_CNI_certs, A_sg_C_proofs_from_sg_CNI_proofs,
              P2C_sg_C, P2C_sg_CNI. simpl. 
       destruct A_sg_CNI_not_idempotent as [i A]. 
       simpl. reflexivity.        
Defined.

Lemma correct_sg_C_certs_from_sg_CS_certs (sgS : sg_CS_proofs S r b) : 
       sg_C_certs_from_sg_CS_certs S r b s f (P2C_sg_CS r b sgS)
       = 
       P2C_sg_C r b (A_sg_C_proofs_from_sg_CS_proofs S r b s f nt eqvS sgS). 
Proof.  destruct sgS. destruct eqvS. 
       unfold sg_C_certs_from_sg_CS_certs, A_sg_C_proofs_from_sg_CS_proofs, P2C_sg_C, P2C_sg_CS; 
       simpl. reflexivity.        
Defined.

End Certificates.

Section Combinators.


Theorem correct_sg_from_sg_C (S : Type) (P : A_sg_C S) : 
         sg_from_sg_C (A2C_sg_C P) = A2C_sg (A_sg_from_sg_C S P). 
Proof. destruct P.
       unfold sg_from_sg_C, A_sg_from_sg_C, A2C_sg_C, A2C_sg; simpl.
       destruct A_sg_C_eqv. simpl. 
       rewrite <-correct_sg_certs_from_sg_C_certs; auto. 
Qed. 

Theorem correct_sg_C_from_sg_CI (S : Type) (P : A_sg_CI S) : 
         sg_C_from_sg_CI (A2C_sg_CI P) = A2C_sg_C (A_sg_C_from_sg_CI S P). 
Proof. unfold sg_C_from_sg_CI, A_sg_C_from_sg_CI, A2C_sg_CI, A2C_sg_C; simpl. 
       rewrite <- correct_sg_C_certs_from_sg_CI_certs; auto. 
Qed.

Theorem correct_sg_C_from_sg_CNI (S : Type) (P : A_sg_CNI S) : 
  sg_C_from_sg_CNI (A2C_sg_CNI P)
  =
  A2C_sg_C (A_sg_C_from_sg_CNI S P). 
Proof. unfold sg_C_from_sg_CNI, A_sg_C_from_sg_CNI,
              A2C_sg_CNI, A2C_sg_C; simpl. 
       rewrite <- correct_sg_C_certs_from_sg_CNI_certs; auto. 
Qed.

Theorem correct_sg_C_from_sg_CS (S : Type) (P : A_sg_CS S) : 
         sg_C_from_sg_CS (A2C_sg_CS P) = A2C_sg_C (A_sg_C_from_sg_CS S P). 
Proof. unfold sg_C_from_sg_CS, A_sg_C_from_sg_CS, A2C_sg_CS, A2C_sg_C; simpl. 
       rewrite <- correct_sg_C_certs_from_sg_CS_certs; auto. 
Qed.

Theorem correct_cast_up_sg_CS (S : Type) (A : @A_below_sg_CS S) : 
  cast_up_sg_CS (A2C_below_sg_CS A)
  =
    A2C_sg_CS (A_cast_up_sg_CS A).
Proof. destruct A.
       unfold cast_up_sg_CS, A_cast_up_sg_CS, A2C_below_sg_CS, A2C_sg_CS.
       reflexivity.
Qed.        

Theorem correct_cast_up_sg_CI (S : Type) (A : @A_below_sg_CI S) : 
  cast_up_sg_CI (A2C_below_sg_CI A)
  =
  A2C_sg_CI (A_cast_up_sg_CI A).
Proof. destruct A.
       unfold cast_up_sg_CI, A_cast_up_sg_CI, A2C_below_sg_CI, A2C_sg_CI.
       reflexivity.
Qed.

Theorem correct_cast_up_sg_CNI (S : Type) (A : @A_below_sg_CNI S) : 
  cast_up_sg_CNI (A2C_below_sg_CNI A)
  =
  A2C_sg_CNI (A_cast_up_sg_CNI A).
Proof. destruct A.
       unfold cast_up_sg_CNI, A_cast_up_sg_CNI, A2C_below_sg_CNI, A2C_sg_CNI.
       reflexivity.
Qed.        

Theorem correct_cast_up_sg_C (S : Type) (A : @A_below_sg_C S) : 
  cast_up_sg_C (A2C_below_sg_C A)
  =
    A2C_sg_C (A_cast_up_sg_C A).
Proof. destruct A; unfold cast_up_sg_C, A_cast_up_sg_C; simpl. 
       - reflexivity.
       - rewrite correct_cast_up_sg_CS.
         rewrite correct_sg_C_from_sg_CS. 
         reflexivity.
       - rewrite correct_cast_up_sg_CI.
         rewrite correct_sg_C_from_sg_CI. 
         reflexivity.
       - rewrite correct_cast_up_sg_CNI.
         rewrite correct_sg_C_from_sg_CNI. 
         reflexivity.
Qed.        

Theorem correct_cast_up_sg (S : Type) (A : @A_below_sg S) : 
  cast_up_sg (A2C_below_sg A)
  =
    A2C_sg (A_cast_up_sg A).
Proof. destruct A; unfold cast_up_sg, A_cast_up_sg; simpl. 
       - reflexivity.
       - rewrite correct_cast_up_sg_C.
         rewrite correct_sg_from_sg_C. 
         reflexivity.
Qed.

Theorem correct_cast_below_sg_C_to_below_sg_CI (S : Type) (A : @A_below_sg_C S) :
  cast_below_sg_C_to_below_sg_CI (A2C_below_sg_C A)
  =
  option_map A2C_below_sg_CI (A_cast_below_sg_C_to_below_sg_CI A).
Proof. destruct A; unfold A_cast_below_sg_C_to_below_sg_CI,
         cast_below_sg_C_to_below_sg_CI; simpl; try reflexivity.
Qed.

Theorem correct_cast_below_sg_C_to_below_sg_CS (S : Type) (A : @A_below_sg_C S) :
  cast_below_sg_C_to_below_sg_CS (A2C_below_sg_C A)
  =
  option_map A2C_below_sg_CS (A_cast_below_sg_C_to_below_sg_CS A).
Proof. destruct A; unfold A_cast_below_sg_C_to_below_sg_CI,
         cast_below_sg_C_to_below_sg_CI; simpl; try reflexivity.
Qed.

Theorem correct_cast_below_sg_to_below_sg_CI (S : Type) (A : @A_below_sg S) :
  cast_below_sg_to_below_sg_CI (A2C_below_sg A)
  =
  option_map A2C_below_sg_CI (A_cast_below_sg_to_below_sg_CI A).
Proof. destruct A; unfold A_cast_below_sg_to_below_sg_CI,
         cast_below_sg_to_below_sg_CI; simpl; try reflexivity.
       apply correct_cast_below_sg_C_to_below_sg_CI. 
Qed.

Theorem correct_cast_below_sg_to_below_sg_CS (S : Type) (A : @A_below_sg S) :
  cast_below_sg_to_below_sg_CS (A2C_below_sg A)
  =
  option_map A2C_below_sg_CS (A_cast_below_sg_to_below_sg_CS A).
Proof. destruct A; unfold A_cast_below_sg_to_below_sg_CS,
         cast_below_sg_to_below_sg_CS; simpl; try reflexivity.
       apply correct_cast_below_sg_C_to_below_sg_CS. 
Qed.


Theorem correct_cast_below_sg_to_below_sg_C (S : Type) (A : @A_below_sg S) :
  cast_below_sg_to_below_sg_C (A2C_below_sg A)
  =
  option_map A2C_below_sg_C (A_cast_below_sg_to_below_sg_C A).
Proof. destruct A; unfold A_cast_below_sg_to_below_sg_C,
         cast_below_sg_to_below_sg_C; simpl; try reflexivity. 
Qed.

End Combinators.

Section Commute. 

  Variable S : Type.

Lemma cast_up_sg_CS_A2C_commute (A : @A_below_sg_CS S) : 
  cast_up_sg_CS (A2C_below_sg_CS A)
  =
    A2C_sg_CS (A_cast_up_sg_CS A).
Proof. destruct A; unfold cast_up_sg_CS, A_cast_up_sg_CS; simpl.
       reflexivity.
Qed.       

Lemma cast_up_sg_CI_A2C_commute (A : @A_below_sg_CI S) : 
  cast_up_sg_CI (A2C_below_sg_CI A)
  =
    A2C_sg_CI (A_cast_up_sg_CI A).
Proof. destruct A; unfold cast_up_sg_CI, A_cast_up_sg_CI; simpl.
       reflexivity.
Qed.       

Lemma cast_up_sg_CNI_A2C_commute (A : @A_below_sg_CNI S) : 
  cast_up_sg_CNI (A2C_below_sg_CNI A)
  =
  A2C_sg_CNI (A_cast_up_sg_CNI A).
Proof. destruct A;
       unfold cast_up_sg_CNI, A_cast_up_sg_CNI; simpl.
       reflexivity.
Qed.       

Lemma cast_up_sg_C_A2C_commute (A : @A_below_sg_C S) : 
  cast_up_sg_C (A2C_below_sg_C A)
  =
    A2C_sg_C (A_cast_up_sg_C A).
Proof. destruct A; unfold cast_up_sg_C, A_cast_up_sg_C; simpl.
       - reflexivity.
       - rewrite cast_up_sg_CS_A2C_commute.
         rewrite correct_sg_C_from_sg_CS. 
         reflexivity.
       - rewrite cast_up_sg_CI_A2C_commute.
         rewrite correct_sg_C_from_sg_CI. 
         reflexivity.
       - rewrite cast_up_sg_CNI_A2C_commute.
         rewrite correct_sg_C_from_sg_CNI. 
         reflexivity.
Qed. 

Lemma cast_up_sg_A2C_commute (A : @A_below_sg S) : 
  cast_up_sg (A2C_below_sg A)
  =
  A2C_sg (A_cast_up_sg A).
Proof. destruct A; unfold cast_up_sg, A_cast_up_sg; simpl.
       - reflexivity.
       - rewrite cast_up_sg_C_A2C_commute.
         rewrite correct_sg_from_sg_C. 
         reflexivity.
Qed.
  
End Commute. 


End Verify.   
