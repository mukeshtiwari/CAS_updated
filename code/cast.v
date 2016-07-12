Require Import CAS.code.basic_types. 
Require Import CAS.code.bop.  
Require Import CAS.code.cef.  
Require Import CAS.code.ast. 
Require Import CAS.code.certificates.
Require Import CAS.code.cert_records. 
Require Import CAS.code.cas_records. 



(* IMPLICATIONS *) 



(* UPCASTS *) 


Definition sg_certs_from_sg_C_certs : ∀ (S : Type), brel S -> binary_op S -> eqv_certificates S -> sg_C_certificates S -> sg_certificates S 
:= λ S r b eqvS sgS, 
let ntS := eqv_nontrivial S eqvS in 
match certify_nontrivial_witness S ntS, certify_nontrivial_negate S ntS with 
| Certify_Witness s, Certify_Negate f => 
{|
  sg_associative      := Assert_Associative S 
; sg_congruence       := Assert_Bop_Congruence S 
; sg_commutative_d    := Certify_Commutative S 
; sg_selective_d      := sg_C_selective_d S sgS    
; sg_is_left_d        := Certify_Not_Is_Left S (cef_commutative_implies_not_is_left S r b s f)
; sg_is_right_d       := Certify_Not_Is_Right S (cef_commutative_implies_not_is_right S r b s f)
; sg_idempotent_d     := sg_C_idempotent_d S sgS    
; sg_exists_id_d      := sg_C_exists_id_d S sgS    
; sg_exists_ann_d     := sg_C_exists_ann_d S sgS    
; sg_left_cancel_d    := sg_C_left_cancel_d S sgS    
; sg_right_cancel_d   := sg_C_right_cancel_d S sgS    
; sg_left_constant_d  := sg_C_left_constant_d S sgS
; sg_right_constant_d := sg_C_right_constant_d S sgS
; sg_anti_left_d      := sg_C_anti_left_d S sgS
; sg_anti_right_d     := sg_C_anti_right_d S sgS
|}
end. 


Definition sg_from_sg_C: ∀ (S : Type),  sg_C S -> sg S 
:= λ S sg_CS, 
   {| 
     sg_eq    := sg_C_eqv S sg_CS
   ; sg_bop   := sg_C_bop S sg_CS
   ; sg_certs := sg_certs_from_sg_C_certs S 
                    (eqv_eq S (sg_C_eqv S sg_CS)) 
                    (sg_C_bop S sg_CS) 
                    (eqv_certs S (sg_C_eqv S sg_CS))
                    (sg_C_certs S sg_CS) 
   ; sg_ast   := Ast_sg_from_sg_C (sg_C_ast S sg_CS)
   |}. 




Definition sg_C_certs_from_sg_CI_certs : ∀ (S : Type), brel S -> binary_op S -> eqv_certificates S -> sg_CI_certificates S -> sg_C_certificates S 
:= λ S r b eqvS sgS, 
let ntS := eqv_nontrivial S eqvS in 
match certify_nontrivial_witness S ntS, certify_nontrivial_negate S ntS with 
| Certify_Witness s, Certify_Negate f => 
{|
  sg_C_associative      := Assert_Associative S 
; sg_C_congruence       := Assert_Bop_Congruence S 
; sg_C_commutative      := Assert_Commutative S 
; sg_C_selective_d      := sg_CI_selective_d S sgS    
; sg_C_idempotent_d     := Certify_Idempotent S 
; sg_C_exists_id_d      := sg_CI_exists_id_d S sgS    
; sg_C_exists_ann_d     := sg_CI_exists_ann_d S sgS    
; sg_C_left_cancel_d    := 
     Certify_Not_Left_Cancellative S 
        (match sg_CI_selective_d S sgS with 
        | Certify_Selective => 
             cef_selective_and_commutative_imply_not_left_cancellative S r b s f
        | Certify_Not_Selective (s1, s2) => 
             cef_idempotent_and_commutative_and_not_selective_imply_not_left_cancellative S b s1 s2
        end) 
; sg_C_right_cancel_d   := 
     Certify_Not_Right_Cancellative S 
        (match sg_CI_selective_d S sgS with 
        | Certify_Selective => 
             cef_selective_and_commutative_imply_not_right_cancellative S r b s f
        | Certify_Not_Selective (s1, s2) => 
             cef_idempotent_and_commutative_and_not_selective_imply_not_right_cancellative S b s1 s2
        end) 
; sg_C_left_constant_d  := 
     Certify_Not_Left_Constant S (cef_idempotent_and_commutative_imply_not_left_constant S r b s f)
; sg_C_right_constant_d := 
     Certify_Not_Right_Constant S (cef_idempotent_and_commutative_imply_not_right_constant S r b s f)
; sg_C_anti_left_d      := Certify_Not_Anti_Left S (cef_idempotent_implies_not_anti_left S s)
; sg_C_anti_right_d     := Certify_Not_Anti_Right S (cef_idempotent_implies_not_anti_right S s)
|}
end. 

Definition sg_C_from_sg_CI: ∀ (S : Type),  sg_CI S -> sg_C S 
:= λ S sgS, 
   {| 
     sg_C_eqv   := sg_CI_eqv S sgS
   ; sg_C_bop   := sg_CI_bop S sgS
   ; sg_C_certs := sg_C_certs_from_sg_CI_certs S 
                      (eqv_eq S (sg_CI_eqv S sgS)) 
                      (sg_CI_bop S sgS) 
                      (eqv_certs S (sg_CI_eqv S sgS))
                      (sg_CI_certs S sgS) 
   ; sg_C_ast   := Ast_sg_C_from_sg_CI (sg_CI_ast S sgS)
   |}. 





Definition sg_CI_certs_from_sg_CS_certs : ∀ (S : Type), sg_CS_certificates S -> sg_CI_certificates S 
:= λ S sgS, 
{|
  sg_CI_associative        := Assert_Associative S 
; sg_CI_congruence         := Assert_Bop_Congruence S 
; sg_CI_commutative        := Assert_Commutative S 
; sg_CI_idempotent         := Assert_Idempotent S 
; sg_CI_selective_d        := Certify_Selective S 
; sg_CI_exists_id_d        := sg_CS_exists_id_d S sgS    
; sg_CI_exists_ann_d       := sg_CS_exists_ann_d S sgS    
|}. 

Definition sg_CI_from_sg_CS: ∀ (S : Type),  sg_CS S -> sg_CI S 
:= λ S sgS, 
   {| 
     sg_CI_eqv   := sg_CS_eqv S sgS
   ; sg_CI_bop   := sg_CS_bop S sgS
   ; sg_CI_certs := sg_CI_certs_from_sg_CS_certs S (sg_CS_certs S sgS) 
   ; sg_CI_ast   := Ast_sg_CI_from_sg_CS (sg_CS_ast S sgS)
   |}. 


Definition sg_C_certs_from_sg_CK_certs : ∀ (S : Type), brel S -> binary_op S -> eqv_certificates S -> sg_CK_certificates S -> sg_C_certificates S 
:= λ S r b eqvS sgS, 
let ntS := eqv_nontrivial S eqvS in 
match certify_nontrivial_witness S ntS, certify_nontrivial_negate S ntS with 
| Certify_Witness s, Certify_Negate f => 
let ni := match sg_CK_exists_id_d S sgS with 
          | Certify_Exists_Id i => cef_cancellative_and_exists_id_imply_not_idempotent S r s i f
          | Certify_Not_Exists_Id => s 
          end 
in 
{|
  sg_C_associative      := Assert_Associative S 
; sg_C_congruence       := Assert_Bop_Congruence S 
; sg_C_commutative      := Assert_Commutative S 

; sg_C_idempotent_d     := Certify_Not_Idempotent S ni 
; sg_C_selective_d      := Certify_Not_Selective S 
                              (cef_not_idempotent_implies_not_selective S ni) 

; sg_C_exists_id_d      := sg_CK_exists_id_d S sgS
; sg_C_exists_ann_d     := Certify_Not_Exists_Ann S 

; sg_C_left_constant_d  := Certify_Not_Left_Constant S 
                              (cef_left_cancellative_implies_not_left_constant S s f) 
; sg_C_right_constant_d := Certify_Not_Right_Constant S 
                              (cef_right_cancellative_implies_not_right_constant S s f) 

; sg_C_left_cancel_d    := Certify_Left_Cancellative S 
; sg_C_right_cancel_d   := Certify_Right_Cancellative S 
; sg_C_anti_left_d      := sg_CK_anti_left_d S sgS 
; sg_C_anti_right_d     := sg_CK_anti_right_d S sgS 
|}
end. 




Definition sg_C_from_sg_CK: ∀ (S : Type),  sg_CK S -> sg_C S 
:= λ S sg, 
   {| 
     sg_C_eqv   := sg_CK_eqv S sg
   ; sg_C_bop   := sg_CK_bop S sg
   ; sg_C_certs := sg_C_certs_from_sg_CK_certs S 
                      (eqv_eq S (sg_CK_eqv S sg))
                      (sg_CK_bop S sg)
                      (eqv_certs S (sg_CK_eqv S sg)) 
                      (sg_CK_certs S sg) 
   ; sg_C_ast   := Ast_sg_C_from_sg_CK (sg_CK_ast S sg)
   |}. 




(* DERIVED UPCASTS *) 

Definition sg_from_sg_CI: ∀ (S : Type),  sg_CI S -> sg S 
:= λ S sgS, sg_from_sg_C S (sg_C_from_sg_CI S sgS).  

Definition sg_from_sg_CK: ∀ (S : Type),  sg_CK S -> sg S 
:= λ S sgS, sg_from_sg_C S (sg_C_from_sg_CK S sgS).  

Definition sg_C_from_sg_CS: ∀ (S : Type),  sg_CS S -> sg_C S 
:= λ S sgS, sg_C_from_sg_CI S (sg_CI_from_sg_CS S sgS ). 

Definition sg_from_sg_CS: ∀ (S : Type),  sg_CS S -> sg S 
:= λ S sgS, sg_from_sg_C S (sg_C_from_sg_CS S sgS).  



(* 
Definition sg_certs_from_sg_CI_certs : ∀ (S : Type), sg_CI_certs S -> sg_certs S 
:= λ S sg_CIS, sg_certs_from_sg_C_certs S (sg_C_certs_from_sg_CI_certs S sg_CIS).  

Definition sg_C_certs_from_sg_CS_certs : ∀ (S : Type),  sg_CS_certs S -> sg_C_certs S 
:= λ S sg_CSS, sg_C_certs_from_sg_CI_certs S (sg_CI_certs_from_sg_CS_certs S sg_CSS ). 

Definition sg_certs_from_sg_CS_certs : ∀ (S : Type),  sg_CS_certs S -> sg_certs S 
:= λ S sg_CSS, sg_certs_from_sg_C_certs S (sg_C_certs_from_sg_CS_certs S sg_CSS).  
*) 


(* DOWNCASTS *) 

Definition sg_C_certs_option_from_sg_certs : ∀ (S : Type), sg_certificates S -> option (sg_C_certificates S) 
:= λ S sgS, 
   match sg_commutative_d S sgS with 
   | Certify_Commutative => Some
      {|
        sg_C_associative      := Assert_Associative S 
      ; sg_C_congruence       := Assert_Bop_Congruence S 
      ; sg_C_commutative      := Assert_Commutative S 
      ; sg_C_selective_d      := sg_selective_d S sgS    
      ; sg_C_idempotent_d     := sg_idempotent_d S sgS    
      ; sg_C_exists_id_d      := sg_exists_id_d S sgS    
      ; sg_C_exists_ann_d     := sg_exists_ann_d S sgS   
      ; sg_C_left_cancel_d    := sg_left_cancel_d S sgS    
      ; sg_C_right_cancel_d   := sg_right_cancel_d S sgS    
      ; sg_C_left_constant_d  := sg_left_constant_d S sgS
      ; sg_C_right_constant_d := sg_right_constant_d S sgS
      ; sg_C_anti_left_d      := sg_anti_left_d  S sgS
      ; sg_C_anti_right_d     := sg_anti_right_d S sgS
     |}
   | _ => None
   end . 

Definition sg_C_option_from_sg: ∀ (S : Type),  sg S -> option (sg_C S) 
:= λ S sgS, 
   match sg_C_certs_option_from_sg_certs S (sg_certs S sgS) with 
   | None => None
   | Some c => Some
      {| 
        sg_C_eqv   := sg_eq S sgS
      ; sg_C_bop   := sg_bop S sgS
      ; sg_C_certs := c 
      ; sg_C_ast   := Ast_sg_C_from_sg (sg_ast S sgS)
      |}
   end. 



Definition sg_CI_certs_option_from_sg_C_certs : ∀ (S : Type), sg_C_certificates S -> option (sg_CI_certificates S) 
:= λ S sg_CS, 
   match sg_C_idempotent_d S sg_CS with 
   | Certify_Idempotent => Some
      {|
        sg_CI_associative        := Assert_Associative S 
      ; sg_CI_congruence         := Assert_Bop_Congruence S 
      ; sg_CI_commutative        := Assert_Commutative S 
      ; sg_CI_idempotent         := Assert_Idempotent S 
      ; sg_CI_selective_d        := sg_C_selective_d S sg_CS    
      ; sg_CI_exists_id_d        := sg_C_exists_id_d S sg_CS    
      ; sg_CI_exists_ann_d       := sg_C_exists_ann_d S sg_CS    
     |}
   | _ => None
   end. 

Definition sg_CI_option_from_sg_C: ∀ (S : Type),  sg_C S -> option (sg_CI S) 
:= λ S sg_CS, 
   match sg_CI_certs_option_from_sg_C_certs S (sg_C_certs S sg_CS) with 
   | None => None
   | Some certs => Some
      {| 
        sg_CI_eqv   := sg_C_eqv S sg_CS
      ; sg_CI_bop   := sg_C_bop S sg_CS
      ; sg_CI_certs := certs 
      ; sg_CI_ast   := Ast_sg_CI_from_sg_C (sg_C_ast S sg_CS)
      |}
   end. 


Definition sg_CS_certs_option_from_sg_CI_certs : ∀ (S : Type), sg_CI_certificates S -> option (sg_CS_certificates S) 
:= λ S sg_CIS, 
   match sg_CI_selective_d S sg_CIS with 
   | Certify_Selective => Some
      {|
        sg_CS_associative        := Assert_Associative S 
      ; sg_CS_congruence         := Assert_Bop_Congruence S 
      ; sg_CS_commutative        := Assert_Commutative S 
      ; sg_CS_selective          := Assert_Selective S 
      ; sg_CS_exists_id_d        := sg_CI_exists_id_d S sg_CIS    
      ; sg_CS_exists_ann_d       := sg_CI_exists_ann_d S sg_CIS    
     |}
   | _ => None
   end . 



Definition sg_CS_option_from_sg_CI: ∀ (S : Type),  sg_CI S -> option (sg_CS S) 
:= λ S sg_CIS, 
   match sg_CS_certs_option_from_sg_CI_certs S (sg_CI_certs S sg_CIS) with 
   | None => None
   | Some certs => Some
      {| 
        sg_CS_eqv   := sg_CI_eqv S sg_CIS
      ; sg_CS_bop   := sg_CI_bop S sg_CIS
      ; sg_CS_certs := certs 
      ; sg_CS_ast   := Ast_sg_CS_from_sg_CI (sg_CI_ast S sg_CIS)
      |}
   end. 


Definition sg_CK_certs_option_from_sg_C_certs : ∀ (S : Type), sg_C_certificates S -> option (sg_CK_certificates S) 
:= λ S sgS, 
   match sg_C_left_cancel_d S sgS with 
   | Certify_Left_Cancellative => Some
      {|
        sg_CK_associative        := sg_C_associative S sgS    
      ; sg_CK_congruence         := sg_C_congruence S sgS    
      ; sg_CK_commutative        := sg_C_commutative S sgS    
      ; sg_CK_left_cancel        := Assert_Left_Cancellative S
      ; sg_CK_exists_id_d        := sg_C_exists_id_d S sgS    
      ; sg_CK_anti_left_d        := sg_C_anti_left_d S sgS   
      ; sg_CK_anti_right_d       := sg_C_anti_right_d S sgS   
     |}
   |  _ => None
   end . 


Definition sg_CK_option_from_sg_C: ∀ (S : Type),  sg_C S -> option (sg_CK S) 
:= λ S sgS, 
   match sg_CK_certs_option_from_sg_C_certs S (sg_C_certs S sgS) with 
   | None => None
   | Some c => Some
      {| 
        sg_CK_eqv         := sg_C_eqv S sgS
      ; sg_CK_bop         := sg_C_bop S sgS
      ; sg_CK_certs       := c
      ; sg_CK_ast         := Ast_sg_CK_from_sg_C (sg_C_ast S sgS)
      |}
   end. 


(* DERIVED DOWNCASTS *) 

Definition sg_CI_option_from_sg: ∀ (S : Type),  sg S -> option (sg_CI S) 
:= λ S sgS, 
   match sg_C_option_from_sg S sgS with 
   | None => None
   | Some sgS => sg_CI_option_from_sg_C S sgS 
   end. 


Definition sg_CK_option_from_sg: ∀ (S : Type),  sg S -> option (sg_CK S) 
:= λ S sgS, 
   match sg_C_option_from_sg S sgS with 
   | None => None
   | Some sgS => sg_CK_option_from_sg_C S sgS 
   end. 


Definition sg_CS_option_from_sg_C : ∀ (S : Type),  sg_C S -> option (sg_CS S) 
:= λ S sgS, 
   match sg_CI_option_from_sg_C S sgS with 
   | None => None
   | Some sgS => sg_CS_option_from_sg_CI S sgS 
   end. 


Definition sg_CS_option_from_sg: ∀ (S : Type),  sg S -> option (sg_CS S) 
:= λ S sgS, 
   match sg_CI_option_from_sg S sgS with 
   | None => None
   | Some sgS => sg_CS_option_from_sg_CI S sgS 
   end. 


