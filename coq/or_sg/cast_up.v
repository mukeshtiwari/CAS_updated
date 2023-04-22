Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.

Require Import CAS.coq.or_sg.properties.
Require Import CAS.coq.or_sg.structures.


Section ACAS. 

Section Proofs.

Variables (S : Type) (eq lte : brel S) (times : binary_op S).   
    
Definition os_monotone_proofs_from_monotone_increasing_proofs
           (M : os_monotone_increasing_proofs S lte times) :
                os_monotone_proofs S lte times :=
{|
  A_mono_left_monotonic     :=  A_mono_inc_left_monotonic _ _ _ M 
; A_mono_right_monotonic    :=  A_mono_inc_right_monotonic _ _ _ M 
; A_mono_left_increasing_d  := inl (A_mono_inc_left_increasing _ _ _ M)
; A_mono_right_increasing_d := inl (A_mono_inc_right_increasing _ _ _ M)
|}.


End Proofs. 

  
End ACAS. 


Section CAS. 

Section Proofs.

Definition os_monotone_certs_from_monotone_increasing_certs {S : Type} 
           (M : @os_monotone_increasing_certificates S) : @os_monotone_certificates S :=
{|
  mono_left_monotonic     := Assert_Left_Monotone 
; mono_right_monotonic    := Assert_Right_Monotone 
; mono_left_increasing_d  := Certify_Left_Increasing
; mono_right_increasing_d := Certify_Right_Increasing 
|}.


End Proofs. 

  
End CAS. 


