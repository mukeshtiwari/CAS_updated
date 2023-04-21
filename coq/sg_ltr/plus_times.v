Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.     (* beq_nat *) 
Require Import Coq.Arith.Min.       (* why am I using min_comm??? *) 

Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.

Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.eqv.nat.
Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures.
Require Import CAS.coq.sg.plus.
Require Import CAS.coq.sg.times.
Require Import CAS.coq.bs.properties.
Require Import CAS.coq.bs.structures.
Require Import CAS.coq.bs.plus_times.
Require Import CAS.coq.tr.properties.
Require Import CAS.coq.tr.left.from_sg.
Require Import CAS.coq.st.properties.
Require Import CAS.coq.st.structures.
Section Theory.

Open Scope nat.   

Lemma slt_plus_times_distributive : 
        slt_distributive brel_eq_nat bop_plus (ltr_from_sg bop_times).
Proof. apply bop_plus_times_left_distributive. Qed. 

Lemma slt_plus_times_not_absorptive : 
        slt_not_absorptive brel_eq_nat bop_plus (ltr_from_sg bop_times).
Proof. destruct (bops_plus_times_not_left_right_absorptive) as [[a b] P].
       exists (b, a). unfold ltr_from_sg.
       exact P.
Defined.

Lemma slt_plus_times_not_strictly_absorptive : 
        slt_not_strictly_absorptive brel_eq_nat bop_plus (ltr_from_sg bop_times).
Proof. destruct slt_plus_times_not_absorptive as [[a b] A].
       exists (a, b). left. exact A. 
Defined.


Lemma slt_plus_times_exists_id_ann_equal : slt_exists_id_ann_equal brel_eq_nat bop_plus (ltr_from_sg bop_times).
Proof. exists 0. split.
       + apply bop_plus_zero_is_id. 
       + unfold ltr_is_ann, ltr_from_sg.
         intro l. destruct (bop_times_zero_is_ann l) as [A B]. 
         exact B.
Defined.

End Theory.

Section ACAS.

Definition slt_plus_times_left_semiring_proofs := 
{|
  A_left_semiring_distributive   := slt_plus_times_distributive
; A_left_semiring_not_absorptive := slt_plus_times_not_absorptive 
|}.

Open Scope string_scope. 

Definition A_slt_plus_times : @A_left_semiring nat nat :=
{|
      A_left_semiring_carrier         := A_eqv_nat 
    ; A_left_semiring_label           := A_eqv_nat 
    ; A_left_semiring_plus            := bop_plus
    ; A_left_semiring_trans           := ltr_from_sg bop_times
    ; A_left_semiring_plus_proofs     := A_sg_C_proofs_plus
    ; A_left_semiring_trans_proofs    := ltr_from_sg_proofs _ _ _ sg_proofs_times   
    ; A_left_semiring_exists_plus_ann_d := inr bop_plus_not_exists_ann 
    ; A_left_semiring_id_ann_proofs   := slt_plus_times_exists_id_ann_equal 
    ; A_left_semiring_proofs          := slt_plus_times_left_semiring_proofs
    ; A_left_semiring_ast             := Cas_ast ("slt_plus_times_FIX_AST", nil)
  |}.



End ACAS.

Section MACAS.

Definition A_mcas_slt_plus_times := A_SLT_Semiring A_slt_plus_times. 

End MACAS.
  
Section CAS.

  Open Scope string_scope.
  Open Scope nat_scope.

Definition slt_plus_times : @left_semiring nat nat :=
{|
      left_semiring_carrier           := eqv_eq_nat 
    ; left_semiring_label             := eqv_eq_nat 
    ; left_semiring_plus              := bop_plus
    ; left_semiring_trans             := ltr_from_sg bop_times
    ; left_semiring_plus_certs        := sg_C_certs_plus
    ; left_semiring_trans_certs       := ltr_from_sg_certs _ sg_certs_times   
    ; left_semiring_exists_plus_ann_d := Certify_Not_Exists_Ann 
    ; left_semiring_id_ann_certs      := Assert_Slt_Exists_Id_Ann_Equal 0
    ; left_semiring_certs             :=
        {|
          left_semiring_distributive   := Assert_Slt_Distributive 
        ; left_semiring_not_absorptive := Assert_Slt_Not_Absorptive (1, 1) 
        |}
    ; left_semiring_ast               := Cas_ast ("slt_plus_times_FIX_AST", nil)
  |}.

End CAS.

Section MCAS.

Definition mcas_slt_plus_times := SLT_Semiring slt_plus_times. 

End MCAS.
  
Section Verify.

Theorem correct_plus_times : 
  slt_plus_times = A2C_left_semiring A_slt_plus_times. 
Proof. compute. reflexivity. Qed.


Theorem correct_mcas_slt_plus_times : mcas_slt_plus_times = A2C_mcas_slt A_mcas_slt_plus_times.
Proof. compute. reflexivity. Qed. 


End Verify.   
