
Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.data.
Require Import CAS.coq.common.ast.

Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.

Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures.

Require Import CAS.coq.bs.properties.
Require Import CAS.coq.bs.structures.
Require Import CAS.coq.bs.cast. 


Section AMCAS.

Definition A_classify_bs_CS {S : Type} (A : @A_bs_CS S) : @A_below_bs_CS S :=
  A_Below_bs_CS_top A.

Definition A_classify_bs_CI {S : Type} (A : @A_bs_CI S) : @A_below_bs_CI S :=
  A_Below_bs_CI_top A.

Definition A_classify_bs {S : Type} (B : @A_bs S) : @A_below_bs S :=
  let P := A_bs_plus_props B in 
  match A_sg_C_idempotent_d _ _ _ P with
  | inr _ => A_Below_bs_top B 
  | inl idem =>
      match A_sg_C_selective_d _ _ _ P with
      | inl sel =>
              let C :=
                {|
                    A_bs_CS_eqv            := A_bs_eqv B 
                  ; A_bs_CS_plus           := A_bs_plus B
                  ; A_bs_CS_times          := A_bs_times B 
                  ; A_bs_CS_plus_props     :=
                      {|
                         A_sg_CS_congruence  := A_sg_C_congruence _ _ _ P
                       ; A_sg_CS_associative := A_sg_C_associative _ _ _ P
                       ; A_sg_CS_commutative := A_sg_C_commutative _ _ _ P 
                       ; A_sg_CS_selective   := sel
                      |}
                  ; A_bs_CS_times_props     := A_bs_times_props B
                  ; A_bs_CS_id_ann_props    := A_bs_id_ann_props B                                                                 
                  ; A_bs_CS_props           := A_bs_props B                                                               
                  ; A_bs_CS_ast             := A_bs_ast B 
                |}                       
              in A_Below_bs_bs_CS (A_classify_bs_CS C)
      | inr nsel =>
          let C :=
                {|
                  A_bs_CI_eqv            := A_bs_eqv B
                  ; A_bs_CI_plus           := A_bs_plus B
                  ; A_bs_CI_times          := A_bs_times B          
                  ; A_bs_CI_plus_props     :=
                      {|
                         A_sg_CI_congruence  := A_sg_C_congruence _ _ _ P
                       ; A_sg_CI_associative := A_sg_C_associative _ _ _ P
                       ; A_sg_CI_commutative := A_sg_C_commutative _ _ _ P 
                       ; A_sg_CI_idempotent := idem
                       ; A_sg_CI_not_selective := nsel 
                      |}
                  ; A_bs_CI_times_props     := A_bs_times_props B
                  ; A_bs_CI_id_ann_props    := A_bs_id_ann_props B                                                                 
                  ; A_bs_CI_props           := A_bs_props B                                                               
                  ; A_bs_CI_ast             := A_bs_ast B 
                |}       
          in A_Below_bs_bs_CI (A_classify_bs_CI C)
      end 
  end. 

End AMCAS.                                                                                            


Section MCAS.

Definition classify_bs_CS {S : Type} (A : @bs_CS S) : @below_bs_CS S :=
  Below_bs_CS_top A.

Definition classify_bs_CI {S : Type} (A : @bs_CI S) : @below_bs_CI S :=
  Below_bs_CI_top A.

Definition classify_bs {S : Type} (B : @bs S) : @below_bs S :=
  let P := bs_plus_props B in 
  match sg_C_idempotent_d   P with
  | Certify_Not_Idempotent _ => Below_bs_top B 
  | Certify_Idempotent =>
      match sg_C_selective_d   P with
      | Certify_Selective =>
              let C :=
                {|
                    bs_CS_eqv            := bs_eqv B 
                  ; bs_CS_plus           := bs_plus B
                  ; bs_CS_times          := bs_times B 
                  ; bs_CS_plus_props     :=
                      {|
                         sg_CS_congruence  := sg_C_congruence   P
                       ; sg_CS_associative := sg_C_associative   P
                       ; sg_CS_commutative := sg_C_commutative   P 
                       ; sg_CS_selective   := Assert_Selective 
                      |}
                  ; bs_CS_times_props     := bs_times_props B
                  ; bs_CS_id_ann_props    := bs_id_ann_props B                                                                 
                  ; bs_CS_props           := bs_props B                                                               
                  ; bs_CS_ast             := bs_ast B 
                |}                       
              in Below_bs_bs_CS (classify_bs_CS C)
      | Certify_Not_Selective ce =>
          let C :=
                {|
                  bs_CI_eqv            := bs_eqv B
                  ; bs_CI_plus           := bs_plus B
                  ; bs_CI_times          := bs_times B          
                  ; bs_CI_plus_props     :=
                      {|
                         sg_CI_congruence  := sg_C_congruence   P
                       ; sg_CI_associative := sg_C_associative   P
                       ; sg_CI_commutative := sg_C_commutative   P 
                       ; sg_CI_idempotent := Assert_Idempotent
                       ; sg_CI_not_selective := Assert_Not_Selective ce 
                      |}
                  ; bs_CI_times_props     := bs_times_props B
                  ; bs_CI_id_ann_props    := bs_id_ann_props B                                                                 
                  ; bs_CI_props           := bs_props B                                                               
                  ; bs_CI_ast             := bs_ast B 
                |}       
          in Below_bs_bs_CI (classify_bs_CI C)
      end 
  end. 

End MCAS.                                                                                            

Section Verify.

  Variable (S : Type).

  Lemma correct_classify_bs_CS (A : @A_bs_CS S) : 
  classify_bs_CS (A2C_bs_CS A)
  =
  A2C_below_bs_CS (A_classify_bs_CS A).
  Proof. destruct A. simpl. reflexivity. Qed. 

  Lemma correct_classify_bs_CI (A : @A_bs_CI S) : 
  classify_bs_CI (A2C_bs_CI A)
  =
  A2C_below_bs_CI (A_classify_bs_CI A).
  Proof. destruct A. simpl. reflexivity. Qed. 

  Lemma correct_classify_bs (A : @A_bs S) : 
  classify_bs (A2C_bs A)
  =
  A2C_below_bs (A_classify_bs A).
  Proof. destruct A.
       unfold A_classify_bs, classify_bs, A2C_below_bs, A2C_bs. 
       destruct A_bs_plus_props; simpl. 
       destruct A_sg_C_selective_d as [sel | [p A]];
       destruct A_sg_C_idempotent_d as [idem | [i C]];
       simpl; reflexivity. 
Qed.

End Verify.   
