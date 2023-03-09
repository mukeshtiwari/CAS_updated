
Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.data.
Require Import CAS.coq.common.ast.
Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures. 

(* semigroups 

Current Implementation Hierarchy

sg     = semigroup 
sg_C   = commutative semigroup 
sg_CS  = commutative selective semigroup (is idempotent, of course) 
sg_CI  = commutative idempotent semigroup, not selective 
sg_CNI = commutative, not idempotent semigroup, 

           sg 
           |  
          sg_C
         / | \ 
        /  |  \ 
       /   |   \  
      /    |    \
  sg_CI sg_CNI  sg_CS 

*) 

Section AMCAS.

  (*
Definition A_classify_sg_C_proofs 
           (S : Type)
           (eq : brel S)
           (bop : binary_op S)
           (A : sg_C_proofs S eq bop) : below_sg_proofs S eq bop :=
match A_sg_C_idempotent_d _ _ _ A with 
| inl idem =>
  match A_sg_C_selective_d _ _ _ A with
  | inl sel => SG_CS_below_sg_proofs _ _ _
                {|    
                    A_sg_CS_associative        := A_sg_C_associative _ _ _ A 
                  ; A_sg_CS_congruence         := A_sg_C_congruence  _ _ _ A 
                  ; A_sg_CS_commutative        := A_sg_C_commutative  _ _ _ A 
                  ; A_sg_CS_selective          := sel 
                |}
  | inr nsel => SG_CI_below_sg_proofs _ _ _
                {|    
                    A_sg_CI_associative        := A_sg_C_associative _ _ _ A 
                  ; A_sg_CI_congruence         := A_sg_C_congruence  _ _ _ A 
                  ; A_sg_CI_commutative        := A_sg_C_commutative  _ _ _ A
                  ; A_sg_CI_idempotent         := idem 
                  ; A_sg_CI_not_selective      := nsel 
                |}
  end 
| inr _  => SG_C_below_sg_proofs _ _ _ A
end.


Definition A_classify_sg_proofs  
           (S : Type)
           (eq : brel S)
           (bop : binary_op S)
           (P : sg_proofs S eq bop) : below_sg_proofs S eq bop :=
match A_sg_commutative_d _ _ _ P with 
| inl comm => A_classify_sg_C_proofs _ _ _ 
   {| 
       A_sg_C_associative      := A_sg_associative _ _ _ P
     ; A_sg_C_congruence       := A_sg_congruence _ _ _ P
     ; A_sg_C_commutative      := comm 
     ; A_sg_C_anti_left_d      := A_sg_anti_left_d _ _ _ P
     ; A_sg_C_anti_right_d     := A_sg_anti_right_d _ _ _ P
     ; A_sg_C_selective_d      := A_sg_selective_d _ _ _ P
     ; A_sg_C_idempotent_d     := A_sg_idempotent_d _ _ _ P
     ; A_sg_C_cancel_d         := A_sg_left_cancel_d _ _ _ P
     ; A_sg_C_constant_d       := A_sg_left_constant_d _ _ _ P
   |}                                        
| inr _  => SG_below_sg_proofs _ _ _ P
end.
*) 
Definition A_classify_sg_CS {S : Type} (A : A_sg_CS S) : @A_below_sg_CS S :=
  A_Below_sg_CS_top A.


Definition A_classify_sg_CI {S : Type} (A : A_sg_CI S) : @A_below_sg_CI S :=
  A_Below_sg_CI_top A.

Definition A_classify_sg_CNI {S : Type} (A : A_sg_CNI S) : @A_below_sg_CNI S :=
  A_Below_sg_CNI_top A.

Definition A_classify_sg_C {S : Type} (B : A_sg_C S) : @A_below_sg_C S :=
  let P := A_sg_C_proofs _ B in 
  match A_sg_C_idempotent_d _ _ _ P with
      | inl idem =>
          match A_sg_C_selective_d _ _ _ P with
          | inl sel =>
              let C :=
                {|
                    A_sg_CS_eqv            := A_sg_C_eqv _ B 
                  ; A_sg_CS_bop            := A_sg_C_bop _ B 
                  ; A_sg_CS_exists_id_d    := A_sg_C_exists_id_d _ B
                  ; A_sg_CS_exists_ann_d   := A_sg_C_exists_ann_d _ B 
                  ; A_sg_CS_proofs         :=
                      {|
                         A_sg_CS_congruence  := A_sg_C_congruence _ _ _ P
                       ; A_sg_CS_associative := A_sg_C_associative _ _ _ P
                       ; A_sg_CS_commutative := A_sg_C_commutative _ _ _ P 
                       ; A_sg_CS_selective   := sel
                       |}
                  ; A_sg_CS_ast            := A_sg_C_ast _ B 
                |}       
                
              in A_Below_sg_C_sg_CS (A_classify_sg_CS C)
          | inr nsel =>
              let C :=
                {|
                    A_sg_CI_eqv            := A_sg_C_eqv _ B 
                  ; A_sg_CI_bop            := A_sg_C_bop _ B 
                  ; A_sg_CI_exists_id_d    := A_sg_C_exists_id_d _ B
                  ; A_sg_CI_exists_ann_d   := A_sg_C_exists_ann_d _ B 
                  ; A_sg_CI_proofs         :=
                      {|
                         A_sg_CI_congruence  := A_sg_C_congruence _ _ _ P
                       ; A_sg_CI_associative := A_sg_C_associative _ _ _ P
                       ; A_sg_CI_commutative := A_sg_C_commutative _ _ _ P 
                       ; A_sg_CI_idempotent  := idem
                       ; A_sg_CI_not_selective  := nsel
                       |}
                  ; A_sg_CI_ast            := A_sg_C_ast _ B 
                |}       
              in A_Below_sg_C_sg_CI (A_classify_sg_CI C)
          end 
  | inr nidem =>
      let C :=
        {|
          A_sg_CNI_eqv            := A_sg_C_eqv _ B 
        ; A_sg_CNI_bop            := A_sg_C_bop _ B 
        ; A_sg_CNI_exists_id_d    := A_sg_C_exists_id_d _ B
        ; A_sg_CNI_exists_ann_d   := A_sg_C_exists_ann_d _ B 
        ; A_sg_CNI_proofs         :=
            {|
              A_sg_CNI_congruence   := A_sg_C_congruence _ _ _ P
            ; A_sg_CNI_associative  := A_sg_C_associative _ _ _ P
            ; A_sg_CNI_commutative  := A_sg_C_commutative _ _ _ P 
            ; A_sg_CNI_not_idempotent := nidem
            ; A_sg_CNI_cancel_d     := A_sg_C_cancel_d _ _ _ P
            ; A_sg_CNI_constant_d   := A_sg_C_constant_d _ _ _ P
            ; A_sg_CNI_anti_left_d  := A_sg_C_anti_left_d _ _ _ P
            ; A_sg_CNI_anti_right_d := A_sg_C_anti_right_d _ _ _ P
            |}
        ; A_sg_CNI_ast            := A_sg_C_ast _ B 
        |} 
      in A_Below_sg_C_sg_CNI (A_classify_sg_CNI C)
  end. 


Definition A_classify_sg {S : Type} (B : A_sg S) : @A_below_sg S :=
      let P := A_sg_proofs _ B in 
      match A_sg_commutative_d _ _ _ P with
      | inl comm =>
          let C :=
            {|
              A_sg_C_eqv            := A_sg_eqv _ B 
            ; A_sg_C_bop            := A_sg_bop _ B 
            ; A_sg_C_exists_id_d    := A_sg_exists_id_d _ B
            ; A_sg_C_exists_ann_d   := A_sg_exists_ann_d _ B 
            ; A_sg_C_proofs         :=
                {|
                  A_sg_C_congruence   := A_sg_congruence _ _ _ P
                ; A_sg_C_associative  := A_sg_associative _ _ _ P
                ; A_sg_C_commutative  := comm
                ; A_sg_C_selective_d  := A_sg_selective_d _ _ _ P 
                ; A_sg_C_idempotent_d := A_sg_idempotent_d _ _ _ P
                ; A_sg_C_anti_left_d  := A_sg_anti_left_d _ _ _ P
                ; A_sg_C_anti_right_d := A_sg_anti_right_d _ _ _ P
                ; A_sg_C_cancel_d     := A_sg_left_cancel_d _ _ _ P
                ; A_sg_C_constant_d   := A_sg_left_constant_d _ _ _ P
                |}
            ; A_sg_C_ast            := A_sg_ast _ B 
            |}       
          in A_Below_sg_sg_C (A_classify_sg_C C)
      | _ => A_Below_sg_top B 
      end.

End AMCAS.                                                                                            


Section MCAS.

Definition classify_sg_CS {S : Type} (A : @sg_CS S) : @below_sg_CS S :=
  Below_sg_CS_top A. 


Definition classify_sg_CI {S : Type} (A : @sg_CI S) : @below_sg_CI S :=
  Below_sg_CI_top A.

Definition classify_sg_CNI {S : Type} (A : @sg_CNI S) : @below_sg_CNI S :=
  Below_sg_CNI_top A. 

Definition classify_sg_C {S : Type} (B : @sg_C S) : @below_sg_C S :=
  let P := sg_C_certs B in 
  match sg_C_idempotent_d P with
      | Certify_Idempotent =>
          match sg_C_selective_d P with
          | Certify_Selective =>
              let C :=
                {|
                    sg_CS_eqv            := sg_C_eqv B 
                  ; sg_CS_bop            := sg_C_bop B 
                  ; sg_CS_exists_id_d    := sg_C_exists_id_d B
                  ; sg_CS_exists_ann_d   := sg_C_exists_ann_d B 
                  ; sg_CS_certs         :=
                      {|
                         sg_CS_congruence  := sg_C_congruence P
                       ; sg_CS_associative := sg_C_associative P
                       ; sg_CS_commutative := sg_C_commutative P 
                       ; sg_CS_selective   := Assert_Selective
                       |}
                  ; sg_CS_ast            := sg_C_ast B 
                |}       
                
              in Below_sg_C_sg_CS (classify_sg_CS C)
          | Certify_Not_Selective p =>
              let C :=
                {|
                    sg_CI_eqv            := sg_C_eqv B 
                  ; sg_CI_bop            := sg_C_bop B 
                  ; sg_CI_exists_id_d    := sg_C_exists_id_d B
                  ; sg_CI_exists_ann_d   := sg_C_exists_ann_d B 
                  ; sg_CI_certs         :=
                      {|
                         sg_CI_congruence  := sg_C_congruence P
                       ; sg_CI_associative := sg_C_associative P
                       ; sg_CI_commutative := sg_C_commutative P 
                       ; sg_CI_idempotent  := Assert_Idempotent
                       ; sg_CI_not_selective  := Assert_Not_Selective p
                       |}
                  ; sg_CI_ast            := sg_C_ast B 
                |}       
              in Below_sg_C_sg_CI (classify_sg_CI C)
          end 
  | Certify_Not_Idempotent i =>
      let C :=
        {|
          sg_CNI_eqv            := sg_C_eqv B 
        ; sg_CNI_bop            := sg_C_bop B 
        ; sg_CNI_exists_id_d    := sg_C_exists_id_d B
        ; sg_CNI_exists_ann_d   := sg_C_exists_ann_d B 
        ; sg_CNI_certs         :=
            {|
              sg_CNI_congruence   := sg_C_congruence P
            ; sg_CNI_associative  := sg_C_associative P
            ; sg_CNI_commutative  := sg_C_commutative P 
            ; sg_CNI_not_idempotent := Assert_Not_Idempotent i
            ; sg_CNI_cancel_d     := sg_C_cancel_d P
            ; sg_CNI_constant_d   := sg_C_constant_d P
            ; sg_CNI_anti_left_d  := sg_C_anti_left_d P
            ; sg_CNI_anti_right_d := sg_C_anti_right_d P
            |}
        ; sg_CNI_ast            := sg_C_ast B 
        |} 
      in Below_sg_C_sg_CNI (classify_sg_CNI C)
  end. 

Definition classify_sg {S : Type} (B : @sg S) : @below_sg S :=
  let P := sg_certs B in 
  match sg_commutative_d P with
      | Certify_Commutative =>
          let C :=
            {|
              sg_C_eqv            := sg_eqv B 
            ; sg_C_bop            := sg_bop B 
            ; sg_C_exists_id_d    := sg_exists_id_d B
            ; sg_C_exists_ann_d   := sg_exists_ann_d B 
            ; sg_C_certs         :=
                {|
                  sg_C_congruence   := sg_congruence P
                ; sg_C_associative  := sg_associative P
                ; sg_C_commutative  := Assert_Commutative
                ; sg_C_selective_d  := sg_selective_d P 
                ; sg_C_idempotent_d := sg_idempotent_d P
                ; sg_C_anti_left_d  := sg_anti_left_d P
                ; sg_C_anti_right_d := sg_anti_right_d P
                ; sg_C_cancel_d     := sg_left_cancel_d P
                ; sg_C_constant_d   := sg_left_constant_d P
                |}
            ; sg_C_ast            := sg_ast B 
            |}       
          in Below_sg_sg_C (classify_sg_C C)
      | _ => Below_sg_top B
  end.

End MCAS.                                                                                            

Section Verify.
(*
Section Proofs.   
Variables {S : Type}
          (eq : brel S)
          (bop : binary_op S).

Lemma correct_sg_certificates_classify_sg_C (s : sg_C_proofs S eq bop) : 
  classify_sg_C_certificates _ (P2C_sg_C S eq bop s) =
  P2C_below_sg_proofs S eq bop (A_classify_sg_C_proofs S eq bop s).
Proof. destruct s.
       destruct A_sg_C_idempotent_d as [A | [i A]];
       destruct A_sg_C_selective_d as [B | [[a b] B]]; reflexivity. 
Qed.


Lemma correct_sg_certificates_classify_sg (s : sg_proofs S eq bop) : 
  classify_sg_certificates _ (P2C_sg S eq bop s) =
  P2C_below_sg_proofs S eq bop (A_classify_sg_proofs S eq bop s).
Proof. destruct s.
       destruct A_sg_commutative_d as [B | [[a b] B]]; try reflexivity.
       destruct A_sg_idempotent_d as [A | [i A]];
       destruct A_sg_selective_d as [C | [[a b] C]]; reflexivity. 
Qed.

End Proofs.
*) 
Section Structures.   

  Variable (S : Type).

  Lemma correct_classify_sg_CS (s : A_sg_CS S) : 
  classify_sg_CS (A2C_sg_CS s)
  =
  A2C_below_sg_CS (A_classify_sg_CS s).
  Proof. destruct s. simpl. reflexivity. Qed. 

  Lemma correct_classify_sg_CI (s : A_sg_CI S) : 
  classify_sg_CI (A2C_sg_CI s)
  =
  A2C_below_sg_CI (A_classify_sg_CI s).
  Proof. destruct s. simpl. reflexivity. Qed. 

  Lemma correct_classify_sg_CNI (s : A_sg_CNI S) : 
  classify_sg_CNI (A2C_sg_CNI s)
  =
  A2C_below_sg_CNI (A_classify_sg_CNI s).
  Proof. destruct s. simpl. reflexivity. Qed. 

Lemma correct_classify_sg_C (s : A_sg_C S) : 
  classify_sg_C (A2C_sg_C s)
  =
  A2C_below_sg_C (A_classify_sg_C s).
Proof. destruct s;
       unfold A_classify_sg_C, classify_sg_C, A2C_sg_C, A2C_below_sg_C; simpl.
       - destruct A_sg_C_proofs.
         destruct A_sg_C_selective_d as [sel | [p A]];
         destruct A_sg_C_idempotent_d as [idem | [i C]];
         simpl; reflexivity. 
Qed.          

Lemma correct_classify_sg (s : A_sg S) : 
  classify_sg (A2C_sg s)
  =
  A2C_below_sg (A_classify_sg s).
Proof. destruct s.
       unfold A_classify_sg, classify_sg, A2C_below_sg, A2C_sg. 
       destruct A_sg_proofs.
       destruct A_sg_commutative_d as [comm| [p NC]]; 
         try reflexivity.
       destruct A_sg_selective_d as [sel | [p A]];
       destruct A_sg_idempotent_d as [idem | [i C]];
       simpl; reflexivity. 
Qed.

End Structures. 

End Verify.   
