
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
let bsP     := A_bs_CS_props A in
let id_annP := A_bs_CS_id_ann_props A in   
match A_id_ann_plus_times_d _ _ _ id_annP, A_id_ann_times_plus_d _ _ _ id_annP with
|  A_Id_Ann_Equal _ _ _ ZeroP, A_Id_Ann_Equal _ _ _ OneP =>
    match A_bs_left_distributive_d _ _ _ bsP with 
    | inl ld =>
        match A_bs_right_distributive_d _ _ _ bsP with 
        | inl rd =>
            A_Below_bs_CS_spa
              {|
                A_spa_eqv := A_bs_CS_eqv A
              ; A_spa_plus := A_bs_CS_plus A
              ; A_spa_times := A_bs_CS_times A
              ; A_spa_plus_props := A_bs_CS_plus_props A
              ; A_spa_times_props := A_bs_CS_times_props A
              ; A_spa_id_ann_props :=
                  {|
                    A_bounded_plus_id_is_times_ann := ZeroP
                  ; A_bounded_times_id_is_plus_ann := OneP 
                  |}
              ; A_spa_props :=
                  {|
                    A_pa_left_distributive := ld
                  ; A_pa_right_distributive := rd
                  |}
              ; A_spa_ast := A_bs_CS_ast A                                                               
              |} 
        | inr _ => A_Below_bs_CS_top A
        end 
    | inr _ => A_Below_bs_CS_top A
    end 
| _, _ => A_Below_bs_CS_top A
end.                             

Definition A_classify_bs_CI {S : Type} (A : @A_bs_CI S) : @A_below_bs_CI S :=
let bsP     := A_bs_CI_props A in
let id_annP := A_bs_CI_id_ann_props A in   
match A_id_ann_plus_times_d _ _ _ id_annP, A_id_ann_times_plus_d _ _ _ id_annP with
|  A_Id_Ann_Equal _ _ _ ZeroP, A_Id_Ann_Equal _ _ _ OneP =>
    match A_bs_left_distributive_d _ _ _ bsP with 
    | inl ld =>
        match A_bs_right_distributive_d _ _ _ bsP with 
        | inl rd =>
            A_Below_bs_CI_pa
              {|
                A_pa_eqv := A_bs_CI_eqv A
              ; A_pa_plus := A_bs_CI_plus A
              ; A_pa_times := A_bs_CI_times A
              ; A_pa_plus_props := A_bs_CI_plus_props A
              ; A_pa_times_props := A_bs_CI_times_props A
              ; A_pa_id_ann_props :=
                  {|
                    A_bounded_plus_id_is_times_ann := ZeroP
                  ; A_bounded_times_id_is_plus_ann := OneP 
                  |}
              ; A_pa_props :=
                  {|
                    A_pa_left_distributive := ld
                  ; A_pa_right_distributive := rd
                  |}
              ; A_pa_ast := A_bs_CI_ast A                                                               
              |} 
        | inr _ => A_Below_bs_CI_top A
        end 
    | inr _ => A_Below_bs_CI_top A
    end 
| _, _ => A_Below_bs_CI_top A
end.                             


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
let bsP     := bs_CS_props A in
let id_annP := bs_CS_id_ann_props A in   
match id_ann_plus_times_d   id_annP, id_ann_times_plus_d   id_annP with
|  Id_Ann_Equal zero, Id_Ann_Equal one =>
    match bs_left_distributive_d   bsP with 
    | inl ld =>
        match bs_right_distributive_d   bsP with 
        | inl rd =>
            Below_bs_CS_spa
              {|
                spa_eqv := bs_CS_eqv A
              ; spa_plus := bs_CS_plus A
              ; spa_times := bs_CS_times A
              ; spa_plus_props := bs_CS_plus_props A
              ; spa_times_props := bs_CS_times_props A
              ; spa_id_ann_props :=
                  {|
                    bounded_plus_id_is_times_ann := BS_Exists_Id_Ann_Equal zero
                  ; bounded_times_id_is_plus_ann := BS_Exists_Id_Ann_Equal one  
                  |}
              ; spa_props :=
                  {|
                    pa_left_distributive := ld
                  ; pa_right_distributive := rd
                  |}
              ; spa_ast := bs_CS_ast A                                                               
              |} 
        | inr _ => Below_bs_CS_top A
        end 
    | inr _ => Below_bs_CS_top A
    end 
| _, _ => Below_bs_CS_top A
end.                             

Definition classify_bs_CI {S : Type} (A : @bs_CI S) : @below_bs_CI S :=
let bsP     := bs_CI_props A in
let id_annP := bs_CI_id_ann_props A in   
match id_ann_plus_times_d   id_annP, id_ann_times_plus_d   id_annP with
|  Id_Ann_Equal zero, Id_Ann_Equal one =>
    match bs_left_distributive_d   bsP with 
    | inl ld =>
        match bs_right_distributive_d   bsP with 
        | inl rd =>
            Below_bs_CI_pa
              {|
                pa_eqv := bs_CI_eqv A
              ; pa_plus := bs_CI_plus A
              ; pa_times := bs_CI_times A
              ; pa_plus_props := bs_CI_plus_props A
              ; pa_times_props := bs_CI_times_props A
              ; pa_id_ann_props :=
                  {|
                    bounded_plus_id_is_times_ann := BS_Exists_Id_Ann_Equal zero
                  ; bounded_times_id_is_plus_ann := BS_Exists_Id_Ann_Equal one
                  |}
              ; pa_props :=
                  {|
                    pa_left_distributive := ld
                  ; pa_right_distributive := rd
                  |}
              ; pa_ast := bs_CI_ast A                                                               
              |} 
        | inr _ => Below_bs_CI_top A
        end 
    | inr _ => Below_bs_CI_top A
    end 
| _, _ => Below_bs_CI_top A
end.                             

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
  Proof. unfold classify_bs_CS, A_classify_bs_CS,
           A2C_below_bs_CS; destruct A; simpl.
         destruct A_bs_CS_id_ann_props; simpl. 
         destruct A_id_ann_plus_times_d as [[v1 v1'] | [v2 v2'] | [v3 v3'] |[v4 v4']| v5]; 
         destruct A_id_ann_times_plus_d as [[w1 w1'] | [w2 w2'] | [w3 w3'] |[w4 w4']| w5]; 
           simpl; try reflexivity.
         destruct A_bs_left_distributive_d, A_bs_right_distributive_d;
           simpl; try reflexivity.
Qed. 

  Lemma correct_classify_bs_CI (A : @A_bs_CI S) : 
  classify_bs_CI (A2C_bs_CI A)
  =
  A2C_below_bs_CI (A_classify_bs_CI A).
  Proof. unfold classify_bs_CI, A_classify_bs_CI,
           A2C_below_bs_CI; destruct A; simpl.
         destruct A_bs_CI_id_ann_props; simpl. 
         destruct A_id_ann_plus_times_d as [[v1 v1'] | [v2 v2'] | [v3 v3'] |[v4 v4']| v5]; 
         destruct A_id_ann_times_plus_d as [[w1 w1'] | [w2 w2'] | [w3 w3'] |[w4 w4']| w5]; 
           simpl; try reflexivity.
         destruct A_bs_left_distributive_d, A_bs_right_distributive_d;
           simpl; try reflexivity.
Qed. 


  Lemma correct_classify_bs (A : @A_bs S) : 
  classify_bs (A2C_bs A)
  =
  A2C_below_bs (A_classify_bs A).
  Proof. destruct A.
       unfold A_classify_bs, classify_bs, A2C_below_bs, A2C_bs. 
       destruct A_bs_plus_props; simpl. 
       destruct A_sg_C_selective_d as [sel | [p A]];
       destruct A_sg_C_idempotent_d as [idem | [i C]];
         simpl; try reflexivity.
         - rewrite <- correct_classify_bs_CS. reflexivity.
         - rewrite <- correct_classify_bs_CI. reflexivity.            
Qed.

End Verify.   
