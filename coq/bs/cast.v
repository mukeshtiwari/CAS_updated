Require Import Coq.Strings.String.
Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.

Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.

Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures.
Require Import CAS.coq.sg.cast_up.


Require Import CAS.coq.bs.properties.
Require Import CAS.coq.bs.structures.
Require Import CAS.coq.bs.theory. 
Section ACAS.

Definition A_bs_id_ann_properties_from_bounded_properties
    {S: Type} (eq : brel S) (plus : binary_op S) (times : binary_op S)
    (P : A_bs_id_ann_bounded_properties eq plus times) := 
{|
  A_id_ann_plus_times_d  := A_Id_Ann_Equal _ _ _ (A_bounded_plus_id_is_times_ann _ _ _ P) 
; A_id_ann_times_plus_d  := A_Id_Ann_Equal _ _ _ (A_bounded_times_id_is_plus_ann _ _ _ P) 
|}.


Definition A_bs_properties_from_pa_properties
  {S: Type} (eq : brel S) (plus : binary_op S) (times : binary_op S)
  (eqvP : eqv_proofs S eq)
  (pcng : bop_congruence S eq plus)
  (tcng : bop_congruence S eq times)
  (A : A_bs_exists_id_ann_equal eq times plus)
  (P : A_pa_properties eq plus times) :=
let ref := A_eqv_reflexive _ _ eqvP in
let sym := A_eqv_symmetric _ _ eqvP in 
let trn := A_eqv_transitive _ _ eqvP in
let ld   := A_pa_left_distributive _ _ _ P in 
let rd   := A_pa_right_distributive _ _ _ P in           
{|
  A_bs_left_distributive_d  := inl ld 
; A_bs_right_distributive_d := inl rd 
; A_bs_left_absorptive_d    := inl (one_is_plus_annihilator_implies_left_absorptive S 
                                       eq plus times ref sym trn pcng tcng A ld)
; A_bs_right_absorptive_d   := inl (one_is_plus_annihilator_implies_right_absorptive S 
                                       eq plus times ref sym trn pcng tcng A rd)
|}.

  

Definition A_bs_from_bs_CS {S : Type} (B : @A_bs_CS S) : @A_bs S := 
   {| 
     A_bs_eqv          := A_bs_CS_eqv B
   ; A_bs_plus         := A_bs_CS_plus B
   ; A_bs_times        := A_bs_CS_times B
   ; A_bs_plus_props   := A_sg_C_proofs_from_sg_CS_proofs _ _ _ 
                            (A_eqv_witness _ (A_bs_CS_eqv B))
                            (A_eqv_new _ (A_bs_CS_eqv B))
                            (A_eqv_not_trivial _ (A_bs_CS_eqv B))
                            (A_eqv_proofs _ (A_bs_CS_eqv B)) 
                            (A_bs_CS_plus_props B)
   ; A_bs_times_props := A_bs_CS_times_props B
   ; A_bs_id_ann_props := A_bs_CS_id_ann_props B
   ; A_bs_props       := A_bs_CS_props B                                             
   ; A_bs_ast         := A_bs_CS_ast B
   |}.


Definition A_bs_from_bs_CI {S : Type} (B : @A_bs_CI S) : @A_bs S := 
   {| 
     A_bs_eqv          := A_bs_CI_eqv B
   ; A_bs_plus         := A_bs_CI_plus B
   ; A_bs_times        := A_bs_CI_times B
   ; A_bs_plus_props   := A_sg_C_proofs_from_sg_CI_proofs _ _ _ 
                            (A_eqv_witness _ (A_bs_CI_eqv B))
                            (A_eqv_new _ (A_bs_CI_eqv B))
                            (A_eqv_not_trivial _ (A_bs_CI_eqv B))
                            (A_eqv_proofs _ (A_bs_CI_eqv B)) 
                            (A_bs_CI_plus_props B)
   ; A_bs_times_props  := A_bs_CI_times_props B
   ; A_bs_id_ann_props := A_bs_CI_id_ann_props B
   ; A_bs_props        := A_bs_CI_props B
   ; A_bs_ast          := A_bs_CI_ast B
   |}. 

Definition A_bs_CI_from_path_algebra {S : Type} (B : @A_path_algebra S) : @A_bs_CI S :=
  let eqv    := A_pa_eqv B in
  let eq     := A_eqv_eq _ eqv in
  let eqvP   := A_eqv_proofs _ eqv in 
  let plus   := A_pa_plus B in
  let times  := A_pa_times B in
  let plusP  := A_pa_plus_props B in
  let pcng   := A_sg_CI_congruence _ _ _ plusP in 
  let timesP := A_pa_times_props B  in
  let tcng   := A_sg_congruence _ _ _ timesP in   
   {| 
     A_bs_CI_eqv          := eqv 
   ; A_bs_CI_plus         := plus 
   ; A_bs_CI_times        := times 
   ; A_bs_CI_plus_props   := plusP
   ; A_bs_CI_times_props  := timesP 
   ; A_bs_CI_id_ann_props := A_bs_id_ann_properties_from_bounded_properties _ _ _ (A_pa_id_ann_props B)
   ; A_bs_CI_props        := A_bs_properties_from_pa_properties eq plus times eqvP pcng tcng 
                               (A_bounded_times_id_is_plus_ann _ _ _ (A_pa_id_ann_props B)) 
                               (A_pa_props B)                                             
   ; A_bs_CI_ast          := A_pa_ast B
   |}. 

Definition A_bs_CS_from_selective_path_algebra {S : Type} (B : @A_selective_path_algebra S) : @A_bs_CS S :=
  let eqv    := A_spa_eqv B in
  let eq     := A_eqv_eq _ eqv in
  let eqvP   := A_eqv_proofs _ eqv in 
  let plus   := A_spa_plus B in
  let times  := A_spa_times B in
  let plusP  := A_spa_plus_props B in
  let pcng   := A_sg_CS_congruence _ _ _ plusP in   
  let timesP := A_spa_times_props B  in
  let tcng   := A_sg_congruence _ _ _ timesP in   
   {| 
     A_bs_CS_eqv          := eqv 
   ; A_bs_CS_plus         := plus 
   ; A_bs_CS_times        := times 
   ; A_bs_CS_plus_props   := plusP
   ; A_bs_CS_times_props  := timesP 
   ; A_bs_CS_id_ann_props := A_bs_id_ann_properties_from_bounded_properties _ _ _ (A_spa_id_ann_props B)
   ; A_bs_CS_props        := A_bs_properties_from_pa_properties eq plus times eqvP pcng tcng
                               (A_bounded_times_id_is_plus_ann _ _ _ (A_spa_id_ann_props B)) 
                               (A_spa_props B)                                             
   ; A_bs_CS_ast          := A_spa_ast B
   |}. 


End ACAS.


Section AMCAS.
  
    Definition A_cast_up_bs_CS {S : Type} (A : @A_below_bs_CS S) : @A_bs_CS S :=
    match A with
    | A_Below_bs_CS_top  B    => B
    | A_Below_bs_CS_spa  B    => A_bs_CS_from_selective_path_algebra B
    end. 

    Definition A_cast_up_bs_CI {S : Type} (A : @A_below_bs_CI S) : @A_bs_CI S :=
    match A with
    | A_Below_bs_CI_top  B    => B
    | A_Below_bs_CI_pa   B    => A_bs_CI_from_path_algebra B                                   
    end. 
    
  Definition A_cast_up_bs {S : Type} (A : @A_below_bs S) : @A_bs S :=
    match A with 
    | A_Below_bs_top B   => B 
    | A_Below_bs_bs_CS B => A_bs_from_bs_CS (A_cast_up_bs_CS B)
    | A_Below_bs_bs_CI B => A_bs_from_bs_CI (A_cast_up_bs_CI B)                                                   
    end.


    (* NB: each of the following cast (down) functions assumes 
       that its argument has been classified already.
       These functions can "fail" by returning None. 
    *)  
    Definition A_cast_below_bs_to_below_bs_CI {S : Type}
    (A : @A_below_bs S) : option (@A_below_bs_CI S) :=
    match A with
    | A_Below_bs_top _  => None
    | A_Below_bs_bs_CI B => Some B
    | A_Below_bs_bs_CS _ => None
    end. 

    Definition A_cast_below_bs_to_below_bs_CS {S : Type}
    (A : @A_below_bs S) : option (@A_below_bs_CS S) :=
    match A with
    | A_Below_bs_top _  => None
    | A_Below_bs_bs_CI _ => None
    | A_Below_bs_bs_CS B => Some B
    end. 

End AMCAS.

Section CAS.

Definition bs_id_ann_properties_from_bounded_properties
  {S: Type} (P : @bs_id_ann_bounded_properties S)
  : @bs_id_ann_properties S :=
  match bounded_plus_id_is_times_ann P, bounded_times_id_is_plus_ann P with
  | BS_Exists_Id_Ann_Equal zero, BS_Exists_Id_Ann_Equal one => 
      {|
        id_ann_plus_times_d  := Id_Ann_Equal zero
      ; id_ann_times_plus_d  := Id_Ann_Equal one 
      |}
  end.


Definition bs_properties_from_pa_properties {S: Type} (w : S):=
{|
  bs_left_distributive_d  := inl (BS_Left_Distributive w) 
; bs_right_distributive_d := inl (BS_Right_Distributive w)
; bs_left_absorptive_d    := inl (BS_Left_Absorptive w)
; bs_right_absorptive_d   := inl (BS_Right_Absorptive w) 
|}.

Definition bs_from_bs_CS {S : Type} (B : @bs_CS S) : @bs S := 
   {| 
     bs_eqv          := bs_CS_eqv B
   ; bs_plus         := bs_CS_plus B
   ; bs_times        := bs_CS_times B
   ; bs_plus_props   := sg_C_certs_from_sg_CS_certs
                          S
                          (eqv_eq (bs_CS_eqv B))
                          (bs_CS_plus B)
                          (eqv_witness (bs_CS_eqv B))
                          (eqv_new (bs_CS_eqv B))
                          (bs_CS_plus_props B)
   ; bs_times_props := bs_CS_times_props B
   ; bs_id_ann_props := bs_CS_id_ann_props B
   ; bs_props       := bs_CS_props B                                             
   ; bs_ast         := bs_CS_ast B
   |}.



Definition bs_from_bs_CI {S : Type} (B : @bs_CI S) : @bs S := 
   {| 
     bs_eqv          := bs_CI_eqv B
   ; bs_plus         := bs_CI_plus B
   ; bs_times        := bs_CI_times B
   ; bs_plus_props   := sg_C_certs_from_sg_CI_certs 
                          S
                          (eqv_eq (bs_CI_eqv B))
                          (bs_CI_plus B)
                          (eqv_witness (bs_CI_eqv B))
                          (eqv_new (bs_CI_eqv B))
                          (bs_CI_plus_props B)
   ; bs_times_props := bs_CI_times_props B
   ; bs_id_ann_props := bs_CI_id_ann_props B
   ; bs_props       := bs_CI_props B                                             
   ; bs_ast         := bs_CI_ast B
   |}.


Definition bs_CI_from_path_algebra {S : Type} (B : @path_algebra S) : @bs_CI S :=
  {|
     bs_CI_eqv          := pa_eqv B
   ; bs_CI_plus         := pa_plus B 
   ; bs_CI_times        := pa_times B 
   ; bs_CI_plus_props   := pa_plus_props B 
   ; bs_CI_times_props  := pa_times_props B  
   ; bs_CI_id_ann_props := bs_id_ann_properties_from_bounded_properties (pa_id_ann_props B)
   ; bs_CI_props        := bs_properties_from_pa_properties (eqv_witness (pa_eqv B))
   ; bs_CI_ast          := pa_ast B
   |}. 


Definition bs_CS_from_selective_path_algebra {S : Type} (B : @selective_path_algebra S) : @bs_CS S :=
   {| 
     bs_CS_eqv          := spa_eqv B
   ; bs_CS_plus         := spa_plus B 
   ; bs_CS_times        := spa_times B 
   ; bs_CS_plus_props   := spa_plus_props B 
   ; bs_CS_times_props  := spa_times_props B  
   ; bs_CS_id_ann_props := bs_id_ann_properties_from_bounded_properties (spa_id_ann_props B)
   ; bs_CS_props        := bs_properties_from_pa_properties (eqv_witness (spa_eqv B))
   ; bs_CS_ast          := spa_ast B
   |}. 

End CAS.

Section MCAS.
    Definition cast_up_bs_CS {S : Type} (A : @below_bs_CS S) : @bs_CS S :=
    match A with
    | Below_bs_CS_top  B    => B
    | Below_bs_CS_spa  B    => bs_CS_from_selective_path_algebra B                                 
    end. 

    Definition cast_up_bs_CI {S : Type} (A : @below_bs_CI S) : @bs_CI S :=
    match A with
    | Below_bs_CI_top  B    => B
    | Below_bs_CI_pa   B    => bs_CI_from_path_algebra B                                  
    end. 
    
  Definition cast_up_bs {S : Type} (A : @below_bs S) : @bs S :=
    match A with 
    | Below_bs_top B   => B 
    | Below_bs_bs_CS B => bs_from_bs_CS (cast_up_bs_CS B)
    | Below_bs_bs_CI B => bs_from_bs_CI (cast_up_bs_CI B)                                                   
    end.


    (* NB: each of the following cast (down) functions assumes 
       that its argument has been classified already.
       These functions can "fail" by returning None. 
    *)  
    Definition cast_below_bs_to_below_bs_CI {S : Type}
    (A : @below_bs S) : option (@below_bs_CI S) :=
    match A with
    | Below_bs_top _  => None
    | Below_bs_bs_CI B => Some B
    | Below_bs_bs_CS _ => None
    end. 

    Definition cast_below_bs_to_below_bs_CS {S : Type}
    (A : @below_bs S) : option (@below_bs_CS S) :=
    match A with
    | Below_bs_top _  => None
    | Below_bs_bs_CI _ => None
    | Below_bs_bs_CS B => Some B
    end. 

    Definition cast_below_bs_to_path_algebra {S : Type}
    (A : @below_bs S) : option (@path_algebra S) :=
    match A with
    | Below_bs_top _  => None
    | Below_bs_bs_CI (Below_bs_CI_top _) => None 
    | Below_bs_bs_CI (Below_bs_CI_pa B) => Some B
    | Below_bs_bs_CS B => None
    end. 

    Definition cast_below_bs_to_selective_path_algebra {S : Type}
    (A : @below_bs S) : option (@selective_path_algebra S) :=
    match A with
    | Below_bs_top _  => None
    | Below_bs_bs_CS (Below_bs_CS_top _) => None 
    | Below_bs_bs_CS (Below_bs_CS_spa B) => Some B
    | Below_bs_bs_CI B => None
    end. 
    
End MCAS.


Section Verify.


Theorem correct_bs_from_bs_CS (S : Type) (P : @A_bs_CS S) : 
  bs_from_bs_CS (A2C_bs_CS P)
  =
  A2C_bs (A_bs_from_bs_CS P). 
Proof. unfold bs_from_bs_CS, A_bs_from_bs_CS, A2C_bs_CS, A2C_bs; simpl. 
       rewrite <- correct_sg_C_certs_from_sg_CS_certs; auto. 
Qed.

Theorem correct_bs_from_bs_CI (S : Type) (P : @A_bs_CI S) : 
  bs_from_bs_CI (A2C_bs_CI P)
  =
  A2C_bs (A_bs_from_bs_CI P). 
Proof. unfold bs_from_bs_CI, A_bs_from_bs_CI, A2C_bs_CI, A2C_bs; simpl. 
       rewrite <- correct_sg_C_certs_from_sg_CI_certs; auto. 
Qed.

Lemma correct_bs_properties_from_pa_properties
  (S : Type) (eq : brel S) (w : S) (plus times : binary_op S)
  (eqvP : eqv_proofs S eq)
  (pcng : bop_congruence S eq plus)
  (tcng : bop_congruence S eq times)
  (A : A_bs_exists_id_ann_equal eq times plus)
  (P : A_pa_properties eq plus times) : 
  bs_properties_from_pa_properties w
  =
  P2C_bs eq w plus times 
    (A_bs_properties_from_pa_properties eq plus times eqvP pcng tcng A P). 
Proof. reflexivity. Qed.


Lemma correct_bs_id_ann_properties_from_bounded_properties
  (S : Type) (eq : brel S) (plus times : binary_op S)
  (P : A_bs_id_ann_bounded_properties eq plus times) : 
  bs_id_ann_properties_from_bounded_properties
    (P2C_bs_id_ann_bounded_properties _ _ _ _ P)
  =
  P2C_id_ann _ _ _ _
    (A_bs_id_ann_properties_from_bounded_properties eq plus times P). 
Proof. reflexivity. Qed.

Theorem correct_bs_CI_from_path_algebra (S : Type) (P : @A_path_algebra S) : 
  bs_CI_from_path_algebra (A2C_path_algebra P)
  =
  A2C_bs_CI (A_bs_CI_from_path_algebra P). 
Proof. unfold bs_CI_from_path_algebra, A_bs_CI_from_path_algebra,
         A2C_bs_CI, A2C_path_algebra; simpl.
       rewrite <- correct_bs_id_ann_properties_from_bounded_properties. 
       rewrite <- correct_bs_properties_from_pa_properties.
       reflexivity. 
Qed.

Theorem correct_bs_CS_from_selective_path_algebra (S : Type) (P : @A_selective_path_algebra S) : 
  bs_CS_from_selective_path_algebra (A2C_selective_path_algebra P)
  =
  A2C_bs_CS (A_bs_CS_from_selective_path_algebra P). 
Proof. unfold bs_CS_from_selective_path_algebra,
         A_bs_CS_from_selective_path_algebra,
         A2C_bs_CS, A2C_selective_path_algebra; simpl.
       rewrite <- correct_bs_id_ann_properties_from_bounded_properties. 
       rewrite <- correct_bs_properties_from_pa_properties.
       reflexivity. 
Qed.


Theorem correct_cast_below_bs_to_below_bs_CS (S : Type) (A : @A_below_bs S) :
  cast_below_bs_to_below_bs_CS (A2C_below_bs A)
  =
  option_map A2C_below_bs_CS (A_cast_below_bs_to_below_bs_CS A).
Proof. destruct A; unfold A_cast_below_bs_to_below_bs_CI,
         cast_below_bs_to_below_bs_CI; simpl; try reflexivity.
Qed.

Theorem correct_cast_below_bs_to_below_bs_CI (S : Type) (A : @A_below_bs S) :
  cast_below_bs_to_below_bs_CI (A2C_below_bs A)
  =
  option_map A2C_below_bs_CI (A_cast_below_bs_to_below_bs_CI A).
Proof. destruct A; unfold A_cast_below_bs_to_below_bs_CI,
         cast_below_bs_to_below_bs_CI; simpl; try reflexivity.
Qed.


Section Commute.

Variable S : Type.

Lemma cast_up_bs_CS_A2C_commute (A : @A_below_bs_CS S) : 
  cast_up_bs_CS (A2C_below_bs_CS A)
  =
  A2C_bs_CS (A_cast_up_bs_CS A).
Proof. destruct A; reflexivity. Qed. 

Lemma cast_up_bs_CI_A2C_commute (A : @A_below_bs_CI S) : 
  cast_up_bs_CI (A2C_below_bs_CI A)
  =
  A2C_bs_CI (A_cast_up_bs_CI A).
Proof. destruct A; reflexivity. Qed.       

Lemma cast_up_bs_A2C_commute (A : @A_below_bs S) : 
  cast_up_bs (A2C_below_bs A)
  =
  A2C_bs (A_cast_up_bs A).
Proof. destruct A; unfold cast_up_bs, A_cast_up_bs; simpl; try reflexivity. 
       - rewrite cast_up_bs_CS_A2C_commute.
         rewrite correct_bs_from_bs_CS. 
         reflexivity.
       - rewrite cast_up_bs_CI_A2C_commute.
         rewrite correct_bs_from_bs_CI. 
         reflexivity.
Qed.
  
End Commute. 

End Verify.   
