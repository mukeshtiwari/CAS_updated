Require Import Coq.Strings.String.
Require Import CAS.coq.common.compute. 
Require Import
        CAS.coq.algorithms.matrix_definition 
        CAS.coq.algorithms.matrix_algorithms. 
Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures.
Require Import CAS.coq.bs.properties.
Require Import CAS.coq.bs.structures.
Require Import CAS.coq.bs.cast. 
Require Import List. 
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope. 

Require Import Init.Nat. (* for sub *)

(*
Fixpoint list_enum (n : nat) : list nat :=
  match n with
  | O => []
  | S n' => n' :: list_enum n' 
  end.
*) 

Definition square_matrix_exp {S : Type} (m : @square_matrix S) 
  (zero one : S) (plus times : binary_op S) :=
    let n := sqm_size m  in
    let m' := sqm_functional_matrix m in 
  {|
    sqm_size              := n 
  ; sqm_functional_matrix := matrix_exp zero one plus times n m' (sub n 1)
  |}. 
                  
Definition A_path_algebra_matrix_solver {S : Type}
  (P : @A_path_algebra S) 
  (m : @square_matrix S) :=
  let Q := A_pa_id_ann_props P in 
  match A_bounded_plus_id_is_times_ann _ _ _ Q, A_bounded_times_id_is_plus_ann _ _ _ Q with
  | existT _ zero _, existT _ one _  => 
       square_matrix_exp m zero one (A_pa_plus P) (A_pa_times P)
  end.                                                            

Definition A_selective_path_algebra_matrix_solver {S : Type}
  (P : @A_selective_path_algebra S) 
  (m : @square_matrix S) :=
  let Q := A_spa_id_ann_props P in 
  match A_bounded_plus_id_is_times_ann _ _ _ Q, A_bounded_times_id_is_plus_ann _ _ _ Q with
  | existT _ zero _, existT _ one _  => 
       square_matrix_exp m zero one (A_spa_plus P) (A_spa_times P)
  end.                                                            



Definition path_algebra_matrix_solver {S : Type}
  (P : @path_algebra S) 
  (m : @square_matrix S) :=
  let Q := pa_id_ann_props P in 
  match bounded_plus_id_is_times_ann Q, bounded_times_id_is_plus_ann Q with
  | BS_Exists_Id_Ann_Equal zero, BS_Exists_Id_Ann_Equal one => 
       square_matrix_exp m zero one (pa_plus P) (pa_times P)
  end.                                                            


Definition selective_path_algebra_matrix_solver {S : Type}
  (P : @selective_path_algebra S) 
  (m : @square_matrix S) :=
  let Q := spa_id_ann_props P in 
  match bounded_plus_id_is_times_ann Q, bounded_times_id_is_plus_ann Q with
  | BS_Exists_Id_Ann_Equal zero, BS_Exists_Id_Ann_Equal one => 
       square_matrix_exp m zero one (spa_plus P) (spa_times P)
  end.                                                            






  


    



