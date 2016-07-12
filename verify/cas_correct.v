Require Import CAS.code.basic_types. 
Require Import CAS.code.brel. 
Require Import CAS.code.bop. 
Require Import CAS.code.certificates.
Require Import CAS.code.cert_records.
Require Import CAS.code.cast.
Require Import CAS.code.construct_certs.
Require Import CAS.code.cas_records.
Require Import CAS.code.cas.
Require Import CAS.a_code.a_cast.
Require Import CAS.theory.properties.        (* ~~ certificates *) 
Require Import CAS.a_code.proof_records.     (* ~~ cert_records *) 
Require Import CAS.a_code.construct_proofs.  (* ~~ construct_certs *)
Require Import CAS.a_code.a_cas_records.     (* ~~ cas_records  *) 
Require Import CAS.a_code.a_cas.             (* ~~ cas          *) 
Require Import CAS.verify.proofs_to_certs. 
Require Import CAS.verify.construct_correct. (* ~~ construct_certs <-> construct_proofs *)


(* eqv *) 

Theorem correct_eqv_eq_bool : eqv_eq_bool = A2C_eqv bool (A_eqv_eq_bool). 
Proof. unfold eqv_eq_bool, A_eqv_eq_bool, A2C_eqv; simpl. 
       rewrite correct_eqv_certs_eq_bool. reflexivity. 
Qed. 

Theorem correct_eqv_eq_nat : eqv_eq_nat = A2C_eqv nat (A_eqv_eq_nat). 
Proof. unfold eqv_eq_nat, A_eqv_eq_nat, A2C_eqv; simpl. 
Proof. compute. reflexivity. Qed. 

Theorem correct_eqv_add_constant : ∀ (S : Type) (c : cas_constant) (E : A_eqv S),  
         eqv_add_constant S (A2C_eqv S E) c = A2C_eqv (with_constant S) (A_eqv_add_constant S E c). 
Proof. intros S c E. destruct E. 
       unfold eqv_add_constant, A_eqv_add_constant, A2C_eqv; simpl. 
       rewrite correct_eqv_certs_add_constant. reflexivity. 
Qed. 

Theorem correct_eqv_list : ∀ (S : Type) (E : A_eqv S),  
         eqv_list S (A2C_eqv S E) = A2C_eqv (list S) (A_eqv_list S E). 
Proof. intros S E. 
       destruct E. unfold eqv_list, A_eqv_list, A2C_eqv; simpl. 
       rewrite correct_eqv_certs_brel_list. reflexivity. 
Qed. 

Theorem correct_eqv_set : ∀ (S : Type) (E : A_eqv S),  
         eqv_set S (A2C_eqv S E) = A2C_eqv (finite_set S) (A_eqv_set S E). 
Proof. intros S E. 
       destruct E. unfold eqv_set, A_eqv_set, A2C_eqv; simpl. 
       rewrite correct_eqv_certs_brel_set. reflexivity. 
Qed. 


Theorem correct_eqv_product :
      ∀ (S T : Type) (eS : A_eqv S) (eT : A_eqv T), 
         eqv_product S T (A2C_eqv S eS) (A2C_eqv T eT)
         = 
         A2C_eqv (S * T) (A_eqv_product S T eS eT). 
Proof. intros S T eS eT. destruct eS; destruct eT. 
       unfold eqv_product, A_eqv_product, A2C_eqv; simpl. 
       rewrite correct_eqv_certs_product. reflexivity. 
Qed. 

Theorem correct_eqv_sum :
      ∀ (S T : Type) (eS : A_eqv S) (eT : A_eqv T), 
         eqv_sum S T (A2C_eqv S eS) (A2C_eqv T eT)
         = 
         A2C_eqv (S + T) (A_eqv_sum S T eS eT). 
Proof. intros S T eS eT. destruct eS; destruct eT. 
       unfold eqv_sum, A_eqv_sum, A2C_eqv; simpl. 
       rewrite correct_eqv_certs_sum. reflexivity. 
Qed. 


(* semigroups *) 

(* basics *) 

Theorem correct_sg_C_times : sg_C_times = A2C_sg_C nat (A_sg_C_times). 
Proof. compute. reflexivity. Qed. 

Theorem correct_sg_CK_plus : sg_CK_plus = A2C_sg_CK nat (A_sg_CK_plus). 
Proof. compute. reflexivity. Qed. 

Theorem correct_sg_CS_and : sg_CS_and = A2C_sg_CS bool (A_sg_CS_and). 
Proof. compute. reflexivity. Qed. 

Theorem correct_sg_CS_or : sg_CS_or = A2C_sg_CS bool (A_sg_CS_or). 
Proof. compute. reflexivity. Qed. 

Theorem correct_sg_CS_min : sg_CS_min = A2C_sg_CS nat (A_sg_CS_min). 
Proof. compute. reflexivity. Qed. 

Theorem correct_sg_CS_max : sg_CS_max = A2C_sg_CS nat (A_sg_CS_max). 
Proof. compute. reflexivity. Qed. 


Theorem correct_sg_concat :
      ∀ (S : Type) (eS : A_eqv S), 
         sg_concat S (A2C_eqv S eS) 
         = 
         A2C_sg (list S) (A_sg_concat S eS). 
Proof. intros S eS. 
       unfold sg_concat, A_sg_concat, A2C_sg. simpl. 
       rewrite correct_eqv_list. 
       rewrite correct_sg_certs_concat. 
       reflexivity. 
Qed. 

Theorem correct_sg_left :
      ∀ (S : Type) (eS : A_eqv S), 
         sg_left S (A2C_eqv S eS) 
         = 
         A2C_sg S (A_sg_left S eS). 
Proof. intros S eS. 
       unfold sg_left, A_sg_left, A2C_sg; simpl. 
       rewrite correct_sg_certs_left.  
       reflexivity. 
Qed. 

Theorem correct_sg_right :
      ∀ (S : Type) (eS : A_eqv S), 
         sg_right S (A2C_eqv S eS) 
         = 
         A2C_sg S (A_sg_right S eS). 
Proof. intros S eS. 
       unfold sg_right, A_sg_right, A2C_sg; simpl. 
       rewrite correct_sg_certs_right. 
       reflexivity. 
Qed. 


(* semigroup add_id *) 

Theorem correct_sg_add_id  :
      ∀ (S : Type) (c : cas_constant) (sgS : A_sg S), 
         sg_add_id S c (A2C_sg S sgS) 
         = 
         A2C_sg (with_constant S) (A_sg_add_id S c sgS). 
Proof. intros S c sgS. 
       unfold sg_add_id, A_sg_add_id, A2C_sg; simpl. 
       rewrite correct_eqv_add_constant. 
       rewrite correct_sg_certs_add_id. 
       reflexivity. 
Qed. 


Theorem correct_sg_C_add_id  :
      ∀ (S : Type) (c : cas_constant) (sg_CS : A_sg_C S), 
         sg_C_add_id S c (A2C_sg_C S sg_CS) 
         = 
         A2C_sg_C (with_constant S) (A_sg_C_add_id S c sg_CS). 
Proof. intros S c sg_CS. destruct sg_CS. 
       unfold sg_C_add_id, A_sg_C_add_id, A2C_sg_C; simpl. 
       rewrite correct_eqv_add_constant. 
       rewrite correct_sg_C_certs_add_id. 
       reflexivity. 
Qed. 

Theorem correct_sg_CI_add_id  :
      ∀ (S : Type) (c : cas_constant) (sg_CIS : A_sg_CI S), 
         sg_CI_add_id S c (A2C_sg_CI S sg_CIS) 
         = 
         A2C_sg_CI (with_constant S) (A_sg_CI_add_id S c sg_CIS). 
Proof. intros S c sg_CIS. destruct sg_CIS. 
       unfold sg_CI_add_id, A_sg_CI_add_id, A2C_sg_CI; simpl. 
       rewrite correct_eqv_add_constant. 
       rewrite correct_sg_CI_certs_add_id. 
       reflexivity. 
Qed. 

Theorem correct_sg_CS_add_id  :
      ∀ (S : Type) (c : cas_constant) (sg_CSS : A_sg_CS S), 
         sg_CS_add_id S c (A2C_sg_CS S sg_CSS) 
         = 
         A2C_sg_CS (with_constant S) (A_sg_CS_add_id S c sg_CSS). 
Proof. intros S c sg_CSS. destruct sg_CSS. 
       unfold sg_CS_add_id, A_sg_CS_add_id, A2C_sg_CS; simpl. 
       rewrite correct_eqv_add_constant. 
       rewrite correct_sg_CS_certs_add_id. 
       reflexivity. 
Qed. 


(* semigroup add_ann *) 

Theorem correct_sg_add_ann  :
      ∀ (S : Type) (c : cas_constant) (sgS : A_sg S), 
         sg_add_ann S c (A2C_sg S sgS) 
         = 
         A2C_sg (with_constant S) (A_sg_add_ann S c sgS). 
Proof. intros S c sgS. 
       unfold sg_add_ann, A_sg_add_ann, A2C_sg; simpl. 
       rewrite correct_eqv_add_constant. 
       rewrite correct_sg_certs_add_ann. 
       reflexivity. 
Qed. 


Theorem correct_sg_C_add_ann  :
      ∀ (S : Type) (c : cas_constant) (sg_CS : A_sg_C S), 
         sg_C_add_ann S c (A2C_sg_C S sg_CS) 
         = 
         A2C_sg_C (with_constant S) (A_sg_C_add_ann S c sg_CS). 
Proof. intros S c sg_CS. destruct sg_CS. 
       unfold sg_C_add_ann, A_sg_C_add_ann, A2C_sg_C; simpl. 
       rewrite correct_eqv_add_constant. 
       rewrite correct_sg_C_certs_add_ann. 
       reflexivity. 
Qed. 

Theorem correct_sg_CI_add_ann  :
      ∀ (S : Type) (c : cas_constant) (sg_CIS : A_sg_CI S), 
         sg_CI_add_ann S c (A2C_sg_CI S sg_CIS) 
         = 
         A2C_sg_CI (with_constant S) (A_sg_CI_add_ann S c sg_CIS). 
Proof. intros S c sg_CIS. destruct sg_CIS. 
       unfold sg_CI_add_ann, A_sg_CI_add_ann, A2C_sg_CI; simpl. 
       rewrite correct_eqv_add_constant. 
       rewrite correct_sg_CI_certs_add_ann. 
       reflexivity. 
Qed. 

Theorem correct_sg_CS_add_ann  :
      ∀ (S : Type) (c : cas_constant) (sg_CSS : A_sg_CS S), 
         sg_CS_add_ann S c (A2C_sg_CS S sg_CSS) 
         = 
         A2C_sg_CS (with_constant S) (A_sg_CS_add_ann S c sg_CSS). 
Proof. intros S c sg_CSS. destruct sg_CSS. 
       unfold sg_CS_add_ann, A_sg_CS_add_ann, A2C_sg_CS; simpl. 
       rewrite correct_eqv_add_constant. 
       rewrite correct_sg_CS_certs_add_ann. 
       reflexivity. 
Qed. 



(* semigroup products *) 

Theorem correct_sg_product :
      ∀ (S T : Type) (sgS : A_sg S) (sgT : A_sg T), 
         sg_product S T (A2C_sg S sgS) (A2C_sg T sgT) 
         = 
         A2C_sg (S * T) (A_sg_product S T sgS sgT). 
Proof. intros S T sgS sgT. 
       unfold sg_product, A_sg_product, A2C_sg; simpl. 
       rewrite correct_eqv_product. 
       rewrite correct_sg_certs_product. 
       reflexivity. 
Qed. 


Theorem correct_sg_product_new :
      ∀ (S T : Type) (sgS : A_sg_new S) (sgT : A_sg_new T), 
         sg_product_new S T (A2C_sg_new S sgS) (A2C_sg_new T sgT) 
         = 
         A2C_sg_new (S * T) (A_sg_product_new S T sgS sgT). 
Proof. intros S T sgS sgT. 
       unfold sg_product_new, A_sg_product_new, A2C_sg_new; simpl. 
       rewrite correct_eqv_product. 
       rewrite correct_sg_certs_product_new. 
       reflexivity. 
Qed. 


Theorem correct_sg_CK_product :
      ∀ (S T : Type) (sgS : A_sg_CK S) (sgT : A_sg_CK T), 
         sg_CK_product S T (A2C_sg_CK S sgS) (A2C_sg_CK T sgT) 
         = 
         A2C_sg_CK (S * T) (A_sg_CK_product S T sgS sgT). 
Proof. intros S T sgS sgT. destruct sgS; destruct sgT. 
       unfold sg_CK_product, A_sg_CK_product, A2C_sg_CK; simpl. 
       rewrite correct_eqv_product. 
       rewrite <- correct_sg_CK_certs_product. 
       reflexivity. 
Qed. 



(* semigroup sums *) 

Theorem correct_sg_left_sum :
      ∀ (S T : Type) (sgS : A_sg S) (sgT : A_sg T), 
         sg_left_sum S T (A2C_sg S sgS) (A2C_sg T sgT) 
         = 
         A2C_sg (S + T) (A_sg_left_sum S T sgS sgT). 
Proof. intros S T sgS sgT. 
       unfold sg_left_sum, A_sg_left_sum, A2C_sg. simpl. 
       rewrite correct_eqv_sum. 
       rewrite correct_sg_certs_left_sum. 
       reflexivity. 
Qed. 


Theorem correct_sg_right_sum :
      ∀ (S T : Type) (sgS : A_sg S) (sgT : A_sg T), 
         sg_right_sum S T (A2C_sg S sgS) (A2C_sg T sgT) 
         = 
         A2C_sg (S + T) (A_sg_right_sum S T sgS sgT). 
Proof. intros S T sgS sgT. 
       unfold sg_right_sum, A_sg_right_sum, A2C_sg; simpl. 
       rewrite correct_eqv_sum.
       rewrite correct_sg_certs_right_sum. 
       reflexivity. 
Qed. 


Theorem correct_sg_C_left_sum :
      ∀ (S T : Type) (sgS : A_sg_C S) (sgT : A_sg_C T), 
         sg_C_left_sum S T (A2C_sg_C S sgS) (A2C_sg_C T sgT) 
         = 
         A2C_sg_C (S + T) (A_sg_C_left_sum S T sgS sgT). 
Proof. intros S T sgS sgT. 
       unfold sg_C_left_sum, A_sg_C_left_sum, A2C_sg_C. simpl. 
       rewrite correct_eqv_sum. 
       rewrite correct_sg_C_certs_left_sum. 
       reflexivity. 
Qed. 


Theorem correct_sg_C_right_sum :
      ∀ (S T : Type) (sgS : A_sg_C S) (sgT : A_sg_C T), 
         sg_C_right_sum S T (A2C_sg_C S sgS) (A2C_sg_C T sgT) 
         = 
         A2C_sg_C (S + T) (A_sg_C_right_sum S T sgS sgT). 
Proof. intros S T sgS sgT. 
       unfold sg_C_right_sum, A_sg_C_right_sum, A2C_sg_C; simpl. 
       rewrite correct_eqv_sum.
       rewrite correct_sg_C_certs_right_sum. 
       reflexivity. 
Qed. 


Theorem correct_sg_CS_left_sum :
      ∀ (S T : Type) (sgS : A_sg_CS S) (sgT : A_sg_CS T), 
         sg_CS_left_sum S T (A2C_sg_CS S sgS) (A2C_sg_CS T sgT) 
         = 
         A2C_sg_CS (S + T) (A_sg_CS_left_sum S T sgS sgT). 
Proof. intros S T sgS sgT. 
       unfold sg_CS_left_sum, A_sg_CS_left_sum, A2C_sg_CS. simpl. 
       rewrite correct_eqv_sum. 
       rewrite correct_sg_CS_certs_left_sum. 
       reflexivity. 
Qed. 


Theorem correct_sg_CS_right_sum :
      ∀ (S T : Type) (sgS : A_sg_CS S) (sgT : A_sg_CS T), 
         sg_CS_right_sum S T (A2C_sg_CS S sgS) (A2C_sg_CS T sgT) 
         = 
         A2C_sg_CS (S + T) (A_sg_CS_right_sum S T sgS sgT). 
Proof. intros S T sgS sgT. 
       unfold sg_CS_right_sum, A_sg_CS_right_sum, A2C_sg_CS; simpl. 
       rewrite correct_eqv_sum.
       rewrite correct_sg_CS_certs_right_sum. 
       reflexivity. 
Qed. 

Theorem correct_sg_CI_left_sum :
      ∀ (S T : Type) (sgS : A_sg_CI S) (sgT : A_sg_CI T), 
         sg_CI_left_sum S T (A2C_sg_CI S sgS) (A2C_sg_CI T sgT) 
         = 
         A2C_sg_CI (S + T) (A_sg_CI_left_sum S T sgS sgT). 
Proof. intros S T sgS sgT. 
       unfold sg_CI_left_sum, A_sg_CI_left_sum, A2C_sg_CI. simpl. 
       rewrite correct_eqv_sum. 
       rewrite correct_sg_CI_certs_left_sum. 
       reflexivity. 
Qed. 


Theorem correct_sg_CI_right_sum :
      ∀ (S T : Type) (sgS : A_sg_CI S) (sgT : A_sg_CI T), 
         sg_CI_right_sum S T (A2C_sg_CI S sgS) (A2C_sg_CI T sgT) 
         = 
         A2C_sg_CI (S + T) (A_sg_CI_right_sum S T sgS sgT). 
Proof. intros S T sgS sgT. 
       unfold sg_CI_right_sum, A_sg_CI_right_sum, A2C_sg_CI; simpl. 
       rewrite correct_eqv_sum.
       rewrite correct_sg_CI_certs_right_sum. 
       reflexivity. 
Qed. 


(* semigroup lexicographic *) 

Theorem correct_sg_llex :
      ∀ (S T : Type) (sgS : A_sg_CS S) (sgT : A_sg T), 
         sg_llex S T (A2C_sg_CS S sgS) (A2C_sg T sgT) 
         = 
         A2C_sg (S * T) (A_sg_llex S T sgS sgT). 
Proof. intros S T sgS sgT. destruct sgS; destruct sgT. 
       unfold sg_llex, A_sg_llex, A2C_sg, A2C_sg_CS; simpl. 
       rewrite correct_sg_certs_llex. 
       rewrite correct_eqv_product. 
       reflexivity. 
Qed. 




Theorem correct_sg_C_llex :
      ∀ (S T : Type) (sgS : A_sg_CS S) (sgT : A_sg_C T), 
         sg_C_llex S T (A2C_sg_CS S sgS) (A2C_sg_C T sgT) 
         = 
         A2C_sg_C (S * T) (A_sg_C_llex S T sgS sgT). 
Proof. intros S T sgS sgT. destruct sgS; destruct sgT. 
       unfold sg_C_llex, A_sg_C_llex, A2C_sg_C, A2C_sg_CS; simpl. 
       rewrite correct_eqv_product. 
       rewrite correct_sg_C_certs_llex. 
       reflexivity. 
Qed. 

Theorem correct_sg_CS_llex :
      ∀ (S T : Type) (sgS : A_sg_CS S) (sgT : A_sg_CS T), 
         sg_CS_llex S T (A2C_sg_CS S sgS) (A2C_sg_CS T sgT) 
         = 
         A2C_sg_CS (S * T) (A_sg_CS_llex S T sgS sgT). 
Proof. intros S T sgS sgT. destruct sgS; destruct sgT. 
       unfold sg_CS_llex, A_sg_CS_llex, A2C_sg_CS; simpl. 
       rewrite correct_eqv_product. 
       rewrite correct_sg_CS_certs_llex. 
       reflexivity. 
Qed. 

Theorem correct_sg_CI_llex :
      ∀ (S T : Type) (sgS : A_sg_CS S) (sgT : A_sg_CI T), 
         sg_CI_llex S T (A2C_sg_CS S sgS) (A2C_sg_CI T sgT) 
         = 
         A2C_sg_CI (S * T) (A_sg_CI_llex S T sgS sgT). 
Proof. intros S T sgS sgT. destruct sgS; destruct sgT. 
       unfold sg_CI_llex, A_sg_CI_llex, A2C_sg_CI, A2C_sg_CS; simpl. 
       rewrite correct_eqv_product. 
       rewrite correct_sg_CI_certs_llex. 
       reflexivity. 
Qed. 

(* SETS *) 

Theorem correct_sg_CI_union_with_ann  :
      ∀ (S : Type) (c : cas_constant) (eqvS : A_eqv S), 
         sg_CI_union_with_ann S c (A2C_eqv S eqvS) 
         = 
         A2C_sg_CI (with_constant (finite_set S)) (A_sg_CI_union_with_ann S c eqvS). 
Proof. intros S c eqvS. destruct eqvS. 
       unfold sg_CI_union_with_ann, A_sg_CI_union_with_ann, A2C_eqv, A2C_sg_CI; simpl. 
       rewrite correct_sg_CI_certs_union_with_ann. 
       rewrite <- correct_eqv_add_constant.
       unfold eqv_set. simpl. 
       unfold A2C_eqv. simpl. 
       rewrite correct_eqv_certs_brel_set. 
       reflexivity. 
Qed. 

Theorem correct_sg_CI_intersect_with_id  :
      ∀ (S : Type) (c : cas_constant) (eqvS : A_eqv S), 
         sg_CI_intersect_with_id S c (A2C_eqv S eqvS) 
         = 
         A2C_sg_CI (with_constant (finite_set S)) (A_sg_CI_intersect_with_id S c eqvS). 
Proof. intros S c eqvS. destruct eqvS. 
       unfold sg_CI_intersect_with_id, A_sg_CI_intersect_with_id, A2C_eqv, A2C_sg_CI. simpl. 
       rewrite correct_sg_CI_certs_intersect_with_id. 
       unfold eqv_set. simpl. 
       unfold A2C_eqv. simpl. 
       rewrite correct_eqv_certs_brel_set. 
       unfold eqv_add_constant. simpl. 
       reflexivity. 
Qed. 




(* sg_sg 

Theorem correct_sg_sg_add_zero : ∀ (S : Type) (sg_sgS: A_sg_sg S) (c : cas_constant), 
   sg_sg_add_zero S (A2C_sg_sg S sg_sgS) c 
   =
   A2C_sg_sg (with_constant S) (A_sg_sg_add_zero S sg_sgS c). 
Proof. intros S sg_sgS c. 
       unfold sg_sg_add_zero, A_sg_sg_add_zero, A2C_sg_sg; simpl. 
       rewrite correct_eqv_add_constant. 
       rewrite correct_sg_certs_add_id. 
       rewrite correct_sg_certs_add_ann. 
       rewrite correct_sg_sg_certs_add_zero. 
       reflexivity. 
Qed. 


Theorem correct_sg_sg_add_one : ∀ (S : Type) (sg_sgS: A_sg_C_sg S) (c : cas_constant), 
   sg_C_sg_add_one S (A2C_sg_C_sg S sg_sgS) c 
   =
   A2C_sg_C_sg (with_constant S) (A_sg_C_sg_add_one S sg_sgS c). 
Proof. intros S sg_sgS c. 
       unfold sg_C_sg_add_one, A_sg_C_sg_add_one, A2C_sg_C_sg; simpl. 
       rewrite correct_eqv_add_constant. 
       rewrite correct_sg_C_certs_add_ann. 
       rewrite correct_sg_certs_add_id. 
       rewrite correct_sg_sg_certs_add_one. 
       reflexivity. 
Qed. 



Theorem correct_sg_sg_product : ∀ (S T : Type) (sg_sgS: A_sg_sg S) (sg_sgT : A_sg_sg T), 
   sg_sg_product S T (A2C_sg_sg S sg_sgS) (A2C_sg_sg T sg_sgT)
   =
   A2C_sg_sg (S * T) (A_sg_sg_product S T sg_sgS sg_sgT). 
Proof. intros S T sg_sgS sg_sgT. 
       unfold sg_sg_product, A_sg_sg_product, A2C_sg_sg; simpl. 
       rewrite correct_eqv_product. 
       rewrite correct_sg_certs_product. 
       rewrite correct_sg_certs_product. 
       rewrite correct_sg_sg_certs_product. 
       reflexivity. 
Qed. 


Theorem correct_sg_C_sg_llex : ∀ (S T : Type) (sg_sgS: A_sg_CS_sg S) (sg_sgT : A_sg_C_sg T), 
   sg_C_sg_llex S T (A2C_sg_CS_sg S sg_sgS) (A2C_sg_C_sg T sg_sgT)
   =
   A2C_sg_C_sg (S * T) (A_sg_C_sg_llex S T sg_sgS sg_sgT). 
Proof. intros S T sg_sgS sg_sgT. 
       unfold sg_C_sg_llex, A_sg_C_sg_llex, A2C_sg_CS_sg, A2C_sg_C_sg; simpl. 
       rewrite correct_eqv_product. 
       rewrite correct_sg_C_certs_llex. 
       rewrite correct_sg_certs_product. 
       rewrite correct_sg_sg_certs_llex_product. 
       reflexivity. 
Qed. 


*) 








