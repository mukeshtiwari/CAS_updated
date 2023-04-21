(*
Approach 1
----------
union_insert eqv SELF

(inr X) + (inr Y) = inr (X union Y)
(inl SELF) + _    = (inl SELF)

x |> inr X    = inr ({x} union X) 
x |> inl SELF = inr {x} 

+id  = inr {}
+ann = inl SELF

problem: not distributive 

lhs = x |> (inl SELF) + (inr X) 
    = x |> (inl SELF) 
    = inr {x} 

rhs = (x |> (inl SELF)) + (x |> (inr X)) 
    = inr {x} union' inr ({x} union X)
    = inr ({x} union X)

Approach 2
----------
start with distributive 

x |> X = {x} union X
(+) = union

(+)-id = {} 

note : x |> {} = {x} 

So, {} could be read as "self". However, 
such a best value should be the (+) annahilator, not the id. 

Add a double ann now. 

(inl SELF) + _    = (inl SELF)

but 

x |> inl SELF = inl SELF

which is not correct. 

Approach 3
----------
??? 

*) 
Require Import Coq.Strings.String.
Require Import CAS.coq.common.ast.
Require Import CAS.coq.common.compute.
Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures. 
Require Import CAS.coq.eqv.set.
Require Import CAS.coq.eqv.add_constant.
Require Import CAS.coq.eqv.sum.
Require Import CAS.coq.sg.properties. 
Require Import CAS.coq.sg.structures.
Require Import CAS.coq.sg.union.
Require Import CAS.coq.sg.cast_up.
Require Import CAS.coq.sg.add_ann. 
Require Import CAS.coq.tr.left.insert.
Require Import CAS.coq.bs.properties.
Require Import CAS.coq.bs.union_union. 
Require Import CAS.coq.st.properties. 
Require Import CAS.coq.st.structures.

Section Theory.

Variables (S : Type)
          (c : cas_constant) 
          (wS : S)   
          (eq : brel S)
          (f : S -> S)
          (nt : brel_not_trivial S eq f)
          (ref : brel_reflexive S eq)
          (sym : brel_symmetric S eq)
          (trn : brel_transitive S eq). 


Lemma slt_union_insert_not_distributive :
  @slt_not_distributive S
                    (with_constant (finite_set S))
                    (brel_sum brel_constant (brel_set eq))
                    (bop_add_ann (bop_union eq) c) 
                    (ltr_insert eq).
Proof. exists (wS, (inl c, inr ((f wS) :: nil))); simpl. 
       case_eq(brel_set eq (wS :: nil)
                        (bop_union eq (wS :: nil)
                                   (bop_union eq (wS :: nil) (f wS :: nil)))); intro A; auto.
       apply brel_set_elim_prop in A; auto.
       destruct A as [A B]. 
       assert (C : set.in_set eq (bop_union eq (wS :: nil) (bop_union eq (wS :: nil) (f wS :: nil))) (f wS) = true).
          apply in_set_bop_union_intro; auto.
          right. apply in_set_bop_union_intro; auto.
          right. compute. rewrite ref. reflexivity.
       assert (D := B _ C). compute in D.
       destruct (nt wS) as [L R].
       rewrite R in D. discriminate D. 
Defined. 

Lemma slt_union_insert_not_absorptive : 
  @slt_not_absorptive S
                    (with_constant (finite_set S))
                    (brel_sum brel_constant (brel_set eq))
                    (bop_add_ann (bop_union eq) c) 
                    (ltr_insert eq).
Proof. exists (wS, inr nil). compute. reflexivity. Defined. 

Lemma slt_union_insert_not_strictly_absorptive : 
  @slt_not_strictly_absorptive S
                    (with_constant (finite_set S))
                    (brel_sum brel_constant (brel_set eq))
                    (bop_add_ann (bop_union eq) c) 
                    (ltr_insert eq).
Proof. exists (wS, inr nil). left. compute. reflexivity. Defined. 

Lemma slt_union_insert_exists_id_ann_decide (fin_d : carrier_is_finite_decidable S eq) : 
  @slt_exists_id_ann_decidable S
                               (with_constant (finite_set S))
                               (brel_sum brel_constant (brel_set eq))
                               (bop_add_ann (bop_union eq) c) 
                               (ltr_insert eq).
Proof. destruct fin_d as [finP | nfinP].
       + assert (A : @slt_exists_id_ann_not_equal S
                                                  (with_constant (finite_set S))
                                                  (brel_sum brel_constant (brel_set eq))
                                                  (bop_add_ann (bop_union eq) c) 
                                                  (ltr_insert eq)).
         exists (inr nil, inr ((projT1 finP) tt)); simpl. split. split.
         apply bop_add_ann_is_id. 
         apply bop_union_nil_is_id; auto. 
         apply ltr_insert_enum_is_ann; auto.
         case_eq(brel_set eq nil (projT1 finP tt)); intro B; auto.
            destruct finP as [enum P]. unfold projT1 in B.
            assert (C := P wS).
            apply brel_set_elim_prop in B;auto. destruct B as [B1 B2].
            assert (D := B2 _ C).
            compute in D. discriminate D.
         exact (@SLT_Id_Ann_Proof_Not_Equal _ _ _ _ _ A). 
       + exact (@SLT_Id_Ann_Proof_Id_None _ _ _ _ _ 
                   (bop_add_ann_exists_id _ _ c (bop_union eq) (bop_union_exists_id S eq ref sym trn), 
                    ltr_insert_not_exists_ann S eq wS ref sym trn nfinP)).
Defined.          


End Theory.

Section ACAS.

Definition union_insert_slt_proofs
           (S : Type)
           (c : cas_constant)
           (eq : brel S)
           (wS : S)
           (f : S → S)
           (nt : brel_not_trivial S eq f) 
           (eqvP : eqv_proofs S eq) :=
let ref := A_eqv_reflexive _ _ eqvP in
let sym := A_eqv_symmetric _ _ eqvP in
let trn := A_eqv_transitive _ _ eqvP in      
{|
  A_slt_distributive_d   := inr (slt_union_insert_not_distributive S c wS eq f nt ref sym trn)
; A_slt_absorptive_d := inr (slt_union_insert_not_absorptive S c wS eq)
; A_slt_strictly_absorptive_d := inr (slt_union_insert_not_strictly_absorptive S c wS eq)
|}.

Open Scope string_scope.

Definition A_slt_union_insert (S :Type) (eqv : A_eqv S) (c : cas_constant) :=
let eq         := A_eqv_eq S eqv in
let wS          := A_eqv_witness S eqv in
let f          := A_eqv_new S eqv in
let ntS        := A_eqv_not_trivial S eqv in
let fin_d      := A_eqv_finite_d S eqv in
let eqvP       := A_eqv_proofs S eqv in
let refS       := A_eqv_reflexive _ _ eqvP in
let symS       := A_eqv_symmetric _ _ eqvP in
let trnS       := A_eqv_transitive _ _ eqvP in
  {|
    A_slt_carrier           := A_eqv_add_constant _ (A_eqv_set S eqv) c 
  ; A_slt_label             := eqv 
  ; A_slt_plus              := bop_add_ann (bop_union eq) c 
  ; A_slt_trans             := ltr_insert eq 
  ; A_slt_plus_proofs       :=
      (* triple UGLY!  need some abstraction here.... FIX someday .... *) 
      sg_proofs_add_ann
        (finite_set S)
        (brel_set eq)
        c
        (bop_union eq)
        (wS :: nil)
        (λ (l : finite_set S), if brel_set eq nil l then (wS :: nil) else nil)
        (brel_set_not_trivial S eq wS)
        (eqv_proofs_set S eq eqvP)
        (A_sg_proofs_from_sg_CI_proofs
           (finite_set S) 
           (brel_set eq)
           (bop_union eq) 
           (wS :: nil)
           (λ (l : finite_set S), if brel_set eq nil l then (wS :: nil) else nil)
           (brel_set_not_trivial S eq wS)
           (eqv_proofs_set S eq eqvP)
           (sg_CI_proofs_union eqv))
  ; A_slt_trans_proofs      := ltr_insert_proofs S eq wS f ntS eqvP 
  ; A_slt_exists_plus_ann_d := inl (bop_add_ann_exists_ann _ (brel_set eq) c (bop_union eq))
  ; A_slt_id_ann_proofs_d   := slt_union_insert_exists_id_ann_decide S c wS eq refS symS trnS fin_d 
  ; A_slt_proofs            := union_insert_slt_proofs S c eq wS f ntS eqvP  
  ; A_slt_ast               := Cas_ast ("slt_union_insert", (Cas_eqv_ast (A_eqv_ast S eqv)) :: (Cas_ast_constant c) :: nil)
|}.

 
End ACAS.   

Section AMCAS.


Definition A_mcas_slt_union_insert (S : Type) (eqv : @A_mcas_eqv S) (c : cas_constant) :=
match eqv with
| A_EQV_eqv A    => A_slt_classify (A_SLT (A_slt_union_insert _ A c))
| A_EQV_Error sl => A_SLT_Error sl     
end.
  
End AMCAS.   

Section CAS.

Definition union_insert_slt_certs {S : Type} (c : cas_constant) (wS : S) (f : S -> S) :=
{|
  slt_distributive_d        := @Certify_Slt_Not_Distributive S (with_constant (finite_set S)) (wS, (inl c, inr ((f wS) :: nil)))
; slt_absorptive_d          := @Certify_Slt_Not_Absorptive S (with_constant (finite_set S)) (wS, inr nil)
; slt_strictly_absorptive_d := @Certify_Slt_Not_Strictly_Absorptive S (with_constant (finite_set S)) (wS, inr nil)
|}.

Open Scope string_scope.


Definition slt_union_insert_exists_id_ann_certify
           {S : Type}
           (fin_d : @check_is_finite S) : @check_slt_exists_id_ann S (with_constant (finite_set S)) :=
  match fin_d with
  | Certify_Is_Finite enum => Certify_SLT_Id_Ann_Proof_Not_Equal (inr nil, inr (enum tt))
  | Certify_Is_Not_Finite  => Certify_SLT_Id_Ann_Proof_Id_None (inr nil) 
  end.

  
Definition slt_union_insert {S :Type} (eqv : @eqv S) (c : cas_constant) :=
let eq         := eqv_eq eqv in
let wS         := eqv_witness eqv in
let f          := eqv_new eqv in
let fin_d      := eqv_finite_d eqv in
  {|
    slt_carrier           := eqv_add_constant (eqv_set eqv) c 
  ; slt_label             := eqv 
  ; slt_plus              := bop_add_ann (bop_union eq) c
  ; slt_trans             := ltr_insert eq 
  ; slt_plus_certs        :=
      (* triple UGLY!  need some abstraction here.... FIX someday .... *) 
      @sg_certs_add_ann 
        (finite_set S)
        c 
        (wS :: nil)
        (λ (l : finite_set S), if brel_set eq nil l then (wS :: nil) else nil)
        (sg_certs_from_sg_CI_certs
           (finite_set S) 
           (brel_set eq)
           (bop_union eq) 
           (wS :: nil)
           (λ (l : finite_set S), if brel_set eq nil l then (wS :: nil) else nil)
           (sg_CI_certs_union eqv))
  ; slt_trans_certs       := ltr_insert_certs wS f 
  ; slt_exists_plus_ann_d := Certify_Exists_Ann  (inl c)                                  
  ; slt_id_ann_certs_d    := slt_union_insert_exists_id_ann_certify fin_d 
  ; slt_certs             := union_insert_slt_certs c wS f
  ; slt_ast               := Cas_ast ("slt_union_insert", (Cas_eqv_ast (eqv_ast eqv)) :: (Cas_ast_constant c) :: nil)
|}.
  
End CAS.

Section MCAS.

Definition mcas_slt_union_insert {S : Type} (eqv : @mcas_eqv S) (c : cas_constant):=
match eqv with
| EQV_eqv A    => slt_classify (SLT (slt_union_insert A c))
| EQV_Error sl => SLT_Error sl     
end.
  

End MCAS.

Section Verify.


Lemma correct_certs_union_insert
      (S : Type)
      (c : cas_constant)
      (eq : brel S)
      (wS : S)
      (f : S → S)
      (nt : brel_not_trivial S eq f) 
      (eqvP : eqv_proofs S eq) :    
      union_insert_slt_certs c wS f 
      = 
      P2C_slt (brel_sum brel_constant (brel_set eq))
              (bop_add_ann (bop_union eq) c)
              (ltr_insert eq)
              (union_insert_slt_proofs S c eq wS f nt eqvP). 
Proof. compute. reflexivity. Qed. 
  

Lemma correct_id_ann_certs_union_insert
      (S : Type)
      (c : cas_constant)
      (eq : brel S)
      (wS : S)
      (fin_d : carrier_is_finite_decidable S eq)
      (ref : brel_reflexive S eq)
      (sym : brel_symmetric S eq) 
      (trn : brel_transitive S eq) : 
     slt_union_insert_exists_id_ann_certify (p2c_is_finite_check S eq fin_d)
     =
     p2c_slt_exists_id_ann_check 
        (brel_sum brel_constant (brel_set eq))
        (bop_add_ann (bop_union eq) c) 
        (ltr_insert eq)
        (slt_union_insert_exists_id_ann_decide 
            S c wS eq ref sym trn fin_d). 
Proof. unfold p2c_slt_exists_id_ann_check, slt_union_insert_exists_id_ann_decide,
              slt_union_insert_exists_id_ann_certify, p2c_is_finite_check; 
              destruct fin_d as [[enum A] | C]; simpl; reflexivity. 
Qed.

  
Theorem correct_union_insert (S : Type) (eqv: A_eqv S) (c : cas_constant) : 
    slt_union_insert (A2C_eqv S eqv) c
    =
    A2C_slt (A_slt_union_insert S eqv c).
Proof. unfold slt_union_insert, A_slt_union_insert, A2C_slt; simpl.
       rewrite correct_eqv_set.       
       rewrite correct_eqv_add_constant. 
       rewrite correct_ltr_insert_certs.
       rewrite <- correct_certs_union_insert.               
       rewrite <- correct_id_ann_certs_union_insert.
       (* UGLY! *)
       unfold A_sg_proofs_from_sg_CI_proofs. 
       unfold sg_certs_from_sg_CI_certs.
       rewrite correct_bop_union_certs.
       rewrite <- correct_sg_certs_add_ann.
       rewrite <- correct_sg_certs_from_sg_C_certs.       
       rewrite <- correct_sg_C_certs_from_sg_CI_certs.              
       reflexivity.
Qed. 

 
Theorem correct_bop_mcas_union_insert (S : Type) (eqvS : @A_mcas_eqv S) (c : cas_constant): 
         mcas_slt_union_insert (A2C_mcas_eqv S eqvS) c
         = 
         A2C_mcas_slt (A_mcas_slt_union_insert S eqvS c). 
Proof. unfold mcas_slt_union_insert, A_mcas_slt_union_insert.
       unfold A_slt_classify, slt_classify.       
       destruct eqvS; unfold A2C_mcas_eqv. 
       + simpl. reflexivity. 
       + rewrite correct_union_insert.
         rewrite <- correctness_slt_classify_slt.
         reflexivity. 
Qed.  

End Verify.   
