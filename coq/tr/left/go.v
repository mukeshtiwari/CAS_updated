Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.

Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.eqv.theory.
Require Import CAS.coq.eqv.sum.
Require Import CAS.coq.eqv.product. 

Require Import CAS.coq.tr.properties.
Require Import CAS.coq.tr.structures.

Section Compute.

  Definition go_left
    {A B C D  : Type }
    (f : ltr_type A B)           (* A -> B -> B *)                
    (g : ltr_type C D) :         (* C -> D -> D *)
    ltr_type (A * C) (B + D) :=  (* (A * C) -> (B + D) -> (B + D) *) 
    λ  (p : (A * C)), λ (v : B + D), 
    match p with
    | (a, c) =>
        match v with
        | inl b => inl (f a b)
        | inr d => inr (g c d)                        
        end
    end.


    Definition ltr_left_product
    {A B D : Type }
    (f : ltr_type A B) :   (* A -> B -> B *)                
    ltr_type A (B * D) :=  (* A -> (B * D) -> (B * D) *) 
    λ  (a : A), λ (v : B * D), 
     match v with
    | (b, d) => (f a b, d) 
    end.

    Definition ltr_right_product 
    {B C D : Type }
    (g : ltr_type C D) :    (* C -> D -> D *)
    ltr_type C (B * D) :=   (* C -> (B * D) -> (B * D) *)       
    λ  (c : C), λ (v : B * D), 
     match v with
    | (b, d) => (b, g c d) 
     end.

    (* note: this does not work well as a bottom-up combinator 
       over bi-semigroups sincre requires same 
       additive component. 
    *) 
    Definition ltr_co_pair
      {A B C : Type }
    (f : ltr_type A B)      (* A -> B -> B *)      
    (g : ltr_type C B) :    (* C -> B -> B *)
    ltr_type (A + C) B :=   (* (A + C) B -> B *)
    λ  (d : A + C), λ (b : B), 
     match d with
     | inl a => f a b
     | inr c => g c b
     end.

    
    Definition go_right_derived 
    {A B C D : Type }
    (f : ltr_type A B)           (* A -> B -> B *)                
    (g : ltr_type C D) :         (* C -> D -> D *)
    ltr_type (A + C) (B * D) :=  (* (A + C) -> (B * D) -> (B * D) *) 
      ltr_co_pair (ltr_left_product f) (ltr_right_product g). 
  

    Definition go_right
    {A B C D : Type }
    (f : ltr_type A B)           (* A -> B -> B *)                
    (g : ltr_type C D) :         (* C -> D -> D *)
    ltr_type (A + C) (B * D) :=  (* (A + C) -> (B * D) -> (B * D) *) 
    λ  (p : (A + C)), λ (v : B * D), 
     match v with
    | (b, d) =>
        match p with
        | inl a =>(f a b, d) 
        | inr c => (b, g c d)                                
        end
    end.

End Compute.   


Section Theory.

  Variable  S LS T LT: Type.
  Variable eqS : brel S.
  Variable eqT : brel T.
  Variable eqLS : brel LS.
  Variable eqLT : brel LT.    
  Variable wS : S.
  Variable wT : T.
  Variable wLS : LS.
  Variable wLT : LT.  

  Variable (f : ltr_type LS S).
  Variable (g : ltr_type LT T).

  Definition eqProdST := brel_product eqS eqT.
  Definition eqSumLSLT  := brel_sum eqLS eqLT.

  Definition eqProdLSLT := brel_product eqLS eqLT.
  Definition eqSumST  := brel_sum eqS eqT.   


 Lemma go_right_congruence : ltr_congruence _ _ eqSumLSLT eqProdST (go_right f g). 
 Proof. unfold ltr_congruence.
        intros [ls1 | lt1] [ls2 | lt2] [s1 t1] [s2 t2] A B.         
        - apply brel_product_intro.
          + admit.
          + admit.             
        - admit.
        - admit.
        - admit.           
 Admitted.

 Lemma go_left_congruence : ltr_congruence _ _ eqProdLSLT eqSumST (go_left f g).  
 Admitted.


 Lemma go_left_left_cancellative
   (fLC : ltr_left_cancellative _ _ eqS f)
   (gLC : ltr_left_cancellative _ _ eqT g):    
   ltr_left_cancellative _ _ eqSumST (go_left f g).  
 Proof. unfold ltr_left_cancellative.
        intros [l1 l2] [s1 | t1] [s2 | t2]; simpl; intro A. 
        - exact (fLC _ _ _ A). 
        - discriminate A. 
        - discriminate A. 
        - exact (gLC _ _ _ A). 
Qed.        

 Lemma go_right_left_cancellative
   (fLC : ltr_left_cancellative _ _ eqS f)
   (gLC : ltr_left_cancellative _ _ eqT g):    
   ltr_left_cancellative _ _ eqProdST (go_right f g).  
 Proof. unfold ltr_left_cancellative.
        intros [l | l] [s1 t1] [s2 t2]; intro A;
        apply brel_product_elim in A; destruct A as [A B]. 
        - apply brel_product_intro; auto. 
          exact (fLC _ _ _ A).
        - apply brel_product_intro; auto. 
          exact (gLC _ _ _ B).           
Qed.        
 
 Lemma go_left_is_right
   (fIR : ltr_is_right _ _ eqS f)
   (gIR : ltr_is_right _ _ eqT g):    
   ltr_is_right _ _ eqSumST (go_left f g).  
 Proof. unfold ltr_is_right.
        intros [l1 l2] [s | t]; simpl. 
        - apply fIR. 
        - apply gIR. 
Qed.        


 Lemma go_right_is_right
   (refS : brel_reflexive _ eqS)          
   (refT : brel_reflexive _ eqT) 
   (fIR : ltr_is_right _ _ eqS f)
   (gIR : ltr_is_right _ _ eqT g):    
   ltr_is_right _ _ eqProdST (go_right f g).  
 Proof. unfold ltr_is_right.
        intros [l | l] [s t]; unfold go_right. 
        - apply brel_product_intro.
          + apply fIR.
          + apply refT. 
        - apply brel_product_intro.
          + apply refS. 
          + apply gIR. 
Qed.        
 

 Lemma go_left_not_left_constant : 
   ltr_not_left_constant _ _ eqSumST (go_left f g).  
 Proof. exists ((wLS, wLT),  (inl wS, inr wT)).
        compute. reflexivity.
 Defined. 


  Lemma go_right_left_constant : 
   ltr_left_constant _ _ eqProdST (go_right f g).  
 Proof. unfold ltr_left_constant.
        intros [l | l] [s1 t1] [s2 t2]; unfold go_right. 
        - admit. (*need eqT NT*) 
        - admit. (*need eqS NT*) 
 Admitted. 

 
(*
Lemma ltr_cons_not_exists_id : ltr_not_exists_id S (list S) (brel_list eq) ltr_cons. 
Lemma ltr_cons_not_exists_ann : ltr_not_exists_ann S (list S) (brel_list eq) ltr_cons. 
*)  
 
End Theory.

Section ACAS.

(*
Definition ltr_cons_proofs (S : Type) (eq : brel S) (s : S) (eqvP : eqv_proofs S eq) :
    left_transform_proofs S (list S) (brel_list eq) eq (@ltr_cons S) := 
{|
  A_left_transform_congruence          := 
; A_left_transform_is_right_d          := 
; A_left_transform_left_constant_d     := 
; A_left_transform_left_cancellative_d := 
|}.

Definition A_ (S : Type) (eqv : A_eqv S) :=
{|
  A_left_transform_carrier      := 
; A_left_transform_label        := 
; A_left_transform_ltr          := 
; A_left_transform_exists_id_d  := 
; A_left_transform_exists_ann_d := 
; A_left_transform_proofs       := 
; A_left_transform_ast          := Cas_ast ("", []) 
|}.
*) 
End ACAS.

Section CAS.

End CAS. 


Section Verify.

(*
Lemma correct_ltr_certs_cons (S : Type) (eS : A_eqv S): 
    ltr_cons_certs (A_eqv_witness S eS)
    =                    
    P2C_left_transform S
            (list S)
            (brel_list (A_eqv_eq S eS))
            (A_eqv_eq S eS)
            ltr_cons
            (ltr_cons_proofs S (A_eqv_eq S eS) (A_eqv_witness S eS) (A_eqv_proofs S eS)). 
Proof. compute. reflexivity. Qed. 


Theorem correct_left_transform_cons (S : Type) (eS : A_eqv S)  : 
         left_transform_cons (A2C_eqv S eS) 
         = 
         A2C_left_transform S (list S) (A_left_transform_cons S eS). 
Proof. unfold left_transform_cons, A2C_left_transform, A_left_transform_cons. simpl. 
       rewrite correct_eqv_list. 
       rewrite <- correct_ltr_certs_cons. 
       reflexivity. 
Qed. 
  
 *)  
 
End Verify.   
  
