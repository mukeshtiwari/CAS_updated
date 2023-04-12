Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.

Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.eqv.theory.
Require Import CAS.coq.eqv.sum.
Require Import CAS.coq.eqv.product.

Require Import CAS.coq.sg.and. 

Require Import CAS.coq.tr.properties.
Require Import CAS.coq.tr.structures.

Section Compute.

  Definition ltr_sum 
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


End Compute.   


Section Theory.

  Variable  S LS T LT: Type.
  Variable eqS : brel S.
  Variable eqT : brel T.
  Variable eqLS : brel LS.
  Variable eqLT : brel LT.
  Variable refS : brel_reflexive S eqS.   
  Variable refT : brel_reflexive T eqT. 
  Variable wS : S.
  Variable wT : T.
  Variable wLS : LS.
  Variable wLT : LT.
  Variable f : S -> S. 
  Variable ntS : brel_not_trivial S eqS f. 
  Variable g : T -> T. 
  Variable ntT : brel_not_trivial T eqT g. 
  Variable (ltrS : ltr_type LS S).
  Variable (ltrT : ltr_type LT T).
  Variable (congS : ltr_congruence _ _ eqLS eqS ltrS).
  Variable (congT : ltr_congruence _ _ eqLT eqT ltrT).   

  Definition eqProdLSLT := brel_product eqLS eqLT.
  Definition eqSumST  := brel_sum eqS eqT.   


   Lemma ltr_sum_congruence : ltr_congruence _ _ eqProdLSLT eqSumST (ltr_sum ltrS ltrT).  
   Proof. intros [ls1 lt1] [ls2 lt2] [s | s] [t | t] A B; simpl; simpl in A, B; auto. 
          - apply bop_and_elim in A. destruct A as [A C].
            apply congS; auto. 
          - apply bop_and_elim in A. destruct A as [A C].
            apply congT; auto. 
   Qed.             


 Lemma ltr_sum_left_cancellative
   (fLC : ltr_left_cancellative _ _ eqS ltrS)
   (gLC : ltr_left_cancellative _ _ eqT ltrT):    
   ltr_left_cancellative _ _ eqSumST (ltr_sum ltrS ltrT).  
 Proof. unfold ltr_left_cancellative.
        intros [l1 l2] [s1 | t1] [s2 | t2]; simpl; intro A. 
        - exact (fLC _ _ _ A). 
        - discriminate A. 
        - discriminate A. 
        - exact (gLC _ _ _ A). 
Qed.        

 Lemma ltr_sum_not_left_cancellative_left 
   (fNLC : ltr_not_left_cancellative _ _ eqS ltrS): 
   ltr_not_left_cancellative _ _ eqSumST (ltr_sum ltrS ltrT).  
 Proof. destruct fNLC as [[ls [s s']] [A B]].
        exists ((ls, wLT), (inl s, inl s')). simpl.
        split; auto. 
Defined.   

 Lemma ltr_sum_not_left_cancellative_right
   (gNLC : ltr_not_left_cancellative _ _ eqT ltrT) :             
   ltr_not_left_cancellative _ _ eqSumST (ltr_sum ltrS ltrT).  
 Proof. destruct gNLC as [[lt [t t']] [A B]].
        exists ((wLS, lt), (inr t, inr t')). simpl.
        split; auto. 
 Defined. 

 Definition ltr_sum_left_cancellative_decide
   (fLC_d : ltr_left_cancellative_decidable _ _ eqS ltrS)
   (gLC_d : ltr_left_cancellative_decidable _ _ eqT ltrT):    
   ltr_left_cancellative_decidable _ _ eqSumST (ltr_sum ltrS ltrT) :=
   match fLC_d with
   | inl fLC =>
       match gLC_d with
       | inl gLC => inl (ltr_sum_left_cancellative fLC gLC)
       | inr gNLC => inr (ltr_sum_not_left_cancellative_right gNLC) 
       end 
   | inr fNLC => inr (ltr_sum_not_left_cancellative_left  fNLC) 
   end .
 

 Lemma ltr_sum_not_left_constant : 
   ltr_not_left_constant _ _ eqSumST (ltr_sum ltrS ltrT).  
 Proof. exists ((wLS, wLT),  (inl wS, inr wT)). 
        compute. reflexivity.
 Defined. 

 Lemma ltr_sum_is_right
   (fIR : ltr_is_right _ _ eqS ltrS)
   (gIR : ltr_is_right _ _ eqT ltrT):    
   ltr_is_right _ _ eqSumST (ltr_sum ltrS ltrT).  
 Proof. intros [l1 l2] [s | t]; simpl; auto. Qed.        


 Lemma ltr_sum_not_is_right_left
   (fNIR : ltr_not_is_right _ _ eqS ltrS): 
   ltr_not_is_right _ _ eqSumST (ltr_sum ltrS ltrT).  
 Proof. destruct fNIR as [[l s] A]. 
        exists ((l, wLT), (inl s)); simpl; auto.
 Defined. 

  Lemma ltr_sum_not_is_right_right
   (gNIR : ltr_not_is_right _ _ eqT ltrT):    
   ltr_not_is_right _ _ eqSumST (ltr_sum ltrS ltrT).  
 Proof. destruct gNIR as [[l t] A]. 
        exists ((wLS, l), (inr t)); simpl; auto.
 Defined.


  Definition ltr_sum_is_right_decide
   (fIR_d : ltr_is_right_decidable _ _ eqS ltrS)
   (gIR_d : ltr_is_right_decidable _ _ eqT ltrT):    
   ltr_is_right_decidable _ _ eqSumST (ltr_sum ltrS ltrT) :=
   match fIR_d with
   | inl fIR =>
       match gIR_d with
       | inl gIR => inl (ltr_sum_is_right fIR gIR)
       | inr gNIR => inr (ltr_sum_not_is_right_right gNIR) 
       end 
   | inr fNIR => inr (ltr_sum_not_is_right_left fNIR) 
   end .


 Lemma ltr_sum_exists_id 
   (IDS : ltr_exists_id _ _ eqS ltrS)
   (IDT : ltr_exists_id _ _ eqT ltrT):    
    ltr_exists_id _ _ eqSumST (ltr_sum ltrS ltrT).  
 Proof. destruct IDS as [iS A].
        destruct IDT as [iT B].
        exists (iS, iT).
        intros [s | t]; simpl; auto. 
 Defined.


  Lemma ltr_sum_not_exists_id_left
   (NIDS : ltr_not_exists_id _ _ eqS ltrS) : 
    ltr_not_exists_id _ _ eqSumST (ltr_sum ltrS ltrT).  
  Proof. intros [ls lt].
         destruct (NIDS ls) as [s A]. 
         exists (inl s). simpl; auto. 
  Defined. 

  Lemma ltr_sum_not_exists_id_right
   (NIDT : ltr_not_exists_id _ _ eqT ltrT):    
    ltr_not_exists_id _ _ eqSumST (ltr_sum ltrS ltrT).  
  Proof. intros [ls lt].
         destruct (NIDT lt) as [t A]. 
         exists (inr t). simpl; auto. 
  Defined. 

  Definition ltr_sum_exists_id_decide
   (IDS_d : ltr_exists_id_decidable _ _ eqS ltrS)
   (IDT_d : ltr_exists_id_decidable _ _ eqT ltrT):    
   ltr_exists_id_decidable _ _ eqSumST (ltr_sum ltrS ltrT) :=
   match IDS_d with
   | inl IDS =>
       match IDT_d with
       | inl IDT => inl (ltr_sum_exists_id IDS IDT)
       | inr NIDT => inr (ltr_sum_not_exists_id_right NIDT) 
       end 
   | inr NIDS => inr (ltr_sum_not_exists_id_left NIDS) 
   end .


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
  
