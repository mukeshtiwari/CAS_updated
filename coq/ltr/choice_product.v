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


  Definition ltr_choice_product
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


 (* Note : ltr_choice_product could be derived from more basic 
   combinators. 

    Definition ltr_co_pair
      {A B C : Type }
    (f : ltr_type A B)      (* A -> B -> B *)      
    (g : ltr_type C B) :    (* C -> B -> B *)
    ltr_type (A + C) B :=   (* (A + C) -> B -> B *)
    λ  (d : A + C), λ (b : B), 
     match d with
     | inl a => f a b
     | inr c => g c b
     end.

    (* could be defined as the product of f with id ltr *)
    Definition ltr_left_product
    {A B D : Type }
    (f : ltr_type A B) :   (* A -> B -> B *)                
    ltr_type A (B * D) :=  (* A -> (B * D) -> (B * D) *) 
    λ  (a : A), λ (v : B * D), 
     match v with
    | (b, d) => (f a b, d) 
    end.

    (* could be defined as the product of id ltr with g *)
    Definition ltr_right_product 
    {B C D : Type }
    (g : ltr_type C D) :    (* C -> D -> D *)
    ltr_type C (B * D) :=   (* C -> (B * D) -> (B * D) *)       
    λ  (c : C), λ (v : B * D), 
     match v with
    | (b, d) => (b, g c d) 
     end.
    
    
    Definition ltr_choice_product_derived 
    {A B C D : Type }
    (f : ltr_type A B)           (* A -> B -> B *)                
    (g : ltr_type C D) :         (* C -> D -> D *)
    ltr_type (A + C) (B * D) :=  (* (A + C) -> (B * D) -> (B * D) *) 
      ltr_co_pair (ltr_left_product f) (ltr_right_product g). 


    However, the ltr_co_pair combinator does not 
    work well as as a bottom-up combinator for semigroup transforms. 
    Why? Suppose (S1, L1, +_1, |1>) and (S2, L2, +_2, |2>) 
    are semigroup transforms and we want to combine them so 
    that the new multiplicative operation is 
    "ltr_co_pair |1> |2>". Then we have to make sure that S1=S2, 
     which is difficult. 
    *)

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

  Definition eqProdST := brel_product eqS eqT.
  Definition eqSumLSLT  := brel_sum eqLS eqLT.


 Lemma ltr_choice_product_congruence : ltr_congruence _ _ eqSumLSLT eqProdST (ltr_choice_product ltrS ltrT). 
 Proof. intros [ls1 | lt1] [ls2 | lt2] [s1 t1] [s2 t2] A B; simpl in *;
          apply bop_and_elim in B; destruct B as [B C]; auto. 
        - apply brel_product_intro; auto. 
        - discriminate A. 
        - discriminate A. 
        - apply brel_product_intro; auto. 
 Qed. 

 
 Lemma ltr_choice_product_left_cancellative
   (fLC : ltr_left_cancellative _ _ eqS ltrS)
   (gLC : ltr_left_cancellative _ _ eqT ltrT):    
   ltr_left_cancellative _ _ eqProdST (ltr_choice_product ltrS ltrT).  
 Proof. unfold ltr_left_cancellative.
        intros [l | l] [s1 t1] [s2 t2]; intro A;
        apply brel_product_elim in A; destruct A as [A B]. 
        - apply brel_product_intro; auto. 
          exact (fLC _ _ _ A).
        - apply brel_product_intro; auto. 
          exact (gLC _ _ _ B).           
Qed.        


 Lemma ltr_choice_product_not_left_cancellative_left 
   (fNLC : ltr_not_left_cancellative _ _ eqS ltrS): 
   ltr_not_left_cancellative _ _ eqProdST (ltr_choice_product ltrS ltrT).  
 Proof. destruct fNLC as [[ls [s s']] [A B]].
        exists ((inl ls), ((s, wT), (s', wT))). simpl.
        rewrite A, B. rewrite (refT wT). compute; auto. 
 Defined.   

Lemma ltr_choice_product_not_left_cancellative_right 
   (gNLC : ltr_not_left_cancellative _ _ eqT ltrT): 
   ltr_not_left_cancellative _ _ eqProdST (ltr_choice_product ltrS ltrT).  
 Proof. destruct gNLC as [[lt [t t']] [A B]].
        exists ((inr lt), ((wS, t), (wS, t'))). simpl.
        rewrite A, B. rewrite (refS wS). compute; auto. 
 Defined.   


 Definition ltr_choice_product_left_cancellative_decide
   (fLC_d : ltr_left_cancellative_decidable _ _ eqS ltrS)
   (gLC_d : ltr_left_cancellative_decidable _ _ eqT ltrT):    
   ltr_left_cancellative_decidable _ _ eqProdST (ltr_choice_product ltrS ltrT) :=
   match fLC_d with
   | inl fLC =>
       match gLC_d with
       | inl gLC => inl (ltr_choice_product_left_cancellative fLC gLC)
       | inr gNLC => inr (ltr_choice_product_not_left_cancellative_right gNLC) 
       end 
   | inr fNLC => inr (ltr_choice_product_not_left_cancellative_left  fNLC) 
   end .
 
  Lemma ltr_choice_product_not_left_constant : 
   ltr_not_left_constant _ _ eqProdST (ltr_choice_product ltrS ltrT).  
  Proof. exists ((inl wLS), ((wS, wT), (wS, g wT))). simpl.
         destruct (ntT wT) as [A B].
         rewrite A. compute. rewrite refS. reflexivity.
  Defined.

 Lemma ltr_choice_product_is_right
   (fIR : ltr_is_right _ _ eqS ltrS)
   (gIR : ltr_is_right _ _ eqT ltrT):    
   ltr_is_right _ _ eqProdST (ltr_choice_product ltrS ltrT).  
 Proof. intros [l | l] [s t]; simpl; apply brel_product_intro; auto. Qed.        
 

 Lemma ltr_choice_product_not_is_right_left
   (fNIR : ltr_not_is_right _ _ eqS ltrS): 
   ltr_not_is_right _ _ eqProdST (ltr_choice_product ltrS ltrT).  
 Proof. destruct fNIR as [[l s] A]. 
        exists ((inl l), (s, wT)). simpl. 
        rewrite A. reflexivity. 
 Qed. 

 Lemma ltr_choice_product_not_is_right_right
   (gNIR : ltr_not_is_right _ _ eqT ltrT):    
   ltr_not_is_right _ _ eqProdST (ltr_choice_product ltrS ltrT).  
 Proof. destruct gNIR as [[l t] A]. 
        exists ((inr l), (wS, t)). simpl. 
        rewrite A. rewrite refS. reflexivity. 
 Qed. 

  Definition ltr_choice_product_is_right_decide
   (fIR_d : ltr_is_right_decidable _ _ eqS ltrS)
   (gIR_d : ltr_is_right_decidable _ _ eqT ltrT):    
   ltr_is_right_decidable _ _ eqProdST (ltr_choice_product ltrS ltrT) :=
   match fIR_d with
   | inl fIR =>
       match gIR_d with
       | inl gIR => inl (ltr_choice_product_is_right fIR gIR)
       | inr gNIR => inr (ltr_choice_product_not_is_right_right gNIR) 
       end 
   | inr fNIR => inr (ltr_choice_product_not_is_right_left fNIR) 
   end .


 Lemma ltr_choice_product_exists_id_left
   (IDS : ltr_exists_id _ _ eqS ltrS) : 
   ltr_exists_id _ _ eqProdST (ltr_choice_product ltrS ltrT).  
 Proof. destruct IDS as [iS A].
        exists (inl iS).
        intros [s t]; simpl.
        rewrite refT. rewrite (A s).
        reflexivity. 
 Defined.

 Lemma ltr_choice_product_exists_id_right
   (IDT : ltr_exists_id _ _ eqT ltrT):    
   ltr_exists_id _ _ eqProdST (ltr_choice_product ltrS ltrT).  
 Proof. destruct IDT as [iT A].
        exists (inr iT).
        intros [s t]; simpl.
        rewrite refS. rewrite (A t).
        reflexivity. 
 Defined.

 Lemma ltr_choice_product_not_exists_id 
   (NIDS : ltr_not_exists_id _ _ eqS ltrS)
   (NIDT : ltr_not_exists_id _ _ eqT ltrT):    
    ltr_not_exists_id _ _ eqProdST (ltr_choice_product ltrS ltrT).  
 Proof. intros [ls | lt]. 
        - destruct (NIDS ls) as [s A].
          exists (s, wT). compute. rewrite A.
          reflexivity.
        - destruct (NIDT lt) as [t A].
          exists (wS, t). compute. rewrite A.
          rewrite refS. 
          reflexivity.
 Defined. 
 
  Definition ltr_choice_product_exists_id_decide
   (IDS_d : ltr_exists_id_decidable _ _ eqS ltrS)
   (IDT_d : ltr_exists_id_decidable _ _ eqT ltrT):    
      ltr_exists_id_decidable _ _ eqProdST (ltr_choice_product ltrS ltrT) :=
   match IDS_d with
   | inl IDS => inl (ltr_choice_product_exists_id_left IDS) 
   | inr NIDS =>
       match IDT_d with
       | inl IDT => inl (ltr_choice_product_exists_id_right IDT) 
       | inr NIDT => inr (ltr_choice_product_not_exists_id NIDS NIDT) 
       end 
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
  
