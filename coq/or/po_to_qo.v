
Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.
Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.or.properties.
Require Import CAS.coq.or.structures. 

Close Scope nat. 

Definition embedding_not_antisymmetric (S T : Type) (eqS : brel S) (lte : brel T) (h : S -> T) := 
{z : S * S & let (s, t) := z in ((lte (h s) (h t) = true) * (lte (h t) (h s) = true) * (eqS s t = false))}. 

Definition embedding_not_total (S T : Type) (lte : brel T) (h : S -> T) := 
{z : S * S & let (s, t) := z in ((lte (h s) (h t) = false) * (lte (h t) (h s) = false))}.

Definition fun_congruence (S T : Type) (eqS : brel S) (eqT : brel T) (h : S -> T) := 
   ∀ (s t : S), eqS s t = true -> eqT (h s) (h t) = true.

Section Compute.

Definition brel_po_to_qo {T S : Type} (h : T -> S) (lte : brel S) : brel T
  := λ x y, lte (h x) (h y). 

End Compute. 


Section Theory.

Variable S  : Type.   
Variable T  : Type.

Variable eqS : brel S.
Variable eqT : brel T.
Variable refT : brel_reflexive T eqT.

Variable h     : S -> T.
Variable lte   : brel T.
Variable lteRef : brel_reflexive T lte.
Variable lteTran : brel_transitive T lte.
Variable lteAnti : brel_antisymmetric T eqT lte.
Variable lteCong : brel_congruence T eqT lte. 
Variable hCong : fun_congruence S T eqS eqT h.

Lemma po_to_qo_congruence : brel_congruence S eqS (brel_po_to_qo h lte).
Proof. compute. intros s t u v A B.
       assert (C := hCong _ _ A). assert (D := hCong _ _ B). 
       rewrite (lteCong _ _ _ _ C D). 
       reflexivity.
Qed.        
       
Lemma po_to_qo_reflexive : brel_reflexive S  (brel_po_to_qo h lte).
Proof. intro s. compute; auto. Qed.

Lemma po_to_qo_transitive : brel_transitive S  (brel_po_to_qo h lte).
Proof. intros s t u. compute. intros A B. exact (lteTran _ _ _ A B). Qed. 

Lemma po_to_qo_not_antisymmetric (P :embedding_not_antisymmetric S T eqS lte h) : 
     brel_not_antisymmetric S eqS (brel_po_to_qo h lte).
Proof. unfold brel_not_antisymmetric. compute. exact P. Defined. 


Lemma po_to_qo_total (tot : brel_total T lte) : brel_total S (brel_po_to_qo h lte).
Proof. compute. intros s t. apply tot. Qed. 

Lemma po_to_qo_not_total (Q : embedding_not_total S T lte h) : brel_not_total S (brel_po_to_qo h lte).
Proof. compute.  exact Q. Defined. 

Definition po_to_qo_not_total_decide : 
  (brel_total T lte) + (embedding_not_total S T lte h) -> brel_total_decidable S (brel_po_to_qo h lte)
:= λ d,
     match d with
     | inl tot => inl (po_to_qo_total tot) 
     | inr Q   => inr (po_to_qo_not_total Q) 
     end.


Lemma po_to_qo_is_qo_bottom
      (bottom : T) (P: brel_is_bottom T lte bottom) (s : S) (Q : eqT (h s) bottom = true)
           : brel_is_qo_bottom S eqS (brel_po_to_qo h lte) s.
Proof. compute. split.
       intro t. rewrite (lteCong _ _ _ _ Q (refT (h t))). apply P. 
       intros t A B. (* need lte (h t) bottom = true -> eqT (h t) bottom = true -> s [=S] t *) 
Admitted. 

Lemma po_to_qo_is_qo_top
      (top : T) (P: brel_is_top T lte top) (s : S) (Q : eqT (h s) top = true)
           : brel_is_qo_top S eqS (brel_po_to_qo h lte) s.
Proof. compute. split.
       intro t. rewrite (lteCong _ _ _ _ (refT (h t)) Q). apply P. 
       intros t A B. (* need lte top (h t) = true -> eqT (h t) top = true -> s [=S] t *) 
Admitted. 


Lemma po_to_qo_not_exists_qo_top : brel_not_exists_qo_top S eqS (brel_po_to_qo h lte). 
Proof. unfold brel_not_exists_qo_top. intro s. unfold brel_not_is_qo_top. 
Admitted. 
  
End Theory.


Section ACAS.

Definition po_to_qo_proofs 
    (S T : Type) 
    (eqS : brel S)
    (eqT : brel T)
    (lte : brel T)        
    (poP : po_proofs T eqT lte)    
    (h : S -> T)
    (hCong : fun_congruence S T eqS eqT h) 
    (P : embedding_not_antisymmetric S T eqS lte h)
    (D : embedding_not_total S T lte h) := 
let lteCong := A_po_congruence T eqT lte poP in  
let lteRef  := A_po_reflexive T eqT lte poP in  
let lteTran := A_po_transitive T eqT lte poP in          
{|
  A_qo_congruence        := po_to_qo_congruence S T eqS eqT h lte lteCong hCong
; A_qo_reflexive         := po_to_qo_reflexive S T h lte lteRef 
; A_qo_transitive        := po_to_qo_transitive S T h lte lteTran 
; A_qo_not_antisymmetric := po_to_qo_not_antisymmetric S T eqS h lte P 
; A_qo_not_total         := po_to_qo_not_total S T h lte D 
|}.
  

Definition po_to_wp_proofs 
    (S T : Type) 
    (eqS : brel S)
    (eqT : brel T)
    (lte : brel T)        
    (poP : po_proofs T eqT lte)    
    (h : S -> T)
    (hCong : fun_congruence S T eqS eqT h) 
    (P : embedding_not_antisymmetric S T eqS lte h)
    (D : brel_total T lte) := 
let lteCong := A_po_congruence T eqT lte poP in  
let lteRef  := A_po_reflexive T eqT lte poP in  
let lteTran := A_po_transitive T eqT lte poP in          
{|
  A_wp_congruence        := po_to_qo_congruence S T eqS eqT h lte lteCong hCong
; A_wp_reflexive         := po_to_qo_reflexive S T h lte lteRef 
; A_wp_transitive        := po_to_qo_transitive S T h lte lteTran 
; A_wp_not_antisymmetric := po_to_qo_not_antisymmetric S T eqS h lte P 
; A_wp_total             := po_to_qo_total S T h lte D 
|}.




Definition A_po_to_qo
    (S T : Type) 
    (eqvS : A_eqv S)
    (po : A_po T)    
    (h : S -> T)
    (hCong : fun_congruence S T (A_eqv_eq S eqvS) (A_eqv_eq T (A_po_eqv T po)) h) 
    (P : embedding_not_antisymmetric S T (A_eqv_eq S eqvS) (A_po_lte T po) h)
    (D : (brel_total T (A_po_lte T po)) + (embedding_not_total S T (A_po_lte T po) h)) := 
let eqS := A_eqv_eq S eqvS in 
let eqT := A_eqv_eq T (A_po_eqv T po) in 
let lte := A_po_lte T po in 
{|
  A_qo_eqv    := eqvS 
; A_qo_lte    := brel_po_to_qo h lte
; A_qo_proofs := po_to_qo_proofs S T eqS eqT lte (A_po_proofs T po) h hCong P D
; A_qo_ast    := Ast_qo_length (A_po_ast T po)
|}.

End ACAS.


Section CAS.

Definition po_to_qo_certs 
    (S T : Type) 
    (eqS : brel S)
    (eqT : brel T)
    (lte : brel T)        
    (h : S -> T)
    (p : S * S) 
    (D : (@assert_total S) + (S * S)) := 
{|
  qo_congruence        := Assert_Brel_Congruence 
; qo_reflexive         := Assert_Reflexive
; qo_transitive        := Assert_Transitive
; qo_not_antisymmetric := Assert_Not_Antisymmetric p 
; qo_total_d           := match D with
                          | inl _ => Certify_Total 
                          | inr p => Certify_Not_Total p
                          end 
|}.

Definition po_to_qo
    {S T : Type} 
    (eqvS : @eqv S)
    (po : @po T)    
    (h : S -> T)
    (P : S * S) 
    (D : (@assert_total S) + (S * S)) := 
let eqS := eqv_eq eqvS in 
let eqT := eqv_eq (po_eqv po) in 
let lte := po_lte po in 
{|
  qo_eqv   := eqvS 
; qo_lte   := brel_po_to_qo h lte
; qo_certs := po_to_qo_certs S T eqS eqT lte h P D
; qo_ast   := Ast_qo_length (po_ast po)
|}.
  

End CAS.

Section Verify.

Definition P2C_P
    (S T : Type) 
    (eqS : brel S)
    (lte : brel T)        
    (h : S -> T)
    (P : embedding_not_antisymmetric S T eqS lte h) := projT1 P.

Definition P2C_D
    (S T : Type) 
    (lte : brel T)        
    (h : S -> T)
    (D : (brel_total T lte) + (embedding_not_total S T lte h)) : (@assert_total S) + (S * S)
:=
    match D with
    | inl _ => inl Assert_Total 
    | inr Q => inr (projT1 Q)
    end.

  
Theorem correct_po_to_qo
    (S T : Type)
    (eqvS : A_eqv S)
    (po : A_po T)    
    (h : S -> T)
    (hCong : fun_congruence S T (A_eqv_eq S eqvS) (A_eqv_eq T (A_po_eqv T po)) h) 
    (P : embedding_not_antisymmetric S T (A_eqv_eq S eqvS) (A_po_lte T po) h)
    (D : (brel_total T (A_po_lte T po)) + (embedding_not_total S T (A_po_lte T po) h)) :
    po_to_qo (A2C_eqv S eqvS) (A2C_po T po) h (P2C_P _ _ _ _ h P) (P2C_D _ _ _ h D) 
    = 
    A2C_qo S (A_po_to_qo S T eqvS po h hCong P D). 
Proof. unfold po_to_qo, A_po_to_qo, A2C_qo, P2C_P, P2C_D ; simpl.
       destruct D as [tot | [[s t] A]]; auto. 
Qed.        
  
 
End Verify.   
  
