Require Import Coq.Bool.Bool. 
Require Import Coq.Strings.String.

Require Import CAS.coq.common.compute. 
Require Import CAS.coq.common.ast.

Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.eqv.add_constant.
Require Import CAS.coq.eqv.sum. 

Require Import CAS.coq.po.properties.
Require Import CAS.coq.po.structures.
Require Import CAS.coq.po.cast_up. 





Section Compute.

Definition brel_add_bottom : ∀ {S : Type}, brel S → cas_constant → brel (cas_constant + S)
:= λ  {S} lte c x y, 
   match x, y with
   | (inl _), (inl _) => true (* all constants equal! *) 
   | (inl _), (inr _) => true  (* new bottom ! *) 
   | (inr _), (inl _) => false 
   | (inr a), (inr b) => lte a b 
   end.
  

End Compute.   

Section Theory.
Variable bottom : cas_constant.
Variable S  : Type.  

Variable eq : brel S.
Variable refl : brel_reflexive S eq.

Variable lte : brel S.
Variable lteTran : brel_transitive S lte.
Variable lteRefl : brel_reflexive S lte. 
Variable lteCong : brel_congruence S eq lte.

Notation "a [+] b"  := (brel_add_bottom b a)       (at level 15).

Lemma brel_add_bottom_congruence : brel_congruence (with_constant S ) (brel_sum brel_constant eq) (bottom [+] lte). 
Proof. unfold brel_congruence. intros [s1 | t1] [s2 | t2] [s3 | t3] [s4 | t4]; compute; intros A B; auto; discriminate. Qed. 

Lemma brel_add_bottom_reflexive : brel_reflexive (with_constant S ) (bottom [+] lte). 
Proof. intros [c | s]; compute; auto. Qed. 

Lemma brel_add_bottom_transitive : brel_transitive (with_constant S ) (bottom [+] lte). 
Proof. intros [c1 | s1] [c2 | s2] [c3 | s3]; compute; intros A B; auto. 
       discriminate. exact (lteTran _ _ _ A B). 
Qed.

Lemma brel_add_bottom_antisymmetric (anti : brel_antisymmetric S eq lte):
     brel_antisymmetric (with_constant S ) (brel_sum brel_constant eq) (bottom [+] lte). 
Proof. intros [c1 | s1] [c2 | s2]; compute; intros A B; auto. Qed.

Lemma brel_add_bottom_not_antisymmetric (nanti : brel_not_antisymmetric S eq lte):
     brel_not_antisymmetric (with_constant S ) (brel_sum brel_constant eq) (bottom [+] lte). 
Proof. destruct nanti as [[s1 s2] [A B]]. exists (inr s1, inr s2); compute; auto. Defined.

Definition brel_add_bottom_antisymmetic_decide : 
  brel_antisymmetric_decidable S eq lte  →
     brel_antisymmetric_decidable (with_constant S) (brel_sum brel_constant eq) (bottom [+] lte)
:= λ dS,  
   match dS with 
   | inl anti  => inl _ (brel_add_bottom_antisymmetric anti)
   | inr nanti => inr _ (brel_add_bottom_not_antisymmetric nanti)
   end.  

Lemma brel_add_bottom_is_bottom : brel_is_bottom (with_constant S) (bottom [+] lte) (inl bottom). 
Proof. intros [c | s]; compute; auto. Qed.

Lemma brel_add_bottom_is_qo_bottom :
     brel_is_qo_bottom (with_constant S) (brel_sum brel_constant eq) (bottom [+] lte) (inl bottom). 
Proof. split. apply brel_add_bottom_is_bottom. 
       intros [c | s]; compute; auto.
Qed.      

Lemma brel_add_bottom_exists_bottom : brel_exists_bottom (with_constant S) (bottom [+] lte). 
Proof. exists (inl bottom). apply brel_add_bottom_is_bottom. Defined.

Lemma brel_add_bottom_exists_qo_bottom : brel_exists_qo_bottom (with_constant S) (brel_sum brel_constant eq) (bottom [+] lte). 
Proof. exists (inl bottom). apply brel_add_bottom_is_qo_bottom. Defined. 


Lemma brel_add_bottom_is_top (t : S) (top : brel_is_top S lte t) : brel_is_top (with_constant S) (bottom [+] lte) (inr t). 
Proof. intros [c | s]; compute; auto. Qed. 


Lemma brel_add_bottom_exists_top (top : brel_exists_top S lte) :
     brel_exists_top (with_constant S) (bottom [+] lte). 
Proof. destruct top as [t A]. exists (inr t). apply brel_add_bottom_is_top; auto. Defined. 

Lemma brel_add_bottom_not_exists_top (wS : S) (ntop : brel_not_exists_top S lte) :
    brel_not_exists_top (with_constant S) (bottom [+] lte). 
Proof. intros [c | s]. exists (inr wS); compute; auto. 
       destruct (ntop s) as [b A]. exists (inr b); compute; auto.
Defined.

Definition brel_add_bottom_exists_top_decide (wS : S) : 
     brel_exists_top_decidable S lte  → brel_exists_top_decidable (with_constant S) (bottom [+] lte)
:= λ dS,  
   match dS with 
   | inl top  => inl _ (brel_add_bottom_exists_top top)
   | inr ntop => inr _ (brel_add_bottom_not_exists_top wS ntop)
   end.  


Lemma brel_add_bottom_exists_qo_top (top : brel_exists_qo_top S eq lte) :
     brel_exists_qo_top (with_constant S) (brel_sum brel_constant eq) (bottom [+] lte). 
Proof. destruct top as [t A]. destruct A as [A B]; auto.
       exists (inr t). split.
       apply brel_add_bottom_is_top; auto. 
       intros [c | s]; compute; auto.
Defined. 

Lemma brel_add_bottom_not_exists_qo_top (wS : S) (ntop : brel_not_exists_qo_top S eq lte) :
    brel_not_exists_qo_top (with_constant S) (brel_sum brel_constant eq) (bottom [+] lte). 
Proof. unfold brel_not_exists_qo_top in ntop. unfold brel_not_exists_qo_top. 
       unfold brel_not_is_qo_top in ntop. unfold brel_not_is_qo_top. 
       intros [c | s].  
          left. unfold brel_not_is_top. exists (inr wS); compute; auto. 
          destruct (ntop s) as [[u A] | [u [[A B] C]]].
             left. exists (inr u); compute; auto.
             right. exists (inr u); compute; auto.
Defined.

Definition brel_add_bottom_exists_qo_top_decide (wS : S) : 
  brel_exists_qo_top_decidable S eq lte
  → brel_exists_qo_top_decidable (with_constant S) (brel_sum brel_constant eq) (bottom [+] lte)
:= λ dS,  
   match dS with 
   | inl top  => inl _ (brel_add_bottom_exists_qo_top top)
   | inr ntop => inr _ (brel_add_bottom_not_exists_qo_top wS ntop)
   end.  



Lemma brel_add_bottom_total (tot : brel_total S lte) : brel_total (with_constant S ) (bottom [+] lte). 
Proof. intros [c1 | s1] [c2 | s2]; compute; auto. Qed. 

Lemma brel_add_bottom_not_total (ntot : brel_not_total S lte) : brel_not_total (with_constant S ) (bottom [+] lte). 
Proof. destruct ntot as [[s1 s2] [A B]]. exists (inr s1, inr s2). compute; auto. Defined. 


Definition brel_add_bottom_total_decide : 
     brel_total_decidable S lte  → brel_total_decidable (with_constant S) (bottom [+] lte)
:= λ dS,  
   match dS with 
   | inl tot  => inl _ (brel_add_bottom_total tot)
   | inr ntot => inr _ (brel_add_bottom_not_total ntot)
   end.

Lemma brel_add_bottom_not_trivial (wS : S) : order_not_trivial (with_constant S ) (bottom [+] lte). 
Proof. exists (inr wS, inl bottom). compute. reflexivity. Defined. 


End Theory.

Section ACAS.

Section Proofs.   

Variables (S : Type) (eq lte : brel S) (bottom : cas_constant) (wS : S).

Definition or_proofs_add_bottom (orP : or_proofs S eq lte) : 
      or_proofs (with_constant S) (brel_sum brel_constant eq) (brel_add_bottom lte bottom) := 
{|
  A_or_congruence      := brel_add_bottom_congruence bottom S eq lte (A_or_congruence _ _ _ orP)  
; A_or_reflexive       := brel_add_bottom_reflexive bottom S lte (A_or_reflexive _ _ _ orP)
; A_or_transitive      := brel_add_bottom_transitive bottom S lte (A_or_transitive _ _ _ orP)                                                    
; A_or_antisymmetric_d := brel_add_bottom_antisymmetic_decide bottom S eq lte (A_or_antisymmetric_d _ _ _ orP) 
; A_or_total_d         := brel_add_bottom_total_decide bottom S lte (A_or_total_d _ _ _ orP) 
; A_or_trivial_d       := inr (brel_add_bottom_not_trivial bottom S lte wS) 
|}. 

End Proofs.

Section Combinators.

Definition A_or_add_bottom (S : Type) (A : @A_or S) (c : cas_constant) : @A_or (cas_constant + S) :=
let eqv := A_or_eqv _ A in
let wS  := A_eqv_witness _ eqv in
let eq  := A_eqv_eq _ eqv in
let lte := A_or_lte _ A in   
{|
  A_or_eqv             := A_eqv_add_constant S eqv c 
; A_or_lte             := brel_add_bottom lte c 
; A_or_exists_top_d    := brel_add_bottom_exists_qo_top_decide c S eq lte wS (A_or_exists_top_d _ A)
; A_or_exists_bottom_d := inl (brel_add_bottom_exists_qo_bottom c S eq lte) 
; A_or_proofs          := or_proofs_add_bottom S eq lte c wS (A_or_proofs _ A) 
; A_or_ast             := Ast_or_add_bottom (c, A_or_ast _ A) 
|}.   

End Combinators.   

End ACAS.

Section AMCAS.

Open Scope string_scope.

Definition A_mcas_or_add_bottom (S : Type) (A : @A_or_mcas S) (c : cas_constant)  : @A_or_mcas (with_constant S) :=
match A_or_mcas_cast_up A with
| A_OR_or A'      => A_or_classify (A_OR_or (A_or_add_bottom _ A' c))
| A_OR_Error sl1  => A_OR_Error sl1
| _               => A_OR_Error ("Internal Error : mcas_or_add_bottom" :: nil)
end.

End AMCAS. 


Section CAS.



Definition brel_add_bottom_reflexive_check : 
   ∀ {S : Type},  @check_reflexive S → @check_reflexive (with_constant S) 
:= λ {S} dS,  
   match dS with 
   | Certify_Reflexive       => Certify_Reflexive
   | Certify_Not_Reflexive s => Certify_Not_Reflexive (inr _ s)
   end. 


Definition brel_add_bottom_total_check : 
   ∀ {S : Type},  @certify_total S → @certify_total (with_constant S)
:= λ {S} dS,  
   match dS with 
   | Certify_Total            => Certify_Total
   | Certify_Not_Total (s, t) => Certify_Not_Total (inr s, inr t)
   end. 


Definition brel_add_bottom_exists_bottom_check : 
   ∀ {S : Type},  @certify_exists_bottom S → @certify_exists_bottom (with_constant S)
:= λ {S} dS,  
   match dS with 
   | Certify_Exists_Bottom b   => Certify_Exists_Bottom (inr b)
   | Certify_Not_Exists_Bottom => Certify_Not_Exists_Bottom
   end. 


Definition brel_add_bottom_exists_qo_bottom_check : 
   ∀ {S : Type},  @certify_exists_qo_bottom S → @certify_exists_qo_bottom (with_constant S)
:= λ {S} dS,  
   match dS with 
   | Certify_Exists_Qo_Bottom b   => Certify_Exists_Qo_Bottom (inr b)
   | Certify_Not_Exists_Qo_Bottom => Certify_Not_Exists_Qo_Bottom
   end. 


Definition brel_add_bottom_exists_qo_top_check : 
   ∀ {S : Type},  @certify_exists_qo_top S → @certify_exists_qo_top (with_constant S)
:= λ {S} dS,  
   match dS with 
   | Certify_Exists_Qo_Top b   => Certify_Exists_Qo_Top (inr b)
   | Certify_Not_Exists_Qo_Top => Certify_Not_Exists_Qo_Top
   end. 


Definition or_certs_add_bottom {S : Type} (wS : S) (c : cas_constant) 
      (orP: @or_certificates S) : @or_certificates (with_constant S) := 
{|
  or_congruence      := Assert_Brel_Congruence
; or_reflexive       := Assert_Reflexive 
; or_transitive      := Assert_Transitive 
; or_antisymmetric_d := match or_antisymmetric_d orP with
                          | Certify_Antisymmetric => Certify_Antisymmetric
                          | Certify_Not_Antisymmetric (s, t) => Certify_Not_Antisymmetric (inr s, inr t) 
                          end 
; or_total_d         :=  match or_total_d orP with
                          | Certify_Total => Certify_Total
                          | Certify_Not_Total (s, t) => Certify_Not_Total (inr s, inr t) 
                         end
; or_trivial_d       :=  Certify_Order_Not_Trivial (inr wS, inl c) 
|}. 


Definition or_add_bottom {S : Type} (orS : @or S) (c : cas_constant) : @or (with_constant S) :=
let wS := eqv_witness (or_eqv orS) in   
  {| 
     or_eqv             := eqv_add_constant (or_eqv orS) c  
   ; or_lte             := brel_add_bottom (or_lte orS) c
   ; or_exists_top_d    := brel_add_bottom_exists_qo_top_check (or_exists_top_d orS)
   ; or_exists_bottom_d := Certify_Exists_Qo_Bottom (inl c)
   ; or_certs           := or_certs_add_bottom wS c (or_certs orS) 
   ; or_ast             := Ast_or_add_bottom (c, or_ast orS)
   |}. 


 
End CAS.

Section MCAS.

Open Scope string_scope.

Definition mcas_or_add_bottom {S : Type}  (A : @or_mcas S) (c : cas_constant) : @or_mcas (with_constant S) :=
match or_mcas_cast_up A with
| OR_or A'      => or_classify (OR_or (or_add_bottom A' c))
| OR_Error sl1  => OR_Error sl1
| _             => OR_Error ("Internal Error : mcas_or_add_bottom" :: nil)
end.

End MCAS.



Section Verify.

Section Proofs.

Variables (S : Type) (eq lte : brel S) (wS : S) (b : cas_constant).   


Lemma correct_or_certs_add_bottom (P : or_proofs S eq lte) : 
       or_certs_add_bottom wS b (P2C_or eq lte P) 
       = 
       P2C_or 
          (brel_sum brel_constant eq) 
          (brel_add_bottom lte b) 
          (or_proofs_add_bottom S eq lte b wS P).
Proof. destruct P; unfold or_proofs_add_bottom, or_certs_add_bottom, P2C_or; simpl.
       destruct A_or_antisymmetric_d as [ anti | [[s1 s2] [[A B] C]]];
       destruct A_or_total_d as [ tot | [[s3 s4] [D E]]];
       destruct A_or_trivial_d as [ triv | [[s5 s6] F]]; simpl; try reflexivity. 
Defined. 

End Proofs. 

Section Combinators.
  
Theorem correct_or_add_bottom (S : Type) (b : cas_constant) (orS : @A_or S):  
         or_add_bottom (A2C_or orS) b  
         = 
         A2C_or (A_or_add_bottom S orS b). 
Proof. destruct orS; unfold or_add_bottom, A_or_add_bottom, A2C_or; simpl.
       rewrite correct_eqv_add_constant. 
       rewrite <- correct_or_certs_add_bottom.
       unfold brel_add_bottom_exists_qo_bottom.
       destruct A_or_exists_top_d as [[t [A B]] | P]; simpl; try reflexivity.        
Qed.

Theorem correct_mcas_or_add_bottom (S : Type) (orS : @A_or_mcas S) (c : cas_constant): 
         mcas_or_add_bottom (A2C_mcas_or orS) c
         = 
         A2C_mcas_or (A_mcas_or_add_bottom S orS c).
Proof. unfold mcas_or_add_bottom, A_mcas_or_add_bottom.  
       rewrite correct_or_mcas_cast_up.       
       destruct (A_or_cast_up_is_error_or_or _ orS) as [[l1 A] | [s1 A]]. 
       + rewrite A; simpl. reflexivity. 
       + rewrite A; simpl. rewrite correct_or_add_bottom. 
         apply correct_or_classify_or. 
Qed. 



End Combinators. 

End Verify.   
  
