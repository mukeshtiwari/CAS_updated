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
Require Import CAS.coq.po.classify. 





Section Compute.

Definition brel_add_top : ∀ {S : Type}, brel S → cas_constant → brel (cas_constant + S)
:= λ  {S} lte c x y, 
   match x, y with
   | (inl _), (inl _) => true (* all constants equal! *) 
   | (inl _), (inr _) => false  
   | (inr _), (inl _) => true (* new top ! *) 
   | (inr a), (inr b) => lte a b 
   end.
  

End Compute.   

Section Theory.
Variable top : cas_constant.
Variable S  : Type.  

Variable eq : brel S.
Variable refl : brel_reflexive S eq.

Variable lte : brel S.
Variable lteTran : brel_transitive S lte.
Variable lteRefl : brel_reflexive S lte. 
Variable lteCong : brel_congruence S eq lte.

Notation "a [+] b"  := (brel_add_top b a)       (at level 15).

Lemma brel_add_top_congruence : brel_congruence (with_constant S ) (brel_sum brel_constant eq) (top [+] lte). 
Proof. unfold brel_congruence. intros [s1 | t1] [s2 | t2] [s3 | t3] [s4 | t4]; compute; intros A B; auto; discriminate. Qed. 

Lemma brel_add_top_reflexive : brel_reflexive (with_constant S ) (top [+] lte). 
Proof. intros [c | s]; compute; auto. Qed. 

Lemma brel_add_top_transitive : brel_transitive (with_constant S ) (top [+] lte). 
Proof. intros [c1 | s1] [c2 | s2] [c3 | s3]; compute; intros A B; auto. 
       discriminate. exact (lteTran _ _ _ A B). 
Qed.

Lemma brel_add_top_antisymmetric (anti : brel_antisymmetric S eq lte):
     brel_antisymmetric (with_constant S ) (brel_sum brel_constant eq) (top [+] lte). 
Proof. intros [c1 | s1] [c2 | s2]; compute; intros A B; auto. Qed.

Lemma brel_add_top_not_antisymmetric (nanti : brel_not_antisymmetric S eq lte):
     brel_not_antisymmetric (with_constant S ) (brel_sum brel_constant eq) (top [+] lte). 
Proof. destruct nanti as [[s1 s2] [A B]]. exists (inr s1, inr s2); compute; auto. Defined.

Definition brel_add_top_antisymmetic_decide : 
  brel_antisymmetric_decidable S eq lte  →
     brel_antisymmetric_decidable (with_constant S) (brel_sum brel_constant eq) (top [+] lte)
:= λ dS,  
   match dS with 
   | inl anti  => inl _ (brel_add_top_antisymmetric anti)
   | inr nanti => inr _ (brel_add_top_not_antisymmetric nanti)
   end.  

(* top *) 

Lemma brel_add_top_is_top : brel_is_top (with_constant S) (top [+] lte) (inl top). 
Proof. intros [c | s]; compute; auto. Qed.

Lemma brel_add_top_exists_top : brel_exists_top (with_constant S) (top [+] lte). 
Proof. exists (inl top). apply brel_add_top_is_top. Defined.

Lemma brel_add_top_is_qo_top :
     brel_is_qo_top (with_constant S) (brel_sum brel_constant eq) (top [+] lte) (inl top). 
Proof. split. apply brel_add_top_is_top. 
       intros [c | s]; compute; auto.
Qed.      

Lemma brel_add_top_exists_qo_top : brel_exists_qo_top (with_constant S) (brel_sum brel_constant eq) (top [+] lte). 
Proof. exists (inl top). apply brel_add_top_is_qo_top. Defined. 

(* bottom *)

Lemma brel_add_top_is_bottom (b : S) (bot : brel_is_bottom S lte b) :
     brel_is_bottom (with_constant S) (top [+] lte) (inr b). 
Proof. intros [c | s]; compute; auto. Qed. 


Lemma brel_add_top_exists_bottom (bot : brel_exists_bottom S lte) :
     brel_exists_bottom (with_constant S) (top [+] lte). 
Proof. destruct bot as [b A]. exists (inr b). apply brel_add_top_is_bottom; auto. Defined. 

Lemma brel_add_top_not_exists_bottom (wS : S) (nbot : brel_not_exists_bottom S lte) :
    brel_not_exists_bottom (with_constant S) (top [+] lte). 
Proof. intros [c | s]. exists (inr wS); compute; auto. 
       destruct (nbot s) as [b A]. exists (inr b); compute; auto.
Defined.

Definition brel_add_top_exists_bottom_decide (wS : S) : 
     brel_exists_bottom_decidable S lte  → brel_exists_bottom_decidable (with_constant S) (top [+] lte)
:= λ dS,  
   match dS with 
   | inl bot  => inl _ (brel_add_top_exists_bottom bot)
   | inr nbot => inr _ (brel_add_top_not_exists_bottom wS nbot)
   end.  


Lemma brel_add_top_exists_qo_bottom (bot : brel_exists_qo_bottom S eq lte) :
     brel_exists_qo_bottom (with_constant S) (brel_sum brel_constant eq) (top [+] lte). 
Proof. destruct bot as [t [A B]]; auto.
       exists (inr t). split.
       apply brel_add_top_is_bottom; auto. 
       intros [c | s]; compute; auto.
Defined. 

Lemma brel_add_top_not_exists_qo_bottom (wS : S) (nbot : brel_not_exists_qo_bottom S eq lte) :
    brel_not_exists_qo_bottom (with_constant S) (brel_sum brel_constant eq) (top [+] lte). 
Proof. intros [c | s].  
          left. exists (inr wS); compute; auto. 
          destruct (nbot s) as [[u A] | [u [[A B] C]]].
             left. exists (inr u); compute; auto.
             right. exists (inr u); compute; auto.
Defined.

Definition brel_add_top_exists_qo_bottom_decide (wS : S) : 
  brel_exists_qo_bottom_decidable S eq lte
  → brel_exists_qo_bottom_decidable (with_constant S) (brel_sum brel_constant eq) (top [+] lte)
:= λ dS,  
   match dS with 
   | inl bot  => inl _ (brel_add_top_exists_qo_bottom bot)
   | inr nbot => inr _ (brel_add_top_not_exists_qo_bottom wS nbot)
   end.  



Lemma brel_add_top_total (tot : brel_total S lte) : brel_total (with_constant S ) (top [+] lte). 
Proof. intros [c1 | s1] [c2 | s2]; compute; auto. Qed. 

Lemma brel_add_top_not_total (ntot : brel_not_total S lte) : brel_not_total (with_constant S ) (top [+] lte). 
Proof. destruct ntot as [[s1 s2] [A B]]. exists (inr s1, inr s2). compute; auto. Defined. 


Definition brel_add_top_total_decide : 
     brel_total_decidable S lte  → brel_total_decidable (with_constant S) (top [+] lte)
:= λ dS,  
   match dS with 
   | inl tot  => inl _ (brel_add_top_total tot)
   | inr ntot => inr _ (brel_add_top_not_total ntot)
   end.

Lemma brel_add_top_not_trivial (wS : S) : order_not_trivial (with_constant S ) (top [+] lte). 
Proof. exists (inl top, inr wS). compute. reflexivity. Defined. 


End Theory.

Section ACAS.

Section Proofs.   

Variables (S : Type) (eq lte : brel S) (top : cas_constant) (wS : S).

Definition qo_proofs_add_top (orP : qo_proofs S eq lte) : 
      qo_proofs (with_constant S) (brel_sum brel_constant eq) (brel_add_top lte top) := 
{|
  A_qo_congruence      := brel_add_top_congruence top S eq lte (A_qo_congruence _ _ _ orP)  
; A_qo_reflexive       := brel_add_top_reflexive top S lte (A_qo_reflexive _ _ _ orP)
; A_qo_transitive      := brel_add_top_transitive top S lte (A_qo_transitive _ _ _ orP)                                                    
; A_qo_antisymmetric_d := brel_add_top_antisymmetic_decide top S eq lte (A_qo_antisymmetric_d _ _ _ orP) 
; A_qo_total_d         := brel_add_top_total_decide top S lte (A_qo_total_d _ _ _ orP) 
; A_qo_trivial_d       := inr (brel_add_top_not_trivial top S lte wS) 
|}. 

End Proofs.

Section Combinators.

Definition A_qo_add_top {S : Type} (c : cas_constant) (A : @A_qo S) : @A_qo (cas_constant + S) :=
let eqv := A_qo_eqv _ A in
let wS  := A_eqv_witness _ eqv in
let eq  := A_eqv_eq _ eqv in
let lte := A_qo_lte _ A in   
{|
  A_qo_eqv             := A_eqv_add_constant S eqv c 
; A_qo_lte             := brel_add_top lte c 
; A_qo_exists_top_d    := inl (brel_add_top_exists_qo_top c S eq lte) 
; A_qo_exists_bottom_d := brel_add_top_exists_qo_bottom_decide c S eq lte wS (A_qo_exists_bottom_d _ A)
; A_qo_proofs          := qo_proofs_add_top S eq lte c wS (A_qo_proofs _ A) 
; A_qo_ast             := Ast_or_add_top (c, A_qo_ast _ A) 
|}.   

End Combinators.   

End ACAS.

Section AMCAS.

Definition A_qo_add_top_below_qo {S : Type}
    (c : cas_constant)
    (A : @A_below_qo S) : @A_below_qo (with_constant S) :=
  A_classify_qo (A_qo_add_top c (A_cast_up_qo A)). 

Definition A_mcas_qo_add_top {S : Type}
  (c : cas_constant)
  (A : @A_qo_mcas S) : @A_qo_mcas (with_constant S) :=
    match A with
    | A_MCAS_qo B        => A_MCAS_qo (A_qo_add_top_below_qo c B)  
    | A_MCAS_qo_Error sl => A_MCAS_qo_Error sl
    end.

End AMCAS. 


Section CAS.



Definition brel_add_top_reflexive_check {S : Type}
   (dS : @check_reflexive S) : @check_reflexive (with_constant S) := 
   match dS with 
   | Certify_Reflexive       => Certify_Reflexive
   | Certify_Not_Reflexive s => Certify_Not_Reflexive (inr _ s)
   end. 

Definition brel_add_top_total_check {S : Type}
  (dS : @certify_total S) : @certify_total (with_constant S) := 
   match dS with 
   | Certify_Total            => Certify_Total
   | Certify_Not_Total (s, t) => Certify_Not_Total (inr s, inr t)
   end. 


Definition brel_add_top_exists_bottom_check {S : Type}
  (dS : @certify_exists_bottom S) : @certify_exists_bottom (with_constant S) := 
   match dS with 
   | Certify_Exists_Bottom b   => Certify_Exists_Bottom (inr b)
   | Certify_Not_Exists_Bottom => Certify_Not_Exists_Bottom
   end. 


Definition brel_add_top_exists_qo_bottom_check {S : Type}
  (dS : @certify_exists_qo_bottom S) : @certify_exists_qo_bottom (with_constant S) := 
   match dS with 
   | Certify_Exists_Qo_Bottom b   => Certify_Exists_Qo_Bottom (inr b)
   | Certify_Not_Exists_Qo_Bottom => Certify_Not_Exists_Qo_Bottom
   end. 


Definition qo_certs_add_top {S : Type} (wS : S) (c : cas_constant) 
      (orP: @qo_certificates S) : @qo_certificates (with_constant S) := 
{|
  qo_congruence      := Assert_Brel_Congruence
; qo_reflexive       := Assert_Reflexive 
; qo_transitive      := Assert_Transitive 
; qo_antisymmetric_d := match qo_antisymmetric_d orP with
                          | Certify_Antisymmetric => Certify_Antisymmetric
                          | Certify_Not_Antisymmetric (s, t) => Certify_Not_Antisymmetric (inr s, inr t) 
                          end 
; qo_total_d         :=  match qo_total_d orP with
                          | Certify_Total => Certify_Total
                          | Certify_Not_Total (s, t) => Certify_Not_Total (inr s, inr t) 
                         end
; qo_trivial_d       :=  Certify_Order_Not_Trivial (inl c, inr wS) 
|}. 


Definition qo_add_top {S : Type} (c : cas_constant)  (qoS : @qo S) : @qo (with_constant S) :=
let wS := eqv_witness (qo_eqv qoS) in   
  {| 
     qo_eqv             := eqv_add_constant (qo_eqv qoS) c  
   ; qo_lte             := brel_add_top (qo_lte qoS) c
   ; qo_exists_top_d    := Certify_Exists_Qo_Top (inl c)
   ; qo_exists_bottom_d := brel_add_top_exists_qo_bottom_check (qo_exists_bottom_d qoS)
   ; qo_certs           := qo_certs_add_top wS c (qo_certs qoS) 
   ; qo_ast             := Ast_or_add_top (c, qo_ast qoS)
   |}. 


 
End CAS.

Section MCAS.

Definition qo_add_top_below_qo {S : Type}
    (c : cas_constant)
    (A : @below_qo S) : @below_qo (with_constant S) :=
  classify_qo (qo_add_top c (cast_up_qo A)). 

Definition mcas_qo_add_top {S : Type}
  (c : cas_constant)
  (A : @qo_mcas S) : @qo_mcas (with_constant S) :=
    match A with
    | MCAS_qo B        => MCAS_qo (qo_add_top_below_qo c B)  
    | MCAS_qo_Error sl => MCAS_qo_Error sl
    end.

End MCAS.



Section Verify.

Section Proofs.

Variables (S : Type) (eq lte : brel S) (wS : S) (b : cas_constant).   


Lemma correct_qo_certs_add_top (P : qo_proofs S eq lte) : 
       qo_certs_add_top wS b (P2C_qo eq lte P) 
       = 
       P2C_qo 
          (brel_sum brel_constant eq) 
          (brel_add_top lte b) 
          (qo_proofs_add_top S eq lte b wS P).
Proof. destruct P; unfold qo_proofs_add_top, qo_certs_add_top, P2C_qo; simpl.
       destruct A_qo_antisymmetric_d as [ anti | [[s1 s2] [[A B] C]]];
       destruct A_qo_total_d as [ tot | [[s3 s4] [D E]]];
       destruct A_qo_trivial_d as [ triv | [[s5 s6] F]]; simpl; try reflexivity. 
Defined. 

End Proofs. 

Section Combinators.
  
Theorem correct_qo_add_top (S : Type) (c : cas_constant) (orS : @A_qo S):  
         qo_add_top c (A2C_qo orS)  
         = 
         A2C_qo (A_qo_add_top c orS). 
Proof. destruct orS; unfold qo_add_top, A_qo_add_top, A2C_qo; simpl.
       rewrite correct_eqv_add_constant. 
       rewrite <- correct_qo_certs_add_top.
       unfold brel_add_top_exists_qo_top.
       destruct A_qo_exists_bottom_d as [[t [A B]] | P]; simpl; try reflexivity.        
Qed.

Theorem correct_qo_add_top_below_qo (S : Type)
  (c : cas_constant) (A :  @A_below_qo S) : 
  qo_add_top_below_qo c (A2C_below_qo A)
  =
  A2C_below_qo (A_qo_add_top_below_qo c A).
Proof. unfold A_qo_add_top_below_qo, qo_add_top_below_qo.
       rewrite cast_up_qo_A2C_commute.
       rewrite correct_qo_add_top. 
       rewrite correct_classify_qo. 
       reflexivity. 
Qed.

Theorem correct_mcas_qo_add_top (S : Type) (c : cas_constant) (qoS : @A_qo_mcas S) : 
         mcas_qo_add_top c (A2C_qo_mcas qoS) 
         = 
         A2C_qo_mcas (A_mcas_qo_add_top c qoS).
Proof. unfold mcas_qo_add_top, A_mcas_qo_add_top.  
       destruct qoS; simpl; try reflexivity.        
       rewrite correct_qo_add_top_below_qo. reflexivity. 
Qed. 

End Combinators. 

End Verify.   
  
