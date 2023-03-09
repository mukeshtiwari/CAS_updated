Require Import Coq.Strings.String.
Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.

Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.

Require Import CAS.coq.po.properties.
Require Import CAS.coq.po.theory. 
Require Import CAS.coq.po.structures.

(* 

implementation hierarchy for orders 

           qo 
         / | \
        /  |  \ 
       /   |   \ 
      /    |    \ 
     /     |     \
     p   qo_wb   fo  
     |  /     \  |
     | /       \ |
    po_wb      fo_wb

wb = with_bottom 

qo = quasi order (ref, trans) 
po = partial order (ref, trans, antisymm, not total)   
fo = preference order quasi order (ref, trans, total) 
wb = with_bottom (currently needed for minset_union ) 

K is a class. 

    cast_up_K : below_K -> K 

K1, K2 classes, with K2 below K1 in the hierarchy. 

    cast_K1_down_to_K2 : below_K1 -> option below_K2
*) 

Section ACAS.
 

Section Proofs.

Variables (S : Type)
          (eq lte : brel S)
          (wS : S)
          (f : S -> S) 
          (nt : brel_not_trivial S eq f). 


Definition qo_proofs_from_po_proofs (d : po_proofs S eq lte) :=
let anti := (A_po_antisymmetric _ _ _ d ) in   
{|  
  A_qo_congruence      := A_po_congruence _ _ _ d 
; A_qo_reflexive       := A_po_reflexive _ _ _ d 
; A_qo_transitive      := A_po_transitive _ _ _ d 
; A_qo_antisymmetric_d := inl anti 
; A_qo_total_d         := inr (A_po_not_total _ _ _ d) 
; A_qo_trivial_d       := inr (antisymmetric_implies_order_not_trivial S eq lte wS f nt anti)                              
|}.


Definition qo_proofs_from_fo_proofs (d : fo_proofs S eq lte) :=
{|  
  A_qo_congruence      := A_fo_congruence _ _ _ d 
; A_qo_reflexive       := A_fo_reflexive _ _ _ d 
; A_qo_transitive      := A_fo_transitive _ _ _ d 
; A_qo_antisymmetric_d := A_fo_antisymmetric_d _ _ _ d 
; A_qo_total_d         := inl (A_fo_total _ _ _ d) 
; A_qo_trivial_d       := A_fo_trivial_d _ _ _ d 
|}.

End Proofs.
  
Section Combinators.


Definition A_qo_from_po {S : Type} (A : A_po S) :=
let eqv := A_po_eqv _ A in 
let wS  := A_eqv_witness _ eqv in
let f   := A_eqv_new _ eqv in
let nt  := A_eqv_not_trivial _ eqv  in
let P := A_po_proofs _ A in
let anti := A_po_antisymmetric _ _ _ P in 
{|    
  A_qo_eqv             := eqv 
; A_qo_lte             := A_po_lte _ A 
; A_qo_exists_top_d    := brel_exists_qo_top_decidable_from_brel_exists_top_decidable _ _ _ anti (A_po_exists_top_d _ A)
; A_qo_exists_bottom_d := brel_exists_qo_bottom_decidable_from_brel_exists_bottom_decidable _ _ _ anti (A_po_exists_bottom_d _ A)
; A_qo_proofs          := qo_proofs_from_po_proofs _ _ _ wS f nt P
; A_qo_ast             := A_po_ast _ A 
|}.


Definition A_qo_from_fo {S : Type} (A : A_fo S) :=
{|    
  A_qo_eqv             := A_fo_eqv _ A 
; A_qo_lte             := A_fo_lte _ A 
; A_qo_exists_top_d    := A_fo_exists_top_d _ A
; A_qo_exists_bottom_d := A_fo_exists_bottom_d _ A
; A_qo_proofs          := qo_proofs_from_fo_proofs _ _ _ (A_fo_proofs _ A)
; A_qo_ast             := A_fo_ast _ A 
|}.

Definition A_po_from_po_with_bottom {S : Type} (A : A_po_with_bottom S) :=
{|    
  A_po_eqv             := A_po_with_bottom_eqv _ A 
; A_po_lte             := A_po_with_bottom_lte _ A 
; A_po_exists_top_d    := A_po_with_bottom_exists_top_d _ A
; A_po_exists_bottom_d := inl (A_po_with_bottom_exists_bottom _ A)
; A_po_proofs          := A_po_with_bottom_proofs _ A 
; A_po_ast             := A_po_with_bottom_ast _ A 
|}.

Definition A_qo_from_qo_with_bottom {S : Type} (A : A_qo_with_bottom S) :=
{|    
  A_qo_eqv             := A_qo_with_bottom_eqv _ A 
; A_qo_lte             := A_qo_with_bottom_lte _ A 
; A_qo_exists_top_d    := A_qo_with_bottom_exists_top_d _ A
; A_qo_exists_bottom_d := inl (A_qo_with_bottom_exists_bottom _ A)
; A_qo_proofs          := A_qo_with_bottom_proofs _ A 
; A_qo_ast             := A_qo_with_bottom_ast _ A 
|}.



Definition A_fo_from_fo_with_bottom {S : Type} (A : A_fo_with_bottom S) :=
{|    
  A_fo_eqv             := A_fo_with_bottom_eqv _ A 
; A_fo_lte             := A_fo_with_bottom_lte _ A 
; A_fo_exists_top_d    := A_fo_with_bottom_exists_top_d _ A
; A_fo_exists_bottom_d := inl (A_fo_with_bottom_exists_bottom _ A)
; A_fo_proofs          := A_fo_with_bottom_proofs _ A 
; A_fo_ast             := A_fo_with_bottom_ast _ A 
|}.

Definition A_qo_with_bottom_from_fo_with_bottom {S : Type} (A : A_fo_with_bottom S) :=
{|    
  A_qo_with_bottom_eqv             := A_fo_with_bottom_eqv _ A 
; A_qo_with_bottom_lte             := A_fo_with_bottom_lte _ A 
; A_qo_with_bottom_exists_top_d    := A_fo_with_bottom_exists_top_d _ A
; A_qo_with_bottom_exists_bottom   := A_fo_with_bottom_exists_bottom _ A
; A_qo_with_bottom_proofs          := qo_proofs_from_fo_proofs _ _ _ (A_fo_with_bottom_proofs _ A) 
; A_qo_with_bottom_ast             := A_fo_with_bottom_ast _ A 
|}.


Definition A_qo_with_bottom_from_po_with_bottom {S : Type} (A : A_po_with_bottom S) :=
let eqv := A_po_with_bottom_eqv _ A in 
let wS  := A_eqv_witness _ eqv in
let f   := A_eqv_new _ eqv in
let nt  := A_eqv_not_trivial _ eqv  in
let P := A_po_with_bottom_proofs _ A in
let anti := A_po_antisymmetric _ _ _ P in 
{|    
  A_qo_with_bottom_eqv             := eqv
; A_qo_with_bottom_lte             := A_po_with_bottom_lte _ A 
; A_qo_with_bottom_exists_top_d    := brel_exists_qo_top_decidable_from_brel_exists_top_decidable _ _ _ anti (A_po_with_bottom_exists_top_d _ A)
; A_qo_with_bottom_exists_bottom   := brel_exists_qo_bottom_from_brel_exists_bottom _ _ _ anti (A_po_with_bottom_exists_bottom _ A)
; A_qo_with_bottom_proofs          := qo_proofs_from_po_proofs  _ _ _ wS f nt P 
; A_qo_with_bottom_ast             := A_po_with_bottom_ast _ A 
|}.


End Combinators. 

End ACAS.


Section AMCAS.

Definition A_cast_up_po_with_bottom {S : Type} (A : @A_below_po_with_bottom S) : A_po_with_bottom S :=
    match A with 
    | A_Below_po_with_bottom_top B => B 
    end.

Definition A_cast_up_fo_with_bottom {S : Type} (A : @A_below_fo_with_bottom S) : A_fo_with_bottom S :=
    match A with 
    | A_Below_fo_with_bottom_top B => B 
    end.

Definition A_cast_up_po {S : Type} (A : @A_below_po S) : A_po S :=
    match A with 
    | A_Below_po_top B            => B 
    | A_Below_po_po_with_bottom B =>
        A_po_from_po_with_bottom (A_cast_up_po_with_bottom B)
    end.

Definition A_cast_up_fo {S : Type} (A : @A_below_fo S) : A_fo S :=
    match A with 
    | A_Below_fo_top B            => B 
    | A_Below_fo_fo_with_bottom B =>
        A_fo_from_fo_with_bottom (A_cast_up_fo_with_bottom B)
    end.

Definition A_cast_up_qo_with_bottom {S : Type} (A : @A_below_qo_with_bottom S) : A_qo_with_bottom S :=
    match A with 
    | A_Below_qo_with_bottom_top B            => B
    | A_Below_qo_with_bottom_fo_with_bottom B => A_qo_with_bottom_from_fo_with_bottom (A_cast_up_fo_with_bottom B)
    | A_Below_qo_with_bottom_po_with_bottom B => A_qo_with_bottom_from_po_with_bottom (A_cast_up_po_with_bottom B)
    end.


Definition A_cast_up_qo {S : Type} (A : @A_below_qo S) : A_qo S :=
    match A with 
    | A_Below_qo_top B            => B 
    | A_Below_qo_po B             => A_qo_from_po (A_cast_up_po B)
    | A_Below_qo_fo B             => A_qo_from_fo (A_cast_up_fo B)
    | A_Below_qo_qo_with_bottom B => A_qo_from_qo_with_bottom (A_cast_up_qo_with_bottom B)
    end.

    (* NB: each of the following cast (down) functions assumes 
       that its argument has been classified already.
       These functions can "fail" by returning None. 
    *)  
  Definition A_cast_po_down_to_po_with_bottom {S : Type}
    (A : @A_below_po S) : option (@A_below_po_with_bottom S) :=
    match A with
    | A_Below_po_top _            => None
    | A_Below_po_po_with_bottom B => Some B 
    end. 

  Definition A_cast_fo_down_to_fo_with_bottom {S : Type}
    (A : @A_below_fo S) : option (@A_below_fo_with_bottom S) :=
    match A with
    | A_Below_fo_top _            => None
    | A_Below_fo_fo_with_bottom B => Some B 
    end. 
  
  Definition A_cast_qo_down_to_po {S : Type}
    (A : @A_below_qo S) : option (@A_below_po S) :=
    match A with
    | A_Below_qo_top _            => None
    | A_Below_qo_po B             => Some B
    | A_Below_qo_fo B             => None
    | A_Below_qo_qo_with_bottom B => None 
    end.

  Definition A_cast_qo_down_to_fo {S : Type}
    (A : @A_below_qo S) : option (@A_below_fo S) :=
    match A with
    | A_Below_qo_top _  => None
    | A_Below_qo_po _ => None 
    | A_Below_qo_fo B => Some B
    | A_Below_qo_qo_with_bottom B => None 
    end.

    Definition A_cast_qo_down_to_qo_with_bottom {S : Type}
    (A : @A_below_qo S) : option (@A_below_qo_with_bottom S) :=
    match A with
    | A_Below_qo_top _  => None
    | A_Below_qo_po _ => None 
    | A_Below_qo_fo B => None 
    | A_Below_qo_qo_with_bottom B => Some B
    end.

  Definition A_cast_qo_down_to_po_with_bottom {S : Type}
    (A : @A_below_qo S) : option (@A_below_po_with_bottom S) :=
    match A_cast_qo_down_to_po A with
    | Some B => A_cast_po_down_to_po_with_bottom B       
    | _      => None
    end. 

  Definition A_cast_qo_down_to_fo_with_bottom {S : Type}
    (A : @A_below_qo S) : option (@A_below_fo_with_bottom S) :=
    match A_cast_qo_down_to_fo A with
    | Some B => A_cast_fo_down_to_fo_with_bottom B       
    | _      => None
    end. 

  
End AMCAS.

Section CAS.

  Section Certificates.


Definition qo_certs_from_po_certs {S : Type} (wS : S) (f : S -> S) (lte : brel S) (d : @po_certificates S) :=
{|  
  qo_congruence      := po_congruence d 
; qo_reflexive       := po_reflexive d 
; qo_transitive      := po_transitive d 
; qo_antisymmetric_d := match po_antisymmetric d with
                        | Assert_Antisymmetric => Certify_Antisymmetric
                        end 
; qo_total_d         := match po_not_total d with
                        | Assert_Not_Total p => Certify_Not_Total p 
                        end 
; qo_trivial_d       := Certify_Order_Not_Trivial (witness_antisymmetric_implies_order_not_trivial _ lte wS f)                          
|}.

Definition qo_certs_from_fo_certs {S : Type} (d : @fo_certificates S) :=
{|  
  qo_congruence      := fo_congruence d 
; qo_reflexive       := fo_reflexive d 
; qo_transitive      := fo_transitive d 
; qo_antisymmetric_d := fo_antisymmetric_d d 
; qo_total_d         := match fo_total d with
                        | Assert_Total => Certify_Total
                        end 
; qo_trivial_d       := fo_trivial_d d
|}.

End Certificates. 

Section Combinators.

Definition qo_from_po {S : Type} (A : @po S) :=
let lte  := po_lte A in
let eqv  := po_eqv A in      
let wS  := eqv_witness eqv in
let f   := eqv_new eqv in
{|    
  qo_eqv             := po_eqv A 
; qo_lte             := po_lte A 
; qo_exists_top_d    := match po_exists_top_d A with
                        | Certify_Exists_Top t => Certify_Exists_Qo_Top t
                        | Certify_Not_Exists_Top => Certify_Not_Exists_Qo_Top
                        end 
; qo_exists_bottom_d := match po_exists_bottom_d A with
                        | Certify_Exists_Bottom t => Certify_Exists_Qo_Bottom t
                        | Certify_Not_Exists_Bottom => Certify_Not_Exists_Qo_Bottom
                        end 
; qo_certs           := qo_certs_from_po_certs wS f lte (po_certs A) 
; qo_ast             := po_ast A 
|}.


Definition qo_from_fo {S : Type} (A : @fo S) :=
{|    
  qo_eqv             := fo_eqv A 
; qo_lte             := fo_lte A 
; qo_exists_top_d    := fo_exists_top_d A 
; qo_exists_bottom_d := fo_exists_bottom_d A 
; qo_certs           := qo_certs_from_fo_certs (fo_certs A) 
; qo_ast             := fo_ast A 
|}.

Definition po_from_po_with_bottom {S : Type} (A : @po_with_bottom S) :=
{|    
  po_eqv             := po_with_bottom_eqv A 
; po_lte             := po_with_bottom_lte A 
; po_exists_top_d    := po_with_bottom_exists_top_d A 
; po_exists_bottom_d := match po_with_bottom_exists_bottom A with
                        | Assert_Exists_Bottom bot =>
                            Certify_Exists_Bottom bot
                        end 
; po_certs           := po_with_bottom_certs A
; po_ast             := po_with_bottom_ast A 
|}.

Definition fo_from_fo_with_bottom {S : Type} (A : @fo_with_bottom S) :=
{|    
  fo_eqv             := fo_with_bottom_eqv A 
; fo_lte             := fo_with_bottom_lte A 
; fo_exists_top_d    := fo_with_bottom_exists_top_d A 
; fo_exists_bottom_d := match fo_with_bottom_exists_bottom A with
                        | Assert_Exists_Qo_Bottom bot =>
                            Certify_Exists_Qo_Bottom bot
                        end 
; fo_certs           := fo_with_bottom_certs A
; fo_ast             := fo_with_bottom_ast A 
|}.



Definition qo_with_bottom_from_fo_with_bottom {S : Type} (A : @fo_with_bottom S) :=
{|    
  qo_with_bottom_eqv             := fo_with_bottom_eqv A 
; qo_with_bottom_lte             := fo_with_bottom_lte A 
; qo_with_bottom_exists_top_d    := fo_with_bottom_exists_top_d A
; qo_with_bottom_exists_bottom   := fo_with_bottom_exists_bottom A
; qo_with_bottom_certs           := qo_certs_from_fo_certs (fo_with_bottom_certs A) 
; qo_with_bottom_ast             := fo_with_bottom_ast A 
|}.


Definition qo_with_bottom_from_po_with_bottom {S : Type} (A : @po_with_bottom S) :=
let eqv := po_with_bottom_eqv A in 
let wS  := eqv_witness eqv in
let lte := po_with_bottom_lte A in 
let f   := eqv_new eqv in
let P   := po_with_bottom_certs A in
{|    
  qo_with_bottom_eqv             := eqv
; qo_with_bottom_lte             := po_with_bottom_lte A 
; qo_with_bottom_exists_top_d    := match po_with_bottom_exists_top_d A with
                                    | Certify_Exists_Top top =>
                                        Certify_Exists_Qo_Top top
                                    | Certify_Not_Exists_Top =>
                                        Certify_Not_Exists_Qo_Top
                                    end 
; qo_with_bottom_exists_bottom   := match po_with_bottom_exists_bottom A with
                                    | Assert_Exists_Bottom bot =>
                                        Assert_Exists_Qo_Bottom bot
                                    end 
; qo_with_bottom_certs           := qo_certs_from_po_certs wS f lte P 
; qo_with_bottom_ast             := po_with_bottom_ast A 
|}.

Definition qo_from_qo_with_bottom {S : Type} (A : @qo_with_bottom S) :=
{|    
  qo_eqv             := qo_with_bottom_eqv A 
; qo_lte             := qo_with_bottom_lte A 
; qo_exists_top_d    := qo_with_bottom_exists_top_d A 
; qo_exists_bottom_d := match qo_with_bottom_exists_bottom A with
                        | Assert_Exists_Qo_Bottom bot =>
                            Certify_Exists_Qo_Bottom bot
                        end 
; qo_certs           := qo_with_bottom_certs A
; qo_ast             := qo_with_bottom_ast A 
|}.


End Combinators. 
End CAS.

Section MCAS.


Definition cast_up_po_with_bottom {S : Type} (A : @below_po_with_bottom S) : @po_with_bottom S :=
    match A with 
    | Below_po_with_bottom_top B => B 
    end.

Definition cast_up_fo_with_bottom {S : Type} (A : @below_fo_with_bottom S) : @fo_with_bottom S :=
    match A with 
    | Below_fo_with_bottom_top B => B 
    end.


Definition cast_up_po {S : Type} (A : @below_po S) : @po S :=
    match A with 
    | Below_po_top B            => B 
    | Below_po_po_with_bottom B =>
        po_from_po_with_bottom (cast_up_po_with_bottom B)
    end.

Definition cast_up_fo {S : Type} (A : @below_fo S) : @fo S :=
    match A with 
    | Below_fo_top B            => B 
    | Below_fo_fo_with_bottom B =>
        fo_from_fo_with_bottom (cast_up_fo_with_bottom B)
    end.

Definition cast_up_qo_with_bottom {S : Type} (A : @below_qo_with_bottom S) : @qo_with_bottom S :=
    match A with 
    | Below_qo_with_bottom_top B            => B
    | Below_qo_with_bottom_fo_with_bottom B => qo_with_bottom_from_fo_with_bottom (cast_up_fo_with_bottom B)
    | Below_qo_with_bottom_po_with_bottom B => qo_with_bottom_from_po_with_bottom (cast_up_po_with_bottom B)
    end.


Definition cast_up_qo {S : Type} (A : @below_qo S) : @qo S :=
    match A with 
    | Below_qo_top B            => B 
    | Below_qo_po B             => qo_from_po (cast_up_po B)
    | Below_qo_fo B             => qo_from_fo (cast_up_fo B)
    | Below_qo_qo_with_bottom B => qo_from_qo_with_bottom (cast_up_qo_with_bottom B)
    end.

    (* NB: each of the following cast (down) functions assumes 
       that its argument has been classified already.
       These functions can "fail" by returning None. 
    *)  
  Definition cast_po_down_to_po_with_bottom {S : Type}
    (A : @below_po S) : option (@below_po_with_bottom S) :=
    match A with
    | Below_po_top _            => None
    | Below_po_po_with_bottom B => Some B 
    end.
  
  Definition cast_fo_down_to_fo_with_bottom {S : Type}
    (A : @below_fo S) : option (@below_fo_with_bottom S) :=
    match A with
    | Below_fo_top _            => None
    | Below_fo_fo_with_bottom B => Some B 
    end. 

  
  Definition cast_qo_down_to_po {S : Type}
    (A : @below_qo S) : option (@below_po S) :=
    match A with
    | Below_qo_top _  => None
    | Below_qo_po B => Some B 
    | Below_qo_fo _ => None
    | Below_qo_qo_with_bottom _ => None
    end.

  Definition cast_qo_down_to_fo {S : Type}
    (A : @below_qo S) : option (@below_fo S) :=
    match A with
    | Below_qo_top _  => None
    | Below_qo_po _ => None 
    | Below_qo_fo B => Some B
    | Below_qo_qo_with_bottom _ => None
    end.

  Definition cast_qo_down_to_po_with_bottom {S : Type}
    (A : @below_qo S) : option (@below_po_with_bottom S) :=
    match cast_qo_down_to_po A with
    | Some B => cast_po_down_to_po_with_bottom B       
    | _      => None
    end. 

  Definition cast_qo_down_to_fo_with_bottom {S : Type}
    (A : @below_qo S) : option (@below_fo_with_bottom S) :=
    match cast_qo_down_to_fo A with
    | Some B => cast_fo_down_to_fo_with_bottom B       
    | _      => None
    end. 

    Definition cast_qo_down_to_qo_with_bottom {S : Type}
    (A : @below_qo S) : option (@below_qo_with_bottom S) :=
    match A with
    | Below_qo_top _  => None
    | Below_qo_po _ => None 
    | Below_qo_fo B => None 
    | Below_qo_qo_with_bottom B => Some B
    end.

End MCAS.


Section Verify.

Section Certificates.

Variables (S : Type) (eq lte : brel S) (wS : S) (f : S -> S) (nt : brel_not_trivial S eq f).       

Lemma correct_qo_certs_from_po_certs (P : po_proofs S eq lte) :
 P2C_qo eq lte (qo_proofs_from_po_proofs S eq lte wS f nt P)
 =
 qo_certs_from_po_certs wS f lte (P2C_po eq lte P).
Proof. destruct P. 
       unfold qo_proofs_from_po_proofs, qo_certs_from_po_certs,
       P2C_qo, P2C_po; simpl.
       reflexivity. 
Qed.

Lemma correct_qo_certs_from_fo_certs (P : fo_proofs S eq lte) :
 P2C_qo eq lte (qo_proofs_from_fo_proofs S eq lte P)
 =
 qo_certs_from_fo_certs (P2C_fo eq lte P).
Proof. destruct P. 
       unfold qo_proofs_from_fo_proofs, qo_certs_from_fo_certs,
       P2C_qo, P2C_fo; simpl.
       reflexivity. 
Qed.

End Certificates.

Section Combinators.

Variable (S : Type).   

Lemma correct_qo_from_po (a : A_po S) : 
  qo_from_po (A2C_po a) = A2C_qo (A_qo_from_po a).
Proof. destruct a; unfold qo_from_po, A_qo_from_po, A2C_qo, A2C_po; simpl.
       rewrite correct_qo_certs_from_po_certs.
       destruct A_po_exists_top_d as [[t A] | ntop];
       destruct A_po_exists_bottom_d as [[b C] | nbot]; simpl;          
       reflexivity. 
Qed.

Lemma correct_qo_from_fo (a : A_fo S) : 
  qo_from_fo (A2C_fo a) = A2C_qo (A_qo_from_fo a).
Proof. destruct a; unfold qo_from_fo, A_qo_from_fo, A2C_qo, A2C_fo; simpl.
       rewrite correct_qo_certs_from_fo_certs.
       reflexivity. 
Qed.

Lemma correct_po_from_po_with_bottom (a : A_po_with_bottom S) : 
  po_from_po_with_bottom (A2C_po_with_bottom a)
  =
 A2C_po (A_po_from_po_with_bottom a).
Proof. destruct a; unfold po_from_po_with_bottom,
           A_po_from_po_with_bottom, A2C_po, A2C_po_with_bottom; simpl.
       destruct A_po_with_bottom_exists_top_d as [[t A] | ntop];
       reflexivity. 
Qed.

Lemma correct_qo_from_qo_with_bottom (a : A_qo_with_bottom S) : 
  qo_from_qo_with_bottom (A2C_qo_with_bottom a)
  =
  A2C_qo (A_qo_from_qo_with_bottom a).
Proof. destruct a; unfold qo_from_qo_with_bottom,
           A_qo_from_qo_with_bottom, A2C_qo, A2C_qo_with_bottom; simpl; 
       try reflexivity. 
Qed.

Lemma correct_fo_from_fo_with_bottom (a : A_fo_with_bottom S) : 
  fo_from_fo_with_bottom (A2C_fo_with_bottom a) = A2C_fo (A_fo_from_fo_with_bottom a).
Proof. destruct a; unfold fo_from_fo_with_bottom,
           A_fo_from_fo_with_bottom, A2C_fo, A2C_fo_with_bottom; simpl.
       destruct A_fo_with_bottom_exists_top_d as [[t A] | ntop];
       reflexivity. 
Qed.


Lemma correct_qo_with_bottom_from_po_with_bottom (a : A_po_with_bottom S) : 
  qo_with_bottom_from_po_with_bottom (A2C_po_with_bottom a)
  =
 A2C_qo_with_bottom (A_qo_with_bottom_from_po_with_bottom a).
Proof. destruct a; unfold qo_with_bottom_from_po_with_bottom,
           A_qo_with_bottom_from_po_with_bottom, A2C_qo_with_bottom; 
         destruct A_po_with_bottom_exists_top_d as [[t A] | ntop];
         destruct A_po_with_bottom_exists_bottom as [b B]; simpl;
       try reflexivity. 
Qed. 


Lemma correct_qo_with_bottom_from_fo_with_bottom (a : A_fo_with_bottom S) : 
  qo_with_bottom_from_fo_with_bottom (A2C_fo_with_bottom a)
  =
 A2C_qo_with_bottom (A_qo_with_bottom_from_fo_with_bottom a).
Proof. destruct a; unfold qo_with_bottom_from_fo_with_bottom,
           A_qo_with_bottom_from_fo_with_bottom, A2C_fo_with_bottom; 
       try reflexivity. 
Qed. 

       
End Combinators.

Section MCAS.

  Variable (S : Type).

  Theorem correct_cast_up_po_with_bottom (a : @A_below_po_with_bottom S) : 
  cast_up_po_with_bottom (A2C_below_po_with_bottom a)
  =
  A2C_po_with_bottom (A_cast_up_po_with_bottom a).
  Proof. destruct a. destruct a.
         unfold cast_up_po_with_bottom, A_cast_up_po_with_bottom,
         A2C_below_po_with_bottom, A2C_po_with_bottom. simpl. 
         reflexivity. 
  Qed.

  Theorem correct_cast_up_fo_with_bottom (a : @A_below_fo_with_bottom S) : 
  cast_up_fo_with_bottom (A2C_below_fo_with_bottom a)
  =
  A2C_fo_with_bottom (A_cast_up_fo_with_bottom a).
  Proof. destruct a. destruct a.
         unfold cast_up_fo_with_bottom, A_cast_up_fo_with_bottom,
         A2C_below_fo_with_bottom, A2C_fo_with_bottom. simpl. 
         reflexivity. 
  Qed.

  Theorem correct_cast_up_po (a : @A_below_po S) : 
  cast_up_po (A2C_below_po a)
  =
  A2C_po (A_cast_up_po a).
  Proof. unfold A2C_below_po, A_cast_up_po, cast_up_po, A2C_po; simpl.
         destruct a.
         - reflexivity. 
         - rewrite correct_cast_up_po_with_bottom.
           destruct a. destruct a. simpl.
           unfold A2C_po_with_bottom, po_from_po_with_bottom;
             reflexivity. 
  Qed.
  
  Theorem correct_cast_up_fo (a : @A_below_fo S) : 
  cast_up_fo (A2C_below_fo a)
  =
  A2C_fo (A_cast_up_fo a).
  Proof. unfold A2C_below_fo, A_cast_up_fo, cast_up_fo, A2C_fo; simpl.
         destruct a.
         - reflexivity. 
         - rewrite correct_cast_up_fo_with_bottom.
           destruct a. destruct a. simpl.
           unfold A2C_fo_with_bottom, fo_from_fo_with_bottom;
             reflexivity. 
  Qed.

  Theorem correct_cast_up_qo_with_bottom (a : @A_below_qo_with_bottom S) : 
  cast_up_qo_with_bottom (A2C_below_qo_with_bottom a)
  =
  A2C_qo_with_bottom (A_cast_up_qo_with_bottom a).
  Proof. destruct a; destruct a; 
         unfold cast_up_qo_with_bottom, A_cast_up_qo_with_bottom; 
           simpl; try reflexivity.
         rewrite correct_qo_with_bottom_from_po_with_bottom.
         reflexivity. 
  Qed.

  Theorem correct_cast_up_qo (R : @A_below_qo S) :
    cast_up_qo (A2C_below_qo R)
    = 
    A2C_qo (A_cast_up_qo R). 
  Proof. destruct R; simpl. 
         - reflexivity. 
         - rewrite <- correct_qo_from_po. 
           rewrite correct_cast_up_po. reflexivity.
         - rewrite <- correct_qo_from_fo. 
           rewrite correct_cast_up_fo. reflexivity.
         - rewrite correct_cast_up_qo_with_bottom. reflexivity. 
  Qed.

Lemma correct_cast_po_down_to_po_with_bottom (A : @A_below_po S) : 
  cast_po_down_to_po_with_bottom (A2C_below_po A)
  =
    option_map A2C_below_po_with_bottom (A_cast_po_down_to_po_with_bottom A).
Proof. destruct A; unfold cast_po_down_to_po_with_bottom,
         A_cast_po_down_to_po_with_bottom,
         A2C_below_po, A2C_below_po_with_bottom; reflexivity. 
Qed.

Lemma correct_cast_fo_down_to_fo_with_bottom (A : @A_below_fo S) : 
  cast_fo_down_to_fo_with_bottom (A2C_below_fo A)
  =
    option_map A2C_below_fo_with_bottom (A_cast_fo_down_to_fo_with_bottom A).
Proof. destruct A; unfold cast_fo_down_to_fo_with_bottom,
         A_cast_fo_down_to_fo_with_bottom,
         A2C_below_fo, A2C_below_fo_with_bottom; reflexivity. 
Qed.

Lemma correct_cast_qo_down_to_po (A : @A_below_qo S) : 
  cast_qo_down_to_po (A2C_below_qo A)
  =
  option_map A2C_below_po (A_cast_qo_down_to_po A).
Proof. destruct A; unfold cast_qo_down_to_po, 
         A_cast_qo_down_to_po, 
         A2C_below_po, A2C_below_qo; reflexivity. 
Qed.

Lemma correct_cast_qo_down_to_fo (A : @A_below_qo S) : 
  cast_qo_down_to_fo (A2C_below_qo A)
  =
  option_map A2C_below_fo (A_cast_qo_down_to_fo A).
Proof. destruct A; unfold cast_qo_down_to_fo, 
         A_cast_qo_down_to_fo, 
         A2C_below_fo, A2C_below_qo; reflexivity. 
Qed.

Lemma correct_cast_qo_down_to_po_with_bottom (A : @A_below_qo S) : 
  cast_qo_down_to_po_with_bottom (A2C_below_qo A)
  =
    option_map A2C_below_po_with_bottom (A_cast_qo_down_to_po_with_bottom A).
Proof. unfold cast_qo_down_to_po_with_bottom,
         A_cast_qo_down_to_po_with_bottom.
         rewrite correct_cast_qo_down_to_po.
         destruct A; simpl; try reflexivity. 
         apply correct_cast_po_down_to_po_with_bottom. 
Qed.

Lemma correct_cast_qo_down_to_fo_with_bottom (A : @A_below_qo S) : 
  cast_qo_down_to_fo_with_bottom (A2C_below_qo A)
  =
    option_map A2C_below_fo_with_bottom (A_cast_qo_down_to_fo_with_bottom A).
Proof. unfold cast_qo_down_to_fo_with_bottom,
         A_cast_qo_down_to_fo_with_bottom.
         rewrite correct_cast_qo_down_to_fo.
         destruct A; simpl; try reflexivity. 
         apply correct_cast_fo_down_to_fo_with_bottom. 
Qed.


Lemma correct_cast_qo_down_to_qo_with_bottom (A : @A_below_qo S) : 
  cast_qo_down_to_qo_with_bottom (A2C_below_qo A)
  =
  option_map A2C_below_qo_with_bottom (A_cast_qo_down_to_qo_with_bottom A).
Proof. unfold cast_qo_down_to_qo_with_bottom,
         A_cast_qo_down_to_qo_with_bottom.
         destruct A; simpl; try reflexivity. 
Qed.

End MCAS.


End Verify.   

Section Commute. 

  Variable S : Type.

Lemma cast_up_po_with_bottom_A2C_commute (A : @A_below_po_with_bottom S) : 
  cast_up_po_with_bottom (A2C_below_po_with_bottom A)
  =
 A2C_po_with_bottom (A_cast_up_po_with_bottom A).
Proof. destruct A; unfold cast_up_po_with_bottom, A_cast_up_po_with_bottom; simpl.
       reflexivity.
Qed.       

Lemma cast_up_po_A2C_commute (A : @A_below_po S) : 
  cast_up_po (A2C_below_po A)
  =
  A2C_po (A_cast_up_po A).
Proof. destruct A; unfold cast_up_po, A_cast_up_po; simpl.
       - reflexivity. 
       - rewrite cast_up_po_with_bottom_A2C_commute.
         rewrite correct_po_from_po_with_bottom.
         reflexivity.
Qed. 

Lemma cast_up_fo_with_bottom_A2C_commute (A : @A_below_fo_with_bottom S) : 
  cast_up_fo_with_bottom (A2C_below_fo_with_bottom A)
  =
 A2C_fo_with_bottom (A_cast_up_fo_with_bottom A).
Proof. destruct A; unfold cast_up_fo_with_bottom, A_cast_up_fo_with_bottom; simpl.
       reflexivity.
Qed.       

Lemma cast_up_fo_A2C_commute (A : @A_below_fo S) : 
  cast_up_fo (A2C_below_fo A)
  =
  A2C_fo (A_cast_up_fo A).
Proof. destruct A; unfold cast_up_fo, A_cast_up_fo; simpl.
       - reflexivity. 
       - rewrite cast_up_fo_with_bottom_A2C_commute.
         rewrite correct_fo_from_fo_with_bottom.
         reflexivity.
Qed.

Lemma cast_up_qo_with_bottom_A2C_commute (A : @A_below_qo_with_bottom S) : 
  cast_up_qo_with_bottom (A2C_below_qo_with_bottom A)
  =
  A2C_qo_with_bottom (A_cast_up_qo_with_bottom A).
Proof. destruct A;
       unfold cast_up_qo_with_bottom, A_cast_up_qo_with_bottom; simpl; 
         try reflexivity.
       - rewrite cast_up_fo_with_bottom_A2C_commute.
         rewrite correct_qo_with_bottom_from_fo_with_bottom.
         reflexivity.
       - rewrite cast_up_po_with_bottom_A2C_commute.
         rewrite correct_qo_with_bottom_from_po_with_bottom.
         reflexivity. 
Qed.       
  
Lemma cast_up_qo_A2C_commute (A : @A_below_qo S) : 
  cast_up_qo (A2C_below_qo A)
  =
  A2C_qo (A_cast_up_qo A).
Proof. destruct A; unfold cast_up_qo, A_cast_up_qo; simpl.
       - reflexivity.
       - rewrite cast_up_po_A2C_commute.
         rewrite correct_qo_from_po. 
         reflexivity.
       - rewrite cast_up_fo_A2C_commute.
         rewrite correct_qo_from_fo. 
         reflexivity. 
       - rewrite cast_up_qo_with_bottom_A2C_commute.
         rewrite correct_qo_from_qo_with_bottom. 
         reflexivity.
Qed.


End Commute. 


