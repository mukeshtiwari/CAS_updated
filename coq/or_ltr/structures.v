Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast. 
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.po.properties. 
Require Import CAS.coq.po.structures. 
Require Import CAS.coq.tr.structures. 
Require Import CAS.coq.ot.properties.

Section ACAS.


Record top_bottom_proofs (S: Type) (eq lte : brel S) := 
{
  A_top_bottom_exists_top_d       : brel_exists_qo_top_decidable S eq lte
; A_top_bottom_exists_bottom_d    : brel_exists_qo_bottom_decidable S eq lte 
}.

Record oltr_proofs (L S : Type) (lte : brel S) (ltr : ltr_type L S) :=
{
  A_poltr_monotone_d             : olt_monotone_decidable L S lte ltr
; A_poltr_strictly_monotone_d    : olt_strictly_monotone_decidable L S lte ltr
; A_poltr_increasing_d           : olt_increasing_decidable L S lte ltr                                      
; A_poltr_strictly_increasing_d  : olt_strictly_increasing_decidable L S lte ltr
}.

Record A_poltr (L S : Type) :=
{
  A_poltr_carrier      : A_eqv S
; A_poltr_label        : A_eqv L
; A_poltr_lte          : brel S                                               
; A_poltr_ltr          : ltr_type L S (* L -> (S -> S) *)
; A_poltr_lte_proofs   : po_proofs S (A_eqv_eq S A_poltr_carrier) A_poltr_lte                                 
; A_poltr_ltr_proofs   : left_transform_proofs L S (A_eqv_eq S A_poltr_carrier) (A_eqv_eq L A_poltr_label)  A_poltr_ltr
; A_poltr_top_bottom_proofs : top_bottom_proofs S (A_eqv_eq S A_poltr_carrier) A_poltr_lte                                           
; A_poltr_proofs       : oltr_proofs L S A_poltr_lte A_poltr_ltr                                  
; A_poltr_ast          : cas_lotr_ast 
}.



  
Record with_bottom_proofs (S: Type) (eq lte : brel S) := 
{
  A_with_bottom_exists_top_d       : brel_exists_qo_top_decidable S eq lte
; A_with_bottom_exists             : brel_exists_qo_bottom S eq lte 
}.
  
  
Record qoltr_msi_proofs (L S : Type) (lte : brel S) (ltr : ltr_type L S) :=
{
  A_qoltr_msi_monotone  : olt_monotone L S lte ltr 
; A_qoltr_msi_strictly_increasing  : olt_strictly_increasing L S lte ltr
}.


Record A_qoltr_monotone_strictly_increasing (L S : Type) :=
{
  A_qoltr_msi_carrier      : A_eqv S
; A_qoltr_msi_label        : A_eqv L
; A_qoltr_msi_lte          : brel S                                               
; A_qoltr_msi_ltr          : ltr_type L S (* L -> (S -> S) *)
; A_qoltr_msi_lte_proofs   : qo_proofs S (A_eqv_eq S A_qoltr_msi_carrier) A_qoltr_msi_lte                                 
; A_qoltr_msi_ltr_proofs   : left_transform_proofs L S (A_eqv_eq S A_qoltr_msi_carrier) (A_eqv_eq L A_qoltr_msi_label)  A_qoltr_msi_ltr
; A_qoltr_msi_bottom_proofs : with_bottom_proofs S (A_eqv_eq S A_qoltr_msi_carrier) A_qoltr_msi_lte                                           
; A_qoltr_msi_proofs       : qoltr_msi_proofs L S A_qoltr_msi_lte A_qoltr_msi_ltr                                  
; A_qoltr_msi_ast          : cas_lotr_ast 
}.



Record A_woltr_monotone_strictly_increasing (L S : Type) :=
{
  A_woltr_msi_carrier      : A_eqv S
; A_woltr_msi_label        : A_eqv L
; A_woltr_msi_lte          : brel S                                               
; A_woltr_msi_ltr          : ltr_type L S (* L -> (S -> S) *)
; A_woltr_msi_lte_proofs   : wo_proofs S (A_eqv_eq S A_woltr_msi_carrier) A_woltr_msi_lte                                 
; A_woltr_msi_ltr_proofs   : left_transform_proofs L S (A_eqv_eq S A_woltr_msi_carrier) (A_eqv_eq L A_woltr_msi_label)  A_woltr_msi_ltr
; A_woltr_msi_bottom_proofs : with_bottom_proofs S (A_eqv_eq S A_woltr_msi_carrier) A_woltr_msi_lte                                           
; A_woltr_msi_proofs       : qoltr_msi_proofs L S A_woltr_msi_lte A_woltr_msi_ltr                                  
; A_woltr_msi_ast          : cas_lotr_ast 
}.



Record poltr_mi_proofs (L S : Type) (lte : brel S) (ltr : L -> (S -> S)) :=
{
  A_poltr_mi_monotone    : olt_monotone L S lte ltr 
; A_poltr_mi_increasing  : olt_increasing L S lte ltr
}.


Record A_poltr_monotone_increasing (L S : Type) :=
{
  A_poltr_mi_carrier      : A_eqv S
; A_poltr_mi_label        : A_eqv L
; A_poltr_mi_lte          : brel S                                               
; A_poltr_mi_ltr          : ltr_type L S (* L -> (S -> S) *)
; A_poltr_mi_lte_proofs   : po_proofs S (A_eqv_eq S A_poltr_mi_carrier) A_poltr_mi_lte                                 
; A_poltr_mi_ltr_proofs   : left_transform_proofs L S (A_eqv_eq S A_poltr_mi_carrier) (A_eqv_eq L A_poltr_mi_label)  A_poltr_mi_ltr
; A_poltr_mi_bottom_proofs : with_bottom_proofs S (A_eqv_eq S A_poltr_mi_carrier) A_poltr_mi_lte                                 
; A_poltr_mi_proofs       : poltr_mi_proofs L S A_poltr_mi_lte A_poltr_mi_ltr                                  
; A_poltr_mi_ast          : cas_lotr_ast 
}.



End ACAS. 


Section CAS.


Record top_bottom_certificates {S: Type} := 
{
  top_bottom_exists_top_d       : @certify_exists_qo_top S 
; top_bottom_exists_bottom_d    : @certify_exists_qo_bottom S
}.

Record oltr_certificates {L S : Type} :=
{
  poltr_monotone_d             : @certify_olt_monotone L S
; poltr_strictly_monotone_d    : @certify_olt_strictly_monotone L S
; poltr_increasing_d           : @certify_olt_increasing L S
; poltr_strictly_increasing_d  : @certify_olt_strictly_increasing L S
}.

Record poltr {L S : Type} :=
{
  poltr_carrier          : @eqv S
; poltr_label            : @eqv L
; poltr_lte              : @brel S                                               
; poltr_ltr              : @ltr_type L S 
; poltr_lte_certs        : @po_certificates S 
; poltr_ltr_certs        : @left_transform_certificates L S 
; poltr_top_bottom_certs : @top_bottom_certificates S 
; poltr_certs            : @oltr_certificates L S 
; poltr_ast              : cas_lotr_ast 
}.



Record with_bottom_certs {S: Type} := 
{
  with_bottom_exists_top_d  : @certify_exists_qo_top S 
; with_bottom_exists        : @assert_exists_qo_bottom S 
}.
  

Record qoltr_msi_certificates {L S : Type} :=
{
  qoltr_msi_monotone             : @assert_olt_monotone L S 
; qoltr_msi_strictly_increasing  : @assert_olt_strictly_increasing L S 
}.



Record qoltr_monotone_strictly_increasing {L S : Type} :=
{
  qoltr_msi_carrier      : @eqv S
; qoltr_msi_label        : @eqv L
; qoltr_msi_lte          : @brel S                                               
; qoltr_msi_ltr          : @ltr_type L S 
; qoltr_msi_lte_certs    : @qo_certificates S 
; qoltr_msi_ltr_certs    : @left_transform_certificates L S
; qoltr_msi_bottom_certs : @with_bottom_certs S                                                                                          
; qoltr_msi_certs        : @qoltr_msi_certificates L S
; qoltr_msi_ast          : cas_lotr_ast 
}.



Record woltr_monotone_strictly_increasing {L S : Type} :=
{
  woltr_msi_carrier      : @eqv S
; woltr_msi_label        : @eqv L
; woltr_msi_lte          : @brel S                                               
; woltr_msi_ltr          : @ltr_type L S 
; woltr_msi_lte_certs    : @wo_certificates S
; woltr_msi_ltr_certs    : @left_transform_certificates L S
; woltr_msi_bottom_certs : @with_bottom_certs S                                             
; woltr_msi_certs        : @qoltr_msi_certificates L S
; woltr_msi_ast          : cas_lotr_ast 
}.

Record poltr_mi_certificates {L S : Type} := 
{
  poltr_mi_monotone    : @assert_olt_monotone L S 
; poltr_mi_increasing  : @assert_olt_increasing L S 
}.


Record poltr_monotone_increasing {L S : Type} :=
{
  poltr_mi_carrier      : @eqv S
; poltr_mi_label        : @eqv L
; poltr_mi_lte          : @brel S                                               
; poltr_mi_ltr          : @ltr_type L S 
; poltr_mi_lte_certs    : @po_certificates S 
; poltr_mi_ltr_certs    : @left_transform_certificates L S
; poltr_mi_bottom_certs : @with_bottom_certs S                                                                                         
; poltr_mi_certs        : @poltr_mi_certificates L S 
; poltr_mi_ast          : cas_lotr_ast 
}.

End CAS.


Section Translate.

Definition P2C_oltr (L S : Type) (lte : brel S) (ltr : ltr_type L S) (P : oltr_proofs L S lte ltr) := 
{|
  poltr_monotone_d             := p2c_olt_monotone L S lte ltr (A_poltr_monotone_d _ _ _ _ P)
; poltr_strictly_monotone_d    := p2c_olt_strictly_monotone L S lte ltr (A_poltr_strictly_monotone_d _ _ _ _ P)
; poltr_increasing_d           := p2c_olt_increasing L S lte ltr (A_poltr_increasing_d _ _ _ _ P)
; poltr_strictly_increasing_d  := p2c_olt_strictly_increasing L S lte ltr (A_poltr_strictly_increasing_d _ _ _ _ P)
|}.


Definition P2C_top_bottom (S: Type) (eq lte : brel S) (P : top_bottom_proofs S eq lte) := 
{|
  top_bottom_exists_top_d       := p2c_exists_qo_top_check _ _ _ (A_top_bottom_exists_top_d _ _ _ P)
; top_bottom_exists_bottom_d    := p2c_exists_qo_bottom_check _ _ _ (A_top_bottom_exists_bottom_d _ _ _ P)
|}.

 
Definition A2C_poltr (L S : Type) (A : A_poltr L S) := 
{|
  poltr_carrier          := A2C_eqv _ (A_poltr_carrier _ _ A)
; poltr_label            := A2C_eqv _ (A_poltr_label _ _ A) 
; poltr_lte              := A_poltr_lte _ _ A 
; poltr_ltr              := A_poltr_ltr _ _ A 
; poltr_lte_certs        := P2C_po _ _ (A_poltr_lte_proofs _ _ A) 
; poltr_ltr_certs        := P2C_left_transform _ _ _ _ _ (A_poltr_ltr_proofs _ _ A) 
; poltr_top_bottom_certs := P2C_top_bottom _ _ _ (A_poltr_top_bottom_proofs _ _ A) 
; poltr_certs            := P2C_oltr _ _ _ _ (A_poltr_proofs _ _ A) 
; poltr_ast              := A_poltr_ast _ _ A
|}.


Definition P2C_with_bottom  (S: Type) (eq lte : brel S) (P : with_bottom_proofs S eq lte) := 
{|
  with_bottom_exists_top_d       := p2c_exists_qo_top_check _ _ _ (A_with_bottom_exists_top_d _ _ _ P)
; with_bottom_exists             := p2c_exists_qo_bottom_assert _ _ _ (A_with_bottom_exists _ _ _ P)
|}.
  


Definition P2C_qoltr_msi (L S : Type) (lte : brel S) (ltr : ltr_type L S) (P : qoltr_msi_proofs L S lte ltr) :=
{|
  qoltr_msi_monotone             := @Assert_Olt_Monotone L S 
; qoltr_msi_strictly_increasing  := @Assert_Olt_Strictly_Increasing L S 
|}.



    
Definition A2C_qoltr_monotone_strictly_increasing (L S : Type) (Q : A_qoltr_monotone_strictly_increasing L S) := 
{|
  qoltr_msi_carrier      := A2C_eqv S (A_qoltr_msi_carrier L S Q) 
; qoltr_msi_label        := A2C_eqv L (A_qoltr_msi_label L S Q) 
; qoltr_msi_lte          := A_qoltr_msi_lte L S Q
; qoltr_msi_ltr          := A_qoltr_msi_ltr L S Q
; qoltr_msi_lte_certs    := P2C_qo _ _ (A_qoltr_msi_lte_proofs L S Q)
; qoltr_msi_ltr_certs    := P2C_left_transform L S _ _ _ (A_qoltr_msi_ltr_proofs L S Q)
; qoltr_msi_bottom_certs := P2C_with_bottom _ _ _ (A_qoltr_msi_bottom_proofs L S Q)
; qoltr_msi_certs        := P2C_qoltr_msi L S _ _ (A_qoltr_msi_proofs L S Q)
; qoltr_msi_ast          := A_qoltr_msi_ast L S Q
|}.


Definition A2C_woltr_monotone_strictly_increasing (L S : Type) (Q : A_woltr_monotone_strictly_increasing L S) := 
{|
  woltr_msi_carrier      := A2C_eqv S (A_woltr_msi_carrier L S Q) 
; woltr_msi_label        := A2C_eqv L (A_woltr_msi_label L S Q) 
; woltr_msi_lte          := A_woltr_msi_lte L S Q
; woltr_msi_ltr          := A_woltr_msi_ltr L S Q
; woltr_msi_lte_certs    := P2C_wo _ _ (A_woltr_msi_lte_proofs L S Q)
; woltr_msi_ltr_certs    := P2C_left_transform L S _ _ _ (A_woltr_msi_ltr_proofs L S Q)
; woltr_msi_bottom_certs := P2C_with_bottom _ _ _ (A_woltr_msi_bottom_proofs L S Q)                                    
; woltr_msi_certs        := P2C_qoltr_msi L S _ _ (A_woltr_msi_proofs L S Q)
; woltr_msi_ast          := A_woltr_msi_ast L S Q
|}.

Definition P2C_poltr_mi (L S : Type) (lte : brel S) (ltr : ltr_type L S) (P : poltr_mi_proofs L S lte ltr) := 
{|
  poltr_mi_monotone    := @Assert_Olt_Monotone L S 
; poltr_mi_increasing  := @Assert_Olt_Increasing L S 
|}.
  
Definition A2C_poltr_monotone_increasing (L S : Type) (P : A_poltr_monotone_increasing L S) :=
{|
  poltr_mi_carrier     := A2C_eqv S (A_poltr_mi_carrier L S P) 
; poltr_mi_label       := A2C_eqv L (A_poltr_mi_label L S P) 
; poltr_mi_lte         := A_poltr_mi_lte L S P 
; poltr_mi_ltr         := A_poltr_mi_ltr L S P 
; poltr_mi_lte_certs   := P2C_po _ _  (A_poltr_mi_lte_proofs L S P)
; poltr_mi_ltr_certs   := P2C_left_transform L S _ _  _ (A_poltr_mi_ltr_proofs L S P)
; poltr_mi_bottom_certs := P2C_with_bottom _ _ _ (A_poltr_mi_bottom_proofs L S P)                                                                      
; poltr_mi_certs       := P2C_poltr_mi L S _ _ (A_poltr_mi_proofs L S P) 
; poltr_mi_ast         := A_poltr_mi_ast L S P 
|}.






End Translate.
