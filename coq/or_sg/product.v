Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.
Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.po.properties.
Require Import CAS.coq.po.structures.
Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures.
Require Import CAS.coq.os.properties.
Require Import CAS.coq.os.structures.


Require Import CAS.coq.theory.facts. 
Require Import CAS.coq.po.from_sg_left. 



Section Theory.

Variable S    : Type.
Variable wS   : S.

Variable T    : Type.
Variable wT   : T.

Variable lteS : brel S.
Variable lteReflS : brel_reflexive S lteS. 

Variable lteT : brel T. 
Variable lteReflT : brel_reflexive T lteT. 

Variable bS     : binary_op S.
Variable bT     : binary_op T.

Notation "a <=S b"   := (lteS a b = true)          (at level 15).
Notation "a <=T b"   := (lteT a b = true)          (at level 15).

Notation "a [*S] b"   := (bS a b)          (at level 15).
Notation "a [*T] b"   := (bT a b)          (at level 15).       

Lemma os_product_left_monotone (LMS : os_left_monotone S lteS bS) (LMT : os_left_monotone T lteT bT) :
     os_left_monotone (S * T) (brel_product lteS lteT) (bop_product bS bT). 
Proof. intros [s1 t1] [s2 t2] [s3 t3]. compute. 
       case_eq(lteS s2 s3); intro A; case_eq(lteT t2 t3); intro B; intro C. 
          assert (D := LMS s1 _ _ A). rewrite D.
          assert (E := LMT t1 _ _ B). rewrite E. reflexivity. 
          discriminate C. discriminate C. discriminate C. 
Qed.        

Lemma os_product_not_left_monotone_first (NLMS : os_not_left_monotone S lteS bS) : 
     os_not_left_monotone (S * T) (brel_product lteS lteT) (bop_product bS bT). 
Proof. destruct NLMS as [[s1 [s2 s3]] [A B]].
       exists ((s1, wT), ((s2, wT), (s3, wT))). split; compute. 
          rewrite A. exact (lteReflT wT). 
          rewrite B; auto. 
Defined. 

Lemma os_product_not_left_monotone_second (NLMT : os_not_left_monotone T lteT bT) : 
     os_not_left_monotone (S * T) (brel_product lteS lteT) (bop_product bS bT). 
Proof. destruct NLMT as [[t1 [t2 t3]] [A B]].
       exists ((wS, t1), ((wS, t2), (wS, t3))). split; compute. 
          rewrite A. rewrite lteReflS; auto.
          rewrite B. case_eq(lteS (wS [*S] wS) (wS [*S] wS)); intro C; auto. 
Defined. 

Definition os_product_left_monotone_decide : 
  os_left_monotone_decidable S lteS bS ->
  os_left_monotone_decidable T lteT bT ->   
   os_left_monotone_decidable (S * T) (brel_product lteS lteT) (bop_product bS bT)
:= λ dS dT ,  
   match dS with 
   | inl LMS  => match dT with
                 | inl LMT  => inl (os_product_left_monotone LMS LMT)
                 | inr NLMT => inr (os_product_not_left_monotone_second NLMT)
                 end 
   | inr NLMS => inr (os_product_not_left_monotone_first NLMS)
   end. 

Lemma os_product_right_monotone  (RMS : os_right_monotone S lteS bS) (RMT : os_right_monotone T lteT bT): 
    os_right_monotone (S * T) (brel_product lteS lteT) (bop_product bS bT). 
Proof. intros [s1 t1] [s2 t2] [s3 t3]. compute. 
       case_eq(lteS s2 s3); intro A; case_eq(lteT t2 t3); intro B; intro C. 
          assert (D := RMS s1 _ _ A). rewrite D.
          assert (E := RMT t1 _ _ B). rewrite E. reflexivity. 
          discriminate C. discriminate C. discriminate C. 
Qed.        

Lemma os_product_not_right_monotone_first (NRMS : os_not_right_monotone S lteS bS) : 
     os_not_right_monotone (S * T) (brel_product lteS lteT) (bop_product bS bT). 
Proof. destruct NRMS as [[s1 [s2 s3]] [A B]].
       exists ((s1, wT), ((s2, wT), (s3, wT))). split; compute. 
          rewrite A. exact (lteReflT wT). 
          rewrite B; auto. 
Defined.

Lemma os_product_not_right_monotone_second (NRMT : os_not_right_monotone T lteT bT) : 
     os_not_right_monotone (S * T) (brel_product lteS lteT) (bop_product bS bT). 
Proof. destruct NRMT as [[t1 [t2 t3]] [A B]].
       exists ((wS, t1), ((wS, t2), (wS, t3))). split; compute. 
          rewrite A. rewrite lteReflS; auto.
          rewrite B. case_eq(lteS (wS [*S] wS) (wS [*S] wS)); intro C; auto. 
Defined. 

Definition os_product_right_monotone_decide : 
  os_right_monotone_decidable S lteS bS ->
  os_right_monotone_decidable T lteT bT ->   
   os_right_monotone_decidable (S * T) (brel_product lteS lteT) (bop_product bS bT)
:= λ dS dT ,  
   match dS with 
   | inl RMS  => match dT with
                 | inl RMT  => inl (os_product_right_monotone RMS RMT)
                 | inr NRMT => inr (os_product_not_right_monotone_second NRMT)
                 end 
   | inr NRMS => inr (os_product_not_right_monotone_first NRMS)
   end. 


Lemma os_product_left_increasing : 
  os_left_increasing S lteS bS -> os_left_increasing T lteT bT -> 
  os_left_increasing (S * T) (brel_product lteS lteT) (bop_product bS bT). 
Proof. intros LIS LIT [s1 t1] [s2 t2]. compute. rewrite LIS. rewrite LIT; auto. Qed. 

Lemma os_product_not_left_increasing_first : 
  os_not_left_increasing S lteS bS -> 
  os_not_left_increasing (S * T) (brel_product lteS lteT) (bop_product bS bT). 
Proof. intros [[s1 s2] A]. exists ((s1, wT), (s2, wT)). compute. rewrite A; auto. Defined. 

Lemma os_product_not_left_increasing_second : 
  os_not_left_increasing T lteT bT -> 
  os_not_left_increasing (S * T) (brel_product lteS lteT) (bop_product bS bT). 
Proof. intros [[t1 t2] A]. exists ((wS, t1), (wS, t2)). compute. rewrite A.
       case_eq(lteS wS (wS [*S] wS)); intro B; auto. 
Defined. 

Definition os_product_left_increasing_decide : 
  os_left_increasing_decidable S lteS bS ->
  os_left_increasing_decidable T lteT bT ->   
   os_left_increasing_decidable (S * T) (brel_product lteS lteT) (bop_product bS bT)
:= λ dS dT ,  
   match dS with 
   | inl LIS  => match dT with
                 | inl LIT  => inl (os_product_left_increasing LIS LIT)
                 | inr NLIT => inr (os_product_not_left_increasing_second NLIT)
                 end 
   | inr NLIS => inr (os_product_not_left_increasing_first NLIS)
   end. 


Lemma os_product_right_increasing : 
  os_right_increasing S lteS bS -> os_right_increasing T lteT bT -> 
  os_right_increasing (S * T) (brel_product lteS lteT) (bop_product bS bT). 
Proof. intros RIS RIT [s1 t1] [s2 t2]. compute. rewrite RIS. rewrite RIT; auto. Qed. 


Lemma os_product_not_right_increasing_first : 
  os_not_right_increasing S lteS bS -> 
  os_not_right_increasing (S * T) (brel_product lteS lteT) (bop_product bS bT). 
Proof. intros [[s1 s2] A]. exists ((s1, wT), (s2, wT)). compute. rewrite A; auto. Defined. 

Lemma os_product_not_right_increasing_second : 
  os_not_right_increasing T lteT bT -> 
  os_not_right_increasing (S * T) (brel_product lteS lteT) (bop_product bS bT). 
Proof. intros [[t1 t2] A]. exists ((wS, t1), (wS, t2)). compute. rewrite A.
       case_eq(lteS wS (wS [*S] wS)); intro B; auto. 
Defined. 

Definition os_product_right_increasing_decide : 
  os_right_increasing_decidable S lteS bS ->
  os_right_increasing_decidable T lteT bT ->   
   os_right_increasing_decidable (S * T) (brel_product lteS lteT) (bop_product bS bT)
:= λ dS dT ,  
   match dS with 
   | inl LIS  => match dT with
                 | inl LIT  => inl (os_product_right_increasing LIS LIT)
                 | inr NLIT => inr (os_product_not_right_increasing_second NLIT)
                 end 
   | inr NLIS => inr (os_product_not_right_increasing_first NLIS)
   end. 


Lemma os_product_left_strictly_increasing :
  ((os_left_strictly_increasing S lteS bS) * (os_left_strictly_increasing T lteT bT)) +  
  ((os_left_strictly_increasing S lteS bS) * (os_left_increasing T lteT bT)) + 
  ((os_left_increasing S lteS bS) * (os_left_strictly_increasing T lteT bT)) ->
     os_left_strictly_increasing (S * T) (brel_product lteS lteT) (bop_product bS bT). 
Proof. intros [ [ [LSIS LSIT] | [LSIS LIT] ] | [LIS LSIT]] [s1 t1] [s2 t2]; compute; split.
          destruct (LSIS s1 s2) as [A B]. destruct (LSIT t1 t2) as [C D]. rewrite A. rewrite C; auto. 
          destruct (LSIS s1 s2) as [A B]. destruct (LSIT t1 t2) as [C D]. rewrite B; auto. 
          destruct (LSIS s1 s2) as [A B]. assert (C := LIT t1 t2). rewrite A. rewrite C; auto. 
          destruct (LSIS s1 s2) as [A B]. assert (C := LIT t1 t2). rewrite B; auto. 
          assert (A := LIS s1 s2). destruct (LSIT t1 t2) as [B C]. rewrite A. rewrite B; auto. 
          assert (A := LIS s1 s2). destruct (LSIT t1 t2) as [B C]. rewrite C. 
             case_eq(lteS (s1 [*S] s2) s1); intro D; auto.           
Qed. 


Lemma os_product_not_left_strictly_increasing :
  ((os_not_left_strictly_increasing S lteS bS) + (os_not_left_increasing T lteT bT)) *
  ((os_not_left_increasing S lteS bS)          + (os_not_left_strictly_increasing T lteT bT)) -> 
  os_not_left_strictly_increasing (S * T) (brel_product lteS lteT) (bop_product bS bT). 
Proof. intros [ [[[s1 s2] [A1 | A2]] | [[t1 t2] B]]  [[[s3 s4] C] | [[t3 t4] [D1 | D2]]] ].
       exists ((s1, wT), (s2, wT)); compute. rewrite A1; auto. 
       exists ((s1, wT), (s2, wT)); compute. rewrite A1; auto. 
       exists ((s1, wT), (s2, wT)); compute. rewrite A1; auto. 
       exists ((s3, wT), (s4, wT)); compute. rewrite C; auto. 
       exists ((wS, t3), (wS, t4)); compute. rewrite D1; auto.        
          case_eq(lteS wS (wS [*S] wS)); intro E; auto. 
       exists ((s1, t3), (s2, t4)); compute. rewrite A2. rewrite D2; auto.        
       exists ((s3, wT), (s4, wT)); compute. rewrite C; auto.        
       exists ((wS, t3), (wS, t4)); compute. rewrite D1; auto.        
          case_eq(lteS wS (wS [*S] wS)); intro E; auto. 
       exists ((wS, t1), (wS, t2)); compute. rewrite B; auto.
          case_eq(lteS wS (wS [*S] wS)); intro E; auto. 
Qed. 


Definition os_product_left_strictly_increasing_decide : 
  os_left_strictly_increasing_decidable S lteS bS ->
  os_left_increasing_decidable S lteS bS ->
  os_left_strictly_increasing_decidable T lteT bT ->
  os_left_increasing_decidable T lteT bT ->     
   os_left_strictly_increasing_decidable (S * T) (brel_product lteS lteT) (bop_product bS bT)
:= λ dLSIS dLIS dLSIT dLIT,  
   match dLSIS, dLSIT with 
   | inl LSIS,  inl LSIT  => inl (os_product_left_strictly_increasing (inl (inl (LSIS, LSIT))))
   | inl LSIS,  inr NLSIT => match dLIT with
                             | inl LIT  => inl (os_product_left_strictly_increasing (inl (inr (LSIS, LIT))))
                             | inr NLIT => inr (os_product_not_left_strictly_increasing (inr NLIT, inr NLSIT))
                             end 
   | inr NLSIS, inl LSIT  => match dLIS with
                             | inl LIS  => inl (os_product_left_strictly_increasing (inr (LIS, LSIT)))
                             | inr NLIS => inr (os_product_not_left_strictly_increasing (inl NLSIS, inl NLIS))
                             end 
   | inr NLSIS, inr NLSIT => inr (os_product_not_left_strictly_increasing (inl NLSIS, inr NLSIT))
   end. 

Lemma os_product_right_strictly_increasing :
  ((os_right_strictly_increasing S lteS bS) * (os_right_strictly_increasing T lteT bT)) +  
  ((os_right_strictly_increasing S lteS bS) * (os_right_increasing T lteT bT)) + 
  ((os_right_increasing S lteS bS) * (os_right_strictly_increasing T lteT bT)) ->
     os_right_strictly_increasing (S * T) (brel_product lteS lteT) (bop_product bS bT). 
Proof. intros [ [ [RSIS RSIT] | [RSIS RIT] ] | [RIS RSIT]] [s1 t1] [s2 t2]; compute; split.
          destruct (RSIS s1 s2) as [A B]. destruct (RSIT t1 t2) as [C D]. rewrite A. rewrite C; auto. 
          destruct (RSIS s1 s2) as [A B]. destruct (RSIT t1 t2) as [C D]. rewrite B; auto. 
          destruct (RSIS s1 s2) as [A B]. assert (C := RIT t1 t2). rewrite A. rewrite C; auto. 
          destruct (RSIS s1 s2) as [A B]. assert (C := RIT t1 t2). rewrite B; auto. 
          assert (A := RIS s1 s2). destruct (RSIT t1 t2) as [B C]. rewrite A. rewrite B; auto. 
          assert (A := RIS s1 s2). destruct (RSIT t1 t2) as [B C]. rewrite C. 
             case_eq(lteS (s1 [*S] s2) s1); intro D; auto. 
             case_eq(lteS (s2 [*S] s1) s1); intro E; auto.              
             case_eq(lteS (s2 [*S] s1) s1); intro E; auto.                           
Qed. 


Lemma os_product_not_right_strictly_increasing :
  ((os_not_right_strictly_increasing S lteS bS) + (os_not_right_increasing T lteT bT)) *
  ((os_not_right_increasing S lteS bS)          + (os_not_right_strictly_increasing T lteT bT)) -> 
  os_not_right_strictly_increasing (S * T) (brel_product lteS lteT) (bop_product bS bT). 
Proof. intros [ [[[s1 s2] [A1 | A2]] | [[t1 t2] B]]  [[[s3 s4] C] | [[t3 t4] [D1 | D2]]] ].
       exists ((s1, wT), (s2, wT)); compute. rewrite A1; auto. 
       exists ((s1, wT), (s2, wT)); compute. rewrite A1; auto. 
       exists ((s1, wT), (s2, wT)); compute. rewrite A1; auto. 
       exists ((s3, wT), (s4, wT)); compute. rewrite C; auto. 
       exists ((wS, t3), (wS, t4)); compute. rewrite D1; auto.        
          case_eq(lteS wS (wS [*S] wS)); intro E; auto. 
       exists ((s1, t3), (s2, t4)); compute. rewrite A2. rewrite D2; auto.        
       exists ((s3, wT), (s4, wT)); compute. rewrite C; auto.        
       exists ((wS, t3), (wS, t4)); compute. rewrite D1; auto.        
          case_eq(lteS wS (wS [*S] wS)); intro E; auto. 
       exists ((wS, t1), (wS, t2)); compute. rewrite B; auto.
          case_eq(lteS wS (wS [*S] wS)); intro E; auto. 
Qed. 


Definition os_product_right_strictly_increasing_decide : 
  os_right_strictly_increasing_decidable S lteS bS ->
  os_right_increasing_decidable S lteS bS ->
  os_right_strictly_increasing_decidable T lteT bT ->
  os_right_increasing_decidable T lteT bT ->     
   os_right_strictly_increasing_decidable (S * T) (brel_product lteS lteT) (bop_product bS bT)
:= λ dRSIS dRIS dRSIT dRIT,  
   match dRSIS, dRSIT with 
   | inl RSIS,  inl RSIT  => inl (os_product_right_strictly_increasing (inl (inl (RSIS, RSIT))))
   | inl RSIS,  inr NRSIT => match dRIT with
                             | inl RIT  => inl (os_product_right_strictly_increasing (inl (inr (RSIS, RIT))))
                             | inr NRIT => inr (os_product_not_right_strictly_increasing (inr NRIT, inr NRSIT))
                             end 
   | inr NRSIS, inl RSIT  => match dRIS with
                             | inl RIS  => inl (os_product_right_strictly_increasing (inr (RIS, RSIT)))
                             | inr NRIS => inr (os_product_not_right_strictly_increasing (inl NRSIS, inl NRIS))
                             end 
   | inr NRSIS, inr NRSIT => inr (os_product_not_right_strictly_increasing (inl NRSIS, inr NRSIT))
   end. 



End Theory.

(*


Lemma os_from_bs_left_top_equals_ann (P : bops_id_equals_ann S eq plus times) : os_top_equals_ann S eq lte times.
Proof. destruct P as [a [A B]]. exists a; split; auto. apply po_from_sg_left_is_top; auto. Defined. 


Lemma os_from_bs_left_not_top_equals_ann (P : bops_not_id_equals_ann S eq plus times) : os_not_top_equals_ann S eq lte times.
Proof. intro s. destruct (P s) as [A | A]; auto. left. 
       destruct A as [u B].  exists u. 
       destruct B as [B | B]; compute. 
          case_eq(eq u (u [+] s)); intro C; auto.
          apply symS in C. assert (D := commP s u). 
          rewrite (trnS _ _ _ D C) in B. discriminate B.
          case_eq(eq u (u [+] s)); intro C; auto.
          apply symS in C. rewrite C in B. discriminate B.
Defined. 


Definition os_from_bs_left_top_equals_ann_decide : 
   bops_id_equals_ann_decidable S eq plus times -> os_top_equals_ann_decidable S eq lte times
:= λ d ,  
   match d with 
   | inl iea  => inl (os_from_bs_left_top_equals_ann iea)
   | inr niea => inr (os_from_bs_left_not_top_equals_ann niea)
   end. 


Lemma os_from_bs_left_bottom_equals_id (P : bops_id_equals_ann S eq times plus) : os_bottom_equals_id S eq lte times.
Proof. destruct P as [a [A B]]. exists a; split; auto. apply po_from_sg_left_is_bottom; auto. Defined. 


Lemma os_from_bs_left_not_bottom_equals_id (P : bops_not_id_equals_ann S eq times plus) : os_not_bottom_equals_id S eq lte times.
Proof. intro s. destruct (P s) as [A | A]; auto. left. 
       destruct A as [u B].  exists u. 
       destruct B as [B | B]; compute. 
          case_eq(eq s (s [+] u)); intro C; auto.
          apply symS in C. rewrite C in B. discriminate B.
          case_eq(eq s (s [+] u)); intro C; auto.
          assert (D := commP u s).  apply symS in C.
          rewrite (trnS _ _ _ D C) in B. discriminate B.
Defined. 


Definition os_from_bs_left_bottom_equals_id_decide : 
   bops_id_equals_ann_decidable S eq times plus -> os_bottom_equals_id_decidable S eq lte times
:= λ d ,  
   match d with 
   | inl iea  => inl (os_from_bs_left_bottom_equals_id iea)
   | inr niea => inr (os_from_bs_left_not_bottom_equals_id niea)
   end. 





Section ACAS.

Definition os_from_bs_left_proofs (S: Type) (eq : brel S) (plus times : binary_op S) :
  eqv_proofs S eq ->
  bop_congruence S eq times -> 
  semiring_proofs S eq plus times ->
  monotone_os_proofs S (brel_lte_left eq plus) times 
:= λ E tcong P,
let ref := A_eqv_reflexive S eq E in
let trn := A_eqv_transitive S eq E in  (* note: symmetry is not needed *) 
{|
  A_mos_left_monotonic     := os_from_bs_left_left_monotone S eq ref trn plus times tcong  (A_semiring_left_distributive S eq plus times P)
; A_mos_right_monotonic    := os_from_bs_left_right_monotone S eq ref trn plus times tcong  (A_semiring_right_distributive S eq plus times P)

; A_mos_left_increasing_d  := os_from_bs_left_left_increasing_decide S eq plus times (A_semiring_left_left_absorptive_d S eq plus times P)
; A_mos_right_increasing_d := os_from_bs_left_right_increasing_decide S eq plus times (A_semiring_left_right_absorptive_d S eq plus times P)
|}. 


Lemma bops_id_equals_ann_to_exists_ann (S: Type) (eq : brel S) (b1 b2 : binary_op S): 
  bops_id_equals_ann S eq b1 b2 -> (bop_exists_ann S eq b2).
Proof. intros [i [idP annP]]. exists i; auto. Defined. 



Definition from_bs_left_top_bottom_proofs (S: Type) (eq : brel S) (eqvP : eqv_proofs S eq)
           (plus : binary_op S) (times : binary_op S) (commP : bop_commutative S eq plus): 
  add_ann_mul_id_proofs S eq plus times -> top_bottom_ann_id_with_id_proofs S eq (lte S eq plus) times 
:= λ P, 
let symS := A_eqv_symmetric S eq eqvP in 
let trnS := A_eqv_transitive S eq eqvP in 
{|
  A_top_ann_d := os_from_bs_left_top_equals_ann_decide S eq symS trnS plus times commP
                          (A_add_ann_mul_id_plus_id_is_times_ann_d S eq plus times P)
; A_bottom_id :=  os_from_bs_left_bottom_equals_id S eq symS plus times
                          (A_add_ann_mul_id_times_id_is_plus_ann S eq plus times P)                                                    
|}.


Definition A_monotone_mposg_from_predioid (S : Type) : A_predioid_with_id S -> A_monotone_posg S
  := λ PDWI,
let eqv   := A_pdwid_eqv S PDWI in
let eq    := A_eqv_eq S eqv in                            
let eqvP  := A_eqv_proofs S eqv in
let plus  := A_pdwid_plus S PDWI in
let times := A_pdwid_times S PDWI in                                                 
let lte   := brel_lte_left eq plus in      
let PSP   := A_pdwid_times_proofs S PDWI in
let PSR   := A_pdwid_proofs S PDWI in
let tcong := A_msg_congruence S eq times PSP in
let commP := A_sg_CI_commutative S eq plus (A_pdwid_plus_proofs S PDWI) in                                                            
let annP := bops_id_equals_ann_to_exists_ann S eq times plus 
              (A_add_ann_mul_id_times_id_is_plus_ann S eq plus times (A_pdwid_id_ann_proofs S PDWI)) in 
let id_d :=  A_add_ann_mul_id_plus_id_d S eq plus times (A_pdwid_id_ann_proofs S PDWI) in 
{|     
  A_mposg_eqv          := eqv
; A_mposg_lte          := lte 
; A_mposg_times        := A_pdwid_times S PDWI 
; A_mposg_lte_proofs   := po_from_sg_left_proofs S eq lte eqvP plus id_d annP (A_pdwid_plus_proofs S PDWI) 
; A_mposg_times_proofs := PSP
; A_mposg_top_bottom   := from_bs_left_top_bottom_proofs S eq eqvP plus times commP (A_pdwid_id_ann_proofs S PDWI)
; A_mposg_proofs       := os_from_bs_left_proofs S eq plus times eqvP tcong PSR
; A_mposg_ast          := Ast_mposg_from_bs (A_pdwid_ast S PDWI)  
|}.

  
End ACAS.

Section CAS.

End CAS.

Section Verify.
 
End Verify.   
*)   