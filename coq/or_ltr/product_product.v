Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.
Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.po.properties.
Require Import CAS.coq.tr.properties.
Require Import CAS.coq.tr.structures.
Require Import CAS.coq.po.structures.
Require Import CAS.coq.ot.properties.
Require Import CAS.coq.ot.structures.



Require Import CAS.coq.eqv.product.
Require Import CAS.coq.po.product. 
Require Import CAS.coq.tr.left.product. 



(* move these ... *)

Definition ltr_eqv_reflexive (L S : Type) (lte : brel S) (ltr : ltr_type L S) := 
           ∀ (l : L) (s t : S), lte s t = true → lte t s = true → lte (ltr l s) (ltr l t) = true. 

Lemma olt_strictly_monotone_implies_monotone (L S : Type) (eqL : brel L) (eqS lte : brel S) (ltr : ltr_type L S)
      (refS : brel_reflexive S eqS) (refL : brel_reflexive L eqL)
      (lteRef : brel_reflexive S lte) (lteCong : brel_congruence S eqS lte)
      (ltrCong : ltr_congruence L S eqL eqS ltr)
      (DD : (brel_antisymmetric S eqS lte) + (ltr_eqv_reflexive L S lte ltr)) :
          olt_strictly_monotone L S lte ltr -> olt_monotone L S lte ltr. 
Proof. intros SM l s t A.
       case_eq(lte t s); intro B.
          destruct DD as [anti | eqv_ref]. 
             assert (C := anti _ _ A B).  
             assert (D := ltrCong _ _ _ _ (refL l) C).
             rewrite (lteCong _ _ _ _ D (refS (ltr l t))).
             apply lteRef. 

             exact (eqv_ref l s t A B). 
             
          destruct (SM l s t A B) as [C D]. exact C. 
Defined.           



Section Theory.
  
  Variable S    : Type.
  Variable LS   : Type.
  Variable eqS  : brel S.
  Variable eqLS  : brel LS.  
  Variable wS   : S.
  Variable wLS  : LS.
  Variable lteS : brel S.
  Variable ltrS : ltr_type LS S .

  Variable refS     : brel_reflexive S eqS.       
  Variable refLS    : brel_reflexive LS eqLS.
  Variable lteRefS  : brel_reflexive S lteS.   
  Variable lteCongS : brel_congruence S eqS lteS.   
  Variable ltrCongS : ltr_congruence LS S eqLS eqS ltrS.     

  Variable T    : Type.
  Variable LT   : Type.
  Variable eqT  : brel T.
  Variable eqLT : brel LT.  
  Variable wT   : T.
  Variable wLT  : LT.
  Variable lteT : brel T.
  Variable ltrT : ltr_type LT T.
 
  Variable refT     : brel_reflexive T eqT.       
  Variable refLT    : brel_reflexive LT eqLT.
  Variable lteRefT  : brel_reflexive T lteT.   
  Variable lteCongT : brel_congruence T eqT lteT.   
  Variable ltrCongT : ltr_congruence LT T eqLT eqT ltrT.     
 


  Notation "a <*> b" := (brel_product a b) (at level 15).
  Notation "a [*] b" := (ltr_product a b) (at level 15).


  Lemma olt_product_monotone :
        olt_monotone LS S lteS ltrS -> olt_monotone LT T lteT ltrT -> 
          olt_monotone (LS * LT) (S * T)  (lteS <*> lteT) (ltrS [*] ltrT). 
  Proof.
        intros MS MT [l1 l2] [s1 t1] [s2 t2]; compute.
        case_eq(lteS s1 s2); intro A; case_eq(lteT t1 t2); intros B C; auto.  
           rewrite MS; auto.  rewrite MT; auto. 
           discriminate C. discriminate C. discriminate C. discriminate C. 
  Defined.

  Lemma olt_product_not_monotone :
        ((olt_not_monotone LS S lteS ltrS) + (olt_not_monotone LT T lteT ltrT)) -> 
          olt_not_monotone (LS * LT) (S * T)  (lteS <*> lteT) (ltrS [*] ltrT). 
  Proof. unfold olt_not_monotone.
         intros [  [  [lS [s1 s2]] [A B]  ] |  [  [lT [t1 t2]] [A B]  ]  ].
         exists((lS, wLT), ((s1, wT), (s2, wT))). compute. 
         rewrite A. rewrite (lteRefT wT); split; auto. rewrite B; auto. 
         exists((wLS, lT), ((wS, t1), (wS, t2))). compute.
         rewrite A. rewrite (lteRefS wS); split; auto. rewrite B; auto.          
         rewrite lteRefS. auto. 
  Defined.

Definition olt_product_monotone_decide
           (MS : olt_monotone_decidable LS S lteS ltrS)
           (MT : olt_monotone_decidable LT T lteT ltrT) : 
  olt_monotone_decidable (LS * LT) (S * T)  (lteS <*> lteT) (ltrS [*] ltrT) :=
match MS with
| inl mS  => match MT with
             | inl mT  => inl (olt_product_monotone mS mT)
             | inr nmT => inr (olt_product_not_monotone (inr nmT))
             end 
| inr nmS => inr (olt_product_not_monotone (inl nmS))      
end.


Lemma olt_product_increasing :
        olt_increasing LS S lteS ltrS -> olt_increasing LT T lteT ltrT -> 
        olt_increasing (LS * LT) (S * T)  (lteS <*> lteT) (ltrS [*] ltrT).
Proof. intros INCS INCT [lS lT] [s t]. compute. rewrite INCS. rewrite INCT. auto. Defined.

Lemma olt_product_not_increasing_v1 :
        olt_not_increasing LS S lteS ltrS ->
           olt_not_increasing (LS * LT) (S * T)  (lteS <*> lteT) (ltrS [*] ltrT).
Proof. intros [[l s] A]. exists ((l, wLT), (s, wT)). compute. rewrite A; auto.  Defined. 

Lemma olt_product_not_increasing_v2 :
        olt_not_increasing LT T lteT ltrT ->
           olt_not_increasing (LS * LT) (S * T)  (lteS <*> lteT) (ltrS [*] ltrT).
Proof. intros [[l t] A]. exists ((wLS, l), (wS, t)). compute. rewrite A; auto.
       case_eq(lteS wS (ltrS wLS wS)); intro B; auto. 
Defined. 

Definition olt_product_increasing_decide 
           (INC_S  : olt_increasing_decidable LS S lteS ltrS)
           (INC_T  : olt_increasing_decidable LT T lteT ltrT) : 
              olt_increasing_decidable (LS * LT) (S * T)  (lteS <*> lteT) (ltrS [*] ltrT) :=
match INC_S with
| inl incS  => match INC_T with
               | inl incT  => inl (olt_product_increasing incS incT) 
               | inr nincT => inr (olt_product_not_increasing_v2 nincT)
               end 
| inr nincS => inr (olt_product_not_increasing_v1 nincS)
end. 


Lemma olt_product_strictly_increasing_inc_sinc :
        olt_increasing LS S lteS ltrS -> olt_strictly_increasing LT T lteT ltrT -> 
          olt_strictly_increasing (LS * LT) (S * T)  (lteS <*> lteT) (ltrS [*] ltrT). 
Proof. unfold olt_strictly_increasing. unfold olt_increasing. 
       intros INC SINC [lS lT] [s t]. destruct (SINC lT t) as [A B]; auto. 
       compute. rewrite A. rewrite B. rewrite INC. 
       case_eq(lteS (ltrS lS s) s); intro C; auto.        
Defined.


Lemma olt_product_strictly_increasing_sinc_inc :
        olt_strictly_increasing LS S lteS ltrS -> olt_increasing LT T lteT ltrT -> 
          olt_strictly_increasing (LS * LT) (S * T)  (lteS <*> lteT) (ltrS [*] ltrT). 
Proof. unfold olt_strictly_increasing. unfold olt_increasing. 
       intros SINC INC [lS lT] [s t]. destruct (SINC lS s) as [A B]; auto. 
       compute. rewrite A. rewrite B. rewrite INC.  auto. 
Defined.


Lemma olt_product_strictly_increasing_sinc_sinc :
        olt_strictly_increasing LS S lteS ltrS -> olt_strictly_increasing LT T lteT ltrT -> 
          olt_strictly_increasing (LS * LT) (S * T)  (lteS <*> lteT) (ltrS [*] ltrT). 
Proof. intros SINCS SINCT [lS lT] [s t].
       destruct (SINCS lS s) as [A B]; auto. destruct (SINCT lT t) as [C D]; auto. 
       compute. rewrite A. rewrite B. rewrite C. auto. 
Defined.

Lemma olt_product_not_strictly_increasing_v1 :
        olt_not_increasing LS S lteS ltrS -> 
          olt_not_strictly_increasing (LS * LT) (S * T)  (lteS <*> lteT) (ltrS [*] ltrT). 
Proof. intros [[l s] B]. exists ((l, wLT), (s, wT)). compute. rewrite B. left; auto. Defined. 


Lemma olt_product_not_strictly_increasing_v2 :
        olt_not_increasing LT T lteT ltrT -> 
          olt_not_strictly_increasing (LS * LT) (S * T)  (lteS <*> lteT) (ltrS [*] ltrT). 
Proof. intros [[l t] B]. exists ((wLS, l), (wS, t)). compute. rewrite B.
       left. case_eq(lteS wS (ltrS wLS wS)); intro C; auto.
Defined.


Lemma olt_product_not_strictly_increasing_v3 : 
        olt_not_strictly_increasing LS S lteS ltrS -> olt_not_strictly_increasing LT T lteT ltrT -> 
          olt_not_strictly_increasing (LS * LT) (S * T)  (lteS <*> lteT) (ltrS [*] ltrT). 
Proof. intros [[lS s] [A | A]] [[lT t] [B | B]]; exists ((lS, lT), (s, t)); compute. 
       rewrite A. left; auto. 
       rewrite A. left; auto. 
       rewrite B. left. case_eq(lteS s (ltrS lS s)); intro C; auto. 
       rewrite B. rewrite A. right. auto. 
Defined.

Definition olt_product_strictly_increasing_decide 
           (INC_S  : olt_increasing_decidable LS S lteS ltrS)
           (INC_T  : olt_increasing_decidable LT T lteT ltrT)
           (SINC_S : olt_strictly_increasing_decidable LS S lteS ltrS)
           (SINC_T : olt_strictly_increasing_decidable LT T lteT ltrT) : 
              olt_strictly_increasing_decidable (LS * LT) (S * T)  (lteS <*> lteT) (ltrS [*] ltrT) :=
match INC_S with
| inl incS  => match INC_T with
               | inl incT  => match SINC_S with
                              | inl sincS  => inl (olt_product_strictly_increasing_sinc_inc sincS incT) 
                              | inr nsincS => match SINC_T with
                                              | inl sincT  => inl (olt_product_strictly_increasing_inc_sinc incS sincT) 
                                              | inr nsincT => inr (olt_product_not_strictly_increasing_v3 nsincS nsincT) 
                                              end 
                              end 
               | inr nincT => inr (olt_product_not_strictly_increasing_v2 nincT)
               end 
| inr nincS => inr (olt_product_not_strictly_increasing_v1 nincS)
end.
          
Lemma olt_product_strictly_monotone
      (DDS : (brel_antisymmetric S eqS lteS) + (ltr_eqv_reflexive LS S lteS ltrS))
      (DDT : (brel_antisymmetric T eqT lteT) + (ltr_eqv_reflexive LT T lteT ltrT)):   
          olt_strictly_monotone LS S lteS ltrS -> 
          olt_strictly_monotone LT T lteT ltrT -> 
             olt_strictly_monotone (LS * LT) (S * T)  (lteS <*> lteT) (ltrS [*] ltrT). 
Proof. intros SMS SMT [lS lT] [s1 t1] [s2 t2].
       assert (MS := olt_strictly_monotone_implies_monotone LS S eqLS eqS lteS ltrS refS refLS lteRefS lteCongS ltrCongS DDS SMS).
       assert (MT := olt_strictly_monotone_implies_monotone LT T eqLT eqT lteT ltrT refT refLT lteRefT lteCongT ltrCongT DDT SMT).       
       compute. intros A B.
       case_eq(lteS s1 s2); intro C; case_eq(lteS s2 s1); intro D; rewrite C in A; rewrite D in B. 
           
           destruct (SMT lT _ _ A B) as [E F]. rewrite E. rewrite F. 
           split. 
              case_eq(lteS (ltrS lS s1) (ltrS lS s2)); intro G; auto.
                 assert (H := MS lS _ _ C).
                 rewrite H in G. discriminate G. 
              case_eq(lteS (ltrS lS s2) (ltrS lS s1)); intro G; auto. 

           destruct (SMS lS s1 s2 C D) as [E F]. rewrite E, F. 
           rewrite (MT lT _ _ A). auto. 
              
           discriminate A. 
           discriminate A. 
Defined. 


Lemma olt_product_not_strictly_monotone_v1 :
          olt_not_strictly_monotone LS S lteS ltrS -> 
             olt_not_strictly_monotone (LS * LT) (S * T)  (lteS <*> lteT) (ltrS [*] ltrT). 
Proof. intros [[l [s1 s2]] [[A B] [C | C]]]. 
       exists ((l, wLT), ((s1, wT), (s2, wT))). compute. 
       rewrite A, B, C. rewrite lteRefT. auto. 

       exists ((l, wLT), ((s1, wT), (s2, wT))). compute. 
       rewrite A, B, C. rewrite lteRefT. split; auto. 
Defined. 

Lemma olt_product_not_strictly_monotone_v2 :
          olt_not_strictly_monotone LT T lteT ltrT -> 
             olt_not_strictly_monotone (LS * LT) (S * T)  (lteS <*> lteT) (ltrS [*] ltrT). 
Proof. intros [[l [t1 t2]] [[A B] [C | C]]]. 
       exists ((wLS, l), ((wS, t1), (wS, t2))). compute. 
       rewrite A, B, C. rewrite lteRefS. rewrite lteRefS. auto. 

       exists ((wLS, l), ((wS, t1), (wS, t2))). compute. 
       rewrite A, B, C. rewrite lteRefS. rewrite lteRefS. auto. 
Defined. 

Definition olt_product_strictly_monotone_decide 
      (DDS : (brel_antisymmetric S eqS lteS) + (ltr_eqv_reflexive LS S lteS ltrS))
      (DDT : (brel_antisymmetric T eqT lteT) + (ltr_eqv_reflexive LT T lteT ltrT))
      (SMS : olt_strictly_monotone_decidable LS S lteS ltrS) 
      (SMT : olt_strictly_monotone_decidable LT T lteT ltrT) : 
             olt_strictly_monotone_decidable (LS * LT) (S * T)  (lteS <*> lteT) (ltrS [*] ltrT) := 
match SMS with
| inl smS  => match SMT with
              | inl smT  => inl (olt_product_strictly_monotone DDS DDT smS smT)
              | inr nsmT => inr (olt_product_not_strictly_monotone_v2 nsmT)    
              end 
| inr nsmS => inr (olt_product_not_strictly_monotone_v1 nsmS)    
end.


(*********** bottom/top vs ??? *******************) 




End Theory.

Section ACAS.


Definition poltr_product_oleft_transform_proofs (LS S LT T: Type) (wLS : LS) (wS : S) (wLT : LT) (wT : T) 
           (eqS lteS : brel S) (eqvS : eqv_proofs S eqS) (POS : po_proofs S eqS lteS)
           (eqLS : brel LS) (eqvLS : eqv_proofs LS eqLS)
           (ltrS : ltr_type LS S) (LTS : left_transform_proofs LS S eqS eqLS ltrS) 
           (eqT lteT : brel T) (eqvT : eqv_proofs T eqT) (POT : po_proofs T eqT lteT)
           (eqLT : brel LT) (eqvLT : eqv_proofs LT eqLT)           
           (ltrT : ltr_type LT T) (LTT : left_transform_proofs LT T eqT eqLT ltrT) 
           (PS : oltr_proofs LS S lteS ltrS)
           (PT : oltr_proofs LT T lteT ltrT) :
  oltr_proofs (LS * LT) (S * T) (brel_product lteS lteT) (ltr_product ltrS ltrT) :=

let refS     := A_eqv_reflexive S eqS eqvS in 
let refLS    := A_eqv_reflexive LS eqLS eqvLS in 
let lteRefS  := A_po_reflexive S eqS lteS POS in
let lteCongS := A_po_congruence S eqS lteS POS in
let ltrCongS := A_left_transform_congruence LS S eqS eqLS ltrS LTS in
let antiS    := A_po_antisymmetric S eqS lteS POS in

let refT     := A_eqv_reflexive T eqT eqvT in 
let refLT    := A_eqv_reflexive LT eqLT eqvLT in 
let lteRefT  := A_po_reflexive T eqT lteT POT in
let lteCongT := A_po_congruence T eqT lteT POT in
let ltrCongT := A_left_transform_congruence LT T eqT eqLT ltrT LTT in 
let antiT    := A_po_antisymmetric T eqT lteT POT in
{|
  A_poltr_monotone_d             := olt_product_monotone_decide S LS wS wLS lteS ltrS lteRefS T LT wT wLT lteT ltrT lteRefT
                                                                (A_poltr_monotone_d LS S lteS ltrS PS)
                                                                (A_poltr_monotone_d LT T lteT ltrT PT)
; A_poltr_strictly_monotone_d    := olt_product_strictly_monotone_decide S LS eqS eqLS wS wLS lteS ltrS refS refLS
                                                                           lteRefS lteCongS ltrCongS T LT eqT eqLT wT
                                                                           wLT lteT ltrT refT refLT lteRefT lteCongT ltrCongT
                                                                           (inl antiS) (inl antiT)
                                                                           (A_poltr_strictly_monotone_d LS S lteS ltrS PS)
                                                                           (A_poltr_strictly_monotone_d LT T lteT ltrT PT)
; A_poltr_increasing_d           := olt_product_increasing_decide S LS wS wLS lteS ltrS T LT wT wLT lteT ltrT
                                                                (A_poltr_increasing_d LS S lteS ltrS PS)
                                                                (A_poltr_increasing_d LT T lteT ltrT PT)    
; A_poltr_strictly_increasing_d  := olt_product_strictly_increasing_decide S LS wS wLS lteS ltrS T LT wT wLT lteT ltrT
                                                                (A_poltr_increasing_d LS S lteS ltrS PS)
                                                                (A_poltr_increasing_d LT T lteT ltrT PT)
                                                                (A_poltr_strictly_increasing_d LS S lteS ltrS PS)
                                                                (A_poltr_strictly_increasing_d LT T lteT ltrT PT)                                           
|}.

(*
Definition poltr_product_top_bottom_proofs (S T : Type) (eqS lteS : brel S) (eqT lteT : brel T) (eqvP : eqv_proofs S eqS)
    (lteReflS : brel_reflexive S lteS) (lteReflT : brel_reflexive T lteT) 
    (PS : top_bottom_proofs S eqS lteS)  (PT : top_bottom_proofs T eqT lteT) := 
let refS   := A_eqv_reflexive S eqS eqvP in
let topS_d := A_top_bottom_exists_top_d _ _ _ PS in
let topT_d := A_top_bottom_exists_top_d _ _ _ PT in                                    
let botS_d := A_top_bottom_exists_bottom_d _ _ _ PS in
let botT_d := A_top_bottom_exists_bottom_d _ _ _ PT in                                  
{|
  A_top_bottom_exists_top_d       := ord_product_exists_qo_top_decide S T eqS eqT lteS lteT lteReflS lteReflT refS topS_d topT_d 
; A_top_bottom_exists_bottom_d    := ord_product_exists_qo_bottom_decide S T eqS eqT lteS lteT lteReflS lteReflT refS botS_d botT_d 
|}.



Definition A_poltr_product (LS S LT T: Type) (AS : A_poltr LS S) (AT : A_poltr LT T) :=
let ES   := A_poltr_carrier LS S AS in
let ESP   := A_eqv_proofs S ES in   
let eqS  := A_eqv_eq _ ES in
let refS := A_eqv_reflexive _ _ ESP in 
let wS   := A_eqv_witness _ ES in 
let ELS  := A_poltr_label LS S AS in
let ELSP   := A_eqv_proofs _ ELS in   
let eqLS := A_eqv_eq _ ELS in
let wLS  := A_eqv_witness _ ELS in 

let lteS := A_poltr_lte LS S AS in

let ltrS := A_poltr_ltr LS S AS in 

let ET   := A_poltr_carrier LT T AT in
let ETP   := A_eqv_proofs _ ET in   
let eqT  := A_eqv_eq _ ET in
let refT := A_eqv_reflexive _ _ ETP in 
let wT   := A_eqv_witness _ ET in 
let ELT  := A_poltr_label LT T AT in
let ELTP   := A_eqv_proofs _ ELT in   
let eqLT := A_eqv_eq _ ELT in
let wLT  := A_eqv_witness _ ELT in 

let lteT := A_poltr_lte LT T AT in

let ltrT := A_poltr_ltr LT T AT in 

let POS := A_poltr_lte_proofs LS S AS in
let lteReflS := A_po_reflexive _ _ _ POS in
let POT := A_poltr_lte_proofs LT T AT in  
let lteReflT := A_po_reflexive _ _ _ POT in

let LTS := A_poltr_left_transform_proofs LS S AS in
let LTT := A_poltr_left_transform_proofs LT T AT in 
{|
  A_poltr_carrier      := A_eqv_product S T (A_poltr_carrier LS S AS) (A_poltr_carrier LT T AT)
; A_poltr_label        := A_eqv_product LS LT (A_poltr_label LS S AS) (A_poltr_label LT T AT)
; A_poltr_lte          := brel_product lteS lteT 
; A_poltr_ltr          := ltr_product ltrS ltrT 
; A_poltr_lte_proofs   := po_product_proofs S T eqS lteS wS POS eqT lteT wT POT 
; A_poltr_left_transform_proofs   := ltr_product_proofs LS S LT T eqS eqLS wS wLS ltrS refS LTS eqT eqLT wT wLT ltrT refT LTT 
; A_poltr_top_bottom_proofs := poltr_product_top_bottom_proofs S T eqS lteS eqT lteT ESP lteReflS lteReflT
                            (A_poltr_top_bottom_proofs LS S AS) (A_poltr_top_bottom_proofs LT T AT) 
; A_poleft_transform_proofs       := poltr_product_oleft_transform_proofs LS S LT T wLS wS wLT wT
                            eqS lteS ESP POS eqLS ELSP ltrS LTS
                            eqT lteT ETP POT eqLT ELTP ltrT LTT                                                    
                            (A_poleft_transform_proofs LS S AS) (A_poleft_transform_proofs LT T AT)
; A_poltr_ast          := Ast_lotr_product (A_poltr_ast LS S AS, A_poltr_ast LT T AT) 
|}.




  (* THINK ABOUT THESE HACKS *) 

Definition olt_product_qoltr_msi_proofs (LS S LT T : Type) (lteS : brel S) (ltrS : ltr_type LS S) (PS : poltr_mi_proofs LS S lteS ltrS)
           (lteT : brel T) (ltrT : ltr_type LT T) (PT : qoltr_msi_proofs LT T lteT ltrT) :
           qoltr_msi_proofs (LS * LT) (S * T) (brel_product lteS lteT) (ltr_product ltrS ltrT) :=
let MS := A_poltr_mi_monotone LS S lteS ltrS PS in
let MT := A_qoltr_msi_monotone LT T lteT ltrT PT in   
let INCS := A_poltr_mi_increasing LS S lteS ltrS PS in   
let SINCT := A_qoltr_msi_strictly_increasing LT T lteT ltrT PT in   
{|
  A_qoltr_msi_monotone             := olt_product_monotone S LS lteS ltrS T LT lteT ltrT MS MT 
; A_qoltr_msi_strictly_increasing  := olt_product_strictly_increasing_inc_sinc S LS lteS ltrS T LT lteT ltrT INCS SINCT
|}.




Definition olt_product_with_bottom_proofs (S T : Type) (eqS lteS : brel S) (eqT lteT : brel T) (eqvP : eqv_proofs S eqS)
    (lteReflS : brel_reflexive S lteS) (lteReflT : brel_reflexive T lteT) 
    (PS : with_bottom_proofs S eqS lteS)  (PT : with_bottom_proofs T eqT lteT) := 
let refS   := A_eqv_reflexive S eqS eqvP in
let topS_d := A_with_bottom_exists_top_d _ _ _ PS in
let topT_d := A_with_bottom_exists_top_d _ _ _ PT in                                    
let botS   := A_with_bottom_exists _ _ _ PS in
let botT   := A_with_bottom_exists _ _ _ PT in                                  
{|
  A_with_bottom_exists_top_d       := ord_product_exists_qo_top_decide S T eqS eqT lteS lteT lteReflS lteReflT refS topS_d topT_d 
; A_with_bottom_exists             := ord_product_exists_qo_bottom S T eqS eqT lteS lteT botS botT 
|}.


Definition A_product_qoltr_monotone_strictly_increasing (LS S LT T : Type) 
    (P : A_poltr_monotone_increasing LS S) 
    (Q : A_woltr_monotone_strictly_increasing LT T) :
         A_qoltr_monotone_strictly_increasing (LS * LT) (S * T) :=
let eqvS := A_poltr_mi_carrier _ _ P in
let eqS := A_eqv_eq _ eqvS in
let eqvPS := A_eqv_proofs _ eqvS in
let refS := A_eqv_reflexive _ _ eqvPS in 
let eqvLS := A_poltr_mi_label _ _ P in
let eqLS := A_eqv_eq _ eqvLS in
let wS := A_eqv_witness _ eqvS in
let wLS := A_eqv_witness _ eqvLS in 
let lteS := A_poltr_mi_lte _ _ P in  
let ltrS := A_poltr_mi_ltr _ _ P in  
let POS := A_poltr_mi_lte_proofs _ _ P in
let lteReflS := A_po_reflexive _ _ _ POS in 
let PTS := A_poltr_mi_left_transform_proofs _ _ P in
let PS := A_poltr_mi_proofs _ _ P in

let eqvT := A_woltr_msi_carrier _ _ Q in
let eqT := A_eqv_eq _ eqvT in
let eqvPT := A_eqv_proofs _ eqvT in
let refT := A_eqv_reflexive _ _ eqvPT in 
let eqvLT := A_woltr_msi_label _ _ Q in
let eqLT := A_eqv_eq _ eqvLT in
let wT := A_eqv_witness _ eqvT in
let wLT := A_eqv_witness _ eqvLT in 
let lteT := A_woltr_msi_lte _ _ Q in  
let ltrT := A_woltr_msi_ltr _ _ Q in  
let POT := A_woltr_msi_lte_proofs _ _ Q in
let lteReflT := A_wo_reflexive _ _ _ POT in 
let PTT := A_woltr_msi_left_transform_proofs _ _ Q in
let PT := A_woltr_msi_proofs _ _ Q in
{|
  A_qoltr_msi_carrier      := A_eqv_product S T eqvS eqvT
; A_qoltr_msi_label        := A_eqv_product LS LT eqvLS eqvLT
; A_qoltr_msi_lte          := brel_product lteS lteT
; A_qoltr_msi_ltr          := ltr_product ltrS ltrT
; A_qoltr_msi_lte_proofs   := ord_po_wo_product_proofs S T eqS lteS wS POS eqT lteT wT POT
; A_qoltr_msi_left_transform_proofs   := ltr_product_proofs LS S LT T eqS eqLS wS wLS ltrS refS PTS eqT eqLT wT wLT ltrT refT PTT
; A_qoltr_msi_bottom_proofs := olt_product_with_bottom_proofs S T eqS lteS eqT lteT eqvPS lteReflS lteReflT
                                (A_poltr_mi_bottom_proofs _ _ P) (A_woltr_msi_bottom_proofs _ _ Q) 
; A_qoltr_msi_proofs       := olt_product_qoltr_msi_proofs LS S LT T lteS ltrS PS lteT ltrT PT 
; A_qoltr_msi_ast          := Ast_lotr_product (A_poltr_mi_ast _ _ P, A_woltr_msi_ast _ _ Q)
|}.
*)  
End ACAS.

Section CAS.

  
(* move some of this to po/product .... *) 
Definition olt_product_qoltr_msi_certs {LS S LT T : Type} (PS : @poltr_mi_certificates LS S) (PT : @qoltr_msi_certificates LT T) :=
{|
  qoltr_msi_monotone             := @Assert_Olt_Monotone (LS * LT) (S * T)
; qoltr_msi_strictly_increasing  := @Assert_Olt_Strictly_Increasing (LS * LT) (S * T)
|}.


Definition ord_product_exists_top_check {S T : Type}
     (DS : @certify_exists_qo_top S)
     (DT : @certify_exists_qo_top T) : 
           @certify_exists_qo_top (S * T) := 
match DS with 
| Certify_Exists_Qo_Top topS   =>
               match DT with
               |  Certify_Exists_Qo_Top topT => Certify_Exists_Qo_Top (topS, topT) 
               |  Certify_Not_Exists_Qo_Top => Certify_Not_Exists_Qo_Top 
               end 
| Certify_Not_Exists_Qo_Top => Certify_Not_Exists_Qo_Top 
end.


Definition ord_product_exists_bottom_assert {S T : Type}
     (DS : @assert_exists_qo_bottom S)
     (DT : @assert_exists_qo_bottom T) : 
           @assert_exists_qo_bottom (S * T) := 
match DS, DT with 
| Assert_Exists_Qo_Bottom botS, Assert_Exists_Qo_Bottom botT =>  
     Assert_Exists_Qo_Bottom (botS, botT)
end.

Definition olt_product_with_bottom_certs {S T : Type} 
    (PS : @with_bottom_certs S)  (PT : @with_bottom_certs T) := 
let topS_d := with_bottom_exists_top_d PS in
let topT_d := with_bottom_exists_top_d PT in                                    
let botS   := with_bottom_exists PS in
let botT   := with_bottom_exists PT in                                  
{|
  with_bottom_exists_top_d       := ord_product_exists_top_check topS_d topT_d 
; with_bottom_exists             := ord_product_exists_bottom_assert botS botT 
|}.


(*
Definition product_qoltr_monotone_strictly_increasing {LS S LT T : Type}
    (P : @poltr_monotone_increasing LS S) 
    (Q : @woltr_monotone_strictly_increasing LT T) :
         @qoltr_monotone_strictly_increasing (LS * LT) (S * T) :=
let eqvS := poltr_mi_carrier P in
let eqvLS := poltr_mi_label P in
let wS := eqv_witness eqvS in
let lteS := poltr_mi_lte P in  
let ltrS := poltr_mi_ltr P in  
let wLS := eqv_witness eqvLS in 
let POS := poltr_mi_lte_certs P in
let PTS := poltr_mi_ltr_certs P in
let PS := poltr_mi_certs P in

let eqvT := woltr_msi_carrier Q in
let eqvLT := woltr_msi_label Q in
let wT := eqv_witness eqvT in
let wLT := eqv_witness eqvLT in
let lteT := woltr_msi_lte Q in  
let ltrT := woltr_msi_ltr Q in  
let POT := woltr_msi_lte_certs Q in
let PTT := woltr_msi_ltr_certs Q in
let PT := woltr_msi_certs Q in
{|
  qoltr_msi_carrier     := eqv_product eqvS eqvT
; qoltr_msi_label       := eqv_product eqvLS eqvLT
; qoltr_msi_lte         := brel_product lteS lteT
; qoltr_msi_ltr         := ltr_product ltrS ltrT
; qoltr_msi_lte_certs   := ord_po_wo_product_certs wS POS wT POT
; qoltr_msi_ltr_certs   := ltr_product_certs wS wLS PTS wT wLT PTT
; qoltr_msi_bottom_certs := olt_product_with_bottom_certs (poltr_mi_bottom_certs P) (woltr_msi_bottom_certs Q)                                              
; qoltr_msi_certs       := olt_product_qoltr_msi_certs PS PT 
; qoltr_msi_ast         := Ast_lotr_product (poltr_mi_ast P, woltr_msi_ast Q) (* FIX *)
|}.

*) 
End CAS.

(*
Section Verify.


Lemma correct_olt_product_qoltr_msi_proofs (LS S LT T : Type)
            (lteS : brel S) (ltrS : ltr_type LS S) (PS : poltr_mi_proofs LS S lteS ltrS)
            (lteT : brel T) (ltrT : ltr_type LT T) (PT : qoltr_msi_proofs LT T lteT ltrT) :
   olt_product_qoltr_msi_certs (P2C_poltr_mi LS S lteS ltrS PS) (P2C_qoltr_msi LT T lteT ltrT PT)
   =
   P2C_qoltr_msi _ _ _ _ (olt_product_qoltr_msi_proofs LS S LT T lteS ltrS PS lteT ltrT PT).
Proof. unfold olt_product_qoltr_msi_certs, olt_product_qoltr_msi_proofs, P2C_qoltr_msi, P2C_poltr_mi; simpl.
       reflexivity. 
Qed. 


Lemma correct_olt_product_with_bottom_certs (S T : Type) (eqS lteS : brel S) (eqT lteT : brel T) (eqvP : eqv_proofs S eqS)
       (lteReflS : brel_reflexive S lteS) (lteReflT : brel_reflexive T lteT) 
       (PS : with_bottom_proofs S eqS lteS)  (PT : with_bottom_proofs T eqT lteT): 

  olt_product_with_bottom_certs (P2C_with_bottom S eqS lteS PS) (P2C_with_bottom T eqT lteT PT)
  =     
  P2C_with_bottom _ _ _ (olt_product_with_bottom_proofs S T eqS lteS eqT lteT eqvP lteReflS lteReflT PS PT). 
Proof. unfold olt_product_with_bottom_certs, olt_product_with_bottom_proofs, P2C_with_bottom; simpl. 
       destruct PS, PT.
       destruct A_with_bottom_exists_top_d as [[tS [A1 A2]] | NTS];
       destruct A_with_bottom_exists_top_d0 as [[tT [B1 B2]] | NTT];       
       destruct A_with_bottom_exists as [bS [C1 C2]]; 
       destruct A_with_bottom_exists0 as [bT [D1 D2]];                
       unfold ord_product_exists_top_check, p2c_exists_qo_top_check; simpl; auto. 
Qed.

Theorem correct_product_qoltr_monotone_strictly_increasing (LS S LT T : Type) 
    (P : A_poltr_monotone_increasing LS S) 
    (Q : A_woltr_monotone_strictly_increasing LT T) :
  product_qoltr_monotone_strictly_increasing (A2C_poltr_monotone_increasing _ _ P) (A2C_woltr_monotone_strictly_increasing _ _ Q)
  =
  A2C_qoltr_monotone_strictly_increasing _ _ (A_product_qoltr_monotone_strictly_increasing _ _ _ _ P Q). 
Proof. unfold product_qoltr_monotone_strictly_increasing, A_product_qoltr_monotone_strictly_increasing,
       A2C_qoltr_monotone_strictly_increasing, A2C_poltr_monotone_increasing, A2C_woltr_monotone_strictly_increasing; simpl. 
       destruct P. destruct Q. simpl.
       rewrite correct_eqv_product. rewrite correct_eqv_product. 
       rewrite <- correct_ord_po_wo_product_certs. 
       rewrite <- correct_ltr_product_certs. 
       unfold olt_product_qoltr_msi_proofs, olt_product_qoltr_msi_certs, P2C_qoltr_msi; simpl.
       rewrite <- correct_olt_product_with_bottom_certs. 
       reflexivity. 
Qed.





End Verify.   
*) 
