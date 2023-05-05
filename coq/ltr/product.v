Require Import Coq.Strings.String.
Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.
Require Import CAS.coq.eqv.product.
Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.ltr.properties.
Require Import CAS.coq.ltr.structures.
Require Import CAS.coq.ltr.classify.
Require Import CAS.coq.ltr.cast. 
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Open Scope string_scope.
Import ListNotations.


Definition ltr_product_op :
   ∀ {LS S LT T: Type}, ltr_type LS S → ltr_type LT T → ltr_type (LS * LT) (S * T)
   := λ {LS S LT T} ltrS ltrT x y,  
     match x, y with
     | (x1, x2), (y1, y2) => (ltrS x1 y1, ltrT x2 y2) 
     end.

Section Theory.
  
Variable LS S : Type.  
Variable LT T : Type.
Variable eqS : brel S.
Variable eqLS : brel LS.
Variable wS : S.
Variable wLS : LS.
Variable ltrS : ltr_type LS S.
Variable eqT : brel T.
Variable eqLT : brel LT.
Variable wT : T.
Variable wLT : LT.
Variable ltrT : ltr_type LT T.

Variable refS : brel_reflexive S eqS.
Variable refT : brel_reflexive T eqT. 

Notation "a <*> b" := (brel_product a b) (at level 15).
Notation "a [*] b" := (ltr_product_op a b) (at level 15).


Lemma ltr_product_congruence
      (CS : A_ltr_congruence eqLS eqS ltrS)      
      (CT : A_ltr_congruence eqLT eqT ltrT) : 
   A_ltr_congruence (eqLS <*> eqLT) (eqS <*> eqT)  (ltrS [*] ltrT).     
Proof. intros [s1 t1] [s2 t2] [s3 t3] [s4 t4]. intros A B.
       apply brel_product_elim in A. destruct A as [A1 A2].
       apply brel_product_elim in B. destruct B as [B1 B2].
       apply brel_product_intro; auto. 
Qed. 

Lemma ltr_product_is_right
  (RS : A_ltr_is_right eqS ltrS)      
  (RT : A_ltr_is_right eqT ltrT) : 
      A_ltr_is_right (eqS <*> eqT)  (ltrS [*] ltrT).     
Proof. intros [lS lT] [s t]. apply brel_product_intro; auto. Qed. 

Lemma ltr_product_not_is_right_left
  (NRS : A_ltr_not_is_right eqS ltrS) :
  A_ltr_not_is_right (eqS <*> eqT)  (ltrS [*] ltrT).     
Proof. destruct NRS as [[l s] A].
       exists ((l, wLT), (s, wT)). compute. rewrite A; auto.
Defined. 

Lemma ltr_product_not_is_right_right
  (NRT : A_ltr_not_is_right eqT ltrT) :
  A_ltr_not_is_right (eqS <*> eqT)  (ltrS [*] ltrT).     
Proof. destruct NRT as [[l t] A].
       exists ((wLS, l), (wS, t)). compute. rewrite A; auto.
       case_eq(eqS (ltrS wLS wS) wS); intro B; auto. 
Defined. 

Definition A_ltr_product_is_right_decidable 
      (DS : A_ltr_is_right_decidable eqS ltrS)      
      (DT : A_ltr_is_right_decidable eqT ltrT) : 
   A_ltr_is_right_decidable (eqS <*> eqT)  (ltrS [*] ltrT) := 
match DS with 
| inl RS => match DT with
            | inl RT => inl (ltr_product_is_right RS RT)
            | inr NRT => inr (ltr_product_not_is_right_right NRT)
            end 
| inr NRS => inr (ltr_product_not_is_right_left NRS)
end. 

Lemma ltr_product_cancellative
      (RS : A_ltr_cancellative eqS ltrS)      
      (RT : A_ltr_cancellative eqT ltrT) : 
   A_ltr_cancellative (eqS <*> eqT)  (ltrS [*] ltrT).     
Proof. intros [lS lT] [s1 t1] [s2 t2] A.
       apply brel_product_elim in A.
       destruct A as [A B].
       apply brel_product_intro; auto.
       - apply (RS _ _ _ A).
       - apply (RT _ _ _ B).
Qed.        

Lemma ltr_product_not_cancellative_left
  (NRS : A_ltr_not_cancellative eqS ltrS) :
  A_ltr_not_cancellative (eqS <*> eqT)  (ltrS [*] ltrT).     
Proof. destruct NRS as [[l [s1 s2]] [A B]].
       exists ((l, wLT), ((s1, wT), (s2, wT))). split.
       - apply brel_product_intro; auto. 
       - compute. rewrite B; auto. 
Defined.        

Lemma ltr_product_not_cancellative_right
      (NRT : A_ltr_not_cancellative eqT ltrT) :
   A_ltr_not_cancellative (eqS <*> eqT)  (ltrS [*] ltrT).     
Proof. destruct NRT as [[l [t1 t2]] [A B]].
       exists ((wLS, l), ((wS, t1), (wS, t2))). split. 
       - apply brel_product_intro; auto.
       - compute. rewrite refS, B; auto. 
Defined.        

Definition A_ltr_product_cancellative_decidable 
  (DS : A_ltr_cancellative_decidable eqS ltrS)      
  (DT : A_ltr_cancellative_decidable eqT ltrT) : 
  A_ltr_cancellative_decidable (eqS <*> eqT)  (ltrS [*] ltrT) := 
match DS with 
| inl RS => match DT with
            | inl RT => inl (ltr_product_cancellative RS RT)
            | inr NRT => inr (ltr_product_not_cancellative_right NRT)
            end 
| inr NRS => inr (ltr_product_not_cancellative_left NRS)
end.


Lemma ltr_product_constant
      (RS : A_ltr_constant eqS ltrS)      
      (RT : A_ltr_constant eqT ltrT) : 
   A_ltr_constant (eqS <*> eqT)  (ltrS [*] ltrT).     
Proof. intros [lS lT] [s1 t1] [s2 t2]. compute.
       rewrite (RS lS s1 s2). rewrite (RT lT t1 t2). reflexivity. 
Qed.        

Lemma ltr_product_not_constant_left
      (NRS : A_ltr_not_constant eqS ltrS) :
   A_ltr_not_constant (eqS <*> eqT)  (ltrS [*] ltrT).     
Proof. destruct NRS as [[l [s1 s2]] A].
       exists ((l, wLT), ((s1, wT), (s2, wT))). compute. 
       rewrite A. reflexivity. 
Defined.        

Lemma ltr_product_not_constant_right
      (NRT : A_ltr_not_constant eqT ltrT) :
   A_ltr_not_constant (eqS <*> eqT)  (ltrS [*] ltrT).     
Proof. destruct NRT as [[l [t1 t2]] A].
       exists ((wLS, l), ((wS, t1), (wS, t2))). compute. 
       rewrite A. rewrite refS. reflexivity. 
Defined.        

Definition A_ltr_product_constant_decidable
      (DS : A_ltr_constant_decidable eqS ltrS)      
      (DT : A_ltr_constant_decidable eqT ltrT) : 
   A_ltr_constant_decidable (eqS <*> eqT)  (ltrS [*] ltrT) := 
match DS with 
| inl RS => match DT with
            | inl RT => inl (ltr_product_constant RS RT)
            | inr NRT => inr (ltr_product_not_constant_right NRT)
            end 
| inr NRS => inr (ltr_product_not_constant_left NRS)
end.


Lemma ltr_product_is_id (lS : LS) (lT : LT)
  (idS : A_ltr_is_id eqS ltrS lS)
  (idT : A_ltr_is_id eqT ltrT lT) : 
  A_ltr_is_id (eqS <*> eqT)  (ltrS [*] ltrT) (lS, lT). 
Proof. intros [s t]. compute. rewrite (idS s). rewrite (idT t). reflexivity. Qed. 

Lemma ltr_product_exists_id
  (idS : A_ltr_exists_id eqS ltrS)
  (idT : A_ltr_exists_id eqT ltrT) : 
  A_ltr_exists_id (eqS <*> eqT)  (ltrS [*] ltrT). 
Proof. destruct idS as [lS PS]; destruct idT as [lT PT].
       exists (lS, lT). apply ltr_product_is_id; auto. 
Defined. 

Lemma ltr_product_not_exists_id_left
  (nidS : A_ltr_not_exists_id eqS ltrS) : 
  A_ltr_not_exists_id (eqS <*> eqT)  (ltrS [*] ltrT).
Proof. intros [lS lT]. 
       destruct (nidS lS) as [s P]. 
       exists (s, wT). compute. rewrite P. reflexivity. 
Defined. 

Lemma ltr_product_not_exists_id_right
  (nidT : A_ltr_not_exists_id eqT ltrT) : 
  A_ltr_not_exists_id (eqS <*> eqT)  (ltrS [*] ltrT).
Proof. intros [lS lT]. 
       destruct (nidT lT) as [t P]. 
       exists (wS, t). compute. rewrite P.
       case_eq(eqS (ltrS lS wS) wS); intro Q; auto. 
Defined.

Definition A_ltr_product_exists_id_decidable 
      (DS : A_ltr_exists_id_decidable eqS ltrS)      
      (DT : A_ltr_exists_id_decidable eqT ltrT) : 
   A_ltr_exists_id_decidable (eqS <*> eqT)  (ltrS [*] ltrT) := 
match DS with 
| inl RS => match DT with
            | inl RT => inl (ltr_product_exists_id RS RT)
            | inr NRT => inr (ltr_product_not_exists_id_right NRT)
            end 
| inr NRS => inr (ltr_product_not_exists_id_left NRS)
end.


Lemma ltr_product_is_ann (s : S) (t : T)
  (annS : A_ltr_is_ann eqS ltrS s)
  (annT : A_ltr_is_ann eqT ltrT t) : 
  A_ltr_is_ann (eqS <*> eqT)  (ltrS [*] ltrT) (s, t). 
Proof. intros [lS lT]. compute. rewrite (annS lS). rewrite (annT lT). reflexivity. Qed. 

Lemma ltr_product_exists_ann
  (annS : A_ltr_exists_ann eqS ltrS)
  (annT : A_ltr_exists_ann eqT ltrT) : 
  A_ltr_exists_ann (eqS <*> eqT)  (ltrS [*] ltrT). 
Proof. destruct annS as [s P]; destruct annT as [t Q].
       exists (s, t). apply ltr_product_is_ann; auto. 
Defined. 

Lemma ltr_product_not_exists_ann_left
  (nannS : A_ltr_not_exists_ann eqS ltrS) : 
  A_ltr_not_exists_ann(eqS <*> eqT)  (ltrS [*] ltrT).
Proof. intros [s t]. destruct (nannS s) as [lS P]. 
       exists (lS, wLT). compute. rewrite P. reflexivity. 
Defined. 

Lemma ltr_product_not_exists_ann_right
  (nannT : A_ltr_not_exists_ann eqT ltrT) : 
  A_ltr_not_exists_ann (eqS <*> eqT)  (ltrS [*] ltrT).
Proof. intros [s t]. destruct (nannT t) as [lT P]. 
       exists (wLS, lT). compute. rewrite P.
       case_eq(eqS (ltrS wLS s) s); intro Q; auto. 
Defined.

Definition A_ltr_product_exists_ann_decidable 
      (DS : A_ltr_exists_ann_decidable eqS ltrS)      
      (DT : A_ltr_exists_ann_decidable eqT ltrT) : 
   A_ltr_exists_ann_decidable (eqS <*> eqT)  (ltrS [*] ltrT) := 
match DS with 
| inl RS => match DT with
            | inl RT => inl (ltr_product_exists_ann RS RT)
            | inr NRT => inr (ltr_product_not_exists_ann_right NRT)
            end 
| inr NRS => inr (ltr_product_not_exists_ann_left NRS)
end.

End Theory.

Section ACAS.

Section Proofs.   
Variables
  (LS LT S T: Type)  
  (eqS : brel S) (eqLS : brel LS) (wS : S) (wLS : LS) (ltrS : ltr_type LS S) (refS : brel_reflexive S eqS)
  (eqT : brel T) (eqLT : brel LT) (wT : T) (wLT : LT) (ltrT : ltr_type LT T) (refT : brel_reflexive T eqT). 

Definition A_ltr_product_properties
       (PS : A_ltr_properties eqLS eqS ltrS)
       (PT : A_ltr_properties eqLT eqT ltrT) :
             A_ltr_properties (brel_product eqLS eqLT) (brel_product eqS eqT) (ltr_product_op ltrS ltrT) :=
{|
  A_ltr_props_congruence     :=
    ltr_product_congruence LS S LT T eqS eqLS ltrS eqT eqLT ltrT
      (A_ltr_props_congruence eqLS eqS ltrS PS)
      (A_ltr_props_congruence eqLT eqT ltrT PT) 
; A_ltr_props_is_right_d     :=
    A_ltr_product_is_right_decidable LS S LT T eqS wS wLS ltrS eqT wT wLT ltrT
      (A_ltr_props_is_right_d eqLS eqS ltrS PS)
      (A_ltr_props_is_right_d eqLT eqT ltrT PT)
; A_ltr_props_constant_d :=
    A_ltr_product_constant_decidable LS S LT T eqS wS wLS ltrS eqT wT wLT ltrT refS
      (A_ltr_props_constant_d eqLS eqS ltrS PS)
      (A_ltr_props_constant_d eqLT eqT ltrT PT)        
; A_ltr_props_cancellative_d :=
    A_ltr_product_cancellative_decidable LS S LT T eqS wS wLS ltrS eqT wT wLT ltrT refS refT
      (A_ltr_props_cancellative_d eqLS eqS ltrS PS)
      (A_ltr_props_cancellative_d eqLT eqT ltrT PT)                                                           
|}.


End Proofs.   

Section Combinators.

  Definition A_ltr_product
    {L L' S S' : Type}
    (A : @A_ltr L S)
    (B : @A_ltr L' S') : @A_ltr (L * L') (S * S') :=
  let eqvS := A_ltr_carrier A in
  let eqS := A_eqv_eq _ eqvS in
  let eqvPS := A_eqv_proofs _ eqvS in
  let refS := A_eqv_reflexive _ _ eqvPS in   
  let wS := A_eqv_witness _ eqvS in    
  let eqvS' := A_ltr_carrier B in
  let eqS' := A_eqv_eq _ eqvS' in
  let eqvPS' := A_eqv_proofs _ eqvS' in
  let refS' := A_eqv_reflexive _ _ eqvPS' in   
  let wS' := A_eqv_witness _ eqvS' in      
  let eqvL := A_ltr_label A in
  let eqL := A_eqv_eq _ eqvL in        
  let wL := A_eqv_witness _ eqvL in        
  let eqvL' := A_ltr_label B in
  let eqL' := A_eqv_eq _ eqvL' in          
  let wL' := A_eqv_witness _ eqvL' in          
  let ltrA := A_ltr_ltr A in
  let ltrB := A_ltr_ltr B in     
{|
  A_ltr_carrier      := A_eqv_product _ _ eqvS eqvS' 
; A_ltr_label        := A_eqv_product _ _ eqvL eqvL' 
; A_ltr_ltr          := ltr_product_op ltrA ltrB
; A_ltr_exists_id_d :=
    A_ltr_product_exists_id_decidable L S L' S' eqS wS ltrA eqS' wS' ltrB
      (A_ltr_exists_id_d A) (A_ltr_exists_id_d B)
; A_ltr_exists_ann_d :=
    A_ltr_product_exists_ann_decidable L S L' S' eqS wL ltrA eqS' wL' ltrB
      (A_ltr_exists_ann_d A) (A_ltr_exists_ann_d B)
; A_ltr_props       :=
    A_ltr_product_properties L L' S S' eqS eqL wS wL ltrA refS eqS' eqL' wS' wL' ltrB refS'
      (A_ltr_props A) (A_ltr_props B)
; A_ltr_ast          :=
    Cas_ast ("A_ltr_product", [A_ltr_ast A; A_ltr_ast B])
|}.

End Combinators.   

End ACAS.


Section AMCAS.


  Definition A_ltr_product_below_ltr {LS LT S T : Type}
    (A : @A_below_ltr LS S)
    (B : @A_below_ltr LT T)  : @A_below_ltr (LS * LT) (S * T) :=
    A_classify_ltr (A_ltr_product (A_cast_up_ltr A) (A_cast_up_ltr B)).

  
  Definition A_mcas_ltr_product {LS LT S T : Type}
    (A : @A_ltr_mcas LS S)
    (B : @A_ltr_mcas LT T)  : @A_ltr_mcas (LS * LT )(S * T) :=
    match A, B with
    | A_MCAS_ltr A', A_MCAS_ltr B'               => A_MCAS_ltr (A_ltr_product_below_ltr A' B')
    | A_MCAS_ltr_Error sl1, A_MCAS_ltr_Error sl2 => A_MCAS_ltr_Error (sl1 ++ sl2)
    | A_MCAS_ltr_Error sl1, _                   => A_MCAS_ltr_Error sl1
    | _,  A_MCAS_ltr_Error sl2                  => A_MCAS_ltr_Error sl2
    end.
  
End AMCAS.   

Section CAS.

  Definition ltr_product_cancellative_decidable 
    {LS LT S T : Type}
    (DS : @ltr_cancellative_decidable LS S) 
    (DT : @ltr_cancellative_decidable LT T)
    (wLS : LS) (wS : S) (wLT : LT) (wT : T) : 
  @ltr_cancellative_decidable (LS * LT) (S * T) := 
    match DS with 
    | inl (LTR_cancellative (lS, s)) =>
        match DT with
        | inl (LTR_cancellative (lT, t)) =>
            inl (LTR_cancellative ((lS, lT), (s, t)))
        | inr (LTR_not_cancellative (lT, (t1, t2))) =>
            inr (LTR_not_cancellative ((wLS, lT), ((wS, t1), (wS, t2))))
        end 
    | inr (LTR_not_cancellative (lS, (s1, s2))) =>
            inr (LTR_not_cancellative ((lS, wLT), ((s1, wT), (s2, wT))))
    end.

  Definition ltr_product_constant_decidable 
    {LS LT S T : Type}
    (DS : @ltr_constant_decidable LS S) 
    (DT : @ltr_constant_decidable LT T)
    (wLS : LS) (wS : S) (wLT : LT) (wT : T) : 
  @ltr_constant_decidable (LS * LT) (S * T) := 
    match DS with 
    | inl (LTR_constant (lS, s)) =>
        match DT with
        | inl (LTR_constant (lT, t)) =>
            inl (LTR_constant ((lS, lT), (s, t)))
        | inr (LTR_not_constant (lT, (t1, t2))) =>
            inr (LTR_not_constant ((wLS, lT), ((wS, t1), (wS, t2))))
        end 
    | inr (LTR_not_constant (lS, (s1, s2))) =>
            inr (LTR_not_constant ((lS, wLT), ((s1, wT), (s2, wT))))
    end.


  
    Definition ltr_product_is_right_decidable 
    {LS LT S T : Type}
    (DS : @ltr_is_right_decidable LS S) 
    (DT : @ltr_is_right_decidable LT T)
    (wLS : LS) (wS : S) (wLT : LT) (wT : T) : 
  @ltr_is_right_decidable (LS * LT) (S * T) := 
    match DS with 
    | inl (LTR_is_right (lS, s)) =>
        match DT with
        | inl (LTR_is_right (lT, t)) =>
            inl (LTR_is_right ((lS, lT), (s, t)))
        | inr (LTR_not_is_right (lT, t)) =>
            inr (LTR_not_is_right ((wLS, lT), (wS, t)))
        end 
    | inr (LTR_not_is_right (lS, s)) =>
            inr (LTR_not_is_right ((lS, wLT), (s, wT)))
    end.



    Definition ltr_product_exists_id_decidable 
    {LS LT : Type}
    (DS : @ltr_exists_id_decidable LS) 
    (DT : @ltr_exists_id_decidable LT)
    (wLS : LS) (wLT : LT) : 
  @ltr_exists_id_decidable (LS * LT) := 
    match DS with 
    | inl (LTR_exists_id lS) =>
        match DT with
        | inl (LTR_exists_id lT) =>
            inl (LTR_exists_id (lS, lT))
        | inr (LTR_not_exists_id _) =>
            inr (LTR_not_exists_id (wLS, wLT))
        end 
    | inr (LTR_not_exists_id _) =>
            inr (LTR_not_exists_id (wLS, wLT))
    end.


    Definition ltr_product_exists_ann_decidable 
    {S T : Type}
    (DS : @ltr_exists_ann_decidable S) 
    (DT : @ltr_exists_ann_decidable T)
    (wS : S) (wT : T) : 
  @ltr_exists_ann_decidable (S * T) := 
    match DS with 
    | inl (LTR_exists_ann s) =>
        match DT with
        | inl (LTR_exists_ann t) =>
            inl (LTR_exists_ann (s, t))
        | inr (LTR_not_exists_ann _) =>
            inr (LTR_not_exists_ann (wS, wT))
        end 
    | inr (LTR_not_exists_ann _) =>
            inr (LTR_not_exists_ann (wS, wT))
    end.

Definition ltr_product_properties {LS LT S T} 
       (PS : @ltr_properties LS S)
       (PT : @ltr_properties LT T) 
       (wLS : LS) (wS : S) (wLT : LT) (wT : T) :
           @ltr_properties (LS * LT) (S * T):= 
{|
  ltr_props_is_right_d     :=
    ltr_product_is_right_decidable 
      (ltr_props_is_right_d PS)
      (ltr_props_is_right_d PT)
      wLS wS wLT wT
; ltr_props_constant_d :=
    ltr_product_constant_decidable 
      (ltr_props_constant_d PS)
      (ltr_props_constant_d PT)
      wLS wS wLT wT       
; ltr_props_cancellative_d :=
    ltr_product_cancellative_decidable 
      (ltr_props_cancellative_d PS)
      (ltr_props_cancellative_d PT)
      wLS wS wLT wT 
|}.

 
Definition ltr_product
  {LS LT S T : Type}
  (A : @ltr LS S)
  (B : @ltr LT T) : @ltr (LS * LT) (S * T) :=
  let eqvS := ltr_carrier A in
  let wS := eqv_witness eqvS in
  let eqvT := ltr_carrier B in
  let wT := eqv_witness eqvT in      
  let eqvLS := ltr_label A in
  let wLS := eqv_witness eqvLS in        
  let eqvLT := ltr_label B in
  let wLT := eqv_witness eqvLT in          
  let ltrA := ltr_ltr A in
  let ltrB := ltr_ltr B in     
{|
  ltr_carrier      := eqv_product eqvS eqvT
; ltr_label        := eqv_product eqvLS eqvLT 
; ltr_ltr          := ltr_product_op ltrA ltrB 
; ltr_exists_id_d  := ltr_product_exists_id_decidable
                        (ltr_exists_id_d A)
                        (ltr_exists_id_d B)
                        wLS wLT 
; ltr_exists_ann_d := ltr_product_exists_ann_decidable 
                        (ltr_exists_ann_d  A)
                        (ltr_exists_ann_d B)
                        wS wT                         
; ltr_props        := ltr_product_properties
                        (ltr_props A)
                        (ltr_props B)
                        wLS wS wLT wT                         
; ltr_ast          := Cas_ast ("A_ltr_product", [ltr_ast A; ltr_ast B])
|}.


End CAS.

Section MCAS.

  Definition ltr_product_below_ltr {LS LT S T : Type}
    (A : @below_ltr LS S)
    (B : @below_ltr LT T)  : @below_ltr (LS * LT) (S * T) :=
    classify_ltr (ltr_product (cast_up_ltr A) (cast_up_ltr B)).

  
  Definition mcas_ltr_product {LS LT S T : Type}
    (A : @ltr_mcas LS S)
    (B : @ltr_mcas LT T)  : @ltr_mcas (LS * LT )(S * T) :=
    match A, B with
    | MCAS_ltr A', MCAS_ltr B'               => MCAS_ltr (ltr_product_below_ltr A' B')
    | MCAS_ltr_Error sl1, MCAS_ltr_Error sl2 => MCAS_ltr_Error (sl1 ++ sl2)
    | MCAS_ltr_Error sl1, _                   => MCAS_ltr_Error sl1
    | _,  MCAS_ltr_Error sl2                  => MCAS_ltr_Error sl2
    end.
  
  
End MCAS.   


Section Verify.

Section Proofs.   
Variables
  (LS LT S T: Type)
  (eqS : brel S) (eqLS : brel LS) (wS : S) (wLS : LS) (ltrS : ltr_type LS S) (refS : brel_reflexive S eqS)
  (eqT : brel T) (eqLT : brel LT) (wT : T) (wLT : LT) (ltrT : ltr_type LT T) (refT : brel_reflexive T eqT).


Lemma correct_ltr_product_exists_ann_decidable
      (annS_d : A_ltr_exists_ann_decidable eqS ltrS)
      (annT_d : A_ltr_exists_ann_decidable eqT ltrT):
      p2c_ltr_exists_ann_decidable
        (brel_product eqS eqT) 
        (ltr_product_op ltrS ltrT)
        (A_ltr_product_exists_ann_decidable LS S LT T                                            
           eqS wLS ltrS eqT wLT ltrT annS_d annT_d) (wS, wT)
      = 
      ltr_product_exists_ann_decidable
        (p2c_ltr_exists_ann_decidable eqS ltrS annS_d wS)
        (p2c_ltr_exists_ann_decidable eqT ltrT annT_d wT)
        wS wT. 
Proof. destruct annS_d as [ [annS annPS] | nannS ]; 
       destruct annT_d as [ [annT annPT] | nannT ]; simpl; 
       reflexivity.
Qed. 


Lemma correct_ltr_product_exists_id_decidable
      (idS_d : A_ltr_exists_id_decidable eqS ltrS)
      (idT_d : A_ltr_exists_id_decidable eqT ltrT):
      p2c_ltr_exists_id_decidable
        (brel_product eqS eqT) 
        (ltr_product_op ltrS ltrT)
        (A_ltr_product_exists_id_decidable LS S LT T                                            
           eqS wS ltrS eqT wT ltrT idS_d idT_d) (wLS, wLT)
      = 
      ltr_product_exists_id_decidable
        (p2c_ltr_exists_id_decidable eqS ltrS idS_d wLS)
        (p2c_ltr_exists_id_decidable eqT ltrT idT_d wLT)
        wLS wLT. 
Proof. destruct idS_d as [ [idS idPS] | nidS ]; 
       destruct idT_d as [ [idT idPT] | nidT ]; simpl; 
       reflexivity.
Qed. 

Lemma correct_ltr_product_is_right_decidable
      (irS_d : A_ltr_is_right_decidable eqS ltrS)
      (irT_d : A_ltr_is_right_decidable eqT ltrT):
      p2c_ltr_is_right_decidable
        (brel_product eqS eqT) 
        (ltr_product_op ltrS ltrT)
        (A_ltr_product_is_right_decidable LS S LT T                                            
           eqS wS wLS ltrS eqT wT wLT ltrT irS_d irT_d)
        (wLS, wLT) (wS, wT)
      = 
      ltr_product_is_right_decidable
        (p2c_ltr_is_right_decidable eqS ltrS irS_d wLS wS)
        (p2c_ltr_is_right_decidable eqT ltrT irT_d wLT wT)
        wLS wS wLT wT. 
Proof. unfold ltr_product_is_right_decidable, A_ltr_product_is_right_decidable,
         p2c_ltr_is_right_decidable.
       destruct irS_d as [irS | [[lS s] nirS]]; 
         destruct irT_d as [irT | [[lT t] nirT]]; simpl;
         reflexivity. 
Qed. 

Lemma correct_ltr_product_cancellative_decidable
      (cS_d : A_ltr_cancellative_decidable eqS ltrS)
      (cT_d : A_ltr_cancellative_decidable eqT ltrT):
      p2c_ltr_cancellative_decidable
        (brel_product eqS eqT) 
        (ltr_product_op ltrS ltrT)
        (A_ltr_product_cancellative_decidable LS S LT T                                            
           eqS wS wLS ltrS eqT wT wLT ltrT refS refT cS_d cT_d)
        (wLS, wLT) (wS, wT)
      = 
      ltr_product_cancellative_decidable
        (p2c_ltr_cancellative_decidable eqS ltrS cS_d wLS wS)
        (p2c_ltr_cancellative_decidable eqT ltrT cT_d wLT wT)
        wLS wS wLT wT. 
Proof. unfold ltr_product_cancellative_decidable, A_ltr_product_cancellative_decidable,
         p2c_ltr_cancellative_decidable.
       destruct cS_d as [cS | [[lS [s1 s2]] [A B]]]; 
         destruct cT_d as [cT | [[lT [t1 t2]] [C D]]]; simpl;
         try reflexivity. 
Qed.

Lemma correct_ltr_product_constant_decidable
      (cS_d : A_ltr_constant_decidable eqS ltrS)
      (cT_d : A_ltr_constant_decidable eqT ltrT):
      p2c_ltr_constant_decidable
        (brel_product eqS eqT) 
        (ltr_product_op ltrS ltrT)
        (A_ltr_product_constant_decidable LS S LT T                                            
           eqS wS wLS ltrS eqT wT wLT ltrT refS cS_d cT_d)
        (wLS, wLT) (wS, wT)
      = 
      ltr_product_constant_decidable
        (p2c_ltr_constant_decidable eqS ltrS cS_d wLS wS)
        (p2c_ltr_constant_decidable eqT ltrT cT_d wLT wT)
        wLS wS wLT wT. 
Proof. unfold ltr_product_constant_decidable, A_ltr_product_constant_decidable,
         p2c_ltr_constant_decidable.
       destruct cS_d as [cS | [[lS [s1 s2]] A]]; 
         destruct cT_d as [cT | [[lT [t1 t2]] C]]; simpl;
         try reflexivity. 
Qed. 


  Lemma correct_ltr_product_properties 
      (PS : A_ltr_properties eqLS eqS ltrS)
      (PT : A_ltr_properties eqLT eqT ltrT) :
  P2C_ltr_properties _ _ _ 
    (A_ltr_product_properties LS LT S T eqS eqLS wS wLS ltrS refS eqT eqLT wT wLT ltrT refT PS PT)
    (wLS, wLT) (wS, wT) 
  =
  ltr_product_properties
    (P2C_ltr_properties _ _ _ PS wLS wS)
    (P2C_ltr_properties _ _ _ PT wLT wT)
    wLS wS wLT wT. 
  Proof. destruct PS. destruct PT.
         unfold ltr_product_properties, A_ltr_product_properties, P2C_ltr_properties; simpl. 
         rewrite correct_ltr_product_is_right_decidable.
         rewrite correct_ltr_product_cancellative_decidable.
         rewrite correct_ltr_product_constant_decidable.         
         reflexivity. 
  Qed.

End Proofs.

Section Combinators.

  Theorem correct_ltr_product (LS LT S T : Type)
    (A : @A_ltr LS S) (B : @A_ltr LT T) : 
    A2C_ltr (A_ltr_product A B)
    =                        
    ltr_product (A2C_ltr A) (A2C_ltr B).
  Proof. unfold A2C_ltr, A_ltr_product, ltr_product. simpl.
         rewrite correct_eqv_product.
         rewrite correct_eqv_product.         
         rewrite correct_ltr_product_properties.
         rewrite correct_ltr_product_exists_id_decidable. 
         rewrite correct_ltr_product_exists_ann_decidable. 
         reflexivity. 
  Qed.

  Theorem correct_ltr_product_below_ltr (LS LT S T : Type)
    (A : @A_below_ltr LS S) (B : @A_below_ltr LT T) : 
    A2C_below_ltr (A_ltr_product_below_ltr A B)
    =
    ltr_product_below_ltr (A2C_below_ltr A) (A2C_below_ltr B). 
  Proof. unfold A_ltr_product_below_ltr, ltr_product_below_ltr,
           A2C_below_ltr; destruct A, B; simpl; try reflexivity. 
         unfold classify_ltr.
         rewrite correct_ltr_product.
         reflexivity.
  Qed.
  
  Theorem correct_mcas_ltr_product (LS LT S T : Type)
    (A : @A_ltr_mcas LS S) (B : @A_ltr_mcas LT T) : 
    A2C_mcas_ltr (A_mcas_ltr_product A B)
    =                        
    mcas_ltr_product (A2C_mcas_ltr A) (A2C_mcas_ltr B).
  Proof. unfold A_mcas_ltr_product, mcas_ltr_product, A2C_mcas_ltr; simpl.
         destruct A, B; try reflexivity.
         rewrite correct_ltr_product_below_ltr. 
         reflexivity. 
  Qed.
  
End Combinators.   

End Verify.   
  
  

