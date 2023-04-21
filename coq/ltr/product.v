Require Import Coq.Strings.String.
Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.
Require Import CAS.coq.eqv.product.
Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.tr.properties.
Require Import CAS.coq.tr.structures.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Open Scope string_scope.
Import ListNotations.


Definition ltr_product :
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
Notation "a [*] b" := (ltr_product a b) (at level 15).


Lemma ltr_product_congruence
      (CS : ltr_congruence LS S eqLS eqS ltrS)      
      (CT : ltr_congruence LT T eqLT eqT ltrT) : 
   ltr_congruence (LS * LT) (S * T) (eqLS <*> eqLT) (eqS <*> eqT)  (ltrS [*] ltrT).     
Proof. intros [s1 t1] [s2 t2] [s3 t3] [s4 t4]. compute.
       case_eq(eqLS s1 s2); intro A; case_eq(eqLT t1 t2); intro B; intro C. 
         case_eq(eqS s3 s4); intro D; case_eq(eqT t3 t4); intro E; intro F. 
            rewrite (CS _ _ _ _ A D). rewrite (CT _ _ _ _ B E). reflexivity. 
            discriminate F. discriminate F. discriminate F. 
         discriminate C. discriminate C. discriminate C. 
Qed. 

Lemma ltr_product_is_right
      (RS : ltr_is_right LS S eqS ltrS)      
      (RT : ltr_is_right LT T eqT ltrT) : 
   ltr_is_right (LS * LT) (S * T) (eqS <*> eqT)  (ltrS [*] ltrT).     
Proof. intros [lS lT] [s t]. compute. rewrite RS, RT; auto. Qed. 

Lemma ltr_product_not_is_right_left
      (NRS : ltr_not_is_right LS S eqS ltrS) :
   ltr_not_is_right (LS * LT) (S * T) (eqS <*> eqT)  (ltrS [*] ltrT).     
Proof. destruct NRS as [[l s] A]. exists ((l, wLT), (s, wT)). compute. rewrite A; auto. Defined. 

Lemma ltr_product_not_is_right_right
      (NRT : ltr_not_is_right LT T eqT ltrT) :
   ltr_not_is_right (LS * LT) (S * T) (eqS <*> eqT)  (ltrS [*] ltrT).     
Proof. destruct NRT as [[l t] A]. exists ((wLS, l), (wS, t)). compute. rewrite A; auto.
       case_eq(eqS (ltrS wLS wS) wS); intro B; auto. 
Defined. 

Definition ltr_product_is_right_decidable 
      (DS : ltr_is_right_decidable LS S eqS ltrS)      
      (DT : ltr_is_right_decidable LT T eqT ltrT) : 
   ltr_is_right_decidable (LS * LT) (S * T) (eqS <*> eqT)  (ltrS [*] ltrT) := 
match DS with 
| inl RS => match DT with
            | inl RT => inl (ltr_product_is_right RS RT)
            | inr NRT => inr (ltr_product_not_is_right_right NRT)
            end 
| inr NRS => inr (ltr_product_not_is_right_left NRS)
end. 

  

Lemma ltr_product_left_cancellative
      (RS : ltr_left_cancellative LS S eqS ltrS)      
      (RT : ltr_left_cancellative LT T eqT ltrT) : 
   ltr_left_cancellative (LS * LT) (S * T) (eqS <*> eqT)  (ltrS [*] ltrT).     
Proof. intros [lS lT] [s1 t1] [s2 t2]. compute.
       case_eq(eqS (ltrS lS s1) (ltrS lS s2)); intro A; 
       case_eq(eqT (ltrT lT t1) (ltrT lT t2)); intro B; intro C.
          apply RS in A. apply RT in B. rewrite A, B; auto. 
          discriminate C. discriminate C. discriminate C. 
Qed.        

Lemma ltr_product_not_left_cancellative_left
      (NRS : ltr_not_left_cancellative LS S eqS ltrS) :
   ltr_not_left_cancellative (LS * LT) (S * T) (eqS <*> eqT)  (ltrS [*] ltrT).     
Proof. destruct NRS as [[l [s1 s2]] [A B]]. exists ((l, wLT), ((s1, wT), (s2, wT))). compute. 
       rewrite A, B. rewrite (refT (ltrT wLT wT)); auto.
Defined.        

Lemma ltr_product_not_left_cancellative_right
      (NRT : ltr_not_left_cancellative LT T eqT ltrT) :
   ltr_not_left_cancellative (LS * LT) (S * T) (eqS <*> eqT)  (ltrS [*] ltrT).     
Proof. destruct NRT as [[l [t1 t2]] [A B]]. exists ((wLS, l), ((wS, t1), (wS, t2))). compute. 
       rewrite A, B. rewrite (refS (ltrS wLS wS)); rewrite (refS wS); auto. 
Defined.        



Definition ltr_product_left_cancellative_decide
      (DS : ltr_left_cancellative_decidable LS S eqS ltrS)      
      (DT : ltr_left_cancellative_decidable LT T eqT ltrT) : 
   ltr_left_cancellative_decidable (LS * LT) (S * T) (eqS <*> eqT)  (ltrS [*] ltrT) := 
match DS with 
| inl RS => match DT with
            | inl RT => inl (ltr_product_left_cancellative RS RT)
            | inr NRT => inr (ltr_product_not_left_cancellative_right NRT)
            end 
| inr NRS => inr (ltr_product_not_left_cancellative_left NRS)
end.


Lemma ltr_product_left_constant
      (RS : ltr_left_constant LS S eqS ltrS)      
      (RT : ltr_left_constant LT T eqT ltrT) : 
   ltr_left_constant (LS * LT) (S * T) (eqS <*> eqT)  (ltrS [*] ltrT).     
Proof. intros [lS lT] [s1 t1] [s2 t2]. compute.
       rewrite (RS lS s1 s2). rewrite (RT lT t1 t2). reflexivity. 
Qed.        

Lemma ltr_product_not_left_constant_left
      (NRS : ltr_not_left_constant LS S eqS ltrS) :
   ltr_not_left_constant (LS * LT) (S * T) (eqS <*> eqT)  (ltrS [*] ltrT).     
Proof. destruct NRS as [[l [s1 s2]] A]. exists ((l, wLT), ((s1, wT), (s2, wT))). compute. 
       rewrite A. reflexivity. 
Defined.        

Lemma ltr_product_not_left_constant_right
      (NRT : ltr_not_left_constant LT T eqT ltrT) :
   ltr_not_left_constant (LS * LT) (S * T) (eqS <*> eqT)  (ltrS [*] ltrT).     
Proof. destruct NRT as [[l [t1 t2]] A]. exists ((wLS, l), ((wS, t1), (wS, t2))). compute. 
       rewrite A. rewrite refS. reflexivity. 
Defined.        



Definition ltr_product_left_constant_decide
      (DS : ltr_left_constant_decidable LS S eqS ltrS)      
      (DT : ltr_left_constant_decidable LT T eqT ltrT) : 
   ltr_left_constant_decidable (LS * LT) (S * T) (eqS <*> eqT)  (ltrS [*] ltrT) := 
match DS with 
| inl RS => match DT with
            | inl RT => inl (ltr_product_left_constant RS RT)
            | inr NRT => inr (ltr_product_not_left_constant_right NRT)
            end 
| inr NRS => inr (ltr_product_not_left_constant_left NRS)
end.



Lemma ltr_product_is_id (lS : LS) (lT : LT) (idS : ltr_is_id LS S eqS ltrS lS) (idT : ltr_is_id LT T eqT ltrT lT) : 
  ltr_is_id (LS * LT) (S * T) (eqS <*> eqT)  (ltrS [*] ltrT) (lS, lT). 
Proof. intros [s t]. compute. rewrite (idS s). rewrite (idT t). reflexivity. Qed. 

Lemma ltr_product_exists_id (idS : ltr_exists_id LS S eqS ltrS) (idT : ltr_exists_id LT T eqT ltrT) : 
  ltr_exists_id (LS * LT) (S * T) (eqS <*> eqT)  (ltrS [*] ltrT). 
Proof. destruct idS as [lS PS]; destruct idT as [lT PT].
       exists (lS, lT). apply ltr_product_is_id; auto. 
Defined. 

Lemma ltr_product_not_exists_id_left (nidS : ltr_not_exists_id LS S eqS ltrS) : 
  ltr_not_exists_id (LS * LT) (S * T) (eqS <*> eqT)  (ltrS [*] ltrT).
Proof. unfold ltr_not_exists_id. intros [lS lT]. 
       destruct (nidS lS) as [s P]. 
       exists (s, wT). compute. rewrite P. reflexivity. 
Defined. 

Lemma ltr_product_not_exists_id_right (nidT : ltr_not_exists_id LT T eqT ltrT) : 
  ltr_not_exists_id (LS * LT) (S * T) (eqS <*> eqT)  (ltrS [*] ltrT).
Proof. unfold ltr_not_exists_id. intros [lS lT]. 
       destruct (nidT lT) as [t P]. 
       exists (wS, t). compute. rewrite P.
       case_eq(eqS (ltrS lS wS) wS); intro Q; auto. 
Defined.

Definition ltr_product_exists_id_decidable 
      (DS : ltr_exists_id_decidable LS S eqS ltrS)      
      (DT : ltr_exists_id_decidable LT T eqT ltrT) : 
   ltr_exists_id_decidable (LS * LT) (S * T) (eqS <*> eqT)  (ltrS [*] ltrT) := 
match DS with 
| inl RS => match DT with
            | inl RT => inl (ltr_product_exists_id RS RT)
            | inr NRT => inr (ltr_product_not_exists_id_right NRT)
            end 
| inr NRS => inr (ltr_product_not_exists_id_left NRS)
end.


Lemma ltr_product_is_ann (s : S) (t : T) (annS : ltr_is_ann LS S eqS ltrS s) (annT : ltr_is_ann LT T eqT ltrT t) : 
  ltr_is_ann (LS * LT) (S * T) (eqS <*> eqT)  (ltrS [*] ltrT) (s, t). 
Proof. intros [lS lT]. compute. rewrite (annS lS). rewrite (annT lT). reflexivity. Qed. 

Lemma ltr_product_exists_ann (annS : ltr_exists_ann LS S eqS ltrS) (annT : ltr_exists_ann LT T eqT ltrT) : 
  ltr_exists_ann (LS * LT) (S * T) (eqS <*> eqT)  (ltrS [*] ltrT). 
Proof. destruct annS as [s P]; destruct annT as [t Q].
       exists (s, t). apply ltr_product_is_ann; auto. 
Defined. 

Lemma ltr_product_not_exists_ann_left (nannS : ltr_not_exists_ann LS S eqS ltrS) : 
  ltr_not_exists_ann (LS * LT) (S * T) (eqS <*> eqT)  (ltrS [*] ltrT).
Proof. unfold ltr_not_exists_ann. intros [s t]. 
       destruct (nannS s) as [lS P]. 
       exists (lS, wLT). compute. rewrite P. reflexivity. 
Defined. 

Lemma ltr_product_not_exists_ann_right (nannT : ltr_not_exists_ann LT T eqT ltrT) : 
  ltr_not_exists_ann (LS * LT) (S * T) (eqS <*> eqT)  (ltrS [*] ltrT).
Proof. unfold ltr_not_exists_ann. intros [s t]. 
       destruct (nannT t) as [lT P]. 
       exists (wLS, lT). compute. rewrite P.
       case_eq(eqS (ltrS wLS s) s); intro Q; auto. 
Defined.

Definition ltr_product_exists_ann_decidable 
      (DS : ltr_exists_ann_decidable LS S eqS ltrS)      
      (DT : ltr_exists_ann_decidable LT T eqT ltrT) : 
   ltr_exists_ann_decidable (LS * LT) (S * T) (eqS <*> eqT)  (ltrS [*] ltrT) := 
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
  (LS S LT T: Type)  
  (eqS : brel S) (eqLS : brel LS) (wS : S) (wLS : LS) (ltrS : ltr_type LS S) (refS : brel_reflexive S eqS)
  (eqT : brel T) (eqLT : brel LT) (wT : T) (wLT : LT) (ltrT : ltr_type LT T) (refT : brel_reflexive T eqT). 
  
Definition ltr_product_proofs 
       (PS : left_transform_proofs LS S eqS eqLS ltrS)
       (PT : left_transform_proofs LT T eqT eqLT ltrT) :
              left_transform_proofs (LS * LT) (S * T) (brel_product eqS eqT) (brel_product eqLS eqLT) (ltr_product ltrS ltrT) :=
{|
  A_left_transform_congruence          := ltr_product_congruence LS S LT T eqS eqLS ltrS eqT eqLT ltrT
                                  (A_left_transform_congruence LS S eqS eqLS ltrS PS)
                                  (A_left_transform_congruence LT T eqT eqLT ltrT PT)                                                      
; A_left_transform_is_right_d          := ltr_product_is_right_decidable LS S LT T eqS wS wLS ltrS eqT wT wLT ltrT
                                  (A_left_transform_is_right_d LS S eqS eqLS ltrS PS)
                                  (A_left_transform_is_right_d LT T eqT eqLT ltrT PT)
; A_left_transform_left_constant_d := ltr_product_left_constant_decide LS S LT T eqS wS wLS ltrS eqT wT wLT ltrT refS 
                                  (A_left_transform_left_constant_d LS S eqS eqLS ltrS PS)
                                  (A_left_transform_left_constant_d LT T eqT eqLT ltrT PT)   
; A_left_transform_left_cancellative_d := ltr_product_left_cancellative_decide LS S LT T eqS wS wLS ltrS eqT wT wLT ltrT refS refT
                                  (A_left_transform_left_cancellative_d LS S eqS eqLS ltrS PS)
                                  (A_left_transform_left_cancellative_d LT T eqT eqLT ltrT PT)                                                        
|}.
End Proofs.   

Section Combinators.

Definition A_left_transform_product {L L' S S' : Type} (A : A_left_transform L S) (B : A_left_transform L' S') : A_left_transform (L * L') (S * S') :=
  let eqvS := A_left_transform_carrier _ _ A in
  let eqS := A_eqv_eq _ eqvS in
  let eqvPS := A_eqv_proofs _ eqvS in
  let refS := A_eqv_reflexive _ _ eqvPS in   
  let wS := A_eqv_witness _ eqvS in    
  let eqvS' := A_left_transform_carrier _ _ B in
  let eqS' := A_eqv_eq _ eqvS' in
  let eqvPS' := A_eqv_proofs _ eqvS' in
  let refS' := A_eqv_reflexive _ _ eqvPS' in   
  let wS' := A_eqv_witness _ eqvS' in      
  let eqvL := A_left_transform_label _ _ A in
  let eqL := A_eqv_eq _ eqvL in        
  let wL := A_eqv_witness _ eqvL in        
  let eqvL' := A_left_transform_label _ _ B in
  let eqL' := A_eqv_eq _ eqvL' in          
  let wL' := A_eqv_witness _ eqvL' in          
  let ltrA := A_left_transform_ltr _ _ A in
  let ltrB := A_left_transform_ltr _ _ B in     
{|
  A_left_transform_carrier      := A_eqv_product _ _ eqvS eqvS' 
; A_left_transform_label        := A_eqv_product _ _ eqvL eqvL' 
; A_left_transform_ltr          := ltr_product ltrA ltrB 
; A_left_transform_exists_id_d  := ltr_product_exists_id_decidable L S L' S' eqS wS ltrA eqS' wS' ltrB
                                                                    (A_left_transform_exists_id_d _ _ A) (A_left_transform_exists_id_d _ _ B)
; A_left_transform_exists_ann_d := ltr_product_exists_ann_decidable L S L' S' eqS wL ltrA eqS' wL' ltrB
                                                                    (A_left_transform_exists_ann_d _ _ A) (A_left_transform_exists_ann_d _ _ B)
; A_left_transform_proofs       := ltr_product_proofs L S L' S' eqS eqL wS wL ltrA refS eqS' eqL' wS' wL' ltrB refS'
                                                      (A_left_transform_proofs _ _ A) (A_left_transform_proofs _ _ B)
; A_left_transform_ast          := Cas_ast ("A_left_transform_product", 
    [A_left_transform_ast _ _ A; A_left_transform_ast _ _ B])
  (* Ast_ltr_product (A_left_transform_ast _ _ A, A_left_transform_ast _ _ B) *)
|}.


End Combinators.   

End ACAS.


Section AMCAS.

  Definition A_mcas_ltr_product {LS S LT T} (A : A_ltr_mcas LS S) (B : A_ltr_mcas LT T) :=
    match A, B with
    | A_MCAS_ltr _ _ A', A_MCAS_ltr _ _ B' => A_MCAS_ltr _ _ (A_left_transform_product A' B')
    | A_MCAS_ltr_Error _ _ sl1, A_MCAS_ltr_Error _ _ sl2 =>  A_MCAS_ltr_Error _ _ (sl1 ++ sl2)
    | A_MCAS_ltr_Error _ _ sl, _ =>  A_MCAS_ltr_Error _ _ sl
    | _, A_MCAS_ltr_Error _ _ sl =>  A_MCAS_ltr_Error _ _ sl                                       
   end.
  

  
End AMCAS.   

Section CAS.


Definition ltr_product_is_right_check {LS S LT T: Type} (wS : S) (wLS : LS) (wT : T) (wLT : LT) 
      (DS : @check_ltr_is_right LS S)      
      (DT : @check_ltr_is_right LT T) : 
            @check_ltr_is_right (LS * LT) (S * T) := 
match DS with 
| Certify_Ltr_Is_Right =>
            match DT with
            | Certify_Ltr_Is_Right => Certify_Ltr_Is_Right
            | Certify_Ltr_Not_Is_Right (l, t)  => Certify_Ltr_Not_Is_Right ((wLS, l), (wS, t))
            end 
| Certify_Ltr_Not_Is_Right (l, s)  => Certify_Ltr_Not_Is_Right ((l, wLT), (s, wT))
end. 


Definition ltr_product_left_cancellative_check {LS S LT T: Type} (wS : S) (wLS : LS) (wT : T) (wLT : LT) 
      (DS : @check_ltr_left_cancellative LS S)      
      (DT : @check_ltr_left_cancellative LT T) : 
            @check_ltr_left_cancellative (LS * LT) (S * T) := 
match DS with 
| Certify_Ltr_Left_Cancellative =>
            match DT with
            | Certify_Ltr_Left_Cancellative => Certify_Ltr_Left_Cancellative
            | Certify_Ltr_Not_Left_Cancellative (l, (t1, t2))  => Certify_Ltr_Not_Left_Cancellative ((wLS, l), ((wS, t1), (wS, t2)))
            end 
| Certify_Ltr_Not_Left_Cancellative (l, (s1, s2))  => Certify_Ltr_Not_Left_Cancellative ((l, wLT), ((s1, wT), (s2, wT)))
end. 


Definition ltr_product_left_constant_check {LS S LT T: Type} (wS : S) (wLS : LS) (wT : T) (wLT : LT) 
      (DS : @check_ltr_left_constant LS S)      
      (DT : @check_ltr_left_constant LT T) : 
            @check_ltr_left_constant (LS * LT) (S * T) := 
match DS with 
| Certify_Ltr_Left_Constant =>
            match DT with
            | Certify_Ltr_Left_Constant => Certify_Ltr_Left_Constant
            | Certify_Ltr_Not_Left_Constant (l, (t1, t2))  => Certify_Ltr_Not_Left_Constant ((wLS, l), ((wS, t1), (wS, t2)))
            end 
| Certify_Ltr_Not_Left_Constant (l, (s1, s2))  => Certify_Ltr_Not_Left_Constant ((l, wLT), ((s1, wT), (s2, wT)))
end. 



Definition ltr_product_certs {LS S LT T: Type}
      (wS : S) (wLS : LS) (PS : @left_transform_certificates LS S)
      (wT : T) (wLT : LT) (PT : @left_transform_certificates LT T) :
              @left_transform_certificates (LS * LT) (S * T) :=
{|
  left_transform_congruence          := Assert_Ltr_Congruence                                                       
; left_transform_is_right_d := ltr_product_is_right_check wS wLS wT wLT 
                                  (left_transform_is_right_d PS)
                                  (left_transform_is_right_d PT)
; left_transform_left_constant_d := ltr_product_left_constant_check wS wLS wT wLT 
                                  (left_transform_left_constant_d PS)
                                  (left_transform_left_constant_d PT)                                                        
; left_transform_left_cancellative_d := ltr_product_left_cancellative_check wS wLS wT wLT 
                                  (left_transform_left_cancellative_d PS)
                                  (left_transform_left_cancellative_d PT)                                                        
|}.

Definition ltr_product_exists_id_certifiable {LS S LT T : Type}
      (DS : @check_ltr_exists_id LS S)      
      (DT : @check_ltr_exists_id LT T) : 
   @check_ltr_exists_id (LS * LT) (S * T) := 
match DS with 
| Certify_Ltr_Exists_Id idS =>
            match DT with
            | Certify_Ltr_Exists_Id idT => Certify_Ltr_Exists_Id(idS, idT) 
            | Certify_Ltr_Not_Exists_Id => Certify_Ltr_Not_Exists_Id
            end 
| Certify_Ltr_Not_Exists_Id => Certify_Ltr_Not_Exists_Id
end.


Definition ltr_product_exists_ann_certifiable {LS S LT T : Type}
      (DS : @check_ltr_exists_ann LS S)      
      (DT : @check_ltr_exists_ann LT T) : 
   @check_ltr_exists_ann (LS * LT) (S * T) := 
match DS with 
| Certify_Ltr_Exists_Ann annS =>
            match DT with
            | Certify_Ltr_Exists_Ann annT => Certify_Ltr_Exists_Ann (annS, annT) 
            | Certify_Ltr_Not_Exists_Ann => Certify_Ltr_Not_Exists_Ann
            end 
| Certify_Ltr_Not_Exists_Ann => Certify_Ltr_Not_Exists_Ann
end.


Section Combinators.
 
Definition left_transform_product {L L' S S' : Type} (A : @left_transform L S) (B : @left_transform L' S') : @left_transform (L * L') (S * S') :=
  let eqvS := left_transform_carrier _ _ A in
  let wS := eqv_witness eqvS in
  let eqvS' := left_transform_carrier _ _ B in
  let wS' := eqv_witness eqvS' in      
  let eqvL := left_transform_label _ _ A in
  let wL := eqv_witness eqvL in        
  let eqvL' := left_transform_label _ _ B in
  let wL' := eqv_witness eqvL' in          
  let ltrA := left_transform_ltr _ _ A in
  let ltrB := left_transform_ltr _ _ B in     
{|
  left_transform_carrier      := eqv_product eqvS eqvS' 
; left_transform_label        := eqv_product eqvL eqvL' 
; left_transform_ltr          := ltr_product ltrA ltrB 
; left_transform_exists_id_d  := ltr_product_exists_id_certifiable (left_transform_exists_id_d _ _ A) (left_transform_exists_id_d _ _ B)
; left_transform_exists_ann_d := ltr_product_exists_ann_certifiable (left_transform_exists_ann_d  _ _ A) (left_transform_exists_ann_d _ _ B)
; left_transform_certs        := ltr_product_certs wS wL  (left_transform_certs _ _ A) wS' wL' (left_transform_certs _ _ B)
; left_transform_ast          := Cas_ast ("A_left_transform_product", 
    [left_transform_ast _ _ A; left_transform_ast _ _ B])
  (* Ast_ltr_product (left_transform_ast _ _ A, left_transform_ast _ _ B) *)
|}.

End Combinators.

End CAS.

Section MCAS.

  Definition mcas_ltr_product {LS S LT T} (A : @ltr_mcas LS S) (B : @ltr_mcas LT T) :=
    match A, B with
    | MCAS_ltr A', MCAS_ltr B' => MCAS_ltr (left_transform_product A' B')
    | MCAS_ltr_Error sl1, MCAS_ltr_Error sl2 =>  MCAS_ltr_Error (sl1 ++ sl2)
    | MCAS_ltr_Error sl, _ =>  MCAS_ltr_Error sl
    | _, MCAS_ltr_Error sl =>  MCAS_ltr_Error sl                                       
    end.

  
End MCAS.   


Section Verify.

Section Proofs.   
Variables
  (LS S LT T: Type)
  (eqS : brel S) (eqLS : brel LS) (wS : S) (wLS : LS) (ltrS : ltr_type LS S) (refS : brel_reflexive S eqS)
  (eqT : brel T) (eqLT : brel LT) (wT : T) (wLT : LT) (ltrT : ltr_type LT T) (refT : brel_reflexive T eqT).

Lemma correct_ltr_product_exists_ann_certifiable
      (annS_d : ltr_exists_ann_decidable LS S eqS ltrS)
      (annT_d : ltr_exists_ann_decidable LT T eqT ltrT): 
      ltr_product_exists_ann_certifiable
        (p2c_ltr_exists_ann LS S eqS ltrS annS_d)
        (p2c_ltr_exists_ann LT T eqT ltrT annT_d)
      = 
      p2c_ltr_exists_ann
        (LS * LT)
        (S * T)
        (brel_product eqS eqT) 
        (ltr_product ltrS ltrT)
        (ltr_product_exists_ann_decidable LS S LT T
           eqS wLS ltrS eqT wLT ltrT annS_d annT_d).
Proof. destruct annS_d as [ [annS annPS] | nannS ]; 
       destruct annT_d as [ [annT annPT] | nannT ]; simpl; 
       reflexivity.
Qed. 

Lemma correct_ltr_product_exists_id_certifiable
      (idS_d : ltr_exists_id_decidable LS S eqS ltrS)
      (idT_d : ltr_exists_id_decidable LT T eqT ltrT): 
      ltr_product_exists_id_certifiable
        (p2c_ltr_exists_id LS S eqS ltrS idS_d)
        (p2c_ltr_exists_id LT T eqT ltrT idT_d)
      = 
      p2c_ltr_exists_id
        (LS * LT)
        (S * T)
        (brel_product eqS eqT) 
        (ltr_product ltrS ltrT)
        (ltr_product_exists_id_decidable LS S LT T
           eqS wS ltrS eqT wT ltrT idS_d idT_d).
Proof. destruct idS_d as [ [idS idPS] | nidS ]; 
       destruct idT_d as [ [idT idPT] | nidT ]; simpl; 
       reflexivity.
Qed. 


Lemma correct_ltr_product_certs 
      (PS : left_transform_proofs LS S eqS eqLS ltrS)
      (PT : left_transform_proofs LT T eqT eqLT ltrT) :
   ltr_product_certs wS wLS  (P2C_left_transform _ _ _ _ _ PS) wT wLT (P2C_left_transform _ _ _ _ _ PT) 
   =
   P2C_left_transform _ _ _ _ _ (ltr_product_proofs LS S LT T eqS eqLS wS wLS ltrS refS eqT eqLT wT wLT ltrT refT PS PT).
Proof. destruct PS. destruct PT. unfold ltr_product_certs, ltr_product_proofs, P2C_left_transform; simpl. 
       destruct A_left_transform_is_right_d as [IRS | [[lS s] A]];
       destruct A_left_transform_is_right_d0 as [IRT | [[lT t] B]];
       destruct A_left_transform_left_constant_d as [ILKS | [[l1' [s1' s2']] C']];
       destruct A_left_transform_left_constant_d0 as [ILKT | [[l2' [t1' t2']] E']];         
       destruct A_left_transform_left_cancellative_d as [ILCS | [[l1 [s1 s2]] [C D]]];
       destruct A_left_transform_left_cancellative_d0 as [ILCT | [[l2 [t1 t2]] [E F]]]; simpl; auto.          
Qed.

End Proofs.

Section Combinators.

  Theorem correct_left_transform_product (L L' S S' : Type) (A : A_left_transform L S) (B : A_left_transform L' S') : 
    A2C_left_transform _ _ (A_left_transform_product A B)
    =                        
    left_transform_product (A2C_left_transform _ _ A) (A2C_left_transform _ _ B).
  Proof. unfold A2C_left_transform, A_left_transform_product, left_transform_product. simpl. 
         rewrite <- correct_ltr_product_certs.
         rewrite correct_eqv_product.
         rewrite correct_eqv_product.
         rewrite <- correct_ltr_product_exists_id_certifiable. 
         rewrite <- correct_ltr_product_exists_ann_certifiable. 
         reflexivity. 
  Qed.


  Theorem correct_mcas_left_transform_product (L L' S S' : Type) (A : A_ltr_mcas L S) (B : A_ltr_mcas L' S') : 
    A2C_mcas_ltr _ _ (A_mcas_ltr_product A B)
    =                        
    mcas_ltr_product (A2C_mcas_ltr _ _ A) (A2C_mcas_ltr _ _ B).
  Proof. unfold A_mcas_ltr_product, mcas_ltr_product, A2C_mcas_ltr. simpl.
         destruct A, B; simpl; try reflexivity. 
         rewrite correct_left_transform_product.
         reflexivity. 
  Qed.

  
End Combinators.   

End Verify.   
  
