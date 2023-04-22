Require Import CAS.coq.common.base. 
Require Import CAS.coq.eqv.sum.
Require Import CAS.coq.sg.left_sum.
Require Import CAS.coq.ltr.sum_of_product. 

Section Theory.

  (*  
     left_sum_sum_of_product (S, LS, +_S, |>_S) (T, LT, +_T, |>_T) = 
            (S + T, LS * LT, bop_left_sum +_S +_T, ltr_sum_of_product |>_S |>_T)
            
    (inl s) + (inl s') = inl (s +_S s') 
    (inr t) + (inr t') = inr (t +_T t') 
    (inl s) + (inr t) = inl s
    (inr t) + (inl s) = inl s

    (lS, lT) |> inl s = inl (lS |>_S s) 
    (lS, lT) |> inr t = inr (lT |>_T t) 

    What about adding a "bump up" label? 

    inl(lS, lT) |> inl s = inl (lS |>_S s) 
    inl(lS, lT) |> inr t = inr (lT |>_T t) 
     inr(lS, t) |> inl c = inr (t) 
     inr(lT, t) |> inr c = inr (l |>_T c) 

    this could be implemented with a label_union 

    label_union (S, LS_1, +_S, |>_1) (S, LS_2, +_S, |>_2) = (S, LS_1 + LS_2, +_S, |>_1 + |>_2)

    with ltr_sum_of_product (S, LS, |>_S) (T, LT, |>_T)

    (lS, lT) |> inl s = inl (lS |>_S s) 
    (lS, lT) |> inr t = inr (lT |>_T t) 

    and  with ltr_sum_of_product (T, T, right) (T, LT, |>_T)

     (t, lT) |> inl c = inr (t) 
     (t, lT) |> inr c = inr (l |>_T c) 


      
*) 


Variable LS S LT T : Type.
Variable rS : brel S.
Variable rT : brel T.

Variable refS : brel_reflexive S rS.

Variable wS : S.
Variable wT : T.

Variable wLS : LS.
Variable wLT : LT.

Variable addT : binary_op T. 
Variable addS : binary_op S.

Variable ltrS : left_transform LS S.
Variable ltrT : left_transform LT T.

Notation "a [+] b" := (brel_sum a b) (at level 15).
Notation "x <+] y"  := (bop_left_sum x y) (at level 15).
Notation "a |*> b" := (ltr_sum_of_product a b) (at level 15). 


Lemma sltr_left_sum_sum_of_product_distributive :
  sltr_distributive S  LS rS addS ltrS → 
  sltr_distributive T LT rT addT ltrT →
         sltr_distributive (S + T) (LS * LT) (rS [+] rT) (addS <+] addT) (ltrS |*> ltrT).
Proof. unfold sltr_distributive.  intros dS dT [lS lT] [s1 | t1] [s2 | t2]; compute; auto. Qed. 


Lemma sltr_left_sum_sum_of_product_not_distributive_v1 : 
  sltr_not_distributive S LS rS addS ltrS → 
       sltr_not_distributive (S + T) (LS * LT) (rS [+] rT) (addS <+] addT) (ltrS |*> ltrT).
Proof. intros [[lS [s1 s2]] Ps]. exists ((lS, wLT), (inl s1, inl s2)). compute. assumption. Defined.        

Lemma sltr_left_sum_sum_of_product_not_distributive_v2 : 
  sltr_not_distributive T LT rT addT ltrT → 
       sltr_not_distributive (S + T) (LS * LT) (rS [+] rT) (addS <+] addT) (ltrS |*> ltrT).
Proof. intros [[lT [t1 t2]] Pt]. exists ((wLS, lT), (inr t1, inr t2)). compute. assumption. Defined.        


Definition sltr_left_sum_sum_of_product_distributive_decide :
  sltr_distributive_decidable S LS rS addS ltrS → 
  sltr_distributive_decidable T LT rT addT ltrT →
         sltr_distributive_decidable (S + T) (LS * LT) (rS [+] rT) (addS <+] addT) (ltrS |*> ltrT)
:= λ ldS_d ldT_d,
match ldS_d with
| inl ldS  => match ldT_d with
              | inl ldT  => inl (sltr_left_sum_sum_of_product_distributive ldS ldT)
              | inr nldT => inr (sltr_left_sum_sum_of_product_not_distributive_v2 nldT)
              end 
| inr nldS => inr (sltr_left_sum_sum_of_product_not_distributive_v1 nldS)
end. 

Lemma sltr_left_sum_sum_of_product_absorptive :
        sltr_absorptive S LS rS addS ltrS -> sltr_absorptive T LT rT addT ltrT ->
          sltr_absorptive (S + T) (LS * LT) (rS [+] rT) (addS <+] addT) (ltrS |*> ltrT). 
Proof. intros aS aT [l1 l2] [s | t]; compute; auto. Qed. 


Lemma sltr_left_sum_sum_of_product_not_absorptive_v1 :
        sltr_not_absorptive S LS rS addS ltrS -> sltr_not_absorptive (S + T) (LS * LT) (rS [+] rT) (addS <+] addT) (ltrS |*> ltrT). 
Proof. intros [[lS s] P]. exists((lS, wLT), inl s). compute; auto. Defined. 

Lemma sltr_left_sum_sum_of_product_not_absorptive_v2 :
        sltr_not_absorptive T LT rT addT ltrT -> sltr_not_absorptive (S + T) (LS * LT) (rS [+] rT) (addS <+] addT) (ltrS |*> ltrT). 
Proof. intros [[lT t] P]. exists((wLS, lT), inr t). compute; auto. Defined. 

Definition sltr_left_sum_sum_of_product_absorptive_decide :
  sltr_absorptive_decidable S LS rS addS ltrS → 
  sltr_absorptive_decidable T LT rT addT ltrT →
         sltr_absorptive_decidable (S + T) (LS * LT) (rS [+] rT) (addS <+] addT) (ltrS |*> ltrT)
:= λ aS_d aT_d,
match aS_d with
| inl aS  => match aT_d with
              | inl aT  => inl (sltr_left_sum_sum_of_product_absorptive aS aT)
              | inr naT => inr (sltr_left_sum_sum_of_product_not_absorptive_v2 naT)
              end 
| inr naS => inr (sltr_left_sum_sum_of_product_not_absorptive_v1 naS)
end. 

                                                                                   

End Theory.

Section ACAS.
                                                                             
                                   
End ACAS.

Section CAS.

End CAS.

Section Verify.
  

 
End Verify.   
  