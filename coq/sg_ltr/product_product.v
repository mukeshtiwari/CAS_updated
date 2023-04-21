Require Import Coq.Bool.Bool.
Require Import CAS.coq.common.base.
Require Import CAS.coq.eqv.product.
Require Import CAS.coq.ltr.product. 


Section Theory.
  
  Variable S    : Type.
  Variable LS   : Type.
  Variable eqS  : brel S.
  Variable wS   : S.
  Variable wLS  : LS.
  Variable addS : binary_op S.
  Variable ltrS : left_transform LS S .

  Variable T    : Type.
  Variable LT   : Type.
  Variable eqT  : brel T.
  Variable wT   : T.
  Variable wLT  : LT.
  Variable addT : binary_op T.
  Variable ltrT : left_transform LT T.

  Notation "a <*> b" := (brel_product a b) (at level 15).
  Notation "a [+] b" := (bop_product a b) (at level 15).
  Notation "a |*> b" := (ltr_product a b) (at level 15).


  Lemma sltr_product_distributive :
        sltr_distributive S LS eqS addS ltrS -> sltr_distributive T LT eqT addT ltrT ->
          sltr_distributive (S * T) (LS * LT) (eqS <*> eqT) (addS [+] addT) (ltrS |*> ltrT). 
  Proof.
        intros dS dT [l1 l2] [s1 s2] [sg lg].
        simpl. rewrite dS, dT. simpl. reflexivity.
  Defined.

  
  Lemma sltr_product_not_distributive_v1 :
        sltr_not_distributive S LS eqS addS ltrS ->
          sltr_not_distributive (S * T) (LS * LT) (eqS <*> eqT) (addS [+] addT) (ltrS |*> ltrT). 
  Proof.
        intros [ [l [s1 s2]] nd ].
        exists ((l, wLT), ((s1, wT), (s2, wT))).
        simpl. rewrite nd. simpl. reflexivity.
  Defined.

  Lemma sltr_product_not_distributive_v2 :
        sltr_not_distributive T LT eqT addT ltrT ->
          sltr_not_distributive (S * T) (LS * LT) (eqS <*> eqT) (addS [+] addT) (ltrS |*> ltrT).
  Proof.
        intros [ [lt [t1 t2]] nd ].
        exists ((wLS, lt), ((wS, t1), (wS, t2))).
        simpl. rewrite nd. apply andb_comm.   
  Defined.
  
  Lemma sltr_product_not_distributive :
        (sltr_not_distributive S LS eqS addS ltrS +
        sltr_not_distributive T LT eqT addT ltrT) ->
          sltr_not_distributive (S * T) (LS * LT) (eqS <*> eqT) (addS [+] addT) (ltrS |*> ltrT).
  Proof.
        intros [SND | TND].
        apply sltr_product_not_distributive_v1; auto. 
        apply sltr_product_not_distributive_v2; auto.
  Defined.
  (* MACEKI: ask TIM: v1-v2  vs.  _left-_right ??  *)

  
  Definition sltr_product_distributive_decide :
    sltr_distributive_decidable S LS eqS addS ltrS ->
    sltr_distributive_decidable T LT eqT addT ltrT ->
    sltr_distributive_decidable (S * T) (LS * LT) (eqS <*> eqT) (addS [+] addT) (ltrS |*> ltrT)
      := λ dS_d dT_d,
         match dS_d with
         | inl dS =>
           match dT_d with
           | inl dT => inl _ (sltr_product_distributive dS dT)
           | inr not_dT => inr _ (sltr_product_not_distributive_v2 not_dT)
           end
         | inr not_dS => inr _ (sltr_product_not_distributive_v1 not_dS)
         end.


  Lemma sltr_product_absorptive :
        sltr_absorptive S LS eqS addS ltrS -> sltr_absorptive T LT eqT addT ltrT ->
          sltr_absorptive (S * T) (LS * LT) (eqS <*> eqT) (addS [+] addT) (ltrS |*> ltrT). 
  Proof.
        intros aS aT [l1 l2] [s1 s2].
        simpl. rewrite aS, aT. simpl. reflexivity.
  Defined.

  
  Lemma sltr_product_not_absorptive_v1 :
        sltr_not_absorptive S LS eqS addS ltrS ->
          sltr_not_absorptive (S * T) (LS * LT) (eqS <*> eqT) (addS [+] addT) (ltrS |*> ltrT). 
  Proof.
        intros [ [ls s] nd ].
        exists ((ls, wLT), (s, wT)).
        simpl. rewrite nd. simpl. reflexivity.
  Defined.
    
  Lemma sltr_product_not_absorptive_v2 :
        sltr_not_absorptive T LT eqT addT ltrT ->
          sltr_not_absorptive (S * T) (LS * LT) (eqS <*> eqT) (addS [+] addT) (ltrS |*> ltrT). 
  Proof.
        intros [ [lt t] nd ].
        exists ((wLS, lt), (wS, t)).
        simpl. rewrite nd. apply andb_comm.
  Defined.
  
  Lemma sltr_product_not_absorptive :
        (sltr_not_absorptive S LS eqS addS ltrS +
        sltr_not_absorptive T LT eqT addT ltrT) ->
          sltr_not_absorptive (S * T) (LS * LT) (eqS <*> eqT) (addS [+] addT) (ltrS |*> ltrT).
  Proof.
        intros [SNA | TNA].
        apply sltr_product_not_absorptive_v1; auto. 
        apply sltr_product_not_absorptive_v2; auto.
  Defined.
  

  Definition sltr_product_absorptive_decide :
    sltr_absorptive_decidable S LS eqS addS ltrS ->
    sltr_absorptive_decidable T LT eqT addT ltrT ->
    sltr_absorptive_decidable (S * T) (LS * LT) (eqS <*> eqT) (addS [+] addT) (ltrS |*> ltrT)
      := λ aS_d aT_d,
        match aS_d with
        | inl aS =>
          match aT_d with
          | inl aT => inl _ (sltr_product_absorptive aS aT)
          | inr not_aT => inr _ (sltr_product_not_absorptive_v2 not_aT)
          end
        | inr not_aS => inr _ (sltr_product_not_absorptive_v1 not_aS)
        end.

End Theory.