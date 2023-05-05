Require Import Coq.Bool.Bool.
Require Import CAS.coq.common.compute. 

Require Import CAS.coq.eqv.product.
Require Import CAS.coq.sg.product. 
Require Import CAS.coq.ltr.product. 
Require Import CAS.coq.sg_ltr.properties. 
Require Import CAS.coq.sg_ltr.structures. 

Section Theory.
  
  Variable S    : Type.
  Variable LS   : Type.
  Variable eqS  : brel S.
  Variable wS   : S.
  Variable wLS  : LS.
  Variable addS : binary_op S.
  Variable ltrS : ltr_type LS S .

  Variable T    : Type.
  Variable LT   : Type.
  Variable eqT  : brel T.
  Variable wT   : T.
  Variable wLT  : LT.
  Variable addT : binary_op T.
  Variable ltrT : ltr_type LT T.

  Notation "a <*> b" := (brel_product a b) (at level 15).
  Notation "a [+] b" := (bop_product a b) (at level 15).
  Notation "a |*> b" := (ltr_product_op a b) (at level 15).


  Lemma sg_ltr_product_distributive 
    (dS : A_sg_ltr_distributive eqS addS ltrS)
    (dT : A_sg_ltr_distributive eqT addT ltrT) : 
       A_sg_ltr_distributive (eqS <*> eqT) (addS [+] addT) (ltrS |*> ltrT). 
  Proof. intros [l1 l2] [s1 s2] [sg lg]; simpl. 
         rewrite dS, dT. reflexivity.
  Qed.

  
  Lemma sg_ltr_product_not_distributive_v1 
        (ndS : A_sg_ltr_not_distributive eqS addS ltrS) : 
          A_sg_ltr_not_distributive (eqS <*> eqT) (addS [+] addT) (ltrS |*> ltrT). 
  Proof. destruct ndS as [ [l [s1 s2]] nd ].
        exists ((l, wLT), ((s1, wT), (s2, wT))).
        simpl. rewrite nd. reflexivity.
  Defined.

  Lemma sg_ltr_product_not_distributive_v2 
        (ndT : A_sg_ltr_not_distributive  eqT addT ltrT): 
          A_sg_ltr_not_distributive (eqS <*> eqT) (addS [+] addT) (ltrS |*> ltrT).
  Proof. destruct ndT as [ [lt [t1 t2]] nd ].
        exists ((wLS, lt), ((wS, t1), (wS, t2))).
        simpl. rewrite nd. apply andb_comm.   
  Defined.
  
  
  Definition sg_ltr_product_distributive_decidable 
    (dS_d : A_sg_ltr_distributive_decidable eqS addS ltrS)
    (dT_d : A_sg_ltr_distributive_decidable eqT addT ltrT) : 
    A_sg_ltr_distributive_decidable (eqS <*> eqT) (addS [+] addT) (ltrS |*> ltrT) := 
    match dS_d with
    | inl dS =>
        match dT_d with
        | inl dT => inl _ (sg_ltr_product_distributive dS dT)
        | inr not_dT => inr _ (sg_ltr_product_not_distributive_v2 not_dT)
        end
    | inr not_dS => inr _ (sg_ltr_product_not_distributive_v1 not_dS)
    end.

  Lemma sg_ltr_product_absorptive 
    (aS : A_sg_ltr_absorptive eqS addS ltrS)
    (aT : A_sg_ltr_absorptive eqT addT ltrT) : 
          A_sg_ltr_absorptive (eqS <*> eqT) (addS [+] addT) (ltrS |*> ltrT). 
  Proof. intros [l1 l2] [s1 s2]; simpl. 
         rewrite aS, aT. reflexivity.
  Qed. 
  
  Lemma sg_ltr_product_not_absorptive_v1 
        (naS : A_sg_ltr_not_absorptive eqS addS ltrS) : 
          A_sg_ltr_not_absorptive (eqS <*> eqT) (addS [+] addT) (ltrS |*> ltrT). 
  Proof. destruct naS as [ [ls s] nd ].
         exists ((ls, wLT), (s, wT)); simpl. 
         rewrite nd. reflexivity.
  Defined.
    
  Lemma sg_ltr_product_not_absorptive_v2 
        (naT : A_sg_ltr_not_absorptive eqT addT ltrT) : 
          A_sg_ltr_not_absorptive (eqS <*> eqT) (addS [+] addT) (ltrS |*> ltrT). 
  Proof. destruct naT as [ [lt t] nd ].
        exists ((wLS, lt), (wS, t)). simpl. 
        rewrite nd. apply andb_comm.
  Defined.
  

  Definition sg_ltr_product_absorptive_decidable 
    (aS_d : A_sg_ltr_absorptive_decidable eqS addS ltrS)
    (aT_d : A_sg_ltr_absorptive_decidable eqT addT ltrT) : 
    A_sg_ltr_absorptive_decidable (eqS <*> eqT) (addS [+] addT) (ltrS |*> ltrT) := 
    match aS_d with
    | inl aS =>
        match aT_d with
        | inl aT => inl _ (sg_ltr_product_absorptive aS aT)
        | inr not_aT => inr _ (sg_ltr_product_not_absorptive_v2 not_aT)
        end
    | inr not_aS => inr _ (sg_ltr_product_not_absorptive_v1 not_aS)
    end.

  Lemma sg_ltr_product_strictly_absorptive 
    (aS : A_sg_ltr_strictly_absorptive eqS addS ltrS)
    (aT : A_sg_ltr_strictly_absorptive eqT addT ltrT) : 
          A_sg_ltr_strictly_absorptive (eqS <*> eqT) (addS [+] addT) (ltrS |*> ltrT). 
  Proof. intros [l1 l2] [s1 s2]; simpl. unfold A_sg_ltr_strictly_absorptive in aS. 
         HERE. 
         - rewrite aS, aT. reflexivity.
  Qed. 
  
  Lemma sg_ltr_product_not_strictly_absorptive_v1 
        (naS : A_sg_ltr_not_strictly_absorptive eqS addS ltrS) : 
          A_sg_ltr_not_strictly_absorptive (eqS <*> eqT) (addS [+] addT) (ltrS |*> ltrT). 
  Proof. destruct naS as [ [ls s] nd ].
         exists ((ls, wLT), (s, wT)); simpl. 
         rewrite nd. reflexivity.
  Defined.
    
  Lemma sg_ltr_product_not_strictly_absorptive_v2 
        (naT : A_sg_ltr_not_strictly_absorptive eqT addT ltrT) : 
          A_sg_ltr_not_strictly_absorptive (eqS <*> eqT) (addS [+] addT) (ltrS |*> ltrT). 
  Proof. destruct naT as [ [lt t] nd ].
        exists ((wLS, lt), (wS, t)). simpl. 
        rewrite nd. apply andb_comm.
  Defined.
  

  Definition sg_ltr_product_strictly_absorptive_decidable 
    (aS_d : A_sg_ltr_strictly_absorptive_decidable eqS addS ltrS)
    (aT_d : A_sg_ltr_strictly_absorptive_decidable eqT addT ltrT) : 
    A_sg_ltr_strictly_absorptive_decidable (eqS <*> eqT) (addS [+] addT) (ltrS |*> ltrT) := 
    match aS_d with
    | inl aS =>
        match aT_d with
        | inl aT => inl _ (sg_ltr_product_strictly_absorptive aS aT)
        | inr not_aT => inr _ (sg_ltr_product_not_strictly_absorptive_v2 not_aT)
        end
    | inr not_aS => inr _ (sg_ltr_product_not_strictly_absorptive_v1 not_aS)
    end.
  

End Theory.

Section ACAS.

  Print A_sg_ltr_properties.

  Definition A_sg_ltr_product_properties
    {LS LT S T : Type} (eqS : brel S) (eqT : brel T)
    (addS : binary_op S) (addT : binary_op T)
    (ltrS : ltr_type LS S) (ltrT : ltr_type LT T) 
    (A : A_sg_ltr_properties LS S eqS addS ltrS)
    (B : A_sg_ltr_properties LT T eqS addT ltrT) :=        
    {|
      A_sg_ltr_distributive_d        :=
    ; A_sg_ltr_absorptive_d          := 
    ; A_sg_ltr_strictly_absorptive_d :=
    |}.
  

End ACAS.   
