Require Import Coq.Arith.Arith.     (* beq_nat *) 
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List. 

Require Import CAS.coq.common.compute. 
Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.theory.
Require Import CAS.coq.theory.set. (* in_set currently defined here *) 
Require Import CAS.coq.sg.product.
Check in_set. 
Lemma in_set_product_intro
         
        -> in_set (brel_product eqS eqT) (X x Y) (s, t) 


