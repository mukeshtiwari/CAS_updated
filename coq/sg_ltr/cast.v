Require Import CAS.coq.common.compute.
Require Import CAS.coq.sg_ltr.structures.
Require Import CAS.coq.sg_ltr.classify. 

Section AMCAS. 

  Definition A_cast_up_sg_ltr {L S : Type} (A : @A_below_sg_ltr L S) : @A_sg_ltr L S :=
    match A with 
    | A_Below_sg_ltr_top B   => B 
    end.
  
End AMCAS. 

Section MCAS. 

  Definition cast_up_sg_ltr {L S : Type} (A : @below_sg_ltr L S) : @sg_ltr L S :=
    match A with 
    | Below_sg_ltr_top B   => B 
    end.

End MCAS. 


