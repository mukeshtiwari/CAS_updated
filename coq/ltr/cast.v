Require Import CAS.coq.common.compute.
Require Import CAS.coq.ltr.structures.
Require Import CAS.coq.ltr.classify. 

Section AMCAS. 

  Definition A_cast_up_ltr {L S : Type} (A : @A_below_ltr L S) : @A_ltr L S :=
    match A with 
    | A_Below_ltr_top B   => B 
    end.
  
End AMCAS. 

Section MCAS. 

  Definition cast_up_ltr {L S : Type} (A : @below_ltr L S) : @ltr L S :=
    match A with 
    | Below_ltr_top B   => B 
    end.

End MCAS. 


