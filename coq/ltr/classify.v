
Require Import CAS.coq.common.compute.
Require Import CAS.coq.ltr.structures.

Section AMCAS. 


Definition A_classify_ltr {L S : Type} (A : @A_ltr L S) : @A_below_ltr L S := 
   A_Below_ltr_top A. 

End AMCAS. 

Section MCAS. 


Definition classify_ltr {L S : Type} (A : @ltr L S) : @below_ltr L S := 
   Below_ltr_top A. 

End MCAS. 

