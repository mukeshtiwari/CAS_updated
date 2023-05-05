
Require Import CAS.coq.common.compute.
Require Import CAS.coq.sg_ltr.structures.

Section AMCAS. 


Definition A_classify_sg_ltr {L S : Type} (A : @A_sg_ltr L S) : @A_below_sg_ltr L S := 
   A_Below_sg_ltr_top A. 

End AMCAS. 

Section MCAS. 


Definition classify_sg_ltr {L S : Type} (A : @sg_ltr L S) : @below_sg_ltr L S := 
   Below_sg_ltr_top A. 

End MCAS. 

