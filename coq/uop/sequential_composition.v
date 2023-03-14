Require Export CAS.coq.common.compute.
Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.reduce. 
Require Import CAS.coq.uop.properties.
Require Import CAS.coq.sg.properties. 
Require Import CAS.coq.sg.reduce. 
(*
   Sequential composition of reductions 

   (S, =, (x)) -----------
   |                      |
   r1                     |
   |                      | 
   \/                     | 
  (S_r1, =, (x)_r1)       | r2 o r1  
   |                      | 
   r2                     | 
   |                      |
   \/                     \/
  ((S_r1)_r2, =, ((x)_r1)_r2) 

 

  Two steps: 

      a ((x)_r1)_r2 b = r2(a (x)_r1 b). 
                      = r2(r1(a (x) b)). 

    (S_r1)_r2 = {a in S_r1 | r2(a) = a}
              = {a in {a in S | r1(a) = a} | r2(a) = a} 
              = {a in S | r1(a) = a and r2(a) = a} 


   Equality in "OCaml"? 

        a =_{r1 o r2} b <-> (r1(a) =_r1(b)) and (r2(a) =_r2(b)) 

 
      a (x)_{r2 o r1} b = (r2 o r1)(a (x) b). 
                        = r2(r1(a (x) b)). 


"r2 o r1" as a reduction over (S, =, (x))
          
 left1 : (r2 o r1)(((r2 o r1) x) + y) = (r2 o r1)(x + y)
       = r2(r1( (r2 (r1 x)) + y) ) = r2 (r1 (x + y))

right1 : (r2 o r1)(x + ((r2 o r1) y)) = (r2 o r1)(x + y)
       = r2(r1( x + (r2 (r1 y))) ) = r2 (r1 (x + y))

Note, if "r2 o r1 = r1 o r2" and both are reductions 
then 

 left : r2(r1( (r2 (r1 x)) + y) ) 
      = r2(r1( (r1 (r2 x)) + y) ) 
      = r2(r1((r2 x)) + y)
      = r1(r2((r2 x)) + y)
      = r1(r2(x + y)
      = r2(r1(x + y).
And the same with right. 

What if r1 and r2 don't commute? 

Suppose r1 is a reduction 
  left : r1 ((r1 x) + y) = r1 (x + y) 
 right : r1 (x + (r1 y)) = r1 (x + y) 

Should we insist that r2 be a reduction over that? 
This makes sense if we want to read the diagram as 
a composition of two reductions. 
That is, 

   left2 : r2 ((r2 x) +_r1 y) = r2 (x +_r1 y) 
         = r2 (r1((r2 x) + y)) = r2 (r1 (x + y))
         = (r2 o r1)((r2 x) + y) = (r2 o r1)(x + y)

This is stronger than left1: 

left2 -> left1 : 
     r2(r1( (r2 (r1 x)) + y) )
   = r2(r1( (r1 x) + y) )
   = r2(r1(x + y) )

Note that to go the other way we need something stronger still, like 

    r1((r2 (r1 x)) + y) = r1(x + y) 

but then r2 is not required to be a reduction and this might not 
make sense.... 

Look at "bottleneck semiring" for an example? 

*) 
Section Computation.
Definition bop_sequential_compose : ∀ {S : Type}, unary_op S → unary_op S → binary_op S → binary_op S 
  := λ {S} r2 r1 b, bop_reduce r2 (bop_reduce r1 b).

(* Note: 

Compute uop_sequential_compose.
= λ (x x0 : unary_op ?S) (x1 : binary_op ?S) (x2 x3 : ?S), x (x0 (x1 x2 x3))
  : unary_op ?S → unary_op ?S → binary_op ?S → binary_op ?S

So, "bop_sequential_compose r2 r1 b" is really the same as 

    bop_reduce (uop_compose r2 r1) b

where uop_compose is defined in commutative_composition.v. 
However, I want to be a bit more careful here....
*) 

End Computation. 

Section Theory.

  Variable S : Type. 
  Variable b : binary_op S.
  Variable r1 : unary_op S.
  Variable r2       : unary_op S.
  Variable eqS    : brel S.    

  (* r1 is a reduction over S *) 
  Variable r1_cong  : uop_congruence S eqS r1. 
  Variable r1_idem  : uop_idempotent S eqS r1.
  Variable r1_left  : bop_left_uop_invariant S eqS (bop_reduce r1 b) r1.  
  Variable r1_right : bop_right_uop_invariant S eqS (bop_reduce r1 b) r1.

  (* r2 is just idempotent *) 
  Variable r2_cong  : uop_congruence S eqS r2. 
  Variable r2_idem  : uop_idempotent S eqS r2.

  Definition eqS_r1 : brel S      := brel_reduce eqS r1. 
  Definition b_r1   : binary_op S := bop_reduce r1 b.

  (* Now, let's use r2 to try to build a reduction over ((S, eqS_r1), b_r1) *) 

  (* NB : this does not require that r2 and r1 commute *) 
  Lemma r2_idempotent : uop_idempotent S eqS_r1 r2.  
  Proof. intro s. compute.
         assert (H1 := r2_idem s). 
         apply r1_cong in H1.
         exact H1. 
  Qed.
  
  Lemma r2_left_uop_invariant :
    (* H0 : ∀ s1 s2 : S, eqS (r1 (b (r2 s1) s2)) (r1 (b s1 s2)) = true *) 
    bop_left_uop_invariant S eqS b_r1 r2 -> 
      bop_left_uop_invariant S eqS_r1 (bop_sequential_compose r2 r1 b) r2.  
  Proof. intros H0 s t. compute.
         assert (H1 : eqS (r1 (b (r2 s) t)) (r1 (b s t)) = true).
         {
           assert (H2 := H0 s t). compute in H2.
           exact H2. 
         } 
         apply r2_cong in H1. apply r1_cong in H1.
         exact H1. 
  Qed. 

  Lemma r2_right_uop_invariant :
    (* H0 : ∀ s1 s2 : S, eqS (r1 (b s1 (r2 s2))) (r1 (b s1 s2)) = true *)
    bop_right_uop_invariant S eqS b_r1 r2 -> 
      bop_right_uop_invariant S eqS_r1 (bop_sequential_compose r2 r1 b) r2.  
  Proof. intros H0 s t. compute.
         assert (H1 : eqS (r1 (b s (r2 t))) (r1 (b s t)) = true).
         {
           assert (H2 := H0 s t). compute in H2.
           exact H2. 
         } 
         apply r2_cong in H1. apply r1_cong in H1.
         exact H1. 
  Qed.


End Theory.

