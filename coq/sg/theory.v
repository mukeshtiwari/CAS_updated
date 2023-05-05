Require Import Coq.Arith.Arith.  

Require Import CAS.coq.common.compute.

Require Import CAS.coq.uop.properties.

Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.theory.
Require Import CAS.coq.eqv.set. 

Require Import CAS.coq.sg.properties.


(* 

In addition to properties for identities and annihilators, the semigroup properties, so far 
are as follows (from structures.v): 

Record sg_proofs (S: Type) (eq : brel S) (bop : binary_op S) := 
{
(* "root set" required                          *) 
  A_sg_associative      : bop_associative S eq bop 
; A_sg_congruence       : bop_congruence S eq bop   

(* "root set" of optional semigroup properties *) 
; A_sg_commutative_d    : bop_commutative_decidable S eq bop  
; A_sg_selective_d      : bop_selective_decidable S eq bop  
; A_sg_idempotent_d     : bop_idempotent_decidable S eq bop  

(* needed to decide selectivity of sg product    *) 
; A_sg_is_left_d        : bop_is_left_decidable S eq bop  
; A_sg_is_right_d       : bop_is_right_decidable S eq bop  

(* needed to decide distributivity of (lex, product). For multiplicative operator *) 
; A_sg_left_cancel_d    : bop_left_cancellative_decidable S eq bop 
; A_sg_right_cancel_d   : bop_right_cancellative_decidable S eq bop 

(* needed to decide distributivity of (lex, product). For multiplicative operator *) 
; A_sg_left_constant_d  : bop_left_constant_decidable S eq bop 
; A_sg_right_constant_d : bop_right_constant_decidable S eq bop 

(* needed to decide absorptivity of (lex, product). For multiplicative operator *) 
; A_sg_anti_left_d      : bop_anti_left_decidable S eq bop 
; A_sg_anti_right_d     : bop_anti_right_decidable S eq bop

}. 

Some temporary abbreviations: 

P                 NOT P 
--------------------------------------------
N = id             n   (need left/right?)
A = Ann            a   (need left/right?)

C = Commutative    c
I = Idempotent     i
S = Selective      s

LK = cancellative  lk (left)
RK = cancellative  rk (right) 
LQ = constant      lq (left)  
RQ = constant      rq (right) 
L = is left        l 
R = is right       r
Y = anti left      y 
Z = anti right     z

Call {C, c, I, i, S, s} the "additive properties".  
The others (not including N and A) are "multiplicative properties". 

We can "sub-class" semigroups by looking at the implications 
of various combinations of properties. 

Recall: we are assuming all carrier sets are not trivial. 

Below, q alone stands for both lq and rq, k alone for both lk and rk. 

Here is a summary of the implications proved below. 

C          ->   l r
I          ->         y z 
CI(S || s) -> k l r q y z     (S || s) means that proof assume selectivity is decidable. 
NA         -> k l r q y z 
N          ->   l r q y z 
A          -> k l r   y z


S  -> I 
i  -> s 
K  -> a
K(id || not_id)  -> i 
LK -> lq
RK -> rq



From this we can derive some "natural" semigroup classes. 
A "D" says that the propery is decidable. 

N A C I S   LK RK LQ RQ L R Y Z        comments 
-----------------------------------------------------------
D D D D D   D  D  D  D  D D D D        semigroup
D A D D D   lk rk D  D  l r y z        semigroup "with zero" (thinking multiplicitively) 
N D D D D   D  D  lq rq l r y z        monoid 
N A D D D   kk rk lq rq l r y z        monoid "with zero" 
D D C I s   kk rk lq rq l r y z        commutative and idempotent semigroup (semi lattice) 
D D C I S   kk rk lq rq l r y z        commutative and selective semigroup


What "types" do base semigroups have? 

                N A C I S   LK RK LQ RQ L R Y Z 
-----------------------------------------------
and             N A C I S   lk rk lq rq l r y z 
or              N A C I S   lk rk lq rq l r y z 
min             n A C I S   lk rk lq rq l r y z 
max             N a C I S   lk rk lq rq l r y z 
union           N D C I s   lk rk lq rq l r y z 
intersect       D A C I s   lk rk lq rq l r y z 
times           N A C i s   lk rk lq rq l r y z 
plus            N a C i s   LK RK lq rq l r y z 
concat          N a c i s   LK RK lq rq l r y z 
left            n a c i S   lk RK LQ rq L r y z 
right           n a c i S   LK rk lq RQ l R y z 

Question : can we think of a (natural) base algebra that is anit-left or anti-right or both? 

Here are the *result types* of the current set of semigroup combinators. 
A "D" says that the propery is decidable. 

                N A C I S   LK RK LQ RQ L R Y Z 
-----------------------------------------------
product         D D D D D   D  D  D  D  D D D D          (note: product is anit-left if either arg is. same for anit-right) 
add_id          N D D D D   D  D  lq rq l r y z 
add_ann         D A D D D   lk rk lq rq l r y z 
left_sum        D D D D D   lk rk lq rq l r y z 
right_sum       D D D D D   lk rk lq rq l r y z 
llex            D D D D D   lk rk lq rq l r y z          (general version?) 
lift            D A D D D   lk rk lq rq l r y z          
minset_union    N D C I s   lk rk lq rq l r y z    
minset_lift     D A D ? ?   lk rk lq rq l r y z          (what about pre-order version?)






Combinators 

CI x CI = CI 
CI x CS = CI 
CS x CI = CI 
CS x CS = CI 

CSNA CINA CSnA CSNa    

CINA x CINA = CINA 
CSNA x CSNA = CINA 
CINA x CSNA = CINA 
CSNA x CINA = CINA 




*) 





Section Id_Ann.

(* Id, Ann are unique *) 

Lemma bop_id_unique : ∀ (S : Type) 
                        (r : brel S )
                        (symS : brel_symmetric S r)
                        (trnS : brel_transitive S r)
                        (b : binary_op S )
                        (p : bop_exists_id S r b)        
                        (q : bop_exists_id S r b), r (projT1 p) (projT1 q) = true.             
Proof. intros S r symS trnS b [s1 P] [s2 Q]. simpl.  
       destruct (Q s1) as [_ R1]. destruct (P s2) as [L2 _]. 
       apply symS in R1. apply (trnS _ _ _ R1 L2). 
Defined.                         

Lemma bop_is_id_equal : ∀ (S : Type) 
                        (r : brel S )
                        (symS : brel_symmetric S r)
                        (trnS : brel_transitive S r)
                        (b : binary_op S )
                        (x : S )
                        (y : S )
                        (p : bop_is_id S r b x)        
                        (q : bop_is_id S r b y), r x y = true.             
Proof. intros S r symS trnS b x y p q. 
       destruct (q x) as [_ R1]. destruct (p y) as [L2 _]. 
       apply symS in R1. apply (trnS _ _ _ R1 L2). 
Defined.                         


Lemma bop_ann_unique : ∀ (S : Type) 
                        (r : brel S )
                        (symS : brel_symmetric S r)
                        (trnS : brel_transitive S r)
                        (b : binary_op S )
                        (p : bop_exists_ann S r b)        
                        (q : bop_exists_ann S r b), r (projT1 p) (projT1 q) = true.             
Proof. intros S r symS trnS b [s1 P] [s2 Q]. simpl.  
       destruct (Q s1) as [_ R1]. destruct (P s2) as [L2 _]. 
       apply symS in L2. apply (trnS _ _ _ L2 R1). 
Defined.                         

Lemma bop_is_ann_equal : ∀ (S : Type) 
                        (r : brel S )
                        (symS : brel_symmetric S r)
                        (trnS : brel_transitive S r)
                        (b : binary_op S )
                        (x : S )
                        (y : S )
                        (p : bop_is_ann S r b x)        
                        (q : bop_is_ann S r b y), r x y = true.             
Proof. intros S r symS trnS b x y p q.  
       destruct (q x) as [_ R1]. destruct (p y) as [L2 _]. 
       apply symS in L2. apply (trnS _ _ _ L2 R1). 
Defined.


Lemma bop_not_is_id_intro (S : Type) (r : brel S) (id s : S) (bS : binary_op S)
                          (symS : brel_symmetric S r) (trnS : brel_transitive S r) : bop_is_id S r bS id -> r id s = false -> bop_not_is_id S r bS s.
Proof. intros ID F. exists id. destruct (ID s) as [L R]. 
       left. case_eq(r (bS s id) id); intro J; auto. apply symS in J.
       assert (K := trnS _ _ _ J R). rewrite K in F. exact F. 
Defined.

Lemma bop_not_is_ann_intro (S : Type) (r : brel S) (a s : S) (bS : binary_op S)
                          (symS : brel_symmetric S r) (trnS : brel_transitive S r) : bop_is_ann S r bS a -> r a s = false -> bop_not_is_ann S r bS s.
Proof. intros ID F. exists a. destruct (ID s) as [L R]. 
       left. case_eq(r (bS s a) s); intro J; auto. apply symS in R.
       assert (K := trnS _ _ _ R J). rewrite K in F. exact F. 
Defined.

End Id_Ann.   


Section Addition.

Open Scope nat_scope. 
(* 
plus_Snm_nSm: ∀ n m : nat, S n + m = n + S m
plus_Sn_m: ∀ n m : nat, S n + m = S (n + m)
*) 
Lemma plus_SS : ∀ s t : nat, S s + S t = S(S(s + t)). 
Proof. intros s t. rewrite plus_Snm_nSm. 
       rewrite plus_comm at 1. 
       rewrite plus_Sn_m. 
       rewrite plus_Sn_m. 
       rewrite plus_comm at 1. 
       reflexivity. 
Defined. 

Lemma injection_S : ∀ s t : nat, s = t -> S s = S t. 
Proof. intros s t H. rewrite H. reflexivity. Defined. 

Lemma injective_S : ∀ s t : nat, S s = S t -> s = t. 
Proof. intros s t H. injection H. auto. Defined. 
  
End Addition.   

Section Property_Interactions.

Definition bop_commutative_dual (S : Type) (r : brel S) (b : binary_op S) := 
    ∀ s t u : S, (r (b s t) u = false) → (r (b t s) u = false). 

Lemma bop_commutative_implies_dual : ∀ (S: Type) (r : brel S) (b : binary_op S), 
      brel_transitive S r -> 
      bop_commutative S r b -> bop_commutative_dual S r b. 
Proof. intros S r b transS commS s t u H. 
       assert (C := commS s t). 
       assert (D := brel_transititivity_implies_dual S r transS). 
       unfold brel_transitive_dual in D. 
       apply (D (b s t) (b t s) u C H).     
Defined. 

(*
u(s + t) = u (t + s)
         = u ((u t) + s)
         = u (s + (u t))
*) 
Lemma bop_commutative_left_implies_right_invariant : 
   ∀ (S : Type) (r : brel S) (u : unary_op S) (b : binary_op S),
     brel_symmetric S r →
     brel_transitive S r →
     bop_commutative S r b →
     uop_congruence S r u →
     uop_bop_left_invariant S r u b →
        uop_bop_right_invariant S r u b.  
Proof. intros S r u b symS transS comm_b cong_u. 
       unfold uop_bop_left_invariant, uop_bop_right_invariant. 
       intros H s t. 
       assert (A := comm_b s t). 
       assert (B := comm_b s (u t)). 
       assert (Au := cong_u _ _ A). 
       assert (Bu := cong_u _ _ B). apply symS in Bu. 
       assert (Hu := H t s). 
       assert (T1 := transS _ _ _ Au Hu). 
       assert (T2 := transS _ _ _ T1 Bu). assumption. 
Defined. 


(* 
u((u s) + (u t)) = u((u s) + t) = u(s + t)    
*) 
Lemma uop_bop_invariant_left_intro : 
   ∀ (S : Type) (r : brel S) (u : unary_op S) (b : binary_op S),
     brel_symmetric S r →
     brel_transitive S r →
     bop_commutative S r b →
     uop_congruence S r u →
     uop_bop_left_invariant S r u b → uop_bop_invariant S r u b.  
Proof. intros S r u b symS transS comm_b cong_u. unfold uop_bop_left_invariant, uop_bop_invariant. 
       intros I_l s t. 
       assert (I_r := bop_commutative_left_implies_right_invariant S r u b symS transS comm_b cong_u I_l).      
       unfold uop_bop_left_invariant in I_r. unfold uop_bop_right_invariant in I_r. 
       assert(A := I_l s t). 
       assert(B := I_r (u s) t). 
       assert(T := transS _ _ _ A B). assumption. 
Defined. 


(* I *) 

Lemma bop_idempotent_implies_not_anti_left : ∀ (S : Type) (r : brel S) (b : binary_op S) (s : S) , 
       brel_symmetric S r -> 
       bop_idempotent S r b -> 
       bop_not_anti_left S r b. 
Proof. intros S r b s symS idemS. 
       unfold bop_not_anti_left. 
       exists (cef_idempotent_implies_not_anti_left s); simpl. 
       assert (fact := idemS s). apply symS in fact. assumption. 
Defined. 

Lemma bop_idempotent_implies_not_anti_right : ∀ (S : Type) (r : brel S) (b : binary_op S) (s : S), 
       brel_symmetric S r -> 
       bop_idempotent S r b -> 
       bop_not_anti_right S r b. 
Proof. intros S r b s symS idemS. exists (cef_idempotent_implies_not_anti_right s); simpl. 
       assert (fact := idemS s). apply symS in fact. assumption. 
Defined. 


(* S *) 

Lemma bop_selective_implies_idempotent : ∀ (S : Type) (r : brel S) (b : binary_op S),
        bop_selective S r b -> bop_idempotent S r b.
Proof. intros S r b selS x. destruct (selS x x) as [H | H]; assumption. Defined. 


Lemma bop_selective_implies_not_anti_left : ∀ (S : Type) (r : brel S) (b : binary_op S) (s : S), 
       brel_symmetric S r -> 
       bop_selective S r b -> 
       bop_not_anti_left S r b. 
Proof. intros S r b s symS idemS. 
       apply bop_idempotent_implies_not_anti_left; auto. 
       apply bop_selective_implies_idempotent; auto. 
Defined. 


Lemma bop_selective_implies_not_anti_right : ∀ (S : Type) (r : brel S) (b : binary_op S) (s : S), 
       brel_symmetric S r -> 
       bop_selective S r b -> 
       bop_not_anti_right S r b. 
Proof. intros S r b s symS idemS. 
       apply bop_idempotent_implies_not_anti_right; auto. 
       apply bop_selective_implies_idempotent; auto. 
Defined. 

(* i *) 
Lemma bop_not_idempotent_implies_not_selective : ∀ (S : Type) (r : brel S) (b : binary_op S),
        bop_not_idempotent S r b -> bop_not_selective S r b. 
Proof. intros S r b [i Pi]. exists (i, i). auto. Defined. 


(* K *) 

Lemma bop_left_cancellative_implies_not_left_constant : 
    ∀ (S : Type) (r : brel S) (b : binary_op S) (s : S) (f : S -> S), 
       brel_not_trivial S r f -> 
       bop_left_cancellative S r b -> 
          bop_not_left_constant S r b. 
Proof. intros S r b s f Pf lcS. 
       unfold bop_not_left_constant. 
       exists (cef_left_cancellative_implies_not_left_constant s f). 
       unfold cef_left_cancellative_implies_not_left_constant. 
       case_eq(r (b s s) (b s (f s))); intro H. 
          apply lcS in H. 
          destruct (Pf s) as [L R]. 
          rewrite H in L. 
          assumption. 
          reflexivity. 
Defined. 

Lemma bop_right_cancellative_implies_not_right_constant : 
    ∀ (S : Type) (r : brel S) (b : binary_op S) (s : S) (f : S -> S), 
       brel_not_trivial S r f -> 
       bop_right_cancellative S r b -> 
          bop_not_right_constant S r b. 
Proof. intros S r b s f Pf rcS. 
       unfold bop_not_right_constant. 
       exists (cef_right_cancellative_implies_not_right_constant s f). 
       unfold cef_right_cancellative_implies_not_right_constant. 
       case_eq(r (b s s) (b (f s) s)); intro H. 
          apply rcS in H. 
          destruct (Pf s) as [L R]. 
          rewrite H in L. 
          assumption. 
          reflexivity. 
Defined. 

Lemma bop_left_cancellative_implies_not_exists_ann : 
   ∀ (S : Type) (r : brel S) (b : binary_op S) (s : S) (f : S -> S), 
      brel_symmetric S r -> 
      brel_transitive S r -> 
      brel_not_trivial S r f -> 
      bop_left_cancellative S r b -> 
         bop_not_exists_ann S r b. 
Proof. intros S r b s f symS transS Pf lcS a. 
       destruct (Pf s) as [L R]. 
       case_eq(r (b a s) a); case_eq(r (b a (f s)) a); intros H K. 
          apply symS in K. 
          assert (T := transS _ _ _ H K). 
          apply lcS in T. 
          rewrite T in R. discriminate. 
          exists (f s).  left. assumption. 
          exists s. left. assumption. 
          exists s. left. assumption. 
Qed. 

Lemma bop_right_cancellative_implies_not_exists_ann : 
   ∀ (S : Type) (r : brel S) (b : binary_op S) (s : S) (f : S -> S), 
      brel_symmetric S r -> 
      brel_transitive S r -> 
      brel_not_trivial S r f -> 
      bop_right_cancellative S r b -> 
         bop_not_exists_ann S r b. 
Proof. intros S r b s f symS transS Pf lcS a. 
       destruct (Pf s) as [L R]. 
       case_eq(r (b s a) a); case_eq(r (b (f s) a) a); intros H K. 
          apply symS in K. 
          assert (T := transS _ _ _ H K). 
          apply lcS in T. 
          rewrite T in R. discriminate. 
          exists (f s).  right. assumption. 
          exists s. right. assumption. 
          exists s. right. assumption. 
Qed. 


Lemma bop_left_cancellative_implies_any_idempotent_is_left_id : 
   ∀ (S : Type) (r : brel S) (b : binary_op S), 
      brel_reflexive S r -> 
      brel_symmetric S r -> 
      brel_transitive S r -> 
      bop_associative S r b -> 
      bop_congruence S r b -> 
      bop_left_cancellative S r b -> 
      ∀ i : S, r (b i i) i = true -> ∀ s : S, r s (b i s) = true. 
Proof. intros S r b refS symS transS assS congS lcS i H s. 
       assert (A := assS i i s). 
       assert (B : r (b i s) (b (b i i) s) = true). 
           assert (C := congS _ _ _ _ H (refS s)). 
           apply symS in C.  
           assumption. 
       assert (C := transS _ _ _ B A).        
       assert (D := lcS _ _ _ C). 
       assumption. 
Qed. 


Lemma bop_right_cancellative_implies_any_idempotent_is_right_id : 
   ∀ (S : Type) (r : brel S) (b : binary_op S), 
      brel_reflexive S r -> 
      brel_symmetric S r -> 
      brel_transitive S r -> 
      bop_associative S r b -> 
      bop_congruence S r b -> 
      bop_right_cancellative S r b -> 
      ∀ i : S, r (b i i) i = true -> ∀ s : S, r s (b s i) = true. 
Proof. intros S r b refS symS transS assS congS lcS i H s. 
       assert (A := assS s i i). 
       assert (B : r (b s i) (b s (b i i)) = true). 
           assert (C := congS _ _ _ _ (refS s) H). 
           apply symS in C.  
           assumption. 
       apply symS in A. assert (C := transS _ _ _ B A).        
       assert (D := lcS _ _ _ C). 
       assumption. 
Qed. 


Lemma bop_cancellative_implies_idempotent_is_id : 
   ∀ (S : Type) (r : brel S) (b : binary_op S), 
      brel_reflexive S r -> 
      brel_symmetric S r -> 
      brel_transitive S r -> 
      bop_associative S r b -> 
      bop_congruence S r b -> 
      bop_left_cancellative S r b -> 
      bop_right_cancellative S r b -> 
      ∀ i : S, r (b i i) i = true -> bop_is_id S r b i. 
Proof. intros S r b refS symS transS assS congS lcS rcS i H s.      
       split; apply symS.
       apply bop_left_cancellative_implies_any_idempotent_is_left_id; auto. 
       apply bop_right_cancellative_implies_any_idempotent_is_right_id; auto. 
Defined. 



Lemma bop_cancellative_and_exists_id_imply_not_idempotent : 
   ∀ (S : Type) (r : brel S) (b : binary_op S) (x : S) (f : S -> S), 
      brel_not_trivial S r f -> 
      brel_reflexive S r -> 
      brel_symmetric S r -> 
      brel_transitive S r -> 
      bop_associative S r b -> 
      bop_congruence S r b -> 
      bop_left_cancellative S r b -> 
      bop_right_cancellative S r b -> 
      bop_exists_id S r b -> 
         bop_not_idempotent S r b. 
Proof. intros S r b x f Pf refS symS transS assS congS lcS rcS [i Pi]. 
       exists (cef_cancellative_and_exists_id_imply_not_idempotent r x i f). 
       unfold cef_cancellative_and_exists_id_imply_not_idempotent. 
       case_eq(r x i); intro H. 
             case_eq(r (b (f x) (f x)) (f x)); intro F. 
                destruct (Pf x) as [L R].
                assert (A : bop_is_id S r b (f x)). 
                   apply bop_cancellative_implies_idempotent_is_id; auto.
                assert (B : r i (f x) = true). 
                   apply (bop_is_id_equal S r symS transS b); auto.
                assert (C := transS _ _ _ H B). 
                rewrite C in L. 
                assumption. 
                reflexivity. 
             case_eq(r (b x x) x); intro F. 
                assert (A : bop_is_id S r b x). 
                   apply bop_cancellative_implies_idempotent_is_id; auto.
                assert (B : r i x = true). 
                   apply (bop_is_id_equal S r symS transS b); auto.
                apply symS in B. 
                rewrite B in H. 
                assumption. 
                reflexivity. 
Defined. 


Lemma bop_cancellative_and_not_exists_id_imply_not_idempotent : 
   ∀ (S : Type) (r : brel S) (b : binary_op S) (x : S) (f : S -> S), 
      brel_not_trivial S r f -> 
      brel_reflexive S r -> 
      brel_symmetric S r -> 
      brel_transitive S r -> 
      bop_associative S r b -> 
      bop_congruence S r b -> 
      bop_left_cancellative S r b -> 
      bop_right_cancellative S r b -> 
      bop_not_exists_id S r b -> 
         bop_not_idempotent S r b. 
Proof. intros S r b x f Pf refS symS transS assS congS lcS rcS no_id. 
       exists x. 
          case_eq(r (b x x) x); intro F. 
             assert (A : bop_is_id S r b x). 
                apply bop_cancellative_implies_idempotent_is_id; auto.
             destruct (no_id x) as [y [J | J]]; destruct (A y) as [L R]. 
                rewrite L in J. assumption. 
                rewrite R in J. assumption. 
             reflexivity. 
Defined. 


Lemma bop_cancellative_implies_not_idempotent : 
  ∀ (S : Type) (r : brel S) (b : binary_op S) (s : S) (f : S -> S),
      brel_not_trivial S r f -> 
      brel_reflexive S r -> 
      brel_symmetric S r -> 
      brel_transitive S r -> 
      bop_associative S r b -> 
      bop_congruence S r b -> 
      bop_left_cancellative S r b -> 
      bop_right_cancellative S r b -> 
      bop_exists_id_decidable S r b -> 
         bop_not_idempotent S r b. 
Proof. intros S r b s f Pf refS symS transS assS congS lcS rcS [ id | no_id]. 
       apply (bop_cancellative_and_exists_id_imply_not_idempotent S r b s f); auto.
       apply (bop_cancellative_and_not_exists_id_imply_not_idempotent S r b s f); auto. 
Defined. 

(* C *) 
Lemma bop_commutative_and_not_is_left_imply_not_is_right  : 
      ∀ (S: Type) (r : brel S) (b : binary_op S), 
         brel_transitive S r -> bop_commutative S r b -> 
            bop_not_is_left S r b -> bop_not_is_right S r b.
Proof. intros S r b transS commS [[s1 s2] P]. exists (s2, s1). 
       assert (A := commS s1 s2). 
       apply (brel_transititivity_implies_dual _ _ transS _ _ _ A P). 
Defined. 


Lemma bop_commutative_and_left_constant_imply_right_constant  : 
      ∀ (S: Type) (r : brel S) (b : binary_op S), 
         brel_transitive S r -> 
         bop_commutative S r b -> 
         bop_left_constant S r b -> bop_right_constant S r b.
Proof. intros S r b tranS commS lcS s t u.
       exact (tranS _ _ _ (commS t s) (tranS _ _ _ (lcS s t u) (commS s u))). 
Qed. 

Lemma bop_commutative_and_not_left_constant_imply_not_right_constant  : 
      ∀ (S: Type) (r : brel S) (b : binary_op S), 
         brel_symmetric S r -> 
         brel_transitive S r -> 
         bop_commutative S r b -> 
            bop_not_left_constant S r b -> bop_not_right_constant S r b.
Proof. intros S r b symS transS commS [ p P]. exists p. 
       destruct p as [s1 [s2 s3]]. 
       assert (A := commS s1 s2). 
       assert (B := brel_transititivity_implies_dual _ _ transS _ _ _ A P). 
       assert (C := brel_symmetric_implies_dual _ _ symS _ _ B). 
       assert (D := commS s1 s3). 
       assert (E := brel_transititivity_implies_dual _ _ transS _ _ _ D C). 
       assert (F := brel_symmetric_implies_dual _ _ symS _ _ E). 
       assumption. 
Defined. 


Lemma bop_commutative_and_not_anti_left_imply_not_anti_right : 
      ∀ (S: Type) (r : brel S) (b : binary_op S), 
         brel_transitive S r -> 
         bop_commutative S r b -> 
            bop_not_anti_left S r b -> bop_not_anti_right S r b.
Proof. intros S r b transS commS [[s1 s2] P]. exists (s1, s2). 
       assert (A := commS s1 s2). 
       assert (B := transS _ _ _ P A). 
       assumption. 
Defined. 



Lemma bop_commutative_and_left_cancellative_imply_right_cancellative  : 
      ∀ (S: Type) (r : brel S) (b : binary_op S), 
         brel_transitive S r -> 
         bop_commutative S r b -> 
            bop_left_cancellative S r b -> bop_right_cancellative S r b.
Proof. intros S r b transS commS lcS s1 s2 s3 H. 
       assert (A : r (b s1 s2) (b s1 s3) = true). 
          assert (B := commS s1 s2). 
          assert (C := commS s3 s1). 
          assert (D := transS _ _ _ B H). 
          assert (E := transS _ _ _ D C). 
          assumption. 
       apply lcS in A. 
       assumption. 
Defined. 

Lemma bop_commutative_and_not_left_cancellative_imply_not_right_cancellative  : 
      ∀ (S: Type) (r : brel S) (b : binary_op S), 
         brel_symmetric S r -> 
         brel_transitive S r -> 
         bop_commutative S r b -> 
            bop_not_left_cancellative S r b -> bop_not_right_cancellative S r b.
Proof. intros S r b symS transS commS [ p P ]. 
       exists p. 
       destruct p as [s1 [s2 s3]]. destruct P as [L R]. split. 
          assert (A := commS s2 s1). 
          assert (B := commS s1 s3). 
          assert (C := transS _ _ _ A L). 
          assert (D := transS _ _ _ C B). 
          assumption. 
          assumption. 
Defined. 

Lemma bop_commutative_implies_not_is_left  : ∀ (S: Type) (r : brel S) (b : binary_op S) (s : S) (f : S -> S), 
     brel_not_trivial S r f -> 
     brel_symmetric S r -> 
     brel_transitive S r -> 
        bop_commutative S r b -> bop_not_is_left S r b. 
Proof. intros S r b s f Pf symS transS commS. 
       exists (cef_commutative_implies_not_is_left r b s f).
       destruct (Pf s) as [L R].
       assert (C := commS s (f s)). 
       unfold cef_commutative_implies_not_is_left. 
       case_eq (r (b (f s) s) s); intro H. 
          apply (brel_transititivity_implies_dual _ _ transS _ _ _ (symS _ _ H) L).  
          apply (brel_transititivity_implies_dual _ _ transS _ _ _ (symS _ _ C) H).  
Defined. 


Lemma bop_commutative_implies_not_is_right  : ∀ (S: Type) (r : brel S) (b : binary_op S) (s : S) (f : S -> S), 
     brel_not_trivial S r f -> 
     brel_symmetric S r -> 
     brel_transitive S r -> 
        bop_commutative S r b -> bop_not_is_right S r b. 
Proof. intros S r b s f Pf symS transS commS. 
       exists (cef_commutative_implies_not_is_right r b s f). 
       destruct (Pf s) as [L R].
       assert (C := commS (f s) s). 
       unfold cef_commutative_implies_not_is_right. 
       case_eq (r (b (f s) s) s); intro H. 
          apply symS in H.  
          apply brel_symmetric_implies_dual in R; auto. 
          assert (A := brel_transititivity_implies_dual _ _ transS _ _ _ H R).  
          apply (brel_transititivity_implies_dual _ _ transS _ _ _ C A).  
          assumption. 
Defined. 


(* N *) 

Lemma exists_id_implies_not_left_constant : ∀ (S : Type) (r : brel S) (b : binary_op S) (s : S) (f : S -> S), 
               brel_congruence S r r -> 
               brel_not_trivial S r f-> 
               bop_exists_id S r b -> 
                  bop_not_left_constant S r b. 
Proof. intros S r b s f congS Pf [i Pi].
       exists (i, (s, f s)).               
       destruct (Pi s) as [Ls Rs]. 
       destruct (Pi (f s)) as [Lf Rf]. 
       destruct (Pf s) as [L R]. 
       assert (C := congS _ _ _ _ Ls Lf). 
       rewrite L in C. 
       assumption. 
Defined. 


Lemma exists_id_implies_not_right_constant : ∀ (S : Type) (r : brel S) (b : binary_op S) (s : S) (f : S -> S), 
               brel_congruence S r r -> 
               brel_not_trivial S r f -> 
               bop_exists_id S r b -> 
                  bop_not_right_constant S r b. 
Proof. intros S r b  s f congS Pf [i Pi].
       exists (i, (s, f s)).        
       destruct (Pi s) as [Ls Rs]. 
       destruct (Pi (f s)) as [Lf Rf]. 
       destruct (Pf s) as [L R]. 
       assert (C := congS _ _ _ _ Rs Rf). 
       rewrite L in C. 
       assumption. 
Defined. 

(* really : exists_right_id ... *) 
Lemma exists_id_implies_not_anti_left : ∀ (S : Type) (r : brel S) (b : binary_op S), 
               brel_symmetric S r -> 
               S -> 
               bop_exists_id S r b -> 
                  bop_not_anti_left S r b. 
Proof. intros S r b symS s [i Pi]. 
       exists (s, i). destruct (Pi s) as [L R]. 
       apply symS in R. assumption. 
Defined. 


(* really : exists_left_id ... *) 
Lemma exists_id_implies_not_anti_right : ∀ (S : Type) (r : brel S) (b : binary_op S), 
               brel_symmetric S r -> 
               S -> 
               bop_exists_id S r b -> 
                  bop_not_anti_right S r b. 
Proof. intros S r b symS s [i Pi]. 
       exists (s, i). destruct (Pi s) as [L R]. 
       apply symS in L. assumption. 
Defined. 


Lemma exists_id_implies_not_is_left : ∀ (S : Type) (r : brel S) (b : binary_op S) (f : S -> S), 
               brel_symmetric S r -> 
               brel_transitive S r -> 
               brel_not_trivial S r f -> 
               bop_exists_id S r b -> 
                  bop_not_is_left S r b. 
Proof. intros S r b f symS transS Pf [i Pi].
       exists (i, f i).       
       destruct (Pf i) as [L1 R1]. 
       destruct (Pi (f i)) as [L2 R2]. 
       apply symS in L2. 
       apply (brel_transititivity_implies_dual _ _ transS _ _ _ L2 R1). 
Defined. 

Lemma exists_id_implies_not_is_right : ∀ (S : Type) (r : brel S) (b : binary_op S) (f : S -> S), 
               brel_symmetric S r -> 
               brel_transitive S r -> 
               brel_not_trivial S r f -> 
               bop_exists_id S r b -> 
                  bop_not_is_right S r b. 
Proof. intros S r b f symS transS Pf [i Pi].
       exists (f i, i).       
       destruct (Pf i) as [L1 R1]. 
       destruct (Pi (f i)) as [L2 R2]. 
       apply symS in R2. 
       apply (brel_transititivity_implies_dual _ _ transS _ _ _ R2 R1). 
Defined. 

(* A *) 

Lemma exists_ann_implies_not_anti_left : ∀ (S : Type) (r : brel S) (b : binary_op S), 
               brel_symmetric S r -> 
               S -> 
               bop_exists_ann S r b -> 
                  bop_not_anti_left S r b. 
Proof. intros S r b symS s [a Pa]. 
       unfold bop_not_anti_left. 
       unfold bop_is_ann in Pa. 
       exists (a, s). destruct (Pa s) as [L R]. 
       apply symS in L. assumption. 
Defined. 


Lemma exists_ann_implies_not_is_left : ∀ (S : Type) (r : brel S) (b : binary_op S) (f : S -> S), 
               brel_symmetric S r -> 
               brel_transitive S r -> 
               brel_not_trivial S r f -> 
               bop_exists_ann S r b -> 
                  bop_not_is_left S r b. 
Proof. intros S r b f symS transS Pf [a Pa]. 
       destruct (Pf a) as [L1 R1]. 
       destruct (Pa (f a)) as [L2 R2]. 
       unfold bop_not_is_left. 
       unfold bop_is_ann in Pa. 
       exists (f a, a).
       apply (brel_transititivity_implies_dual _ _ transS _ _ _ (symS _ _ R2) L1). 
Defined. 

Lemma exists_ann_implies_not_anti_right : ∀ (S : Type) (r : brel S) (b : binary_op S), 
               brel_symmetric S r -> 
               S  -> 
               bop_exists_ann S r b -> 
                  bop_not_anti_right S r b. 
Proof. intros S r b symS s [a Pa]. 
       destruct (Pa s) as [L R]. 
       exists (a, s). 
       apply symS. assumption. 
Defined. 

Lemma exists_ann_implies_not_is_right : ∀ (S : Type) (r : brel S) (b : binary_op S) (f : S -> S), 
               brel_symmetric S r -> 
               brel_transitive S r -> 
               brel_not_trivial S r f -> 
               bop_exists_ann S r b -> 
                  bop_not_is_right S r b. 
Proof. intros S r b f symS transS Pf [a Pa]. 
       destruct (Pf a) as [L1 R1]. 
       destruct (Pa (f a)) as [L2 R2]. 
       unfold bop_not_is_right. 
       unfold bop_is_ann in Pa. 
       exists (a, f a).
       apply (brel_transititivity_implies_dual _ _ transS _ _ _ (symS _ _ L2) L1). 
Defined. 



Lemma exists_ann_implies_not_left_cancellative : 
     ∀ (S : Type) (r : brel S) (b : binary_op S) (s : S) (f : S -> S), 
       brel_reflexive S r -> 
       brel_congruence S r r -> 
       brel_not_trivial S r f -> 
       bop_exists_ann S r b -> 
                  bop_not_left_cancellative S r b. 
Proof. intros S r b s f refS congS Pf [a Pa]. 
       destruct (Pf s) as [L1 R1]. 
       destruct (Pa s) as [L2 R2]. 
       destruct (Pa (f s)) as [L3 R4]. 
       exists (a, (s, f s)). split. 
          assert (C := congS _ _ _ _ L2 L3). 
          rewrite (refS a) in C. 
          assumption.        
          assumption.        
Defined. 

Lemma exists_ann_implies_not_right_cancellative : 
     ∀ (S : Type) (r : brel S) (b : binary_op S) (s : S) (f : S -> S), 
       brel_reflexive S r -> 
       brel_congruence S r r -> 
       brel_not_trivial S r f -> 
       bop_exists_ann S r b -> 
                  bop_not_right_cancellative S r b. 
Proof. intros S r b s f refS congS Pf [a Pa]. 
       destruct (Pf s) as [L1 R1]. 
       destruct (Pa s) as [L2 R2]. 
       destruct (Pa (f s)) as [L3 R4]. 
       exists (a, (s, f s)). split. 
          assert (C := congS _ _ _ _ R2 R4). 
          rewrite (refS a) in C. 
          assumption.        
          assumption.        
Defined.



(* CI *) 

Lemma bop_idempotent_and_commutative_imply_not_left_constant : 
    ∀ (S : Type) (r : brel S) (b : binary_op S) (s : S) (f : S -> S), 
       brel_not_trivial S r f -> 
       brel_congruence S r r -> 
       brel_reflexive S r -> 
       brel_transitive S r -> 
       bop_idempotent S r b -> 
       bop_commutative S r b -> 
          bop_not_left_constant S r b. 
Proof. intros S r b s f Pf congS refS transS idemS commS. 
       exists (cef_idempotent_and_commutative_imply_not_left_constant r b s f). 
       unfold cef_idempotent_and_commutative_imply_not_left_constant. 
       assert (A := idemS s). 
       assert (B := idemS (f s)). 
       case_eq(r (b (f s) s) s); intro H.
          assert (C := congS _ _ _ _ H B). 
          destruct (Pf s) as [L R]. 
          rewrite L in C.
          assumption. 
          case_eq(r (b s (f s)) (f s)); intro J.
             assert (C := congS _ _ _ _ J A). 
             destruct (Pf s) as [L R]. 
             rewrite R in C.
             assumption. 
             assert (C := commS (f s) s). 
             assert (D := brel_transititivity_implies_dual _ _ transS _ _ _ C H). 
             assert (E := congS _ _ _ _ (refS (b s (f s))) A). 
             rewrite D in E.
             assumption.                          
Defined. 


Lemma bop_idempotent_and_commutative_imply_not_right_constant : 
    ∀ (S : Type) (r : brel S) (b : binary_op S) (s : S) (f : S -> S), 
       brel_not_trivial S r f -> 
       brel_congruence S r r -> 
       brel_reflexive S r -> 
       brel_symmetric S r -> 
       brel_transitive S r -> 
       bop_idempotent S r b -> 
       bop_commutative S r b -> 
          bop_not_right_constant S r b. 
Proof. intros S r b s f Pf congS refS symS transS idemS commS. 
       apply bop_commutative_and_not_left_constant_imply_not_right_constant; auto. 
       apply (bop_idempotent_and_commutative_imply_not_left_constant S r b s f); auto. 
Defined. 


(* CS *) 

Lemma bop_selective_and_commutative_imply_not_left_constant : 
    ∀ (S : Type) (r : brel S) (b : binary_op S) (s : S) (f : S -> S), 
       brel_not_trivial S r f -> 
       brel_congruence S r r -> 
       brel_reflexive S r -> 
       brel_transitive S r -> 
       bop_selective S r b -> 
       bop_commutative S r b -> 
          bop_not_left_constant S r b. 
Proof. intros S r b s f Pf congS refS transS selS commS. 
       apply (bop_idempotent_and_commutative_imply_not_left_constant S r b s f); auto. 
       apply bop_selective_implies_idempotent; auto. 
Defined. 


Lemma bop_selective_and_commutative_imply_not_right_constant : 
    ∀ (S : Type) (r : brel S) (b : binary_op S) (s : S) (f : S -> S), 
       brel_not_trivial S r f -> 
       brel_congruence S r r -> 
       brel_reflexive S r -> 
       brel_symmetric S r -> 
       brel_transitive S r -> 
       bop_selective S r b -> 
       bop_commutative S r b -> 
          bop_not_right_constant S r b. 
Proof. intros S r b s f Pf congS refS symS transS selS commS. 
       apply (bop_idempotent_and_commutative_imply_not_right_constant S r b s f); auto. 
       apply bop_selective_implies_idempotent; auto. 
Defined. 



Lemma bop_selective_and_commutative_imply_not_left_cancellative : 
   ∀ (S : Type) (r : brel S) (b : binary_op S) (s : S) (f : S -> S),
      brel_symmetric S r -> 
      brel_transitive S r -> 
      brel_not_trivial S r f -> 
      bop_selective S r b -> 
      bop_commutative S r b -> 
      bop_not_left_cancellative S r b.
Proof. intros S r b s f symS transS Pf selS commS. 
       exists (cef_selective_and_commutative_imply_not_left_cancellative  r b s f). 
       assert (idemS := bop_selective_implies_idempotent S r b selS).
       destruct (Pf s) as [L R]. 
       unfold cef_selective_and_commutative_imply_not_left_cancellative. 
       destruct (selS s (f s)) as [H | H]. 
          rewrite H. split. 
             assert (I := idemS s). 
             apply symS in H. 
             assert (T := transS _ _ _ I H). 
             assumption. 
             assumption. 
          assert (F : r (b s (f s)) s = false). 
             apply symS in H. 
             assert (A := brel_transititivity_implies_dual _ _ transS _ _ _ H R). 
             assumption. 
          rewrite F. split. 
             assert (I := idemS (f s)). 
             apply symS in H. 
             assert (T1 := transS _ _ _ I H). 
             assert (C := commS s (f s)). 
             assert (T2 := transS _ _ _ T1 C). 
             assumption. 
             assumption. 
Defined. 


Lemma bop_selective_and_commutative_imply_not_right_cancellative : 
   ∀ (S : Type) (r : brel S) (b : binary_op S) (s : S) (f : S -> S),
      brel_symmetric S r -> 
      brel_transitive S r -> 
      brel_not_trivial S r f -> 
      bop_selective S r b -> 
      bop_commutative S r b -> 
         bop_not_right_cancellative S r b. 
Proof. intros S r b s f symS transS Pf selS commS. 
       apply bop_commutative_and_not_left_cancellative_imply_not_right_cancellative; auto. 
       apply (bop_selective_and_commutative_imply_not_left_cancellative S r b s f); auto. 
Defined. 



(* CIs *) 


Lemma bop_idempotent_and_commutative_and_not_selective_imply_not_left_cancellative: 
    ∀ (S : Type) (r : brel S) (b : binary_op S), 
       brel_congruence S r r -> 
       brel_reflexive S r -> 
       brel_symmetric S r -> 
       brel_transitive S r -> 
       bop_associative S r b -> 
       bop_congruence S r b -> 
       bop_idempotent S r b -> 
       bop_commutative S r b -> 
       bop_not_selective S r b -> 
          bop_not_left_cancellative S r b. 
Proof. intros S r b congS refS symS transS assS b_congS idemS commS [[s1 s2]  [H1 H2]]. 
       exists (cef_idempotent_and_commutative_and_not_selective_imply_not_left_cancellative  b s1 s2). 
       unfold cef_idempotent_and_commutative_and_not_selective_imply_not_left_cancellative. split. 
          assert (A : r (b (b s1 s2) s1) (b s1 s2) = true). 
             assert (B := b_congS _ _ _ _ (commS s1 s2) (refS s1)). 
             assert (C := assS s2 s1 s1). 
             assert (D := b_congS _ _ _ _ (refS s2) (idemS s1)). 
             assert (E := commS s2 s1). 
             assert (F := transS _ _ _ B C). 
             assert (G := transS _ _ _ F D). 
             assert (H := transS _ _ _ G E). 
             assumption. 
          assert (B : r (b (b s1 s2) s2) (b s1 s2) = true). 
             assert (C := assS s1 s2 s2). 
             assert (D := b_congS _ _ _ _ (refS s1) (idemS s2)). 
             assert (T := transS _ _ _ C D). 
             assumption. 
          assert (C := congS _ _ _ _ A B). 
          rewrite (refS (b s1 s2)) in C. 
          assumption. 
          case_eq(r s1 s2); intro F. 
             assert (I := idemS s1). 
             assert (C := b_congS _ _ _ _ (refS s1) F). 
             apply symS in C. 
             assert (T := transS _ _ _ C I). 
             rewrite T in H1.
             assumption. 
             reflexivity. 
Defined. 

Lemma bop_idempotent_and_commutative_and_not_selective_imply_not_right_cancellative: 
    ∀ (S : Type) (r : brel S) (b : binary_op S), 
       brel_congruence S r r -> 
       brel_reflexive S r -> 
       brel_symmetric S r -> 
       brel_transitive S r -> 
       bop_associative S r b -> 
       bop_congruence S r b -> 
       bop_idempotent S r b -> 
       bop_commutative S r b -> 
       bop_not_selective S r b -> 
          bop_not_right_cancellative S r b. 
Proof. intros S r b congS refS symS transS assS b_congS idemS commS not_selS. 
       apply bop_commutative_and_not_left_cancellative_imply_not_right_cancellative; auto. 
       apply bop_idempotent_and_commutative_and_not_selective_imply_not_left_cancellative; auto. 
Defined. 


(* CI(S || s) *) 

Lemma bop_idempotent_and_commutative_and_selective_decidable_imply_not_left_cancellative: 
    ∀ (S : Type) (r : brel S) (b : binary_op S) (s : S) (f : S -> S), 
       brel_congruence S r r -> 
       brel_not_trivial S r f -> 
       brel_reflexive S r -> 
       brel_symmetric S r -> 
       brel_transitive S r -> 
       bop_associative S r b -> 
       bop_congruence S r b -> 
       bop_idempotent S r b -> 
       bop_commutative S r b -> 
       bop_selective_decidable S r b -> 
          bop_not_left_cancellative S r b. 
Proof. intros S r b s f congS Pf refS symS transS assS b_congS idemS commS [selS | not_selS]. 
       apply (bop_selective_and_commutative_imply_not_left_cancellative S r b s f); auto. 
       apply bop_idempotent_and_commutative_and_not_selective_imply_not_left_cancellative; auto. 
Defined. 

Lemma bop_idempotent_and_commutative_and_selective_decidable_imply_not_right_cancellative: 
    ∀ (S : Type) (r : brel S) (b : binary_op S) (s : S) (f : S -> S), 
       brel_congruence S r r -> 
       brel_not_trivial S r f -> 
       brel_reflexive S r -> 
       brel_symmetric S r -> 
       brel_transitive S r -> 
       bop_associative S r b -> 
       bop_congruence S r b -> 
       bop_idempotent S r b -> 
       bop_commutative S r b -> 
       bop_selective_decidable S r b -> 
          bop_not_right_cancellative S r b. 
Proof. intros S r b s f congS Pf refS symS transS assS b_congS idemS commS d_selS. 
       apply bop_commutative_and_not_left_cancellative_imply_not_right_cancellative; auto. 
       apply (bop_idempotent_and_commutative_and_selective_decidable_imply_not_left_cancellative S r b s f); auto. 
Defined. 


End Property_Interactions.   


Section Bottoms. 
Open Scope list_scope.

(* because the definitions have changed too often .... *)

(*
Lemma yet_another_sanity_check (S : Type) (rS : brel S) (bS : binary_op S)
      (sym : brel_symmetric S rS)
      (comm : bop_commutative S rS bS) 
      (bf : something_is_finite S rS bS)
      (bnf : something_not_is_finite S rS bS) : true = false.
Proof. destruct bf as [[BOTTOMS w] [A B]].
       destruct bnf as [F C].
       destruct (C BOTTOMS A) as [D E].
       destruct (B (F BOTTOMS)) as [G | G].
          rewrite G in D. discriminate D.
          destruct G as [G1 [G2 G3]].
          assert (H := E _ G1). 
          destruct H as [H | H].
             rewrite H in G2. discriminate G2.
             rewrite H in G3. discriminate G3.
Defined.  

Lemma exists_ann_implies_something_is_finite (T : Type) (eq : brel T) (b : binary_op T)
      (cong : bop_congruence T eq b)
      (ref : brel_reflexive T eq)
      (sym : brel_symmetric T eq)
      (trn : brel_transitive T eq)
      (comm : bop_commutative T eq b) 
      (idm : bop_idempotent T eq b)
      (g : T -> T)                 
      (Pg : brel_not_trivial T eq g)
      (ann : bop_exists_ann T eq b) : 
  something_is_finite T eq b.
Proof. destruct ann as [a P]. unfold something_is_finite. 
       exists (a::nil, λ t, a).  split. 
          intros s A t B. left. 
          apply (in_set_singleton_elim T eq sym) in A. 
          apply (in_set_singleton_elim T eq sym) in B. 
          assert (C := P a). destruct C as [_ C].
          assert (D := cong _ _ _ _ A B).                     
          assert (E := cong _ _ _ _ B A).                     
          apply sym in A. apply sym in B. apply sym in C. 
          assert (F := trn _ _ _ B (trn _ _ _ C E)). 
          assert (G := trn _ _ _ A (trn _ _ _ C D)). split. 
             exact F.
             exact G. 
          intro s.
          case_eq(eq a s); intro A. 
             left. apply (in_set_singleton_intro T eq sym). exact A. 
             right.
                assert (B := P s). destruct B as [B1 B2]. split. 
                apply (in_set_singleton_intro T eq sym). apply ref.
                split. apply sym. exact B1. 
                case_eq(eq s (b s a)); intro C; auto. 
                   destruct (P s) as [D E].
                   assert (F := trn _ _ _ C E). apply sym in F. 
                   rewrite F in A. discriminate A. 
Qed.


Lemma not_exists_ann_implies_something_is_not_finite (T : Type) (F : list T → T)  (eq : brel T) (b : binary_op T)
      (cong : bop_congruence T eq b)
      (ref : brel_reflexive T eq)
      (sym : brel_symmetric T eq)
      (trn : brel_transitive T eq)
      (comm : bop_commutative T eq b) 
      (idm : bop_idempotent T eq b)
      (g : T -> T)                 
      (Pg : brel_not_trivial T eq g)
      (ann : bop_not_exists_ann T eq b) : 
  something_not_is_finite T eq b.
Proof. unfold something_not_is_finite. exists F.
       unfold bop_not_exists_ann in ann. unfold bop_not_is_ann in ann. 
       intros B I. split.
          admit. 
          intros s C.          
Admitted.
*) 
End Bottoms. 
