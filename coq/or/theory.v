Require Import Coq.Bool.Bool.

Require Import CAS.coq.common.compute.

Require Import CAS.coq.theory.set. 

Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.theory. 

Require Import CAS.coq.or.properties.

Require Import CAS.coq.sg.and.
Require Import CAS.coq.sg.or. 

Section Computation. 

Definition below {S : Type} (lte : brel S) : brel S
    := λ a y, bop_and (lte y a) (uop_not(lte a y)).
  
Definition equiv {S : Type} (lte : brel S) : brel S
  := λ a b, bop_and (lte a b) (lte b a).

Definition incomp {S : Type} (lte : brel S) : brel S
  := λ a b, bop_and (uop_not(lte a b)) (uop_not (lte b a)).

Definition equiv_or_incomp {S : Type} (lte : brel S) : brel S
  := λ a b, bop_or (equiv lte a b) (incomp lte a b).

(* move this? *) 
Definition is_antichain (S : Type) (eq lte : brel S) (X : finite_set S) :=
∀ (s : S), in_set eq X s = true  -> ∀ (t : S), in_set eq X t = true -> equiv_or_incomp lte t s = true. 

End Computation. 



Section Complement.


Lemma brel_complement_asymmetric : ∀ (S : Type) (r : brel S), 
          (∀ s t : S, r s t = false → r t s = true) -> 
          brel_asymmetric S (brel_complement r).  
Proof. unfold brel_asymmetric, brel_complement. intros S r K s t J. 
       case_eq(r t s); intro Q. 
          compute. reflexivity. 
          rewrite (K _ _ Q) in J. compute in J. discriminate. 
Defined. 

Lemma brel_complement_irreflexive : ∀ (S : Type) (r : brel S), 
          brel_reflexive S r -> brel_irreflexive S (brel_complement r).  
Proof. unfold brel_reflexive, brel_irreflexive, brel_complement. intros S r H s. 
       rewrite (H s). compute. reflexivity. 
Defined. 

Lemma brel_complement_reflexive : ∀ (S : Type) (r : brel S), 
          brel_irreflexive S r -> brel_reflexive S (brel_complement r).  
Proof. unfold brel_reflexive, brel_irreflexive, brel_complement. intros S r H s. 
       rewrite (H s). compute. reflexivity. 
Defined. 


End Complement.   




Section Conjunction. 

Variable S  : Type. 
Variable r1 : brel S.
Variable r2 : brel S. 

Notation "a <&> b"  := (brel_conjunction a b) (at level 15).


Lemma brel_conjunction_irreflexive_left : ∀ (rS1 : brel S) (rS2 : brel S),  
        brel_irreflexive S rS1 -> 
           brel_irreflexive S (rS1 <&> rS2). 
Proof. 
     unfold brel_irreflexive, brel_conjunction. 
     intros rS1 rS2 irr s. rewrite (irr s). reflexivity. 
Defined. 


Lemma brel_conjunction_irreflexive_right : ∀ (rS1 : brel S) (rS2 : brel S),  
        brel_irreflexive S rS2 -> 
           brel_irreflexive S (rS1 <&> rS2). 
Proof. 
     unfold brel_irreflexive, brel_conjunction. 
     intros rS1 rS2 irr s. rewrite (irr s). apply andb_comm. 
Defined. 

Lemma brel_conjunction_irreflexive : 
        ((brel_irreflexive S r1) + (brel_irreflexive S r2)) -> 
           brel_irreflexive S (r1 <&> r2). 
Proof. intros [L | R]. 
       apply brel_conjunction_irreflexive_left; auto. 
       apply brel_conjunction_irreflexive_right; auto. 
Defined. 



(*


Lemma brel_conjunction_not_reflexive_right : 
              (brel_not_reflexive S r2) 
               → brel_not_reflexive S (r1 <&> r2). 
Proof. unfold brel_not_reflexive, brel_conjunction. 
       intros [s P]. exists s. rewrite P. apply andb_comm. 
Defined. 

Definition brel_conjunction_reflexive_decide: 
   ∀ (S : Type) 
     (r1 : brel S) 
     (r2 : brel S),   
     brel_reflexive_decidable S r1 → 
     brel_reflexive_decidable S r2 → 
        brel_reflexive_decidable S (r1 <&> r2)
:= λ S r1 r2 d1 d2,  
       match d1 with 
       | inl ref1 => 
         match d2 with 
         | inl ref2     => inl _ (brel_conjunction_reflexive S r1 r2 ref1 ref2)
         | inr not_ref2 => inr _ (brel_conjunction_not_reflexive_right S r1 r2 not_ref2)
         end 
       | inr not_ref1   => inr _ (brel_conjunction_not_reflexive_left S r1 r2 not_ref1)
       end. 


Lemma brel_conjunction_asymmetric_left : ∀ (S : Type) (r1 : brel S) (r2 : brel S),  
              (brel_asymmetric S r1) → 
                  brel_asymmetric S (r1 <&> r2). 
Proof. unfold brel_asymmetric, brel_conjunction.  
     intros S r1 r2 asy s t H. apply andb_is_true_left in H. destruct H as [L _]. 
     rewrite (asy _ _ L). compute. reflexivity. 
Defined. 

Lemma brel_conjunction_asymmetric_right : ∀ (S : Type) (r1 : brel S) (r2 : brel S),  
              (brel_asymmetric S r2) → 
                  brel_asymmetric S (r1 <&> r2). 
Proof. unfold brel_asymmetric, brel_conjunction.  
     intros S r1 r2 asy s t H. apply andb_is_true_left in H. destruct H as [_ R]. 
     rewrite (asy _ _ R). apply andb_comm.  
Defined. 


Lemma brel_conjunction_antisymmetric : 
         ∀ (S : Type) (eq : brel S) (r1 : brel S) (r2 : brel S),  
              (brel_antisymmetric S eq r1) + (brel_antisymmetric S eq r2) → 
              
              brel_antisymmetric S eq (r1 <&> r2). 
Proof. unfold brel_antisymmetric, brel_conjunction. 
     intros S eq r1 r2 [anti | anti] s t H1 H2. 
        destruct (andb_is_true_left _ _ H1) as [L1 _]; 
        destruct (andb_is_true_left _ _ H2) as [L2 _]. apply (anti _ _ L1 L2). 

        destruct (andb_is_true_left _ _ H1) as [_ R1]; 
        destruct (andb_is_true_left _ _ H2) as [_ R2]. apply (anti _ _ R1 R2). 
Defined. 
*) 

End Conjunction.




Section Theory.

Variable S        : Type.
Variable eq       : brel S.
Variable lte     : brel S. 
Variable lteCong  : brel_congruence S eq lte.
Variable lteRefl  : brel_reflexive S lte.
Variable lteTrans : brel_transitive S lte. 

Notation "a <<= b"  := (lte a b = true)        (at level 15).
Notation "a !<<= b" := (lte a b = false)       (at level 15).
Notation "a << b"   := (below lte b a = true) (at level 15).
Notation "a !<< b"  := (below lte b a = false) (at level 15).
Notation "a [~] b"   := (equiv lte b a = true) (at level 15).
Notation "a [!~] b"   := (equiv lte b a = false) (at level 15).
Notation "a [#] b"   := (incomp lte b a = true) (at level 15).
Notation "a [!#] b"   := (incomp lte b a = false) (at level 15).
Notation "a [~|#] b"   := (equiv_or_incomp lte b a = true) (at level 15).
Notation "a [!~|#] b"   := (equiv_or_incomp lte b a = false) (at level 15).


(************** intro and elim ******************)
(**************** below *************************) 

Lemma below_intro (a b : S) : b <<= a  -> a !<<= b -> b << a. 
Proof. intros A B. unfold below. rewrite A, B. compute. auto. Qed. 

Lemma below_elim (a b : S) : b << a -> (b <<= a) * (a !<<= b). 
Proof. intros A. unfold below in A. 
       case_eq(lte b a); intro B; case_eq(lte a b); intro C; auto.  
       rewrite B, C in A. compute in A. discriminate A.
       rewrite B, C in A. compute in A. discriminate A.
       rewrite B, C in A. compute in A. discriminate A.        
Qed.

Lemma below_false_intro (a b : S) : (b !<<= a  + a <<= b) -> b !<< a. 
Proof. unfold below. intros [A | A]; rewrite A; compute; auto. 
       case_eq(lte b a); intro B; auto. 
Qed. 

Lemma below_false_elim (a b : S) : b !<< a -> (b !<<= a  + a <<= b). 
Proof. intros A. unfold below in A. 
       case_eq(lte b a); intro B; case_eq(lte a b); intro C; auto.  
       rewrite B, C in A. compute in A. discriminate A.
Qed.

(**************** equiv *************************) 

Lemma equiv_intro (a b : S) : b <<= a  -> a <<= b -> b [~] a. 
Proof. intros A B. unfold equiv. rewrite A, B. compute. auto. Qed. 

Lemma equiv_elim (a b : S) : b [~] a -> (b <<= a) * (a <<= b). 
Proof. intros A. unfold equiv in A. 
       case_eq(lte b a); intro B; case_eq(lte a b); intro C; auto.  
       rewrite B, C in A. compute in A. discriminate A.
       rewrite B, C in A. compute in A. discriminate A.
       rewrite B, C in A. compute in A. discriminate A.        
Qed.

Lemma equiv_false_intro (a b : S) : (b !<<= a  + a !<<= b) -> b [!~] a. 
Proof. unfold equiv. intros [A | A]; rewrite A; compute; auto. 
       case_eq(lte a b); intro B; auto. 
Qed. 

Lemma equiv_false_elim (a b : S) : b [!~] a -> (b !<<= a  + a !<<= b). 
Proof. intros A. unfold equiv in A. 
       case_eq(lte b a); intro B; case_eq(lte a b); intro C; auto.  
       rewrite B, C in A. compute in A. discriminate A.
Qed.

(**************** incomp *************************) 

Lemma incomp_intro (a b : S) : b !<<= a  -> a !<<= b -> b [#] a. 
Proof. intros A B. unfold incomp. rewrite A, B. compute. auto. Qed. 

Lemma incomp_elim (a b : S) : b [#] a -> (b !<<= a) * (a !<<= b). 
Proof. intros A. unfold incomp in A. 
       case_eq(lte b a); intro B; case_eq(lte a b); intro C; auto.  
       rewrite B, C in A. compute in A. discriminate A.
       rewrite B, C in A. compute in A. discriminate A.
       rewrite B, C in A. compute in A. discriminate A.        
Qed.

Lemma incomp_false_intro (a b : S) : (b <<= a  + a <<= b) -> b [!#] a. 
Proof. unfold incomp. intros [A | A]; rewrite A; compute; auto. 
       case_eq(lte a b); intro B; auto. 
Qed. 

Lemma incomp_false_elim (a b : S) : b [!#] a -> (b <<= a  + a <<= b). 
Proof. intros A. unfold incomp in A. 
       case_eq(lte b a); intro B; case_eq(lte a b); intro C; auto.  
       rewrite B, C in A. compute in A. discriminate A.
Qed.



(**************** equiv_or_incomp *************************) 
Lemma equiv_or_incomp_intro (a b : S) : (a [~] b) + (a [#] b) -> a [~|#] b.
Proof. unfold equiv_or_incomp. intros [A | A].
       rewrite A ; compute; auto.
       compute in A.  compute. 
       case_eq(lte b a); intro B; case_eq(lte a b); intro C; auto.
          rewrite B in A. discriminate A.
          rewrite B in A. rewrite C in A. discriminate A.        
Qed. 

Lemma equiv_or_incomp_elim (a b : S) : a [~|#] b -> (a [~] b) + (a [#] b).
Proof. intros A. compute in A. compute. 
       case_eq(lte b a); intro B; case_eq(lte a b); intro C; auto.  
       rewrite B, C in A. discriminate A.
       rewrite B, C in A. discriminate A.
Qed.

Lemma equiv_or_incomp_false_intro (a b : S) :  (a [!~] b) * (a [!#] b) -> a [!~|#] b. 
Proof. unfold equiv_or_incomp. intros [A  B]. rewrite A, B. compute; auto. Qed. 

Lemma equiv_or_incomp_false_elim (a b : S) : a [!~|#] b -> (a [!~] b) * (a [!#] b).
Proof. intros A. compute in A. compute. 
       case_eq(lte b a); intro B; case_eq(lte a b); intro C; auto.  
          rewrite B, C in A. discriminate A.
          rewrite B, C in A. discriminate A.       
Qed.

(************** brel properties *****************)
(**************** below *************************) 

Lemma below_congruence : brel_congruence S eq (below lte). 
Proof. intros a b c d A B.
       unfold below. 
       rewrite (lteCong _ _ _ _ B A). 
       rewrite (lteCong _ _ _ _ A B). 
       compute. 
       case_eq(lte d c); intro C; case_eq(lte c d); intro D; auto.
Qed. 

Lemma below_not_reflexive (a : S ) : a !<< a.
Proof. compute.
       (* note: could use lteRefl here, but no need to add this dependency.... *) 
       case_eq(lte a a); intro K; reflexivity. 
Qed.

Lemma below_anti_symmetric (a b : S ) : a << b -> b !<< a.
Proof. compute. case_eq(lte a b); intro A; case_eq(lte b a); intro B; auto. Qed. 

Lemma below_transitive (a s t : S ) : t << a -> a << s -> t << s. 
Proof. intros A B. apply below_elim in A. apply below_elim in B.
       destruct A as [A C]. destruct B as [B D]. 
       apply below_intro.
          exact (lteTrans _ _ _ A B). 
          case_eq(lte s t); intro E; auto. 
             assert (F := lteTrans _ _ _ B E). 
             rewrite F in C. discriminate C.
Qed.

Lemma below_pseudo_transitive_left (s t u : S) : s <<= t -> t << u -> s << u.
Proof. intros A B. apply below_elim in B. destruct B as [B C]. 
       apply below_intro. 
         exact (lteTrans _ _ _ A B). 
         case_eq(lte u s); intro D; auto. 
         rewrite (lteTrans _ _ _ D A) in C. discriminate C. 
Qed. 


Lemma below_pseudo_transitive_right (s t u : S) : s << t -> t <<= u -> s << u.
Proof. intros A B. apply below_elim in A. destruct A as [A C]. 
       apply below_intro. 
         exact (lteTrans _ _ _ A B). 
         case_eq(lte u s); intro D; auto. 
         rewrite (lteTrans _ _ _ B D) in C. discriminate C. 
Qed. 


(**************** equiv *************************) 

Lemma equiv_congruence : brel_congruence S eq (equiv lte). 
Proof. intros a b c d A B.
       unfold equiv. 
       rewrite (lteCong _ _ _ _ B A). 
       rewrite (lteCong _ _ _ _ A B). 
       compute. 
       case_eq(lte d c); intro C; case_eq(lte c d); intro D; auto.
Qed. 

Lemma equiv_reflexive : brel_reflexive S (equiv lte).
Proof. compute. intro s. rewrite lteRefl. exact (lteRefl s).  Qed.

Lemma equiv_symmetric (a t : S ) : t [~] a -> a [~] t. 
Proof. intros A. apply equiv_elim in A. 
       destruct A as [A B]. 
       apply equiv_intro; auto. 
Qed. 

Lemma equiv_transitive (a s t : S ) : t [~] a -> a [~] s -> t [~] s. 
Proof. intros A B. apply equiv_elim in A. apply equiv_elim in B.
       destruct A as [A C]. destruct B as [B D]. 
       apply equiv_intro.
          exact (lteTrans _ _ _ A B).
          exact (lteTrans _ _ _ D C).        
Qed. 


(**************** incomp *************************) 
Lemma incomp_congruence : brel_congruence S eq (incomp lte). 
Proof. intros a b c d A B.
       unfold incomp. 
       rewrite (lteCong _ _ _ _ B A). 
       rewrite (lteCong _ _ _ _ A B). 
       compute. 
       case_eq(lte d c); intro C; case_eq(lte c d); intro D; auto.
Qed. 

Lemma incomp_not_reflexive (a : S ) : a [!#] a.
Proof. compute. rewrite lteRefl. reflexivity. Qed. 

Lemma incomp_symmetric (a t : S ) : t [#] a -> a [#] t. 
Proof. intros A. apply incomp_elim in A. 
       destruct A as [A B]. 
       apply incomp_intro; auto. 
Qed. 

Lemma incomp_pseudo_transitive (a s t : S ) : t [#] a -> a [#] s -> (t [#] s) + (t [~] s) + (s << t ) + (t << s). 
Proof. intros A B. apply incomp_elim in A. apply incomp_elim in B.
       destruct A as [A C]. destruct B as [B D]. 
       compute.
       case_eq(lte s t); intro E; case_eq(lte t s); intro F; auto.
Qed. 


(**************** equiv_or_incomp *************************) 
Lemma equiv_or_incomp_congruence : brel_congruence S eq (equiv_or_incomp lte). 
Proof. intros a b c d A B.
       unfold equiv_or_incomp. 
       rewrite (equiv_congruence _ _ _ _ A B). 
       rewrite (incomp_congruence _ _ _ _ A B). 
       compute. 
       case_eq(lte d c); intro C; case_eq(lte c d); intro D; auto.
Qed. 

Lemma equiv_or_incomp_reflexive : brel_reflexive S (equiv_or_incomp lte).
Proof. compute. intro s. rewrite lteRefl. rewrite lteRefl; auto. Qed.

Lemma equiv_or_incomp_symmetric (a t : S ) : t [~|#] a -> a [~|#] t. 
Proof. intros A. apply equiv_or_incomp_elim in A.
       apply equiv_or_incomp_intro. 
       destruct A as [A | A]. 
          left. apply equiv_symmetric; auto.
          right. apply incomp_symmetric; auto.        
Qed. 

Lemma equiv_or_incomp_pseudo_transitive (a s t : S ) : t [~|#] a -> a [~|#] s -> (t [~|#] s) + (s << t) + (t << s).  
Proof. intros A B. apply equiv_or_incomp_elim in A. apply equiv_or_incomp_elim in B.
       destruct A as [A | A]; destruct B as [B | B].
          left. left. apply equiv_or_incomp_intro.
          left. exact (equiv_transitive _ _ _ A B).

          (* t [~] a -> a [#] s -> t [#] s     extract as lemma *)
          left. left. apply equiv_or_incomp_intro.          
          right. 
          apply incomp_elim in B. apply equiv_elim in A.
          case_eq(lte t s); intro C; auto.
             destruct A as [_ A]. 
             rewrite (lteTrans _ _ _  A C) in B. destruct B as [B _].
             discriminate B.
             apply incomp_intro; auto. 
                (* s !<<= a -> a <<=t -> s !<<= t       extract *) 
                case_eq(lte s t); intro D; auto. 
                   destruct A as [A _]. destruct B as [_ B].                               
                   rewrite (lteTrans _ _ _ D A) in B.
                   discriminate B.

          (* t [#] a -> a [~] s -> t [#] s     extract as lemma *)
          left. left. apply equiv_or_incomp_intro.                             
          right. 
          apply incomp_elim in A. apply equiv_elim in B.
          case_eq(lte t s); intro C; auto.
             destruct B as [_ B]. 
             rewrite (lteTrans _ _ _  C B) in A. destruct A as [A _].
             discriminate A.
             apply incomp_intro; auto.
             destruct A as [_ A]. destruct B as [B _].                               
                (* t !<<= s -> a <<= s -> s !<<= t       extract *) 
                case_eq(lte s t); intro D; auto. 
                   rewrite (lteTrans _ _ _ B D) in A.
                   discriminate A.

          assert (C := incomp_pseudo_transitive _ _ _ A B).
          destruct C as [[[C | C] | C] | C]; auto.
          left. left. apply equiv_or_incomp_intro. right; auto.
          left. left. apply equiv_or_incomp_intro. left; auto.          
Qed. 


Lemma equiv_implies_not_below (a s : S) : (a [~] s) -> a !<< s * s !<< a.
Proof. compute. case_eq(lte a s); intro A; case_eq(lte s a); intro B; auto. Qed. 

Lemma incomp_implies_not_below (a s : S) : (a [#] s) -> a !<< s * s !<< a.   
Proof. compute. case_eq(lte a s); intro A; case_eq(lte s a); intro B; auto. Qed.

Lemma equiv_or_incomp_implies_not_below (a s : S) : (a [~|#] s) -> a !<< s * s !<< a. 
Proof. compute. case_eq(lte a s); intro A; case_eq(lte s a); intro B; auto. Qed.

Lemma not_below_implies_equiv_or_incomp (a s : S) : a !<< s -> (s !<< a) -> (a [~|#] s). 
Proof. compute. case_eq(lte a s); intro A; case_eq(lte s a); intro B; auto. Qed.


Lemma below_equiv_pseudo_congruence :
  ∀ a b c d : S, a [~] c → b [~] d → (below lte a b = below lte c d) + ((a << b) *  (d << c)) + ((b << a) * (c << d)). 
Proof. intros a b c d A B.
       apply equiv_elim in A. apply equiv_elim in B.
       destruct A as [A1 A2]. destruct B as [B1 B2].
       compute. 
       case_eq(lte d c); intro C; case_eq(lte c d); intro D;
       case_eq(lte b a); intro E; case_eq(lte a b); intro F; auto.
          (* a~c, b~d, d~c, but b!~a  *** *)      
          assert (G := lteTrans _ _ _ A1 D). 
          assert (H := lteTrans _ _ _ G B2). 
          rewrite H in F. discriminate F. 
          (* a~c, b~d, a~b, but c!~d  *** *)        
          assert (G := lteTrans _ _ _ A2 F). 
          assert (H := lteTrans _ _ _ G B1). 
          rewrite H in D. discriminate D. 
          (* a~c, b~d, but d <<c   a#b  ***  *) 
          assert (G := lteTrans _ _ _ B1 C). 
          assert (H := lteTrans _ _ _ G A2). 
          rewrite H in E. discriminate E. 
          (* a~c, b~d, but c#d     b << a ***  *)
          assert (G := lteTrans _ _ _ B2 E). 
          assert (H := lteTrans _ _ _ G A1). 
          rewrite H in C. discriminate C. 
Qed. 


Lemma below_equiv_pseudo_congruence_v2 :
  ∀ a b c  : S, a [~] c → below lte a b = below lte c b. 
Proof. intros a b c A.       
       destruct (below_equiv_pseudo_congruence _ _ _ _ A (equiv_reflexive b)) as [[C | [C D]] | [C D]]; auto.
          apply equiv_elim in A. destruct A as [A B].
          assert (E := below_transitive _ _ _ C D).
          apply below_elim in E. destruct E as [E F].       
          rewrite F in B. discriminate B.
          apply equiv_elim in A. destruct A as [A B].
          assert (E := below_transitive _ _ _ D C).
          apply below_elim in E. destruct E as [E F].       
          rewrite F in A. discriminate A.
Qed.


Close Scope nat. 

(*******************BOTTOMS********************************)


(*
{B : finite_set T & (is_antichain T eq lte B) * 
                    (∀(t : T), (in_set eq B t = true) + {s : S & (in_set eq B s = true) * (below lte t s = true)})}
*) 



Definition bottoms_set_is_finite (T : Type) (eq lte : brel T) 
  := {p : (list T) * (T -> T) &
          match p with (B, w) =>
                       (is_antichain T eq lte B) * 
                       (∀(s : T), (in_set eq B s = true) + ((in_set eq B (w s) = true) * (below lte s (w s) = true)))
          end}.


Definition bottoms_set_is_finite2 (T : Type) (eq lte : brel T) 
  := {p : (list T) * (T -> T) &
          match p with (B, w) =>
                       (is_antichain T eq lte B) * 
                       (∀(s : T), (in_set eq B (w s) = true) * (below lte s (w s) = true))
          end}.
(*

negate 

{B : finite_set T & (is_antichain T eq lte B) * 
                    (∀(t : T), (in_set eq B t = true) + {s : S & (in_set eq B s = true) * (below lte t s = true)})}

to 
∀ B : finite_set T,  (is_antichain T eq lte B)  -> 
                     {t : T & (in_set eq B t = false) * (∀ s : S, (in_set eq B s = true) -> (below lte t s = false))}

now, functionalise this 


{F : (finite_set T) -> T & 
     ∀ B : finite_set T, (is_antichain T eq lte B) -> (in_set eq B (F B) = false) * 
                                                      (∀ s : S, (in_set eq B s = true) -> (below lte (F B) s = false))}
 *)

Definition bottoms_set_not_is_finite2 (T : Type) (eq lte : brel T) 
  := {F : (list T) -> T & 
                      ∀ B : finite_set T, (is_antichain T eq lte B) ->
                                          (∀ s : T, (in_set eq B s = true) -> (below lte (F B) s = false))}. 


Definition bottoms_set_not_is_finite (T : Type) (eq lte : brel T) 
  := {F : (list T) -> T &
                      ∀ B : finite_set T, (is_antichain T eq lte B) ->
                                          (in_set eq B (F B) = false) * 
                                          (∀ s : T, (in_set eq B s = true) -> (below lte (F B) s = false))}. 
     

(* because the definitions have changed too often .... *) 
Lemma another_bottoms_sanity_check (T : Type) (rT lteT : brel T)
      (bf : bottoms_set_is_finite T rT lteT) (bnf : bottoms_set_not_is_finite T rT lteT) : true = false.
Proof. destruct bf as [[BOTTOMS w] [A B]].
       destruct bnf as [F C].
       destruct (C BOTTOMS A) as [D E].
       destruct (B (F BOTTOMS)) as [G | G].
          rewrite G in D. discriminate D.
          destruct G as [G1 G2]. 
          assert (H := E _ G1).
          rewrite H in G2. discriminate G2. 
Qed.   


Lemma another_bottoms_sanity_check2 (T : Type) (rT lteT : brel T)
      (bf : bottoms_set_is_finite2 T rT lteT) (bnf : bottoms_set_not_is_finite2 T rT lteT) : true = false.
Proof. destruct bf as [[BOTTOMS w] [A B]].
       destruct bnf as [F C].
       assert (E := C BOTTOMS A).
       destruct (B (F BOTTOMS)) as [G1 G2].
          assert (H := E _ G1).
          rewrite H in G2. discriminate G2. 
Qed.   


(***************************************************)

(* a few trivial lemmas needed in classify in po/structures.v and po/cast_up.v 
*)

(* for classify : *)
Lemma brel_exists_bottom_from_brel_exists_qo_bottom
      (P : brel_exists_qo_bottom S eq lte) : brel_exists_bottom S lte.
Proof. destruct P as [bot [A B]]. exists bot; auto. Defined. 

Lemma brel_not_exists_bottom_from_brel_not_exists_qo_bottom
      (anti : brel_antisymmetric S eq lte) 
      (P : brel_not_exists_qo_bottom S eq lte) : brel_not_exists_bottom S lte.
Proof. intro b. 
       destruct (P b) as [Q | Q].
       + exact Q. 
       + destruct Q as [a [[A B] C]].
         rewrite (anti b a A B) in C.
         discriminate C. 
Defined.

Definition brel_exists_bottom_decidable_from_brel_exists_qo_bottom_decidable 
  (anti : brel_antisymmetric S eq lte) 
  (D : brel_exists_qo_bottom_decidable S eq lte) : brel_exists_bottom_decidable S lte := 
  match D with
  | inl bot => inl (brel_exists_bottom_from_brel_exists_qo_bottom bot)
  | inr nbot => inr (brel_not_exists_bottom_from_brel_not_exists_qo_bottom anti nbot)
  end.


Lemma brel_exists_top_from_brel_exists_qo_top
     (P : brel_exists_qo_top S eq lte) : brel_exists_top S lte.
Proof. destruct P as [top [A B]]. exists top; auto. Defined. 

Lemma brel_not_exists_top_from_brel_not_exists_qo_top
      (anti : brel_antisymmetric S eq lte) 
      (P : brel_not_exists_qo_top S eq lte) : brel_not_exists_top S lte.
Proof. intro b. 
       destruct (P b) as [Q | Q].
       + exact Q. 
       + destruct Q as [a [[A B] C]].
         rewrite (anti b a A B) in C.
         discriminate C. 
Defined.

Definition brel_exists_top_decidable_from_brel_exists_qo_top_decidable 
  (anti : brel_antisymmetric S eq lte) 
  (D : brel_exists_qo_top_decidable S eq lte) : brel_exists_top_decidable S lte := 
  match D with
  | inl top => inl (brel_exists_top_from_brel_exists_qo_top top)
  | inr ntop => inr (brel_not_exists_top_from_brel_not_exists_qo_top anti ntop)
  end.


(* other direction for cast_up : *) 
Lemma brel_exists_qo_bottom_from_brel_exists_bottom
      (anti : brel_antisymmetric S eq lte)       
      (P : brel_exists_bottom S lte) : brel_exists_qo_bottom S eq lte.
Proof. destruct P as [bot A]. exists bot. split; auto. 
       exact (anti bot). 
Defined. 

Lemma brel_not_exists_qo_bottom_from_brel_not_exists_bottom
      (P : brel_not_exists_bottom S lte) : brel_not_exists_qo_bottom S eq lte.
Proof. intro b. left. exact (P b).  Defined.

Definition brel_exists_qo_bottom_decidable_from_brel_exists_bottom_decidable 
  (anti : brel_antisymmetric S eq lte) 
  (D : brel_exists_bottom_decidable S lte) : brel_exists_qo_bottom_decidable S eq lte := 
  match D with
  | inl bot => inl (brel_exists_qo_bottom_from_brel_exists_bottom anti bot)
  | inr nbot => inr (brel_not_exists_qo_bottom_from_brel_not_exists_bottom nbot)
  end.


Lemma brel_exists_qo_top_from_brel_exists_top
      (anti : brel_antisymmetric S eq lte)       
      (P : brel_exists_top S lte) : brel_exists_qo_top S eq lte.
Proof. destruct P as [top A]. exists top. split; auto. 
       exact (anti top). 
Defined. 


Lemma brel_not_exists_qo_top_from_brel_not_exists_top
      (P : brel_not_exists_top S lte) : brel_not_exists_qo_top S eq lte.
Proof. intro b. left. exact (P b).  Defined.

Definition brel_exists_qo_top_decidable_from_brel_exists_top_decidable 
  (anti : brel_antisymmetric S eq lte) 
  (D : brel_exists_top_decidable S lte) : brel_exists_qo_top_decidable S eq lte := 
  match D with
  | inl top => inl (brel_exists_qo_top_from_brel_exists_top anti top)
  | inr ntop => inr (brel_not_exists_qo_top_from_brel_not_exists_top ntop)
  end.


(* triviality *)

Lemma order_trivial_implies_total (TS : order_trivial S lte) : brel_total S lte. 
Proof. intros s1 s2. rewrite (TS s1 s2). left. reflexivity. Qed.        

Lemma order_not_total_implies_not_trivial (TS : brel_not_total S lte) : order_not_trivial S lte. 
Proof. destruct TS as [[s1 s2] [A B]]. exists (s1, s2). exact A.  Defined.   

Definition witness_antisymmetric_implies_order_not_trivial (wS : S) (f : S -> S) :=
  if lte wS (f wS) then (f wS, wS) else (wS, f wS).

Lemma antisymmetric_implies_order_not_trivial (wS : S) (f : S -> S) (nt : brel_not_trivial S eq f) 
      (anti : brel_antisymmetric S eq lte) : order_not_trivial S lte.
Proof. exists (witness_antisymmetric_implies_order_not_trivial wS f). 
       destruct (nt wS) as [L R].
       unfold witness_antisymmetric_implies_order_not_trivial.               
       case_eq(lte wS (f wS)); intro A. 
       + case_eq(lte (f wS) wS); intro B. 
         ++ rewrite (anti wS (f wS) A B) in L. discriminate L. 
         ++ reflexivity. 
       + exact A.          
Defined.   
 
End Theory. 
