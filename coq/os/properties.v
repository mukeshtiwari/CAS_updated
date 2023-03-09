Require Import CAS.coq.common.compute.
Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.sg.properties.
Require Import CAS.coq.po.properties.

Close Scope nat. 

Section ACAS. 

(* t <= u -> (s x t) <= (s X u) *)   
Definition os_left_monotone {S : Type} (lte : brel S) (b : binary_op S)  
   := ∀ s t u : S, lte t u = true -> lte (b s t) (b s u) = true. 

Definition os_not_left_monotone {S : Type} (lte : brel S) (b : binary_op S)  
   := { z : S * (S * S) & match z with (s, (t, u)) => (lte t u = true) * (lte (b s t) (b s u) = false) end }. 

Definition os_left_monotone_decidable {S : Type} (lte : brel S) (b : binary_op S)  
   := (os_left_monotone lte b) + (os_not_left_monotone lte b). 

(* t <= u -> (t x s) <= (u X s) *)   
Definition os_right_monotone {S : Type} (lte : brel S) (b : binary_op S)  
   := ∀ s t u : S, lte t u = true -> lte (b t s) (b u s) = true. 

Definition os_not_right_monotone {S : Type} (lte : brel S) (b : binary_op S)  
   := { z : S * (S * S) & match z with (s, (t, u)) => (lte t u = true) * (lte (b t s) (b u s) = false) end }. 

Definition os_right_monotone_decidable {S : Type} (lte : brel S) (b : binary_op S)  
   := (os_right_monotone lte b) + (os_not_right_monotone lte b). 


(* s <= (s x t) *)   
Definition os_left_increasing {S : Type} (lte : brel S) (b : binary_op S)  
   := ∀ s t : S, lte s (b s t) = true. 

Definition os_not_left_increasing {S : Type} (lte : brel S) (b : binary_op S)  
   := { z : S * S & match z with (s, t) => lte s (b s t) = false end }. 

Definition os_left_increasing_decidable {S : Type} (lte : brel S) (b : binary_op S)  
   := (os_left_increasing lte b) + (os_not_left_increasing lte b). 

(* s <= (t x s) *)   
Definition os_right_increasing {S : Type} (lte : brel S) (b : binary_op S)  
   := ∀ s t : S, lte s (b t s) = true. 

Definition os_not_right_increasing {S : Type} (lte : brel S) (b : binary_op S)  
   := { z : S * S & match z with (s, t) => lte s (b t s) = false end }. 

Definition os_right_increasing_decidable {S : Type} (lte : brel S) (b : binary_op S)  
   := (os_right_increasing lte b) + (os_not_right_increasing lte b). 


(* decreasing *)

(* (s x t) <= s *)   
Definition os_left_decreasing {S : Type} (lte : brel S) (b : binary_op S)  
   := ∀ s t : S, lte (b s t) s = true. 

Definition os_not_left_decreasing {S : Type} (lte : brel S) (b : binary_op S)  
   := { z : S * S & match z with (s, t) => lte (b s t) s = false end }. 

Definition os_left_decreasing_decidable {S : Type} (lte : brel S) (b : binary_op S)  
   := (os_left_decreasing lte b) + (os_not_left_decreasing lte b). 


(* (t x s) <= s *)   
Definition os_right_decreasing {S : Type} (lte : brel S) (b : binary_op S)  
   := ∀ s t : S, lte (b t s) s = true. 

Definition os_not_right_decreasing {S : Type} (lte : brel S) (b : binary_op S)  
   := { z : S * S & match z with (s, t) => lte (b t s) s = false end }. 

Definition os_right_decreasing_decidable {S : Type} (lte : brel S) (b : binary_op S)  
   := (os_right_decreasing lte b) + (os_not_right_decreasing lte b). 



(***** strict versions ******)

(* s < (s x t) *)   
Definition os_left_strictly_increasing {S : Type} (lte : brel S) (b : binary_op S)  
   := ∀ s t : S, (lte s (b s t) = true) * (lte (b s t) s = false). 

Definition os_not_left_strictly_increasing {S : Type} (lte : brel S) (b : binary_op S)  
   := { z : S * S & match z with (s, t) => (lte s (b s t) = false) + (lte (b s t) s = true)  end }. 

Definition os_left_strictly_increasing_decidable {S : Type} (lte : brel S) (b : binary_op S)  
   := (os_left_strictly_increasing lte b) + (os_not_left_strictly_increasing lte b). 

(* s < (t x s) *)   
Definition os_right_strictly_increasing {S : Type} (lte : brel S) (b : binary_op S)  
   := ∀ s t : S, (lte s (b t s) = true) * (lte (b t s) s = false). 

Definition os_not_right_strictly_increasing {S : Type} (lte : brel S) (b : binary_op S)  
   := { z : S * S & match z with (s, t) => (lte s (b t s) = false) + (lte (b t s) s = true)  end }. 

Definition os_right_strictly_increasing_decidable {S : Type} (lte : brel S) (b : binary_op S)  
  := (os_right_strictly_increasing lte b) + (os_not_right_strictly_increasing lte b).

(* t < u -> (s x t) < (s x u)  *)
Definition os_left_strictly_monotone {S : Type} (lte : brel S) (b : binary_op S)  
  := ∀ s t u : S, lte t u = true -> lte u t = false ->
                  (lte (b s t) (b s u) = true) * (lte (b s u) (b s t) = false). 

Definition os_not_left_strictly_monotone {S : Type} (lte : brel S) (b : binary_op S)  
  := { z : S * (S * S) & match z with (s, (t, u)) =>
            (lte t u = true) * (lte u t = false) * ((lte (b s t) (b s u) = false) + (lte (b s u) (b s t) = true))end }. 

Definition os_left_strictly_monotone_decidable {S : Type} (lte : brel S) (b : binary_op S)  
   := (os_left_strictly_monotone lte b) + (os_not_left_strictly_monotone lte b). 

(* t < u -> (t x s) < (u x s)  *)
Definition os_right_strictly_monotone {S : Type} (lte : brel S) (b : binary_op S)  
   := ∀ s t u : S, lte t u = true -> lte u t = false -> (lte (b t s) (b u s) = true) * (lte (b u s) (b t s) = false). 

Definition os_not_right_strictly_monotone {S : Type} (lte : brel S) (b : binary_op S)  
  := { z : S * (S * S) & match z with (s, (t, u)) =>
            (lte t u = true) * (lte u t = false) * ((lte (b t s) (b u s) = false) + (lte (b u s) (b t s) = true)) end }. 

Definition os_right_strictly_monotone_decidable {S : Type} (lte : brel S) (b : binary_op S)  
   := (os_right_strictly_monotone lte b) + (os_not_right_strictly_monotone lte b). 


(* do the following belong in po/properties.v ? *) 
Definition is_lower_bound {S : Type} (lte : brel S) (a b c : S) :=  
     (lte c a = true) *  (lte c b = true). 

Definition is_upper_bound {S : Type} (lte : brel S) (a b c : S) :=  
     (lte a c = true) *  (lte b c = true). 

Definition is_glb {S : Type} (lte : brel S) (a b c : S) :=  
      (is_lower_bound lte a b c) *
          (∀ u : S, (is_lower_bound lte a b u) -> lte u c = true). 

Definition is_lub {S : Type} (lte : brel S) (a b c : S) :=  
      (is_upper_bound lte a b c) *
      (∀ u : S, (is_upper_bound lte a b u) -> lte c u = true).

Definition bop_is_glb {S : Type} (lte : brel S) (b : binary_op S) :=  ∀ s t : S,  is_glb lte s t (b s t).

Definition bop_is_lub {S : Type} (lte : brel S) (b : binary_op S) :=  ∀ s t : S,  is_lub lte s t (b s t).

Definition exists_glb {S : Type} (lte : brel S) := {b : binary_op S &  bop_is_glb lte b}.

Definition exists_lub {S : Type} (lte : brel S) := {b : binary_op S &  bop_is_lub lte b}.  


(********************** Top, bottom vs id ann *****************************************)

(* quasi ordered *) 

Definition A_os_exists_qo_bottom_id_equal {S : Type} (r lte : brel S) (b : binary_op S)
  := { i : S & (brel_is_qo_bottom S r lte i) * (bop_is_id S r b i)}.


Definition A_os_exists_qo_bottom_id_not_equal {S : Type} (r lte : brel S) (mul : binary_op S)
  := { z : S * S & let (b, i) := z in (brel_is_qo_bottom S r lte b) * (bop_is_id S r mul i) * (r i b = false)}.


Inductive os_exists_qo_bottom_id_decidable (S : Type) (eq lte : brel S) (b : binary_op S)  : Type :=
| Qo_Bottom_Id_Proof_None        : (brel_not_exists_qo_bottom S eq lte) * (bop_not_exists_id S eq b) -> os_exists_qo_bottom_id_decidable S eq lte b
| Qo_Bottom_Id_Proof_Bottom_None : (brel_exists_qo_bottom S eq lte) * (bop_not_exists_id S eq b)     -> os_exists_qo_bottom_id_decidable S eq lte b
| Qo_Bottom_Id_Proof_None_Id     : (brel_not_exists_qo_bottom S eq lte) * (bop_exists_id S eq b)     -> os_exists_qo_bottom_id_decidable S eq lte b
| Qo_Bottom_Id_Proof_Equal       : A_os_exists_qo_bottom_id_equal eq lte b                           -> os_exists_qo_bottom_id_decidable S eq lte b
| Qo_Bottom_Id_Proof_Not_Equal   : A_os_exists_qo_bottom_id_not_equal eq lte b                       -> os_exists_qo_bottom_id_decidable S eq lte b.

(********************** quasi-ordered Top vs ann *****************************************)

Definition A_os_exists_qo_top_ann_equal {S : Type} (r lte : brel S) (b : binary_op S)
  := { t : S & (brel_is_qo_top S r lte t) * (bop_is_ann S r b t)}.

Definition A_os_exists_qo_top_ann_not_equal {S : Type} (r lte : brel S) (mul : binary_op S)
  := { z : S * S & let (t, a) := z in (brel_is_qo_top S r lte t) * (bop_is_ann S r mul a) * (r t a = false)}.

Inductive os_exists_qo_top_ann_decidable (S : Type) (eq lte : brel S) (b : binary_op S)  : Type :=
| Qo_Top_Ann_Proof_None      : (brel_not_exists_qo_top S eq lte) * (bop_not_exists_ann S eq b) -> os_exists_qo_top_ann_decidable S eq lte b
| Qo_Top_Ann_Proof_Top_None  : (brel_exists_qo_top S eq lte) * (bop_not_exists_ann S eq b)     -> os_exists_qo_top_ann_decidable S eq lte b
| Qo_Top_Ann_Proof_None_Ann  : (brel_not_exists_qo_top S eq lte) * (bop_exists_ann S eq b)     -> os_exists_qo_top_ann_decidable S eq lte b
| Qo_Top_Ann_Proof_Equal     : A_os_exists_qo_top_ann_equal eq lte b                           -> os_exists_qo_top_ann_decidable S eq lte b
| Qo_Top_Ann_Proof_Not_Equal : A_os_exists_qo_top_ann_not_equal eq lte b                       -> os_exists_qo_top_ann_decidable S eq lte b.

(* partially ordered *)

(********************** bottom vs id *****************************************)

Definition A_os_exists_bottom_id_equal {S : Type} (r lte : brel S) (b : binary_op S)
  := { bot : S & (brel_is_bottom S lte bot) * (bop_is_id S r b bot)}.

Definition A_os_exists_bottom_id_not_equal {S : Type} (r lte : brel S) (b : binary_op S)
  := { z : S * S & match z with (bot, id) => (brel_is_bottom S lte bot) * (bop_is_id S r b id) * (r bot id = false) end}.

Definition A_extract_exist_bottom_from_exists_bottom_id_equal (S : Type) (r lte : brel S) (b : binary_op S)
           (P : A_os_exists_bottom_id_equal r lte b) : brel_exists_bottom S lte := 
  existT (λ x : S, brel_is_bottom S lte x) (projT1 P) (fst (projT2 P)).

Definition A_extract_exist_id_from_exists_bottom_id_equal (S : Type) (r lte : brel S) (b : binary_op S)
           (P : A_os_exists_bottom_id_equal r lte b) : bop_exists_id S r b := 
  existT (λ x : S, bop_is_id S r b x) (projT1 P) (snd (projT2 P)).

Definition A_extract_exist_bottom_from_exists_bottom_id_not_equal (S : Type) (r lte : brel S) (b : binary_op S)
           (P :  A_os_exists_bottom_id_not_equal r lte b) : brel_exists_bottom S lte :=
  match P with
  existT _ (i, a) p =>     
     existT (λ x : S, brel_is_bottom S lte x) i (fst (fst p))
  end. 

Definition A_extract_exist_id_from_exists_bottom_id_not_equal (S : Type) (r lte : brel S) (b : binary_op S)
           (P :  A_os_exists_bottom_id_not_equal r lte b) : bop_exists_id S r b :=
  match P with
  existT _ (bot, id) ((_, p), _) =>     
     existT (λ x : S, bop_is_id S r b x) id p
  end. 


Inductive os_exists_bottom_id_decidable (S : Type) (eq lte : brel S) (b : binary_op S)  : Type :=
| Bottom_Id_Proof_None        : (brel_not_exists_bottom S lte) * (bop_not_exists_id S eq b) -> os_exists_bottom_id_decidable S eq lte b
| Bottom_Id_Proof_Bottom_None : (brel_exists_bottom S lte) * (bop_not_exists_id S eq b)     -> os_exists_bottom_id_decidable S eq lte b
| Bottom_Id_Proof_None_Id     : (brel_not_exists_bottom S lte) * (bop_exists_id S eq b)     -> os_exists_bottom_id_decidable S eq lte b
| Bottom_Id_Proof_Equal       : A_os_exists_bottom_id_equal eq lte b                          -> os_exists_bottom_id_decidable S eq lte b
| Bottom_Id_Proof_Not_Equal   : A_os_exists_bottom_id_not_equal eq lte b                      -> os_exists_bottom_id_decidable S eq lte b.

Definition extract_exists_bottom_decidable_from_exists_bottom_id_decidable
           (S : Type) (r lte : brel S) (b : binary_op S)
           (P : os_exists_bottom_id_decidable S r lte b) : brel_exists_bottom_decidable S lte :=
match P with
| Bottom_Id_Proof_None _ _ _ _ (no_bot, _)             => inr no_bot 
| Bottom_Id_Proof_Bottom_None  _ _ _ _ (exists_bot, _) => inl exists_bot 
| Bottom_Id_Proof_None_Id _ _ _ _ (no_bot, _)          => inr no_bot
| Bottom_Id_Proof_Equal _ _ _ _ bot_id_eq              => inl (A_extract_exist_bottom_from_exists_bottom_id_equal S r lte b bot_id_eq) 
| Bottom_Id_Proof_Not_Equal _ _ _ _ bot_id_not_eq      => inl (A_extract_exist_bottom_from_exists_bottom_id_not_equal S r lte b bot_id_not_eq) 
end.

Definition extract_exists_id_decidable_from_exists_bottom_id_decidable
           (S : Type) (r lte : brel S) (b : binary_op S)
           (P : os_exists_bottom_id_decidable S r lte b) : bop_exists_id_decidable S r b :=
match P with
| Bottom_Id_Proof_None _ _ _ _ (_, no_id)          => inr no_id
| Bottom_Id_Proof_Bottom_None  _ _ _ _ (_, no_id)  => inr no_id
| Bottom_Id_Proof_None_Id _ _ _ _ (_, exists_id)   => inl exists_id
| Bottom_Id_Proof_Equal _ _ _ _ bot_id_eq          => inl (A_extract_exist_id_from_exists_bottom_id_equal S r lte b bot_id_eq) 
| Bottom_Id_Proof_Not_Equal _ _ _ _ bot_id_not_eq  => inl (A_extract_exist_id_from_exists_bottom_id_not_equal S r lte b bot_id_not_eq) 
end.


(********************** Top vs ann *****************************************)

Definition A_os_exists_top_ann_equal {S : Type} (r lte : brel S) (b : binary_op S)
  := { top : S & (brel_is_top S lte top) * (bop_is_ann S r b top)}.

Definition A_os_exists_top_ann_not_equal {S : Type} (r lte : brel S) (b : binary_op S)
  := { z : S * S & match z with (top, ann) => (brel_is_top S lte top) * (bop_is_ann S r b ann) * (r top ann = false) end}.

Definition A_extract_exist_top_from_exists_top_ann_equal (S : Type) (r lte : brel S) (b : binary_op S)
           (P : A_os_exists_top_ann_equal r lte b) : brel_exists_top S lte := 
  existT (λ x : S, brel_is_top S lte x) (projT1 P) (fst (projT2 P)).

Definition A_extract_exist_ann_from_exists_top_ann_equal (S : Type) (r lte : brel S) (b : binary_op S)
           (P : A_os_exists_top_ann_equal r lte b) : bop_exists_ann S r b := 
  existT (λ x : S, bop_is_ann S r b x) (projT1 P) (snd (projT2 P)).

Definition A_extract_exist_top_from_exists_top_ann_not_equal (S : Type) (r lte : brel S) (b : binary_op S)
           (P :  A_os_exists_top_ann_not_equal r lte b) : brel_exists_top S lte :=
  match P with
  existT _ (top, _) p =>     
     existT (λ x : S, brel_is_top S lte x) top (fst (fst p))
  end. 

Definition A_extract_exist_ann_from_exists_top_ann_not_equal (S : Type) (r lte : brel S) (b : binary_op S)
           (P :  A_os_exists_top_ann_not_equal r lte b) : bop_exists_ann S r b :=
  match P with
  existT _ (_, ann) ((_, p), _) =>     
     existT (λ x : S, bop_is_ann S r b x) ann p
  end. 


Inductive os_exists_top_ann_decidable (S : Type) (eq lte : brel S) (b : binary_op S)  : Type :=
| Top_Ann_Proof_None      : (brel_not_exists_top S lte) * (bop_not_exists_ann S eq b) -> os_exists_top_ann_decidable S eq lte b
| Top_Ann_Proof_Top_None  : (brel_exists_top S lte) * (bop_not_exists_ann S eq b)     -> os_exists_top_ann_decidable S eq lte b
| Top_Ann_Proof_None_Ann  : (brel_not_exists_top S lte) * (bop_exists_ann S eq b)     -> os_exists_top_ann_decidable S eq lte b
| Top_Ann_Proof_Equal     : A_os_exists_top_ann_equal eq lte b                          -> os_exists_top_ann_decidable S eq lte b
| Top_Ann_Proof_Not_Equal : A_os_exists_top_ann_not_equal eq lte b                      -> os_exists_top_ann_decidable S eq lte b.

Definition A_extract_exists_top_decidable_from_exists_top_ann_decidable
           (S : Type) (r lte : brel S) (b : binary_op S)
           (P : os_exists_top_ann_decidable S r lte b) : brel_exists_top_decidable S lte :=
match P with
| Top_Ann_Proof_None _ _ _ _ (no_top, _)             => inr no_top 
| Top_Ann_Proof_Top_None  _ _ _ _ (exists_top, _) => inl exists_top 
| Top_Ann_Proof_None_Ann _ _ _ _ (no_top, _)          => inr no_top
| Top_Ann_Proof_Equal _ _ _ _ top_ann_eq              => inl (A_extract_exist_top_from_exists_top_ann_equal S r lte b top_ann_eq) 
| Top_Ann_Proof_Not_Equal _ _ _ _ top_ann_not_eq      => inl (A_extract_exist_top_from_exists_top_ann_not_equal S r lte b top_ann_not_eq) 
end.

Definition A_extract_exists_ann_decidable_from_exists_top_ann_decidable
           (S : Type) (r lte : brel S) (b : binary_op S)
           (P : os_exists_top_ann_decidable S r lte b) : bop_exists_ann_decidable S r b :=
match P with
| Top_Ann_Proof_None _ _ _ _ (_, no_ann)          => inr no_ann
| Top_Ann_Proof_Top_None  _ _ _ _ (_, no_ann)  => inr no_ann
| Top_Ann_Proof_None_Ann _ _ _ _ (_, exists_ann)   => inl exists_ann
| Top_Ann_Proof_Equal _ _ _ _ top_ann_eq          => inl (A_extract_exist_ann_from_exists_top_ann_equal S r lte b top_ann_eq) 
| Top_Ann_Proof_Not_Equal _ _ _ _ top_ann_not_eq  => inl (A_extract_exist_ann_from_exists_top_ann_not_equal S r lte b top_ann_not_eq) 
end.

Lemma os_exists_qo_bottom_implies_os_exists_bottom
      (S : Type) (eq lte : brel S)
      (d : brel_exists_qo_bottom S eq lte) : brel_exists_bottom S lte.
Proof. destruct d as [b [A B]]. 
       exists b; auto. 
Defined.        
       
Lemma os_not_exists_qo_bottom_implies_os_not_exists_bottom
      (S : Type) (eq lte : brel S)
      (anti : brel_antisymmetric S eq lte) 
      (d : brel_not_exists_qo_bottom S eq lte) : brel_not_exists_bottom S lte.
Proof. unfold brel_not_exists_qo_bottom in d.
       intro s. destruct (d s) as [A | [a [[A B] C]]]; auto.
       rewrite (anti _ _ A B) in C. discriminate C. 
Qed.

Lemma os_exists_qo_bottom_id_equal_implies_os_exists_bottom_id_equal
      (S : Type) (eq lte : brel S) (times : binary_op S) 
      (anti : brel_antisymmetric S eq lte) 
      (d : A_os_exists_qo_bottom_id_equal eq lte times) : A_os_exists_bottom_id_equal eq lte times.
Proof. destruct d as [b [[A B] C]].
       exists b; auto. 
Defined.        

Lemma os_exists_qo_bottom_id_not_equal_implies_os_exists_bottom_id_not_equal
      (S : Type) (eq lte : brel S) (times : binary_op S)
      (sym : brel_symmetric S eq) 
      (anti : brel_antisymmetric S eq lte) 
      (d : A_os_exists_qo_bottom_id_not_equal eq lte times) : A_os_exists_bottom_id_not_equal eq lte times.
Proof. destruct d as [[b i] [[[A B] C] D]].
       exists (b, i); split; auto.
       case_eq(eq b i); intro E; auto.
       rewrite (sym _ _ E) in D. discriminate D. 
Defined.        

Definition os_exists_bottom_id_decidable_from_os_exists_qo_bottom_id_decidable
           (S : Type) (eq lte : brel S) (b : binary_op S)
           (sym : brel_symmetric S eq)            
           (anti : brel_antisymmetric S eq lte) 
           (d : os_exists_qo_bottom_id_decidable S eq lte b) :
                  os_exists_bottom_id_decidable S eq lte b :=   
match d with
| Qo_Bottom_Id_Proof_None _ _ _ _ (nqob, nid)     =>
     Bottom_Id_Proof_None _ _ _ _ (os_not_exists_qo_bottom_implies_os_not_exists_bottom S eq lte anti nqob, nid) 
| Qo_Bottom_Id_Proof_Bottom_None _ _ _ _ (qob, nid) =>
     Bottom_Id_Proof_Bottom_None _ _ _ _ (os_exists_qo_bottom_implies_os_exists_bottom S eq lte qob, nid) 
| Qo_Bottom_Id_Proof_None_Id _ _ _ _ (nqob, idP)    =>
  Bottom_Id_Proof_None_Id _ _ _ _ (os_not_exists_qo_bottom_implies_os_not_exists_bottom S eq lte anti nqob, idP)    
| Qo_Bottom_Id_Proof_Equal _ _ _ _ P              =>
    Bottom_Id_Proof_Equal _ _ _ _ (os_exists_qo_bottom_id_equal_implies_os_exists_bottom_id_equal S eq lte b anti P)
| Qo_Bottom_Id_Proof_Not_Equal _ _ _ _ P          =>
    Bottom_Id_Proof_Not_Equal _ _ _ _ (os_exists_qo_bottom_id_not_equal_implies_os_exists_bottom_id_not_equal S eq lte b sym anti P)
end. 

Lemma os_exists_qo_top_implies_os_exists_top
      (S : Type) (eq lte : brel S)
      (d : brel_exists_qo_top S eq lte) : brel_exists_top S lte.
Proof. destruct d as [b [A B]]. 
       exists b; auto. 
Defined.        
       
Lemma os_not_exists_qo_top_implies_os_not_exists_top
      (S : Type) (eq lte : brel S)
      (anti : brel_antisymmetric S eq lte) 
      (d : brel_not_exists_qo_top S eq lte) : brel_not_exists_top S lte.
Proof. unfold brel_not_exists_qo_top in d.
       intro s. destruct (d s) as [A | [a [[A B] C]]]; auto.
       rewrite (anti _ _ A B) in C. discriminate C. 
Qed.

Lemma os_exists_qo_top_ann_equal_implies_os_exists_top_ann_equal
      (S : Type) (eq lte : brel S) (times : binary_op S) 
      (anti : brel_antisymmetric S eq lte) 
      (d : A_os_exists_qo_top_ann_equal eq lte times) : A_os_exists_top_ann_equal eq lte times.
Proof. destruct d as [b [[A B] C]].
       exists b; auto. 
Defined.        

Lemma os_exists_qo_top_ann_not_equal_implies_os_exists_top_ann_not_equal
      (S : Type) (eq lte : brel S) (times : binary_op S)
      (sym : brel_symmetric S eq) 
      (anti : brel_antisymmetric S eq lte) 
      (d : A_os_exists_qo_top_ann_not_equal eq lte times) : A_os_exists_top_ann_not_equal eq lte times.
Proof. destruct d as [[b i] [[[A B] C] D]].
       exists (b, i); split; auto.
Defined.        

Definition os_exists_top_ann_decidable_from_os_exists_qo_top_ann_decidable
           (S : Type) (eq lte : brel S) (b : binary_op S)
           (sym : brel_symmetric S eq)            
           (anti : brel_antisymmetric S eq lte) 
           (d : os_exists_qo_top_ann_decidable S eq lte b) :
                  os_exists_top_ann_decidable S eq lte b :=   
match d with
| Qo_Top_Ann_Proof_None _ _ _ _ (nqob, nid)     =>
     Top_Ann_Proof_None _ _ _ _ (os_not_exists_qo_top_implies_os_not_exists_top S eq lte anti nqob, nid) 
| Qo_Top_Ann_Proof_Top_None _ _ _ _ (qob, nid) =>
     Top_Ann_Proof_Top_None _ _ _ _ (os_exists_qo_top_implies_os_exists_top S eq lte  qob, nid) 
| Qo_Top_Ann_Proof_None_Ann _ _ _ _ (nqob, idP)    =>
  Top_Ann_Proof_None_Ann _ _ _ _ (os_not_exists_qo_top_implies_os_not_exists_top S eq lte anti nqob, idP)    
| Qo_Top_Ann_Proof_Equal _ _ _ _ P              =>
    Top_Ann_Proof_Equal _ _ _ _ (os_exists_qo_top_ann_equal_implies_os_exists_top_ann_equal S eq lte b anti P)
| Qo_Top_Ann_Proof_Not_Equal _ _ _ _ P          =>
    Top_Ann_Proof_Not_Equal _ _ _ _ (os_exists_qo_top_ann_not_equal_implies_os_exists_top_ann_not_equal S eq lte b sym anti P)
end. 

End ACAS.


Section CAS.


Inductive assert_left_monotone {S : Type} := 
| Assert_Left_Monotone : @assert_left_monotone S. 

Inductive check_left_monotone {S : Type} := 
| Certify_Left_Monotone : @check_left_monotone S
| Certify_Not_Left_Monotone : (S * (S * S)) → @check_left_monotone S.

Inductive assert_right_monotone {S : Type} := 
| Assert_Right_Monotone : @assert_right_monotone S. 

Inductive check_right_monotone {S : Type} := 
| Certify_Right_Monotone : @check_right_monotone S
| Certify_Not_Right_Monotone : (S * (S * S)) → @check_right_monotone S.

Inductive assert_left_strictly_monotone {S : Type} := 
| Assert_Left_Strictly_Monotone : @assert_left_strictly_monotone S. 

Inductive check_left_strictly_monotone {S : Type} := 
| Certify_Left_Strictly_Monotone : @check_left_strictly_monotone S
| Certify_Not_Left_Strictly_Monotone : (S * (S * S)) → @check_left_strictly_monotone S.

Inductive assert_right_strictly_monotone {S : Type} := 
| Assert_Right_Strictly_Monotone : @assert_right_strictly_monotone S. 

Inductive check_right_strictly_monotone {S : Type} := 
| Certify_Right_Strictly_Monotone : @check_right_strictly_monotone S
| Certify_Not_Right_Strictly_Monotone : (S * (S * S)) → @check_right_strictly_monotone S.


Inductive assert_left_increasing {S : Type} := 
| Assert_Left_Increasing : @assert_left_increasing S. 

Inductive check_left_increasing {S : Type} := 
| Certify_Left_Increasing : @check_left_increasing S
| Certify_Not_Left_Increasing : (S * S) → @check_left_increasing S.

Inductive assert_right_increasing {S : Type} := 
| Assert_Right_Increasing : @assert_right_increasing S. 

Inductive check_right_increasing {S : Type} := 
| Certify_Right_Increasing : @check_right_increasing S
| Certify_Not_Right_Increasing : (S * S) → @check_right_increasing S.

Inductive assert_left_strictly_increasing {S : Type} := 
| Assert_Left_Strictly_Increasing : @assert_left_strictly_increasing S. 

Inductive check_left_strictly_increasing {S : Type} := 
| Certify_Left_Strictly_Increasing : @check_left_strictly_increasing S
| Certify_Not_Left_Strictly_Increasing : (S * S) → @check_left_strictly_increasing S.

Inductive assert_right_strictly_increasing {S : Type} := 
| Assert_Right_Strictly_Increasing : @assert_right_strictly_increasing S. 

Inductive check_right_strictly_increasing {S : Type} := 
| Certify_Right_Strictly_Increasing : @check_right_strictly_increasing S
| Certify_Not_Right_Strictly_Increasing : (S * S) → @check_right_strictly_increasing S.

(********************** Top, bottom vs id ann *****************************************)
(* quasi ordered *) 

Inductive os_qo_exists_bottom_id_equal {S : Type} :=
|  Assert_Os_Qo_Exists_Bottom_Id_Equal : S -> @os_qo_exists_bottom_id_equal  S.

Inductive os_qo_exists_bottom_id_not_equal {S : Type} :=
|  Assert_Os_Qo_Exists_Bottom_Id_Not_Equal : S * S -> @os_qo_exists_bottom_id_not_equal S.

Inductive os_exists_qo_bottom_id_certificate {S : Type} :=
| Qo_Bottom_Id_Cert_None        : @os_exists_qo_bottom_id_certificate S
| Qo_Bottom_Id_Cert_Bottom_None : S -> @os_exists_qo_bottom_id_certificate S
| Qo_Bottom_Id_Cert_None_Id     : S -> @os_exists_qo_bottom_id_certificate S
| Qo_Bottom_Id_Cert_Equal       : S -> @os_exists_qo_bottom_id_certificate S
| Qo_Bottom_Id_Cert_Not_Equal   : S * S -> @os_exists_qo_bottom_id_certificate S.


(********************** top vs ann *****************************************)
(* quasi ordered *) 

Inductive os_qo_exists_top_ann_equal {S : Type} :=
|  Assert_Os_Qo_Exists_Top_Ann_Equal : S -> @os_qo_exists_top_ann_equal  S.

Inductive os_qo_exists_top_ann_not_equal {S : Type} :=
|  Assert_Os_Qo_Exists_Top_Ann_Not_Equal : S * S -> @os_qo_exists_top_ann_not_equal S.

Inductive os_exists_qo_top_ann_certificate {S : Type} :=
| Qo_Top_Ann_Cert_None        : @os_exists_qo_top_ann_certificate S
| Qo_Top_Ann_Cert_Top_None    : S -> @os_exists_qo_top_ann_certificate S
| Qo_Top_Ann_Cert_None_Ann    : S -> @os_exists_qo_top_ann_certificate S
| Qo_Top_Ann_Cert_Equal       : S -> @os_exists_qo_top_ann_certificate S
| Qo_Top_Ann_Cert_Not_Equal   : S * S -> @os_exists_qo_top_ann_certificate S.



(* partially ordered *)

(********************** bottom vs id *****************************************)

Inductive os_exists_bottom_id_equal {S : Type} := 
|  Assert_Os_Exists_Bottom_Id_Equal : S -> @os_exists_bottom_id_equal S. 

Inductive os_exists_bottom_id_not_equal {S : Type} := 
|  Assert_Os_Exists_Bottom_Id_Not_Equal : (S * S) -> @os_exists_bottom_id_not_equal S. 

Definition extract_exist_bottom_from_exists_bottom_id_equal {S : Type} 
           (P : @os_exists_bottom_id_equal S) : @assert_exists_bottom S :=
  match P with
  | Assert_Os_Exists_Bottom_Id_Equal i => Assert_Exists_Bottom i 
  end. 

Definition extract_exist_id_from_exists_bottom_id_equal {S : Type} 
           (P : @os_exists_bottom_id_equal S) : @assert_exists_id S := 
  match P with
  | Assert_Os_Exists_Bottom_Id_Equal i => Assert_Exists_Id i 
  end. 

Definition extract_exist_bottom_from_exists_bottom_id_not_equal {S : Type} 
           (P :  @os_exists_bottom_id_not_equal S) : @assert_exists_bottom S :=
  match P with
  | Assert_Os_Exists_Bottom_Id_Not_Equal (b, _) => Assert_Exists_Bottom b
  end. 

Definition extract_exist_id_from_exists_bottom_id_not_equal {S : Type} 
           (P : @os_exists_bottom_id_not_equal S) : @assert_exists_id S := 
  match P with
  | Assert_Os_Exists_Bottom_Id_Not_Equal (_, i) => Assert_Exists_Id i 
  end. 

Inductive os_exists_bottom_id_certificate {S : Type} : Type :=
| Bottom_Id_Cert_None        : @os_exists_bottom_id_certificate S 
| Bottom_Id_Cert_Bottom_None : S -> @os_exists_bottom_id_certificate S 
| Bottom_Id_Cert_None_Id     : S -> @os_exists_bottom_id_certificate S 
| Bottom_Id_Cert_Equal       : S -> @os_exists_bottom_id_certificate S 
| Bottom_Id_Cert_Not_Equal   : (S * S) -> @os_exists_bottom_id_certificate S.


Definition extract_exists_id_certificate_from_exists_bottom_id_certificate
           {S : Type} 
           (P : @os_exists_bottom_id_certificate S) : @check_exists_id S :=
match P with
| Bottom_Id_Cert_None              => Certify_Not_Exists_Id 
| Bottom_Id_Cert_Bottom_None  _    => Certify_Not_Exists_Id 
| Bottom_Id_Cert_None_Id id        => Certify_Exists_Id id 
| Bottom_Id_Cert_Equal bot_id      => Certify_Exists_Id bot_id
| Bottom_Id_Cert_Not_Equal (_, id) => Certify_Exists_Id id 
end.

Definition extract_exists_bottom_certificate_from_exists_bottom_id_certificate
           {S : Type} 
           (P : @os_exists_bottom_id_certificate S) : @certify_exists_bottom S :=
match P with
| Bottom_Id_Cert_None                => Certify_Not_Exists_Bottom 
| Bottom_Id_Cert_Bottom_None  bot    => Certify_Exists_Bottom bot
| Bottom_Id_Cert_None_Id _           => Certify_Not_Exists_Bottom 
| Bottom_Id_Cert_Equal bot_id        => Certify_Exists_Bottom bot_id
| Bottom_Id_Cert_Not_Equal (bot, _)  => Certify_Exists_Bottom bot
end.

(********************** Top vs ann *****************************************)

Inductive os_exists_top_ann_equal {S : Type} := 
|  Assert_Os_Exists_Top_Ann_Equal : S -> @os_exists_top_ann_equal S. 

Inductive os_exists_top_ann_not_equal {S : Type} := 
|  Assert_Os_Exists_Top_Ann_Not_Equal : (S * S) -> @os_exists_top_ann_not_equal S. 

Definition extract_exist_top_from_exists_top_ann_equal {S : Type} 
           (P : @os_exists_top_ann_equal S) : @assert_exists_top S :=
  match P with
  | Assert_Os_Exists_Top_Ann_Equal i => Assert_Exists_Top i 
  end. 

Definition extract_exist_ann_from_exists_top_ann_equal {S : Type} 
           (P : @os_exists_top_ann_equal S) : @assert_exists_id S := 
  match P with
  | Assert_Os_Exists_Top_Ann_Equal i => Assert_Exists_Id i 
  end. 

Definition extract_exist_top_from_exists_top_ann_not_equal {S : Type} 
           (P :  @os_exists_top_ann_not_equal S) : @assert_exists_top S :=
  match P with
  | Assert_Os_Exists_Top_Ann_Not_Equal (b, _) => Assert_Exists_Top b
  end. 

Definition extract_exist_ann_from_exists_top_ann_not_equal {S : Type} 
           (P : @os_exists_top_ann_not_equal S) : @assert_exists_ann S := 
  match P with
  | Assert_Os_Exists_Top_Ann_Not_Equal (_, a) => Assert_Exists_Ann a
  end. 

Inductive os_exists_top_ann_certificate {S : Type} : Type :=
| Top_Ann_Cert_None        : @os_exists_top_ann_certificate S 
| Top_Ann_Cert_Top_None    : S -> @os_exists_top_ann_certificate S 
| Top_Ann_Cert_None_Ann    : S -> @os_exists_top_ann_certificate S 
| Top_Ann_Cert_Equal       : S -> @os_exists_top_ann_certificate S 
| Top_Ann_Cert_Not_Equal   : (S * S) -> @os_exists_top_ann_certificate S.


Definition extract_exists_ann_certificate_from_exists_top_ann_certificate
           {S : Type} 
           (P : @os_exists_top_ann_certificate S) : @check_exists_ann S :=
match P with
| Top_Ann_Cert_None               => Certify_Not_Exists_Ann
| Top_Ann_Cert_Top_None  _        => Certify_Not_Exists_Ann 
| Top_Ann_Cert_None_Ann ann       => Certify_Exists_Ann ann
| Top_Ann_Cert_Equal top_ann      => Certify_Exists_Ann top_ann
| Top_Ann_Cert_Not_Equal (_, ann) => Certify_Exists_Ann ann  
end.

Definition extract_exists_top_certificate_from_exists_top_ann_certificate
           {S : Type} 
           (P : @os_exists_top_ann_certificate S) : @certify_exists_top S :=
match P with
| Top_Ann_Cert_None                => Certify_Not_Exists_Top 
| Top_Ann_Cert_Top_None  top       => Certify_Exists_Top top
| Top_Ann_Cert_None_Ann _          => Certify_Not_Exists_Top 
| Top_Ann_Cert_Equal top_ann       => Certify_Exists_Top top_ann
| Top_Ann_Cert_Not_Equal (top, _)  => Certify_Exists_Top top
end.

End CAS. 


Section Translation.

Variables (S : Type) (eq lte : brel S) (b : binary_op S).
  
Definition p2c_left_monotone (d : os_left_monotone_decidable lte b) : @check_left_monotone S := 
   match d with 
   | inl _ => Certify_Left_Monotone 
   | inr p => Certify_Not_Left_Monotone (projT1 p) 
   end. 

Definition p2c_right_monotone (d : os_right_monotone_decidable lte b) : @check_right_monotone S := 
   match d with 
   | inl _ => Certify_Right_Monotone
   | inr p => Certify_Not_Right_Monotone (projT1 p)
   end. 


Definition p2c_left_increasing (d : os_left_increasing_decidable lte b) : @check_left_increasing S := 
   match d with 
   | inl _ => Certify_Left_Increasing 
   | inr p => Certify_Not_Left_Increasing (projT1 p) 
   end. 

Definition p2c_right_increasing (d : os_right_increasing_decidable lte b) : @check_right_increasing S := 
   match d with 
   | inl _ => Certify_Right_Increasing
   | inr p => Certify_Not_Right_Increasing (projT1 p)
   end.

Definition p2c_os_exists_bottom_id_decidable (d : os_exists_bottom_id_decidable S eq lte b) :
              @os_exists_bottom_id_certificate S :=
match d with
| Bottom_Id_Proof_None _ _ _ _ (_,_)         => Bottom_Id_Cert_None   
| Bottom_Id_Proof_Bottom_None _ _ _ _ (P, _) => Bottom_Id_Cert_Bottom_None (projT1 P) 
| Bottom_Id_Proof_None_Id _ _ _ _ (_, P)     => Bottom_Id_Cert_None_Id (projT1 P) 
| Bottom_Id_Proof_Equal _ _ _ _ P            => Bottom_Id_Cert_Equal (projT1 P) 
| Bottom_Id_Proof_Not_Equal _ _ _ _ P        => Bottom_Id_Cert_Not_Equal (projT1 P)  
end. 

Definition p2c_os_exists_top_ann_decidable (d : os_exists_top_ann_decidable S eq lte b) :
              @os_exists_top_ann_certificate S :=
match d with
| Top_Ann_Proof_None _ _ _ _ (_,_)         => Top_Ann_Cert_None   
| Top_Ann_Proof_Top_None _ _ _ _ (P, _)    => Top_Ann_Cert_Top_None (projT1 P) 
| Top_Ann_Proof_None_Ann _ _ _ _ (_, P)    => Top_Ann_Cert_None_Ann (projT1 P) 
| Top_Ann_Proof_Equal _ _ _ _ P            => Top_Ann_Cert_Equal (projT1 P) 
| Top_Ann_Proof_Not_Equal _ _ _ _ P        => Top_Ann_Cert_Not_Equal (projT1 P)  
end.


Definition p2c_os_exists_bottom_id_equal
           (d : A_os_exists_bottom_id_equal eq lte b) : @os_exists_bottom_id_equal S := 
 Assert_Os_Exists_Bottom_Id_Equal (projT1 d). 

Definition p2c_os_exists_bottom_id_not_equal
           (d : A_os_exists_bottom_id_not_equal eq lte b) : @os_exists_bottom_id_not_equal S := 
 Assert_Os_Exists_Bottom_Id_Not_Equal (projT1 d). 

Definition p2c_os_exists_top_ann_equal
           (d : A_os_exists_top_ann_equal eq lte b) : @os_exists_top_ann_equal S := 
 Assert_Os_Exists_Top_Ann_Equal (projT1 d). 

Definition p2c_os_exists_top_ann_not_equal
           (d : A_os_exists_top_ann_not_equal eq lte b) : @os_exists_top_ann_not_equal S := 
  Assert_Os_Exists_Top_Ann_Not_Equal (projT1 d).


Definition p2c_os_exists_qo_bottom_id_decidable (d : os_exists_qo_bottom_id_decidable S eq lte b) :
              @os_exists_qo_bottom_id_certificate S :=
match d with
| Qo_Bottom_Id_Proof_None _ _ _ _ (_,_)         => Qo_Bottom_Id_Cert_None   
| Qo_Bottom_Id_Proof_Bottom_None _ _ _ _ (P, _) => Qo_Bottom_Id_Cert_Bottom_None (projT1 P) 
| Qo_Bottom_Id_Proof_None_Id _ _ _ _ (_, P)     => Qo_Bottom_Id_Cert_None_Id (projT1 P) 
| Qo_Bottom_Id_Proof_Equal _ _ _ _ P            => Qo_Bottom_Id_Cert_Equal (projT1 P) 
| Qo_Bottom_Id_Proof_Not_Equal _ _ _ _ P        => Qo_Bottom_Id_Cert_Not_Equal (projT1 P)  
end. 

Definition p2c_os_exists_qo_top_ann_decidable (d : os_exists_qo_top_ann_decidable S eq lte b) :
              @os_exists_qo_top_ann_certificate S :=
match d with
| Qo_Top_Ann_Proof_None _ _ _ _ (_,_)         => Qo_Top_Ann_Cert_None   
| Qo_Top_Ann_Proof_Top_None _ _ _ _ (P, _)    => Qo_Top_Ann_Cert_Top_None (projT1 P) 
| Qo_Top_Ann_Proof_None_Ann _ _ _ _ (_, P)    => Qo_Top_Ann_Cert_None_Ann (projT1 P) 
| Qo_Top_Ann_Proof_Equal _ _ _ _ P            => Qo_Top_Ann_Cert_Equal (projT1 P) 
| Qo_Top_Ann_Proof_Not_Equal _ _ _ _ P        => Qo_Top_Ann_Cert_Not_Equal (projT1 P)  
end.


  
End Translation. 


Section Verify.




End Verify.   


