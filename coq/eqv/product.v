Require Import Coq.Bool.Bool.    

Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.data.
Require Import CAS.coq.common.ast.


Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.eqv.theory. 
Require Import CAS.coq.eqv.list.
Require Import CAS.coq.eqv.set. 

Require Import CAS.coq.sg.and. 



Section Computation.

Definition brel_product : ∀ {S T : Type}, brel S → brel T → brel (S * T)
:= λ {S} {T} U V x y, 
   match x, y with
   | (x1, x2), (y1, y2) => bop_and (U x1 y1) (V x2 y2) 
   end.

End Computation. 

Declare Scope brel_product_scope.

Notation "a <*> b"  := (brel_product a b) (at level 15) : brel_product_scope.

Open Scope brel_product_scope.

Section Theory.

Variable S  : Type. 
Variable T  : Type.
Variable wS : S. 
Variable wT : T. 
Variable rS : brel S. 
Variable rT : brel T.

Variable f : S -> S. 
Variable ntS : brel_not_trivial S rS f.
Variable g : T -> T. 
Variable ntT : brel_not_trivial T rT g. 
                                
Variable refS : brel_reflexive S rS. 
Variable symS : brel_symmetric S rS. 
Variable trnS : brel_transitive S rS. 

Variable refT : brel_reflexive T rT.
Variable symT : brel_symmetric T rT. 
Variable trnT : brel_transitive T rT. 



Lemma brel_product_intro (a c : S) (b d : T) (A : rS a c = true) (B : rT b d = true): brel_product rS rT (a, b) (c, d) = true.
Proof. compute. rewrite A, B. reflexivity. Qed.

Lemma brel_product_elim (a c : S) (b d : T) (A: brel_product rS rT (a, b) (c, d) = true) : (rS a c = true) * (rT b d = true). 
Proof. compute in A.
       case_eq(rS a c); intro B; case_eq(rT b d); intro C.
       + auto. 
       + rewrite B, C in A. congruence. 
       + rewrite B in A. congruence. 
       + rewrite B in A. congruence. 
Qed.

Definition uop_product_new (f : S -> S) (p : S * T) := let (s, t) := p in (f s, t). 

Lemma brel_product_not_trivial : brel_not_trivial (S * T) (rS <*> rT) (uop_product_new f).
Proof. intros [s t]. simpl. destruct (ntS s) as [L R].
     rewrite L, R. rewrite (refT t). simpl. auto. 
Defined.


Lemma brel_product_congruence : 
         ∀ (r1 : brel S) (r2 : brel T),  brel_congruence S rS r1  → brel_congruence T rT r2  → 
               brel_congruence (S * T) (rS <*> rT) (r1 <*> r2). 
Proof. unfold brel_congruence. intros r1 r2 C1 C2. 
       intros [s1 s2] [t1 t2] [u1 u2] [v1 v2]. unfold brel_product. 
       intros H1 H2. 
       apply bop_and_elim in H1. destruct H1 as [L1 R1]. 
       apply bop_and_elim in H2. destruct H2 as [L2 R2]. 
       rewrite (C1 _ _ _ _ L1 L2). 
       rewrite (C2 _ _ _ _ R1 R2). reflexivity. 
Defined.



Lemma brel_product_transitive : brel_transitive (S * T) (rS <*> rT). 
Proof. intros [s1 t1] [s2 t2] [s3 t3]. unfold brel_product. 
     intros.           
     apply bop_and_elim in H.  destruct H as [H_l H_r]. 
     apply bop_and_elim in H0. destruct H0 as [H0_l H0_r]. 
     apply bop_and_intro.      
        apply (trnS _ _ _ H_l H0_l). 
        apply (trnT _ _ _ H_r H0_r). 
Defined. 

Lemma brel_product_reflexive : brel_reflexive (S * T) (rS <*> rT). 
Proof. intros [s t]. unfold brel_product. compute. rewrite (refS s), (refT t). reflexivity. Defined. 

Lemma brel_product_symmetric : brel_symmetric (S * T) (rS <*> rT). 
Proof. intros [s1 t1] [s2 t2]; simpl. intro H. 
       apply bop_and_elim in H. destruct H as [H_l H_r].          
       apply bop_and_intro. 
         apply (symS _ _ H_l). 
         apply (symT _ _ H_r). 
Defined. 

(*
Lemma brel_product_not_reflexive_left : ∀ (t : T),   (brel_not_reflexive _ rS) 
               → brel_not_reflexive (S * T) (rS <*> rT). 
Proof. intros t [s P]. exists (s, t). compute. rewrite P. reflexivity.  Defined. 

Lemma brel_product_not_reflexive_right : ∀ (s : S),   (brel_not_reflexive _ rT) 
               → brel_not_reflexive (S * T) (rS <*> rT). 
Proof. unfold brel_not_reflexive. intros s [t P]. 
        exists (s, t). compute. rewrite P. case_eq(rS s s); intro H; auto. 
Defined. 


Lemma brel_product_not_symmetric_left : brel_not_symmetric S rS → T → 
         brel_not_symmetric (S * T) (rS <*> rT). 
Proof. unfold brel_not_symmetric. 
       intros [ [s1 s2] [P1 P2]] t. 
       exists ((s1, t), (s2, t)). compute. 
       rewrite P1, P2, (refT t). auto. 
Defined. 


Lemma brel_product_not_symmetric_right : brel_not_symmetric T rT → S → 
         brel_not_symmetric (S * T) (rS <*> rT). 
Proof. unfold brel_not_symmetric. intros [ [t1 t2] [P1 P2]] s. 
       exists ((s, t1), (s, t2)). compute. rewrite P1, P2, (refS s). auto. 
Defined. 

Definition brel_product_reflexive_decide: 
   ∀ (s : S) (t : T),    
     brel_reflexive_decidable S rS → 
     brel_reflexive_decidable T rT → 
        brel_reflexive_decidable (S * T) (rS <*> rT)
:= λ s t dS dT,  
       match dS with 
       | inl refS => 
         match dT with 
         | inl refT     => inl _ (brel_product_reflexive refS refT)
         | inr not_refT => inr _ (brel_product_not_reflexive_right s not_refT)
         end 
       | inr not_refS   => inr _ (brel_product_not_reflexive_left t not_refS)
       end. 


Definition brel_product_symmetric_decide: 
     S -> T -> brel_symmetric_decidable S rS → brel_symmetric_decidable T rT → 
        brel_symmetric_decidable (S * T) (rS <*> rT)
:= λ wS wT dS dT,  
       match dS with 
       | inl symS => 
         match dT with 
         | inl symT     => inl _ (brel_product_symmetric symS symT)
         | inr not_symT => inr _ (brel_product_not_symmetric_right not_symT wS)
         end 
       | inr not_symS   => inr _ (brel_product_not_symmetric_left not_symS wT)
       end.
*) 

Lemma brel_product_at_least_three : brel_at_least_three (S * T) (rS <*> rT).
Proof. exists ((wS , wT), ((f wS, wT), (wS, g wT))).
       destruct (ntS wS) as [LS RS]. destruct (ntT wT) as [LT RT].       
       compute. rewrite LS, LT, RS; split; auto. rewrite (refS wS); auto. 
Defined. 

Lemma brel_product_not_exactly_two : brel_not_exactly_two (S * T) (rS <*> rT).
Proof. apply brel_at_least_thee_implies_not_exactly_two.
       apply brel_product_symmetric; auto. 
       apply brel_product_transitive; auto.
       apply brel_product_at_least_three; auto. 
Defined.


Definition list_product : S -> list T -> list (S * T) 
:= fix f  s y := 
      match y with
         | nil => nil 
         | t :: rest => (s, t) :: (f s rest)
      end.

Definition lists_product : list S -> list T -> list (S * T) 
:= fix f x y := 
      match x with
         | nil => nil 
         | a :: rest => (list_product a y) ++ (f rest y) 
      end.

Lemma lemm1 (a s : S) (t : T) (Y : finite_set T) (HS : rS a s = true) (HT : in_list rT Y t = true) : 
  in_list (rS <*> rT) (list_product a Y) (s, t) = true.
Proof. induction Y. compute in HT. discriminate HT. 
       apply in_list_cons_elim in HT; auto. destruct HT as [HT | HT].
       unfold list_product. fold @list_product.
       apply in_list_cons_intro. apply brel_product_symmetric; auto.
       left. compute. rewrite HS, HT; auto. 

       unfold list_product. fold @list_product.
       apply in_list_cons_intro. apply brel_product_symmetric; auto.
       right. apply IHY; auto.
Qed.        
       

Lemma lemm2 (s : S) (a t : T) (X : finite_set S) (Y : finite_set T) (HS : in_list rS X s = true) (HT : rT a t = true): 
  in_list (rS <*> rT) (lists_product X (a :: Y)) (s, t) = true.
Proof. induction X. compute in HS. discriminate HS.
       apply in_list_cons_elim in HS; auto. destruct HS as [HS | HS].

       apply in_list_cons_intro. apply brel_product_symmetric; auto.
       left. compute. rewrite HS, HT; auto.        

       unfold lists_product. fold @lists_product. 
       apply in_list_concat_intro. 
       right. apply IHX; auto.
Qed.

Lemma in_list_lists_product (s : S) (t : T) (X : finite_set S) (Y : finite_set T) (HS : in_list rS X s = true) (HT : in_list rT Y t = true) : 
  in_list (rS <*> rT) (lists_product X Y) (s, t) = true.
Proof. induction X; induction Y; auto.
       compute in HT. discriminate HT. 
       apply in_list_cons_elim in HS; auto. apply in_list_cons_elim in HT; auto. 
       destruct HS as [ HS | HS ]; destruct HT as [ HT | HT ].

       unfold lists_product. fold @lists_product. unfold list_product. fold @list_product.
       apply in_list_cons_intro; auto. apply brel_product_symmetric; auto.
       left. compute. rewrite HS, HT; auto. 

       unfold lists_product. fold @lists_product. unfold list_product. fold @list_product.
       apply in_list_concat_intro.
       case_eq(in_list rS X s); intro K.
          right. apply IHX; auto. 
          left. apply in_list_cons_intro. apply brel_product_symmetric; auto.
          right. apply lemm1; auto. 

       unfold lists_product. fold @lists_product. unfold list_product. fold @list_product.
       apply in_list_concat_intro.
       case_eq(in_list rS X s); intro K.
          right. apply IHX; auto. 
          right. apply lemm2; auto. 


       unfold lists_product. fold @lists_product. unfold list_product. fold @list_product.
       apply in_list_concat_intro.
       assert (K := IHX HS). right. exact K. 
Qed. 


Definition product_enum (fS : unit -> list S) (fT : unit -> list T) (x : unit) := lists_product (fS tt) (fT tt). 

Lemma brel_product_finite : carrier_is_finite S rS -> carrier_is_finite T rT -> carrier_is_finite (S * T) (rS <*> rT).
Proof. intros [fS pS] [fT pT]. unfold carrier_is_finite. exists (product_enum fS fT).
       intros [s t]. assert (HS := pS s); assert (HT := pT t).
       unfold product_enum. apply in_list_lists_product; auto.
Defined. 


Lemma in_list_pair_elim_left (s : S) (t : T) (X : list (S * T)) : 
  in_list (rS <*> rT) (X) (s, t) = true -> in_list rS (List.map fst X) s = true.
Proof. intro H. induction X. compute in H. discriminate H.
       destruct a as (s', t'). 
       apply in_list_cons_elim in H; auto. destruct H as [H | H].
       compute in H.
       case_eq(rS s' s); intro Hss; case_eq(rT t' t); intro Htt. 
          unfold List.map. apply in_list_cons_intro; auto.  
          rewrite Hss, Htt in H. discriminate H.
          rewrite Hss in H. discriminate H.
          rewrite Hss in H. discriminate H.                     
       assert (K := IHX H).
       unfold List.map. apply in_list_cons_intro; auto. apply brel_product_symmetric; auto. 
Defined.

Lemma in_list_pair_elim_right (s : S) (t : T) (X : finite_set (S * T)) : 
  in_list (rS <*> rT) (X) (s, t) = true -> in_list rT (List.map snd X) t = true.
Proof. intro H. induction X. compute in H. discriminate H.
       destruct a as (s', t'). 
       apply in_list_cons_elim in H; auto. destruct H as [H | H].
       compute in H.
       case_eq(rS s' s); intro Hss; case_eq(rT t' t); intro Htt. 
          unfold List.map. apply in_list_cons_intro; auto.
          rewrite Hss, Htt in H. discriminate H.
          rewrite Hss in H. discriminate H.
          rewrite Hss in H. discriminate H.
       assert (K := IHX H).
       unfold List.map. apply in_list_cons_intro; auto. apply brel_product_symmetric; auto. 
Defined.

Lemma brel_product_not_finite_left : carrier_is_not_finite S rS -> carrier_is_not_finite (S * T) (rS <*> rT).
Proof. unfold carrier_is_not_finite. intro H.
       intro fST. assert (K := H (λ _, List.map fst (fST tt))).
       destruct K as [s Ps].
       exists (s, wT).
       case_eq(in_list (rS <*> rT) (fST tt) (s, wT)); intro J; auto.
       apply in_list_pair_elim_left in J. 
       rewrite J in Ps. discriminate Ps. 
Defined. 

Lemma brel_product_not_finite_right : carrier_is_not_finite T rT -> carrier_is_not_finite (S * T) (rS <*> rT).
Proof. unfold carrier_is_not_finite. intro H.
       intro fST. assert (K := H (λ _, List.map snd (fST tt))).
       destruct K as [t Pt].
       exists (wS, t).
       case_eq(in_list (rS <*> rT) (fST tt) (wS, t)); intro J; auto.
       apply in_list_pair_elim_right in J.
       rewrite J in Pt. exact Pt. 
Defined. 





End Theory.

Section ACAS.


Definition eqv_product_decidable (S T : Type) (wS : S) (wT : T) (rS : brel S) (rT : brel T) 
         (symS : brel_symmetric S rS) (symT : brel_symmetric T rT) 
         (dS : carrier_is_finite_decidable S rS) (dT: carrier_is_finite_decidable T rT) :
    carrier_is_finite_decidable (S * T) (rS <*> rT)
  := match dS, dT with
     | inr nfS, _ => inr (brel_product_not_finite_left S T wT rS rT symS symT nfS) 
     | _, inr nfT => inr (brel_product_not_finite_right S T wS rS rT symS symT nfT) 
     | inl fS, inl fT => inl (brel_product_finite S T rS rT symS symT fS fT)
     end. 
  

Definition eqv_proofs_product : 
   ∀ (S T : Type) (rS : brel S) (rT : brel T),
       eqv_proofs S rS -> eqv_proofs T rT -> eqv_proofs (S * T) (rS <*> rT) 
:= λ S T rS rT eqvS eqvT, 
{|

  A_eqv_congruence  := brel_product_congruence S T rS rT rS rT 
                        (A_eqv_congruence S rS eqvS)
                        (A_eqv_congruence T rT eqvT)
; A_eqv_reflexive   := brel_product_reflexive S T rS rT 
                        (A_eqv_reflexive S rS eqvS) 
                        (A_eqv_reflexive T rT eqvT) 
; A_eqv_transitive  := brel_product_transitive S T rS rT  
                        (A_eqv_transitive S rS eqvS) 
                        (A_eqv_transitive T rT eqvT) 
; A_eqv_symmetric   := brel_product_symmetric S T rS rT  
                        (A_eqv_symmetric S rS eqvS) 
                        (A_eqv_symmetric T rT eqvT)
|}.



Definition A_eqv_product : ∀ (S T : Type),  A_eqv S -> A_eqv T -> A_eqv (S * T) 
:= λ S T eqvS eqvT,
  let eqS := A_eqv_eq S eqvS in
  let s  := A_eqv_witness S eqvS in
  let f  := A_eqv_new S eqvS in
  let ntS := A_eqv_not_trivial S eqvS in
  let eqT := A_eqv_eq T eqvT in
  let t  := A_eqv_witness T eqvT in
  let g  := A_eqv_new T eqvT in
  let ntT := A_eqv_not_trivial T eqvT in  
  let eqPS := A_eqv_proofs S eqvS in
  let eqPT := A_eqv_proofs T eqvT in
  let refS := A_eqv_reflexive S eqS eqPS in    
  let symS := A_eqv_symmetric S eqS eqPS in
  let trnS := A_eqv_transitive S eqS eqPS in
  let refT := A_eqv_reflexive T eqT eqPT in  
  let symT := A_eqv_symmetric T eqT eqPT in
  let trnT := A_eqv_transitive T eqT eqPT in
   {| 
        A_eqv_eq          := brel_product eqS eqT 
    ; A_eqv_proofs        := eqv_proofs_product S T eqS eqT eqPS eqPT 
    ; A_eqv_witness       := (s, t)
    ; A_eqv_new           := uop_product_new S T f
    ; A_eqv_not_trivial   := brel_product_not_trivial S T eqS eqT f ntS refT 
    ; A_eqv_exactly_two_d := inr (brel_product_not_exactly_two S T s t eqS eqT f ntS g ntT refS symS trnS symT trnT)
    ; A_eqv_data          := λ p, DATA_pair (A_eqv_data S eqvS (fst p), A_eqv_data T eqvT (snd p))
    ; A_eqv_rep           := λ p, (A_eqv_rep S eqvS (fst p), A_eqv_rep T eqvT (snd p))
    ; A_eqv_finite_d      := eqv_product_decidable S T s t eqS eqT symS symT  (A_eqv_finite_d _ eqvS) (A_eqv_finite_d _ eqvT)
    ; A_eqv_ast           := Ast_eqv_product (A_eqv_ast _ eqvS, A_eqv_ast _ eqvT)
   |}.

End ACAS.

Section CAS.

Definition eqv_product_finite_certifiable {S T : Type} (fS : @check_is_finite S ) (fT : @check_is_finite T )
 :=  match fS, fT with
       Certify_Is_Not_Finite, _        => Certify_Is_Not_Finite
     | _, Certify_Is_Not_Finite        => Certify_Is_Not_Finite
     | Certify_Is_Finite f, Certify_Is_Finite g => Certify_Is_Finite (product_enum S T f g)
     end. 

Definition eqv_product : ∀ {S T : Type},  @eqv S -> @eqv T -> @eqv (S * T)
:= λ {S T} eqvS eqvT,
  let eqS := eqv_eq eqvS in
  let eqT := eqv_eq eqvT in
  let s   := eqv_witness eqvS in
  let f   := eqv_new eqvS in  
  let t   := eqv_witness eqvT in
  let g   := eqv_new eqvT in    
  let r   := brel_product eqS eqT in 
   {| 
      eqv_eq            := r
    ; eqv_certs         := 
     {|
       eqv_congruence     := @Assert_Brel_Congruence (S *T)
     ; eqv_reflexive      := @Assert_Reflexive (S * T)
     ; eqv_transitive     := @Assert_Transitive (S *T) 
     ; eqv_symmetric      := @Assert_Symmetric (S * T)

     |}  
    ; eqv_witness       := (s, t)
    ; eqv_new           := uop_product_new S T f
    ; eqv_exactly_two_d := Certify_Not_Exactly_Two (not_ex2 r (s , t) (f s, t) (s, g t))
    ; eqv_data          := λ p, DATA_pair (eqv_data eqvS (fst p), eqv_data eqvT (snd p))
    ; eqv_rep           := λ p, (eqv_rep eqvS (fst p), eqv_rep eqvT (snd p))
    ; eqv_finite_d      := eqv_product_finite_certifiable (eqv_finite_d eqvS) (eqv_finite_d eqvT)
    ; eqv_ast           := Ast_eqv_product (eqv_ast eqvS, eqv_ast eqvT)
   |}. 

End CAS.


Section MCAS.

Definition mcas_eqv_product {S T : Type} (A : @mcas_eqv S) (B : @mcas_eqv T) : @mcas_eqv (S * T) :=
match A, B with
| EQV_eqv C, EQV_eqv D         => EQV_eqv (eqv_product C D)
| EQV_Error sl, EQV_eqv _      => EQV_Error sl
| EQV_eqv _, EQV_Error sl      => EQV_Error sl
| EQV_Error sl1, EQV_Error sl2 => EQV_Error (sl1 ++ sl2)                                                                           
end.                  

End MCAS.


Section Verify.

Lemma correct_eqv_product_decidable (S : Type) (T : Type) (wS : S) (wT : T) (eqS : brel S) (eqT : brel T)
              (symS : brel_symmetric S eqS) (symT : brel_symmetric T eqT) 
              (FS : carrier_is_finite_decidable S eqS) 
              (FT : carrier_is_finite_decidable T eqT) : 
   eqv_product_finite_certifiable (p2c_is_finite_check S eqS FS) (p2c_is_finite_check T eqT FT)
   =   
   p2c_is_finite_check (S * T) (eqS <*> eqT) (eqv_product_decidable S T wS wT eqS eqT symS symT FS FT). 
Proof. destruct FS as [[fS PS] | NFS]; destruct FT as [[fT PT]| NFT]; simpl; auto. Qed. 


Theorem correct_eqv_product :
      ∀ (S T : Type) (eS : A_eqv S) (eT : A_eqv T), 
         eqv_product (A2C_eqv S eS) (A2C_eqv T eT)
         = 
         A2C_eqv (S * T)(A_eqv_product S T eS eT). 
Proof. intros S T eS eT. destruct eS; destruct eT. 
       unfold eqv_product, A_eqv_product, A2C_eqv; simpl.
       rewrite <- correct_eqv_product_decidable. reflexivity. 
Qed.


End Verify.   
  
Close Scope brel_product_scope.
