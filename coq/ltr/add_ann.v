Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool. 

Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.ast.

Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.eqv.add_constant.
Require Import CAS.coq.eqv.sum. 

Require Import CAS.coq.sg.properties.
Require Import CAS.coq.sg.structures.
Require Import CAS.coq.sg.theory.
Require Import CAS.coq.sg.cast_up.

Require Import CAS.coq.tr.properties.
Require Import CAS.coq.tr.structures.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Open Scope string_scope.
Import ListNotations.

Section Computation.

Definition ltr_add_ann_op {L S : Type} : 
  ltr_type L S -> cas_constant -> ltr_type L (cas_constant + S) :=
  λ ltr c l s, 
    match s with 
    | inl w => inl w
    | inr v => inr (ltr l v) 
    end. 

 
End Computation. 

Section Theory.


  Context {L S : Type}.
  Variable c : cas_constant.
  Variable eqS : brel S.
  Variable eqL : brel L.
  Variable wS : S.
  Variable wL : L.
  Variable ltr : ltr_type L S.
  Variable refS : brel_reflexive S eqS.


  Lemma ltr_add_ann_congruence : 
    ltr_congruence L S eqL eqS ltr -> 
    ltr_congruence L (with_constant S) eqL 
    (brel_sum brel_constant eqS) (ltr_add_ann_op ltr c).
  Proof.
    intros Ha ? ? [sa | sa] [sb | sb] Hb Hc;
    simpl in * |- *;
    try assumption.
    apply Ha;
    try assumption.
  Defined.


  Lemma ltr_add_ann_is_right : ltr_is_right L S eqS ltr -> 
    ltr_is_right L (with_constant S) 
    (brel_sum brel_constant eqS) (ltr_add_ann_op ltr c).
  Proof.
    intros Ha ? [sa | sa]; simpl.
    + reflexivity.
    + apply Ha.
  Defined.


  Lemma ltr_add_ann_not_is_right : ltr_not_is_right L S eqS ltr -> 
    ltr_not_is_right L (with_constant S)
    (brel_sum brel_constant eqS) (ltr_add_ann_op ltr c).
  Proof.
    intros ((l, s) & H).
    exists (l, inr s);
    simpl.
    exact H.
  Defined.


  Lemma ltr_add_ann_is_right_decidable : ltr_is_right_decidable L S eqS ltr ->
    ltr_is_right_decidable L (with_constant S) 
    (brel_sum brel_constant eqS) (ltr_add_ann_op ltr c).
  Proof.
    intros [Ha | Ha].
    + left.  
      apply ltr_add_ann_is_right;
      try assumption.
    + right.
      apply ltr_add_ann_not_is_right; 
      try assumption.
  Defined.

  
  Lemma ltr_add_ann_is_id : ltr_is_id L S eqS ltr wL ->
    ltr_is_id L (with_constant S) 
      (brel_sum brel_constant eqS) (ltr_add_ann_op ltr c) wL.
  Proof.
    intros Ha [sa | sa]; simpl.
    + reflexivity.
    + apply Ha.
  Defined.  

  Lemma ltr_add_ann_not_is_id : ltr_not_is_id L S eqS ltr wL ->
    ltr_not_is_id L (with_constant S) 
      (brel_sum brel_constant eqS) (ltr_add_ann_op ltr c) wL.
  Proof.
    intros (s & Hs).
    exists (inr s);
    exact Hs.
  Defined.
  

  Lemma ltr_add_ann_exists_id :  ltr_exists_id L S eqS ltr ->
    ltr_exists_id  L (with_constant S) 
    (brel_sum brel_constant eqS) (ltr_add_ann_op ltr c).
  Proof.
    intros (l & Hl).
    exists l; simpl.
    unfold ltr_is_id in * |- *.
    intros [sa | sa];
    simpl.
    + reflexivity.
    + apply Hl.
  Defined.
  

  Lemma ltr_add_ann_not_exists_id : 
    ltr_not_exists_id L S eqS ltr ->
    ltr_not_exists_id  L (with_constant S) 
    (brel_sum brel_constant eqS) (ltr_add_ann_op ltr c).
  Proof.
    intros Ha l. 
    unfold ltr_not_exists_id in * |- *.
    destruct (Ha l) as (x & Hx).
    exists (inr x);
    exact Hx.
  Defined.
  
  
  Lemma ltr_add_ann_exists_id_decidable : 
    ltr_exists_id_decidable L S eqS ltr -> 
    ltr_exists_id_decidable L (with_constant S) 
    (brel_sum brel_constant eqS) (ltr_add_ann_op ltr c).
  Proof.
    intros [H | H].
    + left. 
      apply ltr_add_ann_exists_id;
      try assumption.
    + right.
      apply ltr_add_ann_not_exists_id;
      try assumption.
  Defined.


  Lemma ltr_add_ann_is_ann : ltr_is_ann L S eqS ltr wS ->
    ltr_is_ann L (with_constant S) 
    (brel_sum brel_constant eqS) (ltr_add_ann_op ltr c) (inr wS).
  Proof.
    unfold ltr_is_ann.
    intros Ha ?. 
    exact (Ha l).
  Defined.


  Lemma ltr_add_ann_not_is_ann : ltr_not_is_ann L S eqS ltr wS ->
    ltr_not_is_ann L (with_constant S) 
    (brel_sum brel_constant eqS) (ltr_add_ann_op ltr c) (inr wS).
  Proof.
    intros (l & Hl).
    exists l; exact Hl.
  Defined.


  Lemma ltr_add_ann_exists_ann :
    ltr_exists_ann L (with_constant S) 
    (brel_sum brel_constant eqS) (ltr_add_ann_op ltr c).
  Proof.
    unfold ltr_exists_ann.
    exists (inl c);
    unfold ltr_is_ann.
    intros ?.
    reflexivity.
  Defined.


  Lemma ltr_add_ann_left_cancellative : ltr_left_cancellative L S eqS ltr ->
    ltr_left_cancellative L (with_constant S) 
    (brel_sum brel_constant eqS) (ltr_add_ann_op ltr c).
  Proof.
    unfold ltr_left_cancellative.
    intros Ha ? [sa | sa] [sb | sb] Hb;
    simpl in * |- *.
    + exact Hb.
    + congruence.
    + congruence.
    + eapply Ha;
      exact Hb.
  Defined.


  Lemma ltr_add_ann_not_left_cancellative : 
    ltr_not_left_cancellative L S eqS ltr ->
    ltr_not_left_cancellative L (with_constant S) 
    (brel_sum brel_constant eqS) (ltr_add_ann_op ltr c).
  Proof.
    unfold ltr_not_left_cancellative.
    intros ((au, (bu, cu)) & Ha & Hb).
    exists (au, (inr bu, inr cu));
    simpl.
    exact (Ha, Hb).
  Defined.


  Lemma ltr_add_ann_left_cancellative_decidable :
    ltr_left_cancellative_decidable L S eqS ltr ->
    ltr_left_cancellative_decidable L (with_constant S)
    (brel_sum brel_constant eqS) (ltr_add_ann_op ltr c).
  Proof.
    intros [H | H].
    + left.
      apply ltr_add_ann_left_cancellative;
      try assumption.
    + right.
      apply ltr_add_ann_not_left_cancellative;
      try assumption.
  Defined.
  
    
  Lemma ltr_add_ann_not_left_constant :
    ltr_not_left_constant L (with_constant S)
    (brel_sum brel_constant eqS) (ltr_add_ann_op ltr c).
  Proof.
    unfold ltr_not_left_constant.
    exists (wL, (inl c, inr wS));
    simpl.
    reflexivity.
  Defined.

End Theory.


Section ACAS.

 
  
  Definition A_ltr_add_ann_proofs 
    {L S : Type} 
    (c : cas_constant)
    (wS : S)
    (wL : L)
    (eqS : brel S)
    (eqL : brel L)
    (ltr : ltr_type L S) 
    (Ha : left_transform_proofs L S eqS eqL ltr) : 
    left_transform_proofs L (with_constant S)
      (brel_sum brel_constant eqS) eqL 
      (ltr_add_ann_op ltr c) := 
    {|
      A_left_transform_congruence  := 
        ltr_add_ann_congruence c eqS eqL ltr 
          (A_left_transform_congruence _ _ _ _ _ Ha) 
    ; A_left_transform_is_right_d  := 
        ltr_add_ann_is_right_decidable c eqS ltr 
          (A_left_transform_is_right_d _ _ _ _ _ Ha) 
    ; A_left_transform_left_constant_d := 
        inr (ltr_add_ann_not_left_constant c eqS 
          wS wL ltr)
    ; A_left_transform_left_cancellative_d := 
        ltr_add_ann_left_cancellative_decidable c eqS ltr
          (A_left_transform_left_cancellative_d _ _ _ _ _ Ha)
    |}.



Definition A_ltr_add_ann 
    {L S : Type}
    (c : cas_constant)
    (Hl : A_left_transform L S) : 
    A_left_transform L (with_constant S) := 
    {|
        A_left_transform_carrier :=  
          A_eqv_add_constant S (A_left_transform_carrier _ _ Hl) c
      ; A_left_transform_label  := 
          A_left_transform_label _ _ Hl                                                    
      ; A_left_transform_ltr  := 
          (ltr_add_ann_op (A_left_transform_ltr _ _ Hl) c)
      ; A_left_transform_exists_id_d  := 
          ltr_add_ann_exists_id_decidable c
          (A_eqv_eq S (A_left_transform_carrier L S Hl))
          (A_left_transform_ltr L S Hl) 
          (A_left_transform_exists_id_d L S Hl)
      ; A_left_transform_exists_ann_d := 
          inl
          (ltr_add_ann_exists_ann c
            (A_eqv_eq S (A_left_transform_carrier L S Hl))
            (A_left_transform_ltr L S Hl)) 
      ; A_left_transform_proofs  :=  A_ltr_add_ann_proofs c
          (A_eqv_witness S (A_left_transform_carrier L S Hl))
          (A_eqv_witness L (A_left_transform_label L S Hl))
          (A_eqv_eq S (A_left_transform_carrier L S Hl))
          (A_eqv_eq L (A_left_transform_label L S Hl))
          (A_left_transform_ltr L S Hl) 
          (A_left_transform_proofs _ _ Hl)
      ; A_left_transform_ast  := Cas_ast ("A_left_transform_with_constant", 
        [A_left_transform_ast _ _ Hl])
    |}.

End ACAS.


Section AMCAS.

  Definition A_mcas_ltr_add_ann {L S : Type}
    (Hl : A_ltr_mcas L S) (c : cas_constant) :=
    match Hl with 
    | A_MCAS_ltr_Error _ _ err =>  A_MCAS_ltr_Error _ _ err
    | A_MCAS_ltr _ _ Hlt =>  @A_MCAS_ltr L (with_constant S) (A_ltr_add_ann c Hlt)
    end.

  (* 
  Definition A_mcas_ltr_add_ann {L S : Type}
    (Hl : A_left_transform L S) (c : cas_constant) := 
    @A_MCAS_ltr L (with_constant S) (A_ltr_add_ann c Hl).
  *)

End AMCAS.

Section Certificate.


  Context {L S : Type}.


Definition ltr_add_ann_congruence_cert 
    (Ha : @assert_ltr_congruence L S) : 
  @assert_ltr_congruence L (with_constant S) :=
  @Assert_Ltr_Congruence L (with_constant S).

Definition  ltr_add_ann_is_right_certs 
    (Ha : @check_ltr_is_right L S) :
  @check_ltr_is_right L (with_constant S) :=
  match Ha with
  | Certify_Ltr_Is_Right => Certify_Ltr_Is_Right
  | Certify_Ltr_Not_Is_Right p => Certify_Ltr_Not_Is_Right (fst p, inr (snd p))
  end. 
    
Definition ltr_add_ann_exists_id_certs 
    (Ha : @check_ltr_exists_id L S): 
        @check_ltr_exists_id L (with_constant S ) :=
       match Ha with
       | Certify_Ltr_Exists_Id l    => Certify_Ltr_Exists_Id l
       | Certify_Ltr_Not_Exists_Id => Certify_Ltr_Not_Exists_Id
       end.
                                    

(*   
  Print ltr_add_ann_exists_id_certs. 
ltr_add_ann_exists_id_certs = 
λ Ha : check_ltr_exists_id,
  match Ha as c return (Ha = c → check_ltr_exists_id) with
  | Certify_Ltr_Exists_Id l =>
      λ _ : Ha = Certify_Ltr_Exists_Id l, Certify_Ltr_Exists_Id l
  | Certify_Ltr_Not_Exists_Id =>
      λ _ : Ha = Certify_Ltr_Not_Exists_Id, Certify_Ltr_Not_Exists_Id
  end eq_refl
     : check_ltr_exists_id → check_ltr_exists_id

  This extracts to 

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

let ltr_add_ann_exists_id_certs ha =
  (match ha with
   | Certify_Ltr_Exists_Id l -> (fun _ -> Certify_Ltr_Exists_Id l)
   | Certify_Ltr_Not_Exists_Id -> (fun _ -> Certify_Ltr_Not_Exists_Id)) __


*)     

Definition ltr_add_ann_left_cancellative_certs 
    (Ha : @check_ltr_left_cancellative L S) : 
  @check_ltr_left_cancellative L (with_constant S) :=
  match Ha with
  | Certify_Ltr_Left_Cancellative => Certify_Ltr_Left_Cancellative
  | Certify_Ltr_Not_Left_Cancellative (l, (s1, s2)) =>
      Certify_Ltr_Not_Left_Cancellative (l, (inr s1, inr s2))
  end. 

End Certificate.



Section CAS. 


  Definition ltr_add_ann_certs  
    {L S : Type} 
    (c : cas_constant)
    (wS : S)
    (wL : L) 
    (Ha : @left_transform_certificates L S) :  
    @left_transform_certificates L (with_constant S) := 
    {|
      left_transform_congruence  := ltr_add_ann_congruence_cert 
        (left_transform_congruence Ha)
    ; left_transform_is_right_d  := ltr_add_ann_is_right_certs 
        (left_transform_is_right_d Ha) 
    ; left_transform_left_constant_d :=  (Certify_Ltr_Not_Left_Constant  (wL, (inl c, inr wS)))
    ; left_transform_left_cancellative_d := ltr_add_ann_left_cancellative_certs 
        (left_transform_left_cancellative_d Ha) 
    |}.

Definition ltr_add_ann 
    {L S : Type}
    (c : cas_constant)
    (Hl : left_transform L S) : 
    left_transform L (with_constant S) := 
    {|
        left_transform_carrier  := eqv_add_constant (left_transform_carrier _ _ Hl) c 
      ; left_transform_label  := left_transform_label _ _ Hl                                                 
      ; left_transform_ltr  := ltr_add_ann_op (left_transform_ltr _ _ Hl) c 
      ; left_transform_exists_id_d  := 
          ltr_add_ann_exists_id_certs (left_transform_exists_id_d _ _ Hl)  
      ; left_transform_exists_ann_d := Certify_Ltr_Exists_Ann (inl c)
      ; left_transform_certs  := 
        @ltr_add_ann_certs _ _ c 
        (eqv_witness (left_transform_carrier _ _ Hl)) 
        (eqv_witness (left_transform_label L S Hl)) (left_transform_certs _ _ Hl) 
      ; left_transform_ast := Cas_ast ("A_left_transform_with_constant", 
        [left_transform_ast _ _ Hl])
    |}.


End CAS. 

Section MCAS.

  Definition mcas_ltr_add_ann {L S : Type}
    (Hl : @ltr_mcas L S) (c : cas_constant) :=
    match Hl with 
    | @MCAS_ltr_Error _ _ err =>  @MCAS_ltr_Error _ _ err
    | @MCAS_ltr _ _ Hlt =>  @MCAS_ltr L (with_constant S) (ltr_add_ann c Hlt)
    end.
  

End MCAS.

Section Verify.
 

  Lemma correct_ltr_certs_add_ann 
    {L S : Type} 
    (c : cas_constant)
    (wS : S)
    (wL : L)
    (eqS : brel S) 
    (eqL : brel L) 
    (ltr : L → S → S)
    (pf : left_transform_proofs L S eqS eqL ltr) :
    @P2C_left_transform L (with_constant S)
      (brel_sum brel_constant eqS)
      eqL (ltr_add_ann_op ltr c)
      (@A_ltr_add_ann_proofs L S c wS wL eqS eqL ltr pf) = 
    ltr_add_ann_certs c wS wL
      (P2C_left_transform L S eqS eqL ltr pf).
  Proof.
    unfold P2C_left_transform,
    ltr_add_ann_certs; cbn.
    destruct pf; simpl.
    f_equal.
    + destruct A_left_transform_is_right_d as [H | H];
      simpl. 
      ++ reflexivity.
      ++ destruct H, x;
         reflexivity.
    + destruct A_left_transform_left_cancellative_d as [H | H];
      cbn.
      ++ reflexivity.
      ++ destruct H, x, p, y; cbn.
         reflexivity.
  Qed.
  
  
  Lemma correct_ltr_transform_ann_add 
    {L S : Type}
    (c : cas_constant)
    (Hl : A_left_transform L S) : 
    A2C_left_transform L (with_constant S) 
      (A_ltr_add_ann c Hl) = 
    ltr_add_ann c
      (A2C_left_transform L S Hl).
  Proof.
    unfold A2C_left_transform,
    ltr_add_ann; 
    destruct Hl; simpl.
    f_equal.
    + rewrite correct_eqv_add_constant.
      f_equal.
    + destruct A_left_transform_exists_id_d as [H | H];
      cbn.
      ++ destruct H; reflexivity.
      ++ reflexivity.
    + apply correct_ltr_certs_add_ann.
  Qed.


  
  Lemma correct_mcas_ltr_add_ann {L S : Type} 
    (Hl : A_ltr_mcas L S) (c : cas_constant) :
    @A2C_mcas_ltr L (with_constant S) (A_mcas_ltr_add_ann Hl c) = 
    @mcas_ltr_add_ann L _ (A2C_mcas_ltr _ _ Hl) c.
  Proof.
    unfold A_mcas_ltr_add_ann, 
    mcas_ltr_add_ann;
    destruct Hl; simpl.
    + reflexivity.
    + rewrite <-correct_ltr_transform_ann_add.
      f_equal.
  Qed.


  
  
End Verify.




  


    
    

     



   


    




   

    


    



    

    

  
  


