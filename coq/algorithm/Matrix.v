From Coq Require Import List Utf8
  FunctionalExtensionality BinNatDef 
  Lia Even.
From CAS Require Import coq.common.compute
  coq.eqv.properties coq.eqv.structures
  coq.eqv.theory coq.sg.properties.
Import ListNotations.

Section Lfn.
  (* This is temporary section and the functions defined 
    here will move to another file.*)
  Variables (A : Type)
    (eqA : brel A)
    (refA : brel_reflexive A eqA)
    (symA : brel_symmetric A eqA)
    (trnA : brel_transitive A eqA).

  Fixpoint no_dup (l : list A) : bool :=
    match l with
    | [] => true
    | h :: t => negb (in_list eqA t h) &&
        no_dup t
    end.

  Fixpoint list_equality (l₁ l₂ : list A) : bool := 
    match l₁ with 
    | [] => match l₂ with 
      | [] => true
      | _ => false
      end
    | h₁ :: t₁ => match l₂ with
      | [] => false 
      | h₂ :: t₂ => (eqA h₁ h₂) && (list_equality t₁ t₂) 
      end
    end.   

  Lemma list_equality_refl : forall l : list A, list_equality l l = true.
  Proof.
    induction l.
    + simpl; reflexivity.
    + simpl. apply Bool.andb_true_iff.
      split. apply refA. apply IHl.
  Qed.
  
  Lemma list_mem_not : forall (l : list A) (c a : A), eqA c a = true ->
    in_list eqA l a = false -> in_list eqA l c = false.
  Proof.
    induction l; simpl; intros ? ? Heq Hf.
    + reflexivity.
    + apply Bool.orb_false_iff in Hf.
      destruct Hf as [Hfa Hfb].
      apply Bool.orb_false_iff.
      split. 
      (* from Heq and Hfa, I have the conclusion *)
      admit.
      apply IHl with (a := a0).
      exact Heq. exact Hfb.
  Admitted.

  Lemma list_mem_true_false : forall (l : list A) (a c : A),
    in_list eqA l a = false -> in_list eqA l c = true -> eqA c a = false.
  Proof.
    induction l; simpl; intros ? ? Ha Hb.
    + inversion Hb.
    + apply Bool.orb_false_iff in Ha.
      apply Bool.orb_true_iff in Hb.
      destruct Ha as [Ha1 Ha2].
      destruct Hb as [Hb | Hb].
      apply symA in Hb.
      (* eqA a0 a = false /\ eqA a c = true -> eqA a0 c = false *)
      admit.
      apply IHl; assumption.
  Admitted. 

  Lemma list_split : forall (l : list A) (c : A),
    l <> [] -> in_list eqA l c = true -> 
    no_dup l = true -> exists l₁ l₂ : list A, 
    list_equality l (l₁ ++ [c] ++ l₂) = true /\ 
    in_list eqA l₁ c = false /\ 
    in_list eqA l₂ c = false.
  Proof.
    induction l; simpl.
    + intros ? H₁ H₂ H₃.
      inversion H₂.
    + intros c H₁ H₂ H₃.
      apply Bool.andb_true_iff in H₃.
      destruct H₃ as [Hl₃ Hr₃].
      apply Bool.orb_true_iff in H₂.
      destruct H₂ as [H₂ | H₂].
      exists [], l; simpl; subst.
      apply Bool.negb_true_iff in Hl₃.
      split. apply Bool.andb_true_iff.
      split. apply symA. apply H₂.
      apply list_equality_refl.
      split. auto.
      apply list_mem_not with (a := a).
      exact H₂. exact Hl₃.
      (* l = [] \/ l <> []*)
      destruct l as [|b l].
      - inversion H₂.
      - assert (Ht : b :: l <> []).
        intro Hf. inversion Hf.
        destruct (IHl c Ht H₂ Hr₃) as 
         [la [lb [Ha [Hb Hc]]]].
        exists (a :: la), lb.
        assert (Hlf : (a :: la) ++ c :: lb = a :: la ++ c :: lb).
        simpl. reflexivity.
        rewrite Hlf. clear Hlf.
        apply Bool.negb_true_iff in Hl₃.
        split. apply Bool.andb_true_iff.
        split. apply refA.
        exact Ha.
        split. simpl.
        apply Bool.orb_false_iff.
        split. apply list_mem_true_false with (l := b :: l).
        exact Hl₃. exact H₂.
        exact Hb. exact Hc.
  Qed.
        
    
End Lfn.



Section Matrix.
  Variables 
    (Node : Type)
    (finN : finite_set Node)
    (eqN  : brel Node)
    (refN : brel_reflexive Node eqN)
    (symN : brel_symmetric Node eqN)
    (trnN : brel_transitive Node eqN)
    (memN : forall x : Node, in_list eqN finN x = true)

    (* carrier set and the operators *)
    (R : Type)
    (zeroR oneR : R) (* 0 and 1 *)
    (plusR mulR : binary_op R)

    (* equivalence relation on R *)
    (eqR  : brel R)
    (refR : brel_reflexive R eqR)
    (symR : brel_symmetric R eqR)
    (trnR : brel_transitive R eqR)
    (* end of equivalence relation *)

    (* Semiring Axiom on R *)
    (zero_left_identity_plus  : forall r : R, eqR (plusR zeroR r) r = true)
    (zero_right_identity_plus : forall r : R, eqR (plusR r zeroR) r = true)
    (plus_associative : forall a b c : R, eqR (plusR a (plusR b c)) 
      (plusR (plusR a b) c) = true)
    (plus_commutative  : forall a b : R, eqR (plusR a b) (plusR b a) = true)
    (one_left_identity_mul  : forall r : R, eqR (mulR oneR r) r = true)
    (one_right_identity_mul : forall r : R, eqR (mulR r oneR) r = true)
    (mul_associative : forall a b c : R, eqR (mulR a (mulR b c)) 
      (mulR (mulR a b) c) = true)
    (left_distributive_mul_over_plus : forall a b c : R, eqR (mulR a (plusR b c)) 
      (plusR (mulR a b) (mulR a c)) = true)
    (right_distributive_mul_over_plus : forall a b c : R, eqR (mulR (plusR a b) c) 
      (plusR (mulR a c) (mulR b c)) = true)
    (zero_left_anhilator_mul  : forall a : R, eqR (mulR zeroR a) zeroR = true)
    (zero_right_anhilator_mul : forall a : R, eqR (mulR a zeroR) zeroR = true)
    (* end of axioms *)

    (* start of congruence relation *)
    (congrP : bop_congruence R eqR plusR)
    (congrM : bop_congruence R eqR mulR)
    (congrR : brel_congruence R eqR eqR).
    (* end of congruence *)
    

    Declare Scope Mat_scope.
    Delimit Scope Mat_scope with R.
    Bind Scope Mat_scope with R.
    Local Open Scope Mat_scope.
  

    Local Notation "0" := zeroR : Mat_scope.
    Local Notation "1" := oneR : Mat_scope.
    Local Infix "+" := plusR : Mat_scope.
    Local Infix "*" := mulR : Mat_scope.
    Local Infix "=r=" := eqR (at level 70) : Mat_scope.
    Local Infix "=n=" := eqN (at level 70) : Mat_scope.

    
    (* (square) matrix is a function. It's easy to prove various 
      properties of matrix with this representation. However, 
      it's not very efficient, at least in my experience, 
      so later we will replace it by another similar more 
      efficient structure for computation *) 
    
    Definition Matrix : Type := Node -> Node -> R.


    (* returns the cth row of m *)
    Definition get_row (m : Matrix) (c : Node) : Node -> R := 
      fun d => m c d.

    (* returns the cth column of m *)
    Definition get_col (m : Matrix) (c : Node) : Node -> R :=
      fun d => m d c.

    (* zero matrix, additive identity of plus *)
    Definition zero_matrix : Node -> Node -> R := 
      fun _ _ => 0.
    


    (* identity matrix, mulitplicative identity of mul *)
    (* Idenitity Matrix *)
    Definition I : Matrix := fun (c d : Node) =>
      match c =n= d with 
      | true => 1
      | false => 0 
      end.
    
    
    (* transpose the matrix m *)
    Definition transpose (m : Matrix) : Matrix := 
      fun (c d : Node) => m d c.

    Definition transpose_transpose_id : ∀ (m : Matrix) (c d : Node), 
      (((transpose (transpose m)) c d) =r= (m c d)) = true.
    Proof. 
      intros ? ? ?; unfold transpose; 
      simpl. 
      apply refR.
    Defined.

    (* pointwise addition to two matrices *)
    Definition matrix_add (m₁ m₂ : Matrix) : Matrix :=
      fun c d => (m₁ c d + m₂ c d).


    Lemma zero_add_left : forall c d m, 
      eqR (matrix_add zero_matrix m c d) (m c d) = true.
    Proof.
      intros c d m.
      unfold matrix_add, zero_matrix.
      rewrite zero_left_identity_plus.
      exact eq_refl.
    Qed. 

    Lemma zero_add_right : forall c d m, 
      eqR (matrix_add m zero_matrix c d) (m c d) = true.
    Proof.
      intros c d m.
      unfold matrix_add, zero_matrix.
      rewrite zero_right_identity_plus.
      exact eq_refl.
    Qed. 

    Lemma matrix_add_assoc : forall m₁ m₂ m₃ c d, 
      matrix_add m₁ (matrix_add m₂ m₃) c d =r= 
      matrix_add (matrix_add m₁ m₂) m₃ c d = true.
    Proof.
      unfold matrix_add; intros.
      rewrite plus_associative;
      exact eq_refl.
    Qed.

    
    Lemma matrix_add_comm : forall m₁ m₂ c d, 
      matrix_add m₁ m₂ c d =r= matrix_add m₂ m₁ c d = true.
    Proof.
      intros; unfold matrix_add.
      rewrite plus_commutative.
      reflexivity.
    Qed.


    Fixpoint sum_fn (f : Node -> R) (l : list Node) : R :=
      match l with 
      | [] => 0
      | h :: t => f h + sum_fn f t
      end.

    Lemma sum_with_two_var : forall fn ga u v, 
      fn =r= u + v= true -> ga + fn =r= u + (ga + v) = true.
    Proof.
      intros.
      unfold bop_congruence in congrP.
      assert (Ht: ga + fn =r= ga + (u + v) = true).
      apply congrP; [apply refR | exact H].
      rewrite <-Ht; clear Ht.
      apply congrR. apply refR.
      assert (Ht : u + (ga + v) =r= u + (v + ga) = true).
      apply congrP. apply refR.
      apply plus_commutative.
      rewrite <-Ht; clear Ht.
      apply congrR. apply refR.
      assert (Ht : (u + v) + ga =r= u + (v + ga) = true).
      apply symR, plus_associative.
      rewrite <-Ht. apply congrR.
      apply plus_commutative. 
      apply refR.
    Qed.


    Lemma sum_first_congr : forall fa ga u v fn, 
      fn =r= u + v = true -> 
      fa + ga + fn =r= fa + u + (ga + v) = true.
    Proof.
      intros.
      pose proof (congrP fa (ga + fn) fa (u + (ga + v)) (refR fa)
        (sum_with_two_var _ _ _ _ H)) as Href.
      rewrite <-Href.
      apply congrR, symR, plus_associative.
      apply symR, plus_associative.
    Qed.
  
    
    Lemma sum_fn_congr : forall (f g : Node -> R) (a : Node) (l : list Node),
      (sum_fn (λ x : Node, f x + g x) l =r= sum_fn f l + sum_fn g l) = true ->
      (f a + g a + sum_fn (λ x : Node, f x + g x) l =r= 
      f a + sum_fn f l + (g a + sum_fn g l)) = true.
    Proof.
      intros. 
      apply sum_first_congr.
      exact H.
    Qed.
  

    Lemma sum_fn_add : forall (f g : Node -> R) (l : list Node), 
      (sum_fn (fun x => f x + g x) l) =r= (sum_fn f l +  sum_fn g l) = true.
    Proof.
      intros ? ?.
      induction l; simpl.
      + apply symR, zero_left_identity_plus.
      + apply sum_fn_congr. exact IHl.
    Qed.

    Lemma mul_gen_left_distr : forall c fa fn gn, 
      fn =r= c * gn = true -> c * fa + fn =r= c * (fa + gn) = true.
    Proof.
      intros.
      assert (Ht : c * fa + fn =r= c * fa + c * gn = true).
      apply congrP. apply refR. exact H.
      rewrite <-Ht; clear Ht.
      apply congrR. apply refR.
      assert (Ht : c * (fa + gn) =r= c * fa + c * gn = true).
      apply left_distributive_mul_over_plus.
      rewrite <-Ht; clear Ht.
      apply congrR. apply refR.
      apply congrP; apply refR.
    Qed.
    


    Lemma mul_constant_left : forall (f : Node -> R) (c : R) (l : list Node), 
      sum_fn (fun x => c * f x) l =r= (c * sum_fn f l) = true.
    Proof.
      intros ? ?. 
      induction l; simpl.
      + apply symR,
        zero_right_anhilator_mul.
      + apply mul_gen_left_distr; exact IHl.
    Qed.



    Lemma mul_gen_right_distr : forall c fa fn gn, 
      fn =r= gn * c = true -> fa * c + fn =r= (fa + gn) * c = true.
    Proof.
      intros.
      assert (Ht : fa * c + fn =r= fa * c + gn * c = true).
      apply congrP. apply refR. exact H.
      rewrite <-Ht; clear Ht.
      apply congrR. apply refR.
      assert (Ht : (fa + gn) * c =r= fa * c + gn * c = true).
      apply right_distributive_mul_over_plus.
      rewrite <-Ht; clear Ht.
      apply congrR. apply refR.
      apply congrP; apply refR.
    Qed.


    Lemma mul_constant_right : forall (f : Node -> R) (c : R) (l : list Node), 
      sum_fn (fun x => (f x * c)) l =r= (sum_fn f l * c) = true.
    Proof.
      intros ? ?.
      induction l; simpl.
      + apply symR, zero_left_anhilator_mul.
      + apply mul_gen_right_distr; exact IHl.
    Qed.



    (* generalised matrix multiplication *)
    Definition matrix_mul_gen (m₁ m₂ : Matrix) (l : list Node) : Matrix :=
      fun (c d : Node) => sum_fn (fun y => (m₁ c y * m₂ y d)) l.



    Lemma push_mul_right_gen : forall a b c d fn gn, 
      fn =r= gn = true -> 
      (a * b + c) * d + fn =r= a * b * d + c * d + gn = true.
    Proof.
      intros. apply congrP.
      apply right_distributive_mul_over_plus.
      exact H.
    Qed.

    (* This need right distributive (a + b) * c = a * c + b * c*)  
    Lemma push_mul_right_sum_fn : forall (l₂ l₁ : list Node) 
      (m₁ m₂ m₃ : Matrix) a x x0,
      sum_fn (λ y : Node,
        ((m₁ x a * m₂ a y + 
          sum_fn (λ y0 : Node, m₁ x y0 * m₂ y0 y) l₁) * m₃ y x0)) l₂ =r= 
      sum_fn (λ y : Node, 
        (m₁ x a * m₂ a y * m₃ y x0 + 
          sum_fn (λ y0 : Node, m₁ x y0 * m₂ y0 y) l₁ * m₃ y x0)) l₂ = true.
    Proof.
      intros.
      revert l₁ m₁ m₂ m₃ a x x0.
      induction l₂; simpl; intros ? ? ? ? ? ? ?.
      + apply refR.
      + apply push_mul_right_gen, IHl₂.
    Qed.
      

    Local Lemma rewrite_gen_ind : forall a b c d e f g, 
      a * d + f =r= g = true -> 
      a * (b * c + d) + (e * c + f) =r= 
      (a * b + e) * c + g = true.
    Proof.
      intros.
      assert (Ht : a * (b * c + d) + (e * c + f) =r= 
        a * b * c + a * d + (e * c + f) = true).
      apply congrP.
      assert (Hw : a * b * c + a * d =r= a * (b * c) + a * d = true).
      apply congrP. apply symR. apply mul_associative.
      apply refR. apply symR.
      rewrite <-Hw; clear Hw. 
      apply congrR. apply refR.
      apply left_distributive_mul_over_plus.
      apply refR.
      rewrite <-Ht; clear Ht. 
      apply congrR. 
      apply refR. apply symR.
      assert (Ht : a * b * c + a * d + (e * c + f) =r= 
        a * b * c + (a * d + (e * c + f)) = true).
      apply symR. apply plus_associative.
      rewrite <-Ht; clear Ht. 
      apply congrR.
      apply refR. 
      apply symR.
      assert (Ht : a * b * c + (a * d + (e * c + f)) =r= 
        a * b * c + (e * c + a * d + f) = true).
      apply congrP. apply refR.
      assert (Hw : a * d + (e * c + f) =r= 
        a * d + e * c + f = true).
      apply plus_associative.
      rewrite <- Hw; clear Hw.
      apply congrR. apply refR.
      apply congrP. 
      apply plus_commutative.
      apply refR. 
      rewrite <- Ht; clear Ht.
      apply congrR.
      apply refR. apply symR.
      assert (Ht : (a * b + e) * c + g =r= 
        a * b * c + e * c + g = true).
      apply congrP.
      apply right_distributive_mul_over_plus.
      apply refR. apply symR in Ht.
      rewrite <-Ht; clear Ht.
      apply congrR. 
      assert (Ht : a * b * c + e * c + g =r= 
        a * b * c + (e * c + g) = true).
      apply symR.
      apply plus_associative. 
      apply symR in Ht.
      rewrite <- Ht; clear Ht.
      apply congrR. apply congrP.
      apply refR.
      assert (Ht : e * c + g =r= e * c + (a * d + f) = true).
      apply congrP. apply refR.
      apply symR. exact H.
      apply symR in Ht.
      rewrite <-Ht; clear Ht.
      apply congrR. apply symR.
      apply plus_associative.
      all: apply refR.
    Qed.


    Lemma matrix_mul_gen_assoc : forall l₁ l₂ m₁ m₂ m₃ (c d : Node),
      (matrix_mul_gen m₁ (matrix_mul_gen m₂ m₃ l₂) l₁ c d) =r= 
      (matrix_mul_gen (matrix_mul_gen m₁ m₂ l₁) m₃ l₂ c d) = true.
    Proof.
      intros.
        revert l₁ l₂ m₁ m₂ m₃ c d.
      unfold matrix_mul_gen; induction l₁; simpl;
      intros ? ? ? ? ? ?. 
      +
        induction l₂; simpl.
        ++ apply refR.
        ++ apply symR.
          assert (Ht: 0 * m₃ a d + sum_fn (λ y : Node, 0 * m₃ y d) l₂ =r= 
            0 + sum_fn (λ y : Node, 0 * m₃ y d) l₂ = true).
          apply congrP. apply zero_left_anhilator_mul.
          apply refR. rewrite <-Ht; clear Ht.
          apply congrR. apply refR.
          assert (Ht : 0 + sum_fn (λ y : Node, 0 * m₃ y d) l₂ =r=
            sum_fn (λ y : Node, 0 * m₃ y d) l₂ = true).
          apply zero_left_identity_plus. apply symR in Ht.
          rewrite <-Ht. apply congrR.
          exact IHl₂. apply refR.
      (* inductive case *)
      + specialize (IHl₁ l₂ m₁ m₂ m₃ c d).
        (* This one is going to be tricky *)
        assert (Ht: m₁ c a * sum_fn (λ y : Node, m₂ a y * m₃ y d) l₂ +
          sum_fn 
            (λ y : Node, m₁ c y * 
              sum_fn (λ y0 : Node, m₂ y y0 * m₃ y0 d) l₂) l₁ =r=
          m₁ c a * sum_fn (λ y : Node, m₂ a y * m₃ y d) l₂ + 
          sum_fn
            (λ y : Node,
              sum_fn (λ y0 : Node, m₁ c y0 * m₂ y0 y) l₁ * m₃ y d) l₂ = true).
        apply congrP.
        apply refR. exact IHl₁.
        rewrite <-Ht.
        apply congrR. apply refR.
        clear Ht; clear IHl₁.
        apply symR.
        induction l₂; simpl.
        ++ assert (Ht : m₁ c a * 0 + 0 =r= 0 + 0 = true).
          apply congrP. apply zero_right_anhilator_mul.
          apply refR.
          rewrite <-Ht. apply congrR.
          apply refR. apply symR.
          apply zero_left_identity_plus.
        ++ apply rewrite_gen_ind. exact IHl₂.
    Qed.

    
    Lemma sum_fn_list_app : forall (l₁ l₂ : list Node) (f : Node -> R), 
      sum_fn f (l₁ ++ l₂) =r= (sum_fn f l₁ + sum_fn f l₂) = true.
    Proof.
      induction l₁; simpl.
      intros ? ?.
      + apply symR, zero_left_identity_plus.
      + intros ? ?.
        specialize (IHl₁ l₂ f).
        assert (Ht : f a + sum_fn f l₁ + sum_fn f l₂ =r= 
          f a + (sum_fn f l₁ + sum_fn f l₂) = true).
        apply symR, plus_associative.
        apply symR in Ht.
        rewrite <-Ht; clear Ht.
        apply congrR. apply congrP.
        apply refR. exact IHl₁.
        apply refR.
    Qed.
  

    Lemma sum_fn_zero : forall (l₁ l₂ : list Node) (f : Node -> R),
      sum_fn f l₁ =r= 0 = true ->  
      sum_fn f (l₁ ++ l₂) =r= sum_fn f l₂ = true.
    Proof.
      intros ? ? ? Hf.
      assert (sum_fn f (l₁ ++ l₂) =r= sum_fn f l₁ + sum_fn f l₂ = true).
      apply sum_fn_list_app.
      rewrite <-H; clear H.
      apply congrR. apply refR.
      assert (Ht : sum_fn f l₁ + sum_fn f l₂ =r= 0 + sum_fn f l₂ = true).
      apply congrP. exact Hf.
      apply refR. apply symR.
      rewrite <-Ht; clear Ht.
      apply congrR. apply refR.
      apply symR. apply zero_left_identity_plus.
    Qed.


    (* for this proof, I need l to be finite, non-empty, 
      but more importantly, non-duplicate. 
    *)
    
    Lemma sum_fn_list_eqv : forall (l la lb : list Node) 
      (c : Node) (f : Node -> R), 
      list_equality Node eqN l (la ++ [c] ++ lb) = true ->
      sum_fn f l =r= sum_fn f (la ++ [c] ++ lb) = true.
    Proof.

    Admitted.

    Lemma sum_fn_not_mem : forall (l : list Node) (c d : Node) 
      (m : Node -> Node -> R), in_list eqN l c = false ->
      sum_fn (λ y : Node, (if c =n= y then 1 else 0) * m y d) l =r= 
      0 = true.
    Proof.
      induction l; simpl; intros c d m H.
      + apply refR.
      + apply Bool.orb_false_iff in H.
        destruct H as [Ha Hb]. 
        rewrite Ha.
        specialize (IHl c d m Hb).
        assert (Ht : 0 * m a d + 
          sum_fn (λ y : Node, (if c =n= y then 1 else 0) * m y d) l =r= 
          0 + sum_fn (λ y : Node, (if c =n= y then 1 else 0) * m y d) l 
          = true).
        apply congrP. apply zero_left_anhilator_mul.
        apply refR. rewrite <-Ht; clear Ht.
        apply congrR. apply refR.
        apply symR. 
        rewrite <-IHl. apply congrR.
        apply zero_left_identity_plus.
        apply refR.
    Qed.
        
    Lemma matrix_mul_left_identity : forall (l : list Node),
      l <> [] -> (∀ x : Node, in_list eqN l x = true) -> 
      no_dup Node eqN l = true -> forall (m : Matrix) (c d : Node),
      matrix_mul_gen I m l c d =r= m c d = true.
    Proof.
      unfold matrix_mul_gen, I.
      intros ? Hl Hx Hn ? ? ?.
      destruct (list_split _ eqN refN symN trnN l c Hl (Hx c) 
        Hn) as [la [lb [Hleq [Hina Hinb]]]].
      eapply sum_fn_not_mem.
      (* I need to replace l by la ++ [c] ++ lb *)




    Definition matrix_mul (m₁ m₂ : Matrix) := 
      matrix_mul_gen m₁ m₂ finN.

    
    Lemma matrix_mul_assoc : forall m₁ m₂ m₃ (c d : Node),
      matrix_mul m₁ (matrix_mul m₂ m₃) c d =r= 
      matrix_mul (matrix_mul m₁ m₂) m₃ c d = true.
    Proof.
      unfold matrix_mul.
      apply matrix_mul_gen_assoc.
    Qed.



    (* Now I need Matrix exponentiation *)
    (* write a slow one, nat, and fast one, Binary nat and 
      prove that they are equal. 
      For nat, 
      proofs will be easy, but slow computation. For Binary nat, 
      proofs be difficult but computation will be fast. 

      Then show that 0-stable, then it reaches a fixpoint
      *)
    Fixpoint matrix_exp_unary (m : Matrix) (n : nat) : Matrix :=
      match n with 
      | 0%nat => I 
      | S n' => matrix_mul m (matrix_exp_unary m n')
      end.
    
      
    Fixpoint repeat_op_ntimes_rec (e : Matrix) (n : positive) : Matrix :=
      match n with
      | xH => e
      | xO p => let ret := repeat_op_ntimes_rec e p in matrix_mul ret ret
      | xI p => let ret := repeat_op_ntimes_rec e p in matrix_mul e (matrix_mul ret ret)
      end.

    Definition matrix_exp_binary (e : Matrix) (n : N) :=
      match n with
      | N0 => I
      | Npos p => repeat_op_ntimes_rec e p 
      end.

    
    (* now prove that slow and fast computes the same value. *)

    Lemma binnat_zero : forall (n : nat), 0%N = N.of_nat n -> n = 0%nat.
    Proof.
      induction n; try lia.
    Qed.

  
    Lemma binnat_odd : forall (p : positive) (n : nat), N.pos (xI p) = N.of_nat n -> 
      exists k,  n = (2 * k + 1)%nat /\  (N.pos p) = (N.of_nat k).
    Proof.
      intros p n Hp.
      destruct (Even.even_or_odd n) as [H | H].
      apply Even.even_equiv in H. destruct H as [k Hk].
      (* Even (impossible) Case *)
      rewrite Hk in Hp; lia.
      (* Odd (possible) case *)
      apply Even.odd_equiv in H. destruct H as [k Hk].
      rewrite Hk in Hp. exists k.
      split. exact Hk. lia.
    Qed.



    Lemma binnat_even : forall (p : positive) (n : nat), N.pos (xO p) = N.of_nat n :> N -> 
      exists k, n = (Nat.mul 2 k) /\  (N.pos p) = (N.of_nat k).
    Proof.
      intros p n Hp.
      destruct (Even.even_or_odd n) as [H | H].
      apply Even.even_equiv in H. destruct H as [k Hk].
      (* Even (possible) case*)
      rewrite Hk in Hp. exists k.
      split. exact Hk. lia.
      (* Odd (impossible) case *)
      apply Even.odd_equiv in H. 
      destruct H as [k Hk].
      rewrite Hk in Hp. lia.
    Qed. 

    (* 
    Lemma push_out_e_unary_nat_gen : forall k1 k2 e c d , matrix_exp e (k1 + k2)  c d = 
      matrix_mul (matrix_exp e k1)  (matrix_exp e k2) c d.
    Proof.
      induction k1.
      + intros ? ?; simpl. 
        (* requires I * m = m *)
        admit.
      + admit.
    Admitted. *)









    
    




