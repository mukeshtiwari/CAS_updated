(***********************************************************************)
(* This file contains a formalization of the central result of         *)
(*                                                                     *)
(*    Routing in Equilibrium.                                          *)
(*    João Luís Sobrinho and Timothy G. Griffin.                       *)
(*    19th International Symposium on Mathematical                     *)
(*    Theory of Networks and Systems (MTNS 2010).                      *)
(*    http://www.cl.cam.ac.uk/~tgg22/publications/routing_in_equilibrium_mtns_2010.pdf *) 
(*                                                                     *)
(*    The main idea is to show that Dijkstra's Algorithm can be        *)
(*    generalized to algebraic structures where distributivity         *)
(*    does not hold.                                                   *)
(*                                                                     *) 
(*    First, some notation. This file works with an algebraic          *)
(*    structure of the form (S, L, +, <|), where + is a selective,     *)
(*    commutative, semigroup.  The "multiplicative" operation <|       *)
(*    has type                                                         *)
(*                   <| : S -> L -> S                                  *)
(*    which will be written as an infix operation, s <| l.  Here       *) 
(*    L is the type of link labels and S is the type of path weights.  *)
(*    Distributivity for such an algebra is the property               *)
(*               (a + b) <| l = (a <| l) + (b <| l).              (1)  *) 
(*                                                                     *)
(*    Without distributivity, we do not get the best path              *)
(*    weights over all possible paths, but rather we get one           *)
(*    row of a solution to this "right" matrix equation:               *)
(*                                                                     *) 
(*            R = R <| A + I.                                          *)
(*                                                                     *) 
(*    Here, A the n-by-n adjacency matrix and I is the multiplicative  *)
(*    identity matrix. The R <| A represents the matrix over S:        *) 
(*                                                                     *) 
(*          R[i,j] = (D <| A)[i,j] + I[i, j]                           *) 
(*                 = (sum_q D[i,q] <| A[q,j]) + I[i, j].               *) 
(*                                                                     *) 
(*    For dijkstra's algorithm, we start at some node i (0<=i<n) and   *) 
(*    (D i) is the row ith row of such a solution. Let (v i) be the    *) 
(*    n-vector with (v i)[i] = one, (v i)[j] = zero for j <> i.        *)
(*    Then specializing (1) to the i-th row we have                    *) 
(*                                                                     *) 
(*              (D i)[j] = ((D i) <| A)[j] + (v i)[j]                  *) 
(*                       = (sum_q (D i)[q] <| A[q,j]) + (v i)[j]       *)
(*                                                                     *)
(*    Note that 0 < n, and i in [0, 1, ..., n-1].                      *)
(*                                                                     *)
(* TODO : a) extend results to the "classic" case where (1) holds and  *)
(*           to the case where L = S and <| is a                       *) 
(*           semigroup and left- and right-distributivity hold.        *)
(*        b) extend to case of the paper                               *)
(*             On the Forwarding Paths Produced by Internet            *) 
(*             Routing Algorithms.                                     *) 
(*             Seweryn Dynerowicz, Timothy G. Griffin. ICNP 2013.      *) 
(*                                                                     *)
(*    --- tim griffin, March 2023                                      *) 
(***********************************************************************)

Require Import
  List
  Coq.Init.Datatypes.

Import ListNotations. 

From CAS Require Import
  coq.common.compute
  coq.theory.arithmetic 
  coq.eqv.properties
  coq.eqv.nat
  coq.eqv.list
  coq.eqv.product  
  coq.or.properties
  coq.or.from_sg
  coq.rtr.properties
  coq.sg.properties
  coq.sg.theory
  coq.or_sg.properties (* for bop_is_glb *)   
  coq.or_sg.theory     (* for bop_is_glb_wrt_lte_left *)
  coq.sg_rtr.properties 
  coq.sg.min
  coq.sg.or
  coq.sg.and
  coq.algorithms.big_plus
  coq.algorithms.matrix_definition     (* just for list_enum? *) 
  coq.algorithms.matrix_algorithms     (* just for def of big_plus ? *)   
  coq.algorithms.bs_matrix_multiplication (* just for def of I ? *)
  .
  
Section Computation.
  Open Scope nat_scope.   
  
  Definition Node := nat.
  
  Variables 
    (S : Type)
    (L : Type)
    (eqS : brel S)
    (eqL : brel L)       
    (zero one : S)
    (plus : binary_op S) 
    (rtr : rtr_type L S). (* S → L → S *) 
    
  Local Infix "⊕" := plus (at level 70). 
  Local Infix "<|" := rtr (at level 70). 

  
  Fixpoint find_min_node 
    (p : S * Node)
    (carry : list (S * Node))
    (l : list (S * Node)) : (S * Node) * list (S * Node) :=
    match p with
    | (w, q) => 
      match l with 
      | [] => (p, carry)
      | (w', q') :: l' => 
        if brel_lte_left eqS plus w w' 
        then find_min_node (w, q) ((w', q') :: carry) l' 
        else find_min_node (w', q') ((w, q) :: carry) l' 
      end
    end.

  (* the state of a dijkstra computation *) 
  Record state := 
    {
      visited     : list (S * Node); 
      estimated   : list (S * Node)
    }.
  
  Definition relax_edge
    (m : Node -> Node -> L)              
    (p1 : S * Node)
    (p2 : S * Node) : (S * Node) :=             
    match p1, p2 with 
    | (w1, q1), (w2, q2) => (w2 ⊕ (w1 <| (m q1 q2)), q2)
    end.
  
  Definition relax_edges
    (m : Node -> Node -> L)              
    (p : S * Node) : list (S * Node) -> list (S * Node) :=
    List.map (relax_edge m p). 


  (* one iteration of Dijkstra. *)
  Definition dijkstra_one_step
             (m : Node -> Node -> L) 
             (s : state) : state :=
    match estimated s with 
    | nil => s 
    | h :: tl =>
      let (p, est) := find_min_node h [] tl in 
      {|
          visited   := p:: (visited s)
        ; estimated := relax_edges m p est
      |}
    end.

  (* move this ? *) 
  Fixpoint list_remove {U : Type} (eqU : brel U) (e : U) (l : list U) :=
    match l with
    | [] => l
    | h :: tl => if eqU e h then tl else h :: (list_remove eqU e tl)
    end.

(* list of [n-1, n-2, ..., 0] without i *) 
Fixpoint nodes_0_to_finish_without_i (n i : nat) : list nat :=
  match n with
  | 0 => []
  | Datatypes.S n' =>
    if brel_eq_nat i n' 
    then list_enum n'
    else n' :: nodes_0_to_finish_without_i n' i
  end.

(*
Compute (nodes_0_to_finish_without_i 10 7).

     = [9; 8; 6; 5; 4; 3; 2; 1; 0]
     : list nat
*) 

  Definition nat_pred (n : nat) :=
    match n with
    | 0 => 0
    | (Datatypes.S n') => n'
    end. 

  Definition initial_state
             (m : Node -> Node -> L)
             (n : nat)              
             (i : Node) : state :=
    {|
        visited   := [(one, i)] 
      ; estimated := List.map (λ j, (one <| (m i j), j))
                              (nodes_0_to_finish_without_i n i) 
    |}.


  Fixpoint dijkstra_k_steps 
             (m : Node -> Node -> L)
             (n : nat)              
             (i : Node)
             (k : nat) : state :=
    match k with
    | 0                => initial_state m n i
    | (Datatypes.S k') => dijkstra_one_step m (dijkstra_k_steps m n i k') 
    end .


    Definition dijkstra_raw
             (m : Node -> Node -> L)
             (n : nat)
             (i : Node) : state := 
      dijkstra_k_steps m n i (nat_pred n). 

  Definition visited_to_map (g : Node -> S) (l : list (S * Node)) : Node -> S := 
    List.fold_left (λ f '(v, q) x, if brel_eq_nat x q then v else f x) l g.

  Definition dijkstra
             (m : Node -> Node -> L)
             (n : nat)
             (i : Node) : Node -> S := 
    visited_to_map (λ x, zero) (visited (dijkstra_raw m n i)).
  Close Scope nat_scope.     
End Computation. 
  


Section Preliminary.
  (* Facts about functions list_enum and nodes_0_to_finish_without_i. 
     The proofs need to do induction on n.  
     Since in the next section n is global variable, 
     such proofs are in this preliminary section. 
   *)
  Open Scope nat_scope.  

  Lemma  in_list_enum_intro :
    ∀ n u,  Nat.ltb 0 n = true ->             
             Nat.ltb u n = true ->           
             in_list brel_eq_nat (list_enum n) u = true.   
  Proof. induction n; intros u A B. 
         - compute in A. discriminate A. 
         - simpl.
           apply bop_or_intro.
           + case_eq(brel_eq_nat u n); intro C; auto.
             right. apply IHn.
             * destruct n.
               -- apply ltb_n_1_l in B.
                  rewrite B in C.
                  discriminate C. 
               -- reflexivity. 
             * apply ltb_S_not_eqb ; auto. 
  Qed. 

    Lemma  in_list_enum_elim :
    ∀ n u, in_list brel_eq_nat (list_enum n) u = true -> Nat.ltb u n = true. 
  Proof. induction n; intros u A.
         - compute in A. discriminate A. 
         - simpl in A.
           apply bop_or_elim in A.
           destruct A as [A | A]. 
           + apply eq_lt_n_Sm;auto. 
           + apply IHn in A.
             apply ltb_ltb_succ_r; auto. 
  Qed.

  Lemma zero_in_list_enum : ∀ n, Nat.ltb 0 n = true ->  in_list brel_eq_nat (list_enum n) 0%nat = true. 
  Proof. induction n; intro A.
         - compute in A. discriminate A. 
         - simpl. destruct n.
           + reflexivity.
           + simpl. apply IHn.
             compute. reflexivity.
  Qed.
  
  Lemma  in_nodes_0_to_finish_without_i_elim :
   ∀ n u i, in_list brel_eq_nat (nodes_0_to_finish_without_i n i) u = true -> brel_eq_nat u i = false. 
  Proof. induction n; intros u i A.
         - compute in A. discriminate A. 
         - simpl in A.
           case_eq(brel_eq_nat i n); intro B; rewrite B in A.
           + apply in_list_enum_elim in A.
             case_eq(brel_eq_nat u i); intro C; auto.
             assert (D := brel_eq_nat_transitive _ _ _ C B).
             apply ltb_not_eqb in A.
             rewrite D in A. exact A. 
           + simpl in A.
             apply bop_or_elim in A.
             destruct A as [A | A].
             * case_eq(brel_eq_nat u i); intro C; auto.
               apply brel_eq_nat_symmetric in C.
               rewrite (brel_eq_nat_transitive _ _ _ C A) in B.
               exact B. 
             * apply IHn; auto. 
  Qed. 

  Lemma  in_nodes_0_to_finish_without_i_elim_v2 :
   ∀ n u i, in_list brel_eq_nat (nodes_0_to_finish_without_i n i) u = true -> Nat.ltb u n = true. 
  Proof. induction n; intros u i A.
         - compute in A. discriminate A. 
         - simpl in A.
           case_eq(brel_eq_nat i n); intro B; rewrite B in A.
           + apply in_list_enum_elim in A. 
             apply ltb_ltb_succ_r; auto. 
           + simpl in A.
             apply bop_or_elim in A.
             destruct A as [A | A].
             * case_eq(brel_eq_nat u i); intro C. 
               -- apply brel_eq_nat_symmetric in C.
                  rewrite (brel_eq_nat_transitive _ _ _ C A) in B.
                  discriminate B. 
               -- apply eq_lt_n_Sm; auto. 
             * assert (C := IHn _ _ A). 
               apply ltb_ltb_succ_r; auto. 
  Qed. 
  
 Lemma in_nodes_0_to_finish_without_i_intro :
   ∀ n u i, Nat.ltb 0 n = true ->
             Nat.ltb u n = true ->
             brel_eq_nat u i = false ->
             in_list brel_eq_nat (nodes_0_to_finish_without_i n i) u = true. 
 Proof. induction n; intros u i Z A B.
        - compute in A. discriminate A. 
        - simpl.
          case_eq(brel_eq_nat i n); intro C.
          + apply in_list_enum_intro; auto. 
            * apply ltb_S_not_eqb; auto.
              case_eq(brel_eq_nat 0 n); intro D; auto.
              apply eqb_to_eq in D.
              apply eqb_to_eq in C.
              rewrite <- D in A.
              apply ltb_n_1_l in A.
              apply eqb_to_eq in A.
              rewrite A, C in B.
              rewrite <- D in B.
              compute in B. discriminate B. 
            * apply eqb_to_eq in C.
              rewrite C in B.
              apply ltb_S_not_eqb; auto. 
          + simpl.
            apply bop_or_intro.
            case_eq(brel_eq_nat u n); intro D; auto.
            right.
            apply IHn; auto.
            * apply ltb_S_not_eqb; auto.
              case_eq(brel_eq_nat 0 n); intro E; auto.
              apply eqb_to_eq in E.
              rewrite <- E in A. 
              apply ltb_n_1_l in A.
              apply eqb_to_eq in A.
              rewrite <- E in D.
              rewrite A in D.
              compute in D.
              discriminate D.
            * apply ltb_S_not_eqb; auto. 
 Qed.

 Close Scope nat_scope.
 
 Fixpoint nodes_all_unique l :=
    match l with 
      [] => True
    | q :: tl => (∀ q', in_list brel_eq_nat tl q' = true -> brel_eq_nat q' q = false)
                 *
                 (nodes_all_unique tl) 
    end.

     Lemma list_enum_is_0_to_n_minus_1 :
     ∀ n q, 
       in_list brel_eq_nat (list_enum n) q = true
       -> Nat.ltb q n = true.
     Proof. induction n; simpl; intros q A. 
            - discriminate A.
            - case_eq(brel_eq_nat q n); intro B.
              + apply eq_lt_n_Sm; auto. 
              + rewrite B in A. simpl in A.
                assert (C := IHn _ A).
                apply ltb_ltb_succ_r; auto.
     Qed. 

    Lemma list_enum_out_of_bounds :
     ∀ n q, 
       in_list brel_eq_nat (list_enum n) q = true
       -> brel_eq_nat q n = false. 
    Proof. intros n q A.
           assert (B := list_enum_is_0_to_n_minus_1 _ _ A).
           apply ltb_not_eqb; auto. 
    Qed.     

    Lemma list_enum_unique :
     ∀ n, nodes_all_unique (list_enum n).
   Proof. induction n; simpl. 
          - auto. 
          - split; auto.
            intros q A.
            apply list_enum_out_of_bounds; auto.
   Qed. 

   Lemma nodes_0_to_finish_without_i_limit :
     ∀ n i, in_list brel_eq_nat (nodes_0_to_finish_without_i n i) n = false.
   Proof. induction n; intro i; simpl. 
          - reflexivity.
          - case_eq (brel_eq_nat i n); intro A.
            + case_eq(in_list brel_eq_nat (list_enum n) (Datatypes.S n)); intro B; auto.
              apply list_enum_is_0_to_n_minus_1 in B. 
              rewrite (nltb_succ_diag_l n) in B.
              discriminate B. 
            + case_eq(in_list brel_eq_nat (n :: nodes_0_to_finish_without_i n i) (Datatypes.S n)); intro B; auto.
              simpl in B.
              destruct n.
              * simpl in B. discriminate B.
              * rewrite brel_eq_nat_Su_u in B. unfold orb in B.
                apply in_nodes_0_to_finish_without_i_elim_v2 in B.
                rewrite (nltb_succ_diag_l) in B.
                discriminate B. 
   Qed. 
   
  Lemma nodes_0_to_finish_without_i_unique :
   ∀ n i, nodes_all_unique (nodes_0_to_finish_without_i n i). 
  Proof. induction n; intro i.
         - simpl. auto. 
         - simpl. 
           case_eq(brel_eq_nat i n); intro A. 
           + apply list_enum_unique. 
           + simpl. split.
             * intros q B.
               case_eq(brel_eq_nat q n); intro C; auto.
               apply eqb_to_eq in C. rewrite C in B.
               rewrite (nodes_0_to_finish_without_i_limit n i) in B.
               discriminate B. 
             * apply IHn.
  Qed. 

End Preliminary.  
  
Section Theory. 

  
  Variables 
    (S : Type)
    (L : Type)
    (eqS : brel S)
    (eqL : brel L)       
    (zero one : S)
    (plus : binary_op S) 
    (rtr : rtr_type L S)  (* S → L → S *)

    (conS : brel_congruence S eqS eqS)    
    (refS : brel_reflexive S eqS)
    (symS : brel_symmetric S eqS)
    (trnS : brel_transitive S eqS)

    (refL : brel_reflexive L eqL)    

    (cong  : bop_congruence S eqS plus)
    (assoc : bop_associative S eqS plus)
    (comm  : bop_commutative S eqS plus)
    (sel  :  bop_selective S eqS plus)   
    (zeroId   : bop_is_id S eqS plus zero)
    (oneAnn   : bop_is_ann S eqS plus one)
    (cong_rtr   : A_rtr_congruence eqL eqS rtr)
    (absorb   : A_sg_rtr_absorptive eqS plus rtr)
    (m : Node -> Node -> L)
    (n : nat)
    (i : Node)
    (cong_m : ∀ v v' j j', brel_eq_nat v v' = true -> brel_eq_nat j j' = true -> eqL (m v j) (m v' j') = true)
    (zero_lt_n : Nat.ltb 0 n = true)
    (i_lt_n : Nat.ltb i n = true). 
 
  Local Definition lte a b := brel_lte_left eqS plus a b.
  Local Definition is_lte a b := brel_lte_left eqS plus a b = true.
                
  Local Infix "≦" := is_lte (at level 70).   
  Local Infix "<|" := rtr (at level 70). 
  Local Infix "<?" := Nat.ltb (at level 70).
  Local Infix "⊕" := plus (at level 70). 
  Local Notation "⨁" := (big_plus zero plus) (at level 70).

  Local Definition is_eqS a b := (eqS a b = true).
  Local Infix "=S=" := is_eqS (at level 70).       
  Local Infix "=?S" := eqS (at level 70).


  Local Definition is_eqL a b := eqL a b = true.
  Local Infix "=L=" := is_eqL (at level 70).
  Local Infix "=?L" := eqL (at level 70).  

  Local Definition eqN  := brel_eq_nat.
  Local Definition refN := brel_eq_nat_reflexive.
  Local Definition symN := brel_eq_nat_symmetric.
  Local Definition trnN := brel_eq_nat_transitive.
  Local Definition conN := brel_eq_nat_congruence.  

  Local Definition is_eqN a b := (brel_eq_nat a b = true).
  Local Infix "=N=" := is_eqN (at level 70).
  Local Infix "=?N" := brel_eq_nat (at level 70).

  Local Definition in_list_of_S_Node_pairs := in_list (brel_product eqS brel_eq_nat).

  Local Notation "a ∈ l" := (in_list (brel_product eqS brel_eq_nat) l a = true) (at level 70).
  Local Notation "a ∉ l" := (in_list_of_S_Node_pairs l a = false) (at level 70).

  Local Notation "a ∈' l" := (in_list brel_eq_nat l a = true) (at level 70).  
  
  (* abbreviations of functions *) 
  Local Definition I       := I S zero one.
  Local Definition D1      := dijkstra_one_step S L eqS plus rtr m.
  Local Definition Dk      := dijkstra_k_steps S L eqS one plus rtr m n i.
  Local Definition DR      := dijkstra_raw S L eqS one plus rtr m n i.
  Local Definition D       := dijkstra S L eqS zero one plus rtr m n i.
  
  Local Definition IS      := initial_state S L one rtr m n i.
  Local Notation FindMin := (find_min_node S eqS plus).

  Local Definition eqS_N := (brel_product eqS brel_eq_nat).
  Local Definition is_eqS_N a b := (brel_product eqS brel_eq_nat a b = true).
  Local Infix "=p=" := is_eqS_N (at level 70).
  

  (* some useful lemmas *)
  Lemma m_cong : ∀a b c d, a =N= b → c =N= d → (m a c) =L= (m b d).
  Proof. intros a b c d. unfold is_eqN. unfold brel_eq_nat.
         intros A B. apply beq_nat_to_prop in A, B. 
         rewrite <- A. rewrite B.
         apply refL.
  Qed.
  
  Lemma eqS_N_reflexive : brel_reflexive (S * Node) eqS_N.
  Proof. apply brel_product_reflexive; auto. apply brel_eq_nat_reflexive. Qed.     

  Lemma eqS_N_symmetric : brel_symmetric (S * Node) eqS_N.   
  Proof. apply brel_product_symmetric; auto. apply brel_eq_nat_symmetric. Qed. 


  Lemma lte_ref : ∀ w , w ≦ w. 
  Proof. apply brel_lte_left_reflexive; auto.
         apply bop_selective_implies_idempotent; auto. 
  Qed.

  Lemma lte_total : ∀ w1 w2, (w1 ≦ w2) + (w2 ≦ w1).
  Proof. apply brel_lte_left_total; auto. Qed.
  
  Lemma lte_trn : ∀ w1 w2 w3, w1 ≦ w2 → w2 ≦ w3 → w1 ≦ w3. 
  Proof. apply brel_lte_left_transitive; auto. Qed.

  Lemma one_is_bottom : ∀ w, one ≦ w. 
  Proof. apply brel_lte_left_is_bottom; auto. Qed.

  Lemma zero_is_right_plus_id : ∀x, x ⊕ zero =S= x.
  Proof. intro x. destruct (zeroId x) as [_ B]. exact B. Qed. 

  Lemma plus_idempotent : bop_idempotent S eqS plus.
  Proof. apply bop_selective_implies_idempotent; auto. Qed.
  
  Lemma lte_is_total : ∀ w1 w2, (w1 ≦ w2) + (w2 ≦ w1). 
  Proof. apply brel_lte_left_total; auto. Qed.

  Lemma rtr_is_increasing : ∀ w label, w ≦ (w <| label). 
  Proof. intros w label. apply absorb; auto. Qed.
  
  Lemma lte_congruence : ∀ w1 w2 w3 w4, w1 =S= w2 → w3 =S= w4 → (w1 ≦ w3) = (w2 ≦ w4).
  Proof. unfold is_eqS, is_lte. intros w1 w2 w3 w4 A B.
         rewrite (brel_lte_left_congruence _ eqS conS symS plus cong _ _ _ _ A B).
         reflexivity. 
  Qed.

  Lemma lte_elim_l : ∀ a b,  a ≦ b -> a =S= (a ⊕ b). 
  Proof. intros a b A.
         unfold is_lte in A. unfold brel_lte_left in A.
         exact A. 
  Qed.
  
  Lemma lte_elim_r : ∀ a b,  a ≦ b -> a =S= (b ⊕ a). 
  Proof. intros a b A.
         unfold is_lte in A. unfold brel_lte_left in A.
         exact (trnS _ _ _ A (comm a b)). 
  Qed.
  
  Lemma plus_is_an_upper_bound :∀ a b c, a ≦ b → a ≦ c → a ≦ (b ⊕ c).
  Proof. unfold is_lte. 
         intros a b c A B.
         apply bop_is_glb_wrt_lte_left; auto.
         - apply plus_idempotent.
         - unfold is_lower_bound; auto. 
  Qed.
  
  Lemma I_on_diagonal (j : Node) : i =N= j -> (I i j) =S= one.
  Proof. intro A. unfold I, bs_matrix_multiplication.I, matrix_mul_identity. 
         rewrite A. apply refS. 
  Qed.

  Lemma I_off_diagonal (j : Node) : i =?N j = false -> (I i j) =S= zero.
  Proof. intro A. unfold I, bs_matrix_multiplication.I, matrix_mul_identity. 
         rewrite A. apply refS. 
  Qed.

  Lemma initial_estimate_elim :
    ∀ w j ln, (w, j) ∈ map (λ j : Node, (one <| m i j, j)) ln -> (w =S= (one <| m i j)) * (j ∈' ln).
  Proof. intros w j ln A.
         induction ln.
         - compute in A. discriminate A. 
         - split. 
           + apply in_list_cons_elim in A.
             * destruct A as [A | A].
               apply brel_product_elim in A.
               -- destruct A as [A B].
                  apply symS in A.
                  assert (C := m_cong _ _ _ _ (brel_eq_nat_reflexive i) B).
                  assert (D := cong_rtr _ _ _ _ C (refS one)).
                  exact (trnS _ _ _ A D). 
               -- apply IHln; auto. 
             * apply eqS_N_symmetric.
           + apply in_list_cons_elim in A.
             * destruct A as [A | A].
               apply brel_product_elim in A.
               -- destruct A as [A B].
                  apply in_list_cons_intro; auto.
                  apply symN. 
               -- apply in_list_cons_intro; auto.
                  apply symN.
                  right. apply IHln; auto. 
             * apply eqS_N_symmetric.
  Qed. 
           

  (****************** uniqueness of nodes ********************************************)

 Definition node_not_in_value_node_list q tl := ∀ w' q', (w', q') ∈ tl -> eqN q q' = false. 
   
 Fixpoint pairs_have_nodes_all_unique l :=
    match l with 
      [] => True
    | (w, q) :: tl => (* ∀ w' q', (w', q') ∈ tl -> eqN q q' = false *)
                      (node_not_in_value_node_list q tl)
                      *
                      (pairs_have_nodes_all_unique tl) 
    end.

    Lemma pairs_have_nodes_all_unique_cons_intro :
    ∀ l h j,
      (*∀ (w' : S) (q' : nat), (w', q') ∈ l → eqN j q' = false *)
      node_not_in_value_node_list j l 
       -> pairs_have_nodes_all_unique l  
       -> pairs_have_nodes_all_unique ((h, j) :: l) .
  Proof. intros l h j A B. simpl.  split; auto.   Qed.

  Lemma pairs_have_nodes_all_unique_cons_elim :
    ∀ l h j,
      pairs_have_nodes_all_unique ((h, j) :: l) 
      ->  (*∀ (w' : S) (q' : nat), (w', q') ∈ l → eqN j q' = false*)
          (node_not_in_value_node_list j l)
          *      
          (pairs_have_nodes_all_unique l). 
  Proof. intros l h j [A B]. split; auto. Qed.


  Definition no_shared_nodes_in_value_node_lists l1 l2 := 
    ∀ (w : S) (q : nat), (w, q) ∈ l1 → node_not_in_value_node_list q l2.
  
  Lemma pairs_have_nodes_all_unique_concat_intro :
    ∀ l l',
      (*∀ (w : S) (q : nat),
          (w, q) ∈ l → ∀ (w' : S) (q' : nat), (w', q') ∈ l' → eqN q q' = false *)
      (*∀ (w : S) (q : nat), (w, q) ∈ l → node_not_in_value_node_list q l'*)
      no_shared_nodes_in_value_node_lists l l'
      -> pairs_have_nodes_all_unique l
      -> pairs_have_nodes_all_unique l'                                       
      -> pairs_have_nodes_all_unique (l ++ l') .
  Proof. induction l; intros l' A B C.
         - rewrite app_nil_l. exact C.
         - destruct a as [h j]. 
           rewrite <- app_comm_cons. 
           apply pairs_have_nodes_all_unique_cons_elim in B.
           destruct B as [B D].
           apply pairs_have_nodes_all_unique_cons_intro.
           + intros w q E.
             apply in_list_concat_elim in E.
             * destruct E as [E | E].
               -- exact (B _ _ E). 
               -- assert (F : (h, j) ∈ (h, j) :: l).
                  {
                    apply in_list_cons_intro.
                    apply eqS_N_symmetric.
                    left.
                    apply eqS_N_reflexive. 
                  } 
                  exact (A _ _ F _ _ E).
             * apply eqS_N_symmetric.               
           + apply IHl; auto.
             intros w q F w' q' G.
             assert (J : (w, q) ∈ (h, j) :: l).
             {
               apply in_list_cons_intro.
               apply eqS_N_symmetric.
               right. exact F. 
             } 
             exact (A _ _ J _ _ G). 
  Qed.


  Lemma pairs_have_nodes_all_unique_concat_elim :
    ∀ l l',
      pairs_have_nodes_all_unique (l ++ l')
      -> (*∀ (w : S) (q : nat),
          (w, q) ∈ l → ∀ (w' : S) (q' : nat), (w', q') ∈ l' → eqN q q' = false)*)
        (no_shared_nodes_in_value_node_lists l l') 
         *
         (pairs_have_nodes_all_unique l)
         * 
        (pairs_have_nodes_all_unique l').                                        
 Proof. induction l; intros l' A.       
        - rewrite app_nil_l in A.
          split.
          + split.
            * intros w q B. compute in B.
              discriminate B. 
            * simpl. auto. 
          + exact A. 
        - rewrite <- app_comm_cons in A.
          destruct a as [w q]. 
          apply pairs_have_nodes_all_unique_cons_elim in A.
          destruct A as [A B]. 
          apply IHl in B. destruct B as [[B C] D]. 
          split. 
          + split.
            * intros w'' q'' E w' q' F.
              apply in_list_cons_elim in E.
              -- destruct E as [E | E].
                 ++ apply brel_product_elim in E.
                    destruct E as [E G].
                    apply eqb_to_eq in G.
                    rewrite <- G.
                    assert (J : (w', q') ∈ l ++ l').
                    {
                      apply in_list_concat_intro; auto. 
                    } 
                    exact (A _ _ J). 
                 ++ exact (B _ _ E _ _ F). 
              -- apply eqS_N_symmetric. 
            * apply pairs_have_nodes_all_unique_cons_intro.
              -- intros w' q' E.
                 assert (F : (w', q') ∈ l ++ l').
                 {
                   apply in_list_concat_intro; auto. 
                 }
                 exact (A _ _ F). 
              -- exact C. 
          +  exact D.
 Qed.
 
  Lemma pairs_have_nodes_all_unique_rearrange_v0 :
    ∀ l p p',  pairs_have_nodes_all_unique (p :: p' :: l)
                  -> pairs_have_nodes_all_unique (p :: l). 
  Proof. intros l [w q] [w' q']; intro A.
         apply pairs_have_nodes_all_unique_cons_elim in A.
         destruct A as [A B]. 
         apply pairs_have_nodes_all_unique_cons_elim in B.
         destruct B as [B C].          
         apply pairs_have_nodes_all_unique_cons_intro; auto. 
         intros w'' q'' D.
         assert (E := B _ _ D). 
         assert (F := A w'' q'').
         assert ((w'', q'') ∈ (w', q') :: l).
         {
           apply in_list_cons_intro.
           apply eqS_N_symmetric.
           right. exact D. 
         } 
         exact (F H).
  Qed.
  
  Lemma pairs_have_nodes_all_unique_rearrange_v1 :
    ∀ est carry h j w q,    
    pairs_have_nodes_all_unique (((h, j) :: (w, q) :: est) ++ carry) 
    -> pairs_have_nodes_all_unique (((h, j) :: est) ++ (w, q) :: carry).
  Proof. intros est carry h j w q A.
         apply pairs_have_nodes_all_unique_concat_elim in A. 
         destruct A as [[A B] C].
         apply pairs_have_nodes_all_unique_cons_elim in B. 
         destruct B as [B D]. 
         apply pairs_have_nodes_all_unique_cons_elim in D. 
         destruct D as [D E]. 
         apply pairs_have_nodes_all_unique_concat_intro. 
         - intros w' q' F w'' q'' G.
           apply in_list_cons_elim in F.
           + apply in_list_cons_elim in G.
             * destruct F as [F | F];
                 destruct G as [G | G].
               -- apply brel_product_elim in F, G.
                  destruct F as [F1 F2].
                  destruct G as [G1 G2].
                  apply eqb_to_eq in F2, G2.
                  rewrite <- G2.
                  rewrite <- F2.
                  assert (H : (w, q) ∈ (w, q) :: est).
                  {
                    apply in_list_cons_intro; auto.
                    apply eqS_N_symmetric.
                    left. apply eqS_N_reflexive.
                  }
                  exact (B _ _ H). 
               -- apply brel_product_elim in F.
                  destruct F as [F1 F2].
                  apply eqb_to_eq in F2.
                  rewrite <- F2.
                  assert (H : (h, j) ∈ (h, j) :: (w, q) :: est).
                  {
                    apply in_list_cons_intro; auto.
                    apply eqS_N_symmetric.
                    left. apply eqS_N_reflexive.
                  }
                  exact (A _ _ H _ _ G). 
               -- apply brel_product_elim in G.
                  destruct G as [G1 G2].
                  apply eqb_to_eq in G2.
                  rewrite <- G2.
                  assert (H := D _ _ F).
                  case_eq(eqN q' q); intro J; auto.
                  apply symN in J. unfold eqN in H.
                  rewrite J in H. discriminate H. 
               -- assert (H : (w', q') ∈ (h, j) :: (w, q) :: est).
                  {
                   apply in_list_cons_intro; auto.
                   ++ apply eqS_N_symmetric.
                   ++ right. apply in_list_cons_intro; auto.
                      ** apply eqS_N_symmetric.
                  }
                  exact (A _ _ H _ _ G). 
             * apply eqS_N_symmetric. 
           + apply eqS_N_symmetric. 
         - apply pairs_have_nodes_all_unique_cons_intro; auto. 
           + intros w' q' F.
             assert (G : (w', q') ∈ (w, q) :: est).
             {
               apply in_list_cons_intro; auto.
               apply eqS_N_symmetric. 
             } 
             exact (B _ _ G). 
         - apply pairs_have_nodes_all_unique_cons_intro; auto. 
           + intros w' q' F.
             assert (G : (w, q) ∈ (h, j) :: (w, q) :: est).
             {
               apply in_list_cons_intro.
               * apply eqS_N_symmetric. 
               * right. apply in_list_cons_intro.
                 -- apply eqS_N_symmetric. 
                 -- left. apply eqS_N_reflexive. 
             } 
             exact (A _ _ G _ _ F). 
  Qed. 

  Lemma pairs_have_nodes_all_unique_rearrange_v2 :
    ∀ est carry h j w q,    
      pairs_have_nodes_all_unique (((h, j) :: (w, q) :: est) ++ carry)
      -> pairs_have_nodes_all_unique (((w, q) :: est) ++ (h, j) :: carry).
  Proof. intros est carry h j w q A.
         apply pairs_have_nodes_all_unique_concat_elim in A. 
         destruct A as [[A B] C].
         apply pairs_have_nodes_all_unique_cons_elim in B. 
         destruct B as [B D]. 
         apply pairs_have_nodes_all_unique_cons_elim in D. 
         destruct D as [D E]. 
         apply pairs_have_nodes_all_unique_concat_intro. 
         - intros w' q' F w'' q'' G.
           apply in_list_cons_elim in F.
           + apply in_list_cons_elim in G.
             * destruct F as [F | F];
                 destruct G as [G | G].
               -- apply brel_product_elim in F, G.
                  destruct F as [F1 F2].
                  destruct G as [G1 G2].
                  apply eqb_to_eq in F2, G2.
                  rewrite <- G2.
                  rewrite <- F2.
                  assert (H : (w, q) ∈ (w, q) :: est).
                  {
                    apply in_list_cons_intro; auto.
                    apply eqS_N_symmetric.
                    left. apply eqS_N_reflexive.
                  }
                  assert(J := B _ _ H). 
                  case_eq(eqN q j); intro K; auto.
                  unfold eqN in J, K.
                  apply symN in K. rewrite J in K.
                  discriminate K. 
               -- apply brel_product_elim in F.
                  destruct F as [F1 F2].
                  apply eqb_to_eq in F2.
                  rewrite <- F2.
                  assert (H : (w, q) ∈ (h, j) :: (w, q) :: est).
                  {
                    apply in_list_cons_intro; auto.
                    apply eqS_N_symmetric.
                    right. apply in_list_cons_intro; auto.
                    apply eqS_N_symmetric. left.
                    apply eqS_N_reflexive. 
                  }
                  exact(A _ _ H _ _ G). 
               -- apply brel_product_elim in G.
                  destruct G as [G1 G2].
                  apply eqb_to_eq in G2.
                  rewrite <- G2.
                  assert (H : (w', q') ∈ (w, q) :: est).
                  {
                    apply in_list_cons_intro; auto.
                    apply eqS_N_symmetric.
                  } 
                  assert (J := B _ _ H).
                  case_eq(eqN q' j); intro K; auto. 
                  apply symN in K. unfold eqN in J.
                  rewrite K in J. discriminate J. 
               -- assert (H : (w', q') ∈ (h, j) :: (w, q) :: est).
                  {
                   apply in_list_cons_intro; auto.
                   ++ apply eqS_N_symmetric.
                   ++ right. apply in_list_cons_intro; auto.
                      ** apply eqS_N_symmetric.
                  }
                  exact (A _ _ H _ _ G). 
             * apply eqS_N_symmetric. 
           + apply eqS_N_symmetric. 
         - apply pairs_have_nodes_all_unique_cons_intro; auto. 
         - apply pairs_have_nodes_all_unique_cons_intro; auto. 
           + intros w' q' F.
             assert (G : (h, j) ∈ (h, j) :: (w, q) :: est).
             {
               apply in_list_cons_intro.
               * apply eqS_N_symmetric. 
               * left. apply eqS_N_reflexive.
             } 
             exact (A _ _ G _ _ F). 
  Qed. 



     Lemma relax_edges_elim : 
   ∀ est w w' q q', 
      (w, q) ∈ relax_edges S L plus rtr m (w', q') est -> 
                    {w'' & ((w'', q) ∈ est) * (w =S= (w'' ⊕ (w' <| (m q' q))))}.
 Proof. induction est; intros w w' q q' A.
        - compute in A. discriminate A. 
        - destruct a as [v j].
          apply in_list_cons_elim in A.
          + destruct A as [A | A].
            * apply brel_product_elim in A.
              destruct A as [A B].
              exists v. split.
              -- apply in_list_cons_intro; auto.
                 ++ apply eqS_N_symmetric.
                 ++ left.
                    apply brel_product_intro; auto. 
              -- apply symS in A.
                 assert (C := cong_m _ _ _ _ (refN q') B).
                 assert (D := cong_rtr _ _ _ _ C (refS w')).
                 assert (E := cong _ _ _ _ (refS v) D). 
                 exact (trnS _ _ _ A E). 
            * destruct (IHest _ _ _ _ A) as [w'' [B C]].
              exists w''. split.
              -- apply in_list_cons_intro.
                 ++ apply eqS_N_symmetric.
                 ++  right. exact B. 
              -- exact C. 
          + apply eqS_N_symmetric.
 Qed.

 Lemma relax_edges_intro_simple : 
   ∀ est w_min q_min w u,
      (w, u) ∈ est -> 
         (w ⊕ (w_min <| m q_min u), u) ∈ relax_edges S L plus rtr m (w_min, q_min) est. 
 Proof. induction est; intros w_min q_min w u A.
        - compute in A. discriminate A.
        - destruct a as [h j]. 
          apply in_list_cons_elim in A.
          + destruct A as [A | A].
            * apply in_list_cons_intro.
              -- apply eqS_N_symmetric.
              -- left.
                 apply brel_product_elim in A.
                 destruct A as [A B].
                 apply brel_product_intro; auto.
                 assert (C := cong_m _ _ _ _ (refN q_min) B).
                 assert (D := cong_rtr _ _ _ _ C (refS w_min)).
                 exact(cong _ _ _ _ A D).
            * apply in_list_cons_intro.
              -- apply eqS_N_symmetric.
              -- right. apply IHest; auto. 
          + apply eqS_N_symmetric.
Qed.             
            
 Lemma relax_edges_intro : 
   ∀ est carry est' p w_min q_min w u, 
      FindMin p carry est = ((w_min, q_min), est') -> 
      (w, u) ∈ p :: (carry ++ est) -> 
      eqN u q_min = false -> 
      (w ⊕ (w_min <| m q_min u), u) ∈ relax_edges S L plus rtr m (w_min, q_min) est'. 
 Proof. induction est; intros carry est' p w_min q_min w u A B C.
        - simpl in A. destruct p as [w' q']. 
          inversion A. rewrite <- H1 in C.
          apply in_list_cons_elim in B.
          + destruct B as [B | B].
            * apply brel_product_elim in B.
              destruct B as [B D].
              apply symN in D. unfold eqN in C. 
              rewrite C in D.
              discriminate D. 
            * rewrite app_nil_r in B.
              rewrite H2 in B.
              apply relax_edges_intro_simple; auto. 
          + apply eqS_N_symmetric.
        - destruct p as [h j].
          destruct a as [w' q']. 
          simpl in A.
          case_eq(brel_lte_left eqS plus h w'); intro D; rewrite D in A.
          + (* show 
               B : (w, u) ∈ (h, j) :: carry ++ (w', q') :: est 
              -> 
               E : (w, u) ∈ (h, j) :: ((w', q') :: carry) ++ est

               Write a tactic for this kind of situation? 
             *)
            assert (E : (w, u) ∈ (h, j) :: ((w', q') :: carry) ++ est).
            {
              apply in_list_cons_intro.
              * apply eqS_N_symmetric.
              * apply in_list_cons_elim in B.
                -- destruct B as [B | B].
                   ++ left. exact B. 
                   ++ right.
                      apply in_list_concat_intro.
                      apply in_list_concat_elim in B.
                      ** destruct B as [B | B].
                         --- left. apply in_list_cons_intro.
                             +++ apply eqS_N_symmetric.
                             +++ right. exact B. 
                         --- apply in_list_cons_elim in B.
                             +++ destruct B as [B | B].
                                 *** left.
                                     apply in_list_cons_intro.
                                     ---- apply eqS_N_symmetric.
                                     ---- left. exact B. 
                                 *** right. exact B. 
                             +++ apply eqS_N_symmetric.
                      ** apply eqS_N_symmetric.
                -- apply eqS_N_symmetric.
            } 
            exact (IHest _ _ _ _ _ _ _ A E C).
          + (* show 
               B : (w, u) ∈ (h, j) :: carry ++ (w', q') :: est
              -> 
               E : (w, u) ∈ (w', q') :: ((h, j) :: carry) ++ est

               Write a tactic for this kind of situation? 
             *)
            assert (E : (w, u) ∈ (w', q') :: ((h, j) :: carry) ++ est).
            {
              apply in_list_cons_intro.
              * apply eqS_N_symmetric.
              * apply in_list_cons_elim in B.
                -- destruct B as [B | B].
                   ++ right.
                      apply in_list_concat_intro.
                      left. apply in_list_cons_intro. 
                      ** apply eqS_N_symmetric.
                      ** left. exact B. 
                   ++ apply in_list_concat_elim in B.
                      destruct B as [B | B].
                      ** right.
                         apply in_list_concat_intro.
                         left.
                         apply in_list_cons_intro.
                         --- apply eqS_N_symmetric.
                         --- right. exact B. 
                      ** apply in_list_cons_elim in B.
                         --- destruct B as [B | B].
                             +++ left. exact B. 
                             +++ right.
                                 apply in_list_concat_intro.
                                 right. exact B. 
                         --- apply eqS_N_symmetric.
                      ** apply eqS_N_symmetric.                             
                -- apply eqS_N_symmetric.
            } 
            exact (IHest _ _ _ _ _ _ _ A E C).
 Qed. 

    
  Lemma relax_edges_preserves_uniqueness : 
    ∀ est w_min q_min,
      pairs_have_nodes_all_unique ((w_min, q_min) :: est)
      -> pairs_have_nodes_all_unique (relax_edges S L plus rtr m (w_min, q_min) est).
  Proof. induction est as [ | [h j] est']; intros w_min q_min A.
         - simpl. auto. 
         - simpl. split. 
           + intros w q B.
             apply relax_edges_elim in B.
             destruct B as [w' [B C]].
             simpl in A.
             destruct A as [_ [D _]].
             exact (D _ _ B). 
           + apply IHest'.
             exact (pairs_have_nodes_all_unique_rearrange_v0 _ _ _ A).
  Qed. 

  Lemma find_min_node_preserves_uniqueness : 
    ∀ est carry est' h j w_min q_min,
      pairs_have_nodes_all_unique (((h, j) ::est) ++ carry)
      → FindMin (h, j) carry est = (w_min, q_min, est')
      → pairs_have_nodes_all_unique ((w_min, q_min) :: est'). 
  Proof. induction est; intros carry est' h j w_min q_min A B.
         - simpl in B. inversion B.
           rewrite H0, H1, H2 in A.
           simpl in A. simpl. exact A. 
         - destruct a as [w' q'].
           simpl in B. 
           case_eq(brel_lte_left eqS plus h w'); intro D; rewrite D in B.
           + assert (A' : pairs_have_nodes_all_unique (((h, j) :: est) ++ ((w', q') :: carry))).
             {
               apply pairs_have_nodes_all_unique_rearrange_v1 in A. exact A.
             } 
             apply (IHest ((w', q') :: carry) _ _ _ _ _ A' B). 
           + assert (A' : pairs_have_nodes_all_unique (((w', q') :: est) ++ ((h, j) :: carry))).
             {
               apply pairs_have_nodes_all_unique_rearrange_v2 in A. exact A.
             } 
             apply (IHest ((h, j) :: carry) _ _ _ _ _ A' B). 
  Qed. 

  Lemma q_min_not_in_est' : 
    ∀ est est' h j w_min q_min,
      pairs_have_nodes_all_unique (((h, j) ::est))
      → FindMin (h, j) [] est = (w_min, q_min, est')
      → node_not_in_value_node_list q_min est'. 
  Proof. intros est est' h j w_min q_min A B.
         rewrite app_nil_end in A. 
         assert (C := find_min_node_preserves_uniqueness est [] est' h j w_min q_min A B). 
         unfold pairs_have_nodes_all_unique in C.
         destruct C as [C _].
         exact C.
  Qed. 
         
  (* we really should have a general version of in_list_map elim .... *) 
  Lemma in_map_elim : 
        ∀ l w q, (w, q) ∈ map (λ j : Node, (one <| m i j, j)) l -> q ∈' l. 
  Proof. induction l; simpl; intros w q A.
         - exact A. 
         - case_eq(q =?N a); intro B. 
           + simpl. reflexivity.
           + simpl. assert (C := IHl w q).
             apply C.
             apply bop_or_elim in A.
             destruct A as [A | A].
             * apply bop_and_elim in A.
               destruct A as [_ A].
               rewrite A in B. discriminate B. 
             * exact A. 
  Qed. 

  Lemma map_init_preserves_uniqueness : 
        ∀ l, nodes_all_unique l -> 
             pairs_have_nodes_all_unique (map (λ j : Node, (one <| m i j, j)) l). 
  Proof. induction l; intro A.
         - simpl. auto. 
         - simpl. simpl in A.
           destruct A as [A B]. 
           split.
           + intros w q C.
             apply in_map_elim in C.
             assert (D := A _ C).
             case_eq(eqN a q); intro E; auto.
             apply symN in E. rewrite E in D.
             discriminate D. 
           + apply IHl; auto. 
  Qed. 


  
  (******************* Invariantes for Dijkstra ***************************************)


   Definition Invariant_i_in_visited (s  : state S) := 
     (one, i) ∈ visited _ s.

   Definition Invariant_visited_not_in_estimated (s : state S) := 
      ∀ w w' q q',  (w, q) ∈ visited _ s → (w', q') ∈ estimated _ s → eqN q q' = false. 

   Definition Invariant_visited_closer (s : state S) := 
     ∀ w q,  (w, q) ∈ (visited _ s) → ∀ w' q', (w', q') ∈ (estimated _ s) → w ≦ w'. 

   Definition Invariant_right_equation_visited (s : state S) := 
     ∀ w j, (w, j) ∈ visited _ s →
         w =S= (I i j ⊕ (⨁ (λ '(w', q), w' <| m q j) (visited S s))).

   Definition Invariant_right_equation_estimated (s : state S) := 
     ∀ w j, (w, j) ∈ estimated _ s  →
            w =S= (⨁ (λ '(w', q), w' <| m q j) (visited S s)).

  Definition Invariant_all_nodes_unique (s : state S) :=
    pairs_have_nodes_all_unique ((visited _ s) ++ (estimated _ s)).

(*  This is only needed at the very end to show that
    Invariant_visited_not_in_estimated. 
    It is implied by Invariant_all_nodes_unique. 
*) 
  Definition Invariant_estimated_node_unique (s : state S) :=
    pairs_have_nodes_all_unique (estimated _ s). 

(*  This is only needed at the very end to show that
    visited_to_map is correct. 
    It is implied by Invariant_all_nodes_unique. 
*) 
  Definition Invariant_visited_node_unique (s : state S) :=
    pairs_have_nodes_all_unique (visited _ s). 

  
   (*********** Invariants hold for initial state IS **************************)
  Lemma Invariant_estimated_node_unique_IS :
     Invariant_estimated_node_unique IS.
  Proof. unfold IS, Invariant_estimated_node_unique, initial_state. unfold estimated.
         apply map_init_preserves_uniqueness.
         apply nodes_0_to_finish_without_i_unique. 
  Qed. 


  Lemma Invariant_visited_node_unique_IS :
     Invariant_visited_node_unique IS.
  Proof. unfold IS, Invariant_visited_node_unique, initial_state.
         unfold visited.
         unfold pairs_have_nodes_all_unique.
         split; auto.
         intros w q A. 
         compute in A. discriminate A. 
  Qed. 


    Lemma Invariant_all_nodes_unique_IS :
     Invariant_all_nodes_unique IS.
     Proof. unfold IS, Invariant_all_nodes_unique, initial_state.
            unfold visited, estimated.
            apply pairs_have_nodes_all_unique_concat_intro.
            - intros w q A w' q' B.
              apply in_list_cons_elim in A.
              + destruct A as [A | A].
                * apply brel_product_elim in A.
                  destruct A as [A1 A2].
                  apply in_map_elim in B.
                  apply in_nodes_0_to_finish_without_i_elim in B.
                  case_eq(eqN q q'); intro C; auto.
                  assert (D := trnN _ _ _ A2 C).
                  apply symN in D. rewrite D in B.
                  discriminate B. 
                * compute in A. discriminate A.
              + apply eqS_N_symmetric.
            - unfold pairs_have_nodes_all_unique.
              split; auto.
              intros w q A. 
              compute in A. discriminate A.
            - apply map_init_preserves_uniqueness.
              apply nodes_0_to_finish_without_i_unique.
     Qed. 


  
 Lemma Invariant_i_in_visited_IS : Invariant_i_in_visited IS. 
 Proof. unfold Invariant_i_in_visited.
        unfold IS. unfold initial_state.
        apply in_list_cons_intro. 
        - apply eqS_N_symmetric.
        - left. apply eqS_N_reflexive. 
 Qed.
            
 (* move this to eqv.list.v ? *)
 Lemma in_list_map_intro
       (V U : Type)
       (eqV : brel V)
       (eqU : brel U)
       (symV : brel_symmetric V eqV) 
       (f : V -> U)
       (cong_f : ∀ v v', eqV v v' = true -> eqU (f v) (f v') = true)
       (v : V) :
   ∀ l, in_list eqV l v = true -> in_list eqU (map f l) (f v) = true.
 Proof. induction l; intro A. 
        - compute in A. discriminate A. 
        - apply in_list_cons_elim in A; auto. simpl. 
          apply bop_or_intro. 
          + simpl. destruct A as [A | A].
            * left. apply cong_f; auto. 
            * right. apply IHl; auto. 
 Qed.

   Lemma Invariant_visited_not_in_estimated_IS :
     Invariant_visited_not_in_estimated IS.
   Proof. intros w w' q q'.
          unfold IS. unfold initial_state.
          intros A B.
          apply in_list_cons_elim in A.
          - destruct A as [A | A].
            + apply brel_product_elim in A.
              destruct A as [A C].
              apply initial_estimate_elim in B. destruct B as [B D].
              apply in_nodes_0_to_finish_without_i_elim in D.
              unfold eqN in *.
              rewrite (conN _ _ _ _  (refN q') C) in D.
              case_eq(q =?N q'); intro E; auto.
              apply symN in E. rewrite E in D.
              discriminate D. 
            + compute in A. discriminate A. 
          - apply eqS_N_symmetric. 
   Qed. 
   
   Lemma Invariant_visited_closer_IS :
     Invariant_visited_closer IS.
   Proof. unfold IS. unfold initial_state; simpl.
          intros w q A w' q' B. 
          apply in_list_cons_elim in A.
          - destruct A as [A | A].
            + apply brel_product_elim in A.
              destruct A as [A C].
              assert (D := one_is_bottom w').
              assert (E := lte_congruence _ _ _ _ A (refS w')).
              rewrite E in D.  exact D. 
            + compute in A. discriminate A. 
          - apply eqS_N_symmetric.
   Qed. 

 Lemma Invariant_right_equation_visited_IS :
   Invariant_right_equation_visited IS.
 Proof. intros w j.
        unfold IS. unfold initial_state. 
        intro A. unfold big_plus. simpl.
        apply in_list_cons_elim in A.
        - destruct A as [A | A].
          ++ apply brel_product_elim in A.
             destruct A as [A B].
             assert (C := I_on_diagonal _  B).
             assert (D := cong _ _ _ _ C (refS ((one <| m i j) ⊕ zero))).
             destruct (oneAnn ((one <| m i j) ⊕ zero)) as [E F]. 
             apply symS in A, D, E. 
             exact (trnS _ _ _ (trnS _ _ _ A E) D). 
          ++ compute in A. discriminate A. 
        - apply eqS_N_symmetric. 
 Qed.


 Lemma Invariant_right_equation_estimated_IS :
   Invariant_right_equation_estimated IS.
 Proof. intros w j.
        unfold IS. unfold initial_state; simpl.
        intro A.
        apply initial_estimate_elim in A.
        destruct A as [A B].
        unfold big_plus. simpl. 
        destruct (zeroId (one <| m i j)) as [C D].
        apply symS in D.
        exact (trnS _ _ _ A D). 
 Qed. 
 

 (*********** Invariantes are preserved by one step of dijkstra, D1 **************************)

 
 Lemma find_min_node_elim_for_result_list : 
   ∀ est carry est' p w_min q_min, 
     FindMin p carry est = ((w_min, q_min), est') ->
                   ∀ w q, (w, q) ∈ est' -> (w, q) ∈ p :: (carry ++ est). 
  Proof. induction est; intros carry est' p w_min q_min A. 
         - destruct p as [w' q']. simpl in A.
           inversion A.
           intros w q B. rewrite app_nil_r. 
           apply in_list_cons_intro.
           + apply eqS_N_symmetric.
           + right. exact B.
         - intros w q B. simpl in A. 
           destruct a as [h' j']. 
           destruct p as [h j].
           case_eq(brel_lte_left eqS plus h h'); intro C; rewrite C in A.
           + assert (D := IHest _ _ _ _ _ A _ _ B).
             (* show 
                D : (w, q) ∈ (h, j) :: ((h', j') :: carry) ++ est
                ============================
                    (w, q) ∈ (h, j) :: carry ++ (h', j') :: est

                Write a tactic for this kind of situation? 
             *) 
             apply in_list_cons_elim in D.
             * destruct D as [D | D].
               -- apply in_list_cons_intro.
                  ++ apply eqS_N_symmetric.
                  ++ left. exact D. 
               -- apply in_list_concat_elim in D.
                  ** destruct D as [D | D].
                     --- apply in_list_cons_intro.
                         +++ apply eqS_N_symmetric.
                         +++ right.
                             apply in_list_concat_intro.
                             apply in_list_cons_elim in D.
                             *** destruct D as [D | D].
                                 ---- right.
                                      apply in_list_cons_intro.
                                      ++++ apply eqS_N_symmetric.
                                      ++++ left. exact D. 
                                 ---- left. exact D.
                             *** apply eqS_N_symmetric.
                     --- apply in_list_cons_intro.
                         +++ apply eqS_N_symmetric.
                         +++ right.
                             apply in_list_concat_intro.
                             right. apply in_list_cons_intro.
                             *** apply eqS_N_symmetric.
                             *** right. exact D. 
                  ** apply eqS_N_symmetric. 
             * apply eqS_N_symmetric. 
           + assert (D := IHest _ _ _ _ _ A _ _ B).
             (* show 
                D : (w, q) ∈ (h', j') :: ((h, j) :: carry) ++ est
                ============================
                    (w, q) ∈ (h, j) :: carry ++ (h', j') :: est

                Write a tactic for this kind of situation? 
             *) 
             apply in_list_cons_elim in D.
             * destruct D as [D | D].
               -- apply in_list_cons_intro.
                  ++ apply eqS_N_symmetric.
                  ++ right.
                     apply in_list_concat_intro.
                     right.
                     apply in_list_cons_intro.
                     ** apply eqS_N_symmetric.
                     ** left. exact D. 
               -- apply in_list_concat_elim in D.
                  ++ destruct D as [D | D].
                     ** apply in_list_cons_intro.
                        --- apply eqS_N_symmetric.
                        --- apply in_list_cons_elim in D.
                            +++ destruct D as [D | D].
                                *** left. exact D. 
                                *** right.
                                    apply in_list_concat_intro.
                                    left. exact D. 
                            +++ apply eqS_N_symmetric. 
                     ** apply in_list_cons_intro.
                        --- apply eqS_N_symmetric.
                        --- right. apply in_list_concat_intro.
                            right.
                            apply in_list_cons_intro.
                            +++ apply eqS_N_symmetric.
                            +++ right. exact D. 
                  ++ apply eqS_N_symmetric. 
             * apply eqS_N_symmetric. 
  Qed. 

  

  Lemma find_min_node_elim_for_head_minimality : 
   ∀ est carry est' h j w_min q_min, 
     FindMin (h, j) carry est = ((w_min, q_min), est')
     ->  w_min ≦ h.
  Proof. induction est; intros carry est' h j w_min q_min A.
         - simpl in A.
           inversion A.
           apply lte_ref.
         - simpl in A. destruct a as [w q]. 
           case_eq(brel_lte_left eqS plus h w); intro B; rewrite B in A. 
           + exact (IHest _ _ _ _ _ _ A). 
           + assert (C := IHest _ _ _ _ _ _ A).
             assert (D : w ≦ h).
             {
               destruct (lte_total w h) as [E | E].
               * exact E. 
               * rewrite E in B.
                 discriminate B. 
             } 
             exact (lte_trn _ _ _ C D).
  Qed.

  
    Lemma find_min_node_elim_for_minimality : 
    ∀ est carry est' p w_min q_min,
      FindMin p carry est = ((w_min, q_min), est')
     -> (∀ w q, (w, q) ∈ carry -> w_min ≦ w)                                                    
     -> (∀ w q, (w, q) ∈ est'  -> w_min ≦ w). 
     
  Proof. induction est; intros carry est' p w_min q_min A B w q C.
         - simpl in A. destruct p as [w' q'].
           inversion A.
           rewrite H2 in B.
           exact (B _ _ C). 
         - destruct a as [w' q'].
           destruct p as [h j].
           simpl in A.
           case_eq(brel_lte_left eqS plus h w'); intro D; rewrite D in A.
           + assert (E := IHest _ _ _ _ _ A). 
             assert (F : ∀ (w : S) (q : nat), (w, q) ∈ (w', q') :: carry → w_min ≦ w).
             {
               intros w'' q'' G.
               apply in_list_cons_elim in G. 
               * destruct G as [G | G].
                 -- (* w_min ≦ h ≦ w' = w'' *)
                   apply brel_product_elim in G.
                   destruct G as [G H]. 
                   assert (J := find_min_node_elim_for_head_minimality _ _ _ _ _ _ _ A).
                   assert (K := lte_trn _ _ _ J D).
                   rewrite <- (lte_congruence _ _ _ _ (refS w_min) G).
                   exact K. 
                 -- exact (B w'' q'' G). 
               * apply eqS_N_symmetric. 
              } 
             exact (E F _ _ C). 
           + assert (E := IHest _ _ _ _ _ A). 
             assert (F : ∀ (w : S) (q : nat), (w, q) ∈ (h, j) :: carry → w_min ≦ w).
             {
               intros w'' q'' G.
               apply in_list_cons_elim in G. 
               * destruct G as [G | G].
                 -- (* w_min ≦ w' ≦ h = w'' *)
                   apply brel_product_elim in G.
                   destruct G as [G H]. 
                   assert (J := find_min_node_elim_for_head_minimality _ _ _ _ _ _ _ A).
                   assert (K : w' ≦ h).
                   {
                     destruct (lte_total w' h) as [M | M].
                     * exact M. 
                     * rewrite M in D.
                       discriminate D. 
                   }
                   rewrite (lte_congruence _ _ _ _ (refS w') G) in K.
                   exact (lte_trn _ _ _ J K).
                 -- exact (B _ _ G). 
               * apply eqS_N_symmetric. 
              } 
             exact (E F _ _ C). 
  Qed. 

  Lemma find_min_node_elim_for_min_origin : 
   ∀ est carry est' p w_min q_min, 
     FindMin p carry est = (w_min, q_min, est')
     -> (w_min, q_min) ∈ p :: est. 
  Proof. induction est; intros carry est' p w_min q_min A.
         - simpl in A. destruct p as [w q].
           inversion A.
           apply in_list_cons_intro.
           + apply eqS_N_symmetric. 
           + left. apply eqS_N_reflexive.
         - destruct p as [h j].
           destruct a as [w' q']. 
           simpl in A.
           apply in_list_cons_intro.
           + apply eqS_N_symmetric.
           + case_eq(brel_lte_left eqS plus h w'); intro B; rewrite B in A.
             * apply IHest in A.
               apply in_list_cons_elim in A.
               -- destruct A as [A | A].
                  ++ left. exact A. 
                  ++ right.  apply in_list_cons_intro.
                     ** apply eqS_N_symmetric.
                     ** right. exact A. 
               -- apply eqS_N_symmetric. 
             * apply IHest in A.
               apply in_list_cons_elim in A.
               -- destruct A as [A | A].
                  ++ right.  apply in_list_cons_intro.
                     ** apply eqS_N_symmetric.
                     ** left. exact A.
                  ++ right.  apply in_list_cons_intro.
                     ** apply eqS_N_symmetric.
                     ** right. exact A.
               -- apply eqS_N_symmetric. 
  Qed. 


 Lemma in_visited_after_one_step:
   ∀ s w q ,
      Invariant_estimated_node_unique s -> 
      (w, q) ∈ visited S (dijkstra_one_step S L eqS plus rtr m s) -> 
           ((w, q) ∈ visited S s) 
           + 
           (∀ w' q', (w', q') ∈ estimated S (dijkstra_one_step S L eqS plus rtr m s) -> eqN q q' = false).
 Proof. intros s w q. destruct s. 
        unfold dijkstra_one_step.
        destruct estimated0 eqn:A. simpl. 
        - intros INV B. left. exact B. 
        - destruct (FindMin p [] l) as [[w_min q_min] est'] eqn:B. 
          destruct p as [w' q']. simpl.
          rewrite B. simpl.
          unfold Invariant_estimated_node_unique.
          unfold estimated. simpl. 
          intros [E INV] C. 
          apply bop_or_elim in C.
          destruct C as [C | C].
          * (* (w, q) = (w_min, q_min *) 
            right. 
            intros w'' q'' D.
            apply brel_product_elim in C.
            destruct C as [C J].
            apply eqb_to_eq in J. rewrite J. 
            apply relax_edges_elim in D.
            destruct D as [ v [D F]].
            assert (G : pairs_have_nodes_all_unique (((w', q') ::l) ++ [])).
            {
              rewrite app_nil_r. simpl. split; auto. 
            } 
            assert (K := find_min_node_preserves_uniqueness _ _ _ _ _ _ _ G B).
            unfold pairs_have_nodes_all_unique in K.
            destruct K as [K _].
            exact (K _ _ D). 
          * left. exact C.
 Qed. 
 
   Lemma estimated_persistance : 
   ∀ s w q , 
     (w, q) ∈ estimated S (dijkstra_one_step S L eqS plus rtr m s) -> { w' & (w', q) ∈ estimated S s}.
  Proof. unfold dijkstra_one_step. destruct s. 
        destruct estimated0 as [ | [h j] est] eqn:Eq1; simpl.
        - intros w q A.
          compute in A.
          discriminate A. 
        - intros w q A.
          destruct (FindMin (h, j) [] est) as [[w_min q_min] est'] eqn:Eq2.
          simpl in A.
          apply relax_edges_elim in A.
          destruct A as [w' [C D]].
          assert (E := find_min_node_elim_for_result_list _ _ _ _ _ _ Eq2).
          assert (F := E _ _ C).
          exists w'. exact F. 
  Qed.


 Lemma big_plus_to_equal_destinations: 
   ∀  l j j',
     j =N= j' -> 
          (⨁ (λ '(w, q), w <| m q j) l)
          =S=
          (⨁ (λ '(w, q), w <| m q j') l). 
 Proof. intros l j j' A.
        assert (B: ∀ p1 p2, eqS_N p1 p2 = true →
                            ((λ '(w', q), w' <| m q j) p1)
                            =S=
                            ((λ '(w', q), w' <| m q j') p2)).
        {
          intros [v1 j1] [v2 j2]. simpl. intro X.
          apply bop_and_elim in X. destruct X as [X Y].
          assert (Z := cong_m _ _ _ _ Y A).
          exact(cong_rtr _ _ _ _ Z X). 
        }
        exact (big_plus_congruence_general _ eqS refS plus cong zero 
                                         _ eqS_N 
                                         (λ '(w', q), w' <| m q j)
                                         (λ '(w', q), w' <| m q j')
                                         B l l 
                                         (brel_list_reflexive _ eqS_N eqS_N_reflexive l)). 
 Qed.

 (* really should have the general version of this somewhere .... *) 
 Lemma in_list_left_congruence :
   ∀  l p p', p =p= p' -> p ∈ l -> p' ∈ l.
 Proof. induction l; intros [v j] [v' j'] A B.
        - compute in B. discriminate B. 
        - destruct a as [v'' j''].          
          apply in_list_cons_intro.    
          + apply eqS_N_symmetric. 
          + apply in_list_cons_elim in B.
            * destruct B as [B | B].
              -- left.
                 apply brel_product_elim in A.
                 destruct A as [A1 A2].               
                 apply brel_product_elim in B.
                 destruct B as [B C].
                 apply brel_product_intro; auto.
                 ++ exact (trnS _ _ _ B A1). 
                 ++ exact (trnN _ _ _ C A2).
              -- right. exact (IHl _ _ A B).
            * apply eqS_N_symmetric. 
 Qed.               
              
  Lemma dijkstra_one_step_preserves_Invariant_i_in_visited (s : state S) :
    Invariant_i_in_visited s -> Invariant_i_in_visited (D1 s).
  Proof. unfold Invariant_i_in_visited, D1, dijkstra_one_step.
         destruct s; intro i_in_vis.
         destruct estimated0; simpl. 
         + exact i_in_vis. 
         + destruct (FindMin p [] estimated0) as [[w q] est]; simpl. 
           * apply bop_or_intro. right. exact i_in_vis.
  Qed.              

  (*
  Lemma dijkstra_one_step_preserves_Invariant_estimated_node_unique (s : state S) :
    Invariant_estimated_node_unique s -> Invariant_estimated_node_unique (D1 s).
  Proof. unfold Invariant_estimated_node_unique, D1, dijkstra_one_step.
         destruct s; simpl. intros est_unique.
         destruct estimated0 as [ | [h j] est] eqn:Eq1.
         - simpl. auto. 
         - destruct (FindMin (h, j) [] est) as [[w_min q_min] est'] eqn:Eq2.
           unfold estimated.
           assert (A : pairs_have_nodes_all_unique (((h, j) ::est) ++ [])).
           {
             rewrite app_nil_r; auto. 
           } 
           assert (B := find_min_node_preserves_uniqueness _ _ _ _ _ _ _ A Eq2). 
           apply relax_edges_preserves_uniqueness; auto. 
  Qed.


  Lemma dijkstra_one_step_preserves_Invariant_visited_node_unique (s : state S) :
    Invariant_visited_node_unique s -> Invariant_visited_node_unique (D1 s).
  Proof. unfold Invariant_visited_node_unique, D1, dijkstra_one_step.
         destruct s; simpl. intros vis_unique.
         destruct visited0 as [ | [h j] vis] eqn:Eq1.
         - simpl. destruct estimated0; simpl; auto.
           + destruct p as (h, j);
             destruct (FindMin (h, j) [] estimated0) as [[w_min q_min] est'] eqn:Eq2.
             simpl. split; auto. intros _ q A. discriminate A. 
         - destruct estimated0. 
           + unfold visited. exact vis_unique. 
           + destruct p as [h' j']. 
             destruct (FindMin (h', j') [] estimated0) as [[w_min q_min] est'] eqn:Eq2.
             simpl. split.
             * intros w' q' A. apply bop_or_elim in A. destruct A as [A | A].
               -- apply bop_and_elim in A.  destruct A as [A B].
                  admit. 
               -- admit. 
             * admit. 
Admitted.              

  
   *)

  Lemma dijkstra_one_step_preserves_Invariant_visited_not_in_estimated (s : state S) :
    Invariant_estimated_node_unique s -> 
    Invariant_visited_not_in_estimated s -> Invariant_visited_not_in_estimated (D1 s).
    Proof. unfold Invariant_visited_not_in_estimated, D1. 
           intros est_unique vis_est_disjoint w w' q q' A B.
           apply in_visited_after_one_step in A; auto. 
           destruct A as [A | A]. 
           -- apply estimated_persistance in B.
              destruct B as [w'' C].
              exact (vis_est_disjoint _ _ _ _ A C). 
           -- exact (A _ _ B).
    Qed.

    Lemma dijkstra_one_step_preserves_Invariant_all_nodes_unique (s : state S) :
    Invariant_all_nodes_unique s -> Invariant_all_nodes_unique (D1 s).
    Proof. unfold Invariant_all_nodes_unique, D1, dijkstra_one_step.
           destruct s; simpl. intros all_unique.
           destruct estimated0 as [ | [w q] est] eqn:EqEst.
           - simpl. exact all_unique.
           - destruct (FindMin (w, q) [] est) as [[w_min q_min] est'] eqn:FMN.
             unfold visited, estimated.
             assert (A := find_min_node_elim_for_min_origin _ _ _ _ _ _ FMN).
             apply pairs_have_nodes_all_unique_concat_elim in all_unique.
             destruct all_unique as [[U1 U2] U3]. 
             apply pairs_have_nodes_all_unique_concat_intro.
             + (* no_shared_nodes_in_value_node_lists ((w_min, q_min) :: visited0) (relax_edges S L plus rtr m (w_min, q_min) est') *) 
               unfold no_shared_nodes_in_value_node_lists in *.
               intros w' q' B. intros w'' q'' C.
               apply relax_edges_elim in C.
               destruct C as [w0 [C D]].
               apply in_list_cons_elim in B.
               * destruct B as [B | B].
                 -- apply brel_product_elim in B.
                    destruct B as [B1 B2].
                    assert (E := q_min_not_in_est' est est' w q w_min q_min U3 FMN _ _ C). 
                    case_eq(eqN q' q''); intro F; auto.
                    unfold eqN in E, F. 
                    rewrite (trnN _ _ _ B2 F) in E.
                    discriminate E. 
                 -- assert (F := U1 _ _ B).
                    assert (G := find_min_node_elim_for_result_list est [] est' (w, q) w_min q_min FMN _ _ C).
                    rewrite app_nil_l in G. 
                    exact (F _ _ G).
               * apply eqS_N_symmetric. 
             + (* pairs_have_nodes_all_unique ((w_min, q_min) :: visited0) *)
               simpl. split; auto.
               unfold no_shared_nodes_in_value_node_lists in U1. 
               intros w' q' B.
               assert (C := U1 _ _ B _ _ A).
               case_eq(eqN q_min q'); intro D; auto.
               apply symN in D. unfold eqN in C. rewrite C in D.
               discriminate D. 
             + (* pairs_have_nodes_all_unique (relax_edges S L plus rtr m (w_min, q_min) est') *)
               apply relax_edges_preserves_uniqueness.
               rewrite app_nil_end in U3.
               assert (B := find_min_node_preserves_uniqueness _ _ _ _ _ _ _ U3 FMN).
               apply pairs_have_nodes_all_unique_cons_elim in B.
               destruct B as [B1 B2]. 
               apply pairs_have_nodes_all_unique_cons_intro. 
               * (*  node_not_in_value_node_list q_min est' *)
                 exact B1. 
               * exact B2. 
    Qed. 

  Lemma dijkstra_one_step_preserves_Invariant_estimated_node_unique (s : state S) :
    Invariant_all_nodes_unique s -> Invariant_estimated_node_unique  s.
  Proof. intro A.
         unfold Invariant_all_nodes_unique  in A.
         unfold Invariant_estimated_node_unique.
         apply pairs_have_nodes_all_unique_concat_elim in A. 
         destruct A as [[A B] C].
         exact C.
  Qed. 

    Lemma dijkstra_one_step_preserves_Invariant_visited_node_unique (s : state S) :
    Invariant_all_nodes_unique s -> Invariant_visited_node_unique  s.
  Proof. intro A.
         unfold Invariant_all_nodes_unique  in A.
         unfold Invariant_estimated_node_unique.
         apply pairs_have_nodes_all_unique_concat_elim in A. 
         destruct A as [[A B] C].
         exact B.
  Qed. 

(*    
    Lemma dijkstra_one_step_preserves_Invariant_all_nodes_unique (s : state S) :
    Invariant_all_nodes_unique s -> Invariant_all_nodes_unique (D1 s).
  Proof. unfold Invariant_all_nodes_unique, D1, dijkstra_one_step.
         destruct s; simpl. intros all_unique.
         destruct visited0 as [ | [w q] vis] eqn:Eq1; 
           destruct estimated0 as [ | [w' q'] est] eqn:Eq2.
         - compute; auto. 
         - destruct (FindMin (w', q') [] est) as [[w_min q_min] est'] eqn:Eq3.
           unfold visited, estimated.
           admit. 
         - simpl. rewrite app_nil_r in *.
           simpl in all_unique. exact all_unique. 
         - apply pairs_have_nodes_all_unique_concat_elim in all_unique.
           destruct all_unique as [[U1 U2] U3].
           apply pairs_have_nodes_all_unique_cons_elim in U2, U3.
           assert (U3' := U3). 
           destruct U3 as [U4 U5].
           destruct U2 as [U2 U3]. 
           destruct (FindMin (w', q') [] est) as [[w_min q_min] est'] eqn:Eq3.
           unfold visited, estimated. 
           apply pairs_have_nodes_all_unique_concat_intro.
           + intros w0 q0 A w2 q2 B.
             apply relax_edges_elim in B.
             destruct B as [w'' [B1 B2]].
             admit. 
           + apply pairs_have_nodes_all_unique_cons_intro.
             * admit. 
             * apply pairs_have_nodes_all_unique_cons_intro.
               -- exact U2. 
               -- exact U3. 
           + apply relax_edges_preserves_uniqueness.
             apply (find_min_node_preserves_uniqueness est [] est' w' q' w_min q_min).
             * rewrite app_nil_r. exact U3'. 
             * exact Eq3.
Admitted.                
*) 


    Lemma dijkstra_one_step_preserves_Invariant_visited_closer (s : state S) :
        Invariant_visited_closer s -> Invariant_visited_closer (D1 s).
    Proof. unfold Invariant_visited_closer, D1, dijkstra_one_step.
           destruct s; simpl. intros vis_closest w q A w' q' B. 
           destruct estimated0; simpl; simpl in vis_closest, A, B.
           ++ compute in B. discriminate B. 
           ++ destruct p as [h j]. (* head of estimated *)
              destruct (FindMin (h, j) [] estimated0) as [[w_min q_min] est'] eqn:Eq1. 
              simpl in A, B.
              apply bop_or_elim in A.
              destruct A as [A | A].
              --- apply brel_product_elim in A.
                  destruct A as [A C].
                  rewrite (lte_congruence _ _ _ _ A (refS w')).
                  destruct (relax_edges_elim _ _ _ _ _ B) as [w'' [D E]].
                  assert (F := rtr_is_increasing w_min (m q_min q')).
                  assert (G : w_min ≦ w'').
                  {
                    assert (H := find_min_node_elim_for_minimality _ _ _ _ _ _ Eq1).
                    assert (J : ∀ (w : S) (q : nat), (w, q) ∈ [] → w_min ≦ w).
                    {
                      intros v j' K. compute in K. discriminate K. 
                    } 
                    exact(H J _ _ D).
                  } 
                  assert (J := plus_is_an_upper_bound _ _ _ G F).
                  rewrite (lte_congruence _ _ _ _ (refS w_min) E).
                  exact J. 
              --- assert (C := vis_closest w q A).
                  apply relax_edges_elim in B.
                  destruct B as [w''' [D E]].
                  assert (F := rtr_is_increasing w_min (m q_min q')).
                  assert (G : w ≦ w_min).
                  {
                    assert (H := find_min_node_elim_for_min_origin _ _ _ _ _ _ Eq1).
                    exact(C _ _ H). 
                  } 
                  assert (M : w ≦ w''').
                  {
                    assert(K := find_min_node_elim_for_minimality _ _ _ _ _ _ Eq1).
                    assert (J : ∀ (w : S) (q : nat), (w, q) ∈ [] → w_min ≦ w).
                    {
                      intros v j' K'. compute in K'. discriminate K'. 
                    } 
                    assert (M := K J _ _ D).
                    exact (lte_trn _ _ _ G M). 
                  }
                  assert (H : w ≦ (w_min <| m q_min q')).
                  {
                    exact (lte_trn _ _ _ G F). 
                  } 
                  assert (J := plus_is_an_upper_bound _ _ _ M H).
                  rewrite (lte_congruence _ _ _ _ (refS w) E).
                  exact J. 
    Qed.

    Lemma dijkstra_one_step_preserves_Invariant_right_equation_visited (s : state S) :
      Invariant_i_in_visited s
      -> Invariant_visited_not_in_estimated s
      -> Invariant_visited_closer s
      -> Invariant_right_equation_estimated s
      -> Invariant_right_equation_visited s -> Invariant_right_equation_visited (D1 s).
    Proof. unfold Invariant_right_equation_visited,
           D1, dijkstra_one_step.
           destruct s; simpl.
           intros i_in_vis vis_est_disjoint vis_closest right_equation_est right_equation_vis w j A. 
           destruct estimated0 as [ | [h hj] est] eqn:Eq1; 
             simpl; simpl in right_equation_vis, A.
           ** apply right_equation_vis; auto. 
           ** destruct (FindMin (h, hj) [] est) as [[w_min q_min] est'] eqn:Eq2.
              simpl; simpl in A.
(*              
              assert (Z := big_plus_cons _ _ eqS plus zero refS (λ '(w', q), w' <| m q j) (w_min, q_min) visited0).

              rewrite (big_plus_cons _ plus zero _ (λ '(w', q), w' <| m q j) ((w_min, q_min)) visited0).
*) 
              unfold Invariant_right_equation_estimated in right_equation_est.
              simpl in right_equation_est.                     
              apply bop_or_elim in A.
              destruct A as [A | A].
              +++ apply brel_product_elim in A.
                  destruct A as [A B]. 
                  (* Eq1 : estimated0 = (h, hj) :: est *)
                  assert (C := find_min_node_elim_for_min_origin _ _ _ _ _ _ Eq2).
                  assert (D1 := right_equation_est _ _ C).
                  assert (D : w_min =S= ⨁ (λ '(w', q), w' <| m q j) visited0).
                  { 
                    assert (F := big_plus_to_equal_destinations visited0 _ _ B). 
                    apply symS in F.
                    exact (trnS _ _ _ D1 F). 
                  }
                  assert (E := trnS _ _ _ A D).
                  assert (F : w ≦ (w_min <| m q_min j)).
                  {
                    rewrite (lte_congruence _ _ _ _ A (refS ((w_min <| m q_min j)))).
                    apply rtr_is_increasing. 
                  } 
                  assert (G : w =S= ((w_min <| m q_min j) ⊕ w)).
                  {
                    apply lte_elim_r; auto. 
                  }
                  assert (H := cong _ _ _ _ (refS (w_min <| m q_min j)) E).
                  assert (J := trnS _ _ _ G H). 
                  assert (K : (I i j) =S= zero).
                  {
                    apply I_off_diagonal.
                    case_eq(i =?N j); intro M; auto.
                    assert (P := trnN _ _ _ M B).
                    unfold Invariant_i_in_visited in i_in_vis. simpl in i_in_vis.
                    unfold Invariant_visited_not_in_estimated in vis_est_disjoint.
                    unfold visited, estimated in vis_est_disjoint.
                    assert (Q : (w_min, j) ∈ (h, hj) :: est).
                    {
                      assert (R : (w_min, q_min) =p= (w_min, j)).
                      {
                        apply brel_product_intro; auto. apply symN.
                        exact (trnN _ _ _ (symN _ _ M) P).
                      } 
                      exact (in_list_left_congruence _ _ _ R C). 
                    } 
                    assert (R := vis_est_disjoint _ _ _ _ i_in_vis Q). 
                    unfold eqN in R. rewrite M in R. discriminate R. 
                  } 
                  assert (M := cong _ _ _ _ K (refS (((w_min <| m q_min j) ⊕ ⨁ (λ '(w', q), w' <| m q j) visited0)))).
                  destruct (zeroId ((w_min <| m q_min j) ⊕ ⨁ (λ '(w', q), w' <| m q j) visited0)) as [P _]. 
                  assert (O := trnS _ _ _ M P). apply symS in O.
                  assert (Q := trnS _ _ _ J O).
                  exact Q. 
              +++ assert (B := right_equation_vis w j A).
                  assert (C := find_min_node_elim_for_min_origin _  _ _ _ _ _ Eq2).
                  assert (D := right_equation_est _ _ C).
                  unfold Invariant_visited_closer in vis_closest.
                  simpl in vis_closest.
                  assert (E := vis_closest _ _ A _ _ C). 
                  assert (F := rtr_is_increasing w_min (m q_min j)).
                  assert (G := lte_trn _ _ _ E F).                             
                  assert (H : w =S= ((w_min <| (m q_min j)) ⊕ w)).
                  {
                    apply lte_elim_r; auto. 
                  } 
                  assert (J : ((w_min <| m q_min j) ⊕ w)
                              =S=
                              ((w_min <| m q_min j) ⊕ (I i j ⊕ ⨁ (λ '(w', q), w' <| m q j) visited0))).
                  {
                    exact (cong _ _ _ _ (refS ((w_min <| m q_min j))) B). 
                  } 
                  assert (K := trnS _ _ _ H J).
                  assert (M := assoc (w_min <| m q_min j) (I i j) (⨁ (λ '(w', q), w' <| m q j) visited0)).
                  apply symS in M.
                  assert (O := trnS _ _ _ K M).
                  assert (P := comm (w_min <| m q_min j) (I i j)).
                  assert (Q := cong _ _ _ _ P (refS (⨁ (λ '(w', q), w' <| m q j) visited0))). 
                  assert (R := trnS _ _ _ O Q).
                  assert (U := assoc (I i j) (w_min <| m q_min j) (⨁ (λ '(w', q), w' <| m q j) visited0)).                                                      assert (W := trnS _ _ _ R U).
                  exact W.            
    Qed. 
    
    Lemma dijkstra_one_step_preserves_Invariant_right_equation_estimated (s : state S) :
     Invariant_right_equation_estimated s -> Invariant_right_equation_estimated (D1 s).
    Proof. unfold Invariant_right_equation_estimated, D1, dijkstra_one_step.
           destruct s; simpl. intros right_equation_est w j A. 
                    destruct estimated0 as [ | [h hj] est] eqn:Eq1;
                      (* Eq1 : estimated0 = (h, hj) :: est *) 
                      simpl.  
                    ** apply right_equation_est; auto. 
                    ** destruct (FindMin (h, hj) [] est) as [[w_min q_min] est'] eqn:Eq2.
                       unfold visited, estimated in right_equation_est.
                       simpl in A. simpl.
(*                       
                       rewrite (big_plus_cons _ plus zero _ (λ '(w', q), w' <| m q j) ((w_min, q_min)) visited0).
*) 
                       apply relax_edges_elim in A.
                       destruct A as [w' [A B]].
                       assert (C : (w', j) ∈ (h, hj) :: est).
                       {
                         assert (D := find_min_node_elim_for_result_list _ _ _ _ _ _ Eq2 _ _ A).
                         rewrite app_nil_l in D. 
                         exact D. 
                       }
                       assert (D := right_equation_est _ _ C).
                       assert (E := comm w' (w_min <| m q_min j)).
                       assert (F := trnS _ _ _ B E).
                       assert (G := cong _ _ _ _ (refS (w_min <| m q_min j)) D).
                       exact (trnS _ _ _ F G).            
    Qed. 


 Definition dijkstra_invariants (s : state S) :=
     (Invariant_i_in_visited s)
      * 
      ( (* (Invariant_estimated_node_unique s) *)
        (Invariant_all_nodes_unique s)    
      *
      ((Invariant_visited_not_in_estimated s)
       *
       ((Invariant_visited_closer s)
        * 
        ((Invariant_right_equation_visited s)
         *
         (Invariant_right_equation_estimated s))))).

    

  Lemma dijkstra_invariants_IS :
    dijkstra_invariants IS.
  Proof. unfold dijkstra_invariants.
         split.
         - apply Invariant_i_in_visited_IS. 
         - split.
           + (* apply Invariant_estimated_node_unique_IS. *)
             apply Invariant_all_nodes_unique_IS.
           + split. 
             * apply Invariant_visited_not_in_estimated_IS. 
             * split.
               -- apply Invariant_visited_closer_IS. 
               -- split.
                  ++ apply Invariant_right_equation_visited_IS.
                  ++ apply Invariant_right_equation_estimated_IS.
  Qed.                  

    
  Lemma dijkstra_one_step_preserves_all_invariants (s : state S) :
    dijkstra_invariants s -> dijkstra_invariants (D1 s).
  Proof. unfold dijkstra_invariants.
         intros [i_in_vis [all_unique [vis_est_disjoint [vis_closest [right_equation_vis right_equation_est]]]]]. 
         split.
         - exact (dijkstra_one_step_preserves_Invariant_i_in_visited s i_in_vis). 
         - split.
           + (*exact (dijkstra_one_step_preserves_Invariant_estimated_node_unique s est_unique). *)
             exact (dijkstra_one_step_preserves_Invariant_all_nodes_unique s all_unique). 
           + split.
             * exact (dijkstra_one_step_preserves_Invariant_visited_not_in_estimated s (dijkstra_one_step_preserves_Invariant_estimated_node_unique s all_unique) vis_est_disjoint).
             * split.
               -- exact (dijkstra_one_step_preserves_Invariant_visited_closer s vis_closest). 
               -- split.
                  ++ exact (dijkstra_one_step_preserves_Invariant_right_equation_visited s
                              i_in_vis vis_est_disjoint vis_closest right_equation_est right_equation_vis).
                  ++ exact (dijkstra_one_step_preserves_Invariant_right_equation_estimated s right_equation_est).
  Qed. 


  Lemma dijkstra_invariants_Dk :
    ∀ k, dijkstra_invariants (Dk k).
  Proof. induction k. 
         - apply dijkstra_invariants_IS.
         - unfold Dk. simpl. 
           apply dijkstra_one_step_preserves_all_invariants; auto. 
  Qed.

  Lemma dijkstra_invariants_DR :
     dijkstra_invariants DR.
  Proof. unfold DR. unfold dijkstra_raw.
         apply dijkstra_invariants_Dk. 
  Qed.


  (* Main result for dijkstra_raw

   ∀ (w : S) (j : nat), (w, j) ∈ visited S DR 
     → w =S= (I i j) ⊕ ⨁ (λ '(w', q), w' <| m q j) (visited S DR)
  *) 
  Lemma Invariant_right_equation_visited_DR :
     Invariant_right_equation_visited DR.
  Proof. destruct dijkstra_invariants_DR as [_ [_ [_ [_ [A _]]]]].
        exact A. 
  Qed.


  Lemma tmp0 :
    ∀ j, (j <? n) = true ->
         {w : S & ((w, j) ∈ (visited S DR))
                  *
                  (w =S= visited_to_map S (λ _ : Node, zero) (visited S DR) j)}.     
  Proof. intros j A.
         exists (visited_to_map S (λ _ : Node, zero) (visited S DR) j). split.
         - unfold visited_to_map.
           destruct (visited S DR).
           + admit. 
           + simpl. admit. 
         - apply refS. 
  Admitted.


  Lemma tmp00 :
    ∀ l w j, (w, j) ∈ l -> 
           (w =S= visited_to_map S (λ _ : Node, zero) l j).     
  Proof. induction l; intros w j A.
         - compute in A. discriminate . 
         - destruct a as [w' j']; simpl.
           apply in_list_cons_elim in A; auto.
           destruct A as [A | A].
           + apply brel_product_elim in A.
             destruct A as [A B].
             unfold visited_to_map.
             unfold fold_left.
             admit. 
           + 
  Admitted.

  
  Lemma dijkstra_in_visited :   
    ∀ j, (j <? n) = true -> (D j, j) ∈ visited S DR.
  Proof. intros j A.
         unfold D. unfold dijkstra. unfold DR.
         destruct (tmp0 j A) as [w [B C]].
         unfold DR in B, C.
         assert ((w, j) =p= (visited_to_map S (λ _ : Node, zero)
                                            (visited S (dijkstra_raw S L eqS one plus rtr m n i)) j, j)).
         {
           apply brel_product_intro; auto.
           apply refN. 
         }
         exact (in_list_left_congruence _ _ _ H B). 
  Qed. 


  Lemma dijkstra_big_plus_equation_1 : ∀ l j f,
    (⨁ (λ '(w', q), w' <| m q j) (map (λ q, (f q, q)) l))
     =S= 
    (⨁ (λ q, f q <| m q j) l). 
  Proof. induction l; intros j f. 
         - compute. apply refS.
         - simpl.
           assert (A := big_plus_cons _ _ eqS refS plus zero (λ '(w', q), w' <| m q j) (f a, a) ((map (λ q : Node, (f q, q))) l)).
           assert (B := big_plus_cons _ _ eqS refS plus zero (λ q : Node, f q <| m q j) a l).
           simpl in A, B.
           assert (C : 
                    ((f a <| m a j) ⊕ ⨁ (λ '(w', q), w' <| m q j) (map (λ q : Node, (f q, q)) l))
                    =S=
                      ((f a <| m a j) ⊕ ⨁ (λ q : Node, f q <| m q j) l)).
           {
             exact (cong _ _ _ _ (refS (f a <| m a j)) (IHl j f)).
           } 
           assert (D := trnS _ _ _ A C). apply symS in B. 
           exact (trnS _ _ _ D B). 
  Qed.

  Lemma dijkstra_big_plus_equation_2 (j : Node) : 
     (⨁ (λ '(w', q), w' <| m q j) (map (λ q, (D q, q)) (list_enum n)))
     =S= 
     (⨁ (λ q, D q <| m q j) (list_enum n)). 
  Proof. apply dijkstra_big_plus_equation_1. Qed.

    (*


     Show : Permutation (visited S DR) (map (λ q, (D q, q)) (list_enum n))

            Permutation (visited S DR) 
                        (map (λ q, ((visited_to_map (λ x, zero) (visited S DR)) q, q)) (list_enum n))

            Permutation lp 
                        (map (λ q, ((visited_to_map (λ x, zero) lp) q, q)) ?l?)


  Definition visited_to_map (g : Node -> S) (l : list (S * Node)) : Node -> S := 
    List.fold_left (λ f '(v, q) x, if brel_eq_nat x q then v else f x) l g.

     *)

(*
    Lemma dijkstra_permutation_lemma_general :
    ∀ f pl l ,
    PermutationEqv _ eqN l (map snd pl) -> 
    PermutationEqv _ eqS_N pl (map (λ q : Node, (visited_to_map S f pl q, q)) l). 
    Proof. intro f. induction pl as [ | [w q] pl']; intros l A; simpl.
           - admit.
           - simpl in A. 
*) 
  Lemma dijkstra_permutation_lemma_general :
    ∀ f pl l ,
    PermutationEqv _ eqN l (map snd pl) -> 
    PermutationEqv _ eqS_N pl (map (λ q : Node, (visited_to_map S f pl q, q)) l). 
  Proof. intro f. induction pl as [ | [w q] pl'];
           induction l as [ | q' l']; simpl; intro A; try auto. 
         - apply perm_eqv_nil.
         - apply PermutationEqv_symmetric in A; auto. 
           apply PermutationEqv_nil_cons in A. elim A; auto.
           apply brel_eq_nat_symmetric. 
         - apply PermutationEqv_nil_cons in A. elim A. 
         - admit. 
  Admitted.

  Lemma test (k : nat) :
    PermutationEqv _ eqN (list_enum k) (map snd (visited S (dijkstra_k_steps S L eqS one plus rtr m k i (nat_pred k)))).
  Proof. induction k.
         - simpl. admit.
         - simpl. admit.
  Admitted.            

  Lemma list_enum_permutation_lemma :
    PermutationEqv _ eqN (list_enum n) (map snd (visited S DR)). 
  Proof. unfold DR. unfold dijkstra_raw.
         apply test.
  Qed. 
  
  Lemma dijkstra_permutation_lemma :
    PermutationEqv _ eqS_N
      (visited S DR)
      (map (λ q, (D q, q)) (list_enum n)).
  Proof. unfold D, DR. unfold dijkstra.
(*

  PermutationEqv (visited S (dijkstra_raw S L eqS one plus rtr m n i))
                 (map (λ q : Node, (visited_to_map S (λ _ : Node, zero) (visited S (dijkstra_raw S L eqS one plus rtr m n i)) q, q)) 
                      (list_enum n))


*) 
         
         apply dijkstra_permutation_lemma_general.
         apply list_enum_permutation_lemma. 
  Qed. 

  Lemma dijkstra_big_plus_equation_3 (j : Node) : 
     (⨁ (λ '(w', q), w' <| m q j) (visited S DR))
     =S= 
     (⨁ (λ '(w', q), w' <| m q j) (map (λ q, (D q, q)) (list_enum n))).
  Proof. apply (big_plus_permutation _ _ eqS refS symS trnS eqS_N); auto.
         - apply eqS_N_reflexive.
         - intros [w q] [w' q'] Z.
           apply brel_product_elim in Z; auto.
           destruct Z as [Z Z']. 
           apply cong_rtr; auto. 
           + apply cong_m; auto.
             apply brel_eq_nat_reflexive. 
         - apply dijkstra_permutation_lemma.
  Qed.
  
  Lemma dijkstra_big_plus_equation (j : Node) : 
    (⨁ (λ '(w', q), w' <| m q j) (visited S DR))
     =S= 
    (⨁ (λ q, D q <| m q j) (list_enum n)).
  Proof. assert (A := dijkstra_big_plus_equation_3 j).
         assert (B := dijkstra_big_plus_equation_2 j).
         exact (trnS _ _ _ A B). 
  Qed. 
    
(*  Main non-classical result. 

              (D i)[j] = ((D i) <| A)[j] + (v i)[j] 
                       = (sum_q (D i)[q] <| A[q,j]) + (v i)[j] 

*)
  Theorem dijkstra_solves_right_equation : 
  ∀ j, j <? n = true -> D j =S= (I i j ⊕ (⨁ (λ q, D q <| m q j) (list_enum n))).
  Proof. intros j A. 
         assert (B := Invariant_right_equation_visited_DR).
         unfold Invariant_right_equation_visited in B.
         assert (C := B (D j) j (dijkstra_in_visited j A)).
         assert (D := dijkstra_big_plus_equation j).
         assert (E := cong _ _ _ _ (refS (I i j)) D).
         exact (trnS _ _ _ C E).
  Qed.


End Theory. 

(*
Note: These assumptions are never used in Invariant_right_equation_visited_DR: 

    (zero_lt_n : Nat.ltb 0 n = true)
    (i_lt_n : Nat.ltb i n = true). 


Check Invariant_right_equation_visited_DR.

*) 
  
    







  




