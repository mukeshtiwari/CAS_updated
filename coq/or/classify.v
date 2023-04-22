Require Import Coq.Strings.String.

Require Import CAS.coq.common.compute.
Require Import CAS.coq.common.data.
Require Import CAS.coq.common.ast.
Require Import CAS.coq.eqv.properties.
Require Import CAS.coq.eqv.structures.
Require Import CAS.coq.or.properties.
Require Import CAS.coq.or.theory.
Require Import CAS.coq.or.structures. 
(* implementation hierarchy for orders 

           qo 
         / | \
        /  |  \ 
       /   |   \ 
      /    |    \ 
     /     |     \
     p   qo_wb   fo  
     |  /     \  |
     | /       \ |
    po_wb      fo_wb

wb = with_bottom 

qo = quasi order (ref, trans) 
po = partial order (ref, trans, antisymm, not total)   
fo = preference order quasi order (ref, trans, total) 
wb = with_bottom (currently needed for minset_union ) 

K is a class. 

    classify_K : K -> below K 

*) 
Section AMCAS.

Definition A_classify_po_with_bottom {S : Type} (A : A_po_with_bottom S) : @A_below_po_with_bottom S :=
  A_Below_po_with_bottom_top A.

Definition A_classify_fo_with_bottom {S : Type} (A : A_fo_with_bottom S) : @A_below_fo_with_bottom S :=
  A_Below_fo_with_bottom_top A.

Definition A_classify_qo_with_bottom {S : Type} (A : A_qo_with_bottom S) : @A_below_qo_with_bottom S :=
  let P := A_qo_with_bottom_proofs _ A in 
  match A_qo_total_d _ _ _ P with
  | inr ntot => match A_qo_antisymmetric_d _ _ _ P with
               | inr _    => A_Below_qo_with_bottom_top A
               | inl anti =>
                   A_Below_qo_with_bottom_po_with_bottom
                     (A_classify_po_with_bottom
                        {|
                          A_po_with_bottom_eqv           := A_qo_with_bottom_eqv _ A
                        ; A_po_with_bottom_lte           := A_qo_with_bottom_lte _ A
                        ; A_po_with_bottom_exists_top_d  :=
                            brel_exists_top_decidable_from_brel_exists_qo_top_decidable _ _ _ anti (A_qo_with_bottom_exists_top_d _ A)
                        ; A_po_with_bottom_exists_bottom :=
                            brel_exists_bottom_from_brel_exists_qo_bottom _ _ _ (A_qo_with_bottom_exists_bottom _ A)
                        ; A_po_with_bottom_proofs        :=
                            {|
                              A_po_congruence      := A_qo_congruence _ _ _ P
                            ; A_po_reflexive       := A_qo_reflexive _ _ _ P
                            ; A_po_transitive      := A_qo_transitive _ _ _ P
                            ; A_po_antisymmetric   := anti 
                            ; A_po_not_total       := ntot
                            |}
                        ; A_po_with_bottom_ast           := A_qo_with_bottom_ast _ A
                        |}
                     )
               end 
  | inl tot => A_Below_qo_with_bottom_fo_with_bottom
                 (A_classify_fo_with_bottom
                    {|
                      A_fo_with_bottom_eqv           := A_qo_with_bottom_eqv _ A
                    ; A_fo_with_bottom_lte           := A_qo_with_bottom_lte _ A
                    ; A_fo_with_bottom_exists_top_d  := A_qo_with_bottom_exists_top_d _ A
                    ; A_fo_with_bottom_exists_bottom := A_qo_with_bottom_exists_bottom _ A
                    ; A_fo_with_bottom_proofs        :=
                        {|
                          A_fo_congruence      := A_qo_congruence _ _ _ P
                        ; A_fo_reflexive       := A_qo_reflexive _ _ _ P
                        ; A_fo_transitive      := A_qo_transitive _ _ _ P
                        ; A_fo_antisymmetric_d := A_qo_antisymmetric_d _ _ _ P
                        ; A_fo_total           := tot
                        ; A_fo_trivial_d       := A_qo_trivial_d _ _ _ P
                        |}
                    ; A_fo_with_bottom_ast           := A_qo_with_bottom_ast _ A
                    |}
                 )
  end. 

Definition A_classify_po {S : Type} (A : A_po S) : @A_below_po S :=
match A_po_exists_bottom_d _ A with 
| inl bot => A_Below_po_po_with_bottom (
                  A_classify_po_with_bottom 
                    {|
                      A_po_with_bottom_eqv           := A_po_eqv _ A
                    ; A_po_with_bottom_lte           := A_po_lte _ A
                    ; A_po_with_bottom_exists_top_d  := A_po_exists_top_d _ A
                    ; A_po_with_bottom_exists_bottom := bot 
                    ; A_po_with_bottom_proofs        := A_po_proofs _ A 
                    ; A_po_with_bottom_ast           := A_po_ast _ A
                    |})
| _ => A_Below_po_top A
end.  

Definition A_classify_fo {S : Type} (A : A_fo S) : @A_below_fo S :=
match A_fo_exists_bottom_d _ A with 
| inl bot => A_Below_fo_fo_with_bottom (
                  A_classify_fo_with_bottom 
                    {|
                      A_fo_with_bottom_eqv           := A_fo_eqv _ A
                    ; A_fo_with_bottom_lte           := A_fo_lte _ A
                    ; A_fo_with_bottom_exists_top_d  := A_fo_exists_top_d _ A
                    ; A_fo_with_bottom_exists_bottom := bot 
                    ; A_fo_with_bottom_proofs        := A_fo_proofs _ A 
                    ; A_fo_with_bottom_ast           := A_fo_ast _ A
                    |})
| _ => A_Below_fo_top A
end.  
  
Definition A_classify_qo {S : Type} (A : A_qo S) : @A_below_qo S :=
let P := A_qo_proofs _ A in
match A_qo_antisymmetric_d _ _ _ P, A_qo_total_d _ _ _ P with 
| inl anti, inr ntot  =>
             A_Below_qo_po (
                  A_classify_po
                    {|
                      A_po_eqv           := A_qo_eqv _ A
                    ; A_po_lte           := A_qo_lte _ A
                    ; A_po_exists_top_d  :=
                        brel_exists_top_decidable_from_brel_exists_qo_top_decidable _ _ _ anti (A_qo_exists_top_d _ A)
                    ; A_po_exists_bottom_d :=
                        brel_exists_bottom_decidable_from_brel_exists_qo_bottom_decidable  _ _ _ anti (A_qo_exists_bottom_d _ A)
                    ; A_po_proofs        :=
                        {|
                          A_po_congruence     := A_qo_congruence _ _ _ P
                        ; A_po_reflexive      := A_qo_reflexive _ _ _ P
                        ; A_po_transitive     := A_qo_transitive _ _ _ P
                        ; A_po_antisymmetric  := anti 
                        ; A_po_not_total      := ntot 
                        |}
                    ; A_po_ast           := A_qo_ast _ A
                    |})
| _, inl tot => A_Below_qo_fo (
                      A_classify_fo
                        {|
                          A_fo_eqv           := A_qo_eqv _ A
                        ; A_fo_lte           := A_qo_lte _ A
                        ; A_fo_exists_top_d  := A_qo_exists_top_d _ A
                        ; A_fo_exists_bottom_d := A_qo_exists_bottom_d _ A
                        ; A_fo_proofs        :=
                            {|
                              A_fo_congruence      := A_qo_congruence _ _ _ P
                            ; A_fo_reflexive       := A_qo_reflexive _ _ _ P
                            ; A_fo_transitive      := A_qo_transitive _ _ _ P
                            ; A_fo_antisymmetric_d := A_qo_antisymmetric_d _ _ _ P
                            ; A_fo_total           := tot
                            ; A_fo_trivial_d       := A_qo_trivial_d _ _ _ P
                            |}
                        ; A_fo_ast           := A_qo_ast _ A
                        |})
| _, _ => match A_qo_exists_bottom_d _ A with
          | inl bot => A_Below_qo_qo_with_bottom (
                           A_classify_qo_with_bottom 
                             {|
                               A_qo_with_bottom_eqv           := A_qo_eqv _ A
                             ; A_qo_with_bottom_lte           := A_qo_lte _ A
                             ; A_qo_with_bottom_exists_top_d  := A_qo_exists_top_d _ A
                             ; A_qo_with_bottom_exists_bottom := bot 
                             ; A_qo_with_bottom_proofs        := P 
                             ; A_qo_with_bottom_ast           := A_qo_ast _ A
                             |}
                         ) 
          | _       => A_Below_qo_top A                                 
          end
end.

End AMCAS. 

Section MCAS.

Definition classify_po_with_bottom {S : Type} (A : @po_with_bottom S) : @below_po_with_bottom S :=
  Below_po_with_bottom_top A.

Definition classify_fo_with_bottom {S : Type} (A : @fo_with_bottom S) : @below_fo_with_bottom S :=
  Below_fo_with_bottom_top A.

Definition classify_qo_with_bottom {S : Type} (A : @qo_with_bottom S) : @below_qo_with_bottom S :=
  let P := qo_with_bottom_certs A in 
  match qo_total_d P with
  | Certify_Not_Total p =>
      match qo_antisymmetric_d P with
      | Certify_Not_Antisymmetric _    => Below_qo_with_bottom_top A
      | Certify_Antisymmetric =>
          Below_qo_with_bottom_po_with_bottom
            (classify_po_with_bottom
               {|
                 po_with_bottom_eqv           := qo_with_bottom_eqv A
               ; po_with_bottom_lte           := qo_with_bottom_lte A
               ; po_with_bottom_exists_top_d  :=
                      match qo_with_bottom_exists_top_d A with
                      | Certify_Exists_Qo_Top t => Certify_Exists_Top t
                      | Certify_Not_Exists_Qo_Top => Certify_Not_Exists_Top 
                      end 
               ; po_with_bottom_exists_bottom :=
                      match qo_with_bottom_exists_bottom A with
                      | Assert_Exists_Qo_Bottom b => Assert_Exists_Bottom b
                      end 
               ; po_with_bottom_certs        :=
                   {|
                     po_congruence      := qo_congruence P
                   ; po_reflexive       := qo_reflexive P
                   ; po_transitive      := qo_transitive P
                   ; po_antisymmetric   := Assert_Antisymmetric 
                   ; po_not_total       := Assert_Not_Total p 
                   |}
               ; po_with_bottom_ast           := qo_with_bottom_ast A
               |}
            )
      end 
  | Certify_Total =>
      Below_qo_with_bottom_fo_with_bottom
        (classify_fo_with_bottom
           {|
             fo_with_bottom_eqv           := qo_with_bottom_eqv A
           ; fo_with_bottom_lte           := qo_with_bottom_lte A
           ; fo_with_bottom_exists_top_d  := qo_with_bottom_exists_top_d A
           ; fo_with_bottom_exists_bottom := qo_with_bottom_exists_bottom A
           ; fo_with_bottom_certs        :=
               {|
                 fo_congruence      := qo_congruence P
               ; fo_reflexive       := qo_reflexive P
               ; fo_transitive      := qo_transitive P
               ; fo_antisymmetric_d := qo_antisymmetric_d P
               ; fo_total           := Assert_Total 
               ; fo_trivial_d       := qo_trivial_d P
               |}
           ; fo_with_bottom_ast           := qo_with_bottom_ast A
           |}
        )
  end. 

Definition classify_po {S : Type} (A : @po S) : @below_po S :=
match po_exists_bottom_d A with 
| Certify_Exists_Bottom b =>
             Below_po_po_with_bottom (
                  classify_po_with_bottom 
                    {|
                      po_with_bottom_eqv           := po_eqv A
                    ; po_with_bottom_lte           := po_lte A
                    ; po_with_bottom_exists_top_d  := po_exists_top_d A
                    ; po_with_bottom_exists_bottom := Assert_Exists_Bottom b
                    ; po_with_bottom_certs         := po_certs A 
                    ; po_with_bottom_ast           := po_ast A
                    |})
| _ => Below_po_top A
end.  

Definition classify_fo {S : Type} (A : @fo S) : @below_fo S :=
match fo_exists_bottom_d A with 
| Certify_Exists_Qo_Bottom b =>
             Below_fo_fo_with_bottom (
                  classify_fo_with_bottom 
                    {|
                      fo_with_bottom_eqv           := fo_eqv A
                    ; fo_with_bottom_lte           := fo_lte A
                    ; fo_with_bottom_exists_top_d  := fo_exists_top_d A
                    ; fo_with_bottom_exists_bottom := Assert_Exists_Qo_Bottom b
                    ; fo_with_bottom_certs         := fo_certs A 
                    ; fo_with_bottom_ast           := fo_ast A
                    |})
| _ => Below_fo_top A
end.  

  
Definition classify_qo {S : Type} (A : @qo S) : @below_qo S :=
let P := qo_certs A in
match qo_antisymmetric_d P, qo_total_d P with 
| Certify_Antisymmetric, Certify_Not_Total p  =>
           Below_qo_po (
                  classify_po
                    {|
                      po_eqv           := qo_eqv A
                    ; po_lte           := qo_lte A
                    ; po_exists_top_d  :=
                      (* this should be a function .... *) 
                      match qo_exists_top_d A with
                      | Certify_Exists_Qo_Top t => Certify_Exists_Top t
                      | Certify_Not_Exists_Qo_Top => Certify_Not_Exists_Top 
                      end 
                    ; po_exists_bottom_d :=
                      (* this should be a function .... *) 
                      match qo_exists_bottom_d A with
                      | Certify_Exists_Qo_Bottom t => Certify_Exists_Bottom t
                      | Certify_Not_Exists_Qo_Bottom => Certify_Not_Exists_Bottom 
                      end 
                    ; po_certs        :=
                        {|
                          po_congruence     := qo_congruence P
                        ; po_reflexive      := qo_reflexive P
                        ; po_transitive     := qo_transitive P
                        ; po_antisymmetric  := Assert_Antisymmetric 
                        ; po_not_total      := Assert_Not_Total p 
                        |}
                    ; po_ast           := qo_ast A
                    |})
| _, Certify_Total => 
    Below_qo_fo (
        classify_fo 
          {|
            fo_eqv           := qo_eqv A
          ; fo_lte           := qo_lte A
          ; fo_exists_top_d  := qo_exists_top_d A
          ; fo_exists_bottom_d := qo_exists_bottom_d A
          ; fo_certs         :=
              {|
                fo_congruence      := qo_congruence P
              ; fo_reflexive       := qo_reflexive P
              ; fo_transitive      := qo_transitive P
              ; fo_antisymmetric_d := qo_antisymmetric_d P
              ; fo_total           := Assert_Total 
              ; fo_trivial_d       := qo_trivial_d P
              |}
          ; fo_ast           := qo_ast A
          |})
| _, _ => match qo_exists_bottom_d A with
          | Certify_Exists_Qo_Bottom b  => Below_qo_qo_with_bottom (
                           Below_qo_with_bottom_top
                             {|
                               qo_with_bottom_eqv           := qo_eqv A
                             ; qo_with_bottom_lte           := qo_lte A
                             ; qo_with_bottom_exists_top_d  := qo_exists_top_d A
                             ; qo_with_bottom_exists_bottom := Assert_Exists_Qo_Bottom b
                             ; qo_with_bottom_certs         := P 
                             ; qo_with_bottom_ast           := qo_ast A
                             |}
                         ) 
          | _       => Below_qo_top A                                 
          end
end.


End MCAS.

Section Verify.
  Variable (S : Type).

  Lemma correct_classify_po_with_bottom (s : A_po_with_bottom S) : 
  classify_po_with_bottom (A2C_po_with_bottom s)
  =
  A2C_below_po_with_bottom (A_classify_po_with_bottom s).
  Proof. destruct s. simpl. reflexivity. Qed. 

  Lemma correct_classify_fo_with_bottom (s : A_fo_with_bottom S) : 
  classify_fo_with_bottom (A2C_fo_with_bottom s)
  =
  A2C_below_fo_with_bottom (A_classify_fo_with_bottom s).
  Proof. destruct s. simpl. reflexivity. Qed. 
  
  Lemma correct_classify_po (s : A_po S) : 
  classify_po (A2C_po s)
  =
  A2C_below_po (A_classify_po s).
  Proof. destruct s;
         unfold A_classify_po, classify_po, A2C_below_po, A2C_po; simpl. 
         destruct A_po_exists_bottom_d as [[b bot] | nbot]; simpl. 
         - rewrite correct_classify_po_with_bottom.
           reflexivity. 
         - reflexivity. 
  Qed.

  Lemma correct_classify_fo (s : A_fo S) : 
  classify_fo (A2C_fo s)
  =
  A2C_below_fo (A_classify_fo s).
  Proof. destruct s;
         unfold A_classify_fo, classify_fo, A2C_below_fo, A2C_fo; simpl. 
         destruct A_fo_exists_bottom_d as [[b bot] | nbot]; simpl. 
         - rewrite correct_classify_fo_with_bottom.
           reflexivity. 
         - reflexivity. 
  Qed.
  

Lemma correct_classify_qo (A : A_qo S) : 
  classify_qo (A2C_qo A)
  =
  A2C_below_qo (A_classify_qo A).
Proof. destruct A; destruct A_qo_proofs;
       unfold classify_qo, A_classify_qo,  A2C_below_qo, A2C_qo; simpl. 
       destruct A_qo_antisymmetric_d as [antiP | [[s1 s2] [I J]]];
       destruct A_qo_total_d as [tot | [[s3 s4] [E F]]];
       destruct A_qo_exists_top_d as [[t [A B]] | ntop];
       destruct A_qo_exists_bottom_d as [[b [C D]] | nbot]; simpl; 
         try reflexivity. 
Qed.

End Verify. 
