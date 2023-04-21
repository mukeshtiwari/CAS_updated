Require Import
  List
  Coq.Strings.String. 
Import ListNotations. 

From CAS Require Import
  coq.common.compute
  coq.algorithms.dijkstra.general
  coq.eqv.add_constant
  coq.eqv.sum
  coq.sg.add_id
  coq.sg.add_ann
  coq.sg.plus.



Section Testing.
  Close Scope nat_scope.
  Definition S := cas_constant + nat.
  Definition L := cas_constant + nat.   
  Open Scope nat_scope.
  (*************** TESTING 1, 2, 3, ... *********************

  From https://en.wikipedia.org/wiki/Dijkstra%27s_algorithm#/media/File:Dijkstra_Animation.gif
  (with node number-1 in order to start at 0) 


              ----- 4 ---- 
             /            \
           9/              \6
           /    2       11  \
          5---------2 -------3 
           \       /  \     /
          14\    9/    \10 /15 
             \   /      \ / 
               0---------1 
                    7
  *)

  Definition inf :=
    {|
      constant_ascii := "INF"
    ; constant_latex := "\\infty" 
    |}.


  Definition eq := brel_sum brel_constant brel_eq_nat.
  Definition min' := bop_add_id bop_min inf.
  Definition plus' := bop_add_ann bop_plus inf.   
  Definition i' := 0.
  Definition n' := 6. 
  Definition m' : Node -> Node -> L :=
    λ i, λ j,
    match i, j with
    | 0, 0 => inr 0
    | 0, 1 => inr 7
    | 0, 2 => inr 9
    | 0, 5 => inr 14
    | 1, 1 => inr 0
    | 1, 0 => inr 7                  
    | 1, 2 => inr 10
    | 1, 3 => inr 15
    | 2, 2 => inr 0                  
    | 2, 0 => inr 9
    | 2, 1 => inr 10
    | 2, 3 => inr 11
    | 2, 5 => inr 2
    | 3, 3 => inr 0                                    
    | 3, 1 => inr 15
    | 3, 2 => inr 11
    | 3, 4 => inr 6
    | 4, 4 => inr 0                                                      
    | 4, 3 => inr 6
    | 4, 5 => inr 9
    | 5, 5 => inr 0                                                      
    | 5, 2 => inr 2                                
    | 5, 4 => inr 9              
    | _, _ => inl inf
    end. 

  Definition step := dijkstra_one_step S L eq min' plus' m'.   
  Definition s0 := initial_state S L (inr 0) plus' m' n' 0.
  Definition s1 := step s0.
  Definition s2 := step s1.
  Definition s3 := step s2.
  Definition s4 := step s3.
  Definition s5 := step s4.     
  Definition s6 := step s5.
  
  Compute s0. 
  (*
     = {|
         visited := [(inr 0, 0)];
         estimated :=
           [(inr 14, 5);
           (inl {| constant_ascii := "INF"; constant_latex := "\\infty" |},
           4);
           (inl {| constant_ascii := "INF"; constant_latex := "\\infty" |},
           3); (inr 9, 2); (inr 7, 1)]
       |}
 *) 
  Compute s1. 
  (*
     = {|
         visited := [(inr 7, 1); (inr 0, 0)];
         estimated :=
           [(inr 9, 2); (inr 14, 5); (inr 22, 3);
           (inl {| constant_ascii := "INF"; constant_latex := "\\infty" |},
           4)]
       |}

  *) 
  Compute s2. 
  (*
     = {|
         visited := [(inr 9, 2); (inr 7, 1); (inr 0, 0)];
         estimated :=
           [(inl {| constant_ascii := "INF"; constant_latex := "\\infty" |},
            4); (inr 20, 3); (inr 11, 5)]
       |}
  *) 
  Compute s3. 
  (*
     = {|
         visited := [(inr 11, 5); (inr 9, 2); (inr 7, 1); (inr 0, 0)];
         estimated := [(inr 20, 3); (inr 20, 4)]
       |}
  *) 
  Compute s4. 
  (*
     = {|
         visited :=
           [(inr 20, 3); (inr 11, 5); (inr 9, 2); (inr 7, 1); (inr 0, 0)];
         estimated := [(inr 20, 4)]
       |}
  *) 
  Compute s5. 
  (*
     = {|
         visited :=
           [(inr 20, 4); (inr 20, 3); (inr 11, 5); 
           (inr 9, 2); (inr 7, 1); (inr 0, 0)];
         estimated := []
       |}
   *)
  Compute s6. 
  (*
     = {|
         visited :=
           [(inr 20, 4); (inr 20, 3); (inr 11, 5); 
           (inr 9, 2); (inr 7, 1); (inr 0, 0)];
         estimated := []
       |}
   *)

End Testing.
