
open Cas;;
open Describe;;
open Matrix_solver;;

(* 

Experiments with a generalized Martelli combinator: 

   minset_lift_union (S, <=, (x)) = (P(S), (+), (x')) 
   where 
   (+)  = min(<=, lift(x)) 
   (x') = min(<=, union)
   That is, 
   X (+) Y = min(<=, {x (x) y | x in X, y in Y}
   X (x') Y = min(<=, X union Y)

   NOTE: The construction (currently) requires (x) to be commutative, idempotent, and not selective. 

A*[i,j] = (+)_{p in P(i,j)} w(p) 
        = (+)_{p in P(i,j)} min(<=, U_{e in p} w(e))
        = (+)_{p in {p_1, .... p_k}} min(<=, U_{e in p} w(e))
        = min(<=, U_{e in p_1} w(e)) (+) ... (+) min(<=, U_{e in p_k} w(e))
        = (U_{e in p_1} w(e)) (+) ... (+) (U_{e in p_k} w(e))
        = min(<=, {w(e_1) (x) w(e_2) ... (x) w(e_k) | e_1 in p_1, ... e_k in p_k})


   This is more general than Martelli's semiring where 
   A*[i,j] is the set of all minimal cut-sets that disconnect i and j. 

   To reconstruct martelli: 
   1) Note that A subset_eq B iff B = A union B (the right-order wrt union), 
      and A subset_eq B iff A = A intersect B (the left-order wrt intersect) 
      So, start with (P_f(S), intersect, union) 
      so, (+) = intersect, (x) = union. 
   2) construct an order-semigroup (os) as follows: 
       os_from_bs_left (P(S), intersect, union) = (P(S), subset_eq, union). 
   3) Let (P(P(S)), (+), (x')) = minset_lift_union (P(S), subset_eq, union)
   where 
   (+)  = min(subset_eq, lift(union)) 
   (x') = min(subset_eq, union)
   That is, 
   X (+) Y  = min(subset_eq, {x union y | x in X, y in Y}
   X (x') Y = min(subset_eq, X union Y)
   4) Finally, what is S?  It is S = E, the arc-set for the directed graph G = (V, E). 
      w(i, j) = {{(i, j)}}, or w(e) = {{e}}, for e in E. 

From above 

A*[i,j] = min(<=, { w(e_1) (x) w(e_2) ... (x) w(e_k) | e_1 in p_1, ... e_k in p_k}
        = min(subset_eq, { {{e_1}} union {{e_2}} ... union {{e_k}} | e_1 in p_1, ... e_k in p_k}
        = min(subset_eq, { {{e_1, e_2, ... e_k}} | e_1 in p_1, ... e_k in p_k}
*)   

let eqv_edge = mcas_eqv_product mcas_eqv_eq_nat mcas_eqv_eq_nat;;
let bs_edge_sets_intersect_union = mcas_bs_add_zero (mcas_bs_intersect_union eqv_edge) infinity;;
let os_edge_sets_intersect_union = mcas_os_from_bs_left bs_edge_sets_intersect_union;;
let martelli = mcas_minset_lift_union os_edge_sets_intersect_union;;


let martelli_solver = instantiate_algorithm martelli Matrix_power;; 

let martelli_solve_adj_list adjl =
  match martelli_solver with
  | Matrix_Power_Instance(algebra, mf ) -> 
    let sqm = square_matrix_from_adj_list algebra adjl 
    in mf sqm.sqm_size sqm 
  | _ -> error "martelli_solve_adj_list : internal error";; 

let mt_w i j = [Inr [(i, j)]] ;;

(*       
    0 ------> 3
    |      /  |
    |     /   | 
    |    /    |
    \/ \/    \/
     1 --- -> 2
         
*) 
  

let martelli_adj_1 = 
  { adj_size = 4;
    adj_list = 
  [
    (0, [(1, mt_w 0 1); (3, mt_w 0 3)]);
    
    (1, [(2, mt_w 1 2)]);
    
    (3, [(1, mt_w 3 1); (2, mt_w 3 2)])
  ]};; 

let martelli_sol_1 = martelli_solve_adj_list martelli_adj_1;; 

(*

print_solution martelli martelli_sol_1;; 
(0, 0): []
(0, 1): [inr({(0, 3), (0, 1)}), inr({(3, 1), (0, 1)})]
(0, 2): [inr({(0, 3), (0, 1)}), inr({(0, 3), (1, 2)}), inr({(3, 1), (3, 2), (0, 1)}), inr({(3, 2), (1, 2)})]
(0, 3): [inr({(0, 3)})]
(1, 0): [inr({})]
(1, 1): []
(1, 2): [inr({(1, 2)})]
(1, 3): [inr({})]
(2, 0): [inr({})]
(2, 1): [inr({})]
(2, 2): []
(2, 3): [inr({})]
(3, 0): [inr({})]
(3, 1): [inr({(3, 1)})]
(3, 2): [inr({(3, 2), (3, 1)}), inr({(3, 2), (1, 2)})]
(3, 3): []
 *)   


(*       
    0 ------ 3
    |      /  |
    |     /   | 
    |    /    |
    |   /     |
    |  /      |	  
    1 ------- 2
*) 
let martelli_adj_2 = 
  { adj_size = 4;
    adj_list = 
  [
    (0, [(1, mt_w 0 1); (3, mt_w 0 3)]);
    
    (1, [(0, mt_w 1 0); (2, mt_w 1 2); (3, mt_w 1 3)]);

    (2, [(1, mt_w 2 1); (3, mt_w 2 3)]);    
    
    (3, [(0, mt_w 3 0); (1, mt_w 3 1); (2, mt_w 3 2)])
  ]};; 

let martelli_sol_2 = martelli_solve_adj_list martelli_adj_2;; 

(*

print_solution martelli martelli_sol_2
  ;;
(0, 0): []
(0, 1): [inr({(0, 3), (0, 1)}), inr({(3, 2), (3, 1), (0, 1)}), inr({(2, 1), (3, 1), (0, 1)})]
(0, 2): [inr({(0, 3), (0, 1)}), inr({(1, 3), (0, 3), (1, 2)}), inr({(3, 1), (3, 2), (0, 1)}), inr({(3, 2), (1, 2)})]
(0, 3): [inr({(0, 1), (0, 3)}), inr({(1, 2), (1, 3), (0, 3)}), inr({(2, 3), (1, 3), (0, 3)})]
(1, 0): [inr({(1, 2), (1, 3), (1, 0)}), inr({(2, 3), (1, 3), (1, 0)}), inr({(3, 0), (1, 0)})]
(1, 1): []
(1, 2): [inr({(1, 3), (1, 2), (1, 0)}), inr({(1, 3), (0, 3), (1, 2)}), inr({(3, 2), (1, 2)})]
(1, 3): [inr({(1, 2), (1, 3), (1, 0)}), inr({(1, 2), (1, 3), (0, 3)}), inr({(2, 3), (1, 3), (1, 0)}), inr({(2, 3), (1, 3), (0, 3)})]
(2, 0): [inr({(2, 3), (2, 1)}), inr({(2, 3), (1, 3), (1, 0)}), inr({(3, 1), (3, 0), (2, 1)}), inr({(3, 0), (1, 0)})]
(2, 1): [inr({(2, 3), (2, 1)}), inr({(3, 0), (3, 1), (2, 1)}), inr({(0, 1), (3, 1), (2, 1)})]
(2, 2): []
(2, 3): [inr({(2, 3), (2, 1)}), inr({(2, 3), (1, 3), (1, 0)}), inr({(2, 3), (1, 3), (0, 3)})]
(3, 0): [inr({(3, 2), (3, 1), (3, 0)}), inr({(2, 1), (3, 1), (3, 0)}), inr({(1, 0), (3, 0)})]
(3, 1): [inr({(3, 2), (3, 1), (3, 0)}), inr({(3, 2), (3, 1), (0, 1)}), inr({(2, 1), (3, 1), (3, 0)}), inr({(2, 1), (3, 1), (0, 1)})]
(3, 2): [inr({(3, 2), (3, 1), (3, 0)}), inr({(3, 1), (3, 2), (0, 1)}), inr({(3, 2), (1, 2)})]
(3, 3): [] 

 *)

 (* try sp lex martelli

        2
    0 ------ 3
    |      /  |
    |     /   | 
  1 |   1/    | 1
    |   /     |
    |  /      |	  
    1 ------- 2
        2
*)

let mt2_w d i j = Inr (d, mt_w i j) ;; 

let martelli_adj_3 = 
  { adj_size = 4;
    adj_list = 
  [
    (0, [(1, mt2_w 1 0 1); (3, mt2_w 2 0 3)]);
    
    (1, [(0, mt2_w 1 1 0); (2, mt2_w 2 1 2); (3, mt2_w 1 1 3)]);

    (2, [(1, mt2_w 2 2 1); (3, mt2_w 1 2 3)]);    
    
    (3, [(0, mt2_w 2 3 0); (1, mt2_w 1 3 1); (2, mt2_w 1 3 2)])
  ]};; 


let sp_lex_martelli = mcas_bs_add_zero (mcas_bs_llex_product mcas_min_plus martelli) infinity;; 
 
let sp_lex_martelli_solver = instantiate_algorithm sp_lex_martelli Matrix_power;; 

let sp_lex_martelli_solve_adj_list adjl =
  match sp_lex_martelli_solver with
  | Matrix_Power_Instance(algebra, mf ) -> 
    let sqm = square_matrix_from_adj_list algebra adjl 
    in mf sqm.sqm_size sqm 
  | _ -> error "martelli_solve_adj_list : internal error";; 


let sp_lex_martelli_sol_3 = sp_lex_martelli_solve_adj_list martelli_adj_3;;

(*
print_solution sp_lex_martelli sp_lex_martelli_sol_3;; 
 (0, 0): inr((0, []))
(0, 1): inr((1, [inr({(0, 1)})]))
(0, 2): inr((3, [inr({(0, 3), (0, 1)}), inr({(1, 3), (0, 3), (1, 2)}), inr({(3, 2), (0, 1)}), inr({(3, 2), (1, 2)})]))
(0, 3): inr((2, [inr({(0, 1), (0, 3)}), inr({(1, 3), (0, 3)})]))
(1, 0): inr((1, [inr({(1, 0)})]))
(1, 1): inr((0, []))
(1, 2): inr((2, [inr({(1, 3), (1, 2)}), inr({(3, 2), (1, 2)})]))
(1, 3): inr((1, [inr({(1, 3)})]))
(2, 0): inr((3, [inr({(2, 3), (2, 1)}), inr({(2, 3), (1, 0)}), inr({(3, 1), (3, 0), (2, 1)}), inr({(3, 0), (1, 0)})]))
(2, 1): inr((2, [inr({(2, 3), (2, 1)}), inr({(3, 1), (2, 1)})]))
(2, 2): inr((0, []))
(2, 3): inr((1, [inr({(2, 3)})]))
(3, 0): inr((2, [inr({(3, 1), (3, 0)}), inr({(1, 0), (3, 0)})]))
(3, 1): inr((1, [inr({(3, 1)})]))
(3, 2): inr((1, [inr({(3, 2)})]))
(3, 3): inr((0, []))

*) 


(* Now, an experiment with a generalized version 

   Minimal cutsets can explode exponentially in size. 
   However, there are applications of the generalized 
   martelli semiring that do not.  

   Suppose our network relies on 3 resources R = {1, 2, 3}. 
   That is, every arc in the graph is assigned some subset of 
   R.  For example,  w(i,j) = {{1,3}}, this means that if both 
   resources 1 and 3 fail, then this link will fail. 
   If w(i, j) = {{}}, then the link does not depend on any 
   of the resources in R. 
   
   Examples of resources:
   1) a tunnel in Baltimore 
   2) a power station 
   3) the lack of a flood. 
   4) a software/hardware version 
   ... 

   Now, when X in A*[i,j], then we can call X a "shared risk group" for 
   the connectivity of i and j.  That is, if the resources of X fail, 
   then the path can fail. 
*)
let bs_nat_intersect_union = mcas_bs_add_zero (mcas_bs_intersect_union mcas_eqv_eq_nat) infinity;;
let os_nat_sets_intersect_union = mcas_os_from_bs_left bs_nat_intersect_union;;
let risk_groups = mcas_minset_lift_union os_nat_sets_intersect_union;;
let risk_groups_solver = instantiate_algorithm risk_groups Matrix_power;; 

let risk_groups_solve_adj_list adjl =
  match risk_groups_solver with
  | Matrix_Power_Instance(algebra, mf ) -> mf (square_matrix_from_adj_list algebra adjl)
  | _ -> error "martelli_solve_adj_list : internal error";; 

let rg_w i j w = [Inr w] ;;

(*      {3}
    0 ------ 3
    |      /  |
    |     /   | 
{1} |    /    | {2, 3} 
    |   /     |
    |  /      |	  
    1 <-------2
       {1, 3}
      -------> 
        {2}
 *) 
  

let risk_groups_adj_1 = 
  { adj_size = 4;
    adj_list = 
  [
    (0, [(1, rg_w 0 1 [1]); (3, rg_w 0 3 [3])]);
    
    (1, [(0, rg_w 1 0 [2]); (2, rg_w 1 2 [2]); (3, rg_w 1 3 [2])]);

    (2, [(1, rg_w 2 1 [1;3]); (3, rg_w 2 3 [2;3])]);    
    
    (3, [(0, rg_w 3 0 [1]); (1, rg_w 3 1 [1]); (2, rg_w 3 2 [1])])
  ]};; 

let risk_groups_sol_1 = risk_groups_solve_adj_list risk_groups_adj_1;; 
  
(*
list_sq_matrix risk_groups_sol_1;; 

- : (int * int * int Cas.finite_set Cas.with_constant Cas.finite_set) list =
[
(0, 0, []); 
(0, 1, [Inr [1]]); 
(0, 2, [Inr [2; 3]; Inr [1]]);
(0, 3, [Inr [2; 3]; Inr [1; 3]]); 
(1, 0, [Inr [2]]); 
(1, 1, []);
(1, 2, [Inr [2]]); 
(1, 3, [Inr [2]]);
(2, 0, [Inr [2; 1]; Inr [2; 3]; Inr [3; 1]]); 
(2, 1, [Inr [3; 1]]);
(2, 2, []); 
(2, 3, [Inr [2; 3]]); 
(3, 0, [Inr [1]]); 
(3, 1, [Inr [1]]);
(3, 2, [Inr [1]]); 
(3, 3, [])]
 *)


