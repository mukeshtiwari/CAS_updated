
open Cas;; 
open Describe;;
open Matrix_solver;; 

(* we need to add a zero to min-plus *)
let mcas_shortest_paths = mcas_bs_add_zero infinity mcas_bs_min_plus;;

(*
 bs_mcas_describe_fully mcas_shortest_paths;;
(S_0, +_0, *_0) = min_plus
where
S_0 = nat
x +_0 y = x min y
x *_0 y = x + y

(S_1, +_1, *_1) = bs_add_zero (S_0, +_0, *_0) INF
where
S_1 = {INF} + S_0
Inr(x) +_1 Inr(y) = Inr(x +_0 y)
Inl(INF) +_1 a = a
a +_1 Inl(INF) = a
Inr(x) *_1 Inr(y) = Inr(x *_0 y)
Inl(INF) *_1 _ = Inl(INF)
_ *_1 Inl(INF) = Inl(INF)
Additive properties:
--------------------
Identity = inl(INF)
Annihilator = inr(0)
Idempotent
Selective 
Not Left Cancellative: 
   inr(0).inr(0) = inr(0)
   inr(0).inl(INF) = inr(0)
   inr(0) <> inl(INF)
Not Left Constant: 
   inl(INF).inr(0) = inr(0)
   inl(INF).inl(INF) = inl(INF)
Not Anti Left: 
   inl(INF).inl(INF) = inl(INF)
Not Anti Right: 
   inl(INF).inl(INF) = inl(INF)
Multiplicative properties:
-------------------------
Identity = inr(0)
Annihilator = inl(INF)
Not Idempotent: 
   inr(1).inr(1) = inr(2)
Commutative
Not Selective: 
   inr(1).inr(1) = inr(2)
Not Left Cancellative: 
   inl(INF).inr(0) = inl(INF)
   inl(INF).inr(1) = inl(INF)
   inr(0) <> inr(1)
Not Right Cancellative: 
   inr(0).inl(INF) = inl(INF)
   inr(1).inl(INF) = inl(INF)
   inr(0) <> inr(1)
Not Left Constant: 
   inr(0).inr(0) = inr(0)
   inr(0).inl(INF) = inl(INF)
Not Right Constant: 
   inr(0).inr(0) = inr(0)
   inl(INF).inr(0) = inl(INF)
Not Anti Left: 
   inl(INF).inr(0) = inl(INF)
Not Anti Right: 
   inr(0).inl(INF) = inl(INF)
Not Is Left: 
   inr(0).inl(INF) = inl(INF)
Not Is Right: 
   inl(INF).inr(0) = inl(INF)
Interaction of Additive and Multiplicative operations
-------------------------------------------------------
Left Distributive
Right Distributive 
Left Left Absorptive
Left_Right Absorptive 

 *) 

(*       2 
    0 ------> 1 
    |         |
  1 |         | 2
    |         |
    \/       \/
    2 ------> 3
         1
*) 
let adj_1 = { adj_size = 4;
	      adj_list = [
		          (0, [(1, Inr 2); (2, Inr 1)]);
		          (1, [(3, Inr 2)]);
		          (2, [(3, Inr 1)])
			 ]
			 } ;;
			 
let shortest_paths = cast_bs_mcas_to_selective_path_algebra mcas_shortest_paths;; 
let shortest_path_solver = selective_path_algebra_matrix_solver shortest_paths;;
let (zero, one) = fetch_zero_and_one_from_selective_path_algebra shortest_paths;; 
let mat_1 = square_matrix_from_adj_list (zero, one) adj_1;;
let sol_1 = shortest_path_solver mat_1;; 
(*
list_sq_matrix mat_1;; 

list_sq_matrix mat_1;; 
- : (int * int * int Cas.with_constant) list =
[(0, 0, Inr 0); (0, 1, Inr 2); (0, 2, Inr 1);
 (0, 3,
  Inl
   {constant_ascii = ['I'; 'N'; 'F'];
    constant_latex = ['\\'; 'i'; 'n'; 'f'; 't'; 'y']});
 (1, 0,
  Inl
   {constant_ascii = ['I'; 'N'; 'F'];
    constant_latex = ['\\'; 'i'; 'n'; 'f'p; 't'; 'y']});
 (1, 1, Inr 0);
 (1, 2,
  Inl
   {constant_ascii = ['I'; 'N'; 'F'];
    constant_latex = ['\\'; 'i'; 'n'; 'f'; 't'; 'y']});
 (1, 3, Inr 2);
 (2, 0,
  Inl
   {constant_ascii = ['I'; 'N'; 'F'];
    constant_latex = ['\\'; 'i'; 'n'; 'f'; 't'; 'y']});
 (2, 1,
  Inl
   {constant_ascii = ['I'; 'N'; 'F'];
    constant_latex = ['\\'; 'i'; 'n'; 'f'; 't'; 'y']});
 (2, 2, Inr 0); (2, 3, Inr 1);
 (3, 0,
  Inl
   {constant_ascii = ['I'; 'N'; 'F'];
    constant_latex = ['\\'; 'i'; 'n'; 'f'; 't'; 'y']});
 (3, 1,
  Inl
   {constant_ascii = ['I'; 'N'; 'F'];
    constant_latex = ['\\'; 'i'; 'n'; 'f'; 't'; 'y']});
 (3, 2,
  Inl
   {constant_ascii = ['I'; 'N'; 'F'];
    constant_latex = ['\\'; 'i'; 'n'; 'f'; 't'; 'y']});
 (3, 3, Inr 0)]


*)

  
(*       2 
    0 ------- 1 
    |         |
  1 |         | 2
    |         |
    2 ------- 3
         1
*) 
let adj_2 = { adj_size = 4;
	      adj_list = [
		          (0, [(1, Inr 2); (2, Inr 1)]);
		          (1, [(0, Inr 2); (3, Inr 2)]);
		          (2, [(0, Inr 1); (3, Inr 1)]);
		          (3, [(1, Inr 2); (2, Inr 1)])
			 ]
	    } ;;
let mat_2 = square_matrix_from_adj_list (zero, one) adj_2;;
let sol_2 = shortest_path_solver adj_2;;

(*
list_sq_matrix mat_2;; 
- : (int * int * int Cas.with_constant) list =
[(0, 0, Inr 0); (0, 1, Inr 2); (0, 2, Inr 1);
 (0, 3,
  Inl
   {constant_ascii = ['I'; 'N'; 'F'];
    constant_latex = ['\\'; 'i'; 'n'; 'f'; 't'; 'y']});
 (1, 0, Inr 2); (1, 1, Inr 0);
 (1, 2,
  Inl
   {constant_ascii = ['I'; 'N'; 'F'];
    constant_latex = ['\\'; 'i'; 'n'; 'f'; 't'; 'y']});
 (1, 3, Inr 2); (2, 0, Inr 1);
 (2, 1,
  Inl
   {constant_ascii = ['I'; 'N'; 'F'];
    constant_latex = ['\\'; 'i'; 'n'; 'f'; 't'; 'y']});
 (2, 2, Inr 0); (2, 3, Inr 1);
 (3, 0,
  Inl
   {constant_ascii = ['I'; 'N'; 'F'];
    constant_latex = ['\\'; 'i'; 'n'; 'f'; 't'; 'y']});
 (3, 1, Inr 2); (3, 2, Inr 1); (3, 3, Inr 0)]

list_sq_matrix sol_2;; 
- : (int * int * int Cas.with_constant) list =
[(0, 0, Inr 0); (0, 1, Inr 2); (0, 2, Inr 1); (0, 3, Inr 2); (1, 0, Inr 2);
 (1, 1, Inr 0); (1, 2, Inr 3); (1, 3, Inr 2); (2, 0, Inr 1); (2, 1, Inr 3);
 (2, 2, Inr 0); (2, 3, Inr 1); (3, 0, Inr 2); (3, 1, Inr 2); (3, 2, Inr 1);
 (3, 3, Inr 0)]
 *)   



    (*

 dijkstra_solver shortest_paths mat_2 0;;    
- : (Cas.node * int Cas.with_constant) list =
[(3, Inr 2); (2, Inr 1); (1, Inr 2); (0, Inr 0)]
# 
  dijkstra_solver shortest_paths mat_2 1;; 
- : (Cas.node * int Cas.with_constant) list =
[(3, Inr 2); (2, Inr 3); (1, Inr 0); (0, Inr 2)]
# dijkstra_solver shortest_paths mat_2 2;; 
- : (Cas.node * int Cas.with_constant) list =
[(3, Inr 1); (2, Inr 0); (1, Inr 3); (0, Inr 1)]
# dijkstra_solver shortest_paths mat_2 3;; 
- : (Cas.node * int Cas.with_constant) list =
[(3, Inr 0); (2, Inr 1); (1, Inr 2); (0, Inr 2)]
# 
     *) 

