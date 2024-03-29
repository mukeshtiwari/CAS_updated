open Cas
open Describe
       
(* utility function *)
let rec compute_pair_gen (l : 'a list) (m : 'b list) : ('a * 'b) list = 
  match l with
  | [] -> []
  | h :: t -> (List.map (fun x -> (h, x)) m) @ (compute_pair_gen t m)

let compute_pair l = compute_pair_gen l l

let enumerate_matrix_indicies n = compute_pair (List.rev (list_enum n));;  

let list_sq_matrix m =
  let mk_trip (x, y) = (x, y, m.sqm_functional_matrix x y) 
  in List.map mk_trip (enumerate_matrix_indicies m.sqm_size);;

let print_sq_matrix string_of_elem m =
  let print_trip (x, y) =
    let x_str = string_of_int x in
    let y_str = string_of_int y in
    let v_str = string_of_elem (m.sqm_functional_matrix x y) in 
    let trip_str = "(" ^ x_str ^ ", " ^ y_str ^ "): " ^ v_str ^ "\n"
    in print_string trip_str 
  in List.iter print_trip (enumerate_matrix_indicies m.sqm_size);;


let print_solution alg = print_sq_matrix (fun x -> data_to_string Ascii (get_data alg x));; 

  
let update_square_matrix (f : int -> int -> 'a) 
  ((u, v, w) : int * int * 'a) : int -> int -> 'a =
  fun c d -> if c = u && d = v then w else f c d


let rec massage_adj_list (l : (int * (int * 'a) list) list) 
  : (int * int * 'a) list = 
  match l with
  | [] -> []
  | (u, lu) :: ut -> (List.map (fun (x, y) -> (u, x, y)) lu) @  
    massage_adj_list ut

(* end of utility function *)


let fetch_zero_and_one_from_algebra (alg : 'a bs_mcas) = 
  let b = bs_mcas_cast_up alg in
  match b with
  | BS_Error l -> errors (List.map char_list_to_string l)
  | BS_bs a ->
     (*     let bsP = a.bs_certs in *) 
     let id_annP = a.bs_id_ann_certs in
     (match id_annP.id_ann_plus_times_d with
     | Id_Ann_Cert_Equal zero -> 
        (match id_annP.id_ann_times_plus_d with
          | Id_Ann_Cert_Equal one -> (zero, one)
          | _ -> error "fetch_zero_and_one_from_algebra : expecting a one")
     | _ -> error "fetch_zero_and_one_from_algebra : expecting a zero")
  | _  -> error "fetch_zero_and_one_from_algebra : internal error"

let square_matrix_from_adj_list' (n : int) (l : (int * (int * 'a) list) list) (alg : 'a bs_mcas)
  : 'a square_matrix =
  {
    sqm_size = n;
    sqm_functional_matrix = 
      (let (zero, one) = fetch_zero_and_one_from_algebra alg in 
      List.fold_left 
        update_square_matrix 
        (fun c d -> if c = d then one else zero) 
        (massage_adj_list l))
  }

type 'a adjacency_list = { adj_size : int; adj_list : (int * (int * 'a) list) list }  ;;     

let square_matrix_from_adj_list algebra adjl =
     square_matrix_from_adj_list' adjl.adj_size adjl.adj_list algebra;; 
					       

type algorithm =  Matrix_power | Not_implemented_yet


let matrix_solver (algo : algorithm) (alge : 'a bs_mcas) :
      (int -> int -> 'a Cas.square_matrix -> 'a Cas.square_matrix,
       char list list) Cas.sum =
  match algo with
  | Matrix_power -> bs_instantiate_matrix_exp_square_matrix alge 
  | _ -> error "matrix_solver : algorithm not implemented yet"

type 'a algorithm_instance =
 | Matrix_Power_Instance of ('a bs_mcas) * (int -> 'a square_matrix -> 'a square_matrix)
 | Another_Instance of ('a bs_mcas) * ('a square_matrix -> 'a square_matrix);;  
  
let instantiate_algorithm algebra algo = 
   match matrix_solver algo algebra with
   | Inl mf -> Matrix_Power_Instance (algebra, fun n -> mf n (n-1))  
   | Inr l -> errors ("Your algebra does not meet the requirements of this algorithm" :: (List.map char_list_to_string l));;

let bs_adj_list_solver alg adjl =
  match instantiate_algorithm alg Matrix_power with
  | Matrix_Power_Instance(algebra, mf ) ->
     let sqm = square_matrix_from_adj_list algebra adjl in 
     mf sqm.sqm_size sqm 
  | _ -> error ("mk_adj_list_solver : internal error");; 
  
(* 
In the future, we want 
'a Cas.square_matrix -> 'a Cas.square_matrix to be an abstract data type 
because we will more algorithms, e.g., Dijkstra, Floyd Warshall, 
solver for X = A * X + B, etc.
*)
