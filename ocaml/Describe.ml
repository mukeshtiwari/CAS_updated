open Cas
       
exception Error of string list 

let error s = raise (Error [s])
let errors sl = raise (Error sl) 		    
       
let nl s = s ^ "\n"       

let char_list_to_string cl = String.concat "" (List.map (String.make 1) cl)

let print_error_list cll =
   let sl = List.map char_list_to_string cll in 
   (print_string "**** Errors *****\n";
    print_string (String.concat "\n" sl);
    print_string "\n")

let rec from_to start finish =
  if start > finish
  then []
  else start :: (from_to (start + 1) finish);;

let string_to_char_list s = List.map (String.get s) (from_to 0 ((String.length s) - 1));;

let make_constant' s1 s2 = make_constant (string_to_char_list s1) (string_to_char_list s2);;

let infinity = make_constant' "INF"  "\\infty";;
let self = make_constant' "SELF"  "\\bot";;

let get_plus bs = (cast_up_bs bs).bs_plus;; 

let get_times bs = (cast_up_bs bs).bs_times;; 

let get_eq bs = (cast_up_bs bs).bs_eqv.eqv_eq;;

let get_data bs = (cast_up_bs bs).bs_eqv.eqv_data;; 

type string_type = Ascii | Latex

let rec data_to_string st = function 
| DATA_nat n         -> string_of_int n 
| DATA_bool b        -> string_of_bool b 
| DATA_string l      -> String.concat "" (List.map (String.make 1) l)
| DATA_constant c    -> String.concat "" (List.map (String.make 1) (c.Cas.constant_ascii))
| DATA_pair (d1, d2) -> (match st with
              		| Ascii -> "(" ^ (data_to_string st d1) ^  ", " ^ (data_to_string st d2) ^ ")"
			| Latex -> "(" ^ (data_to_string st d1) ^  ", " ^ (data_to_string st d2) ^ ")" )
| DATA_inl d         -> (match st with
			 | Ascii -> "inl(" ^ (data_to_string st d) ^ ")"
			 | Latex -> "\\inl{" ^ (data_to_string st d) ^ "}")
| DATA_inr d         -> (match st with
			 | Ascii -> "inr(" ^ (data_to_string st d) ^ ")"
			 | Latex -> "\\inr{" ^ (data_to_string st d) ^ "}" )
| DATA_list l        -> (match st with
			 | Ascii -> "[" ^ (String.concat ", " (List.map (data_to_string st) l)) ^ "]"
			 | Latex -> "[" ^ (String.concat ", " (List.map (data_to_string st) l)) ^ "]")
| DATA_set l         -> (match st with
			 | Ascii -> "{" ^ (String.concat ", " (List.map (data_to_string st) l)) ^ "}"	 
                         | Latex -> "\\{" ^ (String.concat ", " (List.map (data_to_string st) l)) ^ "\\}")
| DATA_ascii c       -> "DATA_ascii : Not Yet Implemented"
(*| DATA_square_matrix _ -> "DATA_square_matrix : Not Yet Implemented"*) 
			     
let rec data_to_ascii = data_to_string Ascii
let rec data_to_latex = data_to_string Latex 
			     

let rec unfold_eqv_ast = function 
| Ast_eqv_ascii  -> "ascii" 
| Ast_eqv_bool   -> "bool" 
| Ast_eqv_nat    -> "nat" 
| Ast_eqv_matrix -> "matrix?" 
| Ast_eqv_list eqv -> "(" ^ (unfold_eqv_ast eqv) ^ ") list"
| Ast_eqv_set eqv -> "(" ^ (unfold_eqv_ast eqv) ^ ") set"
| Ast_eqv_product (eqv1, eqv2) -> "(" ^ (unfold_eqv_ast eqv1) ^ ") * (" ^ (unfold_eqv_ast eqv2) ^ ")" 
| Ast_eqv_sum (eqv1, eqv2) -> "(" ^ (unfold_eqv_ast eqv1) ^ ") + (" ^ (unfold_eqv_ast eqv2) ^ ")" 
| Ast_eqv_add_constant (c, eqv) -> "{" ^ (char_list_to_string c.constant_ascii) ^ "} + (" ^ (unfold_eqv_ast eqv) ^ ")" 
| Ast_eqv_nat_ceiling n -> "[" ^ (string_of_int n) ^ "]"
| Ast_eqv_minset orsg -> "(" ^ (unfold_or_ast orsg) ^ ") minimal_set"
| Ast_eqv_of_or ord -> "Ast_eqv_of_or ord : Fix me" 
| Ast_eqv_of_sg sg -> "Ast_eqv_of_sg : Fix me"
| Ast_eqv_of_bs gs -> "Ast_eqv_of_bs : Fix me"
| Ast_eqv_of_os os -> "Ast_eqv_of_or : Fix me"
and unfold_or_ast = function 
| Ast_or_nat -> "(nat, <=)"
| Ast_or_bool -> "or_bool : NEEDED?"
| Ast_or_add_bottom (c, ord) -> "add_bottom(" ^ (char_list_to_string c.constant_ascii) ^ "," ^ (unfold_or_ast ord) ^ ")" 
| Ast_or_add_top (c, ord) -> "add_top(" ^ (char_list_to_string c.constant_ascii) ^ "," ^ (unfold_or_ast ord) ^ ")" 
| Ast_or_dual ord -> "dual(" ^ (unfold_or_ast ord) ^ ")" 
| Ast_or_llte sg -> "left_lte_from_sg(" ^ (unfold_sg_ast sg) ^ ")" 
| Ast_or_rlte sg -> "right_lte_from_sg(" ^ (unfold_sg_ast sg) ^ ")" 
| Ast_or_length eqv -> "list_length(" ^ (unfold_eqv_ast eqv) ^ ")" 
| Ast_or_llex (ord1, ord2) -> "order_llex_product(" ^ (unfold_or_ast ord1) ^ ") * (" ^ (unfold_or_ast ord2) ^ ")" 
| Ast_or_product (ord1, ord2) -> "order_product(" ^ (unfold_or_ast ord1) ^ ") * (" ^ (unfold_or_ast ord2) ^ ")" 
| Ast_or_subset eqv -> "or_subset : NEEDED?"
| Ast_or_set eqv -> "or_set : NEEDED?"
| Ast_or_left_sum (ord1, ord2) -> "left_sum(" ^ (unfold_or_ast ord1) ^ ") * (" ^ (unfold_or_ast ord2) ^ ")" 
| Ast_or_right_sum (ord1, ord2) -> "right_sum(" ^ (unfold_or_ast ord1) ^ ") * (" ^ (unfold_or_ast ord2) ^ ")" 
| Ast_or_trivial eqv -> "trivial_order(" ^ (unfold_eqv_ast eqv) ^ ")" 
| Ast_or_of_os os -> "Ast_or_of_os : fix me"
and unfold_sg_ast = function 
| Ast_sg_times -> "(nat, *" ^ ")"
| Ast_sg_plus -> "(nat, +)"
| Ast_sg_or -> "(bool, or)"
| Ast_sg_and -> "(bool, and)"
| Ast_sg_min -> "(nat, min)"
| Ast_sg_max -> "(nat, max)"
| Ast_sg_add_id (c, sg) -> "add_id(" ^ (char_list_to_string c.constant_ascii) ^ ", " ^ (unfold_sg_ast sg) ^ ")"
| Ast_sg_add_ann (c, sg) -> "add_ann(" ^ (char_list_to_string c.constant_ascii) ^ ", " ^ (unfold_sg_ast sg) ^ ")"
| Ast_sg_concat eqv -> "sg_concat(" ^ (unfold_eqv_ast eqv) ^ ")"
| Ast_sg_union eqv -> "sg_union(" ^ (unfold_eqv_ast eqv) ^ ")"
| Ast_sg_intersect eqv -> "sg_intersect(" ^ (unfold_eqv_ast eqv) ^ ")"
| Ast_sg_left eqv -> "sg_left(" ^ (unfold_eqv_ast eqv) ^ ")"
| Ast_sg_right eqv -> "sg_right(" ^ (unfold_eqv_ast eqv) ^ ")"
| Ast_sg_left_sum (sg1, sg2) -> "sg_left_sum(" ^ (unfold_sg_ast sg1) ^ ", " ^ (unfold_sg_ast sg2) ^ ")" 
| Ast_sg_right_sum (sg1, sg2) -> "sg_right_sum(" ^ (unfold_sg_ast sg1) ^ ", " ^ (unfold_sg_ast sg2) ^ ")" 
| Ast_sg_lift sg -> "lift(" ^ (unfold_sg_ast sg) ^ ")"
| Ast_sg_llex (sg1, sg2) -> "sg_llex(" ^ (unfold_sg_ast sg1) ^ ", " ^ (unfold_sg_ast sg2) ^ ")" 
| Ast_sg_product (sg1, sg2) -> "sg_product(" ^ (unfold_sg_ast sg1) ^ ", " ^ (unfold_sg_ast sg2) ^ ")" 
| Ast_sg_minset_lift os -> "sg_minset_lift(" ^ (unfold_os_ast os) ^ ")"
| Ast_sg_minset_union ord -> "sg_minset_union(" ^ (unfold_or_ast ord) ^ ")"
| Ast_sg_plus_of_bs bs -> "Ast_sg_plus_of_bs : fix me" 
| Ast_sg_times_of_bs bs -> "Ast_sg_times_of_bs : fix me" 
| Ast_sg_times_of_os os -> "Ast_sg_times_of_os : fix me" 
and unfold_bs_ast = function 
| Ast_min_plus -> "(nat, min, +)" 
| Ast_max_plus -> "(nat, max, +)" 
| Ast_and_or -> "(bool, and, or)" 
| Ast_or_and -> "(bool, or, and)" 
| Ast_max_min -> "(nat, max, min)" 
| Ast_min_max -> "(nat, min, max)" 
| Ast_bs_add_zero (c, bs) -> "add_zero(" ^ (char_list_to_string c.constant_ascii) ^ ", " ^ (unfold_bs_ast bs) ^ ")"
| Ast_bs_add_one (c, bs) -> "add_one(" ^ (char_list_to_string c.constant_ascii) ^ ", " ^ (unfold_bs_ast bs) ^ ")"
| Ast_bs_product (bs1, bs2) -> "product(" ^ (unfold_bs_ast bs1) ^ ", " ^ (unfold_bs_ast bs2) ^ ")" 
| Ast_bs_llex_product (bs1, bs2) -> "llex_product(" ^ (unfold_bs_ast bs1) ^ ", " ^ (unfold_bs_ast bs2) ^ ")" 
| Ast_bs_union_lift sg -> "union_lift(" ^ (unfold_sg_ast sg) ^ ")"
| Ast_bs_left_sum_right_sum (bs1, bs2) -> "left_sum_right_sum(" ^ (unfold_bs_ast bs1) ^ ", " ^ (unfold_bs_ast bs2) ^ ")" 
| Ast_bs_right_sum_left_sum (bs1, bs2) -> "right_sum_left_sum(" ^ (unfold_bs_ast bs1) ^ ", " ^ (unfold_bs_ast bs2) ^ ")" 
| Ast_bs_left sg  -> "bs_left(" ^ (unfold_sg_ast sg) ^ ")"
| Ast_bs_right sg -> "bs_right(" ^ (unfold_sg_ast sg) ^ ")"
| Ast_union_intersect eqv  -> "union_intersect(" ^ (unfold_eqv_ast eqv) ^ ")" 
| Ast_intersect_union eqv  -> "intersect_union(" ^ (unfold_eqv_ast eqv) ^ ")" 
| Ast_bs_dual bs           -> "dual(" ^ (unfold_bs_ast bs) ^ ")" 
| Ast_minset_lift_union os -> "minset_lift_union(" ^ (unfold_os_ast os) ^ ")"
| Ast_minset_union_lift os -> "minset_union_lift(" ^ (unfold_os_ast os) ^ ")"
| Ast_lift_union sg        -> "lift_union(" ^ (unfold_sg_ast sg) ^ ")"
| Ast_union_lift sg        -> "union_lift(" ^ (unfold_sg_ast sg) ^ ")"
and unfold_os_ast = function 
| Ast_os_from_bs_left bs  -> "os_from_bs_left(" ^ (unfold_bs_ast bs) ^ ")" 
| Ast_os_from_bs_right bs  -> "os_from_bs_right(" ^ (unfold_bs_ast bs) ^ ")" 
| Ast_os_llex_product (os1, os2) -> "os_llex_product(" ^ (unfold_os_ast os1) ^ ", " ^ (unfold_os_ast os2) ^ ")" 
| Ast_os_product (os1, os2) -> "os_product(" ^ (unfold_os_ast os1) ^ ", " ^ (unfold_os_ast os2) ^ ")" 
| Ast_os_add_bottom_id (c, os) -> "os_add_bottom_id(" ^ (char_list_to_string c.constant_ascii) ^ ", " ^ (unfold_os_ast os) ^ ")"
| Ast_os_add_top_ann (c, os) -> "os_add_top_ann(" ^ (char_list_to_string c.constant_ascii) ^ ", " ^ (unfold_os_ast os) ^ ")"
and unfold_ltr_ast = function 
| Ast_ltr_cons eqv  -> "ltr_cons(" ^ (unfold_eqv_ast eqv) ^ ")" 
| Ast_ltr_product (ltr1, ltr2) -> "ltr_product(" ^ (unfold_ltr_ast ltr1) ^ ", " ^ (unfold_ltr_ast ltr2) ^ ")" 
| Ast_ltr_left_sum (ltr1, ltr2) -> "ltr_left_sum(" ^ (unfold_ltr_ast ltr1) ^ ", " ^ (unfold_ltr_ast ltr2) ^ ")" 
| Ast_ltr_right_sum (ltr1, ltr2) -> "ltr_right_sum(" ^ (unfold_ltr_ast ltr1) ^ ", " ^ (unfold_ltr_ast ltr2) ^ ")" 
| Ast_ltr_lift ltr -> "ltr_lift(" ^ (unfold_ltr_ast ltr) ^ ")"
| Ast_ltr_from_sg ltr -> "ltr_from_sg : constructor has wrong type"
| Ast_ltr_with_policy ltr -> "ltr_from_policy : Not Yet Implemented"
and destribe_lstr_ast = function 
| Ast_lstr_product (lstr1, lstr2) -> "lstr_product : Not Yet Implemented"
| Ast_lstr_llex_product (lstr1, lstr2) -> "lstr_product : Not Yet Implemented"
and unfold_lotr_ast = function 
| Ast_lotr_length_cons eqv  -> "length_cons(" ^ (unfold_eqv_ast eqv) ^ ")" 
| Ast_lotr_product (lotr1, lotr2) -> "lotr_product(" ^ (unfold_lotr_ast lotr1) ^ ", " ^ (unfold_lotr_ast lotr2) ^ ")" 
| Ast_lotr_llex_product (lotr1, lotr2) -> "lotr_llex_product(" ^ (unfold_lotr_ast lotr1) ^ ", " ^ (unfold_lotr_ast lotr2) ^ ")" 



				       

let rec describe_eqv_ast = function 
| Ast_eqv_ascii  -> "ascii" 
| Ast_eqv_bool   -> "bool" 
| Ast_eqv_nat    -> "nat" 
| Ast_eqv_matrix -> "matrix?" 
| Ast_eqv_list eqv -> "(" ^ (describe_eqv_ast eqv) ^ ") list"
| Ast_eqv_set eqv -> "(" ^ (describe_eqv_ast eqv) ^ ") set"
| Ast_eqv_product (eqv1, eqv2) -> "(" ^ (describe_eqv_ast eqv1) ^ ") * (" ^ (describe_eqv_ast eqv2) ^ ")" 
| Ast_eqv_sum (eqv1, eqv2) -> "(" ^ (describe_eqv_ast eqv1) ^ ") + (" ^ (describe_eqv_ast eqv2) ^ ")" 
| Ast_eqv_add_constant (c, eqv) -> "{" ^ (char_list_to_string c.constant_ascii) ^ "} + (" ^ (describe_eqv_ast eqv) ^ ")" 
| Ast_eqv_nat_ceiling n -> "[" ^ (string_of_int n) ^ "]"
| Ast_eqv_minset orsg -> "(" ^ (describe_or_ast orsg) ^ ") minimal_set"
| Ast_eqv_of_or ord -> "Ast_eqv_of_or ord : Fix me" 
| Ast_eqv_of_sg sg -> "Ast_eqv_of_sg : Fix me"
| Ast_eqv_of_bs gs -> "Ast_eqv_of_bs : Fix me"
| Ast_eqv_of_os os -> "Ast_eqv_of_or : Fix me"
and describe_or_ast = function 
| Ast_or_nat -> "(nat, <=)"
| Ast_or_bool -> "or_bool : NEEDED?"
| Ast_or_add_bottom (c, ord) -> "add_bottom(" ^ (char_list_to_string c.constant_ascii) ^ "," ^ (describe_or_ast ord) ^ ")" 
| Ast_or_add_top (c, ord) -> "add_top(" ^ (char_list_to_string c.constant_ascii) ^ "," ^ (describe_or_ast ord) ^ ")" 
| Ast_or_dual ord -> "dual(" ^ (describe_or_ast ord) ^ ")" 
| Ast_or_llte sg -> "left_lte_from_sg(" ^ (describe_sg_ast sg) ^ ")" 
| Ast_or_rlte sg -> "right_lte_from_sg(" ^ (describe_sg_ast sg) ^ ")" 
| Ast_or_length eqv -> "list_length(" ^ (describe_eqv_ast eqv) ^ ")" 
| Ast_or_llex (ord1, ord2) -> "order_llex_product(" ^ (describe_or_ast ord1) ^ ") * (" ^ (describe_or_ast ord2) ^ ")" 
| Ast_or_product (ord1, ord2) -> "order_product(" ^ (describe_or_ast ord1) ^ ") * (" ^ (describe_or_ast ord2) ^ ")" 
| Ast_or_subset eqv -> "or_subset : NEEDED?"
| Ast_or_set eqv -> "or_set : NEEDED?"
| Ast_or_left_sum (ord1, ord2) -> "left_sum(" ^ (describe_or_ast ord1) ^ ") * (" ^ (describe_or_ast ord2) ^ ")" 
| Ast_or_right_sum (ord1, ord2) -> "right_sum(" ^ (describe_or_ast ord1) ^ ") * (" ^ (describe_or_ast ord2) ^ ")" 
| Ast_or_trivial eqv -> "trivial_order(" ^ (describe_eqv_ast eqv) ^ ")" 
| Ast_or_of_os os -> "Ast_or_of_os : fix me"
and describe_sg_ast = function 
| Ast_sg_times -> "(nat, *" ^ ")"
| Ast_sg_plus -> "(nat, +)"
| Ast_sg_or -> "(bool, or)"
| Ast_sg_and -> "(bool, and)"
| Ast_sg_min -> "(nat, min)"
| Ast_sg_max -> "(nat, max)"
| Ast_sg_add_id (c, sg) -> "add_id(" ^ (char_list_to_string c.constant_ascii) ^ ", " ^ (describe_sg_ast sg) ^ ")"
| Ast_sg_add_ann (c, sg) -> "add_ann(" ^ (char_list_to_string c.constant_ascii) ^ ", " ^ (describe_sg_ast sg) ^ ")"
| Ast_sg_concat eqv -> "sg_concat(" ^ (describe_eqv_ast eqv) ^ ")"
| Ast_sg_union eqv -> "sg_union(" ^ (describe_eqv_ast eqv) ^ ")"
| Ast_sg_intersect eqv -> "sg_intersect(" ^ (describe_eqv_ast eqv) ^ ")"
| Ast_sg_left eqv -> "sg_left(" ^ (describe_eqv_ast eqv) ^ ")"
| Ast_sg_right eqv -> "sg_right(" ^ (describe_eqv_ast eqv) ^ ")"
| Ast_sg_left_sum (sg1, sg2) -> "sg_left_sum(" ^ (describe_sg_ast sg1) ^ ", " ^ (describe_sg_ast sg2) ^ ")" 
| Ast_sg_right_sum (sg1, sg2) -> "sg_right_sum(" ^ (describe_sg_ast sg1) ^ ", " ^ (describe_sg_ast sg2) ^ ")" 
| Ast_sg_lift sg -> "lift(" ^ (describe_sg_ast sg) ^ ")"
| Ast_sg_llex (sg1, sg2) -> "sg_llex(" ^ (describe_sg_ast sg1) ^ ", " ^ (describe_sg_ast sg2) ^ ")" 
| Ast_sg_product (sg1, sg2) -> "sg_product(" ^ (describe_sg_ast sg1) ^ ", " ^ (describe_sg_ast sg2) ^ ")" 
| Ast_sg_minset_lift os -> "sg_minset_lift(" ^ (describe_os_ast os) ^ ")"
| Ast_sg_minset_union ord -> "sg_minset_union(" ^ (describe_or_ast ord) ^ ")"
| Ast_sg_plus_of_bs bs -> "Ast_sg_plus_of_bs : fix me" 
| Ast_sg_times_of_bs bs -> "Ast_sg_times_of_bs : fix me" 
| Ast_sg_times_of_os os -> "Ast_sg_times_of_os : fix me" 
and describe_bs_ast = function 
| Ast_min_plus -> "(nat, min, +)" 
| Ast_max_plus -> "(nat, max, +)" 
| Ast_and_or -> "(bool, and, or)" 
| Ast_or_and -> "(bool, or, and)" 
| Ast_max_min -> "(nat, max, min)" 
| Ast_min_max -> "(nat, min, max)" 
| Ast_bs_add_zero (c, bs) -> "add_zero(" ^ (char_list_to_string c.constant_ascii) ^ ", " ^ (describe_bs_ast bs) ^ ")"
| Ast_bs_add_one (c, bs) -> "add_one(" ^ (char_list_to_string c.constant_ascii) ^ ", " ^ (describe_bs_ast bs) ^ ")"
| Ast_bs_product (bs1, bs2) -> "product(" ^ (describe_bs_ast bs1) ^ ", " ^ (describe_bs_ast bs2) ^ ")" 
| Ast_bs_llex_product (bs1, bs2) -> "llex_product(" ^ (describe_bs_ast bs1) ^ ", " ^ (describe_bs_ast bs2) ^ ")" 
| Ast_bs_union_lift sg -> "union_lift(" ^ (describe_sg_ast sg) ^ ")"
| Ast_bs_left_sum_right_sum (bs1, bs2) -> "left_sum_right_sum(" ^ (describe_bs_ast bs1) ^ ", " ^ (describe_bs_ast bs2) ^ ")" 
| Ast_bs_right_sum_left_sum (bs1, bs2) -> "right_sum_left_sum(" ^ (describe_bs_ast bs1) ^ ", " ^ (describe_bs_ast bs2) ^ ")" 
| Ast_bs_left sg  -> "bs_left(" ^ (describe_sg_ast sg) ^ ")"
| Ast_bs_right sg -> "bs_right(" ^ (describe_sg_ast sg) ^ ")"
| Ast_union_intersect eqv  -> "union_intersect(" ^ (describe_eqv_ast eqv) ^ ")" 
| Ast_intersect_union eqv  -> "intersect_union(" ^ (describe_eqv_ast eqv) ^ ")" 
| Ast_bs_dual bs           -> "dual(" ^ (describe_bs_ast bs) ^ ")" 
| Ast_minset_lift_union os -> "minset_lift_union(" ^ (describe_os_ast os) ^ ")"
| Ast_minset_union_lift os -> "minset_union_lift(" ^ (describe_os_ast os) ^ ")"
| Ast_lift_union sg        -> "lift_union(" ^ (describe_sg_ast sg) ^ ")"
| Ast_union_lift sg        -> "union_lift(" ^ (describe_sg_ast sg) ^ ")"
and describe_os_ast = function 
| Ast_os_from_bs_left bs  -> "os_from_bs_left(" ^ (describe_bs_ast bs) ^ ")" 
| Ast_os_from_bs_right bs  -> "os_from_bs_right(" ^ (describe_bs_ast bs) ^ ")" 
| Ast_os_llex_product (os1, os2) -> "os_llex_product(" ^ (describe_os_ast os1) ^ ", " ^ (describe_os_ast os2) ^ ")" 
| Ast_os_product (os1, os2) -> "os_product(" ^ (describe_os_ast os1) ^ ", " ^ (describe_os_ast os2) ^ ")" 
| Ast_os_add_bottom_id (c, os) -> "os_add_bottom_id(" ^ (char_list_to_string c.constant_ascii) ^ ", " ^ (describe_os_ast os) ^ ")"
| Ast_os_add_top_ann (c, os) -> "os_add_top_ann(" ^ (char_list_to_string c.constant_ascii) ^ ", " ^ (describe_os_ast os) ^ ")"
and describe_ltr_ast = function 
| Ast_ltr_cons eqv  -> "ltr_cons(" ^ (describe_eqv_ast eqv) ^ ")" 
| Ast_ltr_product (ltr1, ltr2) -> "ltr_product(" ^ (describe_ltr_ast ltr1) ^ ", " ^ (describe_ltr_ast ltr2) ^ ")" 
| Ast_ltr_left_sum (ltr1, ltr2) -> "ltr_left_sum(" ^ (describe_ltr_ast ltr1) ^ ", " ^ (describe_ltr_ast ltr2) ^ ")" 
| Ast_ltr_right_sum (ltr1, ltr2) -> "ltr_right_sum(" ^ (describe_ltr_ast ltr1) ^ ", " ^ (describe_ltr_ast ltr2) ^ ")" 
| Ast_ltr_lift ltr -> "ltr_lift(" ^ (describe_ltr_ast ltr) ^ ")"
| Ast_ltr_from_sg ltr -> "ltr_from_sg : constructor has wrong type"
| Ast_ltr_with_policy ltr -> "ltr_from_policy : Not Yet Implemented"
and destribe_lstr_ast = function 
| Ast_lstr_product (lstr1, lstr2) -> "lstr_product : Not Yet Implemented"
| Ast_lstr_llex_product (lstr1, lstr2) -> "lstr_product : Not Yet Implemented"
and describe_lotr_ast = function 
| Ast_lotr_length_cons eqv  -> "length_cons(" ^ (describe_eqv_ast eqv) ^ ")" 
| Ast_lotr_product (lotr1, lotr2) -> "lotr_product(" ^ (describe_lotr_ast lotr1) ^ ", " ^ (describe_lotr_ast lotr2) ^ ")" 
| Ast_lotr_llex_product (lotr1, lotr2) -> "lotr_llex_product(" ^ (describe_lotr_ast lotr1) ^ ", " ^ (describe_lotr_ast lotr2) ^ ")" 
 

			     


(*
let rec ast_type_to_string st = function 
| Ast_type_bool             -> (match st with
			       | Ascii -> "bool"
                               | Latex -> "bool")		    
| Ast_type_nat              -> (match st with
			       | Ascii -> "int"
                               | Latex -> "int")		    
| Ast_type_list t           -> (match st with
			       | Ascii -> "(" ^ (ast_type_to_string st t) ^ ") list"
                               | Latex -> "(" ^ (ast_type_to_string st t) ^ ") list")		    
| Ast_type_set t            -> (match st with
			       | Ascii -> "(" ^ (ast_type_to_string st t) ^ ") set"
                               | Latex -> "(" ^ (ast_type_to_string st t) ^ ") set")		    
| Ast_type_product (t1, t2) -> (match st with
			       | Ascii -> "(" ^ (ast_type_to_string st t1) ^ " * " ^ (ast_type_to_string st t2) ^ ")"
                               | Latex -> "(" ^ (ast_type_to_string st t1) ^ " * " ^ (ast_type_to_string st t2) ^ ")")		    
| Ast_type_sum (t1, t2)     -> (match st with
			       | Ascii -> "(" ^ (ast_type_to_string st t1) ^ " + " ^ (ast_type_to_string st t2) ^ ")"
                               | Latex -> "(" ^ (ast_type_to_string st t1) ^ " + " ^ (ast_type_to_string st t2) ^ ")")		    
| Ast_type_add_constant (c,t) -> (match st with
			       | Ascii ->  "(" ^ "cas_constant" ^ " + " ^ (ast_type_to_string st t) ^ ")"
                               | Latex -> "(" ^ "cas_constant" ^ " + " ^ (ast_type_to_string st t) ^ ")"
				 )		    

let rec ast_type_to_string st = function
  | Ast_eqv_bool -> "bool"
  | _ -> "NADA"

let rec ast_type_to_ascii = ast_type_to_string Ascii
let rec ast_type_to_latex = ast_type_to_string Latex

					       
let rec ast_to_string st = function
| Ast_eqv_bool                  -> "bool"
| Ast_eqv_nat                   -> "int"
| Ast_eqv_list eqv              -> "(" ^ (ast_to_string st eqv) ^ ") list"
| Ast_eqv_set eqv               -> "(" ^ (ast_to_string st eqv) ^ ") set"
| Ast_eqv_product (eqv1, eqv2)  -> "(" ^ (ast_to_string st eqv1) ^ " * " ^ (ast_to_string st eqv2) ^ ")"
| Ast_eqv_sum (eqv1, eqv2)      -> "(" ^ (ast_to_string st eqv1) ^ " + " ^ (ast_to_string st eqv2) ^ ")"
| Ast_eqv_add_constant (c, eqv) -> "({" ^ (char_list_to_string c.constant_ascii)      ^ "} + " ^ (ast_to_string st eqv) ^ ")"
| Ast_eqv_nat_ceiling  n        -> "[" ^ (string_of_int (n +1)) ^ "]"
| Ast_eqv_minset po             -> "minset ..." 
| _ -> "NADA"

let ast_to_ascii = ast_to_string Ascii
let ast_to_latex = ast_to_string Latex 									     

 *)
							     
let string_of_check_exists_id data = function 
    | Certify_Not_Exists_Id -> "No Identity\n" 
    | Certify_Exists_Id a -> "Identity " ^ (data_to_ascii (data a)) ^ "\n"

let string_of_check_exists_ann data = function 
    | Certify_Not_Exists_Ann -> "No Annihilator\n" 
    | Certify_Exists_Ann a -> "Annihilator " ^ (data_to_ascii (data a)) ^ "\n"
          
let string_of_check_commutative eq bop data = function 
    | Certify_Commutative -> "Commutative\n" 
    | Certify_Not_Commutative (a, b) ->
       let lhs = bop a b in
       let rhs = bop b a in
       if eq lhs rhs
       then "INTERNAL ERROR : Not Commutative\n"
       else "Not Commutative: \n" ^
	      "   " ^ (data_to_ascii (data a)) ^  "." ^ (data_to_ascii (data b)) ^ " = " ^ (data_to_ascii (data lhs)) ^ "\n" ^
	      "   " ^ (data_to_ascii (data b)) ^  "." ^ (data_to_ascii (data a)) ^ " = " ^ (data_to_ascii (data rhs)) ^ "\n"

let string_of_check_idempotent eq bop data = function 
    | Certify_Idempotent -> "Idempotent\n" 
    | Certify_Not_Idempotent a ->
       let result = bop a a in
       if eq a result
       then "INTERNAL ERROR : Not Idempotent\n"
       else "Not Idempotent: \n" ^
	    "   " ^ (data_to_ascii (data a)) ^  "." ^ (data_to_ascii (data a)) ^ " = " ^ (data_to_ascii (data result)) ^ "\n" 

let string_of_check_selective eq bop data = function 
    | Certify_Selective -> "Selective \n" 
    | Certify_Not_Selective (a, b) ->
       let result = bop a b in
       if (eq a result) || (eq b result)
       then "INTERNAL ERROR : Not Selective\n"
       else "Not Selective: \n" ^
	      "   " ^ (data_to_ascii (data a)) ^  "." ^ (data_to_ascii (data b)) ^ " = " ^ (data_to_ascii (data result)) ^ "\n"

let string_of_check_anti_left eq bop data = function 
    | Certify_Anti_Left -> "Anti Left\n" 
    | Certify_Not_Anti_Left (a, b) ->
       let result = bop a b in
       if eq a result 
       then "Not Anti Left: \n" ^
	      "   " ^ (data_to_ascii (data a)) ^  "." ^ (data_to_ascii (data b)) ^ " = " ^ (data_to_ascii (data result)) ^ "\n"
       else "INTERNAL ERROR : Not Anti Left\n"

let string_of_check_anti_right eq bop data = function 
    | Certify_Anti_Right -> "Anti Right\n" 
    | Certify_Not_Anti_Right (s, t) -> 
       let result = bop t s in
       if eq s result 
       then "Not Anti Right: \n" ^
	      "   " ^ (data_to_ascii (data t)) ^  "." ^ (data_to_ascii (data s)) ^ " = " ^ (data_to_ascii (data result)) ^ "\n"
       else "INTERNAL ERROR : Not Anti Right\n"


let string_of_check_is_left eq bop data = function 
    | Certify_Is_Left -> "Is Left\n" 
    | Certify_Not_Is_Left (a, b) ->
       let result = bop a b in
       if eq a result 
       then "INTERNAL ERROR : Not Is Left\n"
       else "Not Is Left: \n" ^
	      "   " ^ (data_to_ascii (data a)) ^  "." ^ (data_to_ascii (data b)) ^ " = " ^ (data_to_ascii (data result)) ^ "\n"

let string_of_check_is_right eq bop data = function 
    | Certify_Is_Right -> "Is Right\n" 
    | Certify_Not_Is_Right (a, b) -> 
       let result = bop a b in
       if eq b result 
       then "INTERNAL ERROR : Not Is Right\n"
       else "Not Is Right: \n" ^
	      "   " ^ (data_to_ascii (data a)) ^  "." ^ (data_to_ascii (data b)) ^ " = " ^ (data_to_ascii (data result)) ^ "\n"
															   

let string_of_check_left_cancellative eq bop data = function 
    | Certify_Left_Cancellative -> "Left Cancellative\n" 
    | Certify_Not_Left_Cancellative (a, (b, c)) ->
       (* ab = ac and b <> c *)
       let ab = bop a b in
       let ac = bop a c in       
       if eq b c 
       then "INTERNAL ERROR : Not Left Cancellative\n"
       else if eq ab ac
            then "Not Left Cancellative: \n" ^
		   "   " ^ (data_to_ascii (data a)) ^  "." ^ (data_to_ascii (data b)) ^ " = " ^ (data_to_ascii (data ab)) ^ "\n" ^
		   "   " ^ (data_to_ascii (data a)) ^  "." ^ (data_to_ascii (data c)) ^ " = " ^ (data_to_ascii (data ac)) ^ "\n" ^
		   "   " ^ (data_to_ascii (data b)) ^ " <> " ^ (data_to_ascii (data c)) ^ "\n" 	       
            else  "INTERNAL ERROR\n"	      

let string_of_check_right_cancellative eq bop data = function 
    | Certify_Right_Cancellative ->  "Right Cancellative\n" 
    | Certify_Not_Right_Cancellative (a, (b, c)) ->
       (* ba = ca and b <> c *)
       let ba = bop b a in
       let ca = bop c a in       
       if eq b c 
       then "INTERNAL ERROR : Not Right Cancellative\n"
       else if eq ba ca
            then "Not Right Cancellative: \n" ^
		   "   " ^ (data_to_ascii (data b)) ^  "." ^ (data_to_ascii (data a)) ^ " = " ^ (data_to_ascii (data ba)) ^ "\n" ^
		   "   " ^ (data_to_ascii (data c)) ^  "." ^ (data_to_ascii (data a)) ^ " = " ^ (data_to_ascii (data ca)) ^ "\n" ^
		   "   " ^ (data_to_ascii (data b)) ^ " <> " ^ (data_to_ascii (data c)) ^ "\n" 	       
            else  "INTERNAL ERROR\n"	      

let string_of_check_left_constant eq bop data = function 
    | Certify_Left_Constant -> "Left Constant\n" 
    | Certify_Not_Left_Constant (a, (b, c)) ->
       (* ab <> ac *) 
       let ab = bop a b in
       let ac = bop a c in       
       if eq ab ac 
       then "INTERNAL ERROR Not Left Constant\n"
       else "Not Left Constant: \n" ^
		   "   " ^ (data_to_ascii (data a)) ^  "." ^ (data_to_ascii (data b)) ^ " = " ^ (data_to_ascii (data ab)) ^ "\n" ^
		   "   " ^ (data_to_ascii (data a)) ^  "." ^ (data_to_ascii (data c)) ^ " = " ^ (data_to_ascii (data ac)) ^ "\n"


let string_of_check_right_constant eq bop data = function 
    | Certify_Right_Constant -> "Right Constant\n" 
    | Certify_Not_Right_Constant (s, (t, u)) -> 
       (* ts <> us *) 
       let ts = bop t s in
       let us = bop u s in       
       if eq ts us 
       then "INTERNAL ERROR : Not Right Constant???: \n" 
       else "Not Right Constant: \n" ^
		   "   " ^ (data_to_ascii (data t)) ^  "." ^ (data_to_ascii (data s)) ^ " = " ^ (data_to_ascii (data ts)) ^ "\n" ^
		   "   " ^ (data_to_ascii (data u)) ^  "." ^ (data_to_ascii (data s)) ^ " = " ^ (data_to_ascii (data us)) ^ "\n"


let string_of_check_left_distributive eq plus times data = function 
    | Inl (BS_Left_Distributive _) ->  "Left Distributive\n" 
    | Inr (BS_Not_Left_Distributive (a, (b, c))) ->
       (* lhs = a*(b + c) <> a*b + a*c = rhs *)
       let plus_b_c = plus b c    in
       let lhs = times a plus_b_c in
       let times_a_b = times a b in
       let times_a_c = times a c in
       let rhs = plus  times_a_b  times_a_c in
       if eq lhs rhs
       then "INTERNAL ERROR : Not Left Distributive\n"
       else "Not Left Distributive:\n" ^
	      "   a = " ^ (data_to_ascii (data a)) ^ "\n" ^
	      "   b = " ^ (data_to_ascii (data b)) ^ "\n" ^
	      "   c = " ^ (data_to_ascii (data c)) ^ "\n" ^				  
	      "   lhs = a*(b + c) <> a*b + a*c = rhs: \n" ^
	      "   b + c = " ^ (data_to_ascii (data plus_b_c)) ^ "\n" ^
	      "   a*b = " ^ (data_to_ascii (data times_a_b)) ^ "\n" ^
	      "   a*c = " ^ (data_to_ascii (data times_a_c)) ^ "\n" ^
	      "   lhs = " ^ (data_to_ascii (data lhs)) ^ "\n" ^				 
	      "   rhs = " ^ (data_to_ascii (data rhs)) ^ "\n" 
		  
let string_of_check_right_distributive eq plus times data = function 
    | Inl (BS_Right_Distributive _) -> "Right Distributive \n" 
    | Inr (BS_Not_Right_Distributive (a, (b, c))) -> 
       (* lhs = (b + c)*a <> b*a + c*a = rhs *)
       let plus_b_c = plus b c    in
       let lhs = times plus_b_c a in
       let times_b_a = times b a in
       let times_c_a = times c a in
       let rhs = plus  times_b_a  times_c_a in
       if eq lhs rhs
       then "INTERNAL ERROR : Not Right Distributive\n"
       else "Not Right Distributive: \n" ^
	      "   a = " ^ (data_to_ascii (data a)) ^ "\n" ^
	      "   b = " ^ (data_to_ascii (data b)) ^ "\n" ^
	      "   c = " ^ (data_to_ascii (data c)) ^ "\n" ^				  
	      "   lhs = (b + c)*a <> b*a + c*a = rhs: \n" ^
	      "   b + c = " ^ (data_to_ascii (data plus_b_c)) ^ "\n" ^
	      "   b*a = " ^ (data_to_ascii (data times_b_a)) ^ "\n" ^
	      "   c*a = " ^ (data_to_ascii (data times_c_a)) ^ "\n" ^
	      "   lhs = " ^ (data_to_ascii (data lhs)) ^ "\n" ^				 
	      "   rhs = " ^ (data_to_ascii (data rhs)) ^ "\n" 

							   
let string_of_check_left_absorptive eq plus times data = function 
    | Inl (BS_Left_Absorptive _) -> "Left Left Absorptive\n" 
    | Inr (BS_Not_Left_Absorptive (a, b)) -> 
       (* a <> a + (a * b) *)
       let times_a_b = times a b in
       let rhs = plus a times_a_b in
       if eq a rhs
       then "INTERNAL ERROR : Not Left left Absorptive\n"
       else "Not Left left Absorptive: \n" ^
	      "   a = " ^ (data_to_ascii (data a)) ^ "\n" ^
	      "   b = " ^ (data_to_ascii (data b)) ^ "\n" ^
	      "   a <> a + a*b = rhs: \n" ^
	      "   a*b = " ^ (data_to_ascii (data times_a_b)) ^ "\n" ^
	      "   rhs = " ^ (data_to_ascii (data rhs)) ^ "\n" 

let string_of_check_right_absorptive eq plus times data = function 
    | Inl (BS_Right_Absorptive _ ) -> "Left_Right Absorptive \n" 
    | Inr (BS_Not_Right_Absorptive (a, b)) -> 
       (* a <> a + (b * a) *)
       let times_b_a = times b a in
       let rhs = plus a times_b_a in
       if eq a rhs
       then "INTERNAL ERROR : Not Left Right Absorptive\n"
       else "Not Left Right Absorptive: \n" ^
	      "   a = " ^ (data_to_ascii (data a)) ^ "\n" ^
	      "   b = " ^ (data_to_ascii (data b)) ^ "\n" ^
	      "   a <> a + b*a = rhs: \n" ^
	      "   b*a = " ^ (data_to_ascii (data times_b_a)) ^ "\n" ^
	      "   rhs = " ^ (data_to_ascii (data rhs)) ^ "\n" 

(*******************************************************)

(*			 
let bop_describe bop = (print_string "Binary operation ->\n";  print_string (nl (ast_to_ascii bop)))			 			 
let plus_describe bop = (print_string "\nAdditive operation ->\n";
			 print_string   "--------------------\n";
			 print_string (nl (ast_to_ascii bop)))			 
let times_describe bop = (print_string "\nMultiplicative operation ->\n";
			  print_string   "--------------------------\n";
			  print_string (nl (ast_to_ascii bop)))


let eqv_describe (eqv : 'a Cas.eqv) = print_string "eqv_describe"

  (
     print_string "Carrier type: ";  print_string (nl (ast_type_to_ascii (eqv_type_ast (eqv_certs eqv))));
     print_string "Equality: ";      print_string (nl (ast_to_ascii (eqv_brel_ast (eqv_certs eqv))));     
  )
 *)
						
let sg_certs_describe eq b data certs =
  (
       print_string (string_of_check_idempotent eq b data (certs.sg_idempotent_d)) ; 
       print_string (string_of_check_commutative eq b data (certs.sg_commutative_d)) ; 
       print_string (string_of_check_selective eq b data (certs.sg_selective_d))
  )
			   
let sg_describe sg =
 ( print_string (string_of_check_exists_id sg.sg_eqv.eqv_data (sg.sg_exists_id_d)) ; 
   print_string (string_of_check_exists_ann sg.sg_eqv.eqv_data (sg.sg_exists_ann_d)) ; 
   sg_certs_describe sg.sg_eqv.eqv_eq sg.sg_bop sg.sg_eqv.eqv_data sg.sg_certs) 



let sg_certs_describe_fully eq b data certs =
  (
       print_string (string_of_check_idempotent eq b data (certs.sg_idempotent_d)) ; 
       print_string (string_of_check_commutative eq b data (certs.sg_commutative_d)) ; 
       print_string (string_of_check_selective eq b data (certs.sg_selective_d)) ;
       print_string (string_of_check_left_cancellative eq b data (certs.sg_left_cancel_d)) ; 
       print_string (string_of_check_right_cancellative eq b data (certs.sg_right_cancel_d)) ; 
       print_string (string_of_check_left_constant eq b data (certs.sg_left_constant_d)) ; 
       print_string (string_of_check_right_constant eq b data (certs.sg_right_constant_d)) ; 
       print_string (string_of_check_anti_left eq b data (certs.sg_anti_left_d)) ; 
       print_string (string_of_check_anti_right eq b data (certs.sg_anti_right_d)) ; 
       print_string (string_of_check_is_left eq b data (certs.sg_is_left_d)) ;  
       print_string (string_of_check_is_right eq b data (certs.sg_is_right_d))
      )


let sg_C_certs_describe eq b data certs =
  (
       print_string (string_of_check_idempotent eq b data (certs.sg_C_idempotent_d)) ; 
       print_string (string_of_check_selective eq b data (certs.sg_C_selective_d)) ;
       print_string (string_of_check_left_cancellative eq b data (certs.sg_C_cancel_d)) ; 
       print_string (string_of_check_left_constant eq b data (certs.sg_C_constant_d)) ; 
       print_string (string_of_check_anti_left eq b data (certs.sg_C_anti_left_d)) ; 
       print_string (string_of_check_anti_right eq b data (certs.sg_C_anti_right_d)) 
      )

let sg_describe_fully sg =
  (print_string (string_of_check_exists_id sg.sg_eqv.eqv_data (sg.sg_exists_id_d)) ; 
   print_string (string_of_check_exists_ann sg.sg_eqv.eqv_data (sg.sg_exists_ann_d)) ; 
   sg_certs_describe_fully sg.sg_eqv.eqv_eq sg.sg_bop sg.sg_eqv.eqv_data sg.sg_certs)


let mcas_sg_describe_fully msg = sg_describe_fully (cast_up_sg msg);; 

let bs_certs_describe eq plus times data certs = 
  (print_string "Interaction of Additive and Multiplicative operations: \n";
   print_string   "-------------------------------------------------------\n"; 
   print_string (string_of_check_left_distributive eq plus times data (certs.bs_left_distributive_d) ); 
   print_string (string_of_check_right_distributive eq plus times data (certs.bs_right_distributive_d) );
(*   
   print_string (string_of_check_plus_id_is_times_ann (bs_plus_id_is_times_ann_d) ); 
   print_string (string_of_check_times_id_is_plus_ann (bs_times_id_is_plus_ann_d)) ; 
 *)
  )

let bs_certs_describe_fully eq plus times data certs = 
     (print_string "Interaction of Additive and Multiplicative operations\n";
      print_string   "-------------------------------------------------------\n";    
       print_string (string_of_check_left_distributive eq plus times data (certs.bs_left_distributive_d) ); 
       print_string (string_of_check_right_distributive eq plus times data (certs.bs_right_distributive_d) );
       print_string (string_of_check_left_absorptive eq plus times data (certs.bs_left_absorptive_d) ); 
       print_string (string_of_check_right_absorptive eq plus times data (certs.bs_right_absorptive_d) )
      )

let eqv_describe_fully eqv =
  print_string ((describe_eqv_ast eqv.eqv_ast) ^ "\n");;

let describe_id data = function 
| Id_Ann_None                -> print_string "No identity\n"
| Id_Ann_Id_None id          -> print_string ("Identity = " ^ (data_to_ascii (data id)) ^ "\n")
| Id_Ann_None_Ann _          -> print_string "No identity\n"
| Id_Ann_Equal id_ann        -> print_string ("Identity = " ^ (data_to_ascii (data id_ann)) ^ "\n")
| Id_Ann_Not_Equal (id, _)   -> print_string ("Identity = " ^ (data_to_ascii (data id)) ^ "\n");; 

let describe_ann data = function 
| Id_Ann_None                -> print_string "No annihilator\n"
| Id_Ann_Id_None _           -> print_string "No annihilator\n"
| Id_Ann_None_Ann ann        -> print_string ("Annihilator = " ^ (data_to_ascii (data ann)) ^ "\n")
| Id_Ann_Equal id_ann        -> print_string ("Annihilator = " ^ (data_to_ascii (data id_ann)) ^ "\n")
| Id_Ann_Not_Equal (_, ann)  -> print_string ("Annihilator = " ^ (data_to_ascii (data ann)) ^ "\n");; 
						  
  
let id_ann_certs_describe_plus data id_ann_certs =
  (describe_id data id_ann_certs.id_ann_plus_times_d;
   describe_ann data id_ann_certs.id_ann_times_plus_d);; 

let id_ann_certs_describe_times data id_ann_certs =
  (describe_id data id_ann_certs.id_ann_times_plus_d;
   describe_ann data id_ann_certs.id_ann_plus_times_d);; 
                                                      

let bs_describe bs =
    let eqv         = bs.bs_eqv          in        
    let eq          = bs.bs_eqv.eqv_eq   in   
    let data        = bs.bs_eqv.eqv_data in 
    let plus_props  = bs.bs_plus_props   in 
    let times_props = bs.bs_times_props  in
    let id_ann_props = bs.bs_id_ann_props  in     
    let certs       = bs.bs_props        in
    let plus        = bs.bs_plus         in
    let times       = bs.bs_times        in
    let ast         = bs.bs_ast          in             
    (print_string "Carrier set:\n";
     eqv_describe_fully eqv;
     print_string "Additive properties:\n";
     print_string "--------------------\n";         
     sg_C_certs_describe eq plus data plus_props;
     id_ann_certs_describe_plus data id_ann_props;
     print_string "Multiplicative properties:\n";
     print_string "-------------------------\n";              
     sg_certs_describe eq times data times_props;
     id_ann_certs_describe_times data id_ann_props;
     bs_certs_describe eq plus times data certs
    )

let next_int_ref = ref 0;; 

let reset_next_int_ref () = next_int_ref := 0;;
  
let next_int () =
  let v = !next_int_ref
  in (next_int_ref := v + 1; v);;


let stdf = Format.std_formatter;;
let strf = Format.str_formatter;;

let sg_eq i l = (Format.fprintf strf "(S_%s, *_%s) = %s" i i (String.concat " " l);
		 Format.flush_str_formatter ());;  

let sg_i i = (Format.fprintf strf "(S_%s, *_%s)" i i ;
	      Format.flush_str_formatter ());;

  
let bs_i i = (Format.fprintf strf "(S_%s, +_%s, *_%s)" i i i;
	      Format.flush_str_formatter ());;

let bs_eq i l = (Format.fprintf strf "(S_%s, +_%s, *_%s) = %s" i i i (String.concat " " l);
		 Format.flush_str_formatter ());;

let slt_i i = (Format.fprintf strf "(L_%s, S_%s, +_%s, |>_%s)" i i i i;
	       Format.flush_str_formatter ());;

let slt_eq i l = (Format.fprintf strf "(L_%s, S_%s, +_%s, *_%s) = %s" i i i i (String.concat " " l);
		  Format.flush_str_formatter ());;

  
let s_i i = "S_" ^ i
let l_i i = "L_" ^ i		     

let s_eq i t = (s_i i) ^ " = " ^ t
let l_eq i t = (l_i i) ^ " = " ^ t				   

let plus_i i a  b = (Format.fprintf strf "%s +_%s %s" a i b;
		       Format.flush_str_formatter ());; 

let times_i i a  b = (Format.fprintf strf "%s *_%s %s" a i b;
			Format.flush_str_formatter ());;

let ltr_i i a  b = (Format.fprintf strf "%s |>_%s %s" a i b;
			Format.flush_str_formatter ());;
  
let plus_eq i a  b c = (Format.fprintf strf "%s +_%s %s = %s" a i b c;
		       Format.flush_str_formatter ());; 

let plus_eq_cond i a  b c cond =
  (Format.fprintf strf "%s +_%s %s = %s (if %s)" a i b c cond;
   Format.flush_str_formatter ());; 
  
let times_eq i a  b c = (Format.fprintf strf "%s *_%s %s = %s" a i b c;
			Format.flush_str_formatter ());;

let ltr_eq i a  b c = (Format.fprintf strf "%s |>_%s %s = %s" a i b c;
			Format.flush_str_formatter ());;
  
let pline l = Format.pp_print_string stdf (l ^ "\n")

let singleton a = "{" ^ a ^ "}"
let set a = "set(" ^ a ^ ")"			      
let sum a b = a ^ " + " ^ b
let prod a b = a ^ " * " ^ b				   			    
let inl x = "Inl(" ^ x ^ ")"
let inr x = "Inr(" ^ x ^ ")"
let pair x y = "(" ^ x ^ ", " ^ y ^ ")"
let equal x y = x ^ " = " ^ y
let nequal x y = x ^ " <> " ^ y

let rec sg_describe_algebra_fully_aux =  function 			
  | Ast_sg_times ->
     let i = string_of_int (next_int ()) in
     (pline (sg_eq i ["sg_times"]);
      pline "where";       
      pline (s_eq i "nat");
      pline (times_eq i "x" "y" "x * y"); 
      i) 
  | Ast_sg_plus ->
     let i = string_of_int (next_int ()) in
     (pline (sg_eq i ["sg_plus"]);
      pline "where";       
      pline (s_eq i "nat");
      pline (times_eq i "x" "y" "x + y"); 
      i) 
  | Ast_sg_or  -> 
     let i = string_of_int (next_int ()) in
     (pline (sg_eq i ["sg_or"]);
      pline "where"; 
      pline (s_eq i "bool");
      pline (times_eq i "x" "y" "x or y"); 
      i) 
  | Ast_sg_and -> 
     let i = string_of_int (next_int ()) in
     (pline (sg_eq i ["sg_and"]);
      pline "where"; 
      pline (s_eq i "bool");
      pline (times_eq i "x" "y" "x and y"); 
      i) 
  | Ast_sg_min ->
     let i = string_of_int (next_int ()) in
     (pline (sg_eq i ["sg_min"]);
      pline "where";       
      pline (s_eq i "nat");
      pline (times_eq i "x" "y" "x min y"); 
      i) 
  | Ast_sg_max ->
     let i = string_of_int (next_int ()) in
     (pline (sg_eq i ["sg_max"]);
      pline "where";       
      pline (s_eq i "nat");
      pline (times_eq i "x" "y" "x max y"); 
      i)
  | Ast_sg_left ast ->
     let i = string_of_int (next_int ()) in
     let carrier = unfold_eqv_ast ast in 
     (pline (sg_eq i ["sg_left"; carrier]);
      pline (s_eq i carrier);
      pline (times_eq i "x" "y" "x");       
     i)
  | _ ->
     let i = string_of_int (next_int ()) in          
     (pline "bs_describe_algebra_fully_aux: Not Matched!"; i)       
(*
  | Ast_sg_add_id of (cas_constant*cas_sg_ast) -> 
  | Ast_sg_add_ann of (cas_constant*cas_sg_ast)
  | Ast_sg_concat of cas_eqv_ast
| Ast_sg_union of cas_eqv_ast
| Ast_sg_intersect of cas_eqv_ast

| Ast_sg_right of cas_eqv_ast
| Ast_sg_left_sum of (cas_sg_ast*cas_sg_ast)
| Ast_sg_right_sum of (cas_sg_ast*cas_sg_ast)
| Ast_sg_lift of cas_sg_ast
| Ast_sg_llex of (cas_sg_ast*cas_sg_ast)
| Ast_sg_product of (cas_sg_ast*cas_sg_ast)
| Ast_sg_minset_lift of cas_os_ast
| Ast_sg_minset_union of cas_or_ast
| Ast_sg_plus_of_bs of cas_bs_ast
| Ast_sg_times_of_bs of cas_bs_ast
| Ast_sg_times_of_os of cas_os_ast
 *) 
  
let rec bs_describe_algebra_fully_aux =  function
  | Ast_min_plus ->
     let i = string_of_int (next_int ()) in
     (pline (bs_eq i ["min_plus"]);
      pline "where"; 
      pline (s_eq i "nat");
      pline (plus_eq i "x" "y" "x min y"); 
      pline (times_eq i "x" "y" "x + y"); 
      i) 
  | Ast_max_plus ->
     let i = string_of_int (next_int ()) in
     (pline (bs_eq i ["max_plus"]);
      pline "where";       
      pline (s_eq i "nat");
      pline (plus_eq i "x" "y" "x max y"); 
      pline (times_eq i "x" "y" "x + y"); 
      i) 
  | Ast_and_or ->
     let i = string_of_int (next_int ()) in
     (pline (bs_eq i ["and_or"]);
      pline "where"; 
      pline (s_eq i "bool");
      pline (plus_eq i "x" "y" "x and y"); 
      pline (times_eq i "x" "y" "x or y"); 
      i) 
  | Ast_or_and ->
     let i = string_of_int (next_int ()) in
     (pline (bs_eq i ["or_and"]);
      pline "where"; 
      pline (s_eq i "bool");
      pline (plus_eq i "x" "y" "x or y"); 
      pline (times_eq i "x" "y" "x and y"); 
      i) 
  | Ast_max_min ->
     let i = string_of_int (next_int ()) in
     (pline (bs_eq i ["max_min"]);
      pline "where"; 
      pline (s_eq i "nat");       
      pline (plus_eq i "x" "y" "x max y"); 
      pline (times_eq i "x" "y" "x min y"); 
      i) 
  | Ast_min_max ->
     let i = string_of_int (next_int ()) in
     (pline (bs_eq i ["min_max"]);
      pline "where"; 
      pline (s_eq i "nat");       
      pline (plus_eq i "x" "y" "x min y"); 
      pline (times_eq i "x" "y" "x max y"); 
      i) 
  | Ast_bs_add_zero (c, bs) -> 
     let j = bs_describe_algebra_fully_aux bs in 
     let i = string_of_int (next_int ()) in     
     let c' = char_list_to_string c.constant_ascii in
     (pline (bs_eq i ["bs_add_zero"; (bs_i j); c']);
      pline "where"; 
      pline (s_eq i (sum (singleton c') (s_i j))); 
      pline(plus_eq i (inr "x") (inr "y") (inr (plus_i j "x" "y")));
      pline(plus_eq i (inl c') "a" "a");
      pline(plus_eq i "a" (inl c') "a");      
      pline(times_eq i (inr "x") (inr "y") (inr (times_i j "x" "y")));
      pline(times_eq i (inl c') "_" (inl c')); 
      pline(times_eq i "_" (inl c') (inl c')); 
      i)
  | Ast_bs_add_one (c, bs) ->
     let j = bs_describe_algebra_fully_aux bs in 
     let i = string_of_int (next_int ()) in     
     let c' = char_list_to_string c.constant_ascii in
     (pline (bs_eq i ["bs_add_one"; (bs_i j); c']);
      pline "where"; 
      pline (s_eq i (sum (singleton c') (s_i j))); 
      pline(plus_eq i (inr "x") (inr "y") (inr (plus_i j "x" "y")));
      pline(plus_eq i (inl c') "_" (inl c')); 
      pline(plus_eq i "_" (inl c') (inl c')); 
      pline(times_eq i (inr "x") (inr "y") (inr (times_i j "x" "y")));
      pline(times_eq i (inl c') "a" "a");
      pline(times_eq i "a" (inl c') "a");            
      i)
  | Ast_bs_product (bs1, bs2) ->
     let i1 = bs_describe_algebra_fully_aux bs1 in
     let i2 = bs_describe_algebra_fully_aux bs2 in           
     let i = string_of_int (next_int ()) in
     (pline (bs_eq i ["bs_product"; (bs_i i1); (bs_i i2)]);
      pline "where"; 
      pline (s_eq i (prod (s_i i1) (s_i i2)));
      pline (plus_eq i "(a, b)" "(c, d)" (pair (plus_i i1 "a" "c") (plus_i i2 "b" "d")));
      pline (times_eq i "(a, b)" "(c, d)" (pair (times_i i1 "a" "c") (times_i i2 "b" "d")));       
      i) 
  | Ast_bs_llex_product (bs1, bs2) ->
     let i1 = bs_describe_algebra_fully_aux bs1 in
     let i2 = bs_describe_algebra_fully_aux bs2 in           
     let i = string_of_int (next_int ()) in
     (pline (bs_eq i ["bs_llex_product"; (bs_i i1); (bs_i i2)]);
      pline "where";       
      pline (s_eq i (prod (s_i i1) (s_i i2)));
      pline (plus_eq_cond i "(a, b)" "(c, d)" (pair "a" (plus_i i2 "b" "d")) (equal (equal "a" ((plus_i i1 "a" "c"))) "c") );
      pline (plus_eq_cond i "(a, b)" "(c, d)" "(a, b)" (nequal (equal "a" ((plus_i i1 "a" "c"))) "c") );
      pline (plus_eq_cond i "(a, b)" "(c, d)" "(c, d)" (equal (nequal "a" ((plus_i i1 "a" "c"))) "c") );
      pline (times_eq i "(a, b)" "(c, d)" (pair (times_i i1 "a" "c") (times_i i2 "b" "d")));       
      i)
  | Ast_bs_union_lift sg        ->
     let i1 = sg_describe_algebra_fully_aux sg in     
     let i = string_of_int (next_int ()) in     
     (pline (bs_eq i ["bs_union_lift"; (sg_i i1)]);
      pline (s_eq i (set (s_i i1)));
      pline (plus_eq i "X" "Y" "X union Y");
      pline (times_eq i "X" "Y" ("{" ^ (times_i i1 "x" "y") ^ " | x in X, y in Y}")); 
      i)
  | Ast_bs_left_sum_right_sum (bs1, bs2) ->
     let i = string_of_int (next_int ()) in     
     (pline "bs_describe_algebra_fully_aux: Not Yet!"; i) 
  | Ast_bs_right_sum_left_sum (bs1, bs2) ->
     let i = string_of_int (next_int ()) in     
     (pline "bs_describe_algebra_fully_aux: Not Yet!"; i) 
  | Ast_bs_left sg  ->
     let i = string_of_int (next_int ()) in     
     (pline "bs_describe_algebra_fully_aux: Not Yet!"; i) 
  | Ast_bs_right sg ->
     let i = string_of_int (next_int ()) in
     (pline "bs_describe_algebra_fully_aux: Not Yet!"; i) 
  | Ast_union_intersect eqv  ->
     let i = string_of_int (next_int ()) in     
     (pline "bs_describe_algebra_fully_aux: Not Yet!"; i) 
  | Ast_intersect_union eqv  ->
     let i = string_of_int (next_int ()) in     
     (pline "bs_describe_algebra_fully_aux: Not Yet!"; i) 
  | Ast_bs_dual bs           ->
     let i = string_of_int (next_int ()) in     
     (pline "bs_describe_algebra_fully_aux: Not Yet!"; i) 
  | Ast_minset_lift_union os ->
     let i = string_of_int (next_int ()) in     
     (pline "bs_describe_algebra_fully_aux: Not Yet!"; i) 
  | Ast_minset_union_lift os ->
     let i = string_of_int (next_int ()) in     
     (pline "bs_describe_algebra_fully_aux: Not Yet!"; i) 
  | Ast_lift_union sg        ->
     let i = string_of_int (next_int ()) in     
     (pline "bs_describe_algebra_fully_aux: Not Yet!"; i) 
  | _   ->
     let i = string_of_int (next_int ()) in          
     (pline "bs_describe_algebra_fully_aux: Not Matched!"; i)       

let bs_describe_algebra_fully ast =
  let _ = reset_next_int_ref () in
  bs_describe_algebra_fully_aux ast
  
let bs_describe_fully bs =
    let eqv         = bs.bs_eqv          in      
    let eq          = eqv.eqv_eq         in   
    let data        = bs.bs_eqv.eqv_data in 
    let plus_props  = bs.bs_plus_props   in 
    let times_props = bs.bs_times_props  in
    let id_ann_props = bs.bs_id_ann_props  in         
    let certs       = bs.bs_props        in
    let plus        = bs.bs_plus         in
    let times       = bs.bs_times        in
    let ast         = bs.bs_ast          in             
    (bs_describe_algebra_fully ast; 
     print_string "Additive properties:\n";
     print_string "--------------------\n";
     id_ann_certs_describe_plus data id_ann_props;     
     sg_C_certs_describe eq plus data plus_props;
     print_string "Multiplicative properties:\n";
     print_string "-------------------------\n";
     id_ann_certs_describe_times data id_ann_props;     
     sg_certs_describe_fully eq times data times_props;
     bs_certs_describe_fully eq plus times data certs
    )

let bs_mcas_describe_fully mbs =
    match mbs with
    | MCAS_bs_Error cll -> print_error_list cll 
    | MCAS_bs bbs -> bs_describe_fully (cast_up_bs bbs) 

    
