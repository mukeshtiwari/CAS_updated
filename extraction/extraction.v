Require Import CAS.coq.common.compute. 

Require Import CAS.coq.eqv.nat.
Require Import CAS.coq.eqv.product.
Require Import CAS.coq.eqv.sum.
Require Import CAS.coq.eqv.add_constant.
Require Import CAS.coq.eqv.bool.
Require Import CAS.coq.eqv.list.
Require Import CAS.coq.eqv.set.
Require Import CAS.coq.eqv.minset. 
(*
Require Import CAS.coq.eqv.nat_ceiling.
Require Import CAS.coq.sg.cast_up.
*)
Require Import CAS.coq.sg.plus.
Require Import CAS.coq.sg.min.
Require Import CAS.coq.sg.max.
Require Import CAS.coq.sg.product.
Require Import CAS.coq.sg.llex.
Require Import CAS.coq.sg.add_id.
Require Import CAS.coq.sg.add_ann.
Require Import CAS.coq.sg.times.
Require Import CAS.coq.sg.and.
Require Import CAS.coq.sg.or.
Require Import CAS.coq.sg.left.
Require Import CAS.coq.sg.right.
Require Import CAS.coq.sg.left_sum.
Require Import CAS.coq.sg.right_sum.
Require Import CAS.coq.sg.concat.
Require Import CAS.coq.sg.union.
Require Import CAS.coq.sg.intersect.
Require Import CAS.coq.sg.minset_union. 
Require Import CAS.coq.sg.lift.
Require Import CAS.coq.sg.minset_lift.

Require Import CAS.coq.po.cast_up.
Require Import CAS.coq.po.add_bottom.
Require Import CAS.coq.po.add_top.
Require Import CAS.coq.po.from_sg.
Require Import CAS.coq.po.product.
Require Import CAS.coq.po.trivial.
Require Import CAS.coq.po.lex.

(* 
Require Import CAS.coq.po.lte_nat. (* why is this not from_sg_left sg_min?*)

Require Import CAS.coq.po.length.
Require Import CAS.coq.po.po_to_qo.

Require Import CAS.coq.po.left_sum. 
Require Import CAS.coq.po.right_sum. 

*) 

Require Import CAS.coq.bs.and_or.
Require Import CAS.coq.bs.or_and.
Require Import CAS.coq.bs.max_min.
Require Import CAS.coq.bs.min_max.
Require Import CAS.coq.bs.plus_times.
Require Import CAS.coq.bs.min_plus.
Require Import CAS.coq.bs.max_plus.
Require Import CAS.coq.bs.product.
Require Import CAS.coq.bs.add_zero.
Require Import CAS.coq.bs.add_one.
Require Import CAS.coq.bs.llex_product.
Require Import CAS.coq.bs.left_sum.
Require Import CAS.coq.bs.right_sum.
Require Import CAS.coq.bs.union_intersect.
Require Import CAS.coq.bs.intersect_union.
Require Import CAS.coq.bs.union_union. 
Require Import CAS.coq.bs.left.
Require Import CAS.coq.bs.right.
Require Import CAS.coq.bs.union_lift. 
Require Import CAS.coq.bs.cast.
Require Import CAS.coq.bs.minset_union_lift.
Require Import CAS.coq.bs.minset_lift_union.
(* Require Import CAS.coq.bs.dual.*)
Require Import CAS.coq.os.from_bs_left.
Require Import CAS.coq.os.from_sg.
Require Import CAS.coq.os.trivial. 
(*Require Import CAS.coq.st.cast_up.
Require Import CAS.coq.st.left.min_plus_one.
Require Import CAS.coq.st.left.llex_product.
Require Import CAS.coq.st.left.union_insert. 
Require Import CAS.coq.st.left.add_zero.
Require Import CAS.coq.st.left.plus_times.*)
Require Import CAS.coq.algorithms.dijkstra.general. 
Require Import CAS.coq.algorithms.wrapper. 
(* from coq/tr/left
Require Import CAS.coq.tr.left.add_ann.
*)
(*Require Import CAS.coq.algorithm.Mat.*) 

Require Extraction.

Cd "extraction".

(* Require Import Coq.ExtrOcamlString. *) (* why does this not work?? *) 

(* BEGIN from ExtrOcamlString.v  *)
Require Import Ascii String.

Extract Inductive ascii => char
[
"(* If this appears, you're using Ascii internals. Please don't *)
 (fun (b0,b1,b2,b3,b4,b5,b6,b7) ->
  let f b i = if b then 1 lsl i else 0 in
  Char.chr (f b0 0 + f b1 1 + f b2 2 + f b3 3 + f b4 4 + f b5 5 + f b6 6 + f b7 7))"
]
"(* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))".

Extract Constant zero => "'\000'".
Extract Constant one => "'\001'".
Extract Constant shift =>
 "fun b c -> Char.chr (((Char.code c) lsl 1) land 255 + if b then 1 else 0)".

Extract Inlined Constant ascii_dec => "(=)".

Extract Inductive string => "char list" [ "[]" "(::)" ].



(* End from ExtrOcamlString.v *) 

(* Evaluation / Extraction /Testing  

Set Extraction Optimize. (* DEFAULT *) 
Unset Extraction Optimize.

Set Extraction KeepSingleton. 
Unset Extraction KeepSingleton. (* DEFAULT *) 

Set Extraction AutoInline. (* DEFAULT *) 
Unset Extraction AutoInline.

Extraction Inline qualid1 ... qualidn. 
Extraction NoInline qualid1 ... qualidn.
Print Extraction Inline. 
Reset Extraction Inline.

Extraction qualid.
Recursive Extraction qualid_1 ... qualid_n .
Extraction "file" qualid1 ... qualidn.
Extraction Library ident.

*) 


Set Extraction KeepSingleton.
(* Set Extraction Conservative Types. *) 
Unset Extraction Optimize.
Unset Extraction AutoInline.


Extraction Language OCaml. 
Extract Inductive unit => "unit" [ "()" ].
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive prod => "(*)"  [ "(,)" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive option => "option"  [ "Some" "None" ].
Extract Inductive nat => int [ "0" "succ" ] 
     "(fun fO fS n -> if n=0 then fO () else fS (n-1))".

(* Avoid name clashes *)
Extraction Blacklist List String Int.
(*  *) 
Extraction "Cas.ml"
   make_constant
   mcas_eqv_eq_nat           
   mcas_eqv_bool
   mcas_eqv_list
   mcas_eqv_set   
   mcas_eqv_product
   mcas_eqv_add_constant
   mcas_eqv_sum
   mcas_eqv_minset
   (* semigroups *) 
   mcas_and
   mcas_or
   mcas_sg_min
   mcas_sg_max   
   mcas_sg_plus
   mcas_sg_times
   mcas_sg_concat
   mcas_sg_left
   mcas_sg_right
   mcas_sg_product 
   mcas_sg_llex
   mcas_sg_add_id
   mcas_sg_add_ann
   mcas_sg_left_sum
   mcas_sg_right_sum
   mcas_sg_lift
   mcas_sg_union
   mcas_sg_union_with_ann    
   mcas_sg_intersect
   mcas_sg_intersect_with_id    
   mcas_sg_minset_union
   (*mcas_minset_lift *)
   (* orders 
   mcas_or_add_top
   mcas_or_add_bottom
   mcas_or_product
   mcas_or_left_lex
   mcas_or_trivial 
   mcas_left_order_from_sg*)
   (* mcas_right_order_from_sg *) 
   (* b-semigroups *)    
   cast_up_bs  (* used in ocaml/Describe.ml *)
   mcas_bs_and_or
   mcas_bs_or_and     
   mcas_bs_min_plus
   mcas_bs_max_plus
   mcas_plus_times
   mcas_bs_max_min
   mcas_bs_min_max      
   mcas_bs_product
   mcas_bs_llex_product   
   mcas_bs_add_zero
   mcas_bs_add_one
   mcas_bs_union_lift 
   mcas_bs_union_intersect
   mcas_bs_union_intersect_with_one
   mcas_bs_intersect_union 
   mcas_bs_intersect_union_with_zero
   (*mcas_bs_union_union *) 
   mcas_bs_left
   mcas_bs_right
   (* mcas_minset_union_lift*) 
   (* mcas_minset_lift_union TGG: fix this! *) 
(*
   mcas_left_sum_right_sum
   mcas_right_sum_left_sum  

 *)
   (* transform tr/left 
   mcas_ltr_add_ann *)
   (* order semirgroups 
   mcas_os_from_bs_left
   mcas_os_from_sg_right
   mcas_os_from_sg_trivial
*)
   (*
   semigroup transforms 

   cast_slt_mcas_to_slt  (* used in ocaml/Describe.ml *)
   mcas_slt_min_plus_one
   mcas_slt_llex_product
   mcas_slt_union_insert
   mcas_slt_llex_product
   mcas_slt_add_zero
   mcas_slt_plus_times
    *)
   
   (* algorithms *)
   cast_below_bs_to_selective_path_algebra
   cast_below_bs_to_path_algebra
   path_algebra_matrix_solver
   selective_path_algebra_matrix_solver
   dijkstra
. 
   (* semigroup left transform *)


