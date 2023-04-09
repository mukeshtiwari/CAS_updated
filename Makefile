
COQINCLUDES= -R . CAS 
COQC=coqc -q $(COQINCLUDES)
COQDOC=coqdoc $(COQINCLUDES)
COQDEP=coqdep -c
COQEXEC=coqtop $(COQINCLUDES) -batch -load-vernac-source
OCAMLBUILD=ocamlbuild
OCAMLMKTOP=ocamlmktop
CAMLINCLUDES= -I extraction -I ocaml
OCB_OPTIONS=\
  -j 2 \
  -no-hygiene \
  -no-links \
  $(CAMLINCLUDES)


BASE=\
   coq/common/compute.v \
   coq/common/ast.v \
   coq/common/data.v \
   coq/theory/arithmetic.v \
   coq/theory/set.v \
   coq/theory/lattice_theory.v \
   coq/theory/semilattice_theory.v \

CAS=\
   coq/eqv/properties.v \
   coq/eqv/structures.v \
   coq/eqv/theory.v \
   coq/eqv/ascii.v \
   coq/eqv/string.v \
   coq/eqv/nat.v \
   coq/eqv/bool.v \
   coq/eqv/list.v \
   coq/eqv/set.v \
   coq/eqv/sum.v \
   coq/eqv/product.v \
   coq/eqv/add_constant.v \
   coq/eqv/reduce.v \
   coq/eqv/minset.v \
   coq/eqv/manger_sets.v \
   coq/sg/properties.v \
   coq/sg/theory.v \
   coq/sg/structures.v \
   coq/sg/classify.v \
   coq/sg/cast_up.v \
   coq/sg/plus.v \
   coq/sg/times.v \
   coq/sg/and.v \
   coq/sg/or.v \
   coq/sg/max.v \
   coq/sg/min.v \
   coq/sg/times.v \
   coq/sg/left.v \
   coq/sg/right.v \
   coq/sg/concat.v \
   coq/sg/left_sum.v \
   coq/sg/right_sum.v \
   coq/sg/product.v \
   coq/sg/llex.v \
   coq/sg/add_id.v \
   coq/sg/add_ann.v \
   coq/sg/union.v \
   coq/sg/intersect.v \
   coq/sg/lift.v \
   coq/sg/minset_union.v \
   coq/sg/minset_lift.v \
   coq/sg/reduce.v \
   coq/sg/manger_llex.v \
   coq/sg/manger_product.v \
   coq/po/properties.v \
   coq/po/theory.v \
   coq/po/structures.v \
   coq/po/classify.v \
   coq/po/cast_up.v \
   coq/po/trivial.v \
   coq/po/add_bottom.v \
   coq/po/from_sg.v \
   coq/po/add_top.v \
   coq/po/product.v \
   coq/po/length.v \
   coq/po/lex.v \
   coq/po/subset.v \
   coq/po/minset_subset.v \
   coq/po/set_lte.v \
   coq/po/dual.v \
   coq/tr/properties.v \
   coq/tr/structures.v \
   coq/tr/left/from_sg.v \
   coq/tr/left/plus_one.v \
   coq/tr/left/cons.v \
   coq/tr/left/singleton.v \
   coq/tr/left/insert.v \
   coq/tr/left/lift.v \
   coq/tr/left/product.v \
   coq/tr/left/add_ann.v  \
   coq/tr/left/go.v  \
   coq/bs/properties.v \
   coq/bs/structures.v \
   coq/bs/theory.v \
   coq/bs/cast.v \
   coq/bs/classify.v \
   coq/bs/plus_times.v \
   coq/bs/min_plus.v \
   coq/bs/max_plus.v \
   coq/bs/dual.v \
   coq/bs/and_or.v \
   coq/bs/or_and.v \
   coq/bs/product.v \
   coq/bs/llex_product.v \
   coq/bs/left_sum.v \
   coq/bs/right_sum.v \
   coq/bs/min_max.v \
   coq/bs/max_min.v \
   coq/bs/add_zero.v \
   coq/bs/add_one.v \
   coq/bs/left.v \
   coq/bs/right.v \
   coq/bs/reduce.v \
   coq/bs/union_lift.v \
   coq/bs/intersect_union.v \
   coq/bs/union_intersect.v \
   coq/bs/minset_union_lift.v \
   coq/bs/minset_lift_union.v \
   coq/bs/union_union.v \
   coq/os/properties.v \
   coq/os/structures.v \
   coq/os/theory.v \
   coq/os/cast_up.v \
   coq/os/from_sg.v \
   coq/os/from_bs_left.v \
   coq/os/trivial.v \
   coq/os/lex_product.v \
   coq/uop/properties.v \
   coq/uop/product.v \
   coq/uop/left_sum.v \
   coq/uop/right_sum.v \
   coq/uop/commutative_composition.v \
   coq/algorithms/big_plus.v \
   coq/algorithms/list_congruences.v \
   coq/algorithms/matrix_definition.v \
   coq/algorithms/matrix_algorithms.v \
   coq/algorithms/matrix_addition.v \
   coq/algorithms/matrix_multiplication.v \
   coq/algorithms/weighted_path.v \
   coq/algorithms/dijkstra/general.v \
   coq/algorithms/wrapper.v 

FILES=$(BASE) $(CAS)

-include $(addsuffix .d,$(FILES))
.SECONDARY: $(addsuffix .d,$(FILES))

# is there a better way? 
CMOFILES=\
Cas.cmo \
../ocaml/Describe.cmo \
../ocaml/Mcas.cmo \
../ocaml/Matrix_solver.cmo 

# 

.PHONY: all casml html clean test

all:
	$(MAKE) coq
	$(MAKE) extraction
	$(MAKE) casml

depend: $(FILES:.v=.v.d)

coq: $(FILES:.v=.vo) depend

extraction: extraction/STAMP

extraction/STAMP: $(FILES:.v=.vo) extraction/extraction.v
	rm -f extraction/*.ml extraction/*.mli
	$(COQEXEC) extraction/extraction.v
	touch extraction/STAMP

casml: extraction/STAMP ocaml/Mcas.ml ocaml/Describe.ml ocaml/Matrix_solver.ml
	./mk_casml.sh
	chmod +x casml
	$(OCAMLBUILD) $(OCB_OPTIONS) Driver.byte
	cd _build/extraction && $(OCAMLMKTOP) -o casml $(CMOFILES)

html: $(FILES:.v=.glob)
	$(COQDOC) --html --toc --utf8 --charset utf8 --interpolate -d doc/html $(FILES)

%.vo: %.v
	$(COQC) $*.v

%.v.d: %.v
	$(COQDEP) $(COQINCLUDES) "$<" > "$@" 

clean:
	rm -f casml
	rm -f  */*.glob  */*/*.glob */*/*/*.glob 
	rm -f  */*.vo  */*/*.vo */*/*/*.vo
	rm -f  */*.vok  */*/*.vok */*/*/*.vok
	rm -f  */*.vos  */*/*.vos */*/*/*.vos 
	rm -f  */*.d  */*/*.d */*/*/*.d 
	rm -f  */.*.aux  */*/.*.aux */*/*/.*.aux 
	rm -rf _build
	rm -rf extraction/*.ml extraction/*.mli extraction/STAMP

cleancasml:
	rm -f casml
	rm -rf _build

