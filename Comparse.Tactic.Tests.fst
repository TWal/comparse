module Comparse.Tactic.Tests

open Comparse.Bytes.Typeclass
open Comparse.Parser
open Comparse.Tactic

(*** Features test ***)

assume val test_ni: Type0
assume val test_ne: Type0
assume val test_ii: #bytes:Type0 -> {|bytes_like bytes|} -> Type0
assume val test_ie: #bytes:Type0 -> {|bytes_like bytes|} -> Type0
assume val test_ei: bytes:Type0 -> {|bytes_like bytes|} -> Type0
assume val test_ee: bytes:Type0 -> {|bytes_like bytes|} -> Type0

assume val ps_test_ni: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes test_ni
assume val ps_test_ne: bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes test_ne
assume val ps_test_ii: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes (test_ii #bytes)
assume val ps_test_ie: bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes (test_ie #bytes)
assume val ps_test_ei: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes (test_ei bytes)
assume val ps_test_ee: bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes (test_ee bytes)

noeq type test_explicit_implicit (bytes:Type0) {|bytes_like bytes|} = {
  f_ni: test_ni;
  f_ne: test_ne;
  f_ii: test_ii #bytes;
  f_ie: test_ie #bytes;
  f_ei: test_ei bytes;
  f_ee: test_ei bytes;
}

#push-options "--fuel 0 --ifuel 0 --print_implicits"
%splice [ps_test_explicit_implicit] (gen_parser (`test_explicit_implicit))
#pop-options

assume val test_dep_nat_n: nat -> Type0
assume val test_dep_nat_i: #bytes:Type0 -> {|bytes_like bytes|} -> nat -> Type0
assume val test_dep_nat_e: bytes:Type0 -> {|bytes_like bytes|} -> nat -> Type0

assume val ps_test_dep_nat_n: #bytes:Type0 -> {|bytes_like bytes|} -> n:nat -> parser_serializer bytes (test_dep_nat_n n)
assume val ps_test_dep_nat_i: #bytes:Type0 -> {|bytes_like bytes|} -> n:nat -> parser_serializer bytes (test_dep_nat_i #bytes n)
assume val ps_test_dep_nat_e: #bytes:Type0 -> {|bytes_like bytes|} -> n:nat -> parser_serializer bytes (test_dep_nat_e bytes n)

noeq type test_dep_fixed (bytes:Type0) {|bytes_like bytes|} = {
  f_n: test_dep_nat_n 42;
  f_i: test_dep_nat_i #bytes 1337;
  f_e: test_dep_nat_e bytes 256;
}

#push-options "--fuel 0 --ifuel 0 --print_implicits"
%splice [ps_test_dep_fixed] (gen_parser (`test_dep_fixed))
#pop-options

noeq type test_dep_dep (bytes:Type0) {|bytes_like bytes|} (n:nat) = {
  f_n: test_dep_nat_n n;
  f_i: test_dep_nat_i #bytes (n+1);
  f_e: test_dep_nat_e bytes (n+n);
}

#push-options "--fuel 0 --ifuel 0 --print_implicits"
%splice [ps_test_dep_dep] (gen_parser (`test_dep_dep))
#pop-options

noeq type test_no_bytes = {
  f_ni: test_ni;
  f_ne: test_ne;
  f_dn: test_dep_nat_n 256;
}

#push-options "--fuel 0 --ifuel 0 --print_implicits"
%splice [ps_test_no_bytes] (gen_parser (`test_no_bytes))
#pop-options

noeq type test_no_bytes_dep (n:nat) = {
  f_nodep: test_dep_nat_n 256;
  f_dep: test_dep_nat_n n;
}

#push-options "--fuel 0 --ifuel 0 --print_implicits"
%splice [ps_test_no_bytes_dep] (gen_parser (`test_no_bytes_dep))
#pop-options

assume val ps_option: #bytes:Type0 -> {|bytes_like bytes|} -> #a:Type -> parser_serializer bytes a -> parser_serializer bytes (option a)

noeq type test_with_parser (bytes:Type0) {|bytes_like bytes|} (n:nat) = {
  [@@@ with_parser #bytes (ps_option ps_test_ni)]
  f0: option test_ni;
  [@@@ with_parser #bytes (ps_option ps_test_ei)]
  f1: option (test_ei bytes);
  [@@@ with_parser #bytes (ps_option (ps_test_dep_nat_e 256))]
  f2: option (test_dep_nat_e bytes 256);
  [@@@ with_parser #bytes (ps_option (ps_test_dep_nat_e n))]
  f3: option (test_dep_nat_e bytes n);
}

#push-options "--fuel 0 --ifuel 0"
%splice [ps_test_with_parser] (gen_parser (`test_with_parser))
#pop-options

type test_tag_unit =
  | TagUnit1: unit -> test_tag_unit
  | TagUnit2: unit -> test_tag_unit
  | TagUnit3: unit -> test_tag_unit
  | TagUnit4: unit -> test_tag_unit

#push-options "--fuel 0 --ifuel 1" // --print_implicits"
%splice [ps_test_tag_unit] (gen_parser (`test_tag_unit))
#pop-options

type test_tag_simple =
  | TagSimple1: test_tag_simple
  | TagSimple2: test_tag_simple
  | TagSimple3: test_tag_simple
  | TagSimple4: test_tag_simple

#push-options "--fuel 0 --ifuel 1 --print_implicits"
%splice [ps_test_tag_simple] (gen_parser (`test_tag_simple))
#pop-options

noeq type test_sum_no_annot (bytes:Type0) {|bytes_like bytes|} =
  | TestSumNoAnnot_1: test_ni -> test_ei bytes -> test_sum_no_annot bytes
  | TestSumNoAnnot_2: test_ni -> test_sum_no_annot bytes
  | TestSumNoAnnot_3: test_dep_nat_e bytes 256 -> test_ei bytes -> test_sum_no_annot bytes

#push-options "--fuel 0 --ifuel 1 --print_implicits"
%splice [ps_test_sum_no_annot] (gen_parser (`test_sum_no_annot))
#pop-options

noeq type test_sum_num_annot (bytes:Type0) {|bytes_like bytes|} =
  | TestSumNumAnnot_1: [@@@ with_tag #(nat_lbytes 4) 42] test_ni -> test_ei bytes -> test_sum_num_annot bytes
  | TestSumNumAnnot_2: [@@@ with_tag #(nat_lbytes 4) 1337] test_ni -> test_sum_num_annot bytes
  | TestSumNumAnnot_3: [@@@ with_tag #(nat_lbytes 4) 123456789] test_dep_nat_e bytes 256 -> test_ei bytes -> test_sum_num_annot bytes

#push-options "--fuel 0 --ifuel 1" // --print_implicits"
%splice [ps_test_sum_num_annot] (gen_parser (`test_sum_num_annot))
#pop-options

noeq type test_sum_tag_annot (bytes:Type0) {|bytes_like bytes|} =
  | TestSumTagAnnot_1: [@@@ with_tag TagSimple1] test_ni -> test_ei bytes -> test_sum_tag_annot bytes
  | TestSumTagAnnot_2: [@@@ with_tag TagSimple2] test_ni -> test_sum_tag_annot bytes
  | TestSumTagAnnot_3: [@@@ with_tag TagSimple3] test_dep_nat_e bytes 256 -> test_ei bytes -> test_sum_tag_annot bytes

#push-options "--fuel 0 --ifuel 1 --print_implicits"
%splice [ps_test_sum_tag_annot] (gen_parser (`test_sum_tag_annot))
#pop-options

noeq type test_sum_dep (bytes:Type0) {|bytes_like bytes|} (n:nat) =
  | TestSumDep_1: test_ni -> test_ei bytes -> test_sum_dep bytes n
  | TestSumDep_2: test_ni -> test_sum_dep bytes n
  | TestSumDep_3: test_dep_nat_e bytes 256 -> test_ei bytes -> test_sum_dep bytes n
  | TestSumDep_4: test_dep_nat_e bytes n -> test_dep_nat_e bytes (n+n) -> test_sum_dep bytes n

#push-options "--fuel 0 --ifuel 1 --print_implicits"
%splice [ps_test_sum_dep] (gen_parser (`test_sum_dep))
#pop-options

(*** Stress test ***)

noeq type test_big_record (bytes:Type0) {|bytes_like bytes|} = {
  f0:  test_ni;f1:  test_ni;f2:  test_ni;f3:  test_ni;f4:  test_ni;f5:  test_ni;f6:  test_ni;f7:  test_ni;
  f8:  test_ni;f9:  test_ni;f10: test_ni;f11: test_ni;f12: test_ni;f13: test_ni;f14: test_ni;f15: test_ni;
  f16: test_ni;f17: test_ni;f18: test_ni;f19: test_ni;f20: test_ni;f21: test_ni;f22: test_ni;f23: test_ni;
  f24: test_ni;f25: test_ni;f26: test_ni;f27: test_ni;f28: test_ni;f29: test_ni;f30: test_ni;f31: test_ni;
}

#push-options "--fuel 0 --ifuel 0 --print_implicits"
%splice [ps_test_big_record] (gen_parser (`test_big_record))
#pop-options

noeq type test_big_sum (bytes:Type0) {|bytes_like bytes|} =
  | TestBigSum_0:  test_ni -> test_big_sum bytes
  | TestBigSum_1:  test_ni -> test_big_sum bytes
  | TestBigSum_2:  test_ni -> test_big_sum bytes
  | TestBigSum_3:  test_ni -> test_big_sum bytes
  | TestBigSum_4:  test_ni -> test_big_sum bytes
  | TestBigSum_5:  test_ni -> test_big_sum bytes
  | TestBigSum_6:  test_ni -> test_big_sum bytes
  | TestBigSum_7:  test_ni -> test_big_sum bytes
  | TestBigSum_8:  test_ni -> test_big_sum bytes
  | TestBigSum_9:  test_ni -> test_big_sum bytes
  | TestBigSum_10: test_ni -> test_big_sum bytes
  | TestBigSum_11: test_ni -> test_big_sum bytes
  | TestBigSum_12: test_ni -> test_big_sum bytes
  | TestBigSum_13: test_ni -> test_big_sum bytes
  | TestBigSum_14: test_ni -> test_big_sum bytes
  | TestBigSum_15: test_ni -> test_big_sum bytes

#push-options "--fuel 0 --ifuel 1 --print_implicits"
%splice [ps_test_big_sum] (gen_parser (`test_big_sum))
#pop-options
