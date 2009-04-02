(benchmark bitvec1.smt
  :source {
Hand-crafted bit-vector benchmarks.  Some are from the SVC benchmark suite.
Contributed by Vijay Ganesh (vganesh@stanford.edu).  Translated into SMT-LIB
format by Clark Barrett using CVC Lite.

}
  :status unsat
:difficulty { 0 }
:category { crafted }
  :logic QF_UFBV[32]
  :extrafuns ((a BitVec[32]))
  :extrafuns ((b BitVec[32]))
  :extrafuns ((c BitVec[32]))
  :extrafuns ((res BitVec[32]))
  :formula
(flet ($cvcl_1 (= (extract[0:0] a) (extract[0:0] bv1))) (flet ($cvcl_2 (= (extract[0:0] b) (extract[0:0] bv1))) (let (?cvcl_0 (extract[0:0] c)) (flet ($cvcl_6 (= ?cvcl_0 (extract[0:0] bv1))) (let (?cvcl_3 (extract[0:0] res)) (flet ($cvcl_4 (= (extract[1:1] a) (extract[0:0] bv1))) (flet ($cvcl_5 (= (extract[1:1] b) (extract[0:0] bv1))) (flet ($cvcl_8 (if_then_else $cvcl_4 (not $cvcl_5) $cvcl_5)) (let (?cvcl_7 (extract[1:1] c)) (let (?cvcl_9 (extract[1:1] res)) (not (implies (and (and (and (= (extract[1:0] a) (extract[1:0] bv1)) (= (extract[1:0] b) (extract[1:0] bv1))) (and (if_then_else (and $cvcl_1 $cvcl_2) $cvcl_6 (= ?cvcl_0 (extract[0:0] bv0))) (if_then_else (if_then_else $cvcl_1 (not $cvcl_2) $cvcl_2) (= ?cvcl_3 (extract[0:0] bv1)) (= ?cvcl_3 (extract[0:0] bv0))))) (and (if_then_else (or (and $cvcl_4 $cvcl_5)  (and $cvcl_8 $cvcl_6) ) (= ?cvcl_7 (extract[0:0] bv1)) (= ?cvcl_7 (extract[0:0] bv0))) (if_then_else (if_then_else $cvcl_6 (not $cvcl_8) $cvcl_8) (= ?cvcl_9 (extract[0:0] bv1)) (= ?cvcl_9 (extract[0:0] bv0))))) (and (= (extract[1:0] res) (extract[1:0] bv2)) (= (extract[1:0] c) (extract[1:0] bv1)))))))))))))))
)
