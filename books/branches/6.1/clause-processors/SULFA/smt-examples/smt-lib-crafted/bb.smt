(benchmark bb.smt
  :source {
Hand-crafted bit-vector benchmarks.  Some are from the SVC benchmark suite.
Contributed by Vijay Ganesh (vganesh@stanford.edu).  Translated into SMT-LIB
format by Clark Barrett using CVC Lite.

}
  :status unsat
:difficulty { 0 }
:category { crafted }
  :logic QF_UFBV[32]
  :formula
(flet ($cvcl_0 (= (extract[1:1] (extract[2:0] bv1)) (extract[0:0] bv1))) (flet ($cvcl_1 (= (extract[1:1] (extract[2:0] bv7)) (extract[0:0] bv1))) (flet ($cvcl_4 (or (and (not $cvcl_0) $cvcl_1)  (and $cvcl_0 (not $cvcl_1)) )) (flet ($cvcl_2 (= (extract[0:0] (extract[2:0] bv1)) (extract[0:0] bv1))) (flet ($cvcl_3 (= (extract[0:0] (extract[2:0] bv7)) (extract[0:0] bv1))) (flet ($cvcl_5 (= (ite (or (and $cvcl_2 $cvcl_3)  (and (or (and (not $cvcl_2) $cvcl_3)  (and $cvcl_2 (not $cvcl_3)) ) (= (extract[0:0] bv0) (extract[0:0] bv1))) ) (extract[0:0] bv1) (extract[0:0] bv0)) (extract[0:0] bv1))) (not (= (ite (or (and (not $cvcl_4) $cvcl_5)  (and $cvcl_4 (not $cvcl_5)) ) (extract[0:0] bv1) (extract[0:0] bv0)) (extract[0:0] bv0)))))))))
)
