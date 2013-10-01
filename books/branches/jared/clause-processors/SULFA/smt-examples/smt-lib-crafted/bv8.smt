(benchmark bv8.smt
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
(flet ($cvcl_0 (= (extract[0:0] (extract[2:0] bv2)) (extract[0:0] bv1))) (not (= (ite (not (= (ite (= (ite (not (or $cvcl_0  (and (and (= (extract[0:0] (extract[2:0] bv5)) (extract[0:0] bv1)) (not $cvcl_0)) (= (extract[0:0] bv0) (extract[0:0] bv1))) )) (extract[0:0] bv1) (extract[0:0] bv0)) (extract[0:0] bv1)) (extract[0:0] bv1) (extract[0:0] bv0)) (extract[0:0] bv1))) (extract[0:0] bv1) (extract[0:0] bv0)) (extract[0:0] bv0))))
)
