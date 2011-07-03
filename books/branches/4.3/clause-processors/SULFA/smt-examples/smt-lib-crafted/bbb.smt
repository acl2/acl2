(benchmark bbb.smt
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
(not (= (concat (ite (not (= (ite false (extract[0:0] bv1) (extract[0:0] bv0)) (extract[0:0] bv1))) (extract[0:0] bv1) (extract[0:0] bv0)) (extract[0:0] bv0)) (extract[1:0] bv2)))
)
