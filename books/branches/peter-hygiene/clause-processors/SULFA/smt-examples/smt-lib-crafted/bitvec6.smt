(benchmark bitvec6.smt
  :source {
Hand-crafted bit-vector benchmarks.  Some are from the SVC benchmark suite.
Contributed by Vijay Ganesh (vganesh@stanford.edu).  Translated into SMT-LIB
format by Clark Barrett using CVC Lite.

}
  :status unsat
:difficulty { 0 }
:category { crafted }
  :logic QF_UFBV[32]
  :extrafuns ((bv BitVec[10]))
  :extrapreds ((a))
  :formula
(not (and (= (extract[5:3] (extract[7:0] bv96)) (extract[4:2] (concat (extract[6:0] bv121) (extract[0:0] bv)))) (= (concat (extract[0:0] bv1) (ite a (extract[0:0] bv0) (extract[0:0] bv1))) (extract[1:0] (ite a (extract[2:0] bv6) (extract[2:0] bv3))))))
)
