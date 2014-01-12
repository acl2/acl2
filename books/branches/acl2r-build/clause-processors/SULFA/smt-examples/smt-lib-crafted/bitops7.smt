(benchmark bitops7.smt
  :source {
Hand-crafted bit-vector benchmarks.  Some are from the SVC benchmark suite.
Contributed by Vijay Ganesh (vganesh@stanford.edu).  Translated into SMT-LIB
format by Clark Barrett using CVC Lite.

}
  :status sat
:difficulty { 0 }
:category { crafted }
  :logic QF_UFBV[32]
  :extrafuns ((x BitVec[3]))
  :extrafuns ((y BitVec[2]))
  :formula
(not (implies (= (extract[2:2] x) (extract[0:0] bv0)) (= (extract[5:5] (bvadd (bvmul (extract[5:0] bv10) (concat (extract[2:0] bv0) x)) (concat (extract[3:0] bv0) y))) (extract[0:0] bv0))))
)
