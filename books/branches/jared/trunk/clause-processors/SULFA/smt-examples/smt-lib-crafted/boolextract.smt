(benchmark boolextract.smt
  :source {
Hand-crafted bit-vector benchmarks.  Some are from the SVC benchmark suite.
Contributed by Vijay Ganesh (vganesh@stanford.edu).  Translated into SMT-LIB
format by Clark Barrett using CVC Lite.

}
  :status sat
:difficulty { 0 }
:category { crafted }
  :logic QF_UFBV[32]
  :extrafuns ((ini_c_1 BitVec[32] BitVec[8]))
  :assumption
(= (extract[7:7] (ini_c_1 (extract[31:0] bv0))) bit1)
  :formula
(not false)
)
