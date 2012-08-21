(benchmark bitops4.smt
  :source {
Hand-crafted bit-vector benchmarks.  Some are from the SVC benchmark suite.
Contributed by Vijay Ganesh (vganesh@stanford.edu).  Translated into SMT-LIB
format by Clark Barrett using CVC Lite.

}
  :status unsat
:difficulty { 0 }
:category { crafted }
  :logic QF_UFBV[32]
  :extrafuns ((x BitVec[1]))
  :extrafuns ((y BitVec[1]))
  :extrafuns ((z BitVec[1]))
  :extrapreds ((a))
  :formula
(flet ($cvcl_0 (= x (bvadd y z))) (not (implies (and $cvcl_0 (= (bvadd (concat (extract[1:0] bv0) x) (bvadd (concat (extract[1:0] bv0) y) (concat (extract[1:0] bv0) z))) (ite a (extract[2:0] bv7) (extract[2:0] bv0)))) $cvcl_0)))
)
