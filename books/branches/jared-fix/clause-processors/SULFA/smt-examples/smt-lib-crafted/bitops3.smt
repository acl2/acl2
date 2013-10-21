(benchmark bitops3.smt
  :source {
Hand-crafted bit-vector benchmarks.  Some are from the SVC benchmark suite.
Contributed by Vijay Ganesh (vganesh@stanford.edu).  Translated into SMT-LIB
format by Clark Barrett using CVC Lite.

}
  :status unsat
:difficulty { 0 }
:category { crafted }
  :logic QF_UFBV[32]
  :extrafuns ((a BitVec[3]))
  :extrafuns ((b BitVec[3]))
  :extrafuns ((x BitVec[4]))
  :extrafuns ((y BitVec[4]))
  :extrafuns ((z BitVec[2]))
  :formula
(flet ($cvcl_0 (= x y)) (let (?cvcl_2 (concat (extract[0:0] bv0) x)) (let (?cvcl_1 (bvadd ?cvcl_2 (concat (extract[0:0] bv0) y))) (not (and (and (and (= (extract[1:1] (bvnot (concat (extract[0:0] bv0) (extract[3:3] (bvadd (concat (extract[0:0] bv0) a) (concat (extract[0:0] bv0) b)))))) (extract[0:0] bv1)) (implies $cvcl_0 (= (extract[4:4] ?cvcl_1) (extract[3:3] x)))) (implies $cvcl_0 (= ?cvcl_1 (bvmul (extract[4:0] bv2) ?cvcl_2)))) (= (extract[3:3] (bvadd (extract[3:0] bv7) (concat (extract[0:0] bv0) (concat z (extract[0:0] bv1))))) (extract[0:0] bv1)))))))
)
