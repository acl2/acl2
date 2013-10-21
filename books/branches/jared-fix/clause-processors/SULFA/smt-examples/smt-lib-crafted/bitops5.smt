(benchmark bitops5.smt
  :source {
Hand-crafted bit-vector benchmarks.  Some are from the SVC benchmark suite.
Contributed by Vijay Ganesh (vganesh@stanford.edu).  Translated into SMT-LIB
format by Clark Barrett using CVC Lite.

}
  :status unsat
:difficulty { 0 }
:category { crafted }
  :logic QF_UFBV[32]
  :extrafuns ((a BitVec[2]))
  :extrafuns ((b BitVec[2]))
  :extrafuns ((x BitVec[4]))
  :extrafuns ((y BitVec[7]))
  :extrafuns ((c BitVec[3]))
  :extrafuns ((d BitVec[3]))
  :formula
(not (and (implies (and (and (or (or (or (= a (extract[1:0] bv0))  (= a (extract[1:0] bv1)) )  (= a (extract[1:0] bv2)) )  (= a (extract[1:0] bv3)) ) (or (or (or (= b (extract[1:0] bv0))  (= b (extract[1:0] bv1)) )  (= b (extract[1:0] bv2)) )  (= b (extract[1:0] bv3)) )) (= x (concat (extract[1:0] bv2) (bvadd a b)))) (= (extract[3:3] x) (extract[0:0] bv1))) (implies (= y (concat (concat (extract[2:0] bv2) (bvadd c d)) (extract[0:0] bv1))) (= (extract[0:0] y) (extract[0:0] bv1)))))
)
