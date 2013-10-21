(benchmark bitops2.smt
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
  :extrafuns ((x BitVec[7]))
  :formula
(not (and (and (or (or (or (or (or (or (or (= a (extract[2:0] bv0))  (= a (extract[2:0] bv1)) )  (= a (extract[2:0] bv2)) )  (= a (extract[2:0] bv3)) )  (= a (extract[2:0] bv4)) )  (= a (extract[2:0] bv5)) )  (= a (extract[2:0] bv6)) )  (= a (extract[2:0] bv7)) ) (or (or (or (or (or (or (or (= b (extract[2:0] bv0))  (= b (extract[2:0] bv1)) )  (= b (extract[2:0] bv2)) )  (= b (extract[2:0] bv3)) )  (= b (extract[2:0] bv4)) )  (= b (extract[2:0] bv5)) )  (= b (extract[2:0] bv6)) )  (= b (extract[2:0] bv7)) )) (implies (= x (concat (concat (extract[2:0] bv2) (bvadd a (concat (extract[0:0] bv0) (extract[1:0] b)))) (extract[0:0] bv1))) (and (= (extract[0:0] x) (extract[0:0] bv1)) (= (extract[5:5] x) (extract[0:0] bv1))))))
)
