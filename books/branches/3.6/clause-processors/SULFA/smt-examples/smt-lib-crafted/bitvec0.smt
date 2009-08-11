(benchmark bitvec0.smt
  :source {
Hand-crafted bit-vector benchmarks.  Some are from the SVC benchmark suite.
Contributed by Vijay Ganesh (vganesh@stanford.edu).  Translated into SMT-LIB
format by Clark Barrett using CVC Lite.

}
  :status unsat
:difficulty { 0 }
:category { crafted }
  :logic QF_UFBV[32]
  :extrafuns ((a BitVec[32]))
  :extrafuns ((t BitVec[32]))
  :extrafuns ((b BitVec[32]))
  :extrafuns ((aa BitVec[32]))
  :extrafuns ((c BitVec[32]))
  :extrafuns ((d BitVec[32]))
  :extrafuns ((aaaa BitVec[32]))
  :extrafuns ((bbb BitVec[32]))
  :extrafuns ((aaa BitVec[32]))
  :extrafuns ((z BitVec[32]))
  :formula
(let (?cvcl_0 (extract[6:2] a)) (let (?cvcl_1 (extract[2:2] t)) (let (?cvcl_2 (extract[6:6] t)) (let (?cvcl_3 (extract[2:0] b)) (let (?cvcl_4 (extract[2:0] c)) (not (and (and (and (if_then_else (= (concat (concat (extract[0:0] bv0) (extract[3:2] a)) (extract[6:5] a)) ?cvcl_0) (= ?cvcl_0 (extract[4:0] bv0)) (if_then_else (or (or (= (extract[2:0] bv2) (extract[2:0] bv6))  (= (extract[2:0] bv0) (extract[2:0] bv6)) )  (= (extract[2:0] bv7) (extract[2:0] bv6)) ) false true)) (and (if_then_else (= (concat (extract[3:2] t) (extract[6:5] t)) (extract[5:2] t)) (= ?cvcl_1 ?cvcl_2) true) (if_then_else (= (extract[4:0] t) (extract[6:2] t)) (and (and (= ?cvcl_1 (extract[4:4] t)) (= (extract[0:0] t) ?cvcl_2)) (= (extract[1:1] t) (extract[5:5] t))) true))) (implies (and (and (= ?cvcl_3 (extract[2:0] aa)) (= ?cvcl_4 ?cvcl_3)) (= ?cvcl_4 (extract[2:0] d))) (= (extract[1:1] d) (extract[1:1] aa)))) (and (and (and (if_then_else (= (extract[2:0] bv7) (extract[2:0] aaaa)) (= (extract[0:0] bv1) (extract[1:1] aaaa)) true) (if_then_else (= (extract[2:0] bbb) (extract[2:0] aaa)) (= (extract[1:1] bbb) (extract[1:1] aaa)) true)) (= (concat (concat (concat (extract[2:0] bv4) (extract[0:0] bv1)) (extract[0:0] bv1)) (extract[1:0] bv2)) (concat (concat (extract[0:0] bv1) (extract[4:0] bv7)) (extract[0:0] bv0)))) (if_then_else (= (extract[1:0] bv3) (extract[1:0] z)) (= (extract[0:0] bv1) (extract[0:0] z)) true)))))))))
)
