(benchmark bitvec4.smt
  :source {
Hand-crafted bit-vector benchmarks.  Some are from the SVC benchmark suite.
Contributed by Vijay Ganesh (vganesh@stanford.edu).  Translated into SMT-LIB
format by Clark Barrett using CVC Lite.

}
  :status unsat
:difficulty { 0 }
:category { crafted }
  :logic QF_UFBV[32]
  :extrafuns ((e BitVec[32]))
  :extrafuns ((a BitVec[32]))
  :extrafuns ((c BitVec[32]))
  :extrafuns ((b BitVec[32]))
  :formula
(let (?cvcl_2 (extract[7:0] a)) (let (?cvcl_0 (extract[1:0] c)) (let (?cvcl_1 (extract[1:0] b)) (not (and (implies (= (extract[15:0] e) (extract[23:8] e)) (= (extract[5:2] e) (extract[21:18] e))) (implies (and (= ?cvcl_2 (concat (concat (concat ?cvcl_0 ?cvcl_1) ?cvcl_0) ?cvcl_1)) (= (extract[31:0] c) (concat (concat (concat ?cvcl_2 ?cvcl_2) ?cvcl_2) ?cvcl_2))) (= (extract[11:8] c) (extract[31:28] c))))))))
)
