(benchmark bitops1.smt
  :source {
Hand-crafted bit-vector benchmarks.  Some are from the SVC benchmark suite.
Contributed by Vijay Ganesh (vganesh@stanford.edu).  Translated into SMT-LIB
format by Clark Barrett using CVC Lite.

}
  :status unsat
:difficulty { 0 }
:category { crafted }
  :logic QF_UFBV[32]
  :extrafuns ((x BitVec[5]))
  :extrafuns ((y BitVec[4]))
  :extrafuns ((yy BitVec[3]))
  :formula
(let (?cvcl_0 (concat x (extract[3:0] bv0))) (let (?cvcl_3 (concat (extract[2:0] bv0) (bvnot y))) (let (?cvcl_1 (concat ?cvcl_3 (extract[1:0] bv3))) (let (?cvcl_2 (concat (extract[2:0] bv0) (bvnot (extract[3:2] y)))) (let (?cvcl_4 (bvadd x ?cvcl_2)) (not (and (and (and (= (extract[8:4] (bvadd ?cvcl_0 ?cvcl_1)) ?cvcl_4) (= (extract[8:4] (bvadd ?cvcl_0 (bvadd ?cvcl_1 (concat (extract[0:0] bv0) (concat y (extract[3:0] bv0)))))) (bvadd x (bvadd (concat (extract[0:0] bv0) y) ?cvcl_2)))) (= (extract[8:4] (bvadd ?cvcl_0 (concat (concat (extract[2:0] bv0) (bvnot yy)) (extract[2:0] bv7)))) (bvadd x (concat (extract[2:0] bv0) (bvnot (extract[2:1] yy)))))) (= (extract[7:3] (bvadd (concat x (extract[2:0] bv0)) (concat ?cvcl_3 (extract[0:0] bv0)))) ?cvcl_4))))))))
)
