(benchmark bitops0.smt
  :source {
Hand-crafted bit-vector benchmarks.  Some are from the SVC benchmark suite.
Contributed by Vijay Ganesh (vganesh@stanford.edu).  Translated into SMT-LIB
format by Clark Barrett using CVC Lite.

}
  :status unsat
:difficulty { 0 }
:category { crafted }
  :logic QF_UFBV[32]
  :extrafuns ((y BitVec[1]))
  :extrafuns ((x BitVec[2]))
  :extrafuns ((z BitVec[4]))
  :extrafuns ((d BitVec[3]))
  :extrafuns ((e BitVec[4]))
  :extrafuns ((f BitVec[3]))
  :extrafuns ((a BitVec[5]))
  :extrafuns ((b BitVec[5]))
  :extrafuns ((c BitVec[5]))
  :formula
(let (?cvcl_0 (bvadd (extract[4:0] bv7) b)) (let (?cvcl_1 (bvadd a b)) (let (?cvcl_2 (concat (extract[0:0] bv0) x)) (not (and (and (and (and (and (and (and (and (and (not (= y (bvnot y))) (= (extract[6:6] (bvnot (concat (concat x (extract[2:0] bv5)) z))) (extract[0:0] bv0))) (implies (= (extract[7:2] (bvnot (concat (concat d e) (extract[2:0] bv2)))) (concat d f)) (if_then_else (= e (extract[3:0] bv0)) (and (= d (extract[2:0] bv3)) (= f (extract[2:0] bv7))) (implies (= e (extract[3:0] bv15)) (and (= d (extract[2:0] bv4)) (= f (extract[2:0] bv1))))))) (not (= ?cvcl_0 (bvnot ?cvcl_0)))) (not (= ?cvcl_1 (bvnot ?cvcl_1)))) (implies (= ?cvcl_1 (bvadd a c)) (= b c))) (= (bvadd x (bvadd (bvnot x) (extract[1:0] bv1))) (extract[1:0] bv0))) (implies (= (extract[3:3] z) (extract[0:0] bv0)) (not (= (bvadd (extract[3:0] bv1) (bvadd (extract[3:0] bv2) (bvadd (extract[3:0] bv4) z))) (extract[3:0] bv0))))) (= (extract[5:5] (bvadd (extract[5:0] bv10) (extract[5:0] bv21))) (extract[0:0] bv0))) (implies (= (extract[1:1] x) (extract[0:0] bv0)) (= (extract[2:2] (bvadd ?cvcl_2 ?cvcl_2)) (extract[0:0] bv0))))))))
)
