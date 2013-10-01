(benchmark bitvec3.smt
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
  :extrafuns ((b BitVec[32]))
  :extrafuns ((c1 BitVec[32]))
  :extrafuns ((c2 BitVec[32]))
  :extrafuns ((out BitVec[32]))
  :extrafuns ((carry BitVec[32]))
  :formula
(let (?cvcl_0 (extract[1:0] b)) (let (?cvcl_1 (extract[2:0] c1)) (let (?cvcl_3 (concat (extract[0:0] bv0) (extract[1:0] bv0))) (let (?cvcl_2 (extract[2:0] c2)) (flet ($cvcl_4 (= (extract[0:0] c1) (extract[0:0] bv1))) (flet ($cvcl_5 (= (extract[0:0] c2) (extract[0:0] bv1))) (let (?cvcl_6 (extract[0:0] carry)) (let (?cvcl_7 (extract[1:1] c1)) (flet ($cvcl_11 (= ?cvcl_7 (extract[0:0] bv1))) (let (?cvcl_8 (extract[1:1] c2)) (flet ($cvcl_10 (= ?cvcl_8 (extract[0:0] bv0))) (flet ($cvcl_9 (= ?cvcl_7 (extract[0:0] bv0))) (flet ($cvcl_12 (= ?cvcl_8 (extract[0:0] bv1))) (flet ($cvcl_14 (or (and $cvcl_11 $cvcl_10)  (and $cvcl_9 $cvcl_12) )) (flet ($cvcl_13 (= ?cvcl_6 (extract[0:0] bv1))) (let (?cvcl_15 (extract[1:1] carry)) (let (?cvcl_16 (extract[2:2] c1)) (flet ($cvcl_20 (= ?cvcl_16 (extract[0:0] bv1))) (let (?cvcl_17 (extract[2:2] c2)) (flet ($cvcl_19 (= ?cvcl_17 (extract[0:0] bv0))) (flet ($cvcl_18 (= ?cvcl_16 (extract[0:0] bv0))) (flet ($cvcl_21 (= ?cvcl_17 (extract[0:0] bv1))) (flet ($cvcl_22 (= ?cvcl_15 (extract[0:0] bv1))) (not (implies (and (= (extract[1:0] a) (extract[1:0] bv3)) (= ?cvcl_0 (extract[1:0] bv3))) (implies (and (and (and (and (and (and (and (if_then_else (= (extract[0:0] a) (extract[0:0] bv1)) (= ?cvcl_1 (concat (extract[0:0] bv0) ?cvcl_0)) (= ?cvcl_1 ?cvcl_3)) (if_then_else (= (extract[1:1] a) (extract[0:0] bv1)) (= ?cvcl_2 (concat ?cvcl_0 (extract[0:0] bv0))) (= ?cvcl_2 ?cvcl_3))) (= (extract[0:0] out) (ite (or $cvcl_4  $cvcl_5 ) (extract[0:0] bv1) (extract[0:0] bv0)))) (= ?cvcl_6 (ite (and $cvcl_4 $cvcl_5) (extract[0:0] bv1) (extract[0:0] bv0)))) (= (extract[1:1] out) (ite (or (and (= ?cvcl_6 (extract[0:0] bv0)) $cvcl_14)  (and $cvcl_13 (and $cvcl_9 $cvcl_10)) ) (extract[0:0] bv1) (extract[0:0] bv0)))) (= ?cvcl_15 (ite (or (and $cvcl_11 $cvcl_12)  (and $cvcl_13 $cvcl_14) ) (extract[0:0] bv1) (extract[0:0] bv0)))) (= (extract[2:2] out) (ite (or (and (= ?cvcl_15 (extract[0:0] bv0)) (or (and $cvcl_20 $cvcl_19)  (and $cvcl_18 $cvcl_21) ))  (and $cvcl_22 (and $cvcl_18 $cvcl_19)) ) (extract[0:0] bv1) (extract[0:0] bv0)))) (= (extract[2:2] carry) (ite (or (and $cvcl_20 $cvcl_21)  (and $cvcl_22 (or $cvcl_20  $cvcl_21 )) ) (extract[0:0] bv1) (extract[0:0] bv0)))) (and (= (extract[2:0] out) (extract[2:0] bv1)) (= (extract[2:0] carry) (extract[2:0] bv6)))))))))))))))))))))))))))))
)
