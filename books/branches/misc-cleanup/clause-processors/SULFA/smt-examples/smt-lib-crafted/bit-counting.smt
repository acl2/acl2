(benchmark bit_counting.smt
  :source {
Hand-crafted bit-vector benchmarks.  Some are from the SVC benchmark suite.
Contributed by Vijay Ganesh (vganesh@stanford.edu).  Translated into SMT-LIB
format by Clark Barrett using CVC Lite.

}
  :status unsat
:difficulty { 0 }
:category { crafted }
  :logic QF_UFBV[32]
  :extrafuns ((B0 BitVec[32]))
  :extrafuns ((B1 BitVec[32]))
  :extrafuns ((B2 BitVec[32]))
  :extrafuns ((B3 BitVec[32]))
  :extrafuns ((B4 BitVec[32]))
  :extrafuns ((C1 BitVec[32]))
  :extrafuns ((C2 BitVec[32]))
  :extrafuns ((C3 BitVec[32]))
  :extrafuns ((C4 BitVec[32]))
  :extrafuns ((C5 BitVec[32]))
  :extrafuns ((v BitVec[32]))
  :extrafuns ((x BitVec[8]))
  :extrafuns ((y BitVec[8]))
  :extrafuns ((z BitVec[8]))
  :extrafuns ((k BitVec[31]))
  :assumption
(= x (extract[7:0] bv15))
  :assumption
(= B0 (extract[31:0] bv1431655765))
  :assumption
(= B1 (extract[31:0] bv858993459))
  :assumption
(= B2 (extract[31:0] bv252645135))
  :assumption
(= B3 (extract[31:0] bv16711935))
  :assumption
(= B4 (extract[31:0] bv65535))
  :assumption
(= k (extract[30:0] bv0))
  :assumption
(= v (extract[31:0] bv252645135))
  :assumption
(= C1 (bvadd (bvand (shift_right0 v 1) B0) (bvand v B0)))
  :assumption
(= C2 (bvadd (bvand (shift_right0 C1 2) B1) (bvand C1 B1)))
  :assumption
(= C3 (bvadd (bvand (shift_right0 C2 4) B2) (bvand C2 B2)))
  :assumption
(= C4 (bvadd (bvand (shift_right0 C3 8) B3) (bvand C3 B3)))
  :assumption
(= C5 (bvadd (bvand (shift_right0 C4 16) B4) (bvand C4 B4)))
  :formula
(not (= C5 (bvadd (concat k (extract[31:31] v)) (bvadd (concat k (extract[30:30] v)) (bvadd (concat k (extract[29:29] v)) (bvadd (concat k (extract[28:28] v)) (bvadd (concat k (extract[27:27] v)) (bvadd (concat k (extract[26:26] v)) (bvadd (concat k (extract[25:25] v)) (bvadd (concat k (extract[24:24] v)) (bvadd (concat k (extract[23:23] v)) (bvadd (concat k (extract[22:22] v)) (bvadd (concat k (extract[21:21] v)) (bvadd (concat k (extract[20:20] v)) (bvadd (concat k (extract[19:19] v)) (bvadd (concat k (extract[18:18] v)) (bvadd (concat k (extract[17:17] v)) (bvadd (concat k (extract[16:16] v)) (bvadd (concat k (extract[15:15] v)) (bvadd (concat k (extract[14:14] v)) (bvadd (concat k (extract[13:13] v)) (bvadd (concat k (extract[12:12] v)) (bvadd (concat k (extract[11:11] v)) (bvadd (concat k (extract[10:10] v)) (bvadd (concat k (extract[9:9] v)) (bvadd (concat k (extract[8:8] v)) (bvadd (concat k (extract[7:7] v)) (bvadd (concat k (extract[6:6] v)) (bvadd (concat k (extract[5:5] v)) (bvadd (concat k (extract[4:4] v)) (bvadd (concat k (extract[3:3] v)) (bvadd (concat k (extract[2:2] v)) (bvadd (concat k (extract[1:1] v)) (concat k (extract[0:0] v)))))))))))))))))))))))))))))))))))
)
