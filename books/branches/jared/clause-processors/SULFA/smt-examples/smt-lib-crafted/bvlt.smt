(benchmark bvlt.smt
  :source {
Hand-crafted bit-vector benchmarks.  Some are from the SVC benchmark suite.
Contributed by Vijay Ganesh (vganesh@stanford.edu).  Translated into SMT-LIB
format by Clark Barrett using CVC Lite.

}
  :status sat
:difficulty { 0 }
:category { crafted }
  :logic QF_UFBV[32]
  :extrafuns ((my_recv_result BitVec[32]))
  :extrafuns ((recvBuffer_0 BitVec[32]))
  :extrafuns ((smt_0x80bd7d0_0 BitVec[32]))
  :assumption
(not (= (extract[31:31] recvBuffer_0) bit1))
  :assumption
(not (= (extract[30:30] recvBuffer_0) bit1))
  :assumption
(not (= (extract[29:29] recvBuffer_0) bit1))
  :assumption
(not (= (extract[28:28] recvBuffer_0) bit1))
  :assumption
(not (= (extract[27:27] recvBuffer_0) bit1))
  :assumption
(not (= (extract[26:26] recvBuffer_0) bit1))
  :assumption
(not (= (extract[25:25] recvBuffer_0) bit1))
  :assumption
(not (= (extract[24:24] recvBuffer_0) bit1))
  :assumption
(not (= (extract[23:23] recvBuffer_0) bit1))
  :assumption
(not (= (extract[22:22] recvBuffer_0) bit1))
  :assumption
(not (= (extract[21:21] recvBuffer_0) bit1))
  :assumption
(not (= (extract[20:20] recvBuffer_0) bit1))
  :assumption
(not (= (extract[19:19] recvBuffer_0) bit1))
  :assumption
(not (= (extract[18:18] recvBuffer_0) bit1))
  :assumption
(not (= (extract[17:17] recvBuffer_0) bit1))
  :assumption
(not (= (extract[16:16] recvBuffer_0) bit1))
  :assumption
(not (= (extract[15:15] recvBuffer_0) bit1))
  :assumption
(not (= (extract[14:14] recvBuffer_0) bit1))
  :assumption
(not (= (extract[13:13] recvBuffer_0) bit1))
  :assumption
(not (= (extract[12:12] recvBuffer_0) bit1))
  :assumption
(not (= (extract[11:11] recvBuffer_0) bit1))
  :assumption
(not (= (extract[10:10] recvBuffer_0) bit1))
  :assumption
(not (= (extract[9:9] recvBuffer_0) bit1))
  :assumption
(not (= (extract[8:8] recvBuffer_0) bit1))
  :assumption
(or (bvleq my_recv_result (extract[31:0] bv3))  (= my_recv_result (extract[31:0] bv4294967295)) )
  :assumption
(not (= my_recv_result (extract[31:0] bv4294967295)))
  :assumption
(= smt_0x80bd7d0_0 (bvadd smt_0x80bd7d0_0 my_recv_result))
  :formula
(not false)
)
