(IN-PACKAGE "ACL2")

(INCLUDE-BOOK "source_shallow" :DIR :BOOKS)

(INCLUDE-BOOK "computed-hints" :DIR :BOOKS)

(DEFUND |itr_tmp_11| NIL (LIST 0 1))

(DEFUN |$itr_loop_iter_fibs_3| (|tmp_10| |$limit| |hist_2|)
  (DECLARE
    (XARGS :MEASURE (ACL2-COUNT (|+| 1 |$limit| (|-| |tmp_10|))) :HINTS
      (MEASURE-HINT)))
  (IF (NOT (AND (NATP |tmp_10|) (NATP |$limit|) (TRUE-LISTP |hist_2|)))
    (LIST 0 0)
    (IF (> |tmp_10| |$limit|) |hist_2|
      (LET
        ((|$arm-result|
           (COND
             ((< |tmp_10| 2)
               (NTH (NAT-REP (REVERSE (LIST (= (LOGHEAD 1 |tmp_10|) 1))))
                 (|itr_tmp_11|)))
             (T
               (C-WORD-+ 8
                 (NTH
                   (NAT-REP
                     (REVERSE
                       (LIST (= (LOGHEAD 1 (C-WORD-- 32 |tmp_10| 1)) 1))))
                   |hist_2|)
                 (NTH
                   (NAT-REP
                     (REVERSE
                       (LIST (= (LOGHEAD 1 (C-WORD-- 32 |tmp_10| 2)) 1))))
                   |hist_2|))))))
        (|$itr_loop_iter_fibs_3| (|1+| |tmp_10|) |$limit|
          (UPDATE-NTH (LOGHEAD 1 |tmp_10|) |$arm-result| |hist_2|))))))

(DEFUND |itr_iter_fibs_3| (|tmp_10|)
  (IF (NOT (NATP |tmp_10|)) (LIST 0 0)
    (|$itr_loop_iter_fibs_3| 0 |tmp_10| (LIST 0 0))))

(DEFUN |$itr_0_typep| (X) (AND (NATP X) (< X 4294967296)))

(DEFUND |itr_fib| (|i|)
  (IF (NOT (AND (|$itr_0_typep| |i|))) 0
    (LET* ((|tmp_8| (|itr_iter_fibs_3| |i|)))
      (NTH (NAT-REP (REVERSE (LIST (= (LOGHEAD 1 |i|) 1)))) |tmp_8|))))
