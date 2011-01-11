(IN-PACKAGE "ACL2")

(INCLUDE-BOOK "source_shallow" :DIR :BOOKS)

(INCLUDE-BOOK "computed-hints" :DIR :BOOKS)

(DEFUN |$itr_loop_iter_idx_facs_3| (|tmp_12| |$limit| |hist_2|)
  (DECLARE
    (XARGS :MEASURE (ACL2-COUNT (|+| 1 |$limit| (|-| |tmp_12|))) :HINTS
      (MEASURE-HINT)))
  (IF (NOT (AND (NATP |tmp_12|) (NATP |$limit|) (TRUE-LISTP |hist_2|)))
    (LIST (LIST 0) (LIST 0))
    (IF (> |tmp_12| |$limit|) |hist_2|
      (LET
        ((|$arm-result|
           (COND ((< |tmp_12| 1) (LIST 0 1))
             (T
               (LET* ((|idx_1| (C-WORD-+ 8 (NTH 0 (NTH 0 |hist_2|)) 1)))
                 (LIST |idx_1| (C-WORD-* 8 (NTH 0 (NTH 1 |hist_2|)) |idx_1|)))))))
        (|$itr_loop_iter_idx_facs_3| (|1+| |tmp_12|) |$limit|
          (LIST
            (UPDATE-NTH (LOGHEAD 0 |tmp_12|) (NTH 0 |$arm-result|)
              (NTH 0 |hist_2|))
            (UPDATE-NTH (LOGHEAD 0 |tmp_12|) (NTH 1 |$arm-result|)
              (NTH 1 |hist_2|))))))))

(DEFUND |itr_iter_idx_facs_3| (|tmp_12|)
  (IF (NOT (NATP |tmp_12|)) (LIST (LIST 0) (LIST 0))
    (|$itr_loop_iter_idx_facs_3| 0 |tmp_12| (LIST (LIST 0) (LIST 0)))))

(DEFUN |$itr_0_typep| (X) (AND (NATP X) (< X 4294967296)))

(DEFUND |itr_fac| (|i|)
  (IF (NOT (AND (|$itr_0_typep| |i|))) 0
    (LET*
      ((|tmp_11|
         (LET* ((|tmp_10| (|itr_iter_idx_facs_3| |i|))) (NTH 1 |tmp_10|))))
      (NTH 0 |tmp_11|))))
