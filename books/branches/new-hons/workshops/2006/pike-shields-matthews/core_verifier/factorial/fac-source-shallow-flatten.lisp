(IN-PACKAGE "ACL2")

(INCLUDE-BOOK "source_shallow" :DIR :BOOKS)

(INCLUDE-BOOK "computed-hints" :DIR :BOOKS)

(DEFUN |$ind_measure_idx_2_facs_2| (|$i| |$s|)
  (ACL2-COUNT
    (|+|
      (* (|+| |$i| (COND ((EQ |$s| '|facs_2|) 0) ((EQ |$s| '|idx_2|) 0))) 2)
      (COND ((EQ |$s| '|facs_2|) 1) ((EQ |$s| '|idx_2|) 0)))))

(DEFUN |$ind_block_idx_2_facs_2| (|$i| |$s|)
  (DECLARE
    (XARGS :MEASURE (|$ind_measure_idx_2_facs_2| |$i| |$s|) :HINTS
      (MEASURE-HINT)))
  (IF (NOT (AND (NATP |$i|)))
    (COND ((EQ |$s| '|idx_2|) 0) ((EQ |$s| '|facs_2|) 0))
    (COND
      ((EQ |$s| '|idx_2|)
        (LET ((|tmp_9| |$i|))
          (COND ((< |$i| 1) (NTH (LOGHEAD 0 |tmp_9|) (LIST 0)))
            (T
              (C-WORD-+ 8
                (|$ind_block_idx_2_facs_2| (|+| |tmp_9| -1) '|idx_2|) 1)))))
      ((EQ |$s| '|facs_2|)
        (LET ((|tmp_10| |$i|))
          (COND ((< |$i| 1) (NTH (LOGHEAD 0 |tmp_10|) (LIST 1)))
            (T
              (C-WORD-* 8
                (|$ind_block_idx_2_facs_2| (|+| |tmp_10| -1) '|facs_2|)
                (|$ind_block_idx_2_facs_2| (|+| |tmp_10| 0) '|idx_2|)))))))))

(DEFUND |ind_idx_2| (|$i|)
  (IF (NOT (NATP |$i|)) 0 (|$ind_block_idx_2_facs_2| |$i| '|idx_2|)))

(DEFUND |ind_facs_2| (|$i|)
  (IF (NOT (NATP |$i|)) 0 (|$ind_block_idx_2_facs_2| |$i| '|facs_2|)))

(DEFUN |$ind_0_typep| (X) (AND (NATP X) (< X 4294967296)))

(DEFUND |ind_fac| (|i|)
  (IF (NOT (AND (|$ind_0_typep| |i|))) 0 (|ind_facs_2| |i|)))
