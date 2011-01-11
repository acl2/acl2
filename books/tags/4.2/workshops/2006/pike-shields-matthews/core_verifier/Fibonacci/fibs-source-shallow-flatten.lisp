(IN-PACKAGE "ACL2")

(INCLUDE-BOOK "source_shallow" :DIR :BOOKS)

(INCLUDE-BOOK "computed-hints" :DIR :BOOKS)

(DEFUN |$ind_measure_fibs_2| (|$i| |$s|)
  (ACL2-COUNT
    (|+| (* (|+| |$i| (COND ((EQ |$s| '|fibs_2|) 0))) 1)
      (COND ((EQ |$s| '|fibs_2|) 0)))))

(DEFUN |$ind_block_fibs_2| (|$i| |$s|)
  (DECLARE
    (XARGS :MEASURE (|$ind_measure_fibs_2| |$i| |$s|) :HINTS (MEASURE-HINT)))
  (IF (NOT (AND (NATP |$i|))) (COND ((EQ |$s| '|fibs_2|) 0))
    (COND
      ((EQ |$s| '|fibs_2|)
        (LET ((|tmp_6| |$i|))
          (COND ((< |$i| 2) (NTH (LOGHEAD 1 |tmp_6|) (LIST 0 1)))
            (T
              (C-WORD-+ 8 (|$ind_block_fibs_2| (|+| |tmp_6| -1) '|fibs_2|)
                (|$ind_block_fibs_2| (|+| |tmp_6| -2) '|fibs_2|)))))))))

(DEFUND |ind_fibs_2| (|$i|)
  (IF (NOT (NATP |$i|)) 0 (|$ind_block_fibs_2| |$i| '|fibs_2|)))

(DEFUN |$ind_0_typep| (X) (AND (NATP X) (< X 4294967296)))

(DEFUND |ind_fib| (|i|)
  (IF (NOT (AND (|$ind_0_typep| |i|))) 0 (|ind_fibs_2| |i|)))
