(IN-PACKAGE "ACL2")

; Edited by Matt K.:
; (INCLUDE-BOOK "source_shallow" :DIR :BOOKS)
(INCLUDE-BOOK "../books/source_shallow")

; Edited by Matt K.:
; (INCLUDE-BOOK "computed-hints" :DIR :BOOKS)
(INCLUDE-BOOK "../books/computed-hints")

(DEFUN |$ind_measure_consts_2| (|$i| |$s|)
  (ACL2-COUNT
    (|+| (* (|+| |$i| (COND ((EQ |$s| '|consts_2|) 0))) 1)
      (COND ((EQ |$s| '|consts_2|) 0)))))

(DEFUN |$ind_block_consts_2| (|$i| |$s|)
  (DECLARE
    (XARGS :MEASURE (|$ind_measure_consts_2| |$i| |$s|) :HINTS
      (MEASURE-HINT)))
  (IF (NOT (AND (NATP |$i|))) (COND ((EQ |$s| '|consts_2|) 0))
    (COND
      ((EQ |$s| '|consts_2|)
        (LET ((|tmp_22| |$i|))
          (COND ((< |$i| 1) (NTH (LOGHEAD 0 |tmp_22|) (LIST 3084996963)))
            (T
              (C-WORD-+ 32
                (|$ind_block_consts_2| (|+| |tmp_22| -1) '|consts_2|)
                2654435769))))))))

(DEFUND |ind_consts_2| (|$i|)
  (IF (NOT (NATP |$i|)) 0 (|$ind_block_consts_2| |$i| '|consts_2|)))

(DEFUN |$ind_takes_1| (|$i|)
  (DECLARE
    (XARGS :MEASURE (ACL2-COUNT (|+| 1 44 (|-| |$i|))) :HINTS (MEASURE-HINT)))
  (IF (NOT (NATP |$i|)) NIL
    (IF (>= |$i| 44) NIL
      (CONS (|ind_consts_2| |$i|) (|$ind_takes_1| (|1+| |$i|))))))

(DEFUND |ind_inits_2| NIL (|$ind_takes_1| 0))

(DEFUND |$ind_0_typep| (X)
  (AND (TRUE-LISTP X) (NATP (NTH 0 X)) (< (NTH 0 X) 4294967296)
    (NATP (NTH 1 X)) (< (NTH 1 X) 4294967296)))

(DEFUN |$ind_measure_s_2_l_2| (|$i| |$s|)
  (ACL2-COUNT
    (|+| (* (|+| |$i| (COND ((EQ |$s| '|l_2|) 0) ((EQ |$s| '|s_2|) 0))) 2)
      (COND ((EQ |$s| '|l_2|) 1) ((EQ |$s| '|s_2|) 0)))))

(DEFUN |$ind_block_s_2_l_2| (|initl_1| |$i| |$s|)
  (DECLARE
    (XARGS :MEASURE (|$ind_measure_s_2_l_2| |$i| |$s|) :HINTS (MEASURE-HINT)))
  (IF (NOT (AND (|$ind_0_typep| |initl_1|) (NATP |$i|)))
    (COND ((EQ |$s| '|s_2|) 0) ((EQ |$s| '|l_2|) 0))
    (COND
      ((EQ |$s| '|s_2|)
        (LET ((|tmp_20| |$i|))
          (COND
            ((< |$i| 1)
              (C-WORD-<<< 32
                (C-WORD-+ 32
                  (C-WORD-+ 32 (NTH (LOGHEAD 6 |tmp_20|) (|ind_inits_2|))
                    (NTH (LOGHEAD 0 |tmp_20|) (LIST 0)))
                  (NTH (LOGHEAD 0 |tmp_20|) (LIST 0))) 3))
            ((< |$i| 44)
              (C-WORD-<<< 32
                (C-WORD-+ 32
                  (C-WORD-+ 32 (NTH (LOGHEAD 6 |tmp_20|) (|ind_inits_2|))
                    (|$ind_block_s_2_l_2| |initl_1| (|+| |tmp_20| -1) '|s_2|))
                  (|$ind_block_s_2_l_2| |initl_1| (|+| |tmp_20| -1) '|l_2|))
                3))
            (T
              (C-WORD-<<< 32
                (C-WORD-+ 32
                  (C-WORD-+ 32
                    (|$ind_block_s_2_l_2| |initl_1| (|+| |tmp_20| -44)
                      '|s_2|)
                    (|$ind_block_s_2_l_2| |initl_1| (|+| |tmp_20| -1) '|s_2|))
                  (|$ind_block_s_2_l_2| |initl_1| (|+| |tmp_20| -1) '|l_2|))
                3)))))
      ((EQ |$s| '|l_2|)
        (LET ((|tmp_21| |$i|))
          (COND
            ((< |$i| 1)
              (LET*
                ((|a_1|
                   (|$ind_block_s_2_l_2| |initl_1| (|+| |tmp_21| 0) '|s_2|))
                  (|b_1| (NTH (LOGHEAD 0 |tmp_21|) (LIST 0))))
                (C-WORD-<<< 32
                  (C-WORD-+ 32
                    (C-WORD-+ 32 (NTH (LOGHEAD 1 |tmp_21|) |initl_1|) |a_1|)
                    |b_1|)
                  (LOGHEAD 5 (C-WORD-% (C-WORD-+ 32 |a_1| |b_1|) 5)))))
            ((< |$i| 2)
              (LET*
                ((|a_2|
                   (|$ind_block_s_2_l_2| |initl_1| (|+| |tmp_21| 0) '|s_2|))
                  (|b_2|
                    (|$ind_block_s_2_l_2| |initl_1| (|+| |tmp_21| -1) '|l_2|)))
                (C-WORD-<<< 32
                  (C-WORD-+ 32
                    (C-WORD-+ 32 (NTH (LOGHEAD 1 |tmp_21|) |initl_1|) |a_2|)
                    |b_2|)
                  (LOGHEAD 5 (C-WORD-% (C-WORD-+ 32 |a_2| |b_2|) 5)))))
            (T
              (LET*
                ((|a_3|
                   (|$ind_block_s_2_l_2| |initl_1| (|+| |tmp_21| 0) '|s_2|))
                  (|b_3|
                    (|$ind_block_s_2_l_2| |initl_1| (|+| |tmp_21| -1) '|l_2|)))
                (C-WORD-<<< 32
                  (C-WORD-+ 32
                    (C-WORD-+ 32
                      (|$ind_block_s_2_l_2| |initl_1| (|+| |tmp_21| -2)
                        '|l_2|) |a_3|) |b_3|)
                  (LOGHEAD 5 (C-WORD-% (C-WORD-+ 32 |a_3| |b_3|) 5)))))))))))

(DEFUND |ind_s_2| (|initl_1| |$i|)
  (IF (NOT (NATP |$i|)) 0 (|$ind_block_s_2_l_2| |initl_1| |$i| '|s_2|)))

(DEFUND |ind_l_2| (|initl_1| |$i|)
  (IF (NOT (NATP |$i|)) 0 (|$ind_block_s_2_l_2| |initl_1| |$i| '|l_2|)))

(DEFUND |$ind_1_typep| (X)
  (AND (TRUE-LISTP X) (NATP (NTH 0 X)) (< (NTH 0 X) 256) (NATP (NTH 1 X))
    (< (NTH 1 X) 256) (NATP (NTH 2 X)) (< (NTH 2 X) 256) (NATP (NTH 3 X))
    (< (NTH 3 X) 256) (NATP (NTH 4 X)) (< (NTH 4 X) 256)))

(DEFUN |$ind_takes_2| (|$tmp_23| |$i|)
  (DECLARE
    (XARGS :MEASURE (ACL2-COUNT (|+| 1 44 (|-| |$i|))) :HINTS (MEASURE-HINT)))
  (IF (NOT (NATP |$i|)) NIL
    (IF (>= |$i| 44) NIL
      (CONS (|ind_s_2| |$tmp_23| (|+| 88 |$i|))
        (|$ind_takes_2| |$tmp_23| (|1+| |$i|))))))

(DEFUND |ind_rc6exp| (|key|)
  (IF (NOT (AND (|$ind_1_typep| |key|)))
    (LIST 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
      0 0 0 0 0 0 0 0 0 0)
    (LET*
      ((|initl|
         (C-WORD-SPLIT 32 2
           (C-WORD-APPEND (LIST 40 (C-WORD-JOIN 8 |key|) 24 0)))))
      (IF (<= 0 43) (C-VEC->>> (|$ind_takes_2| |initl| 0) 0)
        (LIST 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
          0 0 0 0 0 0 0 0 0 0 0 0)))))
