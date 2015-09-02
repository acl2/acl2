(IN-PACKAGE "ACL2")

; Edited by Matt K.:
; (INCLUDE-BOOK "source_shallow" :DIR :BOOKS)
(INCLUDE-BOOK "../books/source_shallow")

; Edited by Matt K.:
; (INCLUDE-BOOK "computed-hints" :DIR :BOOKS)
(INCLUDE-BOOK "../books/computed-hints")

(DEFUN |$ind_0_typep| (X) (AND (NATP X) (< X 4294967296)))

(DEFUN |$ind_measure_sums_4_ys_4_zs_4| (|$i| |$s|)
  (ACL2-COUNT
    (|+|
      (*
        (|+| |$i|
          (COND ((EQ |$s| '|zs_4|) 0) ((EQ |$s| '|ys_4|) 0)
            ((EQ |$s| '|sums_4|) 0))) 3)
      (COND ((EQ |$s| '|zs_4|) 2) ((EQ |$s| '|ys_4|) 1)
        ((EQ |$s| '|sums_4|) 0)))))

(DEFUN |$ind_block_sums_4_ys_4_zs_4|
  (|z_3| |y_3| |k3_2| |k2_2| |k1_2| |k0_2| |$i| |$s|)
  (DECLARE
    (XARGS :MEASURE (|$ind_measure_sums_4_ys_4_zs_4| |$i| |$s|) :HINTS
      (MEASURE-HINT)))
  (IF
    (NOT
      (AND (|$ind_0_typep| |k0_2|) (|$ind_0_typep| |k1_2|)
        (|$ind_0_typep| |k2_2|) (|$ind_0_typep| |k3_2|)
        (|$ind_0_typep| |y_3|) (|$ind_0_typep| |z_3|) (NATP |$i|)))
    (COND ((EQ |$s| '|sums_4|) 0) ((EQ |$s| '|ys_4|) 0)
      ((EQ |$s| '|zs_4|) 0))
    (COND
      ((EQ |$s| '|sums_4|)
        (LET ((|tmp_32| |$i|))
          (COND ((< |$i| 1) (NTH (LOGHEAD 0 |tmp_32|) (LIST 2654435769)))
            (T
              (C-WORD-+ 32
                (|$ind_block_sums_4_ys_4_zs_4| |z_3| |y_3| |k3_2| |k2_2|
                  |k1_2| |k0_2| (|+| |tmp_32| -1) '|sums_4|) 2654435769)))))
      ((EQ |$s| '|ys_4|)
        (LET ((|tmp_33| |$i|))
          (COND ((< |$i| 1) (NTH (LOGHEAD 0 |tmp_33|) (LIST |y_3|)))
            (T
              (LET*
                ((|z_4|
                   (|$ind_block_sums_4_ys_4_zs_4| |z_3| |y_3| |k3_2|
                     |k2_2| |k1_2| |k0_2| (|+| |tmp_33| -1) '|zs_4|)))
                (C-WORD-+ 32
                  (|$ind_block_sums_4_ys_4_zs_4| |z_3| |y_3| |k3_2| |k2_2|
                    |k1_2| |k0_2| (|+| |tmp_33| -1) '|ys_4|)
                  (C-WORD-^^
                    (C-WORD-^^ (C-WORD-+ 32 (C-WORD-<< 32 |z_4| 4) |k0_2|)
                      (C-WORD-+ 32 |z_4|
                        (|$ind_block_sums_4_ys_4_zs_4| |z_3| |y_3| |k3_2|
                          |k2_2| |k1_2| |k0_2| (|+| |tmp_33| -1) '|sums_4|)))
                    (C-WORD-+ 32 (C-WORD->> 32 |z_4| 5) |k1_2|))))))))
      ((EQ |$s| '|zs_4|)
        (LET ((|tmp_34| |$i|))
          (COND ((< |$i| 1) (NTH (LOGHEAD 0 |tmp_34|) (LIST |z_3|)))
            (T
              (LET*
                ((|y_4|
                   (|$ind_block_sums_4_ys_4_zs_4| |z_3| |y_3| |k3_2|
                     |k2_2| |k1_2| |k0_2| (|+| |tmp_34| 0) '|ys_4|)))
                (C-WORD-+ 32
                  (|$ind_block_sums_4_ys_4_zs_4| |z_3| |y_3| |k3_2| |k2_2|
                    |k1_2| |k0_2| (|+| |tmp_34| -1) '|zs_4|)
                  (C-WORD-^^
                    (C-WORD-^^ (C-WORD-+ 32 (C-WORD-<< 32 |y_4| 4) |k2_2|)
                      (C-WORD-+ 32 |y_4|
                        (|$ind_block_sums_4_ys_4_zs_4| |z_3| |y_3| |k3_2|
                          |k2_2| |k1_2| |k0_2| (|+| |tmp_34| -1) '|sums_4|)))
                    (C-WORD-+ 32 (C-WORD->> 32 |y_4| 5) |k3_2|)))))))))))

(DEFUND |ind_sums_4| (|z_3| |y_3| |k3_2| |k2_2| |k1_2| |k0_2| |$i|)
  (IF (NOT (NATP |$i|)) 0
    (|$ind_block_sums_4_ys_4_zs_4| |z_3| |y_3| |k3_2| |k2_2| |k1_2| |k0_2|
      |$i| '|sums_4|)))

(DEFUND |ind_ys_4| (|z_3| |y_3| |k3_2| |k2_2| |k1_2| |k0_2| |$i|)
  (IF (NOT (NATP |$i|)) 0
    (|$ind_block_sums_4_ys_4_zs_4| |z_3| |y_3| |k3_2| |k2_2| |k1_2| |k0_2|
      |$i| '|ys_4|)))

(DEFUND |ind_zs_4| (|z_3| |y_3| |k3_2| |k2_2| |k1_2| |k0_2| |$i|)
  (IF (NOT (NATP |$i|)) 0
    (|$ind_block_sums_4_ys_4_zs_4| |z_3| |y_3| |k3_2| |k2_2| |k1_2| |k0_2|
      |$i| '|zs_4|)))

(DEFUND |$ind_1_typep| (X)
  (AND (TRUE-LISTP X) (TRUE-LISTP (NTH 0 X)) (NATP (NTH 0 (NTH 0 X)))
    (< (NTH 0 (NTH 0 X)) 4294967296) (NATP (NTH 1 (NTH 0 X)))
    (< (NTH 1 (NTH 0 X)) 4294967296) (TRUE-LISTP (NTH 1 X))
    (NATP (NTH 0 (NTH 1 X))) (< (NTH 0 (NTH 1 X)) 4294967296)
    (NATP (NTH 1 (NTH 1 X))) (< (NTH 1 (NTH 1 X)) 4294967296)
    (NATP (NTH 2 (NTH 1 X))) (< (NTH 2 (NTH 1 X)) 4294967296)
    (NATP (NTH 3 (NTH 1 X))) (< (NTH 3 (NTH 1 X)) 4294967296)))

(DEFUND |ind_code| (|tmp_4|)
  (IF (NOT (AND (|$ind_1_typep| |tmp_4|))) (LIST 0 0)
    (LET*
      ((|tmp_5| (NTH 0 |tmp_4|)) (|y| (NTH 0 |tmp_5|)) (|z| (NTH 1 |tmp_5|))
        (|tmp_6| (NTH 1 |tmp_4|)) (|k0| (NTH 0 |tmp_6|))
        (|k1| (NTH 1 |tmp_6|)) (|k2| (NTH 2 |tmp_6|)) (|k3| (NTH 3 |tmp_6|)))
      (LIST (|ind_ys_4| |z| |y| |k3| |k2| |k1| |k0| 32)
        (|ind_zs_4| |z| |y| |k3| |k2| |k1| |k0| 32)))))

(DEFUN |$ind_measure_sums_3_ys_3_zs_3| (|$i| |$s|)
  (ACL2-COUNT
    (|+|
      (*
        (|+| |$i|
          (COND ((EQ |$s| '|zs_3|) 0) ((EQ |$s| '|ys_3|) 0)
            ((EQ |$s| '|sums_3|) 0))) 3)
      (COND ((EQ |$s| '|ys_3|) 2) ((EQ |$s| '|zs_3|) 1)
        ((EQ |$s| '|sums_3|) 0)))))

(DEFUN |$ind_block_sums_3_ys_3_zs_3|
  (|z_1| |y_1| |k3_1| |k2_1| |k1_1| |k0_1| |$i| |$s|)
  (DECLARE
    (XARGS :MEASURE (|$ind_measure_sums_3_ys_3_zs_3| |$i| |$s|) :HINTS
      (MEASURE-HINT)))
  (IF
    (NOT
      (AND (|$ind_0_typep| |k0_1|) (|$ind_0_typep| |k1_1|)
        (|$ind_0_typep| |k2_1|) (|$ind_0_typep| |k3_1|)
        (|$ind_0_typep| |y_1|) (|$ind_0_typep| |z_1|) (NATP |$i|)))
    (COND ((EQ |$s| '|sums_3|) 0) ((EQ |$s| '|ys_3|) 0)
      ((EQ |$s| '|zs_3|) 0))
    (COND
      ((EQ |$s| '|sums_3|)
        (LET ((|tmp_29| |$i|))
          (COND
            ((< |$i| 1)
              (NTH (LOGHEAD 0 |tmp_29|) (LIST (C-WORD-* 32 2654435769 32))))
            (T
              (C-WORD-- 32
                (|$ind_block_sums_3_ys_3_zs_3| |z_1| |y_1| |k3_1| |k2_1|
                  |k1_1| |k0_1| (|+| |tmp_29| -1) '|sums_3|) 2654435769)))))
      ((EQ |$s| '|ys_3|)
        (LET ((|tmp_30| |$i|))
          (COND ((< |$i| 1) (NTH (LOGHEAD 0 |tmp_30|) (LIST |y_1|)))
            (T
              (LET*
                ((|z_2|
                   (|$ind_block_sums_3_ys_3_zs_3| |z_1| |y_1| |k3_1|
                     |k2_1| |k1_1| |k0_1| (|+| |tmp_30| 0) '|zs_3|)))
                (C-WORD-- 32
                  (|$ind_block_sums_3_ys_3_zs_3| |z_1| |y_1| |k3_1| |k2_1|
                    |k1_1| |k0_1| (|+| |tmp_30| -1) '|ys_3|)
                  (C-WORD-^^
                    (C-WORD-^^ (C-WORD-+ 32 (C-WORD-<< 32 |z_2| 4) |k0_1|)
                      (C-WORD-+ 32 |z_2|
                        (|$ind_block_sums_3_ys_3_zs_3| |z_1| |y_1| |k3_1|
                          |k2_1| |k1_1| |k0_1| (|+| |tmp_30| -1) '|sums_3|)))
                    (C-WORD-+ 32 (C-WORD->> 32 |z_2| 5) |k1_1|))))))))
      ((EQ |$s| '|zs_3|)
        (LET ((|tmp_31| |$i|))
          (COND ((< |$i| 1) (NTH (LOGHEAD 0 |tmp_31|) (LIST |z_1|)))
            (T
              (LET*
                ((|y_2|
                   (|$ind_block_sums_3_ys_3_zs_3| |z_1| |y_1| |k3_1|
                     |k2_1| |k1_1| |k0_1| (|+| |tmp_31| -1) '|ys_3|)))
                (C-WORD-- 32
                  (|$ind_block_sums_3_ys_3_zs_3| |z_1| |y_1| |k3_1| |k2_1|
                    |k1_1| |k0_1| (|+| |tmp_31| -1) '|zs_3|)
                  (C-WORD-^^
                    (C-WORD-^^ (C-WORD-+ 32 (C-WORD-<< 32 |y_2| 4) |k2_1|)
                      (C-WORD-+ 32 |y_2|
                        (|$ind_block_sums_3_ys_3_zs_3| |z_1| |y_1| |k3_1|
                          |k2_1| |k1_1| |k0_1| (|+| |tmp_31| -1) '|sums_3|)))
                    (C-WORD-+ 32 (C-WORD->> 32 |y_2| 5) |k3_1|)))))))))))

(DEFUND |ind_sums_3| (|z_1| |y_1| |k3_1| |k2_1| |k1_1| |k0_1| |$i|)
  (IF (NOT (NATP |$i|)) 0
    (|$ind_block_sums_3_ys_3_zs_3| |z_1| |y_1| |k3_1| |k2_1| |k1_1| |k0_1|
      |$i| '|sums_3|)))

(DEFUND |ind_ys_3| (|z_1| |y_1| |k3_1| |k2_1| |k1_1| |k0_1| |$i|)
  (IF (NOT (NATP |$i|)) 0
    (|$ind_block_sums_3_ys_3_zs_3| |z_1| |y_1| |k3_1| |k2_1| |k1_1| |k0_1|
      |$i| '|ys_3|)))

(DEFUND |ind_zs_3| (|z_1| |y_1| |k3_1| |k2_1| |k1_1| |k0_1| |$i|)
  (IF (NOT (NATP |$i|)) 0
    (|$ind_block_sums_3_ys_3_zs_3| |z_1| |y_1| |k3_1| |k2_1| |k1_1| |k0_1|
      |$i| '|zs_3|)))

(DEFUND |ind_decode| (|tmp_1|)
  (IF (NOT (AND (|$ind_1_typep| |tmp_1|))) (LIST 0 0)
    (LET*
      ((|tmp_2| (NTH 0 |tmp_1|)) (|y| (NTH 0 |tmp_2|)) (|z| (NTH 1 |tmp_2|))
        (|tmp_3| (NTH 1 |tmp_1|)) (|k0| (NTH 0 |tmp_3|))
        (|k1| (NTH 1 |tmp_3|)) (|k2| (NTH 2 |tmp_3|)) (|k3| (NTH 3 |tmp_3|)))
      (LIST (|ind_ys_3| |z| |y| |k3| |k2| |k1| |k0| 32)
        (|ind_zs_3| |z| |y| |k3| |k2| |k1| |k0| 32)))))
