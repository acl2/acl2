(IN-PACKAGE "ACL2")

; Edited by Matt K.:
; (INCLUDE-BOOK "source_shallow" :DIR :BOOKS)
(INCLUDE-BOOK "../books/source_shallow")

; Edited by Matt K.:
; (INCLUDE-BOOK "computed-hints" :DIR :BOOKS)
(INCLUDE-BOOK "../books/computed-hints")

(DEFUN |$itr_0_typep| (X) (AND (NATP X) (< X 4294967296)))

(DEFUN |$itr_loop_iter_sums_ys_zs_6|
  (|z_2| |y_3| |k3_2| |k2_2| |k1_2| |k0_2| |tmp_48| |$limit| |hist_4|)
  (DECLARE
    (XARGS :MEASURE (ACL2-COUNT (|+| 1 |$limit| (|-| |tmp_48|))) :HINTS
      (MEASURE-HINT)))
  (IF
    (NOT
      (AND (|$itr_0_typep| |k0_2|) (|$itr_0_typep| |k1_2|)
        (|$itr_0_typep| |k2_2|) (|$itr_0_typep| |k3_2|)
        (|$itr_0_typep| |y_3|) (|$itr_0_typep| |z_2|) (NATP |tmp_48|)
        (NATP |$limit|) (TRUE-LISTP |hist_4|)))
    (LIST (LIST 0) (LIST 0) (LIST 0))
    (IF (> |tmp_48| |$limit|) |hist_4|
      (LET
        ((|$arm-result|
           (COND ((< |tmp_48| 1) (LIST 2654435769 |y_3| |z_2|))
             (T
               (LET*
                 ((|ys_1|
                    (LET* ((|z_3| (NTH 0 (NTH 2 |hist_4|))))
                      (C-WORD-+ 32 (NTH 0 (NTH 1 |hist_4|))
                        (C-WORD-^^
                          (C-WORD-^^
                            (C-WORD-+ 32 (C-WORD-<< 32 |z_3| 4) |k0_2|)
                            (C-WORD-+ 32 |z_3| (NTH 0 (NTH 0 |hist_4|))))
                          (C-WORD-+ 32 (C-WORD->> 32 |z_3| 5) |k1_2|))))))
                 (LIST (C-WORD-+ 32 (NTH 0 (NTH 0 |hist_4|)) 2654435769)
                   |ys_1|
                   (C-WORD-+ 32 (NTH 0 (NTH 2 |hist_4|))
                     (C-WORD-^^
                       (C-WORD-^^
                         (C-WORD-+ 32 (C-WORD-<< 32 |ys_1| 4) |k2_2|)
                         (C-WORD-+ 32 |ys_1| (NTH 0 (NTH 0 |hist_4|))))
                       (C-WORD-+ 32 (C-WORD->> 32 |ys_1| 5) |k3_2|)))))))))
        (|$itr_loop_iter_sums_ys_zs_6| |z_2| |y_3| |k3_2| |k2_2| |k1_2|
          |k0_2| (|1+| |tmp_48|) |$limit|
          (LIST
            (UPDATE-NTH (LOGHEAD 0 |tmp_48|) (NTH 0 |$arm-result|)
              (NTH 0 |hist_4|))
            (UPDATE-NTH (LOGHEAD 0 |tmp_48|) (NTH 1 |$arm-result|)
              (NTH 1 |hist_4|))
            (UPDATE-NTH (LOGHEAD 0 |tmp_48|) (NTH 2 |$arm-result|)
              (NTH 2 |hist_4|))))))))

(DEFUND |itr_iter_sums_ys_zs_6|
  (|z_2| |y_3| |k3_2| |k2_2| |k1_2| |k0_2| |tmp_48|)
  (IF (NOT (NATP |tmp_48|)) (LIST (LIST 0) (LIST 0) (LIST 0))
    (|$itr_loop_iter_sums_ys_zs_6| |z_2| |y_3| |k3_2| |k2_2| |k1_2| |k0_2| 0
      |tmp_48| (LIST (LIST 0) (LIST 0) (LIST 0)))))

(DEFUND |$itr_1_typep| (X)
  (AND (TRUE-LISTP X) (NATP (NTH 0 X)) (< (NTH 0 X) 4294967296)
    (NATP (NTH 1 X)) (< (NTH 1 X) 4294967296)))

(DEFUND |$itr_2_typep| (X)
  (AND (TRUE-LISTP X) (NATP (NTH 0 X)) (< (NTH 0 X) 4294967296)
    (NATP (NTH 1 X)) (< (NTH 1 X) 4294967296) (NATP (NTH 2 X))
    (< (NTH 2 X) 4294967296) (NATP (NTH 3 X)) (< (NTH 3 X) 4294967296)))

(DEFUND |itr_code| (|tmp_37| |tmp_38|)
  (IF (NOT (AND (|$itr_2_typep| |tmp_38|) (|$itr_1_typep| |tmp_37|)))
    (LIST 0 0)
    (LET*
      ((|y| (NTH 0 |tmp_37|)) (|z| (NTH 1 |tmp_37|)) (|k0| (NTH 0 |tmp_38|))
        (|k1| (NTH 1 |tmp_38|)) (|k2| (NTH 2 |tmp_38|))
        (|k3| (NTH 3 |tmp_38|)))
      (LIST
        (LET*
          ((|tmp_40|
             (LET*
               ((|tmp_39|
                  (|itr_iter_sums_ys_zs_6| |z| |y| |k3| |k2| |k1| |k0| 32)))
               (NTH 1 |tmp_39|)))) (NTH 0 |tmp_40|))
        (LET*
          ((|tmp_42|
             (LET*
               ((|tmp_41|
                  (|itr_iter_sums_ys_zs_6| |z| |y| |k3| |k2| |k1| |k0| 32)))
               (NTH 2 |tmp_41|)))) (NTH 0 |tmp_42|))))))

(DEFUN |$itr_loop_iter_sums_ys_zs_5|
  (|z_1| |y_1| |k3_1| |k2_1| |k1_1| |k0_1| |tmp_47| |$limit| |hist_3|)
  (DECLARE
    (XARGS :MEASURE (ACL2-COUNT (|+| 1 |$limit| (|-| |tmp_47|))) :HINTS
      (MEASURE-HINT)))
  (IF
    (NOT
      (AND (|$itr_0_typep| |k0_1|) (|$itr_0_typep| |k1_1|)
        (|$itr_0_typep| |k2_1|) (|$itr_0_typep| |k3_1|)
        (|$itr_0_typep| |y_1|) (|$itr_0_typep| |z_1|) (NATP |tmp_47|)
        (NATP |$limit|) (TRUE-LISTP |hist_3|)))
    (LIST (LIST 0) (LIST 0) (LIST 0))
    (IF (> |tmp_47| |$limit|) |hist_3|
      (LET
        ((|$arm-result|
           (COND
             ((< |tmp_47| 1) (LIST (C-WORD-* 32 2654435769 32) |z_1| |y_1|))
             (T
               (LET*
                 ((|zs_1|
                    (LET* ((|y_2| (NTH 0 (NTH 2 |hist_3|))))
                      (C-WORD-- 32 (NTH 0 (NTH 1 |hist_3|))
                        (C-WORD-^^
                          (C-WORD-^^
                            (C-WORD-+ 32 (C-WORD-<< 32 |y_2| 4) |k2_1|)
                            (C-WORD-+ 32 |y_2| (NTH 0 (NTH 0 |hist_3|))))
                          (C-WORD-+ 32 (C-WORD->> 32 |y_2| 5) |k3_1|))))))
                 (LIST (C-WORD-- 32 (NTH 0 (NTH 0 |hist_3|)) 2654435769)
                   |zs_1|
                   (C-WORD-- 32 (NTH 0 (NTH 2 |hist_3|))
                     (C-WORD-^^
                       (C-WORD-^^
                         (C-WORD-+ 32 (C-WORD-<< 32 |zs_1| 4) |k0_1|)
                         (C-WORD-+ 32 |zs_1| (NTH 0 (NTH 0 |hist_3|))))
                       (C-WORD-+ 32 (C-WORD->> 32 |zs_1| 5) |k1_1|)))))))))
        (|$itr_loop_iter_sums_ys_zs_5| |z_1| |y_1| |k3_1| |k2_1| |k1_1|
          |k0_1| (|1+| |tmp_47|) |$limit|
          (LIST
            (UPDATE-NTH (LOGHEAD 0 |tmp_47|) (NTH 0 |$arm-result|)
              (NTH 0 |hist_3|))
            (UPDATE-NTH (LOGHEAD 0 |tmp_47|) (NTH 1 |$arm-result|)
              (NTH 1 |hist_3|))
            (UPDATE-NTH (LOGHEAD 0 |tmp_47|) (NTH 2 |$arm-result|)
              (NTH 2 |hist_3|))))))))

(DEFUND |itr_iter_sums_ys_zs_5|
  (|z_1| |y_1| |k3_1| |k2_1| |k1_1| |k0_1| |tmp_47|)
  (IF (NOT (NATP |tmp_47|)) (LIST (LIST 0) (LIST 0) (LIST 0))
    (|$itr_loop_iter_sums_ys_zs_5| |z_1| |y_1| |k3_1| |k2_1| |k1_1| |k0_1| 0
      |tmp_47| (LIST (LIST 0) (LIST 0) (LIST 0)))))

(DEFUND |itr_decode| (|tmp_35| |tmp_36|)
  (IF (NOT (AND (|$itr_2_typep| |tmp_36|) (|$itr_1_typep| |tmp_35|)))
    (LIST 0 0)
    (LET*
      ((|y| (NTH 0 |tmp_35|)) (|z| (NTH 1 |tmp_35|)) (|k0| (NTH 0 |tmp_36|))
        (|k1| (NTH 1 |tmp_36|)) (|k2| (NTH 2 |tmp_36|))
        (|k3| (NTH 3 |tmp_36|)))
      (LIST
        (LET*
          ((|tmp_44|
             (LET*
               ((|tmp_43|
                  (|itr_iter_sums_ys_zs_5| |z| |y| |k3| |k2| |k1| |k0| 32)))
               (NTH 2 |tmp_43|)))) (NTH 0 |tmp_44|))
        (LET*
          ((|tmp_46|
             (LET*
               ((|tmp_45|
                  (|itr_iter_sums_ys_zs_5| |z| |y| |k3| |k2| |k1| |k0| 32)))
               (NTH 1 |tmp_45|)))) (NTH 0 |tmp_46|))))))
