(IN-PACKAGE "ACL2")

(INCLUDE-BOOK "source_shallow" :DIR :BOOKS)

(INCLUDE-BOOK "computed-hints" :DIR :BOOKS)

(DEFUN |$itr_loop_iter_consts_3| (|tmp_34| |$limit| |hist_4|)
  (DECLARE
    (XARGS :MEASURE (ACL2-COUNT (|+| 1 |$limit| (|-| |tmp_34|))) :HINTS
      (MEASURE-HINT)))
  (IF (NOT (AND (NATP |tmp_34|) (NATP |$limit|) (TRUE-LISTP |hist_4|)))
    (LIST 0)
    (IF (> |tmp_34| |$limit|) |hist_4|
      (LET
        ((|$arm-result|
           (COND ((< |tmp_34| 1) 3084996963)
             (T (C-WORD-+ 32 (NTH 0 |hist_4|) 2654435769)))))
        (|$itr_loop_iter_consts_3| (|1+| |tmp_34|) |$limit|
          (UPDATE-NTH (LOGHEAD 0 |tmp_34|) |$arm-result| |hist_4|))))))

(DEFUND |itr_iter_consts_3| (|tmp_34|)
  (IF (NOT (NATP |tmp_34|)) (LIST 0)
    (|$itr_loop_iter_consts_3| 0 |tmp_34| (LIST 0))))

(SET-IGNORE-OK T)

(DEFUN |$itr_comp_1| (|$i|)
  (DECLARE
    (XARGS :MEASURE (ACL2-COUNT (|+| 1 44 (|-| |$i|))) :HINTS (MEASURE-HINT)))
  (IF (NOT (NATP |$i|)) NIL
    (IF (>= |$i| 44) NIL
      (CONS
        (LET
          ((|tmp_32|
             (NTH |$i|
               (LIST 0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21
                 22 23 24 25 26 27 28 29 30 31 32 33 34 35 36 37 38 39 40 41
                 42 43))))
          (LET* ((|tmp_33| (|itr_iter_consts_3| |tmp_32|))) (NTH 0 |tmp_33|)))
        (|$itr_comp_1| (|1+| |$i|))))))

(SET-IGNORE-OK NIL)

(DEFUND |itr_inits_2| NIL (|$itr_comp_1| 0))

(DEFUND |$itr_0_typep| (X)
  (AND (TRUE-LISTP X) (NATP (NTH 0 X)) (< (NTH 0 X) 4294967296)
    (NATP (NTH 1 X)) (< (NTH 1 X) 4294967296)))

(DEFUN |$itr_loop_iter_s_l_3| (|initl_1| |tmp_31| |$limit| |hist_3|)
  (DECLARE
    (XARGS :MEASURE (ACL2-COUNT (|+| 1 |$limit| (|-| |tmp_31|))) :HINTS
      (MEASURE-HINT)))
  (IF
    (NOT
      (AND (|$itr_0_typep| |initl_1|) (NATP |tmp_31|) (NATP |$limit|)
        (TRUE-LISTP |hist_3|)))
    (LIST
      (LIST 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
        0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
      (LIST 0 0))
    (IF (> |tmp_31| |$limit|) |hist_3|
      (LET
        ((|$arm-result|
           (COND
             ((< |tmp_31| 1)
               (LET*
                 ((|s_1|
                    (C-WORD-<<< 32 (NTH (LOGHEAD 6 |tmp_31|) (|itr_inits_2|))
                      3)))
                 (LIST |s_1|
                   (C-WORD-<<< 32
                     (C-WORD-+ 32
                       (NTH
                         (NAT-REP
                           (REVERSE (LIST (= (LOGHEAD 1 |tmp_31|) 1))))
                         |initl_1|) |s_1|) (LOGHEAD 5 (C-WORD-% |s_1| 5))))))
             ((< |tmp_31| 2)
               (LET*
                 ((|s_2|
                    (C-WORD-<<< 32
                      (C-WORD-+ 32
                        (C-WORD-+ 32
                          (NTH (LOGHEAD 6 |tmp_31|) (|itr_inits_2|))
                          (NTH (LOGHEAD 6 (C-WORD-- 32 |tmp_31| 1))
                            (NTH 0 |hist_3|)))
                        (NTH
                          (NAT-REP
                            (REVERSE
                              (LIST
                                (= (LOGHEAD 1 (C-WORD-- 32 |tmp_31| 1)) 1))))
                          (NTH 1 |hist_3|))) 3)))
                 (LIST |s_2|
                   (LET*
                     ((|b_1|
                        (NTH
                          (NAT-REP
                            (REVERSE
                              (LIST
                                (= (LOGHEAD 1 (C-WORD-- 32 |tmp_31| 1)) 1))))
                          (NTH 1 |hist_3|))))
                     (C-WORD-<<< 32
                       (C-WORD-+ 32
                         (C-WORD-+ 32
                           (NTH
                             (NAT-REP
                               (REVERSE (LIST (= (LOGHEAD 1 |tmp_31|) 1))))
                             |initl_1|) |s_2|) |b_1|)
                       (LOGHEAD 5 (C-WORD-% (C-WORD-+ 32 |s_2| |b_1|) 5)))))))
             ((< |tmp_31| 44)
               (LET*
                 ((|s_3|
                    (C-WORD-<<< 32
                      (C-WORD-+ 32
                        (C-WORD-+ 32
                          (NTH (LOGHEAD 6 |tmp_31|) (|itr_inits_2|))
                          (NTH (LOGHEAD 6 (C-WORD-- 32 |tmp_31| 1))
                            (NTH 0 |hist_3|)))
                        (NTH
                          (NAT-REP
                            (REVERSE
                              (LIST
                                (= (LOGHEAD 1 (C-WORD-- 32 |tmp_31| 1)) 1))))
                          (NTH 1 |hist_3|))) 3)))
                 (LIST |s_3|
                   (LET*
                     ((|b_2|
                        (NTH
                          (NAT-REP
                            (REVERSE
                              (LIST
                                (= (LOGHEAD 1 (C-WORD-- 32 |tmp_31| 1)) 1))))
                          (NTH 1 |hist_3|))))
                     (C-WORD-<<< 32
                       (C-WORD-+ 32
                         (C-WORD-+ 32
                           (NTH
                             (NAT-REP
                               (REVERSE
                                 (LIST
                                   (= (LOGHEAD 1 (C-WORD-- 32 |tmp_31| 2)) 1))))
                             (NTH 1 |hist_3|)) |s_3|) |b_2|)
                       (LOGHEAD 5 (C-WORD-% (C-WORD-+ 32 |s_3| |b_2|) 5)))))))
             (T
               (LET*
                 ((|s_4|
                    (C-WORD-<<< 32
                      (C-WORD-+ 32
                        (C-WORD-+ 32
                          (NTH (LOGHEAD 6 (C-WORD-- 32 |tmp_31| 44))
                            (NTH 0 |hist_3|))
                          (NTH (LOGHEAD 6 (C-WORD-- 32 |tmp_31| 1))
                            (NTH 0 |hist_3|)))
                        (NTH
                          (NAT-REP
                            (REVERSE
                              (LIST
                                (= (LOGHEAD 1 (C-WORD-- 32 |tmp_31| 1)) 1))))
                          (NTH 1 |hist_3|))) 3)))
                 (LIST |s_4|
                   (LET*
                     ((|b_3|
                        (NTH
                          (NAT-REP
                            (REVERSE
                              (LIST
                                (= (LOGHEAD 1 (C-WORD-- 32 |tmp_31| 1)) 1))))
                          (NTH 1 |hist_3|))))
                     (C-WORD-<<< 32
                       (C-WORD-+ 32
                         (C-WORD-+ 32
                           (NTH
                             (NAT-REP
                               (REVERSE
                                 (LIST
                                   (= (LOGHEAD 1 (C-WORD-- 32 |tmp_31| 2)) 1))))
                             (NTH 1 |hist_3|)) |s_4|) |b_3|)
                       (LOGHEAD 5 (C-WORD-% (C-WORD-+ 32 |s_4| |b_3|) 5))))))))))
        (|$itr_loop_iter_s_l_3| |initl_1| (|1+| |tmp_31|) |$limit|
          (LIST
            (UPDATE-NTH (LOGHEAD 6 |tmp_31|) (NTH 0 |$arm-result|)
              (NTH 0 |hist_3|))
            (UPDATE-NTH (LOGHEAD 1 |tmp_31|) (NTH 1 |$arm-result|)
              (NTH 1 |hist_3|))))))))

(DEFUND |itr_iter_s_l_3| (|initl_1| |tmp_31|)
  (IF (NOT (NATP |tmp_31|))
    (LIST
      (LIST 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
        0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
      (LIST 0 0))
    (|$itr_loop_iter_s_l_3| |initl_1| 0 |tmp_31|
      (LIST
        (LIST 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
          0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
        (LIST 0 0)))))

(DEFUND |$itr_1_typep| (X)
  (AND (TRUE-LISTP X) (NATP (NTH 0 X)) (< (NTH 0 X) 256) (NATP (NTH 1 X))
    (< (NTH 1 X) 256) (NATP (NTH 2 X)) (< (NTH 2 X) 256) (NATP (NTH 3 X))
    (< (NTH 3 X) 256) (NATP (NTH 4 X)) (< (NTH 4 X) 256)))

(DEFUND |itr_rc6exp| (|key|)
  (IF (NOT (AND (|$itr_1_typep| |key|)))
    (LIST 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
      0 0 0 0 0 0 0 0 0 0)
    (LET*
      ((|initl|
         (LET*
           ((|tmp_26|
              (LET* ((|tmp_25| (C-WORD-JOIN 8 |key|)))
                (C-WORD-APPEND (LIST 40 |tmp_25| 24 0)))))
           (C-WORD-SPLIT 32 2 |tmp_26|)))
        (|tmp_30|
          (LET*
            ((|tmp_29|
               (LET*
                 ((|tmp_28|
                    (LET*
                      ((|tmp_27|
                         (|itr_iter_s_l_3| |initl| (C-WORD-+ 32 88 43))))
                      (NTH 0 |tmp_27|))))
                 (C-VEC-<<< |tmp_28| (LOGHEAD 6 88))))) (FIRSTN 44 |tmp_29|))))
      (C-VEC->>> |tmp_30| 0))))
