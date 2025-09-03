; Tests of the user helper utilities
;
; Copyright (C) 2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "util2")
(include-book "std/testing/assert-equal" :dir :system)

(assert-equal (symbolic-list 'x 4)
              '(cons x0 (cons x1 (cons x2 (cons x3 'nil)))))

;; same as symbolic-list
(assert-equal (symbolic-byte-list 'x 4)
              '(cons x0 (cons x1 (cons x2 (cons x3 'nil)))))

(assert-equal (bit-blasted-symbolic-byte-list 'x 2)
              '(cons (bvcat '1
                            x_0_7 '7
                            (bvcat '1
                                   x_0_6 '6
                                   (bvcat '1
                                          x_0_5 '5
                                          (bvcat '1
                                                 x_0_4 '4
                                                 (bvcat '1
                                                        x_0_3 '3
                                                        (bvcat '1
                                                               x_0_2 '2
                                                               (bvcat '1 x_0_1 '1 x_0_0)))))))
                (cons (bvcat '1
                             x_1_7 '7
                             (bvcat '1
                                    x_1_6 '6
                                    (bvcat '1
                                           x_1_5 '5
                                           (bvcat '1
                                                  x_1_4 '4
                                                  (bvcat '1
                                                         x_1_3 '3
                                                         (bvcat '1
                                                                x_1_2 '2
                                                                (bvcat '1 x_1_1 '1 x_1_0)))))))
                      'nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (symbolic-array 'x 2 8)
              '(bv-array-write '8 '2 '0 x0 (bv-array-write '8 '2 '1 x1 '(0 0))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (bvcat-nest-for-items '(a0 a1 a2 a3) 8)
              '(bvcat '8 a0 '24 (bvcat '8 a1 '16 (bvcat '8 a2 '8 a3))))

(assert-equal (bit-blasted-symbolic-array 'x 2 8)
              '(bv-array-write '8
                              '2
                              '0
                              (bvcat '1
                                     x_0_7 '7
                                     (bvcat '1
                                            x_0_6 '6
                                            (bvcat '1
                                                   x_0_5 '5
                                                   (bvcat '1
                                                          x_0_4 '4
                                                          (bvcat '1
                                                                 x_0_3 '3
                                                                 (bvcat '1
                                                                        x_0_2 '2
                                                                        (bvcat '1 x_0_1 '1 x_0_0)))))))
                              (bv-array-write '8
                                              '2
                                              '1
                                              (bvcat '1
                                                     x_1_7 '7
                                                     (bvcat '1
                                                            x_1_6 '6
                                                            (bvcat '1
                                                                   x_1_5 '5
                                                                   (bvcat '1
                                                                          x_1_4 '4
                                                                          (bvcat '1
                                                                                 x_1_3 '3
                                                                                 (bvcat '1
                                                                                        x_1_2 '2
                                                                                        (bvcat '1 x_1_1 '1 x_1_0)))))))
                                              ;; Starts with an "empty" array:
                                              '(0 0))))
