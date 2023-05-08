; An approach to unrolling calls to NTH
;
; Copyright (C) 2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This helps us split a call of NTH into cases without decrementing the index
;; (decrementing makes it harder to show that the term representing the index
;; is a natural -- must appeal to overarching tests that it is not 0, not 1,
;; etc.)

;; Usually low and high are constants.  As calls to this function are unrolled,
;; LOW will change, but N will stay the same.
(defun nth-to-unroll (n low high l)
  (declare (xargs :guard (and (natp n)
                              (natp low)
                              (natp high)
                              (true-listp l))
                  :measure (nfix (+ 1 (- high low)))))
  (if (or (not (mbt (natp low)))
          (not (mbt (natp high)))
          (<= high low))
      (nth low l)
    (if (= n low)
        (nth low l)
      (nth-to-unroll n (+ 1 low) high l))))

(defthmd nth-to-unroll-opener
  (implies (and (syntaxp (and (quotep low) (quotep high)))
                (natp low)
                (natp high))
           (equal (nth-to-unroll n low high l)
                  (if (<= high low)
                      (nth low l)
                    (if (= n low)
                        (nth low l)
                      (nth-to-unroll n (+ 1 low) high l)))))
  :hints (("Goal" :in-theory (enable nth-to-unroll))))

(defthmd nth-becomes-nth-to-unroll-helper
  (implies (and (< high (len l))
                (integerp n)
                (natp low)
                (natp high)
                (<= low high)
                (<= low n)
                (<= n high))
           (equal (nth n l)
                  (nth-to-unroll n low high l)))
  :hints (("Goal" :in-theory (enable nth-to-unroll))))

;; too strong for general use but see rules like nth-becomes-nth-to-unroll-for-2d-array.
(defthmd nth-becomes-nth-to-unroll
  (implies (and (natp n)
                (< n (len l)))
           (equal (nth n l)
                  (nth-to-unroll n 0 (+ -1 (len l)) l)))
  :hints (("Goal" :use (:instance nth-becomes-nth-to-unroll-helper
                                  (low 0)
                                  (high (+ -1 (len l)))))))
