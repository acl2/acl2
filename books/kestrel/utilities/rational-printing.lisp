; Utilities for printing rational numbers readably
;
; Copyright (C) 2022-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))

(defund round-to-integer (x)
  (declare (xargs :guard (and (rationalp x)
                              (<= 0 x))))
  (let* ((integer-part (floor x 1))
         (fraction-part (- x integer-part)))
    (if (>= fraction-part 1/2)
        (+ 1 integer-part)
      integer-part)))

(defthm <=-of-0-and-round-to-integer-type
  (implies (<= 0 val)
           (<= 0 (round-to-integer val)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable round-to-integer))))

(defund round-to-hundredths (x)
  (declare (xargs :guard (and (rationalp x)
                              (<= 0 x))))
  (/ (round-to-integer (* 100 x)) 100))

(defthm <=-of-0-and-round-to-hundredths-type
  (implies (<= 0 val)
           (<= 0 (round-to-hundredths val)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable round-to-hundredths))))

(defund natural-length-decimal (n)
  (declare (xargs :guard (natp n)))
  (if (or (not (mbt (natp n)))
          (< n 10))
      1 ; 0-9 have length 1
    (+ 1 (natural-length-decimal (floor n 10)))))


;; Prints VAL, rounded to the hundredths place.
;; Returns nil.
(defund print-to-hundredths (val)
  (declare (xargs :guard (rationalp val)))
  (let* ((sign (if (< val 0) "-" ""))
         (val (abs val))
         (val (round-to-hundredths val))
         (integer-part (floor val 1))
         (fraction-part (- val integer-part))
         (tenths (floor (* fraction-part 10) 1))
         (fraction-part-no-tenths (- fraction-part (/ tenths 10)))
         (hundredths (floor (* fraction-part-no-tenths 100) 1)))
    ;; Hoping that using ~c here prevents any newlines:
    (cw "~s0~c1.~c2~c3" sign (cons integer-part (natural-length-decimal integer-part)) (cons tenths 1) (cons hundredths 1))))
