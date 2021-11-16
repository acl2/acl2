; Tests of specialize-theorems
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "specialize-theorems")
(include-book "kestrel/utilities/deftest" :dir :system)

(deftest
  (specialize-theorem 'car-cons '-with-x-3 '((x . 3)))
  (must-be-redundant
   (DEFTHM CAR-CONS-WITH-X-3
     (EQUAL (CAR (CONS '3 Y))
            '3))))

;same as above but the 3 is quoted:
(deftest
  (specialize-theorem 'car-cons '-with-x-3 '((x . '3)))
  (must-be-redundant
   (DEFTHM CAR-CONS-WITH-X-3
     (EQUAL (CAR (CONS '3 Y))
            '3))))

;; Specializing multiple theorems at once
(deftest
  (specialize-theorems '(car-cons associativity-of-+) '-with-x-3 '((x . 3)))
  (must-be-redundant
   (DEFTHM
    CAR-CONS-WITH-X-3
    (EQUAL (CAR (CONS '3 Y)) '3))
   (DEFTHM ASSOCIATIVITY-OF-+-WITH-X-3
     (EQUAL (BINARY-+ (BINARY-+ '3 Y) Z)
            (BINARY-+ '3 (BINARY-+ Y Z))))))

;; A test where specialization allows entire hyps to be dropped
(deftest
  (defthm foo
    (implies (and (natp i)
                  (< i 4)
                  (equal 4 (len lst))
                  (nat-listp lst)
                  )
             (natp (nth i lst)))
    :hints (("Goal" :expand ((NTH I LST)
                             (NTH (+ -1 I) (CDR LST))
                             (NTH (+ -2 I) (cdr (CDR LST)))))))

  (specialize-theorem 'foo '-with-i-3 '((i . 3)))

  (must-be-redundant
   (DEFTHM FOO-WITH-I-3
     (IMPLIES (IF (EQUAL '4 (LEN LST))
                  (NAT-LISTP LST)
                  'NIL)
              (NATP (NTH '3 LST))))))
