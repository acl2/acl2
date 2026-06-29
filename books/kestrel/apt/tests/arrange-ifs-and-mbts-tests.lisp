; Tests of the arrange-ifs-and-mbts transformation
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)
; Supporting Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "../arrange-ifs-and-mbts")
(include-book "kestrel/utilities/deftest" :dir :system)

(deftest
  (defun foo (x)
    (if (mbt (natp x))
        (if (mbt (posp x))
            (+ 1 x)
          17)
      17))

  (arrange-ifs-and-mbts foo)

  (must-be-redundant
   ;; the MBTS got combined because they have the same else-branch:
   (defun foo$1 (x)
     (declare (xargs :verify-guards nil)) ; todo: clean this up
     (if (mbt (and (natp x) (posp x)))
         (+ 1 x)
       17))))

(deftest
  (defun bar (x)
    (if (and (mbt (natp x)) (< 0 x))
        (+ 1 x)
      17))

  (arrange-ifs-and-mbts bar)

  (must-be-redundant
   ;; the MBTS and the non-MBT test are now in separate IFs:
   (defun bar$1 (x)
     (declare (xargs :verify-guards nil))
     (if (mbt (natp x))
         (if (< 0 x)
             (+ 1 x)
           17)
       17))))

(deftest
  (defun foo2 (x)
    (if (and (mbt (natp x)) (mbt (posp x)))
        (+ 1 x)
      17))

  (arrange-ifs-and-mbts foo2)

  (must-be-redundant
   ;; the MBTS conjuncts got combined:
   (defun foo2$1 (x)
     (declare (xargs :verify-guards nil)) ; todo: clean this up
     (if (mbt (and (natp x) (posp x)))
         (+ 1 x)
       17))))

(deftest
  (defun foo3 (x)
    (if (not (and (mbt (natp x)) (mbt (posp x))))
        (+ 1 x)
      17))

  (arrange-ifs-and-mbts foo3)

  (must-be-redundant
   ;; the MBTS conjuncts got combined:
   (defun foo3$1 (x)
     (declare (xargs :verify-guards nil)) ; todo: clean this up
     (if (mbt (and (natp x) (posp x)))
         17
       (+ 1 x)))))

;; TODO: Add more tests

(deftest
  (defun foo4 (x)
    (if (or (not (mbt (natp x)))
            (zp x))
        17
      (+ 1 x)))

  (arrange-ifs-and-mbts foo4)

  (must-be-redundant
   (defun foo4$1 (x)
     (if (mbt (natp x))
         (if (not (zp x))
             (+ 1 x)
           17)
       17))))

;; Test disjunction of negated mbts
(deftest
  (defun foo5 (x)
    (if (or (not (mbt (natp x))) (not (mbt (posp x))))
        (+ 1 x)
      17))

  (arrange-ifs-and-mbts foo5)

  (must-be-redundant
   (defun foo5$1 (x)
     (declare (xargs :verify-guards nil))
     (if (mbt (and (natp x) (posp x)))
         17
       (+ 1 x)))))

;; Test nested negated mbt
(deftest
  (defun foo6 (x)
    (if (mbt (natp x))
        (if (not (mbt (posp x)))
            17
          (+ 1 x))
      17))

  (arrange-ifs-and-mbts foo6)

  (must-be-redundant
   (defun foo6$1 (x)
     (declare (xargs :verify-guards nil))
     (if (mbt (and (natp x) (posp x)))
         (+ 1 x)
       17))))

;; Test nested disjunction of negated mbts
(deftest
  (defun foo7 (x)
    (if (mbt (integerp x))
      (if (or (not (mbt (natp x))) (not (mbt (posp x))))
          17
        (+ 1 x))
      17))

  (arrange-ifs-and-mbts foo7)

  (must-be-redundant
   (defun foo7$1 (x)
     (declare (xargs :verify-guards nil))
     (if (mbt (and (integerp x) (natp x) (posp x)))
         (+ 1 x)
         17))))

(deftest
  (defun foo8 (x)
    (if (and (natp x) (mbt (posp x)))
        (+ 1 x)
      17))

  (arrange-ifs-and-mbts foo8)

  ;; The inner mbt is pulled to the top level
  (must-be-redundant
   (defun foo8$1 (x)
     (declare (xargs :verify-guards nil))
     (if (mbt (posp x))
         (if (natp x) (+ 1 x) 17)
       17)))

  (defun foo9 (x)
    (if (natp x)
        (if  (mbt (posp x))
            (+ 1 x)
          17)
      17))

  (arrange-ifs-and-mbts foo9)

  ;; The inner mbt is not pulled to the top level
  ;; Why is this different than foo8$1?
  ;; (must-be-redundant
  ;;  (defun foo9$1 (x)
  ;;    (declare (xargs :verify-guards nil))
  ;;    (if (natp x)
  ;;        (if (mbt (posp x)) (+ 1 x) 17)
  ;;      17)))
  )

;; Test mbt$
(deftest

  (defun foo10 (x)
    (if (mbt$ (natp x))
        (if (mbt$ (posp x))
            (+ 1 x)
          17)
      17))

  (arrange-ifs-and-mbts foo10)

  (must-be-redundant
   (defun foo10$1 (x)
     (declare (xargs :verify-guards nil))
     (if (mbt (and (natp x) t (posp x)))
         (+ 1 x)
       17))))

(deftest

  ;; More complicated term with mbt$ and mbt
  (defun foo11 (x)
    (if (mbt$ (integerp x))
        (if (or (not (mbt (natp x))) (not (mbt$ (posp x))))
            17
          (+ 1 x))
      17))

  (arrange-ifs-and-mbts foo11)

  (must-be-redundant
   (defun foo11$1 (x)
     (declare (xargs :verify-guards nil))
     (if (mbt (and (integerp x) t (natp x) (posp x)))
         (+ 1 x)
         17))))

;; Test cond macro translation
(deftest
  (defun foo12 (x)
    (cond ((mbt (natp x))
           (cond ((mbt (posp x)) (+ 1 x))
                 (t 17)))
          (t 17)))

  (arrange-ifs-and-mbts foo12)

  (must-be-redundant
   (defun foo12$1 (x)
     (declare (xargs :verify-guards nil))
     (if (mbt (and (natp x) (posp x)))
         (+ 1 x)
         17))))

(deftest
  (defun foo13 (x)
    (declare (xargs :guard (and (rationalp x)
                                (< 0 x))))
    (if (and (natp x) (mbt (posp x)))
        (+ 1 x)
      17))

  (arrange-ifs-and-mbts foo13 :show-only t)

  ;; Guard proofs fails as arrange-ifs-and-mbts moves the mbt before the
  ;; necessary precondition.
  (must-fail
   (arrange-ifs-and-mbts foo13 :print :info)))
