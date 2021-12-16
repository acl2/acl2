; Tests of the finite-difference transformation
;
; Copyright (C) 2015-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "finite-difference")
(include-book "kestrel/utilities/deftest" :dir :system)

;TODO: Test :check-guard option.

;TODO: Add sum of squares example

;TODO: Add example with len or max of list

(deftest
  ;; return the list of the doubles of all numbers from x down to 0
  (defun list-of-doubles (x)
    (if (zp x)
        '(0)
      (cons (* 2 x)
            (list-of-doubles (+ -1 x)))))

  ;; just a test:
  (assert-event (equal (list-of-doubles 5) '(10 8 6 4 2 0)))

;(set-ignore-ok t) ;TODO: finite-difference could give a nicer error if the new param is not used

  (finite-difference list-of-doubles (* 2 x) (distributivity))

  (must-be-redundant
    (defun list-of-doubles$1 (x v)
      (declare (xargs :guard (equal v (* 2 x))
                      :verify-guards nil))
      (if (zp x) ;would be nice if this test were rephrased in terms of v...
          '(0)
        (cons v ;we use v here
              (list-of-doubles$1 (+ -1 x)
                                 (+ -2
                                    v) ;we incrementally update v here
                                 ))))
    (defun list-of-doubles$1-wrapper (x)
      (declare (xargs :normalize nil))
      (list-of-doubles$1 x (binary-* '2 x)))
    (defthm list-of-doubles-becomes-list-of-doubles$1-wrapper
      (equal (list-of-doubles x)
             (list-of-doubles$1-wrapper x)))))

;; test :eval when used for the list of rules.
(deftest
  ;; return the list of the doubles of all numbers from x down to 0
  (defun list-of-doubles (x)
    (if (zp x)
        '(0)
      (cons (* 2 x)
            (list-of-doubles (+ -1 x)))))

  (finite-difference list-of-doubles (* 2 x) (:eval '(distributivity))))



;This version has a guard (both the core and the wrapper get guards):
(deftest
  ;; return the list of the doubles of all numbers from x down to 0
  (defun list-of-doubles (x)
    (declare (xargs :guard (natp x)))
    (if (zp x)
        '(0)
      (cons (* 2 x)
            (list-of-doubles (+ -1 x)))))
  (finite-difference list-of-doubles (* 2 x) (distributivity))
  (must-be-redundant
    (defun list-of-doubles$1 (x v)
      (declare (xargs :guard (and (natp x)
                                  (equal v (* 2 x)))
                      ))
      (if (zp x) ;would be nice if this test were rephrased in terms of v...
          '(0)
        (cons v ;we use v here
              (list-of-doubles$1 (+ -1 x)
                                 (+ -2
                                    v)       ;we incrementally update v here
                                 ))))
    (defun list-of-doubles$1-wrapper (x)
      (declare (xargs :normalize nil
                      :guard (natp x)))
      (list-of-doubles$1 x (binary-* '2 x)))
    (defthm list-of-doubles-becomes-list-of-doubles$1-wrapper
      (equal (list-of-doubles x)
             (list-of-doubles$1-wrapper x)))))

;; Test of :theorem-name

(deftest
  ;; return the list of the doubles of all numbers from x down to 0
  (defun list-of-doubles (x)
    (if (zp x)
        '(0)
      (cons (* 2 x)
            (list-of-doubles (+ -1 x)))))

  (finite-difference list-of-doubles (* 2 x) (distributivity) :theorem-name foo)

  (must-be-redundant
    (defun list-of-doubles$1 (x v)
      (declare (xargs :guard (equal v (* 2 x))
                      :verify-guards nil))
      (if (zp x) ;would be nice if this test were rephrased in terms of v...
          '(0)
        (cons v ;we use v here
              (list-of-doubles$1 (+ -1 x)
                                 (+ -2
                                    v) ;we incrementally update v here
                                 ))))
    (defun list-of-doubles$1-wrapper (x)
      (declare (xargs :normalize nil))
      (list-of-doubles$1 x (binary-* '2 x)))
    (defthm foo
      (equal (list-of-doubles x)
             (list-of-doubles$1-wrapper x)))))


;;
;; test of :build-wrapper nil:
;;

(deftest
  ;; return the list of the doubles of all numbers from x down to 0
  (defun list-of-doubles (x)
    (if (zp x)
        '(0)
      (cons (* 2 x)
            (list-of-doubles (+ -1 x)))))

;(set-ignore-ok t) ;TODO: finite-difference could give a nicer error if the new param is not used

  (finite-difference list-of-doubles (* 2 x) (distributivity) :build-wrapper nil)

  (must-be-redundant
    (defun list-of-doubles$1 (x v)
      (declare (xargs :guard (equal v (* 2 x))
                      :verify-guards nil))
      (if (zp x)
          '(0)
        (cons v ;we use v here
              (list-of-doubles$1 (+ -1 x)
                                 (+ -2
                                    v)       ;we incrementally update v here
                                 ))))

    ;; This theorem is not about the wrapper:
    (DEFTHM LIST-OF-DOUBLES-BECOMES-LIST-OF-DOUBLES$1
      (EQUAL (LIST-OF-DOUBLES X)
             (LIST-OF-DOUBLES$1 X (BINARY-* '2 X))))))


;; Test :theorem-disabled and :function-disabled (with wrapper)
(deftest
  ;; return the list of the doubles of all numbers from x down to 0
  (defun list-of-doubles (x)
    (if (zp x)
        '(0)
      (cons (* 2 x)
            (list-of-doubles (+ -1 x)))))

  (finite-difference list-of-doubles (* 2 x) (distributivity) :theorem-disabled t :function-disabled t)

  (must-be-redundant
   (defund list-of-doubles$1 (x v)
     (declare (xargs :guard (equal v (* 2 x))
                     :verify-guards nil))
     (if (zp x) ;would be nice if this test were rephrased in terms of v...
         '(0)
       (cons v ;we use v here
             (list-of-doubles$1 (+ -1 x)
                                (+ -2
                                   v)       ;we incrementally update v here
                                ))))
   (defund list-of-doubles$1-wrapper (x)
     (declare (xargs :normalize nil))
     (list-of-doubles$1 x (binary-* '2 x)))
   (defthmd list-of-doubles-becomes-list-of-doubles$1-wrapper
     (equal (list-of-doubles x)
            (list-of-doubles$1-wrapper x)))))

;; Test :theorem-disabled and :function-disabled (no wrapper)
(deftest
  ;; return the list of the doubles of all numbers from x down to 0
  (defun list-of-doubles (x)
    (if (zp x)
        '(0)
      (cons (* 2 x)
            (list-of-doubles (+ -1 x)))))

  (finite-difference list-of-doubles (* 2 x) (distributivity) :theorem-disabled t :function-disabled t :build-wrapper nil)

  (must-be-redundant
    (defund list-of-doubles$1 (x v)
      (declare (xargs :guard (equal v (* 2 x))
                      :verify-guards nil))
      (if (zp x) ;would be nice if this test were rephrased in terms of v...
          '(0)
        (cons v ;we use v here
              (list-of-doubles$1 (+ -1 x)
                                 (+ -2
                                    v) ;we incrementally update v here
                                 ))))
    (defthmd list-of-doubles-becomes-list-of-doubles$1
      (equal (list-of-doubles x)
             (list-of-doubles$1 x (binary-* '2 x))))))


;; Test of :new-name

(deftest
  ;; return the list of the doubles of all numbers from x down to 0
  (defun list-of-doubles (x)
    (if (zp x)
        '(0)
      (cons (* 2 x)
            (list-of-doubles (+ -1 x)))))

  (assert-event (equal (list-of-doubles 5) '(10 8 6 4 2 0)))

;(set-ignore-ok t) ;TODO: finite-difference could give a nicer error if the new param is not used

  (finite-difference list-of-doubles (* 2 x) (distributivity) :new-name bar)

  (must-be-redundant
    (defun bar (x v)
      (declare (xargs :guard (equal v (* 2 x))
                      :verify-guards nil))
      (if (zp x) ;would be nice if this test were rephrased in terms of v...
          '(0)
        (cons v ;we use v here
              (bar (+ -1 x)
                                 (+ -2
                                    v) ;we incrementally update v here
                                 ))))
    (defun bar-wrapper (x)
      (declare (xargs :normalize nil))
      (bar x (binary-* '2 x)))
    (defthm list-of-doubles-becomes-bar-wrapper
      (equal (list-of-doubles x)
             (bar-wrapper x)))))

;; A test involving function normalization:

(deftest
  (defun f () nil)

  (defun h (x y)
    (if (zp x)
        y
      (h (1- x) (f))))

  (finite-difference h 1 nil))

;; A test where the transformation adds an ignore declare:

(deftest
  (defun f () nil)

  (defun h (x y)
    (if (zp x)
        y
      (h (1- x) (f))))

  (finite-difference h x nil))

;; A test with a guard:

(deftest
  ;; return the list of the doubles of all numbers from x down to 0
  (defun list-of-doubles (x)
    (declare (xargs :guard (natp x)))
    (if (zp x)
        '(0)
      (cons (* 2 x)
            (list-of-doubles (+ -1 x)))))

  (finite-difference list-of-doubles (* 2 x) (distributivity))

  (must-be-redundant
    (defun list-of-doubles$1 (x v)
      (declare (xargs :guard (and (natp x)
                                  (equal v (* 2 x)))))
      (if (zp x) ;would be nice if this test were rephrased in terms of v...
          '(0)
        (cons v ;we use v here
              (list-of-doubles$1 (+ -1 x)
                                 (+ -2
                                    v) ;we incrementally update v here
                                 ))))
    (defun list-of-doubles$1-wrapper (x)
      (declare (xargs :guard (natp x)
                      :normalize nil ;todo: remove?
                      ))
      (list-of-doubles$1 x (binary-* '2 x)))
    (defthm list-of-doubles-becomes-list-of-doubles$1-wrapper
      (equal (list-of-doubles x)
             (list-of-doubles$1-wrapper x)))))

;; A test about termination (TODO: Get this to pass.  May need to test the
;; finite difference invariant and return :error if it fails.
;; (deftest
;;   (defun foo (x)
;;     (if (zp x)
;;         0
;;       (foo (+ -1 x ))))
;;   ;;non-sensical but exposes an issue with termination since in the final function the link between v and x-1 is only in the guard (which can't help with termination)
;;   (finite-difference foo (+ -1 x) nil))



;; A test that requires guard-hints:
(deftest
  (defund pre (x) (declare (xargs :guard t)) (natp x))
  (defun list-of-doubles (x)
    (declare (xargs :guard (pre x)
                    :guard-hints (("Goal" :in-theory (enable pre)))))
    (if (zp x)
        '(0)
      (cons (* 2 x)
            (list-of-doubles (+ -1 x)))))
  ;; The guard hint is needed because of "the guard of the guard": (* 2 x) now
  ;; appears in the guard, and * requires its args to be acl2-numbers, so we
  ;; must prove that x is an acl2-number, assuming the previous conjunct of the
  ;; guard, namely (pre x).  It's a bit of a pity to have to re-give the same
  ;; hint that we gave above when admitting list-of-doubles:
  (finite-difference list-of-doubles (* 2 x) (distributivity)
                     :guard-hints (("Goal" :in-theory (enable pre)))))


;; Test :print:
(deftest
  (defun list-of-doubles (x)
    (if (zp x)
        '(0)
      (cons (* 2 x)
            (list-of-doubles (+ -1 x)))))
  ;; TODO: This starts by printing 2 T's; why?
  (finite-difference list-of-doubles (* 2 x) (distributivity) :print :all))

;; Test when called on a non-existing function
(ensure-error (finite-difference blah (* 2 x) nil :print :all))
