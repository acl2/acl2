; Tests of the drop-irrelevant-params transformation
;
; Copyright (C) 2015-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Authors: Eric Smith (eric.smith@kestrel.edu)
;          Nathan Guermond
;          Limei Gilham

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "drop-irrelevant-params")
(include-book "kestrel/utilities/deftest" :dir :system)

;; ----------------------------------------------------------------------
;;; test of a non-recursive function:

(deftest
  ;; z is an irrelevant parameter:
  (defun foo (x y z) (declare (ignore z)) (+ x y))
  (drop-irrelevant-params foo z :build-wrapper t)
  (must-be-redundant
   (DEFUN FOO$1 (X Y)
     (DECLARE (XARGS :VERIFY-GUARDS NIL))
     (+ X Y))
   (DEFUN FOO$1-WRAPPER (X Y Z)
     (DECLARE (IGNORE Z))
     (FOO$1 X Y))
   (DEFTHM FOO-BECOMES-FOO$1-WRAPPER
     (EQUAL (FOO X Y Z)
            (FOO$1-WRAPPER X Y Z)))))

;;; test of a non-recursive function with :build-wrapper nil (the default):

(deftest
  ;; z is an irrelevant parameter:
  (defun foo (x y z) (declare (ignore z)) (+ x y))
  (drop-irrelevant-params foo z)
  (must-be-redundant
    (DEFUN FOO$1 (X Y)
      (DECLARE (XARGS :VERIFY-GUARDS NIL))
      (+ X Y))
    (DEFTHM FOO-BECOMES-FOO$1
      (EQUAL (FOO X Y Z) (FOO$1 X Y)))))



;; ----------------------------------------------------------------------
;;; test of a singly-recursive function:

(deftest
  ;;irrel is an irrelevant parameter:
  (defun my-len (lst irrel)
    (declare (irrelevant irrel))
    (if (endp lst)
        0
      (+ 1 (my-len (rest lst) (+ 7 irrel)))))
  (drop-irrelevant-params my-len irrel :build-wrapper t)
  (must-be-redundant
    (defun my-len$1 (lst)
      (declare (xargs :verify-guards nil
                      :measure (acl2-count lst)))
      (if (endp lst)
          0
        (+ 1 (my-len$1 (cdr lst)))))
    ;;the wrapper (exactly equal to the original function):
    (defun my-len$1-wrapper (lst irrel)
      (my-len$1 lst))
    (defthm my-len-becomes-my-len$1-wrapper
      (equal (my-len lst irrel)
             (my-len$1-wrapper lst irrel)))))


;; ----------------------------------------------------------------------
;;; test of mutual-recursion

(deftest
  (mutual-recursion
   (defun even-natp (x unused)
     (declare (irrelevant unused))
     (if (zp x)
         t
       (not (odd-natp (+ -1 x) unused))))
   (defun odd-natp (x unused)
     (declare (irrelevant unused))
     (if (zp x)
         nil
       (not (even-natp (+ -1 x) unused)))))

  (drop-irrelevant-params even-natp unused :build-wrapper t)

  (must-be-redundant
    ;; no longer passes around the param UNUSED:
    (mutual-recursion (defun even-natp$1 (x)
                        (declare (xargs :verify-guards nil
                                        :measure (acl2-count x)))
                        (if (zp x)
                            t
                          (not (odd-natp$1 (+ -1 x)))))
                      (defun odd-natp$1 (x)
                        (declare (xargs :verify-guards nil
                                        :measure (acl2-count x)))
                        (if (zp x)
                            nil
                          (not (even-natp$1 (+ -1 x))))))
    ;;new wrappers:
    (defun even-natp$1-wrapper (x unused)
      (declare (ignore unused))
      (even-natp$1 x))
    (defun odd-natp$1-wrapper (x unused)
      (declare (ignore unused))
      (odd-natp$1 x))

    ;;theorems about the wrappers:
    (defthm even-natp-becomes-even-natp$1-wrapper
      (equal (even-natp x unused)
             (even-natp$1-wrapper x unused)))
    (defthm odd-natp-becomes-odd-natp$1-wrapper
      (equal (odd-natp x unused)
             (odd-natp$1-wrapper x unused)))))


;;; test of mutual-recursion with :build-wrapper nil

(deftest
  (mutual-recursion
   (defun even-natp (x unused)
     (declare (irrelevant unused))
     (if (zp x)
         t
       (not (odd-natp (+ -1 x) unused))))
   (defun odd-natp (x unused)
     (declare (irrelevant unused))
     (if (zp x)
         nil
       (not (even-natp (+ -1 x) unused)))))

  (drop-irrelevant-params even-natp unused :build-wrapper nil)

  (must-be-redundant
    ;; no longer passes around the param UNUSED:
    (mutual-recursion (defun even-natp$1 (x)
                        (declare (xargs :verify-guards nil
                                        :measure (acl2-count x)))
                        (if (zp x)
                            t
                          (not (odd-natp$1 (+ -1 x)))))
                      (defun odd-natp$1 (x)
                        (declare (xargs :verify-guards nil
                                        :measure (acl2-count x)))
                        (if (zp x)
                            nil
                          (not (even-natp$1 (+ -1 x))))))

    ;;theorems about the new functions:
    (defthm even-natp-becomes-even-natp$1
      (equal (even-natp x unused)
             (even-natp$1 x)))
    (defthm odd-natp-becomes-odd-natp$1
      (equal (odd-natp x unused)
             (odd-natp$1 x)))))

;;; test of mutual-recursion when irrelevant parameters in the mutually recursive
;;; functions have different names.
(deftest
  (mutual-recursion
   (defun even-natp (x unused)
     (declare (irrelevant unused))
     (if (zp x)
         t
       (not (odd-natp (+ -1 x) unused))))
   (defun odd-natp (x unused2)
     (declare (irrelevant unused2))
     (if (zp x)
         nil
       (not (even-natp (+ -1 x) unused2)))))

  ;; fail due to missing irrelevant parameter 'unsued2' in odd-natp
  (must-fail (drop-irrelevant-params even-natp unused))

  ;; succeed when irrelevant parameters from both functions are listed in the
  ;; second parameter
  (drop-irrelevant-params even-natp (unused unused2))

  (must-be-redundant
   ;; no longer passes around the param UNUSED and UNUSED2
   (MUTUAL-RECURSION (DEFUN EVEN-NATP$1 (X)
                       (DECLARE (XARGS :MEASURE (ACL2-COUNT X)
                                       :VERIFY-GUARDS NIL))
                       (IF (ZP X)
                           T (NOT (ODD-NATP$1 (+ -1 X)))))
                     (DEFUN ODD-NATP$1 (X)
                       (DECLARE (XARGS :MEASURE (ACL2-COUNT X)
                                       :VERIFY-GUARDS NIL))
                       (IF (ZP X)
                           NIL (NOT (EVEN-NATP$1 (+ -1 X))))))

   ;;theorems about the new functions:
   (defthm even-natp-becomes-even-natp$1
     (equal (even-natp x unused)
            (even-natp$1 x)))
   (defthm odd-natp-becomes-odd-natp$1
     (equal (odd-natp x unused2)
            (odd-natp$1 x)))))

;; ----------------------------------------------------------------------
;test with a LET:
(deftest
  ;; z is an irrelevant parameter:
  (defun foo (x y z) (declare (irrelevant z)) (let ((w z)) (declare (ignore w)) (+ x y)))
  (drop-irrelevant-params foo z :build-wrapper nil)
  (must-be-redundant
    (DEFUN FOO$1 (X Y)
      (DECLARE (XARGS :VERIFY-GUARDS NIL))
      ((LAMBDA (Y X) (+ X Y)) Y X))
    (DEFTHM FOO-BECOMES-FOO$1
      (EQUAL (FOO X Y Z) (FOO$1 X Y)))))


;; ----------------------------------------------------------------------
;test with multiple irrelevant params, each of which depends on the other

(deftest
  ;;irrel and irrel2 are irrelevant parameters:
  (defun my-len (lst irrel irrel2)
    (declare (irrelevant irrel irrel2))
    (if (endp lst)
        0
      (+ 1 (my-len (rest lst) (+ 7 irrel2) (+ 8 irrel)))))
  (drop-irrelevant-params my-len (irrel irrel2) :build-wrapper t)
  (must-be-redundant
    (defun my-len$1 (lst)
      (declare (xargs :verify-guards nil
                      :measure (acl2-count lst)))
      (if (endp lst)
          0
        (+ 1 (my-len$1 (cdr lst)))))
    ;;the wrapper (exactly equal to the original function):
    (defun my-len$1-wrapper (lst irrel irrel2)
      (my-len$1 lst))
    (defthm my-len-becomes-my-len$1-wrapper
      (equal (my-len lst irrel irrel2)
             (my-len$1-wrapper lst irrel irrel2)))))

;; ----------------------------------------------------------------------
;; Input Validation for the required arguments:
;;   1. fn:   symbol - name of an existing function
;;   2. param(s): symbol or list of symbols - names of irrelevant params

(deftest
  ;; first argument 'fn' not a symbol
  (must-fail (drop-irrelevant-params 123 x))
  (must-fail (drop-irrelevant-params "natp" x))
  ;; first argument 'fn' not name of an existing function
  (must-fail (drop-irrelevant-params blah x))
  (must-fail (drop-irrelevant-params car-cons x))

  (defun foo (x y z) (declare (ignore z)) (+ x y))

  ;; second argument 'params' not a symbol or list of symbols
  (must-fail (drop-irrelevant-params foo 1))
  (must-fail (drop-irrelevant-params foo "z")))

;; ----------------------------------------------------------------------
;; test the :new-name option
(deftest
  ;; z is an irrelevant parameter:
  (defun foo (x y z) (declare (ignore z)) (+ x y))

  ;; :new-name is not a symbol
  (must-fail (drop-irrelevant-params foo z :new-name 123))

  (drop-irrelevant-params foo z :new-name bar :build-wrapper nil)
  (must-be-redundant
    (DEFUN bar (X Y)
      (DECLARE (XARGS :VERIFY-GUARDS NIL))
      (+ X Y))
    (DEFTHM FOO-BECOMES-bar
      (EQUAL (FOO X Y Z) (bar X Y)))))


;; ----------------------------------------------------------------------
(deftest
  (defun foo (x y)
    (declare (ignore y)
             (xargs :guard (and (acl2-numberp x) (acl2-numberp y))))
    (+ x x))
  ;; This previously failed because guards were dropped.  That was because
  ;; conjuncts were not being extracted properly from the untranslated term
  ;; (and (acl2-numberp x) (acl2-numberp y)).
  (drop-irrelevant-params foo y :print :all)
  )

;; ----------------------------------------------------------------------
;; Test with a (declare irrelevant ...)
(deftest
  ;;irrel is an irrelevant parameter:
  (defun my-len (lst irrel)
    (declare (irrelevant irrel))
    (if (endp lst)
        0
      (+ 1 (my-len (rest lst) irrel))))
  (drop-irrelevant-params my-len irrel))

;; ----------------------------------------------------------------------
;; Test the :function-disabled option (t or nil or :auto)

(deftest
  (defun foo (x y z) (declare (ignore z)) (+ x y))
;
; Test: :function-disabled :auto (default)
  (must-succeed*
    (drop-irrelevant-params foo z)

    (assert-event (not (disabledp 'FOO$1))))

  (in-theory (disable foo))

  (must-succeed*
    (drop-irrelevant-params foo z :function-disabled :auto)

    (assert-event (disabledp 'FOO$1)))

;
; Test: :function-disabled t
  (must-succeed*
    (drop-irrelevant-params foo z :function-disabled t)

    (assert-event (disabledp 'FOO$1)))

;
; Test: :function-disabled nil
  (must-succeed*
    (drop-irrelevant-params foo z :function-disabled nil)

    (assert-event (not (disabledp 'FOO$1)))))

;; ----------------------------------------------------------------------
;; Test the :theorem-disabled option (boolean)

(deftest
  (defun foo (x y z) (declare (ignore z)) (+ x y))
;
; Test: :theorem-disabled nil (default)
  (must-succeed*
    (drop-irrelevant-params foo z)

    (assert-event (not (disabledp 'FOO-BECOMES-FOO$1))))

;
; Test: :theorem-disabled t
  (must-succeed*
    (drop-irrelevant-params foo z :theorem-disabled t)

    (assert-event (disabledp 'FOO-BECOMES-FOO$1))))

;; ----------------------------------------------------------------------
;; Test the :show-only option (boolean)

(deftest
  (defun foo (x y z) (declare (ignore z)) (+ x y))

  (must-succeed
   (drop-irrelevant-params foo z :show-only t))

  (must-be-redundant
   ;; a no-op (returns :invisible)
   (drop-irrelevant-params foo z :show-only t)))

;; ----------------------------------------------------------------------
;; Test the :print option (nil or :error or :result or :info or :all)

(deftest
  (defun foo (x y z) (declare (ignore z)) (+ x y))

  (must-fail
   ;; invalid print specifier
   (drop-irrelevant-params foo z :print t))

  (must-succeed
    ;; should print nothing
    (drop-irrelevant-params foo z :print nil))

  (must-succeed
    ;; should print nothing (since there is no error)
    (drop-irrelevant-params foo z :print :error))

  (must-succeed
    ;; should print the result only
    (drop-irrelevant-params foo z :print :result))

  (must-succeed
    ;; should print some info and the result
    (drop-irrelevant-params foo z :print :info))

  (must-succeed
    ;; should print everything (error, info, result, and proof output)
    (drop-irrelevant-params foo z :print :all)))
