; Tests for add-return-value
;
; Copyright (C) 2021-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)
; Supporting Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "../add-return-values")
(include-book "kestrel/utilities/deftest" :dir :system)

;; A typical example (tail-recursive function that modifies a param that is not returned):
(deftest
  (defun bar (x y)
    (if (zp x)
        y
      (bar (+ -1 x) (+ 1 y))))
  ;; Since x gets modified in the recursive call, it may need to be returned:
  (add-return-values bar (x))
  (must-be-redundant
   (defun bar$1 (x y)
     (declare (xargs :measure (acl2-count x)
                     :verify-guards nil))
     (if (zp x)
         (mv y x) ; now returns x
       (bar$1 (+ -1 x) (+ 1 y))))
   (defthm bar-becomes-bar$1
     (equal (bar x y)
            (mv-let (rv x) ; or use y instead of "rv"
              (bar$1 x y)
              (declare (ignore x))
              rv)))))

;; test with a non-recursive function
(deftest
  (defun foo (x) (+ 1 x))
  (add-return-values foo (x))
  (must-be-redundant
   (DEFUN FOO$1 (X)
     (DECLARE (XARGS :VERIFY-GUARDS NIL))
     (MV (+ 1 X) X) ;now also returns x
     )
   (DEFTHM FOO-BECOMES-FOO$1
     (EQUAL (FOO X)
            (MV-LET (RV X)
              (FOO$1 X)
              (DECLARE (IGNORE X))
              RV)))))

;; test with a recursive function (and an IF)
(deftest
  (add-return-values member-equal (x))
  (must-be-redundant
   (DEFUND MEMBER-EQUAL$1 (X LST)
     (DECLARE (XARGS :VERIFY-GUARDS T
                     :MEASURE (ACL2-COUNT LST)
                     :GUARD (TRUE-LISTP LST)))
     (COND ((ENDP LST) (MV NIL X))
           ((EQUAL X (CAR LST)) (MV LST X))
           (T (MEMBER-EQUAL$1 X (CDR LST)))))
   (DEFTHM MEMBER-EQUAL-BECOMES-MEMBER-EQUAL$1
     (EQUAL (MEMBER-EQUAL X LST)
            (MV-LET (RV X)
              (MEMBER-EQUAL$1 X LST)
              (DECLARE (IGNORE X))
              RV)))))

;; test function with a let
(deftest
  (defun foo (x)
    (let ((y (+ 1 x)))
      y))
  (add-return-values foo (x))
  (must-be-redundant
   (DEFUN FOO$1 (X)
     (DECLARE (XARGS :VERIFY-GUARDS NIL))
     (LET ((Y (+ 1 X))) (MV Y X)))
   (DEFTHM FOO-BECOMES-FOO$1
     (EQUAL (FOO X)
            (MV-LET (RV X)
              (FOO$1 X)
              (DECLARE (IGNORE X))
              RV)))))

;; Test with a lambda with a trivial arg (x)
(deftest
  (defun foo (x)
    (let ((y (+ 1 x)))
      (+ x y)))
  (add-return-values foo (x))
  (must-be-redundant
   (DEFUN FOO$1 (X)
     (DECLARE (XARGS :VERIFY-GUARDS NIL))
     (let ((y (+ 1 x)))
      (mv (+ x y) x)))
   (DEFTHM FOO-BECOMES-FOO$1
     (EQUAL (FOO X)
            (MV-LET (RV X)
              (FOO$1 X)
              (DECLARE (IGNORE X))
              RV)))))

;; test tail-recursive function with a lambda
(deftest
  ;; always returns t:
  (defun foo (x)
    (declare (xargs :measure (if (bool-fix x) 1 0)))
    (if x
        (let ((y (not x)))
          (foo y))
      (not x)))
  ;; (add-return-values foo (x)) ;TODO: (DEFTHM FOO-BECOMES-FOO$1 ...) fails (need (:e zp) due to mv-nth opening, also need to open (foo$1 x)
  )

;; Test with a non-tail-recursive function
;; TODO: Fails!
;; (deftest
;;   (add-return-values len (x))
;;   (must-be-redundant ..)
;; )

;; TODO: Fails due to capture
;; (deftest
;;   (defun foo (x y)
;;     (let ((y (+ 1 y)))
;;       (+ x y)))
;;   (add-return-values foo (y)))
