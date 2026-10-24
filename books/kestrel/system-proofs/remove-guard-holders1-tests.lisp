; Tests and examples for remove-guard-holders1.lisp
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

; cert_param: (non-acl2r)

;; Counterexamples and examples for the theorems in
;; remove-guard-holders1.lisp.  This book is not included by top.lisp.

(include-book "remove-guard-holders1")

;; Counterexample showing that pseudo-termp is not enough:

;; A call of THE-CHECK with two arguments becomes its last argument, but it
;; evaluates to its (missing) third argument:
(defthm remove-guard-holders1-incorrect-with-wrong-arity-for-the-check
  (let ((term '(the-check 'nil 't)))
    (and (pseudo-termp term)
         (equal (mv-nth 1 (remove-guard-holders1 nil term lamp)) ''t)
         (not (equal (remove-guard-holders-eval (mv-nth 1 (remove-guard-holders1 nil term lamp)) a)
                     (remove-guard-holders-eval term a)))))
  :hints (("Goal" :expand ((remove-guard-holders1 nil '(the-check 'nil 't) lamp)
                           (remove-guard-holders1 t ''t lamp))))
  :rule-classes nil)

;; The comments in remove-guard-holders1 also say that "if changedp is nil,
;; then changedp0 is nil and new-term is identical to term".  That used to
;; fail when the result came from the TO-DF case, which returned the CHANGEDP
;; flag for the argument of TO-DF and ignored CHANGEDP0, so that, in the
;; example below, CHANGEDP was NIL even though the RETURN-LAST was removed, and
;; remove-guard-holders-weak then kept the RETURN-LAST.  Now the TO-DF case
;; returns (OR CHANGEDP0 CHANGEDP1), and the RETURN-LAST is removed (see
;; remove-guard-holders1-properties.lisp for the general result):
(defthm remove-guard-holders1-changedp-for-to-df
  (equal (remove-guard-holders1 nil '(return-last 'progn (bar) (to-df x)) nil)
         (mv t '(to-df x)))
  :rule-classes nil)

(defthm remove-guard-holders-weak-removes-return-last-around-to-df
  (equal (remove-guard-holders-weak '(foo (return-last 'progn (bar) (to-df x))) nil)
         '(foo (to-df x)))
  :rule-classes nil)
