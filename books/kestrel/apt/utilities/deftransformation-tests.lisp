; Simple tests of deftransformation
;
; Copyright (C) 2017-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Simple tests of deftransformation

;; For a more realistic use, see the call of deftransformation in
;; copy-function.lisp and the resulting forms (re-iterated in
;; copy-function-expansion.lisp).

(include-book "deftransformation")
(include-book "kestrel/utilities/deftest" :dir :system)

(deftest
  ;; A trivial "transformation" that just defines a function called fn
  (defun foo-event (fn state)
    (declare (xargs :stobjs state))
    (mv nil
        `(progn (defun ,fn (x) x))
        state))

  (deftransformation foo
    (fn) ;one required arg
    ()   ;no optional args
    ))

;; Here the function is not called 'fn' (this once caused a problem)
(deftest
  ;; A trivial "transformation" that just defines a function called fn
  (defun foo-event (f state)
    (declare (xargs :stobjs state))
    (mv nil
        `(progn (defun ,f (x) x))
        state))

  (deftransformation foo
    (fn) ;one required arg
    ()   ;no optional args
    ))
