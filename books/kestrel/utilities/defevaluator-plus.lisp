; A nicer interface to defevaluator
;
; Copyright (C) 2014-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;this is used (or will be used?) by state-machines.lisp

(include-book "kestrel/utilities/world" :dir :system)

;; A nicer interface to defevaluator.  Improvements include:
;; 1. looks up the arities of the functions in the world.
;; 2. auto-generates the name of the -list function that will be mutually recursive with the evaluator.

(defun make-defevaluator-call (fn state)
  (declare (xargs :stobjs state
                  :guard (symbolp fn)))
  (let ((formals (fn-formals fn (w state))))
   `(,fn ,@formals)))

;use a defmap
(defun make-defevaluator-calls (fns state)
  (declare (xargs :stobjs state
                  :guard (symbol-listp fns)))
  (if (endp fns)
      nil
    (cons (make-defevaluator-call (first fns) state)
          (make-defevaluator-calls (rest fns) state))))

(defun defevaluator+-event (name fns state)
  (declare (xargs :stobjs state
                  :guard (and (symbolp name)
                              (symbol-listp fns))))
  (let* ((lst-name (add-suffix-to-fn name "-LIST"))
         (calls (make-defevaluator-calls fns state)))
  `(defevaluator ,name ,lst-name
     ,calls)))

(defmacro defevaluator+ (name &rest fns)
  `(make-event (defevaluator+-event ',name ',fns state)))

;test:
(local (progn (defevaluator+ myev binary-*)
              (defthm test (equal (myev '(binary-* '2 x) '((x . 3))) 6))))
