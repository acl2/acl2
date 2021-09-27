; A variant of verify-guards with better treatment of hints
;
; Copyright (C) 2017-2021 Kestrel Institute
; Copyright (C) 2017, Regents of the University of Texas
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Main Author: Eric Smith (eric.smith@kestrel.edu)
; Contributing Author: Matt Kaufmann

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; A version of verify-guards that respects theory hints on Goal (verify-guards
;; itself can simplify a guard obligation using definitions/rules that are
;; disallowed by the theory hint given to Goal !).

;; Tools that do verify-guards in a very restricted theory should
;; probably use verify-guards$ instead of verify-guards.

;; See verify-guards-dollar-example.lisp for an example of when this utility is needed.

(defun verify-guards$-fn (fn hints args)
  (let* ((goal-hints (cdr (assoc-equal "Goal" hints))))
    (if (assoc-keyword :in-theory goal-hints)
        `(encapsulate nil
           (local (in-theory ,(cadr (assoc-keyword :in-theory goal-hints))))
           (verify-guards ,fn ,@args))
      ;; no theory hint given, so no need for the encapsulate:
      `(verify-guards ,fn ,@args))))

(defmacro verify-guards$ (name &rest args &key hints &allow-other-keys)
  (verify-guards$-fn name hints args))
