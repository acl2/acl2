; Wrap a pattern (indicated by a unary lambda) around a term
;
; Copyright (C) 2014-2021 Kestrel Institute
; Copyright (C) 2015, Regents of the University of Texas
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "unary-lambdap")
(include-book "sublis-var-simple")

;todo: rename?
(defun wrap-pattern-around-term (term pattern)
  (declare (xargs :guard (and ;(PSEUDO-TERMP TERM)
                              (unary-lambdap pattern))
                  :guard-hints (("Goal" :in-theory (enable PSEUDO-LAMBDAP))))) ;todo
  (let* ((lambda-formals (second pattern))
         (lambda-body (third pattern))
         (var (first lambda-formals)) ;the only formal
         )
    (sublis-var-simple (acons var term nil) lambda-body)))

;; (assert-event (equal (wrap-pattern-around-term 'boo '(lambda (x) (eq :fail x))) '(EQ :FAIL BOO)))
