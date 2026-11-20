; Erlang in ACL2
;
; Copyright (C) Kuter Bora.
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Kuter Bora
; Contributing Author: Mark Greenstreet

(in-package "ACL2")
(include-book "util")

; This file contains some basic tests for try-catch expressions.

; try 1, 2, 3, ok catch
;   Class:Reason:Stack -> Reason
; end.

; no exception
(assert-equal
  (eval-expr-val
    '(:try
      ((:integer 1) (:integer 2) (:integer 3) (:atom ok))
      (((cases
          (:tuple
            (:cons (:var Class)
                   (:cons (:var Reason)
                          (:cons (:var Stack) (:nil))))))
        (guards)
        (body (:var Reason))))))
  '(:atom ok))

; caught exception
(assert-equal
  (eval-expr-val
    '(:try
      ((:binop div (:integer 1) (:integer 0)))
      (((cases
          (:tuple
            (:cons (:var Class)
                   (:cons (:var Reason)
                          (:cons (:var Stack) (:nil))))))
        (guards)
        (body (:var Reason))))))
  '(:atom badarith))

; uncaught exception
(assert-equal
  (eval-expr-val
    '(:try
      ((:binop div (:integer 1) (:integer 0)))
      (((cases
          (:tuple
            (:cons (:var Class)
                   (:cons (:atom badarg)
                          (:cons (:var Stack) (:nil))))))
        (guards)
        (body (:atom error))))))
  '(:excpt (:atom error) (:atom badarith) nil))