; Erlang in ACL2
;
; Copyright (C) Kuter Bora.
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Kuter Bora
; Contributing Author: Mark Greenstreet

(in-package "ACL2")
(include-book "../top")
(include-book "../../evaluator/examples/util")

; Some utility for testing

; Make a process that will evaluate the given expression with the given bidnings and 10000 fuel.
(defun make-expr-proc (self bind world x)
  (make-proc
    :s (make-erl-state :bind bind :self self :world world)
    :klst (list (make-erl-k :fuel 10000 :kont (make-kont-expr :expr x)))))

; Make a process that will evaluate the given expressions with the given bidnings, world, and 10000 fuel.
(defun make-exprs-proc (self bind xs)
  (make-proc
    :s (make-erl-state :bind bind :self self)
    :klst (list (make-erl-k :fuel 10000 :kont (make-kont-exprs :exprs xs)))))

; helper to print the leaf values
(define print-omap-values ((n network-p))
  :measure (acl2-count (network-fix n))
  (b* ((n (network-fix n))
       ((if (omap::emptyp n)) 'ok)
       (val (erl-state->in (proc->s (omap::head-val n))))
       (- (cw "~x0~%" val)))
    (print-omap-values (omap::tail n))))