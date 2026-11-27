; Erlang in ACL2
;
; Copyright (C) Kuter Bora.
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Kuter Bora
; Contributing Author: Mark Greenstreet

(in-package "ACL2")
(include-book "../erl-eval")
(include-book "std/testing/assert-equal" :dir :system)

; Some utility for testing

; Evaluate x with 10000 fuel.
(defun eval-expr (x)
  (apply-k 
    (make-erl-state)
    (list (make-erl-k
            :fuel 10000
            :kont (make-kont-expr :expr x)))))

; Evaluate x with 10000 fuel, and the given bindings.
(defun eval-expr-bind (x b)
  (apply-k 
    (make-erl-state :bind b)
    (list (make-erl-k
            :fuel 10000
            :kont (make-kont-expr :expr x)))))

; Evaluate x with 10000 fuel, and the given world and module.
(defun eval-expr-world (x m w)
  (apply-k
    (make-erl-state :module m :world w)
    (list (make-erl-k
            :fuel 10000
            :kont (make-kont-expr :expr x)))))

; Evaluate xs with 10000 fuel.
(defun eval-exprs (xs)
  (apply-k 
    (make-erl-state)
    (list (make-erl-k
            :fuel 10000
            :kont (make-kont-exprs :exprs xs)))))

; Evaluate xs with 10000 fuel, and the given bindings.
(defun eval-exprs-bind (xs b)
  (apply-k 
    (make-erl-state :bind b)
    (list (make-erl-k
            :fuel 10000
            :kont (make-kont-exprs :exprs xs)))))

; Evaluate xs with 10000 fuel, and the given world and module.
(defun eval-exprs-world (xs m w)
  (apply-k
    (make-erl-state :module m :world w)
    (list (make-erl-k
            :fuel 10000
            :kont (make-kont-exprs :exprs xs)))))

; Evaluate x with 10000 fuel, and return the value it produces.
(defun eval-expr-val (x)
  (erl-state->in (eval-expr x)))

; Evaluate x with 10000 fuel and the given bindings, and return the
; value it produces.
(defun eval-expr-bind-val (x b)
  (erl-state->in (eval-expr-bind x b)))

; Evaluate x with 10000 fuel and the given module and world, and return
; the value it produces.
(defun eval-expr-world-val (x m w)
  (erl-state->in (eval-expr-world x m w)))

; Evaluate xs with 10000 fuel, and return the value it produces.
(defun eval-exprs-val (xs)
  (erl-state->in (eval-exprs xs)))

; Evaluate xs with 10000 fuel and the given bindings, and return the
; value it produces.
(defun eval-exprs-bind-val (xs b)
  (erl-state->in (eval-exprs-bind xs b)))

; Evaluate xs with 10000 fuel and the given module and world, and return
; the value it produces.
(defun eval-exprs-world-val (xs m w)
  (erl-state->in (eval-exprs-world xs m w)))