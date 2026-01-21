;; SPDX-FileCopyrightText: Copyright (c) 2020 Andrew T. Walter <me@atwalter.com>
;; SPDX-License-Identifier: MIT
(load "try-load-quicklisp.lisp")
(pushnew (truename "../") ql:*local-project-directories*)
(ql:register-local-projects)
(ql:quickload :cl-z3)

(defpackage :z3-bitvectors
  (:use :cl :z3))

(in-package :z3-bitvectors)

(solver-init)

(solver-push)
(z3-assert
 ;; A bitvector variable must be given a length.
 (v (_ :bitvec 5))
 ;; the nil below indicates that we want to treat v as an unsigned
 ;; value when we convert it to an integer.
 (= (bv2int v nil) 20))
(check-sat)
(get-model)
;; Bitvectors are converted to integers when treating as an assignment
(get-model-as-assignment)
(solver-pop)

;; You can represent bitvector constants using int2bv
(solver-push)
(z3-assert
 (v (_ :bitvec 10) x (_ :bitvec 4))
 ;; the second number is the integer to convert to a bitvector, the
 ;; first number is the length of the bitvector to convert to.
 (and (= v ((_ int2bv 10) 27))
      (= x ((_ int2bv 4) -4))))
(check-sat)
(get-model)
(get-model-as-assignment)
;; note that Z3's bitvectors are sign agnostic - individual operators
;; may treat them as signed or unsigned values.
;; We always interpret bitvectors as unsigned integers.
(solver-pop)

;; You can also write bitvector constants using `bv` with lists of
;; {0,1} or booleans.
;; Note that Z3 treats bitvectors as big-endian when converting back to a number.
(solver-push)
(z3-assert
 (v (_ :bitvec 5) x (_ :bitvec 3))
 (and (= v (bv 0 0 0 1 1))
      (= x (bv t nil nil))))
(check-sat)
(get-model-as-assignment)
(solver-pop)

;; There are many functions that operate on bitvectors; see
;; src/ffi/z3-api.lisp if you'd like more information on any of them.
;; See src/z3/ast.lisp for a mapping of z3's function names to the
;; names that are usable in z3-assert.
(solver-push)
(z3-assert
 (v (_ :bitvec 4))
 (= v (bvadd ((_ int2bv 4) 15) ((_ int2bv 4) -1))))
(check-sat)
(get-model-as-assignment)
(solver-pop)

(solver-push)
(z3-assert (x y :int z (_ :bitvec 8))
           (and (>= x 0)
                (>= y 0)
                (< (+ x y) 256)
                (= z ((_ int2bv 8) (+ x y)))))
(check-sat)
(get-model-as-assignment)
(solver-pop)

#|
;; TODO why is this slow? Performance regression?
(solver-push)
(z3-assert
 (x y :int z w (_ :bitvec 8))
 (and (>= x 0)
      (>= y 0)
      (< (+ x y) 256)
      (= z ((_ int2bv 8) x))
      (= w ((_ int2bv 8) y))
      (not (= (+ x y) (bv2int (bvadd z w) nil)))))
(check-sat)
(solver-pop)
|#
