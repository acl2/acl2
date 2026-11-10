; Rust Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "RUST")

(include-book "../interp")
(include-book "factorial")

; Known-answer tests running the factorial MIR body
; (see factorial.lisp) through the interpreter.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define run-factorial ((n acl2::natp))
  :returns (out runoutp)
  (run-fn "factorial"
          (list (value-uint n (uint-type-u64)))
          *factorial-program*
          100000))

(defmacro u64-done (n)
  `(runout-done (value-uint ,n (uint-type-u64))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-event (equal (run-factorial 0) (u64-done 1)))
(assert-event (equal (run-factorial 1) (u64-done 1)))
(assert-event (equal (run-factorial 5) (u64-done 120)))
(assert-event (equal (run-factorial 10) (u64-done 3628800)))

; 20! is the largest factorial that fits in u64.

(assert-event (equal (run-factorial 20) (u64-done 2432902008176640000)))

; Beyond that, the multiplications wrap
; (this body is the overflow-checks-off form of the function).

(assert-event
 (equal (run-factorial 25)
        (u64-done (mod (* 1 2 3 4 5 6 7 8 9 10 11 12 13
                          14 15 16 17 18 19 20 21 22 23 24 25)
                       (expt 2 64)))))

; With too little fuel, the run reports fuel exhaustion.

(assert-event
 (equal (runout-kind (run-fn "factorial"
                             (list (value-uint 20 (uint-type-u64)))
                             *factorial-program*
                             7))
        :limit))

; Calling an unknown function is a stuck (ill-formed) state.

(assert-event
 (equal (runout-kind (run-fn "no-such-function" nil *factorial-program* 10))
        :stuck))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; A two-function program exercising the call terminator:
; main() calls factorial(5), so the run pushes and pops a frame
; and writes the callee's result to the caller's destination place.

(defconst *main-body*
  (make-body
   :locals (list (u64))
   :arg-count 0
   :blocks
   (list (make-basic-block
          :statements nil
          :terminator (terminator-call
                       (operand-constant (const-fn "factorial"))
                       (list (const-u64 5))
                       (make-place :local 0 :projection nil)
                       1))
         (make-basic-block
          :statements nil
          :terminator (terminator-return)))))

(defconst *main-program*
  (make-mir-program
   :funs (omap::update "main"
                       *main-body*
                       (omap::update "factorial" *factorial-body* nil))
   :adts nil))

(assert-event (mir-programp *main-program*))

(assert-event (equal (run-fn "main" nil *main-program* 1000)
                     (u64-done 120)))
