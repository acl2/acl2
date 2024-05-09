(in-package :cl-utilities)

;; This is portable Common Lisp, but implementation-specific code may
;; improve performance considerably.
(defun expt-mod (n exponent modulus)
  "As (mod (expt n exponent) modulus), but more efficient."
  (declare (optimize (speed 3) (safety 0) (space 0) (debug 1)))
  ;; It's much faster on SBCL and ACL to use the simple method, and
  ;; trust the compiler to optimize it. This may be the case on other
  ;; Lisp implementations as well.
  #+(or sbcl allegro) (mod (expt n exponent) modulus)
  #-(or sbcl allegro)
  (if (some (complement #'integerp) (list n exponent modulus))
      (mod (expt n exponent) modulus)
      (loop with result = 1
	    for i of-type fixnum from 0 below (integer-length exponent)
	    for sqr = n then (mod (* sqr sqr) modulus)
	    when (logbitp i exponent) do
	    (setf result (mod (* result sqr) modulus))
	    finally (return result))))

;; If the compiler is going to expand compiler macros, we should
;; directly inline the simple expansion; this lets the compiler do all
;; sorts of fancy optimizations based on type information that
;; wouldn't be used to optimize the normal EXPT-MOD function.
#+(or sbcl allegro)
(define-compiler-macro expt-mod (n exponent modulus)
  `(mod (expt ,n ,exponent) ,modulus))


;; Here's some benchmarking code that may be useful. I probably
;; completely wasted my time declaring ITERATIONS to be a fixnum.
#+nil
(defun test (&optional (iterations 50000000))
  (declare (optimize (speed 3) (safety 0) (space 0) (debug 1))
	   (fixnum iterations))
  (time (loop repeat iterations do (mod (expt 12 34) 235)))
  (time (loop repeat iterations do (expt-mod 12 34 235))))