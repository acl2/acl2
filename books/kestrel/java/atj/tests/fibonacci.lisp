; Java Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "../implementation" :ttags (:open-input-channel (:oslib) (:quicklisp) :quicklisp.osicat))

(include-book "../types-for-natives")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Fibonacci function.

(defun fib (n)
  (declare (xargs :guard (natp n)))
  (cond ((zp n) 1)
        ((= n 1) 1)
        (t (+ (fib (- n 1))
              (fib (- n 2))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Tests for the Fibonacci function.

(defconst *fib-tests*
  '(("Fibonacci0" (fib 0))
    ("Fibonacci1" (fib 1))
    ("Fibonacci10" (fib 10))
    ("Fibonacci20" (fib 20))
    ("Fibonacci30" (fib 30))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Generate Java code for the Fibonacci function, with testing code.

(java::atj fib
           :deep t
           :guards nil
           :java-class "FibonacciDeep"
           :tests *fib-tests*)

(java::atj fib
           :deep t
           :guards t
           :java-class "FibonacciDeepUnderGuards"
           :tests *fib-tests*)

(java::atj fib
           :deep nil
           :guards nil
           :java-class "FibonacciShallow"
           :tests *fib-tests*)

(java::atj fib
           :deep nil
           :guards t
           :java-class "FibonacciShallowUnderGuards"
           :tests *fib-tests*)
