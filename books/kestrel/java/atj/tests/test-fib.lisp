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
  '(("Fib0" (fib 0))
    ("Fib1" (fib 1))
    ("Fib10" (fib 10))
    ("Fib20" (fib 20))
    ("Fib30" (fib 30))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Generate Java code for the Fibonacci function, with testing code.

(java::atj fib
           :deep t
           :guards nil
           :java-class "FibDeep"
           :tests *fib-tests*)

(java::atj fib
           :deep t
           :guards t
           :java-class "FibDeepUnderGuards"
           :tests *fib-tests*)

(java::atj fib
           :deep nil
           :guards nil
           :java-class "FibShallow"
           :tests *fib-tests*)

(java::atj fib
           :deep nil
           :guards t
           :java-class "FibShallowUnderGuards"
           :tests *fib-tests*)
