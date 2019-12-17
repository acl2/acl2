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

; Fibonacci function (with "natural" recursion).

(defun fib (n)
  (declare (xargs :guard (natp n)))
  (cond ((zp n) 1)
        ((= n 1) 1)
        (t (+ (fib (- n 1))
              (fib (- n 2))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Tail-recursive Fibonacci function.

(defun fib-tail (n prev curr)
  (declare (xargs :guard (and (natp n) (natp prev) (natp curr))))
  (if (zp n)
      curr
    (fib-tail (1- n) curr (+ prev curr))))

(defthmd fib-tail-correct-lemma
  (implies (and (natp prev)
                (natp curr))
           (equal (fib-tail n prev curr)
                  (if (zp n)
                      curr
                    (+ (* prev (fib (1- n)))
                       (* curr (fib n))))))
  :hints (("Goal" :expand ((fib-tail 1 prev curr)))))

(defthmd fib-tail-correct
  (equal (fib-tail n 0 1)
         (fib n))
  :hints (("Goal" :in-theory (enable fib-tail-correct-lemma))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Tests for the Fibonacci function.

(defconst *fib-tests*
  '(("Fibonacci0" (fib 0))
    ("Fibonacci1" (fib 1))
    ("Fibonacci10" (fib 10))
    ("Fibonacci20" (fib 20))
    ("Fibonacci30" (fib 30))
    ("FibonacciTail0" (fib-tail 0 0 1))
    ("FibonacciTail1" (fib-tail 1 0 1))
    ("FibonacciTail10" (fib-tail 10 0 1))
    ("FibonacciTail20" (fib-tail 20 0 1))
    ("FibonacciTail30" (fib-tail 30 0 1))))
