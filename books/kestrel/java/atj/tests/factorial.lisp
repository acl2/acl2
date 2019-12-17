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

; Factorial function (with "natural" recursion).

(defun fact (n)
  (declare (xargs :guard (natp n)))
  (if (zp n)
      1
    (* n (fact (1- n)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Tail-recursive factorial function.

(defun fact-tail (n r)
  (declare (xargs :guard (and (natp n) (natp r))))
  (if (zp n)
      r
    (fact-tail (1- n) (* n r))))

(local (include-book "arithmetic/top" :dir :system))

(defthmd fact-tail-correct-lemma
  (implies (natp r)
           (equal (fact-tail n r)
                  (* r (fact n)))))

(defthm fact-tail-correct
  (equal (fact-tail n 1)
         (fact n))
  :hints (("Goal" :in-theory (enable fact-tail-correct-lemma))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Tests for the factorial functions.

(defconst *fact-tests*
  '(("Factorial0" (fact 0))
    ("Factorial1" (fact 1))
    ("Factorial10" (fact 10))
    ("Factorial100" (fact 100))
    ("Factorial1000" (fact 1000))
    ("Factorial10000" (fact 10000))
    ("FactorialTail0" (fact-tail 0 1))
    ("FactorialTail1" (fact-tail 1 1))
    ("FactorialTail10" (fact-tail 10 1))
    ("FactorialTail100" (fact-tail 100 1))
    ("FactorialTail1000" (fact-tail 1000 1))
    ("FactorialTail10000" (fact-tail 10000 1))))
