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

; Factorial function.

(defun fact (n)
  (declare (xargs :guard (natp n)))
  (if (zp n)
      1
    (* n (fact (1- n)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Tests for the factorial function.

(defconst *fact-tests*
  '(("Fact0" (fact 0))
    ("Fact1" (fact 1))
    ("Fact10" (fact 10))
    ("Fact100" (fact 100))
    ("Fact1000" (fact 1000))
    ("Fact10000" (fact 10000))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Generate Java code for the factorial function, with testing code.

(java::atj fact
           :deep t
           :guards nil
           :java-class "FactDeep"
           :tests *fact-tests*)

(java::atj fact
           :deep t
           :guards t
           :java-class "FactDeepUnderGuards"
           :tests *fact-tests*)

(java::atj fact
           :deep nil
           :guards nil
           :java-class "FactShallow"
           :tests *fact-tests*)

(java::atj fact
           :deep nil
           :guards t
           :java-class "FactShallowUnderGuards"
           :tests *fact-tests*)
