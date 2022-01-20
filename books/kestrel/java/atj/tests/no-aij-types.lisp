; Java Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "../atj" :ttags ((:open-output-channel!) (:oslib) (:quicklisp) :quicklisp.osicat))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Modular Java int factorial, with tail-recursion (compiled to a loop).

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define int-fact-loop ((n java::int-valuep) (r java::int-valuep))
  :guard (java::boolean-value->bool (java::int-greateq n (java::int-value 0)))
  :returns (result java::int-valuep)
  (if (mbt (and (java::int-valuep n)
                (java::int-valuep r)
                (>= (java::int-value->int n) 0)))
      (if (java::boolean-value->bool (java::int-eq n (java::int-value 0)))
          r
        (java::int-mul n
                       (int-fact-loop (java::int-sub n (java::int-value 1))
                                      (java::int-mul n r))))
    (java::int-value 0))
  :measure (nfix (java::int-value->int n))
  :hints (("Goal" :in-theory (enable java::int-eq
                                     java::int-greateq
                                     java::int-sub
                                     sbyte32p)))
  :verify-guards nil ; done below
  :prepwork ((local (include-book "arithmetic-5/top" :dir :system)))
  ///
  (verify-guards int-fact-loop
    :hints (("Goal" :in-theory (enable java::int-eq
                                       java::int-greateq
                                       java::int-sub
                                       java::int-valuep
                                       sbyte32p)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define int-fact ((n java::int-valuep))
  :guard (java::boolean-value->bool (java::int-greateq n (java::int-value 0)))
  :returns (result java::int-valuep)
  (int-fact-loop n (java::int-value 1)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(java::atj-main-function-type int-fact-loop (:jint :jint) :jint)

(java::atj-main-function-type int-fact (:jint) :jint)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *int-fact-tests*
  '(("IntFact0" (int-fact (java::int-value 0)))
    ("IntFact1" (int-fact (java::int-value 0)))
    ("IntFact2" (int-fact (java::int-value 0)))
    ("IntFact3" (int-fact (java::int-value 0)))
    ("IntFact4" (int-fact (java::int-value 0)))
    ("IntFact5" (int-fact (java::int-value 0)))
    ("IntFact6" (int-fact (java::int-value 0)))
    ("IntFact7" (int-fact (java::int-value 0)))
    ("IntFact8" (int-fact (java::int-value 0)))
    ("IntFact9" (int-fact (java::int-value 0)))
    ("IntFact100" (int-fact (java::int-value 0)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(java::atj int-fact
           :deep nil
           :guards t
           :no-aij-types t
           :java-class "NoAIJTypes"
           :tests *int-fact-tests*)
