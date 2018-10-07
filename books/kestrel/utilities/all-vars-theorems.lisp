; Theorems about ALL-VARS (and ALL-VARS1)
;
; Copyright (C) 2016 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "tools/flag" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc theorems-about-all-vars
  :parents (theorems-about-non-kestrel-books system-utilities-non-built-in)
  :short "Theorems about @(tsee all-vars)."
  :long
  "<p>
   See the file for lemmas about @('all-vars1').
   </p>
   @(def symbol-listp-of-all-vars)
   @(def true-listp-of-all-vars)")

;;;  Theorems about all-vars1

(make-flag all-vars1)

(defthm-flag-all-vars1
  (defthm true-listp-of-all-vars1
    (equal (true-listp (all-vars1 term ans))
           (true-listp ans))
    :flag all-vars1)
  (defthm true-listp-of-all-vars1-lst
    (equal (true-listp (all-vars1-lst lst ans))
           (true-listp ans))
    :flag all-vars1-lst))

(defthm true-listp-of-all-vars1-type
  (implies (true-listp ans)
           (true-listp (all-vars1 term ans)))
  :rule-classes :type-prescription)

(defthm true-listp-of-all-vars1-lst-type
  (implies (true-listp ans)
           (true-listp (all-vars1-lst term ans)))
  :rule-classes :type-prescription)

(defthm-flag-all-vars1
  (defthm symbol-listp-of-all-vars1
    (implies (pseudo-termp term)
             (equal (symbol-listp (all-vars1 term ans))
                    (symbol-listp ans)))
    :flag all-vars1)
  (defthm symbol-listp-of-all-vars1-lst
    (implies (pseudo-term-listp lst)
             (equal (symbol-listp (all-vars1-lst lst ans))
                    (symbol-listp ans)))
    :flag all-vars1-lst))

;;;  Theorems about all-vars

(defthm symbol-listp-of-all-vars
  (implies (pseudo-termp term)
           (symbol-listp (all-vars term))))

(defthm true-listp-of-all-vars
  (true-listp (all-vars term))
  :rule-classes (:rewrite :type-prescription))
