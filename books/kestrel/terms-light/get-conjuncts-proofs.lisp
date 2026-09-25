; Proof of correctness of get-conjuncts
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "get-conjuncts")
(include-book "kestrel/evaluators/if-eval" :dir :system)

;; The conjuncts all evaluate to true exactly when TERM does.
(defthm all-eval-to-true-with-if-eval-of-get-conjuncts
  (iff (all-eval-to-true-with-if-eval (get-conjuncts term) a)
       (if-eval term a))
  :hints (("Goal" :in-theory (enable get-conjuncts))))

;; Conjoining the conjuncts gives back something equivalent to TERM.
(defthm if-eval-of-conjoin-of-get-conjuncts
  (iff (if-eval (conjoin (get-conjuncts term)) a)
       (if-eval term a)))
