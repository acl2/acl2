; Proof of correctness of negate-term
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "negate-term")
(include-book "kestrel/evaluators/not-eval" :dir :system)

(defthm negate-term-correct
  (implies (pseudo-termp term)
           (iff (not-eval (negate-term term) a)
                (not (not-eval term a))))
  :hints (("Goal" :in-theory (enable negate-term))))
