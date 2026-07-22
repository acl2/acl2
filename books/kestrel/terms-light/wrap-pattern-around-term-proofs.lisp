; Proofs about wrap-pattern-around-term

; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "wrap-pattern-around-term")
(local (include-book "sublis-var-simple-proofs"))

(defthm pseudo-termp-of-wrap-pattern-around-term
  (implies (and (pseudo-termp term)
                (unary-lambdap pattern))
           (pseudo-termp (wrap-pattern-around-term term pattern)))
  :hints (("Goal" :in-theory (enable wrap-pattern-around-term
                                     unary-lambdap
                                     pseudo-lambdap))))
