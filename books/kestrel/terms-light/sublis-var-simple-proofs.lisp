; Proofs about sublis-var-simple
;
; Copyright (C) 2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "sublis-var-simple")
(include-book "lambdas-closed-in-termp")

;move?
(local
 (defthm lambdas-closed-in-termp-of-cdr-of-assoc-equal
   (implies (lambdas-closed-in-termsp (strip-cdrs alist))
            (lambdas-closed-in-termp (cdr (assoc-equal term alist))))
   :hints (("Goal" :in-theory (enable assoc-equal)))))

(defthm-flag-sublis-var-simple
  (defthm lambdas-closed-in-termp-of-sublis-var-simple
    (implies (and (pseudo-termp term)
                  (lambdas-closed-in-termp term)
                  (lambdas-closed-in-termsp (strip-cdrs alist)))
             (lambdas-closed-in-termp (sublis-var-simple alist term)))
    :flag sublis-var-simple)
  (defthm lambdas-closed-in-termp-of-sublis-var-lst-simple
    (implies (and (pseudo-term-listp terms)
                  (lambdas-closed-in-termsp terms)
                  (lambdas-closed-in-termsp (strip-cdrs alist)))
             (lambdas-closed-in-termsp (sublis-var-simple-lst alist terms)))
    :flag sublis-var-simple-lst)
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable sublis-var-simple
                              sublis-var-simple-lst
                              lambdas-closed-in-termp))))
