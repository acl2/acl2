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
(local (include-book "../lists-light/subsetp-equal"))

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

(local
 (defthm subsetp-equal-of-free-vars-in-term-of-assoc-equal-and-free-vars-in-terms-of-strip-cdrs
   (implies (and (member-equal term (strip-cars alist))
                 (assoc-equal term alist))
            (subsetp-equal (free-vars-in-term (cdr (assoc-equal term alist)))
                           (free-vars-in-terms (strip-cdrs alist))))
   :hints (("Goal" :in-theory (enable subsetp-equal assoc-equal free-vars-in-terms)))))

(defthm-flag-free-vars-in-term
  ;; If we substitute all variables in the term, then the new free vars are limited to the free vars in the terms put in by substitution.
  (defthm subsetp-equal-of-free-vars-in-term-of-sublis-var-simple-and-free-vars-in-terms-of-strip-cdrs
    (implies (subsetp-equal (free-vars-in-term term)
                            (strip-cars alist))
             (subsetp-equal (free-vars-in-term (sublis-var-simple alist term))
                            (free-vars-in-terms (strip-cdrs alist))))
    :flag free-vars-in-term)
  (defthm subsetp-equal-of-free-vars-in-term-of-sublis-var-simple-lst-and-free-vars-in-terms-of-strip-cdrs
    (implies (subsetp-equal (free-vars-in-terms terms)
                            (strip-cars alist))
             (subsetp-equal (free-vars-in-terms (sublis-var-simple-lst alist terms))
                            (free-vars-in-terms (strip-cdrs alist))))
    :flag free-vars-in-terms)
  :hints (("Goal" :in-theory (enable sublis-var-simple
                                     sublis-var-simple-lst
                                     free-vars-in-term
                                     free-vars-in-terms))))

;; Simple consequence of the above.
(defthm subsetp-equal-of-free-vars-in-term-of-sublis-var-simple-and-free-vars-in-terms-of-strip-cdrs-gen
  (implies (and (subsetp-equal (free-vars-in-term term) ; the alist binds all the vars, so any free vars in the result come from the alist
                               (strip-cars alist))
                (subsetp-equal (free-vars-in-terms (strip-cdrs alist)) free))
           (subsetp-equal (free-vars-in-term (sublis-var-simple alist term))
                          free)))
