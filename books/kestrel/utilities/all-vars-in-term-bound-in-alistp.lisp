; A utility to quickly check that all vars in a term are bound in an alist
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/terms-light/free-vars-in-term" :dir :system)

;; Note that this avoids doing any consing (e.g., to construct the list of vars
;; in the term, or to extract the strip-cars of the alist).

(mutual-recursion
 (defund all-vars-in-term-bound-in-alistp (term alist)
   (declare (xargs :guard (and (pseudo-termp term)
                               (alistp alist))))
   (if (atom term)
       ;; term is a var, so check that it is bound in the alist:
       (assoc-eq term alist)
     (if (eq 'quote (ffn-symb term))
         t
       (all-vars-in-terms-bound-in-alistp (fargs term) alist))))

 (defund all-vars-in-terms-bound-in-alistp (terms alist)
   (declare (xargs :guard (and (pseudo-term-listp terms)
                               (alistp alist))))
   (if (endp terms)
       t
     (and (all-vars-in-term-bound-in-alistp (first terms) alist)
          (all-vars-in-terms-bound-in-alistp (rest terms) alist)))))

(make-flag all-vars-in-term-bound-in-alistp)

;; Proves that all-vars-in-term-bound-in-alistp works as expected.
(defthm-flag-all-vars-in-term-bound-in-alistp
  (defthm all-vars-in-term-bound-in-alistp-correct
    (implies (and (pseudo-termp term)
                  (alistp alist))
             (iff (all-vars-in-term-bound-in-alistp term alist)
                  (subsetp-equal (vars-in-term term) (strip-cars alist))))
    :flag all-vars-in-term-bound-in-alistp)
  (defthm all-vars-in-terms-bound-in-alistp-correct
    (implies (and (pseudo-term-listp terms)
                  (alistp alist))
             (iff (all-vars-in-terms-bound-in-alistp terms alist)
                  (subsetp-equal (vars-in-terms terms) (strip-cars alist))))
    :flag all-vars-in-terms-bound-in-alistp)
  :hints (("Goal" :in-theory (enable all-vars-in-term-bound-in-alistp
                                     all-vars-in-terms-bound-in-alistp
                                     vars-in-term
                                     vars-in-terms))))
