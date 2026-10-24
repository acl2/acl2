; Properties of the substitutions returned by one-way-unify
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; We show that the substitution computed by one-way-unify1 binds variables to
;; pseudo-terms that mention no variables in VARS, if the term mentions none
;; (and VARS does not contain NIL).  The bindings are subterms of the term, or
;; quoted constants, or NIL (for a missing argument).

(include-book "tools/flag" :dir :system)
(include-book "kestrel/terms-light/free-vars-in-term" :dir :system)
(local (include-book "helpers"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The subproblems produced when the term is a quoted constant: The terms
;; are quoted constants.
(defthm quotep-of-one-way-unify1-quotep-subproblems
  (implies (quotep term)
           (and (implies (mv-nth 1 (one-way-unify1-quotep-subproblems pat term))
                         (quotep (mv-nth 1 (one-way-unify1-quotep-subproblems pat term))))
                (implies (mv-nth 3 (one-way-unify1-quotep-subproblems pat term))
                         (quotep (mv-nth 3 (one-way-unify1-quotep-subproblems pat term))))))
  :hints (("Goal" :in-theory (enable one-way-unify1-quotep-subproblems))))

(defthm pseudo-termp-of-one-way-unify1-quotep-subproblems
  (implies (and (quotep term)
                (pseudo-termp term))
           (and (pseudo-termp (mv-nth 1 (one-way-unify1-quotep-subproblems pat term)))
                (pseudo-termp (mv-nth 3 (one-way-unify1-quotep-subproblems pat term)))))
  :hints (("Goal" :in-theory (enable one-way-unify1-quotep-subproblems))))

(local
 (defthm free-vars-in-term-when-quotep
   (implies (quotep term)
            (equal (free-vars-in-term term)
                   nil))
   :hints (("Goal" :expand ((free-vars-in-term term))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defthm not-intersectp-equal-of-free-vars-in-term-of-nil
   (implies (not (member-equal nil vars))
            (not (intersectp-equal vars (free-vars-in-term nil))))
   :hints (("Goal" :expand ((free-vars-in-term nil))))))

(local
 (defthm not-intersectp-equal-of-free-vars-in-term-of-one-way-unify1-quotep-subproblems
   (implies (and (quotep term)
                 (not (member-equal nil vars)))
            (and (not (intersectp-equal vars (free-vars-in-term (mv-nth 1 (one-way-unify1-quotep-subproblems pat term)))))
                 (not (intersectp-equal vars (free-vars-in-term (mv-nth 3 (one-way-unify1-quotep-subproblems pat term)))))))
   :hints (("Goal" :use quotep-of-one-way-unify1-quotep-subproblems
            :in-theory (disable quotep-of-one-way-unify1-quotep-subproblems)))))

(make-flag one-way-unify1)

;; The properties, for each function in the clique: The bindings are
;; pseudo-terms, and they mention no variables in VARS.
(defthm-flag-one-way-unify1
  (defthm one-way-unify1-properties
    (let ((res (mv-nth 1 (one-way-unify1 pat term alist))))
      (and (implies (and (pseudo-termp term)
                         (pseudo-term-listp (strip-cdrs alist)))
                    (pseudo-term-listp (strip-cdrs res)))
           (implies (and (not (intersectp-equal vars (free-vars-in-term term)))
                         (not (intersectp-equal vars (free-vars-in-terms (strip-cdrs alist))))
                         (not (member-equal nil vars)))
                    (not (intersectp-equal vars (free-vars-in-terms (strip-cdrs res)))))))
    :flag one-way-unify1)
  (defthm one-way-unify1-lst-properties
    (let ((res (mv-nth 1 (one-way-unify1-lst pl tl alist))))
      (and (implies (and (pseudo-term-listp tl)
                         (pseudo-term-listp (strip-cdrs alist)))
                    (pseudo-term-listp (strip-cdrs res)))
           (implies (and (not (intersectp-equal vars (free-vars-in-terms tl)))
                         (not (intersectp-equal vars (free-vars-in-terms (strip-cdrs alist))))
                         (not (member-equal nil vars)))
                    (not (intersectp-equal vars (free-vars-in-terms (strip-cdrs res)))))))
    :flag one-way-unify1-lst)
  (defthm one-way-unify1-equal1-properties
    (let ((res (mv-nth 1 (one-way-unify1-equal1 pat1 pat2 term1 term2 alist))))
      (and (implies (and (pseudo-termp term1)
                         (pseudo-termp term2)
                         (pseudo-term-listp (strip-cdrs alist)))
                    (pseudo-term-listp (strip-cdrs res)))
           (implies (and (not (intersectp-equal vars (free-vars-in-term term1)))
                         (not (intersectp-equal vars (free-vars-in-term term2)))
                         (not (intersectp-equal vars (free-vars-in-terms (strip-cdrs alist))))
                         (not (member-equal nil vars)))
                    (not (intersectp-equal vars (free-vars-in-terms (strip-cdrs res)))))))
    :flag one-way-unify1-equal1)
  (defthm one-way-unify1-equal-properties
    (let ((res (mv-nth 1 (one-way-unify1-equal pat1 pat2 term1 term2 alist))))
      (and (implies (and (pseudo-termp term1)
                         (pseudo-termp term2)
                         (pseudo-term-listp (strip-cdrs alist)))
                    (pseudo-term-listp (strip-cdrs res)))
           (implies (and (not (intersectp-equal vars (free-vars-in-term term1)))
                         (not (intersectp-equal vars (free-vars-in-term term2)))
                         (not (intersectp-equal vars (free-vars-in-terms (strip-cdrs alist))))
                         (not (member-equal nil vars)))
                    (not (intersectp-equal vars (free-vars-in-terms (strip-cdrs res)))))))
    :flag one-way-unify1-equal)
  :hints (("Goal" :in-theory (e/d (one-way-unify1 one-way-unify1-lst
                                                  one-way-unify1-equal1
                                                  one-way-unify1-equal)
                                  (one-way-unify1-quotep-subproblems))
           :expand ((free-vars-in-term term)
                    (free-vars-in-terms tl)))))
