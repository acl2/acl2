; Helper functions for manipulating calls of case-match
;
; Copyright (C) 2015-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)
; Supporting Author: Stephen Westfold (westfold@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See tests in case-match-helpers-tests.lisp.

(local (include-book "kestrel/lists-light/last" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/utilities/acl2-count" :dir :system))
(local (include-book "kestrel/alists-light/symbol-alistp" :dir :system))

(defund legal-case-match-casesp (cases)
  (declare (xargs :guard t))
  (if (atom cases)
      (null cases)
    (let ((case (first cases)))
      (and (true-listp case)
           (<= 2 (len case)) ; a pattern, maybe some declares, then a body
           ;; todo: add a check on the declares
           ;; todo: can we do any checks on the pattern or body?
           ;; A case with a pattern of & must be last:
           (if (eq '& (first case))
               (null (rest cases))
             t)
           (legal-case-match-casesp (rest cases))))))

;; justifies calling strip-cars
(defthm legal-case-match-casesp-forward-to-alistp
  (implies (legal-case-match-casesp cases)
           (alistp cases))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable alistp legal-case-match-casesp))))

;; ;eventually drop?
;; (defthm legal-case-match-casesp-forward-to-true-list-listp
;;   (implies (legal-case-match-casesp cases)
;;            (true-list-listp cases))
;;   :hints (("Goal" :in-theory (enable legal-case-match-casesp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Extract the bodies of the CASES.  These are the untranslated terms that need to be handled.
;; TODO: What about a decl of (type (satisfies foo)) where perhaps FOO is a function to replace?
(defun extract-terms-from-case-match-cases (cases)
  (declare (xargs :guard (legal-case-match-casesp cases)
                  :guard-hints (("Goal" :in-theory (enable legal-case-match-casesp)))))
  (if (endp cases)
      nil
    (let* ((case (first cases)) ; (pat ...declares... body)
           (body (car (last case))))
      (cons body (extract-terms-from-case-match-cases (rest cases))))))

(defthm <=-of-acl2-count-of-extract-terms-from-case-match-cases-linear
  (<= (acl2-count (extract-terms-from-case-match-cases cases))
      (acl2-count cases))
  :rule-classes :linear)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Whenever there is a term in the CASES, use the corresponding term from NEW-TERMS.
;; Consumes one of the NEW-TERMS for each of the CASES.
(defun recreate-case-match-cases (cases new-terms)
  (declare (xargs :guard (and (legal-case-match-casesp cases)
                              (true-listp new-terms)
                              ;; (equal (len cases) (len new-terms)) ; uncomment?
                              )
                  :guard-hints (("Goal" :in-theory (enable legal-case-match-casesp)))))
  (if (endp cases)
      nil
    (let* ((case (first cases))
           (pattern (first case))
           (declares (butlast (rest case) 1)) ; may be empty
           ;; (body (car (last case))) ; the part being replaced
           )
      (cons `(,pattern ,@declares ,(first new-terms))
            (recreate-case-match-cases (rest cases) (rest new-terms))))))

(defthm legal-case-match-casesp-of-recreate-case-match-cases
  (implies (legal-case-match-casesp cases)
           (legal-case-match-casesp (recreate-case-match-cases cases new-terms)))
  :hints (("Goal" :in-theory (enable legal-case-match-casesp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defthm alistp-of-mv-nth-1-of-match-tests-and-bindings
   (implies (alistp bindings)
            (alistp (mv-nth 1 (match-tests-and-bindings x pat tests bindings dups))))))

(local
 (defthm symbol-alistp-of-mv-nth-1-of-match-tests-and-bindings
   (implies (symbol-alistp bindings)
            (symbol-alistp (mv-nth 1 (match-tests-and-bindings x pat tests bindings dups))))))

;; todo: nested induction.  use an alists book?
(local
 (defthm no-duplicatesp-equal-of-strip-cars-of-mv-nth-1-of-match-tests-and-bindings
   (implies (no-duplicatesp-equal (strip-cars bindings))
            (no-duplicatesp-equal (strip-cars (mv-nth 1 (match-tests-and-bindings x pat tests bindings dups)))))
   :hints (("Goal" :do-not '(generalize eliminate-destructors)))))

;; Returns a list of all the vars bound by case-match when something
;; successfully matches PAT.
(defund vars-bound-in-case-match-pattern (pat)
  (declare (xargs :guard t))
  (mv-let (tests bindings dups)
      (match-tests-and-bindings :ignore pat nil nil nil)
    (declare (ignore tests dups))
    (strip-cars bindings)))

(defthm symbol-listp-of-vars-bound-in-case-match-pattern
  (symbol-listp (vars-bound-in-case-match-pattern pat))
  :hints (("Goal" :in-theory (enable vars-bound-in-case-match-pattern))))

(defthm no-duplicatesp-equal-of-vars-bound-in-case-match-pattern
  (no-duplicatesp-equal (vars-bound-in-case-match-pattern pat))
  :hints (("Goal" :in-theory (enable vars-bound-in-case-match-pattern))))
