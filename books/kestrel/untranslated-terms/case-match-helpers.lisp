; Helper functions for manipulating calls of case-match
;
; Copyright (C) 2021-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; TODO: Consider using this as a guard on the functions below:
(defund legal-case-match-casesp (cases)
  (declare (xargs :guard t))
  (if (atom cases)
      (null cases)
    (let ((case (first cases)))
      (and (true-listp case)
           (or (= 2 (len case))
               (= 3 (len case)))
           ;; todo: add a check on the declare
           ;; todo: can there be more than one declare?
           ;; todo: can we do any checks on the pattern or body
           ;; A case with just & must be last:
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

;eventually drop?
(defthm legal-case-match-casesp-forward-to-true-list-listp
  (implies (legal-case-match-casesp cases)
           (true-list-listp cases))
  :hints (("Goal" :in-theory (enable legal-case-match-casesp))))

;; Extract the bodies of the items.  These are the untranslated terms that need to be handled.
;; TODO: What about a decl of (type (satisfies foo)) where perhaps FOO is a function to replace?
(defun extract-terms-from-case-match-cases (cases ;each is either (<pat> <body>) or (<pat> <dcl> <body>).
                                            )
  (declare (xargs :guard (true-list-listp cases)))
  (if (endp cases)
      nil
    (let ((case (first cases)))
      (if (= 2 (len case))
          ;; case is (<pat> <body>):
          (cons (second case) (extract-terms-from-case-match-cases (rest cases)))
        ;; case is (<pat> <dcl> <body>):
        (cons (third case) (extract-terms-from-case-match-cases (rest cases)))))))

(defthm <=-of-acl2-count-of-extract-terms-from-case-match-cases-linear
  (<= (acl2-count (extract-terms-from-case-match-cases cases))
      (acl2-count cases))
  :rule-classes :linear)

;; Whenever there is a term in the cases, use the corresponding term from new-terms-from-cases.
(defun recreate-case-match-cases (cases new-terms-from-cases)
  (declare (xargs :guard (and (true-list-listp cases)
                              (true-listp new-terms-from-cases))))
  (if (endp cases)
      nil
    (let ((case (first cases)))
      (if (= 2 (len case))
          ;; case is (<pat> <body>):
          (cons (list (first case) (first new-terms-from-cases))
                (recreate-case-match-cases (rest cases) (rest new-terms-from-cases)))
        ;; case is (<pat> <dcl> <body>):
        (cons (list (first case) (second case) (first new-terms-from-cases))
              (recreate-case-match-cases (rest cases) (rest new-terms-from-cases)))))))

(defthm legal-case-match-casesp-of-recreate-case-match-cases
  (implies (legal-case-match-casesp cases)
           (legal-case-match-casesp (recreate-case-match-cases cases new-terms-from-cases)))
  :hints (("Goal" :in-theory (enable legal-case-match-casesp))))
