;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (September 22th 2021)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

(in-package "SMT")
(include-book "xdoc/top" :dir :system)
(include-book "centaur/fty/top" :dir :system)

(include-book "hint-interface")
(include-book "type-options")

(defalist symbol-thm-spec-alist
  :key-type symbolp
  :val-type thm-spec-p
  :true-listp t)

(defthm assoc-equal-of-symbol-thm-spec-alist
  (implies (and (symbol-thm-spec-alist-p alst)
                (assoc-equal x alst))
           (and (consp (assoc-equal x alst))
                (thm-spec-p (cdr (assoc-equal x alst))))))

(defprod replace-options
  ((supertype type-to-types-alist-p)
   (fixers symbol-thm-spec-alist-p)))

(define construct-fixer-alist ((types smt-type-list-p))
  :returns (fixer-alst symbol-thm-spec-alist-p)
  :measure (len types)
  (b* ((types (smt-type-list-fix types))
       ((unless (consp types)) nil)
       ((cons t-hd t-tl) types)
       ((smt-type type) t-hd)
       ((smt-function f) type.fixer))
    (acons f.name (make-thm-spec :formals f.formals
                                 :thm f.replace-thm)
           (construct-fixer-alist t-tl))))

(define construct-replace-options ((hints smtlink-hint-p))
  :returns (type-alst replace-options-p)
  (b* ((hints (smtlink-hint-fix hints))
       ((smtlink-hint h) hints)
       ((mv & supertype) (construct-sub/supertype-alist h.types))
       (fixers (construct-fixer-alist h.types)))
    (make-replace-options :supertype supertype
                          :fixers fixers)))
