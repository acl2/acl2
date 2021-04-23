;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (April 19th 2021)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

(in-package "SMT")
(include-book "xdoc/top" :dir :system)
(include-book "centaur/fty/top" :dir :system)

(include-book "hint-interface")

(defalist symbol-smt-function-alist
  :key-type symbolp
  :val-type smt-function-p
  :pred symbol-smt-function-alistp
  :true-listp t)

(defthm assoc-equal-of-symbol-smt-function-alist
  (implies (and (symbol-smt-function-alistp alst)
                (assoc-equal x alst))
           (and (consp (assoc-equal x alst))
                (smt-function-p (cdr (assoc-equal x alst))))))

(defprod expand-options
  ((functions symbol-smt-function-alistp)
   (types symbol-symbol-alistp)
   (wrld-fn-len natp)))

(define construct-function-info ((func-lst smt-function-list-p))
  :returns (alst symbol-smt-function-alistp)
  :measure (len func-lst)
  (b* ((func-lst (smt-function-list-fix func-lst))
       ((unless (consp func-lst)) nil)
       ((cons func-hd func-tl) func-lst)
       (name (smt-function->name func-hd)))
    (acons name func-hd (construct-function-info func-tl))))

(define construct-type-related-functions-helper ((func-lst smt-function-list-p)
                                                 (acc symbol-symbol-alistp))
  :returns (alst symbol-symbol-alistp)
  :measure (len func-lst)
  (b* ((func-lst (smt-function-list-fix func-lst))
       (acc (symbol-symbol-alist-fix acc))
       ((unless (consp func-lst)) nil)
       ((cons func-hd func-tl) func-lst)
       (name (smt-function->name func-hd)))
    (construct-type-related-functions-helper func-tl (acons name nil acc))))

(define construct-type-related-functions ((types smt-type-list-p)
                                          (acc symbol-symbol-alistp))
  :returns (types symbol-symbol-alistp)
  :measure (len types)
  (b* ((types (smt-type-list-fix types))
       (acc (symbol-symbol-alist-fix acc))
       ((unless (consp types)) nil)
       ((cons types-hd types-tl) types)
       (acc-1 (acons (smt-type->recognizer types-hd) nil
                     (construct-type-related-functions-helper
                      (smt-type->functions types-hd) acc))))
    (construct-type-related-functions types-tl acc-1)))

(define construct-expand-options ((hints smtlink-hint-p))
  :returns (eo expand-options-p)
  (b* ((hints (smtlink-hint-fix hints))
       ((smtlink-hint h) hints)
       (functions (construct-function-info h.functions))
       (types (construct-type-related-functions h.types nil)))
    (make-expand-options :functions functions
                         :types types
                         :wrld-fn-len h.wrld-fn-len)))
