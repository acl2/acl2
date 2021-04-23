;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (December 30th 2019)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

(in-package "SMT")
(include-book "xdoc/top" :dir :system)
(include-book "centaur/fty/top" :dir :system)
(include-book "clause-processors/term-vars" :dir :system)

(include-book "hint-interface")

(defalist type-to-types-alist
  :key-type symbolp
  :val-type smt-sub/supertype-list-p
  :true-listp t)

(defthm assoc-equal-of-type-to-types-alist
  (implies (and (type-to-types-alist-p alst)
                (assoc-equal x alst))
           (and (consp (assoc-equal x alst))
                (smt-sub/supertype-list-p (cdr (assoc-equal x alst))))))

(defprod return-spec
  ((formals symbol-listp)
   (thm symbolp)))

(deflist return-spec-list
  :elt-type return-spec-p
  :true-listp t)

(defalist symbol-return-spec-list-alist
  :key-type symbolp
  :val-type return-spec-list-p
  :true-listp t)

(defthm assoc-equal-of-symbol-return-spec-list-alist
  (implies (and (symbol-return-spec-list-alist-p alst)
                (assoc-equal x alst))
           (and (consp (assoc-equal x alst))
                (return-spec-list-p (cdr (assoc-equal x alst))))))

(defprod type-options
  ((supertype type-to-types-alist-p)
   (subtype type-to-types-alist-p)
   (functions symbol-return-spec-list-alist-p)
   (names symbol-listp)))

(define is-type? ((type symbolp)
                  (supertype-alst type-to-types-alist-p))
  :returns (ok booleanp)
  (b* ((supertype-alst (type-to-types-alist-fix supertype-alst))
       (type (symbol-fix type)))
    (not (null (assoc-equal type supertype-alst)))))

(define construct-sub/supertype-alist ((types smt-type-list-p))
  :returns (mv (subtype type-to-types-alist-p)
               (supertype type-to-types-alist-p))
  :measure (len types)
  (b* ((types (smt-type-list-fix types))
       ((unless (consp types)) (mv nil nil))
       ((cons types-hd types-tl) types)
       ((smt-type tp) types-hd)
       ((mv subtype-tl supertype-tl)
        (construct-sub/supertype-alist types-tl)))
    (mv (acons tp.recognizer tp.subtypes subtype-tl)
        (acons tp.recognizer tp.supertypes supertype-tl))))

(define construct-return-spec ((formals symbol-listp)
                               (return-lst symbol-listp))
  :returns (return-spec-lst return-spec-list-p)
  :measure (len return-lst)
  (b* ((formals (symbol-list-fix formals))
       (return-lst (symbol-list-fix return-lst))
       ((unless (consp return-lst)) nil)
       ((cons return-hd return-tl) return-lst))
    (cons (make-return-spec :formals formals :thm return-hd)
          (construct-return-spec formals return-tl))))

(define construct-function-alist ((funcs smt-function-list-p))
  :returns (func-alst symbol-return-spec-list-alist-p)
  :measure (len funcs)
  (b* ((funcs (smt-function-list-fix funcs))
       ((unless (consp funcs)) nil)
       ((cons f-hd f-tl) funcs)
       ((smt-function f) f-hd))
    (acons f.name (construct-return-spec f.formals f.returns)
           (construct-function-alist f-tl))))

(define construct-type-options ((smtlink-hint smtlink-hint-p)
                                (term pseudo-termp))
  :returns (type-options type-options-p)
  (b* ((smtlink-hint (smtlink-hint-fix smtlink-hint))
       (term (pseudo-term-fix term))
       ((smtlink-hint h) smtlink-hint)
       ((mv subtype supertype) (construct-sub/supertype-alist h.types))
       (functions (construct-function-alist h.functions))
       (names (acl2::simple-term-vars term)))
    (make-type-options :supertype supertype
                       :subtype subtype
                       :functions functions
                       :names names)))
