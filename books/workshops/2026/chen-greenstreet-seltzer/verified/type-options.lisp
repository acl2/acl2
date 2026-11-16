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

; BOZO-mrg: I'm including expand-options for the find-recognizers function.
;   find-recognizers should be in hint-interface, but I don't want to change
;   the hint-interface book without double-checking with Yan.
(include-book "expand-options")

(defalist type-to-types-alist
  :key-type symbolp
  :val-type smt-sub/supertype-list-p
  :true-listp t)

(defthm assoc-equal-of-type-to-types-alist
  (implies (and (type-to-types-alist-p alst)
                (assoc-equal x alst))
           (and (consp (assoc-equal x alst))
                (smt-sub/supertype-list-p (cdr (assoc-equal x alst))))))

(defprod type-options
  ((supertype type-to-types-alist-p)
   (subtype type-to-types-alist-p)
   (functions symbol-thm-spec-list-alist-p)
   (type-recognizers fn-sym-list-p)
   (names symbol-listp)))

(define construct-sub/supertype-alist ((types smt-acl2type-list-p))
  :returns (mv (subtype type-to-types-alist-p)
               (supertype type-to-types-alist-p))
  :measure (len types)
  (b* ((types (smt-acl2type-list-fix types))
       ((unless (consp types)) (mv nil nil))
       ((cons types-hd types-tl) types)
       ((mv subtype-tl supertype-tl)
        (construct-sub/supertype-alist types-tl))
       ((smt-acl2type tp) types-hd))
    (mv (acons tp.recognizer tp.subtypes subtype-tl)
        (acons tp.recognizer tp.supertypes supertype-tl))))

(define construct-function-alist ((funcs smt-function-list-p)
                                  (acc symbol-thm-spec-list-alist-p))
  :returns (func-alst symbol-thm-spec-list-alist-p)
  :measure (len funcs)
  (b* ((funcs (smt-function-list-fix funcs))
       (acc (symbol-thm-spec-list-alist-fix acc))
       ((unless (consp funcs)) acc)
       ((cons f-hd f-tl) funcs)
       ((smt-function f) f-hd)
       ((if (assoc-equal f.name acc))
        (construct-function-alist f-tl acc)))
    (construct-function-alist f-tl (acons f.name f.returns acc))))

(define construct-type-options ((smtlink-hint smtlink-hint-p)
                                (term pseudo-termp))
  :returns (type-options type-options-p)
  (b* ((smtlink-hint (smtlink-hint-fix smtlink-hint))
       (term (pseudo-term-fix term))
       ((smtlink-hint h) smtlink-hint)
       ((mv subtype supertype) (construct-sub/supertype-alist h.acl2types))
       (functions (construct-function-alist h.functions nil))
       (type-recognizers (find-recognizers h))
       (names (acl2::simple-term-vars term)))
    (make-type-options :supertype supertype
                       :subtype subtype
                       :functions functions
                       :type-recognizers type-recognizers
                       :names names)))
