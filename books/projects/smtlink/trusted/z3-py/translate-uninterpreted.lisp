;; Copyright (C) 2015, University of British Columbia
;; Written (originally) by Yan Peng (19th October, 2021)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2

(in-package "SMT")
(include-book "centaur/fty/top" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/strings/top" :dir :system)

(include-book "../../verified/hint-interface")
(include-book "../property/construct-uninterpreted")
(include-book "translate-declarations")
(include-book "datatypes")

(local (in-theory (enable paragraph-p word-p)))

(define generate-uninterpreted-property ((name symbolp)
                                         (hints uninterpreted-p))
  :returns (property pseudo-termp)
  (b* ((name (symbol-fix name))
       (hints (uninterpreted-fix hints))
       ((uninterpreted h) hints))
    (construct-uninterpreted name h.formals h.formal-types h.return-type)))

(define translate-uninterpreted-arguments ((types symbol-listp))
  :returns (translated paragraph-p)
  :measure (len types)
  (b* ((types (symbol-list-fix types))
       ((unless (consp types)) nil)
       ((cons first rest) types)
       (translated-type (translate-type first)))
    (cons `(#\, #\Space ,translated-type)
          (translate-uninterpreted-arguments rest))))

(define translate-one-uninterpreted ((name symbolp)
                                     (hints uninterpreted-p))
  :returns (translated paragraph-p)
  (b* ((name (symbol-fix name))
       (hints (uninterpreted-fix hints))
       ((uninterpreted h) hints)
       (translated-formals
        (translate-uninterpreted-arguments h.formal-types))
       (translated-returns
        (translate-uninterpreted-arguments (list h.return-type))))
    `(,(translate-variable name) "= z3.Function("
      #\' ,name #\' ,translated-formals ,translated-returns
      ")" #\Newline)))

(define translate-uninterpreted ((uninterpreted symbol-uninterpreted-alist-p))
  :returns (mv (py-term paragraph-p)
               (smt-property pseudo-term-listp))
  :measure (len (symbol-uninterpreted-alist-fix uninterpreted))
  (b* ((uninterpreted (symbol-uninterpreted-alist-fix uninterpreted))
       ((unless (consp uninterpreted)) (mv nil nil))
       ((cons first rest) uninterpreted)
       ((cons name hints) first)
       (first-decl (translate-one-uninterpreted name hints))
       (first-property (generate-uninterpreted-property name hints))
       ((mv rest-decl rest-property) (translate-uninterpreted rest)))
    (mv (cons first-decl rest-decl)
        (cons first-property rest-property))))
