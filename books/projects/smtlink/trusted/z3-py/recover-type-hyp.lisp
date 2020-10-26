;; Copyright (C) 2015, University of British Columbia
;; Written (originally) by Yan Peng (13th March, 2014)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2

(in-package "SMT")
(include-book "centaur/fty/top" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "../../verified/extractor")

(defsection SMT-recover-types
  :parents (z3-py)
  :short "Recovering types from type-hyp"

  (define recover-type-decl-list ((hyp-lst pseudo-term-listp)
                                  (fixinfo smt-fixtype-info-p)
                                  (abs symbol-listp))
    :returns (type-decl-list decl-list-p)
    (b* ((fixinfo (smt-fixtype-info-fix fixinfo))
         (hyp-lst (pseudo-term-list-fix hyp-lst))
         ((unless (consp hyp-lst)) nil)
         ((cons first rest) hyp-lst)
         ((unless (type-decl-p first fixinfo abs))
          (er hard? 'recover-type-hype=>recover-type-decl-list "ill-formed ~
                          type term: ~q0" first))
         (var (cadr first)))
      (cons (make-decl :name var :type (make-hint-pair :thm first))
            (recover-type-decl-list rest fixinfo abs))))

  (define recover-type-hyp-main ((decl-list pseudo-term-listp)
                                 (fixinfo smt-fixtype-info-p)
                                 (abs symbol-listp))
    :returns (type-decl-list decl-list-p)
    (b* ((decl-list (pseudo-term-list-fix decl-list))
         ((unless (consp decl-list)) nil)
         ((cons first rest) decl-list))
      (case-match first
        (('type-hyp ('hide hyp-lst) tag)
         (cond ((equal tag '':type)
                (b* (((unless (and (consp hyp-lst)
                                   (equal (car hyp-lst) 'quote)
                                   (consp (cdr hyp-lst))))
                      (er hard? 'recover-type-hyp=>recover-type-hyp-main
                          "Wrong form of decl-list: ~q0" decl-list))
                     (hyp-lst (cadr hyp-lst))
                     ((unless (pseudo-term-listp hyp-lst))
                      (er hard? 'recover-type-hyp=>recover-type-hyp-main
                          "Not a pseudo-term-listp: ~q0" hyp-lst))
                     (first-type-decl (recover-type-decl-list hyp-lst fixinfo abs))
                     (rest-type-decl (recover-type-hyp-main rest fixinfo abs)))
                  (append first-type-decl rest-type-decl)))
               (t (prog2$ (er hard? 'recover-type-hyp=>recover-type-hyp-main "tag ~
                          isn't recognized: ~q0" tag)
                          nil))))
        (& (prog2$ (er hard? 'recover-type-hyp=>recover-type-hyp-main
                       "recover-type-hyp-main found a malformed type-hyp: ~q0"
                       first)
                   nil)))))

  (define recover-type-hyp ((term pseudo-termp)
                            (smtlink-hint smtlink-hint-p))
    :returns (mv (type-decl-list decl-list-p)
                 (untyped-theorem pseudo-termp))
    (b* ((term (pseudo-term-fix term))
         (smtlink-hint (smtlink-hint-fix smtlink-hint))
         ((smtlink-hint h) smtlink-hint)
         ((mv type-hyp-lst untyped-theorem)
          (smt-extract term h.types-info h.abs)))
      (mv (recover-type-hyp-main type-hyp-lst h.types-info h.abs)
          untyped-theorem)))
  )
