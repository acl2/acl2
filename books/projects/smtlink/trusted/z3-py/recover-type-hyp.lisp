;; Copyright (C) 2015, University of British Columbia
;; Written (originally) by Yan Peng (13th March, 2014)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2

(in-package "SMT")
(include-book "centaur/fty/top" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "../../verified/hint-interface")
(include-book "../../verified/basics")

(defsection SMT-recover-types
  :parents (z3-py)
  :short "Recovering types from type-hyp"

  (define is-type-decl ((type symbolp)
                        (fty-info fty-info-alist-p)
                        (abs symbol-listp))
    :returns (ok booleanp)
    (b* ((type (symbol-fix type))
         (fty-info (fty-info-alist-fix fty-info)))
      (if (or ;; basic types
           (member-equal type (strip-cars *SMT-types*))
           ;; abstract types
           (member-equal type abs)
           ;; fty types
           (typedecl-of-flextype type fty-info))
          t nil)))

  (define recover-type-decl-list ((hyp-lst t)
                                  (fty-info fty-info-alist-p)
                                  (abs symbol-listp))
    :returns (type-decl-list decl-listp)
    (b* ((fty-info (fty-info-alist-fix fty-info))
         ((unless (consp hyp-lst)) nil)
         ((cons first rest) hyp-lst)
         ((unless (and (equal (len first) 2)
                       (symbolp (car first))
                       (and (symbolp (cadr first)) (cadr first))))
          (er hard? 'recover-type-hype=>recover-type-decl-list "ill-formed ~
                          type term: ~q0" first))
         (type (car first))
         (var (cadr first))
         ((unless (is-type-decl type fty-info abs))
          (er hard? 'recover-type-hyp=>recover-type-decl-list "not a type: ~q0"
              type)))
      (cons (make-decl :name var :type (make-hint-pair :thm type :hints nil))
            (recover-type-decl-list rest fty-info abs))))

  (define recover-type-hyp ((decl-list pseudo-term-listp)
                            (fn-alst func-alistp)
                            (fty-info fty-info-p)
                            (abs symbol-listp)
                            (fn-decl-acc func-alistp)
                            state)
    ;; :returns (mv (fn-decl-list func-alistp)
    ;;              (type-decl-list decl-listp))
    :mode :program ;; because of untranslate
    (b* ((decl-list (pseudo-term-list-fix decl-list))
         ((unless (consp decl-list)) (mv fn-decl-acc nil))
         ((cons first rest) decl-list))
      (case-match first
        (('type-hyp ('hide hyp-lst) tag)
         (cond ((equal tag '':type)
                (b* ((untranslated-hyp-lst
                      (untranslate hyp-lst nil (w state)))
                     ((unless (and (consp untranslated-hyp-lst)
                                   (equal (car untranslated-hyp-lst) 'list)))
                      (prog2$
                       (er hard? 'recover-type-hyp=>recover-type-hyp "untranslate ~
                          hyp-lst returns something unrecognizable: ~q0"
                           untranslated-hyp-lst)
                       (mv fn-decl-acc nil)))
                     (hyp-lst (cdr untranslated-hyp-lst))
                     (first-type-decl (recover-type-decl-list hyp-lst fty-info abs))
                     ((mv rest-fn-decl rest-type-decl)
                      (recover-type-hyp rest fn-alst fty-info abs
                                        fn-decl-acc state)))
                  (mv rest-fn-decl
                      (append first-type-decl rest-type-decl))))
               ((equal tag '':return)
                (case-match hyp-lst
                  (('cons return-type-term ''nil)
                   (b* (((unless (and (equal (len return-type-term) 2)
                                      (symbolp (car return-type-term))
                                      (consp (cadr return-type-term))
                                      (symbolp (caadr return-type-term))))
                         (prog2$
                          (er hard? 'recover-type-hyp=>recover-type-hyp
                              "ill-formed return-type-alist term: ~q0"
                              return-type-term)
                          (mv fn-decl-acc nil)))
                        (return-type (car return-type-term))
                        ((unless (is-type-decl return-type fty-info abs))
                         (prog2$
                          (er hard? 'recover-type-hyp=>recover-type-hyp "not a ~
                          type: ~q0" return-type)
                          (mv fn-decl-acc nil)))
                        (fn-name (caadr return-type-term))
                        ((if (assoc-equal fn-name fn-decl-acc))
                         (recover-type-hyp rest fn-alst fty-info abs
                                           fn-decl-acc state))
                        (fn-in-hint (cdr (assoc-equal fn-name fn-alst)))
                        ((unless fn-in-hint)
                         (prog2$
                          (er hard? 'recover-type-hype=>recover-type-hyp "function ~
                          not found in smtlink-hint: ~q0" fn-name)
                          (mv fn-decl-acc nil)))
                        (return-name (decl->name (car (func->returns fn-in-hint))))
                        (the-fn (make-func
                                 :name fn-name
                                 :formals (func->formals fn-in-hint)
                                 :returns (list (make-decl
                                                 :name return-name
                                                 :type (make-hint-pair
                                                        :thm return-type
                                                        :hints nil)))))
                        ((mv rest-fn-decl rest-type-decl)
                         (recover-type-hyp rest fn-alst fty-info abs
                                           (acons fn-name the-fn fn-decl-acc) state)))
                     (mv rest-fn-decl rest-type-decl)))
                  (& (prog2$ (er hard? 'recover-type-hyp=>recover-type-hyp
                                 ":return type predicate ill-formed: ~q0"
                                 hyp-lst)
                             (mv fn-decl-acc nil)))))
               (t (prog2$ (er hard? 'recover-type-hyp=>recover-type-hyp "tag ~
                          isn't recognized: ~q0" tag)
                          (mv fn-decl-acc nil)))))
        (& (prog2$ (er hard? 'recover-type-hyp=>recover-type-hyp
                       "recover-type-hyp found a malformed type-hyp: ~q0"
                       first)
                   (mv fn-decl-acc nil))))))
  )
