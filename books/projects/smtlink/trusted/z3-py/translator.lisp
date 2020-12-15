;; Copyright (C) 2015, University of British Columbia
;; Written (originally) by Yan Peng (13th March, 2014)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2

(in-package "SMT")
(include-book "centaur/fty/top" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/strings/top" :dir :system)
;; for lambda expression
(include-book "kestrel/utilities/system/terms" :dir :system)
(include-book "centaur/misc/hons-extra" :dir :system)

(include-book "../../verified/extractor")
(include-book "translate-uninterpreted")
(include-book "translate-type")
(include-book "recover-type-hyp")
(include-book "recover-uninterpreted")
(include-book "pretty-printer")

;; (defsection SMT-translator
;;   :parents (z3-py)
;;   :short "SMT-translator does the LISP to Python translation."

(local (in-theory (disable natp nfix)))

(define map-translated-actuals ((actuals paragraph-p))
  :returns (mapped paragraph-p)
  (b* ((actuals (paragraph-fix actuals))
       ((unless (consp actuals)) actuals)
       ((unless (consp (cdr actuals))) actuals)
       ((cons first rest) actuals)
       (mapped-rest (map-translated-actuals rest)))
    (cons first (cons #\, mapped-rest))))

(define translate-fixtype-fncall ((fn-call symbolp)
                                  (fixinfo smt-fixtype-info-p))
  :returns (mv (translated word-p
                           :hints (("Goal"
                                    :in-theory (enable word-p))))
               (which symbolp))
  (b* ((fn-call (symbol-fix fn-call))
       (fixinfo (smt-fixtype-info-fix fixinfo))
       (item (assoc-equal fn-call fixinfo))
       ((unless item)
        (mv (er hard? 'translator=>translate-fixtype-fncall
                "~p0 fn-call is a function call, but it's not a fixtype call, a
       uninterpreted function, or a basic function. Therefore we are stuck.~%"
                fn-call)
            nil))
       ((info-pair p) (cdr item))
       (name-val (symbol-append p.name '-val)))
    (case p.fn-type
      (:store (mv (translate-symbol 'store) :store))
      (:select (mv (translate-symbol 'select) :select))
      (:fixer (mv nil :fixer))
      (:kind-fn (mv (concatenate 'string
                                 (translate-symbol p.name) "."
                                 (translate-symbol fn-call))
                    :kind-fn))
      (:destructor
       (mv (concatenate 'string
                        (translate-symbol name-val) "."
                        (translate-symbol fn-call) "("
                        (translate-symbol p.name) ".value")
           :destructor))
      (:constructor
       (mv (concatenate 'string
                        (translate-symbol p.name) ".make("
                        (translate-symbol p.kind) ", "
                        (translate-symbol name-val) "."
                        (translate-symbol fn-call))
           :constructor))
      (t (mv (er hard? 'translator=>translate-fixtype-fncall
                 "~p0 is not one of the translatable function type. Possibly a
       recognizer that still exits in the theorem body.~%"
                 p.fn-type)
             nil)))))

(defthm stringp-implies-word-p
  (implies (stringp x) (word-p x))
  :hints (("Goal"
           :in-theory (enable word-p))))

(define translate-fncall-cases ((fn-call symbolp)
                                (fn-lst smt-function-list-p)
                                (fixinfo smt-fixtype-info-p))
  :returns (mv (translated word-p)
               (which symbolp))
  :guard-hints (("Goal"
                 :expand (is-basic-function fn-call)))
  (cond ((is-function fn-call fn-lst)
         (mv (translate-symbol fn-call) nil))
        ((not (equal (is-basic-function fn-call) ""))
         (mv (is-basic-function fn-call) nil))
        (t (translate-fixtype-fncall fn-call fixinfo))))

(defines translate
  :parents (SMT-translator)
  :short "Translation function for translating the main theorem."
  :hints (("Goal"
           :in-theory (e/d (pseudo-term-fix)
                           (natp))))
  :verify-guards nil

  (define translate-term ((term pseudo-termp)
                          (fn-lst smt-function-list-p)
                          (fixinfo smt-fixtype-info-p)
                          (sym-index natp)
                          (sym-acc symbol-string-alistp)
                          (avoid symbol-listp))
    :returns (mv (translated-term paragraph-p)
                 (index natp)
                 (syms symbol-string-alistp))
    (b* ((term (pseudo-term-fix term))
         (sym-index (nfix sym-index))
         (fn-lst (smt-function-list-fix fn-lst))
         (fixinfo (smt-fixtype-info-fix fixinfo))
         (sym-acc (symbol-string-alist-fix sym-acc))
         ;; if the term is a variable
         ((if (acl2::variablep term))
          (mv (translate-symbol term) sym-index sym-acc))
         ;; if term is a quoted constant
         ((if (acl2::fquotep term))
          (translate-constant term sym-index sym-acc avoid))
         ;; The first term is now a function call:
         ;; Cons the function call and function actuals out of term
         ((cons fn-call fn-actuals) term)
         ;; if term is a lambda term
         ((if (pseudo-lambdap fn-call))
          (mv (er hard? 'SMT-translator=>translate-term
                  "There is still a lambda in the term, weird: ~q0" term)
              0 nil))
         ;; If fn-call is neither a lambda expression nor a function call
         ((unless (mbt (symbolp fn-call))) (mv nil 0 nil))
         ;; Now fn-call must be a function call
         ;; fn-call is a fixing function, remove the function
         ((if (and (is-fixer fn-call fixinfo) (consp fn-actuals)
                   (null (cdr fn-actuals))))
          (translate-term (car fn-actuals) fn-lst fixinfo sym-index sym-acc
                          avoid))
         ;; fn-call is a fty function, an uninterpreted function or a basic function
         ((mv translated-actuals index-actuals syms-actuals)
          (translate-term-list fn-actuals fn-lst fixinfo sym-index sym-acc
                               avoid))
         ((mv translated-fn-call which)
          (translate-fncall-cases fn-call fn-lst fixinfo))
         ;; if it's a constructor with 0 arguments
         ((if (and (equal which :constructor) (null translated-actuals)))
          (mv `(,translated-fn-call ")") index-actuals syms-actuals))
         ;; if it's a fixing function
         ((if (and (null translated-fn-call) (not (atom translated-actuals))))
          (mv (car translated-actuals) index-actuals syms-actuals))
         ;; if it's a destructor function
         ((if (or (equal which :destructor) (equal which :constructor)))
          (mv `(,translated-fn-call
                #\( ,(map-translated-actuals translated-actuals) #\) ")")
              index-actuals
              syms-actuals)))
      (mv `(,translated-fn-call
            #\( ,(map-translated-actuals translated-actuals) #\) )
          index-actuals
          syms-actuals)))

  (define translate-term-list ((term-list pseudo-term-listp)
                               (fn-lst smt-function-list-p)
                               (fixinfo smt-fixtype-info-p)
                               (sym-index natp)
                               (sym-acc symbol-string-alistp)
                               (avoid symbol-listp))
    :returns (mv (translated-term paragraph-p)
                 (index natp)
                 (syms symbol-string-alistp))
    (b* ((term-list (pseudo-term-list-fix term-list))
         (sym-index (nfix sym-index))
         (sym-acc (symbol-string-alist-fix sym-acc))
         ((unless (consp term-list)) (mv nil sym-index sym-acc))
         ((cons first rest) term-list)
         ((mv translated-first index-first syms-first)
          (translate-term first fn-lst fixinfo sym-index sym-acc avoid))
         ((mv translated-rest index-rest syms-rest)
          (translate-term-list rest fn-lst fixinfo index-first
                               syms-first avoid)))
      (mv (cons translated-first translated-rest)
          index-rest
          syms-rest)))
  )

(verify-guards translate-term :guard-debug t)

(define translate-theorem ((theorem pseudo-termp)
                           (fn-decl-list smt-function-list-p)
                           (fixinfo smt-fixtype-info-p)
                           (avoid symbol-listp))
  :returns (mv (translated-term paragraph-p)
               (index natp)
               (syms-alst symbol-string-alistp))
  (b* ((theorem (pseudo-term-fix theorem))
       (fn-decl-list (smt-function-list-fix fn-decl-list))
       (fixinfo (smt-fixtype-info-fix fixinfo))
       (avoid (symbol-list-fix avoid))
       ((mv translated-theorem-body index symbols)
        (translate-term theorem fn-decl-list fixinfo 0 nil avoid))
       (theorem-assign `("theorem = " ,translated-theorem-body #\Newline))
       (prove-theorem `("_SMT_.prove(theorem)" #\Newline)))
    (mv `(,theorem-assign ,prove-theorem)
        index symbols)))

(define SMT-translation ((term pseudo-termp) (smtlink-hint smtlink-hint-p)
                         state)
    ;; :returns (mv (py-term paragraphp)
    ;;              (smt-precond pseudo-termp)
  ;;              (uninterpreted-precond pseudo-term-list-listp))
  :mode :program
    (b* ((term (pseudo-term-fix term))
         (smtlink-hint (smtlink-hint-fix smtlink-hint))
         ((smtlink-hint h) smtlink-hint)
         ;; extract type-hyp out of the theorem
         ((mv type-decl-list untyped-theorem)
          (recover-type-hyp term smtlink-hint))
         ((unless (decl-list-p type-decl-list))
          (mv (er hard? 'translator=>SMT-translation "returned values from ~
    recover-type-hyp is not of the right type!~%")
              nil))
         ;; extract uninterpreted function fn-decl-list and
         ;; uninterpreted-precond from the theorem
         ((mv unfixed-theorem fn-decl-list uninterpreted-precond)
          (recover-uninterpreted-top untyped-theorem smtlink-hint state))
         ((unless (smt-function-list-p fn-decl-list))
          (mv (er hard? 'translator=>SMT-translation "recover-uninterpreted
  didn't return the correct type of thing.~%")
              nil))
         (avoid (acl2::all-vars1 unfixed-theorem nil))
         ((unless (symbol-listp avoid))
          (mv (er hard? 'translator=>SMT-translation "returned values from ~
    acl2::all-vars1 is not of type symbol-listp!~%")
              nil))
         ;; translate the main theorem
         ((mv translated-theorem index sym-alst)
          (translate-theorem unfixed-theorem fn-decl-list h.types-info avoid))
         ;; Pretty-translated-theorem is the theorem with change lines at 160
         ;; characters. We did this because apparently super long code is
         ;; making Python slow for unknown reason.
         (pretty-translated-theorem
          (pretty-print-theorem translated-theorem 160))
         ;; translate uninterpreted function declarations
         (translated-uninterpreted-decls
          (translate-uninterpreted-decl-lst fn-decl-list h.types-info h.int-to-rat))
         ;; translate type declarations
         (translated-type-decls
          (translate-type-decl-list type-decl-list h.types-info h.int-to-rat))
         (translated-abs-types (translate-abstract-types h.types-info))
         ;; translate type definitions
         ((mv translated-fixtypes fixtype-precond new-sym-alst &)
          (translate-fixtype-list h.types h.types-info sym-alst index avoid
                                  h.int-to-rat nil nil state))
         (symbols (strip-cdrs new-sym-alst))
         (- (cw "symbols: ~q0" symbols))
         ;; translate symbols
         (translated-symbol (translate-symbol-enumeration symbols))
         (translated-theorem-all
          `(,@translated-symbol
            ,@translated-fixtypes
            ,@translated-type-decls
            ,@translated-abs-types
            ,@translated-uninterpreted-decls
            ,@pretty-translated-theorem))
         (precond-all
          `(,@fixtype-precond
            ,@uninterpreted-precond))
         )
      (mv translated-theorem-all precond-all)))
;;  )
