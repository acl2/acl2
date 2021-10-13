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
(include-book "ordinals/lexicographic-ordering-without-arithmetic" :dir :system)

(include-book "../../verified/hint-interface")
(include-book "pretty-printer")
(include-book "translate-declarations")

;; (defsection SMT-translate
;;   :parents (z3-py)
;;   :short "SMT-translate translates from ACL2 to SMT."

(local (in-theory (e/d (paragraph-p word-p)
                       (symbol-listp
                        pseudo-term-listp-of-symbol-listp))))

(define translate-function-name ((fn symbolp))
  :returns (translated paragraph-p)
  (b* ((fn (symbol-fix fn))
       (item (assoc-equal fn *SMT-functions*))
       ((unless item)
        (prog2$ (er hard? 'translate=>translate-function-name
                    "Not a basic function, not supported. ~q0" fn)
                "")))
    (cadr item)))

(define map-translated-actuals ((actuals paragraph-p))
  :returns (mapped paragraph-p)
  :measure (acl2-count (paragraph-fix actuals))
  (b* ((actuals (paragraph-fix actuals))
       ((unless (consp actuals)) actuals)
       ((unless (consp (cdr actuals))) actuals)
       ((cons first rest) actuals)
       (mapped-rest (map-translated-actuals rest)))
    (cons first (cons #\, mapped-rest))))

(defines translate-term
  :well-founded-relation l<
  :flag-local nil
  :verify-guards nil
  :hints (("Goal" :in-theory (e/d (pseudo-term-fix
                                   pseudo-term-list-fix)
                                  ())))

  (define translate-term ((term pseudo-termp)
                          (hint smtlink-hint-p)
                          (sym-keeper symbol-keeper-p))
    :returns (mv (translated paragraph-p)
                 (new-sym-keeper symbol-keeper-p))
    :measure (acl2-count (pseudo-term-fix term))
    (b* ((term (pseudo-term-fix term))
         ((smtlink-hint h) (smtlink-hint-fix hint))
         (sym-keeper (symbol-keeper-fix sym-keeper))
         ((if (acl2::variablep term))
          (mv (translate-variable term) sym-keeper))
         ((if (acl2::quotep term))
          (translate-quote term sym-keeper))
         ((cons fn actuals) term)
         ((if (pseudo-lambdap fn))
          (mv (er hard? 'translate=>translate-term
                  "Found lambda in term ~p0~%" term)
              sym-keeper))
         (translated-fn (translate-function-name fn))
         ((mv translated-actuals actuals-keeper)
          (translate-term-list actuals hint sym-keeper)))
      (mv `(,translated-fn
            #\(
            ,(map-translated-actuals translated-actuals)
            #\))
          actuals-keeper)))

  (define translate-term-list ((term-lst pseudo-term-listp)
                               (hint smtlink-hint-p)
                               (sym-keeper symbol-keeper-p))
    :returns (mv (translated paragraph-p)
                 (new-sym-keeper symbol-keeper-p))
    :measure (acl2-count (pseudo-term-list-fix term-lst))
    (b* ((term-lst (pseudo-term-list-fix term-lst))
         ((smtlink-hint h) (smtlink-hint-fix hint))
         (sym-keeper (symbol-keeper-fix sym-keeper))
         ((unless (consp term-lst)) (mv nil sym-keeper))
         ((cons term-hd term-tl) term-lst)
         ((mv trans-hd keeper-hd)
          (translate-term term-hd hint sym-keeper))
         ((mv trans-tl keeper-tl)
          (translate-term-list term-tl hint keeper-hd)))
      (mv (cons trans-hd trans-tl) keeper-tl)))
  )

(verify-guards translate-term)

#|
(translate-term
 '(not (< (binary-+ (binary-* x y) (binary-* x y))
          (binary-* '2 (binary-* x y))))
 (make-smtlink-hint))
|#

(define translate-theorem ((term pseudo-termp)
                           (hints smtlink-hint-p)
                           (sym-keeper symbol-keeper-p))
  :returns (mv (translated paragraph-p)
               (new-keeper symbol-keeper-p))
  (b* ((term (pseudo-term-fix term))
       ((mv new-term new-keeper) (translate-term term hints sym-keeper))
       (theorem `("theorem = " ,new-term #\Newline))
       (prove-theorem `("_SMT_.prove(theorem)" #\Newline)))
    (mv `(,theorem ,prove-theorem)
        new-keeper)))

(local (in-theory (disable consp-of-is-conjunct?
                           acl2::true-listp-of-car-when-true-list-listp
                           true-list-listp)))

(define SMT-translation ((term pseudo-termp)
                         (smtlink-hint smtlink-hint-p)
                         state)
  :returns (mv (py-term paragraph-p)
               (smt-precond pseudo-termp))
  :ignore-ok t
  (b* ((term (pseudo-term-fix term))
       (- (cw "SMT-translation: ~q0" term))
       (avoid-syms (acl2::simple-term-vars term))
       ((mv okp decl-list theorem-body)
        (case-match term
          (('if ('type-hyp decl-list &) theorem-body ''t)
           (mv t decl-list theorem-body))
          (& (mv nil nil nil))))
       ((unless okp)
        (prog2$ 
         (er hard? 'translate=>SMT-translation
             "Term is ill-formed and cannot be translated: ~q0"
             term)
         (mv nil nil)))
       ((smtlink-hint h) (smtlink-hint-fix smtlink-hint))
       (- (cw "theorem-body: ~q0" theorem-body))
       (- (cw "avoid-syms: ~q0" avoid-syms))
       ((mv translated-body sym-keeper)
        (translate-theorem theorem-body
                           h
                           (make-symbol-keeper :symbol-map nil
                                               :index 0
                                               :avoid-list avoid-syms)))
       (- (cw "decl-list: ~q0" decl-list))
       ((symbol-keeper s) sym-keeper)
       (translated-decl (translate-declarations decl-list (strip-cdrs s.symbol-map)))
       (- (cw "translated-decl: ~q0" translated-decl))
       (pretty-translated-body (pretty-print-theorem translated-body 80))
       (translation `(,translated-decl ,pretty-translated-body)))
    (mv translation nil)))

;;  )
