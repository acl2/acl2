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
                          (hint smtlink-hint-p))
    :returns (translated paragraph-p)
    :measure (acl2-count (pseudo-term-fix term))
    (b* ((term (pseudo-term-fix term))
         ((smtlink-hint h) (smtlink-hint-fix hint))
         ((if (acl2::variablep term))
          (translate-variable term))
         ((if (acl2::quotep term))
          (translate-quote term))
         ((cons fn actuals) term)
         ((if (pseudo-lambdap fn))
          (er hard? 'translate=>translate-term
              "Found lambda in term ~p0~%" term))
         (translated-fn (translate-function-name fn))
         (translated-actuals (translate-term-list actuals hint)))
      `(,translated-fn
        #\(
        ,(map-translated-actuals translated-actuals)
        #\))))

  (define translate-term-list ((term-lst pseudo-term-listp)
                               (hint smtlink-hint-p))
    :returns (translated paragraph-p)
    :measure (acl2-count (pseudo-term-list-fix term-lst))
    (b* ((term-lst (pseudo-term-list-fix term-lst))
         ((smtlink-hint h) (smtlink-hint-fix hint))
         ((unless (consp term-lst)) nil)
         ((cons term-hd term-tl) term-lst))
      (cons (translate-term term-hd hint)
            (translate-term-list term-tl hint))))
  )

(verify-guards translate-term)

#|
(translate-term
 '(not (< (binary-+ (binary-* x y) (binary-* x y))
          (binary-* '2 (binary-* x y))))
 (make-smtlink-hint))
|#

(define translate-theorem ((term pseudo-termp)
                           (hints smtlink-hint-p))
  :returns (translated paragraph-p)
  (b* ((term (pseudo-term-fix term))
       (new-term (translate-term term hints))
       (theorem `("theorem = " ,new-term #\Newline))
       (prove-theorem `("_SMT_.prove(theorem)" #\Newline)))
    `(,theorem ,prove-theorem)))

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
       (- (cw "decl-list: ~q0" decl-list))
       (translated-decl (translate-declarations decl-list))
       (- (cw "translated-decl: ~q0" translated-decl))
       (- (cw "theorem-body: ~q0" theorem-body))
       (translated-body (translate-theorem theorem-body h))
       (pretty-translated-body (pretty-print-theorem translated-body 80))
       (translation `(,translated-decl ,pretty-translated-body)))
    (mv translation nil)))

;;  )
