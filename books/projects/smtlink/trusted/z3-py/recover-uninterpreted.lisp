;; Copyright (C) 2015, University of British Columbia
;; Written (originally) by Yan Peng (17th April, 2019)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2

(in-package "SMT")
(include-book "centaur/fty/top" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "ordinals/lexicographic-ordering-without-arithmetic" :dir :system)
(include-book "../../verified/hint-interface")

;; (defsection SMT-recover-uninterpreted
;;   :parents (z3-py)
;;   :short "Recovering return types of uninterpreted functions"

  (defprod fix-guard
    ((fixer symbolp)
     (guard symbolp)))

  (defalist fn-fix-alist
    :key-type symbolp
    :val-type fix-guard-p
    :true-listp t)

  (local
   (defthm consp-of-assoc-equal-of-fn-fix-alist
     (implies (and (fn-fix-alist-p x)
                   (symbolp y)
                   (assoc-equal y x))
              (and (consp (assoc-equal y x))
                   (fix-guard-p (cdr (assoc-equal y x))))))
   )

  ;; There is an ambiguity when it's possible to find that the fix-guard is
  ;; real/rationalp but the return typep is realp
  (define ambiguous-equal ((fix-guard symbolp)
                           (typep symbolp))
    :returns (ok booleanp)
    (b* (((if (equal fix-guard typep)) t)
         ((if (and (equal fix-guard 'real/rationalp)
                   (equal typep 'realp)))
          t))
      nil))

  (defines recover-uninterpreted
    :well-founded-relation l<
    :flag-local nil
    :flag-defthm-macro defthm-recover-uninterpreted
    :verify-guards nil

    (define recover-uninterpreted-list ((term-lst pseudo-term-listp)
                                        (fn-lst smt-function-list-p)
                                        (fixtypes smt-fixtype-list-p)
                                        (fixinfo smt-fixtype-info-p)
                                        (fn-acc smt-function-list-p)
                                        (fix-alst fn-fix-alist-p))
      :returns (mv (new-term-lst pseudo-term-listp)
                   (new-fn-acc smt-function-list-p)
                   (new-fix-alst fn-fix-alist-p))
      :measure (acl2-count (pseudo-term-list-fix term-lst))
      :hints (("Goal" :in-theory (enable pseudo-term-list-fix
                                         pseudo-term-fix)))
      (b* ((term-lst (pseudo-term-list-fix term-lst))
           (fn-acc (smt-function-list-fix fn-acc))
           (fix-alst (fn-fix-alist-fix fix-alst))
           ((unless (consp term-lst)) (mv term-lst fn-acc fix-alst))
           ((cons first rest) term-lst)
           ((mv first-term first-fn-acc first-fix-alst)
            (recover-uninterpreted first fn-lst fixtypes fixinfo fn-acc fix-alst))
           ((mv rest-term-lst rest-fn-acc rest-fix-alst)
            (recover-uninterpreted-list rest fn-lst fixtypes fixinfo
                                        first-fn-acc first-fix-alst)))
        (mv (cons first-term rest-term-lst)
            rest-fn-acc
            rest-fix-alst)))

    (define recover-uninterpreted ((term pseudo-termp)
                                   (fn-lst smt-function-list-p)
                                   (fixtypes smt-fixtype-list-p)
                                   (fixinfo smt-fixtype-info-p)
                                   (fn-acc smt-function-list-p)
                                   (fix-alst fn-fix-alist-p))
      :returns (mv (new-term pseudo-termp)
                   (new-fn-acc smt-function-list-p)
                   (new-fix-alst fn-fix-alist-p))
      :measure (acl2-count (pseudo-term-fix term))
      (b* ((term (pseudo-term-fix term))
           (fn-lst (smt-function-list-fix fn-lst))
           (fn-acc (smt-function-list-fix fn-acc))
           (fix-alst (fn-fix-alist-fix fix-alst))
           ;; If first term is a symbolp or is quoted, return the current facts
           ((if (or (acl2::variablep term) (acl2::fquotep term)))
            (mv term fn-acc fix-alst))
           ;; The first term is now a function call:
           ;; Cons the function call and function actuals out of term
           ((cons fn-call fn-actuals) term)
           ;; If fn-call is a pseudo-lambdap, transform the body
           ((if (pseudo-lambdap fn-call))
            (prog2$ (er hard? 'recover-uninterpreted=>recover-uninterpreted
                        "There still exists lambda in the term. Very
                                 strange.~%~q0~%" term)
                    (mv nil nil nil)))
           ;; If fn-call is neither a lambda expression nor a function call
           ((unless (mbt (symbolp fn-call))) (mv nil nil nil))

           ;; -----------------------------------------------------------
           ;; Now the term is a function call
           ;; If it is a fixing function, first check fix-alst to see if (caar
           ;; fn-actuals) exists and if it's fixer is the same fixer.
           ;; we find out what its type recognizer is and compare it with the
           ;; fn-lst table. If they don't match, complain; otherwise build an
           ;; item for new-fn-acc and an item for new-fix-alst
           ;; If the function is not a fixing function, continue with the
           ;; arguments.
           (guard (recognizer-of-fixer fn-call fixtypes))
           ((unless guard)
            (b* (((mv rest-term-lst rest-fn-acc rest-fix-alst)
                  (recover-uninterpreted-list fn-actuals fn-lst fixtypes
                                              fixinfo fn-acc fix-alst)))
              (mv (cons fn-call rest-term-lst)
                  rest-fn-acc
                  rest-fix-alst)))
           ((unless (and (consp fn-actuals)
                         (null (cdr fn-actuals))
                         (consp (car fn-actuals))
                         (symbolp (caar fn-actuals))
                         (is-function (caar fn-actuals) fn-lst)))
            (b* (((mv rest-term-lst rest-fn-acc rest-fix-alst)
                  (recover-uninterpreted-list fn-actuals fn-lst fixtypes
                                              fixinfo fn-acc fix-alst)))
              (mv (cons fn-call rest-term-lst)
                  rest-fn-acc
                  rest-fix-alst)))
           (exist? (assoc-equal (caar fn-actuals) fix-alst))
           ((if (and exist? (not (equal (fix-guard->fixer (cdr exist?)) fn-call))))
            (prog2$ (er hard? 'recover-uninterpreted=>recover-uninterpreted
                        "Function ~p0 are fixed with fixer ~p1 and fixer ~p2~%"
                        (caar fn-actuals) (fix-guard->fixer (cdr exist?)) fn-call)
                    (mv nil nil nil)))
           ((if exist?)
            (recover-uninterpreted (car fn-actuals) fn-lst fixtypes fixinfo fn-acc
                                   fix-alst))
           (func (is-function (caar fn-actuals) fn-lst))
           (typep (return-type-of-function func fixinfo))
           ((unless (ambiguous-equal guard typep))
            (prog2$ (er hard? 'recover-uninterpreted=>recover-uninterpreted
                        "Guard for fixing function ~p0 is ~p1, but user defined
function ~p2 returns ~p3~%" fn-call guard (caar fn-actuals) typep)
                    (mv nil nil nil)))
           (new-fn-acc (cons func fn-acc))
           (new-fix-alst (acons (caar fn-actuals)
                                (make-fix-guard :fixer fn-call
                                                :guard guard)
                                fix-alst))
           ((mv rest-term rest-fn-acc rest-fix-alst)
            (recover-uninterpreted (car fn-actuals) fn-lst fixtypes fixinfo
                                   new-fn-acc new-fix-alst)))
        (mv rest-term rest-fn-acc rest-fix-alst)))
    )

  (verify-guards recover-uninterpreted
    :hints (("Goal"
             :in-theory (enable pseudo-term-listp-of-cdr-pseudo-termp
                                pseudo-termp-of-car-of-pseudo-term-listp))))

  (define construct-uninterpreted-precond ((fix-alst fn-fix-alist-p)
                                           (acc symbol-listp)
                                           state)
    ;; :returns (uninterpreted-precond pseudo-term-list-listp)
    :measure (len (fn-fix-alist-fix fix-alst))
    :mode :program
    (b* ((fix-alst (fn-fix-alist-fix fix-alst))
         ((unless (consp fix-alst)) nil)
         ((cons (cons & fix-guard) rest) fix-alst)
         ((fix-guard fg) fix-guard)
         ((if (member-equal fg.fixer acc))
          (construct-uninterpreted-precond rest acc state))
         (thm `(,fg.guard (,fg.fixer x)))
         ((mv err translated-thm)
          (acl2::translate-cmp thm t t nil
                               'recover-uninterpreted=>construct-uninterpreted-precond
                               (w state) (acl2::default-state-vars t)))
         ((when err)
          (er hard? 'recover-uninterpreted=>construct-uninterpreted-precond "Error ~
    translating form: ~@0" thm)))
      (cons (list translated-thm)
            (construct-uninterpreted-precond rest (cons fg.fixer acc) state))))

(define recover-uninterpreted-top ((term pseudo-termp)
                                   (smtlink-hint smtlink-hint-p)
                                   state)
    ;; :returns (mv (new-term pseudo-termp)
    ;;              (new-fn-lst smt-function-list-p)
    ;;              (uninterpreted-precond pseudo-term-list-listp))
    :mode :program
    (b* ((smtlink-hint (smtlink-hint-fix smtlink-hint))
         ((smtlink-hint h) smtlink-hint)
         ((mv new-term new-fn-lst new-fix-alst)
          (recover-uninterpreted term h.functions h.types h.types-info nil nil))
         (uninterpreted-precond
          (construct-uninterpreted-precond new-fix-alst nil state)))
      (mv new-term new-fn-lst uninterpreted-precond)))

;;  )
