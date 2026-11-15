;; Copyright (C) 2026, University of British Columbia
;; Written by Chris Chen
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

;;
;; This book defines a clause processor that extracts typing
;; information from unconditional, monomorphically-typed typed terms.

(in-package "SMT")
(include-book "centaur/fty/top" :dir :system)
(include-book "std/alists/top" :dir :system)
(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/util/defines" :dir :system)
(include-book "std/util/defprojection" :dir :system)
(include-book "xdoc/top" :dir :system)

(include-book "basics")
(include-book "tterm")

(set-state-ok t)
(set-induction-depth-limit 1)
(make-event
 (pprogn (set-warnings-as-errors t '("Use") state)
         (value '(value-triple nil))))

(define symbol-string-append ((left symbolp)
                              (right stringp))
  :returns (rv symbolp)
  (b* ((left (symbol-fix left))
       (right (str-fix right))
       (left-name (symbol-name left))
       (new-sym (intern-in-package-of-symbol (string-append left-name right)
                                             left)))
    new-sym)
  ///
  (fty::deffixequiv symbol-string-append))

(define constant-list ((prefix symbolp)
                       (count natp))
  :returns (rv symbol-listp)
  (b* ((prefix (symbol-fix prefix))
       (count (nfix count))
       (new-sym (symbol-string-append prefix
                                      (str::nat-to-dec-string count))))
    (if (zp count)
        nil
      (cons new-sym
            (constant-list prefix (1- count)))))
  ///
  (fty::deffixequiv constant-list))

(defsection smt-judgement
  :parents (verified)

  (defprod var-judgement
    ((name symbolp)
     (judgement symbolp)))

  (deflist var-judgement-list
    :elt-type var-judgement
    :true-listp t)

  (defprod fn-judgement
    ((name symbolp)
     (domain symbol-listp)
     (range symbolp)))

  (deflist fn-judgement-list
    :elt-type fn-judgement
    :true-listp t)

  (defprod smt-judgement
    ((vars var-judgement-list-p :default nil)
     (fns fn-judgement-list-p :default nil)))
  )

(defsection smt-judgement->expr
  :parents (verified)

  (define var-judgement->expr ((j var-judgement-p))
    :returns (rv pseudo-termp)
    (b* ((j (var-judgement-fix j))
         (judgement (var-judgement->judgement j))
         ((if (equal judgement 'quote)) 't))
      `(,(var-judgement->judgement j) ,(var-judgement->name j)))
    ///
    (fty::deffixequiv var-judgement->expr))

  (std::defprojection var-judgement-list->expr-list ((x var-judgement-list-p))
    :returns (rv pseudo-term-listp)
    (var-judgement->expr x)
    ///
    (fty::deffixequiv var-judgement-list->expr-list))

  (define domain-judgement-helper ((n-r alistp))
    :returns (rv var-judgement-list-p)
    :measure (acl2-count (acl2::alist-fix n-r))
    (b* ((n-r (acl2::alist-fix n-r)))
      (if (consp n-r)
          (cons (var-judgement (symbol-fix (caar n-r))
                               (symbol-fix (cdar n-r)))
                (domain-judgement-helper (cdr n-r)))
        nil))
    ///
    (fty::deffixequiv domain-judgement-helper))

  (define fn-judgement->expr ((j fn-judgement-p))
    :returns (rv pseudo-termp)
    (b* ((j (fn-judgement-fix j))
         (name (fn-judgement->name j))
         (domain (fn-judgement->domain j))
         (range (fn-judgement->range j))
         ((if (or (equal name 'quote)
                  (equal range 'quote)))
          't)
         (domain-syms (constant-list 'x (len domain)))
         (domain-judgements (domain-judgement-helper (pairlis$ domain-syms domain))))
      (implies-expr (and-list-expr (var-judgement-list->expr-list domain-judgements))
                    `(,range (,name ,@domain-syms))))
    ///
    (fty::deffixequiv fn-judgement->expr))

  (std::defprojection fn-judgement-list->expr-list ((x fn-judgement-list-p))
    :returns (rv pseudo-term-listp)
    (fn-judgement->expr x)
    ///
    (fty::deffixequiv fn-judgement-list->expr-list))

  (define smt-judgement->expr ((s-j smt-judgement-p))
    :returns (rv pseudo-termp)
    (b* ((s-j (smt-judgement-fix s-j))
         (var-jl (smt-judgement->vars s-j))
         (fn-jl (smt-judgement->fns s-j)))
      (and-expr (and-list-expr (var-judgement-list->expr-list
                                 var-jl))
                (and-list-expr (fn-judgement-list->expr-list
                                 fn-jl)))))

  )

(defsection smt-judgement-clause
  :parents (verified)

  (define smt-judgement-clause ((s-j smt-judgement-p)
                                (expr pseudo-termp))
    :returns (rv pseudo-termp)
    (b* ((s-j (smt-judgement-fix s-j))
         (expr (pseudo-term-fix expr))
         (var-jl (smt-judgement->vars s-j))
         (fn-jl (smt-judgement->fns s-j)))
      (implies-expr
        (and-expr `(acl2::any-p$inline (quote ,s-j))
                  (and-expr (and-list-expr (var-judgement-list->expr-list
                                             var-jl))
                            (and-list-expr (fn-judgement-list->expr-list
                                             fn-jl))))
        expr))
    ///
    (fty::deffixequiv smt-judgement-clause))

  (define smt-judgement-clause->expr ((cl pseudo-termp))
    :returns (rv pseudo-termp)
    (b* (((unless (pseudo-termp cl)) nil))
      (case-match cl
        (('if & ('if e ''t ''nil) ''t) e)
        (& nil))))

  (define smt-judgement-clause->judgement ((cl pseudo-termp))
    :returns (mv (fail booleanp)
                 (judgement smt-judgement-p))
    (b* (((unless (pseudo-termp cl))
          (mv t (make-smt-judgement)))
         (smt-j (case-match cl
                  (('if ('if ('acl2::any-p$inline ('quote j)) & ''nil) & ''t) j)
                  (& nil)))
         (expr (smt-judgement-clause->expr cl)))
      (if (and (smt-judgement-p smt-j)
               (pseudo-termp expr)
               (equal (smt-judgement-clause smt-j expr)
                      cl))
          (mv nil smt-j)
        (mv t (make-smt-judgement)))))

  )
