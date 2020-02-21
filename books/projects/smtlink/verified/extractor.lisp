;; Copyright (C) 2015, University of British Columbia
;; Written (originally) by Yan Peng (13th March, 2014)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2


(in-package "SMT")
(include-book "centaur/fty/top" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)

(include-book "hint-interface")
(include-book "basics")


(defsection SMT-extract
  :parents (verified)
  :short "SMT-extract extracts type hypotheses from the clause. The SMT solver requires knowing type declarations."

  (define is-type-hyp-decl ((expr pseudo-termp))
    :returns (is-type-hyp? booleanp)
    (b* (((unless (equal (len expr) 3))
          nil)
         (fn-name (car expr))
         ((unless (equal fn-name 'type-hyp)) nil))
      t))

  (define extract-is-decl ((expr pseudo-termp) (fty-info fty-info-alist-p)
                           (abs symbol-listp))
    :returns (is-decl? booleanp)
    (b* (((if (is-type-hyp-decl expr)) t)
         ((unless (equal (len expr) 2))
          nil)
         (fn-name (car expr))
         ((unless (symbolp fn-name)) nil)
         ((unless
              (or ;; basic types
               (member-equal fn-name (strip-cars *SMT-types*))
               ;; abstract types
               (member-equal fn-name abs)
               ;; fty types
               (typedecl-of-flextype fn-name fty-info)
               ))
          nil)
         ((unless (and (symbolp (cadr expr)) (cadr expr))) nil))
      t))

  (defthm pseudo-term-listp-of-append-of-pseudo-term-listp
    (implies (and (pseudo-term-listp x) (pseudo-term-listp y))
             (pseudo-term-listp (append x y))))

  (local (in-theory (enable pseudo-termp pseudo-term-listp
                            pseudo-term-fix
                            pseudo-term-list-fix)))

  (defines extract
    :parents (SMT-extract)
    :short "Functions for extracting type declarations from clause."

    (define extract-disjunct ((term pseudo-termp) (fty-info fty-info-alist-p)
                              (abs symbol-listp))
      :returns (mv (decl-list pseudo-term-listp) (theorem pseudo-termp))
      :verify-guards nil
      :guard-debug t
      ;; looking for (typep var) where var *not* satisfying typep make term trivially true
      (b* ((term (pseudo-term-fix term)))
        (cond ((not (consp term)) (mv nil term))
              ((and (equal (car term) 'if) (equal (caddr term) ''t))
               (b* (((mv decl1 term1) (extract-disjunct (cadr term) fty-info abs))
                    ((mv decl2 term2) (extract-disjunct (cadddr term) fty-info abs)))
                 (mv (append decl1 decl2)
                     (cond ((or (equal term1 ''t) (equal term2 ''t)) ''t)
                           ((equal term1 ''nil) term2)
                           ((equal term2 ''nil) term1)
                           (t `(if ,term1 't ,term2))))))
              ((equal (car term) 'not)
               (b* (((mv decl0 term0) (extract-conjunct (cadr term) fty-info abs)))
                 (mv decl0
                     (cond ((equal term0 ''nil) ''t)
                           ((equal term0 ''t)   ''nil)
                           (t `(not ,term0))))))
              ((equal (car term) 'implies)
               (b* (((mv decl1 term1) (extract-conjunct (cadr term) fty-info abs))
                    ((mv decl2 term2) (extract-disjunct (caddr term) fty-info abs)))
                 (mv (append decl1 decl2)
                     (cond ((or (equal term1 ''nil) (equal term2 ''t)) ''t)
                           ((equal term1 ''t) term2)
                           ((equal term2 ''nil) `(not ,term1))
                           (t `(implies ,term1 ,term2))))))
              (t (mv nil term)))))

    (define extract-conjunct ((term pseudo-termp) (fty-info fty-info-alist-p)
                              (abs symbol-listp))
      :returns (mv (decl-list pseudo-term-listp) (theorem pseudo-termp))
      :verify-guards nil
      :guard-debug t
      ;; looking for (typep var) where var *not* satisfying typep make term trivially false
      (b* ((term (pseudo-term-fix term)))
        (cond ((not (consp term)) (mv nil term))
              ((and (equal (car term) 'if) (equal (cadddr term) ''nil))
               (b* (((mv decl1 term1) (extract-conjunct (cadr term) fty-info abs))
                    ((mv decl2 term2) (extract-conjunct (caddr term) fty-info abs)))
                 (mv (append decl1 decl2)
                     (cond ((or (equal term1 ''nil) (equal term2 ''nil)) ''nil)
                           ((equal term1 ''t) term2)
                           ((equal term2 ''t) term1)
                           (t `(if ,term1 ,term2 'nil))))))
              ((equal (car term) 'not)
               (b* (((mv decl0 term0) (extract-disjunct (cadr term) fty-info abs)))
                 (mv decl0
                     (cond ((equal term0 ''nil) ''t)
                           ((equal term0 ''t)   ''nil)
                           (t `(not ,term0))))))
              ((extract-is-decl term fty-info abs)
               (mv (list term) ''t))
              (t (mv nil term)))))
    )

  (verify-guards extract-conjunct)
  (verify-guards extract-disjunct)

  (define SMT-extract ((term pseudo-termp) (fty-info fty-info-alist-p)
                       (abs symbol-listp))
    :returns (mv (decl-list pseudo-term-listp) (theorem pseudo-termp))
    (b* (((mv decl-list theorem) (extract-disjunct term fty-info abs)))
      (mv decl-list theorem)))
)

