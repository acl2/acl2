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
(include-book "type-hyp")
(include-book "basics")

(defsection SMT-extract
  :parents (verified)
  :short "SMT-extract extracts type hypotheses from the clause. The SMT solver requires knowing type declarations."

  (defthm pseudo-term-listp-of-append-of-pseudo-term-listp
    (implies (and (pseudo-term-listp x) (pseudo-term-listp y))
             (pseudo-term-listp (append x y))))

  (local (in-theory (enable pseudo-termp pseudo-term-listp
                            pseudo-term-fix
                            pseudo-term-list-fix)))

  (defines extract
    :parents (SMT-extract)
    :short "Functions for extracting type declarations from clause."

    (define extract-disjunct ((term pseudo-termp) (fixinfo smt-fixtype-info-p)
                              (abs symbol-listp))
      :returns (mv (decl-list pseudo-term-listp) (theorem pseudo-termp))
      :verify-guards nil
      ;; looking for (typep var) where var *not* satisfying typep make term trivially true
      (b* ((term (pseudo-term-fix term)))
        (cond ((not (consp term)) (mv nil term))
              ((and (equal (car term) 'if) (equal (caddr term) ''t))
               (b* (((mv decl1 term1) (extract-disjunct (cadr term) fixinfo abs))
                    ((mv decl2 term2) (extract-disjunct (cadddr term) fixinfo abs)))
                 (mv (append decl1 decl2)
                     (cond ((or (equal term1 ''t) (equal term2 ''t)) ''t)
                           ((equal term1 ''nil) term2)
                           ((equal term2 ''nil) term1)
                           (t `(if ,term1 't ,term2))))))
              ((equal (car term) 'not)
               (b* (((mv decl0 term0) (extract-conjunct (cadr term) fixinfo abs)))
                 (mv decl0
                     (cond ((equal term0 ''nil) ''t)
                           ((equal term0 ''t)   ''nil)
                           (t `(not ,term0))))))
              ((equal (car term) 'implies)
               (b* (((mv decl1 term1) (extract-conjunct (cadr term) fixinfo abs))
                    ((mv decl2 term2) (extract-disjunct (caddr term) fixinfo abs)))
                 (mv (append decl1 decl2)
                     (cond ((or (equal term1 ''nil) (equal term2 ''t)) ''t)
                           ((equal term1 ''t) term2)
                           ((equal term2 ''nil) `(not ,term1))
                           (t `(implies ,term1 ,term2))))))
              (t (mv nil term)))))

(define extract-conjunct ((term pseudo-termp) (fixinfo smt-fixtype-info-p)
                          (abs symbol-listp))
      :returns (mv (decl-list pseudo-term-listp) (theorem pseudo-termp))
      :verify-guards nil
      ;; looking for (typep var) where var *not* satisfying typep make term trivially false
      (b* ((term (pseudo-term-fix term)))
        (cond ((not (consp term)) (mv nil term))
              ((and (equal (car term) 'if) (equal (cadddr term) ''nil))
               (b* (((mv decl1 term1) (extract-conjunct (cadr term) fixinfo abs))
                    ((mv decl2 term2) (extract-conjunct (caddr term) fixinfo abs)))
                 (mv (append decl1 decl2)
                     (cond ((or (equal term1 ''nil) (equal term2 ''nil)) ''nil)
                           ((equal term1 ''t) term2)
                           ((equal term2 ''t) term1)
                           (t `(if ,term1 ,term2 'nil))))))
              ((equal (car term) 'not)
               (b* (((mv decl0 term0) (extract-disjunct (cadr term) fixinfo abs)))
                 (mv decl0
                     (cond ((equal term0 ''nil) ''t)
                           ((equal term0 ''t)   ''nil)
                           (t `(not ,term0))))))
              ((or (type-decl-p term fixinfo abs) (is-type-hyp term))
               (mv (list term) ''t))
              (t (mv nil term)))))
    )

  (verify-guards extract-conjunct)
  (verify-guards extract-disjunct)

  (define smt-extract ((term pseudo-termp) (fixinfo smt-fixtype-info-p)
                       (abs symbol-listp))
    :returns (mv (decl-list pseudo-term-listp) (theorem pseudo-termp))
    (b* (((mv decl-list theorem) (extract-disjunct term fixinfo))
         ;; (- (cw "decl-list: ~q0theorem:~q1" decl-list theorem))
         )
      (mv decl-list theorem)))
)

