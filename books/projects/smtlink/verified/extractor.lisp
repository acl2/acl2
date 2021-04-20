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
(include-book "evaluator")

;; (defsection SMT-extract
;;   :parents (verified)

(define var-equal-p ((term pseudo-termp))
  :returns (ok booleanp)
  (b* ((term (pseudo-term-fix term)))
    (case-match term
      (('equal lhs &) (symbolp lhs))
      (& nil)))
  ///
  (more-returns
   (ok (implies (and ok (pseudo-termp term))
                (and (consp term)
                     (symbolp (cadr term))))
       :name implies-of-var-equal-p)))

;; (deflist var-equal-list
;;   :elt-type var-equal-p
;;   :true-listp t
;;   :pred var-equal-list-p)

(define hypo-p ((term pseudo-termp) (fixinfo smt-fixtype-info-p))
  :returns (ok booleanp)
  (b* ((term (pseudo-term-fix term))
       (fixinfo (smt-fixtype-info-fix fixinfo)))
    (or (type-decl-p term fixinfo)
        (var-equal-p term)))
  ///
  (more-returns
   (ok (implies (and ok (pseudo-termp term))
                (and (consp term)
                     (symbolp (cadr term))))
       :name implies-of-hypo-p)))

(defthm pseudo-term-listp-of-append-of-pseudo-term-listp
  (implies (and (pseudo-term-listp x) (pseudo-term-listp y))
           (pseudo-term-listp (append x y))))

(local (in-theory (e/d ()
                       (consp-of-pseudo-lambdap
                        symbol-listp
                        pseudo-lambdap-of-fn-call-of-pseudo-termp
                        lambda-of-pseudo-lambdap
                        acl2::true-listp-of-car-when-true-list-listp
                        true-list-listp
                        pseudo-term-listp-of-cdr-of-pseudo-termp
                        pseudo-term-listp-of-cdr-pseudo-termp-if))))

(defines extract
  :parents (SMT-extract)
  :short "Functions for extracting type declarations from clause."
  :hints (("Goal" :in-theory (enable pseudo-term-fix)))
  :flag-local nil

  (define extract-disjunct ((term pseudo-termp) (fixinfo smt-fixtype-info-p))
    :returns (mv (extracted pseudo-term-listp)
                 (new-term pseudo-termp))
    :verify-guards nil
    (b* ((term (pseudo-term-fix term)))
      (cond ((not (consp term)) (mv nil term))
            ((and (equal (car term) 'if) (equal (caddr term) ''t))
             (b* (((mv decl1 term1) (extract-disjunct (cadr term) fixinfo))
                  ((mv decl2 term2) (extract-disjunct (cadddr term) fixinfo)))
               (mv (append decl1 decl2)
                   (cond ((or (equal term1 ''t) (equal term2 ''t)) ''t)
                         ((equal term1 ''nil) term2)
                         ((equal term2 ''nil) term1)
                         (t `(if ,term1 't ,term2))))))
            ((equal (car term) 'not)
             (b* (((mv decl0 term0) (extract-conjunct (cadr term) fixinfo)))
               (mv decl0
                   (cond ((equal term0 ''nil) ''t)
                         ((equal term0 ''t)   ''nil)
                         (t `(not ,term0))))))
            ((or (equal (car term) 'implies)
                 (and (equal (car term) 'if) (equal (cadddr term) ''t)))
             (b* (((mv decl1 term1) (extract-conjunct (cadr term) fixinfo))
                  ((mv decl2 term2) (extract-disjunct (caddr term) fixinfo)))
               (mv (append decl1 decl2)
                   (cond ((or (equal term1 ''nil) (equal term2 ''t)) ''t)
                         ((equal term1 ''t) term2)
                         ((equal term2 ''nil) `(not ,term1))
                         (t `(if ,term1 ,term2 't))))))
            (t (mv nil term)))))

  (define extract-conjunct ((term pseudo-termp) (fixinfo smt-fixtype-info-p))
    :returns (mv (extracted pseudo-term-listp)
                 (new-term pseudo-termp))
    :verify-guards nil
    (b* ((term (pseudo-term-fix term)))
      (cond ((not (consp term)) (mv nil term))
            ((and (equal (car term) 'if) (equal (cadddr term) ''nil))
             (b* (((mv decl1 term1) (extract-conjunct (cadr term) fixinfo))
                  ((mv decl2 term2) (extract-conjunct (caddr term) fixinfo)))
               (mv (append decl1 decl2)
                   (cond ((or (equal term1 ''nil) (equal term2 ''nil)) ''nil)
                         ((equal term1 ''t) term2)
                         ((equal term2 ''t) term1)
                         (t `(if ,term1 ,term2 'nil))))))
            ((equal (car term) 'not)
             (b* (((mv decl0 term0) (extract-disjunct (cadr term) fixinfo)))
               (mv decl0
                   (cond ((equal term0 ''nil) ''t)
                         ((equal term0 ''t)   ''nil)
                         (t `(not ,term0))))))
            ((hypo-p term fixinfo)
             (mv (list term) ''t))
            (t (mv nil term)))))
  )

(verify-guards extract-conjunct)

(define extractor ((term pseudo-termp) (fixinfo smt-fixtype-info-p))
  :returns (mv (hypo-lst pseudo-term-listp) (theorem pseudo-termp))
  (extract-disjunct term fixinfo))

#|
(extractor '(if (if (equal x2 (binary-+ x0 x1))
                    (if (equal x1 (rfix y))
                        (if (equal x0 (ifix x)) 't 'nil)
                      'nil)
                  'nil)
                (if (if (< x y)
                        (if (integerp x) (rationalp y) 'nil)
                      'nil)
                    (< x2 '0)
                  't)
              't)
           `((integerp . ,(make-info-pair :fn-type :recognizer))
             (rationalp . ,(make-info-pair :fn-type :recognizer))))
|#

(defthm-extract-flag
  (defthm correctness-of-extract-disjunct
    (implies (and (pseudo-termp term)
                  (smt-fixtype-info-p fixinfo)
                  (alistp a))
             (b* (((mv hypo-lst new-term)
                   (extract-disjunct term fixinfo)))
               (iff (ev-smtcp `(if ,(conjoin hypo-lst) ,new-term 't) a)
                    (ev-smtcp term a))))
    :flag extract-disjunct
    :hints ((and stable-under-simplificationp
                 '(:in-theory (e/d (extract-disjunct extract-conjunct) ())))))
  (defthm correctness-of-extract-conjunct
    (implies (and (pseudo-termp term)
                  (smt-fixtype-info-p fixinfo)
                  (alistp a))
             (b* (((mv hypo-lst new-term)
                   (extract-conjunct term fixinfo)))
               (iff (ev-smtcp `(if ,(conjoin hypo-lst) ,new-term 'nil) a)
                    (ev-smtcp term a))))
    :flag extract-conjunct
    :hints ((and stable-under-simplificationp
                 '(:in-theory (e/d (extract-disjunct extract-conjunct) ()))))))

(defthm correctness-of-extractor
  (implies (and (pseudo-termp term)
                (smt-fixtype-info-p fixinfo)
                (alistp a))
           (b* (((mv hypo-lst new-term) (extractor term fixinfo)))
             (iff (ev-smtcp `(if ,(conjoin hypo-lst) ,new-term 't) a)
                  (ev-smtcp term a))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (enable extractor))))

;;)

