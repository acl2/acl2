; Centaur Meta-reasoning Library
; Copyright (C) 2019 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Sol Swords <sswords@centtech.com>

(in-package "CMR")

(include-book "term-vars")
(include-book "subst")
(include-book "centaur/misc/errmsg" :dir :system)
(include-book "clause-processors/unify-subst" :dir :system)
(include-book "clause-processors/join-thms" :dir :system)
(include-book "lambda-measure")
(local (std::add-default-post-define-hook :fix))

(local (include-book "std/lists/append" :dir :system))

(defevaluator parse-rw-ev parse-rw-ev-list
  ((if a b c)
   (implies a b)
   (equal a b)
   (iff a b)
   (not x))
  :namedp t)

(acl2::def-join-thms parse-rw-ev)
(acl2::def-ev-pseudo-term-fty-support parse-rw-ev parse-rw-ev-list)

;; (local (defthm alistp-of-pairlis$
;;          (alistp (pairlis$ a b))))

;; (local (defthm alistp-of-append
;;          (implies (and (alistp a) (alistp b))
;;                   (alistp (append a b)))))

;; (defthm true-listp-of-parse-rw-ev-list
;;   (true-listp (parse-rw-ev-list x a))
;;   :hints (("goal" :induct (len x)))
;;   :rule-classes :type-prescription)

;; (define parse-rw-ev-bindinglist ((x bindinglist-p) (a alistp))
;;   ;; Returns the alist for evaluating a body term nested inside all the
;;   ;; bindings.
;;   :returns (final-alist alistp)
;;   (b* (((when (atom x)) (acl2::alist-fix a))
;;        ((binding x1) (car x))
;;        (new-bindings (pairlis$ x1.formals (parse-rw-ev-list x1.args a))))
;;     (parse-rw-ev-bindinglist (cdr x) (append new-bindings a))))

;; (defret parse-rw-ev-of-lambda-nest-to-bindinglist
;;   (equal (parse-rw-ev body (parse-rw-ev-bindinglist bindings a))
;;          (parse-rw-ev x a))
;;   :hints (("goal" :use ((:functional-instance lambda-nest-to-bindinglist-correct
;;                          (base-ev parse-rw-ev)
;;                          (base-ev-list parse-rw-ev-list)
;;                          (base-ev-bindinglist parse-rw-ev-bindinglist)))
;;            :in-theory (enable parse-rw-ev-bindinglist)))
;;   :fn lambda-nest-to-bindinglist)

;; (defret parse-rw-ev-of-bindinglist-to-lambda-nest
;;   (equal (parse-rw-ev term a)
;;          (parse-rw-ev body (parse-rw-ev-bindinglist x a)))
;;   :hints (("goal" :use ((:functional-instance bindinglist-to-lambda-nest-correct
;;                          (base-ev parse-rw-ev)
;;                          (base-ev-list parse-rw-ev-list)
;;                          (base-ev-bindinglist parse-rw-ev-bindinglist)))))
;;   :fn bindinglist-to-lambda-nest)

(defprod rw-pair
  ((hyps pseudo-term-listp)
   (concl pseudo-termp))
  :layout :list)

(deflist rw-pairlist :elt-type rw-pair :true-listp t)

(define rw-pair-term ((x rw-pair-p))
  :returns (term pseudo-termp)
  (b* (((rw-pair x)))
    `(implies ,(conjoin x.hyps) ,x.concl)))

(define rw-pairlist-terms ((x rw-pairlist-p))
  :returns (terms pseudo-term-listp)
  (if (atom x)
      nil
    (cons (rw-pair-term (car x))
          (rw-pairlist-terms (cdr x)))))
  

(define parse-rewrite-hyps ((x pseudo-termp))
  :returns (hyps pseudo-term-listp)
  :measure (pseudo-term-count x)
  (pseudo-term-case x
    :fncall (b* (((when (and (eq x.fn 'if)
                             (equal (third x.args) ''nil)))
                  (append (parse-rewrite-hyps (first x.args))
                          (parse-rewrite-hyps (second x.args)))))
              (list (pseudo-term-fix x)))
    :otherwise (list (pseudo-term-fix x)))
  ///
  (defret parse-rw-ev-of-<fn>
    (iff (parse-rw-ev (conjoin hyps) env)
         (parse-rw-ev x env))))

(defthm parse-rw-ev-of-conjoin-pseudo-term-list-fix
  (iff (parse-rw-ev (conjoin (pseudo-term-list-fix x)) a)
       (parse-rw-ev (conjoin x) a))
  :hints (("goal" :induct (len x)
           :expand ((pseudo-term-list-fix X))
           :in-theory (enable parse-rw-ev-conjoin-when-consp))))

(local (defthm pseudo-term-list-fix-of-append
         (Equal (pseudo-term-list-fix (append x y))
                (append (pseudo-term-list-fix x)
                        (pseudo-term-list-fix y)))))

(define rw-pairs-add-hyps ((hyps pseudo-term-listp)
                           (rules rw-pairlist-p))
  :returns (new-rules rw-pairlist-p)
  (if (atom rules)
      nil
    (cons (b* (((rw-pair rule) (car rules)))
            (change-rw-pair rule :hyps (append hyps rule.hyps)))
          (rw-pairs-add-hyps hyps (cdr rules))))
  ///
  (defret parse-rw-ev-of-<fn>
    (iff (parse-rw-ev (conjoin (rw-pairlist-terms new-rules)) env)
         (or (not (parse-rw-ev (conjoin hyps) env))
             (parse-rw-ev (conjoin (rw-pairlist-terms rules)) env)))
    :hints(("Goal" :in-theory (enable rw-pairlist-terms rw-pair-term)))))


(local (defthm pairlis-strip-cars-of-pair-vars
         (implies (equal (len x) (len y))
                  (equal (pairlis$ (strip-cars (pair-vars x y))
                                   (lambda-measure-list
                                    (strip-cdrs (pair-vars x y))
                                    a))
                         (pair-vars x (lambda-measure-list y a))))
         :hints(("Goal" :in-theory (enable lambda-measure-list pair-vars pairlis$)))))


(local (defthm pseudo-term-subst-p-implies-pseudo-term-substp
         (implies (pseudo-term-subst-p x)
                  (acl2::pseudo-term-substp x))
         :hints(("Goal" :in-theory (enable acl2::pseudo-term-substp)))))


(define parse-rw-ev-alist ((x pseudo-term-subst-p) a)
  :verify-guards nil
  (if (atom x)
      nil
    (if (mbt (and (consp (car x))
                  (pseudo-var-p (caar x))))
        (cons (cons (caar x) (parse-rw-ev (cdar x) a))
              (parse-rw-ev-alist (cdr x) a))
      (parse-rw-ev-alist (cdr x) a)))
  ///

  (defthm lookup-in-parse-rw-ev-alist-split
    (equal (assoc k (parse-rw-ev-alist x a))
           (and (pseudo-var-p k)
                (let ((look (assoc k x)))
                  (and look
                       (cons k (parse-rw-ev (cdr look) a)))))))

  (local (in-theory (enable pseudo-term-subst-fix))))

;; (define parse-rw-ev-alist (x al)
;;   :verify-guards nil
;;   (if (atom x)
;;       nil
;;     (cons (cons (caar x) (parse-rw-ev (cdar x) al))
;;           (parse-rw-ev-alist (cdr x) al)))
;;   ///
;;   (defthm assoc-equal-parse-rw-ev-alist
;;     (equal (cdr (assoc-equal k (parse-rw-ev-alist x al)))
;;            (parse-rw-ev (cdr (assoc-equal k x)) al)))

;;   (defthm assoc-equal-parse-rw-ev-alist-iff
;;     (implies k
;;              (iff (assoc-equal k (parse-rw-ev-alist x al))
;;                   (assoc-equal k x))))

;;   (defthm assoc-equal-parse-rw-ev-alist-when-assoc
;;     (implies (assoc k x)
;;              (assoc k (parse-rw-ev-alist x al))))

;;   (defthm parse-rw-ev-alist-pairlis$
;;     (equal (parse-rw-ev-alist (pairlis$ a b) al)
;;            (pairlis$ a
;;                      (parse-rw-ev-list b al))))

;;   (defthm parse-rw-ev-alist-of-cons
;;     (equal (parse-rw-ev-alist (cons x y) a)
;;            (cons (cons (car x) (parse-rw-ev (cdr x) a))
;;                  (parse-rw-ev-alist y a))))

;;   (defthm parse-rw-ev-alist-of-pair-vars
;;     (equal (parse-rw-ev-alist (pair-vars x y) env)
;;            (pair-vars x (parse-rw-ev-list y env)))
;;     :hints(("Goal" :in-theory (enable pair-vars)))))

;; (local
;;  (acl2::defthm-substitute-into-term-flag
;;    substitute-into-term-correct-lemma
;;    (defthm parse-rw-ev-of-substitute-into-term
;;      (equal (parse-rw-ev (acl2::substitute-into-term x subst) a)
;;             (parse-rw-ev x (parse-rw-ev-alist subst a)))
;;      :hints ('(:expand ((acl2::substitute-into-term x subst)
;;                         (acl2::substitute-into-term nil subst)))
;;              (and stable-under-simplificationp
;;                   '(:in-theory (enable parse-rw-ev-of-fncall-args))))
;;      :flag acl2::substitute-into-term)
;;    (defthm parse-rw-ev-of-substitute-into-list
;;      (equal (parse-rw-ev-list (acl2::substitute-into-list x subst) a)
;;             (parse-rw-ev-list x (parse-rw-ev-alist subst a)))
;;      :hints ('(:expand ((acl2::substitute-into-list x subst))))
;;      :flag acl2::substitute-into-list)))

(acl2::def-functional-instance parse-rw-ev-of-term-subst-strict
  base-ev-of-term-subst-strict
  ((base-ev parse-rw-ev)
   (base-ev-list parse-rw-ev-list)
   (base-ev-alist parse-rw-ev-alist))
  :hints(("Goal" :in-theory (enable parse-rw-ev-alist))))

;; (include-book "centaur/misc/starlogic" :dir :system)

(defthm rw-pairlist-terms-of-append
  (equal (rw-pairlist-terms (append a b))
         (append (rw-pairlist-terms a)
                 (rw-pairlist-terms b)))
  :hints(("Goal" :in-theory (enable rw-pairlist-terms))))

(local (defthm parse-rw-ev-alist-of-pair-vars
         (equal (parse-rw-ev-alist (pair-vars x y) env)
                (pair-vars x (parse-rw-ev-list y env)))
         :hints(("Goal" :in-theory (enable parse-rw-ev-alist
                                           pair-vars)))))

(define rw-pair-nonlambda-p ((x rw-pair-p))
  :enabled t
  (not (pseudo-term-case (rw-pair->concl x) :lambda)))

(define rw-pairs-nonlambda-p ((x rw-pairlist-p))
  (if (atom x)
      t
    (and (rw-pair-nonlambda-p (car x))
         (rw-pairs-nonlambda-p (cdr x))))
  ///
  (defthm rw-pairs-nonlambda-p-of-append
    (implies (and (rw-pairs-nonlambda-p x)
                  (rw-pairs-nonlambda-p y))
             (rw-pairs-nonlambda-p (append x y))))

  (defthm rw-pairs-nonlambda-p-of-rw-pairs-add-hyps
    (equal (rw-pairs-nonlambda-p (rw-pairs-add-hyps hyps x))
           (rw-pairs-nonlambda-p x))
    :hints(("Goal" :in-theory (enable rw-pairs-add-hyps)))))

(define term-parse-rw-pairs ((x pseudo-termp))
  :returns (rw-pairs rw-pairlist-p)
  :measure (lambda-measure x nil)
  :hints ('(:expand ((lambda-measure x nil)
                     (lambda-measure-list (pseudo-term-call->args x) nil)
                     (lambda-measure-list (cdr (pseudo-term-call->args x)) nil))
            :in-theory (enable sum-nat-list)))
  :verify-guards nil
  (pseudo-term-case x
    :const (list (make-rw-pair :concl x))
    :var (list (make-rw-pair :concl x))
    :fncall (b* (((when (acl2::and (eq x.fn 'implies)
                                     (eql (len x.args) 2)))
                  (b* ((hyps1 (parse-rewrite-hyps (first x.args)))
                       (rw-pairs (term-parse-rw-pairs (second x.args))))
                    (rw-pairs-add-hyps hyps1 rw-pairs)))
                 ((when (acl2::and (eq x.fn 'if)
                                     (eql (len x.args) 3)
                                     (equal (third x.args) ''nil)))
                  (append (term-parse-rw-pairs (first x.args))
                          (term-parse-rw-pairs (second x.args)))))
              (list (make-rw-pair :concl x)))
    :lambda (term-parse-rw-pairs (term-subst-strict x.body (pair-vars x.formals x.args))))
  ;; (define term-parse-rw-pairs-lambda ((x pseudo-termp)
  ;;                                    (w plist-worldp)
  ;;                                    (subst pseudo-term-subst-p))
  ;;   :returns (mv (err (iff (stringp err) err))
  ;;                (hyps pseudo-term-listp)
  ;;                (equiv pseudo-fnsym-p)
  ;;                (lhs pseudo-termp)
  ;;                (rhs pseudo-termp))
  ;;   :measure (lambda-measure x (pseudo-term-count x)
  ;;   (pseudo-term-case x
  ;;     :lambda (b* ((subst-args (acl2::substitute-into-list x.args (pseudo-term-subst-fix subst)))
  ;;                  (new-subst (pair-vars x.formals subst-args)))
  ;;               (term-parse-rw-pairs-lambda x.body w new-subst))
  ;;     :otherwise (term-parse-rw-pairs-core (acl2::substitute-into-term (pseudo-term-fix x)
  ;;                                                                     (pseudo-term-subst-fix subst))
  ;;                                         w))
  ;;   ///
  ;;   (defret parse-rw-ev-of-<fn>
  ;;     (implies (not err)
  ;;              (iff (parse-rw-ev `(implies ,(conjoin hyps)
  ;;                                          (,equiv ,lhs ,rhs))
  ;;                                env)
  ;;                   (parse-rw-ev (acl2::substitute-into-term (pseudo-term-fix x)
  ;;                                                            (pseudo-term-subst-fix subst))
  ;;                                env)))
  ;;     :hints(("Goal" :induct t
  ;;             :in-theory (enable parse-rw-ev-of-fncall-args)))))
  ///

  (verify-guards term-parse-rw-pairs)

  (local (defthm equal-plus-const
           (implies (and (syntaxp (and (quotep c1) (quotep c2)))
                         (acl2-numberp c2))
                    (equal (equal (+ c1 a) c2)
                           (equal (fix a) (- c2 c1))))))
  (local (defthm len-equal-const
           (implies (syntaxp (quotep c))
                    (equal (equal (len x) c)
                           (if (zp c)
                               (and (atom x) (equal 0 c))
                             (and (consp x)
                                  (equal (len (cdr x)) (1- c))))))))


  (defret parse-rw-ev-of-<fn>
    (iff (parse-rw-ev (conjoin (rw-pairlist-terms rw-pairs)) env)
         (parse-rw-ev x env))
    :hints(("Goal" :in-theory (enable parse-rw-ev-of-fncall-args
                                      rw-pair-term)
            :induct <call>
            :expand (<call>
                     (:free (x) (rw-pairlist-terms (list x)))))))

  (defret rw-pairs-nonlambda-p-of-<fn>
    (rw-pairs-nonlambda-p rw-pairs)
    :hints(("Goal"
            :induct <call>
            :expand (<call>
                     (:free (x) (rw-pairs-nonlambda-p (list x))))))))



(defprod rewrite
  ((hyps pseudo-term-listp)
   (equiv pseudo-fnsym-p)
   (lhs pseudo-termp)
   (rhs pseudo-termp))
  :layout :list)

(define rewrite-term ((x rewrite-p))
  :returns (term pseudo-termp)
  (b* (((rewrite x)))
    `(implies ,(conjoin x.hyps)
              (,x.equiv ,x.lhs ,x.rhs))))

(deflist rewritelist :elt-type rewrite :true-listp t)

(define rewritelist-terms ((x rewritelist-p))
  :returns (terms pseudo-term-listp)
  (if (atom x)
      nil
    (cons (rewrite-term (car x))
          (rewritelist-terms (cdr x))))
  ///
  (defthm rewritelist-terms-of-append
    (equal (rewritelist-terms (append x y))
           (append (rewritelist-terms x)
                   (rewritelist-terms y)))))

(define check-rewrite-lhs ((x pseudo-termp))
  :returns (errmsg acl2::errmsg-type-p :rule-classes :type-prescription)
  (pseudo-term-case x
    :const (msg "constant ~x0" x.val)
    :var (msg "variable ~x0" x.name)
    :lambda (msg "lambda call ~x0~%" (pseudo-term-fix x))
    :otherwise nil)
  ///
  (defthm check-rewrite-lhs-under-iff
    (iff (check-rewrite-lhs x)
         (not (pseudo-term-case x :fncall)))))

(define rewritelist-lhs-fncalls-p ((x rewritelist-p))
  (if (atom x)
      t
    (and (pseudo-term-case (rewrite->lhs (car x)) :fncall)
         (rewritelist-lhs-fncalls-p (cdr x))))
  ///
  (defthm rewritelist-lhs-fncalls-p-of-append
    (implies (and (rewritelist-lhs-fncalls-p x)
                  (rewritelist-lhs-fncalls-p y))
             (rewritelist-lhs-fncalls-p (append x y)))))

(define rw-pair-to-rewrite ((x rw-pair-p) (w plist-worldp))
  :returns (mv (err acl2::errmsg-type-p :rule-classes :type-prescription)
               (rewrites rewritelist-p))
  (b* (((rw-pair x))
       (err1 (check-rewrite-lhs x.concl))
       ((when err1) (mv err1 nil))
       ((pseudo-term-fncall x.concl))
       (nargs (len x.concl.args))
       ((when (and (eq x.concl.fn 'not)
                   (eql nargs 1)))
        (b* ((arg1 (first x.concl.args))
             (err2 (check-rewrite-lhs arg1))
             ((when err2) (mv err2 nil)))
          (mv nil (list (make-rewrite :hyps x.hyps :equiv 'equal :lhs arg1 :rhs ''nil)))))
       ((when (and (eql nargs 2)
                   (getpropc x.concl.fn 'acl2::coarsenings nil w)))
        (b* ((arg1 (first x.concl.args))
             (err2 (check-rewrite-lhs arg1))
             ((when err2) (mv err2 nil)))
          (mv nil (list (make-rewrite :hyps x.hyps :equiv x.concl.fn :lhs arg1 :rhs (second x.concl.args)))))))
    (mv nil (list (make-rewrite :hyps x.hyps :equiv 'iff :lhs x.concl :rhs ''t))))
  ///
  (local (defthm len-equal-const
           (implies (syntaxp (quotep c))
                    (equal (equal (len x) c)
                           (if (zp c)
                               (and (atom x) (equal 0 c))
                             (and (consp x)
                                  (equal (len (cdr x)) (1- c))))))))

  (defret parse-rw-ev-of-rw-pair-to-rewrite
    (implies (not err)
             (iff (parse-rw-ev (conjoin (rewritelist-terms rewrites)) env)
                  (parse-rw-ev (rw-pair-term x) env)))
    :hints (("goal" :in-theory (enable rewrite-term rw-pair-term
                                       parse-rw-ev-of-fncall-args)
             :expand ((:free (x) (rewritelist-terms (list x)))))))

  (defret rw-pair-to-rewrite-when-err
    (implies err (equal rewrites nil)))

  (defret rewritelist-lhs-fncalls-p-of-<fn>
    (rewritelist-lhs-fncalls-p rewrites)
    :hints(("Goal" :in-theory (enable rewritelist-lhs-fncalls-p)))))

(define rw-pairs-to-rewrites ((x rw-pairlist-p) (w plist-worldp))
  :returns (mv (err acl2::errmsg-type-p :rule-classes :type-prescription)
               (rewrites rewritelist-p))
  (b* (((when (atom x)) (mv nil nil))
       ((mv err1 rewrites1) (rw-pair-to-rewrite (car x) w))
       ((mv err2 rewrites2) (rw-pairs-to-rewrites (cdr x) w)))
    (mv (or err1 err2) (append rewrites1 rewrites2)))
  ///
  (defret parse-rw-ev-of-<fn>-when-no-err
    (implies (not err)
             (iff (parse-rw-ev (conjoin (rewritelist-terms rewrites)) env)
                  (parse-rw-ev (conjoin (rw-pairlist-terms x)) env)))
    :hints(("Goal" :in-theory (enable rw-pairlist-terms))))

  (defret parse-rw-ev-of-<fn>
    (implies (parse-rw-ev (conjoin (rw-pairlist-terms x)) env)
             (parse-rw-ev (conjoin (rewritelist-terms rewrites)) env))
    :hints(("Goal" :in-theory (enable rw-pairlist-terms)
            :induct <call>)
           (and stable-under-simplificationp
                '(:cases ((mv-nth 0 (rw-pair-to-rewrite (car x) w)))))))

  (defret rewritelist-lhs-fncalls-p-of-<fn>
    (rewritelist-lhs-fncalls-p rewrites)))


(define parse-rewrites-from-term ((x pseudo-termp) (w plist-worldp))
  :returns (mv (err acl2::errmsg-type-p :rule-classes :type-prescription)
               (rewrites rewritelist-p))
  (b* ((pairs (term-parse-rw-pairs x)))
    (rw-pairs-to-rewrites pairs w))
  ///
  (defret parse-rw-ev-of-<fn>-when-no-err
    (implies (not err)
             (iff (parse-rw-ev (conjoin (rewritelist-terms rewrites)) env)
                  (parse-rw-ev x env))))

  (defret parse-rw-ev-of-<fn>
    (implies (parse-rw-ev x env)
             (parse-rw-ev (conjoin (rewritelist-terms rewrites)) env)))

  (defret rewritelist-lhs-fncalls-p-of-<fn>
    (rewritelist-lhs-fncalls-p rewrites)))




