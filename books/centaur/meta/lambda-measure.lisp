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
(include-book "substitute")
(include-book "centaur/fty/basetypes" :dir :system)

(local (std::add-default-post-define-hook :fix))

;; (define pair-nonnil-symbols ((vars symbol-listp)
;;                              (vals true-listp))
;;   :returns (subst alistp)
;;   (b* (((when (atom vars)) nil)
;;        (var (car vars))
;;        ((unless (and (mbt (symbolp var)) var))
;;         (pair-nonnil-symbols (cdr vars) (cdr vals))))
;;     (cons (cons var (car vals))
;;           (pair-nonnil-symbols (cdr vars) (cdr vals))))
;;   ///
(defthm assoc-of-pair-vars
  (equal (assoc k (pair-vars vars vals))
         (and k (symbolp k)
              (assoc k (pairlis$ vars vals))))
  :hints(("Goal" :in-theory (enable pair-vars))))

(defthm pseudo-var-list-p-strip-cars-of-pair-nonnil-symbols
  (pseudo-var-list-p (strip-cars (pair-vars vars vals)))
  :hints(("Goal" :in-theory (enable pair-vars))))

;;   (local (in-theory (enable list-fix))))


(fty::defmap var-counts-alist :key-type pseudo-var :val-type natp :true-listp t)


(define sum-nat-list ((x nat-listp))
  :returns (sum natp :rule-classes :type-prescription)
  (if (atom x)
      0
    (+ (lnfix (car x))
       (sum-nat-list (cdr x)))))

;; (define depths-max-list ((x nat-listp))
;;   :returns (sum natp :rule-classes :type-prescription)
;;   (if (atom x)
;;       0
;;     (max (lnfix (car x))
;;          (depths-max-list (cdr x)))))


(local (defthm integerp-when-natp
         (implies (natp x) (integerp x))))

(local (in-theory (disable natp)))

(local (defthm natp-lookup-in-var-counts-alist
         (implies (and (var-counts-alist-p x)
                       (cdr (assoc k x)))
                  (natp (cdr (assoc k x))))))

(local (defthm var-counts-alist-p-of-pair-vars
         (implies (and (equal (len x) (len y))
                       (nat-listp y))
                  (var-counts-alist-p (pair-vars x y)))
         :hints(("Goal" :in-theory (enable pair-vars)))))

(define nat-lists-<= ((x nat-listp)
                      (y nat-listp))
  :Guard (eql (len x) (len y))
  (if (atom x)
      t
    (and (<= (lnfix (car x)) (lnfix (car y)))
         (nat-lists-<= (cdr x) (cdr y))))
  ///
  ;; (defthm depths-max-list-when-nat-lists-<=
  ;;   (implies (nat-lists-<= x y)
  ;;            (<= (depths-max-list x) (depths-max-list y)))
  ;;   :hints(("Goal" :in-theory (enable depths-max-list)))
  ;;   :rule-classes :forward-chaining)

  (defthm sum-nat-list-when-nat-lists-<=
    (implies (nat-lists-<= x y)
             (<= (sum-nat-list x) (sum-nat-list y)))
    :hints(("Goal" :in-theory (enable sum-nat-list)))
    :rule-classes :forward-chaining))


;; (defines lambda-depth
;;   (define lambda-depth ((x pseudo-termp)
;;                         (var-counts-alist var-counts-alist-p))
;;     :returns (depth natp :rule-classes :type-prescription)
;;     :measure (pseudo-term-count x)
;;     :verify-guards nil
;;     (pseudo-term-case x
;;       :const 0
;;       :var (or (cdr (assoc x.name (var-counts-alist-fix var-counts-alist)))
;;                0)
;;       :fncall (depths-max-list (lambda-depth-list x.args var-counts-alist))
;;       :lambda (let ((lst (lambda-depth-list x.args var-counts-alist)))
;;                 (max (lambda-depth x.body (pair-vars x.formals lst))
;;                      (depths-max-list lst)))))
;;   (define lambda-depth-list ((x pseudo-term-listp)
;;                              (var-counts-alist var-counts-alist-p))
;;     :returns (depths nat-listp)
;;     :measure (pseudo-term-list-count x)
;;     (if (atom x)
;;         nil
;;       (cons (lambda-depth (car x) var-counts-alist)
;;             (lambda-depth-list (cdr x) var-counts-alist))))
;;   ///

;;   (defthm len-of-lambda-depths-list
;;     (equal (len (lambda-depth-list x var-counts-alist))
;;            (len x))
;;     :hints(("Goal" :in-theory (enable len))))

;;   (verify-guards lambda-depth)

;;   (defun-sk lambda-depth-when-nat-lists-<=-cond (x)
;;     (forall (vars vals1 vals2)
;;             (implies (nat-lists-<= vals1 vals2)
;;                      (<= (lambda-depth x (pair-vars vars vals1)) (lambda-depth x (pair-vars vars vals2)))))
;;     :rewrite :direct)

;;   (defthm lambda-depth-when-nat-lists-<=-linear
;;     (implies (and (lambda-depth-when-nat-lists-<=-cond x)
;;                   (nat-lists-<= vals1 vals2))
;;              (<= (lambda-depth x (pair-vars vars vals1)) (lambda-depth x (pair-vars vars vals2))))
;;     :rule-classes :linear)

;;   (defun-sk lambda-depth-list-when-nat-lists-<=-cond (x)
;;     (forall (vars vals1 vals2)
;;             (implies (nat-lists-<= vals1 vals2)
;;                      (nat-lists-<= (lambda-depth-list x (pair-vars vars vals1))
;;                                    (lambda-depth-list x (pair-vars vars vals2)))))
;;     :rewrite :direct)
  
;;   (defthm lambda-depth-list-when-nat-lists-<=-cond-linear
;;     (implies (and (lambda-depth-list-when-nat-lists-<=-cond x)
;;                   (nat-lists-<= vals1 vals2))
;;              (<= (depths-max-list (lambda-depth-list x (pair-vars vars vals1)))
;;                  (depths-max-list (lambda-depth-list x (pair-vars vars vals2)))))
;;     :hints (("goal" :use ((:instance lambda-depth-list-when-nat-lists-<=-cond-necc))
;;              :in-theory (disable lambda-depth-list-when-nat-lists-<=-cond-necc)))
;;     :rule-classes :linear)

;;   (defthm lambda-depth-of-pair-lambda-depth-list-when-nat-lists-<=-cond
;;     (implies (and (lambda-depth-when-nat-lists-<=-cond x)
;;                   (lambda-depth-list-when-nat-lists-<=-cond args)
;;                   (nat-lists-<= vals1 vals2))
;;              (<= (lambda-depth x (pair-vars
;;                                   formals
;;                                   (lambda-depth-list args
;;                                                      (pair-vars vars vals1))))
;;                  (lambda-depth x (pair-vars
;;                                   formals
;;                                   (lambda-depth-list args
;;                                                      (pair-vars vars vals2))))))
;;     :hints (("goal" :use ((:instance lambda-depth-list-when-nat-lists-<=-cond-necc
;;                            (x args)))
;;              :in-theory (disable lambda-depth-list-when-nat-lists-<=-cond-necc)))
;;     :rule-classes :linear)

;;   (local (in-theory (disable lambda-depth-when-nat-lists-<=-cond
;;                              lambda-depth-list-when-nat-lists-<=-cond)))

;;   (defthm assoc-of-pair-vars-when-nat-lists-<=
;;     (implies (nat-lists-<= vals1 vals2)
;;              (<= (cdr (assoc key (var-counts-alist-fix (pair-vars vars vals1))))
;;                  (cdr (assoc key (var-counts-alist-fix (pair-vars vars vals2))))))
;;     :hints (("Goal" :in-theory (enable nat-lists-<= pair-vars var-counts-alist-fix))))

;;   (defthm cdr-assoc-under-iff-when-depth-alist-p
;;     (implies (var-counts-alist-p x)
;;              (iff (cdr (assoc k x))
;;                   (assoc k x)))
;;     :hints(("Goal" :in-theory (enable var-counts-alist-p))))

;;   (defthm assoc-under-iff-of-var-counts-alist-fix
;;     (iff (assoc k (var-counts-alist-fix x))
;;          (and (pseudo-var-p k)
;;               (assoc k x)))
;;     :hints(("Goal" :in-theory (enable var-counts-alist-fix))))

;;   (defthm assoc-of-pairlis$-under-iff
;;     (iff (assoc k (pairlis$ keys vals))
;;          (member k keys)))

;;   (defret-mutual lambda-depth-when-nat-lists-<=-lemma
;;     (defret lambda-depth-when-nat-lists-<=-lemma
;;       (lambda-depth-when-nat-lists-<=-cond x)
;;       :hints ('(:expand ((lambda-depth-when-nat-lists-<=-cond x)
;;                          (:free (a) (lambda-depth x a)))))
;;       :fn lambda-depth)

;;     (defret lambda-depth-list-when-nat-lists-<=-lemma
;;       (lambda-depth-list-when-nat-lists-<=-cond x)
;;       :hints ('(:expand ((lambda-depth-list-when-nat-lists-<=-cond x)
;;                          (:free (a) (lambda-depth-list x a))
;;                          (:free (a b c d) (nat-lists-<= (cons a b) (cons c d)))
;;                          (nat-lists-<= nil nil))))
;;       :fn lambda-depth-list))

;;   (defret lambda-depth-when-nat-lists-<=
;;     (implies (nat-lists-<= vals1 vals2)
;;              (<= (lambda-depth x (pair-vars vars vals1)) (lambda-depth x (pair-vars vars vals2))))
;;     :hints (("goal" :use lambda-depth-when-nat-lists-<=-lemma
;;              :in-theory (disable lambda-depth-when-nat-lists-<=-lemma)))
;;     :rule-classes :linear
;;     :fn lambda-depth)

;;   (defret lambda-depth-list-when-nat-lists-<=
;;     (implies (nat-lists-<= vals1 vals2)
;;              (nat-lists-<= (lambda-depth-list x (pair-vars vars vals1))
;;                            (lambda-depth-list x (pair-vars vars vals2))))
;;     :hints (("goal" :use lambda-depth-list-when-nat-lists-<=-lemma
;;              :in-theory (disable lambda-depth-list-when-nat-lists-<=-lemma)))
;;     :fn lambda-depth-list)

;;   (local (defthm nat-lists-<=-of-cons
;;            (iff (nat-lists-<= (cons a b) (cons c d))
;;                 (and (<= (nfix a) (nfix c))
;;                      (nat-lists-<= b d)))
;;            :hints(("Goal" :in-theory (enable nat-lists-<=)))))

  

;;   (local (defthm assoc-of-append-alists
;;            (implies k
;;                     (equal (assoc k (append x y))
;;                            (or (assoc k x)
;;                                (assoc k y))))))

;;   (local (Defthm assoc-lower-bound-when-var-counts-alist-p
;;            (implies (var-counts-alist-p x)
;;                     (<= 0 (cdr (assoc k x))))
;;            :hints(("Goal" :in-theory (enable var-counts-alist-p)))))

;;   (defret-mutual lambda-depth-of-append-lower-bound
;;     (defret lambda-depth-of-append-lower-bound
;;       (<= (lambda-depth x var-counts-alist) (lambda-depth x (append var-counts-alist b)))
;;       :hints ('(:expand ((:free (a) (lambda-depth x a)))))
;;       :rule-classes :linear
;;       :fn lambda-depth)

;;     (defret lambda-depth-list-of-append-lower-bound
;;       (nat-lists-<= (lambda-depth-list x var-counts-alist) (lambda-depth-list x (append var-counts-alist b)))
;;       :hints ('(:expand ((:free (a) (lambda-depth-list x a)))))
;;       :fn lambda-depth-list)))

(defines lambda-measure
  (define lambda-measure ((x pseudo-termp)
                        (var-counts-alist var-counts-alist-p))
    :returns (depth natp :rule-classes :type-prescription)
    :measure (pseudo-term-count x)
    :verify-guards nil
    (pseudo-term-case x
      :const 0
      :var (or (cdr (assoc x.name (var-counts-alist-fix var-counts-alist)))
               0)
      :fncall (+ 1
                 (len x.args)
                 (sum-nat-list (lambda-measure-list x.args var-counts-alist)))
      :lambda (let ((lst (lambda-measure-list x.args var-counts-alist)))
                (+ 1
                   (lambda-measure x.body (pair-vars x.formals lst))
                   (len x.args)
                   (sum-nat-list lst)))))
  (define lambda-measure-list ((x pseudo-term-listp)
                             (var-counts-alist var-counts-alist-p))
    :returns (depths nat-listp)
    :measure (pseudo-term-list-count x)
    (if (atom x)
        nil
      (cons (lambda-measure (car x) var-counts-alist)
            (lambda-measure-list (cdr x) var-counts-alist))))
  ///

  (defthm len-of-lambda-measures-list
    (equal (len (lambda-measure-list x var-counts-alist))
           (len x))
    :hints(("Goal" :in-theory (enable len))))

  (verify-guards lambda-measure)

  (defun-sk lambda-measure-when-nat-lists-<=-cond (x)
    (forall (vars vals1 vals2)
            (implies (nat-lists-<= vals1 vals2)
                     (<= (lambda-measure x (pair-vars vars vals1)) (lambda-measure x (pair-vars vars vals2)))))
    :rewrite :direct)

  (defthm lambda-measure-when-nat-lists-<=-linear
    (implies (and (lambda-measure-when-nat-lists-<=-cond x)
                  (nat-lists-<= vals1 vals2))
             (<= (lambda-measure x (pair-vars vars vals1)) (lambda-measure x (pair-vars vars vals2))))
    :rule-classes :linear)

  (defun-sk lambda-measure-list-when-nat-lists-<=-cond (x)
    (forall (vars vals1 vals2)
            (implies (nat-lists-<= vals1 vals2)
                     (nat-lists-<= (lambda-measure-list x (pair-vars vars vals1))
                                   (lambda-measure-list x (pair-vars vars vals2)))))
    :rewrite :direct)
  
  (defthm lambda-measure-list-when-nat-lists-<=-cond-linear
    (implies (and (lambda-measure-list-when-nat-lists-<=-cond x)
                  (nat-lists-<= vals1 vals2))
             (<= (sum-nat-list (lambda-measure-list x (pair-vars vars vals1)))
                 (sum-nat-list (lambda-measure-list x (pair-vars vars vals2)))))
    :hints (("goal" :use ((:instance lambda-measure-list-when-nat-lists-<=-cond-necc))
             :in-theory (disable lambda-measure-list-when-nat-lists-<=-cond-necc)))
    :rule-classes :linear)

  (defthm lambda-measure-of-pair-lambda-measure-list-when-nat-lists-<=-cond
    (implies (and (lambda-measure-when-nat-lists-<=-cond x)
                  (lambda-measure-list-when-nat-lists-<=-cond args)
                  (nat-lists-<= vals1 vals2))
             (<= (lambda-measure x (pair-vars
                                  formals
                                  (lambda-measure-list args
                                                     (pair-vars vars vals1))))
                 (lambda-measure x (pair-vars
                                  formals
                                  (lambda-measure-list args
                                                     (pair-vars vars vals2))))))
    :hints (("goal" :use ((:instance lambda-measure-list-when-nat-lists-<=-cond-necc
                           (x args)))
             :in-theory (disable lambda-measure-list-when-nat-lists-<=-cond-necc)))
    :rule-classes :linear)

  (local (in-theory (disable lambda-measure-when-nat-lists-<=-cond
                             lambda-measure-list-when-nat-lists-<=-cond)))

  (defthm assoc-of-pair-vars-when-nat-lists-<=
    (implies (nat-lists-<= vals1 vals2)
             (<= (cdr (assoc key (var-counts-alist-fix (pair-vars vars vals1))))
                 (cdr (assoc key (var-counts-alist-fix (pair-vars vars vals2))))))
    :hints (("Goal" :in-theory (enable nat-lists-<= pair-vars var-counts-alist-fix))))

  (defthm cdr-assoc-under-iff-when-depth-alist-p
    (implies (var-counts-alist-p x)
             (iff (cdr (assoc k x))
                  (assoc k x)))
    :hints(("Goal" :in-theory (enable var-counts-alist-p))))

  (defthm assoc-under-iff-of-var-counts-alist-fix
    (iff (assoc k (var-counts-alist-fix x))
         (and (pseudo-var-p k)
              (assoc k x)))
    :hints(("Goal" :in-theory (enable var-counts-alist-fix))))

  (defthm assoc-of-pairlis$-under-iff
    (iff (assoc k (pairlis$ keys vals))
         (member k keys)))

  (defret-mutual lambda-measure-when-nat-lists-<=-lemma
    (defret lambda-measure-when-nat-lists-<=-lemma
      (lambda-measure-when-nat-lists-<=-cond x)
      :hints ('(:expand ((lambda-measure-when-nat-lists-<=-cond x)
                         (:free (a) (lambda-measure x a)))))
      :fn lambda-measure)

    (defret lambda-measure-list-when-nat-lists-<=-lemma
      (lambda-measure-list-when-nat-lists-<=-cond x)
      :hints ('(:expand ((lambda-measure-list-when-nat-lists-<=-cond x)
                         (:free (a) (lambda-measure-list x a))
                         (:free (a b c d) (nat-lists-<= (cons a b) (cons c d)))
                         (nat-lists-<= nil nil))))
      :fn lambda-measure-list))

  (defret lambda-measure-when-nat-lists-<=
    (implies (nat-lists-<= vals1 vals2)
             (<= (lambda-measure x (pair-vars vars vals1)) (lambda-measure x (pair-vars vars vals2))))
    :hints (("goal" :use lambda-measure-when-nat-lists-<=-lemma
             :in-theory (disable lambda-measure-when-nat-lists-<=-lemma)))
    :rule-classes :linear
    :fn lambda-measure)

  (defret lambda-measure-list-when-nat-lists-<=
    (implies (nat-lists-<= vals1 vals2)
             (nat-lists-<= (lambda-measure-list x (pair-vars vars vals1))
                           (lambda-measure-list x (pair-vars vars vals2))))
    :hints (("goal" :use lambda-measure-list-when-nat-lists-<=-lemma
             :in-theory (disable lambda-measure-list-when-nat-lists-<=-lemma)))
    :fn lambda-measure-list)

  (local (defthm nat-lists-<=-of-cons
           (iff (nat-lists-<= (cons a b) (cons c d))
                (and (<= (nfix a) (nfix c))
                     (nat-lists-<= b d)))
           :hints(("Goal" :in-theory (enable nat-lists-<=)))))

  

  (local (defthm assoc-of-append-alists
           (implies k
                    (equal (assoc k (append x y))
                           (or (assoc k x)
                               (assoc k y))))))

  (local (Defthm assoc-lower-bound-when-var-counts-alist-p
           (implies (var-counts-alist-p x)
                    (<= 0 (cdr (assoc k x))))
           :hints(("Goal" :in-theory (enable var-counts-alist-p)))))

  (defret-mutual lambda-measure-of-append-lower-bound
    (defret lambda-measure-of-append-lower-bound
      (<= (lambda-measure x var-counts-alist) (lambda-measure x (append var-counts-alist b)))
      :hints ('(:expand ((:free (a) (lambda-measure x a)))))
      :rule-classes :linear
      :fn lambda-measure)

    (defret lambda-measure-list-of-append-lower-bound
      (nat-lists-<= (lambda-measure-list x var-counts-alist) (lambda-measure-list x (append var-counts-alist b)))
      :hints ('(:expand ((:free (a) (lambda-measure-list x a)))))
      :fn lambda-measure-list)))

(local (defthm pseudo-termp-of-lookup-in-pseudo-term-subst
         (implies (pseudo-term-subst-p x)
                  (pseudo-termp (cdr (assoc k x))))))

(local (defthm var-counts-alist-p-of-pairlis$
         (implies (and (equal (len x) (len y))
                       (pseudo-var-list-p x)
                       (nat-listp y))
                  (var-counts-alist-p (pairlis$ x y)))))


(defsection term-subst
  
  (local (defthm symbol-listp-when-pseudo-var-listp
           (implies (pseudo-var-list-p x)
                    (symbol-listp x))))
  (local (defthm pseudo-var-list-p-strip-cars-when-pseudo-term-subst
           (implies (pseudo-term-subst-p x)
                    (pseudo-var-list-p (strip-cars x)))))
  (local (defthm len-of-strip-cdrs
           (equal (len (strip-cdrs x))
                  (len (strip-cars x)))))

  (local (defthm lookup-in-pair-lambda-measures
           (implies k
                    (equal (ASSOC k (PAIRLIS$ (STRIP-CARS x)
                                              (LAMBDA-MEASURE-LIST (STRIP-CDRS x)
                                                                 ALIST)))
                           (and (assoc k x)
                                (cons k (lambda-measure (cdr (assoc k x)) alist)))))
           :hints(("Goal" :in-theory (enable lambda-measure-list)))))

  (local (include-book "std/lists/take" :dir :system))

  (local (defthm assoc-of-append-alists
           (implies k
                    (equal (assoc k (append x y))
                           (or (assoc k x)
                               (assoc k y))))))

  (defret-mutual lambda-measure-of-term-subst
    (defret  lambda-measure-of-term-subst
      (equal (lambda-measure (term-subst x a) alist)
             (lambda-measure x (append (pairlis$ (strip-cars (pseudo-term-subst-fix a))
                                               (lambda-measure-list (strip-cdrs (pseudo-term-subst-fix a)) alist))
                                     alist)))
      :hints ('(:expand ((term-subst x a)
                         (:free (alist) (lambda-measure x alist))
                         (:free (formals body args) (lambda-measure (pseudo-term-lambda formals body args) alist))
                         (:free (fn args) (lambda-measure (pseudo-term-fncall fn args) alist)))
                :in-theory (enable lambda-measure)
                :cases ((pseudo-term-case x :lambda))))
      :fn term-subst)
    (defret  lambda-measure-list-of-term-subst-list
      (equal (lambda-measure-list (termlist-subst x a) alist)
             (lambda-measure-list x (append (pairlis$ (strip-cars (pseudo-term-subst-fix a))
                                                    (lambda-measure-list (strip-cdrs (pseudo-term-subst-fix a)) alist))
                                          alist)))
      :hints ('(:expand ((termlist-subst x a)
                         (:free (alist) (lambda-measure-list x alist)))
                :in-theory (enable lambda-measure-list)))
      :fn termlist-subst)
    :mutual-recursion term-subst))

(defsection term-subst-strict

  
  (local (defthm symbol-listp-when-pseudo-var-listp
           (implies (pseudo-var-list-p x)
                    (symbol-listp x))))
  (local (defthm pseudo-var-list-p-strip-cars-when-pseudo-term-subst
           (implies (pseudo-term-subst-p x)
                    (pseudo-var-list-p (strip-cars x)))))
  (local (defthm len-of-strip-cdrs
           (equal (len (strip-cdrs x))
                  (len (strip-cars x)))))

  (local (defthm lookup-in-pair-lambda-measures
           (implies k
                    (equal (ASSOC k (PAIRLIS$ (STRIP-CARS x)
                                              (LAMBDA-MEASURE-LIST (STRIP-CDRS x)
                                                                   ALIST)))
                           (and (assoc k x)
                                (cons k (lambda-measure (cdr (assoc k x)) alist)))))
           :hints(("Goal" :in-theory (enable lambda-measure-list)))))

  (local (include-book "std/lists/take" :dir :system))

  (local (defthm assoc-of-append-alists
           (implies k
                    (equal (assoc k (append x y))
                           (or (assoc k x)
                               (assoc k y))))))

  (defret-mutual lambda-measure-of-term-subst-strict
    (defret  lambda-measure-of-term-subst-strict
      (equal (lambda-measure (term-subst-strict x a) alist)
             (lambda-measure x (pairlis$ (strip-cars (pseudo-term-subst-fix a))
                                         (lambda-measure-list (strip-cdrs (pseudo-term-subst-fix a)) alist))))
      :hints ('(:expand ((term-subst-strict x a)
                         (:free (alist) (lambda-measure x alist))
                         (:free (formals body args) (lambda-measure (pseudo-term-lambda formals body args) alist))
                         (:free (fn args) (lambda-measure (pseudo-term-fncall fn args) alist)))
                :in-theory (enable lambda-measure)
                :cases ((pseudo-term-case x :lambda))))
      :fn term-subst-strict)
    (defret  lambda-measure-list-of-termlist-subst-strict
      (equal (lambda-measure-list (termlist-subst-strict x a) alist)
             (lambda-measure-list x (pairlis$ (strip-cars (pseudo-term-subst-fix a))
                                              (lambda-measure-list (strip-cdrs (pseudo-term-subst-fix a)) alist))))
      :hints ('(:expand ((termlist-subst-strict x a)
                         (:free (alist) (lambda-measure-list x alist)))
                :in-theory (enable lambda-measure-list)))
      :fn termlist-subst-strict)
    :mutual-recursion term-subst-strict))
;; (local (defthm pseudo-term-subst-p-of-pair-vars
;;          (implies (And (equal (len x) (len y))
;;                        (pseudo-term-listp y))
;;                   (pseudo-term-subst-p (pair-vars x y)))
;;          :hints(("Goal" :in-theory (enable pair-vars)))))


(local (defthm pair-lambda-measure-list-lemma
         (implies (equal (len formals) (len args))
                  (equal 
                   (PAIRLIS$
                    (STRIP-CARS (PAIR-VARS formals args))
                    (LAMBDA-MEASURE-LIST
                     (STRIP-CDRS (PAIR-VARS formals args)) ALIST))
                   (pair-vars formals (lambda-measure-list args alist))))
         :hints(("Goal" :in-theory (enable pair-vars lambda-measure-list)))))



(defthm lambda-measure-of-term-subst-strict-decr
  (implies (pseudo-term-case x :lambda)
           (< (b* (((pseudo-term-lambda x)))
                (lambda-measure (term-subst-strict x.body (pair-vars x.formals x.args)) alist))
              (lambda-measure x alist)))
  :hints (("goal" :expand ((lambda-measure x alist)))))

(local (defthm base-ev-alist-of-pair-vars
         (equal (base-ev-alist (pair-vars vars vals) env)
                (pair-vars vars (base-ev-list vals env)))
         :hints(("Goal" :in-theory (enable base-ev-alist pair-vars)))))

(defines lazy-beta-reduce
  (define lazy-beta-reduce ((x pseudo-termp))
    :measure (lambda-measure x nil)
    :returns (new-x pseudo-termp)
    (pseudo-term-case x
      :const (pseudo-term-fix x)
      :var (pseudo-term-fix x)
      :fncall (pseudo-term-fncall x.fn (lazy-beta-reduce-list x.args))
      :lambda (lazy-beta-reduce (term-subst-strict x.body (pair-vars x.formals x.args)))))
  (define lazy-beta-reduce-list ((x pseudo-term-listp))
    :measure (+ (len x) (sum-nat-list (lambda-measure-list x nil)))
    :hints(("Goal" :expand ((lambda-measure x nil)
                            (lambda-measure-list x nil))
            :in-theory (enable sum-nat-list)))
    :returns (new-x pseudo-term-listp)
    :verify-guards nil
    (if (atom x)
        nil
      (cons (lazy-beta-reduce (car x))
            (lazy-beta-reduce-list (cdr x)))))
  ///
  (verify-guards lazy-beta-reduce)

  (defret-mutual base-ev-of-<fn>
    (defret base-ev-of-<fn>
      (equal (base-ev new-x a) (base-ev x a))
      :hints ('(:expand (<call>)
                :in-theory (enable acl2::base-ev-of-fncall-args)))
      :fn lazy-beta-reduce)
    (defret base-ev-list-of-<fn>
      (equal (base-ev-list new-x a) (base-ev-list x a))
      :hints ('(:expand (<call>)))
      :fn lazy-beta-reduce-list))

  (defret-mutual <fn>-not-lambda
    (defret <fn>-not-lambda
      (not (pseudo-term-case new-x :lambda))
      :hints ('(:expand (<call>)))
      :fn lazy-beta-reduce)
    :skip-others t))



                                     
