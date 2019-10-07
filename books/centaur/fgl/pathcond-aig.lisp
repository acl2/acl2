; FGL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2008-2013 Centaur Technology
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
 
(in-package "FGL")

(include-book "aig-pathcond-stobj")
(include-book "std/basic/arith-equiv-defs" :dir :system)
(local (include-book "theory"))
(local (std::add-default-post-define-hook :fix))



(local (in-theory (disable ;; equal-of-booleans-rewrite
                           acl2::consp-of-car-when-alistp
                           set::double-containment
                           acl2::aig-eval
                           ;;acl2::consp-under-iff-when-true-listp
                           default-car default-cdr)))


(local (defthm bitp-lookup-when-calistp
         (implies (and (calistp x)
                       (hons-assoc-equal k x))
                  (bitp (cdr (hons-assoc-equal k x))))
         :hints(("Goal" :in-theory (e/d (calistp) (bitp))))))

(local (defthm maybe-bitp-lookup-when-calistp
         (implies (calistp x)
                  (acl2::maybe-bitp (cdr (hons-assoc-equal k x))))
         :hints(("Goal" :cases ((hons-assoc-equal k x))))))

(local (defthm cdr-hons-assoc-equal-when-calistp
         (implies (calistp x)
                  (iff (cdr (hons-assoc-equal k x))
                       (hons-assoc-equal k x)))
         :hints(("Goal" :in-theory (enable calistp)))))


(defthm alistp-when-calistp
  (implies (calistp x)
           (alistp x))
  :hints(("Goal" :in-theory (enable calistp)))
  :rule-classes :forward-chaining)

(local (defthm consp-car-when-alistp
         (implies (alistp x)
                  (equal (consp (car x))
                         (consp x)))))

(local (defthm consp-car-calist-fix
         (equal (consp (car (calist-fix x)))
                (consp (calist-fix x)))
         :hints (("goal" :use ((:instance alistp-when-calistp
                                (x (calist-fix x))))
                  :in-theory (disable alistp-when-calistp)))))

(local (defthm cdr-car-calist-fix
         (iff (cdr (car (calist-fix x)))
              (consp (calist-fix x)))
         :hints(("Goal" :in-theory (e/d (calistp)
                                        (calistp-of-calist-fix))
                 :use ((:instance calistp-of-calist-fix))))))

(local (defthm bitp-cdr-car-of-calist-fix
         (equal (bitp (cdr (car (calist-fix x))))
                (consp (calist-fix x)))
         :hints(("Goal" :in-theory (e/d (calistp)
                                        (calistp-of-calist-fix))
                 :expand ((calistp (calist-fix x)))
                 :use ((:instance calistp-of-calist-fix))))))



(defsection calist-lookup
  (local (in-theory (enable calist-lookup)))
  (local (std::set-define-current-function calist-lookup))

  (local (defthm calist-fix-of-cons-tmp
         (equal (calist-fix (cons pair calist))
                (if (and (consp pair)
                         (not (hons-assoc-equal (car pair) (calist-fix calist))))
                    (cons (cons (car pair)
                                (bfix (cdr pair)))
                          (calist-fix calist))
                  (calist-fix calist)))
         :hints(("Goal" :in-theory (enable calist-fix)))))

  (defthm calist-lookup-of-cons
    (equal (calist-lookup k1 (cons pair calist))
           (if (or (atom pair)
                   (not (equal k1 (car pair)))
                   (calist-lookup (car pair) calist))
               (calist-lookup k1 calist)
             (bfix (cdr pair)))))

  (defthm calist-fix-of-cons
    (equal (calist-fix (cons pair calist))
           (if (and (consp pair)
                    (not (calist-lookup (car pair) calist)))
               (cons (cons (car pair)
                           (bfix (cdr pair)))
                     (calist-fix calist))
             (calist-fix calist))))

  (defthm calist-lookup-of-nil
    (equal (calist-lookup k nil) nil))

  (defthm calist-lookup-of-atom
    (implies (atom x)
             (equal (calist-lookup k x) nil))
    :hints(("Goal" :in-theory (enable calist-fix)))
    :rule-classes ((:rewrite :backchain-limit-lst 0)))

  (defthmd calist-lookup-redef
    (equal (calist-lookup k x)
           (b* ((x (calist-fix x))
                ((unless (consp x)) nil)
                ((when (equal k (caar x))) (cdar x)))
             (calist-lookup k (cdr x))))
    :hints(("Goal" :expand ((hons-assoc-equal k (calist-fix x)))))
    :rule-classes :definition)

  (defthm calist-lookup-in-cdr-when-car
    (implies (and (calistp x)
                  (consp x)
                  (equal k (caar x)))
             (not (calist-lookup k (cdr x))))
    :hints(("Goal" :in-theory (enable calist-lookup calistp))))

  (defret bitp-of-calist-lookup
    (iff (bitp res) res))

  (defthm calistp-of-cons-when-not-calist-lookup
    (implies (and (calistp x)
                  (consp pair)
                  (bitp (cdr pair))
                  (not (calist-lookup (car pair) x)))
             (calistp (cons pair x))))

  (fty::deffixequiv calist-lookup))





(define calist-eval ((calist calistp) (env))
  :returns (ok)
  :measure (len (calist-fix calist))
  (b* ((calist (calist-fix calist)))
    (if (atom calist)
        t
      (and (eql (bool->bit (acl2::aig-eval (caar calist) env))
                (lbfix (cdar calist)))
           (calist-eval (cdr calist) env))))
  ///
  (defthm calist-eval-of-cons
    (equal (calist-eval (cons pair calist) env)
           (and (or (not (consp pair))
                    (calist-lookup (car pair) calist)
                    (equal (bool->bit (acl2::aig-eval (car pair) env))
                           (bfix (cdr pair))))
                (calist-eval calist env)))
    :hints(("Goal" :expand ((calist-eval (cons pair calist) env)))))

  (defthm calist-eval-of-nil
    (equal (calist-eval nil env) t))

  (defthm calist-eval-implies-lookup
    (implies (and (calist-eval calist env)
                  (calist-lookup aig calist))
             (equal (calist-lookup aig calist)
                    (bool->bit (acl2::aig-eval aig env))))
    :hints(("Goal" :in-theory (enable calist-lookup-redef))))

  (defthm calist-eval-implies-lookup-not-equal-negated-eval
    (implies (and (syntaxp (Quotep b))
                  (calist-eval calist env)
                  (equal b (b-not (bool->bit (acl2::aig-eval aig env)))))
             (not (equal (calist-lookup aig calist) b)))
    :hints(("Goal" :use calist-eval-implies-lookup
            :in-theory (disable calist-eval-implies-lookup)))))

(define calist-eval-badguy ((calist calistp) env)
  :returns (bad-aig)
  :measure (len (calist-fix calist))
  (b* ((calist (calist-fix calist))
       ((when (atom calist)) nil)
       ((when (eql (bool->bit (acl2::aig-eval (caar calist) env))
                   (lbfix (cdar calist))))
        (calist-eval-badguy (cdr calist) env)))
    (caar calist))
  ///
  (local (defthm equal-1-when-bitp
           (implies (and (bitp x)
                         (not (equal x 0)))
                    (equal (equal x 1) t))))

  (defthm calist-eval-badguy-correct
    (implies (not (calist-eval calist env))
             (b* ((aig (calist-eval-badguy calist env))
                  (look (calist-lookup aig calist)))
               (and look
                    (equal look (b-not (bool->bit (acl2::aig-eval aig env)))))))
    :hints(("Goal" :in-theory (enable calist-lookup-redef
                                      calist-eval)
            :induct t))))
               




(define calist-extension-p ((x calistp) (y calistp))
  :measure (len (calist-fix x))
  (b* ((x (calist-fix x)))
    (or (equal x (calist-fix y))
        (and (consp x)
             (calist-extension-p (cdr x) y))))
  ///
  (defthm calist-extension-of-cons
    (calist-extension-p (cons pair x) x)
    :hints (("goal" :expand ((calist-extension-p (cons pair x) x)))))

  (defthm calist-extension-transitive
    (implies (and (calist-extension-p x y)
                  (calist-extension-p y z))
             (calist-extension-p x z)))

  (defthm calist-lookup-in-extension
    (implies (and (calist-extension-p x y)
                  (calist-lookup k y))
             (equal (calist-lookup k x)
                    (calist-lookup k y)))
    :hints (("goal" :induct t)
            (and stable-under-simplificationp
                 '(:in-theory (enable calist-lookup-redef)))))

  (defthm calist-extension-implies-len-gte
    (implies (calist-extension-p x y)
             (>= (len (calist-fix x)) (len (calist-fix y))))
    :rule-classes (:rewrite :linear))

  (defthm calist-extension-p-self
    (calist-extension-p x x)))


;; (define rewind-calist ((marker aig-p) (x calistp))
;;   :measure (len (calist-fix x))
;;   :returns (new-x calistp)
;;   :guard (calist-lookup marker x)
;;   :guard-hints (("goal" :in-theory (enable calist-lookup calistp)))
;;   (b* ((x (calist-fix x))
;;        ((unless (mbt (consp x))) nil)
;;        (first (caar x))
;;        (x (acl2::fast-alist-pop x))
;;        ((when (hons-equal first (aig-fix marker))) x))
;;     (rewind-calist marker x))
;;   ///

;;   (defthm rewind-calist-of-extension
;;     (implies (and (calist-extension-p y (cons (cons aig val) x))
;;                   (not (calist-lookup aig x)))
;;              (equal (rewind-calist aig y) (calist-fix x)))
;;     :hints(("Goal" :in-theory (enable calist-extension-p)
;;             :induct t)
;;            (and stable-under-simplificationp
;;                 '(:use ((:instance calist-lookup-in-extension
;;                          (x (cdr (calist-fix y)))
;;                          (y (cons (cons aig val) x))
;;                          (k aig)))
;;                   :in-theory (disable calist-lookup-in-extension))))))

(define calist-stobj-fix (calist-stobj)
  :enabled t
  (mbe :logic (non-exec (calist-fix calist-stobj))
       :exec calist-stobj))


(fty::deffixtype calist-stobj :pred calistp :fix calist-fix :equiv calist-equiv)

(define rewind-calist ((n natp) calist-stobj)
  :measure (len (calist-fix calist-stobj))
  :returns (new-calist calistp)
  :guard (<= n (calist-stobj-len calist-stobj))
  ;; :guard-hints (("goal" :in-theory (enable calist-lookup calistp)))
  ;; :guard-debug t
  (b* ((calist-stobj (calist-stobj-fix calist-stobj))
       ((when (mbe :logic (<= (calist-stobj-len calist-stobj) (nfix n))
                   :exec (eql n (calist-stobj-len calist-stobj))))
        calist-stobj)
       (calist-stobj (calist-stobj-pop calist-stobj)))
    (rewind-calist n calist-stobj))
  ///

  (local (defthm rewind-calist-of-extension-lemma
           (implies (calist-extension-p y x)
                    (equal (rewind-calist (len (calist-fix x))
                                          y)
                           (calist-fix x)))
           :hints(("Goal" :in-theory (enable calist-extension-p)
                   :induct t)
                  (and stable-under-simplificationp
                       '(:use ((:instance calist-lookup-in-extension
                                (x (cdr (calist-fix y)))
                                (y (cons (cons aig val) x))
                                (k aig)))
                         :in-theory (disable calist-lookup-in-extension))))
           :rule-classes nil))

  (fty::deffixequiv rewind-calist)

  (defthm rewind-calist-of-extension
    (implies (and (calist-extension-p y x)
                  (equal (nfix n) (len (calist-fix x))))
             (equal (rewind-calist n y) (calist-fix x)))
    :hints (("goal" :use rewind-calist-of-extension-lemma))))
  

(define calist-depends-on ((v natp) (x calistp))
  :measure (len (calist-fix x))
  (b* ((x (calist-fix x))
       ((when (atom x)) nil))
    (or (set::in (lnfix v) (acl2::aig-vars (caar x)))
        (calist-depends-on v (cdr x))))
  ///
  (local (defthm aig-eval-of-cons-env-when-not-member-aig-vars
           (implies (not (set::in v (acl2::aig-vars x)))
                    (equal (acl2::aig-eval x (cons (cons v val) env))
                           (acl2::aig-eval x env)))
           :hints(("Goal" :in-theory (enable acl2::aig-eval acl2::aig-vars)))))

  (defthm calist-eval-of-set-var-when-not-depends-on
    (implies (not (calist-depends-on v x))
             (equal (calist-eval x (cons (cons (nfix v) val) env))
                    (calist-eval x env)))
    :hints(("Goal" :in-theory (enable calist-eval))))

  (defthm calist-eval-of-set-var-when-not-depends-on-natp
    (implies (and (not (calist-depends-on v x))
                  (natp v))
             (equal (calist-eval x (cons (cons v val) env))
                    (calist-eval x env)))
    :hints(("Goal" :in-theory (enable calist-eval)))))

(define aig-norm (x)
  :returns (mv (abs)
               (negp booleanp :rule-classes :type-prescription))
  :measure (acl2-count x)
  (b* (((when (booleanp x)) (mv nil x))
       ((when (atom x)) (mv x nil))
       ((when (eq (cdr x) nil)) (b* (((mv abs neg) (aig-norm (car x))))
                                  (mv abs (not neg)))))
    (mv x nil))
  ///
  (defret aig-eval-of-aig-norm
    (equal (acl2::aig-eval abs env)
           (xor negp (acl2::aig-eval x env)))
    :hints(("Goal" :in-theory (enable acl2::aig-eval))))

  (defret acl2-count-of-<fn>
    (<= (acl2-count abs) (acl2-count x))
    :rule-classes ((:linear :trigger-terms ((acl2-count abs)))))

  (defret cdr-not-nil-of-aig-norm
    (implies (consp abs)
             (cdr abs)))

  (defret member-vars-of-aig-norm
    (implies (not (set::in v (acl2::aig-vars x)))
             (not (set::in v (acl2::aig-vars abs)))))

  (defret aig-p-of-aig-norm
    (implies (aig-p x bound)
             (aig-p abs bound))
    :hints(("Goal" :in-theory (enable aig-p)))))
       

;; Note: This is a less expensive version that stops when it gets to a
;; negation.  For now we'll try the full-fledged walk through the AIG with
;; memoization.  Might turn out to be too expensive to do at every IF test.
;; (define calist-implies-aux ((x aig-p) (calist calistp))
;;   :returns (res acl2::maybe-bitp :rule-classes :type-prescription)
;;   :measure (acl2-count (aig-fix x))
;;   (b* (((mv abs neg) (aig-norm x))
;;        ((when (booleanp abs)) (b-xor (bool->bit abs) (bool->bit neg)))
;;        (look (calist-lookup abs calist))
;;        ((when look) (b-xor look (bool->bit neg)))
;;        ((when (atom abs)) nil)
;;        ((when neg) nil)
;;        (car (calist-implies-aux (car abs) calist))
;;        ((when (eql car 0)) 0)
;;        (cdr (calist-implies-aux (cdr abs) calist))
;;        ((when (eql cdr 0)) 0)
;;        ((when (and car cdr)) 1))
;;     nil)
;;   ///
;;   (defret eval-when-calist-implies-aux
;;     (implies (and (calist-eval calist env)
;;                   res)
;;              (equal res (bool->bit (acl2::aig-eval (aig-fix x) env))))
;;     :hints(("Goal" :induct t)
;;            (and stable-under-simplificationp
;;                 '(:use ((:instance aig-eval-of-aig-norm))
;;                   :in-theory (e/d (acl2::aig-eval)
;;                                   (aig-eval-of-aig-norm)))))))

;; (define calist-implies ((x aig-p) (calist calistp))
;;   :returns (res acl2::maybe-bitp :rule-classes :type-prescription)
;;   (b* (((mv abs neg) (aig-norm x))
;;        (aux (calist-implies-aux abs calist)))
;;     (and aux (b-xor (bool->bit neg) aux)))
;;   ///
;;   (defret eval-when-calist-implies
;;     (implies (and (calist-eval calist env)
;;                   res)
;;              (equal res (bool->bit (acl2::aig-eval (aig-fix x) env))))))

(local (defthm aig-atom-p-when-consp
         (implies (aig-p x bound)
                  (iff (acl2::aig-atom-p x)
                       (atom x)))
         :hints(("Goal" :in-theory (enable aig-p acl2::aig-atom-p)))))


(define calist-implies (x (calist calistp))
  :returns (res acl2::maybe-bitp :rule-classes :type-prescription)
  :measure (acl2-count x)
  (b* (((mv abs neg) (aig-norm x))
       ((when (booleanp abs)) (b-xor (bool->bit abs) (bool->bit neg)))
       (look (calist-lookup abs calist))
       ((when look) (b-xor look (bool->bit neg)))
       ((when (acl2::aig-atom-p abs)) nil)
       (car (calist-implies (car abs) calist))
       ((when (eql car 0)) (bool->bit neg))
       (cdr (calist-implies (cdr abs) calist))
       ((when (eql cdr 0)) (bool->bit neg))
       ((when (and car cdr)) (b-not (bool->bit neg))))
    nil)
  ///
  (local (in-theory (disable acl2::aig-env-lookup)))
  (defret eval-when-calist-implies
    (implies (and (calist-eval calist env)
                  res)
             (equal res (bool->bit (acl2::aig-eval x env))))
    :hints(("Goal" :induct t)
           (and stable-under-simplificationp
                '(:use ((:instance aig-eval-of-aig-norm))
                  :in-theory (e/d (acl2::aig-eval)
                                  (aig-eval-of-aig-norm))))))

  (memoize 'calist-implies))


(define calist-assume (x (calist-stobj))
  :returns (mv contradictionp (new-calist calistp))
  :measure (acl2-count x)
  :verify-guards nil
  (b* (((mv abs neg) (aig-norm x))
       (calist-stobj (calist-stobj-fix calist-stobj))
       (look (calist-lookup abs (calist-stobj-access calist-stobj)))
       ((when look)
        (mv (eql look (bool->bit neg)) calist-stobj))
       ((when (booleanp abs))
        (mv (eq abs neg) calist-stobj))
       ((when (or neg (acl2::aig-atom-p abs)))
        (b* ((calist-stobj (calist-stobj-acons abs (b-not (bool->bit neg)) calist-stobj)))
          (mv nil calist-stobj)))
       ((mv contradictionp calist-stobj) (calist-assume (car abs) calist-stobj))
       ((when contradictionp) (mv contradictionp calist-stobj)))
    (calist-assume (cdr abs) calist-stobj))
  ///
  (verify-guards calist-assume)

  (defret calist-assume-correct
    (implies (and (calist-eval calist-stobj env)
                  (acl2::aig-eval x env))
             (and (not contradictionp)
                  (calist-eval new-calist env)))
    :hints(("Goal" :induct t)
           (and stable-under-simplificationp
                '(:use ((:instance aig-eval-of-aig-norm))
                  :in-theory (e/d (acl2::aig-eval)
                                  (aig-eval-of-aig-norm))))))

  (defret calist-assume-eval-new-calist
    (implies (not contradictionp)
             (equal (calist-eval new-calist env)
                    (and (calist-eval calist-stobj env)
                         (acl2::aig-eval x env))))
    :hints(("Goal" :induct t)
           (and stable-under-simplificationp
                '(:use ((:instance aig-eval-of-aig-norm))
                  :in-theory (e/d (acl2::aig-eval)
                                  (aig-eval-of-aig-norm))))))

  (defret calist-assume-contradictionp-correct
    (implies (and contradictionp
                  (acl2::aig-eval x env))
             (not (calist-eval calist-stobj env))))

  (defret calist-extension-p-of-calist-assume
    (calist-extension-p new-calist calist-stobj))

  (local (include-book "tools/trivial-ancestors-check" :dir :system))
  (local (acl2::use-trivial-ancestors-check))

  (local (in-theory (disable acl2::aig-vars set::in-tail)))

  (local (defthm aig-vars-of-car/cdr
           (implies (and (not (set::in v (acl2::aig-vars x)))
                         (not (acl2::aig-atom-p x)))
                    (and (not (set::in v (acl2::aig-vars (car x))))
                         (not (set::in v (acl2::aig-vars (cdr x))))))
           :hints (("goal" :expand ((acl2::aig-vars x))))))


  (defret calist-depends-on-of-calist-assume
    (implies (and (not (calist-depends-on v calist-stobj))
                  (not (set::in (nfix v) (acl2::aig-vars x))))
             (not (calist-depends-on v new-calist)))
    :hints (("goal" :induct <call>
             :expand (<call>))
            (and stable-under-simplificationp
                 '(:expand ((:free (a b) (calist-depends-on v (cons a b)))))))))

