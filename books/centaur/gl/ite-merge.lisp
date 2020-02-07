; GL - A Symbolic Simulation Framework for ACL2
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

(in-package "GL")
(include-book "general-objects")
(include-book "symbolic-arithmetic")
(include-book "hyp-fix")
(include-book "split-args")
(include-book "std/basic/two-nats-measure" :dir :system)
(include-book "tools/mv-nth" :dir :system)
(local (include-book "bfr-reasoning"))
;; (local (include-book "misc/invariants" :dir :system))
(local (include-book "general-object-thms"))
(local (include-book "hyp-fix"))

(verify-guards
 general-concrete-obj
 :hints
 (("goal" :in-theory (enable general-concrete-gobject-car-and-cdr))))

(memoize 'general-concrete-obj :condition
         '(and (consp x) (not (or (g-concrete-p x) (concrete-gobjectp x)))))


(defn merge-general-integers (c x y)
  (declare (xargs :guard (and (general-integerp x)
                              (general-integerp y))))
  (b* ((xbits (general-integer-bits x))
       (ybits (general-integer-bits y)))
    (mk-g-integer (bfr-ite-bss-fn c (acl2::list-fix xbits) (acl2::list-fix ybits)))))

(defthm gobj-depends-on-of-merge-general-integers
  (implies (and (not (pbfr-depends-on k p c))
                (not (gobj-depends-on k p x))
                (not (gobj-depends-on k p y))
                (general-integerp x)
                (general-integerp y))
           (not (gobj-depends-on k p (merge-general-integers c x y))))
  :hints(("Goal" :in-theory (enable merge-general-integers
                                    gobj-depends-on))))

(in-theory (disable merge-general-integers))






(defun merge-general-booleans (c a b)
  (declare (xargs :guard (and (general-booleanp a)
                              (general-booleanp b))))
  (let* ((av (general-boolean-value a))
         (bv (general-boolean-value b))
         (val (bfr-ite c av bv)))
    (mk-g-boolean val)))

(defthm gobj-depends-on-of-merge-general-booleans
  (implies (and (not (pbfr-depends-on k p c))
                (not (gobj-depends-on k p x))
                (not (gobj-depends-on k p y))
                (general-booleanp x)
                (general-booleanp y))
           (not (gobj-depends-on k p (merge-general-booleans c x y))))
  :hints(("Goal" :in-theory (enable merge-general-booleans
                                    gobj-depends-on))))

(in-theory (disable merge-general-booleans))




(defun hlexorder (x y)
  (declare (xargs :guard t))
  (cond ((atom x)
         (if (atom y) (alphorder x y) t))
        ((atom y) nil)
        ((hqual (car x) (car y))
         (hlexorder (cdr x) (cdr y)))
        (t (hlexorder (car x) (car y)))))


(defun ite-merge-ordering (x y)
  (declare (xargs :guard t
                  :guard-hints (("goal" :in-theory (e/d (general-booleanp
                                                         general-integerp
                                                         general-concrete-atom
                                                         general-concrete-atom-val
                                                         general-consp)
                                                        ((force)))))))
  (cond ((hqual x y) 'equal)
        ((general-booleanp x)
         (if (general-booleanp y)
             'booleans
           '<))
        ((general-booleanp y) '>)
        ((general-integerp x)
         (if (general-integerp y)
             'integers
           '<))
        ((general-integerp y) '>)
        ((general-concrete-atom x)
         (if (general-concrete-atom y)
             (if (alphorder (general-concrete-atom-val x)
                            (general-concrete-atom-val y)) '< '>)
           '<))
        ((general-concrete-atom y) '>)
        ((general-consp x)
         (if (general-consp y)
             'conses
           '<))
        ((general-consp y) '>)
        ((eq (tag x) :g-var)
         (if (eq (tag y) :g-var)
             (if (hlexorder (g-var->name x) (g-var->name y)) '< '>)
           '<))
        ((eq (tag y) :g-var) '>)
        ((eq (tag x) :g-apply)
         (if (eq (tag y) :g-apply)
             (if (equal (g-apply->fn x) (g-apply->fn y))
                 (if (equal (len (g-apply->args x))
                            (len (g-apply->args y)))
                     'applies
                   (if (< (len (g-apply->args x))
                          (len (g-apply->args y)))
                       '<
                     '>))
               (if (hlexorder (cdr x) (cdr y)) '< '>))
           '<))
        ((eq (tag y) :g-apply) '>)
        (t ;; Both :g-ites
         (if (hlexorder (cdr x) (cdr y)) '< '>))))


(in-theory (disable ite-merge-ordering))




;; (defn merge-rest-guard (c hyp)
;;   (and (not (fh c)) (not (th c))))


(defn ite-merge-measure (x y)
  (two-nats-measure
   (+ 1 (acl2-count x) (acl2-count y))
   1))

(defn maybe-merge-measure (x y)
  (two-nats-measure
   (+ 1 (acl2-count x) (acl2-count y))
   0))

(defn merge-rest-measure (x y)
  (two-nats-measure
   (+ 1
      (acl2-count x)
      (acl2-count y))
   2))

(defun breakdown-ite-by-cond (x)
  (declare (xargs :guard t))
  (if (bool-cond-itep x)
      (mv (bool-cond-itep-cond x)
          (bool-cond-itep-truebr x)
          (bool-cond-itep-falsebr x))
    (mv t x nil)))

(defthm gobj-depends-on-of-breakdown-ite-by-cond
  (implies (not (gobj-depends-on k p x))
           (b* (((mv test x y) (breakdown-ite-by-cond x)))
             (and (not (pbfr-depends-on k p test))
                  (not (gobj-depends-on k p x))
                  (not (gobj-depends-on k p y)))))
  :hints(("Goal" :in-theory (enable breakdown-ite-by-cond
                                    bool-cond-itep
                                    bool-cond-itep-truebr
                                    bool-cond-itep-falsebr
                                    bool-cond-itep-cond))))




(local
 (defthm ite-merge-ordering-cases
   (and (equal (equal (ite-merge-ordering x y) 'equal)
               (equal x y))
        (equal (equal (ite-merge-ordering x y) 'booleans)
               (and (not (equal x y))
                    (general-booleanp x)
                    (general-booleanp y)))
        (equal (equal (ite-merge-ordering x y) 'integers)
               (and (not (equal x y))
                    (general-integerp x)
                    (general-integerp y)))
        (equal (equal (ite-merge-ordering x y) 'conses)
               (and (not (equal x y))
                    (general-consp x)
                    (general-consp y)))
        (equal (equal (ite-merge-ordering x y) 'applies)
               (and (not (equal x y))
                    (equal (tag x) :g-apply)
                    (equal (tag y) :g-apply)
                    (equal (g-apply->fn x) (g-apply->fn y))
                    (equal (len (g-apply->args x))
                           (len (g-apply->args y))))))
   :hints (("goal" :in-theory (enable general-booleanp general-integerp
                                      general-consp general-concrete-atom
                                      tag ite-merge-ordering)))))


(local
 (defthm nfix-natp
   (implies (natp n)
            (equal (nfix n) n))
   :rule-classes ((:rewrite :backchain-limit-lst 0))))

(local
 (encapsulate nil
   ;; (local (add-bfr-pat (hyp-fix . ?)))
   (local (in-theory (disable* acl2-count integer-abs
                               equal-of-booleans-rewrite not
                               hyp-fix-of-hyp-fixedp

;                               bfr-eval-nonnil-forward
                               default-+-2 o<
                               default-<-1
                               default-+-1
                               default-<-2 nfix
                               ;;                                true-under-hyp-rw
                               ;;                                false-under-hyp-rw
                               iff-implies-equal-not
                               bfr-eval-booleanp
                               (:rules-of-class
                                :type-prescription :here))))

;    (local (bfr-reasoning-mode t))

   (local (in-theory (enable (:type-prescription acl2-count))))

   (defthm merge-rest-measure-thm
     (let ((hyp (bfr-hyp-fix hyp)))
       (and (o-p (merge-rest-measure x y))
            (implies (and ;; (and (not (fh c)) (not (th c)))
                      (not (th firstcond))
                      ;; hyp
                      )
                     (let ((old-measure
                            (merge-rest-measure x y)))
                       (and (implies (fh firstcond)
                                     (o< (ite-merge-measure x y)
                                         old-measure))
                            (o< (ite-merge-measure x y)
                                old-measure))))))
     :hints (("goal" :do-not-induct t
              :in-theory nil)
             (and stable-under-simplificationp
                  '(:in-theory (enable)))
             (and stable-under-simplificationp
                  '(:in-theory
                    (enable hyp-fix hyp-fixedp
                            true-under-hyp
                            false-under-hyp)))))

   (defthm maybe-merge-measure-thm
     (let ((old-measure (maybe-merge-measure x y)))
       (and (o-p old-measure)
            (and (implies (eql (ite-merge-ordering x y) 'conses)
                          (and (o< (ite-merge-measure (general-consp-car x)
                                                      (general-consp-car y))
                                   old-measure)
                               (o< (ite-merge-measure (general-consp-cdr x)
                                                      (general-consp-cdr y))
                                   old-measure)))
                 (implies (eql (ite-merge-ordering x y) 'applies)
                          (o< (ite-merge-measure (g-apply->args x)
                                                 (g-apply->args y))
                              old-measure)))))
     :hints ((and stable-under-simplificationp
                  '(:in-theory
                    (enable hyp-fix hyp-fixedp
                            true-under-hyp
                            false-under-hyp)))))

   (defthm ite-merge-measure-thm
     (let ((hyp (bfr-hyp-fix hyp)))
       (and (o-p (ite-merge-measure x y))
            (implies
             (and (not (th c)) (not (fh c)))
             (b* ((old-measure (ite-merge-measure x y))
                  ((mv ?first-x-cond first-x rest-x)
                   ;; x is (if first-x-cond first-x rest-x)
                   (breakdown-ite-by-cond x))
                  ((mv ?first-y-cond first-y rest-y)
                   (breakdown-ite-by-cond y)))
               (and ;;  (implies (and (fh first-x-cond)
                ;;                                 (fh first-y-cond))
                ;;                            (o< (ite-merge-measure c rest-x rest-y hyp)
                ;;                                old-measure))
                ;;                   (implies (and (fh first-x-cond)
                ;;                                 (not (fh first-y-cond)))
                ;;                            (o< (ite-merge-measure c rest-x y hyp)
                ;;                                old-measure))
                ;;                   (implies (and (not (fh first-x-cond))
                ;;                                 (fh first-y-cond))
                ;;                            (o< (ite-merge-measure c x rest-y hyp)
                ;;                                old-measure))
                ;;                   (implies
                ;;                    (and (not (fh first-x-cond))
                ;;                         (not (fh first-y-cond)))
                (let ((firstcond (hf (bfr-ite-fn c first-x-cond first-y-cond))))
                  (and (implies (and (not (and (eq first-x-cond t)
                                               (eq first-y-cond t)))
                                     (equal fc firstcond))
                                (o< (merge-rest-measure rest-x rest-y)
                                    old-measure))
                       (o< (maybe-merge-measure first-x first-y)
                           old-measure)
                       (implies (not (eq first-x-cond t))
                                (o< (merge-rest-measure rest-x y)
                                    old-measure))
                       (implies (not (eq first-y-cond t))
                                (o< (merge-rest-measure x rest-y)
                                    old-measure)))))))))
     :hints (("goal" :do-not-induct t
              :in-theory '(breakdown-ite-by-cond))
             (and stable-under-simplificationp
                  '(:in-theory (disable (two-nats-measure)
                                        (maybe-merge-measure))))
             (and stable-under-simplificationp
                  '(:in-theory
                    (e/d (hyp-fix hyp-fixedp
                            true-under-hyp
                            false-under-hyp)
                         ((two-nats-measure)
                          (maybe-merge-measure)))))))

   (defthm ite-merge-lists-measure-thm
     (implies (consp x)
                (and (o< (ite-merge-measure (car x) (car y))
                         (ite-merge-measure x y))
                     (o< (ite-merge-measure (cdr x) (cdr y))
                         (ite-merge-measure x y))))
     :hints(("Goal" :in-theory (enable ite-merge-measure acl2-count))))))




(mutual-recursion
 (defun merge-rest (firstcond first c x y hyp)
   ;; (if firstcond first (if c x y))
   (declare (xargs :guard t ;; (and (not (fh c)) (not (th c)))
                   :verify-guards nil
                   :stobjs hyp
                   :measure (merge-rest-measure x y)))
   (let* ((hyp (lbfr-hyp-fix hyp)))
   ;;(if (mbt (merge-rest-guard c hyp))
     (cond ;; ((not hyp) nil)
      ((th firstcond)
       (mv first hyp))
      ((fh firstcond)
       (ite-merge c x y hyp))
      (t (b* (((mv contra hyp undo) (bfr-assume (bfr-not firstcond) hyp))
              ((mv merge hyp)
               (if contra
                   (mv nil hyp)
                 (ite-merge (hf c) x y hyp)))
              (hyp (bfr-unassume hyp undo)))
           (mv (mk-g-ite (mk-g-boolean firstcond)
                         first
                         merge)
               hyp))))))

 (defun maybe-merge (c x y xhyp yhyp hyp)
   (declare (xargs :guard t
                   :stobjs hyp
                   :measure (maybe-merge-measure x y)))
   (let* ((hyp (lbfr-hyp-fix hyp))
          (ordersym (ite-merge-ordering x y)))
     (case ordersym
       (equal (mv 'merged x hyp))
       (booleans (mv 'merged (merge-general-booleans c x y) hyp))
       (integers (mv 'merged (merge-general-integers c x y) hyp))
       (conses (b* (((mv contra hyp undo)
                     (bfr-assume (hf (bfr-ite c xhyp yhyp)) hyp))
                    ((when contra)
                     (b* ((hyp (bfr-unassume hyp undo)))
                       (mv 'merged nil hyp)))
                    (c (hf c))
                    ((mv car hyp) (ite-merge (hf c)
                                             (general-consp-car x)
                                             (general-consp-car y)
                                             hyp))
                    ((mv cdr hyp) (ite-merge (hf c)
                                             (general-consp-cdr x)
                                             (general-consp-cdr y)
                                             hyp))
                    (hyp (bfr-unassume hyp undo)))
                 (mv 'merged (gl-cons car cdr) hyp)))
       (applies (b* (((mv contra hyp undo)
                      (bfr-assume (hf (bfr-ite c xhyp yhyp)) hyp))
                     ((when contra)
                      (b* ((hyp (bfr-unassume hyp undo)))
                        (mv 'merged nil hyp)))
                     ((mv merge hyp)
                      (ite-merge-lists (hf c)
                                       (g-apply->args x)
                                       (g-apply->args y)
                                       hyp))
                     (hyp (bfr-unassume hyp undo)))
                  (mv 'merged (g-apply ;; gl-fncall-split-ite ;;
                               (g-apply->fn x) merge)
                      hyp)))
       (otherwise (mv ordersym nil hyp)))))



 (defun ite-merge (c x y hyp)
   ;; (if c x y)
   (declare (xargs :guard t
                   :measure (ite-merge-measure x y)
                   :stobjs hyp
                   :hints (("goal" :do-not-induct t
                            :in-theory '(ite-merge-measure-thm
                                         merge-rest-measure-thm
                                         maybe-merge-measure-thm
                                         ite-merge-lists-measure-thm)))))
   (let* ((hyp (lbfr-hyp-fix hyp)))
     (cond ;; ((not hyp) nil)
      ((hons-equal x y) (mv x hyp))
      ((th c) (mv x hyp))
      ((fh c) (mv y hyp))
      (t (b* (((mv first-x-cond first-x rest-x)
               (breakdown-ite-by-cond x))
              ((mv first-y-cond first-y rest-y)
               (breakdown-ite-by-cond y))
              ((mv merge-flg first hyp)
               (maybe-merge c first-x first-y first-x-cond first-y-cond hyp)))
           (case merge-flg
             (merged
              (cond ((and (eq first-x-cond t)
                          (eq first-y-cond t))
                     (mv first hyp))
                    ((eq first-x-cond t)
                     (mv (mk-g-ite (mk-g-boolean (hf (bfr-or c first-y-cond)))
                                   first rest-y)
                         hyp))
                    ((eq first-y-cond t)
                     (mv (mk-g-ite (mk-g-boolean (hf (bfr-or (bfr-not c)
                                                             first-x-cond)))
                                   first rest-x)
                         hyp))
                    (t (merge-rest (hf (bfr-ite c first-x-cond first-y-cond))
                                   first c rest-x rest-y hyp))))
             (< (if (eq first-x-cond t)
                    (mv (mk-g-ite (mk-g-boolean c) first-x y) hyp)
                  (merge-rest (bfr-and c first-x-cond)
                              first-x c rest-x y hyp)))
             (t ;; >
              (if (eq first-y-cond t)
                  (mv (mk-g-ite (mk-g-boolean (bfr-not c)) first-y x) hyp)
                (merge-rest (bfr-and (bfr-not c) first-y-cond)
                            first-y c x rest-y hyp)))))))))

 (defun ite-merge-lists (c x y hyp)
   ;; (if c x y), x and y lists
   (declare (xargs :guard (equal (len x) (len y))
                   :stobjs hyp
                   :measure (ite-merge-measure x y)))
   (b* ((hyp (lbfr-hyp-fix hyp))
        ((when (atom x)) (mv nil hyp))
        ((mv car hyp) (ite-merge c (car x) (car y) hyp))
        ((mv cdr hyp) (ite-merge-lists c (cdr x) (cdr y) hyp)))
     (mv (cons car cdr) hyp))))


(in-theory (disable ite-merge merge-rest))

(local (in-theory (disable  hyp-fix-of-hyp-fixedp)))





(local
 (encapsulate nil
   (local (defthmd bfr-eval-list-when-boolean-listp
            (implies (boolean-listp x)
                     (equal (bfr-eval-list x env)
                            x))))

   (defthm merge-general-integers-correct
     (implies (and (general-integerp a) (general-integerp b))
              (equal (generic-geval (merge-general-integers c a b) env)
                     (if (bfr-eval c (car env))
                         (generic-geval a env)
                       (generic-geval b env))))
     :hints (("goal"
              :in-theory
              (e/d ;boolean-listp-bfr-ite-bvv-fn-v2n-bind-env-car-env
;boolean-listp-bfr-ite-bss-fn-v2i-bind-env-car-env
               (merge-general-integers)
               (general-integer-bits))
              :do-not-induct t)))))






(local
 (defthm merge-general-booleans-correct
   (implies (and (general-booleanp a)
                 (general-booleanp b))
            (equal (generic-geval (merge-general-booleans c a b) env)
                   (if (bfr-eval c (car env))
                       (generic-geval a env)
                     (generic-geval b env))))
   :hints (("goal" :in-theory
            (e/d (generic-geval booleanp merge-general-booleans))))))



(local
 (defthm breakdown-ite-by-cond-correct
   (mv-let (cond first rest)
     (breakdown-ite-by-cond x)
     (and (implies (and (bfr-eval cond (car env)))
                   (equal (generic-geval first env)
                          (generic-geval x env)))
          (implies (and (not (bfr-eval cond (car env))))
                   (equal (generic-geval rest env)
                          (generic-geval x env)))))
   :hints(("Goal" :in-theory (enable hyp-fix)
           :do-not-induct t))
   :otf-flg t))



(in-theory (disable breakdown-ite-by-cond))




(local
 (defthm hlexorder-is-lexorder
   (equal (hlexorder x y) (lexorder x y))
   :hints (("goal" :in-theory (enable lexorder)))))






(local
 (flag::make-flag ite-merge-ind ite-merge
                  :defthm-macro-name def-ite-merge-thm
                  :hints (("goal" :do-not-induct t
                           :in-theory '(ite-merge-measure-thm
                                        merge-rest-measure-thm
                                        maybe-merge-measure-thm
                                        ite-merge-lists-measure-thm)))))



(local
 (def-ruleset! minimal-rules (set-difference-theories
                              (theory 'minimal-theory) '((force)))))

(local (bfr-reasoning-mode t))

;; (local
;;  (defthm gobjectp-impl-not-g-keyword-symbolp
;;    (implies (gobjectp x)
;;             (not (g-keyword-symbolp x)))
;;    :hints(("Goal" :in-theory (enable
;;                               gobject-hierarchy-impl-not-g-keyword-symbolp
;;                               gobjectp)))))

(local (add-bfr-pat (mv-nth '0 (breakdown-ite-by-cond . &) . &)))


;; (local
;;  (encapsulate nil
;;    (local (in-theory (disable* ;; gobjectp-def
;;                                (:rules-of-class :type-prescription :here)
;;                                bfr-eval-booleanp
;;                                equal-of-booleans-rewrite
;;                                ;; (:ruleset gl-wrong-tag-rewrites)
;;                                ;; (:ruleset gl-tag-forward)
;;                                ;; (:ruleset gl-tag-rewrites)
;;                                )))
;;    (local (bfr-reasoning-mode nil))
;;    (prove-guard-invariants
;;     ite-merge
;;     :simplify-hints (("Goal"
;;                       :in-theory (ruleset-theory 'minimal-rules)))
;;     :hints ((and stable-under-simplificationp
;;                  '(:in-theory (e/d* (false-under-hyp
;;                                      true-under-hyp
;;                                      hyp-fixedp
;;                                      hyp-fix
;;                                      breakdown-ite-by-cond
;;                                      (:type-prescription len)
;;                                      (tau-system)))))))))


;; (local
;;  (defthm ite-merge-guard-forward
;;    (implies (ite-merge-guard c x y hyp)
;;             (and (bfr-p c)
;;                  (gobjectp x)
;;                  (gobjectp y)
;;                  (bfr-p hyp)
;; ;;                  hyp
;; ;;                  (hyp-fixedp c hyp)
;;                  ))
;;    :rule-classes :forward-chaining))

;; (local
;;  (defthm maybe-merge-merge-guard-forward
;;    (implies (maybe-merge-guard c x y xhyp yhyp hyp)
;;             (and (bfr-p c) (bfr-p hyp)
;;                  (bfr-p xhyp) (bfr-p yhyp)
;;                  (gobjectp x)
;;                  (gobjectp y)))
;;    :rule-classes :forward-chaining))


;; (local
;;  (defthm merge-rest-guard-forward
;;    (implies (merge-rest-guard c hyp)
;;             (and (bfr-p c) (bfr-p firstcond) (bfr-p hyp)
;; ;;                  hyp (hyp-fixedp c hyp)
;; ;;                  (hyp-fixedp firstcond hyp)
;;                  (not (fh c)) (not (th c))
;;                  (gobjectp first)
;;                  (gobjectp rest-x)
;;                  (gobjectp rest-y)))
;;    :rule-classes :forward-chaining))


;; (in-theory (disable ite-merge-guard merge-rest-guard maybe-merge-guard))


(local
 (defthm ite-merge-ordering-not-merged
   (not (equal (ite-merge-ordering x y) 'merged))
   :hints(("Goal" :in-theory (enable ite-merge-ordering)))))



(local (defthm generic-geval-list-when-not-consp
         (implies (not (consp x))
                  (equal (generic-geval-list x env) nil))
         :hints(("Goal" :in-theory (enable generic-geval-list)))
         :rule-classes ((:rewrite :backchain-limit-lst 0))))

(local (defthm generic-geval-list-when-len-0
         (implies (equal (len x) 0)
                  (equal (generic-geval-list x env) nil))
         :hints(("Goal" :in-theory (enable generic-geval-list)))
         :rule-classes ((:rewrite :backchain-limit-lst 0))))

(local (defthm len-when-not-consp
         (implies (not (consp x))
                  (equal (len x) 0))
         :rule-classes ((:rewrite :backchain-limit-lst 0))))

(local (defthm len-when-consp
         (implies (consp x)
                  (posp (len x)))
         :rule-classes :type-prescription))


(local
 (def-ite-merge-thm
   (defthm ite-merge-does-not-change-hyp
     (b* (((mv ?res1 hyp1) (ite-merge c x y hyp)))
       (equal hyp1 (bfr-hyp-fix hyp)))
     :hints ('(:expand ((:free (hyp) (ite-merge c x y hyp))
                        (:free (hyp) (ite-merge c x x hyp)))))
     :flag ite-merge)
   (defthm ite-merge-lists-does-not-change-hyp
     (b* (((mv ?res1 hyp1) (ite-merge-lists c x y hyp)))
       (equal hyp1 (bfr-hyp-fix hyp)))
     :hints ('(:expand ((:free (hyp) (ite-merge-lists c x y hyp)))))
     :flag ite-merge-lists)
   (defthm maybe-merge-does-not-change-hyp
     (b* (((mv ?flg1 ?ans1 hyp1) (maybe-merge c x y xhyp yhyp hyp)))
       (equal hyp1 (bfr-hyp-fix hyp)))
     :hints ('(:expand ((:free (hyp) (maybe-merge c x y xhyp yhyp hyp)))))
     :flag maybe-merge)

   (defthm merge-rest-does-not-change-hyp
     (b* (((mv ?res1 hyp1) (merge-rest firstcond first c x y hyp)))
       (equal hyp1 (bfr-hyp-fix hyp)))
     :hints ('(:expand ((:free (hyp) (merge-rest firstcond first c x y hyp)))))
     :flag merge-rest)
   :hints (("goal" :do-not-induct t))))


(local
 (def-ite-merge-thm
   (defthm ite-merge-of-bfr-hyp-fix
     (equal (ite-merge c x y (bfr-hyp-fix hyp))
            (ite-merge c x y hyp))
     :hints ('(:expand ((:free (hyp) (ite-merge c x y hyp))
                        (:free (hyp) (ite-merge c x x hyp)))))
     :flag ite-merge)
   (defthm ite-merge-lists-of-bfr-hyp-fix
     (equal (ite-merge-lists c x y (bfr-hyp-fix hyp))
            (ite-merge-lists c x y hyp))
     :hints ('(:expand ((:free (hyp) (ite-merge-lists c x y hyp)))))
     :flag ite-merge-lists)
   (defthm maybe-merge-of-bfr-hyp-fix
     (equal (maybe-merge c x y xhyp yhyp (bfr-hyp-fix hyp))
            (maybe-merge c x y xhyp yhyp hyp))
     :hints ('(:expand ((:free (hyp) (maybe-merge c x y xhyp yhyp hyp)))))
     :flag maybe-merge)

   (defthm merge-rest-of-bfr-hyp-fix
     (equal (merge-rest firstcond first c x y (bfr-hyp-fix hyp))
            (merge-rest firstcond first c x y hyp))
     :hints ('(:expand ((:free (hyp) (merge-rest firstcond first c x y hyp)))))
     :flag merge-rest)
   :hints (("goal" :do-not-induct t))))

(local
 (progn
   (defcong bfr-hyp-equiv equal (ite-merge c x y hyp) 4
     :hints (("goal" :use ((:instance ite-merge-of-bfr-hyp-fix)
                           (:instance ite-merge-of-bfr-hyp-fix (hyp hyp-equiv)))
              :in-theory (e/d (bfr-hyp-equiv-in-terms-of-bfr-hyp-fix)
                              (ite-merge-of-bfr-hyp-fix)))))

   (defcong bfr-hyp-equiv equal (ite-merge-lists c x y hyp) 4
     :hints (("goal" :use ((:instance ite-merge-lists-of-bfr-hyp-fix)
                           (:instance ite-merge-lists-of-bfr-hyp-fix (hyp hyp-equiv)))
              :in-theory (e/d (bfr-hyp-equiv-in-terms-of-bfr-hyp-fix)
                              (ite-merge-lists-of-bfr-hyp-fix)))))

   (defcong bfr-hyp-equiv equal (maybe-merge c x y xhyp yhyp hyp) 6
     :hints (("goal" :use ((:instance maybe-merge-of-bfr-hyp-fix)
                           (:instance maybe-merge-of-bfr-hyp-fix (hyp hyp-equiv)))
              :in-theory (e/d (bfr-hyp-equiv-in-terms-of-bfr-hyp-fix)
                              (maybe-merge-of-bfr-hyp-fix)))))

   (defcong bfr-hyp-equiv equal (merge-rest firstcond first c x y hyp) 6
     :hints (("goal" :use ((:instance merge-rest-of-bfr-hyp-fix)
                           (:instance merge-rest-of-bfr-hyp-fix (hyp hyp-equiv)))
              :in-theory (e/d (bfr-hyp-equiv-in-terms-of-bfr-hyp-fix)
                              (merge-rest-of-bfr-hyp-fix)))))))

;; (defthm bfr-unassume-cong-of-ite-merge
;;     (implies (acl2::bind-context ((hyp (bfr-hyp-equiv fixhyp (bfr-hyp-fix hyp)))))
;;              (equal (bfr-unassume$a hyp undo)
;;                     (bfr-unassume$a hyp1 undo))))


(local
 (encapsulate
   nil
   (local (in-theory (e/d* (generic-geval-g-apply-p)
                           ((force) member-equal
                            ite-merge merge-rest maybe-merge
                            general-integer-bits-correct

                            boolean-list-bfr-eval-list
                            mv-nth
                            default-car default-cdr
                            hons-assoc-equal
                            (:rewrite bfr-eval-booleanp)
                            ;; break-g-number
                            generic-geval
                            hyp-fix-of-hyp-fixedp
                            eval-concrete-gobjectp
                            default-unary-/

                            len

                            default-*-1 default-*-2
                            (:type-prescription booleanp)
                            (:type-prescription hons-assoc-equal)
                            default-complex-1 default-complex-2
                            ; bfr-eval-nonnil-forward
                            (:type-prescription hyp-fix)
                            (:type-prescription bfr-eval)
                            (:type-prescription q-implies-fn)
                            (:type-prescription bool-cond-itep)
                            (:type-prescription false-under-hyp)
                            (:type-prescription hyp-fixedp)
                            (:type-prescription bfr-binary-and)
                            (:type-prescription general-consp)
                            (:type-prescription ite-merge-ordering)
                            equal-of-booleans-rewrite
                            not))))
   ; (local (bfr-reasoning-mode nil))
   ;;  (defthm ite-merge-c-nil
   ;;    (equal (ite-merge nil x y hyp)
   ;;           (and (ite-merge-guard nil x y hyp)
   ;;                y))
   ;;    :hints(("Goal" :expand ((ite-merge nil x y hyp))
   ;;            :in-theory (enable false-under-hyp true-under-hyp))))

   (def-ite-merge-thm ite-merge-correct-lemma
     (defthm ite-merge-correct
       (implies (bfr-hyp-eval (double-rewrite hyp) (car env))
                (equal (generic-geval (mv-nth 0 (ite-merge c x y hyp)) env)
                       (if (bfr-eval c (car env))
                           (generic-geval x env)
                         (generic-geval y env))))
       :hints ('(:expand ((ite-merge c x y hyp)
                          (ite-merge c x x hyp))))
       :flag ite-merge)
     (defthm ite-merge-lists-correct
      (implies (and (bfr-hyp-eval (double-rewrite hyp) (car env))
                    (equal (len x) (len y)))
               (equal (generic-geval-list (mv-nth 0 (ite-merge-lists c x y hyp)) env)
                      (if (bfr-eval c (car env))
                          (generic-geval-list x env)
                        (generic-geval-list y env))))
       :hints ('(:expand ((ite-merge-lists c x y hyp)
                          (generic-geval-list x env)
                          (generic-geval-list y env)
                          (generic-geval-list nil env)
                          (:free (a b) (generic-geval-list (cons a b) env))
                          (len x) (len y))))
      :flag ite-merge-lists)
     (defthm maybe-merge-correct
       (mv-let (flg ans)
         (maybe-merge c x y xhyp yhyp hyp)
         (implies (and (equal flg 'merged)
                       (bfr-hyp-eval (double-rewrite hyp) (car env)))
                  (and (implies (and (bfr-eval c (car env))
                                     (bfr-eval xhyp (car env)))
                                (equal (generic-geval ans env)
                                       (generic-geval x env)))
                       (implies (and (not (bfr-eval c (car env)))
                                     (bfr-eval yhyp (car env)))
                                (equal (generic-geval ans env)
                                       (generic-geval y env))))))
       :hints ('(:expand ((maybe-merge c x y xhyp yhyp hyp)
                          (maybe-merge c x x xhyp yhyp hyp)))
               (and stable-under-simplificationp
                    '(:in-theory (enable generic-geval))))
       :flag maybe-merge)

     (defthm merge-rest-correct
       (implies (bfr-hyp-eval (double-rewrite hyp) (car env))
                (equal (generic-geval (mv-nth 0 (merge-rest firstcond first c x y hyp)) env)
                       (if (bfr-eval firstcond (car env))
                           (generic-geval first env)
                         (if (bfr-eval c (car env))
                             (generic-geval x env)
                           (generic-geval y env)))))
       :hints ('(:expand ((merge-rest firstcond first c x y hyp))))
       :flag merge-rest)
     :hints ((and stable-under-simplificationp
                  '(:in-theory (enable true-under-hyp false-under-hyp)))))

   (local (Defthm gobj-list-depends-on-nil
            (not (gobj-list-depends-on k p nil))
            :hints(("Goal" :in-theory (enable gobj-list-depends-on)))))

   (def-ite-merge-thm gobj-depends-on-of-ite-merge-lemma
     (defthm gobj-depends-on-of-ite-merge
       (implies (and (not (pbfr-depends-on k p c))
                     (not (gobj-depends-on k p x))
                     (not (gobj-depends-on k p y)))
                (not (gobj-depends-on k p (mv-nth 0 (ite-merge c x y hyp)))))
       :hints ('(:expand ((ite-merge c x y hyp)
                          (ite-merge c x y nil)
                          (ite-merge c x x hyp))))
       :flag ite-merge)
     (defthm gobj-depends-on-of-ite-merge-lists
       (implies (and (not (pbfr-depends-on k p c))
                     (not (gobj-list-depends-on k p x))
                     (not (gobj-list-depends-on k p y)))
                (not (gobj-list-depends-on k p (mv-nth 0 (ite-merge-lists c x y hyp)))))
       :hints ('(:expand ((ite-merge-lists c x y hyp))))
      :flag ite-merge-lists)
     (defthm gobj-depends-on-of-maybe-merge
       (mv-let (flg ans)
         (maybe-merge c x y xhyp yhyp hyp)
         (declare (ignore flg))
         (implies (and (not (pbfr-depends-on k p c))
                       (not (gobj-depends-on k p x))
                       (not (gobj-depends-on k p y)))
                  (not (gobj-depends-on k p ans))))
       :hints ('(:expand ((maybe-merge c x y xhyp yhyp hyp)
                          (maybe-merge c x x xhyp yhyp hyp)))
               (and stable-under-simplificationp
                    '(:in-theory (enable generic-geval))))
       :flag maybe-merge)

     (defthm gobj-depends-on-of-merge-rest
       (implies (and (not (pbfr-depends-on k p firstcond))
                     (not (gobj-depends-on k p first))
                     (not (pbfr-depends-on k p c))
                     (not (gobj-depends-on k p x))
                     (not (gobj-depends-on k p y)))
                (not (gobj-depends-on k p (mv-nth 0 (merge-rest firstcond first c x y hyp)))))
       :hints ('(:expand ((merge-rest firstcond first c x y hyp)
                          (merge-rest firstcond first c x y nil))))
       :flag merge-rest)
     :hints (("goal" :do-not-induct t)))))


(verify-guards ite-merge)





;; (local
;;  (defthm ite-merge-when-true-under-hyp
;;    (implies (and (true-under-hyp c hyp)
;;                  hyp)
;;             (equal (mv-nth 0 (ite-merge c x y hyp)) x))
;;    :hints(("Goal" :expand ((ite-merge c x y hyp))))))

;; (local
;;  (defthm ite-merge-when-false-under-hyp
;;    (implies (and (false-under-hyp c hyp)
;;                  hyp)
;;             (equal (mv-nth 0 (ite-merge c x y hyp)) y))
;;    :hints(("Goal" :expand ((ite-merge c x y hyp))
;;            :in-theory (enable true-under-hyp false-under-hyp)))))





;; (local
;;  (defthm ite-merge-guard-suff
;;    (implies (and (bfr-p c)
;;                  (gobjectp x)
;;                  (gobjectp y)
;;                  (bfr-p hyp))
;;             (ite-merge-guard c x y hyp))
;;    :hints (("goal" :in-theory (enable ite-merge-guard)))))

(define gobj-ite-merge (c x y hyp)
  (ite-merge (hf c) x y hyp)
  ///
  (defthm gobj-ite-merge-preserves-hyp
    (equal (mv-nth 1 (gobj-ite-merge c x y hyp))
           (bfr-hyp-fix hyp)))

  (defthm gobj-ite-merge-of-bfr-hyp-fix
    (equal (gobj-ite-merge c x y (bfr-hyp-fix hyp))
           (gobj-ite-merge c x y hyp)))

  (defcong bfr-hyp-equiv equal (gobj-ite-merge c x y hyp) 4
     :hints (("goal" :use ((:instance gobj-ite-merge-of-bfr-hyp-fix)
                           (:instance gobj-ite-merge-of-bfr-hyp-fix (hyp hyp-equiv)))
              :in-theory (e/d (bfr-hyp-equiv-in-terms-of-bfr-hyp-fix)
                              (gobj-ite-merge-of-bfr-hyp-fix)))))

  (defthm gobj-ite-merge-correct
    (implies (bfr-hyp-eval hyp (car env))
             (equal (generic-geval (mv-nth 0 (gobj-ite-merge c x y hyp)) env)
                    (if (bfr-eval c (car env))
                        (generic-geval x env)
                      (generic-geval y env))))
    :hints(("Goal" :in-theory (e/d (gobj-ite-merge)))))

  (defthm gobj-depends-on-of-gobj-ite-merge
    (implies (and (not (pbfr-depends-on k p c))
                  (not (gobj-depends-on k p x))
                  (not (gobj-depends-on k p y)))
             (not (gobj-depends-on k p (mv-nth 0 (gobj-ite-merge c x y hyp)))))
    :hints(("Goal" :in-theory (enable gobj-ite-merge)))))



