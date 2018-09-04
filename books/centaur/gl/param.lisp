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
(include-book "bfr-param")
(include-book "gtypes")
(include-book "bvar-db")
(include-book "std/stobjs/clone" :dir :system)
(include-book "centaur/ubdds/param" :dir :system)
(include-book "centaur/ubdds/lite" :dir :system)
(include-book "centaur/aig/misc" :dir :system)
(local (include-book "gtype-thms"))
(local (include-book "data-structures/no-duplicates" :dir :system))
(local (include-book "tools/mv-nth" :dir :system))
(local (include-book "ihs/ihs-lemmas" :dir :system))
(local (include-book "centaur/aig/eval-restrict" :dir :system))
(local (include-book "std/util/support" :dir :system)) ;; for expand-calls-computed-hint
(local (in-theory (disable acl2::append-of-nil)))

;; (local
;;  (defthm bfr-p-to-param-space
;;    (implies (bfr-p x)
;;             (bfr-p (bfr-to-param-space p x)))
;;    :hints(("Goal" :in-theory (enable bfr-p)))))

;; (local
;;  (defthm bfr-listp-to-param-space-list
;;    (implies (bfr-listp lst)
;;             (bfr-listp (bfr-list-to-param-space p lst)))
;;    :hints(("Goal" :in-theory (enable bfr-listp bfr-p)))))

(in-theory (disable bfr-to-param-space bfr-list-to-param-space))
  ;; (and (consp n)
  ;;      (cons (bfr-list-to-param-space p (car n))
  ;;            (and (consp (cdr n))
  ;;                 (cons (bfr-list-to-param-space p (cadr n))
  ;;                       (and (consp (cddr n))
  ;;                            (cons (bfr-list-to-param-space p (caddr n))
  ;;                                  (and (consp (cdddr n))
  ;;                                       (list (bfr-list-to-param-space
  ;;                                              p (cadddr n)))))))))))

;; (local
;;  (defthm wf-g-numberp-gnumber-to-param-space
;;    (implies (wf-g-numberp n)
;;             (wf-g-numberp (gnumber-to-param-space n p)))
;;    :hints(("Goal" :in-theory (enable wf-g-numberp gnumber-to-param-space)))))

(mutual-recursion
 (defun gobj-to-param-space (x p)
   (declare (xargs :guard t
                   :verify-guards nil))
   (if (atom x)
       x
     (pattern-match x
       ((g-concrete &) x)
       ((g-boolean b) (mk-g-boolean (bfr-to-param-space p b)))
       ((g-integer bits) (mk-g-integer (bfr-list-to-param-space p bits)))
       ((g-ite if then else)
        (mk-g-ite (gobj-to-param-space if p)
                  (gobj-to-param-space then p)
                  (gobj-to-param-space else p)))
       ((g-apply fn args) (g-apply fn (gobj-list-to-param-space args p)))
       ((g-var &) x)
       (& (gl-cons (gobj-to-param-space (car x) p)
                   (gobj-to-param-space (cdr x) p))))))
 (defun gobj-list-to-param-space (x p)
   (declare (xargs :guard t))
   (if (atom x)
       nil
     (cons (gobj-to-param-space (car x) p)
           (gobj-list-to-param-space (cdr x) p)))))

;; (defthm tag-of-gobj-to-param-space
;;   (implies (and (syntaxp (quotep tag))
;;                 (g-keyword-symbolp tag)
;;                 (not (equal (tag x) tag))
;;                 (not (equal (tag x) :g-ite)))
;;            (not (equal (tag (gobj-to-param-space x p)) tag)))
;;   :hints (("goal" :expand ((gobj-to-param-space x p))
;;            :in-theory (e/d (g-keyword-symbolp
;;                             mk-g-boolean
;;                             gnumber-to-param-space
;;                             mk-g-number
;;                             mk-g-ite
;;                             gl-cons)
;;                            (norm-bvec-s
;;                             norm-bvec-u
;;                             break-g-number))
;;            :do-not-induct t)))

;; (local (in-theory (enable tag-when-g-var-p
;;                           tag-when-g-ite-p
;;                           tag-when-g-apply-p
;;                           tag-when-g-number-p
;;                           tag-when-g-boolean-p
;;                           tag-when-g-concrete-p)))

;; (defthm gobjectp-gobj-to-param-space
;;   (implies (gobjectp x)
;;            (gobjectp (gobj-to-param-space x p)))
;;   :hints(("Goal" :in-theory (e/d (gobjectp-def gobj-to-param-space)
;;                                  ((force))))))

(verify-guards gobj-to-param-space
               :hints(("Goal" :in-theory (e/d () ((force))))))



;; (local
;;  (defthmd gobjectp-g-number-2
;;    (implies (and (wf-g-numberp (g-number->num x))
;;                  (g-number-p x))
;;             (gobjectp x))
;;    :hints(("Goal" :in-theory (enable g-number-p g-number->num tag gobjectp-def)))
;;    :rule-classes ((:rewrite :backchain-limit-lst (nil 0)))))

;; (local
;;  (defthm gobjectp-g-number-list1
;;    (implies (bfr-listp x)
;;             (gobjectp (g-number (list x))))
;;    :hints(("Goal" :in-theory (enable gobjectp-def tag g-number-p
;;                                      wf-g-numberp-simpler-def)))))

;; (local
;;  (defthm gobjectp-g-number-list2
;;    (implies (and (bfr-listp x)
;;                  (bfr-listp y))
;;             (gobjectp (g-number (list x y))))
;;    :hints(("Goal" :in-theory (enable gobjectp-def tag g-number-p
;;                                      wf-g-numberp-simpler-def)))))

;; (local
;;  (defthm gobjectp-g-number-list3
;;    (implies (and (bfr-listp x)
;;                  (bfr-listp y)
;;                  (bfr-listp z))
;;             (gobjectp (g-number (list x y z))))
;;    :hints(("Goal" :in-theory (enable gobjectp-def tag g-number-p
;;                                      wf-g-numberp-simpler-def)))))

;; (local
;;  (defthm gobjectp-g-number-list4
;;    (implies (and (bfr-listp x)
;;                  (bfr-listp y)
;;                  (bfr-listp z)
;;                  (bfr-listp w))
;;             (gobjectp (g-number (list x y z w))))
;;    :hints(("Goal" :in-theory (enable gobjectp-def tag g-number-p
;;                                      wf-g-numberp-simpler-def)))))

;; (local
;;  (defthm wf-g-numberp-implies-bfr-listps
;;    (implies (wf-g-numberp (g-number->num x))
;;             (and (bfr-listp (car (g-number->num x)))
;;                  (bfr-listp (cadr (g-number->num x)))
;;                  (bfr-listp (caddr (g-number->num x)))
;;                  (bfr-listp (cadddr (g-number->num x)))))
;;    :hints(("Goal" :in-theory (enable wf-g-numberp)))))

;; (local
;;  (defthmd gobjectp-g-boolean-2
;;    (implies (and (bfr-p (g-boolean->bool x))
;;                  (g-boolean-p x))
;;             (gobjectp x))
;;    :hints(("Goal" :in-theory (enable gobjectp-def g-boolean-p g-boolean->bool
;;                                      tag)))
;;    :rule-classes ((:rewrite :backchain-limit-lst (nil 0)))))

;; (local
;;  (defthm gobjectp-g-ite-p
;;    (implies (and (g-ite-p x)
;;                  (gobjectp (g-ite->test x))
;;                  (gobjectp (g-ite->then x))
;;                  (gobjectp (g-ite->else x)))
;;             (equal (gobj-fix x) x))
;;    :hints(("Goal" :in-theory (enable gobjectp-def g-ite-p g-ite->test
;;                                      g-ite->then g-ite->else tag)))))



(local
 (defthm nth-open-const-idx
   (implies (syntaxp (quotep n))
            (equal (nth n lst)
                   (if (zp n)
                       (car lst)
                     (nth (1- n) (cdr lst)))))
   :hints(("Goal" :in-theory (enable nth)))))

(local
 (defthm bfr-eval-list-nil
   (Equal (bfr-eval-list nil env)
          nil)
   :hints (("goal" :in-theory (enable bfr-eval-list)))))

(local
 (defthm bfr-eval-list-t
   (Equal (bfr-eval-list '(t) env)
          '(t))
   :hints (("goal" :in-theory (enable bfr-eval-list)))))

;; (defthm gnumber-to-param-space-correct
;;   (implies (bfr-eval p (car env))
;;            (equal (generic-geval (gnumber-to-param-space n p)
;;                                  (cons (bfr-param-env p (car env))
;;                                        (cdr env)))
;;                   (generic-geval (g-number n) env)))
;;   :hints(("Goal" :in-theory (e/d (gnumber-to-param-space
;;                                   generic-geval)
;;                                  (components-to-number
;;                                   break-g-number
;;                                   bfr-param-env)))))

;; (defthm gnumber-to-param-space-correct-with-unparam-env
;;   (implies (and (syntaxp (not (case-match env
;;                                 (('cons ('bfr-param-env . &) . &) t))))
;;                 (bdd-mode-or-p-true p (car env)))
;;            (equal (generic-geval (gnumber-to-param-space n p)
;;                                  env)
;;                   (generic-geval (g-number n)
;;                                  (genv-unparam p env))))
;;   :hints(("Goal" :in-theory (e/d (gnumber-to-param-space
;;                                   generic-geval genv-unparam)
;;                                  (components-to-number
;;                                   break-g-number
;;                                   bfr-param-env)))))


;; (local (defthm generic-geval-g-number-of-g-number->num
;;          (implies (equal (tag x) :g-number)
;;                   (equal (generic-geval (g-number (g-number->num x)) env)
;;                          (generic-geval x env)))
;;          :hints(("Goal" :in-theory (enable generic-geval)))))

(defthm-gobj-flag
  (defthm gobj-to-param-space-correct
    (implies (bfr-eval p (car env))
             (equal (generic-geval (gobj-to-param-space x p)
                                   (genv-param p env))
                    (generic-geval x env)))
    :flag gobj)
  (defthm gobj-list-to-param-space-correct
    (implies (bfr-eval p (car env))
             (equal (generic-geval-list (gobj-list-to-param-space x p)
                                        (genv-param p env))
                    (generic-geval-list x env)))
    :flag list)
    :hints(("Goal" :in-theory
            (e/d* (genv-param
                   ;; gobjectp-g-boolean-2
                   ;; gobjectp-g-number-2
                   default-car default-cdr)
                  ((force) bfr-eval-list
                   boolean-listp bfr-eval
                   (:rules-of-class :type-prescription :here)
; generic-geval-when-g-var-tag

;                 bfr-eval-of-non-consp-cheap
;                 bfr-eval-when-not-consp
                   bfr-to-param-space
                   bfr-list-to-param-space
                   bfr-param-env
                   ;;break-g-number
                   generic-geval
                   hons-assoc-equal)
                  ((:type-prescription len)))
            :expand ((gobj-to-param-space x p)
                     (gobj-list-to-param-space x p))
            :do-not-induct t)
           (and stable-under-simplificationp
                '(:expand ((:free (env) (generic-geval x env)))))
           (and stable-under-simplificationp
                (flag::expand-calls-computed-hint
                 acl2::clause '(generic-geval generic-geval-list)))))



(defthm-gobj-flag
  (defthm gobj-to-param-space-correct-with-unparam-env
    (implies (and (syntaxp (not (and (consp env) (eq (car env) 'genv-param))))
                  (bdd-mode-or-p-true p (car env)))
             (equal (generic-geval (gobj-to-param-space x p) env)
                    (generic-geval x (genv-unparam p env))))
    :flag gobj)
  (defthm gobj-list-to-param-space-correct-with-unparam-env
    (implies (and (syntaxp (not (and (consp env) (eq (car env) 'genv-param))))
                  (bdd-mode-or-p-true p (car env)))
             (equal (generic-geval-list (gobj-list-to-param-space x p) env)
                    (generic-geval-list x (genv-unparam p env))))
    :flag list)
    :hints(("Goal" :in-theory
            (e/d* (genv-unparam
                   ;; gobjectp-g-boolean-2
                   ;; gobjectp-g-number-2
                   default-car default-cdr)
                  ((force) bfr-eval-list
                   boolean-listp bfr-eval
                   (:rules-of-class :type-prescription :here)
; generic-geval-when-g-var-tag

;                 bfr-eval-of-non-consp-cheap
;                 bfr-eval-when-not-consp
                   bfr-to-param-space
                   bfr-list-to-param-space
                   bfr-param-env
                   ;;break-g-number
                   generic-geval
                   hons-assoc-equal)
                  ((:type-prescription len)))
            :expand ((gobj-to-param-space x p)
                     (gobj-list-to-param-space x p))
            :do-not-induct t)
           (and stable-under-simplificationp
                '(:expand ((:free (env) (generic-geval x env)))))
           (and stable-under-simplificationp
                (flag::expand-calls-computed-hint
                 acl2::clause '(generic-geval generic-geval-list)))))



(defthm eval-bfr-to-param-space-self
  (implies (bfr-eval x (car env))
           (bfr-eval (bfr-to-param-space x x) (car (genv-param x env))))
  :hints(("Goal" :in-theory (enable bfr-eval bfr-to-param-space genv-param
                                    bfr-param-env bfr-unparam-env
                                    default-car))))


(defun gobj-alist-to-param-space (alist p)
  (declare (xargs :guard t))
  (if (atom alist)
      nil
    (if (consp (car alist))
        (cons (cons (caar alist) (gobj-to-param-space (cdar alist) p))
              (gobj-alist-to-param-space (cdr alist) p))
      (gobj-alist-to-param-space (cdr alist) p))))

(defthm alistp-gobj-alist-to-param-space
  (alistp (gobj-alist-to-param-space x pathcond)))





(acl2::defstobj-clone bvar-db1 bvar-db :suffix "1")


;; Copies the entries of bvar-db into bvar-db1 but parametrizes all the bound g
;; objects.
(defund parametrize-bvar-db-aux (n p bvar-db bvar-db1)
  (declare (xargs :stobjs (bvar-db bvar-db1)
                  :guard (and (natp n)
                              (<= (base-bvar bvar-db) n)
                              (<= n (next-bvar bvar-db)))
                  :measure (nfix (- (next-bvar bvar-db) (nfix n)))))
  (b* (((when (mbe :logic (zp (- (next-bvar bvar-db) (nfix n)))
                   :exec (int= (next-bvar bvar-db) n)))
        bvar-db1)
       (gobj (get-bvar->term n bvar-db))
       (pgobj (gobj-to-param-space gobj p))
       (bvar-db1 (add-term-bvar pgobj bvar-db1)))
    (parametrize-bvar-db-aux (+ 1 (lnfix n)) p bvar-db bvar-db1)))

(defund parametrize-term-equivs (p x)
  (declare (xargs :guard (alistp x)))
  (if (atom x)
      nil
    (hons-acons (gobj-to-param-space (caar x) p)
                (cdar x)
                (parametrize-term-equivs p (cdr x)))))


(defund parametrize-bvar-db (p bvar-db bvar-db1)
  (declare (xargs :stobjs (bvar-db bvar-db1)
                  :verify-guards nil))
  (b* ((base (base-bvar bvar-db))
       (bvar-db1 (init-bvar-db base bvar-db1))
       (bvar-db1 (parametrize-bvar-db-aux base p bvar-db bvar-db1)))
    (update-term-equivs (parametrize-term-equivs p (term-equivs bvar-db))
                        bvar-db1)))




(defsection parametrize-bvar-db
  (local (in-theory (enable parametrize-bvar-db parametrize-bvar-db-aux)))
  (local (include-book "arithmetic/top-with-meta" :dir :system))
  (local (include-book "std/basic/arith-equivs" :dir :system))

  (local (defthm alistp-when-term-equivsp
           (implies (and (bind-free '((bvar-db . bvar-db)) (bvar-db))
                         (term-equivsp$a x bvar-db))
                    (alistp x))
           :hints(("Goal" :in-theory (enable alistp)))))

  (defthm get-bvar->term-of-parametrize-bvar-db-aux
    (implies (and (<= (base-bvar$a bvar-db1) (nfix m))
                  (< (nfix m) (+ (next-bvar$a bvar-db1)
                                 (- (next-bvar$a bvar-db) (nfix n)))))
             (equal (get-bvar->term$a m (parametrize-bvar-db-aux n p bvar-db bvar-db1))
                    (if (<= (next-bvar$a bvar-db1) (nfix m))
                        (gobj-to-param-space
                         (get-bvar->term$a (+ (- (nfix m) (next-bvar$a bvar-db1))
                                              (nfix n))
                                           bvar-db)
                         p)
                      (get-bvar->term$a m bvar-db1)))))

  (defthm base-bvar-of-parametrize-bvar-db-aux
    (equal (base-bvar$a (parametrize-bvar-db-aux n p bvar-db bvar-db1))
           (base-bvar$a bvar-db1)))

  (defthm next-bvar-of-parametrize-bvar-db-aux
    (equal (next-bvar$a (parametrize-bvar-db-aux n p bvar-db bvar-db1))
           (+ (nfix (- (next-bvar$a bvar-db) (nfix n))) (next-bvar$a
                                                         bvar-db1))))

  (local (defthm bvar-listp-when-same-next/base
           (implies (and (bvar-listp$a x bvar-db)
                         (equal (base-bvar$a bvar-db) (base-bvar$a bvar-db1))
                         (equal (next-bvar$a bvar-db) (next-bvar$a bvar-db1)))
                    (bvar-listp$a x bvar-db1))
           :hints(("Goal" :induct (len x)))))

  (local (defthm term-equivsp-when-same-next/base
           (implies (and (term-equivsp$a x bvar-db)
                         (equal (base-bvar$a bvar-db) (base-bvar$a bvar-db1))
                         (equal (next-bvar$a bvar-db) (next-bvar$a bvar-db1)))
                    (term-equivsp$a x bvar-db1))
           :hints(("Goal" :induct (len x)))))

  (defthm term-equivsp-of-parametrize-term-equivs
    (implies (and (bind-free (and (consp x)
                                  (equal (car x) 'term-equivs$a)
                                  `((bvar-db . ,(cadr x))))
                             (bvar-db))
                  (term-equivsp x bvar-db)
                  (equal (base-bvar$a bvar-db) (base-bvar$a bvar-db1))
                  (equal (next-bvar$a bvar-db) (next-bvar$a bvar-db1)))
             (term-equivsp$a (parametrize-term-equivs p x) bvar-db1))
    :hints(("Goal" :in-theory (enable parametrize-term-equivs))))


  (verify-guards parametrize-bvar-db)


  (defthm normalize-parametrize-bvar-db
    (implies (syntaxp (not (equal bvar-db1 ''nil)))
             (equal (parametrize-bvar-db p bvar-db bvar-db1)
                    (parametrize-bvar-db p bvar-db nil))))

  (defthm base-bvar-of-parametrize-bvar-db
    (equal (base-bvar$a (parametrize-bvar-db p bvar-db bvar-db1))
           (base-bvar$a bvar-db)))

  (defthm next-bvar-of-parametrize-bvar-db
    (equal (next-bvar$a (parametrize-bvar-db p bvar-db bvar-db1))
           (next-bvar$a bvar-db)))

  (defthm get-bvar->term-of-parametrize-bvar-db
    (implies (and (<= (base-bvar$a bvar-db) (nfix n))
                  (< (nfix n) (next-bvar$a bvar-db)))
             (equal (get-bvar->term$a n (parametrize-bvar-db p bvar-db bvar-db1))
                    (gobj-to-param-space
                     (get-bvar->term$a n bvar-db) p)))))





;; (defund gnumber-from-param-space (n p)
;;   (declare (xargs :guard t))
;;   (b* (((mv rnum rden inum iden) (break-g-number n)))
;;     (mk-g-number (bfr-list-from-param-space p rnum)
;;                  (bfr-list-from-param-space p rden)
;;                  (bfr-list-from-param-space p inum)
;;                  (bfr-list-from-param-space p iden))))

;; (mutual-recursion
;;  (defun gobj-from-param-space (x p)
;;    (declare (xargs :guard t
;;                    :verify-guards nil))
;;    (if (atom x)
;;        x
;;      (pattern-match x
;;        ((g-concrete &) x)
;;        ((g-boolean b) (mk-g-boolean (bfr-from-param-space p b)))
;;        ((g-number n) (gnumber-from-param-space n p))
;;        ((g-ite if then else)
;;         (mk-g-ite (gobj-from-param-space if p)
;;                   (gobj-from-param-space then p)
;;                   (gobj-from-param-space else p)))
;;        ((g-apply fn args) (g-apply fn (gobj-list-from-param-space args p)))
;;        ((g-var &) x)
;;        (& (gl-cons (gobj-from-param-space (car x) p)
;;                    (gobj-from-param-space (cdr x) p))))))
;;  (defun gobj-list-from-param-space (x p)
;;    (declare (xargs :guard t))
;;    (if (atom x)
;;        nil
;;      (cons (gobj-from-param-space (car x) p)
;;            (gobj-list-from-param-space (cdr x) p)))))

;; (Verify-guards gobj-from-param-space)

;; (defthm gnumber-from-param-space-correct
;;   (implies (bfr-eval p (car env))
;;            (equal (generic-geval (gnumber-from-param-space n p)
;;                                  env)
;;                   (generic-geval (g-number n)
;;                                  (genv-param p env))))
;;   :hints(("Goal" :in-theory (e/d (gnumber-from-param-space
;;                                   generic-geval
;;                                   genv-param)
;;                                  (components-to-number
;;                                   break-g-number
;;                                   bfr-param-env)))))

;; (defthm-gobj-flag
;;   (defthm gobj-from-param-space-correct
;;     (implies (bfr-eval p (car env))
;;              (equal (generic-geval (gobj-from-param-space x p) env)
;;                     (generic-geval x (genv-param p env))))
;;     :hints ('(:expand ((gobj-from-param-space x p))
;;               :in-theory (enable genv-param))
;;             (and stable-under-simplificationp
;;                  '(:in-theory (enable generic-geval))))
;;     :flag gobj)
;;   (defthm gobj-list-from-param-space-correct
;;     (implies (bfr-eval p (car env))
;;              (equal (generic-geval-list (gobj-list-from-param-space x p) env)
;;                     (generic-geval-list x (genv-param p env))))
;;     :hints ('(:expand ((gobj-list-from-param-space x p))
;;               :in-theory (enable generic-geval-list)))
;;     :flag list))
