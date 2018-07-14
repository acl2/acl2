; GLMC -- Hardware model checking interface
; Copyright (C) 2017 Centaur Technology
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

(include-book "centaur/ubdds/deps" :dir :system)
(include-book "centaur/fty/deftypes" :dir :system)
(include-book "centaur/gl/bfr" :dir :system)
(include-book "centaur/gl/var-bounds" :dir :system)
(include-book "std/alists/alist-defuns" :dir :system)
(include-book "std/util/termhints" :dir :system)
(include-book "centaur/aig/aig-vars" :dir :system)
(local (include-book "std/basic/arith-equivs" :dir :system))
(local (include-book "std/alists/alist-keys" :dir :system))



(fty::deflist aig-varlist :elt-type aig-var)

(defthm aig-varlist-p-of-aig-vars
  (aig-varlist-p (acl2::aig-vars x))
  :hints(("Goal" :in-theory (enable acl2::aig-vars)
          :induct (acl2::aig-vars x))
         (and stable-under-simplificationp
              '(:in-theory (enable acl2::aig-var-p)))))

(fty::deflist bfr-varnamelist :elt-type bfr-varname)

(defthm bfr-varnamelist-p-when-aig-varlist
  (implies (and (bfr-mode)
                (aig-varlist-p x))
           (bfr-varnamelist-p x))
  :hints(("Goal" :in-theory (enable bfr-varnamelist-p bfr-varname-p))))

(defthm bfr-varnamelist-p-when-nat-listp
  (implies (nat-listp x)
           (bfr-varnamelist-p x))
  :hints(("Goal" :in-theory (enable bfr-varnamelist-p nat-listp bfr-varname-p))))

(defsection ubdd-normalize-env-for-deps
  (define and-lists (x y)
    (if (or (atom x) (atom y))
        nil
      (cons (and (car x) (car y))
            (and-lists (cdr x) (cdr y))))
    ///
    (defthm nth-of-and-lists
      (equal (nth n (and-lists x y))
             (and (nth n x) (nth n y)))))

  (defthm boolean-listp-of-or-lists
    (implies (and (boolean-listp x)
                  (boolean-listp y))
             (boolean-listp (acl2::or-lists x y)))
    :hints(("Goal" :in-theory (enable acl2::or-lists))))

  (defthm boolean-listp-of-ubdd-deps
    (boolean-listp (acl2::ubdd-deps x))
    :hints(("Goal" :in-theory (enable acl2::ubdd-deps))))

  (defthm or-lists-identity
    (implies (boolean-listp x)
             (equal (acl2::or-lists x x) x))
    :hints(("Goal" :in-theory (enable acl2::or-lists))))

  (defun ubdd-dep-subset-p (x y)
    (if (atom x)
        t
      (b* (((mv y1 yr)
            (mbe :logic (mv (car y) (cdr y))
                 :exec (if (consp y) (mv (car y) (cdr y)) (mv nil nil)))))
        (and (or (not (car x)) y1)
             (ubdd-dep-subset-p (cdr x) yr)))))

  (defthm ubdd-dep-subset-p-of-or-lists1
    (implies (not (ubdd-dep-subset-p x z))
             (not (ubdd-dep-subset-p (acl2::or-lists x y) z)))
    :hints(("Goal" :in-theory (enable acl2::or-lists))))

  (defthm ubdd-dep-subset-p-of-or-lists2
    (implies (not (ubdd-dep-subset-p x z))
             (not (ubdd-dep-subset-p (acl2::or-lists y x) z)))
    :hints(("Goal" :in-theory (enable acl2::or-lists))))

  (defun bdd-normalize-deps-ind (x mask env)
    (cond ((atom x) (list mask env))
          ((car env) (bdd-normalize-deps-ind (car x) (cdr mask) (cdr env)))
          (t         (bdd-normalize-deps-ind (cdr x) (cdr mask) (cdr env)))))


  (defthm ubdd-eval-under-dep-normalized-env
    ;; the or-lists just makes it more general
    (implies (ubdd-dep-subset-p (acl2::ubdd-deps x) mask)
             (equal (acl2::eval-bdd x (and-lists mask env))
                    (acl2::eval-bdd x env)))
    :hints(("Goal" :in-theory (enable acl2::eval-bdd acl2::ubdd-deps and-lists acl2::or-lists)
            :expand ((acl2::ubdd-deps x))
            :induct (bdd-normalize-deps-ind x mask env))))

  (define ubdd-varlist->mask (x)
    (if (atom x)
        nil
      (if (natp (car x))
          (update-nth (car x) t (ubdd-varlist->mask (cdr x)))
        (ubdd-varlist->mask (cdr x))))
    ///
    (defthm nth-of-ubdd-varlist->mask
      (iff (nth n (ubdd-varlist->mask x))
           (member (nfix n) x))))

  (define ubdd-mask->varlist (x (n natp))
    :returns (varlist nat-listp :hints(("Goal" :in-theory (enable nat-listp))))
    (if (atom x)
        nil
      (if (car x)
          (cons (lnfix n) (ubdd-mask->varlist (cdr x) (1+ (lnfix n))))
        (ubdd-mask->varlist (cdr x) (1+ (lnfix n)))))
    ///
    (Defthm member-of-ubdd-mask->varlist
      (iff (member i (ubdd-mask->varlist x n))
           (and (natp i)
                (>= i (nfix n))
                (nth (- i (nfix n)) x)))))

  (define ubdd-vars (x)
    :returns (vars nat-listp)
    (ubdd-mask->varlist (acl2::ubdd-deps x) 0))

  (define ubdd-vars-normalize-env (vars env)
    (and-lists (ubdd-varlist->mask vars) env)
    ///
    (defthm nth-of-ubdd-vars-normalize-env
      (implies (member (nfix n) vars)
               (equal (nth n (ubdd-vars-normalize-env vars env))
                      (nth n env)))))


  (defthm subsetp-equal-of-ubdd-mask->varlist
    (iff (subsetp-equal (ubdd-mask->varlist x n) y)
         (ubdd-dep-subset-p x (nthcdr n (ubdd-varlist->mask y))))
    :hints(("Goal" :in-theory (enable ubdd-mask->varlist ubdd-varlist->mask))))
  

  (defthm ubdd-eval-under-varlist-normalized-env
    (implies (subsetp (ubdd-vars x) vars)
             (equal (acl2::eval-bdd x (ubdd-vars-normalize-env vars env))
                    (acl2::eval-bdd x env)))
    :hints(("Goal" :in-theory (enable ubdd-vars-normalize-env
                                      ubdd-vars)))))

#!acl2
(define ubdd-diff-env-for-var ((n natp) x)
  :returns (mv successp env)
  (if (zp n)
      (b* (((unless (consp x)) (mv nil nil))
           (xor (q-xor (car x) (cdr x)))
           ((unless xor) (mv nil nil))
           (env (q-sat xor)))
           ;; ((unless (eval-bdd xor env)) (mv nil nil)))
        (mv t (cons nil env)))
    (b* (((when (atom x)) (mv nil nil))
         ((mv car-ok car-env) (ubdd-diff-env-for-var (1- n) (car x)))
         ((when car-ok) (mv t (cons t car-env)))
         ((mv cdr-ok cdr-env) (ubdd-diff-env-for-var (1- n) (cdr x)))
         ((when cdr-ok) (mv t (cons nil cdr-env))))
      (mv nil nil)))
  ///
  (local (defthm nth-when-not-zp
           (implies (not (zp n))
                    (equal (nth n x)
                           (and (consp x)
                                (nth (1- n) (cdr x)))))))

  ;; (local (defthm ubdd-fix-when-q-xor-is-nil
  ;;          (implies (not (q-xor x y))
  ;;                   (equal (ubdd-fix x)
  ;;                          (ubdd-fix y)))
  ;;          :hints(("Goal" :in-theory (enable ubdd-fix q-xor)
  ;;                  :induct (q-xor x y)))))
  (local (defthm q-xor-under-iff
           (implies (and (ubddp x)
                         (ubddp y))
                    (iff (q-xor x y)
                         (not (equal x y))))
           :hints(("Goal" :in-theory (enable q-xor ubddp)))))


  ;; (local
  ;;  (progn
  ;;    (defun ubdd-equiv (x y)
  ;;      (equal (ubdd-fix x) (ubdd-fix y)))

  ;;    (defequiv ubdd-equiv)
  ;;    (defcong ubdd-equiv equal (eval-bdd x env) 1
  ;;      :hints (("goal" :use ((:instance eval-bdd-ubdd-fix)
  ;;                            (:instance eval-bdd-ubdd-fix
  ;;                             (x x-equiv)))
  ;;               :in-theory (disable eval-bdd-ubdd-fix))))
  ;;    (defthm equal-ubdd-fix-nil-forward-to-ubdd-equiv
  ;;      (implies (not (ubdd-fix x))
  ;;               (ubdd-equiv x nil))
  ;;      :rule-classes :forward-chaining)
  ;;    (defthm equal-ubdd-fix-t-forward-to-ubdd-equiv
  ;;      (implies (equal (ubdd-fix x) t)
  ;;               (ubdd-equiv x t))
  ;;      :rule-classes :forward-chaining)
  ;;    (defthm equal-ubdd-fixes-forward-to-ubdd-equiv
  ;;      (implies (equal (ubdd-fix x) (ubdd-fix y))
  ;;               (ubdd-equiv x y))
  ;;      :rule-classes :forward-chaining)))

  (local (in-theory (disable equal-of-booleans-rewrite)))

  (std::defret ubdd-diff-env-for-var-correct-ubddp
    (implies (ubddp x)
             (and (iff successp
                       (nth n (ubdd-deps x)))
                  (implies (nth n (ubdd-deps x))
                           (iff (eval-bdd x (update-nth n t env))
                                (not (eval-bdd x env))))))
    :hints(("Goal" :in-theory (enable ubdd-deps eval-bdd)
            :induct (ubdd-diff-env-for-var n x)
            :expand ((ubddp x)))
           (and stable-under-simplificationp
                '(:use ((:instance q-sat-correct
                         (x (q-xor (car x) (cdr x)))))
                  :in-theory (disable q-sat-correct)))))

  (std::defret ubdd-diff-env-for-var-correct
    (b* (((mv & env) (ubdd-diff-env-for-var n (ubdd-fix x))))
      (implies (nth n (ubdd-deps (ubdd-fix x)))
               (iff (eval-bdd x (update-nth n t env))
                    (not (eval-bdd x env)))))
    :hints (("goal" :use ((:instance ubdd-diff-env-for-var-correct-ubddp
                           (x (ubdd-fix x))))
             :in-theory (disable ubdd-diff-env-for-var-correct-ubddp)))))



(define bfr-vars (x)
  :returns (varnames bfr-varnamelist-p)
  (bfr-case
    :bdd (ubdd-vars (acl2::ubdd-fix x))
    :aig (acl2::aig-vars x))
  ///
  (local (defthm bfr-semantic-depends-on-of-ubdd-fix
           (implies (not (bfr-mode))
                    (iff (bfr-semantic-depends-on k (acl2::ubdd-fix x))
                         (bfr-semantic-depends-on k x)))
           :hints ((and stable-under-simplificationp
                        (b* (((mv x1 x2)
                              (if (member-equal '(bfr-semantic-depends-on k x) clause)
                                  (mv '(acl2::ubdd-fix x) 'x)
                                (mv 'x '(acl2::ubdd-fix x)))))
                          `(:expand ((bfr-semantic-depends-on k ,x1))
                              :use ((:instance bfr-semantic-depends-on-suff
                                     (x ,x2)
                                     (v (mv-nth 1 (bfr-semantic-depends-on-witness k ,x1)))
                                     (env (mv-nth 0 (bfr-semantic-depends-on-witness k ,x1)))))
                              :in-theory (e/d (bfr-eval)
                                              (bfr-semantic-depends-on-suff
                                               bfr-semantic-depends-on-of-set-var))))))))
           
  (defthmd member-bfr-vars-iff-bfr-depends-on
    (iff (member v (bfr-vars x))
         (and (bfr-varname-p v)
              (bfr-depends-on v x)))
    :hints (("goal" :in-theory (enable bfr-depends-on
                                       bfr-eval
                                       bfr-set-var
                                       set::in-to-member))
            (and stable-under-simplificationp
                 (cond ((member-equal '(not (bfr-semantic-depends-on v x)) clause)
                        '(:expand ((bfr-semantic-depends-on v x))
                          :use ((:instance acl2::eval-bdd-of-update-when-not-dependent
                                 (x (acl2::ubdd-fix x))
                                 (n v) (v t)
                                 (env (mv-nth 0 (bfr-semantic-depends-on-witness v x))))
                                (:instance acl2::eval-bdd-of-update-when-not-dependent
                                 (x (acl2::ubdd-fix x))
                                 (n v) (v nil)
                                 (env (mv-nth 0 (bfr-semantic-depends-on-witness v x)))))
                          :in-theory (e/d (ubdd-vars bfr-eval bfr-set-var bfr-varname-p)
                                          (update-nth
                                           acl2::eval-bdd-of-update-when-not-dependent))))
                       ((member-equal '(bfr-semantic-depends-on v x) clause)
                        '(:use ((:instance bfr-semantic-depends-on-suff
                                 (v t) (k v) (x (acl2::ubdd-fix x))
                                 (env (mv-nth 1 (acl2::ubdd-diff-env-for-var v (acl2::ubdd-fix x))))))
                          :in-theory (e/d (ubdd-vars bfr-eval bfr-set-var)
                                          (bfr-semantic-depends-on-suff)))))))))

(defthm aig-eval-of-aig-env-extract
  (implies (subsetp (acl2::aig-vars x) vars)
           (equal (acl2::aig-eval x (acl2::aig-env-extract vars env))
                  (acl2::aig-eval x env)))
  :hints(("Goal" :in-theory (e/d (acl2::aig-vars acl2::aig-eval)
                                 (acl2::aig-env-lookup)))))

(define bfr-normalize-env (vars env)
  (bfr-case :bdd (ubdd-vars-normalize-env vars env)
    :aig (acl2::aig-env-extract vars env))
  ///
  (defthm bfr-eval-of-normalize-env
    (implies (subsetp (bfr-vars x) vars)
             (equal (bfr-eval x (bfr-normalize-env vars env))
                    (bfr-eval x env)))
    :hints(("Goal" :in-theory (enable bfr-vars bfr-eval)
            :use ((:instance UBDD-EVAL-UNDER-VARLIST-NORMALIZED-ENV
                   (x (acl2::ubdd-fix x)))))))

  (defthm lookup-in-bfr-normalize-env
    (equal (bfr-lookup v (bfr-normalize-env vars env))
           (if (member (bfr-varname-fix v) vars)
               (bfr-lookup v env)
             (if (bfr-mode) t nil)))
    :hints(("Goal" :in-theory (enable bfr-lookup ubdd-vars-normalize-env bfr-varname-fix)
            :do-not-induct t))
    :otf-flg t))

(defthm bfr-normalize-env-of-set-non-member
  (implies (not (member (bfr-varname-fix var) vars))
           (bfr-env-equiv (bfr-normalize-env vars (bfr-set-var var val env))
                          (bfr-normalize-env vars env)))
  :hints(("Goal" :in-theory (enable bfr-env-equiv))))

(defthm bfr-eval-of-set-non-member-var
  (implies (not (member (bfr-varname-fix var) (bfr-vars x)))
           (equal (bfr-eval x (bfr-set-var var val env))
                  (bfr-eval x env)))
  :hints (("goal" :use ((:instance bfr-eval-of-normalize-env
                         (vars (bfr-vars x)))
                        (:instance bfr-eval-of-normalize-env
                         (vars (bfr-vars x))
                         (env (bfr-set-var var val env))))
           :in-theory (disable bfr-eval-of-normalize-env))))







(fty::defmap bfr-updates :key-type bfr-varname)


;; (define bfr-mc-env-aux ((vars "list of variable numbers to read from the curr-st")
;;                         curr-st env)
;;   (if (atom vars)
;;       env
;;     (if (natp (car vars))
;;         (bfr-mc-env-aux (cdr vars) curr-st
;;                         (bfr-set-var (car vars)
;;                                      (bfr-lookup (car vars) curr-st)
;;                                      env))
;;       (bfr-mc-env-aux (cdr vars) curr-st env)))
;;   ///
;;   (defthm lookup-in-bfr-mc-env-aux
;;     (equal (bfr-lookup v (bfr-mc-env-aux vars curr-st env))
;;            (if (member (nfix v) vars)
;;                (bfr-lookup v curr-st)
;;              (bfr-lookup v env)))))


(local (include-book "std/alists/fast-alist-clean" :dir :system))

(defthm bfr-varname-p-of-nil
  (and (not (bfr-varname-p nil))
       (not (hide (bfr-varname-p nil))))
  :hints(("Goal" :in-theory (e/d (bfr-varname-p)
                                 ((bfr-varname-p)))
          :expand ((:free (x) (hide x))))))

(define bfr-env-override ((override-vars bfr-varnamelist-p)
                          (override-env)
                          (env))
  :returns (new-env)
  (if (atom override-vars)
      env
    (bfr-set-var (car override-vars)
                 (bfr-lookup (car override-vars) override-env)
                 (bfr-env-override (cdr override-vars) override-env env)))
  ///
  (local (defthm equal-of-bfr-varname-fix-forward
           (implies (equal (bfr-varname-fix x) (bfr-varname-fix y))
                    (bfr-varname-equiv x y))
           :rule-classes :forward-chaining))

  (std::defret lookup-in-bfr-env-override
    (equal (bfr-lookup v new-env)
           (if (member (bfr-varname-fix v) (bfr-varnamelist-fix override-vars))
               (bfr-lookup v override-env)
             (bfr-lookup v env)))
    :hints(("Goal" :in-theory (enable bfr-varnamelist-fix))))

  (local (defthm member-implies-member-bfr-varnamelist-fix
           (implies (member k y)
                    (member (bfr-varname-fix k) (bfr-varnamelist-fix y)))
           :hints(("Goal" :in-theory (enable bfr-varnamelist-fix)))))

  (local (defthm member-of-bfr-varnamelist-fix-subset
           (implies (and (subsetp x y)
                         (member k (bfr-varnamelist-fix x)))
                    (member k (bfr-varnamelist-fix y)))
           :hints(("Goal" :in-theory (enable bfr-varnamelist-fix subsetp)))))

  (defcong acl2::set-equiv acl2::set-equiv (bfr-varnamelist-fix x) 1
    :hints(("Goal" :in-theory (enable acl2::set-equiv acl2::subsetp-witness-rw))))

  (defcong acl2::set-equiv bfr-env-equiv (bfr-env-override override-vars override-env env) 1
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))
                   :do-not-induct t))))

  (defcong bfr-env-equiv equal (bfr-env-override override-vars override-env env) 2
    :hints (("Goal" :induct (bfr-env-override override-vars override-env env)
             :expand ((:free (override-env) (bfr-env-override override-vars override-env env)))))))

(define bfr-updates->states ((x bfr-updates-p))
  :returns (states bfr-varnamelist-p :hints(("Goal" :in-theory (enable nat-listp))))
  (if (atom x)
      nil
    (if (mbt (bfr-varname-p (caar x)))
        (cons (caar x) (bfr-updates->states (cdr x)))
      (bfr-updates->states (cdr x))))
  ///
  (defthm member-bfr-updates->states
    (iff (member v (bfr-updates->states x))
         (and (bfr-varname-p v) (hons-assoc-equal v x))))

  (fty::deffixcong bfr-updates-equiv equal (bfr-updates->states x) x
    :hints(("Goal" :in-theory (enable bfr-updates-fix)))))


(define bfr-mc-env ((updates bfr-updates-p) curr-st env)
  :enabled t
  :guard-hints (("goal" :in-theory (enable bfr-updates->states bfr-env-override)
                 :expand ((bfr-mc-env (cdr updates) curr-st env))))
  (mbe :logic (bfr-env-override (bfr-updates->states updates) curr-st env)
       :exec
       (if (atom updates)
           env
         (if (mbt (bfr-varname-p (caar updates)))
             (bfr-set-var (caar updates)
                          (bfr-lookup (caar updates) curr-st)
                          (bfr-mc-env (cdr updates) curr-st env))
           (bfr-mc-env (cdr updates) curr-st env)))))

(define bfr-eval-updates ((updates bfr-updates-p) env)
  (if (atom updates)
      nil
    (if (mbt (bfr-varname-p (caar updates)))
        (bfr-set-var (caar updates)
                     (bfr-eval (cdar updates) env)
                     (bfr-eval-updates (cdr updates) env))
      (bfr-eval-updates (cdr updates) env)))
  ///
  (defthm bfr-lookup-of-bfr-eval-updates
    (implies (hons-assoc-equal (bfr-varname-fix v) updates)
             (equal (bfr-lookup v (bfr-eval-updates updates env))
                    (bfr-eval (cdr (hons-assoc-equal (bfr-varname-fix v) updates)) env))))

  (defthmd bfr-lookup-of-bfr-eval-updates-split
    (equal (bfr-lookup v (bfr-eval-updates updates env))
           (if (hons-assoc-equal (bfr-varname-fix v) updates)
               (bfr-eval (cdr (hons-assoc-equal (bfr-varname-fix v) updates)) env)
             (if (bfr-mode) t nil)))
    :hints (("Goal" :induct t)
            (and stable-under-simplificationp
                 '(:in-theory (enable bfr-lookup hons-assoc-equal)))))

  (fty::deffixcong bfr-updates-equiv equal (bfr-eval-updates updates env) updates
    :hints(("Goal" :in-theory (enable bfr-updates-fix))))

  (defcong bfr-env-equiv equal (bfr-eval-updates updates env) 2)


  (defthm bfr-eval-updates-of-fast-alist-clean
    (bfr-env-equiv (bfr-eval-updates (fast-alist-clean updates) env)
                   (bfr-eval-updates updates env))
    :hints(("Goal" :in-theory (e/d (bfr-env-equiv
                                    bfr-lookup-of-bfr-eval-updates-split)
                                   (fast-alist-clean))
            :do-not-induct t))))

(local (defthm  bfr-updates->states-of-fast-alist-clean
         (acl2::set-equiv (bfr-updates->states (fast-alist-clean x))
                          (bfr-updates->states x))
         :hints(("Goal" :in-theory (enable acl2::set-unequal-witness-rw)))))
             

;; A bfr-mcstate is a mapping from naturals to Booleans.
;; A bfr-mcupdate is a mapping from naturals to BFRs.
(define bfr-mcrun ((prop "BFR giving the safety property in terms of current state and inputs")
                   (updates bfr-updates-p "next state: mapping from naturals to BFRs")
                   (curr-st "BFR env")
                   (ins "list of BFR envs"))
  :measure (len ins)
  ;; Returns t if the property held until the inputs ran out.
  (b* (((when (atom ins)) t)
       (env (bfr-mc-env updates curr-st (car ins)))
       ((unless (bfr-eval prop env)) nil))
    (mbe :logic
         (b* ((next-st (bfr-eval-updates updates env)))
           (bfr-mcrun prop updates next-st (cdr ins)))
         :exec (or (atom (cdr ins))
                   (b* ((next-st (bfr-eval-updates updates env)))
                     (bfr-mcrun prop updates next-st (cdr ins))))))
  ///
  (fty::deffixcong bfr-updates-equiv equal (bfr-mcrun prop updates curr-st ins) updates
    :hints (("goal" :induct (bfr-mcrun prop updates curr-st ins)
             :expand ((:free (updates) (bfr-mcrun prop updates curr-st ins))))))

  (defthm bfr-mcrun-under-bfr-env-equiv-curr-st
    (implies (bfr-env-equiv curr-st curr-st2)
             (equal (bfr-mcrun prop updates curr-st ins)
                    (bfr-mcrun prop updates curr-st2 ins)))
    :hints (("goal" :induct (bfr-mcrun prop updates curr-st ins)
             :expand ((:free (curr-st) (bfr-mcrun prop updates curr-st ins)))))
    :rule-classes :congruence)

  (defthm bfr-mcrun-of-fast-alist-clean
    (equal (bfr-mcrun prop (fast-alist-clean updates) curr-st ins)
           (bfr-mcrun prop updates curr-st ins))
    :hints (("goal" :induct (bfr-mcrun prop updates curr-st ins)
             :in-theory (disable fast-alist-clean)
             :expand ((:free (updates) (bfr-mcrun prop updates curr-st ins)))))))



;; (define nat-list-filter (x)
;;   (if (atom x)
;;       nil
;;     (if (natp (car x))
;;         (cons (car x) (nat-list-filter (cdr x)))
;;       (nat-list-filter (cdr x))))
;;   ///
;;   (defthm member-of-nat-list-filter
;;     (iff (member v (nat-list-filter x))
;;          (and (natp v) (member v x))))

;;   (defthm nat-list-filter-of-append
;;     (equal (nat-list-filter (append a b))
;;            (append (nat-list-filter a)
;;                    (nat-list-filter b))))

;;   (defthm nat-list-filter-of-union
;;     (acl2::set-equiv (nat-list-filter (set::union a b))
;;                      (append (nat-list-filter (set::sfix a))
;;                              (nat-list-filter (set::sfix b))))
;;     :hints(("Goal" :in-theory (enable acl2::set-unequal-witness-correct))))

;;   (defthm nat-list-filter-of-insert
;;     (acl2::set-equiv (nat-list-filter (set::insert x y))
;;                      (let ((yy (nat-list-filter (set::sfix y))))
;;                      (if (natp x)
;;                          (cons x yy)
;;                        yy)))
;;     :hints(("Goal" :in-theory (enable acl2::set-unequal-witness-correct)))))

;; (defsection aig-normalize-env-for-deps
  

;;   (defthm aig-eval-of-aig-env-extract
;;     (implies (subsetp (acl2::aig-vars x)) vars)
;;              (equal (acl2::aig-eval x (nat-var-aig-env-fix (aig-env-extract vars env)))
;;                     (acl2::aig-eval x (nat-var-aig-env-fix env))))
;;     :hints(("Goal" :in-theory (enable acl2::aig-eval acl2::aig-vars))))







(defthm bfr-normalize-env-of-bfr-env-override
  (implies (subsetp-equal vars (bfr-varnamelist-fix override-vars))
           (bfr-env-equiv (bfr-normalize-env vars (bfr-env-override override-vars curr-st env))
                          (bfr-normalize-env vars curr-st)))
  :hints(("Goal" :in-theory (enable bfr-env-equiv))))

(defun-sk bfr-inductive-invariantp (invar updates)
  (forall (in1 curr-st)
          (and (subsetp-equal (bfr-vars invar) (bfr-updates->states updates))
               (b* ((env1 (bfr-env-override (bfr-updates->states updates) curr-st in1))
                    (next-st (bfr-eval-updates updates env1)))
                 (implies (bfr-eval invar curr-st)
                          (bfr-eval invar next-st)))))
  :rewrite :direct)


(in-theory (disable bfr-inductive-invariantp))

(defthm bfr-mcrun-by-inductive-invariant
  (implies (and (bfr-inductive-invariantp invar updates)
                (bfr-eval invar curr-st)
                ;; invariant implies property
                (bfr-equiv (bfr-and invar (bfr-not prop)) nil))
           (bfr-mcrun prop updates curr-st ins))
  :hints (("goal" :in-theory (enable bfr-mcrun)
           :induct t)
          (and stable-under-simplificationp
               '(:use ((:instance bfr-equiv-necc
                        (x (bfr-binary-and invar (bfr-not prop)))
                        (y nil)
                        (env (bfr-mc-env updates curr-st (car ins))))
                       (:instance bfr-normalize-env-of-bfr-env-override
                        (vars (bfr-updates->states updates))
                        (override-vars (bfr-updates->states updates))
                        (env (car ins)))
                       (:instance bfr-eval-of-normalize-env
                        (x invar) (vars (bfr-updates->states updates))
                        (env (bfr-mc-env updates curr-st (car ins)))))
                 :in-theory (disable BFR-EQUIV-IMPLIES-EQUAL-BFR-EVAL-1
                                     bfr-equiv-necc
                                     bfr-normalize-env-of-bfr-env-override)))))
           
(defun-sk bfr-invariantp (prop updates curr-st)
  (forall ins
          (bfr-mcrun prop updates curr-st ins)))

(defthm bfr-invariantp-when-exists-inductive-invariant
  (implies (and (bfr-inductive-invariantp invar updates)
                (bfr-eval invar curr-st)
                ;; invariant implies property
                (bfr-equiv (bfr-and invar (bfr-not prop)) nil))
           (bfr-invariantp prop updates curr-st))
  :hints(("Goal" :in-theory (enable bfr-invariantp))))












(define bfr-constrained-mcrun ((prop "BFR giving the safety property in terms of current state and inputs")
                               (constr "Constraint assumed to hold at each frame")
                               (updates bfr-updates-p "next state: mapping from naturals to BFRs")
                               (curr-st "BFR env")
                               (ins "list of BFR envs"))
  :measure (len ins)
  ;; Returns t if the property held until the inputs ran out.
  (b* (((when (atom ins)) t)
       (env (bfr-mc-env updates curr-st (car ins)))
       ((unless (bfr-eval constr env)) t)
       ((unless (bfr-eval prop env)) nil))
    (mbe :logic
         (b* ((next-st (bfr-eval-updates updates env)))
           (bfr-constrained-mcrun prop constr updates next-st (cdr ins)))
         :exec (or (atom (cdr ins))
                   (b* ((next-st (bfr-eval-updates updates env)))
                     (bfr-constrained-mcrun prop constr updates next-st (cdr ins))))))
  ///
  (fty::deffixcong bfr-updates-equiv equal (bfr-constrained-mcrun prop constr updates curr-st ins) updates
    :hints (("goal" :induct (bfr-constrained-mcrun prop constr updates curr-st ins)
             :expand ((:free (updates) (bfr-constrained-mcrun prop constr updates curr-st ins))))))

  (defthm bfr-constrained-mcrun-under-bfr-env-equiv-curr-st
    (implies (bfr-env-equiv curr-st curr-st2)
             (equal (bfr-constrained-mcrun prop constr updates curr-st ins)
                    (bfr-constrained-mcrun prop constr updates curr-st2 ins)))
    :hints (("goal" :induct (bfr-constrained-mcrun prop constr updates curr-st ins)
             :expand ((:free (curr-st) (bfr-constrained-mcrun prop constr updates curr-st ins)))))
    :rule-classes :congruence)

  (defthm bfr-constrained-mcrun-of-fast-alist-clean
    (equal (bfr-constrained-mcrun prop constr (fast-alist-clean updates) curr-st ins)
           (bfr-constrained-mcrun prop constr updates curr-st ins))
    :hints (("goal" :induct (bfr-constrained-mcrun prop constr updates curr-st ins)
             :in-theory (disable fast-alist-clean)
             :expand ((:free (updates) (bfr-constrained-mcrun prop constr updates curr-st ins)))))))



(define bfr-varlist-bounded ((k natp)
                             (x bfr-varnamelist-p))
  (if (atom x)
      t
    (and (b* ((x1 (bfr-varname-fix (car x))))
           (and (natp x1)
                (< x1 (lnfix k))))
         (bfr-varlist-bounded k (cdr x))))
  ///
  (defthm not-bfr-varlist-bounded-when-member
    (implies (and (member q x)
                  (bfr-varnamelist-p x)
                  (natp q)
                  (<= (nfix k) q))
             (not (bfr-varlist-bounded k x))))

  (defthm bfr-varlist-bounded-of-nfix
    (equal (bfr-varlist-bounded (nfix k) x)
           (bfr-varlist-bounded k x))))

(encapsulate
  (((bfr-mcheck * * * * *) => (mv * * *)
    :formals (prop constr updates initstp max-bvar)
    :guard (and (bfr-updates-p updates)
                (natp max-bvar))))

  (local (defun bfr-mcheck (prop constr updates initstp max-bvar)
           (declare (ignore prop constr updates initstp max-bvar))
           (mv nil nil nil)))

  (defthm bfr-mcheck-proof-correct
    (b* (((mv result ?ctrex-initst ?ctrex-ins) (bfr-mcheck prop constr updates initstp max-bvar)))
      (implies (and (equal result :proved)
                    (bfr-eval initstp (bfr-env-override (bfr-updates->states updates) init-st (car ins)))
                    (pbfr-vars-bounded max-bvar t prop)
                    (pbfr-vars-bounded max-bvar t constr)
                    (pbfr-vars-bounded max-bvar t initstp)
                    (pbfr-list-vars-bounded max-bvar t (alist-vals (bfr-updates-fix updates)))
                    ;; (subsetp (bfr-vars initstp) (bfr-updates->states updates))
                    (bfr-varlist-bounded max-bvar (bfr-updates->states updates)))
               (bfr-constrained-mcrun prop constr updates init-st ins)))))

(defxdoc bfr-mcheck
  :parents (glmc)
  :short "Attachable interface for @(see GLMC)'s model-checking backend"
  :long "<p>@('Bfr-mcheck') is a constrained function that GLMC calls in order
to solve hardware model-checking queries.</p>

<p>Bfr-mcheck operates on hons-AIGs (see @(see acl2::aig)) whose input
variables are natural numbers.  This is potentially important because it
provides an easy way for a backend to generate new variables that are known to
be unused.  Some of the variables represent primary inputs and some represent
states; the state variables are simply those that are bound in the next-state
alist.  Below, when we refer to a \"single AIG\", this means a single hons-AIG
object, which represents a single-output Boolean function.</p>

<p>Inputs:</p>
<ul>
<li>@('prop'): Single AIG giving the invariant property to prove.</li>
<li>@('constr'): Single AIG giving the invariant constraint to assume.</li>
<li>@('updates'): Alist mapping each state variable to a single AIG
representing its next-state function.</li>
<li>@('initstp'): Single AIG assumed to be true of any initial state.</li>
<li>@('max-bvar'): Natural number greater than all variables used in the AIGs.</li>
</ul>

<p>Outputs:</p>
<ul>
<li>@('result'): one of the symbols @(':proved'), @(':refuted'), or
@(':failed'), indicating the status of the check.</li>
<li>@('ctrex-initst'): when refuted, an alist mapping each state variable to
its Boolean initial state in the counterexample.</li>
<li>@('ctrex-ins'): when refuted, a list of alists representing the frames of
the counterexample, each alist mapping each non-state variable to a Boolean
value.</li>
</ul>

<p>The constraint assumed of @('bfr-mcheck') pertains to what is implied when
it returns the result @(':proved'):</p>

@({
 (b* (((mv result ?ctrex-initst ?ctrex-ins) (bfr-mcheck prop constr updates initstp max-bvar)))
      (implies (and (equal result :proved)
                    (bfr-eval initstp (bfr-env-override (bfr-updates->states updates) init-st (car ins)))
                    (pbfr-vars-bounded max-bvar t prop)
                    (pbfr-vars-bounded max-bvar t constr)
                    (pbfr-vars-bounded max-bvar t initstp)
                    (pbfr-list-vars-bounded max-bvar t (alist-vals (bfr-updates-fix updates)))
                    ;; (subsetp (bfr-vars initstp) (bfr-updates->states updates))
                    (bfr-varlist-bounded max-bvar (bfr-updates->states updates)))
               (bfr-constrained-mcrun prop constr updates init-st ins)))
 })
<p>
This basically says:</p>

<box>
If @('bfr-mcheck') returned @(':proved'), then assuming that all the input AIGs
use only variables below @('max-bvar') and that the initial state of a finite
run satisfies @('initstp'), then the property holds at every frame of that run
at which the constraint has not yet been violated.
</box>

<p>See @(see bfr-mcheck-abc-simple) for an example backend that may be attached
to @('bfr-mcheck').</p>
")



(encapsulate nil
  (local (defun bfr-env-override-env-cong-ind (vars curr-st env1 env2)
           (if (atom vars)
               (list env1 env2)
             (bfr-env-override-env-cong-ind (cdr vars)
                                      curr-st
                                      (bfr-set-var (car vars)
                                                   (bfr-lookup (car vars) curr-st)
                                                   env1)
                                      (bfr-set-var (car vars)
                                                   (bfr-lookup (car vars) curr-st)
                                                   env2)))))
  (defcong bfr-env-equiv bfr-env-equiv (bfr-env-override vars curr-st env) 3
    :hints(("Goal" :in-theory (enable bfr-env-override)
            :induct (bfr-env-override-env-cong-ind vars curr-st env env-equiv))
           (and stable-under-simplificationp
                `(:expand (,(hons-assoc-equal 'bfr-env-equiv clause)))))))

(define bfrlist-vars (x)
  (if (atom x)
      nil
    (append (bfr-vars (car x))
            (bfrlist-vars (cdr x)))))

(define bfrmc-add-constraint ((prop "BFR giving the safety property in terms of current state and inputs")
                              (constr "Constraint assumed to hold at each frame")
                              (updates bfr-updates-p "next state: mapping from naturals to BFRs")
                              (constr-violated-var bfr-varname-p))
  :returns (mv (new-prop)
               (new-updates bfr-updates-p))
  (b* ((constr-violated-expr (bfr-var constr-violated-var))
       (constr-violated-next (bfr-or (bfr-not constr) constr-violated-expr))
       (new-prop (bfr-or constr-violated-next prop))
       (new-updates (cons (cons (bfr-varname-fix constr-violated-var)
                                constr-violated-next)
                          (bfr-updates-fix updates))))
    (mv new-prop new-updates))
  ///
  (std::defret bfrmc-add-constraint-when-violated
    (implies (bfr-lookup constr-violated-var curr-st)
             (bfr-mcrun new-prop new-updates curr-st ins))
    :hints (("goal" :induct (bfr-mcrun
                             (mv-nth 0 (bfrmc-add-constraint prop constr updates constr-violated-var))
                             (mv-nth 1 (bfrmc-add-constraint prop constr updates constr-violated-var))
                             curr-st ins)
             :in-theory (enable (:i bfr-mcrun))
             :expand ((:free (prop updates curr-st) (bfr-mcrun prop updates curr-st ins))))))


  (local (defthmd permute-bfr-set-var-under-bfr-env-equiv
           (implies (syntaxp (eq var2 'var))
                    (bfr-env-equiv (bfr-set-var var1 val1 (bfr-set-var var2 val2 env))
                                   (if (bfr-varname-equiv var1 var2)
                                       (bfr-set-var var1 val1 env)
                                     (bfr-set-var var2 val2 (bfr-set-var var1 val1 env)))))
           :hints(("Goal" :in-theory (enable bfr-env-equiv)))))

  (defthm bfr-normalize-env-of-bfr-env-override-set-irrel
    (implies (not (member (bfr-varname-fix var) vars))
             (bfr-env-equiv (bfr-normalize-env vars (bfr-env-override override-vars override-env
                                                                      (bfr-set-var var val env)))
                            (bfr-normalize-env vars (bfr-env-override override-vars override-env env))))
    :hints(("Goal" :in-theory (enable bfr-env-equiv))))


  ;; (defthm bfr-eval-of-bfr-mc-env-set-irrel-in-var
  ;;   (implies (not (bfr-depends-on var prop))
  ;;            (equal (bfr-eval prop (bfr-mc-env updates st (bfr-set-var var val in)))
  ;;                   (bfr-eval prop (bfr-mc-env updates st in))))
  ;;   :hints(("Goal" :in-theory (enable bfr-mc-env permute-bfr-set-var-under-bfr-env-equiv))))
  (defthm bfr-eval-of-bfr-env-override-set-irrel-in-var
    (implies (not (member (bfr-varname-fix var) (bfr-vars prop)))
             (equal (bfr-eval prop (bfr-env-override vars st (bfr-set-var var val in)))
                    (bfr-eval prop (bfr-env-override vars st in))))
    :hints (("goal" :use ((:instance bfr-eval-of-normalize-env
                           (x prop) (vars (bfr-vars prop))
                           (env (bfr-env-override vars st (bfr-set-var var val in))))
                          (:instance bfr-eval-of-normalize-env
                           (x prop) (vars (bfr-vars prop))
                           (env (bfr-env-override vars st in))))
             :in-theory (e/d () (bfr-eval-of-normalize-env)))))

  (defthm bfr-eval-updates-of-set-irrel-in-var
    (implies (not (member (bfr-varname-fix var) (bfrlist-vars (alist-vals updates1))))
             (equal (bfr-eval-updates updates1 (bfr-set-var var val in))
                    (bfr-eval-updates updates1 in)))
    :hints(("Goal" :in-theory (enable bfr-eval-updates bfrlist-vars alist-vals))))

  (defthm bfr-env-override-set-irrel-st-var
    (implies (not (member (bfr-varname-fix var) (bfr-varnamelist-fix vars)))
             (equal (bfr-env-override vars (bfr-set-var var val st) in)
                    (bfr-env-override vars st in)))
    :hints(("Goal" :in-theory (enable bfr-varnamelist-fix
                                      bfr-env-override)
            :induct (bfr-env-override vars st in))))
  
  (local (std::defret bfrmc-add-constraint-correct-lemma
           (implies (and ;; (not (bfr-depends-on constr-violated-var prop))
                     ;; (not (bfr-depends-on constr-violated-var constr))
                     ;; (not (pbfr-list-depends-on constr-violated-var t (alist-vals updates)))
                     (not (member (bfr-varname-fix constr-violated-var) (bfr-vars prop)))
                     (not (member (bfr-varname-fix constr-violated-var) (bfr-vars constr)))
                     (not (member (bfr-varname-fix constr-violated-var) (bfrlist-vars (alist-vals updates))))
                     (not (hons-assoc-equal (bfr-varname-fix constr-violated-var)
                                            (bfr-updates-fix updates))))
                    (implies (not (bfr-constrained-mcrun prop constr updates curr-st ins))
                             (not (bfr-mcrun new-prop new-updates (bfr-set-var constr-violated-var nil curr-st) ins))))
           :hints(("Goal" :in-theory (enable bfr-mcrun bfr-constrained-mcrun bfr-updates->states)
                   :induct (bfr-constrained-mcrun prop constr updates curr-st ins)
                   :expand ((:free (prop updates curr-st) (bfr-mcrun prop updates curr-st ins))
                            (:free (prop constr updates curr-st) (bfr-constrained-mcrun prop constr updates curr-st ins))
                            (:free (a c st in) (bfr-env-override (cons a c) st in))
                            (:free (a b c env) (bfr-eval-updates (cons (cons a b) c) env)))))))

  (local (std::defret bfrmc-add-constraint-correct-lemma2
           (implies (and (not (member (bfr-varname-fix constr-violated-var) (bfr-vars prop)))
                         (not (member (bfr-varname-fix constr-violated-var) (bfr-vars constr)))
                         (not (member (bfr-varname-fix constr-violated-var) (bfrlist-vars (alist-vals updates))))
                         (not (hons-assoc-equal (bfr-varname-fix constr-violated-var)
                                                (bfr-updates-fix updates))))
                    (implies (bfr-constrained-mcrun prop constr updates curr-st ins)
                             (bfr-mcrun new-prop new-updates (bfr-set-var constr-violated-var nil curr-st) ins)))
           :hints(("Goal" :in-theory (e/d (bfr-mcrun bfr-constrained-mcrun bfr-updates->states))
                   :induct (bfr-constrained-mcrun prop constr updates curr-st ins)
                   :expand ((:free (prop updates curr-st) (bfr-mcrun prop updates curr-st ins))
                            (:free (prop constr updates curr-st) (bfr-constrained-mcrun prop constr updates curr-st ins))
                            (:free (a c st in) (bfr-env-override (cons a c) st in))
                            (:free (a b c env) (bfr-eval-updates (cons (cons a b) c) env))))
                  (and stable-under-simplificationp
                       '(:use ((:instance bfrmc-add-constraint-when-violated
                                (curr-st (bfr-set-var constr-violated-var t
                                                      (bfr-eval-updates updates (bfr-mc-env updates curr-st (car ins)))))
                                (ins (cdr ins)))))))))

  (std::defret bfrmc-add-constraint-correct
    (implies (and (not (member (bfr-varname-fix constr-violated-var) (bfr-vars prop)))
                  (not (member (bfr-varname-fix constr-violated-var) (bfr-vars constr)))
                  (not (member (bfr-varname-fix constr-violated-var) (bfrlist-vars (alist-vals updates))))
                  (not (hons-assoc-equal (bfr-varname-fix constr-violated-var)
                                         (bfr-updates-fix updates))))
             (iff (bfr-mcrun new-prop new-updates (bfr-set-var constr-violated-var nil curr-st) ins)
                  (bfr-constrained-mcrun prop constr updates curr-st ins)))
    :hints(("Goal" :in-theory (disable bfrmc-add-constraint)))))


(include-book "std/lists/index-of" :dir :system)

(define bfr-varnames->bfrs ((x bfr-varnamelist-p))
  :returns (bfrs)
  (if (atom x)
      nil
    (cons (bfr-var (car x))
          (bfr-varnames->bfrs (cdr x))))
  ///
  (std::defret nth-of-bfr-varnames->bfrs
    (implies (< (nfix n) (len x))
             (equal (nth n bfrs)
                    (bfr-var (nth n x))))
    :hints(("Goal" :in-theory (enable nth)))))




(define bfr-ins-to-initst ((st-vars bfr-varnamelist-p)
                           (next-initst-var natp)
                           (env))
  :returns (initst)
  (if (atom st-vars)
      nil
    (bfr-set-var (car st-vars)
                 (bfr-lookup (lnfix next-initst-var) env)
                 (bfr-ins-to-initst (cdr st-vars)
                                    (1+ (lnfix next-initst-var))
                                    env)))
  ///
  (std::defret lookup-in-bfr-ins-to-initst
    (implies (member (bfr-varname-fix var) (bfr-varnamelist-fix st-vars))
             (equal (bfr-lookup var initst)
                    (bfr-lookup (+ (lnfix next-initst-var)
                                   (acl2::index-of (bfr-varname-fix var) (bfr-varnamelist-fix st-vars)))
                                env)))
    :hints(("Goal" :in-theory (enable acl2::index-of bfr-varnamelist-fix))))

  (std::defretd lookup-in-bfr-ins-to-initst-split
    ;; (implies 
    (equal (bfr-lookup var initst)
           (if (member (bfr-varname-fix var) (bfr-varnamelist-fix st-vars))
               (bfr-lookup (+ (lnfix next-initst-var)
                              (acl2::index-of (bfr-varname-fix var) (bfr-varnamelist-fix st-vars)))
                           env)
             (and (bfr-mode) t)))
    :hints(("Goal" :in-theory (enable acl2::index-of bfr-varnamelist-fix)
            :induct t)
           (and stable-under-simplificationp
                '(:in-theory (enable bfr-lookup)))))

  (defthm bfr-ins-to-initst-of-set-irrel-var
    (implies (and (natp (bfr-varname-fix var))
                  (< (bfr-varname-fix var) (nfix next-initst-var))
                  (bfr-varlist-bounded var st-vars))
             (equal (bfr-ins-to-initst st-vars next-initst-var (bfr-set-var var val env))
                    (bfr-ins-to-initst st-vars next-initst-var env)))
    :hints(("Goal" :in-theory (enable bfr-ins-to-initst bfr-varlist-bounded))))

  (local (defthm not-member-when-bfr-varlist-bounded
           (implies (and (bfr-varlist-bounded max-bvar st-vars1)
                         (<= (nfix max-bvar) (nfix next-initst-var)))
                    (not (member (nfix next-initst-var) (bfr-varnamelist-fix st-vars1))))
           :hints(("Goal" :in-theory (enable bfr-varlist-bounded bfr-varnamelist-fix)))))

  (defthm bfr-ins-to-initst-of-override-states
    (implies (and (bfr-varlist-bounded max-bvar st-vars1)
                  (<= (nfix max-bvar) (nfix next-initst-var)))
             (equal (bfr-ins-to-initst st-vars next-initst-var
                                       (bfr-env-override st-vars1 initst env))
                    (bfr-ins-to-initst st-vars next-initst-var env))))

  )

  ;; (std::defret bfr-eval-alist-of-initial-states-when-past-initcycle
  ;;   (implies (bfr-lookup past-initcycle env)
  ;;            (equal (bfr-alist-eval st-alist env)
  ;;                   (bfr-alist-eval (pairlis$ st-vars)

(define bfr-initial-states ((st-vars bfr-varnamelist-p)
                            (past-initcycle)
                            (next-initst-var natp))
  :returns (st-alist bfr-updates-p)
  (if (atom st-vars)
      nil
    (cons (cons (bfr-varname-fix (car st-vars))
                (bfr-ite past-initcycle
                         (bfr-var (car st-vars))
                         (bfr-var (lnfix next-initst-var))))
          (bfr-initial-states (cdr st-vars)
                              past-initcycle
                              (1+ (lnfix next-initst-var)))))
  ///
  (std::defret lookup-in-bfr-initial-states
    (equal (hons-assoc-equal k st-alist)
           (and (member k (bfr-varnamelist-fix st-vars))
                (cons k (bfr-ite past-initcycle
                                 (bfr-var k)
                                 (bfr-var (+ (acl2::index-of k (bfr-varnamelist-fix st-vars)) (nfix next-initst-var)))))))
    :hints(("Goal" :in-theory (enable bfr-varnamelist-fix acl2::index-of))))

  (std::defret bfr-updates->states-of-bfr-initial-states
    (equal (bfr-updates->states st-alist)
           (bfr-varnamelist-fix (list-fix st-vars)))
    :hints(("Goal" :in-theory (enable list-fix bfr-varnamelist-fix bfr-updates->states))))

  ;; (local (defthm hons-assoc-equal-in-pairlis$
  ;;          (equal (hons-assoc-equal k (pairlis$ a b))
  ;;                 (and (member k a)
  ;;                      (cons k (nth (acl2::index-of k a) b))))
  ;;          :hints(("Goal" :in-theory (enable hons-assoc-equal pairlis$ acl2::index-of)))))

  (local (defun nth-of-numlist-ind (n start by len)
           (if (zp n)
               (list start by len)
             (nth-of-numlist-ind (1- n) (+ start by) by (1- len)))))

  (local (defthm nth-of-numlist
           (implies (acl2-numberp start)
                    (equal (nth n (numlist start by len))
                           (and (< (nfix n) (nfix len))
                                (+ start (* (nfix n) by)))))
           :hints(("Goal" :in-theory (enable numlist nth)
                   :induct (nth-of-numlist-ind n start by len)
                   :expand ((numlist start by len))))))
                       
  (std::defret bfr-eval-updates-of-bfr-initial-states
    (bfr-env-equiv (bfr-eval-updates st-alist env)
                   (if (bfr-eval past-initcycle env)
                       (bfr-normalize-env (bfr-varnamelist-fix st-vars) env)
                     (bfr-ins-to-initst st-vars next-initst-var env)
                     ;; (bfr-eval-updates (pairlis$ (bfr-varnamelist-fix st-vars)
                     ;;                             (bfr-varnames->bfrs
                     ;;                              (acl2::numlist (nfix next-initst-var) 1 (len st-vars))))
                     ;;                   env)
                     ))
    :hints(("Goal" :in-theory (enable bfr-env-equiv
                                      bfr-lookup-of-bfr-eval-updates-split
                                      lookup-in-bfr-ins-to-initst-split)
            :do-not-induct t))))

(defthm bfr-varnamlist-p-alist-keys-of-updates
  (implies (bfr-updates-p updates)
           (bfr-varnamelist-p (Alist-keys updates)))
  :hints(("Goal" :in-theory (enable alist-keys bfr-updates-p))))

(defthm bfr-updates-p-of-aig-restrict-alist
  (implies (bfr-updates-p x)
           (bfr-updates-p (acl2::aig-restrict-alist x subst)))
  :hints(("Goal" :in-theory (enable bfr-updates-p acl2::aig-restrict-alist))))


(local (defthm aig-env-lookup-of-bfr-env-override
         (implies (And (bfr-mode) (bfr-varname-p k))
                  (equal (acl2::aig-env-lookup k (bfr-env-override vars a b))
                         (if (member k (bfr-varnamelist-fix vars))
                             (acl2::aig-env-lookup k a)
                           (acl2::aig-env-lookup k b))))
         :hints(("Goal" :use ((:instance LOOKUP-IN-BFR-ENV-OVERRIDE
                               (v k) (override-vars vars) (override-env a) (env b)))
                 :in-theory (e/d (bfr-lookup) (lookup-in-bfr-env-override acl2::aig-env-lookup))))))

(local (defthm aig-env-lookup-of-bfr-eval-updates
         (implies (and (bfr-varname-p k)
                       (bfr-mode))
                  (equal (acl2::aig-env-lookup k  (bfr-eval-updates a env))
                         (if (hons-assoc-equal k a)
                             (bfr-eval (cdr (hons-assoc-equal k a)) env)
                           t)))
         :hints(("Goal" :use ((:instance bfr-lookup-of-bfr-eval-updates-split
                               (v k) (updates a)))
                 :in-theory (e/d (bfr-lookup) (bfr-lookup-of-bfr-eval-updates-split))))))



(local (defthm bfr-aig-eval-of-aig-restrict
         (implies (bfr-mode)
                  (equal (acl2::aig-eval (acl2::aig-restrict x a) env)
                         (acl2::aig-eval x (bfr-env-override (bfr-updates->states a)
                                                             (bfr-eval-updates a env)
                                                             env))))
         :hints(("Goal" :in-theory (e/d (bfr-eval acl2::aig-eval acl2::aig-restrict
                                                  bfr-varname-p)
                                        (acl2::aig-env-lookup))
                 :induct (acl2::aig-restrict x a)))))

(local (defthm bfr-eval-of-aig-restrict
         (implies (bfr-mode)
                  (equal (bfr-eval (acl2::aig-restrict x a) env)
                         (bfr-eval x (bfr-env-override (bfr-updates->states a)
                                                       (bfr-eval-updates a env)
                                                       env))))
         :hints(("Goal" :in-theory (enable bfr-eval)))))

(local (defthm bfr-eval-updates-of-aig-restrict
         (implies (bfr-mode)
                  (equal (bfr-eval-updates (acl2::aig-restrict-alist x a) env)
                         (bfr-eval-updates x (bfr-env-override (bfr-updates->states a)
                                                               (bfr-eval-updates a env)
                                                               env))))
         :hints(("Goal" :in-theory (enable bfr-eval-updates acl2::aig-restrict-alist)))))


(defthm bfr-env-override-of-bfr-normalize-env
  (implies (subsetp (bfr-varnamelist-fix vars) vars1)
           (equal (bfr-env-override vars (bfr-normalize-env vars1 a) b)
                  (bfr-env-override vars a b)))
  :hints(("Goal" :in-theory (enable bfr-env-override subsetp))))


(defthm bfr-env-override-of-bfr-env-override
  (implies (subsetp (bfr-varnamelist-fix vars2) (bfr-varnamelist-fix vars1))
           (bfr-env-equiv (bfr-env-override vars1 a (bfr-env-override vars2 b c))
                          (bfr-env-override vars1 a c)))
  :hints(("Goal" :in-theory (enable bfr-env-equiv))))

(defthm bfr-env-override-subset-of-bfr-env-override
  (implies (subsetp (bfr-varnamelist-fix vars1) (bfr-varnamelist-fix vars2))
           (bfr-env-equiv (bfr-env-override vars1 a (bfr-env-override vars2 a b))
                          (bfr-env-override vars2 a b)))
  :hints(("Goal" :in-theory (enable bfr-env-equiv))))

(defthm not-member-vars-when-pbfr-vars-bounded
  (implies (and (pbfr-vars-bounded max-bvar t x)
                (bfr-varname-p var)
                (bfr-mode)
                (or (not (natp var))
                    (<= (nfix max-bvar) var)))
           (not (member var (bfr-vars x))))
  :hints (("goal" :use ((:instance pbfr-vars-bounded-necc
                         (n max-bvar) (p t) (m var)))
           :in-theory (enable pbfr-depends-on bfr-depends-on bfr-from-param-space
                              set::in-to-member bfr-vars))))

(defthm bfr-eval-updates-of-bfr-env-override-set-irrel-in-var
    (implies (and (pbfr-list-vars-bounded max-bvar t (alist-vals updates))
                  (natp (bfr-varname-fix var))
                  (bfr-mode)
                  (<= (nfix max-bvar) (bfr-varname-fix var)))
             (equal (bfr-eval-updates updates (bfr-env-override vars st (bfr-set-var var val in)))
                    (bfr-eval-updates updates (bfr-env-override vars st in))))
    :hints(("Goal" :in-theory (enable bfr-eval-updates alist-vals pbfr-list-vars-bounded))))

(defthm bfr-env-override-identity
  (bfr-env-equiv (bfr-env-override vars env env)
                 env)
  :hints(("Goal" :in-theory (enable bfr-env-equiv))))


(local (include-book "centaur/aig/aig-vars" :dir :system))

#!acl2
(encapsulate nil
  (local (defthm keys-of-aig-extract-assigns
           (b* (((mv trues falses) (aig-extract-assigns x)))
             (implies (not (member v (aig-vars x)))
                      (and (not (member v trues))
                           (not (member v falses)))))
           :hints(("Goal" :in-theory (enable aig-extract-assigns
                                             aig-vars)))))

  (local (defthm key-of-aig-extract-assigns-alist
           (implies (not (member v (aig-vars x)))
                    (not (hons-assoc-equal v (aig-extract-assigns-alist x))))
           :hints(("Goal" :in-theory (enable aig-extract-assigns-alist)))))

  (local (defthm aig-vars-of-assign-var-list
           (implies (booleanp val)
                    (equal (acl2::aiglist-vars (alist-vals (assign-var-list x val))) nil))
           :hints(("Goal" :in-theory (enable assign-var-list alist-vals acl2::aiglist-vars)))))


  

  ;; (local (defthm alist-vals-of-append
  ;;          (equal (alist-vals (append a b))
  ;;                 (append (alist-vals a) (alist-vals b)))
  ;;          :hints(("Goal" :in-theory (enable alist-vals)))))

  (defthm setp-of-aiglist-vars
    (set::setp (acl2::aiglist-vars x))
    :hints(("Goal" :in-theory (enable acl2::aiglist-vars))))

  (local (defthm aig-vars-of-append
           (equal (acl2::aiglist-vars (append a b))
                  (set::union (acl2::aiglist-vars a) (acl2::aiglist-vars b)))
           :hints(("Goal" :in-theory (enable acl2::aiglist-vars)))))

  (local (defthm aig-vars-of-aig-extract-assigns-alist-vals
           (equal (acl2::aiglist-vars (alist-vals (aig-extract-assigns-alist x))) nil)
           :hints(("Goal" :in-theory (enable aig-extract-assigns-alist)))))

  ;; (local (defthm member-aig-vars-of-aig-and
  ;;          (implies (and (not (member v (aig-vars x)))
  ;;                        (not (member v (aig-vars y))))
  ;;                   (not (member v (aig-vars (aig-and x y)))))
  ;;          :hints (("goal" :cases ((set::in v (aig-vars (aig-and x y))))))))

  (local (defthm aig-vars-of-restrict
           (implies (and (not (member v (acl2::aiglist-vars (alist-vals a))))
                         (not (and (member v (aig-vars x))
                                   (not (hons-assoc-equal v a)))))
                    (not (member v (aig-vars (aig-restrict x a)))))
           :hints(("Goal" :use ((:instance member-aig-vars-aig-restrict
                                 (al a)))
                   :in-theory (e/d (set::in-to-member) (member-aig-vars-aig-restrict))))))
                    

  (defthm key-of-aig-extract-iterated-assigns-alist
    (implies (and (not (member v (gl::bfr-vars x)))
                  (gl::bfr-mode))
             (not (hons-assoc-equal v (aig-extract-iterated-assigns-alist x n))))
    :hints(("Goal" :in-theory (enable aig-extract-iterated-assigns-alist
                                      gl::bfr-vars)))))

(defthm bfr-varnamelist-p-of-aig-extract-assigns
  (b* (((mv trues falses) (acl2::aig-extract-assigns x)))
    (implies (bfr-mode)
             (and (bfr-varnamelist-p trues)
                  (bfr-varnamelist-p falses))))
  :hints(("Goal" :in-theory (enable acl2::aig-extract-assigns))))

(defthm bfr-updates-p-of-assign-var-list
  (implies (bfr-varnamelist-p x)
           (bfr-updates-p (acl2::assign-var-list x val)))
  :hints(("Goal" :in-theory (enable acl2::assign-var-list bfr-updates-p bfr-varnamelist-p))))

(defthm bfr-updates-p-of-aig-extract-assigns-alist
  (implies (bfr-mode)
           (bfr-updates-p (acl2::aig-extract-assigns-alist x)))
  :hints(("Goal" :in-theory (enable acl2::aig-extract-assigns-alist))))

(defthm bfr-updates-p-of-aig-extract-iterated-assigns-alist
  (implies (bfr-mode)
           (bfr-updates-p (acl2::aig-extract-iterated-assigns-alist x n)))
  :hints(("Goal" :in-theory (enable acl2::aig-extract-iterated-assigns-alist))))

(local (defthmd bfr-varname-p-when-lookup-in-bfr-updates
         (implies (and (hons-assoc-equal k x)
                       (bfr-updates-p x))
                  (bfr-varname-p k))
         :hints(("Goal" :in-theory (enable bfr-updates-p)))))

(local (defthm bfr-updates-p-of-fal-extract
         (implies (bfr-updates-p x)
                  (bfr-updates-p (acl2::fal-extract keys x)))
         :hints(("Goal" :in-theory (enable acl2::fal-extract
                                           bfr-varname-p-when-lookup-in-bfr-updates)))))

(define bfrmc-set-initst-pred ((prop)
                               (constr)
                               (updates bfr-updates-p)
                               (initstp)
                               (max-bvar natp))
  :returns (mv (new-prop)
               (new-constr)
               (new-updates bfr-updates-p)
               (new-initst bfr-updates-p :hyp (bfr-mode))
               (next-bvar natp :rule-classes :type-prescription))
  :guard (bfr-mode)
  (b* ((past-initcycle-var (lnfix max-bvar))
       (state-vars (bfr-updates->states updates))
       (consts-from-initstp (acl2::fal-extract state-vars
                                               (acl2::aig-extract-iterated-assigns-alist initstp 10)))
       (const-initsts (cons (cons past-initcycle-var nil)
                            consts-from-initstp))
       (variable-sts (acl2::hons-set-diff (bfr-updates->states updates)
                                          (bfr-updates->states const-initsts)))
       (initst-subst (make-fast-alist
                      (bfr-initial-states variable-sts
                                          (bfr-var past-initcycle-var)
                                          (1+ past-initcycle-var))))
       (next-var (+ 1 past-initcycle-var (len variable-sts)))
       (new-prop (acl2::aig-restrict prop initst-subst))
       (new-initstp (acl2::aig-restrict (acl2::with-fast-alist const-initsts
                                          (acl2::aig-restrict initstp const-initsts))
                                        initst-subst))
       (new-constr1 (acl2::aig-restrict constr initst-subst))
       (new-constr  (bfr-and (bfr-or (bfr-var past-initcycle-var)
                                     new-initstp)
                             new-constr1))
       (new-updates1 (acl2::aig-restrict-alist (bfr-updates-fix updates) initst-subst))
       (new-updates (cons (cons past-initcycle-var t) new-updates1)))
    (fast-alist-free initst-subst)
    (mv new-prop new-constr new-updates
        (make-fast-alist const-initsts) next-var))
  ///
  (local (defthm bfr-updates->states-of-aig-restrict-alist
           (Equal (bfr-updates->states (acl2::aig-restrict-alist x a))
                  (bfr-updates->states x))
           :hints(("Goal" :in-theory (enable bfr-updates->states acl2::aig-restrict-alist)))))

  (local (defthm lookup-in-updates-when-bfr-varlist-bounded
           (implies (bfr-varlist-bounded max-bvar (bfr-updates->states updates))
                    (not (hons-assoc-equal (nfix max-bvar) updates)))
           :hints(("Goal" :in-theory (enable bfr-varlist-bounded bfr-updates->states hons-assoc-equal)))))

  (local (defthm member-bfr-vars-when-pbfr-vars-bounded
           (implies (and (pbfr-vars-bounded max p x)
                         (bfr-mode))
                    (not (member (nfix max) (bfr-vars x))))
           :hints(("Goal" :use ((:instance pbfr-vars-bounded-necc (n max)
                                 (m (nfix max))))
                   :in-theory (enable pbfr-depends-on bfr-depends-on bfr-from-param-space bfr-vars
                                      set::in-to-member)))))

  (local (defthm bfr-lookup-in-fal-extract
           (implies (bfr-mode)
                    (equal (bfr-lookup k (acl2::fal-extract vars x))
                           (if (member (bfr-varname-fix k) vars)
                               (bfr-lookup k x)
                             t)))
           :hints(("Goal" :in-theory (enable bfr-lookup)))))

  (local (defthm bfr-updates->states-of-fal-extract
           (equal (bfr-updates->states (acl2::fal-extract vars x))
                  (intersection$ vars (bfr-updates->states x)))
           :hints(("Goal" :in-theory (enable bfr-updates->states acl2::fal-extract intersection$)))))

  (local (defthm bfr-lookup-of-cons
           (implies (bfr-mode)
                    (equal (bfr-lookup k (cons (cons a b) c))
                           (if (equal (bfr-varname-fix k) a)
                               (bool-fix b)
                             (bfr-lookup k c))))
           :hints(("Goal" :in-theory (enable bfr-lookup)))))

  (std::defret bfrmc-set-initst-pred-later-cycles
    (implies (and (consp ins)
                  (bfr-mode)
                  (pbfr-vars-bounded max-bvar t prop)
                  (pbfr-vars-bounded max-bvar t constr)
                  (pbfr-vars-bounded max-bvar t initstp)
                  (pbfr-list-vars-bounded max-bvar t (alist-vals (bfr-updates-fix updates)))
                  (bfr-varlist-bounded max-bvar (bfr-updates->states updates)))
             (iff (bfr-constrained-mcrun new-prop new-constr new-updates
                                         ;; Past initial state:
                                         (bfr-set-var (nfix max-bvar) t curr-st)
                                         ins)
                  (bfr-constrained-mcrun prop constr updates curr-st ins)))
    :hints (("goal" :induct (bfr-constrained-mcrun prop constr updates curr-st ins)
             :in-theory (enable bfr-constrained-mcrun
                                bfr-env-override
                                bfr-updates->states
                                bfr-eval-updates)
             :expand ((:free (prop constr updates curr-st)
                       (bfr-constrained-mcrun prop constr updates curr-st ins))))))

  ;; (defthm bfr-eval-of-override-var-superset
  ;;   (implies (subsetp (bfr-vars x) (bfr-varnamelist-fix vars))
  ;;            (equal (bfr-eval x (bfr-env-override vars a b))
  ;;                   (bfr-eval x a)))
  ;;   :hints (("goal" :use ((:instance bfr-eval-of-normalize-env
  ;;                          (vars (bfr-varnamelist-fix vars))
  ;;                          (env (Bfr-env-override vars a b)))
  ;;                         (:instance bfr-eval-of-normalize-env
  ;;                          (vars (bfr-varnamelist-fix vars))
  ;;                          (env a)))
  ;;            :in-theory (disable bfr-eval-of-normalize-env))))

  (defthm bfr-varlist-bounded-of-set-diff
    (implies (bfr-varlist-bounded k a)
             (bfr-varlist-bounded k (set-difference$ a b)))
    :hints(("Goal" :in-theory (enable set-difference$ bfr-varlist-bounded))))

  ;; (local (defthm not-member-aig-vars-when-pbfr-vars-bounded
  ;;          (implies (and (pbfr-vars-bounded max t x)
  ;;                        (integerp (bfr-varname-fix v))
  ;;                        (<= (nfix max) (bfr-varname-fix v)))
  ;;                   (not (member v (acl

  ;; (local (defthm 


  (local (defthm bfr-eval-lookup-of-boolean-val-alist
           (implies (acl2::boolean-val-alistp x)
                    (equal (bfr-eval (cdr (hons-assoc-equal k x)) env)
                           (cdr (hons-assoc-equal k x))))
           :hints(("Goal" :in-theory (enable hons-assoc-equal acl2::boolean-val-alistp)))))

  (local (defthm boolean-val-alist-of-fal-extract
           (implies (acl2::boolean-val-alistp x)
                    (acl2::boolean-val-alistp (acl2::fal-extract vars x)))
           :hints(("Goal" :in-theory (enable acl2::fal-extract acl2::boolean-val-alistp)))))

  (local (defthm bfr-eval-updates-of-boolean-val-alist
           (implies (and (acl2::boolean-val-alistp x) (bfr-mode))
                    (bfr-env-equiv (bfr-eval-updates x env)
                                   x))
           :hints(("Goal" :in-theory (enable bfr-env-equiv
                                             bfr-lookup-of-bfr-eval-updates-split))
                  (and stable-under-simplificationp
                       '(:in-theory (enable bfr-lookup acl2::aig-env-lookup))))))


  (local (defthm set-difference-of-cons-irrel
           (implies (not (member a x))
                    (equal (set-difference$ x (cons a y))
                           (set-difference$ x y)))
           :hints(("Goal" :in-theory (enable set-difference$)))))

  (local (defthm bfr-lookup-when-in-iterated-assigns-alist
           (implies (and (bfr-eval x env)
                         (hons-assoc-equal (bfr-varname-fix k) (acl2::aig-extract-iterated-assigns-alist x n))
                         (bfr-mode))
                    (equal (bfr-lookup k env)
                           (bfr-lookup k (acl2::aig-extract-iterated-assigns-alist x n))))
           :hints (("goal" :in-theory (enable bfr-eval bfr-lookup acl2::aig-env-lookup)
                    :use ((:instance acl2::lookup-in-aig-extract-iterated-assigns-alist
                           (v (bfr-varname-fix k)) (env env) (x x) (n n)))
                    :do-not-induct t))))

  ;; (local (defthm env-override-of-iterated-assigns
  ;;          (implies (and ; (subsetp (bfr-vars initstp) states)
  ;;                        (bfr-varnamelist-p states)
  ;;                        (bfr-mode))
  ;;                   (bfr-env-equiv (bfr-normalize-env states
  ;;                                                     (bfr-env-override
  ;;                                                      (bfr-updates->states (acl2::aig-extract-iterated-assigns-alist initstp n))
  ;;                                                      (acl2::aig-extract-iterated-assigns-alist initstp n)
  ;;                                                      (bfr-env-override
  ;;                                                       (set-difference$ states
  ;;                                                                        (bfr-updates->states (acl2::aig-extract-iterated-assigns-alist initstp n)))
  ;;                                                       env
  ;;                                                       env2)))
  ;;                                  (bfr-normalize-env states
  ;;                                                     (bfr-env-override
  ;;                                                      (bfr-updates->states (acl2::aig-extract-iterated-assigns-alist initstp n))
  ;;                                                      (acl2::aig-extract-iterated-assigns-alist initstp n)
  ;;                                                      env))))
  ;;          :hints(("Goal" :in-theory (enable bfr-env-equiv)
  ;;                  :do-not-induct t))))

  ;; (local (defthm eval-env-override-of-iterated-assigns
  ;;          (implies (and ; (subsetp (bfr-vars initstp) states)
  ;;                        (bfr-varnamelist-p states)
  ;;                        (bfr-mode))
  ;;                   (equal (bfr-eval initstp (bfr-env-override
  ;;                                             (bfr-updates->states (acl2::aig-extract-iterated-assigns-alist initstp n))
  ;;                                             (acl2::aig-extract-iterated-assigns-alist initstp n)
  ;;                                             (bfr-env-override
  ;;                                              (set-difference$ states
  ;;                                                               (bfr-updates->states (acl2::aig-extract-iterated-assigns-alist initstp n)))
  ;;                                              env
  ;;                                              env2)))
  ;;                          (bfr-eval initstp (bfr-env-override
  ;;                                             (bfr-updates->states (acl2::aig-extract-iterated-assigns-alist initstp n))
  ;;                                             (acl2::aig-extract-iterated-assigns-alist initstp n)
  ;;                                             env))))
  ;;          :hints (("goal" :use ((:instance bfr-eval-of-normalize-env
  ;;                                 (vars states) (x initstp)
  ;;                                 (env (bfr-env-override
  ;;                                       (bfr-updates->states (acl2::aig-extract-iterated-assigns-alist initstp n))
  ;;                                       (acl2::aig-extract-iterated-assigns-alist initstp n)
  ;;                                       (bfr-env-override
  ;;                                        (set-difference$ states
  ;;                                                         (bfr-updates->states (acl2::aig-extract-iterated-assigns-alist initstp n)))
  ;;                                        env
  ;;                                        env2))))
  ;;                                (:instance bfr-eval-of-normalize-env
  ;;                                 (vars states) (x initstp)
  ;;                                 (env (bfr-env-override
  ;;                                             (bfr-updates->states (acl2::aig-extract-iterated-assigns-alist initstp n))
  ;;                                             (acl2::aig-extract-iterated-assigns-alist initstp n)
  ;;                                             env))))
  ;;                   :in-theory (disable bfr-eval-of-normalize-env)))))


  (local (defthm bfr-env-override-of-cons-irrel
           (implies (and (not (member (bfr-varname-fix var) (bfr-varnamelist-fix vars)))
                         (bfr-mode))
                    (equal (bfr-env-override vars (cons (cons var val) env) env2)
                           (bfr-env-override vars env env2)))
           :hints(("Goal" :in-theory (enable bfr-env-override bfr-varnamelist-fix)))))


  (local (defthm bfr-env-equiv-of-override-states-blah1
           (implies (and (bfr-varnamelist-p states)
                         (bfr-varnamelist-p const-state-vars))
                    (bfr-env-equiv (bfr-env-override (set-difference$ states const-state-vars)
                                                     ins-to-initsts
                                                     (bfr-env-override states const-states ins))
                                   (bfr-env-override states
                                                     (bfr-env-override const-state-vars
                                                                       const-states
                                                                       ins-to-initsts)
                                                     ins)))
           :hints(("Goal" :in-theory (enable bfr-env-equiv)))))

  (local (defthmd bfr-varlist-bounded-implies-not-member
           (implies (and (bfr-varlist-bounded max-bvar vars)
                         (or (not (natp var))
                             (<= (nfix max-bvar) var)))
                    (not (member var (bfr-varnamelist-fix vars))))
           :hints(("Goal" :in-theory (enable bfr-varlist-bounded bfr-varnamelist-fix)))))

  ;; (local (defthm pbfr-vars-bounded-when-subsetp
  ;;          (implies (and (bfr-varlist-bounded max-bvar vars)
  ;;                        (subsetp (bfr-vars x) (bfr-varnamelist-fix vars))
  ;;                        (bfr-mode))
  ;;                   (pbfr-vars-bounded max-bvar t x))
  ;;          :hints(("Goal" :in-theory (enable pbfr-vars-bounded
  ;;                                            pbfr-depends-on
  ;;                                            bfr-depends-on
  ;;                                            bfr-from-param-space
  ;;                                            bfr-vars
  ;;                                            set::in-to-member
  ;;                                            bfr-varlist-bounded-implies-not-member)))))


  (local (defthmd equal-of-bfr-eval-to-equal-normalize
           (iff (equal (bfr-eval x env1) (bfr-eval x env2))
                (or (hide (equal (bfr-eval x env1) (bfr-eval x env2)))
                    (bfr-env-equiv (bfr-normalize-env (bfr-vars x) env1)
                                   (bfr-normalize-env (bfr-vars x) env2))))
           :hints (("goal" :expand ((:free (x) (hide x)))
                    :use ((:instance BFR-EVAL-OF-NORMALIZE-ENV
                           (vars (bfr-vars x))
                           (env env1))
                          (:instance BFR-EVAL-OF-NORMALIZE-ENV
                           (vars (bfr-vars x))
                           (env env2)))
                    :in-theory (disable bfr-eval-of-normalize-env)))))

  (local (defthmd set-difference-of-intersection-with-subset
           (implies (subsetp a b)
                    (equal (set-difference$ a (intersection$ b c))
                           (set-difference$ a c)))
           :hints(("Goal" :in-theory (enable set-difference$ intersection$)))))

  (local (defthm set-difference-of-intersection
           (equal (set-difference$ a (intersection$ a b))
                  (set-difference$ a b))
           :hints(("Goal" :in-theory (enable set-difference-of-intersection-with-subset)))))

  (local (defthm env-equiv-lemma1
           (implies (and (pbfr-vars-bounded max-bvar t initstp)
                         (bfr-mode))
                    (equal (bfr-eval initstp
                                     (BFR-ENV-OVERRIDE
                                      (intersection$
                                       (bfr-updates->states updates)
                                       (BFR-UPDATES->STATES
                                        (ACL2::AIG-EXTRACT-ITERATED-ASSIGNS-ALIST INITSTP 10)))
                                      (acl2::fal-extract
                                       (bfr-updates->states updates)
                                       (ACL2::AIG-EXTRACT-ITERATED-ASSIGNS-ALIST INITSTP 10))
                                      (BFR-ENV-OVERRIDE
                                       (SET-DIFFERENCE-EQUAL
                                        (BFR-UPDATES->STATES UPDATES)
                                        (BFR-UPDATES->STATES
                                         (ACL2::AIG-EXTRACT-ITERATED-ASSIGNS-ALIST INITSTP 10)))
                                       (BFR-INS-TO-INITST
                                        (SET-DIFFERENCE-EQUAL
                                         (BFR-UPDATES->STATES UPDATES)
                                         (BFR-UPDATES->STATES
                                          (ACL2::AIG-EXTRACT-ITERATED-ASSIGNS-ALIST INITSTP 10)))
                                        (+ 1 (NFIX MAX-BVAR))
                                        (CAR INS))
                                       (BFR-SET-VAR (NFIX MAX-BVAR)
                                                    NIL
                                                    (BFR-ENV-OVERRIDE
                                                     (BFR-UPDATES->STATES UPDATES)
                                                     (acl2::fal-extract
                                                      (bfr-updates->states updates)
                                                      (ACL2::AIG-EXTRACT-ITERATED-ASSIGNS-ALIST INITSTP 10))
                                                     (CAR INS))))))
                           (bfr-eval initstp (BFR-ENV-OVERRIDE
                                              (intersection$
                                               (bfr-updates->states updates)
                                               (BFR-UPDATES->STATES
                                                (ACL2::AIG-EXTRACT-ITERATED-ASSIGNS-ALIST INITSTP 10)))
                                              (acl2::fal-extract
                                               (bfr-updates->states updates)
                                               (ACL2::AIG-EXTRACT-ITERATED-ASSIGNS-ALIST INITSTP 10))
                                              (BFR-ENV-OVERRIDE
                                               (SET-DIFFERENCE-EQUAL
                                                (BFR-UPDATES->STATES UPDATES)
                                                (BFR-UPDATES->STATES
                                                 (ACL2::AIG-EXTRACT-ITERATED-ASSIGNS-ALIST INITSTP 10)))
                                               (BFR-INS-TO-INITST
                                                (SET-DIFFERENCE-EQUAL
                                                 (BFR-UPDATES->STATES UPDATES)
                                                 (BFR-UPDATES->STATES
                                                  (ACL2::AIG-EXTRACT-ITERATED-ASSIGNS-ALIST INITSTP 10)))
                                                (+ 1 (NFIX MAX-BVAR))
                                                (CAR INS))
                                               (CAR INS))))))
           :hints(("Goal" :in-theory (enable equal-of-bfr-eval-to-equal-normalize bfr-env-equiv))
                  (and stable-under-simplificationp
                       '(:in-theory (enable bfr-lookup))))))

  (local (defthm env-equiv-lemma2
           (implies (and (pbfr-vars-bounded max-bvar t constr)
                         (bfr-mode))
                    (equal (bfr-eval constr
                                     (BFR-ENV-OVERRIDE
                                      (BFR-UPDATES->STATES UPDATES)
                                      (BFR-ENV-OVERRIDE
                                       (INTERSECTION-EQUAL
                                        (BFR-UPDATES->STATES UPDATES)
                                        (BFR-UPDATES->STATES
                                         (ACL2::AIG-EXTRACT-ITERATED-ASSIGNS-ALIST INITSTP 10)))
                                       (ACL2::FAL-EXTRACT
                                        (BFR-UPDATES->STATES UPDATES)
                                        (ACL2::AIG-EXTRACT-ITERATED-ASSIGNS-ALIST INITSTP 10))
                                       (BFR-ENV-OVERRIDE
                                        (SET-DIFFERENCE-EQUAL
                                         (BFR-UPDATES->STATES UPDATES)
                                         (BFR-UPDATES->STATES
                                          (ACL2::AIG-EXTRACT-ITERATED-ASSIGNS-ALIST INITSTP 10)))
                                        (BFR-INS-TO-INITST
                                         (SET-DIFFERENCE-EQUAL
                                          (BFR-UPDATES->STATES UPDATES)
                                          (BFR-UPDATES->STATES
                                           (ACL2::AIG-EXTRACT-ITERATED-ASSIGNS-ALIST INITSTP 10)))
                                         (+ 1 (NFIX MAX-BVAR))
                                         (CAR INS))
                                        (CAR INS)))
                                      (CAR INS)))
                           (bfr-eval constr
                                     (BFR-ENV-OVERRIDE
                                      (BFR-UPDATES->STATES UPDATES)
                                      (BFR-ENV-OVERRIDE
                                       (BFR-UPDATES->STATES
                                        (ACL2::AIG-EXTRACT-ITERATED-ASSIGNS-ALIST INITSTP 10))
                                       (ACL2::FAL-EXTRACT
                                        (BFR-UPDATES->STATES UPDATES)
                                        (ACL2::AIG-EXTRACT-ITERATED-ASSIGNS-ALIST INITSTP 10))
                                       (BFR-INS-TO-INITST
                                        (SET-DIFFERENCE-EQUAL
                                         (BFR-UPDATES->STATES UPDATES)
                                         (BFR-UPDATES->STATES
                                          (ACL2::AIG-EXTRACT-ITERATED-ASSIGNS-ALIST INITSTP 10)))
                                        (+ 1 (NFIX MAX-BVAR))
                                        (CAR INS)))
                                      (CAR INS)))))
           :hints(("Goal" :in-theory (enable equal-of-bfr-eval-to-equal-normalize bfr-env-equiv)))))

  ;; (local (defthm env-equiv-lemma3
  ;;          (bfr-env-equiv (BFR-ENV-OVERRIDE
  ;;                          (BFR-UPDATES->STATES UPDATES)
  ;;                          (BFR-ENV-OVERRIDE
  ;;                           (BFR-UPDATES->STATES
  ;;                            (ACL2::AIG-EXTRACT-ITERATED-ASSIGNS-ALIST INITSTP 10))
  ;;                           (ACL2::AIG-EXTRACT-ITERATED-ASSIGNS-ALIST INITSTP 10)
  ;;                           (BFR-ENV-OVERRIDE
  ;;                            (SET-DIFFERENCE-EQUAL
  ;;                             (BFR-UPDATES->STATES UPDATES)
  ;;                             (BFR-UPDATES->STATES
  ;;                              (ACL2::AIG-EXTRACT-ITERATED-ASSIGNS-ALIST INITSTP 10)))
  ;;                            (BFR-INS-TO-INITST
  ;;                             (SET-DIFFERENCE-EQUAL
  ;;                              (BFR-UPDATES->STATES UPDATES)
  ;;                              (BFR-UPDATES->STATES
  ;;                               (ACL2::AIG-EXTRACT-ITERATED-ASSIGNS-ALIST INITSTP 10)))
  ;;                             (+ 1 (NFIX MAX-BVAR))
  ;;                             (CAR INS))
  ;;                            (CAR INS)))
  ;;                          (CAR INS))
  ;;                         (BFR-ENV-OVERRIDE
  ;;                          (BFR-UPDATES->STATES UPDATES)
  ;;                          (BFR-ENV-OVERRIDE
  ;;                           (BFR-UPDATES->STATES
  ;;                            (ACL2::AIG-EXTRACT-ITERATED-ASSIGNS-ALIST INITSTP 10))
  ;;                           (ACL2::AIG-EXTRACT-ITERATED-ASSIGNS-ALIST INITSTP 10)
  ;;                           (BFR-INS-TO-INITST
  ;;                            (SET-DIFFERENCE-EQUAL
  ;;                             (BFR-UPDATES->STATES UPDATES)
  ;;                             (BFR-UPDATES->STATES
  ;;                              (ACL2::AIG-EXTRACT-ITERATED-ASSIGNS-ALIST INITSTP 10)))
  ;;                            (+ 1 (NFIX MAX-BVAR))
  ;;                            (CAR INS)))
  ;;                          (CAR INS)))
  ;;          :hints(("Goal" :in-theory (enable bfr-env-equiv)))))

  (local (defthm bfr-varnamelist-p-of-intersection
           (implies (bfr-varnamelist-p a)
                    (bfr-varnamelist-p (intersection$ a b)))
           :hints(("Goal" :in-theory (enable intersection$)))))

  (local (defthm bfr-varnamelist-p-of-set-diff
           (implies (bfr-varnamelist-p a)
                    (bfr-varnamelist-p (set-difference-equal a b)))
           :hints(("Goal" :in-theory (enable set-difference-equal)))))


  (local (defthm env-override-of-env-override-intersection
           (implies (and (bfr-varnamelist-p a)
                         (bfr-varnamelist-p b))
                    (bfr-env-equiv (bfr-env-override a
                                                     (bfr-env-override (intersection$ a b) env1 env2)
                                                     env3)
                                   (bfr-env-override a
                                                     (bfr-env-override b env1 env2)
                                                     env3)))
           :hints(("Goal" :in-theory (enable bfr-env-equiv)))))

  (local (defthm env-override-of-env-override-difference
           (implies (and (bfr-varnamelist-p a)
                         (bfr-varnamelist-p b))
                    (bfr-env-equiv (bfr-env-override a
                                                     env1
                                                     (bfr-env-override (set-difference$ b a) env2 env3))
                                   (bfr-env-override a env1
                                                     (bfr-env-override b env2 env3))))
           :hints(("Goal" :in-theory (enable bfr-env-equiv)))))

  (local (defthm env-override-of-env-override-of-env-override
           (implies (and (bfr-varnamelist-p a)
                         (bfr-varnamelist-p b))
                    (bfr-env-equiv (bfr-env-override
                                    a (bfr-env-override b env1 (bfr-env-override a env2 env3)) env4)
                                   (bfr-env-override a (bfr-env-override b env1 env2) env4)))
           :hints(("Goal" :in-theory (enable bfr-env-equiv)))))

  ;; (local (defthm bfr-env-override-of-intersection-of-env-override-of-difference
  ;;          (implies (and (bfr-varnamelist-p a)
  ;;                        (bfr-varnamelist-p b))
  ;;                   (bfr-env-equiv
  ;;                    (bfr-env-override (intersection-equal a b)
  ;;                                      env1
  ;;                                      (bfr-env-override (set-difference-equal a b)
  ;;                                                        env2 env3))
  ;;                    (bfr-env-override (intersection-equal a b) env1 env2)))
  ;;          :hints(("Goal" :in-theory (enable bfr-env-equiv)))))


  (local (defthm bfr-eval-of-env-override-cons-irrel
           (implies (not (member (bfr-varname-fix var) (bfr-vars x)))
                    (equal (bfr-eval x (bfr-env-override (cons var vars) a b))
                           (bfr-eval x (bfr-env-override vars a b))))
           :hints(("Goal" :in-theory (enable bfr-env-override)))))


  (local (in-theory (disable acl2::aig-restrict acl2::aig-extract-iterated-assigns-alist
                             acl2::consp-when-member-equal-of-atom-listp
                             lookup-in-bfr-ins-to-initst
                             nat-listp member ;; bfr-eval-of-override-var-superset
                             )))

  ;; BOZO package
  (defmacro hq (x) `(acl2::hq ,x))

  (defun bfrmc-set-initst-pred-correct-hint (prop constr updates ins initstp max-bvar
                                                  new-prop new-constr new-updates new-initst)
    (declare (xargs :normalize nil))
    (b* ((new-run (bfr-constrained-mcrun new-prop new-constr new-updates new-initst ins))
         (initial-ins (car ins))
         (variable-sts (acl2::hons-set-diff (bfr-updates->states updates)
                                            (bfr-updates->states new-initst)))
         (ins-to-initst (bfr-set-var (nfix max-bvar) nil
                                     (bfr-env-override
                                      (bfr-updates->states new-initst)
                                      new-initst
                                      (bfr-env-override
                                       variable-sts
                                       (bfr-ins-to-initst variable-sts
                                                          (+ 1 (nfix max-bvar))
                                                          initial-ins)
                                       initial-ins))))
         ;; (old-run (bfr-constrained-mcrun prop constr updates ins-to-initst ins))
         (initst-ok (bfr-eval initstp ins-to-initst))
         ((acl2::termhint-seq `'(:expand ((bfr-constrained-mcrun
                                           ,(hq new-prop)
                                           ,(hq new-constr)
                                           ,(hq new-updates)
                                           ,(hq new-initst)
                                           ,(hq ins))
                                          (bfr-constrained-mcrun
                                           ,(hq prop)
                                           ,(hq constr)
                                           ,(hq updates)
                                           ,(hq ins-to-initst)
                                           ,(hq ins)))
                                 :do-not-induct t)))
         (eval-env (bfr-mc-env updates
                               (bfr-env-override
                                (bfr-updates->states new-initst)
                                new-initst
                                (bfr-ins-to-initst variable-sts
                                                   (+ 1 (nfix max-bvar))
                                                   (car ins)))
                               (car ins)))
         ((when new-run)
          (b* (((when initst-ok)
                `'(:use ((:instance acl2::mark-clause-is-true
                          (x 'new-run-and-initst-implies-old-run))
                         (:instance bfrmc-set-initst-pred-later-cycles
                          (ins ,(hq (cdr ins)))
                          (curr-st
                           ,(hq (bfr-eval-updates updates eval-env))))))))
            `'(:use ((:instance acl2::mark-clause-is-true
                      (x 'new-run-and-not-initst-should-be-done))))))
         ((when initst-ok)
          `'(:use ((:instance acl2::mark-clause-is-true
                    (x 'not-new-run-and-initst-implies-not-old-run))
                   (:instance bfrmc-set-initst-pred-later-cycles
                    (ins ,(hq (cdr ins)))
                    (curr-st
                     ,(hq (bfr-eval-updates updates eval-env))))))))
      `'(:use ((:instance acl2::mark-clause-is-true
                    (x 'not-new-run-implies-initst))))))
                              

  (std::defret bfrmc-set-initst-pred-correct
    (b* ((initial-ins (car ins))
         (variable-sts (acl2::hons-set-diff (bfr-updates->states updates)
                                               (bfr-updates->states new-initst)))
         (ins-to-initst (bfr-set-var (nfix max-bvar) nil
                                     (bfr-env-override
                                      (bfr-updates->states new-initst)
                                      new-initst
                                      (bfr-env-override
                                       variable-sts
                                       (bfr-ins-to-initst variable-sts
                                                          (+ 1 (nfix max-bvar))
                                                          initial-ins)
                                       initial-ins)))))
      (implies (and (consp ins)
                    (bfr-mode)
                    (pbfr-vars-bounded max-bvar t prop)
                    (pbfr-vars-bounded max-bvar t constr)
                    ;; (pbfr-vars-bounded max-bvar t initstp)
                    (pbfr-list-vars-bounded max-bvar t (alist-vals (bfr-updates-fix updates)))
                    (bfr-varlist-bounded max-bvar (bfr-updates->states updates))
                    ;; (subsetp (bfr-vars initstp) (bfr-updates->states updates))
                    (pbfr-vars-bounded max-bvar t initstp)
                    )
               (iff (bfr-constrained-mcrun new-prop new-constr new-updates new-initst ins)
                    (implies (bfr-eval initstp ins-to-initst)
                             (bfr-constrained-mcrun prop constr updates ins-to-initst ins)))))
    :hints (("goal" :in-theory (e/d (bfr-constrained-mcrun
                                      bfr-updates->states
                                      bfr-env-override
                                      bfr-eval-updates)
                                    ((:t bfr-constrained-mcrun))))
            (acl2::use-termhint (bfrmc-set-initst-pred-correct-hint
                                 prop constr updates ins initstp max-bvar
                                 new-prop new-constr new-updates new-initst))))

  (local (defthm pbfr-list-depends-on-in-aig-mode
           (implies (bfr-mode)
                    (iff (pbfr-list-depends-on k t x)
                         (member (bfr-varname-fix k) (acl2::aiglist-vars x))))
           :hints(("Goal" :in-theory (enable pbfr-list-depends-on pbfr-depends-on bfr-depends-on
                                             bfr-from-param-space list-fix
                                             set::in-to-member
                                             bfr-varname-fix
                                             acl2::aiglist-vars)
                   :induct (pbfr-list-depends-on k t x)
                   :expand ((pbfr-list-depends-on k t x))))))

  (local (defthm pbfr-depends-on-of-aig-restrict
           (implies (and (not (pbfr-depends-on k t x))
                         (not (pbfr-list-depends-on k t (alist-vals a)))
                         (bfr-mode))
                    (not (pbfr-depends-on k t (acl2::aig-restrict x a))))
           :hints(("Goal" :in-theory (enable pbfr-depends-on bfr-depends-on bfr-from-param-space
                                             set::in-to-member)))))

  (local (defthm pbfr-vars-bounded-of-aig-restrict
           (implies (and (pbfr-vars-bounded k t x)
                         (pbfr-list-vars-bounded k t (alist-vals a))
                         (bfr-mode))
                    (pbfr-vars-bounded k t (acl2::aig-restrict x a)))
           :hints ((and stable-under-simplificationp
                        `(:expand (,(car (last clause)))
                          :in-theory (disable pbfr-list-depends-on-in-aig-mode))))))

  (local (defthm pbfr-list-vars-bounded-of-aig-restrict-alist-vals
           (implies (and (pbfr-list-vars-bounded k t (alist-vals x))
                         (pbfr-list-vars-bounded k t (alist-vals a))
                         (bfr-mode))
                    (pbfr-list-vars-bounded k t (alist-vals (acl2::aig-restrict-alist x a))))
           :hints(("Goal" :in-theory (enable pbfr-list-vars-bounded alist-vals acl2::aig-restrict-alist)))))


  (defthm pbfr-vars-bounded-of-bfr-ite-fn
    (implies (and (pbfr-vars-bounded k t x)
                  (pbfr-vars-bounded k t y)
                  (pbfr-vars-bounded k t z))
             (pbfr-vars-bounded k t (bfr-ite-fn x y z)))
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

  (defthm pbfr-vars-bounded-of-bfr-and
    (implies (and (pbfr-vars-bounded k t x)
                  (pbfr-vars-bounded k t y))
             (pbfr-vars-bounded k t (bfr-binary-and x y)))
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

  (defthm pbfr-vars-bounded-of-bfr-or
    (implies (and (pbfr-vars-bounded k t x)
                  (pbfr-vars-bounded k t y))
             (pbfr-vars-bounded k t (bfr-binary-or x y)))
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

  (defthm pbfr-vars-bounded-of-bfr-var-bfr-mode
    (implies (and (natp (bfr-varname-fix v))
                  (< (bfr-varname-fix v) (nfix k))
                  (bfr-mode))
             (pbfr-vars-bounded k t (bfr-var v)))
    :hints(("Goal" :in-theory (enable pbfr-vars-bounded pbfr-depends-on bfr-depends-on
                                      bfr-from-param-space))))


  (defthm pbfr-list-vars-bounded-of-bfr-initial-states
    (implies (and (bfr-varlist-bounded k st-vars)
                  (<= (+ (len st-vars) (nfix next-initst-var)) (nfix k))
                  (pbfr-vars-bounded k t max-bvar)
                  (bfr-mode))
             (pbfr-list-vars-bounded k t (alist-vals (bfr-initial-states st-vars max-bvar next-initst-var))))
    :hints(("Goal" :in-theory (enable bfr-initial-states bfr-varlist-bounded pbfr-list-vars-bounded))))

  (defthm bfr-varlist-bounded-of-incr
    (implies (and (bfr-varlist-bounded k vars)
                  (<= (nfix k) (nfix m)))
             (bfr-varlist-bounded m vars))
    :hints(("Goal" :in-theory (enable bfr-varlist-bounded))))

  (defthm pbfr-list-vars-bounded-when-boolean-listp
    (implies (acl2::boolean-val-alistp x)
             (pbfr-list-vars-bounded k t (alist-vals x)))
    :hints(("Goal" :in-theory (enable acl2::boolean-val-alistp pbfr-list-vars-bounded alist-vals
                                      booleanp))))


  ;; (local (defthm pbfr-vars-bounded-when-subsetp-rw
  ;;          (implies (and (subsetp (bfr-vars x) vars)
  ;;                        (bfr-varnamelist-p vars)
  ;;                        (bfr-varlist-bounded max-bvar vars)
  ;;                        (bfr-mode))
  ;;                   (pbfr-vars-bounded max-bvar t x))
  ;;          :hints(("Goal" :in-theory (enable pbfr-vars-bounded
  ;;                                            pbfr-depends-on
  ;;                                            bfr-depends-on
  ;;                                            bfr-from-param-space
  ;;                                            bfr-vars
  ;;                                            set::in-to-member
  ;;                                            bfr-varlist-bounded-implies-not-member)))))

  (std::defret bfrmc-set-initst-pred-vars-bounded
    (implies (and (bfr-mode)
                  (pbfr-vars-bounded max-bvar t prop)
                  (pbfr-vars-bounded max-bvar t constr)
                  (pbfr-vars-bounded max-bvar t initstp)
                  (pbfr-list-vars-bounded max-bvar t (alist-vals (bfr-updates-fix updates)))
                  (bfr-varlist-bounded max-bvar (bfr-updates->states updates)))
             (and (pbfr-vars-bounded next-bvar t new-prop)
                  (pbfr-vars-bounded next-bvar t new-constr)
                  (pbfr-list-vars-bounded next-bvar t (alist-vals new-updates))
                  (bfr-varlist-bounded next-bvar (bfr-updates->states new-updates))))
    :hints(("Goal" :in-theory (enable alist-vals
                                      bfr-updates->states
                                      bfr-varlist-bounded)
            :do-not-induct t)))
  )


(define bfr-ins-from-initst ((st-vars bfr-varnamelist-p)
                             (next-input-var natp)
                             initst)
  :returns (ins)
  (if (atom st-vars)
      nil
    (bfr-set-var (lnfix next-input-var)
                 (bfr-lookup (car st-vars) initst)
                 (bfr-ins-from-initst (cdr st-vars)
                                      (+ 1 (lnfix next-input-var))
                                      initst)))
  ///

  (local (defthm bfr-varname-fix-when-integerp
           (implies (natp (bfr-varname-fix x))
                    (equal (nfix x) (bfr-varname-fix x)))
           :hints(("Goal" :in-theory (enable bfr-varname-fix aig-var-fix)))))

  (std::defret lookup-in-bfr-ins-from-initst
    (equal (bfr-lookup var ins)
           (b* ((var (bfr-varname-fix var)))
             (if (and (integerp var)
                      (<= (nfix next-input-var) var)
                      (< var (+ (nfix next-input-var) (len st-vars))))
                 (bfr-lookup (nth (- var (nfix next-input-var)) st-vars) initst)
               (bool-fix (bfr-mode)))))
    :hints(("Goal" :induct t)
           (and stable-under-simplificationp
                '(:in-theory (enable bfr-lookup)))))

  (defthm bfr-ins-from-initst-of-set-irrel-var
    (implies (not (member (Bfr-varname-fix var) (bfr-varnamelist-fix st-vars)))
             (equal (bfr-ins-from-initst st-vars next-initst-var (bfr-set-var var val env))
                    (bfr-ins-from-initst st-vars next-initst-var env)))
    :hints(("Goal" :in-theory (enable bfr-ins-to-initst bfr-varlist-bounded))))

  ;; (defthm bfr-ins-from-initst-of-override-states
  ;;   (implies (and (bfr-varlist-bounded max-bvar st-vars1)
  ;;                 (<= (nfix max-bvar) (nfix next-initst-var)))
  ;;            (equal (bfr-ins-from-initst st-vars next-initst-var
  ;;                                        (bfr-env-override st-vars1 initst env))
  ;;                   (bfr-ins-from-initst st-vars next-initst-var env))))

  )
  




(define bfrmc-set-initst-pred-inputs ((updates bfr-updates-p)
                                      (initstp)
                                      (max-bvar natp)

                                      (initst)
                                      (ins consp))
  ;; Given an initial state satisfying the predicate and frame inputs for the
  ;; un-transformed machine, create inputs for the new machine.  The initial
  ;; state is given by bfrmc-set-initst-pred.
  :returns (new-ins)
  :guard (bfr-mode)
  :prepwork ((local (defthm bfr-varnamelist-p-of-numlist
                      (implies (and (natp start)
                                    (natp by))
                               (bfr-varnamelist-p (numlist start by n)))
                      :hints(("Goal" :in-theory (enable numlist))))))
  (b* ((past-initcycle-var (lnfix max-bvar))
       (state-vars (bfr-updates->states updates))
       (consts-from-initstp (acl2::fal-extract state-vars
                                               (acl2::aig-extract-iterated-assigns-alist initstp 10)))
       (const-initsts (cons (cons past-initcycle-var nil)
                            consts-from-initstp))
       (variable-sts (acl2::hons-set-diff (bfr-updates->states updates)
                                             (bfr-updates->states const-initsts)))
       (ins-from-initst (bfr-ins-from-initst variable-sts (1+ past-initcycle-var) initst)))
    (cons (bfr-env-override (numlist (1+ past-initcycle-var)
                                     1 (len variable-sts))
                            ins-from-initst (car ins)) (cdr ins)))
  ///

  (local (defthm bfr-lookup-in-fal-extract
           (implies (bfr-mode)
                    (equal (bfr-lookup k (acl2::fal-extract vars x))
                           (if (member (bfr-varname-fix k) vars)
                               (bfr-lookup k x)
                             t)))
           :hints(("Goal" :in-theory (enable bfr-lookup)))))

  (local (defthm bfr-updates->states-of-fal-extract
           (equal (bfr-updates->states (acl2::fal-extract vars x))
                  (intersection$ vars (bfr-updates->states x)))
           :hints(("Goal" :in-theory (enable bfr-updates->states acl2::fal-extract intersection$)))))

  (local (defthm boolean-val-alist-of-fal-extract
           (implies (acl2::boolean-val-alistp x)
                    (acl2::boolean-val-alistp (acl2::fal-extract vars x)))
           :hints(("Goal" :in-theory (enable acl2::fal-extract acl2::boolean-val-alistp)))))



  (local (defthm member-of-numlist
           (implies (natp start)
                    (iff (member k (numlist start 1 n))
                         (and (integerp k)
                              (<= start k)
                              (< k (+ start (nfix n))))))
           :hints(("Goal" :in-theory (enable numlist)))))

  (local (defthm index-of-when-not-member
           (implies (not (member k x))
                    (equal (acl2::index-of k x) nil))
           :hints(("Goal" :in-theory (enable member acl2::index-of)))))

  (local (defthm index-of-when-member
           (implies (member k x)
                    (natp (acl2::index-of k x)))
           :hints(("Goal" :in-theory (enable member acl2::index-of)))
           :rule-classes :type-prescription))

  (local (defthm acl2-numberp-index-of-when-member
           (implies (member k x)
                    (acl2-numberp (acl2::index-of k x)))
           :hints(("Goal" :in-theory (enable member acl2::index-of)))))

  (local (defthm next-bvar-plus-index
           (<= next-bvar (+ next-bvar (acl2::index-of k x)))
           :hints (("goal" :cases ((acl2::index-of k x))))))

  (local (defthm plus-minus
           (equal (+ x (- x) y)
                  (fix y))))



  ;; (local (defthm state-alist-reduction1
  ;;          (let ((variable-sts (set-difference$ (bfr-updates->states updates)
  ;;                                                  (bfr-updates->states const-updates))))
  ;;            (implies (natp next-bvar)
  ;;                     (bfr-env-equiv (bfr-env-override
  ;;                                     (bfr-updates->states const-updates)
  ;;                                     const-updates
  ;;                                     (bfr-ins-to-initst
  ;;                                      variable-sts
  ;;                                      next-bvar
  ;;                                      (bfr-env-override
  ;;                                       (numlist next-bvar 1 (len variable-sts))
  ;;                                       (bfr-ins-from-initst
  ;;                                        variable-sts
  ;;                                        next-bvar
  ;;                                        initst)
  ;;                                       ins)))
  ;;                                    (bfr-env-override
  ;;                                     (bfr-updates->states const-updates)
  ;;                                     const-updates
  ;;                                     (bfr-env-override variable-sts initst nil)))))
  ;;          :hints(("Goal" :in-theory (enable bfr-env-equiv
  ;;                                            lookup-in-bfr-ins-to-initst-split)
  ;;                  :expand ((:free (x) (bfr-lookup x nil)))))))

  (local (defthm set-difference-of-cons-irrel
           (implies (not (member a x))
                    (equal (set-difference$ x (cons a y))
                           (set-difference$ x y)))
           :hints(("Goal" :in-theory (enable set-difference$)))))

  (local (defthm lookup-in-updates-when-bfr-varlist-bounded
           (implies (bfr-varlist-bounded max-bvar (bfr-updates->states updates))
                    (not (hons-assoc-equal (nfix max-bvar) updates)))
           :hints(("Goal" :in-theory (enable bfr-varlist-bounded bfr-updates->states hons-assoc-equal)))))

  (local (defthm new-initst-of-bfrmc-set-initst-pred
           (b* (((mv ?new-prop ?new-constr ?new-updates new-initst ?next-bvar)
                 (bfrmc-set-initst-pred prop constr updates initstp max-bvar)))
             (equal new-initst
                    (b* ((past-initcycle-var (lnfix max-bvar))
                         (state-vars (bfr-updates->states updates))
                         (consts-from-initstp (acl2::fal-extract state-vars
                                                                 (acl2::aig-extract-iterated-assigns-alist initstp 10)))
                         (const-initsts (cons (cons past-initcycle-var nil)
                                              consts-from-initstp)))
                       const-initsts)))
           :hints(("Goal" :in-theory (enable bfrmc-set-initst-pred)))))

  (local (defthm bfr-eval-of-env-override-cons-irrel
           (implies (not (member (bfr-varname-fix var) (bfr-vars x)))
                    (equal (bfr-eval x (bfr-env-override (cons var vars) a b))
                           (bfr-eval x (bfr-env-override vars a b))))
           :hints(("Goal" :in-theory (enable bfr-env-override)))))

  (local (defthm bfr-set-var-of-env-override-cons-irrel
           (bfr-env-equiv (bfr-set-var var val (bfr-env-override (cons var vars) a b))
                          (bfr-set-var var val (bfr-env-override vars a b)))
           :hints(("Goal" :in-theory (enable bfr-env-equiv)))))

  (local (defthmd bfr-lookup-of-cons
           (implies (bfr-mode)
                    (equal (bfr-lookup k (cons (cons a b) c))
                           (if (equal (bfr-varname-fix k) a)
                               (bool-fix b)
                             (bfr-lookup k c))))
           :hints(("Goal" :in-theory (enable bfr-lookup)))))

  (local (defthm bfr-env-override-of-cons-irrel
           (implies (and (not (member (bfr-varname-fix var) (bfr-varnamelist-fix vars)))
                         (bfr-mode))
                    (equal (bfr-env-override vars (cons (cons var val) env) env2)
                           (bfr-env-override vars env env2)))
           :hints(("Goal" :in-theory (enable bfr-env-override bfr-varnamelist-fix
                                             bfr-lookup-of-cons)))))

  (defcong bfr-env-equiv bfr-env-equiv (bfr-set-var var val env) 3
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

  (local (defthm bfr-lookup-when-in-iterated-assigns-alist
           (implies (and (bfr-eval x env)
                         (hons-assoc-equal (bfr-varname-fix k) (acl2::aig-extract-iterated-assigns-alist x n))
                         (bfr-mode))
                    (equal (bfr-lookup k env)
                           (bfr-lookup k (acl2::aig-extract-iterated-assigns-alist x n))))
           :hints (("goal" :in-theory (enable bfr-eval bfr-lookup acl2::aig-env-lookup)
                    :use ((:instance acl2::lookup-in-aig-extract-iterated-assigns-alist
                           (v (bfr-varname-fix k)) (env env) (x x) (n n)))
                    :do-not-induct t))))


  (local (defthmd bfr-lookup-when-in-iterated-assigns-alist-override
           (implies (and (bfr-eval x (bfr-env-override vars env1 env2))
                         (hons-assoc-equal (bfr-varname-fix k) (acl2::aig-extract-iterated-assigns-alist x n))
                         (bfr-mode))
                    (and (implies (member (bfr-varname-fix k) (bfr-varnamelist-fix vars))
                                  (equal (bfr-lookup k env1)
                                         (bfr-lookup k (acl2::aig-extract-iterated-assigns-alist x n))))
                         (implies (not (member (bfr-varname-fix k) (bfr-varnamelist-fix vars)))
                                  (equal (bfr-lookup k env2)
                                         (bfr-lookup k (acl2::aig-extract-iterated-assigns-alist x n))))))
           :hints (("goal" :in-theory (disable bfr-lookup-when-in-iterated-assigns-alist)
                    :use ((:instance bfr-lookup-when-in-iterated-assigns-alist
                           (env (bfr-env-override vars env1 env2))))
                    :do-not-induct t))))

  
                                    

  (local (defthm bfr-varnamelist-p-of-intersection
           (implies (bfr-varnamelist-p a)
                    (bfr-varnamelist-p (intersection$ a b)))
           :hints(("Goal" :in-theory (enable intersection$)))))

  (local (defthm bfr-varnamelist-p-of-set-diff
           (implies (bfr-varnamelist-p a)
                    (bfr-varnamelist-p (set-difference-equal a b)))
           :hints(("Goal" :in-theory (enable set-difference-equal)))))


  (local (defthm env-override-of-env-override-intersection
           (implies (and (bfr-varnamelist-p a)
                         (bfr-varnamelist-p b))
                    (bfr-env-equiv (bfr-env-override a
                                                     (bfr-env-override (intersection$ a b) env1 env2)
                                                     env3)
                                   (bfr-env-override a
                                                     (bfr-env-override b env1 env2)
                                                     env3)))
           :hints(("Goal" :in-theory (enable bfr-env-equiv)))))

  (local (defthm env-override-of-env-override-difference
           (implies (and (bfr-varnamelist-p a)
                         (bfr-varnamelist-p b))
                    (bfr-env-equiv (bfr-env-override a
                                                     env1
                                                     (bfr-env-override (set-difference$ b a) env2 env3))
                                   (bfr-env-override a env1
                                                     (bfr-env-override b env2 env3))))
           :hints(("Goal" :in-theory (enable bfr-env-equiv)))))

  (local (defthm env-override-of-env-override-of-env-override
           (implies (and (bfr-varnamelist-p a)
                         (bfr-varnamelist-p b))
                    (bfr-env-equiv (bfr-env-override
                                    a (bfr-env-override b env1 (bfr-env-override a env2 env3)) env4)
                                   (bfr-env-override a (bfr-env-override b env1 env2) env4)))
           :hints(("Goal" :in-theory (enable bfr-env-equiv)))))

  (defthm bfr-env-override-of-bfr-env-override-same
    (bfr-env-equiv (bfr-env-override vars (bfr-env-override vars a b) c)
                   (bfr-env-override vars a c))
  :hints(("Goal" :in-theory (enable bfr-env-equiv))))

  (local (defthm bfr-env-equiv-of-override-extract-iterated-assigns
           (implies (and (bfr-eval initstp (bfr-env-override (bfr-updates->states updates) initst env2))
                         ;; (pbfr-vars-bounded max-bvar t initstp)
                         (bfr-mode))
                    (b* (;; (past-initcycle-var (lnfix max-bvar))
                          (state-vars (bfr-updates->states updates))
                          (initst-consts (acl2::aig-extract-iterated-assigns-alist initstp 10))
                          (const-states (acl2::fal-extract state-vars initst-consts))
                          ;; (const-state-vars (intersection-equal state-vars (bfr-updates->states initst-consts)))
                          )
                      (bfr-env-equiv (bfr-env-override
                                      state-vars
                                      (bfr-env-override
                                       (bfr-updates->states initst-consts)
                                       const-states
                                       initst)
                                      env2)
                                     (bfr-env-override state-vars initst env2))))
           :hints(("Goal" :in-theory (enable bfr-env-equiv
                                             bfr-lookup-when-in-iterated-assigns-alist-override)
                   :expand ((:free (x) (bfr-lookup x nil)))
                   :do-not-induct t))))

  (local (defthm bfr-constrained-mcrun-of-irrel-st
           (implies (and (bfr-varlist-bounded max-bvar (bfr-updates->states updates))
                         (bfr-eval initstp (bfr-env-override
                                            (bfr-updates->states updates)
                                            initst (car ins)))
                         (bfr-mode))
                    (b* (;; (past-initcycle-var (lnfix max-bvar))
                          (state-vars (bfr-updates->states updates))
                          (initst-consts (acl2::aig-extract-iterated-assigns-alist initstp 10))
                          (const-states (acl2::fal-extract state-vars initst-consts))
                          (const-state-vars (intersection-equal state-vars (bfr-updates->states initst-consts))))
                      (equal (bfr-constrained-mcrun
                              prop constr updates
                              (bfr-set-var (nfix max-bvar) val
                                           (bfr-env-override
                                            const-state-vars
                                            const-states
                                            (bfr-env-override
                                             state-vars
                                             initst env)))
                              ins)
                             (bfr-constrained-mcrun
                              prop constr updates initst ins))))
           :hints (("goal" :expand ((:free (initst)
                                     (bfr-constrained-mcrun prop constr updates initst ins)))
                    :do-not-induct t))))

  (local (defun bfr-varlist-bounded-witness (k x)
           (if (atom x)
               nil
             (b* ((x1 (bfr-varname-fix (car x))))
               (if (and (natp x1) (< x1 (lnfix k)))
                   (bfr-varlist-bounded-witness k (cdr x))
                 x1)))))

  (local (defthmd bfr-varlist-bounded-iff-witness
           (iff (bfr-varlist-bounded max-bvar x)
                (let ((witness (bfr-varlist-bounded-witness max-bvar x)))
                  (or (not (bfr-varname-p witness))
                      (and (natp witness)
                           (< witness (nfix max-bvar)))
                      (not (member witness (bfr-varnamelist-fix x))))))
           :hints(("Goal" :in-theory (enable bfr-varlist-bounded)))))


                       

  (local (defthm bfr-varlist-bounded-of-vars-when-pbfr-vars-bounded
           (implies (and (pbfr-vars-bounded max-bvar t prop)
                         (bfr-mode))
                    (bfr-varlist-bounded max-bvar (bfr-vars prop)))
           :hints(("Goal" :in-theory (e/d (bfr-varlist-bounded-iff-witness)
                                          (BFR-VARNAME-P-WHEN-MEMBER-EQUAL-OF-BFR-VARNAMELIST-P))))))


  
  (local (defthmd equal-of-bfr-eval-to-equal-normalize
           (iff (equal (bfr-eval x env1) (bfr-eval x env2))
                (or (hide (equal (bfr-eval x env1) (bfr-eval x env2)))
                    (bfr-env-equiv (bfr-normalize-env (bfr-vars x) env1)
                                   (bfr-normalize-env (bfr-vars x) env2))))
           :hints (("goal" :expand ((:free (x) (hide x)))
                    :use ((:instance BFR-EVAL-OF-NORMALIZE-ENV
                           (vars (bfr-vars x))
                           (env env1))
                          (:instance BFR-EVAL-OF-NORMALIZE-ENV
                           (vars (bfr-vars x))
                           (env env2)))
                    :in-theory (disable bfr-eval-of-normalize-env)))))

  (local (defthmd bfr-eval-by-normalize
           (implies (bfr-eval x env1)
                    (iff (bfr-eval x env2)
                         (or (hide (bfr-eval x env2))
                             (bfr-env-equiv (bfr-normalize-env (bfr-vars x) env1)
                                            (bfr-normalize-env (bfr-vars x) env2)))))
           :hints (("goal" :expand ((:free (x) (hide x)))
                    :use ((:instance BFR-EVAL-OF-NORMALIZE-ENV
                           (vars (bfr-vars x))
                           (env env1))
                          (:instance BFR-EVAL-OF-NORMALIZE-ENV
                           (vars (bfr-vars x))
                           (env env2)))
                    :in-theory (disable bfr-eval-of-normalize-env)))))

  (local (defthm eval-of-env-override-env-override-numlist-of-bounded-varlist
           (implies (and (pbfr-vars-bounded max-bvar t x)
                         (bfr-mode))
                    (equal (bfr-eval x (bfr-env-override sts initst
                                                         (bfr-env-override (numlist (+ 1 (nfix max-bvar)) 1 n)
                                                                           ins-from-initst ins)))
                           (bfr-eval x (bfr-env-override sts initst ins))))
           :hints(("Goal" :in-theory (enable equal-of-bfr-eval-to-equal-normalize
                                             bfr-env-equiv)
                   :do-not-induct t))))

  (local (defthm eval-updates-of-env-override-env-override-numlist-of-bounded-varlist
           (implies (and (pbfr-list-vars-bounded max-bvar t (alist-vals (bfr-updates-fix updates)))
                         (bfr-mode))
                    (equal (bfr-eval-updates updates (bfr-env-override sts initst
                                                                       (bfr-env-override (numlist (+ 1 (nfix max-bvar)) 1 n)
                                                                                         ins-from-initst ins)))
                           (bfr-eval-updates updates (bfr-env-override sts initst ins))))
           :hints(("Goal" :in-theory (enable bfr-eval-updates bfr-updates-fix alist-vals pbfr-list-vars-bounded)
                   :induct (bfr-eval-updates updates env)
                   :expand ((:free (env) (bfr-eval-updates updates env)))))))

  (local (defthm bfr-constrained-mcrun-of-irrel-input
           (implies (and (pbfr-vars-bounded max-bvar t prop)
                         (pbfr-vars-bounded max-bvar t constr)
                         (pbfr-list-vars-bounded max-bvar t (alist-vals (bfr-updates-fix updates)))
                         (consp ins)
                         (bfr-mode))
                    (equal (bfr-constrained-mcrun
                            prop constr updates initst 
                            (cons (bfr-env-override
                                   (numlist (+ 1 (nfix max-bvar)) 1 n)
                                   ins-from-initst
                                   (car ins))
                                  (cdr ins)))
                           (bfr-constrained-mcrun
                            prop constr updates initst ins)))
           :hints (("goal" :expand ((:free (ins)
                                     (bfr-constrained-mcrun prop constr updates initst ins)))
                    :do-not-induct t))))

  (defthm bfr-ins-to-initst-of-bfr-ins-from-initst
    (implies (and (natp next-bvar)
                  (bfr-varnamelist-p variable-sts))
             (bfr-env-equiv (bfr-ins-to-initst variable-sts
                                               next-bvar
                                               (bfr-env-override
                                                (numlist next-bvar 1 (len variable-sts))
                                                (bfr-ins-from-initst
                                                 variable-sts
                                                 next-bvar
                                                 initst)
                                                env))
                            (bfr-env-override variable-sts initst nil)))
    :hints(("Goal" :in-theory (enable bfr-env-equiv
                                      lookup-in-bfr-ins-to-initst-split)
            :expand ((:free (x) (bfr-lookup x nil)))
            :do-not-induct t)))

  (local (defthmd set-difference-of-intersection-with-subset
           (implies (subsetp a b)
                    (equal (set-difference$ a (intersection$ b c))
                           (set-difference$ a c)))
           :hints(("Goal" :in-theory (enable set-difference$ intersection$)))))

  (local (defthm set-difference-of-intersection
           (equal (set-difference$ a (intersection$ a b))
                  (set-difference$ a b))
           :hints(("Goal" :in-theory (enable set-difference-of-intersection-with-subset)))))

  (local (defthm bfr-env-override-of-intersection-set-diff
           (implies (and (bfr-varnamelist-p a)
                         (bfr-varnamelist-p b))
                    (bfr-env-equiv (bfr-env-override (intersection$ a b)
                                                     env1
                                                     (bfr-env-override (set-difference$ a b) env2 env3))
                                   (bfr-env-override (intersection$ a b)
                                                     env1
                                                     (bfr-env-override a env2 env3))))
           :hints(("Goal" :in-theory (enable bfr-env-equiv)))))

  (local (defthm bfr-eval-initstp-reduce
           (implies (and (pbfr-vars-bounded max-bvar t initstp)
                         (bfr-mode)
                         (BFR-EVAL INITSTP
                                   (BFR-ENV-OVERRIDE (BFR-UPDATES->STATES UPDATES)
                                                     INITST (CAR INS))))
                    (b* (;; (past-initcycle-var (lnfix max-bvar))
                          (state-vars (bfr-updates->states updates))
                          (initst-consts (acl2::aig-extract-iterated-assigns-alist initstp 10))
                          (const-states (acl2::fal-extract state-vars initst-consts))
                          (const-state-vars (intersection-equal state-vars (bfr-updates->states initst-consts))))
                      (bfr-eval initstp (BFR-ENV-OVERRIDE
                                         const-state-vars
                                         const-states
                                         (BFR-ENV-OVERRIDE
                                          state-vars
                                          INITST
                                          (BFR-ENV-OVERRIDE
                                           (NUMLIST
                                            (+ 1 (NFIX MAX-BVAR))
                                            1
                                            (LEN
                                             (SET-DIFFERENCE-EQUAL
                                              (BFR-UPDATES->STATES UPDATES)
                                              (BFR-UPDATES->STATES
                                               (ACL2::AIG-EXTRACT-ITERATED-ASSIGNS-ALIST INITSTP 10)))))
                                           (BFR-INS-FROM-INITST
                                            (SET-DIFFERENCE-EQUAL
                                             (BFR-UPDATES->STATES UPDATES)
                                             (BFR-UPDATES->STATES
                                              (ACL2::AIG-EXTRACT-ITERATED-ASSIGNS-ALIST INITSTP 10)))
                                            (+ 1 (NFIX MAX-BVAR))
                                            INITST)
                                           (CAR INS)))))))
           :hints(("Goal" :in-theory (enable bfr-eval-by-normalize
                                             bfr-lookup-when-in-iterated-assigns-alist-override
                                             bfr-env-equiv)))))



  (std::defret bfrmc-set-initst-pred-inputs-correct
    (b* (((mv new-prop new-constr new-updates new-initst ?next-bvar)
          (bfrmc-set-initst-pred prop constr updates initstp max-bvar)))
      (implies (and (consp ins)
                    (bfr-mode)
                    (pbfr-vars-bounded max-bvar t prop)
                    (pbfr-vars-bounded max-bvar t constr)
                    (pbfr-vars-bounded max-bvar t initstp)
                    (pbfr-list-vars-bounded max-bvar t (alist-vals (bfr-updates-fix updates)))
                    (bfr-varlist-bounded max-bvar (bfr-updates->states updates))
                    ;; (subsetp (bfr-vars initstp) (bfr-updates->states updates))
                    (bfr-eval initstp (bfr-env-override (bfr-updates->states updates) initst (car ins)))
                    ;; (not (bfr-lookup (nfix max-bvar) initst))
                    )
               (iff (bfr-constrained-mcrun new-prop new-constr new-updates new-initst new-ins)
                    (bfr-constrained-mcrun prop constr updates initst ins))))
    :hints (("goal" :use ((:instance bfrmc-set-initst-pred-correct
                           (ins (bfrmc-set-initst-pred-inputs updates initstp max-bvar
                                                              initst ins))))
             :in-theory (e/d (bfr-updates->states)
                             (bfrmc-set-initst-pred-correct))))))

  
  
                               






  
