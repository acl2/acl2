; FGL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2023 Intel Corporation
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
; Original author: Sol Swords <sol.swords@intel.com>


(in-package "FGL")

(include-book "make-isomorphic-def")
(include-book "add-primitives")
(include-book "primitives-stub")
(include-book "bfr-arithmetic")
; (include-book "subst-functions")
(include-book "def-fgl-rewrite")
(include-book "centaur/misc/hons-remove-dups" :dir :system)
(local (include-book "primitive-lemmas"))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (std::add-default-post-define-hook :fix))

(local (in-theory (disable w)))


(define bfrlist-sign-extend ((n natp) (x true-listp))
  :measure (nfix n)
  :returns (new-x true-listp)
  :prepwork ((local (in-theory (disable acl2::list-fix-when-true-listp
                                        acl2::list-fix-when-len-zero
                                        acl2::list-fix-when-not-consp
                                        acl2::subsetp-member
                                        default-car default-cdr))))
  (if (or (zp n) (eql n 1))
      (list (car x))
    (cons (car x)
          (bfrlist-sign-extend (1- n) (scdr x))))
  ///
  (local (defthm len-scdr-equals-len
           (implies (and (equal (len (scdr x)) (len x))
                         (consp x))
                    (equal (len (scdr x)) 1))
           :hints(("Goal" :in-theory (enable scdr)))))

  (local (defthm scdr-when-consp-cdr
           (implies (consp (cdr x))
                    (equal (scdr x) (true-list-fix (cdr x))))
           :hints(("Goal" :in-theory (enable scdr)))))
  
  (local (include-book "arithmetic/top" :dir :system))
  
  (local (defthm bfr-list-eval-under-iff
           (iff (consp (bfr-list-eval x env))
                (consp x))
           :hints(("Goal" :in-theory (enable bfr-list-eval)))))
  
  (local (defthm bools->int-of-bfr-eval-sum
           (equal (* 2 (bools->int (bfr-list-eval (scdr x) env)))
                  (- (bools->int (bfr-list-eval x env))
                     (bool->bit (bfr-eval (car x) env))))
           :hints(("Goal" :expand ((bfr-list-eval x env))
                   :in-theory (enable scdr logcons)))))

  
  (defret eval-of-bfrlist-sign-extend
    (implies (<= (len x) (nfix n))
             (equal (bools->int (bfr-list-eval new-x env))
                    (bools->int (bfr-list-eval x env))))
    :hints(("Goal" :induct <call>
            :in-theory (enable logcons)
            :expand ((bfr-list-eval x env)
                     (bfr-list-eval '(nil) env)
                     (:free (a b) (bfr-list-eval (cons a b) env))))))

  (defret gobj-bfr-list-eval-of-bfrlist-sign-extend
    (implies (<= (len x) (nfix n))
             (equal (bools->int (gobj-bfr-list-eval new-x env))
                    (bools->int (gobj-bfr-list-eval x env))))
    :hints(("Goal" :in-theory (enable GOBJ-BFR-LIST-EVAL-IS-BFR-LIST-EVAL))))

  (defthm member-of-bfrlist-sign-extend
    (implies (and (not (member v x))
                  (not (equal v nil)))
             (not (member v (bfrlist-sign-extend n x))))
    :hints(("Goal" :in-theory (enable scdr)))))

(defines fgl-objects-make-isomorphic
  :prepwork ((local (in-theory (disable acl2::subsetp-member
                                        acl2::lower-bound-of-len-when-sublistp
                                        acl2::len-when-prefixp
                                        acl2::member-when-atom
                                        acl2::append-when-not-consp
                                        acl2::append-atom-under-list-equiv
                                        fgl-object-bfrlist-when-integerp
                                        fgl-object-bfrlist-when-booleanp
                                        bools->int-redef
                                        eq
                                        equal-of-booleans-rewrite))))
  (define fgl-objects-make-isomorphic ((x fgl-object-p)
                                       (y fgl-object-p))
    :measure (+ (fgl-object-count x)
                (fgl-object-count y))
    :hints (("goal" :expand ((fgl-object-count x)
                             (fgl-object-count y)
                             (:free (x) (fgl-object-count (g-concrete x))))))
    :verify-guards nil
    :returns (mv ok
                 (new-x fgl-object-p)
                 (new-y fgl-object-p))
    (fgl-object-case x
      :g-concrete (fgl-object-case y
                    :g-concrete (mv t (fgl-object-fix x) (fgl-object-fix y))
                    :g-boolean (if (booleanp x.val)
                                   (mv t (g-boolean x.val) (fgl-object-fix y))
                                 (mv nil (fgl-object-fix x) (fgl-object-fix y)))
                    :g-integer (if (integerp x.val)
                                   (b* ((x.bits (int->bools x.val))
                                        (len (max (len x.bits) (len y.bits))))
                                     (mv t (g-integer (bfrlist-sign-extend len x.bits))
                                         (g-integer (bfrlist-sign-extend len y.bits))))
                                 (mv nil (fgl-object-fix x) (fgl-object-fix y)))
                    :g-cons (if (consp x.val)
                                (b* (((mv ok1 xcar ycar) (fgl-objects-make-isomorphic
                                                          (g-concrete (car x.val))
                                                          y.car))
                                     ((mv ok2 xcdr ycdr) (fgl-objects-make-isomorphic
                                                          (g-concrete (cdr x.val))
                                                          y.cdr)))
                                  (if (and ok1 ok2)
                                      (mv t (g-cons xcar xcdr) (g-cons ycar ycdr))
                                    (mv nil (fgl-object-fix x) (fgl-object-fix y))))
                              (mv nil (fgl-object-fix x) (fgl-object-fix y)))
                    :otherwise (mv nil (fgl-object-fix x) (fgl-object-fix y)))
      :g-boolean (fgl-object-case y
                   :g-concrete (if (booleanp y.val)
                                   (mv t (fgl-object-fix x) (g-boolean y.val))
                                 (mv nil (fgl-object-fix x) (fgl-object-fix y)))
                   :g-boolean (mv t (fgl-object-fix x) (fgl-object-fix y))
                   :otherwise (mv nil (fgl-object-fix x) (fgl-object-fix y)))
      :g-integer (fgl-object-case y
                   :g-concrete (if (integerp y.val)
                                   (b* ((y.bits (int->bools y.val))
                                        (len (max (len x.bits) (len y.bits))))
                                     (mv t (g-integer (bfrlist-sign-extend len x.bits))
                                         (g-integer (bfrlist-sign-extend len y.bits))))
                                 (mv nil (fgl-object-fix x) (fgl-object-fix y)))
                   :g-integer (b* ((len (max (len x.bits) (len y.bits))))
                                (mv t (g-integer (bfrlist-sign-extend len x.bits))
                                    (g-integer (bfrlist-sign-extend len y.bits))))
                   :otherwise (mv nil (fgl-object-fix x) (fgl-object-fix y)))
      :g-cons (fgl-object-case y
                :g-concrete (if (consp y.val)
                                (b* (((mv ok1 xcar ycar) (fgl-objects-make-isomorphic
                                                          x.car
                                                          (g-concrete (car y.val))))
                                     ((mv ok2 xcdr ycdr) (fgl-objects-make-isomorphic
                                                          x.cdr
                                                          (g-concrete (cdr y.val)))))
                                  (if (and ok1 ok2)
                                      (mv t (g-cons xcar xcdr) (g-cons ycar ycdr))
                                    (mv nil (fgl-object-fix x) (fgl-object-fix y))))
                              (mv nil (fgl-object-fix x) (fgl-object-fix y)))
                :g-cons (b* (((mv ok1 xcar ycar) (fgl-objects-make-isomorphic x.car y.car))
                             ((mv ok2 xcdr ycdr) (fgl-objects-make-isomorphic x.cdr y.cdr)))
                          (if (and ok1 ok2)
                              (mv t (g-cons xcar xcdr) (g-cons ycar ycdr))
                            (mv nil (fgl-object-fix x) (fgl-object-fix y))))
                :otherwise (mv nil (fgl-object-fix x) (fgl-object-fix y)))
      :g-apply (fgl-object-case y
                 :g-apply (if (eq x.fn y.fn)
                              (b* (((mv ok xargs yargs)
                                    (fgl-objectlists-make-isomorphic x.args y.args)))
                                (if ok
                                    (mv t (g-apply x.fn xargs) (g-apply y.fn yargs))
                                  (mv nil (fgl-object-fix x) (fgl-object-fix y))))
                            (mv nil (fgl-object-fix x) (fgl-object-fix y)))
                 :otherwise (mv nil (fgl-object-fix x) (fgl-object-fix y)))
      ;; maybe add g-map support
      :otherwise (mv nil (fgl-object-fix x) (fgl-object-fix y))))
  (define fgl-objectlists-make-isomorphic ((x fgl-objectlist-p)
                                           (y fgl-objectlist-p))
    :measure (+ (fgl-objectlist-count x)
                (fgl-objectlist-count y))
    :returns (mv ok
                 (new-x fgl-objectlist-p)
                 (new-y fgl-objectlist-p))
    (if (atom x)
        (mv (atom y) nil (fgl-objectlist-fix y))
      (if (atom y)
          (mv nil (fgl-objectlist-fix x) nil)
        (b* (((mv ok1 x1 y1) (fgl-objects-make-isomorphic (car x) (car y)))
             ((mv ok2 xr yr) (fgl-objectlists-make-isomorphic (cdr x) (cdr y))))
          (if (and ok1 ok2)
              (mv t (cons x1 xr) (cons y1 yr))
            (mv nil (fgl-objectlist-fix x) (fgl-objectlist-fix y)))))))
  ///
  (local (in-theory (disable fgl-objects-make-isomorphic
                             fgl-objectlists-make-isomorphic)))
  
  (std::defret-mutual fgl-objects-make-isomorphic-correct
    (std::defret <fn>-correct
      (and (equal (fgl-object-eval new-x env)
                  (fgl-object-eval x env))
           (equal (fgl-object-eval new-y env)
                  (fgl-object-eval y env)))
      :hints ('(:expand (<call>)))
      :fn fgl-objects-make-isomorphic)
    (std::defret <fn>-correct
      (and (equal (fgl-objectlist-eval new-x env)
                  (fgl-objectlist-eval x env))
           (equal (fgl-objectlist-eval new-y env)
                  (fgl-objectlist-eval y env)))
      :hints ('(:expand (<call>)))
      :fn fgl-objectlists-make-isomorphic))

  (local (defthm member-of-int->bools
           (implies (and (not (equal v t))
                         (not (Equal v nil)))
                    (not (member-equal v (int->bools x))))
           :hints(("Goal" :in-theory (e/d (int->bools
                                           acl2::member-when-atom)
                                          (intcdr intcar))))))


  (std::defret-mutual fgl-objects-make-isomorphic-bfrs
    (std::defret <fn>-bfrs
      (and (implies (and (not (member-equal v (fgl-object-bfrlist x)))
                         (case-split (not (equal v t)))
                         (case-split (not (equal v nil))))
                    (not (member-equal v (fgl-object-bfrlist new-x))))
           (implies (and (not (member-equal v (fgl-object-bfrlist y)))
                         (case-split (not (equal v t)))
                         (case-split (not (equal v nil))))
                    (not (member-equal v (fgl-object-bfrlist new-y)))))
      :hints ('(:expand (<call>)))
      :fn fgl-objects-make-isomorphic)
    (std::defret <fn>-bfrs
      (and (implies (and (not (member-equal v (fgl-objectlist-bfrlist x)))
                         (not (equal v t))
                         (not (equal v nil)))
                    (not (member-equal v (fgl-objectlist-bfrlist new-x))))
           (implies (and (not (member-equal v (fgl-objectlist-bfrlist y)))
                         (not (equal v t))
                         (not (equal v nil)))
                    (not (member-equal v (fgl-objectlist-bfrlist new-y)))))
      :hints ('(:expand (<call>)))
      :fn fgl-objectlists-make-isomorphic))
  
  (verify-guards fgl-objects-make-isomorphic))


(def-formula-checks iso-formula-checks
  (fgl-make-isomorphic))

;; (include-book "congruence-rules")


(local (defthm fgl-ev-context-equv-forall-extensions-trivial
         (implies (acl2::rewriting-negative-literal
                   `(fgl-ev-context-equiv-forall-extensions ,contexts ,obj ,term ,eval-alist))
                  (iff (fgl-ev-context-equiv-forall-extensions contexts obj term eval-alist)
                       (and 
                        (equal (fgl-ev-context-fix contexts (fgl-ev term eval-alist))
                               (fgl-ev-context-fix contexts obj))
                        (hide (fgl-ev-context-equiv-forall-extensions contexts obj term eval-alist)))))
         :hints (("goal" :expand ((:free (x) (hide x)))
                  :use ((:instance fgl-ev-context-equiv-forall-extensions-necc
                         (ext eval-alist)))
                  :in-theory (disable fgl-ev-context-equiv-forall-extensions-necc)))))

(local (in-theory (disable fgl-ev-context-equiv-forall-extensions)))

(local (defthm equal-of-cons
         (equal (equal (cons x y) z)
                (and (consp z)
                     (Equal (car z) x)
                     (equal (cdr z) y)))))

(local (defthm equal-implies-equal-of-fgl-ev-context-fix
         (implies (equal x y)
                  (equal (equal (fgl-ev-context-fix c x) (fgl-ev-context-fix c y)) t))))

(local (in-theory (disable member-equal
                           fgl-object-bfrlist-when-booleanp
                           fgl-object-bfrlist-when-integerp
                           acl2::booleanp-of-car-when-boolean-listp
                           equal-of-booleans-rewrite)))

(def-fgl-binder-meta fgl-make-isomorphic-binder
  (b* (((mv ok new-x new-y) (fgl-objects-make-isomorphic x y)))
    (mv t 'ans `((ans . ,(g-cons (g-concrete ok)
                                (g-cons new-x
                                        (g-cons new-y nil)))))
        nil interp-st state))
  :formula-check iso-formula-checks
  :origfn fgl-make-isomorphic :formals (x y))


(local (install-fgl-metafns iso-metafns))
