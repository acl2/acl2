; GL - A Symbolic Simulation Framework for ACL2
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

(in-package "FGL")

(include-book "add-primitives")
(include-book "primitives-stub")
(local (include-book "primitive-lemmas"))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (std::add-default-post-define-hook :fix))

(def-formula-checks fgl-pathcond-fix-formula-checks
  (fgl-pathcond-fix))

(local (defthm bfr-p-when-booleanp
         (implies (booleanp x)
                  (bfr-p x))
         :hints(("Goal" :in-theory (enable bfr-p ubddp aig-p max-depth)))))

(local (defthm bfr-eval-when-booleanp
         (implies (booleanp x)
                  (equal (bfr-eval x env) x))
         :hints(("Goal" :in-theory (enable bfr-eval bfr-fix bfr->aignet-lit)))))

(define fgl-pathcond-fix-bfr ((x lbfr-p)
                              pathcond
                              logicman)
  :returns (mv (new-x lbfr-p)
               (new-pathcond (equal new-pathcond (pathcond-fix pathcond))))
  (b* ((x (lbfr-fix x))
       ((mv ansbit pathcond) (logicman-pathcond-implies x pathcond))
       ((when ansbit) (mv (bit->bool ansbit) pathcond)))
    (mv x pathcond))
  ///
  (defret bfr-eval-of-fgl-pathcond-fix-bfr
    (implies (logicman-pathcond-eval env pathcond)
             (equal (bfr-eval new-x env)
                    (bfr-eval x env))))

  (defret gobj-bfr-eval-of-fgl-pathcond-fix-bfr
    (implies (logicman-pathcond-eval (gl-env->bfr-vals env) pathcond)
             (equal (gobj-bfr-eval new-x env)
                    (gobj-bfr-eval x env)))
    :hints(("Goal" :in-theory (enable gobj-bfr-eval))))

  (defret equal-<fn>
    (implies (and (not (booleanp v))
                  (not (equal v (lbfr-fix x))))
             (not (equal v new-x)))))

(define fgl-pathcond-fix-bfrlist ((x lbfr-listp)
                                  pathcond
                                  logicman)
  :returns (mv (new-x lbfr-listp)
               (new-pathcond (equal new-pathcond (pathcond-fix pathcond))))
  (b* (((when (atom x))
        (b* ((pathcond (pathcond-fix pathcond)))
          (mv nil pathcond)))
       ((mv first pathcond) (fgl-pathcond-fix-bfr (car x) pathcond logicman))
       ((mv rest pathcond) (fgl-pathcond-fix-bfrlist (cdr x) pathcond logicman)))
    (mv (cons first rest) pathcond))
  ///
  (defret bfr-list-eval-of-fgl-pathcond-fix-bfrlist
    (implies (logicman-pathcond-eval env pathcond)
             (equal (bfr-list-eval new-x env)
                    (bfr-list-eval x env)))
    :hints(("Goal" :in-theory (enable bfr-list-eval))))

  (defret gobj-bfr-list-eval-of-fgl-pathcond-fix-bfrlist
    (implies (logicman-pathcond-eval (gl-env->bfr-vals env) pathcond)
             (equal (gobj-bfr-list-eval new-x env)
                    (gobj-bfr-list-eval x env)))
    :hints(("Goal" :in-theory (enable gobj-bfr-list-eval))))

  (defret member-of-<fn>
    (implies (and (not (member v (lbfr-list-fix x)))
                  (not (booleanp v)))
             (not (member v new-x)))
    :hints(("Goal" :in-theory (enable bfr-list-fix))))

  (defret true-listp-of-<fn>
    (true-listp new-x)
    :rule-classes :type-prescription))
    

(local (in-theory (disable bfr-listp-when-not-member-witness
                           bfrlist-of-g-ite-accessors
                           member
                           acl2::member-equal-append)))
      
(defines fgl-pathcond-fix-impl
  (define fgl-object-pathcond-fix-impl ((x gl-object-p)
                                        pathcond
                                        logicman)
    :guard (lbfr-listp (gl-object-bfrlist x))
    :returns (mv (new-x gl-object-p)
                 (new-pathcond (equal new-pathcond (pathcond-fix pathcond))))
    :measure (acl2::two-nats-measure (gl-object-count x) 0)
    :verify-guards nil
    (b* ((pathcond (pathcond-fix pathcond))
         (x (gl-object-fix x)))
      (gl-object-case x
        :g-concrete (mv x pathcond)
        :g-boolean (b* (((mv new-bool pathcond) (fgl-pathcond-fix-bfr x.bool pathcond logicman)))
                     (mv (mk-g-boolean new-bool) pathcond))
        :g-integer (b* (((mv new-bits pathcond) (fgl-pathcond-fix-bfrlist x.bits pathcond logicman)))
                     (mv (mk-g-integer new-bits) pathcond))
        :g-ite (b* (((mv new-test pathcond)
                     (fgl-object-pathcond-fix-impl x.test pathcond logicman))
                    ((when (gl-object-case new-test :g-concrete))
                     (if (g-concrete->val new-test)
                         (fgl-object-pathcond-fix-impl x.then pathcond logicman)
                       (fgl-object-pathcond-fix-impl x.else pathcond logicman)))
                    ((mv new-then pathcond) (fgl-object-pathcond-fix-impl x.then pathcond logicman))
                    ((mv new-else pathcond) (fgl-object-pathcond-fix-impl x.else pathcond logicman)))
                 (mv (g-ite new-test new-then new-else) pathcond))
        :g-apply (b* (((mv new-args pathcond)
                       (fgl-objectlist-pathcond-fix-impl x.args pathcond logicman)))
                   (mv (g-apply x.fn new-args) pathcond))
        :g-var (mv x pathcond)
        :g-cons (b* (((mv new-car pathcond) (fgl-object-pathcond-fix-impl x.car pathcond logicman))
                     ((mv new-cdr pathcond) (fgl-object-pathcond-fix-impl x.cdr pathcond logicman)))
                  (mv (mk-g-cons new-car new-cdr) pathcond))
        :g-map (b* (((mv new-alist pathcond)
                     (fgl-object-alist-pathcond-fix-impl x.alist pathcond logicman)))
                 ;; BOZO will need recompressing/make-fast-alist
                 (mv (change-g-map x :alist new-alist) pathcond)))))

  (define fgl-objectlist-pathcond-fix-impl ((x gl-objectlist-p)
                                            pathcond
                                            logicman)
    :guard (lbfr-listp (gl-objectlist-bfrlist x))
    :returns (mv (new-x gl-objectlist-p)
                 (new-pathcond (equal new-pathcond (pathcond-fix pathcond))))
    :measure (acl2::two-nats-measure (gl-objectlist-count x) 0)
    (b* (((when (atom x))
          (b* ((pathcond (pathcond-fix pathcond)))
            (mv nil pathcond)))
         ((mv car pathcond) (fgl-object-pathcond-fix-impl (car x) pathcond logicman))
         ((mv cdr pathcond) (fgl-objectlist-pathcond-fix-impl (cdr x) pathcond logicman)))
      (mv (cons car cdr) pathcond)))

  (define fgl-object-alist-pathcond-fix-impl ((x gl-object-alist-p)
                                            pathcond
                                            logicman)
    :guard (lbfr-listp (gl-object-alist-bfrlist x))
    :returns (mv (new-x gl-object-alist-p)
                 (new-pathcond (equal new-pathcond (pathcond-fix pathcond))))
    :measure (acl2::two-nats-measure (gl-object-alist-count x) (len x))
    (b* (((when (atom x))
          (b* ((pathcond (pathcond-fix pathcond)))
            (mv x pathcond)))
         ((unless (mbt (consp (car x))))
          (fgl-object-alist-pathcond-fix-impl (cdr x) pathcond logicman))
         ((mv cdar pathcond) (fgl-object-pathcond-fix-impl (cdar x) pathcond logicman))
         ((mv cdr pathcond) (fgl-object-alist-pathcond-fix-impl (cdr x) pathcond logicman)))
      (mv (cons (cons (caar x) cdar) cdr) pathcond)))
  ///
  (verify-guards fgl-object-pathcond-fix-impl)

  (defret-mutual eval-of-pathcond-fix-impl
    (defret eval-of-<fn>
      (implies (logicman-pathcond-eval (gl-env->bfr-vals env) pathcond)
               (equal (fgl-object-eval new-x env)
                      (fgl-object-eval x env)))
      :hints ('(:expand (<call>
                         (fgl-object-eval x env))))
      :fn fgl-object-pathcond-fix-impl)
    (defret eval-of-<fn>
      (implies (logicman-pathcond-eval (gl-env->bfr-vals env) pathcond)
               (equal (fgl-objectlist-eval new-x env)
                      (fgl-objectlist-eval x env)))
      :hints ('(:expand (<call>
                         (fgl-objectlist-eval x env))))
      :fn fgl-objectlist-pathcond-fix-impl)
    (defret eval-of-<fn>
      (implies (logicman-pathcond-eval (gl-env->bfr-vals env) pathcond)
               (equal (fgl-object-alist-eval new-x env)
                      (fgl-object-alist-eval x env)))
      :hints ('(:expand (<call>
                         (fgl-object-alist-eval x env))))
      :fn fgl-object-alist-pathcond-fix-impl))

  (defret-mutual lbfr-listp-of-pathcond-fix-impl
    (defret lbfr-listp-of-<fn>
      (lbfr-listp (gl-object-bfrlist new-x))
      :hints ('(:expand (<call>))
              (and stable-under-simplificationp
                   '(:in-theory (enable bfr-listp-when-not-member-witness))))
      :fn fgl-object-pathcond-fix-impl)
    (defret lbfr-listp-of-<fn>
      (lbfr-listp (gl-objectlist-bfrlist new-x))
      :hints ('(:expand (<call>)))
      :fn fgl-objectlist-pathcond-fix-impl)
    (defret lbfr-listp-of-<fn>
      (lbfr-listp (gl-object-alist-bfrlist new-x))
      :hints ('(:expand (<call>)))
      :fn fgl-object-alist-pathcond-fix-impl)))

(set-ignore-ok t)

(local (defthm fgl-objectlist-eval-when-atom
         (implies (not (consp x))
                  (equal (fgl-objectlist-eval x env) nil))
         :hints(("Goal" :in-theory (enable fgl-objectlist-eval)))))

(def-gl-primitive fgl-pathcond-fix (x)
  (stobj-let ((logicman (interp-st->logicman interp-st))
              (pathcond (interp-st->pathcond interp-st)))
             (ans pathcond)
             (fgl-object-pathcond-fix-impl x pathcond logicman)
             (mv t ans interp-st))
  :formula-check fgl-pathcond-fix-formula-checks)

               
  
