; FGL - A Symbolic Simulation Framework for ACL2
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
(include-book "centaur/aignet/self-constprop" :dir :system)
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
    (implies (logicman-pathcond-eval (fgl-env->bfr-vals env) pathcond)
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
    (implies (logicman-pathcond-eval (fgl-env->bfr-vals env) pathcond)
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
  (define fgl-object-pathcond-fix-impl ((x fgl-object-p)
                                        pathcond
                                        logicman)
    :guard (lbfr-listp (fgl-object-bfrlist x))
    :returns (mv (new-x fgl-object-p)
                 (new-pathcond (equal new-pathcond (pathcond-fix pathcond))))
    :measure (acl2::two-nats-measure (fgl-object-count x) 0)
    :verify-guards nil
    (b* ((pathcond (pathcond-fix pathcond))
         (x (fgl-object-fix x)))
      (fgl-object-case x
        :g-concrete (mv x pathcond)
        :g-boolean (b* (((mv new-bool pathcond) (fgl-pathcond-fix-bfr x.bool pathcond logicman)))
                     (mv (mk-g-boolean new-bool) pathcond))
        :g-integer (b* (((mv new-bits pathcond) (fgl-pathcond-fix-bfrlist x.bits pathcond logicman)))
                     (mv (mk-g-integer new-bits) pathcond))
        :g-ite (b* (((mv new-test pathcond)
                     (fgl-object-pathcond-fix-impl x.test pathcond logicman))
                    ((when (fgl-object-case new-test :g-concrete))
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

  (define fgl-objectlist-pathcond-fix-impl ((x fgl-objectlist-p)
                                            pathcond
                                            logicman)
    :guard (lbfr-listp (fgl-objectlist-bfrlist x))
    :returns (mv (new-x fgl-objectlist-p)
                 (new-pathcond (equal new-pathcond (pathcond-fix pathcond))))
    :measure (acl2::two-nats-measure (fgl-objectlist-count x) 0)
    (b* (((when (atom x))
          (b* ((pathcond (pathcond-fix pathcond)))
            (mv nil pathcond)))
         ((mv car pathcond) (fgl-object-pathcond-fix-impl (car x) pathcond logicman))
         ((mv cdr pathcond) (fgl-objectlist-pathcond-fix-impl (cdr x) pathcond logicman)))
      (mv (cons car cdr) pathcond)))

  (define fgl-object-alist-pathcond-fix-impl ((x fgl-object-alist-p)
                                            pathcond
                                            logicman)
    :guard (lbfr-listp (fgl-object-alist-bfrlist x))
    :returns (mv (new-x fgl-object-alist-p)
                 (new-pathcond (equal new-pathcond (pathcond-fix pathcond))))
    :measure (acl2::two-nats-measure (fgl-object-alist-count x) (len x))
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
      (implies (logicman-pathcond-eval (fgl-env->bfr-vals env) pathcond)
               (equal (fgl-object-eval new-x env)
                      (fgl-object-eval x env)))
      :hints ('(:expand (<call>
                         (fgl-object-eval x env))))
      :fn fgl-object-pathcond-fix-impl)
    (defret eval-of-<fn>
      (implies (logicman-pathcond-eval (fgl-env->bfr-vals env) pathcond)
               (equal (fgl-objectlist-eval new-x env)
                      (fgl-objectlist-eval x env)))
      :hints ('(:expand (<call>
                         (fgl-objectlist-eval x env))))
      :fn fgl-objectlist-pathcond-fix-impl)
    (defret eval-of-<fn>
      (implies (logicman-pathcond-eval (fgl-env->bfr-vals env) pathcond)
               (equal (fgl-object-alist-eval new-x env)
                      (fgl-object-alist-eval x env)))
      :hints ('(:expand (<call>
                         (fgl-object-alist-eval x env))))
      :fn fgl-object-alist-pathcond-fix-impl))

  (defret-mutual lbfr-listp-of-pathcond-fix-impl
    (defret lbfr-listp-of-<fn>
      (lbfr-listp (fgl-object-bfrlist new-x))
      :hints ('(:expand (<call>))
              (and stable-under-simplificationp
                   '(:in-theory (enable bfr-listp-when-not-member-witness))))
      :fn fgl-object-pathcond-fix-impl)
    (defret lbfr-listp-of-<fn>
      (lbfr-listp (fgl-objectlist-bfrlist new-x))
      :hints ('(:expand (<call>)))
      :fn fgl-objectlist-pathcond-fix-impl)
    (defret lbfr-listp-of-<fn>
      (lbfr-listp (fgl-object-alist-bfrlist new-x))
      :hints ('(:expand (<call>)))
      :fn fgl-object-alist-pathcond-fix-impl)))


(define bfrlist-min-bound ((x bfr-listp) (bfrstate bfrstate-p))
  :guard (bfrstate-mode-is :aignet)
  :returns (min-bound natp :rule-classes :type-prescription)
  (if (atom x)
      0
    (max (satlink::lit->var (bfr->aignet-lit (car x)))
         (bfrlist-min-bound (cdr x) bfrstate)))
  ///
  (defthm bfr-listp-of-bfrlist-min-bound
    (implies (and (bfrstate-mode-is :aignet)
                  (bfr-listp x)
                  (<= (bfrlist-min-bound x bfrstate) (nfix bound)))
             (bfr-listp x (bfrstate (bfrmode :aignet) bound)))
    :hints(("Goal" :in-theory (enable bfr-listp bfr-p bfr->aignet-lit))))

  (Defthm bfrlist-min-bound-of-append
    (equal (bfrlist-min-bound (append a b) bfrstate)
           (max (bfrlist-min-bound a bfrstate)
                (bfrlist-min-bound b bfrstate))))

  (defthm bfrlist-min-bound-of-logicman-extension
    (implies (and (bind-logicman-extension new old)
                  (bfr-listp x (logicman->bfrstate old)))
             (equal (bfrlist-min-bound x (logicman->bfrstate new))
                    (bfrlist-min-bound x (logicman->bfrstate old))))))

(define bfrs->aignet-lits ((x bfr-listp)
                           (bfrstate bfrstate-p))
  :returns (lits aignet::lit-listp)
  :guard (bfrstate-mode-is :aignet)
  (if (atom x)
      nil
    (cons (bfr->aignet-lit (car x))
          (bfrs->aignet-lits (cdr x) bfrstate)))
  ///
  (defretd lit-max-id-var-of-bfrs->aignet-lits
    (implies (and (bfr-listp x)
                  (bfrstate-mode-is :aignet))
             (equal (aignet::lits-max-id-val lits)
                    (bfrlist-min-bound x bfrstate)))
    :hints(("Goal" :in-theory (enable aignet::lits-max-id-val
                                      bfr-listp bfr-p
                                      bfr->aignet-lit
                                      bfrlist-min-bound))))

  (defret lit-max-id-var-of-bfrs->aignet-lits-less
    (implies (and (bfr-listp x bfrstate1)
                  ;; (<= (bfrstate->bound bfrstate1) (bfrstate->bound bfrstate))
                  (bfrstate-mode-is :aignet bfrstate1)
                  (bfrstate-mode-is :aignet bfrstate)
                  )
             (<= (aignet::lits-max-id-val lits) (bfrstate->bound bfrstate1)))
    :hints(("Goal" :in-theory (enable aignet::lits-max-id-val
                                      bfr-listp
                                      bfr->aignet-lit
                                      aignet-lit->bfr
                                      bfr-p
                                      bounded-lit-fix
                                      bfr-fix)))
    :rule-classes :linear)

  (defret aignet-lit-listp-of-<fn>
    (implies (and (equal bfrstate (logicman->bfrstate))
                  ;; (bfr-listp x (logicman->bfrstate))
                  (lbfr-mode-is :aignet))
             (aignet::aignet-lit-listp lits (logicman->aignet logicman)))
    :hints(("Goal" :in-theory (enable bfr-listp)))))

(define aignet-lits->bfrs ((x aignet::lit-listp)
                           (bfrstate bfrstate-p))
  :guard (and (bfrstate-mode-is :aignet)
              (<= (aignet::lits-max-id-val x) (bfrstate->bound bfrstate)))
  :returns (bfrs true-listp :rule-classes :type-prescription)
  (if (atom x)
      nil
    (cons (aignet-lit->bfr (car x))
          (aignet-lits->bfrs (cdr x) bfrstate)))
  ///
  (defret bfr-listp-of-<fn>
    (implies (bfrstate-mode-is :aignet)
             (bfr-listp bfrs))))




(defines fgl-pathcond-fix-aignet-impl
  (define fgl-object-pathcond-fix-aignet-impl ((x fgl-object-p)
                                               aignet::mark
                                               aignet::copy
                                               logicman)
    :guard (and (lbfr-mode-is :aignet)
                (posp (aignet::bits-length aignet::mark))
                (bfr-listp (fgl-object-bfrlist x) (bfrstate (bfrmode :aignet) (+ -1 (aignet::bits-length aignet::mark))))
                (lbfr-listp (fgl-object-bfrlist x))
                (stobj-let ((aignet (logicman->aignet logicman)))
                           (ok)
                           (aignet::self-constprop-guard aignet aignet::mark aignet::copy)
                           ok))
    :returns (mv (new-x fgl-object-p)
                 (new-mark)
                 (new-copy)
                 (new-logicman))
    :measure (acl2::two-nats-measure (fgl-object-count x) 0)
    :verify-guards nil
    (b* ((x (fgl-object-fix x)))
      (fgl-object-case x
        :g-concrete (mv x aignet::mark aignet::copy logicman)
        :g-boolean (b* ((bfrstate (logicman->bfrstate))
                        (lit (bfr->aignet-lit x.bool)))
                     (stobj-let ((strash (logicman->strash logicman))
                                 (aignet (logicman->aignet logicman)))
                                (aignet::mark aignet::copy strash aignet)
                                (aignet::aignet-self-copy-dfs-rec (aignet::lit->var lit)
                                                                  aignet
                                                                  aignet::mark
                                                                  aignet::copy
                                                                  strash
                                                                  (aignet::default-gatesimp))
                                (b* ((ans (aignet::lit-copy lit aignet::copy))
                                     (bfrstate (logicman->bfrstate logicman)))
                                  (mv (mk-g-boolean (aignet-lit->bfr ans))
                                      aignet::mark aignet::copy logicman))))
        :g-integer (b* ((bfrstate (logicman->bfrstate))
                        (lits (bfrs->aignet-lits x.bits bfrstate)))
                     (stobj-let ((strash (logicman->strash logicman))
                                 (aignet (logicman->aignet logicman)))
                                (aignet::mark aignet::copy strash aignet)
                                (aignet::aignet-self-copy-dfs-rec-list lits
                                                                       aignet
                                                                       aignet::mark
                                                                       aignet::copy
                                                                       strash
                                                                       (aignet::default-gatesimp))
                                (b* ((ans (aignet::lit-list-copies lits aignet::copy))
                                     (bfrstate (logicman->bfrstate logicman)))
                                  (mv (mk-g-integer (aignet-lits->bfrs ans bfrstate))
                                      aignet::mark aignet::copy logicman))))



        :g-ite (b* (((mv new-test aignet::mark aignet::copy logicman)
                     (fgl-object-pathcond-fix-aignet-impl x.test aignet::mark aignet::copy logicman))
                    ((mv okp new-test-bool) (gobj-syntactic-boolean-fix new-test))
                    ((when (and okp (fgl-object-case new-test-bool :g-concrete)))
                     (if (g-concrete->val new-test-bool)
                         (fgl-object-pathcond-fix-aignet-impl x.then aignet::mark aignet::copy logicman)
                       (fgl-object-pathcond-fix-aignet-impl x.else aignet::mark aignet::copy logicman)))
                    ((mv new-then aignet::mark aignet::copy logicman) (fgl-object-pathcond-fix-aignet-impl x.then aignet::mark aignet::copy logicman))
                    ((mv new-else aignet::mark aignet::copy logicman) (fgl-object-pathcond-fix-aignet-impl x.else aignet::mark aignet::copy logicman)))
                 (mv (g-ite new-test new-then new-else) aignet::mark aignet::copy logicman))
        :g-apply (b* (((mv new-args aignet::mark aignet::copy logicman)
                       (fgl-objectlist-pathcond-fix-aignet-impl x.args aignet::mark aignet::copy logicman)))
                   (mv (g-apply x.fn new-args) aignet::mark aignet::copy logicman))
        :g-var (mv x aignet::mark aignet::copy logicman)
        :g-cons (b* (((mv new-car aignet::mark aignet::copy logicman) (fgl-object-pathcond-fix-aignet-impl x.car aignet::mark aignet::copy logicman))
                     ((mv new-cdr aignet::mark aignet::copy logicman) (fgl-object-pathcond-fix-aignet-impl x.cdr aignet::mark aignet::copy logicman)))
                  (mv (mk-g-cons new-car new-cdr) aignet::mark aignet::copy logicman))
        :g-map (b* (((mv new-alist aignet::mark aignet::copy logicman)
                     (fgl-object-alist-pathcond-fix-aignet-impl x.alist aignet::mark aignet::copy logicman)))
                 ;; BOZO will need recompressing/make-fast-alist
                 (mv (change-g-map x :alist new-alist) aignet::mark aignet::copy logicman)))))

  (define fgl-objectlist-pathcond-fix-aignet-impl ((x fgl-objectlist-p)
                                                   aignet::mark aignet::copy
                                                   logicman)
    :guard (and (lbfr-mode-is :aignet)
                (posp (aignet::bits-length aignet::mark))
                (bfr-listp (fgl-objectlist-bfrlist x) (bfrstate (bfrmode :aignet) (+ -1 (aignet::bits-length aignet::mark))))
                (lbfr-listp (fgl-objectlist-bfrlist x))
                (stobj-let ((aignet (logicman->aignet logicman)))
                           (ok)
                           (aignet::self-constprop-guard aignet aignet::mark aignet::copy)
                           ok))
    :returns (mv (new-x fgl-objectlist-p)
                 (new-mark)
                 (new-copy)
                 (new-logicman))
    :measure (acl2::two-nats-measure (fgl-objectlist-count x) 0)
    (b* (((when (atom x))
          (mv nil aignet::mark aignet::copy logicman))
         ((mv car aignet::mark aignet::copy logicman) (fgl-object-pathcond-fix-aignet-impl (car x) aignet::mark aignet::copy logicman))
         ((mv cdr aignet::mark aignet::copy logicman) (fgl-objectlist-pathcond-fix-aignet-impl (cdr x) aignet::mark aignet::copy logicman)))
      (mv (cons car cdr) aignet::mark aignet::copy logicman)))

  (define fgl-object-alist-pathcond-fix-aignet-impl ((x fgl-object-alist-p)
                                                     aignet::mark aignet::copy
                                                     logicman)
    :guard (and (lbfr-mode-is :aignet)
                (posp (aignet::bits-length aignet::mark))
                (bfr-listp (fgl-object-alist-bfrlist x) (bfrstate (bfrmode :aignet) (+ -1 (aignet::bits-length aignet::mark))))
                (lbfr-listp (fgl-object-alist-bfrlist x))
                (stobj-let ((aignet (logicman->aignet logicman)))
                           (ok)
                           (aignet::self-constprop-guard aignet aignet::mark aignet::copy)
                           ok))
    :returns (mv (new-x fgl-object-alist-p)
                 (new-mark)
                 (new-copy)
                 (new-logicman))
    :measure (acl2::two-nats-measure (fgl-object-alist-count x) (len x))
    (b* (((when (atom x))
          (mv x aignet::mark aignet::copy logicman))
         ((unless (mbt (consp (car x))))
          (fgl-object-alist-pathcond-fix-aignet-impl (cdr x) aignet::mark aignet::copy logicman))
         ((mv cdar aignet::mark aignet::copy logicman) (fgl-object-pathcond-fix-aignet-impl (cdar x) aignet::mark aignet::copy logicman))
         ((mv cdr aignet::mark aignet::copy logicman) (fgl-object-alist-pathcond-fix-aignet-impl (cdr x) aignet::mark aignet::copy logicman)))
      (mv (cons (cons (caar x) cdar) cdr) aignet::mark aignet::copy logicman)))
  ///
  (local (in-theory (disable fgl-object-pathcond-fix-aignet-impl
                             fgl-objectlist-pathcond-fix-aignet-impl
                             fgl-object-alist-pathcond-fix-aignet-impl)))

  (defret-mutual logicman-get-of-pathcond-fix-aignet-impl
    (defret logicman-get-of-<fn>
      (implies (and (not (equal (logicman-field-fix key) :aignet))
                    (not (equal (logicman-field-fix key) :strash)))
               (equal (logicman-get key new-logicman)
                      (logicman-get key logicman)))
      :hints ('(:expand (<call>)))
      :fn fgl-object-pathcond-fix-aignet-impl)
    (defret logicman-get-of-<fn>
      (implies (and (not (equal (logicman-field-fix key) :aignet))
                    (not (equal (logicman-field-fix key) :strash)))
               (equal (logicman-get key new-logicman)
                      (logicman-get key logicman)))
      :hints ('(:expand (<call>)))
      :fn fgl-objectlist-pathcond-fix-aignet-impl)
    (defret logicman-get-of-<fn>
      (implies (and (not (equal (logicman-field-fix key) :aignet))
                    (not (equal (logicman-field-fix key) :strash)))
               (equal (logicman-get key new-logicman)
                      (logicman-get key logicman)))
      :hints ('(:expand (<call>)))
      :fn fgl-object-alist-pathcond-fix-aignet-impl))

  (defret-mutual aignet-extension-p-of-pathcond-fix-aignet-impl
    (defret aignet-extension-p-of-<fn>
      (aignet::aignet-extension-p (logicman->aignet new-logicman)
                                  (logicman->aignet logicman))
      :hints ('(:expand (<call>)))
      :fn fgl-object-pathcond-fix-aignet-impl)
    (defret aignet-extension-p-of-<fn>
      (aignet::aignet-extension-p (logicman->aignet new-logicman)
                                  (logicman->aignet logicman))
      :hints ('(:expand (<call>)))
      :fn fgl-objectlist-pathcond-fix-aignet-impl)
    (defret aignet-extension-p-of-<fn>
      (aignet::aignet-extension-p (logicman->aignet new-logicman)
                                  (logicman->aignet logicman))
      :hints ('(:expand (<call>)))
      :fn fgl-object-alist-pathcond-fix-aignet-impl))

  (defret-mutual logicman-extension-p-of-pathcond-fix-aignet-impl
    (defret logicman-extension-p-of-<fn>
      (logicman-extension-p new-logicman logicman)
      :hints ('(:expand (<call>))
              (and stable-under-simplificationp
                   '(:in-theory (enable logicman-extension-p))))
      :fn fgl-object-pathcond-fix-aignet-impl)
    (defret logicman-extension-p-of-<fn>
      (logicman-extension-p new-logicman logicman)
      :hints ('(:expand (<call>)))
      :fn fgl-objectlist-pathcond-fix-aignet-impl)
    (defret logicman-extension-p-of-<fn>
      (logicman-extension-p new-logicman logicman)
      :hints ('(:expand (<call>)))
      :fn fgl-object-alist-pathcond-fix-aignet-impl))

  (defret-mutual pi-count-of-pathcond-fix-aignet-impl
    (defret pi-count-of-<fn>
      (equal (aignet::stype-count :pi (logicman->aignet new-logicman))
             (aignet::stype-count :pi (logicman->aignet logicman)))
      :hints ('(:expand (<call>)))
      :fn fgl-object-pathcond-fix-aignet-impl)
    (defret pi-count-of-<fn>
      (equal (aignet::stype-count :pi (logicman->aignet new-logicman))
             (aignet::stype-count :pi (logicman->aignet logicman)))
      :hints ('(:expand (<call>)))
      :fn fgl-objectlist-pathcond-fix-aignet-impl)
    (defret pi-count-of-<fn>
      (equal (aignet::stype-count :pi (logicman->aignet new-logicman))
             (aignet::stype-count :pi (logicman->aignet logicman)))
      :hints ('(:expand (<call>)))
      :fn fgl-object-alist-pathcond-fix-aignet-impl))

  (defret-mutual reg-count-of-pathcond-fix-aignet-impl
    (defret reg-count-of-<fn>
      (equal (aignet::stype-count :reg (logicman->aignet new-logicman))
             (aignet::stype-count :reg (logicman->aignet logicman)))
      :hints ('(:expand (<call>)))
      :fn fgl-object-pathcond-fix-aignet-impl)
    (defret reg-count-of-<fn>
      (equal (aignet::stype-count :reg (logicman->aignet new-logicman))
             (aignet::stype-count :reg (logicman->aignet logicman)))
      :hints ('(:expand (<call>)))
      :fn fgl-objectlist-pathcond-fix-aignet-impl)
    (defret reg-count-of-<fn>
      (equal (aignet::stype-count :reg (logicman->aignet new-logicman))
             (aignet::stype-count :reg (logicman->aignet logicman)))
      :hints ('(:expand (<call>)))
      :fn fgl-object-alist-pathcond-fix-aignet-impl))

  (local (defthm <=-of-max-1
           (<= x (max x y))
           :rule-classes :linear))
  (local (defthm <=-of-max-2
           (<= y (max x y))
           :rule-classes :linear))

  (local (in-theory (disable max)))

  ;; (local (def-updater-independence-thm self-constprop-guard-of-logicman-aignet-extension
  ;;          #!aignet
  ;;          (implies (and (aignet-extension-p (fgl::logicman->aignet new) (fgl::logicman->aignet old))
  ;;                        (self-constprop-guard bound (fgl::logicman->aignet old) mark copy)
  ;;                        (equal (stype-count :pi (fgl::logicman->aignet new)) (stype-count :pi (fgl::logicman->aignet old)))
  ;;                        (equal (stype-count :reg (fgl::logicman->aignet new)) (stype-count :reg (fgl::logicman->aignet old))))
  ;;                   (self-constprop-guard bound (fgl::logicman->aignet new) mark copy))
  ;;          :hints (("goal" :use ((:instance aignet::self-constprop-guard-of-aignet-extension
  ;;                                 (orig (logicman->aignet old))
  ;;                                 (new (logicman->aignet new))))))))

  (local (in-theory (disable equal-of-booleans-rewrite
                             append
                             bfr-listp$-when-subsetp-equal
                             ;; self-constprop-guard-of-logicman-aignet-extension
                             )))

  (local (defthm lit->var-of-bfr->aignet-lit-bound-by-bfr-p
           (implies (and (bfr-p x (bfrstate (bfrmode :aignet) bound))
                          (bfrstate-mode-is :aignet bfrstate))
                    (<= (satlink::lit->var (bfr->aignet-lit x bfrstate)) (nfix bound)))
           :hints(("Goal" :in-theory (enable bfr-p bfr->aignet-lit bfr-fix aignet-lit->bfr bounded-lit-fix)))
           :rule-classes :linear))
  
  (defret-mutual copy-len-of-pathcond-fix-aignet-impl
    (defret copy-len-of-<fn>
      (implies (and (lbfr-mode-is :aignet)
                    (< 0 (len aignet::copy))
                    (bfr-listp (fgl-object-bfrlist x) (bfrstate (bfrmode :aignet) (+ -1 (len aignet::copy)))))
               (equal (len new-copy) (len aignet::copy)))
      :hints ('(:expand (<call>))
              (And stable-under-simplificationp
                   '(:in-theory (enable aignet::lits-max-id-val-when-aignet-lit-listp))))
      :fn fgl-object-pathcond-fix-aignet-impl)
    (defret copy-len-of-<fn>
      (implies (and (lbfr-mode-is :aignet)
                    (< 0 (len aignet::copy))
                    (bfr-listp (fgl-objectlist-bfrlist x) (bfrstate (bfrmode :aignet) (+ -1 (len aignet::copy)))))
               (equal (len new-copy) (len aignet::copy)))
      :hints ('(:expand (<call>)))
      :fn fgl-objectlist-pathcond-fix-aignet-impl)
    (defret copy-len-of-<fn>
      (implies (and (lbfr-mode-is :aignet)
                    (< 0 (len aignet::copy))
                    (bfr-listp (fgl-object-alist-bfrlist x) (bfrstate (bfrmode :aignet) (+ -1 (len aignet::copy)))))
               (equal (len new-copy) (len aignet::copy)))
      :hints ('(:expand (<call>
                         (fgl-object-alist-bfrlist x))))
      :fn fgl-object-alist-pathcond-fix-aignet-impl))

  (defret-mutual mark-len-of-pathcond-fix-aignet-impl
    (defret mark-len-of-<fn>
      (implies (and (lbfr-mode-is :aignet)
                    (< 0 (len aignet::mark))
                    (bfr-listp (fgl-object-bfrlist x) (bfrstate (bfrmode :aignet) (+ -1 (len aignet::mark)))))
               (equal (len new-mark) (len aignet::mark)))
      :hints ('(:expand (<call>))
              (And stable-under-simplificationp
                   '(:in-theory (enable aignet::lits-max-id-val-when-aignet-lit-listp))))
      :fn fgl-object-pathcond-fix-aignet-impl)
    (defret mark-len-of-<fn>
      (implies (and (lbfr-mode-is :aignet)
                    (< 0 (len aignet::mark))
                    (bfr-listp (fgl-objectlist-bfrlist x) (bfrstate (bfrmode :aignet) (+ -1 (len aignet::mark)))))
               (equal (len new-mark) (len aignet::mark)))
      :hints ('(:expand (<call>)))
      :fn fgl-objectlist-pathcond-fix-aignet-impl)
    (defret mark-len-of-<fn>
      (implies (and (lbfr-mode-is :aignet)
                    (< 0 (len aignet::mark))
                    (bfr-listp (fgl-object-alist-bfrlist x) (bfrstate (bfrmode :aignet) (+ -1 (len aignet::mark)))))
               (equal (len new-mark) (len aignet::mark)))
      :hints ('(:expand (<call>
                         (fgl-object-alist-bfrlist x))))
      :fn fgl-object-alist-pathcond-fix-aignet-impl))


  (defret-mutual self-constprop-guard-of-pathcond-fix-aignet-impl
    (defret self-constprop-guard-of-<fn>
      (implies (and (aignet::self-constprop-guard (logicman->aignet logicman) aignet::mark aignet::copy)
                    (lbfr-mode-is :aignet)
                    (< 0 (len aignet::copy))
                    (bfr-listp (fgl-object-bfrlist x) (bfrstate (bfrmode :aignet) (+ -1 (len aignet::copy)))))
               (aignet::self-constprop-guard (logicman->aignet new-logicman) new-mark new-copy))
      :hints ('(:expand (<call>)))
      :fn fgl-object-pathcond-fix-aignet-impl)
    (defret self-constprop-guard-of-<fn>
      (implies (and (aignet::self-constprop-guard (logicman->aignet logicman) aignet::mark aignet::copy)
                    (lbfr-mode-is :aignet)
                    (< 0 (len aignet::copy))
                    (bfr-listp (fgl-objectlist-bfrlist x) (bfrstate (bfrmode :aignet) (+ -1 (len aignet::copy)))))
               (aignet::self-constprop-guard (logicman->aignet new-logicman) new-mark new-copy))
      :hints ('(:expand (<call>)))
      :fn fgl-objectlist-pathcond-fix-aignet-impl)
    (defret self-constprop-guard-of-<fn>
      (implies (and (aignet::self-constprop-guard (logicman->aignet logicman) aignet::mark aignet::copy)
                    (lbfr-mode-is :aignet)
                    (< 0 (len aignet::copy))
                    (bfr-listp (fgl-object-alist-bfrlist x) (bfrstate (bfrmode :aignet) (+ -1 (len aignet::copy)))))
               (aignet::self-constprop-guard (logicman->aignet new-logicman) new-mark new-copy))
      :hints ('(:expand (<call>
                         (fgl-object-alist-bfrlist x))))
      :fn fgl-object-alist-pathcond-fix-aignet-impl))



  ;; (defret self-constprop-guard-of-<fn>-less
  ;;   (implies (and (aignet::self-constprop-guard bound (logicman->aignet logicman) aignet::mark aignet::copy)
  ;;                 (lbfr-listp (fgl-object-bfrlist x))
  ;;                 (lbfr-mode-is :aignet)
  ;;                 (< (bfrlist-min-bound (fgl-object-bfrlist x) (logicman->bfrstate)) (nfix bound))
  ;;                 (<= (nfix bound1) (nfix bound)))
  ;;            (aignet::self-constprop-guard bound1 (logicman->aignet new-logicman) new-mark new-copy))
  ;;   :hints (("goal" :use self-constprop-guard-of-fgl-object-pathcond-fix-aignet-impl
  ;;            :in-theory (disable self-constprop-guard-of-fgl-object-pathcond-fix-aignet-impl)))
  ;;   :fn fgl-object-pathcond-fix-aignet-impl)
  ;; (defret self-constprop-guard-of-<fn>-less
  ;;   (implies (and (aignet::self-constprop-guard bound (logicman->aignet logicman) aignet::mark aignet::copy)
  ;;                 (lbfr-listp (fgl-objectlist-bfrlist x))
  ;;                 (lbfr-mode-is :aignet)
  ;;                 (< (bfrlist-min-bound (fgl-objectlist-bfrlist x) (logicman->bfrstate)) (nfix bound))
  ;;                 (<= (nfix bound1) (nfix bound)))
  ;;            (aignet::self-constprop-guard bound1 (logicman->aignet new-logicman) new-mark new-copy))
  ;;   :hints (("goal" :use self-constprop-guard-of-fgl-objectlist-pathcond-fix-aignet-impl
  ;;            :in-theory (disable self-constprop-guard-of-fgl-objectlist-pathcond-fix-aignet-impl)))
  ;;   :fn fgl-objectlist-pathcond-fix-aignet-impl)
  ;; (defret self-constprop-guard-of-<fn>-less
  ;;   (implies (and (aignet::self-constprop-guard bound (logicman->aignet logicman) aignet::mark aignet::copy)
  ;;                 (lbfr-listp (fgl-object-alist-bfrlist x))
  ;;                 (lbfr-mode-is :aignet)
  ;;                 (< (bfrlist-min-bound (fgl-object-alist-bfrlist x) (logicman->bfrstate)) (nfix bound))
  ;;                 (<= (nfix bound1) (nfix bound)))
  ;;            (aignet::self-constprop-guard bound1 (logicman->aignet new-logicman) new-mark new-copy))
  ;;   :hints (("goal" :use self-constprop-guard-of-fgl-object-alist-pathcond-fix-aignet-impl
  ;;            :in-theory (disable self-constprop-guard-of-fgl-object-alist-pathcond-fix-aignet-impl)))
  ;;   :fn fgl-object-alist-pathcond-fix-aignet-impl)

  (local
   #!aignet
   (defthmd lits-max-id-val-when-aignet-lit-listp-rw
     (implies (aignet-lit-listp lits aignet)
              (<= (lits-max-id-val lits) (fanin-count aignet)))
     :hints(("Goal" :in-theory (enable lits-max-id-val-when-aignet-lit-listp)))))

  (local (in-theory (disable equal-of-len len-equal-0)))
  
  (local
   #!aignet
   (defthmd lit->var-lte-fanin-count
     (implies (aignet-litp lit aignet)
              (<= (lit->var lit) (fanin-count aignet)))
     :hints(("Goal" :in-theory (enable aignet-idp)))))

  (verify-guards fgl-object-pathcond-fix-aignet-impl
    ;; :guard-debug t
    :hints(("Goal" :in-theory (enable aignet::lits-max-id-val-when-aignet-lit-listp-rw
                                      aignet::lit->var-lte-fanin-count)
            :do-not-induct t)))

  (defret-mutual self-constprop-invar-of-pathcond-fix-aignet-impl
    (defret self-constprop-invar-of-<fn>
      (implies (and (aignet::self-constprop-invar invals regvals (logicman->aignet logicman) aignet::mark aignet::copy)
                    (lbfr-mode-is :aignet)
                    (lbfr-listp (fgl-object-bfrlist x)))
               (aignet::self-constprop-invar invals regvals (logicman->aignet new-logicman) new-mark new-copy))
      :hints ('(:expand (<call>))
              (and stable-under-simplificationp
                   '(:in-theory (enable bfr-listp-when-not-member-witness))))
      :fn fgl-object-pathcond-fix-aignet-impl)
    (defret self-constprop-invar-of-<fn>
      (implies (and (aignet::self-constprop-invar invals regvals (logicman->aignet logicman) aignet::mark aignet::copy)
                    (lbfr-mode-is :aignet)
                    (lbfr-listp (fgl-objectlist-bfrlist x)))
               (aignet::self-constprop-invar invals regvals (logicman->aignet new-logicman) new-mark new-copy))
      :hints ('(:expand (<call>)))
      :fn fgl-objectlist-pathcond-fix-aignet-impl)
    (defret self-constprop-invar-of-<fn>
      (implies (and (aignet::self-constprop-invar invals regvals (logicman->aignet logicman) aignet::mark aignet::copy)
                    (lbfr-mode-is :aignet)
                    (lbfr-listp (fgl-object-alist-bfrlist x)))
               (aignet::self-constprop-invar invals regvals (logicman->aignet new-logicman) new-mark new-copy))
      :hints ('(:expand (<call>
                         (fgl-object-alist-bfrlist x))))
      :fn fgl-object-alist-pathcond-fix-aignet-impl))

  (local (defthm bfr-listp-of-mk-g-integer
           (implies (bfr-listp bits)
                    (bfr-listp (fgl-object-bfrlist (mk-g-integer bits))))
           :hints(("Goal" :in-theory (enable mk-g-integer)))))

  (defret-mutual lbfr-listp-of-pathcond-fix-aignet-impl
    (defret lbfr-listp-of-<fn>
      (implies (lbfr-mode-is :aignet)
               (lbfr-listp (fgl-object-bfrlist new-x) new-logicman))
      :hints ('(:expand (<call>))
              (and stable-under-simplificationp
                   '(:in-theory (enable bfr-listp-when-not-member-witness))))
      :fn fgl-object-pathcond-fix-aignet-impl)
    (defret lbfr-listp-of-<fn>
      (implies (lbfr-mode-is :aignet)
               (lbfr-listp (fgl-objectlist-bfrlist new-x) new-logicman))
      :hints ('(:expand (<call>)))
      :fn fgl-objectlist-pathcond-fix-aignet-impl)
    (defret lbfr-listp-of-<fn>
      (implies (lbfr-mode-is :aignet)
               (lbfr-listp (fgl-object-alist-bfrlist new-x) new-logicman))
      :hints ('(:expand (<call>)))
      :fn fgl-object-alist-pathcond-fix-aignet-impl))

  (local (defretd eval-of-gobj-syntactic-boolean-fix
           (implies okp
                    (equal (fgl-object-eval new-x env)
                           (bool-fix (fgl-object-eval x env))))
           :hints(("Goal" :in-theory (enable gobj-syntactic-boolean-fix
                                             fgl-object-eval)))
           :fn gobj-syntactic-boolean-fix))
  (local (in-theory (disable fgl-object-eval-when-gobj-syntactic-booleanp)))

  (local (defthm bfr-eval-of-aignet-lit->bfr
           (implies (lbfr-mode-is :aignet)
                    (equal (bfr-eval (aignet-lit->bfr lit (logicman->bfrstate)) env logicman)
                           (b* ((invals (alist-to-bitarr (aignet::stype-count :pi (logicman->aignet logicman))
                                                         env nil))
                                (regvals nil))
                             (bit->bool (aignet::lit-eval lit invals regvals (logicman->aignet logicman))))))
           :hints(("Goal" :in-theory (enable bfr-eval)))))

  (local (defthm gobj-bfr-list-eval-of-aignet-lits->bfrs
           (implies (lbfr-mode-is :aignet)
                    (equal (gobj-bfr-list-eval
                            (aignet-lits->bfrs lits (logicman->bfrstate))
                            env logicman)
                           (b* ((invals (alist-to-bitarr (aignet::stype-count :pi (logicman->aignet logicman))
                                                         (fgl-env->bfr-vals env) nil))
                                (regvals nil))
                             (bits->bools (aignet::lit-eval-list lits invals regvals (logicman->aignet logicman))))))
           :hints(("Goal" :in-theory (e/d (gobj-bfr-list-eval
                                             bfr-list-eval
                                             aignet-lits->bfrs
                                             aignet::lit-eval-list
                                             bits->bools)
                                          (gobj-bfr-list-eval-reduce-by-bfr-list-eval))))))

  (local (defthm lit-eval-list-of-bfrs->aignet-lits
           (implies (lbfr-mode-is :aignet)
                    (equal (aignet::lit-eval-list (bfrs->aignet-lits bfrs (logicman->bfrstate))
                                                  (alist-to-bitarr (aignet::stype-count :pi (logicman->aignet logicman))
                                                                   (fgl-env->bfr-vals env) nil)
                                                  nil
                                                  (logicman->aignet logicman))
                           (bools->bits (gobj-bfr-list-eval bfrs env))))
           :hints(("Goal" :in-theory (e/d (gobj-bfr-list-eval
                                           bfrs->aignet-lits
                                           aignet::lit-eval-list
                                           gobj-bfr-eval
                                           bools->bits
                                           bfr-eval)
                                          (gobj-bfr-list-eval-reduce-by-bfr-list-eval
                                           gobj-bfr-eval-reduce-by-bfr-eval))))))
  (local (defthm bits->bools-of-bools->bits
           (equal (bits->bools (bools->bits x))
                  (acl2::boolean-list-fix x))
           :hints(("Goal" :in-theory (enable bits->bools bools->bits)))))

  (local
   #!aignet
   (defthm lit-eval-list-of-lit-list-copies-under-self-constprop-invar
     (implies (and (self-constprop-invar invals regvals aignet mark copy)
                   (lit-list-marked lits mark))
              (equal (lit-eval-list (lit-list-copies lits copy) invals regvals aignet)
                     (lit-eval-list lits invals regvals aignet)))
     :hints(("Goal" :in-theory (enable lit-list-marked lit-eval-list lit-list-copies
                                       self-constprop-invar)))))

  (local
   #!aignet
   (defthm lit-eval-list-of-lit-list-copies-when-self-constprop-invar-aignet-self-copy-dfs-rec-list
     (implies (and (self-constprop-invar invals regvals aignet mark copy)
                   (aignet-lit-listp lits aignet))
              (b* (((mv ?new-mark new-copy ?new-strash new-aignet)
                    (aignet-self-copy-dfs-rec-list lits aignet mark copy strash gatesimp)))
                (equal (lit-eval-list (lit-list-copies lits new-copy) invals regvals new-aignet)
                       (lit-eval-list lits invals regvals aignet))))
     :hints (("goal" :use ((:instance aignet-self-copy-dfs-rec-list-preserves-self-constprop-invar))
              :in-theory (disable aignet-self-copy-dfs-rec-list-preserves-self-constprop-invar)))))

  (local
   #!aignet
   (defthm lit-eval-of-lit-copy-under-self-constprop-invar
     (implies (and (self-constprop-invar invals regvals aignet mark copy)
                   (equal (nth (lit->Var lit) mark) 1))
              (equal (lit-eval (lit-copy lit copy) invals regvals aignet)
                     (lit-eval lit invals regvals aignet)))
     :hints(("Goal" :in-theory (enable self-constprop-invar)))))

  (local
   #!aignet
   (defthm lit-eval-of-lit-copy-when-self-constprop-invar-aignet-self-copy-dfs-rec
     (implies (and (self-constprop-invar invals regvals aignet mark copy)
                   (aignet-litp lit aignet))
              (b* (((mv ?new-mark new-copy ?new-strash new-aignet)
                    (aignet-copy-dfs-rec (lit->var lit) aignet mark copy strash gatesimp aignet)))
                (equal (lit-eval (lit-copy lit new-copy) invals regvals new-aignet)
                       (lit-eval lit invals regvals aignet))))
     :hints (("goal" :use ((:instance aignet-copy-dfs-rec-preserves-self-constprop-invar
                            (id (lit->var lit))))
              :in-theory (disable aignet-copy-dfs-rec-preserves-self-constprop-invar)))))

  (defret-mutual eval-of-pathcond-fix-aignet-impl
    (defret eval-of-<fn>
      (b* ((invals (alist-to-bitarr (aignet::stype-count :pi (logicman->aignet logicman))
                                    (fgl-env->bfr-vals env) nil))
           (regvals nil))
        (implies (and (aignet::self-constprop-invar invals regvals
                                                    (logicman->aignet logicman)
                                                    aignet::mark aignet::copy)
                      (lbfr-mode-is :aignet)
                      (lbfr-listp (fgl-object-bfrlist x)))
                 (equal (fgl-object-eval new-x env new-logicman)
                        (fgl-object-eval x env logicman))))
      :hints ('(:expand (<call>))
              (acl2::use-termhint
               (fgl-object-case x
                 :g-ite
                 (b* (((mv new-test aignet::mark aignet::copy logicman)
                       (fgl-object-pathcond-fix-aignet-impl x.test aignet::mark aignet::copy logicman))
                      ((mv okp new-test-bool) (gobj-syntactic-boolean-fix new-test)))
                   `(:use ((:instance eval-of-gobj-syntactic-boolean-fix
                            (x ,(acl2::hq new-test))
                            (logicman ,(acl2::hq logicman))))
                     :expand ((fgl-object-eval ,(acl2::hq new-test-bool) env ,(acl2::hq logicman)))))
                 :g-boolean '(:in-theory (e/d (gobj-bfr-eval bfr-eval)
                                              (gobj-bfr-eval-reduce-by-bfr-eval)))
                 :otherwise
                 '(:expand ((fgl-object-eval x env logicman))))))
      :fn fgl-object-pathcond-fix-aignet-impl)
    (defret eval-of-<fn>
      (b* ((invals (alist-to-bitarr (aignet::stype-count :pi (logicman->aignet logicman))
                                    (fgl-env->bfr-vals env) nil))
           (regvals nil))
        (implies (and (aignet::self-constprop-invar invals regvals
                                                    (logicman->aignet logicman)
                                                    aignet::mark aignet::copy)
                      (lbfr-mode-is :aignet)
                      (lbfr-listp (fgl-objectlist-bfrlist x)))
                 (equal (fgl-objectlist-eval new-x env new-logicman)
                        (fgl-objectlist-eval x env logicman))))
      :hints ('(:expand (<call>
                         (fgl-objectlist-eval x env logicman))))
      :fn fgl-objectlist-pathcond-fix-aignet-impl)
    (defret eval-of-<fn>
      (b* ((invals (alist-to-bitarr (aignet::stype-count :pi (logicman->aignet logicman))
                                    (fgl-env->bfr-vals env) nil))
           (regvals nil))
        (implies (and (aignet::self-constprop-invar invals regvals
                                                    (logicman->aignet logicman)
                                                    aignet::mark aignet::copy)
                      (lbfr-mode-is :aignet)
                      (lbfr-listp (fgl-object-alist-bfrlist x)))
                 (equal (fgl-object-alist-eval new-x env new-logicman)
                        (fgl-object-alist-eval x env logicman))))
      :hints ('(:expand (<call>
                         (fgl-object-alist-eval x env logicman)
                         (fgl-object-alist-bfrlist x))))
      :fn fgl-object-alist-pathcond-fix-aignet-impl))
)


(set-ignore-ok t)






;; (define fgl-object-pathcond-fix ((x fgl-object-p)
;;                                  (pathcond)
;;                                  (logicman))
;;   :returns (mv (new-x fgl-object-p)
;;                (new-pathcond (equal new-pathcond (pathcond-fix pathcond)))
;;                (new-logicman))
;;   (lbfr-case
;;     :aignet (b* ((pathcond (mbe :logic (pathcond-fix pathcond) :exec pathcond))
;;                  (cube (pathcond-to-cube pathcond nil))
;;                  (lits (bfrs->aignet-lits cube (logicman->bfrstate)))
;;                  ((local-stobjs aignet::mark aignet::copy)
;;                   (mv ans pathcond logicman aignet::mark aignet::copy)))
;;               (stobj-let ((aignet (logicman->aignet logicman)))
;;                          (aignet::mark aignet::copy)
;;                          (aignet-self-constprop-prep lits aignet aignet::mark aignet::copy)
;;                          (b* (((mv ans aignet::mark aignet::copy logicman)
;;                                (fgl-object-pathcond-fix-aignet-impl
;;                                 x aignet::mark aignet::copy logicman)))
;;                            (mv ans pathcond logicman aignet::mark aignet::copy))))
;;     :otherwise (b* (((mv ans pathcond) (fgl-object-pathcond-fix-impl x pathcond logicman)))
;;                  (mv ans pathcond logicman)))
;;   ///
;;   (


(local
 (set-default-hints
  '((and stable-under-simplificationp
         '(:in-theory (enable logicman->bfrstate))))))

(local (in-theory (enable bfr-listp-when-not-member-witness)))

(local #!aignet
       (defthm aignet-eval-conjunction-of-nil
         (equal (aignet-eval-conjunction nil invals regvals aignet) 1)
         :hints(("Goal" :in-theory (enable aignet-eval-conjunction)))))

(def-fgl-primitive fgl-pathcond-fix (x)
  (stobj-let ((logicman (interp-st->logicman interp-st))
              (pathcond (interp-st->pathcond interp-st)))
             (ans pathcond logicman)
             (lbfr-case
               :aignet (b* ((pathcond (mbe :logic (pathcond-fix pathcond) :exec pathcond))
                            ((unless (pathcond-enabledp pathcond))
                             (mv (fgl-object-fix x) pathcond logicman))
                            (cube (pathcond-to-cube pathcond nil))
                            ;; (lits (bfrs->aignet-lits cube (logicman->bfrstate)))
                            ((acl2::local-stobjs aignet::mark aignet::copy)
                             (mv ans pathcond logicman aignet::mark aignet::copy)))
                         (stobj-let ((aignet (logicman->aignet logicman)))
                                    (aignet::mark aignet::copy)
                                    (aignet::aignet-self-constprop-prep cube aignet aignet::mark aignet::copy)
                                    (b* (((mv ans aignet::mark aignet::copy logicman)
                                          (fgl-object-pathcond-fix-aignet-impl
                                           x aignet::mark aignet::copy logicman)))
                                      (mv ans pathcond logicman aignet::mark aignet::copy))))
               :otherwise (b* (((mv ans pathcond) (fgl-object-pathcond-fix-impl x pathcond logicman)))
                            (mv ans pathcond logicman)))
             (mv ans interp-st))
  :returns (mv ans interp-st)
  :formula-check fgl-pathcond-fix-formula-checks)

               
  
