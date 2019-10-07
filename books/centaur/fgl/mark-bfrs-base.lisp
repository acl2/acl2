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

(include-book "bfr")
(include-book "centaur/aignet/arrays" :dir :system)
(include-book "std/stobjs/clone" :dir :system)
(include-book "std/stobjs/updater-independence" :dir :system)
;; (include-book "stack-logic")
;; (include-book "bvar-db-equivs")

(local (std::add-default-post-define-hook :fix))
(defstobj-clone bitarr aignet::bitarr :pkg fgl-fgl)
(defstobj-clone litarr aignet::litarr :pkg fgl-fgl)
;; NOTE: In order for transforms to be efficient we are going to need to
;; hons-copy all of the symbolic objects.  Otherwise there will most likely be
;; too much repetition.  Therefore, we'll memoize and avoid retraversals of
;; fgl-objects using fast alists.  This will avoid the overhead of memoizing
;; functions that take stobjs.

(define bfr-markedp (x bitarr)
  :guard (and (< 0 (bits-length bitarr))
              (bfr-p x (bfrstate (bfrmode :aignet) (1- (bits-length bitarr)))))
  :guard-hints (("goal" :in-theory (enable bfr-p)))
  (b* (((when (mbe :logic (or (eq x t) (eq x nil) (eql x 0))
                   :exec (or (eq x t) (eq x nil))))
        t))
    (equal 1 (get-bit (satlink::lit->var x) bitarr)))
  ///
  (defthm bfr-markedp-of-consts
    (and (bfr-markedp t bitarr)
         (bfr-markedp nil bitarr)
         (bfr-markedp 0 bitarr))))

(define bfr-mark (x bitarr)
  :prepwork ((local (in-theory (enable bfr-p)))
             (local (defthm lit->var-when-not-0-or-1
                      (implies (and (satlink::litp bfr)
                                    (not (equal bfr 0))
                                    (not (equal bfr 1)))
                               (not (equal (satlink::lit->var bfr) 0)))
                      :hints(("Goal" :use ((:instance satlink::equal-of-make-lit
                                            (var 0)
                                            (neg 0)
                                            (a bfr))
                                           (:instance satlink::equal-of-make-lit
                                            (var 0)
                                            (neg 1)
                                            (a bfr))))))))
  :guard (and (< 0 (bits-length bitarr))
              (bfr-p x (bfrstate (bfrmode :aignet) (1- (bits-length bitarr)))))
  :returns (new-bitarr)
  (b* (((when (or (eq x t) (eq x nil))) bitarr))
    (set-bit (satlink::lit->var x) 1 bitarr))
  ///
  (defret length-of-<fn>
    (implies (bfr-p x (bfrstate (bfrmode :aignet) (1- (len bitarr))))
             (equal (len new-bitarr)
                    (len bitarr))))

  (defret length-of-<fn>-incr
    (<= (len bitarr) (len new-bitarr))
    :rule-classes :linear)

  (defret bfr-markedp-preserved-of-<fn>
    (implies (bfr-markedp y bitarr)
             (bfr-markedp y new-bitarr))
    :hints(("Goal" :in-theory (enable bfr-markedp))))

  (defret bfr-markedp-of-<fn>
    (bfr-markedp x new-bitarr)
    :hints(("Goal" :in-theory (enable bfr-markedp)))))

(local (defthm bfr-p-of-increase-bound
         (implies (and (bfr-p x (bfrstate (bfrmode :aignet) bound1))
                       (<= (nfix bound1) (nfix bound)))
                  (bfr-p x (bfrstate (bfrmode :aignet) bound)))
         :hints(("Goal" :in-theory (enable bfr-p)))))

(define bfrlist-mark (x bitarr)
  :guard (and (< 0 (bits-length bitarr))
              (bfr-listp x (bfrstate (bfrmode :aignet) (1- (bits-length bitarr)))))
  :returns (new-bitarr)
  (b* (((when (atom x)) bitarr)
       (bitarr (bfr-mark (car x) bitarr)))
    (bfrlist-mark (cdr x) bitarr))
  ///
  (defret length-of-<fn>
    (implies (bfr-listp x (bfrstate (bfrmode :aignet) (1- (len bitarr))))
             (equal (len new-bitarr)
                    (len bitarr))))

  (defret length-of-<fn>-incr
    (<= (len bitarr) (len new-bitarr))
    :rule-classes :linear)

  (defret bfr-markedp-preserved-of-<fn>
    (implies (bfr-markedp y bitarr)
             (bfr-markedp y new-bitarr)))

  (defret bfr-markedp-of-<fn>
    (implies (member k x)
             (bfr-markedp k new-bitarr))))


(local (defthm fgl-objectlist-p-of-append
         (implies (and (fgl-objectlist-p x)
                       (fgl-objectlist-p y))
                  (fgl-objectlist-p (append x y)))))

(defines fgl-object-subobjects
  :ruler-extenders :all
  (define fgl-object-subobjects ((x fgl-object-p))
    :measure (acl2::two-nats-measure (fgl-object-count x) 0)
    :returns (subobjs fgl-objectlist-p)
    (cons (fgl-object-fix x)
          (fgl-object-case x
            :g-ite (append (fgl-object-subobjects x.test)
                           (fgl-object-subobjects x.then)
                           (fgl-object-subobjects x.else))
            :g-apply (fgl-objectlist-subobjects x.args)
            :g-map (fgl-object-alist-subobjects x.alist)
            :g-cons (append (fgl-object-subobjects x.car)
                            (fgl-object-subobjects x.cdr))
            :otherwise nil)))
  (define fgl-objectlist-subobjects ((x fgl-objectlist-p))
    :measure (acl2::two-nats-measure (fgl-objectlist-count x) 0)
    :returns (subobjs fgl-objectlist-p)
    (and (consp x)
         (append (fgl-object-subobjects (car x))
                 (fgl-objectlist-subobjects (cdr x)))))
  (define fgl-object-alist-subobjects ((x fgl-object-alist-p))
    :measure (acl2::two-nats-measure (fgl-object-alist-count x) (len x))
    :returns (subobjs fgl-objectlist-p)
    (and (consp x)
         (append (and (mbt (consp (car x)))
                      (fgl-object-subobjects (cdar x)))
                 (fgl-object-alist-subobjects (cdr x)))))
  ///
  (fty::deffixequiv-mutual fgl-object-subobjects
    :hints(("Goal" :in-theory (enable fgl-object-alist-fix))))


  (defret-mutual <fn>-transitive
    (defret <fn>-transitive
      (implies (and (member y subobjs)
                    (member z (fgl-object-subobjects y)))
               (member z subobjs))
      :hints ('(:expand (<call>))
              (and stable-under-simplificationp
                   '(:expand ((:free (y) <call>)))))
      :fn fgl-object-subobjects)
    (defret <fn>-transitive
      (implies (and (member y subobjs)
                    (member z (fgl-object-subobjects y)))
               (member z subobjs))
      :hints ('(:expand ((:free (y) <call>))))
      :fn fgl-objectlist-subobjects)
    (defret <fn>-transitive
      (implies (and (member y subobjs)
                    (member z (fgl-object-subobjects y)))
               (member z subobjs))
      :hints ('(:expand ((:free (y) <call>))))
      :fn fgl-object-alist-subobjects))

  (defret-mutual bfr-member-of-<fn>
    (defret bfr-member-of-<fn>
      (implies (and (member k (fgl-object-bfrlist y))
                    (not (member k (fgl-object-bfrlist x))))
               (not (member y subobjs)))
      :hints ('(:expand (<call>
                         (fgl-object-bfrlist x))))
      :fn fgl-object-subobjects)
    (defret bfr-member-of-<fn>
      (implies (and (member k (fgl-object-bfrlist y))
                    (not (member k (fgl-objectlist-bfrlist x))))
               (not (member y subobjs)))
      :hints ('(:expand (<call>
                         (fgl-objectlist-bfrlist x))))
      :fn fgl-objectlist-subobjects)
    (defret bfr-member-of-<fn>
      (implies (and (member k (fgl-object-bfrlist y))
                    (not (member k (fgl-object-alist-bfrlist x))))
               (not (member y subobjs)))
      :hints ('(:expand (<call>
                         (fgl-object-alist-bfrlist x))))
      :fn fgl-object-alist-subobjects))

  (defret-mutual not-<fn>-when-count-less
    (defret not-<fn>-when-count-less
      (implies (< (fgl-object-count x) (fgl-object-count y))
               (not (member y subobjs)))
      :hints ('(:expand (<call>)))
      :fn fgl-object-subobjects)
    (defret not-<fn>-when-count-less
      (implies (< (fgl-objectlist-count x) (fgl-object-count y))
               (not (member y subobjs)))
      :hints ('(:expand (<call>)))
      :fn fgl-objectlist-subobjects)
    (defret not-<fn>-when-count-less
      (implies (< (fgl-object-alist-count x) (fgl-object-count y))
               (not (member y subobjs)))
      :hints ('(:expand (<call>)))
      :fn fgl-object-alist-subobjects))

  (defthm fgl-object-subobjects-self
    (implies (fgl-object-p x)
             (member x (fgl-object-subobjects x)))
    :hints (("goal" :expand ((fgl-object-subobjects x)))))

  (defthm fgl-object-subobjects-self-fix
    (member (fgl-object-fix x) (fgl-object-subobjects x))
    :hints (("goal" :expand ((fgl-object-subobjects x)))))


  (defret <fn>-when-g-ite
    (implies (fgl-object-case x :g-ite)
             (equal subobjs
                    (b* (((g-ite x)))
                      (cons (fgl-object-fix x)
                            (append (fgl-object-subobjects x.test)
                                    (fgl-object-subobjects x.then)
                                    (fgl-object-subobjects x.else))))))
    :fn fgl-object-subobjects)

  (defret <fn>-when-g-apply
    (implies (fgl-object-case x :g-apply)
             (equal subobjs
                    (b* (((g-apply x)))
                      (cons (fgl-object-fix x)
                            (fgl-objectlist-subobjects x.args)))))
    :fn fgl-object-subobjects)

  (defret <fn>-when-g-map
    (implies (fgl-object-case x :g-map)
             (equal subobjs
                    (b* (((g-map x)))
                      (cons (fgl-object-fix x)
                            (fgl-object-alist-subobjects x.alist)))))
    :fn fgl-object-subobjects)

  (defret <fn>-when-g-cons
    (implies (fgl-object-case x :g-cons)
             (equal subobjs
                    (b* (((g-cons x)))
                      (cons (fgl-object-fix x)
                            (append (fgl-object-subobjects x.car)
                                    (fgl-object-subobjects x.cdr))))))
    :fn fgl-object-subobjects)

  (defret <fn>-when-atomic-1
    (implies (fgl-object-case x '(:g-concrete :g-boolean :g-var))
             (equal subobjs
                    (list (fgl-object-fix x))))
    :fn fgl-object-subobjects)

  (defret <fn>-when-atomic-2
    (implies (fgl-object-case x :g-integer)
             (equal subobjs
                    (list (fgl-object-fix x))))
    :fn fgl-object-subobjects)

  (defret <fn>-when-consp
    (implies (consp x)
             (equal subobjs
                    (append (fgl-object-subobjects (car x))
                            (fgl-objectlist-subobjects (cdr x)))))
    :fn fgl-objectlist-subobjects)

  (defret <fn>-when-atom
    (implies (not (consp x))
             (equal subobjs nil))
    :fn fgl-objectlist-subobjects)

  (defret <fn>-when-consp-car
    (implies (consp (car x))
             (equal subobjs
                    (append (fgl-object-subobjects (cdar x))
                            (fgl-object-alist-subobjects (cdr x)))))
    :fn fgl-object-alist-subobjects)

  (defret <fn>-when-not-consp-car
    (implies (and (consp x)
                  (not (consp (car x))))
             (equal subobjs
                    (fgl-object-alist-subobjects (cdr x))))
    :fn fgl-object-alist-subobjects)

  (defret <fn>-when-atom
    (implies (not (consp x))
             (equal subobjs nil))
    :fn fgl-object-alist-subobjects))


(define fgl-object-top-bfrlist1 ((x fgl-object-p))
  :returns (bfrs)
  (fgl-object-case x
    :g-boolean (list x.bool)
    :otherwise nil)
  ///
  (defret member-bfrlist-when-<fn>
    (implies (not (member bfr (fgl-object-bfrlist x)))
             (not (member bfr bfrs)))
    :hints(("Goal" :expand ((fgl-object-bfrlist x))))))



(define fgl-objectlist-top-bfrlist1 ((x fgl-objectlist-p))
  :returns (bfrs)
  (if (atom x)
      nil
    (append (fgl-object-top-bfrlist1 (car x))
            (fgl-objectlist-top-bfrlist1 (cdr x))))
  ///
  (defret member-bfrlist-when-<fn>
    (implies (not (member bfr (fgl-objectlist-bfrlist x)))
             (not (member bfr bfrs)))
    :hints(("Goal" :induct <call>
            :expand ((fgl-objectlist-bfrlist x))))))

(define fgl-object-alist-top-bfrlist1 ((x fgl-object-alist-p))
  :hooks ((:fix :hints (("goal" :in-theory (enable fgl-object-alist-fix)))))
  :returns (bfrs)
  (if (atom x)
      nil
    (append (and (mbt (consp (car x)))
                 (fgl-object-top-bfrlist1 (cdar x)))
            (fgl-object-alist-top-bfrlist1 (cdr x))))
  ///
  (defret member-bfrlist-when-<fn>
    (implies (not (member bfr (fgl-object-alist-bfrlist x)))
             (not (member bfr bfrs)))
    :hints(("Goal" :induct <call>
            :expand ((fgl-object-alist-bfrlist x))))))

(define fgl-object-top-bfrlist ((x fgl-object-p))
  :returns (bfrs)
  (fgl-object-case x
    :g-boolean (list x.bool)
    :g-integer x.bits
    :g-ite (append (fgl-object-top-bfrlist1 x.test)
                   (fgl-object-top-bfrlist1 x.then)
                   (fgl-object-top-bfrlist1 x.else))
    :g-apply (fgl-objectlist-top-bfrlist1 x.args)
    :g-map (fgl-object-alist-top-bfrlist1 x.alist)
    :g-cons (append (fgl-object-top-bfrlist1 x.car)
                    (fgl-object-top-bfrlist1 x.cdr))
    :otherwise nil)
  ///
  (defret member-bfrlist-when-<fn>
    (implies (not (member bfr (fgl-object-bfrlist x)))
             (not (member bfr bfrs)))
    :hints(("Goal" 
            :expand ((fgl-object-bfrlist x))))))



(define fgl-objectlist-subobj-containing-top-bfr ((x fgl-objectlist-p)
                                                 bfr)
  :returns (subobj fgl-object-p)
  (if (atom x)
      nil
    (if (member-equal bfr (fgl-object-top-bfrlist1 (car x)))
        (fgl-object-fix (car x))
      (fgl-objectlist-subobj-containing-top-bfr (cdr x) bfr)))
  ///
  (defret <fn>-finds-subobj
    (implies (member bfr (fgl-objectlist-top-bfrlist1 x))
             (and (member bfr (fgl-object-top-bfrlist1 subobj))
                  (member subobj (fgl-objectlist-subobjects x))))
    :hints (("goal" :induct t :expand ((fgl-objectlist-top-bfrlist1 x)
                                       (fgl-objectlist-subobjects x))))))

(define fgl-object-alist-subobj-containing-top-bfr ((x fgl-object-alist-p)
                                                   bfr)
  :hooks ((:fix :hints (("goal" :in-theory (enable fgl-object-alist-fix)))))
  :returns (subobj fgl-object-p)
  (if (atom x)
      nil
    (if (and (mbt (consp (car x)))
             (member-equal bfr (fgl-object-top-bfrlist1 (cdar x))))
        (fgl-object-fix (cdar x))
      (fgl-object-alist-subobj-containing-top-bfr (cdr x) bfr)))
  ///
  (defret <fn>-finds-subobj
    (implies (member bfr (fgl-object-alist-top-bfrlist1 x))
             (and (member bfr (fgl-object-top-bfrlist1 subobj))
                  (member subobj (fgl-object-alist-subobjects x))))
    :hints (("goal" :induct t :expand ((fgl-object-alist-top-bfrlist1 x)
                                       (fgl-object-alist-subobjects x))))))

(define fgl-object-subobj-containing-top-bfr ((x fgl-object-p)
                                             bfr)
  :returns (subobj fgl-object-p)
  (fgl-object-case x
    :g-ite (cond ((member-equal bfr (fgl-object-top-bfrlist1 x.test)) x.test)
                 ((member-equal bfr (fgl-object-top-bfrlist1 x.then)) x.then)
                 ((member-equal bfr (fgl-object-top-bfrlist1 x.else)) x.else))
    :g-apply (fgl-objectlist-subobj-containing-top-bfr x.args bfr)
    :g-map (fgl-object-alist-subobj-containing-top-bfr x.alist bfr)
    :g-cons (cond ((member-equal bfr (fgl-object-top-bfrlist1 x.car)) x.car)
                  ((member-equal bfr (fgl-object-top-bfrlist1 x.cdr)) x.cdr))
    :otherwise nil)
  ///
  (local (defthm not-equal-fgl-objects-when-count-less
           (implies (< (fgl-object-count x) (fgl-object-count y))
                    (not (equal x y)))))

  (local (in-theory (enable acl2::member-of-cons)))

  (defret <fn>-finds-subobj
    (implies (and (member bfr (fgl-object-top-bfrlist x))
                  (not (fgl-object-case x '(:g-var :g-concrete :g-boolean :g-integer))))
             (and (member bfr (fgl-object-top-bfrlist1 subobj))
                  (member subobj (fgl-object-subobjects x))
                  (not (equal subobj x))
                  (not (equal subobj (fgl-object-fix x)))))
    :hints (("goal" :expand ((fgl-object-top-bfrlist x)
                             (fgl-object-subobjects x)))
            (and stable-under-simplificationp
                 '(:use ((:instance fgl-object-alist-subobj-containing-top-bfr-finds-subobj
                          (x (g-map->alist x)))
                         (:instance fgl-objectlist-subobj-containing-top-bfr-finds-subobj
                          (x (g-apply->args x))))
                   :expand ((fgl-object-count x))
                   :in-theory (disable fgl-object-alist-subobj-containing-top-bfr-finds-subobj
                                       fgl-objectlist-subobj-containing-top-bfr-finds-subobj)
                   :do-not '(generalize fertilize eliminate-destructors))))))



(defines fgl-object-subobj-containing-bfr-at-top
  (define fgl-object-subobj-containing-bfr-at-top ((x fgl-object-p) bfr)
    :measure (two-nats-measure (fgl-object-count x) 0)
    :returns (subobj fgl-object-p)
    (if (member-equal bfr (fgl-object-top-bfrlist x))
        (fgl-object-fix x)
      (fgl-object-case x
        :g-ite (cond ((member-equal bfr (fgl-object-bfrlist x.test))
                      (fgl-object-subobj-containing-bfr-at-top x.test bfr))
                     ((member-equal bfr (fgl-object-bfrlist x.then))
                      (fgl-object-subobj-containing-bfr-at-top x.then bfr))
                     ((member-equal bfr (fgl-object-bfrlist x.else))
                      (fgl-object-subobj-containing-bfr-at-top x.else bfr)))
        :g-cons (cond ((member-equal bfr (fgl-object-bfrlist x.car))
                       (fgl-object-subobj-containing-bfr-at-top x.car bfr))
                      ((member-equal bfr (fgl-object-bfrlist x.cdr))
                       (fgl-object-subobj-containing-bfr-at-top x.cdr bfr)))
        :g-apply (fgl-objectlist-subobj-containing-bfr-at-top x.args bfr)
        :g-map (fgl-object-alist-subobj-containing-bfr-at-top x.alist bfr)
        :otherwise nil)))
  (define fgl-objectlist-subobj-containing-bfr-at-top ((x fgl-objectlist-p) bfr)
    :measure (two-nats-measure (fgl-objectlist-count x) 0)
    :returns (subobj fgl-object-p)
    (if (atom x)
        nil
      (if (member-equal bfr (fgl-object-bfrlist (car x)))
          (fgl-object-subobj-containing-bfr-at-top (car x) bfr)
        (fgl-objectlist-subobj-containing-bfr-at-top (cdr x) bfr))))
  (define fgl-object-alist-subobj-containing-bfr-at-top ((x fgl-object-alist-p) bfr)
    :measure (two-nats-measure (fgl-object-alist-count x) (len x))
    :returns (subobj fgl-object-p)
    (if (atom x)
        nil
      (if (and (mbt (consp (car x)))
               (member-equal bfr (fgl-object-bfrlist (cdar x))))
          (fgl-object-subobj-containing-bfr-at-top (cdar x) bfr)
        (fgl-object-alist-subobj-containing-bfr-at-top (cdr x) bfr))))
  ///
  (defret-mutual <fn>-when-member-bfrs
    (defret <fn>-when-member-bfrs
      (implies (member bfr (fgl-object-bfrlist x))
               (and (member subobj (fgl-object-subobjects x))
                    (member bfr (fgl-object-top-bfrlist subobj))))
      :hints ('(:expand (<call>
                         (fgl-object-subobjects x)
                         (fgl-object-bfrlist x)))
              (and stable-under-simplificationp
                   '(:expand ((fgl-object-top-bfrlist x)))))
      :fn fgl-object-subobj-containing-bfr-at-top)
    (defret <fn>-when-member-bfrs
      (implies (member bfr (fgl-objectlist-bfrlist x))
               (and (member subobj (fgl-objectlist-subobjects x))
                    (member bfr (fgl-object-top-bfrlist subobj))))
      :hints ('(:expand (<call>
                         (fgl-objectlist-subobjects x)
                         (fgl-objectlist-bfrlist x))))
      :fn fgl-objectlist-subobj-containing-bfr-at-top)
    (defret <fn>-when-member-bfrs
      (implies (member bfr (fgl-object-alist-bfrlist x))
               (and (member subobj (fgl-object-alist-subobjects x))
                    (member bfr (fgl-object-top-bfrlist subobj))))
      :hints ('(:expand (<call>
                         (fgl-object-alist-subobjects x)
                         (fgl-object-alist-bfrlist x))))
      :fn fgl-object-alist-subobj-containing-bfr-at-top))

  (defret-mutual <fn>-not-var-type
    (defret <fn>-not-var-type
      (not (equal (fgl-object-kind subobj) :g-var))
      :hints ('(:expand (<call>))
              (and stable-under-simplificationp
                   '(:expand ((fgl-object-top-bfrlist x)))))
      :fn fgl-object-subobj-containing-bfr-at-top)
    (defret <fn>-not-var-type
      (not (equal (fgl-object-kind subobj) :g-var))
      :hints ('(:expand (<call>)))
      :fn fgl-objectlist-subobj-containing-bfr-at-top)
    (defret <fn>-not-var-type
      (not (equal (fgl-object-kind subobj) :g-var))
      :hints ('(:expand (<call>)))
      :fn fgl-object-alist-subobj-containing-bfr-at-top))

  (defret-mutual <fn>-not-concrete-type
    (defret <fn>-not-concrete-type
      (implies (member bfr (fgl-object-bfrlist x))
               (not (equal (fgl-object-kind subobj) :g-concrete)))
      :hints ('(:expand (<call>
                         (fgl-object-bfrlist x)))
              (and stable-under-simplificationp
                   '(:expand ((fgl-object-top-bfrlist x)))))
      :fn fgl-object-subobj-containing-bfr-at-top)
    (defret <fn>-not-concrete-type
      (implies (member bfr (fgl-objectlist-bfrlist x))
               (not (equal (fgl-object-kind subobj) :g-concrete)))
      :hints ('(:expand (<call>
                         (fgl-objectlist-bfrlist x))))
      :fn fgl-objectlist-subobj-containing-bfr-at-top)
    (defret <fn>-not-concrete-type
      (implies (member bfr (fgl-object-alist-bfrlist x))
               (not (equal (fgl-object-kind subobj) :g-concrete)))
      :hints ('(:expand (<call>
                         (fgl-object-alist-bfrlist x))))
      :fn fgl-object-alist-subobj-containing-bfr-at-top))

  (defret-mutual <fn>-not-boolean-type
    (defret <fn>-not-boolean-type
      (iff (equal (fgl-object-kind subobj) :g-boolean)
           (and (equal (fgl-object-kind x) :g-boolean)
                (equal bfr (g-boolean->bool x))
                (equal subobj (fgl-object-fix x))))
      :hints ('(:expand (<call>
                         (fgl-object-bfrlist x))
                :in-theory (enable acl2::member-of-cons))
              (and stable-under-simplificationp
                   '(:expand ((fgl-object-top-bfrlist x))
                     :in-theory (enable fgl-object-top-bfrlist1
                                        acl2::member-of-cons))))
      :fn fgl-object-subobj-containing-bfr-at-top)
    (defret <fn>-not-boolean-type
      (implies (not (member bfr (fgl-objectlist-top-bfrlist1 x)))
               (not (equal (fgl-object-kind subobj) :g-boolean)))
      :hints ('(:expand (<call>
                         (fgl-objectlist-top-bfrlist1 x))
                :in-theory (enable fgl-object-top-bfrlist1))
              (and stable-under-simplificationp
                   '(:expand ((fgl-object-bfrlist (car x))))))
      :fn fgl-objectlist-subobj-containing-bfr-at-top)
    (defret <fn>-not-boolean-type
      (implies (not (member bfr (fgl-object-alist-top-bfrlist1 x)))
               (not (equal (fgl-object-kind subobj) :g-boolean)))
      :hints ('(:expand (<call>
                         (fgl-object-alist-top-bfrlist1 x))
                :in-theory (enable fgl-object-top-bfrlist1))
              (and stable-under-simplificationp
                   '(:expand ((fgl-object-bfrlist (cdar x))))))
      :fn fgl-object-alist-subobj-containing-bfr-at-top)
    :skip-others t))
    

 


(defsection fgl-objectlist-closed-downwards
  (acl2::defquant fgl-objectlist-closed-downwards (x)
    (forall (y z)
            (implies (and (member (fgl-object-fix y) x)
                          ;; (fgl-object-p z)
                          (not (member z x)))
                     (not (member z (fgl-object-subobjects y)))))
    :rewrite :direct)

  (acl2::defexample fgl-objectlist-closed-downwards-example
    :pattern (member z (fgl-object-subobjects y))
    :templates (y z)
    :instance-rulename fgl-objectlist-closed-downwards-instancing)

  (defthm fgl-objectlist-closed-downwards-of-fgl-object-subobjects
    (fgl-objectlist-closed-downwards (fgl-object-subobjects x))
    :hints ((acl2::witness)))

  (defthm fgl-objectlist-closed-downwards-of-fgl-objectlist-subobjects
    (fgl-objectlist-closed-downwards (fgl-objectlist-subobjects x))
    :hints ((acl2::witness)))

  (defthm fgl-objectlist-closed-downwards-of-fgl-object-alist-subobjects
    (fgl-objectlist-closed-downwards (fgl-object-alist-subobjects x))
    :hints ((acl2::witness)))

  (defthm fgl-objectlist-closed-downwards-of-append
    (implies (and (fgl-objectlist-closed-downwards x)
                  (fgl-objectlist-closed-downwards y))
             (fgl-objectlist-closed-downwards (append x y)))
    :hints ((acl2::witness))))

(defsection bitarr-subsetp
  (acl2::defquant bitarr-subsetp (x y)
    (forall b
            (implies (bfr-markedp b x)
                     (bfr-markedp b y)))
    :rewrite :direct)

  (acl2::defexample bitarr-subsetp-example
    :pattern (bfr-markedp b x)
    :templates (b)
    :instance-rulename bitarr-subsetp-instancing)

  (defthm bitarr-subsetp-of-bfr-mark
    (bitarr-subsetp x (bfr-mark b x))
    :hints(("Goal" :in-theory (enable bitarr-subsetp))))

  (defthm bitarr-subsetp-trans
    (implies (and (bitarr-subsetp x y)
                  (bitarr-subsetp y z))
             (bitarr-subsetp x z))
    :hints ((acl2::witness)))

  (defthm bitarr-subsetp-of-bfrlist-mark
    (bitarr-subsetp x (bfrlist-mark b x))
    :hints(("Goal" :in-theory (enable bitarr-subsetp))))

  (defthm bitarr-subsetp-self
    (bitarr-subsetp x x)
    :hints(("Goal" :in-theory (enable bitarr-subsetp)))))

(defines fgl-object-mark-bfrs
  (define fgl-object-mark-bfrs ((x fgl-object-p)
                               bitarr
                               seen)
    :guard (and (< 0 (bits-length bitarr))
                (bfr-listp (fgl-object-bfrlist x) (bfrstate (bfrmode :aignet) (1- (bits-length bitarr)))))
    :verify-guards nil
    :measure (acl2::two-nats-measure (fgl-object-count x) 0)
    :returns (mv new-bitarr new-seen)
    (fgl-object-case x
      :g-concrete (mv bitarr seen)
      :g-var (mv bitarr seen)
      :g-boolean (b* ((bitarr (bfr-mark x.bool bitarr)))
                   (mv bitarr seen))
      :otherwise
      (b* ((x (fgl-object-fix x))
           ((when (hons-get x seen)) (mv bitarr seen))
           (seen (hons-acons x t seen)))
        (case acl2::x.kind
          (:g-integer (b* ((bitarr (bfrlist-mark (g-integer->bits x) bitarr)))
                        (mv bitarr seen)))
          (:g-ite (b* (((g-ite x))
                       ((mv bitarr seen) (fgl-object-mark-bfrs x.test bitarr seen))
                       ((mv bitarr seen) (fgl-object-mark-bfrs x.then bitarr seen)))
                    (fgl-object-mark-bfrs x.else bitarr seen)))
          (:g-apply (fgl-objectlist-mark-bfrs (g-apply->args x) bitarr seen))
          (:g-map (fgl-object-alist-mark-bfrs (g-map->alist x) bitarr seen))
          (otherwise (b* (((g-cons x))
                          ((mv bitarr seen) (fgl-object-mark-bfrs x.car bitarr seen)))
                       (fgl-object-mark-bfrs x.cdr bitarr seen)))))))

  (define fgl-objectlist-mark-bfrs ((x fgl-objectlist-p)
                                   bitarr
                                   seen)
    :guard (and (< 0 (bits-length bitarr))
                (bfr-listp (fgl-objectlist-bfrlist x)
                           (bfrstate (bfrmode :aignet) (1- (bits-length bitarr)))))
    :measure (acl2::two-nats-measure (fgl-objectlist-count x) 0)
    :returns (mv new-bitarr new-seen)
    (b* (((when (atom x))
          (mv bitarr seen))
         ((mv bitarr seen) (fgl-object-mark-bfrs (car x) bitarr seen)))
      (fgl-objectlist-mark-bfrs (cdr x) bitarr seen)))

  (define fgl-object-alist-mark-bfrs ((x fgl-object-alist-p)
                                     bitarr
                                     seen)
    :guard (and (< 0 (bits-length bitarr))
                (bfr-listp (fgl-object-alist-bfrlist x)
                           (bfrstate (bfrmode :aignet) (1- (bits-length bitarr)))))
    :measure (acl2::two-nats-measure (fgl-object-alist-count x) (len x))
    :returns (mv new-bitarr new-seen)
    (b* (((when (atom x)) (mv bitarr seen))
         ((unless (mbt (consp (car x))))
          (fgl-object-alist-mark-bfrs (cdr x) bitarr seen))
         ((mv bitarr seen) (fgl-object-mark-bfrs (cdar x) bitarr seen)))
      (fgl-object-alist-mark-bfrs (cdr x) bitarr seen)))
  ///

  ;; Basic properties...

  (defret-mutual length-of-<fn>
    (defret length-of-<fn>
      (implies (bfr-listp (fgl-object-bfrlist x) (bfrstate (bfrmode :aignet) (1- (len bitarr))))
               (equal (len new-bitarr) (len bitarr)))
      :hints ('(:expand (<call>
                         (fgl-object-bfrlist x))))
      :fn fgl-object-mark-bfrs)
    (defret length-of-<fn>
      (implies (bfr-listp (fgl-objectlist-bfrlist x) (bfrstate (bfrmode :aignet) (1- (len bitarr))))
               (equal (len new-bitarr) (len bitarr)))
      :hints ('(:expand (<call>
                         (fgl-objectlist-bfrlist x))))
      :fn fgl-objectlist-mark-bfrs)
    (defret length-of-<fn>
      (implies (bfr-listp (fgl-object-alist-bfrlist x) (bfrstate (bfrmode :aignet) (1- (len bitarr))))
               (equal (len new-bitarr) (len bitarr)))
      :hints ('(:expand (<call>
                         (fgl-object-alist-bfrlist x))))
      :fn fgl-object-alist-mark-bfrs))

  (verify-guards fgl-object-mark-bfrs
    :hints (("goal" :expand (fgl-object-bfrlist x))))

  (defret-mutual length-of-<fn>-incr
    (defret length-of-<fn>-incr
      (>= (len new-bitarr) (len bitarr))
      :hints ('(:expand (<call>)))
      :fn fgl-object-mark-bfrs
      :rule-classes :linear)
    (defret length-of-<fn>-incr
      (>= (len new-bitarr) (len bitarr))
      :hints ('(:expand (<call>)))
      :fn fgl-objectlist-mark-bfrs
      :rule-classes :linear)
    (defret length-of-<fn>-incr
      (>= (len new-bitarr) (len bitarr))
      :hints ('(:expand (<call>)))
      :fn fgl-object-alist-mark-bfrs
      :rule-classes :linear))

  

  (defret-mutual bfr-markedp-preserved-of-<fn>
    (defret bfr-markedp-preserved-of-<fn>
      (implies (bfr-markedp y bitarr)
               (bfr-markedp y new-bitarr))
      :hints ('(:expand (<call>)))
      :fn fgl-object-mark-bfrs)
    (defret bfr-markedp-preserved-of-<fn>
      (implies (bfr-markedp y bitarr)
               (bfr-markedp y new-bitarr))
      :hints ('(:expand (<call>)))
      :fn fgl-objectlist-mark-bfrs)
    (defret bfr-markedp-preserved-of-<fn>
      (implies (bfr-markedp y bitarr)
               (bfr-markedp y new-bitarr))
      :hints ('(:expand (<call>)))
      :fn fgl-object-alist-mark-bfrs))

  
  (defret-mutual bitarr-subsetp-of-<fn>
    (defret bitarr-subsetp-of-<fn>
      (bitarr-subsetp bitarr new-bitarr)
      :hints ('(:expand (<call>)))
      :fn fgl-object-mark-bfrs)
    (defret bitarr-subsetp-of-<fn>
      (bitarr-subsetp bitarr new-bitarr)
      :hints ('(:expand (<call>)))
      :fn fgl-objectlist-mark-bfrs)
    (defret bitarr-subsetp-of-<fn>
      (bitarr-subsetp bitarr new-bitarr)
      :hints ('(:expand (<call>)))
      :fn fgl-object-alist-mark-bfrs))

  ;; Two top-level invariants:
  ;; - fgl-object-mark-bfrs-bitarr-invar
  ;; - fgl-object-mark-bfrs-seen-invar

  ;; We'll prove a whole lot of local lemmas before we
  ;; prove that these top-level invariants are preserved by these functions and
  ;; also ensure that the bitarr will always contain the bfrs of x.



  (acl2::defquant fgl-object-mark-bfrs-bitarr-invar (seen bitarr)
    (forall (obj bfr)
            (implies (and (hons-assoc-equal (fgl-object-fix obj) seen)
                          (member bfr (fgl-object-bfrlist obj)))
                     (bfr-markedp bfr bitarr)))
    :rewrite :direct)

  (acl2::defquant fgl-object-mark-bfrs-seen-invar (seen)
    (forall (x y)
            (implies (and (hons-assoc-equal (fgl-object-fix x) seen)
                          (not (hons-assoc-equal (fgl-object-fix y) seen))
                          (not (fgl-object-case y '(:g-var :g-concrete :g-boolean))))
                     (not (member y (fgl-object-subobjects x)))))
    :rewrite :direct)

  (acl2::defquant bfrs-markedp (immed-bfrs bitarr)
    (forall bfr
            (implies (member bfr immed-bfrs)
                     (bfr-markedp bfr bitarr)))
    :rewrite :direct)


  (defund fgl-object-mark-bfrs-invar (seen bitarr)
    (and (fgl-object-mark-bfrs-seen-invar seen)
         (fgl-object-mark-bfrs-bitarr-invar seen bitarr)))
  


  (local
   (progn

     (acl2::defquant fgl-object-mark-bfrs-local-invar (subobjs seen)
       (forall (y z)
               (implies (and (member (fgl-object-fix y) subobjs)
                             (hons-assoc-equal (fgl-object-fix y) seen)
                             (not (hons-assoc-equal (fgl-object-fix z) seen))
                             (not (fgl-object-case z '(:g-var :g-concrete :g-boolean))))
                        (not (member z (fgl-object-subobjects y)))))
       :rewrite :direct)

     (acl2::defexample fgl-object-mark-bfrs-local-invar-example
       :pattern (member z (fgl-object-subobjects y))
       :templates (y z)
       :instance-rulename fgl-object-mark-bfrs-local-invar-instancing)

     (acl2::def-witness-ruleset mark-bfrs-witness-rules
       '(fgl-object-mark-bfrs-local-invar-instancing
         fgl-object-mark-bfrs-local-invar-example
         fgl-object-mark-bfrs-local-invar-witnessing))

     (defthm fgl-object-mark-bfrs-local-invar-of-append
       (iff (fgl-object-mark-bfrs-local-invar (append x y) seen)
            (and (fgl-object-mark-bfrs-local-invar x seen)
                 (fgl-object-mark-bfrs-local-invar y seen)))
       :hints ((acl2::witness :ruleset mark-bfrs-witness-rules)))

     (defthm fgl-object-mark-bfrs-local-invar-no-subobjs
       (fgl-object-mark-bfrs-local-invar nil seen)
       :hints ((acl2::witness :ruleset mark-bfrs-witness-rules)))

     (defthmd fgl-object-fix-when-equal-fgl-object-fix
       (implies (equal a (fgl-object-fix b))
                (equal (fgl-object-fix a) a)))

     (defthm fgl-object-mark-bfrs-local-invar-of-cons
       (implies (syntaxp (not (equal b ''nil)))
                (iff (fgl-object-mark-bfrs-local-invar (cons a b) seen)
                     (and (fgl-object-mark-bfrs-local-invar (list a) seen)
                          (fgl-object-mark-bfrs-local-invar b seen))))
       :hints (("goal" :in-theory (enable fgl-object-fix-when-equal-fgl-object-fix))
               (acl2::witness :ruleset mark-bfrs-witness-rules)))

     (in-theory (disable acl2::member-of-cons
                         member-equal
                         acl2::commutativity-of-append-under-set-equiv
                         acl2::commutativity-2-of-append-under-set-equiv))


     (defthm fgl-object-mark-bfrs-local-invar-of-nil
       (fgl-object-mark-bfrs-local-invar x nil)
       :hints ((acl2::witness)))

     (acl2::defquant fgl-object-mark-bfrs-seen-contents (new-seen seen subobjs)
       (forall y
               (implies (fgl-object-p y)
                        (iff (hons-assoc-equal y new-seen)
                             (or (and (member y subobjs)
                                      (not (fgl-object-case y '(:g-var :g-concrete :g-boolean))))
                                 (hons-assoc-equal y seen)))))
       :rewrite :direct)

     (acl2::defexample fgl-object-mark-bfrs-seen-contents-example
       :pattern (hons-assoc-equal y new-seen)
       :templates (y)
       :instance-rulename fgl-object-mark-bfrs-seen-contents-instancing)


     (acl2::def-witness-ruleset mark-bfrs-witness-rules2
       '(fgl-object-mark-bfrs-seen-contents-witnessing
         fgl-object-mark-bfrs-seen-contents-instancing
         fgl-object-mark-bfrs-seen-contents-example
         fgl-objectlist-mark-bfrs-seen-contents-witnessing
         mark-bfrs-witness-rules))

     (in-theory (disable not
                         (:t hons-assoc-equal)))


     (defcong set-equiv equal (fgl-object-mark-bfrs-seen-contents new-seen seen subobjs) 3
       :hints ((acl2::witness :ruleset mark-bfrs-witness-rules2)))


     (defthmd member-fgl-objectlist-p-when-not-fgl-object-p
       (implies (and (not (fgl-object-p y))
                     (fgl-objectlist-p x))
                (not (member y x)))
       :hints(("Goal" :in-theory (enable fgl-objectlist-p member))))

     (defthm fgl-object-mark-bfrs-seen-contents-implies-invar
       (implies (and (fgl-object-mark-bfrs-seen-contents new-seen seen subobjs)
                     (fgl-objectlist-closed-downwards subobjs)
                     (fgl-object-mark-bfrs-local-invar y seen))
                (fgl-object-mark-bfrs-local-invar y new-seen))
       :hints ((acl2::witness)
               (and stable-under-simplificationp
                    '(:cases ((fgl-object-p acl2::z0))
                      :in-theory (enable member-fgl-objectlist-p-when-not-fgl-object-p)))))

     (defthm fgl-object-mark-bfrs-seen-contents-self
       (fgl-object-mark-bfrs-seen-contents seen seen nil)
       :hints(("Goal" :in-theory (enable fgl-object-mark-bfrs-seen-contents))))

     (defthm fgl-object-mark-bfrs-seen-contents-of-append
       (implies (and (fgl-object-mark-bfrs-seen-contents new-seen1 seen a)
                     (fgl-object-mark-bfrs-seen-contents new-seen new-seen1 b))
                (fgl-object-mark-bfrs-seen-contents new-seen seen (append a b)))
       :hints ((acl2::witness)))

     (defthm fgl-object-mark-bfrs-local-invar-of-cons-non-member
       (implies (and (fgl-object-mark-bfrs-local-invar subobjs seen)
                     (not (member z subobjs)))
                (fgl-object-mark-bfrs-local-invar subobjs (cons (cons z val) seen)))
       :hints ((acl2::witness)))

     (defthmd member-when-equal-cons
       (implies (and (equal x (cons a b)))
                (iff (member y x)
                     (or (equal y a)
                         (member y b))))
       :hints(("Goal" :in-theory (enable member))))
     
     (defthm fgl-object-mark-bfrs-seen-contents-of-cons
       (implies (and (not (fgl-object-case x '(:g-var :g-concrete :g-boolean)))
                     (fgl-object-mark-bfrs-seen-contents new-seen (cons (cons x t) seen) rest)
                     (equal (cons x rest) (fgl-object-subobjects x)))
                (fgl-object-mark-bfrs-seen-contents new-seen seen (cons x rest)))
       :hints ((acl2::witness)
               (and stable-under-simplificationp
                    '(:in-theory (enable member-when-equal-cons
                                         ;; member
                                         )))))

     (defthm fgl-object-mark-bfrs-seen-contents-of-already-seen
       (implies (and (hons-assoc-equal (fgl-object-fix x) seen)
                     (fgl-object-mark-bfrs-local-invar (fgl-object-subobjects x) seen))
                (fgl-object-mark-bfrs-seen-contents seen seen (fgl-object-subobjects x)))
       :hints ((acl2::witness)))
     
     (defthm fgl-object-mark-bfrs-seen-contents-of-atomic
       (implies (and (fgl-object-case x '(:g-var :g-concrete :g-boolean))
                     ;; (fgl-object-p x)
                     )
                (fgl-object-mark-bfrs-seen-contents seen seen (list x)))
       :hints ((acl2::witness)
               (and stable-under-simplificationp
                    '(:in-theory (enable member)))))


     (defret-mutual <fn>-new-seenlist-contents
       (defret <fn>-new-seenlist-contents
         (b* ((subobjs (fgl-object-subobjects x)))
           (implies (fgl-object-mark-bfrs-local-invar subobjs seen)
                    (and (fgl-object-mark-bfrs-seen-contents new-seen seen subobjs))))
         :hints ('(:expand (<call>)))
         :fn fgl-object-mark-bfrs)
       (defret <fn>-new-seenlist-contents
         (b* ((subobjs (fgl-objectlist-subobjects x)))
           (implies (fgl-object-mark-bfrs-local-invar subobjs seen)
                    (and (fgl-object-mark-bfrs-seen-contents new-seen seen subobjs))))
         :hints ('(:expand (<call>)))
         :fn fgl-objectlist-mark-bfrs)
       (defret <fn>-new-seenlist-contents
         (b* ((subobjs (fgl-object-alist-subobjects x)))
           (implies (fgl-object-mark-bfrs-local-invar subobjs seen)
                    (and (fgl-object-mark-bfrs-seen-contents new-seen seen subobjs))))
         :hints ('(:expand (<call>)))
         :fn fgl-object-alist-mark-bfrs))

     (defret <fn>-preserves-mark-bfrs-invar
       (implies (and (fgl-object-mark-bfrs-local-invar (fgl-object-subobjects x) seen)
                     (fgl-object-mark-bfrs-local-invar y seen))
                (fgl-object-mark-bfrs-local-invar y new-seen))
       :hints (("goal" :use fgl-object-mark-bfrs-new-seenlist-contents
                :in-theory (disable fgl-object-mark-bfrs-new-seenlist-contents)))
       :fn fgl-object-mark-bfrs)

     (defret <fn>-preserves-mark-bfrs-invar
       (implies (and (fgl-object-mark-bfrs-local-invar (fgl-objectlist-subobjects x) seen)
                     (fgl-object-mark-bfrs-local-invar y seen))
                (fgl-object-mark-bfrs-local-invar y new-seen))
       :hints (("goal" :use fgl-objectlist-mark-bfrs-new-seenlist-contents
                :in-theory (disable fgl-objectlist-mark-bfrs-new-seenlist-contents)))
       :fn fgl-objectlist-mark-bfrs)

     (defret <fn>-preserves-mark-bfrs-invar
       (implies (and (fgl-object-mark-bfrs-local-invar (fgl-object-alist-subobjects x) seen)
                     (fgl-object-mark-bfrs-local-invar y seen))
                (fgl-object-mark-bfrs-local-invar y new-seen))
       :hints (("goal" :use fgl-object-alist-mark-bfrs-new-seenlist-contents
                :in-theory (disable fgl-object-alist-mark-bfrs-new-seenlist-contents)))
       :fn fgl-object-alist-mark-bfrs)


     
     

     ;; Z must be set in bitarr if some subobj not in seen has z as an immediate bfr.
     (acl2::defquant fgl-object-mark-bfrs-bitarr-contents (subobjs seen bitarr)
       (forall (y z)
               (implies (and (member (fgl-object-fix y) subobjs)
                             (not (hons-assoc-equal (fgl-object-fix y) seen))
                             (not (fgl-object-case y '(:g-var :g-concrete :g-boolean)))
                             (member z (fgl-object-top-bfrlist y)))
                        (bfr-markedp z bitarr)))
       :rewrite :direct)


     (acl2::defexample fgl-object-mark-bfrs-bitarr-contents-example
       :pattern (member z (fgl-object-top-bfrlist y))
       :templates (y z)
       :instance-rulename fgl-object-mark-bfrs-bitarr-contents-instancing)

     (defthm fgl-object-mark-bfrs-bitarr-contents-of-nil
       (fgl-object-mark-bfrs-bitarr-contents nil seen bitarr)
       :hints(("Goal" :in-theory (enable fgl-object-mark-bfrs-bitarr-contents))))

     (defthm fgl-object-mark-bfrs-bitarr-contents-of-append
       (iff (fgl-object-mark-bfrs-bitarr-contents (append x y) seen bitarr)
            (and (fgl-object-mark-bfrs-bitarr-contents x seen bitarr)
                 (fgl-object-mark-bfrs-bitarr-contents y seen bitarr)))
       :hints ((acl2::witness)))

     (defthm fgl-object-mark-bfrs-bitarr-contents-when-seen
       (implies (and (hons-assoc-equal (fgl-object-fix x) seen)
                     (fgl-object-mark-bfrs-local-invar (fgl-object-subobjects x) seen))
                (fgl-object-mark-bfrs-bitarr-contents (fgl-object-subobjects x) seen bitarr))
       :hints ((acl2::witness)))

     (defthm fgl-object-mark-bfrs-bitarr-contents-g-boolean
       (implies (fgl-object-case x :g-boolean)
                (fgl-object-mark-bfrs-bitarr-contents (list (fgl-object-fix x)) seen
                                                     (bfr-mark (g-boolean->bool x) bitarr)))
       :hints (("goal" :in-theory (enable acl2::member-of-cons))
               (acl2::witness)))

     (defthm fgl-object-mark-bfrs-bitarr-contents-atomic
       (implies (fgl-object-case x '(:g-var :g-concrete))
                (fgl-object-mark-bfrs-bitarr-contents (list (fgl-object-fix x)) seen bitarr))
       :hints (("goal" :in-theory (enable acl2::member-of-cons))
               (acl2::witness)))

     ;; (defthm fgl-object-mark-bfrs-bitarr-contents-of-cons
     ;;   (implies (syntaxp (not (equal y ''nil)))
     ;;            (iff (fgl-object-mark-bfrs-bitarr-contents (cons x y) seen bitarr)
     ;;                 (and (fgl-object-mark-bfrs-bitarr-contents (list x) seen bitarr)
     ;;                      (fgl-object-mark-bfrs-bitarr-contents y seen bitarr))))
     ;;   :hints ((acl2::witness)
     ;;           (and stable-under-simplificationp
     ;;                '(:in-theory (enable member)))))

     (def-updater-independence-thm fgl-object-mark-bfrs-bitarr-contents-when-bitarr-subsetp
       (implies (and (fgl-object-mark-bfrs-bitarr-contents x seen old)
                     (bitarr-subsetp old new))
                (fgl-object-mark-bfrs-bitarr-contents x seen new))
       :hints ((acl2::witness)))

     (def-updater-independence-thm fgl-object-mark-bfrs-bitarr-contents-backtrack
       (implies (and (fgl-object-mark-bfrs-bitarr-contents x new-seen new)
                     (fgl-object-mark-bfrs-bitarr-contents y seen old)
                     (fgl-object-mark-bfrs-seen-contents new-seen seen y)
                     (bitarr-subsetp old new))
                (fgl-object-mark-bfrs-bitarr-contents x seen new))
       :hints ((acl2::witness)))

     (def-updater-independence-thm fgl-object-mark-bfrs-bitarr-contents-backtrack2
       (implies (and (fgl-object-mark-bfrs-bitarr-contents x new-seen new)
                     (fgl-object-mark-bfrs-bitarr-contents y seen2 old)
                     (fgl-object-mark-bfrs-seen-contents new-seen seen2 y)
                     (fgl-object-mark-bfrs-bitarr-contents yy seen oldold)
                     (fgl-object-mark-bfrs-seen-contents seen2 seen yy)
                     (bitarr-subsetp old new)
                     (bitarr-subsetp oldold old))
                (fgl-object-mark-bfrs-bitarr-contents x seen new))
       :hints ((acl2::witness)))

     
     (acl2::defexample fgl-object-mark-bfrs-bitarr-contents-top-subobj-example
       :pattern (member z (fgl-object-top-bfrlist y))
       :templates ((fgl-object-subobj-containing-top-bfr y z) z)
       :instance-rulename fgl-object-mark-bfrs-bitarr-contents-instancing)


     (acl2::defexample bfrs-markedp-example
       :pattern (bfr-markedp bfr bitarr)
       :templates (bfr)
       :instance-rulename bfrs-markedp-instancing)
     
     (defthm bfrs-markedp-nil
       (bfrs-markedp nil bitarr)
       :hints(("Goal" :in-theory (enable bfrs-markedp))))

     (defthm bfrs-markedp-of-append
       (iff (bfrs-markedp (append x y) bitarr)
            (and (bfrs-markedp x bitarr)
                 (bfrs-markedp y bitarr)))
       :hints ((acl2::witness)))


     (defthm fgl-object-mark-bfrs-bitarr-contents-of-cons
       (implies (and (fgl-object-mark-bfrs-bitarr-contents rest (cons (cons x t) seen) bitarr)
                     (bfrs-markedp (fgl-object-top-bfrlist x) bitarr)
                     (equal (cons x rest) (fgl-object-subobjects x)))
                (fgl-object-mark-bfrs-bitarr-contents (cons x rest) seen bitarr))
       :hints (("goal" :in-theory (enable member-when-equal-cons))
               (acl2::witness))
       :otf-flg t)

     (defret <fn>-bitarr-contains-top-bfrlist1
       (bfrs-markedp (fgl-object-top-bfrlist1 x) new-bitarr)
       :hints(("Goal" :in-theory (enable fgl-object-top-bfrlist1
                                         bfrs-markedp
                                         acl2::member-of-cons)
               :expand (<call>)))
       :fn fgl-object-mark-bfrs)

     ;; (defthm bfrs-markedp-when-bitarr-subsetp
     ;;   (implies (and (bfrs-markedp x bitarr)
     ;;                 (bitarr-subsetp bitarr new-bitarr))
     ;;            (bfrs-markedp x new-bitarr))
     ;;   :hints ((acl2::witness)))

     (def-updater-independence-thm bfrs-markedp-when-bitarr-subsetp
       (implies (and (bfrs-markedp x old)
                     (bitarr-subsetp old new))
                (bfrs-markedp x new))
       :hints ((acl2::witness)))


     (defret-mutual <fn>-bitarr-contains-top-bfrlist1
       (defret <fn>-bitarr-contains-top-bfrlist1
         (bfrs-markedp (fgl-objectlist-top-bfrlist1 x) new-bitarr)
         :hints('(:in-theory (e/d (fgl-objectlist-top-bfrlist1))
                  :expand (<call>)))
         :fn fgl-objectlist-mark-bfrs)

       (defret <fn>-bitarr-contains-top-bfrlist1
         (bfrs-markedp (fgl-object-alist-top-bfrlist1 x) new-bitarr)
         :hints('(:in-theory (e/d (fgl-object-alist-top-bfrlist1))
                  :expand (<call>)))
         :fn fgl-object-alist-mark-bfrs)
       :skip-others t)

     (defret <fn>-bitarr-contains-top-bfrlist
       (implies (not (hons-assoc-equal (fgl-object-fix x) seen))
                (bfrs-markedp (fgl-object-top-bfrlist x) new-bitarr))
       :hints(("Goal" :in-theory (enable fgl-object-top-bfrlist)
               :expand (<call>))
              (and stable-under-simplificationp
                   '(:in-theory (enable bfrs-markedp
                                        acl2::member-of-cons))))
       :fn fgl-object-mark-bfrs)

     (def-updater-independence-thm bitarr-subsetp-trans-rw
       (implies (and (bitarr-subsetp oldold old)
                     (bitarr-subsetp old new))
                (bitarr-subsetp oldold new))
       :hints ((acl2::witness)))

     (include-book "tools/trivial-ancestors-check" :dir :system)
     (acl2::use-trivial-ancestors-check)


     (defret-mutual <fn>-bitarr-contents-correct
       (defret <fn>-bitarr-contents-correct
         (b* ((subobjs (fgl-object-subobjects x)))
           (implies (fgl-object-mark-bfrs-local-invar subobjs seen)
                    (fgl-object-mark-bfrs-bitarr-contents subobjs seen new-bitarr)))
         :hints ('(:expand (<call>)
                   :use fgl-object-mark-bfrs-bitarr-contains-top-bfrlist
                   :in-theory (disable fgl-object-mark-bfrs-bitarr-contains-top-bfrlist)
                   :do-not-induct t))
         :fn fgl-object-mark-bfrs)
       (defret <fn>-bitarr-contents-correct
         (b* ((subobjs (fgl-objectlist-subobjects x)))
           (implies (fgl-object-mark-bfrs-local-invar subobjs seen)
                    (fgl-object-mark-bfrs-bitarr-contents subobjs seen new-bitarr)))
         :hints ('(:expand (<call>)))
         :fn fgl-objectlist-mark-bfrs)
       (defret <fn>-bitarr-contents-correct
         (b* ((subobjs (fgl-object-alist-subobjects x)))
           (implies (fgl-object-mark-bfrs-local-invar subobjs seen)
                    (fgl-object-mark-bfrs-bitarr-contents subobjs seen new-bitarr)))
         :hints ('(:expand (<call>)))
         :fn fgl-object-alist-mark-bfrs))




     

     (acl2::defexample fgl-object-mark-bfrs-seen-invar-example
       :pattern (member y (fgl-object-subobjects x))
       :templates (x y)
       :instance-rulename fgl-object-mark-bfrs-seen-invar-instancing)


     

     (defthm fgl-object-mark-bfrs-seen-invar-implies-fgl-object-mark-bfrs-local-invar
       (implies (and (fgl-object-mark-bfrs-seen-invar seen)
                     (fgl-objectlist-closed-downwards subobjs))
                (fgl-object-mark-bfrs-local-invar subobjs seen))
       :hints ((acl2::witness)))

     (defthmd fgl-object-p-when-member-of-fgl-objectlist
       (implies (and (member y x)
                     (fgl-objectlist-p x))
                (fgl-object-p y))
       :hints(("Goal" :in-theory (enable member fgl-objectlist-p))))

     (defthm fgl-object-mark-bfrs-seen-contents-preserves-seen-invar
       (implies (and (fgl-object-mark-bfrs-seen-invar seen)
                     (fgl-object-mark-bfrs-seen-contents new seen subobjs)
                     (fgl-objectlist-closed-downwards subobjs))
                (fgl-object-mark-bfrs-seen-invar new))
       :hints ((acl2::witness)
               (and stable-under-simplificationp
                    '(:in-theory (enable fgl-object-p-when-member-of-fgl-objectlist)))))
     
     




     (acl2::defexample fgl-object-mark-bfrs-bitarr-invar-example
       :pattern (member bfr (fgl-object-bfrlist obj))
       :templates (obj bfr)
       :instance-rulename fgl-object-mark-bfrs-bitarr-invar-instancing)

     

     
     (acl2::defexample fgl-object-mark-bfrs-bitarr-contents-bfr-at-top-example
       :pattern (member bfr (fgl-object-bfrlist obj))
       :templates ((fgl-object-subobj-containing-bfr-at-top obj bfr) bfr)
       :instance-rulename fgl-object-mark-bfrs-bitarr-contents-instancing)

     
     (acl2::defexample fgl-objectlist-closed-downwards-bfr-at-top-example
       :pattern (member z (fgl-object-bfrlist y))
       :templates (y (fgl-object-subobj-containing-bfr-at-top y z))
       :instance-rulename fgl-objectlist-closed-downwards-instancing)

     
     (acl2::defexample fgl-object-mark-bfrs-bitarr-invar-bfr-at-top-example
       :pattern (member bfr (fgl-object-bfrlist obj))
       :templates ((fgl-object-subobj-containing-bfr-at-top obj bfr) bfr)
       :instance-rulename fgl-object-mark-bfrs-bitarr-invar-instancing)


     (defthm member-bfrlist-of-fgl-object-subobj-containing-bfr-at-top
       (implies (member bfr (fgl-object-bfrlist obj))
                (member bfr (fgl-object-bfrlist (fgl-object-subobj-containing-bfr-at-top obj bfr))))
       :hints (("goal" :use ((:instance fgl-object-subobj-containing-bfr-at-top-when-member-bfrs (x obj)))
                :in-theory (disable fgl-object-subobj-containing-bfr-at-top-when-member-bfrs))))
     
     
     (defthm fgl-object-mark-bfrs-bitarr-invar-preserved
       (implies (and (fgl-object-mark-bfrs-seen-invar seen)
                     (fgl-object-mark-bfrs-bitarr-invar seen bitarr)
                     (fgl-object-mark-bfrs-bitarr-contents subobjs seen new-b)
                     (fgl-object-mark-bfrs-seen-contents new-s seen subobjs)
                     (fgl-objectlist-closed-downwards subobjs)
                     (bitarr-subsetp bitarr new-b))
                (fgl-object-mark-bfrs-bitarr-invar new-s new-b))
       :hints ((acl2::Witness)
               (and stable-under-simplificationp
                    '(:in-theory (enable acl2::member-of-cons))))
       :otf-flg t)

     

     (defret <fn>-in-seen
       (implies (and (fgl-object-mark-bfrs-seen-invar seen)
                     (not (hons-assoc-equal y seen))
                     (fgl-object-p y)
                     (case-split (not (fgl-object-case y '(:g-var :g-concrete :g-boolean)))))
                (iff (hons-assoc-equal y new-seen)
                     (member y (fgl-object-subobjects x))))
       :hints (("goal" :use ((:instance fgl-object-mark-bfrs-new-seenlist-contents))
                :in-theory (e/d (fgl-object-mark-bfrs-seen-contents-necc)
                                (fgl-object-mark-bfrs-new-seenlist-contents))))
       :fn fgl-object-mark-bfrs)

     (defthm fgl-object-mark-bfrs-seen-invar-of-nil
       (fgl-object-mark-bfrs-seen-invar nil)
       :hints(("Goal" :in-theory (enable fgl-object-mark-bfrs-seen-invar))))

     (defret <fn>-preserves-seen-invar
       (implies (fgl-object-mark-bfrs-seen-invar seen)
                (fgl-object-mark-bfrs-seen-invar new-seen))
       :hints (("goal" :use ((:instance fgl-object-mark-bfrs-seen-contents-preserves-seen-invar
                              (new new-seen)
                              (subobjs (fgl-object-subobjects x))))
                :in-theory (disable fgl-object-mark-bfrs-seen-contents-preserves-seen-invar)))
       :fn fgl-object-mark-bfrs)

     (defret <fn>-preserves-seen-invar
       (implies (fgl-object-mark-bfrs-seen-invar seen)
                (fgl-object-mark-bfrs-seen-invar new-seen))
       :hints (("goal" :use ((:instance fgl-object-mark-bfrs-seen-contents-preserves-seen-invar
                              (new new-seen)
                              (subobjs (fgl-objectlist-subobjects x))))
                :in-theory (disable fgl-object-mark-bfrs-seen-contents-preserves-seen-invar)))
       :fn fgl-objectlist-mark-bfrs)

     (defret <fn>-preserves-seen-invar
       (implies (fgl-object-mark-bfrs-seen-invar seen)
                (fgl-object-mark-bfrs-seen-invar new-seen))
       :hints (("goal" :use ((:instance fgl-object-mark-bfrs-seen-contents-preserves-seen-invar
                              (new new-seen)
                              (subobjs (fgl-object-alist-subobjects x))))
                :in-theory (disable fgl-object-mark-bfrs-seen-contents-preserves-seen-invar)))
       :fn fgl-object-alist-mark-bfrs)

     (defthm fgl-object-mark-bfrs-bitarr-invar-empty
       (fgl-object-mark-bfrs-bitarr-invar nil bitarr)
       :hints(("Goal" :in-theory (enable fgl-object-mark-bfrs-bitarr-invar))))

     (defret <fn>-preserves-bitarr-invar
       (implies (and (fgl-object-mark-bfrs-seen-invar seen)
                     (fgl-object-mark-bfrs-bitarr-invar seen bitarr))
                (fgl-object-mark-bfrs-bitarr-invar new-seen new-bitarr))
       :hints (("goal" :use ((:instance fgl-object-mark-bfrs-bitarr-invar-preserved
                              (new-s new-seen)
                              (new-b new-bitarr)
                              (subobjs (fgl-object-subobjects x))))
                :in-theory (disable fgl-object-mark-bfrs-bitarr-invar-preserved)))
       :fn fgl-object-mark-bfrs)

     (defret <fn>-preserves-bitarr-invar
       (implies (and (fgl-object-mark-bfrs-seen-invar seen)
                     (fgl-object-mark-bfrs-bitarr-invar seen bitarr))
                (fgl-object-mark-bfrs-bitarr-invar new-seen new-bitarr))
       :hints (("goal" :use ((:instance fgl-object-mark-bfrs-bitarr-invar-preserved
                              (new-s new-seen)
                              (new-b new-bitarr)
                              (subobjs (fgl-objectlist-subobjects x))))
                :in-theory (disable fgl-object-mark-bfrs-bitarr-invar-preserved)))
       :fn fgl-objectlist-mark-bfrs)

     (defret <fn>-preserves-bitarr-invar
       (implies (and (fgl-object-mark-bfrs-seen-invar seen)
                     (fgl-object-mark-bfrs-bitarr-invar seen bitarr))
                (fgl-object-mark-bfrs-bitarr-invar new-seen new-bitarr))
       :hints (("goal" :use ((:instance fgl-object-mark-bfrs-bitarr-invar-preserved
                              (new-s new-seen)
                              (new-b new-bitarr)
                              (subobjs (fgl-object-alist-subobjects x))))
                :in-theory (disable fgl-object-mark-bfrs-bitarr-invar-preserved)))
       :fn fgl-object-alist-mark-bfrs)
     
     (defret <fn>-ensures-bitarr-contains-bfrs
       (implies (and (fgl-object-mark-bfrs-seen-invar seen)
                     (fgl-object-mark-bfrs-bitarr-invar seen bitarr))
                (bfrs-markedp (fgl-object-bfrlist x) new-bitarr))
       :hints (("goal" :use fgl-object-mark-bfrs-preserves-bitarr-invar
                :in-theory (e/d (acl2::member-of-cons
                                 fgl-object-bfrlist-when-g-boolean
                                 fgl-object-bfrlist-when-g-concrete
                                 fgl-object-bfrlist-when-g-var)
                                (fgl-object-mark-bfrs-preserves-bitarr-invar)))
               (acl2::witness))
       :fn fgl-object-mark-bfrs)

     (defret-mutual <fn>-ensures-bitarr-contains-bfrs
       (defret <fn>-ensures-bitarr-contains-bfrs
         (implies (and (fgl-object-mark-bfrs-seen-invar seen)
                       (fgl-object-mark-bfrs-bitarr-invar seen bitarr))
                  (bfrs-markedp (fgl-objectlist-bfrlist x) new-bitarr))
         :hints ('(:expand (<call>
                            (fgl-objectlist-bfrlist x))))
         :fn fgl-objectlist-mark-bfrs)
       (defret <fn>-ensures-bitarr-contains-bfrs
         (implies (and (fgl-object-mark-bfrs-seen-invar seen)
                       (fgl-object-mark-bfrs-bitarr-invar seen bitarr))
                  (bfrs-markedp (fgl-object-alist-bfrlist x) new-bitarr))
         :hints ('(:expand (<call>
                            (fgl-object-alist-bfrlist x))))
         :fn fgl-object-alist-mark-bfrs)
       :skip-others t)))


  (local (in-theory (enable fgl-object-mark-bfrs-invar)))

  (defthm fgl-object-mark-bfrs-invar-when-seen-empty
    (fgl-object-mark-bfrs-invar nil bitarr))

  (def-updater-independence-thm fgl-object-mark-bfrs-invar-of-mark-bitarr
    (implies (and (fgl-object-mark-bfrs-invar seen old)
                  (bitarr-subsetp old new))
             (fgl-object-mark-bfrs-invar seen new))
    :hints ((acl2::witness)))


  (defret <fn>-preserves-invar
    (implies (fgl-object-mark-bfrs-invar seen bitarr)
             (fgl-object-mark-bfrs-invar new-seen new-bitarr))
    :fn fgl-object-mark-bfrs)

  (defret <fn>-preserves-invar
    (implies (fgl-object-mark-bfrs-invar seen bitarr)
             (fgl-object-mark-bfrs-invar new-seen new-bitarr))
    :fn fgl-objectlist-mark-bfrs)

  (defret <fn>-preserves-invar
    (implies (fgl-object-mark-bfrs-invar seen bitarr)
             (fgl-object-mark-bfrs-invar new-seen new-bitarr))
    :fn fgl-object-alist-mark-bfrs)


  (defret <fn>-marks-bfrs
    (implies (fgl-object-mark-bfrs-invar seen bitarr)
             (bfrs-markedp (fgl-object-bfrlist x) new-bitarr))
    :fn fgl-object-mark-bfrs)

  (defret <fn>-marks-bfrs
    (implies (fgl-object-mark-bfrs-invar seen bitarr)
             (bfrs-markedp (fgl-objectlist-bfrlist x) new-bitarr))
    :fn fgl-objectlist-mark-bfrs)

  (defret <fn>-marks-bfrs
    (implies (fgl-object-mark-bfrs-invar seen bitarr)
             (bfrs-markedp (fgl-object-alist-bfrlist x) new-bitarr))
    :fn fgl-object-alist-mark-bfrs))
    



