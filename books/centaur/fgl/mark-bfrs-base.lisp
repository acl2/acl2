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
;; gl-objects using fast alists.  This will avoid the overhead of memoizing
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


(local (defthm gl-objectlist-p-of-append
         (implies (and (gl-objectlist-p x)
                       (gl-objectlist-p y))
                  (gl-objectlist-p (append x y)))))

(defines gl-object-subobjects
  :ruler-extenders :all
  (define gl-object-subobjects ((x gl-object-p))
    :measure (acl2::two-nats-measure (gl-object-count x) 0)
    :returns (subobjs gl-objectlist-p)
    (cons (gl-object-fix x)
          (gl-object-case x
            :g-ite (append (gl-object-subobjects x.test)
                           (gl-object-subobjects x.then)
                           (gl-object-subobjects x.else))
            :g-apply (gl-objectlist-subobjects x.args)
            :g-map (gl-object-alist-subobjects x.alist)
            :g-cons (append (gl-object-subobjects x.car)
                            (gl-object-subobjects x.cdr))
            :otherwise nil)))
  (define gl-objectlist-subobjects ((x gl-objectlist-p))
    :measure (acl2::two-nats-measure (gl-objectlist-count x) 0)
    :returns (subobjs gl-objectlist-p)
    (and (consp x)
         (append (gl-object-subobjects (car x))
                 (gl-objectlist-subobjects (cdr x)))))
  (define gl-object-alist-subobjects ((x gl-object-alist-p))
    :measure (acl2::two-nats-measure (gl-object-alist-count x) (len x))
    :returns (subobjs gl-objectlist-p)
    (and (consp x)
         (append (and (mbt (consp (car x)))
                      (gl-object-subobjects (cdar x)))
                 (gl-object-alist-subobjects (cdr x)))))
  ///
  (fty::deffixequiv-mutual gl-object-subobjects
    :hints(("Goal" :in-theory (enable gl-object-alist-fix))))


  (defret-mutual <fn>-transitive
    (defret <fn>-transitive
      (implies (and (member y subobjs)
                    (member z (gl-object-subobjects y)))
               (member z subobjs))
      :hints ('(:expand (<call>))
              (and stable-under-simplificationp
                   '(:expand ((:free (y) <call>)))))
      :fn gl-object-subobjects)
    (defret <fn>-transitive
      (implies (and (member y subobjs)
                    (member z (gl-object-subobjects y)))
               (member z subobjs))
      :hints ('(:expand ((:free (y) <call>))))
      :fn gl-objectlist-subobjects)
    (defret <fn>-transitive
      (implies (and (member y subobjs)
                    (member z (gl-object-subobjects y)))
               (member z subobjs))
      :hints ('(:expand ((:free (y) <call>))))
      :fn gl-object-alist-subobjects))

  (defret-mutual bfr-member-of-<fn>
    (defret bfr-member-of-<fn>
      (implies (and (member k (gl-object-bfrlist y))
                    (not (member k (gl-object-bfrlist x))))
               (not (member y subobjs)))
      :hints ('(:expand (<call>
                         (gl-object-bfrlist x))))
      :fn gl-object-subobjects)
    (defret bfr-member-of-<fn>
      (implies (and (member k (gl-object-bfrlist y))
                    (not (member k (gl-objectlist-bfrlist x))))
               (not (member y subobjs)))
      :hints ('(:expand (<call>
                         (gl-objectlist-bfrlist x))))
      :fn gl-objectlist-subobjects)
    (defret bfr-member-of-<fn>
      (implies (and (member k (gl-object-bfrlist y))
                    (not (member k (gl-object-alist-bfrlist x))))
               (not (member y subobjs)))
      :hints ('(:expand (<call>
                         (gl-object-alist-bfrlist x))))
      :fn gl-object-alist-subobjects))

  (defret-mutual not-<fn>-when-count-less
    (defret not-<fn>-when-count-less
      (implies (< (gl-object-count x) (gl-object-count y))
               (not (member y subobjs)))
      :hints ('(:expand (<call>)))
      :fn gl-object-subobjects)
    (defret not-<fn>-when-count-less
      (implies (< (gl-objectlist-count x) (gl-object-count y))
               (not (member y subobjs)))
      :hints ('(:expand (<call>)))
      :fn gl-objectlist-subobjects)
    (defret not-<fn>-when-count-less
      (implies (< (gl-object-alist-count x) (gl-object-count y))
               (not (member y subobjs)))
      :hints ('(:expand (<call>)))
      :fn gl-object-alist-subobjects))

  (defthm gl-object-subobjects-self
    (implies (gl-object-p x)
             (member x (gl-object-subobjects x)))
    :hints (("goal" :expand ((gl-object-subobjects x)))))

  (defthm gl-object-subobjects-self-fix
    (member (gl-object-fix x) (gl-object-subobjects x))
    :hints (("goal" :expand ((gl-object-subobjects x)))))


  (defret <fn>-when-g-ite
    (implies (gl-object-case x :g-ite)
             (equal subobjs
                    (b* (((g-ite x)))
                      (cons (gl-object-fix x)
                            (append (gl-object-subobjects x.test)
                                    (gl-object-subobjects x.then)
                                    (gl-object-subobjects x.else))))))
    :fn gl-object-subobjects)

  (defret <fn>-when-g-apply
    (implies (gl-object-case x :g-apply)
             (equal subobjs
                    (b* (((g-apply x)))
                      (cons (gl-object-fix x)
                            (gl-objectlist-subobjects x.args)))))
    :fn gl-object-subobjects)

  (defret <fn>-when-g-map
    (implies (gl-object-case x :g-map)
             (equal subobjs
                    (b* (((g-map x)))
                      (cons (gl-object-fix x)
                            (gl-object-alist-subobjects x.alist)))))
    :fn gl-object-subobjects)

  (defret <fn>-when-g-cons
    (implies (gl-object-case x :g-cons)
             (equal subobjs
                    (b* (((g-cons x)))
                      (cons (gl-object-fix x)
                            (append (gl-object-subobjects x.car)
                                    (gl-object-subobjects x.cdr))))))
    :fn gl-object-subobjects)

  (defret <fn>-when-atomic-1
    (implies (gl-object-case x '(:g-concrete :g-boolean :g-var))
             (equal subobjs
                    (list (gl-object-fix x))))
    :fn gl-object-subobjects)

  (defret <fn>-when-atomic-2
    (implies (gl-object-case x :g-integer)
             (equal subobjs
                    (list (gl-object-fix x))))
    :fn gl-object-subobjects)

  (defret <fn>-when-consp
    (implies (consp x)
             (equal subobjs
                    (append (gl-object-subobjects (car x))
                            (gl-objectlist-subobjects (cdr x)))))
    :fn gl-objectlist-subobjects)

  (defret <fn>-when-atom
    (implies (not (consp x))
             (equal subobjs nil))
    :fn gl-objectlist-subobjects)

  (defret <fn>-when-consp-car
    (implies (consp (car x))
             (equal subobjs
                    (append (gl-object-subobjects (cdar x))
                            (gl-object-alist-subobjects (cdr x)))))
    :fn gl-object-alist-subobjects)

  (defret <fn>-when-not-consp-car
    (implies (and (consp x)
                  (not (consp (car x))))
             (equal subobjs
                    (gl-object-alist-subobjects (cdr x))))
    :fn gl-object-alist-subobjects)

  (defret <fn>-when-atom
    (implies (not (consp x))
             (equal subobjs nil))
    :fn gl-object-alist-subobjects))


(define gl-object-top-bfrlist1 ((x gl-object-p))
  :returns (bfrs)
  (gl-object-case x
    :g-boolean (list x.bool)
    :otherwise nil)
  ///
  (defret member-bfrlist-when-<fn>
    (implies (not (member bfr (gl-object-bfrlist x)))
             (not (member bfr bfrs)))
    :hints(("Goal" :expand ((gl-object-bfrlist x))))))



(define gl-objectlist-top-bfrlist1 ((x gl-objectlist-p))
  :returns (bfrs)
  (if (atom x)
      nil
    (append (gl-object-top-bfrlist1 (car x))
            (gl-objectlist-top-bfrlist1 (cdr x))))
  ///
  (defret member-bfrlist-when-<fn>
    (implies (not (member bfr (gl-objectlist-bfrlist x)))
             (not (member bfr bfrs)))
    :hints(("Goal" :induct <call>
            :expand ((gl-objectlist-bfrlist x))))))

(define gl-object-alist-top-bfrlist1 ((x gl-object-alist-p))
  :hooks ((:fix :hints (("goal" :in-theory (enable gl-object-alist-fix)))))
  :returns (bfrs)
  (if (atom x)
      nil
    (append (and (mbt (consp (car x)))
                 (gl-object-top-bfrlist1 (cdar x)))
            (gl-object-alist-top-bfrlist1 (cdr x))))
  ///
  (defret member-bfrlist-when-<fn>
    (implies (not (member bfr (gl-object-alist-bfrlist x)))
             (not (member bfr bfrs)))
    :hints(("Goal" :induct <call>
            :expand ((gl-object-alist-bfrlist x))))))

(define gl-object-top-bfrlist ((x gl-object-p))
  :returns (bfrs)
  (gl-object-case x
    :g-boolean (list x.bool)
    :g-integer x.bits
    :g-ite (append (gl-object-top-bfrlist1 x.test)
                   (gl-object-top-bfrlist1 x.then)
                   (gl-object-top-bfrlist1 x.else))
    :g-apply (gl-objectlist-top-bfrlist1 x.args)
    :g-map (gl-object-alist-top-bfrlist1 x.alist)
    :g-cons (append (gl-object-top-bfrlist1 x.car)
                    (gl-object-top-bfrlist1 x.cdr))
    :otherwise nil)
  ///
  (defret member-bfrlist-when-<fn>
    (implies (not (member bfr (gl-object-bfrlist x)))
             (not (member bfr bfrs)))
    :hints(("Goal" 
            :expand ((gl-object-bfrlist x))))))



(define gl-objectlist-subobj-containing-top-bfr ((x gl-objectlist-p)
                                                 bfr)
  :returns (subobj gl-object-p)
  (if (atom x)
      nil
    (if (member-equal bfr (gl-object-top-bfrlist1 (car x)))
        (gl-object-fix (car x))
      (gl-objectlist-subobj-containing-top-bfr (cdr x) bfr)))
  ///
  (defret <fn>-finds-subobj
    (implies (member bfr (gl-objectlist-top-bfrlist1 x))
             (and (member bfr (gl-object-top-bfrlist1 subobj))
                  (member subobj (gl-objectlist-subobjects x))))
    :hints (("goal" :induct t :expand ((gl-objectlist-top-bfrlist1 x)
                                       (gl-objectlist-subobjects x))))))

(define gl-object-alist-subobj-containing-top-bfr ((x gl-object-alist-p)
                                                   bfr)
  :hooks ((:fix :hints (("goal" :in-theory (enable gl-object-alist-fix)))))
  :returns (subobj gl-object-p)
  (if (atom x)
      nil
    (if (and (mbt (consp (car x)))
             (member-equal bfr (gl-object-top-bfrlist1 (cdar x))))
        (gl-object-fix (cdar x))
      (gl-object-alist-subobj-containing-top-bfr (cdr x) bfr)))
  ///
  (defret <fn>-finds-subobj
    (implies (member bfr (gl-object-alist-top-bfrlist1 x))
             (and (member bfr (gl-object-top-bfrlist1 subobj))
                  (member subobj (gl-object-alist-subobjects x))))
    :hints (("goal" :induct t :expand ((gl-object-alist-top-bfrlist1 x)
                                       (gl-object-alist-subobjects x))))))

(define gl-object-subobj-containing-top-bfr ((x gl-object-p)
                                             bfr)
  :returns (subobj gl-object-p)
  (gl-object-case x
    :g-ite (cond ((member-equal bfr (gl-object-top-bfrlist1 x.test)) x.test)
                 ((member-equal bfr (gl-object-top-bfrlist1 x.then)) x.then)
                 ((member-equal bfr (gl-object-top-bfrlist1 x.else)) x.else))
    :g-apply (gl-objectlist-subobj-containing-top-bfr x.args bfr)
    :g-map (gl-object-alist-subobj-containing-top-bfr x.alist bfr)
    :g-cons (cond ((member-equal bfr (gl-object-top-bfrlist1 x.car)) x.car)
                  ((member-equal bfr (gl-object-top-bfrlist1 x.cdr)) x.cdr))
    :otherwise nil)
  ///
  (local (defthm not-equal-gl-objects-when-count-less
           (implies (< (gl-object-count x) (gl-object-count y))
                    (not (equal x y)))))

  (local (in-theory (enable acl2::member-of-cons)))

  (defret <fn>-finds-subobj
    (implies (and (member bfr (gl-object-top-bfrlist x))
                  (not (gl-object-case x '(:g-var :g-concrete :g-boolean :g-integer))))
             (and (member bfr (gl-object-top-bfrlist1 subobj))
                  (member subobj (gl-object-subobjects x))
                  (not (equal subobj x))
                  (not (equal subobj (gl-object-fix x)))))
    :hints (("goal" :expand ((gl-object-top-bfrlist x)
                             (gl-object-subobjects x)))
            (and stable-under-simplificationp
                 '(:use ((:instance gl-object-alist-subobj-containing-top-bfr-finds-subobj
                          (x (g-map->alist x)))
                         (:instance gl-objectlist-subobj-containing-top-bfr-finds-subobj
                          (x (g-apply->args x))))
                   :expand ((gl-object-count x))
                   :in-theory (disable gl-object-alist-subobj-containing-top-bfr-finds-subobj
                                       gl-objectlist-subobj-containing-top-bfr-finds-subobj)
                   :do-not '(generalize fertilize eliminate-destructors))))))



(defines gl-object-subobj-containing-bfr-at-top
  (define gl-object-subobj-containing-bfr-at-top ((x gl-object-p) bfr)
    :measure (two-nats-measure (gl-object-count x) 0)
    :returns (subobj gl-object-p)
    (if (member-equal bfr (gl-object-top-bfrlist x))
        (gl-object-fix x)
      (gl-object-case x
        :g-ite (cond ((member-equal bfr (gl-object-bfrlist x.test))
                      (gl-object-subobj-containing-bfr-at-top x.test bfr))
                     ((member-equal bfr (gl-object-bfrlist x.then))
                      (gl-object-subobj-containing-bfr-at-top x.then bfr))
                     ((member-equal bfr (gl-object-bfrlist x.else))
                      (gl-object-subobj-containing-bfr-at-top x.else bfr)))
        :g-cons (cond ((member-equal bfr (gl-object-bfrlist x.car))
                       (gl-object-subobj-containing-bfr-at-top x.car bfr))
                      ((member-equal bfr (gl-object-bfrlist x.cdr))
                       (gl-object-subobj-containing-bfr-at-top x.cdr bfr)))
        :g-apply (gl-objectlist-subobj-containing-bfr-at-top x.args bfr)
        :g-map (gl-object-alist-subobj-containing-bfr-at-top x.alist bfr)
        :otherwise nil)))
  (define gl-objectlist-subobj-containing-bfr-at-top ((x gl-objectlist-p) bfr)
    :measure (two-nats-measure (gl-objectlist-count x) 0)
    :returns (subobj gl-object-p)
    (if (atom x)
        nil
      (if (member-equal bfr (gl-object-bfrlist (car x)))
          (gl-object-subobj-containing-bfr-at-top (car x) bfr)
        (gl-objectlist-subobj-containing-bfr-at-top (cdr x) bfr))))
  (define gl-object-alist-subobj-containing-bfr-at-top ((x gl-object-alist-p) bfr)
    :measure (two-nats-measure (gl-object-alist-count x) (len x))
    :returns (subobj gl-object-p)
    (if (atom x)
        nil
      (if (and (mbt (consp (car x)))
               (member-equal bfr (gl-object-bfrlist (cdar x))))
          (gl-object-subobj-containing-bfr-at-top (cdar x) bfr)
        (gl-object-alist-subobj-containing-bfr-at-top (cdr x) bfr))))
  ///
  (defret-mutual <fn>-when-member-bfrs
    (defret <fn>-when-member-bfrs
      (implies (member bfr (gl-object-bfrlist x))
               (and (member subobj (gl-object-subobjects x))
                    (member bfr (gl-object-top-bfrlist subobj))))
      :hints ('(:expand (<call>
                         (gl-object-subobjects x)
                         (gl-object-bfrlist x)))
              (and stable-under-simplificationp
                   '(:expand ((gl-object-top-bfrlist x)))))
      :fn gl-object-subobj-containing-bfr-at-top)
    (defret <fn>-when-member-bfrs
      (implies (member bfr (gl-objectlist-bfrlist x))
               (and (member subobj (gl-objectlist-subobjects x))
                    (member bfr (gl-object-top-bfrlist subobj))))
      :hints ('(:expand (<call>
                         (gl-objectlist-subobjects x)
                         (gl-objectlist-bfrlist x))))
      :fn gl-objectlist-subobj-containing-bfr-at-top)
    (defret <fn>-when-member-bfrs
      (implies (member bfr (gl-object-alist-bfrlist x))
               (and (member subobj (gl-object-alist-subobjects x))
                    (member bfr (gl-object-top-bfrlist subobj))))
      :hints ('(:expand (<call>
                         (gl-object-alist-subobjects x)
                         (gl-object-alist-bfrlist x))))
      :fn gl-object-alist-subobj-containing-bfr-at-top))

  (defret-mutual <fn>-not-var-type
    (defret <fn>-not-var-type
      (not (equal (gl-object-kind subobj) :g-var))
      :hints ('(:expand (<call>))
              (and stable-under-simplificationp
                   '(:expand ((gl-object-top-bfrlist x)))))
      :fn gl-object-subobj-containing-bfr-at-top)
    (defret <fn>-not-var-type
      (not (equal (gl-object-kind subobj) :g-var))
      :hints ('(:expand (<call>)))
      :fn gl-objectlist-subobj-containing-bfr-at-top)
    (defret <fn>-not-var-type
      (not (equal (gl-object-kind subobj) :g-var))
      :hints ('(:expand (<call>)))
      :fn gl-object-alist-subobj-containing-bfr-at-top))

  (defret-mutual <fn>-not-concrete-type
    (defret <fn>-not-concrete-type
      (implies (member bfr (gl-object-bfrlist x))
               (not (equal (gl-object-kind subobj) :g-concrete)))
      :hints ('(:expand (<call>
                         (gl-object-bfrlist x)))
              (and stable-under-simplificationp
                   '(:expand ((gl-object-top-bfrlist x)))))
      :fn gl-object-subobj-containing-bfr-at-top)
    (defret <fn>-not-concrete-type
      (implies (member bfr (gl-objectlist-bfrlist x))
               (not (equal (gl-object-kind subobj) :g-concrete)))
      :hints ('(:expand (<call>
                         (gl-objectlist-bfrlist x))))
      :fn gl-objectlist-subobj-containing-bfr-at-top)
    (defret <fn>-not-concrete-type
      (implies (member bfr (gl-object-alist-bfrlist x))
               (not (equal (gl-object-kind subobj) :g-concrete)))
      :hints ('(:expand (<call>
                         (gl-object-alist-bfrlist x))))
      :fn gl-object-alist-subobj-containing-bfr-at-top))

  (defret-mutual <fn>-not-boolean-type
    (defret <fn>-not-boolean-type
      (iff (equal (gl-object-kind subobj) :g-boolean)
           (and (equal (gl-object-kind x) :g-boolean)
                (equal bfr (g-boolean->bool x))
                (equal subobj (gl-object-fix x))))
      :hints ('(:expand (<call>
                         (gl-object-bfrlist x))
                :in-theory (enable acl2::member-of-cons))
              (and stable-under-simplificationp
                   '(:expand ((gl-object-top-bfrlist x))
                     :in-theory (enable gl-object-top-bfrlist1
                                        acl2::member-of-cons))))
      :fn gl-object-subobj-containing-bfr-at-top)
    (defret <fn>-not-boolean-type
      (implies (not (member bfr (gl-objectlist-top-bfrlist1 x)))
               (not (equal (gl-object-kind subobj) :g-boolean)))
      :hints ('(:expand (<call>
                         (gl-objectlist-top-bfrlist1 x))
                :in-theory (enable gl-object-top-bfrlist1))
              (and stable-under-simplificationp
                   '(:expand ((gl-object-bfrlist (car x))))))
      :fn gl-objectlist-subobj-containing-bfr-at-top)
    (defret <fn>-not-boolean-type
      (implies (not (member bfr (gl-object-alist-top-bfrlist1 x)))
               (not (equal (gl-object-kind subobj) :g-boolean)))
      :hints ('(:expand (<call>
                         (gl-object-alist-top-bfrlist1 x))
                :in-theory (enable gl-object-top-bfrlist1))
              (and stable-under-simplificationp
                   '(:expand ((gl-object-bfrlist (cdar x))))))
      :fn gl-object-alist-subobj-containing-bfr-at-top)
    :skip-others t))
    

 


(defsection gl-objectlist-closed-downwards
  (acl2::defquant gl-objectlist-closed-downwards (x)
    (forall (y z)
            (implies (and (member (gl-object-fix y) x)
                          ;; (gl-object-p z)
                          (not (member z x)))
                     (not (member z (gl-object-subobjects y)))))
    :rewrite :direct)

  (acl2::defexample gl-objectlist-closed-downwards-example
    :pattern (member z (gl-object-subobjects y))
    :templates (y z)
    :instance-rulename gl-objectlist-closed-downwards-instancing)

  (defthm gl-objectlist-closed-downwards-of-gl-object-subobjects
    (gl-objectlist-closed-downwards (gl-object-subobjects x))
    :hints ((acl2::witness)))

  (defthm gl-objectlist-closed-downwards-of-gl-objectlist-subobjects
    (gl-objectlist-closed-downwards (gl-objectlist-subobjects x))
    :hints ((acl2::witness)))

  (defthm gl-objectlist-closed-downwards-of-gl-object-alist-subobjects
    (gl-objectlist-closed-downwards (gl-object-alist-subobjects x))
    :hints ((acl2::witness)))

  (defthm gl-objectlist-closed-downwards-of-append
    (implies (and (gl-objectlist-closed-downwards x)
                  (gl-objectlist-closed-downwards y))
             (gl-objectlist-closed-downwards (append x y)))
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

(defines gl-object-mark-bfrs
  (define gl-object-mark-bfrs ((x gl-object-p)
                               bitarr
                               seen)
    :guard (and (< 0 (bits-length bitarr))
                (bfr-listp (gl-object-bfrlist x) (bfrstate (bfrmode :aignet) (1- (bits-length bitarr)))))
    :verify-guards nil
    :measure (acl2::two-nats-measure (gl-object-count x) 0)
    :returns (mv new-bitarr new-seen)
    (gl-object-case x
      :g-concrete (mv bitarr seen)
      :g-var (mv bitarr seen)
      :g-boolean (b* ((bitarr (bfr-mark x.bool bitarr)))
                   (mv bitarr seen))
      :otherwise
      (b* ((x (gl-object-fix x))
           ((when (hons-get x seen)) (mv bitarr seen))
           (seen (hons-acons x t seen)))
        (case acl2::x.kind
          (:g-integer (b* ((bitarr (bfrlist-mark (g-integer->bits x) bitarr)))
                        (mv bitarr seen)))
          (:g-ite (b* (((g-ite x))
                       ((mv bitarr seen) (gl-object-mark-bfrs x.test bitarr seen))
                       ((mv bitarr seen) (gl-object-mark-bfrs x.then bitarr seen)))
                    (gl-object-mark-bfrs x.else bitarr seen)))
          (:g-apply (gl-objectlist-mark-bfrs (g-apply->args x) bitarr seen))
          (:g-map (gl-object-alist-mark-bfrs (g-map->alist x) bitarr seen))
          (otherwise (b* (((g-cons x))
                          ((mv bitarr seen) (gl-object-mark-bfrs x.car bitarr seen)))
                       (gl-object-mark-bfrs x.cdr bitarr seen)))))))

  (define gl-objectlist-mark-bfrs ((x gl-objectlist-p)
                                   bitarr
                                   seen)
    :guard (and (< 0 (bits-length bitarr))
                (bfr-listp (gl-objectlist-bfrlist x)
                           (bfrstate (bfrmode :aignet) (1- (bits-length bitarr)))))
    :measure (acl2::two-nats-measure (gl-objectlist-count x) 0)
    :returns (mv new-bitarr new-seen)
    (b* (((when (atom x))
          (mv bitarr seen))
         ((mv bitarr seen) (gl-object-mark-bfrs (car x) bitarr seen)))
      (gl-objectlist-mark-bfrs (cdr x) bitarr seen)))

  (define gl-object-alist-mark-bfrs ((x gl-object-alist-p)
                                     bitarr
                                     seen)
    :guard (and (< 0 (bits-length bitarr))
                (bfr-listp (gl-object-alist-bfrlist x)
                           (bfrstate (bfrmode :aignet) (1- (bits-length bitarr)))))
    :measure (acl2::two-nats-measure (gl-object-alist-count x) (len x))
    :returns (mv new-bitarr new-seen)
    (b* (((when (atom x)) (mv bitarr seen))
         ((unless (mbt (consp (car x))))
          (gl-object-alist-mark-bfrs (cdr x) bitarr seen))
         ((mv bitarr seen) (gl-object-mark-bfrs (cdar x) bitarr seen)))
      (gl-object-alist-mark-bfrs (cdr x) bitarr seen)))
  ///

  ;; Basic properties...

  (defret-mutual length-of-<fn>
    (defret length-of-<fn>
      (implies (bfr-listp (gl-object-bfrlist x) (bfrstate (bfrmode :aignet) (1- (len bitarr))))
               (equal (len new-bitarr) (len bitarr)))
      :hints ('(:expand (<call>
                         (gl-object-bfrlist x))))
      :fn gl-object-mark-bfrs)
    (defret length-of-<fn>
      (implies (bfr-listp (gl-objectlist-bfrlist x) (bfrstate (bfrmode :aignet) (1- (len bitarr))))
               (equal (len new-bitarr) (len bitarr)))
      :hints ('(:expand (<call>
                         (gl-objectlist-bfrlist x))))
      :fn gl-objectlist-mark-bfrs)
    (defret length-of-<fn>
      (implies (bfr-listp (gl-object-alist-bfrlist x) (bfrstate (bfrmode :aignet) (1- (len bitarr))))
               (equal (len new-bitarr) (len bitarr)))
      :hints ('(:expand (<call>
                         (gl-object-alist-bfrlist x))))
      :fn gl-object-alist-mark-bfrs))

  (verify-guards gl-object-mark-bfrs
    :hints (("goal" :expand (gl-object-bfrlist x))))

  (defret-mutual length-of-<fn>-incr
    (defret length-of-<fn>-incr
      (>= (len new-bitarr) (len bitarr))
      :hints ('(:expand (<call>)))
      :fn gl-object-mark-bfrs
      :rule-classes :linear)
    (defret length-of-<fn>-incr
      (>= (len new-bitarr) (len bitarr))
      :hints ('(:expand (<call>)))
      :fn gl-objectlist-mark-bfrs
      :rule-classes :linear)
    (defret length-of-<fn>-incr
      (>= (len new-bitarr) (len bitarr))
      :hints ('(:expand (<call>)))
      :fn gl-object-alist-mark-bfrs
      :rule-classes :linear))

  

  (defret-mutual bfr-markedp-preserved-of-<fn>
    (defret bfr-markedp-preserved-of-<fn>
      (implies (bfr-markedp y bitarr)
               (bfr-markedp y new-bitarr))
      :hints ('(:expand (<call>)))
      :fn gl-object-mark-bfrs)
    (defret bfr-markedp-preserved-of-<fn>
      (implies (bfr-markedp y bitarr)
               (bfr-markedp y new-bitarr))
      :hints ('(:expand (<call>)))
      :fn gl-objectlist-mark-bfrs)
    (defret bfr-markedp-preserved-of-<fn>
      (implies (bfr-markedp y bitarr)
               (bfr-markedp y new-bitarr))
      :hints ('(:expand (<call>)))
      :fn gl-object-alist-mark-bfrs))

  
  (defret-mutual bitarr-subsetp-of-<fn>
    (defret bitarr-subsetp-of-<fn>
      (bitarr-subsetp bitarr new-bitarr)
      :hints ('(:expand (<call>)))
      :fn gl-object-mark-bfrs)
    (defret bitarr-subsetp-of-<fn>
      (bitarr-subsetp bitarr new-bitarr)
      :hints ('(:expand (<call>)))
      :fn gl-objectlist-mark-bfrs)
    (defret bitarr-subsetp-of-<fn>
      (bitarr-subsetp bitarr new-bitarr)
      :hints ('(:expand (<call>)))
      :fn gl-object-alist-mark-bfrs))

  ;; Two top-level invariants:
  ;; - gl-object-mark-bfrs-bitarr-invar
  ;; - gl-object-mark-bfrs-seen-invar

  ;; We'll prove a whole lot of local lemmas before we
  ;; prove that these top-level invariants are preserved by these functions and
  ;; also ensure that the bitarr will always contain the bfrs of x.



  (acl2::defquant gl-object-mark-bfrs-bitarr-invar (seen bitarr)
    (forall (obj bfr)
            (implies (and (hons-assoc-equal (gl-object-fix obj) seen)
                          (member bfr (gl-object-bfrlist obj)))
                     (bfr-markedp bfr bitarr)))
    :rewrite :direct)

  (acl2::defquant gl-object-mark-bfrs-seen-invar (seen)
    (forall (x y)
            (implies (and (hons-assoc-equal (gl-object-fix x) seen)
                          (not (hons-assoc-equal (gl-object-fix y) seen))
                          (not (gl-object-case y '(:g-var :g-concrete :g-boolean))))
                     (not (member y (gl-object-subobjects x)))))
    :rewrite :direct)

  (acl2::defquant bfrs-markedp (immed-bfrs bitarr)
    (forall bfr
            (implies (member bfr immed-bfrs)
                     (bfr-markedp bfr bitarr)))
    :rewrite :direct)


  (defund gl-object-mark-bfrs-invar (seen bitarr)
    (and (gl-object-mark-bfrs-seen-invar seen)
         (gl-object-mark-bfrs-bitarr-invar seen bitarr)))
  


  (local
   (progn

     (acl2::defquant gl-object-mark-bfrs-local-invar (subobjs seen)
       (forall (y z)
               (implies (and (member (gl-object-fix y) subobjs)
                             (hons-assoc-equal (gl-object-fix y) seen)
                             (not (hons-assoc-equal (gl-object-fix z) seen))
                             (not (gl-object-case z '(:g-var :g-concrete :g-boolean))))
                        (not (member z (gl-object-subobjects y)))))
       :rewrite :direct)

     (acl2::defexample gl-object-mark-bfrs-local-invar-example
       :pattern (member z (gl-object-subobjects y))
       :templates (y z)
       :instance-rulename gl-object-mark-bfrs-local-invar-instancing)

     (acl2::def-witness-ruleset mark-bfrs-witness-rules
       '(gl-object-mark-bfrs-local-invar-instancing
         gl-object-mark-bfrs-local-invar-example
         gl-object-mark-bfrs-local-invar-witnessing))

     (defthm gl-object-mark-bfrs-local-invar-of-append
       (iff (gl-object-mark-bfrs-local-invar (append x y) seen)
            (and (gl-object-mark-bfrs-local-invar x seen)
                 (gl-object-mark-bfrs-local-invar y seen)))
       :hints ((acl2::witness :ruleset mark-bfrs-witness-rules)))

     (defthm gl-object-mark-bfrs-local-invar-no-subobjs
       (gl-object-mark-bfrs-local-invar nil seen)
       :hints ((acl2::witness :ruleset mark-bfrs-witness-rules)))

     (defthmd gl-object-fix-when-equal-gl-object-fix
       (implies (equal a (gl-object-fix b))
                (equal (gl-object-fix a) a)))

     (defthm gl-object-mark-bfrs-local-invar-of-cons
       (implies (syntaxp (not (equal b ''nil)))
                (iff (gl-object-mark-bfrs-local-invar (cons a b) seen)
                     (and (gl-object-mark-bfrs-local-invar (list a) seen)
                          (gl-object-mark-bfrs-local-invar b seen))))
       :hints (("goal" :in-theory (enable gl-object-fix-when-equal-gl-object-fix))
               (acl2::witness :ruleset mark-bfrs-witness-rules)))

     (in-theory (disable acl2::member-of-cons
                         member-equal
                         acl2::commutativity-of-append-under-set-equiv
                         acl2::commutativity-2-of-append-under-set-equiv))


     (defthm gl-object-mark-bfrs-local-invar-of-nil
       (gl-object-mark-bfrs-local-invar x nil)
       :hints ((acl2::witness)))

     (acl2::defquant gl-object-mark-bfrs-seen-contents (new-seen seen subobjs)
       (forall y
               (implies (gl-object-p y)
                        (iff (hons-assoc-equal y new-seen)
                             (or (and (member y subobjs)
                                      (not (gl-object-case y '(:g-var :g-concrete :g-boolean))))
                                 (hons-assoc-equal y seen)))))
       :rewrite :direct)

     (acl2::defexample gl-object-mark-bfrs-seen-contents-example
       :pattern (hons-assoc-equal y new-seen)
       :templates (y)
       :instance-rulename gl-object-mark-bfrs-seen-contents-instancing)


     (acl2::def-witness-ruleset mark-bfrs-witness-rules2
       '(gl-object-mark-bfrs-seen-contents-witnessing
         gl-object-mark-bfrs-seen-contents-instancing
         gl-object-mark-bfrs-seen-contents-example
         gl-objectlist-mark-bfrs-seen-contents-witnessing
         mark-bfrs-witness-rules))

     (in-theory (disable not
                         (:t hons-assoc-equal)))


     (defcong set-equiv equal (gl-object-mark-bfrs-seen-contents new-seen seen subobjs) 3
       :hints ((acl2::witness :ruleset mark-bfrs-witness-rules2)))


     (defthmd member-gl-objectlist-p-when-not-gl-object-p
       (implies (and (not (gl-object-p y))
                     (gl-objectlist-p x))
                (not (member y x)))
       :hints(("Goal" :in-theory (enable gl-objectlist-p member))))

     (defthm gl-object-mark-bfrs-seen-contents-implies-invar
       (implies (and (gl-object-mark-bfrs-seen-contents new-seen seen subobjs)
                     (gl-objectlist-closed-downwards subobjs)
                     (gl-object-mark-bfrs-local-invar y seen))
                (gl-object-mark-bfrs-local-invar y new-seen))
       :hints ((acl2::witness)
               (and stable-under-simplificationp
                    '(:cases ((gl-object-p acl2::z0))
                      :in-theory (enable member-gl-objectlist-p-when-not-gl-object-p)))))

     (defthm gl-object-mark-bfrs-seen-contents-self
       (gl-object-mark-bfrs-seen-contents seen seen nil)
       :hints(("Goal" :in-theory (enable gl-object-mark-bfrs-seen-contents))))

     (defthm gl-object-mark-bfrs-seen-contents-of-append
       (implies (and (gl-object-mark-bfrs-seen-contents new-seen1 seen a)
                     (gl-object-mark-bfrs-seen-contents new-seen new-seen1 b))
                (gl-object-mark-bfrs-seen-contents new-seen seen (append a b)))
       :hints ((acl2::witness)))

     (defthm gl-object-mark-bfrs-local-invar-of-cons-non-member
       (implies (and (gl-object-mark-bfrs-local-invar subobjs seen)
                     (not (member z subobjs)))
                (gl-object-mark-bfrs-local-invar subobjs (cons (cons z val) seen)))
       :hints ((acl2::witness)))

     (defthmd member-when-equal-cons
       (implies (and (equal x (cons a b)))
                (iff (member y x)
                     (or (equal y a)
                         (member y b))))
       :hints(("Goal" :in-theory (enable member))))
     
     (defthm gl-object-mark-bfrs-seen-contents-of-cons
       (implies (and (not (gl-object-case x '(:g-var :g-concrete :g-boolean)))
                     (gl-object-mark-bfrs-seen-contents new-seen (cons (cons x t) seen) rest)
                     (equal (cons x rest) (gl-object-subobjects x)))
                (gl-object-mark-bfrs-seen-contents new-seen seen (cons x rest)))
       :hints ((acl2::witness)
               (and stable-under-simplificationp
                    '(:in-theory (enable member-when-equal-cons
                                         ;; member
                                         )))))

     (defthm gl-object-mark-bfrs-seen-contents-of-already-seen
       (implies (and (hons-assoc-equal (gl-object-fix x) seen)
                     (gl-object-mark-bfrs-local-invar (gl-object-subobjects x) seen))
                (gl-object-mark-bfrs-seen-contents seen seen (gl-object-subobjects x)))
       :hints ((acl2::witness)))
     
     (defthm gl-object-mark-bfrs-seen-contents-of-atomic
       (implies (and (gl-object-case x '(:g-var :g-concrete :g-boolean))
                     ;; (gl-object-p x)
                     )
                (gl-object-mark-bfrs-seen-contents seen seen (list x)))
       :hints ((acl2::witness)
               (and stable-under-simplificationp
                    '(:in-theory (enable member)))))


     (defret-mutual <fn>-new-seenlist-contents
       (defret <fn>-new-seenlist-contents
         (b* ((subobjs (gl-object-subobjects x)))
           (implies (gl-object-mark-bfrs-local-invar subobjs seen)
                    (and (gl-object-mark-bfrs-seen-contents new-seen seen subobjs))))
         :hints ('(:expand (<call>)))
         :fn gl-object-mark-bfrs)
       (defret <fn>-new-seenlist-contents
         (b* ((subobjs (gl-objectlist-subobjects x)))
           (implies (gl-object-mark-bfrs-local-invar subobjs seen)
                    (and (gl-object-mark-bfrs-seen-contents new-seen seen subobjs))))
         :hints ('(:expand (<call>)))
         :fn gl-objectlist-mark-bfrs)
       (defret <fn>-new-seenlist-contents
         (b* ((subobjs (gl-object-alist-subobjects x)))
           (implies (gl-object-mark-bfrs-local-invar subobjs seen)
                    (and (gl-object-mark-bfrs-seen-contents new-seen seen subobjs))))
         :hints ('(:expand (<call>)))
         :fn gl-object-alist-mark-bfrs))

     (defret <fn>-preserves-mark-bfrs-invar
       (implies (and (gl-object-mark-bfrs-local-invar (gl-object-subobjects x) seen)
                     (gl-object-mark-bfrs-local-invar y seen))
                (gl-object-mark-bfrs-local-invar y new-seen))
       :hints (("goal" :use gl-object-mark-bfrs-new-seenlist-contents
                :in-theory (disable gl-object-mark-bfrs-new-seenlist-contents)))
       :fn gl-object-mark-bfrs)

     (defret <fn>-preserves-mark-bfrs-invar
       (implies (and (gl-object-mark-bfrs-local-invar (gl-objectlist-subobjects x) seen)
                     (gl-object-mark-bfrs-local-invar y seen))
                (gl-object-mark-bfrs-local-invar y new-seen))
       :hints (("goal" :use gl-objectlist-mark-bfrs-new-seenlist-contents
                :in-theory (disable gl-objectlist-mark-bfrs-new-seenlist-contents)))
       :fn gl-objectlist-mark-bfrs)

     (defret <fn>-preserves-mark-bfrs-invar
       (implies (and (gl-object-mark-bfrs-local-invar (gl-object-alist-subobjects x) seen)
                     (gl-object-mark-bfrs-local-invar y seen))
                (gl-object-mark-bfrs-local-invar y new-seen))
       :hints (("goal" :use gl-object-alist-mark-bfrs-new-seenlist-contents
                :in-theory (disable gl-object-alist-mark-bfrs-new-seenlist-contents)))
       :fn gl-object-alist-mark-bfrs)


     
     

     ;; Z must be set in bitarr if some subobj not in seen has z as an immediate bfr.
     (acl2::defquant gl-object-mark-bfrs-bitarr-contents (subobjs seen bitarr)
       (forall (y z)
               (implies (and (member (gl-object-fix y) subobjs)
                             (not (hons-assoc-equal (gl-object-fix y) seen))
                             (not (gl-object-case y '(:g-var :g-concrete :g-boolean)))
                             (member z (gl-object-top-bfrlist y)))
                        (bfr-markedp z bitarr)))
       :rewrite :direct)


     (acl2::defexample gl-object-mark-bfrs-bitarr-contents-example
       :pattern (member z (gl-object-top-bfrlist y))
       :templates (y z)
       :instance-rulename gl-object-mark-bfrs-bitarr-contents-instancing)

     (defthm gl-object-mark-bfrs-bitarr-contents-of-nil
       (gl-object-mark-bfrs-bitarr-contents nil seen bitarr)
       :hints(("Goal" :in-theory (enable gl-object-mark-bfrs-bitarr-contents))))

     (defthm gl-object-mark-bfrs-bitarr-contents-of-append
       (iff (gl-object-mark-bfrs-bitarr-contents (append x y) seen bitarr)
            (and (gl-object-mark-bfrs-bitarr-contents x seen bitarr)
                 (gl-object-mark-bfrs-bitarr-contents y seen bitarr)))
       :hints ((acl2::witness)))

     (defthm gl-object-mark-bfrs-bitarr-contents-when-seen
       (implies (and (hons-assoc-equal (gl-object-fix x) seen)
                     (gl-object-mark-bfrs-local-invar (gl-object-subobjects x) seen))
                (gl-object-mark-bfrs-bitarr-contents (gl-object-subobjects x) seen bitarr))
       :hints ((acl2::witness)))

     (defthm gl-object-mark-bfrs-bitarr-contents-g-boolean
       (implies (gl-object-case x :g-boolean)
                (gl-object-mark-bfrs-bitarr-contents (list (gl-object-fix x)) seen
                                                     (bfr-mark (g-boolean->bool x) bitarr)))
       :hints (("goal" :in-theory (enable acl2::member-of-cons))
               (acl2::witness)))

     (defthm gl-object-mark-bfrs-bitarr-contents-atomic
       (implies (gl-object-case x '(:g-var :g-concrete))
                (gl-object-mark-bfrs-bitarr-contents (list (gl-object-fix x)) seen bitarr))
       :hints (("goal" :in-theory (enable acl2::member-of-cons))
               (acl2::witness)))

     ;; (defthm gl-object-mark-bfrs-bitarr-contents-of-cons
     ;;   (implies (syntaxp (not (equal y ''nil)))
     ;;            (iff (gl-object-mark-bfrs-bitarr-contents (cons x y) seen bitarr)
     ;;                 (and (gl-object-mark-bfrs-bitarr-contents (list x) seen bitarr)
     ;;                      (gl-object-mark-bfrs-bitarr-contents y seen bitarr))))
     ;;   :hints ((acl2::witness)
     ;;           (and stable-under-simplificationp
     ;;                '(:in-theory (enable member)))))

     (def-updater-independence-thm gl-object-mark-bfrs-bitarr-contents-when-bitarr-subsetp
       (implies (and (gl-object-mark-bfrs-bitarr-contents x seen old)
                     (bitarr-subsetp old new))
                (gl-object-mark-bfrs-bitarr-contents x seen new))
       :hints ((acl2::witness)))

     (def-updater-independence-thm gl-object-mark-bfrs-bitarr-contents-backtrack
       (implies (and (gl-object-mark-bfrs-bitarr-contents x new-seen new)
                     (gl-object-mark-bfrs-bitarr-contents y seen old)
                     (gl-object-mark-bfrs-seen-contents new-seen seen y)
                     (bitarr-subsetp old new))
                (gl-object-mark-bfrs-bitarr-contents x seen new))
       :hints ((acl2::witness)))

     (def-updater-independence-thm gl-object-mark-bfrs-bitarr-contents-backtrack2
       (implies (and (gl-object-mark-bfrs-bitarr-contents x new-seen new)
                     (gl-object-mark-bfrs-bitarr-contents y seen2 old)
                     (gl-object-mark-bfrs-seen-contents new-seen seen2 y)
                     (gl-object-mark-bfrs-bitarr-contents yy seen oldold)
                     (gl-object-mark-bfrs-seen-contents seen2 seen yy)
                     (bitarr-subsetp old new)
                     (bitarr-subsetp oldold old))
                (gl-object-mark-bfrs-bitarr-contents x seen new))
       :hints ((acl2::witness)))

     
     (acl2::defexample gl-object-mark-bfrs-bitarr-contents-top-subobj-example
       :pattern (member z (gl-object-top-bfrlist y))
       :templates ((gl-object-subobj-containing-top-bfr y z) z)
       :instance-rulename gl-object-mark-bfrs-bitarr-contents-instancing)


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


     (defthm gl-object-mark-bfrs-bitarr-contents-of-cons
       (implies (and (gl-object-mark-bfrs-bitarr-contents rest (cons (cons x t) seen) bitarr)
                     (bfrs-markedp (gl-object-top-bfrlist x) bitarr)
                     (equal (cons x rest) (gl-object-subobjects x)))
                (gl-object-mark-bfrs-bitarr-contents (cons x rest) seen bitarr))
       :hints (("goal" :in-theory (enable member-when-equal-cons))
               (acl2::witness))
       :otf-flg t)

     (defret <fn>-bitarr-contains-top-bfrlist1
       (bfrs-markedp (gl-object-top-bfrlist1 x) new-bitarr)
       :hints(("Goal" :in-theory (enable gl-object-top-bfrlist1
                                         bfrs-markedp
                                         acl2::member-of-cons)
               :expand (<call>)))
       :fn gl-object-mark-bfrs)

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
         (bfrs-markedp (gl-objectlist-top-bfrlist1 x) new-bitarr)
         :hints('(:in-theory (e/d (gl-objectlist-top-bfrlist1))
                  :expand (<call>)))
         :fn gl-objectlist-mark-bfrs)

       (defret <fn>-bitarr-contains-top-bfrlist1
         (bfrs-markedp (gl-object-alist-top-bfrlist1 x) new-bitarr)
         :hints('(:in-theory (e/d (gl-object-alist-top-bfrlist1))
                  :expand (<call>)))
         :fn gl-object-alist-mark-bfrs)
       :skip-others t)

     (defret <fn>-bitarr-contains-top-bfrlist
       (implies (not (hons-assoc-equal (gl-object-fix x) seen))
                (bfrs-markedp (gl-object-top-bfrlist x) new-bitarr))
       :hints(("Goal" :in-theory (enable gl-object-top-bfrlist)
               :expand (<call>))
              (and stable-under-simplificationp
                   '(:in-theory (enable bfrs-markedp
                                        acl2::member-of-cons))))
       :fn gl-object-mark-bfrs)

     (def-updater-independence-thm bitarr-subsetp-trans-rw
       (implies (and (bitarr-subsetp oldold old)
                     (bitarr-subsetp old new))
                (bitarr-subsetp oldold new))
       :hints ((acl2::witness)))

     (include-book "tools/trivial-ancestors-check" :dir :system)
     (acl2::use-trivial-ancestors-check)


     (defret-mutual <fn>-bitarr-contents-correct
       (defret <fn>-bitarr-contents-correct
         (b* ((subobjs (gl-object-subobjects x)))
           (implies (gl-object-mark-bfrs-local-invar subobjs seen)
                    (gl-object-mark-bfrs-bitarr-contents subobjs seen new-bitarr)))
         :hints ('(:expand (<call>)
                   :use gl-object-mark-bfrs-bitarr-contains-top-bfrlist
                   :in-theory (disable gl-object-mark-bfrs-bitarr-contains-top-bfrlist)
                   :do-not-induct t))
         :fn gl-object-mark-bfrs)
       (defret <fn>-bitarr-contents-correct
         (b* ((subobjs (gl-objectlist-subobjects x)))
           (implies (gl-object-mark-bfrs-local-invar subobjs seen)
                    (gl-object-mark-bfrs-bitarr-contents subobjs seen new-bitarr)))
         :hints ('(:expand (<call>)))
         :fn gl-objectlist-mark-bfrs)
       (defret <fn>-bitarr-contents-correct
         (b* ((subobjs (gl-object-alist-subobjects x)))
           (implies (gl-object-mark-bfrs-local-invar subobjs seen)
                    (gl-object-mark-bfrs-bitarr-contents subobjs seen new-bitarr)))
         :hints ('(:expand (<call>)))
         :fn gl-object-alist-mark-bfrs))




     

     (acl2::defexample gl-object-mark-bfrs-seen-invar-example
       :pattern (member y (gl-object-subobjects x))
       :templates (x y)
       :instance-rulename gl-object-mark-bfrs-seen-invar-instancing)


     

     (defthm gl-object-mark-bfrs-seen-invar-implies-gl-object-mark-bfrs-local-invar
       (implies (and (gl-object-mark-bfrs-seen-invar seen)
                     (gl-objectlist-closed-downwards subobjs))
                (gl-object-mark-bfrs-local-invar subobjs seen))
       :hints ((acl2::witness)))

     (defthmd gl-object-p-when-member-of-gl-objectlist
       (implies (and (member y x)
                     (gl-objectlist-p x))
                (gl-object-p y))
       :hints(("Goal" :in-theory (enable member gl-objectlist-p))))

     (defthm gl-object-mark-bfrs-seen-contents-preserves-seen-invar
       (implies (and (gl-object-mark-bfrs-seen-invar seen)
                     (gl-object-mark-bfrs-seen-contents new seen subobjs)
                     (gl-objectlist-closed-downwards subobjs))
                (gl-object-mark-bfrs-seen-invar new))
       :hints ((acl2::witness)
               (and stable-under-simplificationp
                    '(:in-theory (enable gl-object-p-when-member-of-gl-objectlist)))))
     
     




     (acl2::defexample gl-object-mark-bfrs-bitarr-invar-example
       :pattern (member bfr (gl-object-bfrlist obj))
       :templates (obj bfr)
       :instance-rulename gl-object-mark-bfrs-bitarr-invar-instancing)

     

     
     (acl2::defexample gl-object-mark-bfrs-bitarr-contents-bfr-at-top-example
       :pattern (member bfr (gl-object-bfrlist obj))
       :templates ((gl-object-subobj-containing-bfr-at-top obj bfr) bfr)
       :instance-rulename gl-object-mark-bfrs-bitarr-contents-instancing)

     
     (acl2::defexample gl-objectlist-closed-downwards-bfr-at-top-example
       :pattern (member z (gl-object-bfrlist y))
       :templates (y (gl-object-subobj-containing-bfr-at-top y z))
       :instance-rulename gl-objectlist-closed-downwards-instancing)

     
     (acl2::defexample gl-object-mark-bfrs-bitarr-invar-bfr-at-top-example
       :pattern (member bfr (gl-object-bfrlist obj))
       :templates ((gl-object-subobj-containing-bfr-at-top obj bfr) bfr)
       :instance-rulename gl-object-mark-bfrs-bitarr-invar-instancing)


     (defthm member-bfrlist-of-gl-object-subobj-containing-bfr-at-top
       (implies (member bfr (gl-object-bfrlist obj))
                (member bfr (gl-object-bfrlist (gl-object-subobj-containing-bfr-at-top obj bfr))))
       :hints (("goal" :use ((:instance gl-object-subobj-containing-bfr-at-top-when-member-bfrs (x obj)))
                :in-theory (disable gl-object-subobj-containing-bfr-at-top-when-member-bfrs))))
     
     
     (defthm gl-object-mark-bfrs-bitarr-invar-preserved
       (implies (and (gl-object-mark-bfrs-seen-invar seen)
                     (gl-object-mark-bfrs-bitarr-invar seen bitarr)
                     (gl-object-mark-bfrs-bitarr-contents subobjs seen new-b)
                     (gl-object-mark-bfrs-seen-contents new-s seen subobjs)
                     (gl-objectlist-closed-downwards subobjs)
                     (bitarr-subsetp bitarr new-b))
                (gl-object-mark-bfrs-bitarr-invar new-s new-b))
       :hints ((acl2::Witness)
               (and stable-under-simplificationp
                    '(:in-theory (enable acl2::member-of-cons))))
       :otf-flg t)

     

     (defret <fn>-in-seen
       (implies (and (gl-object-mark-bfrs-seen-invar seen)
                     (not (hons-assoc-equal y seen))
                     (gl-object-p y)
                     (case-split (not (gl-object-case y '(:g-var :g-concrete :g-boolean)))))
                (iff (hons-assoc-equal y new-seen)
                     (member y (gl-object-subobjects x))))
       :hints (("goal" :use ((:instance gl-object-mark-bfrs-new-seenlist-contents))
                :in-theory (e/d (gl-object-mark-bfrs-seen-contents-necc)
                                (gl-object-mark-bfrs-new-seenlist-contents))))
       :fn gl-object-mark-bfrs)

     (defthm gl-object-mark-bfrs-seen-invar-of-nil
       (gl-object-mark-bfrs-seen-invar nil)
       :hints(("Goal" :in-theory (enable gl-object-mark-bfrs-seen-invar))))

     (defret <fn>-preserves-seen-invar
       (implies (gl-object-mark-bfrs-seen-invar seen)
                (gl-object-mark-bfrs-seen-invar new-seen))
       :hints (("goal" :use ((:instance gl-object-mark-bfrs-seen-contents-preserves-seen-invar
                              (new new-seen)
                              (subobjs (gl-object-subobjects x))))
                :in-theory (disable gl-object-mark-bfrs-seen-contents-preserves-seen-invar)))
       :fn gl-object-mark-bfrs)

     (defret <fn>-preserves-seen-invar
       (implies (gl-object-mark-bfrs-seen-invar seen)
                (gl-object-mark-bfrs-seen-invar new-seen))
       :hints (("goal" :use ((:instance gl-object-mark-bfrs-seen-contents-preserves-seen-invar
                              (new new-seen)
                              (subobjs (gl-objectlist-subobjects x))))
                :in-theory (disable gl-object-mark-bfrs-seen-contents-preserves-seen-invar)))
       :fn gl-objectlist-mark-bfrs)

     (defret <fn>-preserves-seen-invar
       (implies (gl-object-mark-bfrs-seen-invar seen)
                (gl-object-mark-bfrs-seen-invar new-seen))
       :hints (("goal" :use ((:instance gl-object-mark-bfrs-seen-contents-preserves-seen-invar
                              (new new-seen)
                              (subobjs (gl-object-alist-subobjects x))))
                :in-theory (disable gl-object-mark-bfrs-seen-contents-preserves-seen-invar)))
       :fn gl-object-alist-mark-bfrs)

     (defthm gl-object-mark-bfrs-bitarr-invar-empty
       (gl-object-mark-bfrs-bitarr-invar nil bitarr)
       :hints(("Goal" :in-theory (enable gl-object-mark-bfrs-bitarr-invar))))

     (defret <fn>-preserves-bitarr-invar
       (implies (and (gl-object-mark-bfrs-seen-invar seen)
                     (gl-object-mark-bfrs-bitarr-invar seen bitarr))
                (gl-object-mark-bfrs-bitarr-invar new-seen new-bitarr))
       :hints (("goal" :use ((:instance gl-object-mark-bfrs-bitarr-invar-preserved
                              (new-s new-seen)
                              (new-b new-bitarr)
                              (subobjs (gl-object-subobjects x))))
                :in-theory (disable gl-object-mark-bfrs-bitarr-invar-preserved)))
       :fn gl-object-mark-bfrs)

     (defret <fn>-preserves-bitarr-invar
       (implies (and (gl-object-mark-bfrs-seen-invar seen)
                     (gl-object-mark-bfrs-bitarr-invar seen bitarr))
                (gl-object-mark-bfrs-bitarr-invar new-seen new-bitarr))
       :hints (("goal" :use ((:instance gl-object-mark-bfrs-bitarr-invar-preserved
                              (new-s new-seen)
                              (new-b new-bitarr)
                              (subobjs (gl-objectlist-subobjects x))))
                :in-theory (disable gl-object-mark-bfrs-bitarr-invar-preserved)))
       :fn gl-objectlist-mark-bfrs)

     (defret <fn>-preserves-bitarr-invar
       (implies (and (gl-object-mark-bfrs-seen-invar seen)
                     (gl-object-mark-bfrs-bitarr-invar seen bitarr))
                (gl-object-mark-bfrs-bitarr-invar new-seen new-bitarr))
       :hints (("goal" :use ((:instance gl-object-mark-bfrs-bitarr-invar-preserved
                              (new-s new-seen)
                              (new-b new-bitarr)
                              (subobjs (gl-object-alist-subobjects x))))
                :in-theory (disable gl-object-mark-bfrs-bitarr-invar-preserved)))
       :fn gl-object-alist-mark-bfrs)
     
     (defret <fn>-ensures-bitarr-contains-bfrs
       (implies (and (gl-object-mark-bfrs-seen-invar seen)
                     (gl-object-mark-bfrs-bitarr-invar seen bitarr))
                (bfrs-markedp (gl-object-bfrlist x) new-bitarr))
       :hints (("goal" :use gl-object-mark-bfrs-preserves-bitarr-invar
                :in-theory (e/d (acl2::member-of-cons
                                 gl-object-bfrlist-when-g-boolean
                                 gl-object-bfrlist-when-g-concrete
                                 gl-object-bfrlist-when-g-var)
                                (gl-object-mark-bfrs-preserves-bitarr-invar)))
               (acl2::witness))
       :fn gl-object-mark-bfrs)

     (defret-mutual <fn>-ensures-bitarr-contains-bfrs
       (defret <fn>-ensures-bitarr-contains-bfrs
         (implies (and (gl-object-mark-bfrs-seen-invar seen)
                       (gl-object-mark-bfrs-bitarr-invar seen bitarr))
                  (bfrs-markedp (gl-objectlist-bfrlist x) new-bitarr))
         :hints ('(:expand (<call>
                            (gl-objectlist-bfrlist x))))
         :fn gl-objectlist-mark-bfrs)
       (defret <fn>-ensures-bitarr-contains-bfrs
         (implies (and (gl-object-mark-bfrs-seen-invar seen)
                       (gl-object-mark-bfrs-bitarr-invar seen bitarr))
                  (bfrs-markedp (gl-object-alist-bfrlist x) new-bitarr))
         :hints ('(:expand (<call>
                            (gl-object-alist-bfrlist x))))
         :fn gl-object-alist-mark-bfrs)
       :skip-others t)))


  (local (in-theory (enable gl-object-mark-bfrs-invar)))

  (defthm gl-object-mark-bfrs-invar-when-seen-empty
    (gl-object-mark-bfrs-invar nil bitarr))

  (def-updater-independence-thm gl-object-mark-bfrs-invar-of-mark-bitarr
    (implies (and (gl-object-mark-bfrs-invar seen old)
                  (bitarr-subsetp old new))
             (gl-object-mark-bfrs-invar seen new))
    :hints ((acl2::witness)))


  (defret <fn>-preserves-invar
    (implies (gl-object-mark-bfrs-invar seen bitarr)
             (gl-object-mark-bfrs-invar new-seen new-bitarr))
    :fn gl-object-mark-bfrs)

  (defret <fn>-preserves-invar
    (implies (gl-object-mark-bfrs-invar seen bitarr)
             (gl-object-mark-bfrs-invar new-seen new-bitarr))
    :fn gl-objectlist-mark-bfrs)

  (defret <fn>-preserves-invar
    (implies (gl-object-mark-bfrs-invar seen bitarr)
             (gl-object-mark-bfrs-invar new-seen new-bitarr))
    :fn gl-object-alist-mark-bfrs)


  (defret <fn>-marks-bfrs
    (implies (gl-object-mark-bfrs-invar seen bitarr)
             (bfrs-markedp (gl-object-bfrlist x) new-bitarr))
    :fn gl-object-mark-bfrs)

  (defret <fn>-marks-bfrs
    (implies (gl-object-mark-bfrs-invar seen bitarr)
             (bfrs-markedp (gl-objectlist-bfrlist x) new-bitarr))
    :fn gl-objectlist-mark-bfrs)

  (defret <fn>-marks-bfrs
    (implies (gl-object-mark-bfrs-invar seen bitarr)
             (bfrs-markedp (gl-object-alist-bfrlist x) new-bitarr))
    :fn gl-object-alist-mark-bfrs))
    



