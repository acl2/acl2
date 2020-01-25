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

(include-book "logicman")
(include-book "centaur/aignet/count" :dir :system)
(include-book "def-fgl-rewrite")

;; note: redundant with mark-bfrs-base
(defstobj-clone bitarr aignet::bitarr :pkg fgl-fgl)

(define logicman-mark-gates ((x lbfr-p)
                              bitarr
                              logicman)
  :guard (and (lbfr-mode-is :aignet)
              (< (bfrstate->bound (logicman->bfrstate)) (bits-length bitarr)))
  :guard-hints (("goal" :in-theory (enable bfr-p)))
  :returns (new-bitarr)
  (b* ((lit (bfr->aignet-lit x (logicman->bfrstate))))
    (stobj-let ((aignet (logicman->aignet logicman)))
               (bitarr)
               (b* (((mv & bitarr) (aignet::count-gates-mark-rec (satlink::lit->var lit) bitarr aignet)))
                 bitarr)
               bitarr))
  ///
  (defret length-of-<fn>
    (implies (and (lbfr-p x)
                  (lbfr-mode-is :aignet)
                  (< (bfrstate->bound (logicman->bfrstate)) (len bitarr)))
             (equal (len new-bitarr) (len bitarr)))
    :hints(("Goal" :in-theory (enable bfr-p bfr->aignet-lit)))))

(define logicman-mark-gates-list ((x lbfr-listp)
                                   bitarr
                                   logicman)
  :guard (and (lbfr-mode-is :aignet)
              (< (bfrstate->bound (logicman->bfrstate)) (bits-length bitarr)))
  :guard-hints (("goal" :in-theory (enable bfr-p)))
  :returns (new-bitarr)
  (if (atom x)
      bitarr
    (b* ((bitarr (logicman-mark-gates (car x) bitarr logicman)))
      (logicman-mark-gates-list (cdr x) bitarr logicman)))
  ///
  (defret length-of-<fn>
    (implies (and (lbfr-listp x)
                  (lbfr-mode-is :aignet)
                  (< (bfrstate->bound (logicman->bfrstate)) (len bitarr)))
             (equal (len new-bitarr) (len bitarr)))
    :hints(("Goal" :in-theory (enable bfr-p bfr->aignet-lit)))))

(defines fgl-object-mark-gates
  (define fgl-object-mark-gates ((x fgl-object-p)
                                  bitarr
                                  logicman
                                  seen)
    :guard (and (lbfr-listp (fgl-object-bfrlist x))
                (lbfr-mode-is :aignet)
                (< (bfrstate->bound (logicman->bfrstate)) (bits-length bitarr)))
    :verify-guards nil
    :measure (acl2::two-nats-measure (fgl-object-count x) 0)
    :returns (mv new-bitarr new-seen)
    (fgl-object-case x
      :g-concrete (mv bitarr seen)
      :g-var (mv bitarr seen)
      :g-boolean (b* ((bitarr (logicman-mark-gates x.bool bitarr logicman)))
                   (mv bitarr seen))
      :otherwise
      (b* ((x (fgl-object-fix x))
           ((when (hons-get x seen)) (mv bitarr seen))
           (seen (hons-acons x t seen)))
        (case acl2::x.kind
          (:g-integer (b* ((bitarr (logicman-mark-gates-list (g-integer->bits x) bitarr logicman)))
                        (mv bitarr seen)))
          (:g-ite (b* (((g-ite x))
                       ((mv bitarr seen) (fgl-object-mark-gates x.test bitarr logicman seen))
                       ((mv bitarr seen) (fgl-object-mark-gates x.then bitarr logicman seen)))
                    (fgl-object-mark-gates x.else bitarr logicman seen)))
          (:g-apply (fgl-objectlist-mark-gates (g-apply->args x) bitarr logicman seen))
          (:g-map (fgl-object-alist-mark-gates (g-map->alist x) bitarr logicman seen))
          (otherwise (b* (((g-cons x))
                          ((mv bitarr seen) (fgl-object-mark-gates x.car bitarr logicman seen)))
                       (fgl-object-mark-gates x.cdr bitarr logicman seen)))))))

  (define fgl-objectlist-mark-gates ((x fgl-objectlist-p)
                                     bitarr
                                     logicman
                                     seen)
    :guard (and (lbfr-listp (fgl-objectlist-bfrlist x))
                (lbfr-mode-is :aignet)
                (< (bfrstate->bound (logicman->bfrstate)) (bits-length bitarr)))
    :measure (acl2::two-nats-measure (fgl-objectlist-count x) 0)
    :returns (mv new-bitarr new-seen)
    (b* (((when (atom x))
          (mv bitarr seen))
         ((mv bitarr seen) (fgl-object-mark-gates (car x) bitarr logicman seen)))
      (fgl-objectlist-mark-gates (cdr x) bitarr logicman seen)))

  (define fgl-object-alist-mark-gates ((x fgl-object-alist-p)
                                       bitarr
                                       logicman
                                       seen)
    :guard (and (lbfr-listp (fgl-object-alist-bfrlist x))
                (lbfr-mode-is :aignet)
                (< (bfrstate->bound (logicman->bfrstate)) (bits-length bitarr)))
    :measure (acl2::two-nats-measure (fgl-object-alist-count x) (len x))
    :returns (mv new-bitarr new-seen)
    (b* (((when (atom x)) (mv bitarr seen))
         ((unless (mbt (consp (car x))))
          (fgl-object-alist-mark-gates (cdr x) bitarr logicman seen))
         ((mv bitarr seen) (fgl-object-mark-gates (cdar x) bitarr logicman seen)))
      (fgl-object-alist-mark-gates (cdr x) bitarr logicman seen)))
  ///

  ;; Basic properties...

  (defret-mutual length-of-<fn>
    (defret length-of-<fn>
      (implies (and (lbfr-listp (fgl-object-bfrlist x))
                    (lbfr-mode-is :aignet)
                    (< (bfrstate->bound (logicman->bfrstate)) (bits-length bitarr)))
               (equal (len new-bitarr) (len bitarr)))
      :hints ('(:expand (<call>
                         (fgl-object-bfrlist x))))
      :fn fgl-object-mark-gates)
    (defret length-of-<fn>
      (implies (and (lbfr-listp (fgl-objectlist-bfrlist x))
                    (lbfr-mode-is :aignet)
                    (< (bfrstate->bound (logicman->bfrstate)) (bits-length bitarr)))
               (equal (len new-bitarr) (len bitarr)))
      :hints ('(:expand (<call>
                         (fgl-objectlist-bfrlist x))))
      :fn fgl-objectlist-mark-gates)
    (defret length-of-<fn>
      (implies (and (lbfr-listp (fgl-object-alist-bfrlist x))
                    (lbfr-mode-is :aignet)
                    (< (bfrstate->bound (logicman->bfrstate)) (bits-length bitarr)))
               (equal (len new-bitarr) (len bitarr)))
      :hints ('(:expand (<call>
                         (fgl-object-alist-bfrlist x))))
      :fn fgl-object-alist-mark-gates))

  (verify-guards fgl-object-mark-gates
    :hints (("goal" :expand ((fgl-object-bfrlist x)
                             (fgl-object-alist-bfrlist x))))))

(define bitarr-count-aux ((n natp)
                          bitarr
                          (acc natp))
  :guard (<= n (bits-length bitarr))
  :measure (nfix (- (bits-length bitarr) (nfix n)))
  (if (mbe :logic (zp (- (bits-length bitarr) (nfix n)))
           :exec (eql (bits-length bitarr) n))
      (lnfix acc)
    (bitarr-count-aux (1+ (lnfix n)) bitarr
                      (+ (get-bit n bitarr) (lnfix acc))))
  ///
  (local (defthm nthcdr-of-nil
           (equal (nthcdr n nil) nil)))

  (local (defthm consp-of-nthcdr
           (equal (consp (nthcdr n x))
                  (< (nfix n) (len x)))))
  (local (defthm nthcdr-of-cdr
           (equal (nthcdr n (cdr x))
                  (cdr (nthcdr n x)))))

  (local (in-theory (enable car-of-nthcdr)))

  (defthm bitarr-count-aux-is-duplicity
    (equal (bitarr-count-aux n bitarr acc)
           (+ (nfix acc)
              (acl2::duplicity 1 (nthcdr n bitarr))))
    :hints(("Goal" 
            :induct (bitarr-count-aux n bitarr acc)
            :expand ((acl2::duplicity 1 (nthcdr n bitarr)))))))


(define bitarr-count (bitarr)
  :returns (count natp :rule-classes :type-prescription)
  (bitarr-count-aux 0 bitarr 0))


