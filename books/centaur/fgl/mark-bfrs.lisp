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

(include-book "mark-bfrs-base")
(include-book "stack-logic")
(include-book "bvar-db-bfrlist")
(include-book "constraint-db")
(local (std::add-default-post-define-hook :fix))

(defthm bfrs-markedp-of-nil
  (bfrs-markedp nil bitarr)
  :hints(("Goal" :in-theory (enable bfrs-markedp))))

(local
 (acl2::defexample bfrs-markedp-example
   :pattern (bfr-markedp bfr bitarr)
   :templates (bfr)
   :instance-rulename bfrs-markedp-instancing))

(defthm bfrs-markedp-of-append
  (iff (bfrs-markedp (append x y) bitarr)
       (and (bfrs-markedp x bitarr)
            (bfrs-markedp y bitarr)))
  :hints((acl2::witness)))

(defthm bfrs-markedp-of-cons
  (iff (bfrs-markedp (cons x y) bitarr)
       (and (bfr-markedp x bitarr)
            (bfrs-markedp y bitarr)))
  :hints((acl2::witness)))

(defthm bfrs-markedp-of-bfrlist-mark
  (bfrs-markedp x (bfrlist-mark x bitarr))
  :hints(("Goal" :in-theory (enable bfrlist-mark))
         (and stable-under-simplificationp
              '(:in-theory (enable bfrs-markedp)))))

(def-updater-independence-thm bfrs-markedp-when-bitarr-subsetp
  (implies (and (bfrs-markedp x old)
                (bitarr-subsetp old new))
           (bfrs-markedp x new))
  :hints ((acl2::witness)))

(def-updater-independence-thm bitarr-subsetp-trans-rw
  (implies (and (bitarr-subsetp oldold old)
                (bitarr-subsetp old new))
           (bitarr-subsetp oldold new))
  :hints ((acl2::witness)))


(defret bfrs-markedp-preserved-of-<fn>
  (implies (bfrs-markedp y bitarr)
           (bfrs-markedp y new-bitarr))
  :fn fgl-object-mark-bfrs)

(defret bfrs-markedp-preserved-of-<fn>
  (implies (bfrs-markedp y bitarr)
           (bfrs-markedp y new-bitarr))
  :fn fgl-objectlist-mark-bfrs)

(defret bfrs-markedp-preserved-of-<fn>
  (implies (bfrs-markedp y bitarr)
           (bfrs-markedp y new-bitarr))
  :fn fgl-object-alist-mark-bfrs)


(define fgl-object-bindings-mark-bfrs ((x fgl-object-bindings-p)
                                      bitarr
                                      seen)
  :prepwork ((local (defthm fgl-object-alist-p-when-fgl-object-bindings-p
                      (implies (fgl-object-bindings-p x)
                               (fgl-object-alist-p x))
                      :hints(("Goal" :in-theory (enable fgl-object-alist-p
                                                        fgl-object-bindings-p)))))

             (local (defthm fgl-object-bindings-bfrlist-in-terms-of-fgl-object-alist-bfrlist
                      (equal (fgl-object-bindings-bfrlist x)
                             (fgl-object-alist-bfrlist (fgl-object-bindings-fix x)))
                      :hints(("Goal" :in-theory (enable fgl-object-alist-bfrlist
                                                        fgl-object-bindings-bfrlist
                                                        fgl-object-bindings-fix))))))
  :guard (and (< 0 (bits-length bitarr))
              (bfr-listp (fgl-object-bindings-bfrlist x)
                         (bfrstate (bfrmode :aignet) (1- (bits-length bitarr)))))
  :returns (mv new-bitarr new-seen)
  (fgl-object-alist-mark-bfrs (fgl-object-bindings-fix x) bitarr seen)
  ///

  (defret length-of-<fn>
    (implies (bfr-listp (fgl-object-bindings-bfrlist x) (bfrstate (bfrmode :aignet) (1- (len bitarr))))
             (equal (len new-bitarr) (len bitarr))))

  (defret length-of-<fn>-incr
    (>= (len new-bitarr) (len bitarr))
    :rule-classes :linear)

  (defret bfr-markedp-preserved-of-<fn>
    (implies (bfr-markedp y bitarr)
             (bfr-markedp y new-bitarr)))

  (defret bitarr-subsetp-of-<fn>
    (bitarr-subsetp bitarr new-bitarr))

  (defret bfrs-markedp-preserved-of-<fn>
    (implies (bfrs-markedp y bitarr)
             (bfrs-markedp y new-bitarr)))

  (defret <fn>-preserves-invar
    (implies (fgl-object-mark-bfrs-invar seen bitarr)
             (fgl-object-mark-bfrs-invar new-seen new-bitarr)))

  (defret <fn>-marks-bfrs
    (implies (fgl-object-mark-bfrs-invar seen bitarr)
             (bfrs-markedp (fgl-object-bindings-bfrlist x) new-bitarr))))

(define constraint-instance-mark-bfrs ((x constraint-instance-p) bitarr seen)
  :guard (and (< 0 (bits-length bitarr))
              (bfr-listp (constraint-instance-bfrlist x)
                         (bfrstate (bfrmode :aignet) (1- (bits-length bitarr)))))
  :prepwork ((local (in-theory (enable constraint-instance-bfrlist))))
  :returns (mv new-bitarr new-seen)
  (fgl-object-bindings-mark-bfrs (constraint-instance->subst x) bitarr seen)
  ///
  
  (defret length-of-<fn>
    (implies (bfr-listp (constraint-instance-bfrlist x) (bfrstate (bfrmode :aignet) (1- (len bitarr))))
             (equal (len new-bitarr) (len bitarr))))

  (defret length-of-<fn>-incr
    (>= (len new-bitarr) (len bitarr))
    :rule-classes :linear)

  (defret bfr-markedp-preserved-of-<fn>
    (implies (bfr-markedp y bitarr)
             (bfr-markedp y new-bitarr)))

  (defret bitarr-subsetp-of-<fn>
    (bitarr-subsetp bitarr new-bitarr))

  (defret bfrs-markedp-preserved-of-<fn>
    (implies (bfrs-markedp y bitarr)
             (bfrs-markedp y new-bitarr)))

  (defret <fn>-preserves-invar
    (implies (fgl-object-mark-bfrs-invar seen bitarr)
             (fgl-object-mark-bfrs-invar new-seen new-bitarr)))

  (defret <fn>-marks-bfrs
    (implies (fgl-object-mark-bfrs-invar seen bitarr)
             (bfrs-markedp (constraint-instance-bfrlist x) new-bitarr))))

(define constraint-instancelist-mark-bfrs ((x constraint-instancelist-p) bitarr seen)
  :guard (and (< 0 (bits-length bitarr))
              (bfr-listp (constraint-instancelist-bfrlist x)
                         (bfrstate (bfrmode :aignet) (1- (bits-length bitarr)))))
  :prepwork ((local (in-theory (enable constraint-instancelist-bfrlist))))
  :returns (mv new-bitarr new-seen)
  :verify-guards nil
  (b* (((when (atom x)) (mv bitarr seen))
       ((mv bitarr seen) (constraint-instance-mark-bfrs (car x) bitarr seen)))
    (constraint-instancelist-mark-bfrs (cdr x) bitarr seen))
  ///
  
  (defret length-of-<fn>
    (implies (bfr-listp (constraint-instancelist-bfrlist x) (bfrstate (bfrmode :aignet) (1- (len bitarr))))
             (equal (len new-bitarr) (len bitarr))))

  (verify-guards constraint-instancelist-mark-bfrs)

  (defret length-of-<fn>-incr
    (>= (len new-bitarr) (len bitarr))
    :rule-classes :linear)

  (defret bfr-markedp-preserved-of-<fn>
    (implies (bfr-markedp y bitarr)
             (bfr-markedp y new-bitarr)))

  (defret bitarr-subsetp-of-<fn>
    (bitarr-subsetp bitarr new-bitarr))

  (defret bfrs-markedp-preserved-of-<fn>
    (implies (bfrs-markedp y bitarr)
             (bfrs-markedp y new-bitarr)))

  (defret <fn>-preserves-invar
    (implies (fgl-object-mark-bfrs-invar seen bitarr)
             (fgl-object-mark-bfrs-invar new-seen new-bitarr)))

  (defret <fn>-marks-bfrs
    (implies (fgl-object-mark-bfrs-invar seen bitarr)
             (bfrs-markedp (constraint-instancelist-bfrlist x) new-bitarr))))


(define scratchobj-mark-bfrs ((x scratchobj-p) bitarr seen)
  :guard (and (< 0 (bits-length bitarr))
              (bfr-listp (scratchobj->bfrlist x)
                         (bfrstate (bfrmode :aignet) (1- (bits-length bitarr)))))
  :prepwork ((local (in-theory (e/d (scratchobj->bfrlist)
                                    (bfrlist-of-scratchobj-fgl-obj->val
                                     bfrlist-of-scratchobj-fgl-objlist->val
                                     bfrlist-of-scratchobj-bfr->val
                                     bfrlist-of-scratchobj-bfrlist->val
                                     bfrlist-of-scratchobj-cinst->val
                                     bfrlist-of-scratchobj-cinstlist->val)))))
  :returns (mv new-bitarr new-seen)
  :verify-guards nil
  (scratchobj-case x
    :fgl-obj (fgl-object-mark-bfrs x.val bitarr seen)
    :fgl-objlist (fgl-objectlist-mark-bfrs x.val bitarr seen)
    :bfr (b* ((bitarr (bfr-mark x.val bitarr))) (mv bitarr seen))
    :bfrlist (b* ((bitarr (bfrlist-mark x.val bitarr))) (mv bitarr seen))
    :cinst (constraint-instance-mark-bfrs x.val bitarr seen)
    :cinstlist (constraint-instancelist-mark-bfrs x.val bitarr seen))
  ///
  
  (defret length-of-<fn>
    (implies (bfr-listp (scratchobj->bfrlist x) (bfrstate (bfrmode :aignet) (1- (len bitarr))))
             (equal (len new-bitarr) (len bitarr))))

  (verify-guards scratchobj-mark-bfrs)

  (defret length-of-<fn>-incr
    (>= (len new-bitarr) (len bitarr))
    :rule-classes :linear)

  (defret bfr-markedp-preserved-of-<fn>
    (implies (bfr-markedp y bitarr)
             (bfr-markedp y new-bitarr)))

  (defret bitarr-subsetp-of-<fn>
    (bitarr-subsetp bitarr new-bitarr))

  (defret bfrs-markedp-preserved-of-<fn>
    (implies (bfrs-markedp y bitarr)
             (bfrs-markedp y new-bitarr)))

  (defret <fn>-preserves-invar
    (implies (fgl-object-mark-bfrs-invar seen bitarr)
             (fgl-object-mark-bfrs-invar new-seen new-bitarr)))

  (defret <fn>-marks-bfrs
    (implies (fgl-object-mark-bfrs-invar seen bitarr)
             (bfrs-markedp (scratchobj->bfrlist x) new-bitarr))))


(define scratchlist-mark-bfrs ((x scratchlist-p) bitarr seen)
  :guard (and (< 0 (bits-length bitarr))
              (bfr-listp (scratchlist-bfrlist x)
                         (bfrstate (bfrmode :aignet) (1- (bits-length bitarr)))))
  :prepwork ((local (in-theory (enable scratchlist-bfrlist))))
  :returns (mv new-bitarr new-seen)
  :verify-guards nil
  (b* (((when (atom x)) (mv bitarr seen))
       ((mv bitarr seen) (scratchobj-mark-bfrs (car x) bitarr seen)))
    (scratchlist-mark-bfrs (cdr x) bitarr seen))
  ///
  
  (defret length-of-<fn>
    (implies (bfr-listp (scratchlist-bfrlist x) (bfrstate (bfrmode :aignet) (1- (len bitarr))))
             (equal (len new-bitarr) (len bitarr))))

  (verify-guards scratchlist-mark-bfrs)

  (defret length-of-<fn>-incr
    (>= (len new-bitarr) (len bitarr))
    :rule-classes :linear)

  (defret bfr-markedp-preserved-of-<fn>
    (implies (bfr-markedp y bitarr)
             (bfr-markedp y new-bitarr)))

  (defret bitarr-subsetp-of-<fn>
    (bitarr-subsetp bitarr new-bitarr))

  (defret bfrs-markedp-preserved-of-<fn>
    (implies (bfrs-markedp y bitarr)
             (bfrs-markedp y new-bitarr)))

  (defret <fn>-preserves-invar
    (implies (fgl-object-mark-bfrs-invar seen bitarr)
             (fgl-object-mark-bfrs-invar new-seen new-bitarr)))

  (defret <fn>-marks-bfrs
    (implies (fgl-object-mark-bfrs-invar seen bitarr)
             (bfrs-markedp (scratchlist-bfrlist x) new-bitarr))))



(define minor-frame-mark-bfrs ((x minor-frame-p) bitarr seen)
  :guard (and (< 0 (bits-length bitarr))
              (bfr-listp (minor-frame-bfrlist x)
                         (bfrstate (bfrmode :aignet) (1- (bits-length bitarr)))))
  :prepwork ((local (in-theory (enable minor-frame-bfrlist))))
  :returns (mv new-bitarr new-seen)
  (b* (((minor-frame x))
       ((mv bitarr seen) (fgl-object-bindings-mark-bfrs x.bindings bitarr seen)))
    (scratchlist-mark-bfrs x.scratch bitarr seen))
  ///
  
  (defret length-of-<fn>
    (implies (bfr-listp (minor-frame-bfrlist x) (bfrstate (bfrmode :aignet) (1- (len bitarr))))
             (equal (len new-bitarr) (len bitarr))))

  (defret length-of-<fn>-incr
    (>= (len new-bitarr) (len bitarr))
    :rule-classes :linear)

  (defret bfr-markedp-preserved-of-<fn>
    (implies (bfr-markedp y bitarr)
             (bfr-markedp y new-bitarr)))

  (defret bitarr-subsetp-of-<fn>
    (bitarr-subsetp bitarr new-bitarr))

  (defret bfrs-markedp-preserved-of-<fn>
    (implies (bfrs-markedp y bitarr)
             (bfrs-markedp y new-bitarr)))

  (defret <fn>-preserves-invar
    (implies (fgl-object-mark-bfrs-invar seen bitarr)
             (fgl-object-mark-bfrs-invar new-seen new-bitarr)))

  (defret <fn>-marks-bfrs
    (implies (fgl-object-mark-bfrs-invar seen bitarr)
             (bfrs-markedp (minor-frame-bfrlist x) new-bitarr))))


(define minor-stack-mark-bfrs ((x minor-stack-p) bitarr seen)
  :guard (and (< 0 (bits-length bitarr))
              (bfr-listp (minor-stack-bfrlist x)
                         (bfrstate (bfrmode :aignet) (1- (bits-length bitarr)))))
  :prepwork ((local (in-theory (enable minor-stack-bfrlist))))
  :returns (mv new-bitarr new-seen)
  :verify-guards nil
  (b* (((mv bitarr seen) (minor-frame-mark-bfrs (car x) bitarr seen))
       ((when (atom (cdr x))) (mv bitarr seen)))
    (minor-stack-mark-bfrs (cdr x) bitarr seen))
  ///
  
  (defret length-of-<fn>
    (implies (bfr-listp (minor-stack-bfrlist x) (bfrstate (bfrmode :aignet) (1- (len bitarr))))
             (equal (len new-bitarr) (len bitarr))))

  (verify-guards minor-stack-mark-bfrs)

  (defret length-of-<fn>-incr
    (>= (len new-bitarr) (len bitarr))
    :rule-classes :linear)

  (defret bfr-markedp-preserved-of-<fn>
    (implies (bfr-markedp y bitarr)
             (bfr-markedp y new-bitarr)))

  (defret bitarr-subsetp-of-<fn>
    (bitarr-subsetp bitarr new-bitarr))

  (defret bfrs-markedp-preserved-of-<fn>
    (implies (bfrs-markedp y bitarr)
             (bfrs-markedp y new-bitarr)))

  (defret <fn>-preserves-invar
    (implies (fgl-object-mark-bfrs-invar seen bitarr)
             (fgl-object-mark-bfrs-invar new-seen new-bitarr)))

  (defret <fn>-marks-bfrs
    (implies (fgl-object-mark-bfrs-invar seen bitarr)
             (bfrs-markedp (minor-stack-bfrlist x) new-bitarr))))


(define major-frame-mark-bfrs ((x major-frame-p) bitarr seen)
  :guard (and (< 0 (bits-length bitarr))
              (bfr-listp (major-frame-bfrlist x)
                         (bfrstate (bfrmode :aignet) (1- (bits-length bitarr)))))
  :prepwork ((local (in-theory (enable major-frame-bfrlist))))
  :returns (mv new-bitarr new-seen)
  (b* (((major-frame x))
       ((mv bitarr seen) (fgl-object-bindings-mark-bfrs x.bindings bitarr seen)))
    (minor-stack-mark-bfrs x.minor-stack bitarr seen))
  ///
  
  (defret length-of-<fn>
    (implies (bfr-listp (major-frame-bfrlist x) (bfrstate (bfrmode :aignet) (1- (len bitarr))))
             (equal (len new-bitarr) (len bitarr))))

  (defret length-of-<fn>-incr
    (>= (len new-bitarr) (len bitarr))
    :rule-classes :linear)

  (defret bfr-markedp-preserved-of-<fn>
    (implies (bfr-markedp y bitarr)
             (bfr-markedp y new-bitarr)))

  (defret bitarr-subsetp-of-<fn>
    (bitarr-subsetp bitarr new-bitarr))

  (defret bfrs-markedp-preserved-of-<fn>
    (implies (bfrs-markedp y bitarr)
             (bfrs-markedp y new-bitarr)))

  (defret <fn>-preserves-invar
    (implies (fgl-object-mark-bfrs-invar seen bitarr)
             (fgl-object-mark-bfrs-invar new-seen new-bitarr)))

  (defret <fn>-marks-bfrs
    (implies (fgl-object-mark-bfrs-invar seen bitarr)
             (bfrs-markedp (major-frame-bfrlist x) new-bitarr))))


(define major-stack-mark-bfrs ((x major-stack-p) bitarr seen)
  :guard (and (< 0 (bits-length bitarr))
              (bfr-listp (major-stack-bfrlist x)
                         (bfrstate (bfrmode :aignet) (1- (bits-length bitarr)))))
  :prepwork ((local (in-theory (enable major-stack-bfrlist))))
  :returns (mv new-bitarr new-seen)
  :verify-guards nil
  (b* (((mv bitarr seen) (major-frame-mark-bfrs (car x) bitarr seen))
       ((when (atom (cdr x))) (mv bitarr seen)))
    (major-stack-mark-bfrs (cdr x) bitarr seen))
  ///
  
  (defret length-of-<fn>
    (implies (bfr-listp (major-stack-bfrlist x) (bfrstate (bfrmode :aignet) (1- (len bitarr))))
             (equal (len new-bitarr) (len bitarr))))

  (verify-guards major-stack-mark-bfrs)

  (defret length-of-<fn>-incr
    (>= (len new-bitarr) (len bitarr))
    :rule-classes :linear)

  (defret bfr-markedp-preserved-of-<fn>
    (implies (bfr-markedp y bitarr)
             (bfr-markedp y new-bitarr)))

  (defret bitarr-subsetp-of-<fn>
    (bitarr-subsetp bitarr new-bitarr))

  (defret bfrs-markedp-preserved-of-<fn>
    (implies (bfrs-markedp y bitarr)
             (bfrs-markedp y new-bitarr)))

  (defret <fn>-preserves-invar
    (implies (fgl-object-mark-bfrs-invar seen bitarr)
             (fgl-object-mark-bfrs-invar new-seen new-bitarr)))

  (defret <fn>-marks-bfrs
    (implies (fgl-object-mark-bfrs-invar seen bitarr)
             (bfrs-markedp (major-stack-bfrlist x) new-bitarr))))

(define bvar-db-mark-bfrs-aux ((n natp) bvar-db bitarr seen)
  :returns (mv new-bitarr new-seen)
  :measure (nfix (- (nfix n) (base-bvar bvar-db)))
  :guard (and (<= (base-bvar bvar-db) n)
              (<= n (next-bvar bvar-db))
              (< 0 (bits-length bitarr))
              (bfr-listp (bvar-db-bfrlist-aux n bvar-db)
                         (bfrstate (bfrmode :aignet) (1- (bits-length bitarr)))))
  :verify-guards nil
  :prepwork ((local (in-theory (enable bvar-db-bfrlist-aux))))
  (b* (((when (mbe :logic (zp (- (lnfix n) (base-bvar bvar-db)))
                   :exec (eql n (base-bvar bvar-db))))
        (mv bitarr seen))
       ((mv bitarr seen) (fgl-object-mark-bfrs
                          (get-bvar->term (1- (lnfix n)) bvar-db)
                          bitarr seen)))
    (bvar-db-mark-bfrs-aux (1- (lnfix n)) bvar-db bitarr seen))
  ///
  (defret length-of-<fn>
    (implies (bfr-listp (bvar-db-bfrlist-aux n bvar-db) (bfrstate (bfrmode :aignet) (1- (len bitarr))))
             (equal (len new-bitarr) (len bitarr))))

  (verify-guards bvar-db-mark-bfrs-aux)

  (defret length-of-<fn>-incr
    (>= (len new-bitarr) (len bitarr))
    :rule-classes :linear)

  (defret bfr-markedp-preserved-of-<fn>
    (implies (bfr-markedp y bitarr)
             (bfr-markedp y new-bitarr)))

  (defret bitarr-subsetp-of-<fn>
    (bitarr-subsetp bitarr new-bitarr))

  (defret bfrs-markedp-preserved-of-<fn>
    (implies (bfrs-markedp y bitarr)
             (bfrs-markedp y new-bitarr)))

  (defret <fn>-preserves-invar
    (implies (fgl-object-mark-bfrs-invar seen bitarr)
             (fgl-object-mark-bfrs-invar new-seen new-bitarr)))

  (defret <fn>-marks-bfrs
    (implies (fgl-object-mark-bfrs-invar seen bitarr)
             (bfrs-markedp (bvar-db-bfrlist-aux n bvar-db) new-bitarr))))


(define bvar-db-mark-bfrs (bvar-db bitarr seen)
  :returns (mv new-bitarr new-seen)
  :guard (and (< 0 (bits-length bitarr))
              (bfr-listp (bvar-db-bfrlist bvar-db)
                         (bfrstate (bfrmode :aignet) (1- (bits-length bitarr)))))
  :verify-guards nil
  :prepwork ((local (in-theory (enable bvar-db-bfrlist))))
  (bvar-db-mark-bfrs-aux (next-bvar bvar-db) bvar-db bitarr seen)
  ///
  (defret length-of-<fn>
    (implies (bfr-listp (bvar-db-bfrlist bvar-db) (bfrstate (bfrmode :aignet) (1- (len bitarr))))
             (equal (len new-bitarr) (len bitarr))))

  (verify-guards bvar-db-mark-bfrs)

  (defret length-of-<fn>-incr
    (>= (len new-bitarr) (len bitarr))
    :rule-classes :linear)

  (defret bfr-markedp-preserved-of-<fn>
    (implies (bfr-markedp y bitarr)
             (bfr-markedp y new-bitarr)))

  (defret bitarr-subsetp-of-<fn>
    (bitarr-subsetp bitarr new-bitarr))

  (defret bfrs-markedp-preserved-of-<fn>
    (implies (bfrs-markedp y bitarr)
             (bfrs-markedp y new-bitarr)))

  (defret <fn>-preserves-invar
    (implies (fgl-object-mark-bfrs-invar seen bitarr)
             (fgl-object-mark-bfrs-invar new-seen new-bitarr)))

  (defret <fn>-marks-bfrs
    (implies (fgl-object-mark-bfrs-invar seen bitarr)
             (bfrs-markedp (bvar-db-bfrlist bvar-db) new-bitarr))))



;; Skip the cgraph -- just reset it after we do a global transform.
;; (define cgraph-edge-mark-bfrs ((x cgraph-edge-p) bitarr seen)
;;   :returns (mv new-bitarr new-seen)
;;   :guard (and (< 0 (bits-length bitarr))
;;               (bfr-listp (cgraph-edge-bfrlist x)
;;                          (bfrstate (bfrmode :aignet) (1- (bits-length bitarr)))))
;;   :prepwork ((local (in-theory (enable cgraph-edge-bfrlist))))
;;   (fgl-object-bindings-mark-bfrs (cgraph-edge->subst x) bitarr seen)
;;   ///
  
;;   (defret length-of-<fn>
;;     (implies (bfr-listp (cgraph-edge-bfrlist x) (bfrstate (bfrmode :aignet) (1- (len bitarr))))
;;              (equal (len new-bitarr) (len bitarr))))

;;   (verify-guards cgraph-edge-mark-bfrs)

;;   (defret length-of-<fn>-incr
;;     (>= (len new-bitarr) (len bitarr))
;;     :rule-classes :linear)

;;   (defret bfr-markedp-preserved-of-<fn>
;;     (implies (bfr-markedp y bitarr)
;;              (bfr-markedp y new-bitarr)))

;;   (defret bitarr-subsetp-of-<fn>
;;     (bitarr-subsetp bitarr new-bitarr))

;;   (defret <fn>-preserves-invar
;;     (implies (fgl-object-mark-bfrs-invar seen bitarr)
;;              (fgl-object-mark-bfrs-invar new-seen new-bitarr)))

;;   (defret <fn>-marks-bfrs
;;     (implies (fgl-object-mark-bfrs-invar seen bitarr)
;;              (bfrs-markedp (cgraph-edge-bfrlist x) new-bitarr))))


;; (define cgraph-edgelist-mark-bfrs ((x cgraph-edgelist-p) bitarr seen)
;;   :returns (mv new-bitarr new-seen)
;;   :guard (and (< 0 (bits-length bitarr))
;;               (bfr-listp (cgraph-edgelist-bfrlist x)
;;                          (bfrstate (bfrmode :aignet) (1- (bits-length bitarr)))))
;;   :prepwork ((local (in-theory (enable cgraph-edgelist-bfrlist
;;                                        cgraph-edge-mark-bfrs))))
;;   (b* (((when (atom x)) (mv bitarr seen))
;;        ((mv bitarr seen) (cgraph-edge-mark-bfrs (car x) bitarr seen)))
;;     (cgraph-edgelist-mark-bfrs (cdr x) bitarr seen))
    
;;   ///
  
;;   (defret length-of-<fn>
;;     (implies (bfr-listp (cgraph-edgelist-bfrlist x) (bfrstate (bfrmode :aignet) (1- (len bitarr))))
;;              (equal (len new-bitarr) (len bitarr))))

;;   (verify-guards cgraph-edgelist-mark-bfrs)

;;   (defret length-of-<fn>-incr
;;     (>= (len new-bitarr) (len bitarr))
;;     :rule-classes :linear)

;;   (defret bfr-markedp-preserved-of-<fn>
;;     (implies (bfr-markedp y bitarr)
;;              (bfr-markedp y new-bitarr)))

;;   (defret bitarr-subsetp-of-<fn>
;;     (bitarr-subsetp bitarr new-bitarr))

;;   (defret <fn>-preserves-invar
;;     (implies (fgl-object-mark-bfrs-invar seen bitarr)
;;              (fgl-object-mark-bfrs-invar new-seen new-bitarr)))

;;   (defret <fn>-marks-bfrs
;;     (implies (fgl-object-mark-bfrs-invar seen bitarr)
;;              (bfrs-markedp (cgraph-edgelist-bfrlist x) new-bitarr))))

;; (define cgraph-mark-bfrs ((x cgraph-p) bitarr seen)
;;   :returns (mv new-bitarr new-seen)
;;   :guard (and (< 0 (bits-length bitarr))
;;               (bfr-listp (cgraph-bfrlist x)
;;                          (bfrstate (bfrmode :aignet) (1- (bits-length bitarr)))))
;;   :prepwork ((local (in-theory (enable cgraph-bfrlist))))
;;   (b* (((when (atom x)) (mv bitarr seen))
;;        ((unless (mbt (and (consp (car x))
;;                           (fgl-object-p (caar x)))))
;;         (cgraph-mark-bfrs (cdr x) bitarr seen))
;;        ((mv bitarr seen) (fgl-object-mark-bfrs (caar x) bitarr seen))
;;        ((mv bitarr seen) (cgraph-edgelist-mark-bfrs (cdar x) bitarr seen)))
;;     (cgraph-mark-bfrs (cdr x) bitarr seen))
    
;;   ///
  
;;   (defret length-of-<fn>
;;     (implies (bfr-listp (cgraph-bfrlist x) (bfrstate (bfrmode :aignet) (1- (len bitarr))))
;;              (equal (len new-bitarr) (len bitarr))))

;;   (verify-guards cgraph-mark-bfrs)

;;   (defret length-of-<fn>-incr
;;     (>= (len new-bitarr) (len bitarr))
;;     :rule-classes :linear)

;;   (defret bfr-markedp-preserved-of-<fn>
;;     (implies (bfr-markedp y bitarr)
;;              (bfr-markedp y new-bitarr)))

;;   (defret bitarr-subsetp-of-<fn>
;;     (bitarr-subsetp bitarr new-bitarr))

;;   (defret <fn>-preserves-invar
;;     (implies (fgl-object-mark-bfrs-invar seen bitarr)
;;              (fgl-object-mark-bfrs-invar new-seen new-bitarr)))

;;   (defret <fn>-marks-bfrs
;;     (implies (fgl-object-mark-bfrs-invar seen bitarr)
;;              (bfrs-markedp (cgraph-bfrlist x) new-bitarr))))





(define fgl-object-bindingslist-mark-bfrs ((x fgl-object-bindingslist-p) bitarr seen)
  :returns (mv new-bitarr new-seen)
  :guard (and (< 0 (bits-length bitarr))
              (bfr-listp (fgl-object-bindingslist-bfrlist x)
                         (bfrstate (bfrmode :aignet) (1- (bits-length bitarr)))))
  :prepwork ((local (in-theory (enable fgl-object-bindingslist-bfrlist))))
  (b* (((when (atom x))
        (mv bitarr seen))
       ((mv bitarr seen) (fgl-object-bindings-mark-bfrs (car x) bitarr seen)))
    (fgl-object-bindingslist-mark-bfrs (cdr x) bitarr seen))
    
  ///
  
  (defret length-of-<fn>
    (implies (bfr-listp (fgl-object-bindingslist-bfrlist x) (bfrstate (bfrmode :aignet) (1- (len bitarr))))
             (equal (len new-bitarr) (len bitarr))))

  (verify-guards fgl-object-bindingslist-mark-bfrs)

  (defret length-of-<fn>-incr
    (>= (len new-bitarr) (len bitarr))
    :rule-classes :linear)

  (defret bfr-markedp-preserved-of-<fn>
    (implies (bfr-markedp y bitarr)
             (bfr-markedp y new-bitarr)))

  (defret bitarr-subsetp-of-<fn>
    (bitarr-subsetp bitarr new-bitarr))

  (defret bfrs-markedp-preserved-of-<fn>
    (implies (bfrs-markedp y bitarr)
             (bfrs-markedp y new-bitarr)))

  (defret <fn>-preserves-invar
    (implies (fgl-object-mark-bfrs-invar seen bitarr)
             (fgl-object-mark-bfrs-invar new-seen new-bitarr)))

  (defret <fn>-marks-bfrs
    (implies (fgl-object-mark-bfrs-invar seen bitarr)
             (bfrs-markedp (fgl-object-bindingslist-bfrlist x) new-bitarr))))


(define sig-table-mark-bfrs ((x sig-table-p) bitarr seen)
  :returns (mv new-bitarr new-seen)
  :guard (and (< 0 (bits-length bitarr))
              (bfr-listp (sig-table-bfrlist x)
                         (bfrstate (bfrmode :aignet) (1- (bits-length bitarr)))))
  :prepwork ((local (in-theory (enable sig-table-bfrlist))))
  (b* (((when (atom x))
        (mv bitarr seen))
       ((unless (mbt (and (consp (car x))
                          (fgl-objectlist-p (caar x)))))
        (sig-table-mark-bfrs (cdr x) bitarr seen))
       ((mv bitarr seen) (fgl-objectlist-mark-bfrs (caar x) bitarr seen))
       ((mv bitarr seen) (fgl-object-bindingslist-mark-bfrs (cdar x) bitarr seen)))
    (sig-table-mark-bfrs (cdr x) bitarr seen))
    
  ///
  
  (defret length-of-<fn>
    (implies (bfr-listp (sig-table-bfrlist x) (bfrstate (bfrmode :aignet) (1- (len bitarr))))
             (equal (len new-bitarr) (len bitarr))))

  (verify-guards sig-table-mark-bfrs)

  (defret length-of-<fn>-incr
    (>= (len new-bitarr) (len bitarr))
    :rule-classes :linear)

  (defret bfr-markedp-preserved-of-<fn>
    (implies (bfr-markedp y bitarr)
             (bfr-markedp y new-bitarr)))

  (defret bitarr-subsetp-of-<fn>
    (bitarr-subsetp bitarr new-bitarr)
    :hints(("Goal" :in-theory (disable <fn>))
           (acl2::witness)))

  (defret bfrs-markedp-preserved-of-<fn>
    (implies (bfrs-markedp y bitarr)
             (bfrs-markedp y new-bitarr)))

  (defret <fn>-preserves-invar
    (implies (fgl-object-mark-bfrs-invar seen bitarr)
             (fgl-object-mark-bfrs-invar new-seen new-bitarr)))

  (defret <fn>-marks-bfrs
    (implies (fgl-object-mark-bfrs-invar seen bitarr)
             (bfrs-markedp (sig-table-bfrlist x) new-bitarr)))

  (local (in-theory (enable sig-table-fix))))


(define constraint-tuple-mark-bfrs ((x constraint-tuple-p) bitarr seen)
  :returns (mv new-bitarr new-seen)
  :guard (and (< 0 (bits-length bitarr))
              (bfr-listp (constraint-tuple-bfrlist x)
                         (bfrstate (bfrmode :aignet) (1- (bits-length bitarr)))))
  :prepwork ((local (in-theory (enable constraint-tuple-bfrlist))))
  (sig-table-mark-bfrs (constraint-tuple->sig-table x) bitarr seen)
  ///
  
  (defret length-of-<fn>
    (implies (bfr-listp (constraint-tuple-bfrlist x) (bfrstate (bfrmode :aignet) (1- (len bitarr))))
             (equal (len new-bitarr) (len bitarr))))

  (verify-guards constraint-tuple-mark-bfrs)

  (defret length-of-<fn>-incr
    (>= (len new-bitarr) (len bitarr))
    :rule-classes :linear)

  (defret bfr-markedp-preserved-of-<fn>
    (implies (bfr-markedp y bitarr)
             (bfr-markedp y new-bitarr)))

  (defret bitarr-subsetp-of-<fn>
    (bitarr-subsetp bitarr new-bitarr))

  (defret bfrs-markedp-preserved-of-<fn>
    (implies (bfrs-markedp y bitarr)
             (bfrs-markedp y new-bitarr)))

  (defret <fn>-preserves-invar
    (implies (fgl-object-mark-bfrs-invar seen bitarr)
             (fgl-object-mark-bfrs-invar new-seen new-bitarr)))

  (defret <fn>-marks-bfrs
    (implies (fgl-object-mark-bfrs-invar seen bitarr)
             (bfrs-markedp (constraint-tuple-bfrlist x) new-bitarr))))


(define constraint-tuplelist-mark-bfrs ((x constraint-tuplelist-p) bitarr seen)
  :returns (mv new-bitarr new-seen)
  :guard (and (< 0 (bits-length bitarr))
              (bfr-listp (constraint-tuplelist-bfrlist x)
                         (bfrstate (bfrmode :aignet) (1- (bits-length bitarr)))))
  :prepwork ((local (in-theory (enable constraint-tuplelist-bfrlist))))
  (b* (((when (atom x))
        (mv bitarr seen))
       ((mv bitarr seen) (constraint-tuple-mark-bfrs (car x) bitarr seen)))
    (constraint-tuplelist-mark-bfrs (cdr x) bitarr seen))
    
  ///
  
  (defret length-of-<fn>
    (implies (bfr-listp (constraint-tuplelist-bfrlist x) (bfrstate (bfrmode :aignet) (1- (len bitarr))))
             (equal (len new-bitarr) (len bitarr))))

  (verify-guards constraint-tuplelist-mark-bfrs)

  (defret length-of-<fn>-incr
    (>= (len new-bitarr) (len bitarr))
    :rule-classes :linear)

  (defret bfr-markedp-preserved-of-<fn>
    (implies (bfr-markedp y bitarr)
             (bfr-markedp y new-bitarr)))

  (defret bitarr-subsetp-of-<fn>
    (bitarr-subsetp bitarr new-bitarr))

  (defret bfrs-markedp-preserved-of-<fn>
    (implies (bfrs-markedp y bitarr)
             (bfrs-markedp y new-bitarr)))

  (defret <fn>-preserves-invar
    (implies (fgl-object-mark-bfrs-invar seen bitarr)
             (fgl-object-mark-bfrs-invar new-seen new-bitarr)))

  (defret <fn>-marks-bfrs
    (implies (fgl-object-mark-bfrs-invar seen bitarr)
             (bfrs-markedp (constraint-tuplelist-bfrlist x) new-bitarr))))


(define constraint-db-mark-bfrs ((x constraint-db-p) bitarr seen)
  :returns (mv new-bitarr new-seen)
  :guard (and (< 0 (bits-length bitarr))
              (bfr-listp (constraint-db-bfrlist x)
                         (bfrstate (bfrmode :aignet) (1- (bits-length bitarr)))))
  :prepwork ((local (in-theory (enable constraint-db-bfrlist))))
  (b* (((when (atom x))
        (mv bitarr seen))
       ((unless (mbt (and (consp (car x))
                          (pseudo-fnsym-p (caar x)))))
        (constraint-db-mark-bfrs (cdr x) bitarr seen))
       ((mv bitarr seen) (constraint-tuplelist-mark-bfrs (cdar x) bitarr seen)))
    (constraint-db-mark-bfrs (cdr x) bitarr seen))
    
  ///
  
  (defret length-of-<fn>
    (implies (bfr-listp (constraint-db-bfrlist x) (bfrstate (bfrmode :aignet) (1- (len bitarr))))
             (equal (len new-bitarr) (len bitarr))))

  (verify-guards constraint-db-mark-bfrs)

  (defret length-of-<fn>-incr
    (>= (len new-bitarr) (len bitarr))
    :rule-classes :linear)

  (defret bfr-markedp-preserved-of-<fn>
    (implies (bfr-markedp y bitarr)
             (bfr-markedp y new-bitarr)))

  (defret bitarr-subsetp-of-<fn>
    (bitarr-subsetp bitarr new-bitarr)
    :hints(("Goal" :in-theory (disable <fn>))
           (acl2::witness)))

  (defret bfrs-markedp-preserved-of-<fn>
    (implies (bfrs-markedp y bitarr)
             (bfrs-markedp y new-bitarr)))

  (defret <fn>-preserves-invar
    (implies (fgl-object-mark-bfrs-invar seen bitarr)
             (fgl-object-mark-bfrs-invar new-seen new-bitarr)))

  (defret <fn>-marks-bfrs
    (implies (fgl-object-mark-bfrs-invar seen bitarr)
             (bfrs-markedp (constraint-db-bfrlist x) new-bitarr)))

  (local (in-theory (enable constraint-db-fix))))

