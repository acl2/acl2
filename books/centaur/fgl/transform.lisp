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

(include-book "stack-transform")
(include-book "pathcond-transform")
(include-book "mark-bfrs")
(include-book "mark-bfrs-pathcond")
(include-book "primitives-stub")
(include-book "stack-import")
(include-book "bvar-db-bfrlist")
(include-book "bvar-db-equivs")
(include-book "centaur/vl/util/cwtime" :dir :system)
(include-book "add-primitives")
(include-book "def-fgl-rewrite")
(local (include-book "std/lists/resize-list" :dir :system))
(local (std::add-default-post-define-hook :fix))


(defret ipasirs-assumption-free-of-<fn>
  (logicman-ipasirs-assumption-free new-logicman)
  :hints(("Goal" :in-theory (enable logicman-ipasirs-assumption-free
                                    <fn>)))
  :fn logicman-comb-transform)

(local
 (acl2::defexample bfrs-markedp-example
   :pattern (bfr-markedp bfr bitarr)
   :templates (bfr)
   :instance-rulename bfrs-markedp-instancing))

(defcong set-equiv equal (bfrs-markedp bfrs bitarr) 1
  :hints ((acl2::witness)))

(defcong set-equiv equal (bfr-litarr-p bfrs litarr bound) 1
  :hints(("Goal" :in-theory (enable set-equiv
                                    bfr-litarr-p-of-subset))))

(local
 (define bvar-db-bfrlist-alt ((n natp) (max natp) bvar-db)
   :verify-guards nil
   :measure (nfix (- (nfix max) (nfix n)))
   (if (zp (- (nfix max) (nfix n)))
       nil
     (append (fgl-object-bfrlist (get-bvar->term n bvar-db))
             (bvar-db-bfrlist-alt (1+ (lnfix n)) max bvar-db)))
   ///
   (defthmd bvar-db-bfrlist-aux-in-terms-of-decr-max
     (equal (bvar-db-bfrlist-alt n max bvar-db)
            (if (zp (- (nfix max) (nfix n)))
                nil
              (append (bvar-db-bfrlist-alt n (1- (lnfix max)) bvar-db)
                      (fgl-object-bfrlist (get-bvar->term (1- (lnfix max)) bvar-db)))))
     :rule-classes :definition)

   (defthmd bvar-db-bfrlist-aux-in-terms-of-alt
     (set-equiv (bvar-db-bfrlist-aux n bvar-db)
                (bvar-db-bfrlist-alt (base-bvar$a bvar-db) n bvar-db))
     :hints(("Goal" :in-theory (enable bvar-db-bfrlist-aux
                                       bvar-db-bfrlist-aux-in-terms-of-decr-max))))))


(define bvar-db-objectlist ((n natp) bvar-db)
  :returns (objs fgl-objectlist-p)
  :guard (and (<= n (next-bvar bvar-db))
              (<= (base-bvar bvar-db) n))
  :measure (nfix (- (next-bvar bvar-db) (nfix n)))
  (b* (((when (mbe :logic (zp (- (next-bvar bvar-db) (nfix n)))
                   :exec (eql n (next-bvar bvar-db))))
        nil))
    (cons (get-bvar->term n bvar-db)
          (bvar-db-objectlist (1+ (lnfix n)) bvar-db)))
  ///
  (local (defun nth-of-bvar-db-objectlist-ind (k n)
           (declare (xargs :measure (nfix k)))
           (if (zp k)
               n
             (nth-of-bvar-db-objectlist-ind (1- k) (1+ (lnfix n))))))
  (defret nth-of-<fn>
    (equal (nth k objs)
           (and (< (nfix k) (- (next-bvar bvar-db) (nfix n)))
                (get-bvar->term (+ (nfix k) (nfix n)) bvar-db)))
    :hints(("Goal" :in-theory (enable nth)
            :induct (nth-of-bvar-db-objectlist-ind k n)
            :expand (<call>))))

  (local (defretd fgl-objectlist-bfrlist-of-<fn>-in-terms-of-alt
           (equal (fgl-objectlist-bfrlist objs)
                  (bvar-db-bfrlist-alt n (next-bvar$a bvar-db) bvar-db))
           :hints(("Goal" :in-theory (enable bvar-db-bfrlist-alt)))))

  (defret fgl-objectlist-bfrlist-of-<fn>
    (set-equiv (fgl-objectlist-bfrlist (bvar-db-objectlist (base-bvar$a bvar-db) bvar-db))
               (bvar-db-bfrlist bvar-db))
    :hints(("Goal" :in-theory (enable bvar-db-bfrlist
                                      bvar-db-bfrlist-aux-in-terms-of-alt
                                      fgl-objectlist-bfrlist-of-<fn>-in-terms-of-alt))))


  (defret bfr-listp-of-<fn>
    (implies (and (bfr-listp (bvar-db-bfrlist bvar-db))
                  (<= (base-bvar bvar-db) (nfix n)))
             (bfr-listp (fgl-objectlist-bfrlist objs))))

  (defret len-of-<fn>
    (equal (len objs)
           (nfix (- (next-bvar bvar-db) (nfix n))))))

(define bvar-db-from-objectlist ((x fgl-objectlist-p) bvar-db state)
  :returns (new-bvar-db)
  (b* (((when (atom x))
        bvar-db)
       (nextvar (next-bvar bvar-db))
       (x1 (fgl-object-fix (car x)))
       (bvar-db (add-term-bvar x1 bvar-db))
       (bvar-db (maybe-add-equiv-term x1 nextvar bvar-db state)))
    (bvar-db-from-objectlist (cdr x) bvar-db state))
  ///
  (defret bvar-db-bfrlist-of-<fn>
    (implies (and (not (member v (bvar-db-bfrlist bvar-db)))
                  (not (member v (fgl-objectlist-bfrlist x))))
             (not (member v (bvar-db-bfrlist new-bvar-db)))))

  (defret next-bvar-of-<fn>
    (equal (next-bvar$a new-bvar-db)
           (+ (len x) (next-bvar$a bvar-db))))

  (defret base-bvar-of-<fn>
    (equal (base-bvar$a new-bvar-db)
           (base-bvar$a bvar-db)))

  (defret get-bvar->term-of-<fn>
    (equal (get-bvar->term$a n new-bvar-db)
           (cond ((and (<= (next-bvar$a bvar-db) (nfix n))
                       (< (nfix n) (+ (len x) (next-bvar$a bvar-db))))
                  (fgl-object-fix (nth (- (nfix n) (next-bvar$a bvar-db)) x)))
                 (t (get-bvar->term$a n bvar-db))))))




(defthm bvar-db-bfrlist-of-init-bvar-db
  (equal (bvar-db-bfrlist (init-bvar-db$a base-bvar bvar-db)) nil)
  :hints(("Goal" :in-theory (enable bvar-db-bfrlist bvar-db-bfrlist-aux))))





(local (in-theory (disable w)))

(define interp-st-global-transform (config interp-st state)
  :guard (and (interp-st-bfrs-ok interp-st)
              (bfr-mode-is :aignet (interp-st-bfr-mode)))
  :returns (mv contra new-interp-st new-state)
  :guard-hints ((and stable-under-simplificationp
                     '(:in-theory (enable interp-st-bfrs-ok)))
                (and stable-under-simplificationp
                     '(:in-theory (enable bfr-pathcond-p logicman->bfrstate))))

  :prepwork ((local (in-theory (disable member-equal remove
                                        acl2::member-equal-append
                                        acl2::member-of-append
                                        bfr-listp$-when-subsetp-equal
                                        bfr-listp$-of-cdr-when-bfr-listp$
                                        acl2::subsetp-member
                                        not
                                        acl2::member-when-atom
                                        acl2::consp-when-member-equal-of-atom-listp
                                        interp-st-bfrs-ok-implies
                                        bfrs-markedp-when-bitarr-subsetp
                                        nth len
                                        acl2::repeat-when-zp))))
  (time$
   (b* ((interp-st (update-interp-st->cgraph nil interp-st))
        (interp-st (update-interp-st->cgraph-memo nil interp-st))
        (interp-st (update-interp-st->cgraph-index 0 interp-st))

        ;; BOZO what should we do with fgarrays?
        (interp-st (resize-interp-st->fgarrays 0 interp-st))
        (interp-st (update-interp-st->next-fgarray 0 interp-st))

        (constraint-db (interp-st->constraint-db interp-st)))
     (stobj-let ((logicman (interp-st->logicman interp-st))
                 (bvar-db (interp-st->bvar-db interp-st))
                 (stack (interp-st->stack interp-st))
                 (pathcond (interp-st->pathcond interp-st))
                 (constraint-pathcond (interp-st->constraint interp-st)))
                (contra constraint-db logicman bvar-db stack pathcond constraint-pathcond state)
                (b* ((stack-obj (stack-extract stack))
                     (base-bvar (base-bvar bvar-db))
                     (bvar-db-objs (bvar-db-objectlist base-bvar bvar-db))
                     ((mv constraint-db stack-obj bvar-db-objs)
                      (mbe :logic (mv constraint-db stack-obj bvar-db-objs)
                           :exec (b* ((lst (hons-copy (list constraint-db stack-obj bvar-db-objs))))
                                   (mv (car lst) (cadr lst) (caddr lst)))))

                     ((acl2::local-stobjs bitarr litarr)
                      (mv bitarr litarr contra constraint-db logicman bvar-db stack pathcond constraint-pathcond state))

                     (arr-size (+ 1 (bfrstate->bound (logicman->bfrstate logicman))))
                     (bitarr (resize-bits arr-size bitarr))
                     (seen nil)

                     ((mv bitarr seen) (acl2::cwtime (constraint-db-mark-bfrs constraint-db bitarr seen)))
                     ((mv bitarr seen) (acl2::cwtime (major-stack-mark-bfrs stack-obj bitarr seen)))
                     ((mv bitarr seen) (acl2::cwtime (fgl-objectlist-mark-bfrs bvar-db-objs bitarr seen)))
                     (- (fast-alist-free seen))

                     (bitarr
                      (time$ (stobj-let ((aignet-pathcond (pathcond-aignet pathcond)))
                                        (bitarr)
                                        (aignet::aignet-pathcond-mark-bfrs aignet-pathcond bitarr)
                                        bitarr)
                             :msg "; ~s0 (pathcond): ~st seconds, ~sa bytes.~%"
                             :args '(aignet::aignet-pathcond-mark-bfrs)))
                     (bitarr
                      (time$ (stobj-let ((aignet-pathcond (pathcond-aignet constraint-pathcond)))
                                        (bitarr)
                                        (aignet::aignet-pathcond-mark-bfrs aignet-pathcond bitarr)
                                        bitarr)
                             :msg "; ~s0 (constraint): ~st seconds, ~sa bytes.~%"
                             :args '(aignet::aignet-pathcond-mark-bfrs)))

                     ((acl2::hintcontext-bind ((old-logicman logicman)
                                               (old-litarr litarr)
                                               (old-state state)
                                               (old-stack-obj stack-obj)
                                               (old-constraint-db constraint-db)
                                               (old-bvar-db bvar-db)
                                               (old-pathcond pathcond)
                                               (old-constraint-pathcond constraint-pathcond))))
                     ((mv logicman litarr state)
                      (acl2::cwtime (logicman-comb-transform logicman bitarr litarr config state)))
                     
                     (memo nil)

                     ((mv constraint-db memo) (acl2::cwtime (constraint-db-map-bfrs constraint-db litarr memo)))
                     ((mv stack-obj memo) (acl2::cwtime (major-stack-map-bfrs stack-obj litarr memo)))
                     ((mv bvar-db-objs memo) (acl2::cwtime (fgl-objectlist-map-bfrs-memo bvar-db-objs litarr memo)))

                     (- (fast-alist-free memo))

                     ((mv contra1 pathcond)
                      (time$ (logicman-pathcond-map-bfrs pathcond litarr logicman)
                             :msg "; ~s0 (pathcond): ~st seconds, ~sa bytes.~%"
                             :args '(logicman-pathcond-map-bfrs)))
                     ((mv contra2 constraint-pathcond)
                      (time$ (logicman-pathcond-map-bfrs constraint-pathcond litarr logicman)
                             :msg "; ~s0 (constraint): ~st seconds, ~sa bytes.~%"
                             :args '(logicman-pathcond-map-bfrs)))

                     (bvar-db (init-bvar-db base-bvar bvar-db))
                     (bvar-db (bvar-db-from-objectlist bvar-db-objs bvar-db state))

                     (stack (stack-import stack-obj stack))
                     
                     ((acl2::hintcontext :transform)))
                  (mv bitarr litarr
                      (or* (and** contra1 (pathcond-enabledp pathcond))
                           (and** contra2 (pathcond-enabledp constraint-pathcond)))
                      constraint-db
                      logicman
                      bvar-db
                      stack
                      pathcond
                      constraint-pathcond
                      state))

                (b* ((interp-st (update-interp-st->constraint-db constraint-db interp-st)))
                  (mv contra interp-st state))))
   :msg "; ~s0: ~st seconds, ~sa bytes.~%"
   :args '(interp-st-global-transform))
  ///
  (defret w-state-of-<fn>
    (equal (w new-state) (w state)))

  ;; (local (in-theory (enable bfr-listp-when-not-member-witness)))

  (set-ignore-ok t)

  (local (defthm bfrs-markedp-of-mark-bvar-db-objectlist
           (b* (((mv new-bitarr &) (fgl-objectlist-mark-bfrs
                                    (bvar-db-objectlist (base-bvar$a bvar-db) bvar-db)
                                    bitarr seen)))
             (implies (fgl-object-mark-bfrs-invar seen bitarr)
                      (bfrs-markedp (bvar-db-bfrlist bvar-db) new-bitarr)))
           :hints (("goal" :use ((:instance fgl-objectlist-mark-bfrs-marks-bfrs
                                  (x (bvar-db-objectlist (base-bvar$a bvar-db) bvar-db))))
                    :in-theory (disable fgl-objectlist-mark-bfrs-marks-bfrs)))))

  (local (defthm bfrs-markedp-of-mark-bvar-db-objectlist
           (b* (((mv new-bitarr &) (fgl-objectlist-mark-bfrs
                                    (bvar-db-objectlist (base-bvar$a bvar-db) bvar-db)
                                    bitarr seen)))
             (implies (fgl-object-mark-bfrs-invar seen bitarr)
                      (bfrs-markedp (bvar-db-bfrlist bvar-db) new-bitarr)))
           :hints (("goal" :use ((:instance fgl-objectlist-mark-bfrs-marks-bfrs
                                  (x (bvar-db-objectlist (base-bvar$a bvar-db) bvar-db))))
                    :in-theory (disable fgl-objectlist-mark-bfrs-marks-bfrs)))))


  (defret stack-concretize-of-<fn>
    (implies (and (interp-st-bfrs-ok interp-st)
                  (bfr-mode-is :aignet (interp-st-bfr-mode)))
             (equal (fgl-major-stack-concretize (interp-st->stack new-interp-st)
                                                env
                                                (interp-st->logicman new-interp-st))
                    (fgl-major-stack-concretize (interp-st->stack interp-st)
                                                env
                                                (interp-st->logicman interp-st))))
    :hints(("Goal" :in-theory (enable interp-st-bfrs-ok))
           (acl2::function-termhint
            interp-st-global-transform
            (:transform
             `(:in-theory (e/d (logicman->bfrstate
                                bfr-pathcond-p)
                               (bfr-litarr-correct-p-of-logicman-comb-transform))
               :use ((:instance bfr-litarr-correct-p-of-logicman-comb-transform
                      (bfrs (append (major-stack-bfrlist ,(acl2::hq old-stack-obj))
                                    (constraint-db-bfrlist ,(acl2::hq old-constraint-db))
                                    (bvar-db-bfrlist ,(acl2::hq old-bvar-db))
                                    (remove 0 (aignet::nbalist-to-cube (pathcond-aignet ,(acl2::hq old-pathcond))))
                                    (remove 0 (aignet::nbalist-to-cube (pathcond-aignet ,(acl2::hq old-constraint-pathcond))))))
                      (bound (bfrstate->bound (logicman->bfrstate ,(acl2::hq logicman))))
                      (env (fgl-env->bfr-vals ,(acl2::hq env)))
                      (logicman ,(acl2::hq old-logicman))
                      (bitarr ,(acl2::hq bitarr))
                      (litarr ,(acl2::hq old-litarr))
                      (config ,(acl2::hq config))
                      (state ,(acl2::hq old-state)))))))))

  (local (defret logicman-pathcond-eval-checkpoints!-of-<fn>-match-any
           (implies (and ;; (not contra)
                     (bfr-litarr-correct-p some-bfrs
                                           env litarr logicman2 logicman)
                     (bfr-litarr-correct-p (aignet::nbalist-to-cube (pathcond-aignet pathcond))
                                           env litarr logicman2 logicman)
                     (lbfr-mode-is :aignet logicman)
                     (lbfr-mode-is :aignet logicman2)
                     (equal (aignet::num-ins (logicman->aignet logicman))
                            (aignet::num-ins (logicman->aignet logicman2))))
                    (equal (logicman-pathcond-eval-checkpoints! env new-pathcond logicman2)
                           (logicman-pathcond-eval-checkpoints! env pathcond logicman)))
           :hints (("Goal" :use logicman-pathcond-eval-checkpoints!-of-<fn>
                    :in-theory (disable logicman-pathcond-eval-checkpoints!-of-<fn>)))
           :fn logicman-pathcond-map-bfrs))

  (defret pathcond-eval-of-<fn>
    (implies (and (interp-st-bfrs-ok interp-st)
                  (bfr-mode-is :aignet (interp-st-bfr-mode)))
             (equal (logicman-pathcond-eval-checkpoints! env
                                                         (interp-st->pathcond new-interp-st)
                                                         (interp-st->logicman new-interp-st))
                    (logicman-pathcond-eval-checkpoints! env
                                                         (interp-st->pathcond interp-st)
                                                         (interp-st->logicman interp-st))))
    :hints(("Goal" :in-theory (enable interp-st-bfrs-ok))
           (acl2::function-termhint
            interp-st-global-transform
            (:transform
             `(:in-theory (e/d (logicman->bfrstate
                                bfr-pathcond-p)
                               (bfr-litarr-correct-p-of-logicman-comb-transform
                                bfr-litarr-correct-p-all-envs-of-logicman-comb-transform))
               :use ((:instance bfr-litarr-correct-p-of-logicman-comb-transform
                      (bfrs (append (major-stack-bfrlist ,(acl2::hq old-stack-obj))
                                    (constraint-db-bfrlist ,(acl2::hq old-constraint-db))
                                    (bvar-db-bfrlist ,(acl2::hq old-bvar-db))
                                    (remove 0 (aignet::nbalist-to-cube (pathcond-aignet ,(acl2::hq old-pathcond))))
                                    (remove 0 (aignet::nbalist-to-cube (pathcond-aignet ,(acl2::hq old-constraint-pathcond))))))
                      (bound (bfrstate->bound (logicman->bfrstate ,(acl2::hq logicman))))
                      (env ,(acl2::hq env))
                      (logicman ,(acl2::hq old-logicman))
                      (bitarr ,(acl2::hq bitarr))
                      (litarr ,(acl2::hq old-litarr))
                      (config ,(acl2::hq config))
                      (state ,(acl2::hq old-state))))
               :do-not-induct t
               :do-not '(fertilize eliminate-destructors generalize))))))

  ;; (local (defret logicman-pathcond-eval-of-<fn>-match
  ;;          (implies (and ;; (not contra)
  ;;                    (bfr-litarr-correct-p some-bfrs
  ;;                                          env litarr logicman2 logicman)
  ;;                    (bfr-litarr-correct-p (aignet::nbalist-to-cube (pathcond-aignet pathcond))
  ;;                                          env litarr logicman2 logicman)
  ;;                    (lbfr-mode-is :aignet logicman)
  ;;                    (lbfr-mode-is :aignet logicman2)
  ;;                    (equal (aignet::num-ins (logicman->aignet logicman))
  ;;                           (aignet::num-ins (logicman->aignet logicman2))))
  ;;                   (equal (logicman-pathcond-eval env new-pathcond logicman2)
  ;;                          (logicman-pathcond-eval env pathcond logicman)))
  ;;          :hints (("goal" :use logicman-pathcond-eval-of-<fn>
  ;;                   :in-theory (disable logicman-pathcond-eval-of-<fn>)))
  ;;          :fn logicman-pathcond-map-bfrs))

  (defret constraint-eval-of-<fn>
    (implies (and (interp-st-bfrs-ok interp-st)
                  (bfr-mode-is :aignet (interp-st-bfr-mode)))
             (equal (logicman-pathcond-eval env
                                            (interp-st->constraint new-interp-st)
                                            (interp-st->logicman new-interp-st))
                    (logicman-pathcond-eval env
                                            (interp-st->constraint interp-st)
                                            (interp-st->logicman interp-st))))
    :hints(("Goal" :in-theory (enable interp-st-bfrs-ok))
           (acl2::function-termhint
            interp-st-global-transform
            (:transform
             `(:in-theory (e/d (logicman->bfrstate
                                bfr-pathcond-p)
                               (bfr-litarr-correct-p-of-logicman-comb-transform
                                bfr-litarr-correct-p-all-envs-of-logicman-comb-transform))
               :use ((:instance bfr-litarr-correct-p-of-logicman-comb-transform
                      (bfrs (append (major-stack-bfrlist ,(acl2::hq old-stack-obj))
                                    (constraint-db-bfrlist ,(acl2::hq old-constraint-db))
                                    (bvar-db-bfrlist ,(acl2::hq old-bvar-db))
                                    (remove 0 (aignet::nbalist-to-cube (pathcond-aignet ,(acl2::hq old-pathcond))))
                                    (remove 0 (aignet::nbalist-to-cube (pathcond-aignet ,(acl2::hq old-constraint-pathcond))))))
                      (bound (bfrstate->bound (logicman->bfrstate ,(acl2::hq logicman))))
                      (env ,(acl2::hq env))
                      (logicman ,(acl2::hq old-logicman))
                      (bitarr ,(acl2::hq bitarr))
                      (litarr ,(acl2::hq old-litarr))
                      (config ,(acl2::hq config))
                      (state ,(acl2::hq old-state)))))))))

  (defret base-bvar-of-<fn>
    (equal (base-bvar$a (interp-st->bvar-db new-interp-st))
           (base-bvar$a (interp-st->bvar-db interp-st))))

  (defret next-bvar-of-<fn>
    (equal (next-bvar$a (interp-st->bvar-db new-interp-st))
           (next-bvar$a (interp-st->bvar-db interp-st))))

  ;; (local (defthm bfr-litarr-correct-p-when-subsetp
  ;;          (implies (and (bfr-litarr-correct-p x env litarr logicman2 logicman)
  ;;                        (subsetp y x))
  ;;                   (bfr-litarr-correct-p y env litarr logicman2 logicman))
  ;;          :hints (("goal" :in-theory (enable subsetp bfr-litarr-correct-p)))))


  ;; (local (defthm subsetp-bfrlist-of-get-bvar->term$a-aux
  ;;          (implies (and (<= (base-bvar$a bvar-db) (nfix n))
  ;;                        (< (nfix n) (nfix m)))
  ;;                   (subsetp (fgl-object-bfrlist (get-bvar->term$a n bvar-db))
  ;;                            (bvar-db-bfrlist-aux m bvar-db)))
  ;;          :hints(("Goal" :in-theory (enable bvar-db-bfrlist-aux)
  ;;                  :induct (bvar-db-bfrlist-aux m bvar-db)
  ;;                  :expand ((bvar-db-bfrlist-aux m bvar-db))))))

  ;; (local (defthm subsetp-bfrlist-of-get-bvar->term$a
  ;;          (implies (and (<= (base-bvar$a bvar-db) (nfix n))
  ;;                        (< (nfix n) (next-bvar$a bvar-db)))
  ;;                   (subsetp (fgl-object-bfrlist (get-bvar->term$a n bvar-db))
  ;;                            (bvar-db-bfrlist bvar-db)))
  ;;          :hints(("Goal" :in-theory (enable bvar-db-bfrlist)))))

  (local (defret eval-of-<fn>-match-any-bfr-litarr-correct
           (implies (and (bfr-litarr-correct-p some-bfrlist
                                               (fgl-env->bfr-vals env)
                                               litarr logicman2 logicman)
                         (bfr-litarr-correct-p (fgl-object-bfrlist x)
                                               (fgl-env->bfr-vals env)
                                               litarr logicman2 logicman))
                    (equal (fgl-object-eval new-x env logicman2)
                           (fgl-object-eval x env logicman)))
           :fn fgl-object-map-bfrs))

  (local (Defthm bfr-litarr-correct-p-of-get-bvar->term$a
           (implies (and (bfr-litarr-correct-p (bvar-db-bfrlist bvar-db) env litarr logicman2 logicman)
                         (<= (base-bvar$a bvar-db) (nfix n))
                         (< (nfix n) (next-bvar$a bvar-db)))
                    (bfr-litarr-correct-p
                     (fgl-object-bfrlist (get-bvar->term$a n bvar-db))
                     env litarr logicman2 logicman))))

  (local (Defthm bfr-litarr-correct-p-all-envs-of-get-bvar->term$a
           (implies (and (bfr-litarr-correct-p-all-envs (bvar-db-bfrlist bvar-db) litarr logicman2 logicman)
                         (<= (base-bvar$a bvar-db) (nfix n))
                         (< (nfix n) (next-bvar$a bvar-db)))
                    (bfr-litarr-correct-p-all-envs
                     (fgl-object-bfrlist (get-bvar->term$a n bvar-db)) litarr logicman2 logicman))
           :hints(("Goal" :in-theory (enable bfr-litarr-correct-p-all-envs-of-subset)))))

  (local (Defthm bfr-litarr-p-of-get-bvar->term$a
           (implies (and (bfr-litarr-p (bvar-db-bfrlist bvar-db) litarr bound)
                         (<= (base-bvar$a bvar-db) (nfix n))
                         (< (nfix n) (next-bvar$a bvar-db)))
                    (bfr-litarr-p
                     (fgl-object-bfrlist (get-bvar->term$a n bvar-db)) litarr bound))
           :hints(("Goal" :in-theory (enable bfr-litarr-p-of-subset)))))

  ;; (local (defthm fgl-object-eval-of-nth
  ;;          (equal (fgl-object-eval (nth n x) env)
  ;;                 (nth n (fgl-objectlist-eval x env)))
  ;;          :hints(("Goal" :in-theory (enable fgl-objectlist-eval nth)))))

  (local (defthm nth-of-fgl-objectlist-map-bfrs
           (equal (nth n (fgl-objectlist-map-bfrs x litarr))
                  (fgl-object-map-bfrs (nth n x) litarr))
           :hints(("Goal" :in-theory (enable nth fgl-objectlist-map-bfrs)
                   :expand ((fgl-object-map-bfrs nil litarr))))))

  (defret get-bvar->term-of-<fn>
    (implies (and (interp-st-bfrs-ok interp-st)
                  (bfr-mode-is :aignet (interp-st-bfr-mode))
                  ;; (not contra)
                  (<= (base-bvar$a (interp-st->bvar-db interp-st)) (nfix n))
                  (< (nfix n) (next-bvar$a (interp-st->bvar-db interp-st))))
             (equal (fgl-object-eval (get-bvar->term$a n (interp-st->bvar-db new-interp-st))
                                     env
                                     (interp-st->logicman new-interp-st))
                    (fgl-object-eval (get-bvar->term$a n (interp-st->bvar-db interp-st))
                                     env
                                     (interp-st->logicman interp-st))))
    :hints(("Goal" :in-theory (enable interp-st-bfrs-ok))
           (acl2::function-termhint
            interp-st-global-transform
            (:transform
             `(:in-theory (e/d (logicman->bfrstate
                                bfr-pathcond-p)
                               (bfr-litarr-correct-p-of-logicman-comb-transform))
               :use ((:instance bfr-litarr-correct-p-of-logicman-comb-transform
                      (bfrs (append (major-stack-bfrlist ,(acl2::hq old-stack-obj))
                                    (constraint-db-bfrlist ,(acl2::hq old-constraint-db))
                                    (bvar-db-bfrlist ,(acl2::hq old-bvar-db))
                                    (remove 0 (aignet::nbalist-to-cube (pathcond-aignet ,(acl2::hq old-pathcond))))
                                    (remove 0 (aignet::nbalist-to-cube (pathcond-aignet ,(acl2::hq old-constraint-pathcond))))))
                      (bound (bfrstate->bound (logicman->bfrstate ,(acl2::hq logicman))))
                      (env (fgl-env->bfr-vals ,(acl2::hq env)))
                      (logicman ,(acl2::hq old-logicman))
                      (bitarr ,(acl2::hq bitarr))
                      (litarr ,(acl2::hq old-litarr))
                      (config ,(acl2::hq config))
                      (state ,(acl2::hq old-state)))))))))

  (local (defret bfrlist-boundedp-of-<fn>-bind
           (implies (and (bfr-litarr-correct-p-all-envs some-bfrs
                                                        litarr logicman2 logicman)
                         (bfr-litarr-correct-p-all-envs (fgl-object-bfrlist x)
                                                        litarr logicman2 logicman)
                         (equal (logicman->mode logicman2)
                                (logicman->mode logicman))
                         (bfrlist-boundedp (fgl-object-bfrlist x) n logicman))
                    (bfrlist-boundedp (fgl-object-bfrlist new-x) n logicman2))
           :fn fgl-object-map-bfrs))

  (defret bfrlist-boundedp-of-get-bvar->term-of-<fn>
    (implies (and (interp-st-bfrs-ok interp-st)
                  (bfr-mode-is :aignet (interp-st-bfr-mode))
                  ;; (not contra)
                  (<= (base-bvar$a (interp-st->bvar-db interp-st)) (nfix n))
                  (< (nfix n) (next-bvar$a (interp-st->bvar-db interp-st)))
                  (bfrlist-boundedp (fgl-object-bfrlist (get-bvar->term$a n (interp-st->bvar-db interp-st)))
                               k (interp-st->logicman interp-st)))
             (bfrlist-boundedp
                   (fgl-object-bfrlist (get-bvar->term$a n (interp-st->bvar-db new-interp-st)))
                   k (interp-st->logicman new-interp-st)))
    :hints(("Goal" :in-theory (enable interp-st-bfrs-ok))
           (acl2::function-termhint
            interp-st-global-transform
            (:transform
             `(:in-theory (e/d (logicman->bfrstate
                                bfr-pathcond-p)
                               (bfr-litarr-correct-p-all-envs-of-logicman-comb-transform))
               :use ((:instance bfr-litarr-correct-p-all-envs-of-logicman-comb-transform
                      (bfrs (append (major-stack-bfrlist ,(acl2::hq old-stack-obj))
                                    (constraint-db-bfrlist ,(acl2::hq old-constraint-db))
                                    (bvar-db-bfrlist ,(acl2::hq old-bvar-db))
                                    (remove 0 (aignet::nbalist-to-cube (pathcond-aignet ,(acl2::hq old-pathcond))))
                                    (remove 0 (aignet::nbalist-to-cube (pathcond-aignet ,(acl2::hq old-constraint-pathcond))))))
                      (bound (bfrstate->bound (logicman->bfrstate ,(acl2::hq logicman))))
                      (logicman ,(acl2::hq old-logicman))
                      (bitarr ,(acl2::hq bitarr))
                      (litarr ,(acl2::hq old-litarr))
                      (config ,(acl2::hq config))
                      (state ,(acl2::hq old-state)))))))))

  (local (defthm plus-minus
           (equal (+ a (- a) b) (fix b))))

  (local (defthm cancel-plus-first
           (equal (equal (+ a b) (+ a c))
                  (equal (fix b) (fix c)))))

  (local (in-theory (enable bvar-db-boundedp-necc)))

  ;; (local (in-theory (enable bfr-listp-when-not-member-witness)))

  (defret interp-st-bfrs-ok-of-<fn>
    (implies (and (interp-st-bfrs-ok interp-st)
                  (bfr-mode-is :aignet (interp-st-bfr-mode)))
             (interp-st-bfrs-ok new-interp-st))
    :hints(("Goal" :in-theory (enable interp-st-bfrs-ok))
           (acl2::function-termhint
            interp-st-global-transform
            (:transform
             `(:in-theory (e/d (logicman->bfrstate
                                bfr-pathcond-p
                                bfr-listp-when-not-member-witness)
                               (bfr-litarr-p-of-logicman-comb-transform
                                bfr-litarr-correct-p-all-envs-of-logicman-comb-transform))
               :expand ((bvar-db-boundedp ,(acl2::hq bvar-db) ,(acl2::hq logicman)))
               :use ((:instance bfr-litarr-p-of-logicman-comb-transform
                      (bfrs (append (major-stack-bfrlist ,(acl2::hq old-stack-obj))
                                    (constraint-db-bfrlist ,(acl2::hq old-constraint-db))
                                    (bvar-db-bfrlist ,(acl2::hq old-bvar-db))
                                    (remove 0 (aignet::nbalist-to-cube (pathcond-aignet ,(acl2::hq old-pathcond))))
                                    (remove 0 (aignet::nbalist-to-cube (pathcond-aignet ,(acl2::hq old-constraint-pathcond))))))
                      (bound (bfrstate->bound (logicman->bfrstate ,(acl2::hq logicman))))
                      (logicman ,(acl2::hq old-logicman))
                      (bitarr ,(acl2::hq bitarr))
                      (litarr ,(acl2::hq old-litarr))
                      (config ,(acl2::hq config))
                      (state ,(acl2::hq old-state)))
                     (:instance bfr-litarr-correct-p-all-envs-of-logicman-comb-transform
                      (bfrs (append (major-stack-bfrlist ,(acl2::hq old-stack-obj))
                                    (constraint-db-bfrlist ,(acl2::hq old-constraint-db))
                                    (bvar-db-bfrlist ,(acl2::hq old-bvar-db))
                                    (remove 0 (aignet::nbalist-to-cube (pathcond-aignet ,(acl2::hq old-pathcond))))
                                    (remove 0 (aignet::nbalist-to-cube (pathcond-aignet ,(acl2::hq old-constraint-pathcond))))))
                      (bound (bfrstate->bound (logicman->bfrstate ,(acl2::hq logicman))))
                      (logicman ,(acl2::hq old-logicman))
                      (bitarr ,(acl2::hq bitarr))
                      (litarr ,(acl2::hq old-litarr))
                      (config ,(acl2::hq config))
                      (state ,(acl2::hq old-state)))))))))

  (defret interp-st-get-of-<fn>
    (implies (not (member (interp-st-field-fix key)
                          '(:cgraph :cgraph-memo :cgraph-index :fgarrays :next-fgarray
                            :logicman :bvar-db :stack :pathcond :constraint :constraint-db)))
             (equal (interp-st-get key new-interp-st)
                    (interp-st-get key interp-st))))

  (defret scratch-isomorphic-of-<fn>
    (interp-st-scratch-isomorphic new-interp-st interp-st)
    :hints(("Goal" :in-theory (enable interp-st-scratch-isomorphic))))

  (defret logicman->mode-of-<fn>
    (equal (logicman->mode (interp-st->logicman new-interp-st))
           (logicman->mode (interp-st->logicman interp-st))))

  (defret bfr-nvars-of-<fn>
    (equal (bfr-nvars (interp-st->logicman new-interp-st))
           (bfr-nvars (interp-st->logicman interp-st))))

  (defret pathcond-enabledp-of-<fn>
    (equal (nth *pathcond-enabledp* (interp-st->pathcond new-interp-st))
           (nth *pathcond-enabledp* (interp-st->pathcond interp-st))))

  (defret constraint-enabledp-of-<fn>
    (equal (nth *pathcond-enabledp* (interp-st->constraint new-interp-st))
           (nth *pathcond-enabledp* (interp-st->constraint interp-st))))

  (defret pathcond-rewind-stack-len-of-<fn>
    (equal (pathcond-rewind-stack-len (bfrmode :aignet) (interp-st->pathcond new-interp-st))
           (pathcond-rewind-stack-len (bfrmode :aignet) (interp-st->pathcond interp-st))))

  (defret pathcond-rewind-ok-of-<fn>
    (equal (pathcond-rewind-ok (bfrmode :aignet) (interp-st->pathcond new-interp-st))
           (pathcond-rewind-ok (bfrmode :aignet) (interp-st->pathcond interp-st))))

  (defret contra-of-<fn>
    (implies (and (logicman-pathcond-eval env (interp-st->pathcond interp-st)
                                          (interp-st->logicman interp-st))
                  (logicman-pathcond-eval env (interp-st->constraint interp-st)
                                          (interp-st->logicman interp-st))
                  (interp-st-bfrs-ok interp-st)
                  (bfr-mode-is :aignet (interp-st-bfr-mode)))
             (not contra))
    :hints(("Goal" :in-theory (enable interp-st-bfrs-ok or* and*))
           (acl2::function-termhint
            interp-st-global-transform
            (:transform
             `(:in-theory (e/d (logicman->bfrstate
                                bfr-pathcond-p)
                               (bfr-litarr-correct-p-all-envs-of-logicman-comb-transform
                                bfr-litarr-correct-p-of-logicman-comb-transform))
               :use ((:instance bfr-litarr-correct-p-of-logicman-comb-transform
                      (bfrs (append (major-stack-bfrlist ,(acl2::hq old-stack-obj))
                                    (constraint-db-bfrlist ,(acl2::hq old-constraint-db))
                                    (bvar-db-bfrlist ,(acl2::hq old-bvar-db))
                                    (remove 0 (aignet::nbalist-to-cube (pathcond-aignet ,(acl2::hq old-pathcond))))
                                    (remove 0 (aignet::nbalist-to-cube (pathcond-aignet ,(acl2::hq old-constraint-pathcond))))))
                      (bound (bfrstate->bound (logicman->bfrstate ,(acl2::hq logicman))))
                      (env ,(acl2::hq env))
                      (logicman ,(acl2::hq old-logicman))
                      (bitarr ,(acl2::hq bitarr))
                      (litarr ,(acl2::hq old-litarr))
                      (config ,(acl2::hq config))
                      (state ,(acl2::hq old-state))))))))))


(define fgl-global-transform (config)
  :enabled t
  (declare (ignore config))
  nil)

(disable-execution fgl-global-transform)



(def-formula-checks global-trans-formula-checks
  (fgl-global-transform))

(local (include-book "primitive-lemmas"))

(def-fgl-primitive fgl-global-transform (config)
  (b* (((unless (bfr-mode-is :aignet (interp-st-bfr-mode)))
        (cw "Warning: skipping global transform because we're not in aignet mode~%")
        (mv t nil interp-st state))
       ((unless (fgl-object-case config :g-concrete))
        (fgl-interp-error :msg "Fgl-global-transform: config must be a concrete object"
                         :debug-obj config
                         :nvals 2))
       (config (g-concrete->val config))
       ((mv contra interp-st state)
        (interp-st-global-transform config interp-st state))
       ((when contra)
        (b* ((interp-st (interp-st-set-error :unreachable interp-st)))
          (mv t nil interp-st state))))
    (mv t nil interp-st state))
  :returns (mv successp ans interp-st state)
  :formula-check global-trans-formula-checks)


