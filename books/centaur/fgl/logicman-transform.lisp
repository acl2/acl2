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
(include-book "centaur/aignet/simplify-marked" :dir :system)
(include-book "mark-bfrs-base")
(std::make-returnspec-config :hints-sub-returnnames t)
(local (in-theory (disable w)))

(define bfr-map (bfr litarr)
  :guard (and (< 0 (lits-length litarr))
              (bfr-p bfr (bfrstate (bfrmode :aignet) (1- (lits-length litarr)))))
  :guard-hints (("Goal" :in-theory (enable bfr-p)))
  (cond ((eq bfr t) t)
        ((eq bfr nil) nil)
        (t (if (mbt (not (eql bfr 0)))
               (b* ((lit (aignet::lit-copy bfr litarr)))
                 (cond ((eql lit 0) nil)
                       ((eql lit 1) t)
                       (t lit)))
             nil)))
  ///
  (defthm bfr-map-of-consts
    (and (equal (bfr-map nil litarr) nil)
         (equal (bfr-map t litarr)   t)
         (equal (bfr-map 0 litarr)   nil))))


(define bfrlist-map (bfrs litarr)
  :guard (and (< 0 (lits-length litarr))
              (bfr-listp bfrs (bfrstate (bfrmode :aignet) (1- (lits-length litarr)))))
  :guard-hints (("Goal" :in-theory (enable bfr-p)))
  :returns (new-bfrs)
  (if (atom bfrs)
      nil
    (cons (bfr-map (car bfrs) litarr)
          (bfrlist-map (cdr bfrs) litarr)))

  ///
  (defret len-of-<fn>
    (equal (len new-bfrs) (len bfrs))))


(define bfr-litarr-p (bfrs litarr (bfrstate-bound natp))
  :guard (and (< 0 (lits-length litarr))
              (bfr-listp bfrs (bfrstate (bfrmode :aignet) (1- (lits-length litarr)))))
  :returns (ok)
  (if (atom bfrs)
      t
    (and (bfr-p (bfr-map (car bfrs) litarr)
                (bfrstate (bfrmode :aignet) bfrstate-bound))
         (bfr-litarr-p (cdr bfrs) litarr bfrstate-bound)))
  ///
  (defret <fn>-of-cons
    (equal (bfr-litarr-p (cons a x) litarr bfrstate-bound)
           (and (bfr-p (bfr-map a litarr)
                       (bfrstate (bfrmode :aignet) bfrstate-bound))
                (bfr-litarr-p x litarr bfrstate-bound))))

  (defret <fn>-of-nil
    (bfr-litarr-p nil litarr bfrstate-bound))

  (defret <fn>-of-append
    (equal (bfr-litarr-p (append a b) litarr bfrstate-bound)
           (and (bfr-litarr-p a litarr bfrstate-bound)
                (bfr-litarr-p b litarr bfrstate-bound))))

  (local (defthm bfrstate-of-bfrstate->bound
           (implies (equal mode (bfrstate->mode bfrstate))
                    (equal (bfrstate mode (bfrstate->bound bfrstate))
                           (bfrstate-fix bfrstate)))
           :hints(("Goal" :in-theory (enable bfrstate-fix-redef)))))

  (defret bfr-p-of-car-when-bfr-litarr-p
    (implies (and (bfr-litarr-p bfrs litarr bfrstate-bound)
                  (equal bfrstate (bfrstate (bfrmode :aignet) bfrstate-bound)))
             (bfr-p (bfr-map (car bfrs) litarr) bfrstate)))

  (defret bfr-p-of-member-when-bfr-litarr-p
    (implies (and (member bfr bfrs)
                  (bfr-litarr-p bfrs litarr (bfrstate->bound bfrstate))
                  (equal (bfrstate->mode bfrstate) (bfrmode :aignet)))
             (bfr-p (bfr-map bfr litarr) bfrstate)))

  (defret bfr-listp-of-map-when-bfr-litarr-p
    (implies (and (bfr-litarr-p bfrs litarr (bfrstate->bound bfrstate))
                  (equal (bfrstate->mode bfrstate) (bfrmode :aignet)))
             (bfr-listp (bfrlist-map bfrs litarr) bfrstate))
    :hints(("Goal" :in-theory (enable bfrlist-map))))

  (defretd bfr-litarr-p-of-subset
    (implies (and (bfr-litarr-p bfrs litarr bound)
                  (subsetp bfrs1 bfrs))
             (bfr-litarr-p bfrs1 litarr bound))
    :hints(("Goal" :in-theory (enable subsetp))))

  (defthm bfr-litarr-p-of-remove-0
    (iff (bfr-litarr-p (remove 0 bfrs) litarr bound)
         (bfr-litarr-p bfrs litarr bound))
    :hints(("Goal" :in-theory (enable bfr-litarr-p
                                      bfr->aignet-lit
                                      bfr-fix len remove)
            :induct (len bfrs)
            :expand ((bfr-eval 0 env))))))
             

(define bfr-litarr-p-witness (bfrs litarr (bfrstate-bound natp))
  :guard (and (< 0 (lits-length litarr))
              (bfr-listp bfrs (bfrstate (bfrmode :aignet) (1- (lits-length litarr)))))
  :returns (bfr)
  (if (atom bfrs)
      nil
    (if (bfr-p (bfr-map (car bfrs) litarr)
                (bfrstate (bfrmode :aignet) bfrstate-bound))
        (bfr-litarr-p-witness (cdr bfrs) litarr bfrstate-bound)
      (car bfrs)))
  ///
  (defretd bfr-litarr-p-by-witness
    (implies (acl2::rewriting-positive-literal `(bfr-litarr-p ,bfrs ,litarr ,bfrstate-bound))
             (equal (bfr-litarr-p bfrs litarr bfrstate-bound)
                    ;; (implies (member bfr bfrs)
                             (bfr-p (bfr-map bfr litarr)
                                    (bfrstate (bfrmode :aignet) bfrstate-bound))))
    :hints(("Goal" :in-theory (enable bfr-litarr-p))))

  (defretd bfr-litarr-p-when-witness
    (implies (bfr-p (bfr-map bfr litarr)
                    (bfrstate (bfrmode :aignet) bfrstate-bound))
             (bfr-litarr-p bfrs litarr bfrstate-bound))
    :hints(("Goal" :in-theory (enable bfr-litarr-p))))

  (defret bfr-litarr-p-witness-is-member
    (implies (not (bfr-litarr-p bfrs litarr bfrstate-bound))
             (member-equal bfr bfrs))
    :hints(("Goal" :in-theory (enable bfr-litarr-p))))

  ;; (defretd bfr-litarr-p-by-witness
  ;;   (implies (acl2::rewriting-positive-literal `(bfr-litarr-p ,bfrs ,litarr ,bfrstate-bound))
  ;;            (equal (bfr-litarr-p bfrs litarr bfrstate-bound)
  ;;                   (implies (member bfr bfrs)
  ;;                            (bfr-p (bfr-map bfr litarr)
  ;;                                   (bfrstate (bfrmode :aignet) bfrstate-bound)))))
  ;;   :hints(("Goal" :in-theory (enable bfr-litarr-p))))
  )


(defstobj-clone logicman2 logicman :suffix "2")


(define bfr-litarr-correct-p (bfrs env litarr logicman2 logicman)
  :non-executable t
  :guard (and (lbfr-mode-is :aignet)
              (lbfr-mode-is :aignet logicman2)
              (< (bfrstate->bound (logicman->bfrstate)) (lits-length litarr))
              (lbfr-listp bfrs logicman)
              (bfr-litarr-p bfrs litarr (bfrstate->bound (logicman->bfrstate logicman2))))
  :returns (ok)
  :guard-hints (("goal" :in-theory (enable logicman->bfrstate
                                           bfr-litarr-p
                                           bfr-listp)))
  :prepwork ((local (defthm bfr-p-when-gte
                      (implies (and (bfr-p bfrs (bfrstate mode bound1))
                                    (<= (nfix bound1) (nfix bound2)))
                               (bfr-p bfrs (bfrstate mode bound2)))
                      :hints(("Goal" :in-theory (enable bfr-p)))))
             (local (defthm bfr-listp-when-gte
                      (implies (and (bfr-listp bfrs (bfrstate mode bound1))
                                    (<= (nfix bound1) (nfix bound2)))
                               (bfr-listp bfrs (bfrstate mode bound2)))
                      :hints(("Goal" :in-theory (enable bfr-listp))))))
  (if (atom bfrs)
      t
    (and (equal (bfr-eval (bfr-map (car bfrs) litarr) env logicman2)
                (bfr-eval (car bfrs) env logicman))
         (bfr-litarr-correct-p (cdr bfrs) env litarr logicman2 logicman)))
  ///
  
  (defret <fn>-of-cons
    (equal (bfr-litarr-correct-p (cons a x) env litarr logicman2 logicman)
           (and (equal (bfr-eval (bfr-map a litarr) env logicman2)
                       (bfr-eval a env logicman))
                (bfr-litarr-correct-p x env litarr logicman2 logicman))))

  (defret <fn>-of-nil
    (bfr-litarr-correct-p nil env litarr logicman2 logicman))

  (defret <fn>-of-append
    (equal (bfr-litarr-correct-p (append a b) env litarr logicman2 logicman)
           (and (bfr-litarr-correct-p a env litarr logicman2 logicman)
                (bfr-litarr-correct-p b env litarr logicman2 logicman))))

  (defret bfr-eval-of-map-car-when-<fn>
    (implies (bfr-litarr-correct-p bfrs env litarr logicman2 logicman)
             (equal (bfr-eval (bfr-map (car bfrs) litarr) env logicman2)
                    (bfr-eval (car bfrs) env logicman))))

  (defret bfr-eval-of-member-when-<fn>
    (implies (and (member bfr bfrs)
                  (bfr-litarr-correct-p bfrs env litarr logicman2 logicman))
             (equal (bfr-eval (bfr-map bfr litarr) env logicman2)
                    (bfr-eval bfr env logicman))))

  (defret bfr-list-eval-of-map-when-bfr-litarr-correct-p
    (implies (bfr-litarr-correct-p bfrs env litarr logicman2 logicman)
             (equal (bfr-list-eval (bfrlist-map bfrs litarr) env logicman2)
                    (bfr-list-eval bfrs env logicman)))
    :hints(("Goal" :in-theory (enable bfrlist-map bfr-list-eval))))

  (defret bfr-litarr-correct-p-when-subsetp
    (implies (and (bfr-litarr-correct-p bfrs env litarr logicman2 logicman)
                  (subsetp bfrs1 bfrs))
             (bfr-litarr-correct-p bfrs1 env litarr logicman2 logicman))
    :hints(("Goal" :in-theory (enable subsetp))))

  (defthm bfr-litarr-correct-p-of-remove-0
    (implies (and (lbfr-mode-is :aignet)
                  (lbfr-mode-is :aignet logicman2))
             (iff (bfr-litarr-correct-p (remove 0 bfrs) env litarr logicman2 logicman)
                  (bfr-litarr-correct-p bfrs env litarr logicman2 logicman)))
    :hints(("Goal" :in-theory (enable bfr-litarr-correct-p
                                      bfr->aignet-lit
                                      bfr-fix)
            :induct (len bfrs)
            :expand ((bfr-eval 0 env))))))


(define bfr-litarr-correct-p-witness (bfrs env litarr logicman2 logicman)
  :guard (and (lbfr-mode-is :aignet)
              (lbfr-mode-is :aignet logicman2)
              (< (bfrstate->bound (logicman->bfrstate)) (lits-length litarr))
              (lbfr-listp bfrs logicman)
              (bfr-litarr-p bfrs litarr (bfrstate->bound (logicman->bfrstate logicman2))))
  :returns (bfr)
  :guard-hints (("goal" :in-theory (enable logicman->bfrstate
                                           bfr-litarr-p
                                           bfr-listp)))
  :prepwork ((local (defthm bfr-p-when-gte
                      (implies (and (bfr-p bfrs (bfrstate mode bound1))
                                    (<= (nfix bound1) (nfix bound2)))
                               (bfr-p bfrs (bfrstate mode bound2)))
                      :hints(("Goal" :in-theory (enable bfr-p)))))
             (local (defthm bfr-listp-when-gte
                      (implies (and (bfr-listp bfrs (bfrstate mode bound1))
                                    (<= (nfix bound1) (nfix bound2)))
                               (bfr-listp bfrs (bfrstate mode bound2)))
                      :hints(("Goal" :in-theory (enable bfr-listp))))))
  (if (atom bfrs)
      nil
    (if (equal (bfr-eval (bfr-map (car bfrs) litarr) env logicman2)
               (bfr-eval (car bfrs) env logicman))
        (bfr-litarr-correct-p-witness (cdr bfrs) env litarr logicman2 logicman)
      (car bfrs)))
  ///
  (defretd bfr-litarr-correct-p-by-witness
    (implies (acl2::rewriting-positive-literal `(bfr-litarr-correct-p ,bfrs ,env ,litarr ,logicman2 ,logicman))
             (equal (bfr-litarr-correct-p bfrs env litarr logicman2 logicman)
                    (implies (member bfr bfrs)
                             (equal (bfr-eval (bfr-map bfr litarr) env logicman2)
                                    (bfr-eval bfr env logicman)))))
    :hints(("Goal" :in-theory (enable bfr-litarr-correct-p)))))

(defsection bfr-litarr-correct-p-all-envs
  (defun-sk bfr-litarr-correct-p-all-envs (bfrs litarr logicman2 logicman)
    (forall env
            (bfr-litarr-correct-p bfrs env litarr logicman2 logicman))
    :rewrite :direct)

  (in-theory (disable bfr-litarr-correct-p-all-envs))

  (local (defthm bfr-litarr-correct-p-subsetp-when-bfr-litarr-correct-p-all-envs
           (implies (and (bfr-litarr-correct-p-all-envs bfrs litarr logicman2 logicman)
                         (subsetp bfrs1 bfrs))
                    (bfr-litarr-correct-p bfrs1 env litarr logicman2 logicman))
           :hints (("goal" :use ((:instance bfr-litarr-correct-p-all-envs-necc))
                    :in-theory (disable bfr-litarr-correct-p-all-envs-necc)))))

  (defthm bfr-litarr-correct-p-all-envs-implies-bfr-eval
    (implies (and (bfr-litarr-correct-p-all-envs bfrs litarr logicman2 logicman)
                  (member x bfrs))
             (equal (bfr-eval (bfr-map x litarr) env logicman2)
                    (bfr-eval x env logicman)))
    :hints (("goal" :use ((:instance bfr-eval-of-member-when-bfr-litarr-correct-p
                           (bfr x)))
             :in-theory (disable bfr-eval-of-member-when-bfr-litarr-correct-p))))

  (defthm bfr-litarr-correct-p-all-envs-implies-bfrlist-eval
    (implies (bfr-litarr-correct-p-all-envs bfrs litarr logicman2 logicman)
             (equal (bfr-list-eval (bfrlist-map bfrs litarr) env logicman2)
                    (bfr-list-eval bfrs env logicman)))
    :hints (("goal" :use ((:instance bfr-list-eval-of-map-when-bfr-litarr-correct-p))
             :in-theory (disable bfr-list-eval-of-map-when-bfr-litarr-correct-p))))

  (defthm bfr-boundedp-of-bfr-map
    (implies (and (bfr-litarr-correct-p-all-envs bfrs litarr logicman2 logicman)
                  (member x bfrs)
                  (bfr-boundedp x n logicman)
                  (equal (logicman->mode logicman)
                         (logicman->mode logicman2)))
             (bfr-boundedp (bfr-map x litarr) n logicman2))
    :hints (("goal" :expand ((bfr-boundedp (bfr-map x litarr) n logicman2))
             :use ((:instance bfr-boundedp-necc
                    (var (mv-nth 0 (bfr-boundedp-witness (bfr-map x litarr) n logicman2)))
                    (env (mv-nth 1 (bfr-boundedp-witness (bfr-map x litarr) n logicman2)))))
             :in-theory (e/d (bfr-set-var)
                             (bfr-boundedp-necc))
             :do-not-induct t)))

  (defthm bfr-litarr-correct-p-all-envs-implies-cdr
    (implies (bfr-litarr-correct-p-all-envs bfrs litarr logicman2 logicman)
             (bfr-litarr-correct-p-all-envs (cdr bfrs) litarr logicman2 logicman))
    :hints (("goal" :expand ((bfr-litarr-correct-p-all-envs (cdr bfrs) litarr logicman2 logicman))
             :use ((:instance bfr-litarr-correct-p-all-envs-necc
                    (env (bfr-litarr-correct-p-all-envs-witness (cdr bfrs) litarr logicman2 logicman))))
             :in-theory (disable bfr-litarr-correct-p-all-envs-necc))))

  (defthm bfrlist-boundedp-of-bfr-map
    (implies (and (bfr-litarr-correct-p-all-envs bfrs litarr logicman2 logicman)
                  (bfrlist-boundedp bfrs n logicman)
                  (equal (logicman->mode logicman)
                         (logicman->mode logicman2)))
             (bfrlist-boundedp (bfrlist-map bfrs litarr) n logicman2))
    :hints (("goal" :induct (len bfrs)
             :in-theory (enable bfrlist-map bfrlist-boundedp))))

  (local (in-theory (disable append)))
  
  (defthm bfr-litarr-correct-p-all-envs-of-append
    (iff (bfr-litarr-correct-p-all-envs (append a b) litarr logicman2 logicman)
         (and (bfr-litarr-correct-p-all-envs a litarr logicman2 logicman)
              (bfr-litarr-correct-p-all-envs b litarr logicman2 logicman)))
    :hints ((and stable-under-simplificationp
                 (let ((lit (assoc 'bfr-litarr-correct-p-all-envs clause)))
                   `(:expand (,lit))))))

  (defthmd bfr-litarr-correct-p-all-envs-of-subset
    (implies (and (bfr-litarr-correct-p-all-envs bfrs litarr logicman2 logicman)
                  (subsetp bfrs1 bfrs))
             (bfr-litarr-correct-p-all-envs bfrs1 litarr logicman2 logicman))
    :hints (("goal" :expand ((bfr-litarr-correct-p-all-envs bfrs1 litarr logicman2 logicman))
             :use ((:instance bfr-litarr-correct-p-all-envs-necc
                    (env (bfr-litarr-correct-p-all-envs-witness bfrs1 litarr logicman2 logicman))))
             :in-theory (disable bfr-litarr-correct-p-all-envs-necc)))))
  
(define logicman-comb-transform (logicman
                                 bitarr
                                 litarr
                                 config
                                 state)
  :guard (and (lbfr-mode-is :aignet)
              (<= (bits-length bitarr)
                  (stobj-let ((aignet (logicman->aignet logicman)))
                             (num)
                             (aignet::num-fanins aignet)
                             num)))
  :returns (mv new-logicman
               new-litarr
               new-state)
  (stobj-let ((aignet (logicman->aignet logicman))
              (strash (logicman->strash logicman)))
             (aignet strash litarr state)
             (b* (((mv aignet litarr state)
                   (aignet::aignet-simplify-marked aignet bitarr litarr config state))
                  (strash (aignet::strashtab-clear strash))
                  (strash (aignet::aignet-populate-strash 1 strash aignet)))
               (mv aignet strash litarr state))
             (b* ((logicman (resize-logicman->sat-lits 0 logicman))
                  (logicman (logicman-release-ipasirs 0 logicman))
                  (logicman (resize-logicman->ipasir 0 logicman))
                  (logicman (update-logicman->refcounts-index 0 logicman)))
               (mv logicman litarr state)))
  ///
  (local #!aignet
         (defthm lte-fanin-count-by-aignet-idp
           (implies (and (aignet-idp x aignet)
                         (natp x))
                    (<= x (fanin-count aignet)))
           :hints(("Goal" :in-theory (enable aignet-idp)))))
  
  (defret bfr-p-bfr-map-of-<fn>
    (implies (and (bfr-markedp bfr bitarr)
                  (lbfr-mode-is :aignet)
                  (lbfr-p bfr)
                  (<= (len bitarr) (aignet::num-fanins (logicman->aignet logicman)))
                  (equal bfrstate (logicman->bfrstate new-logicman)))
             (bfr-p (bfr-map bfr new-litarr) bfrstate))
    :hints(("Goal" :in-theory (enable bfr-p bfr-map bfr-markedp aignet::lit-copy)
            :do-not-induct t)))

  (local (defthm bfr-p-of-bfr-map-when-0
           (implies (case-split (equal bfr 0))
                    (bfr-p (bfr-map bfr litarr) bfrstate))))

  (local (defthm bfr-map-nonzero
           (not (equal (bfr-map bfr litarr) 0))
           :hints(("Goal" :in-theory (enable bfr-map)))))

  (local (defthm bfr-p-when-member-bfr-listp
           (implies (and (member bfr bfrs)
                         (bfr-listp bfrs))
                    (bfr-p bfr))))

  (local (defthm bfr-p-when-member-bfr-listp-0
           (implies (and (bfr-listp (remove 0 bfrs))
                         (member bfr bfrs)
                         (not (equal 0 bfr)))
                    (bfr-p bfr))))

  (defret bfr-mode-of-<fn>
    (equal (logicman->mode new-logicman)
           (logicman->mode logicman)))

  (local (defthm equal-of-bfrstate-rw
           (equal (equal (bfrstate mode bound) bfrstate)
                  (and (bfrstate-p bfrstate)
                       (equal (bfrstate->mode bfrstate) (bfr-mode-fix mode))
                       (equal (bfrstate->bound bfrstate) (nfix bound))))
           :hints (("goal" :use ((:instance bfrstate-fix-redef (x bfrstate)))
                    :in-theory (disable bfrstate-fix-redef)))))

  (local (include-book "tools/trivial-ancestors-check" :dir :system))
  (local (acl2::use-trivial-ancestors-check))

  (defret bfr-litarr-p-of-<fn>
    (implies (and (bfrs-markedp bfrs bitarr)
                  (lbfr-mode-is :aignet)
                  (lbfr-listp (remove 0 bfrs) logicman)
                  (<= (len bitarr) (aignet::num-fanins (logicman->aignet logicman)))
                  (equal bound (bfrstate->bound (logicman->bfrstate new-logicman))))
             (bfr-litarr-p bfrs new-litarr bound))
    :hints(("Goal" :in-theory (e/d (bfrs-markedp-necc)
                                   (<fn>))
            :use ((:instance bfr-litarr-p-when-witness
                   (litarr new-litarr)
                   (bfrstate-bound bound)))
            :do-not-induct t)))


  (defret litarr-length-of-<fn>
    (implies (<= (len bitarr) (+ 1 (aignet::fanin-count (logicman->aignet logicman))))
             (equal (len new-litarr)
                    (+ 1 (aignet::fanin-count (logicman->aignet logicman))))))



  (local
   #!aignet
   (defthm lit-negate-cond-equal-const
     (implies (syntaxp (and (quotep n1) (quotep x2)))
              (iff (equal (lit-negate-cond x n1) x2)
                   (and (litp x2)
                        (equal (lit-fix x) (lit-negate-cond x2 n1)))))
     :hints(("Goal" :in-theory (enable lit-negate-cond
                                       satlink::equal-of-make-lit)))))

  (defret bfr-eval-bfr-map-of-<fn>
    (implies (and (bfr-markedp bfr bitarr)
                  (lbfr-mode-is :aignet)
                  (lbfr-p bfr)
                  (<= (len bitarr) (aignet::num-fanins (logicman->aignet logicman))))
             (equal (bfr-eval (bfr-map bfr new-litarr) env new-logicman)
                    (bfr-eval bfr env logicman)))
    :hints(("Goal" :in-theory (e/d (bfr-p bfr-eval bfr-map bfr-markedp aignet::lit-copy
                                      bfr->aignet-lit
                                      aignet-lit->bfr)
                                   (aignet::eval-of-aignet-simplify-marked))
            :expand ((:free (invals regvals)
                      (aignet::lit-eval bfr invals regvals (logicman->aignet logicman))))
            :use ((:instance aignet::eval-of-aignet-simplify-marked
                   (n (satlink::lit->var bfr))
                   (aignet (logicman->aignet logicman))
                   (bitarr bitarr)
                   (litarr litarr)
                   (config config)
                   (invals (alist-to-bitarr (aignet::num-ins (logicman->aignet logicman)) env nil))
                   (regvals nil)))
            :do-not-induct t)))

  (defret bfr-litarr-correct-p-of-<fn>
    (implies (and (bfrs-markedp bfrs bitarr)
                  (lbfr-mode-is :aignet)
                  (lbfr-listp bfrs logicman)
                  (<= (len bitarr) (aignet::num-fanins (logicman->aignet logicman)))
                  (equal bound (bfrstate->bound (logicman->bfrstate new-logicman))))
             (bfr-litarr-correct-p bfrs env new-litarr new-logicman logicman))
    :hints(("Goal" :in-theory (e/d (bfr-litarr-correct-p-by-witness
                                    bfrs-markedp-necc)
                                   (<fn>))
            :do-not-induct t)))

  (defret bfr-litarr-correct-p-all-envs-of-<fn>
    (implies (and (bfrs-markedp bfrs bitarr)
                  (lbfr-mode-is :aignet)
                  (lbfr-listp bfrs logicman)
                  (<= (len bitarr) (aignet::num-fanins (logicman->aignet logicman)))
                  (equal bound (bfrstate->bound (logicman->bfrstate new-logicman))))
             (bfr-litarr-correct-p-all-envs bfrs new-litarr new-logicman logicman))
    :hints(("Goal" :in-theory (e/d (bfr-litarr-correct-p-all-envs)
                                   (<fn>))
            :do-not-induct t)))

  (defret w-state-of-<fn>
    (equal (w new-state) (w state)))

  (defret bfr-nvars-of-<fn>
    (equal (bfr-nvars new-logicman)
           (bfr-nvars logicman))
    :hints(("Goal" :in-theory (enable bfr-nvars))))

  (defret logicman-invar-of-<fn>
    (implies (logicman-invar logicman)
             (logicman-invar new-logicman))
    :hints(("Goal" :in-theory (enable logicman-invar
                                      logicman-ipasir-sat-lits-invar))))

  (defret stype-counts-of-<fn>
    (and (equal (aignet::stype-count :pi (logicman->aignet new-logicman))
                (aignet::stype-count :pi (logicman->aignet logicman)))
         (equal (aignet::stype-count :po (logicman->aignet new-logicman))
                0)
         (equal (aignet::stype-count :reg (logicman->aignet new-logicman))
                (aignet::stype-count :reg (logicman->aignet logicman))))))




(defines fgl-object-map-bfrs
  :ruler-extenders :lambdas
  (define fgl-object-map-bfrs ((x fgl-object-p)
                              litarr)
    :guard (and (< 0 (lits-length litarr))
                (bfr-listp (fgl-object-bfrlist x)
                           (bfrstate (bfrmode :aignet) (1- (lits-length litarr)))))
    :verify-guards nil
    :returns (new-x fgl-object-p)
    :measure (two-nats-measure (fgl-object-count x) 0)
    (b* ((x (fgl-object-fix x))
         (kind (fgl-object-kind x))
         ((when (member-eq kind '(:g-concrete :g-var))) x))
      (case kind
        (:g-boolean (b* (((g-boolean x))) (mk-g-boolean (bfr-map x.bool litarr))))
        (:g-integer (b* (((g-integer x))) (mk-g-integer (bfrlist-map x.bits litarr))))
        (:g-ite (b* (((g-ite x))
                     (test (fgl-object-map-bfrs x.test litarr))
                     ((when (eq test t))
                      (fgl-object-map-bfrs x.then litarr))
                     ((when (eq test nil))
                      (fgl-object-map-bfrs x.else litarr))
                     (then (fgl-object-map-bfrs x.then litarr))
                     (else (fgl-object-map-bfrs x.else litarr)))
                  (g-ite test then else)))
        (:g-apply (b* (((g-apply x))
                       (args (fgl-objectlist-map-bfrs x.args litarr)))
                    (change-g-apply x :args args)))
        (:g-map (b* (((g-map x))
                     (alist (fgl-object-alist-map-bfrs x.alist litarr)))
                  (change-g-map x :alist alist)))
        (t (b* (((g-cons x))
                (car (fgl-object-map-bfrs x.car litarr))
                (cdr (fgl-object-map-bfrs x.cdr litarr)))
             (g-cons car cdr))))))

  (define fgl-objectlist-map-bfrs ((x fgl-objectlist-p)
                                  litarr)
    :guard (and (< 0 (lits-length litarr))
                (bfr-listp (fgl-objectlist-bfrlist x)
                           (bfrstate (bfrmode :aignet) (1- (lits-length litarr)))))
    :returns (new-x fgl-objectlist-p)
    :measure (two-nats-measure (fgl-objectlist-count x) 0)
    (b* (((when (atom x))
          nil)
         (car (fgl-object-map-bfrs (car x) litarr))
         (cdr (fgl-objectlist-map-bfrs (cdr x) litarr)))
      (cons car cdr)))

  (define fgl-object-alist-map-bfrs ((x fgl-object-alist-p)
                                    litarr)
    :guard (and (< 0 (lits-length litarr))
                (bfr-listp (fgl-object-alist-bfrlist x)
                           (bfrstate (bfrmode :aignet) (1- (lits-length litarr)))))
    :returns (new-x fgl-object-alist-p)
    :measure (two-nats-measure (fgl-object-alist-count x) (len x))
    (b* (((when (atom x))
          x)
         ((unless (mbt (consp (car x))))
          (fgl-object-alist-map-bfrs (cdr x) litarr))
         (cdar (fgl-object-map-bfrs (cdar x) litarr))
         (cdr (fgl-object-alist-map-bfrs (cdr x) litarr)))
      (cons (cons (caar x) cdar) cdr)))
  ///
  (verify-guards fgl-object-map-bfrs
    :hints (("goal" :expand ((fgl-object-bfrlist x)
                             (fgl-object-alist-bfrlist x)))))

  (local (in-theory (enable bfr-listp-when-not-member-witness)))
  
  (local (defthm bfrstate-of-bfrstate->bound
           (implies (equal mode (bfrstate->mode bfrstate))
                    (equal (bfrstate mode (bfrstate->bound bfrstate))
                           (bfrstate-fix bfrstate)))
           :hints(("Goal" :in-theory (enable bfrstate-fix-redef)))))

  (defret-mutual bfr-listp-of-<fn>
    (defret bfr-listp-of-<fn>
      (implies (and (bfr-litarr-p (fgl-object-bfrlist x) litarr (bfrstate->bound bfrstate))
                    (equal (bfrstate->mode bfrstate) (bfrmode :aignet)))
               (bfr-listp (fgl-object-bfrlist new-x) bfrstate))
      :hints ('(:expand (<call>
                         (fgl-object-bfrlist x))))
      :fn fgl-object-map-bfrs)
    (defret bfr-listp-of-<fn>
      (implies (and (bfr-litarr-p (fgl-objectlist-bfrlist x) litarr (bfrstate->bound bfrstate))
                    (equal (bfrstate->mode bfrstate) (bfrmode :aignet)))
               (bfr-listp (fgl-objectlist-bfrlist new-x) bfrstate))
      :hints ('(:expand (<call>
                         (fgl-objectlist-bfrlist x))))
      :fn fgl-objectlist-map-bfrs)
    (defret bfr-listp-of-<fn>
      (implies (and (bfr-litarr-p (fgl-object-alist-bfrlist x) litarr (bfrstate->bound bfrstate))
                    (equal (bfrstate->mode bfrstate) (bfrmode :aignet)))
               (bfr-listp (fgl-object-alist-bfrlist new-x) bfrstate))
      :hints ('(:expand (<call>
                         (fgl-object-alist-bfrlist x))))
      :fn fgl-object-alist-map-bfrs))


  (local (in-theory (enable gobj-bfr-eval
                            GOBJ-BFR-LIST-EVAL-IS-BFR-LIST-EVAL)))

  (defret-mutual eval-of-<fn>
    (defret eval-of-<fn>
      (implies (bfr-litarr-correct-p (fgl-object-bfrlist x)
                                     (fgl-env->bfr-vals env)
                                     litarr logicman2 logicman)
               (equal (fgl-object-eval new-x env logicman2)
                      (fgl-object-eval x env logicman)))
      :hints ('(:expand (<call>
                         (fgl-object-bfrlist x)
                         (fgl-object-eval x env logicman))))
      :fn fgl-object-map-bfrs)
    (defret eval-of-<fn>
      (implies (bfr-litarr-correct-p (fgl-objectlist-bfrlist x)
                                     (fgl-env->bfr-vals env)
                                     litarr logicman2 logicman)
               (equal (fgl-objectlist-eval new-x env logicman2)
                      (fgl-objectlist-eval x env logicman)))
      :hints ('(:expand (<call>
                         (fgl-objectlist-bfrlist x)
                         (fgl-objectlist-eval x env logicman))))
      :fn fgl-objectlist-map-bfrs)
    (defret eval-of-<fn>
      (implies (bfr-litarr-correct-p (fgl-object-alist-bfrlist x)
                                     (fgl-env->bfr-vals env)
                                     litarr logicman2 logicman)
               (equal (fgl-object-alist-eval new-x env logicman2)
                      (fgl-object-alist-eval x env logicman)))
      :hints ('(:expand (<call>
                         (fgl-object-alist-bfrlist x)
                         (fgl-object-alist-eval x env logicman)
                         (fgl-object-alist-eval x env logicman2))))
      :fn fgl-object-alist-map-bfrs))


  (defret eval-of-<fn>-all-envs
    (implies (bfr-litarr-correct-p-all-envs (fgl-object-bfrlist x)
                                            litarr logicman2 logicman)
             (equal (fgl-object-eval new-x env logicman2)
                    (fgl-object-eval x env logicman)))
    :hints (("goal" :use eval-of-<fn>
             :in-theory (disable eval-of-<fn>)))
    :fn fgl-object-map-bfrs)
  (defret eval-of-<fn>-all-envs
      (implies (bfr-litarr-correct-p-all-envs (fgl-objectlist-bfrlist x)
                                     litarr logicman2 logicman)
               (equal (fgl-objectlist-eval new-x env logicman2)
                      (fgl-objectlist-eval x env logicman)))
    :hints (("goal" :use eval-of-<fn>
             :in-theory (disable eval-of-<fn>)))
      :fn fgl-objectlist-map-bfrs)
    (defret eval-of-<fn>-all-envs
      (implies (bfr-litarr-correct-p-all-envs (fgl-object-alist-bfrlist x)
                                     litarr logicman2 logicman)
               (equal (fgl-object-alist-eval new-x env logicman2)
                      (fgl-object-alist-eval x env logicman)))
    :hints (("goal" :use eval-of-<fn>
             :in-theory (disable eval-of-<fn>)))
      :fn fgl-object-alist-map-bfrs)

  (local (defthm fgl-object-bfrlist-of-mk-g-integer-open
           (equal (fgl-object-bfrlist (mk-g-integer bits))
                  (if (boolean-listp (true-list-fix bits))
                      nil
                    (true-list-fix bits)))
           :hints(("Goal" :in-theory (enable mk-g-integer fgl-object-bfrlist)))))

  (local (defthm fgl-object-bfrlist-of-mk-g-boolean-open
           (equal (fgl-object-bfrlist (mk-g-boolean bool))
                  (if (booleanp bool)
                      nil
                    (list bool)))
           :hints(("Goal" :in-theory (enable mk-g-boolean fgl-object-bfrlist)))))


  (defret-mutual bfrlist-boundedp-of-<fn>
    (defret bfrlist-boundedp-of-<fn>
      (implies (and (bfr-litarr-correct-p-all-envs (fgl-object-bfrlist x)
                                                   litarr logicman2 logicman)
                    (equal (logicman->mode logicman2)
                           (logicman->mode logicman))
                    (bfrlist-boundedp (fgl-object-bfrlist x) n logicman))
               (bfrlist-boundedp (fgl-object-bfrlist new-x) n logicman2))
      :hints ('(:expand (<call>
                         (fgl-object-bfrlist x))))
      :fn fgl-object-map-bfrs)
    (defret bfrlist-boundedp-of-<fn>
      (implies (and (bfr-litarr-correct-p-all-envs (fgl-objectlist-bfrlist x)
                                                   litarr logicman2 logicman)
                    (equal (logicman->mode logicman2)
                           (logicman->mode logicman))
                    (bfrlist-boundedp (fgl-objectlist-bfrlist x) n logicman))
               (bfrlist-boundedp (fgl-objectlist-bfrlist new-x) n logicman2))
      :hints ('(:expand (<call>
                         (fgl-objectlist-bfrlist x))))
      :fn fgl-objectlist-map-bfrs)
    (defret bfrlist-boundedp-of-<fn>
      (implies (and (bfr-litarr-correct-p-all-envs (fgl-object-alist-bfrlist x)
                                                   litarr logicman2 logicman)
                    (equal (logicman->mode logicman2)
                           (logicman->mode logicman))
                    (bfrlist-boundedp (fgl-object-alist-bfrlist x) n logicman))
               (bfrlist-boundedp (fgl-object-alist-bfrlist new-x) n logicman2))
      :hints ('(:expand (<call>
                         (fgl-object-alist-bfrlist x))))
      :fn fgl-object-alist-map-bfrs))

  (fty::deffixequiv-mutual fgl-object-map-bfrs
    :hints ('(:Expand ((fgl-objectlist-map-bfrs x litarr)
                       (fgl-objectlist-map-bfrs (fgl-objectlist-fix x) litarr)
                       (fgl-objectlist-map-bfrs nil litarr)
                       (fgl-object-map-bfrs x litarr)
                       (fgl-object-map-bfrs (fgl-object-fix x) litarr)
                       (fgl-object-alist-map-bfrs x litarr)
                       (fgl-object-alist-fix x)
                       (:free (x y) (fgl-object-alist-map-bfrs (cons x y) litarr)))))))

(define fgl-object-map-bfrs-memo-p (x &optional (litarr 'litarr))
  (if (atom x)
      (eq x nil)
    (and (consp (car x))
         (equal (cdar x) (ec-call (fgl-object-map-bfrs (caar x) litarr)))
         (fgl-object-map-bfrs-memo-p (cdr x) litarr)))
  ///
  (defthm fgl-object-map-bfrs-memo-p-of-cons
    (equal (fgl-object-map-bfrs-memo-p (cons (cons key val) x) litarr)
           (and (equal val (fgl-object-map-bfrs key litarr))
                (fgl-object-map-bfrs-memo-p x litarr))))

  (defthm fgl-object-map-bfrs-memo-p-of-nil
    (fgl-object-map-bfrs-memo-p nil litarr))

  (defthmd fgl-object-map-bfrs-memo-p-implies
    (implies (and (fgl-object-map-bfrs-memo-p x litarr)
                  (hons-assoc-equal key x))
             (equal (cdr (hons-assoc-equal key x))
                    (fgl-object-map-bfrs key litarr)))))


(define fgl-object-map-bfrs-memo-fix (x &optional (litarr 'litarr))
  :guard (fgl-object-map-bfrs-memo-p x litarr)
  :inline t
  :returns (new-x (fgl-object-map-bfrs-memo-p new-x litarr))
  :prepwork ((local (in-theory (enable fgl-object-map-bfrs-memo-p))))
  (mbe :logic
       (if (atom x)
           nil
         (if (and (consp (car x))
                  (equal (cdar x) (ec-call (fgl-object-map-bfrs (caar x) litarr))))
             (cons (car x)
                   (fgl-object-map-bfrs-memo-fix (cdr x) litarr))
           (fgl-object-map-bfrs-memo-fix (cdr x) litarr)))
       :exec x)
  ///
  (defthm fgl-object-map-bfrs-memo-fix-when-memo-p
    (implies (fgl-object-map-bfrs-memo-p x litarr)
             (equal (fgl-object-map-bfrs-memo-fix x litarr) x)))

  (defthm lookup-in-fgl-object-map-bfrs-memo-fix
    (let ((x (fgl-object-map-bfrs-memo-fix x litarr)))
      (implies (hons-assoc-equal key x)
               (equal (cdr (hons-assoc-equal key x))
                      (fgl-object-map-bfrs key litarr))))))



(defines fgl-object-map-bfrs-memo
  :ruler-extenders :lambdas
  (define fgl-object-map-bfrs-memo ((x fgl-object-p)
                                   litarr
                                   (memo fgl-object-map-bfrs-memo-p))
    :guard (and (< 0 (lits-length litarr))
                (bfr-listp (fgl-object-bfrlist x)
                           (bfrstate (bfrmode :aignet) (1- (lits-length litarr)))))
    :verify-guards nil
    :measure (two-nats-measure (fgl-object-count x) 0)
    :returns (mv new-x new-memo)
    (b* ((x (fgl-object-fix x))
         (memo (fgl-object-map-bfrs-memo-fix memo litarr))
         (kind (fgl-object-kind x))
         ((when (member-eq kind '(:g-concrete :g-var)))
          (mv x memo))
         (look (hons-get x memo))
         ((when look) (mv (cdr look) memo))
         ((mv ans memo)
          (case kind
            (:g-boolean (b* (((g-boolean x)))
                          (mv (mk-g-boolean (bfr-map x.bool litarr)) memo)))
            (:g-integer (b* (((g-integer x)))
                          (mv (mk-g-integer (bfrlist-map x.bits litarr)) memo)))
            (:g-ite (b* (((g-ite x))
                         ((mv test memo) (fgl-object-map-bfrs-memo x.test litarr memo))
                         ((when (eq test t))
                          (fgl-object-map-bfrs-memo x.then litarr memo))
                         ((when (eq test nil))
                          (fgl-object-map-bfrs-memo x.else litarr memo))
                         ((mv then memo) (fgl-object-map-bfrs-memo x.then litarr memo))
                         ((mv else memo) (fgl-object-map-bfrs-memo x.else litarr memo)))
                      (mv (g-ite test then else) memo)))
            (:g-apply (b* (((g-apply x))
                           ((mv args memo) (fgl-objectlist-map-bfrs-memo x.args litarr memo)))
                        (mv (change-g-apply x :args args) memo)))
            (:g-map (b* (((g-map x))
                         ((mv alist memo) (fgl-object-alist-map-bfrs-memo x.alist litarr memo)))
                      (mv (change-g-map x :alist alist) memo)))
            (t (b* (((g-cons x))
                    ((mv car memo) (fgl-object-map-bfrs-memo x.car litarr memo))
                    ((mv cdr memo) (fgl-object-map-bfrs-memo x.cdr litarr memo)))
                 (mv (g-cons car cdr) memo))))))
      (mv ans (hons-acons x ans memo))))

  (define fgl-objectlist-map-bfrs-memo ((x fgl-objectlist-p)
                                       litarr
                                       (memo fgl-object-map-bfrs-memo-p))
    :guard (and (< 0 (lits-length litarr))
                (bfr-listp (fgl-objectlist-bfrlist x)
                           (bfrstate (bfrmode :aignet) (1- (lits-length litarr)))))
    :measure (two-nats-measure (fgl-objectlist-count x) 0)
    :returns (mv new-x new-memo)
    (b* (((when (atom x))
          (mv nil (fgl-object-map-bfrs-memo-fix memo litarr)))
         ((mv car memo) (fgl-object-map-bfrs-memo (car x) litarr memo))
         ((mv cdr memo) (fgl-objectlist-map-bfrs-memo (cdr x) litarr memo)))
      (mv (cons car cdr) memo)))

  (define fgl-object-alist-map-bfrs-memo ((x fgl-object-alist-p)
                                         litarr
                                         (memo fgl-object-map-bfrs-memo-p))
    :guard (and (< 0 (lits-length litarr))
                (bfr-listp (fgl-object-alist-bfrlist x)
                           (bfrstate (bfrmode :aignet) (1- (lits-length litarr)))))
    :measure (two-nats-measure (fgl-object-alist-count x) (len x))
    :returns (mv new-x new-memo)
    (b* (((when (atom x))
          (mv x (fgl-object-map-bfrs-memo-fix memo litarr)))
         ((unless (mbt (consp (car x))))
          (fgl-object-alist-map-bfrs-memo (cdr x) litarr memo))
         ((mv cdar memo) (fgl-object-map-bfrs-memo (cdar x) litarr memo))
         ((mv cdr memo) (fgl-object-alist-map-bfrs-memo (cdr x) litarr memo)))
      (mv (cons (cons (caar x) cdar) cdr) memo)))
  ///
  (local (in-theory (enable fgl-object-map-bfrs-memo-p-implies)))

  (defret-mutual <fn>-correct
    (defret <fn>-correct
      (and (fgl-object-map-bfrs-memo-p new-memo litarr)
           (equal new-x (fgl-object-map-bfrs x litarr)))
      :hints ('(:expand (<call>
                         (fgl-object-map-bfrs x litarr))))
      :fn fgl-object-map-bfrs-memo)
    (defret <fn>-correct
      (and (fgl-object-map-bfrs-memo-p new-memo litarr)
           (equal new-x (fgl-objectlist-map-bfrs x litarr)))
      :hints ('(:expand (<call>
                         (fgl-objectlist-map-bfrs x litarr))))
      :fn fgl-objectlist-map-bfrs-memo)
    (defret <fn>-correct
      (and (fgl-object-map-bfrs-memo-p new-memo litarr)
           (equal new-x (fgl-object-alist-map-bfrs x litarr)))
      :hints ('(:expand (<call>
                         (fgl-object-alist-map-bfrs x litarr))))
      :fn fgl-object-alist-map-bfrs-memo))
  

  (verify-guards fgl-object-map-bfrs-memo
    :hints (("goal" :expand ((fgl-object-bfrlist x)
                             (fgl-object-alist-bfrlist x))))))
