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

(include-book "logicman-transform")
(include-book "stack-ev")
(include-book "constraint-db")
(include-book "scratch-isomorphic")

(defthm len-of-gl-objectlist-map-bfrs
  (equal (len (gl-objectlist-map-bfrs x litarr))
         (len x))
  :hints(("Goal" :in-theory (enable gl-objectlist-map-bfrs)
          :induct (len x))))

(local (std::add-default-post-define-hook :fix))

(defret concretize-of-<fn>
  (implies (bfr-litarr-correct-p (gl-object-bfrlist x)
                                 (gl-env->bfr-vals env)
                                 litarr logicman2 logicman)
           (equal (fgl-object-concretize new-x env logicman2)
                  (fgl-object-concretize x env logicman)))
  :hints(("Goal" :in-theory (enable fgl-object-concretize)))
  :fn gl-object-map-bfrs)


(defret concretize-of-<fn>
  (implies (bfr-litarr-correct-p (gl-objectlist-bfrlist x)
                                 (gl-env->bfr-vals env)
                                 litarr logicman2 logicman)
           (equal (fgl-objectlist-concretize new-x env logicman2)
                  (fgl-objectlist-concretize x env logicman)))
  :hints(("Goal" :in-theory (enable fgl-objectlist-concretize
                                    gl-objectlist-bfrlist
                                    gl-objectlist-map-bfrs)))
  :fn gl-objectlist-map-bfrs)

(defret concretize-of-<fn>
  (implies (bfr-litarr-correct-p (gl-object-alist-bfrlist x)
                                 (gl-env->bfr-vals env)
                                 litarr logicman2 logicman)
           (equal (fgl-object-alist-concretize new-x env logicman2)
                  (fgl-object-alist-concretize x env logicman)))
  :hints(("Goal" :in-theory (enable fgl-object-alist-concretize
                                    gl-object-alist-bfrlist
                                    gl-object-alist-map-bfrs)))
  :fn gl-object-alist-map-bfrs)


(define gl-object-bindings-map-bfrs ((x gl-object-bindings-p)
                                     litarr
                                     (memo gl-object-map-bfrs-memo-p))
  :prepwork ((local (defthm gl-object-alist-p-when-gl-object-bindings-p
                      (implies (gl-object-bindings-p x)
                               (gl-object-alist-p x))
                      :hints(("Goal" :in-theory (enable gl-object-alist-p
                                                        gl-object-bindings-p)))))

             (local (defthm gl-object-bindings-bfrlist-in-terms-of-gl-object-alist-bfrlist
                      (equal (gl-object-bindings-bfrlist x)
                             (gl-object-alist-bfrlist (gl-object-bindings-fix x)))
                      :hints(("Goal" :in-theory (enable gl-object-alist-bfrlist
                                                        gl-object-bindings-bfrlist
                                                        gl-object-bindings-fix)))))

             (local (defthm gl-object-bindings-p-of-gl-object-alist-map-bfrs
                      (implies (gl-object-bindings-p x)
                               (gl-object-bindings-p (gl-object-alist-map-bfrs x litarr)))
                      :hints(("Goal" :in-theory (enable gl-object-alist-map-bfrs
                                                        gl-object-bindings-p)
                              :induct (gl-object-bindings-p x)))))

             (local (defthm gl-object-bindings-eval-in-terms-of-gl-object-alist-eval
                      (equal (fgl-object-bindings-eval x env logicman)
                             (fgl-object-alist-eval (gl-object-bindings-fix x) env logicman))
                      :hints(("Goal" :in-theory (enable fgl-object-bindings-eval
                                                        fgl-object-alist-eval
                                                        gl-object-bindings-fix)
                              :induct (gl-object-bindings-fix x)))))
             

             (local (defthm gl-object-bindings-concretize-in-terms-of-gl-object-alist-concretize
                      (equal (fgl-object-bindings-concretize x env logicman)
                             (fgl-object-alist-concretize (gl-object-bindings-fix x) env logicman))
                      :hints(("Goal" :in-theory (enable fgl-object-bindings-concretize
                                                        fgl-object-alist-concretize
                                                        gl-object-bindings-fix)
                              :induct (gl-object-bindings-fix x))))))
  :guard (and (< 0 (lits-length litarr))
              (bfr-listp (gl-object-bindings-bfrlist x)
                         (bfrstate (bfrmode :aignet) (1- (lits-length litarr)))))
  :returns (mv (new-x gl-object-bindings-p)
               (new-memo gl-object-map-bfrs-memo-p))
  (gl-object-alist-map-bfrs-memo (gl-object-bindings-fix x) litarr memo)
  ///
  (defret bfr-listp-of-<fn>
    (implies (and (bfr-litarr-p (gl-object-bindings-bfrlist x) litarr
                                (bfrstate->bound bfrstate))
                  (equal (bfrstate->mode bfrstate) (bfrmode :aignet)))
             (bfr-listp (gl-object-bindings-bfrlist new-x) bfrstate)))

  (defret eval-of-<fn>
    (implies (bfr-litarr-correct-p (gl-object-bindings-bfrlist x)
                                   (gl-env->bfr-vals env)
                                   litarr logicman2 logicman)
             (equal (fgl-object-bindings-eval new-x env logicman2)
                    (fgl-object-bindings-eval x env logicman))))

  (defret concretize-of-<fn>
    (implies (bfr-litarr-correct-p (gl-object-bindings-bfrlist x)
                                   (gl-env->bfr-vals env)
                                   litarr logicman2 logicman)
             (equal (fgl-object-bindings-concretize new-x env logicman2)
                    (fgl-object-bindings-concretize x env logicman)))))


(define constraint-instance-map-bfrs ((x constraint-instance-p)
                                     litarr
                                     (memo gl-object-map-bfrs-memo-p))
  :guard (and (< 0 (lits-length litarr))
              (bfr-listp (constraint-instance-bfrlist x)
                         (bfrstate (bfrmode :aignet) (1- (lits-length litarr)))))
  :returns (mv (new-x constraint-instance-p)
               (new-memo gl-object-map-bfrs-memo-p))
  :prepwork ((local (in-theory (enable constraint-instance-bfrlist))))
  (b* (((constraint-instance x))
       ((mv subst memo) (gl-object-bindings-map-bfrs x.subst litarr memo)))
    (mv (change-constraint-instance
         x :subst subst)
        memo))
  ///
  (defret bfr-listp-of-<fn>
    (implies (and (bfr-litarr-p (constraint-instance-bfrlist x) litarr
                                (bfrstate->bound bfrstate))
                  (equal (bfrstate->mode bfrstate) (bfrmode :aignet)))
             (bfr-listp (constraint-instance-bfrlist new-x) bfrstate)))
  
  (defret concretize-of-<fn>
    (implies (bfr-litarr-correct-p (constraint-instance-bfrlist x)
                                   (gl-env->bfr-vals env)
                                   litarr logicman2 logicman)
             (equal (fgl-constraint-instance-concretize new-x env logicman2)
                    (fgl-constraint-instance-concretize x env logicman)))
    :hints(("Goal" :in-theory (enable fgl-constraint-instance-concretize)))))

(define constraint-instancelist-map-bfrs ((x constraint-instancelist-p)
                                     litarr
                                     (memo gl-object-map-bfrs-memo-p))
  :guard (and (< 0 (lits-length litarr))
              (bfr-listp (constraint-instancelist-bfrlist x)
                         (bfrstate (bfrmode :aignet) (1- (lits-length litarr)))))
  :returns (mv (new-x constraint-instancelist-p)
               (new-memo gl-object-map-bfrs-memo-p))
  :prepwork ((local (in-theory (enable constraint-instancelist-bfrlist))))
  (b* (((when (atom x)) (mv nil (gl-object-map-bfrs-memo-fix memo litarr)))
       ((mv car memo) (constraint-instance-map-bfrs (car x) litarr memo))
       ((mv cdr memo) (constraint-instancelist-map-bfrs (cdr x) litarr memo)))
    (mv (cons car cdr) memo))
  ///
  (defret bfr-listp-of-<fn>
    (implies (and (bfr-litarr-p (constraint-instancelist-bfrlist x) litarr
                                (bfrstate->bound bfrstate))
                  (equal (bfrstate->mode bfrstate) (bfrmode :aignet)))
             (bfr-listp (constraint-instancelist-bfrlist new-x) bfrstate)))
  
  (defret concretize-of-<fn>
    (implies (bfr-litarr-correct-p (constraint-instancelist-bfrlist x)
                                   (gl-env->bfr-vals env)
                                   litarr logicman2 logicman)
             (equal (fgl-constraint-instancelist-concretize new-x env logicman2)
                    (fgl-constraint-instancelist-concretize x env logicman)))
    :hints(("Goal" :in-theory (enable fgl-constraint-instancelist-concretize))))

  (defret len-of-<fn>
    (equal (len new-x)
           (len x))))

(local (defthm bfrstate-of-bfrstate->bound
         (implies (equal mode (bfrstate->mode bfrstate))
                  (equal (bfrstate mode (bfrstate->bound bfrstate))
                         (bfrstate-fix bfrstate)))
         :hints(("Goal" :in-theory (enable bfrstate-fix-redef)))))



(define scratchobj-map-bfrs ((x scratchobj-p)
                                     litarr
                                     (memo gl-object-map-bfrs-memo-p))
  :guard (and (< 0 (lits-length litarr))
              (bfr-listp (scratchobj->bfrlist x)
                         (bfrstate (bfrmode :aignet) (1- (lits-length litarr)))))
  :returns (mv (new-x scratchobj-p)
               (new-memo gl-object-map-bfrs-memo-p))
  :prepwork ((local (in-theory (e/d (scratchobj->bfrlist)
                                    (bfrlist-of-scratchobj-gl-obj->val
                                     bfrlist-of-scratchobj-gl-objlist->val
                                     bfrlist-of-scratchobj-bfr->val
                                     bfrlist-of-scratchobj-bfrlist->val
                                     bfrlist-of-scratchobj-cinst->val
                                     bfrlist-of-scratchobj-cinstlist->val)))))
  (scratchobj-case x
    :gl-obj (b* (((mv ans memo) (gl-object-map-bfrs-memo x.val litarr memo)))
              (mv (scratchobj-gl-obj ans) memo))
    :gl-objlist (b* (((mv ans memo) (gl-objectlist-map-bfrs-memo x.val litarr memo)))
                  (mv (scratchobj-gl-objlist ans) memo))
    :bfr (mv (scratchobj-bfr (bfr-map x.val litarr)) (gl-object-map-bfrs-memo-fix memo))
    :bfrlist (mv (scratchobj-bfrlist (bfrlist-map x.val litarr)) (gl-object-map-bfrs-memo-fix memo))
    :cinst (b* (((mv ans memo) (constraint-instance-map-bfrs x.val litarr memo)))
             (mv (scratchobj-cinst ans) memo))
    :cinstlist (b* (((mv ans memo) (constraint-instancelist-map-bfrs x.val litarr memo)))
                 (mv (scratchobj-cinstlist ans) memo)))
  ///
  (defret bfr-listp-of-<fn>
    (implies (and (bfr-litarr-p (scratchobj->bfrlist x) litarr
                                (bfrstate->bound bfrstate))
                  (equal (bfrstate->mode bfrstate) (bfrmode :aignet)))
             (bfr-listp (scratchobj->bfrlist new-x) bfrstate)))
  
  (local (in-theory (enable gobj-bfr-list-eval-is-bfr-list-eval)))

  (defret concretize-of-<fn>
    (implies (bfr-litarr-correct-p (scratchobj->bfrlist x)
                                   (gl-env->bfr-vals env)
                                   litarr logicman2 logicman)
             (equal (fgl-scratchobj-concretize new-x env logicman2)
                    (fgl-scratchobj-concretize x env logicman)))
    :hints(("Goal" :in-theory (enable fgl-scratchobj-concretize))))

  (defret scratchobj-isomorphic-of-<fn>
    (scratchobj-isomorphic new-x x)
    :hints(("Goal" :in-theory (enable scratchobj-isomorphic)))))

(define scratchlist-map-bfrs ((x scratchlist-p)
                                     litarr
                                     (memo gl-object-map-bfrs-memo-p))
  :guard (and (< 0 (lits-length litarr))
              (bfr-listp (scratchlist-bfrlist x)
                         (bfrstate (bfrmode :aignet) (1- (lits-length litarr)))))
  :returns (mv (new-x scratchlist-p)
               (new-memo gl-object-map-bfrs-memo-p))
  :prepwork ((local (in-theory (enable scratchlist-bfrlist))))
  (b* (((when (atom x)) (mv nil (gl-object-map-bfrs-memo-fix memo litarr)))
       ((mv car memo) (scratchobj-map-bfrs (car x) litarr memo))
       ((mv cdr memo) (scratchlist-map-bfrs (cdr x) litarr memo)))
    (mv (cons car cdr) memo))
  ///
  (defret bfr-listp-of-<fn>
    (implies (and (bfr-litarr-p (scratchlist-bfrlist x) litarr
                                (bfrstate->bound bfrstate))
                  (equal (bfrstate->mode bfrstate) (bfrmode :aignet)))
             (bfr-listp (scratchlist-bfrlist new-x) bfrstate)))
  
  (defret concretize-of-<fn>
    (implies (bfr-litarr-correct-p (scratchlist-bfrlist x)
                                   (gl-env->bfr-vals env)
                                   litarr logicman2 logicman)
             (equal (fgl-scratchlist-concretize new-x env logicman2)
                    (fgl-scratchlist-concretize x env logicman)))
    :hints(("Goal" :in-theory (enable fgl-scratchlist-concretize))))

  (defret scratchlist-isomorphic-of-<fn>
    (scratchlist-isomorphic new-x x)
    :hints(("Goal" :in-theory (enable scratchlist-isomorphic)))))


(define minor-frame-map-bfrs ((x minor-frame-p)
                                     litarr
                                     (memo gl-object-map-bfrs-memo-p))
  :guard (and (< 0 (lits-length litarr))
              (bfr-listp (minor-frame-bfrlist x)
                         (bfrstate (bfrmode :aignet) (1- (lits-length litarr)))))
  :returns (mv (new-x minor-frame-p)
               (new-memo gl-object-map-bfrs-memo-p))
  :prepwork ((local (in-theory (enable minor-frame-bfrlist))))
  (b* (((minor-frame x))
       ((mv bindings memo) (gl-object-bindings-map-bfrs x.bindings litarr memo))
       ((mv scratch memo) (scratchlist-map-bfrs x.scratch litarr memo)))
    (mv (change-minor-frame x :bindings bindings :scratch scratch)
        memo))
  ///
  (defret bfr-listp-of-<fn>
    (implies (and (bfr-litarr-p (minor-frame-bfrlist x) litarr
                                (bfrstate->bound bfrstate))
                  (equal (bfrstate->mode bfrstate) (bfrmode :aignet)))
             (bfr-listp (minor-frame-bfrlist new-x) bfrstate)))
  
  (defret concretize-of-<fn>
    (implies (bfr-litarr-correct-p (minor-frame-bfrlist x)
                                   (gl-env->bfr-vals env)
                                   litarr logicman2 logicman)
             (equal (fgl-minor-frame-concretize new-x env logicman2)
                    (fgl-minor-frame-concretize x env logicman)))
    :hints(("Goal" :in-theory (enable fgl-minor-frame-concretize))))

  (defret minor-frame-scratch-isomorphic-of-<fn>
    (minor-frame-scratch-isomorphic new-x x)
    :hints(("Goal" :in-theory (enable minor-frame-scratch-isomorphic)))))


(define minor-stack-map-bfrs ((x minor-stack-p)
                              litarr
                              (memo gl-object-map-bfrs-memo-p))
  :guard (and (< 0 (lits-length litarr))
              (bfr-listp (minor-stack-bfrlist x)
                         (bfrstate (bfrmode :aignet) (1- (lits-length litarr)))))
  :returns (mv (new-x minor-stack-p)
               (new-memo gl-object-map-bfrs-memo-p))
  :prepwork ((local (in-theory (enable minor-stack-bfrlist))))
  (b* (((mv car memo) (minor-frame-map-bfrs (car x) litarr memo))
       ((when (atom (cdr x))) (mv (list car) memo))
       ((mv cdr memo) (minor-stack-map-bfrs (cdr x) litarr memo)))
    (mv (cons car cdr) memo))
  ///
  (defret bfr-listp-of-<fn>
    (implies (and (bfr-litarr-p (minor-stack-bfrlist x) litarr
                                (bfrstate->bound bfrstate))
                  (equal (bfrstate->mode bfrstate) (bfrmode :aignet)))
             (bfr-listp (minor-stack-bfrlist new-x) bfrstate)))
  
  (defret concretize-of-<fn>
    (implies (bfr-litarr-correct-p (minor-stack-bfrlist x)
                                   (gl-env->bfr-vals env)
                                   litarr logicman2 logicman)
             (equal (fgl-minor-stack-concretize new-x env logicman2)
                    (fgl-minor-stack-concretize x env logicman)))
    :hints(("Goal" :in-theory (enable fgl-minor-stack-concretize))))

  (defret minor-stack-scratch-isomorphic-of-<fn>
    (minor-stack-scratch-isomorphic new-x x)
    :hints(("Goal" :in-theory (enable minor-stack-scratch-isomorphic)))))


(define major-frame-map-bfrs ((x major-frame-p)
                              litarr
                              (memo gl-object-map-bfrs-memo-p))
  :guard (and (< 0 (lits-length litarr))
              (bfr-listp (major-frame-bfrlist x)
                         (bfrstate (bfrmode :aignet) (1- (lits-length litarr)))))
  :returns (mv (new-x major-frame-p)
               (new-memo gl-object-map-bfrs-memo-p))
  :prepwork ((local (in-theory (enable major-frame-bfrlist))))
  (b* (((major-frame x))
       ((mv bindings memo) (gl-object-bindings-map-bfrs x.bindings litarr memo))
       ((mv minor-stack memo) (minor-stack-map-bfrs x.minor-stack litarr memo)))
    (mv (change-major-frame x :bindings bindings :minor-stack minor-stack)
        memo))
  ///
  (defret bfr-listp-of-<fn>
    (implies (and (bfr-litarr-p (major-frame-bfrlist x) litarr
                                (bfrstate->bound bfrstate))
                  (equal (bfrstate->mode bfrstate) (bfrmode :aignet)))
             (bfr-listp (major-frame-bfrlist new-x) bfrstate)))
  
  (defret concretize-of-<fn>
    (implies (bfr-litarr-correct-p (major-frame-bfrlist x)
                                   (gl-env->bfr-vals env)
                                   litarr logicman2 logicman)
             (equal (fgl-major-frame-concretize new-x env logicman2)
                    (fgl-major-frame-concretize x env logicman)))
    :hints(("Goal" :in-theory (enable fgl-major-frame-concretize))))

  (defret major-frame-scratch-isomorphic-of-<fn>
    (major-frame-scratch-isomorphic new-x x)
    :hints(("Goal" :in-theory (enable major-frame-scratch-isomorphic)))))


(define major-stack-map-bfrs ((x major-stack-p)
                              litarr
                              (memo gl-object-map-bfrs-memo-p))
  :guard (and (< 0 (lits-length litarr))
              (bfr-listp (major-stack-bfrlist x)
                         (bfrstate (bfrmode :aignet) (1- (lits-length litarr)))))
  :returns (mv (new-x major-stack-p)
               (new-memo gl-object-map-bfrs-memo-p))
  :prepwork ((local (in-theory (enable major-stack-bfrlist))))
  (b* (((mv car memo) (major-frame-map-bfrs (car x) litarr memo))
       ((when (atom (cdr x))) (mv (list car) memo))
       ((mv cdr memo) (major-stack-map-bfrs (cdr x) litarr memo)))
    (mv (cons car cdr) memo))
  ///
  (defret bfr-listp-of-<fn>
    (implies (and (bfr-litarr-p (major-stack-bfrlist x) litarr
                                (bfrstate->bound bfrstate))
                  (equal (bfrstate->mode bfrstate) (bfrmode :aignet)))
             (bfr-listp (major-stack-bfrlist new-x) bfrstate)))
  
  (defret concretize-of-<fn>
    (implies (bfr-litarr-correct-p (major-stack-bfrlist x)
                                   (gl-env->bfr-vals env)
                                   litarr logicman2 logicman)
             (equal (fgl-major-stack-concretize new-x env logicman2)
                    (fgl-major-stack-concretize x env logicman)))
    :hints(("Goal" :in-theory (enable fgl-major-stack-concretize))))

  (defret major-stack-scratch-isomorphic-of-<fn>
    (major-stack-scratch-isomorphic new-x x)
    :hints(("Goal" :in-theory (enable major-stack-scratch-isomorphic)))))


(define gl-object-bindingslist-map-bfrs ((x gl-object-bindingslist-p)
                                     litarr
                                     (memo gl-object-map-bfrs-memo-p))
  :guard (and (< 0 (lits-length litarr))
              (bfr-listp (gl-object-bindingslist-bfrlist x)
                         (bfrstate (bfrmode :aignet) (1- (lits-length litarr)))))
  :returns (mv (new-x gl-object-bindingslist-p)
               (new-memo gl-object-map-bfrs-memo-p))
  :prepwork ((local (in-theory (enable gl-object-bindingslist-bfrlist))))
  (b* (((when (atom x)) (mv nil (gl-object-map-bfrs-memo-fix memo litarr)))
       ((mv car memo) (gl-object-bindings-map-bfrs (car x) litarr memo))
       ((mv cdr memo) (gl-object-bindingslist-map-bfrs (cdr x) litarr memo)))
    (mv (cons car cdr) memo))
  ///
  (defret bfr-listp-of-<fn>
    (implies (and (bfr-litarr-p (gl-object-bindingslist-bfrlist x) litarr
                                (bfrstate->bound bfrstate))
                  (equal (bfrstate->mode bfrstate) (bfrmode :aignet)))
             (bfr-listp (gl-object-bindingslist-bfrlist new-x) bfrstate))))


(define sig-table-map-bfrs ((x sig-table-p)
                                     litarr
                                     (memo gl-object-map-bfrs-memo-p))
  :guard (and (< 0 (lits-length litarr))
              (bfr-listp (sig-table-bfrlist x)
                         (bfrstate (bfrmode :aignet) (1- (lits-length litarr)))))
  :returns (mv (new-x sig-table-p)
               (new-memo gl-object-map-bfrs-memo-p))
  :prepwork ((local (in-theory (enable sig-table-bfrlist))))
  (b* (((when (atom x)) (mv nil (gl-object-map-bfrs-memo-fix memo litarr)))
       ((unless (mbt (and (consp (car x))
                          (gl-objectlist-p (caar x)))))
        (sig-table-map-bfrs (cdr x) litarr memo))
       ((mv caar memo) (gl-objectlist-map-bfrs-memo (caar x) litarr memo))
       ((mv cdar memo) (gl-object-bindingslist-map-bfrs (cdar x) litarr memo))
       ((mv cdr memo) (sig-table-map-bfrs (cdr x) litarr memo)))
    (mv (hons-acons caar cdar cdr) memo))
  ///
  (defret bfr-listp-of-<fn>
    (implies (and (bfr-litarr-p (sig-table-bfrlist x) litarr
                                (bfrstate->bound bfrstate))
                  (equal (bfrstate->mode bfrstate) (bfrmode :aignet)))
             (bfr-listp (sig-table-bfrlist new-x) bfrstate)))

  (local (in-theory (enable sig-table-fix))))


(define constraint-tuple-map-bfrs ((x constraint-tuple-p)
                              litarr
                              (memo gl-object-map-bfrs-memo-p))
  :guard (and (< 0 (lits-length litarr))
              (bfr-listp (constraint-tuple-bfrlist x)
                         (bfrstate (bfrmode :aignet) (1- (lits-length litarr)))))
  :returns (mv (new-x constraint-tuple-p)
               (new-memo gl-object-map-bfrs-memo-p))
  :prepwork ((local (in-theory (enable constraint-tuple-bfrlist))))
  (b* (((constraint-tuple x))
       ((mv sig-table memo) (sig-table-map-bfrs x.sig-table litarr memo)))
    (mv (change-constraint-tuple x :sig-table sig-table)
        memo))
  ///
  (defret bfr-listp-of-<fn>
    (implies (and (bfr-litarr-p (constraint-tuple-bfrlist x) litarr
                                (bfrstate->bound bfrstate))
                  (equal (bfrstate->mode bfrstate) (bfrmode :aignet)))
             (bfr-listp (constraint-tuple-bfrlist new-x) bfrstate))))


(define constraint-tuplelist-map-bfrs ((x constraint-tuplelist-p)
                                     litarr
                                     (memo gl-object-map-bfrs-memo-p))
  :guard (and (< 0 (lits-length litarr))
              (bfr-listp (constraint-tuplelist-bfrlist x)
                         (bfrstate (bfrmode :aignet) (1- (lits-length litarr)))))
  :returns (mv (new-x constraint-tuplelist-p)
               (new-memo gl-object-map-bfrs-memo-p))
  :prepwork ((local (in-theory (enable constraint-tuplelist-bfrlist))))
  (b* (((when (atom x)) (mv nil (gl-object-map-bfrs-memo-fix memo litarr)))
       ((mv car memo) (constraint-tuple-map-bfrs (car x) litarr memo))
       ((mv cdr memo) (constraint-tuplelist-map-bfrs (cdr x) litarr memo)))
    (mv (cons car cdr) memo))
  ///
  (defret bfr-listp-of-<fn>
    (implies (and (bfr-litarr-p (constraint-tuplelist-bfrlist x) litarr
                                (bfrstate->bound bfrstate))
                  (equal (bfrstate->mode bfrstate) (bfrmode :aignet)))
             (bfr-listp (constraint-tuplelist-bfrlist new-x) bfrstate))))



(define constraint-db-map-bfrs ((x constraint-db-p)
                                     litarr
                                     (memo gl-object-map-bfrs-memo-p))
  :guard (and (< 0 (lits-length litarr))
              (bfr-listp (constraint-db-bfrlist x)
                         (bfrstate (bfrmode :aignet) (1- (lits-length litarr)))))
  :returns (mv (new-x constraint-db-p)
               (new-memo gl-object-map-bfrs-memo-p))
  :prepwork ((local (in-theory (enable constraint-db-bfrlist))))
  (b* (((when (atom x)) (mv nil (gl-object-map-bfrs-memo-fix memo litarr)))
       ((unless (mbt (and (consp (car x))
                          (pseudo-fnsym-p (caar x)))))
        (constraint-db-map-bfrs (cdr x) litarr memo))
       ((mv cdar memo) (constraint-tuplelist-map-bfrs (cdar x) litarr memo))
       ((mv cdr memo) (constraint-db-map-bfrs (cdr x) litarr memo)))
    (mv (hons-acons (caar x) cdar cdr) memo))
  ///
  (defret bfr-listp-of-<fn>
    (implies (and (bfr-litarr-p (constraint-db-bfrlist x) litarr
                                (bfrstate->bound bfrstate))
                  (equal (bfrstate->mode bfrstate) (bfrmode :aignet)))
             (bfr-listp (constraint-db-bfrlist new-x) bfrstate)))

  (local (in-theory (enable constraint-db-fix))))

