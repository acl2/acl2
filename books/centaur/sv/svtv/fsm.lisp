; SV - Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2014-2015 Centaur Technology
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
; Original authors: Sol Swords <sswords@centtech.com>

(in-package "SV")
(include-book "structure")
(include-book "../svex/unroll")
(include-book "../svex/rewrite-base")
(include-book "../svex/env-ops")
(include-book "centaur/misc/hons-extra" :dir :system)
(include-book "centaur/gl/gl-mbe" :dir :system)
(include-book "centaur/gl/def-gl-rewrite" :dir :system)
(local (include-book "centaur/misc/equal-sets" :dir :system))
(local (include-book "std/osets/element-list" :dir :system))
(local (include-book "std/osets/under-set-equiv" :dir :system))
(local (include-book "std/alists/hons-assoc-equal" :dir :system))
(local (include-book "std/basic/arith-equivs" :dir :system))
(local (include-book "std/lists/take" :dir :system))
(local (include-book "std/lists/nth" :dir :system))
(local (std::add-default-post-define-hook :fix))


;;===================================


(defthm alist-keys-of-svex-alist-eval
  (equal (alist-keys (svex-alist-eval x env))
         (svex-alist-keys x))
  :hints(("Goal" :in-theory (enable alist-keys svex-alist-keys svex-alist-eval))))

(local (defthmd member-alist-keys
         (iff (member v (alist-keys x))
              (hons-assoc-equal v x))
         :hints(("Goal" :in-theory (enable alist-keys)))))

(local (defthm svex-env-lookup-of-append
         (equal (svex-env-lookup v (append a b))
                (if (member (svar-fix v) (alist-keys (svex-env-fix a)))
                    (svex-env-lookup v a)
                  (svex-env-lookup v b)))
         :hints(("Goal" :in-theory (enable svex-env-lookup member-alist-keys)))))





(local (defthm alist-keys-of-svex-env-fix-of-svar-alist
         (implies (svar-alist-p x)
                  (equal (alist-keys (svex-env-fix x))
                         (alist-keys x)))
         :hints(("Goal" :in-theory (enable svar-alist-p svex-env-fix alist-keys)))))

(local (defthm noncycle-var-member-svex-add-cycle-num
         (implies (not (svex-cycle-var-p v))
                  (not (member (svar-fix v) (alist-keys (svar-alist-add-cycle-num env cycle)))))
         :hints(("Goal" :in-theory (enable svar-alist-add-cycle-num
                                           alist-keys
                                           svex-cycle-var-p)))))

(local (defthm svex-env-extract-of-append-cycles
         (implies (not (svarlist-has-svex-cycle-var keys))
                  (equal (svex-env-extract keys (append (svar-alist-add-cycle-num env cycle) rest))
                         (svex-env-extract keys rest)))
         :hints(("Goal" :in-theory (enable svex-env-extract svarlist-has-svex-cycle-var)))))

(defthm svex-cycle-envs-to-single-env-extract-non-cycle-keys
  (implies (not (svarlist-has-svex-cycle-var keys))
           (equal (svex-env-extract keys (svex-cycle-envs-to-single-env envs curr-cycle rest))
                  (svex-env-extract keys rest)))
  :hints(("Goal" :in-theory (enable svex-cycle-envs-to-single-env))))


(local (defthm len-equal-0
         (equal (equal (len x) 0)
                (not (consp x)))))

(local (in-theory (disable acl2::hons-dups-p)))


;; (defsection svex-eval-unroll-multienv-expand-cycle

;;   (defthm-svex-eval-unroll-multienv-flag
;;     (defthm svex-eval-unroll-multienv-at-cycle-0
;;       (equal (svex-eval-unroll-multienv x 0 nextstates in-envs orig-state)
;;              (svex-eval x (append (svex-env-extract (svex-alist-keys nextstates)
;;                                                     orig-state)
;;                                   (car in-envs))))
;;       :hints ('(:expand ((svex-eval-unroll-multienv x 0 nextstates in-envs orig-state)
;;                          (:free (env) (svex-eval x env)))))
;;       :flag svex-eval-unroll-multienv)
;;     (defthm svexlist-eval-unroll-multienv-at-cycle-0
;;       (equal (svexlist-eval-unroll-multienv x 0 nextstates in-envs orig-state)
;;              (svexlist-eval x (append (svex-env-extract (svex-alist-keys nextstates)
;;                                                         orig-state)
;;                                       (car in-envs))))
;;       :hints ('(:expand ((svexlist-eval-unroll-multienv x 0 nextstates in-envs orig-state)
;;                          (:free (env) (svexlist-eval x env)))))
;;       :flag svexlist-eval-unroll-multienv))

;;   (defthm-svex-eval-unroll-multienv-flag
;;     (defthm svex-eval-unroll-multienv-expand-cycle
;;       (implies (posp cycle)
;;                (equal (svex-eval-unroll-multienv x cycle nextstates in-envs orig-state)
;;                       (svex-eval-unroll-multienv x (1- cycle)
;;                                                  nextstates
;;                                                  (cdr in-envs)
;;                                                  (svex-alist-eval nextstates
;;                                                                   (append (svex-env-extract (svex-alist-keys nextstates)
;;                                                                                             orig-state)
;;                                                                           (car in-envs))))))
;;       :hints ('(:expand ((:free (cycle in-envs orig-state)
;;                           (svex-eval-unroll-multienv x cycle nextstates in-envs orig-state)))))
;;       :flag svex-eval-unroll-multienv)
;;     (defthm svexlist-eval-unroll-multienv-expand-cycle
;;       (implies (posp cycle)
;;                (equal (svexlist-eval-unroll-multienv x cycle nextstates in-envs orig-state)
;;                       (svexlist-eval-unroll-multienv x (1- cycle)
;;                                                      nextstates
;;                                                      (cdr in-envs)
;;                                                      (svex-alist-eval nextstates
;;                                                                       (append (svex-env-extract (svex-alist-keys nextstates)
;;                                                                                                 orig-state)
;;                                                                               (car in-envs))))))
;;       :hints ('(:expand ((:free (cycle in-envs orig-state)
;;                           (svexlist-eval-unroll-multienv x cycle nextstates in-envs orig-state)))))
;;       :flag svexlist-eval-unroll-multienv))

;;   (in-theory (disable svex-eval-unroll-multienv-expand-cycle
;;                       svexlist-eval-unroll-multienv-expand-cycle)))

(local (in-theory (disable acl2::hons-dups-p)))

(define svtv-fsm-step ((in svex-env-p)
                       (prev-st svex-env-p)
                       (x svtv-p))
  :guard (and (equal (alist-keys prev-st) (svex-alist-keys (svtv->nextstate x)))
              (not (acl2::hons-dups-p (svex-alist-keys (svtv->nextstate x)))))
  :returns (next-st svex-env-p)
  (b* (((svtv x))
       (current-cycle-env (make-fast-alist (append (mbe :logic (svex-env-extract (svex-alist-keys x.nextstate)
                                                                                 prev-st)
                                                        :exec prev-st)
                                                   (svex-env-fix in)))))
    (svex-alist-eval x.nextstate current-cycle-env))
  ///
  (defret alist-keys-of-svtv-fsm-step
    (equal (alist-keys next-st)
           (svex-alist-keys (svtv->nextstate x)))))

(define svtv-fsm-step-outs ((in svex-env-p)
                            (prev-st svex-env-p)
                            (x svtv-p))
  :guard (and (equal (alist-keys prev-st) (svex-alist-keys (svtv->nextstate x)))
              (not (acl2::hons-dups-p (svex-alist-keys (svtv->nextstate x)))))
  :returns (next-st svex-env-p)
  (b* (((svtv x))
       (current-cycle-env (make-fast-alist (append (mbe :logic (svex-env-extract (svex-alist-keys x.nextstate)
                                                                                 prev-st)
                                                        :exec prev-st)
                                                   (svex-env-fix in)))))
    (svex-alist-eval x.outexprs current-cycle-env)))

(define svtv-fsm-final-state ((ins svex-envlist-p)
                              (prev-st svex-env-p)
                              (x svtv-p))
  :guard (and (equal (alist-keys prev-st) (svex-alist-keys (svtv->nextstate x)))
              (not (acl2::hons-dups-p (svex-alist-keys (svtv->nextstate x)))))
  :returns (final-st svex-env-p)
  (b* (((svtv x)))
    (if (atom ins)
        (mbe :logic (svex-env-extract (svex-alist-keys x.nextstate)
                                      prev-st)
             :exec prev-st)
      (svtv-fsm-final-state (cdr ins)
                            (svtv-fsm-step (car ins) prev-st x)
                            x))))


(define svtv-fsm-eval ((ins svex-envlist-p)
                       (prev-st svex-env-p)
                       (x svtv-p))
  :guard (and (equal (alist-keys prev-st) (svex-alist-keys (svtv->nextstate x)))
              (not (acl2::hons-dups-p (svex-alist-keys (svtv->nextstate x)))))
  :returns (outs svex-envlist-p)
  (b* (((when (atom ins)) nil)
       ((svtv x))
       (current-cycle-env (make-fast-alist (append (mbe :logic (svex-env-extract (svex-alist-keys x.nextstate)
                                                                                 prev-st)
                                                        :exec prev-st)
                                                   (svex-env-fix (car ins)))))
       (outs (svex-alist-eval x.outexprs current-cycle-env)))
    (mbe :logic (b* ((next-st (svex-alist-eval x.nextstate current-cycle-env)))
                  (clear-memoize-table 'svex-eval)
                  (fast-alist-free current-cycle-env)
                  (cons outs (svtv-fsm-eval (cdr ins) next-st x)))
         :exec (b* (((when (atom (cdr ins)))
                     (clear-memoize-table 'svex-eval)
                     (fast-alist-free current-cycle-env)
                     (list outs))
                    (next-st (svex-alist-eval x.nextstate current-cycle-env)))
                 (clear-memoize-table 'svex-eval)
                 (fast-alist-free current-cycle-env)
                 (cons outs (svtv-fsm-eval (cdr ins) next-st x)))))
  ///
  (defthm car-of-svtv-fsm-eval
    (equal (car (svtv-fsm-eval ins prev-st x))
           (and (consp ins)
                (svtv-fsm-step-outs (car ins) prev-st x)))
    :hints(("Goal" :in-theory (enable svtv-fsm-step-outs))))

  (defthm cdr-of-svtv-fsm-eval
    (equal (cdr (svtv-fsm-eval ins prev-st x))
           (and (consp ins)
                (svtv-fsm-eval (cdr ins) (svtv-fsm-step (car ins) prev-st x) x)))
    :hints(("Goal" :in-theory (enable svtv-fsm-step))))

  (defthm svtv-fsm-eval-of-cons
    (Equal (svtv-fsm-eval (cons a b) prev-st x)
           (cons (svtv-fsm-step-outs a prev-st x)
                 (svtv-fsm-eval b (svtv-fsm-step a prev-st x) x)))
    :hints(("Goal" :in-theory (enable svtv-fsm-eval
                                      svtv-fsm-step
                                      svtv-fsm-step-outs))))


  (defthm consp-of-svtv-fsm-eval
    (equal (consp (svtv-fsm-eval ins prev-st x))
           (consp ins)))






  (defun svtv-fsm-eval-is-svex-eval-unroll-multienv-ind (n ins prev-st x)
    (if (zp n)
        (list ins prev-st x)
      (b* (((svtv x))
           (current-cycle-env (make-fast-alist (append (mbe :logic (svex-env-extract (svex-alist-keys x.nextstate)
                                                                                     prev-st)
                                                            :exec prev-st)
                                                       (svex-env-fix (car ins)))))
           (next-st (svex-alist-eval x.nextstate current-cycle-env)))
        (svtv-fsm-eval-is-svex-eval-unroll-multienv-ind (1- n) (cdr ins) next-st x))))

  (local (defthm svex-alist-eval-is-pairlis$
           (equal (pairlis$ (svex-alist-keys x)
                            (svexlist-eval (svex-alist-vals x) env))
                  (svex-alist-eval x env))
           :hints(("Goal" :in-theory (enable svex-alist-keys
                                             svex-alist-vals
                                             svex-alist-eval)))))

  (defthm len-of-svtv-fsm-eval
    (equal (len (svtv-fsm-eval ins prev-st x))
           (len ins)))

  (defthm svtv-fsm-eval-of-extract-states-from-prev-st
    (equal (svtv-fsm-eval ins (svex-env-extract (svex-alist-keys (svtv->nextstate x)) prev-st) x)
           (svtv-fsm-eval ins prev-st x))
    :hints(("Goal" :in-theory (enable svtv-fsm-eval))))

  (defthm svtv-fsm-eval-of-reduce-states-from-prev-st
    (equal (svtv-fsm-eval ins (svex-env-reduce (svex-alist-keys (svtv->nextstate x)) prev-st) x)
           (svtv-fsm-eval ins prev-st x))
    :hints(("Goal" :in-theory (enable svtv-fsm-eval))))

  (defthmd svtv-fsm-eval-is-svex-eval-unroll-multienv
    (implies (< (nfix n) (len ins))
             (equal (nth n (svtv-fsm-eval ins prev-st x))
                    (pairlis$ (svex-alist-keys (svtv->outexprs x))
                              (svexlist-eval-unroll-multienv (svex-alist-vals (svtv->outexprs x))
                                                             n (svtv->nextstate x) ins prev-st))))
    :hints (("goal" :induct (svtv-fsm-eval-is-svex-eval-unroll-multienv-ind n ins prev-st x)
             :expand ((svtv-fsm-eval ins prev-st x))
             :in-theory (enable svexlist-eval-unroll-multienv-expand-cycle
                                svexlist-eval-unroll-multienv-at-cycle-0))))

  (local (defun nthcdr-of-svtv-fsm-eval-ind (n ins prev-st svtv)
           (if (zp n)
               (list ins prev-st)
             (b* (((svtv x) svtv)
                  (current-cycle-env (make-fast-alist (append (mbe :logic (svex-env-extract (svex-alist-keys x.nextstate)
                                                                                            prev-st)
                                                                   :exec prev-st)
                                                              (svex-env-fix (car ins)))))
                  (next-st (svex-alist-eval x.nextstate current-cycle-env)))
               (nthcdr-of-svtv-fsm-eval-ind (1- n) (cdr ins) next-st svtv)))))

  (defthm nthcdr-of-svtv-fsm-eval-is-svtv-fsm-eval
    (equal (nthcdr n (svtv-fsm-eval ins initst svtv))
           (svtv-fsm-eval (nthcdr n ins)
                          (svex-unroll-state (svtv->nextstate svtv)
                                             (take n ins)
                                             initst)
                          svtv))
    :hints (("goal" :induct (nthcdr-of-svtv-fsm-eval-ind n ins initst svtv)
             :expand ((:free (x) (nthcdr n x))
                      (:free (x) (take n x))
                      (:free (nextstate a b) (svex-unroll-state nextstate (cons a b) initst))
                      (:free (nextstate) (svex-unroll-state nextstate nil initst))))
            (and stable-under-simplificationp
                 '(:expand ((svtv-fsm-eval ins initst svtv))
                   :in-theory (enable svtv-fsm-step)))))



  (local (defun svtv-fsm-eval-+-n-m-ind (n m ins prev-st x)
           (b* (((svtv x))
                (current-cycle-env (make-fast-alist (append (mbe :logic (svex-env-extract (svex-alist-keys x.nextstate)
                                                                                          prev-st)
                                                                 :exec prev-st)
                                                            (svex-env-fix (car ins)))))
                ((when (zp n))
                 (list n m ins prev-st x))
                (next-st (svex-alist-eval x.nextstate current-cycle-env)))
             (clear-memoize-table 'svex-eval)
             (fast-alist-free current-cycle-env)
             (svtv-fsm-eval-+-n-m-ind (1- n) (1- (nfix m)) (cdr ins) next-st x))))

  (defthm lookup-in-fsm-eval-of-take
    (implies (and (< (nfix n) (len ins))
                  (< (nfix n) (nfix m)))
             (equal (nth n (svtv-fsm-eval (take m ins) initst svtv))
                    (nth n (svtv-fsm-eval ins initst svtv))))
    :hints (("Goal" :induct (svtv-fsm-eval-+-n-m-ind n m ins initst svtv)
             :expand ((svtv-fsm-eval ins initst svtv)
                      (:free (a b) (svtv-fsm-eval (cons a b) initst svtv))
                      (take m ins)
                      (svtv-fsm-eval nil initst svtv)
                      (svtv-fsm-step-outs (car ins) initst svtv)
                      (svtv-fsm-step (car ins) initst svtv))))))


;; thms about take and nth
(local (fty::deflist svex-envlist :elt-type svex-env :true-listp t :elementp-of-nil t))


(define svtv-fsm-eval-states ((ins svex-envlist-p)
                         (prev-st svex-env-p)
                         (x svtv-p))
  :guard (and (equal (alist-keys prev-st) (svex-alist-keys (svtv->nextstate x)))
              (not (acl2::hons-dups-p (svex-alist-keys (svtv->nextstate x)))))
  :returns (outs svex-envlist-p)
  (b* (((when (atom ins)) nil)
       ((svtv x))
       (current-cycle-env (make-fast-alist (append (mbe :logic (svex-env-extract (svex-alist-keys x.nextstate)
                                                                                 prev-st)
                                                        :exec prev-st)
                                                   (svex-env-fix (car ins)))))
       (next-st (svex-alist-eval x.nextstate current-cycle-env)))
    (clear-memoize-table 'svex-eval)
    (fast-alist-free current-cycle-env)
    (cons next-st (svtv-fsm-eval-states (cdr ins) next-st x)))
  ///
  (defthm car-of-svtv-fsm-eval-states
    (equal (car (svtv-fsm-eval-states ins prev-st x))
           (and (consp ins)
                (svtv-fsm-step (car ins) prev-st x)))
    :hints(("Goal" :in-theory (enable svtv-fsm-step))))

  (defthm cdr-of-svtv-fsm-eval-states
    (equal (cdr (svtv-fsm-eval-states ins prev-st x))
           (and (consp ins)
                (svtv-fsm-eval-states (cdr ins) (svtv-fsm-step (car ins) prev-st x) x)))
    :hints(("Goal" :in-theory (enable svtv-fsm-step))))

  (defthm svtv-fsm-eval-states-of-cons
    (Equal (svtv-fsm-eval-states (cons a b) prev-st x)
           (b* ((nextst (svtv-fsm-step a prev-st x)))
             (cons nextst
                   (svtv-fsm-eval-states b nextst x))))
    :hints(("Goal" :in-theory (enable svtv-fsm-eval-states
                                      svtv-fsm-step
                                      svtv-fsm-step-outs))))


  (defthm consp-of-svtv-fsm-eval-states
    (equal (consp (svtv-fsm-eval-states ins prev-st x))
           (consp ins)))






  (defun svtv-fsm-eval-states-is-svex-eval-unroll-multienv-ind (n ins prev-st x)
    (if (zp n)
        (list ins prev-st x)
      (b* (((svtv x))
           (current-cycle-env (make-fast-alist (append (mbe :logic (svex-env-extract (svex-alist-keys x.nextstate)
                                                                                     prev-st)
                                                            :exec prev-st)
                                                       (svex-env-fix (car ins)))))
           (next-st (svex-alist-eval x.nextstate current-cycle-env)))
        (svtv-fsm-eval-states-is-svex-eval-unroll-multienv-ind (1- n) (cdr ins) next-st x))))

  (local (defthm svex-alist-eval-is-pairlis$
           (equal (pairlis$ (svex-alist-keys x)
                            (svexlist-eval (svex-alist-vals x) env))
                  (svex-alist-eval x env))
           :hints(("Goal" :in-theory (enable svex-alist-keys
                                             svex-alist-vals
                                             svex-alist-eval)))))

  (defthm len-of-svtv-fsm-eval-states
    (equal (len (svtv-fsm-eval-states ins prev-st x))
           (len ins)))

  (defthm svtv-fsm-eval-states-of-extract-states-from-prev-st
    (equal (svtv-fsm-eval-states ins (svex-env-extract (svex-alist-keys (svtv->nextstate x)) prev-st) x)
           (svtv-fsm-eval-states ins prev-st x))
    :hints(("Goal" :in-theory (enable svtv-fsm-eval-states))))

  (defthmd svtv-fsm-eval-states-is-svex-eval-unroll-multienv
    (implies (< (nfix n) (len ins))
             (equal (nth n (svtv-fsm-eval-states ins prev-st x))
                    (pairlis$ (svex-alist-keys (svtv->nextstate x))
                              (svexlist-eval-unroll-multienv (svex-alist-vals (svtv->nextstate x))
                                                             n (svtv->nextstate x) ins prev-st))))
    :hints (("goal" :induct (svtv-fsm-eval-states-is-svex-eval-unroll-multienv-ind n ins prev-st x)
             :expand ((svtv-fsm-eval-states ins prev-st x))
             :in-theory (enable svexlist-eval-unroll-multienv-expand-cycle
                                svexlist-eval-unroll-multienv-at-cycle-0))))

  (local (defun nthcdr-of-svtv-fsm-eval-states-ind (n ins prev-st svtv)
           (if (zp n)
               (list ins prev-st)
             (b* (((svtv x) svtv)
                  (current-cycle-env (make-fast-alist (append (mbe :logic (svex-env-extract (svex-alist-keys x.nextstate)
                                                                                            prev-st)
                                                                   :exec prev-st)
                                                              (svex-env-fix (car ins)))))
                  (next-st (svex-alist-eval x.nextstate current-cycle-env)))
               (nthcdr-of-svtv-fsm-eval-states-ind (1- n) (cdr ins) next-st svtv)))))

  (defthm nthcdr-of-svtv-fsm-eval-states-is-svtv-fsm-eval-states
    (equal (nthcdr n (svtv-fsm-eval-states ins initst svtv))
           (svtv-fsm-eval-states (nthcdr n ins)
                          (svex-unroll-state (svtv->nextstate svtv)
                                             (take n ins)
                                             initst)
                          svtv))
    :hints (("goal" :induct (nthcdr-of-svtv-fsm-eval-states-ind n ins initst svtv)
             :expand ((:free (x) (nthcdr n x))
                      (:free (x) (take n x))
                      (:free (nextstate a b) (svex-unroll-state nextstate (cons a b) initst))
                      (:free (nextstate) (svex-unroll-state nextstate nil initst))))
            (and stable-under-simplificationp
                 '(:expand ((svtv-fsm-eval-states ins initst svtv))
                   :in-theory (enable svtv-fsm-step)))))

  (defthm nth-of-svtv-fsm-eval-states-is-svex-unroll-state
    (implies (and (< (nfix n) (len ins))
                  (no-duplicatesp (svex-alist-keys (svtv->nextstate svtv))))
             (equal (nth n (svtv-fsm-eval-states ins initst svtv))
                    (svex-unroll-state (svtv->nextstate svtv)
                                       (take (+ 1 (nfix n)) ins) initst)))
    :hints (("goal" :induct (nthcdr-of-svtv-fsm-eval-states-ind n ins initst svtv)
             :in-theory (enable svtv-fsm-step)
             :expand ((:free (x) (nthcdr n x))
                      (:free (x) (take n x))
                      (svtv-fsm-eval-states ins initst svtv)
                      (:free (nextstate a b initst) (svex-unroll-state nextstate (cons a b) initst))
                      (:free (nextstate initst) (svex-unroll-state nextstate nil initst))))))



  (local (defun svtv-fsm-eval-states-+-n-m-ind (n m ins prev-st x)
           (b* (((svtv x))
                (current-cycle-env (make-fast-alist (append (mbe :logic (svex-env-extract (svex-alist-keys x.nextstate)
                                                                                          prev-st)
                                                                 :exec prev-st)
                                                            (svex-env-fix (car ins)))))
                ((when (zp n))
                 (list n m ins prev-st x))
                (next-st (svex-alist-eval x.nextstate current-cycle-env)))
             (clear-memoize-table 'svex-eval)
             (fast-alist-free current-cycle-env)
             (svtv-fsm-eval-states-+-n-m-ind (1- n) (1- (nfix m)) (cdr ins) next-st x))))

  (defthm lookup-in-fsm-eval-states-of-take
    (implies (and (< (nfix n) (len ins))
                  (< (nfix n) (nfix m)))
             (equal (nth n (svtv-fsm-eval-states (take m ins) initst svtv))
                    (nth n (svtv-fsm-eval-states ins initst svtv))))
    :hints (("Goal" :induct (svtv-fsm-eval-states-+-n-m-ind n m ins initst svtv)
             :expand ((svtv-fsm-eval-states ins initst svtv)
                      (:free (a b) (svtv-fsm-eval-states (cons a b) initst svtv))
                      (take m ins)
                      (svtv-fsm-eval-states nil initst svtv)
                      (svtv-fsm-step-outs (car ins) initst svtv)
                      (svtv-fsm-step (car ins) initst svtv))))))






(define svex-envlist-extract ((keys svarlist-list-p)
                              (envs svex-envlist-p))
  :returns (new-envs svex-envlist-p)
  (if (atom keys)
      nil
    (cons (svex-env-extract (car keys) (car envs))
          (svex-envlist-extract (cdr keys) (cdr envs))))
  ///
  (defthm svex-envlist-extract-lookup
    (implies (member (svar-fix var) (svarlist-fix (nth n signals)))
             (equal (svex-env-lookup var (nth n (svex-envlist-extract signals x)))
                    (svex-env-lookup var (nth n x))))
    :hints(("Goal" :in-theory (enable nth svex-envlist-extract
                                      default-car nthcdr)
            :induct (list (nthcdr n signals) (nthcdr n x))))))



(local (defthm take-of-svex-envlist-fix
         (svex-envlist-equiv (take n (svex-envlist-fix x))
                             (take n x))
         :hints(("Goal" :in-theory (e/d (svex-envlist-fix)
                                        (acl2::take-of-zero
                                         acl2::take-of-too-many
                                         acl2::take-when-atom))))))


(define svtv-fsm-run ((ins svex-envlist-p)
                      (prev-st svex-env-p)
                      (x svtv-p)
                      (signals svarlist-list-p))
  :guard (and (equal (alist-keys prev-st) (svex-alist-keys (svtv->nextstate x)))
              (not (acl2::hons-dups-p (svex-alist-keys (svtv->nextstate x)))))
  :guard-debug t
  :returns (outs svex-envlist-p)
  (svex-envlist-extract signals (svtv-fsm-eval (take (len signals) ins) prev-st x))

  ///

  ;; (defthm svtv-fsm-eval-of-take
  ;;   (implies (posp n)
  ;;            (equal (sv::svtv-fsm-eval (take n ins) initst svtv)
  ;;                   (take n (sv::svtv-fsm-eval ins initst svtv))))
  ;;   :hints(("Goal" :induct (svtv-fsm-eval-+-n-ind n ins initst svtv)
  ;;           :expand ((svtv-fsm-eval ins initst svtv)
  ;;                    (:free (a b) (svtv-fsm-eval (cons a b) initst svtv))))))

  (defthm svtv-fsm-run-lookup-is-eval-lookup
    (implies (member (svar-fix var) (svarlist-fix (nth n signals)))
             (equal (svex-env-lookup var (nth n (svtv-fsm-run ins initst svtv signals)))
                    (svex-env-lookup var (nth n (svtv-fsm-eval (take (len signals) ins) initst svtv)))))
    :hints(("Goal" :in-theory (enable svtv-fsm-run)))))


(define svtv-fsm-run-states ((ins svex-envlist-p)
                             (prev-st svex-env-p)
                             (x svtv-p)
                             (signals svarlist-list-p))
  :guard (and (equal (alist-keys prev-st) (svex-alist-keys (svtv->nextstate x)))
              (not (acl2::hons-dups-p (svex-alist-keys (svtv->nextstate x)))))
  :guard-debug t
  :returns (outs svex-envlist-p)
  (svex-envlist-extract signals (svtv-fsm-eval-states (take (len signals) ins) prev-st x))

  ///

  ;; (defthm svtv-fsm-eval-of-take
  ;;   (implies (posp n)
  ;;            (equal (sv::svtv-fsm-eval (take n ins) initst svtv)
  ;;                   (take n (sv::svtv-fsm-eval ins initst svtv))))
  ;;   :hints(("Goal" :induct (svtv-fsm-eval-+-n-ind n ins initst svtv)
  ;;           :expand ((svtv-fsm-eval ins initst svtv)
  ;;                    (:free (a b) (svtv-fsm-eval (cons a b) initst svtv))))))

  (defthm svtv-fsm-run-states-lookup-is-eval-lookup
    (implies (member (svar-fix var) (svarlist-fix (nth n signals)))
             (equal (svex-env-lookup var (nth n (svtv-fsm-run-states ins initst x signals)))
                    (svex-env-lookup var (nth n (svtv-fsm-eval-states (take (len signals) ins) initst x)))))
    :hints(("Goal" :in-theory (enable svtv-fsm-run)))))

(define svtv-fsm-run-outs-and-states ((ins svex-envlist-p)
                                      (prev-st svex-env-p)
                                      (svtv svtv-p)
                                      &key
                                      (out-signals svarlist-list-p)
                                      (state-signals svarlist-list-p))
  :guard (and (equal (alist-keys prev-st) (svex-alist-keys (svtv->nextstate svtv)))
              (not (acl2::hons-dups-p (svex-alist-keys (svtv->nextstate svtv)))))
  (mv (svtv-fsm-run ins prev-st svtv out-signals)
      (svtv-fsm-run-states ins prev-st svtv state-signals)))








;; (define svtv-fsm-run-symbolic1 ((signals svarlist-list-p)
;;                                 (cycle natp)
;;                                 (x svtv-p)
;;                                 (env svex-env-p))
;;   :returns (outs svex-envlist-p)
;;   (if (atom signals)
;;       nil
;;     (cons (svex-alist-eval
;;            (pairlis$ (car signals)
;;                      (svexlist-compose*-unroll (svex-alist-vals (svex-alist-extract (Car signals) (svtv->outexprs x)))
;;                                                cycle (svtv->nextstate x)))

(define svtv-fsm-run-spec ((signals svarlist-list-p)
                           (cycle natp)
                           (outs svex-alist-p)
                           (nextstate svex-alist-p)
                           (env svex-env-p))
  (if (atom signals)
      nil
    (cons (pairlis$ (svarlist-fix (car signals))
                    (svexlist-eval-unroll-multienv
                     (svex-alist-vals (svex-alist-extract (car signals) outs))
                     cycle
                     nextstate
                     (svex-env-to-cycle-envs env (+ (lnfix cycle) (len signals)))
                     (svex-env-extract (svex-alist-keys nextstate) env)))
          (svtv-fsm-run-spec (cdr signals) (1+ (lnfix cycle)) outs nextstate env)))
  ///


  (local (defthm consp-by-len
           (implies (and (equal consp (posp (len x)))
                         (syntaxp (quotep consp)))
                    (iff (consp x) consp))))

  (local (defthm svex-envlist-extract-when-not-consp
           (implies (not (consp signals))
                    (equal (svex-envlist-extract signals envs) nil))
           :hints(("Goal" :in-theory (enable svex-envlist-extract)))))

  (local (defthm len-cdr
           (implies (and (equal len (len x))
                         (syntaxp (case-match len
                                    (('quote &) t)
                                    (('binary-+ ''1 foo)
                                     (not (case-match foo
                                            (('len ('cdr y)) (equal y x))
                                            (& nil))))
                                    (& nil))))
                    (equal (len (cdr x))
                           (max 0 (+ -1 (len x)))))))

  (local (include-book "std/lists/nthcdr" :dir :system))

  ;; (local (defthm car-of-svtv-fsm-eval
  ;;          (implies (consp ins)
  ;;                   (equal (car (svtv-fsm-eval ins prev-st x))
  ;;                          (pairlis$ (svex-alist-keys (svtv->outexprs x))
  ;;                                    (svexlist-eval-unroll-multienv
  ;;                                     (svex-alist-vals (svtv->outexprs x))
  ;;                                     0 (svtv->nextstate x) ins prev-st))))
  ;;          :hints (("goal" :in-theory (enable nth len)
  ;;                   :use ((:instance svtv-fsm-eval-is-svex-eval-unroll-multienv
  ;;                          (n 0)))))))



  (local (in-theory (enable SVEXLIST-EVAL-UNROLL-MULTIENV-IN-TERMS-OF-SVEX-UNROLL-STATE)))

  (local (defthm svex-unroll-state-of-svex-unroll-state
           (equal (svex-unroll-state nextstate ins1 (svex-unroll-state nextstate ins2 prevst))
                  (svex-unroll-state nextstate (append ins2 ins1) prevst))
           :hints(("Goal" :in-theory (enable svex-unroll-state)
                   :induct (svex-unroll-state nextstate ins2 prevst))
                  (and stable-under-simplificationp
                       '(:expand ((:free (prevst)
                                   (svex-unroll-state nextstate ins1 prevst))))))))


  (local (defthm pairlis$-is-svex-alist-eval
           (equal (pairlis$ (svex-alist-keys alist)
                            (svexlist-eval (svex-alist-vals alist) env))
                  (svex-alist-eval alist env))
           :hints(("Goal" :in-theory (enable svex-alist-keys
                                             svex-alist-vals
                                             svex-alist-eval)))))



  (local (defthm pairlis$-is-svex-env-extract-of-eval
           (implies (and (syntaxp (or (equal signals1 signals)
                                      (case-match signals1
                                        (('svarlist-fix$inline x) (equal x signals))
                                        (& nil))))
                         (svarlist-p signals1)
                         (svarlist-equiv signals1 signals))
                    (equal (pairlis$ signals1
                                     (svexlist-eval (svex-alist-vals (svex-alist-extract signals alist)) env))
                           (svex-env-extract signals (svex-alist-eval alist env))))
           :hints(("Goal" :in-theory (enable svex-env-extract
                                             svex-alist-extract
                                             svex-alist-vals
                                             pairlis$
                                             svarlist-fix)))))

  ;; (local (defthm svex-env-extract-of-pairlis$-eval-alist
  ;;          (equal (svex-env-extract signals (pairlis$ (svex-alist-keys alist)
  ;;                                                     (svexlist-eval (svex-alist-vals alist) env)))
  ;;                 (pairlis$ (svarlist-fix signals)
  ;;                           (svexlist-eval (svex-alist-vals (svex-env-extract signals alist)) env)))
  ;;          :hints(("Goal" :in-theory (enable svex-alist-keys
  ;;                                            svex-alist-vals
  ;;                                            svexlist-eval
  ;;                                            svex-env-extract
  ;;                                            pairlis$
  ;;                                            svarlist-fix)))))

  (local (defthmd svtv-fsm-eval-expand
           (implies (consp (cdr ins))
                    (equal (svtv-fsm-eval ins prev-st x)
                           (b* (((svtv x))
                                (current-cycle-env (make-fast-alist (append (mbe :logic (svex-env-extract (svex-alist-keys x.nextstate)
                                                                                                          prev-st)
                                                                                 :exec prev-st)
                                                                            (svex-env-fix (car ins)))))
                                (outs (svex-alist-eval x.outexprs current-cycle-env))
                                ((when (atom (cdr ins)))
                                 (clear-memoize-table 'svex-eval)
                                 (fast-alist-free current-cycle-env)
                                 (list outs))
                                (next-st (svex-alist-eval x.nextstate current-cycle-env)))
                             (clear-memoize-table 'svex-eval)
                             (fast-alist-free current-cycle-env)
                             (cons outs (svtv-fsm-eval (cdr ins) next-st x)))))
           :hints(("Goal" :in-theory (enable svtv-fsm-eval)))))

  (local (defthmd svtv-fsm-eval-states-expand
           (implies (consp (cdr ins))
                    (equal (svtv-fsm-eval-states ins prev-st x)
                           (b* (((when (atom ins)) nil)
                                ((svtv x))
                                (current-cycle-env (make-fast-alist (append (mbe :logic (svex-env-extract (svex-alist-keys x.nextstate)
                                                                                                          prev-st)
                                                                                 :exec prev-st)
                                                                            (svex-env-fix (car ins)))))
                                (next-st (svex-alist-eval x.nextstate current-cycle-env)))
                             (clear-memoize-table 'svex-eval)
                             (fast-alist-free current-cycle-env)
                             (cons next-st (svtv-fsm-eval-states (cdr ins) next-st x)))))
           :hints(("Goal" :in-theory (enable svtv-fsm-eval-states)))))

  (local (in-theory (disable acl2::take nthcdr)))

  (local (defthm dumb
           (equal (+ a (- a) b)
                  (fix b))))

  (local (defthm len-gt-0
           (implies (consp x)
                    (< 0 (len x)))))


  (local (defthm dumb2
           (implies (< 0 len)
                    (< (+ 1 cyc)
                       (+ 1 cyc len)))))

  (local (defthm cdr-of-nthcdr
           (equal (cdr (nthcdr n x))
                  (nthcdr (+ 1 (nfix n)) x))
           :hints(("Goal" :in-theory (enable nthcdr)))))

  (defthm svtv-fsm-run-spec-is-svtv-fsm-run
    ;; (implies (consp signals)
    (equal (svtv-fsm-run-spec signals cycle (svtv->outexprs x) (svtv->nextstate x) env)
           (b* ((in-envs (svex-env-to-cycle-envs env (+ (len signals) (nfix cycle)))))
             (svtv-fsm-run (nthcdr cycle in-envs)
                           (svex-unroll-state (svtv->nextstate x)
                                              (take cycle in-envs)
                                              (svex-env-extract (svex-alist-keys (svtv->nextstate x)) env))
                           x signals)))
    :hints (("goal" :induct (svtv-fsm-run-spec signals cycle (svtv->outexprs x) (svtv->nextstate x) env)
             :in-theory (enable svtv-fsm-run svtv-fsm-step-outs svtv-fsm-step)
             :expand ((:free (envs) (svex-envlist-extract signals envs))))
            (and stable-under-simplificationp
                 '(:in-theory (enable svtv-fsm-eval-expand
                                      svex-unroll-state-unroll-backward)
                   :cases ((consp (cdr signals)))))))

  (defthm svtv-fsm-run-spec-is-svtv-fsm-run-states
    (equal (svtv-fsm-run-spec signals cycle (svtv->nextstate x) (svtv->nextstate x) env)
           (b* ((in-envs (svex-env-to-cycle-envs env (+ (len signals) (nfix cycle)))))
             (svtv-fsm-run-states (nthcdr cycle in-envs)
                                  (svex-unroll-state (svtv->nextstate x)
                                                     (take cycle in-envs)
                                                     (svex-env-extract (svex-alist-keys (svtv->nextstate x)) env))
                                  x signals)))
    :hints (("goal" :induct (svtv-fsm-run-spec signals cycle (svtv->nextstate x) (svtv->nextstate x) env)
             :in-theory (enable svtv-fsm-run-states svtv-fsm-step-outs svtv-fsm-step)
             :expand ((:free (envs) (svex-envlist-extract signals envs)))
             :do-not-induct t
             :do-not '(generalize fertilize))
            (and stable-under-simplificationp
                 '(:in-theory (enable svtv-fsm-eval-expand
                                      svex-unroll-state-unroll-backward)
                   :cases ((consp (cdr signals))))))))


(defthm len-of-svexlist-compose*-unroll
  (equal (len (svexlist-compose*-unroll x cycle nextstate))
         (len x))
  :hints(("Goal" :in-theory (enable svexlist-compose*-unroll))))

(defthm len-of-svex-alist-extract
  (equal (len (svex-alist-extract vars x))
         (len vars))
  :hints(("Goal" :in-theory (enable svex-alist-extract))))

(local
 (defthm len-of-svex-alist-vals2
   (implies (svex-alist-p x)
            (equal (len (svex-alist-vals x)) (len x)))
   :hints(("Goal" :in-theory (enable svex-alist-vals svex-alist-keys svex-alist-p)))))

(defthm svex-alist-eval-of-pairlis$
  (implies (and (equal (len keys) (len vals))
                (svarlist-p keys))
           (equal (svex-alist-eval (pairlis$ keys vals) env)
                  (pairlis$ keys (svexlist-eval vals env))))
  :hints(("Goal" :in-theory (enable svex-alist-eval svexlist-eval pairlis$))))

(define svex-alistlist-key-lists ((x svex-alistlist-p))
  :returns (keys svarlist-list-p)
  (if (atom x)
      nil
    (cons (svex-alist-keys (car x))
          (svex-alistlist-key-lists (cdr x)))))


(define svtv-fsm-run-svex-alists ((signals svarlist-list-p)
                                  (cycle natp)
                                  (outexprs svex-alist-p)
                                  (nextstate svex-alist-p))
  :returns (outs svex-alistlist-p)
  (if (atom signals)
      nil
    (cons (pairlis$ (svarlist-fix (car signals))
                    (svexlist-compose*-unroll (svex-alist-vals (svex-alist-extract (car signals) outexprs))
                                              cycle nextstate))
          (svtv-fsm-run-svex-alists (cdr signals) (1+ (lnfix cycle)) outexprs nextstate)))
  ///
  (local (defthmd svexlist-eval-unroll-is-unroll-multienv-here
           (implies (and (bind-free '((ncycles . (binary-+ '1 (binary-+ (nfix cycle) (len (cdr signals)))))) (ncycles))
                         (< (nfix cycle) (nfix ncycles)))
                    (equal (svexlist-eval-unroll x cycle nextstates env)
                           (svexlist-eval-unroll-multienv x cycle nextstates
                                                      (svex-env-to-cycle-envs env ncycles)
                                                      (svex-env-extract (svex-alist-keys nextstates) env))))
           :hints (("goal" :use svexlist-eval-unroll-is-unroll-multienv))))

  (defret svex-alistlist-eval-of-<fn>
    (equal (svex-alistlist-eval outs env)
           (svtv-fsm-run-spec signals cycle outexprs nextstate env))
    :hints(("Goal" :in-theory (enable svtv-fsm-run-spec
                                      svexlist-eval-unroll-is-unroll-multienv-here)
            :induct (svtv-fsm-run-spec signals cycle outexprs nextstate env))))

  (defret svex-alistlist-key-list-of-svtv-fsm-run-svex-alists
    (equal (svex-alistlist-key-lists outs)
           (svarlist-list-fix signals))
    :hints(("Goal" :in-theory (enable svex-alistlist-key-lists)))))

(define append-svex-alist-vals ((x svex-alistlist-p))
  :returns (vals svexlist-p)
  (if (atom x)
      nil
    (append (svex-alist-vals (car x))
            (append-svex-alist-vals (cdr x)))))




(define svtv-fsm-run-symbolic-svexlist ((signals svarlist-list-p)
                                        (cycle natp)
                                        (outexprs svex-alist-p)
                                        (nextstate svex-alist-p))
  :returns (outs svexlist-p)
  (if (atom signals)
      nil
    (append (svexlist-compose*-unroll (svex-alist-vals (svex-alist-extract (car signals) outexprs))
                                      cycle nextstate)
            (svtv-fsm-run-symbolic-svexlist (cdr signals) (1+ (lnfix cycle)) outexprs nextstate)))
  ///
  (defretd <fn>-is-append-vals-of-svtv-fsm-run-svex-alists
    (equal outs
           (append-svex-alist-vals
            (svtv-fsm-run-svex-alists signals cycle outexprs nextstate)))
    :hints(("Goal" :in-theory (enable append-svex-alist-vals
                                      svtv-fsm-run-svex-alists)))))




(define svtv-fsm-run-symbolic-svexlist->alists ((signals svarlist-list-p)
                                                (vals 4veclist-p))
  :hooks nil

  :prepwork ((local (include-book "std/lists/take" :dir :system))
             (local (defthm 4veclist-p-of-nthcdr
                      (implies (4veclist-p x)
                               (4veclist-p (nthcdr n x)))
                      :hints(("Goal" :in-theory (enable nthcdr 4veclist-p)))))
             (local (defthm 4veclist-p-of-take
                      (implies (and (4veclist-p x)
                                    (<= (nfix n) (len x)))
                               (4veclist-p (take n x)))
                      :hints(("Goal" :in-theory (enable 4veclist-p)))))
             (local (defthm svex-env-p-of-pairlis$
                      (implies (and (equal (len x) (len y))
                                    (svarlist-p x) (4veclist-p y))
                               (svex-env-p (pairlis$ x y)))
                      :hints(("Goal" :in-theory (enable svex-env-p pairlis$)))))
             (local (defthm len-of-nthcdr
                      (implies (<= (nfix n) (len x))
                               (equal (len (nthcdr n x))
                                      (- (len x) (nfix n)))))))
  :returns (alists svex-envlist-p :hyp (and (4veclist-p vals)
                                            (<= (sum-of-lengths signals) (len vals))))
  (b* (((when (atom signals)) nil)
       (len (len (car signals))))
    (cons (pairlis$ (svarlist-fix (car signals))
                    (take len vals))
          (svtv-fsm-run-symbolic-svexlist->alists (cdr signals) (nthcdr len vals))))
  ///

  (defthm nthcdr-of-append
    (implies (equal (nfix n) (len x))
             (equal (nthcdr n (append x y))
                    y))
    :hints (("goal" :induct (nthcdr n x))))

  (local (defthm pairlis$-of-svexlist-eval
           (equal (pairlis$ (svex-alist-keys x) (svexlist-eval (svex-alist-vals x) env))
                  (svex-alist-eval x env))
           :hints(("Goal" :in-theory (enable svex-alist-eval svex-alist-vals svex-alist-keys)))))

  (local (defthm svtv-fsm-run-symbolic-svexlist->alists-of-append-alist-vals
           (equal (svtv-fsm-run-symbolic-svexlist->alists
                   (svex-alistlist-key-lists x)
                   (svexlist-eval (append-svex-alist-vals x) env))
                  (svex-alistlist-eval x env))
           :hints(("Goal" :in-theory (enable svex-alistlist-eval
                                             append-svex-alist-vals
                                             svex-alistlist-key-lists)))))

  (fty::deffixequiv svtv-fsm-run-symbolic-svexlist->alists :omit (vals))

  (defthm svtv-fsm-run-symbolic-svexlist->alists-of-append-alist-vals-of-eval
    (implies (equal (svarlist-list-fix keys) (svex-alistlist-key-lists x))
             (equal (svtv-fsm-run-symbolic-svexlist->alists
                     keys
                     (svexlist-eval
                      (append-svex-alist-vals x)
                      env))
                    (svex-alistlist-eval x env)))
    :hints (("goal" :use svtv-fsm-run-symbolic-svexlist->alists-of-append-alist-vals
             :in-theory (disable svtv-fsm-run-symbolic-svexlist->alists-of-append-alist-vals)
             :do-not-induct t)))

  (local (defthmd nthcdr-of-append-less
           (implies (<= (nfix n) (len x))
                    (equal (nthcdr n (append x y))
                           (append (nthcdr n x) y)))
           :hints(("Goal" :in-theory (enable nthcdr append)))))

  (defthm svtv-fsm-run-symbolic-svexlist->alists-of-append-excess
    (implies (<= (sum-of-lengths keys) (len x))
             (equal (svtv-fsm-run-symbolic-svexlist->alists keys (append x y))
                    (svtv-fsm-run-symbolic-svexlist->alists keys x)))
    :hints(("Goal" :in-theory (enable svtv-fsm-run-symbolic-svexlist->alists
                                      sum-of-lengths
                                      nthcdr-of-append-less)
            :induct (svtv-fsm-run-symbolic-svexlist->alists keys x)
            :expand ((:free (x) (svtv-fsm-run-symbolic-svexlist->alists keys x)))))))

(local
 (progn

   (defthm svtv-fsm-eval-of-prev-st-cycle-envs-to-single-env
     (implies (not (svarlist-has-svex-cycle-var (svex-alist-keys (svtv->nextstate x))))
              (equal (svtv-fsm-eval ins (svex-cycle-envs-to-single-env ins2 cyc rest) x)
                     (svtv-fsm-eval ins rest x)))
     :hints(("Goal" :expand ((:free (prev-st) (svtv-fsm-eval ins prev-st x))))))

   (defthm svtv-fsm-eval-states-of-prev-st-cycle-envs-to-single-env
     (implies (not (svarlist-has-svex-cycle-var (svex-alist-keys (svtv->nextstate x))))
              (equal (svtv-fsm-eval-states ins (svex-cycle-envs-to-single-env ins2 cyc rest) x)
                     (svtv-fsm-eval-states ins rest x)))
     :hints(("Goal" :expand ((:free (prev-st) (svtv-fsm-eval-states ins prev-st x))))))))


(define svtv-fsm-symbolic-env ((ins svex-envlist-p)
                               (statevars svarlist-p)
                               (prev-st svex-env-p))
  :enabled t
  ;; Make this opaque to GL, at least when envs are term-level
  (make-fast-alist (svex-cycle-envs-to-single-env ins 0 (svex-env-reduce statevars prev-st))))

(define svtv-fsm-run-symbolic-svexlist-memo ((signals svarlist-list-p)
                                             (outexprs svex-alist-p)
                                             (nextstate svex-alist-p))
  :enabled t
  (svtv-fsm-run-symbolic-svexlist signals 0 outexprs nextstate)
  ///
  (memoize 'svtv-fsm-run-symbolic-svexlist-memo))




(define svtv-fsm-run-outs-and-states-symbolic ((ins svex-envlist-p)
                                               (prev-st svex-env-p)
                                               (x svtv-p)
                                               &key
                                               (out-signals svarlist-list-p)
                                               (state-signals svarlist-list-p))
  :prepwork ((local (defthm nthcdr-of-len-append
                      (equal (nthcdr (len x) (append x y)) y)))
             (local (defthm nthcdr-append-of-same-len
                      (implies (equal (nfix n) (len x))
                               (equal (nthcdr n (append x y))
                                      y))
                      :hints(("Goal" :do-not-induct t
                              :use nthcdr-of-len-append
                              :in-theory (e/d* (acl2::arith-equiv-forwarding)
                                               (nthcdr-of-len-append)))))))
  :guard (and (equal (alist-keys prev-st) (svex-alist-keys (svtv->nextstate x)))
              (not (acl2::hons-dups-p (svex-alist-keys (svtv->nextstate x)))))
  (b* (((svtv x))
       ((when (and (atom out-signals) (atom state-signals)))
        (mv nil nil))
       (statevars (svex-alist-keys x.nextstate))
       ((when (svarlist-has-svex-cycle-var statevars))
        ;; bad!
        (mv (gl::gl-hide (svtv-fsm-run ins prev-st x out-signals))
            (gl::gl-hide (svtv-fsm-run-states ins prev-st x state-signals))))
       (x.outexprs (make-fast-alist x.outexprs))
       (x.nextstate (make-fast-alist x.nextstate))
       (env (svtv-fsm-symbolic-env ins statevars prev-st))
       (out-svexes (svtv-fsm-run-symbolic-svexlist-memo out-signals x.outexprs x.nextstate))
       (state-svexes (svtv-fsm-run-symbolic-svexlist-memo state-signals x.nextstate x.nextstate))
       (- (clear-memoize-table 'svex-compose*-unroll))
       (all-svexes (append out-svexes state-svexes))
       (values (svexlist-eval-for-symbolic all-svexes env '((:allvars . t))))
       (out-len (len out-svexes))
       (out-values (take out-len values))
       (state-values (nthcdr out-len values)))
    (mv (svtv-fsm-run-symbolic-svexlist->alists out-signals out-values)
        (svtv-fsm-run-symbolic-svexlist->alists state-signals state-values)))
  ///

  (local (defthm svex-envlist-extract-of-atom
           (implies (not (consp keys))
                    (equal (svex-envlist-extract keys x)
                           nil))
           :hints(("Goal" :in-theory (enable svex-envlist-extract)))))


  (local (defthm svarlist-has-cycle-var-of-env-reduce
           (implies (not (svarlist-has-svex-cycle-var vars))
                    (not (svarlist-has-svex-cycle-var
                          (intersection$ vars keys))))
           :hints(("Goal" :in-theory (enable svarlist-has-svex-cycle-var
                                             intersection-equal)))))

  (defthm svtv-fsm-run-outs-and-states-symbolic-is-svtv-fsm-run
    (equal (svtv-fsm-run-outs-and-states-symbolic ins prev-st x
                                                  :out-signals out-signals
                                                  :state-signals state-signals)
           (svtv-fsm-run-outs-and-states ins prev-st x :out-signals out-signals
                                         :state-signals state-signals))
    :hints (("goal" :in-theory (e/d (svtv-fsm-run-symbolic-svexlist-is-append-vals-of-svtv-fsm-run-svex-alists
                                     svtv-fsm-run-outs-and-states
                                     svex-unroll-state)))
            (and stable-under-simplificationp
                 '(:in-theory (enable svtv-fsm-run svtv-fsm-eval
                                      svtv-fsm-run-states svtv-fsm-eval-states
                                      svex-envlist-extract)
                   :do-not-induct t))))

  (gl::def-gl-rewrite svtv-fsm-run-is-symbolic
    (equal (svtv-fsm-run ins prev-st x signals)
           (b* (((mv outs ?states) (svtv-fsm-run-outs-and-states-symbolic ins prev-st x :out-signals signals)))
             outs))
    :hints(("Goal" :in-theory (enable svtv-fsm-run-outs-and-states))))

  (gl::def-gl-rewrite svtv-fsm-run-states-is-symbolic
    (equal (svtv-fsm-run-states ins prev-st x signals)
           (b* (((mv ?outs states) (svtv-fsm-run-outs-and-states-symbolic ins prev-st x :state-signals signals)))
             states))
    :hints(("Goal" :in-theory (enable svtv-fsm-run-outs-and-states)))))
