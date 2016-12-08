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
(local (include-book "centaur/misc/arith-equivs" :dir :system))
(local (include-book "std/lists/take" :dir :system))
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

(define svtv-fsm-eval ((ins svex-envlist-p)
                       (prev-st svex-env-p)
                       (x svtv-p))
  :guard (and (consp ins)
              (equal (alist-keys prev-st) (svex-alist-keys (svtv->nextstate x)))
              (not (acl2::hons-dups-p (svex-alist-keys (svtv->nextstate x)))))
  :returns (outs svex-envlist-p)
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
    (cons outs (svtv-fsm-eval (cdr ins) next-st x)))
  ///
  (defthm svtv-fsm-eval-of-cons
    (Equal (svtv-fsm-eval (cons a b) prev-st x)
           (b* ((alist (append (svex-env-extract (svex-alist-keys (svtv->nextstate x)) prev-st)
                               (svex-env-fix a))))
             (cons (svex-alist-eval (svtv->outexprs x) alist)
                   (if (atom b)
                       nil
                     (svtv-fsm-eval b
                                   (svex-alist-eval (svtv->nextstate x) alist) x)))))
    :hints(("Goal" :in-theory (enable svtv-fsm-eval))))




  


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
    (implies (consp ins)
             (equal (len (svtv-fsm-eval ins prev-st x))
                    (len ins))))

  (defthm svtv-fsm-eval-is-svex-eval-unroll-multienv
    (implies (< (nfix n) (len ins))
             (equal (nth n (svtv-fsm-eval ins prev-st x))
                    (pairlis$ (svex-alist-keys (svtv->outexprs x))
                              (svexlist-eval-unroll-multienv (svex-alist-vals (svtv->outexprs x))
                                                         n (svtv->nextstate x) ins prev-st))))
    :hints (("goal" :induct (svtv-fsm-eval-is-svex-eval-unroll-multienv-ind n ins prev-st x)
             :expand ((svtv-fsm-eval ins prev-st x))
             :in-theory (enable svexlist-eval-unroll-multienv-expand-cycle
                                svexlist-eval-unroll-multienv-at-cycle-0)))))

(fty::deflist svarlist-list :elt-type svarlist :true-listp t)

(define svex-envlist-extract ((keys svarlist-list-p)
                              (envs svex-envlist-p))
  :returns (new-envs svex-envlist-p)
  (if (atom keys)
      nil
    (cons (svex-env-extract (car keys) (car envs))
          (svex-envlist-extract (cdr keys) (cdr envs)))))


;; thms about take
(local (fty::deflist svex-envlist :elt-type svex-env :true-listp t :elementp-of-nil t))

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
  :guard (and (consp signals)
              (equal (alist-keys prev-st) (svex-alist-keys (svtv->nextstate x)))
              (not (acl2::hons-dups-p (svex-alist-keys (svtv->nextstate x)))))
  :guard-debug t
  (svex-envlist-extract signals (svtv-fsm-eval (take (len signals) ins) prev-st x)))







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

(local
 (define svtv-fsm-run-spec ((signals svarlist-list-p)
                            (cycle natp)
                            (x svtv-p)
                            (env svex-env-p))
   (if (atom signals)
       nil
     (cons (pairlis$ (svarlist-fix (car signals))
                     (svexlist-eval-unroll-multienv
                      (svex-alist-vals (svex-alist-extract (car signals) (svtv->outexprs x)))
                      cycle
                      (svtv->nextstate x)
                      (svex-env-to-cycle-envs env (+ (lnfix cycle) (len signals)))
                      (svex-env-extract (svex-alist-keys (svtv->nextstate x)) env)))
           (svtv-fsm-run-spec (cdr signals) (1+ (lnfix cycle)) x env)))
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
   (local (include-book "std/lists/take" :dir :system))
   (local (include-book "std/lists/nth" :dir :system))

   (local (defthm car-of-svtv-fsm-eval
            (implies (consp ins)
                     (equal (car (svtv-fsm-eval ins prev-st x))
                            (pairlis$ (svex-alist-keys (svtv->outexprs x))
                                      (svexlist-eval-unroll-multienv
                                       (svex-alist-vals (svtv->outexprs x))
                                       0 (svtv->nextstate x) ins prev-st))))
            :hints (("goal" :in-theory (enable nth len)
                     :use ((:instance svtv-fsm-eval-is-svex-eval-unroll-multienv
                            (n 0)))))))

   (local (defthm svex-env-extract-of-superset
            (implies (subsetp (svarlist-fix keys) (svarlist-fix keys2))
                     (Equal (svex-env-extract keys (svex-env-extract keys2 x))
                            (svex-env-extract keys x)))
            :hints(("Goal" :in-theory (enable svex-env-extract svarlist-fix)))))

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

   (local (defthm svex-env-extract-states-from-unroll-state
            (equal (svex-env-extract (svex-alist-keys nextstate)
                                     (svex-unroll-state nextstate ins prev-st))
                   (svex-unroll-state nextstate ins prev-st))
            :hints(("Goal" :in-theory (enable svex-unroll-state)))))

   (local (defthm svtv-fsm-eval-of-extract-states-from-prev-st
            (equal (svtv-fsm-eval ins (svex-env-extract (svex-alist-keys (svtv->nextstate x)) prev-st) x)
                   (svtv-fsm-eval ins prev-st x))
            :hints(("Goal" :in-theory (enable svtv-fsm-eval)))))

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

   (local (in-theory (disable ACL2::TAKE-REDEFINITION nthcdr)))

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
     (implies (consp signals)
              (equal (svtv-fsm-run-spec signals cycle x env)
                     (b* ((in-envs (svex-env-to-cycle-envs env (+ (len signals) (nfix cycle)))))
                       (svtv-fsm-run (nthcdr cycle in-envs)
                                     (svex-unroll-state (svtv->nextstate x)
                                                        (take cycle in-envs)
                                                        (svex-env-extract (svex-alist-keys (svtv->nextstate x)) env))
                                     x signals))))
     :hints (("goal" :induct (svtv-fsm-run-spec signals cycle x env)
              :in-theory (enable svtv-fsm-run)
              :expand ((:free (envs) (svex-envlist-extract signals envs))))
             (and stable-under-simplificationp
                  '(:in-theory (enable svtv-fsm-eval-expand
                                       svex-unroll-state-unroll-backward)
                    :cases ((consp (cdr signals)))))))))

(define svtv-fsm-run-symbolic-svexlist ((signals svarlist-list-p)
                                        (cycle natp)
                                        (outexprs svex-alist-p)
                                        (nextstate svex-alist-p))
  :returns (outs svexlist-p)
  (if (atom signals)
      nil
    (append (svexlist-compose*-unroll (svex-alist-vals (svex-alist-extract (car signals) outexprs))
                                      cycle nextstate)
            (svtv-fsm-run-symbolic-svexlist (cdr signals) (1+ (lnfix cycle)) outexprs nextstate))))



(define svtv-fsm-run-symbolic-svexlist->alists ((signals svarlist-list-p)
                                                (x svtv-p)
                                                (vals 4veclist-p))
  :hooks nil

  :prepwork ((local (include-book "std/lists/take" :dir :system))
             (local (defthm 4veclist-p-of-nthcdr
                      (implies (4veclist-p x)
                               (4veclist-p (nthcdr n x)))
                      :hints(("Goal" :in-theory (enable nthcdr 4veclist-p)))))
             (local (defthm 4veclist-p-of-take
                      (implies (4veclist-p x)
                               (4veclist-p (nthcdr n x)))
                      :hints(("Goal" :in-theory (enable 4veclist-p)))))
             (local (defthm svex-env-p-of-pairlis$
                      (implies (and (equal (len x) (len y))
                                    (svarlist-p x) (4veclist-p y))
                               (svex-env-p (pairlis$ x y)))
                      :hints(("Goal" :in-theory (enable svex-env-p pairlis$))))))

  (b* (((when (atom signals)) nil)
       (len (len (car signals))))
    (cons (pairlis$ (svarlist-fix (car signals))
                    (take len vals))
          (svtv-fsm-run-symbolic-svexlist->alists (cdr signals) x (nthcdr len vals))))
  ///

  (local (defthm len-of-svexlist-eval-unroll-multienv
           (equal (len (svexlist-eval-unroll-multienv x cycle nextstate in-envs orig-state))
                  (len x))
           :hints (("goal" :induct (len x)
                    :expand ((svexlist-eval-unroll-multienv x cycle nextstate in-envs orig-state))))))

  (local (defthm len-of-svexlist-eval-unroll
           (equal (len (svexlist-eval-unroll x cycle nextstate env))
                  (len x))
           :hints (("goal" :induct (len x)
                    :expand ((svexlist-eval-unroll x cycle nextstate env))))))

  (local (defthm len-of-svex-alist-extract
           (equal (len (svex-alist-extract vars x))
                  (len vars))
           :hints(("Goal" :in-theory (enable svex-alist-extract)))))

  (local (defthm len-of-svex-alist-vals2
           (implies (svex-alist-p x)
                    (equal (len (svex-alist-vals x)) (len x)))
           :hints(("Goal" :in-theory (enable svex-alist-vals svex-alist-keys svex-alist-p)))))

  (local (defthm nthcdr-of-append
           (implies (equal (nfix n) (len x))
                    (equal (nthcdr n (append x y))
                           y))
           :hints(("Goal" :in-theory (enable nthcdr len append)
                   :induct (nthcdr n x)))))

  (local (defun ind (signals cycle ins prev-st x)
           (if (atom signals)
               (list cycle ins prev-st)
             (ind (cdr signals) (1+ (lnfix cycle)) (cdr ins)
                  (svex-alist-eval (svtv->nextstate x)
                                   (append (svex-env-extract
                                            (svex-alist-keys (svtv->nextstate x))
                                            prev-st)
                                           (car ins)))
                  x))))
     


  (local (defthm svex-alist-eval-is-pairlis$
           (equal (pairlis$ (svex-alist-keys x)
                            (svexlist-eval (svex-alist-vals x) env))
                  (svex-alist-eval x env))
           :hints(("Goal" :in-theory (enable svex-alist-keys
                                             svex-alist-vals
                                             svex-alist-eval)))))

  (local (defthm svex-env-extract-of-pairlis$-svexlist-eval
           (equal (svex-env-extract vars (pairlis$ (svex-alist-keys x)
                                                   (svexlist-eval (svex-alist-vals x) env)))
                  (svex-alist-eval (svex-alist-extract vars x) env))))

  (local (in-theory (disable svex-alist-eval-of-svex-alist-extract)))

  (local (defthm nthcdr-of-svex-envlist-extract
           (equal (nthcdr n (svex-envlist-extract signals x))
                  (svex-envlist-extract (nthcdr n signals)
                                        (nthcdr n x)))
           :hints(("Goal" :in-theory (enable nthcdr svex-envlist-extract)))))

  (local (defthmd svexlist-eval-unroll-is-unroll-multienv-here
           (implies (and (bind-free '((ncycles . (binary-+ (nfix cycle) (len signals)))) (ncycles))
                         (< (nfix cycle) (nfix ncycles)))
                    (equal (svexlist-eval-unroll x cycle nextstates env)
                           (svexlist-eval-unroll-multienv x cycle nextstates
                                                      (svex-env-to-cycle-envs env ncycles)
                                                      (svex-env-extract (svex-alist-keys nextstates) env))))
           :hints (("goal" :use svexlist-eval-unroll-is-unroll-multienv))))

  (local (defthm dumb-lemma1
           (implies (consp signals)
                    (< cyc (+ cyc (len signals))))))

  (local (in-theory (disable svtv-fsm-run-spec-is-svtv-fsm-run)))

  (local (defthm svtv-fsm-run-symbolic-composition-is-svtv-fsm-run-spec
           (equal (svtv-fsm-run-symbolic-svexlist->alists
                   signals x
                   (svexlist-eval (svtv-fsm-run-symbolic-svexlist signals cycle (svtv->outexprs x) (svtv->nextstate x))
                                  env))
                  (svtv-fsm-run-spec signals cycle x env))
           :hints(("Goal" ;; :in-theory (enable svtv-fsm-run-symbolic-svexlist)
                   :in-theory (enable svtv-fsm-run-spec (:i svtv-fsm-run-symbolic-svexlist)
                                      svexlist-eval-unroll-is-unroll-multienv-here)
                   :induct (svtv-fsm-run-symbolic-svexlist signals cycle (svtv->outexprs x) (svtv->nextstate x))
                   :expand ((svtv-fsm-run-symbolic-svexlist signals cycle (svtv->outexprs x) (svtv->nextstate x))
                            ;; (svtv-fsm-eval ins prev-st x)
                            (:free (vals) (svtv-fsm-run-symbolic-svexlist->alists signals x vals)))))))

  (local (defthm svex-env-extract-of-superset
           (implies (subsetp (svarlist-fix keys) (svarlist-fix keys2))
                    (Equal (svex-env-extract keys (svex-env-extract keys2 x))
                           (svex-env-extract keys x)))
           :hints(("Goal" :in-theory (enable svex-env-extract svarlist-fix)))))

  

  (local (defthm svtv-fsm-eval-of-extract-states-from-prev-st
           (equal (svtv-fsm-eval ins (svex-env-extract (svex-alist-keys (svtv->nextstate x)) prev-st) x)
                  (svtv-fsm-eval ins prev-st x))
           :hints(("Goal" :in-theory (enable svtv-fsm-eval)))))

  (defthm svtv-fsm-run-symbolic-composition-is-svtv-fsm-run
    (implies (consp signals)
             (equal (svtv-fsm-run-symbolic-svexlist->alists
                     signals x
                     (svexlist-eval (svtv-fsm-run-symbolic-svexlist signals 0 (svtv->outexprs x) (svtv->nextstate x))
                                    env))
                    (b* ((in-envs (svex-env-to-cycle-envs env (len signals))))
                      (svtv-fsm-run in-envs
                                    env
                                    x signals))))
    :hints(("Goal" :in-theory (enable svtv-fsm-run-spec-is-svtv-fsm-run
                                      svtv-fsm-run)
            :expand ((:free (env) (svex-unroll-state (svtv->nextstate x) nil env)))
            :do-not-induct t)))

  (deffixequiv svtv-fsm-run-symbolic-svexlist->alists :omit (vals)))


(local
 (progn

   (defthm svtv-fsm-eval-of-prev-st-cycle-envs-to-single-env
     (implies (not (svarlist-has-svex-cycle-var (svex-alist-keys (svtv->nextstate x))))
              (equal (svtv-fsm-eval ins (svex-cycle-envs-to-single-env ins2 cyc rest) x)
                     (svtv-fsm-eval ins rest x)))
     :hints(("Goal" :expand ((:free (prev-st) (svtv-fsm-eval ins prev-st x))))))

   (defthm svex-env-extract-of-superset
     (implies (subsetp (svarlist-fix keys) (svarlist-fix keys2))
              (Equal (svex-env-extract keys (svex-env-extract keys2 x))
                     (svex-env-extract keys x)))
     :hints(("Goal" :in-theory (enable svex-env-extract svarlist-fix))))

   (defthm svtv-fsm-eval-of-extract-states-from-prev-st
     (equal (svtv-fsm-eval ins (svex-env-extract (svex-alist-keys (svtv->nextstate x)) prev-st) x)
            (svtv-fsm-eval ins prev-st x))
     :hints(("Goal" :in-theory (enable svtv-fsm-eval))))))


(define svtv-fsm-symbolic-env ((ins svex-envlist-p)
                               (statevars svarlist-p)
                               (prev-st svex-env-p))
  :enabled t
  ;; Make this opaque to GL
  (make-fast-alist (svex-cycle-envs-to-single-env ins 0 (svex-env-extract statevars prev-st))))

(define svtv-fsm-run-symbolic-svexlist-memo ((signals svarlist-list-p)
                                             (outexprs svex-alist-p)
                                             (nextstate svex-alist-p))
  :enabled t
  (svtv-fsm-run-symbolic-svexlist signals 0 outexprs nextstate)
  ///
  (memoize 'svtv-fsm-run-symbolic-svexlist-memo))


(define svtv-fsm-run-symbolic ((ins svex-envlist-p)
                               (prev-st svex-env-p)
                               (x svtv-p)
                               (signals svarlist-list-p))
  :guard (and (consp signals)
              (equal (alist-keys prev-st) (svex-alist-keys (svtv->nextstate x)))
              (not (acl2::hons-dups-p (svex-alist-keys (svtv->nextstate x)))))  
  (b* (((svtv x))
       ((when (atom signals))
        nil)
       (statevars (svex-alist-keys x.nextstate))
       ((when (svarlist-has-svex-cycle-var statevars))
        ;; bad!
        (gl::gl-hide (svtv-fsm-run ins prev-st x signals)))
       (x.outexprs (make-fast-alist x.outexprs))
       (x.nextstate (make-fast-alist x.nextstate))
       (env (svtv-fsm-symbolic-env ins statevars prev-st))
       (svexes (svtv-fsm-run-symbolic-svexlist-memo signals x.outexprs x.nextstate))
       (values (svexlist-eval-for-symbolic svexes env '((:allvars . t)))))
    (svtv-fsm-run-symbolic-svexlist->alists signals x values))
  ///
  (local (defthm svex-envlist-extract-of-atom
           (implies (not (consp keys))
                    (equal (svex-envlist-extract keys x)
                           nil))
           :hints(("Goal" :in-theory (enable svex-envlist-extract)))))

  (defthm svtv-fsm-run-symbolic-is-svtv-fsm-run
    (equal (svtv-fsm-run-symbolic ins prev-st x signals)
           (svtv-fsm-run ins prev-st x signals))
    :hints ((and stable-under-simplificationp
                 '(:in-theory (enable svtv-fsm-run svtv-fsm-eval)
                   :do-not-induct t))))

  (gl::def-gl-rewrite svtv-fsm-run-is-symbolic
    (equal (svtv-fsm-run ins prev-st x signals)
           (svtv-fsm-run-symbolic ins prev-st x signals))))






#||

(defsection svex-eval-equiv-by-env-similarity-on-vars


  (defquant svex-envs-similar-on-vars (vars env1 env2)
    (forall v
            (implies (member v (svarlist-fix vars))
                     (equal (svex-env-lookup v env1)
                            (svex-env-lookup v env2))))
    :rewrite :direct)

  (local (in-theory (enable svex-envs-similar-on-vars-necc)))

  (local (defthm subsetp-of-union
           (iff (subsetp (union a b) c)
                (and (subsetp (sfix a) c)
                     (subsetp (sfix b) c)))
           :hints ((set-reasoning))))

  (defthm-svex-eval-flag
    (defthm svex-eval-when-envs-similar-on-vars
      (implies (and (svex-envs-similar-on-vars vars env1 env2)
                    (subsetp (svex-vars x) (svarlist-fix vars)))
               (equal (svex-eval x env1)
                      (svex-eval x env2)))
      :hints ('(:expand ((svex-vars x)
                         (:free (env) (svex-eval x env)))))
      :flag expr)
    (defthm svexlist-eval-when-envs-similar-on-vars
      (implies (and (svex-envs-similar-on-vars vars env1 env2)
                    (subsetp (svexlist-vars x) (svarlist-fix vars)))
               (equal (svexlist-eval x env1)
                      (svexlist-eval x env2)))
      :hints ('(:expand ((svexlist-vars x)
                         (:free (env) (svexlist-eval x env)))))
      :flag list))


  (defthm svex-alist-eval-when-svex-envs-similar-on-vars
    (implies (and (svex-envs-similar-on-vars vars env1 env2)
                  (subsetp (svex-alist-vars x) (svarlist-fix vars)))
             (equal (svex-alist-eval x env1)
                    (svex-alist-eval x env2)))
    :hints(("Goal" :in-theory (enable svex-alist-eval svex-alist-vars)))))
           


(local
 (progn

   (defun trees-differ-by-svex-alist-eval (x y)
     (if (or (atom x)
             (atom y))
         nil
       (if (and (eq (car x) 'svex-alist-eval)
                (eq (car y) 'svex-alist-eval))
           `(equal ,x ,y)
         (if (equal (car x) (car y))
             (trees-differ-by-svex-alist-eval (cdr x) (cdr y))
           (and (equal (cdr x) (cdr y))
                (trees-differ-by-svex-alist-eval (car x) (car y)))))))

   (defun find-alist-eval-diff (x clause)
     (if (atom clause)
         nil
       (or (trees-differ-by-svex-alist-eval x (car clause))
           (find-alist-eval-diff x (cdr clause)))))

   (defun base-hint-for-svex-alist-eval-equality (lit)
     (case-match lit
       (('equal ('svex-alist-eval x env1)
                ('svex-alist-eval x env2))
        `(:computed-hint-replacement
          ((acl2::witness :ruleset svex-envs-similar-on-vars-witnessing))
          :use ((:instance svex-alist-eval-when-svex-envs-similar-on-vars
                 (x ,x)
                 (vars (svex-alist-vars ,x))
                 (env1 ,env1)
                 (env2 ,env2)))))))

   (defun hint-for-svex-alist-eval-equality (clause)
     (declare (xargs :mode :program))
     (b* ((lit (Car (last clause))))
       (case-match lit
         (('equal ('svex-alist-eval x env1)
                  ('svex-alist-eval x env2))
          (declare (ignore x env1 env2))
          (base-hint-for-svex-alist-eval-equality lit))
         (& (b* ((lit1 (case-match lit
                         (('equal x1 x2)
                          (trees-differ-by-svex-alist-eval x1 x2))))
                 ((when lit1)
                  (base-hint-for-svex-alist-eval-equality lit1))
                 (lit2 (find-alist-eval-diff (acl2::dumb-negate-lit lit) clause))
                 ((When lit2)
                  (base-hint-for-svex-alist-eval-equality lit2)))
              nil)))))))




(define svex-alistlist->svexes ((x svex-alistlist-p))
  :returns (svexes svexlist-p)
  (if (atom x)
      nil
    (append (svex-alist-vals (car x))
            (svex-alistlist->svexes (cdr x)))))



(define svex-alistlist-vals-to-envs ((x svex-alistlist-p)
                                     (vals 4veclist-p))
  :guard (equal (len vals) (len (svex-alistlist->svexes x)))
  :prepwork ((local (include-book "std/lists/take" :dir :system))
             (local (include-book "std/lists/nthcdr" :dir :system))
             
             (local (fty::deflist 4veclist :elt-type 4vec :true-listp t))

             (local (defthm nthcdr-of-4veclist-fix
                      (equal (nthcdr n (4veclist-fix x))
                             (4veclist-fix (nthcdr n x)))
                      :hints(("Goal" :in-theory (enable nthcdr 4veclist-fix)))))
             (local (defthm take-of-4veclist-fix
                      (4veclist-equiv (take n (4veclist-fix x))
                                      (take n x))
                      :hints(("Goal" :in-theory (enable 4veclist-fix)
                              :induct (nthcdr n x))))))
  :guard-hints (("goal" :in-theory (enable svex-alistlist->svexes)))
  (if (atom x)
      nil
    (b* ((keys (svex-alist-keys (car x)))
         (len (len keys)))
    (cons (pairlis$ keys (4veclist-fix (take len vals)))
          (svex-alistlist-vals-to-envs (cdr x) (nthcdr len vals)))))
  ///
  (local (defthm pairlis-keys-vals-is-svex-alist-eval
           (equal (pairlis$ (svex-alist-keys x)
                            (svexlist-eval (svex-alist-vals x) env))
                  (svex-alist-eval x env))
           :hints(("Goal" :in-theory (enable svex-alist-eval svex-alist-keys svex-alist-vals)))))
  (local (defthm nthcdr-of-append
           (implies (equal n (len a))
                    (Equal (nthcdr n (append a b))
                           b))
           :hints (("goal" :induct (nthcdr n a)))))


  (defthm svex-alistlist-vals-to-envs-correct
    (equal (svex-alistlist-vals-to-envs x (svexlist-eval (svex-alistlist->svexes x) env))
           (svex-alistlist-eval x env))
    :hints(("Goal" :in-theory (enable svex-alistlist->svexes
                                      svex-alistlist-eval)
            :induct (svex-alistlist->svexes x)
            :expand ((:free (vals) (svex-alistlist-vals-to-envs x vals)))))))

(define svex-alistlist-eval-for-symbolic ((x svex-alistlist-p)
                                          (env svex-env-p)
                                          (symbolic-params alistp))
  :returns (res (equal res (svex-alistlist-eval x env)))
  :verify-guards nil
  (mbe :logic
       (svex-alistlist-vals-to-envs x (svexlist-eval-for-symbolic
                                       (hons-copy (svex-alistlist->svexes x))
                                       env
                                       symbolic-params))
       :exec (svex-alistlist-eval x env))
  ///
  (verify-guards svex-alistlist-eval-for-symbolic))


(define svtv-cycles-compose-aux ((x svtv-p)
                                 (remaining-cycles natp)
                                 (curr-cycle natp)
                                 (in-vars svarlist-p)
                                 (prev-state svex-alist-p))
  :returns (outalists svex-alistlist-p)
  (b* (((svtv x))
       (in-alist (svex-cycle-var-assigns in-vars curr-cycle))
       (full-alist (make-fast-alist (append in-alist (svex-alist-fix prev-state))))
       (outs (svex-alist-compose x.outexprs full-alist))
       ((when (zp remaining-cycles))
        (clear-memoize-table 'svex-compose)
        (fast-alist-free full-alist)
        (list outs))
       (next-state (svex-alist-compose x.nextstate full-alist)))
    (clear-memoize-table 'svex-compose)
    (fast-alist-free full-alist)
    (cons outs
          (svtv-cycles-compose-aux x (1- remaining-cycles) (1+ (lnfix curr-cycle))
                                   in-vars next-state)))
  ///
  (local (defthm consp-by-len
           (implies (and (equal posp-len (posp (len x)))
                         (syntaxp (quotep posp-len)))
                    (equal (consp x) posp-len))))

  (local (defthm len-of-cdr
           (equal (len (cdr x))
                  (if (consp x)
                      (1- (len x))
                    0))))




  (local (in-theory (disable svex-alist-eval-when-svex-envs-similar-on-vars)))
                         
  ;; (local (defthm member-alist-keys-of-svex-env-fix
  ;;          (implies (svar-p v)
  ;;                   (iff (member v (alist-keys (svex-env-fix a)))
  ;;                        (member v (alist-keys a))))
  ;;          :hints(("Goal" :in-theory (enable svex-env-fix alist-keys)))))

  (local (defthm member-alist-keys
           (iff (member v (alist-keys x))
                (hons-assoc-equal v x))
           :hints(("Goal" :in-theory (enable alist-keys)))))

  (local (defthm svex-env-lookup-of-append
           (equal (svex-env-lookup v (append a b))
                  (if (member (svar-fix v) (alist-keys (svex-env-fix a)))
                      (svex-env-lookup v a)
                    (svex-env-lookup v b)))
           :hints(("Goal" :in-theory (enable svex-env-lookup)))))

  (local (in-theory (disable member-alist-keys)))

  (local (defthm alist-keys-of-svex-alist-eval
           (equal (alist-keys (svex-alist-eval x env))
                  (svex-alist-keys x))
           :hints(("Goal" :in-theory (enable svex-alist-eval svex-alist-keys alist-keys)))))

  (local (defthmd svex-lookup-is-member-alist-keys
           ;; opposite of member-svex-alist-keys
           (iff (svex-lookup x a)
                (member (svar-fix x) (svex-alist-keys a)))))

  (local (defthm svar-p-when-member-of-svarlist
           (implies (and (member v x)
                         (svarlist-p x))
                    (svar-p v))))


  (local (defthm svex-eval-of-svex-var
           (equal (svex-eval (svex-var v) env)
                  (svex-env-lookup v env))
           :hints(("Goal" :in-theory (enable svex-eval)))))

  (local (include-book "hints/subgoalp" :dir :system))


  (local (defthm svex-alist-keys-of-svex-alist-compose
           (equal (svex-alist-keys (svex-alist-compose x subst))
                  (svex-alist-keys x))
           :hints(("Goal" :in-theory (enable svex-alist-keys svex-alist-compose)))))

  (defret svtv-cycles-compose-aux-eval-is-svtv-fsm-eval
    (implies (and (not (svarlist-has-svex-cycle-var (svex-alist-vars (svtv->outexprs x))))
                  (not (svarlist-has-svex-cycle-var (svex-alist-vars (svtv->nextstate x))))
                  (set-equiv (svex-alist-keys prev-state) (svex-alist-keys (svtv->nextstate x)))
                  (not (intersectp (svarlist-fix in-vars) (svex-alist-keys (svtv->nextstate x))))
                  (subsetp (svex-alist-vars (svtv->outexprs x))
                           (append (svex-alist-keys (svtv->nextstate x))
                                   (svarlist-fix in-vars)))
                  (subsetp (svex-alist-vars (svtv->nextstate x))
                           (append (svex-alist-keys (svtv->nextstate x))
                                   (svarlist-fix in-vars))))
             (equal (svex-alistlist-eval outalists env)
                    (b* ((cycle-envs (svex-env-to-cycle-envs-starting env curr-cycle (+ 1 (nfix remaining-cycles)))))
                      (svtv-fsm-eval cycle-envs
                                    (svex-alist-eval prev-state env)
                                    x))))
    :hints (("goal" :induct t :do-not-induct t)
            ;; (and (acl2::irrelevant-subgoal-p id "Subgoal *1/1")
            ;;      '(:by nil))
            (and stable-under-simplificationp
                 '(:expand (;; (SVEX-ENV-TO-CYCLE-ENVS-STARTING ENV CURR-CYCLE 1)
                            (:free (n pst) (svtv-fsm-eval
                                            (svex-env-to-cycle-envs-starting env curr-cycle n)
                                            pst x)))))
            (and stable-under-simplificationp
                 (hint-for-svex-alist-eval-equality clause))
            (and stable-under-simplificationp
                 '(:in-theory (e/d (svex-lookup-is-member-alist-keys)
                                   (member-svex-alist-keys))))
            (acl2::witness :ruleset acl2::set-reasoning-no-consp))
    :otf-flg t))

(local
 ;; for mergesort/difference thms
 (deflist svarlist
  :elt-type svar
  :true-listp t
  :elementp-of-nil nil))

(define svarlist-identity-alist ((x svarlist-p))
  :returns (alist svex-alist-p)
  (if (atom x)
      nil
    (cons (cons (svar-fix (car x)) (svex-var (car x)))
          (svarlist-identity-alist (cdr x))))
  ///
  (defret svarlist-identity-alist-lookup
    (equal (svex-lookup v (svarlist-identity-alist x))
           (and (member (svar-fix v) (svarlist-fix x))
                (svex-var v)))
    :hints(("Goal" :in-theory (enable svex-lookup svarlist-fix))))

  (defret svex-alist-vars-of-svarlist-identity-alist
    (equal (svex-alist-keys alist)
           (svarlist-fix x))
    :hints(("Goal" :in-theory (enable svex-alist-keys svarlist-fix))))

  (defthm eval-of-identity-alist-is-svex-env-extract
    (equal (svex-alist-eval (svarlist-identity-alist x) env)
           (svex-env-extract x env))
    :hints(("Goal" :in-theory (enable svex-env-extract svex-alist-eval)
            :expand ((:free (v) (svex-eval (svex-var v) env)))))))


(local (defthm append-set-diff
         (set-equiv (append a (set-difference$ b a))
                    (append a b))
         :hints ((set-reasoning))))

(local (defthm svexlist-vars-of-svex-alist-vals
         (equal (svexlist-vars (svex-alist-vals x))
                (svex-alist-vars x))
         :hints(("Goal" :in-theory (enable svex-alist-vals svex-alist-vars svexlist-vars)))))

(define svtv-cycles-compose ((x svtv-p)
                             (ncycles natp))
  :returns (outalists svex-alistlist-p)
  (b* (((svtv x))
       (all-vars (mergesort (svexlist-collect-vars (append (svex-alist-vals x.outexprs)
                                                           (svex-alist-vals x.nextstate)))))
       (state-vars (mergesort (svex-alist-keys x.nextstate)))
       (in-vars (difference all-vars state-vars)))
    (svtv-cycles-compose-aux x ncycles 0 in-vars (svarlist-identity-alist state-vars)))
  ///

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

  (local (defthm alist-keys-of-svex-alist-eval
           (equal (alist-keys (svex-alist-eval x env))
                  (svex-alist-keys x))
           :hints(("Goal" :in-theory (enable svex-alist-eval svex-alist-keys alist-keys)))))

  (local (defthm svex-eval-of-svex-var
           (equal (svex-eval (svex-var v) env)
                  (svex-env-lookup v env))
           :hints(("Goal" :in-theory (enable svex-eval)))))

  (local (defthm not-cycle-var-when-member
           (implies (and (member v noncycle-vars)
                         (not (svarlist-has-svex-cycle-var noncycle-vars)))
                    (not (svex-cycle-var-p v)))
           :hints(("Goal" :in-theory (enable svarlist-has-svex-cycle-var)))))

  (local (defthm svtv-fsm-eval-of-identity-state
           (equal (svtv-fsm-eval cycle-envs
                                (svex-env-extract (mergesort keys) env)
                                x)
                  (svtv-fsm-eval cycle-envs
                                (svex-env-extract keys env)
                                x))
           :hints (("goal" :expand ((:free (prevst) (svtv-fsm-eval cycle-envs prevst x))))
                   (and stable-under-simplificationp
                        (hint-for-svex-alist-eval-equality clause)))))

  (local (defthm svex-env-extract-of-subset
           (implies (subsetp (svarlist-fix a) (svarlist-fix b))
                    (equal (svex-env-extract a (svex-env-extract b x))
                           (svex-env-extract a x)))
           :hints (("goal" :in-theory (enable (:i svex-env-extract))
                    :induct (svex-env-extract a x)
                    :expand ((:free (x) (svex-env-extract a x)))))))

  (local (defthm svtv-fsm-eval-of-extract-alist-keys
           (equal (svtv-fsm-eval cycle-envs (svex-env-extract (svex-alist-keys (svtv->nextstate x)) env) x)
                  (svtv-fsm-eval cycle-envs env x))
           :hints(("Goal" :expand ((:free (prevst) (svtv-fsm-eval cycle-envs prevst x)))))))


  (defret eval-of-svtv-cycles-compose
    (implies (and (not (svarlist-has-svex-cycle-var (svex-alist-vars (svtv->outexprs x))))
                  (not (svarlist-has-svex-cycle-var (svex-alist-vars (svtv->nextstate x)))))
             (equal (svex-alistlist-eval outalists env)
                    (b* ((cycle-envs (svex-env-to-cycle-envs env (+ 1 (nfix ncycles)))))
                      (svtv-fsm-eval cycle-envs
                                    ;; (svex-alist-eval (svarlist-identity-alist
                                    ;;                   (mergesort (svex-alist-keys (svtv->nextstate x))))
                                    ;;                  env)
                                    env
                                    x))))
    :hints (("goal" :use ((:instance svtv-cycles-compose-aux-eval-is-svtv-fsm-eval
                           (remaining-cycles ncycles)
                           (curr-cycle 0)
                           (in-vars (b* (((svtv x))
                                         (all-vars (mergesort (svexlist-collect-vars (append (svex-alist-vals x.outexprs)
                                                                                             (svex-alist-vals x.nextstate)))))
                                         (state-vars (mergesort (svex-alist-keys x.nextstate))))
                                      (difference all-vars state-vars)))
                           (prev-state (b* (((svtv x))
                                            (state-vars (mergesort (svex-alist-keys x.nextstate))))
                                         (svarlist-identity-alist state-vars)))))
             :in-theory (disable svtv-cycles-compose-aux-eval-is-svtv-fsm-eval))
            (set-reasoning))))






(define svtv-fsm-eval-alt ((ins svex-envlist-p)
                          (prev-st svex-env-p)
                          (x svtv-p))
  :guard (consp ins)
  (b* (((svtv x))
       (outalists (svtv-cycles-compose x (1- (len ins))))
       (env (svex-cycle-envs-to-single-env ins 0 prev-st)))
    (svex-alistlist-eval outalists env))
  ///

  (local (defthm natp-of-posp-minus-1
           (implies (posp x)
                    (natp (+ -1 x)))))

  (local (defthm posp-of-len-when-consp
           (implies (consp x)
                    (posp (len x)))
           :rule-classes :type-prescription))

  (local (defthm svarlist-has-svex-cycle-var-when-subset
           (implies (and (subsetp vars noncycle-vars)
                         (not (svarlist-has-svex-cycle-var noncycle-vars)))
                    (not (svarlist-has-svex-cycle-var vars)))
           :hints(("Goal" :in-theory (enable svarlist-has-svex-cycle-var subsetp)))))

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

  (local (defthm alist-keys-of-svex-alist-eval
           (equal (alist-keys (svex-alist-eval x env))
                  (svex-alist-keys x))
           :hints(("Goal" :in-theory (enable svex-alist-eval svex-alist-keys alist-keys)))))


  (local (defthm not-cycle-var-when-member
           (implies (and (member v noncycle-vars)
                         (not (svarlist-has-svex-cycle-var noncycle-vars)))
                    (not (svex-cycle-var-p v)))
           :hints(("Goal" :in-theory (enable svarlist-has-svex-cycle-var)))))

  (local (defthm len-equal-len-cdr-plus-1
           (implies (consp x)
                    (equal (+ 1 (len (cdr x))) (len x)))))

  (defthmd svtv-fsm-eval-is-run-alt
    (implies (and (not (svarlist-has-svex-cycle-var (svex-alist-keys (svtv->nextstate x))))
                  (not (svarlist-has-svex-cycle-var (svex-alist-vars (svtv->outexprs x))))
                  (not (svarlist-has-svex-cycle-var (svex-alist-vars (svtv->nextstate x))))
                  (not (svarlist-has-svex-cycle-var (alist-keys (svex-env-fix prev-st))))
                  (consp ins))
             (equal (svtv-fsm-eval ins prev-st x)
                    (svtv-fsm-eval-alt ins prev-st x)))
    :hints (("Goal" :do-not-induct t
             :in-theory (enable set-equiv))
            (and stable-under-simplificationp
                 '(:expand ((:free (prev-st) (svtv-fsm-eval ins prev-st x)))))
            (and stable-under-simplificationp
                 (hint-for-svex-alist-eval-equality clause)))))


(define svtv-fsm-states ((ins svex-envlist-p)
                         (prev-st svex-env-p)
                         (nextstate svex-alist-p))
  :guard (and (equal (alist-keys prev-st) (svex-alist-keys nextstate))
              (not (acl2::hons-dups-p (svex-alist-keys nextstate))))
  :returns (states svex-envlist-p)
  (b* ((curr-st (mbe :logic (svex-env-extract (svex-alist-keys nextstate)
                                              prev-st)
                     :exec prev-st))
       ((when (atom ins)) (list curr-st))
       (current-cycle-env (make-fast-alist (append curr-st
                                                   (svex-env-fix (car ins)))))
       (next-st (svex-alist-eval nextstate current-cycle-env)))
    (clear-memoize-table 'svex-eval)
    (fast-alist-free current-cycle-env)
    (cons curr-st (svtv-fsm-states (cdr ins) next-st nextstate)))
  ///
  (defthm svtv-fsm-eval-in-terms-of-fsm-states
    (implies (< (nfix n) (len ins))
             (equal (nth n (svtv-fsm-eval ins prev-st x))
                    (svex-alist-eval (svtv->outexprs x)
                                     (append (nth n (svtv-fsm-states ins prev-st (svtv->nextstate x)))
                                             (nth n ins)))))
    :hints(("Goal" :in-theory (enable svtv-fsm-eval svtv-fsm-states))))

  (local (defun svtv-fsm-states-n-ind (ins prev-st nextstate n)
           (if (zp n)
               (list ins prev-st nextstate)
             (b* ((curr-st (mbe :logic (svex-env-extract (svex-alist-keys nextstate)
                                                         prev-st)
                                :exec prev-st))
                  (current-cycle-env (make-fast-alist (append curr-st
                                                              (svex-env-fix (car ins)))))
                  (next-st (svex-alist-eval nextstate current-cycle-env)))
               (cons curr-st (svtv-fsm-states-n-ind (cdr ins) next-st nextstate (1- n)))))))

  (defret alist-keys-of-nth-svtv-fsm-states
    (equal (alist-keys (nth n states))
           (and (<= (nfix n) (len ins))
                (svex-alist-keys nextstate)))
    :hints (("goal" :induct (svtv-fsm-states-n-ind ins prev-st nextstate n))))

  (defret env-lookup-of-nth-svtv-fsm-states
    (implies (and (member (svar-fix v) (svex-alist-keys nextstate))
                  (<= (nfix n) (len ins)))
             (equal (svex-env-lookup v (nth n states))
                    (if (zp n)
                        (svex-env-lookup v prev-st)
                      (svex-eval (svex-lookup v nextstate)
                                 (append (nth (+ -1 n) states)
                                         (nth (+ -1 n) ins))))))
    :hints (("goal" :induct (svtv-fsm-states-n-ind ins prev-st nextstate n))))

  


  (defthm-svex-eval-unroll-multienv-flag
    (defthm svex-eval-unroll-multienv-in-terms-of-svtv-fsm-states
      (implies (< (nfix cycle) (len in-envs))
               (equal (svex-eval-unroll-multienv x cycle nextstates in-envs orig-state)
                      (svex-eval x (append (nth cycle (svtv-fsm-states in-envs orig-state nextstates))
                                           (nth cycle in-envs)))))
      :hints ('(:expand ((svex-eval-unroll-multienv x cycle nextstates in-envs orig-state)
                         (:free (env) (svex-eval x env)))
                :do-not-induct t)
              ;; (and stable-under-simplificationp
              ;;      '(:expand ((svtv-fsm-states in-envs orig-state nextstates))))
              )
      :flag svex-eval-unroll-multienv)
    (defthm svexlist-eval-unroll-multienv-in-terms-of-svtv-fsm-states
      (implies (< (nfix cycle) (len in-envs))
               (equal (svexlist-eval-unroll-multienv x cycle nextstates in-envs orig-state)
                      (svexlist-eval x (append (nth cycle (svtv-fsm-states in-envs orig-state nextstates))
                                               (nth cycle in-envs)))))
      :hints ('(:expand ((svexlist-eval-unroll-multienv x cycle nextstates in-envs orig-state)
                         (:free (env) (svexlist-eval x env)))))
      :flag svexlist-eval-unroll-multienv)))





||#
