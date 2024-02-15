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
(include-book "fsm-obj")
(include-book "print")
(include-book "../svex/lists")
(include-book "../svex/alist-equiv")
(include-book "../svex/env-ops")
(local (include-book "std/lists/sets" :dir :system))
;; (local (include-book "std/lists/take" :dir :system))
(local (std::add-default-post-define-hook :fix))

(defthm alist-keys-of-svex-alist-eval
  (equal (alist-keys (svex-alist-eval x env))
         (svex-alist-keys x))
  :hints(("Goal" :in-theory (enable alist-keys svex-alist-keys svex-alist-eval))))

(local (in-theory (disable acl2::hons-dups-p)))


(define fsm-eval-equiv ((x fsm-p) (y fsm-p))
  (b* (((fsm x))
       ((fsm y)))
    (and (ec-call (svex-alist-eval-equiv x.values y.values))
         (ec-call (svex-alist-eval-equiv! x.nextstate y.nextstate))
         ;; (equal x.design y.design)
         ;; (equal x.user-names y.user-names)
         ;; (equal x.namemap y.namemap)
         ))
  ///
  (defequiv fsm-eval-equiv)

  (defcong fsm-eval-equiv svex-alist-eval-equiv (fsm->values fsm) 1)
  (defcong fsm-eval-equiv svex-alist-eval-equiv! (fsm->nextstate fsm) 1)

  (defrefinement fsm-equiv fsm-eval-equiv))

;; (define fsm-eval-equiv! ((x fsm-p) (y fsm-p))
;;   (b* (((fsm x))
;;        ((fsm y)))
;;     (and (ec-call (svex-alist-eval-equiv! x.values y.values))
;;          (ec-call (svex-alist-eval-equiv! x.nextstate y.nextstate))
;;          ;; (equal x.design y.design)
;;          ;; (equal x.user-names y.user-names)
;;          ;; (equal x.namemap y.namemap)
;;          ))
;;   ///
;;   (defequiv fsm-eval-equiv!)
;;   (defrefinement fsm-eval-equiv! fsm-eval-equiv
;;     :hints(("Goal" :in-theory (enable fsm-eval-equiv))))

;;   (defcong fsm-eval-equiv! svex-alist-eval-equiv! (fsm->values fsm) 1))


(define svtv-fsm-eval/namemap-equiv ((x svtv-fsm-p) (y svtv-fsm-p))
  (b* (((svtv-fsm x))
       ((svtv-fsm y)))
    (and (fsm-eval-equiv x.fsm y.fsm)
         (equal x.namemap y.namemap)))
  ///
  (defequiv svtv-fsm-eval/namemap-equiv)

  ;; (defrefinement svtv-fsm-eval/namemap-equiv svtv-fsm-eval-equiv
  ;;   :hints(("Goal" :in-theory (enable svtv-fsm-eval-equiv))))

  (defcong fsm-eval-equiv svtv-fsm-eval/namemap-equiv 
    (svtv-fsm fsm namemap) 1)

  (defcong svtv-fsm-eval/namemap-equiv fsm-eval-equiv (svtv-fsm->fsm fsm) 1)

  (defcong svtv-fsm-eval/namemap-equiv equal (svtv-fsm->namemap fsm) 1))


;; (define svtv-fsm-eval/namemap-equiv! ((x svtv-fsm-p) (y svtv-fsm-p))
;;   (b* (((svtv-fsm x))
;;        ((svtv-fsm y)))
;;     (and (fsm-eval-equiv! x.fsm y.fsm)
;;          (equal x.namemap y.namemap)))
;;   ///
;;   (defequiv svtv-fsm-eval/namemap-equiv!)

;;   (defrefinement svtv-fsm-eval/namemap-equiv! svtv-fsm-eval/namemap-equiv
;;     :hints (("Goal" :in-theory (enable svtv-fsm-eval/namemap-equiv))))

;;   ;; (defrefinement svtv-fsm-eval/namemap-equiv svtv-fsm-eval-equiv
;;   ;;   :hints(("Goal" :in-theory (enable svtv-fsm-eval-equiv))))

;;   (defcong fsm-eval-equiv! svtv-fsm-eval/namemap-equiv!
;;     (svtv-fsm fsm namemap) 1)

;;   (defcong svtv-fsm-eval/namemap-equiv! fsm-eval-equiv! (svtv-fsm->fsm fsm) 1))





(define fsm-step-env ((in svex-env-p)
                           (prev-st svex-env-p)
                           (x.nextstate svex-alist-p))
  :guard (and (equal (alist-keys prev-st) (svex-alist-keys x.nextstate))
              (not (acl2::hons-dups-p (svex-alist-keys x.nextstate))))
  :returns (step-env svex-env-p)
  (make-fast-alist (append (mbe :logic (svex-env-extract (svex-alist-keys x.nextstate)
                                                         prev-st)
                                :exec prev-st)
                           (svex-env-fix in)))
  ///
  (defthm fsm-step-env-of-extract-states-from-prev-st
    (equal (fsm-step-env ins (svex-env-extract (svex-alist-keys x.nextstate) prev-st) x.nextstate)
           (fsm-step-env ins prev-st x.nextstate)))

  (defthm fsm-step-env-of-reduce-states-from-prev-st
    (equal (fsm-step-env ins (svex-env-reduce (svex-alist-keys x.nextstate) prev-st) x.nextstate)
           (fsm-step-env ins prev-st x.nextstate)))

  (defcong svex-envs-similar svex-envs-similar (fsm-step-env in prev-st x.nextstate) 1)

  (defcong svex-envs-similar equal (fsm-step-env in prev-st x.nextstate) 2)
  
  (defcong svex-alist-eval-equiv svex-envs-equivalent (fsm-step-env in prev-st x.nextstate) 3))
  


(define fsm-step ((in svex-env-p)
                       (prev-st svex-env-p)
                       (x.nextstate svex-alist-p))
  :guard (and (equal (alist-keys prev-st) (svex-alist-keys x.nextstate))
              (not (acl2::hons-dups-p (svex-alist-keys x.nextstate))))
  :returns (next-st svex-env-p)
  (b* ((current-cycle-env (fsm-step-env in prev-st x.nextstate)))
    (svex-alist-eval x.nextstate current-cycle-env))
  ///
  (defret alist-keys-of-fsm-step
    (equal (alist-keys next-st)
           (svex-alist-keys x.nextstate)))

  (defthm fsm-step-of-extract-states-from-prev-st
    (equal (fsm-step ins (svex-env-extract (svex-alist-keys x.nextstate) prev-st) x.nextstate)
           (fsm-step ins prev-st x.nextstate)))

  (defthm fsm-step-of-reduce-states-from-prev-st
    (equal (fsm-step ins (svex-env-reduce (svex-alist-keys x.nextstate) prev-st) x.nextstate)
           (fsm-step ins prev-st x.nextstate)))

  (defcong svex-envs-similar equal (fsm-step in prev-st x.nextstate) 1)

  (defcong svex-envs-similar equal (fsm-step in prev-st x.nextstate) 2)
  
  (defcong svex-alist-eval-equiv svex-envs-equivalent (fsm-step in prev-st x.nextstate) 3))




(define fsm-step-outs ((in svex-env-p)
                            (prev-st svex-env-p)
                            (x fsm-p))
  :guard (and (equal (alist-keys prev-st) (svex-alist-keys (fsm->nextstate x)))
              (not (acl2::hons-dups-p (svex-alist-keys (fsm->nextstate x)))))
  :returns (next-st svex-env-p)
  (b* (((fsm x))
       (current-cycle-env (fsm-step-env in prev-st x.nextstate)))
    (svex-alist-eval x.values current-cycle-env))
  ///
  (defthm fsm-step-outs-of-extract-states-from-prev-st
    (equal (fsm-step-outs ins (svex-env-extract (svex-alist-keys (fsm->nextstate x)) prev-st) x)
           (fsm-step-outs ins prev-st x)))

  (defthm fsm-step-outs-of-reduce-states-from-prev-st
    (equal (fsm-step-outs ins (svex-env-reduce (svex-alist-keys (fsm->nextstate x)) prev-st) x)
           (fsm-step-outs ins prev-st x)))

  (defcong svex-envs-similar equal (fsm-step-outs in prev-st x) 1)

  (defcong svex-envs-similar equal (fsm-step-outs in prev-st x) 2)
  
  (defcong fsm-eval-equiv svex-envs-equivalent (fsm-step-outs in prev-st x) 3))






(define fsm-final-state ((ins svex-envlist-p)
                              (prev-st svex-env-p)
                              (x.nextstate svex-alist-p))
  :guard (and (equal (alist-keys prev-st) (svex-alist-keys x.nextstate))
              (not (acl2::hons-dups-p (svex-alist-keys x.nextstate))))
  :returns (final-st svex-env-p)
  (if (atom ins)
      (mbe :logic (svex-env-extract (svex-alist-keys x.nextstate)
                                    prev-st)
           :exec prev-st)
    (fsm-final-state (cdr ins)
                          (fsm-step (car ins) prev-st x.nextstate)
                          x.nextstate))
  ///
  (defthm fsm-final-state-of-extract-states-from-prev-st
    (equal (fsm-final-state ins (svex-env-extract (svex-alist-keys x.nextstate) prev-st) x.nextstate)
           (fsm-final-state ins prev-st x.nextstate)))

  (defthm fsm-final-state-of-reduce-states-from-prev-st
    (equal (fsm-final-state ins (svex-env-reduce (svex-alist-keys x.nextstate) prev-st) x.nextstate)
           (fsm-final-state ins prev-st x.nextstate)))

  (defcong svex-envs-similar equal (fsm-final-state ins prev-st x.nextstate) 2)

  (defcong svex-alist-eval-equiv svex-envs-equivalent (fsm-final-state ins prev-st x.nextstate) 3)
  
  (local (defun fsm-final-st-ins-cong-ind (ins ins-equiv prev-st x.nextstate)
           (if (atom ins)
               (list ins-equiv prev-st x.nextstate)
             (fsm-final-st-ins-cong-ind (cdr ins) (cdr ins-equiv)
                                             (fsm-step (car ins) prev-st x.nextstate)
                                             x.nextstate))))

  (defcong svex-envlists-similar equal (fsm-final-state ins prev-st x.nextstate) 1
    :hints (("goal" :induct (fsm-final-st-ins-cong-ind ins ins-equiv prev-st x.nextstate))))

  (defcong svex-envs-equivalent svex-envlists-equivalent (cons a b) 1
    :hints ((witness)
            (and stable-under-simplificationp
                 '(:expand ((:free (a) (nth n0 (cons a b))))))))

  (defcong svex-envlists-equivalent svex-envlists-equivalent (cons a b) 2
    :hints ((witness :ruleset (svex-envlists-equivalent-witnessing))
            (and stable-under-simplificationp
                 '(:expand ((:free (a) (nth n0 (cons a b))))))))

  (defthm alist-keys-of-fsm-final-state
    (equal (alist-keys (fsm-final-state ins initst nextstate))
           (svex-alist-keys nextstate))
    :hints(("Goal" :in-theory (enable fsm-final-state
                                      fsm-step)))))






(define fsm-eval ((ins svex-envlist-p)
                       (prev-st svex-env-p)
                       (x fsm-p))
  :guard (and (equal (alist-keys prev-st) (svex-alist-keys (fsm->nextstate x)))
              (not (acl2::hons-dups-p (svex-alist-keys (fsm->nextstate x)))))
  :guard-hints (("Goal" :in-theory (enable fsm-step-outs
                                           fsm-step)
                 :expand ((:free (prev-st) (fsm-eval nil prev-st x)))))
  :returns (outs svex-envlist-p)
  (b* (((when (atom ins)) nil))
    (mbe :logic (cons (fsm-step-outs (car ins) prev-st x)
                      (fsm-eval (cdr ins)
                                     (fsm-step (car ins) prev-st (fsm->nextstate x))
                                     x))
         :exec
         (b* (((fsm x))
              (current-cycle-env (fsm-step-env (car ins) prev-st x.nextstate))
              (outs (svex-alist-eval x.values current-cycle-env))
              ((when (atom (cdr ins)))
               (clear-memoize-table 'svex-eval)
               (fast-alist-free current-cycle-env)
               (list outs))
              (next-st (svex-alist-eval x.nextstate current-cycle-env)))
           (clear-memoize-table 'svex-eval)
           (fast-alist-free current-cycle-env)
           (cons outs (fsm-eval (cdr ins) next-st x)))))
  ///
  (defthm car-of-fsm-eval
    (equal (car (fsm-eval ins prev-st x))
           (and (consp ins)
                (fsm-step-outs (car ins) prev-st x)))
    :hints(("Goal" :in-theory (enable fsm-step-outs))))

  (defthm cdr-of-fsm-eval
    (equal (cdr (fsm-eval ins prev-st x))
           (and (consp ins)
                (fsm-eval (cdr ins) (fsm-step (car ins) prev-st (fsm->nextstate x)) x)))
    :hints(("Goal" :in-theory (enable fsm-step))))

  (defthm fsm-eval-of-cons
    (Equal (fsm-eval (cons a b) prev-st x)
           (cons (fsm-step-outs a prev-st x)
                 (fsm-eval b (fsm-step a prev-st (fsm->nextstate x)) x)))
    :hints(("Goal" :in-theory (enable fsm-eval
                                      fsm-step
                                      fsm-step-outs))))


  (defthm consp-of-fsm-eval
    (equal (consp (fsm-eval ins prev-st x))
           (consp ins)))







  (defthm len-of-fsm-eval
    (equal (len (fsm-eval ins prev-st x))
           (len ins)))

  (defthm fsm-eval-of-extract-states-from-prev-st
    (equal (fsm-eval ins (svex-env-extract (svex-alist-keys (fsm->nextstate x)) prev-st) x)
           (fsm-eval ins prev-st x))
    :hints(("Goal" :in-theory (enable fsm-eval))))

  (defthm fsm-eval-of-reduce-states-from-prev-st
    (equal (fsm-eval ins (svex-env-reduce (svex-alist-keys (fsm->nextstate x)) prev-st) x)
           (fsm-eval ins prev-st x))
    :hints(("Goal" :in-theory (enable fsm-eval))))



  (local (defun fsm-eval-+-n-m-ind (n m ins prev-st x)
           (b* (((fsm x))
                (current-cycle-env (fsm-step-env (car ins) prev-st x.nextstate))
                ((when (zp n))
                 (list n m ins prev-st x))
                (next-st (svex-alist-eval x.nextstate current-cycle-env)))
             (clear-memoize-table 'svex-eval)
             (fast-alist-free current-cycle-env)
             (fsm-eval-+-n-m-ind (1- n) (1- (nfix m)) (cdr ins) next-st x))))

  (defthm lookup-in-fsm-eval-of-take
    (implies (and (< (nfix n) (len ins))
                  (< (nfix n) (nfix m)))
             (equal (nth n (fsm-eval (take m ins) initst svtv))
                    (nth n (fsm-eval ins initst svtv))))
    :hints (("Goal" :induct (fsm-eval-+-n-m-ind n m ins initst svtv)
             :expand ((fsm-eval ins initst svtv)
                      (:free (a b) (fsm-eval (cons a b) initst svtv))
                      (take m ins)
                      (fsm-eval nil initst svtv)
                      (fsm-step-outs (car ins) initst svtv)
                      (fsm-step (car ins) initst (fsm->nextstate svtv))))))

  (defcong svex-envs-similar equal (fsm-eval ins prev-st x) 2)

  (defcong fsm-eval-equiv svex-envlists-equivalent (fsm-eval ins prev-st x) 3)
  
  (local (defun fsm-eval-ins-cong-ind (ins ins-equiv prev-st x)
           (b* (((fsm x)))
             (if (atom ins)
                 (list ins-equiv prev-st x)
               (fsm-eval-ins-cong-ind (cdr ins) (cdr ins-equiv)
                                               (fsm-step (car ins) prev-st (fsm->nextstate x))
                                               x)))))

  (defcong svex-envlists-similar equal (fsm-eval ins prev-st x) 1
    :hints (("goal" :induct (fsm-eval-ins-cong-ind ins ins-equiv prev-st x)))))



(define fsm-eval-states ((ins svex-envlist-p)
                              (prev-st svex-env-p)
                              (x.nextstate svex-alist-p))
  :guard (and (equal (alist-keys prev-st) (svex-alist-keys x.nextstate))
              (not (acl2::hons-dups-p (svex-alist-keys x.nextstate))))
  :guard-hints (("goal" :in-theory (enable fsm-step)))
  :returns (outs svex-envlist-p)
  (b* (((when (atom ins)) nil))
    (mbe :logic
         (let ((next (fsm-step (car ins) prev-st x.nextstate)))
           (cons next (fsm-eval-states (cdr ins) next x.nextstate)))
         :exec (b* ((current-cycle-env (fsm-step-env (car ins) prev-st x.nextstate))
                    (next-st (svex-alist-eval x.nextstate current-cycle-env)))
                 (clear-memoize-table 'svex-eval)
                 (fast-alist-free current-cycle-env)
                 (cons next-st (fsm-eval-states (cdr ins) next-st x.nextstate)))))
  ///
  (defthm car-of-fsm-eval-states
    (equal (car (fsm-eval-states ins prev-st x.nextstate))
           (and (consp ins)
                (fsm-step (car ins) prev-st x.nextstate)))
    :hints(("Goal" :in-theory (enable fsm-step))))

  (defthm cdr-of-fsm-eval-states
    (equal (cdr (fsm-eval-states ins prev-st x.nextstate))
           (and (consp ins)
                (fsm-eval-states (cdr ins) (fsm-step (car ins) prev-st x.nextstate) x.nextstate)))
    :hints(("Goal" :in-theory (enable fsm-step))))

  (defthm fsm-eval-states-of-cons
    (Equal (fsm-eval-states (cons a b) prev-st x.nextstate)
           (b* ((nextst (fsm-step a prev-st x.nextstate)))
             (cons nextst
                   (fsm-eval-states b nextst x.nextstate))))
    :hints(("Goal" :in-theory (enable fsm-eval-states
                                      fsm-step
                                      fsm-step-outs))))


  (defthm consp-of-fsm-eval-states
    (equal (consp (fsm-eval-states ins prev-st x.nextstate))
           (consp ins)))


  

  (defthm len-of-fsm-eval-states
    (equal (len (fsm-eval-states ins prev-st x.nextstate))
           (len ins)))

  (defthm fsm-eval-states-of-extract-states-from-prev-st
    (equal (fsm-eval-states ins (svex-env-extract (svex-alist-keys x.nextstate) prev-st) x.nextstate)
           (fsm-eval-states ins prev-st x.nextstate))
    :hints(("Goal" :in-theory (enable fsm-eval-states))))


  (local (defun fsm-eval-states-+-n-m-ind (n m ins prev-st x.nextstate)
           (b* ((current-cycle-env (fsm-step-env (car ins) prev-st x.nextstate))
                ((when (zp n))
                 (list n m ins prev-st x.nextstate))
                (next-st (svex-alist-eval x.nextstate current-cycle-env)))
             (clear-memoize-table 'svex-eval)
             (fast-alist-free current-cycle-env)
             (fsm-eval-states-+-n-m-ind (1- n) (1- (nfix m)) (cdr ins) next-st x.nextstate))))

  (defthm lookup-in-fsm-eval-states-of-take
    (implies (and (< (nfix n) (len ins))
                  (< (nfix n) (nfix m)))
             (equal (nth n (fsm-eval-states (take m ins) initst svtv))
                    (nth n (fsm-eval-states ins initst svtv))))
    :hints (("Goal" :induct (fsm-eval-states-+-n-m-ind n m ins initst svtv)
             :expand ((fsm-eval-states ins initst svtv)
                      (:free (a b) (fsm-eval-states (cons a b) initst svtv))
                      (take m ins)
                      (fsm-eval-states nil initst svtv)
                      (fsm-step-outs (car ins) initst svtv)
                      (fsm-step (car ins) initst svtv)))))

  (defcong svex-envs-similar equal (fsm-eval-states ins prev-st x.nextstate) 2)

  (defcong svex-alist-eval-equiv svex-envlists-equivalent (fsm-eval-states ins prev-st x.nextstate) 3)
  
  (local (defun fsm-eval-ins-cong-ind (ins ins-equiv prev-st x.nextstate)
           (if (atom ins)
               (list ins-equiv prev-st x.nextstate)
             (fsm-eval-ins-cong-ind (cdr ins) (cdr ins-equiv)
                                         (fsm-step (car ins) prev-st x.nextstate)
                                         x.nextstate))))

  (defcong svex-envlists-similar equal (fsm-eval-states ins prev-st x.nextstate) 1
    :hints (("goal" :induct (fsm-eval-ins-cong-ind ins ins-equiv prev-st x.nextstate)
             :expand ((:free (ins) (fsm-eval-states ins prev-st x.nextstate)))))))





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
            :induct (list (nthcdr n signals) (nthcdr n x)))))

  (defcong svex-envlists-similar equal (svex-envlist-extract keys envs) 2)

  (defret len-of-<fn>
    (equal (len new-envs) (len keys))))


(local (defthm take-of-svex-envlist-fix
         (svex-envlist-equiv (take n (svex-envlist-fix x))
                             (take n x))
         :hints(("Goal" :in-theory (e/d (svex-envlist-fix)
                                        (;; acl2::take-of-zero
                                         acl2::take-of-too-many
                                         acl2::take-when-atom))))))


(local (defcong svex-envlists-similar svex-envlists-similar (take n x) 2))


(define fsm-run ((ins svex-envlist-p)
                      (prev-st svex-env-p)
                      (x fsm-p)
                      (signals svarlist-list-p))
  :guard (and (equal (alist-keys prev-st) (svex-alist-keys (fsm->nextstate x)))
              (not (acl2::hons-dups-p (svex-alist-keys (fsm->nextstate x)))))
  :guard-debug t
  :returns (outs svex-envlist-p)
  (svex-envlist-extract signals (fsm-eval (take (len signals) ins) prev-st x))
  ///

  ;; (defthm fsm-eval-of-take
  ;;   (implies (posp n)
  ;;            (equal (sv::fsm-eval (take n ins) initst svtv)
  ;;                   (take n (sv::fsm-eval ins initst svtv))))
  ;;   :hints(("Goal" :induct (fsm-eval-+-n-ind n ins initst svtv)
  ;;           :expand ((fsm-eval ins initst svtv)
  ;;                    (:free (a b) (fsm-eval (cons a b) initst svtv))))))

  (defthm fsm-run-lookup-is-eval-lookup
    (implies (member (svar-fix var) (svarlist-fix (nth n signals)))
             (equal (svex-env-lookup var (nth n (fsm-run ins initst svtv signals)))
                    (svex-env-lookup var (nth n (fsm-eval (take (len signals) ins) initst svtv)))))
    :hints(("Goal" :in-theory (enable fsm-run))))


  (defcong svex-envs-similar equal (fsm-run ins prev-st x signals) 2)

  (defcong fsm-eval-equiv svex-envlists-equivalent (fsm-run ins prev-st x signals) 3)

  (defcong svex-envlists-similar equal (fsm-run ins prev-st x signals) 1)

  (defret len-of-<fn>
    (equal (len outs) (len signals))))


(define fsm-print-run ((ins svex-envlist-p)
                            (outs svex-envlist-p)
                            (states svex-envlist-p)
                            (cycle natp)
                            print-ins
                            print-outs
                            print-states)
  :measure (max (len outs) (len states))
  (if (and (atom outs) (atom states))
      nil
    (progn$ (cw "Cycle ~x0: " cycle)
            (and print-ins
                 (prog2$ (cw "Inputs:~%")
                         (svtv-print-alist-readable (car ins))))
            (and print-outs
                 (prog2$ (cw "Outputs:~%")
                         (svtv-print-alist-readable (car outs))))
            (and print-states
                 (prog2$ (cw "States:~%")
                         (svtv-print-alist-readable (car states))))
            (fsm-print-run (cdr ins) (cdr outs) (cdr states) (1+ (lnfix cycle))
                                print-ins print-outs print-states))))


(define fsm-run* ((ins svex-envlist-p)
                       (prev-st svex-env-p)
                       (x fsm-p)
                       (signals svarlist-list-p)
                       &key
                       (print-initsts 'nil)
                       (print-ins 't)
                       (print-outs 't))
  :guard (and (equal (alist-keys prev-st) (svex-alist-keys (fsm->nextstate x)))
              (not (acl2::hons-dups-p (svex-alist-keys (fsm->nextstate x)))))
  :enabled t
  (b* ((ans (fsm-run ins prev-st x signals)))
    (and print-initsts
         (prog2$ (cw "Initial state:~%") (svtv-print-alist-readable prev-st)))
    (and (or print-ins print-outs)
         (fsm-print-run ins ans nil 0 print-ins print-outs nil))
    ans))


(define fsm-run-states ((ins svex-envlist-p)
                             (prev-st svex-env-p)
                             (x.nextstate svex-alist-p)
                             (signals svarlist-list-p))
  :guard (and (equal (alist-keys prev-st) (svex-alist-keys x.nextstate))
              (not (acl2::hons-dups-p (svex-alist-keys x.nextstate))))
  :guard-debug t
  :returns (outs svex-envlist-p)
  (svex-envlist-extract signals (fsm-eval-states (take (len signals) ins) prev-st x.nextstate))

  ///

  ;; (defthm fsm-eval-of-take
  ;;   (implies (posp n)
  ;;            (equal (sv::fsm-eval (take n ins) initst svtv)
  ;;                   (take n (sv::fsm-eval ins initst svtv))))
  ;;   :hints(("Goal" :induct (fsm-eval-+-n-ind n ins initst svtv)
  ;;           :expand ((fsm-eval ins initst svtv)
  ;;                    (:free (a b) (fsm-eval (cons a b) initst svtv))))))

  (defthm fsm-run-states-lookup-is-eval-lookup
    (implies (member (svar-fix var) (svarlist-fix (nth n signals)))
             (equal (svex-env-lookup var (nth n (fsm-run-states ins initst x.nextstate signals)))
                    (svex-env-lookup var (nth n (fsm-eval-states (take (len signals) ins) initst x.nextstate)))))
    :hints(("Goal" :in-theory (enable fsm-run))))


  (defcong svex-envs-similar equal (fsm-run-states ins prev-st x.nextstate signals) 2)

  (defcong svex-alist-eval-equiv svex-envlists-equivalent (fsm-run-states ins prev-st x.nextstate signals) 3)

  (defcong svex-envlists-similar equal (fsm-run-states ins prev-st x.nextstate signals) 1)

  (defret len-of-<fn>
    (equal (len outs) (len signals))))


(define fsm-run-states* ((ins svex-envlist-p)
                              (prev-st svex-env-p)
                              (x.nextstate svex-alist-p)
                              (signals svarlist-list-p)
                              &key
                              (print-initsts 'nil)
                              (print-ins 't)
                              (print-states 't))
  :guard (and (equal (alist-keys prev-st) (svex-alist-keys x.nextstate))
              (not (acl2::hons-dups-p (svex-alist-keys x.nextstate))))
  :enabled t
  (b* ((ans (fsm-run-states ins prev-st x.nextstate signals)))
    (and print-initsts
         (prog2$ (cw "Initial state:~%") (svtv-print-alist-readable prev-st)))
    (and (or print-ins print-states)
         (fsm-print-run ins nil ans 0 print-ins nil print-states))
    ans))


(define fsm-run-outs-and-states ((ins svex-envlist-p)
                                      (prev-st svex-env-p)
                                      (x fsm-p)
                                      &key
                                      (out-signals svarlist-list-p)
                                      (state-signals svarlist-list-p))
  :guard (and (equal (alist-keys prev-st) (svex-alist-keys (fsm->nextstate x)))
              (not (acl2::hons-dups-p (svex-alist-keys (fsm->nextstate x)))))
  (mv (fsm-run ins prev-st x out-signals)
      (fsm-run-states ins prev-st (fsm->nextstate x) state-signals)))


(define fsm-run-outs-and-states* ((ins svex-envlist-p)
                                       (prev-st svex-env-p)
                                       (x fsm-p)
                                       &key
                                       (out-signals svarlist-list-p)
                                       (state-signals svarlist-list-p)
                                       (print-initsts 'nil)
                                       (print-ins 't)
                                       (print-outs 't)
                                       (print-states 't))
  :guard (and (equal (alist-keys prev-st) (svex-alist-keys (fsm->nextstate x)))
              (not (acl2::hons-dups-p (svex-alist-keys (fsm->nextstate x)))))
  :guard-hints (("goal" :in-theory (enable fsm-run-outs-and-states)))
  :enabled t
  (b* (((mv outs states) (fsm-run-outs-and-states
                          ins prev-st x :out-signals out-signals :state-signals state-signals)))
    (and print-initsts
         (prog2$ (cw "Initial state:~%") (svtv-print-alist-readable prev-st)))
    (and (or print-ins print-outs print-states)
         (fsm-print-run ins outs states 0 print-ins print-outs print-states))
    (mv outs states)))
