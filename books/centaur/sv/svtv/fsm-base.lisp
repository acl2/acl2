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


(define base-fsm-eval-equiv ((x base-fsm-p) (y base-fsm-p))
  (b* (((base-fsm x))
       ((base-fsm y)))
    (and (ec-call (svex-alist-eval-equiv x.values y.values))
         (ec-call (svex-alist-eval-equiv! x.nextstate y.nextstate))
         ;; (equal x.design y.design)
         ;; (equal x.user-names y.user-names)
         ;; (equal x.namemap y.namemap)
         ))
  ///
  (defequiv base-fsm-eval-equiv)

  (defcong base-fsm-eval-equiv svex-alist-eval-equiv (base-fsm->values fsm) 1)
  (defcong base-fsm-eval-equiv svex-alist-eval-equiv! (base-fsm->nextstate fsm) 1)

  (defrefinement base-fsm-equiv base-fsm-eval-equiv))

;; (define base-fsm-eval-equiv! ((x base-fsm-p) (y base-fsm-p))
;;   (b* (((base-fsm x))
;;        ((base-fsm y)))
;;     (and (ec-call (svex-alist-eval-equiv! x.values y.values))
;;          (ec-call (svex-alist-eval-equiv! x.nextstate y.nextstate))
;;          ;; (equal x.design y.design)
;;          ;; (equal x.user-names y.user-names)
;;          ;; (equal x.namemap y.namemap)
;;          ))
;;   ///
;;   (defequiv base-fsm-eval-equiv!)
;;   (defrefinement base-fsm-eval-equiv! base-fsm-eval-equiv
;;     :hints(("Goal" :in-theory (enable base-fsm-eval-equiv))))

;;   (defcong base-fsm-eval-equiv! svex-alist-eval-equiv! (base-fsm->values fsm) 1))


(define svtv-fsm-eval/namemap-equiv ((x svtv-fsm-p) (y svtv-fsm-p))
  (b* (((svtv-fsm x))
       ((svtv-fsm y)))
    (and (base-fsm-eval-equiv x.base-fsm y.base-fsm)
         (equal x.namemap y.namemap)))
  ///
  (defequiv svtv-fsm-eval/namemap-equiv)

  ;; (defrefinement svtv-fsm-eval/namemap-equiv svtv-fsm-eval-equiv
  ;;   :hints(("Goal" :in-theory (enable svtv-fsm-eval-equiv))))

  (defcong base-fsm-eval-equiv svtv-fsm-eval/namemap-equiv 
    (svtv-fsm base-fsm namemap) 1)

  (defcong svtv-fsm-eval/namemap-equiv base-fsm-eval-equiv (svtv-fsm->base-fsm fsm) 1)

  (defcong svtv-fsm-eval/namemap-equiv equal (svtv-fsm->namemap fsm) 1))


;; (define svtv-fsm-eval/namemap-equiv! ((x svtv-fsm-p) (y svtv-fsm-p))
;;   (b* (((svtv-fsm x))
;;        ((svtv-fsm y)))
;;     (and (base-fsm-eval-equiv! x.base-fsm y.base-fsm)
;;          (equal x.namemap y.namemap)))
;;   ///
;;   (defequiv svtv-fsm-eval/namemap-equiv!)

;;   (defrefinement svtv-fsm-eval/namemap-equiv! svtv-fsm-eval/namemap-equiv
;;     :hints (("Goal" :in-theory (enable svtv-fsm-eval/namemap-equiv))))

;;   ;; (defrefinement svtv-fsm-eval/namemap-equiv svtv-fsm-eval-equiv
;;   ;;   :hints(("Goal" :in-theory (enable svtv-fsm-eval-equiv))))

;;   (defcong base-fsm-eval-equiv! svtv-fsm-eval/namemap-equiv!
;;     (svtv-fsm base-fsm namemap) 1)

;;   (defcong svtv-fsm-eval/namemap-equiv! base-fsm-eval-equiv! (svtv-fsm->base-fsm fsm) 1))





(define base-fsm-step-env ((in svex-env-p)
                           (prev-st svex-env-p)
                           (x base-fsm-p))
  :guard (and (equal (alist-keys prev-st) (svex-alist-keys (base-fsm->nextstate x)))
              (not (acl2::hons-dups-p (svex-alist-keys (base-fsm->nextstate x)))))
  :returns (step-env svex-env-p)
  (b* (((base-fsm x)))
    (make-fast-alist (append (mbe :logic (svex-env-extract (svex-alist-keys x.nextstate)
                                                           prev-st)
                                  :exec prev-st)
                             (svex-env-fix in))))
  ///
  (defthm base-fsm-step-env-of-extract-states-from-prev-st
    (equal (base-fsm-step-env ins (svex-env-extract (svex-alist-keys (base-fsm->nextstate x)) prev-st) x)
           (base-fsm-step-env ins prev-st x)))

  (defthm base-fsm-step-env-of-reduce-states-from-prev-st
    (equal (base-fsm-step-env ins (svex-env-reduce (svex-alist-keys (base-fsm->nextstate x)) prev-st) x)
           (base-fsm-step-env ins prev-st x)))

  (defcong svex-envs-similar svex-envs-similar (base-fsm-step-env in prev-st x) 1)

  (defcong svex-envs-similar svex-envs-equivalent (base-fsm-step-env in prev-st x) 2)
  
  (defcong base-fsm-eval-equiv svex-envs-equivalent (base-fsm-step-env in prev-st x) 3))
  


(define base-fsm-step ((in svex-env-p)
                       (prev-st svex-env-p)
                       (x base-fsm-p))
  :guard (and (equal (alist-keys prev-st) (svex-alist-keys (base-fsm->nextstate x)))
              (not (acl2::hons-dups-p (svex-alist-keys (base-fsm->nextstate x)))))
  :returns (next-st svex-env-p)
  (b* (((base-fsm x))
       (current-cycle-env (base-fsm-step-env in prev-st x)))
    (svex-alist-eval x.nextstate current-cycle-env))
  ///
  (defret alist-keys-of-base-fsm-step
    (equal (alist-keys next-st)
           (svex-alist-keys (base-fsm->nextstate x))))

  (defthm base-fsm-step-of-extract-states-from-prev-st
    (equal (base-fsm-step ins (svex-env-extract (svex-alist-keys (base-fsm->nextstate x)) prev-st) x)
           (base-fsm-step ins prev-st x)))

  (defthm base-fsm-step-of-reduce-states-from-prev-st
    (equal (base-fsm-step ins (svex-env-reduce (svex-alist-keys (base-fsm->nextstate x)) prev-st) x)
           (base-fsm-step ins prev-st x)))

  (defcong svex-envs-similar svex-envs-equivalent (base-fsm-step in prev-st x) 1)

  (defcong svex-envs-similar svex-envs-equivalent (base-fsm-step in prev-st x) 2)
  
  (defcong base-fsm-eval-equiv svex-envs-equivalent (base-fsm-step in prev-st x) 3))




(define base-fsm-step-outs ((in svex-env-p)
                            (prev-st svex-env-p)
                            (x base-fsm-p))
  :guard (and (equal (alist-keys prev-st) (svex-alist-keys (base-fsm->nextstate x)))
              (not (acl2::hons-dups-p (svex-alist-keys (base-fsm->nextstate x)))))
  :returns (next-st svex-env-p)
  (b* (((base-fsm x))
       (current-cycle-env (base-fsm-step-env in prev-st x)))
    (svex-alist-eval x.values current-cycle-env))
  ///
  (defthm base-fsm-step-outs-of-extract-states-from-prev-st
    (equal (base-fsm-step-outs ins (svex-env-extract (svex-alist-keys (base-fsm->nextstate x)) prev-st) x)
           (base-fsm-step-outs ins prev-st x)))

  (defthm base-fsm-step-outs-of-reduce-states-from-prev-st
    (equal (base-fsm-step-outs ins (svex-env-reduce (svex-alist-keys (base-fsm->nextstate x)) prev-st) x)
           (base-fsm-step-outs ins prev-st x)))

  (defcong svex-envs-similar svex-envs-equivalent (base-fsm-step-outs in prev-st x) 1)

  (defcong svex-envs-similar svex-envs-equivalent (base-fsm-step-outs in prev-st x) 2)
  
  (defcong base-fsm-eval-equiv svex-envs-equivalent (base-fsm-step-outs in prev-st x) 3))






(define base-fsm-final-state ((ins svex-envlist-p)
                              (prev-st svex-env-p)
                              (x base-fsm-p))
  :guard (and (equal (alist-keys prev-st) (svex-alist-keys (base-fsm->nextstate x)))
              (not (acl2::hons-dups-p (svex-alist-keys (base-fsm->nextstate x)))))
  :returns (final-st svex-env-p)
  (b* (((base-fsm x)))
    (if (atom ins)
        (mbe :logic (svex-env-extract (svex-alist-keys x.nextstate)
                                      prev-st)
             :exec prev-st)
      (base-fsm-final-state (cdr ins)
                            (base-fsm-step (car ins) prev-st x)
                            x)))
  ///
  (defthm base-fsm-final-state-of-extract-states-from-prev-st
    (equal (base-fsm-final-state ins (svex-env-extract (svex-alist-keys (base-fsm->nextstate x)) prev-st) x)
           (base-fsm-final-state ins prev-st x)))

  (defthm base-fsm-final-state-of-reduce-states-from-prev-st
    (equal (base-fsm-final-state ins (svex-env-reduce (svex-alist-keys (base-fsm->nextstate x)) prev-st) x)
           (base-fsm-final-state ins prev-st x)))

  (defcong svex-envs-similar svex-envs-equivalent (base-fsm-final-state ins prev-st x) 2)

  (defcong base-fsm-eval-equiv svex-envs-equivalent (base-fsm-final-state ins prev-st x) 3)
  
  (local (defun base-fsm-final-st-ins-cong-ind (ins ins-equiv prev-st x)
           (b* (((base-fsm x)))
             (if (atom ins)
                 (list ins-equiv prev-st x)
               (base-fsm-final-st-ins-cong-ind (cdr ins) (cdr ins-equiv)
                                               (base-fsm-step (car ins) prev-st x)
                                               x)))))

  (defcong svex-envlists-similar svex-envs-equivalent (base-fsm-final-state ins prev-st x) 1
    :hints (("goal" :induct (base-fsm-final-st-ins-cong-ind ins ins-equiv prev-st x))))

  (defcong svex-envs-equivalent svex-envlists-equivalent (cons a b) 1
    :hints ((witness)
            (and stable-under-simplificationp
                 '(:expand ((:free (a) (nth n0 (cons a b))))))))

  (defcong svex-envlists-equivalent svex-envlists-equivalent (cons a b) 2
    :hints ((witness :ruleset (svex-envlists-equivalent-witnessing))
            (and stable-under-simplificationp
                 '(:expand ((:free (a) (nth n0 (cons a b)))))))))






(define base-fsm-eval ((ins svex-envlist-p)
                       (prev-st svex-env-p)
                       (x base-fsm-p))
  :guard (and (equal (alist-keys prev-st) (svex-alist-keys (base-fsm->nextstate x)))
              (not (acl2::hons-dups-p (svex-alist-keys (base-fsm->nextstate x)))))
  :guard-hints (("Goal" :in-theory (enable base-fsm-step-outs
                                           base-fsm-step)
                 :expand ((:free (prev-st) (base-fsm-eval nil prev-st x)))))
  :returns (outs svex-envlist-p)
  (b* (((when (atom ins)) nil))
    (mbe :logic (cons (base-fsm-step-outs (car ins) prev-st x)
                      (base-fsm-eval (cdr ins)
                                     (base-fsm-step (car ins) prev-st x)
                                     x))
         :exec
         (b* (((base-fsm x))
              (current-cycle-env (base-fsm-step-env (car ins) prev-st x))
              (outs (svex-alist-eval x.values current-cycle-env))
              ((when (atom (cdr ins)))
               (clear-memoize-table 'svex-eval)
               (fast-alist-free current-cycle-env)
               (list outs))
              (next-st (svex-alist-eval x.nextstate current-cycle-env)))
           (clear-memoize-table 'svex-eval)
           (fast-alist-free current-cycle-env)
           (cons outs (base-fsm-eval (cdr ins) next-st x)))))
  ///
  (defthm car-of-base-fsm-eval
    (equal (car (base-fsm-eval ins prev-st x))
           (and (consp ins)
                (base-fsm-step-outs (car ins) prev-st x)))
    :hints(("Goal" :in-theory (enable base-fsm-step-outs))))

  (defthm cdr-of-base-fsm-eval
    (equal (cdr (base-fsm-eval ins prev-st x))
           (and (consp ins)
                (base-fsm-eval (cdr ins) (base-fsm-step (car ins) prev-st x) x)))
    :hints(("Goal" :in-theory (enable base-fsm-step))))

  (defthm base-fsm-eval-of-cons
    (Equal (base-fsm-eval (cons a b) prev-st x)
           (cons (base-fsm-step-outs a prev-st x)
                 (base-fsm-eval b (base-fsm-step a prev-st x) x)))
    :hints(("Goal" :in-theory (enable base-fsm-eval
                                      base-fsm-step
                                      base-fsm-step-outs))))


  (defthm consp-of-base-fsm-eval
    (equal (consp (base-fsm-eval ins prev-st x))
           (consp ins)))







  (defthm len-of-base-fsm-eval
    (equal (len (base-fsm-eval ins prev-st x))
           (len ins)))

  (defthm base-fsm-eval-of-extract-states-from-prev-st
    (equal (base-fsm-eval ins (svex-env-extract (svex-alist-keys (base-fsm->nextstate x)) prev-st) x)
           (base-fsm-eval ins prev-st x))
    :hints(("Goal" :in-theory (enable base-fsm-eval))))

  (defthm base-fsm-eval-of-reduce-states-from-prev-st
    (equal (base-fsm-eval ins (svex-env-reduce (svex-alist-keys (base-fsm->nextstate x)) prev-st) x)
           (base-fsm-eval ins prev-st x))
    :hints(("Goal" :in-theory (enable base-fsm-eval))))



  (local (defun base-fsm-eval-+-n-m-ind (n m ins prev-st x)
           (b* (((base-fsm x))
                (current-cycle-env (base-fsm-step-env (car ins) prev-st x))
                ((when (zp n))
                 (list n m ins prev-st x))
                (next-st (svex-alist-eval x.nextstate current-cycle-env)))
             (clear-memoize-table 'svex-eval)
             (fast-alist-free current-cycle-env)
             (base-fsm-eval-+-n-m-ind (1- n) (1- (nfix m)) (cdr ins) next-st x))))

  (defthm lookup-in-fsm-eval-of-take
    (implies (and (< (nfix n) (len ins))
                  (< (nfix n) (nfix m)))
             (equal (nth n (base-fsm-eval (take m ins) initst svtv))
                    (nth n (base-fsm-eval ins initst svtv))))
    :hints (("Goal" :induct (base-fsm-eval-+-n-m-ind n m ins initst svtv)
             :expand ((base-fsm-eval ins initst svtv)
                      (:free (a b) (base-fsm-eval (cons a b) initst svtv))
                      (take m ins)
                      (base-fsm-eval nil initst svtv)
                      (base-fsm-step-outs (car ins) initst svtv)
                      (base-fsm-step (car ins) initst svtv)))))

  (defcong svex-envs-similar svex-envlists-equivalent (base-fsm-eval ins prev-st x) 2)

  (defcong base-fsm-eval-equiv svex-envlists-equivalent (base-fsm-eval ins prev-st x) 3)
  
  (local (defun base-fsm-eval-ins-cong-ind (ins ins-equiv prev-st x)
           (b* (((base-fsm x)))
             (if (atom ins)
                 (list ins-equiv prev-st x)
               (base-fsm-eval-ins-cong-ind (cdr ins) (cdr ins-equiv)
                                               (base-fsm-step (car ins) prev-st x)
                                               x)))))

  (defcong svex-envlists-similar svex-envlists-equivalent (base-fsm-eval ins prev-st x) 1
    :hints (("goal" :induct (base-fsm-eval-ins-cong-ind ins ins-equiv prev-st x)))))



(define base-fsm-eval-states ((ins svex-envlist-p)
                              (prev-st svex-env-p)
                              (x base-fsm-p))
  :guard (and (equal (alist-keys prev-st) (svex-alist-keys (base-fsm->nextstate x)))
              (not (acl2::hons-dups-p (svex-alist-keys (base-fsm->nextstate x)))))
  :guard-hints (("goal" :in-theory (enable base-fsm-step)))
  :returns (outs svex-envlist-p)
  (b* (((when (atom ins)) nil))
    (mbe :logic
         (let ((next (base-fsm-step (car ins) prev-st x)))
           (cons next (base-fsm-eval-states (cdr ins) next x)))
         :exec (b* (((base-fsm x))
                    (current-cycle-env (base-fsm-step-env (car ins) prev-st x))
                    (next-st (svex-alist-eval x.nextstate current-cycle-env)))
                 (clear-memoize-table 'svex-eval)
                 (fast-alist-free current-cycle-env)
                 (cons next-st (base-fsm-eval-states (cdr ins) next-st x)))))
  ///
  (defthm car-of-base-fsm-eval-states
    (equal (car (base-fsm-eval-states ins prev-st x))
           (and (consp ins)
                (base-fsm-step (car ins) prev-st x)))
    :hints(("Goal" :in-theory (enable base-fsm-step))))

  (defthm cdr-of-base-fsm-eval-states
    (equal (cdr (base-fsm-eval-states ins prev-st x))
           (and (consp ins)
                (base-fsm-eval-states (cdr ins) (base-fsm-step (car ins) prev-st x) x)))
    :hints(("Goal" :in-theory (enable base-fsm-step))))

  (defthm base-fsm-eval-states-of-cons
    (Equal (base-fsm-eval-states (cons a b) prev-st x)
           (b* ((nextst (base-fsm-step a prev-st x)))
             (cons nextst
                   (base-fsm-eval-states b nextst x))))
    :hints(("Goal" :in-theory (enable base-fsm-eval-states
                                      base-fsm-step
                                      base-fsm-step-outs))))


  (defthm consp-of-base-fsm-eval-states
    (equal (consp (base-fsm-eval-states ins prev-st x))
           (consp ins)))


  

  (defthm len-of-base-fsm-eval-states
    (equal (len (base-fsm-eval-states ins prev-st x))
           (len ins)))

  (defthm base-fsm-eval-states-of-extract-states-from-prev-st
    (equal (base-fsm-eval-states ins (svex-env-extract (svex-alist-keys (base-fsm->nextstate x)) prev-st) x)
           (base-fsm-eval-states ins prev-st x))
    :hints(("Goal" :in-theory (enable base-fsm-eval-states))))


  (local (defun base-fsm-eval-states-+-n-m-ind (n m ins prev-st x)
           (b* (((base-fsm x))
                (current-cycle-env (base-fsm-step-env (car ins) prev-st x))
                ((when (zp n))
                 (list n m ins prev-st x))
                (next-st (svex-alist-eval x.nextstate current-cycle-env)))
             (clear-memoize-table 'svex-eval)
             (fast-alist-free current-cycle-env)
             (base-fsm-eval-states-+-n-m-ind (1- n) (1- (nfix m)) (cdr ins) next-st x))))

  (defthm lookup-in-fsm-eval-states-of-take
    (implies (and (< (nfix n) (len ins))
                  (< (nfix n) (nfix m)))
             (equal (nth n (base-fsm-eval-states (take m ins) initst svtv))
                    (nth n (base-fsm-eval-states ins initst svtv))))
    :hints (("Goal" :induct (base-fsm-eval-states-+-n-m-ind n m ins initst svtv)
             :expand ((base-fsm-eval-states ins initst svtv)
                      (:free (a b) (base-fsm-eval-states (cons a b) initst svtv))
                      (take m ins)
                      (base-fsm-eval-states nil initst svtv)
                      (base-fsm-step-outs (car ins) initst svtv)
                      (base-fsm-step (car ins) initst svtv)))))

  (defcong svex-envs-similar svex-envlists-equivalent (base-fsm-eval-states ins prev-st x) 2)

  (defcong base-fsm-eval-equiv svex-envlists-equivalent (base-fsm-eval-states ins prev-st x) 3)
  
  (local (defun base-fsm-eval-ins-cong-ind (ins ins-equiv prev-st x)
           (b* (((base-fsm x)))
             (if (atom ins)
                 (list ins-equiv prev-st x)
               (base-fsm-eval-ins-cong-ind (cdr ins) (cdr ins-equiv)
                                               (base-fsm-step (car ins) prev-st x)
                                               x)))))

  (defcong svex-envlists-similar svex-envlists-equivalent (base-fsm-eval-states ins prev-st x) 1
    :hints (("goal" :induct (base-fsm-eval-ins-cong-ind ins ins-equiv prev-st x)
             :expand ((:free (ins) (base-fsm-eval-states ins prev-st x)))))))





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

  (defcong svex-envlists-similar svex-envlists-equivalent (svex-envlist-extract keys envs) 2)

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


(define base-fsm-run ((ins svex-envlist-p)
                      (prev-st svex-env-p)
                      (x base-fsm-p)
                      (signals svarlist-list-p))
  :guard (and (equal (alist-keys prev-st) (svex-alist-keys (base-fsm->nextstate x)))
              (not (acl2::hons-dups-p (svex-alist-keys (base-fsm->nextstate x)))))
  :guard-debug t
  :returns (outs svex-envlist-p)
  (svex-envlist-extract signals (base-fsm-eval (take (len signals) ins) prev-st x))
  ///

  ;; (defthm base-fsm-eval-of-take
  ;;   (implies (posp n)
  ;;            (equal (sv::base-fsm-eval (take n ins) initst svtv)
  ;;                   (take n (sv::base-fsm-eval ins initst svtv))))
  ;;   :hints(("Goal" :induct (base-fsm-eval-+-n-ind n ins initst svtv)
  ;;           :expand ((base-fsm-eval ins initst svtv)
  ;;                    (:free (a b) (base-fsm-eval (cons a b) initst svtv))))))

  (defthm base-fsm-run-lookup-is-eval-lookup
    (implies (member (svar-fix var) (svarlist-fix (nth n signals)))
             (equal (svex-env-lookup var (nth n (base-fsm-run ins initst svtv signals)))
                    (svex-env-lookup var (nth n (base-fsm-eval (take (len signals) ins) initst svtv)))))
    :hints(("Goal" :in-theory (enable base-fsm-run))))


  (defcong svex-envs-similar svex-envlists-equivalent (base-fsm-run ins prev-st x signals) 2)

  (defcong base-fsm-eval-equiv svex-envlists-equivalent (base-fsm-run ins prev-st x signals) 3)

  (defcong svex-envlists-similar svex-envlists-equivalent (base-fsm-run ins prev-st x signals) 1)

  (defret len-of-<fn>
    (equal (len outs) (len signals))))


(define base-fsm-print-run ((ins svex-envlist-p)
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
            (base-fsm-print-run (cdr ins) (cdr outs) (cdr states) (1+ (lnfix cycle))
                                print-ins print-outs print-states))))


(define base-fsm-run* ((ins svex-envlist-p)
                       (prev-st svex-env-p)
                       (x base-fsm-p)
                       (signals svarlist-list-p)
                       &key
                       (print-initsts 'nil)
                       (print-ins 't)
                       (print-outs 't))
  :guard (and (equal (alist-keys prev-st) (svex-alist-keys (base-fsm->nextstate x)))
              (not (acl2::hons-dups-p (svex-alist-keys (base-fsm->nextstate x)))))
  :enabled t
  (b* ((ans (base-fsm-run ins prev-st x signals)))
    (and print-initsts
         (prog2$ (cw "Initial state:~%") (svtv-print-alist-readable prev-st)))
    (and (or print-ins print-outs)
         (base-fsm-print-run ins ans nil 0 print-ins print-outs nil))
    ans))


(define base-fsm-run-states ((ins svex-envlist-p)
                             (prev-st svex-env-p)
                             (x base-fsm-p)
                             (signals svarlist-list-p))
  :guard (and (equal (alist-keys prev-st) (svex-alist-keys (base-fsm->nextstate x)))
              (not (acl2::hons-dups-p (svex-alist-keys (base-fsm->nextstate x)))))
  :guard-debug t
  :returns (outs svex-envlist-p)
  (svex-envlist-extract signals (base-fsm-eval-states (take (len signals) ins) prev-st x))

  ///

  ;; (defthm base-fsm-eval-of-take
  ;;   (implies (posp n)
  ;;            (equal (sv::base-fsm-eval (take n ins) initst svtv)
  ;;                   (take n (sv::base-fsm-eval ins initst svtv))))
  ;;   :hints(("Goal" :induct (base-fsm-eval-+-n-ind n ins initst svtv)
  ;;           :expand ((base-fsm-eval ins initst svtv)
  ;;                    (:free (a b) (base-fsm-eval (cons a b) initst svtv))))))

  (defthm base-fsm-run-states-lookup-is-eval-lookup
    (implies (member (svar-fix var) (svarlist-fix (nth n signals)))
             (equal (svex-env-lookup var (nth n (base-fsm-run-states ins initst x signals)))
                    (svex-env-lookup var (nth n (base-fsm-eval-states (take (len signals) ins) initst x)))))
    :hints(("Goal" :in-theory (enable base-fsm-run))))


  (defcong svex-envs-similar svex-envlists-equivalent (base-fsm-run-states ins prev-st x signals) 2)

  (defcong base-fsm-eval-equiv svex-envlists-equivalent (base-fsm-run-states ins prev-st x signals) 3)

  (defcong svex-envlists-similar svex-envlists-equivalent (base-fsm-run-states ins prev-st x signals) 1)

  (defret len-of-<fn>
    (equal (len outs) (len signals))))


(define base-fsm-run-states* ((ins svex-envlist-p)
                              (prev-st svex-env-p)
                              (x base-fsm-p)
                              (signals svarlist-list-p)
                              &key
                              (print-initsts 'nil)
                              (print-ins 't)
                              (print-states 't))
  :guard (and (equal (alist-keys prev-st) (svex-alist-keys (base-fsm->nextstate x)))
              (not (acl2::hons-dups-p (svex-alist-keys (base-fsm->nextstate x)))))
  :enabled t
  (b* ((ans (base-fsm-run-states ins prev-st x signals)))
    (and print-initsts
         (prog2$ (cw "Initial state:~%") (svtv-print-alist-readable prev-st)))
    (and (or print-ins print-states)
         (base-fsm-print-run ins nil ans 0 print-ins nil print-states))
    ans))


(define base-fsm-run-outs-and-states ((ins svex-envlist-p)
                                      (prev-st svex-env-p)
                                      (x base-fsm-p)
                                      &key
                                      (out-signals svarlist-list-p)
                                      (state-signals svarlist-list-p))
  :guard (and (equal (alist-keys prev-st) (svex-alist-keys (base-fsm->nextstate x)))
              (not (acl2::hons-dups-p (svex-alist-keys (base-fsm->nextstate x)))))
  (mv (base-fsm-run ins prev-st x out-signals)
      (base-fsm-run-states ins prev-st x state-signals)))


(define base-fsm-run-outs-and-states* ((ins svex-envlist-p)
                                       (prev-st svex-env-p)
                                       (x base-fsm-p)
                                       &key
                                       (out-signals svarlist-list-p)
                                       (state-signals svarlist-list-p)
                                       (print-initsts 'nil)
                                       (print-ins 't)
                                       (print-outs 't)
                                       (print-states 't))
  :guard (and (equal (alist-keys prev-st) (svex-alist-keys (base-fsm->nextstate x)))
              (not (acl2::hons-dups-p (svex-alist-keys (base-fsm->nextstate x)))))
  :guard-hints (("goal" :in-theory (enable base-fsm-run-outs-and-states)))
  :enabled t
  (b* (((mv outs states) (base-fsm-run-outs-and-states
                          ins prev-st x :out-signals out-signals :state-signals state-signals)))
    (and print-initsts
         (prog2$ (cw "Initial state:~%") (svtv-print-alist-readable prev-st)))
    (and (or print-ins print-outs print-states)
         (base-fsm-print-run ins outs states 0 print-ins print-outs print-states))
    (mv outs states)))
