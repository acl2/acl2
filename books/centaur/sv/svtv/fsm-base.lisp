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


(define svtv-fsm-eval-equiv ((x svtv-fsm-p) (y svtv-fsm-p))
  (b* (((svtv-fsm x))
       ((svtv-fsm y)))
    (and (ec-call (svex-alist-eval-equiv x.values y.values))
         (ec-call (svex-alist-eval-equiv x.nextstate y.nextstate))
         ;; (equal x.design y.design)
         ;; (equal x.user-names y.user-names)
         ;; (equal x.namemap y.namemap)
         ))
  ///
  (defequiv svtv-fsm-eval-equiv)

  (defcong svtv-fsm-eval-equiv svex-alist-eval-equiv (svtv-fsm->values fsm) 1)
  (defcong svtv-fsm-eval-equiv svex-alist-eval-equiv (svtv-fsm->nextstate fsm) 1))


(define svtv-fsm-eval/namemap-equiv ((x svtv-fsm-p) (y svtv-fsm-p))
  (b* (((svtv-fsm x))
       ((svtv-fsm y)))
    (and (ec-call (svex-alist-eval-equiv x.values y.values))
         (ec-call (svex-alist-eval-equiv x.nextstate y.nextstate))
         (equal x.namemap y.namemap)))
  ///
  (defequiv svtv-fsm-eval/namemap-equiv)

  (defrefinement svtv-fsm-eval/namemap-equiv svtv-fsm-eval-equiv
    :hints(("Goal" :in-theory (enable svtv-fsm-eval-equiv))))

  (defcong svex-alist-eval-equiv svtv-fsm-eval/namemap-equiv 
    (svtv-fsm values nextstate design user-names namemap) 1)

  (defcong svex-alist-eval-equiv svtv-fsm-eval/namemap-equiv 
    (svtv-fsm values nextstate design user-names namemap) 2)



  (defcong svtv-fsm-eval/namemap-equiv equal (svtv-fsm->namemap fsm) 1))





(define svtv-fsm-step-env ((in svex-env-p)
                           (prev-st svex-env-p)
                           (x svtv-fsm-p))
  :guard (and (equal (alist-keys prev-st) (svex-alist-keys (svtv-fsm->nextstate x)))
              (not (acl2::hons-dups-p (svex-alist-keys (svtv-fsm->nextstate x)))))
  :returns (step-env svex-env-p)
  (b* (((svtv-fsm x)))
    (make-fast-alist (append (mbe :logic (svex-env-extract (svex-alist-keys x.nextstate)
                                                           prev-st)
                                  :exec prev-st)
                             (svex-env-fix in))))
  ///
  (defthm svtv-fsm-step-env-of-extract-states-from-prev-st
    (equal (svtv-fsm-step-env ins (svex-env-extract (svex-alist-keys (svtv-fsm->nextstate x)) prev-st) x)
           (svtv-fsm-step-env ins prev-st x)))

  (defthm svtv-fsm-step-env-of-reduce-states-from-prev-st
    (equal (svtv-fsm-step-env ins (svex-env-reduce (svex-alist-keys (svtv-fsm->nextstate x)) prev-st) x)
           (svtv-fsm-step-env ins prev-st x)))

  (defcong svex-envs-similar svex-envs-similar (svtv-fsm-step-env in prev-st x) 1)

  (defcong svex-envs-similar svex-envs-equivalent (svtv-fsm-step-env in prev-st x) 2)
  
  (defcong svtv-fsm-eval-equiv svex-envs-equivalent (svtv-fsm-step-env in prev-st x) 3))
  


(define svtv-fsm-step ((in svex-env-p)
                       (prev-st svex-env-p)
                       (x svtv-fsm-p))
  :guard (and (equal (alist-keys prev-st) (svex-alist-keys (svtv-fsm->nextstate x)))
              (not (acl2::hons-dups-p (svex-alist-keys (svtv-fsm->nextstate x)))))
  :returns (next-st svex-env-p)
  (b* (((svtv-fsm x))
       (current-cycle-env (svtv-fsm-step-env in prev-st x)))
    (svex-alist-eval x.nextstate current-cycle-env))
  ///
  (defret alist-keys-of-svtv-fsm-step
    (equal (alist-keys next-st)
           (svex-alist-keys (svtv-fsm->nextstate x))))

  (defthm svtv-fsm-step-of-extract-states-from-prev-st
    (equal (svtv-fsm-step ins (svex-env-extract (svex-alist-keys (svtv-fsm->nextstate x)) prev-st) x)
           (svtv-fsm-step ins prev-st x)))

  (defthm svtv-fsm-step-of-reduce-states-from-prev-st
    (equal (svtv-fsm-step ins (svex-env-reduce (svex-alist-keys (svtv-fsm->nextstate x)) prev-st) x)
           (svtv-fsm-step ins prev-st x)))

  (defcong svex-envs-similar svex-envs-equivalent (svtv-fsm-step in prev-st x) 1)

  (defcong svex-envs-similar svex-envs-equivalent (svtv-fsm-step in prev-st x) 2)
  
  (defcong svtv-fsm-eval-equiv svex-envs-equivalent (svtv-fsm-step in prev-st x) 3))




(define svtv-fsm-step-outs ((in svex-env-p)
                            (prev-st svex-env-p)
                            (x svtv-fsm-p))
  :guard (and (equal (alist-keys prev-st) (svex-alist-keys (svtv-fsm->nextstate x)))
              (not (acl2::hons-dups-p (svex-alist-keys (svtv-fsm->nextstate x)))))
  :returns (next-st svex-env-p)
  (b* (((svtv-fsm x))
       (current-cycle-env (svtv-fsm-step-env in prev-st x)))
    (svex-alist-eval x.values current-cycle-env))
  ///
  (defthm svtv-fsm-step-outs-of-extract-states-from-prev-st
    (equal (svtv-fsm-step-outs ins (svex-env-extract (svex-alist-keys (svtv-fsm->nextstate x)) prev-st) x)
           (svtv-fsm-step-outs ins prev-st x)))

  (defthm svtv-fsm-step-outs-of-reduce-states-from-prev-st
    (equal (svtv-fsm-step-outs ins (svex-env-reduce (svex-alist-keys (svtv-fsm->nextstate x)) prev-st) x)
           (svtv-fsm-step-outs ins prev-st x)))

  (defcong svex-envs-similar svex-envs-equivalent (svtv-fsm-step-outs in prev-st x) 1)

  (defcong svex-envs-similar svex-envs-equivalent (svtv-fsm-step-outs in prev-st x) 2)
  
  (defcong svtv-fsm-eval-equiv svex-envs-equivalent (svtv-fsm-step-outs in prev-st x) 3))





(defsection svex-envlists-similar
  (def-universal-equiv svex-envlists-similar
    :qvars (n)
    :equiv-terms ((svex-envs-similar (nth n x))
                  (equal (len x)))
    :defquant t)

  (defexample svex-envlists-similar-nth-ex
    :pattern (nth n x)
    :templates (n)
    :instance-rulename svex-envlists-similar-instancing)

  (defcong svex-envlists-similar svex-envs-similar (car x) 1
    :hints (("goal" :use ((:instance svex-envlists-similar-necc (n 0) (y x-equiv))))))

  (defcong svex-envlists-similar svex-envlists-similar (cdr x) 1
    :hints (("goal" :use ((:instance svex-envlists-similar-necc
                           (n (+ (nfix (svex-envlists-similar-witness (cdr x) (cdr x-equiv))) 1))
                           (y x-equiv)))
             :expand ((:free (x y) (svex-envlists-similar (cdr x) y))
                      (:free (x y) (svex-envlists-similar y (cdr x)))))))

  (defcong svex-envlists-similar equal (len x) 1
    :hints (("goal" :in-theory (enable svex-envlists-similar))))

  (defcong svex-envlists-similar equal (consp x) 1
    :hints (("goal" :in-theory (enable svex-envlists-similar))))

  (defcong svex-envlists-similar svex-envs-similar (nth n x) 2 :hints ((witness)))

  (defcong svex-envs-similar svex-envlists-similar (cons a b) 1
    :hints ((witness)
            (and stable-under-simplificationp
                 '(:expand ((:free (a) (nth n0 (cons a b))))))))

  (defcong svex-envlists-similar svex-envlists-similar (cons a b) 2
    :hints ((witness :ruleset (svex-envlists-similar-witnessing))
            (and stable-under-simplificationp
                 '(:expand ((:free (a) (nth n0 (cons a b)))))))))


(defsection svex-envlists-equivalent
  (def-universal-equiv svex-envlists-equivalent
    :qvars (n)
    :equiv-terms ((svex-envs-equivalent (nth n x))
                  (equal (len x)))
    :defquant t)

  (defexample svex-envlists-equivalent-nth-ex
    :pattern (nth n x)
    :templates (n)
    :instance-rulename svex-envlists-equivalent-instancing)

  (defrefinement svex-envlists-equivalent svex-envlists-similar
    :hints ((witness)))


  (defcong svex-envlists-equivalent svex-envs-equivalent (car x) 1
    :hints (("goal" :use ((:instance svex-envlists-equivalent-necc (n 0) (y x-equiv))))))

  (defcong svex-envlists-equivalent svex-envlists-equivalent (cdr x) 1
    :hints (("goal" :use ((:instance svex-envlists-equivalent-necc
                           (n (+ (nfix (svex-envlists-equivalent-witness (cdr x) (cdr x-equiv))) 1))
                           (y x-equiv)))
             :expand ((:free (x y) (svex-envlists-equivalent (cdr x) y))
                      (:free (x y) (svex-envlists-equivalent y (cdr x)))))))

  (defcong svex-envlists-equivalent svex-envs-equivalent (nth n x) 2
    :hints ((witness))))



(define svtv-fsm-final-state ((ins svex-envlist-p)
                              (prev-st svex-env-p)
                              (x svtv-fsm-p))
  :guard (and (equal (alist-keys prev-st) (svex-alist-keys (svtv-fsm->nextstate x)))
              (not (acl2::hons-dups-p (svex-alist-keys (svtv-fsm->nextstate x)))))
  :returns (final-st svex-env-p)
  (b* (((svtv-fsm x)))
    (if (atom ins)
        (mbe :logic (svex-env-extract (svex-alist-keys x.nextstate)
                                      prev-st)
             :exec prev-st)
      (svtv-fsm-final-state (cdr ins)
                            (svtv-fsm-step (car ins) prev-st x)
                            x)))
  ///
  (defthm svtv-fsm-final-state-of-extract-states-from-prev-st
    (equal (svtv-fsm-final-state ins (svex-env-extract (svex-alist-keys (svtv-fsm->nextstate x)) prev-st) x)
           (svtv-fsm-final-state ins prev-st x)))

  (defthm svtv-fsm-final-state-of-reduce-states-from-prev-st
    (equal (svtv-fsm-final-state ins (svex-env-reduce (svex-alist-keys (svtv-fsm->nextstate x)) prev-st) x)
           (svtv-fsm-final-state ins prev-st x)))

  (defcong svex-envs-similar svex-envs-equivalent (svtv-fsm-final-state ins prev-st x) 2)

  (defcong svtv-fsm-eval-equiv svex-envs-equivalent (svtv-fsm-final-state ins prev-st x) 3)
  
  (local (defun svtv-fsm-final-st-ins-cong-ind (ins ins-equiv prev-st x)
           (b* (((svtv-fsm x)))
             (if (atom ins)
                 (list ins-equiv prev-st x)
               (svtv-fsm-final-st-ins-cong-ind (cdr ins) (cdr ins-equiv)
                                               (svtv-fsm-step (car ins) prev-st x)
                                               x)))))

  (defcong svex-envlists-similar svex-envs-equivalent (svtv-fsm-final-state ins prev-st x) 1
    :hints (("goal" :induct (svtv-fsm-final-st-ins-cong-ind ins ins-equiv prev-st x))))

  (defcong svex-envs-equivalent svex-envlists-equivalent (cons a b) 1
    :hints ((witness)
            (and stable-under-simplificationp
                 '(:expand ((:free (a) (nth n0 (cons a b))))))))

  (defcong svex-envlists-equivalent svex-envlists-equivalent (cons a b) 2
    :hints ((witness :ruleset (svex-envlists-equivalent-witnessing))
            (and stable-under-simplificationp
                 '(:expand ((:free (a) (nth n0 (cons a b)))))))))






(define svtv-fsm-eval ((ins svex-envlist-p)
                       (prev-st svex-env-p)
                       (x svtv-fsm-p))
  :guard (and (equal (alist-keys prev-st) (svex-alist-keys (svtv-fsm->nextstate x)))
              (not (acl2::hons-dups-p (svex-alist-keys (svtv-fsm->nextstate x)))))
  :guard-hints (("Goal" :in-theory (enable svtv-fsm-step-outs
                                           svtv-fsm-step)
                 :expand ((:free (prev-st) (svtv-fsm-eval nil prev-st x)))))
  :returns (outs svex-envlist-p)
  (b* (((when (atom ins)) nil))
    (mbe :logic (cons (svtv-fsm-step-outs (car ins) prev-st x)
                      (svtv-fsm-eval (cdr ins)
                                     (svtv-fsm-step (car ins) prev-st x)
                                     x))
         :exec
         (b* (((svtv-fsm x))
              (current-cycle-env (svtv-fsm-step-env (car ins) prev-st x))
              (outs (svex-alist-eval x.values current-cycle-env))
              ((when (atom (cdr ins)))
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







  (defthm len-of-svtv-fsm-eval
    (equal (len (svtv-fsm-eval ins prev-st x))
           (len ins)))

  (defthm svtv-fsm-eval-of-extract-states-from-prev-st
    (equal (svtv-fsm-eval ins (svex-env-extract (svex-alist-keys (svtv-fsm->nextstate x)) prev-st) x)
           (svtv-fsm-eval ins prev-st x))
    :hints(("Goal" :in-theory (enable svtv-fsm-eval))))

  (defthm svtv-fsm-eval-of-reduce-states-from-prev-st
    (equal (svtv-fsm-eval ins (svex-env-reduce (svex-alist-keys (svtv-fsm->nextstate x)) prev-st) x)
           (svtv-fsm-eval ins prev-st x))
    :hints(("Goal" :in-theory (enable svtv-fsm-eval))))



  (local (defun svtv-fsm-eval-+-n-m-ind (n m ins prev-st x)
           (b* (((svtv-fsm x))
                (current-cycle-env (svtv-fsm-step-env (car ins) prev-st x))
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
                      (svtv-fsm-step (car ins) initst svtv)))))

  (defcong svex-envs-similar svex-envlists-equivalent (svtv-fsm-eval ins prev-st x) 2)

  (defcong svtv-fsm-eval-equiv svex-envlists-equivalent (svtv-fsm-eval ins prev-st x) 3)
  
  (local (defun svtv-fsm-eval-ins-cong-ind (ins ins-equiv prev-st x)
           (b* (((svtv-fsm x)))
             (if (atom ins)
                 (list ins-equiv prev-st x)
               (svtv-fsm-eval-ins-cong-ind (cdr ins) (cdr ins-equiv)
                                               (svtv-fsm-step (car ins) prev-st x)
                                               x)))))

  (defcong svex-envlists-similar svex-envlists-equivalent (svtv-fsm-eval ins prev-st x) 1
    :hints (("goal" :induct (svtv-fsm-eval-ins-cong-ind ins ins-equiv prev-st x)))))



(define svtv-fsm-eval-states ((ins svex-envlist-p)
                              (prev-st svex-env-p)
                              (x svtv-fsm-p))
  :guard (and (equal (alist-keys prev-st) (svex-alist-keys (svtv-fsm->nextstate x)))
              (not (acl2::hons-dups-p (svex-alist-keys (svtv-fsm->nextstate x)))))
  :guard-hints (("goal" :in-theory (enable svtv-fsm-step)))
  :returns (outs svex-envlist-p)
  (b* (((when (atom ins)) nil))
    (mbe :logic
         (let ((next (svtv-fsm-step (car ins) prev-st x)))
           (cons next (svtv-fsm-eval-states (cdr ins) next x)))
         :exec (b* (((svtv-fsm x))
                    (current-cycle-env (svtv-fsm-step-env (car ins) prev-st x))
                    (next-st (svex-alist-eval x.nextstate current-cycle-env)))
                 (clear-memoize-table 'svex-eval)
                 (fast-alist-free current-cycle-env)
                 (cons next-st (svtv-fsm-eval-states (cdr ins) next-st x)))))
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


  

  (defthm len-of-svtv-fsm-eval-states
    (equal (len (svtv-fsm-eval-states ins prev-st x))
           (len ins)))

  (defthm svtv-fsm-eval-states-of-extract-states-from-prev-st
    (equal (svtv-fsm-eval-states ins (svex-env-extract (svex-alist-keys (svtv-fsm->nextstate x)) prev-st) x)
           (svtv-fsm-eval-states ins prev-st x))
    :hints(("Goal" :in-theory (enable svtv-fsm-eval-states))))


  (local (defun svtv-fsm-eval-states-+-n-m-ind (n m ins prev-st x)
           (b* (((svtv-fsm x))
                (current-cycle-env (svtv-fsm-step-env (car ins) prev-st x))
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
                      (svtv-fsm-step (car ins) initst svtv)))))

  (defcong svex-envs-similar svex-envlists-equivalent (svtv-fsm-eval-states ins prev-st x) 2)

  (defcong svtv-fsm-eval-equiv svex-envlists-equivalent (svtv-fsm-eval-states ins prev-st x) 3)
  
  (local (defun svtv-fsm-eval-ins-cong-ind (ins ins-equiv prev-st x)
           (b* (((svtv-fsm x)))
             (if (atom ins)
                 (list ins-equiv prev-st x)
               (svtv-fsm-eval-ins-cong-ind (cdr ins) (cdr ins-equiv)
                                               (svtv-fsm-step (car ins) prev-st x)
                                               x)))))

  (defcong svex-envlists-similar svex-envlists-equivalent (svtv-fsm-eval-states ins prev-st x) 1
    :hints (("goal" :induct (svtv-fsm-eval-ins-cong-ind ins ins-equiv prev-st x)
             :expand ((:free (ins) (svtv-fsm-eval-states ins prev-st x)))))))





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

  (defcong svex-envlists-similar svex-envlists-equivalent (svex-envlist-extract keys envs) 2))


(local (defthm take-of-svex-envlist-fix
         (svex-envlist-equiv (take n (svex-envlist-fix x))
                             (take n x))
         :hints(("Goal" :in-theory (e/d (svex-envlist-fix)
                                        (;; acl2::take-of-zero
                                         acl2::take-of-too-many
                                         acl2::take-when-atom))))))


(local (defcong svex-envlists-similar svex-envlists-similar (take n x) 2))


(define svtv-fsm-run ((ins svex-envlist-p)
                      (prev-st svex-env-p)
                      (x svtv-fsm-p)
                      (signals svarlist-list-p))
  :guard (and (equal (alist-keys prev-st) (svex-alist-keys (svtv-fsm->nextstate x)))
              (not (acl2::hons-dups-p (svex-alist-keys (svtv-fsm->nextstate x)))))
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
    :hints(("Goal" :in-theory (enable svtv-fsm-run))))


  (defcong svex-envs-similar svex-envlists-equivalent (svtv-fsm-run ins prev-st x signals) 2)

  (defcong svtv-fsm-eval-equiv svex-envlists-equivalent (svtv-fsm-run ins prev-st x signals) 3)

  (defcong svex-envlists-similar svex-envlists-equivalent (svtv-fsm-run ins prev-st x signals) 1))


(define svtv-fsm-print-run ((ins svex-envlist-p)
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
            (svtv-fsm-print-run (cdr ins) (cdr outs) (cdr states) (1+ (lnfix cycle))
                                print-ins print-outs print-states))))


(define svtv-fsm-run* ((ins svex-envlist-p)
                       (prev-st svex-env-p)
                       (x svtv-fsm-p)
                       (signals svarlist-list-p)
                       &key
                       (print-initsts 'nil)
                       (print-ins 't)
                       (print-outs 't))
  :guard (and (equal (alist-keys prev-st) (svex-alist-keys (svtv-fsm->nextstate x)))
              (not (acl2::hons-dups-p (svex-alist-keys (svtv-fsm->nextstate x)))))
  :enabled t
  (b* ((ans (svtv-fsm-run ins prev-st x signals)))
    (and print-initsts
         (prog2$ (cw "Initial state:~%") (svtv-print-alist-readable prev-st)))
    (and (or print-ins print-outs)
         (svtv-fsm-print-run ins ans nil 0 print-ins print-outs nil))
    ans))


(define svtv-fsm-run-states ((ins svex-envlist-p)
                             (prev-st svex-env-p)
                             (x svtv-fsm-p)
                             (signals svarlist-list-p))
  :guard (and (equal (alist-keys prev-st) (svex-alist-keys (svtv-fsm->nextstate x)))
              (not (acl2::hons-dups-p (svex-alist-keys (svtv-fsm->nextstate x)))))
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
    :hints(("Goal" :in-theory (enable svtv-fsm-run))))


  (defcong svex-envs-similar svex-envlists-equivalent (svtv-fsm-run-states ins prev-st x signals) 2)

  (defcong svtv-fsm-eval-equiv svex-envlists-equivalent (svtv-fsm-run-states ins prev-st x signals) 3)

  (defcong svex-envlists-similar svex-envlists-equivalent (svtv-fsm-run-states ins prev-st x signals) 1))


(define svtv-fsm-run-states* ((ins svex-envlist-p)
                              (prev-st svex-env-p)
                              (x svtv-fsm-p)
                              (signals svarlist-list-p)
                              &key
                              (print-initsts 'nil)
                              (print-ins 't)
                              (print-states 't))
  :guard (and (equal (alist-keys prev-st) (svex-alist-keys (svtv-fsm->nextstate x)))
              (not (acl2::hons-dups-p (svex-alist-keys (svtv-fsm->nextstate x)))))
  :enabled t
  (b* ((ans (svtv-fsm-run-states ins prev-st x signals)))
    (and print-initsts
         (prog2$ (cw "Initial state:~%") (svtv-print-alist-readable prev-st)))
    (and (or print-ins print-states)
         (svtv-fsm-print-run ins nil ans 0 print-ins nil print-states))
    ans))


(define svtv-fsm-run-outs-and-states ((ins svex-envlist-p)
                                      (prev-st svex-env-p)
                                      (x svtv-fsm-p)
                                      &key
                                      (out-signals svarlist-list-p)
                                      (state-signals svarlist-list-p))
  :guard (and (equal (alist-keys prev-st) (svex-alist-keys (svtv-fsm->nextstate x)))
              (not (acl2::hons-dups-p (svex-alist-keys (svtv-fsm->nextstate x)))))
  (mv (svtv-fsm-run ins prev-st x out-signals)
      (svtv-fsm-run-states ins prev-st x state-signals)))


(define svtv-fsm-run-outs-and-states* ((ins svex-envlist-p)
                                       (prev-st svex-env-p)
                                       (x svtv-fsm-p)
                                       &key
                                       (out-signals svarlist-list-p)
                                       (state-signals svarlist-list-p)
                                       (print-initsts 'nil)
                                       (print-ins 't)
                                       (print-outs 't)
                                       (print-states 't))
  :guard (and (equal (alist-keys prev-st) (svex-alist-keys (svtv-fsm->nextstate x)))
              (not (acl2::hons-dups-p (svex-alist-keys (svtv-fsm->nextstate x)))))
  :guard-hints (("goal" :in-theory (enable svtv-fsm-run-outs-and-states)))
  :enabled t
  (b* (((mv outs states) (svtv-fsm-run-outs-and-states
                          ins prev-st x :out-signals out-signals :state-signals state-signals)))
    (and print-initsts
         (prog2$ (cw "Initial state:~%") (svtv-print-alist-readable prev-st)))
    (and (or print-ins print-outs print-states)
         (svtv-fsm-print-run ins outs states 0 print-ins print-outs print-states))
    (mv outs states)))
