; Centaur SV Hardware Verification Package
; Copyright (C) 2016 Centaur Technology
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

(include-book "cycle-base")
(include-book "../svex/rewrite")
(include-book "../svex/unroll")
(local (std::add-default-post-define-hook :fix))

(encapsulate nil
  (local (defthm member-of-cons
           (iff (member k (cons a b))
                (or (equal k a)
                    (member k b)))))
  (local (in-theory (disable cons-equal member-equal)))
  (local (defthmd svex-alist-extract-when-not-present
           (implies (not (member-equal (caar x) (svarlist-fix keys)))
                    (equal (svex-alist-extract keys x)
                           (svex-alist-extract keys (cdr x))))
           :hints(("Goal" :in-theory (enable (:i svex-alist-extract)
                                             svex-lookup)
                   :induct (svex-alist-extract keys x)
                   :expand ((:free (x) (svex-alist-extract keys x))
                            (svarlist-fix keys)
                            (:free (k) (hons-assoc-equal k x)))))))

  (local (defthmd svex-alist-extract-when-bad-pair
           (implies (or (not (consp (car x)))
                        (not (svar-p (caar x))))
                    (equal (svex-alist-extract keys x)
                           (svex-alist-extract keys (cdr x))))
           :hints(("Goal" :in-theory (enable (:i svex-alist-extract)
                                             svex-lookup)
                   :induct (svex-alist-extract keys x)
                   :expand ((:free (x) (svex-alist-extract keys x))
                            (:free (k) (hons-assoc-equal k x)))))))

  (local (defthm svex-alist-extract-of-cons
           (equal (svex-alist-extract (cons key rest) x)
                  (cons (cons (svar-fix key)
                              (or (svex-lookup key x)
                                  (svex-x)))
                        (svex-alist-extract rest x)))
           :hints(("Goal" :in-theory (enable svex-alist-extract)))))

  (defthm svex-alist-extract-when-same-keys
    (implies (no-duplicatesp-equal (svex-alist-keys x))
             (equal (svex-alist-extract (svex-alist-keys x) x)
                    (svex-alist-fix x)))
    :hints(("Goal" :in-theory (enable svex-alist-extract-when-bad-pair
                                      svex-alist-extract-when-not-present
                                      svex-alist-fix
                                      svex-alist-keys
                                      no-duplicatesp-equal
                                      svex-lookup)))))


(local (in-theory (disable hons-dups-p)))

(local (defthm hons-assoc-equal-of-append
         (equal (hons-assoc-equal k (append x y))
                (or (hons-assoc-equal k x)
                    (hons-assoc-equal k y)))))

(define base-fsm-step-subst ((in svex-alist-p)
                             (prev-st svex-alist-p)
                             (x base-fsm-p))
  :guard (and (equal (svex-alist-keys prev-st) (svex-alist-keys (base-fsm->nextstate x)))
              (not (acl2::hons-dups-p (svex-alist-keys (base-fsm->nextstate x)))))
  :returns (subst svex-alist-p)
  (b* (((base-fsm x)))
    (make-fast-alist
     (append (mbe :logic (svex-alist-extract (svex-alist-keys x.nextstate)
                                             prev-st)
                  :exec prev-st)
             (svex-alist-fix in))))
  ///
  (defret eval-of-base-fsm-step-subst
    (equal (svex-alist-eval subst env)
           (base-fsm-step-env (svex-alist-eval in env)
                              (svex-alist-eval prev-st env)
                              x))
    :hints(("Goal" :in-theory (enable base-fsm-step-env))))

  (local (defthm svex-lookup-of-append
           (equal (svex-lookup k (append x y))
                  (or (svex-lookup k x)
                      (svex-lookup k y)))
           :hints(("Goal" :in-theory (enable svex-lookup)))))

  (defret eval-lookup-of-base-fsm-step-subst
    (equal (svex-eval (svex-lookup k subst) env)
           (svex-env-lookup k (base-fsm-step-env (svex-alist-eval in env)
                                                 (svex-alist-eval prev-st env)
                                                 x)))
    :hints(("Goal" :in-theory (enable base-fsm-step-env))))

  (defret normalize-base-fsm-fields-of-<fn>
    (implies (syntaxp (not (and (equal values ''nil))))
             (equal (let ((x (base-fsm values nextstate))) <call>)
                    (let ((x (base-fsm nil nextstate)))
                      <call>)))))

(define svex-env-to-subst ((x svex-env-p))
  :returns (subst svex-alist-p)
  (if (atom x)
      nil
    (if (mbt (and (consp (car x))
                  (svar-p (caar x))))
        (cons (cons (caar x)
                    (svex-quote (cdar x)))
              (svex-env-to-subst (cdr x)))
      (svex-env-to-subst (cdr x))))
  ///
  (defret eval-lookup-of-<fn>
    (equal (svex-eval (svex-lookup key subst) env)
           (svex-env-lookup key x))
    :hints(("Goal" :in-theory (enable svex-env-lookup svex-lookup))))

  (defret eval-of-<fn>
    (equal (svex-alist-eval subst env)
           (svex-env-fix x))
    :hints(("Goal" :in-theory (enable svex-alist-eval svex-env-fix))))

  (local (in-theory (enable svex-env-fix))))
       

(define svtv-cycle-step-phase-exprs ((prev-st svex-alist-p)
                                     (phase svtv-cyclephase-p)
                                     (x base-fsm-p)
                                     (simp svex-simpconfig-p))
  :guard (and (equal (svex-alist-keys prev-st) (svex-alist-keys (base-fsm->nextstate x)))
              (not (acl2::hons-dups-p (svex-alist-keys (base-fsm->nextstate x)))))
  :returns (mv (outs svex-alist-p)
               (nextsts svex-alist-p))
  (b* (((svtv-cyclephase phase))
       (subst (make-svex-substconfig
               :simp simp
               :alist (base-fsm-step-subst (svex-env-to-subst phase.constants)
                                           prev-st x)))
       ((base-fsm x))
       (outs (and phase.outputs-captured
                  (if phase.inputs-free
                      (svex-alist-compose-rw x.values subst)
                    (svex-alist-subst-rw x.values subst))))
       (nextsts (if phase.inputs-free
                    (svex-alist-compose-rw x.nextstate subst)
                  (svex-alist-subst-rw x.nextstate subst))))
    (fast-alist-free subst)
    (clear-memoize-table (if phase.inputs-free 'svex-compose-rw 'svex-subst-rw))
    (mv outs nextsts))
  ///
  (defret eval-outs-of-<fn>
    (equal (svex-alist-eval outs env)
           (and (svtv-cyclephase->outputs-captured phase)
                (svtv-cycle-step-phase-outs env
                                            (svex-alist-eval prev-st env)
                                            phase x)))
    :hints(("Goal" :in-theory (enable svtv-cycle-step-phase-outs
                                      base-fsm-step-env)
            :expand ((svex-alist-eval nil env)))))

  (defret eval-nextsts-of-<fn>
    (equal (svex-alist-eval nextsts env)
           (svtv-cycle-step-phase-nextsts env
                                          (svex-alist-eval prev-st env)
                                          phase x))
    :hints(("Goal" :in-theory (enable svtv-cycle-step-phase-nextsts
                                      base-fsm-step-env)
            :expand ((svex-alist-eval nil env)))))

  (local (defthm svex-eval-of-svex-lookup
           (equal (svex-eval (svex-lookup k x) env)
                  (svex-env-lookup k (svex-alist-eval x env)))
           :hints(("Goal" :in-theory (enable svex-alist-eval svex-env-lookup svex-lookup
                                             svex-env-fix svex-alist-fix)))))

  (defret eval-outs-lookup-of-<fn>
    (equal (svex-eval (svex-lookup k outs) env)
           (if (svtv-cyclephase->outputs-captured phase)
               (svex-env-lookup k
                                (svtv-cycle-step-phase-outs env
                                                            (svex-alist-eval prev-st env)
                                                            phase x))
             (svex-x)))
    :hints(("Goal" :in-theory (disable svex-env-lookup-of-svex-alist-eval <fn>))))

  (defret eval-nextsts-lookup-of-<fn>
    (equal (svex-eval (svex-lookup k nextsts) env)
           (svex-env-lookup k
                            (svtv-cycle-step-phase-nextsts env
                                                           (svex-alist-eval prev-st env)
                                                           phase x)))
    :hints(("Goal" :in-theory (disable svex-env-lookup-of-svex-alist-eval <fn>))))

  (defret svex-alist-keys-of-<fn>-nextst
    (equal (svex-alist-keys nextsts)
           (svex-alist-keys (base-fsm->nextstate x)))))



;; (define svtv-cycle-compile-outs ((ins svex-alist-p)
;;                                  (prev-st svex-alist-p)
;;                                  (phases svtv-cyclephaselist-p)
;;                                  (x base-fsm-p))
;;   :guard (and (equal (svex-alist-keys prev-st) (svex-alist-keys (base-fsm->nextstate x)))
;;               (not (acl2::hons-dups-p (svex-alist-keys (base-fsm->nextstate x)))))
;;   :returns (outs svex-alist-p)
;;   :prepwork ((local (defthm true-listp-when-svex-alist-p-rw
;;                       (implies (svex-alist-p x)
;;                                (true-listp x)))))
;;   (b* (((when (atom phases)) nil)
;;        ((mv outs1 nextst) (svtv-cycle-step-phase-exprs ins prev-st (car phases) x))
;;        (rest-outs (svtv-cycle-compile-outs ins nextst (cdr phases) x)))
;;     (mbe :logic (append outs1 rest-outs)
;;          :exec (if rest-outs
;;                    (append outs1 rest-outs)
;;                  outs1)))
;;   ///
;;   (defret eval-of-<fn>
;;     (equal (svex-alist-eval outs env)
;;            (svtv-cycle-eval-outs (svex-alist-eval ins env)
;;                                  (svex-alist-eval prev-st env)
;;                                  phases x))
;;     :hints(("Goal" :in-theory (enable svtv-cycle-eval-outs)
;;             :induct t
;;             :expand ((svex-alist-eval nil env))))))


;; (define svtv-cycle-compile-nextst ((ins svex-alist-p)
;;                                 (prev-st svex-alist-p)
;;                                 (phases svtv-cyclephaselist-p)
;;                                 (x base-fsm-p))
;;   :guard (and (equal (svex-alist-keys prev-st) (svex-alist-keys (base-fsm->nextstate x)))
;;               (not (acl2::hons-dups-p (svex-alist-keys (base-fsm->nextstate x)))))
;;   :returns (nextst svex-alist-p)
;;   (b* (((when (atom phases))
;;         (mbe :logic (svex-alist-extract (svex-alist-keys (base-fsm->nextstate x)) prev-st)
;;              :exec prev-st))
;;        (nextst (svtv-cycle-step-phase-nextsts ins prev-st (car phases) x)))
;;     (svtv-cycle-compile-nextst ins nextst (cdr phases) x))
;;   ///
;;   (defret eval-of-<fn>
;;     (equal (svex-alist-eval nextst env)
;;            (svtv-cycle-eval-nextst (svex-alist-eval ins env)
;;                                  (svex-alist-eval prev-st env)
;;                                  phases x))
;;     :hints(("Goal" :in-theory (enable svtv-cycle-eval-outs)
;;             :induct t
;;             :expand ((svex-alist-eval nil env)))))

;;   (defret svex-alist-keys-of-<fn>
;;     (equal (svex-alist-keys nextst)
;;            ()


(define svtv-cycle-compile ((prev-st svex-alist-p)
                            (phases svtv-cyclephaselist-p)
                            (x base-fsm-p)
                            (simp svex-simpconfig-p))
  :guard (and (equal (svex-alist-keys prev-st) (svex-alist-keys (base-fsm->nextstate x)))
              (not (acl2::hons-dups-p (svex-alist-keys (base-fsm->nextstate x)))))
  :returns (mv (outs svex-alist-p)
               (nextst svex-alist-p))
  :prepwork ((local (defthm true-listp-when-svex-alist-p-rw
                      (implies (svex-alist-p x)
                               (true-listp x)))))
  (b* (((when (atom phases))
        (mv nil
            (mbe :logic (svex-alist-extract (svex-alist-keys (base-fsm->nextstate x)) prev-st)
                 :exec prev-st)))
       ((mv outs1 nextst) (svtv-cycle-step-phase-exprs prev-st (car phases) x simp))
       ((mv rest-outs final-st) (svtv-cycle-compile nextst (cdr phases) x simp)))
    (mv (if (svtv-cyclephase->outputs-captured (car phases))
            outs1
          rest-outs)
        final-st))
  ///
  (defret eval-outs-of-<fn>
    (equal (svex-alist-eval outs env)
           (svtv-cycle-eval-outs env
                                 (svex-alist-eval prev-st env)
                                 phases x))
    :hints(("Goal" :in-theory (enable svtv-cycle-eval-outs)
            :induct <call>
            :expand ((svex-alist-eval nil env)))))

  (defret eval-nextsts-of-<fn>
    (equal (svex-alist-eval nextst env)
           (svtv-cycle-eval-nextst env
                                   (svex-alist-eval prev-st env)
                                   phases x))
    :hints(("Goal" :in-theory (enable svtv-cycle-eval-nextst)
            :induct <call>
            :expand ((svex-alist-eval nil env)))))

  (defret svex-alist-keys-of-<fn>
    (equal (svex-alist-keys nextst)
           (svex-alist-keys (base-fsm->nextstate x)))
    :hints (("goal" :in-theory (disable <fn>
                                        alist-keys-of-svex-alist-eval)
             :use ((:instance alist-keys-of-svex-alist-eval
                    (x nextst)))))))


(define svex-identity-subst ((x svarlist-p))
  :returns (subst svex-alist-p)
  (pairlis$ (svarlist-fix x) (svarlist->svexes x))
  ///
  (defret svex-alist-keys-of-<fn>
    (equal (svex-alist-keys subst) (svarlist-fix x)))

  (local (defthm nth-of-svarlist->svexes
           (equal (nth n (svarlist->svexes x))
                  (and (< (nfix n) (len x))
                       (svex-var (nth n x))))
           :hints(("Goal" :in-theory (enable svarlist->svexes nth)))))


  (local (defthm hons-assoc-equal-of-pairlis
           (equal (hons-assoc-equal var (pairlis$ (svarlist-fix x)
                                                  (svarlist->svexes x)))
                  (and (member-equal var (svarlist-fix x))
                       (cons var (svex-var var))))
           :hints(("Goal" :in-theory (enable pairlis$ svarlist-fix svarlist->svexes)))))

  (defret svex-lookup-of-<fn>
    (equal (svex-lookup var subst)
           (and (member-equal (svar-fix var) (svarlist-fix x))
                (svex-var var)))
    :hints(("Goal" :in-theory (e/d (svex-lookup) (len) ;; svarlist-fix svarlist->svexes
                                   ))))

  (local (include-book "std/lists/sets" :dir :system))

  (local
   (deflist svarlist :elt-type svar :true-listp t :elementp-of-nil nil))

  (defcong set-equiv svex-alist-eval-equiv (svex-identity-subst x) 1
    :hints (("goal" :in-theory (disable set-equiv svex-identity-subst))
            (witness)))

  (defthm svex-alist-eval-of-svex-identity-subst
    (equal (svex-alist-eval (svex-identity-subst vars) env)
           (svex-env-extract vars env))
    :hints(("Goal" :in-theory (enable svex-alist-eval svex-env-extract pairlis$ svarlist-fix svarlist->svexes svex-eval)))))




(define base-fsm-to-cycle ((phases svtv-cyclephaselist-p)
                           (x base-fsm-p)
                           (simp svex-simpconfig-p))
  :returns (cycle base-fsm-p)
  :guard (not (hons-dups-p (svex-alist-keys (base-fsm->nextstate x))))
  (b* (((base-fsm x))
       (statevars (svex-alist-keys x.nextstate))
       (prev-st (svex-identity-subst statevars))
       ((mv outs nextst)
        (with-fast-alist prev-st
          (svtv-cycle-compile prev-st phases x simp))))
    (change-base-fsm x :values outs :nextstate nextst))
  ///

  (defret nextst-svex-alist-keys-of-<fn>
    (equal (svex-alist-keys (base-fsm->nextstate cycle))
           (svex-alist-keys (base-fsm->nextstate x)))))


(local (defthm svex-envlist-p-of-append
         (implies (and (svex-envlist-p x)
                       (svex-envlist-p y))
                  (svex-envlist-p (append x y)))))




(defthm base-fsm-step-env-of-svex-env-removekeys
  (svex-envs-equivalent (base-fsm-step-env (svex-env-removekeys
                                            (svex-alist-keys (base-fsm->nextstate x))
                                            in)
                                           prev-st x)
                        (base-fsm-step-env in prev-st x))
  :hints(("Goal" :in-theory (enable svex-envs-equivalent base-fsm-step-env))))


;; BOZO obvs this should be elsewhere
(define svex-envlist-remove-keys ((keys svarlist-p) (envs svex-envlist-p))
  :returns (new-envs svex-envlist-p)
  (if (atom envs)
      nil
    (cons (svex-env-removekeys keys (car envs))
          (svex-envlist-remove-keys keys (cdr envs))))
  ///
  (defthm base-fsm-eval-of-svex-envlist-remove-statevars
    (equal (base-fsm-eval (svex-envlist-remove-keys
                           (svex-alist-keys (base-fsm->nextstate x))
                           ins)
                          prev-st x)
           (base-fsm-eval ins prev-st x))
    :hints(("Goal" :in-theory (enable base-fsm-eval base-fsm-step-outs base-fsm-step))))

  (defthm base-fsm-final-state-of-svex-envlist-remove-statevars
    (equal (base-fsm-final-state (svex-envlist-remove-keys
                           (svex-alist-keys (base-fsm->nextstate x))
                           ins)
                          prev-st x)
           (base-fsm-final-state ins prev-st x))
    :hints(("Goal" :in-theory (enable base-fsm-final-state base-fsm-step))))

  (defthm svex-envlist-remove-keys-of-svtv-cycle-fsm-inputs
    (equal (svex-envlist-remove-keys keys (svtv-cycle-fsm-inputs
                                           (svex-env-removekeys keys in)
                                           phases))
           (svex-envlist-remove-keys keys (svtv-cycle-fsm-inputs in phases)))
    :hints(("Goal" :in-theory (enable svtv-cycle-fsm-inputs
                                      svtv-cycle-step-fsm-inputs)))))
  








(defsection svtv-cycle-run-fsm-inputs
  (local (std::set-define-current-function svtv-cycle-run-fsm-inputs))
  (local (in-theory (enable svtv-cycle-run-fsm-inputs)))

  (local (defthm base-fsm-eval-of-append
           (equal (base-fsm-eval (append ins1 ins2) initst x)
                  (append (base-fsm-eval ins1 initst x)
                          (base-fsm-eval ins2
                                         (base-fsm-final-state ins1 initst x)
                                         x)))
           :hints(("Goal" :in-theory (enable base-fsm-eval base-fsm-final-state)))))

  (local (defthm base-fsm-final-state-of-append
           (equal (base-fsm-final-state (append ins1 ins2) initst x)
                  (base-fsm-final-state ins2
                                        (base-fsm-final-state ins1 initst x)
                                        x))
           :hints(("Goal" :in-theory (enable base-fsm-final-state)))))

  (local (defthm nth-of-append
           (equal (nth n (append x y))
                  (if (< (nfix n) (len x))
                      (nth n x)
                    (nth (- (nfix n) (len x)) y)))
           :hints(("Goal" :in-theory (enable nth)))))

  (local (defthm member-svar-fix
           (implies (member x y)
                    (member (svar-fix x) (svarlist-fix y)))))

  (local (defthm extract-of-append-extract
           (implies (subsetp keys1 keys2)
                    (equal (svex-env-extract keys1 (append (svex-env-extract keys2 x) y))
                           (svex-env-extract keys1 x)))
           :hints(("Goal" :in-theory (enable svex-env-extract)))))

  (local (include-book "std/lists/sets" :dir :system))

  (local (defthm base-fsm-final-state-of-append-extract
           (equal (base-fsm-final-state
                   ins
                   (append (Svex-env-extract (svex-alist-keys (base-fsm->nextstate x)) initst)
                           rest)
                   x)
                  (base-fsm-final-state ins initst x))
           :hints (("goal" :use ((:instance base-fsm-final-state-of-extract-states-from-prev-st
                                  (prev-st (append (Svex-env-extract (svex-alist-keys (base-fsm->nextstate x)) initst)
                                                   rest)))
                                 (:instance base-fsm-final-state-of-extract-states-from-prev-st
                                  (prev-st initst)))
                    :in-theory (disable base-fsm-final-state-of-extract-states-from-prev-st)))))
                                  

  (local (defthm svex-env-removekeys-of-extract
           (implies (subsetp (svarlist-fix keys2) (svarlist-fix keys1))
                    (equal (svex-env-removekeys keys1 (svex-env-extract keys2 x))
                           nil))
           :hints(("Goal" :in-theory (enable svex-env-extract svex-env-removekeys svarlist-fix)))))

  (local (include-book "tools/trivial-ancestors-check" :dir :system))
  (local (acl2::use-trivial-ancestors-check))

  (local (defthmd base-fsm-final-state-rewrite-envlist-remove
           (implies (and (syntaxp (not (and (consp ins) (eq (car ins) 'svex-envlist-remove-keys))))
                         (equal ins1 (svex-envlist-remove-keys (svex-alist-keys (base-fsm->nextstate x)) ins))
                         (syntaxp
                          (prog2$ (cw "ins: ~x0 ins1: ~x1~%" ins ins1)
                                  (case-match ins1
                                    (('svex-envlist-remove-keys & ins2)
                                     (not (equal ins2 ins)))
                                    (& t)))))
                    (equal (base-fsm-final-state ins prev-st x)
                           (base-fsm-final-state ins1 prev-st x)))))

  

  (local (defthmd base-fsm-eval-rewrite-envlist-remove
           (implies (and (syntaxp (not (and (consp ins) (eq (car ins) 'svex-envlist-remove-keys))))
                         (equal ins1 (svex-envlist-remove-keys (svex-alist-keys (base-fsm->nextstate x)) ins))
                         (syntaxp
                          (prog2$ (cw "ins: ~x0 ins1: ~x1~%" ins ins1)
                                  (case-match ins1
                                    (('svex-envlist-remove-keys & ins2)
                                     (not (equal ins2 ins)))
                                    (& t)))))
                    (equal (base-fsm-eval ins prev-st x)
                           (base-fsm-eval ins1 prev-st x)))))

  (local (defthmd svex-envlist-remove-keys-of-cycle-fsm-inputs-rewrite
           (implies (and (syntaxp (not (and (consp ins) (eq (car ins) 'svex-env-removekeys))))
                         (equal ins1 (svex-env-removekeys (svex-alist-keys (base-fsm->nextstate x)) ins))
                         (syntaxp
                          (prog2$ (cw "ins: ~x0 ins1: ~x1~%" ins ins1)
                                  (case-match ins1
                                    (('svex-env-removekeys & ins2)
                                     (not (equal ins2 ins)))
                                    (& t)))))
                    (equal (svex-envlist-remove-keys
                            (svex-alist-keys (base-fsm->nextstate x))
                            (svtv-cycle-fsm-inputs ins phases))
                           (svex-envlist-remove-keys
                            (svex-alist-keys (base-fsm->nextstate x))
                            (svtv-cycle-fsm-inputs ins1 phases))))))

  (local (defthm base-fsm-final-state-of-cycle-fsm-append-extract
           (equal (base-fsm-final-state
                   (svtv-cycle-fsm-inputs
                    (append (svex-env-extract (svex-alist-keys (base-fsm->nextstate x)) foo) ins)
                    phases)
                   initst x)
                  (base-fsm-final-state (svtv-cycle-fsm-inputs ins phases) initst x))
           :hints(("Goal" :in-theory (enable base-fsm-final-state-rewrite-envlist-remove
                                             svex-envlist-remove-keys-of-cycle-fsm-inputs-rewrite)))))


  (local (defthm base-fsm-eval-of-cycle-fsm-append-extract
           (equal (base-fsm-eval
                   (svtv-cycle-fsm-inputs
                    (append (svex-env-extract (svex-alist-keys (base-fsm->nextstate x)) foo) ins)
                    phases)
                   initst x)
                  (base-fsm-eval (svtv-cycle-fsm-inputs ins phases) initst x))
           :hints(("Goal" :in-theory (enable base-fsm-eval-rewrite-envlist-remove
                                             svex-envlist-remove-keys-of-cycle-fsm-inputs-rewrite)))))

                                                         


  (defthm base-fsm-step-of-cycle-in-terms-of-fsm
    (b* ((cycle-fsm (base-fsm-to-cycle phases x simp)))
      (equal (base-fsm-step ins initst cycle-fsm)
             (base-fsm-final-state (svtv-cycle-fsm-inputs ins phases) initst x)))
    :hints(("Goal" :in-theory (enable base-fsm-to-cycle base-fsm-step base-fsm-step-env
                                      svtv-cycle-eval-nextst-is-fsm-final-state-of-fsm-inputs))))

  (defthm base-fsm-step-outs-of-cycle-in-terms-of-fsm
    (b* ((cycle-fsm (base-fsm-to-cycle phases x simp)))
      (equal (base-fsm-step-outs ins initst cycle-fsm)
             (let ((output-phase (svtv-cycle-output-phase phases)))
               (and output-phase
                    (nth output-phase
                         (base-fsm-eval (svtv-cycle-fsm-inputs ins phases) initst x))))))
    :hints(("Goal" :in-theory (enable base-fsm-to-cycle base-fsm-step-outs base-fsm-step-env
                                      svtv-cycle-eval-outs-is-fsm-eval-of-fsm-inputs))))

  (local (defun ind1 (ins initst phases x)
           (if (atom ins)
               initst
             (ind1 (cdr ins)
                   (svtv-cycle-eval-nextst (car ins) initst phases x)
                   phases x))))

  (defthm base-fsm-final-state-of-cycle-in-terms-of-fsm
    (b* ((cycle-fsm (base-fsm-to-cycle phases x simp)))
      (equal (base-fsm-final-state ins initst cycle-fsm)
             (base-fsm-final-state (svtv-cycle-run-fsm-inputs ins phases) initst x)))
    :hints (("goal" :induct (ind1 ins initst phases x)
             :expand ((svtv-cycle-run-fsm-inputs ins phases)
                      (:free (fsm) (base-fsm-final-state ins initst fsm))
                      (base-fsm-final-state nil initst x))
             :in-theory (enable svtv-cycle-eval-nextst-is-fsm-final-state-of-fsm-inputs
                                base-fsm-step base-fsm-step-env))))

  (local (defun ind (n ins initst phases x)
           (if (zp n)
               (list ins initst)
             (ind (1- n) (cdr ins)
                  (svtv-cycle-eval-nextst (car ins) initst phases x)
                  phases x))))

  (local (include-book "arithmetic/top-with-meta" :dir :system))

  (local (defthm nat-times-nat-type
           (implies (and (natp n) (natp m))
                    (natp (* n m)))
           :rule-classes :type-prescription))

  (local (defthm lemma
           (implies (and (natp n) (posp m))
                    (<= n (* m n)))
           :rule-classes :linear))

  (local (defthm svtv-cycle-output-phase-limit
           (implies (svtv-cycle-output-phase phases)
                    (< (svtv-cycle-output-phase phases) (len phases)))
           :hints(("Goal" :in-theory (enable svtv-cycle-output-phase)))
           :rule-classes :linear))

  (defthm base-fsm-eval-of-cycle-in-terms-of-fsm
    (b* ((cycle-fsm (base-fsm-to-cycle phases x simp)))
      (equal (nth n (base-fsm-eval ins initst cycle-fsm))
             (let ((output-phase (svtv-cycle-output-phase phases)))
               (and output-phase
                    (nth (+ output-phase (* (nfix n) (len phases)))
                         (base-fsm-eval (svtv-cycle-run-fsm-inputs ins phases) initst x))))))
    :hints (("goal" :induct (ind n ins initst phases x)
             :expand ((svtv-cycle-run-fsm-inputs ins phases)
                      (:free (fsm) (base-fsm-eval ins initst fsm)))
             :in-theory (enable svtv-cycle-eval-nextst-is-fsm-final-state-of-fsm-inputs
                                svtv-cycle-eval-outs-is-fsm-eval-of-fsm-inputs))))

  (local (in-theory (enable svex-envlist-fix))))

