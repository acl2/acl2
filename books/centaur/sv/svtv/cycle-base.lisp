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

(include-book "../svtv/fsm-base")
(local (std::add-default-post-define-hook :fix))
(local (in-theory (disable hons-dups-p)))

;; Let's standardize on having a cycle in which the signals that aren't set to
;; concrete values are left as their original canonical variables.  That means
;; that a wire can't be set to more than one distinct variable in a cycle.  If
;; we want that, then we're going to just do it phase-based instead.
;; Similarly, we're going to produce outputs on one phase of the cycle (we
;; won't require this strictly, but will just return the outputs from the first
;; phase where they're recorded).

;; So: A cycle will be defined by a list of phases, each of which will have (1)
;; an assignment of (canonical) variables to constant values, (2) a
;; Boolean saying whether the rest of the input variables are assigned Xes or
;; left free, and (3) a Boolean saying whether the outputs are captured that phase.

(fty::defprod svtv-cyclephase
  ((constants svex-env-p)
   (inputs-free booleanp)
   (outputs-captured booleanp))
  :layout :fulltree)


(fty::deflist svtv-cyclephaselist :elt-type svtv-cyclephase :true-listp t)

(define svtv-cycle-step-phase-outs ((ins svex-env-p)
                                    (prev-st svex-env-p)
                                    (phase svtv-cyclephase-p)
                                    (x base-fsm-p))
  :guard (and (equal (alist-keys prev-st) (svex-alist-keys (base-fsm->nextstate x)))
              (not (acl2::hons-dups-p (svex-alist-keys (base-fsm->nextstate x)))))
  :returns (outs svex-env-p)
  (b* (((svtv-cyclephase phase))
       (env (base-fsm-step-env (if phase.inputs-free
                                   (append phase.constants ins)
                                 phase.constants)
                               prev-st x))
       ((base-fsm x))
       (outs (svex-alist-eval x.values env)))
    (fast-alist-free env)
    outs)
  ///
  (defcong svex-envs-similar svex-envs-equivalent (svtv-cycle-step-phase-outs ins prev-st phase x) 1)
  (defcong svex-envs-similar svex-envs-equivalent (svtv-cycle-step-phase-outs ins prev-st phase x) 2)

  (defcong base-fsm-eval-equiv svex-envs-equivalent (svtv-cycle-step-phase-outs ins prev-st phase x) 4))

(define svtv-cycle-step-phase-nextsts ((ins svex-env-p)
                                       (prev-st svex-env-p)
                                       (phase svtv-cyclephase-p)
                                       (x base-fsm-p))
  :guard (and (equal (alist-keys prev-st) (svex-alist-keys (base-fsm->nextstate x)))
              (not (acl2::hons-dups-p (svex-alist-keys (base-fsm->nextstate x)))))
  :returns (nextsts svex-env-p)
  (b* (((svtv-cyclephase phase))
       (env (base-fsm-step-env (if phase.inputs-free
                                   (append phase.constants ins)
                                 phase.constants)
                               prev-st x))
       ((base-fsm x))
       (nextsts (svex-alist-eval x.nextstate env)))
    (fast-alist-free env)
    nextsts)
  ///
  (defret alist-keys-of-<fn>
    (equal (alist-keys nextsts) (svex-alist-keys (base-fsm->nextstate x))))
  (defcong svex-envs-similar svex-envs-similar (svtv-cycle-step-phase-nextsts ins prev-st phase x) 1)
  (defcong svex-envs-similar svex-envs-equivalent (svtv-cycle-step-phase-nextsts ins prev-st phase x) 2)

  (defcong base-fsm-eval-equiv svex-envs-equivalent (svtv-cycle-step-phase-nextsts ins prev-st phase x) 4))

(define svtv-cycle-step-phase ((ins svex-env-p)
                               (prev-st svex-env-p)
                               (phase svtv-cyclephase-p)
                               (x base-fsm-p))
  :guard (and (equal (alist-keys prev-st) (svex-alist-keys (base-fsm->nextstate x)))
              (not (acl2::hons-dups-p (svex-alist-keys (base-fsm->nextstate x)))))
  :prepwork ((local (in-theory (enable svtv-cycle-step-phase-nextsts
                                       svtv-cycle-step-phase-outs))))
  :returns (mv (outs (equal outs (and (svtv-cyclephase->outputs-captured phase)
                                      (svtv-cycle-step-phase-outs ins prev-st phase x))))
               (nextsts (equal nextsts (svtv-cycle-step-phase-nextsts ins prev-st phase x))))
  (b* (((svtv-cyclephase phase))
       (env (base-fsm-step-env (if phase.inputs-free
                                   (append phase.constants ins)
                                 phase.constants)
                               prev-st x))
       ((base-fsm x))
       (outs (and phase.outputs-captured
                  (svex-alist-eval x.values env)))
       (nextsts (svex-alist-eval x.nextstate env)))
    (fast-alist-free env)
    (mv outs nextsts)))


(define svtv-cycle-step-fsm-inputs ((ins svex-env-p)
                                    (phase svtv-cyclephase-p))
  :returns (fsm-ins svex-env-p)
  (b* (((svtv-cyclephase phase)))
    (if phase.inputs-free
        (append phase.constants (svex-env-fix ins))
      phase.constants))
  ///
  (defretd svtv-cycle-step-phase-nextsts-is-fsm-step-of-fsm-inputs
    (equal (svtv-cycle-step-phase-nextsts ins prev-st phase x)
           (base-fsm-step fsm-ins prev-st x))
    :hints(("Goal" :in-theory (enable svtv-cycle-step-phase-nextsts
                                      base-fsm-step))))

  (defretd svtv-cycle-step-phase-outs-is-fsm-step-outs-of-fsm-inputs
    (equal (svtv-cycle-step-phase-outs ins prev-st phase x)
           (base-fsm-step-outs fsm-ins prev-st x))
    :Hints(("Goal" :in-theory (enable base-fsm-step-outs
                                      svtv-cycle-step-phase-outs)))))
                                    

(define svtv-cycle-eval-outs ((ins svex-env-p)
                              (prev-st svex-env-p)
                              (phases svtv-cyclephaselist-p)
                              (x base-fsm-p))
  :guard (and (equal (alist-keys prev-st) (svex-alist-keys (base-fsm->nextstate x)))
              (not (acl2::hons-dups-p (svex-alist-keys (base-fsm->nextstate x)))))
  :returns (outs svex-env-p)
  (b* (((when (atom phases)) nil)
       ((mv outs1 nextst) (svtv-cycle-step-phase ins prev-st (car phases) x))
       ((when (svtv-cyclephase->outputs-captured (car phases)))
        outs1))
    (svtv-cycle-eval-outs ins nextst (cdr phases) x))
  ///
  (local (defun svtv-cycle-eval-outs-cong-ind (ins prev-st phases x x-equiv)
           (b* (((when (atom phases))
                 (mv ins prev-st x x-equiv)))
             (svtv-cycle-eval-outs-cong-ind
              ins (svtv-cycle-step-phase-nextsts ins prev-st (car phases) x)
              (cdr phases) x x-equiv))))
              
  (defcong svex-envs-similar svex-envs-equivalent (svtv-cycle-eval-outs ins prev-st phases x) 2
    :hints (("goal" :expand ((:free (prev-st) (svtv-cycle-eval-outs ins prev-st phases x))))))

  (defcong svex-envs-similar svex-envs-equivalent (svtv-cycle-eval-outs ins prev-st phases x) 1
    :hints (("goal" :expand ((:free (ins) (svtv-cycle-eval-outs ins prev-st phases x))))))

  (defcong base-fsm-eval-equiv svex-envs-equivalent (svtv-cycle-eval-outs ins prev-st phases x) 4
    :hints (("goal" :induct (svtv-cycle-eval-outs ins prev-st phases x)
             :expand ((:free (x) (svtv-cycle-eval-outs ins prev-st phases x)))))))



(define svtv-cycle-eval-nextst ((ins svex-env-p)
                                (prev-st svex-env-p)
                                (phases svtv-cyclephaselist-p)
                                (x base-fsm-p))
  :guard (and (equal (alist-keys prev-st) (svex-alist-keys (base-fsm->nextstate x)))
              (not (acl2::hons-dups-p (svex-alist-keys (base-fsm->nextstate x)))))
  :returns (nextst svex-env-p)
  (b* (((when (atom phases))
        (mbe :logic (svex-env-extract (svex-alist-keys (base-fsm->nextstate x)) prev-st)
             :exec prev-st))
       (nextst (svtv-cycle-step-phase-nextsts ins prev-st (car phases) x)))
    (svtv-cycle-eval-nextst ins nextst (cdr phases) x))
  ///

  (local (defthm svex-alist-keys-of-svex-env-extract
           (equal (alist-keys (svex-env-extract keys x))
                  (svarlist-fix keys))
           :hints(("Goal" :in-theory (enable svex-alist-keys svex-env-extract)))))

  (defret svex-alist-keys-of-<fn>
    (equal (alist-keys nextst)
           (svex-alist-keys (base-fsm->nextstate x))))

  (defcong svex-envs-similar svex-envs-equivalent (svtv-cycle-eval-nextst ins prev-st phases x) 2
    :hints (("goal" :expand ((:free (prev-st) (svtv-cycle-eval-nextst ins prev-st phases x))))))

  (defcong svex-envs-similar svex-envs-equivalent (svtv-cycle-eval-nextst ins prev-st phases x) 1
    :hints (("goal" :expand ((:free (ins) (svtv-cycle-eval-nextst ins prev-st phases x))))))

  (defcong base-fsm-eval-equiv svex-envs-equivalent (svtv-cycle-eval-nextst ins prev-st phases x) 4
    :hints (("goal" :induct (svtv-cycle-eval-nextst ins prev-st phases x)
             :expand ((:free (x) (svtv-cycle-eval-nextst ins prev-st phases x)))))))


(define svtv-cycle-eval ((ins svex-env-p)
                         (prev-st svex-env-p)
                         (phases svtv-cyclephaselist-p)
                         (x base-fsm-p))
  :guard (and (equal (alist-keys prev-st) (svex-alist-keys (base-fsm->nextstate x)))
              (not (acl2::hons-dups-p (svex-alist-keys (base-fsm->nextstate x)))))
  :returns (mv (outs (equal outs (svtv-cycle-eval-outs ins prev-st phases x)))
               (nextst (equal nextst (svtv-cycle-eval-nextst ins prev-st phases x))))
  :prepwork ((local (in-theory (enable svtv-cycle-eval-outs
                                       svtv-cycle-eval-nextst))))
  (b* (((when (atom phases))
        (mv nil
            (mbe :logic (svex-env-extract (svex-alist-keys (base-fsm->nextstate x)) prev-st)
                 :exec prev-st)))
       ((mv outs1 nextst) (svtv-cycle-step-phase ins prev-st (car phases) x))
       ((mv rest-outs final-st) (svtv-cycle-eval ins nextst (cdr phases) x)))
    (mv (if (svtv-cyclephase->outputs-captured (car phases))
            Outs1
          rest-outs)
        final-st)))


(define svtv-cycle-output-phase ((phases svtv-cyclephaselist-p))
  :returns (output-phase maybe-natp :rule-classes :type-prescription)
  (if (atom phases)
      nil
    (if (svtv-cyclephase->outputs-captured (car phases))
        0
      (let ((rest (svtv-cycle-output-phase (cdr phases))))
        (and rest
             (+ 1 rest)))))
  ///
  (defret outputs-captured-of-<fn>
    (implies output-phase
             (svtv-cyclephase->outputs-captured (nth output-phase phases))))

  (defret outputs-not-captured-of-<fn>
    (implies (not output-phase)
             (not (svtv-cyclephase->outputs-captured (nth output-phase phases)))))

  (defret outputs-not-captured-before-of-<fn>
    (implies (and output-phase
                  (< (nfix n) output-phase))
             (not (svtv-cyclephase->outputs-captured (nth n phases))))))
          



(define svtv-cycle-fsm-inputs ((ins svex-env-p)
                               (phases svtv-cyclephaselist-p))
  :returns (fsm-ins svex-envlist-p)
  (if (atom phases)
      nil
    (cons (svtv-cycle-step-fsm-inputs ins (car phases))
          (svtv-cycle-fsm-inputs ins (cdr phases))))
  ///
  (defretd svtv-cycle-eval-outs-is-fsm-eval-of-fsm-inputs
    (equal (svtv-cycle-eval-outs ins prev-st phases x)
           (let ((output-phase (svtv-cycle-output-phase phases)))
             (and output-phase
                  (nth output-phase (base-fsm-eval fsm-ins prev-st x)))))
    :hints(("Goal" :in-theory (enable base-fsm-eval
                                      svtv-cycle-eval-outs
                                      svtv-cycle-output-phase
                                      svtv-cycle-step-phase-nextsts-is-fsm-step-of-fsm-inputs
                                      svtv-cycle-step-phase-outs-is-fsm-step-outs-of-fsm-inputs)
            :induct (svtv-cycle-eval-outs ins prev-st phases x))))

  (defretd svtv-cycle-eval-nextst-is-fsm-final-state-of-fsm-inputs
    (equal (svtv-cycle-eval-nextst ins prev-st phases x)
           (base-fsm-final-state fsm-ins prev-st x))
    :hints(("Goal" :in-theory (enable base-fsm-final-state
                                      svtv-cycle-eval-nextst
                                      svtv-cycle-step-phase-nextsts-is-fsm-step-of-fsm-inputs)
            :induct (svtv-cycle-eval-nextst ins prev-st phases x))))

  (defret len-of-<fn>
    (equal (len fsm-ins) (len phases))))






(define svtv-cycle-run-fsm-inputs ((ins svex-envlist-p)
                                   (phases svtv-cyclephaselist-p))
  :returns (fsm-ins svex-envlist-p)
  :prepwork ((local (defthm svex-envlist-p-of-append
                      (implies (and (svex-envlist-p x)
                                    (svex-envlist-p y))
                               (svex-envlist-p (append x y))))))
  (if (atom ins)
      nil
    (append (svtv-cycle-fsm-inputs (car ins) phases)
            (svtv-cycle-run-fsm-inputs (cdr ins) phases))))
