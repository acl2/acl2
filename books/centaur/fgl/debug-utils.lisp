; FGL - A Symbolic Simulation Framework for ACL2
;
; SPDX-FileCopyrightText: Copyright 2025 Arm Limited and/or its affiliates <open-source-office@arm.com>
; SPDX-License-Identifier: MIT
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
; Original author: Sol Swords <sol.swords@arm.com>

(in-package "FGL")

(include-book "interp")

(local (in-theory (disable (tau-system))))

(local (defthm len-equal-0
         (equal (equal (len x) 0)
                (not (consp x)))))


(local (defthmd equal-cons-split
         (equal (equal x (cons y z))
                (and (consp x)
                     (equal (car x) y)
                     (equal (cdr x) z)))))


(define stack-rewind-scratch (stack)
  :measure (stack-scratch-len stack)
  :hints(("Goal" :in-theory (enable stack$a-scratch-len
                                    stack$a-pop-scratch)))
  (if (< 0 (stack-scratch-len stack))
      (b* ((stack (stack-pop-scratch stack)))
        (stack-rewind-scratch stack))
    (mbe :logic (non-exec (major-stack-fix stack)) :exec stack))
  ///
  (defthm stack$a-scratch-len-of-<fn>
    (equal (stack$a-scratch-len (stack-rewind-scratch stack)) 0))

  (defthmd stack-rewind-scratch-redef
    (equal (stack-rewind-scratch x)
           (B* (((MAJOR-FRAME JFRAME) (CAR X))
                ((MINOR-FRAME NFRAME)
                 (CAR JFRAME.MINOR-STACK)))
             (MAJOR-STACK-FIX
              (CONS
               (CHANGE-MAJOR-FRAME
                JFRAME
                :MINOR-STACK (CONS (CHANGE-MINOR-FRAME NFRAME :SCRATCH nil)
                                   (CDR JFRAME.MINOR-STACK)))
               (CDR X)))))
    :hints(("Goal" :induct (stack-rewind-scratch x)
            :expand ((major-stack-fix x))
            :in-theory (enable equal-cons-split
                               stack$a-scratch-len
                               stack$a-pop-scratch)))))

(define stack-pop-minor-frames (stack)
  :measure (stack-minor-frames stack)
  :prepwork ((local (in-theory (enable stack$a-minor-frames
                                       stack$a-pop-minor-frame
                                       stack$a-scratch-len
                                       stack-rewind-scratch-redef))))
  (b* ((stack (stack-rewind-scratch stack)))
    (if (< 1 (stack-minor-frames stack))
        (b* ((stack (stack-pop-minor-frame stack)))
          (stack-pop-minor-frames stack))
      (mbe :logic (non-exec (major-stack-fix stack)) :exec stack)))
  ///
  
  (defthm stack-pop-minor-frames-redef
    (Equal (stack-pop-minor-frames x)
           (b* (((major-frame jframe) (car x))
                ((minor-frame nframe) (nth (- (len jframe.minor-stack) 1) jframe.minor-stack)))
             (major-stack-fix
              (cons
               (change-major-frame jframe
                                   :minor-stack (list (change-minor-frame nframe :scratch nil)))
               (cdr x)))))))


(define stack-pop-n-frames! ((n natp) stack)
  :measure (nfix n)
  :guard (< n (stack-frames stack))
  :prepwork ((in-theory (enable stack$a-frames
                                      stack$a-pop-frame
                                      stack$a-scratch-len
                                      stack$a-minor-frames)))
  (if (zp n)
      (mbe :logic (non-exec (major-stack-fix stack)) :exec stack)
    (b* ((stack (stack-pop-minor-frames stack))
         (stack (stack-pop-frame stack)))
      (stack-pop-n-frames! (1- n) stack)))
  ///
  (local (defthm nthcdr-of-nil
           (equal (nthcdr n nil) nil)))
  (local (defthm nthcdr-of-major-stack-fix
           (equal (nthcdr n (major-stack-fix x))
                  (if (< (nfix n) (len x))
                      (major-stack-fix (nthcdr n x))
                    (if (zp n)
                        (major-stack-fix nil)
                      nil)))
           :hints (("goal" :induct (nthcdr n x)
                    :expand ((major-stack-fix x))))))
  (local (defthm major-stack-fix-of-atom
           (implies (and (syntaxp (not (equal x ''nil)))
                         (not (consp x)))
                    (equal (major-stack-fix x)
                           (major-stack-fix nil)))
           :hints(("Goal" :in-theory (enable major-stack-fix)))))

  (local (defthm consp-of-nthcdr
           (iff (consp (nthcdr n x))
                (< (nfix n) (len x)))
           :hints(("Goal" :induct (nthcdr n x)))))
  
  (defthmd stack-pop-n-frames!-redef
    (equal (stack-pop-n-frames! n stack)
           (major-stack-fix (nthcdr n stack)))))


(define fgl-generic-rule-bound-vars ((x fgl-generic-rule-p))
  :returns (bound-vars (implies (not (equal bound-vars t))
                                (pseudo-var-list-p bound-vars)))
  :guard-hints(("Goal" :in-theory (enable tag-when-fgl-generic-rule-p)))
  (case (tag x)
    (:brewrite (termlist-vars (fgl-binder-rule-brewrite->lhs-args x)))
    (:rewrite (term-vars (cmr::rewrite->lhs (fgl-rule-rewrite->rule x))))
    (otherwise t)))

(define fgl-generic-rule-hyps ((x fgl-generic-rule-p))
  :returns (hyps pseudo-term-listp)
  :guard-hints(("Goal" :in-theory (enable tag-when-fgl-generic-rule-p)))
  (case (tag x)
    (:brewrite (fgl-binder-rule-brewrite->hyps x))
    (:rewrite (cmr::rewrite->hyps (fgl-rule-rewrite->rule x)))
    (otherwise nil)))

(define fgl-generic-rule-hyps ((x fgl-generic-rule-p))
  :returns (hyps pseudo-term-listp)
  :guard-hints(("Goal" :in-theory (enable tag-when-fgl-generic-rule-p)))
  (case (tag x)
    (:brewrite (fgl-binder-rule-brewrite->hyps x))
    (:rewrite (cmr::rewrite->hyps (fgl-rule-rewrite->rule x)))
    (otherwise nil)))

(define fgl-generic-rule-rhs ((x fgl-generic-rule-p))
  :returns (rhs pseudo-termp)
  :guard-hints(("Goal" :in-theory (enable tag-when-fgl-generic-rule-p)))
  (case (tag x)
    (:brewrite (fgl-binder-rule-brewrite->rhs x))
    (:rewrite (cmr::rewrite->rhs (fgl-rule-rewrite->rule x)))
    (otherwise nil)))

(define fgl-object-bindings-keep-keys ((keys pseudo-var-list-p)
                                       (x fgl-object-bindings-p))
  :returns (new-x fgl-object-bindings-p)
  (if (atom x)
      nil
    (if (and (mbt (and (consp (car X))
                       (pseudo-var-p (caar x))))
             (member-eq (caar x) (pseudo-var-list-fix keys)))
        (cons (mbe :logic (cons (caar x) (fgl-object-fix (cdar x)))
                   :exec (car x))
              (fgl-object-bindings-keep-keys keys (cdr x)))
      (fgl-object-bindings-keep-keys keys (cdr x))))
  ///
  (defret member-bfrlist-of-<fn>
    (implies (not (member-equal v (fgl-object-bindings-bfrlist x)))
             (not (member-equal v (fgl-object-bindings-bfrlist new-x))))
    :hints(("Goal" :in-theory (enable fgl-object-bindings-bfrlist)))))

(local (in-theory (disable (tau-system))))
        

(define stack-reset-top-frame (stack)
  (b* ((stack (stack-pop-minor-frames stack))
       (stack (stack-set-minor-bindings nil stack))
       (stack (stack-set-term-index 0 stack))
       (rule (stack-rule stack))
       (bound-vars (or (not rule) (fgl-generic-rule-bound-vars rule))))
    (if (eq bound-vars t)
        stack
      (stack-set-bindings (fgl-object-bindings-keep-keys bound-vars (stack-bindings stack))
                          stack)))
  ///
  (defthm minor-frames-of-stack-reset-top-frame
    (equal (stack$a-minor-frames (stack-reset-top-frame stack)) 1)
    :hints(("Goal" :in-theory (enable stack-pop-minor-frames-redef
                                      stack$a-minor-frames
                                      stack$a-set-minor-bindings
                                      stack$a-set-term-index
                                      stack$a-set-bindings))))

  (defthm scratch-of-stack-reset-top-frame
    (equal (stack$a-scratch-len (stack-reset-top-frame stack)) 0)
    :hints(("Goal" :in-theory (enable stack-pop-minor-frames-redef
                                      stack$a-minor-frames
                                      stack$a-set-minor-bindings
                                      stack$a-set-term-index
                                      stack$a-set-bindings
                                      stack$a-scratch-len))))

  (defthm stack-frames-of-stack-reset-top-frame
    (equal (stack$a-frames (stack-reset-top-frame stack))
           (stack$a-frames stack))
    :hints(("Goal" :in-theory (enable stack-pop-minor-frames-redef
                                      stack$a-set-minor-bindings
                                      stack$a-set-term-index
                                      stack$a-set-bindings
                                      stack$a-frames))))

  (defthmd stack-reset-top-frame-redef
    (Equal (stack-reset-top-frame x)
           (b* (((major-frame jframe) (car x))
                ((minor-frame nframe) (nth (- (len jframe.minor-stack) 1) jframe.minor-stack)))
             (major-stack-fix
              (cons
               (change-major-frame jframe
                                   :minor-stack (list (change-minor-frame nframe :scratch nil :bindings nil :term-index 0))
                                   :bindings (b* ((bound-vars (fgl-generic-rule-bound-vars jframe.rule)))
                                               (if (or (not jframe.rule)
                                                       (eq bound-vars t))
                                                   jframe.bindings
                                                 (fgl-object-bindings-keep-keys bound-vars jframe.bindings))))
               (cdr x)))))
    :hints(("Goal" :in-theory (enable stack-pop-minor-frames-redef
                                      stack$a-set-minor-bindings
                                      stack$a-set-term-index
                                      stack$a-set-bindings
                                      stack$a-frames
                                      stack$a-rule
                                      stack$a-bindings)))))
                 
(define interp-st-reset-top-stack-frame (interp-st)
  (stobj-let ((stack (interp-st->stack interp-st)))
             (stack)
             (stack-reset-top-frame stack)
             interp-st))

(define interp-st-stack-rule (interp-st)
  (stobj-let ((stack (interp-st->stack interp-st)))
             (rule)
             (stack-rule stack)
             rule))

(define interp-st-pop-n-frames! ((n natp) interp-st)
  :guard (< n (interp-st-stack-frames interp-st))
  (stobj-let ((stack (interp-st->stack interp-st)))
             (stack)
             (stack-pop-n-frames! n stack)
             interp-st))

(define fgl-replay-top-rewrite-rule-core (&key
                                          ((equiv-contexts equiv-contextsp) 'nil)
                                          ((interp-st interp-st-bfrs-ok) 'interp-st)
                                          (state 'state))
  :guard (and (< 1 (interp-st-stack-frames interp-st))
              (interp-st-stack-rule interp-st)
              (member (tag (interp-st-stack-rule interp-st)) '(:rewrite :brewrite)))
  :guard-hints (("goal" :in-theory (enable interp-st-stack-frames
                                           interp-st-stack-rule
                                           stack-reset-top-frame-redef
                                           stack$a-frames
                                           stack$a-minor-frames
                                           stack$a-scratch-len
                                           stack$a-pop-frame
                                           stack$a-bindings
                                           bfr-listp-when-not-member-witness)))
  (stobj-let ((stack (interp-st->stack interp-st)))
             (rule bindings hyps rhs stack)
             (b* ((rule (stack-rule stack))
                  (hyps (fgl-generic-rule-hyps rule))
                  (rhs (fgl-generic-rule-rhs rule))
                  (stack (stack-reset-top-frame stack))
                  (bindings (hons-copy (stack-bindings stack)))
                  (stack (stack-pop-frame stack)))
               (mv rule bindings hyps rhs stack))
             (b* ((interp-st (update-interp-st->errmsg nil interp-st)))
               (fgl-rewrite-apply-rule
                rule 'anonymous bindings hyps rhs equiv-contexts interp-st state))))



(defxdoc fgl-replay-top-rewrite-rule
  :parents (fgl-debugging)
  :short "Utility that retries the topmost rewrite rule event on the FGL interpreter stack."
  :long "
<h3>Prerequisite</h3>
<p>This utility must first be installed using</p>
@({
 (include-book \"centaur/fgl/debug-utils\" :dir :system)
 (fgl::def-fgl-replay-top-rewrite-rule)
 })
<p>This event defines the @('fgl-replay-top-rewrite-rule') function by skipping
the proof of a known unsound guard conjecture. This is necessary (for now)
because the FGL interpreter function that the utility calls has a guard that
cannot be executed.</p>

<h3>Usage</h3>
<p>The form</p>
@({
 (fgl::fgl-replay-top-rewrite-rule)
 })
<p>reruns the rewrite rule attempt that is on the top of the FGL interpreter stack.</p>

<h3>Use Cases</h3>

<p>We outline some cases in which this might be a useful debugging tool, and
how to get it to work (i.e., how to leave the interpreter in a state where this
tool can be used) in those cases. Further information on useful debugging
techniques for all of these cases is below in the Debugging Techniques
section.</p>

<h4>Debugging Interpreter Errors</h4>

<p>Often a problem in an FGL proof is revealed when the interpreter produces an
error.  However, in the usual case, the stack has already been emptied when the
interpreter returns, and this utility won't work in that case.  To change this,
you can run either of the following two forms:</p>

@({
 (fgl::stop-on-fgl-error)
 (fgl::break-on-fgl-error)
 })

<p>These will cause the FGL interpreter to (respectively) quit or enter the
Lisp debugger when the first unrecoverable error is encountered.  This ensures
that the interpreter stack is kept in the state it was in when the error
occurred. You can examine the stack by saving it to an object using @(see
save-fgl-stack).</p>

<h4>Debugging Slowdowns</h4>

<p>If the FGL interpreter appears to be hanging or running forever, it might be
useful to interrupt it. At this point the stack can be examined using @(see
save-fgl-stack) and this utility can be used to perform further debugging (see
below).</p>

<h4>Finding Bad Object Constructs</h4>

<p>Sometimes examining the stack reveals an object of a form that shouldn't
exist, perhaps because some rewrite rule didn't work as expected. A technique
to cause the interpreter to stop when something of that form is created is to
add a rewrite rule that matches the offending form and causes an interpreter
error, e.g.:</p>
@({
 (fgl::def-fgl-rewrite stop-on-bad-form
    (equal (foo (bar x))
           (fgl::fgl-prog2
            (syntax-interp (er hard? 'stop-on-bad-form \"bad form: ~x0~%\"
                               (fgl::g-apply 'foo (list (fgl::g-apply 'bar (list x))))))
            (foo (bar x)))))
 })


<h3>Debugging with @('fgl-replay-top-rewrite-rule')</h3>

<p>The best use of @('fgl-replay-top-rewrite-rule') is to debug the particular
FGL rewriting context where something went wrong. Because it doesn't need to
rerun the whole proof from the begininng, you can make better use of expensive
debugging techniques like tracing rewrite rules (see @(see
fgl-rewrite-tracing)) or even tracing the FGL interpreter itself (see @(see
acl2::trace$)).</p>

<p>Sometimes the topmost rewrite rule in the FGL stack isn't the most useful
place to start. After examining the stack with @(see save-fgl-stack), you may
wish to start execution at a prior stack frame. (This is also necessary in the
unlikely event that the top frame of the stack is an application of a
non-@(':rewrite') @(':brewrite') rule.) This can be done by popping the
required number of frames off the stack as follows, and then running
@('fgl-replay-top-rewrite-rule'):</p>

@({
 (fgl::interp-st-pop-n-frames 10 fgl::interp-st)
 })

")

(defmacro def-fgl-replay-top-rewrite-rule ()
  (progn$ (cw "~%~%** WARNING: fgl-replay-top-rewrite-rule defined with unsound guard. **~%~%")
          '(skip-proofs
            (define fgl-replay-top-rewrite-rule (&key
                                                 ((equiv-contexts equiv-contextsp) 'nil)
                                                 (interp-st 'interp-st)
                                                 (state 'state))
              :guard (and (< 1 (interp-st-stack-frames interp-st))
                          (interp-st-stack-rule interp-st)
                          (member (tag (interp-st-stack-rule interp-st)) '(:rewrite :brewrite)))
              (fgl-replay-top-rewrite-rule-core :equiv-contexts equiv-contexts)))))

