; FGL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2019 Centaur Technology
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

(include-book "interp-st")
(include-book "binder-rules")

(local (std::add-default-post-define-hook :fix))

(encapsulate
  (((fgl-rewrite-traced-rule-p * interp-st state) => *
    :formals (rule interp-st state)
    :guard (fgl-generic-rule-p rule)))

  
  
  (set-ignore-ok t)
  (set-irrelevant-formals-ok t)

  (local (defun fgl-rewrite-traced-rule-p (rule interp-st state)
           (declare (xargs :stobjs (interp-st state)
                           :guard (and (fgl-generic-rule-p rule))))
           nil))

  ;; (fty::deffixequiv fgl-rewrite-traced-rule-p :args ((rule fgl-generic-rule-p)))
  )


(define fgl-rewrite-traced-rule-p-default ((rule fgl-generic-rule-p)
                                           interp-st state)
  (declare (ignorable interp-st state))
  (b* ((rule-alist (and (boundp-global :fgl-trace-rule-alist state)
                        (@ :fgl-trace-rule-alist)))
       ((unless (alistp rule-alist))
        (er hard? 'fgl-rewrite-rule-try-trace-default "Bad :fgl-trace-rule-alist -- not an alist")
        nil)
       (rune (fgl-generic-rule->rune rule)))
    (assoc-equal rune rule-alist)))

(defattach fgl-rewrite-traced-rule-p fgl-rewrite-traced-rule-p-default)

(encapsulate
  (((fgl-rewrite-trace-cond * * * interp-st state) => *
    :formals (rule fn args interp-st state)
    :guard (and (pseudo-fnsym-p fn)
                (fgl-objectlist-p args)
                (fgl-generic-rule-p rule))))

  
  
  (set-ignore-ok t)
  (set-irrelevant-formals-ok t)

  (local (defun fgl-rewrite-trace-cond (rule fn args interp-st state)
           (declare (xargs :stobjs (interp-st state)
                           :guard (and (fgl-generic-rule-p rule)
                                       (pseudo-fnsym-p fn)
                                       (fgl-objectlist-p args))))
           nil))

  ;; (fty::deffixequiv fgl-rewrite-trace-cond :args ((rule fgl-generic-rule-p)
  ;;                                                 (fn pseudo-fnsym-p)
  ;;                                                 (args fgl-objectlist-p)))
  )

(define fgl-rewrite-trace-cond-default ((rule fgl-generic-rule-p)
                                        (fn pseudo-fnsym-p)
                                        (args fgl-objectlist-p)
                                        interp-st state)
  :ignore-ok t
  t)

(defattach fgl-rewrite-trace-cond fgl-rewrite-trace-cond-default)

(encapsulate
  (((fgl-rewrite-trace-start-output * * * * interp-st state) => *
    :formals (depth rule fn args interp-st state)
    :guard (and (natp depth)
                (fgl-generic-rule-p rule)
                (pseudo-fnsym-p fn)
                (fgl-objectlist-p args))))
  
  (set-ignore-ok t)
  (set-irrelevant-formals-ok t)
  (local (defun fgl-rewrite-trace-start-output (depth rule fn args interp-st state)
           (declare (xargs :stobjs (interp-st state)
                           :guard (and (natp depth)
                                       (fgl-generic-rule-p rule)
                                       (pseudo-fnsym-p fn)
                                       (fgl-objectlist-p args))))
           nil))

  ;; (fty::deffixequiv fgl-rewrite-trace-start-output :args ((rule fgl-generic-rule-p)
  ;;                                                         (fn pseudo-fnsym-p)
  ;;                                                         (args fgl-objectlist-p)
  ;;                                                         (depth natp)))
  )

(define fgl-rewrite-trace-start-output-default ((depth natp)
                                                (rule fgl-generic-rule-p)
                                                (fn pseudo-fnsym-p)
                                                (args fgl-objectlist-p)
                                                interp-st state)
  (declare (ignorable interp-st state))
  (b* ((rune (fgl-generic-rule->rune rule))
       (evisc-tuple (and (boundp-global :fgl-trace-evisc-tuple state)
                         (@ :fgl-trace-evisc-tuple))))
    (fmt-to-comment-window
     "~t0~x1> ~x2 ~x3~%"
     (pairlis2 acl2::*base-10-chars* (list depth depth rune
                                           (cons fn args)))
     0 evisc-tuple nil)))

(defattach fgl-rewrite-trace-start-output fgl-rewrite-trace-start-output-default)

(encapsulate
  (((fgl-rewrite-trace-success-output * * * * * interp-st state) => *
    :formals (depth val rule fn args interp-st state)
    :guard (and (natp depth)
                (fgl-object-p val)
                (fgl-generic-rule-p rule)
                (pseudo-fnsym-p fn)
                (fgl-objectlist-p args))))
  
  (set-ignore-ok t)
  (set-irrelevant-formals-ok t)
  (local (defun fgl-rewrite-trace-success-output (depth val rule fn args interp-st state)
           (declare (xargs :stobjs (interp-st state)
                           :guard (and (natp depth)
                                       (fgl-object-p val)
                                       (fgl-generic-rule-p rule)
                                       (pseudo-fnsym-p fn)
                                       (fgl-objectlist-p args))))
           nil))


  ;; (fty::deffixequiv fgl-rewrite-trace-success-output :args ((rule fgl-generic-rule-p)
  ;;                                                           (val fgl-object-p)
  ;;                                                           (depth natp)))
  )

(define fgl-rewrite-trace-success-output-default ((depth natp)
                                                  (val fgl-object-p)
                                                  (rule fgl-generic-rule-p)
                                                  (fn pseudo-fnsym-p)
                                                  (args fgl-objectlist-p)
                                                  interp-st state)
  (declare (ignore fn args interp-st))
  (b* ((rune (fgl-generic-rule->rune rule))
       (evisc-tuple (and (boundp-global :fgl-trace-evisc-tuple state)
                         (@ :fgl-trace-evisc-tuple))))
    (fmt-to-comment-window
     "~t0<~x1 ~x2 success: ~x3~%"
     (pairlis2 acl2::*base-10-chars* (list depth depth rune val))
     0 evisc-tuple nil)))

(defattach fgl-rewrite-trace-success-output fgl-rewrite-trace-success-output-default)
  


(encapsulate
  (((fgl-rewrite-trace-failure-output * * * * * interp-st state) => *
    :formals (depth failed-hyp rule fn args interp-st state)
    :guard (and (natp depth)
                (acl2::maybe-natp failed-hyp)
                (fgl-generic-rule-p rule)
                (pseudo-fnsym-p fn)
                (fgl-objectlist-p args))))
  
  (set-ignore-ok t)
  (set-irrelevant-formals-ok t)
  (local (defun fgl-rewrite-trace-failure-output (depth failed-hyp rule fn args interp-st state)
           (declare (xargs :stobjs (interp-st state)
                           :guard (and (natp depth)
                                       (fgl-generic-rule-p rule)
                                       (pseudo-fnsym-p fn)
                                       (fgl-objectlist-p args)
                                       (acl2::maybe-natp failed-hyp))))
           nil))


  ;; (fty::deffixequiv fgl-rewrite-trace-failure-output :args ((rule fgl-generic-rule-p)
  ;;                                                           (failed-hyp acl2::maybe-natp)
  ;;                                                           (depth natp)))
  )

(define fgl-rewrite-trace-failure-output-default ((depth natp)
                                                  (failed-hyp acl2::maybe-natp)
                                                  (rule fgl-generic-rule-p)
                                                  (fn pseudo-fnsym-p)
                                                  (args fgl-objectlist-p)
                                                  interp-st state)
  (declare (ignore fn args))
  (b* ((rune (fgl-generic-rule->rune rule))
       (evisc-tuple (and (boundp-global :fgl-trace-evisc-tuple state)
                         (@ :fgl-trace-evisc-tuple)))
       (errmsg (interp-st->errmsg interp-st)))
    (fmt-to-comment-window
     "~t0<~x1 ~x2 failed (~@3)~%"
     (pairlis2 acl2::*base-10-chars*
               (list depth depth rune
                     (cond ((msgp errmsg) errmsg)
                           (errmsg (msg "~x0" errmsg))
                           (failed-hyp (msg "hyp ~x0 failed" failed-hyp))
                           (t "aborted"))))
     0 evisc-tuple nil)))

(defattach fgl-rewrite-trace-failure-output fgl-rewrite-trace-failure-output-default)



(define fgl-rewrite-do-trace?! ((rule fgl-generic-rule-p)
                                (fn pseudo-fnsym-p)
                                (args fgl-objectlist-p)
                                interp-st state)
  :inline t
  (b* ((rule (fgl-generic-rule-fix rule)))
    (and (fgl-rewrite-traced-rule-p rule interp-st state)
         (fgl-rewrite-trace-cond rule (pseudo-fnsym-fix fn)
                                 (fgl-objectlist-fix args)
                                 interp-st state))))

(define fgl-rewrite-do-trace? ((rule fgl-generic-rule-p)
                               (fn pseudo-fnsym-p)
                               (args fgl-objectlist-p)
                               interp-st state)
  :inline t
  (b* ((flags (interp-st->flags interp-st)))
    (and (interp-flags->trace-rewrites flags)
         (fgl-rewrite-do-trace?! rule fn args interp-st state))))
       



(define interp-st-trace-data (interp-st)
  :guard-hints (("goal" :in-theory (enable stack$a-nth-scratch-kind
                                           stack$a-nth-scratch)))
  :returns (mv ok
               (rule (implies ok (fgl-generic-rule-p rule)))
               (phase acl2::maybe-natp :rule-classes :type-prescription)
               (args fgl-objectlist-p))
  (stobj-let ((stack (interp-st->stack interp-st)))
             (ok rule phase args)
             (b* ((rule (stack-rule stack))
                  ((unless rule) (mv nil nil nil nil))
                  ((unless (and (eql (stack-scratch-len stack) 0)
                                (< 0 (stack-full-scratch-len stack))
                                (eql (stack-nth-scratch-kind 0 stack) :fgl-objlist)))
                   (mv nil nil nil nil))
                  (args (stack-nth-scratch-fgl-objlist 0 stack))
                  (phase (stack-phase stack)))
               (mv t rule phase args))
             (mv ok rule phase args)))

(define interp-st-do-trace? ((fn pseudo-fnsym-p) interp-st state)
  (b* ((flags (interp-st->flags interp-st))
       ((unless (interp-flags->trace-rewrites flags)) nil)
       ((mv ok rule ?phase args) (interp-st-trace-data interp-st)))
    (and ok (fgl-rewrite-do-trace?! rule fn args interp-st state))))

(define fgl-rewrite-trace-start! ((rule fgl-generic-rule-p)
                                  (fn pseudo-fnsym-p)
                                  (args fgl-objectlist-p)
                                  interp-st state)
  :returns (new-interp-st)
  (b* ((depth (+ 1 (nfix (interp-st->trace-scratch interp-st))))
       (interp-st (update-interp-st->trace-scratch depth interp-st)))
    (fgl-rewrite-trace-start-output
     depth (fgl-generic-rule-fix rule) (pseudo-fnsym-fix fn)
     (fgl-objectlist-fix args) interp-st state)
    interp-st)
  ///
  (defret interp-st-get-of-<fn>
    (implies (not (equal (interp-st-field-fix key) :trace-scratch))
             (equal (interp-st-get key new-interp-st)
                    (interp-st-get key interp-st)))))

(define fgl-rewrite-trace-start (tracep
                                 (rule fgl-generic-rule-p)
                                 (fn pseudo-fnsym-p)
                                 (args fgl-objectlist-p)
                                 interp-st state)
  :returns (new-interp-st)
  :inline t
  (if tracep
      (fgl-rewrite-trace-start! rule fn args interp-st state)
    interp-st)
  ///
  (defret interp-st-get-of-<fn>
    (implies (not (equal (interp-st-field-fix key) :trace-scratch))
             (equal (interp-st-get key new-interp-st)
                    (interp-st-get key interp-st)))))
                                 

(define interp-st-trace-start (tracep (fn pseudo-fnsym-p) interp-st state)
  :returns (new-interp-st)
  (b* (((unless tracep) interp-st)
       ((mv ok rule ?phase args) (interp-st-trace-data interp-st))
       ((unless ok) interp-st))
    (fgl-rewrite-trace-start! rule fn args interp-st state))
  ///
  (defret interp-st-get-of-<fn>
    (implies (not (equal (interp-st-field-fix key) :trace-scratch))
             (equal (interp-st-get key new-interp-st)
                    (interp-st-get key interp-st)))))

(define fgl-rewrite-trace-hyp-failure! ((failed-hyp acl2::maybe-natp)
                                        (rule fgl-generic-rule-p)
                                        (fn pseudo-fnsym-p)
                                        (args fgl-objectlist-p)
                                        interp-st state)
  :returns (new-interp-st)
  (b* ((depth (pos-fix (interp-st->trace-scratch interp-st)))
       (interp-st (update-interp-st->trace-scratch (1- depth) interp-st)))
    (fgl-rewrite-trace-failure-output depth (acl2::maybe-natp-fix failed-hyp)
                                      rule (pseudo-fnsym-fix fn) args
                                      interp-st state)
    interp-st)
  ///
  (defret interp-st-get-of-<fn>
    (implies (not (equal (interp-st-field-fix key) :trace-scratch))
             (equal (interp-st-get key new-interp-st)
                    (interp-st-get key interp-st)))))

(define fgl-rewrite-trace-hyp-failure (tracep
                                       (failed-hyp acl2::maybe-natp)
                                       (rule fgl-generic-rule-p)
                                       (fn pseudo-fnsym-p)
                                       (args fgl-objectlist-p)
                                       interp-st state)
  :returns (new-interp-st)
  :inline t
  (if tracep
      (fgl-rewrite-trace-hyp-failure! failed-hyp rule fn args interp-st state)
    interp-st)
  ///
  (defret interp-st-get-of-<fn>
    (implies (not (equal (interp-st-field-fix key) :trace-scratch))
             (equal (interp-st-get key new-interp-st)
                    (interp-st-get key interp-st)))))


(define interp-st-trace-hyp-failure (tracep (failed-hyp acl2::maybe-natp) (fn pseudo-fnsym-p)
                                            interp-st state)
  :returns (new-interp-st)
  (b* (((unless tracep) interp-st)
       ((mv ok rule ?phase args) (interp-st-trace-data interp-st))
       ((unless ok) interp-st))
    (fgl-rewrite-trace-hyp-failure! failed-hyp rule fn args interp-st state))
  ///
  (defret interp-st-get-of-<fn>
    (implies (not (equal (interp-st-field-fix key) :trace-scratch))
             (equal (interp-st-get key new-interp-st)
                    (interp-st-get key interp-st)))))
  
  
(define fgl-rewrite-trace-finish! (successp
                                   (val fgl-object-p)
                                   (rule fgl-generic-rule-p)
                                   (fn pseudo-fnsym-p)
                                   (args fgl-objectlist-p)
                                   interp-st state)
  :returns (new-interp-st)
  (b* ((depth (pos-fix (interp-st->trace-scratch interp-st)))
       (interp-st (update-interp-st->trace-scratch (1- depth) interp-st)))
    (if (and successp
             (not (interp-st->errmsg interp-st)))
        (fgl-rewrite-trace-success-output
         depth (fgl-object-fix val) rule (pseudo-fnsym-fix fn)
         args interp-st state)
      (fgl-rewrite-trace-failure-output
       depth nil rule (pseudo-fnsym-fix fn)
       args interp-st state))
    interp-st)
  ///
  (defret interp-st-get-of-<fn>
    (implies (not (equal (interp-st-field-fix key) :trace-scratch))
             (equal (interp-st-get key new-interp-st)
                    (interp-st-get key interp-st)))))

(define fgl-rewrite-trace-finish (tracep successp
                                         (val fgl-object-p)
                                         (rule fgl-generic-rule-p)
                                         (fn pseudo-fnsym-p)
                                         (args fgl-objectlist-p)
                                         interp-st state)
  :returns (new-interp-st)
  :inline t
  (if tracep
      (fgl-rewrite-trace-finish! successp val rule fn args interp-st state)
    interp-st)
  ///
  (defret interp-st-get-of-<fn>
    (implies (not (equal (interp-st-field-fix key) :trace-scratch))
             (equal (interp-st-get key new-interp-st)
                    (interp-st-get key interp-st)))))


(define interp-st-trace-finish (tracep successp (val fgl-object-p)
                                       (fn pseudo-fnsym-p) interp-st state)
  :returns (new-interp-st)
  (b* (((unless tracep) interp-st)
       ((mv ok rule ?phase args) (interp-st-trace-data interp-st))
       ((unless ok) interp-st))
    (fgl-rewrite-trace-finish! successp val rule fn args interp-st state))
  ///
  (defret interp-st-get-of-<fn>
    (implies (not (equal (interp-st-field-fix key) :trace-scratch))
             (equal (interp-st-get key new-interp-st)
                    (interp-st-get key interp-st)))))

(defmacro fgl-rewrite-trace-defaults ()
  '(progn (defattach fgl-rewrite-traced-rule-p fgl-rewrite-traced-rule-p-default)
          (defattach fgl-rewrite-trace-cond fgl-rewrite-trace-cond-default)
          (defattach fgl-rewrite-trace-start-output fgl-rewrite-trace-start-output-default)
          (defattach fgl-rewrite-trace-success-output fgl-rewrite-trace-success-output-default)
          (defattach fgl-rewrite-trace-failure-output fgl-rewrite-trace-failure-output-default))) 

(defxdoc fgl-rewrite-tracing
  :parents (fgl)
  :short "How to trace the FGL rewriter"
  :long "

<p>FGL allows attempts at applying rewrite rules to be traced using a
configurable tracing function.  By default, a basic tracing function is
provided such that the user only needs to set up some state global variables to
enable and use it.  The function that performs the trace printing is
attachable, so more advanced users can replace it with a custom version.</p>

<h3>Basic Tracing</h3>

<p>The default tracing implementation may be activated by setting the following
state globals:</p>

@({
 ;; Enable the tracing function
 (assign :fgl-trace-rewrites t)

 ;; Alist whose keys are the rules that will be traced
 (assign :fgl-trace-rule-alist '(((:rewrite fgl::fgl-lognot))))

 ;; Evisc tuple for trace output
 (assign :fgl-trace-evisc-tuple (evisc-tuple 8 12 nil nil))

 })

<p>If the attachments for the tracing functions have changed, they may be reset to
the default functions as follows:</p>

@({
 (fgl-rewrite-trace-defaults)
 })

<h3>Custom Tracing</h3>

<p>The default attachment for the tracing functions may be replaced with
custom versions.  It may be useful to base it upon the default implementations,
which append \"-default\" to the name of each function; i.e., the default implementation for @('fgl-rewrite-trace-cond') is @('fgl-rewrite-trace-cond-default').</p>

<p>The tracing functions have the following signatures:</p>

@({
  (fgl-rewrite-traced-rule-p rule interp-st state)
  (fgl-rewrite-trace-cond rule fn args interp-st state)
  (fgl-rewrite-trace-start-output depth rule fn args interp-st state)
  (fgl-rewrite-trace-success-output depth val rule fn args interp-st state)
  (fgl-rewrite-trace-failure-output depth failed-hyp rule fn args interp-st state)
 })

<p>where the inputs are as follows:</p>

<ul>

<li>@('rule'), the rule being attempted, satisfying @('(fgl-generic-rule-p rule)')</li>

<li>@('fn') and @('args') of the object that the rule is being applied to,
where @('args') satisfies @('fgl-objectlist-p')</li>

<li>@('depth'), the current stack depth of traced rule applications</li>

<li>@('status'), either @(':start'), @(':hyps'), @(':finish'), or @(':abort')</li>

<li>@('val'), the return value from a successful rewrite</li>

<li>@('failed-hyp'), the index of the hypothesis that failed or @('nil') if the
rule application failed for some other reason</li>

<li>@('interp-st'), the FGL interpreter state</li>

<li>@('state'), the ACL2 state.</li>
</ul>

")
