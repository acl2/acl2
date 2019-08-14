; GL - A Symbolic Simulation Framework for ACL2
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
(include-book "centaur/meta/pseudo-rewrite-rule" :dir :system)



(encapsulate
  (((gl-rewrite-try-rule-trace * * * interp-st state) => interp-st
    :formals (status rule call interp-st state)
    :guard (and (pseudo-rewrite-rule-p rule)
                (gl-object-p call))))

  (set-ignore-ok t)
  (set-irrelevant-formals-ok t)
  (local (defun gl-rewrite-try-rule-trace (status rule call interp-st state)
           (declare (xargs :stobjs (interp-st state)
                           :guard (and (pseudo-rewrite-rule-p rule)
                                       (gl-object-p call))))
           interp-st))

  (defthm interp-st-get-of-gl-rewrite-try-rule-trace
    (implies (not (equal (interp-st-field-fix key) :trace-scratch))
             (equal (interp-st-get key (gl-rewrite-try-rule-trace status rule call interp-st state))
                    (interp-st-get key interp-st)))))

(define gl-rewrite-try-rule-trace-wrapper (trace
                                           status
                                           (rule pseudo-rewrite-rule-p)
                                           (call gl-object-p)
                                           interp-st
                                           state)
  :inline t
  (if trace
      (gl-rewrite-try-rule-trace status rule call interp-st state)
    interp-st)
  ///
  (defthm interp-st-get-of-gl-rewrite-try-rule-trace-wrapper
    (implies (not (equal (interp-st-field-fix key) :trace-scratch))
             (equal (interp-st-get key (gl-rewrite-try-rule-trace-wrapper
                                        trace status rule call interp-st state))
                    (interp-st-get key interp-st)))))


(define gl-rewrite-rule-try-trace-default (status
                                           (rule pseudo-rewrite-rule-p)
                                           (call gl-object-p)
                                           interp-st state)
  :returns new-interp-st
  (b* ((rule-alist (and (boundp-global :fgl-trace-rule-alist state)
                        (@ :fgl-trace-rule-alist)))
       ((unless (alistp rule-alist))
        (er hard? 'gl-rewrite-rule-try-trace-default "Bad :fgl-trace-rule-alist -- not an alist")
        interp-st)
       (rune (acl2::rewrite-rule->rune rule))
       (look (assoc-equal rune rule-alist))
       ((unless look)
        interp-st)
       (depth (nfix (interp-st->trace-scratch interp-st)))
       (evisc-tuple (and (boundp-global :fgl-trace-evisc-tuple state)
                         (@ :fgl-trace-evisc-tuple))))
    (case-match status
      (':start
       (prog2$ (fmt-to-comment-window
                "~t0~x1> ~x2 ~x3~%"
                (pairlis2 acl2::*base-10-chars* (list depth depth rune call))
                0 evisc-tuple nil)
               (update-interp-st->trace-scratch (1+ depth) interp-st)))
      ((':hyps . failed-hyp)
       (b* ((errmsg (interp-st->errmsg interp-st))
            ((when errmsg)
             (fmt-to-comment-window
              "~t0<~x1 ~x2 failed (error in hyps: ~@3)~%"
              (pairlis2 acl2::*base-10-chars* (list (1- depth) (1- depth) rune
                                                    (if (msgp errmsg)
                                                        errmsg
                                                      (msg "~x0" errmsg))))
              0 evisc-tuple nil)
             (update-interp-st->trace-scratch (1- depth) interp-st))
            ((when failed-hyp)
             (fmt-to-comment-window
              "~t0<~x1 ~x2 failed (hyp ~x3)~%"
              (pairlis2 acl2::*base-10-chars* (list (1- depth) (1- depth) rune failed-hyp))
              0 evisc-tuple nil)
             (update-interp-st->trace-scratch (1- depth) interp-st)))
         interp-st))
      ((':finish . val)
       (b* ((errmsg (interp-st->errmsg interp-st))
            ((when errmsg)
             (fmt-to-comment-window
              "~t0<~x1 ~x2 failed (error: ~@3)~%"
              (pairlis2 acl2::*base-10-chars* (list (1- depth) (1- depth) rune
                                                    (if (msgp errmsg)
                                                        errmsg
                                                      (msg "~x0" errmsg))))
              0 evisc-tuple nil)
             (update-interp-st->trace-scratch (1- depth) interp-st)))
         (fmt-to-comment-window
          "~t0<~x1 ~x2 success: ~x3~%"
          (pairlis2 acl2::*base-10-chars* (list (1- depth) (1- depth) rune val))
          0 evisc-tuple nil)
         (update-interp-st->trace-scratch (1- depth) interp-st)))
      (& (prog2$ (cw "bad status: ~x0~%" status)
                 interp-st))))
  ///
  (defret interp-st-get-of-<fn>
    (implies (not (Equal (interp-st-field-fix key) :trace-scratch))
             (equal (interp-st-get key new-interp-st)
                    (interp-st-get key interp-st)))))

(defattach gl-rewrite-try-rule-trace gl-rewrite-rule-try-trace-default)

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

<p>If the attachment for the tracing function has changed, it may be reset to
the default function as follows:</p>

@({
 (defattach gl-rewrite-try-rule-trace gl-rewrite-rule-try-trace-default)
 })

<h3>Custom Tracing</h3>

<p>The default attachment for the tracing function may be replaced with a
custom version.  It may be useful to base it upon the default implementation,
@('gl-rewrite-rule-try-trace-default').  The tracing function must take the
following inputs:</p>

<ul>

<li>@('status'), which is either @(':start') or one of the pairs
 @('(:hyps . failed-hyp)') or @('(:finish . val)').  Details below.</li>

<li>@('rule'), the rewrite rule structure of the rule being attempted, with
guard @('(pseudo-rewrite-rule-p rule)')</li>

<li>@('call'), the term to be rewritten, with which the LHS was unified</li>

<li>@('interp-st'), the FGL interpreter state</li>

<li>@('state'), the ACL2 state.</li>
</ul>

<p>The function must return only a new @('interp-st'), of which the only field
that may be modified is the @('trace-scratch') field.  This field of the
interpreter state may be used to record any state necessary for the trace
printing.  For example, the default implementation uses it to store the trace
depth.</p>

<p>To install your custom trace function, you may attach it to the function
@('gl-rewrite-try-rule-trace').  Note, however, that this won't even be called
unless tracing is enabled by setting the @(':fgl-trace-rewrites') state
global.</p>

<h3>Status argument</h3>

<p>The @('status') argument passed to the tracing function tells what phase of applying the rule we are in:</p>

<ul>

<li>@(':start') signifies that the current function call has successfully
unified with the LHS of the rule, so we are ready to begin relieving hyps.</li>

<li>@('(:hyps . failed-hyp)') signifies that we have finished relieving hyps.
There are three possible outcomes: there might have been an error while
relieving hyps, in which case @('(interp-st->errmsg interp-st)') is non-NIL.
Otherwise, if one of the hyps failed, the number of that hyp is passed as
@('failed-hyp').  Otherwise if @('failed-hyp') is NIL, we have successfully
relieved all the hyps and will go on to interpret the RHS.</li>

<li>@('(:finish . val)') signifies that we are done interpreting the RHS of the
rule.  There may have been an error, in which case @('(interp-st->errmsg
interp-st)') is non-NIL.  Otherwise, @('val') is the symbolic object value
returned from the interpretation of the RHS.</li>

</ul>

")
