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
(include-book "fancy-ev")

(local (std::add-default-post-define-hook :fix))

(local (in-theory (disable w)))

(encapsulate
  (((fgl-rewrite-rule-tracespec * interp-st state) => *
    :formals (rule interp-st state)
    :guard (fgl-generic-rule-p rule)))

  
  
  (set-ignore-ok t)
  (set-irrelevant-formals-ok t)

  (define fgl-rewrite-rule-tracespec ((rule fgl-generic-rule-p)
                                      interp-st state)
    :returns (tracespec true-listp :rule-classes :type-prescription)
    :local-def t :progn t :hooks nil
    nil
    ///
    (fty::deffixequiv fgl-rewrite-rule-tracespec :skip-cong-thm t)))

(fty::deffixequiv fgl-rewrite-rule-tracespec)

(local (defthm true-listp-lookup-in-trace-alist
         (implies (trace-alist-p x)
                  (true-listp (assoc key x)))))

(define fgl-rewrite-rule-tracespec-default ((rule fgl-generic-rule-p)
                                           interp-st state)
  (declare (ignorable state))
  :returns (tracespec true-listp :rule-classes :type-prescription)
  (assoc-equal (fgl-generic-rule->rune rule)
               (interp-st->trace-alist interp-st)))

(defattach fgl-rewrite-rule-tracespec fgl-rewrite-rule-tracespec-default)

(encapsulate
  (((fgl-rewrite-trace-cond * * * interp-st state) => (mv * interp-st state)
    :formals (rule tracespec bindings interp-st state)
    :guard (and (fgl-generic-rule-p rule)
                (true-listp tracespec)
                (fgl-object-bindings-p bindings)
                (interp-st-bfrs-ok interp-st))))

  
  
  (set-ignore-ok t)
  (set-irrelevant-formals-ok t)

  (define fgl-rewrite-trace-cond ((rule fgl-generic-rule-p)
                                  (tracespec true-listp)
                                  (bindings fgl-object-bindings-p)
                                  (interp-st interp-st-bfrs-ok)
                                  state)
    :returns (mv cond new-interp-st new-state)
    :local-def t :progn t :hooks nil
    (mv nil interp-st state)
    ///
    (make-event `(progn . ,*fancy-ev-primitive-thms*))
    (fty::deffixequiv fgl-rewrite-trace-cond :skip-cong-thm t)))

(fty::deffixequiv fgl-rewrite-trace-cond)

(local (defthm symbol-alistp-when-fgl-object-bindings-p
         (implies (fgl-object-bindings-p x)
                  (symbol-alistp x))))

(define fgl-rewrite-trace-cond-default ((rule fgl-generic-rule-p)
                                        (tracespec true-listp)
                                        (bindings fgl-object-bindings-p)
                                        (interp-st interp-st-bfrs-ok)
                                        state)
  :ignore-ok t
  :returns (mv val new-interp-st new-state)
  (b* ((tracespec (llist-fix tracespec))
       (keyvals (cdr tracespec))
       (tracecond-look (member :cond keyvals))
       ((unless tracecond-look)
        (mv t interp-st state))
       (tracecond-expr (cadr tracecond-look))
       ((unless (pseudo-termp tracecond-expr))
        (raise "Error: trace condition ~x0 for rule ~x1 is not a pseudo-term" tracecond-expr (fgl-generic-rule->rune rule))
        (mv nil interp-st state))
       (bindings (fgl-object-bindings-fix bindings))
       ((mv err val interp-st state) (fancy-ev tracecond-expr `((bindings . ,bindings) . ,bindings) 1000 interp-st state t t))
       ((when err)
        (raise "Error evaluating trace condition ~x0 for rule ~x1: ~@2" tracecond-expr (fgl-generic-rule->rune rule) err)
        (mv nil interp-st state)))
    (mv val interp-st state))
  ///
  (make-event `(progn . ,*fancy-ev-primitive-thms*)))

(defattach fgl-rewrite-trace-cond fgl-rewrite-trace-cond-default)

(encapsulate
  (((fgl-rewrite-trace-start-output * * * * interp-st state) => (mv interp-st state)
    :formals (depth rule tracespec bindings interp-st state)
    :guard (and (natp depth)
                (fgl-generic-rule-p rule)
                (true-listp tracespec)
                (fgl-object-bindings-p bindings) 
                (interp-st-bfrs-ok interp-st))))
  
  (set-ignore-ok t)
  (set-irrelevant-formals-ok t)
  (define fgl-rewrite-trace-start-output ((depth natp)
                                          (rule fgl-generic-rule-p)
                                          (tracespec true-listp)
                                          (bindings fgl-object-bindings-p)
                                          (interp-st interp-st-bfrs-ok)
                                          state)
    :returns (mv new-interp-st new-state)
    :local-def t :progn t :hooks nil
    (mv interp-st state)
    ///
    (make-event `(progn . ,*fancy-ev-primitive-thms*))
    (fty::deffixequiv fgl-rewrite-trace-start-output :skip-cong-thm t)))

(fty::deffixequiv fgl-rewrite-trace-start-output)
  

(local (defthm true-listp-of-member-equal
         (implies (true-listp x)
                  (true-listp (member-equal k x)))
         :rule-classes :type-prescription))

(define my-get-global ((name symbolp) state)
  :hooks nil
  (and (boundp-global name state)
       (f-get-global name state)))

(define fgl-rewrite-trace-start-output-default ((depth natp)
                                                (rule fgl-generic-rule-p)
                                                (tracespec true-listp)
                                                (bindings fgl-object-bindings-p)
                                                (interp-st interp-st-bfrs-ok)
                                                state)
  :returns (mv new-interp-st new-state)
  (b* ((tracespec (llist-fix tracespec))
       (keyvals (cdr tracespec))
       (entry-look (member :entry keyvals))
       ((unless entry-look)
        (b* ((rune (fgl-generic-rule->rune rule))
             (evisc-tuple (my-get-global :fgl-trace-evisc-tuple state)))
          (fmt-to-comment-window
           "~t0~x1> ~x2 ~x3~%"
           (pairlis2 acl2::*base-10-chars* (list depth depth rune bindings))
           0 evisc-tuple nil))
        (mv interp-st state))
       (entry-expr (cadr entry-look))
       ((unless (pseudo-termp entry-expr))
        (raise "Error: trace entry term ~x0 for rule ~x1 is not a pseudo-term" entry-expr (fgl-generic-rule->rune rule))
        (mv interp-st state))
       (bindings (fgl-object-bindings-fix bindings))
       ((mv err val interp-st state) (fancy-ev entry-expr `((bindings . ,bindings) . ,bindings) 1000 interp-st state t t))
       ((when err)
        (raise "Error evaluating trace entry term ~x0 for rule ~x1: ~@2" entry-expr (fgl-generic-rule->rune rule) err)
        (mv interp-st state)))
    (and val
         (b* ((evisc-tuple (my-get-global :fgl-trace-evisc-tuple state)))
           (fmt-to-comment-window
            "~t0~x1> ~x2~%"
            (pairlis2 acl2::*base-10-chars* (list depth depth val))
            0 evisc-tuple nil)))
    (mv interp-st state))
  ///
  (make-event `(progn . ,*fancy-ev-primitive-thms*)))

(defattach fgl-rewrite-trace-start-output fgl-rewrite-trace-start-output-default)

(encapsulate
  (((fgl-rewrite-trace-success-output * * * * * interp-st state) => (mv interp-st state)
    :formals (depth result rule tracespec bindings interp-st state)
    :guard (and (natp depth)
                (fgl-object-p result)
                (fgl-generic-rule-p rule)
                (true-listp tracespec)
                (fgl-object-bindings-p bindings)
                (interp-st-bfrs-ok interp-st))))
  
  (set-ignore-ok t)
  (set-irrelevant-formals-ok t)
  (define fgl-rewrite-trace-success-output ((depth natp)
                                            (result fgl-object-p)
                                            (rule fgl-generic-rule-p)
                                            (tracespec true-listp)
                                            (bindings fgl-object-bindings-p)
                                            (interp-st interp-st-bfrs-ok)
                                            state)
    :returns (mv new-interp-st new-state)
    :local-def t :progn t :hooks nil
    (mv interp-st state)
    ///
    (make-event `(progn . ,*fancy-ev-primitive-thms*))
    (fty::deffixequiv fgl-rewrite-trace-success-output :skip-cong-thm t)))

(fty::deffixequiv fgl-rewrite-trace-success-output)

(define fgl-rewrite-trace-success-output-default ((depth natp)
                                                  (result fgl-object-p)
                                                  (rule fgl-generic-rule-p)
                                                  (tracespec true-listp)
                                                  (bindings fgl-object-bindings-p)
                                                  (interp-st interp-st-bfrs-ok)
                                                  state)
  :returns (mv new-interp-st new-state)
  (b* ((tracespec (llist-fix tracespec))
       (result (fgl-object-fix result))
       (keyvals (cdr tracespec))
       (success-look (member :on-success keyvals))
       ((unless success-look)
        (b* ((rune (fgl-generic-rule->rune rule))
             (evisc-tuple (my-get-global :fgl-trace-evisc-tuple state)))
          (fmt-to-comment-window
           "~t0<~x1 ~x2 success: ~x3~%"
           (pairlis2 acl2::*base-10-chars* (list depth depth rune result))
           0 evisc-tuple nil))
        (mv interp-st state))
       (success-expr (cadr success-look))
       ((unless (pseudo-termp success-expr))
        (raise "Error: trace success term ~x0 for rule ~x1 is not a pseudo-term" success-expr (fgl-generic-rule->rune rule))
        (mv interp-st state))
       (bindings (fgl-object-bindings-fix bindings))
       ((mv err val interp-st state) (fancy-ev success-expr `((result . ,result) (bindings . ,bindings) . ,bindings) 1000 interp-st state t t))
       ((when err)
        (raise "Error evaluating trace success term ~x0 for rule ~x1: ~@2" success-expr (fgl-generic-rule->rune rule) err)
        (mv interp-st state)))
    (and val
         (b* ((evisc-tuple (my-get-global :fgl-trace-evisc-tuple state)))
           (fmt-to-comment-window
            "~t0~x1> ~x2~%"
            (pairlis2 acl2::*base-10-chars* (list depth depth val))
            0 evisc-tuple nil)))
    (mv interp-st state))
  ///
  (make-event `(progn . ,*fancy-ev-primitive-thms*)))

(defattach fgl-rewrite-trace-success-output fgl-rewrite-trace-success-output-default)
  


(encapsulate
  (((fgl-rewrite-trace-failure-output * * * * * interp-st state) => (mv interp-st state)
    :formals (depth failed-hyp rule tracespec bindings interp-st state)
    :guard (and (natp depth)
                (acl2::maybe-natp failed-hyp)
                (fgl-generic-rule-p rule)
                (true-listp tracespec)
                (fgl-object-bindings-p bindings)
                (interp-st-bfrs-ok interp-st))))
  
  (set-ignore-ok t)
  (set-irrelevant-formals-ok t)
  (define fgl-rewrite-trace-failure-output ((depth natp)
                                            (failed-hyp acl2::maybe-natp)
                                            (rule fgl-generic-rule-p)
                                            (tracespec true-listp)
                                            (bindings fgl-object-bindings-p)
                                            (interp-st interp-st-bfrs-ok)
                                            state)
    :returns (mv new-interp-st new-state)
    :local-def t :progn t :hooks nil
    (mv interp-st state)
    ///
    (make-event `(progn . ,*fancy-ev-primitive-thms*))
    (fty::deffixequiv fgl-rewrite-trace-failure-output :skip-cong-thm t)))

(fty::deffixequiv fgl-rewrite-trace-failure-output)

(define fgl-rewrite-trace-failure-output-default ((depth natp)
                                                  (failed-hyp acl2::maybe-natp)
                                                  (rule fgl-generic-rule-p)
                                                  (tracespec true-listp)
                                                  (bindings fgl-object-bindings-p)
                                                  (interp-st interp-st-bfrs-ok)
                                                  state)
  :returns (mv new-interp-st new-state)
  (b* ((tracespec (llist-fix tracespec))
       (failed-hyp (acl2::maybe-natp-fix failed-hyp))
       (keyvals (cdr tracespec))
       (failure-look (member :on-failure keyvals))
       ((unless failure-look)
        (b* ((rune (fgl-generic-rule->rune rule))
             (evisc-tuple (my-get-global :fgl-trace-evisc-tuple state))
             (errmsg (interp-st->errmsg interp-st)))
          (fmt-to-comment-window
           "~t0<~x1 ~x2 failed (~@3)~%"
           (pairlis2 acl2::*base-10-chars*
                     (list depth depth rune
                           (cond ((msgp errmsg) errmsg)
                                 (errmsg (msg "~x0" errmsg))
                                 (failed-hyp (msg "hyp ~x0 failed" failed-hyp))
                                 (t "aborted"))))
           0 evisc-tuple nil))
        (mv interp-st state))
       (failure-expr (cadr failure-look))
       ((unless (pseudo-termp failure-expr))
        (raise "Error: trace failure term ~x0 for rule ~x1 is not a pseudo-term" failure-expr (fgl-generic-rule->rune rule))
        (mv interp-st state))
       (bindings (fgl-object-bindings-fix bindings))
       ((mv err val interp-st state) (fancy-ev failure-expr `((failed-hyp . ,failed-hyp) (bindings . ,bindings) . ,bindings) 1000 interp-st state t t))
       ((when err)
        (raise "Error evaluating trace failure term ~x0 for rule ~x1: ~@2" failure-expr (fgl-generic-rule->rune rule) err)
        (mv interp-st state)))
    (and val
         (b* ((evisc-tuple (my-get-global :fgl-trace-evisc-tuple state)))
           (fmt-to-comment-window
            "~t0~x1> ~x2~%"
            (pairlis2 acl2::*base-10-chars* (list depth depth val))
            0 evisc-tuple nil)))
    (mv interp-st state))
  ///
  (make-event `(progn . ,*fancy-ev-primitive-thms*)))


(defattach fgl-rewrite-trace-failure-output fgl-rewrite-trace-failure-output-default)



;; Interp-st-do-trace: two versions -- one for meta/primitive rules that takes
;; the rule, fn, and args to which the rule is to be applied; these create the
;; bindings as `((x . ,(g-apply fn args))). The one for rewrites extracts the
;; rule and bindings from the top stack frame of the interp-st (using
;; interp-st-trace-data).
(define interp-st-do-trace-meta ((rule fgl-generic-rule-p)
                                 (fn pseudo-fnsym-p)
                                 (args fgl-objectlist-p)
                                 (interp-st interp-st-bfrs-ok)
                                 state)
  :returns (mv (tracespec true-listp :rule-classes :type-prescription)
               new-interp-st new-state)
  (b* (((unless (interp-flags->trace-rewrites (interp-st->flags interp-st)))
        (mv nil interp-st state))
       (tracespec (fgl-rewrite-rule-tracespec rule interp-st state))
       ((unless tracespec) (mv nil interp-st state))
       (bindings `((x . ,(g-apply fn args))))
       ((mv ok interp-st state)
        (fgl-rewrite-trace-cond rule tracespec bindings interp-st state)))
    (mv (and ok tracespec) interp-st state))
  ///
  (make-event `(progn . ,*fancy-ev-primitive-thms*)))

(define interp-st-trace-data (interp-st)
  :guard-hints (("goal" :in-theory (enable stack$a-nth-scratch-kind
                                           stack$a-nth-scratch)))
  :returns (mv ok
               (rule (implies ok (fgl-generic-rule-p rule)))
               (bindings fgl-object-bindings-p))
  (stobj-let ((stack (interp-st->stack interp-st)))
             (ok rule bindings)
             (b* ((rule (stack-rule stack))
                  ((unless rule) (mv nil nil nil))
                  (bindings (stack-bindings stack)))
               (mv t rule bindings))
             (mv ok rule bindings)))

(define interp-st-do-trace-rewrite ((interp-st interp-st-bfrs-ok) state)
  :returns (mv (tracespec true-listp :rule-classes :type-prescription)
               new-interp-st new-state)
  (b* (((unless (interp-flags->trace-rewrites (interp-st->flags interp-st)))
        (mv nil interp-st state))
       ((mv ok rule bindings) (interp-st-trace-data interp-st))
       ((unless ok) (mv nil interp-st state))
       (tracespec (fgl-rewrite-rule-tracespec rule interp-st state))
       ((unless tracespec) (mv nil interp-st state))
       ((mv ok interp-st state)
        (fgl-rewrite-trace-cond rule tracespec bindings interp-st state)))
    (mv (and ok tracespec) interp-st state))
  ///
  (make-event `(progn . ,*fancy-ev-primitive-thms*)))

(define fgl-rewrite-trace-start ((rule fgl-generic-rule-p)
                                 (tracespec true-listp)
                                 (bindings fgl-object-bindings-p)
                                 (interp-st interp-st-bfrs-ok)
                                 state)
  :returns (mv new-interp-st new-state)
  (b* ((depth (+ 1 (nfix (interp-st->trace-scratch interp-st))))
       (interp-st (update-interp-st->trace-scratch depth interp-st)))
    (fgl-rewrite-trace-start-output
     depth rule tracespec bindings interp-st state))
  ///
  (local (include-book "tools/trivial-ancestors-check" :dir :system))
  (local (acl2::use-trivial-ancestors-check))
  (make-event `(progn . ,*fancy-ev-primitive-thms*)))
                                 

(define interp-st-trace-start-rewrite ((tracespec true-listp)
                                       (interp-st interp-st-bfrs-ok)
                                       state)
  :returns (mv new-interp-st new-state)
  (b* (((unless (llist-fix tracespec)) (mv interp-st state))
       ((mv ok rule bindings) (interp-st-trace-data interp-st))
       ((unless ok) (mv interp-st state)))
    (fgl-rewrite-trace-start rule tracespec bindings interp-st state))
  ///
  (make-event `(progn . ,*fancy-ev-primitive-thms*)))

(define interp-st-trace-start-meta ((tracespec true-listp)
                                    (rule fgl-generic-rule-p)
                                    (fn pseudo-fnsym-p)
                                    (args fgl-objectlist-p)
                                    (interp-st interp-st-bfrs-ok)
                                    state)
  :returns (mv new-interp-st new-state)
  (b* (((unless (llist-fix tracespec)) (mv interp-st state)))
    (fgl-rewrite-trace-start
     rule tracespec `((x . ,(g-apply fn args))) interp-st state))
  ///
  (make-event `(progn . ,*fancy-ev-primitive-thms*)))

(define fgl-rewrite-trace-hyp-failure ((failed-hyp acl2::maybe-natp)
                                        (rule fgl-generic-rule-p)
                                        (tracespec true-listp)
                                        (bindings fgl-object-bindings-p)
                                        (interp-st interp-st-bfrs-ok)
                                        state)
  :returns (mv new-interp-st new-state)
  (b* ((depth (pos-fix (interp-st->trace-scratch interp-st)))
       (interp-st (update-interp-st->trace-scratch (1- depth) interp-st)))
    (fgl-rewrite-trace-failure-output depth (acl2::maybe-natp-fix failed-hyp)
                                      rule tracespec bindings interp-st state))
  ///
  (local (include-book "tools/trivial-ancestors-check" :dir :system))
  (local (acl2::use-trivial-ancestors-check))
  (make-event `(progn . ,*fancy-ev-primitive-thms*)))


(define interp-st-trace-rewrite-hyp-failure ((tracespec true-listp)
                                             (failed-hyp acl2::maybe-natp)
                                             (interp-st interp-st-bfrs-ok)
                                             state)
  :returns (mv new-interp-st new-state)
  (b* (((unless (llist-fix tracespec)) (mv interp-st state))
       ((mv ok rule bindings) (interp-st-trace-data interp-st))
       ((unless ok) (mv interp-st state)))
    (fgl-rewrite-trace-hyp-failure failed-hyp rule tracespec bindings interp-st state))
  ///
  (make-event `(progn . ,*fancy-ev-primitive-thms*)))
  
  
(define fgl-rewrite-trace-finish (successp
                                  (result fgl-object-p)
                                  (rule fgl-generic-rule-p)
                                  (tracespec true-listp)
                                  (bindings fgl-object-bindings-p)
                                  (interp-st interp-st-bfrs-ok)
                                  state)
  :returns (mv new-interp-st new-state)
  (b* ((depth (pos-fix (interp-st->trace-scratch interp-st)))
       (interp-st (update-interp-st->trace-scratch (1- depth) interp-st)))
    (if (and successp
             (not (interp-st->errmsg interp-st)))
        (fgl-rewrite-trace-success-output
         depth result rule tracespec bindings interp-st state)
      (fgl-rewrite-trace-failure-output
       depth nil rule tracespec bindings interp-st state)))
  ///
  (local (include-book "tools/trivial-ancestors-check" :dir :system))
  (local (acl2::use-trivial-ancestors-check))
  (make-event `(progn . ,*fancy-ev-primitive-thms*)))


(define interp-st-trace-finish-rewrite ((tracespec true-listp)
                                        successp
                                        (result fgl-object-p)
                                        (interp-st interp-st-bfrs-ok)
                                        state)
  :returns (mv new-interp-st new-state)
  (b* (((unless (llist-fix tracespec)) (mv interp-st state))
       ((mv ok rule bindings) (interp-st-trace-data interp-st))
       ((unless ok) (mv interp-st state)))
    (fgl-rewrite-trace-finish successp result rule tracespec bindings interp-st state))
  ///
  (make-event `(progn . ,*fancy-ev-primitive-thms*)))

(define interp-st-trace-finish-meta ((tracespec true-listp)
                                     successp
                                     (result fgl-object-p)
                                     (rule fgl-generic-rule-p)
                                     (fn pseudo-fnsym-p)
                                     (args fgl-objectlist-p)
                                     (interp-st interp-st-bfrs-ok)
                                     state)
  :returns (mv new-interp-st new-state)
  (b* (((unless (llist-fix tracespec)) (mv interp-st state)))
    (fgl-rewrite-trace-finish successp result rule tracespec `((x . ,(g-apply fn args))) interp-st state))
  ///
  (make-event `(progn . ,*fancy-ev-primitive-thms*)))

(defmacro fgl-rewrite-trace-defaults ()
  '(progn (defattach fgl-rewrite-rule-tracespec fgl-rewrite-rule-tracespec-default)
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
  (fgl-rewrite-rule-tracespec rule interp-st state) => tracespec
  (fgl-rewrite-trace-cond rule tracespec bindings interp-st state) => (mv cond interp-st state)
  (fgl-rewrite-trace-start-output depth rule tracespec bindings interp-st state) => (mv interp-st state)
  (fgl-rewrite-trace-success-output depth result rule tracespec bindings interp-st state) => (mv interp-st state)
  (fgl-rewrite-trace-failure-output depth failed-hyp rule tracespec bindings interp-st state) => (mv interp-st state)
 })

<p>where the inputs are as follows:</p>

<ul>

<li>@('rule'), the rule being attempted, satisfying @('(fgl-generic-rule-p rule)')</li>

<li>@('bindings') are the unifying substitution under which the rule is being applied,
satistying @('fgl-object-bindings-p')</li>

<li>@('depth'), the current stack depth of traced rule applications</li>

<li>@('status'), either @(':start'), @(':hyps'), @(':finish'), or @(':abort')</li>

<li>@('val'), the return value from a successful rewrite</li>

<li>@('failed-hyp'), the index of the hypothesis that failed or @('nil') if the
rule application failed for some other reason</li>

<li>@('interp-st'), the FGL interpreter state</li>

<li>@('state'), the ACL2 state.</li>
</ul>

")
