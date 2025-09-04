; FGL - A Symbolic Simulation Framework for ACL2
;; SPDX-FileCopyrightText: Copyright 2025 Arm Limited and/or its affiliates <open-source-office@arm.com>
;; SPDX-License-Identifier: BSD-3-Clause
;; 
;; Redistribution and use in source and binary forms, with or without
;; modification, are permitted provided that the following conditions are
;; met:

;; o Redistributions of source code must retain the above copyright
;;   notice, this list of conditions and the following disclaimer.

;; o Redistributions in binary form must reproduce the above copyright
;;   notice, this list of conditions and the following disclaimer in the
;;   documentation and/or other materials provided with the distribution.

;; o Neither the name of the copyright holder nor the names of
;;   its contributors may be used to endorse or promote products derived
;;   from this software without specific prior written permission.

;; THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
;; "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
;; LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
;; A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
;; HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
;; SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
;; LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
;; DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
;; THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
;; (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
;; OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

;; Author: Sol Swords <sol.swords@arm.com>

(in-package "FGL")

(include-book "trace")

(local (in-theory (disable w)))

(define abort-current-rewrite (&key (interp-st 'interp-st))
  :returns new-interp-st
  (if (interp-st->errmsg interp-st)
      interp-st
    (update-interp-st->errmsg :abort-rewrite interp-st))
  ///
  (make-event `(progn . ,*fancy-ev-primitive-thms-no-state*)))

(fancy-ev-add-primitive abort-current-rewrite-fn t)

(encapsulate nil
  (local
   (progn
     (defthm w-of-put-global
       (implies (not (equal sym 'current-acl2-world))
                (equal (w (put-global sym val state))
                       (w state)))
       :hints(("Goal" :in-theory (enable put-global w))))
     (defthm w-of-read-acl2-oracle
       (equal (w (mv-nth 2 (read-acl2-oracle state)))
              (w state))
       :hints(("Goal" :in-theory (enable read-acl2-oracle update-acl2-oracle w))))
     (defthm w-of-iprint-oracle-upddes
       (equal (w (acl2::iprint-oracle-updates state))
              (w state))
       :hints(("Goal" :in-theory (e/d (acl2::iprint-oracle-updates)
                                      (put-global)))))
     (defthm w-of-update-open-input-channels
       (equal (w (update-open-input-channels x state))
              (w state))
       :hints(("Goal" :in-theory (enable w update-open-input-channels))))))
   
  (defthm w-of-read-object
    (equal (w (mv-nth 2 (read-object channel statE)))
           (w state))
    :hints(("Goal" :in-theory (disable nth update-open-input-channels))))
  (in-theory (disable read-object)))

(fancy-ev-add-primitive read-object (and (symbolp acl2::channel)
                                         (open-input-channel-p acl2::channel :object state)))

(fancy-ev-add-primitive open-input-channel-p (and (symbolp acl2::channel)
                                                  (member-eq acl2::typ acl2::*file-types*)))




(define fancy-repl ((prompt stringp)
                    (bindings symbol-alistp)
                    (reclimit natp)
                    (interp-st interp-st-bfrs-ok)
                    state)
  :returns (mv new-interp-st new-state)
  (b* (((when (zp reclimit)) (mv interp-st state))
       (channel *standard-oi*)
       ((unless (open-input-channel-p channel :object state))
        (mv interp-st state))
       (- (cw "~s0" prompt))
       ((mv eofp obj state) (read-object channel state))
       ((when eofp) (mv interp-st state))
       ((when (eq obj :exit)) (mv interp-st state))
       ((mv errmsg trans interp-st state)
        (fancy-translate obj 10000 interp-st state t t))
       ((when errmsg)
        (cw "~@0~%" errmsg)
        (fancy-repl prompt bindings (1- reclimit) interp-st state))
       ((mv errmsg val interp-st state)
        (fancy-ev trans bindings 10000 interp-st state t t))
       (- (if errmsg
              (cw "~@0~%" errmsg)
            (cw "~x0~%" val))))
    (fancy-repl prompt bindings (1- reclimit) interp-st state)))


;; (define trace-repl (&key ((bindings symbol-alistp) 'trace-meta-bindings)
;;                          ((interp-st interp-st-bfrs-ok) 'interp-st)
;;                          (state 'state))
;;   (b* (((mv interp-st state)
;;         (fancy-repl "trace> " (cons (cons 'trace-meta-bindings bindings) bindings)
;;                     10000 interp-st state)))
;;     (


(defmacro trace-repl (&key (bindings 'trace-meta-bindings))
  `(b* ((bindings ,bindings)
        (?ign (fancy-repl "trace> " (cons (cons 'trace-meta-bindings bindings) bindings)
                          10000 interp-st state)))
     :default))

(defxdoc trace-repl
  :parents (fgl-rewrite-tracing)
  :short "Enter a read-eval-print loop to explore the FGL state and modify traces."
  :long "<p>Invoking @('(fgl::trace-repl)') as part of a trace expression causes
entry into a read-eval-print loop where arbitrary code can be translated using
@(see fancy-translate) and executed using @(see fancy-ev). From this REPL, a
user can explore the FGL interpreter state in various ways and examine values
relevant to the current rewriting attempt. The variables discussed in @(see
fgl-trace) under \"Variables usable in tracing expressions\" can be referenced
from this REPL, including variables bound in the rule being applied.</p>

<p>To exit from this REPL, submit @(':exit').</p>")

(local (def-fancy-ev-primitives foo-bar))

(local
 (define test-fancy-repl ((prompt stringp)
                          (bindings symbol-alistp)
                          state)
   :guard-hints (("goal" :in-theory (disable create-interp-st)))
   (with-local-stobj interp-st
     (mv-let (interp-st state)
       (fancy-repl prompt bindings 10000 interp-st state)
       state))))

(local
 (define test-fancy-ev ((x pseudo-termp) (alist symbol-alistp) (reclimit natp) state hard-errp aokp)
   ;; this is all just to show interp-st-bfrs-ok of create-interp-st
   :guard-hints (("goal" :in-theory (disable create-interp-st)))
   (with-local-stobj interp-st
     (mv-let (err val interp-st state)
       (fancy-ev x alist reclimit interp-st state hard-errp aokp)
       (mv err val state)))))




(define fgl-trace-entry-fancy-translate-keyvals (keyvals
                                                 (interp-st interp-st-bfrs-ok)
                                                 state)
  :returns (mv err (entry true-listp :rule-classes :type-prescription)
               interp-st state)
  (if (or (atom keyvals)
          (atom (cdr keyvals)))
      (mv nil nil interp-st state)
    (b* (((mv err trans-val interp-st state)
          (fancy-translate (cadr keyvals) 10000 interp-st state t t))
         ((when err) (mv err nil interp-st state))
         ((mv err rest interp-st state)
          (fgl-trace-entry-fancy-translate-keyvals (cddr keyvals) interp-st state))
         ((when err) (mv err nil interp-st state)))
      (mv nil (cons (car keyvals) (cons trans-val rest)) interp-st state))))


(define fgl-trace-entry-fancy-translate (keyvals
                                              restore-rules
                                              (interp-st interp-st-bfrs-ok)
                                              state)
  :returns (mv err (entry true-listp :rule-classes :type-prescription)
               new-interp-st new-state)
  (b* (((mv err trans-keyvals interp-st state)
        (fgl-trace-entry-fancy-translate-keyvals keyvals interp-st state))
       ((when err) (mv err nil interp-st state)))
    (mv nil
        (append trans-keyvals
                (and restore-rules `(:restore-rules ,restore-rules)))
        interp-st state)))

(define fgl-trace*-fn (rune keyvals
                            restore-rules
                            (interp-st interp-st-bfrs-ok)
                            state)
  (b* (((unless (fgl-generic-rune-p rune))
        (mv "Rune must satisfy fgl-generic-rune-p" nil interp-st state))
       ((mv err entry interp-st state)
        (fgl-trace-entry-fancy-translate
         keyvals
         restore-rules
         interp-st
         state))
       ((when err) (mv err nil interp-st state))
       (old-alist (interp-st->trace-alist interp-st))
       (new-alist (cons (cons rune entry) old-alist))
       (interp-st (update-interp-st->trace-alist new-alist interp-st)))
    (mv nil entry interp-st state)))

(defmacro fgl-trace* (rune
                      &key
                      (cond 'nil cond-p)
                      (on-entry 'nil on-entry-p)
                      (on-relieve-hyp 'nil on-relieve-hyp-p)
                      (on-eval-success 'nil on-eval-success-p)
                      (on-eval-failure 'nil on-eval-failure-p)
                      (on-success 'nil on-success-p)
                      (on-failure 'nil on-failure-p)
                      (restore-rules 'nil))
  `(fgl-trace*-fn ',rune
                  (list . ,(append (and cond-p `(:cond ',cond))
                                   (and on-entry-p `(:on-entry ',on-entry))
                                   (and on-relieve-hyp-p `(:on-relieve-hyp ',on-relieve-hyp))
                                   (and on-eval-success-p `(:on-eval-success ',on-eval-success))
                                   (and on-eval-failure-p `(:on-eval-failure ',on-eval-failure))
                                   (and on-success-p `(:on-success ',on-success))
                                   (and on-failure-p `(:on-failure ',on-failure))))
                  ,restore-rules
                  interp-st
                  state))

(defxdoc fgl-trace*
  :parents (fgl-rewrite-tracing)
  :short "Add a trace for an FGL rule during symbolic execution"
  :long "<p>This macro has much the same interface as @(see fgl-trace), but affects the
traced rule alist in the FGL interpreter state instead of the traced rule alist
stored in the ACL2 state. The latter is copied over the former at the beginning
of any FGL invocation, whereas the former is used during FGL
processing. Therefore, this macro is effective only during FGL processing,
whereas @(see fgl-trace) is effective only outside FGL processing. This macro
can be invoked from trace expressions (see @(see fgl-trace) as well as @(see
syntax-interp), @(see syntax-bind), syntaxp, and bind-free forms.</p>")



(define fgl-untrace*-fn (rune &key (interp-st 'interp-st))
  (b* (((unless (fgl-generic-rune-p rune))
        (mv "Rune must satisfy fgl-generic-rune-p" nil interp-st))
       (old-alist (interp-st->trace-alist interp-st))
       (interp-st (update-interp-st->trace-alist
                   (remove-assoc-equal rune old-alist) interp-st)))
    (mv nil rune interp-st)))

(defmacro fgl-untrace* (rune &key (interp-st 'interp-st))
  `(fgl-untrace*-fn ',rune ,interp-st))

(defxdoc fgl-untrace*
  :parents (fgl-rewrite-tracing)
  :short "Untrace an FGL rule during symbolic execution"
  :long "<p>Removes the trace entry, if any, for the given FGL rune. Only useful during
FGL processing, whereas @(see fgl-untrace) does much the same thing outside of
FGL processing; see @(see fgl-trace*) for more explanation.</p>")

(define fgl-untrace-all* (&key (interp-st 'interp-st))
  (b* ((old-alist (interp-st->trace-alist interp-st))
       (interp-st (update-interp-st->trace-alist nil interp-st)))
    (mv nil (alist-keys old-alist) interp-st)))


(defxdoc fgl-untrace-all*
  :parents (fgl-rewrite-tracing)
  :short "Untrace all FGL rules during symbolic execution"
  :long "<p>This macro is only useful during FGL processing, whereas @(see
  fgl-untrace-all) does much the same thing outside of FGL processing; see
  @(see fgl-trace*) for more explanation.</p>")

(define fgl-modify-current-tracespec-fn (rune
                                         keyvals
                                         restore-rules
                                         (interp-st interp-st-bfrs-ok)
                                         state)
  (b* (((mv err entry interp-st state)
        (fgl-trace-entry-fancy-translate keyvals restore-rules interp-st state))
       ((when err)
        (mv err nil interp-st state))
       (interp-st
        (update-interp-st->tracespecs
         (cons (cons rune entry) (cdr (interp-st->tracespecs interp-st)))
         interp-st)))
    (mv nil entry interp-st state)))

(defmacro fgl-modify-current-tracespec
    (rune
     &key
     (cond 'nil cond-p)
     (on-entry 'nil on-entry-p)
     (on-relieve-hyp 'nil on-relieve-hyp-p)
     (on-eval-success 'nil on-eval-success-p)
     (on-eval-failure 'nil on-eval-failure-p)
     (on-success 'nil on-success-p)
     (on-failure 'nil on-failure-p)
     (restore-rules 'nil))
  `(fgl-modify-current-tracespec-fn ',rune
                                    (list . ,(append (and cond-p `(:cond ',cond))
                                                     (and on-entry-p `(:on-entry ',on-entry))
                                                     (and on-relieve-hyp-p `(:on-relieve-hyp ',on-relieve-hyp))
                                                     (and on-eval-success-p `(:on-eval-success ',on-eval-success))
                                                     (and on-eval-failure-p `(:on-eval-failure ',on-eval-failure))
                                                     (and on-success-p `(:on-success ',on-success))
                                                     (and on-failure-p `(:on-failure ',on-failure))))
                                    ,restore-rules
                                    interp-st
                                    state))

(defxdoc fgl-modify-current-tracespec
  :parents (fgl-rewrite-tracing)
  :short "When invoked from a trace expression, change the trace processing of the current rule invocation."
  :long "<p>If called from a trace expression for some particular rule
  invocation, this changes how the tracing for the rest of this rule invocation
  will work.</p>

<p>E.g., suppose a rule was initially traced as follows:</p>

@({
 (fgl::fgl-trace (:formula my-rule)
                 :on-entry (if (equal fgl::depth 5)
                               (let ((?ignore (fgl::fgl-modify-current-tracespec
                                               (:formula my-rule)
                                               :on-success nil
                                               :on-failure \"Failed at trace depth 5\")))
                                 \"Entering at trace depth 5\")
                             \"Entering at trace depth other than 5\")
                 :on-success \"Success at trace depth other than 5\"
                 :on-failure \"Failed at trace depth other than 5\")
 })

<p>This will generally print \"Entering at trace depth other than 5\" on entry
to the specified rule and \"(Success/Failed) at trace depth other than 5\" on
exit. However, if the rule is ever applied at a trace depth of 5, then it will
print \"Entering at trace depth 5\" and, because it modifies the current
tracespec, it will then only print \"Failed at trace depth 5\" if it failed but
print nothing if it succeeded.</p>

<p>Similarly, a trace formula may delete the current tracespec using @(see
fgl-delete-current-tracespec).</p>

")

(defmacro fgl-delete-current-tracespec ()
  '(update-interp-st->tracespecs
    (cons nil (cdr (interp-st->tracespecs interp-st)))
    interp-st))


(defxdoc fgl-delete-current-tracespec
  :parents (fgl-rewrite-tracing)
  :short "When invoked from a trace expression, stop further trace processing of the current rule invocation."
  :long "<p>See also @(see fgl-modify-current-tracespec).</p>")




(defxdoc fgl-advanced-tracing
  :parents (fgl-rewrite-tracing)
  :short "List of advanced things you can do while tracing a rewrite rule in FGL"
  :long "
<p>See @(see fgl-trace) for instructions to set up tracing of a rule. Here we
discuss various things you can do with such tracing:</p>

<ul>

<li>Replace the default printing of trace entry/exit forms with your own:
returning NIL from the on-entry/on-success/on-failure forms prevents printing
of the returned result, and invoking @(see cw) or @(see fmt-to-comment-window)
within the form lets you customize the printing.</li>

<li>Abort the application of the rule (cause it to fail) by invoking @(see
abort-current-rewrite), even in the @(':on-success') form.</li>

<li>Trace rule @('a') only while inside certain applications of rule @('b') by
tracing @('b') with the @(':restore-rules t') option and invoking @(see
fgl-trace*) for rule @('a') within its @(':on-entry') form. (See also @(see
fgl-untrace*) and @(see fgl-untrace-all*).)</li>

<li>Invoke @(see trace-repl) to enter a read-eval-print loop where you may
interactively examine all the information available in trace forms as well as
doing any of the things discussed here.</li>

<li>Modify the tracing behavior for the current rule application using @(see
fgl-modify-current-tracespec) or @(see fgl-delete-current-tracespec),
particularly from the @(see trace-repl).</li>

</ul>
")
