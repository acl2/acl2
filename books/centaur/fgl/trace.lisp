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
(local (include-book "tools/trivial-ancestors-check" :dir :System))

(local (std::add-default-post-define-hook :fix))

(local (in-theory (disable w)))

(local (defthm true-listp-lookup-in-trace-alist
         (implies (trace-alist-p x)
                  (true-listp (assoc key x)))))

(define fgl-rule-tracespec ((rule fgl-generic-rule-p)
                                           interp-st state)
  (declare (ignorable state))
  :returns (tracespec true-listp :rule-classes :type-prescription)
  (assoc-equal (fgl-generic-rule->rune rule)
               (interp-st->trace-alist interp-st)))

;; (encapsulate
;;   (((fgl-rewrite-trace-cond * * * * * interp-st state) => (mv * interp-st state)
;;     :formals (rule tracespec fn args bindings interp-st state)
;;     :guard (and (fgl-generic-rule-p rule)
;;                 (true-listp tracespec)
;;                 (pseudo-fnsym-p fn)
;;                 (fgl-objectlist-p args)
;;                 (fgl-object-bindings-p bindings)
;;                 (interp-st-bfrs-ok interp-st))))

  
  
;;   (set-ignore-ok t)
;;   (set-irrelevant-formals-ok t)

;;   (define fgl-rewrite-trace-cond ((rule fgl-generic-rule-p)
;;                                   (tracespec true-listp)
;;                                   (fn pseudo-fnsym-p)
;;                                   (args fgl-objectlist-p)
;;                                   (bindings fgl-object-bindings-p)
;;                                   (interp-st interp-st-bfrs-ok)
;;                                   state)
;;     :returns (mv cond new-interp-st new-state)
;;     :local-def t :progn t :hooks nil
;;     (mv nil interp-st state)
;;     ///
;;     (make-event `(progn . ,*fancy-ev-primitive-thms*))
;;     (fty::deffixequiv fgl-rewrite-trace-cond :skip-cong-thm t)))

;; (fty::deffixequiv fgl-rewrite-trace-cond)

(local (defthm symbol-alistp-when-fgl-object-bindings-p
         (implies (fgl-object-bindings-p x)
                  (symbol-alistp x))))

(defconst *fancy-ev-primitive-thms-no-state*
  (remove-equal '(defret w-state-of-<fn>
                   (equal (w new-state)
                          (w state)))
                *fancy-ev-primitive-thms*))

(define interp-st-push-trace-alist ((trace-alist trace-alist-p) interp-st)
  :returns new-interp-st
  (update-interp-st->trace-stack (cons (trace-alist-fix trace-alist)
                                       (interp-st->trace-stack interp-st))
                                 interp-st)
  ///
  (make-event `(progn . ,*fancy-ev-primitive-thms-no-state*)))

(define interp-st-maybe-push-trace-alist (restore-cond trace-cond (trace-alist trace-alist-p) interp-st)
  :returns new-interp-st
  (if (and restore-cond trace-cond)
      (update-interp-st->trace-stack (cons (trace-alist-fix trace-alist)
                                           (interp-st->trace-stack interp-st))
                                     interp-st)
    interp-st)
  ///
  (make-event `(progn . ,*fancy-ev-primitive-thms-no-state*)))


(define interp-st-maybe-pop-trace-alist (pushed-cond restore-cond interp-st)
  :returns new-interp-st
  (if pushed-cond
      (b* ((stack (interp-st->trace-stack interp-st))
           (interp-st (update-interp-st->trace-stack (cdr stack) interp-st)))
        (if restore-cond
            (update-interp-st->trace-alist (car stack) interp-st)
          interp-st))
    interp-st)
  ///
  (make-event `(progn . ,*fancy-ev-primitive-thms-no-state*)))

(local (defthm true-listp-of-member-equal
         (implies (true-listp x)
                  (true-listp (member-equal k x)))
         :rule-classes :type-prescription))

(defconst *traceeval-common-inputs*
  '((rule fgl-generic-rule-p)
    (fn pseudo-fnsym-p)
    (bindings fgl-object-bindings-p)
    (tracep)
    (interp-st interp-st-bfrs-ok)
    (state)))

(defconst *traceeval-common-bindings*
  '`((depth . ,(lnfix depth))
     (rune . ,(fgl-generic-rune-fix rune))
     (fn . ,(pseudo-fnsym-fix fn))
     (args . ,(fgl-objectlist-fix args))
     (bindings . ,(fgl-object-bindings-fix bindings))
     . ,(fgl-object-bindings-fix bindings)))


(defun def-trace-eval-body (key default ev-bindings description)
  `(b* ((keyvals (cdr tracespec))
        (expr-look (member ,key keyvals))
        ((unless expr-look)
         (mv ,default interp-st state))
        (expr (cadr expr-look))
        ((unless (pseudo-termp expr))
         (raise "Error: ~s0 ~x1 for rule ~x2 is not a pseudo-term" ,description expr rune)
         (mv nil interp-st state))
        (bindings (list* ,@ev-bindings
                         ,*traceeval-common-bindings*))
        (bindings (cons (cons 'trace-meta-bindings bindings) bindings))
        ((mv err val interp-st state) (fancy-ev expr bindings
                                                10000 interp-st state t t))
        ((when err)
         (raise "Error evaluating ~s0 ~x1 for rule ~x2: ~@3" ,description expr rune err)
         (mv nil interp-st state)))
     (mv val interp-st state)))

;; (defmacro def-trace-eval (name
;;                           formals
;;                           &key key
;;                           ev-bindings
;;                           default
;;                           description
;;                           push)
;;   (b* ((body (def-trace-eval-body key default ev-bindings description))
;;        (body (cond (push
;;                     `(b* ((trace-alist (interp-st->trace-alist interp-st))
;;                           ((mv val interp-st state)
;;                            ,body)
;;                           (interp-st (interp-st-maybe-push-trace-alist
;;                                       (cadr (member :restore-rules (llist-fix tracespec)))
;;                                       val trace-alist interp-st)))
;;                        (mv val interp-st state)))
;;                    (t body))))
                    
;;     `(define ,name (,@formals
;;                     . ,*traceeval-common-inputs*)
;;        :returns (mv val new-interp-st new-state)
;;        ,body
;;        ///
;;        (make-event `(progn . ,*fancy-ev-primitive-thms*)))))


(local (in-theory (disable pseudo-termp pseudo-term-listp
                           acl2::pseudo-termp-opener
                           member-equal
                           acl2::pseudo-termp-car-when-pseudo-term-listp
                           cmr::pseudo-term-list-p-when-pseudo-var-list-p)))

(local (defthm true-listp-car-of-interp-st->tracespecs
         (true-listp (car (interp-st->tracespecs interp-st)))
         :rule-classes :type-prescription))

;; (def-trace-eval fgl-rewrite-trace-cond ()
;;   :key :cond
;;   :default t
;;   :description "trace condition"
;;   :push t)

(define interp-st-rewrite-args (interp-st)
  :returns (args fgl-objectlist-p)
  (and (< 0 (interp-st-scratch-len interp-st))
       (let ((scratch (interp-st-top-scratch interp-st)))
         (scratchobj-case scratch :fgl-objlist scratch.val :otherwise nil))))

(local (acl2::use-trivial-ancestors-check))

(make-event
 `(define fgl-trace-cond ,(remove-equal '(tracep) *traceeval-common-inputs*)
    :returns (mv tracep new-interp-st new-state)
    (b* (((unless (interp-flags->trace-rewrites (interp-st->flags interp-st)))
          (mv nil interp-st state))
         (tracespec (fgl-rule-tracespec rule interp-st state))
         ((unless tracespec) (mv nil interp-st state))
         (trace-alist (interp-st->trace-alist interp-st))
         (depth (+ 1 (interp-st->trace-depth interp-st)))
         (rune (fgl-generic-rule->rune rule))
         (args (interp-st-rewrite-args interp-st))
         (interp-st (update-interp-st->tracespecs
                     (cons tracespec (interp-st->tracespecs interp-st))
                     interp-st))
         ((mv val interp-st state)
          ,(def-trace-eval-body :cond t nil "trace condition"))
         (tracespecs (interp-st->tracespecs interp-st))
         (tracespec (car tracespecs))
         ((unless (and val tracespec))
          (b* ((interp-st (update-interp-st->tracespecs (cdr tracespecs) interp-st)))
            (mv nil interp-st state)))
         (interp-st (update-interp-st->trace-depth depth interp-st))
         ((unless (cadr (member :restore-rules (llist-fix tracespec))))
          (mv t interp-st state))
         (interp-st (interp-st-push-trace-alist trace-alist interp-st)))
      (mv :restore interp-st state))
    ///
    (make-event `(progn . ,*fancy-ev-primitive-thms*))))



(define my-get-global ((name symbolp) state)
  :hooks nil
  (and (boundp-global name state)
       (f-get-global name state)))

(defmacro def-trace-output (name
                            formals
                            &key key
                            ev-bindings
                            description
                            default
                            direction)
  `(define ,name (,@formals
                  . ,*traceeval-common-inputs*)
     :returns (mv new-interp-st new-state)
     (b* (((unless tracep) (mv interp-st state))
          (tracespec (car (interp-st->tracespecs interp-st)))
          (depth (interp-st->trace-depth interp-st))
          ((mv interp-st state)
           (b* (((unless tracespec)
                 (mv interp-st state))
                (rune (fgl-generic-rule->rune rule))
                ((unless (equal (car tracespec) rune))
                 (raise "Unexpected tracespec ~x0 for rule ~x1~%" tracespec rune)
                 (mv interp-st state))
                (args (interp-st-rewrite-args interp-st))
                ((mv val interp-st state)
                 ,(def-trace-eval-body key :default ev-bindings description)))
             (and ,@(if default '(val) '(val (not (eq val :default))))
                  (b* ((evisc-tuple (my-get-global :fgl-trace-evisc-tuple state)))
                    (fmt-to-comment-window
                     ,(case direction
                        (:entry "~t0~x1> ~@2~%")
                        (:exit  "~t0<~x1 ~@2~%")
                        (otherwise "~t0<~x1> ~@2~%"))
                     (pairlis2 acl2::*base-10-chars* (list depth depth
                                                           ,(if default
                                                                `(if (eq val :default)
                                                                     ,default
                                                                   val)
                                                              'val)))
                     0 evisc-tuple nil)))
             (mv interp-st state)))
          ;; Need to pop the the stacks if we started tracing even if the tracespec was cancelled (or changed to delete the restore)
          ,@(and (eq direction :exit)
                 `((tracespec (car (interp-st->tracespecs interp-st)))
                   (interp-st (update-interp-st->tracespecs
                               (cdr (interp-st->tracespecs interp-st)) interp-st))
                   (interp-st (interp-st-maybe-pop-trace-alist
                               (eq tracep :restore)
                               (cadr (member :restore-rules tracespec))
                               interp-st))
                   (interp-st (update-interp-st->trace-depth
                               (nfix (1- depth))
                               interp-st)))))
       (mv interp-st state))
     ///
     (make-event `(progn . ,*fancy-ev-primitive-thms*))))


;; Rewrite rules: four trace events -- entry, relieve hyp, success, or failure
(def-trace-output fgl-trace-entry-output ()
  :key :on-entry
  :description "trace entry term"
  :default (msg "~x0 ~x1~%" rune bindings)
  :direction :entry)


(make-event
 `(define fgl-trace-start ,(remove-equal '(tracep) *traceeval-common-inputs*)
    :returns (mv tracep new-interp-st new-state)
    (b* (((mv tracep interp-st state)
          (fgl-trace-cond . ,(strip-cars (remove-equal '(tracep) *traceeval-common-inputs*))))
         ((mv interp-st state)
          (fgl-trace-entry-output . ,(strip-cars *traceeval-common-inputs*))))
      (mv tracep interp-st state))
    ///
    (make-event `(progn . ,*fancy-ev-primitive-thms*))))
      



(def-trace-output fgl-trace-relieve-hyp-output ((hyp natp))
  :key :on-relieve-hyp
  :ev-bindings (`(hyp . ,(lnfix hyp)))
  :description "trace relieve-hyp term")


(def-trace-output fgl-trace-success-output ((result fgl-object-p))
  :key :on-success
  :ev-bindings (`(result . ,(fgl-object-fix result)))
  :description "trace success term"
  :default (msg "~x0 success: ~x1~%" rune result)
  :direction :exit)

(def-trace-output fgl-trace-failure-output ((failed-hyp acl2::maybe-natp))
  :key :on-failure
  :ev-bindings (`(errmsg . ,(interp-st->errmsg interp-st))
                `(hyp . ,(acl2::maybe-natp-fix failed-hyp)))
  :description "trace success term"
  :default (msg "~x0 failed: (~@1)~%"
                rune
                (let ((errmsg (interp-st->errmsg interp-st)))
                  (cond ((msgp errmsg) errmsg)
                        (errmsg (msg "~x0" errmsg))
                        (failed-hyp (msg "hyp ~x0 failed" failed-hyp))
                        (t "aborted"))))
  :direction :exit)

(make-event
 `(define fgl-trace-finish-rewrite ((result fgl-object-p)
                                    . ,*traceeval-common-inputs*)
    :returns (mv new-interp-st new-state)
    (if (not (interp-st->errmsg interp-st))
        (fgl-trace-success-output result rule fn bindings tracep interp-st state)
      (fgl-trace-failure-output nil rule fn bindings tracep interp-st state))
    ///
    (make-event `(progn . ,*fancy-ev-primitive-thms*))))


;; Meta rules: five trace events -- entry (shared with rewriting), eval
;; success, eval failure, (RHS rewriting) success, (RHS rewriting) failure.
(def-trace-output fgl-trace-meta-eval-success-output ((rhs pseudo-termp))
  :key :on-eval-success
  :ev-bindings (`(rhs . ,(pseudo-term-fix rhs)))
  :description "trace eval-success term")



(def-trace-output fgl-trace-meta-eval-failure-output ()
  :key :on-eval-failure
  :ev-bindings (`(errmsg . ,(interp-st->errmsg interp-st)))
  :description "trace eval-failure term"
  :default (msg "~x0 evaluation failed~@1~%"
                rune
                (let ((errmsg (interp-st->errmsg interp-st)))
                  (cond ((msgp errmsg) (msg " with error ~@0" errmsg))
                        (errmsg (msg " with error ~x0" errmsg))
                        (t ""))))
  :direction :exit)

(def-trace-output fgl-trace-meta-success-output ((result fgl-object-p)
                                                 (rhs pseudo-termp))
  :key :on-success
  :ev-bindings (`(result . ,(fgl-object-fix result))
                `(rhs . ,(pseudo-term-fix rhs)))
  :description "trace success term"
  :default (msg "~x0 success: ~x1~%" rune result)
  :direction :exit)

(def-trace-output fgl-trace-meta-failure-output ((rhs pseudo-termp))
  :key :on-failure
  :ev-bindings (`(rhs . ,(pseudo-term-fix rhs))
                `(errmsg . ,(interp-st->errmsg interp-st)))
  :description "trace failure term"
  :default (msg "~x0 failed: (~@1)~%"
                rune
                (let ((errmsg (interp-st->errmsg interp-st)))
                  (cond ((msgp errmsg) errmsg)
                        (errmsg (msg "~x0" errmsg))
                        (t "aborted"))))
  :direction :exit)


(make-event
 `(define fgl-trace-finish-meta ((successp)
                                 (result fgl-object-p)
                                 (rhs pseudo-termp)
                                 . ,*traceeval-common-inputs*)
    :returns (mv new-interp-st new-state)
    (if (and successp (not (interp-st->errmsg interp-st)))
        (fgl-trace-meta-success-output result rhs rule fn bindings tracep interp-st state)
      (fgl-trace-meta-failure-output rhs rule fn bindings tracep interp-st state))
    ///
    (make-event `(progn . ,*fancy-ev-primitive-thms*))))
 

(defxdoc fgl-rewrite-tracing
  :parents (fgl)
  :short "How to trace the FGL rewriter"
  :long "

<p>FGL allows attempts at applying rewrite rules to be traced using a
configurable tracing function.  By default, a basic tracing function is
provided such that the user only needs to set up some state global variables to
enable and use it.</p>

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

<h3>Advanced Tracing</h3>

<p>More specific tracing behavior can be specified for each rule via the
trace-rule-alist. The @(see fgl-trace) macro offers a more user-friendly
interface for this than direct manipulation of the trace-rule-alist; see that
topic for options, as well as @(see fgl-advanced-tracing).</p>

")


(define set-fgl-trace-rule-alist (new-alist state)
  (f-put-global ':fgl-trace-rule-alist new-alist state))



(define fgl-trace-translate-keyvals (rune keyvals state)
  :mode :program
  (if (or (atom keyvals)
          (atom (cdr keyvals)))
      (value nil)
    (er-let* ((trans-val (acl2::translate (cadr keyvals) t nil nil `(fgl-trace ,rune) (w state) state))
              (rest (fgl-trace-translate-keyvals rune (cddr keyvals) state)))
      (value (cons (car keyvals) (cons trans-val rest))))))

(define fgl-trace-fn (rune
                      keyvals
                      restore-rules
                      state)
  :mode :program
  (b* (((unless (fgl-generic-rune-p rune))
        (er soft 'fgl-trace "Rune must satisfy ~x0" 'fgl-generic-rune-p))
       ((er trans-keyvals) (fgl-trace-translate-keyvals rune keyvals state))
       (entry (cons rune
                    (append trans-keyvals
                            (and restore-rules `(:restore-rules ,restore-rules)))))
       (old-alist (my-get-global :fgl-trace-rule-alist state))
       (state (f-put-global ':fgl-trace-rule-alist
                            (cons entry old-alist) state)))
    (value entry)))
       


(defmacro fgl-trace (rune
                     &key
                     (cond 'nil cond-p)
                     (on-entry 'nil on-entry-p)
                     (on-relieve-hyp 'nil on-relieve-hyp-p)
                     (on-eval-success 'nil on-eval-success-p)
                     (on-eval-failure 'nil on-eval-failure-p)
                     (on-success 'nil on-success-p)
                     (on-failure 'nil on-failure-p)
                     (restore-rules 'nil))
  `(fgl-trace-fn ',rune
                 (list . ,(append (and cond-p `(:cond ',cond))
                                  (and on-entry-p `(:on-entry ',on-entry))
                                  (and on-relieve-hyp-p `(:on-relieve-hyp ',on-relieve-hyp))
                                  (and on-eval-success-p `(:on-eval-success ',on-eval-success))
                                  (and on-eval-failure-p `(:on-eval-failure ',on-eval-failure))
                                  (and on-success-p `(:on-success ',on-success))
                                  (and on-failure-p `(:on-failure ',on-failure))))
                 ,restore-rules
                 state))
        


(defxdoc fgl-trace
  :parents (fgl-rewrite-tracing)
  :short "Trace an FGL rule."
  :long "<p>The @('fgl-trace') macro traces a specified rule (given by its FGL rune) and
allows specifying the condition under which an application of the rule will be
traced and what output will be printed.</p>

<p>Example:</p>
@({
 (fgl-trace (:formula logext-to-logapp)
   :cond (fgl-object-case n :g-integer)
   :on-entry (list 'logext-to-logapp n x)
   :on-success (msg \"~x0 success: n=~x1 x=~x2 result=~x3\" 'logext-to-logapp n x result)
   :on-failure (msg \"~x0 failure: hyp ~x1 errmsg ~x2\" 'logext-to-logapp failed-hyp errmsg)
   :restore-rules t
   :location state)
 })

<p>See @(see fgl-untrace) and @(see fgl-untrace-all) to remove traces from rules.</p>

<p>Note that the @('trace-rewrites') flag of the @(see fgl-config) object must
be set to T for tracing to work at all. This can be set in either of the
following ways:</p>
@({
 ;; Table setting overrides default
 (table fgl::fgl-config-table :trace-rewrites t)

 ;; State global overrides table setting
 (assign :fgl-trace-rewrites t)
 })

<h3>Arguments</h3>

<p>The first argument is a rune satisfying @('fgl-generic-rune-p'). The rest of
the arguments are optional keyword/value pairs among the following:</p>

<ul>

<li>@(':cond cond-expr'): If provided, limits the tracing of the rule to
applications where @('cond-expr') evaluates to true.  The expression may use the standard
trace variables (see below).</li>

<li>@(':entry entry-expr'): If provided, @('entry-expr') is evaluated when
starting an attempt to apply the rule. The expression may use the standard
trace variables. The resulting object should either be @('nil'), in which case
nothing is printed, @(':default'), in which case the default entry message is
printed (same as if the keyword was not provided), or a @(see acl2::msg)
object, in which case it is printed with the @('~@') formatting directive.</li>

<li>@(':on-relieve-hyp relieve-expr'): If provided, after each successful
relieving of a hypothesis (for a rewrite rule) or after successfully evaluating
the metafunction (for a meta rule), @('relieve-expr') is evaluated and may
cause some output to be printed. (By default no output is printed in this case,
unlike for entry, success, and failure.) The expression may use the standard
trace variables as well as @('hyp') (see below). The resulting object should either
be @('nil')/@(':default'), in which cases nothing is printed, or a @(see
acl2::msg) object, in which case it is printed with the @('~@') formatting
directive.</li>

<li>@(':on-success success-expr'): If provided, @('success-expr') is evaluated
when the rule has been applied successfully. The expression may use the
standard trace variables as well as @('result') and additionally @('rhs') if
the rule is a meta rule (see below).  The resulting object should either be
@('nil'), in which case nothing is printed, @(':default'), in which case the
default success message is printed (same as if the keyword was not provided),
or a @(see acl2::msg) object, in which case it is printed with the @('~@')
formatting directive.</li>

<li>@(':on-failure failure-expr'): If provided, @('failure-expr') is evaluated
when the application of the rule has failed. For a rewrite rule, this may be
either because of an unrelieved hypothesis or an error or abort. For a meta
rule, this is due to an error or abort in rewriting the RHS; a failure in
applying the metafunction instead results in the eval-failure
condition (below).  The expression may use the standard trace variables as well
as @('errmsg') and @('hyp') and additionally @('rhs') if the rule is a meta
rule (see below).  The resulting object should either be @('nil'), in which
case nothing is printed, @(':default'), in which case the default failure
message is printed (same as if the keyword was not provided), or a @(see
acl2::msg) object, in which case it is printed with the @('~@') formatting
directive.</li>

<li>@(':on-eval-success success-expr'): If provided, and if the rule is a meta
rule, @('success-expr') is evaluated when the metafunction has been
successfully executed, before the resulting RHS term is rewritten.  The
expression may use the standard trace variables as well as @('rhs') (see
below).  The resulting object should either be @('nil')/@(':default'), in which
case nothing is printed, or a @(see acl2::msg) object, in which case it is
printed with the @('~@') formatting directive.</li>

<li>@(':on-eval-failure failure-expr'): If provided, and if the rule is a meta
rule, @('failure-expr') is evaluated when the metafunction has been
unsuccessfully executed.  The expression may use the standard trace variables
as well as @('errmsg') (see below).  The resulting object should either be
@('nil')/@(':default'), in which case nothing is printed, or a @(see acl2::msg)
object, in which case it is printed with the @('~@') formatting directive.</li>

<li>@(':restore-rules restorep'): If provided and @('restorep') is nonnil,
whenever an application of the rule is traced the current trace rules are
backed up at the start and restored at the end of tracing (albeit before
evaluating the success or failure expressions). This is useful if you want a
trace of one rule to cause tracing of another rule; see @(see
fgl-advanced-tracing).</li>

</ul>

<h3>Variables usable in tracing expressions</h3>

<p>The following variables can be used in all trace expressions; note these
symbols are in the FGL package. Additionally, the variables bound in
@('bindings') may be used directly if they aren't shadowed by one of these
symbols.</p>

<ul>

<li>@('depth'): the number of traced rule applications currently in process;
this counts the current rule application, even if it ends up not being
traced (i.e. its cond expression evaluates to nil).</li>

<li>@('rune'): the name of the traced rule.</li>

<li>@('fn'), @('args'): the function and arguments (FGL objects) of the
object being rewritten.</li>

<li>@('bindings'): The substitution under which the rule is being applied. At
any point in applying a rewrite rule, this is the unifying substitution plus
any free variable bindings that have been added. When applying a meta or
primitive rule, the bindings are initially empty. For a meta rule, after
evaluating the metafunction, it is populated with the bindings returned by the
metafunction (for a primitive, it remains empty).</li>
</ul>

<p>The following variables can be used in some situtations:</p>

<ul>

<li>@('result'): The final result of the rule application, i.e. the rewritten
RHS, available in the @(':on-success') case.</li>


<li>@('hyp'): The index of the relevant hypothesis--in the @(':on-relieve-hyp')
case, this is the index of the latest hypothesis relieved, and in the
@(':on-failure') case this is the index of the failed hypothesis, if any,
otherwise NIL.</li>

<li>@('errmsg'): The error message ending application of the rule, or NIL if
none, available in @(':on-failure') and @(':on-eval-failure') cases.</li>

<li>@('rhs'): the computed RHS term returned by a metafunction, available in
the @(':on-eval-success') and metafunctions' @(':on-success') and
@(':on-failure') cases.</li>


<h3>Tracing rules during FGL processing</h3>

<p>The @('fgl-trace') macro installs an updated set of traced rules in the
@(':fgl-trace-rule-alist') state global variable. When starting a symbolic
execution, the value of that state global is copied into the FGL interpreter
state's @('trace-alist') field.  Therefore, running @('fgl-trace') during
symbolic simulation (e.g. during evaluation of a trace expression) won't affect
the rules traced during the current symbolic execution. Instead, you can use
@(see fgl-trace*) (with much the same interface) to add a traced rule, @(see
fgl-untrace*) to untrace a rule, and @(see fgl-untrace-all*) to untrace all
rules. Note that if a traced rule has the @(':restore-rules') flag set, then
any modifications to the traced rules will be undone (set back to the state
upon beginning application of the rule) after the rule is finished.</p>
")


(define fgl-untrace-fn (rune state)
  (b* (((unless (fgl-generic-rune-p rune))
        (mv (msg "Rune must satisfy ~x0" 'fgl-generic-rune-p) nil state))
       (old-alist (my-get-global :fgl-trace-rule-alist state))
       (state (f-put-global ':fgl-trace-rule-alist
                            (acl2::hons-remove-assoc rune old-alist)
                            state)))
    (value rune)))

(defmacro fgl-untrace (rune)
  `(fgl-untrace-fn ',rune state))

(defxdoc fgl-untrace
  :parents (fgl-rewrite-tracing)
  :short "Untrace an FGL rule"
  :long "<p>Removes the trace entry, if any, for the given FGL rune. Usage:</p>
@({
 (fgl-untrace (:formula my-rule))
 })

<p>See @(see fgl-trace) for details about tracing rules.</p>
")

(define fgl-untrace-all (&key (state 'state))
  (b* ((old-alist (my-get-global :fgl-trace-rule-alist state))
       (state (f-put-global ':fgl-trace-rule-alist nil state)))
    (value (alist-keys old-alist))))

(defxdoc fgl-untrace-all
  :parents (fgl-rewrite-tracing)
  :short "Remove all trace settings for FGL rules"
  :long "<p>See @(see fgl-trace) for details about tracing rules.</p>")
  

