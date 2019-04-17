; GLMC -- Hardware model checking interface
; Copyright (C) 2017 Centaur Technology
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


(in-package "GL")

(include-book "glmc-generic-defs")
(include-book "centaur/aig/g-aig-eval" :dir :system)
(include-book "centaur/gl/gl" :dir :system)
(local (include-book "glmc-generic-proof"))

; Matt K. mod: Avoid ACL2(p) error from
; test-glmc-glcp-geval-apply-agrees-with-test-glmc-glcp-geval-ev
; (clause-processor returns more than two values).
(set-waterfall-parallelism nil)

(encapsulate nil
  (local (include-book "arithmetic/top-with-meta" :dir :system))
  ;; Rules needed for interpreting the results of shape-spec-invert
  (gl::def-gl-rewrite realpart-when-integerp
    (implies (integerp x)
             (equal (realpart x) x)))

  (gl::def-gl-rewrite numerator-when-integerp
    (implies (integerp x)
             (equal (numerator x) x))
    :hints (("goal" :use ((:instance rational-implies2 (x x)))
             :in-theory (disable rational-implies2)))))



;; Side goals clause processor
(define glmc-side-goals ((clause pseudo-term-listp)
                         config
                         state)
  :returns (mv er
               new-clauses
               new-state)
  (b* (((unless (glmc-config-p config))
        (mv "Bad GLMC config" nil state))
       ((glmc-config+ config))
       ((unless (acl2::interp-defs-alistp config.overrides))
        (mv "Bad overrides in GLMC config" nil state))
       (er (glmc-clause-syntax-checks config))
       ((when er)
        (mv er nil state))
       ((unless (bfr-mode))
        (mv "Glmc only works in AIG mode" nil state))
       ;; ((mv (glmc-fsm fsm) er bvar-db state)
       ;;  (glmc-mcheck-to-fsm config bvar-db state))
       ;; ((when er)
       ;;  (mv er nil bvar-db state))

       ;; ((mv er state) (glmc-check-st-hyp-inductive config fsm bvar-db state))
       ;; ((when er)
       ;;  (mv er nil bvar-db state))

       ;; ((mv er state) (glmc-fsm-perform-mcheck config fsm bvar-db state))
       ;; ((when er)
       ;;  (mv er nil bvar-db state))

       (clause-clauses (glmc-clause-check clause config))
       (cov-clause (glmc-cov-clause config)))
    (mv nil
        (cons cov-clause
              (append clause-clauses
                      (list '((not (gl-cp-hint 'side-goals-fake-goal))))))
        state))
  ///
  (Defthm glmc-side-goals-correct
    (implies (and (pseudo-term-listp clause)
                  (alistp a)
                  (glcp-generic-geval-ev-meta-extract-global-facts :state state)
                  (glcp-generic-geval-ev-theoremp
                   (conjoin-clauses
                    (acl2::clauses-result
                     (glmc-side-goals clause config state)))))
             (glcp-generic-geval-ev (disjoin clause) a))
    :rule-classes :clause-processor))


(local (defun glmc-generic-verify-guards-events (glmc-fnnames)
         (if (atom glmc-fnnames)
             nil
           (cons `(verify-guards ,(cdr (assoc (car glmc-fnnames)
                                              *glmc-generic-name-subst*)))
                 (glmc-generic-verify-guards-events (cdr glmc-fnnames))))))

(set-enforce-redundancy t)

(verify-guards glcp-generic-interp-test)
;; Redundant verification of guards and the top-level correctness theorem
(make-event (cons 'progn (glmc-generic-verify-guards-events *glmc-fnnames*)))

(defthm glmc-generic-correct
  (implies (and (pseudo-term-listp clause)
                (alistp a)
                (glcp-generic-geval-ev-meta-extract-global-facts :state state)
                (glcp-generic-geval-ev-theoremp
                 (conjoin-clauses
                  (acl2::clauses-result
                   (glmc-generic clause config interp-st state)))))
           (glcp-generic-geval-ev (disjoin clause) a))
  :rule-classes nil)

(set-enforce-redundancy nil)



(defun glmc-verify-guards-events (glmc-fnnames subst functional-subst)
  (if (atom glmc-fnnames)
      nil
    (cons (b* ((fnname (cdr (assoc (car glmc-fnnames) subst)))
               (generic-fnname (cdr (assoc (car glmc-fnnames)
                                           *glmc-generic-name-subst*))))
            `(verify-guards ,fnname
               :hints ('(:by (:functional-instance
                              (:guard-theorem ,generic-fnname nil)
                              . ,functional-subst))
                       (and stable-under-simplificationp
                            (b* ((lit (car (last clause)))
                                 ((mv fn args)
                                  (case-match lit
                                    (('equal ('mv-nth & (fn . args)) &)
                                     (mv fn args))
                                    (('equal (fn . args) &)
                                     (mv fn args))
                                    (& (mv nil nil)))))
                              (and fn
                                   (rassoc fn ',subst)
                                   `(:expand ((,fn . ,args)))))))))
          (glmc-verify-guards-events (cdr glmc-fnnames) subst functional-subst))))

(defun def-glmc-clause-processor-fn (name)
  (b* ((subst (glmc-name-subst name))
       (glcp (cdr (assoc 'clause-proc subst)))
       (correct (intern-in-package-of-symbol
                 (concatenate 'string (symbol-name name) "-CORRECT")
                 name))
       (functional-subst
        (pairlis$ (strip-cdrs *glmc-generic-name-subst*)
                  (pairlis$ (strip-cdrs subst) nil)))
       (fn-defs (sublis subst *glmc-full-template*))
       (guards (glmc-verify-guards-events *glmc-fnnames* subst functional-subst)))
    `(with-output :off (event prove)
       (progn (def-gl-clause-processor ,glcp)
              (defsection ,name
                (set-verify-guards-eagerness 0)
                ,fn-defs
                (local (in-theory nil))
                ,@guards
                (acl2::def-functional-instance
                  ,correct
                  glmc-generic-correct
                  ,functional-subst
                  :hints ((and stable-under-simplificationp
                               (b* ((lit (car (last clause)))
                                    ((mv fn args)
                                     (case-match lit
                                       (('equal ('mv-nth & (fn . args)) &)
                                        (mv fn args))
                                       (('equal (fn . args) &)
                                        (mv fn args))
                                       (& (mv nil nil)))))
                                 (and fn
                                      (rassoc fn ',subst)
                                      `(:expand ((,fn . ,args)))))))
                  :rule-classes :clause-processor))
              (table glmc-info 'latest-glmc-clause-proc ',name)))))

(defmacro def-glmc-clause-processor (name)
  (def-glmc-clause-processor-fn name))



(def-glmc-clause-processor test-glmc)


(defconst *glmc-hint-table*
  ;; (hint-kwd-name type default . config-names
  ;; When type is nil, the rest are irrelevant because it's not something that goes in a config.
  ;; Config names may be
  ;;   1) a list of keywords, in which case they go in the glmc-config
  ;;   2) a list containing a single list of keywords, in which case they go in the glcp-config.
  '((:side-goals nil)
    (:clause-check-hints nil)
    (:state-hyp-inductive-hints nil)
    (:run-check-hints nil)
    (:measure-hints nil)
    (:do-not-expand nil)
    (:cov-theory-add nil)
    (:cov-hints nil)
    (:cov-hints-position nil)
    (:shape-spec-bindings shape-spec-bindings nil (:shape-spec-alist))
    (:state-var variable acl2::st :st-var)
    (:initstatep term t :initstp)
    (:nextstate term nil :nextst)
    (:frame-input-bindings bindings ((acl2::in (car acl2::ins))) :frame-in-vars :frame-ins)
    (:rest-of-input-bindings bindings ((acl2::ins (cdr acl2::ins))) :in-vars :rest-ins)
    (:body-bindings b*-bindings nil :bindings)
    (:end-of-inputsp term (atom acl2::ins) :end-ins)
    (:measure term (acl2-count acl2::ins) :in-measure)
    (:run term nil :run)
    (:state-hyp term t :st-hyp)
    (:input-hyp term t :in-hyp)
    (:prop term nil :prop)
    (:state-hyp-method st-hyp-method :mcheck :st-hyp-method)
    (:constraint term t :constr)
    (:check-vacuity boolean t (:check-vacuous))
    (:prof-enabledp boolean nil (:prof-enabledp))
    (:ctrex-transform function (lambda (x) x) (:ctrex-transform))
    (:main-rewrite-rules rule-table :default :main-rewrite-rules)
    (:main-branch-merge-rules rule-list :default :main-branch-merge-rules)
    (:extract-rewrite-rules rule-table :default :extract-rewrite-rules)
    (:extract-branch-merge-rules rule-list :default :extract-branch-merge-rules)))

(defun glmc-hint-translate-bindings (bindings ctx state)
  (declare (xargs :stobjs state :mode :program))
  (B* (((when (atom bindings)) (mv nil nil nil state))
       (binding (car bindings))
       ((unless (and (true-listp binding)
                     (eql (len binding) 2)
                     (variablep (car binding))))
        (mv (msg "~x0: Malformed binding ~x1" ctx binding) nil nil state))
       ((mv err trans-term state)
        (acl2::translate (cadr binding) t t nil ctx (w state) state))
       ((when err)
        (mv err nil nil state))
       ((mv err vars terms state)
        (glmc-hint-translate-bindings (cdr bindings) ctx state)))
    (mv err
        (cons (car binding) vars)
        (cons trans-term terms)
        state)))

(defun glmc-process-hint-kwds (tab kwd-alist state)
  (declare (xargs :stobjs state :mode :program))
  (b* (((when (atom tab)) (mv nil nil nil state))
       ((list* user-kwd type default glmc-kwds) (car tab))
       (user-val (std::getarg user-kwd default kwd-alist))
       ((mv glcp-p config-kwds)
        (if (consp (car glmc-kwds))
            (mv t (car glmc-kwds))
          (mv nil glmc-kwds)))
       ((mv err new-kwds state)
        (case type
          (shape-spec-bindings
           (mv nil `(,(car config-kwds) ,user-val) state))

          (variable
           (if (variablep user-val)
               (mv nil `(,(car config-kwds) ',user-val) state)
             (mv (msg "~x0 should be a variable name, but was ~x1" user-kwd user-val) nil state)))

          (term
           (b* (((mv err trans-val state)
                 (acl2::translate user-val t t nil `(glmc-hint ,user-kwd) (w state) state))
                ((when err)
                 (mv err nil state)))
             (mv nil `(,(car config-kwds) ',trans-val) state)))

          (bindings
           (b* (((mv err vars trans-terms state)
                 (glmc-hint-translate-bindings user-val `(glmc-hint ,user-kwd) state))
                ((when err)
                 (mv err nil state)))
             (mv nil `(,(car config-kwds) ',vars ,(cadr config-kwds) ',trans-terms) state)))

          (b*-bindings
           (b* (((mv err bindings)
                 (acl2::b*-binders-to-bindinglist user-val (w state)))
                ((when err)
                 (mv err nil state)))
             (mv nil `(,(car config-kwds) ',bindings) state)))

          (boolean
           (if (booleanp user-val)
               (mv nil `(,(car config-kwds) ,user-val) state)
             (mv (msg "~x0 should be a Boolean, but was ~x1" user-kwd user-val) nil state)))

          (st-hyp-method
           (if (st-hyp-method-p user-val)
               (mv nil `(,(car config-kwds) ,user-val) state)
             (mv (msg "~x0 should be one of ~v1, but was ~x2"
                      user-kwd '(:inductive-clause :inductive-sat :mcheck)
                      user-val)
                 nil state)))

          (function
           (if (or (symbolp user-val)
                   (and (consp user-val) (eq (car user-val) 'lambda)))
               (mv nil `(,(car config-kwds) ',user-val) state)
             (mv (msg "~x0 should be a function symbol or lambda form, but was ~x1"
                      user-kwd user-val)
                 nil state)))

          (rule-table
           (mv nil `(,(car config-kwds) ,user-val) state))

          (rule-list
           (mv nil `(,(car config-kwds) ,user-val) state))

          ((nil) ;;ignore
           (mv nil nil state))

          (otherwise
           (mv (msg "Bad entry in glmc-hint-table? ~x0~%" (car tab)) nil state))))

       ((when err)
        (mv err nil nil state))

       ((mv err glmc-rest glcp-rest state)
        (glmc-process-hint-kwds (cdr tab) kwd-alist state))

       ((mv glmc-kwds glcp-kwds)
        (if glcp-p
            (mv glmc-rest (append new-kwds glcp-rest))
          (mv (append new-kwds glmc-rest) glcp-rest))))
    (mv err glmc-kwds glcp-kwds state)))


(define identity-cp (x)
  (declare (xargs :guard t))
  (list x)
  ///
  (defthm identity-cp-correct
    (implies (and (pseudo-term-listp clause)
                  (alistp a)
                  (cl-ev (conjoin-clauses (identity-cp clause)) a))
             (cl-ev (disjoin clause) a))
    :rule-classes :clause-processor))



(defun glmc-hint-fn (args state)
  (declare (xargs :mode :program :stobjs state))
  (b* (((mv kwd-alist others)
        (std::extract-keywords 'glmc-hint (strip-cars *glmc-hint-table*) args nil))
       ((when others)
        (mv (msg "Extra stuff in glmc-hint args: ~x0~%" others) nil state))
       ((mv err glmc-kwds glcp-kwds state)
        (glmc-process-hint-kwds *glmc-hint-table* kwd-alist state))
       ((when err)
        (mv err nil state))
       (clause-proc-name (if (cdr (assoc :side-goals kwd-alist))
                             'glmc-side-goals
                           ;; (table glmc-info 'latest-glmc-clause-proc ',name)
                           (cdr (assoc 'latest-glmc-clause-proc (table-alist 'glmc-info (w state))))))
       ((unless clause-proc-name)
        (mv "No GLMC clause processor defined according to the glmc-info table." nil state)))
    (value
     `(:computed-hint-replacement
       ((acl2::use-by-computed-hint clause)
        (b* ((lit (car clause)))
          (let ((hints
                 (case-match lit
                   (('not ('gl-cp-hint ('quote clausetype)))
                    (case clausetype
                      (clause-check     ',(cdr (assoc :clause-check-hints kwd-alist)))
                      (st-hyp-inductive ',(cdr (assoc :state-hyp-inductive-hints kwd-alist)))
                      (run-check        ',(cdr (assoc :run-check-hints kwd-alist)))
                      (measure-check    ',(cdr (assoc :measure-hints   kwd-alist)))
                      (coverage         ',(glcp-coverage-hints
                                           (cdr (assoc :do-not-expand kwd-alist))
                                           (cdr (assoc :cov-theory-add kwd-alist))
                                           (cdr (assoc :cov-hints kwd-alist))
                                           (cdr (assoc :cov-hints-position kwd-alist))))
                      (otherwise nil)))
                   (& nil))))
            (and hints
                 `(:computed-hint-replacement
                   ,hints
                   ;; dumb way of going right to the computed-hint-replacement
                   ;; from this hint
                   :clause-processor (identity-cp clause))))))
       :clause-processor
       (,clause-proc-name
        clause
        (make-glmc-config
         :glcp-config (make-glcp-config . ,glcp-kwds)
         . ,glmc-kwds)
        interp-st
        state)
       :do-not-induct t))))

(defmacro glmc-hint (&rest args)
  `(glmc-hint-fn ',args state))


(defxdoc glmc
  :parents (gl)
  :short "ACL2 interface to AIG-based safety model checking"
  :long "<p>The GLMC package allows automated proving of safety properties of
state machines defined in ACL2.  It uses GL to obtain a representation for the
next-state function, property, etc. as AIGs, and calls on an AIG model checker
such as ABC to verify the property.</p>

<p>Here is a small example:</p>

@({

 (include-book \"glmc\")
 (include-book \"bfr-mcheck-abc\")
 (include-book \"centaur/gl/bfr-satlink\" :dir :system)

 ;; use abc as the model checking engine
 (bfr-mcheck-use-abc-simple)
 ;; use satlink (glucose) as the SAT checker
 (gl-satlink-mode)

 ;; start the external shell interface
 (value-triple (acl2::tshell-start))

 ;; Definition of a (very) simple machine: machine state is just a 4-bit natural
 ;; which can be reset to 0 or incremented, but when incremented to exactly 10
 ;; resets to 0.  This is the next-state function:
 (defun my-nextst (st incr reset)
   (b* (((when reset) 0)
        (st (lnfix st))
        ((unless incr) st)
        (next (1+ st))
        ((when (eql next 10)) 0))
     next))

 ;; We'll check that this machine never reaches a state equal to 14.  This function
 ;; checks the property for any finite run, where st is the initial state and ins
 ;; is the list of input pairs (incr . reset):
 (defund my-run-prop (st ins)
   (declare (xargs :measure (len ins)))
   (if (atom ins)
       t
     (and (not (equal st 14))
          (my-run-prop (my-nextst st (caar ins) (cdar ins)) (cdr ins)))))

 ;; Here we prove that if the initial value of the machine state is less than
 ;; 5, then our property holds:
 (defthm my-run-prop-correct
   (implies (and (natp st)
                 (< st 5))
            (my-run-prop st ins))
   :hints ((glmc-hint
            :shape-spec-bindings `((incr ,(g-var 'incr))
                                   (reset ,(g-var 'reset))
                                   (st ,(g-int 0 1 5)))
            :state-var st
            :initstatep (< st 5)
            :nextstate (my-nextst st incr reset)
            :frame-input-bindings ((incr (caar ins))
                                   (reset (cdar ins)))
            :rest-of-input-bindings ((ins (cdr ins)))
            :end-of-inputsp (atom ins)
            :measure (len ins)
            :run (my-run-prop st ins)
            :state-hyp (and (natp st) (< st 16))
            :prop (not (equal st 14))
            :run-check-hints ('(:expand ((my-run-prop st ins)))))))
 })

<p>The notable thing about this example is that the property, as stated, is not
inductive.  The usual way to prove this in ACL2 would be to strengthen the
property into an invariant that is inductive -- either weaken the initial state
assumption so that it is inductive (assume @('(< i 10)') instead of @('(< i
5)')) or strengthen the property (check @('(< st 10)') instead of
@('(not (equal st 14))')).  Instead, we leave that task to the external model
checker (in this case ABC).  GL transforms the ACL2 conjecture into a
finite-state machine safety property.  If we trust ABC when it says the
property was proved, then this produces an ACL2 theorem.</p>


<h3>Glmc-hint options</h3>

<p>GLMC is invoked by the glmc-hint macro, which takes several keyword options:</p>

<ul>

<li>@(':state-var') is the variable containing the current machine
state (as distinguished from the inputs).</li>

<li>@(':body-bindings') is a list of @(see b*) bindings under which to evaluate
the @(':nextstate), @(':initstatep') @(':prop'), and @(':constraint') terms.
It should only use the state variable and frame inputs.</li>

<li>@(':initstatep') is a term that must be true for valid initial states,
though it may reference any variables bound in @(':body-bindings') as well as
the state and frame input variables.</li>

<li>@(':nextstate') is a term giving the next value of the state, in terms of
the state variable, frame inputs, and variables bound by @(':body-bindings').</li>

<li>@(':run') is a term calling some function that recursively checks the
property on some finite run, i.e. it checks the property of the current state
and input frame, then recurs after updating the state with the nextstate
function.</li>

<li>@(':frame-input-bindings') is a binding list (such as in a @('let')),
giving the current-frame inputs in terms of the inputs to the run
function. We'll refer to (e.g.) the list of all remaining frame inputs as the
\"run inputs\", versus (e.g.) a single element of that list as the \"frame
inputs\". E.g., if the input to the run function is simply a list of frame
inputs, then this binding might be @('((in (car ins)))').  </li>

<li>@(':rest-of-input-bindings') is a binding list giving the rest of the
inputs after the current frame, such as is passed to the recursive call of the
run function -- e.g., @('((ins (cdr ins)))').</li>

<li>@(':end-of-inputsp') is a term saying when to stop the run; the run
function should always be true when @(':end-of-inputsp') holds, because that
means it has failed to find a frame in which the property is violated.  In the
case of a simple list of frame inputs, this would be @('(atom ins)').</li>

<li>@(':measure') gives a measure for the run function; for technical reasons,
we must reprove the termination of the run function.</li>

<li>@(':shape-spec-bindings') gives a binding of the state variable and frame
input variables to shape specifier objects; see @(see shape-specs).  Unlike the
other arguments, this one is evaluated, so if you don't want to evaluate it,
quote it.</li>

<li>@(':input-hyp') gives an assumption about the frame inputs that must hold
in each frame or else the run function will return true. (If you want to have a
separate theorem hypothesis saying that the assumption holds for each input,
you may include this in the @(':run') term using @('implies').)  This is used
to prove that the shape-spec given for each non-state input is sufficient to
cover all allowed inputs.</li>

<li>@(':state-hyp') gives an assumption that must hold of all valid states; it
is used to prove that the shape-spec given for the state variable is sufficient
to cover all possible states.  The goal to be proved must assume the state-hyp
holds of the initial state, and it will be proven to hold of all other states
by model checking or inductively; see the @(':state-hyp-method') option
below.</li>

<li>@(':state-hyp-method') should be one of @(':inductive-sat'),
@(':inductive-clause'), or @(':mcheck') (the default); this determines the
method by which we show that the state hyp is invariant.  If it is
@(':inductive-clause'), a proof obligation is generated saying that the state
hyp holds of the next-state if the input hyp and state hyp hold of the current
state.  If it is @(':inductive-sat'), a SAT check is issued which proves this
at the Boolean level.  If it is @(':mcheck'), then the condition is ANDed with
the property in the model checking problem.  This is a more flexible method
 (though potentially slower) because the state hyp may be an invariant of all
reachable states without being an inductive invariant.</li>

<li>@(':prop') gives the property that must be proven to hold in each
frame (i.e., the run function returns false if it is ever violated).  It may
reference the state and frame input variables as well as variables bound in the
@(':body-bindings').</li>

<li>@(':constraint') gives a constraint that is assumed to hold in each
frame (i.e., the run function returns true if it is ever violated). (This may
be omitted; its default is @('T').)  It may reference the state and frame input
variables as well as variables bound in the @(':body-bindings').</li>

<li>@(':side-goals'), if set to @('T'), skips the actual model checking and
simply returns the \"side goals\" such as coverage and the check that the run
function and input clause are of the expected form. (A theorem with
@(':side-goals t') will always fail to prove, but if everything is successful
only a single subgoal of the form @('(not (gl-cp-hint 'side-goals-fake-goal))')
will remain.)</li>

<li>@(':check-vacuity') is @('T') by default; when true, GLMC will check that
the state-hyp, input-hyp, initial state predicate, constraint, and property are
each separately satisfiable, since any of these being unsatisfiable likely
indicates something unexpected.  Setting this to @('NIL') skips these
checks.</li>

<li>@(':clause-check-hints'), @(':run-check-hints), @(':measure-hints'), and
@(':state-hyp-inductive-hints') provide computed hints to various side goals
produced by the clause processor.  Each entry should be a list of hints like
the usual @(':hints') provided to a defthm event, but all the hints should be
computed hints, not subgoal hints.  The side goals are discussed below.</li>

<li>@(':do-not-expand'), @(':cov-theory-add'), @(':cov-hints'), and
@(':cov-hints-position') affect the hints given to the coverage side goal; see
@(see coverage-problems).  To provide your own hints, completely overriding the
default hints provided for coverage, use @(':cov-hints') to give your hints and
set @(':cov-hints-position :replace').</li>

</ul>

<h3>Side goals</h3>

<p>A few proof obligations are produced by a successful call of the GLMC clause
processor.</p>

<ul>

<li>Coverage: Shows that the shape specifiers provided in the
@(':shape-spec-bindings') argument are sufficient to cover all possible states
and inputs allowed by the state and input hyps.  This goal has the same form as
any GL coverage proof; see @(see shape-specs) and @(see coverage-problems).</li>

<li>Clause check: This simply shows that the goal clause is of the required
form.  Specifically, the original goal must follow from this conjecture, which
is what GLMC actually proves:
@({
  (implies (and <initstp> <st-hyp>)
           <run>)
 })</li>

<li>Run check: This checks that the @(':run') term is implied by the recurrence
that is proved by the model check, namely:
@({
 (if <end-of-inputs>
     t
   (let <frame-input-bindings>
     (let <rest-of-input-bindings>
       (if (not (and <input-hyp>
                     (b* <body-bindings> <constraint>)))
           t
         (if (not (b* <body-bindings> <prop>))
             nil
           (let ((<st-var> (b* <body-bindings> <nextstate>)))
             (if (not <state-hyp>)
                 'nil
               <run>)))))))
 })</li>

<li>Measure check: This rechecks that the run function terminates, which is
necessary for technical reasons.</li>

<li>State-hyp-inductive check: This only occurs if the @(':state-hyp-method')
is @(':inductive-clause'); it shows that the state hyp is invariant.</li>

</ul>

<h3>Backends</h3>

<p>GLMC uses the same method as GL to solve combinational SAT problems, such as
vacuity checks (see @(see modes)).  GLMC calls its model-checking backend
through an attachable function called @(see bfr-mcheck). The book
\"glmc/bfr-mcheck-abc.lisp\" provides one backend that can be attached to
@('bfr-mcheck') by calling the macro @('(bfr-mcheck-use-abc-simple)').  That
backend requires a trust tag because it calls out to ABC; it also simply trusts
ABC when it claims the conjecture is proved.</p>

")
