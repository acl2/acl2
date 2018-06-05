;; Copyright (C) 2015, University of British Columbia
;; Written (originally) by Yan Peng (August 2nd 2016)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2


(in-package "SMT")
(include-book "../top")
(include-book "centaur/sv/tutorial/support" :dir :system)
;; def-saved-event is a wrapper that is used by the documentation system,
;; and can be ignored by the reader.
;; Check the book centaur/sv/tutorial/support.lisp for detailed explanation.

; cert_param: (uses-smtlink)

(value-triple (tshell-ensure))
(add-default-hints '((SMT::SMT-process-hint clause
                                            ;; stable-under-simplificationp
                                            )))


;; Section 2. A short tour
;; Example 1
(def-saved-event x^2-y^2
  (defun x^2-y^2 (x y) (- (* x x) (* y y))))
(def-saved-event x^2+y^2
  (defun x^2+y^2 (x y) (+ (* x x) (* y y))))

(defthm fty-deflist-theorem
  (implies (and (integer-listp l)
                (consp (acl2::integer-list-fix l))
                (consp (acl2::integer-list-fix (cdr (acl2::integer-list-fix l)))))
           (>= (x^2+y^2 (car (acl2::integer-list-fix l))
                        (car (acl2::integer-list-fix
                              (cdr (acl2::integer-list-fix l)))))
               0))
  :hints(("Goal"
          :smtlink
          (:fty (acl2::integer-list))))
  :rule-classes nil)

(defalist symbol-integer-alist
  :key-type symbolp
  :val-type integerp
  :true-listp t)

(defthm fty-defalist-theorem
  (implies (and (symbol-integer-alist-p l)
                (symbolp s1)
                (symbolp s2)
                (not (equal (assoc-equal s1 (symbol-integer-alist-fix l))
                            (smt::magic-fix 'symbolp_integerp nil)))
                (not (equal (assoc-equal s2 (symbol-integer-alist-fix l))
                            (smt::magic-fix 'symbolp_integerp nil))))
           (>= (x^2+y^2
                (cdr (smt::magic-fix 'symbolp_integerp
                                     (assoc-equal s1 (symbol-integer-alist-fix l))))
                (cdr (smt::magic-fix 'symbolp_integerp
                                     (assoc-equal s2 (symbol-integer-alist-fix l)))))
               0))
  :hints(("Goal"
          :smtlink
          (:fty (symbol-integer-alist))))
  :rule-classes nil)

(defprod sandwich
  ((bread integerp)
   (fillings symbolp)))

(defthm fty-defprod-theorem
  (implies (and (sandwich-p s1)
                (sandwich-p s2))
           (>= (x^2+y^2
                (sandwich->bread (sandwich-fix s1))
                (sandwich->bread (sandwich-fix s2)))
               0))
  :hints(("Goal"
          :smtlink
          (:fty (sandwich))))
  :rule-classes nil)

(defoption maybe-integer integerp)

(define x^2+y^2-fixed ((x maybe-integer-p)
                       (y maybe-integer-p))
  :returns (res maybe-integer-p)
  (b* ((x (maybe-integer-fix x))
       (y (maybe-integer-fix y))
       ((if (equal x (maybe-integer-fix nil)))
        (maybe-integer-fix nil))
       ((if (equal y (maybe-integer-fix nil)))
        (maybe-integer-fix nil)))
    (maybe-integer-some
     (+ (* (maybe-integer-some->val x)
           (maybe-integer-some->val x))
        (* (maybe-integer-some->val y)
           (maybe-integer-some->val y))))))

(defthm fty-defoption-theorem
  (implies (and (maybe-integer-p m1)
                (maybe-integer-p m2)
                (not (equal m1 (maybe-integer-fix nil)))
                (not (equal m2 (maybe-integer-fix nil))))
           (>= (maybe-integer-some->val (x^2+y^2-fixed m1 m2))
               0))
  :hints(("Goal"
          :smtlink
          (:fty (maybe-integer))))
  :rule-classes nil)

(def-saved-event poly-ineq
  (defthm poly-ineq-example
    (implies (and (real/rationalp x) (real/rationalp y)
                  (<= (+ (* (/ 9 8) x x) (* y y)) 1)
                  (<=  (x^2-y^2 x y) 1))
             (<= y (* 3 (- x (/ 17 8)) (- x (/ 17 8)))))
    :hints(("Goal"
            :smtlink nil)))
  )


(deftutorial Example-1
  :parents (Tutorial)
  :short "Example 1: the basics"
  :long "<h3>Example 1</h3>
<p>Prerequisite read for this tutorial example is @(tsee tutorial).</p>
<p>The first example is a basic polynomial inequality.  Let's say we want to
prove below theorem:</p>

<box>
<p>
<b><color rgb='#323cbe'>Theorem 1.</color></b>
@($\\forall x\\in R$) and @($\\forall y \\in R$), if @($ \\frac{9x^2}{8}+y^2 \\le 1$) and
@($ x^2+y^2 \\le 1$), then @($ y\\le3(x-\\frac{17}{8})^2$).
</p>
</box>

<p>Suppose we've defined a function called @('x^2-y^2') like below:</p>

@(`(:code ($ x^2-y^2))`)

<p>We define our theorem as:</p>

@(`(:code ($ poly-ineq))`)

<p>Smtlink should just prove this inequality without any problem.</p>
<p>Like is shown in the example, @(':smtlink') can be provided as a hint in the
standard @(see acl2::hints) in ACL2.  In the most basic cases where Smtlink
handles everything, no @(see smt-hint) are required to be provided, Hence
@(':smtlink nil').</p>

<p>The output of this defthm should look similar to:</p>

@({
Using clause-processor Smtlink
Goal'
SMT-goal-generator=>Expanding ... X^2-Y^2
Subgoal 4
Using default SMT-trusted-cp...
; SMT solver: `python /tmp/py_file/smtlink.Lc3Dh`: 0.32 sec, 7,872 bytes
Proved!
Subgoal 3
Subgoal 3'
Subgoal 2
Subgoal 1

Summary
Form:  ( DEFTHM POLY-INEQ-EXAMPLE ...)
Rules: ((:DEFINITION HINT-PLEASE)
        (:DEFINITION NOT)
        (:DEFINITION X^2-Y^2)
        (:EXECUTABLE-COUNTERPART BINARY-*)
        (:EXECUTABLE-COUNTERPART UNARY--)
        (:EXECUTABLE-COUNTERPART UNARY-/)
        (:FAKE-RUNE-FOR-TYPE-SET NIL)
        (:REWRITE ASSOCIATIVITY-OF-+)
        (:REWRITE ACL2::COMMUTATIVITY-2-OF-+)
        (:REWRITE COMMUTATIVITY-OF-*)
        (:REWRITE COMMUTATIVITY-OF-+)
        (:REWRITE DISTRIBUTIVITY))
Hint-events: ((:CLAUSE-PROCESSOR PROCESS-HINT)
              (:CLAUSE-PROCESSOR SMT-TRUSTED-CP)
              (:CLAUSE-PROCESSOR SMTLINK-SUBGOALS))
Time:  0.38 seconds (prove: 0.38, print: 0.00, other: 0.00)
Prover steps counted:  633
POLY-INEQ-EXAMPLE

})

<p>Smtlink is a sequence of clause processors and computed hints.  Calling
smtlink from the @(':hints') put the theorem clause though a clause processor
looking for syntax errors in the @(see smt-hint).  If nothing wrong, it will
generate a term to be recognized by the first computed-hint
@('SMT::SMT-process-hint').  The first computed-hint then installs the
next-to-be clause processor to work on the clause.  The next is the main
verified clause processor.  Function expansion happens here.</p>

<p>@('SMT-goal-generator=>Expanding ... X^2-Y^2') shows function expansion is
being conducted. </p>

<p>In this example, four subgoals are generated as a result of this clause
processor.  The first subgoal is the goal to be sent to the trusted clause
processor that transliterates the term into the corresponding SMT form and
writes it out to a file.  An SMT solver is called upon the file and results are
read back into ACL2.  Below are the outputs from this clause processor called
@('SMT-trusted-cp').
</p>

@({
Using default SMT-trusted-cp...
; SMT solver: `python /tmp/py_file/smtlink.Lc3Dh`: 0.32 sec, 7,872 bytes
Proved!
})

<p>The second line tells the user what command is run to execute the SMT
solving.  \"Proved!\" indicates the SMT solver has successfully proved the
theorem.  When a theorem failed, a possible counter-example might be
provided in the form:</p>
@({
Possible counter-example found: ((X ...) (Y ...))
One can access it through global variable SMT-cex by doing (@ SMT-
cex).
})

<p>The other three goals are additional goals.  Proving them ensures the first
verified clause processor doesn't introduce unsoundness.  To understand what
they are and why they can ensure soundness.  Check out the references in @(see
Smtlink).</p>
")

(def-saved-event smtconf-expt-tutorial
  (defun my-smtlink-expt-config ()
    (declare (xargs :guard t))
    (change-smtlink-config (default-smt-cnf)
                           :smt-module    "RewriteExpt"
                           :smt-class     "to_smt_w_expt"
                           :smt-cmd       "python"
                           :pythonpath    "")))

(def-saved-event smtconf-expt-defattach-tutorial
  (defattach custom-smt-cnf my-smtlink-expt-config))

;; Example 2
(def-saved-event poly-of-expt-example
  (encapsulate ()
    (local (include-book "arithmetic-5/top" :dir :system))
    (defthm poly-of-expt-example
      (implies (and (real/rationalp x) (real/rationalp y) (real/rationalp z)
                    (integerp m) (integerp n)
                    (< 0 z) (< z 1) (< 0 m) (< m n))
               (<= (* 2 (expt z n) x y)
                   (* (expt z m) (x^2+y^2 x y))))
      :hints (("Goal"
               :smtlink-custom (:functions ((expt :formals ((r real/rationalp)
                                                            (i real/rationalp))
                                                  :returns ((ex real/rationalp))
                                                  :level 0))
                                :hypotheses (((< (expt z n) (expt z m)))
                                             ((< 0 (expt z m)))
                                             ((< 0 (expt z n))))
                                :int-to-rat t)
      )))))

(deftutorial Example-2
  :parents (Tutorial)
  :short "Example 2: something wild"
  :long "<h3>Example 2</h3>
<p>Prerequisite read for this tutorial example is @(tsee tutorial).</p>
<p>Smtlink is extensible, with the user's understanding that the extended part
is not verified and therefore is the user's responsibility to ensure its
soundness.  A different trust tag is installed if this customized Smtlink is
used.  Such ability makes Smtlink very powerful.  Here's an example to show the
usage.</p>
<p>Let's say we want to prove the theorem:</p>

<box>
<p>
<b><color rgb='#323cbe'>Theorem 2.</color></b>
@($\\forall x,y,z\\in R$), and @($\\forall m,n \\in Z$), if @($ 0 \\le z \\le 1$) and
@($ 0 \\le m \\le n $), then @($ 2xy\\cdot z^n \\le (x^2+y^2)z^m$).
</p>
</box>

<p>In @('smtlink/z3_interface/'), file @('RewriteExpt.py') is a Python class
extending from the default class in ACL2_to_Z3.py.  One could imaging defining
one's own file that does magical things in the SMT solver.  What
@('RewriteExpt.py') does is that it uses basic rewrite lemmas about @('expt')
to help the SMT solver to solve.  In order to make Smtlink uses the custom
version instead of the default, one needs to define and attach a new
configuration:</p>

@(`(:code ($ smtconf-expt-tutorial))`)
@(`(:code ($ smtconf-expt-defattach-tutorial))`)

<p>Defining the function @('x^2+y^2')</p>
@(`(:code ($ ||x^2+y^2||))`)

<p>Then define the theorem to prove:</p>
@(`(:code ($ poly-of-expt-example))`)

<p>Notice the @(':hints') keyword used this time is @(':smtlink-custom').  It
allows the customized version of Smtlink to be applied to the current
clause.  Take a read in @(see smt-hint) for a detailed description of each
keyword.  Here we will only describe what's used in this example.</p>

<p>In the hints, @(':function') tells Smtlink to treat @('expt') as an
uninterpreted function.  @(':formals') tells us the input argument types of the
uninterpreted function and @(':returns') tells us the output argument type.
@(':levels') specifies an expansion level of 0, making the function an
uninterpreted function.</p>

<p>@(':hypotheses') provides a list of hypotheses that the user believes to be
true and can help with the proof. The hypotheses will be insert into the
hypotheses when generating the SMT problem. They will be proved correctness
as part of the returned clauses from the verified clause processor. </p>

<p>@(':int-to-rat') tells Smtlink to raise integers to rationals when
translating the clause into a SMT problem. This is because of the limitation in
Z3. Integers mixed with real numbers are hard for Z3. We prove the given
theorem by proving a more general statement in the SMT solver.</p>

<p>Another observation is that, we are including the arithmetic-5 book for
proving the returned auxiliary clauses, which requires arithmetic
reasoning.</p>
")

;; Buggy example
(def-saved-event non-theorem-example
  (acl2::must-fail
   (defthm non-theorem
     (implies (and (real/rationalp x)
                   (real/rationalp y)
                   (integerp (/ x y)))
              (not (equal y 0)))
     :hints(("Goal"
             :smtlink nil))
     :rule-classes nil)))

(deftutorial Example-3
  :parents (Tutorial)
  :short "Example 3: defence against evil"
  :long "<h3>Example 3</h3>
<p>Prerequisite read for this tutorial example is @(tsee tutorial).</p>
<p>The third evil example is from one of the reviews we get when we first
published our paper in @(see Smtlink). </p>

@(`(:code ($ non-theorem-example))`)

<p>This is an evil theorem because we know below is a theorem in ACL2:</p>

@({
(thm (equal (/ x 0) 0))
})

<p>Therefore if Smtlink falsely prove @('non-theorem'), it will introduce
contradiction into ACL2.</p>

<p>Smtlink fails to prove the @('non-theorem') with error message:</p>

@({
HARD ACL2 ERROR in SMT-TRANSLATOR=>TRANSLATE-FUNCTION:  Not a basic
SMT function: INTEGERP
})

<p>This is because ACL2 treats @('integerp')'s as type declarations in Z3.  But
here in this theorem, @('(integerp (/ x y))') is a constraint/hypotheses rather
than a type declaration. When ACL2 tried to translate it as a constraint, it
finds out @('integerp') is not a supported function.</p>
")
