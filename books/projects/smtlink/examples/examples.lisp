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
(include-book "basictypes")

; cert_param: (uses-smtlink)

(value-triple (tshell-ensure))
(add-default-hints '((SMT::SMT-computed-hint clause)))

;; Example 1
(def-saved-event x^2-y^2
  (defun x^2-y^2 (x y) (- (* x x) (* y y))))
(def-saved-event x^2+y^2
  (defun x^2+y^2 (x y) (+ (* x x) (* y y))))

(def-saved-event poly-ineq
  (defthm poly-ineq-example
    (implies (and (real/rationalp x) (real/rationalp y)
                  (<= (+ (* (/ 9 8) x x) (* y y)) 1)
                  (<=  (x^2-y^2 x y) 1))
             (< y (- (* 3 (- x (/ 17 8)) (- x (/ 17 8))) 3)))
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
@($ x^2-y^2 \\le 1$), then @($ y < 3(x-\\frac{17}{8})^2 - 3$).
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
Goal''
SMT-goal-generator=>Expanding ... X^2-Y^2
Subgoal 2
Subgoal 2.2
Subgoal 2.2'
Using default SMT-trusted-cp...
; SMT solver: `python /tmp/py_file/smtlink.w59zR`: 0.52 sec, 7,904 bytes
Proved!
Subgoal 2.2''
Subgoal 2.1
Subgoal 2.1'
Subgoal 1
Subgoal 1'

Summary
Form:  ( DEFTHM POLY-INEQ-EXAMPLE ...)
Rules: ((:DEFINITION HIDE)
        (:DEFINITION HINT-PLEASE)
        (:DEFINITION NOT)
        (:DEFINITION TYPE-HYP)
        (:DEFINITION X^2-Y^2)
        (:EXECUTABLE-COUNTERPART BINARY-*)
        (:EXECUTABLE-COUNTERPART ACL2::BOOLEAN-LIST-FIX$INLINE)
        (:EXECUTABLE-COUNTERPART CAR)
        (:EXECUTABLE-COUNTERPART CDR)
        (:EXECUTABLE-COUNTERPART CONS)
        (:EXECUTABLE-COUNTERPART CONSP)
        (:EXECUTABLE-COUNTERPART UNARY--)
        (:EXECUTABLE-COUNTERPART UNARY-/)
        (:FAKE-RUNE-FOR-TYPE-SET NIL)
        (:REWRITE ASSOCIATIVITY-OF-+)
        (:REWRITE ACL2::COMMUTATIVITY-2-OF-+)
        (:REWRITE COMMUTATIVITY-OF-*)
        (:REWRITE COMMUTATIVITY-OF-+)
        (:REWRITE DISTRIBUTIVITY)
        (:TYPE-PRESCRIPTION NONNEGATIVE-PRODUCT))
Hint-events: ((:CLAUSE-PROCESSOR ADD-HYPO-CP)
              (:CLAUSE-PROCESSOR EXPAND-CP-FN)
              (:CLAUSE-PROCESSOR PROCESS-HINT)
              (:CLAUSE-PROCESSOR SMT-TRUSTED-CP)
              (:CLAUSE-PROCESSOR TYPE-EXTRACT-FN)
              (:CLAUSE-PROCESSOR UNINTERPRETED-FN-CP))
Time:  0.60 seconds (prove: 0.60, print: 0.00, other: 0.00)
Prover steps counted:  1440
POLY-INEQ-EXAMPLE

})

<p>Smtlink is a sequence of clause processors controlled by a computed hint.
Calling smtlink from the @(':hints') put the theorem clause though a clause
processor looking for syntax errors in the @(see smt-hint).  If nothing wrong,
it will generate a term to be recognized by the computed-hint
@('SMT::SMT-computed-hint').  The computed-hint then installs the next-to-be
clause processor to work on the clause.  The next is the verified clause
processor for adding hypotheses. After that is the verified clause processor
for function expansion.</p>

<p>@('SMT-goal-generator=>Expanding ... X^2-Y^2') shows function expansion is
being conducted. </p>

<p>In this example, several subgoals are generated as a result of this clause
processor.  The first subgoal is the goal to be sent to the trusted clause
processor that transliterates the term into the corresponding SMT form and
writes it out to a file.  An SMT solver is called upon the file and results are
read back into ACL2.  Below are the outputs from this clause processor called
@('SMT-trusted-cp').
</p>

@({
Using default SMT-trusted-cp...
; SMT solver: `python /tmp/py_file/smtlink.w59zR`: 0.52 sec, 7,904 bytes
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

<p>Other subgoals are auxiliary clauses generated by the verified
clause-processors. They help ensure the soundness of Smtlink.</p>
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
  :short "Example 3: defense against evil"
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

(define foo ((x real/rationalp))
  :returns (rx real/rationalp)
  (b* ((x (realfix x)))
    (+ (* x x) 1)))

(in-theory (disable (:type-prescription foo)))

(defthm poly-ineq-example-functions
  (implies (and (real/rationalp x))
           (< 0 (* 2 (foo x))))
  :hints(("Goal"
          :smtlink
          (:functions ((foo :formals ((x real/rationalp))
                            :returns ((rx real/rationalp))
                            :level 0))
           :hypotheses (((<= 1 (foo x))
                         :hints (:in-theory (enable foo))))
          ))))

(def-saved-event fty-deflist-theorem-example
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
    :rule-classes nil))

(acl2::must-fail
(defthm fty-deflist-theorem-fail
  (implies (and (integer-listp l)
                (consp (acl2::integer-list-fix l))
                (consp (acl2::integer-list-fix (cdr (acl2::integer-list-fix l)))))
           (>= (x^2+y^2 (car (acl2::integer-list-fix l))
                        (car (acl2::integer-list-fix
                              (cdr (acl2::integer-list-fix l)))))
               1))
  :hints(("Goal"
          :smtlink
          (:fty (acl2::integer-list))))
  :rule-classes nil)
)

(def-saved-event symbol-integer-example
  (defalist symbol-integer-alist
    :key-type symbolp
    :val-type integerp
    :true-listp t)
)

(def-saved-event fty-defalist-theorem-example
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
  )

(defthm fty-defalist-theorem-acons
  (implies (and (symbol-integer-alist-p l)
                (symbolp s1)
                (symbolp s2)
                (not (equal (assoc-equal s1 (symbol-integer-alist-fix
                                             (acons 'x 1
                                                    (symbol-integer-alist-fix l))))
                            (smt::magic-fix 'symbolp_integerp nil)))
                (not (equal (assoc-equal s2 (symbol-integer-alist-fix l))
                            (smt::magic-fix 'symbolp_integerp nil))))
           (>= (x^2+y^2
                (cdr (smt::magic-fix
                      'symbolp_integerp
                      (assoc-equal s1 (symbol-integer-alist-fix
                                       (acons 'x 1
                                              (symbol-integer-alist-fix l))))))
                (cdr (smt::magic-fix 'symbolp_integerp
                                     (assoc-equal s2 (symbol-integer-alist-fix l)))))
               0))
  :hints(("Goal"
          :smtlink
          (:fty (symbol-integer-alist))))
  :rule-classes nil)

(acl2::must-fail
(defthm fty-defalist-theorem-fail
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
               1))
  :hints(("Goal"
          :smtlink
          (:fty (symbol-integer-alist))))
  :rule-classes nil)
)

(def-saved-event sandwich-example
  (defprod sandwich
    ((bread integerp)
     (fillings symbolp)))
  )

(def-saved-event fty-defprod-theorem-example
  (defthm fty-defprod-theorem
    (implies (and (sandwich-p s1)
                  (sandwich-p s2))
             (>= (x^2+y^2
                  (sandwich->bread s1)
                  (sandwich->bread s2))
                 0))
    :hints(("Goal"
            :smtlink
            (:fty (sandwich))))
    :rule-classes nil)
  )

(acl2::must-fail
(defthm fty-defprod-theorem-fail
  (implies (and (sandwich-p s1)
                (sandwich-p s2))
           (>= (x^2+y^2
                (sandwich->bread (sandwich-fix s1))
                (sandwich->bread (sandwich-fix s2)))
               1))
  :hints(("Goal"
          :smtlink
          (:fty (sandwich))))
  :rule-classes nil)
) 

(def-saved-event x^2+y^2-fixed-example
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
  )

(def-saved-event fty-defoption-theorem-example
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
  )

(acl2::must-fail
(defthm fty-defoption-theorem-fail
  (implies (and (maybe-integer-p m1)
                (maybe-integer-p m2)
                (not (equal m1 (maybe-integer-fix nil)))
                (not (equal m2 (maybe-integer-fix nil))))
           (>= (maybe-integer-some->val (x^2+y^2-fixed m1 m2))
               1))
  :hints(("Goal"
          :smtlink
          (:fty (maybe-integer))))
  :rule-classes nil)
)

(acl2::must-fail
(defthm bogus-revised
  (implies (and (symbolp symx) (symbolp symy))
           (or (eq (symbol-fix symx) 'sym1) (eq (symbol-fix symx) 'sym2)
               (eq (symbol-fix symx) 'sym3)
               (eq (symbol-fix symy) 'sym1) (eq (symbol-fix symy) 'sym2)
               (eq (symbol-fix symy) 'sym3)
               (eq (symbol-fix symx)
                   (symbol-fix symy))))
  :hints (("Goal" :smtlink nil)))
)

(acl2::must-fail
(defthm bogus-revised-still-bogus
  (implies (and (symbolp symx) (symbolp symy))
           (or (eq symx 'symx) (eq symx 'sym2)
               (eq symx 'sym3)
               (eq symy 'symx) (eq symy 'sym2)
               (eq symy 'sym3)
               (eq symx symy)))
  :hints (("Goal" :smtlink nil)))
)

(defprod sym-prod
  ((sym symbolp)))

(acl2::must-fail
(defthm bogus-revised-still-bogus-prod
  (implies (and (sym-prod-p x) (sym-prod-p y))
           (or (eq (sym-prod->sym x) 'sym1) (eq (sym-prod->sym x) 'sym2)
               (eq (sym-prod->sym x) 'sym3)
               (eq (sym-prod->sym y) 'sym1) (eq (sym-prod->sym y) 'sym2)
               (eq (sym-prod->sym y) 'sym3)
               (eq (sym-prod->sym x) (sym-prod->sym y))))
  :hints (("Goal" :smtlink (:fty (sym-prod)))))
)

(acl2::must-fail
 (defthm check-guard
   (implies (acl2::integer-listp x)
            (equal (1+ (1- (car (acl2::integer-list-fix x))))
                   (car (acl2::integer-list-fix x))))
   :hints (("Goal" :smtlink (:fty (acl2::integer-list)))))
)

(acl2::must-fail
 (defthm check-guard-2
   (implies (and (symbol-integer-alist-p l)
                 (symbolp x))
            (equal (1+ (1- (cdr
                            (magic-fix 'symbolp_integerp
                                       (assoc-equal x (symbol-integer-alist-fix
                                                       l))))))
                   (cdr (magic-fix 'symbolp_integerp
                                   (assoc-equal x (symbol-integer-alist-fix l))))))
   :hints (("Goal" :smtlink (:fty (symbol-integer-alist)))))
 )

(defthm check-guard-3
  (implies (maybe-integer-p x)
           (equal (1+ (1- (maybe-integer-some->val
                           (maybe-integer-fix x))))
                  (maybe-integer-some->val
                   (maybe-integer-fix x))))
  :hints (("Goal" :smtlink (:fty (maybe-integer))))
  )

(acl2::must-fail
 (defthm check-guard-3-fail
   (implies (maybe-integer-p x)
            (equal (1+ (1- (maybe-integer-fix x)))
                   (maybe-integer-fix x)))
   :hints (("Goal" :smtlink (:fty (maybe-integer))))
   )
 )

(acl2::must-fail
(defthm check-rational-cex
  (implies (rationalp x)
           (not (equal x 1/4)))
  :hints (("Goal" :smtlink (:fty (maybe-integer))))
  )
)

(acl2::must-fail
 (defthm check-boolean-cex
   (implies (booleanp x)
            (not (equal x nil)))
   :hints (("Goal" :smtlink (:fty (maybe-integer))))
   )
 )

(acl2::must-fail
 (defthm check-symbol-cex
   (implies (symbolp x)
            (not (equal x 'arbitrary-sym)))
   :hints (("Goal" :smtlink (:fty (maybe-integer))))
   )
 )

;; algebraic counter-example example by Carl Kwan
(acl2::must-fail
(defthm poly-sat-7
  (implies (and (real/rationalp x)
                (equal (* (+ x -1) (+ x 1) (+ x 2)) 0)
                (< x 0)
                (real/rationalp y)
                (equal (* y y) 2))
           (and (equal x -1)
                (< y 0)))
  :rule-classes nil
  :hints (("Goal"
		       :smtlink nil)))
)

(deftutorial FTY-examples
  :parents (Tutorial)
  :short "A list of FTY examples"
  :long "<h3>FTY examples</h3>
<p>Prerequisite read for this tutorial example is @(tsee tutorial).</p>
<p>Smtlink supports types defined by @(tsee acl2::FTY) macros @(tsee defprod), @(tsee
  deflist), @(tsee defalist) and @(tsee defoption). We show here an example for
  each type.</p>

<h4>defprod</h4>
<p>Define the function @('x^2+y^2')</p>
@(`(:code ($ ||x^2+y^2||))`)

<p>Define the defprod @('sandwich')</p>
@(`(:code ($ sandwich))`)

<p>Then define the theorem to prove:</p>
@(`(:code ($ fty-defprod-theorem-example))`)

<p>This theorem says, given two @('sandwich-p'), then the square sum of the
bread field of the two sandwiches should be non-negative. This example doesn't
quite make sense.  Here we use this as an example to show how @('defprod')
defined types can be used in a theorem to be discharged by Smtlink.</p>

<p>We notice the @(':fty') hint is used to tell Smtlink which set of FTY types
we will use in proving this theorem. Here, we use the FTY type
@('sandwich'). Smtlink will check @('fty::flextypes-table') for information
about this FTY type.</p>

<p>Counter-examples for defprods like like:</p>
@({
Possible counter-example found:
((S2 (SANDWICH 0 (SYM 2))) (S1 (SANDWICH 0 (SYM 1))))
})


<h4>deflist</h4>
<p>Define the theorem to prove:</p>
@(`(:code ($ fty-deflist-theorem-example))`)

<p>This theorem says, given a list of integers, if there are at least two
elements, then the square sum of the two elements should be non-negative.</p>

<p>First, Smtlink only allows types defined by deflist that are @(tsee
true-listp).  We notice the @(':fty') hint is used to tell Smtlink which set of
FTY types we will use in proving this theorem. Here, we use the FTY type
@('acl2::integer-list'). Smtlink will check @('fty::flextypes-table') to make
sure the given deflist type is a true-listp.</p>

<p>Second, we notice extra fixing functions @(tsee acl2::integer-list-fix)
functions are added. This is because Z3 lists are typed. The polymorphic
functions like @('car') when translated into Z3, also become typed. Therefore
we need to inference which @('car') we want to apply here. Currently Smtlink
doesn't have type inference ability, therefore it requires the user to add
fixing functions for telling it the types.</p>

<p>Counter-examples for deflists like like:</p>
@({
Possible counter-example found: ((L (CONS 0 (CONS 0 NIL))))
})

<h4>defalist</h4>
<p>Define the defalist @('symbol-integer-alist')</p>
@(`(:code ($ symbol-integer-example))`)

<p>Then define the theorem to prove:</p>
@(`(:code ($ fty-defalist-theorem-example))`)

<p>This theorem says, given a symbol-integer-alist l, two symbols s1 and s2, if
one can find both s1 and s2 in the alist l, then the values satisfy that their
square sum is non-negative. I hope the square sum example hasn't bored you yet
at this point.</p>

<p>Similar to deflists, we notice extra fixing functions
@('symbol-integer-alist-fix') functions are added due to similar reasons. In
addition, we notice ACL2 doesn't have a type specification for the thing
returned by an assoc-equal. To make sure @('cdr') knows what its argument type
is, we add a @('magic-fix') function.</p>

<p>Counter-examples for defalists like like:</p>
@({
((S2 (SYM 2)) (L (K SYMBOL (SOME 0))) (S1 (SYM 1)))
})

<p>Here, the counter-example for alist l is</p>
 @({(K SYMBOL (SOME 0))})
<p>This means in Z3 a constant array mapping from symbols to the maybe integer
 0. Also, @('SYM') stands for generated symbols for symbol
 counter-examples.</p>

<h4>defoption</h4>
<p>Define the defoption @('maybe-integer')</p>
@(`(:code ($ maybe-integer-example))`)

<p>Define the fixed version of @('x^2+y^2')</p>
@(`(:code ($ x^2+y^2-fixed-example))`)

<p>Then define the theorem to prove:</p>
@(`(:code ($ fty-defoption-theorem-example))`)

<p>This theorem says, given a maybe-integer m1 and a maybe-integer m2, if they
are not nils, then the square sum of their values is non-negative.</p>

<p>Similar to deflists and defalists, we notice extra fixing functions
@('maybe-integer-fix') functions are added due to similar reasons. In addition,
we notice in definition of function @('x^2+y^2-fixed'), even when one knows x
and y are not nil, they are still maybe-integers. Therefore, field-accessors
and constructors are required.</p>

<p>Counter-examples for defalists like like:</p>
@({
Possible counter-example found: ((M2 (SOME 0)) (M1 (SOME 0)))
})

")

(defthm poly-ineq-example-with-prog2$
  (implies (and (real/rationalp x) (real/rationalp y)
                (<= (+ (* (/ 9 8) x x) (* y y)) 1)
                (<= (prog2$ (cw "I'm here!~%")
                            (x^2-y^2 x y))
                    1))
           (< y (- (* 3 (- x (/ 17 8)) (- x (/ 17 8))) 3)))
  :hints(("Goal"
          :smtlink nil)))

;; Abstract datatype example
(encapsulate
  (((abstract-p *) => *))
  (local
   (defun abstract-p (x)
       (acl2::any-p x))))

(defthm abstract-example
  (implies (abstract-p x)
           (equal x x))
  :hints(("Goal"
          :smtlink (:abstract (abstract-p))))
  :rule-classes nil)

;; Thanks to Andrew Walter and Pete Manolios for providing this bug example.
;; In this example, it used to be that unary-/ is translated to be integer
;; division in Z3. Since unary-/ is interpreted as integer division and x >=
;; 10, 1/x is 0, which makes y 0. We fixed this problem by casting the input of
;; unary-/ to be real. Check the reciprocal function in ACL2_to_Z3.py for
;; detail.
(acl2::must-fail
 (defthm smt-not-integer-division
   (implies (and (integerp x)
                 (integerp y)
                 (integerp z)
                 (>= x 10)
                 (= y (* (unary-/ x) z)))
            (= y 0))
   :hints (("goal" :smtlink nil))
   :rule-classes nil)
 )
