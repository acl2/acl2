; Centaur AIG Library
; Copyright (C) 2008-2011 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: Sol Swords <sswords@centtech.com>
;
; July 2011, Jared added lots of documentation.

(in-package "ACL2")
(include-book "std/util/define" :dir :system)
(include-book "../misc/hons-alphorder-merge")

; aig-base.lisp
;   - Semantics of AIGs (aig-eval)
;   - Primitive AIG constructors (aig-not, aig-and, ...)
;   - Substitution operations: aig-restrict, aig-compose, aig-partial-eval

; BOZO consider using defprojection throughout?

(defsection aig-cases
  :parents (aig-other)
  :short "Control-flow macro to split into cases on what kind of AIG you have
encountered."
  :long "@(def aig-cases)"

  (defmacro aig-cases (x &key true false var inv and)
    `(let ((aig-cases-var ,x))
       (cond
        ((atom aig-cases-var)
         (cond ((eq aig-cases-var t) ,true)
               ((eq aig-cases-var nil) ,false)
               (t ,var)))
        ((eq (cdr aig-cases-var) nil) ,inv)
        (t ,and)))))


; -----------------------------------------------------------------------------
;
;                            EVALUATING AIGS
;
; -----------------------------------------------------------------------------

(defsection aig-env-lookup-missing-output
  :parents (aig-eval)
  :short "Stub for warnings about missing variables in AIG evaluation."

  :long "<p>This stub is called when @(see aig-eval) encounters a variable in
the AIG that has no binding in the environment.  It is generally configured
with @(see aig-env-lookup-missing-action).</p>"

  (defstub aig-env-lookup-missing-output (name) nil))


(defsection aig-env-lookup-missing-action
  :parents (aig-eval)
  :short "Configurable warnings about missing variables in AIG evaluation."

  :long "<p>Ordinarily @(see aig-eval) treats any variables that are not bound
in the environment as having value @('t').  But a missing bindings could be the
result of a bug in your program, so by default @('aig-eval') is set up to print
a warning if this happens.</p>

<p>@(call aig-env-lookup-missing-action) allows you to control whether these
warnings are printed, and also whether @(see break$) should be called.  The
valid @('action')s are:</p>

<ul>
 <li>@('nil'), silently bind the variable to @('t'),</li>
 <li>@(':warn') (the default), print a warning but do not @('break$'), and</li>
 <li>@(':break'), to print the warning and then call @('break$').</li>
</ul>"

  (defconst *aig-env-lookup-warn-missing-binding*
    ;; Even with the stub and defattach, it is useful to have this "constant"
    ;; so that, in raw lisp, we can use a let-binding to disable missing output
    ;; warnings temporarily, e.g., so that if a SAT solver produces an
    ;; incomplete counterexample, we don't print warnings when we check it.
    ;; Doing this with defattach directly would be hard/impossible due to
    ;; attachment being an event.
    t)

  (defun aig-env-lookup-missing-quiet (name)
    (declare (xargs :guard t) (ignore name))
    nil)

  (defun aig-env-lookup-missing-complain (name)
    (declare (xargs :guard t))
    (and *aig-env-lookup-warn-missing-binding*
         (cw "WARNING: Missing variable binding ~x0 in AIG-ENV-LOOKUP; ~
              assigning T~%"
             name)))

  (local (in-theory (disable (break$))))

  (defun aig-env-lookup-missing-break (name)
    (declare (xargs :guard t))
    (and *aig-env-lookup-warn-missing-binding*
         (prog2$ (cw "WARNING: Missing variable binding ~x0 in ~x1; assigning ~
                      T. To avoid this break, run ~x2, where action is NIL or ~
                      :WARN.~%"
                     name
                     'aig-env-lookup
                     '(aig-env-lookup-missing-action action))
                 (break$))))

  (defmacro aig-env-lookup-missing-action (val)
    (case val
      ((nil) '(defattach aig-env-lookup-missing-output
                aig-env-lookup-missing-quiet))
      (:warn '(defattach aig-env-lookup-missing-output
                aig-env-lookup-missing-complain))
      (:break '(defattach aig-env-lookup-missing-output
                 aig-env-lookup-missing-break))
      (t (er hard 'aig-env-lookup-missing-action
             "Expected argument NIL, :WARN, or :BREAK.~%"))))

  (aig-env-lookup-missing-action :warn))


(define aig-env-lookup
  :parents (aig-eval)
  :short "Look up the value of an AIG variable in an environment."

  ((x   "Variable to look up.")
   (env "Fast alist mapping variables to values."))

  :long "<p>Unbound variables are given the default value @('t') instead of
@('nil') because this makes theorems about @(see faig) evaluation work out more
nicely (it makes unbound FAIG variables evaluate to @('X')).</p>

<p>Jared was once tempted to change this to produce an always Boolean
result, since it would seem nicer to do that here than in @(see aig-eval).  But
this function is also used in @(see aig-compose), and it is not valid to
Boolean-fix it there.</p>"

  :enabled t

  (let ((look (hons-get x env)))
    (if look
        (cdr look)
      (mbe :logic t
           :exec
           (if *aig-env-lookup-warn-missing-binding*
               (prog2$ (aig-env-lookup-missing-output x)
                       t)
             t)))))


(define aig-eval
  :parents (aig-semantics)
  :short "@(call aig-eval) gives the semantics of @(see AIG)s: it gives the
Boolean value of the AIG @('x') under the environment @('env')."

  ((x   "The AIG to evaluate.")
   (env "A fast alist that binds variables to values.  Typically it should bind
every variable in @('x') to some Boolean value.  When this isn't the case,
variables are assigned the default value @('t'); see @(see aig-env-lookup)."))

  :long "<p>This function is @(see memoize)d.  You should typically free its
memo table after you are done with whatever @('env') you are using, to avoid
excessive memory usage.  (We don't use @(':forget t') because you often want to
evaluate several related AIGs.)</p>"

  :enabled t

  (aig-cases x
    :true t
    :false nil
    :var (and (aig-env-lookup x env) t)
    :inv (not (aig-eval (car x) env))
    :and (and (aig-eval (car x) env)
              (aig-eval (cdr x) env)))

  ///
  (memoize 'aig-eval :condition '(and (consp x) (cdr x))))

(define aig-eval-list
  :parents (aig-semantics)
  :short "@(call aig-eval-list) evaluates a list of AIGs."
  ((x   "The AIG list to evaluate.")
   (env "The environment to use; see @(see aig-eval)."))
  :returns
  (vals "A list of Boolean values; the evaluations of each AIG under this
         environment.")
  :enabled t
  (if (atom x)
      nil
    (cons (aig-eval (car x) env)
          (aig-eval-list (cdr x) env))))

(define aig-eval-alist
  :parents (aig-semantics)
  :short "@(call aig-eval-alist) evaluates an AIG Alist (an alist binding keys
to AIGs)."
  ((x   "The AIG alist to evaluate.  This does not need to be a fast alist.")
   (env "The environment to use; see @(see aig-eval)."))
  :returns
  (vals-alist "An ordinary (slow) alist that binds the same keys to the values
               of their associated AIGs.")
  :enabled t
  (cond ((atom x)
         nil)
        ((atom (car x))
         ;; Bad-alist convention
         (aig-eval-alist (cdr x) env))
        (t
         (cons (cons (caar x) (aig-eval (cdar x) env))
               (aig-eval-alist (cdr x) env))))
  ///
  (defthm hons-assoc-equal-aig-eval-alist
    (equal (hons-assoc-equal key (aig-eval-alist x env))
           (and (hons-assoc-equal key x)
                (cons key
                      (aig-eval (cdr (hons-assoc-equal key x)) env))))
    :hints(("Goal" :induct t))))

(define aig-eval-alists
  :parents (aig-semantics)
  :short "Evaluate a list of AIG Alists."
  ((x   "List of AIG Alists to evaluate.")
   (env "The environment to use; see @(see aig-eval)."))
  :returns
  (vals-alists "A copy of @('x'), except that each AIG has been replaced with
                its value.")
  :enabled t
  (if (atom x)
      nil
    (cons (aig-eval-alist (car x) env)
          (aig-eval-alists (cdr x) env))))




; -----------------------------------------------------------------------------
;
;                        COLLECTING AIG VARIABLES
;
; -----------------------------------------------------------------------------

(define aig-vars (x)
  :parents (aig)
  :short "@(call aig-vars) returns the variables of the AIG @('X')."
  :returns (vars "An ordered set of AIG variables (atoms).")

  :long "<p>Note: variable collection can be surprisingly tricky to do
efficiently.  For a good background discussion that describes various
approaches to the problem and ways to avoid needing to collect variables, see
@(see 4v-sexpr-vars).</p>

<p>@('aig-vars') is a slow but simple way to collect the variables that occur
within an AIG, and we adopt it as our <b>normal form</b> for talking about the
variables of an AIG.  That is, when we introduce other, faster algorithms for
collecting variables, we always relate them back to @('aig-vars').</p>

<p>The variable collection strategy used by @('aig-vars') is to memoize the
whole computation; this implicitly records, for every AND node, the exact set
of variables that are found under that node.  We use ordinary @(see osets) as
our variable set representation so that merging these sets is linear at each
node.  The overall complexity is then @('O(n^2)') in the size of the AIG.</p>

<p>This approach records the full variable information for every AND node
throughout the AIG.  This takes a lot of memory, and often you do not need
nearly this much information.  In practice, functions like @(see
aig-vars-1pass) are often much more practical.</p>"

  :verify-guards nil
  :enabled t
  (aig-cases x
    :true  nil
    :false nil
    :var   (mbe :logic (set::insert x nil)
                :exec (hons x nil))
    :inv   (aig-vars (car x))
    :and   (mbe :logic (set::union (aig-vars (car x))
                                    (aig-vars (cdr x)))
                :exec (hons-alphorder-merge (aig-vars (car x))
                                            (aig-vars (cdr x)))))
  ///
  (defthm atom-listp-aig-vars
    (atom-listp (aig-vars x)))

  (defthm true-listp-aig-vars
    (true-listp (aig-vars x))
    :rule-classes :type-prescription)

  (defthm setp-aig-vars
    (set::setp (aig-vars x))
    :hints(("Goal" :in-theory (enable* (:ruleset set::primitive-rules)))))

  (verify-guards aig-vars
    :hints(("Goal" :in-theory (enable* (:ruleset set::primitive-rules)))))

  (memoize 'aig-vars :condition '(and (consp x) (cdr x))))




; -----------------------------------------------------------------------------
;
;                              AIG CONSTRUCTION
;
; -----------------------------------------------------------------------------

(define aig-not (x)
  :parents (aig-constructors)
  :short "@(call aig-not) constructs an AIG representing @('(not x)')."
  :long "<p>This could be implemented as @('(hons x nil)'), but we at least
take care to fold constants and avoid creating double negatives.</p>"
  :returns aig
  (cond ((eq x nil) t)
        ((eq x t) nil)
        ((and (consp x) (eq (cdr x) nil))
         (car x))
        (t
         (hons x nil)))
  ///
  (defthm aig-eval-not
    (equal (aig-eval (aig-not x) env)
           (not (aig-eval x env)))))

(define aig-and (x y)
  :parents (aig-constructors)
  :short "@(call aig-and) constructs an AIG representing @('(and x y)')."
  :long "<p>This could have been implemented as @('(hons x y)'), but we take
care to fold constants and reduce @('x & x') and @('x & ~x').</p>"
  :returns aig
  (cond ((or (eq x nil) (eq y nil)) nil)
        ((eq x t) y)
        ((eq y t) x)
        ((hons-equal x y) x)
        ((and (consp y) (eq (cdr y) nil)
              (hons-equal (car y) x))
         nil)
        ((and (consp x) (eq (cdr x) nil)
              (hons-equal (car x) y))
         nil)
        (t (hons x y)))
  ///
  (defthm aig-eval-and
    (equal (aig-eval (aig-and x y) env)
           (and (aig-eval x env)
                (aig-eval y env))))
  (defthm aig-and-constants
    (and (equal (aig-and nil x) nil)
         (equal (aig-and x nil) nil)
         (equal (aig-and x t) x)
         (equal (aig-and t x) x))))

(define aig-or (x y)
  :parents (aig-constructors)
  :short "@(call aig-or) constructs an AIG representing @('(or x y)')."
  :returns aig
  (aig-not (aig-and (aig-not x) (aig-not y)))
  ///
  (defthm aig-eval-or
    (equal (aig-eval (aig-or x y) env)
           (or (aig-eval x env)
               (aig-eval y env)))))

(define aig-xor (x y)
  :parents (aig-constructors)
  :short "@(call aig-xor) constructs an AIG representing @('(xor x y)')."
  :returns aig
  (aig-or (aig-and x (aig-not y))
          (aig-and (aig-not x) y))
  ///
  (defthm aig-eval-xor
    (equal (aig-eval (aig-xor x y) env)
           (xor (aig-eval x env)
                (aig-eval y env)))))

(define aig-iff (x y)
  :parents (aig-constructors)
  :short "@(call aig-iff) constructs an AIG representing @('(iff x y)')."
  :returns aig
  (aig-or (aig-and x y)
          (aig-and (aig-not x) (aig-not y)))
  ///
  (defthm aig-eval-iff
    (equal (aig-eval (aig-iff x y) env)
           (iff (aig-eval x env)
                (aig-eval y env)))))

(define aig-implies (x y)
  :parents (aig-constructors)
  :short "@(call aig-implies) constructs an AIG representing @('(implies x
  y)')."
  :returns aig
  (aig-not (aig-and x (aig-not y)))
  ///
  (defthm aig-eval-implies
    (equal (aig-eval (aig-implies x y) env)
           (implies (aig-eval x env)
                    (aig-eval y env)))))

(define aig-ite (a b c)
  :parents (aig-constructors)
  :short "@(call aig-ite) constructs an AIG representing @('(if a b c)')."
  :returns aig
  (cond ((hons-equal b c)
         b)
        ((eq b t)
         (aig-or a c))
        (t
         (aig-or (aig-and a b)
                 (aig-and (aig-not a) c))))
  ///
  (defthm aig-eval-ite
    (iff (aig-eval (aig-ite a b c) env)
         (if (aig-eval a env)
             (aig-eval b env)
           (aig-eval c env)))))

(define aig-not-list (x)
  :parents (aig-constructors)
  :short "@(call aig-not-list) negates every AIG in the list @('x')."
  :returns aig-list
  :enabled t
  (if (atom x)
      nil
    (cons (aig-not (car X))
          (aig-not-list (cdr x)))))

(define aig-and-list (x)
  :parents (aig-constructors)
  :short "@(call aig-and-list) <i>and</i>s together all of the AIGs in the list
@('x')."
  :returns aig
  :enabled t
  (if (atom x)
      t
    (aig-and (car x)
             (aig-and-list (cdr x)))))

(define aig-or-list (x)
  :parents (aig-constructors)
  :short "@(call aig-or-list) <i>or</i>s together all of the AIGs in the list
@('x')."
  :returns aig
  :enabled t
  (if (atom x)
      nil
    (aig-or (car x) (aig-or-list (cdr x)))))

(define aig-and-lists (x y)
  :parents (aig-constructors)
  :short "@(call aig-and-lists) pairwise <i>and</i>s together the AIGs from the
lists @('x') and @('y')."
  :returns aig-list
  :enabled t
  (if (or (atom x) (atom y))
      nil
    (cons (aig-and (car x) (car y))
          (aig-and-lists (cdr x) (cdr y)))))

(define aig-or-lists (x y)
  :parents (aig-constructors)
  :short "@(call aig-or-lists) pairwise <i>or</i>s together the AIGs from the
lists @('x') and @('y')."
  :returns aig-list
  :enabled t
  (if (or (atom x) (atom y))
      nil
    (cons (aig-or (car x) (car y))
          (aig-or-lists (cdr x) (cdr y)))))

(define aig-iff-lists (x y)
  :parents (aig-constructors)
  :short "@(call aig-iff-lists) pairwise <i>iff</i>s together the AIGs from the
lists @('x') and @('y')."
  :returns aig-list
  :enabled t
  (if (or (atom x) (atom y))
      nil
    (cons (aig-iff (car x) (car y))
          (aig-iff-lists (cdr x) (cdr y)))))

(define aig-xor-lists (x y)
  :parents (aig-constructors)
  :short "@(call aig-xor-lists) pairwise <i>xor</i>s together the AIGs from the
lists @('x') and @('y')."
  :returns aig-list
  :enabled t
  (if (or (atom x) (atom y))
      nil
    (cons (aig-xor (car x) (car y))
          (aig-xor-lists (cdr x) (cdr y)))))

(define aig-implies-lists (x y)
  :parents (aig-constructors)
  :short "@(call aig-implies-lists) pairwise <i>implies</i> together the AIGs
from the lists @('x') and @('y')."
  :returns aig-list
  :enabled t
  (if (or (atom x) (atom y))
      nil
    (cons (aig-implies (car x) (car y))
          (aig-implies-lists (cdr x) (cdr y)))))

(def-ruleset aig-constructors
  '(aig-not
    aig-and
    aig-or
    aig-xor
    aig-iff
    aig-implies
    aig-ite
    aig-not-list
    aig-and-list
    aig-or-list
    aig-and-lists
    aig-or-lists
    aig-iff-lists
    aig-xor-lists
    aig-implies-lists))

; -----------------------------------------------------------------------------
;
;                         SUBSTITUTION INTO AIGS
;
; -----------------------------------------------------------------------------

(define aig-restrict
  :parents (aig-substitution)
  :short "@(call aig-restrict) performs variable substitution throughout the
AIG @('x'), replacing any variables bound in @('sigma') with their
corresponding values."
  ((x     "The AIG to restrict.")
   (sigma "A fast alist binding variables to replacement AIGs."))
  :returns
  (aig "Modified version of @('x') where all variables bound in @('sigma') are
replaced, and any unmentioned variables are left <b>unchanged</b>.")

  :long "<p>The name @('sigma') is intended to evoke the notion of substitution
lists in logic.  Any variables that are not mentioned in @('sigma') are left
unchanged.  When all of the variables in @('x') are bound in @('sigma'), and
all of the values are Boolean, this is equivalent to @(see aig-eval).</p>

<p>This function is @(see memoize)d.  You should typically free its memo table
after you are done with whatever @('sigma') you are using, to avoid excessive
memory usage.  (We don't use @(':forget t') because you often want to restrict
several related AIGs.)</p>"

  :enabled t

  (aig-cases x
    :true t
    :false nil
    :var (let ((a (hons-get x sigma)))
           (if a
               (cdr a)
             x))
    :inv (aig-not (aig-restrict (car x) sigma))
    :and (let ((a (aig-restrict (car x) sigma)))
           (and a (aig-and a (aig-restrict (cdr x) sigma)))))
  ///
  (memoize 'aig-restrict :condition '(and (consp x) (cdr x)))

  (local (defthm hons-assoc-equal-of-append
           (equal (hons-assoc-equal k (append a b))
                  (or (hons-assoc-equal k a)
                      (hons-assoc-equal k b)))))

  (defthm aig-eval-of-aig-restrict
    (equal (aig-eval (aig-restrict x al1) al2)
           (aig-eval x (append (aig-eval-alist al1 al2) al2)))
    :hints(("Goal"
            :induct t
            :in-theory (enable aig-env-lookup)))))

(define aig-restrict-list
  :parents (aig-substitution)
  :short "@(call aig-restrict-list) substitutes into a list of AIGs."
  ((x     "List of AIGs.")
   (sigma "Fast alist binding variables to replacement AIGs, as in @(see
           aig-restrict)."))
  :returns aig-list
  :enabled t
  (if (atom x)
      nil
    (cons (aig-restrict (car x) sigma)
          (aig-restrict-list (cdr x) sigma))))

(define aig-restrict-alist
  :parents (aig-substitution)
  :short "@(call aig-restrict-alist) substitutes into an AIG Alist (an alist
binding keys to AIGs)."
  ((x     "Alist binding names to AIGs.  This doesn't need to be a fast alist.")
   (sigma "Fast alist binding variables to replacement AIGs, as in @(see
           aig-restrict)."))
  :returns
  (aig-alist "Ordinary (slow) alist with the same keys as @('x'), and values
              formed by restricting each aig with @(see aig-restrict).")
  :enabled t
  (cond ((atom x)
         nil)
        ((atom (car x))
         ;; Bad-alist convention
         (aig-restrict-alist (cdr x) sigma))
        (t
         (cons (cons (caar x)
                     (aig-restrict (cdar x) sigma))
               (aig-restrict-alist (cdr x) sigma))))
  ///
  (defthm alistp-of-aig-restrict-alist
    (alistp (aig-restrict-alist x sigma))))

(define aig-restrict-alists
  :parents (aig-substitution)
  :short "@(call aig-restrict-alists) substitutes into a list of AIG Alists."
  ((x     "List of AIG alists, which need not be fast.")
   (sigma "Fast alist binding variables to replacement AIGs, as in @(see
           aig-restrict)."))
  :returns
  (aig-alists "List of ordinary (slow) alists, derived from @('x') via
               @(see aig-restrict-alist).")
  :enabled t
  (if (atom x)
      nil
    (cons (aig-restrict-alist (car x) sigma)
          (aig-restrict-alists (cdr x) sigma))))



; -----------------------------------------------------------------------------
;
;                             AIG COMPOSITION
;
; -----------------------------------------------------------------------------

(define aig-compose
  :parents (aig-substitution)
  :short "@(call aig-compose) performs variable substitution throughout the AIG
@('x'), <b>unconditionally</b> replacing every variable in @('x') with its
binding in @('sigma')."
  ((x     "The AIG to compose into.")
   (sigma "A fast alist that should bind variables to replacement AIGs."))
  :returns
  (aig "Modified version of @('x') where every variable is replaced with its
        binding in @('sigma') or @('t') if it has no binding.")

  :long "<p>The name @('sigma') is intended to evoke the notion of substitution
lists in logic.  This operation is similar to @(see aig-restrict), except that
whereas @('aig-restrict') leaves unbound variables alone, @('aig-compose')
replaces them with @('t').  This has the logically nice property that the
variables after composition are just the variables in the AIGs of
@('sigma').</p>

<p>This function is @(see memoize)d.  You should typically free its memo table
after you are done with whatever @('sigma') you are using, to avoid excessive
memory usage.  (We don't use @(':forget t') because you often want to compose
several related AIGs.)</p>"

  :enabled t

  (aig-cases x
    :true t
    :false nil
    :var (aig-env-lookup x sigma)
    :inv (aig-not (aig-compose (car x) sigma))
    :and (let ((a (aig-compose (car x) sigma)))
           (and a (aig-and a (aig-compose (cdr x) sigma)))))
  ///
  (memoize 'aig-compose :condition '(and (consp x) (cdr x))))

(define aig-compose-list
  :parents (aig-substitution)
  :short "@(call aig-compose-list) composes into a list of AIGs."
  ((x     "List of AIGs.")
   (sigma "Fast alist binding variables to replacement AIGs, as in @(see
           aig-compose)."))
  :returns aig-list
  :enabled t
  (if (atom x)
      nil
    (cons (aig-compose (car x) sigma)
          (aig-compose-list (cdr x) sigma))))

(define aig-compose-alist
  :parents (aig-substitution)
  :short "@(call aig-compose-alist) composes into an AIG Alist (an alist
binding keys to AIGs)."
  ((x     "Alist binding names to AIGs.  This doesn't need to be a fast alist.")
   (sigma "Fast alist binding variables to replacement AIGs, as in @(see
           aig-compose)."))
  :returns
  (aig-alist "Ordinary (slow) alist with the same keys as @('x'), and values formed
              by restricting each aig with @(see aig-compose).")
  :enabled t
  (cond ((atom x)
         nil)
        ((atom (car x))
         ;; Bad alist convention
         (aig-compose-alist (cdr x) sigma))
        (t
         (cons (cons (caar x)
                     (aig-compose (cdar x) sigma))
               (aig-compose-alist (cdr x) sigma)))))

(define aig-compose-alists
  :parents (aig-substitution)
  :short "@(call aig-compose-alists) composes into a list of AIG Alists."
  ((x     "List of AIG alists, which need not be fast.")
   (sigma "Fast alist binding variables to replacement AIGs, as in @(see
           aig-compose)."))
  :returns
  (aig-alists "List of ordinary (slow) alists, derived from @('x') via @(see
               aig-compose-alist).")
  :enabled t
  (if (atom x)
      nil
    (cons (aig-compose-alist (car x) sigma)
          (aig-compose-alists (cdr x) sigma))))



; -----------------------------------------------------------------------------
;
;                      PARTIALLY EVALUATING AIGS
;
; -----------------------------------------------------------------------------

(define aig-partial-eval
  :parents (aig-substitution)
  :short "@(call aig-partial-eval) evaluates @('x'), an AIG, under the partial
environment @('env'), producing a new AIG as a result."
  ((x   "The AIG to partially evaluate.")
   (env "A fast alist that (typically) binds some of the variables in @('x') to
         Boolean values."))
  :returns
  (aig "Modified version of @('x') obtained by replacing bound variables with their
        values and doing basic constant propagation.")

  :long "<p>In ordinary AIG evaluation with @(see aig-eval), any variables that
are missing from @('env') are just assumed to have a default value.  Because of
this, every variable can be given a Boolean value and we can evaluate the whole
AIG to produce a Boolean result.</p>

<p>In partial evaluation, variables that aren't bound in @('env') are left
alone.  Because of this, the result of a partial evaluation is a typically a
reduced AIG instead of a Boolean.</p>

<p>Another way to do partial evaluations is with @(see aig-restrict).  In fact,
the only difference between @('aig-restrict') and @('aig-partial-eval') is that
@('aig-partial-eval') Boolean-fixes the values in the alist as it looks them
up.  This has logically nice properties, e.g., since we never replace a
variable by a subtree, only by a Boolean, we know unconditionally that the
variables of the resulting AIG are a subset of the variables of the
original.</p>

<p>This function is @(see memoize)d.  You should typically free its memo table
after you are done with whatever @('env') you are using, to avoid excessive
memory usage.  (We don't use @(':forget t') because you often want to evaluate
several related AIGs.)</p>"

  :enabled t
  (aig-cases x
    :true t
    :false nil
    :var (let ((a (hons-get x env)))
           (if a (and (cdr a) t) x))
    :inv (aig-not (aig-partial-eval (car x) env))
    :and (let ((a (aig-partial-eval (car x) env)))
           (and a
                (aig-and a (aig-partial-eval (cdr x) env)))))
  ///
  (memoize 'aig-partial-eval :condition '(and (consp x) (cdr x))))

(define aig-partial-eval-list
  :parents (aig-substitution)
  :short "@(call aig-partial-eval-list) partially evaluates a list of AIGs."
  ((x   "List of AIGs.")
   (env "Fast alist binding variables to Booleans, as in @(see
         aig-partial-eval)."))
  :returns aig-list
  :enabled t
  (if (atom x)
      nil
    (cons (aig-partial-eval (car x) env)
          (aig-partial-eval-list (cdr x) env))))

(define aig-partial-eval-alist
  :parents (aig-substitution)
  :short "@(call aig-partial-eval-alist) partially evaluates an AIG Alist (an
alist binding keys to AIGs)."
  ((x   "Alist binding names to AIGs.  This doesn't need to be a fast alist.")
   (env "Fast alist binding variables to Booleans, as in @(see
         aig-partial-eval)."))
  :returns
  (aig-alist "Ordinary (slow) alist with the same keys as x, and values formed
              by restricting each aig with @(see aig-partial-eval).")
  :enabled t
  (cond ((atom x)
         nil)
        ((atom (car x))
         ;; Bad-alist convention
         (aig-partial-eval-alist (cdr x) env))
        (t
         (cons (cons (caar x)
                     (aig-partial-eval (cdar x) env))
               (aig-partial-eval-alist (cdr x) env))))
  ///
  (defthm alistp-of-aig-partial-eval-alist
    (alistp (aig-partial-eval-alist x env))))

