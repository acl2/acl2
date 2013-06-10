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
(include-book "xdoc/top" :dir :system)
(include-book "../misc/hons-alphorder-merge")

; aig/base.lisp
;   - Semantics of AIGs (aig-eval) and FAIGs (faig-eval)
;   - Primitive AIG constructors (aig-not, aig-and, ...)
;   - Substitution operations: aig-restrict, aig-compose, aig-partial-eval
;   - FAIG versions of the substitution operations


; BOZO consider using defprojection throughout?

(defxdoc aig
  :short "Centaur AIG Library"

  :long "<p><b>AIGs</b> (And/Inverter Graphs) are a representation of Boolean
functions, using only <i>and</i> and <i>not</i> operations.</p>

<p><b><see topic='@(url faig)'>FAIGs</see></b> (Four-valued AIGs) are a related
concept, where two AIGs are pasted together to represent a function in
four-valued logic.</p>


<h3>Motivation for AIGs</h3>

<p>There are many ways to represent Boolean functions.  One alternative is
to use BDDs, e.g., we provide a @(see ubdds) library.  In comparison with
BDDs, AIGs are:</p>

<ul>

<li>cheaper to construct, e.g., if we want to <i>or</i> together the functions
@('f') and @('g'), it only takes a few conses with AIGs, whereas with BDDs we
need to walk through @('f') and @('g') to construct a new structure (which
might be quite large); but</li>

<li>more expensive to compare, e.g., with BDDs we can determine if @('f') and
@('g') are equal via pointer equality, whereas with AIGs this is a
satisfiablity problem.</li>

</ul>

<p>This tradeoff is often worth it because you can simplify and reduce AIGs
after they have been constructed, but before comparing them.  For instance, our
@(see bddify) algorithm converts an AIG into a BDD, and since it can often
\"prune\" branches of the AIG that turn out to be irrelevant, it can be much
more efficient than directly constructing BDDs.  A more sophisticated tool is
@(see abc), which provides various kinds of rewriting and reductions on AIGs.
These reductions can be used before calling a SAT solver or @('bddify') to make
the input AIGs much smaller and easier to process.</p>

<p>Another alternative would be to use a richer language such as Lisp-style
s-expressions, where operations other than <i>and</i> and <i>not</i> could be
used directly.  On the surface, this approach would appear to be more compact,
e.g., we can represent @('(or a b)') as a single operation instead of as
something like @('(not (and (not a) (not b)))').</p>

<p>But another critical part of memory efficiency is structure sharing.  That
is, suppose that we already need @('(not a)') and @('(not b)') elsewhere in the
function.  With s-expressions, these terms would have nothing in common with
@('(or a b)'), but with AIGs we can reuse the existing parts of
@('(not (and (not a) (not b)))').</p>


<h3>Representation of AIGs</h3>

<p>We always construct AIGs with @(see hons) so that existing pieces of AIGs
will be automatically reused.  We represent AIGs as arbitrary cons trees, which
we interpret as follows:</p>

<ul>

<li>@('T') represents the constant-true function.</li>

<li>@('NIL') represents the constant-false function.</li>

<li>Any other atom represents a Boolean variable (i.e., an input to the
function.)</li>

<li>A cons of the form @('(A . NIL)') represents the negation of @('A').</li>

<li>Any other cons, @('(A . B)'), represents the conjunction of @('A') and
@('B').</li>

</ul>

<p>This meaning of cons trees is given by the evaluation function @(see
aig-eval), which returns the (Boolean) value of an AIG under some particular
assignment to its variables.  Note that every ACL2 object is a well-formed AIG
under this definition.</p>


<h3>Library Functions</h3>

<p>We provide some basic, low-level @(see aig-constructors) for building
AIGs (<i>and</i>, <i>or</i>, etc.).  We prove these operations correct with
respect to @(see aig-eval).</p>

<p>There are also higher-level operations such as @(see aig-restrict) and @(see
aig-compose) allow you to substitute into AIGs.</p>

<p>It is often important to know which variables occur in an AIG.  One way to
do this is with @(see aig-vars).</p>

<p>The @(see bddify) algorithm provides a way to construct a BDD from an AIG.
This is also used as the basis for an efficient @(see GL) symbolic counterpart
of @(see aig-eval).</p>

<p>BOZO other things that we haven't released yet.</p>")



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
  :short "Configure warnings about missing variables in AIG evaluation."

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


;;(defsection aig-cases
;;  :parents (aig)
;;  :short "Control-flow macro to split into cases on what kind of AIG you have
;;encountered."
;;  :long "@(def aig-cases)"

;;  (defmacro aig-cases (x &key true false var inv and)
;;    `(let ((aig-cases-var ,x))
;;       (cond
;;        ((eq aig-cases-var t) ,true)
;;        ((eq aig-cases-var nil) ,false)
;;        ((atom aig-cases-var) ,var)
;;        ((eq (cdr aig-cases-var) nil) ,inv)
;;        (t ,and)))))

(defsection aig-cases
  :parents (aig)
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



(defsection aig-eval
  :parents (aig)
  :short "@(call aig-eval) evaluates @('x'), an @(see aig), under the
environment @('env'), producing a Boolean result."

  :long "<p>The @('env') should be a fast alist (see @(see fast-alists)) that
binds variables in the AIG to values.  Typically it should bind every variable
in the AIG to a Boolean value.</p>

<p>This function is @(see memoize)d.  You should typically free its memo table
after you are done with whatever @('env') you are using, to avoid excessive
memory usage.  (We don't use @(':forget t') because you often want to evaluate
several related AIGs.)</p>

<p>Unbound variables are given the default value @('t') instead of @('nil')
because this makes theorems about @(see faig) evaluation work out more
nicely (it makes unbound FAIG variables evaluate to @('X')).</p>

<p>This function essentially defines the semantics of AIGs.</p>"

  ;; [Jared] BOZO it might be good to add a check that the variables are indeed
  ;; bound to Booleans.

  (defun aig-env-lookup (x env)
    (declare (xargs :guard t))
    (let ((look (hons-get x env)))
      (if look
          ;; [Jared] I was once tempted to change this to produce an always
          ;; Boolean result, since it would seem nicer to do that here than in
          ;; aig-eval.  But this function is also used in AIG-COMPOSE, and it
          ;; is not valid to Boolean-fix it there.
          (cdr look)
        (mbe :logic t
             :exec
             (if *aig-env-lookup-warn-missing-binding*
                 (prog2$ (aig-env-lookup-missing-output x)
                         t)
               t)))))

  (defun aig-eval (x env)
    (declare (xargs :guard t))
    (aig-cases x
               :true t
               :false nil
               :var (and (aig-env-lookup x env) t)
               :inv (not (aig-eval (car x) env))
               :and (and (aig-eval (car x) env)
                         (aig-eval (cdr x) env))))

  ;; [Jared] note, changed memoization condition from just (consp x) to exclude
  ;; not nodes; this matches aig-vars and I think is probably what we want.
  (memoize 'aig-eval :condition '(and (consp x) (cdr x))))


(defsection aig-eval-list
  :parents (aig-eval)
  :short "@(call aig-eval-list) evaluates a list of AIGs."

  ;; BOZO formal is named benv right now, eventually rename to env but we need
  ;; to patch up GL so it doesn't care about formals named env.
  (defun aig-eval-list (x benv)
    (declare (xargs :guard t))
    (if (atom x)
        nil
      (cons (aig-eval (car x) benv)
            (aig-eval-list (cdr x) benv)))))


(defsection aig-eval-alist
  :parents (aig-eval)
  :short "@(call aig-eval-alist) evaluates an AIG Alist (an alist binding keys
to AIGs)."

  :long "<p>The alist @('x') does not need to be fast, and we produce an
ordinary (slow) alist as a result.</p>"

  (defun aig-eval-alist (x env)
    (declare (xargs :guard t))
    (cond ((atom x)
           nil)
          ((atom (car x))
           ;; Bad-alist convention
           (aig-eval-alist (cdr x) env))
          (t
           (cons (cons (caar x) (aig-eval (cdar x) env))
                 (aig-eval-alist (cdr x) env))))))



(defsection aig-eval-alists
  :parents (aig-eval)
  :short "Evaluate a list of AIG Alists."

  (defun aig-eval-alists (x env)
    (declare (xargs :guard t))
    (if (atom x)
        nil
      (cons (aig-eval-alist (car x) env)
            (aig-eval-alists (cdr x) env)))))




; -----------------------------------------------------------------------------
;
;                        COLLECTING AIG VARIABLES
;
; -----------------------------------------------------------------------------

(defsection aig-vars
  :parents (aig)
  :short "@(call aig-vars) returns the list of variables used in the AIG
@('X')."

;; BOZO the :long here refers to the unreleased sexpr library, but I don't want
;; to redo all that documentation for AIGs.

  :long "<p>This is one scheme for collecting variables from an AIG.  We
memoize the whole computation and return ordered lists so that merging is
linear.  This can be very expensive.  See @(see 4v-sexpr-vars) for an analagous
discussion.</p>"

  (defun aig-vars (x)
    (declare (xargs :guard t
                    :verify-guards nil))
    (aig-cases x
               :true  nil
               :false nil
               :var   (mbe :logic (sets::insert x nil)
                           :exec (hons x nil))
               :inv   (aig-vars (car x))
               :and   (mbe :logic (sets::union (aig-vars (car x))
                                               (aig-vars (cdr x)))
                           :exec (hons-alphorder-merge (aig-vars (car x))
                                                       (aig-vars (cdr x))))))

  (defthm atom-listp-aig-vars
    (atom-listp (aig-vars x)))

  (defthm true-listp-aig-vars
    (true-listp (aig-vars x))
    :rule-classes :type-prescription)

  (defthm setp-aig-vars
    (sets::setp (aig-vars x))
    :hints(("Goal" :in-theory (enable* (:ruleset sets::primitive-rules)))))

  (verify-guards aig-vars
    :hints(("Goal" :in-theory (enable* (:ruleset sets::primitive-rules)))))

  (memoize 'aig-vars :condition '(and (consp x) (cdr x))))




; -----------------------------------------------------------------------------
;
;                              AIG CONSTRUCTION
;
; -----------------------------------------------------------------------------

(defxdoc aig-constructors
  :parents (aig)
  :short "Low-level functions for constructing AIGs.")



(defsection aig-not
  :parents (aig-constructors)
  :short "@(call aig-not) constructs an AIG representing @('(not x)')."

  :long "<p>This could be implemented as @('(hons x nil)'), but we at least
take care to fold constants and avoid creating double negatives.</p>"

  (defund aig-not (x)
    (declare (xargs :guard t))
    (cond ((eq x nil) t)
          ((eq x t) nil)
          ((and (consp x) (eq (cdr x) nil))
           (car x))
          (t
           (hons x nil))))

  (local (in-theory (enable aig-not)))

  (defthm aig-eval-not
    (equal (aig-eval (aig-not x) env)
           (not (aig-eval x env)))))



(defsection aig-and
  :parents (aig-constructors)
  :short "@(call aig-and) constructs an AIG representing @('(and x y)')."

  :long "<p>This could have been implemented as @('(hons x y)'), but we take
care to fold constants and reduce @('x & x') and @('x & ~x').</p>"

  (defund aig-and (x y)
    (declare (xargs :guard t))
    (cond
     ((or (eq x nil) (eq y nil)) nil)
     ((eq x t) y)
     ((eq y t) x)
     ((hons-equal x y) x)
     ((and (consp y) (eq (cdr y) nil)
           (hons-equal (car y) x))
      nil)
     ((and (consp x) (eq (cdr x) nil)
           (hons-equal (car x) y))
      nil)
     (t (hons x y))))

  (local (in-theory (enable aig-and)))

  (defthm aig-eval-and
    (equal (aig-eval (aig-and x y) env)
           (and (aig-eval x env)
                (aig-eval y env))))

  (defthm aig-and-constants
    (and (equal (aig-and nil x) nil)
         (equal (aig-and x nil) nil)
         (equal (aig-and x t) x)
         (equal (aig-and t x) x))))



(defsection aig-or
  :parents (aig-constructors)
  :short "@(call aig-or) constructs an AIG representing @('(or x y)')."

  (defund aig-or (x y)
    (declare (xargs :guard t))
    (aig-not (aig-and (aig-not x) (aig-not y))))

  (local (in-theory (enable aig-or)))

  (defthm aig-eval-or
    (equal (aig-eval (aig-or x y) env)
           (or (aig-eval x env)
               (aig-eval y env)))))



(defsection aig-xor
  :parents (aig-constructors)
  :short "@(call aig-xor) constructs an AIG representing @('(xor x y)')."

  (defund aig-xor (x y)
    (declare (xargs :guard t))
    (aig-or (aig-and x (aig-not y))
            (aig-and (aig-not x) y)))

  (local (in-theory (enable aig-xor)))

  (defthm aig-eval-xor
    (equal (aig-eval (aig-xor x y) env)
           (xor (aig-eval x env)
                (aig-eval y env)))))



(defsection aig-iff
  :parents (aig-constructors)
  :short "@(call aig-iff) constructs an AIG representing @('(iff x y)')."

  (defund aig-iff (x y)
    (declare (xargs :guard t))
    (aig-or (aig-and x y)
            (aig-and (aig-not x) (aig-not y))))

  (local (in-theory (enable aig-iff)))

  (defthm aig-eval-iff
    (equal (aig-eval (aig-iff x y) env)
           (iff (aig-eval x env)
                (aig-eval y env)))))



(defsection aig-implies
  :parents (aig-constructors)
  :short "@(call aig-implies) constructs an AIG representing @('(implies x
  y)')."

  (defund aig-implies (x y)
    (declare (xargs :guard t))
    (aig-not (aig-and x (aig-not y))))

  (local (in-theory (enable aig-implies)))

  (defthm aig-eval-implies
    (equal (aig-eval (aig-implies x y) env)
           (implies (aig-eval x env)
                    (aig-eval y env)))))



(defsection aig-ite
  :parents (aig-constructors)
  :short "@(call aig-ite) constructs an AIG representing @('(if a b c)')."

  (defund aig-ite (a b c)
    (declare (xargs :guard t))
    (cond ((hons-equal b c)
           b)
          ((eq b t)
           (aig-or a c))
          (t
           (aig-or (aig-and a b)
                   (aig-and (aig-not a) c)))))

  (local (in-theory (enable aig-ite)))

  (defthm aig-eval-ite
    (iff (aig-eval (aig-ite a b c) env)
         (if (aig-eval a env)
             (aig-eval b env)
           (aig-eval c env)))))


(defsection aig-not-list
  :parents (aig-constructors)
  :short "@(call aig-not-list) negates every AIG in the list @('x')."

  (defun aig-not-list (x)
    (declare (xargs :guard t))
    (if (atom x)
        nil
      (cons (aig-not (car X))
            (aig-not-list (cdr x))))))


(defsection aig-and-list
  :parents (aig-constructors)
  :short "@(call aig-and-list) ands together all of the AIGs in the list
@('x')."

  (defun aig-and-list (x)
    (declare (xargs :guard t))
    (if (atom x)
        t
      (aig-and (car x)
               (aig-and-list (cdr x))))))


(defsection aig-or-list
  :parents (aig-constructors)
  :short "@(call aig-or-list) ors together all of the AIGs in the list @('x')."

  (defun aig-or-list (x)
    (declare (xargs :guard t))
    (if (atom x)
        nil
      (aig-or (car x) (aig-or-list (cdr x))))))


(defsection aig-and-lists
  :parents (aig-constructors)
  :short "@(call aig-and-lists) pairwise <i>and</i>s together the AIGs from the
lists @('x') and @('y')."

  (defun aig-and-lists (x y)
    (if (or (atom x) (atom y))
        nil
      (cons (aig-and (car x) (car y))
            (aig-and-lists (cdr x) (cdr y))))))


(defsection aig-or-lists
  :parents (aig-constructors)
  :short "@(call aig-or-lists) pairwise <i>or</i>s together the AIGs from the
lists @('x') and @('y')."

  (defun aig-or-lists (x y)
    (declare (xargs :guard t))
    (if (or (atom x) (atom y))
        nil
      (cons (aig-or (car x) (car y))
            (aig-or-lists (cdr x) (cdr y))))))


(defsection aig-iff-lists
  :parents (aig-constructors)
  :short "@(call aig-iff-lists) pairwise <i>iff</i>s together the AIGs from the
lists @('x') and @('y')."

  (defun aig-iff-lists (x y)
    (declare (xargs :guard t))
    (if (or (atom x) (atom y))
        nil
      (cons (aig-iff (car x) (car y))
            (aig-iff-lists (cdr x) (cdr y))))))


(defsection aig-xor-lists
  :parents (aig-constructors)
  :short "@(call aig-xor-lists) pairwise <i>xor</i>s together the AIGs from the
lists @('x') and @('y')."

  (defun aig-xor-lists (x y)
    (declare (xargs :guard t))
    (if (or (atom x) (atom y))
        nil
      (cons (aig-xor (car x) (car y))
            (aig-xor-lists (cdr x) (cdr y))))))


(defsection aig-implies-lists
  :parents (aig-constructors)
  :short "@(call aig-implies-lists) pairwise <i>implies</i> together the AIGs
from the lists @('x') and @('y')."

  (defun aig-implies-lists (x y)
    (declare (xargs :guard t))
    (if (or (atom x) (atom y))
        nil
      (cons (aig-implies (car x) (car y))
            (aig-implies-lists (cdr x) (cdr y))))))




; -----------------------------------------------------------------------------
;
;                         SUBSTITUTION INTO AIGS
;
; -----------------------------------------------------------------------------

(defsection aig-restrict
  :parents (aig)
  :short "@(call aig-restrict) performs variable substitution throughout the
AIG @('x'), replacing any variables bound in @('sigma') with their
corresponding values."

  :long "<p>@('sigma') should be a fast alist; its name is intended to evoke
the notion of substitution lists in logic.  Any variables that are not
mentioned in @('sigma') are left unchanged.</p>

<p>This function is @(see memoize)d.  You should typically free its memo table
after you are done with whatever @('sigma') you are using, to avoid excessive
memory usage.  (We don't use @(':forget t') because you often want to restrict
several related AIGs.)</p>

<p>When all of the variables in @('x') are bound in @('sigma'), and all of the
values are Boolean, this is equivalent to @(see aig-eval).</p>

<p>Some related functions are @(see aig-compose) and @(see
aig-partial-eval).</p>"

  (defun aig-restrict (x sigma)
    (declare (xargs :guard t))
    (aig-cases x
               :true t
               :false nil
               :var (let ((a (hons-get x sigma)))
                      (if a
                          (cdr a)
                        x))
               :inv (aig-not (aig-restrict (car x) sigma))
               :and (let ((a (aig-restrict (car x) sigma)))
                      (and a (aig-and a (aig-restrict (cdr x) sigma))))))

  (memoize 'aig-restrict :condition '(and (consp x) (cdr x))))


(defsection aig-restrict-list
  :parents (aig-restrict)
  :short "@(call aig-restrict-list) substitutes into a list of AIGs."

  (defun aig-restrict-list (x sigma)
    (declare (xargs :guard t))
    (if (atom x)
        nil
      (cons (aig-restrict (car x) sigma)
            (aig-restrict-list (cdr x) sigma)))))


(defsection aig-restrict-alist
  :parents (aig-restrict)
  :short "@(call aig-restrict-alist) substitutes into an AIG Alist (an alist
binding keys to AIGs)."

  :long "<p>The alist @('x') does not need to be fast, and we produce an
ordinary (slow) alist as a result.</p>"

  (defun aig-restrict-alist (x sigma)
    (declare (xargs :guard t))
    (cond ((atom x)
           nil)
          ((atom (car x))
           ;; Bad-alist convention
           (aig-restrict-alist (cdr x) sigma))
          (t
           (cons (cons (caar x)
                       (aig-restrict (cdar x) sigma))
                 (aig-restrict-alist (cdr x) sigma)))))

  (defthm alistp-of-aig-restrict-alist
    (alistp (aig-restrict-alist x sigma))))


(defsection aig-restrict-alists
  :parents (aig-restrict)
  :short "@(call aig-restrict-alists) substitutes into a list of AIG Alists."

  (defun aig-restrict-alists (x sigma)
    (declare (xargs :guard t))
    (if (atom x)
        nil
      (cons (aig-restrict-alist (car x) sigma)
            (aig-restrict-alists (cdr x) sigma)))))




; -----------------------------------------------------------------------------
;
;                             AIG COMPOSITION
;
; -----------------------------------------------------------------------------

(defsection aig-compose
  :parents (aig)
  :short "@(call aig-compose) performs variable substitution throughout the AIG
@('x'), <b>unconditionally</b> replacing every variable in @('x') with its
binding in @('sigma')."

  :long "<p>@('sigma') should be a fast alist; its name is intended to evoke
the notion of substitution lists in logic.</p>

<p>This function is @(see memoize)d.  You should typically free its memo table
after you are done with whatever @('sigma') you are using, to avoid excessive
memory usage.  (We don't use @(':forget t') because you often want to compose
several related AIGs.)</p>

<p>This operation is similar to @(see aig-restrict), except that whereas
@('aig-restrict') leaves unbound variables alone, @('aig-compose') replaces
them with @('t').  (This has the logically nice property that the variables
after composition are just the variables in the AIGs of @('sigma').)</p>"

  (defun aig-compose (x sigma)
    (declare (xargs :guard t))
    (aig-cases x
               :true t
               :false nil
               :var (aig-env-lookup x sigma)
               :inv (aig-not (aig-compose (car x) sigma))
               :and (let ((a (aig-compose (car x) sigma)))
                      (and a (aig-and a (aig-compose (cdr x) sigma))))))

  (memoize 'aig-compose :condition '(and (consp x) (cdr x))))


(defsection aig-compose-list
  :parents (aig-compose)
  :short "@(call aig-compose-list) composes into a list of AIGs."

  (defun aig-compose-list (x sigma)
    (declare (xargs :guard t))
    (if (atom x)
        nil
      (cons (aig-compose (car x) sigma)
            (aig-compose-list (cdr x) sigma)))))


(defsection aig-compose-alist
  :parents (aig-compose)
  :short "@(call aig-compose-alist) composes into an AIG Alist (an alist
binding keys to AIGs)."

  :long "<p>The alist @('x') does not need to be fast, and we produce an
ordinary (slow) alist as a result.</p>"

  (defun aig-compose-alist (x sigma)
    (declare (xargs :guard t))
    (cond ((atom x)
           nil)
          ((atom (car x))
           ;; Bad alist convention
           (aig-compose-alist (cdr x) sigma))
          (t
           (cons (cons (caar x)
                       (aig-compose (cdar x) sigma))
                 (aig-compose-alist (cdr x) sigma))))))


(defsection aig-compose-alists
  :parents (aig-compose)
  :short "@(call aig-compose-alists) composes into a list of AIG Alists."

  (defn aig-compose-alists (x sigma)
    (if (atom x)
        nil
      (cons (aig-compose-alist (car x) sigma)
            (aig-compose-alists (cdr x) sigma)))))



; -----------------------------------------------------------------------------
;
;                      PARTIALLY EVALUATING AIGS
;
; -----------------------------------------------------------------------------

(defsection aig-partial-eval
  :parents (aig)
  :short "@(call aig-partial-eval) evaluates @('x'), an AIG, under the partial
environment @('env'), producing a new AIG as a result."

  :long "<p>@('env') should be a fast alist that binds some of the variables in
the AIG to Boolean values.</p>

<p>This function is @(see memoize)d.  You should typically free its memo table
after you are done with whatever @('env') you are using, to avoid excessive
memory usage.  (We don't use @(':forget t') because you often want to evaluate
several related AIGs.)</p>

<p>In ordinary AIG evaluation with @(see aig-eval), any variables that are
missing from @('env') are just assumed to have a default value.  Because of
this, every variable can be given a Boolean value and we can evaluate the whole
AIG to produce a Boolean result.</p>

<p>In partial evaluation, variables that aren't bound in @('env') are left
alone.  Because of this, the result of a partial evaluation is a
new (presumably smaller) AIG, instead of a Boolean.</p>

<p>Another way to do partial evaluations is with @(see aig-restrict).  The only
difference between @('aig-restrict') and @('aig-partial-eval') is that
@('aig-partial-eval') Boolean-fixes the values in the alist as it looks them
up.  This has logically nice properties, e.g., since we never replace a
variable by a subtree, only by a Boolean, we know unconditionally that the
variables of the resulting AIG are a subset of the variables of the
original.</p>"

  (defun aig-partial-eval (x env)
    (declare (xargs :guard t))
    (aig-cases x
               :true t
               :false nil
               :var (let ((a (hons-get x env)))
                      (if a (and (cdr a) t) x))
               :inv (aig-not (aig-partial-eval (car x) env))
               :and (let ((a (aig-partial-eval (car x) env)))
                      (and a
                           (aig-and a (aig-partial-eval (cdr x) env))))))

  ;; [Jared] note: this had no memoize condition, so I added the usual one.

  (memoize 'aig-partial-eval :condition '(and (consp x) (cdr x))))


(defsection aig-partial-eval-list
  :parents (aig-partial-eval)
  :short "@(call aig-partial-eval-list) partially evaluates a list of AIGs."

  (defun aig-partial-eval-list (x env)
    (declare (xargs :guard t))
    (if (atom x)
        nil
      (cons (aig-partial-eval (car x) env)
            (aig-partial-eval-list (cdr x) env)))))


(defsection aig-partial-eval-alist
  :parents (aig-partial-eval)
  :short "@(call aig-partial-eval-alist) partially evaluates an AIG Alist (an
alist binding keys to AIGs)."

  :long "<p>The alist @('x') does not need to be fast, and we produce an
ordinary (slow) alist as a result.</p>"

  (defun aig-partial-eval-alist (x env)
    (declare (xargs :guard t))
    (cond ((atom x)
           nil)
          ((atom (car x))
           ;; Bad-alist convention
           (aig-partial-eval-alist (cdr x) env))
          (t
           (cons (cons (caar x)
                       (aig-partial-eval (cdar x) env))
                 (aig-partial-eval-alist (cdr x) env)))))

  (defthm alistp-of-aig-partial-eval-alist
    (alistp (aig-partial-eval-alist x env))))




; -----------------------------------------------------------------------------
;
;                       FOUR-VALUED AIG OPERATIONS
;
; -----------------------------------------------------------------------------

; [Jared] it would be nice to move the FAIG stuff out into a separate file.

(defxdoc faig
  :short "A representation of a four-valued function using two AIGs."

  :long "<p>A <b>FAIG</b> (Four-valued AIG) combines two @(see aig)s together
to represent a function with four possible values.  Such functions can be
useful in hardware verification.</p>

<p>We represent an FAIG as the cons of two AIGs, which are called the
<i>onset</i> and <i>offset</i> of the FAIG.  Our FAIG evaluation function,
@(see faig-eval), just evaluates these two AIGs, separately, using ordinary
@(see aig-eval), and conses together the resulting Boolean values.  So, the
four possible values of an FAIG are:</p>

<ul>

<li>@('(nil . nil)'), which we call Z,</li>

<li>@('(t . nil)'), which we call True,</li>

<li>@('(nil . t)'), which we call False, and</li>

<li>@('(t . t)'), which we call X.</li>

</ul>

<p>We generally think of the onset as being a Boolean functions that should
evaluate to @('T') when the wire is being driven to 1.  The offset is similar,
but indicates whether the wire is being driven to 0.  So, the Z value
represents a situation where the wire is completely undriven, and the X value
represents a bad case where the wire is simultaneously driven to both True and
False.</p>

<p>Hons convention.  We ordinarly construct all AIGs with @(see hons), but we
don't bother to hons the FAIG conses that put these AIGs together.</p>

<p>BOZO discuss vu-faigs too.</p>")


; [Jared] BOZO consider a warning as in aig-eval for when faig-eval,
; faig-restrict, etc., are used on non-consp arguments.

(defsection faig-eval
  :parents (faig)
  :short "@(call faig-eval) evaluates @('x'), a @(see faig), under the
environment @('env'), producing a pair of Boolean values."

  :long "<p>See @(see aig-eval); the @('env') should be a fast alist and you
will want to clear the memoize table for @('aig-eval') when you are done using
the @('env').</p>"

  (defun faig-eval (x env)
    (declare (xargs :guard t))
    (if (atom x)
        '(t . t)
      (cons (aig-eval (car x) env)
            (aig-eval (cdr x) env)))))


(defsection faig-eval-list
  :parents (faig-eval)
  :short "@(call faig-eval-list) evaluates a list of FAIGs."

  (defun faig-eval-list (x env)
    (declare (xargs :guard t))
    (if (atom x)
        nil
      (cons (faig-eval (car x) env)
            (faig-eval-list (cdr x) env)))))


(defsection faig-eval-alist
  :parents (faig-eval)
  :short "@(call faig-eval-list) evaluates an FAIG alist (an alist binding
keys to FAIGs)."

  :long "<p>The alist @('x') does not need to be fast, and we produce an
ordinary (slow) alist as a result.</p>"

  (defun faig-eval-alist (x env)
    (declare (xargs :guard t))
    (cond ((atom x)
           nil)
          ((atom (car x))
           ;; Bad alist convention
           (faig-eval-alist (cdr x) env))
          (t
           (cons (cons (caar x)
                       (faig-eval (cdar x) env))
                 (faig-eval-alist (cdr x) env))))))




(defsection faig-restrict
  :parents (faig)
  :short "@(call faig-restrict) performs variable substitution throughout the
FAIG @('x'), replacing any variables bound in @('sigma') with their
corresponding values."

  :long "<p>See @(see aig-restrict); the @('env') should be a fast alist and
you will want to clear the memoize table for @('aig-restrict') when you are
done using the @('env').</p>"

  (defun faig-restrict (x sigma)
    (declare (xargs :guard t))
    (if (atom x)
        '(t . t)
      (cons (aig-restrict (car x) sigma)
            (aig-restrict (cdr x) sigma)))))


(defsection faig-restrict-alist
  :parents (faig-restrict)
  :short "@(call faig-restrict-alist) substitutes into an FAIG alist (an alist
binding keys to FAIGs)."

  :long "<p>The alist @('x') does not need to be fast, and we produce an
ordinary (slow) alist as a result.</p>"

  (defun faig-restrict-alist (x sigma)
    (declare (xargs :guard t))
    (if (atom x)
        nil
      (let ((rest (faig-restrict-alist (cdr x) sigma)))
        (if (atom (car x))
            ;; Bad alist convention
            rest
          (cons (cons (caar x) (faig-restrict (cdar x) sigma))
                rest))))))


(defsection faig-restrict-alists
  :parents (faig-restrict)
  :short "@(call faig-restrict-alists) substitutes into a list of FAIG alists."

  (defun faig-restrict-alists (x sigma)
    (if (atom x)
        nil
      (cons (faig-restrict-alist (car x) sigma)
            (faig-restrict-alists (cdr x) sigma)))))




(defsection faig-compose
  :parents (faig)
  :short "@(call faig-compose) performs variable substitution throughout the
FAIG @('x'), <b>unconditionally</b> replacing every variable in @('x') with its
binding in @('sigma')."

  :long "<p>See @(see aig-compose); the @('sigma') should be a fast alist and
you will want to clear the memoize table for @('aig-compose') when you are done
using the @('env').</p>"

  (defun faig-compose (x sigma)
    (declare (xargs :guard t))
    (if (atom x)
        '(t . t)
      (cons (aig-compose (car x) sigma)
            (aig-compose (cdr x) sigma)))))


(defsection faig-compose-alist
  :parents (faig)
  :short "@(call faig-compose-alist) composes into an FAIG Alist (an alist
binding keys to FAIGs)."

  :long "<p>The alist @('x') does not need to be fast, and we produce an
ordinary (slow) alist as a result.</p>"

  (defun faig-compose-alist (x sigma)
    (declare (xargs :guard t))
    (if (atom x)
        nil
      (let ((rest (faig-compose-alist (cdr x) sigma)))
        (if (atom (car x))
            ;; Bad alist convention
            rest
          (cons (cons (caar x) (faig-compose (cdar x) sigma))
                rest))))))




(defsection faig-partial-eval
  :parents (faig)
  :short "@(call faig-partial-eval) evaluates @('x'), an FAIG, under the
partial environment @('env'), producing a new FAIG as a result."

  :long "<p>See @(see aig-partial-eval); the @('env') should be a fast alist
and you will want to clear the memoize table for @('aig-partial-eval') when you
are done using the @('env').</p>"

  (defun faig-partial-eval (x env)
    (declare (xargs :guard t))
    (if (atom x)
        '(t . t)
      (cons (aig-partial-eval (car x) env)
            (aig-partial-eval (cdr x) env)))))


(defsection faig-partial-eval-alist
  :parents (faig-partial-eval)
  :short "@(call faig-partial-eval-alist) partially evaluates an FAIG alist (an
alist binding keys to FAIGs)."

  :long "<p>The alist @('x') does not need to be fast, and we produce an
ordinary (slow) alist as a result.</p>"

  (defun faig-partial-eval-alist (x env)
    (declare (xargs :guard t))
    (if (atom x)
        nil
      (let ((rest (faig-partial-eval-alist (cdr x) env)))
        (if (atom (car x))
            ;; Bad alist convention
            rest
          (cons (cons (caar x) (faig-partial-eval (cdar x) env))
                rest))))))


(defsection faig-partial-eval-alists
  :parents (faig-partial-eval)
  :short "@(call faig-partial-eval-alists) partially evaluates a list of FAIG
alists."

  (defund faig-partial-eval-alists (x env)
    (declare (xargs :guard t))
    (if (atom x)
        nil
      (cons (faig-partial-eval-alist (car x) env)
            (faig-partial-eval-alists (cdr x) env)))))




(defsection faig-fix
  :parents (faig)
  :short "@(call faig-fix) is the identity for FAIGs, but coerces atoms to
@('(t . t)'), i.e., X."

  :long "<p>This is sometimes when reasoning about FAIG operations.</p>"

  (defun faig-fix (x)
    (declare (xargs :guard t))
    (if (consp x) x '(t . t))))


(defsection faig-fix-list
  :parents (faig-fix)
  :short "@(call faig-fix-list) fixes every element of a list with @(see
faig-fix)."

  (defun faig-fix-list (x)
    (declare (xargs :guard t))
    (if (atom x)
        nil
      (cons (faig-fix (car x))
            (faig-fix-list (cdr x))))))


(defsection faig-fix-alist
  :parents (faig-fix)
  :short "@(call faig-fix-alist) fixes every value in an alist with @(see
faig-fix)."

  (defun faig-fix-alist (x)
    (declare (xargs :guard t))
    (cond ((atom x)
           nil)
          ((atom (car x))
           ;; Bad-alist convention
           (faig-fix-alist (cdr x)))
          (t
           (cons (cons (caar x) (faig-fix (cdar x)))
                 (faig-fix-alist (cdr x)))))))






;; [Jared] These might be more properly part of EMOD/ESIM

(defun aig-eval-pat (pat x al)
  (declare (xargs :guard t))
  (if pat
      (if (atom pat)
          (aig-eval x al)
        (cons (aig-eval-pat (car pat) (ec-call (car x)) al)
              (aig-eval-pat (cdr pat) (ec-call (cdr x)) al)))
    nil))

(defn faig-eval-pat (pat x al)
  (if pat
      (if (atom pat)
          (faig-eval x al)
        (cons (faig-eval-pat (car pat) (ec-call (car x)) al)
              (faig-eval-pat (cdr pat) (ec-call (cdr x)) al)))
    nil))

(defn faig-restrict-pat (pat fpat al)
  (if pat
      (if (atom pat)
          (faig-restrict fpat al)
        (cons (faig-restrict-pat (car pat) (ec-call (car fpat)) al)
              (faig-restrict-pat (cdr pat) (ec-call (cdr fpat)) al)))
    nil))

(defn faig-compose-pat (pat fpat al)
  (if pat
      (if (atom pat)
          (faig-compose fpat al)
        (cons (faig-compose-pat (car pat) (ec-call (car fpat)) al)
              (faig-compose-pat (cdr pat) (ec-call (cdr fpat)) al)))
    nil))

(defn faig-partial-eval-pat (pat fpat al)
  (if pat
      (if (atom pat)
          (faig-partial-eval fpat al)
        (cons (faig-partial-eval-pat (car pat) (ec-call (car fpat)) al)
              (faig-partial-eval-pat (cdr pat) (ec-call (cdr fpat)) al)))
    nil))





;; [Jared] Can we get rid of this stuff?

(defn faigp (x) (consp x))

(defn faig-listp (x)
  (if (consp x)
      (and (faigp (car x))
           (faig-listp (cdr x)))
    (null x)))

(in-theory (disable faig-listp))

(defn aig-p (x)
  (aig-cases
   x
   :true t
   :false t
   :var t
   :inv (and (aig-p (car x))
             (hons-equal (aig-not (car x)) x))
   :and (and (aig-p (car x))
             (aig-p (cdr x))
             (hons-equal (aig-and (car x) (cdr x)) x))))

(memoize 'aig-p :condition '(and (consp x) (cdr x)))

(defn faig-patternp (pat x)
  (if pat
      (if (atom pat)
          (and (consp x)
               (aig-p (car x))
               (aig-p (cdr x)))
        (and (consp x)
             (faig-patternp (car pat) (car x))
             (faig-patternp (cdr pat) (cdr x))))
    t))









;; [Jared] Removed these things...


;; Note that these next two functions are provably equal to T.
;; (defn aigp (x)
;;   (or
;;    (atom x)
;;    (and (consp x) (null (cdr x)))
;;    (and (aigp (car x)) (aigp (cdr x))))
;;   )

;; (defn aig-listp (x)
;;   (if (consp x)
;;       (and
;;        (aigp (car x))
;;        (aig-listp (cdr x)))
;;     t))


;; [Jared] this was never used anywhere, i think it's not necessary since
;; aig-compose uses aig-env-lookup

;; (defconst *aig-compose-warn-missing-binding* t)





;; [jared] this macro stuff was just used in one old mmx property checking
;; thing it might be reasonable to put in xxxjoin style macros for aig-and,
;; aig-or, etc.; could also implement the lazy evaluation stuff like in ubdds,
;; if desired.

;; ;---- some macros for aig-or/aig-and/... 
;; ;do we want to rebalance it (make it less deep and smaller)?
;; ; would rebalancing have any impact on zz-sat performance?
;; (defn aig-and-fn (lst)
;;   (if (consp lst)
;;       (if (consp (cdr lst))
;;           (list
;;            'aig-and
;;            (car lst)
;;            (aig-and-fn (cdr lst)))
;;         (car lst))
;;     t)
;;   )

;; (defmacro aig-and-macro (&rest args) (aig-and-fn args))

;; (defn aig-or-fn (lst)
;;   (if (consp lst)
;;       (if (consp (cdr lst))
;;           (list
;;            'aig-or
;;            (car lst)
;;            (aig-or-fn (cdr lst)))
;;         (car lst))
;;     nil)
;;   )

;; (defmacro aig-or-macro (&rest args) (aig-or-fn args))

;; (defn one-hot-fn (lst)
;;   (if (consp lst)
;;       (if (consp (cdr lst))
;;           `(aig-or
;;             (aig-and 
;;              ,(car lst) 
;;              (aig-not ,(aig-or-fn (cdr lst))))
;;             (aig-and
;;              (aig-not ,(car lst))
;;              ,(one-hot-fn (cdr lst))))
;;         (car lst))
;;     nil
;;     )
;;   )

;; (defmacro one-hot (&rest args) (one-hot-fn args))



;; [Jared] looks like this was part of an experiment in transistor/propagate
;; at one point, but it doesn't seem to be used anymore

;; (defun aig-env-lookup-nil (x al)
;;   (declare (Xargs :guard t))
;;   (let ((look (hons-get x al)))
;;     (if look
;;         (cdr look)
;;       (prog2$ (and *aig-env-lookup-warn-missing-binding*
;;                    (aig-env-lookup-missing-output x))
;;               nil))))

;; (defn aig-compose-nil (x al)
;;   (aig-cases
;;    x
;;    :true t
;;    :false nil
;;    :var (aig-env-lookup-nil x al)
;;    :inv (aig-not (aig-compose-nil (car x) al))
;;    :and (let ((a (aig-compose-nil (car x) al)))
;;           (and a (aig-and a (aig-compose-nil (cdr x) al))))))

;; (memoize 'aig-compose-nil :condition '(and (consp x) (cdr x)))

;; (defn aig-compose-nil-alist (x-alst al)
;;   (if (atom x-alst)
;;       nil
;;     (if (atom (car x-alst))
;;         (aig-compose-nil-alist (cdr x-alst) al)
;;       (cons (cons (caar x-alst)
;;                   (aig-compose-nil (cdar x-alst) al))
;;             (aig-compose-nil-alist (cdr x-alst) al)))))

;; (defn aig-compose-nil-list (x al)
;;   (if (atom x)
;;       nil
;;     (cons (aig-compose-nil (car x) al)
;;           (aig-compose-nil-list (cdr x) al))))




;; (defn faig-compose-nil (x comp-al)
;;   (if (atom x)
;;       '(t . t)
;;     (cons (aig-compose-nil (car x) comp-al)
;;           (aig-compose-nil (cdr x) comp-al))))

;; (defn faig-compose-nil-pat (pat fpat al)
;;   (if pat
;;       (if (atom pat)
;;           (faig-compose-nil fpat al)
;;         (cons (faig-compose-nil-pat (car pat) (ec-call (car fpat)) al)
;;               (faig-compose-nil-pat (cdr pat) (ec-call (cdr fpat)) al)))
;;     nil))

;; (defn faig-compose-nil-alist (al comp-al)
;;   (if (atom al)
;;       nil
;;     (let ((rest (faig-compose-nil-alist (cdr al) comp-al)))
;;       (if (atom (car al))
;;           rest
;;         (cons (cons (caar al) (faig-compose-nil (cdar al) comp-al))
;;               rest)))))








;; [Jared] This doesn't seem to be used for anything...

;; ;; Translate Lisp-like terms into AIGs.
;; (mutual-recursion
;;  (defun logic-to-aig (tree)
;;    (declare (xargs :measure (acl2-count tree)
;;                    :guard t))
;;    (if (atom tree)
;;        tree
;;      (case (car tree)
;;        ((and or xor iff) (logic-to-aig-list (car tree) (cdr tree)))
;;        (nand (aig-not (logic-to-aig-list 'and (cdr tree))))
;;        (nor (aig-not (logic-to-aig-list 'or (cdr tree))))
;;        (implies (and (eql (len tree) 3)
;;                      (aig-or (aig-not (logic-to-aig (cadr tree)))
;;                              (logic-to-aig (caddr tree)))))
;;        (if (and (eql (len tree) 4)
;;                 (aig-ite (logic-to-aig (cadr tree))
;;                          (logic-to-aig (caddr tree))
;;                          (logic-to-aig (cadddr tree)))))
;;        (not (and (eql (len tree) 2)
;;                  (aig-not (logic-to-aig (cadr tree))))))))
;;  (defun logic-to-aig-list (op trees)
;;    (declare (xargs :measure (acl2-count trees)
;;                    :guard t))
;;    (if (atom trees)
;;        (case op
;;          (xor nil)
;;          (iff t)
;;          (and t)
;;          (or nil))
;;      (let ((first (logic-to-aig (car trees)))
;;            (rest (logic-to-aig-list op (cdr trees))))
;;        (case op
;;          (xor (aig-xor first rest))
;;          (iff (aig-iff first rest))
;;          (and (aig-and first rest))
;;          (or (aig-or first rest)))))))

;; (memoize 'logic-to-aig :condition '(consp tree))



