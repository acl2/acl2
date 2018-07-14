; Centaur AIG Library
; Copyright (C) 2008-2011 Centaur Technology
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

(define aig-var-p (x)
  :inline t
  (if (atom x)
      (and (not (eq x t))
           (not (eq x nil)))
    (and (eq (car x) nil)
         (cdr x)
         t))
  ///
  (defthm aig-var-p-of-aig-var
    (implies x
             (aig-var-p (cons nil x))))

  (defthm aig-var-p-of-atom
    (implies (not (aig-var-p x))
             (not (and (atom x)
                       (not (booleanp x)))))
    :rule-classes :compound-recognizer))

(define aig-var-listp (x)
  (if (atom x)
      (eq x nil)
    (and (aig-var-p (car x))
         (aig-var-listp (cdr x))))
  ///
  (defthmd aig-var-p-when-member-of-aig-var-listp
    (implies (and (aig-var-listp x)
                  (member k x))
             (aig-var-p k)))

  (defthm aig-var-listp-of-cons
    (equal (aig-var-listp (cons x y))
           (and (aig-var-p x)
                (aig-var-listp y))))

  (defthm aig-var-listp-of-nil
    (aig-var-listp nil))

  (defthm aig-var-listp-of-insert
    (implies (and (aig-var-p x)
                  (aig-var-listp y))
             (aig-var-listp (set::insert x y)))
    :hints(("Goal" :in-theory (enable set::insert set::head set::tail set::sfix))))

  (defthm aig-var-listp-of-union
    (implies (and (aig-var-listp x)
                  (aig-var-listp y))
             (aig-var-listp (set::union x y)))
    :hints(("Goal" :in-theory (enable set::union set::head set::tail set::sfix)))))

(define aig-atom-p (x)
  :inline t
  (or (atom x)
      (and (eq (car x) nil)
           (cdr x)
           t))
  ///
  (defthm not-aig-atom-implies-consp
    (implies (not (aig-atom-p x))
             (consp x))
    :rule-classes :compound-recognizer)

  (defthm aig-var-p-when-aig-atom-p
    (implies (and (aig-atom-p x)
                  (not (booleanp x)))
             (aig-var-p x))
    :hints(("Goal" :in-theory (enable aig-var-p))))

  (defthm aig-atom-p-when-aig-var-p
    (implies (aig-var-p x)
             (aig-atom-p x))
    :hints(("Goal" :in-theory (enable aig-var-p))))

  (defthm not-aig-atom-p-of-negation
    (not (aig-atom-p (cons x nil))))

  (defthm not-aig-atom-p-of-cons
    (implies x
             (not (aig-atom-p (cons x y)))))

  (defthmd aig-atom-p-of-cons-strong
    (iff (aig-atom-p (cons x y))
         (and (not x) y))
    :hints(("Goal" :in-theory (enable aig-atom-p)))))
  

(defsection aig-cases
  :parents (aig-other)
  :short "Control-flow macro to split into cases on what kind of AIG you have
encountered."
  :long "@(def aig-cases)"

  (defmacro aig-cases (x &key true false var inv and)
    `(let ((aig-cases-var ,x))
       (cond
        ((aig-atom-p aig-cases-var)
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
nicely (it makes unbound FAIG variables evaluate to @('X')).</p>"

  :enabled t

  (let ((look (hons-get x env)))
    (if look
        (and (cdr look) t)
      (mbe :logic t
           :exec
           (if *aig-env-lookup-warn-missing-binding*
               (prog2$ (aig-env-lookup-missing-output x)
                       t)
             t)))))

(define aig-alist-lookup
  :parents (aig-eval)
  :short "Look up the value of an AIG variable in an environment."

  ((x   "Variable to look up.")
   (env "Fast alist mapping variables to values."))

  :long "<p>Unbound variables are given the default value @('t') instead of
@('nil') because this makes theorems about @(see faig) evaluation work out more
nicely (it makes unbound FAIG variables evaluate to @('X')).</p>"

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
    :var (aig-env-lookup x env)
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
          (aig-eval-list (cdr x) env)))
  ///
  (defthm consp-of-aig-eval-list
    (equal (consp (aig-eval-list x env))
           (consp x)))

  (defthm len-of-aig-eval-list
    (equal (len (aig-eval-list x env))
           (len x)))

  (defthm aig-eval-list-of-append
    (equal (aig-eval-list (append x y) env)
           (append (aig-eval-list x env)
                   (aig-eval-list y env)))))


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
of variables that are found under that node.  We use ordinary @(see std/osets)
as our variable set representation so that merging these sets is linear at each
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
             :and   (set::union (aig-vars (car x))
                                (aig-vars (cdr x))))
  ///
  (defthm aig-var-listp-aig-vars
    (aig-var-listp (aig-vars x)))

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
        ((and (not (aig-atom-p x))
              (eq (cdr x) nil))
         (car x))
        (t
         (hons x nil)))
  ///
  (defthm aig-eval-not
    (equal (aig-eval (aig-not x) env)
           (not (aig-eval x env)))))


(define aig-and-count (x)
  :parents (aig)
  :short "Counts how many ANDs are in an AIG."
  :returns (count natp :rule-classes :type-prescription)
  (cond ((aig-atom-p x)
         0)
        ((eq (cdr x) nil)
         (aig-and-count (car x)))
        (t
         (+ 1
            (aig-and-count (car x))
            (aig-and-count (cdr x)))))
  ///
  (defthm aig-and-count-when-atom
    (implies (aig-atom-p x)
             (equal (aig-and-count x)
                    0)))

  (defthm aig-and-count-of-aig-not
    (equal (aig-and-count (aig-not x))
           (aig-and-count x))
    :hints(("Goal" :in-theory (enable aig-not)))))



; -----------------------------------------------------------------------------
;
;                               AIG AND
;
; -----------------------------------------------------------------------------

(local (xdoc::set-default-parents aig-and))

(define aig-negation-p (x y)
  :short "@(call aig-negation-p) determines if the AIGs @('x') and @('y')
are (syntactically) negations of one another."
  :inline t
  (or (and (consp y)
           (eq (cdr y) nil)
           (hons-equal (car y) x))
      (and (consp x)
           (eq (cdr x) nil)
           (hons-equal (car x) y)))
  ///
  (defthm aig-negation-p-symmetric
    (equal (aig-negation-p x y)
           (aig-negation-p y x)))

  (defthmd aig-negation-p-correct-1
    (implies (and (aig-negation-p x y)
                  (aig-eval x env))
             (equal (aig-eval y env)
                    nil)))

  (defthmd aig-negation-p-correct-2
    (implies (and (aig-negation-p x y)
                  (not (aig-eval x env)))
             (equal (aig-eval y env)
                    t))))

(local (in-theory (enable aig-negation-p-correct-1
                          aig-negation-p-correct-2)))

(define aig-and-dumb (x y)
  :short "@(call aig-and-dumb) is a simpler alternative to @(see aig-and)."
  :long "<p>This does far fewer reductions than @(see aig-and).  We fold
constants and collapse @('x & x') and @('x & ~x'), but that's it.</p>"
  :returns aig
  (cond ((or (eq x nil) (eq y nil)) nil)
        ((eq x t) y)
        ((eq y t) x)
        ((hons-equal x y) x)
        ((aig-negation-p x y) nil)
        (t (hons x y)))
  ///
  (defthm aig-eval-of-aig-and-dumb
    (equal (aig-eval (aig-and-dumb x y) env)
           (and (aig-eval x env)
                (aig-eval y env))))

  (defthm aig-and-dumb-of-constants
    (and (equal (aig-and-dumb nil x) nil)
         (equal (aig-and-dumb x nil) nil)
         (equal (aig-and-dumb x t) x)
         (equal (aig-and-dumb t x) x))))


(define aig-and-pass1 (x y)
  :returns (mv hit ans)
  :short "Level 1 simplifications."
  :long "<p>See also @(see aig-and-dumb), which tries to apply these same
reductions, but otherwise just gives up, and doesn't report whether it has
succeded or not.</p>"
  :inline t
  (cond ((eq x nil)           (mv t nil))
        ((eq y nil)           (mv t nil))
        ((eq x t)             (mv t y))
        ((eq y t)             (mv t x))
        ((hons-equal x y)     (mv t x))
        ((aig-negation-p x y) (mv t nil))
        (t                    (mv nil nil)))
  ///
  (defret aig-and-pass1-correct
    (implies hit
             (equal (aig-eval ans env)
                    (and (aig-eval x env)
                         (aig-eval y env))))
    :rule-classes nil))


(define aig-and-pass2a (x y)
  :returns (mv status arg1 arg2)
  :short "Level 2 Contradiction Rule 1 and Idempotence Rule, Single Direction."
  (b* (((unless (and (not (aig-atom-p x))
                     (not (eq (cdr x) nil))))
        (mv :fail x y))
       (a (car x))
       (b (cdr x))
       ((when (or (aig-negation-p a y)
                  (aig-negation-p b y)))
        ;; Level 2, Contradiction Rule 1
        (mv :subterm nil nil))
       ((when (or (hons-equal a y)
                  (hons-equal b y)))
        ;; Level 2, Idempotence Rule
        (mv :subterm x x)))
    (mv :fail x y))
  ///
  (defret aig-and-pass2a-correct
    (equal (and (aig-eval arg1 env)
                (aig-eval arg2 env))
           (and (aig-eval x env)
                (aig-eval y env)))
    :rule-classes nil)

  (defret aig-and-pass2a-never-reduced
    (not (equal status :reduced)))

  (defret aig-and-pass2a-subterm-convention
    (implies (equal status :subterm)
             (equal arg2 arg1)))

  (defret aig-and-pass2a-normalize-status
    (implies (and (not (equal status :subterm))
                  (not (equal status :reduced)))
             (and (equal status :fail)
                  (equal arg1 x)
                  (equal arg2 y)))))


(define aig-and-pass2 (x y)
  :returns (mv status arg1 arg2)
  :short "Level 2 Contradiction Rule 1 and Idempotence Rule, Both Directions."
  :inline t
  ;; Subtle argument order to get fail theorem to work out nicely
  (b* (((mv status a b) (aig-and-pass2a y x))
       ((unless (eq status :fail))
        (mv status a b)))
    (aig-and-pass2a x y))
  ///
  (defret aig-and-pass2-correct
    (equal (and (aig-eval arg1 env)
                (aig-eval arg2 env))
           (and (aig-eval x env)
                (aig-eval y env)))
    :rule-classes nil
    :hints(("Goal" :use ((:instance aig-and-pass2a-correct)
                         (:instance aig-and-pass2a-correct (x y) (y x))))))

  (defret aig-and-pass2-never-reduced
    (not (equal status :reduced)))

  (defret aig-and-pass2-subterm-convention
    (implies (equal status :subterm)
             (equal arg2 arg1)))

  (defret aig-and-pass2-normalize-status
    (implies (and (not (equal status :subterm))
                  (not (equal status :reduced)))
             (and (equal status :fail)
                  (equal arg1 x)
                  (equal arg2 y)))))


(define aig-and-pass3 (x y)
  :returns (mv status arg1 arg2)
  :short "Level 2 Contradiction Rule 2 and all Level 4 Rules."
  :inline t
  (b* (((unless (and (not (aig-atom-p x))
                     (not (eq (cdr x) nil))))
        (mv :fail x y))
       ((unless (and (not (aig-atom-p y))
                     (not (eq (cdr y) nil))))
        (mv :fail x y))
       (a (car x))
       (b (cdr x))
       (c (car y))
       (d (cdr y))
       ((when (or (aig-negation-p a c)
                  (aig-negation-p a d)
                  (aig-negation-p b c)
                  (aig-negation-p b d)))
        ;; Level 2, Contradiction Rule 2
        (mv :subterm nil nil))

       ;; Level 4 -- All Rules.  In all of the following we have some choice as
       ;; to which form we might use.  It is tempting to try to put in some kind
       ;; of a heuristic here to make a better choice.  But it is difficult to
       ;; imagine how something like that might work for Hons AIGs.
       ;;
       ;; Consider the A=C case, but all of the other cases are similar.  The
       ;; choice is really: do we want to prefer B & (A & D) or do we want to
       ;; choose (A & B) & D.  The better form to use is really governed by the
       ;; rest of the circuit, i.e., which form would give us better structure
       ;; sharing.  But with Hons AIGs we don't really have any kind of
       ;; reference counts, so it's not clear how to make a good decision.
       ;;
       ;; As a dumb attempt to try to make our normalization more consistent,
       ;; we will arbitrarily always choose the form that preserves X.
       ((when (hons-equal a c))
        ;; Can choose Idempotence Rule 1 or 4
        ;; (A & B) & (A & D) -- could be B & (A & D) or (A & B) & D
        ;;                               B & Y       or X & D
        (mv :reduced x d))

       ((when (hons-equal b c))
        ;; (A & B) & (B & D) -- could be A & (B & D) or (A & B) & D
        ;;                               A & Y       or X & D
        (mv :reduced x d))

       ((when (hons-equal b d))
        ;; (A & B) & (C & B) -- could be A & (C & B) or (A & B) & C
        ;;                               A & Y       or X & C
        (mv :reduced x c))

       ((when (hons-equal a d))
        ;; (A & B) & (C & A) -- could be B & (C & A) or (A & B) & C
        ;;                               B & Y       or X & C
        (mv :reduced x c)))
    (mv :fail x y))
  ///
  (defret aig-and-pass3-correct
    (equal (and (aig-eval arg1 env)
                (aig-eval arg2 env))
           (and (aig-eval x env)
                (aig-eval y env)))
    :rule-classes nil)

  (defret aig-and-pass3-reduces-count
    (implies (eq status :reduced)
             (< (+ (aig-and-count arg1)
                   (aig-and-count arg2))
                (+ (aig-and-count x)
                   (aig-and-count y))))
    :rule-classes nil
    :hints(("Goal" :in-theory (enable aig-and-count))))

  (defret aig-and-pass3-subterm-convention
    (implies (equal status :subterm)
             (equal arg2 arg1)))

  (defret aig-and-pass3-normalize-status
    (implies (and (not (equal status :subterm))
                  (not (equal status :reduced)))
             (and (equal status :fail)
                  (equal arg1 x)
                  (equal arg2 y)))))


(define aig-and-pass4a (x y)
  :returns (mv status arg1 arg2)
  :short "Level 2, Subsumption Rules 1 and 2, Single Direction."
  (b* (((unless (and (not (aig-atom-p x))
                     (eq (cdr x) nil)))
        (mv :fail x y))
       (~x (car x))
       ((unless (and (not (aig-atom-p ~x))
                     (not (eq (cdr ~x) nil))))
        (mv :fail x y))
       ;; X is ~(A & B)
       (a (car ~x))
       (b (cdr ~x))
       ((when (or (aig-negation-p a y)
                  (aig-negation-p b y)))
        ;; Subsumption Rule 1.
        (mv :subterm y y))

       ((when (and (not (aig-atom-p y))
                   (not (eq (cdr y) nil))))
        ;; Y is an AND.  The only thing we can match is Subsumption Rule 2.
        (b* ((c (car y))
             (d (cdr y))
             ((when (or (aig-negation-p a c)
                        (aig-negation-p a d)
                        (aig-negation-p b c)
                        (aig-negation-p b d)))
              ;; For example:  ~(A & B) & (~A & C)
              ;;           === ~(A & B) & ~A & C
              ;;        So this  ---------^
              ;;        Implies ~(A & B)
              ;;     And the whole thing is just (~A & C)
              (mv :subterm y y)))
          ;; No other rules match ~(A & B) & (C & D).
          (mv :fail x y))))
    (mv :fail x y))
  ///
  (defret aig-and-pass4a-correct
    (equal (and (aig-eval arg1 env)
                (aig-eval arg2 env))
           (and (aig-eval x env)
                (aig-eval y env)))
    :rule-classes nil)

  (defret aig-and-pass4a-never-reduced
    (not (equal status :reduced)))

  (defret aig-and-pass4a-subterm-convention
    (implies (equal status :subterm)
             (equal arg2 arg1)))

  (defret aig-and-pass4a-normalize-status
    (implies (and (not (equal status :subterm))
                  (not (equal status :reduced)))
             (and (equal status :fail)
                  (equal arg1 x)
                  (equal arg2 y)))))


(define aig-and-pass4 (x y)
  :short "Level 2, Subsumption Rules 1 and 2, Both Directions."
  :returns (mv status arg1 arg2)
  :inline t
  ;; Subtle argument order to get fail theorem to work out nicely
  (b* (((mv status arg1 arg2) (aig-and-pass4a y x))
       ((unless (eq status :fail))
        (mv status arg1 arg2)))
    (aig-and-pass4a x y))
  ///
  (defret aig-and-pass4-correct
    (equal (and (aig-eval arg1 env)
                (aig-eval arg2 env))
           (and (aig-eval x env)
                (aig-eval y env)))
    :rule-classes nil
    :hints(("Goal" :use ((:instance aig-and-pass4a-correct)
                         (:instance aig-and-pass4a-correct (x y) (y x))))))

  (defret aig-and-pass4-never-reduced
    (not (equal status :reduced)))

  (defret aig-and-pass4-subterm-convention
    (implies (equal status :subterm)
             (equal arg2 arg1)))

  (defret aig-and-pass4-normalize-status
    (implies (and (not (equal status :subterm))
                  (not (equal status :reduced)))
             (and (equal status :fail)
                  (equal arg1 x)
                  (equal arg2 y)))))


(define aig-and-pass5 (x y)
  :short "Level 2, Resolution Rule."
  :returns (mv status arg1 arg2)
  :inline t
  (b* (((unless (and (not (aig-atom-p x))
                     (eq (cdr x) nil)
                     (not (aig-atom-p (car x)))
                     (not (eq (cdar x) nil))))
        (mv :fail x y))
       ((unless (and (not (aig-atom-p y))
                     (eq (cdr y) nil)
                     (not (aig-atom-p (car y)))
                     (not (eq (cdar y) nil))))
        (mv :fail x y))
       ;; X is ~(A & B), Y is ~(C & D).
       (a (caar x))
       (b (cdar x))
       (c (caar y))
       (d (cdar y))
       ((when (or (and (hons-equal a d) (aig-negation-p b c))
                  (and (hons-equal a c) (aig-negation-p b d))))
        ;; For example, in the first line:
        ;; ~(A & B) & ~(~B & A)
        ;; Which reduces to just ~A.
        ;; How?  I have no idea.  But this is true:
        ;;
        ;; (thm (iff (and (not (and a b))
        ;;                (not (and (not b) a)))
        ;;           (not a)))
        (let ((ans (aig-not a)))
          (mv :subterm ans ans)))

       ((when (or (and (hons-equal b d) (aig-negation-p a c))
                  (and (hons-equal b c) (aig-negation-p a d))))
        ;; As above.
        (let ((ans (aig-not b)))
          (mv :subterm ans ans))))
    (mv :fail x y))
  ///
  (defret aig-and-pass5-correct
    (equal (and (aig-eval arg1 env)
                (aig-eval arg2 env))
           (and (aig-eval x env)
                (aig-eval y env)))
    :rule-classes nil)

  (defret aig-and-pass5-never-reduced
    (not (equal status :reduced)))

  (defret aig-and-pass5-subterm-convention
    (implies (equal status :subterm)
             (equal arg2 arg1)))

  (defret aig-and-pass5-normalize-status
    (implies (and (not (equal status :subterm))
                  (not (equal status :reduced)))
             (and (equal status :fail)
                  (equal arg1 x)
                  (equal arg2 y)))))


(define aig-and-pass6a (x y)
  :short "Level 3 Substitution Rules, Single Direction."
  :returns (mv status arg1 arg2)
  (b* (((unless (and (not (aig-atom-p x))
                     (eq (cdr x) nil)
                     (not (aig-atom-p (car x)))
                     (not (eq (cdar x) nil))))
        (mv :fail x y))
       ;; X is ~(A & B)
       (a (caar x))
       (b (cdar x))

       ;; Substitution Rule 1.
       ((when (hons-equal a y))
        ;; ~(A & B) & A --> A & ~B
        (mv :reduced a (aig-not b)))
       ((when (hons-equal b y))
        ;; ~(A & B) & B --> B & ~A
        (mv :reduced b (aig-not a)))

       ((unless (and (not (aig-atom-p y))
                     (not (eq (cdr y) nil))))
        (mv :fail x y))

       ;; X is ~(A & B), Y is (C & D).
       (c (car y))
       (d (cdr y))

       ((when (or (hons-equal b c)
                  (hons-equal b d)))
        ;; Example: ~(A & B) & (C & B)
        ;;      --> ~A & (C & B)
        (mv :reduced (aig-not a) y))

       ((when (or (hons-equal a c)
                  (hons-equal a d)))
        (mv :reduced (aig-not b) y)))
    (mv :fail x y))
  ///
  (defret aig-and-pass6a-correct
    (equal (and (aig-eval arg1 env)
                (aig-eval arg2 env))
           (and (aig-eval x env)
                (aig-eval y env)))
    :rule-classes nil)

  (defret aig-and-pass6a-reduces-count
    (implies (eq status :reduced)
             (< (+ (aig-and-count arg1)
                   (aig-and-count arg2))
                (+ (aig-and-count x)
                   (aig-and-count y))))
    :rule-classes nil
    :hints(("Goal" :in-theory (enable aig-and-count))))

  (defret aig-and-pass6a-subterm-convention
    (implies (equal status :subterm)
             (equal arg2 arg1)))

  (defret aig-and-pass6a-arg2-on-failure
    (implies (and (equal status :fail)
                  y)
             (iff arg2 t)))

  (defret aig-and-pass6a-when-fail
    (implies (and (not (equal status :subterm))
                  (not (equal status :reduced)))
             (and (equal status :fail)
                  (equal arg1 x)
                  (equal arg2 y)))))


(define aig-and-pass6 (x y)
  :short "Level 3 Substitution Rules, Both Directions."
  :returns (mv status arg1 arg2)
  :inline t
  ;; Subtle argument order to get fail theorem to work out nicely
  (b* (((mv status arg1 arg2) (aig-and-pass6a y x))
       ((unless (eq status :fail))
        (mv status arg1 arg2)))
    (aig-and-pass6a x y))
  ///
  (defret aig-and-pass6-correct
    (equal (and (aig-eval arg1 env)
                (aig-eval arg2 env))
           (and (aig-eval x env)
                (aig-eval y env)))
    :rule-classes nil
    :hints(("Goal" :use ((:instance aig-and-pass6a-correct)
                         (:instance aig-and-pass6a-correct (x y) (y x))))))

  (defret aig-and-pass6-reduces-count
    (implies (eq status :reduced)
             (< (+ (aig-and-count arg1)
                   (aig-and-count arg2))
                (+ (aig-and-count x)
                   (aig-and-count y))))
    :rule-classes nil
    :hints(("Goal" :use ((:instance aig-and-pass6a-reduces-count)
                         (:instance aig-and-pass6a-reduces-count (x y) (y x))))))

  (defret aig-and-pass6-subterm-convention
    (implies (equal status :subterm)
             (equal arg2 arg1)))

  (defret aig-and-pass6-arg2-on-failure
    (implies (and (equal status :fail)
                  y)
             (iff arg2 t)))

  (defret aig-and-pass6-when-fail
    (implies (and (not (equal status :subterm))
                  (not (equal status :reduced)))
             (and (equal status :fail)
                  (equal arg1 x)
                  (equal arg2 y)))))

(define aig-and-main (x y)
  :short "And-Node, Main Optimizations, Non-Recursive."
  :returns (mv status arg1 arg2)
  (b* (;; All Level 1 Rules
       ((mv hit ans) (aig-and-pass1 x y))
       ((when hit)
        (mv :subterm ans ans))

       ;; Level 2 Contradiction Rule 1 and Idempotence Rule
       ((mv status arg1 arg2) (aig-and-pass2 x y))
       ((unless (eq status :fail))
        (mv status arg1 arg2))

       ;; All (A & B) & (C & D) style rules.
       ((mv status arg1 arg2) (aig-and-pass3 x y))
       ((unless (eq status :fail))
        (mv status arg1 arg2))

       ;; Level 2 Subsumption Rules
       ((mv status arg1 arg2) (aig-and-pass4 x y))
       ((unless (eq status :fail))
        (mv status arg1 arg2))

       ;; Level 2 Resolution Rule
       ((mv status arg1 arg2) (aig-and-pass5 x y))
       ((unless (eq status :fail))
        (mv status arg1 arg2)))

    ;; Level 3 Substitution Rules
    (aig-and-pass6 x y))
  ///
  (defret aig-and-main-correct
    (equal (and (aig-eval arg1 env)
                (aig-eval arg2 env))
           (and (aig-eval x env)
                (aig-eval y env)))
    :rule-classes nil
    :hints(("Goal"
            :use ((:instance aig-and-pass1-correct)
                  (:instance aig-and-pass2-correct)
                  (:instance aig-and-pass3-correct)
                  (:instance aig-and-pass4-correct)
                  (:instance aig-and-pass5-correct)
                  (:instance aig-and-pass6-correct)
                  ))))

  (defret aig-and-main-reduces-count
    (implies (eq status :reduced)
             (< (+ (aig-and-count arg1)
                   (aig-and-count arg2))
                (+ (aig-and-count x)
                   (aig-and-count y))))
    :rule-classes nil
    :hints(("Goal" :use ((:instance aig-and-pass3-reduces-count)
                         (:instance aig-and-pass6-reduces-count)
                         ))))

  (defret aig-and-main-subterm-convention
    (implies (equal status :subterm)
             (equal arg2 arg1)))

  (defret aig-and-main-on-failure
    (implies (and (not (equal status :reduced))
                  (not (equal status :subterm)))
             (and (equal status :fail)
                  (equal arg1 x)
                  (equal arg2 y))))

  (defthm aig-and-main-of-constants
    (and (equal (aig-and-main x nil) (mv :subterm nil nil))
         (equal (aig-and-main nil y) (mv :subterm nil nil))
         (equal (aig-and-main x t)   (mv :subterm x x))
         (equal (aig-and-main t x)   (mv :subterm x x)))
    :hints(("Goal" :in-theory (enable aig-and-main aig-and-pass1))))

  (defret aig-and-main-arg2-on-failure
    (implies (equal status :fail)
             arg2)
    :hints(("Goal" :in-theory (enable aig-and-pass1)))))

(define aig-binary-and (x y)
  :short "@(call aig-binary-and) constructs an AIG representing @('(and x y)')."
  :measure (+ (aig-and-count x) (aig-and-count y))
  (b* (((mv status arg1 arg2) (aig-and-main x y))
       ((when (eq status :subterm))
        arg1)
       ((when (eq status :reduced))
        (aig-binary-and arg1 arg2)))
    ;; Else, status is fail.
    (hons arg1 arg2))

  :hints(("Goal" :use ((:instance aig-and-main-reduces-count))))
  ///
  (local (in-theory (enable aig-binary-and)))

  (defthm aig-and-constants
    (and (equal (aig-binary-and nil x) nil)
         (equal (aig-binary-and x nil) nil)
         (equal (aig-binary-and x t) x)
         (equal (aig-binary-and t x) x)))

  (local (in-theory (enable aig-atom-p-of-cons-strong)))
           

  (defthm aig-eval-and
    (equal (aig-eval (aig-binary-and x y) env)
           (and (aig-eval x env)
                (aig-eval y env)))
    :hints(("Goal"
            :induct (aig-binary-and x y)
            :do-not '(generalize fertilize))
           (and stable-under-simplificationp
                '(:use ((:instance aig-and-main-correct)))))))

(define aig-and-macro-logic-part (args)
  :short "Generates the :logic part for a aig-and MBE call."
  :mode :program
  (cond ((atom args)
         t)
        ((atom (cdr args))
         (car args))
        (t
         `(aig-binary-and ,(car args)
                          ,(aig-and-macro-logic-part (cdr args))))))

(define aig-and-macro-exec-part (args)
  :short "Generates the :exec part for a aig-and MBE call."
  :mode :program
  (cond ((atom args)
         t)
        ((atom (cdr args))
         (car args))
        (t
         `(let ((aig-and-x-do-not-use-elsewhere ,(car args)))
            (and aig-and-x-do-not-use-elsewhere
                 (aig-binary-and aig-and-x-do-not-use-elsewhere
                                 ,(aig-and-macro-exec-part (cdr args))))))))

(defsection aig-and
  :parents (aig-constructors)
  :short "@('(aig-and x1 x2 ...)') constructs an AIG representing @('(and x1 x2
...)')."

  :long "<p>The main function is @(see aig-binary-and).  It implements
something like the algorithm described in:</p>

<ul>

<li>Robert Brummayer and Armin Biere.  <a
href='http://fmv.jku.at/papers/BrummayerBiere-MEMICS06.pdf'>Local Two-Level And
Inverter Graph Minimization Without Blowup</a>.  Mathematical and Engineering
Methods in Computer Science (MEMICS).  2006.</li>

</ul>

<p>In particular, see Table 2 in that paper, which describes optimization rules
that are ``locally size decreasing without affecting global sharing
negatively.''</p>

<p>We try to implement these rules in @(see aig-and-main), which returns:</p>

@({
     (mv status arg1 arg2)
})

<p>The status is either:</p>

<ul>
<li>@(':fail') if no rule applies, in which case @('arg1') and @('arg2') are
just copies of @('x') and @('y') and we need to construct a new AND node that
joins them together;</li>

<li>@(':subterm') if a rewrite rule applies that reduces the AND of @('x') and
@('y') to either a constant or to a subterm of @('x') or @('y').  This subterm
is returned as both @('arg1') and @('arg2').  In this case, we assume there is
no more rewriting to be done and just return the reduced subterm.</li>

<li>@(':reduced') if a rewrite rule applies that reduces the AND in some
interesting way, where it is no longer a proper subterm of @('x') or @('y').
In this case, it may be possible to further reduce @('arg1') and @('arg2'),
so we want to recursively rewrite them.</li>

</ul>

<p>@('aig-and') itself is a macro which extends @('aig-binary-and') across many
arguments.  As one last special optimization, when there is more than one
argument we try to \"short-circuit\" the computation and avoid evaluating some
arguments.</p>

<p>See also @(see aig-and-dumb), which is much less sophisticated but may be
easier to reason about in certain cases where you really care about the
structure of the resulting AIGs.</p>

<p>A June 2015 experiment suggests that, for a particular 80-bit floating point
addition problem, this fancier algorithm improves the size of AIGs produced by
@(see SV) by about 3% when measured either by unique AND nodes or by unique
conses.</p>

@(def aig-and)"

  (defmacro aig-and (&rest args)
    ;; BOZO consider doing something like the cheap-and-expensive-arguments
    ;; optimization that is done in q-and.
    `(mbe :logic ,(aig-and-macro-logic-part args)
          :exec  ,(aig-and-macro-exec-part  args)))

  (add-binop aig-and aig-binary-and)

  (local (defthm aig-and-sanity-check
           (and (equal (aig-and) t)
                (equal (aig-and x) x)
                (equal (aig-and x y) (aig-binary-and x y))
                (equal (aig-and x y z) (aig-binary-and x (aig-binary-and y z))))
           :rule-classes nil)))

(local (xdoc::set-default-parents))


(define aig-binary-or (x y)
  :parents (aig-or)
  :short "@(call aig-binary-or) constructs an AIG representing @('(or x y)')."
  :returns aig
  ;; We check for the NIL cases explicitly only in order to get the
  ;; aig-or-constants theorem to go through.  Without these check, we end up
  ;; trying to prove that (aig-not (aig-not x)) == x, which is not true if we
  ;; have a "malformed" AIG where like ((a . nil) . nil).
  (cond ((eq x nil) y)
        ((eq y nil) x)
        (t
         (aig-not (aig-and (aig-not x) (aig-not y)))))
  ///
  (defthm aig-eval-or
    (equal (aig-eval (aig-binary-or x y) env)
           (or (aig-eval x env)
               (aig-eval y env))))

  (defthm aig-or-constants
    ;; Important for the aig-or MBE to work.
    (and (equal (aig-binary-or nil x) x)
         (equal (aig-binary-or x nil) x)
         (equal (aig-binary-or x t) t)
         (equal (aig-binary-or t x) t))))

(define aig-or-macro-logic-part (args)
  :parents (aig-or)
  :mode :program
  (cond ((atom args)
         nil)
        ((atom (cdr args))
         (car args))
        (t
         `(aig-binary-or ,(car args)
                         ,(aig-or-macro-logic-part (cdr args))))))

(define aig-or-macro-exec-part (args)
  :parents (aig-or)
  :mode :program
  (cond ((atom args)
         nil)
        ((atom (cdr args))
         (car args))
        (t
         `(let ((aig-or-x-do-not-use-elsewhere ,(car args)))
            (if (eq t aig-or-x-do-not-use-elsewhere)
                t
              (aig-binary-or aig-or-x-do-not-use-elsewhere
                             (check-vars-not-free
                              (aig-or-x-do-not-use-elsewhere)
                              ,(aig-or-macro-exec-part (cdr args)))))))))


(defsection aig-or
  :parents (aig-constructors)
  :short "@('(aig-or x1 x2 ...)') constructs an AIG representing @('(or x1 x2
  ...)')."
  :long "<p>Like @(see aig-and), we attempt to lazily avoid computing later
terms in the expression.</p>

@(def aig-or)"

  (defmacro aig-or (&rest args)
    ;; BOZO consider doing something like the cheap-and-expensive-arguments
    ;; optimization that is done in q-and.
    `(mbe :logic ,(aig-or-macro-logic-part args)
          :exec  ,(aig-or-macro-exec-part  args)))

  (add-binop aig-or aig-binary-or)

  (local (defthm aig-or-sanity-check
           (or (equal (aig-or) nil)
               (equal (aig-or x) x)
               (equal (aig-or x y) (aig-binary-or x y))
               (equal (aig-or x y z) (aig-binary-or x (aig-binary-or y z))))
           :rule-classes nil)))


(define aig-xor (x y)
  :parents (aig-constructors)
  :short "@(call aig-xor) constructs an AIG representing @('(xor x y)')."
  :returns aig
  (aig-or (aig-and x (aig-not y))
          (aig-and y (aig-not x)))
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


(define aig-implies-fn (x y)
  :parents (aig-implies)
  :returns aig
  (aig-not (aig-and x (aig-not y)))
  ///
  (defthm aig-eval-implies
    (equal (aig-eval (aig-implies-fn x y) env)
           (implies (aig-eval x env)
                    (aig-eval y env))))

  (defthm aig-eval-implies-nil
    (equal (aig-implies-fn nil x) t)))


(defsection aig-implies
  :parents (aig-constructors)
  :short "@(call aig-implies) constructs an AIG representing @('(implies x
  y)')."
  :long "<p>We try to lazily avoid evaluating @('y').</p>
@(def aig-implies)"

  (defmacro aig-implies (x y)
    `(mbe :logic (aig-implies-fn ,x ,y)
          :exec (let ((aig-implies-x-do-not-use-elsewhere ,x))
                  (if (eq nil aig-implies-x-do-not-use-elsewhere)
                      t
                    (aig-implies-fn aig-implies-x-do-not-use-elsewhere
                                    (check-vars-not-free
                                     (aig-implies-x-do-not-use-elsewhere)
                                     ,y))))))

  (add-macro-alias aig-implies aig-implies-fn)

  (local (defthm aig-implies-sanity-check
           (equal (aig-implies x y)
                  (aig-implies-fn x y))
           :rule-classes nil)))


(defsection aig-nand
  :parents (aig-constructors)
  :short "@(call aig-nand) constructs an AIG representing @('(not (and x y))')."
  :long "@(def aig-nand)"

  (defmacro aig-nand (x y)
    `(aig-not (aig-and ,x ,y))))


(defsection aig-nor
  :parents (aig-constructors)
  :short "@(call aig-nor) constructs an AIG representing @('(not (or x y))')."

  (defmacro aig-nor (x y)
    `(aig-and (aig-not ,x) (aig-not ,y))))


(defsection aig-andc1
  :parents (aig-constructors)
  :short "@(call aig-andc1) constructs an AIG representing @('(and (not x) y)')."

  (defmacro aig-andc1 (x y)
    `(aig-and (aig-not ,x) ,y)))


(defsection aig-andc2
  :parents (aig-constructors)
  :short "@(call aig-andc2) constructs an AIG representing @('(and x (not y))')."

  (defmacro aig-andc2 (x y)
    `(aig-and ,x (aig-not ,y))))


(defsection aig-orc1
  :parents (aig-constructors)
  :short "@(call aig-orc1) is identical to @(see aig-implies)."
  :long "@(def aig-orc1)"

  (defmacro aig-orc1 (x y)
    `(aig-implies ,x ,y)))


(defsection aig-orc2
  :parents (aig-constructors)
  :short "@(call aig-orc2) constructs an AIG representing @('(or x (not y))')."

  (defmacro aig-orc2 (x y)
    `(aig-not (aig-and (aig-not ,x) ,y))))


(define aig-ite-fn (a b c)
  :parents (aig-ite)
  :returns aig
  (cond ((eq a t) b)
        ((eq a nil) c)
        ((hons-equal b c)
         b)
        ((eq b t)
         (aig-or a c))
        (t
         (aig-or (aig-and a b)
                 (aig-and (aig-not a) c))))
  ///
  (defthm aig-eval-ite
    (iff (aig-eval (aig-ite-fn a b c) env)
         (if (aig-eval a env)
             (aig-eval b env)
           (aig-eval c env))))

  (defthm aig-ite-of-constants
    ;; Important for MBE substitutions in the AIG-ITE macro.
    (and (equal (aig-ite-fn t b c) b)
         (equal (aig-ite-fn nil b c) c))))


(defsection aig-ite
  :parents (aig-constructors)
  :short "@(call aig-ite) constructs an AIG representing @('(if a b c)')."
  :long "<p>This is logically just @(see aig-ite-fn), but we try to lazily
avoid computing @('b') or @('c') when the value of @('a') is known.</p>"

  (defmacro aig-ite (a b c)
    `(mbe :logic (aig-ite-fn ,a ,b ,c)
          :exec (let ((aig-ite-x-do-not-use-elsewhere ,a))
                  (cond
                   ((eq aig-ite-x-do-not-use-elsewhere t)   ,b)
                   ((eq aig-ite-x-do-not-use-elsewhere nil) ,c)
                   (t
                    (aig-ite-fn aig-ite-x-do-not-use-elsewhere ,b ,c))))))

  (add-macro-alias aig-ite aig-ite-fn))


(define aig-not-list (x)
  :parents (aig-constructors)
  :short "@(call aig-not-list) negates every AIG in the list @('x')."
  :returns aig-list
  :enabled t
  (if (atom x)
      nil
    (cons (aig-not (car X))
          (aig-not-list (cdr x)))))


(define member-eql-without-truelistp ((a eqlablep) x)
  :parents (aig-and-list aig-or-list)
  :enabled t
  (mbe :logic (member a x)
       :exec
       (cond ((atom x) nil)
             ((eql a (car x)) x)
             (t (member-eql-without-truelistp a (cdr x))))))

(define aig-and-list-aux (x)
  :enabled t
  :parents (aig-and-list)
  (if (atom x)
      t
    (aig-and (car x) (aig-and-list-aux (cdr x)))))

(define aig-and-list (x)
  :parents (aig-constructors)
  :short "@(call aig-and-list) <i>and</i>s together all of the AIGs in the list
@('x')."
  :long "<p>As a dumb attempt at optimization, we try to avoid consing if we
see that there's a @('nil') anywhere in the list.  This won't win very often,
but it is quite cheap and it can win big when it does win by avoiding a lot of
AIG construction.</p>"
  :returns aig
  :enabled t
  :verify-guards nil
  (mbe :logic (if (atom x)
                  t
                (aig-and (car x)
                         (aig-and-list (cdr x))))
       :exec (cond ((atom x)
                    t)
                   ((member-eql-without-truelistp nil x)
                    nil)
                   (t
                    (aig-and-list-aux x))))
  ///
  (defthm aig-and-list-aux-removal
    (equal (aig-and-list-aux x)
           (aig-and-list x)))
  (local (defthm aig-and-list-when-member-nil
           (implies (member nil x)
                    (equal (aig-and-list x) nil))))
  (verify-guards aig-and-list))

(define aig-or-list-aux (x)
  :enabled t
  :parents (aig-or-list)
  (if (atom x)
      nil
    (aig-or (car x)
            (aig-or-list-aux (cdr x)))))

(define aig-or-list (x)
  :parents (aig-constructors)
  :short "@(call aig-or-list) <i>or</i>s together all of the AIGs in the list
@('x')."
  :long "<p>As a dumb attempt at optimization, we try to avoid consing if we
see that there's a @('t') anywhere in the list.  This won't win very often, but
it is quite cheap and it can win big when it does win by avoiding a lot of AIG
construction.</p>"
  :returns aig
  :enabled t
  :verify-guards nil
  (mbe :logic (if (atom x)
                  nil
                (aig-or (car x) (aig-or-list (cdr x))))
       :exec (cond ((atom x)
                    nil)
                   ((member-eql-without-truelistp t x)
                    t)
                   (t
                    (aig-or-list-aux x))))
    ///
    (defthm aig-or-list-aux-removal
      (equal (aig-or-list-aux x)
             (aig-or-list x)))
    (local (defthm l0
             (and (equal (aig-or t y) t)
                  (equal (aig-or y t) t))
             :hints(("Goal" :in-theory (enable aig-or)))))
    (local (defthm aig-or-list-when-member-t
             (implies (member t x)
                      (equal (aig-or-list x) t))))
    (verify-guards aig-or-list))

;; BOZO want a reduction xor, nor, nand, etc., as well?

(define aig-and-lists (x y)
  :parents (aig-constructors)
  :short "@(call aig-and-lists) pairwise <i>and</i>s together the AIGs from the
lists @('x') and @('y')."
  :returns aig-list
  :enabled t
  (if (or (atom x) (atom y))
      nil
    (cons (aig-binary-and (car x) (car y))
          (aig-and-lists (cdr x) (cdr y)))))

(define aig-or-lists (x y)
  :parents (aig-constructors)
  :short "@(call aig-or-lists) pairwise <i>or</i>s together the AIGs from the
lists @('x') and @('y')."
  :returns aig-list
  :enabled t
  (if (or (atom x) (atom y))
      nil
    (cons (aig-binary-or (car x) (car y))
          (aig-or-lists (cdr x) (cdr y)))))

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

(define aig-implies-lists (x y)
  :parents (aig-constructors)
  :short "@(call aig-implies-lists) pairwise <i>implies</i> together the AIGs
from the lists @('x') and @('y')."
  :returns aig-list
  :enabled t
  (if (or (atom x) (atom y))
      nil
    (cons (aig-implies-fn (car x) (car y))
          (aig-implies-lists (cdr x) (cdr y)))))

(define aig-nand-lists (x y)
  :parents (aig-constructors)
  :short "@(call aig-nand-lists) pairwise <i>nand</i>s together the AIGs from the
lists @('x') and @('y')."
  :returns aig-list
  :enabled t
  (if (or (atom x) (atom y))
      nil
    (cons (aig-nand (car x) (car y))
          (aig-nand-lists (cdr x) (cdr y)))))

(define aig-nor-lists (x y)
  :parents (aig-constructors)
  :short "@(call aig-nor-lists) pairwise <i>nor</i>s together the AIGs from the
lists @('x') and @('y')."
  :returns aig-list
  :enabled t
  (if (or (atom x) (atom y))
      nil
    (cons (aig-nor (car x) (car y))
          (aig-nor-lists (cdr x) (cdr y)))))

(define aig-andc1-lists (x y)
  :parents (aig-constructors)
  :short "@(call aig-andc1-lists) pairwise <i>andc1</i>s together the AIGs from the
lists @('x') and @('y')."
  :returns aig-list
  :enabled t
  (if (or (atom x) (atom y))
      nil
    (cons (aig-andc1 (car x) (car y))
          (aig-andc1-lists (cdr x) (cdr y)))))

(define aig-andc2-lists (x y)
  :parents (aig-constructors)
  :short "@(call aig-andc2-lists) pairwise <i>andc2</i>s together the AIGs from the
lists @('x') and @('y')."
  :returns aig-list
  :enabled t
  (if (or (atom x) (atom y))
      nil
    (cons (aig-andc2 (car x) (car y))
          (aig-andc2-lists (cdr x) (cdr y)))))

(defsection aig-orc1-lists
  :parents (aig-constructors)
  :short "@(call aig-orc1-lists) is identical to @(see aig-implies-lists)."
  :long "@(def aig-orc1-lists)"
  (defmacro aig-orc1-lists (x y)
    `(aig-implies-lists ,x ,y)))

(define aig-orc2-lists (x y)
  :parents (aig-constructors)
  :short "@(call aig-orc2-lists) pairwise <i>orc2</i>s together the AIGs from the
lists @('x') or @('y')."
  :returns aig-list
  :enabled t
  (if (or (atom x) (atom y))
      nil
    (cons (aig-orc2 (car x) (car y))
          (aig-orc2-lists (cdr x) (cdr y)))))


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
    aig-xor-lists
    aig-iff-lists
    aig-nand-lists
    aig-nor-lists
    aig-implies-lists
    aig-andc1-lists
    aig-andc2-lists
    aig-orc2-lists
    ))


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

(define aig-restrict-list-acc (x sigma (acc true-listp))
  (if (atom x)
      (revappend acc nil)
    (aig-restrict-list-acc
     (cdr x) sigma
     (cons (aig-restrict (car x) sigma) acc))))

(define aig-restrict-list
  :parents (aig-substitution)
  :short "@(call aig-restrict-list) substitutes into a list of AIGs."
  ((x     "List of AIGs.")
   (sigma "Fast alist binding variables to replacement AIGs, as in @(see
           aig-restrict)."))
  :returns aig-list
  :enabled t
  :verify-guards nil
  (mbe :logic
       (if (atom x)
           nil
         (cons (aig-restrict (car x) sigma)
               (aig-restrict-list (cdr x) sigma)))
       :exec (aig-restrict-list-acc x sigma nil))
  ///
  (local (defthm aig-restrict-list-acc-elim
           (equal (aig-restrict-list-acc x sigma acc)
                  (revappend acc (aig-restrict-list x sigma)))
           :hints(("Goal" :in-theory (enable aig-restrict-list-acc)))))

  (verify-guards aig-restrict-list))

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
    :var (aig-alist-lookup x sigma)
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



(define aig-env-extract (vars env)
  :returns (extract true-listp :rule-classes :type-prescription)
  (if (atom vars)
      nil
    (hons-acons (car vars)
                (acl2::aig-env-lookup (car vars) env)
                (aig-env-extract (cdr vars) env)))
  ///
  (defthm aig-env-lookup-in-aig-env-extract
    (iff (acl2::aig-env-lookup v (aig-env-extract vars env))
         (if (member v vars)
             (acl2::aig-env-lookup v env)
           t)))

  (defthm hons-assoc-equal-in-aig-env-extract
    (equal (hons-assoc-equal v (aig-env-extract vars env))
           (and (member v vars)
                (cons v (acl2::aig-env-lookup v env))))))
