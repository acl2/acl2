; Copyright (C) 2009-2015, Regents of the University of Texas
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.
;; A scheme for pattern matching
;; written by Sol Swords, 6/01/2005
;; email: sswords@cs.utexas.edu


;; with code borrowed from the case-match function in basis.lisp,
;; by Matt Kaufmann and J Strother Moore.




;; There is quite a bit left to do with this especially for execution efficiency:
;; since we keep separate lists of tests and bindings for each clause, we may
;; call certain destructor functions many times where we could've used a binding
;; to improve the efficiency.  If destructors are expensive, you may wish to avoid
;; using this.  See the defdoc at the end of this file for usage and explanation.

(in-package "ACL2")
(include-book "xdoc/top" :dir :system)

(program)

(defxdoc pattern-match
  :parents (case-match)
  :short "User-definable pattern-matching."
  :long "<p>Examples:</p>

  @({
  (pattern-match
   x
   ((cons a b) ... body1 ... )
   ((three-elt-constructor a & c) ... body2 ...)
   (& default-value))
  })

<p>@('pm') is a convenient abbreviation for @('pattern-match').</p>

<p>Pattern-match is similar to @(see case-match), but the two macros interpret
patterns differently.  If the pattern is @('(a b c)'), @('case-match')
interprets this as a three-element list and, if the input is also a
three-element list, binds the first to @('a'), second to @('b'), and third to
@('c').  Pattern-match, on the other hand, interprets @('(a b c)') as the
application of a constructor @('a') to arguments @('b') and @('c').  Aside from
this difference, pattern-match contains much the same features as case-match.
See @(see case-match) for the significance of special characters such as @('&')
and @('!').  Also see @(see pattern-match-list), @(see pattern-matches), and
@(see pattern-matches-list).</p>

<h3>Usage</h3>

@({
  (pattern-match
     input
     (pattern1 declare-form condition11 condition12 ... declare-form body1)
     (pattern2 condition21 condition22 ... body2)
      ...)
})

<p>In the previous invocation, pattern-match first matches the input to
pattern1.  If it matches, condition11, condition12, ... are evaluated using any
variable bindings that pattern1 created, and using the declare form preceding
them if there is one.  (The declare form is primarily useful for declaring
ignored variables.)  If they all evaluate to non-nil, body1 is evaluated and
returned with the same variable bindings and with the declare form preceding
it, if any.  If pattern1 does not match or any of the conditions evaluate to
nil, body1 is not evaluated and pattern2 is tried, and so on.  The list of
patterns should be comprehensive or else end with a listing of the form @('(&
finalbody)'), so that finalbody serves as a default value.</p>

<p>In each pattern clause the declare forms and conditions are optional.
Conditions may be included without declare forms and vice versa.  To
distinguish declare forms from conditions we simply check whether the first
item following the pattern and/or the last item before the body are declare
forms; everything between the pattern and body that is not a declare form is
assumed to be a condition.</p>

<p>Each pattern may be a variable, to be bound to the value of the input; an
existing variable name prefixed by ! or a constant, the value of which is to be
compared with the input value; the special symbol @('&') which matches
anything, or an application of a constructor to a number of arguments.  Each
constructor must have an associated macro which allows pattern-match to process
it.  The macro defines what is acceptable syntax, i.e. the number and type of
arguments the constructor can take, the conditions under which the input
matches the constructor, and the significance of the arguments.  For example,
cons-pattern-matcher is defined so that in a pattern match statement, the
constructor cons is required to take exactly two arguments; it matches any
input satisfying (consp input), and its arguments are treated as subpatterns to
be matched to the car and cdr of the input, respectively.</p>

<h3>Extensions</h3>

<p>The pattern-match book includes built-in support for the constructors
@('cons'), @('list'), and @('list*').  Support may be added for user-defined
constructors.  Some ``special constructors'' are also supported, with less
obvious behavior. @('raw') takes one argument, which is matched to the input
using case-match syntax; that is, no constructors are recognized.  @('bind')
takes two arguments, one a variable symbol and one a pattern; if the pattern
matches the input, then the input is bound to the variable.  @('any') compares
the input to each of its arguments using equal; if any of the arguments are
equal to the input then it is considered a match. @('force') assumes that the
pattern matches and makes the specified bindings without checking.</p>

<p>For example, the following pattern-match statement returns @('(1 ((1 2
. 3)))'):</p>

 @({
  (pattern-match (list 1 (cons 1 (cons 2 3)))
    ((cons a (bind k (raw ((a b . c))))) (list a k)))
 })

<p>For documentation on enabling pattern-match to recognize new constructors,
see @(see def-pattern-match-constructor) and for more see @(see
constructor-pattern-match-macros).</p>

<p>Note 1: Currently pattern-match does not bind the input expression to an
internal variable, but simply copies it everywhere it is used.  Therefore it is
wise, if the input is from some expensive calculation, to bind it to a variable
before applying pattern-match.</p>

<p>Note 2: The default value of a pattern-match expression in case no patterns
match is nil.  Because of this, if the pattern-match expression is supposed to
evaluate to a special shape (an mv, or state, for instance), a default value of
the correct shape must be defined by including a final clause of the form @('(&
default-value-of-correct-shape)').</p>")

(defmacro pbl-tests-bindings (tests bindings)
  `(pattern-bindings-list (cdr lhses) (cdr rhses) ,tests ,bindings
                          pmstate))


(defmacro execute-patmatch (testclause bindings-and-body nextcall)
  (if testclause
      `(if ,testclause
           ,bindings-and-body
         ,nextcall)
    bindings-and-body))

(defmacro check-pattern-matches (testclause bindings-and-body nextcall)
  (declare (ignore bindings-and-body nextcall))
  (or testclause t))


(defun intern-check (str sym)
  (if (equal (symbol-package-name sym) "COMMON-LISP")
      (intern str "ACL2")
    (intern-in-package-of-symbol str sym)))


(defun pattern-bindings-list
  (lhses rhses tests bindings pmstate)
  (if (or (atom lhses) (atom rhses))
      (let* ((tests-declare (nth 0 pmstate))
             (final-tests (nth 1 pmstate))
             (declare (nth 2 pmstate))
             (body (nth 3 pmstate))
             (nextcall (nth 4 pmstate))
             (action (nth 5 pmstate))
             (final-test (if final-tests
                             `((let ,(reverse bindings)
                                 ,@tests-declare
                                 (and ,@final-tests)))
                           nil))
             (bindings-and-body
              (if (or (eq body t) (eq body nil))
                  body
                `(let ,(reverse bindings) ,@declare ,body)))
             (tests (revappend tests final-test))
             (testclause
              (if (< 1 (len tests))
                  `(and ,@tests)
                (if (consp tests)
                    (car tests)
                  nil))))
        `(,action ,testclause ,bindings-and-body ,nextcall))
    (let ((lhs (car lhses))
          (rhs (car rhses)))
      (cond
       ((symbolp lhs)
        (cond
         ((or (eq lhs t) (eq lhs nil))
          (pbl-tests-bindings (cons `(eq ,rhs ,lhs) tests) bindings))
         ((and (> (length (symbol-name lhs)) 0)
               (eql #\* (char (symbol-name lhs) 0)))
          (pbl-tests-bindings (cons `(equal ,rhs ,lhs) tests) bindings))
         ((and (> (length (symbol-name lhs)) 0)
               (eql #\! (char (symbol-name lhs) 0)))
          (pbl-tests-bindings
           (cons `(equal ,rhs ,(intern-check (coerce (cdr (coerce (symbol-name lhs) 'list))
                                               'string)
                                       lhs)) tests)
           bindings))
         ((eq lhs '&) (pbl-tests-bindings tests bindings))
         (t (let ((binding (assoc-eq lhs bindings)))
              (cond ((null binding)
                     (pbl-tests-bindings tests (cons `(,lhs ,rhs) bindings)))
                    (t (pbl-tests-bindings (cons `(equal ,rhs ,(cadr binding)) tests)
                                           bindings)))))))
       ((atom lhs)
        (pbl-tests-bindings (cons (equal-x-constant rhs (list 'quote lhs)) tests)
                            bindings))
       ((eq (car lhs) 'quote)
        (pbl-tests-bindings (cons (equal-x-constant rhs lhs) tests)
                            bindings))
       (t
        ;;lhs is aassumed to be a constructor application.  Return a call of
        ;;the pattern match macro for that constructor.
        (let* ((func (car lhs))
               (args (cdr lhs))
               (func-pm-macro (intern-check (concatenate 'string
                                                         (symbol-name func)
                                                         "-PATTERN-MATCHER")
                                            func)))
          (list func-pm-macro rhs args tests bindings (cdr lhses) (cdr rhses)
                pmstate)))))))


(defun test-declare (elt)
  (if (and (consp elt)
           (eq (car elt) 'declare))
      (list elt)
    nil))

(defun slice-clause (clause)
  (case (len clause)
    (0 (mv (er hard 'top-level "Empty clause") nil nil nil nil))
    (1 (mv (er hard 'top-level "Pattern needs a body") nil nil nil nil))
    (2 (mv (car clause) nil nil nil (cadr clause)))
    (3 (let ((decl (test-declare (cadr clause))))
         (if decl
             (mv (car clause) nil nil decl (caddr clause))
           (mv (car clause) nil (list (cadr clause)) nil (caddr clause)))))
    (otherwise
     (let* ((n (len clause))
            (pattern (car clause))
            (maybe-test-declare (test-declare (nth 1 clause)))
            (maybe-body-declare (test-declare (nth (- n 2) clause)))
            (body (nth (- n 1) clause))
            (tests (if maybe-test-declare
                       (if maybe-body-declare
                           (subseq clause 2 (- n 2))
                         (subseq clause 2 (- n 1)))
                     (if maybe-body-declare
                         (subseq clause 1 (- n 2))
                       (subseq clause 1 (- n 1))))))
       (mv pattern maybe-test-declare tests maybe-body-declare body)))))


(defun pattern-match-clauses (term clauses action)
  (if (atom clauses)
      nil
    (mv-let
     (pattern test-decl final-tests body-decl body)
     (slice-clause (car clauses))
     (cond ((and (eq pattern '&) (null final-tests))
            body)
           (t (pattern-bindings-list
               (list pattern) (list term) nil nil
               (list test-decl final-tests body-decl body
                     `(pattern-match ,term ,@(cdr clauses))
                     action)))))))


(defxdoc pattern-match-list
  :parents (pattern-match)
  :short "Pattern matching to a list of terms."
  :long "<p>Example:</p>

  @({
  (pattern-match-list
    (a b c d)
    (((cons !c x) 3 (list* !b y) x)
     (declare (ignore x))
     (foo y))
    (& default-value)))
  })

<p>@('pml') is a convenient abbreviaton of @('pattern-match-list').</p>

<p>Matches a list of terms to a list of pattern clauses.  See @(see
pattern-match) for more documentation of the pattern semantics.  The first
argument to pattern-match-list should be a list of input terms.  (For best
efficiency, these terms should be bound variables or simple constants, not
containing function calls.) Each subsequent argument should be a pattern
clause, consisting of a list of the following items:</p>

<ol>

<li>a list of patterns, the same length as the list of input terms</li>

<li>a declare form, used when evaluating the test forms (optional)</li>

<li>any number of test forms, which may use variables bound in the
pattern (optional)</li>

<li>a declare form whose scope is the body (optional)</li>

<li>the body, an expression to be evaluated if the pattern matches and all the
tests succeed.</li>

</ol>

<p>The final pattern clause may be of the form @('(& default-value)'); this is
an exception to the convention that the pattern list must be a list same length
as the input list, and it simply defines a default value for the pattern-match
clause, to be returned instead of nil when all patterns fail.</p>

<p>See also @(see pattern-matches-list), which simply tests whether or not a
certain pattern list matches the list of inputs.</p>")

(defun pattern-match-list-clauses (term-list clauses action)
  (if (atom clauses)
      nil
    (mv-let
     (patterns test-decl final-tests body-decl body)
     (slice-clause (car clauses))
     (cond ((and (eq patterns '&) (null final-tests))
            body)
           ((= (len patterns) (len term-list))
            (pattern-bindings-list
             patterns term-list nil nil
             (list test-decl final-tests body-decl  body
                   `(pattern-match-list ,term-list ,@(cdr clauses))
                   action)))
           (t (er hard 'top-level
                  "Lengths of term list ~x0 and pattern list ~x1 are unequal"
                  term-list patterns))))))

(defmacro pattern-match-list (term-list &rest clauses)
  (pattern-match-list-clauses term-list clauses 'execute-patmatch))

(defsection pml
  :parents (pattern-match)
  :short "@('pml') is an abbreviation for @('pattern-match-list')."
  :long "@(def pml)"

  (defmacro pml (term-list &rest clauses)
    `(pattern-match-list ,term-list . ,clauses)))

(defsection pattern-matches-list
  :parents (pattern-match)
  :short "Check that a list of terms matches a list of patterns."
  :long "<p>Example</p>

@({
  (pattern-matches-list
     (a b c)
     (x (cons x y) y))
})

<p>The example returns:</p>

<ul>
<li>@('t')  &mdash;  if @('b') equals the @(see cons) of @('a') and @('c'), or,</li>
<li>@('nil') &mdash; otherwise.</li>
</ul>

<p>See @(see pattern-match) and @(see pattern-match-list).</p>"

  (defmacro pattern-matches-list (term-list pattern-list)
    (pattern-match-list-clauses term-list `((,pattern-list t)) 'check-pattern-matches)))

(defmacro pattern-match (term &rest clauses)
  (pattern-match-clauses term clauses 'execute-patmatch))

(defsection pm
  :parents (pattern-match)
  :short "@('pm') is an abbreviation for @('pattern-match')."
  :long "@(def pm)"

  (defmacro pm (term &rest clauses)
    `(pattern-match ,term . ,clauses)))


(defsection pattern-matches
  :parents (pattern-match)
  :short "Check whether a term matches a pattern."
  :long "<p>Example:</p>

@({
    (pattern-matches x (cons a (cons b a)))
})

<p>The example is equivalent to the test</p>

@({
    (and (consp x)
         (consp (cdr x))
         (equal (car x) (cddr x)))
})

<p>See @(see pattern-match) and @(see pattern-match-list).</p>"

  (defmacro pattern-matches (term pattern)
    (pattern-match-clauses term `((,pattern t)) 'check-pattern-matches)))

(mutual-recursion
 (defun explode-term (term)
   (if (consp term)
       (if (eq (car term) 'quote)
           (list 'quote term)
         `(list ',(car term) ,@(explode-list (cdr term))))
     term))

 (defun explode-list (list)
   (if (atom list)
       nil
     (cons (explode-term (car list))
           (explode-list (cdr list))))))

(defmacro expl (tm)
  (explode-term tm))



(defun destructor-subst-list (term destructors)
  (if (atom destructors)
      nil
    (cons (if (consp (car destructors))
              (subst 'term term (explode-term (car destructors)))
            `(list ',(car destructors) term))
         (destructor-subst-list term (cdr destructors)))))

(defun destructor-list (destructors)
  (if (atom destructors)
      nil
    `((list ',(car destructors) term)
      ,@(destructor-list (cdr destructors)))))


(defsection def-pattern-match-constructor
  :parents (pattern-match)
  :short "Allow pattern-match to recognize a constructor."
  :long "<p>Example:</p>

@({
    (def-pattern-match-constructor cons consp (car cdr))
})

<p>For a constructor @('cname'), defines a macro named
@('cname-pattern-matcher') which will allow constructs using @('cname') to be
recognized by the pattern-match macro; see @(see pattern-match).  This macro
takes three arguments: the name of the constructor, which is the symbol that
pattern-match will recognize; the name of a recognizer function which returns
@('t') on objects produced by the constructor; and an ordered list of
destructor function names, which when applied to the constructed object return
the arguments to the constructor.</p>

<p>For example, say we define a function cons3 that combines three objects into
a triple.  We define a recognizer, cons3-p, for correctly-formed triples as
created by cons3, as well as three accessors, cons3-first, cons3-second,
cons3-third.  Now we'd like to have a pattern match expression like this</p>

@({
  (pattern-match x
         ((cons3 a b c) ... body ..)
         ... other clauses ...)
})

<p>resolve to this:</p>

@({
  (if (cons3-p x)
      (let ((a (cons3-first x))
            (b (cons3-second x))
            (c (cons3-third x)))
        ... body ...)
    ... other conditions ...)
})

<p>Therefore the pattern match macro must know that the recognizer for a cons3
object is cons3-p, and that the destructors are cons3-first, etc - we don't
want to have to write out those names anywhere in the untranslated body.  Our
solution is that when pattern-match sees a function symbol fun, it returns a
call to a macro named fun-pattern-matcher.  If this macro does not exist,
pattern-match will fail.  To easily define such macros, we provide
def-pattern-match-constructor, which takes as arguments the constructor name,
the recognizer name, and the ordered list of destructors.  For example, to
allow pattern-match to deal with cons3, we'd call</p>

@({
    (def-pattern-match-constructor cons3 cons3-p
      (cons3-first cons3-second cons3-third))
})

<p>Similarly for cons, the call would be</p>

@({
     (def-pattern-match-constructor cons consp (car cdr))
})

<p>but this is built into the pattern match book.</p>

<p>Pattern-matcher macros may be defined more flexibly without using
@('def-pattern-match-constructor') in order to support, for example, macros
with variable numbers of arguments; see @(see
constructor-pattern-match-macros).</p>")

(defmacro def-pattern-match-constructor (&rest args)
  (let* ((term (if (consp (car args)) (caar args) nil))
        (constructor (if term (cadr args) (car args)))
        (recognizer (if term
                        (if (eq (caddr args) :unconditional)
                            nil
                          (if (consp (caddr args))
                              (subst 'term term (explode-term (caddr args)))
                            `(list ',(caddr args) term)))
                      (if (eq (cadr args) :unconditional)
                          nil
                        `(list ',(cadr args) term))))
        (destructors (if term
                         (cons 'list (destructor-subst-list term (cadddr args)))
                       (cons 'list (destructor-list (caddr args)))))
        (err-string-nargs
         (concatenate 'string
                      "Wrong number of arguments to "
                      (symbol-name constructor)
                      " in pattern matching: ~x0~%"))
        (err-string-truelist
         (concatenate 'string "Badly formed expression: ~x0~%")))

    `(defmacro ,(intern-in-package-of-symbol
                 (concatenate 'string (symbol-name constructor)
                                     "-PATTERN-MATCHER")
                 (if (equal (symbol-package-name constructor) "COMMON-LISP")
                     'acl2::bla
                   constructor))
       (term args tests bindings lhses rhses pmstate)
       (cond ((not (true-listp args))
              (er hard 'top-level ,err-string-truelist (cons ',constructor args)))
             ((not (= (len args) ,(1- (len destructors))))
              (er hard 'top-level ,err-string-nargs (cons ',constructor args)))
             (t
              (let ((rhses
                     (append ,destructors
                             rhses))
                    ,@(if recognizer
                          `((tests (cons ,recognizer tests)))
                        nil)
                    (lhses (append args lhses)))
                (pattern-bindings-list lhses rhses tests bindings pmstate)))))))



(defsection constructor-pattern-match-macros
  :parents (pattern-match)
  :short "How to write pattern-match macros for custom constructors."
  :long "<p>Here we discuss how constructor @(see pattern-match) macros work in
conjunction with pattern-match.  In most cases the user does not need to be
concerned with the internals discussed here; see @(see
def-pattern-match-constructor) for an easy way to get pattern-match to
recognize a user-defined form.</p>

<p>The trick behind pattern-match is that whenever a constructor @('cname') is
seen in a pattern, a call to the macro named @('cname-pattern-matcher') is
returned and macro expansion continues by expanding that macro.  Because of
this, all the unprocessed parts of the original pattern-match call must be
passed through that macro.  By the design of the framework, the constructor
macro will only operate on a few of the arguments given to it, passing the rest
through to the main function that performs pattern matching,
@('pattern-bindings-list').</p>

<p>The arguments given to the constructor's macro are</p>

@({
    (term args tests bindings lhses rhses pmstate)
})

<p>The arguments that @('pattern-bindings-list') takes are</p>

@({
    (lhses rhses tests bindings pmstate)
})

<p>The argument list of @('pattern-bindings-list') is a subset of that of the
constructor's macro.  We will discuss how to form the arguments for
@('pattern-bindings-list') from those given to the constructor macro.</p>

<p>The constructor macro is responsible for error handling in the case of a
nonsensical invocation of the constructor (primarily, one with the wrong number
of arguments), adding appropriate tests to determine whether @('term') can
match the pattern, and ``lining up'' the arguments given to the constructor in
the pattern with the appropriate destructors applied to the term in
question.</p>

<p>We will go through the arguments given to the macro and outline what needs
to be done with them to fulfill the above obligations.</p>

<p>@('term') is a term which should evaluate to the current part of the input
that we are trying to match.  If the original term given as input to pattern
match was x, then term may be something like @('(car (nth 4 (cdr x)))').
Therefore we need to add tests to determine whether this is of the correct form
to be matched to something created by our constructor, and we need to apply the
correct destructors to it to break it down for further matching.</p>

<p>@('args') is the list of arguments given to the constructor in the pattern
that we're matching to.  The whole pattern that @('term') is supporsed to match
is our constructor @('cname') applied to @('args').  For error checking we need
to ensure that @('args') is the correct length for the call to our constructor
to make sense.  It is also helpful to ensure that @('args') is a true-list and
issue a helpful error message if not.  Each element of @('args') must also be
paired with an application of a destructor to @('term') to continue pattern
matching.  If, as is usually the case, the arguments we're expecting are to be
read as subpatterns, the best approach is not to examine them individually but
to let pattern-bindings-list do the real work.</p>

<p>@('tests') is an accumulated list of tests to be applied to the input to
determine whether it matches the pattern.  We need to prepend to this list any
necessary tests on @('term') so as to determine whether it could be formed by
our constructor.</p>

<p>@('bindings') is an accumulated list of variables that will be bound to
applications of destructors to the input term.  While the results of the
processing that our macro does will have a direct effect on this list, most of
the time it should be passed through to @('pattern-bindings-list') and we
should instead manipulate @('lhses') and @('rhses'):</p>

<p>@('lhses') and @('rhses') are lists of, respectively, subpatterns of the
top-level pattern that we're processing and corresponding subterms of the input
term that will be matched to the patterns.  In most cases what we'll do is
prepent @('args') to @('lhses') while prepending a list of each of our
destructors applied to @('term') to @('rhses').  @('pattern-bindings-list')
will then handle the details of variable bindings and recursive subpattern
matching as determined by the contents of @('lhses').  Each macro must maintain
the invariant that @('lhses') and @('rhses') are the same length; if this isn't
the case there are probably other things going wrong as well.  The intuition
behind these names is that eventually patterns in @('lhses') break down to
variables, which are bound to corresponding subterms broken down from elements
of @('rhses').  We're using LHS and RHS here as in an assignment statement in
some imperative language, as opposed to the sense used when talking about a
rewrite rule.</p>

<p>@('pmstate') contains the expression to be evaluated if the pattern matches,
the list of tests to be tried before confirming a match, declarations, the rest
of the clauses to match to in case this match fails, and the name of the macro
to pass the final results to.  These are grouped together specifically because
they don't have to do with the actual pattern-matching but must be kept intact
through the various iterations of macro expansion.  This argument should
*always* be passed through intact to pattern-bindings-list unless you're trying
to really confuse your users.</p>

<p>An example of a very typical constructor macro is the one for cons, which is
automatically generated by @('def-pattern-match-constructor'):</p>

 @({
 (defmacro
   cons-pattern-matcher
   (term args tests bindings lhses rhses pmstate)
   (cond
    ;; First check args for well-formedness: it should always be a true-list of
    ;; length 2, since any other argument list to cons is ill-formed.
    ((not (true-listp args))
     (er hard 'top-level ``badly formed expression: ~~x0~~%''
         (cons 'cons args)))
    ((not (= (len args) 2))
     (er hard 'top-level
         ``Wrong number of arguments to CONS in pattern matching: ~~x0~~%''
         (CONS 'CONS ARGS)))
    (t (let
        ;; Push destructor applications (car term) and (cdr term) onto rhses
        ((rhses (append (list (list 'car term) (list 'cdr term)) rhses))
         ;; Push the args onto lhses (they must occur in the order corresponding
         ;; to the order of the destructor calls pushed onto rhses.)
         (lhses (append args lhses))
         ;; Push a test that term is consp onto tests
         (tests (cons (list 'consp term) tests)))
        ;; Finally call pattern-bindings-list again.
        (pattern-bindings-list lhses rhses tests bindings pmstate)))))
 })

<p>If there are no errors, this simply makes three changes to the existing
arguments: it prepends the two subterms @('(car term)') and @('(cdr term)')
onto @('rhses') and the list of arguments to @('lhses') and adds the test
@('(consp term)') to tests.  It then calls pattern-bindings-list.</p>

<p>The macro for list works the same way, but could not have been generated by
@('def-pattern-match-constructor') because it handles variable length argument
lists.  It again simply prepends all arguments to @('lhses'), prepends a list
of applications of destructors to the input term to rhses (try evaluating
@('(list-of-nths 0 5 'x)') to see the resulting form), and tests whether the
input term is of a suitable form, in this case whether it is a true-list of the
same length as the argument list.</p>

 @({
 (defmacro list-pattern-matcher
   (term args tests bindings lhses rhses pmstate)
   ;; Ensure that args is a true-list; it may be any length.
   (if (not (true-listp args))
       (er hard 'top-level ``Badly formed expression: ~~x0~~%''
           (cons 'list args))
     (let
         ;; list-of-nths produces a list of calls to nth, from (nth 0 term) up
         ;; to (nth (- (length args) 1) term).
         ((rhses (append (list-of-nths 0 (length args) term) rhses))
          ;; push args onto lhses
          (lhses (append args lhses))
          ;; Require that term is a true-list with length corresponding to that
          ;; of args.
          (tests (append `((true-listp ,term)
                           (= (len ,term) ,(length args)))
                         tests)))
       (pattern-bindings-list lhses rhses tests bindings pmstate))))
 })

<p>A nonstandard, but still correct, example is the one for list*, which
instead of doing the processing itself replaces its pattern with an equivalent
cons structure so that the cons macro will do all the work: to illustrate what
is prepended to @('lhses'), try running @('(list*-macro (list 'a 'b 'c 'd))').
In this case no test needs to be added because the cons macro takes care of it.
Note that we could easily cause an infinite loop in macro expansion by abusing
this type of thing and, for example, pushing a new @('list*') pattern onto
lhses.</p>

 @({
 (defmacro list*-pattern-matcher
   (term args tests bindings lhses rhses pmstate)
   ;; Check that args is a true-listp.
   ;; If this is counterintuitive, consider that this would suggest syntax such
   ;; as (list* a b . c).
   (if (not (true-listp args))
       (er hard 'top-level ``Badly formed expression: ~~x0~~%''
           (cons 'list* args))
     (let
         ;; Just push term onto rhses
         ((rhses (cons term rhses))
          ;; list*-macro is the very function that list* uses to expand an
          ;; invocation into a nest of conses.  Since we have a cons pattern
          ;; matcher already, we just take advantage of this.
          (lhses (cons (list*-macro args) lhses)))
       ;; No additional tests are necessary - we trust in cons-pattern-matcher
       ;; to take care of that.
       (pattern-bindings-list lhses rhses tests bindings pmstate))))
 })

<p>Another nonstandard example is raw-pattern-matcher, which reverts the
behavior of pattern-match to that of case-match for the term inside; in fact,
it just calls the function that does the work for case-match -
@('match-tests-and-bindings') - and uses its results.  In this case, since the
argument to our constructor is not taken to be a subpattern of the form handled
by @('pattern-bindings-list'), we manipulate @('bindings') directly rather than
dealing with @('lhses') and @('rhses').  It is fortunate that the form of the
tests and bindings variables for @('match-tests-and-bindings') is the same as
ours or we would need to do more processing of them.</p>

 @({
 (defmacro raw-pattern-matcher
   (term args tests bindings lhses rhses pmstate)
   ;; Args should be a list of length 1 - just a pattern.
   (if (or (atom args)
           (cdr args))
       (er hard 'top-level ``Badly formed expression: ~~x0~~%''
           (cons 'raw args))
     ;; match-tests-and-bindings takes a term, a case-match pattern, and a list
     ;; of tests and bindings; it returns a new version of tests and bindings
     ;; including the ones necessary to match the term to the pattern.
     (mv-let (tests bindings)
             (match-tests-and-bindings term (car args) tests bindings)
             ;; We then pass the new tests and bindings to
             ;; pattern-bindings-list.
             (pattern-bindings-list lhses rhses tests bindings pmstate))))
  })

<p>Also try looking at the definitions for @('bind-pattern-matcher'),
@('any-pattern-matcher'), and both @('force-pattern-matcher') and
@('force-match-remove-tests-pattern-matcher') as further nonstandard
examples.</p>")

(def-pattern-match-constructor cons consp (car cdr))


(defun list-of-nths (n len term)
  (if (= n len)
      nil
    `((nth ,n ,term)
      ,@(list-of-nths (1+ n) len term))))

(defmacro list-pattern-matcher
  (term args tests bindings lhses rhses pmstate)
  ;; Ensure that args is a true-list; it may be any length.
  (if (not (true-listp args))
      (er hard 'top-level "Badly formed expression: ~x0~%"
          (cons 'list args))
    (let
        ;; list-of-nths produces a list of calls to nth, from (nth 0 term) up
        ;; to (nth (- (length args) 1) term).
        ((rhses (append (list-of-nths 0 (length args) term) rhses))
         ;; push args onto lhses
         (lhses (append args lhses))
         ;; Require that term is a true-list with length corresponding to that
         ;; of args.
         (tests (append `((true-listp ,term)
                          (= (len ,term) ,(length args)))
                        tests)))
      (pattern-bindings-list lhses rhses tests bindings pmstate))))


(defmacro list*-pattern-matcher
  (term args tests bindings lhses rhses pmstate)
  ;; Check that args is a true-listp.
  ;; If this is counterintuitive, consider that this would suggest syntax such
  ;; as (list* a b . c).
  (if (not (true-listp args))
      (er hard 'top-level "Badly formed expression: ~x0~%"
          (cons 'list* args))
    (let
        ;; Just push term onto rhses
        ((rhses (cons term rhses))
         ;; list*-macro is the very function that list* uses to expand an
         ;; invocation into a nest of conses.  Since we have a cons pattern
         ;; matcher already, we just take advantage of this.
         (lhses (cons (list*-macro args) lhses)))
      ;; No additional tests are necessary - we trust in cons-pattern-matcher
      ;; to take care of that.
      (pattern-bindings-list lhses rhses tests bindings pmstate))))




(defmacro raw-pattern-matcher
  (term args tests bindings lhses rhses pmstate)
  ;; Args should be a list of length 1 - just a pattern.
  (if (or (atom args)
          (cdr args))
      (er hard 'top-level "Badly formed expression: ~x0~%"
          (cons 'raw args))
    ;; match-tests-and-bindings takes a term, a case-match pattern, and a list
    ;; of tests and bindings; it returns a new version of tests and bindings
    ;; including the ones necessary to match the term to the pattern.
    (mv-let (tests bindings)
            (match-tests-and-bindings term (car args) tests bindings)
            ;; We then pass the new tests and bindings to
            ;; pattern-bindings-list.
            (pattern-bindings-list lhses rhses tests bindings pmstate))))


(defmacro bind-pattern-matcher
  (term args tests bindings lhses rhses pmstate)
  (if (not (and (true-listp args)
                (equal (len args) 2)
                (symbolp (car args))))
      (er hard 'top-level "Badly formed expression: ~x0~%"
          (cons 'bind args))
    (let ((rhses (cons term rhses))
          (lhses (cons (cadr args) lhses))
          (bindings (cons (list (car args) term) bindings)))
      (pattern-bindings-list lhses rhses tests bindings
                             pmstate))))


(defun equal-any-list (term args)
  (if (endp args)
      nil
    (cons `(equal ,term ,(car args))
          (equal-any-list term (cdr args)))))

(defmacro any-pattern-matcher
  (term args tests bindings lhses rhses pmstate)
  (if (not (true-listp args))
      (er hard 'top-level "Badly formed expression: ~x0~%"
          (cons 'any args))
    (let ((tests (cons `(or ,@(equal-any-list term args))
                       tests)))
      (pattern-bindings-list lhses rhses tests bindings
                             pmstate))))


(def-pattern-match-constructor (x) acons
  (and (consp x) (consp (car x)))
  (caar cdar cdr))


(defmacro force-pattern-matcher
  (term args tests bindings lhses rhses pmstate)
  (if (not (true-listp args))
      (er hard 'top-level "Badly formed expression: ~x0~%"
          (cons 'list args))
    (let ((lhses (cons (car args)
                       (cons '(force-match-remove-tests) lhses)))
          (rhses (cons term
                       (cons '(force-match-remove-tests) rhses)))
          (tests (cons '(nil . force-match-remove-tests) tests)))
      (pattern-bindings-list lhses rhses tests bindings pmstate))))


(defun remove-up-to (item list)
  (if (atom list)
      nil
    (if (equal (car list) item)
        (cdr list)
      (remove-up-to item (cdr list)))))

(defmacro force-match-remove-tests-pattern-matcher
  (term args tests bindings lhses rhses pmstate)
  (if (or args (not (equal term '(force-match-remove-tests))))
      (er hard 'top-level
          "Don't use force-match-remove-tests manually!~%")
    (let ((tests (remove-up-to '(nil . force-match-remove-tests) tests)))
      (pattern-bindings-list lhses rhses tests bindings pmstate))))

